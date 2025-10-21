signature SCC_GRAPH = sig
  structure W : WEIGHT
  type node = int
  type graph
  val start: int -> graph
  val add_edge: node * W.t * node
                -> graph -> graph
  val scc: graph -> node list list * (node -> node -> W.t)
  val succs: graph -> node -> node list
end

functor SCCGraph(W : WEIGHT) : SCC_GRAPH = struct
structure W = W
type node = int
type graph = unit Int_Graph.T * W.t option LnLayoutMatrix.matrix
fun start n = (Int_Graph.empty, LnLayoutMatrix.create n NONE)

(* Check whether the exception would be called *)
val node = flip pair ()
fun update_matrix i j x adj =
    case LnLayoutMatrix.sub i j adj of
        NONE => LnLayoutMatrix.update i j (SOME x) adj |
        SOME y => LnLayoutMatrix.update i j (W.max x y |> SOME) adj

fun add_node node G =
    Int_Graph.new_node node G handle Int_Graph.DUP _ => G

fun add_edge (src, w, dst) (G, Adj) =
    (
      G
      |> add_node (node src)
      |> add_node (node dst)
      |> Int_Graph.add_edge (dst, src)
    ,
      tap (update_matrix dst src w) Adj
    )

fun weight adj i j =
    case LnLayoutMatrix.sub i j adj of
        NONE => W.zero |
        SOME x => W.neg x

fun scc g = g |> (apfst Int_Graph.strong_conn #> apsnd weight)
fun succs (g, _) =  Int_Graph.immediate_succs g
end

functor SimpleCeilingGraph(structure E : DBM_ENTRY
                           structure W : WEIGHT) = struct
structure W = W
structure SCCGraph = SCCGraph(W)
type location = int
type clock = int
type index = int
type mapping = location -> clock -> index
type ceiling = mapping * W.t option vector

fun mapping X l clock =
    if clock = 0 then 0
    else 1 + l * X + (clock - 1)

fun init n_locs n_clocks =
    SCCGraph.start (n_locs * n_clocks + 1)

fun add_invar mapping graph cconstr = let
  fun upd x c =
      case W.from_clock_bound c of
          NONE => graph |
          SOME c => SCCGraph.add_edge ((mapping x), c, 0) graph
in
  case cconstr of
      ClockConstraint.Lt (0, 0, _) => graph |
      ClockConstraint.Le (0, 0, _) => graph |
      ClockConstraint.Lt (0, x, c) => upd x c |
      ClockConstraint.Le (0, x, c) => upd x c |
      ClockConstraint.Lt (x, 0, c) => upd x c |
      ClockConstraint.Le (x, 0, c) => upd x c |
      ClockConstraint.Lt (x, y, c) => (upd x c; upd y c) |
      ClockConstraint.Le (x, y, c) => (upd x c; upd y c)
end


fun add_node mapping
             ({invariant, id, ...} : RewriteConstraintTypes.node)
    =
    let
      val add_invar = add_invar (mapping id)
    in
      fold (fn cconstr => fn (g, used) =>
               (
                 add_invar g cconstr,
                 UsedClocks.insert_cconstr cconstr used
               )
           )
           invariant
    end

fun add_nodes mapping =
    let
      val add_node = add_node mapping
    in
      fold add_node
    end

fun add_guard mapping
              ({g_single, g_diag, source, ...} : RewriteConstraintTypes.edge)
    =
    let
      val add_to_graph = add_invar (mapping source)
      fun add_guard' guards = fold (fn guard => fn (graph, used) =>
                                       (
                                         add_to_graph graph guard,
                                         UsedClocks.insert_cconstr guard used
                                       )
                                   ) guards
    in
      add_guard' g_single #> add_guard' g_diag
    end

fun add_guards mapping =
    let
      val add_guard = add_guard mapping
    in
      fold add_guard
    end

fun clocks_in_guard g =
    fold UsedClocks.insert_cconstr g

fun add_update X mapping in_invar
               ({source, target, g_single, g_diag, clock_updates, ...}
                : RewriteConstraintTypes.edge)
               graph =
    let
      val ix_src = mapping source
      val ix_dst = mapping target
      val in_g = UsedClocks.empty
                     |> clocks_in_guard g_single
                     |> clocks_in_guard g_diag
                     |> UsedClocks.is_in
      val used = UsedClocks.is_in in_invar


      fun update' x ix_y c graph =
          SCCGraph.add_edge ((ix_src x), c, ix_y) graph

      fun add_reset (x, c) base graph =
          (
            Inttab.insert_set x base,
            if in_g x (* orelse used x *) then graph
            else update' x 0 (W.from_int c) graph
          )

      fun add_copy (y, x) base graph =
          (
            Inttab.insert_set y base,
            if in_g x (* orelse used y *) then graph
            else update' x (ix_dst y) W.zero graph
          )
      open Syntax
      fun add_single_update upd =
          case upd of
              Syntax.Copy xy => add_copy xy |
              Syntax.Reset xc => add_reset xc |
              _ => Exn.error "There should not be such an update"

      fun handle_updates base graph =
          foldl (fn (upd, (base, graph)) => add_single_update upd base graph)
                (base, graph)

      fun handle_non_base base graph =
          fold_range (fn i => fn graph =>
                         let val x = i + 1 in
                           if Inttab.defined base x (* orelse used x *) then graph
                           else update' x (ix_dst x) W.zero graph end)
                     X graph
    in
      clock_updates
      |> handle_updates Inttab.empty graph
      |> uncurry handle_non_base
    end

fun add_updates clocks mapping in_invar G es =
    foldl (uncurry (add_update clocks mapping in_invar)) G es

fun add_clockconstraints index graph
                         ({nodes, edges_in, edges_out, edges_internal, ...}
                          : RewriteConstraintTypes.automaton) =
    let
      val add_nodes = add_nodes index
      val add_guards = add_guards index
    in
      (
        graph,
        UsedClocks.empty
      )
          |> add_nodes nodes
          |> add_guards edges_internal
          |> add_guards edges_in
          |> add_guards edges_out
    end

fun add_automaton clocks mapping
                  (ta as {nodes, edges_in, edges_out, edges_internal, ...}
                   : RewriteConstraintTypes.automaton) graph
    =
    let
      val (graph, in_invar) = add_clockconstraints mapping graph ta
      val add_upds = flip (add_updates clocks mapping in_invar)
    in
      graph
          |> add_upds edges_in
          |> add_upds edges_out
          |> add_upds edges_internal
    end

fun init_vector n =
    IndexDict.tabulate (n + 1) (fn i => if i = 0 then SOME W.zero else NONE)

fun list_show last f ls =
    "[" ^ (map f ls |> String.concatWith ",") ^ "]" ^ last

fun shortest_scc_paths n graph =
    let
      val (sccs, G) = SCCGraph.scc graph
      val d = init_vector n
      val d' = foldl
                   (
                     fn (vs, d) =>
                        foldl
                            (
                              fn (u, d) =>
                                 foldl
                                     (
                                       fn (v, d) =>
                                          case IndexDict.find u d of
                                              NONE => d |
                                              SOME du =>
                                              case IndexDict.find v d of
                                                  NONE => (
                                                    IndexDict.update
                                                        v (G u v
                                                          |> W.add du
                                                          |> SOME) d
                                               ) |

                                                  SOME dv => (
                                                    IndexDict.update
                                                        v (G u v
                                                          |> W.add du
                                                          |> W.min dv
                                                          |> SOME) d
                                                  )
                                     )
                                     d
                                     (SCCGraph.succs graph u)
                            )
                            d vs
                   )
                   d sccs
      val d'' = foldl
                    (
                      fn (vs, d) =>
                         let
                           val dssc =
                               foldl
                                   (
                                     fn (v, dscc) =>
                                        case dscc of
                                            NONE => IndexDict.find v d |
                                            SOME d' => (
                                              case IndexDict.find v d of
                                                  NONE => dscc |
                                                  SOME dv => SOME (W.min dv d')
                                            )
                                   )
                                   NONE
                                   vs
                         in
                           foldl (fn (v, d) => IndexDict.update v dssc d) d vs
                         end
                    )
                    d'
                    sccs
    in
      IndexDict.map (fn x => case x of NONE => W.zero | SOME x => W.neg x) d''
    end

fun process_k clocks (ta as {nodes, ...} : RewriteConstraintTypes.automaton) =
    let
      val mapping = mapping clocks
      val locations = length nodes
      val n_vertices = locations * clocks
    in
      (
        (* locations, *)
        mapping,
        init locations clocks
        |> add_automaton clocks mapping ta
        |> shortest_scc_paths n_vertices
      )
    end
end

functor LocalCeilingFunction(E : DBM_ENTRY) = struct
structure Maximal = SimpleCeilingGraph(structure E = E
                                   structure W = IntWeight)
structure UpperBounds = SimpleCeilingGraph(structure E = E
                                           structure W = UpperBound)
structure LowerBounds = SimpleCeilingGraph(structure E = E
                                    structure W = LowerBound)

fun lu ({clock_dict, automata, ...} : RewriteConstraintTypes.network) =
    let
      val clocks_with_0 = IndexDict.size clock_dict
      val lower = map (snd #> LowerBounds.process_k (clocks_with_0 - 1)) automata
                      |> IndexDict.fromList
      val upper = map (snd #> UpperBounds.process_k (clocks_with_0 - 1)) automata
                      |> IndexDict.fromList
      fun map_k f = apsnd (IndexDict.map f)
      val k_pos = IndexDict.map (map_k  E.==<) lower
      (* val _ = show_k clocks_with_0 k_dict |> print *)
      val k_neg = IndexDict.map (map_k  (~ #> E.=<)) upper
      fun k choose dict L x = Array.foldli
                                  (fn (p, l, max_x_L) =>
                                      choose
                                          (
                                            IndexDict.find p dict
                                            |> (fn (map, k) =>
                                                   IndexDict.find (map l x) k)
                                          )
                                          max_x_L
                                  )
                                  E.zero L
    in
      (k E.min k_neg, k E.max k_pos)
    end

fun ceil ({clock_dict, automata, ...} : RewriteConstraintTypes.network) =
    let
      val clocks_with_0 = IndexDict.size clock_dict
      val k_dict = map (snd #> Maximal.process_k (clocks_with_0 - 1)) automata
                   |> IndexDict.fromList
      fun map_k f = apsnd (IndexDict.map f)
      val k_pos = IndexDict.map (map_k E.==<) k_dict
      (* val _ = show_k clocks_with_0 k_dict |> print *)
      val k_neg = IndexDict.map (map_k (~ #> E.=<)) k_dict
      fun k choose dict L x = Array.foldli
                                  (fn (p, l, max_x_L) =>
                                      choose
                                          (
                                            IndexDict.find p dict
                                            |> (fn (map, k) =>
                                                   IndexDict.find (map l x) k)
                                          )
                                          max_x_L
                                  )
                                  E.zero L
    in
      (k E.min k_neg, k E.max k_pos)
    end
end
