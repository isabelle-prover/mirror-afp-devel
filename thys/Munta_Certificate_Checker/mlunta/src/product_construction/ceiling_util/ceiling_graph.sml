(* XXX: Use And Instead of FloydWarshall *)
signature CEILING_GRAPH = sig
  structure Graph : SP_GRAPH
  type process
  type location_map
  type map = process -> location_map
  type t
  val add_nodes: location_map -> Graph.graph ->
                 RewriteConstraintTypes.node list
                 -> UsedClocks.t -> UsedClocks.t
  val add_updates: process -> location_map -> UsedClocks.t ->
                 RewriteConstraintTypes.edge list -> t -> t
  val automaton: process -> location_map ->
                 RewriteConstraintTypes.automaton -> t -> t
  val network: RewriteConstraintTypes.network -> t
  val k: t -> Graph.W.t Vector.vector * map
end


functor CeilingGraph(Graph : SP_GRAPH)
        : CEILING_GRAPH = struct
structure Graph = Graph
type process = int
type location = int
type index = int
type clock = int

type location_map = location -> clock -> index
type map = process -> location_map
type t = {
  adj : Graph.graph,
  mapping : map,
  X : string IndexDict.t,
  N : int list
}

fun add_times times x sum =
    x * times + sum

fun size X N =
    foldl (uncurry (add_times X)) 1 N

(* Function calculating the index for a given process, location and clock *)
fun num_nodes_before add_clocks N = let
  val sizes_N = (IndexDict.fromList N)
  val at_p = flip IndexDict.find sizes_N
in
  IndexDict.mapi
      (apfst (flip
                  (fold_range
                       (fn i => fn acc => add_clocks (at_p i) acc))
                  1
             )
      )
      sizes_N
end
(* Find out how to do chop faster and mapping as well also fold_range*)
(* Now may be do this with memo *)
fun mapping N_before p l clock =
    let
      val (until_p, N_p) = IndexDict.find p N_before
      val process_clock = N_p * (clock - 1)
    in
      if clock = 0 then 0
      else until_p + process_clock + l
    end

(* Intitializes a Ceiling Graph for A IndexDict of Clocks X without clock zero
   and a list of number of nodes where the index is the process *)
fun gen X N =
    let
      val X_size = IndexDict.size X
      val add_clocks = add_times X_size
      val N_before = num_nodes_before add_clocks N
    in
      {
        adj = Graph.init (size X_size N),
        mapping = mapping N_before,
        X = X,
        N = N
      }
    end

(******************************************************************************)
(*                   functions for constructiong the Ceiling Graph            *)
(******************************************************************************)

(* Adding a Clock Constraint to the Graph *)
fun add_cconstr ix adj cconstr = let
  fun upd x c =
      case Graph.W.from_clock_bound c of
          NONE => adj |
          SOME c => Graph.add_edge (ix x) 0 c adj
in
  case cconstr of
      ClockConstraint.Lt (0, 0, _) => adj |
      ClockConstraint.Le (0, 0, _) => adj |
      ClockConstraint.Lt (0, x, c) => upd x c |
      ClockConstraint.Le (0, x, c) => upd x c |
      ClockConstraint.Lt (x, 0, c) => upd x c |
      ClockConstraint.Le (x, 0, c) => upd x c |
      ClockConstraint.Lt (x, y, c) => (upd x c; upd y c) |
      ClockConstraint.Le (x, y, c) => (upd x c; upd y c)
end

(* Adding the invariants in a node to the graph *)
fun add_node index adj
             ({invariant, id, ...} : RewriteConstraintTypes.node)
             =
             let
               val ix = index id
               val add_invar = add_cconstr ix adj
             in
               fold (fn cconstr => fn used =>
                               (
                                 add_invar cconstr;
                                 UsedClocks.insert_cconstr cconstr used
                               )
                          )
                    invariant
             end

fun add_nodes index adj =
    let
      val add_node = add_node index adj
    in
      fold add_node
    end

fun add_guard index adj
              ({g_single, g_diag, source, ...} : RewriteConstraintTypes.edge)
              =
    let
      val add_to_graph = add_cconstr (index source) adj
      fun add_guard' g = fold (fn g => fn used =>
                                         (
                                           add_to_graph g;
                                           UsedClocks.insert_cconstr g used
                                         )
                              ) g
    in
       add_guard' g_single #> add_guard' g_diag
    end

fun add_guards index adj =
    let
      val add_guard = add_guard index adj
    in
      fold add_guard
    end

fun clocks_in_guard g =
    fold UsedClocks.insert_cconstr g

fun add_update p index used
             (G as {adj, X, mapping, N, ...} : t)
             ({source, target, g_single, g_diag, clock_updates, ...}
              : RewriteConstraintTypes.edge) =
    let
      val n_p = length N
      val ix_src = index source
      val locations = map (flip (curry List.tabulate) id) N
      val ix_dst = index target
      val in_g = UsedClocks.empty
                 |> clocks_in_guard g_single
                 |> clocks_in_guard g_diag
                 |> UsedClocks.is_in
      val not_used = UsedClocks.is_in used #> not
      fun update' x ix_y c =
          (Graph.add_edge (ix_src x) ix_y (Graph.W.from_int c) adj; ())


      local open Iter in
      fun upd_body (y, x, c) (p, l) =
          update' x (mapping p l y) c

      fun add_before upd =
            for (0 to p <*> inList (take p locations |> flat))
                (upd_body upd)

      fun add_after upd =
          for ((p + 1) to n_p <*> inList (drop (p + 1) locations |> flat))
              (upd_body upd)
      end

      fun add_triv (upd as (y, x, c)) base =
          (
            if in_g x (* orelse not_used y *) then ()
            else update' x (ix_dst y) c;
            Inttab.insert_set y base
          )

      fun add_not_p (upd as (y, x, c)) =
          (
            add_before upd;
            add_after upd
          )

      fun add_reset (x, c) base =
          (
            if in_g x (* orelse not_used x *) then ()
            else
            update' x 0 c;
            Inttab.insert_set x base
          )

      fun add_copy (y, x) base =
          (
            if in_g x (* orelse not_used y *) then ()
            else update' x (ix_dst y) 0;
            Inttab.insert_set y base
          )

      fun add_full upd base =
          (
            add_not_p upd;
            add_triv upd base
          )

      open Syntax
      fun add_single_update upd =
            case upd of
                Syntax.Update (x, y, c) => add_full (x, y, c) |
                Syntax.Copy (x, y)      => add_copy (x, y) |
                Syntax.Shift (x, c)     => add_full (x, x, c) |
                Syntax.Reset (x, c)     => add_reset (x, c)

      fun handle_updates base =
          foldl (uncurry add_single_update) base
      fun dbg base =
          (
            print "\n";
            print ("process: " ^ Int.toString p ^ "\n");
            print ("src: "^ Int.toString source ^"\n") ;
            print ("dst: "^ Int.toString target ^"\n") ;
            Inttab.map (fn k => fn _ => (Int.toString k ^ "," |> print)) base;
            print "\n"
          )
      fun handle_non_base base =
        IndexDict.foldli (fn (i,_, _) =>
                             let val x = i + 1 in
                               if Inttab.defined base x (* orelse not_used x *) then ()
                               else update' x (ix_dst x) 0 end)
                         () X
    in
        clock_updates
        |> handle_updates Inttab.empty
        |> handle_non_base
    end

fun add_updates p index used es G =
    (app (add_update p index used G) es; G)

fun add_clockconstraints index (G as {adj, ...})
                ({nodes, edges_in, edges_out, edges_internal, ...}
                 : RewriteConstraintTypes.automaton) =
    let
      val add_nodes' = add_nodes index adj
      val add_guards' = add_guards index adj
    in
      (
        G,
        UsedClocks.empty
        |> add_nodes' nodes
        |> add_guards' edges_internal
        |> add_guards' edges_in
        |> add_guards' edges_out
      )
    end

fun automaton p index
              (ta as {nodes, edges_in, edges_out, edges_internal, ...}
               : RewriteConstraintTypes.automaton) (G : t)
    =
    let
      val (G, used) = add_clockconstraints index G ta
      val add_upds = add_updates p index used
    in
      G
      |> add_upds edges_in
      |> add_upds edges_out
      |> add_upds edges_internal
    end

fun network ({automata, clock_dict, ...} : RewriteConstraintTypes.network) =
    let
      open RewriteConstraintTypes
      val N = map (snd #> #loc_dict #> IndexDict.size) automata
      val X = IndexDict.size clock_dict - 1
      val clocks = IndexDict.tabulate X (fn i => IndexDict.find (i + 1) clock_dict)
      val (G as {adj, mapping, ...}) = gen clocks N

    in
      foldl (fn ((p,ta),G) => (automaton p (mapping p) ta G)) G automata
    end

(******************************************************************************)
(*                         Showing the Ceiling Graph                          *)
(******************************************************************************)

(******************************************************************************)
(*  mapping_dict gives back a index dict for the mapping of the ceiling graph *)
(******************************************************************************)

fun mapping_dict X N = let
  val X = IndexDict.to_list X
  val N = map (flip (curry List.tabulate) Int.toString) N
  fun map_product' xs ys = flip (flip map_product xs) ys
  fun map_index_prod X N f =
      map_index (fn (p, locs) => map_product' X locs (f p)) N
in
  map_index_prod X N
      (fn p => fn clock => fn loc => (Int.toString p) ^ "," ^ loc ^ "," ^ clock)
  |> flat |> cons "  0  " |> IndexDict.fromList
end

fun show ({adj, mapping, X, N, ...} : t) =
    let
      val names = mapping_dict X N
      val name_at = flip IndexDict.find names
      val _ =
          (
            print "        | ";
            IndexDict.app (fn str => str ^ " | " |> print) names
          )
    in
      (Graph.show name_at adj; print "\n")
    end

fun k (ceil as {adj, mapping, ...} : t) =
    let
      val dim = Graph.nodes adj
      (* val _ = show ceil *)
      val G_sp = Graph.shortest_path adj

      val k = Graph.k adj
      (* val _ = show ceil *)
    in
      (k, mapping)
    end
end

functor NonTrivialLocalCeiling(Entry : DBM_ENTRY) = struct
structure LocalCeiling = CeilingGraph(IntGraph)
structure UpperCeiling = CeilingGraph(UpperGraph)
structure LowerCeiling = CeilingGraph(LowerGraph)
(* fun index_list dict = *)
(*     List.tabulate (IndexDict.size dict, id) *)

(* fun process_loc_clocks locs clocks = *)
(*     map (map (rpair clocks)) locs *)

(* fun k_list k mapping loc_clocks = *)
(*     map_index ( *)
(*       fn (p, locs) => *)
(*       map ( *)
(*         fn (l, clocks) => *)
(*            map ( *)
(*              fn clock => *)
(*                 Vector.sub(k, mapping p l clock) |> Int.toString *)
(*            ) clocks *)
(*       ) locs *)
(*     ) loc_clocks *)


(* fun string_list f xs = *)
(*     let *)
(*       fun help xs = *)
(*        case xs of *)
(*            [] => "]" | *)
(*            [x] => f x ^ "]" | *)
(*            (x::xs) => f x ^ ", " ^ help xs *)
(*     in *)
(*       "[" ^ help xs *)
(*     end *)

(* fun show k = *)
(*     string_list (fn p => string_list (string_list id) p ^ "\n") k *)
(*     |> print *)

fun ceil (n : RewriteConstraintTypes.network) =
    let
      val G = LocalCeiling.network n
      val (k, mapping) = G |> LocalCeiling.k

      (* val clocks = index_list (#clock_dict n) *)
      (* val locs = map (snd #> #loc_dict #> index_list) (#automata n) *)
      (* val loc_clocks = process_loc_clocks locs clocks *)
      (* val k_print = k_list k mapping loc_clocks *)
      (* val _ = show k_print *)

      fun to_entries f = Vector.map f k
      val k_neg = to_entries (~ #> Entry.=<)
      val k_pos = to_entries Entry.==<
      fun k choose vect L x = Array.foldli
                           (fn (p, l, max_x_L) =>
                                 choose
                                     (Vector.sub (vect, (mapping p l x)))
                                     max_x_L
                           )
                           Entry.zero L
    in
       (k Entry.min k_neg, k Entry.max k_pos)
    end

fun lu (n : RewriteConstraintTypes.network) =
    let
      val G_upper = UpperCeiling.network n
      val (upper, mapping) = G_upper |> UpperCeiling.k
      val G_lower = LowerCeiling.network n
      val (lower, _) = G_lower |> LowerCeiling.k

      (* val clocks = index_list (#clock_dict n) *)
      (* val locs = map (snd #> #loc_dict #> index_list) (#automata n) *)
      (* val loc_clocks = process_loc_clocks locs clocks *)
      (* val k_print = k_list k mapping loc_clocks *)
      (* val _ = show k_print *)

      val L = Vector.map (Entry.=< o ~) lower
      val U = Vector.map Entry.==< upper
      fun k choose vect L x = Array.foldli
                           (fn (p, l, max_x_L) =>
                                 choose
                                     (Vector.sub (vect, (mapping p l x)))
                                     max_x_L
                           )
                           Entry.zero L
    in
       (k Entry.min L, k Entry.max U)
    end

end
