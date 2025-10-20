(* Maybe: Need to check for I(L_f) *)
signature CONTSTRUCT_FUNS = sig
  structure Entry : DBM_ENTRY
  structure DBM : DBM_ALG
  val network: Entry.t ClockCeilingTypes.network ->
               (DBM.t, Entry.t) ConstructFunsTypes.network Error.res
end

(* XXX: Add testing*)
functor ConstructFuns (E : DBM_ENTRY) : CONTSTRUCT_FUNS = struct
structure Entry = E
structure DBM = DBM(structure E = Entry and M = LnLayoutMatrix)

open Either
open Error
open CompilationError
open ClockCeilingTypes

val return = succeed ()
(* Maybe: Add minimal constraint stuff *)

(* Maybe: Check the indices of updates but only in dbg mode ?*)
(*      since this shouldn't be possible after renaming *)
fun check_index i size =
    if i < 0 orelse i >= size then i |> invalid_index |> lift_comp_err
    else return

fun check_update size u =
    case u of
        Syntax.Reset (x, _) => check_index x size |
        Syntax.Copy (x, y) => check_index x size
                              <|> check_index y size
                              >>= (K return) |
        Syntax.Shift (x, _) => check_index x size |
        Syntax.Update (x, y, _) => check_index x size
                                   <|> check_index y size
                                   >>= (K return)

fun check_updates size =
    combine_map (check_update size)

fun check_var_bound bounds u =
    case u of
        Syntax.Reset (i, v) => let val (l, u) = IndexDict.find i bounds in
                                   if v < l orelse v > u then
                                     Syntax.Reset (i, v)
                                     |> upd_out_of_bounds
                                     |> lift_comp_err
                                   else return
                               end |
        _ => return

fun check_var_bounds bounds =
    combine_map (check_var_bound bounds)

(* Updates: *)
fun upd_comb f =
    List.foldl (fn (upd, acc) => f upd o acc) id

fun var_update bounds u = let
  fun copy' x y vars =
      let
        val (l, u) = IndexDict.find x bounds
        val at_y = Array.sub (vars, y)
      in
        if l <= at_y andalso at_y <= u
        then (Array.update (vars, x, at_y); SOME vars)
        else NONE
      end
  fun shift' x v vars =
      let
        val new = Array.sub (vars, x) + v
        val (l, u) = IndexDict.find x bounds
      in
        if l <= new andalso new <= u
        then (Array.update (vars, x, new); SOME vars)
        else NONE
      end
  fun reset x v vars = (Array.update (vars, x, v); SOME vars)
  fun update x y c vars =
      let
        val (l, u) = IndexDict.find x bounds
        val new = Array.sub (vars, y) + c
      in
        if l <= new andalso new <= u
        then (Array.update (vars, x, new); SOME vars)
        else NONE
      end
in
  case u of
      Syntax.Reset (x, v) => reset x v |
      Syntax.Copy (x, y) => copy' x y |
      Syntax.Shift (x, v) => shift' x v |
      Syntax.Update (x, y, c) => update x y c
end

fun var_upd_comb f =
    List.foldl (fn (upd, acc) => Option.composePartial (f upd, acc))
               (Option.filter (K true))

fun var_upds bounds upds =
    var_upd_comb (var_update bounds) upds

fun clock_update u =
    case u of
        Syntax.Reset (i, v) => DBM.reset i v |
        Syntax.Copy (x, y) => DBM.copy_clock x y |
        Syntax.Shift (x, v) => DBM.shift x v |
        Syntax.Update (x, y, c) => DBM.copy_clock x y #> DBM.shift x c

fun clock_updates' upds =
    upd_comb clock_update upds

(* Invariants: *)
fun bound x y v = (x, y, Entry.from_int v)

fun constr_to_bound size c = let
  open ClockConstraint
in
      case c of
          Lt (x, y, v) => bound x y (IntRep.LT v) |
          Le (x, y, v) => bound x y (IntRep.LTE v)
end

fun precompile_bound size_c =
    map (constr_to_bound size_c)

fun guards_i size_c =
    precompile_bound size_c #> upd_comb DBM.And

fun invariants size_c = guards_i size_c

(* Dataguards: *)
fun guards_d gds =
    gds
    |> map Syntax.Guard.data_guard
    |> foldl (op andf) (K true)

fun check_edge size_v size_c clock_updates var_updates =
    let
      fun pred size = (fn i => i < 0 orelse i >= size)
      val check_upd_clocks = check_updates size_c
      val check_upd_vars = check_updates size_v
    in
      check_upd_clocks clock_updates
      <|> check_upd_vars var_updates
      >>= (K return)
    end

fun edge var_bounds size_v size_c
         ({source, target, g_single, g_diag,
           g_data, label, clock_updates, var_updates} : edge) =
    let
      val check_e =
          check_edge size_v size_c clock_updates var_updates
      val check_v =
          check_var_bounds var_bounds var_updates
    in
      (check_e <|> check_v)
      |> mapR (K
                   {
                     source = source,
                     target = target,
                     label = label,
                     g_data = guards_d g_data,
                     g = guards_i size_c g_single
                         #> guards_i size_c g_diag,
                     clock_updates = clock_updates' clock_updates,
                     var_updates = var_upds var_bounds var_updates
                   }
              )
    end

fun node size_c ({id, invariant, name} : node) =
    {id = id, invariant = invariants size_c invariant, name = name}

fun G_d_set gs set =
    foldl (uncurry ConstraintSet.insert_set) set gs

fun G_d automata =
    let
      fun diags f =
          f #> map #g_diag #> flat
    in
      foldl (fn ((_,ta), G_d') =>
                G_d'
                |> G_d_set (ta |> diags #edges_in)
                |> G_d_set (ta |> diags #edges_out)
                |> G_d_set (ta |> diags #edges_internal))
            ConstraintSet.empty automata
    end

fun automaton var_bounds size_v size_c
              ({edges_in, edges_out, edges_internal,
                broadcast_in, broadcast_out, committed,
                nodes, initial, loc_dict, name_dict} : automaton) =
    let
      fun comp_es es = combine_map (edge var_bounds size_v size_c) es
      fun comp_nodes nodes = map (node size_c) nodes
    in
      (comp_es edges_in <|> comp_es edges_out)
      <|> (comp_es broadcast_in <|> comp_es broadcast_out)
      <|> (comp_es edges_internal)
      |> mapR (fn (((in_es, out_es),(broadcast_in, broadcast_out)), internal) =>
                          {
                            nodes = comp_nodes nodes,
                            edges_in = in_es,
                            edges_out = out_es,
                            broadcast_in = broadcast_in,
                            broadcast_out = broadcast_out,
                            committed = committed,
                            edges_internal = internal,
                            initial = initial,
                            loc_dict = loc_dict,
                            name_dict = name_dict
                          }
                  )
    end

local
  open Syntax
  open Formula
  open Constraint
  open Difference
in
fun compile_formula F (L, vars) =
    let
      fun diff_sub diff p vars =
          case diff of
              Single x => Array.sub (vars, x) |> p |
              Diff (l, r) => Array.sub (vars, l) - Array.sub (vars, r)
                             |> p
      fun dataguard_to_fun c =
          case c of
              Lt (l, r) => diff_sub l (fn x => x < r) vars |
              Le (l, r) => diff_sub l (fn x => x <= r) vars |
              Eq (l, r) => diff_sub l (fn x => x = r) vars |
              Ge (l, r) => diff_sub l (fn x => x >= r) vars |
              Gt (l, r) => diff_sub l (fn x => x > r) vars

      fun inner F' =
              case F' of
                  True => true |
                  Not f => not (inner f) |
                  And (l, r) => (inner l andalso inner r)  |
                  Or (l, r) => (inner l orelse inner r) |
                  Impl (l, r) => (not (inner l) orelse inner r) |
                  Loc (p, l) => (Array.sub (L, p) = l) |
                  Pred c => dataguard_to_fun c

    in
      inner F
    end
end

fun network ({automata, clock_dict, var_dict, label_dict, ta_names,
              var_bounds, formula, k_neg, k_pos, broadcast_dict}
             : E.t ClockCeilingTypes.network) =
    let
      val size_v = IndexDict.size var_dict
      val size_c = IndexDict.size clock_dict
      fun comp_formula F =
          F
          |> Formula.map compile_formula
          |> Formula.conv
      fun comp_ta k ta =
          automaton var_bounds size_v size_c ta
          |> mapR (pair k)
      fun comp_tas tas = tas |> combine_map (uncurry comp_ta)
    in
      comp_tas automata
      |> mapR (fn tas =>
                {
                  automata = tas,
                  G_d = G_d automata,
                  clock_dict = clock_dict,
                  var_dict = var_dict,
                  label_dict = label_dict,
                  ta_names = ta_names,
                  var_bounds = var_bounds,
                  k_neg = k_neg,
                  k_pos = k_pos,
                  formula = comp_formula formula,
                  broadcast_dict = broadcast_dict
                }
              )
    end
end

structure Funs = ConstructFuns(Entry64Bit)
