signature REWRITE_BEXPS = sig
  val compile_guards:
      string list ->
      string list ->
      (string, int) Syntax.guard ->
       (((string, int) Syntax.diff_constraint list *
        (string, int) Syntax.diff_constraint list) *
       (string, int) Syntax.guard list) Error.res
  val compile_invariant:
      string list ->
      string list ->
      (string, 'a) Syntax.invariant ->
      (string, 'a) Syntax.constraint list Error.res
  val compile_updates:
      string list ->
      string list ->
      string Syntax.update list  ->
      (string Syntax.update list * string Syntax.update list) Error.res
  val network: ParseBexpTypes.network -> RewriteBexpsTypes.network Error.res
end

structure RewriteBexps : REWRITE_BEXPS  = struct

structure Util = struct
open RewriteBexpsTypes
(*
XXX:
Broadcasts:
  - [X] partition broadcast edges
  - [ ] (and check whether the broadcast edges exist ?)
  - [X] check broadcast for duplicates
  - [X] check internal edges for broadcast labels
Committed Locations:
  - [X] check for duplicates
  - [X] check whether they really exist
*)
fun partition_labels is_broadcast (edges : RewriteBexpsTypes.edge list) =
    let
      fun partition_label_es p =
          List.partition (get_label #> p)
      val partition_internal =
          partition_label_es (fn Syntax.Internal _ => true | _ => false)
      val partition_in =
          partition_label_es (fn Syntax.In _ => true | Syntax.Out _ => false)
      val partition_broadcast =
          partition_label_es (fn Syntax.In  x => is_broadcast x |
                                 Syntax.Out x => is_broadcast x)
      val (internal, other) = partition_internal edges
      val (in_actions, out_actions) = partition_in other
      val (broadcast_in, edges_in) = partition_broadcast in_actions
      val (broadcast_out, edges_out) = partition_broadcast out_actions
    in
      find_all (get_label #> Syntax.get_label #> is_broadcast) internal
      |> Either.combine_map (fn e =>
                                LangError.broadcast_is_internal (e
                                                                |> #source
                                                                |> Int.toString
                                                                , e
                                                                |> #target
                                                                |> Int.toString
                                                                )
                                |> Error.lift_lang_err)
      |> Either.mapR (K (internal,
                         edges_in,
                         edges_out,
                         broadcast_in,
                         broadcast_out))
    end

end

open Error
open CompilationError
open NamingError
open LangError
open ParseBexpTypes
open Either
open Syntax

val return = succeed ()
fun is_same x y = x = y

fun lift_constr_err err =
    err |> constr_err |> lift_comp_err
fun lift_naming_err err =
    err |> naming |> lift_comp_err

fun just_singleton l g f ls =
    case ls of
            [] => l |
            [x] => f x |
            _ => g

(* Checks: *)
(* For formula *)
local
  open Formula
in
fun check_formula' b (automata : (string * automaton) list) clocks vars =
    let
      fun is_clock c = List.exists (is_same c) clocks
      fun is_var v = List.exists (is_same v) vars
      fun one_var id =
          if is_clock id then clock_in_formula id |> lift_constr_err
          else if is_var id then succeed id
          else unknown_var id |> lift_naming_err

      fun check_cmp x =
          case x of
              Difference.Single a => one_var a |> mapR Difference.Single |
              Difference.Diff (l, r) => one_var l
                                        <|> one_var r
                                        |> mapR Difference.Diff

      fun process_matches a f =
            just_singleton (unknown_proc a |> lift_naming_err)
                           (ambg_proc a |> lift_naming_err) f
      fun loc_matches a f =
          just_singleton (unknown_loc a |> lift_naming_err)
                         (ambg_loc a |> lift_naming_err) f

      fun inner a x ta = let
          val nodes = (#nodes o snd) ta
          val names = List.map (#name) nodes
          val matches' = List.filter (is_same x) names
        in
          loc_matches a (K return) matches'
        end

      fun check_loc a x =
          let
            val matches = List.filter (fn (b, _) => a = b) automata
          in
            process_matches a (inner a x) matches
          end

      fun check_constr c =
          case c of
              Constraint.Lt (l, r) => check_cmp l
                                      |> mapR (fn l => Constraint.Lt (l, r)) |
              Constraint.Le (l, r) => check_cmp l
                                      |> mapR (fn l => Constraint.Le (l, r)) |
              Constraint.Eq (l, r) => check_cmp l
                                      |> mapR (fn l => Constraint.Eq (l, r)) |
              Constraint.Ge (l, r) => check_cmp l
                                      |> mapR (fn l => Constraint.Ge (l, r)) |
              Constraint.Gt (l, r) => check_cmp l
                                      |> mapR (fn l => Constraint.Gt (l, r))
      fun check e =
          case e of
              True => if b then true_in_formula |> lift_constr_err
                      else succeed True |
              Not e => check e |> mapR Not |
              And (l, r) => check l <|> check r |> mapR And |
              Or (l, r) => check l <|> check r |> mapR Or |
              Impl (l, r) => check l <|> check r |> mapR Impl |
              Loc (a, x) => check_loc a x
                            |> mapR (Loc (a, x) |> K) |
              Pred c => check_constr c |> mapR Pred
    in
      check
    end

fun check_formula automata clocks vars formula =
    let
      fun check' b = check_formula' b automata clocks vars
      val check = check' true
      val checkl = check' false
    in
      case formula of
              Ex f => check f |> mapR Ex |
              Eg f => check f |> mapR Eg |
              Ax f => check f |> mapR Ax |
              Ag f => check f |> mapR Ag |
              Leadsto (p, q) => (checkl p <|> check q)
                                |> mapR Leadsto
    end
end
(* For vars and clocks *)
fun ambg_identifier clocks var =
    if List.exists (is_same var) clocks then var |> ambg_var |> lift_naming_err
    else return

fun check_amb_vars_clocks clocks =
      combine_map (ambg_identifier clocks)

(* For automata: *)
(* Maybe: own stage for checking the initial stuff? or into renaming *)
(* Checking for the existence of the initial state *)
fun check_initial initial ids =
    if List.exists (is_same initial) ids then return
    else initial |> no_initial |> naming |> lift_comp_err

fun invalid_edge_err e =
    e
    |> invalid_edge
    |> lift_naming_err

(* check edges and nodes ids and src dest:*)
fun check_src_dest locs =
    let
      fun inner (e as (src, dest)) =
          if not (List.exists (is_same src) locs) then
            e |> invalid_edge_err
          else if not (List.exists (is_same dest) locs) then
            e |> invalid_edge_err
          else return
    in
      combine_map inner
    end

fun check_dups xs =
    case duplicates (fn ("", _) => false |
                        (_, "") => false |
                        (x, y) => x = y)
                                            xs of
            [] => return |
            dups => fail (map (duplicate #> naming #> comp_err) dups)

fun check_committed is_location_id =
    combine_map (fn id => if is_location_id id then return
                         else id |> unknown_id |> Error.lift_naming_err)

fun check_automaton ({nodes, edges, initial, committed} : automaton) =
    let
      val ids = List.map #id nodes
      val names = List.map #name nodes
      val location_id_set = Inttab.make_set ids
      val src_dest = List.map (fn e => (#source e, #target e)) edges
    in
      check_dups names
      <|> check_dups (map Int.toString ids)
      <|> check_committed (Inttab.defined location_id_set) committed
      <|> check_dups (map Int.toString committed)
      <|> check_initial initial ids
      <|> check_src_dest ids src_dest
      |> bindR (K return)
    end

fun check_bound (var as {lower, upper, ...} : Syntax.var) =
    if lower <= 0 andalso upper >= 0 then return
    else "Variables need to have 0 in their bound" |> GeneralError |> lift_err

fun check_bounds vars = combine_map check_bound vars

fun check_network automata clocks vars formula =
    check_amb_vars_clocks clocks vars
    <|> check_dups clocks <|> check_dups vars
    <|> combine_map (snd #> check_automaton) automata
    |> bindR (K return)

(* Compilation: *)

fun cexp_bexp cexp e =
    case e of
            Constraint.Lt (a, _) => cexp a e |
            Constraint.Le (a, _) => cexp a e |
            Constraint.Eq (a, _) => cexp a e |
            Constraint.Ge (a, _) => cexp a e |
            Constraint.Gt (a, _) => cexp a e

fun cexp_invar clocks vars a x =
    let
      fun is_clock c = List.exists (is_same c) clocks
      fun is_var v = List.exists (is_same v) vars
    in
      if is_var a then a |> var_invar |> lift_constr_err
      else if is_clock a then succeed x
      else a |> unknown_var |> lift_naming_err
    end

(* guards and invariants: *)
fun check_invar clocks vars =
    let
      fun inner a =
          cexp_invar clocks vars a
    in
      combine_map (cexp_bexp inner)
    end

fun pred_bexp_constr p =
    Constraint.ids #> p

fun partition_single ls =
    ls
    |> List.partition (Guard.is_exp (Constraint.ids #> Difference.is_single)
                                    (Exn.impossible ()))

fun compile_invariant clocks vars =
    Invariant.chop
    #> (check_invar clocks vars)


fun check_diff clocks vars =
    let
      fun is_clock c = List.exists (is_same c) clocks
      fun is_var v = List.exists (is_same v) vars
      fun do_check id = case (is_clock id, is_var id) of
                            (* (true, true) => Can not happen is checked before *)
                            (true, _) => Exp.Cexp id |> succeed |
                            (_, true) => Exp.Vexp id |> succeed |
                            (false, false) => id
                                              |> unknown_var
                                              |> lift_naming_err
      val vcexp_diff = lift_constr_err oo clock_and_var
      val cc_single = Exp.map Difference.Single #> succeed
      val cc_diff = Exp.join (vcexp_diff)
                    #> mapR (Exp.map Difference.Diff)
    in
      Difference.check do_check cc_single cc_diff
    end

fun check_single_constraint clocks vars =
    Constraint.check (check_diff clocks vars)

fun check_ors g e =
    if Exp.is_vexp e then succeed e
    else disj (Guard.to_string g)
              (Exp.get_exp e |> Constraint.to_string Difference.to_string)
         |> lift_constr_err

fun check_guard g clocks vars =
    let
      fun single_check e =
          Guard.check (check_single_constraint clocks vars) (check_ors g) e
    in
      combine_map single_check
    end

fun partition_guards ls =
    List.partition (Guard.is_exp Exp.is_cexp false) ls
    |> apply2 (map (Guard.map Exp.get_exp))
    |> apfst (map Guard.get_constraint)

fun partition_diff_guards ls =
    List.partition (Constraint.ids #> Difference.is_single) ls

fun compile_guards clocks vars g =
    Guard.chop (op ::) [] g
    |> check_guard g clocks vars
    |> mapR partition_guards
    |> mapR (apfst partition_diff_guards)

val diff_vcexp =
    (constr_err #> comp_err #> single) oo clock_and_var

fun unknown v =
    v |> unknown_var |> lift_naming_err

fun compile_update clocks vars upd =
    let
      val is = flip (List.exists o is_same)
      val is_clock = is clocks
      val is_var = is vars
      fun check_cexp_vexp a = (is_clock a, is_var a)
      fun check a =
          case check_cexp_vexp a of
              (true, true) => a |> ambg_var |> naming |> lift_comp_err |
              (true, _) => succeed (fail a) |
              (_, true) => succeed (succeed a) |
              _ => a |> unknown_var |> naming |> lift_comp_err
      val helper = uncurry (Either.same (curry Exp.Cexp) (curry Exp.Vexp) diff_vcexp)
      fun reset f i a = Reset (a, i) |> f
      fun shift f i x = Shift (x, i) |> f
    in
      case upd of
          Reset (a, i) => check a
                                |> mapR (either (reset Exp.Cexp i)
                                                (reset Exp.Vexp i)) |
          Copy (x, y) => check x <|> check y
                         |> bindR helper |> mapR (Exp.map Copy) |
          Shift (x, i) => check x
                          |> mapR (either (shift Exp.Cexp i)
                                          (shift Exp.Vexp i)) |
          Update (x, y, c) => check x <|> check y
                              |> bindR helper
                              |> mapR (Exp.map (fn (x ,y) => Update (x, y, c)))
    end

fun partition_cexp_vexp ls =
    List.partition (Exp.is_cexp) ls
    |> apply2 (map Exp.get_exp)

fun compile_updates clocks vars =
    combine_map (compile_update clocks vars)
    #> mapR partition_cexp_vexp

fun compile_edge clocks vars ({source, target, guard, label, update} : edge) =
    compile_guards clocks vars guard
    <|>  compile_updates clocks vars update
    |> mapR (fn (((g_s, g_diag), g_data), (upd_c, upd_v))
                  => {
                         source = source,
                         target = target,
                         g_single = g_s,
                         g_diag = g_diag,
                         g_data = g_data,
                         label = label,
                         clock_updates = upd_c,
                         var_updates = upd_v
               }
              )

fun compile_node clocks vars ({id, name, invariant} : node) =
    compile_invariant clocks vars invariant
    |> mapR (fn invar => {id = id, name = name, invariant = invar})


fun compile_automaton is_broadcast clocks vars
                      ({nodes, edges, initial, committed } : automaton) =
    combine_map (compile_edge clocks vars) edges
    <|> combine_map (compile_node clocks vars) nodes
    |> bindR (fn (E, V) => mapR (rpair V)
                                (Util.partition_labels is_broadcast E))
    |> mapR (fn (E,V) =>
                let
                  val (internal,
                       edges_in,
                       edges_out,
                       broadcast_in,
                       broadcast_out) = E
                in
                  {
                    edges_internal = internal,
                    edges_in = edges_in,
                    edges_out = edges_out,
                    broadcast_in = broadcast_in,
                    broadcast_out = broadcast_out,
                    nodes = V,
                    initial = initial,
                    committed = committed
                  }
                end
            )

fun compile_net is_broadcast clocks vars =
    combine_map
      (fn (k, v) => compile_automaton is_broadcast clocks vars v
                    |> mapR (pair k))

fun network ({automata, clocks, vars, formula, broadcast_channels} : network) =
    let
      val vars' = List.map (#name) vars
      val broadcast_set = Symtab.make_set broadcast_channels
      val is_broadcast = Symtab.defined broadcast_set
    in
      (
        check_network automata clocks vars' formula
        <|> check_bounds vars
        <|> check_dups broadcast_channels
      )
      <|> (compile_net is_broadcast clocks vars' automata
      <|> check_formula automata clocks vars' formula)
      |> mapR (fn (_,(tas, f)) =>
                      {
                        automata = tas,
                        clocks = clocks,
                        vars = vars,
                        formula = f,
                        broadcast_channels = broadcast_channels
                      }
                  )
    end
end
