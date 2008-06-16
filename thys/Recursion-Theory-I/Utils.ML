(*  Title:      Recursion-Theory-I/Utils.ML
    Author:     Michael Nedzelsky, email: MichaelNedzelsky <at> yandex <dot> ru

Some utilities for work with primitive recursive functions.
*)

val pr_comp1_1 = thm "pr_comp1_1"
val pr_comp1_2 = thm "pr_comp1_2"
val pr_comp1_3 = thm "pr_comp1_3"
val pr_comp2_1 = thm "pr_comp2_1"
val pr_comp2_2 = thm "pr_comp2_2"
val pr_comp2_3 = thm "pr_comp2_3"
val pr_comp3_1 = thm "pr_comp3_1"
val pr_comp3_2 = thm "pr_comp3_2"
val pr_comp3_3 = thm "pr_comp3_3"

(********* List of known primitive recursive functions. **************)
val pr_list_ref = ref [thm "pr_zero", thm "pr_suc",
                       thm "pr_id1_1", thm "pr_id2_1", thm "pr_id2_2",
                       thm "pr_id3_1", thm "pr_id3_2", thm "pr_id3_3"]

fun get_pr_list () = !pr_list_ref

fun add_to_pr_list str = pr_list_ref := (thm str) :: (!pr_list_ref)

fun add_thm_to_pr_list th = pr_list_ref := th :: (!pr_list_ref)

(******** Utility functions. ***************)

exception BadArgument

fun extract_prop_arg (Const ("prop", _) $ t)  = t
  | extract_prop_arg  _ = raise BadArgument

fun extract_trueprop_arg (Const ("Trueprop", _) $ t)  = t
  | extract_trueprop_arg  _ = raise BadArgument

fun extract_set_args (Const ("op :", _) $ t1 $ t2)  = (t1, t2)
  | extract_set_args  _ = raise BadArgument

fun get_num_by_set "PRecFun.PrimRec1" = 1
  | get_num_by_set "PRecFun.PrimRec2" = 2
  | get_num_by_set "PRecFun.PrimRec3" = 3
  | get_num_by_set _ = raise BadArgument

fun remove_abs (Abs (_, _, t)) = remove_abs t
  | remove_abs t = t

fun extract_free_from_app (t1 $ t2) (n:int) = extract_free_from_app t1 (n+1)
  | extract_free_from_app (Free (s, tp)) n = (s, tp, n)
  | extract_free_from_app (Const (s, tp)) n = (s, tp, n)
  | extract_free_from_app _ n = raise BadArgument

fun extract_free_arg t = extract_free_from_app (remove_abs t) 0

fun get_comp_by_indexes (1,1) = pr_comp1_1
  | get_comp_by_indexes (1,2) = pr_comp1_2
  | get_comp_by_indexes (1,3) = pr_comp1_3
  | get_comp_by_indexes (2,1) = pr_comp2_1
  | get_comp_by_indexes (2,2) = pr_comp2_2
  | get_comp_by_indexes (2,3) = pr_comp2_3
  | get_comp_by_indexes (3,1) = pr_comp3_1
  | get_comp_by_indexes (3,2) = pr_comp3_2
  | get_comp_by_indexes (3,3) = pr_comp3_3
  | get_comp_by_indexes _ = raise BadArgument

(* t = [Cons ("==>", tp)...] $ ... *)
fun is_impl_first (Const("==>",_) $ _) = true
  | is_impl_first _ = false

(* Result = Cons("Trueprop", tp) $ ... *)
fun extract_right_expr (t:term) =
  case t of
      t1 $ t2 => (if (is_impl_first t1) then (extract_right_expr t2) else t)
    | _ => t

fun term_to_string t =
  case t of
      Const (str, tp) => "Const(" ^ str ^ ",tp)"
    | Free (str, tp) => "Free(" ^ str ^ ",tp)"
    | Var (indexname, tp) => "Var"
    | Bound n => "Bound " ^ (Int.toString n)
    | Abs (a, tp, u) => "Abs(" ^ a ^ ", tp, [" ^ (term_to_string u) ^ "])"
    | t1 $ t2 => "[" ^ (term_to_string t1) ^ "] $ [" ^ (term_to_string t2) ^ "]"

(************ Tactic. ***************)

fun pr_comp_tac ctxt = SUBGOAL (fn (t,i) =>
  let
    val t = extract_trueprop_arg (extract_right_expr t)
    val (t1, t2) = extract_set_args t
    val n2 =
      let
        val Const(s, _) = t2
      in
        get_num_by_set s
      end
    val (name, _, n1) = extract_free_arg t1
    val comp = get_comp_by_indexes (n1, n2)
  in
    res_inst_tac ctxt [(("f", 0), ProofContext.revert_skolem ctxt name)] comp i
  end
  handle BadArgument => no_tac)

fun pr_tac ctxt = cut_facts_tac (get_pr_list()) 1 THEN
                      REPEAT (assume_tac 1 ORELSE pr_comp_tac ctxt 1)
fun pr_ex_tac ctxt ls  = cut_facts_tac ((get_pr_list()) @ ls) 1 THEN
                      REPEAT (assume_tac 1 ORELSE pr_comp_tac ctxt 1)
