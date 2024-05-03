(*
 * Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
 * Copyright (c) 2022 Apple Inc. All rights reserved.
 *
 * SPDX-License-Identifier: BSD-2-Clause
 *)

(*
 * Prettify bound variable names in L2 monadic bodies.
 *)

structure PrettyBoundVarNames =
struct

(* Return the first result, unless it is NONE, in which case return the
 * second. *)
fun try_both a b =
  case (a ()) of
    SOME x => SOME x
  | NONE => b ()

local
  fun is_callee_const callee_names t =  
    case strip_comb t of
      (Const (n,_) , _) =>  member (op =) callee_names n
    | (Free (n,_) , _) => member (op =) callee_names n
    | _ => false
in
fun is_lifted_call callee_names (Abs (x,T,t)) = 
  
  not (Term.is_dependent t) andalso is_callee_const callee_names t 
  | is_lifted_call callee_names t = is_callee_const callee_names t

fun ret_vars_call callee_names t = 
  case t of
    (Const (@{const_name "L2_call"}, _) $ _ $ _ $ ns) =>
      SOME (CLocals.dest_name_hints ns)
   | (Const (@{const_name "L2_VARS"}, _) $ _ $ ns) =>
      SOME (CLocals.dest_name_hints ns)
   | (Const (@{const_name "gets_the"}, _) $ x) =>
      ret_vars_call callee_names x
   | (Const (@{const_name "gets"}, _) $ x) =>
      ret_vars_call callee_names x
   | (Const (@{const_name "ogets"}, _) $ x) =>
      ret_vars_call callee_names x
   | t => if is_lifted_call callee_names t 
       then SOME ["ret"] (* make up a name *)  
       else NONE;
end

(* Get a list of names that the given block of code returns. *)
fun get_var_names_ret callee_names t =
  case t of
     (Abs (_, _, V $ Bound 0)) => get_var_names_ret callee_names V
  |  (Abs (_, _, V)) => get_var_names_ret callee_names V
  | (Const (@{const_name "case_prod"}, _) $ M $ _) =>
      get_var_names_ret callee_names M
  | (Const (@{const_name "case_prod"}, _) $ M) =>
      get_var_names_ret callee_names M
  | (Const (@{const_name "L2_VARS"}, _) $
      (Const (@{const_name "yield"}, _) $ (Const (@{const_name "Exn"}, _) $ _)) $ _) =>
      NONE
  | (Const (@{const_name "L2_VARS"}, _) $ x $ v) =>
     let
       val ns = CLocals.dest_name_hints v
     in if null ns then get_var_names_ret callee_names x else SOME ns end
  | (Const (@{const_name "L2_VARS"}, _) $ x $ v $ s) =>
     let
       val ns = CLocals.dest_name_hints v
     in if null ns then get_var_names_ret callee_names x else SOME ns end
  | (Const (@{const_name "L2_gets"}, _) $ _ $ v) =>
      SOME (CLocals.dest_name_hints v)
  | (Const (@{const_name "L2_unknown"}, _) $ v) =>
      SOME (CLocals.dest_name_hints v)
  | (Const (@{const_name "L2_while"}, _) $ _ $ _ $ _ $ v) =>
      SOME (CLocals.dest_name_hints v)
  | (Const (@{const_name "L2_throw"}, _) $ _ $ _) =>
      NONE
  | (Const (@{const_name "L2_condition"}, _) $ _ $ L $ R) =>
      try_both
        (fn () => get_var_names_ret callee_names L)
        (fn () => get_var_names_ret callee_names R)
  | (Const (@{const_name "condition"}, _) $ _ $ L $ R) =>
      try_both
        (fn () => get_var_names_ret callee_names L)
        (fn () => get_var_names_ret callee_names R)
  | (Const (@{const_name "ocondition"}, _) $ _ $ L $ R) =>
      try_both
        (fn () => get_var_names_ret callee_names L)
        (fn () => get_var_names_ret callee_names R)
  | (Const (@{const_name "HOL.If"}, _) $ _ $ L $ R) =>
      try_both
        (fn () => get_var_names_ret callee_names L)
        (fn () => get_var_names_ret callee_names R)
  | (Const (@{const_name "L2_seq"}, _) $ _ $ R) =>
      get_var_names_ret callee_names R
  | (Const (@{const_name "bind"}, _) $ _ $ R) =>
      get_var_names_ret callee_names  R
  | (Const (@{const_name "obind"}, _) $ _ $ R) =>
      get_var_names_ret callee_names  R
  | (Const (@{const_name "HOL.Let"}, _) $ _ $ R) =>
      get_var_names_ret callee_names  R
  | (Const (@{const_name "L2_guarded"}, _) $ _ $ B) =>
      get_var_names_ret callee_names B
  | (Const (@{const_name "L2_catch"}, _) $ L $ R) =>
      try_both
        (fn () => get_var_names_ret callee_names L)
        (fn () => get_var_names_ret callee_names R)
  | (Const (@{const_name "catch"}, _) $ L $ R) =>
      try_both
        (fn () => get_var_names_ret callee_names L)
        (fn () => get_var_names_ret callee_names R)
  | (Const (@{const_name "L2_try"}, _) $ L) =>
      get_var_names_ret callee_names L
  | (Const (@{const_name "try"}, _) $ L) =>
      get_var_names_ret callee_names L
  | (Const (@{const_name "finally"}, _) $ L) =>
      get_var_names_ret callee_names L
  | (Const (@{const_name "liftE"}, _) $ x ) =>
      get_var_names_ret callee_names  x
  | (Const (@{const_name "yield"}, _) $ (Const (@{const_name "Result"}, _) $ x)) =>
      get_var_names_ret callee_names x
  | (Const (@{const_name "gets"}, _) $ x) => 
      get_var_names_ret callee_names x 
  | (Const (@{const_name "ogets"}, _) $ x) => 
      get_var_names_ret callee_names x 
  | (Const (@{const_name "gets_the"}, _) $ x) =>
      get_var_names_ret callee_names x
  | (Const (@{const_name "exec_concrete"}, _) $ _ $ f) =>
      get_var_names_ret callee_names f
  | (Const (@{const_name "exec_abstract"}, _) $ _ $ f) =>
      get_var_names_ret callee_names f
  | t => ret_vars_call callee_names t

(* Get a list of names that the given block of code throws. *)
fun get_var_names_throw t =
  case t of
    (Abs (_, _, V)) => get_var_names_throw V
  | (Const (@{const_name "case_prod"}, _) $ M $ _) =>
      get_var_names_throw M
  | (Const (@{const_name "case_prod"}, _) $ M) =>
      get_var_names_throw M
  | (Const (@{const_name "L2_gets"}, _) $ _ $ _) =>
      NONE
  | (Const (@{const_name "L2_while"}, _) $ _ $ B $ _ $ _) =>
      get_var_names_throw B
  | (Const (@{const_name "L2_throw"}, _) $ _ $ v) =>
      SOME (CLocals.dest_name_hints v)
  | (Const (@{const_name "L2_VARS"}, _) $
      (Const (@{const_name "yield"}, _) $ (Const (@{const_name "Exn"}, _) $ _)) $ v) =>
      SOME (CLocals.dest_name_hints v)
  | (Const (@{const_name "L2_VARS"}, _) $ 
       ((Const (@{const_name "map_value"}, _) $ (Const (@{const_name "Spec_Monad.map_exn"}, _) $ _)) $ _) $ v) =>
      SOME (CLocals.dest_name_hints v)
  | (Const (@{const_name "L2_call"}, _) $ _ $ _ $ v) =>
      SOME (CLocals.dest_name_hints v)
  | (Const (@{const_name "L2_guarded"}, _) $ _ $ B) =>
      get_var_names_throw B
  | (Const (@{const_name "L2_condition"}, _) $ _ $ L $ R) =>
      try_both
        (fn () => get_var_names_throw L)
        (fn () => get_var_names_throw R)
  | (Const (@{const_name "condition"}, _) $ _ $ L $ R) =>
      try_both
        (fn () => get_var_names_throw L)
        (fn () => get_var_names_throw R)
  | (Const (@{const_name "L2_seq"}, _) $ L $ R) =>
      try_both
        (fn () => get_var_names_throw L)
        (fn () => get_var_names_throw R)
  | (Const (@{const_name "bind"}, _) $ L $ R) =>
      try_both
        (fn () => get_var_names_throw L)
        (fn () => get_var_names_throw R)
  | (Const (@{const_name "L2_catch"}, _) $ _ $ R) =>
      get_var_names_throw R
  | (Const (@{const_name "catch"}, _) $ _ $ R) =>
      get_var_names_throw R
  | (Const (@{const_name "L2_VARS"}, _) $ t) =>
      get_var_names_throw t
  | _ => NONE

(* Regenerate bound variable names based on annotations on "L2_gets" and
 * "L2_throw" statements. *)
local
fun gen_pretty_split_vars exit (SOME (x::xs)) (Abs (_, T, R))
      = let val name = if exit then "exit" else x in Abs (name, T, gen_pretty_split_vars exit (SOME xs) R) end
  | gen_pretty_split_vars exit _ (Abs (_, T, R))
      = let val name = if exit then "exit" else Name.uu_ in Abs (name, T, R) end
  | gen_pretty_split_vars exit (SOME (x::xs)) (Const (@{const_name "case_prod"}, T) $ Abs (_, T', R))
      = (Const (@{const_name "case_prod"}, T) $ Abs (x, T', (gen_pretty_split_vars exit (SOME xs) R)))
  | gen_pretty_split_vars exit _ (Const (@{const_name "case_prod"}, T) $ Abs (_, T', R))
      = (Const (@{const_name "case_prod"}, T) $ Abs (Name.uu_, T', (gen_pretty_split_vars exit NONE R)))
  | gen_pretty_split_vars _ _ t = t

val pretty_split_vars = gen_pretty_split_vars false

(* Add state variable "s" for L2_while,
   renaming any existing "s" if necessary *)
fun map_option _ NONE = NONE
  | map_option f (SOME x) = SOME (f x)
fun sprime str = if str = "s" ^ String.implode (List.tabulate (String.size str - 1, K #"'"))
                    then str ^ "'" else str
fun while_add_st_var vars = (map sprime vars) @ ["s"]
in
fun pretty_bound_vars callee_consts t =
  case t of
    (Const (@{const_name "L2_seq"}, t1) $ L $ R) =>
      let
         val names = get_var_names_ret callee_consts L
      in (Const (@{const_name "L2_seq"}, t1) $ L $ (pretty_split_vars names R)) end
  | (Const (@{const_name "Spec_Monad.bind"}, t1) $ L $ R) =>
      let
         val names = get_var_names_ret callee_consts L
      in (Const (@{const_name "Spec_Monad.bind"}, t1) $ L $ (pretty_split_vars names R)) end
 | (Const (@{const_name "obind"}, t1) $ L $ R) =>
      let
         val names = get_var_names_ret callee_consts L
      in (Const (@{const_name "obind"}, t1) $ L $ (pretty_split_vars names R)) end
 | (Const (@{const_name "HOL.Let"}, t1) $ L $ R) =>
      let
         val names = get_var_names_ret callee_consts L
      in (Const (@{const_name "HOL.Let"}, t1) $ L $ (pretty_split_vars names R)) end
  | (Const (@{const_name "L2_catch"}, t1) $ L $ R) =>
      (Const (@{const_name "L2_catch"}, t1) $ L $ (gen_pretty_split_vars true (get_var_names_throw L) R))
  | (Const (@{const_name "catch"}, t1) $ L $ R) =>
      (Const (@{const_name "catch"}, t1) $ L $ (gen_pretty_split_vars true (get_var_names_throw L) R))
  | (Const (@{const_name "L2_while"}, t1) $ C $ B $ i $ n) =>
    let
      val names = get_var_names_ret callee_consts t
    in
      (Const (@{const_name "L2_while"}, t1)
        $ (pretty_split_vars (map_option while_add_st_var names) C)
        $ (pretty_split_vars names B)
        $ i $ n)
    end
  | (Const (@{const_name "L2_VARS"}, tv) $ (Const (@{const_name "whileLoop"}, t1) $ C $ B $ i) $ n) =>
    let
      val names = get_var_names_ret callee_consts t
    in
      (Const (@{const_name "L2_VARS"}, tv) $ 
        (Const (@{const_name "whileLoop"}, t1) $ 
          (pretty_split_vars (map_option while_add_st_var names) C) $ 
          (pretty_split_vars names B) $ i) $ 
        n)
    end
  | (Const (@{const_name "L2_VARS"}, tv) $ (Const (@{const_name "owhile"}, t1) $ C $ B $ i) $ n) =>
    let
      val names = get_var_names_ret callee_consts t
    in
      (Const (@{const_name "L2_VARS"}, tv) $ 
        (Const (@{const_name "owhile"}, t1) $ 
          (pretty_split_vars (map_option while_add_st_var names) C) $ 
          (pretty_split_vars names B) $ i) $ 
        n)
    end
  | (Const (@{const_name "L2_VARS"}, tv) $ (bdy as (Abs (pn, \<^Type>\<open>ptr T\<close>, with_fresh_stack_ptr))) $ n) =>
    let
      val names = get_var_names_ret callee_consts t |> Option.map (map TermsTypes.mk_local_ptr_name)
    in
      (Const (@{const_name "L2_VARS"}, tv) $ 
       (pretty_split_vars names bdy) $ 
        n)
    end
  | _ => t
end

(* Apply "f" to every subterm, bottom-up. *)
fun map_term_bottom f (a $ b)
      = f ((map_term_bottom f a) $ (map_term_bottom f b))
  | map_term_bottom f (Abs (v, t, b))
      = f (Abs (v, t, map_term_bottom f b))
  | map_term_bottom f t = f t

(* Generate a theorem that "ct_l == ct_r", assuming it can be trivially proven. *)
fun rename_abs_thm ctxt ct_l ct_r =
let
  val input_type = fastype_of (Thm.term_of ct_l)
  val eq_op = Thm.cterm_of ctxt (
      Const (@{const_name "Pure.eq"}, input_type --> input_type --> @{typ prop}))
  val result = Drule.list_comb (eq_op, [ct_l, ct_r])
in
  Goal.init result
  |> simp_tac (put_simpset HOL_basic_ss ctxt) 1 |> Seq.hd
  |> Goal.finish ctxt
end


(* Generate a thm of the form "A == B", where "B" has pretty bound variable
 * names. *)
fun pretty_bound_vars_thm keep_going ctxt callee_names ct =
let
  val _ = Utils.verbose_msg 5 ctxt (fn _ => "pretty_bound_vars input:\n " ^ Syntax.string_of_term ctxt (Thm.term_of ct))
  val rhs = map_term_bottom (pretty_bound_vars callee_names) (Thm.term_of ct)
  val _ = Utils.verbose_msg 5 ctxt (fn _ => "pretty_bound_vars output:\n " ^ Syntax.string_of_term ctxt rhs)
  (* We want to track down stray uu_ that appear in user-visible
   * output. So this code fails hard if it finds one. *)
  fun non_eta (body $ Bound 0) = body (* ignore eta expanded corner case *)
    | non_eta body = body
  fun detect_visible_bad_vars barf term =
    case term of
        (Abs (var, typ, body)) => (if Term.is_dependent (non_eta body) then barf var typ term else ();
                                   detect_visible_bad_vars barf body)
      | f $ x => (detect_visible_bad_vars barf f; detect_visible_bad_vars barf x)
      | _ => ()
  fun barf_uu var typ term =
    if String.isSuffix Name.uu_ var andalso typ <> @{typ unit}
       then Utils.CTERM_non_critical keep_going
                ("autocorres: Internal var " ^ var ^ "::" ^
                 @{make_string} typ ^ " is exposed.")
                [ct, Thm.cterm_of ctxt rhs]
       else ()
  val _ = detect_visible_bad_vars barf_uu rhs
  val crhs = Thm.cterm_of ctxt rhs
  val eq = rename_abs_thm ctxt ct crhs
in
  eq
end

end
