(*
 * Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
 * Copyright (c) 2022 Apple Inc. All rights reserved.
 *
 * SPDX-License-Identifier: BSD-2-Clause
 *)

(*
 * Miscellaneous functions and utilities.
 *
 *)

signature AC_PROOF_DATA =
sig
  type T
  val get: Proof.context -> T
  val put: T -> Proof.context -> Proof.context
  val map: (T -> T) -> Proof.context -> Proof.context
  val transfer: Proof.context -> Proof.context -> Proof.context
end;

functor AC_Proof_Data(Data: PROOF_DATA_ARGS): AC_PROOF_DATA =
struct
structure Data = Proof_Data(Data);
open Data;
fun transfer from_ctxt to_ctxt = put (get from_ctxt) to_ctxt;
end;

infix 1 force_then_conv;
infix 1 then_force_conv;

(* omits reflexive shortcut for cv2 to allow renaming of bound variables *)
fun (cv1 then_force_conv cv2) ct =
  let
    val eq1 = cv1 ct;
    val eq2 = cv2 (Thm.rhs_of eq1);
  in
    if Thm.is_reflexive eq1 then eq2
    else Thm.transitive eq1 eq2
  end;

(* omits reflexive shortcut for cv1 to allow renaming of bound variables *)
fun (cv1 force_then_conv cv2) ct =
  let
    val eq1 = cv1 ct;
    val eq2 = cv2 (Thm.rhs_of eq1);
  in
    if Thm.is_reflexive eq2 then eq1
    else Thm.transitive eq1 eq2
  end;

structure Utils =
struct
  open Utils
fun dest_name_type t = 
  case t of            
     Free (n, T) => (n, T)
  | Var ((n,i), T) => (n, T)
  | Const (n, T) => (n, T)
  | _ => raise TERM ("dest_name_type: unexpected term", [t]) 

fun transitive eq1 eq2 = Thm.transitive (safe_mk_meta_eq eq1) (safe_mk_meta_eq eq2) 

(* Convert a term into a string. *)
fun term_to_string ctxt t =
  Syntax.check_term ctxt t
  |> Thm.cterm_of ctxt
  |> @{make_string}

fun pretty_term_typed ctxt t =
  Pretty.block [Syntax.pretty_term ctxt t, Pretty.str ": ", Syntax.pretty_typ ctxt (fastype_of t)]
fun string_of_term_typed ctxt ts = pretty_term_typed ctxt ts |> Pretty.string_of
fun pretty_terms_typed ctxt ts =
  Pretty.list "[" "]" (map (pretty_term_typed ctxt) ts)
fun string_of_terms_typed ctxt ts = pretty_terms_typed ctxt ts |> Pretty.string_of

(* Warning with 'autocorres' prefix. *)
fun ac_warning str = warning ("autocorres: " ^ str)

(* List functions that should really be included in PolyML. *)

fun zipWith f (x::xs) (y::ys) = f x y :: zipWith f xs ys
  | zipWith _ _ _ = []
fun zip xs ys = zipWith (curry I) xs ys
fun zip3 (x::xs) (y::ys) (z::zs) = ((x,y,z)::(zip3 xs ys zs))
  | zip3 _ _ _ = []

fun findIndex p =
  let fun find _ [] = NONE
        | find n (x::xs) = if p x then SOME (x, n) else find (n+1) xs
  in find 0 end

fun enumerate xs = let
  fun enum _ [] = []
    | enum n (x::xs) = (n, x) :: enum (n+1) xs
  in enum 0 xs end

fun nubBy _ [] = []
  | nubBy f (x::xs) = x :: filter (fn y => f x <> f y) (nubBy f xs)

fun accumulate f acc xs = let
  fun walk results acc [] = (results [], acc)
    | walk results acc (x::xs) = let
        val acc' = f x acc;
        in walk (results o cons acc') acc' xs end;
  in walk I acc xs end;

fun fetch_thm name ctxt = 
  let
    val thm = Proof_Context.get_thm ctxt name
  in 
    thm
  end

fun fetch_thms name ctxt = Proof_Context.get_thms ctxt name

fun export_prop {closed} inner outer prop =
  let
    val dummy_thm = Goal.prove_internal inner [] prop (fn _ => ALLGOALS (Skip_Proof.cheat_tac inner)) 
  in
    dummy_thm |> singleton (Proof_Context.export inner outer) 
    |> closed? Thm.forall_intr_vars 
    |> Thm.cprop_of
  end

(*** evaluate function in locale, preserving slots ***)

fun transfer_slots slots from to =
  to |> fold (fn transfer => fn ctxt => transfer from ctxt) slots

(* Note that the result is the raw-result from the locale 'name' *)
fun gen_in_locale_result slots name f lthy =
  let
    val bottom_locale = Named_Target.bottom_locale_of lthy
    val (reenter, inner_lthy) = 
      if bottom_locale = SOME name (* if we are already in the locale, stay there *)
      then (Local_Theory.end_nested, snd (Local_Theory.begin_nested lthy))
      else Target_Context.switch_named_cmd (SOME (name, Position.none)) (Context.Proof lthy) |> apfst (fn exit => Context.proof_of o exit)
    val (res, inner_lthy') = f (transfer_slots slots lthy inner_lthy)
    val lthy' = inner_lthy' 
      |> reenter |> transfer_slots slots inner_lthy'
  in
      (res, lthy') 
  end

fun gen_in_locale slots name f lthy =
  lthy |> gen_in_locale_result slots name (fn lthy => ((), f lthy)) |> snd

fun gen_eval_in_locale slots name f lthy =
  let
    val (_, inner_lthy) = Target_Context.switch_named_cmd (SOME (name, Position.none)) (Context.Proof lthy)
    val res = f (transfer_slots slots lthy inner_lthy)
  in
    res
  end

fun gen_in_theory_result slots f lthy =
  let
    val reinit = if Named_Target.is_theory lthy 
      then Named_Target.theory_init else Named_Target.init [] (the (Named_Target.locale_of lthy))
    val thy = lthy |> Local_Theory.exit_global
    val (res, thy') = f thy
    val lthy' = thy' |> reinit |> transfer_slots slots lthy
  in
      (res, lthy') 
  end

fun gen_in_theory slots f lthy =
  lthy |> gen_in_theory_result slots (fn thy => ((), f thy)) |> snd

fun gen_in_theory_result' slots f lthy =
  let
    val reinit = if Named_Target.is_theory lthy 
      then Named_Target.theory_init else Named_Target.init [] (the (Named_Target.locale_of lthy))
    val (res, lthy') = lthy |> Local_Theory.exit_global 
      |> Named_Target.theory_init 
      |> transfer_slots slots lthy 
      |> f 
    val lthy'' = lthy' |> Local_Theory.exit_global |> reinit |> transfer_slots slots lthy'
  in
      (res, lthy'') 
  end

fun gen_in_theory' slots f lthy =
  lthy |> gen_in_theory_result' slots (fn thy => ((), f thy)) |> snd



(*
 * Define a constant "name" of value "term" into the local theory "lthy".
 *
 * Arguments "args" to the term may be given, which consist of a list of names
 * and types.
 *)
fun define_const_args name qualify concealed term args decls attrs lthy =
  let
    fun maybe_hide x = if concealed then Binding.concealed x else x

    (* Generate a header for the term. *)
    val head = betapplys (Free (name, (map snd args) ---> fastype_of term), args |> map Free)
    val new_term = Logic.mk_equals (head, term)

    val def_binding = Binding.make (name ^ "_def", \<^here>) |> maybe_hide |> qualify
    (* Define the constant. *)
   val lthy = lthy 
   val ((lhs, (def_name, thm)), lthy) =
        Specification.definition (SOME (maybe_hide (Binding.name name), NONE, NoSyn))
            [] [] ((def_binding, attrs), new_term) lthy
       handle ERROR x => (tracing ("define_const_args: " ^ @{make_string} (Thm.cterm_of lthy term)); raise ERROR x)
   val lthy = lthy |> fold (fn thm_decl => thm_decl thm) decls
  in
    ((lhs, def_name, thm), lthy)
  end


fun define_global_const binding concealed term args attribs lthy =
  let
    val _ = @{assert} (Named_Target.is_theory lthy)
    fun maybe_hide x = if concealed then Binding.concealed x else x
    val name = Binding.name_of binding
    (* Generate a header for the term. *)
    val head = betapplys (Free (name, (map snd args) ---> fastype_of term), args |> map Free)
    val new_term = Logic.mk_equals (head, term)

    (* Define the constant. *)
    (* The begin_nested / end_nested block removes hypothesis 
     * Free def_name \<equiv> Const global_const from the lthy 
     *)
    val ((lhs, (def_name, thm)), lthy) = lthy |> Local_Theory.begin_nested |> snd |>
        Specification.definition (SOME (maybe_hide (binding), NONE, NoSyn))
            [] [] ((Binding.empty, attribs), new_term) 
       handle ERROR x => (tracing ("define_global_const: " ^ @{make_string} (Thm.cterm_of lthy term)); raise ERROR x)
    val export = Local_Theory.target_morphism lthy 
  in
    ((Morphism.term export lhs, Morphism.thm export thm), Local_Theory.end_nested lthy)
  end

(*
 * Define a (possibly recursive) set of functions.
 *
 * We take a list of functions. For each function, we have a name, list
 * of arguments, and a body (which is assumed to have a lambda
 * abstraction for each argument).
 *
 * Recursion (and mutual recursion) can be achieved by the body
 * containing a free variable with the name of the function to be called
 * of the correct type.
 *
 * Termination must be able to be automatically proved for recursive
 * function definitions to succeed. This implies that recursive
 * functions must have at least one argument (lest there be no arguments
 * to prove termination on).
 *
 * For example, the input:
 *
 *     [("fact", [("n", @{typ nat}], @{term "%n. if n = 0 then 1 else n * fact (n - 1))})]
 *
 * would define a new function "fact".
 *
 * We return a tuple:
 *
 *   (<list of function definition thms>, <new context>)
 *)
fun define_functions func_defs (qualify: binding -> binding) concealed is_recursive ccpo_name name_decls induct_decls lthy =
let
  fun maybe_hide x = if concealed then Binding.concealed x else x

  (* Define a set of mutually recursive functions. The function package
   * refuses to make a definition that doesn't take any arguments, so we
   * use this strictly for functions with at least one argument. *)
  fun define_recursive_function func_defs lthy =
  let
    (* Automatic pattern completeness / termination methods from
     * the "function" package. *)
    fun pat_completeness_auto ctxt =
      Pat_Completeness.pat_completeness_tac ctxt 1
      THEN auto_tac ctxt
    fun prove_termination lthy =
      Function.prove_termination NONE
        (Function_Common.termination_prover_tac false lthy) lthy

    (* Get the list of function bindings. *)
    val function_bindings = map (fn (name, bname, _, _) =>
        (ccpo_name, (maybe_hide (Binding.name bname), NONE, NoSyn))) func_defs

    (* Get the list of function bodies. *)
    fun mk_fun_term name args body =
    let
      (* Get the type of the function, and generate a free term for it. *)
      val fun_free = Free (name, fastype_of body)

      (* Create a head of the function, with appropriate arguments. *)
      val fun_head = betapplys (fun_free, map Free args)
      val fun_body = betapplys (body, map Free args)
    in
      HOLogic.mk_Trueprop (HOLogic.mk_eq (fun_head, fun_body))
    end
    fun simps_binding bname = 
      let
        val b = Binding.make ("simps", \<^here>) |> Binding.qualify true bname |> maybe_hide
        val qb = qualify b 
      in if qb <> b then qb else Binding.empty end (* avoid duplicate fact declaration *)

    val function_bodies = map (fn (name,bname,args,body) => (name, (simps_binding bname, mk_fun_term bname args body))) func_defs

    fun subsingleton_solver ctxt = ALLGOALS (simp_tac ctxt)
    (* Define the function. *)
    val lthy = lthy 
    val (info, lthy) = 
      lthy 
      |> Mutual_CCPO_Rec.add_fixed_point function_bindings
          (map (fn (name, (b, body)) => (((b, []), body), [], [])) function_bodies)
          (subsingleton_solver) 
   
    val rec_simps = (#simps info) |> map (the_single o snd)
    val inducts = snd (#inducts info) 

    val lthy = lthy 
      |> fold (fn (name, thm) => fold (fn decl => decl name thm) name_decls #> fold (fn decl => decl name inducts) induct_decls) 
      (map fst function_bodies ~~ rec_simps)
  in
    ((#consts info, rec_simps, inducts), lthy)
  end
in
  case (is_recursive, func_defs) of
      (* Single non-recursive function. *)
      (false, [(name,bname, args, body)]) => 
        define_const_args bname qualify concealed (betapplys (body, map Free args)) args (map (rev_app name) name_decls) [] lthy
        |> (fn ((lhs, _, ctxt_thm), def_lthy) => (([lhs],[ctxt_thm], []), def_lthy))

    | (true, _) =>
      (* Recursion or mutual recursion. *)
      define_recursive_function func_defs lthy
end

(* Define a constant "name" of type "term" into the local theory "lthy". *)
fun define_const name term lthy =
  let
    val lthy = lthy |> Local_Theory.begin_nested |> snd
    val ((_, (def_name, thm)), lthy) = Local_Theory.define ((Binding.name name, NoSyn), (Binding.empty_atts, term)) lthy
    val lthy' = Local_Theory.end_nested lthy
    val thm' = Morphism.thm (Local_Theory.target_morphism lthy) thm
  in
    ((def_name, thm'), lthy')
  end

fun define_const_eq name eq lthy =
  let
  
   val ((_, (def_name, _)), lthy) =
        Specification.definition (SOME (Binding.name name, NONE, NoSyn))
            [] [] (Binding.empty_atts, eq) lthy
  in
    (fetch_thm def_name, lthy)
  end

fun define_lemmas name thm_list attribs lthy =
  let
    val ((name, _), lthy) = Local_Theory.note ((Binding.name name, map (Attrib.internal \<^here> o K) attribs), thm_list) lthy
  in
    (fetch_thms name, lthy)
  end

(* Define a single lemma into the local theory. *)
fun define_lemma binding attribs thm lthy =
  let
    val ((name, [thm]), lthy) = Local_Theory.note ((binding, map (Attrib.internal \<^here> o K) attribs), [thm]) lthy
  in
    (thm, lthy)
  end

(* Define a single lemma into the local theory. *)
fun define_lemma' binding decls thm lthy =
  let
    val ((name, [thm]), lthy) = Local_Theory.note ((binding, []), [thm]) lthy
    val lthy = lthy |> fold (fn decl => decl thm) decls
  in
    (thm, lthy)
  end


(* Return an instance of the term "name". *)
fun get_term ctxt name =
  Syntax.read_term ctxt name

(* Calculate a fixpoint. *)
fun fixpoint f eq init =
  let
    val new = f init
  in
    if (eq (new, init)) then init else (fixpoint f eq new)
  end

(*
 * Convenience function for generating types.
 *
 *   gen_typ @{typ "'a + 'b"} [@{typ word32}, @{typ nat}]
 *
 * will generate @{typ "word32 + nat"}
 *)
fun gen_typ t params =
  let
    fun typ_convert (TFree (a, _)) =
        String.extract (a, 1, NONE)
        |> (fn x => ord x - ord "a")
        |> nth params
      | typ_convert x = x
  in
    Term.map_atyps typ_convert t
  end

(* Anonymous variable name for a lambda abstraction. *)
(* TODO this is unused *)
val dummy_abs_name = Name.internal Name.uu

(*
 * Determine if the given term contains the given subterm.
 *)
fun contains_subterm needle haysack =
  exists_subterm (fn a => a = needle) haysack

(*
 * cterm_instantiate with named parameter.
 *
 * (from records package)
 *)
fun named_cterm_instantiate ctxt values thm =
let
  fun match name ((name', _), _) = name = name'
  fun getvar name =
    (case find_first (match name) (Term.add_vars (Thm.prop_of thm) []) of
          SOME var =>  #1 var
        | NONE => raise THM ("named_cterm_instantiate: " ^ name, 0, [thm]));
in
  infer_instantiate ctxt (map (apfst getvar) values) thm
end

(*
 * Fetch all unique schematics in the given term.
 *)
fun get_vars t =
let
  val all_vars = fold_aterms (fn x => fn l =>
    (case x of Var _ => (x :: l) | _ => l)) t []
in
  sort_distinct Term_Ord.fast_term_ord all_vars
end

(*
 * Given a function "f" that returns either SOME cterm or NONE, instantiate
 * every schematic variable in the given function with the result of "f".
 *
 * If NONE is returned, the variable is left as-is.
 *)
fun instantiate_thm_vars ctxt f thm =
let
  (* Fetch all vars. *)
  val all_vars = get_vars (Thm.prop_of thm)

  (* Get instantiations. *)
  val insts = map_filter (fn Var var =>
    Option.map (fn x => (#1 var, x)) (f var)) all_vars
in
  infer_instantiate ctxt insts thm
end

(*
 * Given a list of name/cterm pairs, instantiate schematic variables in the
 * given "thm" with the given name with the cterm values.
 *)
fun instantiate_thm ctxt vars thm =
let
  val dict = Symtab.make vars
in
  instantiate_thm_vars ctxt (fn ((n, _), _) => Symtab.lookup dict n) thm
end

(* Apply a conversion to the n'th argument of a term. If n < 0, count from the end. *)
fun nth_arg_conv n conv c =
let
  val num_args = Drule.strip_comb c |> snd |> length;
  val num_strips = num_args - (if n < 0 then num_args + 1 + n else n);
  val new_conv = fold (fn _ => fn x => Conv.fun_conv x) (replicate num_strips ()) (Conv.arg_conv conv)
in
  new_conv c
end
handle Subscript => Conv.no_conv c

fun lhs_conv cv = Conv.combination_conv (Conv.arg_conv cv) Conv.all_conv;
fun rhs_conv cv = Conv.combination_conv Conv.all_conv cv

(*
 * Unsafe varify.
 *
 * Convert Var's to Free's, avoiding naming collisions.
 *
 * fixme : Uses of this function are all broken.
 *)
fun unsafe_unvarify term =
let
  fun used_names (Free (x, _)) = [x]
    | used_names (a $ b) = (used_names a) @ (used_names b)
    | used_names (Abs (_, _, x)) = used_names x
    | used_names _ = []
  val term_names = used_names term
in
  map_aterms
    (fn Var ((x, _), T) => Free (singleton (Name.variant_list term_names) x, T)
      | x => x) term
  |> map_types Logic.unvarifyT_global
end

(* Attempt to guess if the given theorem is a "cong" rule. *)
fun is_cong thm =
  case (Thm.concl_of thm) of
       (Const (@{const_name "HOL.Trueprop"}, _) $ (Const (@{const_name "HOL.eq"}, _) $ lhs $ rhs)) =>
         (Term.head_of lhs = Term.head_of rhs)
     | _ => false

(* Given two theorems, attempt to rename bound variables in theorem "new" to
 * use the names in theorem "old". *)
fun thm_restore_names ctxt old_thm new_thm =
let
  fun restore_names old new =
    case (old, new) of
        (Abs (old_name, _, old_body), Abs (_, new_T, new_body)) =>
          Abs (old_name, new_T, restore_names old_body new_body)
      | ((x1 $ y1), (x2 $ y2)) =>
          (restore_names x1 x2 $ restore_names y1 y2)
      | (_, other) => other
  val renamed_prop = restore_names (Thm.prop_of old_thm) (Thm.prop_of new_thm)
in
  Thm.cterm_of ctxt renamed_prop
  |> Goal.init
  |> resolve_tac ctxt [new_thm] 1
  |> Seq.hd
  |> Goal.finish ctxt
end

(*
 * Find the term "term" in the term "body", and pull it out into a lambda
 * function.
 *
 * For instance:
 *
 *   abs_over "x" @{term "cat"} @{term "cat + dog"}
 *
 * would result in the (SOME @{term "%x. x + dog"}).
 *)
fun abs_over varname term body =
  Term.lambda_name (varname, term) (incr_boundvars 1 body)

fun abs_over_apply varname term body =
  let 
    val Abs (s, T, bdy) = Term.lambda_name (varname, term) (incr_boundvars 1 body)
  in
    Abs (s, T, bdy $ Bound 0)
  end

(*
 * Abstract over a tuple of variables.
 *
 * For example, given the list ["a", "b"] of variables to abstract over, and
 * the term "a + b + c", we will produce "%(a, b). a + b + c" where "a" and "b"
 * have become bound.
 *
 * If the input is a single-element list, this function is equivalent to
 * "abs_over".
 *)
fun abs_over_tuple [] body =
      absdummy @{typ unit} body
  | abs_over_tuple [(var_name, abs_term)] body =
      abs_over var_name abs_term body
  | abs_over_tuple ((var_name, abs_term)::xs) body =
     HOLogic.mk_case_prod (abs_over var_name abs_term (abs_over_tuple xs body))

fun abs_over_list [] body =
      absdummy @{typ unit} body
  | abs_over_list [(var_name, abs_term)] body =
      abs_over var_name abs_term body
  | abs_over_list ((var_name, abs_term)::xs) body =
      (abs_over var_name abs_term (abs_over_list xs body))



fun infer_head ctxt (c as Const (cn, cT)) args =
  let
    (* avoid large term arguments for type-inference by introducing fixed variables *)
    val (arg_names, ctxt') = Variable.variant_fixes (map (fn i => "_" ^ string_of_int i) (1 upto (length args))) ctxt
    val arg_types = map Term.fastype_of args
    val t = infer_types_simple ctxt (betapplys (Term.map_types (fn _ => dummyT) c, args))
    val cT' = arg_types ---> fastype_of t
  in 
    betapplys (Const (cn, cT'), args)
  end
  handle ERROR str => raise TERM (str, c:: args)
  

(* Put commas between a list of strings. *)
fun commas l =
  map Pretty.str l
  |> Pretty.commas
  |> Pretty.enclose "" ""
  |> Pretty.unformatted_string_of

(* Make a list of conjunctions. *)
fun mk_conj_list [] = @{term "HOL.True"}
  | mk_conj_list [x] = x
  | mk_conj_list (x::xs) = HOLogic.mk_conj (x, (mk_conj_list xs))

(* Destruct a list of conjunctions. *)
fun dest_conj_list (Const (@{const_name "HOL.conj"}, _) $ l $ r)
        = l :: dest_conj_list r
  | dest_conj_list x = [x]

(*
 * Apply the given tactic to the given theorem, providing (brief) diagnostic
 * messages if something goes wrong.
 *)

fun gen_apply_tac print ctxt (step : string) thmfun (st : thm) =
  let
    val _ = if print then print_tac ctxt step st else Seq.empty
  in
   (thmfun st |> Seq.hd) handle Option =>
    raise TERM ("Failed to apply tactic during " ^ quote step, Thm.prems_of st)
  end

val apply_tac = gen_apply_tac false

fun PRIM ctxt (step: string) thmfun = PRIMITIVE (apply_tac ctxt step thmfun)

(*
 * A "the" operator that explains what is going wrong.
 *)
fun the' str x =
    (the x) handle Option => error str

(*
 * Map every item in a term from bottom to top. We differ from
 * "map_aterms" because we will visit compound terms, such as
 * "a $ b $ c".
 *)
fun term_map_bot f (Abs (a, t, b)) = f (Abs (a, t, term_map_bot f b))
  | term_map_bot f (a $ b) = f (term_map_bot f a $ term_map_bot f b)
  | term_map_bot f x = f x

(*
 * Map every item in a term from top to bottom. A second parameter is
 * returned by our mapping function "f" which is set to true if we
 * should halt recursion after a particular replacement.
 *)
fun term_map_top' f x =
  (case f x of
    (x, true) => x
  | (Abs (a, t, b), false) => Abs (a, t, term_map_top' f b)
  | ((a $ b), false) => term_map_top' f a $ term_map_top' f b
  | (x, false) => x)
fun term_map_top f x = term_map_top' (fn x => (f x, false)) x

(*
 * Map every item in a term from top to bottom, collecting items
 * in a list along the way.
 *)
fun term_fold_map_top' f x =
  (case f x of
    (l, x, true) => (l, x)
  | (l, Abs (a, t, b), false) =>
    let
      val (new_l, new_t) = term_fold_map_top' f b
    in
      (l @ new_l, Abs (a, t, new_t))
    end
  | (l, (a $ b), false) =>
    let
      val (list_a, new_a) = term_fold_map_top' f a
      val (list_b, new_b) = term_fold_map_top' f b
    in
      (l @ list_a @ list_b, new_a $ new_b)
    end
  | (l, x, false) => (l, x))
fun term_fold_map_top f x =
  term_fold_map_top' (fn x =>
    ((f x, false) |> (fn ((a, b), c) => (a, b, c)))) x

fun import_universal_prop t ctxt =
  case t of
    Const (@{const_name Pure.all}, _) $ (abs as Abs (x, xT, P)) => 
      let
        val ([v], ctxt') = fix_variant_frees [(x, xT)] ctxt
        val ((vs, t'), ctxt'') = import_universal_prop (betapply(abs, v)) ctxt' 
      in 
        ((v::vs, t'), ctxt'')
      end
  | _ => (([], t), ctxt)
  
(*
 * Map all levels of the simpset.
 *)
fun simp_map f =
  Context.map_proof (
    Local_Theory.declaration {syntax = false, pervasive = false, pos = \<^here>} (
      K (Simplifier.map_ss f)))
  |> Context.proof_map

(*
 * Add a thm to the simpset.
 *)
fun simp_add thms =
  simp_map (fn ctxt => ctxt addsimps thms)

(*
 * Delete a thm from a simpset.
 *)
fun simp_del thms =
  simp_map (fn ctxt => ctxt delsimps thms)

(* Abstract over the given term with a forall constant. *)
fun forall v t = HOLogic.all_const (fastype_of v) $ lambda v t

(* Convert Var's into foralls. *)
fun vars_to_forall term =
   fold (fn p => fn t => forall p t) (get_vars term) term

(* Convert Var's into meta-foralls. *)
fun vars_to_metaforall term =
   fold (fn p => fn t => Logic.all p t) (get_vars term) term

(* Emulate [abs_def] thm attribute. *)
fun abs_def ctxt =
   Local_Defs.meta_rewrite_rule ctxt #> Drule.abs_def

(*
 * Create a string from a template and a set of values.
 *
 * Template variables are of the form "%n" where "n" is a number between 0 and
 * 9, indicating the value to substitute in.
 *
 * For example, the template "moo %0 cow %1" with the values ["cat", "dog"]
 * would genereate "moo cat cow dog".
 *)
fun subs_template template vals =
let
  fun subs_template' vals (#"%"::v::xs) =
        (nth vals ((Char.ord v) - (Char.ord #"0"))) @ subs_template' vals xs
    | subs_template' vals (v::xs) = v :: (subs_template' vals xs)
    | subs_template' _ [] = []
in
  subs_template' (map String.explode vals) (String.explode template)
  |> String.implode
end

(* Prove a set of rules, giving them the given names. *)
fun prove_rules name lemmas tac lthy =
let
  val thms = map (fn txt =>
    Syntax.read_prop lthy txt
    |> Syntax.check_term lthy
    |> (fn x => Goal.prove lthy [] [] x (K tac))
    |> Thm.forall_intr_frees
    ) lemmas
in
  Local_Theory.note ((Binding.name name, []), thms) lthy |> snd
end

(* Prove a rule from the given string, giving it the given name. *)
fun prove_rule name lemma tac lthy =
  prove_rules name [lemma] tac lthy

fun auto_insert_tac ctxt rules =
 (Method.insert_tac ctxt rules) THEN' (K (auto_tac ctxt))


(*
 * Chain a series of state-predicates together.
 *
 * Each input has the form "%s. P s", where "s" is of type "stateT".
 *)
fun chain_preds stateT [] = Abs ("s", stateT, @{term "HOL.True"})
  | chain_preds     _ [x] = x
  | chain_preds stateT (x::xs) =
      Const (@{const_name "pred_conj"},
          (stateT --> @{typ bool}) --> (stateT --> @{typ bool}) --> (stateT --> @{typ bool}))
        $ x $ (chain_preds stateT xs)

(*
 * Given a term of the form "Abs (a, T, x)" and a function "f" that processes a
 * term into another, feed the term "x" to "f" such that bound variables are
 * replaced with free variables, and then abstracted out again once "f" is
 * complete.
 *
 * For example, if we are called with:
 *
 *   concrete_abs f (Abs ("x", @{typ nat}, Bound 0))
 *
 * then "f" will be given "Free ("x", @{typ nat})", and such instances of this
 * free variable will be abstracted out again once "f" is complete.
 *
 * The variant "concrete_abs'" does not perform the abstraction step, but
 * instead returns the Free variable used.
 *)
fun concrete_abs' ctxt t =
let
  fun get_lambda_name (Abs (n, _, _)) = n
    | get_lambda_name _ = "x"
  val first_argT = domain_type (fastype_of t)
  val [(n', _)] = Variable.variant_frees ctxt [t] [(get_lambda_name t, ())]
  val free = Free (n', first_argT)
in
  ((betapply (t, free)), free, n')
end
fun concrete_abs ctxt f t =
let
  val (term, free, name) = concrete_abs' ctxt t
in
  f term |>> abs_over name free
end

(*
 * Given a definition "thm" of the form:
 *
 *    x a b c == a + b + c
 *
 * return the "thm" with arguments instantiated.
 *)
fun inst_args ctxt vals thm =
let
  (* Fetch schematic variables on the LHS, stripping away locale assumptions
   * and locale fixed variables first. *)
  val vars = Thm.cprop_of thm
    |> Drule.strip_imp_concl
    |> Thm.term_of
    |> lhs_of_eq
    |> Term.strip_comb
    |> snd
    |> filter (is_Var)
    |> map (#1 o dest_Var)
in
  Drule.infer_instantiate ctxt ((take (length vals) vars) ~~ vals) thm
end

(*
 * A tactic like "rtac", but only performs first-order matching.
 *)
fun first_order_rule_tac thm n goal_thm =
let
  val thy = Thm.theory_of_thm goal_thm
  val ctxt = Proof_Context.init_global thy

  (* First-order match "thm" against the n'th premise of our goal. *)
  val thm_term = Thm.concl_of thm
  val goal_term = Logic.nth_prem (n, Thm.prop_of goal_thm)
  val tenv = Pattern.first_order_match thy (thm_term, goal_term)
      (Vartab.empty, Vartab.empty) |> snd

  (* Instantiate "thm" with the matched values. *)
  val inst = map (fn (var_name, (var_type, value)) =>
        (var_name, Thm.cterm_of ctxt value))
      (Vartab.dest tenv)
  val new_thm = infer_instantiate ctxt inst thm
in
  resolve_tac ctxt [new_thm] n goal_thm
end
handle Pattern.MATCH => Seq.empty

(*
 * Unfold all instances of the given theorem once, but don't
 * recursively unfold.
 *)
fun unfold_once_tac ctxt thm =
  CONVERSION (Conv.bottom_conv (K (Conv.try_conv (Conv.rewr_conv thm))) ctxt)

(* Set a simpset as being hidden, so warnings are not printed from it. *)
fun set_hidden_ctxt ctxt =
  Context_Position.set_visible false ctxt

(* Guess the name of a thm. *)
fun guess_thm_name ctxt thm =
  Find_Theorems.all_facts_of ctxt
  |> get_first (fn (a, thm') => if Thm.eq_thm (thm, thm') then SOME (Thm_Name.print a) else NONE);


(* Expand type abbreviations. *)
fun expand_type_abbrevs ctxt t = Thm.typ_of (Thm.ctyp_of ctxt t)

(*
 * Instantiate the schematics in a thm from the given environment.
 *)
fun instantiate_normalize_from_env ctxt env =
let
  fun prep_type (x, (S, ty)) =
    ((x,S), Thm.ctyp_of ctxt ty)
  fun prep_term (x, (T, t)) =
    ((x,T), Thm.cterm_of ctxt t)
  val term_vals = Vartab.dest (Envir.term_env env)
  val typ_vals = Vartab.dest (Envir.type_env env)
in
  (Drule.instantiate_normalize
      (TVars.make (map prep_type typ_vals), Vars.make (map prep_term term_vals)))
end

(*
 * A conversion with behaviour similar to "apply subst".
 *
 * In particular, it can apply a rewrite rule of the form:
 *
 *   ?A + ?A == f
 *
 * whereas "rewrite_conv" and friends will fail because of the reuse of
 * the schematic ?A on the left-hand-side.
 *)
fun subst_conv_raw ctxt thm ct =
let
  val thy = Proof_Context.theory_of ctxt
  val lhs = lhs_of (Thm.concl_of thm)

  (* Determine if the types match. *)
  val maybe_match =
    (Sign.typ_unify thy (fastype_of lhs, fastype_of (Thm.term_of ct)) (Vartab.empty, 0); true)
    handle Type.TUNIFY => false
  val maybe_match2 =
    (Type.raw_unify  (fastype_of lhs, fastype_of (Thm.term_of ct)) (Vartab.empty); true)
    handle Type.TUNIFY => false

  val _ = if maybe_match <> maybe_match2 then
       raise CTERM ("bub", [ct]) else ()

  (* If so, attempt to unify. *)
  val env =
    if maybe_match then
      Unify.matchers (Context.Proof ctxt) [(lhs, Thm.term_of ct)]
      handle ListPair.UnequalLengths => Seq.empty
           | Term.TERM _ => Seq.empty
    else
      Seq.empty
in
  case Seq.pull env of
    NONE =>
      Conv.no_conv ct
  | SOME (env, _) =>
      Conv.rewr_conv (instantiate_normalize_from_env ctxt env thm) ct
end
fun subst_conv ctxt thm =
  (Thm.eta_conversion
      then_conv subst_conv_raw ctxt (Drule.eta_contraction_rule thm))

fun eta_conv ctxt = Conv.bottom_conv (K (Thm.eta_conversion)) ctxt
fun eta_norm ctxt thm = Conv.fconv_rule (eta_conv ctxt) thm

(* A conversion to wade through any Isabelle/Pure or Isabelle/HOL
 * logical gunf. *)
fun remove_meta_conv conv ctxt ct =
  (case Thm.term_of ct of
    Const (@{const_name "Pure.all"}, _) $ Abs _ =>
      Conv.arg_conv (Conv.abs_conv (fn (_, ctxt) =>
          remove_meta_conv conv ctxt) ctxt) ct
  | Const (@{const_name "Trueprop"}, _) $ _ =>
      Conv.arg_conv (remove_meta_conv conv ctxt) ct
  | _ =>
     conv ctxt ct
  )

val beta_eta_normal_conv = Conv.bottom_conv (K Drule.beta_eta_conversion)
fun beta_eta_normal_rule ctxt  = Conv.fconv_rule (beta_eta_normal_conv ctxt)


(* Messages for non-critical errors. *)
val keep_going_instruction =
  "\nPlease notify the AutoCorres maintainers of this failure. " ^
  "In the meantime, use \"autocorres [keep_going]\" to ignore the failure."
val keep_going_info =
  "\nIgnoring this error because keep_going is enabled."

(* Raise exceptions unless keep_going is set. *)
fun TERM_non_critical keep_going msg term =
  if keep_going then warning (msg ^ keep_going_info)
  else raise TERM (msg ^ keep_going_instruction, term)

fun CTERM_non_critical keep_going msg ct =
  if keep_going then warning (msg ^ keep_going_info)
  else raise CTERM (msg ^ keep_going_instruction, ct)

fun THM_non_critical keep_going msg n thm =
  if keep_going then warning (msg ^ keep_going_info)
  else raise THM (msg ^ keep_going_instruction, n, thm)

(* Perform a "Method.trace" on the given list of thms if the given tactic
 * succeeds. *)
fun trace_rule ctxt goal rule =
  if Config.get ctxt Method.rule_trace then
  let
    val _ = Goal_Display.string_of_goal ctxt goal |> tracing
    val _ = (case guess_thm_name ctxt rule of
        SOME x => Pretty.str x
      | NONE => Thm.pretty_thm_item ctxt rule)
      |> Pretty.string_of |> tracing
  in
    ()
  end
  else ();

(* Apply the given tactic. If successful, trace the given "thm" and current
 * goal state. *)
fun trace_if_success ctxt thm tac goal =
  (tac THEN (fn y => (trace_rule ctxt goal thm; all_tac y))) goal

(* Get the type a pointer points to. *)
fun dest_ptrT T = dest_Type T |> snd |> hd
fun mk_ptrT T = Type (@{type_name "ptr"}, [T])

(* Get / dest an option type. *)
fun dest_optionT (Type ("Option.option", [x])) = x
fun mk_optionT T = Type (@{type_name "option"}, [T])

(* Construct other terms. *)
fun mk_the T t = Const (@{const_name "the"}, mk_optionT T --> T) $ t
fun mk_Some T t = Const (@{const_name "Some"}, T --> mk_optionT T) $ t
fun mk_fun_upd rangeT domT f src dest =
  Const (@{const_name "fun_upd"}, (rangeT --> domT) --> rangeT --> domT --> rangeT --> domT)
    $ f $ src $ dest
fun mk_bool true = @{term True}
  | mk_bool false = @{term False}

(* Succeed only if there are no subgoals. *)
fun solved_tac thm =
  if Thm.nprems_of thm = 0 then Seq.single thm else Seq.empty

(* Convenience function for making simprocs. *)
fun mk_simproc' ctxt (name : string, pats : string list, proc : Proof.context -> cterm -> thm option) = let
  in Simplifier.make_simproc ctxt {name = name, identifier = [],  
        lhss = map (Proof_Context.read_term_pattern ctxt) pats,
        proc = K proc} end

(* Get named_theorems in reverse order. We use this for translation rulesets
 * so that user-added rules can override the built-in ones. *)
fun get_rules ctxt = Named_Theorems.get ctxt #> rev

fun symmetric ctxt thm = fst (Thm.apply_attribute Calculation.symmetric thm (Context.Proof ctxt))

fun split_conj thm =
  (thm RS @{thm conjunct1}) :: split_conj (thm RS @{thm conjunct2})
  handle THM _ => [thm]

(* As Substring.position but searches from the end *)
fun positionr pat s = let
  val (s0, begin0, size0) = Substring.base s
  fun search i = if i < begin0 then
                   (s, Substring.substring (s0, begin0 + size0, 0)) (* not found *)
                 else if Substring.isPrefix pat (Substring.substring (s0, i, size0 - i)) then
                   (Substring.substring (s0, begin0, i), (* found *)
                    Substring.substring (s0, begin0 + i, size0 - i))
                 else search (i - 1)
  in search size0 end
val _ = assert (apply2 Substring.string (positionr "br" (Substring.full "abracadabra"))
                 = ("abracada", "bra")) ""
val _ = assert (apply2 Substring.string (positionr "xx" (Substring.full "abracadabra"))
                 = ("abracadabra", "")) ""

(* Merge a list of Symtabs. *)
fun symtab_merge allow_dups tabs =
      maps Symtab.dest tabs
      |> (if allow_dups then sort_distinct (fast_string_ord o apply2 fst) else I)
      |> Symtab.make;

(* Merge with custom merge operation. *)
fun symtab_merge_with merge (tab1, tab2) =
  sort_distinct fast_string_ord (Symtab.keys tab1 @ Symtab.keys tab2)
  |> map (fn k => (k, case (Symtab.lookup tab1 k, Symtab.lookup tab2 k) of
                          (SOME x1, SOME x2) => merge (x1, x2)
                        | (SOME x1, NONE) => x1
                        | (NONE, SOME x2) => x2
                        (* (NONE, NONE) impossible *)))
  |> Symtab.make

fun buckets eq xs =
  let
    fun bucks done [] = done
      | bucks done (x::xs) = 
         let 
           val (same, rest) = split_filter (fn y => eq (x, y)) (x::xs)
         in bucks (same::done) rest end
  in
   bucks [] xs
  end

fun app_snds f ps = 
  let 
    val (xs, ys) = split_list ps
  in xs ~~ f ys end


val add_timing : Timing.timing  -> Timing.timing -> Timing.timing = 
  (fn {elapsed = e1, cpu = c1, gc = g1} => fn {elapsed = e2, cpu = c2, gc = g2} => 
    {elapsed= e1 + e2, cpu = c1 + c2, gc = g1 + g2})

fun add_timings (j1, w1) (j2, w2) = (add_timing j1 j2, add_timing w1 w2)
val zero_timing : Timing.timing = {elapsed = Time.zeroTime, cpu =  Time.zeroTime, gc = Time.zeroTime}
type map_reduce_timing = {join: Timing.timing, workload: Timing.timing}
fun mk_timing (join, workload) = {join=join, workload=workload}

(* map_reduce: kind of fold with parallel execution:
 * - trace: trace function to output message
 * - string_of: convert a task-id to a string
 * - id: id for the task
 * - depends: indicates dependencies between tasks with respect to the accumulator. Before a task
 *          is evaluated all dependencies are first evaluated and the results are joined. 
 * - f: the function to apply to each tasks, gets the task and the accumulator
 * - join: join the outcomes (accumulators) of different tasks, the exact order of the
 *         join must not matter as long as the dependencies are respected. Also note that a join
 *         might be applied multiple times to an accumlator. E.g.
 *         - depends t3 = [t1, t2] : acc3 = f t3 (join (f t1 acc) (f t2 acc)) 
 *         - depends t4 = [t1, t3] : acc4 = f t4 (join (f t1 acc) (f t3 acc))
 *         - depends t6 = [t4, t5] : acc6 = f t6 (join acc4 (f t5 acc)) 
 * - task: list of tasks
 * - acc: the accumulator
 * - returns the list of task-ids paired with the respective outcome.
 *)

fun map_reduce
     (trace: (unit -> string) -> unit)
     (string_of: ''c -> string) 
     (id:'b -> ''c)
     (depends: ''c -> ''c list)
     (f:'b -> 'a -> 'a) 
     (join: 'a list -> 'a) 
     (tasks: 'b list) 
     (acc: 'a) : (''c * 'a) list =
  let
    val group = Future.new_group NONE;
    fun params deps = {name = "map_reduce", group = SOME group, deps = deps, pri = 0, interrupts = true};
    fun fork deps f = (singleton o Future.forks) (params deps) f
    fun string_of_tasks ts = ts |> map (string_of o id) |> Pretty.str_list "[" "]" |> Pretty.string_of
  
    fun work imports t () = 
      let 
        val acc = if null imports then acc else 
          let
            val results = Future.joins (map snd imports)
            val res = join results
          in
            res
          end 
        val acc' = f t acc
      in acc' end
  
    fun ready scheduled task = subset (op =) (depends (id task), map id scheduled)
  
    fun group_tasks scheduled [] = scheduled
      | group_tasks scheduled tasks =
         let
           val (next, waiting) = split_filter (ready (flat scheduled)) tasks
           val _ = if null next then error ("tasks cannot be scheduled according to dependencies. Stuck with:\n " ^ string_of_tasks tasks) else ()
         in group_tasks (scheduled @ [next]) waiting end
  
    fun task_imports forked task =
     let
        val imports = fold (fn t => fn xs => 
           ((t, the (AList.lookup (op =) forked t)))::xs) (depends (id task)) []
     in imports end
  
    fun fork_group tasks forked = 
      let         
        fun fork_work task =
          let 
            val imports = task_imports forked task
            val deps = map (Future.task_of o snd) imports
          in (id task, fork deps (work imports task)) end
      in forked @ map fork_work tasks end
  
    val grouped = group_tasks [[]] tasks
    val _ = trace (fn () => "grouped tasks: " ^ @{make_string} (map (map (string_of o id)) grouped))
  
    val fork_all = 
      let
        val running = fold fork_group grouped []
      in running end
  
    val _ = trace (fn () => "forked " ^ @{make_string} (length fork_all) ^ " tasks") 

    val results =  app_snds Future.joins fork_all   
  in                                                   
    rev results
  end



(* Some Conversions and Tactics *)

fun beta (t1 $ t2) = (betapply (beta t1, t2))
  | beta t = t 

fun open_beta (t as (t1 $ _)) = (case open_beta t1 of Abs (_, _, b) => open_beta b | _ => t)
  | open_beta t = t

val open_beta_eta = open_beta o snd o eta_redex
val open_beta_norm_eta = open_beta o snd o norm_eta

val placeholder = @{pattern "?X"} |> (fn Var ((x, i), T) => Var (("_", i), T));

fun mk_pattern @{term_pat "?a $ ?b"} = (true, snd (mk_pattern a) $ snd (mk_pattern b))
  | mk_pattern (Abs (x,T,b)) = let val (is_pattern, bdy) = mk_pattern b in (is_pattern, Abs ("_",T,bdy)) end 
  | mk_pattern _ = (false, placeholder)


fun reify_comb eq1 eq2 =
  let
    val rule = @{lemma "a \<equiv> a' \<Longrightarrow> b \<equiv> b' \<Longrightarrow> a b \<equiv> (a' $ b')" by simp} 
  in rule OF [eq1, eq2] end

fun gen_combination_conv dest comb cv1 cv2 ct =
  let val (ct1, ct2) = dest ct
  in comb (cv1 ct1) (cv2 ct2) end;

fun gen_reify_comb_conv prep ctxt pat = 
  let 
    val pattern = prep pat
    fun conv (Var x) = Conv.all_conv
      | conv (t1 $ t2) = gen_combination_conv Thm.dest_comb reify_comb (conv t1) (conv t2)
      | conv (Abs (x, _, t)) = Conv.abs_conv (K (conv t)) ctxt 
      | conv _ = Conv.no_conv
  in conv pattern end

val reify_comb_conv = gen_reify_comb_conv (snd o mk_pattern)

fun dest_reified_comb ct = 
  case Thm.term_of ct of
    @{term_pat "?a $ ?b"} => Thm.dest_comb ct |>> Thm.dest_arg 
   | _ => raise CTERM ("no reified combination", [ct])

fun unreify_comb_conv ctxt pat =
  let 
    val pattern = snd (mk_pattern pat)
    fun conv (Var x) = Conv.all_conv
      | conv (t1 $ t2) = gen_combination_conv dest_reified_comb Thm.combination (conv t1) (conv t2)
      | conv (Abs (x, _, t)) = Conv.abs_conv (K (conv t)) ctxt 
      | conv _ = Conv.no_conv
  in conv pattern end




fun trace_conv msg ct =
  let
    val _ = tracing (msg  ^ @{make_string} ct)
  in Conv.all_conv ct end

fun trace_simps msg P ctxt =
 let
   val simps = simpset_of ctxt |> dest_ss |> #simps |> filter P |> map snd
   val _ = tracing (Pretty.string_of (Pretty.big_list msg (map (Thm.pretty_thm ctxt) simps)))
 in
   ()
 end

fun mk_match_insts ctxt (ty_env, trm_env) =  
  (ty_env |> Vartab.dest |> map (fn (x, (sorts, T)) => ((x, sorts), (Thm.ctyp_of ctxt T))),
  trm_env |> Vartab.dest |> map (fn (x, (T, t)) => ((x, Envir.subst_type ty_env T), Thm.cterm_of ctxt t)))

fun match_insts ctxt pat obj =
   Pattern.match (Proof_Context.theory_of ctxt) (pat, obj) (Vartab.empty, Vartab.empty) 
   |> mk_match_insts ctxt
  
fun mk_unify_insts ctxt env =  
  (Envir.type_env env |> Vartab.dest |> map (fn (x, (sorts, T)) => ((x, sorts), (Thm.ctyp_of ctxt T))),
   Envir.term_env env |> Vartab.dest |> map (fn (x, (T, t)) => ((x, Envir.norm_type (Envir.type_env env) T), Thm.cterm_of ctxt t)))

fun unify_env ctxt env pat obj =
  case Unify.unifiers (Context.Proof ctxt, env, [(pat, obj)]) |> Seq.pull of
     SOME ((env,_), _) => env
   | NONE => error ("unify_env failed; pat: " ^ Syntax.string_of_term ctxt pat ^ "\nobj: " ^ Syntax.string_of_term ctxt obj);

fun unify_insts ctxt env pat obj =
  case Unify.unifiers (Context.Proof ctxt, env, [(pat, obj)]) |> Seq.pull of
     SOME ((env,_), _) => mk_unify_insts ctxt env
   | NONE => error ("unify_insts failed; pat: " ^ Syntax.string_of_term ctxt pat ^ "\nobj: " ^ Syntax.string_of_term ctxt obj);
  

fun match_or_unify ctxt pat obj =
  match_insts ctxt pat obj 
  handle Pattern.MATCH => unify_insts ctxt (Envir.init) pat obj


fun get_index' P = get_index (fn x => if P x then SOME x else NONE)

fun get_last_index f =
  let
    fun get_aux (_: int) [] = NONE
      | get_aux i (x :: xs) =
          (case get_aux (i + 1) xs of
            NONE => (case f x of NONE => NONE | SOME y => SOME (i, y))
          | SOME y => SOME y)
  in get_aux 0 end;

fun get_last_index' P = get_last_index (fn x => if P x then SOME x else NONE)

fun get_indexes f =
  let
    fun get_aux (_: int) [] = []
      | get_aux i (x :: xs) =
          let
            val rest = get_aux (i + 1) xs
          in  
            case f x of
              NONE => rest
            | SOME y => (i, y) :: rest
          end
  in get_aux 0 end;

fun get_indexes' P = get_indexes (fn x => if P x then SOME x else NONE)

fun indexes [] xs = []
  | indexes (i::is) xs = nth xs i :: indexes is xs

\<comment>\<open>
\<open>fo_arg_resolve_tac rule\<close> does some custom first order matching for a rule containing
the HOL-reified function application @{term "($)"}. Arguments containing @{term "($)"} are treated 
differently according to their position:
* The last argument is considered to be *matched* against a *concrete term* in the goal
* Optional arguments before are not preprocessed so they are treated by ordinary rule composition.

Here is a typical example:
\<open>abstract_val ?Q ?x id ?x' \<Longrightarrow>
abstract_val ?P ?f id ?f' \<Longrightarrow>
abstract_val (?P \<and> ?Q) (?g $ ?f $ ?x) ?g (?f' $ ?x')\<close>


Argument \<open>(?f' $ ?x')\<close> is matched against a concrete term in the goal. This avoids higher-order
unification issues. Before resolving with the goal the auxiliary @{term "($)"} in this argument are 
removed and replaced by the calculated instantiations for the schematic variables in the rule.

Argument \<open>(?g $ ?f $ ?x)\<close> is unified with a schematic variable in a goal and hence three distinct
schematic variables replacing g, a, b are introduced. 
Note that this is a mere effect of ordinary rule composition. Hence, the auxiliary @{term "($)"} in
these arguments remain in the result.
.

\<close>
local

fun check_pattern rule arg = 
  let
    val all_vars = [] |> fold_aterms (fn Var v => cons v | _ => I) arg
    val dups = duplicates (op =) all_vars
  
  in
    if not (null dups) 
    then error ("fo_arg_resolve_tac: schematic variables in first-order-patterns have to be unique:\n" ^ 
                @{make_string} rule ^ "\n duplicates: " ^ @{make_string} (map (Term.string_of_vname o fst) dups))
    else ()

  end


in 
fun fo_arg_resolve_tac ctxt rule =
  let

    val (head, args) = Thm.concl_of rule |> HOLogic.dest_Trueprop |> Term.strip_comb 
    val exists_fun_app = exists_Const (fn (n, _) => (n = @{const_name "fun_app"}));
    val (n, arg_pat) = case get_last_index' exists_fun_app args of
                         NONE => error ("fo_arg_resolve_tac: expecting one argument with pattern containing '$'")
                       | SOME x => x; 
    val _ = check_pattern rule arg_pat
    val nprems = Thm.nprems_of rule;   
    fun unfold_fun_app ctxt = Conv.fconv_rule 
          (Conv.concl_conv (~1) 
            (Conv.arg_conv (* Trueprop *)
              (nth_arg_conv (n + 1) 
                (Conv.bottom_conv (K (Conv.try_conv (Conv.rewr_conv @{thm "fun_app_def"}))) ctxt))))                 
    val rule' = unfold_fun_app ctxt rule
  in
    fn ctxt => CSUBGOAL (fn (ct, i) => fn st =>
      let
        val t = Thm.term_of ct

        fun match_arg t = t |> concl_of_subgoal_open |> concl_of_subgoal_open 
          |> HOLogic.dest_Trueprop |> Term.strip_comb |> snd |> (fn ts => nth ts n)

        fun abs [] t = t
          | abs ((x,T)::bs) t = abs bs (Abs (x, T, t))

        fun mk_match_pairs (bounds as (pat_bounds, trm_bounds)) (pat, trm) = 
          case (pat, trm) of
            (@{term_pat "?a $ ?b"}, t1 $ t2) => mk_match_pairs bounds (a, t1) @ mk_match_pairs bounds (b, t2)
          | (Abs (x, xT, p), Abs (y, yT, t)) => mk_match_pairs ((x, xT)::pat_bounds, (y, yT)::trm_bounds) (p, t)
          | (p, t) => [(abs pat_bounds p, abs trm_bounds t)]


        val (goal_head, args) = concl_of_subgoal_open t |> HOLogic.dest_Trueprop |> Term.strip_comb
        fun head_matches (Const (x, _)) (Const (y, _)) = (x = y)
          | head_matches _ _ = false
      in
        if head_matches goal_head head andalso n < length args
        then
          if exists_fun_app (nth args n) then resolve_tac ctxt [rule] i st 
          else 
            let         
              val rule = timeit_msg 2 ctxt (fn _ => "fo_arg_resolve_tac lift_rule: ") (fn _ => Thm.lift_rule ct rule)
              val (all_bounds, _) = strip_all_open [] (Thm.term_of ct)
              val pat_arg = match_arg (Thm.prop_of rule)
              val goal_arg = nth args n
              val match_trms = mk_match_pairs (all_bounds, all_bounds) (pat_arg, Envir.beta_eta_contract goal_arg)
              val _ = @{assert} (not (null match_trms))
              val insts = timeit_msg 2 ctxt (fn _ => "fo_arg_resolve_tac match: ") (fn _ => (Vartab.empty, Vartab.empty) 
                |> fold (Pattern.match (Proof_Context.theory_of ctxt)) match_trms
                |> mk_match_insts ctxt
                |> (fn (Ts, Vs) => (TVars.make Ts, Vars.make Vs)))
             
              val rule' =  timeit_msg 2 ctxt (fn _ => "fo_arg_resolve_tac lift rule': ") (fn _ => Thm.lift_rule ct rule')
              (* We deliberately do unfold_fun_app on the unlifted rule for performance reasons. Unfolding
               * the definition under a lot of bound variables can become expensive. The
               * assertion ensures that names of matched variables are preserved for rule vs. rule'. 
               *)
              val _ = @{assert} (Term.add_vars pat_arg [] = Term.add_vars (match_arg (Thm.prop_of rule')) [])
              val rule' = timeit_msg 2 ctxt (fn _ => "fo_arg_resolve_tac instantiate: ") (fn _ => Thm.instantiate insts rule')
              fun info _ = ("fo_arg_resolve_tac:\n " ^ "subgoal: " ^ string_of_int i ^ ": " ^ @{make_string} ct ^ "\n " ^
                   "rule: "  ^ Thm.string_of_thm ctxt rule' ^ "\n " ^
                   "insts: " ^ @{make_string} insts
                 ) 
            in    
              EVERY 
                 [timeap_msg_tac 2 ctxt info (Thm.bicompose (SOME ctxt) {flatten = true, match = false, incremented = true}
                    (false, rule', nprems) i)
                 ] st 
            end handle Pattern.MATCH => (verbose_msg 3 ctxt (fn _ => "fo_arg_resolve_tac: no match"); no_tac st) 
        else no_tac st
      end handle TERM _ => (verbose_msg 3 ctxt (fn _ => "fo_arg_resolve_tac: unexpected term"); no_tac st))
    end 
  end 


fun app2 (x1s, y1s) (x2s, y2s) = (x1s @ x2s, y1s @ y2s)
fun flat2 pss = ([], []) |> fold_rev app2 pss 

fun fo_refl_tac ctxt i st = SUBGOAL (fn (t, i) =>
  let
    val concl = concl_of_subgoal_open t
    val @{term_pat "Trueprop (?lhs = ?rhs)"} = concl
    val (has_comb, pat) = mk_pattern rhs
    val _ = if not has_comb then raise Bind else ()
    fun reify ctxt = Conv.every_conv [Drule.beta_eta_conversion, gen_reify_comb_conv I ctxt pat]
    fun gconv_reify i st =
      PRIMITIVE (Conv.gconv_rule 
       (Conv.params_conv (~1) 
         (K (Conv.concl_conv (~1) (Conv.arg_conv (Conv.arg1_conv (reify ctxt))))) ctxt) i) st handle CTERM _ => no_tac st
  in
    EVERY [
      gconv_reify i, print_subgoal_tac "reify" ctxt i,
      resolve_tac ctxt [refl] i
    ] 
  end) i st 
  handle Bind => no_tac st 

fun fo_resolve_tac ctxt rules = 
  let
    fun check rule = 
      let
        val (prem::_) = Thm.prems_of rule
        val @{term_pat "Trueprop (?lhs = ?rhs)"} = prem
        val (Var _) = lhs
        val has_comb = fst (mk_pattern rhs)
      in if not has_comb then raise Bind else () end
      handle Bind => raise TERM ("fo_resolve_tac: major premise of rule has to have format '?x = (... $ ...)'", [Thm.prop_of rule])
    val _ = map check rules
  in
    EVERY' [resolve_tac ctxt rules, fo_refl_tac ctxt ORELSE' (print_subgoal_tac "fo_refl_tac failed: " ctxt THEN' (K no_tac))]
  end

fun prune_unused_bounds_tac ctxt maxidx all_bounds used_bounds t i =
  let
    fun add_var_app bounds t vars =
      case t of 
        (_ $ _) => 
          (case strip_comb t of 
            (Var v, ts) =>  ((v, ts, bounds)::vars) |> fold (add_var_app bounds) ts
          | (t, ts) => vars |> fold (add_var_app bounds) (t::ts))
       | Abs (x,T, bdy) => add_var_app ((x,T)::bounds) bdy vars 
       | Var v => (v, [], bounds)::vars
       | _ => vars
        
    val vars = add_var_app [] t []
  in                                        
    case duplicates (op =) ((map (#1 o #1)) vars) of 
      (dups as (_::_)) => 
        (warning ("prune_unused_bounds_tac: schematic variables not distinct, pruning skipped: " ^ 
         @{make_string} dups); all_tac)
    | [] =>
      let
        fun make_inst (((v, i), T), args, bounds) =
          let
            val (argTs, rangeT) = strip_type T
            val nbounds = length bounds
            val used_bounds = map (fn i => i + nbounds) used_bounds
            val all_bounds = map (fn i => i + nbounds) all_bounds
            fun strip_args _ [] [] = ([], [])
              | strip_args pos (aT::argTs) [] = 
                  let val (argTs', args') = strip_args (pos - 1) argTs [] 
                  in (aT::argTs', Bound pos::args') end
              | strip_args pos (aT::argTs) (arg::args) =
                  let 
                    val res' as (argTs', args') = strip_args (pos - 1) argTs args
                  in
                    case arg of 
                      Bound n => if member (op =) used_bounds n orelse not (member (op =) all_bounds n)
                                 then (aT::argTs', Bound pos::args') 
                                 else res'
                     | _ => (aT::argTs', Bound pos:: args')
                  end
            val (argTs', args') = strip_args (length argTs - 1) argTs args
            val T' = argTs' ---> rangeT
            val bdy = list_comb (Var ((v, maxidx + 1), T'), args')
            fun abs [] t = t
              | abs (aT::aTs) t = Abs ("_", aT, abs aTs t)
            val abs_bdy = Thm.cterm_of ctxt (abs argTs bdy)
          in
             if length argTs' < length argTs 
             then [(((v,i), T), abs_bdy)]
             else []
          end  
        val insts = map make_inst vars |> flat
        val _ = verbose_msg 2 ctxt (fn _ => "prune_unused_var_tac: pruning schematic variables: " ^ 
           @{make_string} (map (apfst (Thm.cterm_of ctxt o Var)) insts))  

      in
        if null insts then all_tac
        else
          EVERY [  
            PRIMITIVE (Thm.instantiate (TVars.empty, Vars.make insts)), 
            Simplifier.simp_tac (put_simpset HOL_basic_ss ctxt addsimps @{thms triv_forall_equality}) i] 
      end 
  end


fun prune_unused_bounds_from_concr_tac get_concr ctxt st i = CSUBGOAL (fn (cgoal, i) => 
  let
    val t = Thm.term_of cgoal
    val (bounds, concl) = Utils.strip_concl_of_subgoal_open t 
  
    val concr = get_concr (HOLogic.dest_Trueprop concl)

    val nbounds = length bounds
    val used_bounds = Term.loose_bnos concr
    val all_bounds = 0 upto (nbounds - 1)
    val _ = if length used_bounds = nbounds
            then (verbose_msg 2 ctxt (fn _ => "prune_unused_bounds_from_concr_tac: nothing to be done"); 
                 raise THM ("nothing to be done", i, [])) 
            else ()
    val maxidx = Thm.maxidx_of_cterm cgoal
  in                                                 
    EVERY                    
      [prune_unused_bounds_tac ctxt maxidx all_bounds used_bounds concl i, 
       Utils.verbose_print_subgoal_tac 4 "after prune_unused_bounds_tac" ctxt i]
  end) st i
  handle THM ("nothing to be done", _, _) => K all_tac st i

fun THIN_tac prune_tac ctxt = CSUBGOAL (fn (ct, i) =>
      case Utils.concl_of_subgoal_open (Thm.term_of ct) of 
        @{term_pat "(THIN ?P)"} => 
           EVERY' [ 
             resolve_tac ctxt @{thms THIN_I}, 
             Goal.norm_hhf_tac ctxt,
             prune_tac ctxt] i
       | _ => no_tac
     )


end (* structure Utils *)

(* Memoization using a serialized cache. *)
signature Memo = sig
  type arg;
  val memo: (arg -> 'a) -> (arg -> 'a);
end;

functor Memo(Table: TABLE) = struct
  type arg = Table.key;
  fun memo f = let
    val table = Synchronized.var "" Table.empty;
    in fn a =>
         Synchronized.change_result table (fn tab =>
             case Table.lookup tab a of
                 SOME r => (r, tab)
               | NONE => let
                   val r = f a;
                   in (r, Table.update (a, r) tab) end)
    end;
end;
structure String_Memo = Memo(Symtab);

(* Insist the the given tactic solves a subgoal. *)
fun SOLVES tac = SOLVED' (K tac) 1
fun SOLVES_debug ctxt msg tac = 
  SOLVES tac ORELSE (print_tac ctxt msg THEN no_tac)

fun SOLVED'_debug_verbose level ctxt msg tac = 
  SOLVED' tac ORELSE' (Utils.verbose_print_subgoal_tac level msg ctxt THEN' (K no_tac))

(* Given a list of tactics, try them all, backtracking when necessary. *)
fun APPEND_LIST tacs = fold_rev (curry op APPEND) tacs no_tac;



(* Profiling *)

signature Profile_Args =
sig
  structure Key:KEY
  type from (* input of function *)
  type to   (* output of function *)     
  val  make_string_from: int -> from -> string (* for tracing with verbosity level *)
  val  make_string_to: int -> to -> string (* for tracing with verbosity level *)
  val  make_string_key: int -> Key.key -> string (* for tracing with verbosity level *)
  val  name:string (* name for profiling category, derived names for enabled / verbosity*)
end

functor Profile(Args: Profile_Args) = 
struct
  structure Table = Table(Args.Key)
  structure Thy_Data = Theory_Data(
    type T = (Timing.timing * (Args.from * Args.to)) Table.table;
    val empty = Table.empty;
    val merge = Table.merge (K true); 
  )
  structure Prf_Data = Proof_Data(
    type T = (Timing.timing * (Args.from * Args.to)) Table.table Synchronized.var;
    fun init thy = Synchronized.var Args.name (Thy_Data.get thy);
  )
  val enabled = Attrib.setup_config_bool 
    (Binding.make (Args.name ^ "_enabled", Binding.pos_of @{binding here})) (K false);
  val verbosity = Attrib.setup_config_int 
    (Binding.make (Args.name ^ "_verbosity", Binding.pos_of @{binding here})) (K 0);
  fun get ctxt = Synchronized.value (Prf_Data.get ctxt);
  fun transfer ctxt thy = Thy_Data.put (Synchronized.value (Prf_Data.get ctxt)) thy;
  fun lookup ctxt key = Table.lookup (Synchronized.value (Prf_Data.get ctxt)) key;
  fun tracing_msg ctxt maybe_key t x r =
    let 
      val verb = Config.get ctxt verbosity
      fun nl pref msg = if msg = "" then "" else pref ^ msg ^ "\n";
      val key_msg = case maybe_key of SOME key => Args.make_string_key verb key | NONE => ""
    in 
      if verb > 0 then
        tracing (Args.name ^ ": " ^ key_msg ^ "\n" ^ 
          nl "input: " (Args.make_string_from verb x) ^ 
          nl "result: " (Args.make_string_to verb r) ^
          Timing.message t)  
      else ()
        
    end
  fun timeit ctxt maybe_key f x =  
    if Config.get ctxt enabled 
    then
      let 
        val (t, result) = Timing.timing (Exn.result f) x;
      in
        case result of
          Exn.Res r => 
            let 
              val _ = maybe_key |> Option.app (fn key => 
                Synchronized.change (Prf_Data.get ctxt) (Table.update (key, (t, (x, r)))))
              val _ = tracing_msg ctxt maybe_key t x r
            in r end
        | _ =>  Exn.release result
      end
    else f x;
end

(*lexicographic product*)
fun triple_ord a_ord b_ord c_ord ((x, y, z), (x', y', z')) =
  (case a_ord (x, x') of EQUAL => prod_ord b_ord c_ord ((y, z), (y', z')) | ord => ord);

