(*
 * Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
 * Copyright (c) 2022 Apple Inc. All rights reserved.
 *
 * SPDX-License-Identifier: BSD-2-Clause
 *)

(* this is an -*- sml -*- file *)

signature RECURSIVE_RECORD_PACKAGE =
sig

  (* no type variables allowed! *)
  val define_record_type :
       {record_name : string,
        fields : {fldname : string, fldty : typ} list} list ->
      theory -> theory

  type info = {constructor: (string * typ), fields: (string * typ) list, updates: (string * typ) list};
  val get_simpset : theory -> simpset;
  val get_info : theory -> info Symtab.table;
  val is_record : theory -> string -> bool;
  val is_constructor : theory -> string (* type *) -> string (* const *) -> bool;
  val is_update : theory -> string (* type *) -> string (* const *) -> string option (* field-name *);
  val is_field : theory -> string -> string -> bool;

end;

structure RecursiveRecordPackage : RECURSIVE_RECORD_PACKAGE =
struct

type info = {constructor: (string * typ), fields: (string * typ) list, updates: (string * typ) list};
type data = {simpset: simpset, info: info Symtab.table};

fun make_data simpset info = {simpset=simpset, info=info};

structure RecursiveRecordData = Theory_Data
(
  type T = data;
  val empty = make_data HOL_basic_ss Symtab.empty;
  val merge = Utils.fast_merge (fn ({simpset=ss1, info=info1}, {simpset=ss2, info=info2}) =>
    make_data (merge_ss (ss1, ss2)) (Symtab.merge (K true) (info1, info2)));
);

val updateN = Record.updateN

val get_simpset = #simpset o RecursiveRecordData.get;
val get_info = #info o RecursiveRecordData.get

fun is_record thy name = Symtab.defined (get_info thy) name;

fun is_constructor thy type_name const_name =
  case Symtab.lookup (get_info thy) type_name of
    NONE => false
  | SOME info =>  fst (#constructor info) = const_name;

fun is_update thy type_name const_name =
  case Symtab.lookup (get_info thy) type_name of
    NONE => NONE
  | SOME {updates,...} =>
      if AList.defined (op =) updates const_name
      then SOME (unsuffix updateN const_name)
      else NONE;

fun is_field thy name fld =
   case Symtab.lookup (get_info thy) name of
     NONE => false
   | SOME {fields,...} => AList.defined (op =) fields fld;

fun map_simpset f = RecursiveRecordData.map (fn data => make_data (f (#simpset data)) (#info data))
fun map_info f = RecursiveRecordData.map (fn data => make_data (#simpset data) (f (#info data)))

fun add_recursive_record_thms simps congs thy =
  thy
  |> map_simpset (fn ss =>
       Proof_Context.init_global thy
       |> put_simpset ss
       |> (fn ctxt => ctxt addsimps simps)
       |> fold Raw_Simplifier.add_cong congs
       |> simpset_of);

fun add_info (name, info) thy =
  thy |> map_info (Symtab.update_new (name, info));



fun gen_vars tys = List.tabulate(length tys,
                                 (fn n => Free("x" ^ Int.toString n,
                                               List.nth(tys, n))))

(* BNF_LFP_Compat.primrec_global gives back the theorems still within the local context:
 *  Free(foo, _) = Const(foo,...) |- ...
 *  So we export it manually. Alternatively we could lookup the named rule in the updated theory.
 *)
fun export_thm thm =
  Drule.export_without_context thm OF @{thms reflexive}

fun define_accessor arg ({fldname, fldty}, result) thy = let
  val acc_ty = type_of arg --> fldty
  val acc_t = Free(fldname, acc_ty)
  val defn = TermsTypes.mk_prop (TermsTypes.mk_eqt(acc_t $ arg, result))

in
  thy
  |> BNF_LFP_Compat.primrec_global
       [(Binding.name fldname, NONE, NoSyn)]
       [(((Binding.name (fldname ^ "_def"), []), defn), [], [])] 
  |-> (fn (_, [_, simp]) => add_recursive_record_thms [export_thm simp] []) 
end



fun define_updator arg (i, {fldname, fldty}) thy = let
  val arg_ty = type_of arg
  val (con, args) = strip_comb arg
  val upd_ty = (fldty --> fldty) --> (arg_ty --> arg_ty)
  val upd_name = suffix updateN fldname
  val upd_t = Free(upd_name, upd_ty)
  val f = Free("f", fldty --> fldty)
  val lhs_t = upd_t $ f $ arg
  val modified_args = Library.nth_map i (fn t => f $ t) args
  val rhs_t = con |> fold (fn a => fn t => t $ a) modified_args
  val defn = TermsTypes.mk_prop(TermsTypes.mk_eqt(lhs_t, rhs_t))
in
  ((upd_name, upd_ty),
   thy
   |> BNF_LFP_Compat.primrec_global
        [(Binding.name upd_name, NONE, NoSyn)]
        [(((Binding.name (upd_name ^ "_def"), []), defn), [], [])] 
   |-> (fn (_, [_, simp]) => add_recursive_record_thms [export_thm simp] []))
end

fun fold_map_index f =
  let
    fun fold_aux (_: int) [] y = ([], y)
      | fold_aux i (x :: xs) y =
          let
            val (x', y') = f (i, x) y;
            val (xs', y'') = fold_aux (i + 1) xs y'
          in (x' :: xs', y'') end
  in fold_aux 0 end;

fun define_functions (r as {record_name, fields}) thy = let
  val recordnameb = Binding.name record_name
  val constructor_t =
      Const (hd (the (BNF_LFP_Compat.get_constrs thy (Sign.full_name thy recordnameb))))
  val args = gen_vars (map #fldty fields)
  val record_value_t = constructor_t |> fold (fn a => fn t => t $ a) args
  val field_args = ListPair.zip(fields, args)
  fun define_accessors thy =
      thy |> fold (define_accessor record_value_t) field_args
in
  (thy |> Sign.add_path record_name
       |> define_accessors
       |> fold_map_index (define_updator record_value_t) fields
       ||> RecursiveRecordPP.install_translations r
       ||> Sign.parent_path)
  before
  Feedback.informStr (Proof_Context.init_global thy) (1,
    "Defined accessor and update functions for record "^record_name)
end

fun cprod_less_diag list = let
  fun recurse acc l =
      case l of
        [] => acc
      | h::t => let
          val acc' = acc |> fold (fn e => fn acc => (h,e) :: (e,h) :: acc) t
        in
          recurse acc' t
        end
in
  recurse [] list
end

fun lower_triangle list = let
  fun recurse acc l =
      case l of
        [] => acc
      | h :: t => let
          val acc' = acc |> fold (fn e => fn acc => (e,h) :: acc)  t
        in
          recurse acc' t
        end
in
  recurse [] list
end

val updcong_foldE = @{thm "idupdate_compupdate_fold_congE"};

(* copied from src/Pure/old_term.ML -r 6a973bd43949 and then
   s/OrdList/Ord_List/
   s/TermOrd/Term_Ord/
*)
local
(*Accumulates the Vars in the term, suppressing duplicates.*)
fun add_term_vars (t, vars: term list) = case t of
    Var   _ => Ord_List.insert Term_Ord.term_ord t vars
  | Abs (_,_,body) => add_term_vars(body,vars)
  | f$t =>  add_term_vars (f, add_term_vars(t, vars))
  | _ => vars;

fun term_vars t = add_term_vars(t,[]);
in
val [updvar] = term_vars (nth (Thm.prems_of updcong_foldE) 1)
end

fun prove_record_rewrites {record_name, fields} thy = let
  val _ = Feedback.informStr (Proof_Context.init_global thy) (1,
    "Proving rewrites for struct "^record_name)
  val rty = Type(Sign.intern_type thy record_name, [])
  val r_var = Free("r", rty)
  val r_var' = Free("r'", rty)
  val recordnameb = Binding.name record_name
  val constructor = hd (the (BNF_LFP_Compat.get_constrs thy (Sign.full_name thy recordnameb)))
  val constructor_t = Const(constructor)
  open TermsTypes
  val case_tac = Induct_Tacs.case_tac
  fun prove g =
      Goal.prove_global_future thy [] [] (mk_prop g)
                        (fn {prems=_,context} =>
                            case_tac context "r" [] NONE 1 THEN
                            asm_full_simp_tac context 1)
  fun mk_upd_t {fldname,fldty} =
      Const(Sign.intern_const thy (suffix updateN (Long_Name.qualify record_name fldname)),
            (fldty --> fldty) --> (rty --> rty))

  fun prove_accupd_same (fld as {fldname, fldty}) = let
    val f = Free("f", fldty --> fldty)
    val acc = Const(Sign.intern_const thy (Long_Name.qualify record_name fldname), rty --> fldty)
    val upd = mk_upd_t fld
    val lhs_t = acc $ (upd $ f $ r_var)
    val rhs_t = f $ (acc $ r_var)
  in
    prove (mk_eqt(lhs_t, rhs_t))
  end
  val accupd_sames = Par_List.map prove_accupd_same fields

  fun prove_accupd_diff (acc, upd) = let
    val {fldname = accname, fldty = accty} = acc
    val {fldname = _, fldty = updty} = upd
    val acc_t = Const(Sign.intern_const thy (Long_Name.qualify record_name accname), rty --> accty)
    val upd_t = mk_upd_t upd
    val f = Free("f", updty --> updty)
    val lhs_t = acc_t $ (upd_t $ f $ r_var)
    val rhs_t = acc_t $ r_var
  in
    prove(mk_eqt(lhs_t, rhs_t))
  end
  val accupd_diffs = map prove_accupd_diff (cprod_less_diag fields)

  fun prove_updupd_same (fld as {fldname=_, fldty}) = let
    val ffty = fldty --> fldty
    val upd_t = mk_upd_t fld
    val f = Free("f", ffty)
    val g = Free("g", ffty)
    val lhs_t = upd_t $ f $ (upd_t $ g $ r_var)
    val comp = Const("Fun.comp", ffty --> (ffty --> ffty))
    val rhs_t = upd_t $ (comp $ f $ g) $ r_var
  in
    prove(mk_eqt(lhs_t, rhs_t))
  end
  val updupd_sames = Par_List.map prove_updupd_same fields

  fun prove_updupd_diff (upd1, upd2) = let
    val {fldname = _, fldty = updty1} = upd1
    val {fldname = _, fldty = updty2} = upd2
    val upd1_t = mk_upd_t upd1
    val upd2_t = mk_upd_t upd2
    val f = Free("f", updty1 --> updty1)
    val g = Free("g", updty2 --> updty2)
    val lhs_t = upd1_t $ f $ (upd2_t $ g $ r_var)
    val rhs_t = upd2_t $ g $ (upd1_t $ f $ r_var)
  in
    prove(mk_eqt(rhs_t, lhs_t))
  end
  val updupd_diffs = Par_List.map prove_updupd_diff (lower_triangle fields)

  fun prove_idupdates (fld as {fldname, fldty}) = let
    val upd_t = mk_upd_t fld
    val acc_t = Const(Sign.intern_const thy (Long_Name.qualify record_name fldname), rty --> fldty)
    val K = K_rec fldty
  in
    prove(mk_eqt(upd_t $ (K $ (acc_t $ r_var)) $ r_var, r_var))
  end
  val idupdates = Par_List.map prove_idupdates fields

  (* proves that (| fld1 = fld1 v, fld2 = fld2 v, fld3 = fld3 v,..|) = v *)
  val idupd_value1 = let
    fun mk_arg {fldname, fldty} acc = let
      val acc_t = Const(Sign.intern_const thy (Long_Name.qualify record_name fldname), rty --> fldty)
    in
      acc $ (acc_t $ r_var)
    end
  in
    prove(mk_eqt(constructor_t |> fold mk_arg fields, r_var))
  end

  (* proves that u (| fld1 := fld1 v, fld2 := fld2 v, ... |) = v *)
  val idupd_value2 = let
    fun mk_arg (fld as {fldname, fldty}) t = let
      val acc_t = Const(Sign.intern_const thy (Long_Name.qualify record_name fldname), rty --> fldty)
      val upd_t = mk_upd_t fld
      val K = K_rec fldty
    in
      upd_t $ (K $ (acc_t $ r_var)) $ t
    end
  in
    Goal.prove_global_future
      thy [] []
      (mk_prop (mk_eqt(r_var' |> fold mk_arg fields, r_var)))
      (fn {context,...} => case_tac context "r" [] NONE 1 THEN
                         case_tac context "r'" [] NONE 1 THEN
                         asm_full_simp_tac context 1)
  end

  val idupd_complete = let
    fun mk_arg_upd (fld as {fldname, fldty}) t = let
      val upd_t = mk_upd_t fld
      val K = K_rec fldty
      val fld_var = Free(fldname, fldty)
    in
      upd_t $ (K $ fld_var) $ t
    end
    fun mk_arg_constr {fldname, fldty} acc = let
      val fld_var = Free(fldname, fldty)
    in
      acc $ fld_var
    end
  in
    Goal.prove_global_future
      thy [] []
      (mk_prop (mk_eqt(r_var |> fold mk_arg_upd fields, constructor_t |> fold mk_arg_constr fields)))
      (fn {context,...} => case_tac context "r" [] NONE 1 THEN
                         asm_full_simp_tac context 1)
  end

  (* proves a fold congruence, used for eliminating the accessor
     within the body of the updator more generally than the idupdate
     case. *)
  fun prove_fold_cong (idupdate, updupd_same) = let
    val upd = (head_of o fst o HOLogic.dest_eq
                 o HOLogic.dest_Trueprop o Thm.concl_of) idupdate;
    val ctxt = Proof_Context.init_global thy;
    val ct  = Thm.cterm_of ctxt;
    val cgE = infer_instantiate ctxt [(#1(dest_Var updvar), ct upd)] updcong_foldE;
  in [idupdate, updupd_same] MRS cgE end;

  val fold_congs = Par_List.map prove_fold_cong (idupdates ~~ updupd_sames);

  fun add_thms (_, []) thy = thy
    | add_thms (sfx, thms) thy =
        (Global_Theory.add_thmss [
          ( (Binding.name (record_name ^ sfx), thms), [Simplifier.simp_add])] thy)
        |> #2
        |> add_recursive_record_thms thms []

  fun add_fold_thms (_, []) thy = thy
    | add_fold_thms (sfx, thms) thy =
    let
      val (thms', thy') = thy
         |> Global_Theory.add_thmss [((Binding.name(record_name ^ sfx), thms), [])];
    in
      HoarePackage.add_foldcongs (flat thms') thy'
      |> add_recursive_record_thms [] thms
    end;
in
  thy |> add_thms ("_accupd_same", accupd_sames)
      |> add_thms ("_accupd_diff", accupd_diffs)
      |> add_thms ("_updupd_same", updupd_sames)
      |> add_thms ("_updupd_diff", updupd_diffs)
      |> add_thms ("_idupdates",   idupd_value1 :: idupd_value2 :: idupd_complete :: idupdates)
      |> add_fold_thms ("_fold_congs", fold_congs)
      |> pair constructor
end



fun define_record_type records thy = let
  (* define algebraic types *)
  fun mk_one_type {record_name, fields} =
      ((Binding.name record_name, [], NoSyn),
       [(Binding.name record_name, map (fn f => #fldty f) fields, NoSyn)])

  fun mk_info thy ({record_name:string, fields}, (constructor, updates)) =
      (Sign.intern_type thy record_name,
       {constructor = constructor,
        fields=map (fn {fldname, fldty} => (Sign.intern_const thy (Long_Name.qualify record_name fldname), fldty)) fields,
        updates=map (fn (updname, updty) => (Sign.intern_const thy (Long_Name.qualify record_name updname), updty)) updates});

  val (_, thy) =
      BNF_LFP_Compat.add_datatype
          []
          (map mk_one_type records)
          thy
  val _ = Feedback.informStr (Proof_Context.init_global thy) (0, "Defined struct types: "^
                  String.concat (map (fn x => #record_name x ^ " ") records))


in
  thy
  |> fold_map define_functions records
  ||> fold_map prove_record_rewrites records
  |> (fn (updatess, (constructors, thy)) => fold add_info (map (mk_info thy) (records ~~ (constructors ~~ updatess))) thy)
end;

(*
add_datatype_i
  true     (* whether to check for some error condition *)
  false    (* use top-level declaration or not,
                with false, constructors will get called Thy.foo.zero etc *)
  ["foo", "bar"]  (* names for theorems *)
  [([], "foo", NoSyn,                     (* type-name, list for arguments *)
    [("zero", [], NoSyn),                 (* constructors for given type *)
     ("suc", [Type(Sign.full_name thy "bar", [])], NoSyn)]),
   ([], "bar", NoSyn,
    [("b1", [TermsTypes.nat], NoSyn),
     ("b2", [TermsTypes.bool, Type(Sign.full_name thy "foo", [])], NoSyn)])]
  thy;

use "recursive_records/recursive_record_package.ML";
val thy0 = the_context();
val thy = RecursiveRecordPackage.define_record_type
  [{record_name = "lnode",
    fields = [{fldname = "data1", fldty = TermsTypes.nat},
              {fldname = "data2", fldty = TermsTypes.nat},
              {fldname = "next",
               fldty = TermsTypes.mk_ptr_ty
                         (Type(Sign.full_name thy0 "lnode", []))}]}]
  thy0;
print_theorems thy;

*)
end;
