(*
 * Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
 * Copyright (c) 2022 Apple Inc. All rights reserved.
 *
 * SPDX-License-Identifier: BSD-2-Clause
 *)

theory CProof
imports
  "umm_heap/SepFrame"
  "Simpl.Vcg"
  "umm_heap/StructSupport"
  "umm_heap/ArrayAssertion"
  "AutoCorres_Utils"
  "Match_Cterm"
  "ML_Infer_Instantiate"
begin


(* name generation is the only thing this theory wants, but that
   depends on Absyn, which depends on a bunch of other stuff. *)
ML_file "General.ML"
ML_file "SourcePos.ML"
ML_file "SourceFile.ML"
ML_file "Region.ML"
ML_file "Binaryset.ML"
ML_file "Feedback.ML"
ML_file "basics.ML"
ML_file "MString.ML"

ML_file "TargetNumbers-sig.ML"
ML_file "./umm_heap/ARM/TargetNumbers_ARM.ML"
ML_file "./umm_heap/ARM64/TargetNumbers_ARM64.ML"
ML_file "./umm_heap/ARM_HYP/TargetNumbers_ARM_HYP.ML"
ML_file "./umm_heap/RISCV64/TargetNumbers_RISCV64.ML"
ML_file "./umm_heap/X64/TargetNumbers_X64.ML"
ML_file "./umm_heap/TargetNumbers.ML"

ML_file "RegionExtras.ML"
ML_file "Absyn-CType.ML"
ML_file "Absyn-Expr.ML"
ML_file "Absyn-StmtDecl.ML"
ML_file "Absyn.ML"
ML_file "Absyn-Serial.ML"
ML_file "../lib/ml-helpers/StringExtras.ML"
ML_file "name_generation.ML"


(* set up hoare package to rewrite state updates more *)
setup \<open>
  Hoare.add_foldcongsimps [@{thm "update_update"}, @{thm "o_def"}]
\<close>


(* Syntax for apply antiquotation parsing explicitly *)
syntax
  "_quote"  :: "'b => ('a => 'b)"  ("([.[_].])" [0] 1000)

(* Override assertion translation so we can apply the parse translations below
   and add \<star> syntax. *)
syntax
  "_heap" :: "'b \<Rightarrow> ('a \<Rightarrow> 'b)"
  "_heap_state" :: "'a" ("\<zeta>") (* fixme: horrible syntax *)
  "_heap_stateOld" :: "('a \<Rightarrow> 'b) \<Rightarrow> 'b" ("\<^bsup>_\<^esup>\<zeta>" [100] 100) (* fixme: horrible syntax *)

  "_derefCur" :: "('a \<Rightarrow> 'b) \<Rightarrow> 'b" ("\<star>_" [100] 100)
  "_derefOld" :: "'a \<Rightarrow> ('a \<Rightarrow> 'b) \<Rightarrow> 'b" ("\<^bsup>_\<^esup>\<star>_" [100,100] 100)

translations
  "{|b|}" => "CONST Collect (_quote (_heap b))"

definition sep_app :: "(heap_state \<Rightarrow> bool) \<Rightarrow> heap_state \<Rightarrow> bool" where
  "sep_app P s \<equiv> P s"

definition hrs_id :: "heap_raw_state \<Rightarrow> heap_raw_state" where
  "hrs_id \<equiv> id"

declare hrs_id_def [simp add]

parse_translation \<open>
let
  fun ac x = Syntax.const "_antiquoteCur" $ Syntax.const x
  fun aco x y = Syntax.const y $ (Syntax.const "globals" $ x)
  fun hd a = a NameGeneration.global_heap_var
  fun d a = Syntax.const "hrs_htd" $ hd a
  fun repl (Abs (s,T,t)) = Abs (s,T,repl t)
    | repl (Const ("_h_t_valid",_)$x) = Syntax.const "h_t_valid" $ d ac $ Syntax.const "c_guard" $ x
    | repl (Const ("_derefCur",_)$x) = Syntax.const "the" $
        (Syntax.const "lift_t" $ hd ac $ x)
    | repl (Const ("_derefOld",_)$x$y) = Syntax.const "the" $
        (Syntax.const "lift_t" $ hd (aco x) $ y)
    | repl (Const ("_heap_state",_)) = Syntax.const "hrs_id" $ hd ac
    | repl (Const ("_heap_stateOld",_)$x) = Syntax.const "hrs_id" $ hd (aco x)
    | repl (x$y) = repl x $ repl y
    | repl x = x
  fun heap_assert_tr [b] = repl b
    | heap_assert_tr ts = raise TERM ("heap_assert_tr", ts);
in [("_heap",K heap_assert_tr)] end
\<close>


(* Separation logic assertion parse translation *)
parse_translation \<open>
let
  fun ac x = Syntax.const "_antiquoteCur" $ Syntax.const x
  fun aco x y = Syntax.const y $ (Syntax.const "globals" $ x)
  fun hd a = Syntax.const "lift_state" $ (a NameGeneration.global_heap_var)
  fun st2 (Abs (s,T,t)) n = Abs (s,T,st2 t (n+1))
    | st2 (Bound k) n = Bound (if k < n then k else k + 1)
    | st2 (x$y) n = st2 x n $ st2 y n
    | st2 x _ = x
  fun st1 (Abs (s,T,t)) n = Abs (s,T,st1 t (n+1))
    | st1 (Bound k) n = Bound (if k < n then k else k + 1)
    | st1 (Const ("sep_empty",_)) n = Syntax.const "sep_empty" $ Bound n
    | st1 (Const ("sep_map",_)$x$y) n = Syntax.const "sep_map" $
        (st2 x n) $ (st2 y n) $ Bound n
    | st1 (Const ("sep_map'",_)$x$y) n = Syntax.const "sep_map'" $
        (st2 x n) $ (st2 y n) $ Bound n
    | st1 (Const ("sep_conj",_)$x$y) n = Syntax.const "sep_conj" $
        (nst2 x n) $ (nst2 y n) $ Bound n
    | st1 (Const ("sep_impl",_)$x$y) n = Syntax.const "sep_impl" $
        (nst2 x n) $ (nst2 y n) $ Bound n
    | st1 (x$y) n = st1 x n $ st1 y n
    | st1 x _ = x
  and new_heap t = Abs ("s",dummyT,st1 t 0)
  and nst2 x n = new_heap (st2 x n);
  fun sep_tr [t] = Syntax.const "sep_app" $ (*new_heap *) t $ hd ac
    | sep_tr ts = raise TERM ("sep_tr", ts);
in [("_sep_assert",K sep_tr)] end
\<close>

lemma c_null_guard:
  "c_null_guard (p::'a::mem_type ptr) \<Longrightarrow> p \<noteq> NULL"
  by (fastforce simp: c_null_guard_def intro: intvl_self)

lemma (in mem_type) c_guard_no_wrap:
  fixes p :: "'a ptr"
  assumes cgrd: "c_guard p"
  shows   "ptr_val p \<le> ptr_val p + of_nat (size_of TYPE('a) - 1)"
  using cgrd unfolding c_guard_def c_null_guard_def
  apply -
  apply (erule conjE)
  apply (erule contrapos_np)
  apply (simp add: intvl_def)
  apply (drule word_wrap_of_natD)
  apply (erule exE)
  apply (rule exI)
  apply (simp add: nat_le_Suc_less size_of_def  wf_size_desc_gt(1))
  done

lemma word_le_unat_bound:
  fixes a::"'a ::len word"
  assumes "a \<le> a + b"
  shows "unat a + unat b < 2 ^ LENGTH('a)"
  using assms no_olen_add_nat by blast


lemma (in mem_type) c_guard_no_wrap':
  fixes p :: "'a ptr"
  assumes cgrd: "c_guard p"
  shows   "unat (ptr_val p) + size_of TYPE('a) \<le> addr_card"
proof -

  have szb: "size_of TYPE('a) < addr_card"
    by (simp add: local.max_size)
 
 
  have not_null: "0 < size_of TYPE('a)"
    by (simp add: size_of_def wf_size_desc_gt(1))


  have sz_le: "size_of TYPE('a) - Suc 0 < 2 ^ LENGTH(addr_bitsize)"
    using len_of_addr_card less_imp_diff_less szb by simp
  
  with szb 
  have eq:  "unat (word_of_nat (size_of TYPE('a) - 1)::addr_bitsize word) = size_of (TYPE('a)) - 1"
    apply (subst unat_of_nat_eq)
     apply (simp_all )
    done
  from word_le_unat_bound [OF c_guard_no_wrap [OF cgrd], simplified eq] 
  show ?thesis
    by (simp add: addr_card)
qed

definition
c_fnptr_guard_def: "c_fnptr_guard (fnptr::unit ptr) \<equiv> ptr_val fnptr \<noteq> 0"

lemma c_fnptr_guard_NULL [simp]: "c_fnptr_guard NULL = False"
  by (simp add: c_fnptr_guard_def)

lemma c_guardD:
  "c_guard (p::'a::mem_type ptr) \<Longrightarrow> ptr_aligned p \<and> p \<noteq> NULL"
  by (clarsimp simp: c_guard_def c_null_guard)

lemma c_guard_ptr_aligned:
  "c_guard p \<Longrightarrow> ptr_aligned p"
  by (simp add: c_guard_def)

lemma c_guard_NULL:
  "c_guard (p::'a::mem_type ptr) \<Longrightarrow> p \<noteq> NULL"
  by (simp add: c_guardD)

lemma c_guard_NULL_simp [simp]:
  "\<not> c_guard (NULL::'a::mem_type ptr)"
  by (force dest: c_guard_NULL)

lemma c_guard_mono:
  "guard_mono (c_guard::'a::mem_type ptr_guard) (c_guard::'b::mem_type ptr_guard)"
  apply(clarsimp simp: guard_mono_def c_guard_def)
  subgoal premises prems for n f p
  proof -
    have "guard_mono (ptr_aligned::'a::mem_type ptr_guard) (ptr_aligned::'b::mem_type ptr_guard)"
      using prems by - (rule ptr_aligned_mono)
    then show ?thesis
      using prems
      apply -
      apply(clarsimp simp: guard_mono_def ptr_aligned_def c_null_guard_def typ_uinfo_t_def)
      apply(frule field_lookup_export_uinfo_Some_rev)
      apply clarsimp
      apply(drule field_tag_sub [where p=p])
      apply(clarsimp simp: field_lvalue_def field_offset_def field_offset_untyped_def typ_uinfo_t_def)
      apply(metis (mono_tags, opaque_lifting) export_size_of subsetD typ_uinfo_t_def)
      done
  qed
  done

lemma c_guard_NULL_fl:
  "\<lbrakk> c_guard (p::'a::mem_type ptr); field_lookup (typ_info_t TYPE('a)) f 0 = Some (t,n);
     export_uinfo t = typ_uinfo_t TYPE('b::mem_type) \<rbrakk>
   \<Longrightarrow> 0 < &(p\<rightarrow>f)"
  using c_guard_mono
  apply(clarsimp simp: guard_mono_def)
  apply((erule allE)+, erule impE)
   apply(fastforce dest: field_lookup_export_uinfo_Some simp: typ_uinfo_t_def)
  apply(drule field_lookup_export_uinfo_Some)
  apply(simp add: field_lvalue_def field_offset_def field_offset_untyped_def typ_uinfo_t_def)
  apply(clarsimp simp: c_guard_def)
  apply(drule c_null_guard)+
  apply(clarsimp simp: word_neq_0_conv)
  done

lemma c_guard_ptr_aligned_fl:
  "\<lbrakk> c_guard (p::'a::mem_type ptr); field_lookup (typ_info_t TYPE('a)) f 0 = Some (t,n);
     export_uinfo t = typ_uinfo_t TYPE('b::mem_type) \<rbrakk> \<Longrightarrow>
   ptr_aligned ((Ptr &(p\<rightarrow>f))::'b ptr)"
  using c_guard_mono
  apply(clarsimp simp: guard_mono_def)
  apply((erule allE)+, erule impE)
   apply(fastforce dest: field_lookup_export_uinfo_Some simp: typ_uinfo_t_def)
  apply(drule field_lookup_export_uinfo_Some)
  apply(simp add: c_guard_def field_lvalue_def field_offset_def field_offset_untyped_def typ_uinfo_t_def)
  done

(* StrictC guard separation syntax translations *)

(* fixme: make these abbreviations *)
syntax
  "_sep_map" :: "'a::c_type ptr \<Rightarrow> 'a \<Rightarrow> heap_assert" ("_ \<mapsto> _" [56,51] 56) (* fixme: clashes with map update *)
  "_sep_map_any" :: "'a::c_type ptr \<Rightarrow> heap_assert" ("_ \<mapsto> -" [56] 56)
  "_sep_map'" :: "'a::c_type ptr \<Rightarrow> 'a \<Rightarrow> heap_assert" ("_ \<hookrightarrow>  _" [56,51] 56)
  "_sep_map'_any" :: "'a::c_type ptr \<Rightarrow> heap_assert" ("_ \<hookrightarrow> -" [56] 56)
  "_tagd" :: "'a::c_type ptr \<Rightarrow> heap_assert" ("\<turnstile>\<^sub>s _" [99] 100)

translations
  "p \<mapsto> v" == "p \<mapsto>\<^sup>i\<^sub>(CONST c_guard) v"
  "p \<mapsto> -" == "p \<mapsto>\<^sup>i\<^sub>(CONST c_guard) -"
  "p \<hookrightarrow> v" == "p \<hookrightarrow>\<^sup>i\<^sub>(CONST c_guard) v"
  "p \<hookrightarrow> -" == "p \<hookrightarrow>\<^sup>i\<^sub>(CONST c_guard) -"
  "\<turnstile>\<^sub>s p" == "CONST c_guard \<turnstile>\<^sub>s\<^sup>i p"

term "x \<mapsto> y"
term "(x \<mapsto> y \<and>\<^sup>* y \<mapsto> z) s"
term "(x \<mapsto> y \<and>\<^sup>* y \<mapsto> z) \<and>\<^sup>* x \<mapsto> y"
term "\<turnstile>\<^sub>s p"

lemma sep_map_NULL [simp]:
  "NULL \<mapsto> (v::'a::mem_type) = sep_false"
  by (force simp: sep_map_def sep_map_inv_def c_guard_def
            dest: lift_typ_heap_g sep_conjD c_null_guard)

lemma sep_map'_NULL_simp [simp]:
  "NULL \<hookrightarrow> (v::'a::mem_type) = sep_false"
  apply(simp add: sep_map'_def sep_map'_inv_def sep_conj_ac)
  apply(subst sep_conj_com, subst sep_map_inv_def [symmetric])
  apply simp
  done

lemma sep_map'_ptr_aligned:
  "(p \<hookrightarrow> v) s \<Longrightarrow> ptr_aligned p"
  by (rule c_guard_ptr_aligned) (erule sep_map'_g)

lemma sep_map'_NULL:
  "(p \<hookrightarrow> (v::'a::mem_type)) s \<Longrightarrow> p \<noteq> NULL"
  by (rule c_guard_NULL) (erule sep_map'_g)

lemma tagd_sep_false [simp]:
  "\<turnstile>\<^sub>s (NULL::'a::mem_type ptr) = sep_false"
  by (auto simp: tagd_inv_def tagd_def dest!: sep_conjD s_valid_g)

(* Print translations for pointer dereferencing in program statements and
   expressions. *)
syntax (output)
  "_Deref" :: "'b \<Rightarrow> 'b" ("*_" [1000] 1000)
  "_AssignH" :: "'b => 'b => ('a,'p,'f) com" ("(2*_ :==/ _)" [30, 30] 23)

print_translation \<open>
let
  fun deref (Const ("_antiquoteCur",_)$Const (h,_)) p =
      if h=NameGeneration.global_heap then Syntax.const "_Deref" $ p else
        raise Match
    | deref h p = raise Match
  fun lift_tr [h,p] = deref h p
    | lift_tr ts = raise Match
  fun deref_update (Const ("heap_update",_)$l$r$(Const ("_antiquoteCur",_)$
    Const (h,_))) =
      if h=NameGeneration.global_heap then Syntax.const "_AssignH" $ l $ r
        else raise Match
    | deref_update x = raise Match
  (* First we need to determine if this is a heap update or normal assign *)
  fun deref_assign (Const ("_antiquoteCur",_)$Const (h,_)) r =
      if h=NameGeneration.global_heap then deref_update r else
        raise Match
    | deref_assign l r = raise Match
  fun assign_tr [l,r] = deref_assign l r
    | assign_tr ts = raise Match
in [("CTypesDefs.lift",K lift_tr),("_Assign",K assign_tr)] end
\<close>

print_translation \<open>
let
  fun sep_app_tr [l,r] = Syntax.const "_sep_assert" $ l
    | sep_app_tr ts = raise Match
in [("sep_app",K sep_app_tr)] end
\<close>

syntax "_h_t_valid" :: "'a::c_type ptr \<Rightarrow> bool" ("\<Turnstile>\<^sub>t _" [99] 100)

(* will only work when globals record is defined
term "\<lbrace> \<Turnstile>\<^sub>t bar \<rbrace>" *)

abbreviation "lift_t_c" :: "heap_mem \<times> heap_typ_desc \<Rightarrow> 'a::c_type typ_heap" where
  "lift_t_c s == lift_t c_guard s"

syntax "_h_t_valid" :: "heap_typ_desc \<Rightarrow> 'a::c_type ptr \<Rightarrow> bool"  ("_ \<Turnstile>\<^sub>t _" [99,99] 100)
translations
  "d \<Turnstile>\<^sub>t p" == "d,CONST c_guard \<Turnstile>\<^sub>t p"

lemma h_t_valid_c_guard:
  "d \<Turnstile>\<^sub>t p \<Longrightarrow> c_guard p"
  by (clarsimp simp: h_t_valid_def)

lemma h_t_valid_NULL [simp]:
  "\<not> d \<Turnstile>\<^sub>t (NULL::'a::mem_type ptr)"
  by (clarsimp simp: h_t_valid_def dest!: c_guard_NULL)

lemma h_t_valid_ptr_aligned:
  "d \<Turnstile>\<^sub>t p  \<Longrightarrow> ptr_aligned p"
  by (auto simp: h_t_valid_def dest: c_guard_ptr_aligned)

lemma lift_t_NULL:
  "lift_t_c s (NULL::'a::mem_type ptr) = None"
  by (cases s) (auto simp: lift_t_if)

lemma lift_t_ptr_aligned [simp]:
  "lift_t_c s p = Some v \<Longrightarrow> ptr_aligned p"
  by (auto dest: lift_t_g c_guard_ptr_aligned)

lemmas c_typ_rewrs = typ_rewrs h_t_valid_ptr_aligned lift_t_NULL

datatype 'gx c_exntype = Break | Return | Continue | Goto string | Nonlocal 'gx

definition "is_local x = (x = Break \<or> x = Return \<or> x = Continue \<or> (\<exists>l. x = Goto l))"

lemma is_local_simps [simp]: 
  "is_local Break" 
  "is_local Return" 
  "is_local Continue"
  "is_local (Goto l)"
  "\<not>is_local (Nonlocal x)"
  by (auto simp add: is_local_def)

primrec the_Nonlocal where
"the_Nonlocal (Nonlocal x) = x"

datatype strictc_errortype =
         Div_0
       | C_Guard (* merge of Alignment and Null_Dereference *)
       | MemorySafety
       | ShiftError
       | SideEffects
       | ArrayBounds
       | SignedArithmetic
       | DontReach
       | GhostStateError
       | UnspecifiedSyntax
       | OwnershipError
       | UndefinedFunction
       | AdditionalError string
       | ImpossibleSpec
       | AssumeError
       | StackOverflow

definition unspecified_syntax_error :: "string \<Rightarrow> bool" where
  "unspecified_syntax_error s = False"


record ('g, 'l, 'e) state = "('g, 'l) StateSpace.state_locals" +
  global_exn_var'_' :: "'e c_exntype"


lemmas hrs_simps = hrs_mem_update_def hrs_mem_def hrs_htd_update_def hrs_htd_def

lemma sep_map'_lift_lift:
  fixes pa :: "'a :: mem_type ptr" and xf :: "'a \<Rightarrow> 'b :: mem_type"
  assumes fl: "field_lookup (typ_info_t TYPE('a)) f 0 \<equiv>
                 Some (adjust_ti (typ_info_t TYPE('b)) xf (xfu \<circ> (\<lambda>x _. x)), m')"
  and xf_xfu: "fg_cons xf (xfu \<circ> (\<lambda>x _. x))"
  shows "(pa \<hookrightarrow> v)(lift_state h) \<Longrightarrow> CTypesDefs.lift (fst h) (Ptr &(pa\<rightarrow>f)) = xf v"
  using fl xf_xfu
  apply (clarsimp simp: o_def)
  apply (rule sep_map'_lift [OF sep_map'_field_map_inv, where g1=c_guard]; simp?)
     apply (subst (asm) surjective_pairing, assumption)
    apply (simp add: typ_uinfo_t_def export_tag_adjust_ti)
   apply (rule guard_mono_True)
  apply (simp add: o_def)
  done

lemma lift_t_update_fld_other:
  fixes val :: "'b :: mem_type" and ptr :: "'a :: mem_type ptr"
  assumes   fl: "field_ti TYPE('a) f = Some (adjust_ti (typ_info_t TYPE('b)) xf (xfu \<circ> (\<lambda>x _. x)))"
  and   xf_xfu: "fg_cons xf (xfu \<circ> (\<lambda>x _. x))"
  and     disj: "typ_uinfo_t TYPE('c :: mem_type) \<bottom>\<^sub>t typ_uinfo_t TYPE('b)"
  and       cl: "lift_t c_guard hp ptr = Some z"
  shows "(lift_t c_guard (hrs_mem_update (heap_update (Ptr &(ptr\<rightarrow>f)) val) hp)) =
  (lift_t c_guard hp :: 'c :: mem_type typ_heap)"
  (is "?LHS = ?RHS")
proof -
  let ?ati = "adjust_ti (typ_info_t TYPE('b)) xf (xfu \<circ> (\<lambda>x _. x))"
  have eui: "typ_uinfo_t TYPE('b) = export_uinfo (?ati)" using xf_xfu
    by (simp add: typ_uinfo_t_def export_tag_adjust_ti)

  have cl': "lift_t c_guard (fst hp, snd hp) ptr = Some z" using cl by simp

  show ?thesis using fl
    apply (clarsimp simp add: hrs_mem_update_def split_def field_ti_def split: option.splits)
    by (metis cl' disj eui fl h_t_valid_sub lift_t_h_t_valid lift_t_heap_update_same prod.collapse)
qed

lemma idupdate_compupdate_fold_congE:
  assumes idu: "\<And>r. upd (\<lambda>x. accr r) r = r"
  assumes cpu: "\<And>f f' r. upd f (upd f' r) = upd (f o f') r"
  and       r: "r = r'" and v: "accr r' = v'"
  and       f: "\<And>v. v' = v \<Longrightarrow> f v = f' v"
shows        "upd f r = upd f' r'"
proof -
  have "upd (f o (\<lambda>x. accr r')) r' = upd (f' o (\<lambda>x. accr r')) r'"
    by (simp add: o_def f v)
  then show ?thesis
    by (simp add: cpu[symmetric] idu r)
  qed

lemma field_lookup_field_ti:
  "field_lookup (typ_info_t TYPE('a :: c_type)) f 0 \<equiv> Some (a, b) \<Longrightarrow> field_ti TYPE('a) f = Some a"
  unfolding field_ti_def by simp

definition lvar_nondet_init ::
  "(('a \<Rightarrow> 'a) \<Rightarrow> (('g, 'l, 'e, 'z) state_scheme \<Rightarrow> ('g, 'l, 'e, 'z) state_scheme))
      \<Rightarrow> (('g, 'l, 'e, 'z) state_scheme, 'f, 'x) com" where
  "lvar_nondet_init upd \<equiv> Spec {(s, t). \<exists>v. t = (upd (\<lambda>_. v)) s}"

axiomatization
  asm_semantics :: "string \<Rightarrow> addr list \<Rightarrow> (heap_mem \<times> 'a) \<Rightarrow> (addr \<times> (heap_mem \<times> 'a)) set" and
  asm_fetch :: "'s \<Rightarrow> (heap_mem \<times> 'a)" and
  asm_store :: "('s \<Rightarrow> 'b) \<Rightarrow> (heap_mem \<times> 'a) \<Rightarrow> 's \<Rightarrow> 's"
where
  asm_semantics_enabled: "\<forall>iv. asm_semantics nm addr iv \<noteq> {}" and
  asm_store_eq: "\<forall>x s. ghost_data (asm_store ghost_data x s) = ghost_data s"

definition
  asm_spec :: "'a itself \<Rightarrow> ('g \<Rightarrow> 'b) \<Rightarrow> bool \<Rightarrow> string
    \<Rightarrow> (addr \<Rightarrow> ('g, 'l, 'e, 'z) state_scheme \<Rightarrow> ('g, 'l, 'e, 'z) state_scheme)
    \<Rightarrow> (('g, 'l, 'e, 'z) state_scheme \<Rightarrow> addr list)
    \<Rightarrow> (('g, 'l, 'e, 'z) state_scheme \<times> ('g, 'l, 'e, 'z) state_scheme) set"
where
  "asm_spec ti gdata vol spec lhs vs
    = {(s, s'). \<exists>(v', (gl' :: (heap_mem \<times> 'a)))
                   \<in> asm_semantics spec (vs s) (asm_fetch (globals s)).
                        s' = lhs v' (globals_update (asm_store gdata gl') s)}"

lemma asm_spec_enabled:
  "\<exists>s'. (s, s') \<in> asm_spec ti gdata vol spec lhs vs"
  using asm_semantics_enabled[rule_format, where nm = spec
    and addr="vs s" and iv="asm_fetch (globals s)"]
  by (auto simp add: asm_spec_def)

lemma asm_specE:
  "\<lbrakk> (s, s') \<in> asm_spec (ti :: 'a itself) gdata vol spec lhs vs;
     \<And>v' gl'. \<lbrakk> (v', (gl' :: (heap_mem \<times> 'a))) \<in> asm_semantics spec (vs s) (asm_fetch (globals s));
                 s' = lhs v' (globals_update (asm_store gdata gl') s);
                 gdata (asm_store gdata gl' (globals s)) = gdata (globals s) \<rbrakk>
              \<Longrightarrow> P \<rbrakk>
  \<Longrightarrow> P"
  by (clarsimp simp: asm_spec_def asm_store_eq)

lemmas state_eqE = arg_cong[where f="\<lambda>s. (globals s, state.more s)", elim_format]

lemmas asm_store_eq_helper
    = arg_cong2[where f="(=)" and a="asm_store f v s"]
      arg_cong2[where f="(=)" and c="asm_store f v s"] for f v s

definition asm_semantics_ok_to_ignore :: "'a itself \<Rightarrow> bool \<Rightarrow> string \<Rightarrow> bool" where
  "asm_semantics_ok_to_ignore ti volatile specifier
    = (\<forall>xs gl. snd ` asm_semantics specifier xs (gl :: (heap_mem \<times> 'a)) = {gl})"

lemma heap_list_nth:
  "m < n \<Longrightarrow> heap_list hp n p ! m = hp (p + of_nat m)"
proof (induct m arbitrary: n p)
  case (0 n' p')
  thus ?case by (cases n', simp_all)
next
  case (Suc m' n' p')
  show ?case
  proof (cases n')
    case 0 thus ?thesis using \<open>Suc m' < n'\<close> by simp
  next
    case (Suc n'')
    hence "m' < n''" using \<open>Suc m' < n'\<close> by simp
    thus ?thesis using Suc
      by (simp add: Suc.hyps ac_simps)
  qed
qed

lemma heap_update_list_id':
  "heap_list hp n ptr = xs \<Longrightarrow> heap_update_list ptr xs hp = hp"
proof (induct xs arbitrary: ptr n)
  case Nil
  then show ?case by simp
next
  case (Cons x1 xs)
  then show ?case   
  by (cases n) (auto simp add: fun_upd_idem)
qed

lemma heap_update_list_concat_fold:
  assumes "ptr' = ptr + of_nat (length ys)"
  shows "heap_update_list ptr' xs (heap_update_list ptr ys s)
    = heap_update_list ptr (ys @ xs) s"
  unfolding assms
  apply (induct ys arbitrary: ptr s)
   apply simp
  apply simp
  apply (elim meta_allE)
  apply (erule trans[rotated])
  apply (simp add: field_simps)
  done

lemma heap_update_list_concat_fold_hrs_mem:
  "ptr' = ptr + of_nat (length ys) \<Longrightarrow>
   hrs_mem_update (heap_update_list ptr' xs)
        (hrs_mem_update (heap_update_list ptr ys) s)
    = hrs_mem_update (heap_update_list ptr (ys @ xs)) s"
  by (simp add: hrs_mem_update_def split_def
                heap_update_list_concat_fold)

lemmas heap_update_list_concat_unfold
    = heap_update_list_concat_fold[OF refl, symmetric]


lemma intvl_nowrap:
  fixes x :: "'a::len word"
  shows "\<lbrakk>y \<noteq> 0; unat y + z \<le> 2 ^ len_of TYPE('a)\<rbrakk> \<Longrightarrow> x \<notin> {x + y ..+ z}"
  apply clarsimp
  apply (drule intvlD)
  apply clarsimp
  apply (simp add: unat_arith_simps)
  apply (simp split: if_split_asm)
  by (metis add_le_imp_le_left le_unat_uoi less_imp_le_nat not_less)



lemma intvl_off_disj:
  fixes x :: addr
  assumes ylt: "y \<le> off"
  and    zoff: "z + off < 2 ^ word_bits"
  shows   "{x ..+ y} \<inter> {x + of_nat off ..+ z} = {}"
  using ylt zoff
  supply unsigned_of_nat [simp del]
  apply (cases "off = 0")
   apply simp
  apply (rule contrapos_pp [OF TrueI])
  apply (drule intvl_inter)
  apply (erule disjE)
  subgoal premises prems 
  proof -
    have "x \<notin> {x + word_of_nat off..+z}"
      apply (rule intvl_nowrap [where x = x and y = "of_nat off :: addr" and z = z])
      using prems 
       apply -
       apply (rule of_nat_neq_0)
        apply simp
       apply (unfold word_bits_len_of)
       apply simp
      apply (simp add: unat_of_nat word_bits_conv)
      done
    then show ?thesis using prems by simp
  qed
  subgoal
    apply (drule intvlD)
    apply clarsimp
    apply (drule (1) order_less_le_trans)
    apply (drule unat_cong)
    apply (simp add: unat_of_nat word_bits_conv)
    done
  done

lemma intvl_empty2:
  "({p ..+ n} = {}) = (n = 0)"
  by (auto simp add: intvl_def)


lemma heap_update_list_commute:
  "{p ..+ length xs} \<inter> {q ..+ length ys} = {}
      \<Longrightarrow> heap_update_list p xs (heap_update_list q ys hp)
        = heap_update_list q ys (heap_update_list p xs hp)"
  apply (cases "length xs < addr_card")
   apply (cases "length ys < addr_card")
    apply (rule ext, simp add: heap_update_list_value)
    apply blast
   apply (simp_all add: addr_card intvl_overflow intvl_empty2)
  done

lemma heap_update_commute:
  "\<lbrakk> {ptr_val p ..+ size_of TYPE('a)} \<inter> {ptr_val q ..+ size_of TYPE('b)} = {};
       wf_fd (typ_info_t TYPE('a)); wf_fd (typ_info_t TYPE('b)) \<rbrakk>
        \<Longrightarrow> heap_update p v (heap_update q (u :: 'b :: c_type) h)
              = heap_update q u (heap_update p (v :: 'a :: c_type) h)"
  apply (simp add: heap_update_def)
  apply (simp add: heap_update_list_commute heap_list_update_disjoint_same
                   to_bytes_def length_fa_ti size_of_def Int_commute)
  done

lemma heap_update_padding_commute:
  "\<lbrakk> {ptr_val p ..+ size_of TYPE('a)} \<inter> {ptr_val q ..+ size_of TYPE('b)} = {};
    length bs = size_of TYPE('a); length bs' = size_of TYPE('b);
       wf_fd (typ_info_t TYPE('a)); wf_fd (typ_info_t TYPE('b))\<rbrakk>
        \<Longrightarrow> heap_update_padding p v bs (heap_update_padding q (u :: 'b :: c_type) bs' h)
              = heap_update_padding q u bs' (heap_update_padding p (v :: 'a :: c_type) bs h)"
  apply (simp add: heap_update_padding_def)
  apply (simp add: heap_update_list_commute heap_list_update_disjoint_same
                   to_bytes_def length_fa_ti size_of_def Int_commute)

  done

lemma heap_update_padding_heap_update_commute:
  "\<lbrakk> {ptr_val p ..+ size_of TYPE('a)} \<inter> {ptr_val q ..+ size_of TYPE('b)} = {};
    length bs = size_of TYPE('a);
       wf_fd (typ_info_t TYPE('a)); wf_fd (typ_info_t TYPE('b))\<rbrakk>
        \<Longrightarrow> heap_update_padding p v bs (heap_update q (u :: 'b :: c_type) h)
              = heap_update q u (heap_update_padding p (v :: 'a :: c_type) bs h)"
  apply (simp add: heap_update_heap_update_padding_conv)
  apply (subst heap_update_padding_commute)
       apply (auto simp add: heap_list_update_disjoint_same heap_update_padding_def length_fa_ti size_of_def to_bytes_def)
  done

lemma heap_update_heap_update_padding_commute:
  "\<lbrakk> {ptr_val p ..+ size_of TYPE('a)} \<inter> {ptr_val q ..+ size_of TYPE('b)} = {};
     length bs' = size_of TYPE('b);
       wf_fd (typ_info_t TYPE('a)); wf_fd (typ_info_t TYPE('b))\<rbrakk>
        \<Longrightarrow> heap_update p v (heap_update_padding q (u :: 'b :: c_type) bs' h)
              = heap_update_padding q u bs' (heap_update p (v :: 'a :: c_type) h)"
  apply (simp add: heap_update_heap_update_padding_conv)
  apply (subst heap_update_padding_commute)
       apply (auto simp add: heap_list_update_disjoint_same heap_update_padding_def length_fa_ti size_of_def to_bytes_def
       inf_commute )
  done

lemma addr_card_wb:
  "addr_card = 2 ^ word_bits"
  by (simp add: addr_card_def card_word word_bits_conv)

lemma fold_cong':
  "a = b \<Longrightarrow> xs = ys \<Longrightarrow> (\<And>x. x \<in> set xs =simp=> f x = g x)
    \<Longrightarrow> fold f xs a = fold g ys b"
  unfolding simp_implies_def
  by (metis fold_cong)


lemma arg_cong_meta: "x = y \<Longrightarrow> (f x = f y) \<equiv> True"
  by simp

simproc_setup arg_cong (\<open>x = y\<close>) = \<open>fn phi => fn ctxt => fn ct =>
  let
    val {f, x, y, ...} = @{cterm_match (fo) \<open>?f ?x = ?f ?y\<close>} ct
    val eq = \<^infer_instantiate>\<open>x = x and y = y in cprop \<open>x = y\<close>\<close> ctxt
  in
    try (Goal.prove_internal ctxt [] eq) (fn _ => asm_full_simp_tac ctxt 1) 
    |> Option.map (fn thm => (@{thm arg_cong_meta} OF [thm]))
  end
  handle Pattern.MATCH => NONE | Match => NONE
\<close>

declare [[simproc del: arg_cong]]

lemma fun_cong_meta: "f = g \<Longrightarrow> (f x = g x) \<equiv> True"
  by simp

simproc_setup fun_cong (\<open>x = y\<close>) = \<open>fn phi => fn ctxt => fn ct =>
  let
    val {f, g, x, ...} = @{cterm_match (fo) \<open>?f ?x = ?g ?x\<close>} ct
    val ctxt = ctxt delsimps @{thms fun_eq_iff} (* prevent looping *)
    val eq = \<^infer_instantiate>\<open>f = f and g = g in cprop \<open>f = g\<close>\<close> ctxt
  in
    try (Goal.prove_internal ctxt [] eq) (fn _ => asm_full_simp_tac ctxt 1) 
    |> Option.map (fn thm => (@{thm fun_cong_meta} OF [thm]))
  end
  handle Pattern.MATCH => NONE | Match => NONE
\<close>

declare [[simproc del: fun_cong]]

abbreviation
  ptr_span :: "'a::c_type ptr \<Rightarrow> addr set" where
  "ptr_span p \<equiv> {ptr_val p ..+ size_of TYPE('a)}"

lemma nat_index_bound:
  "j * a + k < a * b" if jk: "j < b" "k < a" for j k :: nat
proof (rule less_le_trans)
  show "j * a + k < (b - 1) * a + a"
    using jk by (intro add_le_less_mono mult_le_mono1) simp
  show "(b - 1) * a + a \<le> a * b"
    using jk by (simp add: diff_mult_distrib)
qed

lemma disj_ptr_span_ptr_neq:
 "disjnt (ptr_span (p::'a::mem_type ptr)) (ptr_span (q::'a::mem_type ptr)) \<Longrightarrow>
  p \<noteq> q"
  unfolding disjnt_def
  by (metis empty_iff inf.idem mem_type_self)

lemma field_lvalue_same_conv': "&(p::'a:: c_type ptr\<rightarrow>f) = &(q::'a:: c_type ptr\<rightarrow>f) \<longleftrightarrow> p = q"
  by (simp add: field_lvalue_def)

section \<open>(Partial) Pointer Lenses\<close>

subsection \<open>\<open>pointer_lense\<close>\<close>

named_theorems
read_write_same and
read_write_other and
write_cong and
map_other_commute

locale pointer_lense =
  fixes r::"'s \<Rightarrow> 'a::mem_type ptr \<Rightarrow> 'b"
  fixes w::"'a ptr \<Rightarrow> ('b \<Rightarrow> 'b) \<Rightarrow> 's \<Rightarrow> 's"
  assumes read_write_same[read_write_same]: "r (w p f s) p = f (r s p)" (* FIXME: put to simpset ? *)
  assumes write_same: "f (r s p) = (r s p) \<Longrightarrow> w p f s = s"
  assumes write_comp[update_compose, simp]: "w p f (w p g s) = w p (f o g) s"
  assumes write_other_commute[map_other_commute]: "disjnt (ptr_span p) (ptr_span q) \<Longrightarrow> w q g (w p f s) = w p f (w q g s)"
begin

lemma read_write_other[read_write_other]:
  "disjnt (ptr_span p) (ptr_span p') \<Longrightarrow> r (w p f s) p' = r s p'"
  apply (subst write_same[symmetric, of "\<lambda>x. r s p'" s p'])
  apply simp
  apply (subst write_other_commute[symmetric])
  apply assumption
  apply (rule read_write_same)
  done

lemma write_cong[write_cong]: "f (r s p) = f' (r s p) \<Longrightarrow> w p f s = w p f' s"
  by (metis K_record_comp read_write_same write_comp write_same)

lemma write_read: "w p (\<lambda>_. r s p) s = s"
  by (simp add: write_same)

lemma write_id: "w p (\<lambda>x. x) s = s"
  by (simp add: write_same)

lemma read_write_pointwise_id: "r (w p (\<lambda>x. x) s) = r s"
  using write_same by simp

end

subsection \<open>\<open>partial_pointer_lense\<close>\<close>

locale partial_pointer_lense = is_scene m for m :: "'a::c_type scene" +
  fixes r :: "'h \<Rightarrow> 'a ptr \<Rightarrow> 'a upd"
  fixes w :: "'a ptr \<Rightarrow> 'a \<Rightarrow> 'h upd"
  assumes r_w[simp]: "r (w p x h) p y = m x y"
  assumes w_w[simp]: "w p x (w p y h) = w p x h"
  assumes w_r[simp]: "w p (r h p x) h = h"
  assumes w_m[simp]: "w p (m x y) h = w p x h"
  assumes w_w_disj: "disjnt (ptr_span p) (ptr_span q) \<Longrightarrow> w p x (w q y h) = w q y (w p x h)"
begin

lemma m_r[simp]: "m (r h p x) y = r h p y"
  by (metis r_w w_r)

lemma r_w_disj[simp]: "disjnt (ptr_span p) (ptr_span q) \<Longrightarrow> r (w q x h) p y = r h p y"
  by (metis r_w w_r w_w_disj)

lemma r_m: "r h p (m x y) = r h p y"
  by (metis m_r right)

end

lemma partial_pointer_lenseI:
  fixes get upd r w
  assumes "lense get upd"
  assumes "pointer_lense r w"
  shows "partial_pointer_lense
    (\<lambda>a b. upd (\<lambda>_. get a) b)
    (\<lambda>h p. upd (\<lambda>_. r h p))
    (\<lambda>p x. w p (\<lambda>_. get x))"
proof -
  interpret lense get upd by fact
  interpret pointer_lense r w by fact
  show ?thesis
    apply unfold_locales
    subgoal by simp
    subgoal by (simp add: comp_def)
    subgoal by simp
    subgoal by (simp add: read_write_same)
    subgoal by (simp add: comp_def)
    subgoal by (simp add: write_same)
    subgoal by simp
    subgoal by (simp add: write_other_commute disjnt_def)
    done
qed

lemma pointer_lense_of_lense_fld:
  assumes "lense r w"
  shows "pointer_lense (\<lambda>h p. r h (PTR('a) &(p\<rightarrow>f))) (\<lambda>p v. w (upd_fun (PTR('a) &(p\<rightarrow>f)) v))"
proof -
  interpret lense r w by fact
  show ?thesis
    apply unfold_locales
    apply simp
    apply (simp add: upd_same upd_fun.upd_same)
    apply simp
    apply simp
    apply (subst upd_fun_commute)
    apply (simp_all add: field_lvalue_same_conv' disj_ptr_span_ptr_neq eq_commute)
    done
qed

lemma partial_pointer_lenseI_fld:
  fixes get :: "'a::mem_type \<Rightarrow> 'b" and upd r w
  assumes 1: "lense get upd"
  assumes 2: "lense r w"
  shows "partial_pointer_lense
    (\<lambda>a b. upd (\<lambda>_. get a) b)
    (\<lambda>h p. upd (\<lambda>_. r h (PTR('b) &(p\<rightarrow>f))))
    (\<lambda>p x. w (upd_fun (PTR('b) &(p\<rightarrow>f)) (\<lambda>_. get x)))"
  by (rule partial_pointer_lenseI[OF 1 pointer_lense_of_lense_fld, OF 2])

lemma partial_pointer_lense_compose:
  assumes "partial_pointer_lense m1 r1 w1"
  assumes "partial_pointer_lense m2 r2 w2"
  assumes m[simp]: "\<And>a b c. m1 a (m2 b c) = m2 b (m1 a c)"
  assumes w[simp]: "\<And>p a q b h. p = q \<or> disjnt (ptr_span p) (ptr_span q) \<Longrightarrow>
    w1 p a (w2 q b h) = w2 q b (w1 p a h)"
  shows "partial_pointer_lense (\<lambda>a b. m1 a (m2 a b))
    (\<lambda>h p x. r1 h p (r2 h p x))
    (\<lambda>p x h. w1 p x (w2 p x h))"
proof -
  interpret A: partial_pointer_lense m1 r1 w1 by fact
  interpret B: partial_pointer_lense m2 r2 w2 by fact

  have [simp]: "m1 (m2 a b) c = m1 b c" for a b c
    by (metis A.idem A.left m)

  have r1_w2[simp]: "p = q \<or> disjnt (ptr_span p) (ptr_span q) \<Longrightarrow>
    r1 (w2 p x h) q y = r1 h q y" for p q h x y
    by (metis (no_types, lifting) A.r_w A.w_r disjnt_comm w)

  have r1_r2: "r1 h p (r2 h p x) = r2 h p (r1 h p x)" for h p x
    by (metis A.m_r B.m_r m)

  show ?thesis
    apply unfold_locales
    apply (simp_all add: A.w_w_disj B.w_w_disj disjnt_sym)
    apply (simp add: r1_r2)
    apply (simp flip: m)
    done
qed

lemma partial_pointer_lense_id:
  "partial_pointer_lense (\<lambda>a. id) (\<lambda>h p. id) (\<lambda>p x. id)"
  by (simp add: partial_pointer_lense_def partial_pointer_lense_axioms_def)

lemma partial_pointer_lense_fold:
  fixes rs :: "('h \<Rightarrow> 'a::c_type ptr \<Rightarrow> 'a \<Rightarrow> 'a) list"
  assumes "length ms = length rs" "length ms = length ws"
  assumes "list_all (\<lambda>(m, r, w). partial_pointer_lense m r w) (zip ms (zip rs ws))"
  assumes "\<forall>a b c. distinct_prop (\<lambda>m1 m2. m1 a (m2 b c) = m2 b (m1 a c)) ms"
  assumes "\<forall>p a q b h.
    distinct_prop (\<lambda>w1 w2. p = q \<or> disjnt (ptr_span p) (ptr_span q) \<longrightarrow>
      w1 p a (w2 q b h) = w2 q b (w1 p a h)) ws"
  shows "partial_pointer_lense (\<lambda>a b. fold (\<lambda>m. m a) ms b)
    (\<lambda>h p x. fold (\<lambda>r. r h p) rs x)
    (\<lambda>p x h. fold (\<lambda>w. w p x) ws h)"
  using assms
proof (induction ms arbitrary: ws rs)
  case (Cons m ms ws' rs')
  from Cons.prems(1,2) obtain r rs w ws where [simp]: "rs' = r # rs" "ws' = w # ws"
    by (cases ws'; cases rs'; auto)
  have ppl_ms:
    "partial_pointer_lense
      (\<lambda>a. fold (\<lambda>m. m a) ms)
      (\<lambda>h p. fold (\<lambda>r. r h p) rs)
      (\<lambda>p x. fold (\<lambda>w. w p x) ws)"
    using Cons.prems by (intro Cons.IH; simp)
  from Cons.prems(3) have ppl_m: "partial_pointer_lense m r w" by simp
  show ?case
    apply (simp, rule partial_pointer_lense_compose[OF ppl_ms ppl_m])
  proof -
    fix a b c
    from Cons.prems(4) have "list_all (\<lambda>m'. \<forall>a b c. m a (m' b c) = m' b (m a c)) ms"
      by (simp add: list_all_iff)
    then show "fold (\<lambda>m. m a) ms (m b c) = m b (fold (\<lambda>m. m a) ms c)"
    proof (induction ms arbitrary: c)
      case (Cons m' ms)
      then show ?case by simp metis
    qed simp
  next
    fix p q :: "'a ptr" and a b :: 'a and h :: 'h
    assume "p = q \<or> disjnt (ptr_span p) (ptr_span q)"
    then have "q = p \<or> disjnt (ptr_span q) (ptr_span p)"
      by (simp add: eq_commute disjnt_comm)
    with Cons.prems(5) have "list_all (\<lambda>w'. \<forall>b a h. w q a (w' p b h) = w' p b (w q a h)) ws"
      by (auto simp add: list_all_iff)
    then show "fold (\<lambda>w. w p a) ws (w q b h) = w q b (fold (\<lambda>w. w p a) ws h)"
    proof (induction ws arbitrary: a b h)
      case (Cons w' ws)
      then show ?case
        by simp metis
    qed simp
  qed
qed (simp add: partial_pointer_lense_id)

lemma pointer_lense_of_partial_pointer_lense:
  assumes "partial_pointer_lense m r w"
  assumes [simp]: "\<And>a b. m a b = a"
  shows "pointer_lense (\<lambda>h p. r h p x) (\<lambda>p f h. w p (f (r h p x)) h)"
proof -
  interpret partial_pointer_lense m r w by fact
  show ?thesis
    by unfold_locales (simp_all add: w_w_disj disjnt_def Int_commute)
qed

lemma pointer_lense_of_partials:
  fixes rs :: "('h \<Rightarrow> 'a::mem_type ptr \<Rightarrow> 'a \<Rightarrow> 'a) list"
  assumes *:
    "length ms = length rs" "length ms = length ws"
    "list_all (\<lambda>(m, r, w). partial_pointer_lense m r w) (zip ms (zip rs ws))"
    and **:
    "\<And>a b c. distinct_prop (\<lambda>m1 m2. m1 a (m2 b c) = m2 b (m1 a c)) ms"
    "\<And>p a q b h. distinct_prop (\<lambda>w1 w2. p = q \<or> disjnt (ptr_span p) (ptr_span q) \<longrightarrow>
      w1 p a (w2 q b h) = w2 q b (w1 p a h)) ws"
  assumes ms: "\<And>a b. fold (\<lambda>m. m a) ms b = a"
  assumes R: "\<And>h p. R h p = fold (\<lambda>r. r h p) rs x"
  assumes W: "\<And>p f h. W p f h = fold (\<lambda>w. w p (f (R h p))) ws h"
  shows "pointer_lense R W"
  unfolding R[abs_def] W[abs_def]
  apply (rule pointer_lense_of_partial_pointer_lense[OF partial_pointer_lense_fold, OF *])
  subgoal using **(1) by simp
  subgoal using **(2) by simp
  subgoal by (rule ms)
  done

end
