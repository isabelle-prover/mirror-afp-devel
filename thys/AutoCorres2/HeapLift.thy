(*
 * Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
 * Copyright (c) 2022 Apple Inc. All rights reserved.
 *
 * SPDX-License-Identifier: BSD-2-Clause
 *)


theory HeapLift
  imports
  In_Out_Parameters
  Split_Heap
  AbstractArrays
begin

section "Refinement Lemmas"

lemma ucast_ucast_id:
  "LENGTH('a) \<le> LENGTH('b) \<Longrightarrow> ucast (ucast (x::'a::len word)::'b::len word) = x"
  by (auto intro: ucast_up_ucast_id simp: is_up_def source_size_def target_size_def word_size)

lemma lense_ucast_signed:
  "lense (unsigned :: 'a::len word \<Rightarrow> 'a signed word) (\<lambda>v x. unsigned (v (unsigned x)))"
  by (rule lenseI_equiv) (simp_all add: ucast_ucast_id)

lemma pointer_lense_ucast_signed:
  fixes r :: "'h \<Rightarrow> 'a::len8 word ptr \<Rightarrow> 'a word"
  assumes "pointer_lense r w"
  shows "pointer_lense
    (\<lambda>h p. UCAST('a \<rightarrow> 'a signed) (r h (PTR_COERCE('a signed word \<rightarrow> 'a word) p)))
    (\<lambda>p m. w (PTR_COERCE('a signed word \<rightarrow> 'a word) p)
      (\<lambda>w. UCAST('a signed \<rightarrow> 'a) (m (UCAST('a \<rightarrow> 'a signed) w))))"
proof -
  interpret pointer_lense r w by fact
  note scast_ucast_norm[simp del]
  note ucast_ucast_id[simp]
  show ?thesis
    apply unfold_locales
    apply (simp add: read_write_same)
    apply (simp add: write_same)
    apply (simp add: comp_def)
    apply (simp add: write_other_commute typ_uinfo_t_signed_word_word_conv
                flip: size_of_tag typ_uinfo_size)
    done
qed

lemma (in xmem_type) length_to_bytes:
  "length (to_bytes (v::'a) bs) = size_of TYPE('a)"
  by (simp add: to_bytes_def lense.access_result_size)

lemma (in xmem_type) heap_update_padding_eq:
  "length bs = size_of TYPE('a) \<Longrightarrow>
    heap_update_padding p v bs h = heap_update p v (heap_update_list (ptr_val p) bs h)"
  using u.max_size
  by (simp add: heap_update_padding_def heap_update_def size_of_def
      heap_list_heap_update_list_id heap_update_list_overwrite)

lemma (in xmem_type) heap_update_padding_eq':
  "length bs = size_of TYPE('a) \<Longrightarrow>
    heap_update_padding p v bs = heap_update p v \<circ> heap_update_list (ptr_val p) bs"
  by (simp add: fun_eq_iff heap_update_padding_eq)

lemma split_disj_asm: "P (x \<or> y) = (\<not> (x \<and> \<not> P x \<or> \<not> x \<and> \<not> P y))"
  by (smt (verit, best))

lemma comp_commute_of_fold:
  assumes x: "x = fold f xs"
  assumes xs: "list_all (\<lambda>x. f x o a = a o f x) xs"
  shows "x o a = a o x"
  unfolding x using xs by (induction xs) (simp_all add: fun_eq_iff)

definition padding_closed_under_all_fields where
  "padding_closed_under_all_fields t \<longleftrightarrow>
    (\<forall>s f n bs bs'. field_lookup t f 0 = Some (s, n) \<longrightarrow>
      eq_upto_padding t bs bs' \<longrightarrow> eq_upto_padding s (take (size_td s) (drop n bs)) (take (size_td s) (drop n bs')))"

lemma padding_closed_under_all_fields_typ_uinfo_t:
  "padding_closed_under_all_fields (typ_uinfo_t TYPE('a::xmem_type))"
  unfolding padding_closed_under_all_fields_def
proof safe
  fix s f n bs bs' assume s_n: "field_lookup (typ_uinfo_t TYPE('a)) f 0 = Some (s, n)"
    and bs_bs': "eq_upto_padding (typ_uinfo_t TYPE('a)) bs bs'"
  then have len: "length bs = size_of TYPE('a)" "length bs' = size_of TYPE('a) "
    by (auto simp: eq_upto_padding_def size_of_def)

  from s_n[THEN field_lookup_uinfo_Some_rev] obtain k where
    k: "field_lookup (typ_info_t TYPE('a)) f 0 = Some (k, n)" and k_s: "export_uinfo k = s"
    by auto
  have [simp]: "size_td k = size_td s" by (simp flip: k_s)
  from xmem_type_field_lookup_eq_upto_padding_focus[OF k len bs_bs']
  show "eq_upto_padding s (take (size_td s) (drop n bs)) (take (size_td s) (drop n bs'))"
    unfolding k_s by simp
qed

lemma (in open_types) plift_heap_update_list_eq_upto_padding:
  assumes t: "mem_type_u t" and t': "padding_closed_under_all_fields t"
  assumes a: "ptr_valid_u t (hrs_htd h) a"
  assumes bs_bs': "eq_upto_padding t bs bs'"
  shows "plift (hrs_mem_update (heap_update_list a bs) h) =
    (plift (hrs_mem_update (heap_update_list a bs') h)::'a::xmem_type ptr \<Rightarrow> 'a option)"
  apply (rule plift_eq_plift, simp_all add: h_val_def hrs_mem_update)
proof -
  from bs_bs' have [simp]: "length bs = size_td t" "length bs' = size_td t"
    by (simp_all add: eq_upto_padding_def)
  have [arith]: "size_td t < addr_card"
    using mem_type_u.max_size[OF t] by simp
  have a_bnd: "size_of TYPE('a) \<le> addr_card"
    using max_size[where 'a='a] by arith
  let ?A = "typ_uinfo_t TYPE('a)"

  fix p :: "'a ptr" assume p: "ptr_valid (hrs_htd h) p"
  from ptr_valid_u_cases_weak[OF t a this[unfolded ptr_valid_def]]
  show "from_bytes (heap_list (heap_update_list a bs (hrs_mem h)) (size_of TYPE('a)) (ptr_val p)) =
    (from_bytes (heap_list (heap_update_list a bs' (hrs_mem h)) (size_of TYPE('a)) (ptr_val p))::'a)"
  proof (elim disjE exE conjE)
    assume "disjnt {a..+size_td t} {ptr_val p..+size_td (typ_uinfo_t TYPE('a))}"
    with bs_bs' show ?thesis
      unfolding heap_upd_list_def
      by (subst (1 2) heap_list_update_disjoint_same; simp add: size_of_def disjnt_def)
  next
    fix path assume path: "addressable_field t path ?A" and
      p_eq: "ptr_val p = a + word_of_nat (field_offset_untyped t path)"
    let ?n = "field_offset_untyped t path"
    have sz: "size_of TYPE('a) + ?n \<le> size_td t"
      using field_lookup_offset_size'[OF addressable_fieldD_field_lookup'[OF path]]
      by (simp add: size_of_def)
    let ?s = "typ_uinfo_t TYPE('a)"
    from addressable_fieldD_field_lookup'[OF path] t' bs_bs' have *:
      "eq_upto_padding ?s (take (size_td ?s) (drop ?n bs)) (take (size_td ?s) (drop ?n bs'))"
      unfolding padding_closed_under_all_fields_def
      by (auto simp flip: typ_uinfo_size)

    show ?thesis unfolding p_eq
      using eq_upto_padding_from_bytes_eq[OF *] sz
      apply (subst (1 2) heap_list_update_list)
      apply (simp_all add: size_of_def)
      done
  next
    fix path assume path: "addressable_field ?A path t"
      and p_eq: "a = ptr_val p + word_of_nat (field_offset_untyped ?A path)"
    let ?n = "field_offset_untyped ?A path"
    have sz: "size_td t + ?n \<le> size_of TYPE('a)"
      using field_lookup_offset_size'[OF addressable_fieldD_field_lookup'[OF path]]
      by (simp add: size_of_def)
    from field_lookup_uinfo_Some_rev[OF addressable_fieldD_field_lookup'[OF path]] obtain k
      where k: "field_lookup (typ_info_t TYPE('a)) path 0 = Some (k, ?n)"
        and eq_t: "export_uinfo k = t" by blast
    then have [simp]: "size_td k = size_td t"
      by (simp flip: eq_t)

    have *: "eq_upto_padding (typ_uinfo_t TYPE('a))
      (super_update_bs bs (heap_list (hrs_mem h) (size_of TYPE('a)) (ptr_val p)) ?n)
      (super_update_bs bs' (heap_list (hrs_mem h) (size_of TYPE('a)) (ptr_val p)) ?n)"
      by (subst xmem_type_field_lookup_eq_upto_padding_super_update_bs[OF k(1)])
         (simp_all add: eq_t bs_bs')

    note 1 = c_guard_no_wrap'[OF ptr_valid_c_guard, OF p]
    show ?thesis unfolding p_eq using sz
      apply (subst (1 2) heap_update_list_super_update_bs_heap_list[OF 1])
      apply (simp_all add: heap_list_heap_update_list_id[OF a_bnd])
      apply (intro eq_upto_padding_from_bytes_eq[OF *])
      done
  qed
qed

lemma (in open_types) read_dedicated_heap_heap_update_list_eq_upto_padding[simp]:
  assumes t: "mem_type_u t" and t': "padding_closed_under_all_fields t"
  assumes a: "ptr_valid_u t (hrs_htd h) a"
  assumes bs_bs': "eq_upto_padding t bs bs'"
  shows "read_dedicated_heap (hrs_mem_update (heap_update_list a bs) h) =
    (read_dedicated_heap (hrs_mem_update (heap_update_list a bs') h)::'a::xmem_type ptr \<Rightarrow> 'a) \<longleftrightarrow> True"
  by (simp add: plift_heap_update_list_eq_upto_padding[OF assms] read_dedicated_heap_def fun_eq_iff)

definition "L2Tcorres st A C = corresXF st (\<lambda>r _. r) (\<lambda>r _. r) (\<lambda>_. True) A C"

lemma L2Tcorres_id:
  "L2Tcorres id C C"
  by (metis L2Tcorres_def corresXF_id)

lemma L2Tcorres_fail:
  "L2Tcorres st L2_fail X"
  apply (clarsimp simp: L2Tcorres_def L2_defs)
  apply (rule corresXF_fail)
  done

lemma admissible_nondet_ord_L2Tcorres [corres_admissible]:
  "ccpo.admissible Inf (\<ge>) (\<lambda>A. L2Tcorres st A C)"
  unfolding L2Tcorres_def
  apply (rule admissible_nondet_ord_corresXF)
  done

lemma L2Tcorres_top [corres_top]: "L2Tcorres st \<top> C"
  by (auto simp add: L2Tcorres_def corresXF_def)

(* Abstraction predicates for inner expressions. *)
definition "abs_guard    st   A C \<equiv> \<forall>s. A (st s) \<longrightarrow> C s"
definition "abs_expr     st P A C \<equiv> \<forall>s. P (st s) \<longrightarrow> C s = A (st s)"
definition "abs_modifies st P A C \<equiv> \<forall>s. P (st s) \<longrightarrow> st (C s) = A (st s)"

(* Predicates to enable some transformations on the input expressions
   (namely, rewriting uses of field_lvalue) that are best done
   as a preprocessing stage (st = id).
   The corresTA rules should ensure that these are used to rewrite
   any inner expressions before handing off to the predicates above. *)
definition "struct_rewrite_guard      A C \<equiv> \<forall>s. A s \<longrightarrow> C s"
definition "struct_rewrite_expr     P A C \<equiv> \<forall>s. P s \<longrightarrow> C s = A s"
definition "struct_rewrite_modifies P A C \<equiv> \<forall>s. P s \<longrightarrow> C s = A s"


(* Standard heap abstraction rules. *)
named_theorems heap_abs
(* Rules that require first-order matching. *)
named_theorems heap_abs_fo

named_theorems derived_heap_defs and
 valid_array_defs and
 heap_upd_cong and
 valid_same_typ_descs

lemma deepen_heap_upd_cong: "f = f' \<Longrightarrow> upd f s = upd f' s"
  by simp

lemma deepen_heap_map_cong: "f = f' \<Longrightarrow> upd f p s = upd f' p s"
  by simp


(* fun_app2 is like fun_app, but it skips an abstraction.
 * We use this for terms like "\<lambda>s a. Array.update a k (f s)".
 * fixme: ideally, the first order conversion code can skip abstractions. *)

lemma abs_expr_fun_app2 [heap_abs_fo]:
  "\<lbrakk> abs_expr st P f f';
     abs_expr st Q g g' \<rbrakk> \<Longrightarrow>
   abs_expr st (\<lambda>s. P s \<and> Q s) (\<lambda>s a. f s a (g s a)) (\<lambda>s a. f' s a $ g' s a)"
  by (simp add: abs_expr_def)

lemma abs_expr_fun_app [heap_abs_fo]:
  "\<lbrakk> abs_expr st Y x x'; abs_expr st X f f' \<rbrakk> \<Longrightarrow>
      abs_expr st (\<lambda>s. X s \<and> Y s) (\<lambda>s. f s (x s)) (\<lambda>s. f' s $ x' s)"
  apply (clarsimp simp: abs_expr_def)
  done

lemma abs_expr_Pair [heap_abs]: "
abs_expr st X f1 f1' \<Longrightarrow> abs_expr st Y f2 f2' \<Longrightarrow>
abs_expr st  (\<lambda>s. X s \<and> Y s)  (\<lambda>s. (f1 s, f2 s)) (\<lambda>s. (f1' s, f2' s))"
  apply (clarsimp simp: abs_expr_def)
  done

lemma abs_expr_constant [heap_abs]:
  "abs_expr st (\<lambda>_. True) (\<lambda>s. a) (\<lambda>s. a)"
  apply (clarsimp simp: abs_expr_def)
  done

lemma abs_guard_expr [heap_abs]:
  "abs_expr st P a' a \<Longrightarrow> abs_guard st (\<lambda>s. P s \<and> a' s) a"
  by (simp add: abs_expr_def abs_guard_def)

lemma abs_guard_constant [heap_abs]:
  "abs_guard st (\<lambda>_. P) (\<lambda>_. P)"
  by (clarsimp simp: abs_guard_def)

lemma abs_guard_conj [heap_abs]:
  "\<lbrakk> abs_guard st G G'; abs_guard st H H' \<rbrakk>
      \<Longrightarrow> abs_guard st (\<lambda>s. G s \<and> H s) (\<lambda>s. G' s \<and> H' s)"
  by (clarsimp simp: abs_guard_def)


lemma L2Tcorres_modify [heap_abs]:
    "\<lbrakk> struct_rewrite_modifies P b c; abs_guard st P' P;
       abs_modifies st Q a b \<rbrakk> \<Longrightarrow>
     L2Tcorres st (L2_seq (L2_guard (\<lambda>s. P' s \<and> Q s)) (\<lambda>_. (L2_modify a))) (L2_modify c)"
  apply (auto intro!: refines_bind_guard_right refines_modify  
      simp: corresXF_refines_conv 
      L2Tcorres_def L2_defs abs_modifies_def abs_guard_def struct_rewrite_modifies_def struct_rewrite_guard_def)
  done

lemma L2Tcorres_gets [heap_abs]:
    "\<lbrakk> struct_rewrite_expr P b c; abs_guard st P' P;
       abs_expr st Q a b \<rbrakk> \<Longrightarrow>
     L2Tcorres st (L2_seq (L2_guard (\<lambda>s. P' s \<and> Q s)) (\<lambda>_. L2_gets a n)) (L2_gets c n)"
  apply (auto intro!: refines_bind_guard_right refines_gets   
      simp: corresXF_refines_conv L2Tcorres_def L2_defs abs_expr_def abs_guard_def struct_rewrite_expr_def struct_rewrite_guard_def)
  done

lemma L2Tcorres_gets_const [heap_abs]:
    "L2Tcorres st (L2_gets (\<lambda>_. a) n) (L2_gets (\<lambda>_. a) n)"
  apply (simp add: corresXF_refines_conv refines_gets L2Tcorres_def L2_defs)
  done

lemma L2Tcorres_guard [heap_abs]:
    "\<lbrakk> struct_rewrite_guard b c; abs_guard st a b \<rbrakk> \<Longrightarrow>
     L2Tcorres st (L2_guard a) (L2_guard c)"
  apply (simp add: corresXF_def L2Tcorres_def L2_defs abs_guard_def struct_rewrite_guard_def)
  done

lemma L2Tcorres_while [heap_abs]:
  assumes body_corres [simplified THIN_def,rule_format]:
    "PROP THIN (\<And>x. L2Tcorres st (B' x) (B x))"
  and cond_rewrite [simplified THIN_def,rule_format]:
    "PROP THIN (\<And>r. struct_rewrite_expr (G r) (C' r) (C r))"
  and guard_abs[simplified THIN_def,rule_format]:
    "PROP THIN (\<And>r. abs_guard st (G' r) (G r))"
  and guard_impl_cond[simplified THIN_def,rule_format]:
    "PROP THIN (\<And>r. abs_expr st (H r) (C'' r) (C' r))"
  shows "L2Tcorres st (L2_guarded_while (\<lambda>i s. G' i s \<and> H i s) C'' B' i n) (L2_while C B i n)"
proof -

  have cond_match: "\<And>r s. G' r (st s) \<and> H r (st s) \<Longrightarrow> C'' r (st s) = C r s"
    using cond_rewrite guard_abs guard_impl_cond
    by (clarsimp simp: abs_expr_def abs_guard_def struct_rewrite_expr_def)

  have "corresXF st (\<lambda>r _. r) (\<lambda>r _. r) (\<lambda>_. True)
           (do { _ \<leftarrow> guard (\<lambda>s. G' i s \<and> H i s);
                     whileLoop C''
                       (\<lambda>i. do { r \<leftarrow> B' i;
                                _ \<leftarrow> guard (\<lambda>s. G' r s \<and> H r s);
                                return r
                       }) i
           })
     (whileLoop C B i)"
    apply (rule corresXF_guard_imp)
     apply (rule corresXF_guarded_while [where P="\<lambda>_ _. True" and P'="\<lambda>_ _. True"])
         apply (clarsimp cong: corresXF_cong)
         apply (rule corresXF_guard_imp)
          apply (rule body_corres [unfolded L2Tcorres_def])
         apply simp
        apply (clarsimp simp: cond_match)
       apply clarsimp
       apply (simp add: runs_to_partial_def_old split: xval_splits)
      apply simp
     apply simp
    apply simp
    done

  thus ?thesis
    by (clarsimp simp: L2Tcorres_def L2_defs gets_return top_fun_def)
qed


named_theorems abs_spec

definition "abs_spec st P (A :: ('a \<times> 'a) set) (C :: ('c \<times> 'c) set)
           \<equiv> (\<forall>s t. P (st s) \<longrightarrow> (((s, t) \<in> C) \<longrightarrow> ((st s, st t) \<in> A)))
                              \<and> (\<forall>s. P (st s) \<longrightarrow> (\<exists>x. (st s, x) \<in> A) \<longrightarrow> (\<exists>x. (s, x) \<in> C))"

lemma L2Tcorres_spec [heap_abs]:
  "\<lbrakk> abs_spec st P A C \<rbrakk>
     \<Longrightarrow> L2Tcorres st (L2_seq (L2_guard P) (\<lambda>_. (L2_spec A))) (L2_spec C)"
  unfolding corresXF_refines_conv L2Tcorres_def L2_defs
  apply (clarsimp simp add: abs_spec_def)
  apply (intro refines_bind_guard_right refines_bind_bind_exn_wp refines_state_select)
   apply (force intro!: refines_select simp add: abs_spec_def split: xval_splits)
  apply blast
  done


definition "abs_assume st P (A :: 'a \<Rightarrow> ('b \<times> 'a) set) (C :: 'c \<Rightarrow> ('b \<times> 'c) set)
  \<equiv> (\<forall>s t r. P (st s) \<longrightarrow> (((r, t) \<in> C s) \<longrightarrow> ((r, st t) \<in> A (st s))))"

(* FIXME: replace refines_assume_result_and_state in spec monad *)
lemma refines_assume_result_and_state': 
  "refines (assume_result_and_state P) (assume_result_and_state Q) s t R"
  if "sim_set (\<lambda>(v, s) (w, t). R (Result v, s) (Result w, t))  (P s) (Q t)"
  using that
  by (force simp: refines_def_old  sim_set_def rel_set_def  case_prod_unfold)


lemma L2Tcorres_assume [heap_abs]:
  "\<lbrakk> abs_assume st P A C \<rbrakk>
     \<Longrightarrow> L2Tcorres st (L2_seq (L2_guard P) (\<lambda>_. (L2_assume A))) (L2_assume C)"
  unfolding corresXF_refines_conv L2Tcorres_def L2_defs
  apply (clarsimp simp add: abs_assume_def) thm  refines_mono [OF _ refines_assume_result_and_state]
  apply (intro refines_bind_guard_right refines_bind_bind_exn_wp refines_assume_result_and_state' )
  apply (auto simp add: sim_set_def)
  done

lemma abs_spec_constant [heap_abs]:
  "abs_spec st (\<lambda>_. True) {(a, b). C} {(a, b). C}"
  apply (clarsimp simp: abs_spec_def)
  done

lemma L2Tcorres_condition [heap_abs]:
  "\<lbrakk>PROP THIN (Trueprop (L2Tcorres st L L'));
    PROP THIN (Trueprop (L2Tcorres st R R'));
    PROP THIN (Trueprop (struct_rewrite_expr P C' C));
    PROP THIN (Trueprop (abs_guard st P' P));
    PROP THIN (Trueprop (abs_expr st Q C'' C'))\<rbrakk> \<Longrightarrow>
   L2Tcorres st (L2_seq (L2_guard (\<lambda>s. P' s \<and> Q s)) (\<lambda>_. L2_condition C'' L R)) (L2_condition C L' R')"
  unfolding THIN_def L2_defs L2Tcorres_def corresXF_refines_conv
  apply clarsimp
  apply (intro refines_bind_guard_right refines_condition)
  apply (auto simp add: abs_expr_def abs_guard_def struct_rewrite_expr_def struct_rewrite_guard_def)
  done

lemma L2Tcorres_seq [heap_abs]:
  "\<lbrakk>PROP THIN (Trueprop (L2Tcorres st L' L)); PROP THIN (\<And>r. L2Tcorres st (R' r) (R r)) \<rbrakk>
      \<Longrightarrow> L2Tcorres st (L2_seq L' R') (L2_seq L R)"
  unfolding THIN_def L2_defs L2Tcorres_def corresXF_refines_conv
  apply clarsimp
  apply (intro refines_bind_bind_exn_wp)
  subgoal for t
    apply (erule_tac x=t in allE)
    apply (rule refines_weaken)
     apply assumption
    apply (auto split: xval_splits)
    done
  done


lemma L2Tcorres_guarded_simple [heap_abs]:
  assumes b_c: "struct_rewrite_guard b c"
  assumes a_b: "abs_guard st a b"
  assumes f_g: "\<And>s s'. c s \<Longrightarrow> s' = st s \<Longrightarrow> L2Tcorres st f g"
  shows "L2Tcorres st (L2_guarded a f) (L2_guarded c g)"
  unfolding L2_guarded_def L2_defs L2Tcorres_def corresXF_refines_conv
  using b_c a_b f_g
  by (fastforce simp add: refines_def_old L2Tcorres_def corresXF_refines_conv reaches_bind succeeds_bind 
      struct_rewrite_guard_def abs_guard_def abs_expr_def split: xval_splits)

lemma L2Tcorres_catch [heap_abs]:
    "\<lbrakk>PROP THIN (Trueprop (L2Tcorres st L L'));
      PROP THIN (\<And>r. L2Tcorres st (R r) (R' r))
     \<rbrakk> \<Longrightarrow> L2Tcorres st (L2_catch L R) (L2_catch L' R')"
  unfolding THIN_def
  apply (clarsimp simp: L2Tcorres_def L2_defs)
  apply (rule corresXF_guard_imp)
   apply (erule corresXF_except [where P'="\<lambda>x y s. x = y" and Q="\<lambda>_. True"])
     apply (simp add: corresXF_refines_conv)
    apply (simp add: runs_to_partial_def_old split: xval_splits)
   apply simp
  apply simp
  done

lemma corresXF_return_same:
  "corresXF st (\<lambda>r _. r) (\<lambda>r _. r) (\<lambda>_. True) (return e) (return e)"
  by (clarsimp simp add: corresXF_def)

lemma corresXF_yield_same:
  "corresXF st (\<lambda>r _. r) (\<lambda>r _. r) (\<lambda>_. True) (yield e) (yield e)"
 by (auto simp add: corresXF_refines_conv intro!: refines_yield split: xval_splits)

lemma L2_try_catch: "L2_try L = L2_catch L (\<lambda>e. yield (to_xval e))"
  unfolding L2_defs
  apply (rule spec_monad_eqI)
  apply (clarsimp simp add: runs_to_iff)
  apply (auto simp add: runs_to_def_old unnest_exn_def to_xval_def split: xval_splits sum.splits )
  done

lemma L2Tcorres_try [heap_abs]:
    "\<lbrakk> L2Tcorres st L L'\<rbrakk> \<Longrightarrow> L2Tcorres st (L2_try L) (L2_try L')"
  apply (simp add: L2_try_catch)
  apply (erule L2Tcorres_catch [simplified THIN_def])
  apply (unfold L2Tcorres_def top_fun_def top_bool_def)
  apply (rule corresXF_yield_same)
  done

lemma L2Tcorres_unknown [heap_abs]:
  "L2Tcorres st (L2_unknown ns) (L2_unknown ns)"
  apply (clarsimp simp: L2_unknown_def)
  apply (clarsimp simp: L2Tcorres_def)
  apply (auto intro!: corresXF_select_select)
  done

lemma L2Tcorres_throw [heap_abs]:
  "L2Tcorres st (L2_throw x n) (L2_throw x n)"
  apply (clarsimp simp: L2Tcorres_def L2_defs)
  apply (rule corresXF_throw)
  apply simp
  done

lemma L2Tcorres_split [heap_abs]:
  "\<lbrakk> \<And>x y. L2Tcorres st (P x y) (P' x y) \<rbrakk> \<Longrightarrow>
    L2Tcorres st (case a of (x, y) \<Rightarrow> P x y) (case a of (x, y) \<Rightarrow> P' x y)"
  apply (clarsimp simp: split_def)
  done

lemma L2Tcorres_seq_unused_result [heap_abs]:
  "\<lbrakk>PROP THIN (Trueprop (L2Tcorres st L L')); PROP THIN (Trueprop (L2Tcorres st R R')) \<rbrakk>
  \<Longrightarrow> L2Tcorres st (L2_seq L (\<lambda>_. R)) (L2_seq L' (\<lambda>_. R'))"
  apply (rule L2Tcorres_seq, auto)
  done

lemma abs_expr_split [heap_abs]:
  "\<lbrakk> \<And>a b. abs_expr st (P a b) (A a b) (C a b) \<rbrakk>
       \<Longrightarrow> abs_expr st (case r of (a, b) \<Rightarrow> P a b)
            (case r of (a, b) \<Rightarrow> A a b) (case r of (a, b) \<Rightarrow> C a b)"
  apply (auto simp: split_def)
  done

lemma abs_guard_split [heap_abs]:
  "\<lbrakk> \<And>a b. abs_guard st (A a b) (C a b) \<rbrakk>
       \<Longrightarrow> abs_guard st (case r of (a, b) \<Rightarrow> A a b) (case r of (a, b) \<Rightarrow> C a b)"
  apply (auto simp: split_def)
  done

lemma L2Tcorres_abstract_fail [heap_abs]:
  "L2Tcorres st L2_fail L2_fail"
  apply (clarsimp simp: L2Tcorres_def L2_defs)
  apply (rule corresXF_fail)
  done

lemma abs_expr_id [heap_abs]:
  "abs_expr id (\<lambda>_. True) A A"
  apply (clarsimp simp: abs_expr_def)
  done

lemma abs_expr_lambda_null [heap_abs]:
  "abs_expr st P A C \<Longrightarrow> abs_expr st P (\<lambda>s r. A s) (\<lambda>s r. C s)"
  apply (clarsimp simp: abs_expr_def)
  done

lemma abs_modify_id [heap_abs]:
  "abs_modifies id (\<lambda>_. True) A A"
  apply (clarsimp simp: abs_modifies_def)
  done

lemma corresXF_exec_concrete [intro?]:
  "corresXF id ret_xf ex_xf P A C \<Longrightarrow> corresXF st ret_xf ex_xf P (exec_concrete st A) C"
  by (force simp add: corresXF_refines_conv refines_def_old reaches_exec_concrete succeeds_exec_concrete_iff split: xval_splits)

lemma L2Tcorres_exec_concrete [heap_abs]:
  "L2Tcorres id A C \<Longrightarrow> L2Tcorres st (exec_concrete st (L2_call A emb ns)) (L2_call C emb ns)"
  apply (clarsimp simp: L2Tcorres_def L2_call_def map_exn_catch_conv)
  apply (rule corresXF_exec_concrete)
  apply (rule CorresXF.corresXF_except  [ where P' = "\<lambda>x y s. x = y"])
     apply assumption
  subgoal 
    by (auto simp add: corresXF_refines_conv)
  subgoal
    by (auto simp add: runs_to_partial_def_old split: xval_splits)
  subgoal by simp
  done

lemma L2Tcorres_exec_concrete_simpl [heap_abs]:
  "L2Tcorres id A C \<Longrightarrow> L2Tcorres st (exec_concrete st (L2_call_L1 arg_xf gs ret_xf A)) (L2_call_L1 arg_xf gs ret_xf C)"
  apply (clarsimp simp: L2Tcorres_def L2_call_L1_def)
  apply (rule corresXF_exec_concrete)
  apply (clarsimp simp add: corresXF_refines_conv)
  apply (rule refines_bind_bind_exn_wp)
  apply (clarsimp split: xval_splits)
  apply (rule refines_get_state)
  apply (clarsimp split: xval_splits)
  apply (rule refines_bind_bind_exn_wp)
  apply (clarsimp split: xval_splits)
  apply (rule refines_select)
  apply (clarsimp split: xval_splits)
  subgoal for x
    apply (rule exI[where x=x])
    apply (erule_tac x=x in allE)
    apply (clarsimp)
    apply (rule refines_run_bind)
    apply (clarsimp split: exception_or_result_splits)
    apply (erule refines_weaken)
    apply (clarsimp split: xval_splits)
    apply (rule refines_bind_bind_exn_wp)
    apply (clarsimp split: xval_splits)
    apply (rule refines_set_state)
    apply (clarsimp split: xval_splits)
    done
  done

lemma corresXF_exec_abstract [intro?]:
  "corresXF st ret_xf ex_xf P A C \<Longrightarrow> corresXF id ret_xf ex_xf P (exec_abstract st A) C"
  by (force simp: corresXF_refines_conv refines_def_old reaches_exec_abstract split: xval_splits)

lemma L2Tcorres_exec_abstract [heap_abs]:
    "L2Tcorres st A C \<Longrightarrow> L2Tcorres id (exec_abstract st (L2_call A emb ns)) (L2_call C emb ns)"
  apply (clarsimp simp: L2_call_def map_exn_catch_conv L2Tcorres_def)
  apply (rule corresXF_exec_abstract)
  apply (rule CorresXF.corresXF_except  [ where P' = "\<lambda>x y s. x = y"])
     apply assumption
    subgoal by (auto simp add: corresXF_refines_conv)
    subgoal by (auto simp add: runs_to_partial_def_old split: xval_splits)
    subgoal by simp  
    done

lemma L2Tcorres_call [heap_abs]:
  "L2Tcorres st A C \<Longrightarrow> L2Tcorres st (L2_call A emb ns) (L2_call C emb ns)"
  unfolding L2Tcorres_def L2_call_def map_exn_catch_conv
  apply (rule CorresXF.corresXF_except  [ where P' = "\<lambda>x y s. x = y"])
    apply assumption
    subgoal by (auto simp add: corresXF_refines_conv)
    subgoal by (auto simp add: runs_to_partial_def_old split: xval_splits)
    subgoal by simp  
    done


named_theorems
valid_implies_c_guard and
read_commutes and
write_commutes  and
field_write_commutes and
write_valid_preservation and
lift_heap_update_padding_heap_update_conv

(*
 * Assert the given abstracted heap (accessed using "getter" and "setter") for type
 * "'a" is a valid abstraction w.r.t. the given state translation functions.
 *)



locale valid_implies_cguard =
  fixes st::"'s \<Rightarrow> 't"
  fixes v::"'t \<Rightarrow> 'a::c_type ptr \<Rightarrow> bool"
  assumes valid_implies_c_guard[valid_implies_c_guard]: "v (st s) p \<Longrightarrow> c_guard p"

locale read_simulation =
  fixes st ::"'s \<Rightarrow> 't"
  fixes v ::"'t \<Rightarrow> 'a::c_type ptr \<Rightarrow> bool"
  fixes r :: "'t \<Rightarrow> 'a ptr \<Rightarrow> 'a"
  fixes t_hrs::"'s \<Rightarrow> heap_raw_state"
  assumes read_commutes[read_commutes]: "v (st s) p \<Longrightarrow>
              r (st s) p = h_val (hrs_mem (t_hrs s)) p"

locale write_simulation =
  heap_raw_state t_hrs t_hrs_upd
  for
    t_hrs :: "('s \<Rightarrow> heap_raw_state)" and
    t_hrs_upd::"(heap_raw_state \<Rightarrow> heap_raw_state) \<Rightarrow> 's \<Rightarrow> 's" +
  fixes st ::"'s \<Rightarrow> 't"
  fixes v ::"'t \<Rightarrow> 'a::mem_type ptr \<Rightarrow> bool"
  fixes w :: "'a ptr \<Rightarrow> ('a \<Rightarrow> 'a)  \<Rightarrow> 't \<Rightarrow> 't"

  assumes write_padding_commutes[write_commutes]: "v (st s) p \<Longrightarrow> length bs = size_of TYPE('a) \<Longrightarrow>
           st (t_hrs_upd (hrs_mem_update (heap_update_padding p x bs)) s) =
                           w p (\<lambda>_. x)  (st s)"

begin
lemma write_commutes[write_commutes]:
  assumes valid: "v (st s) p"
  shows "st (t_hrs_upd (hrs_mem_update (heap_update p x)) s) =
                           w p (\<lambda>_. x) (st s)"
proof -
  have eq: "hrs_mem_update (heap_update p x) =
        hrs_mem_update (\<lambda>h. heap_update_padding p x (heap_list h (size_of TYPE('a)) (ptr_val p)) h)"
    using heap_update_heap_update_padding_conv
    by metis

  show ?thesis
    apply (simp only: eq)
    apply (subst write_padding_commutes [symmetric,  where bs="heap_list (hrs_mem (t_hrs s)) (size_of TYPE('a)) (ptr_val p)"])
      apply (rule valid)
     apply clarsimp
    by (metis (no_types, lifting) heap.upd_cong)
qed

lemma lift_heap_update_padding_heap_update_conv[lift_heap_update_padding_heap_update_conv]:
  "v (st s) p \<Longrightarrow> length bs = size_of TYPE('a) \<Longrightarrow>
           st (t_hrs_upd (hrs_mem_update (heap_update_padding p x bs)) s) =
           st (t_hrs_upd (hrs_mem_update (heap_update p x)) s)"
  using write_padding_commutes write_commutes by auto

lemma write_commutes_atomic: "\<forall>s p x. v (st s) p \<longrightarrow>
   st (t_hrs_upd (hrs_mem_update (heap_update p x)) s) =
                           w p (\<lambda>_. x) (st s)"
  using  write_commutes by blast

end


locale write_preserves_valid =
  fixes v ::"'t \<Rightarrow> 'a::c_type ptr \<Rightarrow> bool"
  fixes w :: "'a ptr \<Rightarrow> ('b \<Rightarrow> 'b) \<Rightarrow> 't \<Rightarrow> 't"
  assumes valid_preserved: "v (w p' f s) p = v s p"
begin
lemma valid_preserved_pointless[simp]: "v (w p' f s)  = v s"
  by (rule ext) (rule valid_preserved)
end


locale valid_only_typ_desc_dependent =
  fixes t_hrs :: "('s \<Rightarrow> heap_raw_state)"
  fixes st ::"'s \<Rightarrow> 't"
  fixes v ::"'t \<Rightarrow> 'a::c_type ptr \<Rightarrow> bool"
  assumes valid_same_typ_desc [valid_same_typ_descs]: "hrs_htd (t_hrs s) = hrs_htd (t_hrs t) \<Longrightarrow> v (st s) p = v (st t) p"

locale heap_typing_simulation =
  open_types \<T> + t_hrs: heap_raw_state t_hrs t_hrs_upd + heap_typing_state heap_typing heap_typing_upd
  for
    \<T> and
    t_hrs :: "('s \<Rightarrow> heap_raw_state)" and
    t_hrs_upd :: "(heap_raw_state \<Rightarrow> heap_raw_state) \<Rightarrow> ('s \<Rightarrow> 's)" and
    heap_typing :: "'t \<Rightarrow> heap_typ_desc" and
    heap_typing_upd :: "(heap_typ_desc \<Rightarrow> heap_typ_desc) \<Rightarrow> 't \<Rightarrow> 't" +
  fixes st ::"'s \<Rightarrow> 't"
  assumes heap_typing_commutes[simp]: "heap_typing (st s) = hrs_htd (t_hrs s)"
  assumes lift_heap_update_list_stack_byte_independent:
    "(\<And>i. i < length bs \<Longrightarrow> root_ptr_valid (hrs_htd (t_hrs s)) ((p::stack_byte ptr) +\<^sub>p int i)) \<Longrightarrow>
     st (t_hrs_upd (hrs_mem_update (heap_update_list (ptr_val p) bs)) s) = st s"
  assumes st_eq_upto_padding:
    "mem_type_u t \<Longrightarrow> padding_closed_under_all_fields t \<Longrightarrow>
      ptr_valid_u t (hrs_htd (t_hrs s)) a \<Longrightarrow> eq_upto_padding t bs bs' \<Longrightarrow>
      st (t_hrs_upd (hrs_mem_update (heap_update_list a bs)) s) =
      st (t_hrs_upd (hrs_mem_update (heap_update_list a bs')) s)"
begin

lemma heap_typing_upd_commutes: "heap_typing (heap_typing_upd f (st s)) = hrs_htd (t_hrs (t_hrs_upd (hrs_htd_update f) s))"
  apply (simp add: hrs_htd_update)
  done

lemma write_simulation_alt:
  assumes v: "\<And>s p. v (st s) p \<Longrightarrow> ptr_valid (hrs_htd (t_hrs s)) p"
  assumes *: "\<And>s (p::'a::xmem_type ptr) x. v (st s) p \<Longrightarrow>
    st (t_hrs_upd (hrs_mem_update (heap_update p x)) s) = w p (\<lambda>_. x)  (st s)"
  shows "write_simulation t_hrs t_hrs_upd st v w"
proof
  fix s p x and bs :: "byte list" assume p: "v (st s) p" and bs: "length bs = size_of TYPE('a)"

  have [simp]: "t_hrs_upd (hrs_mem_update (heap_update p x)) s =
    t_hrs_upd (hrs_mem_update (heap_update_list (ptr_val p)
      (to_bytes x (heap_list (hrs_mem (t_hrs s)) (size_of TYPE('a)) (ptr_val p))))) s"
    by (rule t_hrs.heap.upd_cong) (simp add: heap_update_def)

  show "st (t_hrs_upd (hrs_mem_update (heap_update_padding p x bs)) s) = w p (\<lambda>_. x) (st s)"
    apply (subst *[OF p, symmetric])
    apply (simp add: heap_update_padding_def[abs_def])
    apply (rule st_eq_upto_padding[where t="typ_uinfo_t TYPE('a)"])
    apply (rule typ_uinfo_t_mem_type)
    apply (rule padding_closed_under_all_fields_typ_uinfo_t)
    apply (subst ptr_valid_def[symmetric])
    apply (simp add: v p)
    unfolding to_bytes_def typ_uinfo_t_def
    apply (rule field_lookup_access_ti_eq_upto_padding[where f="[]" and 'b='a])
    apply (simp_all add: bs size_of_def)
    done
qed

end

locale typ_heap_simulation =
  heap_raw_state t_hrs t_hrs_update +
  read_simulation st v r t_hrs +
  write_simulation t_hrs t_hrs_update st v w  +
  write_preserves_valid v w +
  valid_implies_cguard st v +
  valid_only_typ_desc_dependent t_hrs st v +
  pointer_lense r w
  for
    st:: "'s \<Rightarrow> 't" and
    r:: "'t \<Rightarrow> ('a::xmem_type) ptr \<Rightarrow> 'a" and
    w:: "'a ptr \<Rightarrow> ('a \<Rightarrow> 'a) \<Rightarrow> 't \<Rightarrow> 't" and
    v:: "'t \<Rightarrow> ('a::xmem_type) ptr \<Rightarrow> bool" and
    t_hrs :: "'s \<Rightarrow> heap_raw_state" and
    t_hrs_update:: "(heap_raw_state \<Rightarrow> heap_raw_state) \<Rightarrow> 's \<Rightarrow> 's"
begin

lemma write_valid_preservation [write_valid_preservation]:
  shows "v (st (t_hrs_update (hrs_mem_update (heap_update q x)) s)) p = v (st s) p"
  by (metis hrs_htd_mem_update get_upd valid_same_typ_desc)

lemma write_padding_valid_preservation [write_valid_preservation]:
  shows "v (st (t_hrs_update (hrs_mem_update (heap_update_padding q x bs)) s)) p = v (st s) p"
  by (metis hrs_htd_mem_update get_upd valid_same_typ_desc)

end



locale stack_simulation =
  heap_typing_simulation \<T> t_hrs t_hrs_update heap_typing heap_typing_upd st +
  typ_heap_typing r w heap_typing heap_typing_upd \<S>
  for
    \<T> and
    st:: "'s \<Rightarrow> 't" and
    r:: "'t \<Rightarrow> ('a::xmem_type) ptr \<Rightarrow> 'a" and
    w:: "'a ptr \<Rightarrow> ('a \<Rightarrow> 'a) \<Rightarrow> 't \<Rightarrow> 't" and
    t_hrs :: "'s \<Rightarrow> heap_raw_state" and
    t_hrs_update:: "(heap_raw_state \<Rightarrow> heap_raw_state) \<Rightarrow> 's \<Rightarrow> 's" and
    heap_typing :: "'t \<Rightarrow> heap_typ_desc" and
    heap_typing_upd :: "(heap_typ_desc \<Rightarrow> heap_typ_desc) \<Rightarrow> 't \<Rightarrow> 't" and
    \<S>:: "addr set" +
assumes sim_stack_alloc:
  "\<And>p d vs bs s n.
    (p, d) \<in> stack_allocs n \<S> TYPE('a) (hrs_htd (t_hrs s)) \<Longrightarrow> length vs = n \<Longrightarrow> length bs = n * size_of TYPE ('a) \<Longrightarrow>
      st (t_hrs_update (hrs_mem_update (fold (\<lambda>i. heap_update_padding (p +\<^sub>p int i) (vs!i) (take (size_of TYPE('a)) (drop (i * size_of TYPE('a)) bs))) [0..<n]) \<circ> hrs_htd_update (\<lambda>_. d)) s) =
      (fold (\<lambda>i. w (p +\<^sub>p int i) (\<lambda>_. (vs ! i))) [0..<n]) (heap_typing_upd (\<lambda>_. d) (st s))"

assumes sim_stack_release: "\<And>p s n. (\<And>i. i < n \<Longrightarrow> root_ptr_valid (hrs_htd (t_hrs s)) (p +\<^sub>p int i)) \<Longrightarrow>
  length bs = n * size_of TYPE('a) \<Longrightarrow>
 st (t_hrs_update (hrs_mem_update (heap_update_list (ptr_val p) bs) \<circ> hrs_htd_update (stack_releases n p)) s) =
         ((heap_typing_upd (stack_releases n p) (fold (\<lambda>i. w (p +\<^sub>p int i) (\<lambda>_. c_type_class.zero)) [0..<n] (st s))))"

assumes stack_byte_zero: "\<And>p d i. (p, d) \<in> stack_allocs n \<S> TYPE('a) (hrs_htd (t_hrs s)) \<Longrightarrow> i < n \<Longrightarrow> r (st s) (p +\<^sub>p int i) = ZERO('a)"


lemma (in typ_heap_simulation) L2Tcorres_IO_modify_paddingE [heap_abs]:
  assumes "abs_expr st P a c"
  shows "L2Tcorres st (L2_seq (L2_guard (\<lambda>t. v t p \<and> P t)) (\<lambda>_. (L2_modify (\<lambda>s. w p (\<lambda>_. a s) s)))) 
    (IO_modify_heap_paddingE (p::'a ptr) c)"
  using assms
  using length_to_bytes write_padding_commutes unfolding liftE_IO_modify_heap_padding
  by (auto simp add: abs_expr_def L2Tcorres_def corresXF_refines_conv L2_defs 
      IO_modify_heap_padding_def refines_def_old reaches_bind succeeds_bind split: xval_splits)



locale typ_heap_typing_stack_simulation =
  typ_heap_simulation st r w v t_hrs t_hrs_update +
  stack_simulation \<T> st r w t_hrs t_hrs_update heap_typing heap_typing_upd \<S>
  for
    \<T> and
    st:: "'s \<Rightarrow> 't" and
    r:: "'t \<Rightarrow> ('a::xmem_type) ptr \<Rightarrow> 'a" and
    w:: "'a ptr \<Rightarrow> ('a \<Rightarrow> 'a) \<Rightarrow> 't \<Rightarrow> 't" and
    v:: "'t \<Rightarrow> ('a::xmem_type) ptr \<Rightarrow> bool" and
    t_hrs :: "'s \<Rightarrow> heap_raw_state" and
    t_hrs_update:: "(heap_raw_state \<Rightarrow> heap_raw_state) \<Rightarrow> 's \<Rightarrow> 's" and
    heap_typing :: "'t \<Rightarrow> heap_typ_desc" and
    heap_typing_upd :: "(heap_typ_desc \<Rightarrow> heap_typ_desc) \<Rightarrow> 't \<Rightarrow> 't" and
    \<S>:: "addr set"
begin

sublocale monolithic: stack_heap_raw_state t_hrs t_hrs_update \<S>
  by (unfold_locales)

definition "rel_split_heap \<equiv> \<lambda>s\<^sub>c s\<^sub>a. s\<^sub>a = st s\<^sub>c"

lemma rel_split_heap_stack_free_eq:
  "rel_split_heap s\<^sub>c s\<^sub>a  \<Longrightarrow> stack_free (hrs_htd (t_hrs s\<^sub>c)) = stack_free (heap_typing s\<^sub>a)"
  by (simp only: rel_split_heap_def heap_typing_commutes)

definition rel_stack_free_eq where
  "rel_stack_free_eq s\<^sub>c s\<^sub>a  \<equiv> stack_free (hrs_htd (t_hrs s\<^sub>c)) = stack_free (heap_typing s\<^sub>a)"

lemma rel_prod_rel_split_heap_conv:
  "rel_prod (=) rel_split_heap = (\<lambda>(v, t) (r, s).
             s = st t \<and> (case v of Exn x \<Rightarrow> r = Exn x | Result x \<Rightarrow> r = Result x)) "
  by (auto simp add: rel_split_heap_def rel_prod_conv fun_eq_iff split: prod.splits xval_splits)

lemma L2Tcorres_refines:
  "L2Tcorres st f\<^sub>a f\<^sub>c \<Longrightarrow> refines f\<^sub>c f\<^sub>a s (st s) (rel_prod (=) rel_split_heap)"
  by (simp add: L2Tcorres_def corresXF_refines_conv rel_prod_rel_split_heap_conv)

lemma refines_L2Tcorres:
  assumes f: "\<And>s. refines f\<^sub>c f\<^sub>a s (st s) (rel_prod (=) rel_split_heap)"
  shows "L2Tcorres st f\<^sub>a f\<^sub>c"
  using f
  by (simp add: L2Tcorres_def corresXF_refines_conv rel_prod_rel_split_heap_conv)

lemma L2Tcorres_refines_conv:
"L2Tcorres st f\<^sub>a f\<^sub>c \<longleftrightarrow> (\<forall>s. refines f\<^sub>c f\<^sub>a s (st s) (rel_prod (=) rel_split_heap))"
  by (auto simp add: L2Tcorres_refines refines_L2Tcorres)

lemma sim_guard_with_fresh_stack_ptr:
  fixes f\<^sub>c:: "'a ptr \<Rightarrow> ('b, 'c, 's) exn_monad"
  assumes init: "init\<^sub>a (st s) = init\<^sub>c s"
  assumes f: "\<And>s p::'a ptr. refines (f\<^sub>c p) (f\<^sub>a p) s (st s) (rel_prod (=) rel_split_heap)"
  shows "refines
           (monolithic.with_fresh_stack_ptr n init\<^sub>c f\<^sub>c)
           (guard_with_fresh_stack_ptr n init\<^sub>a f\<^sub>a) s (st s)
           (rel_prod (=) rel_split_heap)"
  unfolding monolithic.with_fresh_stack_ptr_def guard_with_fresh_stack_ptr_def
                   stack_ptr_acquire_def stack_ptr_release_def assume_stack_alloc_def
  apply (rule refines_bind_bind_exn [where Q= "(rel_prod (=) rel_split_heap)"])
  subgoal
    apply (rule refines_assume_result_and_state')
    using sim_stack_alloc stack_byte_zero 
    by (fastforce simp add: sim_set_def rel_split_heap_def init split: xval_splits)
  apply simp
  apply simp
  apply simp
  apply (rule refines_rel_prod_guard_on_exit [where S'="rel_split_heap"])
   apply (subst (asm) rel_split_heap_def )
   apply simp
   apply (rule f)
  subgoal by (auto simp add: rel_split_heap_def sim_stack_release)
  subgoal by (simp add: Ex_list_of_length)
  done

lemma sim_with_fresh_stack_ptr:
  fixes f\<^sub>c:: "'a ptr \<Rightarrow> ('b, 'c, 's) exn_monad"
  assumes init: "init\<^sub>a (st s) = init\<^sub>c s"
  assumes f: "\<And>s p::'a ptr. refines (f\<^sub>c p) (f\<^sub>a p) s (st s) (rel_prod (=) rel_split_heap)"
  assumes typing_unchanged: "\<And>s p::'a ptr. (f\<^sub>c p) \<bullet> s ?\<lbrace>\<lambda>r t. typing.unchanged_typing_on \<S> s t\<rbrace>"
  shows "refines
           (monolithic.with_fresh_stack_ptr n init\<^sub>c f\<^sub>c)
           (with_fresh_stack_ptr n init\<^sub>a f\<^sub>a) s (st s)
           (rel_prod (=) rel_split_heap)"
  apply (simp add: monolithic.with_fresh_stack_ptr_def with_fresh_stack_ptr_def
                   stack_ptr_acquire_def stack_ptr_release_def assume_stack_alloc_def)
  apply (rule refines_bind_bind_exn [where Q= "\<lambda>(r,t) (r',t').
           (rel_prod (=) rel_split_heap) (r,t) (r',t') \<and>
          (\<exists>p. r = Result p \<and> (\<forall>i < n. ptr_span (p +\<^sub>p int i) \<subseteq> \<S> \<and> root_ptr_valid (heap_typing t') (p +\<^sub>p int i)))"], simp_all)

  subgoal
    apply (rule refines_assume_result_and_state')
    using sim_stack_alloc stack_byte_zero stack_allocs_\<S> 
    apply (clarsimp simp add: sim_set_def init rel_split_heap_def, safe)
      apply blast+
    by (smt (verit) hrs_htd_update stack_allocs_cases)
 
  subgoal for p t t'
    apply (rule refines_runs_to_partial_rel_prod_on_exit [where S'="rel_split_heap" and P="typing.unchanged_typing_on \<S> t"])
       apply (subst (asm) rel_split_heap_def )
       apply simp
       apply (rule f)
      apply (rule typing_unchanged)
    subgoal for s\<^sub>c s\<^sub>a t\<^sub>c
      apply clarsimp
      apply (clarsimp simp add: rel_split_heap_def)
      apply (subst sim_stack_release)
      subgoal for bs i
        using typing.unchanged_typing_on_root_ptr_valid_preservation [where S=\<S> and s=t and t=s\<^sub>c and p=" (p +\<^sub>p int i)"]
        by auto
      subgoal by auto
      subgoal by auto
      done
  subgoal by (simp add: Ex_list_of_length)
  done
  done

lemma sim_assume_with_fresh_stack_ptr:
  fixes f\<^sub>c:: "'a ptr \<Rightarrow> ('b, 'c, 's) exn_monad"
  assumes init: "init\<^sub>a (st s) = init\<^sub>c s"
  assumes f: "\<And>s p::'a ptr. refines (f\<^sub>c p) (f\<^sub>a p) s (st s) (rel_prod (=) rel_split_heap)"
  assumes typing_unchanged: "\<And>s p::'a ptr. (f\<^sub>c p) \<bullet> s ?\<lbrace>\<lambda>r t. typing.unchanged_typing_on \<S> s t\<rbrace>"
  shows "refines
           (monolithic.with_fresh_stack_ptr n init\<^sub>c f\<^sub>c)
           (assume_with_fresh_stack_ptr n init\<^sub>a f\<^sub>a) s (st s)
           (rel_prod (=) rel_split_heap)"
  unfolding monolithic.with_fresh_stack_ptr_def assume_with_fresh_stack_ptr_def
                   stack_ptr_acquire_def stack_ptr_release_def assume_stack_alloc_def
  apply (rule refines_bind_bind_exn [where Q= "\<lambda>(r,t) (r',t').
           (rel_prod (=) rel_split_heap) (r,t) (r',t') \<and>
          (\<exists>p. r = Result p \<and> (\<forall>i < n. ptr_span (p +\<^sub>p int i) \<subseteq> \<S> \<and> root_ptr_valid (heap_typing t') (p +\<^sub>p int i)))"])

  subgoal
    apply (rule refines_assume_result_and_state')
    using sim_stack_alloc stack_byte_zero stack_allocs_\<S>
    apply (clarsimp simp add: sim_set_def init rel_split_heap_def hrs_htd_update stack_allocs_root_ptr_valid_same)
     apply blast
    done
  apply simp
  apply simp
  apply simp
  subgoal for p q t t'
    apply (rule refines_runs_to_partial_rel_prod_assume_on_exit [where S'="rel_split_heap" and P="typing.unchanged_typing_on \<S> t"])
       apply (subst (asm) rel_split_heap_def )
       apply simp
       apply (rule f)
      apply (rule typing_unchanged)
    subgoal for s\<^sub>c s\<^sub>a t\<^sub>c
      apply clarsimp
      apply (clarsimp simp add: rel_split_heap_def)
      apply (subst sim_stack_release)
      subgoal for bs i
        using typing.unchanged_typing_on_root_ptr_valid_preservation [where S=\<S> and s=t and t=s\<^sub>c and p=" (p +\<^sub>p int i)"]
        by auto
      subgoal by auto
      subgoal by auto
      done
    subgoal by (simp add: Ex_list_of_length)
    subgoal for s\<^sub>c s\<^sub>a
      apply clarsimp
      apply (clarsimp simp add: rel_split_heap_def)
      subgoal for i
        using typing.unchanged_typing_on_root_ptr_valid_preservation [where S=\<S> and s=t and t=s\<^sub>c and p=" (p +\<^sub>p int i)"]
        by auto
      done
    done
  done



lemma L2Tcorres_guard_with_fresh_stack_ptr [heap_abs]:
  assumes rew: "struct_rewrite_expr P init\<^sub>c' init\<^sub>c"
  assumes grd: "abs_guard st P' P"
  assumes expr: "abs_expr st Q init\<^sub>a init\<^sub>c'"
  assumes f[simplified THIN_def, rule_format]: "PROP THIN (\<And>p::'a ptr. L2Tcorres st (f\<^sub>a p) (f\<^sub>c p))"
  shows "L2Tcorres st (L2_seq (L2_guard (\<lambda>s. P' s \<and> Q s))
           (\<lambda>_. (guard_with_fresh_stack_ptr n init\<^sub>a (L2_VARS f\<^sub>a nm))))
           (monolithic.with_fresh_stack_ptr n init\<^sub>c (L2_VARS f\<^sub>c nm))"
  apply (rule refines_L2Tcorres)
  apply (simp add: L2_seq_def L2_guard_def  L2_VARS_def )
  apply (rule refines_bind_guard_right)
  apply clarsimp
  apply (rule sim_guard_with_fresh_stack_ptr)
  subgoal for s
    using rew grd expr
    by (auto simp add: struct_rewrite_expr_def abs_guard_def abs_expr_def)
  subgoal for s s' p
    apply (rule L2Tcorres_refines)
    apply (rule f)
    done
  done

lemma L2Tcorres_with_fresh_stack_ptr:
  assumes typing_unchanged: "\<And>s p::'a ptr. (f\<^sub>c p) \<bullet> s ?\<lbrace>\<lambda>r t. typing.unchanged_typing_on \<S> s t\<rbrace>"
  assumes rew: "struct_rewrite_expr P init\<^sub>c' init\<^sub>c"
  assumes grd: "abs_guard st P' P"
  assumes expr: "abs_expr st Q init\<^sub>a init\<^sub>c'"
  assumes f[simplified THIN_def, rule_format]: "PROP THIN (\<And>p::'a ptr. L2Tcorres st (f\<^sub>a p) (f\<^sub>c p))"
  shows "L2Tcorres st (L2_seq (L2_guard (\<lambda>s. P' s \<and> Q s))
           (\<lambda>_. (with_fresh_stack_ptr n init\<^sub>a (L2_VARS f\<^sub>a nm))))
           (monolithic.with_fresh_stack_ptr n init\<^sub>c (L2_VARS f\<^sub>c nm))"
  apply (rule refines_L2Tcorres)
  apply (simp add: L2_seq_def L2_guard_def  L2_VARS_def)
  apply (rule refines_bind_guard_right)
  apply clarsimp
  apply (rule sim_with_fresh_stack_ptr)
  subgoal for s
    using rew grd expr
    by (auto simp add: struct_rewrite_expr_def abs_guard_def abs_expr_def)
  subgoal for s s' p
    apply (rule L2Tcorres_refines)
    apply (rule f)
    done
  using typing_unchanged by blast

lemma L2Tcorres_assume_with_fresh_stack_ptr[heap_abs]:
  assumes typing_unchanged: "\<And>s p::'a ptr. (f\<^sub>c p) \<bullet> s ?\<lbrace>\<lambda>r t. typing.unchanged_typing_on \<S> s t\<rbrace>"
  assumes rew: "struct_rewrite_expr P init\<^sub>c' init\<^sub>c"
  assumes grd: "abs_guard st P' P"
  assumes expr: "abs_expr st Q init\<^sub>a init\<^sub>c'"
  assumes f[simplified THIN_def, rule_format]: "PROP THIN (\<And>p::'a ptr. L2Tcorres st (f\<^sub>a p) (f\<^sub>c p))"
  shows "L2Tcorres st (L2_seq (L2_guard (\<lambda>s. P' s \<and> Q s))
           (\<lambda>_. (assume_with_fresh_stack_ptr n init\<^sub>a (L2_VARS f\<^sub>a nm))))
           (monolithic.with_fresh_stack_ptr n init\<^sub>c (L2_VARS f\<^sub>c nm))"
  apply (rule refines_L2Tcorres)
  apply (simp add: L2_seq_def L2_guard_def L2_VARS_def)
  apply (rule refines_bind_guard_right)
  apply clarsimp
  apply (rule sim_assume_with_fresh_stack_ptr)
  subgoal for s
    using rew grd expr
    by (auto simp add: struct_rewrite_expr_def abs_guard_def abs_expr_def)
  subgoal for s s' p
    apply (rule L2Tcorres_refines)
    apply (rule f)
    done
  using typing_unchanged by blast


lemma unchanged_typing_commutes: "typing.unchanged_typing_on S s t \<Longrightarrow> unchanged_typing_on S (st s) (st t)"
  using heap_typing_commutes [of s] heap_typing_commutes [of t]
  by (auto simp add: unchanged_typing_on_def typing.unchanged_typing_on_def)
end

(* The following lemmas help to establish that reading from stack_byte typed locations
   results in ZERO('a) *)

named_theorems read_stack_byte_ZERO_base
  and read_stack_byte_ZERO_step
  and read_stack_byte_ZERO_step_subst

lemma (in open_types) ptr_span_with_stack_byte_type_implies_ptr_invalid:
  fixes p :: "('a :: {mem_type, stack_type}) ptr"
  assumes *: "\<forall>a \<in> ptr_span p. root_ptr_valid d (PTR (stack_byte) a)"
  shows "\<not> ptr_valid_u (typ_uinfo_t TYPE('a)) d (ptr_val p)"
  by (metis assms disjoint_iff fold_ptr_valid' in_ptr_span_itself ptr_exhaust_eq
            ptr_valid_stack_byte_disjoint)

lemma (in open_types)
  ptr_span_with_stack_byte_type_implies_ZERO[read_stack_byte_ZERO_base]:
  fixes p :: "('a :: {mem_type, stack_type}) ptr"
  assumes "\<forall>a \<in> ptr_span p. root_ptr_valid (hrs_htd d) (PTR (stack_byte) a)"
  shows "the_default (ZERO('a)) (plift d p) = ZERO('a)"
  using ptr_span_with_stack_byte_type_implies_ptr_invalid[OF assms]
  by (simp add: fold_ptr_valid' plift_None)

lemma ptr_span_array_ptr_index_subset_ptr_span:
  fixes p :: "(('a :: {array_outer_max_size})['b :: array_max_count]) ptr"
  assumes "i < CARD('b)"
  shows "ptr_span (array_ptr_index p c i) \<subseteq> ptr_span p"
  using assms
  apply (simp add: array_ptr_index_def ptr_add_def)
  apply (rule intvl_sub_offset)
  apply (rule order_trans[of _ "i * size_of TYPE('a) + size_of TYPE('a)"])
  apply (simp add: unat_le_helper)
  apply (simp add: add.commute less_le_mult_nat)
  done

lemma read_stack_byte_ZERO_array_intro[read_stack_byte_ZERO_step]:
  fixes q :: "('a :: {array_outer_max_size}['b :: array_max_count]) ptr"
  assumes ptr_span_has_stack_byte_type:
    "\<forall>a\<in>ptr_span q. root_ptr_valid d (PTR(stack_byte) a)"
  assumes subtype_reads_ZERO:
    "\<And>p :: 'a ptr. \<forall>a\<in>ptr_span p. root_ptr_valid d (PTR(stack_byte) a) \<Longrightarrow> r s p = ZERO('a)"
  shows "(ARRAY i. r s (array_ptr_index q c i)) = ZERO('a['b])"
  apply (rule array_ext)
  apply (simp add: array_index_zero)
  apply (rule subtype_reads_ZERO)
  using ptr_span_has_stack_byte_type ptr_span_array_ptr_index_subset_ptr_span by blast

lemma read_stack_byte_ZERO_array_2dim_intro[read_stack_byte_ZERO_step]:
  fixes q :: "('a :: {array_inner_max_size}['b :: array_max_count]['c :: array_max_count]) ptr"
  assumes ptr_span_has_stack_byte_type:
    "\<forall>a\<in>ptr_span q. root_ptr_valid d (PTR(stack_byte) a)"
  assumes subtype_reads_ZERO:
    "\<And>p :: 'a ptr. \<forall>a\<in>ptr_span p. root_ptr_valid d (PTR(stack_byte) a) \<Longrightarrow> r s p = ZERO('a)"
  shows "(ARRAY i j. r s (array_ptr_index (array_ptr_index q c i) c j)) = ZERO('a['b]['c])"
  apply (rule array_ext)
  apply (simp add: array_index_zero)
  apply (rule array_ext)
  apply (simp add: array_index_zero)
  apply (rule subtype_reads_ZERO)
  by (metis (no_types, opaque_lifting) subset_iff ptr_span_has_stack_byte_type
            ptr_span_array_ptr_index_subset_ptr_span)

lemma read_stack_byte_ZERO_field_intro[read_stack_byte_ZERO_step]:
  fixes q :: "'a :: mem_type ptr"
  assumes ptr_span_has_stack_byte_type:
    "\<forall>a\<in>ptr_span q. root_ptr_valid d (PTR(stack_byte) a)"
  assumes subtype_reads_ZERO:
    "\<And>p :: 'b :: mem_type ptr. \<forall>a\<in>ptr_span p. root_ptr_valid d (PTR(stack_byte) a) \<Longrightarrow> r s p = ZERO('b)"
  assumes subtype_lookup:
    "field_lookup (typ_uinfo_t TYPE('a)) f 0 = Some (typ_uinfo_t TYPE('b), n)"
  shows "r s (PTR('b) (&(q\<rightarrow>f))) = ZERO('b)"
proof -
  have "ptr_span (PTR('b) (&(q\<rightarrow>f))) \<subseteq> ptr_span q"
    using TypHeapSimple.field_tag_sub'[OF subtype_lookup]
    by (simp, metis size_of_fold)
  thus ?thesis
    using ptr_span_has_stack_byte_type subtype_lookup subtype_reads_ZERO by blast
qed


context open_types
begin

lemma ptr_span_with_stack_byte_type_implies_read_dedicated_heap_ZERO[simp]:
  "\<forall>a\<in>ptr_span p. root_ptr_valid (hrs_htd s) (PTR(stack_byte) a) \<Longrightarrow>
    read_dedicated_heap s p = ZERO('a::{stack_type, xmem_type})"
  unfolding read_dedicated_heap_def ptr_span_with_stack_byte_type_implies_ZERO[of p] merge_addressable_fields.idem ..

lemma write_simulationI:
  fixes R :: "'s \<Rightarrow> 'a::xmem_type ptr \<Rightarrow> 'a"
  assumes fs: "map_of \<T> (typ_uinfo_t TYPE('a)) = Some fs"
  assumes "heap_typing_simulation \<T> t_hrs t_hrs_update heap_typing heap_typing_update l"
    and l_w: "list_all2 (\<lambda>f w. \<forall>t u n h (p::'a ptr) x.
        field_ti TYPE('a) f = Some t \<longrightarrow>
        field_lookup (typ_uinfo_t TYPE('a)) f 0 = Some (u, n) \<longrightarrow>
        ptr_valid_u u (hrs_htd (t_hrs h)) &(p\<rightarrow>f) \<longrightarrow>
        l (t_hrs_update (hrs_mem_update (heap_upd_list (size_td u) &(p\<rightarrow>f) (access_ti t x))) h)
          = w p x (l h)) fs ws"
    and l_u: "\<And>(p::'a ptr) (x::'a) (s::'b).
      ptr_valid (hrs_htd (t_hrs s)) p \<Longrightarrow>
      l (t_hrs_update (write_dedicated_heap p x) s) = u (upd_fun p (\<lambda>old. merge_addressable_fields old x)) (l s)"
  assumes V:
    "\<And>h p. V (l h) p \<longleftrightarrow> ptr_valid (hrs_htd (t_hrs h)) p"
  assumes W:
    "\<And>p f h. W p f h =
      fold (\<lambda>w. w p (f (R h p))) ws (u (upd_fun p (\<lambda>old. merge_addressable_fields old (f (R h p)))) h)"
  shows "write_simulation t_hrs t_hrs_update l V W"
proof -
  interpret hrs: heap_typing_simulation \<T> t_hrs t_hrs_update heap_typing heap_typing_update l
    by fact

  have valid:
    "list_all (\<lambda>f. \<forall>u n. field_lookup (typ_uinfo_t TYPE('a)) f 0 = Some (u, n) \<longrightarrow>
      ptr_valid_u u h &(p\<rightarrow>f)) fs"
    if *: "ptr_valid_u (typ_uinfo_t TYPE('a)) h (ptr_val p)" for h and p :: "'a ptr"
    using ptr_valid_u_step[OF fs _ _ *]
    by (auto simp: list_all_iff field_lvalue_def field_offset_def)

  have fold': "l (fold
        (\<lambda>xa. t_hrs_update
                (hrs_mem_update
                  (heap_upd_list (size_td (the (field_ti TYPE('a) xa))) &(p\<rightarrow>xa)
                    (access_ti (the (field_ti TYPE('a) xa)) x))))
        fs s) =
      fold (\<lambda>w. w p x) ws (l s)"
    if p: "ptr_valid_u (typ_uinfo_t TYPE('a)) (hrs_htd (t_hrs s)) (ptr_val p)"
    for p x s
    using l_w wf_\<T>[OF fs] p[THEN valid]
  proof (induction arbitrary: s)
    case (Cons f fs w ws)
    from Cons.prems obtain u n where f_u :"field_lookup (typ_uinfo_t TYPE('a)) f 0 = Some (u, n)"
      and [simp]: "list_all (\<lambda>f. \<exists>a b. field_lookup (typ_uinfo_t TYPE('a)) f 0 = Some (a, b)) fs"
      by auto
    from f_u[THEN field_lookup_uinfo_Some_rev] obtain k where
      "field_lookup (typ_info_t TYPE('a)) f 0 = Some (k, n)" and u_eq: "u = export_uinfo k"
      by auto
    then have [simp]: "field_ti TYPE('a) f = Some k" by (simp add: field_ti_def)
    have [simp]: "size_td k = size_td u"
      by (simp add: u_eq)
    have [simp]: "ptr_valid_u u (hrs_htd (t_hrs s)) &(p\<rightarrow>f)"
      using Cons.prems(2) f_u by auto
    show ?case
      using Cons.prems Cons.hyps by (simp add: Cons.IH f_u)
  qed simp

  have fold:
    "l ((fold (t_hrs_update \<circ>
          (\<lambda>(f, u). hrs_mem_update (heap_upd_list (size_td u) &(p\<rightarrow>f) (access_ti u x))))
        (addressable_fields TYPE('a)) \<circ>
      t_hrs_update (write_dedicated_heap p x)) s) =
    fold (\<lambda>w. w p x) ws (u (upd_fun p (\<lambda>old. merge_addressable_fields old x)) (l s))"
    if p: "ptr_valid_u (typ_uinfo_t TYPE('a)) (hrs_htd (t_hrs s)) (ptr_val p)"
    for p x s
    by (subst addressable_fields_def)
       (simp add: fs fold_map fold' p ptr_valid_def l_u cong: fold_cong)

  show ?thesis
    apply (rule hrs.write_simulation_alt)
    apply (simp add: V)
    apply (subst hrs_mem_update_heap_update')
    apply (subst W)
    apply (subst (asm) V)
    apply (subst (asm) ptr_valid_def)
    apply (subst hrs.t_hrs.upd_comp[symmetric])
    apply (subst hrs.t_hrs.upd_comp_fold)
    apply (subst fold)
    apply simp_all
    done
qed

end

locale stack_simulation_heap_typing =
  typ_heap_simulation st r w "\<lambda>t p. open_types.ptr_valid \<T> (heap_typing t) p" t_hrs t_hrs_update +
  heap_typing_simulation \<T> t_hrs t_hrs_update heap_typing heap_typing_upd st +
  typ_heap_typing r w heap_typing heap_typing_upd \<S>
  for
    st:: "'s \<Rightarrow> 't" and
    r:: "'t \<Rightarrow> ('a::{xmem_type, stack_type}) ptr \<Rightarrow> 'a" and
    w:: "'a ptr \<Rightarrow> ('a \<Rightarrow> 'a) \<Rightarrow> 't \<Rightarrow> 't" and
    t_hrs :: "'s \<Rightarrow> heap_raw_state" and
    t_hrs_update:: "(heap_raw_state \<Rightarrow> heap_raw_state) \<Rightarrow> 's \<Rightarrow> 's" and
    heap_typing :: "'t \<Rightarrow> heap_typ_desc" and
    heap_typing_upd :: "(heap_typ_desc \<Rightarrow> heap_typ_desc) \<Rightarrow> 't \<Rightarrow> 't" and
    \<S>:: "addr set" and
    \<T>:: "(typ_uinfo * qualified_field_name list) list" +

assumes sim_stack_alloc_heap_typing:
  "\<And>p d s n.
    (p, d) \<in> stack_allocs n \<S> TYPE('a) (hrs_htd (t_hrs s)) \<Longrightarrow>
      st (t_hrs_update (hrs_mem_update (fold (\<lambda>i. heap_update (p +\<^sub>p int i) c_type_class.zero) [0..<n]) \<circ> hrs_htd_update (\<lambda>_. d)) s) =
      (heap_typing_upd (\<lambda>_. d) (st s))"

assumes sim_stack_release_heap_typing:
"\<And>(p::'a ptr) s n. (\<And>i. i < n \<Longrightarrow> root_ptr_valid (hrs_htd (t_hrs s)) (p +\<^sub>p int i)) \<Longrightarrow>
  st (t_hrs_update (hrs_htd_update (stack_releases n p)) s) =
    heap_typing_upd (stack_releases n p)
     (st (t_hrs_update (hrs_mem_update (fold (\<lambda>i. heap_update (p +\<^sub>p int i) c_type_class.zero) [0..<n])) s))"

assumes sim_stack_stack_byte_zero[read_stack_byte_ZERO_step]:
  "\<And>p s. \<forall>a\<in>ptr_span p. root_ptr_valid (hrs_htd (t_hrs s)) (PTR(stack_byte) a) \<Longrightarrow> r (st s) p = ZERO('a)" (* " *)

begin

lemma fold_heap_update_simulation:
  assumes valid: "\<And>i. i < n \<Longrightarrow> ptr_valid (heap_typing (st s)) (p +\<^sub>p int i)"
  shows "st (t_hrs_update (hrs_mem_update (fold (\<lambda>i. heap_update (p +\<^sub>p int i) (vs i)) [0..<n])) s) =
          fold (\<lambda>i. w (p +\<^sub>p int i) (\<lambda>_. vs i)) [0..<n] (st s)"
  using valid
proof (induct n arbitrary: vs s)
  case 0
  then show ?case
    by (simp add: case_prod_unfold hrs_mem_update_def)
next
  case (Suc n)
  from Suc.prems obtain
    valid: "\<And>i. i < Suc n \<Longrightarrow> ptr_valid (heap_typing (st s)) (p +\<^sub>p int i)" by blast

  from valid have valid': "\<And>i. i < n \<Longrightarrow> ptr_valid (heap_typing (st s)) (p +\<^sub>p int i)" by auto
  note hyp = Suc.hyps [OF valid']
  show ?case
    apply (simp add: hyp [symmetric])
    apply (subst write_commutes [symmetric])
    using valid
    apply simp
    using TypHeapSimple.hrs_mem_update_comp hrs_mem_update_def
    apply simp
    done
qed

lemma fold_heap_update_padding_simulation:
  assumes valid: "\<And>i. i < n \<Longrightarrow> ptr_valid (heap_typing (st s)) (p +\<^sub>p int i)"
  assumes lbs: "length bs = n * size_of TYPE('a)"
  shows "st (t_hrs_update (hrs_mem_update (fold (\<lambda>i. heap_update_padding (p +\<^sub>p int i) (vs i) (take (size_of TYPE('a)) (drop (i * size_of TYPE('a)) bs))) [0..<n])) s) =
          fold (\<lambda>i. w (p +\<^sub>p int i) (\<lambda>_. vs i)) [0..<n] (st s)"
  using valid lbs
proof (induct n arbitrary: bs vs s )
  case 0
  then show ?case
    by (simp add: case_prod_unfold hrs_mem_update_def)
next
  case (Suc n)
  from Suc.prems obtain
    valid: "\<And>i. i < Suc n \<Longrightarrow> ptr_valid (heap_typing (st s)) (p +\<^sub>p int i)" and
    lbs': "length (take (n * (size_of TYPE('a))) bs) = n * size_of TYPE('a)"
    by auto

  from valid have valid': "\<And>i. i < n \<Longrightarrow> ptr_valid (heap_typing (st s)) (p +\<^sub>p int i)" by auto
  note hyp = Suc.hyps [OF valid' lbs']
  have take_eq: "\<And>i. i < n \<Longrightarrow> take (size_of TYPE('a)) (drop (i * size_of TYPE('a)) (take (n * size_of TYPE('a)) bs)) =
        take (size_of TYPE('a)) (drop (i * size_of TYPE('a)) bs)"
    by (metis Groups.mult_ac(2) mult_less_cancel1 not_less not_less_eq
        order_less_imp_le take_all take_drop_take times_nat.simps(2))

  have fold_eq: "\<And>h. fold
              (\<lambda>i. heap_update_padding (p +\<^sub>p int i) (vs i)
                        (take (size_of TYPE('a)) (drop (i * size_of TYPE('a)) (take (n * size_of TYPE('a)) bs))))
              [0..<n] h =
            fold
              (\<lambda>i. heap_update_padding (p +\<^sub>p int i) (vs i)
                        (take (size_of TYPE('a)) (drop (i * size_of TYPE('a)) bs)))
                 [0..<n] h"

    apply (rule fold_cong)
      apply (rule refl)
     apply (rule refl)
    using take_eq
    apply simp
    done


  show ?case
    apply (simp add: hyp [symmetric])
    apply (subst write_padding_commutes [symmetric, where bs = "take (size_of TYPE('a)) (drop (n * size_of TYPE('a)) bs)"])
    subgoal using valid
      by simp
    subgoal using Suc.prems by simp
    subgoal
    using TypHeapSimple.hrs_mem_update_comp hrs_mem_update_def
      by (simp add: fold_eq)
    done
qed

lemma sim_stack_alloc':
  assumes alloc: "(p, d) \<in> stack_allocs n \<S> TYPE('a) (hrs_htd (t_hrs s))"
  assumes len: "length vs = n"
  assumes lbs: "length bs = n * size_of TYPE('a)"
  shows "st (t_hrs_update (hrs_mem_update (fold (\<lambda>i. heap_update_padding (p +\<^sub>p int i) (vs!i) (take (size_of TYPE('a)) (drop (i * size_of TYPE('a)) bs))) [0..<n]) \<circ> hrs_htd_update (\<lambda>_. d)) s) =
            (fold (\<lambda>i. w (p +\<^sub>p int i) (\<lambda>_. (vs ! i))) [0..<n]) (heap_typing_upd (\<lambda>_. d) (st s))"
proof -
  {
    fix i
    assume i_bound: "i < n"
    have "ptr_valid (heap_typing (st (t_hrs_update
                 (hrs_mem_update (fold (\<lambda>i. heap_update (p +\<^sub>p int i) c_type_class.zero) [0..<n]) \<circ>
                  hrs_htd_update (\<lambda>_. d))
                 s)))
          (p +\<^sub>p int i)"
    proof -
      from stack_allocs_cases [OF alloc] i_bound
      have ptr_valid: "ptr_valid d (p +\<^sub>p int i)"
        using root_ptr_valid_ptr_valid by auto
      thus ?thesis
        using heap_typing_upd_commutes by (simp, metis)
    qed
  } note valids = this

  from stack_allocs_cases [OF alloc] obtain
    bound: "unat (ptr_val p) + n * size_of TYPE('a) \<le> addr_card" and
    not_null: "ptr_val p \<noteq> 0"
    by (metis Ptr_ptr_val c_guard_NULL_simp)

  show ?thesis
    apply (simp add: sim_stack_alloc_heap_typing [OF alloc, symmetric])
    apply (subst fold_heap_update_padding_simulation [OF valids lbs, symmetric])
      apply (simp)
     apply (simp add: len)
    apply (simp add: comp_def hrs_mem_update_comp')
    apply (subst fold_heap_update_padding_heap_update_collapse [OF bound not_null])
    using lbs
     apply (auto simp add: less_le_mult_nat nat_move_sub_le)
    done
qed

lemma sim_stack_release':
  fixes p :: "'a ptr"
  assumes roots: "\<And>i. i < n \<Longrightarrow> root_ptr_valid (hrs_htd (t_hrs s)) (p +\<^sub>p int i)"
  shows "st (t_hrs_update (hrs_htd_update (stack_releases n p)) s) =
           ((heap_typing_upd (stack_releases n p) ((fold (\<lambda>i. w (p +\<^sub>p int i) (\<lambda>_. c_type_class.zero)) [0..<n]) (st s))))"
proof -
  from roots root_ptr_valid_ptr_valid heap_typing_commutes
  have valids: "\<And>i . i < n \<Longrightarrow> ptr_valid (heap_typing (st s)) (p +\<^sub>p int i)"
    by metis
  note commutes = fold_heap_update_simulation [OF valids, symmetric, of n, simplified]
  show ?thesis
    apply (simp add: commutes )
    apply (simp add: sim_stack_release_heap_typing [OF roots])
    done
qed


lemma sim_stack_release'':
  fixes p :: "'a ptr"
  assumes roots: "\<And>i. i < n \<Longrightarrow> root_ptr_valid (hrs_htd (t_hrs s)) (p +\<^sub>p int i)"
  assumes lbs: "length bs = n * size_of TYPE('a)"
  shows "st (t_hrs_update (hrs_mem_update (heap_update_list (ptr_val p) bs) o hrs_htd_update (stack_releases n p)) s) =
           ((heap_typing_upd (stack_releases n p) ((fold (\<lambda>i. w (p +\<^sub>p int i) (\<lambda>_. c_type_class.zero)) [0..<n]) (st s))))"
proof -
  {
    fix i
    assume bound_i: "i < length bs"
    have "root_ptr_valid (hrs_htd (t_hrs (t_hrs_update (hrs_htd_update (stack_releases n p)) s)))
            ((PTR_COERCE('a \<rightarrow> stack_byte) p) +\<^sub>p int i)"
    proof -
      have span: "ptr_val (((PTR_COERCE('a \<rightarrow> stack_byte) p) +\<^sub>p int i)) \<in> {ptr_val p..+n * size_of TYPE('a)}"
        using lbs bound_i intvlI by (auto simp add: ptr_add_def)
      from roots have "\<forall>i<n. c_guard (p +\<^sub>p int i)"
        using root_ptr_valid_c_guard by blast
      from stack_releases_root_ptr_valid_footprint [OF span this]
      show ?thesis
        using typing.get_upd by force
    qed
  } note sb = this

  show ?thesis
    apply (simp add:  lift_heap_update_list_stack_byte_independent [OF sb, simplified])
    apply (simp add: sim_stack_release' [OF roots])
    done
qed


lemma stack_byte_zero':
  assumes "(p, d) \<in> stack_allocs n \<S> TYPE('a) (hrs_htd (t_hrs s))"
  assumes "i < n"
  shows "r (st s) (p +\<^sub>p int i) = ZERO('a)"
  by (rule sim_stack_stack_byte_zero)
     (meson assms stack_allocs_cases stack_allocs_contained subsetD)

sublocale stack_simulation
  using sim_stack_alloc' sim_stack_release'' stack_byte_zero'
  by (unfold_locales) auto

sublocale typ_heap_typing_stack_simulation \<T> st r w "\<lambda>t p. open_types.ptr_valid \<T> (heap_typing t) p" t_hrs t_hrs_update heap_typing heap_typing_upd \<S>
  by (unfold_locales)

end





(*
 * Assert the given field ("field_getter", "field_setter") of the given structure
 * can be abstracted into the heap, and then accessed as a HOL object.
 *)

(*
 * This can deal with nested structures, but they must be packed_types.
 * fixme: generalise this framework to mem_types
 *)

definition
  valid_struct_field
    :: "string list
           \<Rightarrow> (('p::xmem_type) \<Rightarrow> ('f::xmem_type))
           \<Rightarrow> (('f \<Rightarrow> 'f) \<Rightarrow> ('p \<Rightarrow> 'p))
           \<Rightarrow> ('s \<Rightarrow> heap_raw_state)
           \<Rightarrow> ((heap_raw_state \<Rightarrow> heap_raw_state) \<Rightarrow> 's \<Rightarrow> 's)
           \<Rightarrow> bool"
 where
  "valid_struct_field field_name field_getter field_setter t_hrs t_hrs_update \<equiv>
     (lense field_getter field_setter
      \<and> field_ti TYPE('p) field_name =
          Some (adjust_ti (typ_info_t TYPE('f)) field_getter (field_setter \<circ> (\<lambda>x _. x)))
      \<and> (\<forall>p :: 'p ptr. c_guard p \<longrightarrow> c_guard (Ptr &(p\<rightarrow>field_name) :: 'f ptr))
      \<and> lense t_hrs t_hrs_update)"

lemma typ_heap_simulation_get_hvalD:
  "\<lbrakk> typ_heap_simulation st r w v
        t_hrs t_hrs_update; v (st s) p \<rbrakk> \<Longrightarrow>
      h_val (hrs_mem (t_hrs s)) p = r (st s) p"
  by (clarsimp simp: read_simulation.read_commutes [OF typ_heap_simulation.axioms(2)])

lemma valid_struct_fieldI [intro]:
  fixes field_getter :: "('a::xmem_type) \<Rightarrow> ('f::xmem_type)"
  shows "\<lbrakk>
     \<And>s f. f (field_getter s) = (field_getter s) \<Longrightarrow> field_setter f s = s;
     \<And>s f f'. f (field_getter s) = f' (field_getter s) \<Longrightarrow> field_setter f s = field_setter f' s;
     \<And>s f. field_getter (field_setter f s) = f (field_getter s);
     \<And>s f g. field_setter f (field_setter g s) = field_setter (f \<circ> g) s;
     field_ti TYPE('a) field_name =
         Some (adjust_ti (typ_info_t TYPE('f)) field_getter (field_setter \<circ> (\<lambda>x _. x)));
     \<And>(p::'a ptr). c_guard p \<Longrightarrow> c_guard (Ptr &(p\<rightarrow>field_name) :: 'f ptr);
     \<And>s x. t_hrs (t_hrs_update x s) = x (t_hrs s);
     \<And>s f. f (t_hrs s) = t_hrs s \<Longrightarrow> t_hrs_update f s = s;
     \<And>s f f'. f (t_hrs s) = f' (t_hrs s) \<Longrightarrow> t_hrs_update f s = t_hrs_update f' s;
     \<And>s f g. t_hrs_update f (t_hrs_update g s) = t_hrs_update (\<lambda>x. f (g x)) s
      \<rbrakk> \<Longrightarrow>
    valid_struct_field field_name field_getter field_setter t_hrs t_hrs_update"
  apply (unfold valid_struct_field_def lense_def o_def)
  apply (safe | assumption | rule ext)+
  done

lemma typ_heap_simulation_t_hrs_updateD:
  "\<lbrakk> typ_heap_simulation st r w v
         t_hrs t_hrs_update; v (st s) p \<rbrakk> \<Longrightarrow>
           st (t_hrs_update (hrs_mem_update (heap_update p v')) s) =
                           w p (\<lambda>x. v') (st s)"
  by (clarsimp simp: write_simulation.write_commutes [OF typ_heap_simulation.axioms(3)])

lemma heap_abs_expr_guard [heap_abs]:
  "\<lbrakk> typ_heap_simulation st getter setter vgetter t_hrs t_hrs_update;
     abs_expr st P x' x \<rbrakk> \<Longrightarrow>
     abs_guard st (\<lambda>s. P s \<and> vgetter s (x' s)) (\<lambda>s. (c_guard (x s :: ('a::xmem_type) ptr)))"
  apply (clarsimp simp: abs_expr_def abs_guard_def
                        simple_lift_def root_ptr_valid_def
                        valid_implies_cguard.valid_implies_c_guard [OF typ_heap_simulation.axioms(5)])
  done

lemma heap_abs_expr_h_val [heap_abs]:
  "\<lbrakk> typ_heap_simulation st r w v t_hrs t_hrs_update;
     abs_expr st P x' x \<rbrakk> \<Longrightarrow>
      abs_expr st
       (\<lambda>s. P s \<and> v s (x' s))
         (\<lambda>s. (r s (x' s)))
         (\<lambda>s. (h_val (hrs_mem (t_hrs s))) (x s))"
  apply (clarsimp simp: abs_expr_def simple_lift_def)
  apply (metis typ_heap_simulation_get_hvalD)
  done

lemma heap_abs_modifies_heap_update__unused:
  "\<lbrakk> typ_heap_simulation st r w v t_hrs t_hrs_update;
     abs_expr st Pb b' b;
     abs_expr st Pc c' c \<rbrakk> \<Longrightarrow>
      abs_modifies st (\<lambda>s. Pb s \<and> Pc s \<and> v s (b' s))
        (\<lambda>s. w (b' s) (\<lambda>x. (c' s)) s)
        (\<lambda>s. t_hrs_update (hrs_mem_update (heap_update (b s :: ('a::xmem_type) ptr) (c s))) s)"
  apply (clarsimp simp: typ_simple_heap_simps abs_expr_def abs_modifies_def)
  apply (metis typ_heap_simulation_t_hrs_updateD)
  done

(* See comment for heap_lift__wrap_h_val. *)
definition "heap_lift__h_val \<equiv> h_val"

(* See the comment for struct_rewrite_modifies_field.
 * In this case we rely on nice unification for ?c.
 * The heap_abs_syntax generator also relies on this rule
 * and would need to be modified if the previous rule was used instead. *)
(*        (\<lambda>s. setter (\<lambda>x. x(b' s := c' (x (b' s)) s)) s) *)
lemma heap_abs_modifies_heap_update [heap_abs]:
  "\<lbrakk> typ_heap_simulation st r w v t_hrs t_hrs_update;
     abs_expr st Pb b' b;
     \<And>v. abs_expr st Pc (c' v) (c v) \<rbrakk> \<Longrightarrow>
      abs_modifies st (\<lambda>s. Pb s \<and> Pc s \<and> v s (b' s))
        (\<lambda>s. w (b' s) (\<lambda>_. (c' (r s (b' s)) s)) s)
        (\<lambda>s. t_hrs_update (hrs_mem_update
               (heap_update (b s :: ('a::xmem_type) ptr)
                            (c (heap_lift__h_val (hrs_mem (t_hrs s)) (b s)) s))) s)"
  apply (clarsimp simp: typ_simple_heap_simps abs_expr_def abs_modifies_def heap_lift__h_val_def)
  subgoal for s
    apply (rule subst[where t = "h_val (hrs_mem (t_hrs s)) (b' (st s))"
        and s = "r (st s) (b' (st s))"])
     apply (clarsimp simp: read_simulation.read_commutes [OF typ_heap_simulation.axioms(2)])
    apply (simp add: write_simulation.write_commutes [OF typ_heap_simulation.axioms(3)])
    done
  done


(*
 * struct_rewrite: remove uses of field_lvalue. (field_lvalue p a = &(p\<rightarrow>a))
 * We do three transformations:
 *   c_guard (p\<rightarrow>a)  \<Longleftarrow>  c_guard p
 *   h_val s (p\<rightarrow>a)   =   p_C.a_C (h_val s p)
 *   heap_update (p\<rightarrow>a) v s   =   heap_update p (p_C.a_C_update (\<lambda>_. v) (h_val s p)) s
 * However, an inner expression may nest h_vals arbitrarily.
 *
 * Any output of a struct_rewrite rule should be fully rewritten.
 * By doing this, each rule only needs to rewrite the parts of a term that it
 * introduces by itself.
 *)

(* struct_rewrite_guard rules *)

lemma struct_rewrite_guard_expr [heap_abs]:
  "struct_rewrite_expr P a' a \<Longrightarrow> struct_rewrite_guard (\<lambda>s. P s \<and> a' s) a"
  by (simp add: struct_rewrite_expr_def struct_rewrite_guard_def)

lemma struct_rewrite_guard_constant [heap_abs]:
  "struct_rewrite_guard (\<lambda>_. P) (\<lambda>_. P)"
  by (simp add: struct_rewrite_guard_def)

lemma struct_rewrite_guard_conj [heap_abs]:
  "\<lbrakk> struct_rewrite_guard b' b; struct_rewrite_guard a' a \<rbrakk> \<Longrightarrow>
       struct_rewrite_guard (\<lambda>s. a' s \<and> b' s) (\<lambda>s. a s \<and> b s)"
  by (clarsimp simp: struct_rewrite_guard_def)

lemma struct_rewrite_guard_split [heap_abs]:
  "\<lbrakk> \<And>a b. struct_rewrite_guard (A a b) (C a b) \<rbrakk>
       \<Longrightarrow> struct_rewrite_guard (case r of (a, b) \<Rightarrow> A a b) (case r of (a, b) \<Rightarrow> C a b)"
  apply (auto simp: split_def)
  done

lemma struct_rewrite_guard_c_guard_field [heap_abs]:
  "\<lbrakk> valid_struct_field field_name (field_getter :: ('a :: xmem_type) \<Rightarrow> ('f :: xmem_type)) field_setter t_hrs t_hrs_update;
     struct_rewrite_expr P p' p;
     struct_rewrite_guard Q (\<lambda>s. c_guard (p' s)) \<rbrakk> \<Longrightarrow>
   struct_rewrite_guard (\<lambda>s. P s \<and> Q s)
     (\<lambda>s. c_guard (Ptr (field_lvalue (p s :: 'a ptr) field_name) :: 'f ptr))"
  by (simp add: valid_struct_field_def struct_rewrite_expr_def struct_rewrite_guard_def)

lemma align_of_array: "align_of TYPE(('a :: array_outer_max_size)['b' :: array_max_count]) = align_of TYPE('a)"
  by (simp add: align_of_def align_td_array)


lemma c_guard_array:
  "\<lbrakk> 0 \<le> k; nat k < CARD('b); c_guard (p :: (('a::array_outer_max_size)['b::array_max_count]) ptr) \<rbrakk>
   \<Longrightarrow> c_guard (ptr_coerce p +\<^sub>p k :: 'a ptr)"
  apply (clarsimp simp: CTypesDefs.ptr_add_def c_guard_def c_null_guard_def)
  apply (rule conjI[rotated])
   apply (erule contrapos_nn)
   apply (clarsimp simp: intvl_def)
  subgoal for i
    apply (rule exI[where  x = "nat k * size_of TYPE('a) + i"])
    apply clarsimp
    apply (rule conjI)
     apply (simp add: field_simps)
    apply (rule less_le_trans[where y = "Suc (nat k) * size_of TYPE('a)"])
     apply simp
    apply (metis less_eq_Suc_le mult_le_mono2 mult.commute)
    done
  apply (subgoal_tac "ptr_aligned (ptr_coerce p :: 'a ptr)")
   apply (frule_tac p = "ptr_coerce p" and i = "k" in ptr_aligned_plus)
   apply (clarsimp simp: CTypesDefs.ptr_add_def)
  apply (clarsimp simp: ptr_aligned_def align_of_array)
  done

lemma struct_rewrite_guard_c_guard_Array_field [heap_abs]:
  "\<lbrakk> valid_struct_field field_name (field_getter :: ('a :: xmem_type) \<Rightarrow> ('f::array_outer_max_size ['n::array_max_count])) field_setter t_hrs t_hrs_update;
     struct_rewrite_expr P p' p;
     struct_rewrite_guard Q (\<lambda>s. c_guard (p' s)) \<rbrakk> \<Longrightarrow>
   struct_rewrite_guard (\<lambda>s. P s \<and> Q s \<and> 0 \<le> k \<and> nat k < CARD('n))
     (\<lambda>s. c_guard (ptr_coerce (Ptr (field_lvalue (p s :: 'a ptr) field_name) :: (('f['n]) ptr)) +\<^sub>p k :: 'f ptr))"
  by (simp del: ptr_coerce.simps add: valid_struct_field_def struct_rewrite_expr_def struct_rewrite_guard_def c_guard_array)


(* struct_rewrite_expr rules *)

(* This is only used when heap lifting is turned off,
 * where we expect no rewriting to happen anyway.
 * TODO: it might be safe to enable this unconditionally,
 *       as long as it happens after heap_abs_fo. *)
lemma struct_rewrite_expr_id:
  "struct_rewrite_expr (\<lambda>_. True) A A"
  by (simp add: struct_rewrite_expr_def)


lemma struct_rewrite_expr_fun_app2 [heap_abs_fo]:
  "\<lbrakk> struct_rewrite_expr P f f';
     struct_rewrite_expr Q g g' \<rbrakk> \<Longrightarrow>
   struct_rewrite_expr (\<lambda>s. P s \<and> Q s) (\<lambda>s a. f s a (g s a)) (\<lambda>s a. f' s a $ g' s a)"
  by (simp add: struct_rewrite_expr_def)

lemma struct_rewrite_expr_fun_app [heap_abs_fo]:
  "\<lbrakk> struct_rewrite_expr Y x x'; struct_rewrite_expr X f f' \<rbrakk> \<Longrightarrow>
       struct_rewrite_expr (\<lambda>s. X s \<and> Y s) (\<lambda>s. f s (x s)) (\<lambda>s. f' s $ x' s)"
  by (clarsimp simp: struct_rewrite_expr_def)

lemma struct_rewrite_expr_constant [heap_abs]:
  "struct_rewrite_expr (\<lambda>_. True) (\<lambda>_. a) (\<lambda>_. a)"
  by (clarsimp simp: struct_rewrite_expr_def)

lemma struct_rewrite_expr_lambda_null [heap_abs]:
  "struct_rewrite_expr P A C \<Longrightarrow> struct_rewrite_expr P (\<lambda>s _. A s) (\<lambda>s _. C s)"
  by (clarsimp simp: struct_rewrite_expr_def)

lemma struct_rewrite_expr_split [heap_abs]:
  "\<lbrakk> \<And>a b. struct_rewrite_expr (P a b) (A a b) (C a b) \<rbrakk>
       \<Longrightarrow> struct_rewrite_expr (case r of (a, b) \<Rightarrow> P a b)
            (case r of (a, b) \<Rightarrow> A a b) (case r of (a, b) \<Rightarrow> C a b)"
  apply (auto simp: split_def)
  done

lemma struct_rewrite_expr_basecase_h_val [heap_abs]:
  "struct_rewrite_expr (\<lambda>_. True) (\<lambda>s. h_val (h s) (p s)) (\<lambda>s. h_val (h s) (p s))"
  by (simp add: struct_rewrite_expr_def)

lemma struct_rewrite_expr_indirect_h_val [heap_abs]:
  "struct_rewrite_expr P a c \<Longrightarrow>
   struct_rewrite_expr P (\<lambda>s. h_val (h s) (a s)) (\<lambda>s. h_val (h s) (c s))"
  by (simp add: struct_rewrite_expr_def)

lemma struct_rewrite_expr_field [heap_abs]:
  "\<lbrakk> valid_struct_field field_name (field_getter :: ('a :: xmem_type) \<Rightarrow> ('f :: xmem_type)) field_setter t_hrs t_hrs_update;
     struct_rewrite_expr P p' p;
     struct_rewrite_expr Q a (\<lambda>s. h_val (hrs_mem (t_hrs s)) (p' s)) \<rbrakk>
   \<Longrightarrow> struct_rewrite_expr (\<lambda>s. P s \<and> Q s) (\<lambda>s. field_getter (a s))
        (\<lambda>s. h_val (hrs_mem (t_hrs s)) (Ptr (field_lvalue (p s) field_name)))"
  apply (clarsimp simp: valid_struct_field_def struct_rewrite_expr_def)
  apply (subst h_val_field_from_bytes')
    apply assumption
   apply (rule export_tag_adjust_ti(1)[rule_format])
    apply (simp add: lense.fg_cons)
   apply simp
  apply simp
  done

lemma abs_expr_field [heap_abs]:
  "\<lbrakk> valid_struct_field field_name (field_getter :: ('a :: xmem_type) \<Rightarrow> ('f :: xmem_type)) field_setter t_hrs t_hrs_update;
     abs_expr st P a c\<rbrakk>
   \<Longrightarrow> abs_expr st P (\<lambda>s. field_getter (a s)) (\<lambda>s. field_getter (c s))"
  by (clarsimp simp add: valid_struct_field_def abs_expr_def)

(* Descend into struct fields that are themselves arrays. *)
lemma struct_rewrite_expr_Array_field [heap_abs]:
  "\<lbrakk> valid_struct_field field_name
                        (field_getter :: ('a :: xmem_type) \<Rightarrow> 'f::array_outer_max_size ['n::array_max_count])
                        field_setter t_hrs t_hrs_update;
     struct_rewrite_expr P p' p;
     struct_rewrite_expr Q a (\<lambda>s. h_val (hrs_mem (t_hrs s)) (p' s)) \<rbrakk>
   \<Longrightarrow> struct_rewrite_expr (\<lambda>s. P s \<and> Q s \<and> k \<ge> 0 \<and> nat k < CARD('n))
        (\<lambda>s. index (field_getter (a s)) (nat k))
        (\<lambda>s. h_val (hrs_mem (t_hrs s))
               (ptr_coerce (Ptr (field_lvalue (p s) field_name) :: ('f['n]) ptr) +\<^sub>p k))"
  apply (cases k)
   apply (clarsimp simp: struct_rewrite_expr_def simp del: ptr_coerce.simps)
  subgoal for n s
    apply (subst struct_rewrite_expr_field
        [unfolded struct_rewrite_expr_def, simplified, rule_format, symmetric,
          where field_getter = field_getter and P = P and Q = Q and p = p and p' = p'])
        apply assumption
       apply simp
      apply simp
     apply simp
    apply (rule subst[where s = "p s" and t = "p' s"])
     apply simp
    apply (rule heap_access_Array_element[symmetric])
    apply simp
    done
  apply (simp add: struct_rewrite_expr_def)
  done
declare struct_rewrite_expr_Array_field [unfolded ptr_coerce.simps, heap_abs]

(* struct_rewrite_modifies rules *)

lemma struct_rewrite_modifies_id [heap_abs]:
  "struct_rewrite_modifies (\<lambda>_. True) A A"
  by (simp add: struct_rewrite_modifies_def)

(* We need some typ_heap_simulation, but we're really only after t_hrs_update.
 * We artificially constrain the type of v to limit backtracking,
 * since specialisation of typ_heap_simulation will generate one rule per 'a. *)
lemma struct_rewrite_modifies_basecase [heap_abs]:
  "\<lbrakk> typ_heap_simulation st (getter :: 's \<Rightarrow> 'a ptr \<Rightarrow> ('a::xmem_type)) setter vgetter t_hrs t_hrs_update;
     struct_rewrite_expr P p' p;
     struct_rewrite_expr Q v' v \<rbrakk> \<Longrightarrow>
   struct_rewrite_modifies (\<lambda>s. P s \<and> Q s)
     (\<lambda>s. t_hrs_update (hrs_mem_update (heap_update (p' s) (v' s :: 'a))) s)
     (\<lambda>s. t_hrs_update (hrs_mem_update (heap_update (p s) (v s :: 'a))) s)"
  by (simp add: struct_rewrite_expr_def struct_rewrite_modifies_def)

(* \<approx> heap_update_field.
 * We probably need this rule to generalise struct_rewrite_modifies_field. *)
lemma heap_update_field_unpacked:
  "\<lbrakk> field_ti TYPE('a::mem_type) f = Some (t :: 'a xtyp_info);
     c_guard (p :: 'a::mem_type ptr);
     export_uinfo t = export_uinfo (typ_info_t TYPE('b::mem_type)) \<rbrakk> \<Longrightarrow>
   heap_update (Ptr &(p\<rightarrow>f) :: 'b ptr) v hp =
   heap_update p (update_ti t (to_bytes_p v) (h_val hp p)) hp"
  oops

(* \<approx> heap_update_Array_element. Would want this for struct_rewrite_modifies_Array_field. *)
lemma heap_update_Array_element_unpacked:
  "n < CARD('b::array_max_count) \<Longrightarrow>
   heap_update (ptr_coerce p' +\<^sub>p int n) w hp =
   heap_update (p'::('a::array_outer_max_size['b::array_max_count]) ptr)
               (Arrays.update (h_val hp p') n w) hp"
  oops

(* helper *)
lemma read_write_valid_hrs_mem:
  "lense hrs_mem hrs_mem_update"
  by (clarsimp simp: hrs_mem_def hrs_mem_update_def lense_def)


(*
 * heap_update is a bit harder.
 * Recall that we want to rewrite
 *   "heap_update (ptr\<rightarrow>a\<rightarrow>b\<rightarrow>c) val s" to
 *   "heap_update ptr (c_update (b_update (a_update (\<lambda>_. val))) (h_val s ptr)) s".
 * In the second term, c_update is the outer update even though
 * c is the innermost field.
 *
 * We introduce a schematic update function ?u that would eventually be
 * instantiated to be the chain "\<lambda>f. c_update (b_update (a_update f))".
 * Observe that when we find another field "\<rightarrow>d", we can instantiate
 *   ?u' = \<lambda>f. ?u (d_update f)
 * so that u' is the correct update function for "ptr\<rightarrow>a\<rightarrow>b\<rightarrow>c\<rightarrow>d".
 *
 * This is a big hack because:
 *  - We rely on a particular behaviour of the unifier (see below).
 *  - We will have a chain of flex-flex pairs
 *      ?u1 =?= \<lambda>f. ?u0 (a_update f)
 *      ?u2 =?= \<lambda>f. ?u1 (b_update f)
 *      etc.
 *  - Because we are doing this transformation in steps, moving
 *    one component of "ptr\<rightarrow>a\<rightarrow>..." at a time, we end up invoking
 *    struct_rewrite_expr on the same subterms over and over again.
 * In case we find out this hack doesn't scale, we can avoid the schematic ?u
 * by traversing the chain and constructing ?u in a separate step.
 *)

(*
 * There's more. heap_update rewrites for "ptr\<rightarrow>a\<rightarrow>b := RHS" cause a
 * "h_val s ptr" to appear in the RHS.
 * When we lift to the typed heap, we want this h_val to be treated
 * differently to other "h_val s ptr" terms that were already in the RHS.
 * Thus we define heap_lift__h_val \<equiv> h_val to carry this information around.
 *)
definition "heap_lift__wrap_h_val \<equiv> (=)"

lemma heap_lift_wrap_h_val [heap_abs]:
  "heap_lift__wrap_h_val (heap_lift__h_val s p) (h_val s p)"
  by (simp add: heap_lift__h_val_def heap_lift__wrap_h_val_def)

lemma heap_lift_wrap_h_val_skip [heap_abs]:
  "heap_lift__wrap_h_val (h_val s (Ptr (field_lvalue p f))) (h_val s (Ptr (field_lvalue p f)))"
  by (simp add: heap_lift__wrap_h_val_def)

lemma heap_lift_wrap_h_val_skip_array [heap_abs]:
  "heap_lift__wrap_h_val (h_val s (ptr_coerce p +\<^sub>p k))
                         (h_val s (ptr_coerce p +\<^sub>p k))"
  by (simp add: heap_lift__wrap_h_val_def)

(* These are valid rules, but produce redundant output. *)
lemma struct_rewrite_modifies_field__unused:
  "\<lbrakk> valid_struct_field field_name (field_getter :: ('a::xmem_type) \<Rightarrow> ('f::xmem_type)) field_setter t_hrs t_hrs_update;
     struct_rewrite_expr P p' p;
     struct_rewrite_expr Q f' f;
     struct_rewrite_modifies R
       (\<lambda>s. t_hrs_update (hrs_mem_update (heap_update (p'' s)
                (u s (field_setter (\<lambda>_. f' s))))) s)
       (\<lambda>s. t_hrs_update (hrs_mem_update (heap_update (p' s)
                (field_setter (\<lambda>_. f' s) (h_val (hrs_mem (t_hrs s)) (p' s))))) s);
     struct_rewrite_guard S (\<lambda>s. c_guard (p' s)) \<rbrakk> \<Longrightarrow>
   struct_rewrite_modifies (\<lambda>s. P s \<and> Q s \<and> R s \<and> S s)
     (\<lambda>s. t_hrs_update (hrs_mem_update (heap_update (p'' s)
              (u s (field_setter (\<lambda>_. f' s))))) s)
     (\<lambda>s. t_hrs_update (hrs_mem_update (heap_update (Ptr (field_lvalue (p s) field_name))
              (f s))) s)"
  apply (clarsimp simp: struct_rewrite_expr_def struct_rewrite_guard_def struct_rewrite_modifies_def valid_struct_field_def)
  apply (erule_tac x = s in allE)+
  apply (erule impE, assumption)+
  apply (erule_tac t = "t_hrs_update (hrs_mem_update (heap_update (p'' s)
                          (u s (field_setter (\<lambda>_. f' s))))) s"
               and s = "t_hrs_update (hrs_mem_update (heap_update (p' s)
                          (field_setter (\<lambda>_. f' s) (h_val (hrs_mem (t_hrs s)) (p' s))))) s"
                in subst)
  apply (rule lense.upd_cong[where get = t_hrs and upd = t_hrs_update])
   apply assumption
  apply (rule lense.upd_cong[OF read_write_valid_hrs_mem])
  apply (subst heap_update_field_root_conv''')
     apply assumption+
   apply (simp add: typ_uinfo_t_def lense.fg_cons)
  apply (subst update_ti_update_ti_t)
   apply (simp add: size_of_def)
  apply (subst update_ti_s_adjust_ti_to_bytes_p)
   apply (erule lense.fg_cons)
  apply simp
  done

lemma struct_rewrite_modifies_Array_field__unused:
  "\<lbrakk> valid_struct_field field_name (field_getter :: ('a::xmem_type) \<Rightarrow> (('f::array_outer_max_size)['n::array_max_count])) field_setter t_hrs t_hrs_update;
     struct_rewrite_expr P p' p;
     struct_rewrite_expr Q f' f;
     struct_rewrite_modifies R
       (\<lambda>s. t_hrs_update (hrs_mem_update (heap_update (p'' s)
                (u s (field_setter (\<lambda>a. Arrays.update a (nat k) (f' s)))))) s)
       (\<lambda>s. t_hrs_update (hrs_mem_update (heap_update (p' s)
               (field_setter (\<lambda>a. Arrays.update a (nat k) (f' s))
                  (h_val (hrs_mem (t_hrs s)) (p' s))))) s);
     struct_rewrite_guard S (\<lambda>s. c_guard (p' s)) \<rbrakk> \<Longrightarrow>
   struct_rewrite_modifies (\<lambda>s. P s \<and> Q s \<and> R s \<and> S s \<and> 0 \<le> k \<and> nat k < CARD('n))
     (\<lambda>s. t_hrs_update (hrs_mem_update (heap_update (p'' s)
              (u s (field_setter (\<lambda>a. Arrays.update a (nat k) (f' s)))))) s)
     (\<lambda>s. t_hrs_update (hrs_mem_update (heap_update
            (ptr_coerce (Ptr (field_lvalue (p s) field_name) :: ('f['n]) ptr) +\<^sub>p k) (f s))) s)"
  using ptr_coerce.simps [simp del]
  apply (clarsimp simp: struct_rewrite_expr_def struct_rewrite_guard_def struct_rewrite_modifies_def valid_struct_field_def)
  subgoal for s
    apply (erule_tac x = s in allE)+
    apply (erule impE, assumption)+
    apply (erule_tac t = "t_hrs_update (hrs_mem_update (heap_update (p'' s)
                          (u s(field_setter (\<lambda>a. Arrays.update a (nat k) (f' s)))))) s"
        and s = "t_hrs_update (hrs_mem_update (heap_update (p' s)
                          (field_setter (\<lambda>a. Arrays.update a (nat k) (f' s))
                             (h_val (hrs_mem (t_hrs s)) (p' s))))) s"
        in subst)
    apply (rule lense.upd_cong[where get = t_hrs and upd = t_hrs_update])
     apply assumption
    apply (rule lense.upd_cong[OF read_write_valid_hrs_mem])
    apply (cases k, clarsimp)
     apply (subst heap_update_array_element[symmetric])
       apply assumption
      apply simp
     apply (subst heap_update_field_root_conv''')
        apply assumption+
      apply (simp add: typ_uinfo_t_def lense.fg_cons)
     apply (subst h_val_field_from_bytes')
       apply assumption+
      apply (simp add: lense.fg_cons)
     apply clarsimp
     apply (subst update_ti_update_ti_t)
      apply (simp add: size_of_def)
     apply (subst update_ti_s_adjust_ti_to_bytes_p)
      apply (erule lense.fg_cons)
     apply clarsimp
     apply (subst lense.upd_cong[of field_getter field_setter])
       apply auto
    done
  done


(*
 * These produce less redundant output (we avoid "t_update (\<lambda>_. foo (t x)) x"
 * where x is some huge term).
 * The catch: we rely on the unifier to produce a "greedy" instantiation for ?f.
 * Namely, if we are matching "?f s (h_val s p)" on
 *   "b_update (a_update (\<lambda>_. foo (h_val s p))) (h_val s p)",
 * we expect ?f to be instantiated to
 *   "\<lambda>s v. b_update (a_update (\<lambda>_. foo v)) v"
 * even though there are other valid ones.
 * It just so happens that isabelle's unifier produces such an instantiation.
 * Are we lucky, or presumptuous?
 *)
lemma struct_rewrite_modifies_field [heap_abs]:
  "\<lbrakk> valid_struct_field field_name (field_getter :: ('a::xmem_type) \<Rightarrow> ('f::xmem_type)) field_setter t_hrs t_hrs_update;
     struct_rewrite_expr P p' p;
     struct_rewrite_expr Q f' f;
     \<And>s. heap_lift__wrap_h_val (h_val_p' s) (h_val (hrs_mem (t_hrs s)) (p' s));
     struct_rewrite_modifies R
       (\<lambda>s. t_hrs_update (hrs_mem_update (heap_update (p'' s)
                (u s (field_setter (f' s))))) s)
       (\<lambda>s. t_hrs_update (hrs_mem_update (heap_update (p' s)
                (field_setter (f' s) (h_val_p' s)))) s);
     struct_rewrite_guard S (\<lambda>s. c_guard (p' s)) \<rbrakk> \<Longrightarrow>
   struct_rewrite_modifies (\<lambda>s. P s \<and> Q s \<and> R s \<and> S s)
     (\<lambda>s. t_hrs_update (hrs_mem_update (heap_update (p'' s)
              (u s (field_setter (f' s))))) s)
     (\<lambda>s. t_hrs_update (hrs_mem_update (heap_update (Ptr (field_lvalue (p s) field_name))
              (f s (h_val (hrs_mem (t_hrs s)) (Ptr (field_lvalue (p s) field_name)))))) s)"
  apply (clarsimp simp: struct_rewrite_expr_def struct_rewrite_guard_def struct_rewrite_modifies_def valid_struct_field_def heap_lift__wrap_h_val_def)
  apply (erule_tac x = s in allE)+
  apply (erule impE, assumption)+
  apply (erule_tac t = "t_hrs_update (hrs_mem_update (heap_update (p'' s)
                          (u s (field_setter (f' s))))) s"
               and s = "t_hrs_update (hrs_mem_update (heap_update (p' s)
                          (field_setter (f' s) (h_val (hrs_mem (t_hrs s)) (p' s))))) s"
                in subst)
  apply (rule lense.upd_cong[where get = t_hrs and upd = t_hrs_update])
   apply assumption
  apply (rule lense.upd_cong[OF read_write_valid_hrs_mem])
  apply (subst heap_update_field_root_conv''')
     apply assumption+
   apply (simp add: typ_uinfo_t_def lense.fg_cons)
   apply (subst h_val_field_from_bytes')
     apply assumption+
    apply (simp add: lense.fg_cons)
  apply (subst update_ti_update_ti_t)
   apply (simp add: size_of_def)
  apply (subst update_ti_s_adjust_ti_to_bytes_p)
   apply (erule lense.fg_cons)
  apply (subst lense.upd_cong[where get = field_getter and upd = field_setter])
    apply auto
  done

(* fixme: this is nearly a duplicate. Would a standalone array rule work instead? *)
lemma struct_rewrite_modifies_Array_field [heap_abs]:
  "\<lbrakk> valid_struct_field field_name (field_getter :: ('a::xmem_type) \<Rightarrow> (('f::array_outer_max_size)['n::array_max_count])) field_setter t_hrs t_hrs_update;
     struct_rewrite_expr P p' p;
     struct_rewrite_expr Q f' f;
     \<And>s. heap_lift__wrap_h_val (h_val_p' s) (h_val (hrs_mem (t_hrs s)) (p' s));
     struct_rewrite_modifies R
       (\<lambda>s. t_hrs_update (hrs_mem_update (heap_update (p'' s)
                (u s (field_setter (\<lambda>a. Arrays.update a (nat k) (f' s (index a (nat k)))))))) s)
       (\<lambda>s. t_hrs_update (hrs_mem_update (heap_update (p' s)
               (field_setter (\<lambda>a. Arrays.update a (nat k) (f' s (index a (nat k))))
                  (h_val_p' s)))) s);
     struct_rewrite_guard S (\<lambda>s. c_guard (p' s)) \<rbrakk> \<Longrightarrow>
   struct_rewrite_modifies (\<lambda>s. P s \<and> Q s \<and> R s \<and> S s \<and> 0 \<le> k \<and> nat k < CARD('n))
     (\<lambda>s. t_hrs_update (hrs_mem_update (heap_update (p'' s)
              (u s (field_setter (\<lambda>a. Arrays.update a (nat k) (f' s (index a (nat k)))))))) s)
     (\<lambda>s. t_hrs_update (hrs_mem_update (heap_update
            (ptr_coerce (Ptr (field_lvalue (p s) field_name) :: ('f['n]) ptr) +\<^sub>p k)
                (f s (h_val (hrs_mem (t_hrs s)) (ptr_coerce (Ptr (field_lvalue (p s) field_name) :: ('f['n]) ptr) +\<^sub>p k :: 'f ptr))))) s)"
  using ptr_coerce.simps[simp del]
  apply (clarsimp simp: struct_rewrite_expr_def struct_rewrite_guard_def struct_rewrite_modifies_def valid_struct_field_def heap_lift__wrap_h_val_def)
  subgoal for s
    apply (erule_tac x = s in allE)+
    apply (erule impE, assumption)+
    apply (erule_tac t = "t_hrs_update (hrs_mem_update (heap_update (p'' s)
                          (u s(field_setter (\<lambda>a. Arrays.update a (nat k) (f' s (index a (nat k)))))))) s"
        and s = "t_hrs_update (hrs_mem_update (heap_update (p' s)
                          (field_setter (\<lambda>a. Arrays.update a (nat k) (f' s (index a (nat k))))
                             (h_val (hrs_mem (t_hrs s)) (p' s))))) s"
        in subst)
    apply (rule lense.upd_cong[where get = t_hrs and upd = t_hrs_update])
     apply assumption
    apply (rule lense.upd_cong[OF read_write_valid_hrs_mem])
    apply (cases k, clarsimp)
     apply (subst heap_update_array_element[symmetric])
       apply assumption
      apply simp
     apply (subst heap_update_field_root_conv''')
        apply assumption+
      apply (simp add: typ_uinfo_t_def lense.fg_cons)
     apply (subst h_val_field_from_bytes')
       apply assumption+
      apply (simp add: lense.fg_cons)
     apply (subst heap_access_Array_element[symmetric])
      apply simp
     apply (subst h_val_field_from_bytes')
       apply assumption+
      apply (simp add: lense.fg_cons)
     apply clarsimp
     apply (subst update_ti_update_ti_t)
      apply (simp add: size_of_def)
     apply (subst update_ti_s_adjust_ti_to_bytes_p)
      apply (erule lense.fg_cons)
     apply clarsimp
     apply (subst lense.upd_cong[of field_getter field_setter])
       apply auto
    done
  done


(*
 * Convert gets/sets to global variables into gets/sets in the new globals record.
 *)

definition
  valid_globals_field :: "
     ('s \<Rightarrow> 't)
     \<Rightarrow> ('s \<Rightarrow> 'a)
     \<Rightarrow> (('a \<Rightarrow> 'a) \<Rightarrow> 's \<Rightarrow> 's)
     \<Rightarrow> ('t \<Rightarrow> 'a)
     \<Rightarrow> (('a \<Rightarrow> 'a) \<Rightarrow> 't \<Rightarrow> 't)
     \<Rightarrow> bool"
where
  "valid_globals_field st old_getter old_setter new_getter new_setter \<equiv>
    (\<forall>s. new_getter (st s) = old_getter s)
    \<and> (\<forall>s v. new_setter v (st s) = st (old_setter v s))"

lemma abs_expr_globals_getter [heap_abs]:
  "\<lbrakk> valid_globals_field st old_getter old_setter new_getter new_setter \<rbrakk>
    \<Longrightarrow> abs_expr st (\<lambda>_. True) new_getter old_getter"
  apply (clarsimp simp: valid_globals_field_def abs_expr_def)
  done

lemma abs_expr_globals_setter [heap_abs]:
  "\<lbrakk> valid_globals_field st old_getter old_setter new_getter new_setter;
     \<And>old. abs_expr st (P old) (v old) (v' old) \<rbrakk>
    \<Longrightarrow> abs_modifies st (\<lambda>s. \<forall>old. P old s) (\<lambda>s. new_setter (\<lambda>old. v old s) s) (\<lambda>s. old_setter (\<lambda>old. v' old s) s)"
  apply (clarsimp simp: valid_globals_field_def abs_expr_def abs_modifies_def)
  done

lemma struct_rewrite_expr_globals_getter [heap_abs]:
  "\<lbrakk> valid_globals_field st old_getter old_setter new_getter new_setter \<rbrakk>
    \<Longrightarrow> struct_rewrite_expr (\<lambda>_. True) old_getter old_getter"
  apply (clarsimp simp: struct_rewrite_expr_def)
  done

lemma struct_rewrite_modifies_globals_setter [heap_abs]:
  "\<lbrakk> valid_globals_field st old_getter old_setter new_getter new_setter;
     \<And>old. struct_rewrite_expr (P old) (v' old) (v old) \<rbrakk>
    \<Longrightarrow> struct_rewrite_modifies (\<lambda>s. \<forall>old. P old s) (\<lambda>s. old_setter (\<lambda>old. v' old s) s) (\<lambda>s. old_setter (\<lambda>old. v old s) s)"
  apply (clarsimp simp: valid_globals_field_def struct_rewrite_expr_def struct_rewrite_modifies_def)
  done

(* Translate Hoare modifies specs generated by the C parser.
 * A modifies spec is of the form
 *   {(s, s'). \<exists>v1 v2 ... s' = s\<lparr>field1 := v1, field2 := v2, ...\<rparr>}
 * except using mex and meq instead of \<exists> and =. *)
lemma abs_spec_may_not_modify_globals[heap_abs]:
  "abs_spec st (\<lambda>_. True) {(a, b). meq b a} {(a, b). meq b a}"
  apply (clarsimp simp: abs_spec_def meq_def)
  done

lemma abs_spec_modify_global[heap_abs]:
  "valid_globals_field st old_getter old_setter new_getter new_setter \<Longrightarrow>
   abs_spec st (\<lambda>_. True) {(a, b). C a b} {(a, b). C' a b} \<Longrightarrow>
   abs_spec st (\<lambda>_. True) {(a, b). mex (\<lambda>x. C (new_setter (\<lambda>_. x) a) b)} {(a, b). mex (\<lambda>x. C' (old_setter (\<lambda>_. x) a) b)}"
  apply (fastforce simp: abs_spec_def mex_def valid_globals_field_def)
  done
(* NB: Polish will unfold meq and mex. The reason is explained there. *)


(* Signed words are stored on the heap as unsigned words. *)

lemma uint_scast:
    "uint (scast x :: 'a word) = uint (x :: 'a::len signed word)"
  apply (subst down_cast_same [symmetric])
   apply (clarsimp simp: cast_simps)
  apply (subst uint_up_ucast)
   apply (clarsimp simp: cast_simps)
  apply simp
  done

lemma to_bytes_signed_word:
    "to_bytes (x :: 'a::len8 signed word) p = to_bytes (scast x :: 'a word) p"
  by (clarsimp simp: uint_scast to_bytes_def typ_info_word word_rsplit_def)

lemma from_bytes_signed_word:
    "length p = len_of TYPE('a) div 8 \<Longrightarrow>
           (from_bytes p :: 'a::len8 signed word) = ucast (from_bytes p :: 'a word)"
  by (clarsimp simp: from_bytes_def word_rcat_def scast_def cast_simps typ_info_word)

lemma hrs_mem_update_signed_word:
    "hrs_mem_update (heap_update (ptr_coerce p :: 'a::len8 word ptr) (scast val :: 'a::len8 word))
               = hrs_mem_update (heap_update p (val :: 'a::len8 signed word))"
  apply (rule ext)
  apply (clarsimp simp: hrs_mem_update_def split_def)
  apply (clarsimp simp: heap_update_def to_bytes_signed_word
             size_of_def typ_info_word)
  done

lemma h_val_signed_word:
    "(h_val a p :: 'a::len8 signed word) = ucast (h_val a (ptr_coerce p :: 'a word ptr))"
  apply (clarsimp simp: h_val_def)
  apply (subst from_bytes_signed_word)
   apply (clarsimp simp: size_of_def typ_info_word)
  apply (clarsimp simp: size_of_def typ_info_word)
  done


lemma align_of_signed_word:
  "align_of TYPE('a::len8 signed word) = align_of TYPE('a word)"
  by (clarsimp simp: align_of_def typ_info_word)

lemma size_of_signed_word:
  "size_of TYPE('a::len8 signed word) = size_of TYPE('a word)"
  by (clarsimp simp: size_of_def typ_info_word)

lemma c_guard_ptr_coerce:
  "\<lbrakk> align_of TYPE('a) = align_of TYPE('b);
     size_of TYPE('a) = size_of TYPE('b) \<rbrakk> \<Longrightarrow>
        c_guard (ptr_coerce p :: ('b::c_type) ptr) = c_guard (p :: ('a::c_type) ptr)"
  apply (clarsimp simp: c_guard_def ptr_aligned_def c_null_guard_def)
  done

lemma word_rsplit_signed:
    "(word_rsplit (ucast v' :: ('a::len) signed word) :: 8 word list) = word_rsplit (v' :: 'a word)"
  apply (clarsimp simp: word_rsplit_def)
  apply (clarsimp simp: cast_simps)
  done

lemma heap_update_signed_word:
    "heap_update (ptr_coerce p :: 'a word ptr) (scast v) = heap_update (p :: ('a::len8) signed word ptr) v"
    "heap_update (ptr_coerce p' :: 'a signed word ptr) (ucast v') = heap_update (p' :: ('a::len8) word ptr) v'"
  apply (auto simp: heap_update_def to_bytes_def typ_info_word word_rsplit_def cast_simps uint_scast)
  done

lemma heap_update_padding_signed_word:
    "heap_update_padding (ptr_coerce p :: 'a word ptr) (scast v) bs  = heap_update_padding (p :: ('a::len8) signed word ptr) v bs"
    "heap_update_padding (ptr_coerce p' :: 'a signed word ptr) (ucast v') bs = heap_update_padding (p' :: ('a::len8) word ptr) v' bs"
  by (auto simp: heap_update_padding_def to_bytes_def typ_info_word word_rsplit_def cast_simps uint_scast)

lemma typ_heap_simulation_c_guard:
  "\<lbrakk> typ_heap_simulation st r w v t_hrs t_hrs_update;
           v (st s) p \<rbrakk> \<Longrightarrow> c_guard p"
  by (clarsimp simp: valid_implies_cguard.valid_implies_c_guard [OF typ_heap_simulation.axioms(5)])

abbreviation (input)
  scast_f :: "(('a::len) signed word ptr \<Rightarrow> 'a signed word)
            \<Rightarrow> ('a word ptr \<Rightarrow> 'a word)"
where
  "scast_f f \<equiv> (\<lambda>p. scast (f (ptr_coerce p)))"

abbreviation (input)
  ucast_f :: "(('a::len) word ptr \<Rightarrow> 'a word)
            \<Rightarrow> ('a signed word ptr \<Rightarrow> 'a signed word)"
where
  "ucast_f f \<equiv> (\<lambda>p. ucast (f (ptr_coerce p)))"

abbreviation (input)
  cast_f' :: "('a ptr \<Rightarrow> 'x) \<Rightarrow> ('b ptr \<Rightarrow> 'x)"
where
  "cast_f' f \<equiv> (\<lambda>p. f (ptr_coerce p))"

lemma read_write_validE_weak:
  "\<lbrakk> lense r w;
      \<lbrakk> \<And>f s. r (w f s) = f (r s);
        \<And>f s. f (r s) = (r s) \<Longrightarrow> w f s = s \<rbrakk> \<Longrightarrow> R \<rbrakk>
        \<Longrightarrow> R"
  apply atomize_elim
  apply (unfold lense_def)
  apply metis
  done

lemma lense_transcode:
  "\<lbrakk> lense r w; \<And>v. f' (f v) = v; \<And>v. f (f' v) = v  \<rbrakk> \<Longrightarrow>
   lense (\<lambda>s. f' (r s)) (\<lambda>g s. w (\<lambda>old. f (g (f' old))) s)"
  apply (unfold lense_def)
  apply (simp add:comp_def)
  done


(* fixme: This is a sublocale relation.*)
lemma typ_heap_simulation_signed_word:
  notes align_of_signed_word [simp]
        size_of_signed_word [simp]
        heap_update_signed_word [simp]
  shows
  "\<lbrakk> typ_heap_simulation st
        (r :: 's \<Rightarrow> ('a::len8) word ptr  \<Rightarrow> 'a word) w
              v t_hrs t_hrs_update \<rbrakk>
    \<Longrightarrow> typ_heap_simulation st
              (\<lambda>s p. ucast (r s (ptr_coerce p)) :: 'a signed word)
              (\<lambda>p f.  (w (ptr_coerce p) ((\<lambda>x. scast (f (ucast x)))) ))
              (\<lambda>s p. v s (ptr_coerce p))
              t_hrs t_hrs_update"
  apply (clarsimp simp: typ_heap_simulation_def
          map.compositionality o_def c_guard_ptr_coerce)
  apply (intro conjI impI)
  subgoal
    apply (clarsimp simp add: read_simulation_def)
    apply (drule_tac x=s in spec)+
    apply (drule_tac x="ptr_coerce p" in spec)+
    by (simp add: h_val_signed_word)
  subgoal
    apply (clarsimp simp add: write_simulation_def write_simulation_axioms_def)
    subgoal for s p bs x
      apply (erule_tac x=s in allE)
      apply (erule_tac x="(PTR_COERCE('a signed word \<rightarrow> 'a word) p)" in allE)
      apply clarsimp
      apply (erule_tac x=bs in allE)
      apply clarsimp
      apply (erule_tac x= " SCAST('a signed \<rightarrow> 'a) x" in allE)
      using heap_update_padding_signed_word
      by (metis (mono_tags, lifting) hrs_mem_update_cong)
    done

  subgoal
    by (clarsimp simp add: write_preserves_valid_def)
  subgoal
    apply (clarsimp simp add: valid_implies_cguard_def)
    apply (drule spec, drule spec, erule (1) impE)+
    apply (subst (asm) c_guard_ptr_coerce, simp, simp)
    by blast
  subgoal
    apply (simp (no_asm_use) add: valid_only_typ_desc_dependent_def)
    by blast
  subgoal
    apply (simp (no_asm_use) add: pointer_lense_def)
    apply clarsimp
    by (metis comp_apply ucast_scast_id)
  done

lemma c_guard_ptr_ptr_coerce:
    "\<lbrakk> c_guard (a :: ('a::c_type) ptr ptr); ptr_val a = ptr_val b \<rbrakk> \<Longrightarrow>
         c_guard (b :: ('b::c_type) ptr ptr)"
  by (clarsimp simp: c_guard_def ptr_aligned_def c_null_guard_def)

abbreviation (input)
  ptr_coerce_f :: "('a ptr ptr \<Rightarrow> 'a ptr) \<Rightarrow> ('b ptr ptr \<Rightarrow> 'b ptr)"
where
  "ptr_coerce_f f \<equiv> (\<lambda>p. ptr_coerce (f (ptr_coerce p)))"

abbreviation (input)
  ptr_coerce_range_f :: "('a ptr  \<Rightarrow> bool) \<Rightarrow> ('b ptr \<Rightarrow> bool)"
where
  "ptr_coerce_range_f f \<equiv> (\<lambda>p. (f (ptr_coerce p)))"

(* fixme: this is a sublocale *)
lemma typ_heap_simulation_ptr_coerce:
  "\<lbrakk> typ_heap_simulation st
        (r :: 's \<Rightarrow> ('a::c_type) ptr ptr  \<Rightarrow> 'a ptr) w
              v t_hrs t_hrs_update \<rbrakk>
    \<Longrightarrow> typ_heap_simulation st
              (\<lambda>s p. ptr_coerce (r s (ptr_coerce p)) :: ('b::c_type) ptr)
              (\<lambda>p f.  (w (ptr_coerce p) ((\<lambda>x. ptr_coerce (f (ptr_coerce x))))))
              (\<lambda>s p. v s (ptr_coerce p))
              t_hrs t_hrs_update"
  apply (clarsimp simp: typ_heap_simulation_def fun_upd_def)
  apply (intro conjI impI)
  subgoal
    by (clarsimp simp: read_simulation_def h_val_def typ_info_ptr from_bytes_def)
  subgoal
    apply (clarsimp simp add: write_simulation_def write_simulation_axioms_def)
    apply (erule allE, erule allE, erule (1) impE)+
    apply (erule_tac x="bs" in allE)
    apply clarsimp
    apply (erule_tac x="ptr_coerce x" in allE)
    apply (clarsimp simp: heap_update_padding_def [abs_def] to_bytes_def typ_info_ptr)
    done
  subgoal
    apply (clarsimp simp add: write_preserves_valid_def)
    done
  subgoal
    apply (clarsimp simp add: valid_implies_cguard_def)
    apply (drule spec, drule spec, erule (1) impE)+
    apply (subst (asm) c_guard_ptr_coerce, simp, simp)
    by blast
  subgoal
    apply (simp (no_asm_use) add: valid_only_typ_desc_dependent_def)
    by blast
  subgoal
    apply (simp (no_asm_use) add: pointer_lense_def)
    apply clarsimp
    by (metis comp_apply ptr_coerce_id ptr_coerce_idem)
  done




(*
 * Nasty hack: Convert signed word pointers-to-pointers to word
 * pointers-to-pointers.
 *
 * The idea here is that types of the form:
 *
 *    int ***x;
 *
 * need to be converted to accesses of the "unsigned int ***" heap.
 *)
lemmas signed_typ_heap_simulations =
  typ_heap_simulation_signed_word
  typ_heap_simulation_ptr_coerce [where 'a="('x::len8) word"  and 'b="('x::len8) signed word"]
  typ_heap_simulation_ptr_coerce [where 'a="('x::len8) word ptr"  and 'b="('x::len8) signed word ptr"]
  typ_heap_simulation_ptr_coerce [where 'a="('x::len8) word ptr ptr"  and 'b="('x::len8) signed word ptr ptr"]
  typ_heap_simulation_ptr_coerce [where 'a="('x::len8) word ptr ptr ptr"  and 'b="('x::len8) signed word ptr ptr ptr"]

(*
 * The above lemmas generate a mess in its output, generating things
 * like:
 *
 * (heap_w32_update
 *    (\<lambda>a b. scast
 *            (((\<lambda>b. ucast (a (ptr_coerce b)))(a := 3))
 *              (ptr_coerce b))))
 *
 * This theorem cleans it up a little.
 *)
lemma ptr_coerce_eq:
  "(ptr_coerce x = ptr_coerce y) = (x = y)"
  by (cases x, cases y, auto)

lemma signed_word_heap_opt [L2opt]:
  "(scast (((\<lambda>x. ucast (a (ptr_coerce x))) (p := v :: 'a::len signed word)) (b :: 'a signed word ptr)))
  = ((a(ptr_coerce p := (scast v :: 'a word))) ((ptr_coerce b) :: 'a word ptr))"
  by (auto simp: fun_upd_def ptr_coerce_eq)

lemma signed_word_heap_ptr_coerce_opt [L2opt]:
  "(ptr_coerce (((\<lambda>x. ptr_coerce (a (ptr_coerce x))) (p := v :: 'a ptr)) (b :: 'a ptr ptr)))
  = ((a(ptr_coerce p := (ptr_coerce v :: 'b ptr))) ((ptr_coerce b) :: 'b ptr ptr))"
  by (auto simp: fun_upd_def ptr_coerce_eq)

declare ptr_coerce_idem [L2opt]
declare scast_ucast_id [L2opt]
declare ucast_scast_id [L2opt]

(* array rules *)
lemma heap_abs_expr_c_guard_array [heap_abs]:
  "\<lbrakk> typ_heap_simulation st r w v t_hrs t_hrs_update;
      abs_expr st P x' (\<lambda>s. ptr_coerce (x s) :: 'a ptr) \<rbrakk> \<Longrightarrow>
     abs_guard st
        (\<lambda>s. P s \<and> (\<forall>a \<in> set (array_addrs (x' s) CARD('b)). v s a))
        (\<lambda>s. c_guard (x s :: ('a::array_outer_max_size, 'b::array_max_count) array ptr))"
  apply (clarsimp simp: abs_expr_def abs_guard_def simple_lift_def root_ptr_valid_def)
  apply (subgoal_tac "\<forall>a\<in>set (array_addrs (x' (st s)) CARD('b)). c_guard a")
   apply (erule allE, erule (1) impE)
   apply (rule c_guard_array_c_guard)
   apply (subst (asm) (2) set_array_addrs)
   apply force
  apply clarsimp
  apply (erule (1) my_BallE)
  apply (drule (1) typ_heap_simulation_c_guard)
  apply simp
  done

(* begin machinery for heap_abs_array_update *)
lemma fold_over_st:
  "\<lbrakk> xs = ys; P s;
     \<And>s x. x \<in> set xs \<and> P s \<Longrightarrow> P (g x s) \<and> f x (st s) = st (g x s)
   \<rbrakk> \<Longrightarrow> fold f xs (st s) = st (fold g ys s)"
  apply (erule subst)
  apply (induct xs arbitrary: s)
   apply simp
  apply simp
  done

lemma fold_lift_write:
  "\<lbrakk> xs = ys; lense r w
   \<rbrakk> \<Longrightarrow> fold (\<lambda>i. w (f i)) xs s = w (fold f ys) s"
  apply (erule subst)
  apply (induct xs arbitrary: s)
   apply (simp add: lense.upd_same)
  apply (simp add: lense.upd_compose)
  done

(* cf. heap_update_nmem_same *)
lemma fold_heap_update_list_nmem_same:
  "\<lbrakk> n * size_of TYPE('a :: mem_type) < addr_card;
     n * size_of TYPE('a) \<le> k; k < addr_card;
     \<And>i h. length (pad i h) = size_of TYPE('a) \<rbrakk> \<Longrightarrow>
     h (ptr_val (p :: 'a ptr) + of_nat k) =
     (fold (\<lambda>i h. heap_update_list (ptr_val (p +\<^sub>p int i))
                 (to_bytes (val i h :: 'a) (pad i h)) h) [0..<n] h) (ptr_val p + of_nat k)"
  apply (induct n arbitrary: k)
   apply simp
  apply (clarsimp simp: CTypesDefs.ptr_add_def simp del: mult_Suc)
  apply (subst heap_update_nmem_same)
   apply (subst len)
    apply simp
   apply (simp add: intvl_def)
   apply (intro allI impI)
   apply (subst (asm) of_nat_mult[symmetric] of_nat_add[symmetric])+
   apply (rename_tac j)
   apply (erule_tac Q = "of_nat k = of_nat (n * size_of TYPE('a) + j)" in contrapos_pn)
   apply (subst of_nat_inj)
     apply (subst len_of_addr_card)
     apply simp
    apply (subst len_of_addr_card)
    apply simp
   apply simp
  apply simp
  done

lemma heap_list_of_disjoint_fold_heap_update_list:
  "\<lbrakk> n * size_of TYPE('a :: mem_type) < addr_card;
     n * size_of TYPE('a) + k < addr_card;
     \<And>i h. length (pad i h) = size_of TYPE('a) \<rbrakk> \<Longrightarrow>
   heap_list (fold (\<lambda>i h. heap_update_list (ptr_val ((p :: 'a ptr) +\<^sub>p int i))
                            (to_bytes (val i h :: 'a) (pad i h)) h) [0..<n] h)
             k (ptr_val (p +\<^sub>p int n))
   = heap_list h k (ptr_val (p +\<^sub>p int n))"
  apply (rule nth_equalityI, force)
  subgoal for i
    apply (clarsimp simp: heap_list_nth)
    apply (rule subst[where t = "ptr_val (p +\<^sub>p int n) + of_nat i"
        and s = "ptr_val p + of_nat (n * size_of TYPE('a) + i)"])
     apply (clarsimp simp: CTypesDefs.ptr_add_def)
    apply (rule fold_heap_update_list_nmem_same[symmetric])
       apply simp_all
    done
  done

(* remove false dependency *)
lemma fold_heap_update_list:
  "n * size_of TYPE('a :: mem_type) < 2^addr_bitsize \<Longrightarrow>
   fold (\<lambda>i h. heap_update_list (ptr_val ((p :: 'a ptr) +\<^sub>p int i))
                 (to_bytes (val i :: 'a)
                   (heap_list h (size_of TYPE('a)) (ptr_val (p +\<^sub>p int i)))) h)
        [0..<n] h =
   fold (\<lambda>i. heap_update_list (ptr_val (p +\<^sub>p int i))
               (to_bytes (val i)
                 (heap_list h (size_of TYPE('a)) (ptr_val (p +\<^sub>p int i)))))
        [0..<n] h"
  apply (induct n)
   apply simp
  apply clarsimp
  apply (subst heap_list_of_disjoint_fold_heap_update_list)
     apply (simp add: len_of_addr_card[symmetric])+
  done

(* cf. access_ti_list_array *)
lemma access_ti_list_array_unpacked:
  "\<lbrakk> \<forall>n. size_td_tuple (f n) = v3; length xs = v3 * n;
     \<forall>m xs. length xs = v3 \<and> m < n \<longrightarrow>
              access_ti_tuple (f m) (FCP g) xs = h m xs
   \<rbrakk> \<Longrightarrow>
   access_ti_list (map f [0 ..< n]) (FCP g) xs
     = foldl (@) [] (map (\<lambda>m. h m (take v3 (drop (v3 * m) xs))) [0 ..< n])"
  apply (subgoal_tac "\<forall>ys. size_td_list (map f ys) = v3 * length ys")
   prefer 2
  subgoal
    apply (rule allI)
    subgoal for ys by (induct ys) auto
    done
  apply (induct n arbitrary: xs)
   apply simp
  apply (simp add: access_ti_append)
  apply (rule foldl_cong)
    apply simp
   apply (rule map_cong[OF refl])
   apply (subst take_drop)
   apply (subst take_take)
   apply (subst min_absorb1)
    apply clarsimp
    apply (metis Suc_leI mult_Suc_right nat_mult_le_cancel_disj)
   apply (subst take_drop[symmetric])
   apply (rule refl)
  apply simp
  done

lemma concat_nth_chunk:
  "\<lbrakk> \<forall>x \<in> set xs. length (f x) = chunk; n < length xs \<rbrakk>
   \<Longrightarrow> take chunk (drop (n * chunk) (concat (map f xs))) = f (xs ! n)"
  apply (induct xs arbitrary: n, force)
  subgoal for x xs n
    apply (cases n)
     apply clarsimp
    apply clarsimp
    done
  done

(* fixme: proof should be much nicer when done within locale *)
lemma array_update_split:
  "\<lbrakk> typ_heap_simulation st (r :: 's \<Rightarrow> ('a::array_outer_max_size) ptr \<Rightarrow> 'a) w
                    v t_hrs t_hrs_update;
     \<forall>x \<in> set (array_addrs (ptr_coerce p) CARD('b::array_max_count)).
        v (st s) x
   \<rbrakk> \<Longrightarrow> st (t_hrs_update (hrs_mem_update (heap_update p (arr :: 'a['b]))) s) =
          fold (\<lambda>i. w (ptr_coerce p +\<^sub>p int i) (\<lambda>x. index arr i))
               [0 ..< CARD('b)] (st s)"
  apply (clarsimp simp: typ_heap_simulation_def heap_raw_state_def valid_implies_cguard_def read_simulation_def write_preserves_valid_def)

  apply (drule write_simulation.write_commutes_atomic)

  (* unwrap st *)
  apply (subst fold_over_st[OF refl,
           where P = "\<lambda>s. \<forall>x\<in>set (array_addrs (ptr_coerce p) CARD('b)). v (st s) x"
             and g = "\<lambda>i. t_hrs_update (hrs_mem_update (heap_update
                            (ptr_coerce p +\<^sub>p int i) (index arr i)))"])
    apply simp
  subgoal for sa x
    apply (subgoal_tac "v (st sa) (ptr_coerce p +\<^sub>p int x)")
     apply clarsimp
    apply (clarsimp simp: set_array_addrs)
    apply metis
    done
  apply (rule arg_cong[where f = st])
  apply (subst hrs_mem_update_def)+

  (* unwrap t_hrs_update *)
  apply (subst fold_lift_write[OF refl, where w = t_hrs_update])
   apply assumption
  apply (rule arg_cong[where f = "\<lambda>f. t_hrs_update f s"])
  apply (rule ext)
  apply (subst fold_lift_write[OF refl,
        where r = fst and w = "\<lambda>f s. case s of (h, z) \<Rightarrow> (f h, z)"])
   apply (simp (no_asm) add: lense_def)
  apply clarsimp

  (* split up array update *)
  apply (clarsimp simp: heap_update_def[abs_def])
  apply (subst coerce_heap_update_to_heap_updates[unfolded foldl_conv_fold,
           where chunk = "size_of TYPE('a)" and m = "CARD('b)"])
    apply (rule size_of_array[simplified mult.commute])
   apply simp

  (* remove false dependency *)
  apply (subst fold_heap_update_list[OF array_count_size])
  apply (rule fold_cong[OF refl refl])
  subgoal for a x

    apply (clarsimp simp: CTypesDefs.ptr_add_def)
    apply (rule arg_cong[where f = "heap_update_list (ptr_val p + of_nat x * of_nat (size_of TYPE('a)))"])

    apply (subst fcp_eta[where g = arr, symmetric])
    apply (clarsimp simp: to_bytes_def typ_info_array array_tag_def array_tag_n_eq simp del: fcp_eta)
    apply (subst access_ti_list_array_unpacked)
       apply clarsimp
       apply (rule refl)
      apply (simp add: size_of_def)
     apply clarsimp
     apply (rule refl)
    apply (clarsimp simp: foldl_conv_concat)

  (* we need this later *)
    apply (subgoal_tac
        "\<And>x. x < CARD('b) \<Longrightarrow>
          size_td (typ_info_t TYPE('a))
           \<le> CARD('b) * size_td (typ_info_t TYPE('a)) - size_td (typ_info_t TYPE('a)) * x")
     prefer 2
     apply (subst le_diff_conv2)
      apply simp
     apply (subst mult.commute, subst mult_Suc[symmetric])
     apply (rule mult_le_mono1)
     apply simp

    apply (subst concat_nth_chunk)
      apply clarsimp
      apply (subst fd_cons_length)
        apply simp
       apply (simp add: size_of_def)
      apply (simp add: size_of_def)
     apply simp
    apply (subst drop_heap_list_le)
     apply (simp add: size_of_def)
    apply (subst take_heap_list_le)
     apply (simp add: size_of_def)
    apply (clarsimp simp: size_of_def)
    apply (subst mult.commute, rule refl)
    done
  done

lemma fold_update_id:
  "\<lbrakk> lense getter setter;
     \<forall>i \<in> set xs. \<forall>j \<in> set xs. (i = j) = (ind i = ind j);
     \<forall>i \<in> set xs. val i = getter s (ind i)
  \<rbrakk> \<Longrightarrow> fold (\<lambda>i. setter (\<lambda>x. x(ind i := val i))) xs s = s"
  apply (induct xs)
   apply simp
  apply (rename_tac a xs)
  apply clarsimp
  apply (subgoal_tac "setter (\<lambda>x. x(ind a := getter s (ind a))) s = s")
   apply simp
  apply (subst (asm) lense_def)
  apply simp
  done

lemma fold_update_id':
  "\<lbrakk> pointer_lense r w;
     \<forall>i \<in> set xs. \<forall>j \<in> set xs. (i = j) = (ind i = ind j);
     \<forall>i \<in> set xs. val i = r s (ind i)
  \<rbrakk> \<Longrightarrow> fold (\<lambda>i. w (ind i) (\<lambda>_. val i)) xs s = s"
  apply (induct xs)
   apply simp
  apply (rename_tac a xs)
  apply clarsimp
  apply (subgoal_tac "w (ind a) (\<lambda>x. r s (ind a)) s = s")
   apply simp
  apply (subst (asm) pointer_lense_def)
  apply simp
  done

lemma array_count_index:
  "\<lbrakk> i < CARD('b::array_max_count); j < CARD('b) \<rbrakk>
   \<Longrightarrow> (i = j) =
        ((of_nat (i * size_of TYPE('a::array_outer_max_size)) :: addr)
          = of_nat (j * size_of TYPE('a)))"
  apply (rule subst[where t = "i = j" and s = "i * size_of TYPE('a) = j * size_of TYPE('a)"])
   apply clarsimp
  apply (subgoal_tac "\<And> i. i < CARD('b) \<Longrightarrow> i * size_of TYPE('a) < 2 ^ LENGTH(32)")
   apply (rule of_nat_inj[symmetric]; force)  
  apply (rule subst[where t = "len_of TYPE(addr_bitsize)" and s = addr_bitsize], force)
  apply (rule less_trans)
   apply (erule_tac b = "CARD('b)" in mult_strict_right_mono)
   apply (rule sz_nzero)
  apply (rule array_count_size)
  done


(* end machinery for heap_abs_array_update *)

lemma le_outside_intvl: "p < a \<Longrightarrow> 0 \<notin> {a ..+b} \<Longrightarrow> p \<notin> {a ..+b}"
  apply (clarsimp simp: intvl_def not_le not_less)
  by (metis Word_Lemmas_Internal.word_wrap_of_natD add_increasing2 le0 le_iff_add less_le not_less)

lemma intvl_mult_split:
  "{p ..+ a * b} = (\<Union>i<b. {p + of_nat (i * a) ..+ a})"
proof cases
  assume a: "0 < a"
  note of_nat_add[simp del, symmetric, simp] of_nat_mult[simp del, symmetric, simp]
  show ?thesis using a
    apply (clarsimp simp: intvl_def, intro set_eqI iffI; clarsimp)
    subgoal for i
      by (intro bexI[of _ "i div a"] exI[of _ "i mod a"])
         (simp_all add: dme pos_mod_bound less_mult_imp_div_less ac_simps)
    subgoal for j k
      by (intro exI[of _ "j * a + k"]) (simp add: nat_index_bound)
    done
qed simp

lemma intvl_mul_disjnt:
  fixes n i :: "'a::len word"
  assumes n: "unat n < b" and i: "unat i < b" and b: "sz * b \<le> 2^LENGTH('a)"
  assumes ni: "n \<noteq> i"
  shows "{n * word_of_nat sz..+sz} \<inter> {i * word_of_nat sz..+sz} = {}"
proof -
  { fix j l assume j: "j < sz" and l: "l < sz"
    assume "n * word_of_nat sz + word_of_nat j = i * word_of_nat sz + word_of_nat l"
    then have "(word_of_nat (unat n * sz + j) :: 'a word) = word_of_nat (unat i * sz + l)" by simp
    moreover have "unat n * sz + j < 2^LENGTH('a)"
      by (intro less_le_trans[OF nat_index_bound b] n j)
    moreover have "unat i * sz + l < 2^LENGTH('a)"
      by (intro less_le_trans[OF nat_index_bound b] i l)
    ultimately have "(unat n * sz + j) div sz = (unat i * sz + l) div sz"
      by (subst (asm) of_nat_inj) simp_all
    then have "unat n = unat i"
      using j l by simp
    with ni have False by simp }
  then show ?thesis
    by (auto simp: intvl_def)
qed

lemma array_disj_helper:
  fixes p :: "('a::mem_type['b]) ptr"
  assumes ni: "n < CARD('b)" "i < CARD('b)" "n \<noteq> i"
  assumes valid: "\<forall>x\<in>set (array_addrs (PTR_COERCE('a['b] \<rightarrow> 'a) p) CARD('b)). c_guard x"
  shows "{ptr_val p + word_of_nat n * word_of_nat (size_of TYPE('a))..+size_of TYPE('a)} \<inter>
    {ptr_val p + word_of_nat i * word_of_nat (size_of TYPE('a))..+size_of TYPE('a)} = {}"
proof -
  have [arith]: "CARD('b) \<le> size_of TYPE('a) * CARD('b)"
    using sz_nzero[where 'a='a, arith] by simp

  have "0 \<notin> (\<Union>b<CARD('b). {ptr_val p + of_nat (b * size_of TYPE('a)) ..+ size_of TYPE('a)})"
    using valid
    apply (clarsimp simp: set_array_addrs c_guard_def c_null_guard_def)
    subgoal premises prems for b
      using prems(2-) prems(1)[rule_format, OF exI, of
        "Ptr (ptr_val p + word_of_nat b * word_of_nat (size_of TYPE('a)))" b]
      by (simp add: ptr_add_def)
    done
  then have "0 \<notin> {ptr_val p ..+ size_of TYPE('a) * CARD('b)}"
    unfolding intvl_mult_split .
  from zero_not_in_intvl_no_overflow[OF this]
  have "size_of TYPE('a) * CARD('b) \<le> addr_card"
    by (simp add: addr_card)
  moreover note ni
  ultimately show ?thesis
    by (smt (verit, ccfv_SIG) \<open>CARD('b) \<le> size_of TYPE('a) * CARD('b)\<close> addr_card_len_of_conv
        intvl_disj_offset intvl_mul_disjnt order_less_le_trans unat_of_nat_len)
qed



theorem heap_abs_array_update [heap_abs]:
 "\<lbrakk> typ_heap_simulation st (r :: 's \<Rightarrow> 'a ptr \<Rightarrow> 'a) w
                   v t_hrs t_hrs_update;
    abs_expr st Pb b' b;
    abs_expr st Pn n' n;
    abs_expr st Pv y' y
  \<rbrakk> \<Longrightarrow>
    abs_modifies st (\<lambda>s. Pb s \<and> Pn s \<and> Pv s \<and> n' s < CARD('b) \<and>
                         (\<forall>ptr \<in> set (array_addrs (ptr_coerce (b' s)) CARD('b)). (v s ptr)))
      (\<lambda>s. w (ptr_coerce (b' s) +\<^sub>p int (n' s)) (\<lambda>v. y' s)  s)
      (\<lambda>s. t_hrs_update (hrs_mem_update (
              heap_update (b s) (Arrays.update ((h_val (hrs_mem (t_hrs s)) (b s))
                                 :: ('a::array_outer_max_size)['b::array_max_count]) (n s) (y s)))) s)"
  apply (clarsimp simp: abs_modifies_def abs_expr_def)
  subgoal for s
  (* rewrite heap_update of array *)
    apply (subst array_update_split
        [where st = st and t_hrs = t_hrs and t_hrs_update = t_hrs_update])
      apply assumption
     apply assumption
    apply (clarsimp simp: typ_heap_simulation_def valid_implies_cguard_def read_simulation_def write_preserves_valid_def)
    apply (drule write_simulation.write_commutes_atomic)
    apply (subst fold_cong[OF refl refl,
          where g = "\<lambda>i. w  (ptr_coerce (b' (st s)) +\<^sub>p int i) (\<lambda>x.
                         if i = n' (st s) then y' (st s) else r (st s) (ptr_coerce (b' (st s)) +\<^sub>p int i))"])
    subgoal for x 
      apply (cases "x = n' (st s)")
       apply simp
      apply (subst index_update2)
        apply simp
       apply simp
      apply (rule arg_cong[where x = "index (h_val (hrs_mem (t_hrs s)) (b' (st s))) x"])
      apply (subst heap_access_Array_element)
       apply simp
      apply (clarsimp simp: set_array_addrs)
      apply metis
      done

(* split away the indices that don't change *)
    apply (subst split_upt_on_n[where n = "n s"])
     apply simp
    apply clarsimp
    thm fold_update_id

(* [0..<n] doesn't change *)
    apply (subst fold_update_id'[where s = "st s"])
       apply assumption
      apply (clarsimp simp: CTypesDefs.ptr_add_def)
      apply (subst of_nat_mult[symmetric])+
      apply (rule array_count_index)
       apply (erule less_trans, assumption)+
     apply clarsimp

(* [Suc n..<CARD('b)] doesn't change *)
    apply (subst fold_update_id')
       apply assumption
      apply (clarsimp simp: CTypesDefs.ptr_add_def)
      apply (subst of_nat_mult[symmetric])+
      apply (erule array_count_index)
      apply assumption
     apply clarsimp
      (* index n is disjoint *)
     apply (subst pointer_lense.read_write_other[where r = r and w = w])
       apply assumption
      apply (clarsimp simp: CTypesDefs.ptr_add_def disjnt_def)
      apply (rule array_disj_helper)
         apply simp
        apply assumption
       apply simp
      apply blast
     apply (rule refl)
    apply (rule refl)
    done
  done



(* Array access, which is considerably simpler than updating. *)
lemma heap_abs_array_access[heap_abs]:
 "\<lbrakk> typ_heap_simulation st (r :: 's \<Rightarrow> ('a::xmem_type) ptr \<Rightarrow> 'a) w
                   v t_hrs t_hrs_update;
    abs_expr st Pb b' b;
    abs_expr st Pn n' n
  \<rbrakk> \<Longrightarrow>
    abs_expr st (\<lambda>s. Pb s \<and> Pn s \<and> n' s < CARD('b::finite) \<and> v s (ptr_coerce (b' s) +\<^sub>p int (n' s)))
      (\<lambda>s. r s (ptr_coerce (b' s) +\<^sub>p int (n' s)))
      (\<lambda>s. index (h_val (hrs_mem (t_hrs s)) (b s :: ('a['b]) ptr)) (n s))"
  apply (clarsimp simp: typ_heap_simulation_def abs_expr_def valid_implies_cguard_def read_simulation_def write_simulation_def write_preserves_valid_def)
  apply (subst heap_access_Array_element)
   apply simp
  apply (simp add: set_array_addrs)
  done


lemma the_fun_upd_lemma1:
    "(\<lambda>x. the (f x))(p := v) = (\<lambda>x. the ((f (p := Some v)) x))"
  by auto

lemma the_fun_upd_lemma2:
   "\<exists>z. f p = Some z \<Longrightarrow>
       (\<lambda>x. \<exists>z. (f (p := Some v)) x = Some z) =  (\<lambda>x. \<exists>z. f x = Some z) "
  by auto

lemma the_fun_upd_lemma3:
    "((\<lambda>x. the (f x))(p := v)) x = the ((f (p := Some v)) x)"
  by simp

lemma the_fun_upd_lemma4:
   "\<exists>z. f p = Some z \<Longrightarrow>
       (\<exists>z. (f (p := Some v)) x = Some z) =  (\<exists>z. f x = Some z) "
  by simp

lemmas the_fun_upd_lemmas =
    the_fun_upd_lemma1
    the_fun_upd_lemma2
    the_fun_upd_lemma3
    the_fun_upd_lemma4


(* Used by heap_abs_syntax to simplify signed word updates. *)
lemma sword_update:
"\<And>ptr :: ('a :: len) signed word ptr.
   (\<lambda>(x :: 'a word ptr \<Rightarrow> 'a word) p :: 'a word ptr.
     if ptr_coerce p = ptr then scast (n :: 'a signed word) else x (ptr_coerce p))
    =
   (\<lambda>(old :: 'a word ptr \<Rightarrow> 'a word) x :: 'a word ptr.
     if x = ptr_coerce ptr then scast n else old x)"
  by force

text \<open>Proof taken from @{thm LemmaBucket_C.heap_update_Array_update}\<close>
lemma (in array_outer_max_size) array_index_unat_conv:
  assumes x_bound: "x < CARD('b::array_max_count)"
  assumes k_bound: "k < size_of TYPE('a)"
  shows "unat (of_nat x * of_nat (size_of TYPE('a)) + (of_nat k :: addr))
                 = x * size_of TYPE('a) + k"
proof -
  have size: "CARD('b) * size_of TYPE('a ) < 2 ^ addr_bitsize"
    using array_count_size  by blast
  show ?thesis
    using size x_bound k_bound
    apply (cases "size_of TYPE('a)", simp_all)
    apply (cases "CARD('b)", simp_all)
    apply (subst unat_add_lem[THEN iffD1])
     apply (simp add: unat_word_ariths unat_of_nat less_Suc_eq_le)
     apply (subgoal_tac "Suc x * size_of TYPE('a) < 2 ^ addr_bitsize", simp_all)
     apply (erule order_le_less_trans[rotated], simp add: add_mono)
    apply (subst unat_mult_lem[THEN iffD1])
     apply (simp add: unat_of_nat unat_add_lem[THEN iffD1])
     apply (rule order_less_le_trans, erule order_le_less_trans[rotated],
            rule add_mono, simp+)
      apply (simp add: less_Suc_eq_le trans_le_add2)
     apply simp
    apply (simp add: unat_of_nat unat_add_lem[THEN iffD1])
    done
qed

lemma ptr_span_array_index_disj:
  fixes p::"('a::array_outer_max_size['b::array_max_count]) ptr"
  assumes n_bound: "n < CARD ('b)"
  assumes i_bound: "i < n"
  shows "disjnt (ptr_span (array_ptr_index p False n)) (ptr_span (array_ptr_index p False i))"
  using n_bound i_bound
  apply (clarsimp simp add: array_ptr_index_def ptr_add_def intvl_def disjnt_def)
  apply (intro set_eqI)
  apply clarsimp
  apply (drule word_unat.Rep_inject[THEN iffD2])
  apply (clarsimp simp: array_index_unat_conv [where 'b='b] nat_eq_add_iff1)
  by (metis mult.commute nat_index_bound not_add_less1)

lemma ptr_span_array_ptr_index_disj:
  fixes p::"('a::array_outer_max_size['b::array_max_count]) ptr"
  fixes q::"('a['b::array_max_count]) ptr"
  assumes n_bound: "n < CARD ('b)"
  assumes m_bound: "m < CARD ('b)"
  assumes disj:"disjnt (ptr_span p) (ptr_span q)"
  shows "disjnt (ptr_span (array_ptr_index p False n)) (ptr_span (array_ptr_index q False m))"
proof (rule ccontr)
  assume "\<not>disjnt (ptr_span (array_ptr_index p False n)) (ptr_span (array_ptr_index q False m))"

  then obtain k k' where
    k_bound: "k < size_of TYPE('a)" and
    k'_bound: "k' < size_of TYPE('a)" and
    eq: "ptr_val p + word_of_nat n * word_of_nat (size_of TYPE('a)) + word_of_nat k =
         ptr_val q + word_of_nat m * word_of_nat (size_of TYPE('a)) + word_of_nat k'"
    by (auto simp add: intvl_def array_ptr_index_def ptr_add_def disjnt_def)

  define i where "i = unat ((word_of_nat n::addr) * word_of_nat (size_of TYPE('a)) + word_of_nat k)"
  have i_bound: "i < CARD('b) * size_of TYPE('a)"
    using n_bound k_bound
    by(simp add: i_def array_index_unat_conv [OF n_bound k_bound]  mult.commute nat_index_bound)

  define j where "j = unat ((word_of_nat m::addr) * word_of_nat (size_of TYPE('a)) + word_of_nat k')"
  have j_bound: "j < CARD('b) * size_of TYPE('a)"
    using m_bound k'_bound
    by(simp add: j_def array_index_unat_conv [OF m_bound k'_bound]  mult.commute nat_index_bound)

  from i_bound j_bound disj have "ptr_val p + word_of_nat i \<noteq> ptr_val q + word_of_nat j"
    by (auto simp add: intvl_def disjnt_def)
  with eq show False
    by (simp add: i_def j_def add.commute add.left_commute)
qed

named_theorems select_conv and select_conv_independent and valid_conv and valid_array_conv and
  gen_update_commute and gen_outer_update_commute and update_commute

locale pointer_array_lense = pointer_lense r w
  for r:: "'s \<Rightarrow> 'a:: array_outer_max_size ptr \<Rightarrow> 'a"
  and w:: "'a ptr \<Rightarrow> ('a \<Rightarrow> 'a) \<Rightarrow> 's \<Rightarrow> 's"
begin

definition heap_array  ::"'s \<Rightarrow> ('a['b::array_max_count]) ptr \<Rightarrow> 'a['b]"  where
"heap_array s p = FCP (\<lambda>i. r s (array_ptr_index p False i))"

lemmas [read_stack_byte_ZERO_step_subst] = heap_array_def

definition heap_array_map :: "('a['b]) ptr \<Rightarrow> ('a['b::array_max_count] \<Rightarrow> 'a['b]) \<Rightarrow>  's \<Rightarrow> 's" where
"heap_array_map p f s \<equiv>
  fold (\<lambda>i. w (array_ptr_index p False i) (\<lambda>_. (f (heap_array s p)).[i])) [0..<CARD('b)] s"

lemma element_heap_eq_heap_array_eq [select_conv]: "r s = r s' \<Longrightarrow> heap_array s = heap_array s'"
  apply (rule ext)
  apply (simp add: heap_array_def)
  done

lemma fold_write_independent_field:
  fixes p::"('a['b::array_max_count]) ptr"
  assumes field_independent: "(\<And>p x s. f (w p (\<lambda>_. x) s) = f s)"
  assumes n_bound: "n \<le> CARD('b)"
  shows "f (fold (\<lambda>i. w (array_ptr_index p False i) (\<lambda>_. g (heap_array s p).[i])) [0..<n] t) = f t"
  using n_bound
proof (induct n arbitrary: t)
  case 0
  then show ?case by simp
next
  case (Suc n)
  then show ?case using field_independent
    by simp
qed


lemma heap_array_map_independent_field [select_conv_independent]:
  assumes field_independent: "(\<And>p x s. f (w p (\<lambda>_. x) s) = f s)"
  shows "f (heap_array_map p g s) = f s"
  apply (simp add: heap_array_map_def)
  apply (rule fold_write_independent_field)
   apply (rule field_independent)
  apply simp
  done

lemma fold_write_independent_field_upd_commute:
  fixes p::"('a['b::array_max_count]) ptr"
  assumes write_commute: "\<And>p x s. (f_upd (w p (\<lambda>_. x) s)) = w p (\<lambda>_. x) (f_upd s)"
  assumes n_bound: "n \<le> CARD('b)"
  shows "f_upd (fold (\<lambda>i. w (array_ptr_index p False i) (\<lambda>_. g (heap_array s p).[i])) [0..<n] t) =
          fold (\<lambda>i. w  (array_ptr_index p False i) (\<lambda>_. g (heap_array s p).[i])) [0..<n] (f_upd t)"
  using n_bound
proof (induct n arbitrary: t)
  case 0
  then show ?case by simp
next
  case (Suc n)
  then show ?case using write_commute
    by simp
qed

lemma heap_array_map_independent_field_commute [gen_update_commute]:
  assumes read_independent: "\<And>s. r (f_upd s) = r s"
  assumes write_independent: "\<And>p x s. (f_upd (w p (\<lambda>_. x) s)) = w p (\<lambda>_. x) (f_upd s)"
  shows "f_upd (heap_array_map p g s) = (heap_array_map p g (f_upd s))"
  apply (simp add: heap_array_map_def element_heap_eq_heap_array_eq [OF read_independent])
  apply (rule fold_write_independent_field_upd_commute)
  apply (rule write_independent)
  apply simp
  done

lemma heap_array_index[simp]: "i < CARD('b) \<Longrightarrow>
  heap_array s (p::('a['b::array_max_count]) ptr).[i] = r s (array_ptr_index p False i)"
  by (simp add: heap_array_def)

lemma read_write_same_fold_aux:
  fixes p::"('a['b::array_max_count]) ptr"
  assumes n_bound: "n \<le> CARD ('b)"
  assumes i_bound: "i < n"
  shows "r (fold (\<lambda>i. w (array_ptr_index p False i) (\<lambda>_. f (heap_array s p).[i])) [0..<n] s) (array_ptr_index p False i) = f (heap_array s p).[i]"
  using n_bound i_bound
proof (induct n arbitrary: i s)
  case 0
  then show ?case by simp
next
  case (Suc n)
  from Suc.prems obtain i_bound: "i < Suc n" and Suc_n_bound: "Suc n \<le> CARD ('b)" and
    n_bound: "n \<le> CARD('b)" and n_bound': "n < CARD('b)" by auto
  have size: "CARD('b) * size_of TYPE('a ) < 2 ^ addr_bitsize"
    using Padding_Equivalence.array_count_size by blast
  show ?case
  proof (cases "i=n")
    case True
    show ?thesis
      apply (simp add: True)
      apply (simp add: read_write_same)
      done
  next
    case False
    from False i_bound have i_bound': "i < n" by simp
    have disj: "disjnt (ptr_span (array_ptr_index p False n)) (ptr_span (array_ptr_index p False i))"
      by (rule ptr_span_array_index_disj [OF n_bound' i_bound'])
    show ?thesis
      apply (simp add: False)
      apply (simp add: read_write_other disj )
      apply (rule Suc.hyps [OF n_bound i_bound'])
      done
  qed
qed

lemma array_read_write_same: "heap_array (heap_array_map p f s) p = f (heap_array s p)"
  apply (subst cart_eq )
  apply clarsimp
  apply (simp add: heap_array_map_def)
  apply (rule read_write_same_fold_aux)
  by simp_all

lemma read_write_other_fold_aux:
  fixes p::"('a['b::array_max_count]) ptr"
  fixes p'::"('a['b::array_max_count]) ptr"
  assumes n_bound: "n \<le> CARD ('b)"
  assumes i_bound: "i < CARD ('b)"
  assumes disj:"disjnt (ptr_span p) (ptr_span p')"
  shows "r (fold (\<lambda>i. w (array_ptr_index p False i) (\<lambda>_. f (heap_array s p).[i])) [0..<n] s) (array_ptr_index p' False i) =
         r s (array_ptr_index p' False i)"
  using n_bound i_bound
proof (induct n arbitrary: i s)
  case 0
  then show ?case by simp
next
  case (Suc n)
  from Suc.prems obtain  Suc_n_bound: "Suc n \<le> CARD ('b)" and
    n_bound: "n \<le> CARD('b)" and n_bound': "n < CARD('b)" and
    i_bound: "i < CARD('b)" by auto
  have size: "CARD('b) * size_of TYPE('a ) < 2 ^ addr_bitsize"
    using Padding_Equivalence.array_count_size by blast

  from ptr_span_array_ptr_index_disj [OF n_bound' i_bound disj]
  show ?case
    apply (simp add: read_write_other)
    apply (rule Suc.hyps [OF n_bound i_bound])
    done
qed

lemma array_read_write_other:
  fixes p::"('a['b::array_max_count]) ptr"
  fixes p'::"('a['b::array_max_count]) ptr"
  assumes disj:"disjnt (ptr_span p) (ptr_span p')"
  shows "heap_array (heap_array_map p f s) p' = heap_array s p'"
  apply (subst cart_eq )
  apply clarsimp
  apply (simp add: heap_array_map_def)
  apply (rule read_write_other_fold_aux [OF _ _ disj])
  by simp_all

lemma write_cong_fold_aux:
  fixes p::"('a['b::array_max_count]) ptr"
  assumes f_f': "f (heap_array s p) = f' (heap_array s p)"
  assumes n_bound: "n \<le> CARD('b)"
  shows "fold (\<lambda>i. w (array_ptr_index p False i) (\<lambda>_. f (heap_array s p).[i])) [0..<n] s =
    fold (\<lambda>i. w (array_ptr_index p False i) (\<lambda>_. f' (heap_array s p).[i])) [0..<n] s"
  using n_bound
proof (induct n arbitrary:)
  case 0
  then show ?case by simp
next
  case (Suc n)
  have suc_n_bound: "Suc n \<le> CARD('b)" using Suc.prems .

  define s' where "s' = (fold (\<lambda>i. w (array_ptr_index p False i) (\<lambda>_. f' (heap_array s p).[i])) [0..<n] s)"

  from f_f' suc_n_bound
  have "(\<lambda>_. f (heap_array s p).[n]) =  (\<lambda>_. f' (heap_array s p).[n])"
    by auto
  hence eq: "(\<lambda>_. f (heap_array s p).[n]) (r s' (array_ptr_index p False n)) =
            (\<lambda>_. f' (heap_array s p).[n]) (r s' (array_ptr_index p False n))" by metis
  from Suc show ?case by (simp add: write_cong [OF eq])
qed


lemma array_write_cong:
  fixes p::"('a['b::array_max_count]) ptr"
  assumes eq: "f (heap_array s p) = f' (heap_array s p)"
  shows "heap_array_map p f s = heap_array_map p f' s"
  apply (simp add: heap_array_map_def)
  apply (rule write_cong_fold_aux)
  apply (rule eq)
  apply simp
  done

lemma array_write_same_triv[simp]:
  fixes p::"('a['b::array_max_count]) ptr"
  shows "heap_array_map p (\<lambda>_. f (heap_array s p)) s = heap_array_map p f s"
  using array_write_cong by fastforce

lemma array_write_fold_same_aux:
  fixes p::"('a['b::array_max_count]) ptr"
  assumes f_id: "f (heap_array s p) = heap_array s p"
  assumes n_bound: "n \<le> CARD('b)"
  shows "fold (\<lambda>i. w (array_ptr_index p False i) (\<lambda>_. f (heap_array s p).[i])) [0..<n] s = s"
  using n_bound
proof (induct n)
  case 0
  then show ?case by simp
next
  case (Suc n)
  from Suc.prems f_id
  have f_n_id: "f (heap_array s p).[n] = r s (array_ptr_index p False n)"
    by simp
  from Suc show ?case
    by (simp add: write_same f_n_id)
qed

lemma array_write_same:
  fixes p::"('a['b::array_max_count]) ptr"
  assumes f_id: "f (heap_array s p) = heap_array s p"
  shows "heap_array_map p f s = s"
  apply (simp add: heap_array_map_def)
  apply (rule array_write_fold_same_aux)
   apply (rule f_id)
  by simp

lemma array_write_triv [simp]:
  fixes p::"('a['b::array_max_count]) ptr"
  shows "heap_array_map p (\<lambda>_. heap_array s p) s = s" and "heap_array_map p (\<lambda>x. x) s = s"
  by (simp_all add: array_write_same)



lemma write_fold_other_commute:
  fixes p::"nat \<Rightarrow> 'a ptr"
  and q:: "'a ptr"
assumes disj: "\<And>i. i < n \<Longrightarrow> disjnt (ptr_span q) (ptr_span (p i))"
  shows
  "w q f  (fold (\<lambda>i. w (p i) (g i)) [0..<n] s) =
   fold (\<lambda>i. w (p i) (g i) ) [0..<n] (w q f s)"
  using disj
proof (induct n arbitrary: s)
  case 0
  then show ?case by simp
next
  case (Suc n)
  from Suc.prems obtain
    q_n_disj: "disjnt (ptr_span q) (ptr_span (p n))" and
    disj': "\<And>i. i < n \<Longrightarrow> disjnt (ptr_span q) (ptr_span (p i))" by auto

  note n_commute =  write_other_commute[OF q_n_disj, symmetric]
  show ?case
    apply simp
    apply (subst n_commute)
    apply (subst Suc.hyps [OF disj'])
    apply (simp_all)
    done
qed

lemma write_fold_arr_commute:
  fixes p::"('a['b::array_max_count]) ptr"
  and arr:: "'a['b::array_max_count]"
assumes n_bound: "n < CARD('b)"
  shows
  "w (array_ptr_index p False n) (\<lambda>_. arr.[n])
    (fold (\<lambda>i. w (array_ptr_index p False i) (\<lambda>_. arr.[i]))
       [0..<n] s) =
   fold
       (\<lambda>i. w (array_ptr_index p False i) (\<lambda>_. arr.[i]))
       [0..<n] ( w (array_ptr_index p False n)  (\<lambda>_. arr.[n]) s)"
  apply (rule write_fold_other_commute)
  using n_bound
  by (simp add: ptr_span_array_index_disj)



lemma array_fold_fuse_aux:
  fixes p::"('a['b::array_max_count]) ptr"
  fixes f::"'a['b] \<Rightarrow> 'a['b]"
  fixes g::"'a['b] \<Rightarrow> 'a['b]"
  assumes n_bound: "n \<le> CARD('b)"
  shows "fold
     (\<lambda>i. w (array_ptr_index p False i) (\<lambda>_. f (g (heap_array s p)).[i]))
     [0..<n]
     (fold
       (\<lambda>i. w (array_ptr_index p False i) (\<lambda>_. g (heap_array s p).[i]))
       [0..<n] t) =
    fold
     (\<lambda>i. w (array_ptr_index p False i) (\<lambda>_. f (g (heap_array s p)).[i]))
     [0..<n] t"
  using n_bound
proof (induct n arbitrary: t)
  case 0
  then show ?case by simp
next
  case (Suc n)
  from Suc.prems have n_bound: "n \<le> CARD('b)" and n_bound': "n < CARD('b)"
    by auto
    show ?case
      apply (simp add: )

      apply (subst (2) write_fold_arr_commute [OF n_bound'])
      apply (subst Suc.hyps [OF n_bound])
      apply (subst  write_fold_arr_commute [OF n_bound'])
      apply (subst write_comp)
      apply (subst (1) write_fold_arr_commute [OF n_bound'])
      by (meson comp_apply)
qed




lemma array_write_comp:
  fixes p::"('a['b::array_max_count]) ptr"
  shows "heap_array_map p f (heap_array_map p g s) = heap_array_map p (f o g) s"
proof -
  from  array_read_write_same [of p g s]
  have g_eq: "heap_array (heap_array_map p g s) p = g (heap_array s p)".
  show ?thesis
    apply (subst (1 3) heap_array_map_def)
    apply (simp add: g_eq)
    apply (subst (1) heap_array_map_def)
    apply (rule array_fold_fuse_aux)
    by simp
qed

lemma fold_fold_other_commute:
  fixes p::"nat \<Rightarrow> 'a ptr"
  and q:: "nat \<Rightarrow> 'a ptr"
assumes disj: "\<And>i j. i < n \<Longrightarrow> j < m \<Longrightarrow> disjnt (ptr_span (p i)) (ptr_span (q j))"
  shows
  "fold (\<lambda>i. w (p i) (f i)) [0..<n] (fold (\<lambda>i. w (q i) (g i)) [0..<m] s) =
   fold (\<lambda>i. w (q i) (g i)) [0..<m] (fold (\<lambda>i. w (p i) (f i)) [0..<n] s)"
  using disj
proof (induct n arbitrary: m s)
  case 0
  then show ?case by simp
next
  case (Suc n)
  from Suc.prems obtain
    disj': "\<And>i j. i < n \<Longrightarrow> j < m \<Longrightarrow> disjnt (ptr_span (p i)) (ptr_span (q j))" and
    m_disj: "\<And>j. j < m \<Longrightarrow> disjnt (ptr_span (p n)) (ptr_span (q j))"  by auto
  show ?case
    apply simp
    apply (subst  write_fold_other_commute [OF m_disj, symmetric])
    apply assumption
    apply (subst Suc.hyps [OF disj'])
      apply assumption
     apply assumption
    apply (rule refl)
    done
qed


lemma array_write_other_commute:
  fixes p::"('a['b::array_max_count]) ptr"
  fixes q::"('a['b::array_max_count]) ptr"
  assumes disj: "disjnt (ptr_span p) (ptr_span q)"
  shows "heap_array_map q g (heap_array_map p f s) = heap_array_map p f (heap_array_map q g s)"
proof -
  from array_read_write_other [OF disj]
  have g_eq: "g (heap_array (heap_array_map p f s) q) = g (heap_array s q)" by simp

  from  array_read_write_other disj
  have f_eq: "f (heap_array (heap_array_map q g s) p) = f (heap_array s p)"
    by (metis Int_commute disjnt_def)

  show ?thesis
    apply (subst (1 3) heap_array_map_def)
    apply (simp add: g_eq f_eq)
    apply (simp add: heap_array_map_def)
    apply (rule fold_fold_other_commute)
    using disj
    by (metis Int_commute ptr_span_array_ptr_index_disj disjnt_def)
qed

sublocale array: pointer_lense heap_array heap_array_map
  apply (unfold_locales)
      apply (rule array_read_write_same)
    apply (rule array_write_same, assumption)
   apply (rule array_write_comp)
  apply (rule array_write_other_commute, assumption)
  done

end

locale pointer_two_dimensional_array_lense = pointer_array_lense r w
  for r:: "'s \<Rightarrow> 'a:: array_inner_max_size ptr \<Rightarrow> 'a"
  and w:: "'a ptr \<Rightarrow> ('a \<Rightarrow> 'a) \<Rightarrow> 's \<Rightarrow> 's"
begin
sublocale outer: pointer_array_lense heap_array heap_array_map
  by (intro_locales)

lemmas outer.heap_array_map_independent_field_commute [gen_outer_update_commute]

end

locale valid_array_base =
  fixes vgetter:: "('t \<Rightarrow> 'a::array_outer_max_size ptr \<Rightarrow> bool)"
begin

definition valid_array ::"'t \<Rightarrow> ('a['b::array_max_count]) ptr \<Rightarrow> bool" where
 [valid_array_defs]: "valid_array s p = (\<forall>i < CARD('b). vgetter s (array_ptr_index p False i))"

lemma element_vgetter_eq_valid_array_eq [valid_array_conv]: "vgetter s = vgetter s' \<Longrightarrow> valid_array s = valid_array s'"
  apply (rule ext)
  apply (simp add: valid_array_def)
  done

end

locale valid_pointer_array_lense = pointer_array_lense r w +
  valid_array_base vgetter +
  write_preserves_valid vgetter w
  for r:: "'s \<Rightarrow> 'a:: array_outer_max_size ptr \<Rightarrow> 'a"
  and w:: "'a ptr \<Rightarrow> ('a \<Rightarrow> 'a) \<Rightarrow> 's \<Rightarrow> 's"
  and vgetter:: "('s \<Rightarrow> 'a ptr \<Rightarrow> bool)"
begin

lemma setter_fold_keeps_vgetter:
  fixes p':: "('a['b::array_max_count]) ptr"
  fixes p:: "'a ptr"
  assumes n_bound: "n \<le> CARD('b)"
  shows  "vgetter (fold (\<lambda>i. w (array_ptr_index p' False i) (\<lambda>_. f (heap_array s p').[i])) [0..<n] s) p = vgetter s p"
  using n_bound
proof (induct n arbitrary: s)
  case 0
  then show ?case by (simp )
next
  case (Suc n)
  from Suc.prems obtain
    suc_n_bound: "Suc n \<le> CARD('b)" and
    n_bound: "n \<le> CARD('b)" by auto
  show ?case
    apply simp
    apply (rule Suc.hyps [OF n_bound])
    done
qed

lemma heap_array_map_keeps_vgetter:
  fixes p:: "('a['b::array_max_count]) ptr"
  fixes p':: "('a['b]) ptr"
  shows "valid_array (heap_array_map p' f s) p = valid_array s p"
  by (clarsimp simp add: valid_array_def heap_array_map_def setter_fold_keeps_vgetter)

sublocale array: write_preserves_valid valid_array heap_array_map
  apply (unfold_locales)
  apply (rule heap_array_map_keeps_vgetter)
  done

lemma heap_array_map_keeps_vgetter_element[simp]:
  fixes p':: "('a['b::array_max_count]) ptr"
  shows "vgetter (heap_array_map p' f s) = vgetter s"
  apply (rule ext)
  by (simp add: heap_array_map_def setter_fold_keeps_vgetter)

lemma getter_keeps_valid_array[simp]:
  fixes p':: "'a ptr"
  shows "(valid_array::'s \<Rightarrow> ('a['b::array_max_count]) ptr \<Rightarrow> bool) (w p' f s) = valid_array s"
  apply (rule ext)
  by (simp add: valid_array_def)

lemma getter_keeps_valid_array_pointwise[]:
  fixes p':: "'a ptr"
  fixes p :: "('a['b::array_max_count]) ptr"
  shows "(valid_array::'s \<Rightarrow> ('a['b::array_max_count]) ptr \<Rightarrow> bool) (w p' f s) p = valid_array s p"
  by (simp add: valid_array_def)
end


locale valid_pointer_two_dimensional_array_lense = pointer_two_dimensional_array_lense r w +
  valid_array_base vgetter +
  write_preserves_valid vgetter w
  for r:: "'s \<Rightarrow> 'a:: array_inner_max_size ptr \<Rightarrow> 'a"
  and w:: "'a ptr \<Rightarrow> ('a \<Rightarrow> 'a) \<Rightarrow> 's \<Rightarrow> 's"
  and vgetter:: "('s \<Rightarrow> 'a ptr \<Rightarrow> bool)"
begin
sublocale inner: valid_pointer_array_lense r w vgetter
  by (intro_locales)

sublocale outer: valid_pointer_array_lense heap_array heap_array_map valid_array
  by (intro_locales)

end

locale array_typ_heap_simulation =
  lense t_hrs t_hrs_update +
  read_simulation st v r t_hrs +
  write_simulation t_hrs t_hrs_update st v w +
  write_preserves_valid v w +
  valid_implies_cguard st v +
  valid_only_typ_desc_dependent t_hrs st v +
  pointer_array_lense r w +
  valid_array_base v
  for
    st:: "'s \<Rightarrow> 't" and
    r:: "'t \<Rightarrow> 'a::array_outer_max_size ptr \<Rightarrow> 'a" and
    w:: "'a ptr \<Rightarrow> ('a \<Rightarrow> 'a) \<Rightarrow> 't \<Rightarrow> 't" and
    v:: "'t \<Rightarrow> 'a ptr \<Rightarrow> bool" and
    t_hrs :: "'s \<Rightarrow> heap_raw_state" and
    t_hrs_update:: "(heap_raw_state \<Rightarrow> heap_raw_state) \<Rightarrow> 's \<Rightarrow> 's"
begin

sublocale typ_heap_simulation
  by (intro_locales)

sublocale valid_pointer_array_lense r w v
  by (intro_locales)

lemmas typ_heap_simulation = typ_heap_simulation_axioms


lemma valid_array_implies_safe: "valid_array (st s) p \<Longrightarrow> c_guard p"
  using valid_implies_c_guard
  apply (simp add: valid_array_def)
  by (metis TypHeapSimple.c_guard_array_c_guard array_ptr_index_simps(1))

lemma heap_array_data_correct:
  assumes valid_arr: "valid_array (st s) p"
  shows "heap_array (st s) p = h_val (hrs_mem (t_hrs s)) p"
  apply (subst cart_eq)
  apply clarsimp
  apply (subst  heap_access_Array_element')
   apply simp
  using read_commutes valid_arr
  by (auto simp add: valid_array_def)

lemma write_fold_commutes:
  fixes p:: "('a['b::array_max_count]) ptr"
  assumes n_bound: "n \<le> CARD('b)"
  assumes valid: "valid_array (st s) p"
  shows "st (t_hrs_update (hrs_mem_update (fold (\<lambda>i. heap_update (array_ptr_index p False i) (x.[i])) [0..<n])) s) =
    fold (\<lambda>i. w (array_ptr_index p False i) (\<lambda>_. x.[i])) [0..<n] (st s)"
  using n_bound valid
proof (induct n arbitrary: s)
  case 0
  then show ?case
    by simp
next
  case (Suc n)
  from Suc.prems obtain  suc_n_bound: "Suc n \<le> CARD('b)" and n_bound: "n \<le> CARD('b)" and n_bound': "n < CARD('b)"
    and valid: "valid_array (st s) p" by auto

  have vgetter: "v (st (t_hrs_update (hrs_mem_update (fold (\<lambda>i. heap_update (array_ptr_index p False i) (x.[i])) [0..<n])) s))
    (array_ptr_index p False n)"
    apply (subst Suc.hyps [OF n_bound valid] )
    apply (subst setter_fold_keeps_vgetter [OF n_bound])
    using valid n_bound' apply (simp add: valid_array_def)
    done
  show ?case
    apply simp
    apply (subst Suc.hyps[OF n_bound valid, symmetric])
    apply (subst write_commutes[symmetric])
     apply (rule vgetter)
    by (simp add: hrs_mem_update_def split_def comp_def)
qed

lemma heap_array_map_commutes:
  fixes p:: "('a['b::array_max_count]) ptr"
  assumes valid: "valid_array (st s) p"
  shows "st (t_hrs_update (hrs_mem_update (heap_update p x)) s) = heap_array_map p (\<lambda>_. x) (st s)"
proof -
  from valid_array_implies_safe [OF valid] have cgrd: "c_guard p" .
  show ?thesis
    apply (simp add: heap_array_map_def heap_update_array_pointless [OF cgrd])
    apply (rule write_fold_commutes)
    apply simp
    apply (rule valid)
    done
qed


lemma write_padding_fold_commutes:
  fixes p:: "('a['b::array_max_count]) ptr"
  assumes n_bound: "n \<le> CARD('b)"
  assumes valid: "valid_array (st s) p"
  assumes lbs: "length bs = CARD('b) * size_of TYPE('a)"
  shows "st (t_hrs_update
         (hrs_mem_update
           (fold
             (\<lambda>i. heap_update_padding (array_ptr_index p False i) (x.[i])
                    (take (size_of TYPE('a)) (drop (i * size_of TYPE('a)) bs)))
             [0..<n]))
         s) =
    fold (\<lambda>i. w (array_ptr_index p False i) (\<lambda>_. x.[i])) [0..<n] (st s)"
  using n_bound valid
proof (induct n arbitrary: s)
  case 0
  then show ?case
    by simp
next
  case (Suc n)
  from Suc.prems obtain  suc_n_bound: "Suc n \<le> CARD('b)" and n_bound: "n \<le> CARD('b)" and n_bound': "n < CARD('b)"
    and valid: "valid_array (st s) p" by auto

  from lbs suc_n_bound
  have lbs': "length (take (size_of TYPE('a)) (drop (n * size_of TYPE('a)) bs)) = size_of TYPE('a)"
    by (auto simp add: less_le_mult_nat nat_move_sub_le)


  have vgetter: "v (st (t_hrs_update
            (hrs_mem_update
              (\<lambda>h. fold (\<lambda>i. heap_update_padding (array_ptr_index p False i) (x.[i])
                               (take (size_of TYPE('a)) (drop (i * size_of TYPE('a)) bs)))
                     [0..<n] h))
            s))
     (array_ptr_index p False n)"
    apply (subst Suc.hyps [OF n_bound valid] )

    apply (subst setter_fold_keeps_vgetter [OF n_bound])
    using valid n_bound' apply (simp add: valid_array_def)
    done

  show ?case apply simp
    apply (subst Suc.hyps[OF n_bound valid, symmetric])

    apply (subst write_padding_commutes[where bs = \<open>take (size_of TYPE('a)) (drop (n * size_of TYPE('a)) bs)\<close>, OF vgetter lbs', symmetric])
    apply simp
    apply (simp only: hrs_mem_update_comp)
    apply (simp only: comp_def)
    done
qed


lemma heap_array_padding_map_commutes:
  fixes p:: "('a['b::array_max_count]) ptr"
  assumes valid: "valid_array (st s) p"
  assumes bound: "length bs = size_of TYPE('a['b])"
  shows "st (t_hrs_update (hrs_mem_update (heap_update_padding p x bs)) s) = heap_array_map p (\<lambda>_. x) (st s)"
proof -
  from valid_array_implies_safe [OF valid] have cgrd: "c_guard p" .
  from bound have bound': "length bs = CARD('b) * size_of TYPE('a)"
    by auto
  show ?thesis
    apply (simp add: heap_array_map_def heap_update_padding_array_pointless [OF cgrd bound'])
    apply (simp add: write_padding_fold_commutes [OF _ valid bound'])
    done
qed


lemma array_valid_same_typ_desc:
  fixes p:: "('a['b::array_max_count]) ptr"
  assumes typ_eq: "hrs_htd (t_hrs s) = hrs_htd (t_hrs t)"
  shows "valid_array (st s) p = valid_array (st t) p"
  apply (simp add: valid_array_def)
  using typ_eq valid_same_typ_desc by blast

sublocale array: typ_heap_simulation st heap_array heap_array_map valid_array t_hrs t_hrs_update
  apply (unfold_locales)
     apply (rule heap_array_data_correct, assumption)
    apply (rule heap_array_padding_map_commutes, assumption, assumption)
   apply (rule valid_array_implies_safe, assumption)
  apply (rule array_valid_same_typ_desc, assumption)
  done

end

locale two_dimensional_array_typ_heap_simulation =
  lense t_hrs t_hrs_update +
  read_simulation st v r t_hrs +
  write_simulation t_hrs t_hrs_update st v w  +
  write_preserves_valid v w +
  valid_implies_cguard st v +
  valid_only_typ_desc_dependent t_hrs st v +
  pointer_two_dimensional_array_lense r w
  for
    st:: "'s \<Rightarrow> 't" and
    r:: "'t \<Rightarrow> 'a::array_inner_max_size ptr \<Rightarrow> 'a" and
    w:: "'a ptr  \<Rightarrow> ('a \<Rightarrow> 'a) \<Rightarrow> 't \<Rightarrow> 't" and
    v:: "'t \<Rightarrow> 'a ptr \<Rightarrow> bool" and
    t_hrs :: "'s \<Rightarrow> heap_raw_state" and
    t_hrs_update:: "(heap_raw_state \<Rightarrow> heap_raw_state) \<Rightarrow> 's \<Rightarrow> 's"
begin

sublocale inner: array_typ_heap_simulation st r w v t_hrs t_hrs_update
  by (intro_locales)

lemmas inner_typ_heap_simulation = inner.typ_heap_simulation

sublocale outer: array_typ_heap_simulation st heap_array heap_array_map inner.valid_array t_hrs t_hrs_update
  by (intro_locales)

lemmas outer_typ_heap_simulation = outer.typ_heap_simulation


end

lemma root_ptr_valid_field_lvalue:
  fixes p::"'a::mem_type ptr"
  fixes q:: "'b::mem_type ptr"
  assumes root_p: "root_ptr_valid d p"
  assumes root_q: "root_ptr_valid d q"
  assumes fl: "field_lookup (typ_info_t TYPE('b)) f 0 = Some (t, k)"
  assumes other: "typ_uinfo_t TYPE('a) \<noteq> typ_uinfo_t TYPE('b)"
  shows "ptr_val p = &(q\<rightarrow>f) \<longleftrightarrow> False"
proof
  assume p: "ptr_val p = &(q\<rightarrow>f)"
  from field_tag_sub [OF fl] have "{&(q\<rightarrow>f)..+size_td t} \<subseteq> ptr_span q".
  moreover
  from root_ptr_valid_cases [OF root_p root_q] other have "ptr_span p \<inter> ptr_span q = {}" by blast
  ultimately
  show False
    using p
     by (metis (mono_tags, lifting) disjoint_iff field_lookup_wf_size_desc_gt fl intvl_inter
        intvl_start_inter mem_type_self subset_iff wf_size_desc)
qed simp

lemma root_ptr_valid_field_lvalue':
  fixes q:: "'b::mem_type ptr"
  assumes root_p: "root_ptr_valid d (PTR ('a::mem_type)(&(q\<rightarrow>f)))"
  assumes root_q: "root_ptr_valid d q"
  assumes fl: "field_lookup (typ_info_t TYPE('b)) f 0 = Some (t, k)"
  assumes other: "typ_uinfo_t TYPE('a) \<noteq> typ_uinfo_t TYPE('b)"
  shows "False"
  using root_ptr_valid_field_lvalue [OF root_p root_q fl other]
  by simp


lemma root_ptr_valid_array_ptr_index_dim1:
  fixes q:: "('a::array_outer_max_size['c::array_max_count]) ptr"
  assumes root_p: "root_ptr_valid d (array_ptr_index q False i)"
  assumes root_q: "root_ptr_valid d q"
  assumes other: "typ_uinfo_t TYPE('a) \<noteq> typ_uinfo_t TYPE('a['c])"
  assumes i_bound: "i < CARD('c)"
  shows "False"
proof -
  from field_lookup_array [OF i_bound]
  obtain t k where
    fl: "field_lookup (typ_info_t TYPE('a['c])) [replicate i (CHR ''1'')] 0 = Some (t, k)"
    by blast
  from root_ptr_valid_field_lvalue [OF root_p root_q fl other] i_bound
  show ?thesis
    by (simp add: array_ptr_index_field_lvalue_conv)
qed


lemma root_ptr_valid_field_lvalue_array_ptr_index_dim1:
  fixes q:: "'b::mem_type ptr"
  assumes root_p: "root_ptr_valid d (array_ptr_index (PTR('a['c]) &(q\<rightarrow>f)) False i)"
  assumes root_q: "root_ptr_valid d q"
  assumes other: "typ_uinfo_t TYPE('a) \<noteq> typ_uinfo_t TYPE('b)"
  assumes i_bound: "i < CARD('c)"
  assumes fl: "field_lookup (typ_info_t TYPE('b)) f 0 = Some (t, k)"
  assumes t: "export_uinfo t = typ_uinfo_t (TYPE('a::array_outer_max_size['c::array_max_count]))"
  shows False
proof -
  from field_lookup_array [OF i_bound]
  obtain s n where
    fl_i: "field_lookup (typ_info_t TYPE('a['c])) [replicate i (CHR ''1'')] k = Some (s, n)"
    by blast

  from fl_i t obtain s' n' where
    fl_i': "field_lookup t [replicate i (CHR ''1'')] k = Some (s', n')"
    by (metis (no_types, lifting) Padding_Equivalence.field_lookup_export_uinfo_Some_rev
        field_lookup_export_uinfo_Some fold_typ_uinfo_t)

  from field_lookup_prefix_Some''(1)[rule_format, where f="f" and g="[replicate i CHR ''1'']"
    and m=0, OF fl]
  have fl_app: "field_lookup (typ_info_t TYPE('b)) (f @ [replicate i CHR ''1'']) 0 = Some (s', n')"
    by (simp add: fl_update fl_i')
  have conv: "&(PTR('a['c]) &(q\<rightarrow>f)\<rightarrow>[replicate i CHR ''1'']) = &(q\<rightarrow>f @[replicate i CHR ''1''] )"
    apply (subst field_lvalue_append)
       apply simp_all
      apply (rule field_lookup_field_ti')
      apply (rule fl)
     apply (simp add: typ_uinfo_t_def i_bound t)
    apply (rule field_lookup_field_ti')
    apply (rule field_lookup_array [OF i_bound])
    done

  from root_ptr_valid_field_lvalue [OF root_p root_q fl_app other] show False
    by (simp add: array_ptr_index_field_lvalue_conv i_bound conv)
qed

lemma root_ptr_valid_field_lvalue_array_ptr_index_dim1':
  fixes q:: "'b::mem_type ptr"
  assumes root_p: "root_ptr_valid d (array_ptr_index (PTR(('a::array_outer_max_size['c::array_max_count])) &(q\<rightarrow>f)) False i)"
  assumes root_q: "root_ptr_valid d q"
  assumes other: "typ_uinfo_t TYPE('a) \<noteq> typ_uinfo_t TYPE('b)"
  assumes i_bound: "i < CARD('c)"
  assumes fl: "field_lookup (typ_info_t TYPE('b)) f 0 = Some (adjust_ti (typ_info_t (TYPE('a['c]))) acc upd, k)"
  assumes fg: "fg_cons acc upd"
  shows "False"
  using root_ptr_valid_field_lvalue_array_ptr_index_dim1 [OF root_p root_q other i_bound fl]
  by (simp add: fg)

lemma root_ptr_valid_array_ptr_index_dim2:
  fixes q:: "(('a::array_inner_max_size['c::array_max_count])['d::array_max_count]) ptr"
  assumes root_p: "root_ptr_valid d (array_ptr_index (array_ptr_index q False i) False j)"
  assumes root_q: "root_ptr_valid d q"
  assumes other: "typ_uinfo_t TYPE('a) \<noteq> typ_uinfo_t TYPE('a['c]['d])"
  assumes i_bound: "i < CARD('d)"
  assumes j_bound: "j < CARD('c)"
  shows "False"
proof -
  from field_lookup_array [OF i_bound, of 0, where 'a="'a['c]"]
  have fl_i: "field_lookup (typ_info_t TYPE(('a['c])['d])) [replicate i CHR ''1''] 0 =
                Some (adjust_ti (typ_info_t TYPE('a['c])) (\<lambda>x. x.[i]) (\<lambda>x f. Arrays.update f i x),
                 i * size_of TYPE('a['c]))" by simp
  from field_lookup_array [OF j_bound, of "i * size_of TYPE('a['c])", where 'a="'a"]
  have fl_j: "field_lookup (typ_info_t TYPE('a['c])) [replicate j CHR ''1''] (i * size_of TYPE('a['c])) =
               Some (adjust_ti (typ_info_t TYPE('a)) (\<lambda>x. x.[j]) (\<lambda>x f. Arrays.update f j x),
                i * size_of TYPE('a['c]) + j * size_of TYPE('a))" by simp

  have append: "&(PTR('a['c]) &(q\<rightarrow>[replicate i CHR ''1''])\<rightarrow>[replicate j CHR ''1'']) =
                  &(q\<rightarrow>[replicate i CHR ''1'', replicate j CHR ''1''])"
    apply (subst field_lvalue_append)
       apply simp_all
      apply (rule field_lookup_field_ti')
      apply (rule fl_i)
     apply (simp add: typ_uinfo_t_def i_bound)
    apply (rule field_lookup_field_ti')
    apply (rule field_lookup_array [OF j_bound])
    done

  have sz_eq: "size_of TYPE('a['c]) = (CARD('c) * size_of TYPE('a))"
    using size_of_array by blast
  from field_lookup_prefix_Some''(1)[rule_format, where f="[replicate i CHR ''1'']" and g="[replicate j CHR ''1'']"
   and t =  "(typ_info_t TYPE(('a['c])['d]))" and m=0, OF fl_i]
  obtain t k
    where fl: "field_lookup (typ_info_t TYPE('a['c]['d])) [replicate i CHR ''1'', replicate j CHR ''1''] 0 = Some (t, k)"
    apply (simp add: i_bound)
    apply (simp add: fl_update sz_eq  )
    using fl_j [simplified sz_eq]
    apply simp
    done
  show ?thesis
    using root_ptr_valid_field_lvalue [OF root_p root_q fl other] i_bound j_bound
    apply (simp add: array_ptr_index_field_lvalue_conv append )
    done
qed

lemma root_ptr_valid_field_lvalue_array_ptr_index_dim2:
  fixes q:: "'b::mem_type ptr"
  assumes root_p: "root_ptr_valid d (array_ptr_index (array_ptr_index (PTR('a['c]['d]) &(q\<rightarrow>f)) False i) False j)"
  assumes root_q: "root_ptr_valid d q"
  assumes other: "typ_uinfo_t TYPE('a) \<noteq> typ_uinfo_t TYPE('b)"
  assumes i_bound: "i < CARD('d)"
  assumes j_bound: "j < CARD('c)"
  assumes fl: "field_lookup (typ_info_t TYPE('b)) f 0 = Some (t, k)"
  assumes t: "export_uinfo t = typ_uinfo_t (TYPE(('a::array_inner_max_size['c::array_max_count])['d::array_max_count]))"
  shows "False"
proof -
  from field_lookup_array [OF i_bound]
  obtain s n where
    fl_i: "field_lookup (typ_info_t TYPE('a['c]['d])) [replicate i (CHR ''1'')] k = Some (s, n)" and
    s: "s = adjust_ti (typ_info_t TYPE('a['c])) (\<lambda>x. x.[i]) (\<lambda>x f. Arrays.update f i x)"
    by blast

  from fl_i t s obtain s' n' where
    fl_i': "field_lookup t [replicate i (CHR ''1'')] k = Some (s', n')" and
    s': "export_uinfo s' = typ_uinfo_t TYPE('a['c])"
    by (smt (verit, best) Padding_Equivalence.field_lookup_export_uinfo_Some_rev
       export_tag_adjust_ti(1) fg_cons_array field_lookup_array fold_typ_uinfo_t i_bound wf_fd field_lookup_typ_uinfo_t_Some)

  from field_lookup_prefix_Some''(1)[rule_format, where f="f" and g="[replicate i CHR ''1'']"
    and m=0, OF fl]
  have fl_app1: "field_lookup (typ_info_t TYPE('b)) (f @ [replicate i CHR ''1'']) 0 = Some (s', n')"
    by (simp add: fl_update fl_i')

  from field_lookup_array [OF j_bound]
  obtain s'' n'' where
    fl_j: "field_lookup (typ_info_t TYPE('a['c])) [replicate j (CHR ''1'')] n' = Some (s'', n'')"
    by blast

  from fl_j s' obtain s''' n''' where
    fl_j': "field_lookup s' [replicate j (CHR ''1'')] n' = Some (s''', n''')"
    by (metis (no_types, lifting) CTypes.field_lookup_export_uinfo_Some_rev field_lookup_export_uinfo_Some fold_typ_uinfo_t)

  from field_lookup_prefix_Some''(1)[rule_format, where f="f @ [replicate i CHR ''1'']" and g="[replicate j CHR ''1'']"
     and m=0, OF fl_app1]
  have fl_app2: "field_lookup (typ_info_t TYPE('b)) (f @ [replicate i CHR ''1'', replicate j CHR ''1'']) 0 = Some (s''', n''')"
    by (simp add: fl_update fl_j')

  have conv: "&(PTR('a['c]) &(PTR('a['c]['d]) &(q\<rightarrow>f)\<rightarrow>[replicate i CHR ''1''])\<rightarrow>[replicate j CHR ''1'']) =
           &(q\<rightarrow>f @ [replicate i CHR ''1'', replicate j CHR ''1''])"
    apply (subst field_lvalue_append)
       apply (rule field_lookup_field_ti')
       apply (rule fl)
      apply (simp add: typ_uinfo_t_def i_bound t)
     apply (rule field_lookup_field_ti')
     apply (rule field_lookup_offset_shift')
     apply (rule fl_i)

    apply (subst field_lvalue_append)
    apply (rule field_lookup_field_ti')
       apply (rule field_lookup_offset_shift')
       apply (rule fl_app1)
      apply (simp add: s')
     apply (rule field_lookup_field_ti')
     apply (rule field_lookup_offset_shift')
    apply (rule fl_j)
    apply simp
    done
  from root_ptr_valid_field_lvalue [OF root_p root_q fl_app2 other ] show False
    by (simp add: array_ptr_index_field_lvalue_conv i_bound j_bound conv)
qed

context open_types
begin

definition
  "typ_heap_simulation_of_field (st::'s \<Rightarrow> 't) t_hrs t_hrs_update heap_typing_upd f' r' w' \<longleftrightarrow>
  (\<forall>d p f. heap_typing_upd d o w' p f = w' p f o heap_typing_upd d) \<and>
  (\<forall>t u n.
    field_ti TYPE('a::mem_type) f' = Some t \<longrightarrow>
    field_lookup (typ_uinfo_t TYPE('a)) f' 0 = Some (u, n) \<longrightarrow>
    partial_pointer_lense (merge_ti t) r' w' \<and>
    (\<forall>(p::'a ptr) s. (\<forall>a\<in>ptr_span p. root_ptr_valid (hrs_htd (t_hrs s)) (PTR(stack_byte) a)) \<longrightarrow>
      r' (st s) p ZERO('a) = ZERO('a)) \<and>
    (\<forall>(p::'a ptr) x h. ptr_valid_u u (hrs_htd (t_hrs h)) &(p\<rightarrow>f') \<longrightarrow>
      st (t_hrs_update (hrs_mem_update (heap_upd_list (size_td u) &(p\<rightarrow>f') (access_ti t x))) h) =
      w' p x (st h)))"

end

definition
  pointer_writer_disjnt ::
    "('a::c_type ptr \<Rightarrow> 't upd) \<Rightarrow> ('b::c_type ptr \<Rightarrow> 't upd) \<Rightarrow> bool"
where
  "pointer_writer_disjnt f g \<longleftrightarrow>
    (\<forall>p q. disjnt (ptr_span p) (ptr_span q) \<longrightarrow> f p \<circ> g q = g q o f p)"

definition
  pointer_writer_disjnt_eq ::
    "('a::c_type ptr \<Rightarrow> 'x \<Rightarrow> 't upd) \<Rightarrow> ('b::c_type ptr \<Rightarrow> 'y \<Rightarrow> 't upd) \<Rightarrow> bool"
where
  "pointer_writer_disjnt_eq f g \<longleftrightarrow> (\<forall>p q x y.
    disjnt (ptr_span p) (ptr_span q) \<or> ptr_val p = ptr_val q \<longrightarrow> f p x \<circ> g q y = g q y o f p x)"

named_theorems pointer_writer_disjnt_intros

lemma pointer_writer_disjnt_eq:
  assumes nm: "\<exists>n1 n2.
    field_lookup (typ_uinfo_t TYPE('a::mem_type)) f1 0 =
      Some (typ_uinfo_t TYPE('b::mem_type), n1) \<and>
    field_lookup (typ_uinfo_t TYPE('a)) f2 0 = Some (typ_uinfo_t TYPE('c::mem_type), n2)"
  assumes w1_w2: "\<And>x y. pointer_writer_disjnt (\<lambda>p. w1 p x) (\<lambda>q. w2 q y)"
  shows "disj_fn f1 f2 \<longrightarrow> pointer_writer_disjnt_eq
    (\<lambda>(p::'a ptr). w1 (PTR('b) &(p\<rightarrow>f1)))
    (\<lambda>(p::'a ptr). w2 (PTR('c) &(p\<rightarrow>f2)))" (is "?disj \<longrightarrow> ?goal")
proof
  assume ?disj
  from nm obtain n1 n2 where fl:
    "field_lookup (typ_uinfo_t TYPE('a::mem_type)) f1 0 =
      Some (typ_uinfo_t TYPE('b::mem_type), n1)"
    "field_lookup (typ_uinfo_t TYPE('a)) f2 0 = Some (typ_uinfo_t TYPE('c::mem_type), n2)"
    by auto
  from fl[THEN field_tag_sub']
  have "ptr_span (PTR('b) &(p\<rightarrow>f1)) \<subseteq> ptr_span p \<and> ptr_span (PTR('c) &(q\<rightarrow>f2)) \<subseteq> ptr_span q"
    for p q :: "'a ptr"
    by (auto intro: field_tag_sub' simp: size_of_def del: subsetI)
  then have ne[simp]: "disjnt (ptr_span p) (ptr_span q) \<Longrightarrow>
    disjnt (ptr_span (PTR('b) &(p\<rightarrow>f1))) (ptr_span (PTR('c) &(q\<rightarrow>f2)))" for p q :: "'a ptr"
    by (blast intro: disjnt_subset1 disjnt_subset2)
  moreover
  from fl obtain u1 u2 where fl_t:
      "field_lookup (typ_info_t TYPE('a)) f1 0 = Some (u1, n1)"
      "field_lookup (typ_info_t TYPE('a)) f2 0 = Some (u2, n2)"
    and export: "export_uinfo u1 = typ_uinfo_t TYPE('b)" "export_uinfo u2 = typ_uinfo_t TYPE('c)"
    by (auto dest!: field_lookup_export_uinfo_Some_rev simp: typ_uinfo_t_def)
  from fa_fu_lookup_disj_interD[OF fl_t \<open>disj_fn f1 f2\<close>]
  have "disjnt (ptr_span (PTR('b) &(p\<rightarrow>f1))) (ptr_span (PTR('c) &(p\<rightarrow>f2)))" for p :: "'a ptr"
    apply (simp add: size_of_fold disjnt_def)
    apply (simp add: size_of_def field_lvalue_def field_offset_def field_offset_untyped_def fl
                     intvl_disj_offset
                flip: typ_uinfo_size export)
    done
  ultimately show ?goal using w1_w2
    by (auto simp: pointer_writer_disjnt_def pointer_writer_disjnt_eq_def)
qed

lemma pointer_writer_disjnt_sym:
  "pointer_writer_disjnt f g \<Longrightarrow> pointer_writer_disjnt g f"
  by (auto simp add: pointer_writer_disjnt_def disjnt_sym)

lemma pointer_writer_disjnt_id_left:
  "pointer_writer_disjnt (\<lambda>p h. h) w"
  by (simp add: pointer_writer_disjnt_def fun_eq_iff)

lemma pointer_writer_disjnt_id_left':
  "pointer_writer_disjnt (\<lambda>p. id) w"
  by (simp add: pointer_writer_disjnt_def fun_eq_iff)

lemma pointer_writer_disjnt_comp_left:
  "pointer_writer_disjnt w1 w \<Longrightarrow> pointer_writer_disjnt w2 w \<Longrightarrow>
    pointer_writer_disjnt (\<lambda>p h. w1 p (w2 p h)) w"
  by (simp add: pointer_writer_disjnt_def fun_eq_iff)

lemma pointer_writer_disjnt_comp_left':
  "pointer_writer_disjnt w1 w \<Longrightarrow> pointer_writer_disjnt w2 w \<Longrightarrow>
    pointer_writer_disjnt (\<lambda>p. w1 p \<circ> w2 p) w"
  by (simp add: pointer_writer_disjnt_def fun_eq_iff)

lemma pointer_writer_disjnt_fold_left:
  "list_all (\<lambda>w'. pointer_writer_disjnt (f w') w) ws \<Longrightarrow>
    pointer_writer_disjnt (\<lambda>p. fold (\<lambda>w. f w p) ws) w"
  by (induction ws) (auto intro: pointer_writer_disjnt_comp_left' pointer_writer_disjnt_id_left')

lemma pointer_writer_disjntI:
  "(\<And>p q h. w1 p (w2 q h) = w2 q (w1 p h)) \<Longrightarrow> pointer_writer_disjnt w1 w2"
  by (auto simp: pointer_writer_disjnt_def)

lemma pointer_writer_disjntD:
  "pointer_writer_disjnt w1 w2 \<Longrightarrow> disjnt (ptr_span p) (ptr_span q) \<Longrightarrow>
    w1 p (w2 q h) = w2 q (w1 p h)"
  by (auto simp: pointer_writer_disjnt_def fun_eq_iff)

lemma pointer_writer_disjnt_ptr_map_left:
  fixes w1 :: "'a::mem_type ptr \<Rightarrow> 's upd" and w2 :: "'b::c_type ptr \<Rightarrow> 's upd"
  assumes w1_w2: "pointer_writer_disjnt w1 w2"
  assumes "\<And>(p::'c::c_type ptr). ptr_span (F p) \<subseteq> ptr_span p"
  shows "pointer_writer_disjnt (\<lambda>(p::'c ptr). w1 (F p)) w2"
  using assms by (auto simp: pointer_writer_disjnt_def disjnt_subset1)

lemma pointer_writer_disjnt_ptr_left:
  fixes w1 :: "'a::mem_type ptr \<Rightarrow> 's upd" and w2 :: "'b::mem_type ptr \<Rightarrow> 's upd"
  assumes w1_w2: "pointer_writer_disjnt w1 w2"
  assumes n:
    "\<exists>n. field_lookup (typ_uinfo_t TYPE('c::mem_type)) f 0 = Some (typ_uinfo_t TYPE('a), n)"
  shows "pointer_writer_disjnt (\<lambda>(p::'c ptr). w1 (PTR('a) &(p\<rightarrow>f))) w2"
proof (rule pointer_writer_disjnt_ptr_map_left[OF w1_w2])
  show "ptr_span (PTR('a) &(p\<rightarrow>f)) \<subseteq> ptr_span p" for p :: "'c ptr"
    using field_tag_sub'[where 'a='c, of f "typ_uinfo_t TYPE('a)" _ p] n
    by (auto simp: size_of_def)
qed

lemma pointer_writer_disjnt_ptr_corce:
  fixes w1 :: "'a::mem_type ptr \<Rightarrow> 's upd" and w2 :: "'b::mem_type ptr \<Rightarrow> 's upd"
  assumes w1_w2: "pointer_writer_disjnt w1 w2"
    and size: "size_of TYPE('a) \<le> size_of TYPE('c)"
  shows "pointer_writer_disjnt (\<lambda>(p::'c::c_type ptr). w1 (PTR_COERCE('c \<rightarrow> 'a) p)) w2"
  by (rule pointer_writer_disjnt_ptr_map_left[OF w1_w2])
     (simp add: intvl_start_le size)

lemma pointer_writer_disjnt_ptr_corce_signed:
  fixes w1 :: "'a::len8 word ptr \<Rightarrow> 's upd" and w2 :: "'b::mem_type ptr \<Rightarrow> 's upd"
  assumes w1_w2: "pointer_writer_disjnt w1 w2"
  shows "pointer_writer_disjnt (\<lambda>(p::'a signed word ptr).
    w1 (PTR_COERCE('a signed word \<rightarrow> 'a word) p)) w2"
  using w1_w2 by (rule pointer_writer_disjnt_ptr_corce) (simp add: size_of_signed_word)

lemma pointer_writer_disjnt_ptr_corce_signed':
  fixes w1 :: "'a::len8 word ptr \<Rightarrow> 's upd" and w2 :: "'b::mem_type ptr \<Rightarrow> 's upd"
  shows "pointer_writer_disjnt w2 w1 \<Longrightarrow>
    pointer_writer_disjnt w2 (\<lambda>(p::'a signed word ptr).
      w1 (PTR_COERCE('a signed word \<rightarrow> 'a word) p))"
  using pointer_writer_disjnt_ptr_corce_signed[of w1 w2] by (simp add: pointer_writer_disjnt_sym)

lemma (in pointer_lense) pointer_writer_disjnt_replace_by_const:
  "(\<And>x. pointer_writer_disjnt (\<lambda>p. w p (\<lambda>_. x)) w') \<Longrightarrow> pointer_writer_disjnt (\<lambda>p. w p f) w'"
  by (auto simp add: pointer_writer_disjnt_def fun_eq_iff)
     (metis (no_types, lifting) read_write_same write_cong write_read)

lemma (in pointer_lense) read_commute_of_pointer_writer_disjnt:
  assumes w': "\<And>f. pointer_writer_disjnt (\<lambda>p. w p f) w'"
  assumes p_q: "disjnt (ptr_span p) (ptr_span q)"
  shows "r (w' q h) p = r h p"
  apply (subst write_same[of "\<lambda>_. r h p" h p, OF refl, symmetric])
  apply (subst pointer_writer_disjntD[OF w' p_q, symmetric])
  apply (subst read_write_same)
  apply (rule refl)
  done

lemma (in pointer_lense) read_commute_of_pointer_writer_disjnt':
  assumes w': "\<And>f. pointer_writer_disjnt w' (\<lambda>p. w p f)"
  assumes p_q: "disjnt (ptr_span p) (ptr_span q)"
  shows "r (w' q h) p = r h p"
  using read_commute_of_pointer_writer_disjnt[OF w'[THEN pointer_writer_disjnt_sym] p_q] .

lemma (in pointer_lense) read_commute_of_commute:
  assumes w': "\<And>p f. w p f o w' = w' o w p f"
  shows "r (w' h) p = r h p"
  using read_write_same[of p "\<lambda>_. r h p" "w' h"] w'
  by (subst write_same[of "\<lambda>_. r h p" h p, OF refl, symmetric]) (simp add: fun_eq_iff)

lemma (in pointer_lense) read_commute_of_commute':
  assumes w': "\<And>p f. w' o w p f = w p f o w'"
  shows "r (w' h) p = r h p"
  using read_commute_of_commute[OF w'[symmetric]] .

lemma (in lense) get_commute_of_commute:
  assumes w': "\<And>f. w' o upd f = upd f o w'"
  shows "get (w' h) = get h"
  using get_upd[of "\<lambda>_. get h" "w' h"] w'[symmetric]
  by (subst upd_same[of "\<lambda>_. get h" h, OF refl, symmetric]) (simp add: fun_eq_iff del: get_upd)

lemma (in pointer_lense) pointer_writer_disjnt_replace_dep_by_const:
  assumes *: "\<And>x. pointer_writer_disjnt (\<lambda>p. w p x) w'"
  shows "pointer_writer_disjnt (\<lambda>p s. w p (f (r s p)) s) w'"
  by (auto simp add: pointer_writer_disjnt_def fun_eq_iff
      read_commute_of_pointer_writer_disjnt[OF *]
      pointer_writer_disjntD[OF *])

lemma (in pointer_lense) pointer_writer_disjnt_upd[pointer_writer_disjnt_intros]:
  "pointer_writer_disjnt (\<lambda>p. w p x) (\<lambda>p. w p y)"
  by (simp add: pointer_writer_disjnt_def write_other_commute disjnt_def fun_eq_iff)

lemma (in partial_pointer_lense) read_commute_of_pointer_writer_disjnt:
  assumes w': "\<And>f. pointer_writer_disjnt (\<lambda>p. w p f) w'"
  assumes p_q: "disjnt (ptr_span p) (ptr_span q)"
  shows "r (w' q h) p y = r h p y"
  by (metis m_r p_q pointer_writer_disjntD r_w w' w_r)

lemma pointer_lense_upd_fun_of_lense:
  fixes get upd assumes "lense get upd"
  shows "pointer_lense get (\<lambda>p f. upd (upd_fun p f))"
proof -
  interpret lense get upd by fact
  show ?thesis
  proof qed (simp_all add: upd_same upd_fun.upd_same disj_ptr_span_ptr_neq
      upd_fun_commute Int_commute disjnt_def)
qed

locale open_types_heap_typing_state = open_types \<T> +
  heap_typing_state heap_typing heap_typing_upd
  for
    \<T> and
    heap_typing :: "'t \<Rightarrow> heap_typ_desc" and
    heap_typing_upd :: "(heap_typ_desc \<Rightarrow> heap_typ_desc) \<Rightarrow> 't \<Rightarrow> 't" 


locale typ_heap_simulation_open_types =
  typ_heap_simulation st r w v t_hrs t_hrs_update +
  open_types_heap_typing_state \<T> heap_typing heap_typing_upd
  for
    \<T> and
    st:: "'s \<Rightarrow> 't" and
    r:: "'t \<Rightarrow> ('a::{xmem_type, stack_type}) ptr \<Rightarrow> 'a" and
    w:: "'a ptr \<Rightarrow> ('a \<Rightarrow> 'a) \<Rightarrow> 't \<Rightarrow> 't" and
    v:: "'t \<Rightarrow> 'a ptr \<Rightarrow> bool" and
    t_hrs :: "'s \<Rightarrow> heap_raw_state" and
    t_hrs_update:: "(heap_raw_state \<Rightarrow> heap_raw_state) \<Rightarrow> 's \<Rightarrow> 's" and
    heap_typing :: "'t \<Rightarrow> heap_typ_desc" and
    heap_typing_upd :: "(heap_typ_desc \<Rightarrow> heap_typ_desc) \<Rightarrow> 't \<Rightarrow> 't" +
  assumes heap_typing_commutes[simp]: "heap_typing (st s) = hrs_htd (t_hrs s)"
  assumes heap_typing_upd_write_commute:
    "\<And>p f h d. heap_typing_upd d (w p f h) = w p f (heap_typing_upd d h)"
  assumes ptr_valid_imp_v: "\<And>p h. ptr_valid (heap_typing h) p \<Longrightarrow> v h p"
  assumes sim_stack_stack_byte_zero':
    "\<And>p s. \<forall>a\<in>ptr_span p. root_ptr_valid (hrs_htd (t_hrs s)) (PTR(stack_byte) a) \<Longrightarrow>
      r (st s) p = ZERO('a)"
begin

lemma heap_typing_write[simp]: "heap_typing (w p f h) = heap_typing h"
  apply (subst upd_same[symmetric, of "\<lambda>_. heap_typing h", OF refl])
  apply (subst heap_typing_upd_write_commute[symmetric])
  apply (rule get_upd)
  done

lemma heap_typing_upd[simp]: "r (heap_typing_upd d h) = r h"
  apply (rule ext)
  subgoal for p
    apply (subst write_same[symmetric, of "\<lambda>_. r h p", OF refl])
    apply (subst heap_typing_upd_write_commute)
    apply (rule read_write_same)
    done
  done

lemma unchanged_typing_root_ptr_valid_preserved:
  "unchanged_typing_on A t1 t2 \<Longrightarrow> ptr_span p \<subseteq> A 
  \<Longrightarrow> root_ptr_valid (heap_typing t1) p = root_ptr_valid (heap_typing t2) p"
  by (simp add: unchanged_typing_on_def equal_on_def intvlI 
      root_ptr_valid_def size_of_tag subsetD valid_root_footprint_def)

lemma unchanged_typing_ptr_valid_preserved:
  assumes unch: "unchanged_typing_on UNIV t1 t2" 
  shows "ptr_valid (heap_typing t1) p = ptr_valid (heap_typing t2) p"
proof -
  from unch have "heap_typing t1 = heap_typing t2"
    by (simp add: fun_eq_iff unchanged_typing_on_def equal_on_def)
  thus ?thesis
    by simp
qed

lemma unchanged_typing_on_write [unchanged_typing_on_simps]: 
  "unchanged_typing_on A t (w p f t)"
  using heap_typing_upd_write_commute 
  by (simp add: unchanged_typing_on_def)

lemma heap_typing_fold_upd_write: "heap_typing (fold (\<lambda>i. w (x i) (g i)) [0..<n] t) = heap_typing t"
proof (induct n)
  case 0
  then show ?case by (simp add: heap_typing_upd_write_commute)
next
  case (Suc n)
  then show ?case by (simp add: heap_typing_upd_write_commute)
qed


end

lemma distinct_prop_conj:
  "distinct_prop (\<lambda>a b. R a b \<and> P a b) xs \<longleftrightarrow> distinct_prop R xs \<and> distinct_prop P xs"
  by (auto simp: distinct_prop_iff_nth)

lemma distinct_prop_zip_cons:
  "list_all (\<lambda>(c, d). P a b c d) (zip as bs) \<Longrightarrow>
    distinct_prop (\<lambda>(a, b) (c, d). P a b c d) (zip as bs) \<Longrightarrow>
    distinct_prop (\<lambda>(a, b) (c, d). P a b c d) (zip (a#as) (b#bs))"
  by (simp add: list_all_iff)

lemma distinct_prop_zip_nil:
  "distinct_prop (\<lambda>(a, b) (c, d). P a b c d) (zip [] [])"
  by (simp add: list_all_iff)

lemma list_all_zip_cons:
  "P a b \<Longrightarrow> list_all (\<lambda>(a, b). P a b) (zip as bs) \<Longrightarrow>
    list_all (\<lambda>(a, b). P a b) (zip (a#as) (b#bs))"
  by simp

lemma list_all_zip_nil:
  "list_all (\<lambda>(a, b). P a b) (zip [] [])"
  by simp

named_theorems disjnt_heap_fields_comp

context open_types
begin

lemma typ_heap_simulationI_part_addressable:
  fixes R :: "'t \<Rightarrow> 'a::{xmem_type, stack_type} ptr \<Rightarrow> 'a"
  assumes hrs: "heap_typing_simulation \<T> hrs hrs_upd heap_typing heap_typing_upd l"
  assumes fs: "map_of \<T> (typ_uinfo_t TYPE('a)) = Some fs"
  assumes "lense g u"
  assumes len[simp]: "length rs = length fs" "length ws = length fs"
  assumes *:
      "list_all (\<lambda>(f, r, w). typ_heap_simulation_of_field l hrs hrs_upd heap_typing_upd f r w) (zip fs (zip rs ws))"
    and **: "distinct_prop (\<lambda>(f1, w1) (f2, w2).
      disj_fn f1 f2 \<longrightarrow> pointer_writer_disjnt_eq w1 w2)
      (zip fs ws)"
    and ws_u: "list_all (\<lambda>w. \<forall>p a f. w p a \<circ> u f = u f \<circ> w p a) ws"
    and l_u: "\<And>(p::'a ptr) (x::'a) (s::'b).
      PTR_VALID('a) (hrs_htd (hrs s)) p \<Longrightarrow>
      l (hrs_upd (write_dedicated_heap p x) s) = u (upd_fun p (\<lambda>old. merge_addressable_fields old x)) (l s)"
    and r_stack:
      "\<And>p s. \<forall>a\<in>ptr_span p. root_ptr_valid (hrs_htd (hrs s)) (PTR(stack_byte) a) \<Longrightarrow>
        g (l s) p = ZERO(_)"
    and heap_typing_u: "\<And>x d h. heap_typing_upd d (u x h) = u x (heap_typing_upd d h)"
  assumes V:
    "\<And>h p. V h p \<longleftrightarrow> PTR_VALID('a) (heap_typing h) p"
  assumes R:
    "\<And>h p. R h p = fold (\<lambda>r. r h p) rs (g h p)"
  assumes W:
    "\<And>p f h. W p f h =
      fold (\<lambda>w. w p (f (R h p))) ws (u (upd_fun p (\<lambda>old. merge_addressable_fields old (f (R h p)))) h)"
  shows "typ_heap_simulation_open_types \<T> l R W V hrs hrs_upd heap_typing heap_typing_upd \<and>
    (pointer_lense g (\<lambda>p f. u (upd_fun p f))) \<and>
    (\<forall>w. (\<forall>x. list_all (\<lambda>w'. pointer_writer_disjnt (\<lambda>p. w' p x) w) ws) \<longrightarrow>
      (\<forall>x. pointer_writer_disjnt (\<lambda>p. u (upd_fun p (\<lambda>_. x))) w) \<longrightarrow>
      (\<forall>f. pointer_writer_disjnt (\<lambda>p. W p f) w)) \<and>
    (\<forall>w p. (\<forall>x. list_all (\<lambda>w'. w' p x o w = w o w' p x) ws) \<longrightarrow>
      (\<forall>x. u (upd_fun p (\<lambda>_. x)) o w = w o u (upd_fun p (\<lambda>_. x))) \<longrightarrow>
      (\<forall>f. W p f o w = w o W p f))"
    (is "?t1 \<and> ?t3 \<and>
      (\<forall>w. ?ws w \<longrightarrow> ?u w \<longrightarrow> (\<forall>f. ?t2 f w)) \<and>
      (\<forall>w p. ?ws2 w p \<longrightarrow> ?u2 w p \<longrightarrow> (\<forall>f. ?t4 w p f))")
proof (intro conjI allI impI)
  interpret hrs: heap_typing_simulation \<T> hrs hrs_upd heap_typing heap_typing_upd l by fact
  interpret lense g u by fact

  have [simp]: "length (addressable_fields TYPE('a)) = length fs"
    by (simp add: addressable_fields_def fs)

  have "list_all (\<lambda>f. \<exists>u n. field_lookup (typ_uinfo_t TYPE('a)) f 0 = Some (u, n))
    (map fst (zip fs (zip rs ws)))"
    using wf_\<T>[OF fs] by auto
  then have fs_exists:
    "list_all (\<lambda>x. \<exists>u n. field_lookup (typ_uinfo_t TYPE('a)) (fst x) 0 = Some (u, n))
      (zip fs (zip rs ws))"
    by (simp add: list.pred_map comp_def del: len)

  have rs_ws:
    "list_all (\<lambda>(m, r, w). partial_pointer_lense m r w) (zip (map merge_ti (map snd (addressable_fields TYPE('a)))) (zip rs ws))"
    apply (simp add: zip_map1 list.pred_map addressable_fields_def fs split_beta' comp_def)
    using list_all_conj[OF * fs_exists]
    apply (rule list.pred_mono_strong)
    apply (auto simp: field_ti_def field_lookup_typ_uinfo_t_Some typ_heap_simulation_of_field_def
                dest!: field_lookup_uinfo_Some_rev)
    done

  have dist: "distinct_prop disj_fn fs"
    using \<T>_distinct[OF fs] .

  interpret pointer_lense R W
    apply (rule pointer_lense_of_partials_cover[
      of g u "map merge_ti (map snd (addressable_fields TYPE('a)))" rs ws, OF \<open>lense g u\<close> _ _ _ _ _ _ R])
    subgoal by simp
    subgoal by simp
    subgoal by fact
    subgoal for a b c
      apply (simp add: distinct_prop_map addressable_fields_def fs)
      apply (rule distinct_prop_mono[OF _ dist])
      using wf_\<T>[OF fs]
      apply (intro disjnt_scene_merge_ti[THEN disjnt_sceneD,
        OF option.collapse[symmetric] option.collapse[symmetric]])
      apply (auto simp: list.pred_set field_ti_def disj_fn_def
                  dest!: field_lookup_uinfo_Some_rev)
      done
    subgoal
      using ws_u ** dist
      apply (clarsimp simp add: list_all_iff pointer_writer_disjnt_eq_def[abs_def])
      apply (clarsimp simp add: distinct_prop_iff_nth fun_eq_iff distinct_conv_nth
          disj_fn_def)
      apply metis
      done
    subgoal by (simp add: merge_ti_list_def fold_map comp_def)
    subgoal by (rule W)
    done

  have "list_all (\<lambda>(f, w). \<forall>t u n h p x.
        field_ti TYPE('a) f = Some t \<longrightarrow>
        field_lookup (typ_uinfo_t TYPE('a)) f 0 = Some (u, n) \<longrightarrow>
        ptr_valid_u u (hrs_htd (hrs h)) &(p\<rightarrow>f) \<longrightarrow>
        l (hrs_upd (hrs_mem_update (heap_upd_list (size_td u) &(p\<rightarrow>f) (access_ti t x))) h) =
          w p x (l h))
     (map (\<lambda>frw. (fst frw, snd (snd frw))) (zip fs (zip rs ws)))"
    unfolding list.pred_map
    using * by (rule list.pred_mono_strong) (auto simp:  typ_heap_simulation_of_field_def)
  also have "map (\<lambda>frw. (fst frw, snd (snd frw))) (zip fs (zip rs ws)) = zip fs ws"
    by (simp add: list_eq_iff_nth_eq)
  finally have fs_ws: "list_all2 (\<lambda>f w. \<forall>t u n h p x.
        field_ti TYPE('a) f = Some t \<longrightarrow>
        field_lookup (typ_uinfo_t TYPE('a)) f 0 = Some (u, n) \<longrightarrow>
        ptr_valid_u u (hrs_htd (hrs h)) &(p\<rightarrow>f) \<longrightarrow>
        l (hrs_upd (hrs_mem_update (heap_upd_list (size_td u) &(p\<rightarrow>f) (access_ti t x))) h) =
          w p x (l h))
     fs ws"
    by (subst (asm) list_all_zip_iff_list_all2; simp)

  have V_l: "\<And>h p. V (l h) p \<longleftrightarrow> PTR_VALID('a) (hrs_htd (hrs h)) p"
    by (simp add: V)

  interpret write_simulation hrs hrs_upd l V W
    apply (rule write_simulationI[OF fs hrs, of ws u V _ R])
    apply (rule fs_ws)
    apply (rule l_u)
    apply assumption
    apply (rule V_l)
    apply (rule W)
    done

  show ?t3
    by (rule pointer_lense_upd_fun_of_lense) fact
  then interpret u: pointer_lense g "\<lambda>p f. u (upd_fun p f)" .

  show "?t2 f w" if *: "?ws w" "?u w" for w f
    by (rule pointer_writer_disjnt_replace_by_const)
       (use * in \<open>auto simp add: W[abs_def]
        intro!: pointer_writer_disjnt_comp_left[OF pointer_writer_disjnt_fold_left
                u.pointer_writer_disjnt_replace_by_const]\<close>)

  show disj: "?t4 w p f" if *: "?u2 w p" "?ws2 w p" for p f w
  proof (standard, unfold comp_def)
    fix h
    have w_ws: "w (fold (\<lambda>w. w p c) ws h) = fold (\<lambda>w. w p c) ws (w h)" for c h
      using *[rule_format, of c]
      by (induction ws arbitrary: h) (auto simp: fun_eq_iff)

    have w_u[simp]: "w (u (upd_fun p (\<lambda>_. c)) h) = u (upd_fun p (\<lambda>_. c)) (w h)" for c h
      using *(1) by (auto simp: fun_eq_iff)

    have g_w[simp]: "g (w h) p = g h p" for h
      by (subst u.write_same[of "\<lambda>_. g h p" h p, OF refl, symmetric])
         (simp add: u.read_write_same)

    have w_u'[simp]: "w (u (upd_fun p f) h) = u (upd_fun p f) (w h)" for f h
      by (subst (1 2) u.write_cong[where f'="\<lambda>_. f (g h p)"]) simp_all

    have w_W_const: "w (W p (\<lambda>x. c) h) = W p (\<lambda>x. c) (w h)" for c h
      by (simp add: W w_ws)

    have R_eq: "R (w h) p = R h p"
      apply (subst write_same[of "\<lambda>_. R h p" h p, OF refl, symmetric])
      apply (subst w_W_const)
      apply (subst read_write_same)
      apply (rule refl)
      done

    show "W p f (w h) = w (W p f h)"
      by (simp add: R_eq write_cong[of f _ _ "\<lambda>_. f (R h p)"] w_W_const)
  qed

  show ?t1
  proof
    fix h p assume V_p: "V (l h) p"
    then show "c_guard p" by (simp add: ptr_valid.ptr_valid_c_guard V)

    have l_h: "l h = W p (\<lambda>x. h_val (hrs_mem (hrs h)) p) (l h)"
      apply (subst write_commutes[OF V_p, symmetric])
      apply (subst hrs.t_hrs.heap.upd_same)
      apply (cases "hrs h")
      apply (simp_all add: hrs_mem_update_def hrs_mem_def xmem_type_class.heap_update_id)
      done

    show "R (l h) p = h_val (hrs_mem (hrs h)) p"
      apply (subst l_h)
      apply (subst read_write_same)
      apply simp
      done
  next
    fix p :: "'a ptr" and s
    assume p: "\<forall>a\<in>ptr_span p. root_ptr_valid (hrs_htd (hrs s)) (PTR(stack_byte) a)"
    moreover
    { fix f w and r :: "'t \<Rightarrow> 'a ptr \<Rightarrow> 'a \<Rightarrow> 'a" and u n
      assume "typ_heap_simulation_of_field l hrs hrs_upd heap_typing_upd f r w"
        "field_lookup (typ_uinfo_t TYPE('a)) f 0 = Some (u, n)"
      with p have "r (l s) p ZERO('a) = ZERO('a)"
        unfolding typ_heap_simulation_of_field_def
        by (auto simp: field_ti_def field_lookup_typ_uinfo_t_Some typ_heap_simulation_of_field_def
                 dest!: field_lookup_uinfo_Some_rev) }
    note this[simp]
    from * fs_exists len have "fold (\<lambda>r. r (l s) p) rs ZERO('a) = ZERO('a)"
      by (induction fs arbitrary: rs ws)
         (auto simp: length_Suc_conv simp del: len)
    ultimately show "R (l s) p = ZERO('a)"
      unfolding R by (simp add: r_stack)
  next
    { fix d p f
      have "W p f o heap_typing_upd d = heap_typing_upd d o W p f"
        apply (rule disj)
        subgoal using heap_typing_u by (simp add: fun_eq_iff)
        using * len
        apply (induction fs arbitrary: ws rs)
        apply (auto simp add: length_Suc_conv typ_heap_simulation_of_field_def simp del: len)
        done
      then show "heap_typing_upd d (W p f h) = W p f (heap_typing_upd d h)" for h
        by (simp add: fun_eq_iff) }
    note heap_typing_W = this

    show "V (W p' f h) p = V h p" for p' f h p
      unfolding V
      apply (subst hrs.upd_same[symmetric, of "\<lambda>_. heap_typing h", OF refl])
      apply (subst heap_typing_W[symmetric])
      apply (subst hrs.get_upd)
      ..
  qed (simp_all add: V)
qed

lemma typ_heap_simulationI_no_addressable:
  fixes R :: "'t \<Rightarrow> 'a::{xmem_type, stack_type} ptr \<Rightarrow> 'a"
  assumes "heap_typing_simulation \<T> hrs hrs_upd heap_typing heap_typing_upd l"
  assumes R_u: "lense R u"
  assumes fs: "map_of \<T> (typ_uinfo_t TYPE('a)) = None"
    and l_u: "\<And>(p::'a ptr) (x::'a) (s::'b).
      PTR_VALID('a) (hrs_htd (hrs s)) p \<Longrightarrow>
      l (hrs_upd (write_dedicated_heap p x) s) = u (upd_fun p (\<lambda>old. merge_addressable_fields old x)) (l s)"
    and heap_typing_u: "\<And>x d h. heap_typing_upd d (u x h) = u x (heap_typing_upd d h)"
    and r_stack:
      "\<And>p s. \<forall>a\<in>ptr_span p. root_ptr_valid (hrs_htd (hrs s)) (PTR(stack_byte) a) \<Longrightarrow>
        R (l s) p = ZERO(_)"
  assumes V:
    "\<And>h p. V h p \<longleftrightarrow> PTR_VALID('a) (heap_typing h) p"
  assumes W:
    "\<And>p f h. W p f h = u (\<lambda>h'. h'(p := f (h' p))) h"
  shows "typ_heap_simulation_open_types \<T> l R W V hrs hrs_upd heap_typing heap_typing_upd"
proof -
  interpret hrs: heap_typing_simulation \<T> hrs hrs_upd heap_typing heap_typing_upd l by fact
  interpret lense R u by fact

  have [simp]: "merge_addressable_fields = (\<lambda>a b::'a. b)"
    by (simp add: fun_eq_iff addressable_fields_def fs)

  interpret pointer_lense R W
    using pointer_lense_of_lense_fld[where 'd='a, OF R_u, of "[]"]
    by (simp add: W[abs_def] upd_fun_def[abs_def])

  interpret write_simulation hrs hrs_upd l V W
    apply (rule hrs.write_simulation_alt)
    subgoal by (simp add: V)
    subgoal for h p x
      unfolding W V
      using l_u[of h p x]
      by (simp add: write_dedicated_heap_def heap_upd_const upd_fun_def[abs_def])
    done

  show ?thesis
  proof
    fix h p assume V_p: "V (l h) p"
    then show "c_guard p" by (simp add: ptr_valid.ptr_valid_c_guard V)

    have l_h: "l h = W p (\<lambda>x. h_val (hrs_mem (hrs h)) p) (l h)"
      apply (subst write_commutes[OF V_p, symmetric])
      apply (subst hrs.t_hrs.heap.upd_same)
      apply (cases "hrs h")
      apply (simp_all add: hrs_mem_update_def hrs_mem_def xmem_type_class.heap_update_id)
      done

    show "R (l h) p = h_val (hrs_mem (hrs h)) p"
      apply (subst l_h)
      apply (subst read_write_same)
      apply simp
      done
  next
    show "V (W p' f h) p = V h p" for p' f h p
      unfolding W V
      apply (subst hrs.upd_same[symmetric, of "\<lambda>_. heap_typing h", OF refl])
      apply (subst heap_typing_u[symmetric])
      apply (subst hrs.get_upd)
      ..
  qed (simp_all add: V W heap_typing_u r_stack)
qed

lemma typ_heap_simulationI_all_addressable:
  fixes R :: "'t \<Rightarrow> 'a::{xmem_type, stack_type} ptr \<Rightarrow> 'a"
  assumes hrs: "heap_typing_simulation \<T> hrs hrs_upd heap_typing heap_typing_upd l"
  assumes fs: "map_of \<T> (typ_uinfo_t TYPE('a)) = Some fs"
  assumes len[simp]: "length rs = length fs" "length ws = length fs"
  assumes *:
    "list_all (\<lambda>(f, r, w). typ_heap_simulation_of_field l hrs hrs_upd heap_typing_upd f r w) (zip fs (zip rs ws))"
    and **: "distinct_prop (\<lambda>(f1, w1) (f2, w2).
        disj_fn f1 f2 \<longrightarrow> pointer_writer_disjnt_eq w1 w2)
      (zip fs ws)"
  assumes all: "\<And>a b. fold (\<lambda>x. merge_ti (the (field_ti TYPE('a) x)) a) fs b = a"
  assumes V:
    "\<And>h p. V h p \<longleftrightarrow> PTR_VALID('a) (heap_typing h) p"
  assumes R:
    "\<And>h p x. R h p = fold (\<lambda>r. r h p) rs x"
  assumes W:
    "\<And>p f h. W p f h = fold (\<lambda>w. w p (f (R h p))) ws h"
  shows "typ_heap_simulation_open_types \<T> l R W V hrs hrs_upd heap_typing heap_typing_upd \<and>
    (\<forall>w. (\<forall>x. list_all (\<lambda>w'. pointer_writer_disjnt (\<lambda>p. w' p x) w) ws) \<longrightarrow>
      (\<forall>f. pointer_writer_disjnt (\<lambda>p. W p f) w)) \<and>
    (\<forall>(w::'t \<Rightarrow> 't) p.
      (\<forall>x. list_all (\<lambda>w'. w' p x \<circ> w = w \<circ> w' p x) ws) \<longrightarrow>
      (\<forall>f. W p f \<circ> w = w \<circ> W p f))"
    (is "?t1 \<and> (\<forall>w. ?ws w \<longrightarrow> (\<forall>f. ?t2 f w)) \<and> (\<forall>w p. ?ws2 p w \<longrightarrow> (\<forall>f. ?t3 p f w))")
proof (intro conjI allI impI)
  interpret hrs: heap_typing_simulation \<T> hrs hrs_upd heap_typing heap_typing_upd l by fact

  have [simp]: "length (addressable_fields TYPE('a)) = length fs"
    by (simp add: addressable_fields_def fs)

  have "list_all (\<lambda>f. \<exists>u n. field_lookup (typ_uinfo_t TYPE('a)) f 0 = Some (u, n))
    (map fst (zip fs (zip rs ws)))"
    using wf_\<T>[OF fs] by auto
  then have fs_exists:
    "list_all (\<lambda>x. \<exists>u n. field_lookup (typ_uinfo_t TYPE('a)) (fst x) 0 = Some (u, n))
      (zip fs (zip rs ws))"
    by (simp add: list.pred_map comp_def del: len)

  have coer_eq[simp]: "merge_addressable_fields = (\<lambda>a b::'a. a)"
    by (simp add: merge_ti_list_def addressable_fields_def fold_map fs fun_eq_iff comp_def all)

  have dist: "distinct_prop disj_fn fs"
    using \<T>_distinct[OF fs] .

  interpret pointer_lense R W
    apply (rule pointer_lense_of_partials[
      of "map merge_ti (map snd (addressable_fields TYPE('a)))" rs ws, OF _ _ _ _ _ _ R])
    subgoal by simp
    subgoal by simp
    subgoal
      apply (simp add: zip_map1 list.pred_map addressable_fields_def fs split_beta' comp_def)
      using list_all_conj[OF * fs_exists]
      apply (rule list.pred_mono_strong)
      apply (auto simp: field_ti_def field_lookup_typ_uinfo_t_Some typ_heap_simulation_of_field_def
                  dest!: field_lookup_uinfo_Some_rev)
      done
    subgoal for a b c
      apply (simp add: distinct_prop_map addressable_fields_def fs)
      apply (rule distinct_prop_mono[OF _ dist])
      using wf_\<T>[OF fs]
      apply (intro disjnt_scene_merge_ti[THEN disjnt_sceneD,
        OF option.collapse[symmetric] option.collapse[symmetric]])
      apply (auto simp: list.pred_set field_ti_def disj_fn_def
                  dest!: field_lookup_uinfo_Some_rev)
      done
    subgoal
      using ** dist
      apply (clarsimp simp add: distinct_prop_iff_nth fun_eq_iff pointer_writer_disjnt_eq_def[abs_def]
                             distinct_conv_nth disj_fn_def)
      apply metis
      done
    subgoal by (simp add: addressable_fields_def fs fold_map comp_def all)
    subgoal by (rule W)
    done

  have "list_all (\<lambda>(f, w). \<forall>t u n h p x.
        field_ti TYPE('a) f = Some t \<longrightarrow>
        field_lookup (typ_uinfo_t TYPE('a)) f 0 = Some (u, n) \<longrightarrow>
        ptr_valid_u u (hrs_htd (hrs h)) &(p\<rightarrow>f) \<longrightarrow>
        l (hrs_upd (hrs_mem_update (heap_upd_list (size_td u) &(p\<rightarrow>f) (access_ti t x))) h) =
          w p x (l h))
     (map (\<lambda>frw. (fst frw, snd (snd frw))) (zip fs (zip rs ws)))"
    unfolding list.pred_map
    using * by (rule list.pred_mono_strong) (auto simp:  typ_heap_simulation_of_field_def)
  also have "map (\<lambda>frw. (fst frw, snd (snd frw))) (zip fs (zip rs ws)) = zip fs ws"
    by (simp add: list_eq_iff_nth_eq)
  finally have fs_ws: "list_all2 (\<lambda>f w. \<forall>t u n h p x.
        field_ti TYPE('a) f = Some t \<longrightarrow>
        field_lookup (typ_uinfo_t TYPE('a)) f 0 = Some (u, n) \<longrightarrow>
        ptr_valid_u u (hrs_htd (hrs h)) &(p\<rightarrow>f) \<longrightarrow>
        l (hrs_upd (hrs_mem_update (heap_upd_list (size_td u) &(p\<rightarrow>f) (access_ti t x))) h) =
          w p x (l h))
     fs ws"
    by (subst (asm) list_all_zip_iff_list_all2; simp)

  have V_l: "\<And>h p. V (l h) p \<longleftrightarrow> PTR_VALID('a) (hrs_htd (hrs h)) p"
    by (simp add: V)

  interpret write_simulation hrs hrs_upd l V W
    apply (rule write_simulationI[OF fs hrs, of ws "\<lambda>x y. y" V _ R])
    apply (rule fs_ws)
    apply (simp add: write_dedicated_heap_def heap_upd_id hrs_mem_update_id3 flip: id_def)
    apply (simp add: id_def)
    apply (rule V_l)
    apply (rule W)
    done

  show "?t2 f w" if *: "?ws w" for w f
    apply (rule pointer_writer_disjnt_replace_by_const)
    apply (simp add: W[abs_def])
    apply (intro pointer_writer_disjnt_fold_left *[rule_format])
    done

  show disj: "?t3 p f w" if *: "?ws2 p w" for p f w
  proof (standard, unfold comp_def)
    fix h
    have w_W_const: "w (W p (\<lambda>x. c) h) = W p (\<lambda>x. c) (w h)" for c h
      using *[rule_format, of c]
      apply (simp add: W)
      apply (induction ws arbitrary: h)
      apply (auto simp: fun_eq_iff)
      done
    have R_eq: "R (w h) p = R h p"
      apply (subst write_same[of "\<lambda>_. R h p" h p, OF refl, symmetric])
      apply (subst w_W_const)
      apply (subst read_write_same)
      apply (rule refl)
      done

    show "W p f (w h) = w (W p f h)"
      by (simp add: R_eq write_cong[of f _ _ "\<lambda>_. f (R h p)"] w_W_const)
  qed

  show ?t1
  proof
    fix h p assume V_p: "V (l h) p"
    then show "c_guard p" by (simp add: ptr_valid.ptr_valid_c_guard V)

    have l_h: "l h = W p (\<lambda>x. h_val (hrs_mem (hrs h)) p) (l h)"
      apply (subst write_commutes[OF V_p, symmetric])
      apply (subst hrs.t_hrs.heap.upd_same)
      apply (cases "hrs h")
      apply (simp_all add: hrs_mem_update_def hrs_mem_def xmem_type_class.heap_update_id)
      done

    show "R (l h) p = h_val (hrs_mem (hrs h)) p"
      apply (subst l_h)
      apply (subst read_write_same)
      apply simp
      done
  next
    fix p :: "'a ptr" and s
    assume p: "\<forall>a\<in>ptr_span p. root_ptr_valid (hrs_htd (hrs s)) (PTR(stack_byte) a)"
    moreover
    { fix f w and r :: "'t \<Rightarrow> 'a ptr \<Rightarrow> 'a \<Rightarrow> 'a" and u n
      assume "typ_heap_simulation_of_field l hrs hrs_upd heap_typing_upd f r w"
        "field_lookup (typ_uinfo_t TYPE('a)) f 0 = Some (u, n)"
      with p have "r (l s) p ZERO('a) = ZERO('a)"
        unfolding typ_heap_simulation_of_field_def
        by (auto simp: field_ti_def field_lookup_typ_uinfo_t_Some typ_heap_simulation_of_field_def
                 dest!: field_lookup_uinfo_Some_rev) }
    note this[simp]
    from * fs_exists len have "fold (\<lambda>r. r (l s) p) rs ZERO('a) = ZERO('a)"
      by (induction fs arbitrary: rs ws)
         (auto simp: length_Suc_conv simp del: len)
    ultimately show "R (l s) p = ZERO('a)"
      unfolding R[of _ _ "ZERO('a)"] by simp
  next
    { fix p f d
      have "W p f o heap_typing_upd d = heap_typing_upd d o W p f"
        apply (rule disj)
        using * len
        apply (induction fs arbitrary: ws rs)
        apply (auto simp add: length_Suc_conv typ_heap_simulation_of_field_def simp del: len)
        done
      then show "heap_typing_upd d (W p f h) = W p f (heap_typing_upd d h)" for h
        by (simp add: fun_eq_iff) }
    note heap_typing_W = this

    show "V (W p' f h) p = V h p" for p' f h p
      unfolding V
      apply (subst hrs.upd_same[symmetric, of "\<lambda>_. heap_typing h", OF refl])
      apply (subst heap_typing_W[symmetric])
      apply (subst hrs.get_upd)
      ..
  qed (simp_all add: V)
qed

end

definition
  field_with_lense ::
    "qualified_field_name \<Rightarrow> ('a::c_type \<Rightarrow> 'b::c_type) \<Rightarrow> (('b \<Rightarrow> 'b) \<Rightarrow> 'a \<Rightarrow> 'a) \<Rightarrow> bool"
where
  "field_with_lense f g u \<longleftrightarrow>
    field_ti TYPE('a) f = Some (adjust_ti (typ_info_t TYPE('b)) g (u o (\<lambda>x _. x))) \<and>
    lense g u"

lemma update_desc_id: "update_desc (\<lambda>x. x) (\<lambda>x _. x) = id"
  by (simp add: fun_eq_iff update_desc_def)

lemma field_with_lense_Nil: "field_with_lense [] (\<lambda>x. x) (\<lambda>f x. f x)"
  by (simp add: field_with_lense_def lense_def comp_def adjust_ti_def update_desc_id map_td_id(1))

lemma field_with_lense_Cons:
  fixes g :: "'a::mem_type \<Rightarrow> 'b::mem_type" and gs :: "'b \<Rightarrow> 'c::mem_type"
  assumes fs: "field_with_lense fs gs us"
  assumes f: "field_ti TYPE('a) [f] = Some (adjust_ti (typ_info_t TYPE('b)) g (u o (\<lambda>x _. x)))"
  assumes g_u: "fg_cons g (u o (\<lambda>x _. x))"
  assumes u: "\<And>f x. u f x = u (\<lambda>_. f (g x)) x"
  shows "field_with_lense (f # fs) (\<lambda>x. gs (g x)) (\<lambda>f. u (us f))"
  unfolding field_with_lense_def
proof
  from fs obtain n where fs:
    "field_lookup (typ_info_t TYPE('b)) fs 0 =
      Some (adjust_ti (typ_info_t TYPE('c)) gs (us o (\<lambda>x _. x)), n)"
    and gs_us: "lense gs us"
    by (auto simp add: field_with_lense_def field_ti_def split: option.splits)

  have g_u: "lense g u"
    using g_u
    apply (rule lense_of_fg_cons')
    apply (rule u)
    done
  then interpret lense g u .
  show "lense (\<lambda>x. gs (g x)) (\<lambda>f. u (us f))"
    using g_u gs_us by (rule lense_compose)

  have "(\<lambda>x. gs (g x)) = gs \<circ> g"
    "(\<lambda>v x. u (\<lambda>_. us (\<lambda>_. v) (g x)) x) = (\<lambda>f. u (us f)) \<circ> (\<lambda>x _. x)"
    by (simp_all add: fun_eq_iff cong: upd_cong)
  with field_ti_append_field_lookup[OF f, of fs 0]
  show "field_ti TYPE('a) (f # fs) =
    Some (adjust_ti (typ_info_t TYPE('c)) (\<lambda>x. gs (g x)) ((\<lambda>f. u (us f)) \<circ> (\<lambda>x _. x)))"
    unfolding field_lookup_adjust_ti2[OF fs]
    by (simp add: adjust_ti_adjust_ti)
qed

lemma (in typ_heap_simulation_open_types) typ_heap_simulation_of_field:
  assumes f: "field_with_lense f g u"
  assumes v: "\<And>h p. PTR_VALID('a) (hrs_htd (t_hrs h)) p \<Longrightarrow> v (st h) p"
  assumes g_zero: "g ZERO('x::mem_type) = ZERO('a)"
  shows "typ_heap_simulation_of_field st t_hrs t_hrs_update heap_typing_upd f
     (\<lambda>h p. u (\<lambda>_. r h (PTR('a) &(p\<rightarrow>f))))
     (\<lambda>p x. w (PTR('a) &(p\<rightarrow>f)) (\<lambda>_. g x))"
proof -
  have g_u: "lense g u" using f by (simp add: field_with_lense_def)
  then interpret lense g u .

  have [simp]: "fg_cons g (u \<circ> (\<lambda>x _. x))"
    by (rule fg_cons)
  obtain n where [simp]:
    "field_lookup (typ_uinfo_t TYPE('x)) f 0 = Some (typ_uinfo_t TYPE('a), n)"
    using f
    by (auto simp: field_ti_def field_lookup_typ_uinfo_t_Some field_with_lense_def
             split: option.splits)
  have sz: "size_td (typ_info_t TYPE('a)) = size_of TYPE('a)"
    by (simp add: size_of_def)

  have p_f_eq: "&(p\<rightarrow>f) = ptr_val (PTR('c) &(p\<rightarrow>f))" for p :: "'x ptr"
    by simp

  have ptr_span_subset: "ptr_span (PTR('a) &(p\<rightarrow>f)) \<subseteq> ptr_span p" for  p :: "'x ptr"
    using field_tag_sub'[where 'a='x, of "f" _ _ p] by (simp add: size_of_def)

  have u_zero: "u (\<lambda>_. ZERO('a)) ZERO('x) = ZERO('x)"
    by (simp add: upd_same g_zero)

  show ?thesis using f
    apply (clarsimp simp: typ_heap_simulation_of_field_def field_with_lense_def, intro conjI allI impI)
    subgoal by (simp add: heap_typing_upd_write_commute fun_eq_iff)
    subgoal
      apply (rule partial_pointer_lenseI[OF g_u])
      apply (rule pointer_lense_field_lvalue)
      apply assumption
      apply (simp add: size_of_def)
      done
    subgoal for p
      using ptr_span_subset[of p]
      by (subst sim_stack_stack_byte_zero') (auto simp: u_zero)
    subgoal
      apply (subst sz)
      apply (subst p_f_eq)
      apply (subst heap_update_eq_heap_upd_list[symmetric])
      apply (rule write_commutes)
      apply (simp add: v ptr_valid_def)
      done
    done
qed

context pointer_array_lense
begin

lemma pointer_writer_disjnt_heap_array_map[pointer_writer_disjnt_intros]:
  assumes w': "\<And>x. pointer_writer_disjnt (\<lambda>p. w p x) w'"
  shows "pointer_writer_disjnt (\<lambda>p. heap_array_map p x) w'"
  apply (rule array.pointer_writer_disjnt_replace_by_const)
  apply (simp only: heap_array_map_def[abs_def])
  apply (rule pointer_writer_disjnt_fold_left)
  apply (clarsimp simp add: list_all_iff)
  apply (rule pointer_writer_disjnt_ptr_map_left[OF w' ptr_span_array_ptr_index_subset_ptr_span])
  apply simp
  done

lemma pointer_writer_disjnt_heap_array_map_right[pointer_writer_disjnt_intros]:
  "(\<And>x. pointer_writer_disjnt w' (\<lambda>p. w p x)) \<Longrightarrow> pointer_writer_disjnt w' (\<lambda>p. heap_array_map p x)"
  by (metis pointer_writer_disjnt_heap_array_map pointer_writer_disjnt_sym)

lemma disjnt_comp_heap_array_map[disjnt_heap_fields_comp]:
  assumes w': "\<And>q x. w q x \<circ> w' = w' \<circ> w q x"
  shows "heap_array_map p x \<circ> w' = w' \<circ> heap_array_map p x"
proof -
  have "heap_array_map p (\<lambda>_. c) \<circ> w' = w' \<circ> heap_array_map p (\<lambda>_. c)" for c
    apply (rule comp_commute_of_fold)
    apply (subst heap_array_map_def[abs_def], rule refl)
    apply (simp add: w' list_all_iff)
    done
  then have *: "w' (heap_array_map p (\<lambda>_. c) h) = heap_array_map p (\<lambda>_. c) (w' h)" for c h
    by (simp add: fun_eq_iff)

  have [simp]: "heap_array (w' h) p = heap_array h p" for h
    apply (subst array.write_same[symmetric, of "\<lambda>_. heap_array h p", OF refl])
    apply (subst *)
    apply (subst array.read_write_same)
    apply (rule refl)
    done
  show ?thesis
    apply (rule ext)
    subgoal for h
      apply (clarsimp simp add: fun_eq_iff)
      apply (subst (1 2) array.write_cong[where f'="\<lambda>_. x (heap_array h p)"])
      apply (simp_all flip: *)
      done
    done
qed

end

lemma (in open_types) valid_array_of_ptr_valid_arrayI:
  fixes r :: "'t \<Rightarrow> 'a::{xmem_type, array_outer_max_size} ptr \<Rightarrow> 'a"
  fixes p :: "('a['n::{finite, array_max_count}]) ptr"
  assumes f: "map_of \<T> (typ_uinfo_t TYPE('a['n])) = Some (array_fields CARD('n))"
  assumes p: "PTR_VALID('a['n]) h' p"
  assumes v: "\<And>p. PTR_VALID('a) h' p \<Longrightarrow> v h p"
  shows "valid_array_base.valid_array v h p"
  unfolding valid_array_base.valid_array_def
proof (intro allI impI v)
  fix n assume n: "n < CARD('n)"
  note fl_array = field_lookup_array[OF n, THEN field_lookup_typ_uinfo_t_Some]

  have "[replicate n CHR ''1''] \<in> set (array_fields CARD('n))"
    using n by (auto simp: array_fields_def)

  note * = ptr_valid_u_step[OF f this fl_array p[unfolded ptr_valid_def]]
  have "field_offset_untyped (typ_uinfo_t TYPE('a['n])) [replicate n CHR ''1''] =
    n * size_of TYPE('a)"
    by (simp add: field_offset_untyped_def fl_array)
  with * show "PTR_VALID('a) h' (array_ptr_index p False n)"
    by (simp add: n array_ptr_index_def ptr_add_def ptr_valid_def typ_uinfo_t_def)
qed

lemma (in open_types) valid_array_of_ptr_valid_array1[simp]:
  fixes r :: "'t \<Rightarrow> 'a::{xmem_type, array_outer_max_size} ptr \<Rightarrow> 'a"
  fixes p :: "('a['n::{finite, array_max_count}]) ptr"
  assumes f:
    "map_of \<T> (typ_uinfo_t TYPE('a['n])) = Some (array_fields CARD('n))"
  assumes p: "PTR_VALID('a['n]) (heap_typing h) p"
  shows "valid_array_base.valid_array (\<lambda>h. PTR_VALID('a) (heap_typing h)) h p"
  by (rule valid_array_of_ptr_valid_arrayI[of "heap_typing h", OF f p])

lemma (in open_types) valid_array_of_ptr_valid_array2[simp]:
  fixes r :: "'t \<Rightarrow> 'a::{xmem_type, array_inner_max_size} ptr \<Rightarrow> 'a"
  fixes p :: "('a['n::{finite, array_max_count}]['m::{finite, array_max_count}]) ptr"
  assumes f2:
    "map_of \<T> (typ_uinfo_t TYPE('a['n]['m])) = Some (array_fields CARD('m))"
  assumes f1:
    "map_of \<T> (typ_uinfo_t TYPE('a['n])) = Some (array_fields CARD('n))"
  assumes p: "PTR_VALID('a['n]['m]) (heap_typing h) p"
  shows "valid_array_base.valid_array (valid_array_base.valid_array
    (\<lambda>h. PTR_VALID('a) (heap_typing h))) h p"
  apply (rule valid_array_of_ptr_valid_arrayI[of "heap_typing h", OF f2 p])
  apply (rule valid_array_of_ptr_valid_array1[OF f1])
  apply assumption
  done

lemma (in open_types) ptr_valid_unsigned[simp]:
  "PTR_VALID('a::len8 signed word) h p \<longleftrightarrow>
    PTR_VALID('a::len8 word) h (PTR_COERCE('a signed word \<rightarrow> 'a word) p)"
  by (simp add: typ_uinfo_t_signed_word_word_conv ptr_valid_def)

lemma ucast_zero_word:
  "UCAST('a::len8 \<rightarrow> 'a signed) ZERO('a word) = ZERO('a signed word)"
  using len8_bytes[where 'a='a]
  apply (simp add: zero_def)
  apply (subst from_bytes_signed_word)
  apply (simp_all add: size_of_def typ_info_word ucast_ucast_id)
  done

definition signed_heap:: 
  "('s \<Rightarrow> 'a::len word ptr \<Rightarrow> 'a word) \<Rightarrow> ('s \<Rightarrow> 'a signed word ptr \<Rightarrow> 'a signed word)" where
  "signed_heap h s = UCAST ('a::len \<rightarrow> 'a signed) o (h s) o PTR_COERCE('a signed word \<rightarrow> 'a word)"

lemma signed_heap_apply[simp]: 
  "signed_heap h s p = UCAST ('a::len \<rightarrow> 'a signed) (h s (PTR_COERCE('a signed word \<rightarrow> 'a word) p))"
  by (simp add: signed_heap_def)

lemma signed_typ_heap_simulation_of_typ_heap_simulation:
  fixes r :: "_ \<Rightarrow> _ \<Rightarrow> 'a::len8 word"
  assumes r:
    "typ_heap_simulation_open_types \<T> st r w v t_hrs t_hrs_update heap_typing heap_typing_upd"
  shows "typ_heap_simulation_open_types \<T> st
    (signed_heap r)
    (\<lambda>p m. w (PTR_COERCE('a signed word \<rightarrow> 'a word) p) (\<lambda>w. UCAST('a signed \<rightarrow> 'a) (m (UCAST('a \<rightarrow> 'a signed) w))))
    (\<lambda>h p. v h (PTR_COERCE('a signed word \<rightarrow> 'a word) p))
    t_hrs t_hrs_update heap_typing heap_typing_upd"
proof -
  interpret typ_heap_simulation_open_types \<T> st r w v t_hrs t_hrs_update heap_typing heap_typing_upd
    by fact
  interpret cast: pointer_lense
    "signed_heap r"
    "\<lambda>p m. w (PTR_COERCE('a signed word \<rightarrow> 'a word) p)
      (\<lambda>w. UCAST('a signed \<rightarrow> 'a) (m (UCAST('a \<rightarrow> 'a signed) w)))"
    unfolding signed_heap_def comp_def
    by (rule pointer_lense_ucast_signed) unfold_locales
  have [simp]: "c_guard p \<longleftrightarrow> c_guard (PTR_COERCE('a signed word \<rightarrow> 'a word) p)" for p
    apply (intro c_guard_ptr_coerce[symmetric])
    apply (simp_all add: size_of_signed_word align_of_signed_word)
    done
  note scast_ucast_norm[simp del]
  note ucast_ucast_id[simp]
  show ?thesis
    apply unfold_locales 
    apply (simp_all add: ptr_valid_unsigned ptr_valid_imp_v
        read_commutes h_val_signed_word write_padding_commutes heap_typing_upd_write_commute)
    apply (subst heap_update_padding_signed_word(1)[symmetric])
    apply (subst write_padding_commutes)
    apply (simp_all add: size_of_signed_word scast_ucast_down_same valid_implies_c_guard)
    apply (rule valid_same_typ_desc, simp)
    apply (simp add: sim_stack_stack_byte_zero')
    apply (simp add: ucast_zero_word)
    done
qed

lemma array_typ_heap_simulation_of_typ_heap_simulation:
  fixes r :: "_ \<Rightarrow> _ \<Rightarrow> 'a::{stack_type, xmem_type, array_outer_max_size}"
  assumes "typ_heap_simulation_open_types \<T> st r w v t_hrs t_hrs_update heap_typing heap_typing_upd"
  assumes f: "map_of \<T> (typ_uinfo_t TYPE('a['n::{finite, array_max_count}])) =
    Some (array_fields CARD('n))"
  shows
    "typ_heap_simulation_open_types \<T> st
      (pointer_array_lense.heap_array r :: _ \<Rightarrow> ('a['n]) ptr \<Rightarrow> _)
      (pointer_array_lense.heap_array_map r w)
      (valid_array_base.valid_array v)
      t_hrs t_hrs_update heap_typing heap_typing_upd"
proof -
  interpret sim: typ_heap_simulation_open_types \<T> st r w v t_hrs t_hrs_update by fact
  interpret array_typ_heap_simulation st r w v t_hrs t_hrs_update ..
  show ?thesis
  proof
    fix p :: "('a['n]) ptr" and d f
    have "heap_array_map p f o heap_typing_upd d = heap_typing_upd d o heap_array_map p f"
      by (intro disjnt_comp_heap_array_map)
         (simp add: fun_eq_iff sim.heap_typing_upd_write_commute)
    then show "heap_typing_upd d (heap_array_map p f h) = heap_array_map p f (heap_typing_upd d h)" for h
      by (simp add: fun_eq_iff)
    show "heap_array (st s) p = ZERO(_)"
      if p: "\<forall>a\<in>ptr_span p. root_ptr_valid (hrs_htd (t_hrs s)) (PTR(stack_byte) a)" for s
      apply (intro array_ext)
      apply (simp add: array_index_zero)
      apply (intro sim.sim_stack_stack_byte_zero')
      subgoal for i
        using ptr_span_array_ptr_index_subset_ptr_span[of i p False] p
        apply auto
        done
      done
    show "sim.ptr_valid (heap_typing h) p \<Longrightarrow> valid_array h p" for h
      by (rule sim.valid_array_of_ptr_valid_arrayI[OF f, of "heap_typing h"])
         (simp_all add: sim.ptr_valid_imp_v)
  qed simp
qed

lemma (in typ_heap_simulation_open_types) stack_simulation_heap_typingI:
  assumes hrs: "heap_typing_simulation \<T> t_hrs t_hrs_update heap_typing heap_typing_upd st"
  assumes sim_stack_alloc_heap_typing:
    "\<And>p d s n.
      (p, d) \<in> stack_allocs n \<S> TYPE('a) (hrs_htd (t_hrs s)) \<Longrightarrow>
        st (t_hrs_update (hrs_mem_update (fold (\<lambda>i. heap_update (p +\<^sub>p int i) c_type_class.zero) [0..<n]) \<circ> hrs_htd_update (\<lambda>_. d)) s) =
        (heap_typing_upd (\<lambda>_. d) (st s))"
  assumes sim_stack_release_heap_typing:
    "\<And>(p::'a ptr) s n. (\<And>i. i < n \<Longrightarrow> root_ptr_valid (hrs_htd (t_hrs s)) (p +\<^sub>p int i)) \<Longrightarrow>
      st (t_hrs_update (hrs_htd_update (stack_releases n p)) s) =
        heap_typing_upd (stack_releases n p)
         (st (t_hrs_update (hrs_mem_update (fold (\<lambda>i. heap_update (p +\<^sub>p int i) c_type_class.zero) [0..<n])) s))"
  shows "stack_simulation_heap_typing st r w t_hrs t_hrs_update heap_typing heap_typing_upd \<S> \<T>"
proof -
  interpret hrs: heap_typing_simulation \<T> t_hrs t_hrs_update heap_typing heap_typing_upd st by fact
  interpret write_simulation t_hrs t_hrs_update st "\<lambda>t p. open_types.ptr_valid \<T> (heap_typing t) p" w
    apply (rule hrs.write_simulation_alt)
    apply simp
    apply (simp_all add: ptr_valid.ptr_valid_c_guard ptr_valid_imp_v write_commutes read_commutes)
    done
  interpret typ_heap_simulation
    st r w "\<lambda>t p. open_types.ptr_valid \<T> (heap_typing t) p" t_hrs t_hrs_update
    by unfold_locales
       (simp_all add: ptr_valid.ptr_valid_c_guard ptr_valid_imp_v write_commutes read_commutes)
  show ?thesis
  proof
  qed (simp_all add: sim_stack_stack_byte_zero' sim_stack_alloc_heap_typing sim_stack_release_heap_typing)
qed


end
