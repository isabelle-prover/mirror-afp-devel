(*
 * Copyright (c) 2023 Apple Inc. All rights reserved.
 *
 * SPDX-License-Identifier: BSD-2-Clause
 *)

section "In Out Parameter Refinement"

theory In_Out_Parameters
  imports
    L2ExceptionRewrite
    L2Peephole
    TypHeapSimple 
    Stack_Typing
begin


lemma map_exn_catch_conv: "map_value (map_exn f) m = (m <catch> (\<lambda>r. throw (f r)))"
  apply (rule spec_monad_eqI)
  apply (clarsimp simp add: runs_to_iff)
  apply (auto simp add: runs_to_def_old map_exn_def split: xval_splits)
  done

abbreviation "L2_return x ns \<equiv>  liftE (L2_VARS (return x) ns)"

lemma L2_return_L2_gets_conv: "L2_return x ns = L2_gets (\<lambda>_. x) ns"
  unfolding L2_defs L2_VARS_def
  by (simp add: gets_return)


lemma return_L2_gets_conv: "(return x) = L2_gets (\<lambda>_. x) []"
  unfolding L2_defs L2_VARS_def
  by (simp add: gets_return)


definition (in heap_state)  
  IO_modify_heap_padding::"'a::mem_type ptr \<Rightarrow> ('s \<Rightarrow> 'a) \<Rightarrow> ('b::default, unit, 's) spec_monad" where
 "IO_modify_heap_padding p v = 
    state_select {(s, t). \<exists>bs. length bs = size_of (TYPE('a)) \<and> t = hmem_upd (heap_update_padding p (v s) bs) s}"

lemma (in heap_state) liftE_IO_modify_heap_padding: "liftE (IO_modify_heap_padding p v) = (IO_modify_heap_padding p v)"
  unfolding IO_modify_heap_padding_def
  apply (rule spec_monad_eqI)
  apply (auto simp add: runs_to_iff)
  done

abbreviation (in heap_state) IO_modify_heap_paddingE:: 
    "'a::mem_type ptr \<Rightarrow> ('s \<Rightarrow> 'a) \<Rightarrow> ('b, unit, 's) exn_monad" where
    "IO_modify_heap_paddingE p v \<equiv> liftE (IO_modify_heap_padding p v)"

lemma (in heap_state) no_fail_IO_modify_padding[simp]:  "succeeds (IO_modify_heap_padding p v) s"
  unfolding IO_modify_heap_padding_def
  apply (simp)
  using length_to_bytes_p by blast

lemma (in heap_state) no_fail_IO_modify_paddingE[simp]:  "succeeds (IO_modify_heap_paddingE p v) s"
  unfolding IO_modify_heap_padding_def
  apply (simp)
  using length_to_bytes_p by blast

named_theorems refines_right_eq

lemma (in heap_state) IO_modify_heap_paddingE_root_refines':
  fixes p::"'a::xmem_type ptr"
  fixes fld_update::"('b::xmem_type \<Rightarrow> 'b) \<Rightarrow> 'a \<Rightarrow> 'a"
  assumes fg_cons: "fg_cons fld (fld_update \<circ> (\<lambda>x _. x))"
  assumes fl: "field_lookup (typ_info_t TYPE('a)) f 0 = Some (adjust_ti (typ_info_t TYPE('b::xmem_type)) fld (fld_update \<circ> (\<lambda>x _. x)), n)"
  assumes cgrd: "c_guard p"
  shows "refines 
           (IO_modify_heap_paddingE (PTR('b) &(p\<rightarrow>f)) v)  
           (IO_modify_heap_paddingE p (\<lambda>s. (fld_update (\<lambda>_. v s)) (h_val (hmem s) p))) 
          s s ((=))"
proof -
  {
    fix r t
    assume exec: "reaches (IO_modify_heap_paddingE (PTR('b) &(p\<rightarrow>f)) v) s r t" 
    have "reaches (IO_modify_heap_paddingE p (\<lambda>s. fld_update (\<lambda>_. v s) (h_val (hmem s) p))) s r t"
    proof -
      from exec obtain bs where
        r: "r = Result ()" and bs: "length bs = size_of TYPE('b)" and
        t: "t = hmem_upd (heap_update_padding (PTR('b) &(p\<rightarrow>f)) (v s) bs) s" 
        unfolding liftE_IO_modify_heap_padding
        by (auto simp add:  IO_modify_heap_padding_def)
      note root_conv = heap_update_padding_field_root_conv'' [OF fl fg_cons cgrd bs, where v="v s" and hp = "hmem s"]
      from bs cgrd fl have *: "length (super_update_bs bs (heap_list (hmem s) (size_of TYPE('a)) (ptr_val p)) n) = size_of TYPE('a)"
        apply (subst length_super_update_bs)
        subgoal
          by (metis add.commute field_lookup_offset_size heap_list_length size_of_tag typ_desc_size_update_ti typ_uinfo_size)
        subgoal
          using heap_list_length by blast
        done
      show ?thesis 
        unfolding liftE_IO_modify_heap_padding
        apply (clarsimp simp add: IO_modify_heap_padding_def r)
        using root_conv heap.upd_cong * t 
        by blast
    qed
  } note * = this
  show ?thesis
    using *   
    by (auto simp add: refines_def_old )
qed

lemma (in heap_state) IO_modify_heap_paddingE_root_refines'':
  fixes p::"'a::xmem_type ptr"
  fixes fld_update::"('b::xmem_type \<Rightarrow> 'b) \<Rightarrow> 'a \<Rightarrow> 'a"
  assumes fg_cons: "fg_cons fld (fld_update \<circ> (\<lambda>x _. x))"
  assumes fl: "field_ti TYPE('a) f = Some (adjust_ti (typ_info_t TYPE('b::xmem_type)) fld (fld_update \<circ> (\<lambda>x _. x)))"
  assumes cgrd: "c_guard p"
  shows "refines 
           (IO_modify_heap_paddingE (PTR('b) &(p\<rightarrow>f)) v)  
           (IO_modify_heap_paddingE p (\<lambda>s. (fld_update (\<lambda>_. v s)) (h_val (hmem s) p))) 
          s s ((=))"
proof -
  from fl obtain n where 
    "field_lookup (typ_info_t TYPE('a)) f 0 = Some (adjust_ti (typ_info_t TYPE('b::xmem_type)) fld (fld_update \<circ> (\<lambda>x _. x)), n)"
    using field_ti_field_lookupE by blast
  from IO_modify_heap_paddingE_root_refines' [OF fg_cons this cgrd]
  show ?thesis .
qed

lemma (in heap_state) IO_modify_heap_paddingE_root_refines [refines_right_eq]:
  fixes p::"'a::xmem_type ptr"
  fixes fld_update::"('b::xmem_type \<Rightarrow> 'b) \<Rightarrow> 'a \<Rightarrow> 'a"
  assumes v': "\<And>s. v' s = ((fld_update (\<lambda>_. v s)) (h_val (hmem s) p))"
  assumes fg_cons: "fg_cons fld (fld_update \<circ> (\<lambda>x _. x))"
  assumes fl: "field_ti TYPE('a) f = Some (adjust_ti (typ_info_t TYPE('b::xmem_type)) fld (fld_update \<circ> (\<lambda>x _. x)))"
  assumes cgrd: "c_guard p"
  shows "refines 
           (IO_modify_heap_paddingE (PTR('b) &(p\<rightarrow>f)) v)  
           (IO_modify_heap_paddingE p v')
          s s ((=))"
  unfolding v'
  by (rule IO_modify_heap_paddingE_root_refines'' [OF fg_cons fl cgrd])


lemma refines_subst_right:
  assumes f_g: "refines f g s t Q"
  assumes refines_eq: "refines g g' t t ((=))"
  shows "refines f g' s t Q"
  using f_g refines_eq
  by (force simp add: refines_def_old)
 
lemma refines_right_eq_id: "refines f f s s ((=))"
  by (force simp add: refines_def_old)

lemma refines_subst_left:
  assumes f_g: "refines f g s t Q"
  assumes f_eq: "run f s = run f' s"
  shows "refines f' g s t Q"
  using f_g f_eq
  apply (auto simp add: refines_def_old reaches_def succeeds_def)
  done

lemma refines_right_eq_L2_seq [refines_right_eq]:
  assumes f1: "refines f1 g1 s s ((=))"
  assumes f2: "\<And>v t. refines (f2 v) (g2 v) t t ((=))"
  shows "refines (L2_seq f1 f2) (L2_seq g1 g2) s s ((=))"
  unfolding L2_defs
  apply (rule refines_bind_bind_exn [OF f1])
  subgoal by auto
  subgoal by auto
  subgoal by auto
  subgoal using f2 by auto
  done


lemma refines_right_eq_L2_guard':
  assumes "Q s \<Longrightarrow> P s"
  assumes "Q s \<Longrightarrow> refines X X' s s (=)"
  shows "refines (L2_seq (L2_guard P) (\<lambda>_. X)) (L2_seq (L2_guard Q) (\<lambda>_. X')) s s ((=))"
  unfolding L2_defs
  apply (rule refines_bind'[OF
    refines_guard[THEN refines_strengthen[OF _ runs_to_partial_guard runs_to_partial_guard]]])
  apply (auto simp: assms)
  done

lemma refines_right_eq_L2_guard:
  assumes "Q \<Longrightarrow> P"
  assumes "Q \<Longrightarrow> refines X X' s s (=)"
  shows "refines (L2_seq (L2_guard (\<lambda>_. P)) (\<lambda>_. X)) (L2_seq (L2_guard (\<lambda>_. Q)) (\<lambda>_. X')) s s ((=))"
  using assms
  by (rule refines_right_eq_L2_guard')


lemma select_UNIV_L2_unknown_conv: "(select UNIV) = L2_unknown ns"
  unfolding L2_defs
  by simp

lemma select_singleton_conv: "((select ({x})) >>= g) = g x"
  apply (rule spec_monad_eqI)
  apply (auto simp add: runs_to_iff)
  done

lemma hd_UNIV: "hd ` UNIV \<subseteq> UNIV"
  by (rule subset_UNIV)

lemma hd_singleton: "hd ` {[x]} \<subseteq> {x}"
  by simp

lemma refines_select_right_witness:
  assumes "x \<in> X"
  assumes "refines f (g x) s t Q"
  shows "refines f ((select X) >>= g) s t Q"
  using assms
  using assms
  by (fastforce simp add: refines_def_old succeeds_bind reaches_bind)
  

lemma refines_bindE_right: 
  assumes f: "refines f f' s s' Q"
  assumes ll: "\<And>e e' t t'. Q (Exn e, t) (Exn e', t') \<Longrightarrow> R (Exn e, t) (Exn e', t')"
  assumes lr: "\<And>e v' t t'. Q (Exn e, t) (Result v', t') \<Longrightarrow> refines (throw e) (g' v') t t' R"
  assumes rl: "\<And>v e' t t'. Q (Result v, t) (Exn e', t') \<Longrightarrow> refines ((return v)) (throw e') t t' R"
  assumes rr: "\<And>v v' t t'. Q (Result v, t) (Result v', t') \<Longrightarrow> refines ((return v)) (g' v') t t' R"
  shows "refines f (f' >>= g') s s' R"
proof -
  have eq: "f = (f >>= (\<lambda>v. return v))"
    by simp
  show ?thesis
    apply (subst eq)
    using assms
    by (rule refines_bind_bind_exn)
qed

lemma refines_exec_modify_step_right: 
  assumes "refines (return x) g s (upd t) Q"
  shows "refines (return x) (do{ _ <- (modify (upd)); g }) s t Q"
  using assms
  by (auto simp add: refines_def_old reaches_bind succeeds_bind)

lemma (in heap_state) refines_exec_IO_modify_heap_padding_step_right: 
  fixes p:: "'a::mem_type ptr"
  assumes "
    refines (return x) g s 
       (hmem_upd (heap_update_padding p v (heap_list (hmem s) (size_of TYPE('a)) (ptr_val p) )) t) Q"
  shows "refines (return x) (do { _ <- IO_modify_heap_paddingE p (\<lambda>_. v); g }) s t Q"
  using assms unfolding liftE_IO_modify_heap_padding
  apply (clarsimp simp add: refines_def_old IO_modify_heap_padding_def reaches_bind succeeds_bind  )
  apply (metis heap_list_length)
  done


lemma (in heap_state) refines_exec_IO_modify_heap_padding_single_step_right: 
  fixes p:: "'a::mem_type ptr"
  assumes "Q (Result (), s) 
              (Result (), hmem_upd (heap_update_padding p (v t) (heap_list (hmem s) (size_of TYPE('a)) (ptr_val p))) t)"
  shows "refines (return ()) 
          (IO_modify_heap_paddingE p v) s t Q"
  using assms unfolding liftE_IO_modify_heap_padding
  apply (clarsimp simp add: refines_def_old IO_modify_heap_padding_def reaches_bind succeeds_bind)
  by (metis heap_list_length)

lemma (in heap_state) refines_exec_IO_modify_heap_padding_single_step_right_InL: 
  fixes p:: "'a::mem_type ptr"
  assumes "Q (Exn e, s) (Exn e', hmem_upd (heap_update_padding p (v t) (heap_list (hmem s) (size_of TYPE('a)) (ptr_val p))) t)"
  shows "refines (throw e) 
           (do { _ <- IO_modify_heap_paddingE p v;
                L2_throw e' ns
           })
          s t Q"
  unfolding L2_defs unfolding liftE_IO_modify_heap_padding
  using assms 
  apply (clarsimp simp add: refines_def_old IO_modify_heap_padding_def reaches_bind succeeds_bind Exn_def [symmetric])
  apply (metis heap_list_length)
  done

lemma refines_exec_gets_right: 
  assumes "Q (Result x, s) (Result (g t), t)"
  shows "refines (return x) (gets g) s t Q"
  using assms
  by (auto simp add: refines_def_old)


lemma refines_exec_L2_return_right: 
  assumes "Q (Result x, s) (Result w, t)"
  shows "refines (return (x)) (L2_return w ns) s t Q"
  using assms unfolding L2_VARS_def
  by (auto simp add: refines_def_old)

lemma f_catch_throw: "(f <catch> throw) = f"
  apply (rule spec_monad_eqI)
  apply (clarsimp simp add: runs_to_iff)
  apply (clarsimp simp add: runs_to_def_old)
  by (metis Exn_def default_option_def exception_or_result_cases not_None_eq)

lemma refines_L2_catch_right:
  assumes f: "refines f g s t Q"
  assumes Res_Res: "\<And>v v' s' t'. Q (Result v, s') (Result v', t') \<Longrightarrow> R (Result v, s') (Result v', t')"
  assumes Res_Exn: "\<And>v e' s' t'. Q (Result v, s') (Exn e', t') \<Longrightarrow> refines (return v) (h e') s' t' R"
  assumes Exn_Res: "\<And>e v' s' t'. Q (Exn e, s') (Result v', t') \<Longrightarrow> R (Exn e, s') (Result v', t')"
  assumes Exn_Exn: "\<And>e e' s' t'. Q (Exn e, s') (Exn e', t') \<Longrightarrow> refines (throw e) (h e') s' t' R"
  shows "refines f (L2_catch g h) s t R" unfolding L2_defs
  apply (subst f_catch_throw[symmetric])
  apply (rule refines_catch [OF f])
  subgoal using Exn_Exn by auto
  subgoal using Exn_Res by (auto simp add: refines_def_old Exn_def [symmetric])
  subgoal using Res_Exn by (auto simp add: refines_def_old Exn_def [symmetric])
  subgoal using Res_Res by auto
  done

lemma L2_seq_gets_app_conv: "run (L2_seq (L2_gets f ns) g) s = run (g (f s)) s"
  unfolding L2_defs
  apply (auto simp add: run_bind)
  done


lemma refines_project_right:
  assumes f_g: "refines f g s t Q"
  assumes "run g t = run (g' (prj t)) t"
  shows "refines f (L2_seq (L2_gets prj ns) g') s t Q"
  unfolding L2_defs
  using assms
  apply (clarsimp simp add: refines_def_old reaches_bind succeeds_bind)
  apply (auto simp add: succeeds_def reaches_def)
  done

lemma refines_project_guard_right:
  assumes f_g: "refines f (L2_seq (L2_guard P) (\<lambda>_. g)) s t Q"
  assumes "P t \<Longrightarrow> run g t = run (g' (prj t)) t"
  shows "refines f (L2_seq (L2_guard P) (\<lambda>_. (L2_seq (L2_gets prj ns) g'))) s t Q"
  using assms unfolding L2_defs
  apply (clarsimp simp add: refines_def_old reaches_bind succeeds_bind)
  apply (auto simp add: succeeds_def reaches_def)
  done



named_rules cguard_assms and alloc_assms and modifies_assms and disjoint_assms and
  disjoint_alloc and disjoint_stack_free and stack_ptr and h_val_globals_frame_eq and
  rel_alloc_independent_globals
synthesize_rules refines_in_out
add_synthesize_pattern refines_in_out =
\<open>
  [(Binding.make ("concrete_function", \<^here>), fn ctxt => fn i => fn t => 
     (case t of
        @{term_pat "Trueprop (refines (L2_modify (\<lambda>s. ?glob_upd _ _)) _ _ _ _ )"} => glob_upd
      | @{term_pat "Trueprop (refines (L2_modify (?glob_upd _)) _ _ _ _ )"} => glob_upd
      | @{term_pat "Trueprop (refines ?f _ _ _ _ )"} => f
      | t => t))]
\<close>


lemma refines_yield_both[simp]: "refines (return a) (return b) s t R \<longleftrightarrow> R (Result a, s) (Result b, t)"
  by (auto simp add: refines_def_old)

lemma disjoint_union_distrib: "A \<inter> (B \<union> C) = {} \<longleftrightarrow> A \<inter> B = {} \<and> A \<inter> C = {}"
  by blast

lemma inter_commute: "A \<inter> B = B \<inter> A" by blast
lemma disjoint_symmetric: "A \<inter> B = {} \<Longrightarrow> B \<inter> A = {}"
  by auto
lemma disjoint_symmetric': "A \<inter> B \<equiv> {} \<Longrightarrow> B \<inter> A = {}"
  by auto

definition IOcorres:: " 
  ('s \<Rightarrow> bool) \<Rightarrow>
  ('s \<Rightarrow> ('e,'a) xval \<Rightarrow> 's \<Rightarrow> bool) \<Rightarrow>
  ('s \<Rightarrow> 't) \<Rightarrow>
  ('a \<Rightarrow> 's \<Rightarrow> 'b) \<Rightarrow> 
  ('e \<Rightarrow> 's \<Rightarrow> 'e1) \<Rightarrow> 
  ('e1, 'b, 't) exn_monad =>
  ('e, 'a, 's) exn_monad => bool" where
  "IOcorres P Q st rx ex f\<^sub>a f\<^sub>c \<equiv> corresXF_post st rx ex P Q f\<^sub>a f\<^sub>c"

lemma IOcorres_id: "IOcorres (\<lambda>_. True) (\<lambda> _ _ _. True) (\<lambda>s. s) (\<lambda>r _. r) (\<lambda>r _. r) f f"
  by (auto simp add: IOcorres_def corresXF_post_def split: xval_splits prod.splits)
lemmas IOcorres_skip = IOcorres_id

lemma IOcorres_trivial_from_local_var_extract:
  "L2corres st rx ex P A C \<Longrightarrow> IOcorres (\<lambda>_. True) (\<lambda> _ _ _. True) (\<lambda>s. s) (\<lambda>r _. r) (\<lambda>r _. r) A A"
  by (rule IOcorres_id)

lemma admissible_IOcorres [corres_admissible]: 
  "ccpo.admissible Inf (\<ge>)  (\<lambda>f\<^sub>a. IOcorres P Q st rx ex f\<^sub>a f\<^sub>c)"
  unfolding IOcorres_def
  by (rule admissible_nondet_ord_corresXF_post)

lemma IOcorres_top [corres_top]: "IOcorres P Q st rx ex \<top> f\<^sub>c" 
  unfolding IOcorres_def
  by (rule corresXF_post_top)

lemma distinct_addresses_ptr_val_lemma: 
  "n < addr_card \<Longrightarrow> ptr_val p + word_of_nat n \<notin> (\<lambda>x. ptr_val p + word_of_nat x) ` {0..<n}"
  by auto (metis addr_card_len_of_conv nless_le order_le_less_trans unat_of_nat_eq)

lemma distinct_addresses_ptr_lemma:
  assumes bound: "n \<le> addr_card"
  shows "distinct (map (\<lambda>i. ptr_val p + of_nat i) [0..<n])"
  using bound
proof (induct n arbitrary: p)
  case 0
  then show ?case by simp
next
  case (Suc n)
  from Suc have hyp: "distinct (map (\<lambda>i. ptr_val p + word_of_nat i) [0..<n])" by auto
  show ?case 
    apply (subst upt_Suc_snoc)
    apply (subst map_append) 
    apply (subst distinct_append)
    apply (simp add: hyp)
    using Suc.prems
    apply (simp add: distinct_addresses_ptr_val_lemma)
    done
qed


lemma array_intvl_Suc_split:"{a..+Suc n * m} = {a..+n * m} \<union> {a + (word_of_nat (n*m))..+m}"
  by (metis add_diff_cancel_right' intvl_split le_add2 mult_Suc)


definition "rel_singleton_stack" :: "'a::c_type ptr \<Rightarrow> heap_mem \<Rightarrow> unit \<Rightarrow> 'a \<Rightarrow> bool" 
where
 "rel_singleton_stack p h = (\<lambda>(_::unit) v.
    v = h_val h p)"

lemma domain_rel_singleton_stack:
  "equal_on (ptr_span p) h h' \<Longrightarrow> rel_singleton_stack p h = rel_singleton_stack p h'"
  apply (clarsimp simp add: fun_eq_iff rel_singleton_stack_def)
  apply (metis (mono_tags, lifting) equal_on_def h_val_def heap_list_h_eq2)+
  done



named_theorems rel_stack_intros and rel_stack_simps



lemma rel_singleton_stack_simp [rel_stack_simps]:
  "rel_singleton_stack p h x v \<longleftrightarrow> v = h_val h p"
  by (auto simp add: rel_singleton_stack_def)

lemma rel_stack_refl [rel_stack_intros]: "(\<lambda>_. (=)) h x x"
  by auto

lemma rel_singleton_stackI [rel_stack_intros]: "rel_singleton_stack p h x (h_val h p)"
  by (auto simp add: rel_singleton_stack_def)

lemma rel_singleton_stack_condI [rel_stack_intros]: "h_val h p = y \<Longrightarrow> rel_singleton_stack p h x y"
  by (auto simp add: rel_singleton_stack_def)

lemma fun_of_rel_singleton_stack[fun_of_rel_intros]: "fun_of_rel (rel_singleton_stack p h) (\<lambda>_. (h_val h p))"
  by (auto simp add: fun_of_rel_def rel_singleton_stack_def)

lemma funp_rel_singleton_stack[funp_intros, corres_admissible]: "funp (rel_singleton_stack p h)"
 by (auto simp add: rel_singleton_stack_def funp_def fun_of_rel_def)




definition "rel_push" :: 
  "'a::c_type ptr \<Rightarrow> (heap_mem \<Rightarrow> 'b \<Rightarrow> 'c \<Rightarrow> bool) \<Rightarrow> heap_mem \<Rightarrow>  
  'b \<Rightarrow> 'a \<times> 'c \<Rightarrow> bool" 
where
 "rel_push p R h = (\<lambda>r (v, x).
    R h r x \<and> 
    v = h_val h p)"

lemma rel_singleton_stack_rel_push_conv: "rel_singleton_stack p = (\<lambda>h x y. rel_push p (\<lambda>_ _ _. True) h x (y, ()))"
  by (auto simp add: rel_singleton_stack_def rel_push_def)

lemma rel_push_simp[rel_stack_simps]: "rel_push p R h r (v, x) \<longleftrightarrow> 
   R h r x \<and> v = h_val h p"
  by (auto simp add: rel_push_def)

lemma fun_of_rel_puhsh [fun_of_rel_intros]:
  "fun_of_rel (R h) f \<Longrightarrow> fun_of_rel (rel_push p R h) (\<lambda>x. (h_val h p, f x))"
  by (auto simp add: fun_of_rel_def rel_push_def)

lemma funp_rel_push[funp_intros, corres_admissible]: "funp (R h) \<Longrightarrow> funp (rel_push p R h)"
  by (force simp add: funp_def rel_push_def fun_of_rel_def)

lemma rel_push_stackI [rel_stack_intros]: "Q h x y \<Longrightarrow> rel_push p Q h x ((h_val h p), y)"
  by (auto simp add: rel_push_def)

lemma rel_push_stack_condI [rel_stack_intros]: "h_val h p = v \<Longrightarrow> Q h x y \<Longrightarrow> rel_push p Q h x (v, y)"
  by (auto simp add: rel_push_def)

definition "rel_sum_stack L R h = rel_sum (L h) (R h)"
definition "rel_xval_stack L R h = rel_xval (L h) (R h)"

lemma rel_sum_stack_expand_sum_eq:
  "(rel_sum_stack (\<lambda>_. (=)) R) = (rel_sum_stack (rel_sum_stack (\<lambda>_. (=)) (\<lambda>_. (=))) R)"
  by (auto simp add: rel_sum_stack_def fun_eq_iff rel_sum.simps split: sum.splits )

lemma rel_xval_stack_expand_sum_eq:
  "(rel_xval_stack (\<lambda>_. (=)) R) = (rel_xval_stack (rel_sum_stack (\<lambda>_. (=)) (\<lambda>_. (=))) R)"
  by (auto simp add: rel_sum_stack_def rel_xval_stack_def fun_eq_iff rel_sum.simps sum.rel_eq 
      split: xval_splits sum.splits )

lemma rel_sum_stack_expand_sum_bot:
  "(\<lambda>_ _ _. False) = (rel_sum_stack (\<lambda>_ _ _. False) (\<lambda>_ _ _ . False))"
  by (auto simp add: rel_sum_stack_def fun_eq_iff rel_sum.simps split: sum.splits )

lemma rel_xval_stack_expand_xval_bot:
  "(\<lambda>_ _ _. False) = (rel_xval_stack (\<lambda>_ _ _. False) (\<lambda>_ _ _ . False))"
  by (auto simp add: rel_xval_stack_def fun_eq_iff rel_xval.simps split: xval_splits )


lemma rel_sum_stack_entail:
  assumes L: "\<And>v v'. L' h v v' \<Longrightarrow> L h v v'" 
  assumes R: "\<And>v v'. R' h v v' \<Longrightarrow> R h v v'" 
  assumes "rel_sum_stack L' R' h x y" 
  shows  "rel_sum_stack L R h x y"
  using assms
  by (auto simp add: rel_sum_stack_def rel_sum.simps split: sum.splits)

lemma rel_xval_stack_entail:
  assumes L: "\<And>v v'. L' h v v' \<Longrightarrow> L h v v'" 
  assumes R: "\<And>v v'. R' h v v' \<Longrightarrow> R h v v'" 
  assumes "rel_xval_stack L' R' h x y" 
  shows  "rel_xval_stack L R h x y"
  using assms
  by (auto simp add: rel_xval_stack_def rel_xval.simps)

lemma rel_sum_stack_intros:
  "L h l1 l2 \<Longrightarrow> rel_sum_stack L R h (Inl l1) (Inl l2)"
  "R h r1 r2 \<Longrightarrow> rel_sum_stack L R h (Inr r1) (Inr r2)"
  by (auto simp add: rel_sum_stack_def)

lemma rel_xval_stack_intros:
  "L h l1 l2 \<Longrightarrow> rel_xval_stack L R h (Exn l1) (Exn l2)"
  "R h r1 r2 \<Longrightarrow> rel_xval_stack L R h (Result r1) (Result r2)"
  by (auto simp add: rel_xval_stack_def)

lemma fun_of_rel_sum_stack[fun_of_rel_intros]:
  "fun_of_rel (L h) f_l \<Longrightarrow> fun_of_rel (R h) f_r \<Longrightarrow> fun_of_rel (rel_sum_stack L R h) (sum_map f_l f_r)"
  unfolding rel_sum_stack_def
  by (auto intro: fun_of_rel_intros)



lemma fun_of_rel_xval_stack[fun_of_rel_intros]:
  "fun_of_rel (L h) f_l \<Longrightarrow> fun_of_rel (R h) f_r \<Longrightarrow> fun_of_rel (rel_xval_stack L R h) (map_xval f_l f_r)"
  unfolding rel_xval_stack_def
  by (auto intro: fun_of_rel_intros)

lemma funp_rel_sum_stack[funp_intros, corres_admissible]: "funp (L h) \<Longrightarrow> funp (R h) \<Longrightarrow> funp (rel_sum_stack L R h)"
  unfolding rel_sum_stack_def by (auto intro: funp_intros)


lemma funp_rel_xval_stack[funp_intros, corres_admissible]: "funp (L h) \<Longrightarrow> funp (R h) \<Longrightarrow> funp (rel_xval_stack L R h)"
  unfolding rel_xval_stack_def by (auto intro: funp_intros)


lemma rel_sum_stack_cases:
"rel_sum_stack L R h x y = 
 ((\<exists>v w. x = Inl v \<and> y = Inl w \<and> L h v w) \<or>
 (\<exists>v w. x = Inr v \<and> y = Inr w \<and> R h v w))"
  by (auto simp add: rel_sum_stack_def rel_sum.simps)

lemma rel_xval_stack_cases:
"rel_xval_stack L R h x y = 
 ((\<exists>v w. x = Exn v \<and> y = Exn w \<and> L h v w) \<or>
 (\<exists>v w. x = Result v \<and> y = Result w \<and> R h v w))"
  by (auto simp add: rel_xval_stack_def rel_xval.simps)

lemma rel_sum_stack_simps [simp]:
  "rel_sum_stack L R h (Inl l\<^sub>1) (Inl l\<^sub>2) = L h l\<^sub>1 l\<^sub>2"
  "rel_sum_stack L R h (Inr r\<^sub>1) (Inr r\<^sub>2) = R h r\<^sub>1 r\<^sub>2"
  "rel_sum_stack L R h (Inl l\<^sub>1) (Inr r\<^sub>2) = False"
  "rel_sum_stack L R h (Inr r\<^sub>1) (Inl l\<^sub>2) = False"
  "rel_sum_stack L R h (Inl l\<^sub>1) y = (\<exists>w. y = Inl w \<and> L h l\<^sub>1 w)"
  "rel_sum_stack L R h (Inr r\<^sub>1) y = (\<exists>w. y = Inr w \<and> R h r\<^sub>1 w)"
  "rel_sum_stack L R h x (Inl l\<^sub>2) = (\<exists>v. x = Inl v \<and> L h v l\<^sub>2)"
  "rel_sum_stack L R h x (Inr r\<^sub>2) = (\<exists>v. x = Inr v \<and> R h v r\<^sub>2)"
  by (auto simp add: rel_sum_stack_def rel_sum.simps)

lemma rel_xval_stack_simps [simp]:
  "rel_xval_stack L R h (Exn l\<^sub>1) (Exn l\<^sub>2) = L h l\<^sub>1 l\<^sub>2"
  "rel_xval_stack L R h (Result r\<^sub>1) (Result r\<^sub>2) = R h r\<^sub>1 r\<^sub>2"
  "rel_xval_stack L R h (Exn l\<^sub>1) (Result r\<^sub>2) = False"
  "rel_xval_stack L R h (Result r\<^sub>1) (Exn l\<^sub>2) = False"
  "rel_xval_stack L R h (Exn l\<^sub>1) y = (\<exists>w. y = Exn w \<and> L h l\<^sub>1 w)"
  "rel_xval_stack L R h (Result r\<^sub>1) y = (\<exists>w. y = Result w \<and> R h r\<^sub>1 w)"
  "rel_xval_stack L R h x (Exn l\<^sub>2) = (\<exists>v. x = Exn v \<and> L h v l\<^sub>2)"
  "rel_xval_stack L R h x (Result r\<^sub>2) = (\<exists>v. x = Result v \<and> R h v r\<^sub>2)"
  by (auto simp add: rel_xval_stack_def rel_xval.simps)

lemma rel_sum_stack_eq_collapse: "(rel_sum_stack (\<lambda>_. (=)) (\<lambda>_. (=))) = ((\<lambda>_. (=))) "
  by (auto simp add: rel_sum_stack_cases fun_eq_iff)

lemma rel_xval_stack_eq_collapse: "(rel_xval_stack (\<lambda>_. (=)) (\<lambda>_. (=))) = ((\<lambda>_. (=))) "
  apply (clarsimp simp add: rel_xval_stack_cases fun_eq_iff) 
  by (metis Exn_def default_option_def exception_or_result_cases not_Some_eq)

lemma rel_sum_stack_InlI: "L h l1 l2 \<Longrightarrow> rel_sum_stack L R h (Inl l1) (Inl l2)"
  by (simp)


lemma rel_xval_stack_ExnI: "L h l1 l2 \<Longrightarrow> rel_xval_stack L R h (Exn l1) (Exn l2)"
  by (simp)

lemma rel_sum_stack_InrI: "R h r1 r2 \<Longrightarrow> rel_sum_stack L R h (Inr r1) (Inr r2)"
  by (simp)

lemma rel_xval_stack_ResultI: "R h r1 r2 \<Longrightarrow> rel_xval_stack L R h (Result r1) (Result r2)"
  by (simp)

definition "rel_exit Q h = (\<lambda>v w. \<exists>x. v = Nonlocal x \<and> Q h x w)"

lemma rel_exit_simps[simp]: 
  "rel_exit Q h (Nonlocal x) y = Q h x y"
  "rel_exit Q h Break        y = False"
  "rel_exit Q h Continue     y = False"
  "rel_exit Q h Return       y = False"
  "rel_exit Q h (Goto l)     y = False"
  by (auto simp add: rel_exit_def)

lemma rel_exit_intro: "Q h x y \<Longrightarrow> rel_exit Q h (Nonlocal x) y"
  by (auto simp add: rel_exit_def)

lemma rel_xval_stack_rel_exit_intro:
  assumes "\<And>x. rel_xval_stack (rel_exit Q) R h (Exn (Nonlocal (the_Nonlocal x))) (Exn x)" 
  assumes "rel_exit Q h e e'" 
  shows "rel_xval_stack (rel_exit Q) R h (Exn (Nonlocal (the_Nonlocal e))) (Exn e')"
  using assms
  by (auto simp add: rel_exit_def)


lemma rel_xval_stack_rel_exit_intro':
  assumes "\<And>x. rel_xval_stack (rel_exit Q) R h (Exn (Nonlocal x)) (Exn x)" 
  assumes "Q h e e'" 
  shows "rel_xval_stack (rel_exit Q) R h (Exn (Nonlocal e)) (Exn e')"
  using assms
  by (auto simp add: rel_exit_def)


lemma rel_exit_False_conv [simp]: "rel_exit (\<lambda>_ _ _. False) h e e' \<longleftrightarrow> False"
  by (auto simp add: rel_exit_def)

lemma rel_exit_FalseE: "rel_exit (\<lambda>_ _ _. False) h e e' \<Longrightarrow> L"
  by simp

lemma rel_sum_stack_generalise_left: 
  "rel_sum_stack L R h v w \<Longrightarrow> (\<And>v w. L h v w \<Longrightarrow> L' h v w) \<Longrightarrow> rel_sum_stack L' R h v w"
  by (auto simp add: rel_sum_stack_def rel_sum.simps)

lemma rel_xval_stack_generalise_left: 
  "rel_xval_stack L R h v w \<Longrightarrow> (\<And>v w. L h v w \<Longrightarrow> L' h v w) \<Longrightarrow> rel_xval_stack L' R h v w"
  by (auto simp add: rel_xval_stack_def rel_xval.simps)

lemmas generalise_unreachable_exitE = 
  rel_exit_FalseE
  rel_sum_stack_generalise_left
  rel_xval_stack_generalise_left

lemma fun_of_rel_rel_exit: "fun_of_rel (L h) f_l \<Longrightarrow> fun_of_rel (rel_exit L h) (\<lambda>v. case v of Nonlocal x \<Rightarrow> f_l x | _ \<Rightarrow> undefined)"
  by (auto simp add: fun_of_rel_def split: c_exntype.splits)

lemma funp_rel_exit [funp_intros, corres_admissible]: "funp (L h) \<Longrightarrow> funp (rel_exit L h)"
  using fun_of_rel_rel_exit
  by (metis funp_def)


named_theorems equal_upto_simps
named_theorems refines_stack_intros

lemma equal_uptoI: 
  assumes eq: "\<And>x. x \<notin> A \<Longrightarrow> f x = g x"
  shows "equal_upto A f g"
  using eq
  by (auto simp add: equal_upto_def)

lemma equal_upto_heap_update[equal_upto_simps]:
  fixes p:: "'a::mem_type ptr"
  assumes "(ptr_span p) \<subseteq> A" 
  shows "equal_upto A (heap_update p v h1) h2 = equal_upto A h1 h2"
  using assms 
  by (smt (verit, best) CTypes.mem_type_simps(2) equal_upto_def heap_list_length heap_update_def heap_update_nmem_same subset_iff)

lemma equal_upto_complement: "equal_upto B f g = equal_on (- B) f g"
  by (simp add: equal_on_def equal_upto_def)

lemma equal_upto_update_left_equalize:
  "equal_on (- F) (f s) s \<Longrightarrow> equal_on F (f s) t \<Longrightarrow> equal_upto (F \<union> A) s t = equal_upto A (f s) t" 
  by (smt (verit) Compl_iff Un_iff equal_on_def equal_upto_def)

lemma admissible_const_snd: 
  assumes admissible_fst: "ccpo.admissible \<Inter> (\<lambda>x y. y \<subseteq> x) (\<lambda>X. \<exists>w \<in> X. Q w)"
  shows "ccpo.admissible \<Inter> (\<lambda>x y. y \<subseteq> x) (\<lambda>X. \<exists>w. (w, v) \<in> X \<and> Q w)"
proof (rule ccpo.admissibleI[rule_format])
  fix C::"('a \<times>'b) set set" 
  assume chain: "Complete_Partial_Order.chain (\<lambda>x y. y \<subseteq> x) C" 
  assume nonempty: "C \<noteq> {}" 
  assume chain_prop: "\<And>X. X \<in> C \<Longrightarrow> \<exists>w. (w, v) \<in> X \<and> Q w" 
  show "\<exists>w. (w, v) \<in> \<Inter> C \<and> Q w"
  proof -
    define C' where "C' = Set.filter (\<lambda>(r, t). t =  v) ` C"
    have subset: "\<Inter> C' \<subseteq> \<Inter> C"
      using C'_def by fastforce
    moreover
    have snd_C': "\<And>X t. X \<in> C' \<Longrightarrow>  t \<in> snd ` X \<Longrightarrow> t = v"
      using C'_def
      by auto
    moreover
    from chain have chain_C': "Complete_Partial_Order.chain (\<lambda>x y. y \<subseteq> x) C'"
      using chain_prop C'_def
      by (simp add: chain_imageI subset_iff)
    from nonempty chain_prop have nonempty_C': "C' \<noteq> {}"
      using C'_def
      by blast

    from chain_C' have result_chain: "Complete_Partial_Order.chain (\<lambda>x y. y \<subseteq> x) ((\<lambda>X. fst ` X) ` C')"
      by (simp add: chain_imageI image_mono)
    from nonempty_C' have nonempty_result_chain: "((\<lambda>X. fst ` X) ` C') \<noteq> {}" by auto
    {
      fix X::"'a set"
      assume "X \<in> (`) fst ` C'"
      then obtain X0 where X: "X = fst ` Set.filter (\<lambda>(r, t). t =  v) X0" and X0: "X0 \<in> C"
        by (auto simp add: C'_def)
      from chain_prop [OF X0] obtain w where w: "(w, v) \<in> X0" and Q: "Q w" by blast
      from w X have "w \<in> X"
        apply clarsimp
        by (metis (mono_tags, lifting) case_prodI fst_conv image_iff member_filter)
      with Q 
      have "\<exists>w\<in>X. Q w" ..
    } note result_chain_prop = this
    from ccpo.admissibleD [OF admissible_fst  result_chain nonempty_result_chain result_chain_prop]
    obtain r' where
      r': "r' \<in>  \<Inter> ((\<lambda>X. fst ` X) ` C')" and Q: "Q r'"
      by auto
    from r' snd_C' have "(r', v) \<in> \<Inter> C'"
      by fastforce
    with Q subset show ?thesis by blast
  qed
qed

lemma admissible_funp: "funp Q \<Longrightarrow> ccpo.admissible \<Inter> (\<lambda>x y. y \<subseteq> x) (\<lambda>X. \<exists>w \<in> X. Q v w)"
  apply (clarsimp simp add: funp_def fun_of_rel_def)
  by (smt (verit, del_insts) InterI admissible_const ccpo.admissible_def)

lemma admissible_funp_conj: "funp Q \<Longrightarrow> ccpo.admissible \<Inter> (\<lambda>x y. y \<subseteq> x) (\<lambda>X. \<exists>w \<in> X. Q v w \<and> P w)"
  apply (clarsimp simp add: funp_def fun_of_rel_def)
  by (smt (verit, del_insts) InterI admissible_const ccpo.admissible_def)

lemma override_on_frame_raw_frame_lemma1:  
  assumes disj_A_B: "A \<inter> B = {}"
  assumes sf: "stack_free d \<inter> B = {}"
  shows
    "override_on d (override_on d' d B) (A \<union> B - stack_free d)  = 
     override_on d d' (A - stack_free d)"
  using disj_A_B sf
  by (auto simp add: override_on_def fun_eq_iff)

lemma override_on_frame_raw_frame_lemma2:  
  assumes disj_A_B: "A \<inter> B = {}"
  assumes sf: "stack_free d \<inter> B = {}"
  shows 
    "override_on h' (override_on h h' B) (A \<union> B \<union> stack_free d) =
     override_on h' h (A \<union> stack_free d)"
  using disj_A_B sf
  by (auto simp add: override_on_def fun_eq_iff)


lemma disjoint_stack_free_equal_upto_trans: 
  "equal_upto A d' d \<Longrightarrow>
   P \<inter> A = {} \<Longrightarrow> stack_free d \<inter> P = {} \<Longrightarrow>
   stack_free d' \<inter> P = {}"
  apply (clarsimp simp add: equal_upto_def)
  using root_ptr_valid_def stack_free_def valid_root_footprint_def by fastforce

lemma disjoint_stack_free_equal_on_trans: 
  "equal_on S d' d \<Longrightarrow>
   P \<subseteq> S \<Longrightarrow> stack_free d \<inter> P = {} \<Longrightarrow>
   stack_free d' \<inter> P = {}"
  apply (clarsimp simp add: equal_on_def)
  using root_ptr_valid_def stack_free_def valid_root_footprint_def by fastforce

lemma refines_L2_guard_right': 
  assumes "P t \<Longrightarrow> refines f g s t Q"
  shows "refines f (L2_seq (L2_guard P) (\<lambda>_. g)) s t Q"
  using assms unfolding L2_defs
  by (auto simp add: refines_def_old reaches_bind succeeds_bind)

lemma refines_L2_guard_right'': 
  assumes "P t \<Longrightarrow> refines f (L2_seq (L2_guard P) (\<lambda>_. g)) s t Q"
  shows "refines f (L2_seq (L2_guard P) (\<lambda>_. g)) s t Q"
  using assms unfolding L2_defs
  by (auto simp add: refines_def_old reaches_bind succeeds_bind)

lemma refines_L2_guard_right''': 
  assumes "P t \<Longrightarrow> refines f (L2_seq (L2_seq (L2_guard P) (\<lambda>_. g)) X) s t Q"
  shows "refines f (L2_seq (L2_seq (L2_guard P) (\<lambda>_. g)) X) s t Q"
  using assms unfolding L2_defs
  by (auto simp add: refines_def_old reaches_bind succeeds_bind)

lemma refines_L2_guard_right'''':
  assumes "P t \<Longrightarrow> 
    refines f
      (L2_seq 
        (L2_catch (L2_seq (L2_guard P) (\<lambda>_. g)) X)
        Y) s t Q "
  shows "refines f 
    (L2_seq 
      (L2_catch (L2_seq (L2_guard P) (\<lambda>_. g)) X)
      Y) s t Q "
  using assms unfolding L2_defs
  by (auto simp add: refines_def_old reaches_bind succeeds_bind reaches_catch succeeds_catch)


lemma refines_L2_guard_rightE: 
  assumes "P t" 
  assumes "refines f (L2_seq (L2_guard P) (\<lambda>_. g)) s t Q"
  shows "refines f g s t Q"
  using assms unfolding L2_defs
  by (auto simp add: refines_def_old reaches_bind succeeds_bind)

lemma refines_L2_guard_rightE': 
  assumes "P t" 
  assumes "refines f (L2_seq (L2_guard P) (\<lambda>_. g)) s t Q"
  shows "refines f (L2_seq (L2_guard P) (\<lambda>_. g)) s t Q"
  using assms unfolding L2_defs
  by (auto simp add: refines_def_old reaches_bind succeeds_bind)

lemma refines_L2_guard_right: 
  "(P \<Longrightarrow> refines f g s t Q) \<Longrightarrow> refines f (L2_seq (L2_guard (\<lambda>_. P)) (\<lambda>_. g)) s t Q"
  unfolding L2_defs
  by (auto simp add: refines_def_old reaches_bind succeeds_bind)

context heap_state
begin

lemma equal_upto_heap_on_heap_update[equal_upto_simps]:
  fixes p:: "'a::mem_type ptr"
  assumes "ptr_span p \<subseteq> A" 
  shows "equal_upto_heap_on A (hmem_upd (heap_update p v) s) t = equal_upto_heap_on A s t"
  using assms equal_upto_heap_update
  by (smt (verit, ccfv_threshold) equal_upto_heap_on_def equal_upto_heap_on_refl 
      equal_upto_heap_on_trans heap.get_upd heap.upd_cong heap.upd_same hmem_htd_upd sympD 
      symp_equal_upto_heap_on)

lemma equal_upto_heap_stack_release':
  fixes p:: "'a::mem_type ptr"
  assumes "ptr_span p \<subseteq> A" 
  shows "equal_upto_heap_on A (htd_upd (stack_releases (Suc 0) p) s) s"
  by (metis (no_types, lifting) One_nat_def add_mult_distrib add_right_cancel assms 
      equal_upto_heap_on_zero_heap_on heap_state.equal_upto_heap_on_trans heap_state_axioms 
      plus_1_eq_Suc sympD symp_equal_upto_heap_on times_nat.simps(2) zero_heap_on_stack_releases)


lemma equal_upto_heap_stack_release[equal_upto_simps]:
  fixes p:: "'a::mem_type ptr"
  assumes "ptr_span p \<subseteq> A" 
  shows "equal_upto_heap_on A (htd_upd (stack_releases (Suc 0) p) s) t = equal_upto_heap_on A s t"
  using equal_upto_heap_stack_release'
  by (metis assms equal_upto_heap_on_trans sympD symp_equal_upto_heap_on)

lemma equal_upto_heap_on_htd_upd: 
  "equal_upto_heap_on A s t \<Longrightarrow> 
   equal_upto A (f (htd s)) (htd t) \<Longrightarrow>
   equal_upto_heap_on A (htd_upd f s) t"
  by (smt (verit, best) equal_upto_heap_on_def hmem_htd_upd htd_hmem_upd 
      lense.upd_compose typing.get_upd typing.lense_axioms typing.upd_cong)

lemma equal_upto_heap_on_hmem: "equal_upto_heap_on A s t \<Longrightarrow> equal_upto A (hmem s) (hmem t)"
  by (auto simp add: equal_upto_heap_on_def)

lemma equal_upto_heap_on_sym: "equal_upto_heap_on A s t = equal_upto_heap_on A t s"
  by (metis   heap_state.symp_equal_upto_heap_on heap_state_axioms sympD )

lemma equal_upto_heap_stack_alloc':
  fixes p:: "'a::mem_type ptr"
  shows "equal_upto_heap_on (ptr_span p) 
     (hmem_upd (heap_update p v) (htd_upd (\<lambda>_. ptr_force_type p (htd s)) s)) 
      s"
  by (simp add: equal_upto_def equal_upto_heap_on_heap_update 
      equal_upto_heap_on_htd_upd ptr_force_type_d sympD symp_equal_upto_heap_on)

lemma equal_upto_heap_stack_alloc:
  fixes p:: "'a::mem_type ptr"
  assumes "length bs = size_of TYPE('a)"
  shows "equal_upto_heap_on (ptr_span p) 
     (hmem_upd (heap_update_padding p v bs) (htd_upd (\<lambda>_. ptr_force_type p (htd s)) s))
     s"
  apply (subst equal_upto_heap_on_sym)
  using assms
  apply (clarsimp simp add: equal_upto_def equal_upto_heap_on_def)
  by (smt (verit, del_insts) CTypes.mem_type_simps(2) heap.lense_axioms heap_update_nmem_same 
      heap_update_padding_def hmem_htd_upd lense.upd_cong ptr_force_type_d typing.lense_axioms)

definition 
  "rel_alloc":: "addr set \<Rightarrow> addr set \<Rightarrow> addr set \<Rightarrow> 's \<Rightarrow> 's \<Rightarrow> 's \<Rightarrow> bool" 
  where
  "rel_alloc S M A t\<^sub>0 \<equiv> \<lambda>s t.
     stack_free (htd s) \<subseteq> S \<and> 
     stack_free (htd s) \<inter> A = {} \<and> 
     stack_free (htd s) \<inter> M = {} \<and> 
     t = frame A t\<^sub>0 s"

lemma rel_alloc_fold_frame: "rel_alloc \<S> M A t\<^sub>0 s t \<Longrightarrow> frame A t\<^sub>0 s = t"
  by (auto simp add: rel_alloc_def)

lemma rel_alloc_modifies_antimono: "rel_alloc S M2 A t\<^sub>0 s t \<Longrightarrow> M1 \<subseteq> M2 \<Longrightarrow> rel_alloc S M1 A t\<^sub>0 s t"
  by (auto simp add: rel_alloc_def)

lemma rel_alloc_stack_free_disjoint:  
 "rel_alloc S M A t\<^sub>0 s t \<Longrightarrow> ptr_span p \<subseteq> A \<Longrightarrow> ptr_span p \<inter> stack_free (htd s) = {}"
  by (auto simp add: rel_alloc_def)

lemma rel_alloc_stack_free_disjoint_trans:  
 "rel_alloc S M A t\<^sub>0 s' t \<Longrightarrow> htd s' = htd s \<Longrightarrow> ptr_span p \<subseteq> A \<Longrightarrow> ptr_span p \<inter> stack_free (htd s) = {}"
  by (auto simp add: rel_alloc_def)

lemma rel_alloc_stack_free_disjoint':  
 "rel_alloc S M A t\<^sub>0 s t \<Longrightarrow> ptr_span p \<subseteq> A \<Longrightarrow> stack_free (htd s) \<inter> ptr_span p  = {}"
  by (auto simp add: rel_alloc_def)

lemma rel_alloc_stack_free_disjoint_trans':  
 "rel_alloc S M A t\<^sub>0 s' t \<Longrightarrow> htd s' = htd s \<Longrightarrow> ptr_span p \<subseteq> A \<Longrightarrow> stack_free (htd s) \<inter> ptr_span p  = {}"
  by (auto simp add: rel_alloc_def)

lemma rel_alloc_stack_free_disjoint_field_lvalue:
  fixes p:: "'a::mem_type ptr"
  assumes "rel_alloc S M A t\<^sub>0 s t" "ptr_span p \<subseteq> A" 
  assumes "field_lookup (typ_info_t TYPE('a)) f 0 = Some (T, n)" 
  assumes "export_uinfo T = typ_uinfo_t (TYPE('b))"
  shows "{&(p\<rightarrow>f)..+size_of TYPE('b::c_type)} \<inter> stack_free (htd s) = {}"
  using rel_alloc_stack_free_disjoint  field_tag_sub assms export_size_of
  by fastforce

lemma rel_alloc_stack_free_disjoint_field_lvalue_trans:
  fixes p:: "'a::mem_type ptr"
  assumes "rel_alloc S M A t\<^sub>0 s' t" "htd s' = htd s" "ptr_span p \<subseteq> A" 
  assumes "field_lookup (typ_info_t TYPE('a)) f 0 = Some (T, n)" 
  assumes "export_uinfo T = typ_uinfo_t (TYPE('b))"
  shows "{&(p\<rightarrow>f)..+size_of TYPE('b::c_type)} \<inter> stack_free (htd s) = {}"
  using rel_alloc_stack_free_disjoint  field_tag_sub assms export_size_of
  by fastforce

lemma rel_alloc_stack_free_disjoint_field_lvalue':
  fixes p:: "'a::mem_type ptr"
  assumes "rel_alloc S M A t\<^sub>0 s t" "ptr_span p \<subseteq> A" 
  assumes "field_lookup (typ_info_t TYPE('a)) f 0 = Some (T, n)" 
  assumes "export_uinfo T = typ_uinfo_t (TYPE('b))"
  shows "stack_free (htd s) \<inter> {&(p\<rightarrow>f)..+size_of TYPE('b::c_type)} = {}"
  using rel_alloc_stack_free_disjoint_field_lvalue [OF assms] by blast

lemma rel_alloc_stack_free_disjoint_field_lvalue_trans':
  fixes p:: "'a::mem_type ptr"
  assumes "rel_alloc S M A t\<^sub>0 s' t" "htd s' = htd s" "ptr_span p \<subseteq> A" 
  assumes "field_lookup (typ_info_t TYPE('a)) f 0 = Some (T, n)" 
  assumes "export_uinfo T = typ_uinfo_t (TYPE('b))"
  shows "stack_free (htd s) \<inter> {&(p\<rightarrow>f)..+size_of TYPE('b::c_type)} = {}"
  using rel_alloc_stack_free_disjoint_field_lvalue_trans [OF assms] by blast

lemma h_val_rel_alloc_disjoint:
  fixes p::"'a::mem_type ptr"
  shows "rel_alloc S M A t\<^sub>0 s t \<Longrightarrow> ptr_span p \<inter> A = {} \<Longrightarrow> ptr_span p \<inter> stack_free (htd s) = {} \<Longrightarrow> h_val (hmem t) p = h_val (hmem s) p"
  apply (simp add: rel_alloc_def h_val_frame_disjoint)
  done


definition rel_stack:: 
  "addr set \<Rightarrow> addr set \<Rightarrow> addr set \<Rightarrow> 's \<Rightarrow>  's \<Rightarrow> (heap_mem \<Rightarrow> 'b \<Rightarrow> 'c \<Rightarrow> bool) \<Rightarrow> 
    ('b \<times> 's) \<Rightarrow> ('c \<times> 's) \<Rightarrow> bool"
  where
  "rel_stack S M A s t\<^sub>0 R = (\<lambda>(v, s') (w, t').
     R (hmem s') v w \<and>
     rel_alloc S M A t\<^sub>0 s' t' \<and> 
     equal_upto (M \<union> stack_free (htd s')) (hmem s') (hmem s) \<and>
     htd s' = htd s)" 

lemma rel_stack_unchanged_typing: "rel_alloc S M' A t\<^sub>0 s t \<Longrightarrow> rel_stack S M A s t\<^sub>0 R (v, s') (w, t') \<Longrightarrow>
  equal_on S (htd t') (htd t)"
  by (auto simp add: rel_alloc_def rel_stack_def Diff_triv equal_on_def htd_frame inf_commute)

lemma rel_stack_unchanged_heap: "rel_alloc S M' A t\<^sub>0 s t \<Longrightarrow> rel_stack S M A s t\<^sub>0 R (v, s') (w, t') \<Longrightarrow>
  equal_upto (M \<union> stack_free (htd s')) (hmem t') (hmem t)"
  apply (clarsimp simp add: rel_alloc_def rel_stack_def Diff_triv equal_on_def htd_frame inf_commute)
  by (smt (verit, ccfv_threshold) equal_on_def equal_on_stack_free_preservation equal_upto_def hmem_frame)

lemma rel_stack_unchanged_stack_free: 
  "rel_alloc S M' A t\<^sub>0 s t \<Longrightarrow> rel_stack S M A s t\<^sub>0 R (v, s') (w, t') \<Longrightarrow>
  stack_free (htd s') = stack_free (htd s)"
  apply (auto simp add: rel_alloc_def rel_stack_def Diff_triv htd_frame inf_commute)
  done

lemma rel_stack_unchanged_stack_free': 
  assumes stack: "rel_alloc S M' A t\<^sub>0 s t" 
  assumes rel_stack: "rel_stack S M A s t\<^sub>0 R (v, s') (w, t')"
  shows "stack_free (htd t') = stack_free (htd t)"
  using stack rel_stack
  apply (clarsimp simp add: rel_alloc_def rel_stack_def Diff_triv htd_frame inf_commute)
  subgoal
    using rel_stack_unchanged_stack_free [OF stack rel_stack] equal_on_stack_free_preservation
    by (auto simp add: frame_def stack_free_def root_ptr_valid_def valid_root_footprint_def)
  done

lemma rel_stack_unchanged_heap': 
  assumes alloc: "rel_alloc S {} A t\<^sub>0 s t"
  assumes stack: "rel_stack S M A s t\<^sub>0 R (v, s') (w, t')" 
  shows "equal_upto (M \<union> stack_free (htd t')) (hmem t') (hmem t)"
  apply (rule equal_upto_mono [OF _ rel_stack_unchanged_heap [OF alloc stack]])
  using  stack_free_htd_frame stack
  apply (auto simp add: rel_stack_def rel_alloc_def subset_iff)
  done

lemma rel_stack_Exn[simp]: 
  "rel_stack S M A s t\<^sub>0 (rel_xval_stack L R) (Exn v, s') (Exn w, t') = rel_stack S M A s t\<^sub>0 L (v, s') (w, t')"
  by (simp add: rel_stack_def)
lemma rel_stack_Exn_Result[simp]: 
  "rel_stack S M A s t\<^sub>0  (rel_xval_stack L R) (Exn v, s') (Result w, t') = False"
  by (simp add: rel_stack_def)
lemma rel_stack_Result[simp]: 
  "rel_stack S M A s t\<^sub>0 (rel_xval_stack L R) (Result v, s') (Result w, t') = rel_stack S M A s t\<^sub>0 R (v, s') (w, t')"
  by (simp add: rel_stack_def)
lemma rel_zero_stack_Result_Exn[simp]: 
  "rel_stack S M A s t\<^sub>0 (rel_xval_stack L R) (Result v, s') (Exn w, t') = False"
  by (simp add: rel_stack_def)

lemma admissible_fail: " ccpo.admissible Inf (\<lambda>x y. y \<le> x) (\<lambda>A. \<not> succeeds A t)"
  apply (rule ccpo.admissibleI) 
  apply (clarsimp simp add: ccpo.admissible_def chain_def 
      succeeds_def reaches_def split: prod.splits xval_splits)
  apply transfer
  by (auto simp add: Inf_post_state_def top_post_state_def)


lemma fun_lub_lem: "(\<lambda>(A::('f \<Rightarrow> (('d, 'e) exception_or_result \<times> 'f) post_state) set) x::'f.
            \<Sqinter>f::'f \<Rightarrow> (('d, 'e) exception_or_result \<times> 'f) post_state\<in>A. f x) = fun_lub (Inf)"
  apply (clarsimp simp add: fun_lub_def [abs_def])
  by (simp add: image_def)

lemma fun_ord_lem:
   "(\<lambda>(a::'f \<Rightarrow> (('d, 'e) exception_or_result \<times> 'f) post_state)
            b::'f \<Rightarrow> (('d, 'e) exception_or_result \<times> 'f) post_state. \<forall>x::'f. b x \<le> a x) = fun_ord (\<ge>)"
  apply (simp add: fun_ord_def [abs_def])
  done


(* FIXME: move to spec monad or up *)
lemma admissible_refines_funp:
  assumes *: "funp R"
  shows "ccpo.admissible Inf (\<ge>) (\<lambda>A. refines C A s t R)"
    apply (rule ccpo.admissibleI) 
 
  apply (clarsimp simp add: ccpo.admissible_def chain_def 
        refines_def_old reaches_def succeeds_def)
  apply (intro allI impI conjI)
  subgoal
    apply transfer
    by (auto simp add: Inf_post_state_def top_post_state_def split: if_split_asm)
  subgoal
    using *
    apply transfer
    apply (clarsimp simp add: funp_def fun_of_rel_def Inf_post_state_def top_post_state_def image_def vimage_def 
        split: if_split_asm)
    by (metis post_state.distinct(1) outcomes.simps(2))
  done

lemma fun_of_rel_stack: 
  assumes f: "\<And>h. fun_of_rel (Q h) (f h)" 
  shows "fun_of_rel (rel_stack S M A s t\<^sub>0 Q) (\<lambda>(r, s). (f (hmem s) r, frame A t\<^sub>0 s))"
  using f
  by (auto simp add: fun_of_rel_def rel_stack_def rel_alloc_def)

lemma funp_rel_stack: 
  assumes funp: "\<And>h. funp (Q h)"
  shows "funp (rel_stack S M A s t\<^sub>0 Q)"
proof -
  from funp obtain f where f: "\<And>h. fun_of_rel (Q h) (f h)" 
    apply (clarsimp simp add: funp_def ) 
    by metis
  from fun_of_rel_stack [OF f] 
  have "fun_of_rel (rel_stack S M A s t\<^sub>0 Q) (\<lambda>(r, s). (f (hmem s) r, frame A t\<^sub>0 s))".
  then show ?thesis
    unfolding funp_def
    by blast
qed

theorem admissible_refines_rel_stack[corres_admissible]: 
  assumes funp: "\<And>h. funp (Q h)"
  shows "ccpo.admissible Inf (\<ge>) (\<lambda>g. refines f g s' t' (rel_stack S M A s t\<^sub>0 Q))"
  apply (rule admissible_refines_funp)
  apply (rule funp_rel_stack)
  apply (rule funp)
  done

lemma admissible_rel_stack_eq: "ccpo.admissible \<Inter> (\<lambda>x y. y \<subseteq> x) (\<lambda>X. \<exists>w \<in> X. (\<lambda>_. (=)) h v w)"
  by (auto simp add: ccpo.admissible_def)

lemma admissible_rel_singleton_stack: 
  shows "ccpo.admissible \<Inter> (\<lambda>x y. y \<subseteq> x) (\<lambda>X. \<exists>w \<in> X. (rel_singleton_stack p) h v w)"
    by (auto simp add: ccpo.admissible_def rel_singleton_stack_def)

lemma admissible_rel_push: 
  assumes admiss: "\<And>h v. ccpo.admissible \<Inter> (\<lambda>x y. y \<subseteq> x) (\<lambda>X. \<exists>w \<in> X. Q h v w)"
  shows "ccpo.admissible \<Inter> (\<lambda>x y. y \<subseteq> x) (\<lambda>X. \<exists>w \<in> X. (rel_push p Q) h v w)"
proof -
  have "ccpo.admissible \<Inter> (\<lambda>x y. y \<subseteq> x) (\<lambda>X. \<exists>w. (h_val h p, w) \<in> X \<and> Q h v w)"
  proof (rule ccpo.admissibleI[rule_format])
    fix C::"('c \<times> 'b) set set"  
    assume chain: "Complete_Partial_Order.chain (\<lambda>x y. y \<subseteq> x) C"
    assume nonempty: "C \<noteq> {}"
    assume chain_prop: "(\<And>X. X \<in> C \<Longrightarrow> \<exists>w. (h_val h p, w) \<in> X \<and> Q h v w)"
    show "\<exists>w. (h_val h p, w) \<in> \<Inter> C \<and> Q h v w"
    proof -
      define C' where "C' = Set.filter (\<lambda>(v, w). v = h_val h p) ` C"
      have subset: "\<Inter> C' \<subseteq> \<Inter> C"
        using C'_def by fastforce
      from chain have chain_C': "Complete_Partial_Order.chain (\<lambda>x y. y \<subseteq> x) C'"
        using chain_prop C'_def
        by (simp add: chain_imageI subset_iff)
      have fst_C': "\<And>X t. X \<in> C' \<Longrightarrow>  t \<in> fst ` X \<Longrightarrow> t = h_val h p" 
        using C'_def
        by auto
      from nonempty chain_prop have nonempty_C': "C' \<noteq> {}"
        using C'_def
        by blast
      from chain_C' have result_chain: "Complete_Partial_Order.chain (\<lambda>x y. y \<subseteq> x) ((\<lambda>X. snd ` X) ` C')"
        by (simp add: chain_imageI image_mono)
      from nonempty_C' have nonempty_result_chain: "((\<lambda>X. snd ` X) ` C') \<noteq> {}" by auto
      from chain_prop have result_chain_prop: "(\<And>X. X \<in> (`) snd ` C' \<Longrightarrow> \<exists>w\<in>X. Q h v w) "
        using C'_def
        by auto (metis (mono_tags, lifting) case_prodI member_filter snd_conv)
      from ccpo.admissibleD [OF admiss [of "h" v] result_chain nonempty_result_chain result_chain_prop]
      obtain w where
        w: "w \<in>  \<Inter> ((\<lambda>X. snd ` X) ` C')" and Q: "Q h v w"
        by auto
      from w fst_C' have "(h_val h p, w) \<in> \<Inter> C'"
        by fastforce
      with Q subset show ?thesis by blast
    qed
  qed
  then show ?thesis
    by (clarsimp simp add: rel_push_def  split_paired_Bex)
qed

lemma admissible_rel_sum_stack: 
  assumes admiss_L: "\<And>h v. ccpo.admissible \<Inter> (\<lambda>x y. y \<subseteq> x) (\<lambda>X. \<exists>w \<in> X. L h v w)"
  assumes admiss_R: "\<And>h v. ccpo.admissible \<Inter> (\<lambda>x y. y \<subseteq> x) (\<lambda>X. \<exists>w \<in> X. R h v w)"
  shows "ccpo.admissible \<Inter> (\<lambda>x y. y \<subseteq> x) (\<lambda>X. \<exists>w \<in> X. (rel_sum_stack L R) h v w)"
proof -
  have "ccpo.admissible \<Inter> (\<lambda>x y. y \<subseteq> x) (\<lambda>X. \<exists>w\<in>X. rel_sum (L h) (R h) v w)"
  proof (rule ccpo.admissibleI[rule_format])
    fix C::"('c + 'e) set set" 
    assume chain: "Complete_Partial_Order.chain (\<lambda>x y. y \<subseteq> x) C"
    assume nonempty: "C \<noteq> {}"
    assume chain_prop: "\<And>X. X \<in> C \<Longrightarrow> \<exists>w\<in>X. rel_sum (L h) (R h) v w"
    show "\<exists>w\<in>\<Inter> C. rel_sum (L h) (R h) v w"
    proof (cases v)
      case (Inl l)
      define C' where "C' = Set.filter (Sum_Type.isl) ` C"
      have subset: "\<Inter> C' \<subseteq> \<Inter> C"
        using C'_def by fastforce
      from chain have chain_C': "Complete_Partial_Order.chain (\<lambda>x y. y \<subseteq> x) C'"
        using chain_prop C'_def
        by (simp add: chain_imageI subset_iff)
      from nonempty chain_prop have nonempty_C': "C' \<noteq> {}"
        using C'_def
        by blast
      have prop_C': "\<And>X t. X \<in> C' \<Longrightarrow>  t \<in> X \<Longrightarrow> Sum_Type.isl t" 
        using C'_def
        by auto
      from Inl chain_prop  have chain_prop': 
        "\<And>X. X \<in> C' \<Longrightarrow> \<exists>w\<in>X. \<exists>l'. w = Inl l' \<and> L h l l'"  
        by (fastforce simp add: rel_sum.simps C'_def)
      have "\<exists>w\<in>\<Inter> C. \<exists>l'. w = Inl l' \<and> L h l l'"
      proof - 
        from chain_C' have result_chain: "Complete_Partial_Order.chain (\<lambda>x y. y \<subseteq> x) ((\<lambda>X. Sum_Type.projl ` X) ` C')"
          by (simp add: chain_imageI image_mono)
        from nonempty_C' have nonempty_result_chain: "((\<lambda>X. Sum_Type.projl ` X) ` C') \<noteq> {}" by auto

        from chain_prop' have result_chain_prop: "\<And>X. X \<in>(\<lambda>X. Sum_Type.projl ` X) ` C' \<Longrightarrow> \<exists>w\<in>X. L h l w"
          using image_iff by fastforce
        from ccpo.admissibleD [OF admiss_L [of "h" l] result_chain nonempty_result_chain result_chain_prop]
        obtain w where
          w: "w\<in>\<Inter> ((`) projl ` C')" and L: "L h l w"
          by auto
        from w prop_C' have "Inl w \<in> \<Inter> C'" by fastforce
        with L subset show ?thesis by blast
      qed
      then show ?thesis by (simp add: Inl rel_sum.simps)
    next
      case (Inr r)
      define C' where "C' = Set.filter (Not o Sum_Type.isl) ` C"
      have subset: "\<Inter> C' \<subseteq> \<Inter> C"
        using C'_def by fastforce
      from chain have chain_C': "Complete_Partial_Order.chain (\<lambda>x y. y \<subseteq> x) C'"
        using chain_prop C'_def
        by (simp add: chain_imageI subset_iff)
      from nonempty chain_prop have nonempty_C': "C' \<noteq> {}"
        using C'_def
        by blast
      have prop_C': "\<And>X t. X \<in> C' \<Longrightarrow>  t \<in> X \<Longrightarrow> \<not> (Sum_Type.isl t)" 
        using C'_def
        by auto
      from Inr chain_prop  have chain_prop': 
        "\<And>X. X \<in> C' \<Longrightarrow> \<exists>w\<in>X. \<exists>r'. w = Inr r' \<and> R h r r'"  
        by (fastforce simp add: rel_sum.simps C'_def)
      have "\<exists>w\<in>\<Inter> C. \<exists>r'. w = Inr r' \<and> R h r r'"
      proof - 
        from chain_C' have result_chain: "Complete_Partial_Order.chain (\<lambda>x y. y \<subseteq> x) ((\<lambda>X. Sum_Type.projr ` X) ` C')"
          by (simp add: chain_imageI image_mono)
        from nonempty_C' have nonempty_result_chain: "((\<lambda>X. Sum_Type.projr ` X) ` C') \<noteq> {}" by auto

        from chain_prop' have result_chain_prop: "\<And>X. X \<in>(\<lambda>X. Sum_Type.projr ` X) ` C' \<Longrightarrow> \<exists>w\<in>X. R h r w"
          using image_iff by fastforce
        from ccpo.admissibleD [OF admiss_R [of "h" r] result_chain nonempty_result_chain result_chain_prop]
        obtain w where
          w: "w\<in>\<Inter> ((`) projr ` C')" and L: "R h r w"
          by auto
        from w prop_C' have "Inr w \<in> \<Inter> C'" by fastforce
        with L subset show ?thesis by blast
      qed
      then show ?thesis by (simp add: Inr rel_sum.simps)
    qed
  qed
  then show ?thesis by (simp add: rel_sum_stack_def)
qed

lemma IOcorres_refines_conv: 
  assumes rel_to_prj: "\<And>h. fun_of_rel (R h) (prj h)"
  assumes rel_to_prjE: "\<And>h. fun_of_rel (L h) (prjE h)"
  shows "IOcorres
           (\<lambda>s. rel_alloc \<S> M A t\<^sub>0 s (frame A t\<^sub>0 s) \<and> P s) 
           (\<lambda>s r s'. stack_free (htd s') \<subseteq> \<S> \<and> stack_free (htd s') \<inter> A = {} \<and> stack_free (htd s') \<inter> M1 = {} \<and> 
                    equal_upto (M1 \<union> stack_free (htd s')) (hmem s') (hmem s) \<and> 
                    htd s' = htd s \<and>
                    (case r of Exn l \<Rightarrow> \<exists>e. l = Nonlocal e \<and> L (hmem s') e (prjE (hmem s') e)| Result x \<Rightarrow> R (hmem s') x (prj (hmem s') x)))
           (frame A t\<^sub>0) 
           (\<lambda>r s. prj (hmem s) r) 
           (\<lambda>r s. prjE (hmem s) (the_Nonlocal r))
           g f
         \<longleftrightarrow> 
         (\<forall>s t. rel_alloc \<S> M A t\<^sub>0 s t \<longrightarrow> P s \<longrightarrow> refines f g s t (rel_stack \<S> M1 A s t\<^sub>0 (rel_xval_stack (rel_exit L) R)))"
  apply standard
  subgoal
    apply (clarsimp simp add: IOcorres_def corresXF_post_def)
    apply (rule refinesI)
    subgoal
      using rel_alloc_fold_frame by blast


    subgoal for s t v s'
      apply (erule_tac x=s in allE)
      apply (subst (asm) (1 2) rel_alloc_def)
      apply safe
      apply (clarsimp)
      apply (erule_tac x="v" in allE)
      apply (erule_tac x="s'" in allE)
      subgoal
        apply (clarsimp split: xval_splits)
        subgoal for x
          apply (rule exI[where x="Exn (prjE (hmem s') x)"])
          apply (rule exI[where x="frame A t\<^sub>0 s'"])
          apply (clarsimp simp add: rel_stack_def rel_alloc_def fun_of_rel_def)
          done
        subgoal for x
          apply (rule exI[where x="Result (prj (hmem s') x)"])
          apply (rule exI[where x="frame A t\<^sub>0 s'"])
          apply (clarsimp simp add: rel_stack_def rel_alloc_def fun_of_rel_def)
          done
        done
      done
    done
  subgoal
    apply (clarsimp simp add: IOcorres_def corresXF_post_def)
    subgoal for s
    apply (rule conjI)
    subgoal
      apply clarsimp
      subgoal for v s'
        apply (erule_tac x="s" in allE)
        apply (erule_tac x="(frame A t\<^sub>0 s)" in allE)
        apply (clarsimp simp add: rel_alloc_def refines_def_old)
        apply (erule_tac x="v" in allE)
        apply (erule_tac x="s'" in allE)
        subgoal 
          apply (cases v)
          subgoal  
            using rel_to_prjE  by (clarsimp simp add: rel_stack_def rel_alloc_def fun_of_rel_def rel_exit_def default_option_def 
                Exn_def [symmetric])
          subgoal  
            using rel_to_prj by (clarsimp simp add: rel_stack_def rel_alloc_def fun_of_rel_def default_option_def 
                Exn_def [symmetric]) 
          done
        done
      done
    subgoal 
      by (auto simp add: refines_def_old)
    done
  done
  done

lemmas IOcorres_to_refines = iffD1 [OF  IOcorres_refines_conv, rule_format]
lemmas refines_to_IOcorres = iffD2 [OF  IOcorres_refines_conv, rule_format]

lemma refines_rel_xval_stack_generalise_exit:
    "refines f g s t (rel_stack \<S> M A s t\<^sub>0 (rel_xval_stack L R)) \<Longrightarrow> (\<And>h v w. L h v w \<Longrightarrow> L' h v w) \<Longrightarrow> 
     refines f g s t (rel_stack \<S> M A s t\<^sub>0 (rel_xval_stack L' R))"
  by (erule refines_weaken) (auto simp add: rel_stack_def rel_xval_stack_def rel_xval.simps)

lemma L2_gets_rel_stack': 
  assumes "R (hmem s) (e s) (e' (frame A t\<^sub>0 s))"
  assumes "rel_alloc \<S> M A t\<^sub>0 s t"
  shows "refines (L2_gets e ns) (L2_gets e' ns) s t (rel_stack \<S> {} A s t\<^sub>0 (rel_xval_stack L R))" 
  using assms
  by (auto simp add: refines_def_old L2_defs rel_stack_def rel_alloc_def)


lemma L2_gets_rel_stack: 
  assumes "R (hmem s) (e s) (e' (frame A t\<^sub>0 s))"
  assumes "rel_alloc \<S> M A t\<^sub>0 s t"
  shows "refines (L2_gets e ns) (L2_gets e' ns') s t (rel_stack \<S> {} A s t\<^sub>0 (rel_xval_stack L R))" 
  using assms
  by (auto simp add: refines_def_old L2_defs rel_stack_def rel_alloc_def)

lemma L2_gets_rel_stack_guarded: 
  assumes "G \<Longrightarrow> R (hmem s) (e s) (e' (frame A t\<^sub>0 s))"
  assumes "rel_alloc \<S> M A t\<^sub>0 s t"
  shows "refines (L2_gets e ns) (L2_seq (L2_guard (\<lambda>_. G)) (\<lambda>_. (L2_gets e' ns'))) s t (rel_stack \<S> {} A s t\<^sub>0 (rel_xval_stack L R))" 
  using assms
  by (auto simp add: refines_def_old L2_defs rel_stack_def rel_alloc_def succeeds_bind reaches_bind)

lemma L2_gets_constant_trivial_rel_stack: 
  assumes "rel_alloc \<S> M A t\<^sub>0 s t"
  shows "refines (L2_gets (\<lambda>_. c) ns) (L2_gets (\<lambda>_. c) ns) s t (rel_stack \<S> {} A s t\<^sub>0 (rel_xval_stack L (\<lambda>_. (=))))" 
  using assms
  by (auto simp add: refines_def_old L2_defs rel_stack_def rel_alloc_def)

lemma L2_gets_constant_rel_stack: 
  assumes "R (hmem s) c c'"
  assumes "rel_alloc \<S> M A t\<^sub>0 s t"
  shows "refines (L2_gets (\<lambda>_. c) ns) (L2_gets (\<lambda>_. c') ns) s t (rel_stack \<S> {} A s t\<^sub>0 (rel_xval_stack L R))" 
  using assms
  by (auto simp add: refines_def_old L2_defs rel_stack_def rel_alloc_def)

lemma L2_throw_rel_stack: 
  assumes "L (hmem s) c c'"
  assumes "rel_alloc \<S> M A t\<^sub>0 s t"
  shows "refines (L2_throw c ns) (L2_throw c' ns') s t (rel_stack \<S> {} A s t\<^sub>0 (rel_xval_stack L R))" 
  using assms
  by (auto simp add: refines_def_old L2_defs rel_stack_def rel_alloc_def Exn_def [symmetric])

lemma L2_try_rel_stack: 
  assumes s_t: "rel_alloc \<S> M A t\<^sub>0 s t"
  assumes "refines f g s t (rel_stack \<S> M1 A s t\<^sub>0 (rel_xval_stack (rel_sum_stack L R) R))"
  shows "refines (L2_try f) (L2_try g) s t (rel_stack \<S> M1 A s t\<^sub>0 (rel_xval_stack L R))"
  using assms
  apply (clarsimp simp add: refines_def_old L2_defs rel_stack_def rel_alloc_def reaches_try)
  subgoal for s' r'
  apply (cases r')
     apply (clarsimp simp add: default_option_def Exn_def [symmetric])
    subgoal for y
      apply (cases y)
      subgoal by fastforce
      subgoal by fastforce
      done
    subgoal
      apply fastforce
      done
    done
  done

lemma L2_try_rel_stack_merge1: 
  assumes "\<And>h v v'. R' h v v' \<Longrightarrow>  R h v v'"
  assumes s_t: "rel_alloc \<S> M A t\<^sub>0 s t"
  assumes "refines f g s t (rel_stack \<S> M1 A s t\<^sub>0 (rel_xval_stack (rel_sum_stack L R') R))"
  shows "refines (L2_try f) (L2_try g) s t (rel_stack \<S> M1 A s t\<^sub>0 (rel_xval_stack L R))"
  using assms
  apply (clarsimp simp add: refines_def_old L2_defs rel_stack_def rel_alloc_def reaches_try)
  subgoal for s' r'
  apply (cases r')
     apply (clarsimp simp add: default_option_def Exn_def [symmetric])
    subgoal for y
      apply (cases y)
      subgoal by fastforce
      subgoal by fastforce
      done
    subgoal
      apply fastforce
      done
    done
  done

lemma L2_try_rel_stack_merge2: 
  assumes "\<And>h v v'. R' h v v' \<Longrightarrow> R h v v'"
  assumes s_t: "rel_alloc \<S> M A t\<^sub>0 s t"
  assumes "refines f g s t (rel_stack \<S> M1 A s t\<^sub>0 (rel_xval_stack (rel_sum_stack L R) R'))"
  shows "refines (L2_try f) (L2_try g) s t (rel_stack \<S> M1 A s t\<^sub>0 (rel_xval_stack L R))"
  using assms
  apply (clarsimp simp add: refines_def_old L2_defs rel_stack_def rel_alloc_def reaches_try)
  subgoal for s' r'
  apply (cases r')
     apply (clarsimp simp add: default_option_def Exn_def [symmetric])
    subgoal for y
      apply (cases y)
      subgoal by fastforce
      subgoal by fastforce
      done
    subgoal
      apply fastforce
      done
    done
  done

lemma L2_guard_rel_stack:
  assumes "e' (frame A t\<^sub>0 s) \<Longrightarrow> e s"
  assumes "rel_alloc \<S> M A t\<^sub>0 s t"
  shows "refines (L2_guard e) (L2_guard e') s t (rel_stack \<S> {} A s t\<^sub>0 (rel_xval_stack L (\<lambda>_. (=))))"
  using assms
  by (auto simp add: refines_def_old L2_defs rel_stack_def rel_alloc_def)

lemma L2_modify_heap_update_rel_stack':
  fixes p::"'a:: mem_type ptr"
  assumes "R (heap_update p v (hmem s)) () (e' (frame A t\<^sub>0 s))"
  assumes "ptr_span p \<subseteq> A"
  assumes "rel_alloc \<S> (ptr_span p) A t\<^sub>0 s t"
  shows "refines 
           (L2_modify (hmem_upd (heap_update p v))) 
           (L2_gets e' ns) 
           s t 
           (rel_stack \<S> (ptr_span p) A s t\<^sub>0 (rel_xval_stack L R))"
  using assms
  by (auto simp add: refines_def_old L2_defs rel_stack_def rel_alloc_def 
      frame_heap_update equal_upto_heap_update)

lemma L2_modify_heap_update_rel_stack:
  fixes p::"'a:: mem_type ptr"
  assumes "R (heap_update p (v s) (hmem s)) () (e' (frame A t\<^sub>0 s))"
  assumes "rel_alloc \<S> M A t\<^sub>0 s t"
  assumes "ptr_span p \<subseteq> A"
  assumes "ptr_span p \<subseteq> M"
  shows "refines 
           (L2_modify (\<lambda>s. hmem_upd (heap_update p (v s)) s)) 
           (L2_gets e' ns) 
           s t 
           (rel_stack \<S> (ptr_span p) A s t\<^sub>0 (rel_xval_stack L R))"
  using assms
  by (auto simp add: refines_def_old L2_defs rel_stack_def rel_alloc_def 
      frame_heap_update equal_upto_heap_update)


lemma L2_modify_keep_heap_update_rel_stack:
  fixes p::"'a:: mem_type ptr"
  assumes "v s = v' (frame A t\<^sub>0 s)" 
  assumes "rel_alloc \<S> M A t\<^sub>0 s t"
  assumes "ptr_span p \<inter> A = {}"
  assumes "ptr_span p \<inter> stack_free (htd s) = {}"
  assumes "ptr_span p \<subseteq> M"
  shows "refines 
           (L2_modify (\<lambda>s. hmem_upd (heap_update p (v s)) s)) 
           (L2_modify (\<lambda>s. hmem_upd (heap_update p (v' s)) s)) 
           s t 
           (rel_stack \<S> (ptr_span p) A s t\<^sub>0 (rel_xval_stack L (\<lambda>_. (=))))"
  using assms
  by (auto simp add: refines_def_old L2_defs rel_stack_def rel_alloc_def   
      frame_heap_update disjoint_subset2 equal_upto_heap_update 
      frame_heap_update_disjoint)

lemma L2_modify_keep_heap_update_rel_stack_guarded:
  fixes p::"'a:: mem_type ptr"
  assumes "G \<Longrightarrow> v s = v' (frame A t\<^sub>0 s)" 
  assumes "rel_alloc \<S> M A t\<^sub>0 s t"
  assumes "G \<Longrightarrow> ptr_span p \<inter> A = {}"
  assumes "G \<Longrightarrow> ptr_span p \<inter> stack_free (htd s) = {}"
  assumes "G \<Longrightarrow> ptr_span p \<subseteq> M"
  shows "refines 
           (L2_modify (\<lambda>s. hmem_upd (heap_update p (v s)) s)) 
           (L2_seq (L2_guard (\<lambda>_. G)) (\<lambda>_. (L2_modify (\<lambda>s. hmem_upd (heap_update p (v' s)) s)))) 
           s t 
           (rel_stack \<S> (ptr_span p) A s t\<^sub>0 (rel_xval_stack L (\<lambda>_. (=))))"
  apply (rule refines_L2_guard_right)
  apply (rule L2_modify_keep_heap_update_rel_stack)
  using assms by auto

lemma L2_call_rel_stack':
  assumes "rel_alloc \<S> M A t\<^sub>0 s t"
  assumes L': "\<And>e e' s. L (hmem s) e e' \<Longrightarrow> L' (hmem s) (emb e) (emb' e') "
  assumes f: "refines f g s t
                (rel_stack \<S> M1 A s t\<^sub>0 (rel_xval_stack L R))"
  shows "refines 
            (L2_call f emb ns)
            (L2_call g emb' ns')
            s t 
            (rel_stack \<S> M1 A s t\<^sub>0 (rel_xval_stack L' R))"
  using assms
  apply (clarsimp simp add: L2_call_def refines_def_old reaches_map_value)
  subgoal for s' r'
    apply (cases r')
    subgoal 
      by (fastforce simp add: default_option_def Exn_def [symmetric] 
          rel_stack_def rel_alloc_def rel_xval_stack_def rel_xval.simps)
    subgoal
      by (fastforce simp add: rel_stack_def rel_alloc_def rel_xval_stack_def rel_xval.simps)
    done
  done


lemma L2_call_rel_stack'':
  assumes "rel_alloc \<S> M A t\<^sub>0 s t"
  assumes L': "\<And>e e' s. L (hmem s) e e' \<Longrightarrow> rel_sum_stack L R' (hmem s) (emb e) (emb' e') "
  assumes f: "refines f g s t
                (rel_stack \<S> M1 A s t\<^sub>0 (rel_xval_stack L R))"
  shows "refines 
            (L2_call f emb ns)
            (L2_call g emb' ns')
            s t 
            (rel_stack \<S> M1 A s t\<^sub>0 (rel_xval_stack (rel_sum_stack L R') R))"
  apply (rule L2_call_rel_stack' [OF assms(1) _ f ])
  by (rule L')

lemma L2_call_rel_stack: 
  assumes "rel_alloc \<S> M A t\<^sub>0 s t"
  assumes L': "\<And>e e' s. L (hmem s) e e' \<Longrightarrow> L' (hmem s) (emb e) (emb e') "
  assumes f: "refines f g s t
                (rel_stack \<S> M1 A s t\<^sub>0 (rel_xval_stack L R))"
  shows "refines 
            (L2_call f emb ns)
            (L2_call g emb ns')
            s t 
            (rel_stack \<S> M1 A s t\<^sub>0 (rel_xval_stack L' R))"
  apply (rule  L2_call_rel_stack' [OF assms (1) _ f])
  by (rule L')

text \<open>Currently exceptions on the function level are terminal and are propagated to the toplevel.
 So the result relation for \<^term>\<open>Inl\<close> is equality.\<close>
lemma L2_call_rel_stack_eq_InL:
  assumes "rel_alloc \<S> M A t\<^sub>0 s t"
  assumes f: "refines f g s t
                (rel_stack \<S> M1 A s t\<^sub>0 (rel_xval_stack (\<lambda>_. (=)) R))"
  shows "refines 
            (L2_call f emb ns)
            (L2_call g emb ns')
            s t 
            (rel_stack \<S> M1 A s t\<^sub>0 (rel_xval_stack (\<lambda>_. (=)) R))"
  apply (rule L2_call_rel_stack' [OF assms(1) _ f ])
  by simp

lemma L2_call_rel_stack_bot_InL:
  assumes "rel_alloc \<S> M A t\<^sub>0 s t"
  assumes f: "refines f g s t
                (rel_stack \<S> M1 A s t\<^sub>0 (rel_xval_stack (\<lambda>_ _ _. False) R))"
  shows "refines 
            (L2_call f emb ns)
            (L2_call g emb ns')
            s t 
            (rel_stack \<S> M1 A s t\<^sub>0 (rel_xval_stack (\<lambda>_ _ _. False) R))"
  apply (rule L2_call_rel_stack' [OF assms(1) _ f])
  by simp
   
lemma L2_seq_rel_stack'': 
  assumes s_t: "rel_alloc \<S> M A t\<^sub>0 s t"
  assumes f1_g1: "refines f1 g1 s t (rel_stack \<S> M1 A s t\<^sub>0 (rel_xval_stack L R1))"
  assumes f2_g2: "\<And>s' t' v w. R1 (hmem s') v w \<Longrightarrow> rel_alloc \<S> M A t\<^sub>0 s' t' \<Longrightarrow> 
                equal_upto (M1 \<union> stack_free (htd s')) (hmem s') (hmem s) \<Longrightarrow>
                htd s' = htd s \<Longrightarrow>
            
             refines (f2 v) (g2' s' w) s' t' (rel_stack \<S> M2 A s' t\<^sub>0 (rel_xval_stack L R))"
  assumes g2'_g2: "\<And>s' t' v w. R1 (hmem s') v w \<Longrightarrow> rel_alloc \<S> M A t\<^sub>0 s' t' \<Longrightarrow> 
                equal_upto (M1 \<union> stack_free (htd s')) (hmem s') (hmem s) \<Longrightarrow>
                htd s' = htd s \<Longrightarrow>
                 g2' s' w = g2 w "

  assumes M1: "M1 \<subseteq> M"
  assumes M2: "M2 \<subseteq> M"
  shows "refines (L2_seq f1 f2) (L2_seq g1 g2) s t (rel_stack \<S> (M1 \<union> M2) A s t\<^sub>0 (rel_xval_stack L R))" 
proof -
  from f2_g2 g2'_g2 
  have f2_g2: "\<And>s' t' v w. R1 (hmem s') v w \<Longrightarrow> rel_alloc \<S> M A t\<^sub>0 s' t' \<Longrightarrow> 
                equal_upto (M1 \<union> stack_free (htd s')) (hmem s') (hmem s) \<Longrightarrow>
                htd s' = htd s \<Longrightarrow>
            
             refines (f2 v) (g2 w) s' t' (rel_stack \<S> M2 A s' t\<^sub>0 (rel_xval_stack L R))"
    by metis
  show ?thesis
  apply (rule refines_L2_seq)
      apply (rule f1_g1)
     apply (simp_all)
  subgoal
    using s_t M1 M2 
    apply (clarsimp simp add: rel_stack_def, intro conjI)
    subgoal 
      by (smt (verit, best) Un_commute disjoint_subset2 disjoint_union_distrib 
          equal_on_stack_free_preservation rel_alloc_def sup.coboundedI2)
    subgoal
      using equal_upto_mono
      by (metis inf_sup_ord(3) order_le_less sup_mono)
    done
  apply (rule refines_mono [OF _ f2_g2  ])
  subgoal
    by (auto simp add: rel_stack_def rel_alloc_def equal_upto_def)
  subgoal
    by (auto simp add: rel_stack_def rel_alloc_def)
  subgoal 
    using M1 M2 s_t
    by (auto simp add: rel_stack_def rel_alloc_def)
  subgoal
    by (auto simp add: rel_stack_def)
  subgoal
    by (auto simp add: rel_stack_def)
  done
qed

lemma L2_seq_rel_stack: (* fixme: remove this variant and make g2_normalised the standard? *)
  assumes s_t: "rel_alloc \<S> M A t\<^sub>0 s t"
  assumes f1_g1: "refines f1 g1 s t (rel_stack \<S> M1 A s t\<^sub>0 (rel_xval_stack L R1))"
  assumes f2_g2: "\<And>s' t' v w. R1 (hmem s') v w \<Longrightarrow> rel_alloc \<S> M A t\<^sub>0 s' t' \<Longrightarrow> 
                equal_upto (M1 \<union> stack_free (htd s')) (hmem s') (hmem s) \<Longrightarrow>
                htd s' = htd s \<Longrightarrow>
            
             refines (f2 v) (g2' w s') s' t' (rel_stack \<S> M2 A s' t\<^sub>0 (rel_xval_stack L R))"
  assumes g2'_g2: "\<And>s' t' v w. R1 (hmem s') v w \<Longrightarrow> rel_alloc \<S> M A t\<^sub>0 s' t' \<Longrightarrow> 
                equal_upto (M1 \<union> stack_free (htd s')) (hmem s') (hmem s) \<Longrightarrow>
                htd s' = htd s \<Longrightarrow>
                 g2' w s' = g2 w "

  assumes M1: "M1 \<subseteq> M"
  assumes M2: "M2 \<subseteq> M"
  assumes M': "M' = M1 \<union> M2"
  shows "refines (L2_seq f1 f2) (L2_seq g1 g2) s t (rel_stack \<S> M' A s t\<^sub>0 (rel_xval_stack L R))" 
proof -
  from f2_g2 g2'_g2 
  have f2_g2: "\<And>s' t' v w. R1 (hmem s') v w \<Longrightarrow> rel_alloc \<S> M A t\<^sub>0 s' t' \<Longrightarrow> 
                equal_upto (M1 \<union> stack_free (htd s')) (hmem s') (hmem s) \<Longrightarrow>
                htd s' = htd s \<Longrightarrow>
            
             refines (f2 v) (g2 w) s' t' (rel_stack \<S> M2 A s' t\<^sub>0 (rel_xval_stack L R))"
    by metis
  show ?thesis
  apply (rule refines_L2_seq)
      apply (rule f1_g1)
     apply (simp_all)
  subgoal
    using s_t M1 M2 M'
    apply (clarsimp simp add: rel_stack_def, intro conjI)
    subgoal 
      by (metis (no_types, lifting) Int_Un_distrib rel_alloc_def sup.absorb_iff1)

    subgoal
      using equal_upto_mono
      by (metis inf_sup_ord(3) order_le_less sup_mono)
    done
  apply (rule refines_mono [OF _ f2_g2  ])
  subgoal
    apply (clarsimp simp add: rel_stack_def rel_alloc_def, intro conjI)
    subgoal by auto (metis M1 M2 M' UnE disjoint_iff equal_on_stack_free_preservation)
    subgoal by (smt (verit, best) M1 M2 M' Un_iff equal_on_stack_free_preservation equal_upto_def)
    done
  subgoal
    by (auto simp add: rel_stack_def rel_alloc_def)
  subgoal 
    using M1 M2 s_t
    apply (auto simp add: rel_stack_def rel_alloc_def)
    done
  subgoal
    by (auto simp add: rel_stack_def)
  subgoal
    by (auto simp add: rel_stack_def)
  done
qed

lemma L2_seq_rel_stack_g2_normalised:
  assumes s_t: "rel_alloc \<S> M A t\<^sub>0 s t"
  assumes f1_g1: "refines f1 g1 s t (rel_stack \<S> M1 A s t\<^sub>0 (rel_xval_stack L R1))"
  assumes f2_g2: "\<And>s' t' v w. R1 (hmem s') v w \<Longrightarrow> rel_alloc \<S> M A t\<^sub>0 s' t' \<Longrightarrow> 
                equal_upto (M1 \<union> stack_free (htd s')) (hmem s') (hmem s) \<Longrightarrow>
                htd s' = htd s \<Longrightarrow>
             refines (f2 v) (g2 w) s' t' (rel_stack \<S> M2 A s' t\<^sub>0 (rel_xval_stack L R))"
  assumes M1: "M1 \<subseteq> M"
  assumes M2: "M2 \<subseteq> M"
  assumes M': "M' = M1 \<union> M2"
  shows "refines (L2_seq f1 f2) (L2_seq g1 g2) s t (rel_stack \<S> M' A s t\<^sub>0 (rel_xval_stack L R))" 
  by (rule L2_seq_rel_stack [OF s_t f1_g1 f2_g2 _ M1 M2 M']) auto

lemma L2_seq_rel_stack': 
  assumes s_t: "rel_alloc \<S> M A t\<^sub>0 s t"
  assumes f1_g1: "refines f1 g1 s t (rel_stack \<S> M1 A s t\<^sub>0 (rel_xval_stack L R1))"
  assumes f2_g2: "\<And>s' t' v w. R1 (hmem s') v w \<Longrightarrow> rel_alloc \<S> M A t\<^sub>0 s' t' \<Longrightarrow> 
             refines (f2 v) (g2 w) s' t' (rel_stack \<S> M2 A s' t\<^sub>0 (rel_xval_stack L R))"
  assumes M1: "M1 \<subseteq> M"
  assumes M2: "M2 \<subseteq> M"
  assumes M': "M' = M1 \<union> M2"
  shows "refines (L2_seq f1 f2) (L2_seq g1 g2) s t (rel_stack \<S> M' A s t\<^sub>0 (rel_xval_stack L R))" 
proof -
  show ?thesis
  apply (rule refines_L2_seq)
      apply (rule f1_g1)
     apply (simp_all)
  subgoal
    using s_t M1 M2 M'
    apply (clarsimp simp add: rel_stack_def, intro conjI)
    subgoal 
      by (metis (no_types, lifting) Int_Un_distrib rel_alloc_def sup.absorb_iff1)

    subgoal
      using equal_upto_mono
      by (metis inf_sup_ord(3) order_le_less sup_mono)
    done
  apply (rule refines_mono [OF _ f2_g2  ])
  subgoal
    apply (clarsimp simp add: rel_stack_def rel_alloc_def, intro conjI)
    subgoal by auto (metis M1 M2 M' UnE disjoint_iff equal_on_stack_free_preservation)
    subgoal by (smt (verit, best) M1 M2 M' Un_iff equal_on_stack_free_preservation equal_upto_def)
    done
  subgoal
    by (auto simp add: rel_stack_def rel_alloc_def)
  subgoal 
    using M1 M2 s_t
    apply (auto simp add: rel_stack_def rel_alloc_def)
    done
  done
qed


lemma frame_raw_frame_union: 
  assumes disj_A_B: "A \<inter> B = {}"
  assumes sf: "stack_free (htd s) \<inter> B = {}"
  shows "frame (A \<union> B) (raw_frame B s t\<^sub>0) s = frame A t\<^sub>0 s"
  apply (clarsimp simp add: frame_def raw_frame_def)
  using override_on_frame_raw_frame_lemma1 [OF disj_A_B sf] 
    override_on_frame_raw_frame_lemma2 [OF disj_A_B sf]
  by (metis (no_types, lifting) heap.upd_cong hmem_htd_upd typing.upd_cong)


lemma refines_narrow_frame':
  assumes disj_B_M: "B \<inter> M = {}"
  assumes disj_A_B: "A \<inter> B = {}"
  assumes spec: "\<And>t\<^sub>0 s t. rel_alloc \<S> M1 (A \<union> B) t\<^sub>0 s t \<Longrightarrow> 
    refines f g s t (rel_stack \<S> M (A \<union> B) s t\<^sub>0 Q)"
  assumes sf: "stack_free (htd s) \<inter> B = {}"
  assumes rel_alloc: "rel_alloc \<S> M1 A t\<^sub>0 s t"
  shows "refines f g s t (rel_stack \<S> M A s t\<^sub>0 Q)"
proof -
  from rel_alloc have t: "t = frame A t\<^sub>0 s" by (auto simp add: rel_alloc_def)
  define t\<^sub>0' where  "t\<^sub>0' = raw_frame B s t\<^sub>0"

  have "t = frame (A \<union> B) t\<^sub>0' s"  
    using frame_raw_frame_union [OF disj_A_B sf]
    by (simp add: t\<^sub>0'_def t)

  
  with rel_alloc sf have rel_alloc': "rel_alloc \<S> M1 (A \<union> B) t\<^sub>0' s t"
    by (auto simp add: t\<^sub>0'_def rel_alloc_def)
  from spec [OF rel_alloc'] have refines': "refines f g s t (rel_stack \<S> M (A \<union> B) s t\<^sub>0' Q)" .
  show ?thesis
  proof (rule refinesI)
    show "succeeds g t \<Longrightarrow> succeeds f s" using refines'
      by (auto simp add: refines_def_old)
  next
    fix v s'
    assume succeeds: "succeeds g t" "succeeds f s" 
    assume result: "reaches f s v s'" 
    show "\<exists>w t'. reaches g t w t' \<and> rel_stack \<S> M A s t\<^sub>0 Q (v, s') (w, t')"
    proof - 
      from succeeds result refines' obtain w t' 
        where  
          res: "reaches g t w t'" and 
          stack: "rel_stack \<S> M (A \<union> B) s t\<^sub>0' Q (v, s') (w, t')"
        by (fastforce simp add: refines_def_old)
      from stack obtain 
        mem_eq: "equal_upto (M \<union> stack_free (htd s')) (hmem s') (hmem s)"  and
        htd_eq1: "equal_upto M (htd s') (htd s)" and
        htd_eq2: "equal_on \<S> (htd s') (htd s)"
        by (auto simp add: rel_stack_def)
  
      from stack
      have sf_eq: "stack_free (htd s') = stack_free (htd s)"
        using disj_A_B by (auto simp add: rel_stack_def) 

      have htd_eq: 
        "override_on (htd s') (override_on (htd t\<^sub>0) (htd s) B) (A \<union> B - stack_free (htd s)) = 
              override_on (htd s') (htd t\<^sub>0) (A - stack_free (htd s))"
        using disj_A_B disj_B_M  sf sf_eq htd_eq1
        apply (clarsimp simp add: override_on_def fun_eq_iff)
        by (auto simp add: equal_upto_def orthD1)

      have hmem_eq: 
        "override_on (hmem s') (override_on (hmem t\<^sub>0) (hmem s) B) (A \<union> B \<union> stack_free (htd s)) = 
             override_on (hmem s') (hmem t\<^sub>0) (A \<union> stack_free (htd s))"
        using disj_A_B disj_B_M sf sf_eq mem_eq
        by (auto simp add: override_on_def fun_eq_iff disjoint_iff equal_upto_def)
    

      from stack have rel_stack': "rel_stack \<S> M A s t\<^sub>0 Q (v, s') (w, t')"
        apply (simp add: t\<^sub>0'_def)
        apply (simp add: rel_stack_def rel_alloc_def)
        apply (clarsimp simp add: frame_def raw_frame_def sf_eq)
        using htd_eq mem_eq 
        by auto (metis (no_types, lifting) heap.upd_cong hmem_eq hmem_htd_upd typing.upd_cong)

      then show ?thesis using res
        by auto
    qed
  qed
qed


lemma refines_narrow_frame:
  assumes subset: "B \<subseteq> A"
  assumes disj_B_M: "B \<inter> M = {}"
  assumes spec: "\<And>t\<^sub>0 s t. rel_alloc \<S> M1 A t\<^sub>0 s t \<Longrightarrow> refines f g s t (rel_stack \<S> M A s t\<^sub>0 Q)"
  assumes sf: "stack_free (htd s) \<inter> B = {}"
  assumes rel_alloc: "rel_alloc \<S> M1 (A - B) t\<^sub>0 s t"
  shows "refines f g s t (rel_stack \<S> M (A - B) s t\<^sub>0 Q)"
proof -
  from subset obtain A1 where A: "A = A1 \<union> B" and disj: "A1 \<inter> B = {}" and A1: "A1 = A - B"
    by (metis Diff_Diff_Int Diff_disjoint Un_Diff_Int inter_sub)
  from refines_narrow_frame'[OF disj_B_M disj spec [simplified A] sf] rel_alloc
  show ?thesis
    by (auto simp add: A1)
qed

lemma refines_widen_modifies:
  assumes "rel_alloc S M A t\<^sub>0 s t"
  assumes "refines f g s t (rel_stack S M' A s t\<^sub>0 Q)"
  assumes "M' \<subseteq> M"
  shows "refines f g s t (rel_stack S M A s t\<^sub>0 Q)" 
  using assms
  apply (clarsimp simp add: refines_def_old  rel_stack_def rel_alloc_def split: prod.splits xval_splits)
  by (smt (verit) UnI2 Un_assoc equal_on_stack_free_preservation equal_upto_def sup.absorb_iff1)

lemma refines_widen_modifies':
  assumes "rel_alloc S M A t\<^sub>0 s t \<Longrightarrow> refines f g s t (rel_stack S M' A s t\<^sub>0 Q)"
  assumes "M' \<subseteq> M"
  assumes "rel_alloc S M A t\<^sub>0 s t"
  shows "refines f g s t (rel_stack S M A s t\<^sub>0 Q)" 
  using refines_widen_modifies assms by blast

lemma refines_widen_modifies'':
  assumes "rel_alloc S M A t\<^sub>0 s t"
  assumes "refines f g s t (rel_stack S M1 A s t\<^sub>0 Q)"
  assumes "M1 \<subseteq> M2"
  assumes "M2 \<subseteq> M"
  shows "refines f g s t (rel_stack S M2 A s t\<^sub>0 Q)" 
  using refines_widen_modifies assms rel_alloc_modifies_antimono
  by blast


lemma refines_widen_modifies_weaken:
  assumes alloc: "rel_alloc S M A t\<^sub>0 s t"
  assumes f: "refines f g s t (rel_stack S M1 A s t\<^sub>0 Q')"
  assumes M1_M2: "M1 \<subseteq> M2"
  assumes M2_M: "M2 \<subseteq> M"
  assumes weaken: "\<And>h r r'. Q' h r r' \<Longrightarrow> Q h r r'"
  shows "refines f g s t (rel_stack S M2 A s t\<^sub>0 Q)" 
proof -
  have "refines f g s t (rel_stack S M1 A s t\<^sub>0 Q)"
    apply (rule refines_weaken [OF f])
    using weaken by (auto simp add: rel_stack_def)
  with alloc M1_M2 M2_M refines_widen_modifies rel_alloc_modifies_antimono refines_weaken
  show ?thesis
    by blast
qed

lemma L2_condition_rel_stack:
  assumes s_t: "rel_alloc \<S> M A t\<^sub>0 s t"
  assumes c_c': "c s = c' (frame A t\<^sub>0 s)"
  assumes f1_g1: "refines f1 g1 s t (rel_stack \<S> M1 A s t\<^sub>0 (rel_xval_stack L R))"
  assumes f2_g2: "refines f2 g2 s t (rel_stack \<S> M2 A s t\<^sub>0 (rel_xval_stack L R))"
  assumes M1: "M1 \<subseteq> M"
  assumes M2: "M2 \<subseteq> M"
  assumes M': "M' = M1 \<union> M2"
  shows "refines (L2_condition c f1 f2) (L2_condition c' g1 g2) s t (rel_stack \<S> M' A s t\<^sub>0 (rel_xval_stack L R))"
  unfolding L2_condition_def
  apply (rule refines_condition)
  subgoal using s_t c_c' by (auto simp add: rel_alloc_def)
  subgoal apply (rule refines_widen_modifies [OF _ f1_g1]) using s_t M1 M2 M' rel_alloc_modifies_antimono by auto 
  subgoal apply (rule refines_widen_modifies [OF _ f2_g2]) using s_t M1 M2 M' rel_alloc_modifies_antimono by auto
  done


lemma L2_while_rel_stack'':
  assumes s_t: "rel_alloc \<S> M A t\<^sub>0 s t"
  assumes R_i: "R (hmem s) i i'"
  assumes refines_condition: "\<And>s v v'. R (hmem s) v v' \<Longrightarrow> c' v' (frame A t\<^sub>0 s) = c v s"
  assumes bdy: "\<And>s t v v'. R (hmem s) v v' \<Longrightarrow> rel_alloc \<S> M1 A t\<^sub>0 s t \<Longrightarrow> c v s \<Longrightarrow> c' v' t \<Longrightarrow> 
              refines (f v) (g v') s t (rel_stack \<S> M1 A s t\<^sub>0 (rel_xval_stack L R))"
  assumes M1: "M1 \<subseteq> M"
  shows "refines (L2_while c f i ns) (L2_while c' g i' ns') s t (rel_stack \<S> M1 A s t\<^sub>0 (rel_xval_stack L R))"
  unfolding L2_while_def
  apply (rule refines_whileLoop_exn)
  subgoal by (auto simp add: rel_stack_def refines_condition rel_alloc_def)
  subgoal for v s' w t' 
    apply clarsimp
    apply (rule refines_mono [OF _ bdy])
    subgoal 
      apply (clarsimp simp add: rel_stack_def )
      subgoal by (metis equal_upto_trans)
      done
    apply (auto simp add: rel_stack_def)
    done
  apply (auto simp add: s_t R_i rel_stack_def rel_alloc_modifies_antimono [OF _ M1])
  done

lemma L2_while_rel_stack''':
  assumes s_t: "rel_alloc \<S> M A t\<^sub>0 s t"
  assumes R_i: "R (hmem s) i i'"
  assumes refines_condition: "\<And>s v v'. R (hmem s) v v' \<Longrightarrow> c' v' (frame A t\<^sub>0 s) = c v s"
  assumes bdy: "\<And>s t v v'. R (hmem s) v v' \<Longrightarrow> rel_alloc \<S> M A t\<^sub>0 s t \<Longrightarrow> c v s \<Longrightarrow> c' v' t \<Longrightarrow> 
              refines (f v) (g v') s t (rel_stack \<S> M1 A s t\<^sub>0 (rel_xval_stack L R))"
  assumes M1: "M1 \<subseteq> M"
  shows "refines (L2_while c f i ns) (L2_while c' g i' ns') s t (rel_stack \<S> M1 A s t\<^sub>0 (rel_xval_stack L R))"
  unfolding L2_while_def
  apply (rule refines_whileLoop_exn)
  subgoal by (auto simp add: rel_stack_def refines_condition rel_alloc_def)
  subgoal for v s' w t' 
    apply clarsimp
    apply (rule refines_mono [OF _ bdy])
        apply (clarsimp simp add: rel_stack_def )
        apply (metis  equal_upto_trans)
    using s_t by (auto simp add: rel_stack_def rel_alloc_def)
   apply (auto simp add: s_t R_i rel_stack_def rel_alloc_modifies_antimono [OF _ M1])
  done

lemma L2_while_rel_stack':
  assumes s_t: "rel_alloc \<S> M A t\<^sub>0 s t"
  assumes refines_condition: "\<And>s v v'. R (hmem s) v v' \<Longrightarrow> c' v' (frame A t\<^sub>0 s) = c v s"
  assumes R_i: "R (hmem s) i i'"
  assumes bdy: "\<And>s t v v'. R (hmem s) v v' \<Longrightarrow> rel_alloc \<S> M A t\<^sub>0 s t \<Longrightarrow>  
              refines (f v) (g v') s t (rel_stack \<S> M1 A s t\<^sub>0 (rel_xval_stack L R))"
  assumes M1: "M1 \<subseteq> M"
  shows "refines (L2_while c f i ns) (L2_while c' g i' ns') s t (rel_stack \<S> M1 A s t\<^sub>0 (rel_xval_stack L R))"
  unfolding L2_while_def
  apply (rule refines_whileLoop_exn)
  subgoal by (auto simp add: rel_stack_def refines_condition rel_alloc_def)
  subgoal for v s' w t' 
    apply clarsimp
    apply (rule refines_mono [OF _ bdy])
      apply (clarsimp simp add: rel_stack_def )
      apply (metis equal_upto_trans)
    subgoal by (auto simp add: rel_stack_def)
    subgoal using s_t by (simp add: rel_stack_def) (metis rel_alloc_def)
    done
    apply (auto simp add: s_t R_i rel_stack_def rel_alloc_modifies_antimono [OF _ M1])
  done

lemma L2_while_rel_stack:
  assumes s_t: "rel_alloc \<S> M A t\<^sub>0 s t"
  assumes R_i: "R (hmem s) i i'"
  assumes bdy: "\<And>s' t' v w. R (hmem s') v w \<Longrightarrow> rel_alloc \<S> M A t\<^sub>0 s' t' \<Longrightarrow> c v s' \<Longrightarrow> c' w t' \<Longrightarrow> 
                  equal_upto (M1 \<union> stack_free (htd s')) (hmem s') (hmem s) \<Longrightarrow>
                  htd s' = htd s \<Longrightarrow>
                refines (f v) (g' w s') s' t' (rel_stack \<S> M1 A s' t\<^sub>0 (rel_xval_stack L R))"
  assumes refines_condition: "\<And>s' t'  v w. R (hmem s') v w \<Longrightarrow> rel_alloc \<S> M A t\<^sub>0 s' t' \<Longrightarrow>
            equal_upto (M1 \<union> stack_free (htd s')) (hmem s') (hmem s) \<Longrightarrow> htd s' = htd s \<Longrightarrow> 
            c' w t' = c v s'"
  assumes g'_g: "\<And>s' t' v w. R (hmem s') v w \<Longrightarrow> rel_alloc \<S> M A t\<^sub>0 s' t' \<Longrightarrow> 
                equal_upto (M1 \<union> stack_free (htd s')) (hmem s') (hmem s) \<Longrightarrow>
                htd s' = htd s \<Longrightarrow>
                 g' w s' = g w"
  assumes M1: "M1 \<subseteq> M"
  shows "refines (L2_while c f i ns) (L2_while c' g i' ns') s t (rel_stack \<S> M1 A s t\<^sub>0 (rel_xval_stack L R))"
  unfolding L2_while_def
  apply (rule refines_mono [where R = "\<lambda>(r, s') (w, t').  
         equal_upto (M1 \<union> stack_free (htd s')) (hmem s') (hmem s) \<and>
         htd s' = htd s \<and> 
         (rel_stack \<S> M1 A s' t\<^sub>0 (rel_xval_stack L R)) (r, s') (w, t')"  ])
  subgoal
    by (auto simp add: rel_stack_def)
  apply (rule refines_whileLoop_exn)
  subgoal using s_t by (auto simp add: rel_stack_def refines_condition rel_alloc_def)
  subgoal for v s' w t' 
    apply clarsimp
    apply (rule refines_weaken [where R="(rel_stack \<S> M1 A s' t\<^sub>0 (rel_xval_stack L R))"] )
     apply (subst g'_g [of s' v w t', symmetric])
         apply (simp add: rel_stack_def)

        apply (simp add: rel_stack_def)
    using rel_alloc_def s_t 
        apply force
       apply simp
      apply simp
     apply (rule bdy)
           apply (simp add: rel_stack_def)
               apply (simp add: rel_stack_def)
              using s_t apply (metis equal_on_stack_free_preservation rel_alloc_def)
          apply simp
         apply simp
        apply simp
       apply simp
      apply simp
    apply (clarsimp simp add: rel_stack_def)
    apply (metis equal_upto_trans)
    done
    apply (smt (verit) L2_split_fixup_3 M1 R_i equal_upto_refl heap_state.rel_stack_def heap_state_axioms rel_alloc_modifies_antimono rel_xval_stack_simps(2) s_t)
   apply (auto simp add: s_t R_i rel_stack_def rel_alloc_modifies_antimono [OF _ M1])
  done


lemma L2_while_rel_stack_g_normalised:
  assumes s_t: "rel_alloc \<S> M A t\<^sub>0 s t"
  assumes R_i: "R (hmem s) i i'"
  assumes bdy: "\<And>s' t' v w. R (hmem s') v w \<Longrightarrow> rel_alloc \<S> M A t\<^sub>0 s' t' \<Longrightarrow> c v s' \<Longrightarrow> c' w t' \<Longrightarrow> 
                  equal_upto (M1 \<union> stack_free (htd s')) (hmem s') (hmem s) \<Longrightarrow>
                  htd s' = htd s \<Longrightarrow>
                refines (f v) (g w) s' t' (rel_stack \<S> M1 A s' t\<^sub>0 (rel_xval_stack L R))"
  assumes refines_condition: "\<And>s' t'  v w. R (hmem s') v w \<Longrightarrow> rel_alloc \<S> M A t\<^sub>0 s' t' \<Longrightarrow>
            equal_upto (M1 \<union> stack_free (htd s')) (hmem s') (hmem s) \<Longrightarrow> htd s' = htd s \<Longrightarrow> 
            c' w t' = c v s'"
  assumes M1: "M1 \<subseteq> M"
  shows "refines (L2_while c f i ns) (L2_while c' g i' ns') s t (rel_stack \<S> M1 A s t\<^sub>0 (rel_xval_stack L R))"
  apply (rule L2_while_rel_stack [OF s_t R_i bdy refines_condition _ M1])
  by auto



lemma L2_while_rel_stack_g_normalised_guarded:
  assumes s_t: "rel_alloc \<S> M A t\<^sub>0 s t"
  assumes R_i: "R (hmem s) i i'"
  assumes bdy: "\<And>s' t' v w. R (hmem s') v w \<Longrightarrow> rel_alloc \<S> M A t\<^sub>0 s' t' \<Longrightarrow> c v s' \<Longrightarrow> c' w t' \<Longrightarrow> 
                  equal_upto (M1 \<union> stack_free (htd s')) (hmem s') (hmem s) \<Longrightarrow>
                  htd s' = htd s \<Longrightarrow> 
                refines (f v) (g w) s' t' (rel_stack \<S> M1 A s' t\<^sub>0 (rel_xval_stack L R))"
  assumes refines_condition: "\<And>s' t'  v w. R (hmem s') v w \<Longrightarrow> rel_alloc \<S> M A t\<^sub>0 s' t' \<Longrightarrow>
            equal_upto (M1 \<union> stack_free (htd s')) (hmem s') (hmem s) \<Longrightarrow> htd s' = htd s \<Longrightarrow> G' w t' \<Longrightarrow>
            c' w t' = c v s'"
  assumes M1: "M1 \<subseteq> M"
  assumes G_G': "G t = G' i' t"
  shows "refines (L2_while c f i ns) 
              (L2_seq (L2_guard G) 
                (\<lambda>_. (L2_while c' (\<lambda>v. L2_seq (g v) (\<lambda>res. L2_seq (L2_guard (G' res)) (\<lambda>_. L2_gets (\<lambda>_. res) ns'))) i' ns')) ) s t (rel_stack \<S> M1 A s t\<^sub>0 (rel_xval_stack L R))"
  apply (rule refines_mono [where R = "\<lambda>(r, s') (w, t').  
         equal_upto (M1 \<union> stack_free (htd s')) (hmem s') (hmem s) \<and>
         htd s' = htd s \<and> 
         (rel_stack \<S> M1 A s' t\<^sub>0 (rel_xval_stack L R)) (r, s') (w, t')"  ])
  subgoal
    by (auto simp add: rel_stack_def)
  unfolding L2_defs gets_return
  apply (rule refines_whileLoop_guard_right)
  subgoal using s_t by (auto simp add: rel_stack_def refines_condition rel_alloc_def)
  subgoal for v s' w t' 
    apply clarsimp
    apply (rule refines_weaken [where R="(rel_stack \<S> M1 A s' t\<^sub>0 (rel_xval_stack L R))"] )
     apply (rule bdy)
    subgoal by (auto simp add: rel_stack_def)
    subgoal using rel_alloc_def s_t by (auto simp add: rel_stack_def)
    subgoal by simp
    subgoal by simp
    subgoal using s_t by simp
    subgoal by simp
    subgoal 
      apply (clarsimp simp add: rel_stack_def)
      apply (metis equal_upto_trans)
      done
    done
  subgoal by (auto simp add: rel_stack_def)
  subgoal using R_i s_t by (auto simp add: rel_stack_def rel_alloc_modifies_antimono [OF _ M1])
  subgoal using G_G' by simp
  done


lemma L2_unknown_rel_stack:
  assumes s_t: "rel_alloc \<S> M A t\<^sub>0 s t"
  shows "refines (L2_unknown ns) (L2_unknown ns) s t (rel_stack \<S> {} A s t\<^sub>0 (rel_xval_stack L (\<lambda>_. (=))))"
  using s_t
  by (auto simp add: L2_unknown_def refines_def_old rel_stack_def rel_alloc_modifies_antimono)

lemma L2_fail_rel_stack:
  assumes s_t: "rel_alloc \<S> M A t\<^sub>0 s t"
  shows "refines (L2_fail) (L2_fail) s t (rel_stack \<S> {} A s t\<^sub>0 (rel_xval_stack L R))"
  using s_t
  by (auto simp add: L2_fail_def refines_def_old rel_stack_def rel_alloc_modifies_antimono)

lemma L2_skip_rel_stack:
  assumes s_t: "rel_alloc \<S> M A t\<^sub>0 s t"
  shows "refines L2_skip L2_skip s t (rel_stack \<S> {} A s t\<^sub>0 (rel_xval_stack L (\<lambda>_. (=))))"
  using s_t
  by (auto simp add: L2_gets_def refines_def_old rel_stack_def rel_alloc_modifies_antimono)

(* FIXME: derive more simple rule or setup simplification for standard cases: 
  e.g. r'=r and heap / heap_typing does not change at all
*)
lemma L2_spec_rel_stack:
  assumes s_t: "rel_alloc \<S> M A t\<^sub>0 s t"
  assumes "\<And>t'. (frame A t\<^sub>0 s, t') \<in> r' \<Longrightarrow> \<exists>s'. (s, s') \<in> r"
  assumes "\<And>s'. (s, s') \<in> r \<Longrightarrow> (frame A t\<^sub>0 s, frame A t\<^sub>0 s') \<in> r'"
  assumes "\<And>s'. (s, s') \<in> r \<Longrightarrow> equal_upto (M \<union> stack_free (htd s')) (hmem s') (hmem s)" 
  assumes "\<And>s'. (s, s') \<in> r \<Longrightarrow> htd s' = htd s"
  assumes "\<And>s'. (s, s') \<in> r \<Longrightarrow> stack_free (htd s') \<subseteq> \<S>" 
  assumes "\<And>s'. (s, s') \<in> r \<Longrightarrow> stack_free (htd s') \<inter> A = {}" 
  assumes "\<And>s'. (s, s') \<in> r \<Longrightarrow> stack_free (htd s') \<inter> M = {}"
  shows "refines (L2_spec r) (L2_spec r') s t (rel_stack \<S> M A s t\<^sub>0 (rel_xval_stack L (\<lambda>_. (=))))"
  using assms
  by (auto simp add: L2_spec_def refines_def_old rel_stack_def rel_alloc_def succeeds_bind reaches_bind)


lemma L2_spec_rel_stack':
  assumes s_t: "rel_alloc \<S> M A t\<^sub>0 s t"
  assumes "\<And>t'. rel_alloc \<S> M A t\<^sub>0 s t \<Longrightarrow> (frame A t\<^sub>0 s, t') \<in> r' \<Longrightarrow> \<exists>s'. (s, s') \<in> r"
  assumes "\<And>s'. rel_alloc \<S> M A t\<^sub>0 s t \<Longrightarrow> (s, s') \<in> r \<Longrightarrow> (frame A t\<^sub>0 s, frame A t\<^sub>0 s') \<in> r'"
  assumes "\<And>s'. rel_alloc \<S> M A t\<^sub>0 s t \<Longrightarrow> (s, s') \<in> r \<Longrightarrow> equal_upto (M \<union> stack_free (htd s')) (hmem s') (hmem s)"
  assumes "\<And>s'. rel_alloc \<S> M A t\<^sub>0 s t \<Longrightarrow> (s, s') \<in> r \<Longrightarrow> htd s' = htd s"
  assumes "\<And>s'. rel_alloc \<S> M A t\<^sub>0 s t \<Longrightarrow> (s, s') \<in> r \<Longrightarrow> stack_free (htd s') \<subseteq> \<S>"
  assumes "\<And>s'. rel_alloc \<S> M A t\<^sub>0 s t \<Longrightarrow> (s, s') \<in> r \<Longrightarrow> stack_free (htd s') \<inter> A = {}"
  assumes "\<And>s'. rel_alloc \<S> M A t\<^sub>0 s t \<Longrightarrow> (s, s') \<in> r \<Longrightarrow> stack_free (htd s') \<inter> M = {}"
  shows "refines (L2_spec r) (L2_spec r') s t (rel_stack \<S> M A s t\<^sub>0 (rel_xval_stack L (\<lambda>_. (=))))"
  using s_t assms(2-8) [OF s_t] by (rule L2_spec_rel_stack)

lemma L2_spec_rel_stack_same:
  assumes s_t: "rel_alloc \<S> M A t\<^sub>0 s t"
  assumes "\<And>t'. rel_alloc \<S> M A t\<^sub>0 s t \<Longrightarrow> (frame A t\<^sub>0 s, t') \<in> r \<Longrightarrow> \<exists>s'. (s, s') \<in> r"
  assumes "\<And>s'. rel_alloc \<S> M A t\<^sub>0 s t \<Longrightarrow> (s, s') \<in> r \<Longrightarrow> (frame A t\<^sub>0 s, frame A t\<^sub>0 s') \<in> r"
  assumes "\<And>s'. rel_alloc \<S> M A t\<^sub>0 s t \<Longrightarrow> (s, s') \<in> r \<Longrightarrow> equal_upto (M \<union> stack_free (htd s')) (hmem s') (hmem s)"
  assumes "\<And>s'. rel_alloc \<S> M A t\<^sub>0 s t \<Longrightarrow> (s, s') \<in> r \<Longrightarrow> htd s' = htd s"
  assumes "\<And>s'. rel_alloc \<S> M A t\<^sub>0 s t \<Longrightarrow> (s, s') \<in> r \<Longrightarrow> stack_free (htd s') \<subseteq> \<S>" 
  assumes "\<And>s'. rel_alloc \<S> M A t\<^sub>0 s t \<Longrightarrow> (s, s') \<in> r \<Longrightarrow> stack_free (htd s') \<inter> A = {}" 
  assumes "\<And>s'. rel_alloc \<S> M A t\<^sub>0 s t \<Longrightarrow> (s, s') \<in> r \<Longrightarrow> stack_free (htd s') \<inter> M = {}"
  shows "refines (L2_spec r) (L2_spec r) s t (rel_stack \<S> M A s t\<^sub>0 (rel_xval_stack L (\<lambda>_. (=))))"
  using assms
  by (rule L2_spec_rel_stack')

lemma L2_spec_rel_stack_heap_agnostic:
  assumes s_t: "rel_alloc \<S> M A t\<^sub>0 s t"
  assumes hmem_unchanged: "\<And>s s'. (s, s') \<in> r \<Longrightarrow> hmem s' = hmem s"
  assumes htd_unchanged: "\<And>s s'. (s, s') \<in> r \<Longrightarrow> htd s' = htd s"
  assumes heap_irrelevant: "\<And>s s' f g. (s, s') \<in> r \<Longrightarrow> (hmem_upd g (htd_upd f s), hmem_upd g (htd_upd f s')) \<in> r"
  shows "refines (L2_spec r) (L2_spec r) s t (rel_stack \<S> {} A s t\<^sub>0 (rel_xval_stack L (\<lambda>_. (=))))"
proof -
  have "refines (L2_spec r) (L2_spec r) s t (rel_stack \<S> M A s t\<^sub>0 (rel_xval_stack L (\<lambda>_. (=))))"
    apply (rule L2_spec_rel_stack_same [OF s_t])
    subgoal premises prems for t'
    proof -
      from prems have r: "(frame A t\<^sub>0 s, t') \<in> r" by simp
      have s_eq: "s = hmem_upd (\<lambda>_. hmem s) ((htd_upd (\<lambda>_. htd s) (frame A t\<^sub>0 s)))"
        apply (simp add: frame_def)
        by (metis equal_upto_heap_on_def equal_upto_heap_on_frame frame_def heap.get_upd htd_hmem_upd typing.get_upd)
      show ?thesis
        apply (subst s_eq)
        apply (rule exI)
        apply (rule heap_irrelevant)
        apply (rule r)
        done
    qed
    subgoal
      apply (simp add: frame_def)
      using heap_irrelevant htd_unchanged
      by simp
    subgoal
      using hmem_unchanged by simp
    subgoal
      using htd_unchanged by simp
    subgoal
      using htd_unchanged by (simp add: rel_alloc_def)
    subgoal
      using htd_unchanged by (simp add: rel_alloc_def)
    subgoal
      using htd_unchanged by (simp add: rel_alloc_def)
    done
  then show ?thesis
    using hmem_unchanged htd_unchanged
    apply (clarsimp simp add: L2_spec_def refines_def_old rel_stack_def rel_alloc_def reaches_bind 
        succeeds_bind)
      apply (meson UNIV_I image_eqI)
     apply force+
    done
qed



(* FIXME: how to setup automatic refinement proof? Simplified setup for standard cases, e.g. relation
   not touching the heap? 
*)
lemma L2_assume_rel_stack:
  assumes s_t: "rel_alloc \<S> M A t\<^sub>0 s t"
  assumes "\<And>v s'. (v, s') \<in> f s \<Longrightarrow> 
    \<exists>w. (w, frame A t\<^sub>0 s') \<in> g (frame A t\<^sub>0 s) \<and> rel_stack \<S> M A s t\<^sub>0 R (v, s') (w, frame A t\<^sub>0 s')" 
  shows "refines (L2_assume f) (L2_assume g) s t (rel_stack \<S> M A s t\<^sub>0 (rel_xval_stack L R))"
  using assms
  apply (clarsimp simp add: L2_assume_def refines_def_old rel_alloc_def rel_stack_def)
  by metis

lemma L2_assume_rel_stack_heap_agnostic:
  assumes s_t: "rel_alloc \<S> M A t\<^sub>0 s t"
  assumes hmem_unchanged: "\<And>a s s'. (a, s') \<in> f s \<Longrightarrow> hmem s' = hmem s"
  assumes htd_unchanged: "\<And>a s s'. (a, s') \<in> f s \<Longrightarrow> htd s' = htd s"
  assumes heap_irrelevant: "\<And>a s s' g h. (a, s') \<in> f s \<Longrightarrow> (a, hmem_upd h (htd_upd g s')) \<in> f (hmem_upd h (htd_upd g s))"
  shows "refines (L2_assume f) (L2_assume f) s t (rel_stack \<S> {} A s t\<^sub>0 (rel_xval_stack L (\<lambda>_. (=))))"
  apply (rule L2_assume_rel_stack)
  subgoal
    using s_t
    by (auto simp add: L2_assume_def refines_def_old rel_stack_def rel_alloc_def)
  subgoal for v s'
    apply (rule exI[where x=v])
    apply (intro conjI)
    subgoal
      using frame_def heap_irrelevant htd_unchanged by presburger
    subgoal
      apply (clarsimp simp: rel_stack_def frame_def)
      apply (intro conjI)
      subgoal using \<open>rel_alloc \<S> {} A t\<^sub>0 s t\<close> frame_def htd_unchanged rel_alloc_def by force
      subgoal using hmem_unchanged by force
      subgoal using htd_unchanged by blast
      done
    done
  done


lemma refines_rel_stack_embed_result': 
  assumes rel_alloc: "rel_alloc \<S> M A t\<^sub>0 s t"
  assumes f: "refines f g s t (rel_stack \<S> M1 A s t\<^sub>0 (rel_xval_stack L R))"
  assumes R1: "\<And>v s' w t'. rel_alloc \<S> M A t\<^sub>0 s' t' \<Longrightarrow> R (hmem s') v w \<Longrightarrow>
             equal_upto (M1 \<union> stack_free (htd s')) (hmem s') (hmem s) \<Longrightarrow>  
             htd s' = htd s \<Longrightarrow>
              R1 (hmem s') v (emb w)"
  assumes M2_M: "M2 \<subseteq> M"
  assumes M1_M2: "M1 \<subseteq> M2"
  shows "refines f (L2_seq g (ETA_TUPLED (\<lambda>x. L2_gets (\<lambda>_. emb x) ns))) s t (rel_stack \<S> M2 A s t\<^sub>0 (rel_xval_stack L R1))"
  unfolding L2_defs ETA_TUPLED_def
  apply (subst bind_return [symmetric, of f])
  apply (rule refines_bind_bind_exn [OF f])
  subgoal
    using M1_M2 M2_M rel_alloc
    apply (clarsimp simp add: rel_stack_def rel_alloc_def)
    by auto (meson Un_mono equal_upto_mono equalityE)
  subgoal by auto
  subgoal by auto
  subgoal
    apply (clarsimp simp add: gets_return rel_stack_def)
    apply (intro conjI)
    subgoal using R1 rel_alloc by (auto simp add: rel_alloc_def)
    subgoal using M2_M rel_alloc by (auto simp add: rel_alloc_def)
    subgoal using M1_M2 by (meson equal_upto_mono equalityD2 sup.mono)
    done
  done

lemma refines_rel_stack_root_upd_result: 
  assumes rel_alloc: "rel_alloc \<S> M A t\<^sub>0 s t"
  assumes f: "P t \<Longrightarrow> refines f (L2_seq (L2_guard P) (\<lambda>_. g)) s t (rel_stack \<S> M1 A s t\<^sub>0 (rel_xval_stack L R))"
  assumes R1: "\<And>v s' w t'. rel_alloc \<S> M A t\<^sub>0 s' t' \<Longrightarrow> R (hmem s') v w \<Longrightarrow> P t \<Longrightarrow>
             equal_upto (M1 \<union> stack_free (htd s')) (hmem s') (hmem s) \<Longrightarrow>  
             htd s' = htd s \<Longrightarrow>
              R1 (hmem s') v (emb w)"
  assumes M2_M: "P t \<Longrightarrow> M2 \<subseteq> M"
  assumes M1_M2: "P t \<Longrightarrow> M1 \<subseteq> M2"
  shows "refines f (L2_seq (L2_guard P) (\<lambda>_. L2_seq g (ETA_TUPLED (\<lambda>x. L2_gets (\<lambda>_. emb x) ns)))) s t (rel_stack \<S> M2 A s t\<^sub>0 (rel_xval_stack L R1))"
  using refines_rel_stack_embed_result'[OF assms(1) _ _ assms(4,5), of f g L R R1 emb]
  using assms(2,3)
  by (auto simp add: refines_bind_guard_right_iff L2_defs ETA_TUPLED_def)

lemma refines_rel_stack_embed_exit: 
  assumes rel_alloc: "rel_alloc \<S> M A t\<^sub>0 s t"
  assumes f: "refines f g s t (rel_stack \<S> M1 A s t\<^sub>0 (rel_xval_stack L R))"
  assumes L1: "\<And>v s' w t'. rel_alloc \<S> M A t\<^sub>0 s' t' \<Longrightarrow> L (hmem s') v w \<Longrightarrow>
             equal_upto (M1 \<union> stack_free (htd s')) (hmem s') (hmem s) \<Longrightarrow>  
             htd s' = htd s \<Longrightarrow>
              L1 (hmem s') v (emb w)"
  assumes M2_M: "M2 \<subseteq> M"
  assumes M1_M2: "M1 \<subseteq> M2"
  shows "refines 
  f (L2_catch g (ETA_TUPLED (\<lambda>x. L2_throw (emb x) ns))) s t 
  (rel_stack \<S> M2 A s t\<^sub>0 (rel_xval_stack L1 R))"
  unfolding L2_defs ETA_TUPLED_def
  apply (subst f_catch_throw [symmetric, of f])
  apply (rule refines_catch [OF assms(2)])
  subgoal
    apply (clarsimp simp add: rel_stack_def, intro conjI)
    subgoal using L1 rel_alloc by (auto simp add: rel_alloc_def)
    subgoal using M2_M rel_alloc by (auto simp add: rel_alloc_def)
    subgoal using M1_M2 by (meson equal_upto_mono equalityD2 sup.mono)
    done
  subgoal by auto
  subgoal by auto
  subgoal 
    apply (simp add: rel_stack_def)
    apply (intro conjI)
    subgoal using M2_M rel_alloc by (auto simp add: rel_alloc_def)
    subgoal using M1_M2 by auto (meson equal_upto_mono equalityD2 sup.mono)
    done
  done

lemma refines_rel_stack_embed_both: 
  assumes stack: "rel_alloc \<S> M A t\<^sub>0 s t"
  assumes f_g: "refines f g s t (rel_stack \<S> M1 A s t\<^sub>0 (rel_xval_stack L R))"
  assumes L: "\<And>v s' w t'. rel_alloc \<S> M A t\<^sub>0 s' t' \<Longrightarrow> L (hmem s') v w \<Longrightarrow>
             equal_upto (M1 \<union> stack_free (htd s')) (hmem s') (hmem s) \<Longrightarrow>  
             htd s' = htd s \<Longrightarrow>
              L1 (hmem s') v (embL w)"
  assumes R: "\<And>v s' w t'. rel_alloc \<S> M A t\<^sub>0 s' t' \<Longrightarrow> R (hmem s') v w \<Longrightarrow>
             equal_upto (M1 \<union> stack_free (htd s')) (hmem s') (hmem s) \<Longrightarrow>  
             htd s' = htd s \<Longrightarrow>
              R1 (hmem s') v (embR w)"
  assumes M2_M: "M2 \<subseteq> M"
  assumes M1_M2: "M1 \<subseteq> M2"
  shows "refines 
  f  
  (L2_seq  
    (L2_catch g (ETA_TUPLED (\<lambda>x. L2_throw (embL x) ns)))
    (ETA_TUPLED (\<lambda>x. L2_gets (\<lambda>_. embR x) ns))) s t 
  (rel_stack \<S> M2 A s t\<^sub>0 (rel_xval_stack L1 R1))"
  apply (rule refines_rel_stack_embed_result' [OF stack _  _ M2_M M1_M2, where R=R])
  subgoal
    apply (rule refines_rel_stack_embed_exit [OF stack f_g ])
    subgoal
      by (rule L)
    subgoal using M1_M2 M2_M by auto
    subgoal by auto
    done
  subgoal
    by (rule R)
  done
end

 (*
  {p, q, y} \<subseteq> A
  {p1, q1} \<inter> A = {}
*)
lemma refines_assume_result_and_state_left: 
  assumes "\<And>s' v. (v, s') \<in> A s \<Longrightarrow> refines (f v) g s' t Q"
  shows "refines (do { v <- assume_result_and_state A; f v }) g s t Q"
  using assms
  apply (auto simp add: refines_def_old succeeds_bind reaches_bind split: xval_splits)
  done

lemma refines_assume_result_and_state_right: 
  assumes "A t \<noteq> {}"
  assumes "\<And>t' v. (v, t') \<in> A t \<Longrightarrow> refines f (g v) s t' Q"
  shows "refines f (do { v <- assume_result_and_state A; g v })  s t Q"
  using assms
  apply (clarsimp simp add: refines_def_old succeeds_bind reaches_bind 
      split: exception_or_result_splits )
  by auto (metis (no_types, opaque_lifting) Result_eq_Result is_Result_simps(1) is_Result_simps(2))

lemma refines_assume_result_and_state_both: 
  assumes "B t = {} \<Longrightarrow> A s = {}"
  assumes "\<And>s' v t' w. (v, s') \<in> A s \<Longrightarrow> (w, t') \<in> B t \<Longrightarrow> refines (f v) (g w) s' t' Q"
  shows "refines (do { v <- assume_result_and_state A; f v }) (do {w <- assume_result_and_state B; g w }) s t Q"
  apply (rule refines_bind')
  apply (simp add: refines_assume_result_and_state_iff)
  using assms
  by (force simp add: sim_set_def)

lemma refines_assume_result_and_state_both_same_val': 
  assumes "\<And>s' v. (v, s') \<in> A s \<Longrightarrow> \<exists>t'. (v, t') \<in> B t \<and> refines (f v) (g v) s' t' Q"
  shows "refines (do { v <- assume_result_and_state A; f v }) (do { v <- assume_result_and_state B; g v })  s t Q"
  apply (rule refines_bind')
  apply (simp add: refines_assume_result_and_state_iff)
  using assms
  by (force simp add: sim_set_def)


lemma refines_assume_result_and_state_both_same_val: 
  assumes "\<And>v s'. (v, s') \<in> A s \<Longrightarrow> \<exists>t'. (v, t') \<in> B t"
  assumes "\<And>s' v t'. (v, s') \<in> A s \<Longrightarrow> (v, t') \<in> B t \<Longrightarrow> refines (f v) (g v) s' t' Q"
  shows "refines (do { v <- assume_result_and_state A; f v }) (do { v <- assume_result_and_state B; g v }) s t Q"
  apply (rule refines_bind')
  apply (simp add: refines_assume_result_and_state_iff)
  using assms
  by (force simp add: sim_set_def)


lemma refines_assume_result_and_state_both_same_val_frame: 
  assumes f: "t = frm s"
  assumes "\<And>s' v. (v, s') \<in> A s \<Longrightarrow> (v, frm s') \<in> B t"
  assumes "\<And>s' v. (v, s') \<in> A s \<Longrightarrow>  refines (f v) (g v) s' (frm s') Q"
  shows "refines (do { v <- assume_result_and_state A; f v }) (do { v <- assume_result_and_state B; g v }) s t Q"
  apply (rule refines_bind')
  apply (simp add: refines_assume_result_and_state_iff)
  using assms
  by (force simp add: sim_set_def)

lemma refines_on_exit_left:
  assumes f_g: "refines f g s0 t Q'"
  assumes 1: "\<And>s. \<exists>s'. (s, s') \<in> cleanup "
  assumes 2: "\<And>s v t w s'. Q' (v, s) (w, t) \<Longrightarrow> (s, s') \<in> cleanup \<Longrightarrow> Q (v, s') (w, t)"
  shows "refines (on_exit f cleanup) g s0 t Q"
  unfolding on_exit_def
  apply (subst on_exit'_skip[of g, symmetric])
  apply (rule refines_on_exit'[OF f_g[THEN refines_weaken]])
  apply (auto simp: refines_yield_right_iff runs_to_iff 1 2)
  done

lemma refines_on_exit_same_cleanup:
  assumes f_g: "refines f g s0 t Q'"
  assumes 1: "\<And>s. \<exists>s'. (s, s') \<in> cleanup "
  assumes 2: "\<And>s v t w s' t'. Q' (v, s) (w, t) \<Longrightarrow> (s, s') \<in> cleanup \<Longrightarrow> (t, t') \<in> cleanup \<Longrightarrow> Q (v, s') (w, t')"
  shows "refines (on_exit f cleanup) (on_exit g cleanup) s0 t Q"
  unfolding on_exit_def
  apply (rule refines_on_exit'[OF f_g[THEN refines_weaken]])
  using 1 2
  apply clarsimp
  apply (rule refines_state_select)
   apply force
  apply force
  done

lemma refines_on_exit_same_cleanup_choice:
  assumes f_g: "refines f g s0 t Q'"
  assumes 1: "\<And>s. \<exists>s'. (s, s') \<in> cleanup "
  assumes 2: "\<And>s v t w s'. Q' (v, s) (w, t) \<Longrightarrow> (s, s') \<in> cleanup \<Longrightarrow> \<exists>t'. (t, t') \<in> cleanup \<and> Q (v, s') (w, t')"
  shows "refines (on_exit f cleanup) (on_exit g cleanup) s0 t Q"
  unfolding on_exit_def
  apply (rule refines_on_exit'[OF f_g[THEN refines_weaken]])
  using 1 2
  apply clarsimp
  apply (rule refines_state_select)
  apply auto
  done
  
lemma refines_runs_to_partial_fuse_both:
  assumes sim: "refines f f' s s' Q"
  assumes runs_to_f: "f \<bullet> s ?\<lbrace>P1\<rbrace>"
  assumes runs_to_f': "f' \<bullet> s' ?\<lbrace>P2\<rbrace>"
  shows "refines f f' s s' (\<lambda>(r,t) (r',t'). Q (r,t) (r',t') \<and> P1 r t \<and> P2 r' t')"
  using sim runs_to_f runs_to_f'
  apply (force simp add: refines_def_old runs_to_partial_def_old )
  done

definition "domain_bound A Q = (\<forall>h h'. equal_on A h h' \<longrightarrow> Q h = Q h')"

lemma domain_bound_equal_on: "domain_bound A Q \<Longrightarrow> equal_on A h h' \<Longrightarrow> Q h = Q h'"
  by (auto simp add: domain_bound_def)

lemma domain_bound_equal_on_subset: "domain_bound A Q \<Longrightarrow> A \<subseteq> A' \<Longrightarrow> equal_on A' h h' \<Longrightarrow> Q h = Q h'"
  using domain_bound_equal_on equal_on_mono by blast

lemma domain_bound_heap_update_list:
  fixes p::"'a::mem_type ptr"
  assumes "domain_bound A Q"
  assumes "length bs = size_of TYPE('a)"
  assumes "ptr_span p \<inter> A = {}"
  shows  "Q (heap_update_list (ptr_val p) bs h) = Q h"
  using assms domain_bound_equal_on 
  by (smt (verit, best) equal_on_def heap_update_nmem_same orthD2)


named_theorems domain_bound_intros

lemma domain_bound_mono: "A \<subseteq> A' \<Longrightarrow> domain_bound A Q \<Longrightarrow> domain_bound A' Q"
  by (auto simp add: domain_bound_def equal_on_mono)

lemma domain_bound_eq: "domain_bound {} (\<lambda>_. (=))"
  by (auto simp add: domain_bound_def)

lemma domain_bound_rel_sum_stack[domain_bound_intros]: "domain_bound A L \<Longrightarrow> domain_bound A R \<Longrightarrow> domain_bound A (rel_sum_stack L R)"
  by (auto simp add: domain_bound_def rel_sum_stack_def)

lemma domain_bound_rel_xval_stack[domain_bound_intros]: "domain_bound A L \<Longrightarrow> domain_bound A R \<Longrightarrow> domain_bound A (rel_xval_stack L R)"
  by (auto simp add: domain_bound_def rel_xval_stack_def)

lemma domain_bound_unreachable_exit [domain_bound_intros]: 
  "domain_bound A (rel_exit (\<lambda>_ _ _. False))"
  by (auto simp add: domain_bound_def rel_exit_def)

lemma domain_bound_bot[domain_bound_intros]: "domain_bound A (\<lambda>_ _ _. False)"
  by (auto simp add: domain_bound_def)

lemma domain_bound_eq'[domain_bound_intros]: "domain_bound A (\<lambda>_. (=))"
  using domain_bound_eq domain_bound_mono by blast

lemma domain_bound_top[domain_bound_intros]: "domain_bound A (\<lambda>_ _ _. True)"
  by (auto simp add: domain_bound_def)

lemma domain_bound_rel_singleton_stack: "domain_bound (ptr_span p) (rel_singleton_stack p)"
  using domain_rel_singleton_stack by (auto simp add: domain_bound_def)

lemma domain_bound_rel_exit[domain_bound_intros]: 
  "domain_bound A Q \<Longrightarrow> domain_bound A (rel_exit Q)"
  by (auto simp add: rel_exit_def domain_bound_def)

lemma domain_bound_rel_singleton_stack'[domain_bound_intros]: 
  "ptr_span p \<subseteq> A \<Longrightarrow> domain_bound A (rel_singleton_stack p)"
  using domain_bound_rel_singleton_stack domain_bound_mono by blast

lemma domain_rel_push: "domain_bound A Q \<Longrightarrow> equal_on (ptr_span p \<union> A) h h' \<Longrightarrow> rel_push p Q h = rel_push p Q h'" 
  apply (simp add: domain_bound_def rel_push_def fun_eq_iff) 
  by (metis Un_upper1 domain_rel_singleton_stack equal_on_mono rel_singleton_stack_def sup_commute)

lemma domain_bound_rel_push: "domain_bound A Q \<Longrightarrow> domain_bound (ptr_span p \<union> A) (rel_push p Q)"
  using domain_rel_push domain_bound_def by blast

lemma domain_bound_rel_push'[domain_bound_intros]: "ptr_span p \<subseteq> A \<Longrightarrow> domain_bound A Q \<Longrightarrow> domain_bound A (rel_push p Q)"
  using domain_bound_rel_push 
  by (metis (no_types, lifting) subset_Un_eq)



context stack_heap_state
begin


(* FIXME: make variant with arbitrary n not just Suc 0 *)
lemma with_fresh_stack_ptr_rel_stack'':
  assumes stack: "rel_alloc \<S> M A t\<^sub>0 s t"
  assumes domain_bound: "domain_bound A Q"
  assumes f: "\<And>p s' t\<^sub>0. 
    \<lbrakk>ptr_span p \<subseteq> \<S>; ptr_span p \<subseteq> stack_free (htd s); 
     ptr_span p \<inter> A = {}; ptr_span p \<inter> M = {};
     root_ptr_valid (htd s') p;
     [h_val (hmem s') p] \<in> I s;
     equal_upto_heap_on (ptr_span p) s' s;
     stack_free (htd s') \<subseteq> stack_free (htd s);
     rel_alloc \<S> (ptr_span p \<union> M) (ptr_span p \<union> A) t\<^sub>0 s' t\<rbrakk> 
    \<Longrightarrow> refines (f p) g s' t (rel_stack \<S> (ptr_span p \<union> M1) (ptr_span p \<union> A) s' t\<^sub>0 Q)"
  assumes M1_M: "M1 \<subseteq> M"
  shows "refines (with_fresh_stack_ptr (Suc 0) I f) g s t (rel_stack \<S> M1 A s t\<^sub>0 Q) "
  unfolding with_fresh_stack_ptr_def
  apply (rule refines_assume_result_and_state_left)
  apply clarsimp
  subgoal for p d vs bs
    apply (rule refines_on_exit_left)
      apply (rule f  [of _ _ "htd_upd (\<lambda>d. override_on d stack_byte_typing (ptr_span p)) t\<^sub>0"])
    subgoal 
      by (erule stack_allocs_cases) (auto)
    subgoal 
      using stack_allocs_stack_subset_stack_free by fastforce
    subgoal 
      apply (erule stack_allocs_cases)
      using stack
      by (auto simp add: rel_alloc_def stack_free_def)
    subgoal
      apply (erule stack_allocs_cases)
      using stack
      by (auto simp add: rel_alloc_def stack_free_def)
    subgoal
      apply (erule stack_allocs_cases)
      using stack
      by (auto simp add: rel_alloc_def)
    subgoal
      apply (erule stack_allocs_cases)
      using stack
      by (metis h_val_heap_update_padding heap.get_upd length_1_conv nth_Cons_0)
    subgoal 
      apply (erule stack_allocs_cases)
      apply (auto simp add: equal_upto_heap_stack_alloc)

      done
    subgoal
      by (simp add: stack_free_stack_allocs)
    subgoal
      apply (frule stack_free_stack_allocs)
      apply (erule stack_allocs_cases)
      using stack M1_M
      apply (simp add: rel_alloc_def)
      apply (simp add: frame_heap_update_padding)
      using frame_stack_alloc
      apply (subst frame_stack_alloc)
         apply (auto simp add: stack_free_def)
      done
    subgoal
      by blast
    subgoal
      apply clarsimp
      apply (clarsimp simp add: rel_stack_def)
      apply (clarsimp simp add: rel_alloc_def)
      apply (intro conjI)
      subgoal 
        apply (erule stack_allocs_cases)
        using domain_bound stack domain_bound_heap_update_list
        apply (simp add: rel_alloc_def)
        by (simp add: disjoint_subset domain_bound_heap_update_list)
      subgoal
        by (metis (no_types, lifting) Int_Un_eq(1) distrib_inf_le equal_on_stack_free_preservation 
            in_mono inf_idem rel_alloc_def stack stack_free_stack_allocs stack_free_stack_releases_mono' 
            stack_releases_stack_allocs_inverse subset_drop_Diff_strg)
      subgoal
        by (metis (no_types, lifting) Int_Un_eq(1) distinct_element distrib_inf_le 
            equal_on_stack_free_preservation inf.idem order_antisym_conv rel_alloc_def stack stack_free_stack_allocs stack_free_stack_releases_mono' stack_releases_stack_allocs_inverse subset_drop_Diff_strg)
      subgoal
        apply (erule stack_allocs_cases)
        using M1_M
        by (smt (verit, best) UnE c_guard_def disj_subset disjoint_union_distrib inter_commute
            orthD2 rel_alloc_def stack stack_free_stack_releases)

      subgoal
        apply (erule stack_allocs_cases)
        apply (subst frame_stack_release)
        subgoal by auto
        subgoal by auto (metis IntI empty_iff mem_Collect_eq rel_alloc_def stack stack_free_def)
        subgoal by auto (meson c_null_guard_def)
         apply auto
        done
      subgoal
        apply (subst stack_free_stack_releases)
        subgoal
          by (meson c_guard_def stack_allocs_cases)
        subgoal 
          apply clarsimp
          by (simp add: equal_upto_def heap_update_nmem_same heap_update_padding_def)
        done
      subgoal 
        using stack_allocs_releases_equal_on_stack
        by (smt (verit, del_insts) UnE add.right_neutral equal_upto_def mult_is_0 
            stack_releases_footprint stack_releases_other stack_releases_stack_allocs_inverse times_nat.simps(2))
      done
    done
  done

lemma gen_with_fresh_stack_ptr_rel_stack:
  assumes I': "hd ` I s \<subseteq> I'" \<comment> \<open>There are two cases of local variables: \<open>I s = (\<lambda>_. UNIV)\<close> (unitialized) and \<open>I s = (\<lambda>_. {v})\<close> (initialized) \<close>
  assumes stack: "rel_alloc \<S> M A t\<^sub>0 s t"
  assumes domain_bound: "domain_bound A Q"
  assumes f: "\<And>p s' t\<^sub>0 v. 
    \<lbrakk>ptr_span p \<subseteq> \<S>; ptr_span p \<subseteq> stack_free (htd s); 
     ptr_span p \<inter> A = {}; ptr_span p \<inter> M = {};
     root_ptr_valid (htd s') p;
     h_val (hmem s') p = v; 
     [v] \<in> I s;
     equal_upto_heap_on (ptr_span p) s' s;
     stack_free (htd s') \<subseteq> stack_free (htd s);
     rel_alloc \<S> (ptr_span p \<union> M) (ptr_span p \<union> A) t\<^sub>0 s' t\<rbrakk> 
    \<Longrightarrow> refines (f p) (g v) s' t (rel_stack \<S> (ptr_span p \<union> M1) (ptr_span p \<union> A) s' t\<^sub>0 Q)"
  assumes M1_M: "M1 \<subseteq> M"
  shows "refines (with_fresh_stack_ptr (Suc 0) I f) (select I' >>= g) s t (rel_stack \<S> M1 A s t\<^sub>0 Q) "
  unfolding with_fresh_stack_ptr_def
  apply (rule refines_assume_result_and_state_left)
  apply clarsimp
  subgoal for p d vs bs
    apply (rule refines_on_exit_left)
      apply (rule refines_select_right_witness [where x="hd vs"])
      subgoal  using I'
        by auto
      apply (rule f  [of _ _ _ "htd_upd (\<lambda>d. override_on d stack_byte_typing (ptr_span p)) t\<^sub>0"])
    subgoal 
      by (erule stack_allocs_cases) (auto)
    subgoal 
      using stack_allocs_stack_subset_stack_free by fastforce
    subgoal 
      apply (erule stack_allocs_cases)
      using stack
      by (auto simp add: rel_alloc_def stack_free_def)
    subgoal
      apply (erule stack_allocs_cases)
      using stack
      by (auto simp add: rel_alloc_def stack_free_def)
    subgoal
      apply (erule stack_allocs_cases)
      using stack
      by (auto simp add: rel_alloc_def)
    subgoal
      apply (erule stack_allocs_cases)
      apply (cases vs)
       apply (auto simp add:  h_val_heap_update_padding)
      done
    subgoal
      by (cases vs)  auto
    subgoal 
      apply (erule stack_allocs_cases)
      apply (auto simp add: equal_upto_heap_stack_alloc)
      done
    subgoal
      by (simp add: stack_free_stack_allocs)
    subgoal
      apply (frule stack_free_stack_allocs)
      apply (erule stack_allocs_cases)
      using stack M1_M
      apply (simp add: rel_alloc_def)
      apply (simp add: frame_heap_update_padding)
      using frame_stack_alloc
      apply (subst frame_stack_alloc)
         apply (auto simp add: stack_free_def)
      done
    subgoal
      by blast
    subgoal
      apply clarsimp
      apply (clarsimp simp add: rel_stack_def)
      apply (clarsimp simp add: rel_alloc_def)
      apply (intro conjI)
      subgoal 
        apply (erule stack_allocs_cases)
        using domain_bound stack domain_bound_heap_update_list
        apply (simp add: rel_alloc_def)
        by (simp add: disjoint_subset domain_bound_heap_update_list)
      subgoal
        by (metis (no_types, lifting) Int_Un_eq(1) distrib_inf_le equal_on_stack_free_preservation 
            in_mono inf_idem rel_alloc_def stack stack_free_stack_allocs stack_free_stack_releases_mono' 
            stack_releases_stack_allocs_inverse subset_drop_Diff_strg)
      subgoal
        by (metis (no_types, lifting) Int_Un_eq(1) distinct_element distrib_inf_le 
            equal_on_stack_free_preservation inf.idem order_antisym_conv rel_alloc_def stack stack_free_stack_allocs stack_free_stack_releases_mono' stack_releases_stack_allocs_inverse subset_drop_Diff_strg)
      subgoal
        apply (erule stack_allocs_cases)
        using M1_M 
        by (smt (verit, best) UnE c_guard_def disj_subset disjoint_union_distrib inter_commute
            orthD2 rel_alloc_def stack stack_free_stack_releases)

      subgoal
        apply (erule stack_allocs_cases)
        apply (subst frame_stack_release)
        subgoal by auto
        subgoal by auto (metis IntI empty_iff mem_Collect_eq rel_alloc_def stack stack_free_def)
        subgoal by auto (meson c_null_guard_def)
         apply auto
        done
      subgoal
        apply (subst stack_free_stack_releases)
        subgoal
          by (meson c_guard_def stack_allocs_cases)
        subgoal 
          apply clarsimp
          by (simp add: equal_upto_def heap_update_nmem_same heap_update_padding_def)
        done
      subgoal 
        using stack_allocs_releases_equal_on_stack
        by (smt (verit, del_insts) UnE add.right_neutral equal_upto_def mult_is_0 
            stack_releases_footprint stack_releases_other stack_releases_stack_allocs_inverse times_nat.simps(2))
      done
    done
  done

lemma with_fresh_stack_ptr_rel_stack_uninitialized':
  assumes stack: "rel_alloc \<S> M A t\<^sub>0 s t"
  assumes f: "\<And>p s' t\<^sub>0 v. 
    \<lbrakk>ptr_span p \<subseteq> \<S>; ptr_span p \<subseteq> stack_free (htd s); 
     ptr_span p \<inter> A = {}; ptr_span p \<inter> M = {};
     root_ptr_valid (htd s') p;
     h_val (hmem s') p = v; 
     equal_upto_heap_on (ptr_span p) s' s;
     stack_free (htd s') \<subseteq> stack_free (htd s);
     rel_alloc \<S> (ptr_span p \<union> M) (ptr_span p \<union> A) t\<^sub>0 s' t\<rbrakk> 
    \<Longrightarrow> refines (f p) (g v) s' t (rel_stack \<S> (ptr_span p \<union> M1) (ptr_span p \<union> A) s' t\<^sub>0 Q)"
  assumes M1_M: "M1 \<subseteq> M"
  assumes domain_bound: "domain_bound A Q"
  shows "refines (with_fresh_stack_ptr (Suc 0) (\<lambda>_. UNIV) (L2_VARS f ns)) (L2_seq (L2_unknown ns) g) s t (rel_stack \<S> M1 A s t\<^sub>0 Q)"
  unfolding L2_seq_def L2_unknown_def L2_VARS_def
  by (rule gen_with_fresh_stack_ptr_rel_stack [OF hd_UNIV stack domain_bound f M1_M])

lemma with_fresh_stack_ptr_rel_stack_uninitialized:
  assumes stack: "rel_alloc \<S> M A t\<^sub>0 s t"
  assumes f: "\<And>p s' t\<^sub>0. 
    \<lbrakk>ptr_span p \<subseteq> \<S>; ptr_span p \<subseteq> stack_free (htd s); 
     ptr_span p \<inter> A = {}; ptr_span p \<inter> M = {};
     root_ptr_valid (htd s') p;
     equal_upto_heap_on (ptr_span p) s' s; 
     stack_free (htd s') \<subseteq> stack_free (htd s);
     rel_alloc \<S> (ptr_span p \<union> M) (ptr_span p \<union> A) t\<^sub>0 s' t\<rbrakk> 
    \<Longrightarrow> refines (f p) (g' s' p) s' t (rel_stack \<S> (ptr_span p \<union> M1) (ptr_span p \<union> A) s' t\<^sub>0 Q)"
  assumes g: "\<And>s' p. ptr_span p \<inter> A = {} \<Longrightarrow> equal_upto (ptr_span p) (hmem s') (hmem s) \<Longrightarrow> g' s' p = g (h_val (hmem s') p)"
  assumes M1_M: "M1 \<subseteq> M"
  assumes domain_bound: "domain_bound A Q"
  shows "refines (with_fresh_stack_ptr (Suc 0) (\<lambda>_. UNIV) (L2_VARS f ns)) (L2_seq (L2_unknown ns) g) s t (rel_stack \<S> M1 A s t\<^sub>0 Q)"
  using with_fresh_stack_ptr_rel_stack_uninitialized' [OF stack _ M1_M domain_bound] f g
  by (smt (verit, best) equal_upto_heap_on_hmem)

lemma with_fresh_stack_ptr_rel_stack_uninitialized_g_normalised:
  assumes stack: "rel_alloc \<S> M A t\<^sub>0 s t"
  assumes f: "\<And>p s' t\<^sub>0. 
    \<lbrakk>ptr_span p \<subseteq> \<S>; ptr_span p \<subseteq> stack_free (htd s); 
     ptr_span p \<inter> A = {}; ptr_span p \<inter> M = {};
     root_ptr_valid (htd s') p;
     equal_upto_heap_on (ptr_span p) s' s; 
     stack_free (htd s') \<subseteq> stack_free (htd s);
     rel_alloc \<S> (ptr_span p \<union> M) (ptr_span p \<union> A) t\<^sub>0 s' t\<rbrakk> 
    \<Longrightarrow> refines (f p) (g (h_val (hmem s') p)) s' t (rel_stack \<S> (ptr_span p \<union> M1) (ptr_span p \<union> A) s' t\<^sub>0 Q)"
  assumes M1_M: "M1 \<subseteq> M"
  assumes domain_bound: "domain_bound A Q"
  shows "refines (with_fresh_stack_ptr (Suc 0) (\<lambda>_. UNIV) (L2_VARS f ns)) (L2_seq (L2_unknown ns) g) s t (rel_stack \<S> M1 A s t\<^sub>0 Q)"
  apply (rule with_fresh_stack_ptr_rel_stack_uninitialized [OF stack f _ M1_M domain_bound])
  apply auto
  done

lemma with_fresh_stack_ptr_rel_stack_initialized':
  fixes g::  "('d, 'e, 's) exn_monad"
  assumes stack: "rel_alloc \<S> M A t\<^sub>0 s t"
  assumes f: "\<And>p s' t\<^sub>0. 
    \<lbrakk>ptr_span p \<subseteq> \<S>; ptr_span p \<subseteq> stack_free (htd s); 
     ptr_span p \<inter> A = {}; ptr_span p \<inter> M = {};
     root_ptr_valid (htd s') p;
     h_val (hmem s') p = v; 
     equal_upto_heap_on (ptr_span p) s' s; 
     stack_free (htd s') \<subseteq> stack_free (htd s);
     rel_alloc \<S> (ptr_span p \<union> M) (ptr_span p \<union> A) t\<^sub>0 s' t\<rbrakk> 
    \<Longrightarrow> refines (f p) g s' t (rel_stack \<S> (ptr_span p \<union> M1) (ptr_span p \<union> A) s' t\<^sub>0 Q)"
  assumes M1_M: "M1 \<subseteq> M"
  assumes domain_bound: "domain_bound A Q"
  shows "refines (with_fresh_stack_ptr (Suc 0) (\<lambda>_. {[v]}) (L2_VARS f ns)) g s t (rel_stack \<S> M1 A s t\<^sub>0 Q)"
  unfolding L2_VARS_def
  apply (rule gen_with_fresh_stack_ptr_rel_stack [where I= "(\<lambda>_. {[v]})", OF hd_singleton,  simplified select_singleton_conv, OF stack domain_bound f M1_M])
         apply auto
  done

lemma with_fresh_stack_ptr_rel_stack_initialized:
  fixes g::  "('d, 'e, 's) exn_monad"
  assumes stack: "rel_alloc \<S> M A t\<^sub>0 s t"
  assumes f: "\<And>p s' t\<^sub>0. 
    \<lbrakk>ptr_span p \<subseteq> \<S>; ptr_span p \<subseteq> stack_free (htd s); 
     ptr_span p \<inter> A = {}; ptr_span p \<inter> M = {};
     root_ptr_valid (htd s') p;
     h_val (hmem s') p = v; 
     equal_upto_heap_on (ptr_span p) s' s;
     stack_free (htd s') \<subseteq> stack_free (htd s);
     rel_alloc \<S> (ptr_span p \<union> M) (ptr_span p \<union> A) t\<^sub>0 s' t\<rbrakk> 
    \<Longrightarrow> refines (f p) (g' s' p) s' t (rel_stack \<S> (ptr_span p \<union> M1) (ptr_span p \<union> A) s' t\<^sub>0 Q)"
  assumes g: "\<And>s' p. ptr_span p \<inter> A = {} \<Longrightarrow> equal_upto (ptr_span p) (hmem s') (hmem s) \<Longrightarrow> h_val (hmem s') p = v \<Longrightarrow> g' s' p = g"
  assumes M1_M: "M1 \<subseteq> M"
  assumes domain_bound: "domain_bound A Q"
  shows "refines (with_fresh_stack_ptr (Suc 0) (\<lambda>_. {[v]}) (L2_VARS f ns)) g s t (rel_stack \<S> M1 A s t\<^sub>0 Q)"
  using with_fresh_stack_ptr_rel_stack_initialized' [OF stack _ M1_M domain_bound] g
    equal_upto_heap_on_hmem f by auto

lemma with_fresh_stack_ptr_rel_stack_fix_initialized:
  fixes g::  "('d, 'e, 's) exn_monad"
  assumes stack: "rel_alloc \<S> M A t\<^sub>0 s t"
  assumes f: "\<And>p s' t\<^sub>0. 
    \<lbrakk>ptr_span p \<subseteq> \<S>; ptr_span p \<subseteq> stack_free (htd s); 
     ptr_span p \<inter> A = {}; ptr_span p \<inter> M = {};
     root_ptr_valid (htd s') p;
     h_val (hmem s') p = v; 
     equal_upto_heap_on (ptr_span p) s' s;
     stack_free (htd s') \<subseteq> stack_free (htd s);
     rel_alloc \<S> (ptr_span p \<union> M) (ptr_span p \<union> A) t\<^sub>0 s' t\<rbrakk> 
    \<Longrightarrow> refines (f p) (g' s' p) s' t (rel_stack \<S> (ptr_span p \<union> M1) (ptr_span p \<union> A) s' t\<^sub>0 Q)"
  assumes g: "\<And>s' p. ptr_span p \<inter> A = {} \<Longrightarrow> equal_upto (ptr_span p) (hmem s') (hmem s) \<Longrightarrow> h_val (hmem s') p = v \<Longrightarrow> g' s' p = g"
  assumes M1_M: "M1 \<subseteq> M"
  assumes I: "I s = {[v]}"
  assumes domain_bound: "domain_bound A Q"
  shows "refines (with_fresh_stack_ptr (Suc 0) I (L2_VARS f ns)) g s t (rel_stack \<S> M1 A s t\<^sub>0 Q)"
proof -
  from I have eq: "run (with_fresh_stack_ptr (Suc 0) (\<lambda>_. {[v]}) (L2_VARS f ns)) s = run (with_fresh_stack_ptr (Suc 0) I (L2_VARS f ns)) s"
    unfolding with_fresh_stack_ptr_def
    by (simp add: run_bind)
  from with_fresh_stack_ptr_rel_stack_initialized [OF stack f g M1_M domain_bound]
  have "refines (with_fresh_stack_ptr (Suc 0) (\<lambda>_. {[v]}) (L2_VARS f ns)) g s t (rel_stack \<S> M1 A s t\<^sub>0 Q)" .
  from refines_subst_left [OF this ] eq
  show ?thesis
    by blast
qed

lemma with_fresh_stack_ptr_rel_stack_fix_initialized_g_normalised:
  fixes g::  "('d, 'e, 's) exn_monad"
  assumes stack: "rel_alloc \<S> M A t\<^sub>0 s t"
  assumes f: "\<And>p s' t\<^sub>0. 
    \<lbrakk>ptr_span p \<subseteq> \<S>; ptr_span p \<subseteq> stack_free (htd s); 
     ptr_span p \<inter> A = {}; ptr_span p \<inter> M = {};
     root_ptr_valid (htd s') p;
     h_val (hmem s') p = v; 
     equal_upto_heap_on (ptr_span p) s' s;
     stack_free (htd s') \<subseteq> stack_free (htd s);
     rel_alloc \<S> (ptr_span p \<union> M) (ptr_span p \<union> A) t\<^sub>0 s' t\<rbrakk> 
    \<Longrightarrow> refines (f p) g s' t (rel_stack \<S> (ptr_span p \<union> M1) (ptr_span p \<union> A) s' t\<^sub>0 Q)"
  assumes M1_M: "M1 \<subseteq> M"
  assumes I: "I s = {[v]}"
  assumes domain_bound: "domain_bound A Q"
  shows "refines (with_fresh_stack_ptr (Suc 0) I (L2_VARS f ns)) g s t (rel_stack \<S> M1 A s t\<^sub>0 Q)"
  apply (rule with_fresh_stack_ptr_rel_stack_fix_initialized [OF stack f _ M1_M _ domain_bound])
  using I
            apply auto
  done

lemma with_fresh_stack_ptr_rel_stack:
  assumes stack: "rel_alloc \<S> M A t\<^sub>0 s t"
  assumes f: "\<And>p s' t\<^sub>0. 
    \<lbrakk>
     ptr_span p \<subseteq> \<S>; ptr_span p \<subseteq> stack_free (htd s); 
     ptr_span p \<inter> A = {}; ptr_span p \<inter> M = {};
     root_ptr_valid (htd s') p;
     [h_val (hmem s') p] \<in> I s;
     equal_upto_heap_on (ptr_span p) s' s; 
     stack_free (htd s') \<subseteq> stack_free (htd s);
     rel_alloc \<S> (ptr_span p \<union> M)  (ptr_span p \<union> A) t\<^sub>0 s' t\<rbrakk> 
    \<Longrightarrow> refines (f p) (g' s' p) s' t (rel_stack \<S> (ptr_span p \<union> M1)  (ptr_span p \<union> A) s' t\<^sub>0 Q)"
  assumes g: "\<And>s' p. ptr_span p \<inter> A = {} \<Longrightarrow> equal_upto (ptr_span p) (hmem s') (hmem s) \<Longrightarrow> [h_val (hmem s') p] \<in> I s \<Longrightarrow> g' s' p = g"
  assumes M1_M: "M1 \<subseteq> M"
  assumes domain_bound: "domain_bound A Q"
  shows "refines (with_fresh_stack_ptr (Suc 0) I (L2_VARS f ns)) g s t (rel_stack \<S> M1 A s t\<^sub>0 Q)"
  unfolding L2_VARS_def
  using  with_fresh_stack_ptr_rel_stack'' [OF stack domain_bound ] M1_M f g equal_upto_heap_on_hmem
  by auto

lemma refines_rel_stack_project_result:
  assumes "refines f g s t (rel_stack \<S> M A s t\<^sub>0 (rel_xval_stack L R))"
  assumes "\<And>h x y. R h x y \<Longrightarrow> R' h x (prj y)"
  shows "refines f (L2_seq g (ETA_TUPLED (\<lambda>x. L2_gets (\<lambda>_. prj x) ns))) s t (rel_stack \<S> M A s t\<^sub>0 (rel_xval_stack L R'))"
  using assms
  apply (clarsimp simp add: refines_def_old L2_defs rel_stack_def rel_xval_stack_def ETA_TUPLED_def 
          reaches_bind succeeds_bind
      split: prod.splits sum.splits)
  subgoal for r s'
  apply (cases r)
    subgoal
      apply (clarsimp simp add: default_option_def Exn_def [symmetric])
      by (smt (verit, del_insts) Exn_def Result_neq_Exn case_exception_or_result_Exn rel_xval.simps)
    subgoal
      apply clarsimp
      by (smt (verit, ccfv_SIG) Result_neq_Exn case_exception_or_result_Result rel_xval.cases rel_xval_simps(2))
    done
  done


lemma refines_rel_stack_adjust_result:
  assumes "refines f g s t (rel_stack \<S> M A s t\<^sub>0 (rel_xval_stack L R))"
  assumes "\<And>s' t' v w. R (hmem s') v w \<Longrightarrow> rel_alloc \<S> M A t\<^sub>0 s' t' \<Longrightarrow>  
     equal_upto (M \<union> stack_free (htd s')) (hmem s') (hmem s) \<Longrightarrow>
     equal_upto M (htd s') (htd s) \<Longrightarrow>
     equal_on \<S> (htd s') (htd s) \<Longrightarrow> R' (hmem s') v (adj w)"
  shows "refines f (L2_seq g (ETA_TUPLED (\<lambda>x. L2_gets (\<lambda>_. adj x) ns))) s t (rel_stack \<S> M A s t\<^sub>0 (rel_xval_stack L R'))"
  using assms
  apply (clarsimp simp add: refines_def_old L2_defs rel_stack_def rel_xval_stack_def ETA_TUPLED_def 
          reaches_bind succeeds_bind
      split: prod.splits sum.splits)
  subgoal for r s'
  apply (cases r)
    subgoal
      apply (clarsimp simp add: default_option_def Exn_def [symmetric])
      by (smt (verit, del_insts) Exn_def Result_neq_Exn case_exception_or_result_Exn rel_xval.simps)
    subgoal for v
      apply (erule_tac x="Result v" in allE)
      apply (erule_tac x="s'" in allE)
      apply (fastforce simp add: rel_xval.simps)
    done
  done
  done



lemma stack_allocs_frame:
  assumes alloc: "(p, d) \<in> stack_allocs (Suc 0) \<S> TYPE('a::mem_type) (htd s)"
  shows "\<exists>d. (p, d) \<in> stack_allocs (Suc 0) \<S> TYPE('a::mem_type) (htd (frame A t\<^sub>0 s))"
proof - 
  have "stack_free (htd s) \<subseteq> stack_free (htd (frame A t\<^sub>0 s))"
    by (rule stack_free_htd_frame)
  from stack_allocs_stack_free_mono [OF this alloc]
  show ?thesis .
qed

(* move out *)
lemma heap_list_update_nth:
  "\<And>h p. length v \<le> addr_card \<Longrightarrow>
         i < length v \<Longrightarrow>
          (heap_update_list p v h) (p + of_nat i) = v!i"
proof (induct v arbitrary: i)
  case Nil thus ?case by simp
next
  case (Cons x xs)
  thus ?case
  by (metis heap_list_nth heap_list_update)
qed


lemma stack_alloc_simulation_aux:
  fixes p::"'a::mem_type ptr"
  assumes neq_stack_byte: "typ_uinfo_t TYPE('a) \<noteq> typ_uinfo_t TYPE(stack_byte)"
  assumes disjnt: "stack_free (htd s) \<inter> A = {}"
  assumes stack_free: "\<forall>a\<in>ptr_span p. root_ptr_valid (htd s) (PTR(stack_byte) a) "
  assumes not_null: "0 \<notin> ptr_span p"
  assumes lbs: "length bs = size_of TYPE('a)"
  assumes root_ptr: "root_ptr_valid (ptr_force_type p (htd s)) p"
  shows 
  "htd_upd (\<lambda>x. override_on (ptr_force_type p (htd s)) (htd t\<^sub>0) (A - stack_free (ptr_force_type p (htd s))))
     (hmem_upd (\<lambda>x. override_on (heap_update_padding p (vs ! 0) bs x) (hmem t\<^sub>0) (A \<union> stack_free (ptr_force_type p (htd s)))) s) =
   htd_upd (\<lambda>_. ptr_force_type p (override_on (htd s) (htd t\<^sub>0) (A - stack_free (htd s))))
     (hmem_upd (\<lambda>x. heap_update_padding p (vs ! 0) bs (override_on x (hmem t\<^sub>0) (A \<union> stack_free (htd s)))) s)"
proof -
  from stack_free have stack_free': "ptr_span p \<subseteq> stack_free (htd s)" 
    by (simp add: stack_free_def subsetI)
  with root_ptr neq_stack_byte
  have sf_eq: "stack_free (ptr_force_type p (htd s)) = stack_free (htd s) - ptr_span p"
    apply (clarsimp simp add: root_ptr_valid_def stack_free_def, intro set_eqI iffI)
     apply (clarsimp, intro conjI)
      apply (smt (verit, best) ptr_force_type_d size_of_def typ_uinfo_size valid_root_footprint_domain_cases) 
     apply (metis (mono_tags, lifting) size_of_tag valid_root_footprint_type_neq)
    by (simp add: ptr_force_type_d valid_root_footprint_def)
  have heap_eq: " override_on (heap_update_padding p (vs ! 0) bs (hmem s)) (hmem t\<^sub>0) (A \<union> (stack_free (htd s) - ptr_span p))
        =
      heap_update_padding p (vs ! 0) bs (override_on (hmem s) (hmem t\<^sub>0) (A \<union> stack_free (htd s)))"
    using disjnt stack_free' lbs
    apply (clarsimp simp add: override_on_def fun_eq_iff, intro conjI impI)
    subgoal by (smt (verit) CTypes.mem_type_simps(2) disjoint_subset heap_update_nmem_same heap_update_padding_def orthD2)
    subgoal by (clarsimp simp add: heap_update_nmem_same heap_update_padding_def)
    by (auto simp add: heap_update_mem_same heap_update_padding_def)
       (smt (verit, best) CTypes.mem_type_simps(2) heap_update_nmem_same heap_update_padding_def subset_iff)

  have htd_eq: "override_on (ptr_force_type p (htd s)) (htd t\<^sub>0) (A - stack_free (ptr_force_type p (htd s)))
    =
    ptr_force_type p (override_on (htd s) (htd t\<^sub>0) (A - stack_free (htd s)))
    "
    apply (simp add: sf_eq)
    using disjnt stack_free'
    by (auto simp add: override_on_def fun_eq_iff ptr_force_type_split)
  show ?thesis
    apply (simp add: sf_eq)
    using heap_eq htd_eq
    by (metis (no_types, lifting) heap.upd_cong sf_eq typing.upd_cong)
qed

lemma keep_with_fresh_stack_ptr_rel_stack':
  assumes stack: "rel_alloc \<S> M A t\<^sub>0 s t"
  assumes I: "I (frame A t\<^sub>0 s) = I s"
  assumes f: "\<And>p s' t\<^sub>0 t. \<comment> \<open>I could use the fixed \<open>t\<^sub>0\<close>\<close>
    \<lbrakk>ptr_span p \<subseteq> \<S>; ptr_span p \<subseteq> stack_free (htd s); 
     ptr_span p \<inter> A = {}; ptr_span p \<inter> M = {};
     root_ptr_valid (htd s') p;
     [h_val (hmem s') p] \<in> I s;
     equal_upto_heap_on (ptr_span p) s' s; 
     stack_free (htd s') \<subseteq> stack_free (htd s);
     rel_alloc \<S> (ptr_span p \<union> M) A t\<^sub>0 s' t;
     ptr_span p \<inter> stack_free (htd s') = {}\<rbrakk> 
    \<Longrightarrow> refines (f p) (g p) s' t (rel_stack \<S> (ptr_span p \<union> M1) A s' t\<^sub>0 Q)"
  assumes M1_M: "M1 \<subseteq> M"
  assumes domain_bound: "domain_bound A Q"
  shows "refines (with_fresh_stack_ptr (Suc 0) I f) (with_fresh_stack_ptr (Suc 0) I g) s t (rel_stack \<S> M1 A s t\<^sub>0 Q) "
  unfolding with_fresh_stack_ptr_def
  apply (rule refines_assume_result_and_state_both_same_val_frame [where frm = "frame A t\<^sub>0"])
  subgoal using stack by (auto simp add: rel_alloc_def)
  subgoal for s' p 
    using stack I
    apply (clarsimp simp add: rel_alloc_def)
    apply (frule stack_allocs_frame [where A=A and t\<^sub>0=t\<^sub>0])
    apply clarsimp    
    apply (erule stack_allocs_cases)
    subgoal for d vs bs d'
      apply (rule exI[where x=d'])
      apply clarsimp
      apply (rule exI[where x="vs"])
      apply (simp add: I)
      apply (erule stack_allocs_cases)
      apply clarsimp
      apply (rule exI[where x="bs"])
      using stack
 
      apply (clarsimp simp add: frame_def heap_commute comp_def )
      apply (rule stack_alloc_simulation_aux)
      apply auto
      done
    done
  subgoal for s' p
    apply clarsimp
    apply (rule refines_on_exit_same_cleanup_choice)

    apply (rule f [rule_format, where t\<^sub>0="t\<^sub>0" (* t\<^sub>0="htd_upd (\<lambda>d. override_on d stack_byte_typing (ptr_span p)) t\<^sub>0" *)] )
    subgoal
      by (erule stack_allocs_cases) auto
    subgoal
      apply (erule stack_allocs_cases) 
      by (simp add: stack_free_def subset_iff)
    subgoal 
      using stack rel_alloc_def stack_allocs_stack_subset_stack_free' by fastforce
    subgoal using stack
      by (metis (no_types, lifting) add.right_neutral inf.orderE inf_assoc inf_bot_right mult_is_0 
          rel_alloc_def stack_allocs_stack_subset_stack_free times_nat.simps(2))
    subgoal 
      apply (erule stack_allocs_cases)
      by (metis htd_hmem_upd typing.get_upd)
    subgoal 
      by (metis h_val_heap_update_padding heap.get_upd length_1_conv nth_Cons_0)
    subgoal 
      by (smt (verit, best) append.simps(1) dual_order.refl fold.simps(1) fold.simps(2) 
          heap_state.equal_upto_heap_stack_alloc heap_state_axioms id_comp lense.upd_cong ptr_add_0_id 
          semiring_1_class.of_nat_0 stack_allocs_cases typing.lense_axioms upt.simps(1) upt.simps(2))
    subgoal
      by (simp add: stack_free_stack_allocs)
    subgoal using stack M1_M
      by (smt (verit) Diff_Diff_Int Diff_eq_empty_iff Int_Diff Int_Un_distrib One_nat_def Un_Int_eq(3) 
          add_mult_distrib add_right_cancel htd_hmem_upd inf.absorb_iff2 inf.orderE plus_1_eq_Suc 
          rel_alloc_def stack_allocs_stack_subset_stack_free stack_free_stack_allocs times_nat.simps(2) typing.get_upd)

    subgoal 
      apply (erule stack_allocs_cases)
      by (smt (verit, ccfv_threshold) disjoint_iff htd_hmem_upd in_ptr_span_itself mem_Collect_eq 
          root_ptr_valid_casesE stack_free_def typing.get_upd)
    subgoal by blast
    subgoal for d vs bs s1 v t w s2 
      apply clarsimp
      subgoal for bs1
        apply (rule exI[where x=" hmem_upd 
                  (heap_update_list (ptr_val p) 
                     (heap_list (hmem t\<^sub>0) (size_of TYPE('a)) (ptr_val p))) 
                  (htd_upd (stack_releases (Suc 0) p) t)"])

        apply (rule conjI)
        subgoal using heap_list_length by blast
        using stack
        apply (clarsimp simp add: rel_stack_def)
        apply (intro conjI)
        subgoal
          apply (erule stack_allocs_cases)
          using domain_bound
          by (simp add: disjoint_subset domain_bound_heap_update_list rel_alloc_def)
        subgoal
          apply (clarsimp simp add: rel_alloc_def, intro conjI)
             apply (metis (no_types, lifting) Int_Un_eq(1)  
              in_mono inf_idem stack_free_stack_allocs stack_free_stack_releases_mono' 
              stack_releases_stack_allocs_inverse subset_drop_Diff_strg sup.absorb_iff1)
            apply (metis (no_types, lifting) Int_absorb2 Int_iff Un_Int_eq(4) 
              boolean_algebra.conj_disj_distrib distrib_inf_le orthD1 
              stack_free_stack_allocs stack_free_stack_releases_mono' stack_releases_stack_allocs_inverse subset_drop_Diff_strg) 
          using M1_M 
           apply (smt (verit) c_guard_def disjoint_subset disjoint_union_distrib inter_commute orthD2 
              stack_allocs_cases stack_free_stack_releases)

          apply (erule stack_allocs_cases)
          apply (subst frame_stack_release_keep [where bs=bs1] )
          subgoal
            by (metis disjoint_union_distrib inter_commute)
          subgoal
            by (metis add.right_neutral disjoint_subset mult_Suc mult_is_0)
          subgoal
            by (meson c_guard_def)
          subgoal
            by assumption
          subgoal by simp
          done
        subgoal
          apply (subst stack_free_stack_releases)
          subgoal
            by (meson c_guard_def stack_allocs_cases)
          subgoal 
            apply clarsimp
            by (simp add: equal_upto_def heap_update_nmem_same heap_update_padding_def)
          done
        subgoal 
          using stack_allocs_releases_equal_on_stack
          by (smt (verit, del_insts) UnE add.right_neutral equal_upto_def mult_is_0 
              stack_releases_footprint stack_releases_other stack_releases_stack_allocs_inverse times_nat.simps(2))
        done
      done
    done
  done



lemma keep_with_fresh_stack_ptr_rel_stack:
  assumes stack: "rel_alloc \<S> M A t\<^sub>0 s t"
  assumes I: "I s = I (frame A t\<^sub>0 s)" \<comment> \<open>FIXME: make refinement I' similar to condition in \<open>L2_condition\<close> / \<open>L2_while\<close>?\<close>
  assumes f: "\<And>p s' t\<^sub>0 t. \<comment> \<open>I could use the fixed \<open>t\<^sub>0\<close>\<close>
    \<lbrakk>ptr_span p \<subseteq> \<S>; ptr_span p \<subseteq> stack_free (htd s); 
     ptr_span p \<inter> A = {}; ptr_span p \<inter> M = {};
     root_ptr_valid (htd s') p;
     [h_val (hmem s') p] \<in> I s;
     equal_upto_heap_on (ptr_span p) s' s; 
     stack_free (htd s') \<subseteq> stack_free (htd s);
     rel_alloc \<S> (ptr_span p \<union> M) A t\<^sub>0 s' t; 
     ptr_span p \<inter> stack_free (htd s') = {}\<rbrakk> 
    \<Longrightarrow> refines (f p) (g' s' p) s' t (rel_stack \<S> (ptr_span p \<union> M1) A s' t\<^sub>0 Q)"
  assumes g: "\<And>s' p. ptr_span p \<inter> A = {} \<Longrightarrow> equal_upto (ptr_span p) (hmem s') (hmem s) \<Longrightarrow> [h_val (hmem s') p] \<in> I s 
             \<Longrightarrow> g' s' p = g p"
  assumes M1_M: "M1 \<subseteq> M"
  assumes domain_bound: "domain_bound A Q"
  shows "refines (with_fresh_stack_ptr (Suc 0) I (L2_VARS f ns)) (with_fresh_stack_ptr (Suc 0) I (L2_VARS g ns)) s t (rel_stack \<S> M1 A s t\<^sub>0 Q)"
  unfolding L2_VARS_def
  using keep_with_fresh_stack_ptr_rel_stack' [OF stack I [symmetric] _ M1_M domain_bound] f g 
  using equal_upto_heap_on_hmem by force

lemma keep_with_fresh_stack_ptr_rel_stack_g_normalised:
  assumes stack: "rel_alloc \<S> M A t\<^sub>0 s t"
  assumes I: "I s = I (frame A t\<^sub>0 s)" \<comment> \<open>FIXME: make refinement I' similar to condition in \<open>L2_condition\<close> / \<open>L2_while\<close>?\<close>
  assumes f: "\<And>p s' t\<^sub>0 t. \<comment> \<open>I could use the fixed \<open>t\<^sub>0\<close>\<close>
    \<lbrakk>ptr_span p \<subseteq> \<S>; ptr_span p \<subseteq> stack_free (htd s); 
     ptr_span p \<inter> A = {}; ptr_span p \<inter> M = {};
     root_ptr_valid (htd s') p;
     [h_val (hmem s') p] \<in> I s;
     equal_upto_heap_on (ptr_span p) s' s; 
     stack_free (htd s') \<subseteq> stack_free (htd s);
     rel_alloc \<S> (ptr_span p \<union> M) A t\<^sub>0 s' t; 
     ptr_span p \<inter> stack_free (htd s') = {}\<rbrakk> 
    \<Longrightarrow> refines (f p) (g p) s' t (rel_stack \<S> (ptr_span p \<union> M1) A s' t\<^sub>0 Q)"
  assumes M1_M: "M1 \<subseteq> M"
  assumes domain_bound: "domain_bound A Q"
  shows "refines (with_fresh_stack_ptr (Suc 0) I (L2_VARS f ns)) (with_fresh_stack_ptr (Suc 0) I (L2_VARS g ns)) s t (rel_stack \<S> M1 A s t\<^sub>0 Q)"
  apply (rule keep_with_fresh_stack_ptr_rel_stack [OF stack I f _ M1_M domain_bound])
  apply auto
  done

lemma refines_rel_stack_adapt_right: 
  assumes stack: "rel_alloc \<S> M A t\<^sub>0 s t"
  assumes M1_M: "M1 \<subseteq> M"
  assumes f_g: "refines f g s t (rel_stack \<S> M1 A s t\<^sub>0 (rel_xval_stack L R))"
  assumes h: "\<And>s' v t' w.  
    R (hmem s') v w \<Longrightarrow>
    rel_alloc \<S> M1 A t\<^sub>0 s' t' \<Longrightarrow>
    equal_upto (M1 \<union> stack_free (htd s')) (hmem s') (hmem s) \<Longrightarrow>
    htd s' = htd s \<Longrightarrow> 
    refines (L2_gets (\<lambda>_. v) ns) (h w) s' t' (rel_stack \<S> M1 A s t\<^sub>0 (rel_xval_stack L R'))"
  shows "refines f (L2_seq g h) s t (rel_stack \<S> M1 A s t\<^sub>0 (rel_xval_stack L R'))"
  using stack M1_M f_g h
  apply (clarsimp simp add: refines_def_old L2_defs 
      rel_stack_def rel_alloc_def succeeds_bind reaches_bind )
  subgoal for r s'
    apply (cases r)
    subgoal for e
      apply (clarsimp simp add: default_option_def Exn_def [symmetric])
      subgoal for y
        apply (erule_tac x="Exn y" in allE)
        apply (erule_tac x="s'" in allE)
        by (metis (mono_tags, lifting) Exn_def case_exception_or_result_Exn rel_xval_stack_simps(5))
      done
    subgoal for v
      apply (erule_tac x="Result v" in allE)
      apply (erule_tac x="s'" in allE)
      apply (fastforce simp add: rel_xval.simps)
      done
    done
  done


lemma refines_handleE'_both_sides:
  assumes "refines f g s t Q"
  assumes "\<And>v v' s' t'. Q (Result v, s') (Result v', t') \<Longrightarrow> R (Result v, s') (Result v', t')"
  assumes "\<And>v e' s' t'. Q (Result v, s') (Exn e', t') \<Longrightarrow> refines (return v) (h' e') s' t' R"
  assumes "\<And>e v' s' t'. Q (Exn e, s') (Result v', t') \<Longrightarrow> refines (h e) (return v') s' t' R"
  assumes "\<And>e e' s' t'. Q (Exn e, s') (Exn e', t') \<Longrightarrow> refines (h e) (h' e') s' t' R"
  shows "refines (f <catch> h) (g <catch> h') s t R"
  by (rule Spec_Monad.refines_catch [OF assms(1) assms(5) assms(4) assms(3) assms(2)])


lemma refines_rel_stack_map_exn:
  assumes f_g: "refines f g s t (rel_stack  \<S> M A s t\<^sub>0 (rel_xval_stack L R))"
  assumes L: "\<And>e e' s'. L (hmem s') e e' \<Longrightarrow> L' (hmem s') (emb e) (emb e')"
  shows "refines (map_value (map_exn emb) f) (map_value (map_exn emb) g) s t (rel_stack  \<S> M A s t\<^sub>0 (rel_xval_stack L' R))"
  using assms
  apply (clarsimp simp add: refines_def_old L2_defs 
      rel_stack_def rel_alloc_def reaches_map_value)
  subgoal for s' r
    apply (cases r)
    subgoal for e
      apply (clarsimp simp add: default_option_def Exn_def [symmetric])
      subgoal for y
        apply (erule_tac x="Exn y" in allE)
        apply (erule_tac x="s'" in allE)
        by auto
      done
    subgoal for v
      apply (erule_tac x="Result v" in allE)
      apply (erule_tac x="s'" in allE)
      apply (auto)
      done
    done
  done


lemma refines_rel_stack_map_exn_exit:
  assumes f_g: "refines f g s t (rel_stack  \<S> M A s t\<^sub>0 (rel_xval_stack (rel_exit L) R))"
  assumes L: "\<And>e e' h. L h e e' \<Longrightarrow> L' h (emb e) (emb' e')"
  shows "refines (map_value (map_exn (emb o the_Nonlocal)) f) (map_value (map_exn (emb')) g) s t (rel_stack  \<S> M A s t\<^sub>0 (rel_xval_stack L' R))"
  using assms
  apply (clarsimp simp add: refines_def_old L2_defs
      rel_stack_def rel_alloc_def reaches_map_value )
  subgoal for s' r
    apply (cases r)
    subgoal for e
      apply (clarsimp simp add: default_option_def Exn_def [symmetric])
      subgoal for y
        apply (erule_tac x="Exn y" in allE)
        apply (erule_tac x="s'" in allE)
        apply (auto simp add: rel_exit_def)
        done
      done
    subgoal for v
      apply (erule_tac x="Result v" in allE)
      apply (erule_tac x="s'" in allE)
      apply (auto)
      done
    done
  done


lemma throw_L2_throw_conv: "throw x = L2_throw x []"
  by (simp add: L2_throw_def)

lemma L2_catch_join_exn_conv: 
   "(L2_catch 
          (L2_seq 
            (L2_catch g (\<lambda>x. L2_seq (liftE (h x)) (\<lambda>_. L2_throw (prj x) ns1))) 
            (\<lambda>s. liftE (g1 s))) 
          (\<lambda>r. L2_throw (emb r) ns2)) =
       (L2_seq 
         (L2_catch g (\<lambda>x. L2_seq (liftE (h x)) (\<lambda>_. L2_throw (emb (prj x)) ns2))) 
         (\<lambda>s. liftE (g1 s)))"
  unfolding L2_defs
  
  apply (rule spec_monad_eqI)
  apply (clarsimp simp add: runs_to_iff)
  apply (auto simp add: runs_to_def_old default_option_def Exn_def)
  done

lemma L2_call_rel_stack_embed_exit:
  assumes L: "\<And>e e' h. L h e e' \<Longrightarrow> L' h (emb e) (emb' e')"
  assumes f_g: "refines
    f 
    (L2_seq 
      (L2_catch g (\<lambda>x. (L2_seq (liftE (h x)) (\<lambda>_. L2_throw (prj x) ns')))) 
      (\<lambda>s. liftE (g1 s)))
    s t 
    (rel_stack \<S> M1 A s t\<^sub>0 (rel_xval_stack (rel_exit L) R))"

  shows "refines 
    (L2_call f (emb o the_Nonlocal) ns)
    (L2_seq 
      (L2_catch g (\<lambda>x. (L2_seq (liftE (h x)) (\<lambda>_. L2_throw (emb' (prj x)) ns')))) 
      (\<lambda>s. liftE (g1 s))) 
    s t 
    (rel_stack \<S> M1 A s t\<^sub>0 (rel_xval_stack L' R))"
proof -
  from refines_rel_stack_map_exn_exit [where L' = L', OF f_g L ]
  have "refines 
         (map_value (map_exn (emb o the_Nonlocal)) f) 
         (map_value (map_exn (emb'))  
             (L2_seq 
                (L2_catch g (\<lambda>x. L2_seq (liftE (h x)) (\<lambda>_. L2_throw (prj x) ns'))) 
                (\<lambda>s. liftE (g1 s)))) 
         s t (rel_stack \<S> M1 A s t\<^sub>0 (rel_xval_stack L' R))" .
  then show ?thesis
    apply (simp add: map_exn_catch_conv L2_catch_def [symmetric] throw_L2_throw_conv)
    apply (simp add:  L2_catch_join_exn_conv)
    apply (simp add: L2_call_def map_exn_catch_conv L2_catch_def [symmetric] L2_throw_def)
    done
qed

lemma L2_call_rel_stack_nest_exit_guarded:
  assumes f_g: "P t \<Longrightarrow> refines
    f 
    (L2_seq (L2_guard P) (\<lambda>_. 
      (L2_seq 
        (L2_catch g (\<lambda>x. (L2_seq (liftE (h x)) (\<lambda>_. L2_throw (prj x) ns')))) 
        (\<lambda>s. liftE (g1 s)))))
    s t 
    (rel_stack \<S> M1 A s t\<^sub>0 (rel_xval_stack (rel_exit L) R))"
  assumes L: "\<And>e e' h. P t \<Longrightarrow> L h e e' \<Longrightarrow> L' h (emb e) (emb' e')"
  shows "refines 
    (L2_call f (emb o the_Nonlocal) ns)
    (L2_seq (L2_guard P) (\<lambda>_. 
      (L2_seq 
        (L2_catch g (\<lambda>x. (L2_seq (liftE (h x)) (\<lambda>_. L2_throw (emb' (prj x)) ns')))) 
        (\<lambda>s. liftE (g1 s))))) 
    s t 
    (rel_stack \<S> M1 A s t\<^sub>0 (rel_xval_stack L' R))"
  apply (rule refines_L2_guard_right')
  apply (rule L2_call_rel_stack_embed_exit [where L=L and emb=emb and emb'= emb'])
   apply (rule L, assumption+)
  using f_g refines_L2_guard_rightE by fastforce



lemma bind_catch_liftE_assoc: 
  "(do {v \<leftarrow> (g <catch> (\<lambda>x. do {
                                      y \<leftarrow> liftE (h x);
                                      throw (exn x y)
                                    }));
           liftE (g1 v)
       }) = 
       (do {v \<leftarrow> g; liftE (g1 v)} <catch> (\<lambda>x. do {
                                      y \<leftarrow> liftE (h x);
                                      throw (exn x y)
                                    }))"
  apply (rule spec_monad_eqI)
  apply (auto simp add: runs_to_iff Exn_def[symmetric] elim!: runs_to_weaken)
  done


lemma bind_catch_liftE_split_catch: "(do {
                 s \<leftarrow> g;
                 liftE (g1 s)
               } <catch> (\<lambda>x. do {
                               _ \<leftarrow> liftE (h x);
                               throw (emb (prj x))
                             })) = 
((do {
                 s \<leftarrow> g;
                 liftE (g1 s)
               } <catch> (\<lambda>x. do {
                               _ \<leftarrow> liftE (h x);
                               throw (prj x) }))
                <catch> (\<lambda>x. throw (emb x)))"
  apply (rule spec_monad_eqI)
  apply (auto simp add: runs_to_iff Exn_def[symmetric] elim!: runs_to_weaken)
  done

lemma refines_catch_right_trans:
  fixes f:: "('e, 'a, 's) exn_monad"
  assumes f_g: "refines f g s t Q"
  assumes R: "\<And> r s' e t'. Q (r, s') (Exn e, t') \<Longrightarrow> refines (yield r) (h e) s' t' R"
  assumes Exn_Res: "\<And>e s' v' t'. Q (Exn e, s') (Result v', t') \<Longrightarrow> R (Exn e, s') (Result v', t')"
  assumes Res_Res: "\<And>v v' s' t'. Q (Result v, s') (Result v', t') \<Longrightarrow> R (Result v, s') (Result v', t')"
  shows "refines f (g <catch> h) s t R"
  apply (subst f_catch_throw[symmetric, of f])
  apply (rule refines_catch [OF f_g])
  subgoal premises prems using R [OF prems(1)] by simp
  subgoal using Exn_Res by (auto simp add: refines_yield_right_iff)
  subgoal premises prems using R [OF prems(1)] by simp
  subgoal using Res_Res by (auto simp add: refines_yield_right_iff)
  done

lemma L2_call_rel_stack_embellish_exit:
  assumes s_t: "rel_alloc \<S> M A t\<^sub>0 s t"
  assumes f_g: "P t \<Longrightarrow> refines
    f 
    (L2_seq (L2_guard P) (\<lambda>_. 
      (L2_seq 
        (L2_catch g (\<lambda>x. (L2_seq (liftE (h x)) (\<lambda>_. L2_throw (prj x) ns)))) 
        (\<lambda>s. liftE (g1 s)))))
    s t 
    (rel_stack \<S> M1 A s t\<^sub>0 (rel_xval_stack (rel_exit L) R))"
  assumes L: "\<And>s' t' e e'. L (hmem s') e e' \<Longrightarrow> P t \<Longrightarrow> rel_alloc \<S> M A t\<^sub>0 s' t' \<Longrightarrow>
            equal_upto (M1 \<union> stack_free (htd s')) (hmem s') (hmem s) \<Longrightarrow> htd s' = htd s \<Longrightarrow> 
            L' (hmem s') e (emb e')"
  assumes M1: "P t \<Longrightarrow> M1 \<subseteq> M"
  shows "refines 
    f
    (L2_seq (L2_guard P) (\<lambda>_. 
      (L2_seq 
        (L2_catch g (\<lambda>x. (L2_seq (liftE (h x)) (\<lambda>_. L2_throw (emb (prj x)) ns_exit)))) 
        (\<lambda>s. liftE (g1 s))))) 
    s t 
    (rel_stack \<S> M1 A s t\<^sub>0 (rel_xval_stack (rel_exit L') R))"
  unfolding L2_defs
  apply (clarsimp simp add: refines_bind_guard_right_iff bind_catch_liftE_assoc)
  apply (simp add: bind_catch_liftE_split_catch)
  apply (rule refines_catch_right_trans)
     apply (rule f_g [simplified L2_defs refines_bind_guard_right_iff bind_catch_liftE_assoc, rule_format])
      apply assumption
     apply simp
  subgoal
    apply (clarsimp simp add: rel_stack_def rel_exit_def)
    using L s_t by (auto simp add: rel_alloc_def)
  subgoal
    by (auto simp add: rel_stack_def)
  subgoal
    by (auto simp add: rel_stack_def)
  done

definition "override_heap_on P t1 t2 \<equiv> 
  hmem_upd (\<lambda>h. override_on h (hmem t2) P) 
    (htd_upd (\<lambda>d. override_on d (htd t2) P) t1)"

lemma override_heap_on_empty [simp]: "override_heap_on {} t1 t2 = t1"
  by (simp add: override_heap_on_def)

lemma refines_rel_stack_override_heap_on_exit:
  fixes p:: "'a::xmem_type ptr"
  assumes stack: "rel_alloc \<S> M A t\<^sub>0 s t"
  assumes f_g: "\<And>s t t\<^sub>0. rel_alloc \<S> M (P \<union> A) t\<^sub>0 s t \<Longrightarrow> 
    refines f (g s) s t (rel_stack \<S> M1 (P \<union> A) s t\<^sub>0 Q)"
  assumes disj_A: "P \<inter> A = {}"
  assumes p_M1: "P \<subseteq> M1"
  assumes M1_M: "M1 \<subseteq> M"
  assumes disj_stack_free_s: "P \<inter> stack_free (htd s) = {}"
  shows "refines f (g s) s t 
    (rel_stack \<S> M1 (P \<union> A) s (override_heap_on P t\<^sub>0 t) Q)"
proof -
  from stack have sf_s_t: "stack_free (htd s) \<subseteq> stack_free (htd t)"
    using rel_alloc_def stack_free_htd_frame by auto

  from stack have t: "t = frame A t\<^sub>0 s"
    by (auto simp add: rel_alloc_def)

  define t0' where "t0' = override_heap_on P t\<^sub>0 t"

  have eq_htd: 
    "override_on (htd s) (htd t\<^sub>0) (A - stack_free (htd s)) =
        override_on (htd s) (htd t0') ((P \<union> A) - stack_free (htd s))"
    using disj_stack_free_s disj_A t
    by (auto simp add: t0'_def override_heap_on_def override_on_def fun_eq_iff frame_def)

  have eq_hmem:
    "override_on (hmem s) (hmem t\<^sub>0) (A \<union> stack_free (htd s)) =
        override_on (hmem s) (hmem t0') ((P \<union> A) \<union> stack_free (htd s))"
    using disj_stack_free_s disj_A t
    by (auto simp add: t0'_def override_heap_on_def override_on_def fun_eq_iff frame_def)

  from t have t_t0': "t = frame ((P \<union> A)) t0' s"
    using eq_htd eq_hmem
    apply (simp add: frame_def)
    by (metis (no_types, lifting) heap.upd_cong hmem_htd_upd typing.upd_cong)

  have stack': "rel_alloc \<S> M ((P \<union> A)) t0' s t"
    using stack disj_stack_free_s disj_stack_free_s t t_t0'
    by (auto simp add: rel_alloc_def)

  from disj_stack_free_s disj_stack_free_s stack
  have stack_free': "stack_free (htd s) \<inter> (P \<union> A) = {}"
    by (auto simp add: rel_alloc_def)

  from f_g [OF stack'] 
  have f_g': "refines f (g s) s t
          (rel_stack \<S> M1 ((P \<union> A)) s t0' Q)" .
  then show ?thesis
    by (simp add: t0'_def)
qed

lemma refines_rel_stack_override_heap_on_exit_guarded:
  fixes p:: "'a::xmem_type ptr"
  assumes stack: "rel_alloc \<S> M A t\<^sub>0 s t"
  assumes f_g: "\<And>s t t\<^sub>0. G \<Longrightarrow> rel_alloc \<S> M (P \<union> A) t\<^sub>0 s t \<Longrightarrow> 
    refines f (L2_seq (L2_guard (\<lambda>_. G)) (\<lambda>_. g s)) s t (rel_stack \<S> M1 (P \<union> A) s t\<^sub>0 Q)"
  assumes disj_A: "G \<Longrightarrow> P \<inter> A = {}"
  assumes p_M1: "G \<Longrightarrow> P \<subseteq> M1"
  assumes M1_M: "G \<Longrightarrow> M1 \<subseteq> M"
  assumes disj_stack_free_s: "G \<Longrightarrow> P \<inter> stack_free (htd s) = {}"
  shows "refines f (L2_seq (L2_guard (\<lambda>_. G)) (\<lambda>_. g s)) s t 
    (rel_stack \<S> M1 (P \<union> A) s (override_heap_on P t\<^sub>0 t) Q)"
proof -
  {assume guard: "G" 
    have "refines f (L2_seq (L2_guard (\<lambda>_. G)) (\<lambda>_. g s)) s t (rel_stack \<S> M1 (P \<union> A) s (override_heap_on P t\<^sub>0 t) Q)"
      using refines_rel_stack_override_heap_on_exit [OF stack f_g [OF guard] disj_A [OF guard] p_M1 [OF guard] 
          M1_M [OF guard] disj_stack_free_s [OF guard]].}
  then show ?thesis
    by (rule refines_L2_guard_right'')
qed



lemma refines_rel_stack_override_heap_emptyI:
  assumes "refines f g s t (rel_stack \<S> M (P \<union> A) s (override_heap_on P t\<^sub>0 t) Q)"
  shows "refines f g s t (rel_stack \<S> M (P \<union> {} \<union> A) s (override_heap_on (P \<union> {}) t\<^sub>0 t) Q)"
  using assms
  by simp

lemma refines_rel_stack_pop_heap_both:
  fixes p:: "'a::xmem_type ptr"
  assumes stack: "rel_alloc \<S> M A t\<^sub>0 s t"
  assumes f_g: "refines f g s t 
             (rel_stack \<S> M1 (ptr_span p \<union> P \<union> A) s 
               (override_heap_on (ptr_span p \<union> P) t\<^sub>0 t) 
               (rel_xval_stack (rel_exit (rel_push p L)) (rel_push p R)))"
  assumes disj_P_A: "P \<inter> A = {}"
  assumes disj_p_A: "ptr_span p \<inter> A = {}"
  assumes disj_p_P: "ptr_span p \<inter> P = {}" 
  assumes disj_stack_free_s_p: "ptr_span p \<inter> stack_free (htd s) = {}"
  assumes disj_stack_free_s_P: "P \<inter> stack_free (htd s) = {}"
  shows "refines 
    f 
    (L2_seq 
      (L2_catch g (\<lambda>x. (L2_seq (IO_modify_heap_paddingE p (\<lambda>_. (fst x))) (\<lambda>_. L2_throw (snd x) ns_exit)))) 
      (\<lambda>x. (L2_seq (IO_modify_heap_paddingE p (\<lambda>_. (fst x))) (\<lambda>_. L2_return (snd x) ns)))) s t 
    (rel_stack \<S> M1 (P \<union> A) s (override_heap_on P t\<^sub>0 t) (rel_xval_stack (rel_exit L) R))"
proof -
  from stack have sf_s_t: "stack_free (htd s) \<subseteq> stack_free (htd t)"
    using rel_alloc_def stack_free_htd_frame by auto

  from stack have t: "t = frame A t\<^sub>0 s"
    by (auto simp add: rel_alloc_def)

  define t0' where "t0' = override_heap_on (ptr_span p \<union> P) t\<^sub>0 t"

  have eq_htd: 
    "override_on (htd s) (htd t\<^sub>0) (A - stack_free (htd s)) =
        override_on (htd s) (htd t0') ((ptr_span p \<union> P \<union> A) - stack_free (htd s))"
    using disj_stack_free_s_p disj_stack_free_s_P disj_P_A disj_p_A t
    by (auto simp add: t0'_def override_heap_on_def override_on_def fun_eq_iff frame_def)

  have eq_hmem:
    "override_on (hmem s) (hmem t\<^sub>0) (A \<union> stack_free (htd s)) =
        override_on (hmem s) (hmem t0') ((ptr_span p \<union> P \<union> A) \<union> stack_free (htd s))"
    using disj_stack_free_s_p disj_stack_free_s_P disj_p_A disj_P_A t
    by (auto simp add: t0'_def override_heap_on_def override_on_def fun_eq_iff frame_def)

  from t have t_t0': "t = frame ((ptr_span p \<union> P \<union> A)) t0' s"
    using eq_htd eq_hmem
    apply (simp add: frame_def)
    by (metis (no_types, lifting) heap.upd_cong hmem_htd_upd typing.upd_cong)

  have stack': "rel_alloc \<S> M ((ptr_span p \<union> P \<union> A)) t0' s t"
    using stack disj_stack_free_s_P  disj_stack_free_s_p t t_t0'
    by (auto simp add: rel_alloc_def)

  from disj_stack_free_s_p disj_stack_free_s_P disj_stack_free_s_P stack
  have stack_free': "stack_free (htd s) \<inter> (P \<union> A) = {}"
    by (auto simp add: rel_alloc_def)


  show ?thesis
    unfolding L2_seq_def
    apply (rule refines_bindE_right [where Q = "\<lambda>(v, s') (w, t'). 
        case v of 
          Exn e \<Rightarrow> \<exists>w'. w = Exn w' \<and> rel_stack \<S> M1 (P \<union> A) s (override_heap_on P t\<^sub>0 t) (rel_xval_stack (rel_exit L) (\<lambda>_ _ _. False)) (Exn e, s') (Exn w', t')
        | Result v \<Rightarrow> \<exists>w'. w = Result w' \<and> rel_stack \<S> M1 (ptr_span p \<union> P \<union> A) s (override_heap_on (ptr_span p \<union> P) t\<^sub>0 t) (rel_xval_stack (\<lambda>_ _ _. False) (rel_push p R)) (Result v, s') (Result w', t')"] )
        apply (rule refines_L2_catch_right)
            apply (rule f_g)
    subgoal by (clarsimp simp add: rel_stack_def t0'_def rel_alloc_def)
    subgoal by clarsimp
    subgoal by clarsimp
    subgoal for e e' s' t' 
      apply (frule rel_stack_unchanged_stack_free [OF stack', unfolded t0'_def])
      apply (frule rel_stack_unchanged_stack_free' [OF stack', unfolded t0'_def])
      apply (subst (asm) rel_stack_def)
      apply (clarsimp simp add: rel_exit_def) 
      apply (subst (asm) rel_push_def) 
      apply clarsimp
      apply (rule refines_exec_IO_modify_heap_padding_single_step_right_InL)
      using stack  
      apply (clarsimp simp add: stack_free' rel_alloc_def rel_stack_def t0'_def [symmetric] t [symmetric] t_t0' [symmetric])
      subgoal premises prems for w x
      proof -
        from prems obtain
          "e = Nonlocal x"
          "e' = (h_val (hmem s') p, w)"
          "L (hmem s') x w" and
          sf_s': "stack_free (htd s') = stack_free (htd s)" and
          sf_t': "stack_free (htd (frame (ptr_span p \<union> P \<union> A) t0' s')) = stack_free (htd t)" and
          "stack_free (htd s) \<subseteq> \<S>"
          "stack_free (htd s) \<inter> (ptr_span p \<union> P \<union> A) = {}"
          "stack_free (htd s) \<inter> M1 = {}"
          "t' = frame (ptr_span p \<union> P \<union> A) t0' s'"
          "equal_upto (M1 \<union> stack_free (htd s)) (hmem s') (hmem s)" and
          htd_eq: "htd s' = htd s"  by (simp)
        have eq_typing: 
          "override_on (htd s') (htd t0') (ptr_span p \<union> P \<union> A - stack_free (htd s')) =
                  override_on (htd s') (htd (override_heap_on P t\<^sub>0 t)) (P \<union> A - stack_free (htd s'))"
          using disj_P_A disj_p_A 
          by (auto simp add: override_on_def fun_eq_iff t0'_def htd_eq t htd_frame override_heap_on_def)


        have eq_heap: "heap_update_padding p (h_val (hmem s') p)
                    (heap_list (hmem s') (size_of TYPE('a)) (ptr_val p))
                    (override_on (hmem s') (hmem t0') (ptr_span p \<union> P \<union> A \<union> stack_free (htd s'))) = 
                  override_on (hmem s') (hmem (override_heap_on P t\<^sub>0 t)) (P \<union> A \<union> stack_free (htd s'))"
          using disj_P_A disj_p_A
          apply (simp add: override_on_def override_heap_on_def fun_eq_iff t0'_def)
          by (smt (verit, best) disj_p_P disj_stack_free_s_p h_val_def heap_list_length 
              heap_update_list_id' heap_update_list_value heap_update_padding_def 
              hmem_htd_upd max_size orthD2 sf_s' to_bytes_heap_list_id)

        show "hmem_upd
               (heap_update_padding p (h_val (hmem s') p)
                 (heap_list (hmem s') (size_of TYPE('a)) (ptr_val p)))
               (frame (ptr_span p \<union> P \<union> A) t0' s') =
              frame (P \<union> A) (override_heap_on P t\<^sub>0 t) s'"
          apply (simp add: frame_def comp_def)
          using eq_typing eq_heap
          by (metis (no_types, lifting) heap.upd_cong hmem_htd_upd typing.upd_cong)
      qed
      done
    subgoal by clarsimp
    subgoal by clarsimp
    subgoal by clarsimp
    subgoal for v v' s' t'
      apply (clarsimp)
      apply (frule rel_stack_unchanged_stack_free [OF stack', unfolded t0'_def])
      apply (frule rel_stack_unchanged_stack_free' [OF stack', unfolded t0'_def])
      apply (subst (asm) rel_stack_def)
      apply (clarsimp simp add: rel_exit_def) 
      apply (subst (asm) rel_push_def) 
      apply clarsimp
      apply (rule refines_exec_IO_modify_heap_padding_step_right)
      apply (rule refines_exec_L2_return_right)
      using stack  
      apply (clarsimp simp add: stack_free' rel_alloc_def rel_stack_def t0'_def [symmetric] t [symmetric] t_t0' [symmetric])
      subgoal premises prems for w
      proof -
        from prems obtain
          "v' = (h_val (hmem s') p, w)"
          "R (hmem s') v w" and
          sf_s': "stack_free (htd s') = stack_free (htd s)" and
          sf_t': "stack_free (htd (frame (ptr_span p \<union> P \<union> A) t0' s')) = stack_free (htd t)" and
          "stack_free (htd s) \<subseteq> \<S>"
          "stack_free (htd s) \<inter> (ptr_span p \<union> P \<union> A) = {}"
          "stack_free (htd s) \<inter> M1 = {}"
          "t' = frame (ptr_span p \<union> P \<union> A) t0' s'"
          "equal_upto (M1 \<union> stack_free (htd s)) (hmem s') (hmem s)" and
          htd_eq: "htd s' = htd s" by simp
        have eq_typing: 
          "override_on (htd s') (htd t0') (ptr_span p \<union> P \<union> A - stack_free (htd s')) =
                  override_on (htd s') (htd (override_heap_on P t\<^sub>0 t)) (P \<union> A - stack_free (htd s'))"
          using disj_P_A disj_p_A 
          by (auto simp add: override_on_def fun_eq_iff t0'_def htd_eq t htd_frame override_heap_on_def)


        have eq_heap: "heap_update_padding p (h_val (hmem s') p)
                    (heap_list (hmem s') (size_of TYPE('a)) (ptr_val p))
                    (override_on (hmem s') (hmem t0') (ptr_span p \<union> P \<union> A \<union> stack_free (htd s'))) = 
                  override_on (hmem s') (hmem (override_heap_on P t\<^sub>0 t)) (P \<union> A \<union> stack_free (htd s'))"
          using disj_P_A disj_p_A
          apply (simp add: override_on_def override_heap_on_def fun_eq_iff t0'_def)
          by (smt (verit, best) disj_p_P disj_stack_free_s_p h_val_def heap_list_length 
              heap_update_list_id' heap_update_list_value heap_update_padding_def 
              hmem_htd_upd max_size orthD2 sf_s' to_bytes_heap_list_id)

        show "hmem_upd
               (heap_update_padding p (h_val (hmem s') p)
                 (heap_list (hmem s') (size_of TYPE('a)) (ptr_val p)))
               (frame (ptr_span p \<union> P \<union> A) t0' s') =
              frame (P \<union> A) (override_heap_on P t\<^sub>0 t) s'"
          apply (simp add: frame_def comp_def)
          using eq_typing eq_heap
          by (metis (no_types, lifting) heap.upd_cong hmem_htd_upd typing.upd_cong)
      qed
      done
    done
qed

lemma refines_rel_stack_pop_heap_both_guarded:
  fixes p:: "'a::xmem_type ptr"
  assumes stack: "rel_alloc \<S> M A t\<^sub>0 s t"
  assumes f_g: "refines f (L2_seq (L2_guard (\<lambda>_. G)) (\<lambda>_. g)) s t 
             (rel_stack \<S> M1 (ptr_span p \<union> P \<union> A) s 
               (override_heap_on (ptr_span p \<union> P) t\<^sub>0 t) 
               (rel_xval_stack (rel_exit (rel_push p L)) (rel_push p R)))"
  assumes disj_P_A: "G \<Longrightarrow> P \<inter> A = {}"
  assumes disj_p_A: "G \<Longrightarrow> ptr_span p \<inter> A = {}"
  assumes disj_p_P: "G \<Longrightarrow> ptr_span p \<inter> P = {}" 
  assumes disj_stack_free_s_p: "G \<Longrightarrow> ptr_span p \<inter> stack_free (htd s) = {}"
  assumes disj_stack_free_s_P: "G \<Longrightarrow> P \<inter> stack_free (htd s) = {}"
  shows "refines
    f
    (L2_seq 
      (L2_catch (L2_seq (L2_guard (\<lambda>_. G)) (\<lambda>_. g))
         (\<lambda>x. (L2_seq (IO_modify_heap_paddingE p (\<lambda>_. (fst x))) (\<lambda>_. L2_throw (snd x) ns_exit))))
      (\<lambda>x. (L2_seq (IO_modify_heap_paddingE p (\<lambda>_. (fst x))) (\<lambda>_. L2_return (snd x) ns)))) s t
    (rel_stack \<S> M1 (P \<union> A) s (override_heap_on P t\<^sub>0 t) (rel_xval_stack (rel_exit L) R))"
proof -
  {
    assume grd: "G"
    have ?thesis
      by (rule refines_rel_stack_pop_heap_both [OF stack f_g disj_P_A [OF grd] disj_p_A [OF grd] disj_p_P [OF grd]
            disj_stack_free_s_p [OF grd] disj_stack_free_s_P [OF grd]])
  } then show ?thesis
    by (rule refines_L2_guard_right'''')
qed

lemma refines_rel_stack_pop_heap_both_singleton:
  fixes p:: "'a::xmem_type ptr"
  assumes stack: "rel_alloc \<S> M A t\<^sub>0 s t"
  assumes f_g: "refines f g s t 
             (rel_stack \<S> M1 (ptr_span p \<union> P \<union> A) s 
               (override_heap_on (ptr_span p \<union> P) t\<^sub>0 t) 
               (rel_xval_stack (rel_exit (rel_push p L)) (rel_singleton_stack p)))"
  assumes disj_P_A: "P \<inter> A = {}"
  assumes disj_p_A: "ptr_span p \<inter> A = {}"
  assumes disj_p_P: "ptr_span p \<inter> P = {}" 
  assumes disj_stack_free_s_p: "ptr_span p \<inter> stack_free (htd s) = {}"
  assumes disj_stack_free_s_P: "P \<inter> stack_free (htd s) = {}"
  shows "refines 
    f 
    (L2_seq 
      (L2_catch g (\<lambda>x. (L2_seq (IO_modify_heap_paddingE p (\<lambda>_. (fst x))) (\<lambda>_. L2_throw (snd x) ns_exit)))) 
      (\<lambda>x. (IO_modify_heap_paddingE p (\<lambda>_. x)))) s t 
    (rel_stack \<S> M1 (P \<union> A) s (override_heap_on P t\<^sub>0 t) (rel_xval_stack (rel_exit L) (\<lambda>_. (=))))"
proof -
  from stack have sf_s_t: "stack_free (htd s) \<subseteq> stack_free (htd t)"
    using rel_alloc_def stack_free_htd_frame by auto

  from stack have t: "t = frame A t\<^sub>0 s"
    by (auto simp add: rel_alloc_def)

  define t0' where "t0' = override_heap_on (ptr_span p \<union> P) t\<^sub>0 t"

  have eq_htd: 
    "override_on (htd s) (htd t\<^sub>0) (A - stack_free (htd s)) =
        override_on (htd s) (htd t0') ((ptr_span p \<union> P \<union> A) - stack_free (htd s))"
    using disj_stack_free_s_p disj_stack_free_s_P disj_P_A disj_p_A t
    by (auto simp add: t0'_def override_heap_on_def override_on_def fun_eq_iff frame_def)

  have eq_hmem:
    "override_on (hmem s) (hmem t\<^sub>0) (A \<union> stack_free (htd s)) =
        override_on (hmem s) (hmem t0') ((ptr_span p \<union> P \<union> A) \<union> stack_free (htd s))"
    using disj_stack_free_s_p disj_stack_free_s_P disj_p_A disj_P_A t
    by (auto simp add: t0'_def override_heap_on_def override_on_def fun_eq_iff frame_def)

  from t have t_t0': "t = frame ((ptr_span p \<union> P \<union> A)) t0' s"
    using eq_htd eq_hmem
    apply (simp add: frame_def)
    by (metis (no_types, lifting) heap.upd_cong hmem_htd_upd typing.upd_cong)

  have stack': "rel_alloc \<S> M ((ptr_span p \<union> P \<union> A)) t0' s t"
    using stack disj_stack_free_s_P  disj_stack_free_s_p t t_t0'
    by (auto simp add: rel_alloc_def)

  from disj_stack_free_s_p disj_stack_free_s_P disj_stack_free_s_P stack
  have stack_free': "stack_free (htd s) \<inter> (P \<union> A) = {}"
    by (auto simp add: rel_alloc_def)


  show ?thesis
    unfolding L2_seq_def
    apply (rule refines_bindE_right [where Q = "\<lambda>(v, s') (w, t'). 
        case v of 
          Exn e \<Rightarrow> \<exists>w'. w = Exn w' \<and> rel_stack \<S> M1 (P \<union> A) s (override_heap_on P t\<^sub>0 t) (rel_xval_stack (rel_exit L) (\<lambda>_ _ _. False)) (Exn e, s') (Exn w', t')
        | Result v \<Rightarrow> \<exists>w'. w = Result w' \<and> rel_stack \<S> M1 (ptr_span p \<union> P \<union> A) s  (override_heap_on (ptr_span p \<union> P) t\<^sub>0 t) (rel_xval_stack (\<lambda>_ _ _. False) (rel_singleton_stack p)) (Result v, s') (Result w', t')"] )
        apply (rule refines_L2_catch_right)
            apply (rule f_g)
    subgoal by (clarsimp simp add: rel_stack_def t0'_def rel_alloc_def)
    subgoal by clarsimp
    subgoal by clarsimp
    subgoal for e e' s' t' 
      apply (frule rel_stack_unchanged_stack_free [OF stack', unfolded t0'_def])
      apply (frule rel_stack_unchanged_stack_free' [OF stack', unfolded t0'_def])
      apply (subst (asm) rel_stack_def)
      apply (clarsimp simp add: rel_exit_def) 
      apply (subst (asm) rel_push_def) 
      apply clarsimp
      apply (rule refines_exec_IO_modify_heap_padding_single_step_right_InL)
      using stack  
      apply (clarsimp simp add: stack_free' rel_alloc_def rel_stack_def t0'_def [symmetric] t [symmetric] t_t0' [symmetric])
      subgoal premises prems for w x
      proof -
        from prems obtain
          "e = Nonlocal x"
          "e' = (h_val (hmem s') p, w)"
          "L (hmem s') x w" and
          sf_s': "stack_free (htd s') = stack_free (htd s)" and
          sf_t': "stack_free (htd (frame (ptr_span p \<union> P \<union> A) t0' s')) = stack_free (htd t)" and
          "stack_free (htd s) \<subseteq> \<S>"
          "stack_free (htd s) \<inter> (ptr_span p \<union> P \<union> A) = {}"
          "stack_free (htd s) \<inter> M1 = {}"
          "t' = frame (ptr_span p \<union> P \<union> A) t0' s'"
          "equal_upto (M1 \<union> stack_free (htd s)) (hmem s') (hmem s)" and
          htd_eq: "htd s' = htd s"  by (simp)
        have eq_typing: 
          "override_on (htd s') (htd t0') (ptr_span p \<union> P \<union> A - stack_free (htd s')) =
                  override_on (htd s') (htd (override_heap_on P t\<^sub>0 t)) (P \<union> A - stack_free (htd s'))"
          using disj_P_A disj_p_A 
          by (auto simp add: override_on_def fun_eq_iff t0'_def htd_eq t htd_frame override_heap_on_def)


        have eq_heap: "heap_update_padding p (h_val (hmem s') p)
                    (heap_list (hmem s') (size_of TYPE('a)) (ptr_val p))
                    (override_on (hmem s') (hmem t0') (ptr_span p \<union> P \<union> A \<union> stack_free (htd s'))) = 
                  override_on (hmem s') (hmem (override_heap_on P t\<^sub>0 t)) (P \<union> A \<union> stack_free (htd s'))"
          using disj_P_A disj_p_A
          apply (simp add: override_on_def override_heap_on_def fun_eq_iff t0'_def)
          by (smt (verit, best) disj_p_P disj_stack_free_s_p h_val_def heap_list_length 
              heap_update_list_id' heap_update_list_value heap_update_padding_def 
              hmem_htd_upd max_size orthD2 sf_s' to_bytes_heap_list_id)

        show "hmem_upd
               (heap_update_padding p (h_val (hmem s') p)
                 (heap_list (hmem s') (size_of TYPE('a)) (ptr_val p)))
               (frame (ptr_span p \<union> P \<union> A) t0' s') =
              frame (P \<union> A) (override_heap_on P t\<^sub>0 t) s'"
          apply (simp add: frame_def comp_def)
          using eq_typing eq_heap
          by (metis (no_types, lifting) heap.upd_cong hmem_htd_upd typing.upd_cong)
      qed
      done
    subgoal by clarsimp
    subgoal by clarsimp
    subgoal by clarsimp
    subgoal for v v' s' t'
      apply (clarsimp)
      apply (frule rel_stack_unchanged_stack_free [OF stack', unfolded t0'_def])
      apply (frule rel_stack_unchanged_stack_free' [OF stack', unfolded t0'_def])
      apply (subst (asm) rel_stack_def)
      apply (clarsimp simp add: rel_exit_def) 
      apply (subst (asm) rel_singleton_stack_def) 
      apply clarsimp
      apply (rule refines_exec_IO_modify_heap_padding_single_step_right)
      using stack  
      apply (clarsimp simp add: stack_free' rel_alloc_def rel_stack_def t0'_def [symmetric] t [symmetric] t_t0' [symmetric])
      subgoal premises prems       proof -
        from prems obtain
          "v' = h_val (hmem s') p" and
          sf_s': "stack_free (htd s') = stack_free (htd s)" and
          sf_t': "stack_free (htd (frame (ptr_span p \<union> P \<union> A) t0' s')) = stack_free (htd t)" and
          "stack_free (htd s) \<subseteq> \<S>"
          "stack_free (htd s) \<inter> (ptr_span p \<union> P \<union> A) = {}"
          "stack_free (htd s) \<inter> M1 = {}"
          "t' = frame (ptr_span p \<union> P \<union> A) t0' s'"
          "equal_upto (M1 \<union> stack_free (htd s)) (hmem s') (hmem s)" and
          htd_eq: "htd s' = htd s" by simp
        have eq_typing: 
          "override_on (htd s') (htd t0') (ptr_span p \<union> P \<union> A - stack_free (htd s')) =
                  override_on (htd s') (htd (override_heap_on P t\<^sub>0 t)) (P \<union> A - stack_free (htd s'))"
          using disj_P_A disj_p_A 
          by (auto simp add: override_on_def fun_eq_iff t0'_def htd_eq t htd_frame override_heap_on_def)


        have eq_heap: "heap_update_padding p (h_val (hmem s') p)
                    (heap_list (hmem s') (size_of TYPE('a)) (ptr_val p))
                    (override_on (hmem s') (hmem t0') (ptr_span p \<union> P \<union> A \<union> stack_free (htd s'))) = 
                  override_on (hmem s') (hmem (override_heap_on P t\<^sub>0 t)) (P \<union> A \<union> stack_free (htd s'))"
          using disj_P_A disj_p_A
          apply (simp add: override_on_def override_heap_on_def fun_eq_iff t0'_def)
          by (smt (verit, best) disj_p_P disj_stack_free_s_p h_val_def heap_list_length 
              heap_update_list_id' heap_update_list_value heap_update_padding_def 
              hmem_htd_upd max_size orthD2 sf_s' to_bytes_heap_list_id)

        show "hmem_upd
               (heap_update_padding p (h_val (hmem s') p)
                 (heap_list (hmem s') (size_of TYPE('a)) (ptr_val p)))
               (frame (ptr_span p \<union> P \<union> A) t0' s') =
              frame (P \<union> A) (override_heap_on P t\<^sub>0 t) s'"
          apply (simp add: frame_def comp_def)
          using eq_typing eq_heap
          by (metis (no_types, lifting) heap.upd_cong hmem_htd_upd typing.upd_cong)
      qed
      done
    done
qed

lemma refines_rel_stack_pop_heap_both_singleton_guarded:
  fixes p:: "'a::xmem_type ptr"
  assumes stack: "rel_alloc \<S> M A t\<^sub>0 s t"
  assumes f_g: "refines f (L2_seq (L2_guard (\<lambda>_. G)) (\<lambda>_. g)) s t
             (rel_stack \<S> M1 (ptr_span p \<union> P \<union> A) s
               (override_heap_on (ptr_span p \<union> P) t\<^sub>0 t)
               (rel_xval_stack (rel_exit (rel_push p L)) (rel_singleton_stack p)))"
  assumes disj_P_A: "G \<Longrightarrow> P \<inter> A = {}"
  assumes disj_p_A: "G \<Longrightarrow> ptr_span p \<inter> A = {}"
  assumes disj_p_P: "G \<Longrightarrow> ptr_span p \<inter> P = {}"
  assumes disj_stack_free_s_p: "G \<Longrightarrow> ptr_span p \<inter> stack_free (htd s) = {}"
  assumes disj_stack_free_s_P: "G \<Longrightarrow> P \<inter> stack_free (htd s) = {}"
  shows "refines
    f
    (L2_seq
      (L2_catch (L2_seq (L2_guard (\<lambda>_. G)) (\<lambda>_. g))
         (\<lambda>x. (L2_seq (IO_modify_heap_paddingE p (\<lambda>_. (fst x))) (\<lambda>_. L2_throw (snd x) ns_exit))))
      (\<lambda>x. (IO_modify_heap_paddingE p (\<lambda>_. x)))) s t
    (rel_stack \<S> M1 (P \<union> A) s (override_heap_on P t\<^sub>0 t) (rel_xval_stack (rel_exit L) (\<lambda>_. (=))))"
proof -
  {
    assume grd: "G"
    have ?thesis
      by (rule refines_rel_stack_pop_heap_both_singleton [OF stack f_g disj_P_A [OF grd] disj_p_A [OF grd] disj_p_P [OF grd]
            disj_stack_free_s_p [OF grd] disj_stack_free_s_P [OF grd]])
  } then show ?thesis
    by (rule refines_L2_guard_right'''')
qed

lemma refines_rel_stack_pop_heap_no_exit:
  fixes p:: "'a::xmem_type ptr"
  assumes stack: "rel_alloc \<S> M A t\<^sub>0 s t"
  assumes f_g: "refines f g s t 
             (rel_stack \<S> M1 (ptr_span p \<union> P \<union> A) s 
               (override_heap_on (ptr_span p \<union> P) t\<^sub>0 t) 
               (rel_xval_stack (rel_exit (\<lambda>_ _ _. False)) (rel_push p R)))"
  assumes disj_P_A: "P \<inter> A = {}"
  assumes disj_p_A: "ptr_span p \<inter> A = {}"
  assumes disj_p_P: "ptr_span p \<inter> P = {}" 
  assumes disj_stack_free_s_p: "ptr_span p \<inter> stack_free (htd s) = {}"
  assumes disj_stack_free_s_P: "P \<inter> stack_free (htd s) = {}"
  shows "refines 
    f 
    (L2_seq g (\<lambda>x. (L2_seq (IO_modify_heap_paddingE p (\<lambda>_. (fst x))) (\<lambda>_. L2_return (snd x) ns)))) s t 
    (rel_stack \<S> M1 (P \<union> A) s (override_heap_on P t\<^sub>0 t) (rel_xval_stack (rel_exit (\<lambda>_ _ _. False)) R))"
proof -
  from stack have sf_s_t: "stack_free (htd s) \<subseteq> stack_free (htd t)"
    using rel_alloc_def stack_free_htd_frame by auto

  from stack have t: "t = frame A t\<^sub>0 s"
    by (auto simp add: rel_alloc_def)

  define t0' where "t0' = override_heap_on (ptr_span p \<union> P) t\<^sub>0 t"

  have eq_htd: 
    "override_on (htd s) (htd t\<^sub>0) (A - stack_free (htd s)) =
        override_on (htd s) (htd t0') ((ptr_span p \<union> P \<union> A) - stack_free (htd s))"
    using disj_stack_free_s_p disj_stack_free_s_P disj_P_A disj_p_A t
    by (auto simp add: t0'_def override_heap_on_def override_on_def fun_eq_iff frame_def)

  have eq_hmem:
    "override_on (hmem s) (hmem t\<^sub>0) (A \<union> stack_free (htd s)) =
        override_on (hmem s) (hmem t0') ((ptr_span p \<union> P \<union> A) \<union> stack_free (htd s))"
    using disj_stack_free_s_p disj_stack_free_s_P disj_p_A disj_P_A t
    by (auto simp add: t0'_def override_heap_on_def override_on_def fun_eq_iff frame_def)

  from t have t_t0': "t = frame ((ptr_span p \<union> P \<union> A)) t0' s"
    using eq_htd eq_hmem
    apply (simp add: frame_def)
    by (metis (no_types, lifting) heap.upd_cong hmem_htd_upd typing.upd_cong)

  have stack': "rel_alloc \<S> M ((ptr_span p \<union> P \<union> A)) t0' s t"
    using stack disj_stack_free_s_P  disj_stack_free_s_p t t_t0'
    by (auto simp add: rel_alloc_def)

  from disj_stack_free_s_p disj_stack_free_s_P disj_stack_free_s_P stack
  have stack_free': "stack_free (htd s) \<inter> (P \<union> A) = {}"
    by (auto simp add: rel_alloc_def)

  show ?thesis
    unfolding L2_seq_def
    apply (rule refines_bindE_right)
        apply (rule f_g)
       apply simp_all
    subgoal by (simp add: rel_stack_def)
    subgoal for v v' s' t'
      apply (frule rel_stack_unchanged_stack_free [OF stack', unfolded t0'_def])
      apply (frule rel_stack_unchanged_stack_free' [OF stack', unfolded t0'_def])
      apply (subst (asm) rel_stack_def) 
      apply clarsimp 
      apply (subst (asm) rel_push_def) 
      apply clarsimp
      apply (rule refines_exec_IO_modify_heap_padding_step_right)
      apply (rule refines_exec_L2_return_right)
      using stack
      apply (clarsimp simp add: rel_stack_def rel_push_def rel_alloc_def stack_free')
      unfolding t0'_def [symmetric] t [symmetric]
      subgoal premises prems for w
      proof -
        from prems obtain
          "v' = (h_val (hmem s') p, w)"
          "R (hmem s') v w" and
          sf_s': "stack_free (htd s') = stack_free (htd s)" and
          sf_t': "stack_free (htd (frame (ptr_span p \<union> P \<union> A) t0' s')) = stack_free (htd t)" and
          "stack_free (htd s) \<subseteq> \<S>"
          "stack_free (htd s) \<inter> (ptr_span p \<union> P \<union> A) = {}"
          "stack_free (htd s) \<inter> M1 = {}"
          "t' = frame (ptr_span p \<union> P \<union> A) t0' s'"
          "equal_upto (M1 \<union> stack_free (htd s)) (hmem s') (hmem s)" and
          htd_eq: "htd s' = htd s"  by simp

        have eq_typing: 
          "override_on (htd s') (htd t0') (ptr_span p \<union> P \<union> A - stack_free (htd s')) =
                  override_on (htd s') (htd (override_heap_on P t\<^sub>0 t)) (P \<union> A - stack_free (htd s'))"
          using disj_P_A disj_p_A 
          by (auto simp add: override_on_def fun_eq_iff t0'_def htd_eq t htd_frame override_heap_on_def)


        have eq_heap: "heap_update_padding p (h_val (hmem s') p)
                    (heap_list (hmem s') (size_of TYPE('a)) (ptr_val p))
                    (override_on (hmem s') (hmem t0') (ptr_span p \<union> P \<union> A \<union> stack_free (htd s'))) = 
                  override_on (hmem s') (hmem (override_heap_on P t\<^sub>0 t)) (P \<union> A \<union> stack_free (htd s'))"
          using disj_P_A disj_p_A
          apply (simp add: override_on_def override_heap_on_def fun_eq_iff t0'_def)
          by (smt (verit, best) disj_p_P disj_stack_free_s_p h_val_def heap_list_length 
              heap_update_list_id' heap_update_list_value heap_update_padding_def 
              hmem_htd_upd max_size orthD2 sf_s' to_bytes_heap_list_id)

        show "hmem_upd
               (heap_update_padding p (h_val (hmem s') p)
                 (heap_list (hmem s') (size_of TYPE('a)) (ptr_val p)))
               (frame (ptr_span p \<union> P \<union> A) t0' s') =
              frame (P \<union> A) (override_heap_on P t\<^sub>0 t) s'"
          apply (simp add: frame_def comp_def)
          using eq_typing eq_heap
          by (metis (no_types, lifting) heap.upd_cong hmem_htd_upd typing.upd_cong)
      qed
      done
    done
qed

lemma refines_rel_stack_pop_heap_no_exit_guarded:
  fixes p:: "'a::xmem_type ptr"
  assumes stack: "rel_alloc \<S> M A t\<^sub>0 s t"
  assumes f_g: "refines f (L2_seq (L2_guard (\<lambda>_. G)) (\<lambda>_. g)) s t 
             (rel_stack \<S> M1 (ptr_span p \<union> P \<union> A) s 
               (override_heap_on (ptr_span p \<union> P) t\<^sub>0 t) 
               (rel_xval_stack (rel_exit (\<lambda>_ _ _. False)) (rel_push p R)))"
  assumes disj_P_A: "G \<Longrightarrow> P \<inter> A = {}"
  assumes disj_p_A: "G \<Longrightarrow> ptr_span p \<inter> A = {}"
  assumes disj_p_P: "G \<Longrightarrow> ptr_span p \<inter> P = {}" 
  assumes disj_stack_free_s_p: "G \<Longrightarrow> ptr_span p \<inter> stack_free (htd s) = {}"
  assumes disj_stack_free_s_P: "G \<Longrightarrow> P \<inter> stack_free (htd s) = {}"
  shows "refines 
    f 
    (L2_seq (L2_seq (L2_guard (\<lambda>_. G)) (\<lambda>_. g)) (\<lambda>x. (L2_seq (IO_modify_heap_paddingE p (\<lambda>_. (fst x))) (\<lambda>_. L2_return (snd x) ns)))) s t 
    (rel_stack \<S> M1 (P \<union> A) s (override_heap_on P t\<^sub>0 t) (rel_xval_stack (rel_exit (\<lambda>_ _ _. False)) R))"
proof -
  {
    assume grd: "G"
    have ?thesis
      by (rule refines_rel_stack_pop_heap_no_exit [OF stack f_g disj_P_A [OF grd] disj_p_A [OF grd] disj_p_P [OF grd]
            disj_stack_free_s_p [OF grd] disj_stack_free_s_P [OF grd]])
  } then show ?thesis
    by (rule refines_L2_guard_right''')
qed

lemma refines_rel_stack_pop_heap_no_exit_singleton:
  fixes p:: "'a::xmem_type ptr"
  assumes stack: "rel_alloc \<S> M A t\<^sub>0 s t"
  assumes f_g: "refines f g s t 
             (rel_stack \<S> M1 (ptr_span p \<union> P \<union> A) s 
               (override_heap_on (ptr_span p \<union> P) t\<^sub>0 t) 
               (rel_xval_stack (rel_exit (\<lambda>_ _ _. False)) (rel_singleton_stack p)))"
  assumes disj_P_A: "P \<inter> A = {}"
  assumes disj_p_A: "ptr_span p \<inter> A = {}"
  assumes disj_p_P: "ptr_span p \<inter> P = {}" 
  assumes disj_stack_free_s_p: "ptr_span p \<inter> stack_free (htd s) = {}"
  assumes disj_stack_free_s_P: "P \<inter> stack_free (htd s) = {}"
  shows "refines 
    f 
    (L2_seq g (\<lambda>x. (IO_modify_heap_paddingE p (\<lambda>_. x)))) s t 
    (rel_stack \<S> M1 (P \<union> A) s (override_heap_on P t\<^sub>0 t) (rel_xval_stack (rel_exit (\<lambda>_ _ _. False)) (\<lambda>_. (=))))"
proof -
  from stack have sf_s_t: "stack_free (htd s) \<subseteq> stack_free (htd t)"
    using rel_alloc_def stack_free_htd_frame by auto

  from stack have t: "t = frame A t\<^sub>0 s"
    by (auto simp add: rel_alloc_def)

  define t0' where "t0' = override_heap_on (ptr_span p \<union> P) t\<^sub>0 t"

  have eq_htd: 
    "override_on (htd s) (htd t\<^sub>0) (A - stack_free (htd s)) =
        override_on (htd s) (htd t0') ((ptr_span p \<union> P \<union> A) - stack_free (htd s))"
    using disj_stack_free_s_p disj_stack_free_s_P disj_P_A disj_p_A t
    by (auto simp add: t0'_def override_heap_on_def override_on_def fun_eq_iff frame_def)

  have eq_hmem:
    "override_on (hmem s) (hmem t\<^sub>0) (A \<union> stack_free (htd s)) =
        override_on (hmem s) (hmem t0') ((ptr_span p \<union> P \<union> A) \<union> stack_free (htd s))"
    using disj_stack_free_s_p disj_stack_free_s_P disj_p_A disj_P_A t
    by (auto simp add: t0'_def override_heap_on_def override_on_def fun_eq_iff frame_def)

  from t have t_t0': "t = frame ((ptr_span p \<union> P \<union> A)) t0' s"
    using eq_htd eq_hmem
    apply (simp add: frame_def)
    by (metis (no_types, lifting) heap.upd_cong hmem_htd_upd typing.upd_cong)

  have stack': "rel_alloc \<S> M ((ptr_span p \<union> P \<union> A)) t0' s t"
    using stack disj_stack_free_s_P  disj_stack_free_s_p t t_t0'
    by (auto simp add: rel_alloc_def)

  from disj_stack_free_s_p disj_stack_free_s_P disj_stack_free_s_P stack
  have stack_free': "stack_free (htd s) \<inter> (P \<union> A) = {}"
    by (auto simp add: rel_alloc_def)

  show ?thesis
    unfolding L2_seq_def
    apply (rule refines_bindE_right)
        apply (rule f_g)
       apply simp_all
    subgoal by (simp add: rel_stack_def)
    subgoal for v' s' t'
      apply (frule rel_stack_unchanged_stack_free [OF stack', unfolded t0'_def])
      apply (frule rel_stack_unchanged_stack_free' [OF stack', unfolded t0'_def])
      apply (subst (asm) rel_stack_def) 
      apply clarsimp 
      apply (subst (asm) rel_singleton_stack_def) 
      apply clarsimp
      apply (rule refines_exec_IO_modify_heap_padding_single_step_right)
      using stack
      apply (clarsimp simp add: rel_stack_def rel_push_def rel_alloc_def stack_free')
      unfolding t0'_def [symmetric] t [symmetric]
      subgoal premises prems 
      proof -
        from prems obtain
          "v' = h_val (hmem s') p" and
          sf_s': "stack_free (htd s') = stack_free (htd s)" and
          sf_t': "stack_free (htd (frame (ptr_span p \<union> P \<union> A) t0' s')) = stack_free (htd t)" and
          "stack_free (htd s) \<subseteq> \<S>"
          "stack_free (htd s) \<inter> (ptr_span p \<union> P \<union> A) = {}"
          "stack_free (htd s) \<inter> M1 = {}"
          "t' = frame (ptr_span p \<union> P \<union> A) t0' s'"
          "equal_upto (M1 \<union> stack_free (htd s)) (hmem s') (hmem s)" and
          htd_eq: "htd s' = htd s"  by simp

        have eq_typing: 
          "override_on (htd s') (htd t0') (ptr_span p \<union> P \<union> A - stack_free (htd s')) =
                  override_on (htd s') (htd (override_heap_on P t\<^sub>0 t)) (P \<union> A - stack_free (htd s'))"
          using disj_P_A disj_p_A 
          by (auto simp add: override_on_def fun_eq_iff t0'_def htd_eq t htd_frame override_heap_on_def)


        have eq_heap: "heap_update_padding p (h_val (hmem s') p)
                    (heap_list (hmem s') (size_of TYPE('a)) (ptr_val p))
                    (override_on (hmem s') (hmem t0') (ptr_span p \<union> P \<union> A \<union> stack_free (htd s'))) = 
                  override_on (hmem s') (hmem (override_heap_on P t\<^sub>0 t)) (P \<union> A \<union> stack_free (htd s'))"
          using disj_P_A disj_p_A
          apply (simp add: override_on_def override_heap_on_def fun_eq_iff t0'_def)
          by (smt (verit, best) disj_p_P disj_stack_free_s_p h_val_def heap_list_length 
              heap_update_list_id' heap_update_list_value heap_update_padding_def 
              hmem_htd_upd max_size orthD2 sf_s' to_bytes_heap_list_id)

        show "hmem_upd
               (heap_update_padding p (h_val (hmem s') p)
                 (heap_list (hmem s') (size_of TYPE('a)) (ptr_val p)))
               (frame (ptr_span p \<union> P \<union> A) t0' s') =
              frame (P \<union> A) (override_heap_on P t\<^sub>0 t) s'"
          apply (simp add: frame_def comp_def)
          using eq_typing eq_heap
          by (metis (no_types, lifting) heap.upd_cong hmem_htd_upd typing.upd_cong)
      qed
      done
    done
qed

lemma refines_rel_stack_pop_heap_no_exit_singleton_guarded:
  fixes p:: "'a::xmem_type ptr"
  assumes stack: "rel_alloc \<S> M A t\<^sub>0 s t"
  assumes f_g: "refines f (L2_seq (L2_guard (\<lambda>_. G)) (\<lambda>_. g)) s t 
             (rel_stack \<S> M1 (ptr_span p \<union> P \<union> A) s 
               (override_heap_on (ptr_span p \<union> P) t\<^sub>0 t) 
               (rel_xval_stack (rel_exit (\<lambda>_ _ _. False)) (rel_singleton_stack p)))"
  assumes disj_P_A: "G \<Longrightarrow> P \<inter> A = {}"
  assumes disj_p_A: "G \<Longrightarrow> ptr_span p \<inter> A = {}"
  assumes disj_p_P: "G \<Longrightarrow> ptr_span p \<inter> P = {}" 
  assumes disj_stack_free_s_p: "G \<Longrightarrow> ptr_span p \<inter> stack_free (htd s) = {}"
  assumes disj_stack_free_s_P: "G \<Longrightarrow> P \<inter> stack_free (htd s) = {}"
  shows "refines 
    f 
    (L2_seq (L2_seq (L2_guard (\<lambda>_. G)) (\<lambda>_. g)) (\<lambda>x. (IO_modify_heap_paddingE p (\<lambda>_. x)))) s t 
    (rel_stack \<S> M1 (P \<union> A) s (override_heap_on P t\<^sub>0 t) (rel_xval_stack (rel_exit (\<lambda>_ _ _. False)) (\<lambda>_. (=))))"
proof -
  {
    assume grd: "G"
    have ?thesis
      by (rule refines_rel_stack_pop_heap_no_exit_singleton [OF stack f_g disj_P_A [OF grd] disj_p_A [OF grd] disj_p_P [OF grd]
            disj_stack_free_s_p [OF grd] disj_stack_free_s_P [OF grd]])
  } then show ?thesis
    by (rule refines_L2_guard_right''')
qed

lemma refines_rel_stack_shuffle_both:
  assumes "refines f g s t (rel_stack \<S> M A s t\<^sub>0 (rel_xval_stack (rel_exit L) R))"
  assumes "\<And>h e e'. L h e e' \<Longrightarrow> L' h e (shuffle_exit e')"
  assumes "\<And>h v v'. R h v v' \<Longrightarrow> R' h v (shuffle v')"
  shows "refines 
    f 
    (L2_seq 
      (L2_catch g (\<lambda>e. L2_throw (shuffle_exit e) ns_exit))
      (\<lambda>x. L2_return (shuffle x) ns))
    s t 
    (rel_stack \<S> M A s t\<^sub>0 (rel_xval_stack (rel_exit L') R'))"
  using assms
  apply (clarsimp simp add: reaches_bind reaches_catch succeeds_bind succeeds_catch L2_defs refines_def_old L2_VARS_def
      rel_stack_def rel_alloc_def rel_xval_stack_def rel_exit_def rel_xval.simps default_option_def Exn_def[symmetric]
      split: xval_splits prod.splits)
  subgoal for r s'
  apply (cases r)
    subgoal 
      apply (clarsimp simp add: default_option_def  Exn_def[symmetric])
      subgoal for y

        apply (erule_tac x="Exn y" in allE)
        apply (erule_tac x="s'" in allE)
        apply clarsimp
        by (smt (verit) Exn_def Exn_eq_Exn Result_neq_Exn case_exception_or_result_Exn)
      done
    subgoal for v
        apply (erule_tac x="Result v" in allE)
        apply (erule_tac x="s'" in allE)
        apply clarsimp
      by (smt (z3) Result_eq_Result Result_neq_Exn case_exception_or_result_Result)
    done
  done

lemma refines_rel_stack_shuffle_no_exit:
  assumes "refines f g s t (rel_stack \<S> M A s t\<^sub>0 (rel_xval_stack (rel_exit (\<lambda>_ _ _. False)) R))"
  assumes "\<And>h v v'. R h v v' \<Longrightarrow> R' h v (shuffle v')"
  shows "refines 
    f 
    (L2_seq 
      g
      (\<lambda>x. L2_return (shuffle x) ns))
    s t 
    (rel_stack \<S> M A s t\<^sub>0 (rel_xval_stack (rel_exit (\<lambda>_ _ _. False)) R'))"
  using assms
  apply (clarsimp simp add: succeeds_bind reaches_bind L2_defs refines_def_old L2_VARS_def
      rel_stack_def rel_alloc_def rel_sum_stack_def rel_exit_def rel_sum.simps split: sum.splits prod.splits)
  subgoal for r s'
  apply (cases r)
    subgoal 
      apply (clarsimp simp add: default_option_def  Exn_def[symmetric])
      subgoal for y

        apply (erule_tac x="Exn y" in allE)
        apply (erule_tac x="s'" in allE)
        apply auto
        done
      done
    subgoal for v
        apply (erule_tac x="Result v" in allE)
        apply (erule_tac x="s'" in allE)
        apply clarsimp
        by (smt (z3) Result_eq_Result Result_neq_Exn case_exception_or_result_Result)
      done
    done

lemma L2_call_rel_stack_bare': 
  assumes f: "refines f g s t
                (rel_stack \<S> M1 A s t\<^sub>0 (rel_xval_stack L R))"
  shows "refines 
            f
            (L2_call g (\<lambda>x. x) ns')
            s t 
            (rel_stack \<S> M1 A s t\<^sub>0 (rel_xval_stack L R))"
  using assms
  by (auto simp add: L2_call_def refines_def_old reaches_map_value)

lemma L2_call_rel_stack_bare_retype_unreachable_exit': 
  assumes f: "refines f g s t
                (rel_stack \<S> M1 A s t\<^sub>0 (rel_xval_stack (rel_exit (\<lambda>_ _ _. False)) R))"
  shows "refines 
            f
            (L2_call g emb ns')
            s t 
            (rel_stack \<S> M1 A s t\<^sub>0 (rel_xval_stack (rel_exit (\<lambda>_ _ _. False)) R))"
  using assms
  apply (clarsimp simp add: L2_call_def reaches_map_value succeeds_bind reaches_bind L2_defs refines_def_old L2_VARS_def
      rel_stack_def rel_alloc_def rel_xval_stack_def rel_xval.simps rel_exit_def)
  by fastforce


lemma L2_call_rel_stack_bare_retype_unreachable_exit'': 
  assumes f: "refines f g s t
                (rel_stack \<S> M1 A s t\<^sub>0 (rel_xval_stack (rel_exit (\<lambda>_ _ _. False)) R))"
  shows "refines 
            f
            (L2_seq (L2_guard (\<lambda>_. P)) (\<lambda>_. 
              (L2_seq (L2_catch (L2_call g emb ns) 
                  (\<lambda>x. L2_seq (liftE (return ())) (\<lambda>_. L2_throw x ns_exit)))) 
            (\<lambda>v. L2_return v ns)))
            s t 
            (rel_stack \<S> M1 A s t\<^sub>0 (rel_xval_stack (rel_exit (\<lambda>_ _ _. False)) R))"
  using assms
  apply (clarsimp simp add: L2_call_def reaches_map_value succeeds_catch reaches_catch succeeds_bind reaches_bind L2_defs refines_def_old L2_VARS_def
      rel_stack_def rel_alloc_def rel_xval_stack_def rel_xval.simps rel_exit_def)
  by fastforce

lemma L2_call_rel_stack_bare_retype_unreachable_exit:
  assumes f: "refines f g s t
                (rel_stack \<S> M1 A s t\<^sub>0 (rel_xval_stack (rel_exit (\<lambda>_ _ _. False)) R))"
  shows "refines
            f
            (L2_seq (L2_guard (\<lambda>_. P)) (\<lambda>_.
              (L2_seq (L2_catch (L2_call g undefined ns)
                  (\<lambda>x. L2_seq (liftE (return ())) (\<lambda>_. L2_throw x ns_exit))))
            (\<lambda>v. L2_return v ns)))
            s t
            (rel_stack \<S> M1 A s t\<^sub>0 (rel_xval_stack (rel_exit (\<lambda>_ _ _. False)) R))"
  by (rule L2_call_rel_stack_bare_retype_unreachable_exit'' [OF f])

lemma L2_call_rel_stack_bare_retype_unreachable_exit_extend_modifies':
  assumes f: "refines f g s t
                (rel_stack \<S> M1 A s t\<^sub>0 (rel_xval_stack (rel_exit (\<lambda>_ _ _. False)) R))"
  assumes "P \<Longrightarrow> stack_free (htd s) \<inter> M2 = {}"
  assumes M1_M2: "P \<Longrightarrow> M1 \<subseteq> M2"
  shows "refines 
            f
            (L2_seq (L2_guard (\<lambda>_. P)) (\<lambda>_. 
              (L2_seq (L2_catch (L2_call g emb ns) 
                  (\<lambda>x. L2_seq (liftE (return ())) (\<lambda>_. L2_throw x ns_exit)))) 
            (\<lambda>v. L2_return v ns)))
            s t 
            (rel_stack \<S> M2 A s t\<^sub>0 (rel_xval_stack (rel_exit (\<lambda>_ _ _. False)) R))"
  using assms
  apply (clarsimp simp add: L2_call_def reaches_map_value succeeds_catch reaches_catch succeeds_bind reaches_bind L2_defs refines_def_old L2_VARS_def
      rel_stack_def rel_alloc_def rel_xval_stack_def rel_xval.simps rel_exit_def)
  subgoal for r s'
    apply (cases r)
    subgoal 
      apply (clarsimp simp add: Exn_def [symmetric] default_option_def)
      by (metis Result_neq_Exn)
    subgoal for v
      apply (erule_tac x="Result v" in allE)
      apply (erule_tac x=s' in allE)
      apply (clarsimp simp add: Exn_def [symmetric] default_option_def)
      by (smt (z3) case_xval_simps(2) equal_upto_mono map_exn_simps(2) 
          order_eq_refl sup_mono)
    done
  done


lemma L2_call_rel_stack_bare_retype_unreachable_exit_extend_modifies:
  assumes f: "refines f g s t
                (rel_stack \<S> M1 A s t\<^sub>0 (rel_xval_stack (rel_exit (\<lambda>_ _ _. False)) R))"
  assumes sf: "P \<Longrightarrow> stack_free (htd s) \<inter> M2 = {}"
  assumes M1_M2: "P \<Longrightarrow> M1 \<subseteq> M2"
  shows "refines
            f
            (L2_seq (L2_guard (\<lambda>_. P)) (\<lambda>_.
              (L2_seq (L2_catch (L2_call g undefined ns)
                  (\<lambda>x. L2_seq (liftE (return ())) (\<lambda>_. L2_throw x ns_exit))))
            (\<lambda>v. L2_return v ns)))
            s t
            (rel_stack \<S> M2 A s t\<^sub>0 (rel_xval_stack (rel_exit (\<lambda>_ _ _. False)) R))"
  by (rule L2_call_rel_stack_bare_retype_unreachable_exit_extend_modifies' [OF f sf M1_M2])

lemma L2_call_rel_stack_bare:
  assumes f: "refines f g s t
                (rel_stack \<S> M1 A s t\<^sub>0 (rel_xval_stack (rel_exit L) R))"
  shows "refines
            f
            (L2_seq (L2_guard (\<lambda>_. P)) (\<lambda>_.
              (L2_seq (L2_catch (L2_call g (\<lambda>x. x) ns)
                  (\<lambda>x. L2_seq (liftE (return ())) (\<lambda>_. L2_throw x ns_exit))))
            (\<lambda>v. L2_return v ns)))
            s t
            (rel_stack \<S> M1 A s t\<^sub>0 (rel_xval_stack (rel_exit L) R))"
  using assms
  apply (clarsimp simp add: L2_call_def reaches_map_value succeeds_catch reaches_catch succeeds_bind reaches_bind L2_defs refines_def_old L2_VARS_def
      rel_stack_def rel_alloc_def rel_xval_stack_def rel_xval.simps rel_exit_def)
  subgoal for r s'
    apply (cases r)
    subgoal 
      apply (clarsimp simp add: default_option_def  Exn_def[symmetric])
      subgoal for y

        apply (erule_tac x="Exn y" in allE)
        apply (erule_tac x="s'" in allE)
        apply fastforce
        done
      done
    subgoal for v
      apply (erule_tac x="Result v" in allE)
      apply (erule_tac x="s'" in allE)
      apply fastforce
      done
    done
  done

lemma L2_call_rel_stack_bare_extend_modifies:
  assumes f: "refines f g s t
                (rel_stack \<S> M1 A s t\<^sub>0 (rel_xval_stack (rel_exit L) R))"
  assumes sf: "P \<Longrightarrow> stack_free (htd s) \<inter> M2 = {}"
  assumes M1_M2: "P \<Longrightarrow> M1 \<subseteq> M2"
  shows "refines
            f
            (L2_seq (L2_guard (\<lambda>_. P)) (\<lambda>_.
              (L2_seq (L2_catch (L2_call g (\<lambda>x. x) ns)
                  (\<lambda>x. L2_seq (liftE (return ())) (\<lambda>_. L2_throw x ns_exit))))
            (\<lambda>v. L2_return v ns)))
            s t
            (rel_stack \<S> M2 A s t\<^sub>0 (rel_xval_stack (rel_exit L) R))"
  unfolding L2_defs L2_VARS_def liftE_return 
  apply (clarsimp simp add: f_catch_throw L2_call_def refines_bind_guard_right_iff)
  apply (rule refines_weaken [OF f])
  using sf M1_M2
  apply (clarsimp simp add: rel_stack_def rel_alloc_def)
  by (meson Un_subset_iff Un_upper2 equal_upto_mono sup.coboundedI1)

lemma refines_rel_stack_extend_modifies:
  assumes f: "refines f (L2_seq (L2_guard (\<lambda>_. P)) (\<lambda>_. g)) s t (rel_stack \<S> M1 A s t\<^sub>0 Q)"
  assumes sf: "P \<Longrightarrow> M2 \<inter> stack_free (htd s) = {}"
  assumes M1_M2: "P \<Longrightarrow> M1 \<subseteq> M2"
  shows "refines f (L2_seq (L2_guard (\<lambda>_. P)) (\<lambda>_. g)) s t (rel_stack \<S> M2 A s t\<^sub>0 Q)"
  using assms
  apply (clarsimp simp add: L2_call_def reaches_map_value succeeds_catch reaches_catch succeeds_bind reaches_bind L2_defs refines_def_old L2_VARS_def
      rel_stack_def rel_alloc_def rel_xval_stack_def rel_xval.simps rel_exit_def)
  by (smt (verit, best) dual_order.refl equal_upto_mono inf_aci(1) sup.mono)

lemma refines_rel_sum_stack_pop_exit': 
  assumes f_g: 
  "refines f g s t 
    (rel_stack \<S> M A s t\<^sub>0 
       (rel_xval_stack 
          (rel_exit (rel_push p L)) 
          R))"
  shows   
    "refines f (L2_catch g (\<lambda>(x, p). L2_throw p ns)) s t 
      (rel_stack \<S> M A s t\<^sub>0 
         (rel_xval_stack 
            (rel_exit L) 
            R))"
  apply (rule refines_L2_catch_right)
      apply (rule f_g)
     apply simp_all
  apply (auto simp add: L2_call_def reaches_map_value succeeds_catch reaches_catch 
      succeeds_bind reaches_bind L2_defs refines_def_old default_option_def Exn_def [symmetric] L2_VARS_def
      rel_push_def 
      rel_stack_def rel_alloc_def rel_xval_stack_def rel_xval.simps rel_exit_def)
  done

lemma refines_rel_sum_stack_pop_exit: 
  assumes f_g: 
  "refines f g s t 
    (rel_stack \<S> M A s t\<^sub>0 
       (rel_xval_stack 
          (rel_exit (rel_push p L)) 
          R))"
  shows   
    "refines f (L2_catch g (\<lambda>x. L2_throw (snd x) ns)) s t 
      (rel_stack \<S> M A s t\<^sub>0 
         (rel_xval_stack 
            (rel_exit L) 
            R))"
  apply (rule refines_L2_catch_right)
      apply (rule f_g)
     apply simp_all
  apply (auto simp add: L2_call_def reaches_map_value succeeds_catch reaches_catch 
      succeeds_bind reaches_bind L2_defs refines_def_old default_option_def Exn_def [symmetric] L2_VARS_def
      rel_push_def 
      rel_stack_def rel_alloc_def rel_xval_stack_def rel_xval.simps rel_exit_def)
  done


end



lemma L2_call_fuse_handlers1:
  "L2_seq 
         (L2_catch 
           (L2_seq
              (L2_catch g (\<lambda>x. L2_seq (liftE (h1 x)) (\<lambda>_. L2_throw (prj1 x) ns1))) 
              (\<lambda>x. liftE (g1 x)))
           (\<lambda>x. L2_seq (liftE (h2 x)) (\<lambda>_. L2_throw (prj2 x) ns2)))
         (\<lambda>x. liftE (g2 x)) = 
   (L2_seq
       (L2_catch g (\<lambda>x. L2_seq (L2_seq (liftE (h1 x)) (\<lambda>_. liftE (h2 (prj1 x)))) (\<lambda>_. L2_throw (prj2 (prj1 x)) ns2))) 
       (\<lambda>x. L2_seq (liftE (g1 x)) (\<lambda>x. liftE (g2 x))))"
  unfolding L2_defs
  apply (rule spec_monad_eqI)
  apply (auto simp add: runs_to_iff)
  done

lemma L2_call_fuse_handlers2:
  "(L2_catch 
      (L2_seq
          (L2_catch g (\<lambda>x. L2_seq (liftE (h1 x)) (\<lambda>_. L2_throw (prj1 x) ns1))) 
          (\<lambda>x. liftE (g1 x)))
      (\<lambda>x. L2_throw (prj2 x) ns2))
    = 
      L2_seq 
       (L2_catch g (\<lambda>x. L2_seq (liftE (h1 x)) (\<lambda>_. L2_throw (prj2 (prj1 x)) ns2))) 
       (\<lambda>x. (liftE (g1 x)))"
  unfolding L2_defs
  apply (rule spec_monad_eqI)
  apply (clarsimp simp add: runs_to_iff)
  apply (auto simp add: runs_to_def_old default_option_def Exn_def split: xval_splits)
  done

lemma L2_call_triv_conv: "L2_call f (\<lambda>x. x) ns = f"
  unfolding L2_call_def
  apply (rule spec_monad_eqI)
  apply (auto simp add: runs_to_iff)
  done

lemma L2_catch_L2_call_conv: 
  "L2_catch
     (L2_call f (\<lambda>e. e) ns) 
     (\<lambda>e. L2_throw (emb e) ns') = 
   L2_call f (ETA_TUPLED emb) ns"
  apply (simp add: L2_call_triv_conv ETA_TUPLED_def)
  apply (simp add: L2_call_def map_exn_catch_conv L2_catch_def L2_throw_def comp_def)
  done

lemma L2_seq_return_conv: 
  "L2_seq (liftE (return x)) (\<lambda>x. liftE (return (f x))) = liftE (return (f x))"
  unfolding L2_defs
  apply (rule spec_monad_eqI)
  apply (auto simp add: runs_to_iff)
  done


lemma L2_seq_return_unused_conv: 
  "L2_seq (liftE (return x)) (\<lambda>_. g) = g"
  unfolding L2_defs
  apply (rule spec_monad_eqI)
  apply (auto simp add: runs_to_iff)
  done

lemma L2_seq_L2_return_unused_conv: 
  "L2_seq (L2_return x ns) (\<lambda>_. g) = g"
  unfolding L2_defs L2_VARS_def
  apply (rule spec_monad_eqI)
  apply (auto simp add: runs_to_iff)
  done

lemma L2_seq_return_id_conv: 
  "L2_seq f (\<lambda>x. liftE (return x)) = f"
  unfolding L2_defs
  apply (rule spec_monad_eqI)
  apply (auto simp add: runs_to_iff)
  done


lemma L2_seq_L2_return_id_conv: 
  "L2_seq f (\<lambda>x. L2_return x ns) = f"
  unfolding L2_defs L2_VARS_def
  apply (rule spec_monad_eqI)
  apply (auto simp add: runs_to_iff)
  done

lemma L2_catch_L2_guard_out_conv: "L2_catch (L2_seq (L2_guard P) (\<lambda>_. X)) Y = L2_seq (L2_guard P) (\<lambda>_. L2_catch X Y)"
  unfolding L2_defs
  apply (rule spec_monad_eqI)
  apply (auto simp add: runs_to_iff)
  done


lemma L2_seq_guard_out_conv: 
  "L2_seq (L2_seq (L2_guard P) (\<lambda>_. X)) Y = (L2_seq (L2_guard P) (\<lambda>_. L2_seq X Y))"
  by (simp add: L2_seq_assoc)


lemma L2_seq_L2_catch_assoc: 
  "L2_seq (L2_seq (L2_catch X Y) Z1) Z2 = L2_seq (L2_catch X Y) (\<lambda>x. L2_seq (Z1 x) Z2)"
  by (rule L2_seq_assoc)

lemma L2_catch_throw_id: "L2_catch f (\<lambda>x. L2_throw x ns) = f"
  unfolding L2_defs
  apply (rule spec_monad_eqI)
  apply (clarsimp simp add: runs_to_iff)
  apply (clarsimp simp add: runs_to_def_old)
  by (metis Exn_def default_option_def exception_or_result_cases not_None_eq)

lemma L2_catch_call_throw: 
  "(L2_catch 
      (L2_call f emb ns)
      (\<lambda>x. L2_throw (g x) ns_exit)) = 
    L2_call f (ETA_TUPLED (\<lambda>x. (g (emb x)))) ns"
  unfolding L2_defs L2_call_def ETA_TUPLED_def
  apply (rule spec_monad_eqI)
  apply (clarsimp simp add: runs_to_iff)
  apply (auto simp add: runs_to_def_old map_exn_def split: xval_splits)
  done


lemma liftE_bind_L2_seq: "(liftE (A >>= B)) = L2_seq (liftE A) (ETA_TUPLED (\<lambda>x. liftE (B x)))"
  unfolding L2_defs L2_call_def ETA_TUPLED_def
  apply (rule spec_monad_eqI)
  apply (auto simp add: runs_to_iff)
  done

lemma liftE_L2_seq: "L2_seq (liftE A) (\<lambda>x. liftE (B x)) = (liftE (A >>= B))"
  unfolding L2_defs 
  by (simp add: liftE_bind)

lemma liftE_return_L2_gets_conv: "liftE (return x) = L2_gets (\<lambda>_. x) []"
  by (simp add: return_L2_gets_conv)

lemmas L2_call_canonical_convs = 
  L2_seq_return_conv
  L2_call_fuse_handlers2
  L2_call_fuse_handlers1
  L2_guard_join_nested
  liftE_L2_seq

  L2_seq_L2_catch_assoc
  L2_catch_L2_guard_out_conv
  L2_seq_guard_out_conv

  bind_assoc

lemmas L2_call_pre_final_convs =
  L2_seq_return_unused_conv
  L2_seq_L2_return_unused_conv
  L2_seq_return_id_conv
  L2_seq_L2_return_id_conv
  L2_catch_call_throw

lemmas L2_call_final_convs = 
  L2_seq_return_unused_conv
  L2_seq_L2_return_unused_conv
  L2_seq_return_id_conv
  L2_seq_L2_return_id_conv
  L2_catch_L2_call_conv
  guard_triv
  liftE_bind_L2_seq
  L2_gets_unbound
  L2_catch_throw_id
  L2_return_L2_gets_conv
  liftE_return_L2_gets_conv

  L2_seq_L2_catch_assoc
  L2_catch_L2_guard_out_conv
  L2_seq_guard_out_conv

lemma L2_call_ETA_TUPLED1: "L2_seq (L2_catch g h) g1 \<equiv> L2_seq (L2_catch g (ETA_TUPLED h)) (ETA_TUPLED g1)"
  unfolding ETA_TUPLED_def by simp

lemma L2_call_ETA_TUPLED2: "L2_seq (L2_call g emb ns) g1 \<equiv> L2_seq (L2_call g emb ns) (ETA_TUPLED g1)"
  unfolding ETA_TUPLED_def by simp


lemma distinct_sets_consI: "distinct_sets ps \<Longrightarrow> distinct_sets (p#ps) \<longleftrightarrow> p \<inter> \<Union> (set ps) = {}"
  by (simp)

lemma disjoint_subset_simps:
  "ASSUMPTION (A \<inter> B = {}) \<Longrightarrow> A' \<subseteq> A \<Longrightarrow> B \<inter> A' = {} \<longleftrightarrow> True"
  "ASSUMPTION (B \<inter> A = {}) \<Longrightarrow> A' \<subseteq> A \<Longrightarrow> B \<inter> A' = {} \<longleftrightarrow> True"
  "ASSUMPTION (A \<inter> B = {}) \<Longrightarrow> B' \<subseteq> B \<Longrightarrow> B' \<inter> A = {} \<longleftrightarrow> True"
  "ASSUMPTION (B \<inter> A = {}) \<Longrightarrow> B' \<subseteq> B \<Longrightarrow> B' \<inter> A = {} \<longleftrightarrow> True"
  by (auto simp add: ASSUMPTION_def)

lemma disjoint_subset_simps':
  "(B \<inter> A = {}) \<Longrightarrow> A' \<subseteq> A \<Longrightarrow> B \<inter> A' = {} \<longleftrightarrow> True"
  "(A \<inter> B = {}) \<Longrightarrow> B' \<subseteq> B \<Longrightarrow> B' \<inter> A = {} \<longleftrightarrow> True"
  "(B \<inter> A = {}) \<Longrightarrow> B' \<subseteq> B \<Longrightarrow> B' \<inter> A = {} \<longleftrightarrow> True"
  "(A \<inter> B = {}) \<Longrightarrow> A' \<subseteq> A \<Longrightarrow> B \<inter> A' = {} \<longleftrightarrow> True"
  by auto

lemma field_lvalue_ptr_span_trans:
  fixes p:: "'a::mem_type ptr"
  assumes "field_lookup (typ_info_t TYPE('a)) f 0 = Some (t, n)" 
  assumes "export_uinfo t = typ_uinfo_t (TYPE('b))"
  assumes "ptr_span p \<subseteq> A"
  shows "{&(p\<rightarrow>f)..+size_of TYPE('b::c_type)} \<subseteq> A"
  using field_tag_sub assms export_size_of by fastforce

lemma field_lvalue_ptr_span_root_contained:
  fixes p:: "'a::mem_type ptr"
  assumes "field_lookup (typ_info_t TYPE('a)) f 0 = Some (t, n)" 
  assumes "export_uinfo t = typ_uinfo_t (TYPE('b))"
  shows "{&(p\<rightarrow>f)..+size_of TYPE('b::c_type)} \<subseteq> ptr_span p"
  using field_tag_sub assms export_size_of by fastforce

lemma field_lvalue_disjoint_fields_same_root:
  fixes p:: "'a::mem_type ptr"
  assumes f: "field_lookup (typ_info_t TYPE('a)) f 0 = Some (T1, n)" 
  assumes exp1: "export_uinfo T1 = typ_uinfo_t (TYPE('b::c_type))"
  assumes g: "field_lookup (typ_info_t TYPE('a)) g 0 = Some (T2, m)"
  assumes exp2: "export_uinfo T2 = typ_uinfo_t (TYPE('c::c_type))"
  assumes prfx1: "\<not> prefix f g"
  assumes prfx2: "\<not> prefix g f"
  shows "{&(p\<rightarrow>f)..+size_of TYPE('b::c_type)} \<inter> {&(p\<rightarrow>g)..+size_of TYPE('c::c_type)} = {}"
  using  field_lookup_non_prefix_disj  [OF _ f g prfx2 prfx1] 
   field_lookup_offset_eq [OF f] field_lookup_offset_eq [OF g]  exp1 exp2 
   export_size_of [OF exp1] export_size_of [OF exp2]
  apply simp
  by (smt (verit, best) add.commute add_diff_cancel_left' 
      diff_is_0_eq dual_order.trans export_size_of f field_lookup_offset_size 
      field_lookup_wf_size_desc_gt field_lvalue_def fold_typ_uinfo_t g intvl_fields_disj 
      linorder_not_less max_size nat_less_le unat_of_nat_field_offset wf_size_desc)

lemma ptr_coerce_index_array_ptr_index_conv: 
  "ptr_coerce p +\<^sub>p uint i = array_ptr_index p False (nat (uint i))"
  by (auto simp add: array_ptr_index_def)

lemma ptr_coerce_index_array_ptr_index_numeral_conv: 
  "ptr_coerce p +\<^sub>p (numeral i) = array_ptr_index p False (numeral i)"
  by (auto simp add: array_ptr_index_def)

lemma ptr_coerce_index_array_ptr_index_numeral_conv':
  fixes p:: "(('a :: c_type)['b :: finite]) ptr"
  assumes sz_eq: "size_of TYPE('c::c_type) = size_of TYPE('a)"
  shows "PTR_COERCE('a['b] \<rightarrow> 'c::c_type) p +\<^sub>p (numeral n) = PTR_COERCE('a \<rightarrow> 'c) (array_ptr_index p False (numeral n))" 
  using assms
  by (simp add: array_ptr_index_simps(1) c_type_class.ptr_add_def)

lemma ptr_coerce_index_array_ptr_index_numeral_conv'':
  fixes p:: "(('a :: c_type)['b :: finite]) ptr"
  assumes sz_eq: "size_of TYPE('c::c_type) = size_of TYPE('a)"
  assumes bound:  "numeral n < CARD('b)"
  shows "PTR_COERCE('a['b] \<rightarrow> 'c::c_type) p +\<^sub>p (numeral n) =  PTR('c) &(p\<rightarrow>[replicate (numeral n) CHR ''1''])" 
proof -
  have eq1: "PTR('c) &(p\<rightarrow>[replicate (numeral n) CHR ''1'']) = PTR_COERCE('a \<rightarrow> 'c) (PTR('a) &(p\<rightarrow>[replicate (numeral n) CHR ''1'']))"
    by simp
  note replicate_numeral [simp del]
  show ?thesis
    apply (subst eq1 )
    apply (subst array_ptr_index_field_lvalue_conv [symmetric, OF bound])
    apply (rule  ptr_coerce_index_array_ptr_index_numeral_conv' [OF sz_eq])
    done
qed

lemma ptr_coerce_index_array_ptr_index_0_conv: 
  "ptr_coerce p +\<^sub>p 0 = array_ptr_index p False 0"
  by (auto simp add: array_ptr_index_def)

lemma ptr_coerce_index_array_ptr_index_1_conv: 
  "ptr_coerce p +\<^sub>p 1 = array_ptr_index p False 1"
  by (auto simp add: array_ptr_index_def)

lemma ptr_coerce_index_array_ptr_index_sint_conv: 
  "0 \<le>s i \<Longrightarrow> ptr_coerce p +\<^sub>p sint i = array_ptr_index p False (nat (sint i))"
  by (auto simp add: array_ptr_index_def word_sle_def)

lemma heap_access_Array_element'':
  fixes p :: "('a::mem_type['b::finite]) ptr"
  assumes less: "n < CARD('b)"
  shows
  "index (h_val hp p) n
      = h_val hp (array_ptr_index p False n)"
  using heap_access_Array_element' less
  by auto

lemma index_fupdate_split: "i < CARD('n) \<Longrightarrow> j < CARD('n) \<Longrightarrow> 
  index (fupdate i f (x::'a['n::finite])) j = (if i \<noteq> j then (x.[j]) else f (index x i))"
  by (cases "i=j") (auto simp add: arr_fupdate_same arr_fupdate_other)


lemma root_disjoint_field_lvalue_disjoint1:
  fixes p::"'a::mem_type ptr"
  assumes field_lookup: "field_lookup (typ_info_t TYPE('a)) path 0 = Some (t, n)"
  assumes match: "export_uinfo t = typ_uinfo_t TYPE('f::c_type)"
  assumes "ptr_span p \<inter> A = {}"
  shows "A \<inter> {&(p\<rightarrow>path)..+size_of TYPE('f)} = {}"
  using assms
  by (simp add: disjoint_field_lvalue_propagation_right export_size_of inter_commute)

lemma root_disjoint_field_lvalue_disjoint2:
  fixes p::"'a::mem_type ptr"
  assumes field_lookup: "field_lookup (typ_info_t TYPE('a)) path 0 = Some (t, n)"
  assumes match: "export_uinfo t = typ_uinfo_t TYPE('f::c_type)"
  assumes "ptr_span p \<inter> A = {}"
  shows "{&(p\<rightarrow>path)..+size_of TYPE('f)} \<inter> A = {}"
  using assms
  by (simp add: disjoint_field_lvalue_propagation_right export_size_of inter_commute)

context heap_state_global
begin

lemma global_update_frame_commute:
  shows "glob_upd g (frame A t\<^sub>0 s) =
         frame A t\<^sub>0 (glob_upd g s)"
proof -
  from glob_htd_commute glob_hmem_commute
  show ?thesis
    apply (clarsimp simp add: frame_def)
    by (smt (verit) heap.upd_cong typing.get_upd typing.upd_cong typing.upd_get)
qed

lemma L2_modify_no_heap_update_rel_stack[synthesize_rule refines_in_out]: 
  assumes "rel_alloc \<S> M A t\<^sub>0 s t"
  assumes "v s = v' t"
  shows "refines
          (L2_modify (\<lambda>s. glob_upd (\<lambda>_. v s) s))
          (L2_modify (\<lambda>s. glob_upd (\<lambda>_. v' s) s))
          s t
          (rel_stack \<S> {} A s t\<^sub>0 (rel_xval_stack L (\<lambda>_. (=))))"
proof -
  from  glob_hmem_commute have no_heap1: "\<And>g s. hmem (glob_upd g s) = hmem s"
    by (metis heap.get_upd heap.upd_get)

  from glob_htd_commute have no_htd1: "\<And>g s. htd (glob_upd g s) = htd s"
    by (metis typing.get_upd typing.upd_get)

  from assms no_heap1 no_htd1 global_update_frame_commute
  show ?thesis
    by (auto simp add: refines_def_old rel_stack_def rel_alloc_def L2_defs)
qed

lemma rel_alloc_glabal_independent_eq [rel_alloc_independent_globals]:
  assumes "rel_alloc \<S> M A t\<^sub>0 s t"
  shows "glob t = glob s"
  by (metis assms get_upd global_update_frame_commute rel_alloc_fold_frame upd_get)

end

lemma L2_seq_guard_cong_stateless: 
  "(\<And>s. P s = P' s) \<Longrightarrow> (\<And>s. P' s \<Longrightarrow> X = X') \<Longrightarrow> 
    L2_seq (L2_guard P) (\<lambda>_. X) = L2_seq (L2_guard P') (\<lambda>_. X')"
  using L2_seq_guard_cong''
  by metis

context globals_stack_heap_state
begin
lemma globals_subset_trans: "NO_MATCH \<G> X \<Longrightarrow> NO_MATCH \<G> Y \<Longrightarrow> X \<subseteq> \<G> \<Longrightarrow> \<G> \<subseteq> Y \<Longrightarrow> X \<subseteq> Y"
  by blast

lemma globals_disjoint_subset: "NO_MATCH \<G> X \<Longrightarrow> X \<subseteq> \<G> \<Longrightarrow> \<G> \<inter> A = {} \<Longrightarrow> X \<inter> A = {}"
  by blast
end

lemma Union_Diff_right_conv': "X \<union> Y = X \<union> (Y - X)"
  by blast

lemma Union_Diff_right_conv: "(Y - X) \<equiv> Z \<Longrightarrow> X \<union> Y \<equiv> X \<union> Z"
  apply (subst Union_Diff_right_conv')
  apply simp
  done

lemma Union_assoc: "X \<union> Y \<union> Z = X \<union> (Y \<union> Z)"
  by (simp add: sup_assoc)

simproc_setup Union_Diff_conv (\<open>ptr_span x \<union> Y\<close> ) = \<open>
let
  val cterm_eq = is_equal o Thm.fast_term_ord
  fun dest_union_right ct = ct |> Match_Cterm.switch [
    @{cterm_match \<open>?X \<union> ?Y\<close>} #> (fn {X, Y, ...} => X::dest_union_right Y),
    fn _ => [ct]]
in
fn _ => fn ctxt => fn ct =>
  let
    val {X, Y, ...} = @{cterm_match "?X \<union> ?Y"} ct
    val ys = dest_union_right Y
    val _ = if member cterm_eq ys X then () else raise Match
    val lhs = \<^infer_instantiate>\<open>X = X and Y = Y in cterm "Y - X"\<close> ctxt
    val eq = lhs |> Simplifier.asm_full_rewrite (ctxt addsimps @{thms Un_Diff Diff_triv Union_assoc})
    val rhs = Thm.rhs_of eq
  in
    if cterm_eq (lhs, rhs) then 
       NONE 
    else 
       let val eq' = @{thm Union_Diff_right_conv} OF [eq]
           val _ = Utils.verbose_msg 1 (* FIXME *) ctxt (fn _ => "Union_Diff_conv: " ^ Thm.string_of_thm ctxt eq')
       in SOME eq' end
  end
  handle Match => NONE
end\<close>
declare [[simproc del: Union_Diff_conv]]

lemma
"ptr_span q \<inter> ptr_span p = {} \<Longrightarrow> ptr_span x \<inter> ptr_span p = {} \<Longrightarrow>
  (ptr_span p \<union> (ptr_span q \<union> (ptr_span x \<union> ptr_span p))) = ptr_span p \<union> (ptr_span q \<union> ptr_span x) "
  supply [[simproc add: Union_Diff_conv]]
  apply simp
  done

lemma
"ptr_span q \<inter> ptr_span p = {} \<Longrightarrow> ptr_span x \<inter> ptr_span p = {} \<Longrightarrow>
  ((ptr_span p \<union> ptr_span q) \<union> (ptr_span x \<union> ptr_span p)) = ptr_span p \<union> (ptr_span q \<union> ptr_span x) "
  supply [[simproc add: Union_Diff_conv]]
  apply (simp add: Union_assoc)
  done

lemma
  assumes disj: "ptr_span q \<inter> ptr_span p = {}" 
    "ptr_span p \<inter> ptr_span q = {}" 
    "ptr_span x \<inter> ptr_span p = {}" 
    "ptr_span x \<inter> ptr_span q = {}" 
  shows "((ptr_span p \<union> ptr_span q) \<union> ((ptr_span p \<union> ptr_span q) \<union> ptr_span x \<union>  ptr_span p)) = ptr_span p \<union> (ptr_span q \<union> ptr_span x) "
  supply [[simproc add: Union_Diff_conv]]
  apply (simp add: Union_assoc disj)
  done

lemma subset_union_left: "X \<subseteq> L \<Longrightarrow> X \<subseteq> L \<union> R"
  by blast

lemma subset_union_right: "X \<subseteq> R \<Longrightarrow> X \<subseteq> L \<union> R"
  by blast

end