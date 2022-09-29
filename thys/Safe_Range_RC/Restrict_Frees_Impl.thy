(*<*)
theory Restrict_Frees_Impl
imports
  Restrict_Bounds_Impl
  Restrict_Frees
begin
(*>*)

section \<open>Refining the Non-Deterministic @{term simplification.split} Function\<close>

definition "fixfree_impl \<Q> = map (apsnd set) (filter (\<lambda>(Q, _ :: (nat \<times> nat) list). \<exists>x \<in> fv Q. gen_impl x Q = [])
   (sorted_list_of_set ((apsnd sorted_list_of_set) ` \<Q>)))"

definition "nongens_impl Q = filter (\<lambda>x. gen_impl x Q = []) (sorted_list_of_set (fv Q))"

lemma set_nongens_impl: "set (nongens_impl Q) = nongens Q"
  by (auto simp: nongens_def nongens_impl_def set_gen_impl simp flip: List.set_empty)

lemma set_fixfree_impl: "finite \<Q> \<Longrightarrow> \<forall>(_, Qeq) \<in> \<Q>. finite Qeq \<Longrightarrow> set (fixfree_impl \<Q>) = fixfree \<Q>"
  by (fastforce simp: fixfree_def nongens_def fixfree_impl_def set_gen_impl image_iff apsnd_def map_prod_def
    simp flip: List.set_empty split: prod.splits intro: exI[of _ "sorted_list_of_set _"])

lemma fixfree_empty_iff: "finite \<Q> \<Longrightarrow> \<forall>(_, Qeq) \<in> \<Q>. finite Qeq \<Longrightarrow> fixfree \<Q> \<noteq> {} \<longleftrightarrow> fixfree_impl \<Q> \<noteq> []"
  by (auto simp: set_fixfree_impl dest: arg_cong[of _ _ set] simp flip: List.set_empty)

definition "inf_impl \<Q>fin Q =
  map (apsnd set) (filter (\<lambda>(Qfix, xys). disjointvars Qfix (set xys) \<noteq> {} \<or> fv Qfix \<union> Field (set xys) \<noteq> fv Q)
    (sorted_list_of_set ((apsnd sorted_list_of_set) ` \<Q>fin)))"

lemma set_inf_impl: "finite \<Q>fin \<Longrightarrow> \<forall>(_, Qeq) \<in> \<Q>fin. finite Qeq \<Longrightarrow> set (inf_impl \<Q>fin Q) = inf \<Q>fin Q"
  by (fastforce simp: inf_def inf_impl_def image_iff)

lemma inf_empty_iff: "finite \<Q>fin \<Longrightarrow> \<forall>(_, Qeq) \<in> \<Q>fin. finite Qeq \<Longrightarrow> inf \<Q>fin Q \<noteq> {} \<longleftrightarrow> inf_impl \<Q>fin Q \<noteq> []"
  by (auto simp: set_inf_impl dest: arg_cong[of _ _ set] simp flip: List.set_empty)

definition (in simplification) split_impl :: "('a :: {infinite, linorder}, 'b :: linorder) fmla \<Rightarrow> (('a, 'b) fmla \<times> ('a, 'b) fmla) nres" where
  "split_impl Q = do {
     Q' \<leftarrow> rb_impl Q;
     \<Q>pair \<leftarrow> WHILE
        (\<lambda>(\<Q>fin, _). fixfree_impl \<Q>fin \<noteq> []) (\<lambda>(\<Q>fin, \<Q>inf). do {
          (Qfix, Qeq) \<leftarrow> RETURN (hd (fixfree_impl \<Q>fin));
          x \<leftarrow> RETURN (hd (nongens_impl Qfix));
          G \<leftarrow> RETURN (hd (cov_impl x Qfix));
          let \<Q>fin = \<Q>fin - {(Qfix, Qeq)} \<union>
            {(simp (Conj Qfix (DISJ (qps G))), Qeq)} \<union>
            (\<Union>y \<in> eqs x G. {(cp (Qfix[x \<^bold>\<rightarrow> y]), Qeq \<union> {(x,y)})});
          let \<Q>inf = \<Q>inf \<union> {cp (Qfix \<^bold>\<bottom> x)};
          RETURN (\<Q>fin, \<Q>inf)})
        ({(Q', {})}, {});
     \<Q>pair \<leftarrow> WHILE
        (\<lambda>(\<Q>fin, _). inf_impl \<Q>fin Q \<noteq> []) (\<lambda>(\<Q>fin, \<Q>inf). do {
          Qpair \<leftarrow> RETURN (hd (inf_impl \<Q>fin Q));
          let \<Q>fin = \<Q>fin - {Qpair};
          let \<Q>inf = \<Q>inf \<union> {CONJ Qpair};
          RETURN (\<Q>fin, \<Q>inf)})
        \<Q>pair;
     let (Qfin, Qinf) = assemble \<Q>pair;
     Qinf \<leftarrow> rb_impl Qinf;
     RETURN (Qfin, Qinf)}"

lemma (in simplification) split_INV2_imp_split_INV1: "split_INV2 Q \<Q>pair \<Longrightarrow> split_INV1 Q \<Q>pair"
  unfolding split_INV1_def split_INV2_def wf_state_def sr_def by auto

lemma hd_fixfree_impl_props:
  assumes "finite \<Q>" "\<forall>(_, Qeq) \<in> \<Q>. finite Qeq" "fixfree_impl \<Q> \<noteq> []"
  shows "hd (fixfree_impl \<Q>) \<in> \<Q>" "nongens (fst (hd (fixfree_impl \<Q>))) \<noteq> {}"
proof -
  from hd_in_set[of "fixfree_impl \<Q>"] assms(3) have "hd (fixfree_impl \<Q>) \<in> set (fixfree_impl \<Q>)"
    by blast
  then have "hd (fixfree_impl \<Q>) \<in> fixfree \<Q>"
    by (auto simp: set_fixfree_impl assms(1,2))
  then show "hd (fixfree_impl \<Q>) \<in> \<Q>" "nongens (fst (hd (fixfree_impl \<Q>))) \<noteq> {}"
    unfolding fixfree_def by auto
qed

lemma (in simplification) split_impl_refines_split: "split_impl Q \<le> split Q"
  apply (unfold split_def split_impl_def Let_def)
  supply rb_impl_refines_rb[refine_mono]
  apply refine_mono
   apply (rule order_trans[OF WHILE_le_WHILEI[where I="split_INV1 Q"]])
   apply (rule order_trans[OF WHILEI_le_WHILEIT])
   apply (rule WHILEIT_refine[OF _ _ _ refine_IdI, THEN refine_IdD])
      apply (simp_all only: pair_in_Id_conv split: prod.splits) [4]
    apply (intro allI impI, hypsubst_thin)
    apply (subst fixfree_empty_iff; auto simp: split_INV1_def wf_state_def)
    apply (intro allI impI, simp only: prod.inject, elim conjE, hypsubst_thin)
   apply refine_mono
  apply (subst set_fixfree_impl[symmetric]; auto simp: split_INV1_def wf_state_def intro!: hd_in_set)
  apply clarsimp
  subgoal for Q' \<Q>fin \<Q>inf Qfix Qeq Qfix' Qeq'
    using hd_fixfree_impl_props(2)[of \<Q>fin]
    by (force simp: split_INV1_def wf_state_def set_nongens_impl[symmetric] dest!: sym[of "(Qfix', _)"] intro!: hd_in_set)
   apply clarsimp
  subgoal for Q' \<Q>fin \<Q>inf Qfix Qeq Qfix' Qeq'
    apply (intro RETURN_rule cov_impl_cov hd_in_set rrb_cov_impl)
    using hd_fixfree_impl_props(1)[of \<Q>fin]
    by (force simp: split_INV1_def wf_state_def dest!: sym[of "(Qfix', _)"])
   apply (rule order_trans[OF WHILE_le_WHILEI[where I="split_INV1 Q"]])
   apply (rule order_trans[OF WHILEI_le_WHILEIT])
  apply (rule WHILEIT_refine[OF _ _ _ refine_IdI, THEN refine_IdD])
     apply (simp_all only: pair_in_Id_conv split_INV2_imp_split_INV1 split: prod.splits) [4]
   apply (intro allI impI, simp only: prod.inject, elim conjE, hypsubst_thin)
   apply (subst inf_empty_iff; auto simp: split_INV2_def wf_state_def)
  apply (intro allI impI, simp only: prod.inject, elim conjE, hypsubst_thin)
  apply refine_mono
  apply (subst set_inf_impl[symmetric]; auto simp: split_INV2_def wf_state_def intro!: hd_in_set)
  done

definition (in simplification) split_impl_det :: "('a :: {infinite, linorder}, 'b :: linorder) fmla \<Rightarrow> (('a, 'b) fmla \<times> ('a, 'b) fmla) dres" where
  "split_impl_det Q = do {
     Q' \<leftarrow> rb_impl_det Q;
     \<Q>pair \<leftarrow> dWHILE
        (\<lambda>(\<Q>fin, _). fixfree_impl \<Q>fin \<noteq> []) (\<lambda>(\<Q>fin, \<Q>inf). do {
          (Qfix, Qeq) \<leftarrow> dRETURN (hd (fixfree_impl \<Q>fin));
          x \<leftarrow> dRETURN (hd (nongens_impl Qfix));
          G \<leftarrow> dRETURN (hd (cov_impl x Qfix));
          let \<Q>fin = \<Q>fin - {(Qfix, Qeq)} \<union>
            {(simp (Conj Qfix (DISJ (qps G))), Qeq)} \<union>
            (\<Union>y \<in> eqs x G. {(cp (Qfix[x \<^bold>\<rightarrow> y]), Qeq \<union> {(x,y)})});
          let \<Q>inf = \<Q>inf \<union> {cp (Qfix \<^bold>\<bottom> x)};
          dRETURN (\<Q>fin, \<Q>inf)})
        ({(Q', {})}, {});
     \<Q>pair \<leftarrow> dWHILE
        (\<lambda>(\<Q>fin, _). inf_impl \<Q>fin Q \<noteq> []) (\<lambda>(\<Q>fin, \<Q>inf). do {
          Qpair \<leftarrow> dRETURN (hd (inf_impl \<Q>fin Q));
          let \<Q>fin = \<Q>fin - {Qpair};
          let \<Q>inf = \<Q>inf \<union> {CONJ Qpair};
          dRETURN (\<Q>fin, \<Q>inf)})
        \<Q>pair;
     let (Qfin, Qinf) = assemble \<Q>pair;
     Qinf \<leftarrow> rb_impl_det Qinf;
     dRETURN (Qfin, Qinf)}"

lemma (in simplification) split_impl_det_refines_split_impl: "nres_of (split_impl_det Q) \<le> split_impl Q"
  unfolding split_impl_def split_impl_det_def Let_def
  by (refine_transfer rb_impl_det_refines_rb_impl)

lemmas (in simplification) SPLIT_correct =
  split_impl_det_refines_split_impl[THEN order_trans, OF
  split_impl_refines_split[THEN order_trans, OF
  split_correct]]

(*<*)
end
(*>*)