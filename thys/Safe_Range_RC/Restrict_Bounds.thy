(*<*)
theory Restrict_Bounds
imports
  Relational_Calculus
  "Collections.Collections"
begin
(*>*)

section \<open>Restricting Bound Variables\<close>

fun flat_Disj where
  "flat_Disj (Disj Q1 Q2) = flat_Disj Q1 \<union> flat_Disj Q2"
| "flat_Disj Q = {Q}"

lemma finite_flat_Disj[simp]: "finite (flat_Disj Q)"
  by (induct Q rule: flat_Disj.induct) auto

lemma DISJ_flat_Disj: "DISJ (flat_Disj Q) \<triangleq> Q"
  by (induct Q rule: flat_Disj.induct) (auto simp: DISJ_union[THEN equiv_trans] simp del: cp.simps)

lemma fv_flat_Disj: "(\<Union>Q' \<in> flat_Disj Q. fv Q') = fv Q"
  by (induct Q rule: flat_Disj.induct) auto

lemma fv_flat_DisjD: "Q' \<in> flat_Disj Q \<Longrightarrow> x \<in> fv Q' \<Longrightarrow> x \<in> fv Q"
  by (auto simp: fv_flat_Disj[of Q, symmetric])

lemma cpropagated_flat_DisjD: "Q' \<in> flat_Disj Q \<Longrightarrow> cpropagated Q \<Longrightarrow> cpropagated Q'"
  by (induct Q rule: flat_Disj.induct) auto

lemma flat_Disj_sub: "flat_Disj Q \<subseteq> sub Q"
  by (induct Q) auto

lemma (in simplification) simplified_flat_DisjD: "Q' \<in> flat_Disj Q \<Longrightarrow> simplified Q \<Longrightarrow> simplified Q'"
  by (elim simplified_sub set_mp[OF flat_Disj_sub])

definition fixbound where
  "fixbound \<Q> x = {Q \<in> \<Q>. x \<in> nongens Q}"

definition (in simplification) rb_spec where
  "rb_spec Q = SPEC (\<lambda>Q'. rrb Q' \<and> simplified Q' \<and> Q \<triangleq> Q' \<and> fv Q' \<subseteq> fv Q)"

definition (in simplification) rb_INV where
  "rb_INV x Q \<Q> = (finite \<Q> \<and>
     Exists x Q \<triangleq> DISJ (exists x ` \<Q>) \<and>
     (\<forall>Q' \<in> \<Q>. rrb Q' \<and> fv Q' \<subseteq> fv Q \<and> simplified Q'))"

lemma (in simplification) rb_INV_I:
  "finite \<Q> \<Longrightarrow> Exists x Q \<triangleq> DISJ (exists x ` \<Q>) \<Longrightarrow> (\<And>Q'. Q' \<in> \<Q> \<Longrightarrow> rrb Q') \<Longrightarrow>
   (\<And>Q'. Q' \<in> \<Q> \<Longrightarrow> fv Q' \<subseteq> fv Q) \<Longrightarrow> (\<And>Q'. Q' \<in> \<Q> \<Longrightarrow> simplified Q') \<Longrightarrow> rb_INV x Q \<Q>"
  unfolding rb_INV_def by auto

fun (in simplification) rb :: "('a :: {infinite, linorder}, 'b :: linorder) fmla \<Rightarrow> ('a, 'b) fmla nres" where
  "rb (Neg Q) = do { Q' \<leftarrow> rb Q; RETURN (simp (Neg Q'))}"
| "rb (Disj Q1 Q2) = do { Q1' \<leftarrow> rb Q1; Q2' \<leftarrow> rb Q2; RETURN (simp (Disj Q1' Q2'))}"
| "rb (Conj Q1 Q2) = do { Q1' \<leftarrow> rb Q1; Q2' \<leftarrow> rb Q2; RETURN (simp (Conj Q1' Q2'))}"
| "rb (Exists x Q) = do {
    Q' \<leftarrow> rb Q;
    \<Q> \<leftarrow> WHILE\<^sub>T\<^bsup>rb_INV x Q'\<^esup>
      (\<lambda>\<Q>. fixbound \<Q> x \<noteq> {}) (\<lambda>\<Q>. do {
        Qfix \<leftarrow> RES (fixbound \<Q> x);
        G \<leftarrow> SPEC (cov x Qfix);
        RETURN (\<Q> - {Qfix} \<union>
          {simp (Conj Qfix (DISJ (qps G)))} \<union>
          (\<Union>y \<in> eqs x G. {cp (Qfix[x \<^bold>\<rightarrow> y])}) \<union>
          {cp (Qfix \<^bold>\<bottom> x)})})
      (flat_Disj Q');
    RETURN (simp (DISJ (exists x ` \<Q>)))}"
| "rb Q = do { RETURN (simp Q) }"

lemma (in simplification) cov_fixbound: "cov x Q G \<Longrightarrow> x \<in> fv Q \<Longrightarrow>
  fixbound (insert (cp (Q \<^bold>\<bottom> x)) (insert (simp (Conj Q (DISJ (qps G))))
  (\<Q> - {Q} \<union> ((\<lambda>y. cp (Q[x \<^bold>\<rightarrow> y])) ` eqs x G)))) x = fixbound \<Q> x - {Q}"
  using Gen_simp[OF cov_Gen_qps[of x Q G]]
  by (auto 4 4 simp: fixbound_def nongens_def fv_subst split: if_splits
      dest!: fv_cp[THEN set_mp] fv_simp[THEN set_mp] fv_erase[THEN set_mp] dest: arg_cong[of _ _ fv] simp del: cp.simps)

lemma finite_fixbound[simp]: "finite \<Q> \<Longrightarrow> finite (fixbound \<Q> x)"
  unfolding fixbound_def by auto

lemma fixboundE[elim_format]: "Q \<in> fixbound \<Q> x \<Longrightarrow> x \<in> fv Q \<and> Q \<in> \<Q> \<and> \<not> Gen x Q"
  unfolding fixbound_def nongens_def by auto

lemma fixbound_fv: "Q \<in> fixbound \<Q> x \<Longrightarrow> x \<in> fv Q"
  unfolding fixbound_def nongens_def by auto

lemma fixbound_in: "Q \<in> fixbound \<Q> x \<Longrightarrow> Q \<in> \<Q>"
  unfolding fixbound_def nongens_def by auto

lemma fixbound_empty_Gen: "fixbound \<Q> x = {} \<Longrightarrow> x \<in> fv Q \<Longrightarrow> Q \<in> \<Q> \<Longrightarrow> Gen x Q"
  unfolding fixbound_def nongens_def by auto

lemma fixbound_insert:
  "fixbound (insert Q \<Q>) x = (if Gen x Q \<or> x \<notin> fv Q then fixbound \<Q> x else insert Q (fixbound \<Q> x))"
  by (auto simp: fixbound_def nongens_def)

lemma fixbound_empty[simp]:
  "fixbound {} x = {}"
  by (auto simp: fixbound_def)

lemma flat_Disj_Exists_sub: "Q' \<in> flat_Disj Q \<Longrightarrow> Exists y Qy \<in> sub Q' \<Longrightarrow> Exists y Qy \<in> sub Q"
  by (induct Q arbitrary: Q' rule: flat_Disj.induct) auto

lemma rrb_flat_Disj[simp]: "Q \<in> flat_Disj Q' \<Longrightarrow> rrb Q' \<Longrightarrow> rrb Q"
  by (induct Q' rule: flat_Disj.induct) auto

lemma (in simplification) rb_INV_finite[simp]: "rb_INV x Q \<Q> \<Longrightarrow> finite \<Q>"
  by (auto simp: rb_INV_def)

lemma (in simplification) rb_INV_fv: "rb_INV x Q \<Q> \<Longrightarrow> Q' \<in> \<Q> \<Longrightarrow> z \<in> fv Q' \<Longrightarrow> z \<in> fv Q"
  by (auto simp: rb_INV_def)

lemma (in simplification) rb_INV_rrb: "rb_INV x Q \<Q> \<Longrightarrow> Q' \<in> \<Q> \<Longrightarrow> rrb Q'"
  by (auto simp: rb_INV_def)

lemma (in simplification) rb_INV_cpropagated: "rb_INV x Q \<Q> \<Longrightarrow> Q' \<in> \<Q> \<Longrightarrow> simplified Q'"
  by (auto simp: rb_INV_def)

lemma (in simplification) rb_INV_equiv: "rb_INV x Q \<Q> \<Longrightarrow> Exists x Q \<triangleq> DISJ (exists x ` \<Q>)"
  by (auto simp: rb_INV_def)

lemma (in simplification) rb_INV_init[simp]: "simplified Q \<Longrightarrow> rrb Q \<Longrightarrow> rb_INV x Q (flat_Disj Q)"
  by (auto simp: rb_INV_def fv_flat_DisjD simplified_flat_DisjD
      equiv_trans[OF equiv_Exists_cong[OF DISJ_flat_Disj[THEN equiv_sym]] Exists_DISJ, simplified])

lemma (in simplification) rb_INV_step[simp]:
  fixes Q :: "('a :: {infinite, linorder}, 'b :: linorder) fmla"
  assumes "rb_INV x Q \<Q>" "Q' \<in> fixbound \<Q> x" "cov x Q' G"
  shows "rb_INV x Q (insert (cp (Q' \<^bold>\<bottom> x)) (insert (simp (Conj Q' (DISJ (qps G)))) (\<Q> - {Q'} \<union> (\<lambda>y. cp (Q'[x \<^bold>\<rightarrow> y])) ` eqs x G)))"
proof (rule rb_INV_I, goal_cases finite equiv rrb fv simplified)
  case finite
  from assms(1,3) show ?case by simp
next
  case equiv
  from assms show ?case
    unfolding rb_INV_def
    by (auto 0 5 simp: fixbound_fv exists_cp_erase exists_cp_subst eqs_noteq exists_Exists
        image_image image_Un insert_commute ac_simps dest: fixbound_in elim!: equiv_trans
        intro:
        equiv_trans[OF DISJ_push_in]
        equiv_trans[OF DISJ_insert_reorder']
        equiv_trans[OF DISJ_insert_reorder]
        intro!:
        equiv_trans[OF DISJ_exists_pull_out]
        equiv_trans[OF equiv_Disj_cong[OF cov_Exists_equiv equiv_refl]]
        equiv_trans[OF equiv_Disj_cong[OF equiv_Disj_cong[OF equiv_Exists_exists_cong[OF equiv_refl] equiv_refl] equiv_refl]]
        simp del: cp.simps)
next
  case (rrb Q)
  with assms show ?case
    unfolding rb_INV_def
    by (auto intro!: rrb_cp_subst rrb_cp[OF rrb_erase] rrb_simp[of "Conj _ _"] dest: fixbound_in simp del: cp.simps)
next
  case (fv Q')
  with assms show ?case
    unfolding rb_INV_def
    by (auto 0 4 dest!: fv_cp[THEN set_mp] fv_simp[THEN set_mp] fv_DISJ[THEN set_mp, rotated 1] fv_erase[THEN set_mp]
        cov_fv[OF assms(3) _ qps_in, rotated]
        cov_fv[OF assms(3) _ eqs_in, rotated] dest: fixbound_in
        simp: fv_subst fixbound_fv split: if_splits simp del: cp.simps)
next
  case (simplified Q')
  with assms show ?case
    unfolding rb_INV_def by (auto simp: simplified_simp simplified_cp simp del: cp.simps)
qed

lemma (in simplification) rb_correct:
  fixes Q :: "('a :: {linorder, infinite}, 'b :: linorder) fmla"
  shows "rb Q \<le> rb_spec Q"
proof (induct Q rule: rb.induct[case_names Neg Disj Conj Exists Pred Bool Eq])
  case (Exists x Q)
  then show ?case
    unfolding rb.simps rb_spec_def bind_rule_complete
    by (rule order_trans, refine_vcg WHILEIT_rule[where R="measure (\<lambda>\<Q>. card (fixbound \<Q> x))"])
      (auto simp: rb_INV_rrb rrb_simp simplified_simp fixbound_fv equiv_trans[OF equiv_Exists_cong rb_INV_equiv]
        cov_fixbound fixbound_empty_Gen card_gt_0_iff UNION_singleton_eq_range subset_eq
        intro!: equiv_simp[THEN equiv_trans, THEN equiv_sym, OF equiv_sym]
        dest!: fv_DISJ[THEN set_mp, rotated 1] fv_simp[THEN set_mp] elim!: bspec elim: rb_INV_fv simp del: cp.simps)
qed (auto simp: rb_spec_def bind_rule_complete rrb_simp simplified_simp subset_eq dest!: fv_simp[THEN set_mp]
  elim!: order_trans intro!: equiv_simp[THEN equiv_trans, THEN equiv_sym, OF equiv_sym] simp del: cp.simps)

(*<*)
end
(*>*)