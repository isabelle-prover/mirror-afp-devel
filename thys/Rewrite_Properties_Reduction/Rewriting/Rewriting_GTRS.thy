theory Rewriting_GTRS
  imports Rewriting
    Replace_Constant
begin

subsection \<open>Specific results about rewriting under a ground system\<close>
abbreviation "ground_sys \<R> \<equiv> (\<forall> (s, t) \<in> \<R>. ground s \<and> ground t)"

lemma srrstep_ground:
  assumes "ground_sys \<R>"
    and "(s, t) \<in> srrstep \<F> \<R>"
  shows "ground s" "ground t" using assms
  by (auto simp: sig_step_def ground_subst_apply vars_term_subst elim!: rrstep_subst)

lemma srstep_pres_ground_l:
  assumes "ground_sys \<R>" "ground s"
    and "(s, t) \<in> srstep \<F> \<R>"
  shows "ground t" using assms
  by (auto simp: sig_step_def ground_subst_apply dest!: rstep_imp_C_s_r)

lemma srstep_pres_ground_r:
  assumes "ground_sys \<R>" "ground t"
    and "(s, t) \<in> srstep \<F> \<R>"
  shows "ground s" using assms
  by (auto simp: ground_vars_term_empty vars_term_subst sig_step_def vars_term_ctxt_apply ground_subst_apply dest!: rstep_imp_C_s_r)

lemma srsteps_pres_ground_l:
  assumes "ground_sys \<R>" "ground s"
   and  "(s, t) \<in> (srstep \<F> \<R>)\<^sup>+"
  shows "ground t" using assms(3, 2) srstep_pres_ground_l[OF assms(1)]
  by (induct rule: converse_trancl_induct) auto

lemma srsteps_pres_ground_r:
  assumes "ground_sys \<R>" "ground t"
    and "(s, t) \<in> (srstep \<F> \<R>)\<^sup>+"
  shows "ground s" using assms(3, 2) srstep_pres_ground_r[OF assms(1)]
  by (induct rule: converse_trancl_induct) auto


lemma srsteps_eq_pres_ground_l:
  assumes "ground_sys \<R>" "ground s"
   and  "(s, t) \<in> (srstep \<F> \<R>)\<^sup>*"
  shows "ground t" using srsteps_pres_ground_l[OF assms(1, 2)] assms(2, 3)
  by (auto simp: rtrancl_eq_or_trancl)

lemma srsteps_eq_pres_ground_r:
  assumes "ground_sys \<R>" "ground t"
    and "(s, t) \<in> (srstep \<F> \<R>)\<^sup>*"
  shows "ground s" using srsteps_pres_ground_r[OF assms(1, 2)] assms(2, 3)
  by (auto simp: rtrancl_eq_or_trancl)

lemma srsteps_with_root_step_ground:
  assumes "ground_sys \<R>"
    and "(s, t) \<in> srsteps_with_root_step \<F> \<R>"
  shows "ground s" "ground t" using srrstep_ground[OF assms(1)]
  using srsteps_eq_pres_ground_l[OF assms(1)]
  using srsteps_eq_pres_ground_r[OF assms(1)]
  using assms(2) unfolding srsteps_with_root_step_def
  by (meson relcomp.cases)+

subsection \<open>funas\<close>

lemma srrstep_funas:
  assumes "ground_sys \<R>"
    and "(s, t) \<in> srrstep \<F> \<R>"
  shows "funas_term s \<subseteq> funas_rel \<R>" "funas_term t \<subseteq> funas_rel \<R>" using assms
  by (auto simp: sig_step_def funas_term_subst ground_vars_term_empty funas_rel_def split: prod.splits elim!: rrstep_subst)

lemma srstep_funas_l:
  assumes "ground_sys \<R>"
    and "(s, t) \<in> srstep \<F> \<R>"
  shows "funas_term t \<subseteq> funas_term s \<union> funas_rel \<R>" using assms
  by (auto simp: ground_vars_term_empty vars_term_subst sig_step_def vars_term_ctxt_apply
     funas_term_subst funas_rel_def split: prod.splits dest!: rstep_imp_C_s_r)

lemma srstep_funas_r:
  assumes "ground_sys \<R>"
    and "(s, t) \<in> srstep \<F> \<R>"
  shows "funas_term s \<subseteq> funas_term t \<union> funas_rel \<R>" using assms
  by (auto simp: ground_vars_term_empty vars_term_subst sig_step_def vars_term_ctxt_apply
     funas_term_subst funas_rel_def split: prod.splits dest!: rstep_imp_C_s_r)

lemma srsteps_funas_l:
  assumes "ground_sys \<R>"
   and  "(s, t) \<in> (srstep \<F> \<R>)\<^sup>+"
  shows "funas_term t \<subseteq> funas_term s \<union> funas_rel \<R>" using assms(2)
  by (induct rule: converse_trancl_induct) (auto dest: srstep_funas_l[OF assms(1)])

lemma srsteps_funas_r:
  assumes "ground_sys \<R>"
    and "(s, t) \<in> (srstep \<F> \<R>)\<^sup>+"
  shows "funas_term s \<subseteq> funas_term t \<union> funas_rel \<R>" using assms(2)
  by (induct rule: converse_trancl_induct) (auto dest: srstep_funas_r[OF assms(1)])

lemma srsteps_eq_funas_l:
  assumes "ground_sys \<R>"
    and "(s, t) \<in> (srstep \<F> \<R>)\<^sup>*"
  shows "funas_term t \<subseteq> funas_term s \<union> funas_rel \<R>" using srsteps_funas_l[OF assms(1)] assms(2)
  by (auto simp: rtrancl_eq_or_trancl)

lemma srsteps_eq_funas_r:
  assumes "ground_sys \<R>"
    and "(s, t) \<in> (srstep \<F> \<R>)\<^sup>*"
  shows "funas_term s \<subseteq> funas_term t \<union> funas_rel \<R>" using srsteps_funas_r[OF assms(1)] assms(2)
  by (auto simp: rtrancl_eq_or_trancl)

lemma srsteps_with_root_step_funas:
  assumes "ground_sys \<R>"
    and "(s, t) \<in> srsteps_with_root_step \<F> \<R>"
  shows "funas_term s \<subseteq> funas_rel \<R>" "funas_term t \<subseteq> funas_rel \<R>"
  using srrstep_funas[OF assms(1)]
  using srsteps_eq_funas_l[OF assms(1)]
  using srsteps_eq_funas_r[OF assms(1)]
  using assms(2) unfolding srsteps_with_root_step_def
  by (metis relcompEpair sup_absorb2)+

end