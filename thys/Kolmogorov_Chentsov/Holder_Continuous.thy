(* Title:      Kolmogorov_Chentsov/Holder_Continuous.thy
   Author:     Christian Pardillo Laursen, University of York
*)

section "Hölder continuity"

theory Holder_Continuous
  imports "HOL-Analysis.Analysis"
begin

text \<open> H{\"o}lder continuity is a weaker version of Lipschitz continuity. \<close>

definition holder_at_within :: "real \<Rightarrow> 'a set \<Rightarrow> 'a \<Rightarrow> ('a :: metric_space \<Rightarrow> 'b :: metric_space) \<Rightarrow> bool" where
  "holder_at_within \<gamma> D r \<phi> \<equiv> \<gamma> \<in> {0<..1} \<and> 
  (\<exists>\<epsilon> > 0. \<exists>C \<ge> 0. \<forall>s \<in> D. dist r s < \<epsilon> \<longrightarrow> dist (\<phi> r) (\<phi> s) \<le> C * dist r s powr \<gamma>)"

definition local_holder_on :: "real \<Rightarrow> 'a :: metric_space set \<Rightarrow> ('a \<Rightarrow> 'b :: metric_space) \<Rightarrow> bool" where
  "local_holder_on \<gamma> D \<phi> \<equiv> \<gamma> \<in> {0<..1} \<and>
  (\<forall>t\<in>D. \<exists>\<epsilon> > 0. \<exists>C \<ge> 0. (\<forall>r\<in>D. \<forall>s\<in>D. dist s t < \<epsilon> \<and> dist r t < \<epsilon> \<longrightarrow> dist (\<phi> r) (\<phi> s) \<le> C * dist r s powr \<gamma>))"

definition holder_on :: "real \<Rightarrow> 'a :: metric_space set \<Rightarrow> ('a \<Rightarrow> 'b :: metric_space) \<Rightarrow> bool" ("_-holder'_on" 1000) where
  "\<gamma>-holder_on D \<phi> \<longleftrightarrow> \<gamma> \<in> {0<..1} \<and> (\<exists>C \<ge> 0. (\<forall>r\<in>D. \<forall>s\<in>D. dist (\<phi> r) (\<phi> s) \<le> C * dist r s powr \<gamma>))"

lemma holder_onI:
  assumes "\<gamma> \<in> {0<..1}" "\<exists>C \<ge> 0. (\<forall>r\<in>D. \<forall>s\<in>D. dist (\<phi> r) (\<phi> s) \<le> C * dist r s powr \<gamma>)"
  shows "\<gamma>-holder_on D \<phi>"
  unfolding holder_on_def using assms by blast

text \<open> We prove various equivalent formulations of local holder continuity, using open and closed
  balls and inequalities. \<close>

lemma local_holder_on_cball:
  "local_holder_on \<gamma> D \<phi> \<longleftrightarrow> \<gamma> \<in> {0<..1} \<and>
  (\<forall>t\<in>D. \<exists>\<epsilon> > 0. \<exists>C \<ge> 0. (\<forall>r\<in>cball t \<epsilon> \<inter> D. \<forall>s\<in>cball t \<epsilon> \<inter> D. dist (\<phi> r) (\<phi> s) \<le> C * dist r s powr \<gamma>))"
  (is "?L \<longleftrightarrow> ?R")
proof
  assume *: ?L
  {
    fix t assume "t \<in> D"
    then obtain \<epsilon> C where "\<epsilon> > 0" "C \<ge> 0"
      "\<forall>r\<in>ball t \<epsilon> \<inter> D. \<forall>s\<in>ball t \<epsilon> \<inter> D. dist (\<phi> r) (\<phi> s) \<le> C * dist r s powr \<gamma>"
      using * unfolding local_holder_on_def apply simp
      by (metis Int_iff dist_commute mem_ball)
    then have **: "\<forall>r\<in>cball t (\<epsilon>/2) \<inter> D. \<forall>s\<in>cball t (\<epsilon>/2) \<inter> D. dist (\<phi> r) (\<phi> s) \<le> C * dist r s powr \<gamma>"
      by auto
    have "\<exists>\<epsilon> > 0. \<exists>C \<ge> 0. \<forall>r\<in>cball t \<epsilon> \<inter> D. \<forall>s\<in>cball t \<epsilon> \<inter> D. dist (\<phi> r) (\<phi> s) \<le> C * dist r s powr \<gamma>"
      apply (rule exI[where x = "\<epsilon>/2"])
      apply (simp add: \<open>\<epsilon> > 0\<close>)
      apply (rule exI[where x = "C"])
      using ** \<open>C \<ge> 0\<close> by blast
  }
  then show ?R
    using * local_holder_on_def by blast
next
  assume *: ?R
  {
    fix t assume "t \<in> D"
    then obtain \<epsilon> C where eC: "\<epsilon> > 0" "C \<ge> 0"
      "\<forall>r\<in>cball t \<epsilon> \<inter> D. \<forall>s\<in>cball t \<epsilon> \<inter> D. dist (\<phi> r) (\<phi> s) \<le> C * dist r s powr \<gamma>"
      using * by blast
    then have "\<forall>r \<in> D. \<forall>s \<in> D. dist r t < \<epsilon> \<and> dist s t < \<epsilon> \<longrightarrow> dist (\<phi> r) (\<phi> s) \<le> C * dist r s powr \<gamma>"
      unfolding cball_def by (simp add: dist_commute)
    then have "\<exists>\<epsilon>>0. \<exists>C\<ge>0. \<forall>r \<in> D. \<forall>s \<in> D. dist r t < \<epsilon> \<and> dist s t < \<epsilon> \<longrightarrow> dist (\<phi> r) (\<phi> s) \<le> C * dist r s powr \<gamma>"
      using eC by blast
  }
  then show "local_holder_on \<gamma> D \<phi>"
    using * unfolding local_holder_on_def by metis
qed

corollary local_holder_on_leq_def: "local_holder_on \<gamma> D \<phi> \<longleftrightarrow> \<gamma> \<in> {0<..1} \<and>
  (\<forall>t\<in>D. \<exists>\<epsilon> > 0. \<exists>C \<ge> 0. (\<forall>r\<in>D. \<forall>s\<in>D. dist s t \<le> \<epsilon> \<and> dist r t \<le> \<epsilon> \<longrightarrow> dist (\<phi> r) (\<phi> s) \<le> C * dist r s powr \<gamma>))"
  unfolding local_holder_on_cball by (metis dist_commute Int_iff mem_cball)

corollary local_holder_on_ball: "local_holder_on \<gamma> D \<phi> \<longleftrightarrow> \<gamma> \<in> {0<..1} \<and>
  (\<forall>t\<in>D. \<exists>\<epsilon> > 0. \<exists>C \<ge> 0. (\<forall>r\<in>ball t \<epsilon> \<inter> D. \<forall>s\<in>ball t \<epsilon> \<inter> D. dist (\<phi> r) (\<phi> s) \<le> C * dist r s powr \<gamma>))"
  unfolding local_holder_on_def by (metis dist_commute Int_iff mem_ball)

lemma local_holder_on_altdef:
  assumes "D \<noteq> {}"
  shows "local_holder_on \<gamma> D \<phi> = (\<forall>t \<in> D. (\<exists>\<epsilon> > 0. (\<gamma>-holder_on ((cball t \<epsilon>) \<inter> D) \<phi>)))"
  unfolding local_holder_on_cball holder_on_def using assms by blast

lemma local_holder_on_cong[cong]:
  assumes "\<gamma> = \<epsilon>" "C = D" "\<And>x. x \<in> C \<Longrightarrow> \<phi> x = \<psi> x"
  shows "local_holder_on \<gamma> C \<phi> \<longleftrightarrow> local_holder_on \<epsilon> D \<psi>"
  unfolding local_holder_on_def using assms by presburger

lemma local_holder_onI:
  assumes "\<gamma> \<in> {0<..1}" "(\<forall>t\<in>D. \<exists>\<epsilon> > 0. \<exists>C \<ge> 0. (\<forall>r\<in>D. \<forall>s\<in>D. dist s t < \<epsilon> \<and> dist r t < \<epsilon> \<longrightarrow> dist (\<phi> r) (\<phi> s) \<le> C * dist r s powr \<gamma>))"
  shows "local_holder_on \<gamma> D \<phi>"
  using assms unfolding local_holder_on_def by blast

lemma local_holder_ballI:
  assumes "\<gamma> \<in> {0<..1}"
    and "\<And>t. t \<in> D \<Longrightarrow> \<exists>\<epsilon> > 0. \<exists>C \<ge> 0. \<forall>r\<in>ball t \<epsilon> \<inter> D. \<forall>s\<in>ball t \<epsilon> \<inter> D. 
                dist (\<phi> r) (\<phi> s) \<le> C * dist r s powr \<gamma>"
  shows "local_holder_on \<gamma> D \<phi>"
  using assms unfolding local_holder_on_ball by blast

lemma local_holder_onE:
  assumes local_holder: "local_holder_on \<gamma> D \<phi>"
    and gamma: "\<gamma> \<in> {0<..1}"
    and "t \<in> D"
  obtains \<epsilon> C where "\<epsilon> > 0" "C \<ge> 0" 
    "\<And>r s. r \<in> ball t \<epsilon> \<inter> D \<Longrightarrow> s \<in> ball t \<epsilon> \<inter> D \<Longrightarrow> dist (\<phi> r) (\<phi> s) \<le> C * dist r s powr \<gamma>"
  using assms unfolding local_holder_on_ball by auto

text \<open> Holder continuity matches up with the existing definitions in @{theory "HOL-Analysis.Lipschitz"}\<close>

lemma holder_1_eq_lipschitz: "1-holder_on D \<phi> = (\<exists>C. lipschitz_on C D \<phi>)"
  unfolding holder_on_def lipschitz_on_def by (auto simp: fun_eq_iff dist_commute)

lemma local_holder_1_eq_local_lipschitz: 
  assumes "T \<noteq> {}"
  shows "local_holder_on 1 D \<phi> = local_lipschitz T D (\<lambda>_. \<phi>)"
proof
  assume *: "local_holder_on 1 D \<phi>"
  {
    fix t assume "t \<in> D"
    then obtain \<epsilon> C where eC: "\<epsilon> > 0" "C \<ge> 0"
      "(\<forall>r\<in>D. \<forall>s\<in>D. dist s t \<le> \<epsilon> \<and> dist r t \<le> \<epsilon> \<longrightarrow> dist (\<phi> r) (\<phi> s) \<le> C * dist r s)"
      using * powr_to_1 unfolding local_holder_on_cball apply simp
      by (metis Int_iff dist_commute mem_cball)
    {
      fix r s assume rs: "r \<in> D" "s \<in> D" "dist s t \<le> \<epsilon> \<and> dist r t \<le> \<epsilon>"
      then have "r \<in> cball t \<epsilon> \<inter> D" "s\<in>cball t \<epsilon> \<inter> D" "dist (\<phi> r) (\<phi> s) \<le> C * dist r s"
        unfolding cball_def using rs eC by (auto simp: dist_commute)
    }
    then have "\<forall>r\<in>cball t \<epsilon> \<inter> D. \<forall>s\<in>cball t \<epsilon> \<inter> D. dist (\<phi> r) (\<phi> s) \<le> C * dist r s"
      by (simp add: dist_commute)
    then have "C-lipschitz_on ((cball t \<epsilon>) \<inter> D) \<phi>"
      using eC lipschitz_on_def by blast
    then have "\<exists>\<epsilon>>0. \<exists>C. C-lipschitz_on ((cball t \<epsilon>) \<inter> D) \<phi>"
      using eC(1) by blast
  }
  then show "local_lipschitz T D (\<lambda>_. \<phi>)"
    unfolding local_lipschitz_def by blast
next
  assume *: "local_lipschitz T D (\<lambda>_. \<phi>)"
  {
    fix x assume x: "x \<in> D"
    fix t assume t: "t \<in> T"
    then obtain u L where uL: "u > 0" "\<forall>t\<in>cball t u \<inter> T. L-lipschitz_on (cball x u \<inter> D) \<phi>"
      using * x t unfolding local_lipschitz_def by blast
    then have "L-lipschitz_on (cball x u \<inter> D) \<phi>"
      using t by force
    then have "1-holder_on (cball x u \<inter> D) \<phi>"
      using holder_1_eq_lipschitz by blast
    then have "\<exists>\<epsilon> > 0. (1-holder_on ((cball x \<epsilon>) \<inter> D) \<phi>)"
      using uL by blast
  }
  then have "x \<in> D \<Longrightarrow> \<exists>\<epsilon>>0. (1-holder_on (cball x \<epsilon> \<inter> D) \<phi>)" for x
    using assms by blast
  then show "local_holder_on 1 D \<phi>"
    unfolding local_holder_on_cball holder_on_def by (auto simp: dist_commute)
qed

lemma local_holder_refine:
  assumes g: "local_holder_on g D \<phi>" "g \<le> 1" 
    and  h: "h \<le> g" "h > 0"
  shows "local_holder_on h D \<phi>"
proof -
  {
    fix t assume t: "t \<in> D"
    then have "\<exists>\<epsilon>>0. \<exists>C\<ge>0. (\<forall>r\<in>D. \<forall>s\<in>D. dist s t \<le> \<epsilon> \<and> dist r t \<le> \<epsilon> \<longrightarrow> dist (\<phi> r) (\<phi> s) \<le> C * dist r s powr g)"
      using g(1) unfolding local_holder_on_leq_def by blast 
    then obtain \<epsilon> C where eC: "\<epsilon> > 0" "C \<ge> 0" 
      "(\<forall>s\<in>D. \<forall>r\<in>D. dist s t \<le> \<epsilon> \<and> dist r t \<le> \<epsilon> \<longrightarrow> dist (\<phi> r) (\<phi> s) \<le> C * dist r s powr g)"
      by blast
    let ?e = "min \<epsilon> (1/2)"
    {
      fix s r assume *: "s \<in> D" "r \<in> D" "dist s t \<le> ?e" "dist r t \<le> ?e"
      then have "dist (\<phi> r) (\<phi> s) \<le> C * dist r s powr g"
        using eC by simp
      moreover have "dist r s \<le> 1"
        by (smt (verit) * dist_triangle2 half_bounded_equal)
      ultimately have "dist (\<phi> r) (\<phi> s) \<le> C * dist r s powr h"
        by (metis dual_order.trans zero_le_dist powr_mono' assms(3) eC(2) mult_left_mono )
    }
    then have "(\<forall>s\<in>D. \<forall>r\<in>D. dist s t \<le> ?e \<and> dist r t \<le> ?e \<longrightarrow> dist (\<phi> r) (\<phi> s) \<le> C * dist r s powr h)"
      by blast
    moreover have "?e > 0" "C \<ge> 0"
      using eC by linarith+
    ultimately have "\<exists>\<epsilon>>0. \<exists>C\<ge>0. (\<forall>r\<in>D. \<forall>s\<in>D. dist s t \<le> \<epsilon> \<and> dist r t \<le> \<epsilon> \<longrightarrow> dist (\<phi> r) (\<phi> s) \<le> C * dist r s powr h)"
      by blast
  }
  then show ?thesis
    unfolding local_holder_on_leq_def using assms by force
qed

lemma holder_uniform_continuous:
  assumes "\<gamma>-holder_on X \<phi>"
  shows "uniformly_continuous_on X \<phi>"
  unfolding uniformly_continuous_on_def
proof safe
  fix e::real
  assume "0 < e"
  from assms obtain C where C: "C \<ge> 1" "(\<forall>r\<in>X. \<forall>s\<in>X. dist (\<phi> r) (\<phi> s) \<le> C * dist r s powr \<gamma>)"
    unfolding holder_on_def
    by (smt (verit) dist_eq_0_iff mult_le_cancel_right1 powr_0 powr_gt_zero)
  {
    fix r s assume "r \<in> X" "s \<in> X"
    have dist_0: "dist (\<phi> r) (\<phi> s) = 0 \<Longrightarrow> dist (\<phi> r) (\<phi> s) < e"
      using \<open>0 < e\<close> by linarith
    then have holder_neq_0: "dist (\<phi> r) (\<phi> s) < (C + 1) * dist r s powr \<gamma>" if "dist (\<phi> r) (\<phi> s) > 0"
      using C(2) that
      by (smt (verit, ccfv_SIG) \<open>r \<in> X\<close> \<open>s \<in> X\<close> dist_eq_0_iff mult_le_cancel_right powr_gt_zero)
    have gamma: "\<gamma> \<in> {0<..1}"
      using assms holder_on_def by blast+
    assume "dist r s < (e/C) powr (1 / \<gamma>)"
    then have "C * dist r s powr \<gamma> < C * ((e/C) powr (1 / \<gamma>)) powr \<gamma>" if "dist (\<phi> r) (\<phi> s) > 0"
      using holder_neq_0 C(1) powr_less_mono2 gamma by fastforce
    also have "... = e"
      using C(1) gamma \<open>0 < e\<close> powr_powr by auto
    finally have "dist (\<phi> r) (\<phi> s) < e"
      using dist_0 holder_neq_0 C(2) \<open>r \<in> X\<close> \<open>s \<in> X\<close> by fastforce
  }
  then show "\<exists>d>0. \<forall>x\<in>X. \<forall>x'\<in>X. dist x' x < d \<longrightarrow> dist (\<phi> x') (\<phi> x) < e"
    by (metis C(1) \<open>0 < e\<close> divide_eq_0_iff linorder_not_le order_less_irrefl powr_gt_zero zero_less_one)
qed

corollary holder_on_continuous_on: "\<gamma>-holder_on X \<phi> \<Longrightarrow> continuous_on X \<phi>"
  using holder_uniform_continuous uniformly_continuous_imp_continuous by blast


lemma holder_implies_local_holder: "\<gamma>-holder_on D \<phi> \<Longrightarrow> local_holder_on \<gamma> D \<phi>"
  apply (cases "D = {}")
   apply (simp add: holder_on_def local_holder_on_def)
  apply (simp add: local_holder_on_altdef holder_on_def)
  apply (metis IntD1 inf.commute)
  done

lemma local_holder_imp_continuous:
  assumes local_holder: "local_holder_on \<gamma> X \<phi>"
  shows "continuous_on X \<phi>"
  unfolding continuous_on_def
proof safe
  fix x assume "x \<in> X"
  {
    assume "X \<noteq> {}"
    from local_holder obtain \<epsilon> where "0 < \<epsilon>" and holder: "\<gamma>-holder_on ((cball x \<epsilon>) \<inter> X) \<phi>"
      unfolding local_holder_on_altdef[OF \<open>X \<noteq> {}\<close>] using \<open>x \<in> X\<close> by blast
    have "x \<in> ball x \<epsilon>" using \<open>0 < \<epsilon>\<close> by simp
    then have "(\<phi> \<longlongrightarrow> \<phi> x) (at x within cball x \<epsilon> \<inter> X)"
      using holder_on_continuous_on[OF holder] \<open>x \<in> X\<close> unfolding continuous_on_def by simp
    moreover have "\<forall>\<^sub>F xa in at x. (xa \<in> cball x \<epsilon> \<inter> X) = (xa \<in> X)"
      using eventually_at_ball[OF \<open>0 < \<epsilon>\<close>, of x UNIV]
      by eventually_elim auto
    ultimately have "(\<phi> \<longlongrightarrow> \<phi> x) (at x within X)"
      by (rule Lim_transform_within_set)
  }
  then show "(\<phi> \<longlongrightarrow> \<phi> x) (at x within X)"
    by fastforce
qed

lemma local_holder_compact_imp_holder:
  assumes "compact I" "local_holder_on \<gamma> I \<phi>"
  shows "\<gamma>-holder_on I \<phi>"
proof -
  have *: "\<gamma> \<in> {0<..1}" "(\<forall>t\<in>I. \<exists>\<epsilon>. \<exists>C. \<epsilon> > 0 \<and> C \<ge> 0 \<and> 
    (\<forall>r \<in> ball t \<epsilon> \<inter> I. \<forall>s \<in> ball t \<epsilon> \<inter> I. dist (\<phi> r) (\<phi> s) \<le> C * dist r s powr \<gamma>))"
    using assms(2) unfolding local_holder_on_ball by simp_all
  obtain \<epsilon> C where eC: "t \<in> I \<Longrightarrow> \<epsilon> t > 0 \<and> C t \<ge> 0 \<and> (\<forall>r \<in> ball t (\<epsilon> t) \<inter> I. \<forall>s \<in> ball t (\<epsilon> t) \<inter> I. dist (\<phi> r) (\<phi> s) \<le> C t * dist r s powr \<gamma>)" for t
    by (metis *(2))
  have "I \<subseteq> (\<Union>t \<in> I. ball t (\<epsilon> t))"
    apply (simp add: subset_iff)
    using eC by force
  then obtain D where D: "D \<subseteq> (\<lambda>t. ball t (\<epsilon> t)) ` I" "finite D" "I \<subseteq> \<Union> D"
    using compact_eq_Heine_Borel[of I] apply (simp add: assms(1))
    by (smt (verit, ccfv_SIG) open_ball imageE mem_Collect_eq subset_iff)
  then obtain T where T: "D = (\<lambda>t. ball t (\<epsilon> t)) ` T" "T \<subseteq> I" "finite T"
    by (meson finite_subset_image subset_image_iff)
  text \<open> $\varrho$ is the Lebesgue number of the cover \<close>
  from D obtain \<rho> :: real where \<rho>: "\<forall>t \<in> I. \<exists>U \<in> D. ball t \<rho> \<subseteq> U" "\<rho> > 0"
    by (smt (verit, del_insts) Elementary_Metric_Spaces.open_ball Heine_Borel_lemma assms(1) imageE subset_image_iff)
  have "bounded (\<phi> ` I)"
    by (metis compact_continuous_image compact_imp_bounded assms local_holder_imp_continuous)
  then obtain l where l: "\<forall>x \<in> I. \<forall>y \<in> I. dist (\<phi> x) (\<phi> y) \<le> l"
    by (metis bounded_two_points image_eqI)
  text \<open> Simply need to construct C\_bar such that it is greater than any of these \<close>
  define C_bar where "C_bar \<equiv> max ((\<Sum>t \<in> T. C t)) (l * \<rho> powr (- \<gamma>))"
  have C_bar_le: "C_bar \<ge> C t" if "t \<in> T" for t
  proof -
    have ge_0: "t \<in> T \<Longrightarrow> C t \<ge> 0" for t
      using T(2) eC by blast
    then have "\<Sum> (C ` (T - {t})) \<ge> 0"
      by (metis (mono_tags, lifting) Diff_subset imageE subset_eq sum_nonneg)
    then have "(\<Sum>t \<in> T. C t) \<ge> C t"
      by (metis T(3) ge_0 sum_nonneg_leq_bound that)
    then have "max ((\<Sum>t \<in> T. C t)) S \<ge> C t" for S
      by argo
    then show "C_bar \<ge> C t"
      unfolding C_bar_def by blast
  qed
  {
    fix s r assume sr: "s \<in> I" "r \<in> I"
    {
      assume "dist s r < \<rho>"
      then obtain t where t: "t \<in> T" "s \<in> ball t (\<epsilon> t)" "r \<in> ball t (\<epsilon> t)"
        by (smt (verit) sr D T \<rho> ball_eq_empty centre_in_ball imageE mem_ball subset_iff)
      then have "dist (\<phi> s) (\<phi> r) \<le> C t * dist s r powr \<gamma>"
        using eC[of t] T(2) sr by blast
      then have "dist (\<phi> s) (\<phi> r) \<le> C_bar * dist s r powr \<gamma>"
        by (smt (verit, best) t C_bar_le mult_right_mono powr_non_neg)
    } note le_rho = this
    {
      assume "dist s r \<ge> \<rho>"
      then have "dist (\<phi> s) (\<phi> r) \<le> l * (dist s r / \<rho>) powr \<gamma>"
      proof -
        have "(dist s r / \<rho>) \<ge> 1"
          using \<open>dist s r \<ge> \<rho>\<close> \<open>\<rho> > 0\<close> by auto
        then have "(dist s r / \<rho>) powr \<gamma> \<ge> 1"
          using "*"(1) ge_one_powr_ge_zero by auto
        then show "dist (\<phi> s) (\<phi> r) \<le> l * (dist s r / \<rho>) powr \<gamma>"
          using l
          by (metis dist_self linordered_nonzero_semiring_class.zero_le_one mult.right_neutral mult_mono sr(1) sr(2))
      qed
      also have "... \<le> C_bar * dist s r powr \<gamma>"
      proof -
        have "l * (dist s r / \<rho>) powr \<gamma> = l * \<rho> powr (- \<gamma>) * dist s r powr \<gamma> "
          using \<rho>(2) divide_powr_uminus powr_divide by force
        also have "... \<le> C_bar * dist s r powr \<gamma>"
          unfolding C_bar_def by (simp add: mult_right_mono)
        finally show "l * (dist s r / \<rho>) powr \<gamma> \<le> C_bar * dist s r powr \<gamma>"
          .
      qed
      finally have "dist (\<phi> s) (\<phi> r) \<le> C_bar * dist s r powr \<gamma>"
        .
    }
    then have "dist (\<phi> s) (\<phi> r) \<le> C_bar * dist s r powr \<gamma>"
      using le_rho by argo
  }
  then have "\<forall>r\<in>I. \<forall>s\<in>I. dist (\<phi> r) (\<phi> s) \<le> C_bar * dist r s powr \<gamma>"
    by simp
  then show ?thesis
    unfolding holder_on_def
    by (metis "*"(1) C_bar_def dist_self div_by_0 divide_nonneg_pos divide_powr_uminus 
        dual_order.trans l max.cobounded2 powr_0 powr_gt_zero)
qed

lemma holder_const: "\<gamma>-holder_on C (\<lambda>_. c) \<longleftrightarrow> \<gamma> \<in> {0<..1}"
  unfolding holder_on_def by auto

lemma local_holder_const: "local_holder_on \<gamma> C (\<lambda>_. c) \<longleftrightarrow> \<gamma> \<in> {0<..1}"
  using holder_const holder_implies_local_holder local_holder_on_def by blast

end
