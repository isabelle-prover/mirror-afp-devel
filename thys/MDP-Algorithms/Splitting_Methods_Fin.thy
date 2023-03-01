theory Splitting_Methods_Fin
  imports 
    "MDP-Rewards.Blinfun_Util" 
    MDP_fin
    Splitting_Methods
begin
subsection \<open>Util\<close>

definition upper_triangular_blin :: "('a::linorder \<Rightarrow>\<^sub>b real) \<Rightarrow>\<^sub>L ('a \<Rightarrow>\<^sub>b real) \<Rightarrow> bool" where 
  "upper_triangular_blin X \<longleftrightarrow> (\<forall>u v i. (\<forall>j \<ge> i. apply_bfun v j = apply_bfun u j) \<longrightarrow> X v i = X u i)"

definition strict_upper_triangular_blin :: "('a::linorder \<Rightarrow>\<^sub>b real) \<Rightarrow>\<^sub>L ('a \<Rightarrow>\<^sub>b real) \<Rightarrow> bool" where 
  "strict_upper_triangular_blin X \<longleftrightarrow> (\<forall>u v i. (\<forall>j > i. apply_bfun v j = apply_bfun u j) \<longrightarrow> X v i = X u i)"

lemma upper_triangularD:
  fixes X :: "('a::linorder \<Rightarrow>\<^sub>b real) \<Rightarrow>\<^sub>L ('a \<Rightarrow>\<^sub>b real)"
    and u v :: "'a \<Rightarrow>\<^sub>b real"
  assumes "upper_triangular_blin X" and "\<And>j. i \<le> j \<Longrightarrow> v j = u j"
  shows "X v i = X u i"
  using assms by (auto simp: upper_triangular_blin_def)

lemma upper_triangularI[intro]:
  fixes X :: "('a::linorder \<Rightarrow>\<^sub>b real) \<Rightarrow>\<^sub>L ('a \<Rightarrow>\<^sub>b real)"
  assumes "\<And>i u v. (\<And>j. i \<le> j \<Longrightarrow> apply_bfun v j = apply_bfun u j) \<Longrightarrow> X v i = X u i"
  shows "upper_triangular_blin X"
  using assms by (fastforce simp: upper_triangular_blin_def)

lemma strict_upper_triangularD:
  fixes X :: "('a::linorder \<Rightarrow>\<^sub>b real) \<Rightarrow>\<^sub>L ('a \<Rightarrow>\<^sub>b real)" and u v :: "'a \<Rightarrow>\<^sub>b real"
  assumes "strict_upper_triangular_blin X" and "\<And>j. i < j \<Longrightarrow> v j = u j"
  shows "X v i = X u i"
  using assms by (auto simp: strict_upper_triangular_blin_def)

lemma strict_imp_upper_triangular_blin: "strict_upper_triangular_blin X \<Longrightarrow> upper_triangular_blin X"
  unfolding strict_upper_triangular_blin_def upper_triangular_blin_def by auto

definition lower_triangular_blin :: "('a::linorder \<Rightarrow>\<^sub>b real) \<Rightarrow>\<^sub>L ('a \<Rightarrow>\<^sub>b real) \<Rightarrow> bool" where
  "lower_triangular_blin X \<longleftrightarrow> (\<forall>u v i. (\<forall>j \<le> i. apply_bfun v j = apply_bfun u j) \<longrightarrow> X v i = X u i)"

definition strict_lower_triangular_blin :: "('a::linorder \<Rightarrow>\<^sub>b real) \<Rightarrow>\<^sub>L ('a \<Rightarrow>\<^sub>b real) \<Rightarrow> bool" where
  "strict_lower_triangular_blin X \<longleftrightarrow> (\<forall>u v i. (\<forall>j < i. apply_bfun v j = apply_bfun u j) \<longrightarrow> X v i = X u i)"

lemma lower_triangularD:
  fixes X :: "('a::linorder \<Rightarrow>\<^sub>b real) \<Rightarrow>\<^sub>L ('a \<Rightarrow>\<^sub>b real)"
    and u v :: "'a \<Rightarrow>\<^sub>b real"
  assumes "lower_triangular_blin X" and "\<And>j. i \<ge> j \<Longrightarrow> v j = u j"
  shows "X v i = X u i" 
  using assms by (auto simp: lower_triangular_blin_def)

lemma lower_triangularI[intro]:
  fixes X :: "('a::linorder \<Rightarrow>\<^sub>b real) \<Rightarrow>\<^sub>L ('a \<Rightarrow>\<^sub>b real)"
  assumes "\<And>i u v. (\<And>j. i \<ge> j \<Longrightarrow> apply_bfun v j = apply_bfun u j) \<Longrightarrow> X v i = X u i"
  shows "lower_triangular_blin X"
  using assms by (fastforce simp: lower_triangular_blin_def)

lemma strict_lower_triangularI[intro]:
  fixes X :: "('a::linorder \<Rightarrow>\<^sub>b real) \<Rightarrow>\<^sub>L ('a \<Rightarrow>\<^sub>b real)"
  assumes "\<And>i u v. (\<And>j. i > j \<Longrightarrow> apply_bfun v j = apply_bfun u j) \<Longrightarrow> X v i = X u i"
  shows "strict_lower_triangular_blin X"
  using assms by (fastforce simp: strict_lower_triangular_blin_def)

lemma strict_lower_triangularD:
  fixes X :: "('a::linorder \<Rightarrow>\<^sub>b real) \<Rightarrow>\<^sub>L ('a \<Rightarrow>\<^sub>b real)"
    and u v :: "'a \<Rightarrow>\<^sub>b real"
  assumes "strict_lower_triangular_blin X" and "\<And>j. i > j \<Longrightarrow> v j = u j"
  shows "X v i = X u i"
  using assms by (auto simp: strict_lower_triangular_blin_def)

lemma strict_imp_lower_triangular_blin: "strict_lower_triangular_blin X \<Longrightarrow> lower_triangular_blin X"
  unfolding strict_lower_triangular_blin_def lower_triangular_blin_def
  by auto

lemma all_imp_Max:
  assumes "finite X" "X \<noteq> {}" "\<forall>x \<in> X. P (f x)" 
  shows "P (MAX x \<in> X. f x)"
proof -
  have "(MAX x \<in> X. f x) \<in> f ` X"
    using assms by auto
  thus ?thesis
    using assms by force
qed

lemma bounded_mult: 
  assumes "bounded ((f :: 'c \<Rightarrow> real) ` X)" "bounded (g ` X)"
  shows "bounded ((\<lambda>x. f x * g x) ` X)"
  using assms mult_mono
  by (fastforce simp: bounded_iff abs_mult intro!: mult_mono)

context MDP_nat_disc
begin

subsection \<open>Gauss Seidel Splitting\<close>

lemma \<P>\<^sub>1_det: "\<P>\<^sub>1 (mk_dec_det d) v s = measure_pmf.expectation (K (s, d s)) v"
  by (auto simp: mk_dec_det_def \<P>\<^sub>1.rep_eq K_st_def bind_return_pmf)

lift_definition \<P>\<^sub>U :: "(nat \<Rightarrow> nat) \<Rightarrow> (nat \<Rightarrow>\<^sub>b real) \<Rightarrow>\<^sub>L nat \<Rightarrow>\<^sub>b real" is "\<lambda>d (v :: nat \<Rightarrow>\<^sub>b real). 
  (Bfun (\<lambda>s. (\<P>\<^sub>1 (mk_dec_det d) (bfun_if (\<lambda>s'. s' < s) 0 v) s)))"
proof (standard, goal_cases)
  let ?vl = "\<lambda>v s. (bfun_if (\<lambda>s'. s' < s) 0 v)"
  have norm_bfun_if_le: "norm (?vl v s) \<le> norm v" for v :: "nat \<Rightarrow>\<^sub>b real" and s
    by (auto simp: norm_bfun_def' bfun_if.rep_eq intro!: cSUP_mono bounded_imp_bdd_above)
  hence is_bfun2: "(\<lambda>s. \<P>\<^sub>1 (mk_dec_det d) (?vl v s) s) \<in> bfun" for v :: "nat \<Rightarrow>\<^sub>b real" and d
    by (intro bfun_normI) (fastforce intro: order.trans[OF norm_blinfun] order.trans[OF norm_le_norm_bfun])
  case (1 d u v)
  have *: "\<P>\<^sub>1 (mk_dec_det d) (?vl (u + v) x) x = \<P>\<^sub>1 (mk_dec_det d) (?vl u x) x + \<P>\<^sub>1 (mk_dec_det d) (?vl v x) x " for x
    by (auto simp: bfun_if_zero_add blinfun.add_right)
  show ?case
    by (simp add: * eq_onp_same_args is_bfun2 plus_bfun.abs_eq)
  case (2 d r v)
  have "?vl (r *\<^sub>R v) x = r *\<^sub>R ?vl v x" for x
    by (auto simp: bfun_if.rep_eq)
  hence *: "r * \<P>\<^sub>1 (mk_dec_det d) (?vl v x) x = \<P>\<^sub>1 (mk_dec_det d) (?vl (r *\<^sub>R v) x) x" for x
    by (auto simp: blinfun.scaleR_right)
  show ?case
    using is_bfun2 by (auto simp: *)
  case (3 d)
  have [simp]: "(\<lambda>s. \<bar>apply_bfun x s\<bar>) \<in> bfun" for x :: "nat \<Rightarrow>\<^sub>b real"
    unfolding bfun_def by (auto intro!: boundedI abs_le_norm_bfun)
  have *: "\<bar>(\<P>\<^sub>1 (mk_dec_det d)) (?vl v n) n\<bar> \<le> \<P>\<^sub>1 (mk_dec_det d) (bfun.Bfun (\<lambda>s. \<bar>apply_bfun v s\<bar>)) n" for v n
    unfolding \<P>\<^sub>1_det
    by (subst Bfun_inverse)
      (auto simp: bfun_if.rep_eq abs_le_norm_bfun 
        intro!: order.trans[OF integral_abs_bound] integral_mono AE_pmfI measure_pmf.integrable_const_bound[of _ "norm v"])
  have "norm (bfun.Bfun (\<lambda>s. ((\<P>\<^sub>1 (mk_dec_det d)) (bfun_if (\<lambda>s'. s' < s) 0 x)) s)) \<le> norm x" for x
    by (fastforce simp: norm_bfun_def' Bfun_inverse[OF is_bfun2] 
        intro: cSUP_least order.trans[OF *[of _ x]] order.trans[OF le_norm_bfun] order.trans[OF norm_blinfun])
  thus ?case
    by (auto intro: exI[of _ 1])
qed

lift_definition \<P>\<^sub>L :: "(nat \<Rightarrow> nat) \<Rightarrow> (nat \<Rightarrow>\<^sub>b real) \<Rightarrow>\<^sub>L nat \<Rightarrow>\<^sub>b real" is "\<lambda>d (v :: nat \<Rightarrow>\<^sub>b real). 
  Bfun (\<lambda>s. (\<P>\<^sub>1 (mk_dec_det d) (bfun_if (\<lambda>s'. s' \<ge> s) 0 v) s))"
proof (standard, goal_cases)
  let ?vl = "\<lambda>v s. (bfun_if (\<lambda>s'. s' \<ge> s) 0 v)"
  have "norm (?vl v s) \<le> norm v" for v :: "nat \<Rightarrow>\<^sub>b real" and s
    by (auto simp: norm_bfun_def' bfun_if.rep_eq intro!: cSUP_mono bounded_imp_bdd_above)
  hence is_bfun2: "(\<lambda>s. \<P>\<^sub>1 (mk_dec_det d) (?vl v s) s) \<in> bfun" for v :: "nat \<Rightarrow>\<^sub>b real" and d
    by (intro bfun_normI) (fastforce intro: order.trans[OF norm_blinfun] order.trans[OF norm_le_norm_bfun])
  case (1 d u v)
  have *: "\<P>\<^sub>1 (mk_dec_det d) (?vl (u + v) x) x = \<P>\<^sub>1 (mk_dec_det d) (?vl u x) x + \<P>\<^sub>1 (mk_dec_det d) (?vl v x) x " for x
    by (auto simp: bfun_if_zero_add blinfun.add_right)
  show ?case
    by (simp add: * eq_onp_same_args is_bfun2 plus_bfun.abs_eq)
  case (2 d r v)
  have "?vl (r *\<^sub>R v) x = r *\<^sub>R ?vl v x" for x
    by (auto simp: bfun_if.rep_eq)
  hence *: "r * \<P>\<^sub>1 (mk_dec_det d) (?vl v x) x = \<P>\<^sub>1 (mk_dec_det d) (?vl (r *\<^sub>R v) x) x" for x
    by (auto simp: blinfun.scaleR_right)
  show ?case
    using is_bfun2 by (auto simp: *)
  case (3 d)
  have [simp]: "(\<lambda>s. \<bar>apply_bfun x s\<bar>) \<in> bfun" for x :: "nat \<Rightarrow>\<^sub>b real"
    unfolding bfun_def by (auto intro!: boundedI abs_le_norm_bfun)
  have *: "\<bar>(\<P>\<^sub>1 (mk_dec_det d)) (?vl v n) n\<bar> \<le> \<P>\<^sub>1 (mk_dec_det d) (bfun.Bfun (\<lambda>s. \<bar>apply_bfun v s\<bar>)) n" for v n
    unfolding \<P>\<^sub>1_det
    by (subst Bfun_inverse) (auto simp: bfun_if.rep_eq abs_le_norm_bfun 
        intro!: order.trans[OF integral_abs_bound] integral_mono AE_pmfI measure_pmf.integrable_const_bound[of _ "norm v"])
  have "norm (bfun.Bfun (\<lambda>s. ((\<P>\<^sub>1 (mk_dec_det d)) (bfun_if (\<lambda>s'. s' \<ge> s) 0 x)) s)) \<le> norm x" for x
    by (fastforce simp: norm_bfun_def' Bfun_inverse[OF is_bfun2] 
        intro!: cSUP_least order.trans[OF *[of _ x]] order.trans[OF le_norm_bfun] order.trans[OF norm_blinfun])
  thus ?case
    by (auto intro: exI[of _ 1])
qed

lemma is_bfun_\<P>_raw[simp]: 
  fixes v :: "nat \<Rightarrow>\<^sub>b real" and d
  shows "(\<lambda>s. \<P>\<^sub>1 (mk_dec_det d) (bfun_if (\<lambda>s'. s' \<ge> s) 0 v) s) \<in> bfun" (is ?t1)
    "(\<lambda>s. \<P>\<^sub>1 (mk_dec_det d) (bfun_if (\<lambda>s'. s' < s) 0 v) s) \<in> bfun" (is ?t2)
proof -
  have *: "norm ((bfun_if (\<lambda>s'. s' \<ge> s) 0 v)) \<le> norm v" "norm ((bfun_if (\<lambda>s'. s' < s) 0 v)) \<le> norm v" for v :: "nat \<Rightarrow>\<^sub>b real" and s
    by (auto simp: norm_bfun_def' bfun_if.rep_eq intro!: cSUP_mono bounded_imp_bdd_above)
  thus ?t1 ?t2
    by (fastforce intro!: bfun_normI order.trans[OF norm_blinfun] order.trans[OF norm_le_norm_bfun])+
qed

lemma \<P>\<^sub>U_rep_eq': "\<P>\<^sub>U d v s = \<P>\<^sub>1 (mk_dec_det d) (bfun_if ((>) s) 0 v) s"
  by (auto simp: \<P>\<^sub>U.rep_eq)

lemma \<P>\<^sub>L_rep_eq': "\<P>\<^sub>L d v s = \<P>\<^sub>1 (mk_dec_det d) (bfun_if ((\<le>) s) 0 v) s"
  by (auto simp: \<P>\<^sub>L.rep_eq)

lemma apply_bfun_plus: "apply_bfun f a + apply_bfun g a = apply_bfun (f + g) a"
  by auto

lemma \<P>\<^sub>1_sum_lower_upper: "\<P>\<^sub>1 (mk_dec_det d) = \<P>\<^sub>L d + \<P>\<^sub>U d"
proof -
  have bfun_if_sum: "bfun_if ((\<le>) s) 0 v + bfun_if (\<lambda>s'. s' < s) 0 v = v" for s and v :: "nat \<Rightarrow>\<^sub>b real"
    by (auto simp: bfun_if.rep_eq)
  show ?thesis
    by (fastforce intro: blinfun_eqI simp: blinfun.add_left \<P>\<^sub>L_rep_eq' \<P>\<^sub>U_rep_eq' apply_bfun_plus blinfun.add_right[symmetric] bfun_if_sum)
qed

lemma nonneg_\<P>\<^sub>U: "nonneg_blinfun (\<P>\<^sub>U d)"
  using \<P>\<^sub>1_nonneg is_bfun_\<P>_raw 
  by (auto simp: nonneg_blinfun_def \<P>\<^sub>U.rep_eq bfun_if.rep_eq less_eq_bfun_def)

lemma nonneg_\<P>\<^sub>L: "nonneg_blinfun (\<P>\<^sub>L d)"
  using \<P>\<^sub>1_nonneg is_bfun_\<P>_raw 
  by (auto simp: nonneg_blinfun_def \<P>\<^sub>L.rep_eq bfun_if.rep_eq less_eq_bfun_def)

lemma norm_\<P>\<^sub>L_le: "norm (\<P>\<^sub>L d) \<le> norm (\<P>\<^sub>1 (mk_dec_det d))"
  using nonneg_\<P>\<^sub>L \<P>\<^sub>1_mono
  by (fastforce intro!: matrix_le_norm_mono simp: bfun_if.rep_eq nonneg_blinfun_def blinfun.diff_left \<P>\<^sub>L.rep_eq less_eq_bfun_def)

lemma norm_\<P>\<^sub>U_le: "norm (\<P>\<^sub>U d) \<le> norm (\<P>\<^sub>1 (mk_dec_det d))"
  using nonneg_\<P>\<^sub>U \<P>\<^sub>1_mono
  by (fastforce intro!: matrix_le_norm_mono simp: bfun_if.rep_eq nonneg_blinfun_def blinfun.diff_left \<P>\<^sub>U.rep_eq less_eq_bfun_def)

lemma norm_\<P>\<^sub>L_le_one: "norm (\<P>\<^sub>L d) \<le> 1"
  using norm_\<P>\<^sub>L_le norm_\<P>\<^sub>1 by auto

lemma norm_\<P>\<^sub>U_le_one: "norm (\<P>\<^sub>U d) \<le> 1"
  using norm_\<P>\<^sub>U_le norm_\<P>\<^sub>1 by auto

lemma norm_\<P>\<^sub>L_less_one: "norm (l *\<^sub>R \<P>\<^sub>L d) < 1"
  using order.strict_trans1[OF mult_left_le disc_lt_one] zero_le_disc norm_\<P>\<^sub>L_le_one
  by auto

lemma norm_\<P>\<^sub>U_less_one: "norm (l *\<^sub>R \<P>\<^sub>U d) < 1"
  using order.strict_trans1[OF mult_left_le disc_lt_one] zero_le_disc norm_\<P>\<^sub>U_le_one
  by auto

lemma \<P>\<^sub>L_le_\<P>\<^sub>1: "0 \<le> v \<Longrightarrow> \<P>\<^sub>L d v \<le> \<P>\<^sub>1 (mk_dec_det d) v"
  using \<P>\<^sub>1_mono
  by (auto simp: bfun_if.rep_eq \<P>\<^sub>L_rep_eq' less_eq_bfun_def intro!:)

lemma \<P>\<^sub>U_le_\<P>\<^sub>1: "0 \<le> v \<Longrightarrow> \<P>\<^sub>U d v \<le> \<P>\<^sub>1 (mk_dec_det d) v"
  using \<P>\<^sub>1_mono
  by (auto simp: bfun_if.rep_eq \<P>\<^sub>U_rep_eq' less_eq_bfun_def intro!:)

lemma \<P>\<^sub>U_indep: "d s = d' s \<Longrightarrow> \<P>\<^sub>U d v s = \<P>\<^sub>U d' v s"
  unfolding \<P>\<^sub>U_rep_eq' \<P>\<^sub>1_det by simp
lemma \<P>\<^sub>L_indep: "d s = d' s \<Longrightarrow> \<P>\<^sub>L d v s = \<P>\<^sub>L d' v s"
  unfolding \<P>\<^sub>L_rep_eq' \<P>\<^sub>1_det by simp

lemma \<P>\<^sub>U_indep2: 
  assumes "d s = d' s" "(\<And>s'. s' \<ge> s \<Longrightarrow> apply_bfun v s' = apply_bfun v' s')" 
  shows "\<P>\<^sub>U d v s = \<P>\<^sub>U d' v' s"
  using assms by (auto simp: \<P>\<^sub>U_rep_eq' \<P>\<^sub>1_det bfun_if.rep_eq cong: if_cong)

lemma \<P>\<^sub>L_indep2: "d s = d' s \<Longrightarrow> (\<And>s'. s' < s \<Longrightarrow> apply_bfun v s' = apply_bfun v' s') \<Longrightarrow> \<P>\<^sub>L d v s = \<P>\<^sub>L d' v' s"
  by (auto simp: \<P>\<^sub>L_rep_eq' \<P>\<^sub>1_det bfun_if.rep_eq cong: if_cong)

lemma \<P>\<^sub>1_indep: "d s = d' s \<Longrightarrow> \<P>\<^sub>1 d v s = \<P>\<^sub>1 d' v s"
  by (simp add: K_st_def \<P>\<^sub>1.rep_eq)

lemma \<P>\<^sub>U_upper: "upper_triangular_blin (\<P>\<^sub>U d)"
  using \<P>\<^sub>U_indep2 by fastforce

lemma \<P>\<^sub>L_strict_lower: "strict_lower_triangular_blin (\<P>\<^sub>L d)"
  using \<P>\<^sub>L_indep2 by fastforce

definition "Q_GS d = id_blinfun - l *\<^sub>R \<P>\<^sub>L d"
definition "R_GS d = l *\<^sub>R \<P>\<^sub>U d"

lemma nonneg_R_GS: "nonneg_blinfun (R_GS d)"
  by (simp add: R_GS_def nonneg_\<P>\<^sub>U nonneg_blinfun_scaleR)

lemma splitting_gauss: "is_splitting_blin (id_blinfun - l *\<^sub>R \<P>\<^sub>1 (mk_dec_det d)) (Q_GS d) (R_GS d)"
  unfolding is_splitting_blin_def
proof safe
  show "nonneg_blinfun (R_GS d)"
    using nonneg_R_GS.
next
  show "id_blinfun - l *\<^sub>R \<P>\<^sub>1 (mk_dec_det d) = Q_GS d - R_GS d"
    using \<P>\<^sub>1_sum_lower_upper
    unfolding Q_GS_def R_GS_def
    by (auto simp: algebra_simps scaleR_add_right[symmetric] simp del: scaleR_add_right)
next
  have n_le: "norm (l *\<^sub>R \<P>\<^sub>L d) < 1"
    using mult_left_le[OF norm_\<P>\<^sub>L_le_one[of d] zero_le_disc] order.strict_trans1
    by (auto intro: disc_lt_one)
  thus "invertible\<^sub>L (Q_GS d)"
    by (simp add: Q_GS_def invertible\<^sub>L_inf_sum)
  have "inv\<^sub>L (Q_GS d) = (\<Sum>i. (l *\<^sub>R \<P>\<^sub>L d) ^^ i)"
    using inv\<^sub>L_inf_sum n_le unfolding Q_GS_def by blast
  have "nonneg_blinfun (R_GS d ^^ i)" for i
    using nonneg_R_GS by (auto simp: nonneg_blinfun_def intro: blinfunpow_nonneg)
  have s: "summable (\<lambda>k. ((l *\<^sub>R \<P>\<^sub>L d)^^k))"
    using summable_inv_Q[of "Q_GS d"] norm_\<P>\<^sub>L_less_one
    by (simp add: Q_GS_def algebra_simps blinfun.scaleR_left blincomp_scaleR_right)
  hence s': "summable (\<lambda>k. ((l *\<^sub>R \<P>\<^sub>L d)^^k) v)" for v
    using tendsto_blinfun_apply
    by (auto simp: summable_def sums_def blinfun.sum_left[symmetric])
  hence s'': "summable (\<lambda>k. ((l *\<^sub>R \<P>\<^sub>L d)^^k) v s)" for v s
    by (fastforce simp: summable_def sums_def sum_apply_bfun[symmetric] intro: bfun_tendsto_apply_bfun)
  have "0 \<le> (\<Sum>k. ((l *\<^sub>R \<P>\<^sub>L d)^^k) v s)" if "v \<ge> 0" for v s
    by (rule suminf_nonneg[OF s''])
      (metis blinfunpow_nonneg that less_eq_bfun_def nonneg_\<P>\<^sub>L nonneg_blinfun_nonneg nonneg_blinfun_scaleR zero_bfun.rep_eq zero_le_disc)
  hence "0 \<le> (\<Sum>k. ((l *\<^sub>R \<P>\<^sub>L d)^^k) v)" if "v \<ge> 0" for v
    using that unfolding less_eq_bfun_def suminf_apply_bfun[OF s'] by auto
  hence "nonneg_blinfun (\<Sum>k. ((l *\<^sub>R \<P>\<^sub>L d)^^k))"
    unfolding nonneg_blinfun_def by (simp add: blinfun_apply_suminf s)
  thus "nonneg_blinfun (inv\<^sub>L (Q_GS d))"
    by (simp add: \<open>inv\<^sub>L (Q_GS d) = (\<Sum>i. (l *\<^sub>R \<P>\<^sub>L d) ^^ i)\<close>)
qed

abbreviation "r_det\<^sub>b d \<equiv> r_dec\<^sub>b (mk_dec_det d)"

definition "GS_inv d v = inv\<^sub>L (Q_GS d) (r_dec\<^sub>b (mk_dec_det d) + R_GS d v)"

text \<open>@{term Q_GS} can be expressed as an infinite sum of @{const \<P>\<^sub>L}.\<close>

lemma inv_Q_suminf: "inv\<^sub>L (Q_GS d) = (\<Sum>k. (l *\<^sub>R (\<P>\<^sub>L d)) ^^ k)"
  unfolding Q_GS_def using inv\<^sub>L_inf_sum norm_\<P>\<^sub>L_less_one by blast

text \<open>This recursive definition mimics the computation of the GS iteration.\<close>
lemma GS_inv_rec: "GS_inv d v = r_det\<^sub>b d + l *\<^sub>R (\<P>\<^sub>U d v + \<P>\<^sub>L d (GS_inv d v))"
proof -
  have "Q_GS d (GS_inv d v) = r_det\<^sub>b d + R_GS d v"
    using splitting_gauss[of d] unfolding GS_inv_def is_splitting_blin_def by simp
  thus ?thesis
    unfolding R_GS_def Q_GS_def by (auto simp: algebra_simps blinfun.diff_left blinfun.scaleR_left)
qed

text \<open>As a result, also @{term GS_inv} is independent of lower actions.\<close>
lemma GS_indep_high_states:
  assumes "\<And>s'. s' \<le> s \<Longrightarrow> d s' = d' s'"
  shows "GS_inv d v s = GS_inv d' v s"
  using assms
proof (induction s arbitrary: d d' v rule: less_induct)
  case (less x)
  have "r_det\<^sub>b d x = r_det\<^sub>b d' x"
    by (simp add: less.prems)
  moreover have "\<P>\<^sub>U d v x = \<P>\<^sub>U d' v x"    
    by (meson \<P>\<^sub>U_indep le_refl less.prems)
  moreover have "\<P>\<^sub>L d (GS_inv d v) x = \<P>\<^sub>L d' (GS_inv d' v) x"
    using \<P>\<^sub>L_indep2 less.IH less.prems by fastforce
  ultimately show ?case
    by (subst GS_inv_rec[of d], subst GS_inv_rec[of d']) auto
qed

lemma is_am_GS_inv_extend:
  assumes "\<And>s. s < k \<Longrightarrow> is_arg_max (\<lambda>d. GS_inv d v s) (\<lambda>d. d \<in> D\<^sub>D) d"
    and "is_arg_max (\<lambda>a. GS_inv (d (k := a)) v k) (\<lambda>a. a \<in> A k) a"
    and "s \<le> k"
    and "d \<in> D\<^sub>D"
  shows "is_arg_max (\<lambda>d. GS_inv d v s) (\<lambda>d. d \<in> D\<^sub>D) (d (k := a))"
proof -
  have "is_arg_max (\<lambda>d. GS_inv d v k) (\<lambda>d. d \<in> D\<^sub>D) (d (k := a))"
  proof (rule is_arg_max_linorderI)
    fix y
    assume "y \<in> D\<^sub>D"
    let ?d = "d(k := y k)"   
    have "GS_inv y v k \<le> GS_inv ?d v k"
    proof -
      have "\<P>\<^sub>L y (GS_inv y v) k = (\<P>\<^sub>L ?d (GS_inv y v)) k"
        by (auto intro!: \<P>\<^sub>L_indep2 GS_indep_high_states)
      also have "\<dots> \<le> (\<P>\<^sub>L ?d (bfun_if (\<lambda>s. s < k) (GS_inv d v) (GS_inv y v))) k"
        using assms(1) \<open>y \<in> D\<^sub>D\<close>
        by (fastforce intro!: nonneg_blinfun_mono[THEN less_eq_bfunD] simp: bfun_if.rep_eq less_eq_bfun_def nonneg_\<P>\<^sub>L)
      also have "\<dots> = (\<P>\<^sub>L ?d (GS_inv d v)) k"
        by (metis (no_types, lifting) \<P>\<^sub>L_strict_lower bfun_if.rep_eq strict_lower_triangularD)
      also have "\<dots> = \<P>\<^sub>L ?d (GS_inv ?d v) k"
        using GS_indep_high_states \<P>\<^sub>L_strict_lower
        by (fastforce intro: strict_lower_triangularD[OF \<P>\<^sub>L_strict_lower])
      finally have "\<P>\<^sub>L y (GS_inv y v) k \<le> \<P>\<^sub>L ?d (GS_inv ?d v) k".
      thus ?thesis
        by (subst GS_inv_rec[of y], subst GS_inv_rec[of ?d])
          (auto simp: \<P>\<^sub>U_indep[of y _ ?d] intro!: mult_left_mono)
    qed
    thus "GS_inv y v k \<le> GS_inv (d(k := a)) v k"
      using is_arg_max_linorderD[OF assms(2)] \<open>y \<in> D\<^sub>D\<close> is_dec_det_def by fastforce
  next
    show "d(k := a) \<in> D\<^sub>D"
      using assms by (auto simp: is_dec_det_def is_arg_max_linorder)
  qed
  thus ?thesis
    using assms GS_indep_high_states[of s "d (k := a)" d] by (cases "s < k") fastforce+
qed

lemma is_am_GS_inv_extend':
  assumes "\<And>s. s < k \<Longrightarrow> is_arg_max (\<lambda>d. GS_inv d v s) (\<lambda>d. d \<in> D\<^sub>D) d"
    and "is_arg_max (\<lambda>a. GS_inv (d (k := a)) v k) (\<lambda>a. a \<in> A k) (d k)"
    and "s \<le> k"
    and "d \<in> D\<^sub>D"
  shows "is_arg_max (\<lambda>d. GS_inv d v s) (\<lambda>d. d \<in> D\<^sub>D) d"
  using assms is_am_GS_inv_extend[of k _ d  "d k"] by auto

lemma norm_\<P>\<^sub>L_pow: "norm ((\<Sum>k. (l *\<^sub>R \<P>\<^sub>L d) ^^ k)) \<le> 1 / (1-l)"
  by (fastforce simp: norm_\<P>\<^sub>L_le_one mult_left_le power_mono suminf_geometric
      intro: order.trans[OF summable_norm] summable_comparison_test'[of "\<lambda>n :: nat. l ^ n" 0] 
      order.trans[OF suminf_le[of _ "\<lambda>n. l^n"]] order.trans[OF norm_blinfunpow_le])

lemma summable_disc_\<P>\<^sub>L: "summable (\<lambda>i. ((l *\<^sub>R \<P>\<^sub>L d)^^i))"
  by (metis add_diff_cancel_left' diff_add_cancel norm_\<P>\<^sub>L_less_one summable_inv_Q)

lemma norm_\<P>\<^sub>L_pow_elem: "norm ((\<Sum>k. (l *\<^sub>R \<P>\<^sub>L d) ^^ k) v) \<le> norm v / (1-l)"
  using norm_\<P>\<^sub>L_le_one 
  by (subst blinfun_apply_suminf[symmetric, OF summable_disc_\<P>\<^sub>L]) 
    (auto simp: blincomp_scaleR_right blinfun.scaleR_left intro!: power_le_one sum_disc_bound' 
      order.trans[OF norm_blinfunpow_le] order.trans[OF norm_blinfun] mult_left_le_one_le)

lemma norm_Q_GS: "norm (inv\<^sub>L (Q_GS d) v) \<le> norm v / (1-l)"
  using inv_Q_suminf norm_\<P>\<^sub>L_pow_elem by auto

lemma norm_GS_inv_le: "norm (GS_inv d v) \<le> (r\<^sub>M + l * norm v) / (1 - l)"
proof -
  have "0 < (1 - l)"
    using disc_lt_one by auto
  thus ?thesis
    unfolding GS_inv_def inv_Q_suminf R_GS_def
    using norm_r_dec_le norm_\<P>\<^sub>U_le_one order.strict_implies_order[OF disc_lt_one]
    by (intro order.trans[OF norm_\<P>\<^sub>L_pow_elem]) 
      (auto simp: blinfun.scaleR_left intro!: mult_left_le_one_le order.trans[OF norm_blinfun] mult_left_mono divide_right_mono order.trans[OF norm_triangle_ineq] add_mono)
qed


lemma GS_inv_elem_eq: "GS_inv d v s = (r_det\<^sub>b d + l *\<^sub>R (\<P>\<^sub>1 (mk_dec_det d) (bfun_if (\<lambda>s'. s \<le> s') v (GS_inv d v)))) s"
proof -
  have "bfun_if (\<lambda>s'. s' < s) 0 v + bfun_if ((\<le>) s) 0 (GS_inv d v) = bfun_if ((\<le>) s) v (GS_inv d v)" 
    by (auto simp: bfun_if.rep_eq)
  thus ?thesis
    by (subst GS_inv_rec) (auto simp: \<P>\<^sub>U_rep_eq' \<P>\<^sub>L_rep_eq' apply_bfun_plus blinfun.add_right[symmetric])
qed

subsection \<open>Maximizing Decision Rule for GS\<close>
lemma ex_GS_inv_arg_max: "\<exists>a. is_arg_max (\<lambda>a. GS_inv (d(s:= a)) v s) (\<lambda>a. a \<in> A s) a"
proof -
  have "\<exists>a. is_arg_max (\<lambda>a. (r_det\<^sub>b (d(s := a)) + l *\<^sub>R (\<P>\<^sub>1 (mk_dec_det (d(s := a))) (bfun_if (\<lambda>s'. s \<le> s') v (GS_inv d v)))) s) (\<lambda>a. a \<in> A s) a"
    using Sup_att by (auto simp: \<P>\<^sub>1_det max_L_ex_def has_arg_max_def)
  moreover have"(bfun_if (\<lambda>s'. s \<le> s') v (GS_inv (d(s := a)) v)) = (bfun_if (\<lambda>s'. s \<le> s') v (GS_inv d v))" for a
    using GS_indep_high_states by (fastforce simp: bfun_if.rep_eq)
  ultimately show ?thesis
    by (auto simp: GS_inv_elem_eq)
qed

text \<open>This shows that there always exists a decision rule that maximized @{const GS_inv} for all states simultaneously.\<close>
abbreviation "some_dec \<equiv> (SOME d. d \<in> D\<^sub>D)"

fun d_GS_least :: "(nat \<Rightarrow>\<^sub>b real) \<Rightarrow> nat \<Rightarrow> nat" where
  "d_GS_least v (0::nat) = (LEAST a. is_arg_max (\<lambda>a. GS_inv (some_dec(0 := a)) v 0) (\<lambda>a. a \<in> A 0) a)" |
  "d_GS_least v (Suc n) =  (LEAST a. is_arg_max (\<lambda>a. GS_inv ((\<lambda>s. if s < Suc n then d_GS_least v s else SOME a. a \<in> A s)(Suc n:= a)) v (Suc n)) (\<lambda>a. a \<in> A (Suc n)) a)"

lemma d_GS_least_is_dec: "d_GS_least v \<in> D\<^sub>D"
  unfolding is_dec_det_def
proof safe
  fix s
  show "d_GS_least v s \<in> A s"
    using LeastI_ex[OF ex_GS_inv_arg_max] by (cases s) auto
qed

lemma d_GS_least_eq: "d_GS_least v n = (LEAST a. is_arg_max (\<lambda>a. GS_inv ((d_GS_least v)(n := a)) v n) (\<lambda>a. a \<in> A n) a)"
proof (induction n)
  case 0
  have aux: "apply_bfun (GS_inv ((d_GS_least v)(0 := a)) v) 0 = GS_inv (some_dec(0 := a)) v 0" for a
    by (auto intro: GS_indep_high_states)
  show ?case
    unfolding aux by auto
next
  case (Suc n)
  have aux: "GS_inv ((\<lambda>s. if s < Suc n then d_GS_least v s else SOME a. a \<in> A s)(Suc n := a)) v (Suc n) = 
      (GS_inv ((d_GS_least v)(Suc n := a)) v) (Suc n)" for a
    using GS_indep_high_states by fastforce
  show ?case
    unfolding aux[symmetric] by simp
qed

lemma d_GS_least_is_arg_max: "is_arg_max (\<lambda>d. GS_inv d v s) (\<lambda>d. d \<in> D\<^sub>D) (d_GS_least v)"
proof (induction s rule: nat_less_induct)
  case (1 n)
  assume "\<forall>m<n. is_arg_max (\<lambda>d. apply_bfun (GS_inv d v) m) (\<lambda>d. d \<in> D\<^sub>D) (d_GS_least v)"
  show ?case
    using is_am_GS_inv_extend'[of n _ "(d_GS_least v)"] 1 d_GS_least_is_dec 
    by (fastforce simp: ex_GS_inv_arg_max d_GS_least_eq[of v n] LeastI_ex)
qed

subsection \<open>Gauss-Seidel is a Valid Regular Splitting\<close>

lemma norm_GS_QR_le_disc: "norm (inv\<^sub>L (Q_GS d) o\<^sub>L R_GS d) \<le> l"
proof -
  have "norm (inv\<^sub>L (Q_GS d) o\<^sub>L R_GS d) \<le> norm (inv\<^sub>L ((\<lambda>_. id_blinfun) d) o\<^sub>L (l *\<^sub>R \<P>\<^sub>1 (mk_dec_det d))) "
  proof (rule norm_splitting_le[of "mk_dec_det d"], goal_cases)
    case 1
    then show ?case 
      unfolding is_splitting_blin_def nonneg_blinfun_def
      by (auto simp: \<P>\<^sub>1_pos blinfun.scaleR_left scaleR_nonneg_nonneg)
  next
    case 3
    then show ?case 
      by (simp add: R_GS_def \<P>\<^sub>U_le_\<P>\<^sub>1 blinfun_le_iff scaleR_blinfun.rep_eq scaleR_left_mono)
  qed (auto simp: splitting_gauss blinfun_le_iff)
  also have "\<dots> \<le> l"
    by auto
  finally show ?thesis.
qed

lemma ex_GS_arg_max_all: "\<exists>d. is_arg_max (\<lambda>d. GS_inv d v s) (\<lambda>d. d \<in> D\<^sub>D) d"
  using d_GS_least_is_arg_max by blast

sublocale GS: MDP_QR A K r l Q_GS R_GS
proof -
  have "(\<Squnion>d\<in>D\<^sub>D. norm (inv\<^sub>L (Q_GS d) o\<^sub>L R_GS d)) < 1"
    using norm_GS_QR_le_disc ex_dec_det
    by (fastforce intro: le_less_trans[of _ l 1] intro!: cSUP_least)
  thus "MDP_QR A K r l Q_GS R_GS"
    using norm_GS_QR_le_disc norm_\<P>\<^sub>L_pow d_GS_least_is_arg_max
    by unfold_locales (fastforce intro!: bdd_above.I2 simp: splitting_gauss bounded_iff inv_Q_suminf GS_inv_def)+
qed

subsection \<open>Termination\<close>
lemma dist_\<L>\<^sub>b_split_lt_dist_opt: "dist v (GS.\<L>\<^sub>b_split v) \<le> 2 * dist v \<nu>\<^sub>b_opt"
proof -
  have le1: "dist v (GS.\<L>\<^sub>b_split v) \<le> dist v \<nu>\<^sub>b_opt + dist (GS.\<L>\<^sub>b_split v) \<nu>\<^sub>b_opt"
    by (simp add: dist_triangle dist_commute)
  have le2: "dist (GS.\<L>\<^sub>b_split v) \<nu>\<^sub>b_opt \<le> GS.QR_disc * dist v \<nu>\<^sub>b_opt"
    using GS.\<L>\<^sub>b_split_contraction GS.\<L>\<^sub>b_split_fix by (metis (no_types, lifting))
  show ?thesis
    using mult_right_mono[of GS.QR_disc 1] GS.QR_contraction
    by (fastforce intro!: order.trans[OF le2] order.trans[OF le1])
qed

lemma GS_QR_disc_le_disc: "GS.QR_disc \<le> l"
  using norm_GS_QR_le_disc ex_dec_det by (fastforce intro!: cSUP_least)

text \<open>
The distance between an estimate for the value and the optimal value can be bounded with respect to 
the distance between the estimate and the result of applying it to @{const \<L>\<^sub>b}
\<close>

lemma gs_rel_dec: 
  assumes "l \<noteq> 0" "GS.\<L>\<^sub>b_split v \<noteq> \<nu>\<^sub>b_opt"
  shows "\<lceil>log (1 / l) (dist (GS.\<L>\<^sub>b_split v) \<nu>\<^sub>b_opt) - c\<rceil> < \<lceil>log (1 / l) (dist v \<nu>\<^sub>b_opt) - c\<rceil>"
proof -
  have "log (1 / l) (dist (GS.\<L>\<^sub>b_split v) \<nu>\<^sub>b_opt) - c \<le> log (1 / l) (l * dist v \<nu>\<^sub>b_opt) - c"
    using GS.\<L>\<^sub>b_split_contraction[of _ "\<nu>\<^sub>b_opt"] GS.QR_contraction norm_GS_QR_le_disc disc_lt_one GS_QR_disc_le_disc
    by (fastforce simp: assms less_le intro!: log_le order.trans[OF GS.\<L>\<^sub>b_split_contraction[of v "\<nu>\<^sub>b_opt", simplified]] mult_right_mono)
  also have "\<dots> = log (1 / l) l + log (1/l) (dist v \<nu>\<^sub>b_opt) - c"
    using assms disc_lt_one by (auto simp: less_le intro!: log_mult)
  also have "\<dots> = -(log (1 / l) (1/l)) + (log (1/l) (dist v \<nu>\<^sub>b_opt)) - c"
    using assms disc_lt_one
    by (subst log_inverse[symmetric]) (auto simp: less_le right_inverse_eq)
  also have "\<dots> = (log (1/l) (dist v \<nu>\<^sub>b_opt)) - 1 - c"
    using assms order.strict_implies_not_eq[OF disc_lt_one]
    by (auto intro!: log_eq_one neq_le_trans)
  finally have "log (1 / l) (dist (GS.\<L>\<^sub>b_split v) \<nu>\<^sub>b_opt) - c \<le> log (1 / l) (dist v \<nu>\<^sub>b_opt) - 1 - c" .
  thus ?thesis
    by linarith
qed

abbreviation "gs_measure \<equiv> (\<lambda>(eps, v).
    if v = \<nu>\<^sub>b_opt \<or> l = 0
    then 0
    else nat (ceiling (log (1/l) (dist v \<nu>\<^sub>b_opt) - log (1/l) (eps * (1-l) / (8 * l)))))"

function gs_iteration :: "real \<Rightarrow> (nat \<Rightarrow>\<^sub>b real) \<Rightarrow> (nat \<Rightarrow>\<^sub>b real)" where
  "gs_iteration eps v =
  (if 2 * l * dist v (GS.\<L>\<^sub>b_split v) < eps * (1 - l) \<or> eps \<le> 0 then GS.\<L>\<^sub>b_split v else gs_iteration eps (GS.\<L>\<^sub>b_split v))"
  by auto
termination
proof (relation "Wellfounded.measure gs_measure"; cases "l = 0")
  case False
  fix eps v
  assume h: "\<not> (2 * l * dist v (GS.\<L>\<^sub>b_split v) < eps * (1 - l) \<or> eps \<le> 0)"
  show "((eps, GS.\<L>\<^sub>b_split v), eps, v) \<in> Wellfounded.measure gs_measure"
  proof -
    have gt_zero[simp]: "l \<noteq> 0" "eps > 0" and dist_ge: "eps * (1 - l) \<le> dist v (GS.\<L>\<^sub>b_split v) * (2 * l)"
      using h by (auto simp: algebra_simps)
    have v_not_opt: "v \<noteq> \<nu>\<^sub>b_opt"
      using h by auto
    have "log (1 / l) (eps * (1 - l) / (8 * l)) < log (1 / l) (dist v \<nu>\<^sub>b_opt)"
    proof (intro log_less)
      show "1 < 1 / l"
        by (auto intro!: mult_imp_less_div_pos intro: neq_le_trans)
      show "0 < eps * (1 - l) / (8 * l)" 
        by (auto intro!: mult_imp_less_div_pos intro: neq_le_trans)
      show "eps * (1 - l) / (8 * l) < dist v \<nu>\<^sub>b_opt" 
        using dist_pos_lt[OF v_not_opt] dist_\<L>\<^sub>b_split_lt_dist_opt[of v] gt_zero zero_le_disc mult_strict_left_mono[of "dist v (GS.\<L>\<^sub>b_split v)" "(4 * dist v \<nu>\<^sub>b_opt)" l]
        by (intro mult_imp_div_pos_less le_less_trans[OF dist_ge]) argo+
    qed
    thus ?thesis
      using gs_rel_dec h by auto
  qed
qed auto

subsection \<open>Optimality\<close>

lemma THE_fix_GS: "(THE v. GS.\<L>\<^sub>b_split v = v) = \<nu>\<^sub>b_opt"
  using GS.\<L>\<^sub>b_lim(1) GS.\<L>\<^sub>b_split_fix by blast

lemma contraction_\<L>_split_dist: "(1 - l) * dist v \<nu>\<^sub>b_opt \<le> dist v (GS.\<L>\<^sub>b_split v)"
  using GS_QR_disc_le_disc 
  by (fastforce simp: THE_fix_GS
      intro: order.trans[OF _ contraction_dist, of _ l] order.trans[OF GS.\<L>\<^sub>b_split_contraction] mult_right_mono)+

lemma dist_\<L>\<^sub>b_split_opt_eps:
  assumes "eps > 0" "2 * l * dist v (GS.\<L>\<^sub>b_split v) < eps * (1-l)"
  shows "dist (GS.\<L>\<^sub>b_split v) \<nu>\<^sub>b_opt < eps / 2"
proof -
  have "dist v \<nu>\<^sub>b_opt \<le> dist v (GS.\<L>\<^sub>b_split v) / (1 - l)"
    using contraction_\<L>_split_dist
    by (simp add: mult.commute pos_le_divide_eq)
  hence "2 * l * dist v \<nu>\<^sub>b_opt \<le> 2 * l * (dist v (GS.\<L>\<^sub>b_split v) / (1 - l))"
    using contraction_\<L>_dist assms mult_le_cancel_left_pos[of "2 * l"]
    by (fastforce intro!: mult_left_mono[of _ _ "2 * l"])
  hence "2 * l * dist v \<nu>\<^sub>b_opt < eps"
    by (auto simp: assms(2) pos_divide_less_eq intro: order.strict_trans1)
  hence "dist v \<nu>\<^sub>b_opt * l < eps / 2"
    by argo
  hence *: "l * dist v \<nu>\<^sub>b_opt < eps / 2"
    by (auto simp: algebra_simps)
  show "dist (GS.\<L>\<^sub>b_split v) \<nu>\<^sub>b_opt < eps / 2"
    using GS.\<L>\<^sub>b_split_contraction[of v \<nu>\<^sub>b_opt] order.trans mult_right_mono[OF GS_QR_disc_le_disc zero_le_dist]
    by (fastforce intro!: le_less_trans[OF _ *])
qed

lemma gs_iteration_error: 
  assumes "eps > 0"
  shows "dist (gs_iteration eps v) \<nu>\<^sub>b_opt < eps / 2"
  using assms dist_\<L>\<^sub>b_split_opt_eps gs_iteration.simps
  by (induction eps v rule: gs_iteration.induct) auto

lemma find_policy_error_bound_gs:
  assumes "eps > 0" "2 * l * dist v (GS.\<L>\<^sub>b_split v) < eps * (1-l)"
  shows "dist (\<nu>\<^sub>b (mk_stationary_det (d_GS_least (GS.\<L>\<^sub>b_split v)))) \<nu>\<^sub>b_opt < eps"
proof (rule GS.find_policy_QR_error_bound[OF assms(1)])
  have "2 * GS.QR_disc * dist v (GS.\<L>\<^sub>b_split v) \<le> 2 * l * dist v (GS.\<L>\<^sub>b_split v)"
    using GS_QR_disc_le_disc by (auto intro!: mult_right_mono)
  also have "\<dots> <  eps * (1-l)" 
    using assms by auto
  also have "\<dots> \<le> eps * (1 - GS.QR_disc)" 
    using assms GS_QR_disc_le_disc by (auto intro!: mult_left_mono)
  finally show "2 * GS.QR_disc * dist v (GS.\<L>\<^sub>b_split v) < eps * (1 - GS.QR_disc)".
next
  obtain d where d: "is_dec_det d"
    using ex_dec_det by blast  
  show "is_arg_max (\<lambda>d. (GS.L_split d (GS.\<L>\<^sub>b_split v)) s) (\<lambda>d. d \<in> D\<^sub>D) (d_GS_least (GS.\<L>\<^sub>b_split v))" for s
    unfolding GS_inv_def[symmetric] using d_GS_least_is_arg_max by auto
qed

definition "vi_gs_policy eps v = d_GS_least (gs_iteration eps v)"

lemmas gs_iteration.simps[simp del]

lemma vi_gs_policy_opt:
  assumes "0 < eps"
  shows "dist (\<nu>\<^sub>b (mk_stationary_det (vi_gs_policy eps v))) \<nu>\<^sub>b_opt < eps"
  unfolding vi_gs_policy_def
  using assms
proof (induction eps v rule: gs_iteration.induct)
  case (1 v)
  then show ?case
    using find_policy_error_bound_gs by (subst gs_iteration.simps) auto
qed

section \<open>Preparation for Codegen\<close>
lemma \<L>\<^sub>b_split_eq_GS_inv: "GS.\<L>\<^sub>b_split v = GS_inv (d_GS_least v) v"
  using arg_max_SUP[OF d_GS_least_is_arg_max]
  by (auto simp: GS.\<L>\<^sub>b_split.rep_eq GS.\<L>_split_def GS_inv_def[symmetric])

lemma \<L>\<^sub>b_split_GS: "GS.\<L>\<^sub>b_split v s = (\<Squnion>a \<in> A s. r (s, a) + l * measure_pmf.expectation (K (s, a)) (bfun_if (\<lambda>s'. s' < s) (GS.\<L>\<^sub>b_split v) v))"
proof -
  let ?d = "d_GS_least v"
  have "GS.\<L>\<^sub>b_split v s = GS_inv ?d v s"
    using \<L>\<^sub>b_split_eq_GS_inv by auto
  also have "\<dots> = (\<Squnion>a \<in> A s. GS_inv (?d(s := a)) v s)"
  proof (subst arg_max_SUP[symmetric, of _ _ "?d s"])
    show "is_arg_max (\<lambda>a. (GS_inv (?d(s := a)) v) s) (\<lambda>x. x \<in> A s) (?d s)"
      using d_GS_least_eq A_ne A_fin MDP_reward_Util.arg_max_on_in
      by (auto simp: LeastI_ex finite_is_arg_max)
  qed fastforce
  also have "\<dots> = (\<Squnion>a \<in> A s. (r_det\<^sub>b (?d(s := a)) + l *\<^sub>R (\<P>\<^sub>U (?d(s := a)) v + \<P>\<^sub>L (?d(s := a)) (GS_inv (?d(s := a)) v))) s)"
    using GS_inv_rec by auto
  also have "\<dots> = (\<Squnion>a \<in> A s. r (s, a) + l * (\<P>\<^sub>U (?d(s := a)) v + \<P>\<^sub>L (?d(s := a)) (GS_inv (?d(s := a)) v)) s)"
    by auto
  also have "\<dots> = (\<Squnion>a \<in> A s. r (s, a) + l * (\<P>\<^sub>U (?d(s := a)) v + \<P>\<^sub>L (?d(s := a)) (GS_inv ?d v)) s)"
  proof -
    have "\<P>\<^sub>L (?d(s := a)) (GS_inv (?d(s := a)) v) s = \<P>\<^sub>L (?d(s := a)) (GS_inv (?d) v) s" for a
      by (fastforce intro!: GS_indep_high_states strict_lower_triangularD[OF  \<P>\<^sub>L_strict_lower, of s _ _ "(?d(s := a))"])
    thus ?thesis
      by auto
  qed
  also have "\<dots> = (\<Squnion>a \<in> A s. r (s, a) + l * \<P>\<^sub>1 (mk_dec_det (?d(s := a))) (bfun_if (\<lambda>s'. s' < s) (GS_inv ?d v) v) s)"
  proof -
    have "(bfun_if (\<lambda>s'. s' < s) 0 v + bfun_if ((\<le>) s) 0 (GS_inv ?d v)) = (bfun_if (\<lambda>s'. s' < s) (GS_inv ?d v) v)"
      by (auto simp: bfun_if.rep_eq)
    thus ?thesis
      by (auto simp: \<P>\<^sub>L.rep_eq \<P>\<^sub>U.rep_eq blinfun.add_right[symmetric] apply_bfun_plus)
  qed
  also have "\<dots> = (\<Squnion>a \<in> A s. r (s, a) + l * \<P>\<^sub>1 (mk_dec_det (?d(s := a))) (bfun_if (\<lambda>s'. s' < s) (GS.\<L>\<^sub>b_split v) v) s)"
    using \<L>\<^sub>b_split_eq_GS_inv by presburger
  also have "\<dots> = (\<Squnion>a \<in> A s. r (s, a) + l * measure_pmf.expectation (K (s, a)) (bfun_if (\<lambda>s'. s' < s) (GS.\<L>\<^sub>b_split v) v))"
    using \<P>\<^sub>1_det by auto
  finally show ?thesis.
qed

lemma \<L>\<^sub>b_split_GS_iter:
  assumes "\<And>s'. s' < s \<Longrightarrow> v' s' = GS.\<L>\<^sub>b_split v s'" "\<And>s'. s' \<ge> s \<Longrightarrow> v' s' = v s'"
  shows "GS.\<L>\<^sub>b_split v s = (\<Squnion>a \<in> A s. L\<^sub>a a v' s)"
  unfolding \<L>\<^sub>b_split_GS using assms[symmetric] by (auto simp: bfun_if.rep_eq cong: if_cong)

function GS_rec_upto where
  "GS_rec_upto n v s = (
  if n \<le> s 
  then v 
  else GS_rec_upto n (v(s := (\<Squnion>a \<in> A s. r (s, a) + l * measure_pmf.expectation (K (s, a)) v))) (Suc s))"
  by auto
termination
  by (relation "Wellfounded.measure (\<lambda>(n,v,s). n - s)") auto

lemmas GS_rec_upto.simps[simp del]

lemma GS_rec_upto_ge:
  assumes "s' \<ge> n"
  shows "GS_rec_upto n v s s' = v s'"
  using assms
  by (induction s arbitrary: s' rule: GS_rec_upto.induct) (fastforce simp add:  GS_rec_upto.simps)

lemma GS_rec_upto_less:
  assumes "s > s'"
  shows "GS_rec_upto n v s s' = v s'"
  using assms 
  by (induction s arbitrary: s' rule: GS_rec_upto.induct) (auto simp: GS_rec_upto.simps)

lemma GS_rec_upto_eq:
  assumes "s < n"
  shows "GS_rec_upto n v s s = (\<Squnion>a \<in> A s. L\<^sub>a a v s)"
  using assms
proof (induction n v s rule: GS_rec_upto.induct)
  case (1 n v s)
  then show ?case
    using GS_rec_upto_less by (cases "Suc s < n") (auto simp add: GS_rec_upto.simps)
qed

lemma GS_rec_upto_Suc:
  assumes "s' < n"
  shows "GS_rec_upto (Suc n) v s s' = GS_rec_upto n v s s'"
  using assms
proof (induction n v s arbitrary: s' rule: GS_rec_upto.induct)
  case (1 n v s)
  then show ?case
    using GS_rec_upto_less by (fastforce simp: GS_rec_upto.simps)
qed

lemma GS_rec_upto_Suc':
  assumes "s \<le> n"
  shows "GS_rec_upto (Suc n) v s n = (\<Squnion>a \<in> A n. L\<^sub>a a (GS_rec_upto n v s) n)"
  using assms
proof (induction n v s rule: GS_rec_upto.induct)
  case (1 n v s)
  then show ?case
    by (fastforce simp: not_less_eq_eq GS_rec_upto.simps)
qed

lemma GS_rec_upto_correct:
  assumes "s < n"
  shows "GS.\<L>\<^sub>b_split v s = GS_rec_upto n v 0 s"
  using assms
proof (induction n arbitrary: s)
  case 0
  then show ?case
    by auto
next
  case (Suc n)
  then show ?case
  proof (cases "s < n")
    case True
    thus ?thesis
      using Suc.IH by (auto simp: GS_rec_upto_Suc)
  next
    case False
    hence "s = n"
      using Suc by auto
    thus ?thesis
      using Suc.IH GS_rec_upto_ge by (auto simp: GS_rec_upto_Suc' intro: \<L>\<^sub>b_split_GS_iter)
  qed
qed

end
end

