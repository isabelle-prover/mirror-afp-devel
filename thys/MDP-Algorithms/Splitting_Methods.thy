(* Author: Maximilian Schäffeler *)

theory Splitting_Methods
  imports
    Value_Iteration
    Policy_Iteration
begin

section \<open>Value Iteration using Splitting Methods\<close>

subsection \<open>Regular Splittings for Matrices and Bounded Linear Functions\<close>

definition "is_splitting_blin X Q R \<longleftrightarrow>
  X = Q - R \<and> invertible\<^sub>L Q \<and> nonneg_blinfun (inv\<^sub>L Q) \<and> nonneg_blinfun R"

lemma is_splitting_blinD[dest]: 
  assumes "is_splitting_blin X Q R"
  shows "X = Q - R" "invertible\<^sub>L Q" "nonneg_blinfun (inv\<^sub>L Q)" "nonneg_blinfun R"
  using is_splitting_blin_def assms by auto

lemma is_splitting_blinI[intro]: 
  assumes "X = Q - R" "invertible\<^sub>L Q" "nonneg_blinfun (inv\<^sub>L Q)" "nonneg_blinfun R"
  shows "is_splitting_blin X Q R"
  using is_splitting_blin_def assms by auto

subsection \<open>Splitting Methods for MDPs\<close>

locale MDP_QR = MDP_att_\<L> A K r l 
  for A :: "'s::countable \<Rightarrow> 'a::countable set" 
    and K :: "('s \<times> 'a) \<Rightarrow> 's pmf"
    and r l +
  fixes Q R :: "('s \<Rightarrow> 'a) \<Rightarrow> ('s \<Rightarrow>\<^sub>b real) \<Rightarrow>\<^sub>L ('s \<Rightarrow>\<^sub>b real)"
  assumes is_splitting: "\<And>d. d \<in> D\<^sub>D \<Longrightarrow> is_splitting_blin (id_blinfun - l *\<^sub>R \<P>\<^sub>1 (mk_dec_det d)) (Q d) (R d)"
  and QR_contraction: "(\<Squnion>d\<in>D\<^sub>D. norm (inv\<^sub>L (Q d) o\<^sub>L R d)) < 1"
  and QR_bdd: "bdd_above ((\<lambda>d. norm (inv\<^sub>L (Q d) o\<^sub>L R d)) ` D\<^sub>D)"
  and Q_bdd: "bounded ((\<lambda>d. norm (inv\<^sub>L (Q d))) ` D\<^sub>D)"
  and arg_max_ex_split: "\<exists>d. \<forall>s. is_arg_max (\<lambda>d. inv\<^sub>L (Q d) (r_dec\<^sub>b (mk_dec_det d) + R d v) s) (\<lambda>d. d \<in> D\<^sub>D) d"
begin

lemma inv_Q_mono: "d \<in> D\<^sub>D \<Longrightarrow> u \<le> v \<Longrightarrow> (inv\<^sub>L (Q d)) u \<le> (inv\<^sub>L (Q d)) v"
  using is_splitting 
  by (auto intro!: nonneg_blinfun_mono)

lemma splitting_eq: "d \<in> D\<^sub>D \<Longrightarrow> Q d - R d = (id_blinfun - l *\<^sub>R \<P>\<^sub>1 (mk_dec_det d))"
  using is_splitting
  by fastforce

lemma Q_nonneg: "d \<in> D\<^sub>D \<Longrightarrow> 0 \<le> v \<Longrightarrow> 0 \<le> inv\<^sub>L (Q d) v"
  using is_splitting nonneg_blinfun_nonneg 
  by auto

lemma Q_invertible: "d \<in> D\<^sub>D \<Longrightarrow> invertible\<^sub>L (Q d)"
  using is_splitting
  by auto

lemma R_nonneg: "d \<in> D\<^sub>D \<Longrightarrow> 0 \<le> v \<Longrightarrow> 0 \<le> R d v"
  using is_splitting_blinD[OF is_splitting]
  by (fastforce simp: nonneg_blinfun_nonneg intro: nonneg_blinfun_mono)

lemma R_mono: "d \<in> D\<^sub>D \<Longrightarrow> u \<le> v \<Longrightarrow> (R d) u \<le> (R d) v"
  using R_nonneg[of d "v - u"]
  by (auto simp: blinfun.bilinear_simps)

lemma QR_nonneg: "d \<in> D\<^sub>D \<Longrightarrow> 0 \<le> v \<Longrightarrow> 0 \<le> (inv\<^sub>L (Q d) o\<^sub>L R d) v"
  by (simp add: Q_nonneg R_nonneg)

lemma QR_mono: "d \<in> D\<^sub>D \<Longrightarrow> u \<le> v \<Longrightarrow> (inv\<^sub>L (Q d) o\<^sub>L R d) u \<le> (inv\<^sub>L (Q d) o\<^sub>L R d) v"
  using QR_nonneg[of d "v - u"]
  by (auto simp: blinfun.bilinear_simps)

lemma norm_QR_less_one: "d \<in> D\<^sub>D \<Longrightarrow> norm (inv\<^sub>L (Q d) o\<^sub>L R d) < 1"
  using QR_bdd
  by (auto intro: cSUP_lessD[OF _ QR_contraction])

lemma splitting: "d \<in> D\<^sub>D \<Longrightarrow> id_blinfun - l *\<^sub>R \<P>\<^sub>1 (mk_dec_det d) = Q d - R d"
  using is_splitting
  by auto

subsection \<open>Discount Factor @{term "QR_disc"}\<close>
abbreviation "QR_disc \<equiv> (\<Squnion>d \<in> D\<^sub>D. norm (inv\<^sub>L (Q d) o\<^sub>L R d))"

lemma QR_le_QR_disc: "d \<in> D\<^sub>D \<Longrightarrow> norm (inv\<^sub>L (Q d) o\<^sub>L (R d)) \<le> QR_disc"
  using QR_bdd
  by (auto intro!: cSUP_upper)

lemma a_nonneg: "0 \<le> QR_disc"
  using QR_contraction norm_ge_zero ex_dec_det QR_bdd
  by (fastforce intro!: cSUP_upper2)

subsection \<open>Bellman-Operator\<close>
abbreviation "L_split d v \<equiv> inv\<^sub>L (Q d) (r_dec\<^sub>b (mk_dec_det d) + R d v)"

definition "\<L>_split v s = (\<Squnion>d \<in> D\<^sub>D. L_split d v s)"

lemma \<L>_split_bfun_aux:
  assumes "d \<in> D\<^sub>D"
  shows "norm (L_split d v) \<le> (\<Squnion>d \<in> D\<^sub>D. norm (inv\<^sub>L (Q d))) * r\<^sub>M + norm v"
proof -
  have "norm (L_split d v) \<le> norm (inv\<^sub>L (Q d) (r_dec\<^sub>b (mk_dec_det d))) + norm (inv\<^sub>L (Q d) (R d v))"
    by (simp add: blinfun.add_right norm_triangle_ineq)
  also have "\<dots> \<le> norm (inv\<^sub>L (Q d) (r_dec\<^sub>b (mk_dec_det d))) + norm (inv\<^sub>L (Q d) o\<^sub>L R d) * norm v"    
    by (auto simp: blinfun_apply_blinfun_compose[symmetric] norm_blinfun simp del: blinfun_apply_blinfun_compose)
  also have "\<dots> \<le> norm (inv\<^sub>L (Q d) (r_dec\<^sub>b (mk_dec_det d))) + norm v"
    using norm_QR_less_one assms
    by (fastforce intro!: mult_left_le_one_le)
  also have "\<dots> \<le> norm (inv\<^sub>L (Q d)) * r\<^sub>M + norm v"
    by (auto intro!: order.trans[OF norm_blinfun] mult_left_mono simp:  norm_r_dec_le)
  also have "\<dots> \<le> (\<Squnion>d \<in> D\<^sub>D. norm (inv\<^sub>L (Q d))) * r\<^sub>M + norm v"
    using Q_bdd bounded_imp_bdd_above
    by (auto intro!: mult_right_mono cSUP_upper assms simp: r\<^sub>M_nonneg)
  finally show ?thesis.
qed

lemma L_split_le: "d \<in> D\<^sub>D \<Longrightarrow> L_split d v s \<le> (\<Squnion>d \<in> D\<^sub>D. norm (inv\<^sub>L (Q d))) * r\<^sub>M + norm v"
  using le_norm_bfun order.trans[OF le_norm_bfun \<L>_split_bfun_aux]
  by auto

lift_definition \<L>\<^sub>b_split :: "('s \<Rightarrow>\<^sub>b real) \<Rightarrow> ('s \<Rightarrow>\<^sub>b real)" is \<L>_split 
  unfolding \<L>_split_def bfun_def
  using order.trans[OF abs_le_norm_bfun \<L>_split_bfun_aux] ex_dec_det
  by (fastforce intro!: boundedI cSup_abs_le)

lemma \<L>\<^sub>b_split_def': "\<L>\<^sub>b_split v s = (\<Squnion>d\<in>D\<^sub>D. L_split d v s)"
  unfolding \<L>\<^sub>b_split.rep_eq \<L>_split_def
  by auto

lemma \<L>\<^sub>b_split_contraction: "dist (\<L>\<^sub>b_split v) (\<L>\<^sub>b_split u) \<le> QR_disc * dist v u"
proof -
  have
    "\<L>\<^sub>b_split v s - \<L>\<^sub>b_split u s \<le> QR_disc * norm (v - u)" if h: "\<L>\<^sub>b_split u s \<le> \<L>\<^sub>b_split v s" for u v s
  proof -
    obtain d where d: "is_arg_max (\<lambda>d. inv\<^sub>L (Q d) (r_dec\<^sub>b (mk_dec_det d) + R d v) s) (\<lambda>d. d \<in> D\<^sub>D) d"
      using arg_max_ex_split by blast
    hence *: "inv\<^sub>L (Q d) (r_dec\<^sub>b (mk_dec_det d) + R d u) s \<le> \<L>\<^sub>b_split u s"
      by (fastforce simp: \<L>\<^sub>b_split_def' is_arg_max_linorder intro!: cSUP_upper2 L_split_le)
    have "inv\<^sub>L (Q d) (r_dec\<^sub>b (mk_dec_det d) + R d v) s = \<L>\<^sub>b_split v s"
      by (auto simp: \<L>\<^sub>b_split_def' arg_max_SUP[OF d])
    hence "\<L>\<^sub>b_split v s - \<L>\<^sub>b_split u s = inv\<^sub>L (Q d) (r_dec\<^sub>b (mk_dec_det d) + R d v) s - \<L>\<^sub>b_split u s"
      by auto
    also have "\<dots> \<le> (inv\<^sub>L (Q d) o\<^sub>L R d) (v - u) s"
      using * by (auto simp: blinfun.bilinear_simps)
    also have "\<dots> \<le> norm ((inv\<^sub>L (Q d) o\<^sub>L R d)) * norm (v - u)"
      by (fastforce intro: order.trans[OF le_norm_bfun norm_blinfun])
    also have "\<dots> \<le> QR_disc * norm (v - u)"
      using QR_contraction d QR_bdd
      by (auto simp: is_arg_max_linorder intro!: mult_right_mono cSUP_upper2)
    finally show ?thesis.
  qed
  hence "\<bar>(\<L>\<^sub>b_split v - \<L>\<^sub>b_split u) s\<bar> \<le> QR_disc * dist v u" for s
    by (cases "\<L>\<^sub>b_split v s \<le> \<L>\<^sub>b_split u s") (fastforce simp: dist_norm norm_minus_commute)+
  thus ?thesis
    by (auto intro!: cSUP_least simp: dist_bfun.rep_eq dist_real_def)
qed

lemma \<L>\<^sub>b_lim:
  "\<exists>!v. \<L>\<^sub>b_split v = v"
  "(\<lambda>n. (\<L>\<^sub>b_split ^^ n) v) \<longlonglongrightarrow> (THE v. \<L>\<^sub>b_split v = v)"
  using banach'[of \<L>\<^sub>b_split] a_nonneg QR_contraction \<L>\<^sub>b_split_contraction
  unfolding is_contraction_def
  by auto

lemma \<L>\<^sub>b_split_tendsto_opt: "(\<lambda>n. (\<L>\<^sub>b_split ^^ n) v) \<longlonglongrightarrow> \<nu>\<^sub>b_opt"
proof -
  obtain L where l_fix: "\<L>\<^sub>b_split L = L"
    using \<L>\<^sub>b_lim(1) by auto
  have "\<nu>\<^sub>b (mk_stationary_det d) \<le> L" if d: "d \<in> D\<^sub>D" for d
  proof -
    let ?QR = "inv\<^sub>L (Q d) o\<^sub>L R d"
    have "inv\<^sub>L (Q d) (r_dec\<^sub>b (mk_dec_det d) + R d L) \<le> \<L>\<^sub>b_split L"
      unfolding less_eq_bfun_def \<L>\<^sub>b_split_def'
      using d L_split_le by (auto intro!: bdd_aboveI cSUP_upper2)
    hence "inv\<^sub>L (Q d) (r_dec\<^sub>b (mk_dec_det d) + R d L) \<le> L"
      using l_fix by auto
    hence aux: "inv\<^sub>L (Q d) (r_dec\<^sub>b (mk_dec_det d)) \<le> (id_blinfun - ?QR) L"
      using that by (auto simp: blinfun.bilinear_simps le_diff_eq)
    have inv_eq: "inv\<^sub>L (id_blinfun - ?QR) = (\<Sum>i. ?QR ^^ i)"
      using QR_contraction d norm_QR_less_one
      by (auto intro!: inv\<^sub>L_inf_sum)
    have summable_QR:"summable (\<lambda>i. norm (?QR ^^ i))"
      using QR_contraction QR_bdd d 
      by (auto simp: a_nonneg
          intro!: summable_comparison_test'[of "\<lambda>i. QR_disc^i" 0 "\<lambda>n. norm ((inv\<^sub>L (Q d) o\<^sub>L R d) ^^n)"]
            cSUP_upper2 power_mono order.trans[OF norm_blinfunpow_le])
    have "summable (\<lambda>i. (?QR ^^ i) v s)" for v s 
      by (rule summable_comparison_test'[where g = "\<lambda>i. norm (?QR ^^ i) * norm v"])
        (auto intro!: summable_QR summable_norm_cancel order.trans[OF abs_le_norm_bfun] order.trans[OF norm_blinfun] summable_mult2)
    moreover have "0 \<le> v \<Longrightarrow> 0 \<le> (\<Sum>i<n. (?QR ^^ i) v s)" for n v s
      using blinfunpow_nonneg[OF QR_nonneg[OF d]]
      by (induction n) (auto simp add: less_eq_bfun_def)
    ultimately have "0 \<le> v \<Longrightarrow> 0 \<le> (\<Sum>i. ((?QR ^^ i) v s)) " for v s
      by (auto intro!: summable_LIMSEQ LIMSEQ_le)
    hence "0 \<le> v \<Longrightarrow> 0 \<le> (\<Sum>i. ((?QR ^^ i))) v s" for v s
      using bounded_linear_apply_bfun summable_QR summable_comparison_test' 
      by (subst bounded_linear.suminf[where f = "(\<lambda>i. apply_bfun (blinfun_apply i v) s)"])
        (fastforce intro: bounded_linear_compose[of "\<lambda>s. apply_bfun s _"])+
    hence "0 \<le> v \<Longrightarrow> 0 \<le> inv\<^sub>L (id_blinfun - ?QR) v" for v
      by (simp add: inv_eq less_eq_bfun_def)
    hence "(inv\<^sub>L (id_blinfun - ?QR)) ((inv\<^sub>L (Q d)) (r_dec\<^sub>b (mk_dec_det d)))
    \<le> (inv\<^sub>L (id_blinfun - ?QR)) ((id_blinfun - ?QR) L)"
      by (metis aux blinfun.diff_right diff_ge_0_iff_ge)
    hence "(inv\<^sub>L (id_blinfun - ?QR) o\<^sub>L inv\<^sub>L (Q d)) (r_dec\<^sub>b (mk_dec_det d)) \<le> L"
      using invertible\<^sub>L_inf_sum[OF norm_QR_less_one[OF that]] by auto
    hence "(inv\<^sub>L (Q d o\<^sub>L (id_blinfun - ?QR))) (r_dec\<^sub>b (mk_dec_det d)) \<le> L"
      using d norm_QR_less_one
      by (auto simp: inv\<^sub>L_compose[OF Q_invertible invertible\<^sub>L_inf_sum])
    hence "(inv\<^sub>L (Q d - R d)) (r_dec\<^sub>b (mk_dec_det d)) \<le> L"
      using Q_invertible d
      by (auto simp: blinfun_compose_diff_right blinfun_compose_assoc[symmetric])
    thus "\<nu>\<^sub>b (mk_stationary_det d) \<le> L"
      by (auto simp: \<nu>_stationary splitting[OF that, symmetric] inv\<^sub>L_inf_sum blincomp_scaleR_right)
  qed
  hence opt_le: "\<nu>\<^sub>b_opt \<le> L"
    by (metis \<nu>_conserving_def conserving_imp_opt' ex_improving_det)
  obtain d where d: "is_arg_max (\<lambda>d. inv\<^sub>L (Q d) (r_dec\<^sub>b (mk_dec_det d) + R d L) s) (\<lambda>d. d \<in> D\<^sub>D) d" for s
    using arg_max_ex_split by blast
  hence "d \<in> D\<^sub>D"
    unfolding is_arg_max_linorder by auto
  have "L = inv\<^sub>L (Q d) (r_dec\<^sub>b (mk_dec_det d) + R d L)"
    by (subst l_fix[symmetric]) (fastforce simp: \<L>\<^sub>b_split_def' arg_max_SUP[OF d])
  hence "Q d L = r_dec\<^sub>b (mk_dec_det d) + R d L"
    by (metis Q_invertible \<open>d \<in> D\<^sub>D\<close> inv_app2')
  hence "(id_blinfun - l *\<^sub>R \<P>\<^sub>1 (mk_dec_det d)) L = r_dec\<^sub>b (mk_dec_det d)"
    using splitting[OF \<open>d \<in> D\<^sub>D\<close>] by (simp add: blinfun.diff_left)
  hence "L = inv\<^sub>L ((id_blinfun - l *\<^sub>R \<P>\<^sub>1 (mk_dec_det d))) (r_dec\<^sub>b (mk_dec_det d))"
    using invertible\<^sub>L_inf_sum[OF norm_\<P>\<^sub>1_l_less] inv_app1' by metis
  hence "L = \<nu>\<^sub>b (mk_stationary_det d)"
    by (auto simp: inv\<^sub>L_inf_sum \<nu>_stationary blincomp_scaleR_right)
  hence "\<nu>\<^sub>b_opt = L"
    using opt_le \<open>d \<in> D\<^sub>D\<close> is_markovian_def
    by (auto intro: order.antisym[OF _ \<nu>\<^sub>b_le_opt])
  thus ?thesis
    using \<L>\<^sub>b_lim l_fix the1_equality[OF \<L>\<^sub>b_lim(1)] by auto
qed

lemma \<L>\<^sub>b_split_fix[simp]: "\<L>\<^sub>b_split \<nu>\<^sub>b_opt = \<nu>\<^sub>b_opt"
  using \<L>\<^sub>b_lim \<L>\<^sub>b_split_tendsto_opt the_equality limI
  by (metis (mono_tags, lifting))

lemma dist_\<L>\<^sub>b_split_opt_eps:
  assumes "eps > 0" "2 * QR_disc * dist v (\<L>\<^sub>b_split v) < eps * (1-QR_disc)"
  shows "dist (\<L>\<^sub>b_split v) \<nu>\<^sub>b_opt < eps / 2"
proof -
  have "(1 - QR_disc) * dist v \<nu>\<^sub>b_opt \<le> dist v (\<L>\<^sub>b_split v)"
    using dist_triangle \<L>\<^sub>b_split_contraction[of v "\<nu>\<^sub>b_opt"]
    by (fastforce simp: algebra_simps intro: order.trans[OF _ add_left_mono[of "dist (\<L>\<^sub>b_split v) \<nu>\<^sub>b_opt"]])
  hence "dist v \<nu>\<^sub>b_opt \<le> dist v (\<L>\<^sub>b_split v) / (1 - QR_disc)"
    using QR_contraction
    by (simp add: mult.commute pos_le_divide_eq)
  hence "2 * QR_disc * dist v \<nu>\<^sub>b_opt \<le> 2 * QR_disc * (dist v (\<L>\<^sub>b_split v) / (1 - QR_disc))"
    using \<L>\<^sub>b_split_contraction assms mult_le_cancel_left_pos[of "2 * QR_disc"] a_nonneg
    by (fastforce intro!: mult_left_mono[of _ _ "2 * QR_disc"])
  hence "2 * QR_disc * dist v \<nu>\<^sub>b_opt < eps"
    using a_nonneg QR_contraction
    by (auto simp: assms(2) pos_divide_less_eq intro: order.strict_trans1)
  hence "dist v \<nu>\<^sub>b_opt * QR_disc < eps / 2"
    by argo
  thus "dist (\<L>\<^sub>b_split v) \<nu>\<^sub>b_opt < eps / 2"
    using \<L>\<^sub>b_split_contraction[of v \<nu>\<^sub>b_opt] 
    by (auto simp: algebra_simps)
qed

lemma L_split_fix:
  assumes "d \<in> D\<^sub>D"
  shows "L_split d (\<nu>\<^sub>b (mk_stationary_det d)) = \<nu>\<^sub>b (mk_stationary_det d)"
proof -
  let ?d = "mk_dec_det d"
  let ?p = "mk_stationary_det d"
  have "(Q d - R d) (\<nu>\<^sub>b ?p) = r_dec\<^sub>b ?d"
    using L_\<nu>_fix[of "mk_dec_det d"]
    by (simp add: L_def splitting[OF assms, symmetric] blinfun.bilinear_simps diff_eq_eq)
  thus ?thesis
    using assms
    by (auto simp: blinfun.bilinear_simps diff_eq_eq inv\<^sub>L_cancel_iff[OF Q_invertible])
qed

lemma L_split_contraction:
  assumes "d \<in> D\<^sub>D"
  shows "dist (L_split d v) (L_split d u) \<le> QR_disc * dist v u"
proof -
  have aux: "L_split d v s - L_split d u s \<le> QR_disc * dist v u" if lea: "(L_split d u s) \<le> (L_split d v s)" for v s u
  proof -
    have "L_split d v s - L_split d u s = (inv\<^sub>L (Q d) o\<^sub>L (R d)) (v - u) s"
      by (auto simp: blinfun.bilinear_simps)
    also have "\<dots> \<le> norm ((inv\<^sub>L (Q d) o\<^sub>L (R d)) (v - u))"
      by (simp add: le_norm_bfun)
    also have "\<dots> \<le> norm ((inv\<^sub>L (Q d) o\<^sub>L (R d))) * dist v u"
      by (auto simp only: dist_norm norm_blinfun)
    also have "\<dots> \<le> QR_disc * dist v u"
      using assms QR_le_QR_disc
      by (auto intro!: mult_right_mono)
    finally show ?thesis
      by auto
  qed
  have "dist (L_split d v s) (L_split d u s) \<le> QR_disc * dist v u" for v s u
    using aux aux[of v _ u]
    by (cases "L_split d v s \<ge> L_split d u s") (auto simp: dist_real_def dist_commute)
  thus "dist (L_split d v) (L_split d u) \<le> QR_disc * dist v u"
    by (simp add: dist_bound)
qed



lemma argmax_policy_error_bound:
  assumes am: "\<And>s. is_arg_max (\<lambda>d. L (mk_dec_det d) (\<L>\<^sub>b v) s) (\<lambda>d. d \<in> D\<^sub>D) d"
  shows "(1 - l) * dist (\<nu>\<^sub>b (mk_stationary_det d)) (\<L>\<^sub>b v) \<le> l * dist (\<L>\<^sub>b v) v"
proof -
  have "dist (\<nu>\<^sub>b (mk_stationary_det d)) (\<L>\<^sub>b v) = dist (L (mk_dec_det d) (\<nu>\<^sub>b (mk_stationary_det d))) (\<L>\<^sub>b v)"
    using L_\<nu>_fix by presburger
  also have "\<dots> \<le> dist (L (mk_dec_det d) (\<nu>\<^sub>b (mk_stationary_det d))) (\<L>\<^sub>b (\<L>\<^sub>b v)) + dist (\<L>\<^sub>b (\<L>\<^sub>b v)) (\<L>\<^sub>b v)"
    using dist_triangle by blast
  also have "\<dots> = dist (L (mk_dec_det d) (\<nu>\<^sub>b (mk_stationary_det d))) (L (mk_dec_det d) (\<L>\<^sub>b v)) + dist (\<L>\<^sub>b (\<L>\<^sub>b v)) (\<L>\<^sub>b v)"
    using \<L>\<^sub>b_eq_SUP_det using arg_max_SUP[OF assms, symmetric]
    by (auto simp: dist_bfun_def)
  also have "\<dots> \<le> l * dist (\<nu>\<^sub>b (mk_stationary_det d)) (\<L>\<^sub>b v) + l * dist (\<L>\<^sub>b v) v"
    by (meson add_mono contraction_L contraction_\<L>)
  finally show ?thesis
    by (auto simp: algebra_simps)
qed

lemma find_policy_QR_error_bound:
  assumes "eps > 0" "2 * QR_disc * dist v (\<L>\<^sub>b_split v) < eps * (1-QR_disc)"
  assumes am: "\<And>s. is_arg_max (\<lambda>d. L_split d (\<L>\<^sub>b_split v) s) (\<lambda>d. d \<in> D\<^sub>D) d"
  shows "dist (\<nu>\<^sub>b (mk_stationary_det d)) \<nu>\<^sub>b_opt < eps"
proof -
  let ?p = "mk_stationary_det d"
  have L_eq_\<L>\<^sub>b: "L_split d (\<L>\<^sub>b_split v) = \<L>\<^sub>b_split (\<L>\<^sub>b_split v)"
    by (auto simp: \<L>\<^sub>b_split_def' arg_max_SUP[OF am])
  have "dist (\<nu>\<^sub>b ?p) (\<L>\<^sub>b_split v) = dist (L_split d (\<nu>\<^sub>b ?p)) (\<L>\<^sub>b_split v)"
    using am
    by (auto simp: is_arg_max_linorder L_split_fix)
  also have "\<dots> \<le> dist (L_split d (\<nu>\<^sub>b ?p)) (\<L>\<^sub>b_split (\<L>\<^sub>b_split v)) + dist (\<L>\<^sub>b_split (\<L>\<^sub>b_split v)) (\<L>\<^sub>b_split v)"
    by (auto intro: dist_triangle)
  also have "\<dots> = dist (L_split d (\<nu>\<^sub>b ?p)) (L_split d (\<L>\<^sub>b_split v)) + dist (\<L>\<^sub>b_split (\<L>\<^sub>b_split v)) (\<L>\<^sub>b_split v)"
    by (auto simp: L_eq_\<L>\<^sub>b)
  also have "\<dots> \<le> QR_disc * dist (\<nu>\<^sub>b ?p) (\<L>\<^sub>b_split v) + QR_disc * dist (\<L>\<^sub>b_split v) v"
    using \<L>\<^sub>b_split_contraction L_split_contraction am unfolding is_arg_max_def
    by (auto intro!: add_mono)
  finally have aux: "dist (\<nu>\<^sub>b ?p) (\<L>\<^sub>b_split v) \<le> QR_disc * dist (\<nu>\<^sub>b ?p) (\<L>\<^sub>b_split v) + QR_disc * dist (\<L>\<^sub>b_split v) v" .
  hence "dist (\<nu>\<^sub>b ?p) (\<L>\<^sub>b_split v) - QR_disc * dist (\<nu>\<^sub>b ?p) (\<L>\<^sub>b_split v) \<le> QR_disc * dist (\<L>\<^sub>b_split v) v"
    by auto
  hence "dist (\<nu>\<^sub>b ?p) (\<L>\<^sub>b_split v) * (1 - QR_disc) \<le> QR_disc * dist (\<L>\<^sub>b_split v) v"
    by argo
  hence  "2 * dist (\<nu>\<^sub>b ?p) (\<L>\<^sub>b_split v) * (1-QR_disc) \<le> 2 * (QR_disc * dist (\<L>\<^sub>b_split v) v)"
    using mult_left_mono 
    by auto
  hence "2 * dist (\<nu>\<^sub>b ?p) (\<L>\<^sub>b_split v) * (1 - QR_disc) \<le> eps * (1 - QR_disc)"
    using assms
    by (auto intro!: mult_left_mono simp: dist_commute pos_divide_le_eq)
  hence "2 * dist (\<nu>\<^sub>b ?p) (\<L>\<^sub>b_split v) \<le> eps"
    using QR_contraction mult_right_le_imp_le
    by auto
  moreover have "2 * dist (\<L>\<^sub>b_split v) \<nu>\<^sub>b_opt < eps"
    using dist_\<L>\<^sub>b_split_opt_eps assms
    by fastforce
  ultimately show ?thesis 
    using dist_triangle[of "\<nu>\<^sub>b ?p" \<nu>\<^sub>b_opt "\<L>\<^sub>b_split v"]
    by auto
qed

end
context MDP_att_\<L>
begin


lemma inv_one_sub_Q':
  fixes f :: "'c :: banach \<Rightarrow>\<^sub>L 'c"
  assumes onorm_le: "norm (id_blinfun - f) < 1"
  shows "inv\<^sub>L f = (\<Sum>i. (id_blinfun - f)^^i)"
  by (metis inv\<^sub>L_I inv_one_sub_Q assms)

lemma blinfun_le_trans: "blinfun_le X Y \<Longrightarrow> blinfun_le Y Z \<Longrightarrow> blinfun_le X Z"
  unfolding blinfun_le_def nonneg_blinfun_def
  by (fastforce simp: blinfun.diff_left)

lemma blinfun_leI[intro]: "(\<And>v. v \<ge> 0 \<Longrightarrow> blinfun_apply C v \<le> blinfun_apply D v) \<Longrightarrow> blinfun_le C D"
  unfolding blinfun_le_def nonneg_blinfun_def
  by (auto simp: algebra_simps blinfun.diff_left)
  
lemma blinfun_pow_mono: "nonneg_blinfun (C :: ('c \<Rightarrow>\<^sub>b real) \<Rightarrow>\<^sub>L ('c \<Rightarrow>\<^sub>b real)) \<Longrightarrow> blinfun_le C D \<Longrightarrow> blinfun_le (C ^^ n) (D ^^ n)"
proof (induction n)
  case 0
  then show ?case by (simp add: blinfun_le_def nonneg_blinfun_def)
next
  case (Suc n)
  have *: "\<And>v. 0 \<le> v \<Longrightarrow> blinfun_apply (D ^^ n) (blinfun_apply C v) \<le> blinfun_apply (D ^^ n) (blinfun_apply D v)" 
    by (metis (no_types, opaque_lifting) Suc.prems(1) Suc.prems(2) blinfun_apply_mono blinfunpow_nonneg le_left_mono nonneg_blinfun_def nonneg_blinfun_mono)
  thus ?case
    using blinfun_apply_mono Suc
    by (intro blinfun_leI) (auto simp: blinfunpow_assoc blinfunpow_nonneg nonneg_blinfun_def simp del: blinfunpow.simps intro!: blinfun_apply_mono order.trans[OF _ *])
qed

lemma blinfun_le_iff: "blinfun_le X Y \<longleftrightarrow> (\<forall>v \<ge> 0. X v \<le> Y v)"
  unfolding blinfun_le_def nonneg_blinfun_def
  by (auto simp: blinfun.diff_left)

text \<open>An important theorem: allows to compare the rate of convergence for different splittings\<close>
lemma norm_splitting_le:
  assumes "is_splitting_blin (id_blinfun - l *\<^sub>R \<P>\<^sub>1 d) Q1 R1"
    and "is_splitting_blin (id_blinfun - l *\<^sub>R \<P>\<^sub>1 d) Q2 R2"
    and "blinfun_le R2 R1"
    and "blinfun_le R1 (l *\<^sub>R \<P>\<^sub>1 d)"
  shows "norm (inv\<^sub>L Q2 o\<^sub>L R2) \<le> norm (inv\<^sub>L Q1 o\<^sub>L R1)"
proof -
  have 
    inv_Q: "inv\<^sub>L Q = (\<Sum>i. (id_blinfun - Q)^^i)" "norm (id_blinfun - Q) < 1" and
    splitting_eq: "id_blinfun - Q = l *\<^sub>R \<P>\<^sub>1 d - R" and
    nonneg_Q: "nonneg_blinfun (id_blinfun - Q)"
    if "blinfun_le R (l *\<^sub>R \<P>\<^sub>1 d)"
      and "is_splitting_blin (id_blinfun - l *\<^sub>R \<P>\<^sub>1 d) Q R" for Q R
  proof -
    show splitting_eq: "id_blinfun - Q = l *\<^sub>R \<P>\<^sub>1 d - R"
      using that unfolding is_splitting_blin_def
      by (auto simp: algebra_simps)
    have R_nonneg: "nonneg_blinfun R"
      using that by blast
    show nonneg_Q:  "nonneg_blinfun (id_blinfun - Q)"
      using that by (simp add: blinfun_le_def splitting_eq)
    moreover have "blinfun_le (id_blinfun - Q) (l *\<^sub>R \<P>\<^sub>1 d)"
      using R_nonneg by (simp add: splitting_eq blinfun_le_def)
    ultimately have "norm (id_blinfun - Q) \<le> norm (l *\<^sub>R \<P>\<^sub>1 d)"
      using blinfun_le_def matrix_le_norm_mono by fast
    thus "norm (id_blinfun - Q) < 1"
      using norm_\<P>\<^sub>1_l_less by (simp add: order.strict_trans1)
    thus "inv\<^sub>L Q = (\<Sum>i. (id_blinfun - Q) ^^ i)"
      using inv\<^sub>L_inf_sum by fastforce
  qed

  have i1: "inv\<^sub>L Q1 = (\<Sum>i. (id_blinfun - Q1) ^^ i)" "norm (id_blinfun - Q1) < 1" 
    and i2: "inv\<^sub>L Q2 = (\<Sum>i. (id_blinfun - Q2) ^^ i)" "norm (id_blinfun - Q2) < 1"
    using assms by (auto intro: blinfun_le_trans inv_Q[of R2 Q2] inv_Q[of R1 Q1])

  have Q1_le_Q2: "blinfun_le (id_blinfun - Q1) (id_blinfun - Q2)"
    using assms unfolding is_splitting_blin_def blinfun_le_def eq_diff_eq
    by fastforce

  have "(inv\<^sub>L Q1) = ((\<Sum>i. (id_blinfun - Q1) ^^ i))"
    using i1 by auto
  also have "\<dots> =  ((\<Sum>i. ((id_blinfun - Q1) ^^ i)))"
    using summable_inv_Q i1(2) 
    by auto
  have "blinfun_le ((\<Sum>i. ((id_blinfun - Q1) ^^ i))) (\<Sum>i. ((id_blinfun - Q2) ^^ i))"
  proof -
    have le_n: "\<And>n v. 0 \<le> v \<Longrightarrow> (\<Sum>i<n. ((id_blinfun - Q1) ^^ i) v) \<le> (\<Sum>i<n. ((id_blinfun - Q2) ^^ i) v)" 
      using nonneg_Q blinfun_pow_mono[OF _ Q1_le_Q2] assms
      by (auto intro!: sum_mono simp: blinfun_le_iff)
    hence le_n_elem: "\<And>n v. 0 \<le> v \<Longrightarrow> (\<Sum>i<n. ((id_blinfun - Q1) ^^ i) v s) \<le> (\<Sum>i<n. ((id_blinfun - Q2) ^^ i) v s)" for s
      unfolding less_eq_bfun_def
      by (simp add: sum_apply_bfun)
    have tt: "(\<lambda>n. (\<Sum>i<n. ((id_blinfun - Q1) ^^ i) v s)) \<longlonglongrightarrow> (\<Sum>i. ((id_blinfun - Q1) ^^ i)) v s"
              "(\<lambda>n. (\<Sum>i<n. ((id_blinfun - Q2) ^^ i) v s)) \<longlonglongrightarrow> (\<Sum>i. ((id_blinfun - Q2) ^^ i)) v s" for v s
      unfolding blinfun.sum_left[symmetric] sum_apply_bfun[symmetric]
      using summable_inv_Q[OF i1(2)] summable_inv_Q[OF i2(2)]
      by (fastforce intro: bfun_tendsto_apply_bfun tendsto_blinfun_apply summable_LIMSEQ)+
    show ?thesis                        
      unfolding blinfun_le_iff less_eq_bfun_def
      using le_n_elem
      by (auto simp add: less_eq_bfunI intro: Topological_Spaces.lim_mono[OF _ tt(1) tt(2)])
  qed
  also have "\<dots> = (inv\<^sub>L Q2)"
    using summable_inv_Q i2(2) i2 by auto
  finally have Q1_le_Q2: "blinfun_le (inv\<^sub>L Q1) (inv\<^sub>L Q2)".

  have *: "nonneg_blinfun ((inv\<^sub>L Q1) o\<^sub>L R1)" "nonneg_blinfun ((inv\<^sub>L Q2) o\<^sub>L R2)"
    using assms is_splitting_blin_def
    by (metis blinfun_apply_blinfun_compose nonneg_blinfun_def)+
  have "0 \<le> (id_blinfun - l *\<^sub>R \<P>\<^sub>1 d) 1"
    using less_imp_le[OF disc_lt_one]
    by (auto simp: blinfun.diff_left less_eq_bfun_def blinfun.scaleR_left)
  hence "(inv\<^sub>L Q1) ((id_blinfun - l *\<^sub>R \<P>\<^sub>1 d) 1) \<le> (inv\<^sub>L Q2) ((id_blinfun - l *\<^sub>R \<P>\<^sub>1 d) 1)"
    using Q1_le_Q2
    by (simp add: blinfun_le_iff)
  hence "(inv\<^sub>L Q1) ((Q1 - R1) 1) \<le> (inv\<^sub>L Q2) ((Q2 - R2) 1)"
    by (metis (no_types, opaque_lifting) assms(1) assms(2) is_splitting_blin_def)
  hence "(inv\<^sub>L Q1 o\<^sub>L Q1) 1 - (inv\<^sub>L Q1 o\<^sub>L R1) 1 \<le> (inv\<^sub>L Q2 o\<^sub>L Q2) 1 - (inv\<^sub>L Q2 o\<^sub>L R2) 1"
    by (auto simp: blinfun.add_left blinfun.diff_right blinfun.diff_left)
  hence "(inv\<^sub>L Q2 o\<^sub>L R2) 1 \<le> (inv\<^sub>L Q1 o\<^sub>L R1) 1"
    using assms unfolding is_splitting_blin_def by auto
  moreover have "0 \<le> (inv\<^sub>L Q2 o\<^sub>L R2) 1"
    using * assms(2) by (fastforce simp: less_eq_bfunI intro!: nonneg_blinfun_nonneg)
  ultimately have "norm ((inv\<^sub>L Q2 o\<^sub>L R2) 1) \<le> norm ((inv\<^sub>L Q1 o\<^sub>L R1) 1)"
    by (auto simp: less_eq_bfun_def norm_bfun_def' intro!: abs_le_norm_bfun abs_ge_self cSUP_mono bdd_above.I2 intro: order.trans)
  thus "norm ((inv\<^sub>L Q2 o\<^sub>L R2)) \<le> norm ((inv\<^sub>L Q1 o\<^sub>L R1))"
    by (simp add: * norm_nonneg_blinfun_one)
qed

end


end