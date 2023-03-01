(* Author: Maximilian Schäffeler *)

theory Modified_Policy_Iteration
  imports 
    Policy_Iteration
    Value_Iteration
begin

section \<open>Modified Policy Iteration\<close>

locale MDP_MPI = MDP_att_\<L> A K r l + MDP_act_disc arb_act A K r l 
  for A and K :: "'s :: countable \<times> 'a :: countable \<Rightarrow> 's pmf" and r l arb_act
begin

subsection \<open>The Advantage Function @{term B}\<close>

definition "B v s = (\<Squnion>d \<in> D\<^sub>R. (r_dec d s + (l *\<^sub>R \<P>\<^sub>1 d - id_blinfun) v s))"

text "The function @{const B} denotes the advantage of choosing the optimal action vs.
  the current value estimate"

lemma cSUP_plus:
  assumes "X \<noteq> {}" "bdd_above (f`X)"
  shows "(\<Squnion>x \<in> X. f x + c) = (\<Squnion>x \<in> X. f x) + (c::real)"
proof (rule antisym)
  show "(\<Squnion>x\<in>X. f x + c) \<le> \<Squnion> (f ` X) + c"
    using assms by (fastforce intro: cSUP_least cSUP_upper)
  show "\<Squnion> (f ` X) + c \<le> (\<Squnion>x\<in>X. f x + c)"
    unfolding le_diff_eq[symmetric]
    using assms
    by (intro cSUP_least) (auto simp add: algebra_simps bdd_above_def intro!: cSUP_upper2 intro: add_left_mono)+
qed

lemma cSUP_minus:
  assumes "X \<noteq> {}" "bdd_above (f`X)"
  shows "(\<Squnion>x \<in> X. f x - c) = (\<Squnion>x \<in> X. f x) - (c::real)"
  using cSUP_plus[OF assms, of "- c"] by auto

lemma B_eq_\<L>: "B v s = \<L> v s - v s"
proof -
  have *: "B v s = (\<Squnion>d \<in> D\<^sub>R. L d v s - v s)"
    unfolding B_def L_def by (auto simp add: blinfun.bilinear_simps add_diff_eq)
  have "bdd_above ((\<lambda>d. L d v s - v s) ` D\<^sub>R)"
    by (auto intro!: bounded_const bounded_minus_comp bounded_imp_bdd_above)
  thus ?thesis
    unfolding * \<L>_def using ex_dec by (fastforce intro!: cSUP_minus)
qed

text \<open>@{const B} is a bounded function.\<close>

lift_definition B\<^sub>b :: "('s \<Rightarrow>\<^sub>b real) \<Rightarrow> 's \<Rightarrow>\<^sub>b real" is "B"
  unfolding B_eq_\<L> using \<L>_bfun by (auto intro: Bounded_Functions.minus_cont)

lemma B\<^sub>b_eq_\<L>\<^sub>b: "B\<^sub>b v = \<L>\<^sub>b v - v"
  by (auto simp: \<L>\<^sub>b.rep_eq B\<^sub>b.rep_eq B_eq_\<L>)

lemma \<L>\<^sub>b_eq_SUP_L\<^sub>a': "\<L>\<^sub>b v s = (\<Squnion>a \<in> A s. L\<^sub>a a v s)"
  using L_eq_L\<^sub>a_det \<L>\<^sub>b_eq_SUP_det SUP_step_det_eq
  by auto

subsection \<open>Optimization of the Value Function over Multiple Steps\<close>

definition "U m v s = (\<Squnion>d \<in> D\<^sub>R. (\<nu>\<^sub>b_fin (mk_stationary d) m + ((l *\<^sub>R \<P>\<^sub>1 d)^^m) v) s)"

text \<open>@{const U} expresses the value estimate obtained by optimizing the first @{term m} steps and 
  afterwards using the current estimate.\<close>

lemma U_zero [simp]: "U 0 v = v"
  unfolding U_def \<L>_def by (auto simp: \<nu>\<^sub>b_fin.rep_eq)

lemma U_one_eq_\<L>: "U 1 v s = \<L> v s"
  unfolding U_def \<L>_def by (auto simp: \<nu>\<^sub>b_fin_eq_\<P>\<^sub>X L_def blinfun.bilinear_simps)

lift_definition U\<^sub>b :: "nat \<Rightarrow> ('s \<Rightarrow>\<^sub>b real) \<Rightarrow> ('s \<Rightarrow>\<^sub>b real)" is U
proof -
  fix n v
  have "norm (\<nu>\<^sub>b_fin (mk_stationary d) m) \<le> (\<Sum>i<m. l ^ i * r\<^sub>M)" for d m
    using abs_\<nu>_fin_le \<nu>\<^sub>b_fin.rep_eq by (auto intro!: norm_bound)
  moreover have "norm (((l *\<^sub>R \<P>\<^sub>1 d)^^m) v) \<le> l ^ m * norm v" for d m
    by (auto simp: \<P>\<^sub>X_const[symmetric] blinfun.bilinear_simps blincomp_scaleR_right 
        intro!: boundedI order.trans[OF abs_le_norm_bfun] mult_left_mono)
  ultimately have *: "norm (\<nu>\<^sub>b_fin (mk_stationary d) m + ((l *\<^sub>R \<P>\<^sub>1 d)^^m) v) \<le> (\<Sum>i<m. l ^ i * r\<^sub>M) +  l ^ m * norm v" for d m
    using norm_triangle_mono by blast
  show "U n v \<in> bfun"
    using ex_dec order.trans[OF abs_le_norm_bfun *]
    by (fastforce simp: U_def intro!: bfun_normI cSup_abs_le)
qed

lemma U\<^sub>b_contraction: "dist (U\<^sub>b m v) (U\<^sub>b m u) \<le> l ^ m * dist v u"
proof -
  have aux: "dist (U\<^sub>b m v s) (U\<^sub>b m u s) \<le> l ^ m * dist v u" if le: "U\<^sub>b m u s \<le> U\<^sub>b m v s" for s v u
  proof -
    let ?U = "\<lambda>m v d. (\<nu>\<^sub>b_fin (mk_stationary d) m + ((l *\<^sub>R \<P>\<^sub>1 d) ^^ m) v) s"
    have "U\<^sub>b m v s - U\<^sub>b m u s \<le> (\<Squnion>d \<in> D\<^sub>R. ?U m v d - ?U m u d)"
      using bounded_stationary_\<nu>\<^sub>b_fin bounded_disc_\<P>\<^sub>1 le
      unfolding U\<^sub>b.rep_eq U_def
      by (intro le_SUP_diff') (auto intro: bounded_plus_comp)
    also have "\<dots> = (\<Squnion>d \<in> D\<^sub>R. ((l *\<^sub>R \<P>\<^sub>1 d) ^^ m) (v - u) s)"
      by (simp add: L_def scale_right_diff_distrib blinfun.bilinear_simps)
    also have "\<dots> = (\<Squnion>d \<in> D\<^sub>R. l^m * ((\<P>\<^sub>1 d ^^ m) (v - u) s))"
      by (simp add: blincomp_scaleR_right blinfun.scaleR_left)
    also have "\<dots> = l^m * (\<Squnion>d \<in> D\<^sub>R. ((\<P>\<^sub>1 d ^^ m) (v - u) s))" 
      using D\<^sub>R_ne bounded_P bounded_disc_\<P>\<^sub>1' by (auto intro: bounded_SUP_mul)
    also have "\<dots> \<le> l^m * norm (\<Squnion>d \<in> D\<^sub>R. ((\<P>\<^sub>1 d ^^ m) (v - u) s))"
      by (simp add: mult_left_mono)
    also have "\<dots> \<le> l^m * (\<Squnion>d \<in> D\<^sub>R. norm (((\<P>\<^sub>1 d ^^ m) (v - u) s)))"
      using D\<^sub>R_ne ex_dec bounded_norm_comp bounded_disc_\<P>\<^sub>1'
      by (fastforce intro!: mult_left_mono)
    also have "\<dots> \<le> l^m * (\<Squnion>d \<in> D\<^sub>R. norm ((\<P>\<^sub>1 d ^^ m) ((v - u))))"
      using ex_dec
      by (fastforce intro!: order.trans[OF norm_blinfun] abs_le_norm_bfun mult_left_mono cSUP_mono)
    also have "\<dots> \<le> l^m * (\<Squnion>d \<in> D\<^sub>R. norm ((v - u)))"
      using norm_\<P>\<^sub>X_apply by (auto simp: \<P>\<^sub>X_const[symmetric] cSUP_least mult_left_mono)
    also have "\<dots> = l ^m * dist v u"
      by (auto simp: dist_norm)
    finally have "U\<^sub>b m v s - U\<^sub>b m u s \<le> l^m * dist v u" .
    thus ?thesis
      by (simp add: dist_real_def le)
  qed
  moreover have "U\<^sub>b m v s \<le> U\<^sub>b m u s \<Longrightarrow> dist (U\<^sub>b m v s) (U\<^sub>b m u s) \<le> l^m * dist v u" for u v s
    by (simp add: aux dist_commute)
  ultimately have "dist (U\<^sub>b m v s) (U\<^sub>b m u s) \<le> l^m * dist v u" for u v s
    using linear by blast
  thus "dist (U\<^sub>b m v) (U\<^sub>b m u) \<le> l^m * dist v u"
    by (simp add: dist_bound)
qed

lemma U\<^sub>b_conv:
  "\<exists>!v. U\<^sub>b (Suc m) v = v" 
  "(\<lambda>n. (U\<^sub>b (Suc m) ^^ n) v) \<longlonglongrightarrow> (THE v. U\<^sub>b (Suc m) v = v)"
proof -
  have *: "is_contraction (U\<^sub>b (Suc m))"
    unfolding is_contraction_def
    using U\<^sub>b_contraction[of "Suc m"] le_neq_trans[OF zero_le_disc] 
    by (cases "l = 0") (auto intro!: power_Suc_less_one intro: exI[of _ "l^(Suc m)"])
  show "\<exists>!v. U\<^sub>b (Suc m) v = v" "(\<lambda>n. (U\<^sub>b (Suc m) ^^ n) v) \<longlonglongrightarrow> (THE v. U\<^sub>b (Suc m) v = v)"
    using banach'[OF *] by auto
qed

lemma U\<^sub>b_convergent: "convergent (\<lambda>n. (U\<^sub>b (Suc m) ^^ n) v)"
  by (intro convergentI[OF U\<^sub>b_conv(2)])

lemma U\<^sub>b_mono:
  assumes "v \<le> u" 
  shows "U\<^sub>b m v \<le> U\<^sub>b m u"
proof  -
  have "U\<^sub>b m v s \<le> U\<^sub>b m u s" for s
    unfolding U\<^sub>b.rep_eq U_def
  proof (intro cSUP_mono, goal_cases)
    case 2
    thus ?case
      by (simp add: bounded_imp_bdd_above bounded_disc_\<P>\<^sub>1 bounded_plus_comp bounded_stationary_\<nu>\<^sub>b_fin)
  next
    case (3 n)
    thus ?case 
      using less_eq_bfunD[OF \<P>\<^sub>X_mono[OF assms]]
      by (auto simp: \<P>\<^sub>X_const[symmetric] blincomp_scaleR_right blinfun.scaleR_left intro!: mult_left_mono exI)
  qed auto
  thus ?thesis
    using assms by auto
qed

lemma U\<^sub>b_le_\<L>\<^sub>b: "U\<^sub>b m v \<le> (\<L>\<^sub>b ^^ m) v"
proof -
  have "U\<^sub>b m v s = (\<Squnion>d \<in> D\<^sub>R. (L d^^ m) v s)" for m v s
    by (auto simp: L_iter U\<^sub>b.rep_eq \<L>\<^sub>b.rep_eq U_def \<L>_def)
  thus ?thesis
    using L_iter_le_\<L>\<^sub>b ex_dec by (fastforce intro!: cSUP_least)
qed

lemma L_iter_le_U\<^sub>b: 
  assumes "d \<in> D\<^sub>R" 
  shows "(L d^^m) v \<le> U\<^sub>b m v"
  using assms
  by (fastforce intro!: cSUP_upper bounded_imp_bdd_above
      simp: L_iter U\<^sub>b.rep_eq U_def bounded_disc_\<P>\<^sub>1 bounded_plus_comp bounded_stationary_\<nu>\<^sub>b_fin)

lemma lim_U\<^sub>b: "lim (\<lambda>n. (U\<^sub>b (Suc m) ^^ n) v) = \<nu>\<^sub>b_opt"
proof -
  have le_U: "\<nu>\<^sub>b_opt \<le> U\<^sub>b m \<nu>\<^sub>b_opt" for m
  proof -
    obtain d where d: "\<nu>_improving \<nu>\<^sub>b_opt (mk_dec_det d)" "d \<in> D\<^sub>D"
      using ex_improving_det by auto
    have "\<nu>\<^sub>b_opt = (L (mk_dec_det d) ^^ m) \<nu>\<^sub>b_opt"
      by (induction m) (metis L_\<nu>_fix_iff \<L>\<^sub>b_opt \<nu>_improving_imp_\<L>\<^sub>b d(1) funpow_swap1)+
    thus ?thesis
      using \<open>d \<in> D\<^sub>D\<close> by (auto intro!: order.trans[OF _ L_iter_le_U\<^sub>b])
  qed
  have "U\<^sub>b m \<nu>\<^sub>b_opt \<le> \<nu>\<^sub>b_opt" for m
    using \<L>_inc_le_opt  by (auto intro!: order.trans[OF U\<^sub>b_le_\<L>\<^sub>b] simp: funpow_swap1)
  hence "U\<^sub>b (Suc m) \<nu>\<^sub>b_opt = \<nu>\<^sub>b_opt"
    using le_U by (simp add: antisym)
  moreover have "(lim (\<lambda>n. (U\<^sub>b (Suc m) ^^n) v)) = U\<^sub>b (Suc m) (lim (\<lambda>n. (U\<^sub>b (Suc m) ^^n) v))"
    using limI[OF U\<^sub>b_conv(2)] theI'[OF U\<^sub>b_conv(1)] by auto 
  ultimately show ?thesis
    using U\<^sub>b_conv(1) by metis
qed

lemma U\<^sub>b_tendsto: "(\<lambda>n. (U\<^sub>b (Suc m) ^^ n) v) \<longlonglongrightarrow> \<nu>\<^sub>b_opt"
  using lim_U\<^sub>b U\<^sub>b_convergent convergent_LIMSEQ_iff by metis

lemma U\<^sub>b_fix_unique: "U\<^sub>b (Suc m) v = v \<longleftrightarrow> v = \<nu>\<^sub>b_opt" 
  using theI'[OF U\<^sub>b_conv(1)] U\<^sub>b_conv(1)
  by (auto simp: LIMSEQ_unique[OF U\<^sub>b_tendsto U\<^sub>b_conv(2)[of m]])

lemma dist_U\<^sub>b_opt: "dist (U\<^sub>b m v) \<nu>\<^sub>b_opt \<le> l^m * dist v \<nu>\<^sub>b_opt"
proof -
  have "dist (U\<^sub>b m v) \<nu>\<^sub>b_opt = dist (U\<^sub>b m v) (U\<^sub>b m \<nu>\<^sub>b_opt)"
    by (metis U\<^sub>b.abs_eq U\<^sub>b_fix_unique U_zero apply_bfun_inverse not0_implies_Suc)
  also have "\<dots> \<le> l^m * dist v \<nu>\<^sub>b_opt"
    by (meson U\<^sub>b_contraction)
  finally show ?thesis .
qed

subsection \<open>Expressing a Single Step of Modified Policy Iteration\<close>
text \<open>The function @{term W} equals the value computed by the Modified Policy Iteration Algorithm
  in a single iteration.
  The right hand addend in the definition describes the advantage of using the optimal action for 
  the first m steps.
  \<close>
definition "W d m v = v + (\<Sum>i < m. (l *\<^sub>R \<P>\<^sub>1 d)^^i) (B\<^sub>b v)"

lemma W_eq_L_iter:
  assumes "\<nu>_improving v d"
  shows "W d m v = (L d^^m) v"
proof -
  have "(\<Sum>i<m. (l *\<^sub>R \<P>\<^sub>1 d)^^i) (\<L>\<^sub>b v) = (\<Sum>i<m. (l *\<^sub>R \<P>\<^sub>1 d)^^i) (L d v)"
    using \<nu>_improving_imp_\<L>\<^sub>b assms by auto
  hence "W d m v = v + ((\<Sum>i<m. (l *\<^sub>R \<P>\<^sub>1 d)^^i) (L d v)) - (\<Sum>i<m. (l *\<^sub>R \<P>\<^sub>1 d)^^i) v"
    by (auto simp: W_def B\<^sub>b_eq_\<L>\<^sub>b blinfun.bilinear_simps)
  also have "\<dots> = v + \<nu>\<^sub>b_fin (mk_stationary d) m + (\<Sum>i<m. ((l *\<^sub>R \<P>\<^sub>1 d)^^i) ((l *\<^sub>R \<P>\<^sub>1 d) v)) - (\<Sum>i<m. (l *\<^sub>R \<P>\<^sub>1 d)^^i) v"
    by (auto simp: L_def \<nu>\<^sub>b_fin_eq blinfun.bilinear_simps scaleR_right.sum)
  also have "\<dots> = v + \<nu>\<^sub>b_fin (mk_stationary d) m + (\<Sum>i<m. ((l *\<^sub>R \<P>\<^sub>1 d)^^Suc i) v) - (\<Sum>i<m. (l *\<^sub>R \<P>\<^sub>1 d)^^i) v"
    by (auto simp del: blinfunpow.simps simp: blinfunpow_assoc)
  also have "\<dots> = \<nu>\<^sub>b_fin (mk_stationary d) m + (\<Sum>i<Suc m. ((l *\<^sub>R \<P>\<^sub>1 d)^^ i) v)  - (\<Sum>i<m. (l *\<^sub>R \<P>\<^sub>1 d)^^ i) v"
    by (subst sum.lessThan_Suc_shift) auto
  also have "\<dots> =  \<nu>\<^sub>b_fin (mk_stationary d) m + ((l *\<^sub>R \<P>\<^sub>1 d)^^m) v"
    by (simp add: blinfun.sum_left)
  also have "\<dots> = (L d ^^ m) v"
    using L_iter by auto
  finally show ?thesis .
qed

lemma U\<^sub>b_ge: "d \<in> D\<^sub>R \<Longrightarrow> U\<^sub>b m u \<ge> \<nu>\<^sub>b_fin (mk_stationary d) m + ((l *\<^sub>R \<P>\<^sub>1 d) ^^ m) u"
  using \<nu>_improving_D_MR bounded_stationary_\<nu>\<^sub>b_fin bounded_disc_\<P>\<^sub>1
  by (fastforce intro!: diff_mono bounded_imp_bdd_above cSUP_upper bounded_plus_comp simp: U\<^sub>b.rep_eq U_def)

lemma W_le_U\<^sub>b:
  assumes "v \<le> u" "\<nu>_improving v d"
  shows "W d m v \<le> U\<^sub>b m u"
  using assms
  by (fastforce simp: W_eq_L_iter intro!: order.trans[OF L_iter_le_U\<^sub>b U\<^sub>b_mono])

lemma W_ge_\<L>\<^sub>b:
  assumes "v \<le> u" "0 \<le> B\<^sub>b u" "\<nu>_improving u d'"
  shows "\<L>\<^sub>b v \<le> W d' (Suc m) u"
proof -
  have "\<L>\<^sub>b v \<le> u + B\<^sub>b u"
    using assms(1) \<L>\<^sub>b_mono B\<^sub>b_eq_\<L>\<^sub>b by auto
  also have "\<dots> \<le> W d' (Suc m) u"
    using L_mono \<nu>_improving_imp_\<L>\<^sub>b assms(3) assms 
    by (induction m) (auto simp: W_eq_L_iter B\<^sub>b_eq_\<L>\<^sub>b)
  finally show ?thesis .
qed

lemma B\<^sub>b_le:
  assumes "\<nu>_improving v d"
  shows "B\<^sub>b v + (l *\<^sub>R \<P>\<^sub>1 d - id_blinfun) (u - v) \<le> B\<^sub>b u"
proof -
  have "r_dec\<^sub>b d + (l *\<^sub>R \<P>\<^sub>1 d - id_blinfun) u \<le> B\<^sub>b u"
    using L_def L_le_\<L>\<^sub>b assms by (auto simp: B\<^sub>b_eq_\<L>\<^sub>b \<L>\<^sub>b.rep_eq \<L>_def blinfun.bilinear_simps)
  moreover have "B\<^sub>b v = r_dec\<^sub>b d + (l *\<^sub>R \<P>\<^sub>1 d - id_blinfun) v"
    using assms by (auto simp: B\<^sub>b_eq_\<L>\<^sub>b \<nu>_improving_imp_\<L>\<^sub>b[of _ d] L_def blinfun.bilinear_simps)
  ultimately show ?thesis
    by (simp add: blinfun.diff_right)
qed


subsection \<open>Computing the Bellman Operator over Multiple Steps\<close>
definition "L_pow v d m = (L (mk_dec_det d) ^^ m) v"

(*
lemma sum_telescope': "(\<Sum>i\<le>k. f (Suc i) - f i ) = f (Suc k) - (f 0 :: 'c :: ab_group_add)"
  using sum_telescope[of "-f" k]
  by auto
*)

(* eq 6.5.7 *)
lemma L_pow_eq:
  fixes d defines "d' \<equiv> mk_dec_det d"
  assumes "\<nu>_improving v d'" 
  shows "L_pow v d m = v + (\<Sum>i < m. ((l *\<^sub>R \<P>\<^sub>1 d')^^i)) (B\<^sub>b v)"
  using L_pow_def W_def W_eq_L_iter assms by presburger

lemma L_pow_eq_W:
  assumes "d \<in> D\<^sub>D" 
  shows "L_pow v (policy_improvement d v) m = W (mk_dec_det (policy_improvement d v)) m v" 
  using assms policy_improvement_improving by (auto simp: W_eq_L_iter L_pow_def)


lemma find_policy'_is_dec_det: "is_dec_det (find_policy' v)"
  using find_policy'_def is_dec_det_def some_opt_acts_in_A by presburger

lemma find_policy'_improving: "\<nu>_improving v (mk_dec_det (find_policy' v))"
  using \<nu>_improving_opt_acts find_policy'_def by presburger

lemma L_pow_eq_W': "L_pow v (find_policy' v) m = W (mk_dec_det (find_policy' v)) m v" 
  using find_policy'_improving by (auto simp: W_eq_L_iter L_pow_def)

lemma \<L>\<^sub>b_W_ge:
  assumes "u \<le> \<L>\<^sub>b u" "\<nu>_improving u d"
  shows "W d m u \<le> \<L>\<^sub>b (W d m u)"    
proof -
  have "0 \<le> ((l *\<^sub>R \<P>\<^sub>1 d) ^^ m) (B\<^sub>b u)"
    by (metis B\<^sub>b_eq_\<L>\<^sub>b \<P>\<^sub>1_n_disc_pos assms(1) blincomp_scaleR_right diff_ge_0_iff_ge)
  also have "\<dots> = ((l *\<^sub>R \<P>\<^sub>1 d)^^0 + (\<Sum>i < m. (l *\<^sub>R \<P>\<^sub>1 d)^^(Suc i))) (B\<^sub>b u) - (\<Sum>i < m. (l *\<^sub>R \<P>\<^sub>1 d)^^ i) (B\<^sub>b u)"
    by (subst sum.lessThan_Suc_shift[symmetric]) (auto simp: blinfun.diff_left[symmetric])
  also have "\<dots> = B\<^sub>b u + ((l *\<^sub>R \<P>\<^sub>1 d - id_blinfun) o\<^sub>L (\<Sum>i < m. (l *\<^sub>R \<P>\<^sub>1 d)^^i)) (B\<^sub>b u)" 
    by (auto simp: blinfun.bilinear_simps sum_subtractf)
  also have "\<dots> = B\<^sub>b u + (l *\<^sub>R \<P>\<^sub>1 d - id_blinfun) (W d m u - u)"
    by (auto simp: W_def sum.lessThan_Suc[unfolded lessThan_Suc_atMost])
  also have "\<dots> \<le> B\<^sub>b (W d m u)"
    using B\<^sub>b_le assms(2) by blast
  finally have "0 \<le> B\<^sub>b (W d m u)" .
  thus ?thesis 
    using B\<^sub>b_eq_\<L>\<^sub>b by auto
qed

lemma L_pow_\<L>\<^sub>b_mono_inv:
  assumes "d \<in> D\<^sub>D" "v \<le> \<L>\<^sub>b v"
  shows "L_pow v (policy_improvement d v) m \<le> \<L>\<^sub>b (L_pow v (policy_improvement d v) m)"
  using assms L_pow_eq_W \<L>\<^sub>b_W_ge policy_improvement_improving by auto

lemma L_pow_\<L>\<^sub>b_mono_inv':
  assumes "v \<le> \<L>\<^sub>b v"
  shows "L_pow v (find_policy' v) m \<le> \<L>\<^sub>b (L_pow v (find_policy' v) m)"
  using assms L_pow_eq_W' \<L>\<^sub>b_W_ge find_policy'_improving by auto

subsection \<open>The Modified Policy Iteration Algorithm\<close>
context
  fixes d0 :: "'s \<Rightarrow> 'a"
  fixes v0 :: "'s \<Rightarrow>\<^sub>b real"
  fixes m :: "nat \<Rightarrow> ('s \<Rightarrow>\<^sub>b real) \<Rightarrow> nat"
  assumes d0: "d0 \<in> D\<^sub>D"
begin

text \<open>We first define a function that executes the algorithm for n steps.\<close>
fun mpi :: "nat \<Rightarrow> (('s \<Rightarrow> 'a) \<times> ('s \<Rightarrow>\<^sub>b real))" where
  "mpi 0 = (find_policy' v0, v0)" |
  "mpi (Suc n) =
  (let (d, v) = mpi n; v' = L_pow v d (Suc (m n v)) in
  (find_policy' v', v'))"

definition "mpi_val n = snd (mpi n)"
definition "mpi_pol n = fst (mpi n)"

lemma mpi_pol_zero[simp]: "mpi_pol 0 = find_policy' v0"
  unfolding mpi_pol_def 
  by auto

lemma mpi_pol_Suc: "mpi_pol (Suc n) = find_policy' (mpi_val (Suc n))"
  by (auto simp: case_prod_beta' Let_def mpi_pol_def mpi_val_def)

lemma mpi_pol_is_dec_det: "mpi_pol n \<in> D\<^sub>D"
  unfolding mpi_pol_def
  using find_policy'_is_dec_det d0
  by (induction n)  (auto simp: Let_def split: prod.splits)

lemma \<nu>_improving_mpi_pol: "\<nu>_improving (mpi_val n) (mk_dec_det (mpi_pol n))"
  using d0 find_policy'_improving mpi_pol_is_dec_det mpi_pol_Suc
  by (cases n) (auto simp: mpi_pol_def mpi_val_def)

lemma mpi_val_zero[simp]: "mpi_val 0 = v0"
  unfolding mpi_val_def by auto

lemma mpi_val_Suc: "mpi_val (Suc n) = L_pow (mpi_val n) (mpi_pol n) (Suc (m n (mpi_val n)))"
  unfolding mpi_val_def mpi_pol_def
  by (auto simp: case_prod_beta' Let_def)

lemma mpi_val_eq: "mpi_val (Suc n) = 
  mpi_val n + (\<Sum>i \<le> (m n (mpi_val n)). (l *\<^sub>R \<P>\<^sub>1 (mk_dec_det (mpi_pol n))) ^^ i) (B\<^sub>b (mpi_val n))"
  using lessThan_Suc_atMost by (auto simp: mpi_val_Suc L_pow_eq[OF \<nu>_improving_mpi_pol])

text \<open>Value Iteration is a special case of MPI where @{term "\<forall>n v. m n v = 0"}.\<close>
lemma mpi_includes_value_it: 
  assumes "\<forall>n v. m n v = 0"
  shows "mpi_val (Suc n) = \<L>\<^sub>b (mpi_val n)"
  using assms B\<^sub>b_eq_\<L>\<^sub>b mpi_val_eq by auto

subsection \<open>Convergence Proof\<close>
text \<open>We define the sequence @{term w} as an upper bound for the values of MPI.\<close>
fun w where
  "w 0 = v0" |
  "w (Suc n) = U\<^sub>b (Suc (m n (mpi_val n))) (w n)"

lemma dist_\<nu>\<^sub>b_opt: "dist (w (Suc n)) \<nu>\<^sub>b_opt \<le> l * dist (w n) \<nu>\<^sub>b_opt"
  by (fastforce simp: algebra_simps intro: order.trans[OF dist_U\<^sub>b_opt] mult_left_mono power_le_one
      mult_left_le_one_le order.strict_implies_order)

lemma dist_\<nu>\<^sub>b_opt_n: "dist (w n) \<nu>\<^sub>b_opt \<le> l^n * dist v0 \<nu>\<^sub>b_opt"
  by (induction n) (fastforce simp: algebra_simps intro: order.trans[OF dist_\<nu>\<^sub>b_opt] mult_left_mono)+

lemma w_conv: "w \<longlonglongrightarrow> \<nu>\<^sub>b_opt"
proof -
  have "(\<lambda>n. l^n * dist v0 \<nu>\<^sub>b_opt) \<longlonglongrightarrow> 0"
    using LIMSEQ_realpow_zero by (cases "v0 = \<nu>\<^sub>b_opt") auto
  then show ?thesis
    by (fastforce intro: metric_LIMSEQ_I order.strict_trans1[OF dist_\<nu>\<^sub>b_opt_n] simp: LIMSEQ_def)
qed

text \<open>MPI converges monotonically to the optimal value from below. 
  The iterates are sandwiched between @{const \<L>\<^sub>b} from below and @{const U\<^sub>b} from above.\<close>
theorem mpi_conv:
  assumes "v0 \<le> \<L>\<^sub>b v0"
  shows "mpi_val \<longlonglongrightarrow> \<nu>\<^sub>b_opt" and "\<And>n. mpi_val n \<le> mpi_val (Suc n)"
proof -
  define y where "y n = (\<L>\<^sub>b^^n) v0" for n
  have aux: "mpi_val n \<le> \<L>\<^sub>b (mpi_val n) \<and> mpi_val n \<le> mpi_val (Suc n) \<and> y n \<le> mpi_val n \<and> mpi_val n \<le> w n" for n
  proof (induction n)
    case 0
    show ?case
      using assms B\<^sub>b_eq_\<L>\<^sub>b
      unfolding y_def
      by (auto simp: mpi_val_eq blinfun.sum_left \<P>\<^sub>1_n_disc_pos blincomp_scaleR_right sum_nonneg)
  next
    case (Suc n)
    have val_eq_W: "mpi_val (Suc n) = W (mk_dec_det (mpi_pol n)) (Suc (m n (mpi_val n))) (mpi_val n)"
      using \<nu>_improving_mpi_pol mpi_val_Suc W_eq_L_iter L_pow_def by auto
    hence *: "mpi_val (Suc n) \<le> \<L>\<^sub>b (mpi_val (Suc n))"
      using Suc.IH \<L>\<^sub>b_W_ge \<nu>_improving_mpi_pol by presburger
    moreover have "mpi_val (Suc n) \<le> mpi_val (Suc (Suc n))"
      using *
      by (simp add: B\<^sub>b_eq_\<L>\<^sub>b mpi_val_eq \<P>\<^sub>1_n_disc_pos blincomp_scaleR_right blinfun.sum_left sum_nonneg)
    moreover have "mpi_val (Suc n) \<le> w (Suc n)"
      using Suc.IH \<nu>_improving_mpi_pol by (auto simp: val_eq_W intro: order.trans[OF _ W_le_U\<^sub>b])
    moreover have "y (Suc n) \<le> mpi_val (Suc n)"
      using Suc.IH \<nu>_improving_mpi_pol W_ge_\<L>\<^sub>b by (auto simp: y_def B\<^sub>b_eq_\<L>\<^sub>b val_eq_W)
    ultimately show ?case
      by auto
  qed
  thus "mpi_val n \<le> mpi_val (Suc n)" for n
    by auto
  have "y \<longlonglongrightarrow> \<nu>\<^sub>b_opt"
    using \<L>\<^sub>b_lim y_def by presburger
  thus "mpi_val \<longlonglongrightarrow> \<nu>\<^sub>b_opt"
    using aux by (auto intro: tendsto_bfun_sandwich[OF _ w_conv])
qed

subsection \<open>$\epsilon$-Optimality\<close>
text \<open>This gives an upper bound on the error of MPI.\<close>
lemma mpi_pol_eps_opt:
  assumes "2 * l * dist (mpi_val n) (\<L>\<^sub>b (mpi_val n)) < eps * (1 - l)" "eps > 0"
  shows "dist (\<nu>\<^sub>b (mk_stationary_det (mpi_pol n))) (\<L>\<^sub>b (mpi_val n)) \<le> eps / 2"
proof -
  let ?p = "mk_stationary_det (mpi_pol n)"
  let ?d = "mk_dec_det (mpi_pol n)"
  let ?v = "mpi_val n"
  have "dist (\<nu>\<^sub>b ?p) (\<L>\<^sub>b ?v) = dist (L ?d (\<nu>\<^sub>b ?p)) (\<L>\<^sub>b ?v)"
    using L_\<nu>_fix by force
  also have "\<dots> = dist (L ?d (\<nu>\<^sub>b ?p)) (L ?d ?v)"
    by (metis \<nu>_improving_imp_\<L>\<^sub>b \<nu>_improving_mpi_pol)
  also have "\<dots> \<le> dist (L ?d (\<nu>\<^sub>b ?p)) (L ?d (\<L>\<^sub>b ?v)) + dist (L ?d (\<L>\<^sub>b ?v)) (L ?d ?v)"
    using dist_triangle by blast
  also have "\<dots> \<le> l * dist (\<nu>\<^sub>b ?p) (\<L>\<^sub>b ?v) + dist (L ?d (\<L>\<^sub>b ?v)) (L ?d ?v)"
    using contraction_L by auto
  also have "\<dots> \<le> l * dist (\<nu>\<^sub>b ?p) (\<L>\<^sub>b ?v) + l * dist (\<L>\<^sub>b ?v) ?v"
    using contraction_L by auto
  finally have "dist (\<nu>\<^sub>b ?p) (\<L>\<^sub>b ?v) \<le> l * dist (\<nu>\<^sub>b ?p) (\<L>\<^sub>b ?v) + l * dist (\<L>\<^sub>b ?v) ?v".
  hence *:"(1-l) * dist (\<nu>\<^sub>b ?p) (\<L>\<^sub>b ?v) \<le> l * dist (\<L>\<^sub>b ?v) ?v"
    by (auto simp: left_diff_distrib)
  thus ?thesis
  proof (cases "l = 0")
    case True
    thus ?thesis
      using assms * by auto
  next
    case False
    have **: "dist (\<L>\<^sub>b ?v) (mpi_val n) < eps * (1 - l) / (2 * l)"
      using False le_neq_trans[OF zero_le_disc False[symmetric]] assms
      by (auto simp: dist_commute pos_less_divide_eq Groups.mult_ac(2))
    have "dist (\<nu>\<^sub>b ?p) (\<L>\<^sub>b ?v) \<le> (l/ (1-l)) * dist (\<L>\<^sub>b ?v) ?v"
      using * by (auto simp: mult.commute pos_le_divide_eq)
    also have "\<dots> \<le> (l/ (1-l)) * (eps * (1 - l) / (2 * l))"
      using ** by (fastforce intro!: mult_left_mono simp: divide_nonneg_pos)
    also have "\<dots> = eps / 2"
      using False disc_lt_one by (auto simp: order.strict_iff_order)
    finally show "dist (\<nu>\<^sub>b ?p) (\<L>\<^sub>b ?v) \<le> eps / 2".    
  qed
qed

lemma mpi_pol_opt:
  assumes "2 * l * dist (mpi_val n) (\<L>\<^sub>b (mpi_val n)) < eps * (1 - l)" "eps > 0"
  shows "dist (\<nu>\<^sub>b (mk_stationary_det (mpi_pol n))) (\<nu>\<^sub>b_opt) < eps"
proof -
  have "dist (\<nu>\<^sub>b (mk_stationary_det (mpi_pol n))) (\<nu>\<^sub>b_opt) \<le> eps/2 + dist (\<L>\<^sub>b (mpi_val n)) \<nu>\<^sub>b_opt"
    by (metis mpi_pol_eps_opt[OF assms] dist_commute dist_triangle_le add_right_mono)
  thus ?thesis
    using dist_\<L>\<^sub>b_opt_eps assms by fastforce
qed

lemma mpi_val_term_ex:
  assumes "v0 \<le> \<L>\<^sub>b v0" "eps > 0"
  shows "\<exists>n. 2 * l * dist (mpi_val n) (\<L>\<^sub>b (mpi_val n)) < eps * (1 - l)"
proof -
  have "(\<lambda>n. dist (mpi_val n) \<nu>\<^sub>b_opt) \<longlonglongrightarrow> 0"
    using mpi_conv(1)[OF assms(1)] tendsto_dist_iff 
    by blast
  hence "(\<lambda>n. dist (mpi_val n) (\<L>\<^sub>b (mpi_val n))) \<longlonglongrightarrow> 0"
    using dist_\<L>\<^sub>b_lt_dist_opt
    by (auto simp: metric_LIMSEQ_I intro: tendsto_sandwich[of "\<lambda>_. 0" _ _ "\<lambda>n. 2 * dist (mpi_val n) \<nu>\<^sub>b_opt"])
  hence "\<forall>e >0. \<exists>n. dist (mpi_val n) (\<L>\<^sub>b (mpi_val n)) < e"
    by (fastforce dest!: metric_LIMSEQ_D)
  hence "l \<noteq> 0 \<Longrightarrow> \<exists>n. dist (mpi_val n) (\<L>\<^sub>b (mpi_val n)) < eps * (1 - l) / (2 * l)"
    by (simp add: assms order.not_eq_order_implies_strict)
  thus "\<exists>n. (2 * l) * dist (mpi_val n) (\<L>\<^sub>b (mpi_val n)) < eps * (1 - l)"
    using assms le_neq_trans[OF zero_le_disc]
    by (cases "l = 0") (auto simp: mult.commute pos_less_divide_eq)
qed
end

subsection \<open>Unbounded MPI\<close>
context
  fixes eps \<delta> :: real and M :: nat
begin

function (domintros) mpi_algo where "mpi_algo d v m = (
  if 2 * l * dist v (\<L>\<^sub>b v) <  eps * (1 - l)
  then (find_policy' v, v)
  else mpi_algo (find_policy' v) (L_pow v (find_policy' v) (Suc (m 0 v))) (\<lambda>n. m (Suc n)))"
  by auto

text \<open>We define a tailrecursive version of @{const mpi} which more closely resembles @{const mpi_algo}.\<close>
fun mpi' where
  "mpi' d v 0 m = (find_policy' v, v)" |
  "mpi' d v (Suc n) m = (
  let d' = find_policy' v; v' = L_pow v d' (Suc (m 0 v)) in mpi' d' v' n (\<lambda>n. m (Suc n)))"

lemma mpi_Suc':
  assumes "d \<in> D\<^sub>D"
  shows "mpi v m (Suc n) = mpi (L_pow v (find_policy' v) (Suc (m 0 v))) (\<lambda>a. m (Suc a)) n"
  using assms
  by (induction n rule: nat.induct) (auto simp: Let_def)

lemma
  assumes "d \<in> D\<^sub>D"
  shows "mpi v m n = mpi' d v n m"
  using assms
proof (induction n arbitrary: d v m rule: nat.induct)
  case (Suc nat)
  thus ?case
    using find_policy'_is_dec_det by (fastforce simp: Let_def mpi_Suc'[OF Suc(2)])
qed auto

lemma termination_mpi_algo: 
  assumes "eps > 0" "d \<in> D\<^sub>D" "v \<le> \<L>\<^sub>b v"
  shows "mpi_algo_dom (d, v, m)"
proof -
  define n where "n = (LEAST n. 2 * l * dist (mpi_val v m n) (\<L>\<^sub>b (mpi_val v m n)) < eps * (1 - l))" (is "n = (LEAST n. ?P d v m n)")
  have least0: "\<exists>n. P n \<Longrightarrow> (LEAST n. P n) = (0 :: nat) \<Longrightarrow> P 0"  for P
    by (metis LeastI_ex)
  from n_def assms show ?thesis
  proof (induction n arbitrary: v d m)
    case 0
    have "2 * l * dist (mpi_val v m 0) (\<L>\<^sub>b (mpi_val v m 0)) < eps * (1 - l)"
      using least0 mpi_val_term_ex 0 by (metis (no_types, lifting))
    thus ?case
      using 0 mpi_algo.domintros mpi_val_zero by (metis (no_types, opaque_lifting))
  next
    case (Suc n v d m)
    let ?d = "find_policy' v"
    have "Suc n = Suc (LEAST n. 2 * l * dist (mpi_val v m (Suc n)) (\<L>\<^sub>b (mpi_val v m (Suc n))) < eps * (1 - l))"
      using mpi_val_term_ex[OF Suc.prems(3) \<open>v \<le> \<L>\<^sub>b v\<close> \<open>0 < eps\<close>, of m] Suc.prems 
      by (subst Nat.Least_Suc[symmetric]) (auto intro: LeastI_ex)
    hence "n = (LEAST n. 2 * l * dist (mpi_val v m (Suc n)) (\<L>\<^sub>b (mpi_val v m (Suc n))) < eps * (1 - l))"
      by auto
    hence n_eq: "n =
    (LEAST n. 2 * l * dist (mpi_val (L_pow v ?d (Suc (m 0 v))) (\<lambda>a. m (Suc a)) n) (\<L>\<^sub>b (mpi_val (L_pow v ?d (Suc (m 0 v))) (\<lambda>a. m (Suc a)) n))
        < eps * (1 - l))"
      using Suc.prems mpi_Suc' by (auto simp: is_dec_det_pi mpi_val_def)
    have "\<not> 2 * l * dist v (\<L>\<^sub>b v) < eps * (1 - l)"
      using Suc mpi_val_zero by force
    moreover have "mpi_algo_dom (?d, L_pow v ?d (Suc (m 0 v)), \<lambda>a. m (Suc a))"
      apply (rule Suc.IH[OF n_eq \<open>0 < eps\<close>])
          using Suc.prems is_dec_det_pi L_pow_\<L>\<^sub>b_mono_inv' find_policy'_is_dec_det by auto
    ultimately show ?case
      using mpi_algo.domintros by blast
  qed
qed

abbreviation "mpi_alg_rec d v m \<equiv> 
    (if 2 * l * dist v (\<L>\<^sub>b v) < eps * (1 - l) then (find_policy' v, v)
     else mpi_algo (find_policy' v) (L_pow v (find_policy' v) (Suc (m 0 v)))
           (\<lambda>n. m (Suc n)))"

lemma mpi_algo_def':
  assumes "d \<in> D\<^sub>D" "v \<le> \<L>\<^sub>b v" "eps > 0"
  shows "mpi_algo d v m = mpi_alg_rec d v m"
  using mpi_algo.psimps termination_mpi_algo assms by auto


lemma mpi_algo_def'':
  assumes "d \<in> D\<^sub>D" "v \<le> \<L>\<^sub>b v" "eps > 0"
  shows "mpi_algo d v m = (
  let v' = \<L>\<^sub>b v; d' = find_policy' v in
    if 2 * l * dist v v'  < eps * (1 - l) 
    then (d', v)
    else mpi_algo d' (L_pow v' d' ((m 0 v))) (\<lambda>n. m (Suc n)))"
proof -
  have "\<nu>_improving v (mk_dec_det (find_policy' v))"
    using \<nu>_improving_opt_acts find_policy'_def by presburger
  hence aux: "L_pow (\<L>\<^sub>b v) (find_policy' v) n = L_pow v (find_policy' v) (Suc n)" for n
    using \<open>d \<in> D\<^sub>D\<close>  \<nu>_improving_imp_\<L>\<^sub>b
    by (auto simp: funpow_swap1 L_pow_def)
  show ?thesis
    unfolding mpi_algo_def'[OF assms] Let_def aux[symmetric] by auto
qed

lemma mpi_algo_eq_mpi:
  assumes "d \<in> D\<^sub>D" "v \<le> \<L>\<^sub>b v" "eps > 0"
  shows "mpi_algo d v m = mpi v m (LEAST n. 2 * l * dist (mpi_val v m n) (\<L>\<^sub>b (mpi_val v m n)) < eps * (1 - l))"
proof -
  define n where "n = (LEAST n. 2 * l * dist (mpi_val v m n) (\<L>\<^sub>b (mpi_val v m n)) < eps * (1 - l))" (is "n = (LEAST n. ?P d v m n)")
  from n_def assms show ?thesis
  proof (induction n arbitrary: d v m)
    case 0
    have "?P d v m 0"
      by (metis (no_types, lifting) assms(3) LeastI_ex 0 mpi_val_term_ex)
    thus ?case
      using assms 0 by (auto simp: mpi_val_def mpi_algo_def')
  next
    case (Suc n)
    hence not0: "\<not> (2 * l * dist v (\<L>\<^sub>b v) < eps * (1 - l))"
      using Suc(3) mpi_val_zero by auto
    obtain n' where "2 * l * dist (mpi_val v m n') (\<L>\<^sub>b (mpi_val v m n')) < eps * (1 - l)"
      using mpi_val_term_ex[OF Suc(3) Suc(4), of _ m] assms by blast
    hence "n = (LEAST n. ?P d v m (Suc n))"
      using Suc(2) Suc by (subst (asm) Least_Suc) auto
    hence "n = (LEAST n. ?P (find_policy' v) (L_pow v (find_policy' v) (Suc (m 0 v))) (\<lambda>n. m (Suc n)) n)"
      using Suc(3)  mpi_Suc' by (auto simp: mpi_val_def)
    hence "mpi_algo d v m = mpi v m (Suc n)"
      unfolding mpi_algo_def'[OF Suc.prems(2-4)]
      using Suc(1) Suc.prems(2-4) is_dec_det_pi mpi_Suc' not0 L_pow_\<L>\<^sub>b_mono_inv' find_policy'_is_dec_det
      by fastforce
    thus ?case
      using Suc.prems(1) by presburger
  qed
qed

lemma mpi_algo_opt: 
  assumes "v0 \<le> \<L>\<^sub>b v0" "eps > 0" "d \<in> D\<^sub>D"
  shows "dist (\<nu>\<^sub>b (mk_stationary_det (fst (mpi_algo d v0 m)))) \<nu>\<^sub>b_opt < eps"
proof -
  let ?P = "\<lambda>n. 2 * l * dist (mpi_val v0 m n) (\<L>\<^sub>b (mpi_val v0 m n)) <  eps * (1 - l)"
  let ?n = "Least ?P"
  have "mpi_algo d v0 m = mpi v0 m ?n" and "?P ?n"
    using mpi_algo_eq_mpi LeastI_ex[OF mpi_val_term_ex] assms by auto
  thus ?thesis
    using assms by (auto simp: mpi_pol_opt mpi_pol_def[symmetric])
qed

end

subsection \<open>Initial Value Estimate @{term v0_mpi}\<close>
text \<open>We define an initial estimate of the value function for which Modified Policy Iteration 
  always terminates.\<close>

abbreviation "r_min \<equiv> (\<Sqinter>s'. (\<Sqinter>a \<in> A s'. r (s', a)))"
definition "v0_mpi s = r_min / (1 - l)"

lift_definition v0_mpi\<^sub>b :: "'s \<Rightarrow>\<^sub>b real" is "v0_mpi"
  by (auto simp: v0_mpi_def)

lemma v0_mpi\<^sub>b_le_\<L>\<^sub>b: "v0_mpi\<^sub>b \<le> \<L>\<^sub>b v0_mpi\<^sub>b"
proof (rule less_eq_bfunI)
  fix x
  have bounded_r': "bounded ((\<lambda>a. r (x, a)) ` A x)" for x
    using r_bounded'
    unfolding bounded_def
    by simp (meson UNIV_I)
  have *: "(\<Sqinter>a\<in>A x. r (x, a)) \<le> r (x,a)" if "a \<in> A x" for  a x
    using  bounded_r' that 
    by (auto intro!: cInf_lower bounded_imp_bdd_below)
  have ****: "r (s,a) \<le> r\<^sub>M" for s a
    using abs_le_iff abs_r_le_r\<^sub>M by blast
  have **: "bounded (range (\<lambda>s'. \<Sqinter>a\<in>A s'. r (s', a)))"
    using abs_r_le_r\<^sub>M  ex_dec_det is_dec_det_def A_ne
    by (auto simp add: minus_le_iff abs_le_iff intro!: cINF_greatest order.trans[OF *]  boundedI[of _ "r\<^sub>M"])
  have "r_min \<le> r (s, a)" if "a \<in> A s" for s a
    using  r_bounded' that **
    by (auto intro!: bounded_imp_bdd_below cInf_lower2[OF _ *])
  
    hence "r_min \<le> (1-l) * r (s, a) + l * r_min" if "a \<in> A s" for s a
    using disc_lt_one zero_le_disc that by (meson order_less_imp_le order_refl segment_bound_lemma)
  hence "r_min / (1 - l) \<le> ((1-l) * r (s, a) + l * r_min) / (1 - l)" if "a \<in> A s" for s a
    using order_less_imp_le[OF disc_lt_one] that  by (auto intro!: divide_right_mono)
  hence "r_min / (1 - l) \<le> r (s, a) + (l * r_min) / (1 - l)" if "a \<in> A s" for s a
    using disc_lt_one that by (auto simp: add_divide_distrib)
  hence "r_min / (1 - l) \<le> L\<^sub>a (arb_act (A x)) (\<lambda>s. r_min / (1 - l)) x"
    using A_ne arb_act_in by auto
  moreover have "bdd_above ((\<lambda>a. L\<^sub>a a (\<lambda>s. r_min / (1 - l)) x) ` A x)"
    using r_bounded
    by (fastforce simp: bounded_def intro!: bounded_imp_bdd_above bounded_plus_comp)
  ultimately show "v0_mpi\<^sub>b x \<le> \<L>\<^sub>b v0_mpi\<^sub>b x"
    unfolding \<L>\<^sub>b_eq_SUP_L\<^sub>a' v0_mpi\<^sub>b.rep_eq v0_mpi_def by (auto simp: A_ne intro!: cSUP_upper2)
qed

subsection \<open>An Instance of Modified Policy Iteration with a Valid Conservative Initial Value Estimate\<close>
definition "mpi_user eps m = (
  if eps \<le> 0 then undefined else mpi_algo eps (\<lambda>x. arb_act (A x)) v0_mpi\<^sub>b m)"

lemma mpi_user_eq:
  assumes "eps > 0"
  shows "mpi_user eps = mpi_alg_rec eps (\<lambda>x. arb_act (A x)) v0_mpi\<^sub>b"
  using v0_mpi\<^sub>b_le_\<L>\<^sub>b assms
  by (auto simp: mpi_user_def mpi_algo_def' A_ne is_dec_det_def)

lemma mpi_user_opt:
  assumes "eps > 0"
  shows "dist (\<nu>\<^sub>b (mk_stationary_det (fst (mpi_user eps n)))) \<nu>\<^sub>b_opt < eps"
  unfolding mpi_user_def using assms
  by (auto intro: mpi_algo_opt simp: is_dec_det_def A_ne v0_mpi\<^sub>b_le_\<L>\<^sub>b)
end


end