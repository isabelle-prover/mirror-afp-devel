theory Policy_Iteration_Fin
  imports 
    Policy_Iteration 
    MDP_fin 
    Blinfun_To_Matrix
begin

context MDP_nat_disc begin

lemma finite_D\<^sub>D[simp]: "finite D\<^sub>D"
proof -
  let ?set = "{d. \<forall>x :: nat. (x \<in> {0..<states} \<longrightarrow> d x \<in> (\<Union>s\<in>{0..<states}. A s)) \<and> (x \<notin> {0..<states} \<longrightarrow> d x = 0)}"
  have "finite (\<Union>s<states. A s)"
    using A_fin by auto
  hence "finite ?set"
    by (intro finite_set_of_finite_funs) auto
  moreover have "D\<^sub>D \<subseteq> ?set"
    unfolding is_dec_det_def
    using A_outside
    by (auto simp: not_less)
  ultimately show ?thesis
    using finite_subset 
    by auto
qed

lemma finite_rel: "finite {(u, v). is_dec_det u \<and> is_dec_det v \<and> \<nu>\<^sub>b (mk_stationary_det u) > \<nu>\<^sub>b (mk_stationary_det v)}"
proof-
  have aux: "finite {(u, v). is_dec_det u \<and> is_dec_det v}"
    by auto
  show ?thesis
    by (auto intro: finite_subset[OF _ aux])
qed

lemma eval_eq_imp_policy_eq: 
  assumes "policy_eval d = policy_eval (policy_step d)" "is_dec_det d"
  shows "d = policy_step d"
proof -
  have "policy_eval d s = policy_eval (policy_step d) s" for s
    using assms 
    by auto
  have "policy_eval d = L (mk_dec_det d) (policy_eval (policy_step d))"
    unfolding policy_eval_def
    using L_\<nu>_fix 
    by (auto simp: assms(1)[symmetric, unfolded policy_eval_def])
  hence "policy_eval d = \<L>\<^sub>b (policy_eval d)"
    by (metis L_\<nu>_fix policy_eval_def assms eval_policy_step_L)
  hence "L (mk_dec_det d) (policy_eval d) s = \<L>\<^sub>b (policy_eval d) s" for s
    using \<open>policy_eval d = L (mk_dec_det d) (policy_eval (policy_step d))\<close> assms(1) by auto
  hence "is_arg_max (\<lambda>a. L\<^sub>a a (\<nu>\<^sub>b (mk_stationary (mk_dec_det d))) s) (\<lambda>a. a \<in> A s) (d s)" for s
    unfolding L_eq_L\<^sub>a_det
    unfolding policy_eval_def \<L>\<^sub>b.rep_eq \<L>_eq_SUP_det SUP_step_det_eq
    using assms(2) is_dec_det_def L\<^sub>a_le
    by (auto simp del: \<nu>\<^sub>b.rep_eq simp: \<nu>\<^sub>b.rep_eq[symmetric] 
        intro!: SUP_is_arg_max boundedI[of _ "r\<^sub>M + l * norm _"] bounded_imp_bdd_above)
  thus ?thesis
    unfolding policy_eval_def policy_step_def policy_improvement_def
    by auto
qed


termination policy_iteration
proof (relation "{(u, v). u \<in> D\<^sub>D \<and> v \<in> D\<^sub>D \<and> \<nu>\<^sub>b (mk_stationary_det u) > \<nu>\<^sub>b (mk_stationary_det v)}")
  show "wf {(u, v). u \<in> D\<^sub>D \<and> v \<in> D\<^sub>D \<and> \<nu>\<^sub>b (mk_stationary_det v) < \<nu>\<^sub>b (mk_stationary_det u)}"
    using finite_rel 
    by (auto intro!: finite_acyclic_wf acyclicI_order)
next
  fix d x
  assume h: "x = policy_step d" "\<not> (d = x \<or> \<not> is_dec_det d)"
  have "is_dec_det d \<Longrightarrow> \<nu>\<^sub>b (mk_stationary_det d) \<le> \<nu>\<^sub>b (mk_stationary_det (policy_step d))"
    using policy_eval_mon  
    by (simp add: policy_eval_def)
  hence "is_dec_det d \<Longrightarrow> d \<noteq> policy_step d \<Longrightarrow>
    \<nu>\<^sub>b (mk_stationary_det d) < \<nu>\<^sub>b (mk_stationary_det (policy_step d))"
    using eval_eq_imp_policy_eq policy_eval_def
    by (force intro!: order.not_eq_order_implies_strict)
  thus "(x, d) \<in> {(u, v). u \<in> D\<^sub>D \<and> v \<in> D\<^sub>D \<and> \<nu>\<^sub>b (mk_stationary_det v) < \<nu>\<^sub>b (mk_stationary_det u)}"
    using is_dec_det_pi policy_step_def h 
    by auto
qed

lemma is_dec_det_pi': "d \<in> D\<^sub>D \<Longrightarrow> is_dec_det (policy_iteration d)"
  using is_dec_det_pi
  by (induction d rule: policy_iteration.induct) (auto simp: Let_def policy_step_def)

lemma pi_pi[simp]: "d \<in> D\<^sub>D \<Longrightarrow> policy_step (policy_iteration d) = policy_iteration d"
  using is_dec_det_pi
  by (induction d rule: policy_iteration.induct) (auto simp: policy_step_def Let_def)

lemma policy_iteration_correct: 
  "d \<in> D\<^sub>D \<Longrightarrow> \<nu>\<^sub>b (mk_stationary_det (policy_iteration d)) = \<nu>\<^sub>b_opt" 
  by (induction d rule: policy_iteration.induct)
    (fastforce intro!: policy_step_eq_imp_opt is_dec_det_pi' simp del: policy_iteration.simps)

lemma \<nu>\<^sub>b_zero_notin:  "s \<ge> states \<Longrightarrow> \<nu>\<^sub>b p s = 0"
  using  \<nu>_zero_notin unfolding \<nu>\<^sub>b.rep_eq by auto  

lemma r_dec\<^sub>b_zero_notin:  "s \<ge> states \<Longrightarrow> r_dec\<^sub>b d s = 0"
  using reward_zero_outside
  by auto

lemma \<nu>\<^sub>b_eq_inv: "\<nu>\<^sub>b (mk_stationary d) = inv\<^sub>L (id_blinfun - l *\<^sub>R \<P>\<^sub>1 d) (r_dec\<^sub>b d)"
  using \<nu>_stationary_inv.

lemma \<nu>\<^sub>b_eq_bfun_if: "\<nu>\<^sub>b (mk_stationary d) = bfun_if (\<lambda>i. i < states) (\<nu>\<^sub>b (mk_stationary d)) 0"
  using \<nu>\<^sub>b_zero_notin by (auto simp: bfun_if.rep_eq)

lemma \<nu>\<^sub>b_vec_aux: "((1\<^sub>m states) - l \<cdot>\<^sub>m (blinfun_to_mat states states (\<P>\<^sub>1 d))) *\<^sub>v bfun_to_vec states (\<nu>\<^sub>b (mk_stationary d)) = bfun_to_vec states (r_dec\<^sub>b d)"
proof -
  let ?to_mat = "blinfun_to_mat states states"
  let ?to_vec = "bfun_to_vec states"

  have "((1\<^sub>m states) - l \<cdot>\<^sub>m (?to_mat (\<P>\<^sub>1 d))) *\<^sub>v ?to_vec (\<nu>\<^sub>b (mk_stationary d)) =
      ((1\<^sub>m states) - ?to_mat (l *\<^sub>R (\<P>\<^sub>1 d))) *\<^sub>v ?to_vec (\<nu>\<^sub>b (mk_stationary d))"
    using blinfun_to_mat_scale by fastforce
  also have "\<dots> = (?to_mat id_blinfun - ?to_mat (l *\<^sub>R (\<P>\<^sub>1 d))) *\<^sub>v ?to_vec (\<nu>\<^sub>b (mk_stationary d))"
    using blinfun_to_mat_id by presburger
  also have "\<dots> = ?to_mat (id_blinfun - l *\<^sub>R \<P>\<^sub>1 d) *\<^sub>v ?to_vec (\<nu>\<^sub>b (mk_stationary d))"
    using blinfun_to_mat_sub by presburger
  also have "\<dots> = ?to_vec ((id_blinfun - l *\<^sub>R \<P>\<^sub>1 d) ((\<nu>\<^sub>b (mk_stationary d))))"
    unfolding blinfun_to_mat_mult using \<nu>\<^sub>b_eq_bfun_if by auto
  also have "\<dots> = ?to_vec (r_dec\<^sub>b d)"
    by (metis L_\<nu>_fix_iff L_def blinfun.diff_left blinfun.scaleR_left diff_eq_eq id_blinfun.rep_eq)
  finally show ?thesis.
qed

lemma summable_geom_\<P>\<^sub>1: "summable (\<lambda>k. ((l *\<^sub>R \<P>\<^sub>1 d)^^k))"
  using summable_inv_Q norm_\<P>\<^sub>1
  by (metis add_diff_cancel_left' diff_add_cancel norm_\<P>\<^sub>1_l_less)

lemma summable_geom_\<P>\<^sub>1': "summable (\<lambda>k. ((l *\<^sub>R \<P>\<^sub>1 d)^^k) v)" for v
  using  summable_geom_\<P>\<^sub>1 tendsto_blinfun_apply
  unfolding summable_def sums_def
  by (fastforce simp: blinfun.sum_left)
  
lemma summable_geom_\<P>\<^sub>1'': "summable (\<lambda>k. ((l *\<^sub>R \<P>\<^sub>1 d)^^k) v s)" for v s
  using summable_geom_\<P>\<^sub>1' bfun_tendsto_apply_bfun
    unfolding summable_def sums_def
    by (fastforce simp: sum_apply_bfun)

lemma K_closed': "s<states \<Longrightarrow> j \<in> set_pmf (K (s, a)) \<Longrightarrow> j < states"
  by (meson K_closed atLeastLessThan_iff basic_trans_rules(31))

lemma \<P>\<^sub>1_indep:
  assumes "(\<And>i. i < states \<Longrightarrow> apply_bfun v i = apply_bfun v' i)" "j < states"
  shows "(l *\<^sub>R \<P>\<^sub>1 d) v j = (l *\<^sub>R \<P>\<^sub>1 d) v' j"
  using assms K_closed'[OF assms(2)]
  by (auto simp: blinfun.scaleR_left \<P>\<^sub>1.rep_eq K_st_def intro!: integral_cong_AE AE_pmfI)

lemma inv\<^sub>L_indep: 
  assumes "\<And>i. i < states \<Longrightarrow> apply_bfun v i = apply_bfun v' i" "j < states" 
  shows "((inv\<^sub>L (id_blinfun - l *\<^sub>R \<P>\<^sub>1 d)) v) j = ((inv\<^sub>L (id_blinfun - l *\<^sub>R \<P>\<^sub>1 d)) v') j"
proof -
  have "((l *\<^sub>R \<P>\<^sub>1 d) ^^ n) v j = ((l *\<^sub>R \<P>\<^sub>1 d) ^^ n) v' j" for n
    using assms \<P>\<^sub>1_indep by (induction n arbitrary: j v v') fastforce+
  thus ?thesis
    using summable_geom_\<P>\<^sub>1 summable_geom_\<P>\<^sub>1'
    by (auto simp: inv\<^sub>L_inf_sum blinfun_apply_suminf[symmetric] suminf_apply_bfun)
qed

lemma vec_\<nu>\<^sub>b: "bfun_to_vec states (\<nu>\<^sub>b (mk_stationary d)) = 
    inverse_mat ((1\<^sub>m states) - l \<cdot>\<^sub>m (blinfun_to_mat states states (\<P>\<^sub>1 d))) *\<^sub>v (bfun_to_vec states (r_dec\<^sub>b d))"
proof -
  have "bfun_to_vec states (\<nu>\<^sub>b (mk_stationary d)) = bfun_to_vec states (inv\<^sub>L (id_blinfun - l *\<^sub>R \<P>\<^sub>1 d) (r_dec\<^sub>b d))"
    using \<nu>\<^sub>b_eq_inv by force
  also have "\<dots> = bfun_to_vec states (inv\<^sub>L (id_blinfun - l *\<^sub>R \<P>\<^sub>1 d) (bfun_if (\<lambda>i. i < states) (r_dec\<^sub>b d) 0))"
    using r_dec\<^sub>b_zero_notin
    by (subst bfun_if_eq) auto    
  also have "\<dots> = blinfun_to_mat states states (inv\<^sub>L (id_blinfun - l *\<^sub>R \<P>\<^sub>1 d)) *\<^sub>v (bfun_to_vec states (r_dec\<^sub>b d))"
    using blinfun_to_mat_mult..
  also have "\<dots> = inverse_mat (blinfun_to_mat states states (id_blinfun - l *\<^sub>R \<P>\<^sub>1 d)) *\<^sub>v (bfun_to_vec states (r_dec\<^sub>b d))"
       using inv\<^sub>L_indep \<P>\<^sub>1_indep
       by (fastforce simp add: inverse_blinfun_to_mat  invertible\<^sub>L_inf_sum blinfun.diff_left)+
  finally show ?thesis
    using blinfun_to_mat_id blinfun_to_mat_scale blinfun_to_mat_sub by presburger
qed


lemma invertible_\<nu>\<^sub>b_mat: "invertible_mat ((1\<^sub>m states) - l \<cdot>\<^sub>m (blinfun_to_mat states states (\<P>\<^sub>1 d)))"
proof -
  have "invertible_mat (blinfun_to_mat states states ((id_blinfun - l *\<^sub>R \<P>\<^sub>1 d)))"
    using \<P>\<^sub>1_indep inv\<^sub>L_indep 
    by (fastforce simp: invertible\<^sub>L_inf_sum blinfun.diff_left intro!: inverse_blinfun_to_mat(2))+
  thus ?thesis
    by (auto simp: blinfun_to_mat_id blinfun_to_mat_sub blinfun_to_mat_scale)
qed

lemma mat_cong:
  assumes "(\<And>i j. i < n \<Longrightarrow> j < m \<Longrightarrow> f i j = g i j)"
  shows "Matrix.mat n m (\<lambda>(i, j). f i j) = Matrix.mat n m (\<lambda>(i,j). g i j)"
  using assms by auto

lemma \<P>\<^sub>1_mat: "(Matrix.mat states states (\<lambda>(s, s'). pmf (K (s, d s)) s')) = blinfun_to_mat states states (\<P>\<^sub>1 (mk_dec_det d))"
proof -
  have "pmf (K (s, d s)) s' = measure_pmf.expectation (K (s, d s)) (\<lambda>k. if s' = k then 1 else 0)" 
      if "s < states" "s' < states" for s s'
    by (auto simp: integral_measure_pmf_real[of "{s'}"] split: if_splits)
  thus ?thesis
    by (auto simp: blinfun_to_mat_def \<P>\<^sub>1.rep_eq K_st_def mk_dec_det_def bind_return_pmf)
qed

lemma vec_\<nu>\<^sub>b': "bfun_to_vec states (\<nu>\<^sub>b (mk_stationary_det d)) = 
  inverse_mat ((1\<^sub>m states) - l \<cdot>\<^sub>m (Matrix.mat states states (\<lambda>(s, s'). pmf (K (s, d s)) s'))) *\<^sub>v 
  (vec states (\<lambda>i. r (i, d i)))"
  unfolding vec_\<nu>\<^sub>b using \<P>\<^sub>1_mat by (auto simp: bfun_to_vec_def)

lemma vec_\<nu>\<^sub>b'': 
  assumes "s < states"
  shows "(\<nu>\<^sub>b (mk_stationary_det d)) s = 
  (inverse_mat ((1\<^sub>m states) - l \<cdot>\<^sub>m (Matrix.mat states states (\<lambda>(s, s'). pmf (K (s, d s)) s'))) *\<^sub>v 
  (vec states (\<lambda>i. r (i, d i)))) $ s"
  using vec_\<nu>\<^sub>b' assms unfolding bfun_to_vec_def by (metis index_vec)

lemma invertible_\<nu>\<^sub>b_mat': 
  "invertible_mat (1\<^sub>m states - l \<cdot>\<^sub>m Matrix.mat states states (\<lambda>(s, y). pmf (K (s, d s)) y))"
  using invertible_\<nu>\<^sub>b_mat \<P>\<^sub>1_mat by presburger

lemma dim_vec_\<nu>\<^sub>b: "dim_vec (inverse_mat ((1\<^sub>m states) - 
  l \<cdot>\<^sub>m (Matrix.mat states states (\<lambda>(s, s'). pmf (K (s, d s)) s'))) *\<^sub>v 
  (vec states (\<lambda>i. r (i, d i)))) = states"
  by (simp add: inverse_mat_dims(2) invertible_\<nu>\<^sub>b_mat')

end
end