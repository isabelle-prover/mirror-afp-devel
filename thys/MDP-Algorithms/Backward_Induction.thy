theory Backward_Induction
imports "MDP-Rewards.MDP_reward"
begin

locale MDP_reward_fin = discrete_MDP A K
  for  
    A and 
    K :: "'s ::countable \<times> 'a ::countable \<Rightarrow> 's pmf" +
  fixes
    r :: "('s \<times> 'a) \<Rightarrow> real" and
    r_fin :: "'s \<Rightarrow> real" and
    N :: "nat"    
  assumes
    r_fin_bounded: "bounded (range r_fin)" and
    r_bounded_fin: "bounded (range r)"
begin

interpretation MDP_reward A K r 1
  rewrites "1 * (x::real) = x" and "\<And>x.(1::real)^(x::nat)=1"
  using r_bounded_fin
  by unfold_locales (auto simp: algebra_simps)

definition "\<nu>N p s = (\<integral>t. (\<Sum>i<N. r (t !! i)) +  (r_fin (fst(t !! N))) \<partial>\<T> p s)"

lemma measurable_r_fin_nth [measurable]: "(\<lambda>t. r_fin ((t !! i))) \<in> borel_measurable S"
  by measurable  

lemma integrable_r_fin_nth [simp]: "integrable (\<T> p s) (\<lambda>t. r_fin (fst(t !! i)))"
  using bounded_range_subset[OF r_fin_bounded]
  by (auto simp: range_composition[of r_fin])

lemma \<nu>N_eq: "\<nu>N p s = (\<Sum>i < N. measure_pmf.expectation (Pn' p s i) r) + measure_pmf.expectation (Xn' p s N) r_fin"
proof -
  have "\<nu>N p s = (\<integral>t. (\<Sum>i<N. r (t !! i)) \<partial>\<T> p s) + (\<integral>t. (r_fin (fst(t !! N))) \<partial>\<T> p s)"
    unfolding \<nu>N_def
    by (auto intro: Bochner_Integration.integral_add)
  moreover have " (\<integral>t. (\<Sum>i<N. r (t !! i)) \<partial>\<T> p s) = (\<Sum>i < N. measure_pmf.expectation (Pn' p s i) r)"
    using \<nu>_fin_Suc \<nu>_fin_eq_Pn by force
  moreover have "(\<integral>t. (r_fin (fst(t !! N))) \<partial>\<T> p s) = measure_pmf.expectation (Xn' p s N) r_fin"
    by (auto simp: Xn'_Pn' Pn'_eq_\<T> integral_distr)
  ultimately show ?thesis by auto
qed

function \<nu>N_eval where
  "\<nu>N_eval p h s = (
    if length h = N then r_fin s else 
    if length h > N then 0 else
      measure_pmf.expectation (p h s) (\<lambda>a. r (s,a) +
        measure_pmf.expectation (K (s,a)) (\<lambda>s'. \<nu>N_eval p (h@[(s,a)]) s'))) "
  by auto

termination
  by (relation "Wellfounded.measure (\<lambda>(_,h,s). N - length h)") auto

lemmas abs_disc_eq[simp del]
lemmas \<nu>N_eval.simps[simp del]

lemma pmf_bounded_integrable: "bounded (range (f::_ \<Rightarrow> real)) \<Longrightarrow> integrable (measure_pmf p) f"
  using bounded_norm_le_SUP_norm[of f]
  by (intro measure_pmf.integrable_const_bound[of _ "\<Squnion>x. \<bar>f x\<bar>"]) auto

lemma abs_boundedD[dest]: "(\<And>x. \<bar>f x\<bar> \<le> (c::real)) \<Longrightarrow> bounded (range f)"
  using bounded_real by auto

lemma abs_integral_le[intro]: "(\<And>x. \<bar>f x\<bar> \<le> (c::real)) \<Longrightarrow> abs (measure_pmf.expectation p f) \<le> c"
  by (fastforce intro!: pmf_bounded_integrable abs_boundedD measure_pmf.integral_le_const order.trans[OF integral_abs_bound])

lemma abs_\<nu>N_eval_le: "\<bar>\<nu>N_eval p h s\<bar> \<le> (N - length h) * r\<^sub>M + (\<Squnion>s. \<bar>r_fin s\<bar>)"
proof (induction "(N - length h)" arbitrary: h s)
  case 0
  then show ?case 
    using r_fin_bounded
    by (auto simp: \<nu>N_eval.simps intro!: bounded_imp_bdd_above cSUP_upper2)
next
  case (Suc x)
  have "N > length h"
    using Suc(2) by linarith
  hence Suc_le: "Suc (length h) \<le> N"
    by auto
  have *: "\<bar>\<nu>N_eval p (h @ [(s, a)]) s'\<bar> \<le> real (N - length h - 1) * r\<^sub>M + (\<Squnion>s. \<bar>r_fin s\<bar>)" for a s'
    using Suc.hyps(1)[of "h @[(s,a)]"] Suc.hyps(2)
    by (auto simp: of_nat_diff[OF Suc_le] algebra_simps)
  hence **: "\<bar>measure_pmf.expectation (p h s) (\<lambda>a. measure_pmf.expectation (K (s, a)) (\<nu>N_eval p (h @ [(s, a)])))\<bar>
    \<le> real (N - length h - 1) * r\<^sub>M + (\<Squnion>s. \<bar>r_fin s\<bar>)"
    using Suc by auto
  have "\<bar>measure_pmf.expectation (p h s) (\<lambda>a. r (s, a) + measure_pmf.expectation (K (s, a)) (\<nu>N_eval p (h @ [(s, a)])))\<bar>
      \<le> \<bar>measure_pmf.expectation (p h s) (\<lambda>a. r (s, a))  + measure_pmf.expectation (p h s) (\<lambda>a. measure_pmf.expectation (K (s, a)) (\<nu>N_eval p (h @ [(s, a)])))\<bar>"
    using abs_r_le_r\<^sub>M
    by (subst Bochner_Integration.integral_add) (auto intro!: abs_boundedD * pmf_bounded_integrable)     
  also have "\<dots> \<le> \<bar>measure_pmf.expectation (p h s) (\<lambda>a. r (s, a))\<bar>  + \<bar> measure_pmf.expectation (p h s) (\<lambda>a. measure_pmf.expectation (K (s, a)) (\<nu>N_eval p (h @ [(s, a)])))\<bar>"
    by auto
  also have "\<dots> \<le> r\<^sub>M  + \<bar> measure_pmf.expectation (p h s) (\<lambda>a. measure_pmf.expectation (K (s, a)) (\<nu>N_eval p (h @ [(s, a)])))\<bar>"
    using abs_r_le_r\<^sub>M by auto
  also have "\<dots> \<le> r\<^sub>M  + (N - length h - 1) * r\<^sub>M + (\<Squnion>s. \<bar>r_fin s\<bar>)"
    using "**" by force
  also have "\<dots> \<le> (N - length h) * r\<^sub>M + (\<Squnion>s. \<bar>r_fin s\<bar>)"
    using Suc Suc_le by (auto simp: of_nat_diff algebra_simps)
  finally show ?case
    using \<nu>N_eval.simps \<open>length h < N\<close> by force
qed

lemma abs_\<nu>N_eval_le': "\<bar>\<nu>N_eval p h s\<bar> \<le> N * r\<^sub>M + (\<Squnion>s. \<bar>r_fin s\<bar>)"
  by (simp add: mult_left_mono r\<^sub>M_nonneg algebra_simps order.trans[OF abs_\<nu>N_eval_le[of p h s]])

lemma measure_pmf_expectation_bind: 
  assumes "bounded (range f)" 
  shows "measure_pmf.expectation (p \<bind> q) (f::_ \<Rightarrow> real) = measure_pmf.expectation p (\<lambda>x. measure_pmf.expectation (q x) f)"
  unfolding measure_pmf_bind
  using assms measure_pmf_in_subprob_space
  by (fastforce intro!: Giry_Monad.integral_bind[of _ "count_space UNIV" "\<Squnion>x. \<bar>f x\<bar>"] bounded_imp_bdd_above cSUP_upper)+

lemma Pn'_shift: "bounded (range (f :: _ \<Rightarrow> real)) \<Longrightarrow> measure_pmf.expectation (p h s)
     (\<lambda>a. measure_pmf.expectation (K (s, a))
            (\<lambda>s'. measure_pmf.expectation (Pn' (\<lambda>h'. p ((h @ (s, a)# h'))) s' n) f))
    = measure_pmf.expectation (Pn' (\<lambda>h'. p (h @ h')) s (Suc n)) f"
  unfolding PSuc' \<pi>_Suc_def K0'_def
  by (auto simp: measure_pmf_expectation_bind)

lemma bounded_r_snd': "bounded ((\<lambda>a. r (s, a)) ` X)"
  using r_bounded' image_image
  by metis

lemma bounded_r_snd: "bounded (range (\<lambda>a. r (s, a)))"
  using bounded_r_snd'.

lemma \<nu>N_eval_eq: "length h \<le> N \<Longrightarrow> \<nu>N_eval p h s =
  (\<Sum>i \<in>{length h..< N}.
  measure_pmf.expectation (Pn' (\<lambda>h'. p (h@h')) s (i - length h)) r) + measure_pmf.expectation (Xn' (\<lambda>h'. p (h@h')) s (N - length h)) r_fin"
proof (induction "N - length h" arbitrary: h s)
  case 0
  then show ?case
    using \<nu>N_eval.simps by auto
next
  case (Suc x)
  hence "length h < N"
    by auto
  hence
    "\<nu>N_eval p h s =
      measure_pmf.expectation (p h s) (\<lambda>a. r (s,a) +
        measure_pmf.expectation (K (s,a)) (\<lambda>s'. \<nu>N_eval p (h@[(s,a)]) s'))"
    by (auto simp: \<nu>N_eval.simps[of p h] split: if_splits)
  also have "\<dots> = 
      measure_pmf.expectation (p h s) (\<lambda>a. r (s,a)) + measure_pmf.expectation (p h s) (\<lambda>a. measure_pmf.expectation (K (s,a)) (\<lambda>s'. \<nu>N_eval p (h@[(s,a)]) s'))"
    using abs_\<nu>N_eval_le' bounded_r_snd
    by (fastforce simp: bounded_real intro!: Bochner_Integration.integral_add pmf_bounded_integrable abs_integral_le)
  also have "\<dots> =
    (\<Sum>i = length h..<N. measure_pmf.expectation (Pn' (\<lambda>h'. p (h @ h')) s (i - length h)) r) + measure_pmf.expectation (Xn' (\<lambda>h'. p (h @ h')) s (N - length h)) r_fin"
  proof -
    have "measure_pmf.expectation (p h s) (\<lambda>a. measure_pmf.expectation (K (s,a)) (\<lambda>s'. \<nu>N_eval p (h@[(s,a)]) s')) = 
    measure_pmf.expectation (p h s)
     (\<lambda>a. measure_pmf.expectation (K (s, a))
            (\<lambda>s'. (\<Sum>i = length (h @ [(s, a)])..<N. measure_pmf.expectation (Pn' (\<lambda>h'. p ((h @ [(s, a)]) @ h')) s' (i - length (h @ [(s, a)]))) r) +
                   measure_pmf.expectation (Xn' (\<lambda>h'. p ((h @ [(s, a)]) @ h')) s' (N - length (h @ [(s, a)]))) r_fin))"
      using Suc \<open>length h < N\<close>
      by auto
    also have "\<dots> = 
    measure_pmf.expectation (p h s)
     (\<lambda>a. measure_pmf.expectation (K (s, a))
            (\<lambda>s'. (\<Sum>i = length h + 1..<N. measure_pmf.expectation (Pn' (\<lambda>h'. p ((h @ [(s, a)]) @ h')) s' (i - length h - 1)) r) +
                   measure_pmf.expectation (Xn' (\<lambda>h'. p ((h @ [(s, a)]) @ h')) s' (N - length h - 1)) r_fin))"
      using Suc \<open>length h < N\<close> K0'_def
      by auto
    also have "\<dots> = 
    measure_pmf.expectation (p h s)
     (\<lambda>a. measure_pmf.expectation (K (s, a))
            (\<lambda>s'. (\<Sum>i = length h + 1..<N. measure_pmf.expectation (Pn' (\<lambda>h'. p ((h @ [(s, a)]) @ h')) s' (i - length h - 1)) r)) +
          measure_pmf.expectation (K (s, a))
            (\<lambda>s'. measure_pmf.expectation (Xn' (\<lambda>h'. p ((h @ [(s, a)]) @ h')) s' (N - length h - 1)) r_fin))"
      using abs_exp_r_le r_fin_bounded
      by (fastforce intro!: Bochner_Integration.integral_cong[OF refl] Bochner_Integration.integral_add 
          pmf_bounded_integrable Bochner_Integration.integrable_sum simp: bounded_real)+
    also have "\<dots> = 
    measure_pmf.expectation (p h s)
     (\<lambda>a. measure_pmf.expectation (K (s, a))
            (\<lambda>s'. (\<Sum>i = length h + 1..<N. measure_pmf.expectation (Pn' (\<lambda>h'. p ((h @ [(s, a)]) @ h')) s' (i - length h - 1)) r))) +
      measure_pmf.expectation (p h s) (\<lambda>a. measure_pmf.expectation (K (s, a)) (\<lambda>s'. measure_pmf.expectation 
        (Xn' (\<lambda>h'. p ((h @ [(s, a)]) @ h')) s' (N - length h - 1)) r_fin))"
      using abs_r_le_r\<^sub>M r_fin_bounded
      by (fastforce intro!:
         Bochner_Integration.integral_add Bochner_Integration.integrable_sum pmf_bounded_integrable
         abs_integral_le order.trans[OF sum_abs] order.trans[OF sum_bounded_above[of _ _ "r\<^sub>M"]] simp: bounded_real)
    also have "\<dots> = measure_pmf.expectation (p h s) (\<lambda>a. (\<Sum>i = length h + 1..<N. measure_pmf.expectation (K (s, a))
            (\<lambda>s'. measure_pmf.expectation (Pn' (\<lambda>h'. p ((h @ [(s, a)]) @ h')) s' (i - length h - 1)) r))) +
      measure_pmf.expectation (p h s) (\<lambda>a. measure_pmf.expectation (K (s, a)) (\<lambda>s'. measure_pmf.expectation 
        (Xn' (\<lambda>h'. p ((h @ [(s, a)]) @ h')) s' (N - length h - 1)) r_fin))"
      using abs_r_le_r\<^sub>M
      by (subst Bochner_Integration.integral_sum) (auto intro!: pmf_bounded_integrable boundedI[of _ "r\<^sub>M"] abs_integral_le)
    also have "\<dots> = (\<Sum>i = length h + 1..<N. measure_pmf.expectation (p h s) (\<lambda>a. measure_pmf.expectation (K (s, a))
            (\<lambda>s'. measure_pmf.expectation (Pn' (\<lambda>h'. p ((h @ [(s, a)]) @ h')) s' (i - length h - 1)) r))) +
      measure_pmf.expectation (p h s) (\<lambda>a. measure_pmf.expectation (K (s, a)) (\<lambda>s'. measure_pmf.expectation 
        (Xn' (\<lambda>h'. p ((h @ [(s, a)]) @ h')) s' (N - length h - 1)) r_fin))"
      using abs_r_le_r\<^sub>M
      by (subst Bochner_Integration.integral_sum) (auto intro!: pmf_bounded_integrable boundedI[of _ "r\<^sub>M"] abs_integral_le)
    also have "\<dots> =
      (\<Sum>i = length h + 1..<N. (measure_pmf.expectation (Pn' (\<lambda>h'. p (h @ h')) s (i - length h))) r) + 
      measure_pmf.expectation (Xn' (\<lambda>h'. p (h @ h')) s (N - length h)) r_fin"
      using r_bounded r_fin_bounded \<open>length h < N\<close>
      by (auto simp add: Pn'_shift Xn'_Pn' Suc_diff_Suc range_composition)
    finally show ?thesis
      unfolding sum.atLeast_Suc_lessThan[OF \<open>length h < N\<close>] r_dec_eq_r_K0
      by auto
  qed
  finally show ?case .
qed

lemma \<nu>N_eval_correct: "\<nu>N_eval p [] s = \<nu>N p s"
  using lessThan_atLeast0
  by (auto simp: \<nu>N_eq \<nu>N_eval_eq)

lift_definition \<nu>N\<^sub>b :: "('s, 'a) pol \<Rightarrow> 's \<Rightarrow>\<^sub>b real" is \<nu>N
  using r_fin_bounded
  by (intro bfun_normI[of _ "r\<^sub>M * N + (\<Squnion>x. \<bar>r_fin x\<bar>)"]) 
    (auto simp add: \<nu>N_eq r\<^sub>M_def r_bounded bounded_abs_range intro!: add_mono 
      order.trans[OF integral_abs_bound] pmf_bounded_integrable  lemma_4_3_1
      order.trans[OF sum_abs] order.trans[OF abs_triangle_ineq] order.trans[OF sum_bounded_above[of _ _ r\<^sub>M]])
 
definition "\<nu>N_opt s = (\<Squnion>p \<in> \<Pi>\<^sub>H\<^sub>R. \<nu>N p s)"
definition "\<nu>N_eval_opt h s = (\<Squnion>p \<in> \<Pi>\<^sub>H\<^sub>R. \<nu>N_eval p h s)"

function \<nu>N_opt_eqn where
  "\<nu>N_opt_eqn h s = (
    if length h = N then r_fin s else 
    if length h > N then 0 else
      \<Squnion>a \<in> A s. (r (s,a) +
        measure_pmf.expectation (K (s,a)) (\<lambda>s'. \<nu>N_opt_eqn (h@[(s,a)]) s'))) "
  by auto

termination
  by (relation "Wellfounded.measure (\<lambda>(h,s). N - length h)") auto

lemmas \<nu>N_opt_eqn.simps[simp del]

lemma abs_\<nu>N_opt_eqn_le: "\<bar>\<nu>N_opt_eqn h s\<bar> \<le> (N - length h) * r\<^sub>M + (\<Squnion>s. \<bar>r_fin s\<bar>)"
proof (induction "(N - length h)" arbitrary: h s)
  case 0
  then show ?case 
    using r_fin_bounded
    by (auto simp: \<nu>N_opt_eqn.simps intro!: bounded_imp_bdd_above cSUP_upper2)
next
  case (Suc x)
  have "N > length h"
    using Suc(2) by linarith
  have *: "\<bar>\<nu>N_opt_eqn (h @ [(s, a)]) s'\<bar> \<le> real (N - length h - 1) * r\<^sub>M + (\<Squnion>s. \<bar>r_fin s\<bar>)" for a s'
    using Suc(1)[of "(h @ [(s, a)])"] Suc(2)
    by auto
  hence "\<bar>measure_pmf.expectation (K (s, a)) (\<nu>N_opt_eqn (h @ [(s, a)]))\<bar>
    \<le> real (N - length h - 1) * r\<^sub>M + (\<Squnion>s. \<bar>r_fin s\<bar>)" for a
    using Suc by auto
  hence **: "r\<^sub>M + \<bar>measure_pmf.expectation (K (s, a)) (\<nu>N_opt_eqn (h @ [(s, a)]))\<bar>
    \<le> real (N - length h) * r\<^sub>M + (\<Squnion>s. \<bar>r_fin s\<bar>)" for a
    using Suc
    by (auto simp: of_nat_diff algebra_simps)
  hence *: "\<bar>r (s, a)\<bar> + \<bar>measure_pmf.expectation (K (s, a)) (\<nu>N_opt_eqn (h @ [(s, a)]))\<bar> \<le> real (N - length h) * r\<^sub>M + (\<Squnion>s. \<bar>r_fin s\<bar>)" for a
    using abs_r_le_r\<^sub>M
    by (meson add_le_cancel_right  order.trans)
  hence *: "\<bar>r (s, a) + measure_pmf.expectation (K (s, a)) (\<nu>N_opt_eqn (h @ [(s, a)]))\<bar> \<le> real (N - length h) * r\<^sub>M + (\<Squnion>s. \<bar>r_fin s\<bar>)" for a
    using order.trans[OF abs_triangle_ineq] by auto
  have "\<bar>\<nu>N_opt_eqn h s\<bar> = \<bar>\<Squnion>a\<in>A s. r (s, a) + measure_pmf.expectation (K (s, a)) (\<nu>N_opt_eqn (h @ [(s, a)]))\<bar>"
    unfolding \<nu>N_opt_eqn.simps[of h] using \<open>length h < N\<close>
    by auto
  also have "\<dots> \<le> \<bar>\<Squnion>a\<in>A s. measure_pmf.expectation (return_pmf a) (\<lambda>a. r (s, a) + measure_pmf.expectation (K (s, a)) (\<nu>N_opt_eqn (h @ [(s, a)])))\<bar>"
    by auto
  also have "\<dots> \<le> (\<Squnion>a\<in>A s. \<bar> measure_pmf.expectation (return_pmf a) (\<lambda>a. r (s, a) + measure_pmf.expectation (K (s, a)) (\<nu>N_opt_eqn (h @ [(s, a)])))\<bar>)"
    using \<open>length h < N\<close> A_ne  *
    by (auto intro!: boundedI abs_cSUP_le)
  also have "\<dots> \<le> real (N - length h) * r\<^sub>M + (\<Squnion>s. \<bar>r_fin s\<bar>)"
    using * A_ne
    by (auto intro!: cSUP_least)
  finally show ?case.
qed

lemma abs_\<nu>N_opt_eqn_le': "\<bar>\<nu>N_opt_eqn h s\<bar> \<le> N * r\<^sub>M + (\<Squnion>s. \<bar>r_fin s\<bar>)"
  by (simp add: mult_left_mono r\<^sub>M_nonneg algebra_simps order.trans[OF abs_\<nu>N_opt_eqn_le[of h s]])

lemma abs_\<nu>N_eval_opt_le': "\<bar>\<nu>N_eval_opt h s\<bar> \<le> N * r\<^sub>M + (\<Squnion>s. \<bar>r_fin s\<bar>)"
  unfolding \<nu>N_eval_opt_def
  using policies_ne abs_\<nu>N_eval_le'
  by (auto intro!: order.trans[OF abs_cSUP_le] boundedI cSUP_least)

lemma exp_\<nu>N_eval_opt_le: "\<bar>measure_pmf.expectation (K (s, a)) (\<nu>N_eval_opt h)\<bar> \<le> N * r\<^sub>M + (\<Squnion>s. \<bar>r_fin s\<bar>)"
  by (metis abs_\<nu>N_eval_opt_le' abs_integral_le)

lemma bounded_exp_\<nu>N_eval_opt: "(bounded ((\<lambda>a. measure_pmf.expectation (K (s, a)) (\<nu>N_eval_opt (h a))) ` X))"
  using exp_\<nu>N_eval_opt_le
  by (auto intro!: boundedI)

lemma bounded_r_exp_\<nu>N_eval_opt: "(bounded ((\<lambda>a. r (s, a) + measure_pmf.expectation (K (s, a)) (\<nu>N_eval_opt (h a))) ` X))"
  using bounded_exp_\<nu>N_eval_opt r_bounded abs_r_le_r\<^sub>M
  by (intro bounded_plus_comp) (auto intro!:  boundedI)

lemma integrable_r_exp_\<nu>N_eval_opt: "(integrable (measure_pmf q) ((\<lambda>a. r (s, a) + measure_pmf.expectation (K (s, a)) (\<nu>N_eval_opt (h a)))))"
  using bounded_r_exp_\<nu>N_eval_opt pmf_bounded_integrable by blast


lemma exp_\<nu>N_eval_le: "\<bar>measure_pmf.expectation (K (s, a)) (\<nu>N_eval p h)\<bar> \<le> N * r\<^sub>M + (\<Squnion>s. \<bar>r_fin s\<bar>)"
  by (metis abs_\<nu>N_eval_le' abs_integral_le)

lemma bounded_exp_\<nu>N_eval: "(bounded ((\<lambda>a. measure_pmf.expectation (K (s, a)) (\<nu>N_eval p (h a))) ` X))"
  using exp_\<nu>N_eval_le
  by (auto intro!: boundedI)

lemma bounded_r_exp_\<nu>N_eval: "(bounded ((\<lambda>a. r (s, a) + measure_pmf.expectation (K (s, a)) (\<nu>N_eval p (h a))) ` X))"
  using bounded_exp_\<nu>N_eval r_bounded abs_r_le_r\<^sub>M
  by (intro bounded_plus_comp) (auto intro!:  boundedI)

lemma integrable_r_exp_\<nu>N_eval: "(integrable (measure_pmf q) ((\<lambda>a. r (s, a) + measure_pmf.expectation (K (s, a)) (\<nu>N_eval p (h a)))))"
  using bounded_r_exp_\<nu>N_eval pmf_bounded_integrable by blast

lemma exp_\<nu>N_opt_eqn_le: "\<bar>measure_pmf.expectation (K (s, a)) (\<nu>N_opt_eqn h)\<bar> \<le> N * r\<^sub>M + (\<Squnion>s. \<bar>r_fin s\<bar>)"
  by (metis abs_\<nu>N_opt_eqn_le' abs_integral_le)

lemma bounded_exp_\<nu>N_opt_eqn: "(bounded ((\<lambda>a. measure_pmf.expectation (K (s, a)) (\<nu>N_opt_eqn (h a))) ` X))"
  using exp_\<nu>N_opt_eqn_le
  by (auto intro!: boundedI)

lemma bounded_r_exp_\<nu>N_opt_eqn: "(bounded ((\<lambda>a. r (s, a) + measure_pmf.expectation (K (s, a)) (\<nu>N_opt_eqn (h a))) ` X))"
  using bounded_exp_\<nu>N_opt_eqn r_bounded abs_r_le_r\<^sub>M
  by (intro bounded_plus_comp) (auto intro!:  boundedI)

lemma integrable_r_exp_\<nu>N_opt_eqn: "(integrable (measure_pmf q) ((\<lambda>a. r (s, a) + measure_pmf.expectation (K (s, a)) (\<nu>N_opt_eqn (h a)))))"
  using bounded_r_exp_\<nu>N_opt_eqn pmf_bounded_integrable by blast

lemma \<nu>N_eval_le_opt_eqn: "p \<in> \<Pi>\<^sub>H\<^sub>R \<Longrightarrow> \<nu>N_eval p h s \<le> \<nu>N_opt_eqn h s"
proof (induction p h s rule: \<nu>N_eval.induct)
  case (1 p h s)
  have "\<nu>N_eval p (h @ [(s, a)]) s' \<le> \<nu>N_opt_eqn (h @[(s,a)]) s'" if "length h < N" for a s'
    using that 1 by fastforce
  hence *: "r (s, a) + measure_pmf.expectation (K (s, a)) (\<nu>N_eval p (h @ [(s, a)])) \<le> r (s, a) + measure_pmf.expectation (K (s, a)) (\<nu>N_opt_eqn (h @ [(s, a)]))" if "length h < N" for a
    using abs_\<nu>N_eval_le' abs_\<nu>N_opt_eqn_le' that
    by (fastforce intro!: integral_mono pmf_bounded_integrable simp: bounded_real)
  have **: "a \<in> set_pmf (p h s) \<Longrightarrow> a \<in> A s" for a
    using 1 is_dec_def is_policy_def by blast
  then show ?case
    unfolding \<nu>N_eval.simps[of p h] \<nu>N_opt_eqn.simps[of h]
    using integrable_r_exp_\<nu>N_eval bounded_r_exp_\<nu>N_eval bounded_r_exp_\<nu>N_opt_eqn *
    by (auto simp: set_pmf_not_empty intro!: order.trans[OF lemma_4_3_1] cSUP_mono bexI bounded_imp_bdd_above)
  qed

lemma \<nu>N_eval_le_opt: "p\<in>\<Pi>\<^sub>H\<^sub>R \<Longrightarrow> \<nu>N_eval_opt h s \<ge> \<nu>N_eval p h s"
  unfolding \<nu>N_eval_opt_def
  using bounded_subset_range[OF abs_boundedD[OF abs_\<nu>N_eval_le']]
  by (force intro!: cSUP_upper abs_boundedD bounded_imp_bdd_above)

lemma \<nu>N_opt_eqn_bounded[simp, intro]: "bounded ((\<nu>N_opt_eqn h) ` X)"
  by (meson Blinfun_Util.bounded_subset abs_\<nu>N_opt_eqn_le' abs_boundedD subset_UNIV)

lemma \<nu>N_eval_opt_bounded[simp, intro]: "bounded ((\<nu>N_eval_opt h) ` X)"
  by (meson Blinfun_Util.bounded_subset abs_\<nu>N_eval_opt_le' abs_boundedD subset_UNIV)

lemma \<nu>N_eval_bounded[simp, intro]: "bounded ((\<nu>N_eval p h) ` X)"
  by (meson Blinfun_Util.bounded_subset abs_\<nu>N_eval_le' abs_boundedD subset_UNIV)

lemma \<nu>N_opt_ge: "length h \<le> N \<Longrightarrow> \<nu>N_opt_eqn h s \<ge> \<nu>N_eval_opt h s"
proof (induction "N - length h" arbitrary: h s)
  case 0
  then show ?case
    unfolding \<nu>N_eval_opt_def \<nu>N_opt_eqn.simps[of h]
    using policies_ne
    by (subst \<nu>N_eval_eq) auto
next
  case (Suc x)
  hence "length h < N"
    by linarith
  {
    fix p assume "p \<in> \<Pi>\<^sub>H\<^sub>R"
    have "\<nu>N_eval p h s = measure_pmf.expectation (p h s) (\<lambda>a. (r (s,a) +
        measure_pmf.expectation (K (s,a)) (\<lambda>s'. \<nu>N_eval p (h@[(s,a)]) s')))"
      unfolding \<nu>N_eval.simps[of p h]
      using \<open>length h < N\<close>
      by auto
    also have "\<dots> \<le> (\<Squnion>a \<in> A s. (r (s,a) +
        measure_pmf.expectation (K (s,a)) (\<lambda>s'. \<nu>N_eval p (h@[(s,a)]) s')))"
      using \<open>p \<in> \<Pi>\<^sub>H\<^sub>R\<close> is_dec_def is_policy_def bounded_r_snd' bounded_exp_\<nu>N_eval
      by (auto intro!: lemma_4_3_1 bounded_plus_comp pmf_bounded_integrable simp: r_bounded')
    also have "\<dots> \<le> (\<Squnion>a \<in> A s. (r (s,a) +
        measure_pmf.expectation (K (s,a)) (\<lambda>s'. \<nu>N_opt_eqn (h@[(s,a)]) s')))"
    proof -
      have "a \<in> A s \<Longrightarrow> 
        r (s,a) + measure_pmf.expectation (K (s,a)) (\<nu>N_eval p (h @ [(s,a)])) \<le>
        r (s,a) + measure_pmf.expectation (K (s,a)) (\<nu>N_eval_opt (h@[(s,a)]))" for a
        using abs_boundedD[OF abs_\<nu>N_eval_opt_le'] abs_boundedD[OF abs_\<nu>N_eval_le']
        using \<nu>N_eval_le_opt \<open>p \<in> \<Pi>\<^sub>H\<^sub>R\<close>
        by (force intro!: integral_mono pmf_bounded_integrable)
      moreover have "a \<in> A s \<Longrightarrow> 
        r (s,a) + measure_pmf.expectation (K (s,a)) (\<nu>N_eval_opt (h@[(s,a)])) \<le>
        r (s,a) + measure_pmf.expectation (K (s,a)) (\<nu>N_opt_eqn (h@[(s,a)]))" for a
        using \<nu>N_eval_le_opt_eqn policies_ne Suc
        by (auto intro!: integral_mono pmf_bounded_integrable cSUP_least)
      ultimately show ?thesis
        using A_ne bounded_imp_bdd_above bounded_r_exp_\<nu>N_opt_eqn
        by (fastforce intro!: cSUP_mono)+
    qed
    also have "\<dots> = \<nu>N_opt_eqn h s"
      unfolding \<nu>N_opt_eqn.simps[of h]  
      using \<open>length h < N\<close>
      by auto
    finally have "\<nu>N_opt_eqn h s \<ge> \<nu>N_eval p h s".
  }
  then show ?case    
    unfolding \<nu>N_eval_opt_def
    using policies_ne
    by (auto intro!: cSUP_least)
qed

lemma Sup_wit_ex:
  assumes "(d ::real)> 0"
  assumes "X \<noteq> {}"
  assumes "bdd_above (f ` X)"
  shows "\<exists>x \<in> X. (\<Squnion>x \<in> X. f x) < f x + d"
proof -
  have "\<exists>x \<in>X. (\<Squnion>x \<in> X. f x) - d < f x"
    using assms
    by (auto simp: less_cSUP_iff[symmetric])
  thus ?thesis
    by force
qed


lemma \<nu>N_opt_eqn_markov: "length h \<le> N \<Longrightarrow> length h = length h' \<Longrightarrow> \<nu>N_opt_eqn h = \<nu>N_opt_eqn h'"
proof (induction "N - length h" arbitrary: h h')
  case 0
  then show ?case
    by (auto simp: \<nu>N_opt_eqn.simps)
next
  case (Suc x)
  {
    fix s
    have "\<nu>N_opt_eqn h s = (\<Squnion>a \<in> A s. r (s, a) + measure_pmf.expectation (K(s,a)) (\<nu>N_opt_eqn (h@[(s,a)])))"
      using  Suc by (fastforce simp: \<nu>N_opt_eqn.simps)
    also have "\<dots> = (\<Squnion>a \<in> A s. r (s, a) + measure_pmf.expectation (K(s,a)) (\<nu>N_opt_eqn (h'@[(s,a)])))"
      using Suc
      by (auto intro!: SUP_cong Bochner_Integration.integral_cong Suc(1)[THEN cong])
    also have "\<dots> = \<nu>N_opt_eqn h' s"
      using Suc \<nu>N_opt_eqn.simps by fastforce
    finally have "\<nu>N_opt_eqn h s = \<nu>N_opt_eqn h' s ".
  }
  thus ?case by auto
qed

lemma \<nu>N_opt_le:
  fixes eps :: real
  assumes "eps > 0"
  shows "\<exists>p \<in> \<Pi>\<^sub>M\<^sub>D. \<forall>h s. length h \<le> N \<longrightarrow> \<nu>N_eval (mk_markovian_det p) h s + real (N - length h) * eps \<ge> \<nu>N_opt_eqn h s" 
proof -
  define p where "p = (\<lambda>n s. if n \<ge> N then SOME a. a \<in> A s else
      SOME a. a \<in> A s \<and>
        r (s, a) + measure_pmf.expectation (K (s, a)) (\<nu>N_opt_eqn (replicate n (s, SOME a. a \<in> A s) @ [(s,a)])) + eps > \<nu>N_opt_eqn (replicate n (s,SOME a. a \<in> A s)) s)"
  have *: "\<exists>a . a \<in> A s \<and>
        r (s, a) + measure_pmf.expectation (K (s, a)) (\<nu>N_opt_eqn (h@[(s,a)])) + eps > \<nu>N_opt_eqn h s" 
    if "length h < N"
    for h s
    using that Sup_wit_ex[OF assms A_ne, unfolded Bex_def] bounded_imp_bdd_above bounded_r_exp_\<nu>N_opt_eqn 
    by (auto simp: \<nu>N_opt_eqn.simps)
  hence **: "\<exists>a . a \<in> A s \<and>
        r (s, a) + measure_pmf.expectation (K (s, a)) (\<nu>N_opt_eqn ((replicate n (s,SOME a. a \<in> A s))@[(s,a)])) + eps > \<nu>N_opt_eqn (replicate n (s,SOME a. a \<in> A s)) s" 
    if "n < N" for n s
    using that by simp
  have p_prop: "p n s \<in> A s \<and> r (s, p n s) + measure_pmf.expectation (K (s, p n s)) (\<nu>N_opt_eqn ((replicate n (s,SOME a. a \<in> A s))@[(s,p n s)])) + eps > \<nu>N_opt_eqn ((replicate n (s,SOME a. a \<in> A s))) s"
    if "n < N" for n s
    using someI_ex[OF **[OF that], of s] that
    by (auto simp: p_def)
  hence p_prop': "p (length h) s \<in> A s \<and> r (s, p (length h) s) + measure_pmf.expectation (K (s, p (length h) s)) (\<nu>N_opt_eqn (h@[(s,p (length h) s)])) + eps > \<nu>N_opt_eqn h s"
    if "length h < N" for h s
    using that
    by (auto simp: 
        \<nu>N_opt_eqn_markov[of h "(replicate (length h) (s,SOME a. a \<in> A s))"] 
        \<nu>N_opt_eqn_markov[of "(h@[(s,p (length h) s)])" "(replicate (length h) (s, SOME a. a \<in> A s) @ [(s, p (length h) s)])"])
  have "p n s \<in> A s" for n s
    using SOME_is_dec_det is_dec_det_def p_def p_prop by auto
  hence p:"p \<in> \<Pi>\<^sub>M\<^sub>D"
    using is_dec_det_def by force
  {
    fix h s p
    assume "p \<in> \<Pi>\<^sub>M\<^sub>D"
      and 
      p: "\<And>h s. length h < N \<Longrightarrow> r (s, p (length h) s) + measure_pmf.expectation (K (s, p (length h) s)) (\<nu>N_opt_eqn (h@[(s,p (length h) s)])) + eps > \<nu>N_opt_eqn h s"
    have "length h \<le> N \<Longrightarrow> \<nu>N_eval (mk_markovian_det p) h s + real (N - length h) * eps \<ge> \<nu>N_opt_eqn h s"
    proof (induction "N - length h" arbitrary: h s)
      case 0
      hence *: "length h = N"
        by auto
      thus ?case
        by (auto simp: \<nu>N_opt_eqn.simps \<nu>N_eval.simps)
    next
      case (Suc x)
      hence *: "length h < N"
        by auto
      have "\<nu>N_opt_eqn h s - real (N - length h) * eps < r (s, p (length h) s) + measure_pmf.expectation (K (s, p (length h) s)) (\<nu>N_opt_eqn (h@[(s,p (length h) s)])) - real (N - length h) * eps + eps"
        using p[OF *, of s] by auto        
      also have "\<dots> = r (s, p (length h) s) + measure_pmf.expectation (K (s, p (length h) s)) (\<nu>N_opt_eqn (h@[(s,p (length h) s)])) - real (N - length h - 1) * eps"
      proof -
        have "real (N - length h - 1) = real (N - length h) - 1"
          using * by (auto simp: algebra_simps) 
        thus ?thesis 
          by algebra
      qed
      also have "\<dots> = r (s, p (length h) s) + measure_pmf.expectation (K (s, p (length h) s)) (\<lambda>s'. \<nu>N_opt_eqn (h@[(s,p (length h) s)]) s' - real (N - length h - 1) * eps)"  
        by (subst Bochner_Integration.integral_diff) (auto intro: pmf_bounded_integrable) 
      also have "\<dots> \<le> r (s, p (length h) s) + measure_pmf.expectation (K (s, p (length h) s)) (\<nu>N_eval (mk_markovian_det p) (h@[(s,p (length h) s)]))"
        using Suc(1)[of "h@[_]"] Suc *
        by (auto simp: algebra_simps intro!: integral_mono pmf_bounded_integrable bounded_minus_comp)
      also have "\<dots> = \<nu>N_eval (mk_markovian_det p) h s"
        using Suc
        by (auto simp: mk_markovian_det_def \<nu>N_eval.simps)        
      finally show ?case 
        by auto
    qed
  }
  thus ?thesis
    using p p_prop' by blast
qed

lemma \<nu>N_opt_le':
  fixes eps :: real
  assumes "eps > 0"
  shows "\<exists>p \<in> \<Pi>\<^sub>M\<^sub>D. \<forall>h s. length h \<le> N \<longrightarrow> \<nu>N_eval (mk_markovian_det p) h s + eps \<ge> \<nu>N_opt_eqn h s" 
proof -
  obtain p where "p\<in>\<Pi>\<^sub>M\<^sub>D" and "\<And>h s. length h \<le> N \<Longrightarrow> \<nu>N_opt_eqn h s \<le> \<nu>N_eval (mk_markovian_det p) h s + real (N - length h) * (eps/N)"
    using \<nu>N_opt_le[of "eps / N"] \<nu>N_opt_le assms
    by (cases "N = 0") force+   
  hence **: "\<And>h s. length h \<le> N \<Longrightarrow> \<nu>N_opt_eqn h s \<le> \<nu>N_eval (mk_markovian_det p) h s + eps - ((eps * length h) / N)"
    using assms
    by (cases "N = 0") (auto simp: algebra_simps of_nat_diff intro: add_increasing)
  moreover have *:"eps * real (length h) / N \<ge> 0" for h 
    using assms by auto
  ultimately have "\<And>h s. length h \<le> N \<Longrightarrow> \<nu>N_opt_eqn h s \<le> \<nu>N_eval (mk_markovian_det p) h s + eps"
    by (auto intro!: order.trans[OF **])
  thus ?thesis
    using \<open>p \<in> \<Pi>\<^sub>H\<^sub>D\<close> by blast
qed

lemma mk_det_preserves: "p \<in> \<Pi>\<^sub>H\<^sub>D \<Longrightarrow> (mk_det p) \<in> \<Pi>\<^sub>H\<^sub>R"
  unfolding is_policy_def mk_det_def
  by (auto simp: is_dec_def is_dec_det_def)

lemma mk_markovian_det_preserves: "p \<in> \<Pi>\<^sub>M\<^sub>D \<Longrightarrow> (mk_markovian_det p) \<in> \<Pi>\<^sub>H\<^sub>R"
  unfolding is_policy_def mk_markovian_det_def
  by (auto simp: is_dec_def is_dec_det_def)

lemma \<nu>N_opt_eq:
  assumes "length h \<le> N"
  shows "\<nu>N_opt_eqn h s = \<nu>N_eval_opt h s"
proof -
  {
    fix eps :: real
    assume "0 < eps"
    hence "\<exists>p\<in>\<Pi>\<^sub>H\<^sub>R. \<forall>h s. length h \<le> N \<longrightarrow> \<nu>N_opt_eqn h s \<le> \<nu>N_eval p h s + eps"
    using mk_markovian_det_preserves \<nu>N_opt_le'[of eps]
    by auto
  then obtain p where "p\<in>\<Pi>\<^sub>H\<^sub>R" and **: "length h \<le> N \<Longrightarrow> \<nu>N_opt_eqn h s \<le> \<nu>N_eval p h s + eps" for h s
    by auto
  hence "length h \<le> N \<Longrightarrow> \<nu>N_opt_eqn h s \<le> \<nu>N_eval_opt h s + eps" for h s
    using \<nu>N_eval_le_opt[of p]
    by (auto intro:  order.trans[OF **])
  }
  hence "length h \<le> N \<Longrightarrow> \<nu>N_opt_eqn h s \<le> \<nu>N_eval_opt h s"
    by (meson field_le_epsilon)
  thus ?thesis
    using \<nu>N_opt_ge assms antisym by auto
qed

lemma \<nu>N_opt_eqn_correct: "\<nu>N_opt s = \<nu>N_opt_eqn [] s"
  using \<nu>N_eval_correct \<nu>N_eval_opt_def \<nu>N_opt_def \<nu>N_opt_eq by force

lemma thm_4_3_4:
  assumes "eps \<ge> 0" "p \<in> \<Pi>\<^sub>M\<^sub>D"
    and "\<And>h s. length h < N \<Longrightarrow> r (s, p (length h) s) + measure_pmf.expectation (K (s, p (length h) s)) (\<nu>N_opt_eqn (h@[(s, p (length h) s)])) + eps
    \<ge> (\<Squnion>a \<in> A s. r (s, a) + measure_pmf.expectation (K (s,a)) (\<nu>N_opt_eqn (h@[(s, a)])))"
  shows "\<And>h s.  length h \<le> N \<Longrightarrow> \<nu>N_eval (mk_markovian_det p) h s + (N - length h) * eps \<ge> \<nu>N_opt_eqn h s"
    "\<And>s. \<nu>N (mk_markovian_det p) s + N * eps \<ge> \<nu>N_opt s"
proof -
  show "\<nu>N_eval (mk_markovian_det p) h s + (N - length h) * eps \<ge> \<nu>N_opt_eqn h s" if "length h \<le> N" for h s
    using assms that
  proof (induction "N - length h" arbitrary: h s)
    case 0
    then show ?case
      using \<nu>N_eval.simps \<nu>N_opt_eqn.simps by force
  next
    case (Suc x)
    have "\<nu>N_opt_eqn h s = (\<Squnion>a \<in> A s. r (s, a) + measure_pmf.expectation (K (s,a)) (\<nu>N_opt_eqn (h@[(s, a)])))"
      using Suc.hyps(2) \<nu>N_opt_eqn.simps by fastforce
    also have "\<dots> \<le> r (s, p (length h) s) + measure_pmf.expectation (K (s, p (length h) s)) (\<nu>N_opt_eqn (h@[(s, p (length h) s)])) + eps"
      using Suc.hyps(2) Suc.prems(3)
      by simp
    also have "\<dots> \<le> r (s, p (length h) s) + measure_pmf.expectation (K (s, p (length h) s)) (\<lambda>s'. \<nu>N_eval (mk_markovian_det p) (h@[(s, p (length h) s)]) s' + 
    (N - length (h@[(s,p (length h) s)])) * eps) + eps"
      using Suc(1)[of "(h@[(s,p (length h) s)])"] Suc.hyps(2) assms
      by (auto intro!: integral_mono pmf_bounded_integrable bounded_plus_comp)
    also have "\<dots> = r (s, p (length h) s) + measure_pmf.expectation (K (s, p (length h) s)) (\<nu>N_eval (mk_markovian_det p) (h@[(s, p (length h) s)])) + (N - length h) * eps"
      using Suc
      by (subst Bochner_Integration.integral_add) (auto simp: of_nat_diff left_diff_distrib distrib_right intro!: pmf_bounded_integrable)
    also have "\<dots> = \<nu>N_eval (mk_markovian_det p) h s + (N - length h) * eps"
      using Suc
      by (auto simp add: \<nu>N_eval.simps mk_markovian_det_def)
    finally show ?case.
  qed
  from this[of  "[]"] show "\<nu>N (mk_markovian_det p) s + N * eps \<ge> \<nu>N_opt s" for s
    using \<nu>N_eval_correct \<nu>N_opt_eqn_correct
    by auto
qed

lemma \<nu>N_has_eps_opt_pol:
  assumes "eps > 0"
  shows "\<exists>p \<in> \<Pi>\<^sub>M\<^sub>D. \<forall>s. \<nu>N (mk_markovian_det p) s + eps \<ge> \<nu>N_opt s"
proof -
  obtain p where "p\<in>\<Pi>\<^sub>M\<^sub>D" and 
    P: "\<And>h s. length h \<le> N \<Longrightarrow> \<nu>N_opt_eqn h s \<le> \<nu>N_eval (mk_markovian_det p) h s + eps"
    using \<nu>N_opt_le'[of eps] assms by auto
  from P[of "[]"] have "\<nu>N_opt_eqn [] s \<le> \<nu>N_eval (mk_markovian_det p) [] s + eps" for s
    by auto
  thus ?thesis
    unfolding \<nu>N_opt_eqn_correct
    using \<nu>N_eval_correct \<open>p \<in> \<Pi>\<^sub>H\<^sub>D\<close> by auto 
qed

lemma \<nu>N_le_opt: "p \<in> \<Pi>\<^sub>H\<^sub>R \<Longrightarrow> \<nu>N p s \<le> \<nu>N_opt s"
  by (metis \<nu>N_eval_correct \<nu>N_eval_le_opt_eqn \<nu>N_opt_eqn_correct)

lemma \<nu>N_has_opt_pol:
  assumes "\<And>h s. 
    length h < N 
    \<Longrightarrow> \<exists>a \<in> A s. r (s, a) + measure_pmf.expectation (K (s,a)) (\<nu>N_opt_eqn (h@[(s,a)]))
    = (\<Squnion>a \<in> A s. r (s, a) + measure_pmf.expectation (K (s,a)) (\<nu>N_opt_eqn (h@[(s,a)])))" 
  shows "\<exists>p \<in> \<Pi>\<^sub>M\<^sub>D. \<forall>s. \<nu>N (mk_markovian_det p) s = \<nu>N_opt s"
proof -
  define p where "p = (\<lambda>n s. if n \<ge> N then SOME a. a \<in> A s else
      SOME a. a \<in> A s \<and>
        r (s, a) + measure_pmf.expectation (K (s, a)) (\<nu>N_opt_eqn (replicate n (s,SOME a. a \<in> A s)@[(s,a)])) = \<nu>N_opt_eqn (replicate n (s,SOME a. a \<in> A s)) s
)"
  have p_short: "p n s = (
      SOME a. a \<in> A s \<and>
        r (s, a) + measure_pmf.expectation (K (s, a)) (\<nu>N_opt_eqn (replicate n (s,SOME a. a \<in> A s)@[(s,a)])) = \<nu>N_opt_eqn (replicate n (s,SOME a. a \<in> A s)) s)"
    if "n < N" for n s
    unfolding p_def using that by auto
  have *: "p n s \<in> A s" 
    "(n < N \<Longrightarrow>  r (s, p n s) + measure_pmf.expectation (K (s,p n s)) (\<nu>N_opt_eqn ((replicate n (s,SOME a. a \<in> A s))@[(s,p n s)]))
    = (\<Squnion>a \<in> A s. r (s, a) + measure_pmf.expectation (K (s,a)) (\<nu>N_opt_eqn ((replicate n (s,SOME a. a \<in> A s))@[(s,a)]))))" for n s
      using someI_ex[OF assms[unfolded Bex_def]] SOME_is_dec_det
      by (auto simp: \<nu>N_opt_eqn.simps is_dec_det_def p_def)
    have "\<nu>N (mk_markovian_det p) s \<ge> \<nu>N_opt s" for s
    proof (intro thm_4_3_4(2)[of 0 p, simplified])
      show "\<forall>n. is_dec_det (p n)"
        using *
        by (auto simp: is_dec_det_def)
    next
      {
        fix h :: "('s \<times> 'a) list" and s
        assume "length h < N"
        have "(\<Squnion>a\<in>A s. r (s, a) + measure_pmf.expectation (K (s, a)) (\<nu>N_opt_eqn (h @ [(s, a)]))) = 
          (\<Squnion>a \<in> A s. r (s, a) + measure_pmf.expectation (K (s,a)) (\<nu>N_opt_eqn ((replicate (length h) (s,SOME a. a \<in> A s))@[(s,a)])))"
          using \<open>length h < N\<close>
          by (auto intro!: SUP_cong Bochner_Integration.integral_cong \<nu>N_opt_eqn_markov[THEN cong])
        also have "\<dots> = r (s, p (length h) s) + measure_pmf.expectation (K (s,p (length h) s)) (\<nu>N_opt_eqn ((replicate (length h) (s,SOME a. a \<in> A s))@[(s,p (length h) s)]))"
          using * \<open>length h < N\<close> by presburger
        also have "\<dots> = r (s, p (length h) s) + measure_pmf.expectation (K (s,p (length h) s)) (\<nu>N_opt_eqn (h@[(s,p (length h) s)]))"
          using \<open>length h < N\<close>
          by (auto intro!: Bochner_Integration.integral_cong \<nu>N_opt_eqn_markov[THEN cong])
        finally show "(\<Squnion>a\<in>A s. r (s, a) + measure_pmf.expectation (K (s, a)) (\<nu>N_opt_eqn (h @ [(s, a)])))
           \<le> r (s, p (length h) s) + measure_pmf.expectation (K (s, p (length h) s)) (\<nu>N_opt_eqn (h @ [(s, p (length h) s)]))"
          by auto
      }
    qed
    hence "\<nu>N (mk_markovian_det p) s = \<nu>N_opt s" for s
      using \<nu>N_le_opt *(1) mk_markovian_det_preserves
      by (simp add: is_dec_det_def order_antisym)
    thus ?thesis
      using *(1)
      by (auto simp: is_dec_det_def)
qed

lemma ex_Max: "finite X \<Longrightarrow> X \<noteq> {} \<Longrightarrow> \<exists>x \<in> X.  f x = Max (f ` X)"
  by (metis (mono_tags, opaque_lifting) Max_in empty_is_image finite_imageI imageE)

lemma fin_A_imp_opt_pol:
  assumes "\<And>s. finite (A s)"
  shows "\<exists>p\<in>\<Pi>\<^sub>M\<^sub>D. \<forall>s. \<nu>N (mk_markovian_det p) s = \<nu>N_opt s"
  using A_ne assms \<nu>N_has_opt_pol
  by (fastforce simp: cSup_eq_Max intro!: ex_Max)


section \<open>Backward Induction\<close>

function bw_ind_aux where
  "bw_ind_aux n s = (
    if n = N then r_fin s else 
    if n > N then 0 else
      \<Squnion>a \<in> A s. (r (s,a) +
        measure_pmf.expectation (K (s,a)) (\<lambda>s'. bw_ind_aux (Suc n) s'))) "
  by auto

termination
  by (relation "Wellfounded.measure (\<lambda>(h,s). N - h)") auto

lemmas bw_ind_aux.simps[simp del]


lemma bw_ind_aux_eq: "bw_ind_aux (length h) s = \<nu>N_opt_eqn h s"
  by (induction h s rule: \<nu>N_opt_eqn.induct)
    (auto simp: bw_ind_aux.simps \<nu>N_opt_eqn.simps split: if_splits intro!: Bochner_Integration.integral_cong SUP_cong)

fun bw_ind_aux' where
  "bw_ind_aux' (Suc n) m = (
    let m' = (\<lambda>i s. 
      if i = n 
      then (\<Squnion>a \<in> A s. (r (s,a) + measure_pmf.expectation (K (s,a)) (m (Suc n))))
      else m i s) in
    bw_ind_aux' n m')" |
  "bw_ind_aux' 0 m = m"

definition "bw_ind = bw_ind_aux' N (\<lambda>i s. if i = N then r_fin s else 0)"


lemma bw_ind_aux'_const[simp]:
  assumes "i \<ge> n"
  shows "bw_ind_aux' n m i = m i"
  using assms
proof (induction n arbitrary: m i)
  case 0
  then show ?case by (auto simp: bw_ind_aux'.simps)
next
  case (Suc n)
  then show ?case
    by auto
qed

lemma bw_ind_aux'_indep:
  assumes "i < n" and
    "\<And>j. j > i \<Longrightarrow> m j = m' j"
  shows "bw_ind_aux' n m i s = bw_ind_aux' n m' i s"
  using assms
proof (induction n arbitrary: m i m')
  case 0
  then show ?case
    by fastforce
next
  case (Suc n)
  show ?case
  proof (cases "i < n")
    case True
    then show ?thesis
      by (auto intro!: Suc(1) ext simp: Suc(2,3))
  next
    case False
    then show ?thesis
      using Suc.prems(1) less_Suc_eq
      by (auto simp: Suc)
  qed  
  qed

lemma bw_ind_aux'_simps': "i < n \<Longrightarrow> bw_ind_aux' n m i s = (\<Squnion>a \<in> A s. (r (s,a) + measure_pmf.expectation (K (s,a)) (bw_ind_aux'  n m (Suc i))))"
proof (induction n arbitrary: m i s)
  case 0
  then show ?case by auto
next
  case (Suc n)
  have "bw_ind_aux' (Suc n) m i s = bw_ind_aux' n (\<lambda>i s. if i = n then \<Squnion>a\<in>A s. r (s, a) + measure_pmf.expectation (K (s, a)) (m (Suc n)) else m i s) i s"
    by auto
  also have "\<dots> = (\<Squnion>a\<in>A s. r (s, a) + measure_pmf.expectation (K (s, a)) ((bw_ind_aux' (Suc n) m (Suc i))))"
    using Suc.prems le_less_Suc_eq
    by (cases "n \<le> i") (auto simp: Suc.IH bw_ind_aux'_const)
  finally show ?case.
qed

lemma bw_ind_correct: "n \<le> N \<Longrightarrow> bw_ind n = bw_ind_aux n"
  unfolding bw_ind_def
proof (induction "N - n" arbitrary: n)
  case 0
  show ?case
    using 0
    by (subst bw_ind_aux.simps) (auto)
next
  case (Suc x)
  thus ?case
    by (auto simp: bw_ind_aux'_simps' bw_ind_aux.simps intro!: ext)
qed

definition "bw_ind_pol_gen (d :: 'a set \<Rightarrow> 'a) n s = (
  if n \<ge> N then d (A s)
  else
    d ({a . is_arg_max (\<lambda>a. r (s, a) + measure_pmf.expectation (K (s, a)) (bw_ind_aux (Suc n))) (\<lambda>a. a \<in> A s) a}))"

lemma bw_ind_pol_is_arg_max:
  assumes "\<And>X. X \<noteq> {} \<Longrightarrow> d X \<in> X" "\<And>s. finite (A s)"
  shows "is_arg_max (\<lambda>a. r (s, a) + measure_pmf.expectation (K (s, a)) (bw_ind_aux (Suc n))) (\<lambda>a. a \<in> A s) (d ({a . is_arg_max (\<lambda>a. r (s, a) + measure_pmf.expectation (K (s, a)) (bw_ind_aux (Suc n))) (\<lambda>a. a \<in> A s) a}))"
proof -
  let ?s = "{a. is_arg_max (\<lambda>a. r (s, a) + measure_pmf.expectation (K (s, a)) (bw_ind_aux (Suc n))) (\<lambda>a. a \<in> A s) a}"
  have \<open>d ?s \<in> ?s\<close>
    using assms(1)[of " {a. is_arg_max (\<lambda>a. r (s, a) + measure_pmf.expectation (K (s, a)) (bw_ind_aux (Suc n))) (\<lambda>a. a \<in> A s) a}"]
    using  finite_is_arg_max A_ne assms
    by (auto simp add: finite_is_arg_max)
  thus ?thesis
    by auto
qed

lemma bw_ind_pol_gen:
  assumes "\<And>X. X \<noteq> {} \<Longrightarrow> d X \<in> X" "\<And>s. finite (A s)"
  shows "bw_ind_pol_gen d \<in> \<Pi>\<^sub>M\<^sub>D"
proof -
  have ***:"X \<noteq> {} \<Longrightarrow> X \<subseteq> Y \<Longrightarrow> d X \<in> Y" for X Y 
    using assms
    by auto
  have "\<exists>a. is_arg_max (\<lambda>a. r (s, a) + measure_pmf.expectation (K (s, a)) (bw_ind_aux (Suc n))) (\<lambda>a. a \<in> A s) a" for n s
    using finite_is_arg_max[OF assms(2) A_ne]
    by auto
  thus ?thesis
    unfolding bw_ind_pol_gen_def is_dec_det_def
    by (force intro!: ***)
qed

lemma
  assumes "\<And>X. X \<noteq> {} \<Longrightarrow> d X \<in> X"  "\<And>s. finite (A s)" "length h \<le> N"
  shows "\<nu>N_eval (mk_markovian_det (bw_ind_pol_gen d)) h s = \<nu>N_eval_opt h s"
proof -
  have "(\<And>h s. length h < N \<Longrightarrow>
            (\<Squnion>a\<in>A s. r (s, a) + measure_pmf.expectation (K (s, a)) (\<nu>N_opt_eqn (h @ [(s, a)])))
            \<le> r (s, bw_ind_pol_gen d (length h) s) +
               measure_pmf.expectation (K (s, bw_ind_pol_gen d (length h) s))
                (\<nu>N_opt_eqn (h @ [(s, bw_ind_pol_gen d (length h) s)])))"
    using A_ne bw_ind_pol_is_arg_max[OF assms(1,2)]
    unfolding bw_ind_aux_eq[symmetric]
    by (auto intro!: cSUP_least simp: bw_ind_pol_gen_def)
  hence "length h \<le> N \<Longrightarrow> \<nu>N_opt_eqn h s \<le> \<nu>N_eval (mk_markovian_det (bw_ind_pol_gen d)) h s" for h s
    using assms bw_ind_pol_gen thm_4_3_4[of 0 "bw_ind_pol_gen d", simplified]
    by auto
  thus ?thesis
    using \<nu>N_opt_eq \<nu>N_eval_le_opt assms bw_ind_pol_gen mk_markovian_det_preserves
    by (auto intro!: antisym)
qed


lemma bw_ind_aux'_eq: "n \<le> N \<Longrightarrow> bw_ind_aux' N (\<lambda>i s. if i = N then r_fin s else 0) n = bw_ind_aux n"
  using bw_ind_def bw_ind_correct by presburger
end

end