(*
  File:     Continued_Fractions/E_CFrac.thy
  Author:   Manuel Eberl, University of Innsbruck
*)
section \<open>The continued fraction expansion of $e$\<close>
theory E_CFrac
imports
  "HOL-Analysis.Analysis"
  "Continued_Fractions"
  "Quadratic_Irrationals"
begin

lemma fact_real_at_top: "filterlim (fact :: nat \<Rightarrow> real) at_top at_top"
proof (rule filterlim_at_top_mono)
  have "real n \<le> real (fact n)" for n
    unfolding of_nat_le_iff by (rule fact_ge_self)
  thus "eventually (\<lambda>n. real n \<le> fact n) at_top" by simp
qed (fact filterlim_real_sequentially)

lemma filterlim_div_nat_at_top:
  assumes "filterlim f at_top F" "m > 0"
  shows   "filterlim (\<lambda>x. f x div m :: nat) at_top F"
  unfolding filterlim_at_top
proof
  fix C :: nat
  from assms(1) have "eventually (\<lambda>x. f x \<ge> C * m) F"
    by (auto simp: filterlim_at_top)
  thus "eventually (\<lambda>x. f x div m \<ge> C) F"
  proof eventually_elim
    case (elim x)
    hence "(C * m) div m \<le> f x div m"
      by (intro div_le_mono)
    thus ?case using \<open>m > 0\<close> by simp
  qed
qed

text \<open>
  The continued fraction expansion of $e$ has the form
  $[2; 1, 2, 1, 1, 4, 1, 1, 6, 1, 1, 8, 1, \ldots]$:
\<close>
definition e_cfrac where
  "e_cfrac = cfrac (\<lambda>n. if n = 0 then 2 else if n mod 3 = 2 then 2 * (Suc n div 3) else 1)"

lemma cfrac_nth_e:
  "cfrac_nth e_cfrac n = (if n = 0 then 2 else if n mod 3 = 2 then 2 * (Suc n div 3) else 1)"
  unfolding e_cfrac_def by (subst cfrac_nth_cfrac) (auto simp: is_cfrac_def)

lemma cfrac_length_e [simp]: "cfrac_length e_cfrac = \<infinity>"
  by (simp add: e_cfrac_def)


text \<open>
  The formalised proof follows the one from Proof Wiki~\cite{proofwiki}.
\<close>

context
  fixes A B C :: "nat \<Rightarrow> real" and p q :: "nat \<Rightarrow> int" and a :: "nat \<Rightarrow> int"
  defines "A \<equiv> (\<lambda>n. integral {0..1} (\<lambda>x. exp x * x ^ n * (x - 1) ^ n / fact n))"
      and "B \<equiv> (\<lambda>n. integral {0..1} (\<lambda>x. exp x * x ^ Suc n * (x - 1) ^ n / fact n))"
      and "C \<equiv> (\<lambda>n. integral {0..1} (\<lambda>x. exp x * x ^ n * (x - 1) ^ Suc n / fact n))"
      and "p \<equiv> (\<lambda>n. if n \<le> 1 then 1 else conv_num e_cfrac (n - 2))"
      and "q \<equiv> (\<lambda>n. if n = 0 then 1 else if n = 1 then 0 else conv_denom e_cfrac (n - 2))"
      and "a \<equiv> (\<lambda>n. if n mod 3 = 2 then 2 * (Suc n div 3) else 1)"
begin

lemma
  assumes "n \<ge> 2"
  shows   p_rec: "p n = a (n - 2) * p (n - 1) + p (n - 2)" (is ?th1)
    and   q_rec: "q n = a (n - 2) * q (n - 1) + q (n - 2)" (is ?th2)
proof -
  have n_minus_3: "n - 3 = n - Suc (Suc (Suc 0))"
    by (simp add: numeral_3_eq_3)
  consider "n = 2" | "n = 3" | "n \<ge> 4"
    using assms by force
  hence "?th1 \<and> ?th2"
    by cases (auto simp: p_def q_def cfrac_nth_e a_def conv_num_rec conv_denom_rec n_minus_3)
  thus ?th1 ?th2 by blast+
qed

lemma
  assumes "n \<ge> 1"
  shows   p_rec0: "p (3 * n) = p (3 * n - 1) + p (3 * n - 2)"
    and   q_rec0: "q (3 * n) = q (3 * n - 1) + q (3 * n - 2)"
proof -
  define n' where "n' = n - 1"
  from assms have "(3 * n' + 1) mod 3 \<noteq> 2"
    by presburger
  also have "(3 * n' + 1) = 3 * n - 2"
    using assms by (simp add: n'_def)
  finally show "p (3 * n) = p (3 * n - 1) + p (3 * n - 2)"
               "q (3 * n) = q (3 * n - 1) + q (3 * n - 2)"
    using assms by (subst p_rec q_rec; simp add: a_def)+
qed

lemma
  assumes "n \<ge> 1"
  shows   p_rec1: "p (3 * n + 1) = 2 * int n * p (3 * n) + p (3 * n - 1)"
    and   q_rec1: "q (3 * n + 1) = 2 * int n * q (3 * n) + q (3 * n - 1)"
proof -
  define n' where "n' = n - 1"
  from assms have "(3 * n' + 2) mod 3 = 2"
    by presburger
  also have "(3 * n' + 2) = 3 * n - 1"
    using assms by (simp add: n'_def)
  finally show "p (3 * n + 1) = 2 * int n * p (3 * n) + p (3 * n - 1)"
               "q (3 * n + 1) = 2 * int n * q (3 * n) + q (3 * n - 1)"
    using assms by (subst p_rec q_rec; simp add: a_def)+
qed

lemma p_rec2: "p (3 * n + 2) = p (3 * n + 1) + p (3 * n)"
  and q_rec2: "q (3 * n + 2) = q (3 * n + 1) + q (3 * n)"
  by (subst p_rec q_rec; simp add: a_def nat_mult_distrib nat_add_distrib)+

lemma A_0: "A 0 = exp 1 - 1" and B_0: "B 0 = 1" and C_0: "C 0 = 2 - exp 1"
proof -
  have "(exp has_integral (exp 1 - exp 0)) {0..1::real}"
    by (intro fundamental_theorem_of_calculus)
       (auto intro!: derivative_eq_intros 
             simp flip: has_real_derivative_iff_has_vector_derivative)
  thus "A 0 = exp 1 - 1" by (simp add: A_def has_integral_iff)

  have "((\<lambda>x. exp x * x) has_integral (exp 1 * (1 - 1) - exp 0 * (0 - 1))) {0..1::real}"
    by (intro fundamental_theorem_of_calculus)
       (auto intro!: derivative_eq_intros 
             simp flip: has_real_derivative_iff_has_vector_derivative simp: algebra_simps)
  thus "B 0 = 1" by (simp add: B_def has_integral_iff)

  have "((\<lambda>x. exp x * (x - 1)) has_integral (exp 1 * (1 - 2) - exp 0 * (0 - 2))) {0..1::real}"
    by (intro fundamental_theorem_of_calculus)
       (auto intro!: derivative_eq_intros 
             simp flip: has_real_derivative_iff_has_vector_derivative simp: algebra_simps)
  thus "C 0 = 2 - exp 1" by (simp add: C_def has_integral_iff)
qed

lemma A_bound: "norm (A n) \<le> exp 1 / fact n"
proof -
  have "norm (exp t * t ^ n * (t - 1) ^ n / fact n) \<le> exp 1 * 1 ^ n * 1 ^ n / fact n" 
    if "t \<in> {0..1}" for t :: real using that unfolding norm_mult norm_divide norm_power norm_fact
    by (intro mult_mono divide_right_mono power_mono) auto
  hence "norm (A n) \<le> exp 1 / fact n * (1 - 0)"
    unfolding A_def by (intro integral_bound) (auto intro!: continuous_intros)
  thus ?thesis by simp
qed

lemma B_bound: "norm (B n) \<le> exp 1 / fact n"
proof -
  have "norm (exp t * t ^ Suc n * (t - 1) ^ n / fact n) \<le> exp 1 * 1 ^ Suc n * 1 ^ n / fact n" 
    if "t \<in> {0..1}" for t :: real using that unfolding norm_mult norm_divide norm_power norm_fact
    by (intro mult_mono divide_right_mono power_mono) auto
  hence "norm (B n) \<le> exp 1 / fact n * (1 - 0)"
    unfolding B_def by (intro integral_bound) (auto intro!: continuous_intros)
  thus ?thesis by simp
qed

lemma C_bound: "norm (C n) \<le> exp 1 / fact n"
proof -
  have "norm (exp t * t ^ n * (t - 1) ^ Suc n / fact n) \<le> exp 1 * 1 ^ n * 1 ^ Suc n / fact n" 
    if "t \<in> {0..1}" for t :: real using that unfolding norm_mult norm_divide norm_power norm_fact
    by (intro mult_mono divide_right_mono power_mono) auto
  hence "norm (C n) \<le> exp 1 / fact n * (1 - 0)"
    unfolding C_def by (intro integral_bound) (auto intro!: continuous_intros)
  thus ?thesis by simp
qed

lemma A_Suc: "A (Suc n) = -B n - C n"
proof -
  let ?g = "\<lambda>x. x ^ Suc n * (x - 1) ^ Suc n * exp x / fact (Suc n)"
  have pos: "fact n + real n * fact n > 0" by (intro add_pos_nonneg) auto
  have "A (Suc n) + B n + C n =
          integral {0..1} (\<lambda>x. exp x * x ^ Suc n * (x - 1) ^ Suc n / fact (Suc n) +
             exp x * x ^ Suc n * (x - 1) ^ n / fact n + exp x * x ^ n * (x - 1) ^ Suc n / fact n)"
    unfolding A_def B_def C_def
    apply (subst integral_add [symmetric])
    subgoal
      by (auto intro!: integrable_continuous_real continuous_intros)
    subgoal
      by (auto intro!: integrable_continuous_real continuous_intros)
    apply (subst integral_add [symmetric])
      apply (auto intro!: integrable_continuous_real continuous_intros)
    done
  also have "\<dots> = integral {0..1} (\<lambda>x. exp x / fact (Suc n) *
                    (x ^ Suc n * (x - 1) ^ Suc n + Suc n * x ^ Suc n * (x - 1) ^ n + 
                     Suc n * x ^ n * (x - 1) ^ Suc n))"
    (is "_ = integral _ ?f") 
    apply (simp add: divide_simps)
    apply (simp add: field_simps)?
    done
  also have "(?f has_integral (?g 1 - ?g 0)) {0..1}"
    apply (intro fundamental_theorem_of_calculus)
    subgoal
      by simp
    unfolding has_real_derivative_iff_has_vector_derivative [symmetric]
    apply (rule derivative_eq_intros refl | simp)+
    apply (simp add: algebra_simps)?
    done
  hence "integral {0..1} ?f = 0"
    by (simp add: has_integral_iff)
  finally show ?thesis by simp
qed

lemma B_Suc: "B (Suc n) = -2 * Suc n * A (Suc n) + C n"
proof -
  let ?g = "\<lambda>x. x ^ Suc n * (x - 1) ^ (n+2) * exp x / fact (Suc n)"
  have pos: "fact n + real n * fact n > 0" by (intro add_pos_nonneg) auto
  have "B (Suc n) + 2 * Suc n * A (Suc n) - C n =
          integral {0..1} (\<lambda>x. exp x * x^(n+2) * (x - 1)^(n+1) / fact (Suc n) + 2 * Suc n *
             exp x * x ^ Suc n * (x - 1) ^ Suc n / fact (Suc n) - exp x * x ^ n * (x - 1) ^ Suc n / fact n)"
    unfolding A_def B_def C_def integral_mult_right [symmetric]
    apply (subst integral_add [symmetric])
    subgoal
      by (auto intro!: integrable_continuous_real continuous_intros)
    subgoal
      by (auto intro!: integrable_continuous_real continuous_intros)
    apply (subst integral_diff [symmetric])
      apply (auto intro!: integrable_continuous_real continuous_intros simp: mult_ac)
    done
  also have "\<dots> = integral {0..1} (\<lambda>x. exp x / fact (Suc n) *
                    (x^(n+2) * (x - 1)^(n+1) + 2 * Suc n * x ^ Suc n * (x - 1) ^ Suc n - 
                     Suc n * x ^ n * (x - 1) ^ Suc n))"
    (is "_ = integral _ ?f") 
    apply (simp add: divide_simps)
    apply (simp add: field_simps)?
    done
  also have "(?f has_integral (?g 1 - ?g 0)) {0..1}"
    apply (intro fundamental_theorem_of_calculus)
     apply (simp; fail)
    unfolding has_real_derivative_iff_has_vector_derivative [symmetric]
    apply (rule derivative_eq_intros refl | simp)+
    apply (simp add: algebra_simps)?
    done
  hence "integral {0..1} ?f = 0"
    by (simp add: has_integral_iff)
  finally show ?thesis by (simp add: algebra_simps)
qed

lemma C_Suc: "C n = B n - A n"
  unfolding A_def B_def C_def
  by (subst integral_diff [symmetric])
     (auto intro!: integrable_continuous_real continuous_intros simp: field_simps)

lemma unfold_add_numeral: "c * n + numeral b = Suc (c * n + pred_numeral b)"
  by simp

lemma ABC:
  "A n = q (3 * n) * exp 1 - p (3 * n) \<and>
   B n = p (Suc (3 * n)) - q (Suc (3 * n)) * exp 1 \<and>
   C n = p (Suc (Suc (3 * n))) - q (Suc (Suc (3 * n))) * exp 1"
proof (induction n)
  case 0
  thus ?case by (simp add: A_0 B_0 C_0 a_def p_def q_def cfrac_nth_e)
next
  case (Suc n)
  note [simp] =
    conjunct1[OF Suc.IH] conjunct1[OF conjunct2[OF Suc.IH]] conjunct2[OF conjunct2[OF Suc.IH]]
  have [simp]: "3 + m = Suc (Suc (Suc m))" for m by simp
  
  have A': "A (Suc n) = of_int (q (3 * Suc n)) * exp 1 - of_int (p (3 * Suc n))"
    unfolding A_Suc
    by (subst p_rec0 q_rec0, simp)+ (auto simp: algebra_simps)
  have B': "B (Suc n) = of_int (p (3 * Suc n + 1)) - of_int (q (3 * Suc n + 1)) * exp 1"
    unfolding B_Suc
    by (subst p_rec1 q_rec1 p_rec0 q_rec0, simp)+ (auto simp: algebra_simps A_Suc)
  have C': "C (Suc n) = of_int (p (3*Suc n+2)) - of_int (q (3*Suc n+2)) * exp 1"
    unfolding A_Suc B_Suc C_Suc using p_rec2[of n] q_rec2[of n]
    by ((subst p_rec2 q_rec2)+, (subst p_rec0 q_rec0 p_rec1 q_rec1, simp)+)
       (auto simp: algebra_simps A_Suc B_Suc)
  from A' B' C' show ?case by simp
qed

lemma q_pos: "q n > 0" if "n \<noteq> 1"
  using that by (auto simp: q_def)

lemma conv_diff_exp_bound: "norm (exp 1 - p n / q n) \<le> exp 1 / fact (n div 3)"
proof (cases "n = 1")
  case False
  define n' where "n' = n div 3"
  consider "n mod 3 = 0" | "n mod 3 = 1" | "n mod 3 = 2"
    by force
  hence diff [unfolded n'_def]: "q n * exp 1 - p n =
    (if n mod 3 = 0 then A n' else if n mod 3 = 1 then -B n' else -C n')"
  proof cases
    assume "n mod 3 = 0"
    hence "3 * n' = n" unfolding n'_def by presburger
    with ABC[of n'] show ?thesis by auto
  next
    assume *: "n mod 3 = 1"
    hence "Suc (3 * n') = n" unfolding n'_def by presburger
    with * ABC[of n'] show ?thesis by auto
  next
    assume *: "n mod 3 = 2"
    hence "Suc (Suc (3 * n')) = n" unfolding n'_def by presburger
    with * ABC[of n'] show ?thesis by auto
  qed

  note [[linarith_split_limit = 0]]
  have "norm ((q n * exp 1 - p n) / q n) \<le> exp 1 / fact (n div 3) / 1" unfolding diff norm_divide 
    using A_bound[of "n div 3"] B_bound[of "n div 3"] C_bound[of "n div 3"] q_pos[OF \<open>n \<noteq> 1\<close>]
    by (subst frac_le) (auto simp: of_nat_ge_1_iff)
  also have "(q n * exp 1 - p n) / q n = exp 1 - p n / q n"
    using q_pos[OF \<open>n \<noteq> 1\<close>] by (simp add: divide_simps)
  finally show ?thesis by simp
qed (auto simp: p_def q_def)

theorem e_cfrac: "cfrac_lim e_cfrac = exp 1"
proof -
  have num: "conv_num e_cfrac n = p (n + 2)"
   and denom: "conv_denom e_cfrac n = q (n + 2)" for n
    by (simp_all add: p_def q_def)

  have "(\<lambda>n. exp 1 - p n / q n) \<longlonglongrightarrow> 0"
  proof (rule Lim_null_comparison)
    show "eventually (\<lambda>n. norm (exp 1 - p n / q n) \<le> exp 1 / fact (n div 3)) at_top"
      using conv_diff_exp_bound by (intro always_eventually) auto
    show "(\<lambda>n. exp 1 / fact (n div 3) :: real) \<longlonglongrightarrow> 0"
      by (rule real_tendsto_divide_at_top tendsto_const filterlim_div_nat_at_top
               filterlim_ident filterlim_compose[OF fact_real_at_top])+ auto
  qed
  moreover have "eventually (\<lambda>n. exp 1 - p n / q n = exp 1 - conv e_cfrac (n - 2)) at_top"
    using eventually_ge_at_top[of 2]
  proof eventually_elim
    case (elim n)
    with num[of "n - 2"] denom[of "n - 2"] wf show ?case
      by (simp add: eval_nat_numeral Suc_diff_Suc conv_num_denom)
  qed
  ultimately have "(\<lambda>n. exp 1 - conv e_cfrac (n - 2)) \<longlonglongrightarrow> 0"
    using Lim_transform_eventually by fast
  hence "(\<lambda>n. exp 1 - (exp 1 - conv e_cfrac (Suc (Suc n) - 2))) \<longlonglongrightarrow> exp 1 - 0"
    by (subst filterlim_sequentially_Suc)+ (intro tendsto_diff tendsto_const)
  hence "conv e_cfrac \<longlonglongrightarrow> exp 1" by simp
  moreover have "conv e_cfrac \<longlonglongrightarrow> cfrac_lim e_cfrac"
    by (intro LIMSEQ_cfrac_lim wf) auto
  ultimately have "exp 1 = cfrac_lim e_cfrac"
    by (rule LIMSEQ_unique)
  thus ?thesis ..
qed

corollary e_cfrac_altdef: "e_cfrac = cfrac_of_real (exp 1)"
  by (metis e_cfrac cfrac_infinite_iff cfrac_length_e cfrac_of_real_cfrac_lim_irrational)

text \<open>
  This also provides us with a nice proof that $e$ is not rational and not a quadratic irrational
  either.
\<close>
corollary exp1_irrational: "(exp 1 :: real) \<notin> \<rat>"
  by (metis cfrac_length_e e_cfrac cfrac_infinite_iff)

corollary exp1_not_quadratic_irrational: "\<not>quadratic_irrational (exp 1 :: real)"
proof -
  have "range (\<lambda>n. 2 * (int n + 1)) \<subseteq> range (cfrac_nth e_cfrac)"
  proof safe
    fix n :: nat
    have "cfrac_nth e_cfrac (3*n+2) \<in> range (cfrac_nth e_cfrac)"
      by blast
    also have "(3 * n + 2) mod 3 = 2"
      by presburger
    hence "cfrac_nth e_cfrac (3*n+2) = 2 * (int n + 1)"
      by (simp add: cfrac_nth_e)
    finally show "2 * (int n + 1) \<in> range (cfrac_nth e_cfrac)" .
  qed
  moreover have "infinite (range (\<lambda>n. 2 * (int n + 1)))"
    by (subst finite_image_iff) (auto intro!: injI)
  ultimately have "infinite (range (cfrac_nth e_cfrac))"
    using finite_subset by blast
  thus ?thesis using quadratic_irrational_cfrac_nth_range_finite[of e_cfrac]
    by (auto simp: e_cfrac)
qed
      
end
end