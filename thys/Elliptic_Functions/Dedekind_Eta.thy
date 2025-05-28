section \<open>The Dedekind \<open>\<eta>\<close> function\<close>
theory Dedekind_Eta
imports
  Bernoulli.Bernoulli
  Theta_Inversion
  Basic_Modular_Forms
  Dedekind_Sums.Dedekind_Sums
  Pentagonal_Number_Theorem.Pentagonal_Number_Theorem
begin

(* TODO Fixme *)
hide_const (open) Unique_Factorization.coprime


subsection \<open>Definition and basic properties\<close>

(* Definition in 3.1 p.47 *)
definition dedekind_eta:: "complex \<Rightarrow> complex" ("\<eta>") where
  "\<eta> z = to_nome (z / 12) * euler_phi (to_nome (2*z))"

lemma dedekind_eta_nonzero [simp]: "Im z > 0 \<Longrightarrow> \<eta> z \<noteq> 0"
  by (auto simp: dedekind_eta_def norm_to_nome norm_power power_less_one_iff)

lemma holomorphic_dedekind_eta [holomorphic_intros]:
  assumes "A \<subseteq> {z. Im z > 0}"
  shows   "\<eta> holomorphic_on A"
  using assms unfolding dedekind_eta_def 
  by (auto intro!: holomorphic_intros simp: norm_to_nome norm_power power_less_one_iff)

lemma holomorphic_dedekind_eta' [holomorphic_intros]:
  assumes "f holomorphic_on A" "\<And>z. z \<in> A \<Longrightarrow> Im (f z) > 0"
  shows   "(\<lambda>z. \<eta> (f z)) holomorphic_on A"
  using assms unfolding dedekind_eta_def 
  by (auto intro!: holomorphic_intros simp: norm_to_nome norm_power power_less_one_iff)

lemma analytic_dedekind_eta [analytic_intros]:
  assumes "A \<subseteq> {z. Im z > 0}"
  shows   "\<eta> analytic_on A"
  using assms unfolding dedekind_eta_def 
  by (auto intro!: analytic_intros simp: norm_to_nome norm_power power_less_one_iff)

lemma analytic_dedekind_eta' [analytic_intros]:
  assumes "f analytic_on A" "\<And>z. z \<in> A \<Longrightarrow> Im (f z) > 0"
  shows   "(\<lambda>z. \<eta> (f z)) analytic_on A"
  using assms unfolding dedekind_eta_def 
  by (auto intro!: analytic_intros simp: norm_to_nome norm_power power_less_one_iff)

lemma meromorphic_on_dedekind_eta [meromorphic_intros]:
  "f analytic_on A \<Longrightarrow> (\<And>z. z \<in> A \<Longrightarrow> Im (f z) > 0) \<Longrightarrow> (\<lambda>z. \<eta> (f z)) meromorphic_on A"
  by (rule analytic_on_imp_meromorphic_on) (auto intro!: analytic_intros)

lemma continuous_on_dedekind_eta [continuous_intros]:
  "A \<subseteq> {z. Im z > 0} \<Longrightarrow> continuous_on A \<eta>"
  unfolding dedekind_eta_def 
  by (intro continuous_intros) (auto simp: norm_to_nome norm_power power_less_one_iff)

lemma continuous_on_dedekind_eta' [continuous_intros]:
  assumes "continuous_on A f" "\<And>z. z \<in> A \<Longrightarrow> Im (f z) > 0"
  shows   "continuous_on A (\<lambda>z. \<eta> (f z))"
  using assms unfolding dedekind_eta_def 
  by (intro continuous_intros) (auto simp: norm_to_nome norm_power power_less_one_iff)

lemma tendsto_dedekind_eta [tendsto_intros]:
  assumes "(f \<longlongrightarrow> c) F" "Im c > 0"
  shows   "((\<lambda>x. \<eta> (f x)) \<longlongrightarrow> \<eta> c) F"
  unfolding dedekind_eta_def using assms 
  by (intro tendsto_intros assms) (auto simp: norm_to_nome norm_power power_less_one_iff)

lemma tendsto_at_cusp_dedekind_eta [tendsto_intros]: "(\<eta> \<longlongrightarrow> 0) at_\<i>\<infinity>"
proof -
  have "filterlim (\<lambda>x::real. x / 12) at_top at_top"
    by real_asymp
  hence "filterlim (\<lambda>z. Im z / 12) at_top at_\<i>\<infinity>"
    by (rule filterlim_at_ii_infI)
  hence *: "((\<lambda>z. to_nome (z / 12)) \<longlongrightarrow> 0) at_\<i>\<infinity>"
    by (intro tendsto_0_to_nome) simp_all

  have "filterlim (\<lambda>x::real. 2 * x) at_top at_top"
    by real_asymp
  hence "filterlim (\<lambda>z. 2 * Im z) at_top at_\<i>\<infinity>"
    by (rule filterlim_at_ii_infI)
  hence **: "((\<lambda>z. to_nome (2 * z)) \<longlongrightarrow> 0) at_\<i>\<infinity>"
    by (intro tendsto_0_to_nome) simp_all

  have "((\<lambda>z. to_nome (z / 12) * euler_phi (to_nome (2*z))) \<longlongrightarrow> 0 * euler_phi 0) at_\<i>\<infinity>"
    by (intro tendsto_intros * **) auto
  thus ?thesis
    by (simp add: dedekind_eta_def [abs_def])
qed

lemma dedekind_eta_plus1:
  assumes z: "Im z > 0"
  shows   "\<eta> (z + 1) = cis (pi/12) * \<eta> z"
proof -
  have "\<eta> (z + 1) = to_nome ((z + 1) / 12) * euler_phi (to_nome (2 * (z + 1)))"
    by (simp add: dedekind_eta_def)
  also have "to_nome (2 * (z + 1)) = to_nome (2 * z)"
    by (simp add: to_nome_add ring_distribs)
  also have "to_nome ((z + 1) / 12) = to_nome (1/12) * to_nome (z / 12)"
    by (simp add: to_nome_add add_divide_distrib)
  also have "to_nome (1/12) = cis (pi/12)"
    by (simp add: to_nome_def cis_conv_exp)
  also have "\<dots> * to_nome (z / 12) * euler_phi (to_nome (2*z)) = cis (pi/12) * \<eta> z"
    by (simp add: dedekind_eta_def mult_ac)
  finally show ?thesis by (simp add: cis_conv_exp mult_ac)
qed

lemma dedekind_eta_plus_nat:
  assumes z: "Im z > 0"
  shows   "\<eta> (z + of_nat n) = cis (pi * n / 12) * \<eta> z"
proof (induction n)
  case (Suc n)
  have "\<eta> (z + of_nat (Suc n)) = \<eta> (z + of_nat n + 1)"
    by (simp add: add_ac)
  also have "\<dots> = cis (pi/12) * \<eta> (z + of_nat n)"
    using z by (intro dedekind_eta_plus1) auto
  also have "\<eta> (z + of_nat n) = cis (pi*n/12) * \<eta> z"
    by (rule Suc.IH)
  also have "cis (pi/12) * (cis (pi*n/12) * \<eta> z) = cis (pi*Suc n/12) * \<eta> z"
    by (simp add: ring_distribs add_divide_distrib exp_add mult_ac cis_mult)
  finally show ?case .
qed auto

lemma dedekind_eta_plus_int:
  assumes z: "Im z > 0"
  shows   "\<eta> (z + of_int n) = cis (pi*n/12) * \<eta> z"
proof (cases "n \<ge> 0")
  case True
  thus ?thesis
    using dedekind_eta_plus_nat[OF assms, of "nat n"] by simp
next
  case False
  thus ?thesis
    using dedekind_eta_plus_nat[of "z + of_int n" "nat (-n)"] assms
    by (auto simp: cis_mult field_simps)
qed

text \<open>
  The logarithmic derivative of \<open>\<eta>\<close> is, up to a constant factor, the ``forbidden'' Eisenstein
  series $G_2$. This follows relatively easily from the logarithmic derivative of Euler's function
  $\phi$ and the Fourier expansion of $G_2$, both of which involve the Lambert series
  $\sum_{k=1}^\infty k \frac{q^k}{1-q^k}$.
\<close>
theorem deriv_dedekind_eta:
  assumes z: "Im z > 0"
  shows   "deriv \<eta> z = \<i> / (4 * of_real pi) * Eisenstein_G 2 z * \<eta> z"
proof -
  define f :: "complex \<Rightarrow> complex" where "f = deriv euler_phi"
  have *: "(euler_phi has_field_derivative f q) (at q within A)" if "norm q < 1" for q A
    unfolding f_def using that by (auto intro!: analytic_derivI analytic_intros)
  have [derivative_intros]:
    "((\<lambda>z. euler_phi (g z)) has_field_derivative f (g z) * g') (at z within A)" 
    if "(g has_field_derivative g') (at z within A)" "norm (g z) < 1" for g g' z A
    by (rule DERIV_chain'[OF that(1) *]) fact

  define L where "L = lambert complex_of_nat (to_nome (2 * z))"
  have L_eq: "L = 1 / 24 - Eisenstein_G 2 z / (8 * pi ^ 2)"
    by (subst Eisenstein_G_fourier_expansion)
       (use z in \<open>simp_all add: L_def zeta_2 field_simps to_q_conv_to_nome\<close>)

  have "deriv dedekind_eta z = \<i> * pi * (dedekind_eta z / 12 +
                               2 * (to_nome (z / 12) * (to_nome (2*z) * f (to_nome (2*z)))))"
    by (rule DERIV_imp_deriv)
       (use z in \<open>auto intro!: derivative_eq_intros DERIV_imp_deriv 
                       simp: norm_to_nome dedekind_eta_def [abs_def] algebra_simps\<close>)
  also have "to_nome (2 * z) * f (to_nome (2 * z)) = -L * euler_phi (to_nome (2 * z))"
    unfolding f_def by (subst deriv_euler_phi) (use z in \<open>auto simp: norm_to_nome L_def\<close>)
  also have "to_nome (z / 12) * \<dots> = -L * dedekind_eta z"
    by (simp add: dedekind_eta_def)
  finally have "deriv \<eta> z = (\<i> * pi * (1 / 12 - 2 * L)) * \<eta> z"
    using z by (simp add: field_simps)
  also have "(\<i> * pi * (1 / 12 - 2 * L)) = \<i> / (4 * of_real pi) * Eisenstein_G 2 z"
    unfolding L_eq by (simp add: power2_eq_square)
  finally show ?thesis .
qed

lemma has_field_derivative_dedekind_eta:
  assumes "(f has_field_derivative f') (at x within A)" "Im (f x) > 0"
  shows   "((\<lambda>x. \<eta> (f x)) has_field_derivative
             (\<i> / (4 * of_real pi) * Eisenstein_G 2 (f x) * \<eta> (f x) * f')) (at x within A)"
proof (rule DERIV_chain2[OF _ assms(1)])
  have "(\<eta> has_field_derivative deriv \<eta> (f x)) (at (f x))"
    by (rule analytic_derivI) (use assms(2) in \<open>auto intro!: analytic_intros\<close>)
  thus "(\<eta> has_field_derivative \<i> / (4 * complex_of_real pi) * 
          Eisenstein_G 2 (f x) * \<eta> (f x)) (at (f x))"
    by (subst (asm) deriv_dedekind_eta) (use assms(2) in auto)
qed


subsection \<open>Relation to the Jacobi \<open>\<theta>\<close> functions\<close>

lemma dedekind_eta_conv_jacobi_theta_01:
  assumes t: "Im t > 0"
  shows   "\<eta> t = to_nome (t / 12) * jacobi_theta_01 (-t/2) (3 * t)"
proof -
  include qpochhammer_inf_notation
  define q where "q = to_nome t"
  have q: "q \<noteq> 0" "norm q < 1"
    using t by (auto simp: q_def norm_to_nome)

  have "\<eta> t = to_nome (t / 12) * euler_phi (q ^ 2)"
    unfolding dedekind_eta_def by (simp add: q_def to_nome_power)
  also have "euler_phi (q ^ 2) = ramanujan_theta (- q\<^sup>2) (-(q ^ 4))"
    by (subst pentagonal_number_theorem_complex)
       (use q in \<open>simp_all add: norm_power power_less_1_iff\<close>)
  also have "ramanujan_theta (-(q ^ 2)) (- (q ^ 4)) = jacobi_theta_nome (-1/q) (q^3)"
    using q by (simp add: jacobi_theta_nome_def eval_nat_numeral mult_ac)
  also have "\<dots> = jacobi_theta_00 (-t/2 + 1/2) (3 * t)"
    by (simp add: jacobi_theta_00_def q_def to_nome_power to_nome_diff
                  power_divide diff_divide_distrib)
  also have "\<dots> = jacobi_theta_01 (-t/2) (3 * t)"
    by (simp add: jacobi_theta_01_def)
  finally show ?thesis .
qed

lemma jacobi_theta_01_nw_conv_dedekind_eta:
  assumes t: "Im t > 0"
  shows   "jacobi_theta_01 0 t = \<eta> (t/2) ^ 2 / \<eta> t"
proof -
  include qpochhammer_inf_notation
  define q where "q = to_nome t"
  have q: "q \<noteq> 0" "norm q < 1"
    using t by (auto simp: q_def norm_to_nome)
  have nz: "(q^2 ; q^2)\<^sub>\<infinity> \<noteq> 0"
    by (rule qpochhammer_inf_nonzero) (use q in \<open>auto simp: norm_power power_less_1_iff\<close>)
  have eq: "(q ; q)\<^sub>\<infinity> = (q ; q^2)\<^sub>\<infinity> * (q^2 ; q^2)\<^sub>\<infinity>"
    using prod_qpochhammer_inf_group[of q 2 q] q by (simp add: eval_nat_numeral)

  have "jacobi_theta_01 0 t = jacobi_theta_nome (-1) q"
    by (simp add: q_def jacobi_theta_01_def jacobi_theta_00_def)
  also have "\<dots> = (q^2 ; q^2)\<^sub>\<infinity> * (q ; q^2)\<^sub>\<infinity> ^ 2"
    by (subst jacobi_theta_nome_triple_product_complex) (use q in \<open>simp_all add: power2_eq_square\<close>)
  also have "\<dots> = euler_phi q ^ 2 / euler_phi (q ^ 2)"
    by (simp add: field_simps euler_phi_def eq power2_eq_square)
  also have "\<dots> = \<eta> (t/2) ^ 2 / \<eta> t"
    by (simp add: dedekind_eta_def power_mult_distrib to_nome_power q_def)
  finally show ?thesis .
qed

lemma jacobi_theta_00_nw_conv_dedekind_eta:
  assumes t: "Im t > 0"
  shows   "jacobi_theta_00 0 t = \<eta> ((t+1)/2) ^ 2 / \<eta> (t+1)"
proof -
  include qpochhammer_inf_notation
  define q where "q = to_nome t"
  have q: "q \<noteq> 0" "norm q < 1"
    using t by (auto simp: q_def norm_to_nome)
  have nz: "(q^2 ; q^2)\<^sub>\<infinity> \<noteq> 0"
    by (rule qpochhammer_inf_nonzero) (use q in \<open>auto simp: norm_power power_less_1_iff\<close>)
  have eq: "(-q ; -q)\<^sub>\<infinity> = (- q ; q^2)\<^sub>\<infinity> * (q^2 ; q^2)\<^sub>\<infinity>"
    using prod_qpochhammer_inf_group[of "-q" 2 "-q"] q by (simp add: eval_nat_numeral)

  have "jacobi_theta_00 0 t = jacobi_theta_nome 1 q"
    by (simp add: q_def jacobi_theta_00_def)
  also have "\<dots> = (q\<^sup>2; q\<^sup>2)\<^sub>\<infinity> * (-q; q\<^sup>2)\<^sub>\<infinity> ^ 2"
    by (subst jacobi_theta_nome_triple_product_complex) (use q in \<open>simp_all add: power2_eq_square\<close>)
  also have "\<dots> = euler_phi (-q) ^ 2 / euler_phi (q ^ 2)"
    using nz by (simp add: field_simps euler_phi_def power2_eq_square eq)
  also have "\<dots> = \<eta> ((t+1)/2) ^ 2 / \<eta> (t + 1)"
    by (simp add: dedekind_eta_def power_mult_distrib to_nome_power 
                  to_nome_add add_divide_distrib q_def)
  finally show ?thesis .
qed

lemma jacobi_theta_00_nw_conv_dedekind_eta':
  assumes t: "Im t > 0"
  shows   "jacobi_theta_00 0 t = \<eta> t ^ 5 / (\<eta> (t/2) * \<eta> (2*t)) ^ 2"
proof -
  include qpochhammer_inf_notation
  define q where "q = to_nome t"
  have q: "q \<noteq> 0" "norm q < 1"
    using t by (auto simp: q_def norm_to_nome)
  have nz': "(q ; q)\<^sub>\<infinity> \<noteq> 0"
    by (rule qpochhammer_inf_nonzero) (use q in \<open>auto simp: norm_power power_less_1_iff\<close>)
  have nz'': " (- q\<^sup>2 ; q\<^sup>2)\<^sub>\<infinity> \<noteq> 0"
    by (rule qpochhammer_inf_nonzero) (use q in \<open>auto simp: norm_power power_less_1_iff\<close>)
  have nz: "(q^2 ; q^2)\<^sub>\<infinity> \<noteq> 0"
    by (rule qpochhammer_inf_nonzero) (use q in \<open>auto simp: norm_power power_less_1_iff\<close>)
  have eq: "(-q ; q)\<^sub>\<infinity> = (- q ; q^2)\<^sub>\<infinity> * (-q\<^sup>2 ; q\<^sup>2)\<^sub>\<infinity>"
    using prod_qpochhammer_inf_group[of q 2 "-q"] q by (simp add: eval_nat_numeral)

  have "\<eta> t ^ 5 / (\<eta> (t/2) * \<eta> (2*t)) ^ 2 = 
          to_nome (5 * t / 12) / to_nome (t / 12) / to_nome (t / 3) * 
          euler_phi (q ^ 2) ^ 5 / (euler_phi q * euler_phi (q ^ 4))\<^sup>2"
    by (simp add: dedekind_eta_def power_mult_distrib to_nome_power q_def)
  also have "to_nome (5 * t / 12) / to_nome (t / 12) / to_nome (t / 3) = 
               to_nome (5 * t / 12 - t / 12 - t / 3)"
    unfolding to_nome_diff ..
  also have "5 * t / 12 - t / 12 - t / 3 = 0"
    by simp
  also have "to_nome 0 * euler_phi (q\<^sup>2) ^ 5 / (euler_phi q * euler_phi (q ^ 4))\<^sup>2 =
               (q\<^sup>2 ; q\<^sup>2)\<^sub>\<infinity> ^ 5 / ((q ; q)\<^sub>\<infinity> * (q ^ 4 ; q ^ 4)\<^sub>\<infinity>)\<^sup>2"
    by (simp add: euler_phi_def)
  finally have "\<eta> t ^ 5 / (\<eta> (t / 2) * \<eta> (2 * t))\<^sup>2 =
                  (q\<^sup>2 ; q\<^sup>2)\<^sub>\<infinity> ^ 5 / ((q ; q)\<^sub>\<infinity> * (q ^ 4 ; q ^ 4)\<^sub>\<infinity>)\<^sup>2" .
  also have "\<dots> = (q\<^sup>2 ; q\<^sup>2)\<^sub>\<infinity> * (q\<^sup>2 ; q\<^sup>2)\<^sub>\<infinity> ^ 2 / ((q ; q)\<^sub>\<infinity> * ((q ^ 4 ; q ^ 4)\<^sub>\<infinity> / (q\<^sup>2 ; q\<^sup>2)\<^sub>\<infinity>))\<^sup>2"
    by (simp add: eval_nat_numeral)
  also have "(q ^ 4 ; q ^ 4)\<^sub>\<infinity> / (q\<^sup>2 ; q\<^sup>2)\<^sub>\<infinity> = (-q\<^sup>2 ; q\<^sup>2)\<^sub>\<infinity>"
    using qpochhammer_inf_square[of "q^2" "q^2"] q nz
    by (simp add: norm_power power_less_1_iff field_simps)
  also have "(q\<^sup>2 ; q\<^sup>2)\<^sub>\<infinity> * (q\<^sup>2 ; q\<^sup>2)\<^sub>\<infinity> ^ 2 / ((q ; q)\<^sub>\<infinity> * (- q\<^sup>2 ; q\<^sup>2)\<^sub>\<infinity>)\<^sup>2 =
             (q\<^sup>2 ; q\<^sup>2)\<^sub>\<infinity> * ((q\<^sup>2 ; q\<^sup>2)\<^sub>\<infinity> / (q ; q)\<^sub>\<infinity> / (- q\<^sup>2 ; q\<^sup>2)\<^sub>\<infinity>) ^ 2"
    by (simp add: power_divide power_mult_distrib)
  also have "(q\<^sup>2 ; q\<^sup>2)\<^sub>\<infinity> / (q ; q)\<^sub>\<infinity> = (-q ; q)\<^sub>\<infinity>"
    using qpochhammer_inf_square[of "q" "q"] q nz'
    by (simp add: norm_power power_less_1_iff field_simps)
  also have "(-q ; q)\<^sub>\<infinity> / (- q\<^sup>2 ; q\<^sup>2)\<^sub>\<infinity> = (- q ; q\<^sup>2)\<^sub>\<infinity>"
    using eq nz'' by simp
  also have "(q\<^sup>2 ; q\<^sup>2)\<^sub>\<infinity> * (- q ; q\<^sup>2)\<^sub>\<infinity>\<^sup>2 = jacobi_theta_nome 1 q"
    by (subst jacobi_theta_nome_triple_product_complex) (use q in \<open>simp_all add: power2_eq_square\<close>)
  also have "\<dots> = jacobi_theta_00 0 t"
    by (simp add: q_def jacobi_theta_00_def)
  finally show ?thesis ..
qed

lemma jacobi_theta_10_nw_conv_dedekind_eta:
  assumes t: "Im t > 0"
  shows   "jacobi_theta_10 0 t = 2 * \<eta> (2*t) ^ 2 / \<eta> t"
proof -
  include qpochhammer_inf_notation
  define q where "q = to_nome t"
  have q: "q \<noteq> 0" "norm q < 1"
    using t by (auto simp: q_def norm_to_nome)
  have nz: "(q^2 ; q^2)\<^sub>\<infinity> \<noteq> 0"
    by (rule qpochhammer_inf_nonzero) (use q in \<open>auto simp: norm_power power_less_1_iff\<close>)

  have "2 * \<eta> (2*t) ^ 2 / \<eta> t = 
          2 * (to_nome (t / 3) / to_nome (t / 12)) * euler_phi (q^4) ^ 2 / euler_phi (q^2)"
    by (auto simp: dedekind_eta_def power_mult_distrib to_nome_power q_def)
  also have "to_nome (t / 3) / to_nome (t / 12) = to_nome (t / 3 - t / 12)"
    by (subst to_nome_diff) auto
  also have "t / 3 - t / 12 = t / 4"
    by auto
  finally have *: "2 * \<eta> (2*t) ^ 2 / \<eta> t = 
                   2 * to_nome (t/4) * euler_phi (q^4) ^ 2 / euler_phi (q^2)" .

  have "jacobi_theta_10 0 t = to_nome (t / 4) * jacobi_theta_nome q q"
    by (simp add: q_def jacobi_theta_10_def jacobi_theta_00_def to_nome_power)
  also have "\<dots> = to_nome (t / 4) * ((q\<^sup>2 ; q\<^sup>2)\<^sub>\<infinity> * (-(q\<^sup>2) ; q\<^sup>2)\<^sub>\<infinity> * (-1 ; q\<^sup>2)\<^sub>\<infinity>)"
    by (subst jacobi_theta_nome_triple_product_complex) (use q in \<open>auto simp: power2_eq_square\<close>)
  also have "(-1 ; q\<^sup>2)\<^sub>\<infinity> = 2 * (-q\<^sup>2 ; q\<^sup>2)\<^sub>\<infinity>"
    using qpochhammer_inf_mult_q[of "q^2" "-1"] q by (simp add: norm_power power_less_1_iff)
  also have "(q\<^sup>2 ; q\<^sup>2)\<^sub>\<infinity> * (- q\<^sup>2 ; q\<^sup>2)\<^sub>\<infinity> * (2 * (-q\<^sup>2 ; q\<^sup>2)\<^sub>\<infinity>) = 
               2 * ((q\<^sup>2 ; q\<^sup>2)\<^sub>\<infinity> * (-q\<^sup>2 ; q\<^sup>2)\<^sub>\<infinity>) ^ 2 / (q\<^sup>2 ; q\<^sup>2)\<^sub>\<infinity>"
    using nz by (simp add: power2_eq_square)
  also have "\<dots> = 2 * (q ^ 4 ; q ^ 4)\<^sub>\<infinity> ^ 2 / (q\<^sup>2 ; q\<^sup>2)\<^sub>\<infinity>"
    by (subst qpochhammer_inf_square) (use q in \<open>auto simp: norm_power power_less_1_iff\<close>)
  also have "\<dots> = 2 * euler_phi (q^4) ^ 2 / euler_phi (q^2)"
    using nz by (simp add: euler_phi_def power2_eq_square)
  also have "to_nome (t / 4) * \<dots> = 2 * \<eta> (2*t) ^ 2 / \<eta> t"
    using * by simp
  finally show ?thesis .
qed

lemma jacobi_theta_00_01_10_nw_conv_dedekind_eta:
  assumes t: "Im t > 0"
  shows   "jacobi_theta_00 0 t * jacobi_theta_01 0 t * jacobi_theta_10 0 t = 2 * \<eta> t ^ 3"
  using t by (simp add: jacobi_theta_00_nw_conv_dedekind_eta' field_simps eval_nat_numeral
                jacobi_theta_01_nw_conv_dedekind_eta jacobi_theta_10_nw_conv_dedekind_eta)




subsection \<open>The inversion identity\<close>

text \<open>
  The inversion identity for Jacobi's \<open>\<theta>\<close> function together with the Jacobi triple product allows
  us to give a rather short proof of the inversion law for \<open>\<eta>\<close>. This is remarkable: Apostol
  spends the majority of the chapter on proving this.

  We would like to thank Alexey Ustinov, who answered a question of ours on MathOverflow and
  clarified how to prove the following lemma.
\<close>
lemma dedekind_eta_minus_one_over_aux:
  assumes "Im t > 0"
  shows   "jacobi_theta_10 (1 / 6) (t / 3) = 
             of_real (sqrt 3) * to_nome (t / 12) * jacobi_theta_01 (-t / 2) (3 * t)"
proof -
  include qpochhammer_inf_notation
  define q where "q = to_nome (t / 12)"
  define r where "r = to_nome (1 / 6)"
  define r' where "r' = to_nome (2/3)"

  have cos_120': "cos (pi * 2 / 3) = -1/2"
    using cos_120 by (simp add: field_simps)
  have sin_120': "sin (pi * 2 / 3) = sqrt 3 / 2"
    using sin_120 by (simp add: field_simps)

  have [simp]: "q \<noteq> 0" "r \<noteq> 0"
    by (auto simp: q_def r_def)
  have q: "norm q < 1"
    using assms by (simp add: q_def norm_to_nome)
  have [simp]: "norm (q ^ n) < 1 \<longleftrightarrow> n > 0" for n
    using q by (auto simp: norm_power power_less_1_iff)
  have "jacobi_theta_10 (1 / 6) (t / 3) = r * q * jacobi_theta_nome (r^2 * q^4) (q^4)"
    by (simp add: jacobi_theta_10_def jacobi_theta_00_def power2_eq_square
                  q_def r_def to_nome_power add_ac flip: to_nome_add)
  also have "\<dots> = r * q * ((q^8 ; q^8)\<^sub>\<infinity> * ((-(r^2)) * q^8 ; q ^ 8)\<^sub>\<infinity> * (-(1/r^2) ; q^8)\<^sub>\<infinity>)"
    by (subst jacobi_theta_nome_triple_product_complex) 
       (auto simp: q norm_power power_less_one_iff algebra_simps)
  also have "-(r^2) = r'^2"
  proof -
    have "-(r^2) = to_nome (1 + 1/3)"
      unfolding to_nome_add by (simp add: r_def to_nome_power)
    also have "\<dots> = r' ^ 2"
      by (simp add: r'_def to_nome_power)
    finally show ?thesis .
  qed
  also have "-(1/r^2) = r'"
    by (auto simp: r_def r'_def to_nome_power field_simps simp flip: to_nome_add)
  also have "(r' ; q ^ 8)\<^sub>\<infinity> = (r' * q ^ 8 ; q ^ 8)\<^sub>\<infinity> * (1 - r')"
    by (subst qpochhammer_inf_mult_q) auto
  finally have "jacobi_theta_10 (1 / 6) (t / 3) =
              r * (1 - r') * q * (\<Prod>k<3. (r' ^k * q ^ 8 ; q ^ 8)\<^sub>\<infinity>)"
    by (simp add: numeral_3_eq_3 mult_ac power2_eq_square)
  also have "r * (1 - r') = of_real (sqrt 3)"
    by (simp add: r_def r'_def to_nome_def exp_eq_polar complex_eq_iff
                  cos_30 sin_30 cos_120' sin_120' field_simps)
  also have "(\<Prod>k<3. (r' ^ k * q ^ 8 ; q ^ 8)\<^sub>\<infinity>) = (q ^ 24 ; q ^ 24)\<^sub>\<infinity>"
  proof -
    interpret primroot_cis 3 1
      rewrites "cis (2 * pi * 1 / 3) \<equiv> r'" and
               "cis (2 * pi * j * of_int 1 / of_nat 3) \<equiv> r' ^ j" for j
      by unfold_locales (auto simp: r'_def cis_conv_to_nome to_nome_power field_simps)
    show ?thesis
      using prod_qpochhammer_group_cis[of "q^8" "q^8"] by simp
  qed
  finally have eq1: "jacobi_theta_10 (1 / 6) (t / 3) =
                     complex_of_real (sqrt 3) * q * (q ^ 24 ; q ^ 24)\<^sub>\<infinity>" .

  
  have "jacobi_theta_01 (-t / 2) (3 * t) = jacobi_theta_nome (r^6 / q^12) (q^36)"
    by (simp add: jacobi_theta_01_def jacobi_theta_00_def power2_eq_square
                     q_def r_def to_nome_power flip: to_nome_add to_nome_diff to_nome_minus)
       (simp add: to_nome_diff to_nome_minus field_simps)?
  also have "\<dots> = (q^72; q^72)\<^sub>\<infinity> * (q^48 ; q^72)\<^sub>\<infinity> * ((q^36 / q^12) ; q^72)\<^sub>\<infinity>"
    by (subst jacobi_theta_nome_triple_product_complex) 
       (auto simp: q norm_power power_less_one_iff to_nome_power field_simps r_def)
  also have "q^36 / q^12 = q^24"
    by (auto simp: field_simps)
  finally have "jacobi_theta_01 (- t / 2) (3 * t) = (\<Prod>k<3. (q^24 * (q^24)^k ; q^72)\<^sub>\<infinity>)"
    by (simp add: numeral_3_eq_3 mult_ac)
  also have "\<dots> = (q ^ 24 ; q ^ 24)\<^sub>\<infinity>"
    using prod_qpochhammer_inf_group[of "q^24" 3 "q^24"] by simp
  finally have "jacobi_theta_01 (-t/2) (3*t) = (q^24; q^24)\<^sub>\<infinity>" .
  hence eq2: "of_real (sqrt 3) * to_nome (t / 12) * jacobi_theta_01 (-t/2) (3*t) =
              of_real (sqrt 3) * q * (q^24; q^24)\<^sub>\<infinity>"
    by (simp add: q_def)

  from eq1 eq2 show ?thesis
    by simp
qed

theorem dedekind_eta_minus_one_over:
  assumes t: "Im t > 0"
  shows   "\<eta> (-(1/t)) = csqrt (-\<i>*t) * \<eta> t"
proof -
  have [simp]: "t \<noteq> 0"
    using t by auto
  have "\<eta> (-1/t) = to_nome (- (1 / (t * 12))) * jacobi_theta_01 (1 / (t * 2)) (-(1 / (t / 3)))"
    by (subst dedekind_eta_conv_jacobi_theta_01) (use assms in \<open>auto simp: Im_complex_div_lt_0\<close>)
  also have "\<dots> = csqrt ((1/3) * (-\<i> * t)) * jacobi_theta_10 (1 / 6) (t / 3)"
    by (subst jacobi_theta_01_minus_one_over)
       (auto simp: to_nome_diff to_nome_minus to_nome_add field_simps t power2_eq_square)
  also have "csqrt ((1/3) * (-\<i> * t)) = csqrt (-\<i> * t) / sqrt 3"
    by (subst csqrt_mult) (use Arg_eq_0[of "1/3"] in \<open>auto simp: Arg_bounded real_sqrt_divide\<close>)
  also have "jacobi_theta_10 (1 / 6) (t / 3) = 
               of_real (sqrt 3) * to_nome (t / 12) * jacobi_theta_01 (-t / 2) (3 * t)"
    by (rule dedekind_eta_minus_one_over_aux) fact
  also have "\<dots> = sqrt 3 * \<eta> t"
    using t by (simp add: jacobi_theta_10_def dedekind_eta_conv_jacobi_theta_01)
  finally show ?thesis
    by simp
qed


subsection \<open>General transformation law\<close>

text \<open>
  From our results so far, it is easy to see that $\eta^{24}$ is a modular form of weight 12.
  Thus it follows that if $A = \begin{pmatrix}a&b\\c&d\end{pmatrix}\in\text{SL}(2)$ is a
  modular transformation, then $\eta(Az) = \epsilon(A)\sqrt{z}\eta(z)$, where $\epsilon(A)$ is
  a 24-th unit root that depends on $A$ but not on $z$.

  In the this section, we will give a concrete definition of this 24-th root \<open>\<epsilon>\<close> in terms of $A$.
\<close>
definition dedekind_eps :: "modgrp \<Rightarrow> complex" ("\<epsilon>") where
  "\<epsilon> f =
     (if is_singular_modgrp f then
        cis (pi * ((modgrp_a f + modgrp_d f) / (12 * modgrp_c f) -
          dedekind_sum (modgrp_d f) (modgrp_c f) - 1 / 4))
      else
        cis (pi * modgrp_b f / 12)
     )"

lemma dedekind_eps_1 [simp]: "dedekind_eps 1 = 1"
  by (simp add: dedekind_eps_def)

lemma dedekind_eps_shift [simp]: "\<epsilon> (shift_modgrp m) = cis (pi * m / 12)"
  by (simp add: dedekind_eps_def dedekind_sum_def)

lemma dedekind_eps_S [simp]: "dedekind_eps S_modgrp = cis (-pi / 4)"
  by (simp add: dedekind_eps_def dedekind_sum_def complex_eq_iff)

lemma dedekind_eps_shift_right [simp]: "\<epsilon> (f * shift_modgrp m) = cis (pi * m / 12) * \<epsilon> f"
proof (cases "is_singular_modgrp f")
  case True
  have [simp]: "modgrp_c f \<noteq> 0"
    using True by (simp add: is_singular_modgrp_altdef)
  have "dedekind_sum (modgrp_c f * m + modgrp_d f) (modgrp_c f) =
        dedekind_sum (modgrp_d f) (modgrp_c f)"
  proof (intro dedekind_sum_cong)
    have "[modgrp_c f * m + modgrp_d f = 0 + modgrp_d f] (mod modgrp_c f)"
      by (intro cong_add) (auto simp: Cong.cong_def)
    thus "[modgrp_c f * m + modgrp_d f = modgrp_d f] (mod modgrp_c f)"
      by simp
  qed (use coprime_modgrp_c_d[of f] in \<open>auto simp: Rings.coprime_commute\<close>)
  thus ?thesis using True
    by (simp add: dedekind_eps_def add_divide_distrib ring_distribs is_singular_modgrp_times_iff
             flip: cis_mult cis_divide)
next
  case False
  define n where "n = modgrp_b f"
  have f: "f = shift_modgrp n"
    unfolding n_def using False by (rule not_singular_modgrpD)
  have "f * shift_modgrp m = shift_modgrp (n + m)"
    by (simp add: shift_modgrp_add f)
  also have "\<epsilon> \<dots> = cis (pi * m / 12) * \<epsilon> f"
    by (simp add: f dedekind_eps_def cis_mult ring_distribs add_divide_distrib add_ac)
  finally show ?thesis .
qed

lemma dedekind_eps_shift_left [simp]: "\<epsilon> (shift_modgrp m * f) = cis (pi * m / 12) * \<epsilon> f"
proof (cases "is_singular_modgrp f")
  case True
  have [simp]: "modgrp_c f \<noteq> 0"
    using True by (simp add: is_singular_modgrp_altdef)
  have a: "modgrp_a (shift_modgrp m * f) = modgrp_a f + m * modgrp_c f"
    unfolding shift_modgrp_code using modgrp.unimodular[of f] modgrp_c_nonneg[of f]
    by (subst (3) modgrp_abcd [symmetric], subst times_modgrp_code) (auto simp: modgrp_a_code algebra_simps)
  show ?thesis using True
    by (auto simp: dedekind_eps_def a add_divide_distrib ring_distribs simp flip: cis_mult cis_divide)
next
  case False
  then obtain n where [simp]: "f = shift_modgrp n"
    using not_singular_modgrpD by blast
  show ?thesis
    by simp
qed

lemma dedekind_eps_S_right:
  assumes "is_singular_modgrp f" "modgrp_d f \<noteq> 0"
  shows   "\<epsilon> (f * S_modgrp) = cis (-sgn (modgrp_d f) * pi / 4) * \<epsilon> f"
proof -
  note [simp del] = div_mult_self3 div_mult_self4 div_mult_self2 div_mult_self1
  define a b c d where "a = modgrp_a f" "b = modgrp_b f" "c = modgrp_c f" "d = modgrp_d f"
  have "c > 0"
    using assms modgrp_c_nonneg[of f] unfolding is_singular_modgrp_altdef a_b_c_d_def by auto
  from assms have [simp]: "d \<noteq> 0"
    by (auto simp: a_b_c_d_def)
  have "coprime c d"
    unfolding a_b_c_d_def by (intro coprime_modgrp_c_d)
  have det: "a * d - b * c = 1"
    unfolding a_b_c_d_def by (rule modgrp_abcd_det)
  hence det': "a * d = b * c + 1"
    by linarith

  have "pole_modgrp f \<noteq> (0 :: real)"
    using assms by transfer (auto simp: modgrp_rel_def split: if_splits)
  hence sing: "is_singular_modgrp (f * S_modgrp)"
    using assms by (auto simp: is_singular_modgrp_times_iff)

  show ?thesis
  proof (cases d "0 :: int" rule: linorder_cases)
    case greater
    have [simp]: "modgrp_a (f * S_modgrp) = b"
      using greater unfolding a_b_c_d_def by transfer auto
    have [simp]: "modgrp_b (f * S_modgrp) = -a"
      using greater unfolding a_b_c_d_def by transfer auto
    have [simp]: "modgrp_c (f * S_modgrp) = d"
      using greater unfolding a_b_c_d_def by transfer auto
    have [simp]: "modgrp_d (f * S_modgrp) = -c"
      using greater unfolding a_b_c_d_def by transfer (auto split: if_splits)

    have "dedekind_sum (-c) d = -dedekind_sum c d"
      using \<open>coprime c d\<close> by (simp add: dedekind_sum_negate)
    also have "\<dots> = dedekind_sum d c - c / d / 12 - d / c / 12 + 1 / 4 - 1 / (12 * c * d)"
      using \<open>c > 0\<close> \<open>d > 0\<close> \<open>coprime c d\<close> by (subst dedekind_sum_reciprocity') simp_all
    finally have *: "dedekind_sum (-c) d = \<dots>" .
    have [simp]: "cnj (cis (pi / 4)) = 1 / cis (pi / 4)"
      by (subst divide_conv_cnj) auto

    have "\<epsilon> (f * S_modgrp) = cis (pi * ((b - c) / (12 * d) + c / (12*d) +
                                   d / (12*c) + 1 / (12 * c * d) - dedekind_sum d c - 1 / 2))"
      unfolding dedekind_eps_def a_b_c_d_def [symmetric] using \<open>d > 0\<close> sing assms
      by (simp add: * algebra_simps)
    also have "(b - c) / (12 * d) + c / (12*d) + d / (12*c) + 1 / (12 * c * d) =
               (b * c + 1 + d * d) / (12 * c * d)"
      using \<open>c > 0\<close> \<open>d > 0\<close> by (simp add: field_simps)
    also have "b * c + 1 = a * d"
      using det by (simp add: algebra_simps)
    also have "(a * d + d * d) / (12 * c * d) = (a + d) / (12 * c)"
      using \<open>c > 0\<close> \<open>d > 0\<close> by (simp add: field_simps)
    also have "cis (pi * ((a + d) / (12 * c) - dedekind_sum d c - 1 / 2)) =
                cis (-pi / 4) * \<epsilon> f"
      unfolding dedekind_eps_def a_b_c_d_def [symmetric] using \<open>d > 0\<close> sing assms
      by (auto simp: cis_mult algebra_simps diff_divide_distrib add_divide_distrib)
    finally show ?thesis
      using \<open>d > 0\<close> by (simp add: a_b_c_d_def)

  next
    case less
    have [simp]: "modgrp_a (f * S_modgrp) = -b"
      using less unfolding a_b_c_d_def by transfer (auto split: if_splits)
    have [simp]: "modgrp_b (f * S_modgrp) = a"
      using less unfolding a_b_c_d_def by transfer (auto split: if_splits)
    have [simp]: "modgrp_c (f * S_modgrp) = -d"
      using less unfolding a_b_c_d_def by transfer (auto split: if_splits)
    have [simp]: "modgrp_d (f * S_modgrp) = c"
      using less unfolding a_b_c_d_def by transfer (auto split: if_splits)

    have "dedekind_sum c (-d) = 
            -dedekind_sum (-d) c - c / d / 12 - d / c / 12 - 1 / 4 - 1 / (12 * c * d)"
      using \<open>c > 0\<close> \<open>d < 0\<close> \<open>coprime c d\<close> by (subst dedekind_sum_reciprocity') simp_all
    also have "-dedekind_sum (-d) c = dedekind_sum d c"
      using \<open>coprime c d\<close> by (subst dedekind_sum_negate) (auto simp: Rings.coprime_commute)
    finally have *: "dedekind_sum c (-d) =
                      dedekind_sum d c - c / d / 12 - d / c / 12 - 1 / 4 - 1 / (12 * c * d)" .

    have "\<epsilon> (f * S_modgrp) =
            cis (pi * (c / (12 * d) + d / (12 * c) + 1 / (12 * c * d) - (c - b) / (12 * d) -
                       dedekind_sum d c))"
      unfolding dedekind_eps_def a_b_c_d_def [symmetric] using \<open>d < 0\<close> sing assms
      by (simp add: * algebra_simps)
    also have "c / (12 * d) + d / (12 * c) + 1 / (12 * c * d) - (c - b) / (12 * d) =
               (d * d + (1 + b * c)) / (12 * c * d)"
      using \<open>c > 0\<close> \<open>d < 0\<close> by (simp add: field_simps)
    also have "1 + b * c = a * d"
      using det by (simp add: algebra_simps)
    also have "(d * d + a * d) / (12 * c * d) = (a + d) / (12 * c)"
      using \<open>c > 0\<close> \<open>d < 0\<close> by (simp add: field_simps)
    also have "cis (pi * ((a + d) / (12 * c) - dedekind_sum d c)) = cis (pi / 4) * \<epsilon> f"
      unfolding dedekind_eps_def a_b_c_d_def [symmetric] using \<open>d < 0\<close> sing assms
      by (auto simp: cis_mult algebra_simps diff_divide_distrib add_divide_distrib)
    finally show ?thesis
      using \<open>d < 0\<close> by (simp add: a_b_c_d_def)
  qed auto
qed

lemma dedekind_eps_root_of_unity: "\<epsilon> f ^ 24 = 1"
proof -
  have not_sing: "\<epsilon> f ^ 24 = 1" if "\<not>is_singular_modgrp f" for f
  proof -
    have "\<epsilon> f ^ 24 = cis (2 * (pi * real_of_int (modgrp_b f)))"
      using that by (auto simp: dedekind_eps_def Complex.DeMoivre)
    also have "2 * (pi * real_of_int (modgrp_b f)) = 2 * pi * real_of_int (modgrp_b f)"
      by (simp add: mult_ac)
    also have "cis \<dots> = 1"
      by (rule cis_multiple_2pi) auto
    finally show ?thesis .
  qed

  show ?thesis
  proof (induction f rule: modgrp_induct_S_shift')
    case (S f)
    show ?case
    proof (cases "modgrp_d f = 0")
      case True
      hence "\<epsilon> (f * S_modgrp) ^ 24 = cis (real_of_int (modgrp_b (f * S_modgrp)) * (2 * pi))"
        by (simp add: dedekind_eps_def Complex.DeMoivre mult_ac)
      also have "\<dots> = 1"
        by (subst cis_power_int [symmetric]) auto
      finally show ?thesis
        by simp
    next
      case d: False
      show ?thesis
      proof (cases "is_singular_modgrp f")
        case sing: True
        have "\<epsilon> (f * S_modgrp) ^ 24 = cis (- (pi * (real_of_int (sgn (modgrp_d f)) * 6)))"
          using d sing by (simp add: dedekind_eps_S_right field_simps Complex.DeMoivre S)
        also have "- (pi * (real_of_int (sgn (modgrp_d f)) * 6)) = 2 * pi * of_int (-3 * sgn (modgrp_d f))"
          by simp
        also have "cis \<dots> = 1"
          by (rule cis_multiple_2pi) auto
        finally show ?thesis .
      next
        case False
        then obtain n where [simp]: "f = shift_modgrp n"
          using not_singular_modgrpD by blast
        have "\<epsilon> (f * S_modgrp) ^ 24 = cis (pi * (real_of_int n * 2) - pi * 6)"
          by (simp add: algebra_simps Complex.DeMoivre cis_mult)
        also have "pi * (real_of_int n * 2) - pi * 6 = (real_of_int (n-3) * (2 * pi))"
          by (simp add: algebra_simps)
        also have "cis \<dots> = 1"
          by (subst cis_power_int [symmetric]) auto
        finally show ?thesis .
      qed
    qed
  next
    case (shift f n)
    have "\<epsilon> (f * shift_modgrp n) ^ 24 = cis (of_int n * (2 * pi))"
      by (simp add: power_mult_distrib shift Complex.DeMoivre mult_ac)
    also have "\<dots> = 1"
      by (subst cis_power_int [symmetric]) auto
    finally show ?case .      
  qed auto
qed
      

text \<open>
  The following theorem is Apostol's Theorem~3.4: the general functional equation for
  Dedekind's $\eta$ function. 

  Our version is actually more general than Apostol's lemma since it also holds for modular groups
  with $c = 0$ (i.e.\ shifts, i.e.\ $T^n$). We also use a slightly different definition of \<open>\<epsilon>\<close> 
  though, namely the one from Wikipedia. This makes the functional equation look a bit nicer than
  Apostol's version.
\<close>
theorem dedekind_eta_apply_modgrp:
  assumes "Im z > 0"
  shows   "\<eta> (apply_modgrp f z) = \<epsilon> f * csqrt (modgrp_factor f z) * \<eta> z"
  using assms
proof (induction f arbitrary: z rule: modgrp_induct_S_shift')
  case id
  thus ?case by simp
next
  case (shift f n z)
  have "\<eta> (apply_modgrp (f * shift_modgrp n) z) = \<eta> (apply_modgrp f (z + of_int n))"
    using shift.prems by (subst apply_modgrp_mult) auto
  also have "\<dots> = \<epsilon> f * csqrt (modgrp_factor f (z + of_int n)) * \<eta> (z + of_int n)"
    using shift.prems by (subst shift.IH) auto
  also have "\<eta> (z + of_int n) = cis (pi * n / 12) * \<eta> z"
    using shift.prems by (subst dedekind_eta_plus_int) auto
  also have "\<epsilon> f * csqrt (modgrp_factor f (z + of_int n)) * (cis (pi * n / 12) * \<eta> z) =
             \<epsilon> (f * shift_modgrp n) * csqrt (modgrp_factor (f * shift_modgrp n) z) * \<eta> z"
    by simp
  finally show ?case .
next
  case (S f z)
  note [simp del] = div_mult_self3 div_mult_self4 div_mult_self2 div_mult_self1
  define a b c d where "a = modgrp_a f" "b = modgrp_b f" "c = modgrp_c f" "d = modgrp_d f"
  have det: "a * d - b * c = 1"
    using modgrp_abcd_det[of f] by (simp add: a_b_c_d_def)
  from S.prems have [simp]: "z \<noteq> 0"
    by auto
  show ?case
  proof (cases "is_singular_modgrp f")
    case False
    hence f: "f = shift_modgrp b"
      unfolding a_b_c_d_def by (rule not_singular_modgrpD)
    have *: "f * S_modgrp = modgrp b (-1) 1 0"
      unfolding f shift_modgrp_code S_modgrp_code times_modgrp_code by simp
    have [simp]: "modgrp_a (f * S_modgrp) = b"
                 "modgrp_b (f * S_modgrp) = -1"
                 "modgrp_c (f * S_modgrp) = 1"
                 "modgrp_d (f * S_modgrp) = 0"
      by (simp_all add: * modgrp_a_code modgrp_b_code modgrp_c_code modgrp_d_code)
    have eps: "\<epsilon> (f * S_modgrp) = cis (pi * (b / 12 - 1 / 4))"
      by (simp add: dedekind_eps_def dedekind_sum_def is_singular_modgrp_altdef)

    have "\<eta> (apply_modgrp (f * S_modgrp) z) = \<eta> (-1 / z + of_int b)"
      using S.prems by (subst apply_modgrp_mult) (auto simp: f algebra_simps)
    also have "\<dots> = cis (pi * b / 12) * \<eta> (-(1 / z))"
      using S.prems by (subst dedekind_eta_plus_int) auto
    also have "\<dots> = cis (pi * b / 12) * csqrt (- \<i> * z) * \<eta> z"
      using S.prems by (subst dedekind_eta_minus_one_over) auto
    also have "\<dots> = cis (pi / 4) * csqrt (- \<i> * z) * \<epsilon> (shift_modgrp b * S_modgrp) * \<eta> z"
      using eps by (auto simp: f ring_distribs simp flip: cis_divide)
    also have "csqrt (-\<i> * z) = rcis (norm (csqrt (-\<i> * z))) (Arg (csqrt (-\<i> * z)))"
      by (rule rcis_cmod_Arg [symmetric])
    also have "\<dots> = rcis (sqrt (cmod z)) (Arg (- (\<i> * z)) / 2)"
      by (simp add: norm_mult)
    also have "cis (pi / 4) * \<dots> = rcis (sqrt (norm z)) ((Arg (-\<i>*z) + pi / 2) / 2)"
      by (simp add: rcis_def cis_mult add_divide_distrib algebra_simps)
    also have "Arg (-\<i>*z) + pi / 2 = Arg z"
    proof (rule cis_Arg_unique [symmetric])
      have "cis (Arg (-\<i> * z) + pi / 2) = - (sgn (\<i> * z) * \<i>)"
        by (simp flip: cis_mult add: cis_Arg)
      also have "\<dots> = sgn z"
        by (simp add: complex_sgn_def scaleR_conv_of_real field_simps norm_mult)
      finally show "sgn z = cis (Arg (-\<i> * z) + pi / 2)" ..
    next
      show "-pi < Arg (-\<i> * z) + pi / 2" "Arg (- \<i> * z) + pi / 2 \<le> pi"
        using Arg_Re_pos[of "-\<i> * z"] S.prems by auto
    qed
    also have "rcis (sqrt (norm z)) (Arg z / 2) = rcis (norm (csqrt z)) (Arg (csqrt z))"
      by simp
    also have "\<dots> = csqrt z"
      by (rule rcis_cmod_Arg)
    finally show ?thesis
      by (simp add: f)
  next
    case sing: True
    hence "c > 0"
      unfolding a_b_c_d_def by (meson is_singular_modgrp_altdef modgrp_cd_signs)
    have "Im (1 / z) < 0"
      using S.prems Im_one_over_neg_iff by blast
    have Arg_z: "Arg z \<in> {0<..<pi}"
      using S.prems by (simp add: Arg_lt_pi)
    have Arg_z': "Arg (-\<i> * z) = -pi/2 + Arg z"
      using Arg_z by (subst Arg_times) auto
    have [simp]: "Arg (-z) = Arg z - pi"
      using Arg_z by (subst Arg_minus) auto

    show ?thesis
    proof (cases d "0 :: int" rule: linorder_cases)
      case equal
      hence *: "\<not>is_singular_modgrp (f * S_modgrp)"
        unfolding a_b_c_d_def
        by transfer (auto simp: modgrp_rel_def split: if_splits)
      define n where "n = modgrp_b (f * S_modgrp)"
      have **: "f * S_modgrp = shift_modgrp n"
        unfolding n_def using * by (rule not_singular_modgrpD)
      show ?thesis using S.prems
        by (simp add: ** dedekind_eta_plus_int)
    next
      case greater
      have "modgrp a b c d * S_modgrp = modgrp b (-a) d (-c)"
        unfolding shift_modgrp_code S_modgrp_code times_modgrp_code det by simp
      hence *: "f * S_modgrp = modgrp b (-a) d (-c)"
        by (simp add: a_b_c_d_def)
      have [simp]: "modgrp_a (f * S_modgrp) = b" "modgrp_b (f * S_modgrp) = -a"
                   "modgrp_c (f * S_modgrp) = d" "modgrp_d (f * S_modgrp) = -c"
        unfolding * modgrp_a_code modgrp_b_code modgrp_c_code modgrp_d_code
        using greater det by auto

      have "\<eta> (apply_modgrp (f * S_modgrp) z) = \<eta> (apply_modgrp f (- (1 / z)))"
        using S.prems by (subst apply_modgrp_mult) auto
      also have "\<dots> = \<epsilon> f * csqrt (modgrp_factor f (- (1 / z))) * \<eta> (- (1 / z))"
        using S.prems by (subst S.IH) auto
      also have "modgrp_factor f (- (1 / z)) = d - c / z"
        unfolding modgrp_factor_def by (simp add: a_b_c_d_def)
      also have "\<eta> (- (1 / z)) = csqrt (-\<i> * z) * \<eta> z"
        using S.prems by (subst dedekind_eta_minus_one_over) auto
      also have "\<epsilon> f * csqrt (d - c / z) * (csqrt (-\<i> * z) * \<eta> z) =
                 (csqrt (d - c / z) * csqrt (-\<i> * z)) * \<epsilon> f * \<eta> z"
        by (simp add: mult_ac)
      also have "csqrt (d - c / z) * csqrt (-\<i> * z) = csqrt ((d - c / z) * (-\<i> * z))"
      proof (rule csqrt_mult [symmetric])
        have "Im (of_int d - of_int c / z) = -of_int c * Im (1 / z)"
          by (simp add: Im_divide)
        hence Im: "Im (of_int d - of_int c / z) > 0"
          using \<open>Im (1 / z) < 0\<close> \<open>c > 0\<close> by (auto simp: mult_less_0_iff)
        hence Arg_pos: "Arg (of_int d - of_int c / z) > 0"
          using Arg_pos_iff by blast

        have "Arg (of_int d - of_int c / z) + Arg z \<le> 3 / 2 * pi"
        proof (cases "Re z \<ge> 0")
          case True
          have "Arg (of_int d - of_int c / z) \<le> pi"
            by (rule Arg_le_pi)
          moreover have "Arg z \<le> pi / 2"
            using Arg_Re_nonneg[of z] True by auto
          ultimately show ?thesis by simp
        next
          case False
          have "Re (of_int d - of_int c / z) = of_int d - of_int c * Re z / norm z ^ 2"
            by (simp add: Re_divide norm_complex_def)
          also have "\<dots> \<ge> 0 - 0"
            using \<open>d > 0\<close> \<open>c > 0\<close> False
            by (intro diff_mono divide_nonpos_pos mult_nonneg_nonpos) auto
          finally have "Arg (of_int d - of_int c / z) \<le> pi / 2"
            using Arg_Re_nonneg[of "of_int d - of_int c / z"] by simp
          moreover have "Arg z \<le> pi"
            by (rule Arg_le_pi)
          ultimately show ?thesis by simp
        qed
        moreover have "Arg (of_int d - of_int c / z) + Arg z > 0 + 0"
          using Arg_z by (intro add_strict_mono Arg_pos) auto
        ultimately show "Arg (of_int d - of_int c / z) + Arg (- \<i> * z) \<in> {-pi<..pi}"
          using Arg_z' by auto
      qed
      also have "(d - c / z) * (-\<i> * z) = (-\<i>) * (d * z - c)"
        using S.prems by (auto simp: field_simps)
      also have "csqrt \<dots> = csqrt (-\<i>) * csqrt (d * z - c)"
      proof (intro csqrt_mult)
        have "Arg (of_int d * z - of_int c) > 0"
          using \<open>d > 0\<close> S.prems by (subst Arg_pos_iff) auto
        moreover have "Arg (of_int d * z - of_int c) \<le> pi"
          by (rule Arg_le_pi)
        ultimately show "Arg (-\<i>) + Arg (of_int d * z - of_int c) \<in> {-pi<..pi}"
          by auto
      qed
      also have "csqrt (-\<i>) = cis (-pi / 4)"
        by (simp add: csqrt_exp_Ln cis_conv_exp)
      also have "cis (-pi / 4) * csqrt (d * z - c) * \<epsilon> f * \<eta> z =
                 \<epsilon> (f * S_modgrp) * csqrt (d * z - c) * \<eta> z"
        using \<open>d > 0\<close> sing by (subst dedekind_eps_S_right) (auto simp: a_b_c_d_def)
      also have "\<dots> = \<epsilon> (f * S_modgrp) * csqrt (modgrp_factor (f * S_modgrp) z) * \<eta> z"
        unfolding modgrp_factor_def by simp
      finally show ?thesis .
    next
      case less
      have "modgrp a b c d * S_modgrp = modgrp b (-a) d (-c)"
        unfolding shift_modgrp_code S_modgrp_code times_modgrp_code det by simp
      hence *: "f * S_modgrp = modgrp b (-a) d (-c)"
        by (simp add: a_b_c_d_def)
      have [simp]: "modgrp_a (f * S_modgrp) = -b" "modgrp_b (f * S_modgrp) = a"
                   "modgrp_c (f * S_modgrp) = -d" "modgrp_d (f * S_modgrp) = c"
        unfolding * modgrp_a_code modgrp_b_code modgrp_c_code modgrp_d_code
        using less det by auto

      have "\<eta> (apply_modgrp (f * S_modgrp) z) = \<eta> (apply_modgrp f (- (1 / z)))"
        using S.prems by (subst apply_modgrp_mult) auto
      also have "\<dots> = \<epsilon> f * csqrt (modgrp_factor f (- (1 / z))) * \<eta> (- (1 / z))"
        using S.prems by (subst S.IH) auto
      also have "modgrp_factor f (- (1 / z)) = d - c / z"
        unfolding modgrp_factor_def by (simp add: a_b_c_d_def)
      also have "\<eta> (- (1 / z)) = csqrt (-\<i> * z) * \<eta> z"
        using S.prems by (subst dedekind_eta_minus_one_over) auto
      also have "\<epsilon> f * csqrt (d - c / z) * (csqrt (-\<i> * z) * \<eta> z) =
                 (csqrt (d - c / z) * csqrt (-\<i> * z)) * \<epsilon> f * \<eta> z"
        by (simp add: mult_ac)
      also have "csqrt (-\<i> * z) = csqrt (\<i> * -z)"
        by simp
      also have "\<dots> = csqrt \<i> * csqrt (-z)"
      proof (rule csqrt_mult)
        show "Arg \<i> + Arg (- z) \<in> {- pi<..pi}"
          using Arg_z by auto
      qed
      also have "csqrt (d - c / z) * \<dots> = csqrt \<i> * (csqrt (d - c / z) * csqrt (-z))"
        by (simp add: mult_ac)
      also have "csqrt (d - c / z) * csqrt (-z) = csqrt ((d - c / z) * (-z))"
      proof (rule csqrt_mult [symmetric])
        have "Im (of_int d - of_int c / z) = of_int c * Im z / norm z ^ 2"
          by (simp add: Im_divide norm_complex_def)
        also have "\<dots> > 0"
          using S.prems \<open>c > 0\<close> by (intro mult_pos_pos divide_pos_pos) auto
        finally have "Arg (of_int d - of_int c / z) \<in> {0<..<pi}"
          using Arg_lt_pi[of "of_int d - of_int c / z"] by auto
        thus "Arg (of_int d - of_int c / z) + Arg (- z) \<in> {- pi<..pi}"
          using Arg_z by auto
      qed
      also have "(d - c / z) * (-z) = c - d * z"
        using S.prems by (simp add: field_simps)
      also have "csqrt \<i> = cis (pi / 4)"
        by (simp add: csqrt_exp_Ln complex_eq_iff cos_45 sin_45 field_simps)
      also have "cis (pi / 4) * csqrt (c - d * z) * \<epsilon> f * \<eta> z =
                 \<epsilon> (f * S_modgrp) * csqrt (c - d * z) * \<eta> z"
        using \<open>d < 0\<close> sing by (subst dedekind_eps_S_right) (auto simp: a_b_c_d_def)
      also have "\<dots> = \<epsilon> (f * S_modgrp) * csqrt (modgrp_factor (f * S_modgrp) z) * \<eta> z"
        unfolding modgrp_factor_def by simp
      finally show ?thesis .
    qed
  qed
qed

no_notation dedekind_eta ("\<eta>")
no_notation dedekind_eps ("\<epsilon>")

end
