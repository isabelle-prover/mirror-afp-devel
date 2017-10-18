(*
    File:      Dirichlet_Series_Analysis.thy
    Author:    Manuel Eberl, TU München
*)
section \<open>Analytic properties of Dirichlet series\<close>
theory Dirichlet_Series_Analysis
imports
  "HOL-Analysis.Analysis"
  "HOL-Library.Going_To_Filter"
  Dirichlet_Series
  Moebius_Mu
  Partial_Summation
  Euler_Products
begin

lemma multiplicative_function_divide_nat_power:
  fixes f :: "nat \<Rightarrow> 'a :: {nat_power, field}"
  assumes "multiplicative_function f"
  shows   "multiplicative_function (\<lambda>n. f n / nat_power n s)"
proof
  interpret f: multiplicative_function f by fact
  show "f 0 / nat_power 0 s = 0" "f 1 / nat_power 1 s = 1"
    by simp_all
  fix a b :: nat assume "a > 1" "b > 1" "coprime a b"
  thus "f (a * b) / nat_power (a * b) s = f a / nat_power a s * (f b / nat_power b s)"
    by (simp_all add: f.mult_coprime nat_power_mult_distrib)
qed

lemma completely_multiplicative_function_divide_nat_power:
  fixes f :: "nat \<Rightarrow> 'a :: {nat_power, field}"
  assumes "completely_multiplicative_function f"
  shows   "completely_multiplicative_function (\<lambda>n. f n / nat_power n s)"
proof
  interpret f: completely_multiplicative_function f by fact
  show "f 0 / nat_power 0 s = 0" "f (Suc 0) / nat_power (Suc 0) s = 1"
    by simp_all
  fix a b :: nat assume "a > 1" "b > 1"
  thus "f (a * b) / nat_power (a * b) s = f a / nat_power a s * (f b / nat_power b s)"
    by (simp_all add: f.mult nat_power_mult_distrib)
qed

subsection \<open>Convergence of the $\zeta$ and M\"{o}bius $\mu$ series\<close>

lemma fds_abs_summable_zeta_real_iff [simp]:
  "fds_abs_converges fds_zeta s \<longleftrightarrow> s > (1 :: real)"
proof -
  have "fds_abs_converges fds_zeta s \<longleftrightarrow> summable (\<lambda>n. real n powr -s)"
    unfolding fds_abs_converges_def
    by (intro summable_cong always_eventually)
       (auto simp: fds_nth_zeta powr_minus divide_simps)
  also have "\<dots> \<longleftrightarrow> s > 1" by (simp add: summable_real_powr_iff)
  finally show ?thesis .
qed

lemma fds_abs_summable_zeta_real: "s > (1 :: real) \<Longrightarrow> fds_abs_converges fds_zeta s"
  by simp

lemma fds_abs_converges_moebius_mu_real: 
  assumes "s > (1 :: real)"
  shows   "fds_abs_converges (fds moebius_mu) s"
  unfolding fds_abs_converges_def
proof (rule summable_comparison_test, intro exI allI impI)
  fix n :: nat
  show "norm (norm (fds_nth (fds moebius_mu) n / nat_power n s)) \<le> n powr (-s)"
    by (simp add: powr_minus divide_simps abs_moebius_mu_le)
next
  from assms show "summable (\<lambda>n. real n powr -s)" by (simp add: summable_real_powr_iff)
qed


subsection \<open>Convergence and absolute convergence\<close>

class nat_power_normed_field = nat_power_field + real_normed_field + real_inner + real_algebra_1 +
  fixes real_power :: "real \<Rightarrow> 'a \<Rightarrow> 'a"
  assumes real_power_nat_power: "n > 0 \<Longrightarrow> real_power (real n) c = nat_power n c"
  assumes real_power_1_right_aux: "d > 0 \<Longrightarrow> real_power d 1 = d *\<^sub>R 1"
  assumes real_power_add: "d > 0 \<Longrightarrow> real_power d (a + b) = real_power d a * real_power d b"
  assumes real_power_nonzero [simp]: "d > 0 \<Longrightarrow> real_power d a \<noteq> 0"
  assumes norm_real_power: "x > 0 \<Longrightarrow> norm (real_power x c) = x powr (c \<bullet> 1)"
  assumes has_field_derivative_nat_power_aux:
            "\<And>x::'a. n > 0 \<Longrightarrow> filterlim (\<lambda>y. (nat_power n y - nat_power n x -
               ln (real n) *\<^sub>R nat_power n x * (y - x)) /\<^sub>R norm (y - x)) 
             (INFIMUM {S. open S \<and> 0 \<in> S} principal) 
             (inf_class.inf (INFIMUM {S. open S \<and> x \<in> S} principal) (principal (UNIV - {x})))"
  assumes has_vector_derivative_real_power_aux:
            "x > 0 \<Longrightarrow> filterlim (\<lambda>y. (real_power y c - real_power x (c :: 'a) -
               (y - x) *\<^sub>R (c * real_power x (c - 1))) /\<^sub>R
               norm (y - x)) (INF S:{S. open S \<and> 0 \<in> S}. principal S) (at x)"
  assumes norm_nat_power: "n > 0 \<Longrightarrow> norm (nat_power n y) = real n powr (y \<bullet> 1)"
begin
 
lemma real_power_diff: "d > 0 \<Longrightarrow> real_power d (a - b) = real_power d a / real_power d b"
  using real_power_add[of d b "a - b"] by (simp add: field_simps)

end

lemma real_power_1_right [simp]: "d > 0 \<Longrightarrow> real_power d 1 = of_real d"
  using real_power_1_right_aux[of d] by (simp add: scaleR_conv_of_real)


lemma has_vector_derivative_real_power [derivative_intros]:
  "x > 0 \<Longrightarrow> ((\<lambda>y. real_power y c) has_vector_derivative c * real_power x (c - 1)) (at x within A)"
  by (rule has_vector_derivative_at_within)
     (insert has_vector_derivative_real_power_aux[of x c],
      simp add: has_vector_derivative_def has_derivative_def netlimit_at 
                nhds_def bounded_linear_scaleR_left)
              
lemma has_field_derivative_nat_power [derivative_intros]:
  "n > 0 \<Longrightarrow> ((\<lambda>y. nat_power n y) has_field_derivative ln (real n) *\<^sub>R nat_power n x)
     (at (x :: 'a :: nat_power_normed_field) within A)"
  by (rule has_field_derivative_at_within)
     (insert has_field_derivative_nat_power_aux[of n x],
      simp only: has_field_derivative_def has_derivative_def netlimit_at,
      simp add: nhds_def at_within_def bounded_linear_mult_right)
              
lemma continuous_on_real_power [continuous_intros]: 
  "A \<subseteq> {0<..} \<Longrightarrow> continuous_on A (\<lambda>x. real_power x s)"
  by (rule continuous_on_vector_derivative has_vector_derivative_real_power)+ auto

instantiation real :: nat_power_normed_field
begin

definition real_power_real :: "real \<Rightarrow> real \<Rightarrow> real" where
  [simp]: "real_power_real = op powr"
  
instance proof (standard, goal_cases)
  case (6 n x)
  hence "((\<lambda>x. nat_power n x) has_field_derivative ln (real n) *\<^sub>R nat_power n x) (at x)"
    by (auto intro!: derivative_eq_intros simp: powr_def)
  thus ?case unfolding has_field_derivative_def netlimit_at has_derivative_def
    by (simp add: nhds_def at_within_def)
next
  case (7 x c)
  hence "((\<lambda>y. real_power y c) has_vector_derivative c * real_power x (c - 1)) (at x)"
    by (auto intro!: derivative_eq_intros
             simp: has_field_derivative_iff_has_vector_derivative [symmetric])
  thus ?case by (simp add: has_vector_derivative_def has_derivative_def netlimit_at nhds_def)
qed (simp_all add: powr_add)

end


instantiation complex :: nat_power_normed_field
begin
  
definition nat_power_complex :: "nat \<Rightarrow> complex \<Rightarrow> complex" where
   [simp]: "nat_power_complex n z = of_nat n powr z"

definition real_power_complex :: "real \<Rightarrow> complex \<Rightarrow> complex" where
  [simp]: "real_power_complex = (\<lambda>x y. of_real x powr y)"
  
instance proof
  fix m n :: nat and z :: complex
  assume "m > 0" "n > 0"
  thus "nat_power (m * n) z = nat_power m z * nat_power n z"
    unfolding nat_power_complex_def of_nat_mult by (subst powr_times_real) simp_all
next
  fix n :: nat and z :: complex
  assume "n > 0"
  show "norm (nat_power n z) = real n powr (z \<bullet> 1)" unfolding nat_power_complex_def
    using norm_powr_real_powr[of "of_nat n" z] by simp
next
  fix n :: nat and x :: complex assume n: "n > 0"
  hence "((\<lambda>x. nat_power n x) has_field_derivative ln (real n) *\<^sub>R nat_power n x) (at x)"
    by (auto intro!: derivative_eq_intros simp: powr_def scaleR_conv_of_real mult_ac Ln_of_nat)
  thus "LIM y inf_class.inf (INFIMUM {S. open S \<and> x \<in> S} principal) (principal (UNIV - {x})).
           (nat_power n y - nat_power n x - ln (real n) *\<^sub>R nat_power n x * (y - x)) /\<^sub>R
           cmod (y - x) :> INFIMUM {S. open S \<and> 0 \<in> S} principal"
    unfolding has_field_derivative_def netlimit_at has_derivative_def
    by (simp add: nhds_def at_within_def)
next
  fix x :: real and c :: complex assume "x > 0"
  hence "((\<lambda>y. real_power y c) has_vector_derivative c * real_power x (c - 1)) (at x)"
    by (auto intro!: derivative_eq_intros has_vector_derivative_real_complex)
  thus "LIM y at x. (real_power y c - real_power x c - (y - x) *\<^sub>R (c * real_power x (c - 1))) /\<^sub>R
           norm (y - x) :> INF S:{S. open S \<and> 0 \<in> S}. principal S"
    by (simp add: has_vector_derivative_def has_derivative_def netlimit_at nhds_def)
qed (auto simp: powr_def exp_add exp_of_nat_mult [symmetric] algebra_simps scaleR_conv_of_real 
          simp del: Ln_of_nat)

end

lemma fds_abs_summable_zeta_iff [simp]:
  fixes s :: "'a :: {banach, nat_power_normed_field}"
  shows "fds_abs_converges fds_zeta s \<longleftrightarrow> s \<bullet> 1 > (1 :: real)"
proof -
  have "fds_abs_converges fds_zeta s \<longleftrightarrow> summable (\<lambda>n. real n powr -(s \<bullet> 1))"
    unfolding fds_abs_converges_def
    by (intro summable_cong always_eventually)
       (auto simp: norm_divide fds_nth_zeta powr_minus norm_nat_power divide_simps)
  also have "\<dots> \<longleftrightarrow> s \<bullet> 1 > 1" by (simp add: summable_real_powr_iff)
  finally show ?thesis .
qed

lemma fds_abs_summable_zeta: 
  "(s :: 'a :: {banach, nat_power_normed_field}) \<bullet> 1 > 1 \<Longrightarrow> fds_abs_converges fds_zeta s"
  by simp


lemma fds_abs_converges_moebius_mu:
  fixes s :: "'a :: {banach,nat_power_normed_field}"
  assumes "s \<bullet> 1 > 1"
  shows   "fds_abs_converges (fds moebius_mu) s"
  unfolding fds_abs_converges_def
proof (rule summable_comparison_test, intro exI allI impI)
  fix n :: nat
  show "norm (norm (fds_nth (fds moebius_mu) n / nat_power n s)) \<le> real n powr (-s \<bullet> 1)"
    by (auto simp: powr_minus divide_simps abs_moebius_mu_le norm_nat_power norm_divide
                   moebius_mu_def norm_power)
next
  from assms show "summable (\<lambda>n. real n powr (-s \<bullet> 1))" by (simp add: summable_real_powr_iff)
qed


definition conv_abscissa
    :: "'a :: {nat_power,banach,real_normed_field, real_inner} fds \<Rightarrow> ereal" where
  "conv_abscissa f = (INF s:{s. fds_converges f s}. ereal (s \<bullet> 1))"

definition abs_conv_abscissa
    :: "'a :: {nat_power,banach,real_normed_field, real_inner} fds \<Rightarrow> ereal" where
  "abs_conv_abscissa f = (INF s:{s. fds_abs_converges f s}. ereal (s \<bullet> 1))"


class dirichlet_series = euclidean_space + real_normed_field + nat_power_normed_field +
  assumes one_in_Basis: "1 \<in> Basis"
    
instance real :: dirichlet_series by standard simp_all
instance complex :: dirichlet_series by standard (simp_all add: Basis_complex_def)

context
  assumes "SORT_CONSTRAINT('a :: dirichlet_series)"
begin

lemma fds_abs_converges_Re_le:
  fixes f :: "'a fds"
  assumes "fds_abs_converges f z" "z \<bullet> 1 \<le> z' \<bullet> 1"
  shows   "fds_abs_converges f z'"
  unfolding fds_abs_converges_def
proof (rule summable_comparison_test, intro exI allI impI)
  fix n :: nat assume n: "n \<ge> 1"
  thus "norm (norm (fds_nth f n / nat_power n z')) \<le> norm (fds_nth f n / nat_power n z)"
    using assms(2) by (simp add: norm_divide norm_nat_power divide_simps powr_mono mult_left_mono)
qed (insert assms(1), simp add: fds_abs_converges_def)

lemma fds_abs_converges:
  assumes "s \<bullet> 1 > abs_conv_abscissa (f :: 'a fds)"
  shows   "fds_abs_converges f s"
proof -
  from assms obtain s0 where "fds_abs_converges f s0" "s0 \<bullet> 1 < s \<bullet> 1"
    by (auto simp: INF_less_iff abs_conv_abscissa_def)
  with fds_abs_converges_Re_le[OF this(1), of s] this(2) show ?thesis by simp
qed

lemma fds_abs_diverges:
  assumes "s \<bullet> 1 < abs_conv_abscissa (f :: 'a fds)"
  shows   "\<not>fds_abs_converges f s"
proof
  assume "fds_abs_converges f s"
  hence "abs_conv_abscissa f \<le> s \<bullet> 1" unfolding abs_conv_abscissa_def
    by (intro INF_lower) auto
  with assms show False by simp
qed


lemma uniformly_Cauchy_eval_fds_aux:
  assumes conv: "fds_converges f (s0 :: 'a)"
  assumes B: "compact B" "\<And>z. z \<in> B \<Longrightarrow> z \<bullet> 1 > s0 \<bullet> 1"
  shows   "uniformly_Cauchy_on B (\<lambda>N z. \<Sum>n\<le>N. fds_nth f n / nat_power n z)"
proof (cases "B = {}")
  case False
  show ?thesis
  proof (rule uniformly_Cauchy_onI', goal_cases)
    case (1 \<epsilon>)
    define \<sigma> where "\<sigma> = Inf ((\<lambda>s. s \<bullet> 1) ` B)"
    have \<sigma>_le: "s \<bullet> 1 \<ge> \<sigma>" if "s \<in> B" for s
      unfolding \<sigma>_def using that 
      by (intro cInf_lower bounded_inner_imp_bdd_below compact_imp_bounded B) auto
    have "\<sigma> \<in> ((\<lambda>s. s \<bullet> 1) ` B)"
      unfolding \<sigma>_def using B \<open>B \<noteq> {}\<close>
      by (intro closed_contains_Inf bounded_inner_imp_bdd_below compact_imp_bounded B 
            compact_imp_closed compact_continuous_image continuous_intros) auto
    with B(2) have \<sigma>_gt: "\<sigma> > s0 \<bullet> 1" by auto
    define \<delta> where "\<delta> = \<sigma> - s0 \<bullet> 1"
      
    have "bounded B" by (rule compact_imp_bounded) fact
    then obtain norm_B_aux where norm_B_aux: "\<And>s. s \<in> B \<Longrightarrow> norm s \<le> norm_B_aux" 
      by (auto simp: bounded_iff)
    define norm_B where "norm_B = norm_B_aux + norm s0"
    from norm_B_aux have norm_B: "norm (s - s0) \<le> norm_B" if "s \<in> B" for s
      using norm_triangle_ineq4[of s s0] norm_B_aux[OF that] by (simp add: norm_B_def)
      
    define A where "A = sum_upto (\<lambda>k. fds_nth f k / nat_power k s0)"
    from conv have "convergent (\<lambda>n. \<Sum>k\<le>n. fds_nth f k / nat_power k s0)"
      by (simp add: fds_converges_def summable_iff_convergent')
    hence "Bseq (\<lambda>n. \<Sum>k\<le>n. fds_nth f k / nat_power k s0)" by (rule convergent_imp_Bseq)
    then obtain C_aux where C_aux: "\<And>n. norm (\<Sum>k\<le>n. fds_nth f k / nat_power k s0) \<le> C_aux"
      by (auto simp: Bseq_def)
    define C where "C = max C_aux 1"
    have C_pos: "C > 0" by (simp add: C_def)
    have C: "norm (A x) \<le> C" for x
    proof -
      have "A x = (\<Sum>k\<le>nat \<lfloor>x\<rfloor>. fds_nth f k / nat_power k s0)"
        unfolding A_def sum_upto_altdef by (intro sum.mono_neutral_left) auto
      also have "norm \<dots> \<le> C_aux" by (rule C_aux)
      also have "\<dots> \<le> C" by (simp add: C_def)
      finally show ?thesis .
    qed
    
    have "(\<lambda>m. 2 * C * (1 + norm_B / \<delta>) * real m powr (-\<delta>)) \<longlonglongrightarrow> 0" unfolding \<delta>_def using \<sigma>_gt
      by (intro tendsto_mult_right_zero tendsto_neg_powr filterlim_real_sequentially) simp_all
    from order_tendstoD(2)[OF this \<open>\<epsilon> > 0\<close>] obtain M where
      M: "\<And>m. m \<ge> M \<Longrightarrow> 2 * C * (1 + norm_B / \<delta>) * real m powr - \<delta> < \<epsilon>" 
      by (auto simp: eventually_at_top_linorder)
      
    show ?case
    proof (intro exI[of _ "max M 1"] ballI allI impI, goal_cases)
      case (1 s m n)
      from 1 have s: "s \<bullet> 1 > s0 \<bullet> 1" using B(2)[of s] by simp
      have mn: "m \<ge> M" "m < n" "m > 0" "n > 0" using 1 by (simp_all add: )
      have "dist (\<Sum>n\<le>m. fds_nth f n / nat_power n s) (\<Sum>n\<le>n. fds_nth f n / nat_power n s) =
              dist (\<Sum>n\<le>n. fds_nth f n / nat_power n s) (\<Sum>n\<le>m. fds_nth f n / nat_power n s)"
        by (simp add: dist_commute)
      also from 1 have "\<dots> = norm (\<Sum>k\<in>{..n}-{..m}. fds_nth f k / nat_power k s)"
        by (subst sum_diff) (simp_all add: dist_norm sum_diff)
      also from 1 have "{..n} - {..m} = real -` {real m<..real n}" by auto
      also have "(\<Sum>k\<in>\<dots>. fds_nth f k / nat_power k s) = 
                   (\<Sum>k\<in>\<dots>. fds_nth f k / nat_power k s0 * real_power (real k) (s0 - s))"
        (is "_ = ?S") by (intro sum.cong refl) (simp_all add: nat_power_diff real_power_nat_power)
      also have *: "((\<lambda>t. A t * ((s0 - s) * real_power t (s0 - s - 1))) has_integral
                    (A (real n) * real_power n (s0 - s) - A (real m) * real_power m (s0 - s) - ?S))
                    {real m..real n}" (is "(?h has_integral _) _") unfolding A_def using mn
        by (intro partial_summation_strong[of "{}"]) 
           (auto intro!: derivative_eq_intros continuous_intros)
      hence "?S = A (real n) * nat_power n (s0 - s) - A (real m) * nat_power m (s0 - s) -
                    integral {real m..real n} ?h"
        using mn by (simp add: has_integral_iff real_power_nat_power)
      also have "norm \<dots> \<le> norm (A (real n) * nat_power n (s0 - s)) +
                    norm (A (real m) * nat_power m (s0 - s)) + norm (integral {real m..real n} ?h)"
        by (intro order.trans[OF norm_triangle_ineq4] add_right_mono order.refl)
      also have "norm (A (real n) * nat_power n (s0 - s)) \<le> C * nat_power m ((s0 - s) \<bullet> 1)"
        using mn \<open>s \<in> B\<close> C_pos s
        by (auto simp: norm_mult norm_nat_power algebra_simps intro!: mult_mono C powr_mono2')
      also have "norm (A (real m) * nat_power m (s0 - s)) \<le> C * nat_power m ((s0 - s) \<bullet> 1)"
        using mn by (auto simp: norm_mult norm_nat_power intro!: mult_mono C)
      also have "norm (integral {real m..real n} ?h) \<le> 
                   integral {real m..real n} (\<lambda>t. C * (norm (s0 - s) * t powr ((s0 - s) \<bullet> 1 - 1)))"
      proof (intro integral_norm_bound_integral ballI, goal_cases)
        case 1
        with * show ?case by (simp add: has_integral_iff)
      next
        case 2
        from mn show ?case by (auto intro!: integrable_continuous_real continuous_intros)
      next
        case (3 t)
        thus ?case unfolding norm_mult using C_pos mn 
          by (intro mult_mono C) (auto simp: norm_real_power dot_square_norm algebra_simps)
      qed
      also have "\<dots> = C * norm (s0 - s) * integral {real m..real n} (\<lambda>t. t powr ((s0 - s) \<bullet> 1 - 1))"
        by (simp add: algebra_simps dot_square_norm)
      also {
        have "((\<lambda>t. t powr ((s0 - s) \<bullet> 1 - 1)) has_integral 
                     (real n powr ((s0 - s) \<bullet> 1) / ((s0 - s) \<bullet> 1) - 
                      real m powr ((s0 - s) \<bullet> 1) / ((s0 - s) \<bullet> 1))) {m..n}" 
          (is "(?l has_integral ?I) _") using mn s
          by (intro fundamental_theorem_of_calculus)
             (auto intro!: derivative_eq_intros 
                   simp: has_field_derivative_iff_has_vector_derivative [symmetric] inner_diff_left)
        hence "integral {real m..real n} ?l = ?I" by (simp add: has_integral_iff)
        also have "\<dots> \<le> -(real m powr ((s0 - s) \<bullet> 1) / ((s0 - s) \<bullet> 1))" using s mn
          by (simp add: divide_simps inner_diff_left)
        also have "\<dots> = 1 * (real m powr ((s0 - s) \<bullet> 1) / ((s - s0) \<bullet> 1))"
          using s by (simp add: field_simps inner_diff_left)
        also have "\<dots> \<le> 2 * (real m powr ((s0 - s) \<bullet> 1) / ((s - s0) \<bullet> 1))" using mn s
          by (intro mult_right_mono divide_nonneg_pos) (simp_all add: inner_diff_left)
        finally have "integral {m..n} ?l \<le> \<dots>" .
      }
      hence "C * norm (s0 - s) * integral {real m..real n} (\<lambda>t. t powr ((s0 - s) \<bullet> 1 - 1)) \<le>
               C * norm (s0 - s) * (2 * (real m powr ((s0 - s) \<bullet> 1) / ((s - s0) \<bullet> 1)))" 
        using C_pos mn
        by (intro mult_mono mult_nonneg_nonneg integral_nonneg
              integrable_continuous_real continuous_intros) auto
      also have "C * nat_power m ((s0 - s) \<bullet> 1) + C * nat_power m ((s0 - s) \<bullet> 1) + \<dots> =
                   2 * C * nat_power m ((s0 - s) \<bullet> 1) * (1 + norm (s - s0) / ((s - s0) \<bullet> 1))"
        by (simp add: algebra_simps norm_minus_commute)
      also have "\<dots> \<le> 2 * C * nat_power m (-\<delta>) * (1 + norm_B / \<delta>)" 
        using C_pos s mn \<sigma>_le[of s] \<open>s \<in> B\<close> \<sigma>_gt unfolding nat_power_real_def
        by (intro mult_mono mult_nonneg_nonneg powr_mono frac_le add_mono norm_B)
           (simp_all add: inner_diff_left \<delta>_def)
      also have "\<dots> = 2 * C * (1 + norm_B / \<delta>) * real m powr (-\<delta>)" by simp
      also from \<open>m \<ge> M\<close> have "\<dots> < \<epsilon>" by (rule M)
      finally show ?case by - simp_all
    qed
  qed
qed (auto simp: uniformly_Cauchy_on_def)
  
lemma uniformly_convergent_eval_fds_aux:
  assumes conv: "fds_converges f (s0 :: 'a)"
  assumes B: "compact B" "\<And>z. z \<in> B \<Longrightarrow> z \<bullet> 1 > s0 \<bullet> 1"
  shows   "uniformly_convergent_on B (\<lambda>N z. \<Sum>n\<le>N. fds_nth f n / nat_power n z)"
  by (rule Cauchy_uniformly_convergent uniformly_Cauchy_eval_fds_aux assms)+

theorem fds_converges_Re_le:
  assumes "fds_converges f (s0 :: 'a)" "s \<bullet> 1 > s0 \<bullet> 1"
  shows   "fds_converges f s"
proof -
  have "uniformly_convergent_on {s} (\<lambda>N z. \<Sum>n\<le>N. fds_nth f n / nat_power n z)"
    by (rule uniformly_convergent_eval_fds_aux assms)+ (insert assms(2), auto)
  then obtain l where "uniform_limit {s} (\<lambda>N z. \<Sum>n\<le>N. fds_nth f n / nat_power n z) l at_top"
    by (auto simp: uniformly_convergent_on_def)
  from tendsto_uniform_limitI[OF this, of s]
  have "(\<lambda>n. fds_nth f n / nat_power n s) sums l s" unfolding sums_def'
    by (simp add: atLeast0AtMost)
  thus ?thesis by (simp add: fds_converges_def sums_iff)
qed

lemma fds_converges:
  assumes "s \<bullet> 1 > conv_abscissa (f :: 'a fds)"
  shows   "fds_converges f s"
proof -
  from assms obtain s0 where "fds_converges f s0" "s0 \<bullet> 1 < s \<bullet> 1"
    by (auto simp: INF_less_iff conv_abscissa_def)
  with fds_converges_Re_le[OF this(1), of s] this(2) show ?thesis by simp
qed

lemma fds_diverges:
  assumes "s \<bullet> 1 < conv_abscissa (f :: 'a fds)"
  shows   "\<not>fds_converges f s"
proof
  assume "fds_converges f s"
  hence "conv_abscissa f \<le> s \<bullet> 1" unfolding conv_abscissa_def
    by (intro INF_lower) auto
  with assms show False by simp
qed

theorem fds_converges_imp_abs_converges:
  assumes "fds_converges (f :: 'a fds) s" "s' \<bullet> 1 > s \<bullet> 1 + 1"
  shows   "fds_abs_converges f s'"
  unfolding fds_abs_converges_def
proof (rule summable_comparison_test_ev)
  from assms(2) show "summable (\<lambda>n. real n powr ((s - s') \<bullet> 1))"
    by (subst summable_real_powr_iff) (simp_all add: inner_diff_left)
next
  from assms(1) have "(\<lambda>n. fds_nth f n / nat_power n s) \<longlonglongrightarrow> 0"
    unfolding fds_converges_def by (rule summable_LIMSEQ_zero)
  from tendsto_norm[OF this] have "(\<lambda>n. norm (fds_nth f n / nat_power n s)) \<longlonglongrightarrow> 0" by simp
  hence "eventually (\<lambda>n. norm (fds_nth f n / nat_power n s) < 1) at_top"
    by (rule order_tendstoD) simp_all
  thus "eventually (\<lambda>n. norm (norm (fds_nth f n / nat_power n s')) \<le> 
          real n powr ((s - s') \<bullet> 1)) at_top"
  proof eventually_elim
    case (elim n)
    thus ?case
    proof (cases "n = 0")
      case False
      have "norm (fds_nth f n / nat_power n s') =
              norm (fds_nth f n) / real n powr (s' \<bullet> 1)" using False
        by (simp add: norm_divide norm_nat_power)
      also have "\<dots> = norm (fds_nth f n / nat_power n s) / real n powr ((s' - s) \<bullet> 1)" using False
        by (simp add: norm_divide norm_nat_power inner_diff_left powr_diff)
      also have "\<dots> \<le> 1 / real n powr ((s' - s) \<bullet> 1)" using elim
        by (intro divide_right_mono elim) simp_all
      also have "\<dots> = real n powr ((s - s') \<bullet> 1)" using False
        by (simp add: field_simps inner_diff_left powr_diff) 
      finally show ?thesis by simp
    qed simp_all
  qed
qed

lemma conv_le_abs_conv_abscissa: "conv_abscissa f \<le> abs_conv_abscissa f"
  unfolding conv_abscissa_def abs_conv_abscissa_def
  by (intro INF_superset_mono) auto

lemma conv_abscissa_PInf_iff: "conv_abscissa f = \<infinity> \<longleftrightarrow> (\<forall>s. \<not>fds_converges f s)"
  unfolding conv_abscissa_def by (subst Inf_eq_PInfty) auto

lemma conv_abscissa_PInfI [intro]: "(\<And>s. \<not>fds_converges f s) \<Longrightarrow> conv_abscissa f = \<infinity>"
  by (subst conv_abscissa_PInf_iff) auto
    
lemma conv_abscissa_MInf_iff: "conv_abscissa (f :: 'a fds) = -\<infinity> \<longleftrightarrow> (\<forall>s. fds_converges f s)"
proof safe
  assume *: "\<forall>s. fds_converges f s"
  have "conv_abscissa f \<le> B" for B :: real
    using spec[OF *, of "of_real B"] fds_diverges[of "of_real B" f]
    by (cases "conv_abscissa f \<le> B") simp_all
  thus "conv_abscissa f = -\<infinity>" by (rule ereal_bot)    
qed (auto intro: fds_converges)

lemma conv_abscissa_MInfI [intro]: "(\<And>s. fds_converges (f::'a fds) s) \<Longrightarrow> conv_abscissa f = -\<infinity>"
  by (subst conv_abscissa_MInf_iff) auto

lemma abs_conv_abscissa_PInf_iff: "abs_conv_abscissa f = \<infinity> \<longleftrightarrow> (\<forall>s. \<not>fds_abs_converges f s)"
  unfolding abs_conv_abscissa_def by (subst Inf_eq_PInfty) auto

lemma abs_conv_abscissa_PInfI [intro]: "(\<And>s. \<not>fds_converges f s) \<Longrightarrow> abs_conv_abscissa f = \<infinity>"
  by (subst abs_conv_abscissa_PInf_iff) auto

lemma abs_conv_abscissa_MInf_iff: 
  "abs_conv_abscissa (f :: 'a fds) = -\<infinity> \<longleftrightarrow> (\<forall>s. fds_abs_converges f s)"
proof safe
  assume *: "\<forall>s. fds_abs_converges f s"
  have "abs_conv_abscissa f \<le> B" for B :: real
    using spec[OF *, of "of_real B"] fds_abs_diverges[of "of_real B" f]
    by (cases "abs_conv_abscissa f \<le> B") simp_all
  thus "abs_conv_abscissa f = -\<infinity>" by (rule ereal_bot)    
qed (auto intro: fds_abs_converges)

lemma abs_conv_abscissa_MInfI [intro]: 
  "(\<And>s. fds_abs_converges (f::'a fds) s) \<Longrightarrow> abs_conv_abscissa f = -\<infinity>"
  by (subst abs_conv_abscissa_MInf_iff) auto

lemma conv_abscissa_geI:
  assumes "\<And>c'. ereal c' < c \<Longrightarrow> \<exists>s. s \<bullet> 1 = c' \<and> \<not>fds_converges f s"
  shows   "conv_abscissa (f :: 'a fds) \<ge> c"
proof (rule ccontr)
  assume "\<not>conv_abscissa f \<ge> c"
  hence "c > conv_abscissa f" by simp
  from ereal_dense2[OF this] obtain c' where "c > ereal c'" "c' > conv_abscissa f" by auto
  moreover from assms[OF this(1)] obtain s where "s \<bullet> 1 = c'" "\<not>fds_converges f s" by blast
  ultimately show False using fds_converges[of f s] by auto
qed

lemma conv_abscissa_leI:
  assumes "\<And>c'. ereal c' > c \<Longrightarrow> \<exists>s. s \<bullet> 1 = c' \<and> fds_converges f s"
  shows   "conv_abscissa (f :: 'a fds) \<le> c"
proof (rule ccontr)
  assume "\<not>conv_abscissa f \<le> c"
  hence "c < conv_abscissa f" by simp
  from ereal_dense2[OF this] obtain c' where "c < ereal c'" "c' < conv_abscissa f" by auto
  moreover from assms[OF this(1)] obtain s where "s \<bullet> 1 = c'" "fds_converges f s" by blast
  ultimately show False using fds_diverges[of s f] by auto
qed

lemma abs_conv_abscissa_geI:
  assumes "\<And>c'. ereal c' < c \<Longrightarrow> \<exists>s. s \<bullet> 1 = c' \<and> \<not>fds_abs_converges f s"
  shows   "abs_conv_abscissa (f :: 'a fds) \<ge> c"
proof (rule ccontr)
  assume "\<not>abs_conv_abscissa f \<ge> c"
  hence "c > abs_conv_abscissa f" by simp
  from ereal_dense2[OF this] obtain c' where "c > ereal c'" "c' > abs_conv_abscissa f" by auto
  moreover from assms[OF this(1)] obtain s where "s \<bullet> 1 = c'" "\<not>fds_abs_converges f s" by blast
  ultimately show False using fds_abs_converges[of f s] by auto
qed  

lemma abs_conv_abscissa_leI:
  assumes "\<And>c'. ereal c' > c \<Longrightarrow> \<exists>s. s \<bullet> 1 = c' \<and> fds_abs_converges f s"
  shows   "abs_conv_abscissa (f :: 'a fds) \<le> c"
proof (rule ccontr)
  assume "\<not>abs_conv_abscissa f \<le> c"
  hence "c < abs_conv_abscissa f" by simp
  from ereal_dense2[OF this] obtain c' where "c < ereal c'" "c' < abs_conv_abscissa f" by auto
  moreover from assms[OF this(1)] obtain s where "s \<bullet> 1 = c'" "fds_abs_converges f s" by blast
  ultimately show False using fds_abs_diverges[of s f] by auto
qed

  
theorem abs_conv_le_conv_abscissa_plus_1: "abs_conv_abscissa (f :: 'a fds) \<le> conv_abscissa f + 1"
proof (rule abs_conv_abscissa_leI)
  fix c assume less: "conv_abscissa f + 1 < ereal c"
  define c' where "c' = (if conv_abscissa f = -\<infinity> then c - 2
                     else (c - 1 + real_of_ereal (conv_abscissa f)) / 2)"
  from less have c': "conv_abscissa f < ereal c' \<and> c' < c - 1"
    by (cases "conv_abscissa f") (simp_all add: c'_def field_simps)
  
  from c' have "fds_converges f (of_real c')" 
    by (intro fds_converges) (simp_all add: inner_diff_left dot_square_norm)
  hence "fds_abs_converges f (of_real c)"
    by (rule fds_converges_imp_abs_converges) (insert c', simp_all)
  thus "\<exists>s. s \<bullet> 1 = c \<and> fds_abs_converges f s"
    by (intro exI[of _ "of_real c"]) auto
qed

  
lemma uniformly_Cauchy_eval_fds:
  assumes B: "compact B" "\<And>z. z \<in> B \<Longrightarrow> z \<bullet> 1 > conv_abscissa (f :: 'a fds)"
  shows   "uniformly_Cauchy_on B (\<lambda>N z. \<Sum>n\<le>N. fds_nth f n / nat_power n z)"
proof (cases "B = {}")
  case False
  define \<sigma> where "\<sigma> = Inf ((\<lambda>s. s \<bullet> 1) ` B)"
  have \<sigma>_le: "s \<bullet> 1 \<ge> \<sigma>" if "s \<in> B" for s
    unfolding \<sigma>_def using that 
    by (intro cInf_lower bounded_inner_imp_bdd_below compact_imp_bounded B) auto
  have "\<sigma> \<in> ((\<lambda>s. s \<bullet> 1) ` B)"
    unfolding \<sigma>_def using B \<open>B \<noteq> {}\<close>
    by (intro closed_contains_Inf bounded_inner_imp_bdd_below compact_imp_bounded B 
          compact_imp_closed compact_continuous_image continuous_intros) auto
  with B(2) have \<sigma>_gt: "\<sigma> > conv_abscissa f" by auto
  define s where "s = (if conv_abscissa f = -\<infinity> then \<sigma> - 1 else 
                         (\<sigma> + real_of_ereal (conv_abscissa f)) / 2)"
  from \<sigma>_gt have s: "conv_abscissa f < s \<and> s < \<sigma>"
    by (cases "conv_abscissa f") (auto simp: s_def)
  show ?thesis using s \<open>compact B\<close>
    by (intro uniformly_Cauchy_eval_fds_aux[of f "of_real s"] fds_converges)
       (auto dest: \<sigma>_le)
qed (auto simp: uniformly_Cauchy_on_def)

theorem uniformly_convergent_eval_fds:
  assumes B: "compact B" "\<And>z. z \<in> B \<Longrightarrow> z \<bullet> 1 > conv_abscissa (f :: 'a fds)"
  shows   "uniformly_convergent_on B (\<lambda>N z. \<Sum>n\<le>N. fds_nth f n / nat_power n z)"
  by (rule Cauchy_uniformly_convergent uniformly_Cauchy_eval_fds assms)+
    
corollary uniformly_convergent_eval_fds':
  assumes B: "compact B" "\<And>z. z \<in> B \<Longrightarrow> z \<bullet> 1 > conv_abscissa (f :: 'a fds)"
  shows   "uniformly_convergent_on B (\<lambda>N z. \<Sum>n<N. fds_nth f n / nat_power n z)"
proof -
  from uniformly_convergent_eval_fds[OF assms] obtain l where
    "uniform_limit B (\<lambda>N z. \<Sum>n\<le>N. fds_nth f n / nat_power n z) l at_top" 
    by (auto simp: uniformly_convergent_on_def)
  also have "(\<lambda>N z. \<Sum>n\<le>N. fds_nth f n / nat_power n z) = 
                (\<lambda>N z. \<Sum>n<Suc N. fds_nth f n / nat_power n z)"
    by (simp only: lessThan_Suc_atMost)
  finally have "uniform_limit B (\<lambda>N z. \<Sum>n<N. fds_nth f n / nat_power n z) l at_top" 
    unfolding uniform_limit_iff by (subst (asm) eventually_sequentially_Suc)
  thus ?thesis by (auto simp: uniformly_convergent_on_def)
qed

subsection \<open>Derivative of a Dirichlet series\<close>

lemma fds_converges_deriv_aux:
  assumes conv: "fds_converges f (s0 :: 'a)" and gt: "s \<bullet> 1 > s0 \<bullet> 1"
  shows "fds_converges (fds_deriv f) s"
proof -
  have "Cauchy (\<lambda>n. \<Sum>k\<le>n. (-ln (real k) *\<^sub>R fds_nth f k) / nat_power k s)"
  proof (rule CauchyI', goal_cases)
    case (1 \<epsilon>)
    define \<delta> where "\<delta> = s \<bullet> 1 - s0 \<bullet> 1"
    define \<delta>' where "\<delta>' = \<delta> / 2"
    from gt have \<delta>_pos: "\<delta> > 0" by (simp add: \<delta>_def)
    define A where "A = sum_upto (\<lambda>k. fds_nth f k / nat_power k s0)"
    from conv have "convergent (\<lambda>n. \<Sum>k\<le>n. fds_nth f k / nat_power k s0)"
      by (simp add: fds_converges_def summable_iff_convergent')
    hence "Bseq (\<lambda>n. \<Sum>k\<le>n. fds_nth f k / nat_power k s0)" by (rule convergent_imp_Bseq)
    then obtain C_aux where C_aux: "\<And>n. norm (\<Sum>k\<le>n. fds_nth f k / nat_power k s0) \<le> C_aux"
      by (auto simp: Bseq_def)
    define C where "C = max C_aux 1"
    have C_pos: "C > 0" by (simp add: C_def)
    have C: "norm (A x) \<le> C" for x
    proof -
      have "A x = (\<Sum>k\<le>nat \<lfloor>x\<rfloor>. fds_nth f k / nat_power k s0)"
        unfolding A_def sum_upto_altdef by (intro sum.mono_neutral_left) auto
      also have "norm \<dots> \<le> C_aux" by (rule C_aux)
      also have "\<dots> \<le> C" by (simp add: C_def)
      finally show ?thesis .
    qed
    define C' where "C' = 2 * C + C * (norm (s0 - s) * (1 + 1 / \<delta>) + 1) / \<delta>"
  
    have "(\<lambda>m. C' * real m powr (-\<delta>')) \<longlonglongrightarrow> 0" unfolding \<delta>'_def using gt \<delta>_pos
      by (intro tendsto_mult_right_zero tendsto_neg_powr filterlim_real_sequentially) simp_all
    from order_tendstoD(2)[OF this \<open>\<epsilon> > 0\<close>] obtain M1 where
      M1: "\<And>m. m \<ge> M1 \<Longrightarrow> C' * real m powr - \<delta>' < \<epsilon>" 
      by (auto simp: eventually_at_top_linorder)
    have "((\<lambda>x. ln (real x) / real x powr \<delta>') \<longlongrightarrow> 0) at_top" using \<delta>_pos
      by (intro lim_ln_over_power) (simp_all add: \<delta>'_def)
    from order_tendstoD(2)[OF this zero_less_one] eventually_gt_at_top[of "1::nat"]
      have "eventually (\<lambda>n. ln (real n) \<le> n powr \<delta>') at_top" by eventually_elim simp_all
    then obtain M2 where M2: "\<And>n. n \<ge> M2 \<Longrightarrow> ln (real n) \<le> n powr \<delta>'"
      by (auto simp: eventually_at_top_linorder)
    let ?f' = "\<lambda>k. -ln (real k) *\<^sub>R fds_nth f k"

    show ?case
    proof (intro exI[of _ "max (max M1 M2) 1"] allI impI, goal_cases)
      case (1 m n)
      hence mn: "m \<ge> M1" "m \<ge> M2" "m > 0" "m < n" by simp_all
      define g :: "real \<Rightarrow> 'a" where "g = (\<lambda>t. real_power t (s0 - s) * of_real (ln t))"
      define g' :: "real \<Rightarrow> 'a"            
        where "g' = (\<lambda>t. real_power t (s0 - s - 1) * ((s0 - s) * of_real (ln t) + 1))"
      define norm_g' :: "real \<Rightarrow> real"
        where "norm_g' = (\<lambda>t. t powr (-\<delta> - 1) * (norm (s0 - s) * ln t + 1))"
      define norm_g :: "real \<Rightarrow> real"
        where "norm_g = (\<lambda>t. -(t powr -\<delta>) * (norm (s0 - s) * (\<delta> * ln t + 1) + \<delta>) / \<delta>^2)"
      have g_g': "(g has_vector_derivative g' t) (at t)" if "t \<in> {real m..real n}" for t 
        using mn that by (auto simp: g_def g'_def real_power_diff field_simps real_power_add 
                               intro!: derivative_eq_intros)
      have [continuous_intros]: "continuous_on {real m..real n} g" using mn
        by (auto simp: g_def intro!: continuous_intros)
        
      let ?S = "\<Sum>k\<in>real -` {real m<..real n}. fds_nth f k / nat_power k s0 * g k"
      have "dist (\<Sum>k\<le>m. ?f' k / nat_power k s) (\<Sum>k\<le>n. ?f' k / nat_power k s) =
              norm (\<Sum>k\<in>{..n} - {..m}. fds_nth f k / nat_power k s * of_real (ln (real k)))" 
        using mn by (subst sum_diff) 
           (simp_all add: dist_norm norm_minus_commute sum_negf scaleR_conv_of_real mult_ac)
      also have "{..n} - {..m} = real -` {real m<..real n}" by auto
      also have "(\<Sum>k\<in>\<dots>. fds_nth f k / nat_power k s * of_real (ln (real k))) = 
        (\<Sum>k\<in>\<dots>. fds_nth f k / nat_power k s0 * g k)" using mn unfolding g_def
        by (intro sum.cong refl) (auto simp: real_power_nat_power field_simps nat_power_diff)
      also have *: "((\<lambda>t. A t * g' t) has_integral
                    (A (real n) * g n - A (real m) * g m - ?S))
                    {real m..real n}" (is "(?h has_integral _) _") unfolding A_def using mn
        by (intro partial_summation_strong[of "{}"])
           (auto intro!: g_g' simp: field_simps continuous_intros)
      hence "?S = A (real n) * g n - A (real m) * g m - integral {real m..real n} ?h"
        using mn by (simp add: has_integral_iff field_simps)
      also have "norm \<dots> \<le> norm (A (real n) * g n) + norm (A (real m) * g m) + 
                             norm (integral {real m..real n} ?h)"
        by (intro order.trans[OF norm_triangle_ineq4] add_right_mono order.refl)
      also have "norm (A (real n) * g n) \<le> C * norm (g n)"
        unfolding norm_mult using mn C_pos by (intro mult_mono C) auto
      also have "norm (g n) \<le> n powr -\<delta> * n powr \<delta>'" using mn M2[of n]
        by (simp add: g_def norm_real_power norm_mult \<delta>_def inner_diff_left)
      also have "\<dots> = n powr -\<delta>'" using mn 
        by (simp add: \<delta>'_def powr_minus field_simps powr_add [symmetric])
      also have "norm (A (real m) * g m) \<le> C * norm (g m)"
        unfolding norm_mult using mn C_pos by (intro mult_mono C) auto
      also have "norm (g m) \<le> m powr -\<delta> * m powr \<delta>'" using mn M2[of m]
        by (simp add: g_def norm_real_power norm_mult \<delta>_def inner_diff_left)
      also have "\<dots> = m powr -\<delta>'" using mn 
        by (simp add: \<delta>'_def powr_minus field_simps powr_add [symmetric])
      also have "C * real n powr - \<delta>' \<le> C * real m powr - \<delta>'" using \<delta>_pos mn C_pos
        by (intro mult_left_mono powr_mono2') (simp_all add: \<delta>'_def)
      also have "\<dots> + \<dots> = 2 * \<dots>" by simp
      also have "norm (integral {m..n} ?h) \<le> integral {m..n} (\<lambda>t. C * norm_g' t)"
      proof (intro integral_norm_bound_integral ballI, goal_cases)
        case 1
        with * show ?case by (simp add: has_integral_iff)
      next
        case 2
        from mn show ?case 
          by (auto intro!: integrable_continuous_real continuous_intros simp: norm_g'_def)
      next
        case (3 t)
        have "norm (g' t) \<le> norm_g' t" unfolding g'_def norm_g'_def using 3 mn
          unfolding norm_mult
          by (intro mult_mono order.trans[OF norm_triangle_ineq])
             (auto simp: norm_real_power inner_diff_left dot_square_norm norm_mult \<delta>_def
                   intro!: mult_left_mono)
        thus ?case unfolding norm_mult using C_pos mn 
          by (intro mult_mono C) simp_all
      qed
      also have "\<dots> = C * integral {m..n} norm_g'"
        unfolding norm_g'_def by (simp add: norm_g'_def \<delta>_def inner_diff_left)
      also {
        have "(norm_g' has_integral (norm_g n - norm_g m)) {m..n}"
          unfolding norm_g'_def norm_g_def power2_eq_square using mn \<delta>_pos
          by (intro fundamental_theorem_of_calculus)
             (auto simp: has_field_derivative_iff_has_vector_derivative [symmetric] 
                 field_simps powr_diff intro!: derivative_eq_intros)
        hence "integral {m..n} norm_g' = norm_g n - norm_g m" by (simp add: has_integral_iff)
        also have "norm_g n \<le> 0" unfolding norm_g_def using \<delta>_pos mn
          by (intro divide_nonpos_pos mult_nonpos_nonneg add_nonneg_nonneg mult_nonneg_nonneg)
             simp_all
        hence "norm_g n - norm_g m \<le> -norm_g m" by simp
        also have "\<dots> = real m powr -\<delta> * ln (real m) * (norm (s0 - s)) / \<delta> +
                        real m powr -\<delta> * ((norm (s0 - s) / \<delta> + 1) / \<delta>)" using \<delta>_pos
          by (simp add: field_simps norm_g_def power2_eq_square)
        also {
          have "ln (real m) \<le> real m powr \<delta>'" using M2[of m] mn by simp
          also have "real m powr -\<delta> * \<dots> = real m powr -\<delta>'"
            by (simp add: powr_add [symmetric] \<delta>'_def)
          finally have "real m powr -\<delta> * ln (real m) * (norm (s0 - s)) / \<delta> \<le>
                          \<dots> * (norm (s0 - s)) / \<delta>" using \<delta>_pos
            by (intro divide_right_mono mult_right_mono) (simp_all add: mult_left_mono)
        }
        also have "real m powr -\<delta> * ((norm (s0 - s) / \<delta> + 1) / \<delta>) \<le>
                     real m powr -\<delta>' * ((norm (s0 - s) / \<delta> + 1) / \<delta>)" using mn \<delta>_pos
          by (intro mult_right_mono powr_mono) (simp_all add: \<delta>'_def)
        also have "real m powr - \<delta>' * norm (s0 - s) / \<delta> + \<dots> =
                     real m powr -\<delta>' * (norm (s0 - s) * (1 + 1 / \<delta>) + 1) / \<delta>" using \<delta>_pos
          by (simp add: field_simps power2_eq_square)
        finally have "integral {real m..real n} norm_g' \<le>
                        real m powr - \<delta>' * (norm (s0 - s) * (1 + 1 / \<delta>) + 1) / \<delta>" by - simp_all
      }
      also have "2 * (C * m powr - \<delta>') + C * (m powr - \<delta>' * (norm (s0 - s) * (1 + 1 / \<delta>) + 1) / \<delta>) =
                   C' * m powr -\<delta>'" by (simp add: algebra_simps C'_def)
      also have "\<dots> < \<epsilon>" using M1[of m] mn by simp
      finally show ?case using C_pos by - simp_all
    qed
  qed
  from Cauchy_convergent[OF this] 
    show ?thesis by (simp add: summable_iff_convergent' fds_converges_def fds_nth_deriv)
qed

theorem
  assumes "s \<bullet> 1 > conv_abscissa (f :: 'a fds)"
  shows   fds_converges_deriv: "fds_converges (fds_deriv f) s"
    and   has_field_derivative_eval_fds [derivative_intros]:
            "(eval_fds f has_field_derivative eval_fds (fds_deriv f) s) (at s within A)"
proof -
  define s1 :: real where
    "s1 = (if conv_abscissa f = -\<infinity> then s \<bullet> 1 - 2 else
             (s \<bullet> 1 * 1 / 3 + real_of_ereal (conv_abscissa f) * 2 / 3))"
  define s2 :: real where
    "s2 = (if conv_abscissa f = -\<infinity> then s \<bullet> 1 - 1 else
             (s \<bullet> 1 * 2 / 3 + real_of_ereal (conv_abscissa f) * 1 / 3))"
  from assms have s: "conv_abscissa f < s1 \<and> s1 < s2 \<and> s2 < s \<bullet> 1"
    by (cases "conv_abscissa f") (auto simp: s1_def s2_def field_simps)
  from s have *: "fds_converges f (of_real s1)" by (intro fds_converges) simp_all
  thus conv': "fds_converges (fds_deriv f) s"
    by (rule fds_converges_deriv_aux) (insert s, simp_all)
  from * have conv: "fds_converges (fds_deriv f) (of_real s2)"
    by (rule fds_converges_deriv_aux) (insert s, simp_all)
      
  define \<delta> :: real where "\<delta> = (s \<bullet> 1 - s2) / 2"
  from s have \<delta>_pos: "\<delta> > 0" by (simp add: \<delta>_def)
  
  have "uniformly_convergent_on (cball s \<delta>) 
          (\<lambda>n s. \<Sum>k\<le>n. fds_nth (fds_deriv f) k / nat_power k s)"
  proof (intro uniformly_convergent_eval_fds_aux[OF conv])
    fix s'' :: 'a assume s'': "s'' \<in> cball s \<delta>"
    have "dist (s \<bullet> 1) (s'' \<bullet> 1) \<le> dist s s''" 
      by (intro Euclidean_dist_upper) (simp_all add: one_in_Basis)
    also from s'' have "\<dots> \<le> \<delta>" by simp
    finally show "s'' \<bullet> 1 > (of_real s2 :: 'a) \<bullet> 1" using s
      by (auto simp: \<delta>_def dist_real_def abs_if split: if_splits)
  qed (insert \<delta>_pos, auto)
  then obtain l where 
     "uniform_limit (cball s \<delta>) (\<lambda>n s. \<Sum>k\<le>n. fds_nth (fds_deriv f) k / nat_power k s) l at_top"
    by (auto simp: uniformly_convergent_on_def)
  also have "(\<lambda>n s. \<Sum>k\<le>n. fds_nth (fds_deriv f) k / nat_power k s) =
               (\<lambda>n s. \<Sum>k<Suc n. fds_nth (fds_deriv f) k / nat_power k s)"
    by (simp only: lessThan_Suc_atMost)
  finally have "uniform_limit (cball s \<delta>) (\<lambda>n s. \<Sum>k<n. fds_nth (fds_deriv f) k / nat_power k s) 
                  l at_top"
    unfolding uniform_limit_iff by (subst (asm) eventually_sequentially_Suc)
  hence *: "uniformly_convergent_on (cball s \<delta>) 
              (\<lambda>n s. \<Sum>k<n. fds_nth (fds_deriv f) k / nat_power k s)"
    unfolding uniformly_convergent_on_def by blast
      
  have "(eval_fds f has_field_derivative eval_fds (fds_deriv f) s) (at s)"
    unfolding eval_fds_def
  proof (rule has_field_derivative_series'(2)[OF _ _ *])
    show "s \<in> cball s \<delta>" "s \<in> interior (cball s \<delta>)" using s by (simp_all add: \<delta>_def)
    show "summable (\<lambda>n. fds_nth f n / nat_power n s)"
      using assms fds_converges[of f s] by (simp add: fds_converges_def)
  next
    fix s' :: 'a and n :: nat
    show "((\<lambda>s. fds_nth f n / nat_power n s) has_field_derivative
            fds_nth (fds_deriv f) n / nat_power n s') (at s' within cball s \<delta>)"
      by (cases "n = 0") 
         (simp, auto intro!: derivative_eq_intros simp: fds_nth_deriv field_simps)
  qed (auto simp: fds_nth_deriv intro!: derivative_eq_intros)
  thus "(eval_fds f has_field_derivative eval_fds (fds_deriv f) s) (at s within A)"
    by (rule has_field_derivative_at_within)
qed

lemmas has_field_derivative_eval_fds' [derivative_intros] = 
  DERIV_chain2[OF has_field_derivative_eval_fds]

lemma conv_abscissa_deriv_le:
  fixes f :: "'a fds"
  shows "conv_abscissa (fds_deriv f) \<le> conv_abscissa f"
proof (rule conv_abscissa_leI)
  fix c' :: real
  assume "ereal c' > conv_abscissa f"
  thus "\<exists>s. s \<bullet> 1 = c' \<and> fds_converges (fds_deriv f) s"
    by (intro exI[of _ "of_real c'"]) (auto simp: fds_converges_deriv)
qed

lemma eval_fds_deriv:
  fixes f :: "'a fds"
  assumes "s \<bullet> 1 > conv_abscissa f"
  shows   "eval_fds (fds_deriv f) s = deriv (eval_fds f) s"
  by (intro DERIV_imp_deriv [symmetric] derivative_intros assms)

end


lemma holomorphic_fds_eval [holomorphic_intros]:
  "A \<subseteq> {z. Re z > conv_abscissa f} \<Longrightarrow> eval_fds f holomorphic_on A"
  unfolding holomorphic_on_def field_differentiable_def
  by (rule ballI exI derivative_intros)+ auto
    
lemma analytic_fds_eval [holomorphic_intros]:
  assumes "A \<subseteq> {z. Re z > conv_abscissa f}"
  shows   "eval_fds f analytic_on A"
proof -
  have "eval_fds f analytic_on {z. Re z > conv_abscissa f}"
  proof (subst analytic_on_open)
    show "open {z. Re z > conv_abscissa f}"
      by (cases "conv_abscissa f") (simp_all add: open_halfspace_Re_gt)
  qed (intro holomorphic_intros, simp_all)
  from analytic_on_subset[OF this assms] show ?thesis .
qed

  
subsection \<open>Uniqueness\<close>
  
context
  assumes "SORT_CONSTRAINT ('a :: dirichlet_series)"
begin

lemma norm_dirichlet_series_cutoff_le:
  assumes "fds_abs_converges f (s0 :: 'a)" "N > 0" "s \<bullet> 1 \<ge> c" "c \<ge> s0 \<bullet> 1"
  shows   "summable (\<lambda>n. fds_nth f (n + N) / nat_power (n + N) s)"
          "summable (\<lambda>n. norm (fds_nth f (n + N)) / nat_power (n + N) c)"
    and   "norm (\<Sum>n. fds_nth f (n + N) / nat_power (n + N) s) \<le> 
             (\<Sum>n. norm (fds_nth f (n + N)) / nat_power (n + N) c) / nat_power N (s \<bullet> 1 - c)"
proof -
  from assms have "fds_abs_converges f (of_real c)" 
    using fds_abs_converges_Re_le[of f s0 "of_real c"] by auto
  hence "summable (\<lambda>n. norm (fds_nth f (n + N) / nat_power (n + N) (of_real c)))"
    unfolding fds_abs_converges_def by (rule summable_ignore_initial_segment)
  also have "?this \<longleftrightarrow> summable (\<lambda>n. norm (fds_nth f (n + N)) / nat_power (n + N) c)"
    by (intro summable_cong eventually_mono[OF eventually_gt_at_top[of "0::nat"]]) 
       (auto simp: norm_divide norm_nat_power)
  finally show *: "summable (\<lambda>n. norm (fds_nth f (n + N)) / nat_power (n + N) c)" .

  from assms have "fds_abs_converges f s" using fds_abs_converges_Re_le[of f s0 s] by auto
  hence **: "summable (\<lambda>n. norm (fds_nth f (n + N) / nat_power (n + N) s))"
    unfolding fds_abs_converges_def by (rule summable_ignore_initial_segment)
  thus "summable (\<lambda>n. fds_nth f (n + N) / nat_power (n + N) s)"
    by (rule summable_norm_cancel)

  have "norm (\<Sum>n. fds_nth f (n + N) / nat_power (n + N) s)
          \<le> (\<Sum>n. norm (fds_nth f (n + N) / nat_power (n + N) s))"
    by (intro summable_norm **) 
  also have "\<dots> \<le> (\<Sum>n. norm (fds_nth f (n + N)) / nat_power (n + N) c / nat_power N (s \<bullet> 1 - c))"
  proof (intro suminf_le * ** summable_divide allI)
    fix n :: nat
    have "real N powr (s \<bullet> 1 - c) \<le> real (n + N) powr (s \<bullet> 1 - c)"
      using assms by (intro powr_mono2) simp_all
    also have "real (n + N) powr c * \<dots> = real (n + N) powr (s \<bullet> 1)"
      by (simp add: powr_diff)
    finally have "norm (fds_nth f (n + N)) / real (n + N) powr (s \<bullet> 1) \<le>
                    norm (fds_nth f (n + N)) / (real (n + N) powr c * real N powr (s \<bullet> 1 - c))"
      using \<open>N > 0\<close> by (intro divide_left_mono) (simp_all add: mult_left_mono)
    thus "norm (fds_nth f (n + N) / nat_power (n + N) s) \<le> 
            norm (fds_nth f (n + N)) / nat_power (n + N) c / nat_power N (s \<bullet> 1 - c)"
      using \<open>N > 0\<close> by (simp add: norm_divide norm_nat_power )
  qed
  also have "\<dots> = (\<Sum>n. norm (fds_nth f (n + N)) / nat_power (n + N) c) / nat_power N (s \<bullet> 1 - c)"
    using * by (rule suminf_divide)
  finally show "norm (\<Sum>n. fds_nth f (n + N) / nat_power (n + N) s) \<le> \<dots>" .
qed

lemma eval_fds_zeroD:
  fixes S :: "'b \<Rightarrow> 'a"
  assumes conv:    "fds_abs_converges h (s0 :: 'a)"
  assumes S_limit: "filterlim (\<lambda>n. S n \<bullet> 1) at_top F" and "F \<noteq> bot"
  assumes h_zero:  "eventually (\<lambda>n. eval_fds h (S n) = 0) F"
  shows   "h = 0"
proof (rule ccontr)
  assume "h \<noteq> 0"
  hence ex: "\<exists>n>0. fds_nth h n \<noteq> 0" by (auto simp: fds_eq_iff)
  define N :: nat where "N = (LEAST n. n > 0 \<and> fds_nth h n \<noteq> 0)"
  have N: "N > 0" "fds_nth h N \<noteq> 0" 
    using LeastI_ex[OF ex, folded N_def] by auto
  have less_N: "fds_nth h n = 0" if "n < N" for n
    using Least_le[of "\<lambda>n. n > 0 \<and> fds_nth h n \<noteq> 0" n, folded N_def] that
    by (cases "n = 0") (auto simp: not_less)
      
  define c where "c = s0 \<bullet> 1"
  define remainder where "remainder = (\<lambda>s. (\<Sum>n. fds_nth h (n + Suc N) / nat_power (n + Suc N) s))"
  define A where "A = (\<Sum>n. norm (fds_nth h (n + Suc N)) / nat_power (n + Suc N) c) *
                         nat_power (Suc N) c"

  have eq: "fds_nth h N = nat_power N s * eval_fds h s - nat_power N s * remainder s"
    if "s \<bullet> 1 \<ge> c" for s :: 'a
  proof -
    from conv and that have conv': "fds_abs_converges h s" 
      unfolding c_def by (rule fds_abs_converges_Re_le)
    hence conv'': "fds_converges h s" by blast
    from conv'' have "(\<lambda>n. fds_nth h n / nat_power n s) sums eval_fds h s"
      by (simp add: fds_converges_iff)
    hence "(\<lambda>n. fds_nth h (n + Suc N) / nat_power (n + Suc N) s) sums 
             (eval_fds h s - (\<Sum>n<Suc N. fds_nth h n / nat_power n s))"
      by (rule sums_split_initial_segment)
    also have "(\<Sum>n<Suc N. fds_nth h n / nat_power n s) = 
                 (\<Sum>n<Suc N. if n = N then fds_nth h N / nat_power N s else 0)"
      by (intro sum.cong refl) (auto simp: less_N)
    also have "\<dots> = fds_nth h N / nat_power N s" by (subst sum.delta) auto
    finally show ?thesis unfolding remainder_def using \<open>N > 0\<close> by (auto simp: sums_iff field_simps)
  qed
  
  have remainder_bound: "norm (remainder s) \<le> A / real (Suc N) powr (s \<bullet> 1)"
    if "s \<bullet> 1 \<ge> c" for s :: 'a
  proof -
    note * = norm_dirichlet_series_cutoff_le[of h s0 "Suc N" c s, folded remainder_def]
    have "norm (remainder s) \<le> (\<Sum>n. norm (fds_nth h (n + Suc N)) /
           nat_power (n + Suc N) c) / nat_power (Suc N) (s \<bullet> 1 - c)"
      using that assms unfolding remainder_def by (intro *) (simp_all add: c_def)
    also have "\<dots> = A / real (Suc N) powr (s \<bullet> 1)" by (simp add: A_def powr_diff)
    finally show ?thesis .
  qed
    
  from S_limit have "eventually (\<lambda>k. S k \<bullet> 1 \<ge> s0 \<bullet> 1) F"
    by (auto simp: filterlim_at_top)
  with h_zero have "eventually (\<lambda>k. norm (fds_nth h N) \<le> 
                      (real N / real (Suc N)) powr (S k \<bullet> 1) * A) F"
  proof eventually_elim
    case (elim k)
    hence "norm (fds_nth h N) = real N powr (S k \<bullet> 1) *  norm (remainder (S k))"
      (is "_ = _ * ?X") using \<open>N > 0\<close> by (simp add: eq h_zero norm_mult norm_nat_power c_def)
    also have "norm (remainder (S k)) \<le> A / real (Suc N) powr (S k \<bullet> 1)"
      using elim by (intro remainder_bound) (simp_all add: c_def)
    finally show ?case
      using N by (simp add: mult_left_mono powr_divide field_simps del: of_nat_Suc)
  qed
  moreover have "((\<lambda>k. exp (ln (real N / real (Suc N)) * (S k \<bullet> 1)) * A) \<longlongrightarrow> 0 * A) F"
    by (intro tendsto_mult filterlim_tendsto_neg_mult_at_bot[OF tendsto_const] assms
          filterlim_compose[OF exp_at_bot]) (insert \<open>N > 0\<close>, simp_all add: ln_div del: of_nat_Suc)
  hence "((\<lambda>k. (real N / real (Suc N)) powr (S k \<bullet> 1) * A) \<longlongrightarrow> 0) F"
    using \<open>N > 0\<close> by (simp add: powr_def mult.commute)
  ultimately have "((\<lambda>_. fds_nth h N) \<longlongrightarrow> 0) F" by (rule Lim_null_comparison)
  hence "fds_nth h N = 0" using \<open>F \<noteq> bot\<close> by (simp add: tendsto_const_iff)
  with \<open>fds_nth h N \<noteq> 0\<close> show False by contradiction
qed

lemma eval_fds_eqD:
  fixes S :: "'b \<Rightarrow> 'a"
  assumes conv:    "fds_abs_converges f (s0 :: 'a)" "fds_abs_converges g (s0 :: 'a)"
  assumes S_limit: "filterlim (\<lambda>n. S n \<bullet> 1) at_top F" and "F \<noteq> bot"
  assumes eq:      "eventually (\<lambda>n. eval_fds f (S n) = eval_fds g (S n)) F"
  shows   "f = g"
proof -
  from S_limit have "eventually (\<lambda>n. S n \<bullet> 1 \<ge> s0 \<bullet> 1) F"
    by (auto simp: filterlim_at_top)
  with eq have *: "eventually (\<lambda>n. eval_fds (f - g) (S n) = 0) F"
    by eventually_elim (subst eval_fds_diff, insert conv, auto dest: fds_abs_converges_Re_le)
  have "f - g = 0" by (rule eval_fds_zeroD fds_abs_converges_diff assms * )+
  thus ?thesis by simp
qed

end


subsection \<open>Limit at infinity\<close>

lemma tendsto_eval_fds_Re_at_top:
  assumes "conv_abscissa (f :: 'a :: dirichlet_series fds) \<noteq> \<infinity>"
  assumes lim: "filterlim (\<lambda>x. S x \<bullet> 1) at_top F"
  shows   "((\<lambda>x. eval_fds f (S x)) \<longlongrightarrow> fds_nth f 1) F"
proof -
  from assms(1) have "abs_conv_abscissa f < \<infinity>"
    using abs_conv_le_conv_abscissa_plus_1[of f] by auto
  from ereal_dense2[OF this] obtain c where c: "abs_conv_abscissa f < ereal c" by auto
    
  from c have "fds_abs_converges f (of_real c)" by (intro fds_abs_converges) simp_all
  also have "?this \<longleftrightarrow> summable (\<lambda>n. norm (fds_nth f n) / real n powr c)"
    unfolding fds_abs_converges_def
    by (intro summable_cong eventually_mono[OF eventually_gt_at_top[of "0::nat"]]) 
       (auto simp: norm_divide norm_nat_power)
  finally have summable_c: \<dots> .
  define B where "B = (\<Sum>n. norm (fds_nth f (n+2)) / real (n+2) powr c) * 2 powr c"

  have *: "norm (eval_fds f s - fds_nth f 1) \<le> B / 2 powr (s \<bullet> 1)" if s: "s \<bullet> 1 \<ge> c" for s
  proof -
    note c
    also from s have "ereal c \<le> ereal (s \<bullet> 1)" by simp
    finally have "fds_abs_converges f s" by (rule fds_abs_converges)
    hence summable: "summable (\<lambda>n. norm (fds_nth f n / nat_power n s))"
      by (simp add: fds_abs_converges_def)
    from summable_norm_cancel[OF this]
      have "(\<lambda>n. fds_nth f n / nat_power n s) sums eval_fds f s"
      by (simp add: eval_fds_def sums_iff)
    from sums_split_initial_segment[OF this, of "Suc (Suc 0)"]
      have "norm (eval_fds f s - fds_nth f 1) = norm (\<Sum>n. fds_nth f (n+2) / nat_power (n+2) s)"
      by (auto simp: sums_iff)
    also have "\<dots> \<le> (\<Sum>n. norm (fds_nth f (n+2) / nat_power (n+2) s))"
      by (intro summable_norm summable_ignore_initial_segment summable)
    also have "\<dots> \<le> (\<Sum>n. norm (fds_nth f (n+2)) / real (n+2) powr c / 2 powr (s \<bullet> 1 - c))"
    proof (intro suminf_le allI)
      fix n :: nat
      have "norm (fds_nth f (n + 2) / nat_power (n + 2) s) =
              norm (fds_nth f (n + 2)) / real (n+2) powr c / real (n+2) powr (s\<bullet>1 - c)"
        by (simp add: field_simps powr_diff norm_divide norm_nat_power)
      also have "\<dots> \<le> norm (fds_nth f (n + 2)) / real (n+2) powr c / 2 powr (s\<bullet>1 - c)" using s
        by (intro divide_left_mono divide_nonneg_pos powr_mono2 mult_pos_pos) simp_all
      finally show "norm (fds_nth f (n + 2) / nat_power (n + 2) s) \<le> \<dots>" .
    qed (intro summable_ignore_initial_segment summable summable_divide summable_c)+
    also have "\<dots> = (\<Sum>n. norm (fds_nth f (n+2)) / real (n+2) powr c) / 2 powr (s \<bullet> 1 - c)"
      by (intro suminf_divide summable_ignore_initial_segment summable_c)
    also have "\<dots> = B / 2 powr (s \<bullet> 1)" by (simp add: B_def powr_diff)
    finally show ?thesis .
  qed
  moreover from lim have "eventually (\<lambda>x. S x \<bullet> 1 \<ge> c) F" by (auto simp: filterlim_at_top)
  ultimately have "eventually (\<lambda>x. norm (eval_fds f (S x) - fds_nth f 1) \<le> 
                      B / 2 powr (S x \<bullet> 1)) F" by (auto elim!: eventually_mono)
  moreover have "((\<lambda>x. B / 2 powr (S x \<bullet> 1)) \<longlongrightarrow> 0) F"
    using filterlim_tendsto_pos_mult_at_top[OF tendsto_const[of "ln 2"] _ lim]
    by (intro real_tendsto_divide_at_top[OF tendsto_const])
       (auto simp: powr_def mult_ac intro!: filterlim_compose[OF exp_at_top])
  ultimately have "((\<lambda>x. eval_fds f (S x) - fds_nth f 1) \<longlongrightarrow> 0) F"
    by (rule Lim_null_comparison)
  thus ?thesis by (subst (asm) Lim_null [symmetric])
qed

lemma tendsto_eval_fds_Re_going_to_at_top:
  assumes "conv_abscissa (f :: 'a :: dirichlet_series fds) \<noteq> \<infinity>"
  shows   "((\<lambda>s. eval_fds f s) \<longlongrightarrow> fds_nth f 1) ((\<lambda>s. s \<bullet> 1) going_to at_top)"
  using assms by (rule tendsto_eval_fds_Re_at_top) auto

lemma tendsto_eval_fds_Re_going_to_at_top':
  assumes "conv_abscissa (f :: complex fds) \<noteq> \<infinity>"
  shows   "((\<lambda>s. eval_fds f s) \<longlongrightarrow> fds_nth f 1) (Re going_to at_top)"
  using assms by (rule tendsto_eval_fds_Re_at_top) auto



subsection \<open>Auxiliary lemmas about summation\<close>

lemma integral_count_space_cong:
  assumes "\<And>x. x \<in> A \<Longrightarrow> f x = f' x" "A = A'"
  shows   "lebesgue_integral (count_space A) f = lebesgue_integral (count_space A') f'"
  using assms(1) unfolding assms(2) by (intro integral_cong_AE) (simp_all add: AE_count_space)    

lemma lebesgue_integral_count_space_finite_support':
  assumes "finite B" "B \<subseteq> A" "\<And>x. x \<in> A - B \<Longrightarrow> f x = 0"
  shows "(\<integral>x. f x \<partial>count_space A) = (\<Sum>a | a \<in> B. f a)"
proof -
  from assms have "{x. x \<in> A \<and> f x \<noteq> 0} \<subseteq> B" by auto
  note fin = finite_subset[OF this \<open>finite B\<close>]
  have "(\<integral>x. f x \<partial>count_space A) = (\<Sum>a | a \<in> A \<and> f a \<noteq> 0. f a)"
    using fin by (intro lebesgue_integral_count_space_finite_support)
  also from assms fin have "\<dots> = (\<Sum>a | a \<in> B. f a)"
    by (intro sum.mono_neutral_left) auto
  finally show ?thesis .
qed

lemma set_integrable_carrier_count_space [simp]:
  "A \<subseteq> B \<Longrightarrow> set_integrable (count_space A) B f = integrable (count_space A) f"
  by (rule integrable_cong_AE) (auto simp: AE_count_space indicator_def)

lemma integrable_count_space_subset:
  fixes f :: "'a \<Rightarrow> 'b :: {banach, second_countable_topology}"
  assumes "integrable (count_space B) f" "A \<subseteq> B"
  shows   "integrable (count_space A) f"
proof -
  from assms have "set_integrable (count_space B) B f" by simp
  from set_integrable_subset[OF this _ assms(2)] assms(2)
    have "integrable (restrict_space (count_space B) A) f"
    by (subst integrable_restrict_space) auto
  also from assms have "restrict_space (count_space B) A = count_space A"
    by (simp add: restrict_count_space Int_absorb2)
  finally show ?thesis .
qed

lemma norm_scaleR': "norm (a *\<^sub>R b) = abs a *\<^sub>R norm b"
  by simp

lemma set_integral_at_point:
  fixes a
  assumes "set_integrable M {a} f"
  and [simp]: "{a} \<in> sets M" and "(emeasure M) {a} \<noteq> \<infinity>"
  shows "(LINT x:{a} | M. f x) = f a * measure M {a}"
proof-
  have "set_lebesgue_integral M {a} f = set_lebesgue_integral M {a} (%x. f a)"
    by (intro set_lebesgue_integral_cong) simp_all
  then show ?thesis using assms by simp
qed

lemma integrable_at_point_count_space: 
  fixes f :: "'a \<Rightarrow> 'b::{banach, second_countable_topology}"
  shows "set_integrable (count_space A) {a} f"
proof -
  have "set_integrable (count_space A) {a} f \<longleftrightarrow> integrable (restrict_space (count_space A) {a}) f"
    by (subst integrable_restrict_space) simp_all
  also have "restrict_space (count_space A) {a} = count_space ({a} \<inter> A)"
    by (simp add: restrict_count_space)
  also have "integrable \<dots> f" by (intro integrable_count_space) auto
  finally show ?thesis .
qed

lemma set_integral_at_point_count_space:
  fixes f :: "'a \<Rightarrow> 'b::{banach, second_countable_topology}"
  assumes "a \<in> A"
  shows   "(LINT x:{a} | count_space A. f x) = f a"
proof-
  have "set_lebesgue_integral (count_space A) {a} f = 
          set_lebesgue_integral (count_space A) {a} (%x. f a)"
    using assms by (intro set_lebesgue_integral_cong) simp_all
  then show ?thesis using assms by simp
qed

lemma AE_count_spaceI: "(\<And>x. x \<in> A \<Longrightarrow> P x) \<Longrightarrow> AE x in count_space A. P x"
  by (simp add: AE_count_space)

lemma norm_norm: "norm (norm x) = norm x" by simp
    
lemma integral_indicator': 
  assumes "A \<in> sets M" "emeasure M A < \<infinity>"
  shows "integral\<^sup>L M (indicator A) = (of_real (measure M (A \<inter> space M))
            :: 'a :: {banach, second_countable_topology, real_algebra_1})"
proof -
  have "integral\<^sup>L M (indicator A) = integral\<^sup>L M (\<lambda>x. of_real (indicator A x))"
    by (simp add: indicator_def [abs_def] if_distrib cong: if_cong)
  also have "\<dots> = of_real (integral\<^sup>L M (\<lambda>x. indicator A x))"
    by (intro integral_of_real integrable_real_indicator assms)
  finally show ?thesis by simp
qed

  
subsection \<open>Multiplication of two series\<close>

lemma 
  fixes f g :: "nat \<Rightarrow> 'a :: {banach, real_normed_field, second_countable_topology, nat_power}"
  fixes s :: 'a
  assumes [simp]: "f 0 = 0" "g 0 = 0"
  assumes summable: "summable (\<lambda>n. norm (f n / nat_power n s))"
                    "summable (\<lambda>n. norm (g n / nat_power n s))"
  shows   summable_dirichlet_prod: "summable (\<lambda>n. norm (dirichlet_prod f g n / nat_power n s))"
    and   suminf_dirichlet_prod:
            "(\<Sum>n. dirichlet_prod f g n / nat_power n s) = 
               (\<Sum>n. f n / nat_power n s) * (\<Sum>n. g n / nat_power n s)"
proof -
  have summable': "(\<lambda>n. f n / nat_power n s) abs_summable_on A"
                  "(\<lambda>n. g n / nat_power n s) abs_summable_on A" for A
    by ((rule abs_summable_on_subset[OF _ subset_UNIV], insert summable, 
        simp add: abs_summable_on_nat_iff'); fail)+
  have f_g: "f a / nat_power a s * (g b / nat_power b s) =
              f a * g b / nat_power (a * b) s" for a b
    by (cases "a * b = 0") (auto simp: nat_power_mult_distrib)

  have eq: "(\<Sum>\<^sub>a(m, n)\<in>{(m, n). m * n = x}. f m * g n / nat_power x s) =
              dirichlet_prod f g x / nat_power x s" for x :: nat
  proof (cases "x > 0")
    case False
    hence "(\<Sum>\<^sub>a(m,n) | m * n = x. f m * g n / nat_power x s) = (\<Sum>\<^sub>a(m,n) | m * n = x. 0)"
      by (intro infsetsum_cong) auto
    with False show ?thesis by simp
  next
    case True
    from finite_divisors_nat'[OF this] show ?thesis 
      by (simp add: dirichlet_prod_altdef2 case_prod_unfold sum_divide_distrib)
  qed

  have "(\<lambda>(m,n). (f m / nat_power m s) * (g n / nat_power n s)) abs_summable_on UNIV \<times> UNIV"
    using summable' by (intro abs_summable_on_product) auto
  also have "?this \<longleftrightarrow> (\<lambda>(m,n). f m * g n / nat_power (m*n) s) abs_summable_on UNIV"
    using f_g by (intro abs_summable_on_cong) auto
  also have "\<dots> \<longleftrightarrow> (\<lambda>(x,(m,n)). f m * g n / nat_power (m*n) s) abs_summable_on 
                           (SIGMA x:UNIV. {(m,n). m * n = x})"
    unfolding case_prod_unfold
    by (rule abs_summable_on_reindex_bij_betw [symmetric]) 
       (auto simp: bij_betw_def inj_on_def image_iff)
  also have "\<dots> \<longleftrightarrow> (\<lambda>(x,(m,n)). f m * g n / nat_power x s) abs_summable_on 
                           (SIGMA x:UNIV. {(m,n). m * n = x})"
    by (intro abs_summable_on_cong) auto
  finally have summable'': \<dots> .
  from abs_summable_on_Sigma_project1'[OF this]
    show summable''': "summable (\<lambda>n. norm (dirichlet_prod f g n / nat_power n s))"
    by (simp add: eq abs_summable_on_nat_iff')

  have "(\<Sum>n. f n / nat_power n s) * (\<Sum>n. g n / nat_power n s) =
          (\<Sum>\<^sub>an. f n / nat_power n s) * (\<Sum>\<^sub>an. g n / nat_power n s)"
    using summable' by (simp add: infsetsum_nat')
  also have "\<dots> = (\<Sum>\<^sub>a(m,n). (f m / nat_power m s) * (g n / nat_power n s))"
    using summable' by (subst infsetsum_product [symmetric]) simp_all
  also have "\<dots> = (\<Sum>\<^sub>a(m,n). f m * g n / nat_power (m * n) s)"
    using f_g by (intro infsetsum_cong refl) auto
  also have "\<dots> = (\<Sum>\<^sub>a(x,(m,n))\<in>(SIGMA x:UNIV. {(m,n). m * n = x}). 
                      f m * g n / nat_power (m * n) s)" 
    unfolding case_prod_unfold
    by (rule infsetsum_reindex_bij_betw [symmetric]) (auto simp: bij_betw_def inj_on_def image_iff)
  also have "\<dots> = (\<Sum>\<^sub>a(x,(m,n))\<in>(SIGMA x:UNIV. {(m,n). m * n = x}). 
                      f m * g n / nat_power x s)"
    by (intro infsetsum_cong refl) (auto simp: case_prod_unfold)
  also have "\<dots> = (\<Sum>\<^sub>ax. dirichlet_prod f g x / nat_power x s)"
    (is "_ = infsetsum ?T _") using summable'' by (subst infsetsum_Sigma) (auto simp: eq)
  also have "\<dots> = (\<Sum>x. dirichlet_prod f g x / nat_power x s)"
    using summable''' by (intro infsetsum_nat') (simp_all add: abs_summable_on_nat_iff')
  finally show "\<dots> = (\<Sum>n. f n / nat_power n s) * (\<Sum>n. g n / nat_power n s)" ..
qed

lemma 
  fixes f g :: "nat \<Rightarrow> real"
  fixes s :: real
  assumes "f 0 = 0" "g 0 = 0"
  assumes summable: "summable (\<lambda>n. norm (f n / real n powr s))"
                    "summable (\<lambda>n. norm (g n / real n powr s))"
  shows   summable_dirichlet_prod_real: "summable (\<lambda>n. norm (dirichlet_prod f g n / real n powr s))"
    and   suminf_dirichlet_prod_real:
            "(\<Sum>n. dirichlet_prod f g n / real n powr s) = 
               (\<Sum>n. f n / nat_power n s) * (\<Sum>n. g n / real n powr s)"
  using summable_dirichlet_prod[of f g s] suminf_dirichlet_prod[of f g s] assms by simp_all

lemma fds_abs_converges_mult: 
  fixes s :: "'a :: {nat_power, real_normed_field, banach, second_countable_topology}"
  assumes "fds_abs_converges f s" "fds_abs_converges g s"
  shows   "fds_abs_converges (f * g) s"
  using summable_dirichlet_prod[OF _ _ assms[unfolded fds_abs_converges_def]]
  by (simp add: fds_abs_converges_def fds_nth_times)

lemma eval_fds_mult:
  fixes s :: "'a :: {nat_power, real_normed_field, banach, second_countable_topology}"
  assumes "fds_abs_converges f s" "fds_abs_converges g s"
  shows   "eval_fds (f * g) s = eval_fds f s * eval_fds g s"
  using suminf_dirichlet_prod[OF _ _ assms[unfolded fds_abs_converges_def]]
  by (simp_all add: eval_fds_def fds_nth_times)

lemma eval_fds_inverse:
  fixes s :: "'a :: {nat_power, real_normed_field, banach, second_countable_topology}"
  assumes "fds_abs_converges f s" "fds_abs_converges (inverse f) s" "fds_nth f 1 \<noteq> 0"
  shows   "eval_fds (inverse f) s = inverse (eval_fds f s)"
proof -
  have "eval_fds (inverse f * f) s = eval_fds (inverse f) s * eval_fds f s"
    by (intro eval_fds_mult assms)
  also have "inverse f * f = 1" by (intro fds_left_inverse assms)
  also have "eval_fds 1 s = 1" by simp
  finally show ?thesis by (auto simp: divide_simps)
qed



lemma fds_euler_product_LIMSEQ:
  fixes f :: "'a :: {nat_power, real_normed_field, banach, second_countable_topology} fds"
  assumes "multiplicative_function (fds_nth f)" and "fds_abs_converges f s"
  shows   "(\<lambda>n. \<Prod>p\<le>n. if prime p then \<Sum>i. fds_nth f (p ^ i) / nat_power (p ^ i) s else 1) \<longlonglongrightarrow> 
             eval_fds f s"
  unfolding eval_fds_def
proof (rule euler_product_LIMSEQ)
  show "multiplicative_function (\<lambda>n. fds_nth f n / nat_power n s)"
    by (rule multiplicative_function_divide_nat_power) fact+
qed (insert assms, auto simp: fds_abs_converges_def)

lemma fds_euler_product_LIMSEQ':
  fixes f :: "'a :: {nat_power, real_normed_field, banach, second_countable_topology} fds"
  assumes "completely_multiplicative_function (fds_nth f)" and "fds_abs_converges f s"
  shows   "(\<lambda>n. \<Prod>p\<le>n. if prime p then inverse (1 - fds_nth f p / nat_power p s) else 1) \<longlonglongrightarrow> 
             eval_fds f s"
  unfolding eval_fds_def
proof (rule euler_product_LIMSEQ')
  show "completely_multiplicative_function (\<lambda>n. fds_nth f n / nat_power n s)"
    by (rule completely_multiplicative_function_divide_nat_power) fact+
qed (insert assms, auto simp: fds_abs_converges_def)

lemma fds_abs_convergent_euler_product:
  fixes f :: "'a :: {nat_power, real_normed_field, banach, second_countable_topology} fds"
  assumes "multiplicative_function (fds_nth f)" and "fds_abs_converges f s"
  shows   "abs_convergent_prod 
             (\<lambda>p. if prime p then \<Sum>i. fds_nth f (p ^ i) / nat_power (p ^ i) s else 1)"
  unfolding eval_fds_def
proof (rule abs_convergent_euler_product)
  show "multiplicative_function (\<lambda>n. fds_nth f n / nat_power n s)"
    by (rule multiplicative_function_divide_nat_power) fact+
qed (insert assms, auto simp: fds_abs_converges_def)

lemma fds_abs_convergent_euler_product':
  fixes f :: "'a :: {nat_power, real_normed_field, banach, second_countable_topology} fds"
  assumes "completely_multiplicative_function (fds_nth f)" and "fds_abs_converges f s"
  shows   "abs_convergent_prod 
             (\<lambda>p. if prime p then inverse (1 - fds_nth f p / nat_power p s) else 1)"
  unfolding eval_fds_def
proof (rule abs_convergent_euler_product')
  show "completely_multiplicative_function (\<lambda>n. fds_nth f n / nat_power n s)"
    by (rule completely_multiplicative_function_divide_nat_power) fact+
qed (insert assms, auto simp: fds_abs_converges_def)

lemma fds_abs_convergent_zero_iff:
  fixes f :: "'a :: {nat_power_field, real_normed_field, banach, second_countable_topology} fds"
  assumes "completely_multiplicative_function (fds_nth f)"
  assumes "fds_abs_converges f s"
  shows   "eval_fds f s = 0 \<longleftrightarrow> (\<exists>p. prime p \<and> fds_nth f p = nat_power p s)"
proof -
  let ?g = "\<lambda>p. if prime p then inverse (1 - fds_nth f p / nat_power p s) else 1" 
  have lim: "(\<lambda>n. \<Prod>p\<le>n. ?g p) \<longlonglongrightarrow> eval_fds f s"
    by (intro fds_euler_product_LIMSEQ' assms)
  have conv: "convergent_prod ?g"
    by (intro abs_convergent_prod_imp_convergent_prod fds_abs_convergent_euler_product' assms)

  {
    assume "eval_fds f s = 0"
    from convergent_prod_to_zero_iff[OF conv] and this and lim
      have "\<exists>p. prime p \<and> fds_nth f p = nat_power p s" 
      by (auto split: if_splits)
  } moreover {
    assume "\<exists>p. prime p \<and> fds_nth f p = nat_power p s"
    then obtain p where "prime p" "fds_nth f p = nat_power p s" by blast
    moreover from this have "nat_power p s \<noteq> 0" 
      by (intro nat_power_nonzero) (auto simp: prime_gt_0_nat)
    ultimately have "(\<lambda>n. \<Prod>p\<le>n. ?g p) \<longlonglongrightarrow> 0"
      using convergent_prod_to_zero_iff[OF conv]
      by (auto intro!: exI[of _ p] split: if_splits)
    from tendsto_unique[OF _ lim this] have "eval_fds f s = 0"
      by simp
  }
  ultimately show ?thesis by blast
qed

lemma 
  fixes s :: "'a :: {nat_power_normed_field,banach,euclidean_space}"
  assumes "s \<bullet> 1 > 1"
  shows   euler_product_fds_zeta: 
            "(\<lambda>n. \<Prod>p\<le>n. if prime p then inverse (1 - 1 / nat_power p s) else 1)
                \<longlonglongrightarrow> eval_fds fds_zeta s" (is ?th1)
  and     eval_fds_zeta_nonzero: "eval_fds fds_zeta s \<noteq> 0"
proof -
  have *: "completely_multiplicative_function (fds_nth fds_zeta)"
    by standard auto
  have lim: "(\<lambda>n. \<Prod>p\<le>n. if prime p then inverse (1 - fds_nth fds_zeta p / nat_power p s) else 1) 
          \<longlonglongrightarrow> eval_fds fds_zeta s" (is "filterlim ?g _ _")
    using assms by (intro fds_euler_product_LIMSEQ' * fds_abs_summable_zeta)
  also have "?g = (\<lambda>n. \<Prod>p\<le>n. if prime p then inverse (1 - 1 / nat_power p s) else 1)"
    by (intro ext prod.cong refl) (auto simp: fds_zeta_def fds_nth_fds)
  finally show ?th1 .

  {
    fix p :: nat assume "prime p"
    from this have "p > 1" by (simp add: prime_gt_Suc_0_nat)
    hence "norm (nat_power p s) = real p powr (s \<bullet> 1)" 
      by (simp add: norm_nat_power)
    also have "\<dots> > real p powr 0" using assms and \<open>p > 1\<close> 
      by (intro powr_less_mono) auto
    finally have "nat_power p s \<noteq> 1"
      using \<open>p > 1\<close> by auto
  }
  hence **: "\<nexists>p. prime p \<and> fds_nth fds_zeta p = nat_power p s"
    by (auto simp: fds_zeta_def fds_nth_fds)
  show "eval_fds fds_zeta s \<noteq> 0"
    using assms * ** by (subst fds_abs_convergent_zero_iff) simp_all
qed

subsection \<open>Application to the M\"{o}bius $\mu$ function\<close>

lemma inverse_squares_sums': "(\<lambda>n. 1 / real n ^ 2) sums (pi ^ 2 / 6)"
  using inverse_squares_sums sums_Suc_iff[of "\<lambda>n. 1 / real n ^ 2" "pi^2 / 6"] by simp

lemma norm_summable_moebius_over_square: 
  "summable (\<lambda>n. norm (moebius_mu n / real n ^ 2))"
proof (subst summable_Suc_iff [symmetric], rule summable_comparison_test)
  show "summable (\<lambda>n. 1 / real (Suc n) ^ 2)"
    using inverse_squares_sums by (simp add: sums_iff)
qed (auto simp del: of_nat_Suc simp: field_simps abs_moebius_mu_le)

lemma summable_moebius_over_square:
  "summable (\<lambda>n. moebius_mu n / real n ^ 2)"
  using norm_summable_moebius_over_square by (rule summable_norm_cancel)

lemma moebius_over_square_sums: "(\<lambda>n. moebius_mu n / n\<^sup>2) sums (6 / pi\<^sup>2)"
proof -
  have "1 = eval_fds (1 :: real fds) 2" by simp
  also have "(1 :: real fds) = fds_zeta * fds moebius_mu" 
    by (rule fds_zeta_times_moebius_mu [symmetric])
  also have "eval_fds \<dots> 2 = eval_fds fds_zeta 2 * eval_fds (fds moebius_mu) 2"
    by (intro eval_fds_mult fds_abs_converges_moebius_mu_real) simp_all
  also have "\<dots> = pi ^ 2 / 6 * (\<Sum>n. moebius_mu n / (real n)\<^sup>2)"
    using inverse_squares_sums' by (simp add: eval_fds_at_numeral suminf_fds_zeta_aux sums_iff)
  finally have "(\<Sum>n. moebius_mu n / (real n)\<^sup>2) = 6 / pi ^ 2" by (simp add: field_simps)
  with summable_moebius_over_square show ?thesis by (simp add: sums_iff)
qed
  
end
