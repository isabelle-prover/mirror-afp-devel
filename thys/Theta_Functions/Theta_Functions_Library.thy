theory Theta_Functions_Library
imports
  "HOL-Complex_Analysis.Complex_Analysis"
  "HOL-Computational_Algebra.Computational_Algebra"
begin

lemma has_field_derivative_csqrt' [derivative_intros]:
  assumes "(f has_field_derivative f') (at x within A)" "f x \<notin> \<real>\<^sub>\<le>\<^sub>0"
  shows   "((\<lambda>x. csqrt (f x)) has_field_derivative (f' / (2 * csqrt (f x)))) (at x within A)"
proof -
  have "((csqrt \<circ> f) has_field_derivative (inverse (2 * csqrt (f x)) * f')) (at x within A)"
    using has_field_derivative_csqrt assms(1) by (rule DERIV_chain) fact
  thus ?thesis
    by (simp add: o_def field_simps)
qed

lemma analytic_on_deriv [analytic_intros]:
  assumes "f analytic_on g ` A"
  assumes "g analytic_on A"
  shows   "(\<lambda>x. deriv f (g x)) analytic_on A"
proof -
  have "(deriv f \<circ> g) analytic_on A"
    by (rule analytic_on_compose_gen[OF assms(2) analytic_deriv[OF assms(1)]]) auto
  thus ?thesis
    by (simp add: o_def)
qed

lemma valid_path_compose_analytic:
  assumes "valid_path g" and holo:"f analytic_on S" and "path_image g \<subseteq> S"
  shows "valid_path (f \<circ> g)"
proof (rule valid_path_compose[OF \<open>valid_path g\<close>])
  fix x assume "x \<in> path_image g"
  then show "f field_differentiable at x"
    using analytic_on_imp_differentiable_at analytic_on_open assms holo by blast
next
  show "continuous_on (path_image g) (deriv f)"
    by (intro holomorphic_on_imp_continuous_on analytic_imp_holomorphic analytic_intros
              analytic_on_subset[OF holo] assms)
qed

lemma contour_integral_comp_analyticW:
  assumes "f analytic_on s" "valid_path \<gamma>" "path_image \<gamma> \<subseteq> s"
  shows "contour_integral (f \<circ> \<gamma>) g = contour_integral \<gamma> (\<lambda>w. deriv f w * g (f w))"
proof -
  obtain spikes where "finite spikes" and \<gamma>_diff: "\<gamma> C1_differentiable_on {0..1} - spikes"
    using \<open>valid_path \<gamma>\<close> unfolding valid_path_def piecewise_C1_differentiable_on_def by auto  
  show "contour_integral (f \<circ> \<gamma>) g 
      = contour_integral \<gamma> (\<lambda>w. deriv f w * g (f w))"
    unfolding contour_integral_integral
  proof (rule integral_spike[rule_format,OF negligible_finite[OF \<open>finite spikes\<close>]])
    fix t::real assume t:"t \<in> {0..1} - spikes"
    then have "\<gamma> differentiable at t" 
      using \<gamma>_diff unfolding C1_differentiable_on_eq by auto
    moreover have "f field_differentiable at (\<gamma> t)" 
    proof -
      have "\<gamma> t \<in> s" using t assms unfolding path_image_def by auto 
      thus ?thesis 
        using \<open>f analytic_on s\<close>  analytic_on_imp_differentiable_at by blast
    qed
    ultimately show "deriv f (\<gamma> t) * g (f (\<gamma> t)) * vector_derivative \<gamma> (at t) =
         g ((f \<circ> \<gamma>) t) * vector_derivative (f \<circ> \<gamma>) (at t)"
      by (subst vector_derivative_chain_at_general) (simp_all add:field_simps)
  qed
qed

lemma higher_deriv_cmult':
  assumes "f analytic_on {x}"
  shows   "(deriv ^^ j) (\<lambda>x. c * f x) x = c * (deriv ^^ j) f x"
  using assms higher_deriv_cmult[of f _ x j c] assms
  using analytic_at_two by blast

lemma deriv_cmult':
  assumes "f analytic_on {x}"
  shows   "deriv (\<lambda>x. c * f x) x = c * deriv f x"
  using higher_deriv_cmult'[OF assms, of 1 c] by simp

lemma analytic_derivI:
  assumes "f analytic_on {z}"
  shows   "(f has_field_derivative (deriv f z)) (at z within A)"
  using assms holomorphic_derivI[of f _ z] analytic_at by blast

lemma deriv_compose_analytic:
  fixes f g :: "complex \<Rightarrow> complex"
  assumes "f analytic_on {g z}" "g analytic_on {z}"
  shows "deriv (\<lambda>x. f (g x)) z = deriv f (g z) * deriv g z"
proof -
  have "((f \<circ> g) has_field_derivative (deriv f (g z) * deriv g z)) (at z)"
    by (intro DERIV_chain analytic_derivI assms)
  thus ?thesis
    by (auto intro!: DERIV_imp_deriv simp add: o_def)
qed

lemma holomorphic_compact_finite_zeros:
  assumes S: "f holomorphic_on S" "open S" "connected S"
      and "compact K" "K \<subseteq> S"
      and "\<not>(\<forall>x\<in>S. f x = 0)"
    shows "finite {z\<in>K. f z = 0}"
proof (rule ccontr)
  assume "infinite {z\<in>K. f z = 0}"
  then obtain z where "z \<in> K" and z: "z islimpt {z\<in>K. f z = 0}"
    using \<open>compact K\<close> by (auto simp: compact_eq_Bolzano_Weierstrass)
  moreover have "{z\<in>K. f z = 0} \<subseteq> S"
    using \<open>K \<subseteq> S\<close> by blast
    ultimately show False
    using assms analytic_continuation [OF S]
    by blast
qed

lemma analytic_on_imp_nicely_meromorphic_on:
  "f analytic_on A \<Longrightarrow> f nicely_meromorphic_on A"
  by (meson analytic_at_imp_isCont analytic_on_analytic_at
            analytic_on_imp_meromorphic_on isContD nicely_meromorphic_on_def)



lemmas [derivative_intros del] = DERIV_sum

(* TODO: DERIV_sum in library is really, really bad due to the "?f ?x" pattern,
   which makes unification go absolutely haywire when used with e.g. 
   "auto intro!: derivative_eq_intros". Replace with the following. *)
lemma DERIV_sum[derivative_intros]:
  "(\<And> n. n \<in> S \<Longrightarrow> ((\<lambda>x. f x n) has_field_derivative (f' n)) F) \<Longrightarrow>
    ((\<lambda>x. sum (f x) S) has_field_derivative sum f' S) F"
  by (rule has_derivative_imp_has_field_derivative [OF has_derivative_sum])
     (auto simp: sum_distrib_left mult_commute_abs dest: has_field_derivative_imp_has_derivative)

lemma of_int_div: "b dvd a \<Longrightarrow> of_int (a div b) = (of_int a / of_int b :: 'a :: field_char_0)"
  by (elim dvdE) (auto simp: divide_simps)

(* some rules to simplify away annoying things like "1/2 \<in> \<int>" *)
lemma fraction_numeral_not_in_Ints [simp]:
  assumes "\<not>(numeral b :: int) dvd numeral a"
  shows   "numeral a / numeral b \<notin> (\<int> :: 'a :: {division_ring, ring_char_0} set)"
  using fraction_not_in_ints[of "numeral b" "numeral a", where ?'a = 'a] assms by simp

lemma fraction_numeral_not_in_Ints' [simp]:
  assumes "b \<noteq> Num.One"
  shows   "1 / numeral b \<notin> (\<int> :: 'a :: {division_ring, ring_char_0} set)"
  using fraction_not_in_ints[of "numeral b" 1, where ?'a = 'a] assms by simp

lemmas [simp] = not_in_Ints_imp_not_in_nonpos_Ints minus_in_Ints_iff

lemma is_square_mult_prime_left_iff:
  assumes "prime p"
  shows   "is_square (p * x) \<longleftrightarrow> p dvd x \<and> is_square (x div p)"
proof
  assume *: "p dvd x \<and> is_square (x div p)"
  have [simp]: "p \<noteq> 0"
    using assms by auto
  from * obtain y where y: "x = y ^ 2 * p"
    by (auto elim!: dvdE is_nth_powerE simp: mult_ac)
  have "is_square ((p * y) ^ 2)"
    by auto
  also have "(p * y) ^ 2 = p * x"
    by (simp add: y power2_eq_square algebra_simps)
  finally show "is_square (p * x)" .
next
  assume *: "is_square (p * x)"
  have "p \<noteq> 0"
    using assms by auto
  from * obtain y where y: "p * x = y ^ 2"
    by (elim is_nth_powerE)
  have "p dvd y ^ 2"
    by (simp flip: y)
  hence "p dvd y"
    using \<open>prime p\<close> using prime_dvd_power by blast
  then obtain z where z: "y = p * z "
    by (elim dvdE)
  have "p * x = p * (p * z ^ 2)"
    by (simp add: y z algebra_simps power2_eq_square)
  hence x_eq: "x = p * z ^ 2"
    using \<open>p \<noteq> 0\<close> by simp
  show "p dvd x \<and> is_square (x div p)"
    using \<open>p \<noteq> 0\<close> by (simp add: x_eq)
qed

lemma is_square_mult2_nat_iff:
  "is_square (2 * b :: nat) \<longleftrightarrow> even b \<and> is_square (b div 2)"
  by (rule is_square_mult_prime_left_iff) auto

lemma is_square_mult2_int_iff:
  "is_square (2 * b :: int) \<longleftrightarrow> even b \<and> is_square (b div 2)"
  by (rule is_square_mult_prime_left_iff) auto

lemma is_nth_power_mult_cancel_left:
  fixes a b :: "'a :: semiring_gcd"
  assumes "is_nth_power n a" "a \<noteq> 0"
  shows   "is_nth_power n (a * b) \<longleftrightarrow> is_nth_power n b"
proof (cases "n > 0")
  case True
  show ?thesis
  proof
    assume "is_nth_power n (a * b)"
    then obtain x where x: "a * b = x ^ n"
      by (elim is_nth_powerE)
    obtain y where y: "a = y ^ n"
      using assms by (elim is_nth_powerE)
    have "y ^ n dvd x ^ n"
      by (simp flip: x y)
    hence "y dvd x"
      using \<open>n > 0\<close> by simp
    then obtain z where z: "x = y * z"
      by (elim dvdE)
    have "x ^ n = y ^ n * z ^ n"
      by (simp add: z power_mult_distrib)
    hence "b = z ^ n"
      using \<open>a \<noteq> 0\<close> by (simp flip: x y)
    thus "is_nth_power n b"
      by auto
  qed (use assms in \<open>auto intro: is_nth_power_mult\<close>)
qed (use assms in auto)

lemma is_nth_power_mult_cancel_right:
  fixes a b :: "'a :: semiring_gcd"
  assumes "is_nth_power n b" "b \<noteq> 0"
  shows   "is_nth_power n (a * b) \<longleftrightarrow> is_nth_power n a"
  by (subst mult.commute, subst is_nth_power_mult_cancel_left) (use assms in auto)

lemma higher_deriv_complex_uniform_limit:
  assumes ulim: "uniform_limit A f g F"
      and f_holo: "eventually (\<lambda>n. f n holomorphic_on A) F"
      and F: "F \<noteq> bot"
      and A: "open A" "z \<in> A"
    shows "((\<lambda>n. (deriv ^^ m) (f n) z) \<longlongrightarrow> (deriv ^^ m) g z) F"
proof -
  obtain r where r: "r > 0" "cball z r \<subseteq> A"
    using A by (meson open_contains_cball)
  have r': "ball z r \<subseteq> A"
    using r by auto
  define h where "h = (\<lambda>n z. f n z - g z)"
  define c where "c = of_real (2*pi) * \<i> / fact m"
  have [simp]: "c \<noteq> 0"
    by (simp add: c_def)
  have "g holomorphic_on ball z r \<and> continuous_on (cball z r) g"
  proof (rule holomorphic_uniform_limit)
    show "uniform_limit (cball z r) f g F"
      by (rule uniform_limit_on_subset[OF ulim r(2)])
    show "\<forall>\<^sub>F n in F. continuous_on (cball z r) (f n) \<and> f n holomorphic_on ball z r" using f_holo
      by eventually_elim
         (use holomorphic_on_subset[OF _ r(2)] holomorphic_on_subset[OF _ r'] 
          in  \<open>auto intro!: holomorphic_on_imp_continuous_on\<close>)
  qed (use F in auto)
  hence g_holo: "g holomorphic_on ball z r" and g_cont: "continuous_on (cball z r) g"
    by blast+

  have ulim': "uniform_limit (sphere z r) (\<lambda>n x. h n x / (x - z) ^ (Suc m)) (\<lambda>_. 0) F"
  proof -
    have "uniform_limit (sphere z r) (\<lambda>n x. f n x / (x - z) ^ Suc m) (\<lambda>x. g x / (x - z) ^ Suc m) F"
    proof (intro uniform_lim_divide uniform_limit_intros uniform_limit_on_subset[OF ulim])
      have "compact (g ` sphere z r)"
        by (intro compact_continuous_image continuous_on_subset[OF g_cont]) auto
      thus "bounded (g ` sphere z r)"
        by (rule compact_imp_bounded)
      show "r ^ Suc m \<le> norm ((x - z) ^ Suc m)" if "x \<in> sphere z r" for x unfolding norm_power
        by (intro power_mono) (use that r(1) in \<open>auto simp: dist_norm norm_minus_commute\<close>)
    qed (use r in auto)
    hence "uniform_limit (sphere z r) (\<lambda>n x. f n x / (x - z) ^ Suc m - g x / (x - z) ^ Suc m) 
             (\<lambda>x. g x / (x - z) ^ Suc m - g x / (x - z) ^ Suc m) F"
      by (intro uniform_limit_intros)
    thus ?thesis
      by (simp add: h_def diff_divide_distrib)
  qed

  have has_integral: "eventually (\<lambda>n. ((\<lambda>u. h n u / (u - z) ^ Suc m) has_contour_integral 
                         c * (deriv ^^ m) (h n) z) (circlepath z r)) F"
    using f_holo
  proof eventually_elim
    case (elim n)
    show ?case
      unfolding c_def
    proof (rule Cauchy_has_contour_integral_higher_derivative_circlepath)
      show "continuous_on (cball z r) (h n)" unfolding h_def 
        by (intro continuous_intros g_cont holomorphic_on_imp_continuous_on
                  holomorphic_on_subset[OF elim] r)
      show "h n holomorphic_on ball z r"
        unfolding h_def by (intro holomorphic_intros g_holo holomorphic_on_subset[OF elim] r')
    qed (use r(1) in auto)
  qed

  have "((\<lambda>n. contour_integral (circlepath z r) (\<lambda>u. h n u / (u - z) ^ Suc m)) \<longlongrightarrow> 
         contour_integral (circlepath z r) (\<lambda>u. 0 / (u - z) ^ Suc m)) F"
  proof (rule contour_integral_uniform_limit_circlepath)
    show "\<forall>\<^sub>F n in F. (\<lambda>u. h n u / (u - z) ^ Suc m) contour_integrable_on circlepath z r"
      using has_integral by eventually_elim (blast intro: has_contour_integral_integrable)
  qed (use r(1) \<open>F \<noteq> bot\<close> ulim' in simp_all)
  hence "((\<lambda>n. contour_integral (circlepath z r) (\<lambda>u. h n u / (u - z) ^ Suc m)) \<longlongrightarrow> 0) F"
    by simp
  also have "?this \<longleftrightarrow> ((\<lambda>n. c * (deriv ^^ m) (h n) z) \<longlongrightarrow> 0) F"
  proof (rule tendsto_cong)
    show "\<forall>\<^sub>F x in F. contour_integral (circlepath z r) (\<lambda>u. h x u / (u - z) ^ Suc m) =
                       c * (deriv ^^ m) (h x) z"
      using has_integral by eventually_elim (simp add: contour_integral_unique)
  qed
  finally have "((\<lambda>n. (deriv ^^ m) g z + c * (deriv ^^ m) (h n) z / c) \<longlongrightarrow> 
                  (deriv ^^ m) g z + 0 / c) F"
    by (intro tendsto_intros) auto
  also have "?this \<longleftrightarrow> ((\<lambda>n. (deriv ^^ m) (f n) z) \<longlongrightarrow> (deriv ^^ m) g z) F"
  proof (intro filterlim_cong)
    show "\<forall>\<^sub>F n in F. (deriv ^^ m) g z + c * (deriv ^^ m) (h n) z / c = (deriv ^^ m) (f n) z"
      using f_holo
    proof eventually_elim
      case (elim n)
      have "(deriv ^^ m) (h n) z = (deriv ^^ m) (f n) z - (deriv ^^ m) g z" unfolding h_def
        by (rule higher_deriv_diff holomorphic_on_subset[OF elim r'] g_holo A)+ (use r(1) in auto)
      thus ?case
        by simp
    qed
  qed auto
  finally show ?thesis .
qed

end