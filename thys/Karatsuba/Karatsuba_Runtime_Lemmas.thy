theory Karatsuba_Runtime_Lemmas
  imports Complex_Main "Akra_Bazzi.Akra_Bazzi_Method"
begin

text "An explicit bound for a specific class of recursive functions."

context
  fixes a b c d :: nat
  fixes f :: "nat \<Rightarrow> nat"
  assumes small_bounds: "f 0 \<le> a" "f (Suc 0) \<le> a"
  assumes recursive_bound: "\<And>n. n > 1 \<Longrightarrow> f n \<le> c * n + d + f (n div 2)"
begin

private fun g where
"g 0 = a"
| "g (Suc 0) = a"
| "g n = c * n + d + g (n div 2)"

private lemma f_g_bound: "f n \<le> g n"
  apply (induction n rule: g.induct)
  subgoal using small_bounds by simp
  subgoal using small_bounds by simp
  subgoal for x using recursive_bound[of "Suc (Suc x)"] by auto
  done

private lemma g_mono_aux: "a \<le> g n"
  by (induction n rule: g.induct) simp_all

private lemma g_mono: "m \<le> n \<Longrightarrow> g m \<le> g n"
proof (induction m arbitrary: n rule: g.induct)
  case 1
  then show ?case using g_mono_aux by simp
next
  case 2
  then show ?case using g_mono_aux by simp
next
  case (3 x)
  then obtain y where "n = Suc (Suc y)" using Suc_le_D by blast
  have "g (Suc (Suc x)) = c * Suc (Suc x) + d + g (Suc (Suc x) div 2)"
    by simp
  also have "... \<le> c * n + d + g (n div 2)"
    using 3
    by (metis add_mono add_mono_thms_linordered_semiring(3) div_le_mono nat_mult_le_cancel_disj)
  finally show ?case using \<open>n = Suc (Suc y)\<close> by simp
qed

private lemma g_powers_of_2: "g (2 ^ n) = d * n + c * (2 ^ (n + 1) - 2) + a"
proof (induction n)
  case (Suc n)
  then obtain n' where "2 ^ Suc n = Suc (Suc n')"
    by (metis g.cases less_exp not_less_eq zero_less_Suc)
  then have "g (2 ^ Suc n) = c * 2 ^ Suc n + d + g (2 ^ n)"
    by (metis g.simps(3) nonzero_mult_div_cancel_right power_Suc2 zero_neq_numeral)
  also have "... = c * 2 ^ Suc n + d + d * n + c * (2 ^ (n + 1) - 2) + a"
    using Suc by simp
  also have "... = d * Suc n + c * (2 ^ Suc n + (2 ^ (n + 1) - 2)) + a"
    using add_mult_distrib2[symmetric, of c] by simp
  finally show ?case by simp
qed simp

private lemma pow_ineq:
  assumes "m \<ge> (1 :: nat)"
  assumes "p \<ge> 2"
  shows "p ^ m > m"
  using assms
  apply (induction m)
  subgoal by simp
  subgoal for m
    by (cases m) (simp_all add: less_trans_Suc)
  done

private lemma next_power_of_2:
  assumes "m \<ge> (1 :: nat)"
  shows "\<exists>n k. m = 2 ^ n + k \<and> k < 2 ^ n"
proof -
  from ex_power_ivl1[OF order.refl assms] obtain n where "2 ^ n \<le> m" "m < 2 ^ (n + 1)"
    by auto
  then have "m = 2 ^ n + (m - 2 ^ n)" "m - 2 ^ n < 2 ^ n" by simp_all
  then show ?thesis by blast
qed

lemma div_2_recursion_linear: "f n \<le> (2 * d + 4 * c) * n + a"
proof (cases "n \<ge> 1")
  case True
  then obtain m k where "n = 2 ^ m + k" "k < 2 ^ m" using next_power_of_2 by blast
  have "f n \<le> g n" using f_g_bound by simp
  also have "... \<le> g (2 ^ m + 2 ^ m)" using \<open>n = 2 ^ m + k\<close> \<open>k < 2 ^ m\<close> g_mono by simp
  also have "... = d * Suc m + c * (2 ^ (Suc m + 1) - 2) + a"
    using g_powers_of_2[of "Suc m"]
    apply (subst mult_2[symmetric])
    apply (subst power_Suc[symmetric])
    .
  also have "... \<le> d * Suc m + c * 2 ^ (Suc m + 1) + a" by simp
  also have "... \<le> d * 2 ^ Suc m + c * 2 ^ (Suc m + 1) + a" using less_exp[of "Suc m"]
    by (meson add_le_mono less_or_eq_imp_le mult_le_mono)
  also have "... = (2 * d + 4 * c) * 2 ^ m + a" using mult.assoc add_mult_distrib by simp
  also have "... \<le> (2 * d + 4 * c) * n + a"
    using \<open>n = 2 ^ m + k\<close> power_increasing[of m n] by simp
  finally show ?thesis .
next
  case False
  then have "n = 0" by simp
  then show ?thesis using small_bounds by simp
qed

end

text "General Lemmas for Landau notation."

lemma landau_o_plus_aux':
  fixes f g
  assumes "f \<in> o[F](g)"
  shows "O[F](g) = O[F](\<lambda>x. f x + g x)"
  apply (intro equalityI subsetI)
  subgoal using landau_o.big.trans[OF _ landau_o.plus_aux[OF assms]] by simp
  subgoal for h
    using assms by simp
  done

lemma powr_bigo_linear_index_transformation:
  fixes fl :: "nat \<Rightarrow> nat"
  fixes f :: "nat \<Rightarrow> real"
  assumes "(\<lambda>x. real (fl x)) \<in> O(\<lambda>n. real n)"
  assumes "f \<in> O(\<lambda>n. real n powr p)"
  assumes "p > 0"
  shows "f \<circ> fl \<in> O(\<lambda>n. real n powr p)"
proof -
  obtain c1 where "c1 > 0" "\<forall>\<^sub>F x in sequentially. norm (real (fl x)) \<le> c1 * norm (real x)"
    using landau_o.bigE[OF assms(1)] by auto
  then obtain N1 where fl_bound: "\<forall>x. x \<ge> N1 \<longrightarrow> norm (real (fl x)) \<le> c1 * norm (real x)"
    unfolding eventually_at_top_linorder by blast
  obtain c2 where "c2 > 0" "\<forall>\<^sub>F x in sequentially. norm (f x) \<le> c2 * norm (real x powr p)"
    using landau_o.bigE[OF assms(2)] by auto
  then obtain N2 where f_bound: "\<forall>x. x \<ge> N2 \<longrightarrow> norm (f x) \<le> c2 * norm (real x powr p)"
    unfolding eventually_at_top_linorder by blast

  define cf :: real where "cf = Max {norm (f y) | y. y \<le> N2}"
  then have "cf \<ge> 0" using Max_in[of "{norm (f y) | y. y \<le> N2}"] norm_ge_zero by fastforce
  define c where "c = c2 * c1 powr p"
  then have "c > 0" using \<open>c1 > 0\<close> \<open>c2 > 0\<close> by simp

  have "\<forall>x. x \<ge> N1 \<longrightarrow> norm (f (fl x)) \<le> cf + c * norm (real x) powr p"
  proof (intro allI impI)
    fix x
    assume "x \<ge> N1"
    show "norm (f (fl x)) \<le> cf + c * norm (real x) powr p"
    proof (cases "fl x \<ge> N2")
      case True
      then have "norm (f (fl x)) \<le> c2 * norm (real (fl x) powr p)"
        using f_bound by simp
      also have "... = c2 * norm (real (fl x)) powr p"
        by simp
      also have "... \<le> c2 * (c1 * norm (real x)) powr p"
        apply (intro mult_mono order.refl powr_mono2 norm_ge_zero)
        subgoal using \<open>p > 0\<close> by simp
        subgoal using fl_bound \<open>x \<ge> N1\<close> by simp
        subgoal using \<open>c2 > 0\<close> by simp
        subgoal by simp
        done
      also have "... = c2 * (c1 powr p * norm (real x) powr p)"
        apply (intro arg_cong[where f = "(*) c2"] powr_mult norm_ge_zero)
        using \<open>c1 > 0\<close> by simp
      also have "... = c * norm (real x) powr p" unfolding c_def by simp
      also have "... \<le> cf + c * norm (real x) powr p" using \<open>cf \<ge> 0\<close> by simp
      finally show ?thesis .
    next
      case False
      then have "norm (f (fl x)) \<le> cf" unfolding cf_def
        by (intro Max_ge) auto
      also have "... \<le> cf + c * norm (real x) powr p"
        using \<open>c > 0\<close> by simp
      finally show ?thesis .
    qed
  qed
  then have "f \<circ> fl \<in> O(\<lambda>x. cf + c * (real x) powr p)"
    apply (intro landau_o.big_mono)
    unfolding eventually_at_top_linorder comp_apply by fastforce
  also have "... = O(\<lambda>x. c * (real x) powr p)"
  proof (intro landau_o_plus_aux'[symmetric])
    have "(\<lambda>x. cf) \<in> O(\<lambda>x. real x powr 0)" by simp
    moreover have "(\<lambda>x. real x powr 0) \<in> o(\<lambda>x. real x powr p)"
      using iffD2[OF powr_smallo_iff, OF filterlim_real_sequentially sequentially_bot \<open>p > 0\<close>] .
    ultimately have "(\<lambda>x. cf) \<in> o(\<lambda>x. real x powr p)"
      by (rule landau_o.big_small_trans)
    also have "... = o(\<lambda>x. c * (real x) powr p)"
      using landau_o.small.cmult \<open>c > 0\<close> by simp
    finally show "(\<lambda>x. cf) \<in> ..." .
  qed
  also have "... = O(\<lambda>x. (real x) powr p)" using landau_o.big.cmult \<open>c > 0\<close> by simp
  finally show ?thesis .
qed

lemma real_mono: "(a \<le> b) = (real a \<le> real b)"
  by simp

lemma real_linear: "real (a + b) = real a + real b"
  by simp

lemma real_multiplicative: "real (a * b) = real a * real b"
  by simp

lemma (in landau_pair) big_1_mult_left:
  fixes f g h
  assumes "f \<in> L F (g)" "h \<in> L F (\<lambda>_. 1)"
  shows "(\<lambda>x. h x * f x) \<in> L F (g)"
proof -
  have "(\<lambda>x. f x * h x) \<in> L F (g)" using assms by (rule big_1_mult)
  also have "(\<lambda>x. f x * h x) = (\<lambda>x. h x * f x)" by auto
  finally show ?thesis .
qed

lemma norm_nonneg: "x \<ge> 0 \<Longrightarrow> norm x = x" by simp

lemma landau_mono_always:
  fixes f g
  assumes "\<And>x. f x \<ge> (0 :: real)" "\<And>x. g x \<ge> 0"
  assumes "\<And>x. f x \<le> g x"
  shows "f \<in> O[F](g)"
  apply (intro landau_o.bigI[of 1])
  using assms by simp_all

end