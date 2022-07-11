section \<open>The Weighted Arithmetic--Geometric Mean Inequality\<close>
theory Weighted_Arithmetic_Geometric_Mean
  imports Complex_Main
begin

subsection \<open>Auxiliary Facts\<close>

lemma root_powr_inverse': "0 < n \<Longrightarrow> 0 \<le> x \<Longrightarrow> root n x = x powr (1/n)"
  by (cases "x = 0") (auto simp: root_powr_inverse)

lemma powr_sum_distrib_real_right:
  assumes "a \<noteq> 0"
  shows   "(\<Prod>x\<in>X. a powr e x :: real) = a powr (\<Sum>x\<in>X. e x)"
  using assms
  by (induction X rule: infinite_finite_induct) (auto simp: powr_add)

lemma powr_sum_distrib_real_left:
  assumes "\<And>x. x \<in> X \<Longrightarrow> a x \<ge> 0"
  shows   "(\<Prod>x\<in>X. a x powr e :: real) = (\<Prod>x\<in>X. a x) powr e"
  using assms
  by (induction X rule: infinite_finite_induct)
     (auto simp: powr_mult prod_nonneg)

lemma (in linordered_semidom) prod_mono_strict':
  assumes "i \<in> A"
  assumes "finite A"
  assumes "\<And>i. i \<in> A \<Longrightarrow> 0 \<le> f i \<and> f i \<le> g i"
  assumes "\<And>i. i \<in> A \<Longrightarrow> 0 < g i"
  assumes "f i < g i"
  shows   "prod f A < prod g A"
proof -
  have "prod f A = f i * prod f (A - {i})"
    using assms by (intro prod.remove)
  also have "\<dots> \<le> f i * prod g (A - {i})"
    using assms by (intro mult_left_mono prod_mono) auto
  also have "\<dots> < g i * prod g (A - {i})"
    using assms by (intro mult_strict_right_mono prod_pos) auto
  also have "\<dots> = prod g A"
    using assms by (intro prod.remove [symmetric])
  finally show ?thesis .
qed

lemma prod_ge_pointwise_le_imp_pointwise_eq:
  fixes f :: "'a \<Rightarrow> real"
  assumes "finite X"
  assumes ge: "prod f X \<ge> prod g X"
  assumes nonneg: "\<And>x. x \<in> X \<Longrightarrow> f x \<ge> 0"
  assumes pos: "\<And>x. x \<in> X \<Longrightarrow> g x > 0"
  assumes le: "\<And>x. x \<in> X \<Longrightarrow> f x \<le> g x" and x: "x \<in> X"
  shows   "f x = g x"
proof (rule ccontr)
  assume "f x \<noteq> g x"
  with le[of x] and x have "f x < g x"
    by auto
  hence "prod f X < prod g X"
    using x and le and nonneg and pos and \<open>finite X\<close> 
    by (intro prod_mono_strict') auto
  with ge show False
    by simp
qed

lemma powr_right_real_eq_iff:
  assumes "a \<ge> (0 :: real)"
  shows   "a powr x = a powr y \<longleftrightarrow> a = 0 \<or> a = 1 \<or> x = y"
  using assms by (auto simp: powr_def)

lemma powr_left_real_eq_iff:
  assumes "a \<ge> (0 :: real)" "b \<ge> 0" "x \<noteq> 0"
  shows   "a powr x = b powr x \<longleftrightarrow> a = b"
  using assms by (auto simp: powr_def)

lemma exp_real_eq_one_plus_iff:
  fixes x :: real
  shows "exp x = 1 + x \<longleftrightarrow> x = 0"
proof (cases "x = 0")
  case False
  define f :: "real \<Rightarrow> real" where "f = (\<lambda>x. exp x - 1 - x)"
  have deriv: "(f has_field_derivative (exp x - 1)) (at x)" for x
    by (auto simp: f_def intro!: derivative_eq_intros)

  have "\<exists>z. z>min x 0 \<and> z < max x 0 \<and> f (max x 0) - f (min x 0) = 
            (max x 0 - min x 0) * (exp z - 1)"
    using MVT2[of "min x 0" "max x 0" f "\<lambda>x. exp x - 1"] deriv False
    by (auto simp: min_def max_def)
  then obtain z where "z \<in> {min x 0<..<max x 0}"
     "f (max x 0) - f (min x 0) = (max x 0 - min x 0) * (exp z - 1)"
    by (auto simp: f_def)
  thus ?thesis using False
    by (cases x "0 :: real" rule: linorder_cases) (auto simp: f_def)
qed auto


subsection \<open>The Inequality\<close>

text \<open>
  We first prove the equality under the assumption that all the $a_i$ and $w_i$ are positive.
\<close>
lemma weighted_arithmetic_geometric_mean_pos:
  fixes a w :: "'a \<Rightarrow> real"
  assumes "finite X"
  assumes pos1: "\<And>x. x \<in> X \<Longrightarrow> a x > 0"
  assumes pos2: "\<And>x. x \<in> X \<Longrightarrow> w x > 0"
  assumes sum_weights: "(\<Sum>x\<in>X. w x) = 1"
  shows   "(\<Prod>x\<in>X. a x powr w x) \<le> (\<Sum>x\<in>X. w x * a x)"
proof -
  note nonneg1 = less_imp_le[OF pos1]
  note nonneg2 = less_imp_le[OF pos2]
  define A where "A = (\<Sum>x\<in>X. w x * a x)"
  define r where "r = (\<lambda>x. a x / A - 1)"
  from sum_weights have "X \<noteq> {}" by auto
  hence "A \<noteq> 0"
    unfolding A_def using nonneg1 nonneg2 pos1 pos2 \<open>finite X\<close>
    by (subst sum_nonneg_eq_0_iff) force+
  moreover from nonneg1 nonneg2 have "A \<ge> 0"
    by (auto simp: A_def intro!: sum_nonneg)
  ultimately have "A > 0" by simp

  have "(\<Prod>x\<in>X. (1 + r x) powr w x) = (\<Prod>x\<in>X. (a x / A) powr w x)"
    by (simp add: r_def)
  also have "\<dots> = (\<Prod>x\<in>X. a x powr w x) / (\<Prod>x\<in>X. A powr w x)"
    unfolding prod_dividef [symmetric]
    using assms pos2 \<open>A > 0\<close> by (intro prod.cong powr_divide) (auto intro: less_imp_le)
  also have "(\<Prod>x\<in>X. A powr w x) = exp ((\<Sum>x\<in>X. w x) * ln A)"
    using \<open>A > 0\<close> and \<open>finite X\<close> by (simp add: powr_def exp_sum sum_distrib_right)
  also have "(\<Sum>x\<in>X. w x) = 1" by fact
  also have "exp (1 * ln A) = A"
    using \<open>A > 0\<close> by simp
  finally have lhs: "(\<Prod>x\<in>X. (1 + r x) powr w x) = (\<Prod>x\<in>X. a x powr w x) / A" .

  have "(\<Prod>x\<in>X. exp (w x * r x)) = exp (\<Sum>x\<in>X. w x * r x)"
    using \<open>finite X\<close> by (simp add: exp_sum)
  also have "(\<Sum>x\<in>X. w x * r x) = (\<Sum>x\<in>X. a x * w x) / A - 1"
    using \<open>A > 0\<close> by (simp add: r_def algebra_simps sum_subtractf sum_divide_distrib sum_weights)
  also have "(\<Sum>x\<in>X. a x * w x) / A = 1"
    using \<open>A > 0\<close> by (simp add: A_def mult.commute)
  finally have rhs: "(\<Prod>x\<in>X. exp (w x * r x)) = 1" by simp

  have "(\<Prod>x\<in>X. a x powr w x) / A = (\<Prod>x\<in>X. (1 + r x) powr w x)"
    by (fact lhs [symmetric])
  also have "(\<Prod>x\<in>X. (1 + r x) powr w x) \<le> (\<Prod>x\<in>X. exp (w x * r x))"
  proof (intro prod_mono conjI)
    fix x assume x: "x \<in> X"
    have "1 + r x \<le> exp (r x)"
      by (rule exp_ge_add_one_self)
    hence "(1 + r x) powr w x \<le> exp (r x) powr w x"
      using nonneg1[of x] nonneg2[of x] x \<open>A > 0\<close>
      by (intro powr_mono2) (auto simp: r_def field_simps)
    also have "\<dots> = exp (w x * r x)"
      by (simp add: powr_def)
    finally show "(1 + r x) powr w x \<le> exp (w x * r x)" .
  qed auto
  also have "(\<Prod>x\<in>X. exp (w x * r x)) = 1" by (fact rhs)
  finally show "(\<Prod>x\<in>X. a x powr w x) \<le> A"
    using \<open>A > 0\<close> by (simp add: field_simps)
qed

text \<open>
  We can now relax the positivity assumptions to non-negativity: if one of the $a_i$ is
  zero, the theorem becomes trivial (note that $0^0 = 0$ by convention for the real-valued
  power operator \<^term>\<open>(powr) :: real \<Rightarrow> real \<Rightarrow> real\<close>).

  Otherwise, we can simply remove all the indices that have weight 0 and apply the
  above auxiliary version of the theorem.
\<close>
theorem weighted_arithmetic_geometric_mean:
  fixes a w :: "'a \<Rightarrow> real"
  assumes "finite X"
  assumes nonneg1: "\<And>x. x \<in> X \<Longrightarrow> a x \<ge> 0"
  assumes nonneg2: "\<And>x. x \<in> X \<Longrightarrow> w x \<ge> 0"
  assumes sum_weights: "(\<Sum>x\<in>X. w x) = 1"
  shows   "(\<Prod>x\<in>X. a x powr w x) \<le> (\<Sum>x\<in>X. w x * a x)"
proof (cases "\<exists>x\<in>X. a x = 0")
  case True
  hence "(\<Prod>x\<in>X. a x powr w x) = 0"
    using \<open>finite X\<close> by simp
  also have "\<dots> \<le> (\<Sum>x\<in>X. w x * a x)"
    by (intro sum_nonneg mult_nonneg_nonneg assms)
  finally show ?thesis .
next
  case False
  have "(\<Sum>x\<in>X-{x. w x = 0}. w x) = (\<Sum>x\<in>X. w x)"
    by (intro sum.mono_neutral_left assms) auto
  also have "\<dots> = 1" by fact
  finally have sum_weights': "(\<Sum>x\<in>X-{x. w x = 0}. w x) = 1" .

  have "(\<Prod>x\<in>X. a x powr w x) = (\<Prod>x\<in>X-{x. w x = 0}. a x powr w x)"
    using \<open>finite X\<close> False by (intro prod.mono_neutral_right) auto
  also have "\<dots> \<le> (\<Sum>x\<in>X-{x. w x = 0}. w x * a x)" using assms False
    by (intro weighted_arithmetic_geometric_mean_pos sum_weights')
       (auto simp: order.strict_iff_order)
  also have "\<dots> = (\<Sum>x\<in>X. w x * a x)"
    using \<open>finite X\<close> by (intro sum.mono_neutral_left) auto
  finally show ?thesis .
qed

text \<open>
  We can derive the regular arithmetic/geometric mean inequality from this by simply
  setting all the weights to $\frac{1}{n}$:
\<close>
corollary arithmetic_geometric_mean:
  fixes a :: "'a \<Rightarrow> real"
  assumes "finite X"
  defines "n \<equiv> card X"
  assumes nonneg: "\<And>x. x \<in> X \<Longrightarrow> a x \<ge> 0"
  shows   "root n (\<Prod>x\<in>X. a x) \<le> (\<Sum>x\<in>X. a x) / n"
proof (cases "X = {}")
  case False
  with assms have n: "n > 0"
    by auto
  have "(\<Prod>x\<in>X. a x powr (1 / n)) \<le> (\<Sum>x\<in>X. (1 / n) * a x)"
    using n assms by (intro weighted_arithmetic_geometric_mean) auto
  also have "(\<Prod>x\<in>X. a x powr (1 / n)) = (\<Prod>x\<in>X. a x) powr (1 / n)"
    using nonneg by (subst powr_sum_distrib_real_left) auto
  also have "\<dots> = root n (\<Prod>x\<in>X. a x)"
    using \<open>n > 0\<close> nonneg by (subst root_powr_inverse') (auto simp: prod_nonneg)
  also have "(\<Sum>x\<in>X. (1 / n) * a x) = (\<Sum>x\<in>X. a x) / n"
    by (subst sum_distrib_left [symmetric]) auto
  finally show ?thesis .
qed (auto simp: n_def)


subsection \<open>The Equality Case\<close>

text \<open>
  Next, we show that weighted arithmetic and geometric mean are equal if and only if all the 
  $a_i$ are equal.

  We first prove the more difficult direction as a lemmas and again first assume positivity
  of all $a_i$ and $w_i$ and will relax this somewhat later.
\<close>
lemma weighted_arithmetic_geometric_mean_eq_iff_pos:
  fixes a w :: "'a \<Rightarrow> real"
  assumes "finite X"
  assumes pos1: "\<And>x. x \<in> X \<Longrightarrow> a x > 0"
  assumes pos2: "\<And>x. x \<in> X \<Longrightarrow> w x > 0"
  assumes sum_weights: "(\<Sum>x\<in>X. w x) = 1"
  assumes eq: "(\<Prod>x\<in>X. a x powr w x) = (\<Sum>x\<in>X. w x * a x)"
  shows   "\<forall>x\<in>X. \<forall>y\<in>X. a x = a y"
proof -
  note nonneg1 = less_imp_le[OF pos1]
  note nonneg2 = less_imp_le[OF pos2]
  define A where "A = (\<Sum>x\<in>X. w x * a x)"
  define r where "r = (\<lambda>x. a x / A - 1)"
  from sum_weights have "X \<noteq> {}" by auto
  hence "A \<noteq> 0"
    unfolding A_def using nonneg1 nonneg2 pos1 pos2 \<open>finite X\<close>
    by (subst sum_nonneg_eq_0_iff) force+
  moreover from nonneg1 nonneg2 have "A \<ge> 0"
    by (auto simp: A_def intro!: sum_nonneg)
  ultimately have "A > 0" by simp

  have r_ge: "r x \<ge> -1" if x: "x \<in> X" for x
    using \<open>A > 0\<close> pos1[OF x] by (auto simp: r_def field_simps)

  have "(\<Prod>x\<in>X. (1 + r x) powr w x) = (\<Prod>x\<in>X. (a x / A) powr w x)"
    by (simp add: r_def)
  also have "\<dots> = (\<Prod>x\<in>X. a x powr w x) / (\<Prod>x\<in>X. A powr w x)"
    unfolding prod_dividef [symmetric]
    using assms pos2 \<open>A > 0\<close> by (intro prod.cong powr_divide) (auto intro: less_imp_le)
  also have "(\<Prod>x\<in>X. A powr w x) = exp ((\<Sum>x\<in>X. w x) * ln A)"
    using \<open>A > 0\<close> and \<open>finite X\<close> by (simp add: powr_def exp_sum sum_distrib_right)
  also have "(\<Sum>x\<in>X. w x) = 1" by fact
  also have "exp (1 * ln A) = A"
    using \<open>A > 0\<close> by simp
  finally have lhs: "(\<Prod>x\<in>X. (1 + r x) powr w x) = (\<Prod>x\<in>X. a x powr w x) / A" .

  have "(\<Prod>x\<in>X. exp (w x * r x)) = exp (\<Sum>x\<in>X. w x * r x)"
    using \<open>finite X\<close> by (simp add: exp_sum)
  also have "(\<Sum>x\<in>X. w x * r x) = (\<Sum>x\<in>X. a x * w x) / A - 1"
    using \<open>A > 0\<close> by (simp add: r_def algebra_simps sum_subtractf sum_divide_distrib sum_weights)
  also have "(\<Sum>x\<in>X. a x * w x) / A = 1"
    using \<open>A > 0\<close> by (simp add: A_def mult.commute)
  finally have rhs: "(\<Prod>x\<in>X. exp (w x * r x)) = 1" by simp

  have "a x = A" if x: "x \<in> X" for x
  proof -
    have "(1 + r x) powr w x = exp (w x * r x)"
    proof (rule prod_ge_pointwise_le_imp_pointwise_eq
             [where f = "\<lambda>x. (1 + r x) powr w x" and g = "\<lambda>x. exp (w x * r x)"])
      show "(1 + r x) powr w x \<le> exp (w x * r x)" if x: "x \<in> X" for x
      proof -
        have "1 + r x \<le> exp (r x)"
          by (rule exp_ge_add_one_self)
        hence "(1 + r x) powr w x \<le> exp (r x) powr w x"
          using nonneg1[of x] nonneg2[of x] x \<open>A > 0\<close>
          by (intro powr_mono2) (auto simp: r_def field_simps)
        also have "\<dots> = exp (w x * r x)"
          by (simp add: powr_def)
        finally show "(1 + r x) powr w x \<le> exp (w x * r x)" .
      qed
    next
      show "(\<Prod>x\<in>X. (1 + r x) powr w x) \<ge> (\<Prod>x\<in>X. exp (w x * r x))"
      proof -
        have "(\<Prod>x\<in>X. (1 + r x) powr w x) = (\<Prod>x\<in>X. a x powr w x) / A"
          by (fact lhs)
        also have "\<dots> = 1"
          using \<open>A \<noteq> 0\<close> by (simp add: eq A_def)
        also have "\<dots> = (\<Prod>x\<in>X. exp (w x * r x))"
          by (simp add: rhs)
        finally show ?thesis by simp
      qed
    qed (use x \<open>finite X\<close> in auto)

    also have "exp (w x * r x) = exp (r x) powr w x"
      by (simp add: powr_def)
    finally have "1 + r x = exp (r x)"
      using x pos2[of x] r_ge[of x] by (subst (asm) powr_left_real_eq_iff) auto
    hence "r x = 0"
      using exp_real_eq_one_plus_iff[of "r x"] by auto
    hence "a x = A"
      using \<open>A > 0\<close> by (simp add: r_def field_simps)
    thus ?thesis
      by (simp add: )
  qed
  thus "\<forall>x\<in>X. \<forall>y\<in>X. a x = a y"
    by auto
qed

text \<open>
  We can now show the full theorem and relax the positivity condition on the $a_i$ to
  non-negativity. This is possible because if some $a_i$ is zero and the two means
  coincide, then the product is obviously 0, but the sum can only be 0 if \<^term>\<open>all\<close>
  the $a_i$ are 0.
\<close>
theorem weighted_arithmetic_geometric_mean_eq_iff:
  fixes a w :: "'a \<Rightarrow> real"
  assumes "finite X"
  assumes nonneg1: "\<And>x. x \<in> X \<Longrightarrow> a x \<ge> 0"
  assumes pos2:    "\<And>x. x \<in> X \<Longrightarrow> w x > 0"
  assumes sum_weights: "(\<Sum>x\<in>X. w x) = 1"
  shows   "(\<Prod>x\<in>X. a x powr w x) = (\<Sum>x\<in>X. w x * a x) \<longleftrightarrow> X \<noteq> {} \<and> (\<forall>x\<in>X. \<forall>y\<in>X. a x = a y)"
proof
  assume *: "X \<noteq> {} \<and> (\<forall>x\<in>X. \<forall>y\<in>X. a x = a y)"
  from * have "X \<noteq> {}"
    by blast

  from * obtain c where c: "\<And>x. x \<in> X \<Longrightarrow> a x = c" "c \<ge> 0"
  proof (cases "X = {}")
    case False
    then obtain x where "x \<in> X" by blast
    thus ?thesis using * that[of "a x"] nonneg1[of x] by metis
  next
    case True
    thus ?thesis
      using that[of 1] by auto
  qed

  have "(\<Prod>x\<in>X. a x powr w x) = (\<Prod>x\<in>X. c powr w x)"
    by (simp add: c)
  also have "\<dots> = c"
    using assms c \<open>X \<noteq> {}\<close> by (cases "c = 0") (auto simp: powr_sum_distrib_real_right)
  also have "\<dots> = (\<Sum>x\<in>X. w x * a x)"
    using sum_weights by (simp add: c(1) flip: sum_distrib_left sum_distrib_right)
  finally show "(\<Prod>x\<in>X. a x powr w x) = (\<Sum>x\<in>X. w x * a x)" .
next
  assume *: "(\<Prod>x\<in>X. a x powr w x) = (\<Sum>x\<in>X. w x * a x)"
  have "X \<noteq> {}"
    using * by auto
  moreover have "(\<forall>x\<in>X. \<forall>y\<in>X. a x = a y)"
  proof (cases "\<exists>x\<in>X. a x = 0")
    case False
    with nonneg1 have pos1: "\<forall>x\<in>X. a x > 0"
      by force
    thus ?thesis
      using weighted_arithmetic_geometric_mean_eq_iff_pos[of X a w] assms *
      by blast
  next
    case True
    hence "(\<Prod>x\<in>X. a x powr w x) = 0"
      using assms by auto
    with * have "(\<Sum>x\<in>X. w x * a x) = 0"
      by auto
    also have "?this \<longleftrightarrow> (\<forall>x\<in>X. w x * a x = 0)"
      using assms by (intro sum_nonneg_eq_0_iff mult_nonneg_nonneg) (auto intro: less_imp_le)
    finally have "(\<forall>x\<in>X. a x = 0)"
      using pos2 by force
    thus ?thesis
      by auto
  qed
  ultimately show "X \<noteq> {} \<and> (\<forall>x\<in>X. \<forall>y\<in>X. a x = a y)"
    by blast
qed

text \<open>
  Again, we derive a version for the unweighted arithmetic/geometric mean.
\<close>
corollary arithmetic_geometric_mean_eq_iff:
  fixes a :: "'a \<Rightarrow> real"
  assumes "finite X"
  defines "n \<equiv> card X"
  assumes nonneg: "\<And>x. x \<in> X \<Longrightarrow> a x \<ge> 0"
  shows   "root n (\<Prod>x\<in>X. a x) = (\<Sum>x\<in>X. a x) / n \<longleftrightarrow> (\<forall>x\<in>X. \<forall>y\<in>X. a x = a y)"
proof (cases "X = {}")
  case False
  with assms have "n > 0"
    by auto
  have "(\<Prod>x\<in>X. a x powr (1 / n)) = (\<Sum>x\<in>X. (1 / n) * a x) \<longleftrightarrow>
          X \<noteq> {} \<and> (\<forall>x\<in>X. \<forall>y\<in>X. a x = a y)"
    using assms False by (intro weighted_arithmetic_geometric_mean_eq_iff) auto
  also have "(\<Prod>x\<in>X. a x powr (1 / n)) = (\<Prod>x\<in>X. a x) powr (1 / n)"
    using nonneg by (subst powr_sum_distrib_real_left) auto
  also have "\<dots> = root n (\<Prod>x\<in>X. a x)"
    using \<open>n > 0\<close> nonneg by (subst root_powr_inverse') (auto simp: prod_nonneg)
  also have "(\<Sum>x\<in>X. (1 / n) * a x) = (\<Sum>x\<in>X. a x) / n"
    by (subst sum_distrib_left [symmetric]) auto
  finally show ?thesis using False by auto
qed (auto simp: n_def)


subsection \<open>The Binary Version\<close>

text \<open>
  For convenience, we also derive versions for only two numbers:
\<close>
corollary weighted_arithmetic_geometric_mean_binary:
  fixes w1 w2 x1 x2 :: real
  assumes "x1 \<ge> 0" "x2 \<ge> 0" "w1 \<ge> 0" "w2 \<ge> 0" "w1 + w2 = 1"
  shows   "x1 powr w1 * x2 powr w2 \<le> w1 * x1 + w2 * x2"
proof -
  let ?a = "\<lambda>b. if b then x1 else x2"
  let ?w = "\<lambda>b. if b then w1 else w2"
  from assms have "(\<Prod>x\<in>UNIV. ?a x powr ?w x) \<le> (\<Sum>x\<in>UNIV. ?w x * ?a x)" 
    by (intro weighted_arithmetic_geometric_mean) (auto simp add: UNIV_bool)
  thus ?thesis by (simp add: UNIV_bool add_ac mult_ac)
qed

corollary weighted_arithmetic_geometric_mean_eq_iff_binary:
  fixes w1 w2 x1 x2 :: real
  assumes "x1 \<ge> 0" "x2 \<ge> 0" "w1 > 0" "w2 > 0" "w1 + w2 = 1"
  shows   "x1 powr w1 * x2 powr w2 = w1 * x1 + w2 * x2 \<longleftrightarrow> x1 = x2"
proof -
  let ?a = "\<lambda>b. if b then x1 else x2"
  let ?w = "\<lambda>b. if b then w1 else w2"
  from assms have "(\<Prod>x\<in>UNIV. ?a x powr ?w x) = (\<Sum>x\<in>UNIV. ?w x * ?a x)
                      \<longleftrightarrow> (UNIV :: bool set) \<noteq> {} \<and> (\<forall>x\<in>UNIV. \<forall>y\<in>UNIV. ?a x = ?a y)" 
    by (intro weighted_arithmetic_geometric_mean_eq_iff) (auto simp add: UNIV_bool)
  thus ?thesis by (auto simp: UNIV_bool add_ac mult_ac)
qed

corollary arithmetic_geometric_mean_binary:
  fixes x1 x2 :: real
  assumes "x1 \<ge> 0" "x2 \<ge> 0"
  shows   "sqrt (x1 * x2) \<le> (x1 + x2) / 2"
  using weighted_arithmetic_geometric_mean_binary[of x1 x2 "1/2" "1/2"] assms
  by (simp add: powr_half_sqrt field_simps real_sqrt_mult)

corollary arithmetic_geometric_mean_eq_iff_binary:
  fixes x1 x2 :: real
  assumes "x1 \<ge> 0" "x2 \<ge> 0"
  shows   "sqrt (x1 * x2) = (x1 + x2) / 2 \<longleftrightarrow> x1 = x2"
  using weighted_arithmetic_geometric_mean_eq_iff_binary[of x1 x2 "1/2" "1/2"] assms
  by (simp add: powr_half_sqrt field_simps real_sqrt_mult)

end