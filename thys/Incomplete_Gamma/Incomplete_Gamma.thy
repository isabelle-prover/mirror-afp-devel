(*
   File:     Incomplete_Gamma.thy
   Author:   Manuel Eberl, University of Innsbruck
*)
section \<open>The Incomplete Gamma Function\<close>
theory Incomplete_Gamma
imports
  "HOL-Complex_Analysis.Complex_Analysis" "HOL-Library.Going_To_Filter"
  Generalized_Hypergeometric_Series.Generalized_Hypergeometric_Series
  Safe_Power More_Beta More_Dominated_Convergence
  Derivative_Method Incomplete_Gamma_Lemma_Bucket
begin

subsection \<open>Construction of the auxiliary entire function\<close>

text \<open>
  For an overview of the functions we will define, see \S8.2 of the NIST Digital Library of 
  Mathematical Functions~\<^cite>\<open>nist\<close>.

  We first use the regularised hypergeometric series to define a version of
  the regularised lower gamma function that is entire in both variables
  and therefore particularly pleasant to handle. The NIST DLMF calls this function 
  $\gamma^{*}(s,z)$.
\<close>

definition pre_Gamma_rincl :: "'a :: Gamma \<Rightarrow> 'a \<Rightarrow> 'a" where
  "pre_Gamma_rincl s z = exp (-z) * reg_hypergeo_F [1] [1+s] z"

lemma pre_Gamma_rincl_complex_of_real: 
  "pre_Gamma_rincl (complex_of_real s) (of_real z) = of_real (pre_Gamma_rincl s z)"
  by (simp add: pre_Gamma_rincl_def complex_of_real_reg_hypergeo_F flip: exp_of_real)

lemma pre_Gamma_rincl_0_left [simp]: "pre_Gamma_rincl 0 z = 1"
  by (simp add: pre_Gamma_rincl_def reg_hypergeo_F_conv_hypergeo_F hypergeo_F_cancel exp_minus)

lemma pre_Gamma_rincl_0_right [simp]: "pre_Gamma_rincl s 0 = rGamma (s + 1)"
  by (simp add: pre_Gamma_rincl_def reg_hypergeo_F_0 add_ac)

lemma pre_Gamma_rincl_1_left: 
  assumes  [simp]: "z \<noteq> 0"
  shows   "pre_Gamma_rincl 1 z = (1 - exp (-z)) / z"
proof -
  have "pre_Gamma_rincl 1 z = exp (-z) * hypergeo_F [1] [2] z"
    by (simp add: pre_Gamma_rincl_def reg_hypergeo_F_conv_hypergeo_F
                  rGamma_inverse_Gamma Gamma_numeral)
  also have "hypergeo_F [1] [2] z = (exp z - 1) / z"
    by (subst hypergeo_F_1_2) auto
  also have "exp (-z) * \<dots> = (1 - exp (-z)) / z"
    by (simp add: field_simps exp_minus)
  finally show ?thesis .
qed

lemma analytic_pre_Gamma_rincl [analytic_intros]:
  assumes [analytic_intros]: "s analytic_on X" "z analytic_on X"
  shows   "(\<lambda>x. pre_Gamma_rincl (s x) (z x)) analytic_on X"
  unfolding pre_Gamma_rincl_def
  by (intro analytic_intros analytic_reg_hypergeo_F[where as = "[\<lambda>_. 1]" and bs = "[\<lambda>x. 1 + s x]"])
     (auto intro!: analytic_intros)

lemma continuous_on_pre_Gamma_rincl [continuous_intros]:
  fixes s z :: "_ \<Rightarrow> 'a :: {Gamma, heine_borel}"
  assumes [continuous_intros]: "continuous_on X s" "continuous_on X z"
  shows   "continuous_on X (\<lambda>x. pre_Gamma_rincl (s x) (z x))"
proof -
  have "continuous_on ((\<lambda>x. (s x, z x)) ` X) (\<lambda>(s,z). pre_Gamma_rincl s z :: 'a)"
    unfolding pre_Gamma_rincl_def case_prod_unfold
    by (intro continuous_intros
              continuous_on_reg_hypergeo_F[where as = "[\<lambda>_. 1]" and bs = "[\<lambda>x. 1 + fst x :: 'a]"])
       (auto intro!: continuous_intros)
  hence "continuous_on X ((\<lambda>(s,z). pre_Gamma_rincl s z) \<circ> (\<lambda>x. (s x, z x)))"
    by (intro continuous_on_compose continuous_intros)
  thus ?thesis
    by (simp add: o_def)
qed

lemma tendsto_pre_Gamma_rincl [tendsto_intros]:
  fixes s z :: "'a :: {Gamma, heine_borel}"
  assumes "(f \<longlongrightarrow> s) F" "(g \<longlongrightarrow> z) F"
  shows   "((\<lambda>x. pre_Gamma_rincl (f x) (g x)) \<longlongrightarrow> pre_Gamma_rincl s z) F"
proof -
  have "continuous_on UNIV (\<lambda>(s,z). pre_Gamma_rincl s z :: 'a)"
    by (auto simp: case_prod_unfold intro!: continuous_intros)
  hence "((\<lambda>x. case (f x, g x) of (s, z) \<Rightarrow> pre_Gamma_rincl s z) \<longlongrightarrow> 
            (case (s, z) of (s, z) \<Rightarrow> pre_Gamma_rincl s z)) F"
    by (rule continuous_on_tendsto_compose) (use assms in \<open>auto intro!: tendsto_intros\<close>)
  thus ?thesis
    by simp
qed

lemma continuous_pre_Gamma_rincl [continuous_intros]:
  fixes s z :: "_ \<Rightarrow> 'a :: {Gamma, heine_borel}"
  assumes [continuous_intros]: "continuous (at x within A) s" "continuous (at x within A) z"
  shows   "continuous (at x within A) (\<lambda>x. pre_Gamma_rincl (s x) (z x))"
  using assms unfolding continuous_def
  by (cases "at x within A = bot") (auto simp: Lim_ident_at intro: tendsto_intros)


lemma sums_pre_Gamma_rincl:
  "(\<lambda>n. exp (-z) * rGamma (s + of_nat n + 1) * z ^ n) sums (pre_Gamma_rincl s z)"
  unfolding pre_Gamma_rincl_def
  using sums_mult[OF sums_reg_hypergeo_F[of "[1]" "[1+s]" z], of "exp (-z)"]
  by (simp flip: pochhammer_fact add: add_ac mult_ac)

lemma erf_conv_pre_Gamma_rincl_complex:
  "erf (z :: complex) = z * pre_Gamma_rincl (1 / 2) (z\<^sup>2)"
proof -
  have [simp]: "1 / (2::complex) \<notin> \<int>\<^sub>\<le>\<^sub>0"
    by force
  have "z * pre_Gamma_rincl (1/2) (z^2) = exp (-z\<^sup>2) * z * reg_hypergeo_F [1] [3/2] (z\<^sup>2)"
    by (simp add: pre_Gamma_rincl_def)
  also have "reg_hypergeo_F [1] [3/2] (z\<^sup>2) = rGamma (3/2) * hypergeo_F [1] [3/2] (z\<^sup>2)"
    by (subst reg_hypergeo_F_conv_hypergeo_F) auto
  also have "\<dots> = 1 / Gamma (1/2 + 1) * exp (z\<^sup>2) * hypergeo_F [1/2] [3/2] (-z\<^sup>2)"
    by (subst hypergeo_F_kummer_transform) (auto simp: rGamma_inverse_Gamma field_simps)
  also have "\<dots> = exp (z\<^sup>2) * (of_real (2 / sqrt pi) * hypergeo_F [1/2] [3/2] (-z\<^sup>2))"
    by (subst Gamma_plus1) (auto simp: Gamma_one_half_complex)
  also have "exp (-z\<^sup>2) * z * (exp (z\<^sup>2) * (of_real (2 / sqrt pi) * hypergeo_F [1 / 2] [3 / 2] (- z\<^sup>2))) =
               of_real (2 / sqrt pi) * z * hypergeo_F [1 / 2] [3 / 2] (- z\<^sup>2)"
    by (simp add: exp_minus)
  also have "\<dots> = erf z"
    by (rule erf_conv_hypergeo_F [symmetric])
  finally show ?thesis ..
qed

lemma erf_conv_pre_Gamma_rincl_real:
  "erf (z :: real) = z * pre_Gamma_rincl (1 / 2) (z\<^sup>2)"
  using erf_conv_pre_Gamma_rincl_complex[of "of_real z"]
        pre_Gamma_rincl_complex_of_real[of "1/2" "z^2"] by (simp add: complex_eq_iff)


subsection \<open>The regularised lower Gamma function\<close>

text \<open>
  We now add the factor $z^s$, which contributes a branch cut, to obtain the regularised
  lower gamma function $P(s,z)$ (again using the NIST DLMF notation).

  This is essentially $\gamma(s,z)/\Gamma(s)$, but with the benefit 
  that it is defined even when $\gamma(s,z)$ and $\Gamma(s)$ are not (i.e.\ when $s$ is a
  non-negative integer).
\<close>
definition Gamma_rincl :: "'a :: {Gamma, ln} \<Rightarrow> 'a \<Rightarrow> 'a" where
  "Gamma_rincl s z = z powr' s * pre_Gamma_rincl s z"

lemma Gamma_rincl_0_left [simp]: "Gamma_rincl 0 z = 1"
  by (simp add: Gamma_rincl_def)

lemma Gamma_rincl_0_right [simp]: "s \<noteq> 0 \<Longrightarrow> Gamma_rincl s 0 = 0"
  by (auto simp: Gamma_rincl_def)

lemma Gamma_rincl_1_left: "Gamma_rincl 1 z = 1 - exp (-z)"
  by (cases "z = 0") (auto simp: Gamma_rincl_def pre_Gamma_rincl_1_left)

lemma Gamma_rincl_complex_of_real:
  assumes "s \<notin> \<int> \<Longrightarrow> 0 \<le> z"
  shows   "Gamma_rincl (complex_of_real s) (of_real z) = of_real (Gamma_rincl s z)"
  unfolding Gamma_rincl_def of_real_mult
  by (subst powr'_complex_of_real) (use assms in \<open>auto simp: pre_Gamma_rincl_complex_of_real\<close>)

text \<open>
  $P(s,z)$ is holomorphic in $s$ and $z$ apart from a branch cut along the negative real axis
  for $z$. Alternatively, if $s$ is a fixed integer, $P(s,z)$ is entire in $z$ if $s \geq 0$ and
  meromorphic with a pole at $z = 0$ if $s < 0$.  
\<close>
lemma analytic_Gamma_rincl [analytic_intros]:
  assumes [analytic_intros]: "s analytic_on X" "z analytic_on X"
  assumes "\<And>x. x \<in> X \<Longrightarrow> z x \<notin> \<real>\<^sub>\<le>\<^sub>0"
  shows   "(\<lambda>x. Gamma_rincl (s x) (z x)) analytic_on X"
  unfolding Gamma_rincl_def using assms(3) by (auto intro!: analytic_intros)

lemma analytic_Gamma_rincl':
  assumes [analytic_intros]: "f analytic_on X"
  assumes "\<And>x. x \<in> X \<Longrightarrow> s \<in> (\<int>\<^sub>\<le>\<^sub>0 - {0}) \<Longrightarrow> f x \<noteq> 0"
  assumes "\<And>x. x \<in> X \<Longrightarrow> s \<notin> \<int> \<Longrightarrow> f x \<notin> \<real>\<^sub>\<le>\<^sub>0"
  shows   "(\<lambda>x. Gamma_rincl s (f x)) analytic_on X"
proof (cases "s \<in> \<int>")
  case False
  thus ?thesis
    using assms(3) by (auto intro!: analytic_intros)
next
  case True
  then obtain n where s: "s = of_int n"
    by (elim Ints_cases)
  show ?thesis
    using assms(2,3) unfolding s Gamma_rincl_def powr'_of_int of_int_in_nonpos_Ints_iff
    by (auto intro!: analytic_intros simp: of_int_in_nonpos_Ints_iff)
qed

text \<open>
  $P(s,z)$ is continuous away from the nonpositive reals. It is additionally also continuous
  at $z = 0$ if $\text{Re}(s) > 0$.
\<close>
lemma continuous_on_Gamma_rincl_complex [continuous_intros]:
  fixes x z :: "'a :: topological_space \<Rightarrow> complex"
  assumes [continuous_intros]: "continuous_on X s" "continuous_on X z"
  assumes "\<And>x. x \<in> X \<Longrightarrow> Re (z x) \<ge> 0 \<or> Im (z x) \<noteq> 0"
  assumes "\<And>x. x \<in> X \<Longrightarrow> z x = 0 \<Longrightarrow> Re (s x) > 0"
  shows   "continuous_on X (\<lambda>x. Gamma_rincl (s x) (z x))"
proof -
  have "continuous_on X (\<lambda>x. z x powr s x * pre_Gamma_rincl (s x) (z x))"
    unfolding Gamma_rincl_def using assms(3-)
    by (intro continuous_intros) auto
  also have "?this \<longleftrightarrow> ?thesis"
  proof (intro continuous_on_cong)
    fix x assume "x \<in> X"
    show "z x powr s x * pre_Gamma_rincl (s x) (z x) = Gamma_rincl (s x) (z x)"
    proof (cases "z x = 0")
      case True
      hence "s x \<noteq> 0"
        using assms(3,4)[OF \<open>x \<in> X\<close>] by auto
      thus ?thesis using True
        by (auto simp: Gamma_rincl_def)
    next
      case False
      thus ?thesis using assms(3,4)[OF \<open>x \<in> X\<close>]
        by (auto simp: Gamma_rincl_def powr'_complex)
    qed
  qed auto
  finally show ?thesis .
qed

lemma continuous_on_Gamma_rincl_real [continuous_intros]:
  fixes x z :: "'a :: topological_space \<Rightarrow> real"
  assumes [continuous_intros]: "continuous_on X s" "continuous_on X z"
  assumes "\<And>x. x \<in> X \<Longrightarrow> z x \<ge> 0"
  assumes "\<And>x. x \<in> X \<Longrightarrow> z x = 0 \<Longrightarrow> s x > 0"
  shows   "continuous_on X (\<lambda>x. Gamma_rincl (s x) (z x))"
proof -
  note [continuous_intros del] = continuous_on_powr
  note [continuous_intros] = continuous_on_powr'
  have "continuous_on X (\<lambda>x. z x powr s x * pre_Gamma_rincl (s x) (z x))"
    unfolding Gamma_rincl_def using assms(3-)
    by (intro continuous_intros) auto
  also have "?this \<longleftrightarrow> ?thesis"
  proof (intro continuous_on_cong)
    fix x assume "x \<in> X"
    show "z x powr s x * pre_Gamma_rincl (s x) (z x) = Gamma_rincl (s x) (z x)"
    proof (cases "z x = 0")
      case True
      hence "s x \<noteq> 0"
        using assms(3,4)[OF \<open>x \<in> X\<close>] by auto
      thus ?thesis using True
        by (auto simp: Gamma_rincl_def)
    next
      case False
      thus ?thesis using assms(3,4)[OF \<open>x \<in> X\<close>]
        by (auto simp: Gamma_rincl_def powr'_real)
    qed
  qed auto
  finally show ?thesis .
qed

lemma tendsto_Gamma_rincl_complex [tendsto_intros]:
  fixes s z :: complex
  assumes "(f \<longlongrightarrow> s) F" "(g \<longlongrightarrow> z) F" "z \<notin> \<real>\<^sub>\<le>\<^sub>0 \<or> (z = 0 \<and> Re s > 0)"
  shows   "((\<lambda>x. Gamma_rincl (f x) (g x)) \<longlongrightarrow> Gamma_rincl s z) F"
  unfolding Gamma_rincl_def using assms by (auto intro!: tendsto_intros)

lemma tendsto_Gamma_rincl_real [tendsto_intros]:
  fixes s z :: real
  assumes "(f \<longlongrightarrow> s) F" "(g \<longlongrightarrow> z) F" "z > 0 \<or> (z = 0 \<and> s > 0)"
  shows   "((\<lambda>x. Gamma_rincl (f x) (g x)) \<longlongrightarrow> Gamma_rincl s z) F"
  unfolding Gamma_rincl_def using assms by (auto intro!: tendsto_intros)

lemma continuous_Gamma_rincl_complex [continuous_intros]:
  fixes s z :: "_ \<Rightarrow> complex"
  assumes "continuous (at x within A) s" "continuous (at x within A) z"
  assumes "z x \<notin> \<real>\<^sub>\<le>\<^sub>0 \<or> (z x = 0 \<and> Re (s x) > 0)"
  shows   "continuous (at x within A) (\<lambda>x. Gamma_rincl (s x) (z x))"
  using assms unfolding continuous_def
  by (cases "at x within A = bot") (auto simp: Lim_ident_at intro: tendsto_intros)

lemma continuous_Gamma_rincl_real [continuous_intros]:
  fixes s z :: "_ \<Rightarrow> real"
  assumes "continuous (at x within A) s" "continuous (at x within A) z"
  assumes "z x > 0 \<or> (z x = 0 \<and> s x > 0)"
  shows   "continuous (at x within A) (\<lambda>x. Gamma_rincl (s x) (z x))"
  using assms unfolding continuous_def
  by (cases "at x within A = bot") (auto simp: Lim_ident_at intro: tendsto_intros)


text \<open>
  Writing $P(s,z)$ as a series:
\<close>
lemma sums_Gamma_rincl:
  "(\<lambda>n. z powr' s * z ^ n * exp (-z) * rGamma (s + of_nat n + 1)) sums (Gamma_rincl s z)"
  using sums_mult[OF sums_pre_Gamma_rincl[of z s], of "z powr' s"]
  by (simp add: mult_ac Gamma_rincl_def)

lemma sums_Gamma_rincl_complex:
  assumes "z \<noteq> 0 \<or> s \<notin> \<int>\<^sub>\<le>\<^sub>0"
  shows   "(\<lambda>n. z powr (s + of_nat n) * exp (-z) * rGamma (s + of_nat n + 1 :: complex))
              sums (Gamma_rincl s z)"
proof -
  have "(\<lambda>n. z powr' s * z ^ n * exp (-z) * rGamma (s + of_nat n + 1)) sums (Gamma_rincl s z)"
    by (rule sums_Gamma_rincl)
  also have "(\<lambda>n. z powr' s * z ^ n * exp (-z) * rGamma (s + of_nat n + 1)) =
             (\<lambda>n. z powr (s + of_nat n) * exp (-z) * rGamma (s + of_nat n + 1))"
    using assms
    by (cases "z = 0"; cases "s = 0")
       (auto simp: fun_eq_iff powr'_complex power_0_left powr_add)
  finally show ?thesis .
qed

lemma sums_Gamma_rincl_real:
  assumes "z > 0 \<or> s \<in> \<int> - \<int>\<^sub>\<le>\<^sub>0"
  shows   "(\<lambda>n. z powr' (s + of_nat n) * exp (-z) * rGamma (s + of_nat n + 1 :: real))
              sums (Gamma_rincl s z)"
proof -
  have "(\<lambda>n. z powr' s * z ^ n * exp (-z) * rGamma (s + of_nat n + 1)) sums (Gamma_rincl s z)"
    by (rule sums_Gamma_rincl)
  also have "(\<lambda>n. z powr' s * z ^ n * exp (-z) * rGamma (s + of_nat n + 1)) =
             (\<lambda>n. z powr' (s + of_nat n) * exp (-z) * rGamma (s + of_nat n + 1))"
  proof
    fix n :: nat
    show "z powr' s * z ^ n * exp (-z) * rGamma (s + of_nat n + 1) =
          z powr' (s + of_nat n) * exp (-z) * rGamma (s + of_nat n + 1)"
    proof (cases "s \<in> \<int>")
      case True
      then obtain m where s: "s = of_int m"
        by (elim Ints_cases)
      have *: "s + of_nat n = of_int (m + int n)"
        using s by simp
      have "z powr' (s + of_nat n) = z powi (m + int n)"
        by (subst *, subst powr'_of_int) auto
      also have "\<dots> = z powi m * z ^ n"
        by (subst power_int_add) (use assms s in \<open>auto simp: of_int_in_nonpos_Ints_iff\<close>)
      finally show ?thesis
        by (simp add: s)
    next
      case False
      with assms have "z > 0"
        by blast
      thus ?thesis
        using assms False
        by (auto simp: powr'_def powr_add powr_realpow)
    qed
  qed
  finally show ?thesis .
qed


text \<open>
  The recurrence relation for $P(s,z)$:
\<close>
lemma Gamma_rincl_plus1_complex:
  assumes "s \<noteq> -1"
  shows   "Gamma_rincl (s+1) z = Gamma_rincl s z - z powr' s * exp (-z) * rGamma (s+1 :: complex)"
proof (cases "z = 0")
  case [simp]: True
  show ?thesis
    by (cases "s = 0"; cases "s + 1 = 0"; use assms in \<open>auto simp: add_eq_0_iff2\<close>)
next
  case [simp]: False
  let ?f = "(\<lambda>n. z powr (s + of_nat n) * exp (-z) * rGamma (s + of_nat n + 1))"
  have "(\<lambda>n. ?f (Suc n)) sums (Gamma_rincl (s+1) z)"
    using sums_Gamma_rincl_complex[of z "s + 1"] by (simp add: add_ac)
  hence "?f sums (Gamma_rincl (s+1) z + ?f 0)"
    by (rule sums_Suc)
  moreover have "?f sums (Gamma_rincl s z)"
    by (rule sums_Gamma_rincl_complex) auto
  ultimately have "Gamma_rincl (s+1) z + ?f 0 = Gamma_rincl s z"
    by (rule sums_unique2)
  thus ?thesis
    by (simp add: algebra_simps powr'_complex)
qed

lemma Gamma_rincl_plus1_real:
  assumes "z \<ge> 0 \<or> s \<in> \<int>" "s \<noteq> -1"
  shows   "Gamma_rincl (s+1) z = Gamma_rincl s z - z powr' s * exp (-z) * rGamma (s+1 :: real)"
proof (cases "z = 0")
  case [simp]: False
  have *: "complex_of_real s = -1 \<longleftrightarrow> s = -1"
    by (auto simp: complex_eq_iff)
  have "complex_of_real (Gamma_rincl (s+1) z) = Gamma_rincl (of_real s + 1) (of_real z)"
    by (subst Gamma_rincl_complex_of_real [symmetric]) (use assms(1) in auto)
  also have "\<dots> = Gamma_rincl (of_real s) (of_real z) - 
                    of_real z powr' of_real s * exp (-of_real z) *  rGamma (of_real s + 1)"
    by (subst Gamma_rincl_plus1_complex) (use assms in \<open>auto simp: *\<close>)
  also have "\<dots> = complex_of_real (Gamma_rincl s z - z powr' s * exp (-z) * rGamma (s+1))"
    unfolding of_real_diff
    by (subst Gamma_rincl_complex_of_real)
       (use assms in \<open>auto simp flip: exp_of_real rGamma_complex_of_real simp: powr'_complex_of_real\<close>)
  finally show ?thesis
    by (simp only: of_real_eq_iff)
qed (cases "s = 0"; use assms in auto)


text \<open>
  We can now also easily show a closed form for the case where $s$ is a positive integer:
\<close>
lemma Gamma_rincl_of_nat_left_complex:
  fixes z :: complex
  shows "Gamma_rincl (of_nat (Suc n)) z = 1 - exp (-z) * (\<Sum>k\<le>n. z ^ k / fact k)"
proof (induction n)
  case 0
  thus ?case by (simp add: Gamma_rincl_1_left)
next
  case (Suc n)
  have "of_nat (Suc n) \<noteq> (-1::complex)"
    by (auto simp: complex_eq_iff)
  hence "Gamma_rincl (of_nat (Suc (Suc n))) z = 
           1 - exp (-z) * (\<Sum>k\<le>n. z ^ k / fact k) - 
           z powr' of_nat (Suc n) * exp (-z) * rGamma (of_int (int n + 2))"
    using Gamma_rincl_plus1_complex[of "of_nat (Suc n)" z] Suc.IH by (simp add: add_ac)
  also have "z powr' of_nat (Suc n) = z powr of_nat (Suc n)"
    by (subst powr'_complex) (auto simp: complex_eq_iff)
  also have "\<dots> = z ^ Suc n"
    by (subst powr_nat) auto
  also have "rGamma (of_int (int n + 2) :: complex) = 1 / fact (Suc n)"
    by (subst rGamma_of_int) (auto simp: nat_add_distrib divide_simps)
  also have "1 - exp (- z) * (\<Sum>k\<le>n. z ^ k / fact k) - z ^ Suc n * exp (- z) * (1 / fact (Suc n)) =
             1 - exp (- z) * (\<Sum>k\<in>insert (Suc n) {..n}. z ^ k / fact k)"
    by (subst sum.insert) (auto simp: field_simps simp del: fact_Suc)
  also have "insert (Suc n) {..n} = {..Suc n}"
    by auto
  finally show ?case .
qed

lemma Gamma_rincl_of_nat_left_real:
  fixes z :: real
  shows "Gamma_rincl (of_nat (Suc n)) z = 1 - exp (-z) * (\<Sum>k\<le>n. z ^ k / fact k)"
proof -
  have "Gamma_rincl (of_nat (Suc n)) z = Gamma_rincl (of_nat (Suc n)) (complex_of_real z)"
    using Gamma_rincl_complex_of_real[of "of_nat (Suc n)" z] by simp
  also have "\<dots> = of_real (1 - exp (-z) * (\<Sum>k\<le>n. z ^ k / fact k))"
    by (subst Gamma_rincl_of_nat_left_complex) (simp_all flip: exp_of_real)
  finally show ?thesis
    by (simp only: of_real_eq_iff)
qed
  

text \<open>
  Lastly, when $s = \frac{1}{2}$, the reduced lower incomplete Gamma function is related to
  the error function (via their hypergeometric representations):
\<close>

lemma erf_conv_Gamma_rincl_real: "erf z = sgn z * Gamma_rincl (1/2) (z ^ 2 :: real)"
proof -
  have "Gamma_rincl (1/2) (z ^ 2) = sgn z * (z * pre_Gamma_rincl (1 / 2) (z\<^sup>2))"
    by (simp add: Gamma_rincl_def powr'_real sgn_if)
  also have "\<dots> = sgn z * erf z"
    by (subst erf_conv_pre_Gamma_rincl_real [symmetric]) auto
  finally show ?thesis by (auto simp: sgn_if)
qed

lemma Gamma_rincl_one_half_left_real:
  assumes "z \<ge> 0"
  shows   "Gamma_rincl (1/2) (z :: real) = erf (sqrt z)"
  using assms by (subst erf_conv_Gamma_rincl_real) (auto simp: sgn_if)

lemma Gamma_rincl_one_half_left_complex:
  assumes z: "z \<notin> \<real>\<^sub>\<le>\<^sub>0"
  shows "Gamma_rincl (1/2) (z :: complex) = erf (csqrt z)"
proof -
  have "Gamma_rincl (1/2) z - erf (csqrt z) = 0"
  proof (rule analytic_continuation[of "\<lambda>z. Gamma_rincl (1/2) z - erf (csqrt z)"])
    show "complex_of_real 1 islimpt of_real ` {0<..}"
      by (intro islimpt_isCont_image continuous_intros open_imp_islimpt)
         (auto simp: eventually_at_topological)
  next
    show "(\<lambda>z. Gamma_rincl (1 / 2) z - erf (csqrt z)) holomorphic_on (-\<real>\<^sub>\<le>\<^sub>0)"
      by (auto intro!: analytic_imp_holomorphic analytic_intros)
  next
    have "connected (-complex_of_real ` {..0})"
      by (intro starlike_imp_connected starlike_slotted_complex_plane_left)
    also have "(-complex_of_real ` {..0}) = -\<real>\<^sub>\<le>\<^sub>0"
      by (auto simp: nonpos_Reals_def)
    finally show "connected (-\<real>\<^sub>\<le>\<^sub>0 :: complex set)" .
  next
    show "Gamma_rincl (1/2) z - erf (csqrt z) = 0" if "z \<in> complex_of_real ` {0<..}" for z
    proof -
      from that obtain x where [simp]: "z = of_real x" and x: "x > 0"
        by auto
      have "Gamma_rincl (1/2) z - erf (csqrt z) = of_real (Gamma_rincl (1/2) x - erf (sqrt x))"
        using x by (simp flip: Gamma_rincl_complex_of_real)
      also have "\<dots> = 0"
        by (subst Gamma_rincl_one_half_left_real) (use x in auto)
      finally show ?thesis
        by simp
    qed
  qed (use assms in auto)
  thus ?thesis
    by simp
qed


subsection \<open>The lower incomplete Gamma function\<close>

definition Gamma_incl :: "'a :: {Gamma, ln} \<Rightarrow> 'a \<Rightarrow> 'a" where
  "Gamma_incl s z = Gamma s * Gamma_rincl s z"

lemma Gamma_incl_complex_of_real: 
  assumes "s \<notin> \<int> \<Longrightarrow> 0 \<le> z"
  shows   "Gamma_incl (complex_of_real s) (of_real z) = of_real (Gamma_incl s z)"
  unfolding Gamma_incl_def of_real_mult
  by (subst Gamma_rincl_complex_of_real)
     (use assms in \<open>auto simp: Gamma_complex_of_real Gamma_rincl_complex_of_real\<close>)

text \<open>
  The lower incomplete Gamma function $\gamma(s,z)$ is analytic away from $z \leq 0$ and
  $s \in \{0, -1, -2, \ldots\}$.
\<close>
lemma analytic_Gamma_incl [analytic_intros]:
  assumes [analytic_intros]: "s analytic_on X" "z analytic_on X"
  assumes "\<And>x. x \<in> X \<Longrightarrow> z x \<notin> \<real>\<^sub>\<le>\<^sub>0" "\<And>x. x \<in> X \<Longrightarrow> s x \<notin> \<int>\<^sub>\<le>\<^sub>0"
  shows   "(\<lambda>x. Gamma_incl (s x) (z x)) analytic_on X"
  unfolding Gamma_incl_def using assms(3,4) by (auto intro!: analytic_intros)

text \<open>
  When $s$ is a positive integer, $\gamma(s,z)$ is entire in $z$.
\<close>
lemma analytic_Gamma_incl_nonneg_int [analytic_intros]:
  assumes [analytic_intros]: "z analytic_on X" and "n \<ge> 0"
  shows   "(\<lambda>x. Gamma_incl (of_int n) (z x)) analytic_on X"
proof -
  note [analytic_intros del] = analytic_Gamma_rincl
  show ?thesis
    unfolding Gamma_incl_def using \<open>n \<ge> 0\<close>
    by (intro analytic_intros analytic_Gamma_rincl') (auto simp: of_int_in_nonpos_Ints_iff)
qed

lemma analytic_Gamma_incl':
  assumes [analytic_intros]: "f analytic_on X"
  assumes "\<And>x. x \<in> X \<Longrightarrow> s \<in> \<int>\<^sub>\<le>\<^sub>0 \<Longrightarrow> f x \<noteq> 0"
  assumes "\<And>x. x \<in> X \<Longrightarrow> s \<notin> \<int> \<Longrightarrow> f x \<notin> \<real>\<^sub>\<le>\<^sub>0"
  shows   "(\<lambda>x. Gamma_incl s (f x)) analytic_on X"
proof -
  note [analytic_intros del] = analytic_Gamma_rincl
  note [analytic_intros] = analytic_Gamma_rincl'
  show ?thesis
    unfolding Gamma_incl_def using assms
    by (auto intro!: analytic_intros)
qed

lemma continuous_on_Gamma_incl_complex [continuous_intros]:
  fixes x z :: "'a :: topological_space \<Rightarrow> complex"
  assumes [continuous_intros]: "continuous_on X s" "continuous_on X z"
  assumes "\<And>x. x \<in> X \<Longrightarrow> Re (z x) \<ge> 0 \<or> Im (z x) \<noteq> 0"
  assumes "\<And>x. x \<in> X \<Longrightarrow> z x = 0 \<Longrightarrow> Re (s x) > 0"
  assumes "\<And>x. x \<in> X \<Longrightarrow> s x \<notin> \<int>\<^sub>\<le>\<^sub>0"
  shows   "continuous_on X (\<lambda>x. Gamma_incl (s x) (z x))"
  unfolding Gamma_incl_def
  using assms by (auto intro!: continuous_intros)

lemma continuous_on_Gamma_incl_real [continuous_intros]:
  fixes x z :: "'a :: topological_space \<Rightarrow> real"
  assumes [continuous_intros]: "continuous_on X s" "continuous_on X z"
  assumes "\<And>x. x \<in> X \<Longrightarrow> z x \<ge> 0"
  assumes "\<And>x. x \<in> X \<Longrightarrow> z x = 0 \<Longrightarrow> s x > 0"
  assumes "\<And>x. x \<in> X \<Longrightarrow> s x \<notin> \<int>\<^sub>\<le>\<^sub>0"
  shows   "continuous_on X (\<lambda>x. Gamma_incl (s x) (z x))"
  unfolding Gamma_incl_def
  using assms by (auto intro!: continuous_intros)

lemma tendsto_Gamma_incl_complex [tendsto_intros]:
  fixes s z :: complex
  assumes "(f \<longlongrightarrow> s) F" "(g \<longlongrightarrow> z) F"
  assumes "Re z \<ge> 0 \<or> Im z \<noteq> 0" "z = 0 \<Longrightarrow> Re s > 0" "s \<notin> \<int>\<^sub>\<le>\<^sub>0"
  shows   "((\<lambda>x. Gamma_incl (f x) (g x)) \<longlongrightarrow> Gamma_incl s z) F"
  thm Gamma_incl_def
  unfolding Gamma_incl_def using assms 
  by (auto intro!: tendsto_intros simp: complex_nonpos_Reals_iff complex_eq_iff)

lemma tendsto_Gamma_incl_real [tendsto_intros]:
  fixes s z :: real
  assumes "(f \<longlongrightarrow> s) F" "(g \<longlongrightarrow> z) F" "z \<ge> 0" "z = 0 \<Longrightarrow> s > 0" "s \<notin> \<int>\<^sub>\<le>\<^sub>0"
  shows   "((\<lambda>x. Gamma_incl (f x) (g x)) \<longlongrightarrow> Gamma_incl s z) F"
  unfolding Gamma_incl_def using assms by (auto intro!: tendsto_intros)

lemma continuous_Gamma_incl_complex [continuous_intros]:
  fixes s z :: "_ \<Rightarrow> complex"
  assumes "continuous (at x within A) s" "continuous (at x within A) z"
  assumes "Re (z x) \<ge> 0 \<or> Im (z x) \<noteq> 0" "z x = 0 \<Longrightarrow> Re (s x) > 0" "s x \<notin> \<int>\<^sub>\<le>\<^sub>0"
  shows   "continuous (at x within A) (\<lambda>x. Gamma_incl (s x) (z x))"
  using assms unfolding continuous_def
  by (cases "at x within A = bot") (auto simp: Lim_ident_at intro: tendsto_intros)

lemma continuous_Gamma_incl_real [continuous_intros]:
  fixes s z :: "_ \<Rightarrow> real"
  assumes "continuous (at x within A) s" "continuous (at x within A) z"
  assumes "z x \<ge> 0" "z x = 0 \<Longrightarrow> s x > 0" "s x \<notin> \<int>\<^sub>\<le>\<^sub>0"
  shows   "continuous (at x within A) (\<lambda>x. Gamma_incl (s x) (z x))"
  using assms unfolding continuous_def
  by (cases "at x within A = bot") (auto simp: Lim_ident_at intro: tendsto_intros)


text \<open>
  $\gamma(s,z)$ as a series:
\<close>
lemma sums_Gamma_incl:
  "(\<lambda>n. z powr' s * z ^ n * exp (-z) * Gamma s * rGamma (s + of_nat n + 1)) sums (Gamma_incl s z)"
  using sums_mult[OF sums_Gamma_rincl[of z s], of "Gamma s"]
  by (simp add: mult_ac Gamma_incl_def)

lemma sums_Gamma_incl_complex:
  "(\<lambda>n. z powr (s + complex_of_nat n) * exp (-z) * Gamma s * rGamma (s + of_nat n + 1))
      sums (Gamma_incl s z)"
  using sums_Gamma_incl[of z s]
  by (cases "z = 0"; cases "s = 0") (auto simp: powr'_complex powr_add)

lemma sums_Gamma_incl_real_nonneg:
  assumes "z \<ge> 0"
  shows   "(\<lambda>n. z powr (s + real n) * exp (-z) * Gamma s * rGamma (s + of_nat n + 1)) 
             sums (Gamma_incl s z)"
  using sums_Gamma_incl[of z s] assms
  by (cases "z = 0"; cases "s = 0") (auto simp: powr'_real powr_add powr_realpow)


text \<open>
  The recurrence for $\gamma(s,z)$:
\<close>
lemma Gamma_incl_plus1_complex:
  assumes "s \<notin> \<int>\<^sub>\<le>\<^sub>0"
  shows   "Gamma_incl (s+1) z = s * Gamma_incl s z - z powr' s * exp (-z :: complex)"
proof -
  from assms have "Gamma s \<noteq> 0"
    by (auto simp: Gamma_eq_zero_iff)
  hence "Gamma_incl (s+1) z = s * Gamma_incl s z - z powr' s * exp (-z)"
    unfolding Gamma_incl_def using rGamma_plus1[of s]
    by (subst Gamma_rincl_plus1_complex)
       (use assms in \<open>auto simp: rGamma_inverse_Gamma field_simps\<close>)
  thus ?thesis .
qed

lemma Gamma_incl_plus1_real:
  assumes "s \<in> \<int> \<or> z \<ge> 0" "s \<notin> \<int>\<^sub>\<le>\<^sub>0"
  shows   "Gamma_incl (s+1) z = s * Gamma_incl s z - z powr' s * exp (-z :: real)"
proof -
  from assms have "Gamma s \<noteq> 0"
    by (auto simp: Gamma_eq_zero_iff)
  hence "Gamma_incl (s+1) z = s * Gamma_incl s z - z powr' s * exp (-z)"
    unfolding Gamma_incl_def using rGamma_plus1[of s]
    by (subst Gamma_rincl_plus1_real)
       (use assms in \<open>auto simp: rGamma_inverse_Gamma field_simps\<close>)
  thus ?thesis .
qed


text \<open>
  For $\text{Re}(s) > 0$, $\Gamma(s,z)$ has a representation as a contour integral.
\<close>
theorem has_contour_integral_Gamma_incl:
  fixes s z :: complex
  assumes s: "Re s > 0"
  shows   "((\<lambda>u. u powr (s-1) * exp (-u)) has_contour_integral Gamma_incl s z) (linepath 0 z)"
proof (cases "z = 0")
  case [simp]: True
  from assms have "s \<noteq> 0"
    by auto
  thus ?thesis
    by (simp add: Gamma_incl_def)
next
  case [simp]: False
  define f where "f = (\<lambda>k t. z^k / fact k * of_real t powr (s-1) * (1-t)^k)"
  from s have [simp]: "s \<notin> \<int>\<^sub>\<le>\<^sub>0"
    by (auto elim!: nonpos_Ints_cases)

  have sums: "(\<lambda>k. z^k * Gamma s / Gamma (s + of_nat (Suc k))) sums 
                     ((z powr (-s) * exp z) * Gamma_incl s z)" 
    using sums_mult[OF sums_Gamma_incl[of z s], of "z powr (-s) * exp z"]
    by (simp add: powr_minus field_simps powr'_complex exp_minus rGamma_inverse_Gamma)

  have 1: "set_integrable lborel {0..1} (f k)" for k
  proof -
    have "set_integrable lebesgue {0<..<1} 
            (\<lambda>t. z ^ k / fact k * (of_real t powr (s - 1) * of_real (1 - t) powr (of_nat (Suc k) - 1)))"
      by (intro set_integrable_mult_right has_integral_Beta_complex) (use s in auto)
    also have "?this \<longleftrightarrow> f k absolutely_integrable_on {0<..<1}"
      by (intro set_integrable_cong) (auto simp: f_def powr_nat)
    also have "\<dots> \<longleftrightarrow> set_integrable lborel {0..1} (f k)"
      unfolding absolutely_integrable_on_Icc_iff_Ioo [symmetric] unfolding set_integrable_def
      by (subst integrable_completion) (auto simp: f_def)
    finally show ?thesis .
  qed

  have 2: "AE t\<in>{0..1} in lborel. summable (\<lambda>k. norm (f k t))"
  proof -
    have *: "summable (\<lambda>k. norm (f k t))" if t: "t \<in> {0<..<1}" for t
    proof -
      have "summable (\<lambda>k. t powr (Re s - 1) * (inverse (fact k) * (norm z * (1 - t)) ^ k))"
        by (intro summable_mult summable_exp)
      also have "(\<lambda>k. t powr (Re s - 1) * (inverse (fact k) * (norm z * (1 - t)) ^ k)) = 
                 (\<lambda>k. norm (f k t))"
        using t by (simp add: f_def norm_mult norm_divide norm_power norm_powr_complex 
                              divide_simps mult_ac flip: of_real_diff)
      finally show ?thesis .
    qed
    have "AE t in lborel. t \<noteq> 0 \<and> t \<noteq> (1::real)"
      by (simp add: AE_lborel_singleton)
    thus ?thesis
      by eventually_elim (use * in auto)
  qed

  have 3: "summable (\<lambda>k. LBINT t:{0..1}. norm (f k t))"
  proof (rule summable_comparison_test')
    show "summable (\<lambda>k. Beta (Re s) 1 * (inverse (fact k) * norm z ^ k))"
      by (intro summable_mult summable_exp)
  next
    fix k :: nat assume "k \<ge> 0"
    have "(LBINT t:{0..1}. norm (f k t)) = 
            (LBINT t:{0..1}. (norm z ^ k / fact k) * 
              (of_real t powr (Re s - 1) * of_real (1 - t) powr (of_nat k)))"
      (is "set_lebesgue_integral _ _ ?lhs = set_lebesgue_integral _ _ ?rhs")
    proof (rule set_lebesgue_integral_cong_AE)
      have "AE t in lborel. t \<noteq> (1::real)"
        by (simp add: AE_lborel_singleton)
      thus "AE t\<in>{0..1} in lborel. ?lhs t = ?rhs t"
      proof eventually_elim
        case (elim t)
        thus ?case
          by (auto simp: f_def norm_mult norm_divide norm_powr_complex norm_power powr_realpow
                   simp flip: of_real_diff)
      qed
    qed (auto simp: f_def)
    also have "\<dots> = (norm z ^ k / fact k) * 
             (LBINT t:{0..1}. of_real t powr (Re s - 1) * of_real (1-t) powr (of_nat k))"
      by (rule set_integral_mult_right)
    also have "(LBINT t:{0..1}. of_real t powr (Re s - 1) * of_real (1-t) powr (of_nat k)) = 
                 set_lebesgue_integral lebesgue {0..1} 
                      (\<lambda>t. of_real t powr (Re s - 1) * of_real (1-t) powr (of_nat k))"
      unfolding set_lebesgue_integral_def by (subst integral_completion) auto
    also have "\<dots> = integral {0..1} (\<lambda>t. of_real t powr (Re s - 1) * of_real (1-t) powr (of_nat k))"
      using integrable_Beta'[of "Re s" "of_nat (Suc k)"] s
      by (intro set_lebesgue_integral_eq_integral(2) nonnegative_absolutely_integrable_1) simp_all
    also have "\<dots> = Beta (Re s) (real k + 1)"
      using has_integral_Beta_real[of "Re s" "of_nat (Suc k)"] s
      by (simp add: has_integral_iff add_ac)
    also have "norm z ^ k / fact k * Beta (Re s) (real k + 1) \<le>
               norm z ^ k / fact k * Beta (Re s) 1"
      by (intro mult_left_mono Beta_real_mono) (use s in auto)
    also have "\<dots> = Beta (Re s) 1 * (inverse (fact k) * norm z ^ k)"
      by (simp add: field_simps)
    finally have "(LBINT t:{0..1}. norm (f k t)) \<le> Beta (Re s) 1 * (inverse (fact k) * norm z ^ k)" .
    moreover have "(LBINT t:{0..1}. norm (f k t)) \<ge> 0"
      unfolding set_lebesgue_integral_def by (rule Bochner_Integration.integral_nonneg) auto
    ultimately show "norm (LBINT t:{0..1}. norm (f k t)) \<le> 
                       Beta (Re s) 1 * (inverse (fact k) * norm z ^ k)"
      by simp
  qed

  have sum_eq: "(\<Sum>k. f k t) = of_real t powr (s-1) * exp (z*(1-t))" for t
  proof -
    have "(\<lambda>k. of_real t powr (s - 1) * (((1 - t) * z) ^ k /\<^sub>R fact k)) sums
            (of_real t powr (s - 1) * exp ((1-t)*z))"
      by (intro sums_mult exp_converges)
    also have "(\<lambda>k. of_real t powr (s - 1) * (((1 - t) * z) ^ k /\<^sub>R fact k)) = (\<lambda>k. f k t)"
      by (auto simp: f_def divide_simps scaleR_conv_of_real)
    finally show ?thesis
      by (simp add: sums_iff mult_ac)
  qed

  have integrable':
    "(\<lambda>t. of_real t powr (s - 1) * exp (z * of_real (1 - t))) absolutely_integrable_on {0..1}"
  proof -
    have "set_integrable lborel {0..1} (\<lambda>k. \<Sum>i. f i k)"
      using set_integrable_suminf[OF 1 2 3] by simp
    also have "?this \<longleftrightarrow> set_integrable lborel {0..1} (\<lambda>t. of_real t powr (s-1) * exp (z*(1-t)))"
      by (intro set_integrable_cong sum_eq refl)
    finally show ?thesis 
      unfolding set_integrable_def by (subst integrable_completion) auto
  qed

  have integrand_eq: "of_real t powr (s - 1) * exp (- (z * of_real t)) =
                      z powr -s * (t *\<^sub>R z) powr (s - 1) * exp (- (t *\<^sub>R z)) * z" 
    if t: "t \<in> {0..1}" for t
    using powr_times_real_left[of t z "s - 1"] t
    by (auto simp: scaleR_conv_of_real powr_diff powr_minus field_simps)    

  have "(\<lambda>t. of_real t powr (s - 1) * exp (z * of_real (1 - t))) integrable_on {0..1}"
    using integrable' by (rule set_lebesgue_integral_eq_integral(1))
  hence "(\<lambda>t. z powr s * exp (-z) * (of_real t powr (s - 1) * exp (z * of_real (1 - t)))) integrable_on {0..1}"
    by (rule integrable_on_mult_right)
  also have "?this \<longleftrightarrow> (\<lambda>z. z powr (s-1) * exp (-z)) contour_integrable_on linepath 0 z"
    unfolding contour_integrable_on
  proof (rule integrable_cong, goal_cases)
    case (1 t)
    thus ?case
      using integrand_eq[of t]
      by (auto simp: scaleR_conv_of_real field_simps powr_minus exp_diff exp_minus)
  qed
  finally have contour_integrable:
    "(\<lambda>z. z powr (s-1) * exp (-z)) contour_integrable_on linepath 0 z" .

  have "(\<Sum>k. LBINT t:{0..1}. f k t) = (LBINT t:{0..1}. \<Sum>k. f k t)"
    using 1 2 3 by (rule set_integral_suminf [symmetric])
  also have "(\<lambda>k. LBINT t:{0..1}. f k t) = (\<lambda>k. z^k * Gamma s / Gamma (s + of_nat (Suc k)))"
  proof
    fix k :: nat
    have "(\<lambda>t. of_real t powr (s-1) * of_real (1-t) powr of_nat k) absolutely_integrable_on {0<..<1}"
      using has_integral_Beta_complex[of s "of_nat (Suc k)"] s by simp
    also have "?this \<longleftrightarrow> (\<lambda>t. of_real t powr (s-1) * of_real (1-t) ^ k) absolutely_integrable_on {0<..<1}"
      by (intro set_integrable_cong) auto
    finally have integrable: 
      "(\<lambda>t. of_real t powr (s-1) * of_real (1-t) ^ k) absolutely_integrable_on {0<..<1}" .
    have *: "1 + complex_of_nat k \<notin> \<int>\<^sub>\<le>\<^sub>0"
      by (auto elim!: nonpos_Ints_cases simp: complex_eq_iff)

    have "(LBINT t:{0..1}. f k t) = 
            z ^ k / fact k * (LBINT t:{0..1}. of_real t powr (s - 1) * of_real (1 - t) ^ k)"
      by (simp add: f_def mult_ac flip: set_integral_mult_right set_integral_mult_left)
    also have "(LBINT t:{0..1}. of_real t powr (s - 1) * of_real (1 - t) ^ k) =
               set_lebesgue_integral lebesgue {0..1} (\<lambda>t. of_real t powr (s - 1) * of_real (1 - t) ^ k)"
      unfolding set_lebesgue_integral_def by (rule integral_completion [symmetric]) auto
    also have "\<dots> = integral {0..1} (\<lambda>t. of_real t powr (s-1) * of_real (1-t) ^ k)"
      using integrable
      by (intro set_lebesgue_integral_eq_integral(2) nonnegative_absolutely_integrable_1)
         (simp_all add: absolutely_integrable_on_Icc_iff_Ioo)
    also have "\<dots> = integral {0<..<1} (\<lambda>t. of_real t powr (s-1) * of_real (1-t) ^ k)"
      by (simp add: integral_open_interval_real)
    also have "\<dots> = integral {0<..<1} (\<lambda>t. of_real t powr (s-1) * of_real (1-t) powr of_nat k)"
      by (intro integral_cong) auto
    also have "\<dots> = Beta s (of_nat (Suc k))"
      using has_integral_Beta_complex[of s "of_nat (Suc k)"] s by (simp add: has_integral_iff)
    also have "z ^ k / fact k * Beta s (of_nat (Suc k)) = z ^ k * Gamma s / Gamma (s + of_nat (Suc k))"
      using * by (auto simp: Beta_def add_ac Gamma_eq_zero_iff simp flip: Gamma_fact)
    finally show "(LBINT t:{0..1}. f k t) = z^k * Gamma s / Gamma (s + of_nat (Suc k))" .
  qed
  also have "(\<Sum>k. z^k * Gamma s / Gamma (s + of_nat (Suc k))) = 
               z powr (-s) * exp z * Gamma_incl s z"
    using sums by (simp add: sums_iff)
  also have "(LBINT t:{0..1}. \<Sum>k. f k t) = (LBINT t:{0..1}. of_real t powr (s-1) * exp (z*(1-t)))"
    by (intro set_lebesgue_integral_cong) (use sum_eq in auto)
  also have "\<dots> = set_lebesgue_integral lebesgue {0..1} (\<lambda>t. of_real t powr (s-1) * exp (z*(1-t)))"
    unfolding set_lebesgue_integral_def by (rule integral_completion [symmetric]) auto
  also have "\<dots> = integral {0..1} (\<lambda>t. of_real t powr (s-1) * exp (z*(1-t)))"
    using integrable' by (rule set_lebesgue_integral_eq_integral(2))
  also have "\<dots> = exp z * integral {0..1} (\<lambda>t. of_real t powr (s-1) * exp (-z*t))"
    by (simp add: exp_diff ring_distribs exp_minus field_simps 
             flip: integral_mult_right set_integral_mult_left)
  also have "integral {0..1} (\<lambda>t. of_real t powr (s-1) * exp (-z*t)) = 
             contour_integral (linepath 0 z) (\<lambda>u. z powr (-s) * u powr (s-1) * exp (-u))"
    unfolding contour_integral_integral
  proof (rule integral_cong, goal_cases)
    case (1 t)
    thus ?case using integrand_eq[of t] by simp
  qed
  also have "\<dots> = z powr (-s) * contour_integral (linepath 0 z) (\<lambda>u. u powr (s-1) * exp (-u))"
    by (simp flip: integral_mult_right integral_mult_left add: mult_ac contour_integral_integral)
  finally have "Gamma_incl s z = contour_integral (linepath 0 z) (\<lambda>u. u powr (s-1) * exp (-u))"
    by simp

  thus "((\<lambda>u. u powr (s-1) * exp (-u)) has_contour_integral Gamma_incl s z) (linepath 0 z)"
    using has_contour_integral_integral[OF contour_integrable] by simp
qed

lemma has_integral_Gamma_incl_complex_of_real:
  assumes s: "Re s > (0::real)"
  assumes "x \<ge> 0"
  shows "((\<lambda>t. of_real t powr (s - 1) * of_real (exp (-t))) 
           has_integral Gamma_incl s (of_real x)) {0..x}"
proof (cases "x = 0")
  case True
  have [simp]: "s \<noteq> 0"
    using s by auto
  have "((\<lambda>t. of_real t powr (s - 1) * of_real (exp (-t))) has_integral 0) {0}"
    by (rule has_integral_refl)
  thus ?thesis using True 
    by (simp add: Gamma_incl_def)
next
  case False
  with assms have x: "x > 0"
    by auto
  have "((\<lambda>t. t powr (s - 1) * exp (-t)) has_contour_integral Gamma_incl s (of_real x)) 
          (linepath 0 (of_real x))"
    by (rule has_contour_integral_Gamma_incl) (use \<open>x > 0\<close> s in auto)
  thus ?thesis using x
    by (simp add: has_contour_integral_linepath_Reals_iff exp_of_real flip: of_real_minus)
qed

lemma has_integral_Gamma_incl_complex_of_real':
  assumes s: "Re s > (0::real)"
  assumes "x \<le> 0"
  shows "((\<lambda>t. of_real t powr (s - 1) * of_real (exp (-t))) 
           has_integral (-Gamma_incl s (of_real x))) {x..0}"
proof (cases "x = 0")
  case True
  have [simp]: "s \<noteq> 0"
    using s by auto
  have "((\<lambda>t. of_real t powr (s - 1) * of_real (exp (-t))) has_integral 0) {0}"
    by (rule has_integral_refl)
  thus ?thesis using True 
    by (simp add: Gamma_incl_def)
next
  case False
  with assms have x: "x < 0"
    by auto
  have *: "((\<lambda>t. t powr (s - 1) * exp (-t)) has_contour_integral Gamma_incl s (of_real x)) 
          (linepath 0 (of_real x))"
    by (rule has_contour_integral_Gamma_incl) (use x s in auto)
  have "((\<lambda>t. t powr (s - 1) * exp (-t)) has_contour_integral (-Gamma_incl s (of_real x))) 
          (linepath (of_real x) 0)"
    using has_contour_integral_reversepath[OF _ *] by simp
  thus ?thesis using x
    by (simp add: has_contour_integral_linepath_Reals_iff exp_of_real flip: of_real_minus)
qed

lemma has_integral_Gamma_incl_real:
  assumes s: "s > (0::real)"
  assumes "x \<ge> 0"
  shows "((\<lambda>t. t powr (s - 1) * exp (-t)) has_integral Gamma_incl s x) {0..x}"
proof -
  have "((\<lambda>t. of_real t powr (of_real s - 1) * of_real (exp (-t))) has_integral 
          (Gamma_incl (complex_of_real s) (of_real x))) {0..x}"
    by (rule has_integral_Gamma_incl_complex_of_real) (use assms in auto)
  also have "?this \<longleftrightarrow> ((\<lambda>t. of_real (t powr (s - 1) * exp (-t))) has_integral 
                           (Gamma_incl (complex_of_real s) (of_real x))) {0..x}"
    by (intro has_integral_cong) (auto simp: powr_Reals_eq)
  also have "Gamma_incl (complex_of_real s) (of_real x) = of_real (Gamma_incl s x)"
    by (rule Gamma_incl_complex_of_real) (use assms in auto)
  finally show ?thesis
    by (subst (asm) has_integral_complex_of_real_iff)
qed



subsection \<open>The upper incomplete Gamma function\<close>

text \<open>
  To make the definition work on as big a domain as possible, we do not define the upper
  incomplete Gamma function $\Gamma(s,z)$ as $\Gamma(s,z) = \Gamma(s) - \gamma(s,z)$, since there
  are values of $s$ where the left-hand side exists but the two parts on the right-hand side
  blow up. Rather, we express $\Gamma(s,z)$ as a contour integral starting at $z$ and going
  to $\infty$. The precise path does not matter much, so for convenience, we go from $z$ straight
  to $1$ (the first auxiliary function below) and then from $1$ straight to $\infty$.

  To make the first definition work for both the \<^typ>\<open>real\<close> and \<^typ>\<open>complex\<close> type, we express
  the contour integral in a more explicit fashion.
\<close>
definition Gamma_incu_aux1 :: "'a :: {banach, real_inner, real_normed_field, ln} \<Rightarrow> 'a \<Rightarrow> 'a" where
  "Gamma_incu_aux1 s z =
     (if (z + 1 \<in> \<real>\<^sub>\<le>\<^sub>0 \<and> (z \<noteq> -1 \<or> s \<bullet> 1 \<le> -1)) \<and> s \<notin> \<int> then 0 else 
        integral {0..1} (\<lambda>x. (1 + x *\<^sub>R z) powr' s * exp (- (1 + x *\<^sub>R z))))"

lemma Gamma_incu_aux1_complex_of_real: 
  "Gamma_incu_aux1 (complex_of_real s) (complex_of_real z) = of_real (Gamma_incu_aux1 s z)"
proof (cases "(z + 1 \<in> \<real>\<^sub>\<le>\<^sub>0 \<and> (z \<noteq> -1 \<or> s \<bullet> 1 \<le> -1)) \<and> s \<notin> \<int>")
  case True
  thus ?thesis
    by (auto simp: Gamma_incu_aux1_def nonpos_Reals_def complex_eq_iff)
next
  case False
  have *: "s \<in> \<int> \<or> complex_of_real z + 1 \<notin> \<real>\<^sub>\<le>\<^sub>0 \<or> z = -1 \<and> s > -1"
    using False
    by (auto simp: complex_nonpos_Reals_iff nonpos_Reals_real_eq)

  have **: "1 + x * z \<ge> 0" if x: "x \<ge> 0" "x \<le> 1" and s: "s \<notin> \<int>" for x
  proof (cases "z \<le> 0")
    case True
    have "-1 \<le> 1 * z"
      using False s by (auto simp: nonpos_Reals_real_eq)
    also have "\<dots> \<le> x * z"
      by (intro mult_right_mono_neg) (use x \<open>z \<le> 0\<close> in auto)
    finally show ?thesis
      by simp
  next
    case False
    have "-1 < (0::real)"
      by simp
    also have "\<dots> \<le> x * z"
      by (intro mult_nonneg_nonneg) (use x False in auto)
    finally show ?thesis
      by simp
  qed

  have "Gamma_incu_aux1 (complex_of_real s) (complex_of_real z) = 
         integral {0..1} (\<lambda>x. (1 + x *\<^sub>R complex_of_real z) powr' complex_of_real s *
                              exp (- 1 - x *\<^sub>R complex_of_real z))"
    using False * by (auto simp add: Gamma_incu_aux1_def)
  also have "\<dots> = of_real (integral {0..1} (\<lambda>x. (1 + x *\<^sub>R z) powr' s * exp (- 1 - x *\<^sub>R z)))"
    unfolding integral_complex_of_real [symmetric]
  proof (intro integral_cong)
    fix x assume x: "x \<in> {0..1::real}"
    show "(1 + x *\<^sub>R complex_of_real z) powr' complex_of_real s *
           exp (- 1 - x *\<^sub>R complex_of_real z) =
           complex_of_real ((1 + x *\<^sub>R z) powr' s * exp (- 1 - x *\<^sub>R z))"
      unfolding of_real_mult using **[of x] x False
      by (subst powr'_complex_of_real [symmetric])
         (auto simp: nonpos_Reals_real_eq scaleR_conv_of_real simp flip: exp_of_real)
  qed
  also have "\<dots> = complex_of_real (Gamma_incu_aux1 s z)"
    using False by (auto simp: Gamma_incu_aux1_def)
  finally show ?thesis .
qed

lemma Gamma_incu_aux1_conv_contour_integral:
  assumes "z \<notin> \<real>\<^sub>\<le>\<^sub>0 \<or> z = 0 \<and> Re s > 0 \<or> s \<in> \<int>"
  shows   "(z-1) * Gamma_incu_aux1 (s-1) (z-1) = 
             contour_integral (linepath 1 z) (\<lambda>u. u powr' (s - 1) * exp (-u))"
proof -
  define I where "I = integral {0..1} (\<lambda>x. (1 + x *\<^sub>R (z - 1)) powr' (s - 1) * exp (-(1 + x *\<^sub>R (z - 1))))"
  have "Gamma_incu_aux1 (s-1) (z-1) = I"
    using assms by (auto simp: Gamma_incu_aux1_def I_def)
  also have "(z - 1) * \<dots> = contour_integral (linepath 1 z) (\<lambda>u. u powr' (s - 1) * exp (-u))"
    unfolding contour_integral_integral integral_mult_right [symmetric] I_def
    by (rule integral_cong) (simp_all add: linepath_def algebra_simps)
  finally show ?thesis .
qed

lemma analytic_Gamma_incu_aux1 [analytic_intros]:
  assumes "f analytic_on A" "g analytic_on A" "\<And>x. x \<in> A \<Longrightarrow> 1 + g x \<notin> \<real>\<^sub>\<le>\<^sub>0"
  shows   "(\<lambda>x. Gamma_incu_aux1 (f x) (g x)) analytic_on A"
proof -
  define f' where "f' = deriv f"
  define g' where "g' = deriv g"
  define h where "h = (\<lambda>y x. exp (f y * ln (1 + x *\<^sub>R g y) - (1 + x *\<^sub>R g y)))"
  define h' where
    "h' = (\<lambda>y x. exp (f y * ln (1 + x *\<^sub>R g y) - (1 + x *\<^sub>R g y)) * (f' y * ln (1 + x *\<^sub>R g y) +
                 x *\<^sub>R (g' y * f y) / (1 + x *\<^sub>R g y) - x *\<^sub>R g' y))"
  have "(\<lambda>x. Gamma_incu_aux1 (f x) (g x)) analytic_on {z}" if z: "z \<in> A" for z
  proof -
    from assms(1) obtain A1 where A1: "open A1" "f holomorphic_on A1" "A \<subseteq> A1"
      using analytic_on_holomorphic by auto
    from assms(2) obtain A2 where A2: "open A2" "g holomorphic_on A2" "A \<subseteq> A2"
      using analytic_on_holomorphic by auto
    note [holomorphic_intros] = holomorphic_on_subset[OF A1(2)] holomorphic_on_subset[OF A2(2)]
    have [derivative_intros]: "(f has_field_derivative deriv f x) (at x within X)" 
      if "x \<in> A1" for x X
      by (rule holomorphic_derivI[OF A1(2,1) that])
    have [derivative_intros]: "(g has_field_derivative deriv g x) (at x within X)" 
      if "x \<in> A2" for x X
      by (rule holomorphic_derivI[OF A2(2,1) that])

    have cont: "continuous_on A1 f" "continuous_on A2 g" "continuous_on A1 f'" "continuous_on A2 g'"
      unfolding f'_def g'_def
      by (intro holomorphic_on_imp_continuous_on holomorphic_intros order.refl A1 A2)+
    note [continuous_intros] = cont[THEN continuous_on_compose2]

    have "open ((A1 \<inter> A2) \<inter> (\<lambda>x. 1 + g x) -` (-\<real>\<^sub>\<le>\<^sub>0))"
      by (intro continuous_open_preimage holomorphic_on_imp_continuous_on holomorphic_intros)
         (use A1(1) A2(1) in auto)
    moreover have "z \<in> (A1 \<inter> A2) \<inter> (\<lambda>x. 1 + g x) -` (-\<real>\<^sub>\<le>\<^sub>0)"
      using z assms(3) A1(3) A2(3) by auto
    ultimately obtain r where r: "r > 0" "cball z r \<subseteq> ((A1 \<inter> A2) \<inter> (\<lambda>x. 1 + g x) -` (-\<real>\<^sub>\<le>\<^sub>0))"
      unfolding open_contains_cball by blast

    have *: "1 + x *\<^sub>R g y \<notin> \<real>\<^sub>\<le>\<^sub>0" if x: "x \<in> {0..1}" and y: "y \<in> cball z r" for x y
    proof
      assume "1 + x *\<^sub>R g y \<in> \<real>\<^sub>\<le>\<^sub>0"
      hence "Im (g y) = 0" "1 + x * Re (g y) \<le> 0"
        by (auto simp: complex_nonpos_Reals_iff)
      from this(2) have "x \<noteq> 0"
        by auto
      with x have "x > 0"
        by auto
      with \<open>1 + x * Re (g y) \<le> 0\<close> have "1 + Re (g y) \<le> 1 - 1 / x"
        by (auto simp: field_simps)
      also have "\<dots> \<le> 0"
        using x \<open>x > 0\<close> by (auto simp: field_simps)
      finally have "1 + g y \<in> \<real>\<^sub>\<le>\<^sub>0"
        using \<open>Im (g y) = 0\<close> by (auto simp: complex_nonpos_Reals_iff)
      with y r show False
        by auto
    qed
    have **: "1 + x *\<^sub>R g y \<noteq> 0" if x: "x \<in> {0..1}" and y: "y \<in> cball z r" for x y
      using *[OF x y] by auto

    have "(\<lambda>y. integral (cbox 0 1) (h y)) holomorphic_on cball z r"
    proof (rule leibniz_rule_holomorphic)
      fix y :: complex assume y: "y \<in> cball z r"
      fix x :: real assume x: "x \<in> cbox 0 1"
      from \<open>y \<in> cball z r\<close> have y': "y \<in> A1" "y \<in> A2" "1 + g y \<notin> \<real>\<^sub>\<le>\<^sub>0"
        using r by auto
      show "((\<lambda>y. h y x) has_field_derivative h' y x) (at y within cball z r)"
        unfolding h_def using y' x *[OF _ y, of x]
        by (auto intro!: derivative_eq_intros simp: f'_def g'_def h'_def field_simps)
    next
      fix y assume "y \<in> cball z r"
      thus "h y integrable_on cbox 0 1"
        unfolding h_def by (intro integrable_continuous continuous_intros *) auto
    next
      show "continuous_on (cball z r \<times> cbox 0 1) (\<lambda>(y, t). h' y t)"
        unfolding h'_def case_prod_unfold
        by (intro continuous_intros ballI * **) (use r in auto)
    qed auto
    also have "?this \<longleftrightarrow> (\<lambda>x. Gamma_incu_aux1 (f x) (g x)) holomorphic_on cball z r"
    proof (intro holomorphic_cong)
      fix y assume y: "y \<in> cball z r"
      have "integral {0..1} (\<lambda>x. h y x) =
            integral {0..1} (\<lambda>x. (1 + x *\<^sub>R g y) powr' f y * exp (- 1 - x *\<^sub>R g y))"
      proof (rule integral_cong)
        fix t assume t: "t \<in> {0..1::real}"
        show "h y t = (1 + t *\<^sub>R g y) powr' f y * exp (- 1 - t *\<^sub>R g y)"
          by (subst powr'_complex) 
             (use *[OF t y] in \<open>auto simp: powr_def exp_diff exp_minus field_simps exp_add h_def\<close>)
      qed
      also have "\<dots> = Gamma_incu_aux1 (f y) (g y)"
        unfolding Gamma_incu_aux1_def using y r by (auto simp: add_ac)
      finally show "integral (cbox 0 1) (h y) = Gamma_incu_aux1 (f y) (g y)"
        by simp
    qed auto
    finally show "(\<lambda>x. Gamma_incu_aux1 (f x) (g x)) analytic_on {z}"
      using \<open>r > 0\<close> by (meson analytic_at_ball ball_subset_cball holomorphic_on_subset)
  qed
  thus ?thesis
    by (subst analytic_on_analytic_at) auto
qed

lemma analytic_Gamma_incu_aux1_nat [analytic_intros]:
  assumes "g analytic_on A"
  shows   "(\<lambda>x. Gamma_incu_aux1 (of_nat n) (g x)) analytic_on A"
proof -
  define g' where "g' = deriv g"
  define h where "h = (\<lambda>y x. (1 + x *\<^sub>R g y) ^ n * exp (-(1 + x *\<^sub>R g y)))"
  define h' where
    "h' = (\<lambda>y x. (of_nat n * (1 + x *\<^sub>R g y) ^ (n-1) - (1 + x *\<^sub>R g y) ^ n) * exp (-(1 + x *\<^sub>R g y)) * of_real x * g' y)"
  have "(\<lambda>x. Gamma_incu_aux1 (of_nat n) (g x)) analytic_on {z}" if z: "z \<in> A" for z
  proof -
    from assms(1) obtain A2 where A2: "open A2" "g holomorphic_on A2" "A \<subseteq> A2"
      using analytic_on_holomorphic by auto
    note [holomorphic_intros] = holomorphic_on_subset[OF A2(2)]
    have [derivative_intros]: "(g has_field_derivative deriv g x) (at x within X)" 
      if "x \<in> A2" for x X
      by (rule holomorphic_derivI[OF A2(2,1) that])

    have cont: "continuous_on A2 g" "continuous_on A2 g'"
      unfolding g'_def
      by (intro holomorphic_on_imp_continuous_on holomorphic_intros order.refl A2)+
    note [continuous_intros] = cont[THEN continuous_on_compose2]
    from A2 z obtain r where r: "r > 0" "cball z r \<subseteq> A2"
      unfolding open_contains_cball by blast

    have "(\<lambda>y. integral (cbox 0 1) (h y)) holomorphic_on cball z r"
    proof (rule leibniz_rule_holomorphic)
      fix y :: complex assume y: "y \<in> cball z r"
      fix x :: real assume x: "x \<in> cbox 0 1"
      from \<open>y \<in> cball z r\<close> have y': "y \<in> A2"
        using r by auto
      show "((\<lambda>y. h y x) has_field_derivative h' y x) (at y within cball z r)"
        unfolding h_def using y' x
        by (auto intro!: derivative_eq_intros simp: g'_def h'_def field_simps scaleR_conv_of_real)
    next
      fix y assume "y \<in> cball z r"
      thus "h y integrable_on cbox 0 1"
        unfolding h_def by (intro integrable_continuous continuous_intros)
    next
      show "continuous_on (cball z r \<times> cbox 0 1) (\<lambda>(y, t). h' y t)"
        unfolding h'_def case_prod_unfold
        by (intro continuous_intros ballI) (use r in auto)
    qed auto
    also have "?this \<longleftrightarrow> (\<lambda>x. Gamma_incu_aux1 (of_nat n) (g x)) holomorphic_on cball z r"
    proof (intro holomorphic_cong)
      fix y assume y: "y \<in> cball z r"
      have "integral {0..1} (\<lambda>x. h y x) =
            integral {0..1} (\<lambda>x. (1 + x *\<^sub>R g y) ^ n * exp (- 1 - x *\<^sub>R g y))"
      proof (rule integral_cong)
        fix t assume t: "t \<in> {0..1::real}"
        show "h y t = (1 + t *\<^sub>R g y) ^ n * exp (- 1 - t *\<^sub>R g y)"
          by (auto simp: powr_def exp_diff exp_minus field_simps exp_add h_def)
      qed
      also have "\<dots> = Gamma_incu_aux1 (of_nat n) (g y)"
        unfolding Gamma_incu_aux1_def using y r by (auto simp: add_ac)
      finally show "integral (cbox 0 1) (h y) = Gamma_incu_aux1 (of_nat n) (g y)"
        by simp
    qed auto
    finally show "(\<lambda>x. Gamma_incu_aux1 (of_nat n) (g x)) analytic_on {z}"
      using \<open>r > 0\<close> by (meson analytic_at_ball ball_subset_cball holomorphic_on_subset)
  qed
  thus ?thesis
    by (subst analytic_on_analytic_at) auto
qed


lemma continuous_on_Gamma_incu_aux1_complex':
  fixes A :: "(complex \<times> complex) set"
  assumes A: "\<And>s z. (s, z) \<in> A \<Longrightarrow> (Re z \<ge> -1 \<or> Im z \<noteq> 0) \<and> z \<noteq> -1"
  shows   "continuous_on A (\<lambda>sz. Gamma_incu_aux1 (fst sz) (snd sz))"
proof -
  define h where "h = (\<lambda>s z x. (1 + x *\<^sub>R z) powr' s * exp (- (1 + x *\<^sub>R z)) :: complex)"
  define B :: "(complex \<times> complex) set" where "B = {(s,z). (Re z \<ge> -1 \<or> Im z \<noteq> 0) \<and> z \<noteq> -1}"

  have cont: "continuous_on B (\<lambda>sz. integral (cbox 0 1) (h (fst sz) (snd sz)))"
  proof (rule integral_continuous_on_param)
    have 1: "B \<times> cbox 0 1 \<subseteq> {x. 0 \<le> Re (1 + snd x *\<^sub>R snd (fst x)) \<or> Im (1 + snd x *\<^sub>R snd (fst x)) \<noteq> 0}"
    proof (intro subsetI CollectI, elim SigmaE, simp only: fst_conv snd_conv)
      fix sz :: "complex \<times> complex" and t :: real
      assume sz: "sz \<in> B" and t: "t \<in> cbox 0 1"
      consider "t = 0" | "t > 0" "Im (snd sz) = 0" | "t > 0" "Im (snd sz) \<noteq> 0"
        using t by force
      thus "0 \<le> Re (1 + t *\<^sub>R snd sz) \<or> Im (1 + t *\<^sub>R snd sz) \<noteq> 0"
      proof cases
        case 2
        have "-1 \<le> t * (-1)"
          using t by simp
        also have "t * (-1) \<le> t * Re (snd sz)"
          by (rule mult_left_mono) (use 2 sz in \<open>auto simp: B_def\<close>)
        finally show ?thesis
          using 2 by simp
      qed (use sz t in auto)
    qed

    have 2: False if "((s,z), t) \<in> B \<times> cbox 0 1" "1 + t *\<^sub>R z = 0" for s z t
    proof -
      from that have "Re z \<ge> -1" "1 + t * Re z = 0"
        by (auto simp: complex_eq_iff B_def)
      have "t > 0"
        using that by (cases "t = 0") auto
      with \<open>1 + t * Re z = 0\<close> have Re_z: "Re z = -1 / t"
        by (auto simp: field_simps)
      also have "-1/t \<le> -1"
        using that \<open>t > 0\<close> by (auto simp: field_simps)
      finally have "Re z = -1"
        using \<open>Re z \<ge> -1\<close> by linarith
      with that show False
        by (auto simp: complex_eq_iff B_def)
    qed

    show "continuous_on (B \<times> cbox 0 1) (\<lambda>(sz, t). h (fst sz) (snd sz) t)"
      unfolding case_prod_unfold h_def by (intro continuous_intros) (use 1 2 in force)+
  qed
  also have "?this \<longleftrightarrow> continuous_on B (\<lambda>sz. Gamma_incu_aux1 (fst sz) (snd sz))"
  proof (rule continuous_on_cong)
    fix sz assume sz: "sz \<in> B"
    show "integral (cbox 0 1) (h (fst sz) (snd sz)) = Gamma_incu_aux1 (fst sz) (snd sz)"
      using sz
      by (auto simp: Gamma_incu_aux1_def h_def complex_nonpos_Reals_iff complex_eq_iff B_def)
  qed auto
  finally show ?thesis
    by (rule continuous_on_subset) (use A in \<open>auto simp: B_def\<close>)
qed

lemma continuous_on_Gamma_incu_aux1_complex [continuous_intros]:
  assumes "continuous_on A f" "continuous_on A g"
  assumes A: "\<And>x. x \<in> A \<Longrightarrow> (Re (g x) \<ge> -1 \<or> Im (g x) \<noteq> 0) \<and> g x \<noteq> -1"
  shows   "continuous_on A (\<lambda>x. Gamma_incu_aux1 (f x) (g x :: complex))"
proof -
  have "continuous_on A ((\<lambda>x. Gamma_incu_aux1 (fst x) (snd x)) \<circ> (\<lambda>x. (f x, g x)))"
    by (intro continuous_on_compose continuous_on_Gamma_incu_aux1_complex' continuous_intros assms) 
       (use A in auto)
  thus ?thesis
    by (simp add: o_def)
qed

lemma continuous_Gamma_incu_aux1_at_neg1_aux:
  defines "A \<equiv> {(s,z). Re s > -1 \<and> Re z > -1}"
  assumes "Re s > -1"
  shows   "((\<lambda>(s,z). Gamma_incu_aux1 s z) \<longlongrightarrow> Gamma_incu_aux1 s (-1)) (at (s, -1) within A)"
proof -
  define h where "h = (\<lambda>s z x. (1 + x *\<^sub>R z) powr' s * exp (- (1 + x *\<^sub>R z)) :: complex)"
  define c where "c = \<bar>Im s\<bar> + 1"
  define d where "d = (Re s - 1) / 2"
  define e where "e = Re s + 1"
  define H where "H = (\<lambda>t::real. (1 - t) powr d + (1 + 2 * t) powr e)"

  have *: "Re (1 + t *\<^sub>R z) > 0" if t: "t \<in> {0..1}" and z: "Re z > -1" for t z
  proof (cases "t = 0")
    case False
    hence "t * (-Re z) < t * 1"
      by (intro mult_strict_left_mono) (use z t in \<open>auto simp: A_def\<close>)
    also have "\<dots> \<le> 1"
      using t by simp
    finally show ?thesis
      by simp
  qed auto

  have "((\<lambda>(s,z). integral {0..<1} (h s z)) \<longlongrightarrow> integral {0..<1} (h s (-1))) (at (s,-1) within A)"
    unfolding case_prod_unfold
  proof (rule at_within.dominated_convergence')
    have "\<forall>\<^sub>F (s,z) in at (s, -1) within A. (s,z) \<in> A"
      by (auto simp: eventually_at_topological)
    moreover have "\<forall>\<^sub>F sz in at (s, -1::complex). 
                     sz \<in> ({s. Im s < c} \<inter> {s. Im s > -c} \<inter> {s. Re s > d} \<inter> {s. Re s < e}) \<times> ball 0 2"
      using assms
      by (intro eventually_at_in_open' open_Times open_Int open_halfspace_Re_gt
                open_halfspace_Re_lt open_halfspace_Im_gt open_halfspace_Im_lt)
         (auto simp: c_def d_def e_def dist_norm)
    hence "\<forall>\<^sub>F sz in at (s, -1) within A. 
             sz \<in> ({s. Im s < c} \<inter> {s. Im s > -c} \<inter> {s. Re s > d} \<inter> {s. Re s < e}) \<times> ball 0 2"
      by (rule filter_leD [OF at_within_le_at])
    ultimately show "\<forall>\<^sub>F sz in at (s, -1) within A. \<forall>t\<in>{0..<1}. norm (h (fst sz) (snd sz) t) \<le> 
                       exp (c * pi) * H t"
    proof eventually_elim
      case (elim sz)
      obtain s z where [simp]: "sz = (s, z)"
        by (cases sz)
      show ?case
      proof safe
        fix t assume t: "t \<in> {0..<1::real}"
        have nz: "1 + t *\<^sub>R z \<noteq> 0"
          using *[of t z] t elim by (auto simp: A_def complex_eq_iff)
        have "norm (h (fst sz) (snd sz) t) = norm ((1 + t *\<^sub>R z) powr' s) * exp (- 1 - t * Re z)"
          by (auto simp: h_def norm_mult)
        also have "\<dots> = norm ((1 + t *\<^sub>R z) powr s) * exp (- 1 - t * Re z)"
          by (subst powr'_complex) (use nz in auto)
        also have "\<dots> = norm (1 + t *\<^sub>R z) powr Re s * exp (- (Im s * Arg (1 + t *\<^sub>R z))) * exp (- 1 - t * Re z)"
          by (simp add: norm_powr_complex)
        also have "\<dots> \<le> norm (1 + t *\<^sub>R z) powr Re s * exp (pi * c) * exp 0"
        proof (intro mult_mono mult_nonneg_nonneg exp_mono)
          have "1 * (-1) \<le> t * (-1)"
            by (rule mult_right_mono_neg) (use t in auto)
          also have "t * (-1) \<le> t * Re z"
            by (rule mult_left_mono) (use t elim in \<open>auto simp: A_def\<close>)
          finally show "- 1 - t * Re z \<le> 0"
            by simp
        next
          have "-(Im s * Arg (1 + t *\<^sub>R z)) \<le> \<bar>Im s * Arg (1 + t *\<^sub>R z)\<bar>"
            by linarith
          also have "\<dots> = \<bar>Im s\<bar> * \<bar>Arg (1 + t *\<^sub>R z)\<bar>"
            by (simp add: abs_mult)
          also have "\<dots> \<le> c * pi"
            by (intro mult_mono) (use elim Arg_bounded[of "1 + t *\<^sub>R z"] in auto)
          finally show "-(Im s * Arg (1 + t *\<^sub>R z)) \<le> pi * c"
            by (simp add: mult_ac)
        qed auto
        
        also have "\<dots> \<le> H t * exp (pi * c) * exp 0"
        proof (intro mult_right_mono)
          show "norm (1 + t *\<^sub>R z) powr Re s \<le> H t"
          proof (cases "Re s \<le> 0")
            case True
            have "norm (1 + t *\<^sub>R z) powr Re s \<le> (1 - t) powr Re s"
            proof (intro powr_mono2')
              have "1 + t * (-1) \<le> 1 + t * Re z"
                by (intro add_mono mult_left_mono) (use t elim in \<open>auto simp: A_def\<close>)
              also have "t * Re z \<ge> t * (-1)"
                by (intro mult_left_mono) (use t elim in \<open>auto simp: A_def\<close>)
              hence "1 + t * Re z \<le> \<bar>Re (1 + t *\<^sub>R z)\<bar>"
                by simp
              also have "\<bar>Re (1 + t *\<^sub>R z)\<bar> \<le> norm (1 + t *\<^sub>R z)"
                by (rule abs_Re_le_cmod)
              finally show "norm (1 + t *\<^sub>R z) \<ge> 1 - t"
                by simp
            qed (use \<open>Re s \<le> 0\<close> t in auto)
            also have "\<dots> \<le> (1 - t) powr d"
              by (intro powr_mono') (use t elim True in auto)
            also have "\<dots> \<le> H t"
              using True by (simp add: H_def)
            finally show ?thesis .
          next
            case False
            have "norm (1 + t *\<^sub>R z) powr Re s \<le> (1 + 2 * t) powr Re s"
            proof (intro powr_mono2)
              have "norm (1 + t *\<^sub>R z) \<le> norm (1::complex) + norm (t *\<^sub>R z)"
                by (rule norm_triangle_ineq)
              also have "\<dots> = 1 + t * norm z"
                using t by simp
              also have "\<dots> \<le> 1 + t * 2"
                by (intro add_mono mult_left_mono) (use elim t in auto)
              finally show "norm (1 + t *\<^sub>R z) \<le> (1 + 2 * t)"
                by (simp add: mult_ac)
            qed (use False in auto)
            also have "\<dots> \<le> (1 + 2 * t) powr e"
              by (intro powr_mono) (use t elim in auto)
            also have "\<dots> \<le> H t"
              by (simp add: H_def)
            finally show ?thesis .
          qed
        qed auto
        finally show "norm (h (fst sz) (snd sz) t) \<le> exp (c * pi) * H t"
          by (simp add: mult_ac)
      qed
    qed
  next
    have "\<forall>\<^sub>F (s,z) in at (s, -1) within A. (s,z) \<in> A"
      by (auto simp: eventually_at_topological)
    thus "\<forall>\<^sub>F sz in at (s, -1) within A. h (fst sz) (snd sz) integrable_on {0..<1}"
    proof eventually_elim
      case (elim sz)
      obtain s z where sz [simp]: "sz = (s, z)"
        by (cases sz)
      have z: "Re z > -1"
        using elim by (auto simp: A_def)
      have "continuous_on {0..1} (h (fst sz) (snd sz))"
        unfolding h_def sz snd_conv fst_conv using *[OF _ z]
        by (intro continuous_intros subsetI CollectI) fastforce+
      hence "h (fst sz) (snd sz) integrable_on {0..1}"
        by (rule integrable_continuous_real)
      also have "?this \<longleftrightarrow> ?case"
        by (rule integrable_spike_set_eq[OF negligible_subset[of "{1}"]]) auto
      finally show ?case .
    qed
  next
    have d: "d > -1"
      using assms by (auto simp: d_def)
    have "(\<lambda>x. x powr d) integrable_on {0..1}"
      by (rule integrable_on_powr_from_0) (use d in auto)
    also have "?this \<longleftrightarrow> ((\<lambda>x. (1 + x) powr d) integrable_on {- 1..0}) "
      by (subst Henstock_Kurzweil_Integration.integrable_shift_real_ivl_iff [of _ "-1", symmetric]) simp
    also have "\<dots> \<longleftrightarrow> (\<lambda>x. (1 - x) powr d) integrable_on {0..1}"
      by (subst Henstock_Kurzweil_Integration.integrable_reflect_real [symmetric]) simp
    also have "\<dots> \<longleftrightarrow> (\<lambda>x. (1 - x) powr d) integrable_on {0..<1}"
      by (rule integrable_spike_set_eq[OF negligible_subset[of "{1}"]]) auto
    finally have I1: "(\<lambda>t. (1 - t) powr d) integrable_on {0..<1}" .

    have "(\<lambda>t. (1 + 2 * t) powr e) integrable_on {0..1}"
      by (rule integrable_continuous_real) (auto intro!: continuous_intros)
    also have "?this \<longleftrightarrow> (\<lambda>t. (1 + 2 * t) powr e) integrable_on {0..<1}"
      by (rule integrable_spike_set_eq[OF negligible_subset[of "{1}"]]) auto
    finally have I2: "(\<lambda>t. (1 + 2 * t) powr e) integrable_on {0..<1}" .

    show "(\<lambda>t. exp (c * pi) * H t) integrable_on {0..<1}"
      unfolding H_def by (intro integrable_on_mult_right integrable_add I1 I2)
  next
    fix t assume t: "t \<in> {0..<1::real}"
    have "1 + t *\<^sub>R (-1 :: complex) \<notin> \<real>\<^sub>\<le>\<^sub>0"
      using t by (auto simp: complex_nonpos_Reals_iff)
    thus "((\<lambda>p. h (fst p) (snd p) t) \<longlongrightarrow> h s (- 1) t) (at (s, - 1) within A)"
      unfolding h_def using t by (intro tendsto_intros) (auto intro!: tendsto_eq_intros)
  qed

  also have "integral {0..<1} (h s (-1)) = integral {0..1} (h s (-1))"
    by (rule integral_subset_negligible) auto
  also have "\<dots> = Gamma_incu_aux1 s (-1)"
    using assms(2) by (auto simp: Gamma_incu_aux1_def h_def)
  also have "eventually (\<lambda>sz. sz \<in> A) (at (s, -1) within A)"
    by (auto simp: eventually_at_topological)
  hence "eventually (\<lambda>(s,z). integral {0..<1} (h s z) = Gamma_incu_aux1 s z) (at (s, -1) within A)"
  proof eventually_elim
    case (elim sz)
    obtain s z where [simp]: "sz = (s, z)"
      by (cases sz)
    have "integral {0..<1} (h s z) = integral {0..1} (h s z)"
      by (rule integral_subset_negligible) auto
    also have "\<dots> = Gamma_incu_aux1 s z"
      using elim by (auto simp: Gamma_incu_aux1_def h_def complex_nonpos_Reals_iff A_def)
    finally show ?case
      by simp
  qed
  hence "((\<lambda>(s,z). integral {0..<1} (h s z)) \<longlongrightarrow> Gamma_incu_aux1 s (- 1)) (at (s, -1) within A) \<longleftrightarrow>
         ((\<lambda>(s,z). Gamma_incu_aux1 s z) \<longlongrightarrow> Gamma_incu_aux1 s (-1)) (at (s, -1) within A)"
    by (intro filterlim_cong) (auto simp: case_prod_unfold)
  finally show ?thesis .
qed   
    


definition Gamma_incu_aux2 :: "'a :: {banach, real_normed_algebra_1} \<Rightarrow> 'a" where
  "Gamma_incu_aux2 s = integral {1..} (\<lambda>t. exp ((s-1) * of_real (ln t) - of_real t))"

lemma Gamma_incu_aux2_complex_of_real:
  "Gamma_incu_aux2 (complex_of_real s) = of_real (Gamma_incu_aux2 s)"
  unfolding Gamma_incu_aux2_def integral_complex_of_real [symmetric]
  by (rule integral_cong) (auto simp flip: exp_of_real)

lemma absolutely_integrable_incomplete_Gamma:
  fixes s :: complex
  assumes r: "r > 0"
  shows   "(\<lambda>t. exp (of_real (-t) - s * of_real (ln t))) absolutely_integrable_on {r..}"
proof -
  have "set_integrable lborel {r..} (\<lambda>t. exp (of_real (-t) - s * of_real (ln t)))"
  proof (rule set_integrable_bigo)
    have "(\<lambda>t. norm (exp (of_real (-t) - s * of_real (ln t)))) = (\<lambda>t. exp (-t - Re s * ln t))"
      by simp
    also have "\<dots> \<in> O(\<lambda>t. exp (-t/2))"
      by real_asymp
    finally have "(\<lambda>t. norm (exp (of_real (-t) - s * of_real (ln t)))) \<in> 
                    O(\<lambda>t. norm (complex_of_real (exp (-t/2))))"
      by simp
    thus "(\<lambda>t. exp (of_real (-t) - s * of_real (ln t))) \<in> O(\<lambda>t. complex_of_real (exp (-t/2)))"
      unfolding landau_o.big.norm_iff .
  next
    have "(\<lambda>t. exp (-t/2)) integrable_on {r..}"
      using integrable_on_exp_minus_to_infinity[of "1/2" r] by simp
    hence "(\<lambda>t. exp (-t/2)) absolutely_integrable_on {r..}"
      by (simp add: nonnegative_absolutely_integrable_1) 
    hence "set_integrable lborel {r..} (\<lambda>t. exp (-t/2))"
      unfolding set_integrable_def by (subst (asm) integrable_completion) auto
    hence "integrable lborel (\<lambda>t. complex_of_real (indicator {r..} t * exp (-t/2)))"
      by (intro integrable_of_real) (simp_all add: set_integrable_def)
    thus "set_integrable lborel {r..} (\<lambda>t. complex_of_real (exp (- t / 2)))"
      by (simp add: set_integrable_def of_real_indicator scaleR_conv_of_real)
  next
    show "set_integrable lborel {r..<b} (\<lambda>t. exp (of_real (-t) - s * of_real (ln t)))" if "r \<le> b" for b
    proof (rule set_integrable_subset)
      show "set_integrable lborel {r..b} (\<lambda>t. exp (of_real (-t) - s * of_real (ln t)))"
        by (rule borel_integrable_atLeastAtMost')
           (use \<open>r \<le> b\<close> \<open>r > 0\<close> in \<open>auto intro!: continuous_intros\<close>)
    qed auto
  qed (auto simp: set_borel_measurable_def)
  thus ?thesis
    unfolding set_integrable_def by (subst integrable_completion) auto
qed

lemma analytic_Gamma_incu_aux2_aux:
  fixes r :: real and f :: "complex \<Rightarrow> complex"
  assumes r: "r > 0"
  defines "f \<equiv> (\<lambda>z. integral {r..} (\<lambda>t. exp (-of_real t - z * of_real (ln t))))"
  shows "f holomorphic_on UNIV"
proof -
  define g where "g = (\<lambda>x z. LBINT t:{r..x}. exp (-of_real t - z * complex_of_real (ln t)))"
  define f' where "f' = (\<lambda>z. LBINT t:{r..}. exp (-of_real t - z * complex_of_real (ln t)))"

  have "f' analytic_on {s}" for s
  proof -
    define A where "A = {z. Re z > -\<bar>Re s\<bar> - 1} \<inter> {z. Re z < \<bar>Re s\<bar> + 1}"
    define c where "c = (\<bar>Re s\<bar> + 1)"
    define h :: "real \<Rightarrow> real" where "h = (\<lambda>t. exp (-t + c * \<bar>ln t\<bar>))"

    have "open A"
      unfolding A_def by (intro open_Int open_halfspace_Re_lt open_halfspace_Re_gt)
    moreover have "s \<in> A"
      by (auto simp: A_def)
    ultimately obtain R where R: "R > 0" "cball s R \<subseteq> A"
      using open_contains_cball by blast

    have "uniform_limit A g f' at_top"
      unfolding g_def f'_def
    proof (rule uniform_limit_set_lebesgue_integral_at_top)
      show "set_integrable lborel {r..} h"
      proof (rule set_integrable_bigo)
        show "h \<in> O(\<lambda>t. exp (-t/2))"
          unfolding h_def by real_asymp
      next
        have "(\<lambda>t. exp (-t/2)) integrable_on {r..}"
          using integrable_on_exp_minus_to_infinity[of "1/2" r] by simp
        hence "(\<lambda>t. exp (-t/2)) absolutely_integrable_on {r..}"
          by (simp add: nonnegative_absolutely_integrable_1)
        thus "set_integrable lborel {r..} (\<lambda>t. exp (-t/2))"
          unfolding set_integrable_def by (subst (asm) integrable_completion) auto
      next
        fix b assume "b \<ge> r"
        have "set_integrable lborel {r..b} h" unfolding h_def
          by (intro borel_integrable_atLeastAtMost' continuous_intros) (use r in auto)
        thus "set_integrable lborel {r..<b} h"
          by (rule set_integrable_subset) auto
      qed (auto simp: h_def set_borel_measurable_def)
    next
      fix z t assume z: "z \<in> A" and t: "t \<ge> r"
      have "\<bar>Re z\<bar> < \<bar>Re s\<bar> + 1"
        using z unfolding A_def by auto
      have "norm (exp (-of_real t - z * of_real (ln t))) = exp (-t - Re z * ln t)"
        by simp
      also have "-t - Re z * ln t \<le> -t + (\<bar>Re s\<bar> + 1) * \<bar>ln t\<bar>"
      proof -
        have "-Re z * ln t \<le> \<bar>Re z * ln t\<bar>"
          by linarith
        have "-Re z * ln t \<le> \<bar>Re z * ln t\<bar>"
          by linarith
        also have "\<dots> \<le> (\<bar>Re s\<bar> + 1) * \<bar>ln t\<bar>"
          unfolding abs_mult by (intro mult_right_mono) (use \<open>\<bar>Re z\<bar> < \<bar>Re s\<bar> + 1\<close> in auto)
        finally show ?thesis
          by simp
      qed
      finally show "norm (exp (-of_real t - z * of_real (ln t))) \<le> h t"
        by (simp add: h_def c_def)
    qed (simp_all add: set_borel_measurable_def)
    hence lim: "uniform_limit (cball s R) g f' at_top"
      by (rule uniform_limit_on_subset) (use R in auto)

    have holo: "g b holomorphic_on UNIV" for b
    proof -
      define h :: "complex \<Rightarrow> real \<Rightarrow> complex"
        where "h = (\<lambda>z t. exp (-of_real t - z * of_real (ln t)))"
      define h' where "h' = (\<lambda>z t. -h z t * ln t)"

      have "(\<lambda>z. integral (cbox r b) (h z)) holomorphic_on UNIV"
      proof (rule leibniz_rule_holomorphic)
        show "h z integrable_on cbox r b" for z
          by (rule integrable_continuous) (use r in \<open>auto simp: h_def intro!: continuous_intros\<close>)
      next
        show "((\<lambda>z. h z t) has_field_derivative h' z t) (at z)"
          if t: "t \<in> cbox r b" for z t
          by (auto intro!: derivative_eq_intros simp: h_def h'_def)
      next
        show "continuous_on (UNIV \<times> cbox r b) (\<lambda>(z, t). h' z t)" using r
          by (auto simp: h'_def h_def case_prod_unfold intro!: continuous_intros)
      qed auto
      also have "(\<lambda>z. integral (cbox r b) (h z)) = g b"
      proof
        fix z :: complex
        have "set_integrable lborel {r..b} (h z)" unfolding h_def
          by (intro borel_integrable_atLeastAtMost') (use r in \<open>auto intro!: continuous_intros\<close>)
        thus "integral (cbox r b) (h z) = g b z" unfolding g_def
          by (subst set_borel_integral_eq_integral(2)) (simp_all add: h_def)
      qed
      finally show ?thesis
        by (simp add: g_def)
    qed

    have wf: "\<forall>\<^sub>F b in at_top. continuous_on (cball s R) (g b) \<and> g b holomorphic_on ball s R"
      by (intro always_eventually allI impI conjI holomorphic_on_subset[OF holo]
                holomorphic_on_imp_continuous_on) auto
    have "f' holomorphic_on ball s R"
      using holomorphic_uniform_limit[OF wf lim] by auto
    with \<open>R > 0\<close> show "f' analytic_on {s}"
      using analytic_at_ball by blast
  qed
  hence "f' holomorphic_on UNIV"
    using analytic_imp_holomorphic analytic_on_analytic_at by blast
  also have "?this \<longleftrightarrow> f holomorphic_on UNIV"
  proof (intro holomorphic_cong)
    fix z :: complex
    have "set_integrable lborel {r..} (\<lambda>x. exp (-complex_of_real x - z * complex_of_real (ln x)))"
      using absolutely_integrable_incomplete_Gamma[of r] r
      by (simp add: set_integrable_def integrable_completion)
    thus "f' z = f z"
      unfolding f_def f'_def by (rule set_borel_integral_eq_integral(2))
  qed auto
  finally show ?thesis .
qed

lemma analytic_Gamma_incu_aux2 [analytic_intros]:
  assumes "f analytic_on A"
  shows   "(\<lambda>x. Gamma_incu_aux2 (f x)) analytic_on A"
proof -
  have "(Gamma_incu_aux2 \<circ> f) analytic_on A"
  proof (rule analytic_on_compose_gen)
    have "((\<lambda>z. integral {1..} (\<lambda>t. exp (-complex_of_real t - z * of_real (ln t)))) \<circ> (\<lambda>z. 1 - z))
             holomorphic_on UNIV"
      by (rule holomorphic_on_compose_gen[OF _ analytic_Gamma_incu_aux2_aux]) 
         (auto intro!: holomorphic_intros)
    thus "Gamma_incu_aux2 analytic_on UNIV"
      by (simp add: Gamma_incu_aux2_def [abs_def] o_def algebra_simps analytic_on_open)
  qed (use assms in auto)
  thus ?thesis
    by (simp add: o_def)
qed

lemma continuous_on_Gamma_incu_aux2_complex [continuous_intros]:
  assumes "continuous_on A f"
  shows   "continuous_on A (\<lambda>x. Gamma_incu_aux2 (f x :: complex))"
proof (rule continuous_on_compose2[OF _ assms])
  show "continuous_on (UNIV :: complex set) Gamma_incu_aux2"
    by (intro analytic_imp_holomorphic holomorphic_on_imp_continuous_on analytic_intros)
qed auto

lemma continuous_Gamma_incu_aux2_complex [continuous_intros]:
  assumes "continuous (at x within A) f"
  shows   "continuous (at x within A) (\<lambda>x. Gamma_incu_aux2 (f x :: complex))"
proof (rule continuous_within_compose3[OF _ assms])
  show "isCont Gamma_incu_aux2 (f x)"
    by (intro analytic_at_imp_isCont analytic_intros)
qed


text \<open>
  Finally, we can define the upper incomplete Gamma function $\Gamma(s,z)$:
\<close>
definition Gamma_incu :: "'a :: {banach, real_inner, real_normed_field, ln} \<Rightarrow> 'a \<Rightarrow> 'a"
  where "Gamma_incu s z = Gamma_incu_aux2 s - (z - 1) * Gamma_incu_aux1 (s - 1) (z - 1)"

lemma Gamma_incu_complex_of_real:
  "Gamma_incu (complex_of_real s) (of_real z) = of_real (Gamma_incu s z)"
  by (simp add: Gamma_incu_def flip: Gamma_incu_aux1_complex_of_real Gamma_incu_aux2_complex_of_real)

text \<open>
  In general, $\Gamma(s, z)$ is analytic away from $z \leq 0$ (where it has a branch cut).
\<close>
lemma analytic_Gamma_incu [analytic_intros]:
  assumes "f analytic_on A" "g analytic_on A" "\<And>x. x \<in> A \<Longrightarrow> g x \<notin> \<real>\<^sub>\<le>\<^sub>0"
  shows   "(\<lambda>x. Gamma_incu (f x) (g x)) analytic_on A"
  unfolding Gamma_incu_def by (intro analytic_intros assms(1,2)) (use assms(3) in auto)

text \<open>
  For $s$ a positive integer, $\Gamma(s,z)$ is entire in $z$:
\<close>
lemma analytic_Gamma_incu_pos_int [analytic_intros]:
  assumes "g analytic_on A" "n > 0"
  shows   "(\<lambda>x. Gamma_incu (of_int n) (g x)) analytic_on A"
proof -
  have "(\<lambda>x. Gamma_incu_aux2 (complex_of_int n) - 
          (g x - 1) * Gamma_incu_aux1 (of_nat (nat n - 1)) (g x - 1)) analytic_on A"
    by (intro analytic_intros assms(1))
  thus ?thesis
    using assms(2) by (simp add: Gamma_incu_def)
qed

lemma continuous_on_Gamma_incu_complex [continuous_intros]:
  fixes x z :: "'a :: topological_space \<Rightarrow> complex"
  assumes [continuous_intros]: "continuous_on X s" "continuous_on X z"
  assumes "\<And>x. x \<in> X \<Longrightarrow> Re (z x) > 0 \<or> Im (z x) \<noteq> 0"
  shows   "continuous_on X (\<lambda>x. Gamma_incu (s x) (z x))"
  unfolding Gamma_incu_def by (auto intro!: continuous_intros dest!: assms(3))

lemma tendsto_Gamma_incu_complex [tendsto_intros]:
  fixes s z :: complex
  assumes "(f \<longlongrightarrow> s) F" "(g \<longlongrightarrow> z) F" "Re z > 0 \<or> Im z \<noteq> 0"
  shows   "((\<lambda>x. Gamma_incu (f x) (g x)) \<longlongrightarrow> Gamma_incu s z) F"
proof -
  have "continuous_on {(s,z). Re z > 0 \<or> Im z \<noteq> 0} (\<lambda>(s,z). Gamma_incu s z)"
    by (auto simp: case_prod_unfold intro!: continuous_intros)
  hence "((\<lambda>x. case (f x, g x) of (s, z) \<Rightarrow> Gamma_incu s z) \<longlongrightarrow> 
           (case (s, z) of (s, z) \<Rightarrow> Gamma_incu s z)) F"
  proof (rule continuous_on_tendsto_compose)
    have "\<forall>\<^sub>F x in F. g x \<in> {z. Re z > 0} \<union> {z. Im z > 0} \<union> {z. Im z < 0}"
      by (intro eventually_compose_filterlim[OF eventually_nhds_in_open assms(2)] open_Un)
         (use assms(3) in \<open>auto simp: open_halfspace_Im_gt open_halfspace_Im_lt open_halfspace_Re_gt\<close>)
    thus "\<forall>\<^sub>F x in F. (f x, g x) \<in> {(s, z). 0 < Re z \<or> Im z \<noteq> 0}"
      by eventually_elim auto
  qed (use assms in \<open>auto simp: case_prod_unfold intro: tendsto_intros\<close>)
  thus ?thesis
    by simp
qed

lemma tendsto_Gamma_incu_real [tendsto_intros]:
  fixes s z :: real
  assumes "(f \<longlongrightarrow> s) F" "(g \<longlongrightarrow> z) F" "z > 0"
  shows   "((\<lambda>x. Gamma_incu (f x) (g x)) \<longlongrightarrow> Gamma_incu s z) F"
proof -
  have "((\<lambda>x. Re (Gamma_incu (of_real (f x)) (of_real (g x)))) \<longlongrightarrow> 
          Re (Gamma_incu (of_real s) (of_real z))) F"
    by (rule tendsto_intros assms(1,2))+ (use assms in auto)
  thus ?thesis
    by (simp add: Gamma_incu_complex_of_real)
qed

lemma continuous_Gamma_incu_complex [continuous_intros]:
  fixes s z :: "_ \<Rightarrow> complex"
  assumes "continuous (at x within A) s" "continuous (at x within A) z"
  assumes "Re (z x) > 0 \<or> Im (z x) \<noteq> 0"
  shows   "continuous (at x within A) (\<lambda>x. Gamma_incu (s x) (z x))"
  using assms unfolding continuous_def
  by (cases "at x within A = bot") (auto simp: Lim_ident_at intro: tendsto_intros)

lemma continuous_Gamma_incu_real [continuous_intros]:
  fixes s z :: "_ \<Rightarrow> real"
  assumes "continuous (at x within A) s" "continuous (at x within A) z"
  assumes "z x > 0"
  shows   "continuous (at x within A) (\<lambda>x. Gamma_incu (s x) (z x))"
  using assms unfolding continuous_def
  by (cases "at x within A = bot") (auto simp: Lim_ident_at intro: tendsto_intros)


text \<open>
  The behaviour at the branch point $z = 0$ is also interesting: when approaching from the
  right (i.e. $\text{Re}(s) > 0$ and $\text{Re}(z) > 0$, the function $\Gamma(s,z)$ converges
  as $z \to 0$. We will later see that it converges to $\Gamma(s)$.
\<close>
lemma continuous_Gamma_incu_0_strong_complex:
  assumes "Re s > 0"
  defines "F \<equiv> (at (s,0) within ({s. Re s > 0} \<times> {z. Re z > 0}))"
  shows "continuous F (\<lambda>(s,z). Gamma_incu s z)"
proof -
  define f where "f = (\<lambda>(s,z). Gamma_incu_aux1 s z :: complex)"
  define g where "g = (\<lambda>(s,z). (s - 1 :: complex, z - 1 :: complex))"
  define F' where "F' = (at (s-1, -1) within ({s. Re s > -1} \<times> {z. Re z > -1}))"
  have 1: "filterlim f (nhds (Gamma_incu_aux1 (s-1) (-1))) F'"
    using continuous_Gamma_incu_aux1_at_neg1_aux[of "s-1"] assms(1) by (simp add: f_def F'_def)
  have 2: "filterlim g F' F"
    unfolding F'_def
  proof (rule filterlim_at_withinI)
    show "(g \<longlongrightarrow> (s - 1, - 1)) F"
      by (auto simp: g_def case_prod_unfold F_def intro!: tendsto_eq_intros)
  next
    have "\<forall>\<^sub>F x in F. x \<in> {s. 0 < Re s} \<times> {z. 0 < Re z} - {(s, 0)}"
      by (auto simp: F_def eventually_at_topological)
    thus "\<forall>\<^sub>F x in F. g x \<in> {s. - 1 < Re s} \<times> {z. - 1 < Re z} - {(s - 1, - 1)}"
      by eventually_elim (auto simp: g_def)
  qed
  have "continuous F (\<lambda>x. Gamma_incu_aux1 (fst x - 1) (snd x - 1))"
    using filterlim_compose[OF 1 2]
    by (cases "F = bot")
       (simp_all add: continuous_def f_def g_def o_def case_prod_unfold F_def Lim_ident_at)
  thus ?thesis
    unfolding Gamma_incu_def case_prod_unfold F_def by (intro continuous_intros)
qed

lemma continuous_Gamma_incu_0_complex:
  assumes "Re s > 0"
  shows "continuous (at 0 within {z. Re z > 0}) (\<lambda>z. Gamma_incu s z)"
proof -
  define f where "f = (\<lambda>(s,z). Gamma_incu s z :: complex)"
  define g where "g = (\<lambda>z::complex. (s, z::complex))"
  have "continuous (at 0 within {z. Re z > 0}) (f \<circ> g)"
  proof (rule continuous_within_compose)
    show "continuous (at 0 within {z. 0 < Re z}) g"
      by (auto simp: g_def intro!: continuous_intros)
  next
    have "continuous (at (s,0) within ({s. Re s > 0} \<times> {z. Re z > 0})) f"
      unfolding f_def by (rule continuous_Gamma_incu_0_strong_complex) fact
    also have "(s, 0) = g 0"
      by (simp add: g_def)
    finally show "continuous (at (g 0) within g ` {z. 0 < Re z}) f"
      by (rule continuous_within_subset) (use assms(1) in \<open>auto simp: g_def\<close>)
  qed
  thus ?thesis
    by (simp add: f_def g_def case_prod_unfold o_def)
qed


text \<open>
  It is also straightforward to show that:
  \[\frac{\text{d}}{\text{d}z}\,\Gamma(s,z) = -z^{s-1} \exp(-z)\]
  This is, unsurprisingly, the opposite of the derivative of $\gamma(s,z)$.
\<close>
lemma has_field_derivative_Gamma_incu_complex:
  assumes z: "s \<in> (\<int>-\<int>\<^sub>\<le>\<^sub>0) \<or> (z :: complex) \<notin> \<real>\<^sub>\<le>\<^sub>0"
  shows   "((\<lambda>z. Gamma_incu s z) has_field_derivative (-(z powr' (s-1) * exp (-z)))) (at z within A)"
proof -
  define A where "A = (if s \<in> \<int>-\<int>\<^sub>\<le>\<^sub>0 then UNIV else -\<real>\<^sub>\<le>\<^sub>0 :: complex set)"
  show ?thesis
  proof (rule has_field_derivative_at_within)
    define h where "h = (\<lambda>u. u powr' (s - 1) * exp (-u))"
    have "((\<lambda>z. contour_integral (linepath 1 z) h) has_field_derivative h z) (at z)"
    proof (rule contour_integral_linepath_has_field_derivative)
      show "open A" "z \<in> A" "(1::complex) \<in> A"
        using z by (auto simp: A_def)
    next
      show "closed_segment 1 z \<subseteq> A"
      proof (cases "s \<in> (\<int>-\<int>\<^sub>\<le>\<^sub>0)")
        case False
        have "closed_segment (complex_of_real 1) z \<subseteq> - complex_of_real ` {..0}"
          by (rule starlike_slotted_complex_plane_left_aux) (use False z in auto)
        also have "complex_of_real ` {..0} = \<real>\<^sub>\<le>\<^sub>0"
          by (auto simp: nonpos_Reals_def)
        finally show ?thesis
          using False by (simp add: A_def)
      qed (auto simp: A_def)
    next
      show "h holomorphic_on A"
      proof (cases "s \<in> (\<int>-\<int>\<^sub>\<le>\<^sub>0)")
        case False
        thus ?thesis
          unfolding h_def by (auto intro!: holomorphic_intros simp: A_def)
      next
        case True
        then obtain n where n: "s = of_int n" "n > 0"
          by (auto elim!: Ints_cases simp: of_int_in_nonpos_Ints_iff)
        have *: "s - 1 = of_nat (nat (n - 1))"
          using n by auto
        show ?thesis
          unfolding h_def * powr'_of_nat by (intro holomorphic_intros)
      qed
    qed
    also have "?this \<longleftrightarrow> ((\<lambda>z. (z - 1) * Gamma_incu_aux1 (s - 1) (z - 1)) has_field_derivative h z) (at z)"
    proof (intro DERIV_cong_ev)
      have "eventually (\<lambda>x. x \<in> A) (nhds z)"
        by (rule eventually_nhds_in_open) (use z in \<open>auto simp: A_def\<close>)
      thus "\<forall>\<^sub>F x in nhds z. contour_integral (linepath 1 x) h = (x - 1) * Gamma_incu_aux1 (s - 1) (x - 1)"
      proof eventually_elim
        case (elim x)
        thus ?case
          unfolding h_def 
          by (intro ext Gamma_incu_aux1_conv_contour_integral [symmetric])
             (auto simp: A_def split: if_splits)
      qed
    qed auto
    finally have [derivative_intros]:
      "((\<lambda>z. (z - 1) * Gamma_incu_aux1 (s - 1) (z - 1)) has_field_derivative h z) (at z)" .
    have "((\<lambda>z. Gamma_incu s z) has_field_derivative (0 - h z)) (at z)"
      unfolding Gamma_incu_def by (rule derivative_eq_intros refl)+
    also have "0 - h z = -(z powr' (s - 1) * exp (-z))"
      using assms by (auto simp: h_def exp_diff exp_add field_simps powr_def exp_minus)
    finally show "(Gamma_incu s has_field_derivative - (z powr' (s - 1) * exp (- z))) (at z)" .
  qed
qed

lemma has_field_derivative_Gamma_incu_complex' [derivative_intros]:
  assumes "(f has_field_derivative f') (at z within A)" "s \<in> (\<int>-\<int>\<^sub>\<le>\<^sub>0) \<or> (f z :: complex) \<notin> \<real>\<^sub>\<le>\<^sub>0"
  shows   "((\<lambda>z. Gamma_incu s (f z)) 
             has_field_derivative (-(f z powr' (s-1) * exp (-f z)) * f')) (at z within A)"
  using DERIV_chain[OF has_field_derivative_Gamma_incu_complex[OF assms(2)] assms(1)]
  by (simp add: o_def)

lemma has_field_derivative_Gamma_incu_real:
  assumes "(f has_field_derivative f') (at x within A)" "s \<in> (\<int>-\<int>\<^sub>\<le>\<^sub>0) \<or> (f x :: real) > 0"
  shows   "((\<lambda>x. Gamma_incu s (f x)) has_field_derivative 
             (-(f x powr' (s-1) * exp (-f x) * f'))) (at x within A)"
proof -
  have *: "(Gamma_incu s has_real_derivative - (x powr' (s - 1) * exp (- x))) (at x)" 
    if x: "s \<in> (\<int>-\<int>\<^sub>\<le>\<^sub>0) \<or> x > 0" for x :: real
  proof -
    have "((\<lambda>x. Re (Gamma_incu (of_real s) (of_real x))) has_field_derivative 
            (-(x powr' (s-1) * exp (-x)))) (at x)"
    proof -
      have x': "complex_of_real s \<in> \<int> - \<int>\<^sub>\<le>\<^sub>0 \<or> complex_of_real x \<notin> \<real>\<^sub>\<le>\<^sub>0"
        using x by (auto simp: of_real_in_nonpos_Ints_iff)
      have "((\<lambda>x. Re (Gamma_incu (of_real s) (of_real x))) has_real_derivative 
              Re (-(of_real x powr' of_real (s - 1) * exp (-of_real x)))) (at x)"
        by (rule derivative_eq_intros refl x')+ simp
      also have "-(of_real x powr' of_real (s - 1) * exp (-of_real x)) = 
                 complex_of_real (-(x powr' (s - 1)) * exp (-x))"
        by (subst powr'_complex_of_real) (use x in \<open>auto simp flip: exp_of_real\<close>)
      also have "Re \<dots> = -(x powr' (s - 1)) * exp (-x)"
        by (subst Re_complex_of_real) auto
      finally show ?thesis by simp           
    qed
    also have "(\<lambda>x. Re (Gamma_incu (of_real s) (of_real x))) = Gamma_incu s"
      by (subst Gamma_incu_complex_of_real) auto
    finally show ?thesis .
  qed
  show ?thesis
    using DERIV_chain[OF *[OF assms(2)] assms(1)] by (simp add: o_def)
qed


lemma has_integral_Gamma_incu_complex_of_real':
  assumes x: "x > (0 :: real)"
  shows   "((\<lambda>z. exp ((s-1) * of_real (ln z) - complex_of_real z)) has_integral 
             (Gamma_incu s (of_real x))) {x..}"
proof -
  define h2 where "h2 = (\<lambda>z. exp ((s-1) * of_real (ln z) - of_real z))"
  define h where "h = (\<lambda>z. exp ((s-1) * ln (of_real z) - of_real z))"
  have "(h2 has_integral (Gamma_incu_aux2 s)) {1..}"
    unfolding Gamma_incu_aux2_def h2_def
    by (rule integrable_integral, rule set_lebesgue_integral_eq_integral(1))
       (use absolutely_integrable_incomplete_Gamma[of 1 "1 - s"] in \<open>simp add: algebra_simps\<close>)
  also have "?this \<longleftrightarrow> (h has_integral (Gamma_incu_aux2 s)) {1..}"
    by (intro has_integral_cong) (auto simp: h2_def h_def Ln_of_real)
  finally have 1: "(h has_integral (Gamma_incu s 1)) {1..}"
    by (simp add: Gamma_incu_def)

  have "(h has_integral (Gamma_incu s (of_real x))) {x..}"
  proof (cases "x < 1")
    case True
    have 2: "(h has_integral (-(Gamma_incu s (of_real 1)) - (-Gamma_incu s (of_real x)))) {x..1}"
      by (rule fundamental_theorem_of_calculus)
         (use x True in 
           \<open>auto simp: h_def Ln_of_real powr_def exp_diff exp_minus field_simps exp_add
                       powr'_complex intro!: derivative_eq_intros\<close>)
    have "(h has_integral 
             (Gamma_incu s 1 + (-(Gamma_incu s (of_real 1)) - (-Gamma_incu s (of_real x)))))
             ({1..} \<union> {x..1})"
      by (intro has_integral_Un 1 2) (use True in auto)
    also have "{1..} \<union> {x..1} = {x..}"
      using True by auto
    finally show ?thesis
      by (simp add: h_def)
  next
    case False
    have "(h has_integral (-(Gamma_incu s (of_real x)) - (-Gamma_incu s (of_real 1)))) {1..x}"
      by (rule fundamental_theorem_of_calculus)
         (use x False in \<open>auto simp: h_def Ln_of_real powr_def exp_diff exp_minus field_simps
                                     exp_add powr'_complex intro!: derivative_eq_intros\<close>)
    also have "?this \<longleftrightarrow> (h has_integral (-(Gamma_incu s (of_real x)) - (-Gamma_incu s (of_real 1)))) {1..<x}"
      by (rule has_integral_spike_set_eq) (rule negligible_subset[of "{x}"]; force; fail)+
    finally have 2: "(h has_integral (-(Gamma_incu s (of_real x)) - (-Gamma_incu s (of_real 1)))) {1..<x}" .
      
    have "{1..<x} - {1..} = {}"
      by auto
    hence "(h has_integral 
             (Gamma_incu s 1 - (-(Gamma_incu s (of_real x)) - (-Gamma_incu s (of_real 1)))))
             ({1..} - {1..<x})"
      by (intro has_integral_setdiff 1 2) (use False x in auto)
    also have "{1..} - {1..<x} = {x..}"
      using x False by auto
    finally show ?thesis
      by simp
  qed
  also have "?this \<longleftrightarrow> ?thesis"
    by (intro has_integral_cong) (use x in \<open>auto simp: h_def Ln_of_real\<close>)
  finally show ?thesis .
qed

lemma has_integral_Gamma_incu_complex_of_real:
  assumes x: "x > (0 :: real)"
  shows   "((\<lambda>t. complex_of_real t powr (s - 1) * of_real (exp (-t))) 
             has_integral (Gamma_incu s (of_real x))) {x..}"
proof -
  have "((\<lambda>z. exp ((s-1) * of_real (ln z) - complex_of_real z)) has_integral 
            (Gamma_incu s (of_real x))) {x..}"
    using x by (rule has_integral_Gamma_incu_complex_of_real')
  also have "?this \<longleftrightarrow> ?thesis"
    using x by (intro has_integral_cong) 
               (auto simp: powr_def field_simps exp_minus exp_diff exp_add Ln_of_real exp_of_real)
  finally show ?thesis .
qed

lemma has_integral_Gamma_incu_real:
  fixes x s :: real
  assumes "x > (0::real)"
  shows "((\<lambda>t. t powr (s - 1) * exp (-t)) has_integral Gamma_incu s x) {x..}"
proof -
  have "((\<lambda>t. of_real t powr (of_real s - 1) * of_real (exp (-t))) has_integral 
          (Gamma_incu (complex_of_real s) (of_real x))) {x..}"
    by (rule has_integral_Gamma_incu_complex_of_real) (use assms in auto)
  also have "?this \<longleftrightarrow> ((\<lambda>t. of_real (t powr (s - 1) * exp (-t))) has_integral 
                           (Gamma_incu (complex_of_real s) (of_real x))) {x..}"
    by (intro has_integral_cong) (use assms in \<open>auto simp: powr_Reals_eq\<close>)
  also have "Gamma_incu (complex_of_real s) (of_real x) = of_real (Gamma_incu s x)"
    by (rule Gamma_incu_complex_of_real)
  finally show ?thesis
    by (subst (asm) has_integral_complex_of_real_iff)
qed


subsection \<open>Identities\<close>

text \<open>
  All the facts we have collected so far now allow us to prove that
  $\gamma(s,z) + \Gamma(s,z) = \Gamma(s)$ if $\text{Re}(s) > 0$ (where the integral expressions
  for $\gamma$ and $\Gamma$ are valid). Then we use analytic continuation to lift this result
  to the rest of the domain.
\<close>
lemma Gamma_incl_plus_incu_complex_aux:
  assumes "s \<notin> \<int>\<^sub>\<le>\<^sub>0" "s - 1 \<in> \<nat> \<or> z \<notin> \<real>\<^sub>\<le>\<^sub>0"
  shows   "Gamma_incl s z + Gamma_incu s z = Gamma (s :: complex)"
proof -
  have nonpos_Reals_eq: "\<real>\<^sub>\<le>\<^sub>0 = complex_of_real ` {..0}"
    by (auto simp: nonpos_Reals_def)
  define A where "A = (\<lambda>s::complex. if s - 1 \<in> \<nat> then UNIV else -\<real>\<^sub>\<le>\<^sub>0 :: complex set)"
  have [simp, intro]: "open (A s)" for s
    by (auto simp: A_def)
  have conn: "connected (A s)" for s
    unfolding A_def nonpos_Reals_eq
    by (auto intro: starlike_imp_connected starlike_slotted_complex_plane_left)

  have eq1: "Gamma_incl s z + Gamma_incu s z = Gamma s" if s: "Re s > 0" and z: "z \<in> A s" for s z
  proof -
    from s have s': "s \<notin> \<int>\<^sub>\<le>\<^sub>0"
      by (auto elim!: nonpos_Ints_cases)
    define f where "f = (\<lambda>z. Gamma_incl s z + Gamma_incu s z - Gamma s)"

    have "f z = 0"
    proof (rule analytic_continuation[where f = f])
      show "f holomorphic_on A s"
      proof (cases "s - 1 \<in> \<nat>")
        case False
        thus ?thesis unfolding f_def A_def
          by (intro analytic_imp_holomorphic analytic_intros) 
             (use assms s' in \<open>auto simp: nonpos_Reals_def\<close>)
      next
        case True
        note [analytic_intros del] = analytic_Gamma_incl analytic_Gamma_incu
        from True obtain n' where n': "s - 1 = of_nat n'"
          by (elim Nats_cases)
        define n where "n = int (Suc n')"
        have n: "n > 0" "s = of_int n"
          using n' by (simp_all add: n_def algebra_simps)
        show ?thesis
          unfolding f_def n(2) by (intro analytic_imp_holomorphic analytic_intros) (use n in auto)
      qed
    next
      show "connected (A s)"
        by (rule conn)
    next
      show "complex_of_real ` {0<..} \<subseteq> A s"
        by (auto simp: complex_nonpos_Reals_iff A_def)
    next
      show "complex_of_real 1 islimpt complex_of_real ` {0<..}"
        by (intro islimpt_isCont_image) 
           (auto intro: continuous_intros open_imp_islimpt eventually_neq_at_within)
    next
      fix z assume "z \<in> complex_of_real ` {0<..}"
      then obtain x where x: "z = of_real x" "x > 0"
        by auto
      have 1: "((\<lambda>t. of_real t powr (s - 1) * of_real (exp (-t))) 
                 has_integral (Gamma_incu s (of_real x))) {x..}"
        by (rule has_integral_Gamma_incu_complex_of_real) (use x in auto)
      have 2: "((\<lambda>t. of_real t powr (s - 1) * of_real (exp (-t)))
                 has_integral Gamma_incl s (of_real x)) {0..x}"
        by (rule has_integral_Gamma_incl_complex_of_real) (use x s in auto)
      have "((\<lambda>t. of_real t powr (s - 1) * of_real (exp (-t))) 
                 has_integral (Gamma_incl s (of_real x) + Gamma_incu s (of_real x))) ({0..x} \<union> {x..})"
        by (intro has_integral_Un 1 2) (use x in auto)
      also have "{0..x} \<union> {x..} = {0..}"
        using x by auto
      finally have "((\<lambda>t. of_real t powr (s - 1) * of_real (exp (-t))) 
                       has_integral (Gamma_incl s z + Gamma_incu s z)) {0..}" by (simp add: x)
      moreover have "((\<lambda>t. of_real t powr (s - 1) * of_real (exp (-t))) 
                       has_integral (Gamma s)) {0..}"
        using Gamma_integral_complex[of s] s by (simp add: exp_minus field_simps)
      ultimately have "Gamma_incl s z + Gamma_incu s z = Gamma s"
        by (rule has_integral_unique)
      thus "f z = 0"
        by (simp add: f_def)
    qed (use z in \<open>auto simp: A_def\<close>)
    thus ?thesis
      by (simp add: f_def)
  qed    

  have eq2: "Gamma_incl s z + Gamma_incu s z = Gamma s"
    if s: "s \<notin> \<int>\<^sub>\<le>\<^sub>0" and z: "z \<notin> \<real>\<^sub>\<le>\<^sub>0" for s z :: complex
  proof -
    define g where "g = (\<lambda>s. Gamma_incl s z + Gamma_incu s z - Gamma s)"
    have "g s = 0"
    proof (rule analytic_continuation_open[where f = g])
      show "g holomorphic_on (-\<int>\<^sub>\<le>\<^sub>0)" unfolding g_def using z
        by (intro analytic_imp_holomorphic analytic_intros) 
           (use assms s in \<open>auto simp: nonpos_Reals_def\<close>)
    next
      show "{s. Re s > 0} \<subseteq> -\<int>\<^sub>\<le>\<^sub>0"
        by (auto elim!: nonpos_Ints_cases)
    next
      have "connected (UNIV - \<int>\<^sub>\<le>\<^sub>0 :: complex set)"
        by (rule connected_open_diff_countable) auto
      thus "connected (-\<int>\<^sub>\<le>\<^sub>0 :: complex set)"
        by (simp add: Compl_eq_Diff_UNIV)
    next
      have "1 \<in> {s. Re s > 0}"
        by auto
      thus "{s. Re s > 0} \<noteq> {}"
        by blast
    next
      fix s assume "s \<in> {s. Re s > 0}"
      thus "g s = 0"
        using eq1[of s z] z by (simp add: g_def A_def)
    qed (use s in \<open>auto simp: open_halfspace_Re_gt\<close>)
    thus ?thesis
      by (simp add: g_def)
  qed

  show ?thesis
  proof (cases "s - 1 \<in> \<nat>")
    case True
    then obtain n' where n': "s - 1 = of_nat n'"
      by (elim Nats_cases)
    define n where "n = int (Suc n')"
    have n: "n > 0" "s = of_int n"
      using n' by (simp_all add: n_def algebra_simps)
    show ?thesis
      using eq1[of s z] n unfolding A_def n' by (auto simp: A_def n')
  next
    case False
    thus ?thesis
      using eq2[of s z] assms by auto
  qed
qed


text \<open>
  The recurrence for $\Gamma(s,z)$:
\<close>
lemma Gamma_incu_plus1_complex_aux:
  assumes z: "z \<notin> \<real>\<^sub>\<le>\<^sub>0 \<or> s - 1 \<in> \<nat>"
  shows "Gamma_incu (s+1) z = s * Gamma_incu s z + z powr' s * exp (-z :: complex)"
proof -
  have eq1: "Gamma_incu (s+1) z = s * Gamma_incu s z + z powr' s * exp (-z :: complex)"
    if z: "z \<notin> \<real>\<^sub>\<le>\<^sub>0" for s z
  proof (rule analytic_continuation_open[where f = "\<lambda>s. Gamma_incu (s+1) z"])
    show "(\<lambda>s. Gamma_incu (s+1) z) holomorphic_on UNIV"
      by (intro analytic_imp_holomorphic analytic_intros) (use z in auto)
    show "(\<lambda>s. s * Gamma_incu s z + z powr' s * exp (-z)) holomorphic_on UNIV"
      by (intro analytic_imp_holomorphic analytic_intros) (use z in auto)
  next
    have "1 \<in> (-\<int>\<^sub>\<le>\<^sub>0 :: complex set)"
      by auto
    thus "(-\<int>\<^sub>\<le>\<^sub>0 :: complex set) \<noteq> {}"
      by blast
  next
    fix s :: complex assume s: "s \<in> -\<int>\<^sub>\<le>\<^sub>0"
    have "Gamma_incu (s + 1) z = Gamma (s+1) - Gamma_incl (s + 1) z"
      using Gamma_incl_plus_incu_complex_aux[of "s+1" z] plus_one_in_nonpos_Ints_imp[of s] s z 
      by (auto simp: algebra_simps)
    also have "\<dots> = s * (Gamma s - Gamma_incl s z) + z powr' s * exp (- z)"
      by (subst Gamma_incl_plus1_complex) (use s in \<open>auto simp: Gamma_plus1 ring_distribs\<close>)
    also have "Gamma s - Gamma_incl s z = Gamma_incu s z"
      using Gamma_incl_plus_incu_complex_aux[of s z ]s z by (auto simp: algebra_simps)
    finally show "Gamma_incu (s + 1) z = s * Gamma_incu s z + z powr' s * exp (- z)" .
  qed (auto simp: open_halfspace_Re_gt)

  have eq2: "Gamma_incu (s+1) z = s * Gamma_incu s z + z powr' s * exp (-z :: complex)"
    if "s - 1 \<in> \<nat>" for s z
  proof -
    note [analytic_intros del] = analytic_Gamma_incu
    from that obtain n' where n': "s - 1 = of_nat n'"
      by (elim Nats_cases)
    define n where "n = int (Suc n')"
    have n: "n > 0" "s = of_int n"
      using n' by (simp_all add: n_def algebra_simps)
    show ?thesis
    proof (rule analytic_continuation_open[where f = "\<lambda>z. Gamma_incu (s+1) z"])
      show "Gamma_incu (s + 1) holomorphic_on UNIV"
        using analytic_Gamma_incu_pos_int[OF analytic_on_ident[of UNIV], of "n + 1"] n
        by (auto intro: analytic_imp_holomorphic)
      show "(\<lambda>a. s * Gamma_incu s a + a powr' s * exp (- a)) holomorphic_on UNIV"
        unfolding n(2) using n(1) by (auto intro!: analytic_imp_holomorphic analytic_intros)
      show "Gamma_incu (s+1) z = s * Gamma_incu s z + z powr' s * exp (-z)" if "z \<in> -\<real>\<^sub>\<le>\<^sub>0" for z
        using that eq1[of z s] by simp
    qed auto
  qed

  show ?thesis
    using eq1[of z s] eq2[of s z] assms by auto
qed


theorem Gamma_incu_plus1_complex:
  assumes z: "z \<notin> \<real>\<^sub>\<le>\<^sub>0 \<or> s - 1 \<in> \<nat> \<or> (z = 0 \<and> Re s > 0)"
  shows "Gamma_incu (s+1) z = s * Gamma_incu s z + z powr' s * exp (-z :: complex)"
proof (cases "z = 0 \<and> s - 1 \<notin> \<nat>")
  case True
  define f where "f = (\<lambda>z. Gamma_incu (s+1) (of_real z) - s * Gamma_incu s z - z powr' s * exp (-z))"
  have [continuous_intros]:
    "continuous (at_right 0) (\<lambda>x. Gamma_incu s (of_real x))" if "Re s > 0" for s
  proof -
    have "continuous (at_right 0) (Gamma_incu s \<circ> complex_of_real)"
    proof (rule continuous_within_compose)
      show "continuous (at (complex_of_real 0) within complex_of_real ` {0<..}) (Gamma_incu s)"
        using continuous_Gamma_incu_0_complex unfolding of_real_0
        by (rule continuous_within_subset) (use \<open>Re s > 0\<close> in auto)
    qed (auto intro!: continuous_intros)
    thus ?thesis
      by (simp add: o_def)
  qed

  have "continuous (at_right 0) f"
    unfolding f_def using z True by (intro continuous_intros) (auto simp: Lim_ident_at)
  hence "(f \<longlongrightarrow> f 0) (at_right 0)"
    by (cases "at 0 within {z. Re z > 0} = bot") (auto simp: continuous_def Lim_ident_at)
  also have "?this \<longleftrightarrow> ((\<lambda>_::real. 0) \<longlongrightarrow> f 0) (at_right 0)"
  proof (rule filterlim_cong)
    have "eventually (\<lambda>z::real. z > 0) (at_right 0)"
      by (auto simp: eventually_at_topological)
    thus "eventually (\<lambda>z. f z = 0) (at_right 0)" unfolding f_def
      by eventually_elim (auto simp: Gamma_incu_plus1_complex_aux complex_nonpos_Reals_iff)
  qed auto
  finally have "f 0 = 0"
    by (subst (asm) tendsto_const_iff) auto
  thus ?thesis
    using True by (simp add: f_def field_simps)
qed (use Gamma_incu_plus1_complex_aux[of z s] assms in auto)

hide_fact Gamma_incu_plus1_complex_aux

lemma Gamma_incu_plus1_real:
  assumes z: "z > 0 \<or> (z = 0 \<and> s > 0)"
  shows "Gamma_incu (s+1) z = s * Gamma_incu s z + z powr' s * exp (-z :: real)"
proof -
  have "complex_of_real (Gamma_incu (s+1) z) = Gamma_incu (of_real s + 1) (of_real z)"
    by (subst Gamma_incu_complex_of_real [symmetric]) auto
  also have "\<dots> = complex_of_real (s * Gamma_incu s z + z powr' s * exp (-z))"
    by (subst Gamma_incu_plus1_complex)
       (use assms in \<open>auto simp flip: exp_of_real Gamma_incu_complex_of_real 
                           simp: powr'_complex_of_real\<close>)
  finally show ?thesis
    by (simp only: of_real_eq_iff)
qed


theorem Gamma_incl_plus_incu_complex:
  assumes "s \<notin> \<int>\<^sub>\<le>\<^sub>0" "z \<notin> \<real>\<^sub>\<le>\<^sub>0 \<or> s - 1 \<in> \<nat> \<or> (z = 0 \<and> Re s > 0)"
  shows   "Gamma_incl s z + Gamma_incu s z = Gamma (s :: complex)"
proof (cases "z = 0 \<and> s - 1 \<notin> \<nat>")
  case True
  define f where "f = (\<lambda>z. Gamma_incl s z + Gamma_incu s z)"
  from True and assms have s: "Re s > 0"
    by auto

  have [continuous_intros]:
    "continuous (at_right 0) (\<lambda>x. Gamma_incu s (of_real x))" if "Re s > 0" for s
  proof -
    have "continuous (at_right 0) (Gamma_incu s \<circ> complex_of_real)"
    proof (rule continuous_within_compose)
      show "continuous (at (complex_of_real 0) within complex_of_real ` {0<..}) (Gamma_incu s)"
        using continuous_Gamma_incu_0_complex unfolding of_real_0
        by (rule continuous_within_subset) (use \<open>Re s > 0\<close> in auto)
    qed (auto intro!: continuous_intros)
    thus ?thesis
      by (simp add: o_def)
  qed

  have "continuous_on {x. x \<ge> 0} (\<lambda>x. Gamma_incl s (complex_of_real x))"
    using assms s by (auto intro!: continuous_intros)
  hence [continuous_intros]: "continuous (at_right 0) (\<lambda>x. Gamma_incl s (complex_of_real x))"
    by (rule continuous_on_imp_continuous_within) auto

  have "continuous (at_right 0) f"
    unfolding f_def using s by (intro continuous_intros) auto
  hence "(f \<longlongrightarrow> f 0) (at_right 0)"
    by (cases "at 0 within {z. Re z > 0} = bot") (auto simp: continuous_def Lim_ident_at)
  also have "?this \<longleftrightarrow> ((\<lambda>_::real. Gamma s) \<longlongrightarrow> f 0) (at_right 0)"
  proof (rule filterlim_cong)
    have "eventually (\<lambda>z::real. z > 0) (at_right 0)"
      by (auto simp: eventually_at_topological)
    thus "eventually (\<lambda>z. f z = Gamma s) (at_right 0)" unfolding f_def
      by eventually_elim (subst Gamma_incl_plus_incu_complex_aux, use assms in auto)
  qed auto
  finally have "f 0 = Gamma s"
    by (subst (asm) tendsto_const_iff) auto
  thus ?thesis
    using True by (simp add: f_def field_simps)
qed (use Gamma_incl_plus_incu_complex_aux[of s z] assms in auto)

hide_fact Gamma_incl_plus_incu_complex_aux

lemma Gamma_incl_plus_incu_real:
  assumes "s \<notin> \<int>\<^sub>\<le>\<^sub>0" "z > 0 \<or> (z = 0 \<and> s > 0)"
  shows   "Gamma_incl s z + Gamma_incu s z = Gamma (s :: real)"
proof (cases "z = 0")
  case True
  thus ?thesis
    using Gamma_incl_plus_incu_complex[of s z] assms
          Gamma_incu_complex_of_real[of s z] Gamma_complex_of_real[of s]
    by (auto simp: Gamma_incl_def of_real_in_nonpos_Ints_iff)
next
  case False
  thus ?thesis
    using Gamma_incl_plus_incu_complex[of s z] assms
    by (auto simp: Gamma_incl_complex_of_real Gamma_incu_complex_of_real Gamma_complex_of_real
                   of_real_in_nonpos_Ints_iff simp flip: of_real_add)
qed


subsection \<open>Derivative of $\gamma(s,z)$\<close>

text \<open>
  Via the relationship with $\Gamma(s)$ and $\Gamma(s,z)$, it is now also straightforward
  to prove the derivative of $\gamma(s,z)$:
\<close>
(* TODO: case of s a positive integer *)
lemma has_field_derivative_Gamma_incl_complex:
  fixes s z :: complex
  assumes "s \<notin> \<int>\<^sub>\<le>\<^sub>0" "s - 1 \<in> \<nat> \<or> z \<notin> \<real>\<^sub>\<le>\<^sub>0"
  shows   "((\<lambda>x. Gamma_incl s x) has_field_derivative (z powr' (s-1) * exp (-z))) (at z within A)"
proof (rule has_field_derivative_at_within)
  have "s \<in> \<int>" if "s - 1 \<in> \<nat>"
    using that Ints_1 diff_in_Ints_iff_right minus_in_Ints_iff uminus_in_nonpos_Ints_iff by blast
  hence "((\<lambda>z. Gamma s - Gamma_incu s z) has_field_derivative 
          (z powr' (s - 1) * exp (-z))) (at z)"
    using assms by (auto intro!: derivative_eq_intros)
  also have "?this \<longleftrightarrow> ((\<lambda>x. Gamma_incl s x) has_field_derivative (z powr' (s-1) * exp (-z))) (at z)"
  proof (rule DERIV_cong_ev)
    have "eventually (\<lambda>x. x \<in> (if s - 1 \<in> \<nat> then UNIV else -\<real>\<^sub>\<le>\<^sub>0)) (nhds z)"
      by (rule eventually_nhds_in_open) (use assms in auto)
    thus "\<forall>\<^sub>F x in nhds z. Gamma s - Gamma_incu s x = Gamma_incl s x"
    proof eventually_elim
      case (elim x)
      thus ?case
        using Gamma_incl_plus_incu_complex[of s x, symmetric] assms
        by (auto simp: algebra_simps split: if_splits)
    qed
  qed (auto simp: powr'_complex)
  finally show \<dots> .
qed

lemma has_field_derivative_Gamma_incl_complex' [derivative_intros]:
  fixes f :: "_ \<Rightarrow> complex"
  assumes "(f has_field_derivative f') (at x within A)" "s \<notin> \<int>\<^sub>\<le>\<^sub>0" "s - 1 \<in> \<nat> \<or> f x \<notin> \<real>\<^sub>\<le>\<^sub>0"
  shows   "((\<lambda>x. Gamma_incl s (f x)) has_field_derivative 
             (f x powr' (s-1) * exp (-f x) * f')) (at x within A)"
  using DERIV_chain[OF has_field_derivative_Gamma_incl_complex[OF assms(2,3)] assms(1)]
  by (simp add: o_def)

lemma has_field_derivative_Gamma_incl_real [derivative_intros]:
  fixes f :: "_ \<Rightarrow> real"
  assumes "(f has_field_derivative f') (at x within A)" and s: "s \<notin> \<int>\<^sub>\<le>\<^sub>0" and fx: "f x > 0"
  shows   "((\<lambda>x. Gamma_incl s (f x)) has_field_derivative 
             (f x powr (s-1) * exp (-f x) * f')) (at x within A)"
proof -
  have *: "(Gamma_incl s has_real_derivative (x powr (s - 1) * exp (- x))) (at x)" 
    if x: "x > 0" for x :: real
  proof -
    have "((\<lambda>x. Re (Gamma_incl (of_real s) (of_real x))) has_field_derivative 
            ((x powr' (s-1) * exp (-x)))) (at x)"
    proof -
      have x': "complex_of_real x \<notin> \<real>\<^sub>\<le>\<^sub>0" and s': "complex_of_real s \<notin> \<int>\<^sub>\<le>\<^sub>0"
        using x s by (auto simp: of_real_in_nonpos_Ints_iff)
      show ?thesis
        by (rule derivative_eq_intros refl x' s')+
           (use x in \<open>auto simp: powr'_Reals_eq exp_of_real simp flip: of_real_minus\<close>)
    qed
    also have "?this \<longleftrightarrow> (Gamma_incl s has_field_derivative (x powr (s-1) * exp (-x))) (at x)"
    proof (rule DERIV_cong_ev)
      have "eventually (\<lambda>t. t \<in> {0<..}) (nhds x)"
        by (rule eventually_nhds_in_open) (use x in auto)
      thus "\<forall>\<^sub>F x in nhds x. Re (Gamma_incl (complex_of_real s) (complex_of_real x)) = 
              Gamma_incl s x"
        by eventually_elim (auto simp: Gamma_incl_complex_of_real)
    qed (use x in \<open>auto simp: powr'_real\<close>)
    finally show ?thesis .
  qed
  show ?thesis
    using DERIV_chain[OF *[OF fx] assms(1)] by (simp add: o_def)
qed


subsection \<open>Special values\<close>

text \<open>
  Lastly, we examine the values of $\Gamma(s,z)$ specifically for
  $z = 0$, $s$ is a positive integer, $s = \frac{1}{2}$, and $z\to\infty$.
\<close>

lemma Gamma_incl_0_left: "Gamma_incl 0 z = 0"
  by (simp add: Gamma_incl_def)

lemma Gamma_incl_0_right [simp]: "s \<noteq> 0 \<Longrightarrow> Gamma_incl s 0 = 0"
  by (auto simp: Gamma_incl_def)

lemma Gamma_incu_0_right_complex [simp]: "Re s > 0 \<Longrightarrow> Gamma_incu s 0 = Gamma (s::complex)"
  by (cases "s \<in> \<int>\<^sub>\<le>\<^sub>0"; cases "s = 0") 
     (use Gamma_incl_plus_incu_complex[of s 0] in \<open>auto elim!: nonpos_Ints_cases\<close>)

lemma Gamma_incu_0_right_real [simp]: "s > 0 \<Longrightarrow> Gamma_incu s 0 = Gamma (s::real)"
  by (cases "s \<in> \<int>\<^sub>\<le>\<^sub>0"; cases "s = 0") 
     (use Gamma_incl_plus_incu_real[of s 0] in \<open>auto elim!: nonpos_Ints_cases\<close>)

text \<open>
  The following theorem now summarises the behaviour of $\Gamma(s,z)$ at $z = 0$ and 
  $\text{Re}(s)>0$: when approaching from direction $\text{Re}(z)>0$, $\Gamma(s,z)\to \Gamma(s')$
  as $s\to s'$ and $z\to 0$.
\<close>
theorem tendsto_Gamma_incu_0_right_complex:
  assumes "(f \<longlongrightarrow> s) F" "(g \<longlongrightarrow> 0) F"
  assumes "Re s > 0" "eventually (\<lambda>x. Re (g x) > 0) F"
  shows   "((\<lambda>x. Gamma_incu (f x) (g x)) \<longlongrightarrow> Gamma s) F"
proof -
  have 1: "((\<lambda>x. (f x, g x)) \<longlongrightarrow> (s, 0)) F"
    by (auto intro!: tendsto_intros assms(1,2))
  have "eventually (\<lambda>x. f x \<in> {s. Re s > 0}) F"
    by (intro eventually_compose_filterlim[OF _ assms(1)] eventually_nhds_in_open)
       (use assms(3) in \<open>auto simp: open_halfspace_Re_gt\<close>)
  hence 2: "\<forall>\<^sub>F x in F. (f x, g x) \<in> {s. 0 < Re s} \<times> {z. 0 < Re z}"
    using assms(4) by eventually_elim auto
  show ?thesis
    using continuous_within_tendsto_compose[OF continuous_Gamma_incu_0_strong_complex 2 1] assms(3)
    by simp
qed



lemma Gamma_incl_1_left: "Gamma_incl 1 z = 1 - exp (-z)"
  by (auto simp: Gamma_incl_def Gamma_rincl_1_left)

lemma Gamma_incu_1_left_complex: "Gamma_incu 1 (z::complex) = exp (-z)"
  using Gamma_incl_plus_incu_complex[of 1 z] by (simp add: Gamma_incl_1_left)

lemma Gamma_incu_1_left_real: "z \<ge> 0 \<Longrightarrow> Gamma_incu 1 (z::real) = exp (-z)"
  using Gamma_incl_plus_incu_real[of 1 z] by (cases "z = 0") (auto simp: Gamma_incl_1_left)


theorem Gamma_incl_of_nat_left_complex:
  fixes z :: complex
  shows "Gamma_incl (of_nat (Suc n)) z = fact n * (1 - exp (-z) * (\<Sum>k\<le>n. z ^ k / fact k))"
proof -
  have "Gamma_incl (of_nat (Suc n)) z = 
          Gamma (1 + complex_of_nat n) * Gamma_rincl (of_nat (Suc n)) z"
    by (simp add: Gamma_incl_def)
  also have "Gamma (1 + complex_of_nat n) = fact n"
    by (rule Gamma_fact)
  also have "Gamma_rincl (of_nat (Suc n)) z = 1 - exp (- z) * (\<Sum>k\<le>n. z ^ k / fact k)"
    by (rule Gamma_rincl_of_nat_left_complex)
  finally show ?thesis .
qed

lemma Gamma_incl_of_nat_left_real:
  fixes z :: real
  shows "Gamma_incl (of_nat (Suc n)) z = fact n * (1 - exp (-z) * (\<Sum>k\<le>n. z ^ k / fact k))"
proof -
  have "Gamma_incl (of_nat (Suc n)) z = Gamma (1 + real n) * Gamma_rincl (of_nat (Suc n)) z"
    by (simp add: Gamma_incl_def)
  also have "Gamma (1 + real n) = fact n"
    by (rule Gamma_fact)
  also have "Gamma_rincl (real (Suc n)) z = 1 - exp (- z) * (\<Sum>k\<le>n. z ^ k / fact k)"
    by (rule Gamma_rincl_of_nat_left_real)
  finally show ?thesis .
qed

theorem Gamma_incu_of_nat_left_complex:
  fixes z :: complex
  shows "Gamma_incu (of_nat (Suc n)) z = fact n * exp (-z) * (\<Sum>k\<le>n. z ^ k / fact k)"
proof -
  have "complex_of_nat (Suc n) \<notin> \<int>\<^sub>\<le>\<^sub>0"
    unfolding of_nat_in_nonpos_Ints_iff by simp
  hence "Gamma_incu (of_nat (Suc n)) z = Gamma (of_nat (Suc n)) - Gamma_incl (of_nat (Suc n)) z"
    by (subst Gamma_incl_plus_incu_complex [of _ z, symmetric]) auto
  also have "Gamma (of_nat (Suc n)) = fact n"
    by (simp add: Gamma_fact)
  finally show ?thesis
    by (subst (asm) Gamma_incl_of_nat_left_complex) (auto simp: algebra_simps)
qed

lemma Gamma_incu_of_nat_left_real:
  fixes z :: real
  shows "Gamma_incu (of_nat (Suc n)) z = fact n * exp (-z) * (\<Sum>k\<le>n. z ^ k / fact k)"
proof -
  have "complex_of_real (Gamma_incu (of_nat (Suc n)) z) = Gamma_incu (of_nat (Suc n)) (of_real z)"
    by (simp flip: Gamma_incu_complex_of_real)
  also have "\<dots> = complex_of_real (fact n * exp (-z) * (\<Sum>k\<le>n. z ^ k / fact k))"
    by (subst Gamma_incu_of_nat_left_complex) (simp_all flip: exp_of_real)
  finally show ?thesis
    by (simp only: of_real_eq_iff)
qed


text \<open>
  Via the hypergeometric representation, it is easy to see that for $\gamma(\frac{1}{2}, z)$
  and $\Gamma(\frac{1}{2}, z)$ have representations in terms of $\text{erf}(\sqrt{z})$ and
  $text{erfc}(\sqrt{z})$, respectively:
\<close>
theorem Gamma_incl_one_half_left_complex:
  assumes "z = 0 \<or> z \<notin> \<real>\<^sub>\<le>\<^sub>0"
  shows   "Gamma_incl (1/2) (z :: complex) = sqrt pi * erf (csqrt z)"
proof (cases "z = 0")
  case False
  thus ?thesis
    unfolding Gamma_incl_def
    by (subst Gamma_rincl_one_half_left_complex) (use assms in \<open>auto simp: Gamma_one_half_complex\<close>)
qed auto

lemma Gamma_incl_one_half_left_real:
  assumes "z \<ge> 0"
  shows   "Gamma_incl (1/2) (z :: real) = sqrt pi * erf (sqrt z)"
  unfolding Gamma_incl_def
  by (subst Gamma_rincl_one_half_left_real) (use assms in \<open>auto simp: Gamma_one_half_real\<close>)

lemma Gamma_incu_one_half_left_complex:
  assumes "z = 0 \<or> z \<notin> \<real>\<^sub>\<le>\<^sub>0"
  shows   "Gamma_incu (1/2) (z :: complex) = sqrt pi * erfc (csqrt z)"
proof -
  have "Gamma_incl (1 / 2) z + Gamma_incu (1 / 2) z = Gamma (1 / 2)"
    by (rule Gamma_incl_plus_incu_complex) (use assms in auto)
  thus ?thesis using assms
    by (auto simp: Gamma_incl_one_half_left_complex Gamma_one_half_complex erfc_def field_simps)
qed

lemma Gamma_incu_one_half_left_real:
  assumes "z \<ge> 0"
  shows   "Gamma_incu (1/2) (z :: real) = sqrt pi * erfc (sqrt z)"
proof -
  have "Gamma_incl (1 / 2) z + Gamma_incu (1 / 2) z = Gamma (1 / 2)"
    by (rule Gamma_incl_plus_incu_real) (use assms in auto)
  thus ?thesis using assms
    by (auto simp: Gamma_incl_one_half_left_real Gamma_one_half_real erfc_def field_simps)
qed



(* 
  Could be generalised to Re going_to at_top within some cone, by going down from z
  to the real axis and bounding the integrand and the length of the vertical line.
*)
text \<open>
  $\Gamma(s,x)$ vanishes as $x\to\infty$.
\<close>
lemma Gamma_incu_at_top_complex: "((\<lambda>z. Gamma_incu s (complex_of_real z)) \<longlongrightarrow> 0) at_top"
proof -
  define h where "h = (\<lambda>z. exp ((s-1) * of_real (ln z) - complex_of_real z))"
  have smallo: "(\<lambda>t. exp ((Re s - 1) * ln t - t)) \<in> o(\<lambda>t. exp (-t/2))"
    by (real_asymp simp: field_simps)
  have "eventually (\<lambda>t. exp ((Re s - 1) * ln t - t) \<le> exp (-t/2)) at_top"
    using landau_o.smallD[OF smallo, of 1] by simp
  then obtain x0 where x0: "\<And>t. t \<ge> x0 \<Longrightarrow> exp ((Re s - 1) * ln t - t) \<le> exp (-t/2)"
    unfolding eventually_at_top_linorder by blast

  have "eventually (\<lambda>x. norm (Gamma_incu s (of_real x)) \<le> 2 * exp (-x/2)) at_top"
    using eventually_gt_at_top[of x0] eventually_gt_at_top[of 1]
  proof eventually_elim
    case x: (elim x)
    have h: "(h has_integral (Gamma_incu s (of_real x))) {x..}"
      unfolding h_def by (rule has_integral_Gamma_incu_complex_of_real') (use x in auto)
    have bound: "((\<lambda>t. exp (-t/2)) has_integral (2 * exp (-x/2))) {x..}"
      using has_integral_exp_minus_to_infinity[of "1/2" x] x by (simp add: mult_ac)
    have "norm (integral {x..} h) \<le> integral {x..} (\<lambda>t. exp (-t/2))"
    proof (rule integral_norm_bound_integral)
      fix t assume t: "t \<in> {x..}"
      have "norm (h t) = exp ((Re s - 1) * ln t - t)"
        by (simp add: h_def)
      also have "\<dots> \<le> exp (-t/2)"
        by (rule x0) (use x t in auto)
      finally show "norm (h t) \<le> exp (-t/2)" .
    qed (use bound h in \<open>simp_all add: has_integral_iff\<close>)
    thus "norm (Gamma_incu s (of_real x)) \<le> 2 * exp (-x/2)"
      using bound h by (auto simp: has_integral_iff)
  qed
  moreover have "((\<lambda>x. 2 * exp (-x/2::real)) \<longlongrightarrow> 0) at_top"
    by real_asymp
  ultimately show ?thesis
    by (rule Lim_null_comparison)
qed

lemma Gamma_incu_at_top_real: "((\<lambda>z. Gamma_incu s (z::real)) \<longlongrightarrow> 0) at_top"
proof -
  have "((\<lambda>z. Re (Gamma_incu s (complex_of_real z))) \<longlongrightarrow> Re 0) at_top"
    by (rule tendsto_Re Gamma_incu_at_top_complex)+
  also have "(\<lambda>z. Re (Gamma_incu s (complex_of_real z))) = Gamma_incu s"
    by (simp add: Gamma_incu_complex_of_real)
  finally show ?thesis
    by simp
qed

text \<open>
  Consequently, $\gamma(s,z) \to \Gamma(s)$ as $z\to\infty$:
\<close>
lemma Gamma_incl_at_top_complex:
  assumes "s \<notin> \<int>\<^sub>\<le>\<^sub>0"
  shows   "((\<lambda>z. Gamma_incl s (complex_of_real z)) \<longlongrightarrow> Gamma s) at_top"
proof -
  have "((\<lambda>z. Gamma s - Gamma_incu s (complex_of_real z)) \<longlongrightarrow> Gamma s - 0) at_top"
    by (intro tendsto_intros Gamma_incu_at_top_complex)
  also have "eventually (\<lambda>z. Gamma s - Gamma_incu s (of_real z) = Gamma_incl s (of_real z)) at_top"
    using eventually_gt_at_top[of 0]
  proof eventually_elim
    case (elim z)
    thus ?case
      by (subst Gamma_incl_plus_incu_complex [of s z, symmetric]) (use assms in auto)
  qed
  finally show ?thesis
    by simp
qed

lemma Gamma_incl_at_top_real:
  assumes "s \<notin> \<int>\<^sub>\<le>\<^sub>0"
  shows   "((\<lambda>z. Gamma_incl s (z::real)) \<longlongrightarrow> Gamma s) at_top"
proof -
  have "((\<lambda>z. Re (Gamma_incl (of_real s) (complex_of_real z))) \<longlongrightarrow> Re (Gamma (of_real s))) at_top"
    by (rule tendsto_Re Gamma_incl_at_top_complex)+ 
       (use assms in \<open>auto simp: of_real_in_nonpos_Ints_iff\<close>)
  also have "?this \<longleftrightarrow> ?thesis"
  proof (intro filterlim_cong)
    show "\<forall>\<^sub>F x in at_top. Re (Gamma_incl (complex_of_real s) (complex_of_real x)) = Gamma_incl s x"
      using eventually_gt_at_top[of 0] by eventually_elim (auto simp: Gamma_incl_complex_of_real)
  qed (auto simp: Gamma_complex_of_real)
  finally show ?thesis .
qed

end
