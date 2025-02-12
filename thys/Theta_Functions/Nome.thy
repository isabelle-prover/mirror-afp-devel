section \<open>Conversion from the complex plane to the nome\<close>
theory Nome
  imports "HOL-Complex_Analysis.Complex_Analysis" "HOL-Library.Going_To_Filter"
begin

definition to_nome :: "complex \<Rightarrow> complex" 
  where "to_nome z = exp (\<i> * of_real pi * z)" 

lemma to_nome_nonzero [simp]: "to_nome z \<noteq> 0"
  by (simp add: to_nome_def)

lemma norm_to_nome: "norm (to_nome z) = exp (-pi * Im z)"
  by (simp add: to_nome_def)

lemma to_nome_add: "to_nome (z + w) = to_nome z * to_nome w"
  by (simp add: to_nome_def ring_distribs exp_add)

lemma to_nome_diff: "to_nome (z - w) = to_nome z / to_nome w"
  by (simp add: to_nome_def ring_distribs exp_diff)

lemma to_nome_minus: "to_nome (-z) = inverse (to_nome z)"
  by (simp add: to_nome_def exp_minus field_simps)

lemma to_nome_cnj: "to_nome (cnj z) = cnj (to_nome (-z))"
  by (simp add: to_nome_def exp_cnj)

lemma to_nome_power: "to_nome z ^ n = to_nome (of_nat n * z)"
  by (simp add: to_nome_def mult_ac flip: exp_of_nat_mult)

lemma to_nome_power_int: "to_nome z powi n = to_nome (of_int n * z)"
  by (auto simp: power_int_def to_nome_power simp flip: to_nome_minus)

lemma cis_conv_to_nome: "cis x = to_nome (of_real (x / pi))"
  by (simp add: cis_conv_exp to_nome_def)

lemma to_nome_powr: 
  assumes "Re z \<in> {-1<..1}"
  shows   "to_nome z powr w = to_nome (z * w)"
proof -
  have "to_nome z powr w = exp (w * ln (exp (\<i> * of_real pi * z)))"
    by (simp add: to_nome_def powr_def)
  also have "ln (exp (\<i> * of_real pi * z)) = \<i> * of_real pi * z"
    using mult_strict_left_mono[of "-1" "Re z" pi]
    by (subst Ln_exp) (use assms in auto)
  also have "exp (w * \<dots>) = to_nome (z * w)"
    by (simp add: to_nome_def mult_ac)
  finally show ?thesis .
qed


lemma to_nome_0 [simp]: "to_nome 0 = 1"
  by (simp add: to_nome_def)

lemma to_nome_1 [simp]: "to_nome 1 = -1"
  and to_nome_neg1 [simp]: "to_nome (-1) = -1"
  by (simp_all add: to_nome_def exp_minus)

lemma to_nome_of_nat [simp]: "to_nome (of_nat n) = (-1) ^ n"
  by (simp add: to_nome_def complex_eq_iff Re_exp Im_exp)

lemma to_nome_of_int [simp]: "to_nome (of_int n) = (-1) powi n"
  by (simp add: to_nome_def complex_eq_iff Re_exp Im_exp)

lemma to_nome_one_half [simp]: "to_nome (1 / 2) = \<i>"
  by (simp add: to_nome_def exp_eq_polar)

lemma to_nome_three_halves [simp]: "to_nome (3 / 2) = -\<i>"
proof -
  have "to_nome (1 + 1 / 2) = -\<i>"
    by (subst to_nome_add) auto
  thus ?thesis
    by simp
qed

lemma to_nome_eq_1_iff: "to_nome z = 1 \<longleftrightarrow> (\<exists>n. even n \<and> z = of_int n)"
proof -
  have "to_nome z = 1 \<longleftrightarrow> (\<exists>n. z = complex_of_int (2 * n))"
    unfolding to_nome_def by (subst exp_eq_1) (auto simp: complex_eq_iff)
  also have "(\<exists>n. z = complex_of_int (2 * n)) \<longleftrightarrow> (\<exists>n. even n \<and> z = of_int n)"
    by (metis dvd_def)
  finally show ?thesis .
qed

lemma to_nome_eq_neg1_iff: "to_nome z = -1 \<longleftrightarrow> (\<exists>n. odd n \<and> z = of_int n)"
proof -
  have "to_nome z = -1 \<longleftrightarrow> to_nome (z + 1) = 1"
    by (simp add: to_nome_add minus_equation_iff[of _ 1] eq_commute[of "-1"])
  also have "\<dots> \<longleftrightarrow> (\<exists>n. even n \<and> z + 1 = of_int n)"
    by (rule to_nome_eq_1_iff)
  also have "(\<exists>n. even n \<and> z + 1 = of_int n) \<longleftrightarrow> (\<exists>n. odd n \<and> z = of_int n)"
  proof (intro iffI; elim exE)
    fix n assume "even n \<and> z + 1 = of_int n"
    thus "\<exists>n. odd n \<and> z = of_int n"
      by (intro exI[of _ "n - 1"]) (auto simp: algebra_simps)
  next
    fix n assume "odd n \<and> z = of_int n"
    thus "\<exists>n. even n \<and> z + 1 = of_int n"
      by (intro exI[of _ "n + 1"]) (auto simp: algebra_simps)
  qed
  finally show ?thesis .
qed

lemma to_nome_eq_1_iff': "to_nome z = 1 \<longleftrightarrow> (z / 2) \<in> \<int>"
proof
  assume "to_nome z = 1"
  then obtain n where "z = of_int n" "even n"
    by (subst (asm) to_nome_eq_1_iff) auto
  thus "z / 2 \<in> \<int>"
    by (auto elim!: evenE)
next
  assume "(z / 2) \<in> \<int>"
  then obtain n where "z / 2 = of_int n"
    by (auto elim!: Ints_cases)
  hence "z = of_int (2 * n)" "even (2 * n)"
    by simp_all
  thus "to_nome z = 1"
    using to_nome_eq_1_iff[of z] by blast
qed

lemma to_nome_eq_neg1_iff':"to_nome z = -1 \<longleftrightarrow> ((z-1) / 2) \<in> \<int>"
proof
  assume "to_nome z = -1"
  then obtain n where "z = of_int n" "odd n"
    by (subst (asm) to_nome_eq_neg1_iff) auto
  thus "((z-1) / 2) \<in> \<int>"
    by (auto elim!: oddE)
next
  assume "((z-1) / 2) \<in> \<int>"
  then obtain n where "((z-1) / 2) = of_int n"
    by (auto elim!: Ints_cases)
  hence "z = of_int (2 * n + 1)" "odd (2 * n + 1)"
    by (auto simp: algebra_simps)
  thus "to_nome z = -1"
    using to_nome_eq_neg1_iff[of z] by blast
qed

lemma to_nome_neg_one_half [simp]: "to_nome (-(1 / 2)) = -\<i>"
  by (simp add: to_nome_def exp_eq_polar)

lemma to_nome_2 [simp]: "to_nome 2 = 1"
  by (simp add: to_nome_def exp_eq_polar mult.commute[of pi])


lemma holomorphic_to_nome [holomorphic_intros]:
  "f holomorphic_on A \<Longrightarrow> (\<lambda>z. to_nome (f z)) holomorphic_on A"
  unfolding to_nome_def by (intro holomorphic_intros)

lemma analytic_to_nome [analytic_intros]:
  "f analytic_on A \<Longrightarrow> (\<lambda>z. to_nome (f z)) analytic_on A"
  unfolding to_nome_def by (intro analytic_intros)

lemma tendsto_to_nome [tendsto_intros]:
  assumes "(f \<longlongrightarrow> w) F"
  shows   "((\<lambda>z. to_nome (f z)) \<longlongrightarrow> to_nome w) F"
  using assms unfolding to_nome_def by (intro tendsto_intros)

lemma continuous_on_to_nome [continuous_intros]:
  assumes "continuous_on A f"
  shows   "continuous_on A (\<lambda>z. to_nome (f z))"
  using assms unfolding to_nome_def by (intro continuous_intros)

lemma continuous_to_nome [continuous_intros]:
  assumes "continuous F f"
  shows   "continuous F (\<lambda>z. to_nome (f z))"
  unfolding to_nome_def by (intro continuous_intros assms)


lemma tendsto_0_to_nome:
  assumes "filterlim (\<lambda>x. Im (f x)) at_top F"
  shows   "filterlim (\<lambda>x. to_nome (f x)) (nhds 0) F"
proof -
  have "((\<lambda>x. exp (-(pi * x))) \<longlongrightarrow> 0) at_top"
    by real_asymp
  hence "((\<lambda>x. exp (- (pi * Im (f x)))) \<longlongrightarrow> 0) F"
    by (rule filterlim_compose) fact
  hence "filterlim (\<lambda>x. norm (to_nome (f x))) (nhds 0) F"
    by (simp add: norm_to_nome)
  thus ?thesis
    by (simp only: tendsto_norm_zero_iff)
qed

lemma tendsto_0_to_nome': "(to_nome \<longlongrightarrow> 0) (Im going_to at_top)"
  using tendsto_0_to_nome by fastforce
  
lemma filterlim_at_0_to_nome:
  assumes "filterlim (\<lambda>x. Im (f x)) at_top F"
  shows   "filterlim (\<lambda>x. to_nome (f x)) (at 0) F"
  by (intro filterlim_atI tendsto_0_to_nome assms) auto

end