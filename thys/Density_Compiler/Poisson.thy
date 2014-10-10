(*
  Theory: Poisson.thy
  Author: Manuel Eberl
*)

header {* Poisson Distribution *}

theory Poisson
imports Probability PDF_Misc
begin

class poisson = linordered_semiring +
  fixes poisson_density :: "real \<Rightarrow> 'a \<Rightarrow> ereal"
  fixes poisson_density' :: "real \<Rightarrow> 'a \<Rightarrow> real"
  assumes measurable_poisson_density[measurable]: 
            "split poisson_density \<in> borel_measurable (borel \<Otimes>\<^sub>M count_space UNIV)"
  assumes poisson_density_ge_0: "rate \<ge> 0 \<Longrightarrow> poisson_density rate x \<ge> 0"
  assumes poisson_density_of_neg_eq_0: "x < 0 \<Longrightarrow> poisson_density rate x = 0"
  assumes poisson_density_integral_eq_1: 
            "rate \<ge> 0 \<Longrightarrow> (\<integral>\<^sup>+x. poisson_density rate x \<partial>count_space UNIV) = 1"
  assumes poisson_density_real[simp]: "real (poisson_density rate x) = poisson_density' rate x"
  assumes poisson_density'_ereal[simp]: "ereal (poisson_density' rate x) = poisson_density rate x"
begin

  definition "poisson_space rate \<equiv> density (count_space UNIV) (poisson_density rate)"

  lemma poisson_density'_ge_0: "rate \<ge> 0 \<Longrightarrow> poisson_density' rate x \<ge> 0"
    using poisson_density_ge_0 
    by (simp add: poisson_density'_ereal[symmetric] del: poisson_density'_ereal)

  lemma poisson_density'_of_neg_eq_0: "x < 0 \<Longrightarrow> poisson_density' rate x = 0"
    using poisson_density_of_neg_eq_0 
    by (simp add: poisson_density'_ereal[symmetric] del: poisson_density'_ereal)

  lemma space_poisson_space: "space (poisson_space rate) = UNIV"
    unfolding poisson_space_def by simp

  lemma sets_poisson_space: "sets (poisson_space rate) = UNIV"
    unfolding poisson_space_def by simp

  lemma emeasure_poisson_space: 
      "emeasure (poisson_space rate) A = 
         \<integral>\<^sup>+x. poisson_density rate x * indicator A x \<partial>count_space UNIV"
    by (simp add: poisson_space_def emeasure_density)

  lemma prob_space_poisson[intro]: "rate \<ge> 0 \<Longrightarrow> prob_space (poisson_space rate)"
    by (auto intro!: prob_spaceI 
             simp: poisson_density_integral_eq_1 emeasure_poisson_space space_poisson_space)

  lemma measurable_poisson_space_eq1[simp]:
    "measurable (poisson_space rate) N = measurable (count_space UNIV) N"
    by (intro measurable_cong_sets) (simp_all add: sets_poisson_space)

  lemma measurable_poisson_space_eq2[simp]:
    "measurable M (poisson_space rate) = measurable M (count_space UNIV)"
    by (intro measurable_cong_sets) (simp_all add: sets_poisson_space)

end


lemma poisson_density_nat_integral_eq_1:
  assumes "rate \<ge> 0"
  shows "(\<integral>\<^sup>+(x::nat). rate ^ x / fact x * exp (-rate) \<partial>count_space UNIV) = 1"
proof-
  have summable: "summable (\<lambda>x::nat. rate ^ x / fact x)" using summable_exp
      by (simp add: field_simps field_divide_inverse[symmetric])
  have "(\<integral>\<^sup>+(x::nat). rate ^ x / fact x * exp (-rate) \<partial>count_space UNIV) =
            exp (-rate) * (\<integral>\<^sup>+(x::nat). rate ^ x / fact x \<partial>count_space UNIV)"
      by (simp add: field_simps nn_integral_cmult[symmetric])
  also from assms have "(\<integral>\<^sup>+(x::nat). rate ^ x / fact x \<partial>count_space UNIV) = (\<Sum>x. rate ^ x / fact x)"
      by (simp_all add: nn_integral_count_space_nat
                        suminf_ereal summable suminf_ereal_finite)
  also have "... = exp rate" unfolding exp_def
      by (simp add: field_simps field_divide_inverse[symmetric] transfer_int_nat_factorial)
  also have "ereal (exp (-rate)) * ereal (exp rate) = 1" by (simp add: mult_exp_exp)
  finally show ?thesis .
qed

instantiation nat :: poisson
begin
  definition poisson_density_nat :: "real \<Rightarrow> nat \<Rightarrow> ereal" where
    "poisson_density_nat rate k = rate ^ k / fact k * exp (-rate)"
  definition poisson_density'_nat :: "real \<Rightarrow> nat \<Rightarrow> real" where
    "poisson_density'_nat rate k = rate ^ k / fact k * exp (-rate)"

  instance proof
    show "split (poisson_density :: _ \<Rightarrow> nat \<Rightarrow> _) \<in> borel_measurable (borel \<Otimes>\<^sub>M count_space UNIV)"
      unfolding poisson_density_nat_def[abs_def] by measurable
  next
    fix rate :: real assume "rate \<ge> 0"
    thus "(\<integral>\<^sup>+(x::nat). poisson_density rate x \<partial>count_space UNIV) = 1"
      unfolding poisson_density_nat_def
      by (rule poisson_density_nat_integral_eq_1)
  qed (simp_all add: poisson_density_nat_def poisson_density'_nat_def)
end

instantiation int :: poisson
begin
  definition poisson_density_int :: "real \<Rightarrow> int \<Rightarrow> ereal" where
    "poisson_density_int rate k = rate ^ (nat k) / fact k * exp (-rate)"
  definition poisson_density'_int :: "real \<Rightarrow> int \<Rightarrow> real" where
    "poisson_density'_int rate k = rate ^ (nat k) / fact k * exp (-rate)"

  instance proof
    show "split (poisson_density :: _ \<Rightarrow> int \<Rightarrow> _) \<in> borel_measurable (borel \<Otimes>\<^sub>M count_space UNIV)"
      unfolding poisson_density_int_def[abs_def] by measurable
  next
    fix rate :: real assume r: "rate \<ge> 0"
    have "(\<integral>\<^sup>+(x::int). poisson_density rate x \<partial>count_space UNIV) =
              \<integral>\<^sup>+(x::int). rate ^ nat x / real (fact x) * exp (-rate) \<partial>count_space UNIV"
      unfolding poisson_density_int_def by simp
    also from r have "... = \<integral>\<^sup>+(x::nat). rate ^ x / real (fact x) * exp (-rate) \<partial>count_space UNIV"
      by (simp add: nn_integral_nat_int transfer_int_nat_factorial)
    also from r have "... = 1" by (rule poisson_density_nat_integral_eq_1)
    finally show "(\<integral>\<^sup>+(x::int). poisson_density rate x \<partial>count_space UNIV) = 1" .
  qed (simp_all add: poisson_density_int_def poisson_density'_int_def)
end

lemma transfer_nat_int_poisson_density:
  "(x::int) \<ge> 0 \<Longrightarrow> poisson_density rate (nat x) = poisson_density rate x"
  unfolding poisson_density_nat_def poisson_density_int_def
  by (simp add: transfer_nat_int_factorial)

declare transfer_morphism_nat_int[transfer add return: transfer_nat_int_poisson_density]

lemma transfer_int_nat_poisson_density:
  "poisson_density rate (int x) = poisson_density rate x"
  unfolding poisson_density_nat_def poisson_density_int_def
  by (simp add: transfer_int_nat_factorial)

declare transfer_morphism_int_nat[transfer add return: transfer_int_nat_poisson_density]


lemma poisson_space_nat_distr:
  assumes "rate \<ge> 0"
  shows "poisson_space rate = distr (poisson_space rate) (count_space UNIV) (nat :: int \<Rightarrow> nat)"
    (is "?M1 = ?M2")
proof (intro measure_eqI)
  fix X :: "nat set" assume X: "X \<in> sets (poisson_space rate)"
  have [simp]: "\<And>x. indicator (nat -` X) x = indicator X (nat x)" by (simp add: indicator_def)
  from X and assms 
    have "emeasure ?M1 X = \<integral>\<^sup>+ x. poisson_density rate x * indicator X x \<partial>count_space UNIV"
    by (simp add: sets_poisson_space emeasure_poisson_space)
  also from assms have "... = \<integral>\<^sup>+ x. poisson_density rate x * indicator X (nat x) \<partial>count_space UNIV"
    by (subst nn_integral_nat_int)
       (simp_all add: transfer_int_nat_poisson_density poisson_density_ge_0 
                      poisson_density_of_neg_eq_0)
  also from X have "... = emeasure ?M2 X"
    by (simp add: emeasure_distr emeasure_poisson_space space_poisson_space)
  finally show "emeasure ?M1 X = emeasure ?M2 X" .
qed (simp add: sets_poisson_space)

lemma poisson_space_int_distr:
  assumes "rate \<ge> 0"
  shows "poisson_space rate = distr (poisson_space rate) (count_space UNIV) (int :: nat \<Rightarrow> int)"
    (is "?M1 = ?M2")
proof (intro measure_eqI)
  fix X :: "int set" assume X: "X \<in> sets (poisson_space rate)"
  have [simp]: "\<And>x. indicator (int -` X) x = indicator X (int x)" by (simp add: indicator_def)
  from X and assms 
    have "emeasure ?M1 X = \<integral>\<^sup>+ x. poisson_density rate x * indicator X x \<partial>count_space UNIV"
    by (simp add: sets_poisson_space emeasure_poisson_space)
  also from assms have "... = \<integral>\<^sup>+ x. poisson_density rate x * indicator X (int x) \<partial>count_space UNIV"
    by (subst nn_integral_nat_int)
       (simp_all add: transfer_int_nat_poisson_density poisson_density_ge_0 
                      poisson_density_of_neg_eq_0)
  also from X have "... = emeasure ?M2 X"
    by (simp add: emeasure_distr emeasure_poisson_space space_poisson_space)
  finally show "emeasure ?M1 X = emeasure ?M2 X" .
qed (simp add: sets_poisson_space)


(*
lemma expectation_poisson_nat:
  fixes M :: "'a measure" and X :: "'a \<Rightarrow> nat"
  assumes "prob_space M" 
  assumes r: "rate \<ge> 0" and dist: "distributed M (count_space UNIV) X (poisson_density rate)"
  shows "integral\<^sup>L M (\<lambda>x. real (X x)) = rate"
proof-
  from r have [simp]: "\<And>x::nat. poisson_density' rate x * real x \<ge> 0"
    by (case_tac "x \<ge> 0") (simp_all add: poisson_density'_ge_0 poisson_density'_of_neg_eq_0)
  have "(\<integral>\<^sup>+(x::nat). ereal (- (poisson_density' rate x * real x)) \<partial>count_space UNIV) = 0"
    by (subst nn_integral_0_iff_AE, simp) 
       (auto simp: poisson_density'_ge_0 intro!: AE_I'[of "{}"])
  moreover {
    from r have "1 = (\<integral>\<^sup>+(x::nat). ereal (poisson_density' rate x) \<partial>count_space UNIV)"
      by (simp add: poisson_density_integral_eq_1)
    also from r have "... = (\<Sum>x. ereal (poisson_density' rate x))"
       by (subst nn_integral_count_space_nat) (simp_all add: poisson_density_ge_0)
    finally have A: "(\<Sum>x. ereal (poisson_density' rate x)) = 1" ..
    with r have B: "summable (poisson_density' rate)"
      by (intro summable_ereal) (simp_all add: poisson_density'_ge_0)
    hence "(\<Sum>x. poisson_density' rate x) = exp (-rate) + (\<Sum>x. poisson_density' rate (x+1))"
      by (subst suminf_split_initial_segment[where k = 1]) (simp_all add: poisson_density'_nat_def)
    also have "(\<Sum>x. poisson_density' rate (x+1)) = rate * (\<Sum>x. poisson_density' rate (x+1) * (x + 1))"
  }

  interpret prob_space M by fact
  from dist have "expectation (\<lambda>x. real (X x)) = 
                      integral\<^sup>L (distr M (count_space UNIV) X) real"
    unfolding distributed_def by (subst integral_distr) simp_all
  also from dist have "distr M (count_space UNIV) X = 
                           density (count_space UNIV) (poisson_density' rate)"
    unfolding distributed_def by simp
  also from r and dist 
    have "integral\<^sup>L ... real = 
              integral\<^sup>L (count_space UNIV) (\<lambda>x::nat. poisson_density' rate x * real x)"
    by (subst integral_density) (simp_all add: poisson_density'_ge_0)
  also 
  hence "integral\<^sup>L (count_space UNIV) (\<lambda>x::nat. poisson_density' rate x * real x) = 
             (\<Sum>x. poisson_density' rate x * real x)"
apply (intro integral_count_space_nat)
apply (unfold integrable_def)
apply auto
apply (subst (asm) times_ereal.simps[symmetric])
apply (subst (asm) poisson_density'_ereal)
apply simp
  also have "(\<lambda>x::nat. poisson_density' rate x * real x) = T"
apply (simp add: poisson_density'_nat_def)
*)

end
