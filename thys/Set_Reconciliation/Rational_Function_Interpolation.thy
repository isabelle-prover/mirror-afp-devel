section \<open>Rational Function Interpolation\<close>

theory Rational_Function_Interpolation
  imports
    "Poly_Lemmas"
    "Gauss_Jordan.System_Of_Equations"
    "Polynomial_Interpolation.Missing_Polynomial"
begin

subsection \<open>Definitions\<close>

text \<open>General condition for rational functions interpolation\<close>

definition interpolated_rational_function where
  "interpolated_rational_function p\<^sub>A p\<^sub>B E f\<^sub>A f\<^sub>B d\<^sub>A d\<^sub>B \<equiv>
    (\<forall> e \<in> E. f\<^sub>A e * poly p\<^sub>B e = f\<^sub>B e * poly p\<^sub>A e) \<and>
    degree p\<^sub>A \<le> (d\<^sub>A::real) \<and> degree p\<^sub>B \<le> (d\<^sub>B::real) \<and>
    p\<^sub>A \<noteq> 0 \<and> p\<^sub>B \<noteq> 0"

text \<open>Interpolation condition with given exact degrees\<close>

definition monic_interpolated_rational_function where
 "monic_interpolated_rational_function p\<^sub>A p\<^sub>B E f\<^sub>A f\<^sub>B d\<^sub>A d\<^sub>B  \<equiv>
    (\<forall> e \<in> E. f\<^sub>A e * poly p\<^sub>B e = f\<^sub>B e * poly p\<^sub>A e) \<and>
    degree p\<^sub>A = \<lfloor>d\<^sub>A::real\<rfloor> \<and> degree p\<^sub>B = \<lfloor>d\<^sub>B::real\<rfloor> \<and>
    monic p\<^sub>A \<and> monic p\<^sub>B"

lemma monic0: "\<not> monic (0::'a::zero_neq_one poly)"
  by simp

lemma monic_interpolated_rational_function_interpolated_rational_function:
  "monic_interpolated_rational_function p\<^sub>A p\<^sub>B E f\<^sub>A f\<^sub>B d\<^sub>A d\<^sub>B
     \<Longrightarrow> interpolated_rational_function p\<^sub>A p\<^sub>B E f\<^sub>A f\<^sub>B d\<^sub>A d\<^sub>B \<or> \<not>(p\<^sub>A \<noteq> 0 \<and> p\<^sub>B \<noteq> 0)"
  unfolding monic_interpolated_rational_function_def interpolated_rational_function_def
  by linarith

definition rfi_coefficient_matrix :: "'a::field list \<Rightarrow> ('a \<Rightarrow> 'a) \<Rightarrow> nat \<Rightarrow> nat
    \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> 'a" where
  "rfi_coefficient_matrix E f d\<^sub>A d\<^sub>B i j = (
    if j < d\<^sub>A then
      (E ! i) ^ j
    else if j < d\<^sub>A + d\<^sub>B then
      - f (E ! i) * (E ! i) ^ (j-d\<^sub>A)
    else 0
  )"

definition rfi_constant_vector :: "'a::field list \<Rightarrow> ('a \<Rightarrow> 'a) \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> (nat \<Rightarrow> 'a)" where
   "rfi_constant_vector E f d\<^sub>A d\<^sub>B = (\<lambda> i. f (E ! i) * (E ! i) ^ d\<^sub>B - (E ! i) ^ d\<^sub>A)"

definition rational_function_interpolation :: "'a::field list \<Rightarrow> ('a \<Rightarrow> 'a) \<Rightarrow> nat \<Rightarrow> nat
    \<Rightarrow> 'm::mod_type itself \<Rightarrow> ('a,'m) vec" where
  "rational_function_interpolation E f d\<^sub>A d\<^sub>B m =
    (let solved = solve
      (\<chi> (i::'m) (j::'m). rfi_coefficient_matrix E f d\<^sub>A d\<^sub>B (to_nat i) (to_nat j))
      (\<chi> (i::'m). rfi_constant_vector E f d\<^sub>A d\<^sub>B (to_nat i))
    in fst (the solved))"

definition solution_to_poly :: "('a::finite_field, 'n::mod_type) vec \<Rightarrow>
    nat \<Rightarrow> nat \<Rightarrow> 'a poly \<times> 'a poly" where
  "solution_to_poly S d\<^sub>A d\<^sub>B = (let
    p = Abs_poly (\<lambda>i. if i < d\<^sub>A then S $ (from_nat i) else 0) + monom 1 d\<^sub>A;
    q = Abs_poly (\<lambda>i. if i < d\<^sub>B then S $ (from_nat (i+d\<^sub>A)) else 0) + monom 1 d\<^sub>B in
    (p, q))"

definition interpolate_rat_fun where
  "interpolate_rat_fun E f d\<^sub>A d\<^sub>B m =
  solution_to_poly (rational_function_interpolation E f d\<^sub>A d\<^sub>B m) d\<^sub>A d\<^sub>B"


subsection \<open>Preliminary Results\<close>

lemma consecutive_sum_combine:
  assumes "m \<ge> n"
  shows "(\<Sum>i = 0..n. f i) + (\<Sum>i = Suc n ..m. f i) = (\<Sum>i = 0..m. f i)"
proof -
  from assms have "{0..n} \<union> {Suc n..m} = {0..m}"
    by auto
  moreover have "sum f ({0..n} \<union> {Suc n..m}) =
      sum f ({0..n} - {Suc n..m}) + sum f ({Suc n..m} - {0..n}) + sum f ({0..n} \<inter> {Suc n..m})"
    using sum_Un2 finite_atLeastAtMost by fast
  ultimately show ?thesis
    by (simp add: Diff_triv)
qed

lemma poly_altdef_Abs_poly_le:
  fixes x :: "'a::{comm_semiring_0, semiring_1}"
  shows "poly (Abs_poly (\<lambda>i. if i \<le> n then f i else 0)) x = (\<Sum>i = 0..n. f i * x ^ i)"
proof -
  let ?if\<^sub>A0 = "(\<lambda>i. if i \<le> n then f i else 0)"
  let ?p = "Abs_poly ?if\<^sub>A0"

  have co: "coeff ?p = ?if\<^sub>A0"
    using coeff_Abs_poly_If_le by blast

  then have "\<forall>i>n. coeff ?p i = 0"
    by auto
  then have de: "degree ?p \<le> n"
    using degree_le by blast

  have "\<forall>i>degree ?p. ?if\<^sub>A0 i = 0"
    using co coeff_eq_0 by fastforce
  then have "\<forall>i>degree ?p. ?if\<^sub>A0 i * x ^ i = 0"
    by simp
  then have "\<forall> i \<in> {Suc (degree ?p)..n}. (?if\<^sub>A0 i * x ^ i) = 0"
    using less_eq_Suc_le by fastforce
  then have db: "(\<Sum>i = Suc (degree ?p)..n. ?if\<^sub>A0 i * x ^ i) = 0"
     by simp

  have "poly ?p x = (\<Sum>i\<le>degree ?p. coeff ?p i * x ^ i)"
    using poly_altdef by auto
  also have "\<dots> = (\<Sum>i\<le>degree ?p. ?if\<^sub>A0 i * x ^ i) "
    using co by simp
  also have "\<dots> = (\<Sum>i = 0..degree ?p. ?if\<^sub>A0 i * x ^ i) "
    using atMost_atLeast0 by simp
  also have "\<dots> = (\<Sum>i = 0..degree ?p. ?if\<^sub>A0 i * x ^ i) +
      (\<Sum>i = Suc (degree ?p)..n. ?if\<^sub>A0 i * x ^ i)"
    using db by simp
  also have  "\<dots> = (\<Sum>i = 0..n. ?if\<^sub>A0 i * x ^ i)"
    using consecutive_sum_combine de by blast
  finally show ?thesis
    by simp
qed

lemma poly_altdef_Abs_poly_l:
  fixes x :: "'a::{comm_semiring_0,semiring_1}"
  shows "poly (Abs_poly (\<lambda>i. if i < n then f i else 0)) x = (\<Sum>i<n. f i * x ^ i)"
proof (cases "n")
  case 0
  have p0: "Abs_poly (\<lambda>i. 0) = 0"
    using zero_poly_def by fastforce
  show ?thesis
    using 0 by (simp add: p0)
next
  case (Suc m)
  have "poly (Abs_poly (\<lambda>i. if i \<le> m then f i else 0)) x = (\<Sum>i = 0..m. f i * x ^ i)"
    using poly_altdef_Abs_poly_le by blast
  moreover have "poly (Abs_poly (\<lambda>i. if i \<le> m then f i else 0)) x = poly (Abs_poly (\<lambda>i. if i < n then f i else 0)) x "
    using Suc using less_Suc_eq_le by auto
  moreover have "(\<Sum>i = 0..m. f i * x ^ i) = (\<Sum>i<n. f i * x ^ i)"
    using Suc atLeast0AtMost lessThan_Suc_atMost by presburger
  ultimately show ?thesis by argo
qed

lemma degree_Abs_poly_If_l:
  assumes "n \<noteq> 0"
  shows "degree (Abs_poly (\<lambda>i. if i < n then f i else 0)) < n"
proof -
  have "coeff (Abs_poly (\<lambda>i. if i < n then f i else 0)) x = 0" if "x \<ge> n" for x
    using coeff_Abs_poly [of n  "(\<lambda>i. if i < n then f i else 0)"] using that by simp
  then show ?thesis
    using assms degree_lessI by blast
qed

lemma nth_less_length_in_set_eq:
  shows "(\<forall> i < length E. f (E ! i) = g (E ! i)) \<longleftrightarrow> (\<forall> e \<in> set E. f e = g e)"
proof standard
  show "\<forall>i < length E. f (E ! i) = g (E ! i) \<Longrightarrow> \<forall>e\<in>set E. f e = g e"
    using in_set_conv_nth by metis
next
  show "\<forall>e\<in>set E. f e = g e \<Longrightarrow> \<forall>i<length E. f (E ! i) = g (E ! i)"
    by simp
qed

lemma nat_leq_real_floor: "real (i::nat) \<le> (d::real) \<longleftrightarrow> real i \<le> \<lfloor>d\<rfloor>" (is "?l = ?r")
proof
  assume ?l
  then show ?r
    using floor_mono by fastforce
next
  assume ?r
  then show ?l
    by linarith
qed

lemma mod_type_less_function_eq:
  fixes i :: "'a::mod_type"
  assumes "\<forall> i < CARD('a) . f i = g i"
  shows "f (to_nat i) = g (to_nat i)"
  using assms by (simp add: to_nat_less_card)


subsection \<open>On @{term "solution_to_poly"}\<close>

lemma fst_solution_to_poly_nz:
  "fst (solution_to_poly S d\<^sub>A d\<^sub>B) \<noteq> 0"
proof
  assume "fst (solution_to_poly S d\<^sub>A d\<^sub>B) = 0"
  hence "coeff (Abs_poly (\<lambda>i. if i < d\<^sub>A then S $ (from_nat i) else 0) + monom 1 d\<^sub>A) d\<^sub>A = 0"
    unfolding solution_to_poly_def by simp
  hence "coeff (Abs_poly (\<lambda>i. if i < d\<^sub>A then S $ (from_nat i) else 0)) d\<^sub>A + 1 = 0" by simp
  thus "False" by (subst (asm) coeff_Abs_poly[where n="d\<^sub>A"]) auto
qed

lemma snd_solution_to_poly_nz:
  "snd (solution_to_poly S d\<^sub>A d\<^sub>B) \<noteq> 0"
proof
  assume "snd (solution_to_poly S d\<^sub>A d\<^sub>B) = 0"
  hence "coeff (Abs_poly (\<lambda>i. if i < d\<^sub>B then S $ (from_nat (i+d\<^sub>A)) else 0) + monom 1 d\<^sub>B) d\<^sub>B = 0"
    unfolding solution_to_poly_def by simp
  hence "coeff (Abs_poly (\<lambda>i. if i < d\<^sub>B then S $ (from_nat (i+d\<^sub>A)) else 0)) d\<^sub>B + 1 = 0" by simp
  thus "False" by (subst (asm) coeff_Abs_poly[where n="d\<^sub>B"]) auto
qed

lemma degree_Abs0p1: "degree (Abs_poly (\<lambda>i. 0) + 1) = 0"
    by (metis add_0 degree_1 zero_poly_def)

lemma degree_solution_to_poly_fst:
  "degree (fst (solution_to_poly S d\<^sub>A d\<^sub>B)) = d\<^sub>A"
proof (cases d\<^sub>A)
  case 0
  then show ?thesis unfolding solution_to_poly_def
    using degree_Abs0p1 by (simp add: one_pCons)
next
  case (Suc nat)
  then have "degree (Abs_poly (\<lambda>i. if i < d\<^sub>A then S $ from_nat i else 0)) < d\<^sub>A"
    using degree_Abs_poly_If_l by fast
  moreover have "\<dots> = degree (monom (1::'a) d\<^sub>A)"
    by (simp add: degree_monom_eq)
  ultimately show ?thesis
    unfolding solution_to_poly_def
    by (simp add: degree_add_eq_right)
qed

lemma degree_solution_to_poly_snd:
  "degree (snd (solution_to_poly S d\<^sub>A d\<^sub>B)) = d\<^sub>B"
proof (cases d\<^sub>B)
  case 0
  then show ?thesis unfolding solution_to_poly_def
    using degree_Abs0p1 by (simp add: one_pCons)
next
  case (Suc nat)
  then have "degree (Abs_poly (\<lambda>i. if i < d\<^sub>B then S $ from_nat (i + d\<^sub>A) else 0)) < d\<^sub>B"
    using degree_Abs_poly_If_l by fast
  moreover have "\<dots> = degree (monom (1::'a) d\<^sub>B)"
    by (simp add: degree_monom_eq)
  ultimately  show ?thesis
    unfolding solution_to_poly_def
    by (simp add: degree_add_eq_right)
qed

lemma monic_solution_to_poly_snd:
  "monic (snd (solution_to_poly S d\<^sub>A d\<^sub>B))"
proof (cases d\<^sub>B)
  case 0
  then show ?thesis unfolding solution_to_poly_def
    by (simp add: coeff_Abs_poly degree_Abs0p1)
next
  case (Suc x)
  have 1: "coeff (Abs_poly (\<lambda>i. if i < Suc x then S $ from_nat (i + d\<^sub>A) else 0)) (Suc x) = 0"
    by (simp add: coeff_eq_0 degree_Abs_poly_If_l)
  have "degree (Abs_poly (\<lambda>i. if i < d\<^sub>B then S $ from_nat (i + d\<^sub>A) else 0) + monom 1 d\<^sub>B) = d\<^sub>B"
    using degree_solution_to_poly_snd unfolding solution_to_poly_def by auto
  then show ?thesis
      unfolding solution_to_poly_def using 1 Suc by simp
  qed

lemma monic_solution_to_poly_fst:
  "monic (fst (solution_to_poly S d\<^sub>A d\<^sub>B))"
proof (cases d\<^sub>A)
  case 0
  then show ?thesis
    unfolding solution_to_poly_def by (simp add: coeff_Abs_poly degree_Abs0p1)
next
  case (Suc x)
  have 1: "coeff (Abs_poly (\<lambda>i. if i < d\<^sub>A then S $ (from_nat i) else 0)) (Suc x) = 0"
    by (simp add: Suc coeff_eq_0 degree_Abs_poly_If_l)
  have "degree (Abs_poly (\<lambda>i. if i < d\<^sub>A then S $ (from_nat i) else 0) + monom 1 d\<^sub>A) = d\<^sub>A"
    using degree_solution_to_poly_fst unfolding solution_to_poly_def by auto
  then show ?thesis
      unfolding solution_to_poly_def using 1 Suc by simp
qed

subsection "Correctness"

text \<open>Needs the assumption that the system is consistent, because a solution exists.\<close>
lemma rational_function_interpolation_correct_poly:
  assumes
    "\<forall> x \<in> set E. f x = f\<^sub>A x / f\<^sub>B x" "\<forall> x \<in> set E. f\<^sub>B x \<noteq> 0"
    "d\<^sub>A + d\<^sub>B \<le> length E"
    "CARD('m::mod_type) = length E"
    "consistent (\<chi> (i::'m) (j::'m). rfi_coefficient_matrix E f d\<^sub>A d\<^sub>B (to_nat i) (to_nat j))
                (\<chi> (i::'m). rfi_constant_vector E f d\<^sub>A d\<^sub>B (to_nat i))"
    "S = rational_function_interpolation E f d\<^sub>A d\<^sub>B TYPE('m)"
    "p\<^sub>A = fst (solution_to_poly S d\<^sub>A d\<^sub>B)"
    "p\<^sub>B = snd (solution_to_poly S d\<^sub>A d\<^sub>B)"
  shows
    "\<forall> e \<in> set E. f\<^sub>A e * poly p\<^sub>B e = f\<^sub>B e * poly p\<^sub>A e"
proof -

  let ?coeff = "rfi_coefficient_matrix E f d\<^sub>A d\<^sub>B"
  let ?const = "rfi_constant_vector E f d\<^sub>A d\<^sub>B"
  let ?coeff' = "(\<chi> (i::'m) (j::'m). ?coeff (to_nat i) (to_nat j))"
  let ?const' = "(\<chi> (i::'m). ?const (to_nat i))"

  have "is_solution S ?coeff' ?const'"
    by (simp add: assms(5,6) consistent_imp_is_solution_solve rational_function_interpolation_def)
  then have sol: "?coeff' *v S = ?const'"
    by (simp add: is_solution_def)

  have const: "?const i = ?const' $ from_nat i" if "i < length E" for i
    by (simp add: assms(4) that to_nat_from_nat_id)

  have coeff: "?coeff i j = ?coeff' $ from_nat i $ from_nat j"
    if "i < length E" "j < length E" for i j
  proof -
    have "to_nat (from_nat i ::'m) = i"
      using that assms(4)
      by (intro to_nat_from_nat_id) simp
    moreover have "to_nat (from_nat j ::'m) = j"
      using that assms(4,3)
      by (intro to_nat_from_nat_id) simp
    ultimately show ?thesis
      unfolding rfi_coefficient_matrix_def
      by (simp add: Let_def)
  qed

  have x: "(\<Sum>j < d\<^sub>A + d\<^sub>B. (?coeff i j) * S $ (from_nat j)) = ?const i"
    (is "?l = ?r") if "i < length E" for i
  proof -
    have "?l = (\<Sum>j < length E. ?coeff i j * S $ (from_nat j))"
      using assms(3) by (intro sum.mono_neutral_cong_left) (auto simp add:rfi_coefficient_matrix_def)
    also have "... = (\<Sum>j < length E. ?coeff' $ (from_nat i) $ (from_nat j) * S $ (from_nat j))"
      using coeff that by auto
    also have "\<dots> = (\<Sum>j \<in> {0..< length E}. ?coeff' $ (from_nat i) $ (from_nat j) * S $ (from_nat j))"
      by (intro sum.reindex_bij_betw [symmetric] bij_betwI [where g = id]) auto
    also have "\<dots> = (\<Sum>j\<in>(UNIV::'m set). ?coeff' $ (from_nat i) $ j * S $ j)"
      using bij_from_nat [where 'a = 'm] assms(3,4) by (intro sum.reindex_bij_betw) simp
    also have "\<dots> = (?coeff' *v S) $ (from_nat i)"
      unfolding matrix_vector_mult_def by simp
    also have "\<dots> = ?const' $ (from_nat i)"
      using sol by simp
    finally show "?l = ?r" using const that by simp
  qed

  let ?p_lam = "\<lambda>i. if i < d\<^sub>A then S $ from_nat i else 0"
  let ?q_lam = "\<lambda>i. if i < d\<^sub>B then S $ from_nat (i + d\<^sub>A) else 0"
  let ?p' = "Abs_poly ?p_lam + monom 1 d\<^sub>A"
  let ?q' = "Abs_poly ?q_lam + monom 1 d\<^sub>B"
  have pq: "p\<^sub>A = ?p'" "p\<^sub>B = ?q'"
    using assms(7,8) unfolding solution_to_poly_def by auto

  have "(\<Sum>j<d\<^sub>A. S $ from_nat j * E ! i ^ j) - f (E ! i) * (\<Sum>j<d\<^sub>B. S $ from_nat (j + d\<^sub>A) * E ! i ^ j)
    = f (E ! i) * E ! i ^ d\<^sub>B - E ! i ^ d\<^sub>A" if "i < length E" for i
  proof -
    let ?pq_lam = "(\<lambda>j. (if j < d\<^sub>A then E ! i ^ j else
        if j < d\<^sub>A + d\<^sub>B then - f (E ! i) * E ! i ^ (j - d\<^sub>A) else 0) * S $ from_nat j)"

    have reindex: "(\<Sum>j \<in> {d\<^sub>A..< d\<^sub>A + d\<^sub>B}. - f (E ! i) * E ! i ^ (j - d\<^sub>A) * S $ from_nat j) =
      (\<Sum>j \<in> {0..< d\<^sub>B}. - f (E ! i) * E ! i ^ (j) * S $ from_nat (j+d\<^sub>A))"
      by (rule sum.reindex_bij_witness [of _ "\<lambda>i. i + d\<^sub>A" "\<lambda>i. i - d\<^sub>A"]) auto

    from x have "f (E ! i) * E ! i ^ d\<^sub>B - E ! i ^ d\<^sub>A = (\<Sum>j<d\<^sub>A + d\<^sub>B. ?pq_lam j )"
      unfolding rfi_coefficient_matrix_def rfi_constant_vector_def using that by simp
    also have "\<dots> = (\<Sum>j \<in> {0..< d\<^sub>A + d\<^sub>B}. ?pq_lam j)"
      using atLeast0LessThan by presburger
    also have "\<dots> = (\<Sum>j \<in> {0..< d\<^sub>A}. ?pq_lam j) + (\<Sum>j \<in> {d\<^sub>A..< d\<^sub>A + d\<^sub>B}. ?pq_lam j) "
      by (subst sum.atLeastLessThan_concat) auto
    also have "\<dots> = (\<Sum>j \<in> {0..< d\<^sub>A}. E ! i ^ j * S $ from_nat j) +
        (\<Sum>j \<in> {d\<^sub>A..< d\<^sub>A + d\<^sub>B}. - f (E ! i) * E ! i ^ (j - d\<^sub>A) * S $ from_nat j)"
      by auto
    also have "\<dots> = (\<Sum>j \<in> {0..< d\<^sub>A}. E ! i ^ j * S $ from_nat j) +
        (\<Sum>j \<in> {0..< d\<^sub>B}. - f (E ! i) * E ! i ^ (j) * S $ from_nat (j+d\<^sub>A))"
      using reindex by simp
    also have "\<dots> = (\<Sum>j \<in> {0..< d\<^sub>A}. E ! i ^ j * S $ from_nat j) +
        - f (E ! i) * (\<Sum>j \<in> {0..< d\<^sub>B}. E ! i ^ (j) * S $ from_nat (j+d\<^sub>A))"
      by (simp add: sum_distrib_left mult.commute mult.left_commute)
    finally have "f (E ! i) * E ! i ^ d\<^sub>B - E ! i ^ d\<^sub>A = \<dots>"
      by argo

    moreover have "(\<Sum>j \<in> {0..< d\<^sub>A}. E ! i ^ j * S $ from_nat j) =
        (\<Sum>j<d\<^sub>A. S $ from_nat j * E ! i ^ j)"
      by (subst atLeast0LessThan) (meson mult.commute)
    moreover have "(\<Sum>j \<in> {0..< d\<^sub>B}. E ! i ^ (j) * S $ from_nat (j+d\<^sub>A)) =
        (\<Sum>j<d\<^sub>B. S $ from_nat (j + d\<^sub>A) * E ! i ^ j)"
      by (subst atLeast0LessThan) (meson mult.commute)
    ultimately show ?thesis
      by simp
  qed

  then have "\<forall>e \<in> set E. (\<Sum>j<d\<^sub>A. S $ from_nat j * e ^ j) - f e * (\<Sum>j<d\<^sub>B. S $ from_nat (j + d\<^sub>A) * e ^ j)
      = f e * e ^ d\<^sub>B - e ^ d\<^sub>A"
    by (subst nth_less_length_in_set_eq [symmetric]) auto

  then have "(\<Sum>i<d\<^sub>A. S $ from_nat i * e ^ i) - f e * (\<Sum>i<d\<^sub>B. S $ from_nat (i + d\<^sub>A) * e ^ i)
      = f e * e ^ d\<^sub>B - e ^ d\<^sub>A" if "e \<in> set E" for e
    using that by blast

  then have "(\<Sum>i<d\<^sub>A. S $ from_nat i * e ^ i) + e ^ d\<^sub>A
      = f e * e ^ d\<^sub>B + f e * (\<Sum>i<d\<^sub>B. S $ from_nat (i + d\<^sub>A) * e ^ i)" if "e \<in> set E" for e
    using that by (simp add:field_simps)

  then have "f e * ((\<Sum>i<d\<^sub>B. S $ from_nat (i + d\<^sub>A) * e ^ i) + e ^ d\<^sub>B) =
      (\<Sum>i<d\<^sub>A. S $ from_nat i * e ^ i) + e ^ d\<^sub>A" if "e \<in> set E" for e
    using that by (simp add: ring_class.ring_distribs(1))

  then have "f e * (poly (Abs_poly ?q_lam) e + poly (monom 1 d\<^sub>B) e) =
      poly (Abs_poly ?p_lam) e + poly (monom 1 d\<^sub>A) e" if "e \<in> set E" for e
    unfolding poly_altdef_Abs_poly_l poly_monom using that by auto

  then have "f e * (poly (Abs_poly ?q_lam) e + poly (monom 1 d\<^sub>B) e) =
      poly (Abs_poly ?p_lam) e + poly (monom 1 d\<^sub>A) e" if "e \<in> set E" for e
    using that by simp
  then have "f e * poly (Abs_poly ?q_lam + monom 1 d\<^sub>B) e =
      poly (Abs_poly ?p_lam + monom 1 d\<^sub>A) e" if "e \<in> set E" for e
    by (simp add: that)
  then have "(f\<^sub>A e / f\<^sub>B e) * poly ?q' e =  poly ?p' e" if "e \<in> set E" for e
    using that assms(1) by simp
  then have "f\<^sub>A e * poly ?q' e = f\<^sub>B e * poly ?p' e" if "e \<in> set E" for e
    using that by (simp add: assms(2) nonzero_divide_eq_eq)
  then have "\<forall>e\<in>set E. f\<^sub>A e * poly (snd (solution_to_poly S d\<^sub>A d\<^sub>B)) e =
      f\<^sub>B e * poly (fst (solution_to_poly S d\<^sub>A d\<^sub>B)) e"
    unfolding solution_to_poly_def by auto
  then show "\<forall>e\<in>set E. f\<^sub>A e * poly p\<^sub>B e = f\<^sub>B e * poly p\<^sub>A e"
    using assms(8,7) by simp
qed

lemma poly_lead_coeff_extract:
  "poly p x = (\<Sum>i<degree p. coeff p i * x ^ i) + lead_coeff p *  x ^ degree p"
    for x :: "'a::{comm_semiring_0,semiring_1}"
  unfolding poly_altdef using lessThan_Suc_atMost sum.lessThan_Suc by auto

lemma d\<^sub>A_d\<^sub>B_helper:
  assumes
    "finite A" "finite B"
    "int d\<^sub>A = \<lfloor>(real (length E) + card A - card B)/2\<rfloor>"
    "int d\<^sub>B = \<lfloor>(real (length E) + card B - card A)/2\<rfloor>"
    "card (sym_diff A B) \<le> length E"
  shows
    "d\<^sub>A + d\<^sub>B \<le> length E"
    "card (A - B) \<le> d\<^sub>A" "card (B - A) \<le> d\<^sub>B"
    "d\<^sub>B - card (B - A) = d\<^sub>A - card (A - B)"
proof -
  have a: "real d\<^sub>A = of_int \<lfloor>(real (length E) + card A - card B)/2\<rfloor>"
    using assms(3) by simp
  have b: "real d\<^sub>B = of_int \<lfloor>(real (length E) + card B - card A)/2\<rfloor>"
    using assms(4) by simp

  have "real d\<^sub>A + real d\<^sub>B \<le> (real (length E)+card A-card B)/2 + (real (length E)+card B-card A)/2"
    unfolding a b by (intro add_mono) linarith+
  also have "\<dots> = real (length E)" by argo
  finally have "real d\<^sub>A + real d\<^sub>B \<le> length E" by simp
  thus "d\<^sub>A + d\<^sub>B \<le> length E" by simp

  have "real (card (A - B)) = (real (card (sym_diff A B)) + real (card A) - real (card B))/2"
    unfolding card_sym_diff_finite[OF assms(1,2)] using card_sub_int_diff_finite[OF assms(1,2)]
    by simp
  also have "\<dots> \<le> (real (length E) + real (card A) - real (card B))/2"
    using assms(5) by simp
  finally have "real (card (A-B)) \<le> d\<^sub>A"
    unfolding a using nat_leq_real_floor by blast
  thus c:"card (A-B) \<le> d\<^sub>A" by auto

  have "real (card (B - A)) = (real (card (sym_diff A B)) + real (card B) - real (card A))/2"
    unfolding card_sym_diff_finite[OF assms(1,2)] using card_sub_int_diff_finite[OF assms(1,2)]
    by simp
  also have "\<dots> \<le> (real (length E) + real (card B) - real (card A))/2"
    using assms(5) by simp
  finally have "real (card (B-A)) \<le> d\<^sub>B"
    unfolding b using nat_leq_real_floor by blast
  thus d:"card (B-A) \<le> d\<^sub>B" by auto

  have "real d\<^sub>B - real d\<^sub>A =
    of_int \<lfloor>(real (length E) - card B - card A)/2 + real (card B)\<rfloor> -
    of_int \<lfloor>(real (length E) - card A - card B)/2 + real (card A)\<rfloor>"
    unfolding a b by argo
  also have "\<dots> = real (card B) - real (card A)"
    by (simp add:algebra_simps)
  also have "\<dots> =  real (card (B - A)) - card (A - B)"
    using card_sub_int_diff_finite[OF assms(1,2)] by simp
  finally have "real d\<^sub>B - real d\<^sub>A = real (card (B - A)) - card (A - B)"
    by simp

  thus "d\<^sub>B - card (B - A) = d\<^sub>A - card (A - B)"
    using c d by simp
qed

text "Insert the solution we know that must exist to show it's consistent"
lemma rational_function_interpolation_consistent:
  fixes A B :: "'a::finite_field set"
  assumes
    "\<forall> x \<in> (set E). f x = f\<^sub>A x / f\<^sub>B x"
    "CARD('m::mod_type) = length E"
    "d\<^sub>A + d\<^sub>B \<le> length E"
    "card (A - B) \<le> d\<^sub>A"
    "card (B - A) \<le> d\<^sub>B"
    "d\<^sub>B - card (B - A) = d\<^sub>A - card (A - B)"
    "\<forall> x \<in> set E. x \<notin> A" "\<forall> x \<in> set E. x \<notin> B"
    "f\<^sub>A = (\<lambda> x \<in> set E. poly (set_to_poly A) x)"
    "f\<^sub>B = (\<lambda> x \<in> set E. poly (set_to_poly B) x)"
  shows
    "consistent (\<chi> (i::'m) (j::'m). rfi_coefficient_matrix E f d\<^sub>A d\<^sub>B (to_nat i) (to_nat j))
                (\<chi> (i::'m). rfi_constant_vector E f d\<^sub>A d\<^sub>B (to_nat i))"
proof -
  let ?coeff = "rfi_coefficient_matrix E f d\<^sub>A d\<^sub>B"
  let ?const = "rfi_constant_vector E f d\<^sub>A d\<^sub>B"
  let ?coeff' = "(\<chi> (i::'m) (j::'m). ?coeff (to_nat i) (to_nat j))"
  let ?const' = "(\<chi> (i::'m). ?const (to_nat i))"

  define sp where "sp = set_to_poly (A-B) * monom 1 (d\<^sub>A - card (A-B))"
  define sq where "sq = set_to_poly (B-A) * monom 1 (d\<^sub>B - card (B-A))"

  (* We show that ?x is a solution *)

  let ?x = "(\<chi> (i::'m). if (to_nat i) < d\<^sub>A then coeff sp (to_nat i) else coeff sq (to_nat i - d\<^sub>A))"

  have poly_mul_eq: "f\<^sub>A x * poly sq x = f\<^sub>B x * poly sp x" if "x \<in> set E" for x
  proof -
    have "set_to_poly A * set_to_poly (B - A) = (set_to_poly B) * set_to_poly (A - B)"
      by (simp add: Un_commute set_to_poly_mult_distinct)
    then have "(set_to_poly A * set_to_poly (B - A) * monom 1 (d\<^sub>B - card (B - A)) =
       (set_to_poly B) * set_to_poly (A - B) * monom 1 (d\<^sub>A - card (A - B)))"
       using assms(6) by argo
    hence "poly (set_to_poly A) x * poly (set_to_poly (B - A) * monom 1 (d\<^sub>B - card (B - A))) x =
      poly (set_to_poly B) x * poly (set_to_poly (A - B) * monom 1 (d\<^sub>A - card (A - B))) x"
      by (metis (no_types, lifting) mult.commute mult.left_commute poly_mult)
    thus ?thesis
      using that unfolding assms sp_def sq_def by simp
  qed

  have x_sol_raw: "(\<Sum>j \<in> {0..<d\<^sub>A}. e ^ j * coeff sp j ) + (\<Sum>j \<in> {0..<d\<^sub>B}. - f e * e ^ j * (coeff sq j))
    = f e * e ^ d\<^sub>B - e ^ d\<^sub>A" if "e \<in> set E" for e
  proof -
    have f\<^sub>Az: "f\<^sub>A e \<noteq> 0"
      using assms (7,9) in_set_to_poly that by auto
    moreover have f\<^sub>Bz: "f\<^sub>B e \<noteq> 0"
      using assms (8,10) in_set_to_poly that by auto
    ultimately have fz: "f e \<noteq> 0"
      using that assms(1) by simp
    have ff\<^sub>B: "f e = f\<^sub>A e / f\<^sub>B e"
       using that assms(1) by simp

    have "lead_coeff sp = 1"
      unfolding sp_def lead_coeff_mult using set_to_poly_lead_coeff lead_coeff_monom
      by (auto simp add: degree_monom_eq)
    moreover have "degree sp = d\<^sub>A"
      unfolding sp_def using assms(4)
      by (simp add: add_diff_inverse_nat degree_monom_eq degree_mult_eq order_less_imp_not_less set_to_poly_degree)
    ultimately have poly_sp: "poly sp e = (\<Sum>i<d\<^sub>A. coeff sp i * e ^ i) + e ^ d\<^sub>A" for e
      unfolding poly_lead_coeff_extract by simp

    have "lead_coeff sq = 1"
      unfolding sq_def lead_coeff_mult using set_to_poly_lead_coeff lead_coeff_monom
      by (auto simp add: degree_monom_eq)
    moreover have "degree sq = d\<^sub>B"
      using assms(5) unfolding sq_def
      by (simp add: degree_monom_eq degree_mult_eq le_eq_less_or_eq set_to_poly_degree)
    ultimately have poly_sq: "poly sq e = (\<Sum>i<d\<^sub>B. coeff sq i * e ^ i) + e ^ d\<^sub>B" for e
      unfolding poly_lead_coeff_extract by simp

    have "f\<^sub>B e * ((\<Sum>i = 0..<d\<^sub>A. coeff sp i * e ^ i) + e ^ d\<^sub>A) =
          f\<^sub>A e * ((\<Sum>i = 0..<d\<^sub>B. coeff sq i * e ^ i) + e ^ d\<^sub>B)"
      using that poly_mul_eq unfolding poly_sq poly_sp lessThan_atLeast0 by simp
    then have "f\<^sub>B e * ((\<Sum>j = 0..<d\<^sub>A. e ^ j * coeff sp j) + e ^ d\<^sub>A) =
               f\<^sub>A e * ((\<Sum>j = 0..<d\<^sub>B. e ^ j * coeff sq j) + e ^ d\<^sub>B)"
      by (metis (lifting) Finite_Cartesian_Product.sum_cong_aux mult.commute)
    then have "(\<Sum>j = 0..<d\<^sub>A. e ^ j * coeff sp j) + e ^ d\<^sub>A =
        f e * ((\<Sum>j = 0..<d\<^sub>B. e ^ j * coeff sq j) + e ^ d\<^sub>B)"
      unfolding ff\<^sub>B using f\<^sub>Bz
      by (metis (no_types, lifting) f\<^sub>Bz nonzero_mult_div_cancel_left times_divide_eq_left)
    also have "\<dots> = f e * (\<Sum>j = 0..<d\<^sub>B. e ^ j * coeff sq j) + f e * e ^ d\<^sub>B"
      by algebra
    also have "\<dots> = (\<Sum>j = 0..<d\<^sub>B. f e * e ^ j * coeff sq j) + f e * e ^ d\<^sub>B"
      by (metis (no_types, lifting) Finite_Cartesian_Product.sum_cong_aux mult.assoc sum_distrib_left)
    finally have "(\<Sum>j = 0..<d\<^sub>A. e ^ j * coeff sp j) + e ^ d\<^sub>A =
        (\<Sum>j = 0..<d\<^sub>B. f e * e ^ j * coeff sq j) + f e * e ^ d\<^sub>B"
      by argo
    then have "(\<Sum>j = 0..<d\<^sub>A. e ^ j * coeff sp j) =
        (\<Sum>j = 0..<d\<^sub>B. f e * e ^ j * coeff sq j) + f e * e ^ d\<^sub>B - e ^ d\<^sub>A"
      using add_implies_diff by blast
    then have "(\<Sum>j = 0..<d\<^sub>A. e ^ j * coeff sp j) + (- (\<Sum>j = 0..<d\<^sub>B. f e * e ^ j * coeff sq j)) =
        f e * e ^ d\<^sub>B - e ^ d\<^sub>A"
      by auto
    moreover have "- (\<Sum>j = 0..<d\<^sub>B. f e * e ^ j * (coeff sq j)) =
        (\<Sum>j = 0..<d\<^sub>B. - f e * e ^ j * coeff sq j)"
      using sum_negf [symmetric] by auto
    ultimately show ?thesis
      by argo
  qed

  (* Now we need to convert it to the matrix product representation *)

  let ?const_lam = "\<lambda>e. f e * e ^ d\<^sub>B - e ^ d\<^sub>A"
  let ?const_lam' = "\<lambda>i. ?const_lam (E ! i)"
  let ?coeff_lam = "\<lambda>e j.(if j < d\<^sub>A then e ^ j
             else if j < d\<^sub>A + d\<^sub>B
                  then - f e * e ^ ( j - d\<^sub>A) else 0) *
            (if j < d\<^sub>A then coeff sp j else coeff sq (j- d\<^sub>A))"
  let ?coeff_lam' = "\<lambda>i . ?coeff_lam (E ! i)"


  have "(\<Sum>j \<in> {0..<length E}. ?coeff_lam e j) = ?const_lam e" if "e \<in> set E" for e
  proof -
    have "(\<Sum>j \<in> {0..<length E}. ?coeff_lam e j) = (\<Sum>j \<in> {0..<d\<^sub>A + d\<^sub>B}. ?coeff_lam e j)"
      using assms(3) by (intro sum.mono_neutral_cong_right) auto
    also have "\<dots> = (\<Sum>j\<in>{0..<d\<^sub>A}. e^j * coeff sp j) + (\<Sum>j \<in> {0..<d\<^sub>B}. -f e * e^j*(coeff sq j))"
    proof -
      have "(\<Sum>j \<in> {0..<d\<^sub>A + d\<^sub>B}. ?coeff_lam e j) =
          (\<Sum>j \<in> {0..<d\<^sub>A}. ?coeff_lam e j) + (\<Sum>j \<in> {d\<^sub>A..<d\<^sub>A + d\<^sub>B}. ?coeff_lam e j) "
        by (intro sum.atLeastLessThan_concat [symmetric]) auto
      also have "\<dots> = (\<Sum>j \<in> {0..<d\<^sub>A}. e ^ j * coeff sp j ) +
         (\<Sum>j \<in> {d\<^sub>A..<d\<^sub>A + d\<^sub>B}. - f e * e ^ (j - d\<^sub>A) * (coeff sq (j-d\<^sub>A))) "
        by simp
      moreover have "(\<Sum>j \<in> {d\<^sub>A..<d\<^sub>A + d\<^sub>B}. - f e * e ^ (j - d\<^sub>A) * (coeff sq (j-d\<^sub>A))) =
          (\<Sum>j \<in> {0..<d\<^sub>B}. - f e * e ^ (j) * (coeff sq j))"
        by (rule sum.reindex_bij_witness [of _ "\<lambda>i. i + d\<^sub>A" "\<lambda>i. i - d\<^sub>A"]) auto
      ultimately show ?thesis
        by simp
    qed
    also have "\<dots> = ?const_lam e"
      using that x_sol_raw by simp
    finally show ?thesis by simp
  qed
  then have "(\<Sum>j \<in> {0..<length E}. ?coeff_lam' i j) = ?const_lam' i" if "i < length E" for i
    using that  by simp
  moreover have "(\<Sum>j\<in>(UNIV::'m set). ?coeff_lam i (to_nat j)) = (\<Sum>j \<in> {0..<CARD('m)}. ?coeff_lam i j)" for i
    using bij_to_nat by (intro sum.reindex_bij_betw) blast
  ultimately have "(\<Sum>j\<in>(UNIV::'m set). ?coeff_lam' i (to_nat j)) = ?const_lam' i" if "i < length E" for i
    using that assms using of_nat_eq_iff[of "card top" "length E"] assms(3) by force
  then have "(\<lambda>i. \<Sum>j\<in>(UNIV::'m set). ?coeff_lam' i (to_nat j)) (to_nat (i::'m)) = ?const_lam' (to_nat i)" for i
    using mod_type_less_function_eq [of "(\<lambda>i. \<Sum>j\<in>(UNIV::'m set). ?coeff_lam' i (to_nat j))" ?const_lam' i]
    using assms(2) assms(3) by auto
  then have eval: "(\<lambda>i. \<Sum>j\<in>(UNIV::'m set). ?coeff_lam' (to_nat (i::'m)) (to_nat j)) =
      (\<lambda> i. ?const_lam' (to_nat i))"
    by simp

  have "?coeff' *v ?x = ?const'"
    unfolding matrix_vector_mult_def
      rfi_coefficient_matrix_def
      rfi_constant_vector_def
    using eval by simp
  then show ?thesis
    unfolding consistent_def is_solution_def by auto
qed

subsection \<open>Main lemma\<close>

lemma rational_function_interpolation_correct:
  assumes
    "int d\<^sub>A = \<lfloor>(real (length E) + card A - card B)/2\<rfloor>"
    "int d\<^sub>B = \<lfloor>(real (length E) + card B - card A)/2\<rfloor>"
    "card (sym_diff A B) \<le> length E"

    "\<forall> x \<in> set E. x \<notin> A" "\<forall> x \<in> set E. x \<notin> B"
    "f\<^sub>A = (\<lambda> x \<in> set E. poly (set_to_poly A) x)"
    "f\<^sub>B = (\<lambda> x \<in> set E. poly (set_to_poly B) x)"
    "CARD('m::mod_type) = length E"
  defines
    "sol \<equiv> solution_to_poly (rational_function_interpolation E (\<lambda>e. f\<^sub>A e / f\<^sub>B e) d\<^sub>A d\<^sub>B TYPE('m)) d\<^sub>A d\<^sub>B"
  shows
    "monic_interpolated_rational_function (fst sol) (snd sol) (set E) f\<^sub>A f\<^sub>B d\<^sub>A d\<^sub>B"
proof -
  let ?f = "(\<lambda>e. f\<^sub>A e / f\<^sub>B e)"
  let ?S = "rational_function_interpolation E (\<lambda>e. f\<^sub>A e / f\<^sub>B e) d\<^sub>A d\<^sub>B TYPE('m)"
  let ?p = "fst (solution_to_poly ?S d\<^sub>A d\<^sub>B)"
  let ?q = "snd (solution_to_poly ?S d\<^sub>A d\<^sub>B)"

  have f:"finite A" "finite B"
    using finite by blast+
  note pd_pq_props = d\<^sub>A_d\<^sub>B_helper[OF f assms(1-3)]

  have "consistent (\<chi> (i::'m) (j::'m). rfi_coefficient_matrix E ?f d\<^sub>A d\<^sub>B (to_nat i) (to_nat j))
        (\<chi> (i::'m). rfi_constant_vector E ?f d\<^sub>A d\<^sub>B (to_nat i))"
    using assms pd_pq_props
    by (intro rational_function_interpolation_consistent [where A = A and B = B and f\<^sub>A = f\<^sub>A and f\<^sub>B = f\<^sub>B])
      auto
  then have "\<forall>e\<in>set E. f\<^sub>A e * poly ?q e = f\<^sub>B e * poly ?p e"
    using assms pd_pq_props(1) in_set_to_poly
    by (intro rational_function_interpolation_correct_poly [where f = ?f and d\<^sub>A = d\<^sub>A and d\<^sub>B = d\<^sub>B and S = ?S])
      auto
  moreover have "real (degree ?p) = real d\<^sub>A"
    using degree_solution_to_poly_fst by auto
  moreover have "real (degree ?q) = real d\<^sub>B"
    using degree_solution_to_poly_snd by auto
  moreover have "monic ?q"
    using monic_solution_to_poly_snd by auto
  moreover have "monic ?p"
    using monic_solution_to_poly_fst by auto
  ultimately show ?thesis using fst_solution_to_poly_nz snd_solution_to_poly_nz
    unfolding monic_interpolated_rational_function_def sol_def by force
qed

(*Can also interpolate poly with floor of degree*)
lemma interpolated_rational_function_floor_eq:
  "interpolated_rational_function p\<^sub>A p\<^sub>B E f\<^sub>A f\<^sub>B d\<^sub>A d\<^sub>B \<longleftrightarrow>
   interpolated_rational_function p\<^sub>A p\<^sub>B E f\<^sub>A f\<^sub>B \<lfloor>d\<^sub>A\<rfloor> \<lfloor>d\<^sub>B\<rfloor>"
  unfolding interpolated_rational_function_def using nat_leq_real_floor by simp

lemma sym_diff_bound_div2_ge0:
  fixes A B :: "'a :: finite set"
  assumes "card (sym_diff A B) \<le> length E"
  shows "(real (length E) + card A - card B)/2 \<ge> 0"
proof -
  have *: "finite A" "finite B" using finite by auto

  have "0 \<le> real (card (sym_diff A B)) + real (card (A-B)) - (card (B-A))"
    unfolding card_sym_diff_finite[OF *] by simp
  also have "\<dots> \<le> real (length E) + real (card (A-B)) - (card (B-A))"
    using assms(1) by simp
  also have "\<dots> = (real (length E) + card A - card B)"
    using card_sub_int_diff_finite [OF *] by simp
  finally show ?thesis by simp
qed

text "If the degrees are reals we take the floor first"
lemma rational_function_interpolation_correct_real:
  fixes d'\<^sub>A d'\<^sub>B:: "real"
  assumes
    "card (sym_diff A B) \<le> length E"
    "\<forall> x \<in> set E. x \<notin> A" "\<forall> x \<in> set E. x \<notin> B"
    "f\<^sub>A = (\<lambda> x \<in> set E. poly (set_to_poly A) x)"
    "f\<^sub>B = (\<lambda> x \<in> set E. poly (set_to_poly B) x)"
    "CARD('m::mod_type) = length E"
  defines "d'\<^sub>A \<equiv> (real (length E) + card A - card B)/2"
  defines "d'\<^sub>B \<equiv> (real (length E) + card B - card A)/2"
  defines "d\<^sub>A \<equiv> nat \<lfloor>d'\<^sub>A\<rfloor>"
  defines "d\<^sub>B \<equiv> nat \<lfloor>d'\<^sub>B\<rfloor>"
  defines "sol_poly \<equiv> interpolate_rat_fun E (\<lambda>e. f\<^sub>A e / f\<^sub>B e) d\<^sub>A d\<^sub>B TYPE('m)"
  shows
    "monic_interpolated_rational_function (fst sol_poly) (snd sol_poly) (set E) f\<^sub>A f\<^sub>B d'\<^sub>A d'\<^sub>B"
proof -
  have e: "d'\<^sub>A \<ge> 0"
    unfolding d'\<^sub>A_def using sym_diff_bound_div2_ge0 assms(1) by auto

  hence a: "int d\<^sub>A = \<lfloor>(real (length E) + real (card A) - real (card B)) / 2\<rfloor>"
    using d'\<^sub>A_def unfolding d\<^sub>A_def by simp

  have f: "d'\<^sub>B \<ge> 0"
    unfolding d'\<^sub>B_def using sym_diff_bound_div2_ge0 assms(1) by (metis Un_commute)

  hence b: "int d\<^sub>B = \<lfloor>(real (length E) + real (card B) - real (card A)) / 2\<rfloor>"
    using d'\<^sub>B_def unfolding d\<^sub>B_def by simp

  have c: "monic_interpolated_rational_function (fst sol_poly) (snd sol_poly) (set E) f\<^sub>A f\<^sub>B d\<^sub>A d\<^sub>B"
    unfolding sol_poly_def interpolate_rat_fun_def
    by (intro rational_function_interpolation_correct [OF a b assms(1-6)])
  moreover have "\<lfloor>d'\<^sub>A\<rfloor> = real (nat \<lfloor>d'\<^sub>A\<rfloor>)"
    using e by (intro of_nat_nat[symmetric]) simp
  moreover have "\<lfloor>d'\<^sub>B\<rfloor> = real (nat \<lfloor>d'\<^sub>B\<rfloor>)"
    using f by (intro of_nat_nat[symmetric]) simp
  ultimately have
    "monic_interpolated_rational_function (fst sol_poly) (snd sol_poly) (set E) f\<^sub>A f\<^sub>B (nat \<lfloor>d'\<^sub>A\<rfloor>) (nat \<lfloor>d'\<^sub>B\<rfloor>)"
    unfolding d\<^sub>A_def d\<^sub>B_def
    by simp
  thus ?thesis unfolding monic_interpolated_rational_function_def
    using assms(9,10) a b d'\<^sub>A_def d'\<^sub>B_def floor_of_nat by simp
qed

end
