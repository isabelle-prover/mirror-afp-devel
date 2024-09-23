(*
  File:     Kummer_Congruence/Rat_Congruence.thy
  Author:   Manuel Eberl, University of Innsbruck

  Defining modulo and congruences on rational numbers.
  Also the p-adic valuation of a rational.
*)
section \<open>Congruence of rational numbers modulo an integer\<close>
theory Rat_Congruence
  imports Kummer_Library
begin

(* TODO: this could go into HOL-Number_Theory *)

subsection \<open>$p$-adic valuation of a rational\<close>

text \<open>
  The notion of the multiplicity $\nu_p(n)$ of a prime $p$ in an integer $n$ can be generalised to 
  rational numbers via $\nu_p(a / b) = \nu_p(a) - \nu_p(b)$. This is also called the $p$-adic
  valuation of $a / b$.
\<close>
definition qmultiplicity :: "int \<Rightarrow> rat \<Rightarrow> int" where
  "qmultiplicity p x = (case quotient_of x of (a, b) \<Rightarrow> int (multiplicity p a) - int (multiplicity p b))"

lemma qmultiplicity_of_int [simp]:
  "qmultiplicity p (of_int n) = int (multiplicity p n)"
proof -
  have "quotient_of (of_int n) = (n, 1)"
    by (intro quotient_of_eqI) auto
  thus ?thesis
    by (simp add: qmultiplicity_def)
qed

lemma qmultiplicity_of_nat [simp]:
  "qmultiplicity p (of_nat n) = int (multiplicity p n)"
  using qmultiplicity_of_int[of p "int n"] by (simp del: qmultiplicity_of_int)

lemma qmultiplicity_numeral [simp]:
  "qmultiplicity p (numeral n) = int (multiplicity p (numeral n))"
  using qmultiplicity_of_nat[of p "numeral n"] by (simp del: qmultiplicity_of_nat)

lemma qmultiplicity_0 [simp]: "qmultiplicity p 0 = 0"
  by (simp add: qmultiplicity_def)

lemma qmultiplicity_1 [simp]: "qmultiplicity p 1 = 0"
  by (simp add: qmultiplicity_def)

lemma qmultiplicity_minus [simp]: "qmultiplicity p (-x) = qmultiplicity p x"
  by (auto simp: qmultiplicity_def rat_uminus_code case_prod_unfold Let_def)

lemma qmultiplicity_divide_of_int:
  assumes "x \<noteq> 0" "y \<noteq> 0" "prime_elem p"
  shows   "qmultiplicity p (of_int x / of_int y) = int (multiplicity p x) - int (multiplicity p y)"
proof -
  define d where "d = sgn y * gcd x y"
  define x' y' where "x' = x div d" and "y' = y div d"
  have xy_eq: "x = x' * d" "y = y' * d"
    unfolding x'_def y'_def d_def using assms by (auto simp: sgn_if)
  have "sgn y = sgn y' * sgn d"
    using assms by (auto simp: xy_eq sgn_mult)
  also have "sgn d = sgn y"
    using assms by (auto simp: d_def sgn_mult)
  finally have "y' > 0"
    using assms by (auto simp: sgn_if split: if_splits)

  have "gcd x y = gcd x' y' * \<bar>d\<bar>"
    by (auto simp: xy_eq gcd_mult_right abs_mult gcd.commute)
  also have "\<bar>d\<bar> = gcd x y"
    using assms by (simp add: d_def abs_mult)
  finally have "gcd x' y' = 1"
    using assms by simp
  hence "coprime x' y'"
    by blast

  have "d \<noteq> 0" "x' \<noteq> 0" "y' \<noteq> 0"
    using assms by (auto simp: xy_eq)
  hence "(of_int x / of_int y :: rat) = (of_int x' / of_int y')"
    by (auto simp: xy_eq field_simps)
  also have "quotient_of \<dots> = (x', y')"
    using \<open>coprime x' y'\<close> \<open>y' > 0\<close> by (intro quotient_of_eqI) (auto simp: )
  hence "qmultiplicity p (of_int x' / of_int y') = int (multiplicity p x') - int (multiplicity p y')"
    by (simp add: qmultiplicity_def)
  also have "\<dots> = int (multiplicity p x' + multiplicity p d) - int (multiplicity p y' + multiplicity p d)"
    by simp
  also have "\<dots> = int (multiplicity p x) - int (multiplicity p y)"
    using assms unfolding xy_eq by (subst (1 2) prime_elem_multiplicity_mult_distrib) auto
  finally show ?thesis .
qed

lemma qmultiplicity_mult [simp]:
  assumes "prime_elem p" "x \<noteq> 0" "y \<noteq> 0"
  shows   "qmultiplicity p (x * y) = qmultiplicity p x + qmultiplicity p y"
proof -
  obtain a b where ab: "quotient_of x = (a, b)"
    using prod.exhaust by blast
  obtain c d where cd: "quotient_of y = (c, d)"
    using prod.exhaust by blast
  have x: "x = of_int a / of_int b \<and> b > 0"
    using ab by (simp add: quotient_of_denom_pos quotient_of_div)
  have y: "y = of_int c / of_int d \<and> d > 0"
    using cd by (simp add: quotient_of_denom_pos quotient_of_div)
  have [simp]: "a \<noteq> 0" "b \<noteq> 0" "c \<noteq> 0" "d \<noteq> 0"
    using assms x y by auto
  have "x * y = of_int (a * c) / of_int (b * d)"
    by (simp add: x y)
  also have "qmultiplicity p \<dots> = int (multiplicity p (a * c)) - int (multiplicity p (b * d))"
    using assms(1) by (subst qmultiplicity_divide_of_int) auto
  also have "\<dots> = qmultiplicity p x + qmultiplicity p y"
    using assms(1)
    by (subst (1 2) prime_elem_multiplicity_mult_distrib)
       (auto simp: x y qmultiplicity_divide_of_int)
  finally show ?thesis .
qed  

lemma qmultiplicity_inverse [simp]:
  "qmultiplicity p (inverse x) = -qmultiplicity p x"
proof (cases "x = 0")
  case False
  hence "fst (quotient_of x) \<noteq> 0"
    by (metis div_0 fst_conv of_int_0 quotient_of_div surj_pair)
  thus ?thesis
    by (auto simp: qmultiplicity_def rat_inverse_code case_prod_unfold Let_def sgn_if)
qed auto

lemma qmultiplicity_divide [simp]:
  assumes "prime_elem p" "x \<noteq> 0" "y \<noteq> 0"
  shows   "qmultiplicity p (x / y) = qmultiplicity p x - qmultiplicity p y"
proof -
  have "qmultiplicity p (x / y) = qmultiplicity p (x * inverse y)"
    by (simp add: field_simps)
  also have "\<dots> = qmultiplicity p x - qmultiplicity p y"
    using assms by (subst qmultiplicity_mult) auto
  finally show ?thesis .
qed

lemma qmultiplicity_nonneg_iff:
  assumes "a \<noteq> 0" "b \<noteq> 0" "coprime a b" "prime p"
  shows   "qmultiplicity p (of_int a / of_int b) \<ge> 0 \<longleftrightarrow> \<not>p dvd b"
proof -
  have "qmultiplicity p (of_int a / of_int b) = int (multiplicity p a) - int (multiplicity p b)"
    using assms by (subst qmultiplicity_divide_of_int) auto
  also have "\<dots> \<ge> 0 \<longleftrightarrow> \<not>p dvd b"
  proof (cases "p dvd b")
    case True
    hence "\<not>p dvd a"
      using \<open>coprime a b\<close> \<open>prime p\<close> by (meson coprime_common_divisor_int not_prime_unit zdvd1_eq)
    hence "multiplicity p a = 0"
      using not_dvd_imp_multiplicity_0 by blast
    moreover have "multiplicity p b \<ge> 1"
      using True assms by (intro multiplicity_geI) auto
    ultimately show ?thesis
      using True by simp
  next
    case False
    hence "multiplicity p b = 0"
      using not_dvd_imp_multiplicity_0 by blast
    thus ?thesis
      using False by simp
  qed
  finally show ?thesis .
qed

lemma qmultiplicity_nonneg_imp_not_dvd_denom:
  assumes "qmultiplicity p x \<ge> 0" "\<bar>p\<bar> \<noteq> 1"
  shows   "\<not>p dvd snd (quotient_of x)"
proof -
  obtain a b where ab: "quotient_of x = (a, b)"
    using prod.exhaust by blast
  have "b > 0"
    using ab quotient_of_denom_pos by blast
  have "\<not>p dvd b"
  proof
    assume "p dvd b"
    hence "multiplicity p b \<ge> 1"
      using assms(2) \<open>b > 0\<close> by (intro multiplicity_geI) auto
    moreover have "coprime a b"
      using ab by (simp add: quotient_of_coprime)
    hence "\<not>p dvd a"
      using \<open>p dvd b\<close> assms(2) coprime_common_divisor_int by blast
    hence "multiplicity p a = 0"
      by (intro not_dvd_imp_multiplicity_0)
    ultimately show False
      using assms by (simp add: qmultiplicity_def ab)
  qed
  thus ?thesis
    by (simp add: ab)
qed

lemma qmultiplicity_prime_nonneg_imp_coprime_denom:
  assumes "qmultiplicity p x \<ge> 0" "prime p"
  shows   "coprime (snd (quotient_of x)) p"
  using qmultiplicity_nonneg_imp_not_dvd_denom[OF assms(1)] assms(2)
  by (simp add: coprime_commute prime_ge_0_int prime_imp_coprime_int)


subsection \<open>Rational modulo operation\<close>

text \<open>
  Similarly, we can define $(a / b)\ \text{mod}\ m$ whenever $b$ and $m$ are coprime by choosing to
   interpret $(1 / b)\ \text{mod}\ m$ as the modular inverse of $b$ modulo $m$:
\<close>
definition qmod :: "rat \<Rightarrow> int \<Rightarrow> int" (infixl \<open>qmod\<close> 70) where
  "x qmod m = (let (a, b) = quotient_of x in if coprime b m then (a * modular_inverse m b) mod m else 0)"

lemma qmod_mod_absorb [simp]: "x qmod m mod m = x qmod m"
  by (simp add: qmod_def case_prod_unfold Let_def)

lemma qmod_of_nat [simp]: "m > 1 \<Longrightarrow> of_nat x qmod m = int x mod m"
  by (simp add: qmod_def)

lemma qmod_of_int [simp]: "m > 1 \<Longrightarrow> of_int x qmod m = x mod m"
  by (simp add: qmod_def)

lemma qmod_numeral [simp]: "m > 1 \<Longrightarrow> numeral n qmod m = numeral n mod m"
  by (simp add: qmod_def)

lemma qmod_0 [simp]: "0 qmod m = 0"
  by (simp add: qmod_def)

lemma qmod_1 [simp]: "m > 1 \<Longrightarrow> 1 qmod m = 1"
  by (simp add: qmod_def)

lemma qmod_fraction_eq:
  assumes "coprime b m" "b \<noteq> 0" "m > 0"
  shows   "(of_int a / of_int b) qmod m = a * modular_inverse m b mod m"
proof -
  define d where "d = sgn b * gcd a b"
  define a' where "a' = a div d"
  define b' where "b' = b div d"
  have "d dvd a" "d dvd b"
    using assms unfolding d_def by auto
  hence a_eq: "a = a' * d" and b_eq: "b = b' * d"
    unfolding a'_def b'_def d_def by auto
  have "d \<noteq> 0"
    unfolding d_def using assms by (auto simp: sgn_if)
  hence "sgn d = sgn b"
    by (auto simp: d_def sgn_mult)
  moreover have "sgn b' = sgn d * sgn b"
    using \<open>d \<noteq> 0\<close> by (simp add: b_eq sgn_mult)
  ultimately have "sgn b' = 1"
    using assms by simp
  hence "b' > 0"
    by (auto simp: sgn_if split: if_splits)
  have "gcd a b = gcd a' b' * \<bar>d\<bar>"
    by (simp add: a_eq b_eq gcd_mult_right abs_mult gcd.commute)
  also have "\<bar>d\<bar> = gcd a b"
    using assms by (simp add: d_def abs_mult)
  finally have "gcd a' b' = 1"
    using assms(2) by simp
  hence "coprime a' b'"
    by auto
  have "coprime b' m" "coprime d m"
    using assms(1) b_eq by simp_all
  have ab': "quotient_of (of_int a / of_int b) = (a', b')"
    using \<open>b' > 0\<close> \<open>coprime a' b'\<close> \<open>d \<noteq> 0\<close> by (intro quotient_of_eqI) (auto simp: a_eq b_eq)

  have "(of_int a / of_int b) qmod m = a' * modular_inverse m b' mod m"
    using \<open>coprime b' m\<close> by (simp add: qmod_def ab')
  also have "[\<dots> = a' * 1 * modular_inverse m b'] (mod m)"
    by simp
  also have "[a' * 1 * modular_inverse m b' = a' * (d * modular_inverse m d) * modular_inverse m b'] (mod m)"
    by (intro cong_mult cong_refl cong_sym[OF cong_modular_inverse1] \<open>coprime d m\<close>)
  also have "a' * (d * modular_inverse m d) * modular_inverse m b' =
             (a' * d) * (modular_inverse m d * modular_inverse m b')"
    by (simp add: mult_ac)
  also have "[(a' * d) * (modular_inverse m d * modular_inverse m b') =
              (a' * d) * (modular_inverse m d * modular_inverse m b' mod m)] (mod m)"
    by (intro cong_mult cong_refl) auto
  also have "modular_inverse m d * modular_inverse m b' mod m = modular_inverse m (b' * d)"
    by (rule modular_inverse_int_mult [symmetric]) (use \<open>coprime b' m\<close> \<open>coprime d m\<close> \<open>m > 0\<close> in auto)
  also have "[(a' * d) * modular_inverse m (b' * d) = a * modular_inverse m b mod m] (mod m)"
    by (simp add: a_eq b_eq)
  finally show ?thesis
    by (simp add: Cong.cong_def)
qed


subsection \<open>Congruence relation\<close>

text \<open>
  With this, it is now straightforward to define the congruence relation
   $x = y\ (\text{mod}\ m)$ for rational $x$, $y$:
\<close>
definition qcong :: "rat \<Rightarrow> rat \<Rightarrow> int \<Rightarrow> bool" (\<open>(1[_ = _] '(' qmod _'))\<close>) where
  "[a = b] (qmod m) \<longleftrightarrow>
     coprime (snd (quotient_of a)) m \<and> coprime (snd (quotient_of b)) m \<and> a qmod m = b qmod m"

lemma qcong_of_int_iff [simp]:
  assumes "m > 1"
  shows   "[of_int a = of_int b] (qmod m) \<longleftrightarrow> [a = b] (mod m)"
  using assms by (auto simp: qcong_def Cong.cong_def)

lemma cong_imp_qcong:
  assumes "[a = b] (mod m)" "m > 1"
  shows   "[of_int a = of_int b] (qmod m)"
  using assms by (auto simp: qcong_def Cong.cong_def)

lemma cong_imp_qcong_of_nat:
  assumes "[a = b] (mod m)" "m > 1"
  shows   "[of_nat a = of_nat b] (qmod m)"
  using cong_imp_qcong assms 
  by (metis cong_int_iff of_int_of_nat_eq of_nat_1 of_nat_less_iff)

lemma qcong_refl [intro]: "coprime (snd (quotient_of q)) m \<Longrightarrow> [q = q] (qmod m)"
  by (auto simp: qcong_def)

lemma qcong_sym_eq: "[q1 = q2] (qmod m) \<longleftrightarrow> [q2 = q1] (qmod m)"
  by (simp add: qcong_def conj_ac eq_commute)

lemma qcong_sym: "[q1 = q2] (qmod m) \<Longrightarrow> [q2 = q1] (qmod m)"
  using qcong_sym_eq by blast

lemma qcong_trans [trans]:
  assumes "[q1 = q2] (qmod m)" "[q2 = q3] (qmod m)"
  shows   "[q1 = q3] (qmod m)"
  using assms by (auto simp: qcong_def)

lemma qcong_0D:
  assumes "[x = 0] (qmod m)"
  shows   "m dvd fst (quotient_of x)"
proof -
  have 1: "coprime (snd (quotient_of x)) m"
   and 2: "m dvd fst (quotient_of x) * modular_inverse m (snd (quotient_of x))"
    using assms by (auto simp: qcong_def qmod_def case_prod_unfold Let_def)
  have 3: "coprime (modular_inverse m (snd (quotient_of x))) m"
    using 1 by blast
  from 1 2 3 show ?thesis
    using coprime_commute coprime_dvd_mult_left_iff by blast
qed

lemma qcong_0_iff:
  "[x = 0] (qmod m) \<longleftrightarrow> m dvd fst (quotient_of x) \<and> coprime (snd (quotient_of x)) m"
proof
  assume "m dvd fst (quotient_of x) \<and> coprime (snd (quotient_of x)) m"
  thus "[x = 0] (qmod m)"
    by (auto simp: qcong_def qmod_def case_prod_unfold)
qed (use qcong_0D[of x m] in \<open>auto simp: qcong_def\<close>)

lemma qcong_1 [simp]: "[a = b] (qmod 1)"
  by (simp_all add: qcong_def qmod_def)

lemma mod_minus_cong':
  fixes a b :: "'a :: euclidean_ring_cancel"
  assumes "(- a) mod b = (- a') mod b"
  shows "a mod b = a' mod b"
  using mod_minus_cong[OF assms] by simp

lemma qcong_minus_minus_iff:
  "[-b = -c] (qmod a) \<longleftrightarrow> [b = c] (qmod a)"
  by (auto simp: qcong_def rat_uminus_code case_prod_unfold Let_def qmod_def
           dest: mod_minus_cong' intro: mod_minus_cong)

lemma qcong_minus: "[b = c] (qmod a) \<Longrightarrow> [-b = -c] (qmod a)"
  by (simp only: qcong_minus_minus_iff)

lemma qcong_fraction_iff:
  assumes "b \<noteq> 0" "d \<noteq> 0" "coprime b m" "coprime d m" "m > 0"
  shows   "[of_int a / of_int b = of_int c / of_int d] (qmod m) \<longleftrightarrow> [a * d = b * c] (mod m)"
proof
  assume *: "[of_int a / of_int b = of_int c / of_int d] (qmod m)"
  have "[a * 1 * d = a * (modular_inverse m b * b) * d] (mod m)"
    by (rule cong_sym, intro cong_mult cong_modular_inverse2 cong_refl assms)
  also from * have "rat_of_int a / rat_of_int b qmod m = rat_of_int c / rat_of_int d qmod m"
    by (auto simp: qcong_def)
  hence "[a * modular_inverse m b = c * modular_inverse m d] (mod m)"
    using assms by (auto simp: qmod_fraction_eq Cong.cong_def)
  hence "[a * modular_inverse m b * (b * d) = c * modular_inverse m d * (b * d)] (mod m)"
    by (rule cong_mult) (rule cong_refl)
  hence "[a * (modular_inverse m b * b) * d = c * (modular_inverse m d * d) * b] (mod m)"
    by (simp add: mult_ac)
  also have "[c * (modular_inverse m d * d) * b = c * 1 * b] (mod m)"
    by (intro cong_mult cong_modular_inverse2 cong_refl assms)
  finally show "[a * d = b * c] (mod m)"
    by (simp add: mult_ac)
next
  assume *: "[a * d = b * c] (mod m)"
  have "rat_of_int a / rat_of_int b qmod m = a * modular_inverse m b mod m"
    using assms by (subst qmod_fraction_eq) auto
  have "rat_of_int c / rat_of_int d qmod m = c * modular_inverse m d mod m"
    using assms by (subst qmod_fraction_eq) auto
  let ?b' = "modular_inverse m b" and ?d' = "modular_inverse m d"
  have "[a * ?b' mod m = a * 1 * ?b'] (mod m)"
    by auto
  also have "[a * 1 * ?b' = a * (d * ?d') * ?b'] (mod m)"
    by (rule cong_sym, intro cong_mult cong_modular_inverse1 cong_refl assms)
  also have "[a * d * (?b' * ?d') = b * c * (?b' * ?d')] (mod m)"
    using * by (rule cong_mult) (rule cong_refl)
  hence "[a * (d * ?d') * ?b' = b * ?b' * c * ?d'] (mod m)"
    by (simp add: mult_ac)
  also have "[b * ?b' * c * ?d' = 1 * c * ?d'] (mod m)"
    by (intro cong_mult cong_modular_inverse1 cong_refl assms)
  also have "[1 * c * ?d' = c * ?d' mod m] (mod m)"
    by auto
  finally have "rat_of_int a / rat_of_int b qmod m = rat_of_int c / rat_of_int d qmod m"
    using assms by (simp add: qmod_fraction_eq Cong.cong_def)
  moreover have "coprime (snd (Rat.normalize (a, b))) m" "coprime (snd (Rat.normalize (c, d))) m"
    using dvd_rat_normalize assms by (meson coprime_divisors dvd_refl)+
  ultimately show "[of_int a / of_int b = of_int c / of_int d] (qmod m)"
    unfolding qcong_def by (auto simp: quotient_of_fraction_conv_normalize)
qed  

lemma qcong_fractionI:
  assumes "x = of_int a / of_int b" "b \<noteq> 0" "coprime b m"
  shows   "[x = of_int a / of_int b] (qmod m)"
proof -
  obtain a' b' where ab: "quotient_of x = (a', b')"
    using prod.exhaust by blast
  have "(a', b') = Rat.normalize (a, b)"
    using assms ab by (metis Fract_of_int_quotient quotient_of_Fract)
  hence "b' dvd b"
    unfolding Rat.normalize_def
    by (metis assms(2) dvd_def dvd_div_mult_self gcd_dvd2 minus_dvd_iff snd_eqD)
  with assms have "coprime b' m"
    by (meson coprime_divisors dvd_refl)
  thus ?thesis
    unfolding assms(1) using ab by (intro qcong_refl) (auto simp: assms(1))
qed

lemma qcong_add:
  assumes "[x = x'] (qmod m)" "[y = y'] (qmod m)" "m > 0"
  shows   "[x + y = x' + y'] (qmod m)"
proof -
  obtain a b where ab: "quotient_of x = (a, b)"
    using prod.exhaust by blast
  obtain c d where cd: "quotient_of y = (c, d)"
    using prod.exhaust by blast
  obtain a' b' where ab': "quotient_of x' = (a', b')"
    using prod.exhaust by blast
  obtain c' d' where cd': "quotient_of y' = (c', d')"
    using prod.exhaust by blast
  have x_eq: "x = of_int a / of_int b" and y_eq: "y = of_int c / of_int d"
    using ab cd quotient_of_div by blast+
  have x'_eq: "x' = of_int a' / of_int b'" and y'_eq: "y' = of_int c' / of_int d'"
    using ab' cd' quotient_of_div by blast+
  have pos: "b > 0" "d > 0" "b' > 0" "d' > 0"
    using ab cd ab' cd' by (simp_all add: quotient_of_denom_pos)
  have coprime: "coprime b m" "coprime d m" "coprime b' m" "coprime d' m"
    using ab cd ab' cd' assms unfolding qcong_def by auto

  have "[x + y = of_int (a * d + b * c) / of_int (b * d)] (qmod m)"
    using pos coprime by (intro qcong_fractionI) (auto simp: x_eq y_eq field_simps)
  also have "[of_int (a * d + b * c) / of_int (b * d) = of_int (a' * d' + b' * c') / of_int (b' * d')] (qmod m)"
  proof (subst qcong_fraction_iff)
    have cong1: "[a * b' = b * a'] (mod m)"
      using assms(1) pos coprime \<open>m > 0\<close> unfolding x_eq x'_eq
      by (subst (asm) qcong_fraction_iff) auto
    have cong2:"[c * d' = d * c'] (mod m)"
      using assms(2) pos coprime \<open>m > 0\<close> unfolding y_eq y'_eq
      by (subst (asm) qcong_fraction_iff) auto
    have "[(a * d + b * c) * (b' * d') = (a * b') * d * d' + (c * d') * b * b'] (mod m)"
      by (simp add: algebra_simps)
    also have "[(a * b') * d * d' + (c * d') * b * b' = (b * a') * d * d' + (d * c') * b * b'] (mod m)"
      by (intro cong1 cong2 cong_mult[OF _ cong_refl] cong_add cong_refl)
    also have "(b * a') * d * d' + (d * c') * b * b' = b * d * (a' * d' + b' * c')"
      by (simp add: algebra_simps)
    finally show "[(a * d + b * c) * (b' * d') = b * d * (a' * d' + b' * c')] (mod m)" .
  qed (use pos coprime \<open>m > 0\<close> in auto)
  also have "[of_int (a' * d' + b' * c') / of_int (b' * d') = x' + y'] (qmod m)"
    by (rule qcong_sym, rule qcong_fractionI) (use pos coprime in \<open>auto simp: x'_eq y'_eq field_simps\<close>)
  finally show ?thesis .
qed

lemma qcong_diff:
  assumes "[x = x'] (qmod m)" "[y = y'] (qmod m)" "m > 0"
  shows   "[x - y = x' - y'] (qmod m)"
  using qcong_add[OF assms(1) qcong_minus[OF assms(2)]] \<open>m > 0\<close> by simp

lemma qcong_mult:
  assumes "[x = x'] (qmod m)" "[y = y'] (qmod m)" "m > 0"
  shows   "[x * y = x' * y'] (qmod m)"
proof -
  obtain a b where ab: "quotient_of x = (a, b)"
    using prod.exhaust by blast
  obtain c d where cd: "quotient_of y = (c, d)"
    using prod.exhaust by blast
  obtain a' b' where ab': "quotient_of x' = (a', b')"
    using prod.exhaust by blast
  obtain c' d' where cd': "quotient_of y' = (c', d')"
    using prod.exhaust by blast
  have x_eq: "x = of_int a / of_int b" and y_eq: "y = of_int c / of_int d"
    using ab cd quotient_of_div by blast+
  have x'_eq: "x' = of_int a' / of_int b'" and y'_eq: "y' = of_int c' / of_int d'"
    using ab' cd' quotient_of_div by blast+
  have pos: "b > 0" "d > 0" "b' > 0" "d' > 0"
    using ab cd ab' cd' by (simp_all add: quotient_of_denom_pos)
  have coprime: "coprime b m" "coprime d m" "coprime b' m" "coprime d' m"
    using ab cd ab' cd' assms unfolding qcong_def by auto

  have "[x * y = of_int (a * c) / of_int (b * d)] (qmod m)"
    using pos coprime by (intro qcong_fractionI) (auto simp: x_eq y_eq field_simps)
  also have "[of_int (a * c) / of_int (b * d) = of_int (a' * c') / of_int (b' * d')] (qmod m)"
  proof (subst qcong_fraction_iff)
    have cong1: "[a * b' = b * a'] (mod m)"
      using assms(1) pos coprime \<open>m > 0\<close> unfolding x_eq x'_eq
      by (subst (asm) qcong_fraction_iff) auto
    have cong2:"[c * d' = d * c'] (mod m)"
      using assms(2) pos coprime \<open>m > 0\<close> unfolding y_eq y'_eq
      by (subst (asm) qcong_fraction_iff) auto
    have "[a * c * (b' * d') = (a * b') * (c * d')] (mod m)"
      by (simp add: algebra_simps)
    also have "[(a * b') * (c * d') = (b * a') * (d * c')] (mod m)"
      by (intro cong1 cong2 cong_mult)
    also have "(b * a') * (d * c') = b * d * (a' * c')"
      by (simp add: algebra_simps)
    finally show "[a * c * (b' * d') = b * d * (a' * c')] (mod m)" .
  qed (use pos coprime \<open>m > 0\<close> in auto)
  also have "[of_int (a' * c') / of_int (b' * d') = x' * y'] (qmod m)"
    by (rule qcong_sym, rule qcong_fractionI) (use pos coprime in \<open>auto simp: x'_eq y'_eq field_simps\<close>)
  finally show ?thesis .
qed

lemma qcong_divide_of_int:
  assumes "[x = x'] (qmod m)" "[c = c'] (mod m)" "coprime c m" "c \<noteq> 0" "c' \<noteq> 0" "m > 0"
  shows   "[x / of_int c = x' / of_int c'] (qmod m)"
proof -
  obtain a b where ab: "quotient_of x = (a, b)"
    using prod.exhaust by blast
  obtain a' b' where ab': "quotient_of x' = (a', b')"
    using prod.exhaust by blast
  have x_eq: "x = of_int a / of_int b" and x'_eq: "x' = of_int a' / of_int b'"
    using ab ab' quotient_of_div by blast+
  have pos: "b > 0" "b' > 0"
    using ab ab' by (simp_all add: quotient_of_denom_pos)
  have coprime: "coprime b m" "coprime b' m"
    using ab ab' assms unfolding qcong_def by auto
  from assms have coprime': "coprime c' m"
    using cong_imp_coprime by blast

  have "[x / of_int c = of_int a / of_int (b * c)] (qmod m)"
    using pos coprime assms by (intro qcong_fractionI) (auto simp: x_eq field_simps)
  also have "[of_int a / of_int (b * c) = of_int a' / of_int (b' * c')] (qmod m)"
  proof (subst qcong_fraction_iff)
    have cong: "[a * b' = b * a'] (mod m)"
      using assms(1) pos coprime \<open>m > 0\<close> unfolding x_eq x'_eq
      by (subst (asm) qcong_fraction_iff) auto
    have "[a * (b' * c') = (a * b') * c'] (mod m)"
      by (simp add: algebra_simps)
    also have "[(a * b') * c' = (b * a') * c] (mod m)"
      by (intro cong cong_sym[OF assms(2)] cong_mult)
    also have "(b * a') * c = b * c * a'"
      by (simp add: algebra_simps)
    finally show "[a * (b' * c') = b * c * a'] (mod m)" .
  qed (use pos coprime coprime' assms in auto)
  also have "[of_int a' / of_int (b' * c') = x' / of_int c'] (qmod m)"
    by (rule qcong_sym, rule qcong_fractionI)
       (use pos coprime coprime' assms in \<open>auto simp: x'_eq field_simps\<close>)
  finally show ?thesis .
qed

lemma qcong_mult_of_int_cancel_left:
  assumes "[of_int a * b = of_int a * c] (qmod m)" "coprime a m" "a \<noteq> 0" "m > 0"
  shows   "[b = c] (qmod m)"
proof -
  have "[of_int a * b / of_int a = of_int a * c / of_int a] (qmod m)"
    by (rule qcong_divide_of_int) (use assms in auto)
  thus ?thesis
    using assms(3) by simp
qed

lemma qcong_pow:
  assumes "[a = b] (qmod m)" "m > 0"
  shows   "[a ^ n = b ^ n] (qmod m)"
  by (induction n) (auto intro!: qcong_mult assms)

lemma qcong_sum:
  "[sum f A = sum g A] (qmod m)" if "\<And>x. x \<in> A \<Longrightarrow> [f x = g x] (qmod m)" "m > 0"
  using that by (induct A rule: infinite_finite_induct) (auto intro: qcong_add)

lemma qcong_prod:
  "[prod f A = prod g A] (qmod m)" if "(\<And>x. x \<in> A \<Longrightarrow> [f x = g x] (qmod m))" "m > 0"
  using that by (induct A rule: infinite_finite_induct) (auto intro: qcong_mult)

lemma qcong_modulus_abs_1:
  assumes "\<bar>n\<bar> = 1"
  shows   "[a = b] (qmod n)"
  using assms by (auto simp: qcong_def qmod_def case_prod_unfold abs_if split: if_splits)

lemma qcong_divide_of_int_left_iff:
  assumes "coprime c n" "c \<noteq> 0" \<open>n > 0\<close>
  shows   "[a / of_int c = b] (qmod n) \<longleftrightarrow> [a = b * of_int c] (qmod n)"
proof
  assume *: "[a / of_int c = b] (qmod n)"
  hence "[a / of_int c * of_int c = b * of_int c] (qmod n)"
    by (rule qcong_mult) (use assms in auto)
  also have "a / of_int c * of_int c = a"
    using assms by simp
  finally show "[a = b * of_int c] (qmod n)" .
next
  assume "[a = b * of_int c] (qmod n)"
  hence "[a / of_int c = b * of_int c / of_int c] (qmod n)"
    by (intro qcong_divide_of_int assms cong_refl)
  also have "b * of_int c / of_int c = b"
    using assms by simp
  finally show "[a / of_int c = b] (qmod n)" .
qed

lemma qcong_divide_of_nat_left_iff:
  assumes "coprime (int c) n" "c \<noteq> 0" "n > 0"
  shows   "[a / of_nat c = b] (qmod n) \<longleftrightarrow> [a = b * of_nat c] (qmod n)"
  using qcong_divide_of_int_left_iff[of "int c" n a b] assms by simp

lemma qcong_divide_of_int_right_iff:
  assumes "coprime c n" "c \<noteq> 0" "n > 0"
  shows   "[a = b / of_int c] (qmod n) \<longleftrightarrow> [a * of_int c = b] (qmod n)"
  using qcong_divide_of_int_left_iff[OF assms, of b a] by (simp add: qcong_sym_eq)

lemma qcong_divide_of_nat_right_iff:
  assumes "coprime (int c) n" "c \<noteq> 0" "n > 0"
  shows   "[a = b / of_nat c] (qmod n) \<longleftrightarrow> [a * of_nat c = b] (qmod n)"
  using qcong_divide_of_int_right_iff[of "int c" n a b] assms by simp

lemma qcong_qmultiplicity_pos_transfer:
  assumes "[x = y] (qmod m)" "qmultiplicity m x > 0"
  shows   "y = 0 \<or> qmultiplicity m y > 0"
proof -
  obtain a b where ab: "quotient_of x = (a, b)"
    using prod.exhaust by blast
  obtain c d where cd: "quotient_of y = (c, d)"
    using prod.exhaust by blast
  have "b > 0" "d > 0"
    using ab cd quotient_of_denom_pos by blast+
  have coprime: "coprime a b" "coprime c d"
    using ab cd quotient_of_coprime by blast+
  have *: "coprime b m" "coprime d m" "[a * modular_inverse m b = c * modular_inverse m d] (mod m)"
    using assms(1) unfolding qcong_def ab cd qmod_def by (auto simp: Cong.cong_def)

  have x: "x = of_int a / of_int b" and y: "y = of_int c / of_int d"
    using ab cd by (simp_all add: quotient_of_div)
  from assms have "multiplicity m a > multiplicity m b"
    unfolding qmultiplicity_def ab cd by auto
  hence "m dvd a"
    using not_dvd_imp_multiplicity_0 by force
  hence "[0 = a * modular_inverse m b] (mod m)"
    by (auto simp: Cong.cong_def)
  also have "[a * modular_inverse m b = c * modular_inverse m d] (mod m)"
    by fact
  finally have "m dvd c * modular_inverse m d"
    using cong_dvd_iff by blast
  moreover have "coprime (modular_inverse m d) m"
    using * by auto
  ultimately have "m dvd c"
    using coprime_commute coprime_dvd_mult_left_iff by blast
  hence "c = 0 \<or> multiplicity m c \<ge> 1"
    by (metis \<open>multiplicity m b < multiplicity m a\<close> dual_order.refl less_one linorder_not_le 
          multiplicity_eq_zero_iff multiplicity_unit_left)
  hence "c = 0 \<or> multiplicity m c > multiplicity m d"
    using coprime(2) \<open>m dvd c\<close>
    by (metis Suc_le_eq coprime_common_divisor multiplicity_unit_left
              not_dvd_imp_multiplicity_0 One_nat_def)
  thus ?thesis
    unfolding qmultiplicity_def cd unfolding y by auto
qed

end