(*  Title:       Computational p-Adics: Parametric Equality and Depth
    Author:      Jeremy Sylvestre <jeremy.sylvestre at ualberta.ca>, 2025
    Maintainer:  Jeremy Sylvestre <jeremy.sylvestre at ualberta.ca>
*)


theory Parametric_Equiv_Depth

imports
  "HOL.Rat"
  "HOL-Computational_Algebra.Fraction_Field"
  "HOL-Computational_Algebra.Primes"
  "HOL-Library.Function_Algebras"
  "HOL-Library.Set_Algebras"
  "HOL.Topological_Spaces"
  Polynomial_Extras

begin


section \<open>Common structures for adelic types\<close>


subsection \<open>Preliminaries\<close>

lemma ex_least_nat_le':
  fixes P :: "nat \<Rightarrow> bool"
  assumes "P n"
  shows "\<exists>k\<le>n. (\<forall>i<k. \<not> P i) \<and> P k"
  by (metis assms exists_least_iff not_le_imp_less)

lemma ex_ex1_least_nat_le:
  fixes P :: "nat \<Rightarrow> bool"
  assumes "\<exists>n. P n"
  shows "\<exists>!k. P k \<and> (\<forall>i. P i \<longrightarrow> k \<le> i)"
  by (smt (verit) assms ex_least_nat_le' le_eq_less_or_eq nle_le)

lemma least_le_least:
  "Least Q \<le> Least P"
  if  P : "\<exists>!x. P x \<and> (\<forall>y. P y \<longrightarrow> x \<le> y)"
  and Q : "\<exists>!x. Q x \<and> (\<forall>y. Q y \<longrightarrow> x \<le> y)"
  and PQ: "\<forall>x. P x \<longrightarrow> Q x"
  for P Q :: "'a::order \<Rightarrow> bool"
  using PQ Least1_le[OF Q] Least1I[OF P] by blast

lemma linorder_wlog' [case_names le sym]:
  "\<lbrakk>
    \<And>a b. f a \<le> f b \<Longrightarrow> P a b;
    \<And>a b. P b a \<Longrightarrow> P a b
  \<rbrakk> \<Longrightarrow> P a b"
  for f :: "'a \<Rightarrow> 'b::linorder"
  by (cases rule: le_cases[of "f a" "f b"]) blast+

lemma log_powi_cancel [simp]:
  "a > 0 \<Longrightarrow> a \<noteq> 1 \<Longrightarrow> log a (a powi b) = b"
  by (cases "b \<ge> 0", simp_all add: power_int_def power_inverse log_inverse)


subsection \<open>Existence of primes\<close>

class factorial_comm_ring = factorial_semiring + comm_ring
begin subclass comm_ring_1 .. end

class factorial_idom = factorial_semiring + idom
begin subclass factorial_comm_ring .. end

class nontrivial_factorial_semiring = factorial_semiring +
  assumes nontrivial_elem_exists: "\<exists>x. x \<noteq> 0 \<and> normalize x \<noteq> 1"
begin

lemma primeE:
  obtains p where "prime p"
proof-
  from nontrivial_elem_exists obtain x where x: "x \<noteq> 0" "normalize x \<noteq> 1" by fast
  from x(1) obtain A
    where "\<forall>x. x \<in># A \<longrightarrow> prime x" "normalize (prod_mset A) = normalize x"
    by (auto elim: prime_factorization_exists')
  with x(2) obtain p where "prime p" by fastforce
  with that show thesis by fast
qed

lemma primes_exist: "\<exists>p. prime p"
proof-
  obtain p where "prime p" by (elim primeE)
  thus ?thesis by fast
qed

end (* class nontrivial_factorial_semiring *)

class nontrivial_factorial_comm_ring = nontrivial_factorial_semiring + comm_ring
begin
  subclass factorial_comm_ring ..
end

class nontrivial_factorial_idom = nontrivial_factorial_semiring + idom
begin
  subclass nontrivial_factorial_comm_ring ..
  subclass factorial_idom ..
end

instance int :: nontrivial_factorial_idom
proof
  have "(2::int) \<noteq> 0" "normalize (2::int) \<noteq> 1" by auto
  thus "\<exists>x::int. x \<noteq> 0 \<and> normalize x \<noteq> 1" by fast
qed

typedef (overloaded) 'a prime =
  "{p::'a::nontrivial_factorial_semiring. prime p}"
  using primes_exist by fast

lemma Rep_prime_n0: "Rep_prime p \<noteq> 0"
  using Rep_prime[of p] prime_imp_nonzero by simp

lemma Rep_prime_not_unit: "\<not> is_unit (Rep_prime p)"
  using Rep_prime[of p] by auto

abbreviation pdvd ::
  "'a::nontrivial_factorial_semiring prime \<Rightarrow> 'a \<Rightarrow> bool" (infix "pdvd" 50)
  where "p pdvd a \<equiv> (Rep_prime p) dvd a"
abbreviation "pmultiplicity p \<equiv> multiplicity (Rep_prime p)"

lemma multiplicity_distinct_primes:
  "p \<noteq> q \<Longrightarrow> pmultiplicity p (Rep_prime q) = 0"
  using Rep_prime_inject Rep_prime
        multiplicity_distinct_prime_power[of "Rep_prime p" "Rep_prime q" 1]
  by    auto


subsection \<open>Generic algebraic equality\<close>

context
  fixes R
  assumes sympR  : "symp R"
    and   transpR: "transp R"
begin

lemma transp_left: "R x z \<Longrightarrow> R y z \<Longrightarrow> R x y"
  by (metis sympR sympD transpR transpD)

lemma transp_right: "R x y \<Longrightarrow> R x z \<Longrightarrow> R y z"
  by (metis sympR sympD transpR transpD)

lemma transp_iffs:
  assumes "R x y" shows "R x z \<longleftrightarrow> R y z" and "R z x \<longleftrightarrow> R z y"
  using assms transpD[OF transpR] transp_left transp_right by (blast, blast)

lemma transp_cong: "R w z" if "R x w" and "R y z" and "R x y"
  using that transpD[OF transpR] transp_right by blast

lemma transp_cong_sym: "R x y" if "R x w" and "R y z" and "R w z"
  using that transp_cong sympD[OF sympR] by blast

end (* context symp transp *)

lemma equivp_imp_symp: "equivp R \<Longrightarrow> symp R"
  by (simp add: equivp_reflp_symp_transp)


locale generic_alg_equality =
  fixes   alg_eq :: "'a \<Rightarrow> 'a \<Rightarrow> bool"
  assumes equivp: "equivp alg_eq"
begin

lemmas  refl          = equivp_reflp    [OF equivp]
  and   sym [sym]     = equivp_symp     [OF equivp]
  and   trans [trans] = equivp_transp   [OF equivp]
  and   trans_left    = transp_left     [OF equivp_imp_symp equivp_imp_transp, OF equivp equivp]
  and   trans_right   = transp_right    [OF equivp_imp_symp equivp_imp_transp, OF equivp equivp]
  and   trans_iffs    = transp_iffs     [OF equivp_imp_symp equivp_imp_transp, OF equivp equivp]
  and   cong          = transp_cong     [OF equivp_imp_symp equivp_imp_transp, OF equivp equivp]
  and   cong_sym      = transp_cong_sym [OF equivp_imp_symp equivp_imp_transp, OF equivp equivp]

lemma sym_iff: "alg_eq x y = alg_eq y x"
  using sym by blast

end (* locale generic_alg_equality *)


locale ab_group_alg_equality = generic_alg_equality alg_eq
  for alg_eq :: "'a::ab_group_add \<Rightarrow> 'a \<Rightarrow> bool"
+
  assumes conv_0: "alg_eq x y \<longleftrightarrow> alg_eq (x - y) 0"
begin

lemmas trans0_iff = trans_iffs(1)[of _ _ 0]

lemma add_equiv0_left: "alg_eq (x + y) y" if "alg_eq x 0"
  using that conv_0 by fastforce

lemma add_equiv0_right:  "alg_eq (x + y) x" if "alg_eq y 0"
  using that conv_0 by fastforce

lemma add:
  "alg_eq (x1 + x2) (y1 + y2)" if "alg_eq x1 y1" and "alg_eq x2 y2"
proof (rule iffD2, rule conv_0)
  from that have "alg_eq (x1 - y1) 0" and "alg_eq (x2 - y2) 0"
    using conv_0 by auto
  hence "alg_eq ((x1 - y1) + (x2 - y2)) 0" using add_equiv0_left trans by blast
  moreover have "(x1 - y1) + (x2 - y2) = (x1 + x2) - (y1 + y2)" by simp
  ultimately show "alg_eq ((x1 + x2) - (y1 + y2)) 0" by simp
qed

lemma add_left: "alg_eq (x + y) (x + y')" if "alg_eq y y'"
  using that refl add by simp

lemma add_right: "alg_eq (x + y) (x' + y)" if "alg_eq x x'"
  using that refl add by simp

lemma add_0_left: "alg_eq (x + y) y" if "alg_eq x 0"
  using that add_right[of x 0] by simp

lemma add_0_right: "alg_eq (x + y) x" if "alg_eq y 0"
  using that add_left[of y 0] by simp

lemma sum_zeros:
  "finite A \<Longrightarrow> \<forall>a\<in>A. alg_eq (f a) 0 \<Longrightarrow> alg_eq (sum f A) 0"
  by (induct A rule: finite_induct, simp add: refl, use add in force)

lemma uminus: "alg_eq x y \<Longrightarrow> alg_eq (-x) (-y)"
  using conv_0[of x y] conv_0[of "-y" "-x"] sym[of "-y" "-x"] by force

lemma uminus_iff:
  "alg_eq x y \<longleftrightarrow> alg_eq (-x) (-y)"
  using uminus[of x y] uminus[of "-x" "-y"] by fastforce

lemma add_0: "alg_eq (x + y) 0" if "alg_eq x 0" and "alg_eq y 0"
  using that add[of x 0 y 0] by auto

lemma minus:
  "alg_eq x1 y1 \<Longrightarrow> alg_eq x2 y2 \<Longrightarrow>
    alg_eq (x1 - x2) (y1 - y2)"
  using uminus[of x2 y2] add[of x1 y1 "-x2" "-y2"] by simp

lemma minus_0: "alg_eq (x - y) 0" if "alg_eq x 0" and "alg_eq y 0"
  using that minus[of x 0 y 0] by simp

lemma minus_left: "alg_eq (x - y) (x - y')" if "alg_eq y y'"
  using that refl minus by simp

lemma minus_right: "alg_eq (x - y) (x' - y)" if "alg_eq x x'"
  using that refl minus by simp

lemma minus_0_left: "alg_eq (x - y) (-y)" if "alg_eq x 0"
  using that refl minus_right[of x 0] by simp

lemma minus_0_right: "alg_eq (x - y) x" if "alg_eq y 0"
  using that refl minus_left[of y 0] by simp

end (* locale ab_group_alg_equality *)


locale ring_alg_equality = ab_group_alg_equality alg_eq
  for alg_eq :: "'a::comm_ring \<Rightarrow> 'a \<Rightarrow> bool"
+
  assumes mult_0_right: "alg_eq y 0 \<Longrightarrow> alg_eq (x * y) 0"
begin

lemma mult_0_left: "alg_eq x 0 \<Longrightarrow> alg_eq (x * y) 0"
  using mult_0_right[of x y] by (simp add: mult.commute)

lemma mult:
  "alg_eq x1 y1 \<Longrightarrow> alg_eq x2 y2 \<Longrightarrow> alg_eq (x1 * x2) (y1 * y2)"
  using mult_0_right[of "x2 - y2" x1] mult_0_left[of "x1 - y1" y2] conv_0 trans
  by    (force simp add: algebra_simps)

lemma mult_left: "alg_eq y y' \<Longrightarrow> alg_eq (x * y) (x * y')"
  using refl mult by force

lemma mult_right: "alg_eq x x' \<Longrightarrow> alg_eq (x * y) (x' * y)"
  using refl mult by force

end (* locale ring_alg_equality *)


locale ring_1_alg_equality = ring_alg_equality alg_eq
  for alg_eq :: "'a::comm_ring_1 \<Rightarrow> 'a \<Rightarrow> bool"
begin

lemma mult_one_left: "alg_eq x 1 \<Longrightarrow> alg_eq (x * y) y"
  using mult_right by fastforce

lemma mult_one_right: "alg_eq y 1 \<Longrightarrow> alg_eq (x * y) x"
  using mult_left by fastforce

lemma prod_ones:
  "finite A \<Longrightarrow> \<forall>a\<in>A. alg_eq (f a) 1 \<Longrightarrow>
    alg_eq (prod f A) 1"
  by (induct A rule: finite_induct, simp add: refl, use mult in force)

lemma prod_with_zero:
  "alg_eq (prod f (insert a A)) 0" if "finite A" and "alg_eq (f a) 0"
  using that prod.insert[of "A - {a}" a f] mult_0_left by fastforce

lemma pow: "alg_eq (x ^ n) (y ^ n)" if "alg_eq x y"
  using that refl mult by (induct n, simp_all)

lemma pow_equiv0: "alg_eq (x ^ n) 0" if "n > 0" and "alg_eq x 0"
  by (metis that zero_power pow)

end (* locale ring_1_alg_equality *)


subsection \<open>Indexed equality\<close>

subsubsection \<open>General structure\<close>

locale p_equality =
  fixes p_equal :: "'a \<Rightarrow> 'b::comm_ring \<Rightarrow> 'b \<Rightarrow> bool"
  assumes p_alg_equality: "ring_alg_equality (p_equal p)"
begin

lemmas p_group_alg_equality   = ring_alg_equality.axioms(1)[OF p_alg_equality]
lemmas p_generic_alg_equality = ab_group_alg_equality.axioms(1)[OF p_group_alg_equality]

lemmas  equivp        = generic_alg_equality.equivp      [OF p_generic_alg_equality]
  and   refl[simp]    = generic_alg_equality.refl        [OF p_generic_alg_equality]
  and   sym  [sym]    = generic_alg_equality.sym         [OF p_generic_alg_equality]
  and   trans [trans] = generic_alg_equality.trans       [OF p_generic_alg_equality]
  and   sym_iff       = generic_alg_equality.sym_iff     [OF p_generic_alg_equality]
  and   trans_left    = generic_alg_equality.trans_left  [OF p_generic_alg_equality]
  and   trans_right   = generic_alg_equality.trans_right [OF p_generic_alg_equality]
  and   trans_iffs    = generic_alg_equality.trans_iffs  [OF p_generic_alg_equality]
  and   cong          = generic_alg_equality.cong        [OF p_generic_alg_equality]
  and   cong_sym      = generic_alg_equality.cong_sym    [OF p_generic_alg_equality]

lemmas  conv_0           = ab_group_alg_equality.conv_0           [OF p_group_alg_equality]
  and   trans0_iff       = ab_group_alg_equality.trans0_iff       [OF p_group_alg_equality]
  and   add_equiv0_left  = ab_group_alg_equality.add_equiv0_left  [OF p_group_alg_equality]
  and   add_equiv0_right = ab_group_alg_equality.add_equiv0_right [OF p_group_alg_equality]
  and   add              = ab_group_alg_equality.add              [OF p_group_alg_equality]
  and   add_left         = ab_group_alg_equality.add_left         [OF p_group_alg_equality]
  and   add_right        = ab_group_alg_equality.add_right        [OF p_group_alg_equality]
  and   add_0_left       = ab_group_alg_equality.add_0_left       [OF p_group_alg_equality]
  and   add_0_right      = ab_group_alg_equality.add_0_right      [OF p_group_alg_equality]
  and   sum_zeros        = ab_group_alg_equality.sum_zeros        [OF p_group_alg_equality]
  and   uminus           = ab_group_alg_equality.uminus           [OF p_group_alg_equality]
  and   uminus_iff       = ab_group_alg_equality.uminus_iff       [OF p_group_alg_equality]
  and   add_0            = ab_group_alg_equality.add_0            [OF p_group_alg_equality]
  and   minus            = ab_group_alg_equality.minus            [OF p_group_alg_equality]
  and   minus_0          = ab_group_alg_equality.minus_0          [OF p_group_alg_equality]
  and   minus_left       = ab_group_alg_equality.minus_left       [OF p_group_alg_equality]
  and   minus_right      = ab_group_alg_equality.minus_right      [OF p_group_alg_equality]
  and   minus_0_left     = ab_group_alg_equality.minus_0_left     [OF p_group_alg_equality]
  and   minus_0_right    = ab_group_alg_equality.minus_0_right    [OF p_group_alg_equality]

lemmas  mult_0_left  = ring_alg_equality.mult_0_left  [OF p_alg_equality]
  and   mult_0_right = ring_alg_equality.mult_0_right [OF p_alg_equality]
  and   mult         = ring_alg_equality.mult         [OF p_alg_equality]
  and   mult_left    = ring_alg_equality.mult_left    [OF p_alg_equality]
  and   mult_right   = ring_alg_equality.mult_right   [OF p_alg_equality]

definition globally_p_equal :: "'b \<Rightarrow> 'b \<Rightarrow> bool"
  where globally_p_equal_def[simp]: "globally_p_equal x y = (\<forall>p::'a. p_equal p x y)"

lemma globally_p_equalI[intro]: "globally_p_equal x y" if "\<And>p::'a. p_equal p x y"
  using that unfolding globally_p_equal_def by blast

lemma globally_p_equalD: "globally_p_equal x y \<Longrightarrow> p_equal p x y"
  unfolding globally_p_equal_def by fast

lemma globally_p_nequalE:
  assumes "\<not> globally_p_equal x y"
  obtains p where "\<not> p_equal p x y"
  using     assms
  unfolding globally_p_equal_def
  by        fast

sublocale globally_p_equality: ring_alg_equality globally_p_equal
proof (standard, intro equivpI)
  show "reflp globally_p_equal"
    using refl unfolding globally_p_equal_def by (fastforce intro: reflpI)
  show "symp globally_p_equal"
    using sym unfolding globally_p_equal_def by (fastforce intro: sympI)
  show "transp globally_p_equal"
    using trans unfolding globally_p_equal_def by (fastforce intro: transpI)
  fix x y :: 'b
  show        "globally_p_equal x y = globally_p_equal (x - y) 0"
  and         "globally_p_equal y 0 \<Longrightarrow> globally_p_equal (x * y) 0"
    using     conv_0 mult_0_right
    unfolding globally_p_equal_def
    by        auto
qed

lemmas  globally_p_equal_equivp           = globally_p_equality.equivp
  and   globally_p_equal_refl[simp]       = globally_p_equality.refl
  and   globally_p_equal_sym              = globally_p_equality.sym
  and   globally_p_equal_trans            = globally_p_equality.trans
  and   globally_p_equal_trans_left       = globally_p_equality.trans_left
  and   globally_p_equal_trans_right      = globally_p_equality.trans_right
  and   globally_p_equal_trans_iffs       = globally_p_equality.trans_iffs
  and   globally_p_equal_cong             = globally_p_equality.cong
  and   globally_p_equal_conv_0           = globally_p_equality.conv_0
  and   globally_p_equal_trans0_iff       = globally_p_equality.trans0_iff
  and   globally_p_equal_add_equiv0_left  = globally_p_equality.add_equiv0_left
  and   globally_p_equal_add_equiv0_right = globally_p_equality.add_equiv0_right
  and   globally_p_equal_add              = globally_p_equality.add
  and   globally_p_equal_uminus           = globally_p_equality.uminus
  and   globally_p_equal_uminus_iff       = globally_p_equality.uminus_iff
  and   globally_p_equal_add_0            = globally_p_equality.add_0
  and   globally_p_equal_minus            = globally_p_equality.minus
  and   globally_p_equal_mult_0_left      = globally_p_equality.mult_0_left
  and   globally_p_equal_mult_0_right     = globally_p_equality.mult_0_right
  and   globally_p_equal_mult             = globally_p_equality.mult
  and   globally_p_equal_mult_left        = globally_p_equality.mult_left
  and   globally_p_equal_mult_right       = globally_p_equality.mult_right

lemma globally_p_equal_transfer_equals_rsp:
  "p_equal p x1 y1 \<longleftrightarrow> p_equal p x2 y2"
  if "globally_p_equal x1 x2" and "globally_p_equal y1 y2"
  using that trans_iffs globally_p_equalD by blast

end  (* locale p_equality *)


locale p_equality_1 = p_equality p_equal
  for p_equal :: "'a \<Rightarrow> 'b::comm_ring_1 \<Rightarrow> 'b \<Rightarrow> bool"
begin

lemma p_alg_equality_1: "ring_1_alg_equality (p_equal p)"
  using ring_1_alg_equality.intro p_alg_equality by blast

lemmas  mult_one_left  = ring_1_alg_equality.mult_one_left  [OF p_alg_equality_1]
  and   mult_one_right = ring_1_alg_equality.mult_one_right [OF p_alg_equality_1]
  and   prod_ones      = ring_1_alg_equality.prod_ones      [OF p_alg_equality_1]
  and   pow            = ring_1_alg_equality.pow            [OF p_alg_equality_1]
  and   pow_equiv0     = ring_1_alg_equality.pow_equiv0     [OF p_alg_equality_1]

end (* locale p_equality_1 *)


locale p_equality_no_zero_divisors = p_equality
+
  assumes no_zero_divisors:
    "\<not> p_equal p x 0 \<Longrightarrow> \<not> p_equal p y 0 \<Longrightarrow>
      \<not> p_equal p (x * y) 0"
begin

lemma mult_equiv_0_iff:
  "p_equal p (x * y) 0 \<longleftrightarrow>
    p_equal p x 0 \<or> p_equal p y 0"
  using mult_0_right no_zero_divisors by (fastforce simp add: mult.commute)

end (* locale p_equality_no_zero_divisors *)


locale p_equality_no_zero_divisors_1 = p_equality_no_zero_divisors p_equal
  for p_equal ::
    "'a \<Rightarrow> 'b::comm_ring_1 \<Rightarrow> 'b \<Rightarrow> bool"
+
  assumes nontrivial: "\<exists>x. \<not> p_equal p x 0"
begin

sublocale p_equality_1 ..

lemma one_p_nequal_zero: "\<not> p_equal p (1::'b) (0::'b)"
  using nontrivial mult_equiv_0_iff[of p "1::'b"] by fastforce

lemma zero_p_nequal_one: "\<not> p_equal p (0::'b) (1::'b)"
  using nontrivial one_p_nequal_zero sym by blast

lemma neg_one_p_nequal_zero: "\<not> p_equal p (-1::'b) (0::'b)"
  using one_p_nequal_zero uminus by fastforce

lemma pow_equiv_0_iff: "p_equal p (x ^ n) 0 \<longleftrightarrow> p_equal p x 0 \<and> n \<noteq> 0"
proof (cases n)
  case (Suc k) show ?thesis by (simp only: Suc, induct k, simp_all add: mult_equiv_0_iff)
qed (simp add: one_p_nequal_zero)

lemma pow_equiv_base: "p_equal p (x ^ n) (y ^ n)" if "p_equal p x y"
  using that mult by (induct n) auto

end (* locale p_equality_no_zero_divisors_1 *)


locale p_equality_div_inv = p_equality_no_zero_divisors_1 p_equal
  for p_equal ::
    "'a \<Rightarrow> 'b::{comm_ring_1, inverse, divide_trivial} \<Rightarrow>
      'b \<Rightarrow> bool"
+
  assumes divide_inverse    : "\<And>x y :: 'b. x / y = x * inverse y"
    and   inverse_inverse   : "\<And>x::'b. inverse (inverse x) = x"
    and   inverse_mult      : "\<And>x y :: 'b. inverse (x * y) = inverse x * inverse y"
    and   inverse_equiv0_iff: "p_equal p (inverse x) 0 \<longleftrightarrow> p_equal p x 0"
    and   divide_self_equiv : "\<not> p_equal p x 0 \<Longrightarrow> p_equal p (x / x) 1"
begin

text \<open>Global algebra facts\<close>

lemma inverse_eq_divide: "inverse x = 1 / x" for x :: 'b
  using divide_inverse by auto

lemma inverse_div_inverse: "inverse x / inverse y = y / x" for x y :: 'b
  by (simp add: divide_inverse inverse_inverse)

lemma inverse_0[simp]: "inverse (0::'b) = 0"
  using inverse_eq_divide by simp

lemma inverse_1[simp]: "inverse (1::'b) = 1"
  using inverse_eq_divide by simp

lemma inverse_pow: "inverse (x ^ n) = inverse x ^ n" for x :: 'b
  by (induct n) (simp_all add: inverse_mult)

lemma power_int_minus: "power_int x (-n) = inverse (power_int x n)" for x :: 'b
  by (cases "n \<ge> 0") (simp_all add: power_int_def inverse_pow inverse_inverse)

lemma power_int_minus_divide: "power_int x (-n) = 1 / (power_int x n)" for x :: 'b
  using power_int_minus inverse_eq_divide by presburger

lemma power_int_0_left_if: "power_int (0 :: 'b) m = (if m = 0 then 1 else 0)"
  by (auto simp add: power_int_def zero_power)

lemma power_int_0_left [simp]: "m \<noteq> 0 \<Longrightarrow> power_int (0 :: 'b) m = 0"
  by (simp add: power_int_0_left_if)

lemma power_int_1_left [simp]: "power_int (1::'b) n = 1"
  by (auto simp: power_int_def)

lemma inverse_power_int: "inverse (power_int x n) = power_int x (-n)" for x :: 'b
  using inverse_pow inverse_inverse unfolding power_int_def by (cases n) auto

lemma power_int_inverse:
 "power_int (inverse x) n = inverse (power_int x n)" for x :: 'b
proof (cases "n > 0")
  case True thus ?thesis using inverse_pow power_int_def by metis
next
  case False
  moreover define m where "m \<equiv> - n"
  ultimately have "m \<ge> 0" by fastforce
  hence "power_int (inverse x) (-m) = inverse (power_int x (-m))"
  proof (induct m rule: int_ge_induct)
    case (step m)
    from step(1) have "inverse x powi - (m + 1) = x * inverse x powi (- m)"
      using power_Suc[of x "nat m"]
      by    (fastforce simp add: Suc_nat_eq_nat_zadd1 inverse_inverse power_int_def)
    with step show ?case
      by (
        simp  add : inverse_inverse inverse_mult add.commute power_int_def
              flip: Suc_nat_eq_nat_zadd1
      )
  qed simp
  with m_def show ?thesis by force
qed

lemma power_int_mult_distrib:
  "power_int (x * y) m = power_int x m * power_int y m" for x y :: 'b
  by (cases "m \<ge> 0") (simp_all add: power_int_def power_mult_distrib inverse_mult)

lemma inverse_divide: "inverse (a / b) = b / a" for a b :: 'b
  by (metis divide_inverse inverse_mult inverse_inverse mult.commute)

lemma minus_divide_left: "- (a / b) = (- a) / b" for a b :: 'b
  by (simp add: divide_inverse algebra_simps)

lemma times_divide_times_eq: "(a / b) * (c / d) = (a * c) / (b * d)" for a b :: 'b
  by (simp add: divide_inverse inverse_mult algebra_simps)

lemma divide_pow: "(x ^ n) / (y ^ n) =  (x / y) ^ n" for x y :: 'b
proof (induct n)
  case (Suc n) thus ?case using times_divide_times_eq[of x y "x ^ n" "y ^ n"] by force
qed simp

lemma power_int_divide_distrib:
  "power_int (x / y) m = power_int x m / power_int y m" for x y :: 'b
  by (cases "m \<ge> 0") (simp_all add: power_int_def divide_pow inverse_divide inverse_div_inverse)

lemma power_int_one_over: "power_int (1 / x) n = 1 / power_int x n" for x :: 'b
  by (auto simp add: power_int_inverse simp flip: inverse_eq_divide)

lemma add_divide_distrib: "(a + b) / c = (a / c) + (b / c)" for a b c :: 'b
  by (simp add: divide_inverse algebra_simps)

lemma diff_divide_distrib: "(a - b) / c = (a / c) - (b / c)" for a b c :: 'b
  by (simp add: divide_inverse algebra_simps)

lemma times_divide_eq_right: "a * (b / c) = (a * b) / c" for a b c :: 'b
  using times_divide_times_eq[of a 1] by force

lemma times_divide_eq_left: "(b / c) * a = (b * a) / c" for a b c :: 'b
  using times_divide_eq_right by (simp add: ac_simps)

lemma divide_divide_eq_left: "(a / b) / c = a / (b * c)" for a b c :: 'b
  using divide_inverse mult.assoc inverse_mult[of b c] by metis

lemma swap_numerator: "a * (b / c) = (a / c) * b" for a b c :: 'b
  by (metis times_divide_eq_right mult.commute)

lemma divide_divide_times_eq: "(a / b) / (c / d) = (a * d) / (b * c)" for a b c d :: 'b
  by (metis divide_inverse inverse_divide times_divide_times_eq)

text \<open>Algebra facts by place\<close>

lemma right_inverse_equiv: "p_equal p (x * inverse x) 1" if "\<not> p_equal p x 0"
  using that divide_self_equiv divide_inverse by force

lemma left_inverse_equiv: "p_equal p (inverse x * x) 1" if "\<not> p_equal p x 0"
  using that right_inverse_equiv by (simp add: mult.commute)

lemma inverse_p_unique:
  "p_equal p (inverse x) y" if "p_equal p (x * y) 1"
proof-
  from that have x_n0: "\<not> p_equal p x 0"
    using mult_0_left trans_right zero_p_nequal_one by blast
  with that have "p_equal p (inverse x * x * y) (inverse x * x * inverse x)"
    by (metis right_inverse_equiv trans_left mult_left mult.assoc)
  moreover
    have  "p_equal p (inverse x * x * y) y"
    and   "p_equal p (inverse x * x * inverse x) (inverse x)"
    using x_n0 left_inverse_equiv mult_right
    by    (fastforce, fastforce)
  ultimately show "p_equal p (inverse x) y" using cong sym by blast
qed

lemma inverse_equiv_imp_equiv:
  "p_equal p (inverse a) (inverse b) \<Longrightarrow> p_equal p a b"
proof (cases "p_equal p a 0", metis inverse_equiv0_iff trans_right trans_left)
  case False
  moreover assume ab: "p_equal p (inverse a) (inverse b)"
  ultimately have "\<not> p_equal p b 0" using inverse_equiv0_iff trans_right trans_left by meson
  moreover from False ab have
    "p_equal p b (a * (inverse b * b))"
    by (metis mult_left right_inverse_equiv trans_right mult_right mult_1_left mult.assoc)
  ultimately show "p_equal p a b"
    by (metis left_inverse_equiv mult_left trans sym mult_1_right)
qed

lemma inverse_pcong: "p_equal p (inverse x) (inverse y)" if "p_equal p x y"
proof (
  cases "p_equal p x 0", metis that trans_right inverse_equiv0_iff trans_left,
  intro inverse_p_unique
)
  case False with that show "p_equal p (x * inverse y) 1"
    using mult_right right_inverse_equiv cong refl by blast
qed

lemma inverse_equiv_iff_equiv:
  "p_equal p (inverse a) (inverse b) \<longleftrightarrow> p_equal p a b"
  using inverse_equiv_imp_equiv inverse_pcong by blast

lemma power_int_equiv_0_iff:
  "p_equal p (power_int x n) 0 \<longleftrightarrow> p_equal p x 0 \<and> n \<noteq> 0"
proof (cases "n \<ge> 0")
  case False thus ?thesis
    using inverse_pow[of x "nat (-n)"] inverse_equiv0_iff[of p "x ^ nat (- n)"]
          pow_equiv_0_iff[of p x "nat (- n)"]
    by    (force simp add: power_int_def)
qed (simp add: pow_equiv_0_iff power_int_def)

lemma power_diff_conv_inverse_equiv:
  "m \<le> n \<Longrightarrow> p_equal p (x ^ (n - m)) (x ^ n * inverse x ^ m)"
  if "\<not> p_equal p x 0"
proof (induct n)
  case (Suc n) show ?case
  proof (cases "Suc n = m")
    case True show ?thesis
    proof (cases "m = 0")
      case False
      moreover have "p_equal p 1 (x ^ m * inverse x ^ m)"
        using that pow_equiv_0_iff right_inverse_equiv inverse_pow sym by metis
      ultimately show ?thesis using Suc \<open>Suc n = m\<close> by simp
    qed simp
  next
    case False
    with Suc(2) have mn: "m \<le> n" by linarith
    with Suc(1) have "p_equal p (x ^ Suc (n - m)) (x ^ Suc n * inverse x ^ m)"
      using mult_left by (simp add: mult.assoc)
    moreover from mn have "Suc (n - m) = Suc n - m" by linarith
    ultimately show ?thesis by argo
  qed
qed simp

lemma power_int_add_1_equiv:
  "p_equal p (power_int x (m + 1)) (power_int x m * x)"
  if "\<not> p_equal p x 0 \<or> m \<noteq> -1"
proof (cases "p_equal p x 0")
  case True
  with that have "p_equal p (power_int x (m + 1)) 0" and "p_equal p (power_int x m * x) 0"
    using power_int_equiv_0_iff mult_0_right by auto
  thus ?thesis using trans_left by blast
next
  case False show ?thesis
  proof (cases "m + 1" rule: int_cases3)
    case zero
    hence "m = -1" by auto
    with False show ?thesis using left_inverse_equiv sym power_int_def by auto
  next
    case (pos n)
    hence "nat (m + 1) = Suc (nat m)" by auto
    moreover from pos have "power_int x (m + 1) = x ^ nat (m + 1)" by auto
    ultimately have "power_int x (m + 1) = power_int x m * x" by (simp add: power_int_def)
    thus ?thesis by fastforce
  next
    case (neg n)
    hence "nat (- m) = Suc n" by fastforce
    hence "power_int x m * x = inverse x ^ n * (inverse x * x)" unfolding power_int_def by auto
    with False neg show ?thesis
      using mult_left left_inverse_equiv mult_1_right sym unfolding power_int_def by fastforce
  qed
qed

lemma power_int_add_equiv:
  "\<not> p_equal p x 0 \<or> m + n \<noteq> 0 \<Longrightarrow>
    p_equal p (power_int x (m + n)) (power_int x m * power_int x n)"
proof (induct m n rule: linorder_wlog)
  fix m n :: int assume mn: "m \<le> n" and x: "\<not> p_equal p x 0 \<or> m + n \<noteq> 0"
  show "p_equal p (power_int x (m + n)) (power_int x m * power_int x n)"
  proof (cases "p_equal p x 0")
    case True
    moreover from this x have "p_equal p (power_int x m) 0 \<or> p_equal p (power_int x n) 0"
      using power_int_equiv_0_iff by presburger
    ultimately show ?thesis
      using x mult_0_left mult_0_right power_int_equiv_0_iff trans_left by meson
  next
    case False
    have
      "m \<le> n \<Longrightarrow>
        p_equal p (power_int x (m + n)) (power_int x m * power_int x n)"
    proof (induct n rule: int_ge_induct)
      case base show ?case
      proof (cases "m \<ge> 0")
        case True thus ?thesis
          using nat_add_distrib[of m] power_add[of x] unfolding power_int_def by fastforce
      next
        case False thus ?thesis
          using     nat_add_distrib[of "-m" "-m"] power_add[of "inverse x"]
          unfolding power_int_def
          by        auto
      qed
    next
      case (step n)
      from False have "p_equal p (x powi (m + (n + 1))) (x powi (m + n) * x)"
        using power_int_add_1_equiv[of p x "m + n"] by (simp add: add.assoc)
      with step(2) False have "p_equal p (x powi (m + (n + 1))) (x powi m * (x powi n * x))"
        using mult_right trans by (force simp flip: mult.assoc)
      with False show "p_equal p (x powi (m + (n + 1))) (x powi m * x powi (n + 1))"
        using trans power_int_add_1_equiv sym mult_left by meson
    qed
    with mn show ?thesis by fast
  qed
qed (simp add: ac_simps)

lemma power_int_diff_equiv:
  "p_equal p (power_int x (m - n)) (power_int x m / power_int x n)"
  if "\<not> p_equal p x 0 \<or> m \<noteq> n"
  using that power_int_add_equiv[of p x m "-n"] power_int_minus_divide times_divide_eq_right by auto

lemma power_int_minus_mult_equiv:
  "p_equal p (power_int x (n - 1) * x) (power_int x n)"
  if "\<not> p_equal p x 0 \<or> n \<noteq> 0"
  using that sym power_int_add_1_equiv[of p x "n - 1"] by auto

lemma power_int_not_equiv_zero:
  "\<not> p_equal p x 0 \<or> n = 0 \<Longrightarrow> \<not> p_equal p (power_int x n) 0"
  by (subst power_int_equiv_0_iff) auto

lemma power_int_equiv_base: "p_equal p (power_int x n) (power_int y n)" if "p_equal p x y"
  by (
    cases "n \<ge> 0", metis that power_int_def pow_equiv_base,
    metis that inverse_pcong power_int_def pow_equiv_base
  )

lemma divide_equiv_0_iff:
  "p_equal p (x / y) 0 \<longleftrightarrow> p_equal p x 0 \<or> p_equal p y 0"
  using divide_inverse mult_equiv_0_iff inverse_equiv0_iff by metis

lemma divide_pcong: "p_equal p (w / x) (y / z)" if "p_equal p w y" and "p_equal p x z"
  by (metis that divide_inverse inverse_pcong mult)

lemma divide_left_equiv: "p_equal p x y \<Longrightarrow> p_equal p (x / z) (y / z)"
  by (metis mult_right divide_inverse)

lemma divide_right_equiv: "p_equal p x y \<Longrightarrow> p_equal p (z / x) (z / y)"
  by (metis inverse_pcong mult_left divide_inverse)

lemma add_frac_equiv:
  "p_equal p ((a / b) + (c / d)) ((a * d + c * b) / (b * d))"
  if "\<not> p_equal p b 0" and "\<not> p_equal p d 0"
proof-
  from that have
    "(a * d + c * b) / (b * d) =
      a * d * (inverse b * inverse d) + c * b * (inverse b * inverse d)"
    by (metis add_divide_distrib divide_inverse inverse_mult)
  with that show ?thesis
    using mult_left[of p "d * inverse d" 1 "a / b"] mult_right[of p "b * inverse b" 1 "c / d"]
    by    (simp add: ac_simps divide_inverse right_inverse_equiv add sym)
qed

lemma mult_divide_mult_cancel_right:
  "p_equal p ((a * b) / (c * b)) (a / c)" if "\<not> p_equal p b 0"
proof-
  have "(a * b) / (c * b) = a * b * (inverse c * inverse b)"
    by (metis divide_inverse inverse_mult)
  with that show ?thesis
    using mult_left[of p "b * inverse b" 1 "a / c"]
    by    (simp add: ac_simps divide_inverse right_inverse_equiv sym)
qed

lemma mult_divide_mult_cancel_right2:
  "p_equal p ((a * c) / (c * b)) (a / b)" if "\<not> p_equal p c 0"
  by (metis that mult_divide_mult_cancel_right mult.commute)

lemma mult_divide_mult_cancel_left:
  "p_equal p ((c * a) / (c * b)) (a / b)" if "\<not> p_equal p c 0"
  by (metis that mult_divide_mult_cancel_right mult.commute)

lemma mult_divide_mult_cancel_left2:
  "p_equal p ((c * a) / (b * c)) (a / b)" if "\<not> p_equal p c 0"
  by (metis that mult_divide_mult_cancel_left mult.commute)

lemma mult_divide_cancel_right: "p_equal p ((a * b) / b) a" if "\<not> p_equal p b 0"
  using that mult_divide_mult_cancel_right[of p b a 1] by auto

lemma mult_divide_cancel_left: "p_equal p ((a * b) / a) b" if "\<not> p_equal p a 0"
  using that mult_divide_cancel_right mult.commute by metis

lemma divide_equiv_equiv: "(p_equal p (b / c) a) = (p_equal p b (a * c))" if "\<not> p_equal p c 0"
proof
  assume "p_equal p (b / c) a"
  hence "p_equal p (b * (inverse c * c)) (a * c)" by (metis divide_inverse mult_right mult.assoc)
  with that show "p_equal p b (a * c)"
    by (metis left_inverse_equiv mult_left mult_1_right trans_right)
next
  assume "p_equal p b (a * c)"
  hence "p_equal p (b / c) (a * (c * inverse c))"
    by (metis mult_right mult.assoc divide_inverse)
  with that show "p_equal p (b / c) a"
    using mult_left right_inverse_equiv trans
    by    fastforce
qed

lemma neg_divide_equiv_equiv:
  "p_equal p (- (b / c)) a \<longleftrightarrow> p_equal p (-b) (a * c)" if "\<not> p_equal p c 0"
  using that uminus_iff[of p "- (b / c)" a] divide_equiv_equiv uminus_iff[of p b] by force

lemma equiv_divide_imp:
  "p_equal p (a * c) b \<Longrightarrow> p_equal p a (b / c)" if "\<not> p_equal p c 0"
  using that divide_left_equiv mult_divide_cancel_right trans_right by blast

lemma add_divide_equiv_iff:
  "p_equal p (x + y / z) ((x * z + y) / z)" if "\<not> p_equal p z 0"
  using that add sym mult_divide_cancel_right by (fastforce simp add: add_divide_distrib)

lemma divide_add_equiv_iff: "p_equal p (x / z + y) ((x + y * z) / z)" if "\<not> p_equal p z 0"
  using that add_divide_equiv_iff[of p z y x] by (simp add: ac_simps)

lemma diff_divide_equiv_iff: "p_equal p (x - y / z) ((x * z - y) / z)" if "\<not> p_equal p z 0"
  using that minus sym mult_divide_cancel_right by (fastforce simp add: diff_divide_distrib)

lemma minus_divide_add_equiv_iff:
  "p_equal p (- (x / z) + y) ((- x + y * z) / z)" if "\<not> p_equal p z 0"
  by (metis that minus_divide_left divide_add_equiv_iff)

lemma divide_diff_equiv_iff: "p_equal p (x / z - y) ((x - y * z) / z)" if "\<not> p_equal p z 0"
  by (metis that diff_conv_add_uminus minus_mult_left divide_add_equiv_iff)

lemma minus_divide_diff_equiv_iff:
  "p_equal p (- (x / z) - y) ((- x - y * z) / z)" if "\<not> p_equal p z 0"
  by (metis that divide_diff_equiv_iff minus_divide_left)

lemma divide_mult_cancel_left: "p_equal p (a / (a * b)) (1 / b)" if "\<not> p_equal p a 0"
  by (metis that divide_divide_eq_left divide_left_equiv divide_self_equiv)

lemma divide_mult_cancel_right: "p_equal p (b / (a * b)) (1 / a)" if "\<not> p_equal p b 0"
  by (metis that divide_mult_cancel_left mult.commute)

lemma diff_frac_equiv:
  "p_equal p (x / y - w / z) ((x * z - w * y) / (y * z))"
  if "\<not> p_equal p y 0" and "\<not> p_equal p z 0"
proof-
  from that have "p_equal p (x / y - w / z) ((x * z + - (w * y)) / (y * z))"
    using diff_conv_add_uminus minus_divide_left add_frac_equiv minus_mult_left by metis
  thus ?thesis by force
qed

lemma frac_equiv_equiv:
  "p_equal p (x / y) (w / z) \<longleftrightarrow> p_equal p (x * z) (w * y)"
  if "\<not> p_equal p y 0" and "\<not> p_equal p z 0"
  by (metis that divide_equiv_equiv times_divide_eq_left sym)

lemma inverse_equiv_1_iff:
  "p_equal p (inverse x) 1 \<longleftrightarrow> p_equal p x 1"
  using one_p_nequal_zero trans_right inverse_equiv0_iff mult_left right_inverse_equiv mult_1_right
        mult_right sym mult_1_left
  by    metis

lemma inverse_neg_1_equiv: "p_equal p (inverse (-1)) (-1)"
  using inverse_p_unique by auto

lemma globally_inverse_neg_1: "globally_p_equal (inverse (-1)) (-1)"
  using inverse_neg_1_equiv by blast

lemma inverse_uminus_equiv: "p_equal p (inverse (-x)) (- inverse x)"
  using inverse_mult[of "-1" x] inverse_neg_1_equiv mult_right by fastforce

lemma minus_divide_right_equiv: "p_equal p (a / (- b)) (- (a / b))"
  using divide_inverse inverse_uminus_equiv mult_left trans by fastforce

lemma minus_divide_divide_equiv: "p_equal p ((- a) / (- b)) (a / b)"
  using refl minus_divide_left minus_divide_right_equiv trans by fastforce

lemma divide_minus1_equiv: "p_equal p (x / (-1)) (- x)"
  using minus_divide_right_equiv[of p x 1] by simp

lemma divide_cancel_right:
  "p_equal p (a / c) (b / c) \<longleftrightarrow> p_equal p c 0 \<or> p_equal p a b"
proof
  assume "p_equal p (a / c) (b / c)"
  hence "p_equal p ((c * a) / c) ((c * b) / c)"
    using mult_left times_divide_eq_right by metis
  thus "p_equal p c 0 \<or> p_equal p a b" using mult_divide_cancel_left cong by blast
qed (metis divide_left_equiv divide_equiv_0_iff trans_left)

lemma divide_cancel_left:
  "p_equal p (c / a) (c / b) \<longleftrightarrow> p_equal p c 0 \<or> p_equal p a b"
proof
  assume *: "p_equal p (c / a) (c / b)"
  show "p_equal p c 0 \<or> p_equal p a b"
  proof (cases "p_equal p a 0" "p_equal p c 0" rule: case_split[case_product case_split])
    case False_False
    from * False_False(1) have "p_equal p ((c * a) / c) ((c * b) / c)"
      using divide_equiv_0_iff trans divide_equiv_equiv times_divide_eq_left sym divide_left_equiv
      by    metis
    with False_False(2) show ?thesis using mult_divide_cancel_left cong by blast
  qed (simp, metis * divide_equiv_0_iff trans0_iff trans_left, simp)
qed (metis divide_right_equiv divide_equiv_0_iff trans_left)

lemma divide_equiv_1_iff:
  "p_equal p (a / b) 1 \<longleftrightarrow> \<not> p_equal p b 0 \<and> p_equal p a b"
proof (standard, standard)
  assume "p_equal p (a / b) 1"
  moreover from this show "\<not> p_equal p b 0"
    using divide_equiv_0_iff zero_p_nequal_one trans_right by metis
  ultimately show "p_equal p a b"
    using mult_left mult_1_right times_divide_eq_right mult_divide_cancel_left trans_right
    by    metis
qed (metis divide_left_equiv divide_self_equiv trans)

lemma divide_equiv_minus_1_iff:
  "p_equal p (a / b) (- 1) \<longleftrightarrow> \<not> p_equal p b 0 \<and> p_equal p a (- b)"
proof-
  have "p_equal p (a / b) (- 1) \<longleftrightarrow> p_equal p (- (a / b)) 1"
    using uminus_iff by fastforce
  also have "\<dots> \<longleftrightarrow> \<not> p_equal p (- b) 0 \<and> p_equal p a (- b)"
    using minus_divide_right_equiv sym trans_right divide_equiv_1_iff by blast
  finally show ?thesis using uminus_iff by fastforce
qed

end (* locale p_equality_div_inv *)


subsection \<open>Indexed depth functions\<close>

subsubsection \<open>General structure\<close>

locale p_equality_depth = p_equality +
  fixes p_depth :: "'a \<Rightarrow> 'b::comm_ring \<Rightarrow> int"
  assumes depth_of_0[simp]: "p_depth p 0 = 0"
  and     depth_equiv: "p_equal p x y \<Longrightarrow> p_depth p x = p_depth p y"
  and     depth_uminus: "p_depth p (-x) = p_depth p x"
  and     depth_pre_nonarch:
    "\<not> p_equal p x 0 \<Longrightarrow> p_depth p x < p_depth p y \<Longrightarrow>
      p_depth p (x + y) = p_depth p x"
    "\<lbrakk> \<not> p_equal p x 0; \<not> p_equal p (x + y) 0; p_depth p x = p_depth p y \<rbrakk>
      \<Longrightarrow> p_depth p (x + y) \<ge> p_depth p x"
begin

lemma depth_equiv_0: "p_equal p x 0 \<Longrightarrow> p_depth p x = 0"
  using depth_of_0 depth_equiv by presburger

lemma depth_equiv_uminus: "p_equal p y (-x) \<Longrightarrow> p_depth p y = p_depth p x"
  using depth_equiv depth_uminus by force

lemma depth_add_equiv0_left: "p_equal p x 0 \<Longrightarrow> p_depth p (x + y) = p_depth p y"
  using add_equiv0_left depth_equiv by blast

lemma depth_add_equiv0_right: "p_equal p y 0 \<Longrightarrow> p_depth p (x + y) = p_depth p x"
  using add_equiv0_right depth_equiv by blast

lemma depth_add_equiv:
  "p_depth p (x + y) = p_depth p (w + z)" if "p_equal p x w" and "p_equal p y z"
  using that add depth_equiv by auto

lemma depth_diff: "p_depth p (x - y) = p_depth p (y - x)"
  using depth_uminus[of p "y - x"] by auto

lemma depth_diff_equiv0_left: "p_equal p x 0 \<Longrightarrow> p_depth p (x - y) = p_depth p y"
  using depth_add_equiv0_right[of p x "-y"] depth_uminus by fastforce

lemma depth_diff_equiv0_right: "p_equal p y 0 \<Longrightarrow> p_depth p (x - y) = p_depth p x"
  using depth_diff_equiv0_left[of p y x] depth_uminus[of p "x - y"] by simp

lemma depth_diff_equiv:
  "p_depth p (x - y) = p_depth p (w - z)" if "p_equal p x w" and "p_equal p y z"
  using that minus depth_equiv by auto

lemma depth_pre_nonarch_diff_left:
  "p_depth p (x - y) = p_depth p x" if "\<not> p_equal p x 0" and "p_depth p x < p_depth p y"
  using that depth_pre_nonarch(1)[of p x "-y"] depth_uminus by simp

lemma depth_pre_nonarch_diff_right:
  "p_depth p (x - y) = p_depth p y" if "\<not> p_equal p y 0" and "p_depth p y < p_depth p x"
  using that depth_pre_nonarch_diff_left[of p y x] depth_uminus[of p "x - y"] by simp

lemma depth_nonarch:
  "\<lbrakk> \<not> p_equal p x 0; \<not> p_equal p y 0; \<not> p_equal p (x + y) 0 \<rbrakk>
    \<Longrightarrow> p_depth p (x + y) \<ge> min (p_depth p x) (p_depth p y)"
  using depth_pre_nonarch[of p x y] depth_pre_nonarch[of p y x]
  by    (cases "p_depth p x" "p_depth p y" rule: linorder_cases, auto simp add: add.commute)

lemma depth_nonarch_diff:
  "\<lbrakk> \<not> p_equal p x 0; \<not> p_equal p y 0; \<not> p_equal p (x - y) 0 \<rbrakk>
    \<Longrightarrow> p_depth p (x - y) \<ge> min (p_depth p x) (p_depth p y)"
  using depth_nonarch[of p x "-y"] depth_uminus uminus_iff by fastforce

lemma depth_sum_nonarch:
  "finite A \<Longrightarrow> \<not> p_equal p (sum f A) 0 \<Longrightarrow>
    p_depth p (sum f A) \<ge> Min {p_depth p (f a) | a. a \<in> A \<and> \<not> p_equal p (f a) 0 }"
proof (induct A rule: finite_induct)
  case (insert a A)
  define D
    where "D \<equiv> \<lambda>A. {p_depth p (f a) |a. a \<in> A \<and> \<not> p_equal p (f a) 0}"
  consider  (fa0)     "p_equal p (f a) 0" |
            (sum0)    "p_equal p (sum f A) 0" |
            (neither) "\<not> p_equal p (f a) 0" "\<not> p_equal p (sum f A) 0"
    by blast
  thus "p_depth p (sum f (insert a A)) \<ge> Min (D (insert a A))"
  proof cases
    case fa0
    with insert D_def have "p_depth p (sum f A) \<ge> Min (D A)" using add by fastforce
    moreover from fa0 insert(1,2) have "p_depth p (sum f (insert a A)) = p_depth p (sum f A)"
      using depth_add_equiv0_left by auto
    moreover from fa0 D_def have "D (insert a A) = D A" by blast
    ultimately show ?thesis by argo
  next
    case sum0
    with D_def insert(1,2,4) have "p_depth p (f a) \<in> D (insert a A)" using add by force
    moreover from insert(1,2) sum0 have "p_depth p (sum f (insert a A)) = p_depth p (f a)"
      using depth_add_equiv0_right by fastforce
    ultimately show ?thesis using D_def insert(1) by force
  next
    case neither
    from D_def neither(1) have "D (insert a A) = insert (p_depth p (f a)) (D A)" by blast
    hence "Min (D (insert a A)) = Min (insert (p_depth p (f a)) (D A))" by simp
    also have "\<dots> = min (p_depth p (f a)) (Min (D A))"
    proof (rule Min_insert)
      from D_def insert(1) show "finite (D A)" by simp
      from D_def insert(1) neither(2) show "D A \<noteq> {}" using sum_zeros by fast
    qed
    finally show ?thesis using neither D_def insert depth_nonarch by fastforce
  qed
qed simp

lemma obtains_depth_sum_nonarch_witness:
  assumes "finite A" and "\<not> p_equal p (sum f A) 0"
  obtains a
    where "a \<in> A" and "\<not> p_equal p (f a) 0" and "p_depth p (sum f A) \<ge> p_depth p (f a)"
proof-
  define D where "D \<equiv> {p_depth p (f a) |a. a \<in> A \<and> \<not> p_equal p (f a) 0}"
  from assms D_def obtain a
    where a: "a \<in> A" "\<not> p_equal p (f a) 0" "Min D = p_depth p (f a)"
    using sum_zeros[of A p f] obtains_Min[of D] by auto
  from assms D_def a(3) have "p_depth p (sum f A) \<ge> p_depth p (f a)"
    using depth_sum_nonarch by fastforce
  with that a(1,2) show thesis by blast
qed

lemma depth_add_cancel_imp_eq_depth:
  "p_depth p x = p_depth p y" if "\<not> p_equal p x 0" and "p_depth p (x + y) > p_depth p x"
  using that depth_pre_nonarch(1)[of p x y] depth_pre_nonarch(1)[of p y x] depth_add_equiv0_right
  by    (fastforce simp add: ac_simps)

lemma depth_diff_cancel_imp_eq_depth_left:
  "p_depth p x = p_depth p y" if  "\<not> p_equal p x 0" and "p_depth p (x - y) > p_depth p x"
  using that depth_add_cancel_imp_eq_depth[of p x "-y"] depth_uminus by auto

lemma depth_diff_cancel_imp_eq_depth_right:
  "p_depth p x = p_depth p y" if  "\<not> p_equal p y 0" and "p_depth p (x - y) > p_depth p y"
  by (metis that depth_diff_cancel_imp_eq_depth_left depth_diff)

lemma level_closed_add:
  "p_depth p (x + y) \<ge> n"
  if "\<not> p_equal p (x + y) 0" and "p_depth p x \<ge> n" and "p_depth p y \<ge> n"
proof-
  consider
    "p_equal p x 0" | "p_equal p y 0" |
    (both_n0) "\<not> p_equal p x 0" "\<not> p_equal p y 0"
    by blast
  thus ?thesis
  proof cases
    case both_n0 with that show ?thesis using depth_nonarch by fastforce
  qed (simp add: that(3) depth_add_equiv0_left, simp add: that(2) depth_add_equiv0_right)
qed

lemma level_closed_diff:
  "p_depth p (x - y) \<ge> n"
  if "\<not> p_equal p (x - y) 0" and "p_depth p x \<ge> n" and "p_depth p y \<ge> n"
  using that level_closed_add[of p x "-y"] depth_uminus by auto

definition p_depth_set :: "'a \<Rightarrow> int \<Rightarrow> 'b set"
  where "p_depth_set p n = {x. \<not> p_equal p x 0 \<longrightarrow> p_depth p x \<ge> n}"

definition global_depth_set :: "int \<Rightarrow> 'b set"
  where
    "global_depth_set n =
      {x. \<forall>p. \<not> p_equal p x 0 \<longrightarrow> p_depth p x \<ge> n}"

lemma global_depth_set: "global_depth_set n = (\<Inter>p. p_depth_set p n)"
  unfolding p_depth_set_def global_depth_set_def by auto

lemma p_depth_setD:
  "\<not> p_equal p x 0 \<Longrightarrow> x \<in> p_depth_set p n \<Longrightarrow>
    p_depth p x \<ge> n"
  unfolding p_depth_set_def by blast

lemma nonpos_p_depth_setD:
  "n \<le> 0 \<Longrightarrow> x \<in> p_depth_set p n \<Longrightarrow> p_depth p x \<ge> n"
  by (cases "p_equal p x 0", simp_all add: depth_equiv_0 p_depth_setD)

lemma global_depth_setD:
  "\<not> p_equal p x 0 \<Longrightarrow> x \<in> global_depth_set n \<Longrightarrow>
    p_depth p x \<ge> n"
  unfolding global_depth_set_def by blast

lemma nonpos_global_depth_setD:
  "n \<le> 0 \<Longrightarrow> x \<in> global_depth_set n \<Longrightarrow> p_depth p x \<ge> n"
  by (cases "p_equal p x 0", simp_all add: depth_equiv_0 global_depth_setD)

lemma p_depth_set_0: "0 \<in> p_depth_set p n"
  unfolding p_depth_set_def by fastforce

lemma global_depth_set_0: "0 \<in> global_depth_set n"
  unfolding global_depth_set_def by fastforce

lemma p_depth_set_equiv0: "p_equal p x 0 \<Longrightarrow> x \<in> p_depth_set p n"
  unfolding p_depth_set_def by blast

lemma p_depth_setI:
  "x \<in> p_depth_set p n" if "\<not> p_equal p x 0 \<longrightarrow> p_depth p x \<ge> n"
  using that unfolding p_depth_set_def by blast

lemma p_depth_set_by_equivI:
  "x \<in> p_depth_set p n" if "p_equal p x y" and "y \<in> p_depth_set p n"
  by (metis that trans p_depth_setD depth_equiv p_depth_setI)

lemma global_depth_setI:
  "x \<in> global_depth_set n"
  if "\<And>p. \<not> p_equal p x 0 \<Longrightarrow> p_depth p x \<ge> n"
  using that unfolding global_depth_set_def by blast

lemma global_depth_setI': "x \<in> global_depth_set n" if "\<And>p. p_depth p x \<ge> n"
  by (intro global_depth_setI, rule that)

lemma global_depth_setI'': "x \<in> global_depth_set n" if "\<And>p. x \<in> p_depth_set p n"
  using that global_depth_set by blast

lemma p_depth_set_antimono:
  "n \<le> m \<Longrightarrow> p_depth_set p n \<supseteq> p_depth_set p m"
  unfolding p_depth_set_def by force

lemma global_depth_set_antimono:
  "n \<le> m \<Longrightarrow> global_depth_set n \<supseteq> global_depth_set m"
  unfolding global_depth_set_def by force

lemma p_depth_set_add:
  "x + y \<in> p_depth_set p n" if "x \<in> p_depth_set p n" and "y \<in> p_depth_set p n"
proof (intro p_depth_setI, clarify)
  assume nequiv0: "\<not> p_equal p (x + y) 0"
  consider "p_equal p x 0" | "p_equal p y 0" | "\<not> p_equal p x 0" "\<not> p_equal p y 0"
    by blast
  thus "p_depth p (x + y) \<ge> n"
    by (
      cases, metis that(2) nequiv0 add_0_left depth_equiv trans p_depth_setD,
      metis that(1) nequiv0 add_0_right depth_equiv trans p_depth_setD,
      metis that nequiv0 level_closed_add p_depth_setD
    )
qed

lemma global_depth_set_add:
  "x + y \<in> global_depth_set n" if "x \<in> global_depth_set n" and "y \<in> global_depth_set n"
  using that p_depth_set_add global_depth_set by simp

lemma p_depth_set_uminus: "-x \<in> p_depth_set p n" if "x \<in> p_depth_set p n"
  using that uminus depth_uminus unfolding p_depth_set_def by fastforce

lemma global_depth_set_uminus: "-x \<in> global_depth_set n" if "x \<in> global_depth_set n"
  using that p_depth_set_uminus global_depth_set by simp

lemma p_depth_set_minus:
  "x - y \<in> p_depth_set p n" if "x \<in> p_depth_set p n" and "y \<in> p_depth_set p n"
  using that p_depth_set_add p_depth_set_uminus by fastforce

lemma global_depth_set_minus:
  "x - y \<in> global_depth_set n" if "x \<in> global_depth_set n" and "y \<in> global_depth_set n"
  using that p_depth_set_minus global_depth_set by simp

lemma p_depth_set_elt_set_plus:
  "x +o p_depth_set p n = p_depth_set p n" if "x \<in> p_depth_set p n"
  unfolding elt_set_plus_def
proof (standard, safe)
  fix y assume y: "y \<in> p_depth_set p n"
  define z where "z \<equiv> y - x"
  with that y have "z \<in> p_depth_set p n" using p_depth_set_minus by simp
  with z_def show "\<exists>z\<in>p_depth_set p n. y = x + z" by force
qed (simp add: that p_depth_set_add)

lemma global_depth_set_elt_set_plus:
  "x +o global_depth_set n = global_depth_set n" if "x \<in> global_depth_set n"
  unfolding elt_set_plus_def
proof (standard, safe)
  fix y assume y: "y \<in> global_depth_set n"
  define z where "z \<equiv> y - x"
  with that y have "z \<in> global_depth_set n" using global_depth_set_minus by simp
  with z_def show "\<exists>z\<in>global_depth_set n. y = x + z" by force
qed (simp add: that global_depth_set_add)

lemma p_depth_set_elt_set_plus_closed:
  "x +o p_depth_set p m \<subseteq> p_depth_set p n" if "m \<ge> n" and "x \<in> p_depth_set p n"
  using that set_plus_mono p_depth_set_antimono p_depth_set_elt_set_plus by metis

lemma global_depth_set_elt_set_plus_closed:
  "x +o global_depth_set m \<subseteq> global_depth_set n"
  if "m \<ge> n" and "x \<in> global_depth_set n"
  using that set_plus_mono global_depth_set_antimono global_depth_set_elt_set_plus by metis

lemma p_depth_set_plus_coeffs:
  "set xs \<subseteq> p_depth_set p n \<Longrightarrow>
    set ys \<subseteq> p_depth_set p n \<Longrightarrow>
    set (plus_coeffs xs ys) \<subseteq> p_depth_set p n"
proof (induct xs ys rule: list_induct2')
  case (4 x xs y ys) thus ?case
    using cCons_def[of "x + y" "plus_coeffs xs ys"] p_depth_set_add by auto
qed simp_all

lemma global_depth_set_plus_coeffs:
  "set (plus_coeffs xs ys) \<subseteq> global_depth_set n"
  if "set xs \<subseteq> global_depth_set n" and "set ys \<subseteq> global_depth_set n"
  using that p_depth_set_plus_coeffs[of xs _ n ys] global_depth_set[of n] by fastforce

lemma p_depth_set_poly_pCons:
  "set (coeffs (pCons a f)) \<subseteq> p_depth_set p n"
  if "a \<in> p_depth_set p n" and "set (coeffs f) \<subseteq> p_depth_set p n"
  by (cases "a = 0 \<and> f = 0") (simp add: p_depth_set_0, use that in auto)

lemma p_depth_set_poly_add:
  "set (coeffs (f + g)) \<subseteq> p_depth_set p n"
  if "set (coeffs f) \<subseteq> p_depth_set p n" and "set (coeffs g) \<subseteq> p_depth_set p n"
  using that coeffs_plus_eq_plus_coeffs p_depth_set_plus_coeffs by metis

lemma global_depth_set_poly_add:
  "set (coeffs (f + g)) \<subseteq> global_depth_set n"
  if  "set (coeffs f) \<subseteq> global_depth_set n"
  and "set (coeffs g) \<subseteq> global_depth_set n"
  using that p_depth_set_poly_add[of f _ n g] global_depth_set by fastforce

end  (* locale p_equality_depth *)


locale p_equality_depth_no_zero_divisors =
  p_equality_no_zero_divisors + p_equality_depth
+ assumes depth_mult_additive:
    "\<not> p_equal p (x * y) 0 \<Longrightarrow> p_depth p (x * y) = p_depth p x + p_depth p y"
begin

lemma depth_mult3_additive:
  "p_depth p (x * y * z) = p_depth p x + p_depth p y + p_depth p z"
  if "\<not> p_equal p (x * y * z) 0"
  using that mult_0_left depth_mult_additive by fastforce

lemma p_depth_set_times:
  "x * y \<in> p_depth_set p n"
  if "n \<ge> 0" and "x \<in> p_depth_set p n" and "y \<in> p_depth_set p n"
proof (intro p_depth_setI, clarify)
  assume "\<not> p_equal p (x * y) 0"
  moreover from this have "\<not> p_equal p x 0" and "\<not> p_equal p y 0"
    by (metis mult_0_left, metis mult_0_right)
  ultimately show "p_depth p (x * y) \<ge> n"
    using that p_depth_setD[of p x] p_depth_setD[of p y] depth_mult_additive by fastforce
qed

lemma global_depth_set_times:
  "x * y \<in> global_depth_set n"
  if "n \<ge> 0" and "x \<in> global_depth_set n" and "y \<in> global_depth_set n"
  using that p_depth_set_times global_depth_set by simp

lemma poly_p_depth_set_poly:
  "set (coeffs f) \<subseteq> p_depth_set p n \<Longrightarrow> poly f x \<in> p_depth_set p n"
  if "n \<ge> 0" and "x \<in> p_depth_set p n"
  by (induct f, simp add: p_depth_set_0, use that p_depth_set_times p_depth_set_add in force)

lemma poly_global_depth_set_poly:
  "poly f x \<in> global_depth_set n"
  if    "n \<ge> 0"
  and   "x \<in> global_depth_set n"
  and   "set (coeffs f) \<subseteq> global_depth_set n"
  using that poly_p_depth_set_poly global_depth_set
  by    fastforce

lemma p_depth_set_ideal:
  "x * y \<in> p_depth_set p n"
  if "x \<in> p_depth_set p 0" and "y \<in> p_depth_set p n"
proof (intro p_depth_setI, clarify)
  assume "\<not> p_equal p (x * y) 0"
  moreover from this have "\<not> p_equal p x 0" and "\<not> p_equal p y 0"
    by (metis mult_0_left, metis mult_0_right)
  ultimately show "p_depth p (x * y) \<ge> n"
    using that p_depth_setD[of p x] p_depth_setD[of p y] depth_mult_additive by fastforce
qed

lemma global_depth_set_ideal:
  "x * y \<in> global_depth_set n"
  if "x \<in> global_depth_set 0" and "y \<in> global_depth_set n"
  using that p_depth_set_ideal global_depth_set by simp

lemma poly_p_depth_set_poly_ideal:
  "set (coeffs f) \<subseteq> p_depth_set p n \<Longrightarrow> poly f x \<in> p_depth_set p n"
  if "x \<in> p_depth_set p 0"
  using that p_depth_set_0 p_depth_set_ideal p_depth_set_add by (induct f) auto

lemma poly_global_depth_set_poly_ideal:
  "poly f x \<in> global_depth_set n"
  if "x \<in> global_depth_set 0" and "set (coeffs f) \<subseteq> global_depth_set n"
  using that poly_p_depth_set_poly_ideal global_depth_set by fastforce

lemma p_depth_set_poly_smult:
  "set (coeffs (smult x f)) \<subseteq> p_depth_set p n"
  if "n \<ge> 0" and "x \<in> p_depth_set p n" and "set (coeffs f) \<subseteq> p_depth_set p n"
proof-
  have "set (coeffs (smult x f)) = (*) x ` set (strip_while (\<lambda>c. x * c = 0) (coeffs f))"
    using coeffs_smult_eq_smult_coeffs set_map by metis
  also have "\<dots> \<subseteq> set (map ((*) x) (coeffs f))"
    using set_strip_while image_mono set_map by fastforce
  finally show ?thesis using that p_depth_set_times by fastforce
qed

lemma global_depth_set_poly_smult:
  "set (coeffs (smult x f)) \<subseteq> global_depth_set n"
  if    "n \<ge> 0"
  and   "x \<in> global_depth_set n"
  and   "set (coeffs f) \<subseteq> global_depth_set n"
  using that p_depth_set_poly_smult global_depth_set
  by    fastforce

lemma p_depth_set_poly_smult_ideal:
  "set (coeffs (smult x f)) \<subseteq> p_depth_set p n"
  if "x \<in> p_depth_set p 0" and "set (coeffs f) \<subseteq> p_depth_set p n"
proof-
  have "set (coeffs (smult x f)) = (*) x ` set (strip_while (\<lambda>c. x * c = 0) (coeffs f))"
    using coeffs_smult_eq_smult_coeffs set_map by metis
  also have "\<dots> \<subseteq> set (map ((*) x) (coeffs f))"
    using set_strip_while image_mono set_map by fastforce
  finally show ?thesis using that p_depth_set_ideal by fastforce
qed

lemma global_depth_set_poly_smult_ideal:
  "set (coeffs (smult x f)) \<subseteq> global_depth_set n"
  if "x \<in> global_depth_set 0" and "set (coeffs f) \<subseteq> global_depth_set n"
  using that p_depth_set_poly_smult_ideal global_depth_set by fastforce

lemma p_depth_set_poly_times:
  "set (coeffs f) \<subseteq> p_depth_set p n \<Longrightarrow>
    set (coeffs g) \<subseteq> p_depth_set p n \<Longrightarrow>
    set (coeffs (f * g)) \<subseteq> p_depth_set p n"
  if  "n \<ge> 0"
proof (induct f)
  case (pCons a f)
  hence "set (coeffs (f * g)) \<subseteq> p_depth_set p n" by auto
  moreover from pCons(1,3) have "a \<in> p_depth_set p n" by fastforce
  ultimately show ?case
    using that pCons(4) mult_pCons_left p_depth_set_poly_add p_depth_set_poly_smult
          p_depth_set_poly_pCons p_depth_set_0
    by    auto
qed simp

lemma global_depth_set_poly_times:
  "set (coeffs (f * g)) \<subseteq> global_depth_set n"
  if  "n \<ge> 0"
  and "set (coeffs g) \<subseteq> global_depth_set n"
  and "set (coeffs f) \<subseteq> global_depth_set n"
  using that p_depth_set_poly_times[of n f _ g] global_depth_set by fastforce

lemma p_depth_set_poly_times_ideal:
  "set (coeffs f) \<subseteq> p_depth_set p 0 \<Longrightarrow>
    set (coeffs g) \<subseteq> p_depth_set p n \<Longrightarrow>
    set (coeffs (f * g)) \<subseteq> p_depth_set p n"
proof (induct f)
  case (pCons a f)
  hence "set (coeffs (f * g)) \<subseteq> p_depth_set p n" by auto
  moreover from pCons(1,3) have "a \<in> p_depth_set p 0" by fastforce
  ultimately show ?case
    using pCons(4) mult_pCons_left p_depth_set_poly_add p_depth_set_poly_smult_ideal
          p_depth_set_poly_pCons p_depth_set_0
    by    simp
qed simp

lemma global_depth_set_poly_times_ideal:
  "set (coeffs (f * g)) \<subseteq> global_depth_set n"
  if  "set (coeffs f) \<subseteq> global_depth_set 0"
  and "set (coeffs g) \<subseteq> global_depth_set n"
  using that p_depth_set_poly_times_ideal[of f _ g] global_depth_set by fastforce

end


locale p_equality_depth_no_zero_divisors_1 =
  p_equality_no_zero_divisors_1 + p_equality_depth_no_zero_divisors
begin

lemma depth_of_1[simp]: "p_depth p 1 = 0"
  using one_p_nequal_zero depth_mult_additive[of p 1] by auto

lemma depth_of_neg1: "p_depth p (-1) = 0"
  using depth_uminus by auto

lemma depth_pow_additive: "p_depth p (x ^ n) = int n * p_depth p x"
proof (cases "p_equal p x 0")
  case True thus ?thesis using pow_equiv_0_iff depth_equiv_0 by (cases "n = 0") auto
next
  case False show ?thesis
  proof (induct n)
    case (Suc n)
    from False have "p_depth p (x ^ Suc n) = p_depth p x + p_depth p (x ^ n)"
      using pow_equiv_0_iff depth_mult_additive by force
    also from Suc have "\<dots> = (int n + 1) * p_depth p x" by algebra
    finally show ?case by auto
  qed simp
qed

lemma depth_prod_summative:
  "finite X \<Longrightarrow> \<not> p_equal p (\<Prod>X) 0 \<Longrightarrow>
    p_depth p (\<Prod>X) = sum (p_depth p) X"
  by (induct X rule: finite_induct, simp, use depth_mult_additive mult_0_right in force)

lemma p_depth_set_1: "1 \<in> p_depth_set p 0"
  using p_depth_setI by simp

lemma pos_p_depth_set_1: "n > 0 \<Longrightarrow> 1 \<notin> p_depth_set p n"
  using one_p_nequal_zero p_depth_setD by fastforce

lemma global_depth_set_1: "1 \<in> global_depth_set 0"
  using p_depth_set_1 global_depth_set by blast

lemma pos_global_depth_set_1: "n > 0 \<Longrightarrow> 1 \<notin> global_depth_set n"
  using pos_p_depth_set_1 global_depth_set by blast

lemma p_depth_set_neg1: "-1 \<in> p_depth_set p 0"
  using depth_of_neg1 p_depth_setI by simp

lemma global_depth_set_neg1: "-1 \<in> global_depth_set 0"
  using p_depth_set_neg1 global_depth_set by blast

lemma p_depth_set_pow:
  "x ^ Suc k \<in> p_depth_set p n" if "n \<ge> 0" and "x \<in> p_depth_set p n"
  by (induct k, simp_all add: that p_depth_set_times)

lemma global_depth_set_pow:
  "x ^ Suc k \<in> global_depth_set n" if "n \<ge> 0" and "x \<in> global_depth_set n"
  using that p_depth_set_pow global_depth_set by simp

lemma p_depth_set_0_pow: "x ^ k \<in> p_depth_set p 0" if "x \<in> p_depth_set p 0"
  by (induct k, simp_all add: that p_depth_set_1 p_depth_set_times)

lemma global_depth_set_0_pow: "x ^ k \<in> global_depth_set 0" if "x \<in> global_depth_set 0"
  using that p_depth_set_0_pow global_depth_set by simp

lemma p_depth_set_of_nat: "of_nat n \<in> p_depth_set p 0"
  using p_depth_set_0 p_depth_set_1 p_depth_set_add by (induct n) simp_all

lemma global_depth_set_of_nat: "of_nat n \<in> global_depth_set 0"
  using p_depth_set_of_nat global_depth_set by blast

lemma p_depth_set_of_int: "of_int n \<in> p_depth_set p 0"
  using p_depth_set_of_nat p_depth_set_neg1 p_depth_set_minus by (induct n) simp_all

lemma global_depth_set_of_int: "of_int n \<in> global_depth_set 0"
  using p_depth_set_of_int global_depth_set by blast

lemma p_depth_set_polyderiv:
  "set (coeffs f) \<subseteq> p_depth_set p n \<Longrightarrow>
    set (coeffs (polyderiv f)) \<subseteq> p_depth_set p n"
proof (induct f)
  case (pCons a f)
  from pCons(1) have
    "set (coeffs (polyderiv (pCons a f))) =
      set (plus_coeffs (coeffs f) (coeffs (pCons 0 (polyderiv f))))"
    using polyderiv_pCons coeffs_plus_eq_plus_coeffs by metis
  moreover from pCons(1,3) have "set (coeffs f) \<subseteq> p_depth_set p n" by fastforce
  ultimately show ?case
    using pCons(2) p_depth_set_poly_pCons p_depth_set_0 p_depth_set_plus_coeffs by presburger
qed simp

lemma global_depth_set_polyderiv:
  "set (coeffs (polyderiv f)) \<subseteq> global_depth_set n"
  if "set (coeffs f) \<subseteq> global_depth_set n"
  using that p_depth_set_polyderiv global_depth_set by fastforce

lemma poly_p_depth_set_polyderiv:
  "poly (polyderiv f) x \<in> p_depth_set p n"
  if "n \<ge> 0" and "set (coeffs f) \<subseteq> p_depth_set p n" and "x \<in> p_depth_set p n"
  using that poly_p_depth_set_poly p_depth_set_polyderiv by blast

lemma poly_global_depth_set_polyderiv:
  "poly (polyderiv f) x \<in> global_depth_set n"
  if  "n \<ge> 0"
  and "set (coeffs f) \<subseteq> global_depth_set n"
  and "x \<in> global_depth_set n"
  using that poly_p_depth_set_polyderiv global_depth_set by fastforce

lemma p_set_depth_additive_poly_poly:
  "set (coeffs f) \<subseteq> p_depth_set p m \<Longrightarrow>
    set (coeffs (coeff (additive_poly_poly f) n)) \<subseteq> p_depth_set p m"
  if "m \<ge> 0"
proof (induct f arbitrary: n rule: pCons_induct')
  case (pCons0 a) thus ?case using additive_poly_poly_pCons0 by (cases n, fastforce, fastforce)
next
  case (pCons a f) show ?case
  proof (cases n)
    case 0 with pCons(1,3) show ?thesis by (simp add: additive_poly_poly_coeff0 cCons_def)
  next
    case (Suc k)
    moreover have
      "set (coeffs (pCons 0 1 * coeff (additive_poly_poly f) n + coeff (additive_poly_poly f) k))
        \<subseteq> p_depth_set p m"
      by (
        intro p_depth_set_poly_add p_depth_set_poly_times_ideal that pCons(2),
        simp add: p_depth_set_0 p_depth_set_1, use pCons(1,3) in auto
      )
    ultimately show
      "set (coeffs (coeff (additive_poly_poly (pCons a f)) n)) \<subseteq> p_depth_set p m"
      using pCons(1) additive_poly_poly_pCons coeff_add coeff_smult coeff_pCons_Suc by fastforce
  qed
qed simp

lemma global_depth_set_additive_poly_poly:
  "set (coeffs (coeff (additive_poly_poly f) n)) \<subseteq> global_depth_set m"
  if "m \<ge> 0" and "set (coeffs f) \<subseteq> global_depth_set m"
  using that p_set_depth_additive_poly_poly global_depth_set by fastforce

lemma poly_p_depth_set_additive_poly_poly:
  "poly (coeff (additive_poly_poly f) n) x \<in> p_depth_set p m"
  if "m \<ge> 0" and "set (coeffs f) \<subseteq> p_depth_set p m" and "x \<in> p_depth_set p m"
  using that poly_p_depth_set_poly p_set_depth_additive_poly_poly by auto

lemma poly_global_depth_set_additive_poly_poly:
  "poly (coeff (additive_poly_poly f) n) x \<in> global_depth_set m"
  if  "m \<ge> 0"
  and "set (coeffs f) \<subseteq> global_depth_set m"
  and "x \<in> global_depth_set m"
  using that poly_p_depth_set_additive_poly_poly global_depth_set by fastforce

lemma sum_poly_additive_poly_poly_depth_bound:
  fixes p :: 'a and f :: "'b poly" and x y :: 'b and a b n :: nat
  defines "g \<equiv> \<lambda>i. poly (coeff (additive_poly_poly f) (Suc i)) x * y ^ (Suc i)"
  defines "S \<equiv> sum g {a..b}"
  assumes coeffs: "set (coeffs f) \<subseteq> p_depth_set p 0"
    and   arg   : "x \<in> p_depth_set p 0"
    and   sum   : "\<not> p_equal p S 0"
  obtains j where "j \<in> {a..b}" and "p_depth p S \<ge> int (Suc j) * p_depth p y"
proof-
  from S_def sum obtain j where j:
    "j \<in> {a..b}" "\<not> p_equal p (g j) 0" "p_depth p S \<ge> p_depth p (g j)"
    using obtains_depth_sum_nonarch_witness by blast
  from g_def j(2)
    have  y_coeff_n0: "\<not> p_equal p (poly (coeff (additive_poly_poly f) (Suc j)) x) 0"
    using mult_0_left[of p _ "y ^ Suc j"]
    by    blast
  from g_def j(2,3) have
    "p_depth p (g j) =
      p_depth p (poly (coeff (additive_poly_poly f) (Suc j)) x) +
      int (Suc j) * p_depth p y"
    using depth_mult_additive[of p _ "y ^ Suc j"] depth_pow_additive[of p y "Suc j"] by auto
  also from coeffs arg
    have  "\<dots> \<ge> int (Suc j) * p_depth p y"
    using y_coeff_n0 poly_p_depth_set_additive_poly_poly[of 0 f p x "Suc j"]
          p_depth_setD[of p "poly (coeff (additive_poly_poly f) (Suc j)) x" 0]
    by    auto
  finally have "p_depth p (g j) \<ge> int (Suc j) * p_depth p y" by blast
  with j(3) have "p_depth p S \<ge> int (Suc j) * p_depth p y" by simp
  with j(1) that show thesis by blast
qed

end (* locale p_equality_depth_no_zero_divisors_1 *)

subsubsection \<open>Depth of inverses and division\<close>

locale p_equality_depth_div_inv =
  p_equality_div_inv + p_equality_depth_no_zero_divisors_1
begin

lemma inverse_depth: "p_depth p (inverse x) = - p_depth p x"
proof (cases "p_equal p x 0")
  case False
  from False have "p_depth p (x * inverse x) = 0"
    using depth_equiv right_inverse_equiv depth_of_1 by metis
  moreover from False have "\<not> p_equal p (x * inverse x) 0"
    using right_inverse_equiv trans_right one_p_nequal_zero by blast
  ultimately show ?thesis using depth_mult_additive by simp
qed (simp add: inverse_equiv0_iff depth_equiv_0)

lemma depth_powi_additive: "p_depth p (power_int x n) = n * p_depth p x"
proof (cases "n \<ge> 0")
  case True thus ?thesis using depth_pow_additive unfolding power_int_def by auto
next
  case False
  moreover from this have "(- int (nat (-n))) = n" by simp
  ultimately show ?thesis
    using power_int_def inverse_pow inverse_depth depth_pow_additive minus_mult_left by metis
qed

lemma p_depth_set_inverse: "inverse x \<in> p_depth_set p 0" if "p_depth p x = 0"
  using that inverse_depth p_depth_setI by force

lemma divide_depth: "p_depth p (x / y) = p_depth p x - p_depth p y" if "\<not> p_equal p (x / y) 0"
  using that by (simp add: divide_inverse depth_mult_additive inverse_depth)

lemma p_depth_set_divide:
  "x / y \<in> p_depth_set p n" if "x \<in> p_depth_set p n" and "p_depth p y = 0"
  by (
    auto  intro   : p_depth_setI
          simp add: that p_depth_set_equiv0 divide_equiv_0_iff p_depth_setD divide_depth
  )

lemma p_depth_poly_deriv_quotient:
  "p_depth p ((poly f a) / (poly (polyderiv f) a)) \<ge> n"
  if    "n \<ge> 0"
  and   "set (coeffs f) \<subseteq> p_depth_set p n"
  and   "a \<in> p_depth_set p n"
  and   "\<not> p_equal p (poly f a) 0"
  and   "\<not> p_equal p (poly (polyderiv f) a) 0"
  and   "p_depth p (poly f a) \<ge> 2 * p_depth p (poly (polyderiv f) a)"
  using that divide_equiv_0_iff divide_depth poly_p_depth_set_polyderiv poly_p_depth_set_poly
        p_depth_setD[of p "poly (polyderiv f) a" n]
  by    force

lemma p_depth_set_poly_deriv_quotient:
  "(poly f a) / (poly (polyderiv f) a) \<in> p_depth_set p n"
  if    "n \<ge> 0"
  and   "set (coeffs f) \<subseteq> p_depth_set p n"
  and   "a \<in> p_depth_set p n"
  and   "\<not> p_equal p (poly f a) 0"
  and   "\<not> p_equal p (poly (polyderiv f) a) 0"
  and   "p_depth p (poly f a) \<ge> 2 * p_depth p (poly (polyderiv f) a)"
  using that divide_equiv_0_iff p_depth_poly_deriv_quotient p_depth_setI
  by    presburger

end (* locale p_equality_depth_div_inv *)


subsection \<open>Global equality and restriction of places\<close>

subsubsection \<open>Locales\<close>

locale global_p_equality = p_equality
+
  fixes   p_restrict :: "'b::comm_ring \<Rightarrow> ('a \<Rightarrow> bool) \<Rightarrow> 'b"
  assumes p_restrict_equiv      : "P p \<Longrightarrow> p_equal p (p_restrict x P) x"
  and     p_restrict_equiv0     : "\<not> P p \<Longrightarrow> p_equal p (p_restrict x P) 0"
begin

lemma p_restrict_equiv_sym: "P p \<Longrightarrow> p_equal p x (p_restrict x P)"
  using p_restrict_equiv sym by presburger

lemma p_restrict_equiv0_iff:
  "p_equal p (p_restrict x P) 0 \<longleftrightarrow> p_equal p x 0 \<or> \<not> P p"
  by (metis p_restrict_equiv p_restrict_equiv0 trans trans_right)

lemma p_restrict_restrict_equiv_conj:
  "p_equal p (p_restrict (p_restrict x P) Q) (p_restrict x (\<lambda>p. P p \<and> Q p))"
proof-
  consider (both) "Q p" "P p" | (Q) "Q p" "\<not> P p" | (nQ) "\<not> Q p" by blast
  thus ?thesis
  proof cases
    case both thus ?thesis using p_restrict_equiv trans trans_left by metis
  next
    case Q thus ?thesis using p_restrict_equiv p_restrict_equiv0 trans trans_left by metis
  next
    case nQ thus ?thesis using p_restrict_equiv0 trans_left by metis
  qed
qed

lemma p_restrict_restrict_equiv: "p_equal p (p_restrict (p_restrict x P) P) (p_restrict x P)"
  using p_restrict_restrict_equiv_conj[of p x P P] by metis

lemma p_restrict_0_equiv0: "p_equal p (p_restrict 0 P) 0"
  by (metis p_restrict_equiv p_restrict_equiv0)

lemma p_restrict_add_equiv: "p_equal p (p_restrict (x + y) P) (p_restrict x P + p_restrict y P)"
  by (
    cases "P p", metis p_restrict_equiv sym add trans,
    metis p_restrict_equiv0 trans_left add_0_left
  )

lemma p_restrict_add_mixed_equiv:
  "p_equal p (p_restrict x P + p_restrict y Q) (x + y)" if "P p" and "Q p"
  using that p_restrict_equiv add by simp

lemma p_restrict_add_mixed_equiv_drop_right:
  "p_equal p (p_restrict x P + p_restrict y Q) x" if "P p" and "\<not> Q p"
  using that p_restrict_equiv[of P p x] p_restrict_equiv0[of Q p y] add by fastforce

lemma p_restrict_add_mixed_equiv_drop_left:
  "p_equal p (p_restrict x P + p_restrict y Q) y" if "\<not> P p" and "Q p"
  using that p_restrict_equiv[of Q p y] p_restrict_equiv0[of P p x] add by fastforce

lemma p_restrict_add_mixed_equiv_drop_both:
  "p_equal p (p_restrict x P + p_restrict y Q) 0" if "\<not> P p" and "\<not> Q p"
  using that p_restrict_equiv0[of P p x] p_restrict_equiv0[of Q p y] add by fastforce

lemma p_restrict_uminus_equiv: "p_equal p (p_restrict (-x) P) (- p_restrict x P)"
  by (
    cases "P p", metis p_restrict_equiv sym uminus trans,
    metis p_restrict_equiv0 uminus trans_left minus_zero
  )

lemma p_restrict_minus_equiv: "p_equal p (p_restrict (x - y) P) (p_restrict x P - p_restrict y P)"
  by (
    cases "P p", metis p_restrict_equiv sym minus trans,
    metis p_restrict_equiv0 minus trans_left diff_zero
  )

lemma p_restrict_minus_mixed_equiv:
  "p_equal p (p_restrict x P - p_restrict y Q) (x - y)" if "P p" and "Q p"
  using that p_restrict_equiv minus by simp

lemma p_restrict_minus_mixed_equiv_drop_right:
  "p_equal p (p_restrict x P - p_restrict y Q) x" if "P p" and "\<not> Q p"
  using that p_restrict_equiv[of P p x] p_restrict_equiv0[of Q p y] minus by fastforce

lemma p_restrict_minus_mixed_equiv_drop_left:
  "p_equal p (p_restrict x P - p_restrict y Q) (-y)" if "\<not> P p" and "Q p"
  using that p_restrict_equiv[of Q p y] p_restrict_equiv0[of P p x] minus by fastforce

lemma p_restrict_minus_mixed_equiv_drop_both:
  "p_equal p (p_restrict x P - p_restrict y Q) 0" if "\<not> P p" and "\<not> Q p"
  using that p_restrict_equiv0[of P p x] p_restrict_equiv0[of Q p y] minus by fastforce

lemma p_restrict_times_equiv:
  "p_equal p ((p_restrict x P) * (p_restrict y Q))
    (p_restrict (x * y) (\<lambda>p. P p \<and> Q p))"
proof-
  consider (both) "P p" "Q p" | (P) "P p" "\<not> Q p" | (nP) "\<not> P p" by blast
  thus ?thesis
  proof cases
    case both thus ?thesis using p_restrict_equiv sym mult trans by metis
  next
    case P thus ?thesis
      using p_restrict_equiv p_restrict_equiv0 mult trans_left mult_zero_right by metis
  next
    case nP thus ?thesis
      using p_restrict_equiv p_restrict_equiv0 mult trans_left mult_zero_left by metis
  qed
qed

lemma p_restrict_times_equiv':
  "p_equal p ((p_restrict x P) * (p_restrict y P)) (p_restrict (x * y) P)"
  using p_restrict_times_equiv[of p x P y P] by simp

lemma p_restrict_p_equalI:
  "p_equal p (p_restrict x P) y"
  if  "P p \<longrightarrow> p_equal p x y"
  and "\<not> P p \<longrightarrow> p_equal p y 0"
  by  (
    cases "P p", metis that(1) p_restrict_equiv trans, metis that(2) p_restrict_equiv0 trans_left
  )

lemma p_restrict_p_equal_p_restrictI:
  "p_equal p (p_restrict x P) (p_restrict y Q)"
  if  "(P p \<and> Q p)   \<longrightarrow> p_equal p x y"
  and "(P p \<and> \<not> Q p) \<longrightarrow> p_equal p x 0"
  and "(\<not> P p \<and> Q p) \<longrightarrow> p_equal p y 0"
proof (cases "P p" "Q p" rule: case_split[case_product case_split])
  case True_True thus ?thesis using that(1) p_restrict_equiv sym cong by metis
next
  case True_False thus ?thesis using that(2) p_restrict_equiv p_restrict_equiv0 sym cong by metis
next
  case False_True thus ?thesis using that(3) p_restrict_equiv p_restrict_equiv0 sym cong by metis
next
  case False_False thus ?thesis using p_restrict_equiv0 refl cong by metis
qed

lemma p_restrict_p_equal_p_restrict_by_sameI:
  "p_equal p (p_restrict x P) (p_restrict y P)" if "P p \<longrightarrow> p_equal p x y"
  using that p_restrict_p_equal_p_restrictI by auto

end (* locale global_p_equality *)


locale global_p_equality_div_inv =
  p_equality_div_inv p_equal + global_p_equality p_equal p_restrict
  for p_equal    ::
    "'a \<Rightarrow> 'b::{comm_ring_1, inverse, divide_trivial} \<Rightarrow>
      'b \<Rightarrow> bool"
  and p_restrict :: "'b \<Rightarrow> ('a \<Rightarrow> bool) \<Rightarrow> 'b"
begin

lemma inverse_p_restrict_equiv: "p_equal p (inverse (p_restrict x P)) (p_restrict (inverse x) P)"
  by (
    cases "p_equal p x 0 \<or> \<not> P p",
    metis p_restrict_equiv0_iff inverse_equiv0_iff trans_left,
    intro inverse_p_unique, metis p_restrict_times_equiv' p_restrict_equiv right_inverse_equiv trans
  )

end (* locale global_p_equality_div_inv *)


locale global_p_equal = global_p_equality
+ assumes global_imp_eq: "globally_p_equal x y \<Longrightarrow> x = y"
begin

lemma global_eq_iff: "globally_p_equal x y \<longleftrightarrow> x = y"
  using global_imp_eq by fastforce

lemma p_restrict_true[simp] : "p_restrict x (\<lambda>x. True) = x"
  using p_restrict_equiv[of "\<lambda>x. True"] global_imp_eq by blast

lemma p_restrict_false[simp]: "p_restrict x (\<lambda>x. False) = 0"
  using p_restrict_equiv0[of "\<lambda>x. False"] global_imp_eq by blast

lemma p_restrict_restrict:
  "p_restrict (p_restrict x P) Q = p_restrict x (\<lambda>p. P p \<and> Q p)"
  using p_restrict_restrict_equiv_conj global_imp_eq by blast

lemma p_restrict_restrict'[simp]: "p_restrict (p_restrict x P) P = p_restrict x P"
  using p_restrict_restrict by fastforce

lemma p_restrict_image_restrict: "p_restrict x P = x" if "x \<in> (\<lambda>z. p_restrict z P) ` B"
proof-
  from that obtain z where "x = p_restrict z P" by blast
  thus ?thesis using p_restrict_restrict' by auto
qed

lemma p_restrict_zero: "p_restrict 0 P = 0"
  using p_restrict_0_equiv0 global_imp_eq by blast

lemma p_restrict_add: "p_restrict (x + y) P = p_restrict x P + p_restrict y P"
  using p_restrict_add_equiv global_imp_eq by blast

lemma p_restrict_uminus: "p_restrict (-x) P = - p_restrict x P"
  using p_restrict_uminus_equiv global_imp_eq by blast

lemma p_restrict_minus: "p_restrict (x - y) P = p_restrict x P - p_restrict y P"
  using p_restrict_minus_equiv global_imp_eq by blast

lemma p_restrict_times:
  "(p_restrict x P) * (p_restrict y Q) = p_restrict (x * y) (\<lambda>p. P p \<and> Q p)"
  using p_restrict_times_equiv global_imp_eq by blast

lemma times_p_restrict: "x * (p_restrict y P) = p_restrict (x * y) P"
  using p_restrict_times[of x "\<lambda>p. True"] by auto

lemmas p_restrict_pre_finite_adele_simps =
  p_restrict_zero p_restrict_add p_restrict_uminus p_restrict_minus p_restrict_times

lemma p_equal_0_iff_p_restrict_eq_0: "p_equal p x 0 \<longleftrightarrow> p_restrict x ((=) p) = 0"
proof (standard, rule global_imp_eq, standard)
  fix q show "p_equal p x 0 \<Longrightarrow> p_equal q (p_restrict x ((=) p)) 0"
    using p_restrict_equiv[of "(=) p"] trans p_restrict_equiv0[of "(=) p"]
    by    (cases "p = q", blast, blast)
qed (metis (full_types) p_restrict_equiv_sym)

lemma p_equal_iff_p_restrict_eq:
  "p_equal p x y \<longleftrightarrow> p_restrict x ((=) p) = p_restrict y ((=) p)"
  using conv_0 p_equal_0_iff_p_restrict_eq_0 p_restrict_minus by auto

lemma p_restrict_eqI:
  "y = p_restrict x P"
  if      P: "\<And>p. P p \<Longrightarrow> p_equal p y x"
  and not_P: "\<And>p. \<not> P p \<Longrightarrow> p_equal p y 0"
proof (intro global_imp_eq, standard)
  fix p :: 'a show "p_equal p y (p_restrict x P)"
    by (cases "P p", metis P p_restrict_equiv trans_left, metis not_P p_restrict_equiv0 trans_left)
qed

lemma p_restrict_eq_p_restrict_mixedI:
  "p_restrict x P = p_restrict y Q"
  if  both: "\<And>p::'a. P p \<Longrightarrow> Q p \<Longrightarrow> p_equal p x y"
  and P   : "\<And>p::'a. P p \<Longrightarrow> \<not> Q p \<Longrightarrow> p_equal p x 0"
  and Q   : "\<And>p::'a. \<not> P p \<Longrightarrow> Q p \<Longrightarrow> p_equal p y 0"
  by (
    intro p_restrict_eqI, metis both Q p_restrict_equiv trans p_restrict_equiv0 trans_left,
    metis P p_restrict_equiv trans p_restrict_equiv0
  )

lemma p_restrict_eq_p_restrictI:
  "p_restrict x P = p_restrict y P" if "\<And>p::'a. P p \<Longrightarrow> p_equal p x y"
  by (intro p_restrict_eqI, metis that trans p_restrict_equiv, simp add: p_restrict_equiv0)

lemma p_restrict_eq_p_restrict_iff:
  "p_restrict x P = p_restrict y P \<longleftrightarrow>
    (\<forall>p::'a. P p \<longrightarrow> p_equal p x y)"
  by (standard, safe, metis p_restrict_equiv trans_right, simp add: p_restrict_eq_p_restrictI)

lemma p_restrict_eq_zero_iff:
  "p_restrict x P = 0 \<longleftrightarrow> (\<forall>p. P p \<longrightarrow> p_equal p x 0)"
proof-
  have "(p_restrict x P = 0) = (\<forall>p. p_equal p (p_restrict x P) 0)"
    using global_imp_eq by auto
  thus ?thesis by (metis p_restrict_equiv p_restrict_equiv0 trans trans_right)
qed

lemma p_restrict_decomp:
  "x = p_restrict x P + p_restrict x (\<lambda>p. \<not> P p)"
proof (intro global_imp_eq, standard)
  fix p show "p_equal p x (p_restrict x P + p_restrict x (\<lambda>p. \<not> P p))"
    using p_restrict_add_mixed_equiv_drop_left p_restrict_add_mixed_equiv_drop_right sym by metis
qed

lemma restrict_complement:
  "range (\<lambda>x. p_restrict x P) + range (\<lambda>x. p_restrict x (\<lambda>p. \<not> P p))
    = UNIV"
  using p_restrict_decomp[of _ P]
        set_plus_intro[of
          "p_restrict _ P" "range (\<lambda>x. p_restrict x P)"
          "p_restrict _ (\<lambda>p. \<not> P p)"
          "range (\<lambda>x. p_restrict x (\<lambda>p. \<not> P p))"
        ]
  by    fastforce

end (* locale global_p_equal *)


locale global_p_equal_no_zero_divisors =
  global_p_equal p_equal p_restrict + p_equality_no_zero_divisors p_equal
  for p_equal :: "'a \<Rightarrow> 'b::comm_ring \<Rightarrow> 'b \<Rightarrow> bool"
  and p_restrict :: "'b \<Rightarrow> ('a \<Rightarrow> bool) \<Rightarrow> 'b"


locale global_p_equal_no_zero_divisors_1 =
  global_p_equal_no_zero_divisors p_equal p_restrict + p_equality_no_zero_divisors_1 p_equal
  for p_equal :: "'a \<Rightarrow> 'b::comm_ring_1 \<Rightarrow> 'b \<Rightarrow> bool"
  and p_restrict :: "'b \<Rightarrow> ('a \<Rightarrow> bool) \<Rightarrow> 'b"
begin

lemma pow_eq_0_iff: "x ^ n = 0 \<longleftrightarrow> x = 0 \<and> n \<noteq> 0" for x :: 'b
  using global_eq_iff pow_equiv_0_iff[of _ x n] by force

end (* locale global_p_equal_no_zero_divisors_1 *)


locale global_p_equal_div_inv =
  global_p_equality_div_inv p_equal p_restrict
+ global_p_equal p_equal p_restrict
  for p_equal    ::
    "'a \<Rightarrow> 'b::{comm_ring_1, inverse, divide_trivial} \<Rightarrow>
      'b \<Rightarrow> bool"
  and p_restrict :: "'b \<Rightarrow> ('a \<Rightarrow> bool) \<Rightarrow> 'b"
begin

lemma power_int_eq_0_iff:
  "power_int x n = 0 \<longleftrightarrow> x = 0 \<and> n \<noteq> 0" for x :: 'b
  using global_eq_iff power_int_equiv_0_iff[of _ x n] by fastforce

lemma inverse_eq0_iff: "inverse x = 0 \<longleftrightarrow> x = 0" for x :: 'b
  using inverse_equiv0_iff global_eq_iff by fastforce

lemma inverse_neg_1 [simp]: "inverse (-1::'b) = -1"
  using global_imp_eq globally_inverse_neg_1 by force

lemma inverse_uminus: "inverse (-x) = - inverse x" for x :: 'b
  using global_imp_eq inverse_uminus_equiv by blast

lemma global_right_inverse: "x * inverse x = 1" if "\<forall>p. \<not> p_equal p x 0"
  using that global_imp_eq right_inverse_equiv by fast

lemma right_inverse: "x * inverse x = p_restrict 1 (\<lambda>p. \<not> p_equal p x 0)"
proof (intro global_imp_eq, standard)
  fix p :: 'a show "p_equal p (x * inverse x) (p_restrict 1 (\<lambda>p. \<not> p_equal p x 0))"
  by (
    cases "p_equal p x 0", metis inverse_equiv0_iff mult_0_right p_restrict_equiv0 trans_left,
    metis right_inverse_equiv p_restrict_equiv trans_left
  )
qed

lemma global_left_inverse: "inverse x * x = 1" if "\<forall>p. \<not> p_equal p x 0"
  using that global_imp_eq left_inverse_equiv by fast

lemma left_inverse: "inverse x * x = p_restrict 1 (\<lambda>p. \<not> p_equal p x 0)"
  by (metis right_inverse mult.commute)

lemma inverse_unique: "inverse x = y" if "x * y = 1" for x y :: 'b
  using that inverse_p_unique global_imp_eq[of "inverse x" y] by fastforce

lemma inverse_p_restrict: "inverse (p_restrict x P) = p_restrict (inverse x) P"
  using global_imp_eq inverse_p_restrict_equiv by blast

lemma power_diff_conv_inverse:
  "x ^ (n - m) =  x ^ n * inverse x ^ m" if "m < n"
  for x :: 'b
proof (intro global_imp_eq, standard)
  fix p show "p_equal p (x ^ (n - m)) (x ^ n * inverse x ^ m)"
  proof (cases "p_equal p x 0")
    case True
    from that True have "p_equal p (x ^ n * inverse x ^ m) 0"
      using pow_equiv_0_iff inverse_equiv0_iff mult_0_left mult_0_right by force
    moreover from that True have "p_equal p (x ^ (n - m)) 0" using pow_equiv_0_iff by fastforce
    ultimately show ?thesis using trans_left by fast
  next
    case False with that show ?thesis using power_diff_conv_inverse_equiv by simp
  qed
qed

lemma power_int_add_1: "power_int x (m + 1) = power_int x m * x" if "m \<noteq> -1" for x :: 'b
  using that power_int_add_1_equiv by (auto intro: global_imp_eq)

lemma power_int_add:
  "power_int x (m + n) = power_int x m * power_int x n"
  if "(\<forall>p. \<not> p_equal p x 0) \<or> m + n \<noteq> 0" for x :: 'b
  using that power_int_add_equiv by (auto intro: global_imp_eq)

lemma power_int_diff:
  "power_int x (m - n) = power_int x m / power_int x n" if "m \<noteq> n" for x :: 'b
  using that power_int_diff_equiv by (auto intro: global_imp_eq)

lemma power_int_minus_mult: "power_int x (n - 1) * x = power_int x n" if "n \<noteq> 0" for x :: 'b
  using that power_int_minus_mult_equiv by (auto intro: global_imp_eq)

lemma power_int_not_eq_zero:
  "x \<noteq> 0 \<or> n = 0 \<Longrightarrow> power_int x n \<noteq> 0" for x :: 'b
  by (subst power_int_eq_0_iff) auto

lemma minus_divide_right: "a / (- b) = - (a / b)" for a b :: 'b
  using global_imp_eq minus_divide_right_equiv by blast

lemma minus_divide_divide: "(- a) / (- b) = a / b" for a b :: 'b
  using global_imp_eq minus_divide_divide_equiv by blast

lemma divide_minus1 [simp]: "x / (-1) = - x" for x :: 'b
  using global_imp_eq divide_minus1_equiv by blast

lemma divide_self: "x / x = p_restrict 1 (\<lambda>p. \<not> p_equal p x 0)"
  by (metis divide_inverse right_inverse)

lemma global_divide_self: "x / x = 1" if "\<forall>p. \<not> p_equal p x 0"
  by (metis that global_right_inverse divide_inverse)

lemma global_mult_divide_mult_cancel_right:
  "(a * b) / (c * b) = a / c" if "\<forall>p. \<not> p_equal p b 0"
  using that global_imp_eq mult_divide_mult_cancel_right[of _ b a c] by fastforce

lemma global_mult_divide_mult_cancel_left:
  "(c * a) / (c * b) = a / b" if "\<forall>p. \<not> p_equal p c 0"
  by (metis that global_mult_divide_mult_cancel_right mult.commute)

lemma divide_p_restrict_left: "(p_restrict x P) / y = p_restrict (x / y) P"
  using p_restrict_eqI[of P "(p_restrict x P) / y"] p_restrict_equiv[of P _ x]
        p_restrict_equiv0[of P _ x] divide_left_equiv
  by    fastforce

lemma divide_p_restrict_right: "x / (p_restrict y P) = p_restrict (x / y) P"
  using p_restrict_eqI[of P "x / (p_restrict y P)"] p_restrict_equiv[of P _ y]
        p_restrict_equiv0[of P _ y] divide_right_equiv
  by    fastforce

lemma inj_divide_right:
  "inj (\<lambda>b. b / a) \<longleftrightarrow> (\<forall>p. \<not> p_equal p a 0)"
  unfolding inj_def
proof (standard, safe)
  fix p
  assume  inj: "\<forall>x y :: 'b. x / a = y / a \<longrightarrow> x = y"
    and   a  : "p_equal p a 0"
  from a have "(p_restrict 1 ((=) p)) / a = (p_restrict 0 ((=) p)) / a"
    by (simp add: p_restrict_eq_p_restrictI divide_equiv_0_iff divide_p_restrict_left)
  with inj show False using p_restrict_eq_p_restrict_iff one_p_nequal_zero by blast
next
  fix x y :: 'b
  assume a: "\<forall>p. \<not> p_equal p a 0 " and xy: "x / a = y / a"
  thus "x = y"
    using times_divide_eq_right[of a x a] times_divide_eq_right[of a y a]
          mult_divide_cancel_left[of _ a x] mult_divide_cancel_left[of _ a y]
          cong global_imp_eq[of x y]
    by    fastforce
qed

end (* locale global_p_equal_div_inv *)


locale global_p_equality_depth = global_p_equality + p_equality_depth
begin

lemma globally_p_equal_p_depth: "globally_p_equal x y \<Longrightarrow> p_depth p x = p_depth p y"
  using depth_equiv globally_p_equalD by simp

lemma p_restrict_depth:
  "P p \<Longrightarrow> p_depth p (p_restrict x P) = p_depth p x"
  "\<not> P p \<Longrightarrow> p_depth p (p_restrict x P) = 0"
  by (metis p_restrict_equiv depth_equiv, metis p_restrict_equiv0 depth_equiv_0)

lemma p_restrict_add_mixed_depth_drop_right:
  "p_depth p (p_restrict x P + p_restrict y Q) = p_depth p x" if "P p" and "\<not> Q p"
  using that p_restrict_add_mixed_equiv_drop_right depth_equiv by auto

lemma p_restrict_add_mixed_depth_drop_left:
  "p_depth p (p_restrict x P + p_restrict y Q) = p_depth p y" if "\<not> P p" and "Q p"
  using that p_restrict_add_mixed_equiv_drop_left depth_equiv by auto

lemma p_depth_set_p_restrict:
  "p_restrict x P \<in> p_depth_set p n" if "P p \<longrightarrow> x \<in> p_depth_set p n"
proof (rule p_depth_set_by_equivI)
  show "p_equal p (p_restrict x P) (if P p then x else 0)"
    using p_restrict_equiv p_restrict_equiv0 by simp
  from that show "(if P p then x else 0) \<in> p_depth_set p n"
    using p_depth_set_0 by auto
qed

lemma global_depth_set_p_restrict:
  "p_restrict x P \<in> global_depth_set n" if "x \<in> global_depth_set n"
  using that p_depth_set_p_restrict global_depth_set by auto

lemma p_depth_set_closed_under_p_restrict_image:
  "(\<lambda>x. p_restrict x P) ` p_depth_set p n \<subseteq> p_depth_set p n"
  using p_depth_set_p_restrict by blast

lemma global_depth_set_closed_under_p_restrict_image:
  "(\<lambda>x. p_restrict x P) ` global_depth_set n \<subseteq> global_depth_set n"
  using global_depth_set_p_restrict by blast

lemma global_depth_set_p_restrictI:
  "p_restrict x P \<in> global_depth_set n"
  if "\<And>p. P p \<Longrightarrow> x \<in> p_depth_set p n"
  by (
    intro global_depth_setI,
    metis that p_restrict_equiv p_restrict_equiv0 trans p_depth_setD p_restrict_depth(1)
  )

lemma p_depth_set_image_under_one_p_restrict_image:
  "(\<lambda>x. p_restrict x ((=) p)) ` p_depth_set p n \<subseteq> global_depth_set n"
  using global_depth_set_p_restrictI by force

end (* locale global_p_equality_depth *)


locale global_p_equality_depth_no_zero_divisors_1 =
  p_equality_depth_no_zero_divisors_1 p_equal p_depth
+ global_p_equality_depth p_equal p_restrict p_depth
  for p_equal    ::
    "'a \<Rightarrow> 'b::comm_ring_1 \<Rightarrow> 'b \<Rightarrow> bool"
  and p_restrict :: "'b \<Rightarrow> ('a \<Rightarrow> bool) \<Rightarrow> 'b"
  and p_depth    :: "'a \<Rightarrow> 'b \<Rightarrow> int"


locale global_p_equality_depth_div_inv =
  p_equality_depth_div_inv + global_p_equality_depth
begin

sublocale global_p_equality_div_inv ..

lemma global_depth_set_inverse:
  "p_restrict (inverse x) (\<lambda>p. p_depth p x = 0) \<in> global_depth_set 0"
  using global_depth_set_p_restrictI p_depth_set_inverse by simp

lemma global_depth_set_divide:
  "p_restrict (x / y) (\<lambda>p. p_depth p y = 0) \<in> global_depth_set n"
  if "x \<in> global_depth_set n"
  using that global_depth_set_p_restrictI global_depth_set p_depth_set_divide by auto

lemma global_depth_set_divideI:
  "p_restrict (x / y) (\<lambda>p. p_depth p y = 0) \<in> global_depth_set n"
  if "\<And>p. p_depth p y = 0 \<Longrightarrow> x \<in> p_depth_set p n"
  using that global_depth_set_p_restrictI global_depth_set p_depth_set_divide by auto

end


locale global_p_equal_depth = global_p_equal + global_p_equality_depth
begin

lemma p_depth_set_vs_global_depth_set_image_under_one_p_restrict_image:
  "(\<lambda>x. p_restrict x ((=) p)) ` p_depth_set p n =
    (\<lambda>x. p_restrict x ((=) p)) `global_depth_set n"
proof (standard, standard, clarify)
  fix x assume "x \<in> p_depth_set p n"
  hence "p_restrict x ((=) p) \<in> global_depth_set n"
    using p_depth_set_image_under_one_p_restrict_image by fast
  thus "p_restrict x ((=) p) \<in> (\<lambda>x. p_restrict x ((=) p)) `global_depth_set n"
    using p_restrict_restrict'[of x "(=) p", symmetric] by blast
qed (use global_depth_set in fast)

end

locale global_p_equal_depth_no_zero_divisors =
  global_p_equal_no_zero_divisors + p_equality_depth_no_zero_divisors
begin
sublocale global_p_equal_depth ..
end


locale global_p_equal_depth_div_inv =
  global_p_equality_depth_div_inv + global_p_equal_depth_no_zero_divisors
begin

sublocale global_p_equal_div_inv ..

lemma p_depth_set_eq_coset:
  "p_depth_set p n = (w powi n) *o (p_depth_set p 0)"
  if "p_depth p w = 1" and "\<forall>p. \<not> p_equal p w 0"
  unfolding elt_set_times_def
proof safe
  fix x assume "x \<in> p_depth_set p n"
  moreover define y where "y \<equiv> w powi (-n) * x"
  ultimately have "y \<in> p_depth_set p 0"
    using that(1) mult_0_right p_depth_setD depth_mult_additive depth_powi_additive
    by    (intro p_depth_setI, clarify, fastforce)
  moreover from y_def have "x = w powi n * y"
    using that(2) power_int_equiv_0_iff global_right_inverse power_int_minus
    by    (force simp flip: mult.assoc)
  ultimately show "\<exists>y\<in>p_depth_set p 0. x = w powi n * y" by metis
next
  fix x assume "x \<in> p_depth_set p 0"
  thus "w powi n * x \<in> p_depth_set p n"
    using that(1) mult_0_right p_depth_setD depth_mult_additive depth_powi_additive
    by    (intro p_depth_setI, clarify, fastforce)
qed

lemma global_depth_set_eq_coset:
  "global_depth_set n = (w powi n) *o (global_depth_set 0)" if "\<forall>p. p_depth p w = 1"
  unfolding elt_set_times_def
proof safe
  fix x assume x: "x \<in> global_depth_set n"
  define y where "y \<equiv> w powi (-n) * x"
  from that have "\<forall>p. \<not> p_equal p w 0" using depth_equiv_0 by fastforce
  with y_def have "x = w powi n * y"
    using power_int_equiv_0_iff global_right_inverse power_int_minus mult.assoc mult_1_left by metis
  moreover from x y_def have "y \<in> global_depth_set 0"
    using that mult_0_right global_depth_setD depth_mult_additive depth_powi_additive
    by    (intro global_depth_setI, fastforce)
  ultimately show "\<exists>y\<in>global_depth_set 0. x = w powi n * y" by metis
next
  fix x assume "x \<in> global_depth_set 0"
  thus "w powi n * x \<in> global_depth_set n"
    using that mult_0_right global_depth_setD depth_mult_additive depth_powi_additive
    by    (intro global_depth_setI, fastforce)
qed

lemma p_depth_set_eq_coset':
  "p_depth_set p 0 = (w powi (-n)) *o (p_depth_set p n)"
  if "p_depth p w = 1" and "\<forall>p. \<not> p_equal p w 0"
proof-
  from that(2) have "w powi (-n) * w powi n = 1"
    using power_int_minus power_int_equiv_0_iff global_left_inverse by simp
  with that show ?thesis
    using p_depth_set_eq_coset set_times_rearrange2 power_int_minus set_one_times by metis
qed

lemma global_depth_set_eq_coset':
  "global_depth_set 0 = (w powi (-n)) *o (global_depth_set n)" if "\<forall>p. p_depth p w = 1"
proof-
  from that have "\<forall>p. \<not> p_equal p w 0" using depth_equiv_0 by fastforce
  hence "w powi (-n) * w powi n = 1"
    using power_int_minus power_int_equiv_0_iff global_left_inverse by presburger
  with that show ?thesis
    using global_depth_set_eq_coset set_times_rearrange2 power_int_minus set_one_times by metis
qed

end (* locale global_p_equal_depth_div_inv *)


subsubsection \<open>Embedding of base type constants\<close>

locale global_p_equality_w_consts = global_p_equality p_equal p_restrict
  for p_equal    ::
    "'a \<Rightarrow> 'b::comm_ring_1 \<Rightarrow> 'b \<Rightarrow> bool"
  and p_restrict :: "'b \<Rightarrow> ('a \<Rightarrow> bool) \<Rightarrow> 'b"
+
  fixes func_of_consts :: "('a \<Rightarrow> 'c::ring_1) \<Rightarrow> 'b"
  assumes consts_1    [simp]: "func_of_consts 1 = 1"
    and   consts_diff [simp]: "func_of_consts (f - g) = func_of_consts f - func_of_consts g"
    and   consts_mult [simp]:
      "func_of_consts (f * g) = func_of_consts f * func_of_consts g"
begin

abbreviation "consts \<equiv> func_of_consts"
abbreviation "const a \<equiv> consts (\<lambda>p. a)"

lemma consts_0[simp]: "consts 0 = 0"
  using consts_diff[of 0 0] by force

lemma const_0[simp]: "const 0 = 0"
  using consts_0 unfolding zero_fun_def by simp

lemma const_1[simp]: "const 1 = 1"
  using consts_1 unfolding one_fun_def by simp

lemma consts_uminus [simp]: "consts (- f) = - consts f"
  using consts_diff[of 0 f] by fastforce

lemma const_uminus [simp]: "const (-a) = - const a"
  using consts_uminus unfolding fun_Compl_def by auto

lemma const_diff [simp]: "const (a - b) = const a - const b"
  using consts_diff unfolding fun_diff_def by auto

lemma consts_add [simp]: "consts (f + g) = consts f + consts g"
proof-
  have "consts f + consts g = consts (f - (-g))" by (simp flip: diff_minus_eq_add)
  thus ?thesis by simp
qed

lemma const_add [simp]: "const (a + b) = const a + const b"
  using consts_add unfolding plus_fun_def by auto

lemma const_mult [simp]: "const (a * b) = const a * const b"
  using consts_mult unfolding times_fun_def by auto

lemma const_of_nat: "const (of_nat n) = of_nat n"
  by (induct n) simp_all

lemma const_of_int: "const (of_int z) = of_int z"
  by (cases z rule: int_cases2, simp_all add: const_of_nat)

end (* locale global_p_equality_w_consts *)


locale global_p_equal_w_consts =
  global_p_equal p_equal p_restrict
+ global_p_equality_w_consts p_equal p_restrict func_of_consts
  for p_equal ::
    "'a \<Rightarrow> 'b::comm_ring_1 \<Rightarrow> 'b \<Rightarrow> bool"
  and p_restrict :: "'b \<Rightarrow> ('a \<Rightarrow> bool) \<Rightarrow> 'b"
  and func_of_consts :: "('a \<Rightarrow> 'c::ring_1) \<Rightarrow> 'b"


locale global_p_equality_w_inj_consts = global_p_equality_w_consts
+
  assumes p_equal_func_of_consts_0: "p_equal p (consts f) 0 \<longleftrightarrow> f p = 0"
begin

lemmas p_equal_func_of_const_0 = p_equal_func_of_consts_0[of _ "\<lambda>p. _"]

lemma p_equal_func_of_consts:
  "p_equal p (consts f) (consts g) \<longleftrightarrow> f p = g p"
  by (metis conv_0 consts_diff p_equal_func_of_consts_0 fun_diff_def right_minus_eq)

lemma globally_p_equal_func_of_consts:
  "globally_p_equal (func_of_consts f) (func_of_consts g) \<longleftrightarrow>
    (\<forall>p. f p = g p)"
  using p_equal_func_of_consts unfolding globally_p_equal_def by auto

lemma const_p_equal: "p_equal p (const a) (const b) \<Longrightarrow> a = b"
  using p_equal_func_of_consts by force

end (* locale global_p_equality_w_inj_consts *)


locale global_p_equality_w_inj_consts_char_0 =
  global_p_equality_w_inj_consts p_equal p_restrict func_of_consts
  for p_equal        ::
    "'a \<Rightarrow> 'b::comm_ring_1 \<Rightarrow> 'b \<Rightarrow> bool"
  and p_restrict     :: "'b \<Rightarrow> ('a \<Rightarrow> bool) \<Rightarrow> 'b"
  and func_of_consts :: "('a \<Rightarrow> 'c::ring_char_0) \<Rightarrow> 'b"
begin

lemma const_of_nat_p_equal_0_iff: "p_equal p (of_nat n) 0 \<longleftrightarrow> n = 0"
  by (metis const_of_nat p_equal_func_of_const_0 of_nat_eq_0_iff)

lemma const_of_int_p_equal_0_iff: "p_equal p (of_int z) 0 \<longleftrightarrow> z = 0"
  by (metis const_of_int of_int_eq_0_iff p_equal_func_of_const_0)

end (* locale global_p_equality_w_inj_consts_char_0 *)


locale global_p_equality_div_inv_w_inj_consts =
  p_equality_div_inv + global_p_equality_w_inj_consts
begin

lemma consts_divide_self_equiv: "p_equal p ((consts f) / (consts f)) 1" if "f p \<noteq> 0"
  using that
  by    (simp add: p_equal_func_of_consts divide_self_equiv flip: consts_0)

lemma const_divide_self_equiv: "p_equal p ((const c) / (const c)) 1" if "c \<noteq> 0"
  using that by (simp add: consts_divide_self_equiv)

end (* locale global_p_equality_div_inv_w_consts *)


locale global_p_equal_w_inj_consts =
  global_p_equal p_equal p_restrict
+ global_p_equality_w_inj_consts p_equal p_restrict
  for p_equal    ::
    "'a \<Rightarrow> 'b::comm_ring_1 \<Rightarrow> 'b \<Rightarrow> bool"
  and p_restrict :: "'b \<Rightarrow> ('a \<Rightarrow> bool) \<Rightarrow> 'b"
begin

lemma consts_eq_iff: "consts f = consts g \<longleftrightarrow> f = g"
  using global_eq_iff globally_p_equal_func_of_consts by blast

lemma consts_eq_0_iff: "consts f = 0 \<longleftrightarrow> f = 0"
  using consts_eq_iff by force

lemma inj_consts: "inj consts"
  using consts_eq_iff injI by meson

lemma const_eq_iff: "const a = const b \<longleftrightarrow> a = b"
  by (metis consts_eq_iff)

lemma const_eq_0_iff: "const a = 0 \<longleftrightarrow> a = 0"
  using consts_eq_0_iff unfolding zero_fun_def by metis

lemma inj_const: "inj const"
  using const_eq_iff injI by meson

end (* locale global_p_equal_w_inj_consts *)


locale global_p_equal_div_inv_w_inj_consts =
  global_p_equal_div_inv + global_p_equal_w_inj_consts
begin

sublocale global_p_equality_div_inv_w_inj_consts ..

lemma consts_divide_self:
  "(consts f) / (consts f) = p_restrict 1 (\<lambda>p::'a. f p \<noteq> 0)"
  by (simp add: p_equal_func_of_consts_0 divide_self)

lemma const_right_inverse [simp]: "const a * inverse (const a) = 1" if "a \<noteq> 0"
  using that global_right_inverse p_equal_func_of_const_0 by blast

lemma const_left_inverse [simp]: "inverse (const a) * const a = 1" if "a \<noteq> 0"
  by (metis that const_right_inverse mult.commute)

lemma const_divide_self: "(const c) / (const c) = 1" if "c \<noteq> 0"
  using that by (simp add: divide_inverse)

lemma mult_const_divide_mult_const_cancel_right:
  "(y * const a) / (z * const a) = y / z" if "a \<noteq> 0"
  using that global_mult_divide_mult_cancel_right p_equal_func_of_const_0 by blast

lemma mult_const_divide_mult_const_cancel_left:
  "(const a * y) / (const a * z) = y / z" if "a \<noteq> 0"
  by (metis that mult_const_divide_mult_const_cancel_right mult.commute)

lemma mult_const_divide_mult_const_cancel_left_right:
  "(const a * y) / (z * const a) = y / z" if "a \<noteq> 0"
  by (metis that mult.commute mult_const_divide_mult_const_cancel_left)

lemma mult_const_divide_mult_const_cancel_right_left:
  "(y * const a) / (const a * z) = y / z" if "a \<noteq> 0"
  by (metis that mult.commute mult_const_divide_mult_const_cancel_left)

end (* locale global_p_equal_div_inv_w_consts *)


locale global_p_equal_div_inv_w_inj_consts_char_0 =
  global_p_equality_w_inj_consts_char_0 p_equal p_restrict func_of_consts
+ global_p_equal_div_inv_w_inj_consts p_equal p_restrict func_of_consts
  for p_equal        ::
    "'a \<Rightarrow> 'b::{comm_ring_1, ring_char_0, inverse, divide_trivial} \<Rightarrow>
      'b \<Rightarrow> bool"
  and p_restrict     :: "'b \<Rightarrow> ('a \<Rightarrow> bool) \<Rightarrow> 'b"
  and func_of_consts :: "('a \<Rightarrow> 'c::ring_char_0) \<Rightarrow> 'b"
begin

context
  fixes n :: nat
  assumes "n \<noteq> 0"
begin

lemma left_inverse_const_of_nat[simp]: "inverse (of_nat n :: 'b) * of_nat n = 1"
  by (metis \<open>n \<noteq> 0\<close> const_of_nat const_left_inverse of_nat_eq_0_iff)

lemma right_inverse_const_of_nat[simp]: "of_nat n * inverse (of_nat n :: 'b) = 1"
  by (metis left_inverse_const_of_nat mult.commute)

lemma divide_self_const_of_nat[simp]: "(of_nat n :: 'b) / of_nat n = 1"
  by (metis \<open>n \<noteq> 0\<close> of_nat_eq_0_iff const_of_nat const_divide_self)

lemma mult_const_of_nat_divide_const_mult_of_nat_cancel_right:
  "(a * of_nat n) / (b * of_nat n) = a / b" for a b :: 'b
  using \<open>n \<noteq> 0\<close> const_of_nat of_nat_eq_0_iff
        mult_const_divide_mult_const_cancel_right
  by    metis

lemma mult_const_of_nat_divide_const_mult_of_nat_cancel_left:
  "(of_nat n * a) / (of_nat n * b) = a / b" for a b :: 'b
  by (metis mult_const_of_nat_divide_const_mult_of_nat_cancel_right mult.commute)

end (* context nonzero nat *)

context
  fixes z :: int
  assumes "z \<noteq> 0"
begin

lemma left_inverse_const_of_int[simp]: "inverse (of_int z :: 'b) * of_int z = 1"
  by (metis \<open>z \<noteq> 0\<close> const_of_int const_left_inverse of_int_eq_0_iff)

lemma right_inverse_const_of_int[simp]: "of_int z * inverse (of_int z :: 'b) = 1"
  by (metis left_inverse_const_of_int mult.commute)

lemma divide_self_const_of_int[simp]: "(of_int z :: 'b) / of_int z = 1"
  by (metis \<open>z \<noteq> 0\<close> of_int_eq_0_iff const_of_int const_divide_self)

lemma mult_const_of_int_divide_const_mult_of_int_cancel_right:
  "(a * of_int z) / (b * of_int z) = a / b" for a b :: 'b
  by (
    metis \<open>z \<noteq> 0\<close> const_of_int of_int_eq_0_iff
          mult_const_divide_mult_const_cancel_right
  )

lemma mult_const_of_int_divide_const_mult_of_int_cancel_left:
  "(of_int z * a) / (of_int z * b) = a / b" for a b :: 'b
  by (metis mult_const_of_int_divide_const_mult_of_int_cancel_right mult.commute)

end (* context nonzero int *)

context
  includes rat.lifting
begin

lift_definition const_of_rat :: "rat \<Rightarrow> 'b"
  is "\<lambda>x. of_int (fst x) / of_int (snd x)"
  unfolding ratrel_def
proof (clarify, unfold fst_conv snd_conv)
  fix a b c d :: int
  assume ratrel: "b \<noteq> 0" "d \<noteq> 0" "a * d = c * b"
  define oi :: "int \<Rightarrow> 'b" where "oi \<equiv> of_int"
  moreover from this ratrel(1,3) have "(oi a / oi b) * (oi d / oi d) = oi c / oi d"
    by (metis of_int_mult times_divide_eq_right divide_self_const_of_int mult_1_right mult.commute)
  ultimately show "oi a / oi b = oi c / oi d" using ratrel(2) by fastforce
qed

lemma inj_const_of_rat: "inj const_of_rat"
proof
  fix x y show "const_of_rat x = const_of_rat y \<Longrightarrow> x = y"
  proof (transfer, clarify, unfold ratrel_iff fst_conv snd_conv, clarify)
    fix a b c d :: int
    define oi :: "int \<Rightarrow> 'b" where "oi \<equiv> of_int"
    assume ratrel: "b \<noteq> 0" "d \<noteq> 0" "oi a / oi b = oi c / oi d"
    from oi_def ratrel(1,3) have "oi a * oi d = (oi d / oi d) * oi c * oi b"
      by (metis swap_numerator divide_self_const_of_int mult_1_right mult.assoc mult.commute)
    with oi_def ratrel(2) show "a * d = c * b" using of_int_eq_iff by fastforce
  qed
qed

lemma const_of_rat_rat: "const_of_rat (Rat.Fract a b) = (of_int a :: 'b) / of_int b"
  by transfer simp

lemma const_of_rat_0 [simp]: "const_of_rat 0 = 0"
  by transfer simp

lemma const_of_rat_1 [simp]: "const_of_rat 1 = 1"
  by transfer simp

lemma const_of_rat_minus: "const_of_rat (- a) = - const_of_rat a"
  by (transfer, simp add: minus_divide_left)

lemma const_of_rat_add: "const_of_rat (a + b) = const_of_rat a + const_of_rat b"
proof (transfer, clarify, unfold fst_conv snd_conv of_int_add of_int_mult)
  fix a b c d :: int
  assume b: "b \<noteq> 0" and d: "d \<noteq> 0"
  define w x y z :: 'b
    where "w \<equiv> of_int a" and "x \<equiv> of_int b"
    and   "y \<equiv> of_int c" and "z \<equiv> of_int d"
  from d z_def have "(w * z + y * x) / (x * z) = w / x + (y * x) / (x * z)"
    by (
      metis add_divide_distrib mult_const_of_int_divide_const_mult_of_int_cancel_right
    )
  with b x_def show "(w * z + y * x) / (x * z) = w / x + y / z"
    by (metis mult.commute mult_const_of_int_divide_const_mult_of_int_cancel_right)
qed

lemma const_of_rat_mult: "const_of_rat (a * b) = const_of_rat a * const_of_rat b"
  by (transfer, simp, metis times_divide_times_eq)

lemma const_of_rat_p_equal_0_iff: "p_equal p (const_of_rat a) 0 \<longleftrightarrow> a = 0"
  by (transfer fixing: p_equal p, simp, metis divide_equiv_0_iff const_of_int_p_equal_0_iff)

end (* context rat.lifting *)

lemma const_of_rat_eq_0_iff [simp]: "const_of_rat a = 0 \<longleftrightarrow> a = 0"
  using const_of_rat_p_equal_0_iff global_eq_iff by fastforce

lemma const_of_rat_neg_one [simp]: "const_of_rat (- 1) = -1"
  by (simp add: const_of_rat_minus)

lemma const_of_rat_diff: "const_of_rat (a - b) = const_of_rat a - const_of_rat b"
  using const_of_rat_add[of a "-b"] by (simp add: const_of_rat_minus)

lemma const_of_rat_sum: "const_of_rat (\<Sum>a\<in>A. f a) = (\<Sum>a\<in>A. const_of_rat (f a))"
  by (induct rule: infinite_finite_induct) (auto simp: const_of_rat_add)

lemma const_of_rat_prod: "const_of_rat (\<Prod>a\<in>A. f a) = (\<Prod>a\<in>A. const_of_rat (f a))"
  by (induct rule: infinite_finite_induct) (auto simp: const_of_rat_mult)

lemma const_of_rat_inverse: "const_of_rat (inverse a) = inverse (const_of_rat a)"
  by (cases "a = 0", simp, rule inverse_unique[symmetric], simp flip: const_of_rat_mult)

lemma left_inverse_const_of_rat[simp]:
  "inverse (const_of_rat a) * const_of_rat a = 1" if "a \<noteq> 0"
  by (metis that const_of_rat_inverse const_of_rat_mult Fields.left_inverse const_of_rat_1)

lemma right_inverse_const_of_rat[simp]:
  "const_of_rat a * inverse (const_of_rat a) = 1" if "a \<noteq> 0"
  by (metis that left_inverse_const_of_rat mult.commute)

lemma const_of_rat_divide: "const_of_rat (a / b) = const_of_rat a / const_of_rat b"
  by (metis Fields.divide_inverse const_of_rat_mult const_of_rat_inverse divide_inverse)

lemma divide_self_const_of_rat[simp]: "(const_of_rat a) / (const_of_rat a) = 1" if "a \<noteq> 0"
  by (metis that divide_inverse right_inverse_const_of_rat)

lemma const_of_rat_power: "const_of_rat (a ^ n) = (const_of_rat a) ^ n"
  by (induct n) (simp_all add: const_of_rat_mult)

lemma const_of_rat_eq_iff [simp]: "const_of_rat a = const_of_rat b \<longleftrightarrow> a = b"
  by (metis inj_const_of_rat inj_def)

lemma zero_eq_const_of_rat_iff [simp]: "0 = const_of_rat a \<longleftrightarrow> 0 = a"
  by simp

lemma const_of_rat_eq_1_iff [simp]: "const_of_rat a = 1 \<longleftrightarrow> a = 1"
  using const_of_rat_eq_iff [of _ 1] by simp

lemma one_eq_const_of_rat_iff [simp]: "1 = const_of_rat a \<longleftrightarrow> 1 = a"
  by simp

text \<open>Collapse nested embeddings.\<close>
lemma const_of_rat_of_nat_eq [simp]: "const_of_rat (of_nat n) = of_nat n"
  by (induct n) (simp_all add: const_of_rat_add)

lemma const_of_rat_of_int_eq [simp]: "const_of_rat (of_int z) = of_int z"
  by (cases z rule: int_diff_cases) (simp add: const_of_rat_diff)

text \<open>Product of all p-adic embeddings of the field of rationals.\<close>
definition range_const_of_rat :: "'b set" ("\<rat>\<^sub>\<forall>\<^sub>p")
  where "\<rat>\<^sub>\<forall>\<^sub>p = range const_of_rat"

lemma range_const_of_rat_cases [cases set: range_const_of_rat]:
  assumes "q \<in> \<rat>\<^sub>\<forall>\<^sub>p"
  obtains (const_of_rat) r where "q = const_of_rat r"
proof -
  from assms have "q \<in> range const_of_rat" by (simp only: range_const_of_rat_def)
  then obtain r where "q = const_of_rat r" ..
  then show thesis ..
qed

lemma range_const_of_rat_cases':
  assumes "x \<in> \<rat>\<^sub>\<forall>\<^sub>p"
  obtains a b where "b > 0" "coprime a b" "x = of_int a / of_int b"
proof -
  from assms obtain r where "x = const_of_rat r"
    by (auto simp: range_const_of_rat_def)
  obtain a b where quot: "quotient_of r = (a,b)" by force
  have "b > 0" using quotient_of_denom_pos[OF quot] .
  moreover have "coprime a b" using quotient_of_coprime[OF quot] .
  moreover have "x = of_int a / of_int b" unfolding \<open>x = const_of_rat r\<close>
      quotient_of_div[OF quot] by (simp add: const_of_rat_divide)
  ultimately show ?thesis using that by blast
qed

lemma range_const_of_rat_of_rat [simp]: "const_of_rat r \<in> \<rat>\<^sub>\<forall>\<^sub>p"
  by (simp add: range_const_of_rat_def)

lemma range_const_of_rat_of_int [simp]: "of_int z \<in> \<rat>\<^sub>\<forall>\<^sub>p"
  by (subst const_of_rat_of_int_eq [symmetric]) (rule range_const_of_rat_of_rat)

lemma Ints_subset_range_const_of_rat: "\<int> \<subseteq> \<rat>\<^sub>\<forall>\<^sub>p"
  using Ints_cases range_const_of_rat_of_int by blast

lemma range_const_of_rat_of_nat [simp]: "of_nat n \<in> \<rat>\<^sub>\<forall>\<^sub>p"
  by (subst const_of_rat_of_nat_eq [symmetric]) (rule range_const_of_rat_of_rat)

lemma Nats_subset_range_const_of_rat: "\<nat> \<subseteq> \<rat>\<^sub>\<forall>\<^sub>p"
  using Ints_subset_range_const_of_rat Nats_subset_Ints by blast

lemma range_const_of_rat_0 [simp]: "0 \<in> \<rat>\<^sub>\<forall>\<^sub>p"
  unfolding range_const_of_rat_def by (rule range_eqI, rule const_of_rat_0 [symmetric])

lemma range_const_of_rat_1 [simp]: "1 \<in> \<rat>\<^sub>\<forall>\<^sub>p"
  unfolding range_const_of_rat_def by (rule range_eqI, rule const_of_rat_1 [symmetric])

lemma range_const_of_rat_add [simp]:
  "a \<in> \<rat>\<^sub>\<forall>\<^sub>p \<Longrightarrow>
    b \<in> \<rat>\<^sub>\<forall>\<^sub>p \<Longrightarrow>
    a + b \<in> \<rat>\<^sub>\<forall>\<^sub>p"
  by (metis range_const_of_rat_cases range_const_of_rat_of_rat const_of_rat_add)

lemma range_const_of_rat_minus_iff [simp]:
  "- a \<in> \<rat>\<^sub>\<forall>\<^sub>p \<longleftrightarrow>
    a \<in> \<rat>\<^sub>\<forall>\<^sub>p"
  by (
    metis range_const_of_rat_cases range_const_of_rat_of_rat add.inverse_inverse
          const_of_rat_minus
  )

lemma range_const_of_rat_diff [simp]:
  "a \<in> \<rat>\<^sub>\<forall>\<^sub>p \<Longrightarrow>
    b \<in> \<rat>\<^sub>\<forall>\<^sub>p \<Longrightarrow>
    a - b \<in> \<rat>\<^sub>\<forall>\<^sub>p"
  by (metis range_const_of_rat_add range_const_of_rat_minus_iff diff_conv_add_uminus)

lemma range_const_of_rat_mult [simp]:
  "a \<in> \<rat>\<^sub>\<forall>\<^sub>p \<Longrightarrow>
    b \<in> \<rat>\<^sub>\<forall>\<^sub>p \<Longrightarrow>
    a * b \<in> \<rat>\<^sub>\<forall>\<^sub>p"
  by (metis range_const_of_rat_cases range_const_of_rat_of_rat const_of_rat_mult)

lemma range_const_of_rat_inverse [simp]:
  "a \<in> \<rat>\<^sub>\<forall>\<^sub>p \<Longrightarrow>
    inverse a \<in> \<rat>\<^sub>\<forall>\<^sub>p"
  by (metis range_const_of_rat_cases range_const_of_rat_of_rat const_of_rat_inverse)

lemma range_const_of_rat_divide [simp]:
  "a \<in> \<rat>\<^sub>\<forall>\<^sub>p \<Longrightarrow>
    b \<in> \<rat>\<^sub>\<forall>\<^sub>p \<Longrightarrow>
    a / b \<in> \<rat>\<^sub>\<forall>\<^sub>p"
  by (simp add: divide_inverse)

lemma range_const_of_rat_power [simp]:
  "a \<in> \<rat>\<^sub>\<forall>\<^sub>p \<Longrightarrow>
    a ^ n \<in> \<rat>\<^sub>\<forall>\<^sub>p"
  by (metis range_const_of_rat_cases range_const_of_rat_of_rat const_of_rat_power)

lemma range_const_of_rat_sum [intro]:
  "(\<And>x. x \<in> A \<Longrightarrow> f x \<in> \<rat>\<^sub>\<forall>\<^sub>p) \<Longrightarrow>
    sum f A \<in> \<rat>\<^sub>\<forall>\<^sub>p"
  by (induction A rule: infinite_finite_induct) auto

lemma range_const_of_rat_prod [intro]:
  "(\<And>x. x \<in> A \<Longrightarrow> f x \<in> \<rat>\<^sub>\<forall>\<^sub>p)
    \<Longrightarrow> prod f A \<in> \<rat>\<^sub>\<forall>\<^sub>p"
  by (induction A rule: infinite_finite_induct) auto

lemma range_const_of_rat_induct [case_names const_of_rat, induct set: range_const_of_rat]:
  "q \<in> \<rat>\<^sub>\<forall>\<^sub>p \<Longrightarrow>
    (\<And>r. P (const_of_rat r)) \<Longrightarrow> P q"
  by (rule range_const_of_rat_cases) auto

lemma p_adic_Rats_p_equal_0_iff:
  "a \<in> \<rat>\<^sub>\<forall>\<^sub>p \<Longrightarrow>
    p_equal p a 0 \<longleftrightarrow> a = 0"
  by (induct a rule: range_const_of_rat_induct, simp, rule const_of_rat_p_equal_0_iff)

lemma range_const_of_rat_infinite: "\<not> finite \<rat>\<^sub>\<forall>\<^sub>p"
  by (auto dest!: finite_imageD simp: inj_on_def infinite_UNIV_char_0 range_const_of_rat_def)

lemma left_inverse_range_const_of_rat:
  "a \<in> \<rat>\<^sub>\<forall>\<^sub>p \<Longrightarrow> a \<noteq> 0 \<Longrightarrow>
    inverse a * a = 1"
  by (
    induct a rule: range_const_of_rat_induct, rule left_inverse_const_of_rat,
    simp add: const_of_rat_p_equal_0_iff
  )

lemma right_inverse_range_const_of_rat:
  "a \<in> \<rat>\<^sub>\<forall>\<^sub>p \<Longrightarrow> a \<noteq> 0 \<Longrightarrow>
    a * inverse a = 1"
  by (metis left_inverse_range_const_of_rat mult.commute)

lemma divide_self_range_const_of_rat:
  "a \<in> \<rat>\<^sub>\<forall>\<^sub>p \<Longrightarrow> a \<noteq> 0 \<Longrightarrow>
    a / a = 1"
  by (metis divide_inverse right_inverse_range_const_of_rat)

lemma range_const_of_rat_add_iff:
  "a \<in> \<rat>\<^sub>\<forall>\<^sub>p \<or>
    b \<in> \<rat>\<^sub>\<forall>\<^sub>p \<Longrightarrow>
    a + b \<in> \<rat>\<^sub>\<forall>\<^sub>p \<longleftrightarrow>
      a \<in> \<rat>\<^sub>\<forall>\<^sub>p \<and> b \<in> \<rat>\<^sub>\<forall>\<^sub>p"
  by (metis range_const_of_rat_add range_const_of_rat_diff add_diff_cancel add_diff_cancel_left')

lemma range_const_of_rat_diff_iff:
  "a \<in> \<rat>\<^sub>\<forall>\<^sub>p \<or>
    b \<in> \<rat>\<^sub>\<forall>\<^sub>p \<Longrightarrow>
      a - b \<in> \<rat>\<^sub>\<forall>\<^sub>p \<longleftrightarrow>
      a \<in> \<rat>\<^sub>\<forall>\<^sub>p \<and> b \<in> \<rat>\<^sub>\<forall>\<^sub>p"
  by (metis range_const_of_rat_add_iff diff_add_cancel)

lemma range_const_of_rat_mult_iff:
  "a * b \<in> \<rat>\<^sub>\<forall>\<^sub>p \<longleftrightarrow>
    a \<in> \<rat>\<^sub>\<forall>\<^sub>p \<and> b \<in> \<rat>\<^sub>\<forall>\<^sub>p"
  if
    "a \<in> \<rat>\<^sub>\<forall>\<^sub>p - {0} \<or>
      b \<in> \<rat>\<^sub>\<forall>\<^sub>p - {0}"
proof-
  have *:
    "\<And>a b :: 'b.
      a \<in> \<rat>\<^sub>\<forall>\<^sub>p - {0} \<Longrightarrow>
      a * b \<in> \<rat>\<^sub>\<forall>\<^sub>p \<longleftrightarrow>
        b \<in> \<rat>\<^sub>\<forall>\<^sub>p"
  proof
    fix a b :: 'b
    assume  "a \<in> \<rat>\<^sub>\<forall>\<^sub>p - {0}"
      and   "a * b \<in> \<rat>\<^sub>\<forall>\<^sub>p"
    thus "b \<in> \<rat>\<^sub>\<forall>\<^sub>p"
      using range_const_of_rat_mult[of "inverse a"] left_inverse_range_const_of_rat[of a]
      by    (fastforce simp flip: mult.assoc)
  qed simp
  show ?thesis
  proof (cases "a \<in> \<rat>\<^sub>\<forall>\<^sub>p - {0}")
    case True thus ?thesis using *[of a b] by fast
  next
    case False
    with that have "b \<in> \<rat>\<^sub>\<forall>\<^sub>p - {0}" by blast
    moreover from this have
      "a * b \<in> \<rat>\<^sub>\<forall>\<^sub>p \<longleftrightarrow>
        a \<in> \<rat>\<^sub>\<forall>\<^sub>p"
      by (metis * mult.commute)
    ultimately show ?thesis by blast
  qed
qed

lemma range_const_of_rat_inverse_iff [simp]:
  "inverse a \<in> \<rat>\<^sub>\<forall>\<^sub>p \<longleftrightarrow>
    a \<in> \<rat>\<^sub>\<forall>\<^sub>p"
  by (metis range_const_of_rat_inverse inverse_inverse)

lemma range_const_of_rat_divide_iff:
  "a / b \<in> \<rat>\<^sub>\<forall>\<^sub>p \<longleftrightarrow>
      a \<in> \<rat>\<^sub>\<forall>\<^sub>p \<and> b \<in> \<rat>\<^sub>\<forall>\<^sub>p"
  if
    "a \<in> \<rat>\<^sub>\<forall>\<^sub>p - {0} \<or>
      b \<in> \<rat>\<^sub>\<forall>\<^sub>p - {0}"
  using that range_const_of_rat_inverse inverse_inverse[of b] range_const_of_rat_inverse_iff
        divide_inverse[of a b] range_const_of_rat_mult_iff[of a "inverse b"]
  by    force

end (* locale global_p_equal_div_inv_w_inj_consts_char_0 *)

lemma Fract_eq0_iff: "Fraction_Field.Fract a b = 0 \<longleftrightarrow> a = 0 \<or> b = 0"
  by transfer simp

locale global_p_equal_div_inv_w_inj_idom_consts =
  global_p_equal_div_inv_w_inj_consts p_equal p_restrict func_of_consts
+ global_p_equality_w_inj_consts p_equal p_restrict func_of_consts
  for p_equal        ::
    "'a \<Rightarrow> 'b::{comm_ring_1, inverse, divide_trivial} \<Rightarrow>
      'b \<Rightarrow> bool"
  and p_restrict     :: "'b \<Rightarrow> ('a \<Rightarrow> bool) \<Rightarrow> 'b"
  and func_of_consts :: "('a \<Rightarrow> 'c::idom) \<Rightarrow> 'b"
begin

lift_definition const_of_fract :: "'c fract \<Rightarrow> 'b"
  is "\<lambda>x::'c \<times> 'c. const (fst x) / const (snd x)"
proof (clarify, unfold fractrel_iff fst_conv snd_conv, clarify)
  fix a b c d :: 'c
  assume fractrel: "b \<noteq> 0" "d \<noteq> 0" "a * d = c * b"
  from fractrel(1,3) have "(const a / const b) * (const d / const d) = const c / const d"
    by (metis const_mult times_divide_eq_right const_divide_self mult_1_right swap_numerator)
  with fractrel(2) show "const a / const b = const c / const d"
    using const_divide_self by fastforce
qed

lemma inj_const_of_fract: "inj const_of_fract"
proof
  fix x y show "const_of_fract x = const_of_fract y \<Longrightarrow> x = y"
  proof (transfer, clarify, unfold fractrel_iff fst_conv snd_conv, clarify)
    fix a b c d :: 'c
    assume fractrel: "b \<noteq> 0" "d \<noteq> 0" "const a / const b = const c / const d"
    from fractrel(1,3) have "const d * const a = const d * (const c / const d * const b)"
      by (metis swap_numerator const_divide_self mult_1_right)
    with fractrel(2) have "d * a = c * b"
      by (metis mult.assoc swap_numerator const_divide_self mult_1_left const_mult const_eq_iff)
    thus "a * d = c * b" by algebra
  qed
qed

lemma const_of_fract_0 [simp]: "const_of_fract 0 = 0"
  by transfer simp

lemma const_of_fract_1 [simp]: "const_of_fract 1 = 1"
  by transfer simp

lemma const_of_fract_Fract: "const_of_fract (Fraction_Field.Fract a b) = const a / const b"
  by transfer simp

lemma const_of_fract_p_eq_0_iff [simp]: "p_equal p (const_of_fract x) 0 \<longleftrightarrow> x = 0"
  by  (cases x)
      (simp add: const_of_fract_Fract divide_equiv_0_iff p_equal_func_of_const_0 Fract_eq0_iff)

lemma const_of_fract_equal_0_iff [simp]: "const_of_fract x = 0 \<longleftrightarrow> x = 0"
  by (simp flip: global_eq_iff)

lemma const_of_fract_minus: "const_of_fract (- a) = - const_of_fract a"
  by (transfer, simp add: minus_divide_left fun_Compl_def)

lemma const_of_fract_add: "const_of_fract (a + b) = const_of_fract a + const_of_fract b"
  by (
    transfer, clarify,
    simp add: add_divide_distrib mult_const_divide_mult_const_cancel_right
              mult_const_divide_mult_const_cancel_right_left
  )

lemma const_of_fract_mult: "const_of_fract (a * b) = const_of_fract a * const_of_fract b"
  by (transfer, simp add: times_divide_times_eq)

lemma const_of_fract_neg_one [simp]: "const_of_fract (- 1) = -1"
  by (simp add: const_of_fract_minus)

lemma const_of_fract_diff: "const_of_fract (a - b) = const_of_fract a - const_of_fract b"
  using const_of_fract_add[of a "-b"] by (simp add: const_of_fract_minus)

lemma const_of_fract_sum:
  "const_of_fract (\<Sum>a\<in>A. f a) = (\<Sum>a\<in>A. const_of_fract (f a))"
  by (induct rule: infinite_finite_induct) (auto simp: const_of_fract_add)

lemma const_of_fract_prod:
  "const_of_fract (\<Prod>a\<in>A. f a) = (\<Prod>a\<in>A. const_of_fract (f a))"
  by (induct rule: infinite_finite_induct) (auto simp: const_of_fract_mult)

lemma const_of_fract_inverse: "const_of_fract (inverse a) = inverse (const_of_fract a)"
  by (cases "a = 0", simp, rule inverse_unique[symmetric], simp flip: const_of_fract_mult)

lemma left_inverse_const_of_fract[simp]:
  "inverse (const_of_fract a) * const_of_fract a = 1" if "a \<noteq> 0"
  by (metis that const_of_fract_inverse const_of_fract_mult Fields.left_inverse const_of_fract_1)

lemma right_inverse_const_of_fract[simp]:
  "(const_of_fract a) * inverse (const_of_fract a) = 1" if "a \<noteq> 0"
  by (metis that left_inverse_const_of_fract mult.commute)

lemma const_of_fract_divide: "const_of_fract (a / b) = const_of_fract a / const_of_fract b"
  by (metis divide_inverse const_of_fract_mult const_of_fract_inverse Fields.divide_inverse)

lemma p_adic_prod_divide_self_of_fract[simp]:
  "(const_of_fract a) / (const_of_fract a) = 1" if "a \<noteq> 0"
  by (metis that divide_inverse right_inverse_const_of_fract)

lemma const_of_fract_power: "const_of_fract (a ^ n) = (const_of_fract a) ^ n"
  by (induct n) (simp_all add: const_of_fract_mult)

lemma const_of_fract_eq_iff [simp]:
  "const_of_fract a = const_of_fract b \<longleftrightarrow> a = b"
  by (metis inj_const_of_fract inj_def)

lemma zero_eq_const_of_fract_iff [simp]: "0 = const_of_fract a \<longleftrightarrow> 0 = a"
  by simp

lemma const_of_fract_eq_1_iff [simp]: "const_of_fract a = 1 \<longleftrightarrow> a = 1"
  using const_of_fract_eq_iff [of _ 1] by simp

lemma one_eq_const_of_fract_iff [simp]: "1 = const_of_fract a \<longleftrightarrow> 1 = a"
  by simp

text \<open>Collapse nested embeddings.\<close>
lemma const_of_fract_numer_eq_const [simp]: "const_of_fract (Fraction_Field.Fract a 1) = const a"
  by (metis const_of_fract_Fract const_1 div_by_1)

lemma const_of_fract_of_nat_eq [simp]: "const_of_fract (of_nat n) = of_nat n"
  by (induct n) (simp_all add: const_of_fract_add)

lemma const_of_fract_of_int_eq [simp]: "const_of_fract (of_int z) = of_int z"
  by (cases z rule: int_diff_cases) (simp add: const_of_fract_diff)

text \<open>Product of all p-adic embeddings of the field of fractions of the base ring.\<close>
definition range_const_of_fract :: "'b set" ("\<Q>\<^sub>\<forall>\<^sub>p")
  where "\<Q>\<^sub>\<forall>\<^sub>p = range const_of_fract"

lemma range_const_of_fract_cases [cases set: range_const_of_fract]:
  assumes "q \<in> \<Q>\<^sub>\<forall>\<^sub>p"
  obtains (const_of_fract) r where "q = const_of_fract r"
proof -
  from assms have "q \<in> range const_of_fract" by (simp only: range_const_of_fract_def)
  then obtain r where "q = const_of_fract r" ..
  then show thesis ..
qed

lemma range_const_of_fract_cases':
  assumes "x \<in> \<Q>\<^sub>\<forall>\<^sub>p"
  obtains a b where "b \<noteq> 0" "x = const a / const b"
proof -
  from assms obtain r where "x = const_of_fract r" by (auto simp: range_const_of_fract_def)
  moreover obtain a b where Fract: "b \<noteq> 0" "r = Fraction_Field.Fract a b"
    using Fract_cases by meson
  ultimately have "x = const a / const b" using const_of_fract_Fract by blast
  with that Fract(1) show thesis by fast
qed

lemma range_const_of_fract_of_fract [simp]:
  "const_of_fract r \<in> \<Q>\<^sub>\<forall>\<^sub>p"
  by (simp add: range_const_of_fract_def)

lemma range_const_of_fract_const [simp]: "const a \<in> \<Q>\<^sub>\<forall>\<^sub>p"
  unfolding range_const_of_fract_def
  by        (standard, rule const_of_fract_numer_eq_const[symmetric], simp)

lemma range_const_of_fract_of_int [simp]: "of_int z \<in> \<Q>\<^sub>\<forall>\<^sub>p"
  by (subst const_of_fract_of_int_eq [symmetric]) (rule range_const_of_fract_of_fract)

lemma Ints_subset_range_const_of_fract: "\<int> \<subseteq> \<Q>\<^sub>\<forall>\<^sub>p"
  using Ints_cases range_const_of_fract_of_int by blast

lemma range_const_of_fract_of_nat [simp]: "of_nat n \<in> \<Q>\<^sub>\<forall>\<^sub>p"
  by (subst const_of_fract_of_nat_eq [symmetric]) (rule range_const_of_fract_of_fract)

lemma Nats_subset_range_const_of_fract: "\<nat> \<subseteq> \<Q>\<^sub>\<forall>\<^sub>p"
  using Ints_subset_range_const_of_fract Nats_subset_Ints by blast

lemma range_const_of_fract_0 [simp]: "0 \<in> \<Q>\<^sub>\<forall>\<^sub>p"
  unfolding range_const_of_fract_def by (rule range_eqI, rule const_of_fract_0 [symmetric])

lemma range_const_of_fract_1 [simp]: "1 \<in> \<Q>\<^sub>\<forall>\<^sub>p"
  unfolding range_const_of_fract_def by (rule range_eqI, rule const_of_fract_1 [symmetric])

lemma range_const_of_fract_add [simp]:
  "a \<in> \<Q>\<^sub>\<forall>\<^sub>p \<Longrightarrow>
    b \<in> \<Q>\<^sub>\<forall>\<^sub>p \<Longrightarrow>
    a + b \<in> \<Q>\<^sub>\<forall>\<^sub>p"
  by (metis range_const_of_fract_cases range_const_of_fract_of_fract const_of_fract_add)

lemma range_const_of_fract_minus_iff [simp]:
  "- a \<in> \<Q>\<^sub>\<forall>\<^sub>p \<longleftrightarrow>
    a \<in> \<Q>\<^sub>\<forall>\<^sub>p"
  by (
    metis range_const_of_fract_cases range_const_of_fract_of_fract add.inverse_inverse
          const_of_fract_minus
  )

lemma range_const_of_fract_diff [simp]:
  "a \<in> \<Q>\<^sub>\<forall>\<^sub>p \<Longrightarrow>
    b \<in> \<Q>\<^sub>\<forall>\<^sub>p \<Longrightarrow>
    a - b \<in> \<Q>\<^sub>\<forall>\<^sub>p"
  by (metis range_const_of_fract_add range_const_of_fract_minus_iff diff_conv_add_uminus)

lemma range_const_of_fract_mult [simp]:
  "a \<in> \<Q>\<^sub>\<forall>\<^sub>p \<Longrightarrow>
    b \<in> \<Q>\<^sub>\<forall>\<^sub>p \<Longrightarrow>
    a * b \<in> \<Q>\<^sub>\<forall>\<^sub>p"
  by (metis range_const_of_fract_cases range_const_of_fract_of_fract const_of_fract_mult)

lemma range_const_of_fract_inverse [simp]:
  "a \<in> \<Q>\<^sub>\<forall>\<^sub>p \<Longrightarrow>
    inverse a \<in> \<Q>\<^sub>\<forall>\<^sub>p"
  by (metis range_const_of_fract_cases range_const_of_fract_of_fract const_of_fract_inverse)

lemma range_const_of_fract_divide [simp]:
  "a \<in> \<Q>\<^sub>\<forall>\<^sub>p \<Longrightarrow>
    b \<in> \<Q>\<^sub>\<forall>\<^sub>p \<Longrightarrow>
    a / b \<in> \<Q>\<^sub>\<forall>\<^sub>p"
  by (simp add: divide_inverse)

lemma range_const_of_fract_power [simp]:
  "a \<in> \<Q>\<^sub>\<forall>\<^sub>p \<Longrightarrow>
    a ^ n \<in> \<Q>\<^sub>\<forall>\<^sub>p"
  by (metis range_const_of_fract_cases range_const_of_fract_of_fract const_of_fract_power)

lemma range_const_of_fract_sum [intro]:
  "(\<And>x. x \<in> A \<Longrightarrow>
    f x \<in> \<Q>\<^sub>\<forall>\<^sub>p) \<Longrightarrow>
    sum f A \<in> \<Q>\<^sub>\<forall>\<^sub>p"
  by (induction A rule: infinite_finite_induct) auto

lemma range_const_of_fract [intro]:
  "(\<And>x. x \<in> A \<Longrightarrow> f x \<in> \<Q>\<^sub>\<forall>\<^sub>p)
    \<Longrightarrow> prod f A \<in> \<Q>\<^sub>\<forall>\<^sub>p"
  by (induction A rule: infinite_finite_induct) auto

lemma range_const_of_fract_induct [case_names const_of_fract, induct set: range_const_of_fract]:
  "q \<in> \<Q>\<^sub>\<forall>\<^sub>p \<Longrightarrow>
    (\<And>r. P (const_of_fract r)) \<Longrightarrow> P q"
  by (rule range_const_of_fract_cases) auto

lemma p_adic_Fracts_p_equal_0_iff:
  "a \<in> \<Q>\<^sub>\<forall>\<^sub>p \<Longrightarrow>
    p_equal p a 0 \<longleftrightarrow> a = 0"
  by (induct a rule: range_const_of_fract_induct, simp)

lemma range_const_of_fract_infinite:
  "infinite \<Q>\<^sub>\<forall>\<^sub>p" if "infinite (UNIV :: 'c set)"
  using that finite_imageD[OF _ inj_const] range_const_of_fract_const
        finite_subset[of "range const"]
  by    blast

lemma left_inverse_range_const_of_fract:
  "a \<in> \<Q>\<^sub>\<forall>\<^sub>p \<Longrightarrow> a \<noteq> 0 \<Longrightarrow>
    inverse a * a = 1"
  by (induct a rule: range_const_of_fract_induct, rule left_inverse_const_of_fract, simp)

lemma right_inverse_range_const_of_fract:
  "a \<in> \<Q>\<^sub>\<forall>\<^sub>p \<Longrightarrow> a \<noteq> 0 \<Longrightarrow>
    a * inverse a = 1"
  by (metis left_inverse_range_const_of_fract mult.commute)

lemma divide_self_range_const_of_fract:
  "a \<in> \<Q>\<^sub>\<forall>\<^sub>p \<Longrightarrow> a \<noteq> 0 \<Longrightarrow>
    a / a = 1"
  by (metis divide_inverse right_inverse_range_const_of_fract)

lemma range_const_of_fract_add_iff:
  "a \<in> \<Q>\<^sub>\<forall>\<^sub>p \<or>
    b \<in> \<Q>\<^sub>\<forall>\<^sub>p \<Longrightarrow>
    a + b \<in> \<Q>\<^sub>\<forall>\<^sub>p \<longleftrightarrow>
      a \<in> \<Q>\<^sub>\<forall>\<^sub>p \<and> b \<in> \<Q>\<^sub>\<forall>\<^sub>p"
  using range_const_of_fract_add range_const_of_fract_diff add_diff_cancel add_diff_cancel_left'
  by    metis

lemma range_const_of_fract_diff_iff:
  "a \<in> \<Q>\<^sub>\<forall>\<^sub>p \<or>
    b \<in> \<Q>\<^sub>\<forall>\<^sub>p \<Longrightarrow>
      a - b \<in> \<Q>\<^sub>\<forall>\<^sub>p \<longleftrightarrow>
      a \<in> \<Q>\<^sub>\<forall>\<^sub>p \<and> b \<in> \<Q>\<^sub>\<forall>\<^sub>p"
  by (metis range_const_of_fract_add_iff diff_add_cancel)

lemma range_const_of_fract_mult_iff:
  "a * b \<in> \<Q>\<^sub>\<forall>\<^sub>p \<longleftrightarrow>
    a \<in> \<Q>\<^sub>\<forall>\<^sub>p \<and> b \<in> \<Q>\<^sub>\<forall>\<^sub>p"
  if
    "a \<in> \<Q>\<^sub>\<forall>\<^sub>p - {0} \<or>
      b \<in> \<Q>\<^sub>\<forall>\<^sub>p - {0}"
proof-
  have *:
    "\<And>a b :: 'b.
      a \<in> \<Q>\<^sub>\<forall>\<^sub>p - {0} \<Longrightarrow>
      a * b \<in> \<Q>\<^sub>\<forall>\<^sub>p \<longleftrightarrow>
        b \<in> \<Q>\<^sub>\<forall>\<^sub>p"
  proof
    fix a b :: 'b
    assume  "a \<in> \<Q>\<^sub>\<forall>\<^sub>p - {0}"
      and   "a * b \<in> \<Q>\<^sub>\<forall>\<^sub>p"
    thus "b \<in> \<Q>\<^sub>\<forall>\<^sub>p"
      using range_const_of_fract_mult[of "inverse a"] left_inverse_range_const_of_fract[of a]
      by    (fastforce simp flip: mult.assoc)
  qed simp
  show ?thesis
  proof (cases "a \<in> \<Q>\<^sub>\<forall>\<^sub>p - {0}")
    case True thus ?thesis using *[of a b] by fast
  next
    case False
    with that have "b \<in> \<Q>\<^sub>\<forall>\<^sub>p - {0}" by blast
    moreover from this have
      "a * b \<in> \<Q>\<^sub>\<forall>\<^sub>p \<longleftrightarrow>
        a \<in> \<Q>\<^sub>\<forall>\<^sub>p"
      by (metis * mult.commute)
    ultimately show ?thesis by blast
  qed
qed

lemma range_const_of_fract_inverse_iff [simp]:
  "inverse a \<in> \<Q>\<^sub>\<forall>\<^sub>p \<longleftrightarrow>
    a \<in> \<Q>\<^sub>\<forall>\<^sub>p"
  by (metis range_const_of_fract_inverse inverse_inverse)

lemma range_const_of_fract_divide_iff:
  "a / b \<in> \<Q>\<^sub>\<forall>\<^sub>p \<longleftrightarrow>
      a \<in> \<Q>\<^sub>\<forall>\<^sub>p \<and> b \<in> \<Q>\<^sub>\<forall>\<^sub>p"
  if
    "a \<in> \<Q>\<^sub>\<forall>\<^sub>p - {0} \<or>
      b \<in> \<Q>\<^sub>\<forall>\<^sub>p - {0}"
  using that range_const_of_fract_inverse inverse_inverse[of b]
        range_const_of_fract_inverse_iff divide_inverse[of a b]
        range_const_of_fract_mult_iff[of a "inverse b"]
  by    force

end (* locale global_p_equal_div_inv_w_idom_consts *)

locale global_p_equality_w_inj_index_consts = global_p_equality_w_inj_consts
+
  fixes index_inj :: "'a \<Rightarrow> 'c"
  assumes index_inj  : "inj index_inj"
  and index_inj_nzero: "index_inj p \<noteq> 0"
begin

abbreviation "global_uniformizer \<equiv> consts index_inj"
abbreviation "index_const p \<equiv> const (index_inj p)"

lemma global_uniformizer_locally_uniformizes: "p_equal p global_uniformizer (index_const p)"
  using p_equal_func_of_consts by auto

lemma index_const_globally_nequiv_0: "\<not> p_equal q (index_const p) 0"
  using p_equal_func_of_consts_0 index_inj_nzero by fast

lemma global_uniformizer_globally_nequiv_0: "\<not> p_equal p global_uniformizer 0"
  using p_equal_func_of_consts_0 index_inj_nzero by simp

end (* locale global_p_equality_w_inj_index_consts *)

locale global_p_equality_no_zero_divisors_1_w_inj_index_consts =
  global_p_equality_w_inj_index_consts + p_equality_no_zero_divisors_1
begin

lemma index_const_pow_globally_nequiv_0: "\<not> p_equal q (index_const p ^ n) 0"
  using index_const_globally_nequiv_0 pow_equiv_0_iff by fast

lemma global_uniformizer_pow_globally_nequiv_0: "\<not> p_equal q (global_uniformizer ^ n) 0"
  using global_uniformizer_globally_nequiv_0 pow_equiv_0_iff by blast

end

locale global_p_equality_depth_w_inj_index_consts =
  p_equality_depth p_equal p_depth
+ global_p_equality_w_inj_index_consts p_equal p_restrict func_of_consts index_inj
  for p_equal        :: "'a \<Rightarrow> 'b::comm_ring_1 \<Rightarrow> 'b \<Rightarrow> bool"
  and p_restrict     :: "'b \<Rightarrow> ('a \<Rightarrow> bool) \<Rightarrow> 'b"
  and p_depth        :: "'a \<Rightarrow> 'b \<Rightarrow> int"
  and func_of_consts :: "('a \<Rightarrow> 'c::{factorial_semiring,ring_1}) \<Rightarrow> 'b"
  and index_inj      :: "'a \<Rightarrow> 'c"
+
  assumes p_depth_func_of_consts:
    "p_depth p (func_of_consts f) = int (multiplicity (index_inj p) (f p))"
  and index_inj_nunit  : "\<not> is_unit (index_inj p)"
  and index_inj_coprime:
    "p \<noteq> q \<Longrightarrow> multiplicity (index_inj p) (index_inj q) = 0"
begin

lemma p_depth_set_consts: "func_of_consts f \<in> p_depth_set p 0"
  using p_depth_func_of_consts p_depth_setI by simp

lemma global_depth_set_consts: "func_of_consts f \<in> global_depth_set 0"
  using p_depth_set_consts global_depth_set by blast

lemma p_depth_1[simp]: "p_depth p (1::'b) = 0"
  using p_depth_func_of_consts[of p 1] by simp

lemma p_depth_index_const: "p_depth p (index_const p) = 1"
  using p_depth_func_of_consts index_inj_nzero index_inj_nunit multiplicity_self by fastforce

lemma p_depth_index_const': "p_depth q (index_const p) = of_bool (q = p)"
  by (cases "q = p", simp_all add: p_depth_index_const p_depth_func_of_consts index_inj_coprime)

lemma p_depth_global_uniformizer: "p_depth p (global_uniformizer::'b) = 1"
  using p_depth_func_of_consts index_inj_nzero index_inj_nunit multiplicity_self by fastforce

lemma p_depth_consts_func_ge0: "p_depth p (consts f) \<ge> 0"
  using p_depth_func_of_consts by fastforce

end (* locale global_p_equality_depth_w_inj_index_consts *)


locale global_p_equal_depth_no_zero_divisors_w_inj_index_consts =
  global_p_equal p_equal p_restrict
+ global_p_equality_depth_no_zero_divisors_1 p_equal p_restrict p_depth
+ global_p_equality_depth_w_inj_index_consts p_equal p_restrict p_depth func_of_consts index_inj
  for p_equal        :: "'a \<Rightarrow> 'b::comm_ring_1 \<Rightarrow> 'b \<Rightarrow> bool"
  and p_restrict     :: "'b \<Rightarrow> ('a \<Rightarrow> bool) \<Rightarrow> 'b"
  and p_depth        :: "'a \<Rightarrow> 'b \<Rightarrow> int"
  and func_of_consts :: "('a \<Rightarrow> 'c::{factorial_semiring,ring_1}) \<Rightarrow> 'b"
  and index_inj      :: "'a \<Rightarrow> 'c"
begin

sublocale global_p_equal_w_inj_consts ..
sublocale global_p_equal_depth_no_zero_divisors ..

lemma p_depth_index_const_pow: "p_depth p ((index_const p) ^ n) = int n"
  using p_depth_index_const depth_pow_additive by auto

lemma p_depth_index_const_pow': "p_depth q ((index_const p) ^ n) = int n * of_bool (q = p)"
  using p_depth_index_const' depth_pow_additive by fastforce

lemma p_depth_global_uniformizer_pow: "p_depth p (global_uniformizer ^ n) = int n"
  using p_depth_global_uniformizer depth_pow_additive by auto

end

locale global_p_equal_depth_div_inv_w_inj_index_consts =
  global_p_equal_depth_div_inv p_equal p_depth p_restrict
+ global_p_equal_depth_no_zero_divisors_w_inj_index_consts
    p_equal p_restrict p_depth func_of_consts index_inj
  for p_equal        ::
    "'a \<Rightarrow> 'b::{comm_ring_1, inverse, divide_trivial} \<Rightarrow>
      'b \<Rightarrow> bool"
  and p_depth        :: "'a \<Rightarrow> 'b \<Rightarrow> int"
  and p_restrict     :: "'b \<Rightarrow> ('a \<Rightarrow> bool) \<Rightarrow> 'b"
  and func_of_consts :: "('a \<Rightarrow> 'c::{factorial_semiring,ring_1}) \<Rightarrow> 'b"
  and index_inj      :: "'a \<Rightarrow> 'c"
begin

lemma index_const_powi_globally_nequiv_0: "\<not> p_equal q (index_const p powi n) 0"
  using index_const_globally_nequiv_0 power_int_equiv_0_iff by simp

lemma global_uniformizer_powi_globally_nequiv_0: "\<not> p_equal q (global_uniformizer powi n) 0"
  using global_uniformizer_globally_nequiv_0 power_int_equiv_0_iff by blast

lemma index_const_powi_add:
  "(index_const p) powi (m + n) = (index_const p) powi m * (index_const p) powi n"
  using power_int_add index_const_globally_nequiv_0 by blast

lemma global_uniformizer_powi_add:
  "global_uniformizer powi (m + n) = global_uniformizer powi m * global_uniformizer powi n"
  using power_int_add global_uniformizer_globally_nequiv_0 by blast

lemma p_depth_index_const_powi: "p_depth p (index_const p powi n) = n"
  by  (cases "n \<ge> 0")
      (simp_all add: power_int_def p_depth_index_const_pow inverse_depth flip: inverse_pow)

lemma p_depth_index_const_powi': "p_depth q (index_const p powi n) = n * of_bool (q = p)"
  by (
    cases "q = p", simp add: p_depth_index_const_powi, cases "n \<ge> 0",
    simp_all add: power_int_def p_depth_index_const_pow' inverse_depth flip: inverse_pow
  )

lemma p_depth_global_uniformizer_powi: "p_depth p (global_uniformizer powi n) = n"
  by (
    cases "n \<ge> 0",
    simp_all add: power_int_def p_depth_global_uniformizer_pow inverse_depth flip: inverse_pow
  )

lemma local_uniformizer_locally_uniformizes:
  "p_depth p ((index_const p) powi (-n) * x) = 0" if "p_depth p x = n"
  using that depth_equiv_0 mult_0_right index_const_powi_globally_nequiv_0 no_zero_divisors
        depth_mult_additive p_depth_index_const_powi
  by    (cases "p_equal p x 0") auto

lemma global_uniformizer_locally_uniformizes:
  "p_depth p (global_uniformizer powi (-n) * x) = 0" if "p_depth p x = n"
  using that depth_equiv_0 mult_0_right global_uniformizer_powi_globally_nequiv_0 no_zero_divisors
        depth_mult_additive p_depth_global_uniformizer_powi
  by    (cases "p_equal p x 0") auto

lemma p_depth_set_eq_index_const_coset:
  "p_depth_set p n = ((index_const p) powi n) *o (p_depth_set p 0)"
  using p_depth_set_eq_coset p_depth_index_const index_const_globally_nequiv_0 by blast

lemma p_depth_set_eq_index_const_coset':
  "p_depth_set p 0 = ((index_const p) powi (-n)) *o (p_depth_set p n)"
  using p_depth_set_eq_coset' p_depth_index_const index_const_globally_nequiv_0 by blast

lemma p_depth_set_eq_global_uniformizer_coset:
  "p_depth_set p n = (global_uniformizer powi n) *o (p_depth_set p 0)"
  using p_depth_set_eq_coset p_depth_global_uniformizer global_uniformizer_globally_nequiv_0
  by    blast

lemma p_depth_set_eq_global_uniformizer_coset':
  "p_depth_set p 0 = (global_uniformizer powi (-n)) *o (p_depth_set p n)"
  using p_depth_set_eq_coset' p_depth_global_uniformizer global_uniformizer_globally_nequiv_0
  by    blast

lemma global_depth_set_eq_global_uniformizer_coset:
  "global_depth_set n = (global_uniformizer powi n) *o (global_depth_set 0)"
  using global_depth_set_eq_coset p_depth_global_uniformizer by simp

lemma global_depth_set_eq_global_uniformizer_coset':
  "global_depth_set 0 = (global_uniformizer powi (-n)) *o (global_depth_set n)"
  using global_depth_set_eq_coset' p_depth_global_uniformizer by simp

definition shift_p_depth :: "'a \<Rightarrow> int \<Rightarrow> 'b \<Rightarrow> 'b"
  where "shift_p_depth p n x = x * (consts (\<lambda>q. if q = p then index_inj p else 1)) powi n"

lemma shift_p_depth_0[simp]: "shift_p_depth p n 0 = 0"
  by (simp add: shift_p_depth_def)

lemma shift_p_depth_by_0[simp]: "shift_p_depth p 0 x = x"
  unfolding shift_p_depth_def by fastforce

lemma shift_p_depth_add[simp]:
  "shift_p_depth p n (x + y) = shift_p_depth p n x + shift_p_depth p n y"
  using shift_p_depth_def distrib_right[of x y] by presburger

lemma shift_p_depth_uminus[simp]:
  "shift_p_depth p n (- x) = - shift_p_depth p n x"
  using shift_p_depth_def mult_minus_left[of x] by presburger

lemma shift_p_depth_minus[simp]:
  "shift_p_depth p n (x - y) = shift_p_depth p n x - shift_p_depth p n y"
  using shift_p_depth_add[of p n x "-y"] by auto

lemma shift_p_depth_equiv_at_place: "p_equal p (shift_p_depth p n x) (x * (index_const p powi n))"
  using shift_p_depth_def p_equal_func_of_consts power_int_equiv_base mult_left by simp

lemma shift_p_depth_equiv_at_other_places:
  "p_equal q (shift_p_depth p n x) x" if "q \<noteq> p"
  using that p_equal_func_of_consts[of q _ 1] power_int_equiv_base power_int_1_left
        shift_p_depth_def mult_left
  by    fastforce

lemma shift_p_depth_equiv0_iff:
  "p_equal q (shift_p_depth p n x) 0 \<longleftrightarrow> p_equal q x 0"
  using shift_p_depth_equiv_at_place trans0_iff mult_equiv_0_iff power_int_equiv_0_iff
        index_const_globally_nequiv_0 shift_p_depth_equiv_at_other_places
  by (metis (full_types))

lemma shift_p_depth_equiv_iff:
  "p_equal q (shift_p_depth p n x) (shift_p_depth p n y) = p_equal q x y"
  using conv_0 shift_p_depth_minus shift_p_depth_equiv0_iff by metis

lemma shift_p_depth_trivial_iff:
  "shift_p_depth p n x = x \<longleftrightarrow> n = 0 \<or> p_equal p x 0"
proof
  assume "shift_p_depth p n x = x"
  hence "p_equal p (x * (1 - index_const p powi n)) 0"
    using shift_p_depth_equiv_at_place conv_0 mult_1_right right_diff_distrib by metis
  thus "n = 0 \<or> p_equal p x 0"
    using mult_equiv_0_iff conv_0 sym depth_equiv p_depth_1 p_depth_index_const_powi by metis
next
  assume "n = 0 \<or> p_equal p x 0"
  moreover have "n = 0 \<Longrightarrow> shift_p_depth p n x = x" by simp
  moreover have "p_equal p x 0 \<Longrightarrow> p_equal p (shift_p_depth p n x) x"
    using shift_p_depth_equiv_at_place mult_0_left trans trans_left by blast
  ultimately have "p_equal p (shift_p_depth p n x) x" by fastforce
  thus "shift_p_depth p n x = x" using global_imp_eq shift_p_depth_equiv_at_other_places by force
qed

lemma shift_p_depth_times_right: "shift_p_depth p n (x * y) = x * shift_p_depth p n y"
proof (intro global_imp_eq, standard)
  fix q show "p_equal q (shift_p_depth p n (x * y)) (x * shift_p_depth p n y)"
  proof (cases "q = p")
    case True thus "p_equal q (shift_p_depth p n (x * y)) (x * shift_p_depth p n y)"
      using shift_p_depth_equiv_at_place[of p n "x * y"] mult.assoc[of x y]
            shift_p_depth_equiv_at_place mult_left sym trans
      by    presburger
  qed (use shift_p_depth_equiv_at_other_places mult_left sym trans in fast)
qed

lemma shift_p_depth_times_left: "shift_p_depth p n (x * y) = shift_p_depth p n x * y"
  using shift_p_depth_times_right mult.commute by metis

lemma shift_shift_p_depth: "shift_p_depth p n (shift_p_depth p m x) = shift_p_depth p (m + n) x"
proof (intro global_imp_eq, standard)
  fix q show "p_equal q (shift_p_depth p n (shift_p_depth p m x)) (shift_p_depth p (m + n) x)"
  proof (cases "q = p")
    case True
    thus ?thesis
      using shift_p_depth_equiv_at_place[of p n "shift_p_depth p m x"]
            shift_p_depth_equiv_at_place[of p m x]
            mult_right trans mult.assoc[of x, symmetric]
            index_const_globally_nequiv_0
            power_int_add[of "index_const p" m n]
            shift_p_depth_equiv_at_place[of p "m + n" x]
            trans_left[of
              p "shift_p_depth p n (shift_p_depth p m x)" "x * index_const p powi (m + n)"
              "shift_p_depth p (m + n) x"
            ]
      by    presburger
  next
    case False
    hence   "p_equal q (shift_p_depth p n (shift_p_depth p m x)) x"
      and   "p_equal q ((shift_p_depth p (m + n) x)) x"
      using shift_p_depth_equiv_at_other_places trans
      by    (blast, blast)
    thus ?thesis using trans_left by blast
  qed
qed

lemma shift_shift_p_depth_image:
  "shift_p_depth p n ` shift_p_depth p m ` A = shift_p_depth p (m + n) ` A"
proof safe
  fix a assume a: "a \<in> A"
  have *: "shift_p_depth p n (shift_p_depth p m a) = shift_p_depth p (m + n) a"
    using shift_shift_p_depth by auto
  from a show "shift_p_depth p n (shift_p_depth p m a) \<in> shift_p_depth p (m + n) ` A"
    using * by fast
  from a show "shift_p_depth p (m + n) a \<in> shift_p_depth p n ` shift_p_depth p m ` A"
    using *[symmetric] by fast
qed

lemma shift_p_depth_at_place:
  "p_depth p (shift_p_depth p n x) = p_depth p x + n" if "n = 0 \<or> \<not> p_equal p x 0"
proof (cases "n = 0")
  case True
  moreover from this have "p_equal p (shift_p_depth p n x) x"
    using shift_p_depth_equiv_at_place power_int_0_right mult_1_right by metis
  ultimately show ?thesis using depth_equiv by fastforce
next
  case False
  with that have "\<not> p_equal p (x * (index_const p powi n)) 0"
    using no_zero_divisors power_int_equiv_0_iff index_const_globally_nequiv_0 by auto
  hence "p_depth p (shift_p_depth p n x) = p_depth p x + p_depth p (index_const p powi n)"
    using depth_equiv shift_p_depth_equiv_at_place depth_mult_additive by metis
  thus ?thesis using p_depth_index_const_powi by simp
qed

lemma shift_p_depth_at_other_places:
  "p_depth q (shift_p_depth p n x) = p_depth q x" if "q \<noteq> p"
  using that depth_equiv shift_p_depth_equiv_at_other_places by blast

lemma p_depth_set_shift_p_depth_closed:
  "shift_p_depth p n x \<in> p_depth_set p m" if "p_depth p x \<ge> m - n"
  using that shift_p_depth_equiv0_iff shift_p_depth_at_place p_depth_setI by auto

lemma global_depth_set_shift_p_depth_closed:
  "shift_p_depth p n x \<in> global_depth_set m"
  if  "x \<in> global_depth_set m"
  and "\<not> p_equal p x 0 \<longrightarrow> p_depth p x \<ge> m - n"
  using that p_depth_set_shift_p_depth_closed p_depth_setD shift_p_depth_at_other_places
        shift_p_depth_equiv0_iff global_depth_setD global_depth_setI
  by    metis

lemma shift_p_depth_mem_p_depth_set:
  "p_depth p x \<ge> m - n"
  if "\<not> p_equal p x 0" and "shift_p_depth p n x \<in> p_depth_set p m"
  using that shift_p_depth_equiv0_iff shift_p_depth_at_place
        p_depth_setD[of p "shift_p_depth p n x"]
  by    fastforce

lemma shift_p_depth_mem_global_depth_set:
  "p_depth p x \<ge> m - n"
  if "\<not> p_equal p x 0" and "shift_p_depth p n x \<in> global_depth_set m"
  using that shift_p_depth_equiv0_iff shift_p_depth_at_place
        global_depth_setD[of p "shift_p_depth p n x"]
  by    fastforce

lemma shift_p_depth_p_depth_set: "shift_p_depth p n ` p_depth_set p m = p_depth_set p (m + n)"
proof safe
  fix x assume "x \<in> p_depth_set p m"
  thus "shift_p_depth p n x \<in> p_depth_set p (m + n)"
    using     shift_p_depth_at_place shift_p_depth_equiv0_iff
    unfolding p_depth_set_def
    by        simp
next
  fix x assume "x \<in> p_depth_set p (m + n)"
  hence "\<not> p_equal p x 0 \<longrightarrow> p_depth p x \<ge> m + n"
    using p_depth_setD by blast
  hence
    "\<not> p_equal p (shift_p_depth p (-n) x) 0 \<longrightarrow>
      p_depth p (shift_p_depth p (-n) x) \<ge> m"
    using shift_p_depth_at_place shift_p_depth_equiv0_iff by force
  hence "shift_p_depth p (-n) x \<in> p_depth_set p m" using p_depth_setI by simp
  moreover have "x = shift_p_depth p n (shift_p_depth p (-n) x)"
    using shift_shift_p_depth by force
  ultimately show "x \<in> shift_p_depth p n ` p_depth_set p m" by blast
qed

lemma shift_p_depth_cong:
  "p_equal q (shift_p_depth p n x) (shift_p_depth p n y)" if "p_equal q x y"
  using that cong_sym shift_p_depth_equiv_at_place mult_right
        shift_p_depth_equiv_at_other_places
  by    (cases "q = p", blast, blast)

lemma shift_p_depth_p_restrict:
  "shift_p_depth p n (p_restrict x P) = p_restrict (shift_p_depth p n x) P"
proof (intro global_imp_eq, standard)
  fix q
  show "p_equal q (shift_p_depth p n (p_restrict x P)) (p_restrict (shift_p_depth p n x) P)"
    by (
      cases "P q",
      metis p_restrict_equiv shift_p_depth_cong trans_right,
      metis p_restrict_equiv0 shift_p_depth_cong shift_p_depth_0 trans_left
    )
qed

lemma shift_p_depth_p_restrict_global_depth_set_memI:
  "shift_p_depth p n (p_restrict x ((=) p)) \<in> global_depth_set m"
  if "\<not> p_equal p x 0 \<longrightarrow> p_depth p x \<ge> m - n"
  using that shift_p_depth_p_restrict shift_p_depth_equiv0_iff shift_p_depth_at_place
        global_depth_set_p_restrictI p_depth_setI
  by    fastforce

lemma shift_p_depth_p_restrict_global_depth_set_memI':
  "shift_p_depth p n (p_restrict x ((=) p)) \<in> global_depth_set (m + n)"
  if "x \<in> p_depth_set p m"
proof-
 from that have "p_restrict x ((=) p) \<in> p_depth_set p m"
  using p_depth_set_p_restrict by simp
  hence "p_restrict (shift_p_depth p n x) ((=) p) \<in> p_depth_set p (m + n)"
    using shift_p_depth_p_depth_set shift_p_depth_p_restrict[of p n x "(=) p"] by force
  hence "p_restrict (shift_p_depth p n x) ((=) p) \<in> global_depth_set (m + n)"
    using global_depth_set_p_restrictI[of "(=) p"] by force
  thus ?thesis using shift_p_depth_p_restrict[of p n x "(=) p"] by auto
qed

lemma shift_p_depth_p_restrict_global_depth_set_image:
  "shift_p_depth p n ` (\<lambda>x. p_restrict x ((=) p)) ` global_depth_set m
    = (\<lambda>x. p_restrict x ((=) p)) ` global_depth_set (m + n)"
proof safe
  fix x assume "x \<in> global_depth_set m"
  hence
    "shift_p_depth p n (p_restrict x ((=) p)) \<in> global_depth_set (m + n)"
    using shift_p_depth_p_restrict_global_depth_set_memI' global_depth_set by blast
  moreover have
    "shift_p_depth p n (p_restrict x ((=) p)) =
      p_restrict (shift_p_depth p n (p_restrict x ((=) p))) ((=) p)"
    using shift_p_depth_p_restrict p_restrict_restrict' by presburger
  ultimately show
    "shift_p_depth p n (p_restrict x ((=) p)) \<in>
      (\<lambda>x. p_restrict x ((=) p)) ` global_depth_set (m + n)"
      by fast
next
  fix x assume "x \<in> global_depth_set (m + n)"
  moreover define y where "y \<equiv> shift_p_depth p (-n) (p_restrict x ((=) p))"
  ultimately have "y \<in> global_depth_set m"
    using shift_p_depth_p_restrict_global_depth_set_memI'[of x p "m + n" "-n"]
          global_depth_set[of "m + n"]
    by    simp
  moreover from y_def have
    "p_restrict x ((=) p) = shift_p_depth p n (p_restrict y ((=) p))"
    using shift_p_depth_p_restrict[of p n y "(=) p"] p_restrict_restrict'[of x "(=) p"]
          shift_shift_p_depth[of p n "-n" "p_restrict x ((=) p)"]
    by    force
  ultimately show
    "p_restrict x ((=) p) \<in>
      shift_p_depth p n ` (\<lambda>x. p_restrict x ((=) p)) ` global_depth_set m"
    using y_def by fast
qed

end (* locale global_p_equal_depth_div_inv_w_inj_index_consts *)


subsection \<open>Topological patterns\<close>

subsubsection \<open>By place\<close>

text \<open>Convergence of sequences as measured by depth\<close>

context p_equality_depth
begin

definition p_limseq_condition ::
  "'a \<Rightarrow> (nat \<Rightarrow> 'b) \<Rightarrow> 'b \<Rightarrow> int \<Rightarrow>
    nat \<Rightarrow> bool"
  where
    "p_limseq_condition p X x n K =
      (\<forall>k\<ge>K. \<not> p_equal p (X k) x \<longrightarrow> p_depth p (X k - x) > n)"

lemma p_limseq_conditionI [intro]:
  "p_limseq_condition p X x n K"
  if
    "\<And>k. k \<ge> K \<Longrightarrow> \<not> p_equal p (X k) x \<Longrightarrow>
      p_depth p (X k - x) > n"
  using that unfolding p_limseq_condition_def by blast

lemma p_limseq_conditionD:
  "p_depth p (X k - x) > n"
  if "p_limseq_condition p X x n K" and "k \<ge> K" and "\<not> p_equal p (X k) x"
  using that unfolding p_limseq_condition_def by blast

abbreviation p_limseq ::
  "'a \<Rightarrow> (nat \<Rightarrow> 'b) \<Rightarrow> 'b \<Rightarrow> bool"
  where "p_limseq p X x \<equiv> (\<forall>n. \<exists>K. p_limseq_condition p X x n K)"

lemma p_limseq_p_cong:
  "p_limseq p X x"
  if "\<forall>n\<ge>N. p_equal p (X n) (Y n)" and "p_equal p x y" and "p_limseq p Y y"
proof
  fix n
  from that(3) obtain M where M: "p_limseq_condition p Y y n M" by fastforce
  define K where "K \<equiv> max M N"
  with M that(1,2) have "p_limseq_condition p X x n K"
    using trans[of p "X _" "Y _" y] trans_left[of p "X _" y x] p_limseq_conditionD[of p Y y n M]
          depth_diff_equiv
    by    fastforce
  thus "\<exists>K. p_limseq_condition p X x n K" by auto
qed

lemma p_limseq_p_constant: "p_limseq p X x" if "\<forall>n. p_equal p (X n) x"
  using that by fast

lemma p_limseq_constant: "p_limseq p (\<lambda>n. x) x"
  using p_limseq_p_constant by auto

lemma p_limseq_p_eventually_constant:
  "p_limseq p X x" if "\<forall>\<^sub>F k in sequentially. p_equal p (X k) x"
proof
  fix n
  from that obtain K where K: "\<forall>k\<ge>K. p_equal p (X k) x"
    using eventually_sequentially by auto
  hence "p_limseq_condition p X x n K" by blast
  thus "\<exists>K. p_limseq_condition p X x n K" by blast
qed

lemma p_limseq_0 [simp]: "p_limseq p 0 0"
  using p_limseq_p_constant by simp

lemma p_limseq_0_iff: "p_limseq p 0 x \<longleftrightarrow> p_equal p x 0"
proof
  have "\<not> p_equal p x 0 \<Longrightarrow> \<not> p_limseq p 0 x"
  proof
    assume x: "\<not> p_equal p x 0" "p_limseq p 0 x"
    have "\<forall>n. p_depth p x > n"
    proof
      fix n
      from x obtain K :: nat where "\<forall>k\<ge>K. p_depth p x > n"
        using p_limseq_conditionD zero_fun_apply diff_0 depth_uminus sym by metis
      thus "p_depth p x > n" by fast
    qed
    thus False by fast
  qed
  thus "p_limseq p 0 x \<Longrightarrow> p_equal p x 0" by blast
qed (use sym in force)

lemma p_limseq_add: "p_limseq p (X + Y) (x + y)" if "p_limseq p X x" and "p_limseq p Y y"
proof
  fix n
  from that obtain K_x K_y
    where K_x: "p_limseq_condition p X x n K_x"
    and   K_y: "p_limseq_condition p Y y n K_y"
    by    blast
  define K where "K \<equiv> max K_x K_y"
  have "p_limseq_condition p (X + Y) (x + y) n K"
  proof (standard, unfold plus_fun_apply)
    fix k assume k: "k \<ge> K" "\<not> p_equal p (X k + Y k) (x + y)"
    from K_def k(1) have k_K_x_y: "k \<ge> K_x" "k \<ge> K_y" by auto
    have *:
      "\<And>X Y x y.
        p_equal p (X k) x \<Longrightarrow> p_depth p (Y k - y) > n \<Longrightarrow>
          p_depth p (X k + Y k - (x + y)) > n"
    proof-
      fix X Y x y
      assume X: "p_equal p (X k) x" and Y: "p_depth p (Y k - y) > n"
      have "p_depth p (X k + Y k - (x + y)) = p_depth p (X k + (Y k - (x + y)))"
        by (simp add: algebra_simps)
      also from X have "\<dots> = p_depth p (x + (Y k - (x + y)))"
        using add_right depth_equiv by blast
      also have "\<dots> = p_depth p (Y k - y)" by fastforce
      finally show "p_depth p (X k + Y k - (x + y)) > n" using Y by metis
    qed
    from k(2) consider
      (x_not_y) "  p_equal p (X k) x" "\<not> p_equal p (Y k) y" |
      (y_not_x) "\<not> p_equal p (X k) x" "  p_equal p (Y k) y" |
      (neither) "\<not> p_equal p (X k) x" "\<not> p_equal p (Y k) y"
      using add by blast
    thus "p_depth p (X k + Y k - (x + y)) > n"
    proof cases
      case x_not_y
      from K_y k_K_x_y(2) x_not_y(2) have "p_depth p (Y k - y) > n"
        using p_limseq_conditionD by auto
      with x_not_y(1) show ?thesis using * by blast
    next
      case y_not_x
      from K_x k_K_x_y(1) y_not_x(1) have "p_depth p (X k - x) > n"
        using p_limseq_conditionD by auto
      with y_not_x(2) have "p_depth p (Y k + X k - (y + x)) > n" using * by force
      thus ?thesis by (simp add: algebra_simps)
    next
      case neither
      moreover from K_x K_y k_K_x_y this have "min (p_depth p (X k - x)) (p_depth p (Y k - y)) > n"
        using p_limseq_conditionD by simp
      moreover from k(2) have "\<not> p_equal p (X k - x + (Y k - y)) 0"
        using conv_0 by (simp add: algebra_simps)
      ultimately have "p_depth p (X k - x + (Y k - y)) > n"
        using conv_0 depth_nonarch[of p "X k - x" "Y k - y"] by auto
      thus ?thesis by (simp add: algebra_simps)
    qed
  qed
  thus "\<exists>K. p_limseq_condition p (X + Y) (x + y) n K" by blast
qed

lemma p_limseq_uminus: "p_limseq p (-X) (-x)" if "p_limseq p X x"
proof
  fix n from that obtain K where "p_limseq_condition p X x n K" by metis
  hence "p_limseq_condition p (-X) (-x) n K"
    using uminus depth_diff unfolding p_limseq_condition_def by auto
  thus "\<exists>K. p_limseq_condition p (-X) (-x) n K" by blast
qed

lemma p_limseq_diff: "p_limseq p (X - Y) (x - y)" if "p_limseq p X x" and "p_limseq p Y y"
  using that p_limseq_uminus[of p Y y] p_limseq_add[of p X x "-Y" "-y"] by force

lemma p_limseq_conv_0: "p_limseq p X x \<longleftrightarrow> p_limseq p (\<lambda>n. X n - x) 0"
proof
  assume "p_limseq p X x"
  moreover have "X - (\<lambda>n. x) = (\<lambda>n. X n - x)" by fastforce
  ultimately show "p_limseq p (\<lambda>n. X n - x) 0"
    using p_limseq_diff[of p X x "\<lambda>n. x"] p_limseq_constant by force
next
  assume "p_limseq p (\<lambda>n. X n - x) 0"
  moreover have "(\<lambda>n. X n - x) + (\<lambda>n. x) = X" by force
  ultimately show "p_limseq p X x"
    using p_limseq_add[of p "\<lambda>n. X n - x" 0 "\<lambda>n. x"] p_limseq_constant by simp
qed

lemma p_limseq_unique: "p_equal p x y" if "p_limseq p X x" and "p_limseq p X y"
  using that p_limseq_diff[of p X x X y] p_limseq_0_iff[of p "x - y"] conv_0[of p] by auto

lemma p_limseq_eventually_nequiv_0:
  "\<forall>\<^sub>F k in sequentially. \<not> p_equal p (X k) 0"
  if "\<not> p_equal p x 0" and "p_limseq p X x"
proof-
  have "\<not> (\<forall>K. \<exists>k\<ge>K. p_equal p (X k) 0)"
  proof
    assume "\<forall>K. \<exists>k\<ge>K. p_equal p (X k) 0"
    with that have "\<forall>n. p_depth p x > n"
      by (metis p_limseq_conditionD trans_right depth_diff_equiv0_left)
    thus False by blast
  qed
  thus ?thesis using eventually_sequentially by force
qed

lemma p_limseq_bdd_depth:
  assumes "\<not> p_equal p x 0" and "p_limseq p X x"
  obtains d where "\<forall>k. \<not> p_equal p (X k) 0 \<longrightarrow> p_depth p (X k) \<le> d"
proof-
  from assms(2) obtain K where K: "p_limseq_condition p X x (p_depth p x) K" by auto
  define D where "D \<equiv> {p_depth p x} \<union> {p_depth p (X k) | k. k < K}"
  define d where "d \<equiv> Max D"
  have "\<forall>k. \<not> p_equal p (X k) 0 \<longrightarrow> p_depth p (X k) \<le> d"
  proof clarify
    fix k show "p_depth p (X k) \<le> d"
    proof (cases "k \<ge> K")
      case True
      with assms(1) K have "p_depth p (X k) \<le> p_depth p x"
        using depth_equiv depth_pre_nonarch_diff_right[of p x "X k"] p_limseq_conditionD
        by    fastforce
      also from D_def d_def have "\<dots> \<le> d" using Max_ge[of D "p_depth p x"] by simp
      finally show ?thesis by blast
    next
      case False with D_def d_def show ?thesis using Max_ge[of D "p_depth p (X k)"] by fastforce
    qed
  qed
  with that show thesis by blast
qed

lemma p_limseq_eventually_bdd_depth:
  "\<forall>\<^sub>F k in sequentially. p_depth p (X k) \<le> p_depth p x"
  if "\<not> p_equal p x 0" and "p_limseq p X x"
proof-
  from that(2) obtain K where K: "p_limseq_condition p X x (p_depth p x) K" by auto
  have "\<forall>k\<ge>K. p_depth p (X k) \<le> p_depth p x"
  proof clarify
    fix k assume "k \<ge> K"
    with that(1) K show "p_depth p (X k) \<le> p_depth p x"
      using depth_equiv depth_pre_nonarch_diff_right[of p x "X k"] p_limseq_conditionD by fastforce
  qed
  thus ?thesis using eventually_sequentially by blast
qed

lemma p_limseq_delayed_iff:
  "p_limseq p X x \<longleftrightarrow> p_limseq p (\<lambda>n. X (N + n)) x"
proof (standard, safe)
  fix n
  assume "p_limseq p X x"
  from this obtain K where "p_limseq_condition p X x n K" by fastforce
  hence "p_limseq_condition p (\<lambda>n. X (N + n)) x n K"
    unfolding p_limseq_condition_def by simp
  thus "\<exists>K. p_limseq_condition p (\<lambda>n. X (N + n)) x n K" by blast
next
  fix n
  assume "p_limseq p (\<lambda>n. X (N + n)) x"
  from this obtain M where M: "p_limseq_condition p (\<lambda>n. X (N + n)) x n M" by auto
  define K where "K \<equiv> M + N"
  have "p_limseq_condition p X x n K"
  proof
    fix k assume k: "k \<ge> K" and X: "\<not> p_equal p (X k) x"
    from k K_def have "N + (k - N) = k" by simp
    moreover from k K_def have "k - N \<ge> M" by auto
    moreover from k K_def X have "\<not> p_equal p (X (N + (k - N))) x"
      by (simp add: algebra_simps)
    ultimately show "p_depth p (X k - x) > n" using M p_limseq_conditionD by metis
  qed
  thus "\<exists>K. p_limseq_condition p X x n K" by blast
qed

lemma p_depth_set_p_limseq_closed:
  "x \<in> p_depth_set p n"
  if "p_limseq p X x" and "\<forall>\<^sub>F k in sequentially. X k \<in> p_depth_set p n"
proof (intro p_depth_setI, clarify)
  assume x_n0: "\<not> p_equal p x 0"
  from that(1) obtain K where K: "p_limseq_condition p X x n K" by blast
  from that(2) obtain N where N: "\<forall>k\<ge>N. X k \<in> p_depth_set p n"
    using eventually_sequentially by fastforce
  define k where "k \<equiv> max N K"
  show "p_depth p x \<ge> n"
  proof (cases "p_equal p (X k) x")
    case True with N x_n0 k_def show ?thesis
      using trans_right[of p _ x] p_depth_setD[of p "X k"] depth_equiv by fastforce
  next
    case False
    with K k_def have X_x: "p_depth p (X k - x) > n"
      using p_limseq_conditionD by force
    show ?thesis
    proof (cases "p_equal p (X k) 0")
      case True thus ?thesis using X_x depth_diff_equiv0_left by simp
    next
      case False
      with N x_n0 k_def show "p_depth p x \<ge> n"
        using X_x depth_pre_nonarch_diff_right[of p x "X k"] p_depth_setD[of p _ n] by fastforce
    qed
  qed
qed

text \<open>Cauchy sequences by place\<close>

definition p_cauchy_condition ::
  "'a \<Rightarrow> (nat \<Rightarrow> 'b) \<Rightarrow> int \<Rightarrow> nat \<Rightarrow> bool"
  where
    "p_cauchy_condition p X n K =
      (\<forall>k1\<ge>K. \<forall>k2\<ge>K.
        \<not> p_equal p (X k1) (X k2) \<longrightarrow> p_depth p (X k1 - X k2) > n
      )"

lemma p_cauchy_conditionI:
  "p_cauchy_condition p X n K"
  if
    "\<And>k k'. k \<ge> K \<Longrightarrow> k' \<ge> K \<Longrightarrow>
      \<not> p_equal p (X k) (X k') \<Longrightarrow> p_depth p (X k - X k') > n"
  using that unfolding p_cauchy_condition_def by blast

lemma p_cauchy_conditionD:
  "p_depth p (X k - X k') > n"
  if  "p_cauchy_condition p X n K" and "k \<ge> K" and "k' \<ge> K"
  and "\<not> p_equal p (X k) (X k')"
  using that unfolding p_cauchy_condition_def by blast

lemma p_cauchy_condition_mono_seq_tail:
  "p_cauchy_condition p X n K \<Longrightarrow> p_cauchy_condition p X n K'"
  if "K' \<ge> K"
  using that unfolding p_cauchy_condition_def by auto

lemma p_cauchy_condition_mono_depth:
  "p_cauchy_condition p X n K \<Longrightarrow> p_cauchy_condition p X m K"
  if "m \<le> n"
  using that unfolding p_cauchy_condition_def by fastforce

abbreviation "p_cauchy p X \<equiv> (\<forall>n. \<exists>K. p_cauchy_condition p X n K)"

lemma p_cauchy_condition_LEAST:
  "p_cauchy_condition p X n (LEAST K. p_cauchy_condition p X n K)"
  if "p_cauchy p X"
  using that Least1I[OF ex_ex1_least_nat_le] by blast

lemma p_cauchy_condition_LEAST_mono:
  "(LEAST K. p_cauchy_condition p X m K) \<le> (LEAST K. p_cauchy_condition p X n K)"
  if "p_cauchy p X" and "m \<le> n"
  using that least_le_least[OF ex_ex1_least_nat_le ex_ex1_least_nat_le]
        p_cauchy_condition_mono_depth
  by    force

definition p_consec_cauchy_condition ::
  "'a \<Rightarrow> (nat \<Rightarrow> 'b) \<Rightarrow> int \<Rightarrow> nat \<Rightarrow> bool"
  where
    "p_consec_cauchy_condition p X n K =
      (\<forall>k\<ge>K.
        \<not> p_equal p (X (Suc k)) (X k) \<longrightarrow> p_depth p (X (Suc k) - X k) > n
      )"

lemma p_consec_cauchy_conditionI:
  "p_consec_cauchy_condition p X n K"
  if
    "\<And>k. k \<ge> K \<Longrightarrow> \<not> p_equal p (X (Suc k)) (X k) \<Longrightarrow>
      p_depth p (X (Suc k) - X k) > n"
  using that unfolding p_consec_cauchy_condition_def by blast

lemma p_consec_cauchy:
  "p_cauchy p X = (\<forall>n. \<exists>K. p_consec_cauchy_condition p X n K)"
proof (standard, safe)
  fix n
  assume "p_cauchy p X"
  from this obtain K where K: "p_cauchy_condition p X n K" by auto
  hence "p_consec_cauchy_condition p X n K"
    using p_cauchy_conditionD by (force intro: p_consec_cauchy_conditionI)
  thus "\<exists>K. p_consec_cauchy_condition p X n K" by blast
next
  fix n
  assume "\<forall>n. \<exists>K. p_consec_cauchy_condition p X n K"
  from this obtain K where K: "p_consec_cauchy_condition p X n K" by blast
  have "p_cauchy_condition p X n K"
  proof (intro p_cauchy_conditionI)
    fix k k' show
      "k \<ge> K \<Longrightarrow> k' \<ge> K \<Longrightarrow>
        \<not> p_equal p (X k) (X k') \<Longrightarrow> p_depth p (X k - X k') > n"
    proof (induct k' k rule: linorder_wlog)
      case (le a b)
      define c where "c \<equiv> b - a"
      have
        "a \<ge> K \<Longrightarrow> \<not> p_equal p (X (a + c)) (X a) \<Longrightarrow>
          p_depth p (X (a + c) - X a) > n"
      proof (induct c)
        case (Suc c)
        have decomp: "X (a + Suc c) - X a = (X (a + Suc c) - X (a + c)) + (X (a + c) - X a)"
          by fastforce
        consider  "p_equal p (X (a + Suc c)) (X (a + c))"   |
                  "p_equal p (X (a + c)) (X a)"             |
                  "\<not> p_equal p (X (a + Suc c)) (X (a + c))"
                  "\<not> p_equal p (X (a + c)) (X a)"
          by blast
        thus ?case
        proof (cases, metis Suc trans decomp conv_0 depth_add_equiv0_left)
          case 2
          with Suc(3) have "\<not> p_equal p (X (a + Suc c)) (X (a + c))" using trans by blast
          with K Suc(2) have "p_depth p (X (a + Suc c) - X (a + c)) > n"
            using p_consec_cauchy_condition_def[of p X n K] by force
          with 2 show ?thesis using decomp conv_0 depth_add_equiv0_right by presburger
        next
          case 3
          moreover from K Suc(2) 3(1) have "p_depth p (X (a + Suc c) - X (a + c)) > n"
            using p_consec_cauchy_condition_def[of p X n K] by force
          moreover from 3(2) Suc(1,2) have "p_depth p (X (a + c) - X a) > n" by fast
          ultimately show ?thesis using Suc(3) decomp conv_0 depth_nonarch[of p] by fastforce
        qed
      qed simp
      with le c_def show ?case by force
    qed (metis sym depth_diff)
  qed
  thus "\<exists>K. p_cauchy_condition p X n K" by blast
qed

end (* context p_equality_depth *)

context p_equality_depth_no_zero_divisors
begin

lemma p_limseq_mult_both_0: "p_limseq p (X * Y) 0" if "p_limseq p X 0" and "p_limseq p Y 0"
proof
  fix n
  from that obtain K_X K_Y
    where "p_limseq_condition p X 0 \<bar>n\<bar> K_X"
    and   "p_limseq_condition p Y 0 \<bar>n\<bar> K_Y"
    by    metis
  moreover define K where "K \<equiv> max K_X K_Y"
  ultimately have "p_limseq_condition p (X * Y) 0 n K"
    using     K_def mult_0_left mult_0_right depth_mult_additive
    unfolding p_limseq_condition_def
    by        fastforce
  thus "\<exists>K. p_limseq_condition p (X * Y) 0 n K" by blast
qed

lemma p_limseq_constant_mult_0: "p_limseq p (\<lambda>n. x * Y n) 0" if "p_limseq p Y 0"
proof
  fix n
  from that obtain K where "p_limseq_condition p Y 0 (n - p_depth p x) K" by auto
  hence "p_limseq_condition p (\<lambda>n. x * Y n) 0 n K"
    using mult_0_right depth_mult_additive unfolding p_limseq_condition_def by auto
  thus "\<exists>K. p_limseq_condition p (\<lambda>n. x * Y n) 0 n K" by auto
qed

lemma p_limseq_mult_0_right: "p_limseq p (X * Y) 0" if "p_limseq p X x" and "p_limseq p Y 0"
proof-
  from that(1) have "p_limseq p (\<lambda>n. X n - x) 0" using p_limseq_conv_0 by blast
  with that(2) have "p_limseq p ((\<lambda>n. X n - x) * Y) 0" using p_limseq_mult_both_0 by blast
  moreover have "(\<lambda>n. X n - x) * Y = X * Y - (\<lambda>n. x * Y n)"
    unfolding times_fun_def fun_diff_def by (auto simp add: algebra_simps)
  ultimately have "p_limseq p (X * Y - (\<lambda>n. x * Y n)) 0" by auto
  with that(2) have "p_limseq p (X * Y - (\<lambda>n. x * Y n) + (\<lambda>n. x * Y n)) 0"
    using p_limseq_constant_mult_0[of p Y x]
          p_limseq_add[of p "X * Y - (\<lambda>n. x * Y n)" 0 "\<lambda>n. x * Y n"]
    by    simp
  thus ?thesis by (simp add: algebra_simps)
qed

lemma p_limseq_mult: "p_limseq p (X * Y) (x * y)" if "p_limseq p X x" and "p_limseq p Y y"
proof-
  from that have "p_limseq p (X * (\<lambda>n. Y n - y)) 0"
    using p_limseq_conv_0 p_limseq_mult_0_right by simp
  moreover from that have "p_limseq p (\<lambda>n. y * (X n - x)) 0"
    using p_limseq_conv_0 p_limseq_constant_mult_0 by blast
  ultimately have "p_limseq p (X * (\<lambda>n. Y n - y) + (\<lambda>n. y * (X n - x))) 0"
    using p_limseq_add[of p "X * (\<lambda>n. Y n - y)" 0] by force
  moreover have
    "X * (\<lambda>n. Y n - y) + (\<lambda>n. y * (X n - x)) = (\<lambda>n. (X * Y) n - x * y)"
    by (auto simp add: algebra_simps)
  ultimately show "p_limseq p (X * Y) (x * y)" using p_limseq_conv_0 by metis
qed

lemma poly_continuous_p_open_nbhds:
  "p_limseq p (\<lambda>n. poly f (X n)) (poly f x)" if "p_limseq p X x"
proof (induct f)
  case (pCons a f)
  have "(\<lambda>n. poly (pCons a f) (X n)) = (\<lambda>n. a) + X * (\<lambda>n. poly f (X n))"
    by auto
  with that pCons(2) show ?case using p_limseq_constant p_limseq_add p_limseq_mult by simp
qed (simp flip: zero_fun_def)

end (* context p_equality_depth_no_zero_divisors *)

context p_equality_depth_no_zero_divisors_1
begin

lemma p_limseq_pow: "p_limseq p (\<lambda>k. (X k)^n) (x ^ n)" if "p_limseq p X x"
proof (induct n)
  case (Suc n)
  moreover have "(\<lambda>k. X k ^ Suc n) = X * (\<lambda>k. X k ^ n)" by auto
  ultimately show ?case using that p_limseq_mult by simp
qed (simp add: p_limseq_constant)

lemma p_limseq_poly: "p_limseq p (\<lambda>n. poly f (X n)) (poly f x)" if "p_limseq p X x"
proof (induct f)
  case (pCons a f)
  have "(\<lambda>n. poly (pCons a f) (X n)) = (\<lambda>n. a) + X * (\<lambda>n. poly f (X n))"
    by auto
  with that pCons(2) show ?case using p_limseq_mult p_limseq_add p_limseq_constant by auto
qed (simp flip: zero_fun_def)

end (* context p_equality_depth_no_zero_divisors_1 *)

context p_equality_depth_div_inv
begin

lemma p_limseq_inverse:
  "p_limseq p (\<lambda>n. inverse (X n)) (inverse x)"
  if "\<not> p_equal p x 0" and "p_limseq p X x"
proof
  fix n
  from that obtain K1 where K1: "\<forall>k\<ge>K1. p_depth p (X k) \<le> p_depth p x"
    using p_limseq_eventually_bdd_depth eventually_sequentially by fastforce
  from that obtain K2 where K2: "\<forall>k\<ge>K2. \<not> p_equal p (X k) 0"
    using p_limseq_eventually_nequiv_0 eventually_sequentially by force
  from that(2) obtain K3
    where K3: "p_limseq_condition p X x (\<bar>n\<bar> + 2 * p_depth p x) K3"
    by    fast
  define K where "K \<equiv> Max {K1, K2, K3}"
  have "p_limseq_condition p (\<lambda>n. inverse (X n)) (inverse x) n K"
  proof
    fix k assume k: "k \<ge> K" and X_k: "\<not> p_equal p (inverse (X k)) (inverse x)"
    from k(1) K_def K2 have "p_equal p (inverse (X k) * X k) 1" using left_inverse_equiv by simp
    moreover from that(1) have "p_equal p (x * inverse x) 1" using right_inverse_equiv by simp
    ultimately have "p_equal p (inverse (X k) * (x - X k) * inverse x) (inverse (X k) - inverse x)"
      using minus mult_left[of p "x * inverse x" 1 "inverse (X k)"]
            mult_right[of p "inverse (X k) * X k" 1 "inverse x"]
      by    (simp add: algebra_simps)
    with X_k have
      "p_depth p (inverse (X k) - inverse x) =
        p_depth p (inverse (X k)) + p_depth p (X k - x) + p_depth p (inverse x)"
      using depth_equiv trans_right conv_0 depth_mult3_additive depth_diff by metis
    also from k X_k K_def K1 K2 K3 have "\<dots> > n"
      using inverse_depth inverse_equiv_iff_equiv p_limseq_conditionD
      by    (fastforce simp add: algebra_simps)
    finally show "p_depth p (inverse (X k) - inverse x) > n" by force
  qed
  thus "\<exists>K. p_limseq_condition p (\<lambda>n. inverse (X n)) (inverse x) n K" by blast
qed

lemma p_limseq_divide:
  "p_limseq p (\<lambda>n. X n / Y n) (x / y)"
  if "\<not> p_equal p y 0" and "p_limseq p X x" and "p_limseq p Y y"
proof-
  have "(\<lambda>n. X n / Y n) = X * (\<lambda>n. inverse (Y n))" using divide_inverse by force
  with that show ?thesis using p_limseq_mult p_limseq_inverse divide_inverse by simp
qed

end (* context p_equality_depth_div_inv *)

context global_p_equality_depth
begin

lemma p_limseq_p_restrict_iff:
  "p_limseq p (\<lambda>n. p_restrict (X n) P) x \<longleftrightarrow> p_limseq p X x" if "P p"
  using that sym p_restrict_equiv p_limseq_p_cong[of 0 p "\<lambda>n. p_restrict (X n) P" X x x]
        p_limseq_p_cong[of 0 p X "\<lambda>n. p_restrict (X n) P" x x]
  by    auto

lemma p_limseq_p_restricted: "p_limseq p (\<lambda>n. p_restrict (X n) P) 0" if "\<not> P p"
  using that p_restrict_equiv0 p_limseq_p_cong by blast

end (* context global_p_equality_depth *)

text \<open>Base of open sets at local places\<close>

context global_p_equal_depth
begin

abbreviation p_open_nbhd :: "'a \<Rightarrow> int \<Rightarrow> 'b \<Rightarrow> 'b set"
  where "p_open_nbhd p n x \<equiv> x +o p_depth_set p n"

abbreviation "local_p_open_nbhds p \<equiv> { p_open_nbhd p n x | n x. True }"
abbreviation "p_open_nbhds         \<equiv> (\<Union>p. local_p_open_nbhds p)"

lemma p_open_nbhd: "x \<in> p_open_nbhd p n x"
  unfolding elt_set_plus_def using p_depth_set_0 by force

lemma local_p_open_nbhd_is_open: "generate_topology (local_p_open_nbhds p) (p_open_nbhd p n x)"
  using generate_topology.intros(4)[of _ "local_p_open_nbhds p"] by blast

lemma p_open_nbhd_is_open: "generate_topology p_open_nbhds (p_open_nbhd p n x)"
  using generate_topology.intros(4)[of _ p_open_nbhds] by blast

lemma local_p_open_nbhds_are_coarser:
  "generate_topology (local_p_open_nbhds p) S \<Longrightarrow> generate_topology p_open_nbhds S"
proof (
  induct S rule: generate_topology.induct, rule generate_topology.UNIV,
  use generate_topology.Int in blast, use generate_topology.UN in blast
)
  case (Basis S)
  hence "S \<in> p_open_nbhds" by blast
  thus ?case using generate_topology.Basis by meson
qed

lemma p_open_nbhd_diff_depth:
  "p_depth p (y - x) \<ge> n" if "\<not> p_equal p y x" and "y \<in> p_open_nbhd p n x"
proof-
  from that(2) have "y - x \<in> p_depth_set p n"
    unfolding elt_set_plus_def by fastforce
  with that(1) show ?thesis using conv_0 p_depth_setD by blast
qed

lemma p_open_nbhd_eq_circle:
  "p_open_nbhd p n x = {y. \<not> p_equal p y x \<longrightarrow> p_depth p (y - x) \<ge> n}"
proof safe
(* simp add: p_open_nbhd_diff_depth *)
  fix y assume "y \<notin> p_open_nbhd p n x" "p_equal p y x"
  thus False using conv_0 p_depth_set_equiv0 unfolding elt_set_plus_def by force
next
  fix y assume "n \<le> p_depth p (y - x)"
  thus "y \<in> p_open_nbhd p n x"
    unfolding elt_set_plus_def using p_depth_setI by force
qed (simp add: p_open_nbhd_diff_depth)

lemma p_open_nbhd_circle_multicentre:
  "p_open_nbhd p n y = p_open_nbhd p n x" if "y \<in> p_open_nbhd p n x"
proof-
  have *:
    "\<And>x y. y \<in> p_open_nbhd p n x \<Longrightarrow>
      p_open_nbhd p n y \<subseteq> p_open_nbhd p n x"
  proof clarify
    fix x y z assume yx: "y \<in> p_open_nbhd p n x" and zy: "z \<in> p_open_nbhd p n y"
    have "\<not> p_equal p z x \<longrightarrow> p_depth p (z - x) \<ge> n"
    proof
      assume zx: "\<not> p_equal p z x"
      have zyx: "z - x = (z - y) + (y - x)" by auto
      consider
        "p_equal p z y" | "p_equal p y x" | (neq) "\<not> p_equal p z y" "\<not> p_equal p y x"
        by fast
      thus "p_depth p (z - x) \<ge> n"
      proof (
        cases,
        metis zyx yx zx yx trans conv_0 depth_add_equiv0_left p_open_nbhd_diff_depth,
        metis zyx zy zx trans conv_0 depth_add_equiv0_right p_open_nbhd_diff_depth
      )
        case neq
        with yx zy have "p_depth p (z - y) \<ge> n" and "p_depth p (y - x) \<ge> n"
          using p_open_nbhd_diff_depth by simp_all
        hence "min (p_depth p (z - y)) (p_depth p (y - x)) \<ge> n" by presburger
        moreover from neq zyx zx
          have  "p_depth p (z - x) \<ge> min (p_depth p (z - y)) (p_depth p (y - x))"
          by    (metis conv_0 depth_nonarch)
        ultimately show ?thesis by linarith
      qed
    qed
    thus "z \<in> p_open_nbhd p n x" using p_open_nbhd_eq_circle by auto
  qed
  moreover from that have "x \<in> p_open_nbhd p n y"
    using p_open_nbhd_eq_circle sym depth_diff by force
  ultimately show ?thesis using that by auto
qed

lemma p_open_nbhd_circle_multicentre':
  "x \<in> p_open_nbhd p n y \<longleftrightarrow> y \<in> p_open_nbhd p n x"
  using p_open_nbhd p_open_nbhd_circle_multicentre by blast

lemma p_open_nbhd_p_restrict:
  "p_open_nbhd p n (p_restrict x P) = p_open_nbhd p n x" if "P p"
proof (intro set_eqI)
  fix y from that show
    "y \<in> p_open_nbhd p n (p_restrict x P) \<longleftrightarrow>
      y \<in> p_open_nbhd p n x"
    using p_open_nbhd_eq_circle[of "p_restrict x P" p n]
          p_open_nbhd_eq_circle[of x p n] p_restrict_equiv[of P p x]
          depth_diff_equiv[of p y y "p_restrict x P" x]
          trans[of p y "p_restrict x P" x] trans_left[of p y x "p_restrict x P"]
    by    force
qed

lemma p_restrict_p_open_nbhd_mem_iff:
  "y \<in> p_open_nbhd p n x \<longleftrightarrow> p_restrict y P \<in> p_open_nbhd p n x" if "P p"
  using that p_open_nbhd_circle_multicentre' p_open_nbhd_p_restrict by auto

lemma p_open_nbhd_p_restrict_add_mixed_drop_right:
  "p_open_nbhd p n (p_restrict x P + p_restrict y Q) = p_open_nbhd p n x"
  if "P p" and "\<not> Q p"
proof (intro set_eqI)
  fix z
  from that have *: "p_equal p (p_restrict x P + p_restrict y Q) x"
    using p_restrict_add_mixed_equiv_drop_right by simp
  hence
    "z \<in> p_open_nbhd p n (p_restrict x P + p_restrict y Q) \<longleftrightarrow>
      \<not> p_equal p z x \<longrightarrow>
        p_depth p (z - (p_restrict x P + p_restrict y Q)) \<ge> n"
    using p_open_nbhd_eq_circle trans trans_left by blast
  moreover have "p_depth p (z - (p_restrict x P + p_restrict y Q)) = p_depth p (z - x)"
    using * depth_diff_equiv by auto
  ultimately show
    "z \<in> p_open_nbhd p n (p_restrict x P + p_restrict y Q) \<longleftrightarrow>
      z \<in> p_open_nbhd p n x"
    using p_open_nbhd_eq_circle by auto
qed

lemma p_open_nbhd_p_restrict_add_mixed_drop_left:
  "p_open_nbhd p n (p_restrict x P + p_restrict y Q) = p_open_nbhd p n y"
  if "\<not> P p" and "Q p"
  using that p_open_nbhd_p_restrict_add_mixed_drop_right[of Q p P y x] by (simp add: add.commute)

lemma p_open_nbhd_antimono:
  "p_open_nbhd p n x \<subseteq> p_open_nbhd p m x" if "m \<le> n"
  using that p_open_nbhd_eq_circle by auto

lemma p_open_nbhds_open_subopen:
  "generate_topology (local_p_open_nbhds p) A =
    (\<forall>a\<in>A. \<exists>n. p_open_nbhd p n a \<subseteq> A)"
proof
  show
    "generate_topology (local_p_open_nbhds p) A \<Longrightarrow>
      \<forall>a\<in>A. \<exists>n. p_open_nbhd p n a \<subseteq> A"
  proof (induct A rule: generate_topology.induct)
    case (Int A B) show ?case
    proof
      fix x assume x: "x \<in> A \<inter> B"
      from x Int(2) obtain n_A where "p_open_nbhd p n_A x \<subseteq> A" by blast
      moreover from x Int(4) obtain n_B where "p_open_nbhd p n_B x \<subseteq> B" by blast
      moreover define n where "n = max n_A n_B"
      ultimately have "p_open_nbhd p n x \<subseteq> A \<inter> B"
        using p_open_nbhd_antimono[of n_A n x p] p_open_nbhd_antimono[of n_B n x p] by auto
      thus "\<exists>n. p_open_nbhd p n x \<subseteq> A \<inter> B" by blast
    qed
  qed (simp, fast, use p_open_nbhd_circle_multicentre in blast)
next
  assume *: "\<forall>a\<in>A. \<exists>n. p_open_nbhd p n a \<subseteq> A"
  define f where "f \<equiv> \<lambda>a. (SOME n. p_open_nbhd p n a \<subseteq> A)"
  have "A = (\<Union>a\<in>A. p_open_nbhd p (f a) a)"
  proof safe
    fix a show "a \<in> A \<Longrightarrow> a \<in> (\<Union>a\<in>A. p_open_nbhd p (f a) a)"
      using p_open_nbhd by blast
  next
    fix x a assume a: "a \<in> A" and x: "x \<in> p_open_nbhd p (f a) a"
    from a * have ex_n: "\<exists>n. p_open_nbhd p n a \<subseteq> A" by fastforce
    from x f_def show "x \<in> A" using someI_ex[OF ex_n] by blast
  qed
  moreover have "\<forall>a\<in>A. generate_topology (local_p_open_nbhds p) (p_open_nbhd p (f a) a)"
    using generate_topology.Basis[of _ "local_p_open_nbhds p"] by blast
  ultimately show "generate_topology (local_p_open_nbhds p) A"
    using generate_topology.UN[of "(\<lambda>a. p_open_nbhd p (f a) a) ` A" "local_p_open_nbhds p"]
    by    fastforce
qed

lemma p_restrict_p_open_set_mem_iff:
  "a \<in> A \<longleftrightarrow> p_restrict a P \<in> A"
  if "generate_topology (local_p_open_nbhds p) A" and "P p"
  using that p_open_nbhds_open_subopen p_open_nbhd p_restrict_p_open_nbhd_mem_iff by fast

lemma hausdorff:
  "\<exists>p n. (p_open_nbhd p n x) \<inter> (p_open_nbhd p n y) = {}" if "x \<noteq> y"
proof-
  from that obtain p :: 'a where p: "\<not> p_equal p x y" using global_imp_eq by blast
  define n where "n \<equiv> p_depth p (x - y) + 1"
  have "(p_open_nbhd p n x) \<inter> (p_open_nbhd p n y) = {}"
    unfolding elt_set_plus_def
  proof (intro equals0I, clarify)
    fix a b
    assume  a : "a \<in> p_depth_set p n"
      and   b : "b \<in> p_depth_set p n"
      and   ab: "x + a = y + b"
    from ab have "x - y = b - a" by (simp add: algebra_simps)
    with p a b have "p_depth p (x - y) \<ge> n"
      using p_depth_set_minus conv_0 p_depth_setD by metis
    with n_def show False by linarith
  qed
  thus ?thesis by blast
qed

sublocale t2_p_open_nbhds: t2_space "generate_topology p_open_nbhds"
proof (intro class.t2_space.intro, rule topological_space_generate_topology, unfold_locales)
  fix x y :: 'b assume "x \<noteq> y"
  from this obtain p and n where pn: "(p_open_nbhd p n x) \<inter> (p_open_nbhd p n y) = {}"
    using hausdorff by presburger
  thus
    "\<exists>V V'. generate_topology p_open_nbhds V \<and> generate_topology p_open_nbhds V' \<and>
      x \<in> V \<and> y \<in> V' \<and> V \<inter> V' = {}"
    using p_open_nbhd_is_open p_open_nbhd by meson
qed

abbreviation "p_open_nbhds_tendsto    \<equiv> t2_p_open_nbhds.tendsto"
abbreviation "p_open_nbhds_convergent \<equiv> t2_p_open_nbhds.convergent"
abbreviation "p_open_nbhds_LIMSEQ     \<equiv> t2_p_open_nbhds.LIMSEQ"

lemma locally_limD: "\<exists>K. p_limseq_condition p X x n K" if "p_open_nbhds_LIMSEQ X x"
proof-
  from that have "\<exists>K. \<forall>k\<ge>K. X k \<in> p_open_nbhd p (n + 1) x"
    using     p_open_nbhd_is_open p_open_nbhd
    unfolding t2_p_open_nbhds.tendsto_def eventually_sequentially
    by        presburger
  thus "\<exists>K. p_limseq_condition p X x n K" using p_open_nbhd_eq_circle by force
qed

lemma globally_limseq_imp_locally_limseq:
  "p_limseq p X x" if "p_open_nbhds_LIMSEQ X x"
  using that locally_limD by blast

lemma globally_limseq_iff_locally_limseq: "p_open_nbhds_LIMSEQ X x = (\<forall>p. p_limseq p X x)"
proof (standard, standard, use globally_limseq_imp_locally_limseq in fast)
  assume X: "\<forall>p. p_limseq p X x"
  show "p_open_nbhds_LIMSEQ X x"
    unfolding t2_p_open_nbhds.tendsto_def eventually_sequentially
  proof clarify
    fix S :: "'b set"
    have
      "generate_topology p_open_nbhds S \<Longrightarrow> x \<in> S \<Longrightarrow>
        (\<forall>p. p_limseq p X x) \<Longrightarrow> \<exists>K. \<forall>k\<ge>K. X k \<in> S"
    proof (induct S rule: generate_topology.induct)
      case (Int A B)
      from Int(2,4-6) obtain Ka and Kb
        where "\<forall>k\<ge>Ka. X k \<in> A"
        and   "\<forall>k\<ge>Kb. X k \<in> B"
        by    blast
      from this have "\<forall>k\<ge>max Ka Kb. X k \<in> A \<inter> B" by fastforce
      thus ?case by blast
    next
      case (Basis S)
      from Basis(1,2) obtain p n where "S = p_open_nbhd p n x"
        using p_open_nbhd_circle_multicentre by blast
      moreover from Basis(3) have "\<exists>K. p_limseq_condition p X x (n - 1) K" by blast
      ultimately show ?case using p_limseq_conditionD p_open_nbhd_eq_circle by fastforce
    qed (simp, blast)
    with X show
      "generate_topology p_open_nbhds S \<Longrightarrow>
        x \<in> S \<Longrightarrow> \<exists>K. \<forall>k\<ge>K. X k \<in> S"
      by fast
  qed
qed

lemma p_open_nbhds_LIMSEQ_eventually_p_constant:
  "p_equal p x c"
  if "p_open_nbhds_LIMSEQ X x" and "\<forall>\<^sub>F k in sequentially. p_equal p (X k) c"
proof-
  have "\<not> (\<not> p_equal p x c)"
  proof
    assume contra: "\<not> p_equal p x c"
    define d where "d \<equiv> max 1 (p_depth p (x - c))"
    from that(1) obtain K1 where K1: "p_limseq_condition p X x d K1"
      using locally_limD by blast
    from that(2) obtain K2 where K2: "\<forall>k\<ge>K2. p_equal p (X k) c"
      using eventually_sequentially by auto
    define K where "K \<equiv> max K1 K2"
    show False
    proof (cases "p_equal p (X K) x")
      case True with contra K2 K_def show False using trans_right[of p "X K"] by simp
    next
      case False
      with K1 K_def have "p_depth p (X K - x) > d" using p_limseq_conditionD by simp
      with d_def K2 K_def show False using depth_diff_equiv[of p "X K" c x x] depth_diff by simp
    qed
  qed
  thus ?thesis by blast
qed

lemma p_open_nbhds_LIMSEQ_p_restrict:
  "p_equal p x 0" if "p_open_nbhds_LIMSEQ (\<lambda>n. p_restrict (X n) P) x" and "\<not> P p"
    using that globally_limseq_iff_locally_limseq sym p_restrict_equiv0 p_limseq_0_iff
          p_limseq_p_cong[of 0 p 0 "\<lambda>n. p_restrict (X n) P" x x]
   by     auto

lemma global_depth_set_p_open_nbhds_LIMSEQ_closed:
  "x \<in> global_depth_set n"
  if  "p_open_nbhds_LIMSEQ X x"
  and "\<forall>\<^sub>F k in sequentially. X k \<in> global_depth_set n"
proof (intro global_depth_setI'')
  fix p
  from that(2) have "\<forall>\<^sub>F k in sequentially. X k \<in> p_depth_set p n"
    using eventually_sequentially global_depth_set by force
  with that(1) show "x \<in> p_depth_set p n"
    using globally_limseq_imp_locally_limseq p_depth_set_p_limseq_closed by blast
qed

end (* context global_p_equal_depth *)

context global_p_equal_depth_div_inv_w_inj_index_consts
begin

lemma shift_p_depth_p_open_nbhd:
  "shift_p_depth p n ` p_open_nbhd p m x = p_open_nbhd p (m + n) (shift_p_depth p n x)"
proof safe
  fix y assume y: "y \<in> p_open_nbhd p m x"
  show "shift_p_depth p n y \<in> p_open_nbhd p (m + n) (shift_p_depth p n x)"
    unfolding p_open_nbhd_eq_circle
  proof clarify
    assume *: "\<not> p_equal p (shift_p_depth p n y) (shift_p_depth p n x)"
    hence "\<not> p_equal p y x" using shift_p_depth_equiv_iff by force
    moreover from this y have "p_depth p (y - x) + n \<ge> m + n"
      using p_open_nbhd_eq_circle by auto
    ultimately show "p_depth p (shift_p_depth p n y - shift_p_depth p n x) \<ge> m + n"
      using conv_0 shift_p_depth_at_place shift_p_depth_minus by metis
  qed
next
  fix y assume y: "y \<in> p_open_nbhd p (m + n) (shift_p_depth p n x)"
  have "shift_p_depth p (-n) y \<in> p_open_nbhd p m x"
  proof (cases "n = 0", use y in auto)
    case n: False show ?thesis
    proof (cases "p_equal p y (shift_p_depth p n x)")
      case True
      hence "p_equal p (shift_p_depth p (-n) y) x"
        using shift_p_depth_equiv_iff[of p p "-n" y] shift_shift_p_depth[of p "-n" n x] by force
      thus "shift_p_depth p (-n) y \<in> p_open_nbhd p m x" using p_open_nbhd_eq_circle by simp
    next
      case False
      moreover from this y have "p_depth p (y - shift_p_depth p n x) + (-n) \<ge> m"
        using p_open_nbhd_diff_depth by fastforce
      moreover have "shift_p_depth p (-n) (shift_p_depth p n x) = x"
        using shift_shift_p_depth by simp
      ultimately have "p_depth p (shift_p_depth p (-n) y - x) \<ge> m"
        using n conv_0 shift_p_depth_at_place shift_p_depth_minus by metis
      with False show "shift_p_depth p (-n) y \<in> p_open_nbhd p m x"
        using p_open_nbhd_eq_circle shift_p_depth_equiv_iff[of p p "-n" y "shift_p_depth p n x"]
              shift_shift_p_depth
        by    blast
    qed
  qed
  moreover have "y = shift_p_depth p n (shift_p_depth p (-n) y)"
    using shift_shift_p_depth by auto
  ultimately show "y \<in> shift_p_depth p n ` p_open_nbhd p m x" by blast
qed

lemma shift_p_depth_p_open_set:
  "generate_topology (local_p_open_nbhds p) (shift_p_depth p n ` A)"
  if "generate_topology (local_p_open_nbhds p) A"
proof (rule iffD2, rule p_open_nbhds_open_subopen, clarify)
  fix a assume "a \<in> A"
  with that obtain m where "p_open_nbhd p m a \<subseteq> A"
    using p_open_nbhds_open_subopen by fastforce
  hence "shift_p_depth p n ` p_open_nbhd p m a \<subseteq> shift_p_depth p n ` A" by fast
  moreover have
    "shift_p_depth p n ` p_open_nbhd p m a = p_open_nbhd p (m + n) (shift_p_depth p n a)"
    using shift_p_depth_p_open_nbhd by blast
  ultimately
    show  "\<exists>m. p_open_nbhd p m (shift_p_depth p n a) \<subseteq> shift_p_depth p n ` A"
    by    fast
qed

end (* context global_p_equal_depth_div_inv_w_inj_index_consts *)

locale p_complete_global_p_equal_depth = global_p_equal_depth +
  assumes complete:
    "p_cauchy p X \<Longrightarrow> p_open_nbhds_convergent (\<lambda>n. p_restrict (X n) ((=) p))"
begin

lemma p_cauchyE:
  assumes "p_cauchy p X"
  obtains x where "p_open_nbhds_LIMSEQ (\<lambda>n. p_restrict (X n) ((=) p)) x"
  using   assms complete t2_p_open_nbhds.convergent_def
  by      blast

end (* locale p_complete_global_p_equal_depth *)

text \<open>Hensel's Lemma.\<close>

context p_equality_div_inv
begin

\<comment> \<open>A sequence to approach a root from within the ring of integers.\<close>
primrec hensel_seq :: "'a \<Rightarrow> 'b poly \<Rightarrow> 'b \<Rightarrow> nat \<Rightarrow> 'b"
  where "hensel_seq p f x 0 = x" |
  "hensel_seq p f x (Suc n) = (
    if p_equal p (poly f (hensel_seq p f x n)) 0 then hensel_seq p f x n
    else
      hensel_seq p f x n - (poly f (hensel_seq p f x n)) / (poly (polyderiv f) (hensel_seq p f x n))
  )"

lemma constant_hensel_seq_case:
  "k \<ge> n \<Longrightarrow> hensel_seq p f x k = hensel_seq p f x n"
  if "p_equal p (poly f (hensel_seq p f x n)) 0"
proof (induct k)
  case (Suc k) thus ?case by (cases "n = Suc k", simp, use that in force)
qed simp

end (* context p_equality_div_inv *)

context p_equality_depth_div_inv
begin

\<comment> \<open>Context for inductive steps leading to Hensel's Lemma.\<close>
context
  fixes p :: 'a and f :: "'b poly" and x :: 'b and n :: nat
  assumes f_deg   : "degree f > 0"
    and   f_depth : "set (coeffs f) \<subseteq> p_depth_set p 0"
    and   d_hensel: "hensel_seq p f x n \<in> p_depth_set p 0"
    and   f       : "\<not> p_equal p (poly f (hensel_seq p f x n)) 0"
    and   deriv_f : "\<not> p_equal p (poly (polyderiv f) (hensel_seq p f x n)) 0"
    and   df      :
      "p_depth p (poly f (hensel_seq p f x n)) >
        2 * p_depth p (poly (polyderiv f) (hensel_seq p f x n))"
begin

lemma hensel_seq_step_1:
  "p_depth p (poly f (hensel_seq p f x (Suc n))) >
    p_depth p (poly f ((hensel_seq p f x n)))"
  if  next_f: "\<not> p_equal p (poly f (hensel_seq p f x (Suc n))) 0"
proof (cases f)
  case (pCons c q)
  define a a' where "a \<equiv> hensel_seq p f x n" and "a' \<equiv> hensel_seq p f x (Suc n)"
  define b where "b \<equiv> - ((poly f a) / (poly (polyderiv f) a))"
  define c_add_poly :: "nat \<Rightarrow> 'b poly"
    where "c_add_poly \<equiv> coeff (additive_poly_poly f)"
  define  sum_fun Suc_sum_fun :: "nat \<Rightarrow> 'b"
    where "sum_fun     \<equiv> \<lambda>i. poly (c_add_poly i) a * b ^ i"
    and   "Suc_sum_fun \<equiv> \<lambda>i. poly (c_add_poly (Suc i)) a * b ^ (Suc i)"
  define S :: "'b" where "S \<equiv> sum Suc_sum_fun {1..degree q}"
  moreover from sum_fun_def Suc_sum_fun_def have Suc_sum_fun: "Suc_sum_fun = sum_fun \<circ> Suc"
    by auto
  moreover have "{0..degree q} = {..degree q}" by auto
  moreover from f_deg pCons have "degree f = Suc (degree q)" by auto
  ultimately have "poly f a' = poly f a + poly (polyderiv f) a * b + S"
    using f a_def a'_def b_def c_add_poly_def sum_fun_def additive_poly_poly_decomp[of f a b]
          sum_up_index_split[of sum_fun 0] sum.atLeast_Suc_atMost_Suc_shift[of sum_fun 0]
          sum_up_index_split[of "sum_fun \<circ> Suc" 0] additive_poly_poly_coeff0[of f]
          additive_poly_poly_coeff1[of f]
    by    (simp add: ac_simps)
  with deriv_f a_def b_def have equiv_sum: "p_equal p (poly f a') S"
    using minus_divide_left times_divide_eq_right mult_divide_cancel_left add_left
          add.right_inverse add_equiv0_left
    by    metis
  with next_f a'_def have "\<not> p_equal p S 0" using trans by fast
  from this f_depth d_hensel a_def c_add_poly_def Suc_sum_fun_def S_def obtain j where j:
    "j \<in> {1..degree q}" "p_depth p S \<ge> int (Suc j) * p_depth p b"
    using sum_poly_additive_poly_poly_depth_bound[of f p] by force
  from f_depth f deriv_f d_hensel df a_def b_def have "p_depth p b \<ge> 0"
    using p_depth_poly_deriv_quotient depth_uminus[of p b] by fastforce
  moreover from j(1) have "2 \<le> int (Suc j)" by force
  ultimately have "int (Suc j) * p_depth p b \<ge> 2 * p_depth p b" using mult_right_mono by blast
  moreover from f deriv_f a_def b_def
    have  "p_depth p b = p_depth p (poly f a) - p_depth p (poly (polyderiv f) a)"
    using divide_equiv_0_iff depth_uminus divide_depth by metis
  ultimately show "p_depth p (poly f a') > p_depth p (poly f a)"
    using j(2) df a_def equiv_sum depth_equiv by force
qed

lemma hensel_seq_step_2:
  "\<not> p_equal p (poly (polyderiv f) (hensel_seq p f x (Suc n))) 0"
  "p_depth p (poly (polyderiv f) (hensel_seq p f x (Suc n))) =
    p_depth p (poly (polyderiv f) (hensel_seq p f x n))"
proof-

  define a a' where "a \<equiv> hensel_seq p f x n" and "a' \<equiv> hensel_seq p f x (Suc n)"
  define b where "b \<equiv> - ((poly f a) / (poly (polyderiv f) a))"
  from f deriv_f a_def b_def
    have  db: "p_depth p b = p_depth p (poly f a) - p_depth p (poly (polyderiv f) a)"
    using divide_equiv_0_iff depth_uminus divide_depth by metis

  have
    "p_depth p (poly (polyderiv f) (a')) = p_depth p (poly (polyderiv f) a) \<and>
      \<not> p_equal p (poly (polyderiv f) a') 0"
  proof (cases "degree (polyderiv f)")
    case (Suc m)
    define  c_add_poly :: "nat \<Rightarrow> 'b poly"
      where "c_add_poly \<equiv> coeff (additive_poly_poly (polyderiv f))"
    define sum_fun :: "nat \<Rightarrow> 'b"
      where "sum_fun \<equiv> \<lambda>i. poly (c_add_poly i) a * b ^ i"
    define S :: "'b" where "S \<equiv> sum (sum_fun \<circ> Suc) {0..m}"
    from f a_def a'_def b_def Suc c_add_poly_def sum_fun_def S_def have diff_eq_sum:
      "poly (polyderiv f) a' - poly (polyderiv f) a = S"
      using additive_poly_poly_decomp[of "polyderiv f" a b] sum_up_index_split[of sum_fun 0]
            sum.atLeast_Suc_atMost_Suc_shift[of sum_fun 0]
      by    (simp add: algebra_simps additive_poly_poly_coeff0)
    show ?thesis
    proof (cases "p_equal p S 0", safe)
      case True
      from True show
        "p_depth p (poly (polyderiv f) a') = p_depth p (poly (polyderiv f) a)"
        using diff_eq_sum conv_0 depth_equiv by metis
      from deriv_f a_def True show "p_equal p (poly (polyderiv f) a') 0 \<Longrightarrow> False"
        using diff_eq_sum conv_0 trans_right by blast
    next
      case False
      from this f_depth d_hensel a_def S_def sum_fun_def c_add_poly_def obtain j
        where j: "p_depth p S \<ge> int (Suc j) * p_depth p b"
        using p_depth_set_polyderiv[of f p 0]
              sum_poly_additive_poly_poly_depth_bound[of "polyderiv f" p a b 0 m]
        by    force
      from f_depth d_hensel deriv_f a_def have "p_depth p (poly (polyderiv f) a) \<ge> 0"
        using poly_p_depth_set_polyderiv[of 0 f p a] p_depth_setD[of p "poly (polyderiv f) a" 0]
        by    simp
      hence
        "p_depth p (poly (polyderiv f) a) \<le>
          int (Suc j) * (2 * p_depth p (poly (polyderiv f) a) - p_depth p (poly (polyderiv f) a))"
        using mult_right_mono[of 1 "int (Suc j)"] by auto
      also from df a_def have "\<dots> < int (Suc j) * p_depth p b" using db by simp
      finally have *:
        "p_depth p (poly (polyderiv f) a) <
          p_depth p (poly (polyderiv f) a' - poly (polyderiv f) a)"
        using j diff_eq_sum by fastforce
      with deriv_f a_def
        show  "p_depth p (poly (polyderiv f) a') = p_depth p (poly (polyderiv f) a)"
        using depth_diff_cancel_imp_eq_depth_right by blast
      show "p_equal p (poly (polyderiv f) a') 0 \<Longrightarrow> False"
        using * depth_diff_equiv0_left by fastforce
    qed
  qed (elim degree_eq_zeroE, simp, use deriv_f in fastforce)

  thus  "p_depth p (poly (polyderiv f) (a')) = p_depth p (poly (polyderiv f) a)"
    and "\<not> p_equal p (poly (polyderiv f) a') 0"
    by  auto

qed

end (* Hensel's step context *)

\<comment> \<open>Context for Hensel's Lemma.\<close>
context
  fixes p :: 'a and f :: "'b poly" and x :: 'b
  assumes f_deg       : "degree f > 0"
    and   f_depth     : "set (coeffs f) \<subseteq> p_depth_set p 0"
    and   d_init      : "x \<in> p_depth_set p 0"
    and   init_deriv  :
      "\<not> p_equal p (poly f x) 0 \<longrightarrow> \<not> p_equal p (poly (polyderiv f) x) 0"
    and   d_init_deriv:
      "\<not> p_equal p (poly f x) 0 \<longrightarrow>
        p_depth p (poly f x) > 2 * p_depth p (poly (polyderiv f) x)"
begin

lemma
      hensel_seq_adelic_int : "hensel_seq p f x n \<in> p_depth_set p 0" (is "?A")
  and hensel_seq_poly_depth :
    "\<not> p_equal p (poly f (hensel_seq p f x n)) 0 \<longrightarrow>
      p_depth p (poly f (hensel_seq p f x n)) \<ge> p_depth p (poly f x) + int n"
      (is "?B")
  and hensel_seq_deriv      :
    "\<not> p_equal p (poly f (hensel_seq p f x n)) 0 \<longrightarrow>
      \<not> p_equal p (poly (polyderiv f) (hensel_seq p f x n)) 0"
      (is "?C")
  and hensel_seq_deriv_depth:
    "\<not> p_equal p (poly f (hensel_seq p f x n)) 0 \<longrightarrow>
      p_depth p (poly (polyderiv f) (hensel_seq p f x n)) = p_depth p (poly (polyderiv f) x)"
      (is "?D")
  and hensel_seq_depth_ineq:
    "\<not> p_equal p (poly f (hensel_seq p f x n)) 0 \<longrightarrow>
      p_depth p (poly f (hensel_seq p f x n)) >
      2 * p_depth p (poly (polyderiv f) (hensel_seq p f x n))"
      (is "?E")
proof-

  have "?A \<and> ?B \<and> ?C \<and> ?D \<and> ?E"
  proof (induct n, use d_init init_deriv d_init_deriv in force)
    case (Suc n)
    define a a' where "a \<equiv> hensel_seq p f x n" and "a' \<equiv> hensel_seq p f x (Suc n)"
    show ?case
    proof (cases "p_equal p (poly f a) 0")
      case False show ?thesis
      proof (fold a_def a'_def, safe)

        from False Suc a_def a'_def
          have  prev_int        : "a \<in> p_depth_set p 0"
          and   prev_poly_depth : "p_depth p (poly f a) \<ge> p_depth p (poly f x) + int n"
          and   prev_deriv      : "\<not> p_equal p (poly (polyderiv f) a) 0"
          and   prev_deriv_depth:
            "p_depth p (poly (polyderiv f) a) = p_depth p (poly (polyderiv f) x)"
          and   prev_depth_ineq : "p_depth p (poly f a) > 2 * p_depth p (poly (polyderiv f) a)"
          by    auto

        define b where "b \<equiv> (poly f a) / (poly (polyderiv f) a)"
        with f_depth False a_def a'_def b_def show "a' \<in> p_depth_set p 0"
          using prev_int prev_deriv prev_depth_ineq p_depth_set_minus
                p_depth_set_poly_deriv_quotient[of 0 f p]
          by    force

        from f_deg f_depth a_def a'_def False
          show  next_deriv: "p_equal p (poly (polyderiv f) a') 0 \<Longrightarrow> False"
          using hensel_seq_step_2(1) prev_int prev_deriv prev_depth_ineq by blast

        from f_deg f_depth a_def a'_def False show next_deriv_depth:
          "p_depth p (poly (polyderiv f) a') = p_depth p (poly (polyderiv f) x)"
          by (metis hensel_seq_step_2(2) prev_int prev_deriv prev_depth_ineq prev_deriv_depth)

        moreover assume *: "\<not> p_equal p (poly f a') 0"

        ultimately
          show  "p_depth p (poly f a') > 2 * p_depth p (poly (polyderiv f) a')"
          using f_deg f_depth a_def a'_def False hensel_seq_step_1 prev_int prev_deriv
                prev_depth_ineq next_deriv prev_depth_ineq prev_deriv_depth next_deriv_depth
          by    force

        from f_deg f_depth a_def a'_def False
          show  "p_depth p (poly f a') \<ge> p_depth p (poly f x) + int (Suc n)"
          using * hensel_seq_step_1 prev_int prev_deriv prev_depth_ineq next_deriv prev_poly_depth
          by    force

      qed
    qed (simp add: a_def Suc)
  qed

  thus ?A ?B ?C ?D ?E by auto

qed

lemma hensel_seq_cauchy: "p_cauchy p (hensel_seq p f x)"
proof (rule iffD2, rule p_consec_cauchy, clarify)
  fix n
  show "\<exists>K. p_consec_cauchy_condition p (hensel_seq p f x) n K"
  proof (cases "\<exists>N. p_equal p (poly f (hensel_seq p f x N)) 0")
    case True
    from this obtain N where N: "p_equal p (poly f (hensel_seq p f x N)) 0" by fast
    have "p_consec_cauchy_condition p (hensel_seq p f x) n N"
    proof (intro p_consec_cauchy_conditionI)
      fix k
      assume  "k \<ge> N"
        and   "\<not> p_equal p (hensel_seq p f x (Suc k)) (hensel_seq p f x k)"
      with N show "p_depth p (hensel_seq p f x (Suc k) - hensel_seq p f x k) > n"
        using constant_hensel_seq_case[of p f x N k] by auto
    qed
    thus ?thesis by blast
  next
    case False
    hence *: "\<forall>n. \<not> p_equal p (poly f (hensel_seq p f x n)) 0" by fast
    define d where "d \<equiv> p_depth p (poly f x) - p_depth p (poly (polyderiv f) x)"
    define K where "K \<equiv> nat (n - d + 1)"
    have "p_consec_cauchy_condition p (hensel_seq p f x) n K"
    proof (intro p_consec_cauchy_conditionI)
      fix k assume "k \<ge> K"
      moreover define a a'
        where "a \<equiv> hensel_seq p f x k" and "a' \<equiv> hensel_seq p f x (Suc k)"
      moreover define b where "b \<equiv> - ((poly f a) / (poly (polyderiv f) a))"
      moreover from this a_def
        have  "p_depth p b = p_depth p (poly f a) - p_depth p (poly (polyderiv f) a)"
        using * hensel_seq_deriv divide_equiv_0_iff depth_uminus divide_depth by metis
      ultimately show "p_depth p (a' - a) > n"
        using d_def K_def * hensel_seq_deriv_depth hensel_seq_poly_depth by fastforce
    qed
    thus ?thesis by blast
  qed
qed

lemma p_limseq_poly_hensel_seq: "p_limseq p (\<lambda>n. poly f (hensel_seq p f x n)) 0"
proof
  fix n
  define K where "K \<equiv> nat (n - p_depth p (poly f x) + 1)"
  have "p_limseq_condition p (\<lambda>n. poly f (hensel_seq p f x n)) 0 n K"
  proof (intro p_limseq_conditionI)
    fix k assume "k \<ge> K" and "\<not> p_equal p (poly f (hensel_seq p f x k)) 0"
    with K_def show "p_depth p (poly f (hensel_seq p f x k) - 0) > n"
      using hensel_seq_poly_depth by fastforce
  qed
  thus "\<exists>K. p_limseq_condition p (\<lambda>n. poly f (hensel_seq p f x n)) 0 n K" by fast
qed

end (* Hensel's lemma context *)

end (* context p_equality_depth_div_inv *)


locale p_complete_global_p_equal_depth_div_inv =
  global_p_equal_depth_div_inv + p_complete_global_p_equal_depth
begin

lemma hensel:
  fixes p :: 'a and f :: "'b poly" and x :: 'b
  assumes "degree f > 0"
    and   "set (coeffs f) \<subseteq> p_depth_set p 0"
    and   "x \<in> p_depth_set p 0"
    and
      "\<not> p_equal p (poly f x) 0 \<longrightarrow> \<not> p_equal p (poly (polyderiv f) x) 0"
    and
      "\<not> p_equal p (poly f x) 0 \<longrightarrow>
        p_depth p (poly f x) > 2 * p_depth p (poly (polyderiv f) x)"
  obtains z where "z \<in> p_depth_set p 0" and "p_equal p (poly f z) 0"
proof-
  define X where "X \<equiv> hensel_seq p f x"
  define res_X where "res_X \<equiv> \<lambda>n. p_restrict (X n) ((=) p)"
  from assms X_def res_X_def obtain z where "p_open_nbhds_LIMSEQ res_X z"
    using hensel_seq_cauchy p_cauchyE by blast
  hence "p_limseq p res_X z" using globally_limseq_iff_locally_limseq by blast
  with res_X_def have X_to_z: "p_limseq p X z" using p_limseq_p_restrict_iff by blast
  with assms X_def have "p_equal p (poly f z) 0"
    using poly_continuous_p_open_nbhds p_limseq_poly_hensel_seq p_limseq_unique by metis
  moreover from assms X_def have "z \<in> p_depth_set p 0"
    using X_to_z hensel_seq_adelic_int p_depth_set_p_limseq_closed by fastforce
  ultimately show thesis using that by blast
qed

end (* locale p_complete_global_p_equal_depth_div_inv *)


subsubsection \<open>Globally\<close>

text \<open>We use bounded depth to create a global metric.\<close>

context p_equality_depth
begin

definition bdd_global_depth :: "'b \<Rightarrow> nat"
  where
    "bdd_global_depth x =
      (if globally_p_equal x 0 then 0 else Inf {nat (p_depth p x + 1) | p. \<not> p_equal p x 0})"
\<comment> \<open>The plus-one is to distinguish depth-0 from negative depth.\<close>

lemma bdd_global_depth_0[simp]: "globally_p_equal x 0 \<Longrightarrow> bdd_global_depth x = 0"
  unfolding bdd_global_depth_def by simp

lemma bdd_global_depthD:
  "bdd_global_depth x = Inf {nat (p_depth p x + 1) | p. \<not> p_equal p x 0}"
  if "\<not> globally_p_equal x 0"
  using that unfolding bdd_global_depth_def by argo

lemma bdd_global_depthD_as_image:
  "bdd_global_depth x = (INF p\<in>{p. \<not> p_equal p x 0}. nat (p_depth p x + 1))"
  if "\<not> globally_p_equal x 0"
  using that image_Collect unfolding bdd_global_depth_def by metis

lemma bdd_global_depth_cong:
  "bdd_global_depth x = bdd_global_depth y" if "globally_p_equal x y"
proof (cases "globally_p_equal x 0")
  case True with that show ?thesis using globally_p_equal_trans_right[of x y 0] by fastforce
next
  case False
  moreover from that have "{p. \<not> p_equal p x 0} = {p. \<not> p_equal p y 0}"
    using trans[of _ x y 0] trans_right[of _ x y 0] by auto
  moreover from that
    have  "(\<lambda>p. nat (p_depth p x + 1)) = (\<lambda>p. nat (p_depth p y + 1))"
    using depth_equiv[of _ x y]
    by    simp
  ultimately show ?thesis using that globally_p_equal_trans bdd_global_depthD_as_image by metis
qed

lemma bdd_global_depth_le:
  "bdd_global_depth x \<le> nat (p_depth p x + 1)" if "\<not> p_equal p x 0"
  using that bdd_global_depthD_as_image cINF_lower[of "\<lambda>p. nat (p_depth p x + 1)"]
  by    fastforce

lemma bdd_global_depth_greatest:
  "bdd_global_depth x \<ge> B"
  if  "\<not> p_equal p x 0"
  and "\<forall>q. \<not> p_equal q x 0 \<longrightarrow> nat (p_depth q x + 1) \<ge> B"
  using that bdd_global_depthD_as_image
        cINF_greatest[of
          "{p. \<not> p_equal p x 0}" B "\<lambda>p. nat (p_depth p x + 1)"
        ]
  by    fastforce

lemma bdd_global_depth_witness:
  assumes "\<not> globally_p_equal x 0"
  obtains p where "\<not> p_equal p x 0" and "bdd_global_depth x = nat (p_depth p x + 1)"
proof-
  define D where "D \<equiv> {nat (p_depth p x + 1) | p. \<not> p_equal p x 0}"
  from assms obtain q where "\<not> p_equal q x 0" by blast
  with D_def have "nat (p_depth q x + 1) \<in> D" by force
  with assms D_def obtain p
    where "\<not> p_equal p x 0"
    and   "bdd_global_depth x = nat (p_depth p x + 1)"
    using wellorder_InfI[of _ D] bdd_global_depthD
    by    auto
  with that show thesis by meson
qed

lemma bdd_global_depth_eq_0:
  "bdd_global_depth x = 0" if "p_depth p x < 0"
  using that depth_equiv_0 bdd_global_depth_le[of p x] by fastforce

lemma bdd_global_depth_eq_0_iff:
  "bdd_global_depth x = 0 \<longleftrightarrow>
    (\<exists>p. p_depth p x < 0) \<or> (globally_p_equal x 0)"
  (is "?L = ?R")
proof
  assume L: ?L show ?R
  proof clarify
    assume "\<not> globally_p_equal x 0"
    from this obtain p where "\<not> p_equal p x 0" and "bdd_global_depth x = nat (p_depth p x + 1)"
      using bdd_global_depth_witness[of x] by auto
    with L have "p_depth p x < 0" by force
    thus "\<exists>p. p_depth p x < 0" by blast
  qed
next
  assume ?R thus ?L by (cases "globally_p_equal x 0", use bdd_global_depth_eq_0 in auto)
qed

lemma bdd_global_depth_diff: "bdd_global_depth (x - y) = bdd_global_depth (y - x)"
  using depth_diff conv_0 sym_iff[of _ x y] unfolding bdd_global_depth_def by simp

lemma bdd_global_depth_uminus: "bdd_global_depth (- x) = bdd_global_depth x"
  using depth_uminus uminus_iff[of _ x 0] unfolding bdd_global_depth_def by auto

lemma bdd_global_depth_nonarch:
  "bdd_global_depth (x + y) \<ge> min (bdd_global_depth x) (bdd_global_depth y)"
  if "\<not> globally_p_equal (x + y) 0"
proof-
  consider  "globally_p_equal x 0" | "globally_p_equal y 0" |
            (n0) "\<not> globally_p_equal x 0" "\<not> globally_p_equal y 0"
    by      blast
  thus ?thesis
  proof cases
    case n0
    define N :: "'b \<Rightarrow> 'a set" where "N \<equiv> \<lambda>x. {p. \<not> p_equal p x 0}"
    define dp1 where "dp1 \<equiv> \<lambda>x p. p_depth p x + 1"
    define trunc_dp1 where "trunc_dp1 \<equiv> \<lambda>x p. nat (dp1 x p)"
    define inf_trunc_dp1 :: "'b \<Rightarrow> nat"
      where "inf_trunc_dp1 \<equiv> \<lambda>x. (INF p\<in>N x. trunc_dp1 x p)"
    from inf_trunc_dp1_def have inf_trunc_dp1:
      "\<And>p x. p \<in> N x \<Longrightarrow> inf_trunc_dp1 x \<le> trunc_dp1 x p"
      using cINF_lower by fast
    define choose_dpth :: "'a \<Rightarrow> int" where
      "choose_dpth \<equiv> \<lambda>p.
        if p_equal p x 0 then dp1 y p
        else if p_equal p y 0 then dp1 x p
        else min (dp1 x p) (dp1 y p)"
    from that n0 N_def
      have  nempty: "N x \<noteq> {}" "N y \<noteq> {}" "N (x + y) \<noteq> {}"
      using globally_p_equalI
      by    (blast, blast, blast)
    have
      "Inf ((nat \<circ> choose_dpth) ` (N x \<union> N y)) =
        min (inf_trunc_dp1 x) (inf_trunc_dp1 y)"
    proof (intro cInf_eq_non_empty)
      fix n assume "n \<in> (nat \<circ> choose_dpth) ` (N x \<union> N y)"
      from this obtain p where "p \<in> N x \<union> N y" "n = nat (choose_dpth p)" by auto
      thus "min (inf_trunc_dp1 x) (inf_trunc_dp1 y) \<le> n"
        using N_def trunc_dp1_def choose_dpth_def inf_trunc_dp1[of p x] inf_trunc_dp1[of p y]
        by    auto
    next
      fix n
      assume *:
        "\<And>m. m \<in> (nat \<circ> choose_dpth) ` (N x \<union> N y) \<Longrightarrow>
          n \<le> m"
      have "n \<le> inf_trunc_dp1 x"
        unfolding inf_trunc_dp1_def
      proof (intro cInf_greatest)
        fix m assume "m \<in> trunc_dp1 x ` N x"
        from this obtain p where "p \<in> N x" "m = trunc_dp1 x p" by blast
        with N_def trunc_dp1_def choose_dpth_def * show "n \<le> m"
          by (cases "p \<in> N y", fastforce, fastforce)
      qed (simp add: nempty(1))
      moreover have "n \<le> inf_trunc_dp1 y"
        unfolding inf_trunc_dp1_def
      proof (intro cInf_greatest)
        fix m assume "m \<in> trunc_dp1 y ` N y"
        from this obtain p where "p \<in> N y" "m = trunc_dp1 y p" by blast
        with N_def trunc_dp1_def choose_dpth_def * show "n \<le> m"
          by (cases "p \<in> N x", fastforce, fastforce)
      qed (simp add: nempty(2))
      ultimately
        show  "n \<le> min (inf_trunc_dp1 x) (inf_trunc_dp1 y)"
        by    auto
    qed (simp add: nempty(1))
    moreover from n0(1) have "inf_trunc_dp1 x = bdd_global_depth x"
      using     bdd_global_depthD_as_image
      unfolding N_def inf_trunc_dp1_def trunc_dp1_def dp1_def
      by        auto
    moreover from n0(2) have "inf_trunc_dp1 y = bdd_global_depth y"
      using     bdd_global_depthD_as_image
      unfolding N_def inf_trunc_dp1_def trunc_dp1_def dp1_def
      by        auto
    ultimately have
      "min (bdd_global_depth x) (bdd_global_depth y) =
        Inf ((nat \<circ> choose_dpth) ` (N x \<union> N y))"
      by presburger
    also have "\<dots> \<le> inf_trunc_dp1 (x + y)"
      unfolding inf_trunc_dp1_def
    proof (intro cINF_mono nempty(3))
      fix p assume p: "p \<in> N (x + y)"
      with N_def have nequiv0:
        "\<not> p_equal p (x + y) 0" "\<not> p_equal p x 0 \<or> \<not> p_equal p y 0"
        using add[of p x 0 y 0] by auto
      from nequiv0(2) consider
        "p_equal p x 0" | "p_equal p y 0" "\<not> p_equal p x 0" |
        (neither) "\<not> p_equal p x 0" "\<not> p_equal p y 0"
        by blast
      hence "(nat \<circ> choose_dpth) p \<le> trunc_dp1 (x + y) p"
      proof cases
        case neither with nequiv0(1) show "(nat \<circ> choose_dpth) p \<le> trunc_dp1 (x + y) p"
          using depth_nonarch
          by    (fastforce simp add: choose_dpth_def trunc_dp1_def dp1_def)
      qed (
        simp_all add: choose_dpth_def trunc_dp1_def dp1_def depth_add_equiv0_left
                      depth_add_equiv0_right
      )
      moreover from N_def nequiv0(2) have "p \<in> N x \<union> N y" by force
      ultimately show
        "\<exists>q\<in>N x \<union> N y. (nat \<circ> choose_dpth) q \<le> trunc_dp1 (x + y) p"
        by blast
    qed simp
    finally show ?thesis
      using that N_def inf_trunc_dp1_def trunc_dp1_def dp1_def bdd_global_depthD_as_image by simp
  qed simp_all
qed

definition bdd_global_dist :: "'b \<Rightarrow> 'b \<Rightarrow> real" where
  "bdd_global_dist x y =
    (if globally_p_equal x y then 0 else inverse (2 ^ bdd_global_depth (x - y)))"

lemma bdd_global_dist_eqD [simp]: "bdd_global_dist x y = 0" if "globally_p_equal x y"
  using that unfolding bdd_global_dist_def by simp

lemma bdd_global_distD:
  "bdd_global_dist x y = inverse (2 ^ bdd_global_depth (x - y))" if "\<not> globally_p_equal x y"
  using that unfolding bdd_global_dist_def by fastforce

lemma bdd_global_dist_cong:
  "bdd_global_dist w x = bdd_global_dist y z"
  if "globally_p_equal w y" and "globally_p_equal x z"
proof (cases "globally_p_equal w x")
  case True with that show ?thesis using globally_p_equal_cong using bdd_global_dist_eqD by metis
next
  case False with that show ?thesis
    using globally_p_equal_sym globally_p_equal_cong bdd_global_distD globally_p_equal_minus
          bdd_global_depth_cong[of "w - x" "y - z"]
    by    metis
qed

lemma bdd_global_dist_nonneg: "bdd_global_dist x y \<ge> 0"
  unfolding bdd_global_dist_def by auto

lemma bdd_global_dist_bdd: "bdd_global_dist x y \<le> 1"
  using     le_imp_inverse_le[of 1 "2 ^ bdd_global_depth (x - y)"]
  unfolding bdd_global_dist_def
  by        auto

lemma bdd_global_dist_lessI:
  "bdd_global_dist x y < e"
  if pos: "e > 0"
  and depth:
    "\<And>p. \<not> p_equal p x y \<Longrightarrow>
      p_depth p (x - y) \<ge> \<lfloor>log 2 (inverse e)\<rfloor>"
proof (cases "e > 1")
  case True
  moreover have "bdd_global_dist x y \<le> 1" by (rule bdd_global_dist_bdd)
  ultimately show ?thesis by linarith
next
  case False
  hence small: "e \<le> 1" by linarith
  show ?thesis
  proof (cases "globally_p_equal x y")
    case False
    define d where "d \<equiv> \<lfloor>log 2 (inverse e)\<rfloor>"
    have
      "\<forall>p. \<not> p_equal p x y \<longrightarrow>
        nat (p_depth p (x - y) + 1) \<ge> nat (d + 1)"
    proof clarify
      fix p assume "\<not> p_equal p x y"
      with depth d_def have *: "p_depth p (x - y) \<ge> d" by simp
      moreover from pos d_def have "d \<ge> 0"
        using small le_imp_inverse_le zero_le_log_cancel_iff[of 2 "inverse e"] by force
      ultimately have "p_depth p (x - y) + 1 > 0" by linarith
      with * show "nat (p_depth p (x - y) + 1) \<ge> nat (d + 1)"
        using le_nat_iff[of "p_depth p (x - y) + 1" "nat d"] by simp
    qed
    with False have "bdd_global_depth (x - y) \<ge> nat (d + 1)"
      using conv_0 bdd_global_depth_greatest by auto
    with d_def have "bdd_global_depth (x - y) \<ge> d + 1" by auto
    with pos d_def have "e > inverse (2 ^ bdd_global_depth (x - y))"
      using real_of_int_floor_add_one_gt[of "log 2 (inverse e)"]
            log_pow_cancel[of 2 "bdd_global_depth (x - y)"]
            log_less_cancel_iff[of 2 "inverse e" "2 ^ bdd_global_depth (x - y)"]
            less_imp_inverse_less
      by    fastforce
    moreover from False have "bdd_global_dist x y = inverse (2 ^ bdd_global_depth (x - y))"
      using bdd_global_distD by force
    ultimately show ?thesis by simp
  qed (simp add: pos)
qed

lemma bdd_global_dist_less_imp:
  "p_depth p (x - y) \<ge> \<lfloor>log 2 (inverse e)\<rfloor>"
  if "e > 0" and "e \<le> 1" and "\<not> p_equal p x y" and "bdd_global_dist x y < e"
proof-
  from that have "log 2 (inverse e) < bdd_global_depth (x - y)"
    using bdd_global_distD inverse_less_imp_less[of _ "inverse e"] log_less[of 2 "inverse e"]
    by    fastforce
  hence "\<lfloor>log 2 (inverse e)\<rfloor> < bdd_global_depth (x - y)" by linarith
  with that(3) have "\<lfloor>log 2 (inverse e)\<rfloor> < int (nat (p_depth p (x - y) + 1))"
    using conv_0 bdd_global_depth_le by fastforce
  moreover from that(1,2) have "\<lfloor>log 2 (inverse e)\<rfloor> \<ge> 0"
    using le_imp_inverse_le zero_le_log_cancel_iff[of 2 "inverse e"] by force
  ultimately show ?thesis by linarith
qed

lemma bdd_global_dist_less_pow2_iff:
  "bdd_global_dist x y < inverse (2 ^ n) \<longleftrightarrow>
    (\<forall>p. \<not> p_equal p x y \<longrightarrow> p_depth p (x - y) \<ge> int n)"
proof (cases "globally_p_equal x y")
  case False show ?thesis
  proof (standard, standard, clarify)
    fix p assume "\<not> p_equal p x y"
    moreover assume "bdd_global_dist x y < inverse (2 ^ n)"
    ultimately show "p_depth p (x - y) \<ge> int n"
      using le_imp_inverse_le[of 1 "2 ^ n"] bdd_global_dist_less_imp[of "inverse (2 ^ n)" p x y]
      by    force
  next
    assume "\<forall>p. \<not> p_equal p x y \<longrightarrow> p_depth p (x - y) \<ge> int n"
    thus "bdd_global_dist x y < inverse (2 ^ n)" by (auto intro: bdd_global_dist_lessI)
  qed
qed simp

lemma bdd_global_dist_sym: "bdd_global_dist x y = bdd_global_dist y x"
  using globally_p_equal_sym bdd_global_depth_diff unfolding bdd_global_dist_def by force

lemma bdd_global_dist_conv0: "bdd_global_dist x y = bdd_global_dist (x - y) 0"
  using globally_p_equal_conv_0 unfolding bdd_global_dist_def by simp

lemma bdd_global_dist_conv0': "bdd_global_dist x y = bdd_global_dist 0 (x - y)"
  using bdd_global_dist_conv0 bdd_global_dist_sym by simp

lemma bdd_global_dist_nonarch:
  "bdd_global_dist x y \<le> max (bdd_global_dist x z) (bdd_global_dist y z)"
proof (cases "globally_p_equal x y")
  case True thus ?thesis
    using bdd_global_dist_nonneg[of x z] bdd_global_dist_nonneg[of y z] by simp
next
  case xy: False show ?thesis
  proof (cases "globally_p_equal x z")
    case True thus ?thesis
      using bdd_global_dist_cong[of x z y y] bdd_global_dist_sym by auto
  next
    case xz: False show ?thesis
    proof (cases "globally_p_equal y z")
      case True thus ?thesis
        using bdd_global_dist_cong[of y z x x] bdd_global_dist_sym by auto
    next
      case False with xy xz show ?thesis
      proof (induct x y rule: linorder_wlog'[of "\<lambda>x. bdd_global_dist x z"])
        case (le x y)
        from le(2) have "\<not> globally_p_equal ((x - z) + (z - y)) 0"
          using globally_p_equal_conv_0[of x y] by fastforce
        moreover from le(1,3,4) have "bdd_global_depth (x - z) \<ge> bdd_global_depth (y - z)"
          using bdd_global_distD inverse_le_imp_le by auto
        ultimately have "bdd_global_depth (x - y) \<ge> bdd_global_depth (y - z)"
          using bdd_global_depth_nonarch[of "x - z" "z - y"] bdd_global_depth_diff[of y z] by auto
        with le(1,2,4)
          show  "bdd_global_dist x y \<le> max (bdd_global_dist x z) (bdd_global_dist y z)"
          using le_imp_inverse_le bdd_global_distD
          by    auto
      next
        case (sym x y)
        hence "bdd_global_dist y x \<le> max (bdd_global_dist y z) (bdd_global_dist x z)"
          using globally_p_equal_sym[of y x] by blast
        thus ?case using bdd_global_dist_sym max.commute by metis
      qed
    qed
  qed
qed

lemma bdd_global_dist_ball_multicentre:
  "{z. bdd_global_dist y z < e} = {z. bdd_global_dist x z < e}"
  if "bdd_global_dist x y < e"
proof-
  define B where "B \<equiv> \<lambda>x. {z. bdd_global_dist x z < e}"
  moreover have "\<And>x y. bdd_global_dist x y < e \<Longrightarrow> B y \<subseteq> B x"
    unfolding B_def
  proof clarify
    fix x y z
    assume "bdd_global_dist x y < e" and "bdd_global_dist y z < e"
    thus "bdd_global_dist x z < e"
      using bdd_global_dist_nonarch[of x z y] bdd_global_dist_sym by simp
  qed
  ultimately show ?thesis using that bdd_global_dist_sym by fastforce
qed

lemma bdd_global_dist_ball_at_0:
  "{z. bdd_global_dist 0 z < inverse (2 ^ n)} = global_depth_set (int n)"
  using bdd_global_dist_less_pow2_iff bdd_global_dist_sym unfolding global_depth_set_def by auto

lemma bdd_global_dist_ball_UNIV:
  "{z. bdd_global_dist x z < e} = UNIV" if "e > 1"
  using that bdd_global_dist_bdd order_le_less_subst1[of _ id 1 e] by fastforce

lemma bdd_global_dist_ball_at_0_normalize:
  "{z. bdd_global_dist 0 z < e} = global_depth_set (\<lfloor>log 2 (inverse e)\<rfloor>)"
  if "e > 0" and "e \<le> 1"
  using     that bdd_global_dist_less_imp bdd_global_dist_sym bdd_global_dist_lessI
  unfolding global_depth_set_def
  by        fastforce

lemma bdd_global_dist_ball_translate:
  "{z. bdd_global_dist x z < e} = x +o {z. bdd_global_dist 0 z < e}"
  unfolding elt_set_plus_def
proof safe
  fix y assume "bdd_global_dist x y < e"
  hence "bdd_global_dist 0 (y - x) < e"
    using bdd_global_dist_sym bdd_global_dist_conv0' by presburger
  moreover have "y = x + (y - x)" by auto
  ultimately show "\<exists>b\<in>{z. bdd_global_dist 0 z < e}. y = x + b" by fast
next
  fix y assume "bdd_global_dist 0 y < e"
  thus "bdd_global_dist x (x + y) < e"
    using bdd_global_dist_conv0'[of "x + y" x] bdd_global_dist_sym by auto
qed

lemma bdd_global_dist_left_translate_continuous:
  "bdd_global_dist (x + y) (x + z) < e" if "bdd_global_dist y z < e"
  using that bdd_global_dist_conv0[of y z] bdd_global_dist_conv0[of "x + y" "x + z"] by simp

lemma bdd_global_dist_right_translate_continuous:
  "bdd_global_dist (y + x) (z + x) < e" if "bdd_global_dist y z < e"
  using that bdd_global_dist_conv0[of y z] bdd_global_dist_conv0[of "y + x" "z + x"] by simp

definition global_cauchy_condition ::
  "(nat \<Rightarrow> 'b) \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> bool"
  where
    "global_cauchy_condition X n K =
      (\<forall>k1\<ge>K. \<forall>k2\<ge>K. \<forall>p.
        \<not> p_equal p (X k1) (X k2) \<longrightarrow> nat (p_depth p (X k1 - X k2)) > n
      )"

lemma global_cauchy_conditionI:
  "global_cauchy_condition X n K"
  if
    "\<And>p k k'. k \<ge> K \<Longrightarrow> k' \<ge> K \<Longrightarrow>
      \<not> p_equal p (X k) (X k') \<Longrightarrow> nat (p_depth p (X k - X k')) > n"
  using that unfolding global_cauchy_condition_def by blast

lemma global_cauchy_conditionD:
  "nat (p_depth p (X k - X k')) > n"
  if  "global_cauchy_condition X n K" and "k \<ge> K" and "k' \<ge> K"
  and "\<not> p_equal p (X k) (X k')"
  using that unfolding global_cauchy_condition_def by blast

lemma global_cauchy_condition_mono_seq_tail:
  "global_cauchy_condition X n K \<Longrightarrow> global_cauchy_condition X n K'"
  if "K' \<ge> K"
  using that unfolding global_cauchy_condition_def by auto

lemma global_cauchy_condition_mono_depth:
  "global_cauchy_condition X n K \<Longrightarrow> global_cauchy_condition X m K"
  if "m \<le> n"
  using that unfolding global_cauchy_condition_def by fastforce

abbreviation "globally_cauchy X \<equiv> (\<forall>n. \<exists>K. global_cauchy_condition X n K)"

lemma global_cauchy_condition_LEAST:
  "global_cauchy_condition X n (LEAST K. global_cauchy_condition X n K)" if "globally_cauchy X"
  using that Least1I[OF ex_ex1_least_nat_le] by blast

lemma global_cauchy_condition_LEAST_mono:
  "(LEAST K. global_cauchy_condition X m K) \<le> (LEAST K. global_cauchy_condition X n K)"
  if "globally_cauchy X" and "m \<le> n"
  using that least_le_least[OF ex_ex1_least_nat_le ex_ex1_least_nat_le]
        global_cauchy_condition_mono_depth
  by    force

definition bdd_global_uniformity :: "('b \<times> 'b) filter"
  where "bdd_global_uniformity = (INF e\<in>{0 <..}. principal {(x, y). bdd_global_dist x y < e})"

end (* context p_equality_depth *)

context global_p_equal_depth
begin

sublocale metric_space_by_bdd_depth:
  metric_space bdd_global_dist bdd_global_uniformity
    "\<lambda>U. \<forall>x\<in>U.
      eventually (\<lambda>(x', y). x' = x \<longrightarrow> y \<in> U) bdd_global_uniformity"
proof
  fix x y z
  define dxy dxz dyz
    where "dxy \<equiv> bdd_global_dist x y"
    and   "dxz \<equiv> bdd_global_dist x z"
    and   "dyz \<equiv> bdd_global_dist y z"
  hence "dxy \<le> max dxz dyz" using bdd_global_dist_nonarch by metis
  also from dxz_def dyz_def have "\<dots> \<le> max dxz dyz + min dxz dyz"
    using bdd_global_dist_def by auto
  finally show "dxy \<le> dxz + dyz" by auto
  from dxy_def show "(dxy = 0) = (x = y)" using global_eq_iff unfolding bdd_global_dist_def by simp
qed (simp only: bdd_global_uniformity_def, simp)

lemma nonneg_global_depth_set_LIMSEQ_closed:
  "x \<in> global_depth_set (int n)"
  if  lim: "metric_space_by_bdd_depth.LIMSEQ X x"
  and seq: "\<forall>\<^sub>F k in sequentially. X k \<in> global_depth_set (int n)"
proof (intro global_depth_setI)
  fix p assume p: "\<not> p_equal p x 0"
  from seq obtain K where K: "\<forall>k\<ge>K. X k \<in> global_depth_set (int n)"
    using eventually_sequentially by fastforce
  from lim have "\<forall>\<^sub>F k in sequentially. bdd_global_dist (X k) x < inverse (2 ^ n)"
    using metric_space_by_bdd_depth.tendstoD[of X x sequentially "inverse (2 ^ n)"] by fastforce
  from this obtain K' :: nat
    where K': "\<forall>k\<ge>K'. bdd_global_dist (X k) x < inverse (2 ^ n)"
    using eventually_sequentially
    by    meson
  define m where "m \<equiv> max K K'"
  consider
    (eq) "p_equal p (X m) x" |
    (0)  "\<not> p_equal p (X m) x"   "p_equal p (X m) 0" |
    (n0) "\<not> p_equal p (X m) x" "\<not> p_equal p (X m) 0"
    by blast
  thus "p_depth p x \<ge> int n"
  proof cases
    case eq
    moreover from this K m_def have "X m \<in> global_depth_set (int n)" by auto
    ultimately show ?thesis using p trans_right global_depth_setD depth_equiv by metis
  next
    case 0 with K' m_def show ?thesis
      using bdd_global_dist_less_pow2_iff[of "X m" x n] depth_diff_equiv0_left by auto
  next
    case n0
    with p K K' m_def show ?thesis
      using bdd_global_dist_less_pow2_iff[of "X m" x n] global_depth_setD[of p "X m" "int n"]
            depth_pre_nonarch_diff_right[of p x "X m"]
      by    force
  qed
qed

lemma globally_cauchy_vs_bdd_metric_Cauchy:
  "globally_cauchy X = metric_space_by_bdd_depth.Cauchy X" for X :: "nat \<Rightarrow> 'b"
proof
  assume X: "globally_cauchy X" show "metric_space_by_bdd_depth.Cauchy X"
  proof (intro metric_space_by_bdd_depth.metric_CauchyI)
    fix e :: real assume pos: "e > 0"
    show "\<exists>M. \<forall>m\<ge>M. \<forall>n\<ge>M. bdd_global_dist (X m) (X n) < e"
    proof (cases "e > 1")
      case True
      hence "\<forall>m\<ge>0. \<forall>n\<ge>0. bdd_global_dist (X m) (X n) < e"
        using bdd_global_dist_bdd order_le_less_subst1[of _ id 1 e] by fastforce
      thus ?thesis by blast
    next
      case False
      hence small: "e \<le> 1" by simp
      define d where "d \<equiv> \<lfloor>log 2 (inverse e)\<rfloor>"
      from X obtain M where M: "global_cauchy_condition X (nat d) M" by fast
      have "\<forall>m\<ge>M. \<forall>n\<ge>M. bdd_global_dist (X m) (X n) < e"
      proof (clarify, intro bdd_global_dist_lessI pos)
        fix m n :: nat and p :: 'a
        assume "m \<ge> M" and "n \<ge> M" and "\<not> p_equal p (X m) (X n)"
        with M have "nat (p_depth p (X m - X n)) > nat d" using global_cauchy_conditionD by blast
        moreover from d_def pos small have "d \<ge> 0"
          using le_imp_inverse_le zero_le_log_cancel_iff[of 2 "inverse e"] by force
        ultimately show "p_depth p (X m - X n) \<ge> \<lfloor>log 2 (inverse e)\<rfloor>"
          using d_def by simp
      qed
      thus ?thesis by blast
    qed
  qed
next
  assume X: "metric_space_by_bdd_depth.Cauchy X" show "globally_cauchy X"
  proof
    fix n
    from X obtain M
      where M:
        "\<forall>m\<ge>M. \<forall>m'\<ge>M. bdd_global_dist (X m) (X m') < inverse (2 ^ Suc n)"
      using metric_space_by_bdd_depth.metric_CauchyD[of X "inverse (2 ^ Suc n)"]
      by    auto
    hence "global_cauchy_condition X n M"
      using bdd_global_dist_less_pow2_iff[of _ _ "Suc n"]
      by    (fastforce intro: global_cauchy_conditionI)
    thus "\<exists>M. global_cauchy_condition X n M" by fast
  qed
qed

end (* context global_p_equal_depth *)

context global_p_equal_depth_no_zero_divisors
begin

lemma bdd_global_dist_bdd_mult_continuous:
  "bdd_global_dist (w * x) (w * y) < e"
  if  pos  : "e > 0"
  and bdd  : "\<forall>p. \<not> p_equal p w 0 \<longrightarrow> p_depth p w \<ge> n"
  and input: "bdd_global_dist x y < min (e * 2 powi (n - 1)) 1"
proof (cases "e > 1", use bdd_global_dist_ball_UNIV in blast, intro bdd_global_dist_lessI pos)
  case False
  fix p assume p: "\<not> p_equal p (w * x) (w * y)"
  from p have w: "\<not> p_equal p w 0"
    using mult_0_left cong[of p 0 "w * x" 0 "w * y"] sym by force
  from p have xy: "\<not> p_equal p x y" using mult_left by force
  from p have wxy: "\<not> p_equal p (w * (x - y)) 0"
    using conv_0 right_diff_distrib[of w x y] by auto
  define d' where "d' \<equiv> e * 2 powi (n - 1)"
  define d  where "d  \<equiv> min d' 1"
  define m  where "m  \<equiv> \<lfloor>log 2 (inverse d)\<rfloor>"
  from pos d_def d'_def have "d > 0" "d \<le> 1" by auto
  with input m_def d_def d'_def have "m \<le> p_depth p (x - y)"
    using xy bdd_global_dist_less_imp[of d p x y] by fast
  with bdd have *: "n + m \<le> p_depth p (w * x - w * y)"
    using w wxy right_diff_distrib[of w x y] depth_mult_additive[of p w "x - y"]
          bdd_global_depth_le[of p w]
    by    force
  moreover have "n + m \<ge> log 2 (inverse e)"
  proof (cases "e * 2 powi (n - 1) < 1")
    case True
    moreover from m_def have "real_of_int (n + m) \<ge> real_of_int n + (- log 2 d - 1)"
      using real_of_int_floor_ge_diff_one log_inverse by fastforce
    ultimately show ?thesis using d_def d'_def pos by (simp add: log_mult log_inverse algebra_simps)
  next
    case False
    moreover from this pos have "log 2 (e * 2 powi (n - 1)) \<ge> 0"
      by (simp add: le_imp_inverse_le log_mono log_inverse)
    ultimately show ?thesis using pos m_def d_def d'_def
    by (fastforce simp add: log_mult log_inverse)
  qed
  ultimately show  "p_depth p (w * x - w * y) \<ge> \<lfloor>log 2 (inverse e)\<rfloor>" by linarith
qed

lemma bdd_global_dist_limseq_bdd_mult:
  "metric_space_by_bdd_depth.LIMSEQ (\<lambda>k. w * X k) (w * x)"
  if  bdd: "\<forall>p. \<not> p_equal p w 0 \<longrightarrow> p_depth p w \<ge> n"
  and seq: "metric_space_by_bdd_depth.LIMSEQ X x"
proof
  fix e :: real assume e: "e > 0"
  define d where "d \<equiv> min (e * 2 powi (n - 1)) 1"
  with e have d: "d > 0" by auto
  with seq obtain K :: nat where "\<forall>k\<ge>K. bdd_global_dist (X k) x < d"
    using metric_space_by_bdd_depth.tendstoD[of X x] eventually_sequentially by meson
  with bdd e d_def have "\<forall>k\<ge>K. bdd_global_dist (w * X k) (w * x) < e"
    using bdd_global_dist_bdd_mult_continuous by blast
  thus "\<forall>\<^sub>F k in sequentially. bdd_global_dist (w * X k) (w * x) < e"
    using eventually_sequentially by blast
qed

end (* context global_p_equal_depth_no_zero_divisors *)

context global_p_equal_depth_div_inv_w_inj_index_consts
begin

lemma bdd_global_dist_limseq_global_uniformizer_powi_mult:
  "metric_space_by_bdd_depth.LIMSEQ
    (\<lambda>k. global_uniformizer powi n * X k) (global_uniformizer powi n * x)"
  if "metric_space_by_bdd_depth.LIMSEQ X x"
  using that bdd_global_dist_limseq_bdd_mult[of _ n] p_depth_global_uniformizer_powi by auto

lemma global_depth_set_LIMSEQ_closed:
  "x \<in> global_depth_set n"
  if  lim  : "metric_space_by_bdd_depth.LIMSEQ X x"
  and depth: "\<forall>\<^sub>F k in sequentially. X k \<in> global_depth_set n"
proof-
  define Y and y
    where "Y \<equiv> \<lambda>k. global_uniformizer powi (-n) * X k"
    and   "y \<equiv> global_uniformizer powi (-n) * x"
  from depth Y_def have "\<forall>\<^sub>F k in sequentially. Y k \<in> global_depth_set 0"
    using global_depth_set_eq_global_uniformizer_coset'[of n] eventually_sequentially by auto
  with Y_def y_def lim have "y \<in> global_depth_set 0"
    using bdd_global_dist_limseq_global_uniformizer_powi_mult
          nonneg_global_depth_set_LIMSEQ_closed[of Y y 0]
    by    simp
  moreover from y_def have "global_uniformizer powi n * y = x"
    using global_uniformizer_powi_add[of n "-n"] by (simp add: ac_simps)
  ultimately show ?thesis
    using global_depth_set_eq_global_uniformizer_coset[of n] by blast
qed

end (* context global_p_equality_w_inj_index_consts *)


subsection \<open>Notation\<close>

consts
  p_equal :: "'a \<Rightarrow> 'b \<Rightarrow> 'b \<Rightarrow> bool"
  globally_p_equal ::
    "'b \<Rightarrow> 'b \<Rightarrow> bool"
    ("(_/ \<simeq>\<^sub>\<forall>\<^sub>p/ _)" [51, 51] 50)
  p_restrict :: "'b \<Rightarrow> ('a \<Rightarrow> bool) \<Rightarrow> 'b" (infixl "prestrict" 70)
  p_depth :: "'a \<Rightarrow> 'b \<Rightarrow> int"
  p_depth_set :: "'a \<Rightarrow> int \<Rightarrow> 'b set" ("\<P>\<^sub>@\<^sub>_\<^sup>_")
  global_depth_set :: "int \<Rightarrow> 'b set" ("\<P>\<^sub>\<forall>\<^sub>p\<^sup>_")
  global_unfrmzr_pows :: "('a \<Rightarrow> 'c) \<Rightarrow> 'b"

abbreviation p_equal_notation :: "'b \<Rightarrow> 'a \<Rightarrow> 'b \<Rightarrow> bool"
  ("(_/ \<simeq>\<^sub>_/ _)" [51, 51, 51] 50)
  where "p_equal_notation x p y \<equiv> p_equal p x y"

abbreviation p_nequal_notation :: "'b \<Rightarrow> 'a \<Rightarrow> 'b \<Rightarrow> bool"
  ("(_/ \<not>\<simeq>\<^sub>_/ _)" [51, 51, 51] 50)
  where "p_nequal_notation x p y \<equiv> \<not> p_equal p x y"

abbreviation p_depth_notation :: "'b \<Rightarrow> 'a \<Rightarrow> int"
  ("(_\<degree>\<^sup>_)" [51, 51] 50)
  where "p_depth_notation x p \<equiv> p_depth p x"

abbreviation p_depth_set_0_notation :: "'a \<Rightarrow> 'b set" ("\<O>\<^sub>@\<^sub>_")
  where "p_depth_set_0_notation p \<equiv> p_depth_set p 0"

abbreviation p_depth_set_1_notation :: "'a \<Rightarrow> 'b set" ("\<P>\<^sub>@\<^sub>_")
  where "p_depth_set_1_notation p \<equiv> p_depth_set p 1"

abbreviation global_depth_set_0_notation :: "'b set" ("\<O>\<^sub>\<forall>\<^sub>p")
  where "global_depth_set_0_notation \<equiv> global_depth_set 0"

abbreviation global_depth_set_1_notation :: "'b set" ("\<P>\<^sub>\<forall>\<^sub>p")
  where "global_depth_set_1_notation \<equiv> global_depth_set 1"

abbreviation "\<pp> \<equiv> global_unfrmzr_pows"

end (* theory *)
