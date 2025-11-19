(*  Title:       Computational p-Adics: Product of All p-Adic Fields
    Author:      Jeremy Sylvestre <jeremy.sylvestre at ualberta.ca>, 2025
    Maintainer:  Jeremy Sylvestre <jeremy.sylvestre at ualberta.ca>
*)


theory pAdic_Product

imports
  FLS_Prime_Equiv_Depth
  "HOL-Computational_Algebra.Fraction_Field"
  "HOL-Analysis.Elementary_Metric_Spaces"

begin


section \<open>p-Adic fields as equivalence classes of sequences of formal Laurent series\<close>


subsection \<open>Preliminaries\<close>

lemma inj_on_vimage_image_eq:
  "(f -` (f ` B)) \<inter> A = B" if "inj_on f A" and "B \<subseteq> A"
  using that unfolding inj_on_def by fast


subsection \<open>The type definition as a quotient\<close>

quotient_type (overloaded) 'a p_adic_prod
  = "'a::nontrivial_factorial_idom fls_pseq" / globally_p_equal
  by (simp, rule p_equality_depth_fls_pseq.globally_p_equal_equivp)

lemmas  rep_p_adic_prod_inverse              = Quotient3_abs_rep[OF Quotient3_p_adic_prod]
  and   p_adic_prod_lift_globally_p_equal    = Quotient3_rel_abs[OF Quotient3_p_adic_prod]
  and   globally_p_equal_fls_pseq_equals_rsp = equals_rsp[OF Quotient3_p_adic_prod]
  and   p_adic_prod_eq_iff
    = Quotient3_rel_rep[OF Quotient3_p_adic_prod, symmetric]
  and   globally_p_equal_fls_pseq_rep_p_adic_prod_refl
    = Quotient3_rep_reflp[OF Quotient3_p_adic_prod]
  and globally_p_equal_fls_pseq_rep_abs_p_adic_prod
    = rep_abs_rsp[OF Quotient3_p_adic_prod] rep_abs_rsp_left[OF Quotient3_p_adic_prod]

lemma p_adic_prod_globally_p_equal_self:
  "(rep_p_adic_prod (abs_p_adic_prod r)) \<simeq>\<^sub>\<forall>\<^sub>p r"
  using Quotient3_rep_abs[OF Quotient3_p_adic_prod]
        p_equality_depth_fls_pseq.globally_p_equal_refl
  by    auto

lemma rep_p_adic_prod_p_equal_self: "rep_p_adic_prod (abs_p_adic_prod r) \<simeq>\<^sub>p r"
  for p :: "'a::nontrivial_factorial_idom prime" and r :: "'a fls_pseq"
  using p_adic_prod_globally_p_equal_self p_equality_depth_fls_pseq.globally_p_equalD by auto

lemma rep_p_adic_prod_set_inverse: "abs_p_adic_prod ` (rep_p_adic_prod ` A) = A"
proof
  show "abs_p_adic_prod ` rep_p_adic_prod ` A \<subseteq> A"
  proof
    fix x assume "x \<in> abs_p_adic_prod ` rep_p_adic_prod ` A"
    from this obtain a where "a \<in> A" "x = abs_p_adic_prod (rep_p_adic_prod a)" by fast
    thus "x \<in> A" using rep_p_adic_prod_inverse by metis
  qed
  show "A \<subseteq> abs_p_adic_prod ` rep_p_adic_prod ` A"
  proof
    fix a assume "a \<in> A"
    thus "a \<in> abs_p_adic_prod ` rep_p_adic_prod ` A"
      using rep_p_adic_prod_inverse[of a] by force
  qed
qed

lemma p_adic_prod_cases [case_names abs_p_adic_prod, cases type: p_adic_prod]:
  C if "\<And>X. x = abs_p_adic_prod X \<Longrightarrow> C"
  by (metis that rep_p_adic_prod_inverse)

lemmas  two_p_adic_prod_cases   = p_adic_prod_cases[case_product p_adic_prod_cases]
  and   three_p_adic_prod_cases =
    p_adic_prod_cases[case_product p_adic_prod_cases[case_product p_adic_prod_cases]]

lemma p_adic_prod_reduced_cases [case_names abs_p_adic_prod]:
  fixes x :: "'a::nontrivial_euclidean_ring_cancel p_adic_prod"
  obtains X where "x = abs_p_adic_prod X" and "\<forall>p. (X p) pmod p = X p"
proof (cases x)
  case (abs_p_adic_prod X)
  define Y where "Y \<equiv> (\<lambda>p. (X p) pmod p)"
  with abs_p_adic_prod have "x = abs_p_adic_prod Y"
    using fls_pseq_globally_reduced p_adic_prod_lift_globally_p_equal by blast
  moreover from Y_def have "\<forall>p. (Y p) pmod p = Y p" by fastforce
  ultimately show ?thesis using that by blast
qed

lemma p_adic_prod_unique_rep:
  "\<exists>!X. x = abs_p_adic_prod X \<and> (\<forall>p. (X p) pmod p = X p)"
  for x :: "'a::nontrivial_euclidean_ring_cancel p_adic_prod"
proof (intro ex_ex1I, safe)
  obtain X where "x = abs_p_adic_prod X \<and> (\<forall>p. (X p) pmod p = X p)"
    using p_adic_prod_reduced_cases by meson
  thus "\<exists>X. x = abs_p_adic_prod X \<and> (\<forall>p. X p pmod p = X p)" by fast
next
  fix X X' :: "'a fls_pseq"
  assume  "\<forall>p. X  p pmod p = X  p"
    and   "\<forall>p. X' p pmod p = X' p"
    and   "abs_p_adic_prod X = abs_p_adic_prod X'"
  thus "X = X'" using p_adic_prod.abs_eq_iff[of X X'] fls_pmod_cong by fastforce
qed

abbreviation
  "reduced_rep_p_adic_prod x \<equiv>
    (THE X. x = abs_p_adic_prod X \<and> (\<forall>p. (X p) pmod p = X p))"

lemma reduced_rep_p_adic_prod_is_rep:
  "x = abs_p_adic_prod (reduced_rep_p_adic_prod x)"
  for x :: "'a::nontrivial_euclidean_ring_cancel p_adic_prod"
  using theI'[OF p_adic_prod_unique_rep] by fast

lemma reduced_rep_p_adic_prod_is_reduced:
  "(reduced_rep_p_adic_prod x p) pmod p = reduced_rep_p_adic_prod x p"
  for p :: "'a::nontrivial_euclidean_ring_cancel prime" and X :: "'a p_adic_prod"
  using theI'[OF p_adic_prod_unique_rep] by fast

lemma abs_p_adic_prod_inverse:
  "reduced_rep_p_adic_prod (abs_p_adic_prod X) = X" if "\<forall>p. (X p) pmod p = X p"
  for X :: "'a::nontrivial_euclidean_ring_cancel fls_pseq"
  by (intro the1_equality p_adic_prod_unique_rep, simp add: that)

lemma p_adic_prod_seq_cases [case_names abs_p_adic_prod]:
  C if "\<And>F. X = (\<lambda>n. abs_p_adic_prod (F n)) \<Longrightarrow> C"
proof-
  define F where "F \<equiv> \<lambda>n. rep_p_adic_prod (X n)"
  hence "X = (\<lambda>n. abs_p_adic_prod (F n))"
    using rep_p_adic_prod_inverse by metis
  with that show C by auto
qed

lemma p_adic_prod_seq_reduced_cases [case_names abs_p_adic_prod]:
  fixes X :: "nat \<Rightarrow> 'a::nontrivial_euclidean_ring_cancel p_adic_prod"
  obtains F
    where "X = (\<lambda>n. abs_p_adic_prod (F n))"
    and   "\<forall>(n::nat) (p::'a prime). (F n p) pmod p = F n p"
proof-
  define F where "F \<equiv> \<lambda>n. reduced_rep_p_adic_prod (X n)"
  from F_def have "X = (\<lambda>n. abs_p_adic_prod (F n))"
    using reduced_rep_p_adic_prod_is_rep by blast
  moreover from F_def have "\<forall>(n::nat) (p::'a prime). (F n p) pmod p = F n p"
    using reduced_rep_p_adic_prod_is_reduced by blast
  ultimately show thesis using that by simp
qed


subsection \<open>Algebraic instantiations\<close>

text \<open>The product of p-adic fields form a ring.\<close>

instantiation p_adic_prod :: (nontrivial_factorial_idom) comm_ring_1
begin

lift_definition zero_p_adic_prod :: "'a p_adic_prod" is "0::'a fls_pseq" .

lift_definition one_p_adic_prod :: "'a p_adic_prod" is "1::'a fls_pseq" .

lift_definition plus_p_adic_prod ::
  "'a p_adic_prod \<Rightarrow> 'a p_adic_prod \<Rightarrow> 'a p_adic_prod"
  is "\<lambda>X Y. X + Y"
  using p_equality_depth_fls_pseq.globally_p_equal_add by force

lift_definition uminus_p_adic_prod :: "'a p_adic_prod \<Rightarrow> 'a p_adic_prod"
  is "\<lambda>X. - X"
using p_equality_depth_fls_pseq.globally_p_equal_uminus by auto

lift_definition minus_p_adic_prod ::
  "'a p_adic_prod \<Rightarrow> 'a p_adic_prod \<Rightarrow> 'a p_adic_prod"
  is "\<lambda>X Y. X - Y"
  using p_equality_depth_fls_pseq.globally_p_equal_minus by force

lift_definition times_p_adic_prod ::
  "'a p_adic_prod \<Rightarrow> 'a p_adic_prod \<Rightarrow> 'a p_adic_prod"
  is "\<lambda>X Y. X * Y"
  using p_equality_depth_fls_pseq.globally_p_equal_mult by fastforce

instance
proof
  fix a b c :: "'a p_adic_prod"
  show "a + b + c = a + (b + c)" by transfer (simp add: add.assoc)
  show "a + b = b + a" by transfer (simp add: add.commute)
  show "1 * a = a" by transfer simp
  show "0 + a = a" by transfer simp
  show "- a + a = 0" by transfer simp
  show "a - b = a + - b" by transfer simp
  show "a * b * c = a * (b * c)" by transfer (simp add: mult.assoc)
  show "(a + b) * c = a * c + b * c" by transfer (simp add: distrib_right)
  show "a * b = b * a" by transfer (simp add: mult.commute)
  have "\<not> (0::'a fls_pseq) \<simeq>\<^sub>\<forall>\<^sub>p (1::'a fls_pseq)"
    using p_equality_depth_fls_pseq.globally_p_equalD p_equal_fls_sym fls_1_not_p_equal_0
    by    fastforce
  thus "(0::'a p_adic_prod) \<noteq> (1::'a p_adic_prod)" by transfer simp
qed

end (* instantiation p_adic_prod :: comm_ring_1 *)

lemma pow_p_adic_prod_abs_eq:
  "(abs_p_adic_prod X) ^ n = abs_p_adic_prod (X ^ n)"
  for X :: "'a::nontrivial_factorial_idom fls_pseq"
proof (induct n)
  case 0
  have "(abs_p_adic_prod X) ^ 0 = (1 :: 'a p_adic_prod)" by auto
  moreover have "abs_p_adic_prod (X ^ 0) = (1 :: 'a p_adic_prod)"
    using one_p_adic_prod.abs_eq by simp
  ultimately show ?case by presburger
next
  case (Suc n) thus "(abs_p_adic_prod X) ^ Suc n = abs_p_adic_prod (X ^ Suc n)"
    using times_p_adic_prod.abs_eq by auto
qed

text \<open>We can create inverses at the nonzero places.\<close>

instantiation p_adic_prod ::
  (nontrivial_factorial_unique_euclidean_bezout) "{divide_trivial, inverse}"
begin

lift_definition divide_p_adic_prod ::
  "'a p_adic_prod \<Rightarrow> 'a p_adic_prod \<Rightarrow> 'a p_adic_prod"
  is "\<lambda>X Y. X * (Y\<inverse>\<^sup>\<forall>\<^sup>p)"
proof-
  fix X X' Y Y' :: "'a fls_pseq"
  assume "X \<simeq>\<^sub>\<forall>\<^sub>p X'" and "Y \<simeq>\<^sub>\<forall>\<^sub>p Y'"
  thus
    "X * (Y\<inverse>\<^sup>\<forall>\<^sup>p) \<simeq>\<^sub>\<forall>\<^sub>p
      X' * (Y'\<inverse>\<^sup>\<forall>\<^sup>p)"
    using globally_pinverse_cong[of Y Y'] p_equality_depth_fls_pseq.globally_p_equal_mult[of X X']
    by    fastforce
qed

lift_definition inverse_p_adic_prod :: "'a p_adic_prod \<Rightarrow> 'a p_adic_prod"
  is global_pinverse_fls_pseq
  by (rule globally_pinverse_cong)

instance
proof
  show "\<And>a::'a p_adic_prod. a div 0 = 0" by transfer (simp flip: zero_fun_def)
  show "\<And>a::'a p_adic_prod. a div 1 = a" by transfer (simp flip: one_fun_def)
  show "\<And>a::'a p_adic_prod. 0 div a = 0" by transfer (simp flip: zero_fun_def)
qed

end


subsection \<open>Equivalence and depth relative to a prime\<close>

overloading
  p_equal_p_adic_prod \<equiv>
    "p_equal :: 'a::nontrivial_factorial_idom prime \<Rightarrow> 'a p_adic_prod \<Rightarrow>
      'a p_adic_prod \<Rightarrow> bool"
  p_restrict_p_adic_prod \<equiv>
    "p_restrict :: 'a p_adic_prod \<Rightarrow>
      ('a prime \<Rightarrow> bool) \<Rightarrow> 'a p_adic_prod"
  p_depth_p_adic_prod \<equiv> "p_depth :: 'a prime \<Rightarrow> 'a p_adic_prod \<Rightarrow> int"
  global_unfrmzr_pows_p_adic_prod \<equiv>
    "global_unfrmzr_pows :: ('a prime \<Rightarrow> int) \<Rightarrow> 'a p_adic_prod"
begin

lift_definition p_equal_p_adic_prod ::
  "'a::nontrivial_factorial_idom prime \<Rightarrow>
    'a p_adic_prod \<Rightarrow> 'a p_adic_prod \<Rightarrow> bool"
  is p_equal
  by (
    simp only: globally_p_equal_fls_pseq_def,
    rule p_equality_depth_fls_pseq.globally_p_equal_transfer_equals_rsp, simp_all
  )

lift_definition p_restrict_p_adic_prod ::
  "'a::nontrivial_factorial_idom p_adic_prod \<Rightarrow>
    ('a prime \<Rightarrow> bool) \<Rightarrow> 'a p_adic_prod"
  is "\<lambda>X P p. if P p then X p else 0"
  using p_equality_depth_fls_pseq.globally_p_equalD by fastforce

lift_definition p_depth_p_adic_prod ::
  "'a::nontrivial_factorial_idom prime \<Rightarrow> 'a p_adic_prod \<Rightarrow> int"
  is p_depth
  by (
    simp only: globally_p_equal_fls_pseq_def,
    rule p_equality_depth_fls_pseq.globally_p_equal_p_depth
  )

lift_definition global_unfrmzr_pows_p_adic_prod ::
  "('a::nontrivial_factorial_idom prime \<Rightarrow> int) \<Rightarrow> 'a p_adic_prod"
  is global_unfrmzr_pows .

end  (* overloading *)

lemma p_equal_p_adic_prod_abs_eq0: "(abs_p_adic_prod X \<simeq>\<^sub>p 0) = (X \<simeq>\<^sub>p 0)"
  for   p :: "'a::nontrivial_factorial_idom prime" and X :: "'a fls_pseq"
  using p_equal_p_adic_prod.abs_eq[of p X "0::'a fls_pseq"]
  by    (simp add: zero_p_adic_prod.abs_eq)

lemma p_equal_p_adic_prod_abs_eq1: "(abs_p_adic_prod X \<simeq>\<^sub>p 1) = (X \<simeq>\<^sub>p 1)"
  for   p :: "'a::nontrivial_factorial_idom prime" and X :: "'a fls_pseq"
  using p_equal_p_adic_prod.abs_eq[of p X "1::'a fls_pseq"]
  by    (simp add: one_p_adic_prod.abs_eq)

global_interpretation p_equality_p_adic_prod:
  p_equality_no_zero_divisors_1
    "p_equal :: 'a::nontrivial_factorial_idom prime \<Rightarrow>
      'a p_adic_prod \<Rightarrow> 'a p_adic_prod \<Rightarrow> bool"
proof

  fix p :: "'a prime"

  define E :: "'a p_adic_prod \<Rightarrow> 'a p_adic_prod \<Rightarrow> bool"
    where "E \<equiv> p_equal p"

  show "equivp E"
    unfolding E_def p_equal_p_adic_prod_def
  proof-
    define  F :: "'a fls_pseq \<Rightarrow> 'a fls_pseq \<Rightarrow> bool"
      and   G :: "'a p_adic_prod \<Rightarrow> 'a p_adic_prod \<Rightarrow> bool"
      where "F \<equiv> p_equal p"
      and
        "G \<equiv>
          map_fun id (map_fun rep_p_adic_prod (map_fun rep_p_adic_prod id)) p_equal p"
    hence "G = (\<lambda>x y. F (rep_p_adic_prod x) (rep_p_adic_prod y))" by force
    with F_def show "equivp G" using equivp_transfer p_equality_depth_fls_pseq.equivp by fast
  qed

  show  "\<exists>x::'a p_adic_prod. x \<not>\<simeq>\<^sub>p 0"
    by (transfer, rule p_equality_depth_fls_pseq.nontrivial)

  fix x y :: "'a p_adic_prod"
  show  "(x \<simeq>\<^sub>p y) = (x - y \<simeq>\<^sub>p 0)"
  and   "y \<simeq>\<^sub>p 0 \<Longrightarrow> x * y \<simeq>\<^sub>p 0"
    by (
      transfer, rule p_equality_depth_fls_pseq.conv_0,
      transfer, rule p_equality_depth_fls_pseq.mult_0_right
    )

  assume "x \<not>\<simeq>\<^sub>p 0" and "y \<not>\<simeq>\<^sub>p 0"
  thus "x * y \<not>\<simeq>\<^sub>p 0"
    using p_depth_fls.no_zero_divisors[of p]
    by    (cases x, cases y)
          (auto simp add: p_equal_p_adic_prod_abs_eq0 times_p_adic_prod.abs_eq)

qed

overloading
  globally_p_equal_p_adic_prod \<equiv>
    "globally_p_equal ::
      'a::nontrivial_factorial_idom p_adic_prod \<Rightarrow> 'a p_adic_prod \<Rightarrow> bool"
begin

definition globally_p_equal_p_adic_prod ::
  "'a::nontrivial_factorial_idom p_adic_prod \<Rightarrow> 'a p_adic_prod \<Rightarrow> bool"
  where globally_p_equal_p_adic_prod_def[simp]:
    "globally_p_equal_p_adic_prod = p_equality_p_adic_prod.globally_p_equal"

end  (* overloading *)

global_interpretation global_p_depth_p_adic_prod:
  global_p_equal_depth_no_zero_divisors_w_inj_index_consts
    "p_equal :: 'a::nontrivial_factorial_idom prime \<Rightarrow>
      'a p_adic_prod \<Rightarrow> 'a p_adic_prod \<Rightarrow> bool"
    "p_restrict ::
      'a p_adic_prod \<Rightarrow> ('a prime \<Rightarrow> bool) \<Rightarrow> 'a p_adic_prod"
    "p_depth :: 'a prime \<Rightarrow> 'a p_adic_prod \<Rightarrow> int"
    "\<lambda>f. abs_p_adic_prod (\<lambda>p. fls_const (f p))"
    Rep_prime
proof (unfold_locales, fold globally_p_equal_p_adic_prod_def)

  fix p :: "'a prime"

  fix x y :: "'a p_adic_prod"

  show "x \<simeq>\<^sub>\<forall>\<^sub>p y \<Longrightarrow> x = y" by (simp, transfer, simp)

  fix P :: "'a prime \<Rightarrow> bool"
  show "P p \<Longrightarrow> x prestrict P \<simeq>\<^sub>p x" by transfer simp
  show "\<not> P p \<Longrightarrow> x prestrict P \<simeq>\<^sub>p 0" by transfer simp

  show "((0::'a p_adic_prod)\<degree>\<^sup>p) = 0" by transfer simp
  show "x \<simeq>\<^sub>p y \<Longrightarrow> (x\<degree>\<^sup>p) = (y\<degree>\<^sup>p)"
    by (transfer, rule p_equality_depth_fls_pseq.depth_equiv, simp)
  show   "(- x\<degree>\<^sup>p) = (x\<degree>\<^sup>p)"
    by (transfer, rule p_equality_depth_fls_pseq.depth_uminus)
  show
    "x \<not>\<simeq>\<^sub>p 0 \<Longrightarrow> (x\<degree>\<^sup>p) < (y\<degree>\<^sup>p)
      \<Longrightarrow> (x + y\<degree>\<^sup>p) = (x\<degree>\<^sup>p)"
    by (transfer, rule p_equality_depth_fls_pseq.depth_pre_nonarch(1), simp, simp)
  show
    "\<lbrakk>
      x \<not>\<simeq>\<^sub>p 0; x + y \<not>\<simeq>\<^sub>p 0;
      (x\<degree>\<^sup>p) = (y\<degree>\<^sup>p)
    \<rbrakk> \<Longrightarrow> (x\<degree>\<^sup>p) \<le> ((x + y)\<degree>\<^sup>p)"
    using p_equality_depth_fls_pseq.depth_pre_nonarch(2)[of p] by (transfer, simp add: mult.commute)
  show
    "x * y \<not>\<simeq>\<^sub>p 0 \<Longrightarrow>
      (x * y\<degree>\<^sup>p) = (x\<degree>\<^sup>p) + (y\<degree>\<^sup>p)"
    by (transfer, rule p_equality_depth_fls_pseq.depth_mult_additive, simp)

  define F :: "('a prime \<Rightarrow> 'a) \<Rightarrow> 'a p_adic_prod"
    where "F \<equiv> \<lambda>f. abs_p_adic_prod (\<lambda>p. fls_const (f p))"

  show "F 1 = 1" by (simp add: F_def one_p_adic_prod.abs_eq flip: one_fun_def)

  fix f g :: "'a prime \<Rightarrow> 'a"
  show  "F (f - g) = F f - F g"
    and "F (f * g) = F f * F g"
    and "(F f \<simeq>\<^sub>p 0) = (f p = 0)"
    and "((F f)\<degree>\<^sup>p) = int (pmultiplicity p (f p))"
    by  (simp_all
      add:  F_def fls_minus_const fun_diff_def minus_p_adic_prod.abs_eq times_p_adic_prod.abs_eq
            times_fun_def p_equal_p_adic_prod_abs_eq0 p_equal_fls_const_0_iff p_depth_const_def
            p_depth_p_adic_prod.abs_eq
      flip: p_depth_const
    )

qed (
  metis Rep_prime_inject injI, rule Rep_prime_n0, rule Rep_prime_not_unit,
  rule multiplicity_distinct_primes
)

lemma p_depth_p_adic_prod_diff_abs_eq:
  "((abs_p_adic_prod X - abs_p_adic_prod Y)\<degree>\<^sup>p) = ((X - Y)\<degree>\<^sup>p)"
  for p :: "'a::nontrivial_factorial_idom prime" and X Y :: "'a fls_pseq"
  using minus_p_adic_prod.abs_eq p_depth_p_adic_prod.abs_eq by metis

lemma p_depth_p_adic_prod_diff_abs_eq':
  "((abs_p_adic_prod X - abs_p_adic_prod Y)\<degree>\<^sup>p) = ((X p - Y p)\<degree>\<^sup>p)"
  for p :: "'a::nontrivial_factorial_idom prime" and X Y :: "'a fls_pseq"
  using p_depth_p_adic_prod_diff_abs_eq by auto

overloading
  p_depth_set_p_adic_prod \<equiv>
    "p_depth_set ::
      'a::nontrivial_factorial_idom prime \<Rightarrow> int \<Rightarrow> 'a p_adic_prod set"
  global_depth_set_p_adic_prod \<equiv>
    "global_depth_set :: int \<Rightarrow> 'a p_adic_prod set"
begin

definition p_depth_set_p_adic_prod ::
  "'a::nontrivial_factorial_idom prime \<Rightarrow> int \<Rightarrow> 'a p_adic_prod set"
  where p_depth_set_p_adic_prod_def[simp]:
    "p_depth_set_p_adic_prod = global_p_depth_p_adic_prod.p_depth_set"

definition global_depth_set_p_adic_prod ::
  "int \<Rightarrow> 'a::nontrivial_factorial_idom p_adic_prod set"
  where global_depth_set_p_adic_prod_def[simp]:
    "global_depth_set_p_adic_prod = global_p_depth_p_adic_prod.global_depth_set"

end

lemma p_depth_set_p_adic_prod_eq_projection:
  "((\<P>\<^sub>@\<^sub>p\<^sup>n) :: 'a p_adic_prod set) =
    abs_p_adic_prod ` (\<P>\<^sub>@\<^sub>p\<^sup>n)"
  for p :: "'a::nontrivial_factorial_idom prime"
proof safe
  fix x :: "'a p_adic_prod"
  assume x: "x \<in> \<P>\<^sub>@\<^sub>p\<^sup>n"
  show "x \<in> abs_p_adic_prod ` \<P>\<^sub>@\<^sub>p\<^sup>n"
  proof (cases x)
    case (abs_p_adic_prod X)
    with x have "X \<in> \<P>\<^sub>@\<^sub>p\<^sup>n"
      using p_depth_set_p_adic_prod_def global_p_depth_p_adic_prod.p_depth_setD
            p_equal_p_adic_prod_abs_eq0 p_depth_p_adic_prod.abs_eq
            p_equality_depth_fls_pseq.p_depth_setI p_depth_set_fls_pseq_def
      by    metis
    with abs_p_adic_prod show "x \<in> abs_p_adic_prod ` \<P>\<^sub>@\<^sub>p\<^sup>n" by fast
  qed
qed (
  metis p_equality_depth_fls_pseq.p_depth_setD p_depth_set_fls_pseq_def p_equal_p_adic_prod_abs_eq0
        p_depth_p_adic_prod.abs_eq p_depth_set_p_adic_prod_def
        global_p_depth_p_adic_prod.p_depth_setI
)

lemma global_depth_set_p_adic_prod_eq_projection:
  "((\<P>\<^sub>\<forall>\<^sub>p\<^sup>n) :: 'a p_adic_prod set) =
    abs_p_adic_prod ` (\<P>\<^sub>\<forall>\<^sub>p\<^sup>n)"
  for p :: "'a::nontrivial_factorial_idom prime"
proof safe
  fix x :: "'a p_adic_prod"
  assume x: "x \<in> \<P>\<^sub>\<forall>\<^sub>p\<^sup>n"
  show "x \<in> abs_p_adic_prod ` \<P>\<^sub>\<forall>\<^sub>p\<^sup>n"
  proof (cases x)
    case (abs_p_adic_prod X)
    with x have "X \<in> \<P>\<^sub>\<forall>\<^sub>p\<^sup>n"
      using global_depth_set_p_adic_prod_def global_p_depth_p_adic_prod.global_depth_setD
            p_equal_p_adic_prod_abs_eq0 p_depth_p_adic_prod.abs_eq
            p_equality_depth_fls_pseq.global_depth_setI global_depth_set_fls_pseq_def
      by    metis
    with abs_p_adic_prod show "x \<in> abs_p_adic_prod ` \<P>\<^sub>\<forall>\<^sub>p\<^sup>n"
      by fast
  qed
qed (
  metis p_equality_depth_fls_pseq.global_depth_setD global_depth_set_fls_pseq_def
        p_equal_p_adic_prod_abs_eq0 p_depth_p_adic_prod.abs_eq global_depth_set_p_adic_prod_def
        global_p_depth_p_adic_prod.global_depth_setI
)

context
  fixes x :: "'a::nontrivial_factorial_idom p_adic_prod"
begin

lemma p_adic_prod_p_restrict_depth:
  "(x prestrict P)\<degree>\<^sup>p = (if P p then x\<degree>\<^sup>p else 0)"
  for P :: "'a prime \<Rightarrow> bool"
  by (transfer, simp)

lemma p_adic_prod_global_depth_setI:
  "x \<in> \<P>\<^sub>\<forall>\<^sub>p\<^sup>n"
  if  "\<And>p::'a prime. x \<not>\<simeq>\<^sub>p 0 \<Longrightarrow> (x\<degree>\<^sup>p) \<ge> n"
  using that global_p_depth_p_adic_prod.global_depth_setI global_depth_set_p_adic_prod_def by auto

lemma p_adic_prod_global_depth_setI':
  "x \<in> \<P>\<^sub>\<forall>\<^sub>p\<^sup>n"
  if  "\<And>p::'a prime. (x\<degree>\<^sup>p) \<ge> n"
  using that global_p_depth_p_adic_prod.global_depth_setI' global_depth_set_p_adic_prod_def by auto

lemma p_adic_prod_global_depth_set_p_restrictI:
  "p_restrict x P \<in> \<P>\<^sub>\<forall>\<^sub>p\<^sup>n"
  if "\<And>p::'a prime. P p \<Longrightarrow> x \<in> \<P>\<^sub>@\<^sub>p\<^sup>n"
  using that global_p_depth_p_adic_prod.global_depth_set_p_restrictI
        global_depth_set_p_adic_prod_def
  by    auto

lemma p_adic_prod_p_depth_setI:
  "x \<in> \<P>\<^sub>@\<^sub>p\<^sup>n"
  if "x \<not>\<simeq>\<^sub>p 0 \<longrightarrow> (x\<degree>\<^sup>p) \<ge> n"
  for p :: "'a prime"
  using that global_p_depth_p_adic_prod.p_depth_setI p_depth_set_p_adic_prod_def by auto

end (* context nontrivial_factorial_idom *)

context
  fixes p :: "'a::nontrivial_euclidean_ring_cancel prime"
begin

lemma p_adic_prod_diff_depth_gt_equiv_trans:
  "((x - z)\<degree>\<^sup>p) > n"
  if  xy: "x \<simeq>\<^sub>p y"
  and yz: "y \<not>\<simeq>\<^sub>p z" "((y - z)\<degree>\<^sup>p) > n"
  for x y z :: "'a p_adic_prod"
proof (cases x y z  rule: three_p_adic_prod_cases)
  case (abs_p_adic_prod_abs_p_adic_prod_abs_p_adic_prod X Y Z)
  from xy abs_p_adic_prod_abs_p_adic_prod_abs_p_adic_prod(1,2)
    have XY: "X \<simeq>\<^sub>p Y" using p_equal_p_adic_prod.abs_eq by auto
  moreover from yz(1) abs_p_adic_prod_abs_p_adic_prod_abs_p_adic_prod(2,3)
    have YZ: "Y \<not>\<simeq>\<^sub>p Z" using p_equal_p_adic_prod.abs_eq by auto
  moreover from yz(2) abs_p_adic_prod_abs_p_adic_prod_abs_p_adic_prod(2,3)
    have "((Y p - Z p)\<degree>\<^sup>p) > n" using p_depth_p_adic_prod_diff_abs_eq' by metis
  ultimately have "\<forall>k\<le>n. ((X p) pmod p) $$ k = ((Z p) pmod p) $$ k"
    using fls_pmod_eq_pmod_iff[of "X p" p "Y p"] fls_pmod_diff_cancel_iff by fastforce
  moreover have "(X p) \<not>\<simeq>\<^sub>p (Z p)" using XY YZ p_equality_fls.trans_right by auto
  ultimately show "n < ((x - z)\<degree>\<^sup>p)"
    using abs_p_adic_prod_abs_p_adic_prod_abs_p_adic_prod(1,3) fls_pmod_diff_cancel_iff
          p_depth_p_adic_prod_diff_abs_eq'
    by    metis
qed

lemma p_adic_prod_diff_depth_gt0_equiv_trans:
  "((x - z)\<degree>\<^sup>p) > n"
  if "n \<ge> 0" and "x \<simeq>\<^sub>p y" and "((y - z)\<degree>\<^sup>p) > n"
  for x y z :: "'a p_adic_prod"
  using that p_equality_p_adic_prod.conv_0 p_adic_prod_diff_depth_gt_equiv_trans
        global_p_depth_p_adic_prod.depth_equiv_0[of p "y - z"]
  by    fastforce

lemma p_adic_prod_diff_depth_gt_trans:
  "((x - z)\<degree>\<^sup>p) > n"
  if  xy: "x \<not>\<simeq>\<^sub>p y" "((x - y)\<degree>\<^sup>p) > n"
  and yz: "y \<not>\<simeq>\<^sub>p z" "((y - z)\<degree>\<^sup>p) > n"
  and xz: "x \<not>\<simeq>\<^sub>p z"
  for x y z :: "'a p_adic_prod"
proof (cases x y z rule: three_p_adic_prod_cases)
  case (abs_p_adic_prod_abs_p_adic_prod_abs_p_adic_prod X Y Z)
  moreover from this xy(2) yz(2)
    have  "((X p - Y p)\<degree>\<^sup>p) > n"
    and   "((Y p - Z p)\<degree>\<^sup>p) > n"
    using p_depth_p_adic_prod_diff_abs_eq'
    by    (metis, metis)
  ultimately have "\<forall>k\<le>n. ((X p) pmod p) $$ k = ((Z p) pmod p) $$ k"
    using xy(1) yz(1) by (simp add: p_equal_p_adic_prod.abs_eq fls_pmod_diff_cancel_iff)
  with xz abs_p_adic_prod_abs_p_adic_prod_abs_p_adic_prod(1,3)
    show  "n < ((x - z)\<degree>\<^sup>p)"
    using p_equal_p_adic_prod.abs_eq[of p X Z] fls_pmod_diff_cancel_iff[of p "X p" "Z p"]
          p_depth_p_adic_prod_diff_abs_eq[of p X Z]
    by    simp
qed

lemma p_adic_prod_diff_depth_gt0_trans:
  "((x - z)\<degree>\<^sup>p) > n"
  if  "n \<ge> 0"
  and "((x - y)\<degree>\<^sup>p) > n"
  and "((y - z)\<degree>\<^sup>p) > n"
  and "x \<not>\<simeq>\<^sub>p z"
  for x y z :: "'a p_adic_prod"
  using that p_adic_prod_diff_depth_gt_trans
        p_equality_p_adic_prod.conv_0[of p x y] p_equality_p_adic_prod.conv_0[of p y z]
        global_p_depth_p_adic_prod.depth_equiv_0[of p "x - y"]
        global_p_depth_p_adic_prod.depth_equiv_0[of p "y - z"]
  by    auto

end (* context nontrivial_euclidean_ring_cancel *)

lemma p_adic_prod_diff_cancel_lead_coeff:
  "((inverse x - inverse y)\<degree>\<^sup>p) > -n"
  if  x : "x \<not>\<simeq>\<^sub>p 0" "x\<degree>\<^sup>p = n"
  and y : "y \<not>\<simeq>\<^sub>p 0" "y\<degree>\<^sup>p = n"
  and xy: "x \<not>\<simeq>\<^sub>p y" "((x - y)\<degree>\<^sup>p) > n"
  for p :: "'a::nontrivial_factorial_unique_euclidean_bezout prime"
  and x y :: "'a p_adic_prod"
proof (cases x y rule: two_p_adic_prod_cases)
  case (abs_p_adic_prod_abs_p_adic_prod X Y)
  with x(1) y(1) xy(1)
    have  "X \<not>\<simeq>\<^sub>p 0"
    and   "Y \<not>\<simeq>\<^sub>p 0"
    and   "X \<not>\<simeq>\<^sub>p Y"
    using p_equal_p_adic_prod_abs_eq0 p_equal_p_adic_prod.abs_eq
    by    (fast, fast, fast)
  moreover from abs_p_adic_prod_abs_p_adic_prod x(2) y(2) xy(2)
    have  "X\<degree>\<^sup>p = n"
    and   "Y\<degree>\<^sup>p = n"
    and   "((X - Y)\<degree>\<^sup>p) > n"
    using p_depth_p_adic_prod.abs_eq
    by    (metis, metis, metis minus_p_adic_prod.abs_eq)
  moreover from abs_p_adic_prod_abs_p_adic_prod have
    "((inverse x - inverse y)\<degree>\<^sup>p) =
      ((
        (X\<inverse>\<^sup>\<forall>\<^sup>p) -
        (Y\<inverse>\<^sup>\<forall>\<^sup>p)
      )\<degree>\<^sup>p)"
    using inverse_p_adic_prod.abs_eq[of X] inverse_p_adic_prod.abs_eq[of Y]
          p_depth_p_adic_prod_diff_abs_eq[of
            p "X\<inverse>\<^sup>\<forall>\<^sup>p" "Y\<inverse>\<^sup>\<forall>\<^sup>p"
          ]
    by    argo
  ultimately show ?thesis using global_pinverse_diff_cancel_lead_coeff by auto
qed

lemma global_unfrmzr_pows_p_adic_prod0:
  "(\<pp> (0 :: 'a::nontrivial_factorial_idom prime \<Rightarrow> int) :: 'a p_adic_prod) = 1"
  by (
    transfer,
    metis p_equality_depth_fls_pseq.globally_p_equal_refl globally_p_equal_fls_pseq_def
          global_unfrmzr_pows0_fls_pseq
  )

context
  fixes p :: "'a::nontrivial_factorial_idom prime"
begin

lemma global_unfrmzr_pows_p_adic_prod_nequiv0:
  "(\<pp> f :: 'a p_adic_prod) \<not>\<simeq>\<^sub>p 0" for f :: "'a prime \<Rightarrow> int"
  by (transfer, rule global_unfrmzr_pows_fls_pseq_nequiv0)

lemma global_unfrmzr_pows_p_adic_prod:
  "(\<pp> f :: 'a p_adic_prod)\<degree>\<^sup>p = f p" for f :: "'a prime \<Rightarrow> int"
  by (transfer, rule global_unfrmzr_pows_fls_pseq)

lemma global_unfrmzr_pows_p_adic_prod_depth_set:
  fixes   f :: "'a prime \<Rightarrow> int"
  defines "n \<equiv> f p"
  shows   "(\<pp> f :: 'a p_adic_prod) \<in> \<P>\<^sub>@\<^sub>p\<^sup>n"
  using p_adic_prod_p_depth_setI[of p] n_def global_unfrmzr_pows_p_adic_prod[of f] by force

lemma global_unfrmzr_pows_p_adic_prod_pequiv_iff:
  "((\<pp> f :: 'a p_adic_prod) \<simeq>\<^sub>p (\<pp> g)) = (f p = g p)"
  for f g :: "'a prime \<Rightarrow> int"
  by (transfer, rule global_unfrmzr_pows_fls_pseq_pequiv_iff)

end (* context nontrivial_factorial_idom *)

lemma global_unfrmzr_pows_p_adic_prod_global_depth_set:
  "(\<pp> f :: 'a p_adic_prod) \<in> \<P>\<^sub>\<forall>\<^sub>p\<^sup>n"
  if "\<forall>p. f p \<ge> n" for f :: "'a::nontrivial_factorial_idom prime \<Rightarrow> int"
  by (
    metis that global_depth_set_p_adic_prod_def global_p_depth_p_adic_prod.global_depth_setI
          global_unfrmzr_pows_p_adic_prod
  )

lemma global_unfrmzr_pows_p_adic_prod_global_depth_set_0:
  "(\<pp> (int \<circ> f) :: 'a p_adic_prod) \<in> \<O>\<^sub>\<forall>\<^sub>p"
  for f :: "'a::nontrivial_factorial_idom prime \<Rightarrow> nat"
  using global_unfrmzr_pows_p_adic_prod_global_depth_set[of 0 "int \<circ> f"] by simp

lemma global_unfrmzr_pows_prod_p_adic_prod:
  "(\<pp> f :: 'a p_adic_prod) * (\<pp> g) = \<pp> (f + g)"
  for f g :: "'a::nontrivial_factorial_idom prime \<Rightarrow> int"
  by (
    transfer, simp, standard,
    simp only: global_unfrmzr_pows_prod_fls_pseq p_equality_fls.refl flip: times_fun_apply
  )

context
  fixes p :: "'a::nontrivial_factorial_idom prime"
begin

lemma global_unfrmzr_pows_p_adic_prod_nzero:
  "(\<pp> f :: 'a p_adic_prod) \<not>\<simeq>\<^sub>p 0" for f :: "'a prime \<Rightarrow> int"
  by (transfer, rule global_unfrmzr_pows_fls_pseq_nzero)

lemma prod_w_global_unfrmzr_pows_p_adic_prod:
  "x \<not>\<simeq>\<^sub>p 0 \<Longrightarrow>
    (x * \<pp> f)\<degree>\<^sup>p = (x\<degree>\<^sup>p) + f p"
  for f :: "'a prime \<Rightarrow> int" and x :: "'a p_adic_prod"
  by (transfer, rule prod_w_global_unfrmzr_pows_fls_pseq, simp)

lemma p_adic_prod_normalize_depth:
  "(x * \<pp> (\<lambda>p::'a prime. -(x\<degree>\<^sup>p)))\<degree>\<^sup>p = 0"
  for x :: "'a p_adic_prod"
  by (transfer, rule normalize_depth_fls_pseq)

end (* context nontrivial_factorial_idom *)

lemma p_adic_prod_normalized_depth_product_equiv:
  "(x * \<pp> (\<lambda>p::'a prime. -(x\<degree>\<^sup>p))) *
    (y * \<pp> (\<lambda>p::'a prime. -(y\<degree>\<^sup>p))) =
      ((x * y) * \<pp> (\<lambda>p::'a prime. -((x * y)\<degree>\<^sup>p)))"
  for x y :: "'a::nontrivial_factorial_idom p_adic_prod"
proof transfer
  fix X Y :: "'a fls_pseq"
  define d :: "'a fls_pseq \<Rightarrow> 'a prime \<Rightarrow> int"
    where "d \<equiv> \<lambda>X p. - (X\<degree>\<^sup>p)"
  thus
    "(X * \<pp> (d X)) * (Y * \<pp> (d Y)) \<simeq>\<^sub>\<forall>\<^sub>p
      (X * Y * \<pp> (d (X * Y)))"
    using times_fun_apply p_equal_fls_pseq_def normalized_depth_fls_pseq_product_equiv by fastforce
qed

context
  fixes p :: "'a::nontrivial_factorial_idom prime"
begin

lemma trivial_global_unfrmzr_pows_p_adic_prod:
  "f p = 0 \<Longrightarrow> (\<pp> f :: 'a p_adic_prod) \<simeq>\<^sub>p 1"
  for f :: "'a prime \<Rightarrow> int"
  by (transfer, rule trivial_global_unfrmzr_pows_fls_pseq, simp)

lemma prod_w_trivial_global_unfrmzr_pows_p_adic_prod:
  "f p = 0 \<Longrightarrow> x * \<pp> f \<simeq>\<^sub>p x"
  for f :: "'a prime \<Rightarrow> int" and x :: "'a p_adic_prod"
  by (transfer, rule prod_w_trivial_global_unfrmzr_pows_fls_pseq, simp)

end (* context nontrivial_factorial_idom *)

lemma global_unfrmzr_pows_p_adic_prod_pow:
  "(\<pp> f :: 'a p_adic_prod) ^ n = (\<pp> (\<lambda>p. int n * f p))"
  for f :: "'a::nontrivial_factorial_idom prime \<Rightarrow> int"
  by (
    transfer,
    metis globally_p_equal_fls_pseq_def p_equality_depth_fls_pseq.globally_p_equal_refl
          pow_global_unfrmzr_pows_fls_pseq
  )
lemma global_unfrmzr_pows_p_adic_prod_inv:
  "(\<pp> (-f) :: 'a p_adic_prod) * (\<pp> f) = 1"
  for f :: "'a::nontrivial_factorial_idom prime \<Rightarrow> int"
  by (
    transfer,
    metis globally_p_equal_fls_pseq_def p_equality_depth_fls_pseq.globally_p_equal_refl
          global_unfrmzr_pows_fls_pseq_inv
  )

lemma global_unfrmzr_pows_p_adic_prod_inverse:
  "inverse (\<pp> f :: 'a p_adic_prod) = \<pp> (-f)"
  for f :: "'a::nontrivial_factorial_unique_euclidean_bezout prime \<Rightarrow> int"
proof (transfer)
  fix f :: "'a::nontrivial_factorial_unique_euclidean_bezout prime \<Rightarrow> int"
  have "((\<pp> f)\<inverse>\<^sup>\<forall>\<^sup>p) = (\<pp> (- f) :: 'a fls_pseq)"
    using global_unfrmzr_pows_fls_pseq_def[of f] global_unfrmzr_pows_fls_pseq_def[of "-f"]
          fls_pinv_X_intpow
    by    auto
  thus
    "((\<pp> f)\<inverse>\<^sup>\<forall>\<^sup>p) \<simeq>\<^sub>\<forall>\<^sub>p
      (\<pp> (- f) :: 'a fls_pseq)"
    by auto
qed

lemma global_unfrmzr_pows_p_adic_prod_decomp:
  "x = (
    (x * \<pp> (\<lambda>p::'a prime. -(x\<degree>\<^sup>p))) *
    \<pp> (\<lambda>p::'a prime. x\<degree>\<^sup>p)
  )"
  for p :: "'a::nontrivial_factorial_idom prime" and x :: "'a p_adic_prod"
  by (
    transfer,
    metis global_unfrmzr_pows_fls_pseq_decomp p_equality_depth_fls_pseq.globally_p_equal_refl
          globally_p_equal_fls_pseq_def
  )

lemma p_adic_prod_normalize_depthE:
  fixes   x :: "'a::nontrivial_factorial_idom p_adic_prod"
  obtains x_0
  where   "\<forall>p::'a prime. x_0\<degree>\<^sup>p = 0"
  and     "x = x_0 * \<pp> (\<lambda>p::'a prime. x\<degree>\<^sup>p)"
  using   p_adic_prod_normalize_depth global_unfrmzr_pows_p_adic_prod_decomp
  by      blast

global_interpretation p_adic_prod_div_inv:
  global_p_equal_depth_div_inv
    "p_equal :: 'a::nontrivial_factorial_unique_euclidean_bezout prime \<Rightarrow>
      'a p_adic_prod \<Rightarrow> 'a p_adic_prod \<Rightarrow> bool"
    "p_depth :: 'a prime \<Rightarrow> 'a p_adic_prod \<Rightarrow> int"
    "p_restrict ::
      'a p_adic_prod \<Rightarrow> ('a prime \<Rightarrow> bool) \<Rightarrow> 'a p_adic_prod"
proof
  fix p :: "'a prime" and x y :: "'a p_adic_prod"
  show "x / y = x * inverse y" by transfer simp
  show "inverse (inverse x) = x" by transfer (rule global_pinverse_pinverse_fls_pseq)
  show "inverse (x * y) = inverse x * inverse y" by transfer (rule global_pinverse_mult_fls_pseq)
  show "(inverse x \<simeq>\<^sub>p 0) = (x \<simeq>\<^sub>p 0)"
    by transfer (simp add: fls_pinv_equiv0_iff)
  show "x \<not>\<simeq>\<^sub>p 0 \<Longrightarrow> x / x \<simeq>\<^sub>p 1"
    by transfer (simp add: pinverse_fls_mult_equiv1')
qed


subsection \<open>Embeddings of the base ring, @{typ nat}, @{typ int}, and @{typ rat}\<close>

subsubsection \<open>Embedding of the base ring\<close>

abbreviation "p_adic_prod_consts \<equiv> global_p_depth_p_adic_prod.consts"
abbreviation "p_adic_prod_const \<equiv> global_p_depth_p_adic_prod.const"

lemma p_depth_p_adic_prod_consts:
  "(p_adic_prod_consts f)\<degree>\<^sup>p = ((f p)\<degree>\<^sup>p)"
  for p :: "'a::nontrivial_factorial_idom prime" and f :: "'a prime \<Rightarrow> 'a"
  by (simp add: p_depth_p_adic_prod.abs_eq flip: p_depth_const_def)

lemmas p_depth_p_adic_prod_const = p_depth_p_adic_prod_consts[of _ "\<lambda>p. _"]

lemma p_adic_prod_global_unfrmzr:
  "(\<pp> (1 :: 'a::nontrivial_factorial_idom prime \<Rightarrow> int) :: 'a p_adic_prod) =
    p_adic_prod_consts Rep_prime"
proof (rule global_p_depth_p_adic_prod.global_imp_eq, standard)
  fix p :: "'a prime"
  define \<pp>1_fls_pseq :: "'a fls_pseq" and \<pp>1_pre :: "'a p_adic_prod"
    where "\<pp>1_fls_pseq \<equiv> \<pp> (1 :: 'a prime \<Rightarrow> int)"
    and   "\<pp>1_pre \<equiv> \<pp> (1 :: 'a prime \<Rightarrow> int)"
  have
    "(abs_p_adic_prod \<pp>1_fls_pseq) \<simeq>\<^sub>p
      (abs_p_adic_prod (\<lambda>p::'a prime. fls_const (Rep_prime p)))"
    unfolding \<pp>1_fls_pseq_def p_equal_p_adic_prod.abs_eq
    by        (rule global_unfrmzr_fls_pseq)
  thus "\<pp>1_pre \<simeq>\<^sub>p (p_adic_prod_consts Rep_prime)"
    unfolding \<pp>1_fls_pseq_def \<pp>1_pre_def global_unfrmzr_pows_p_adic_prod_def by simp
qed


subsubsection \<open>Embedding of the field of fractions of the base ring\<close>

global_interpretation p_adic_prod_embeds:
  global_p_equal_div_inv_w_inj_idom_consts
    "p_equal :: 'a::nontrivial_factorial_unique_euclidean_bezout prime \<Rightarrow>
      'a p_adic_prod \<Rightarrow> 'a p_adic_prod \<Rightarrow> bool"
    "p_restrict ::
      'a p_adic_prod \<Rightarrow> ('a prime \<Rightarrow> bool) \<Rightarrow> 'a p_adic_prod"
    "\<lambda>f. abs_p_adic_prod (\<lambda>p. fls_const (f p))"
  ..

global_interpretation p_adic_prod_depth_embeds:
  global_p_equal_depth_div_inv_w_inj_index_consts
    "p_equal :: 'a::nontrivial_factorial_unique_euclidean_bezout prime \<Rightarrow>
      'a p_adic_prod \<Rightarrow> 'a p_adic_prod \<Rightarrow> bool"
    "p_depth :: 'a prime \<Rightarrow> 'a p_adic_prod \<Rightarrow> int"
    "p_restrict ::
      'a p_adic_prod \<Rightarrow> ('a prime \<Rightarrow> bool) \<Rightarrow> 'a p_adic_prod"
    "\<lambda>f. abs_p_adic_prod (\<lambda>p. fls_const (f p))"
    Rep_prime
  ..

abbreviation "p_adic_prod_shift_p_depth \<equiv> p_adic_prod_depth_embeds.shift_p_depth"
abbreviation "p_adic_prod_of_fract      \<equiv> p_adic_prod_embeds.const_of_fract"

lemma p_adic_prod_of_fract_depth:
  "(p_adic_prod_of_fract (Fraction_Field.Fract a b) :: 'a p_adic_prod)\<degree>\<^sup>p =
    (a\<degree>\<^sup>p) - (b\<degree>\<^sup>p)"
  if  "a \<noteq> 0" and "b \<noteq> 0"
  for p :: "'a::nontrivial_factorial_unique_euclidean_bezout prime"
  and a b :: 'a
  using that global_p_depth_p_adic_prod.p_equal_func_of_const_0
        p_adic_prod_div_inv.divide_equiv_0_iff p_adic_prod_embeds.const_of_fract_Fract
        p_adic_prod_div_inv.divide_depth p_depth_p_adic_prod_const
  by    metis

text \<open>Product of all p-adic embeddings of the field of fractions of the base ring.\<close>
abbreviation p_adic_Fracts_prod ::
  "'a::nontrivial_factorial_unique_euclidean_bezout p_adic_prod set"
  ("\<Q>\<^sub>\<forall>\<^sub>p")
  where "\<Q>\<^sub>\<forall>\<^sub>p \<equiv> p_adic_prod_embeds.range_const_of_fract"

subsubsection \<open>Characteristic zero embeddings\<close>

class nontrivial_factorial_idom_char_0 = nontrivial_factorial_idom + semiring_char_0
begin
subclass ring_char_0 ..
end

instance int :: nontrivial_factorial_idom_char_0 ..

class nontrivial_factorial_unique_euclidean_bezout_char_0 =
  nontrivial_factorial_unique_euclidean_bezout + nontrivial_factorial_idom_char_0

instance int :: nontrivial_factorial_unique_euclidean_bezout_char_0 ..

instance p_adic_prod :: (nontrivial_factorial_idom_char_0) ring_char_0
  by (
    standard, standard,
    metis global_p_depth_p_adic_prod.const_of_nat global_p_depth_p_adic_prod.const_eq_iff
          of_nat_eq_iff
  )

global_interpretation p_adic_prod_consts_char_0:
  global_p_equality_w_inj_consts_char_0
    "p_equal :: 'a::nontrivial_factorial_idom_char_0 prime \<Rightarrow>
      'a p_adic_prod \<Rightarrow> 'a p_adic_prod \<Rightarrow> bool"
    "p_restrict ::
      'a p_adic_prod \<Rightarrow> ('a prime \<Rightarrow> bool) \<Rightarrow> 'a p_adic_prod"
    "\<lambda>f. abs_p_adic_prod (\<lambda>p. fls_const (f p))"
  ..

global_interpretation p_adic_prod_div_inv_consts_char_0:
  global_p_equal_div_inv_w_inj_consts_char_0
    "p_equal :: 'a::nontrivial_factorial_unique_euclidean_bezout_char_0 prime \<Rightarrow>
      'a p_adic_prod \<Rightarrow> 'a p_adic_prod \<Rightarrow> bool"
    "p_restrict ::
      'a p_adic_prod \<Rightarrow> ('a prime \<Rightarrow> bool) \<Rightarrow> 'a p_adic_prod"
    "\<lambda>f. abs_p_adic_prod (\<lambda>p. fls_const (f p))"
 ..

lemma p_adic_prod_of_nat_depth:
  "(of_nat n :: 'a p_adic_prod)\<degree>\<^sup>p = ((of_nat n :: 'a)\<degree>\<^sup>p)"
  for p :: "'a::nontrivial_factorial_idom prime"
  by (metis global_p_depth_p_adic_prod.const_of_nat p_depth_p_adic_prod_const)

lemma p_adic_prod_of_int_depth:
  "(of_int z :: 'a p_adic_prod)\<degree>\<^sup>p = ((of_int z :: 'a)\<degree>\<^sup>p)"
  for p :: "'a::nontrivial_factorial_idom prime"
  by (metis global_p_depth_p_adic_prod.const_of_int p_depth_p_adic_prod_const)

abbreviation "p_adic_prod_of_rat \<equiv> p_adic_prod_div_inv_consts_char_0.const_of_rat"

lemma p_adic_prod_of_rat_depth:
  "(p_adic_prod_of_rat (Rat.Fract a b) :: 'a p_adic_prod)\<degree>\<^sup>p =
    ((of_int a :: 'a)\<degree>\<^sup>p) - ((of_int b :: 'a)\<degree>\<^sup>p)"
  if  "a \<noteq> 0" and "b \<noteq> 0"
  for p :: "'a::nontrivial_factorial_unique_euclidean_bezout_char_0 prime"
  and a b :: int
  using that p_adic_prod_consts_char_0.const_of_int_p_equal_0_iff
        p_adic_prod_div_inv.divide_equiv_0_iff p_adic_prod_div_inv_consts_char_0.const_of_rat_rat
        p_adic_prod_div_inv.divide_depth p_adic_prod_of_int_depth
  by    metis


subsection \<open>Topologies on products of p-adic fields\<close>

subsubsection \<open>By local place\<close>

text \<open>Completeness\<close>

abbreviation "p_adic_prod_p_open_nbhd \<equiv> global_p_depth_p_adic_prod.p_open_nbhd"
abbreviation "p_adic_prod_p_open_nbhds \<equiv> global_p_depth_p_adic_prod.p_open_nbhds"
abbreviation
  "p_adic_prod_p_limseq_condition \<equiv> global_p_depth_p_adic_prod.p_limseq_condition"
abbreviation
  "p_adic_prod_p_cauchy_condition \<equiv> global_p_depth_p_adic_prod.p_cauchy_condition"
abbreviation "p_adic_prod_p_limseq \<equiv> global_p_depth_p_adic_prod.p_limseq"
abbreviation "p_adic_prod_p_cauchy \<equiv> global_p_depth_p_adic_prod.p_cauchy"
abbreviation
  "p_adic_prod_p_open_nbhds_limseq \<equiv> global_p_depth_p_adic_prod.p_open_nbhds_LIMSEQ"
abbreviation
  "p_adic_prod_local_p_open_nbhds \<equiv> global_p_depth_p_adic_prod.local_p_open_nbhds"

lemma abs_p_adic_prod_seq_cases [case_names abs_p_adic_prod]:
  C if "\<And>F. X = (\<lambda>n. abs_p_adic_prod (F n)) \<Longrightarrow> C"
proof-
  have "X = (\<lambda>n. abs_p_adic_prod (rep_p_adic_prod (X n)))"
    using rep_p_adic_prod_inverse by metis
  with that show C by fast
qed

lemma abs_p_adic_prod_p_limseq_condition:
  "p_adic_prod_p_limseq_condition p (\<lambda>n. abs_p_adic_prod (F n)) (abs_p_adic_prod X) n K =
    fls_p_limseq_condition p (\<lambda>n. F n p) (X p) n K"
  unfolding global_p_depth_p_adic_prod.p_limseq_condition_def p_depth_fls.p_limseq_condition_def
  by (auto simp add: p_equal_p_adic_prod.abs_eq p_depth_p_adic_prod_diff_abs_eq)

lemma abs_p_adic_prod_p_limseq:
  "p_adic_prod_p_limseq p (\<lambda>n. abs_p_adic_prod (F n)) (abs_p_adic_prod X) =
    fls_p_limseq p (\<lambda>n. F n p) (X p)"
  using abs_p_adic_prod_p_limseq_condition by fast

lemma abs_p_adic_prod_p_cauchy_condition:
  "p_adic_prod_p_cauchy_condition p (\<lambda>n. abs_p_adic_prod (F n)) n K =
    fls_p_cauchy_condition p (\<lambda>n. F n p) n K"
  unfolding global_p_depth_p_adic_prod.p_cauchy_condition_def p_depth_fls.p_cauchy_condition_def
  by (auto simp add: p_equal_p_adic_prod.abs_eq p_depth_p_adic_prod_diff_abs_eq)

lemma abs_p_adic_prod_p_cauchy:
  "p_adic_prod_p_cauchy p (\<lambda>n. abs_p_adic_prod (F n)) = fls_p_cauchy p (\<lambda>n. F n p) "
  using abs_p_adic_prod_p_cauchy_condition by blast

lemma p_adic_prod_p_restrict_cauchy_lim:
  "p_adic_prod_p_limseq q
    (\<lambda>n. p_restrict (X n) ((=) p))
    (abs_p_adic_prod (\<lambda>q.
      if q = p then fls_p_cauchy_lim p (\<lambda>n. rep_p_adic_prod (X n) p) else 0
    ))"
  if "p_adic_prod_p_cauchy p X"
proof (cases X rule: abs_p_adic_prod_seq_cases)
  case (abs_p_adic_prod F)
  define limval where
    "limval \<equiv>
      abs_p_adic_prod (\<lambda>q.
        if q = p then fls_p_cauchy_lim p (\<lambda>n. rep_p_adic_prod (X n) p) else 0
      )"
  show "p_adic_prod_p_limseq q (\<lambda>n. X n prestrict (=) p) limval"
  proof (cases "p = q")
    case True
    with that abs_p_adic_prod have F: "fls_p_cauchy q (\<lambda>n. F n q)"
      using abs_p_adic_prod_p_cauchy by blast
    have "fls_p_limseq q (\<lambda>n. F n q) (fls_p_cauchy_lim q (\<lambda>n. F n q))"
      using F fls_p_cauchy_limseq by blast
    moreover have
      "fls_p_cauchy_lim q (\<lambda>n. rep_p_adic_prod (abs_p_adic_prod (F n)) q) =
        fls_p_cauchy_lim q (\<lambda>n. F n q)"
      by (
        intro fls_p_cauchy_lim_unique F, clarify,
        use abs_p_adic_prod p_adic_prod_globally_p_equal_self globally_p_equal_fls_pseq_def
        in  auto
      )
    ultimately have "p_adic_prod_p_limseq q X limval"
      using True limval_def abs_p_adic_prod abs_p_adic_prod_p_limseq by force
    moreover from True have "\<forall>n. (p_restrict (X n) ((=) p)) \<simeq>\<^sub>q (X n)"
      using global_p_depth_p_adic_prod.p_restrict_equiv by blast
    ultimately show ?thesis
      using global_p_depth_p_adic_prod.p_limseq_p_cong[of 0 q _ X limval limval] by auto
  next
    case False
    with abs_p_adic_prod limval_def show ?thesis
      using global_p_depth_p_adic_prod.p_restrict_equiv0[of "(=) p" q]
            p_equal_p_adic_prod_abs_eq0[of q]
            global_p_depth_p_adic_prod.p_limseq_p_cong[of
              0 q "\<lambda>n. (X n) prestrict (=) p" 0 limval
            ]
            global_p_depth_p_adic_prod.p_limseq_0_iff[of q limval]
      by    fastforce
  qed
qed


global_interpretation p_complete_p_adic_prod:
  p_complete_global_p_equal_depth
    "p_equal :: 'a::nontrivial_euclidean_ring_cancel prime \<Rightarrow>
      'a p_adic_prod \<Rightarrow> 'a p_adic_prod \<Rightarrow> bool"
    "p_restrict ::
      'a p_adic_prod \<Rightarrow> ('a prime \<Rightarrow> bool) \<Rightarrow> 'a p_adic_prod"
    "p_depth :: 'a prime \<Rightarrow> 'a p_adic_prod \<Rightarrow> int"
proof
  fix p :: "'a prime" and X :: "nat \<Rightarrow> 'a p_adic_prod"
  define res_X :: "nat \<Rightarrow> 'a p_adic_prod" and limval :: "'a p_adic_prod"
    where "res_X \<equiv> \<lambda>n. p_restrict (X n) ((=) p)"
    and
      "limval \<equiv>
        abs_p_adic_prod (\<lambda>q.
          if q = p then fls_p_cauchy_lim p (\<lambda>n. rep_p_adic_prod (X n) p) else 0
        )"
  moreover assume "p_adic_prod_p_cauchy p X"
  ultimately have "\<forall>q. p_adic_prod_p_limseq q res_X limval"
    using p_adic_prod_p_restrict_cauchy_lim by blast
  hence "p_adic_prod_p_open_nbhds_limseq res_X limval"
    using global_p_depth_p_adic_prod.globally_limseq_iff_locally_limseq by fast
  thus "global_p_depth_p_adic_prod.p_open_nbhds_convergent res_X"
    using global_p_depth_p_adic_prod.t2_p_open_nbhds.convergent_def by auto
qed

global_interpretation p_complete_p_adic_prod_div_inv:
  p_complete_global_p_equal_depth_div_inv
    "p_equal :: 'a::nontrivial_factorial_unique_euclidean_bezout prime \<Rightarrow>
      'a p_adic_prod \<Rightarrow> 'a p_adic_prod \<Rightarrow> bool"
    "p_depth :: 'a prime \<Rightarrow> 'a p_adic_prod \<Rightarrow> int"
    "p_restrict ::
      'a p_adic_prod \<Rightarrow> ('a prime \<Rightarrow> bool) \<Rightarrow> 'a p_adic_prod"
  ..

lemmas p_adic_prod_hensel = p_complete_p_adic_prod_div_inv.hensel


subsubsection \<open>By bounded global depth\<close>

text \<open>The metric\<close>
instantiation p_adic_prod :: (nontrivial_factorial_idom) metric_space
begin

definition "dist = global_p_depth_p_adic_prod.bdd_global_dist"
declare dist_p_adic_prod_def [simp]

definition "uniformity = global_p_depth_p_adic_prod.bdd_global_uniformity"
declare uniformity_p_adic_prod_def [simp]

definition open_p_adic_prod :: "'a p_adic_prod set \<Rightarrow> bool"
  where
    "open_p_adic_prod U = (\<forall>x\<in>U.
      eventually (\<lambda>(x', y). x' = x \<longrightarrow> y \<in> U) uniformity
    )"

instance
  by (
    standard,
    simp_all add: global_p_depth_p_adic_prod.bdd_global_uniformity_def open_p_adic_prod_def
                  global_p_depth_p_adic_prod.metric_space_by_bdd_depth.dist_triangle2
  )

end (* instantiation p_adic_prod metric_space *)

abbreviation "p_adic_prod_global_depth \<equiv> global_p_depth_p_adic_prod.bdd_global_depth"

lemma bdd_global_depth_p_adic_prod_abs_eq:
  "p_adic_prod_global_depth (abs_p_adic_prod X) = fls_pseq_bdd_global_depth X"
proof (cases "X \<simeq>\<^sub>\<forall>\<^sub>p 0")
  case True
  hence "abs_p_adic_prod X = 0"
    using p_adic_prod_lift_globally_p_equal zero_p_adic_prod.abs_eq by metis
  with True show ?thesis by force
next
  case False
  hence "abs_p_adic_prod X \<noteq> 0"
    using p_adic_prod.abs_eq_iff zero_p_adic_prod.abs_eq by metis
  hence "\<not> abs_p_adic_prod X \<simeq>\<^sub>\<forall>\<^sub>p 0"
    using global_p_depth_p_adic_prod.global_eq_iff by auto
  hence
    "p_adic_prod_global_depth (abs_p_adic_prod X) =
      (INF p\<in>{p::'a prime. abs_p_adic_prod X \<not>\<simeq>\<^sub>p 0}.
        nat (((abs_p_adic_prod X)\<degree>\<^sup>p) + 1))"
    using global_p_depth_p_adic_prod.bdd_global_depthD_as_image[of "abs_p_adic_prod X"]
    by    fastforce
  also have
    "\<dots> = (INF p\<in>{p::'a prime. X \<not>\<simeq>\<^sub>p 0}.
      nat (((abs_p_adic_prod X)\<degree>\<^sup>p) + 1))"
    using p_equal_p_adic_prod.abs_eq zero_p_adic_prod.abs_eq by metis
  finally show ?thesis
    using False p_depth_p_adic_prod.abs_eq[of _ X]
          p_equality_depth_fls_pseq.bdd_global_depthD_as_image
    by    force
qed

lemma dist_p_adic_prod_abs_eq:
  "dist (abs_p_adic_prod X) (abs_p_adic_prod Y) = fls_pseq_bdd_global_dist X Y"
proof (cases "X \<simeq>\<^sub>\<forall>\<^sub>p Y")
  case True
  hence "abs_p_adic_prod X = abs_p_adic_prod Y" using p_adic_prod_lift_globally_p_equal by metis
  with True show ?thesis by fastforce
next
  case False
  from False have "abs_p_adic_prod X \<noteq> abs_p_adic_prod Y"
    using p_adic_prod.abs_eq_iff by metis
  hence "\<not> abs_p_adic_prod X \<simeq>\<^sub>\<forall>\<^sub>p abs_p_adic_prod Y"
    using global_p_depth_p_adic_prod.global_eq_iff by auto
  hence
    "dist (abs_p_adic_prod X) (abs_p_adic_prod Y) =
      inverse (2 ^ p_adic_prod_global_depth (abs_p_adic_prod X - abs_p_adic_prod Y))"
    using global_p_depth_p_adic_prod.bdd_global_distD by auto
  also have "\<dots> = inverse (2 ^ p_adic_prod_global_depth (abs_p_adic_prod (X - Y)))"
    using minus_p_adic_prod.abs_eq by metis
  finally show ?thesis
    using False bdd_global_depth_p_adic_prod_abs_eq p_equality_depth_fls_pseq.bdd_global_distD
    by    fastforce
qed

lemma p_adic_prod_metric_is_finer:
  "generate_topology p_adic_prod_p_open_nbhds U \<Longrightarrow> open U"
proof (induct U rule: generate_topology.induct)
  case (Basis U) show "open U"
  proof (intro Elementary_Metric_Spaces.openI)
    fix u assume "u \<in> U"
    moreover from Basis obtain p n x where "U = p_adic_prod_p_open_nbhd p n x"
      by fast
    ultimately have U: "U = p_adic_prod_p_open_nbhd p n u"
      using global_p_depth_p_adic_prod.p_open_nbhd_circle_multicentre by fast
    have "ball u (inverse (2 ^ nat n)) \<subseteq> U"
      unfolding U global_p_depth_p_adic_prod.p_open_nbhd_eq_circle ball_def
      using     global_p_depth_p_adic_prod.bdd_global_dist_sym[of u]
                global_p_depth_p_adic_prod.bdd_global_dist_less_pow2_iff[of _ u "nat n"]
      by        auto
    thus "\<exists>e>0. ball u e \<subseteq> U" by force
  qed
qed (simp, fast, fast)

lemma p_adic_prod_metric_is_finer_than_purely_local:
  "generate_topology (p_adic_prod_local_p_open_nbhds p) U \<Longrightarrow>
    open U"
  for p :: "'a::nontrivial_factorial_idom prime"
  and U :: "'a p_adic_prod set"
  using global_p_depth_p_adic_prod.local_p_open_nbhds_are_coarser p_adic_prod_metric_is_finer
  by    blast

lemma p_adic_prod_limseq_abs_eq:
  "(\<lambda>n. abs_p_adic_prod (X n)) \<longlonglongrightarrow> abs_p_adic_prod x
    \<longleftrightarrow>
    (\<forall>e>0. \<forall>\<^sub>F n in sequentially. fls_pseq_bdd_global_dist (X n) x < e)"
proof-
  have
    "\<forall>n. dist (abs_p_adic_prod (X n)) (abs_p_adic_prod x) =
      fls_pseq_bdd_global_dist (X n) x"
    using dist_p_adic_prod_abs_eq[of "X _" x] by blast
  thus ?thesis
    using tendsto_iff[of "\<lambda>n. abs_p_adic_prod (X n)" "abs_p_adic_prod x"] by presburger
qed

lemma p_adic_prod_bdd_metric_LIMSEQ:
  "X \<longlonglongrightarrow> x = global_p_depth_p_adic_prod.metric_space_by_bdd_depth.LIMSEQ X x"
  for X :: "nat \<Rightarrow> 'a::nontrivial_factorial_idom p_adic_prod" and x :: "'a p_adic_prod"
  unfolding tendsto_iff global_p_depth_p_adic_prod.metric_space_by_bdd_depth.tendsto_iff
            dist_p_adic_prod_def
  by        fast

lemma p_adic_prod_global_depth_set_lim_closed:
  "x \<in> \<P>\<^sub>\<forall>\<^sub>p\<^sup>n"
  if  lim  : "X \<longlonglongrightarrow> x"
  and depth: "\<forall>\<^sub>F k in sequentially. X k \<in> \<P>\<^sub>\<forall>\<^sub>p\<^sup>n"
  for X :: "nat \<Rightarrow> 'a::nontrivial_factorial_unique_euclidean_bezout p_adic_prod"
  and x :: "'a p_adic_prod"
  using that p_adic_prod_bdd_metric_LIMSEQ p_adic_prod_depth_embeds.global_depth_set_LIMSEQ_closed
  by    fastforce

lemma p_adic_prod_metric_ball_multicentre:
  "ball y e = ball x e" if "y \<in> ball x e"
  for x y :: "'a::nontrivial_factorial_idom p_adic_prod"
  using     that global_p_depth_p_adic_prod.bdd_global_dist_ball_multicentre
  unfolding ball_def dist_p_adic_prod_def
  by        blast

lemma p_adic_prod_metric_ball_at_0:
  "ball (0::'a::nontrivial_factorial_idom p_adic_prod) (inverse (2 ^ n)) = global_depth_set (int n)"
  using     global_p_depth_p_adic_prod.bdd_global_dist_ball_at_0
  unfolding ball_def dist_p_adic_prod_def global_depth_set_p_adic_prod_def
  by        auto

lemma p_adic_prod_metric_ball_UNIV:
  "ball x e = UNIV" if "e > 1"
  for x :: "'a::nontrivial_factorial_idom p_adic_prod"
  using     that global_p_depth_p_adic_prod.bdd_global_dist_ball_UNIV
  unfolding ball_def dist_p_adic_prod_def
  by        blast

lemma p_adic_prod_metric_ball_at_0_normalize:
  "ball (0::'a::nontrivial_factorial_idom p_adic_prod) e =
    global_depth_set \<lfloor>log 2 (inverse e)\<rfloor>"
  if "e > 0" and "e \<le> 1"
  using     that global_p_depth_p_adic_prod.bdd_global_dist_ball_at_0_normalize
  unfolding ball_def dist_p_adic_prod_def global_depth_set_p_adic_prod_def
  by        blast

lemma p_adic_prod_metric_ball_translate:
  "ball x e = x +o ball 0 e" for x :: "'a::nontrivial_factorial_idom p_adic_prod"
  using     global_p_depth_p_adic_prod.bdd_global_dist_ball_translate
  unfolding ball_def dist_p_adic_prod_def
  by        blast

lemma p_adic_prod_left_translate_metric_continuous:
  "continuous_on UNIV ((+) x)" for x :: "'a::nontrivial_factorial_idom p_adic_prod"
proof
  fix e :: real and z :: "'a p_adic_prod"
  assume e: "e > 0"
  moreover have "\<forall>y. dist y z < e \<longrightarrow> dist (x + y) (x + z) \<le> e"
    using global_p_depth_p_adic_prod.bdd_global_dist_left_translate_continuous[of
            _ _ e x
          ]
    unfolding dist_p_adic_prod_def
    by        fastforce
  ultimately show
    "\<exists>d>0. \<forall>x'\<in>UNIV.
      dist x' z < d \<longrightarrow> dist (x + x') (x + z) \<le> e"
    by auto
qed

lemma p_adic_prod_right_translate_metric_continuous:
  "continuous_on UNIV (\<lambda>z. z + x)" for x :: "'a::nontrivial_factorial_idom p_adic_prod"
proof-
  have "(\<lambda>z. z + x) = (+) x" by (auto simp add: add.commute)
  thus ?thesis using p_adic_prod_left_translate_metric_continuous by metis
qed

lemma p_adic_prod_left_bdd_mult_bdd_metric_continuous:
  "continuous_on UNIV ((*) x)"
  if bdd:
    "\<forall>p::'a prime. x \<not>\<simeq>\<^sub>p 0 \<longrightarrow>
      (x\<degree>\<^sup>p) \<ge> n"
  for x :: "'a::nontrivial_factorial_idom p_adic_prod"
proof
  fix e :: real and z :: "'a p_adic_prod"
  assume e: "e > 0"
  moreover define d where "d \<equiv> min (e * 2 powi (n - 1)) 1"
  ultimately have "\<forall>y. dist y z < d \<longrightarrow> dist (x * y) (x * z) \<le> e"
    using bdd global_p_depth_p_adic_prod.bdd_global_dist_bdd_mult_continuous by fastforce
  moreover from e d_def have "d > 0" by auto
  ultimately show
    "\<exists>d>0. \<forall>y\<in>UNIV. dist y z < d \<longrightarrow> dist (x * y) (x * z) \<le> e"
    by blast
qed

lemma p_adic_prod_bdd_metric_limseq_bdd_mult:
  "(\<lambda>k. w * X k) \<longlonglongrightarrow> (w * x)"
  if bdd:
    "\<forall>p::'a prime. w \<not>\<simeq>\<^sub>p 0 \<longrightarrow>
      (w\<degree>\<^sup>p) \<ge> n"
  and seq: "X \<longlonglongrightarrow> x"
  for w x :: "'a::nontrivial_factorial_idom p_adic_prod" and X :: "nat \<Rightarrow> 'a p_adic_prod"
  using bdd seq p_adic_prod_left_bdd_mult_bdd_metric_continuous continuous_on_tendsto_compose
  by    fastforce

lemma p_adic_prod_nonpos_global_depth_set_open:
  "ball x 1 \<subseteq> (\<P>\<^sub>\<forall>\<^sub>p\<^sup>n)"
  if "n \<le> 0" and "x \<in> (\<P>\<^sub>\<forall>\<^sub>p\<^sup>n)"
  for x :: "'a::nontrivial_factorial_idom p_adic_prod"
proof-
  have "ball x 1 = x +o ball 0 1" using p_adic_prod_metric_ball_translate by blast
  also have "\<dots> = x +o (\<O>\<^sub>\<forall>\<^sub>p)"
    using p_adic_prod_metric_ball_at_0[of 0] by auto
  finally show ?thesis
    using that global_p_depth_p_adic_prod.global_depth_set_elt_set_plus_closed[of n 0] by auto
qed

lemma p_adic_prod_global_depth_set_open:
  "open ((\<P>\<^sub>\<forall>\<^sub>p\<^sup>n) :: 'a::nontrivial_factorial_idom p_adic_prod set)"
proof (cases "n \<ge> 0")
  case True
  hence "(\<P>\<^sub>\<forall>\<^sub>p\<^sup>n) = ball (0::'a p_adic_prod) (inverse (2 ^ nat n))"
    using p_adic_prod_metric_ball_at_0 by fastforce
  thus ?thesis by simp
next
  case False thus ?thesis
    using p_adic_prod_nonpos_global_depth_set_open[of n]
          Elementary_Metric_Spaces.openI[of
            "(\<P>\<^sub>\<forall>\<^sub>p\<^sup>n) :: 'a p_adic_prod set"
          ]
    by    force
qed

lemma p_adic_prod_ball_abs_eq:
  "abs_p_adic_prod ` {Y. fls_pseq_bdd_global_dist X Y < e} =
    ball (abs_p_adic_prod X) e"
  for x :: "'a::nontrivial_factorial_idom p_adic_prod"
proof-
  define B B'
    where "B \<equiv>  {Y. fls_pseq_bdd_global_dist X Y < e}"
    and   "B' \<equiv> ball (abs_p_adic_prod X) e"
  moreover have "\<And>y. y \<in> B' \<Longrightarrow> y \<in> abs_p_adic_prod ` B"
  proof-
    fix y assume y: "y \<in> B'"
    show "y \<in> abs_p_adic_prod ` B"
    proof (cases y)
      case (abs_p_adic_prod Y)
      moreover from this B'_def y have "fls_pseq_bdd_global_dist X Y < e"
        using mem_ball dist_p_adic_prod_abs_eq by metis
      ultimately show ?thesis using B_def by blast
    qed
  qed
  ultimately show "abs_p_adic_prod ` B = B'"
    using dist_p_adic_prod_abs_eq[of X] by fastforce
qed

text \<open>Completeness\<close>

abbreviation "p_adic_prod_globally_cauchy \<equiv> global_p_depth_p_adic_prod.globally_cauchy"
abbreviation
  "p_adic_prod_global_cauchy_condition  \<equiv> global_p_depth_p_adic_prod.global_cauchy_condition"

lemma p_adic_prod_global_cauchy_condition_abs_eq:
  "p_adic_prod_global_cauchy_condition (\<lambda>n. abs_p_adic_prod (X n)) =
    fls_pseq_global_cauchy_condition X"
  unfolding global_p_depth_p_adic_prod.global_cauchy_condition_def
            p_equality_depth_fls_pseq.global_cauchy_condition_def
  by        (
              standard, standard,
              metis p_equal_p_adic_prod.abs_eq p_depth_p_adic_prod_diff_abs_eq
            )

lemma p_adic_prod_globally_cauchy_abs_eq:
  "p_adic_prod_globally_cauchy (\<lambda>n. abs_p_adic_prod (X n)) = fls_pseq_globally_cauchy X"
  using p_adic_prod_global_cauchy_condition_abs_eq by metis

lemma p_adic_prod_globally_cauchy_vs_bdd_metric_Cauchy:
  "p_adic_prod_globally_cauchy X = Cauchy X"
  for X :: "nat \<Rightarrow> 'a::nontrivial_factorial_idom p_adic_prod"
  using     global_p_depth_p_adic_prod.globally_cauchy_vs_bdd_metric_Cauchy
  unfolding global_p_depth_p_adic_prod.metric_space_by_bdd_depth.Cauchy_def Cauchy_def
  by        auto

abbreviation
  "p_adic_prod_cauchy_lim X \<equiv>
    abs_p_adic_prod (\<lambda>p.
      fls_condition_lim p
        (\<lambda>n. reduced_rep_p_adic_prod (X n) p)
        (p_adic_prod_global_cauchy_condition X)
    )"

lemma p_adic_prod_bdd_metric_complete':
  "X \<longlonglongrightarrow> p_adic_prod_cauchy_lim X" if "Cauchy X"
proof (cases X rule: p_adic_prod_seq_reduced_cases)
  case (abs_p_adic_prod F) with that show ?thesis
    using p_adic_prod_globally_cauchy_vs_bdd_metric_Cauchy[of "\<lambda>n. abs_p_adic_prod (F n)"]
          p_adic_prod_globally_cauchy_abs_eq fls_pseq_cauchy_condition_lim
          p_adic_prod_global_cauchy_condition_abs_eq[of F] abs_p_adic_prod_inverse[of "F _"]
          p_adic_prod_limseq_abs_eq[of F]
    by    fastforce
qed

lemma p_adic_prod_bdd_metric_complete:
  "complete (UNIV :: 'a::nontrivial_euclidean_ring_cancel p_adic_prod set)"
  using p_adic_prod_bdd_metric_complete' completeI by blast


subsection \<open>Hiding implementation details\<close>

lifting_update p_adic_prod.lifting
lifting_forget p_adic_prod.lifting


subsection \<open>The subring of adelic integers\<close>

subsubsection \<open>Type definition as a subtype of adeles\<close>

typedef (overloaded) 'a adelic_int =
  "\<O>\<^sub>\<forall>\<^sub>p :: 'a::nontrivial_factorial_idom p_adic_prod set"
  using global_p_depth_p_adic_prod.global_depth_set_0 by auto

lemma Abs_adelic_int_inverse':
  "Rep_adelic_int (Abs_adelic_int x) = x" if "x \<in> \<O>\<^sub>\<forall>\<^sub>p"
  using that Abs_adelic_int_inverse by fast

lemma Abs_adelic_int_cases [case_names Abs_adelic_int, cases type: adelic_int]:
  P if
    "\<And>x. z = Abs_adelic_int x \<Longrightarrow>
      x \<in> \<O>\<^sub>\<forall>\<^sub>p \<Longrightarrow> P"
proof-
  define x where "x \<equiv> Rep_adelic_int z"
  hence "z = Abs_adelic_int x" using Rep_adelic_int_inverse by metis
  moreover from x_def have "x \<in> \<O>\<^sub>\<forall>\<^sub>p" using Rep_adelic_int by blast
  ultimately show P using that by fast
qed

lemmas  two_Abs_adelic_int_cases   = Abs_adelic_int_cases[case_product Abs_adelic_int_cases]
  and   three_Abs_adelic_int_cases =
    Abs_adelic_int_cases[case_product Abs_adelic_int_cases[case_product Abs_adelic_int_cases]]

lemma adelic_int_seq_cases [case_names Abs_adelic_int]:
  fixes X :: "nat \<Rightarrow> 'a::nontrivial_factorial_idom adelic_int"
  obtains F :: "nat \<Rightarrow> 'a p_adic_prod"
    where "X = (\<lambda>n. Abs_adelic_int (F n))"
    and   "range F \<subseteq> \<O>\<^sub>\<forall>\<^sub>p"
proof-
  define F where "F \<equiv> \<lambda>n. Rep_adelic_int (X n)"
  hence "X = (\<lambda>n. Abs_adelic_int (F n))"
    using Rep_adelic_int_inverse by metis
  moreover from F_def have "range F \<subseteq> \<O>\<^sub>\<forall>\<^sub>p"
    using Rep_adelic_int by blast
  ultimately show thesis using that by presburger
qed

subsubsection \<open>Algebraic instantiaions\<close>

instantiation adelic_int :: (nontrivial_factorial_idom) comm_ring_1
begin

definition "0 = Abs_adelic_int 0"

lemma zero_adelic_int_rep_eq: "Rep_adelic_int 0 = 0"
  using global_p_depth_p_adic_prod.global_depth_set_0[of 0] Abs_adelic_int_inverse
  by    (simp add: zero_adelic_int_def)

definition "1 \<equiv> Abs_adelic_int 1"

lemma one_adelic_int_rep_eq: "Rep_adelic_int 1 = 1"
  using global_p_depth_p_adic_prod.global_depth_set_1 Abs_adelic_int_inverse
  by    (simp add: one_adelic_int_def)

definition "x + y = Abs_adelic_int (Rep_adelic_int x + Rep_adelic_int y)"

lemma plus_adelic_int_rep_eq: "Rep_adelic_int (a + b) = Rep_adelic_int a + Rep_adelic_int b"
  using     Rep_adelic_int global_p_depth_p_adic_prod.global_depth_set_add Abs_adelic_int_inverse
  unfolding plus_adelic_int_def
  by        fastforce

lemma plus_adelic_int_abs_eq:
  "x \<in> \<O>\<^sub>\<forall>\<^sub>p \<Longrightarrow>
    y \<in> \<O>\<^sub>\<forall>\<^sub>p \<Longrightarrow>
    Abs_adelic_int x + Abs_adelic_int y = Abs_adelic_int (x + y)"
  using     Abs_adelic_int_inverse[of x] Abs_adelic_int_inverse[of y]
  unfolding plus_adelic_int_def
  by        simp

definition "-x = Abs_adelic_int (- Rep_adelic_int x)"

lemma uminus_adelic_int_rep_eq: "Rep_adelic_int (- x) = - Rep_adelic_int x"
  using     Rep_adelic_int global_p_depth_p_adic_prod.global_depth_set_uminus
            Abs_adelic_int_inverse
  unfolding uminus_adelic_int_def
  by        auto

lemma uminus_adelic_int_abs_eq:
  "x \<in> \<O>\<^sub>\<forall>\<^sub>p \<Longrightarrow> - Abs_adelic_int x = Abs_adelic_int (- x)"
  using Abs_adelic_int_inverse[of x] unfolding uminus_adelic_int_def by simp

definition minus_adelic_int ::
  "'a adelic_int \<Rightarrow> 'a adelic_int \<Rightarrow> 'a adelic_int"
  where "minus_adelic_int \<equiv> (\<lambda>x y. x + - y)"

lemma minus_adelic_int_rep_eq: "Rep_adelic_int (x - y) = Rep_adelic_int x - Rep_adelic_int y"
  using plus_adelic_int_rep_eq uminus_adelic_int_rep_eq by (simp add: minus_adelic_int_def)

lemma minus_adelic_int_abs_eq:
  "x \<in> \<O>\<^sub>\<forall>\<^sub>p \<Longrightarrow>
    y \<in> \<O>\<^sub>\<forall>\<^sub>p \<Longrightarrow>
    Abs_adelic_int x - Abs_adelic_int y = Abs_adelic_int (x - y)"
  using global_p_depth_p_adic_prod.global_depth_set_uminus[of y]
  by    (simp add:
          minus_adelic_int_def uminus_adelic_int_abs_eq
          plus_adelic_int_abs_eq
        )

definition "x * y = Abs_adelic_int (Rep_adelic_int x * Rep_adelic_int y)"

lemma times_adelic_int_rep_eq: "Rep_adelic_int (x * y) = Rep_adelic_int x * Rep_adelic_int y"
  using     Rep_adelic_int global_p_depth_p_adic_prod.global_depth_set_times Abs_adelic_int_inverse
  unfolding times_adelic_int_def
  by        force

lemma times_adelic_int_abs_eq:
  "x \<in> \<O>\<^sub>\<forall>\<^sub>p \<Longrightarrow>
    y \<in> \<O>\<^sub>\<forall>\<^sub>p \<Longrightarrow>
    Abs_adelic_int x * Abs_adelic_int y = Abs_adelic_int (x * y)"
  using     Abs_adelic_int_inverse[of x] Abs_adelic_int_inverse[of y]
  unfolding times_adelic_int_def
  by        simp

instance
proof

  fix a b c :: "'a adelic_int"

  show "a + b = b + a" by (cases a, cases b) (simp add: plus_adelic_int_abs_eq add.commute)
  show "0 + a = a"
    using     global_p_depth_p_adic_prod.global_depth_set_0 plus_adelic_int_abs_eq[of 0]
    unfolding zero_adelic_int_def
    by        (cases a) auto
  show "1 * a = a"
    using global_p_depth_p_adic_prod.global_depth_set_1 times_adelic_int_abs_eq[of 1]
    by    (cases a) (simp add: one_adelic_int_def)
  show "- a + a = 0"
    using     global_p_depth_p_adic_prod.global_depth_set_uminus uminus_adelic_int_abs_eq
              plus_adelic_int_abs_eq
    unfolding zero_adelic_int_def
   by         (cases a) fastforce
  show "a - b = a + - b" by (simp add: minus_adelic_int_def)
  show "a * b = b * a" by (cases a, cases b) (simp add: times_adelic_int_abs_eq mult.commute)

  show "a + b + c = a + (b + c)"
  proof (cases a b c rule: three_Abs_adelic_int_cases)
    case (Abs_adelic_int_Abs_adelic_int_Abs_adelic_int x y z) thus ?thesis
      using global_p_depth_p_adic_prod.global_depth_set_add[of x]
            global_p_depth_p_adic_prod.global_depth_set_add[of y]
      by    (simp add: plus_adelic_int_abs_eq add.assoc)
  qed

  show "a * b * c = a * (b * c)"
  proof (cases a b c rule: three_Abs_adelic_int_cases)
    case (Abs_adelic_int_Abs_adelic_int_Abs_adelic_int x y z) thus "a * b * c = a * (b * c)"
      using global_p_depth_p_adic_prod.global_depth_set_times[of 0 x]
            global_p_depth_p_adic_prod.global_depth_set_times[of 0 y]
      by    (simp add: times_adelic_int_abs_eq mult.assoc)
  qed

  show "(a + b) * c = a * c + b * c"
  proof (cases a b c rule: three_Abs_adelic_int_cases)
    case (Abs_adelic_int_Abs_adelic_int_Abs_adelic_int x y z) thus "(a + b) * c = a * c + b * c"
      using global_p_depth_p_adic_prod.global_depth_set_add[of x]
            global_p_depth_p_adic_prod.global_depth_set_times[of 0 x]
            global_p_depth_p_adic_prod.global_depth_set_times[of 0 y]
      by    (simp add: plus_adelic_int_abs_eq times_adelic_int_abs_eq distrib_right)
  qed

  show "(0::'a adelic_int) \<noteq> 1"
    using     Abs_adelic_int_inject[of "0::'a p_adic_prod" 1]
              global_p_depth_p_adic_prod.global_depth_set_0
              global_p_depth_p_adic_prod.global_depth_set_1
    unfolding zero_adelic_int_def one_adelic_int_def
    by        auto

qed

end (* instantiation adelic_int :: comm_ring *)

lemma pow_adelic_int_rep_eq: "Rep_adelic_int (x ^ n) = (Rep_adelic_int x) ^ n"
  by (induct n, simp_all add: one_adelic_int_rep_eq times_adelic_int_rep_eq)

lemma pow_adelic_int_abs_eq:
  "(Abs_adelic_int x) ^ n = Abs_adelic_int (x ^ n)" if "x \<in> \<O>\<^sub>\<forall>\<^sub>p"
  using that global_p_depth_p_adic_prod.global_depth_set_0_pow times_adelic_int_abs_eq
  by    (induct n, simp add: one_adelic_int_def, fastforce)


subsubsection \<open>Equivalence and depth relative to a prime\<close>

overloading
  p_equal_adelic_int \<equiv>
    "p_equal :: 'a::nontrivial_factorial_idom prime \<Rightarrow>
      'a adelic_int \<Rightarrow> 'a adelic_int \<Rightarrow> bool"
  p_restrict_adelic_int \<equiv>
    "p_restrict :: 'a adelic_int \<Rightarrow>
      ('a prime \<Rightarrow> bool) \<Rightarrow> 'a adelic_int"
  p_depth_adelic_int \<equiv>
    "p_depth :: 'a::nontrivial_factorial_idom prime \<Rightarrow> 'a adelic_int \<Rightarrow> int"
  global_unfrmzr_pows_adelic_int \<equiv>
    "global_unfrmzr_pows :: ('a prime \<Rightarrow> nat) \<Rightarrow> 'a adelic_int"
begin

definition p_equal_adelic_int ::
  "'a::nontrivial_factorial_idom prime \<Rightarrow>
    'a adelic_int \<Rightarrow> 'a adelic_int \<Rightarrow> bool"
  where "p_equal_adelic_int p x y \<equiv> (Rep_adelic_int x) \<simeq>\<^sub>p (Rep_adelic_int y)"

definition p_restrict_adelic_int ::
  "'a::nontrivial_factorial_idom adelic_int \<Rightarrow>
    ('a prime \<Rightarrow> bool) \<Rightarrow> 'a adelic_int"
  where
    "p_restrict_adelic_int x P \<equiv> Abs_adelic_int ((Rep_adelic_int x) prestrict P)"

definition p_depth_adelic_int ::
  "'a::nontrivial_factorial_idom prime \<Rightarrow> 'a adelic_int \<Rightarrow> int"
  where "p_depth_adelic_int p x \<equiv> ((Rep_adelic_int x)\<degree>\<^sup>p)"

definition global_unfrmzr_pows_adelic_int ::
  "('a::nontrivial_factorial_idom prime \<Rightarrow> nat) \<Rightarrow> 'a adelic_int"
  where
    "global_unfrmzr_pows_adelic_int f \<equiv> Abs_adelic_int (global_unfrmzr_pows (int \<circ> f))"

end  (* overloading *)

context
  fixes p :: "'a::nontrivial_factorial_idom prime"
begin

lemma p_equal_adelic_int_abs_eq:
  "(Abs_adelic_int x) \<simeq>\<^sub>p (Abs_adelic_int y) \<longleftrightarrow>
    x \<simeq>\<^sub>p y"
  if  "x \<in> \<O>\<^sub>\<forall>\<^sub>p"
  and "y \<in> \<O>\<^sub>\<forall>\<^sub>p"
  for x y :: "'a p_adic_prod"
  using that
  by    (simp add: p_equal_adelic_int_def Abs_adelic_int_inverse)

lemma p_equal_adelic_int_abs_eq0:
  "(Abs_adelic_int x) \<simeq>\<^sub>p 0 \<longleftrightarrow> x \<simeq>\<^sub>p 0"
  if "x \<in> \<O>\<^sub>\<forall>\<^sub>p" for x :: "'a p_adic_prod"
  using     that p_equal_adelic_int_abs_eq global_p_depth_p_adic_prod.global_depth_set_0
  unfolding zero_adelic_int_def
  by        auto

lemma p_equal_adelic_int_rep_eq0:
  "(Rep_adelic_int x) \<simeq>\<^sub>p 0 \<longleftrightarrow> x \<simeq>\<^sub>p 0"
  for x :: "'a adelic_int"
  using p_equal_adelic_int_def zero_adelic_int_rep_eq by metis

lemma p_equal_adelic_int_abs_eq1:
  "(Abs_adelic_int x) \<simeq>\<^sub>p 1 \<longleftrightarrow> x \<simeq>\<^sub>p 1"
  if "x \<in> \<O>\<^sub>\<forall>\<^sub>p" for x :: "'a p_adic_prod"
  using     that p_equal_adelic_int_abs_eq global_p_depth_p_adic_prod.global_depth_set_1
  unfolding one_adelic_int_def
  by        auto

lemma p_depth_adelic_int_abs_eq:
  "(Abs_adelic_int x)\<degree>\<^sup>p = (x\<degree>\<^sup>p)"
  if "x \<in> \<O>\<^sub>\<forall>\<^sub>p" for x :: "'a p_adic_prod"
  using that by (simp add: p_depth_adelic_int_def Abs_adelic_int_inverse)

lemma adelic_int_depth: "(x\<degree>\<^sup>p) \<ge> 0" for x :: "'a adelic_int"
  using global_p_depth_p_adic_prod.nonpos_global_depth_setD p_depth_adelic_int_abs_eq
  by    (cases x) auto

end (* context nontrivial_factorial_idom *)

lemma p_restrict_adelic_int_rep_eq:
  "Rep_adelic_int (x prestrict P) = (Rep_adelic_int x) prestrict P"
  for x :: "'a::nontrivial_factorial_idom adelic_int"
  and P :: "'a prime \<Rightarrow> bool"
  using     Rep_adelic_int global_p_depth_p_adic_prod.global_depth_set_p_restrict
            Abs_adelic_int_inverse
  unfolding p_restrict_adelic_int_def
  by        fastforce

lemma p_restrict_adelic_int_abs_eq:
  "(Abs_adelic_int x) prestrict P = Abs_adelic_int (x prestrict P)"
  if "x \<in> \<O>\<^sub>\<forall>\<^sub>p"
  for x :: "'a::nontrivial_factorial_idom p_adic_prod" and P :: "'a prime \<Rightarrow> bool"
  using that Abs_adelic_int_inverse' p_restrict_adelic_int_def by metis

lemma global_unfrmzr_pows_adelic_int_rep_eq:
  "Rep_adelic_int (\<pp> f :: 'a adelic_int) = \<pp> (int \<circ> f)"
  for f :: "'a::nontrivial_factorial_idom prime \<Rightarrow> nat"
  using global_unfrmzr_pows_p_adic_prod_global_depth_set_0 Abs_adelic_int_inverse'
        global_unfrmzr_pows_adelic_int_def
  by    metis

global_interpretation p_equality_adelic_int:
  p_equality_no_zero_divisors_1
    "p_equal :: 'a::nontrivial_factorial_idom prime \<Rightarrow>
      'a adelic_int \<Rightarrow> 'a adelic_int \<Rightarrow> bool"
proof

  fix p :: "'a prime"

  show "equivp (p_equal p :: 'a adelic_int \<Rightarrow> 'a adelic_int \<Rightarrow> bool)"
    using equivp_transfer p_equality_p_adic_prod.equivp unfolding p_equal_adelic_int_def by fast

  fix x y :: "'a adelic_int"

  show "(x \<simeq>\<^sub>p y) = (x - y \<simeq>\<^sub>p 0)"
    using p_equality_p_adic_prod.conv_0
    by    (simp add: p_equal_adelic_int_def minus_adelic_int_rep_eq zero_adelic_int_rep_eq)

  show "y \<simeq>\<^sub>p 0 \<Longrightarrow> x * y \<simeq>\<^sub>p 0"
    using p_equality_p_adic_prod.mult_0_right
    by    (simp add: p_equal_adelic_int_def times_adelic_int_rep_eq zero_adelic_int_rep_eq)

  have "(1::'a adelic_int) \<not>\<simeq>\<^sub>p 0"
    unfolding p_equal_adelic_int_def
    by        (metis
                zero_adelic_int_rep_eq one_adelic_int_rep_eq
                p_equality_p_adic_prod.one_p_nequal_zero
              )
  thus "\<exists>x::'a adelic_int. x \<not>\<simeq>\<^sub>p 0" by blast

  assume "x \<not>\<simeq>\<^sub>p 0" and "y \<not>\<simeq>\<^sub>p 0"
  thus "x * y \<not>\<simeq>\<^sub>p 0"
    using p_equality_p_adic_prod.no_zero_divisors
    by    (simp add: p_equal_adelic_int_def times_adelic_int_rep_eq zero_adelic_int_rep_eq)

qed

overloading
  globally_p_equal_adelic_int \<equiv>
    "globally_p_equal ::
      'a::nontrivial_factorial_idom adelic_int \<Rightarrow> 'a adelic_int \<Rightarrow> bool"
begin

definition globally_p_equal_adelic_int ::
  "'a::nontrivial_factorial_idom adelic_int \<Rightarrow> 'a adelic_int \<Rightarrow> bool"
  where globally_p_equal_adelic_int_def[simp]:
    "globally_p_equal_adelic_int = p_equality_adelic_int.globally_p_equal"

end  (* overloading *)

global_interpretation global_p_depth_adelic_int:
  global_p_equal_depth_no_zero_divisors_w_inj_index_consts
    "p_equal :: 'a::nontrivial_factorial_idom prime \<Rightarrow>
      'a adelic_int \<Rightarrow> 'a adelic_int \<Rightarrow> bool"
    "p_restrict ::
      'a adelic_int \<Rightarrow> ('a prime \<Rightarrow> bool) \<Rightarrow> 'a adelic_int"
    "p_depth :: 'a prime \<Rightarrow> 'a adelic_int \<Rightarrow> int"
    "\<lambda>f. Abs_adelic_int (p_adic_prod_consts f)"
    Rep_prime
proof (unfold_locales, fold globally_p_equal_adelic_int_def)

  fix p :: "'a prime"

  fix x y :: "'a adelic_int"

  show "x \<simeq>\<^sub>\<forall>\<^sub>p y \<Longrightarrow> x = y"
    by (
      cases x, cases y,
      use p_equal_adelic_int_abs_eq global_p_depth_p_adic_prod.global_imp_eq in fastforce
    )

  fix P :: "'a prime \<Rightarrow> bool"
  show  "P p \<Longrightarrow> x prestrict P \<simeq>\<^sub>p x"
    by (
      cases x,
      metis global_depth_set_p_adic_prod_def p_restrict_adelic_int_abs_eq p_equal_adelic_int_abs_eq
            global_p_depth_p_adic_prod.global_depth_set_p_restrict
            global_p_depth_p_adic_prod.p_restrict_equiv
    )
  show "\<not> P p \<Longrightarrow> x prestrict P \<simeq>\<^sub>p 0"
    by (
      cases x,
      metis global_depth_set_p_adic_prod_def p_restrict_adelic_int_abs_eq p_equal_adelic_int_abs_eq0
            global_p_depth_p_adic_prod.global_depth_set_p_restrict
            global_p_depth_p_adic_prod.p_restrict_equiv0
    )

  show "((0::'a adelic_int)\<degree>\<^sup>p) = 0"
    using global_p_depth_p_adic_prod.depth_of_0
    by    (simp add: p_depth_adelic_int_def zero_adelic_int_rep_eq)

  show "x \<simeq>\<^sub>p y \<Longrightarrow> (x\<degree>\<^sup>p) = (y\<degree>\<^sup>p)"
    using global_p_depth_p_adic_prod.depth_equiv
    by    (simp add: p_equal_adelic_int_def p_depth_adelic_int_def)

  show "(- x\<degree>\<^sup>p) = (x\<degree>\<^sup>p)"
    using global_p_depth_p_adic_prod.depth_uminus
    by    (simp add: p_depth_adelic_int_def uminus_adelic_int_rep_eq)

  show
    "x \<not>\<simeq>\<^sub>p 0 \<Longrightarrow>
      (x\<degree>\<^sup>p) < (y\<degree>\<^sup>p) \<Longrightarrow>
      ((x + y)\<degree>\<^sup>p) = (x\<degree>\<^sup>p)"
    using global_p_depth_p_adic_prod.depth_pre_nonarch(1)
    by    (
            simp add: p_equal_adelic_int_def p_depth_adelic_int_def zero_adelic_int_rep_eq
                      plus_adelic_int_rep_eq
          )

  show
    "\<lbrakk>
      x \<not>\<simeq>\<^sub>p 0;
      (x + y) \<not>\<simeq>\<^sub>p 0;
      (x\<degree>\<^sup>p) = (y\<degree>\<^sup>p)
    \<rbrakk> \<Longrightarrow> (x + y\<degree>\<^sup>p) \<ge> (x\<degree>\<^sup>p)"
    using global_p_depth_p_adic_prod.depth_pre_nonarch(2)
    by    (
            fastforce
            simp add: p_equal_adelic_int_def p_depth_adelic_int_def zero_adelic_int_rep_eq
                      plus_adelic_int_rep_eq
          )

  show
    "(x * y) \<not>\<simeq>\<^sub>p 0 \<Longrightarrow>
       (x * y\<degree>\<^sup>p) = (x\<degree>\<^sup>p) + (y\<degree>\<^sup>p)"
    using global_p_depth_p_adic_prod.depth_mult_additive
    by    (
            simp add: p_equal_adelic_int_def p_depth_adelic_int_def zero_adelic_int_rep_eq
                      times_adelic_int_rep_eq
          )

  show "Abs_adelic_int (p_adic_prod_consts 1) = 1"
    by (metis global_p_depth_p_adic_prod.consts_1 one_adelic_int_def)

  fix f g :: "'a prime \<Rightarrow> 'a"

  show
    "Abs_adelic_int (p_adic_prod_consts (f - g)) =
      Abs_adelic_int (p_adic_prod_consts f) - Abs_adelic_int (p_adic_prod_consts g)"
    by (
      metis global_depth_set_p_adic_prod_def global_p_depth_p_adic_prod.consts_diff
            global_p_depth_p_adic_prod.global_depth_set_consts minus_adelic_int_abs_eq
    )

  show
    "Abs_adelic_int (p_adic_prod_consts (f * g)) =
      Abs_adelic_int (p_adic_prod_consts f) * Abs_adelic_int (p_adic_prod_consts g)"
    by (
      metis global_depth_set_p_adic_prod_def global_p_depth_p_adic_prod.consts_mult
            global_p_depth_p_adic_prod.global_depth_set_consts times_adelic_int_abs_eq
    )

  show "(Abs_adelic_int (p_adic_prod_consts f) \<simeq>\<^sub>p 0) = (f p = 0)"
    by (
      metis global_depth_set_p_adic_prod_def global_p_depth_p_adic_prod.global_depth_set_consts
            p_equal_adelic_int_abs_eq0 global_p_depth_p_adic_prod.p_equal_func_of_consts_0
    )

  show "(Abs_adelic_int (p_adic_prod_consts f)\<degree>\<^sup>p) = int (pmultiplicity p (f p))"
    by (
      metis global_depth_set_p_adic_prod_def global_p_depth_p_adic_prod.global_depth_set_consts
            p_depth_adelic_int_abs_eq global_p_depth_p_adic_prod.p_depth_func_of_consts
    )

qed
(
  metis Rep_prime_inject injI, rule Rep_prime_n0, rule Rep_prime_not_unit,
  rule multiplicity_distinct_primes
)

lemma p_depth_adelic_int_diff_abs_eq:
  "((Abs_adelic_int x - Abs_adelic_int y)\<degree>\<^sup>p) = ((x - y)\<degree>\<^sup>p)"
  if "x \<in> \<O>\<^sub>\<forall>\<^sub>p" and "y \<in> \<O>\<^sub>\<forall>\<^sub>p"
  for p :: "'a::nontrivial_factorial_idom prime" and x y :: "'a p_adic_prod"
  using that global_depth_set_p_adic_prod_def minus_adelic_int_abs_eq p_depth_adelic_int_abs_eq
        global_p_depth_p_adic_prod.global_depth_set_minus
  by    metis

lemma p_depth_adelic_int_diff_abs_eq':
  "((Abs_adelic_int (abs_p_adic_prod X) - Abs_adelic_int (abs_p_adic_prod Y))\<degree>\<^sup>p) =
    ((X - Y)\<degree>\<^sup>p)"
  if X: "X \<in> \<O>\<^sub>\<forall>\<^sub>p" and Y: "Y \<in> \<O>\<^sub>\<forall>\<^sub>p"
  for p :: "'a::nontrivial_factorial_idom prime" and X Y :: "'a fls_pseq"
proof-
  have "abs_p_adic_prod X \<in> \<O>\<^sub>\<forall>\<^sub>p"
    by (
      simp, intro global_p_depth_p_adic_prod.global_depth_setI,
      metis X p_equal_p_adic_prod_abs_eq0 p_equality_depth_fls_pseq.global_depth_setD
            global_depth_set_fls_pseq_def p_depth_p_adic_prod.abs_eq
    )
  moreover have "abs_p_adic_prod Y \<in> \<O>\<^sub>\<forall>\<^sub>p"
    by (
      simp, intro global_p_depth_p_adic_prod.global_depth_setI,
      metis Y p_equal_p_adic_prod_abs_eq0 p_equality_depth_fls_pseq.global_depth_setD
            global_depth_set_fls_pseq_def p_depth_p_adic_prod.abs_eq
    )
  ultimately show ?thesis by (metis p_depth_adelic_int_diff_abs_eq p_depth_p_adic_prod_diff_abs_eq)
qed

context
  fixes p :: "'a::nontrivial_euclidean_ring_cancel prime"
begin

lemma adelic_int_diff_depth_gt_equiv_trans:
  "((a - c)\<degree>\<^sup>p) > n"
  if  "a \<simeq>\<^sub>p b" and "b \<not>\<simeq>\<^sub>p c" and "((b - c)\<degree>\<^sup>p) > n"
  for a b c :: "'a adelic_int"
  by (
    cases a, cases b, cases c,
    metis that p_depth_adelic_int_diff_abs_eq p_equal_adelic_int_abs_eq
          p_adic_prod_diff_depth_gt_equiv_trans
  )

lemma adelic_int_diff_depth_gt0_equiv_trans:
  "((a - c)\<degree>\<^sup>p) > n"
  if "n \<ge> 0" and "a \<simeq>\<^sub>p b" and "((b - c)\<degree>\<^sup>p) > n"
  for a b c :: "'a adelic_int"
  using that p_equality_adelic_int.conv_0 adelic_int_diff_depth_gt_equiv_trans
        global_p_depth_adelic_int.depth_equiv_0[of p "b - c"]
  by    fastforce

lemma adelic_int_diff_depth_gt_trans:
  "((a - c)\<degree>\<^sup>p) > n"
  if  "a \<not>\<simeq>\<^sub>p b" and "((a - b)\<degree>\<^sup>p) > n"
  and "b \<not>\<simeq>\<^sub>p c" and "((b - c)\<degree>\<^sup>p) > n"
  and "a \<not>\<simeq>\<^sub>p c"
  for a b c :: "'a adelic_int"
  by (
    cases a, cases b, cases c,
    metis that p_depth_adelic_int_diff_abs_eq p_equal_adelic_int_abs_eq
          p_adic_prod_diff_depth_gt_trans
  )

lemma adelic_int_diff_depth_gt0_trans:
  "((a - c)\<degree>\<^sup>p) > n"
  if  "n \<ge> 0"
  and "((a - b)\<degree>\<^sup>p) > n"
  and "((b - c)\<degree>\<^sup>p) > n"
  and "a \<not>\<simeq>\<^sub>p c"
  for a b c :: "'a adelic_int"
  using that adelic_int_diff_depth_gt_trans
        p_equality_adelic_int.conv_0[of p a b] p_equality_adelic_int.conv_0[of p b c]
        global_p_depth_adelic_int.depth_equiv_0[of p "a - b"]
        global_p_depth_adelic_int.depth_equiv_0[of p "b - c"]
  by    auto

lemma adelic_int_prestrict_zero_depth:
  "1 \<le> ((x prestrict (\<lambda>p::'a prime. (x\<degree>\<^sup>p) = 0) - x)\<degree>\<^sup>p)"
  if "x prestrict (\<lambda>p::'a prime. (x\<degree>\<^sup>p) = 0) \<not>\<simeq>\<^sub>p x"
  for x :: "'a adelic_int"
  using that adelic_int_depth[of p x] global_p_depth_adelic_int.depth_equiv[of p]
        global_p_depth_adelic_int.p_restrict_equiv[of "\<lambda>p. (x\<degree>\<^sup>p) = 0"]
        global_p_depth_adelic_int.p_restrict_equiv0[of "\<lambda>p. (x\<degree>\<^sup>p) = 0" p x]
        p_equality_adelic_int.minus_right[of p _ _ x] global_p_depth_adelic_int.depth_uminus[of p x]
  by    force

end (* context nontrivial_euclidean_ring_cancel *)

lemma adelic_int_normalize_depth:
  "(x * \<pp> (\<lambda>p::'a prime. -(x\<degree>\<^sup>p))) \<in> \<O>\<^sub>\<forall>\<^sub>p"
  for x :: "'a::nontrivial_factorial_idom p_adic_prod"
  using p_adic_prod_normalize_depth[of _ x] by (fastforce intro: p_adic_prod_global_depth_setI')

lemma global_unfrmzr_pows0_adelic_int:
  "(\<pp> (0 :: 'a::nontrivial_factorial_idom prime \<Rightarrow> nat) :: 'a adelic_int) = 1"
proof-
  have "int \<circ> (0 :: 'a prime \<Rightarrow> nat) = (0 :: 'a prime \<Rightarrow> int)" by auto
  thus ?thesis
    using     global_unfrmzr_pows_p_adic_prod0
    unfolding global_unfrmzr_pows_adelic_int_def one_adelic_int_def
    by        metis
qed

context
  fixes p :: "'a::nontrivial_factorial_idom prime"
begin

lemma global_unfrmzr_pows_adelic_int:
  "(\<pp> f :: 'a adelic_int)\<degree>\<^sup>p = int (f p)" for f :: "'a prime \<Rightarrow> nat"
  using     global_unfrmzr_pows_p_adic_prod_global_depth_set_0 p_depth_adelic_int_abs_eq[of _ p]
            global_unfrmzr_pows_p_adic_prod[of p]
  unfolding global_unfrmzr_pows_adelic_int_def
  by        fastforce

lemma global_unfrmzr_pows_adelic_int_pequiv_iff:
  "((\<pp> f :: 'a adelic_int) \<simeq>\<^sub>p (\<pp> g)) = (f p = g p)"
  for f g :: "'a prime \<Rightarrow> nat"
proof-
  have "((int \<circ> f) p = (int \<circ> g) p) = (f p = g p)" by fastforce
  thus ?thesis
    using     global_unfrmzr_pows_p_adic_prod_global_depth_set_0 p_equal_adelic_int_abs_eq
              global_unfrmzr_pows_p_adic_prod_pequiv_iff
    unfolding global_unfrmzr_pows_adelic_int_def
    by        blast
qed

end (* context nontrivial_factorial_idom *)

lemma global_unfrmzr_pows_prod_adelic_int:
  "(\<pp> f :: 'a adelic_int) * (\<pp> g) = \<pp> (f + g)"
  for f g :: "'a::nontrivial_factorial_idom prime \<Rightarrow> nat"
proof-
  have "(int \<circ> f) + (int \<circ> g) = int \<circ> (f + g)" by fastforce
  thus ?thesis
    using     global_unfrmzr_pows_p_adic_prod_global_depth_set_0 times_adelic_int_abs_eq
              global_unfrmzr_pows_prod_p_adic_prod
    unfolding global_unfrmzr_pows_adelic_int_def
    by        metis
qed

context
  fixes p :: "'a::nontrivial_factorial_idom prime"
begin

lemma global_unfrmzr_pows_adelic_int_nzero:
  "(\<pp> f :: 'a adelic_int) \<not>\<simeq>\<^sub>p 0" for f :: "'a prime \<Rightarrow> nat"
  using     global_unfrmzr_pows_p_adic_prod_global_depth_set_0 p_equal_adelic_int_abs_eq0
            global_unfrmzr_pows_p_adic_prod_nzero
  unfolding global_unfrmzr_pows_adelic_int_def
  by        blast

lemma prod_w_global_unfrmzr_pows_adelic_int:
  "(x * \<pp> f)\<degree>\<^sup>p = (x\<degree>\<^sup>p) + int (f p)"
  if  "x \<not>\<simeq>\<^sub>p 0" for f :: "'a prime \<Rightarrow> nat" and x :: "'a adelic_int"
proof (cases x)
  case (Abs_adelic_int a)
  moreover have "(\<lambda>x. int (f x)) = int \<circ> f" by auto
  moreover from that Abs_adelic_int have "a \<not>\<simeq>\<^sub>p 0"
    using p_equal_adelic_int_abs_eq0[of a p] by blast
  ultimately have
    "((x * \<pp> f)\<degree>\<^sup>p) =
      (a\<degree>\<^sup>p) + int (f p)"
    using     that times_adelic_int_abs_eq global_unfrmzr_pows_p_adic_prod_global_depth_set_0
              p_depth_adelic_int_abs_eq global_depth_set_p_adic_prod_def
              global_p_depth_p_adic_prod.global_depth_set_times[of 0 _ "\<pp> (int \<circ> f)"]
              prod_w_global_unfrmzr_pows_p_adic_prod[of p a f]
    unfolding global_unfrmzr_pows_adelic_int_def
    by        fastforce
  with Abs_adelic_int show ?thesis using p_depth_adelic_int_abs_eq by fastforce
qed

lemma trivial_global_unfrmzr_pows_adelic_int:
  "(\<pp> f :: 'a adelic_int) \<simeq>\<^sub>p 1" if "f p = 0" for f :: "'a prime \<Rightarrow> nat"
  using     that p_equal_adelic_int_abs_eq1 global_unfrmzr_pows_p_adic_prod_global_depth_set_0
            trivial_global_unfrmzr_pows_p_adic_prod[of _ p]
  unfolding global_unfrmzr_pows_adelic_int_def
  by        force

lemma prod_w_trivial_global_unfrmzr_pows_adelic_int:
  "x * \<pp> f \<simeq>\<^sub>p x" if "f p = 0"
  for f :: "'a prime \<Rightarrow> nat" and x :: "'a adelic_int"
  using that p_equality_adelic_int.mult_one_right trivial_global_unfrmzr_pows_adelic_int by blast

end (* context nontrivial_factorial_idom *)

lemma pow_global_unfrmzr_pows_adelic_int:
  "(\<pp> f :: 'a adelic_int) ^ n = (\<pp> ((\<lambda>p. n) * f))"
  for f :: "'a::nontrivial_factorial_idom prime \<Rightarrow> nat"
proof-
  have "(\<lambda>p. int n * (int \<circ> f) p) = int \<circ> ((\<lambda>p. n) * f)" by auto
  thus ?thesis
    using     global_unfrmzr_pows_p_adic_prod_global_depth_set_0 pow_adelic_int_abs_eq
              global_unfrmzr_pows_p_adic_prod_pow
    unfolding global_unfrmzr_pows_adelic_int_def
    by        metis
qed

abbreviation "adelic_int_consts \<equiv> global_p_depth_adelic_int.consts"
abbreviation "adelic_int_const  \<equiv> global_p_depth_adelic_int.const"

lemma adelic_int_p_depth_consts:
  "(adelic_int_consts f)\<degree>\<^sup>p = ((f p)\<degree>\<^sup>p)"
  for p :: "'a::nontrivial_factorial_idom prime" and f :: "'a prime \<Rightarrow> 'a"
  using global_depth_set_p_adic_prod_def global_p_depth_p_adic_prod.global_depth_set_consts
        p_depth_adelic_int_abs_eq p_depth_p_adic_prod_consts
  by    metis

lemmas adelic_int_p_depth_const = adelic_int_p_depth_consts[of _ "\<lambda>p. _"]

lemma adelic_int_global_unfrmzr:
  "(\<pp> (1 :: 'a::nontrivial_factorial_idom prime \<Rightarrow> nat) :: 'a adelic_int)
    = adelic_int_consts Rep_prime"
proof-
  define natfun_1 :: "'a prime \<Rightarrow> nat" and intfun_1 :: "'a prime \<Rightarrow> int"
    where "natfun_1 \<equiv> 1" and "intfun_1 \<equiv> 1"
  moreover from this have "int \<circ> natfun_1 = intfun_1" by auto
  ultimately show ?thesis
    using p_adic_prod_global_unfrmzr unfolding global_unfrmzr_pows_adelic_int_def by metis
qed

lemma adelic_int_normalize_depthE:
  fixes   x :: "'a::nontrivial_factorial_idom adelic_int"
  obtains x_0
  where   "\<forall>p::'a prime. x_0\<degree>\<^sup>p = 0"
  and     "x = x_0 * \<pp> (\<lambda>p::'a prime. nat (x\<degree>\<^sup>p))"
proof (cases x)
  define f :: "'a prime \<Rightarrow> nat"
    where "f \<equiv> \<lambda>p::'a prime. nat (x\<degree>\<^sup>p)"
  case (Abs_adelic_int a)
  obtain a_0 where a_0:
    "\<forall>p::'a prime. a_0\<degree>\<^sup>p = 0"
    "a = a_0 * \<pp> (\<lambda>p::'a prime. (a\<degree>\<^sup>p))"
    by (elim p_adic_prod_normalize_depthE)
  from a_0(1) have a_0_int: "a_0 \<in> \<O>\<^sub>\<forall>\<^sub>p"
    using p_adic_prod_global_depth_setI'[of 0 a_0] by auto
  moreover from f_def Abs_adelic_int
    have  "(\<lambda>p::'a prime. (a\<degree>\<^sup>p)) = int \<circ> f"
    using p_depth_adelic_int_abs_eq adelic_int_depth
    by    fastforce
  ultimately have "x = Abs_adelic_int a_0 * \<pp> f"
    using f_def Abs_adelic_int(1) a_0(2) times_adelic_int_abs_eq
          global_unfrmzr_pows_p_adic_prod_global_depth_set[of 0 "int \<circ> f"]
          global_unfrmzr_pows_adelic_int_def[of f]
    by    fastforce
  moreover from a_0(1) have "\<forall>p::'a prime. (Abs_adelic_int (a_0))\<degree>\<^sup>p = 0"
    using a_0_int p_depth_adelic_int_abs_eq by metis
  ultimately show thesis using that f_def by presburger
qed


subsubsection \<open>Inverses\<close>

text \<open>We can create inverses at depth-zero places.\<close>

instantiation adelic_int ::
  (nontrivial_factorial_unique_euclidean_bezout) "{divide_trivial, inverse}"
begin

definition inverse_adelic_int ::
  "'a adelic_int \<Rightarrow> 'a adelic_int"
  where
    "inverse_adelic_int x =
      Abs_adelic_int (
        (inverse (Rep_adelic_int x)) prestrict (\<lambda>p::'a prime. x\<degree>\<^sup>p = 0)
      )"

definition divide_adelic_int ::
  "'a adelic_int \<Rightarrow> 'a adelic_int \<Rightarrow> 'a adelic_int"
  where divide_adelic_int_def[simp]: "divide_adelic_int x y = x * inverse y"

instance
proof
  fix x :: "'a adelic_int"
  have "(\<lambda>p::'a prime. (0::'a adelic_int)\<degree>\<^sup>p = 0) = (\<lambda>p. True)"
    using global_p_depth_adelic_int.depth_of_0 by fast
  hence "x div 0 = x * Abs_adelic_int (0 prestrict (\<lambda>p::'a prime. True))"
    using     inverse_adelic_int_def[of 0]
    unfolding zero_adelic_int_rep_eq p_adic_prod_div_inv.inverse_0
    by        simp
  thus "x div 0 = 0"
    by (metis global_p_depth_p_adic_prod.p_restrict_true mult_zero_right zero_adelic_int_def)
  have "(\<lambda>p::'a prime. (1::'a adelic_int)\<degree>\<^sup>p = 0) = (\<lambda>p. True)"
    using global_p_depth_adelic_int.p_depth_1 by fast
  hence "x div 1 = x * Abs_adelic_int (1 prestrict (\<lambda>p::'a prime. True))"
    using     inverse_adelic_int_def[of 1]
    unfolding one_adelic_int_rep_eq p_adic_prod_div_inv.inverse_1
    by        simp
  thus "x div 1 = x"
    by (metis global_p_depth_p_adic_prod.p_restrict_true mult_1_right one_adelic_int_def)
qed simp

end

lemma inverse_adelic_int_abs_eq:
  "inverse (Abs_adelic_int x) =
    Abs_adelic_int (inverse x prestrict (\<lambda>p::'a prime. x\<degree>\<^sup>p = 0))"
  if  "x \<in> \<O>\<^sub>\<forall>\<^sub>p"
  for x :: "'a::nontrivial_factorial_unique_euclidean_bezout p_adic_prod"
  using     that Abs_adelic_int_inverse[of x] p_depth_adelic_int_abs_eq[of x]
  unfolding inverse_adelic_int_def
  by        auto

lemma divide_adelic_int_abs_eq:
  "Abs_adelic_int x / Abs_adelic_int y =
      Abs_adelic_int ((x / y) prestrict (\<lambda>p::'a prime. y\<degree>\<^sup>p = 0))"
  if "x \<in> \<O>\<^sub>\<forall>\<^sub>p" and "y \<in> \<O>\<^sub>\<forall>\<^sub>p"
  for x y :: "'a::nontrivial_factorial_unique_euclidean_bezout p_adic_prod"
  using that divide_adelic_int_def inverse_adelic_int_abs_eq global_depth_set_p_adic_prod_def
        p_adic_prod_div_inv.global_depth_set_inverse times_adelic_int_abs_eq
        global_p_depth_p_adic_prod.times_p_restrict p_adic_prod_div_inv.divide_inverse
  by    metis

lemma p_depth_adelic_int_inverse_diff_abs_eq:
  "((inverse (Abs_adelic_int x) - inverse (Abs_adelic_int y))\<degree>\<^sup>p) =
    ((inverse x - inverse y)\<degree>\<^sup>p)"
  if  "x \<in> \<O>\<^sub>\<forall>\<^sub>p" "x\<degree>\<^sup>p = 0"
  and "y \<in> \<O>\<^sub>\<forall>\<^sub>p" "y\<degree>\<^sup>p = 0"
  for p :: "'a::nontrivial_factorial_unique_euclidean_bezout prime" and x y :: "'a p_adic_prod"
  using that inverse_adelic_int_abs_eq p_adic_prod_div_inv.global_depth_set_inverse
        p_depth_adelic_int_diff_abs_eq[of
          "inverse x prestrict (\<lambda>p::'a prime. (x\<degree>\<^sup>p) = 0)"
        ]
        global_depth_set_p_adic_prod_def global_p_depth_p_adic_prod.depth_diff_equiv[of p]
        global_p_depth_p_adic_prod.p_restrict_equiv[of _ p]
  by    fastforce

context
  fixes x :: "'a::nontrivial_factorial_unique_euclidean_bezout adelic_int"
begin

lemma inverse_adelic_int_rep_eq:
  "Rep_adelic_int (inverse x) =
    (inverse (Rep_adelic_int x)) prestrict (\<lambda>p::'a prime. x\<degree>\<^sup>p = 0)"
  using     Rep_adelic_int p_adic_prod_div_inv.global_depth_set_inverse Abs_adelic_int_inverse
  unfolding inverse_adelic_int_def
  by        (auto simp add: p_depth_adelic_int_def)

lemma adelic_int_inverse_equiv0_iff:
  "inverse x \<simeq>\<^sub>p 0 \<longleftrightarrow>
    (x \<simeq>\<^sub>p 0 \<or> (x\<degree>\<^sup>p) \<noteq> 0)"
  for p :: "'a prime"
proof (cases x)
  case (Abs_adelic_int a)
  thus ?thesis
    using inverse_adelic_int_abs_eq[of a] p_adic_prod_div_inv.global_depth_set_inverse[of a]
          p_equal_adelic_int_abs_eq0[of _ p]
          global_p_depth_p_adic_prod.p_restrict_equiv0[of _ p "inverse a"]
          global_p_depth_p_adic_prod.p_restrict_equiv[of _ p "inverse a"]
          p_equality_p_adic_prod.trans0_iff[of p _ "inverse a"]
          p_adic_prod_div_inv.inverse_equiv0_iff[of p] p_depth_adelic_int_abs_eq[of a]
    by    auto
qed

lemma adelic_int_inverse_equiv0_iff':
  "inverse x \<simeq>\<^sub>p 0 \<longleftrightarrow>
    (x \<simeq>\<^sub>p 0 \<or> (x\<degree>\<^sup>p) \<ge> 1)"
  for p :: "'a prime"
  using adelic_int_inverse_equiv0_iff adelic_int_depth[of p x] by force

end (* context nontrivial_factorial_unique_euclidean_bezout *)

lemma adelic_int_inverse_eq0_iff:
  "inverse x = 0 \<longleftrightarrow>
    (\<forall>p::'a prime. x\<degree>\<^sup>p = 0 \<longrightarrow> x \<simeq>\<^sub>p 0)"
  for x :: "'a::nontrivial_factorial_unique_euclidean_bezout adelic_int"
proof (standard, clarify)
  fix p :: "'a prime" assume "inverse x = 0" "x\<degree>\<^sup>p = 0" thus "x \<simeq>\<^sub>p 0"
    using adelic_int_inverse_equiv0_iff by fastforce
next
  assume x: "\<forall>p::'a prime. x\<degree>\<^sup>p = 0 \<longrightarrow> x \<simeq>\<^sub>p 0"
  show "inverse x = 0"
  proof (intro global_p_depth_adelic_int.global_imp_eq, standard)
    fix p :: "'a prime"
    from x show "inverse x \<simeq>\<^sub>p 0"
      using adelic_int_depth[of p x] adelic_int_inverse_equiv0_iff
      by    (cases "x\<degree>\<^sup>p = 0", fast, fastforce)
  qed
qed

lemma divide_adelic_int_rep_eq:
  "Rep_adelic_int (x / y) =
    (Rep_adelic_int x / Rep_adelic_int y) prestrict (\<lambda>p::'a prime. y\<degree>\<^sup>p = 0)"
  for x y :: "'a::nontrivial_factorial_unique_euclidean_bezout adelic_int"
  using divide_adelic_int_def times_adelic_int_rep_eq inverse_adelic_int_rep_eq
        global_p_depth_p_adic_prod.times_p_restrict p_adic_prod_div_inv.divide_inverse
  by    metis

lemma adelic_int_divide_by_pequiv0:
  "x / y \<simeq>\<^sub>p 0" if "y \<simeq>\<^sub>p 0"
  for p :: "'a::nontrivial_factorial_unique_euclidean_bezout prime" and x y :: "'a adelic_int"
  using that divide_adelic_int_def adelic_int_inverse_equiv0_iff p_equality_adelic_int.mult_0_right
  by    metis

lemma adelic_int_divide_by_pos_depth:
  "x / y \<simeq>\<^sub>p 0" if "(y\<degree>\<^sup>p) > 0"
  for p :: "'a::nontrivial_factorial_unique_euclidean_bezout prime" and x y :: "'a adelic_int"
  using that adelic_int_inverse_equiv0_iff p_equality_adelic_int.mult_0_right[of p] by force

lemma adelic_int_inverse0[simp]:
  "inverse (0::'a::nontrivial_factorial_unique_euclidean_bezout adelic_int) = 0"
  using adelic_int_inverse_eq0_iff by force

lemma adelic_int_inverse1[simp]:
  "inverse (1::'a::nontrivial_factorial_unique_euclidean_bezout adelic_int) = 1"
proof-
  have "(\<lambda>p::'a prime. (1::'a p_adic_prod)\<degree>\<^sup>p = 0) = (\<lambda>p. True)"
    by simp
  thus ?thesis
    using global_depth_set_p_adic_prod_def one_adelic_int_def inverse_adelic_int_abs_eq
          global_p_depth_p_adic_prod.global_depth_set_1 p_adic_prod_div_inv.inverse_1
          global_p_depth_p_adic_prod.p_restrict_true
    by    metis
qed

lemma adelic_int_inverse_mult:
  "inverse (x * y) = inverse x * inverse y"
  for x y :: "'a::nontrivial_factorial_unique_euclidean_bezout adelic_int"
proof (
  intro global_p_depth_adelic_int.global_imp_eq, standard, cases x y rule: two_Abs_adelic_int_cases
)
  case (Abs_adelic_int_Abs_adelic_int a b)
  fix p :: "'a prime"
  define P :: "'a p_adic_prod \<Rightarrow> 'a prime \<Rightarrow> bool"
    where "P \<equiv> (\<lambda>z p. z\<degree>\<^sup>p = 0)"
  define iab iab' ia ib
    where "iab  \<equiv> inverse (a * b) prestrict (P (a * b))"
    and   "iab' \<equiv> inverse (a * b) prestrict (\<lambda>p. P a p \<and> P b p)"
    and   "ia   \<equiv> inverse a prestrict (P a)"
    and   "ib   \<equiv> inverse b prestrict (P b)"
  from P_def Abs_adelic_int_Abs_adelic_int(2,4) have
    "P (a * b) p \<Longrightarrow> inverse (a *b) \<not>\<simeq>\<^sub>p 0 \<Longrightarrow>
      P a p \<and> P b p"
    using p_adic_prod_div_inv.inverse_equiv0_iff global_p_depth_p_adic_prod.depth_mult_additive
          global_p_depth_p_adic_prod.nonpos_global_depth_setD[of 0 a p]
          global_p_depth_p_adic_prod.nonpos_global_depth_setD[of 0 b p]
          global_depth_set_p_adic_prod_def
    by    force
  moreover from P_def have
    "\<not> P (a * b) p \<Longrightarrow> P a p \<Longrightarrow> P b p \<Longrightarrow>
      inverse (a * b) \<simeq>\<^sub>p 0"
    using global_p_depth_p_adic_prod.depth_mult_additive p_adic_prod_div_inv.inverse_equiv0_iff
    by    force
  ultimately have "iab \<simeq>\<^sub>p iab'"
    using     global_p_depth_p_adic_prod.p_restrict_p_equal_p_restrictI[of _ p]
    unfolding iab_def iab'_def
    by        force
  moreover from iab'_def ia_def ib_def have "iab' \<simeq>\<^sub>p ia * ib"
    using global_p_depth_p_adic_prod.p_restrict_times_equiv[of p _ "P a" _ "P b"]
          p_adic_prod_div_inv.inverse_mult p_equality_p_adic_prod.sym by metis
  ultimately have "iab \<simeq>\<^sub>p ia * ib" using p_equality_p_adic_prod.trans by metis
  with Abs_adelic_int_Abs_adelic_int P_def iab_def ia_def ib_def show
    "inverse (x * y) \<simeq>\<^sub>p
      (inverse x * inverse y)"
    using global_depth_set_p_adic_prod_def p_adic_prod_div_inv.global_depth_set_inverse
          global_p_depth_p_adic_prod.global_depth_set_times times_adelic_int_abs_eq
          p_equal_adelic_int_abs_eq[of
            "inverse (a * b) prestrict (P (a * b))"
            "(inverse a prestrict (P a)) * (inverse b prestrict (P b))"
          ]
          inverse_adelic_int_abs_eq[of a] inverse_adelic_int_abs_eq[of b]
          inverse_adelic_int_abs_eq[of "a * b"]
    by    fastforce
qed

lemma adelic_int_inverse_pcong:
  "(inverse x) \<simeq>\<^sub>p (inverse y)" if "x \<simeq>\<^sub>p y"
  for p :: "'a::nontrivial_factorial_unique_euclidean_bezout prime" and x y :: "'a adelic_int"
proof (cases x y rule: two_Abs_adelic_int_cases)
  case (Abs_adelic_int_Abs_adelic_int a b)
  with that have "a \<simeq>\<^sub>p b" using p_equal_adelic_int_abs_eq by blast
  moreover define d :: "'a p_adic_prod \<Rightarrow> 'a prime \<Rightarrow> bool"
    where "d \<equiv> \<lambda>z p. z\<degree>\<^sup>p = 0"
  ultimately have "(inverse a prestrict (d a)) \<simeq>\<^sub>p (inverse b prestrict (d b))"
    by (
      auto
        intro   : global_p_depth_p_adic_prod.p_restrict_p_equal_p_restrictI
        simp add: p_adic_prod_div_inv.inverse_pcong global_p_depth_p_adic_prod.depth_equiv
    )
  with Abs_adelic_int_Abs_adelic_int d_def show ?thesis
    using inverse_adelic_int_abs_eq[of a] inverse_adelic_int_abs_eq[of b] p_equal_adelic_int_abs_eq
          p_adic_prod_div_inv.global_depth_set_inverse[of a]
          p_adic_prod_div_inv.global_depth_set_inverse[of b]
    by    auto
qed

context
  fixes x :: "'a::nontrivial_factorial_unique_euclidean_bezout adelic_int"
begin

lemma adelic_int_inverse_uminus: "inverse (-x) = - inverse x"
proof (cases x)
  case (Abs_adelic_int a) thus ?thesis
    using global_depth_set_p_adic_prod_def global_p_depth_p_adic_prod.global_depth_set_uminus[of a]
          uminus_adelic_int_abs_eq[of a] p_adic_prod_div_inv.inverse_uminus[of a]
          uminus_adelic_int_abs_eq[of "inverse a prestrict _"]
          p_adic_prod_div_inv.global_depth_set_inverse[of a]
          inverse_adelic_int_abs_eq[of "-a"] inverse_adelic_int_abs_eq[of a]
          global_p_depth_p_adic_prod.p_restrict_uminus[of "inverse a"]
          global_p_depth_p_adic_prod.depth_uminus[of _ a]
    by    fastforce
qed

lemma adelic_int_inverse_inverse:
  "inverse (inverse x) = x prestrict (\<lambda>p::'a prime. x\<degree>\<^sup>p = 0)"
proof (cases x)
  case (Abs_adelic_int a)
  moreover define P where "P \<equiv> (\<lambda>p::'a prime. a\<degree>\<^sup>p = 0)"
  moreover from this
    have  "(\<lambda>p::'a prime. P p \<and> (inverse a prestrict P)\<degree>\<^sup>p = 0) = P"
    using global_p_depth_p_adic_prod.p_restrict_depth[of P]
          p_adic_prod_div_inv.inverse_depth[of _ a]
    by    auto
  ultimately show ?thesis
    using inverse_adelic_int_abs_eq p_adic_prod_div_inv.global_depth_set_inverse[of a]
          p_adic_prod_div_inv.inverse_inverse[of a]
          inverse_adelic_int_abs_eq[of "inverse a prestrict P"] p_depth_adelic_int_abs_eq
          p_adic_prod_div_inv.inverse_p_restrict[of "inverse a" P] p_restrict_adelic_int_abs_eq
          global_p_depth_p_adic_prod.p_restrict_restrict[of a P]
    by    fastforce
qed

lemma adelic_int_inverse_pow: "inverse (x ^ n) = (inverse x) ^ n"
  by (induct n, simp_all add: adelic_int_inverse_mult)

lemma adelic_int_divide_self':
  "x / x \<simeq>\<^sub>p 1" if "x \<not>\<simeq>\<^sub>p 0" and "x\<degree>\<^sup>p = 0"
  for p :: "'a prime"
proof (cases x)
  case (Abs_adelic_int a)
  define P :: "'a prime \<Rightarrow> bool"
    where "P \<equiv> (\<lambda>p. (a\<degree>\<^sup>p) = 0)"
  moreover from that Abs_adelic_int have "a \<not>\<simeq>\<^sub>p 0" "a\<degree>\<^sup>p = 0"
    using that p_equal_adelic_int_abs_eq0 p_depth_adelic_int_abs_eq by (blast, fastforce)
  ultimately
    have  "Abs_adelic_int (a / a prestrict P) \<simeq>\<^sub>p (Abs_adelic_int 1)"
    using Abs_adelic_int(2) global_p_depth_p_adic_prod.p_restrict_equiv[of P p]
          p_adic_prod_div_inv.divide_right_equiv[of p _ a]
          p_adic_prod_div_inv.divide_self_equiv[of p] p_equality_p_adic_prod.trans[of p _ "a / a" 1]
          p_adic_prod_div_inv.divide_p_restrict_right[of a a]
          p_adic_prod_div_inv.global_depth_set_divide[of a 0]
          p_equal_adelic_int_abs_eq global_p_depth_p_adic_prod.global_depth_set_1
    by    fastforce
  with Abs_adelic_int P_def show ?thesis using divide_adelic_int_abs_eq one_adelic_int_def by metis
qed

lemma adelic_int_global_divide_self:
  "x / x = 1"
  if    "\<forall>p::'a prime. x \<not>\<simeq>\<^sub>p 0"
  and   "\<forall>p::'a prime. x\<degree>\<^sup>p = 0"
  using that global_p_depth_adelic_int.global_imp_eq adelic_int_divide_self' by fastforce

lemma adelic_int_divide_self:
  "x / x =
    1 prestrict (\<lambda>p::'a prime. x \<not>\<simeq>\<^sub>p 0 \<and> x\<degree>\<^sup>p = 0)"
proof (intro global_p_depth_adelic_int.global_imp_eq, standard)
  define P :: "'a prime \<Rightarrow> bool"
    where "P \<equiv> (\<lambda>p. x \<not>\<simeq>\<^sub>p 0 \<and> x\<degree>\<^sup>p = 0)"
  fix p :: "'a prime" show "x / x \<simeq>\<^sub>p 1 prestrict P"
  proof (cases "P p")
    case True with P_def show ?thesis
      using p_equality_adelic_int.trans_left adelic_int_divide_self'[of p]
            global_p_depth_adelic_int.p_restrict_equiv[of _ p]
      by    force
  next
    case False
    moreover from this P_def have "x / x \<simeq>\<^sub>p 0"
      using divide_adelic_int_def adelic_int_inverse_equiv0_iff
            p_equality_adelic_int.mult_0_right
      by    metis
    ultimately show ?thesis
      using global_p_depth_adelic_int.p_restrict_equiv0 p_equality_adelic_int.trans_left by metis
  qed
qed

lemma adelic_int_p_restrict_inverse:
  "(inverse x) prestrict P = inverse (x prestrict P)" for P :: "'a prime \<Rightarrow> bool"
proof (cases x)
  case (Abs_adelic_int a)
  moreover have
    "(\<lambda>p::'a prime. a\<degree>\<^sup>p = 0 \<and> P p) =
      (\<lambda>p::'a prime. P p \<and> (a prestrict P)\<degree>\<^sup>p = 0)"
    using global_p_depth_p_adic_prod.p_restrict_equiv global_p_depth_p_adic_prod.depth_equiv
    by    metis
  ultimately show ?thesis
    using inverse_adelic_int_abs_eq[of a] inverse_adelic_int_abs_eq[of "a prestrict P"]
          p_adic_prod_div_inv.global_depth_set_inverse[of a] p_restrict_adelic_int_abs_eq[of _ P]
          p_adic_prod_div_inv.inverse_p_restrict[of a]
          global_p_depth_p_adic_prod.p_restrict_restrict[of "inverse a"]
          global_p_depth_p_adic_prod.global_depth_set_p_restrict[of a 0 P]
    by    force
qed

lemma adelic_int_inverse_depth: "(inverse x)\<degree>\<^sup>p = 0" for p :: "'a prime"
proof (cases x)
  case (Abs_adelic_int X)
  hence
    "(inverse x)\<degree>\<^sup>p =
      ((inverse X prestrict (\<lambda>p::'a prime. X\<degree>\<^sup>p = 0))\<degree>\<^sup>p)"
    using inverse_adelic_int_abs_eq p_adic_prod_div_inv.global_depth_set_inverse
          p_depth_adelic_int_abs_eq
    by    fastforce
  thus ?thesis
    using global_p_depth_p_adic_prod.p_restrict_equiv[of _ p "inverse X"]
          global_p_depth_p_adic_prod.depth_equiv[of p _ "inverse X"]
          p_adic_prod_div_inv.inverse_depth[of p X] global_p_depth_p_adic_prod.depth_equiv_0[of p]
          global_p_depth_p_adic_prod.p_restrict_equiv0[of _ p "inverse X"]
    by    (cases "X\<degree>\<^sup>p = 0", presburger, presburger)
qed

end (* context nontrivial_factorial_unique_euclidean_bezout *)

lemma adelic_int_consts_divide_self:
  "(adelic_int_consts f) / (adelic_int_consts f) =
    1 prestrict (\<lambda>p::'a prime. f p \<noteq> 0 \<and> (f p)\<degree>\<^sup>p = 0)"
  for f :: "'a::nontrivial_factorial_unique_euclidean_bezout prime \<Rightarrow> 'a"
  using adelic_int_divide_self[of "adelic_int_consts f"] adelic_int_p_depth_consts[of _ f]
        global_p_depth_adelic_int.p_equal_func_of_consts_0[of _ f]
  by    presburger

lemma adelic_int_const_divide_self:
  "(adelic_int_const c) / (adelic_int_const c) =
    1 prestrict (\<lambda>p::'a prime. c\<degree>\<^sup>p = 0)"
  if "c \<noteq> 0" for c :: "'a::nontrivial_factorial_unique_euclidean_bezout"
  using that by (simp del: divide_adelic_int_def add: adelic_int_consts_divide_self)

lemma adelic_int_consts_divide_self':
  "(adelic_int_consts f) / (adelic_int_consts f) \<simeq>\<^sub>p 1"
  if "f p \<noteq> 0" and "(f p)\<degree>\<^sup>p = 0"
  for f :: "'a::nontrivial_factorial_unique_euclidean_bezout prime \<Rightarrow> 'a"
  using that adelic_int_consts_divide_self[of f] global_p_depth_adelic_int.p_restrict_equiv[of _ p]
  by    presburger

lemma adelic_int_divide_depth:
  "(x / y)\<degree>\<^sup>p = (x\<degree>\<^sup>p)" if "x / y \<not>\<simeq>\<^sub>p 0"
  for x y :: "'a::nontrivial_factorial_unique_euclidean_bezout adelic_int" and p :: "'a prime"
proof (cases x y rule: two_Abs_adelic_int_cases)
  case (Abs_adelic_int_Abs_adelic_int a b)
  from that Abs_adelic_int_Abs_adelic_int(3,4) have db: "b\<degree>\<^sup>p = 0"
    using p_depth_adelic_int_abs_eq adelic_int_depth[of p y] adelic_int_divide_by_pos_depth[of p y]
    by    fastforce
  moreover have "a / b \<not>\<simeq>\<^sub>p 0"
  proof
    assume "a / b \<simeq>\<^sub>p 0" with that Abs_adelic_int_Abs_adelic_int db show False
      using global_p_depth_p_adic_prod.p_restrict_equiv[of _ p "a / b"]
            p_equality_p_adic_prod.trans[of p _ "a / b" 0]
            p_adic_prod_div_inv.global_depth_set_divide[of a 0 b]
            p_equal_adelic_int_abs_eq0 divide_adelic_int_abs_eq[of a b]
      by    force
  qed
  ultimately show "(x / y)\<degree>\<^sup>p = (x\<degree>\<^sup>p)"
    using Abs_adelic_int_Abs_adelic_int divide_adelic_int_abs_eq
          p_adic_prod_div_inv.global_depth_set_divide[of _ 0] p_depth_adelic_int_abs_eq[of _ p]
          p_adic_prod_div_inv.divide_depth[of p a b]
          global_p_depth_p_adic_prod.depth_equiv[of p _ "a / b"]
          global_p_depth_p_adic_prod.p_restrict_equiv[of _ p "a / b"]
    by    fastforce
qed

lemma global_unfrmzr_pows_adelic_int_inverse:
  "inverse (\<pp> f :: 'a adelic_int) = 1 prestrict (\<lambda>p::'a prime. f p = 0)"
  for f :: "'a::nontrivial_factorial_unique_euclidean_bezout prime \<Rightarrow> nat"
proof (intro global_p_depth_adelic_int.global_imp_eq, standard)
  fix p :: "'a prime"
  define P :: "'a prime \<Rightarrow> bool" where "P \<equiv> (\<lambda>p. f p = 0)"
  define  \<pp>nif :: "'a p_adic_prod" and \<pp>f   :: "'a adelic_int"
    where "\<pp>nif \<equiv> \<pp> (- (int \<circ> f))" and "\<pp>f   \<equiv> \<pp> f"
  from P_def \<pp>nif_def \<pp>f_def have "inverse \<pp>f = Abs_adelic_int (\<pp>nif prestrict P)"
    using     global_unfrmzr_pows_p_adic_prod_global_depth_set_0[of f]
              inverse_adelic_int_abs_eq[of "\<pp> (int \<circ> f)"]
              global_unfrmzr_pows_p_adic_prod[of _ "int \<circ> f"]
              global_unfrmzr_pows_p_adic_prod_inverse[of "int \<circ> f"]
    unfolding global_unfrmzr_pows_adelic_int_def
    by        fastforce
  moreover from P_def \<pp>nif_def have "\<pp>nif prestrict P \<simeq>\<^sub>p 1 prestrict P"
    using global_p_depth_p_adic_prod.p_restrict_p_equal_p_restrict_by_sameI[of P p]
          trivial_global_unfrmzr_pows_p_adic_prod[of _ p]
    by    force
  moreover have "\<pp>nif prestrict P \<in> \<O>\<^sub>\<forall>\<^sub>p"
  proof (intro p_adic_prod_global_depth_set_p_restrictI)
    fix p :: "'a prime" assume "P p"
    moreover from \<pp>nif_def have "\<pp>nif \<in> p_depth_set p (- (int \<circ> f) p)"
      using global_unfrmzr_pows_p_adic_prod_depth_set[of "- (int \<circ> f)"] by simp
    ultimately show "\<pp>nif \<in> \<O>\<^sub>@\<^sub>p" using P_def by fastforce
  qed
  ultimately show "(inverse \<pp>f) \<simeq>\<^sub>p (1 prestrict P)"
    using one_adelic_int_def global_p_depth_p_adic_prod.global_depth_set_1
          p_equal_adelic_int_abs_eq p_restrict_adelic_int_abs_eq global_depth_set_p_adic_prod_def
          global_p_depth_p_adic_prod.global_depth_set_p_restrict
    by    metis
qed

lemma adelic_int_diff_cancel_lead_coeff:
  "((inverse x - inverse y)\<degree>\<^sup>p) > 0"
  if  x : "x \<not>\<simeq>\<^sub>p 0" "x\<degree>\<^sup>p = 0"
  and y : "y \<not>\<simeq>\<^sub>p 0" "y\<degree>\<^sup>p = 0"
  and xy: "x \<not>\<simeq>\<^sub>p y" "((x - y)\<degree>\<^sup>p) > 0"
  for p :: "'a::nontrivial_factorial_unique_euclidean_bezout prime"
  and x y :: "'a adelic_int"
proof (cases x y rule: two_Abs_adelic_int_cases)
  define P :: "'a p_adic_prod \<Rightarrow> 'a prime \<Rightarrow> bool"
    where "P \<equiv> \<lambda>a p. a\<degree>\<^sup>p = 0"
  case (Abs_adelic_int_Abs_adelic_int a b)
  moreover from this x(1) y(1) xy(1)
    have  "a \<not>\<simeq>\<^sub>p 0"
    and   "b \<not>\<simeq>\<^sub>p 0"
    and   "a \<not>\<simeq>\<^sub>p b"
    using p_equal_adelic_int_abs_eq0 p_equal_adelic_int_abs_eq
    by    (fast, fast, fast)
  moreover from Abs_adelic_int_Abs_adelic_int x(2) y(2) xy(2)
    have  "a\<degree>\<^sup>p = 0"
    and   "b\<degree>\<^sup>p = 0"
    and   "((a - b)\<degree>\<^sup>p) > 0"
    by (
      metis p_depth_adelic_int_abs_eq, metis p_depth_adelic_int_abs_eq,
      metis p_depth_adelic_int_diff_abs_eq
    )
  ultimately show ?thesis
    using p_depth_adelic_int_inverse_diff_abs_eq p_adic_prod_diff_cancel_lead_coeff by fastforce
qed


subsubsection \<open>The ideal of primes\<close>

overloading
  p_depth_set_adelic_int \<equiv>
    "p_depth_set ::
      'a::nontrivial_factorial_idom prime \<Rightarrow> int \<Rightarrow> 'a adelic_int set"
  global_depth_set_adelic_int \<equiv>
    "global_depth_set :: int \<Rightarrow> 'a adelic_int set"
begin

definition p_depth_set_adelic_int ::
  "'a::nontrivial_factorial_idom prime \<Rightarrow> int \<Rightarrow> 'a adelic_int set"
  where p_depth_set_adelic_int_def[simp]:
    "p_depth_set_adelic_int = global_p_depth_adelic_int.p_depth_set"

definition global_depth_set_adelic_int ::
  "int \<Rightarrow> 'a::nontrivial_factorial_idom adelic_int set"
  where global_depth_set_adelic_int_def[simp]:
    "global_depth_set_adelic_int = global_p_depth_adelic_int.global_depth_set"

end

context
  fixes x :: "'a::nontrivial_factorial_idom adelic_int"
begin

lemma adelic_int_global_depth_setI:
  "x \<in> \<P>\<^sub>\<forall>\<^sub>p\<^sup>n"
  if  "\<And>p::'a prime. x \<not>\<simeq>\<^sub>p 0 \<Longrightarrow> (x\<degree>\<^sup>p) \<ge> n"
  using that global_p_depth_adelic_int.global_depth_setI by auto

lemma adelic_int_global_depth_setI':
  "x \<in> \<P>\<^sub>\<forall>\<^sub>p\<^sup>n"
  if  "\<And>p::'a prime. (x\<degree>\<^sup>p) \<ge> n"
  using that global_p_depth_adelic_int.global_depth_setI' by auto

lemma adelic_int_global_depth_set_p_restrictI:
  "p_restrict x P \<in> \<P>\<^sub>\<forall>\<^sub>p\<^sup>n"
  if "\<And>p::'a prime. P p \<Longrightarrow> x \<in> \<P>\<^sub>@\<^sub>p\<^sup>n"
  using that global_p_depth_adelic_int.global_depth_set_p_restrictI by auto

end (* context nontrivial_factorial_idom *)

context
  fixes p :: "'a::nontrivial_factorial_idom prime"
begin

lemma adelic_int_p_depth_setI:
  "x \<in> \<P>\<^sub>@\<^sub>p\<^sup>n"
  if "x \<not>\<simeq>\<^sub>p 0 \<longrightarrow> (x\<degree>\<^sup>p) \<ge> n"
  for x :: "'a adelic_int"
  using that global_p_depth_adelic_int.p_depth_setI by auto

lemma nonpos_p_depth_set_adelic_int:
  "(\<P>\<^sub>@\<^sub>p\<^sup>n) = (UNIV :: 'a::nontrivial_factorial_idom adelic_int set)"
  if "n \<le> 0"
proof safe
  fix x :: "'a adelic_int" show "x \<in> (\<P>\<^sub>@\<^sub>p\<^sup>n)"
  proof (intro adelic_int_p_depth_setI, clarify)
    from that show "n \<le> (x\<degree>\<^sup>p)"
      using adelic_int_depth[of p x] by fastforce
  qed
qed simp

lemma p_depth_set_adelic_int_eq_projection:
  "((\<P>\<^sub>@\<^sub>p\<^sup>n) :: 'a::nontrivial_factorial_idom adelic_int set) =
    Abs_adelic_int ` ((\<P>\<^sub>@\<^sub>p\<^sup>n) \<inter> \<O>\<^sub>\<forall>\<^sub>p)"
proof safe
  fix x :: "'a adelic_int" assume "x \<in> \<P>\<^sub>@\<^sub>p\<^sup>n"
  thus
    "x \<in>
      Abs_adelic_int ` ((\<P>\<^sub>@\<^sub>p\<^sup>n) \<inter> \<O>\<^sub>\<forall>\<^sub>p)"
    using p_equal_adelic_int_abs_eq0 global_p_depth_adelic_int.p_depth_setD
          p_depth_adelic_int_abs_eq p_adic_prod_p_depth_setI
    by    (cases x) fastforce
next
  fix a :: "'a p_adic_prod"
  assume "a \<in> \<P>\<^sub>@\<^sub>p\<^sup>n" "a \<in> \<O>\<^sub>\<forall>\<^sub>p"
  thus "Abs_adelic_int a \<in> \<P>\<^sub>@\<^sub>p\<^sup>n"
    using p_equal_adelic_int_abs_eq0 global_p_depth_p_adic_prod.p_depth_setD
          p_depth_adelic_int_abs_eq
    by    (fastforce intro: adelic_int_p_depth_setI)
qed

lemma lift_p_depth_set_adelic_int:
  "Rep_adelic_int `
    ((\<P>\<^sub>@\<^sub>p\<^sup>n) :: 'a::nontrivial_factorial_idom adelic_int set)
    = (\<P>\<^sub>@\<^sub>p\<^sup>n) \<inter> \<O>\<^sub>\<forall>\<^sub>p"
proof-
  have
    "Rep_adelic_int ` Abs_adelic_int `
      ((\<P>\<^sub>@\<^sub>p\<^sup>n) \<inter> \<O>\<^sub>\<forall>\<^sub>p)
      = (\<P>\<^sub>@\<^sub>p\<^sup>n) \<inter> \<O>\<^sub>\<forall>\<^sub>p"
    using Abs_adelic_int_inverse by force
  thus ?thesis using p_depth_set_adelic_int_eq_projection by metis
qed

end (* context nontrivial_factorial_idom *)

lemma nonpos_global_depth_set_adelic_int:
  "(\<P>\<^sub>\<forall>\<^sub>p\<^sup>n) = (UNIV :: 'a::nontrivial_factorial_idom adelic_int set)"
  if "n \<le> 0"
  using that nonpos_p_depth_set_adelic_int global_p_depth_adelic_int.global_depth_set by fastforce

lemma nonneg_global_depth_set_adelic_int_eq_projection:
  "((\<P>\<^sub>\<forall>\<^sub>p\<^sup>n)  :: 'a::nontrivial_factorial_idom adelic_int set) =
    Abs_adelic_int ` \<P>\<^sub>\<forall>\<^sub>p\<^sup>n"
  if n: "n \<ge> 0"
proof safe
  fix x :: "'a adelic_int" assume x: "x \<in> \<P>\<^sub>\<forall>\<^sub>p\<^sup>n"
  show "x \<in> Abs_adelic_int ` \<P>\<^sub>\<forall>\<^sub>p\<^sup>n"
  proof (cases x)
    case (Abs_adelic_int a)
    moreover from this x have "a \<in> \<P>\<^sub>\<forall>\<^sub>p\<^sup>n"
      using p_equal_adelic_int_abs_eq0 global_p_depth_adelic_int.global_depth_setD
            p_depth_adelic_int_abs_eq
      by    (fastforce intro: p_adic_prod_global_depth_setI)
    ultimately show ?thesis by fast
  qed
next
  fix a :: "'a p_adic_prod" assume "a \<in> \<P>\<^sub>\<forall>\<^sub>p\<^sup>n"
  moreover from this n have "a \<in> \<O>\<^sub>\<forall>\<^sub>p"
    using global_p_depth_p_adic_prod.global_depth_set_antimono by auto
  ultimately show "Abs_adelic_int a \<in> \<P>\<^sub>\<forall>\<^sub>p\<^sup>n"
    using n p_equal_adelic_int_abs_eq0 global_p_depth_p_adic_prod.global_depth_setD
          p_depth_adelic_int_abs_eq
    by    (fastforce intro: adelic_int_global_depth_setI)
qed

lemma lift_nonneg_global_depth_set_adelic_int:
  "Rep_adelic_int `
    ((\<P>\<^sub>\<forall>\<^sub>p\<^sup>n)  :: 'a::nontrivial_factorial_idom adelic_int set)
    = \<P>\<^sub>\<forall>\<^sub>p\<^sup>n"
  if n: "n \<ge> 0"
proof-
  from n have
    "Rep_adelic_int ` Abs_adelic_int `
      (\<P>\<^sub>\<forall>\<^sub>p\<^sup>n)
      = \<P>\<^sub>\<forall>\<^sub>p\<^sup>n"
    using global_p_depth_p_adic_prod.global_depth_set_antimono Abs_adelic_int_inverse by force
  with n show ?thesis using nonneg_global_depth_set_adelic_int_eq_projection by metis
qed

subsubsection \<open>Topology p-open neighbourhoods\<close>

text \<open>General properties of p-open sets\<close>

abbreviation "adelic_int_p_open_nbhd         \<equiv> global_p_depth_adelic_int.p_open_nbhd"
abbreviation "adelic_int_p_open_nbhds        \<equiv> global_p_depth_adelic_int.p_open_nbhds"
abbreviation "adelic_int_local_p_open_nbhds  \<equiv> global_p_depth_adelic_int.local_p_open_nbhds"

lemma adelic_int_nonpos_p_open_nbhd:
  "adelic_int_p_open_nbhd p n x = UNIV" if "n \<le> 0"
  for p :: "'a::nontrivial_factorial_idom prime"
proof-
  from that have "adelic_int_p_open_nbhd p n x = adelic_int_p_open_nbhd p n 0"
    using global_p_depth_adelic_int.p_open_nbhd_eq_circle[of 0 p n]
          adelic_int_depth[of p x]
          global_p_depth_adelic_int.p_open_nbhd_circle_multicentre[of x 0 p n]
    by    simp
  moreover have "adelic_int_p_open_nbhd p n 0 = UNIV"
  proof safe
    fix y :: "'a adelic_int" from that show "y \<in> adelic_int_p_open_nbhd p n 0"
      using global_p_depth_adelic_int.p_open_nbhd_eq_circle[of 0 p n] adelic_int_depth[of p y]
      by    auto
  qed simp
  ultimately show ?thesis by presburger
qed

lemma adelic_int_p_open_nbhd_bound:
  "adelic_int_p_open_nbhd p n x = adelic_int_p_open_nbhd p (int (nat n)) x"
  using adelic_int_nonpos_p_open_nbhd[of n x p] adelic_int_nonpos_p_open_nbhd[of 0 x p] by simp

lemma adelic_int_p_open_nbhd_abs_eq:
  "adelic_int_p_open_nbhd p n (Abs_adelic_int x) =
    Abs_adelic_int ` (p_adic_prod_p_open_nbhd p n x \<inter> \<O>\<^sub>\<forall>\<^sub>p)"
  if "x \<in> \<O>\<^sub>\<forall>\<^sub>p"
  for p :: "'a::nontrivial_factorial_idom prime"
proof safe
  fix y assume y: "y \<in> adelic_int_p_open_nbhd p n (Abs_adelic_int x)"
  show
    "y \<in> Abs_adelic_int ` (p_adic_prod_p_open_nbhd p n x \<inter> \<O>\<^sub>\<forall>\<^sub>p)"
  proof (cases y)
    case (Abs_adelic_int z)
    with that y have "z \<in> p_adic_prod_p_open_nbhd p n x"
      using global_p_depth_adelic_int.p_open_nbhd_eq_circle p_equal_adelic_int_abs_eq[of z x p]
            p_depth_adelic_int_diff_abs_eq[of z x p]
            global_p_depth_p_adic_prod.p_open_nbhd_eq_circle
      by    fastforce
    with Abs_adelic_int show ?thesis by blast
  qed
next
  fix z assume z: "z \<in> p_adic_prod_p_open_nbhd p n x" "z \<in> \<O>\<^sub>\<forall>\<^sub>p"
  with that show "Abs_adelic_int z \<in> adelic_int_p_open_nbhd p n (Abs_adelic_int x)"
    using global_p_depth_adelic_int.p_open_nbhd_eq_circle p_equal_adelic_int_abs_eq[of z x p]
          p_depth_adelic_int_diff_abs_eq[of z x p] global_p_depth_p_adic_prod.p_open_nbhd_eq_circle
    by    fastforce
qed

lemma adelic_int_p_open_nbhd_rep_eq:
  "Rep_adelic_int ` adelic_int_p_open_nbhd p n x =
    p_adic_prod_p_open_nbhd p n (Rep_adelic_int x) \<inter> \<O>\<^sub>\<forall>\<^sub>p"
  for p :: "'a::nontrivial_factorial_idom prime"
proof (cases x)
  case (Abs_adelic_int z)
  hence
    "Rep_adelic_int ` adelic_int_p_open_nbhd p n x =
      Rep_adelic_int ` Abs_adelic_int `
        (p_adic_prod_p_open_nbhd p n z \<inter> \<O>\<^sub>\<forall>\<^sub>p)"
    using adelic_int_p_open_nbhd_abs_eq by metis
  also have "\<dots> = p_adic_prod_p_open_nbhd p n z \<inter> \<O>\<^sub>\<forall>\<^sub>p"
    using Abs_adelic_int_inverse by force
  finally show ?thesis using Abs_adelic_int Abs_adelic_int_inverse by force
qed

lemma adelic_int_local_depth_ring_lift_cover:
  fixes n :: int
  and   p :: "'a::nontrivial_factorial_unique_euclidean_bezout prime"
  and   \<A> :: "'a adelic_int set set"
  defines
    "(\<A>' :: 'a p_adic_prod set set) \<equiv>
      (\<lambda>A.
        (\<lambda>x. x prestrict ((=) p)) ` Rep_adelic_int ` A +
        range (\<lambda>x. x prestrict ((\<noteq>) p))
      ) ` \<A>"
  assumes nonneg: "n \<ge> 0"
    and   cover:
    "(\<lambda>x. x prestrict ((=) p)) ` (\<P>\<^sub>\<forall>\<^sub>p\<^sup>n) \<subseteq>
      \<Union> \<A>"
  shows
    "(\<lambda>x. x prestrict ((=) p)) ` (\<P>\<^sub>\<forall>\<^sub>p\<^sup>n) \<subseteq>
      \<Union> \<A>'"
proof clarify
  fix x :: "'a p_adic_prod"
  assume x: "x \<in> (\<P>\<^sub>\<forall>\<^sub>p\<^sup>n)"
  with nonneg have x_O: "x \<in> \<O>\<^sub>\<forall>\<^sub>p"
    using global_p_depth_p_adic_prod.global_depth_set_antimono by auto
  from x nonneg have res_x_P: "x prestrict ((=) p) \<in> (\<P>\<^sub>\<forall>\<^sub>p\<^sup>n)"
    using global_p_depth_p_adic_prod.global_depth_set_closed_under_p_restrict_image
    by    fastforce
  with nonneg have res_x_O: "x prestrict ((=) p) \<in> \<O>\<^sub>\<forall>\<^sub>p"
    using global_p_depth_p_adic_prod.global_depth_set_antimono by auto
  from nonneg
    have  "Abs_adelic_int (x prestrict ((=) p)) \<in> (\<P>\<^sub>\<forall>\<^sub>p\<^sup>n)"
    using res_x_P nonneg_global_depth_set_adelic_int_eq_projection
    by    fast
  moreover have
    "Abs_adelic_int (x prestrict ((=) p)) =
      (Abs_adelic_int (x prestrict ((=) p))) prestrict ((=) p)"
    using res_x_O p_restrict_adelic_int_abs_eq by fastforce
  ultimately obtain A where A: "A \<in> \<A>" "Abs_adelic_int (x prestrict ((=) p)) \<in> A"
    using cover by blast
  from A(2) have "x prestrict ((=) p) \<in> Rep_adelic_int ` A"
    using res_x_O Abs_adelic_int_inverse by force
  moreover have "x prestrict ((=) p) = (x prestrict ((=) p)) prestrict ((=) p)"
    using global_p_depth_p_adic_prod.p_restrict_restrict' by simp
  moreover have restr_0: "(0 :: 'a p_adic_prod) = 0 prestrict ((\<noteq>) p)"
    using global_p_depth_p_adic_prod.p_restrict_zero by metis
  ultimately have
    "x prestrict ((=) p) + 0 prestrict ((\<noteq>) p) \<in>
      (\<lambda>x. x prestrict ((=) p)) ` Rep_adelic_int ` A +
      range (\<lambda>x. x prestrict ((\<noteq>) p))"
    by fast
  with A(1) \<A>'_def show "x prestrict ((=) p) \<in> \<Union> \<A>'" using restr_0 by auto
qed

lemma adelic_int_lift_local_p_open:
  fixes p :: "'a::nontrivial_factorial_unique_euclidean_bezout prime"
  and   A :: "'a adelic_int set"
  defines
    "A' \<equiv>
      (\<lambda>x. x prestrict ((=) p)) ` Rep_adelic_int ` A +
      range (\<lambda>x. x prestrict ((\<noteq>) p))"
  assumes adelic_int_p_open: "generate_topology (adelic_int_local_p_open_nbhds p) A"
  shows "generate_topology (p_adic_prod_local_p_open_nbhds p) A'"
    unfolding A'_def set_plus_def
proof (rule iffD2, rule global_p_depth_p_adic_prod.p_open_nbhds_open_subopen, clarify)
  define f f' :: "'a p_adic_prod \<Rightarrow> 'a p_adic_prod"
    where "f  \<equiv> \<lambda>x. x prestrict ((=) p)"
    and   "f' \<equiv> \<lambda>x. x prestrict ((\<noteq>) p)"
  fix a b assume a: "a \<in> A"
  with adelic_int_p_open obtain n where n: "adelic_int_p_open_nbhd p (int (nat n)) a \<subseteq> A"
    using global_p_depth_adelic_int.p_open_nbhds_open_subopen[of p A]
          adelic_int_p_open_nbhd_bound[of a p]
    by    presburger
  hence *:
    "p_adic_prod_p_open_nbhd p (int (nat n)) (Rep_adelic_int a)
      \<inter> \<O>\<^sub>\<forall>\<^sub>p
      \<subseteq> Rep_adelic_int ` A"
    using adelic_int_p_open_nbhd_rep_eq by blast
  have
    "p_adic_prod_p_open_nbhd p (int (nat n)) (f (Rep_adelic_int a) + f' b) \<subseteq>
      f ` Rep_adelic_int ` A + range f'"
  proof
    fix y
    assume "y \<in> p_adic_prod_p_open_nbhd p (int (nat n)) (f (Rep_adelic_int a) + f' b)"
    with f_def f'_def have y: "y \<in> p_adic_prod_p_open_nbhd p (int (nat n)) (Rep_adelic_int a)"
      by (simp add: global_p_depth_p_adic_prod.p_open_nbhd_p_restrict_add_mixed_drop_right)
    have f_y: "f y \<in> \<O>\<^sub>\<forall>\<^sub>p"
      unfolding f_def global_depth_set_p_adic_prod_def
    proof (
      intro global_p_depth_p_adic_prod.global_depth_set_p_restrictI
            global_p_depth_p_adic_prod.p_depth_setI,
      clarify
    )
      assume y_n0: "y \<not>\<simeq>\<^sub>p 0"
      show "(y\<degree>\<^sup>p) \<ge> 0"
      proof (cases "y \<simeq>\<^sub>p (Rep_adelic_int a)")
        case True thus ?thesis
          using global_p_depth_p_adic_prod.depth_equiv p_depth_adelic_int_def adelic_int_depth
          by    metis
      next
        case y_a_nequiv: False
        hence y_a_depth: "((y - Rep_adelic_int a)\<degree>\<^sup>p) \<ge> int (nat n)"
          using y global_p_depth_p_adic_prod.p_open_nbhd_eq_circle by blast
        show ?thesis
        proof (cases "Rep_adelic_int a \<simeq>\<^sub>p 0")
          case True thus ?thesis
            using y_a_depth
                  global_p_depth_p_adic_prod.depth_diff_equiv0_right[of p "Rep_adelic_int a" y]
            by    linarith
        next
          case False
          from y_n0 have
            "(y\<degree>\<^sup>p) < ((Rep_adelic_int a)\<degree>\<^sup>p) \<Longrightarrow> ?thesis"
            using y_a_depth
                  global_p_depth_p_adic_prod.depth_pre_nonarch_diff_left[
                    of p y "Rep_adelic_int a"
                  ]
            by    linarith
          moreover from False have
            "(y\<degree>\<^sup>p) \<ge> ((Rep_adelic_int a)\<degree>\<^sup>p) \<Longrightarrow>
              ?thesis"
            using global_p_depth_p_adic_prod.depth_pre_nonarch_diff_right[
                    of p "Rep_adelic_int a" y
                  ]
                  p_depth_adelic_int_def[of p a] adelic_int_depth[of p a]
            by    simp
          ultimately show ?thesis by fastforce
        qed
      qed
    qed
    with y f_def have "f y \<in> Rep_adelic_int ` A"
      using * global_p_depth_p_adic_prod.p_open_nbhd_circle_multicentre'[of y]
            global_p_depth_p_adic_prod.p_open_nbhd_circle_multicentre'[of "f y"]
            global_p_depth_p_adic_prod.p_open_nbhd_p_restrict
      by    fast
    moreover from f_def f'_def have "y = f (f y) + f' y"
      using global_p_depth_p_adic_prod.p_restrict_restrict'
            global_p_depth_p_adic_prod.p_restrict_decomp
      by    auto
    ultimately show "y \<in> f ` Rep_adelic_int ` A + range f'"
      using set_plus_def by fast
  qed
  thus
    "\<exists>n. p_adic_prod_p_open_nbhd p n (f (Rep_adelic_int a) + f' b)
      \<subseteq> {c. \<exists>a\<in>f ` Rep_adelic_int ` A. \<exists>b\<in>range f'. c = a + b}"
    using set_plus_def by blast
qed


text \<open>Sequences\<close>

abbreviation
  "adelic_int_p_limseq_condition \<equiv> global_p_depth_adelic_int.p_limseq_condition"
abbreviation
  "adelic_int_p_cauchy_condition \<equiv> global_p_depth_adelic_int.p_cauchy_condition"
abbreviation "adelic_int_p_limseq            \<equiv> global_p_depth_adelic_int.p_limseq"
abbreviation "adelic_int_p_cauchy            \<equiv> global_p_depth_adelic_int.p_cauchy"
abbreviation "adelic_int_p_open_nbhds_limseq \<equiv> global_p_depth_adelic_int.p_open_nbhds_LIMSEQ"

context
  fixes p :: "'a::nontrivial_factorial_idom prime"
    and X :: "nat \<Rightarrow> 'a p_adic_prod"
    and Y :: "nat \<Rightarrow> 'a adelic_int"
  defines "Y \<equiv> \<lambda>n. Abs_adelic_int (X n)"
  assumes range_X: "range X \<subseteq> \<O>\<^sub>\<forall>\<^sub>p"
begin

lemma adelic_int_p_limseq_condition_abs_eq:
  "adelic_int_p_limseq_condition p Y (Abs_adelic_int x) =
    p_adic_prod_p_limseq_condition p X x"
  if "x \<in> \<O>\<^sub>\<forall>\<^sub>p"
proof (standard, standard)
  fix n :: int and N :: nat
  from range_X have "\<forall>n. X n \<in> \<O>\<^sub>\<forall>\<^sub>p" by blast
  with that Y_def have
    "adelic_int_p_limseq_condition p Y (Abs_adelic_int x) n N =
      (\<forall>k\<ge>N. (X k) \<not>\<simeq>\<^sub>p x \<longrightarrow>
        ((X k - x)\<degree>\<^sup>p) > n)"
    using global_p_depth_adelic_int.p_limseq_condition_def p_equal_adelic_int_abs_eq
          p_depth_adelic_int_diff_abs_eq
    by    metis
  thus
    "adelic_int_p_limseq_condition p Y (Abs_adelic_int x) n N =
      p_adic_prod_p_limseq_condition p X x n N"
    using global_p_depth_p_adic_prod.p_limseq_condition_def by blast
qed

lemma adelic_int_p_limseq_abs_eq:
  "adelic_int_p_limseq p Y (Abs_adelic_int x) = p_adic_prod_p_limseq p X x"
  if "x \<in> \<O>\<^sub>\<forall>\<^sub>p"
  using that adelic_int_p_limseq_condition_abs_eq by auto

lemma adelic_int_p_cauchy_condition_abs_eq:
  "adelic_int_p_cauchy_condition p Y = p_adic_prod_p_cauchy_condition p X"
proof (standard, standard)
  fix n :: int and K :: nat
  from range_X have "\<forall>n. X n \<in> \<O>\<^sub>\<forall>\<^sub>p" by blast
  moreover from this Y_def
    have  "\<forall>n n'. ((Y n - Y n')\<degree>\<^sup>p) = ((X n - X n')\<degree>\<^sup>p)"
    using p_equal_adelic_int_abs_eq p_depth_adelic_int_diff_abs_eq
    by    blast
  ultimately have
    "adelic_int_p_cauchy_condition p Y n K =
      (\<forall>k1\<ge>K. \<forall>k2\<ge>K.
        (X k1) \<not>\<simeq>\<^sub>p (X k2) \<longrightarrow>
          ((X k1 - X k2)\<degree>\<^sup>p) > n)"
    using Y_def global_p_depth_adelic_int.p_cauchy_condition_def p_equal_adelic_int_abs_eq by metis
  thus "adelic_int_p_cauchy_condition p Y n K = p_adic_prod_p_cauchy_condition p X n K"
    using global_p_depth_p_adic_prod.p_cauchy_condition_def by blast
qed

lemma adelic_int_p_cauchy_abs_eq: "adelic_int_p_cauchy p Y = p_adic_prod_p_cauchy p X"
  using adelic_int_p_cauchy_condition_abs_eq by simp

end (* context p_adic_prod int ring seq *)

lemma adelic_int_p_open_nbhds_limseq_abs_eq:
  "adelic_int_p_open_nbhds_limseq (\<lambda>n. Abs_adelic_int (X n)) (Abs_adelic_int x) =
    p_adic_prod_p_open_nbhds_limseq X x"
  if "range X \<subseteq> \<O>\<^sub>\<forall>\<^sub>p" and "x \<in> \<O>\<^sub>\<forall>\<^sub>p"
  using that adelic_int_p_limseq_abs_eq
        global_p_depth_p_adic_prod.globally_limseq_iff_locally_limseq[of X x]
        global_p_depth_adelic_int.globally_limseq_iff_locally_limseq[of
          "\<lambda>n. Abs_adelic_int (X n)" "Abs_adelic_int x"
        ]
  by    blast

subsubsection \<open>Topology via global depth\<close>

text \<open>The metric\<close>
instantiation adelic_int :: (nontrivial_factorial_idom) metric_space
begin

definition "dist = global_p_depth_adelic_int.bdd_global_dist"
declare dist_adelic_int_def [simp]

definition "uniformity = global_p_depth_adelic_int.bdd_global_uniformity"
declare uniformity_adelic_int_def [simp]

definition open_adelic_int :: "'a adelic_int set \<Rightarrow> bool"
  where
    "open_adelic_int U =
      (\<forall>x\<in>U.
        eventually (\<lambda>(x', y). x' = x \<longrightarrow> y \<in> U) uniformity
      )"

instance
  by (
    standard,
    simp_all add: global_p_depth_adelic_int.bdd_global_uniformity_def open_adelic_int_def
                  global_p_depth_adelic_int.metric_space_by_bdd_depth.dist_triangle2
  )

end (* instantiation adelic_int metric_space *)

abbreviation "adelic_int_global_depth  \<equiv> global_p_depth_adelic_int.bdd_global_depth"

lemma adelic_int_bdd_global_depth_abs_eq:
  "adelic_int_global_depth (Abs_adelic_int x) = p_adic_prod_global_depth x"
  if "x \<in> \<O>\<^sub>\<forall>\<^sub>p" for x :: "'a::nontrivial_factorial_idom p_adic_prod"
proof (cases "x = 0")
  case True thus ?thesis
    using     global_p_depth_adelic_int.bdd_global_depth_0
              global_p_depth_p_adic_prod.bdd_global_depth_0
    unfolding zero_adelic_int_def
    by        force
next
  case False
  moreover from this that have "Abs_adelic_int x \<noteq> 0"
    using     Abs_adelic_int_inject global_p_depth_p_adic_prod.global_depth_set_0
    unfolding zero_adelic_int_def
    by        auto
  ultimately show ?thesis
    using that Abs_adelic_int_inject global_p_depth_adelic_int.bdd_global_depthD
          p_equal_adelic_int_abs_eq0 p_depth_adelic_int_abs_eq
          global_p_depth_p_adic_prod.bdd_global_depthD
          global_p_depth_adelic_int.global_eq_iff
    by    fastforce
qed

lemma dist_adelic_int_abs_eq:
  "dist (Abs_adelic_int x) (Abs_adelic_int y) = dist x y"
  if "x \<in> \<O>\<^sub>\<forall>\<^sub>p" and "y \<in> \<O>\<^sub>\<forall>\<^sub>p"
  for x y :: "'a::nontrivial_factorial_idom p_adic_prod"
proof (cases "x = y")
  case True with that show ?thesis
    using Abs_adelic_int_inject global_p_depth_adelic_int.bdd_global_dist_eqD
          global_p_depth_p_adic_prod.bdd_global_dist_eqD
    by    auto
next
  case False with that show ?thesis
    using dist_adelic_int_def Abs_adelic_int_inject global_p_depth_adelic_int.bdd_global_distD
          minus_adelic_int_abs_eq global_p_depth_p_adic_prod.global_depth_set_minus
          adelic_int_bdd_global_depth_abs_eq global_depth_set_p_adic_prod_def
          global_p_depth_p_adic_prod.bdd_global_distD dist_p_adic_prod_def
          global_p_depth_p_adic_prod.global_eq_iff global_p_depth_adelic_int.global_eq_iff
    by    metis
qed

lemma adelic_int_limseq_abs_eq:
  "(\<lambda>n. Abs_adelic_int (X n)) \<longlonglongrightarrow> Abs_adelic_int x
    \<longleftrightarrow> X \<longlonglongrightarrow> x"
  if "range X \<subseteq> \<O>\<^sub>\<forall>\<^sub>p" and "x \<in> \<O>\<^sub>\<forall>\<^sub>p"
proof-
  from that have "\<forall>n. dist (Abs_adelic_int (X n)) (Abs_adelic_int x) = dist (X n) x"
    using dist_adelic_int_abs_eq[of "X _" x] by blast
  thus ?thesis
    using tendsto_iff[of "\<lambda>n. Abs_adelic_int (X n)" "Abs_adelic_int x"] tendsto_iff[of X x]
    by    presburger
qed

lemma adelic_int_bdd_metric_LIMSEQ:
  "X \<longlonglongrightarrow> x = global_p_depth_adelic_int.metric_space_by_bdd_depth.LIMSEQ X x"
  for X :: "nat \<Rightarrow> 'a::nontrivial_factorial_idom adelic_int" and x :: "'a adelic_int"
  unfolding tendsto_iff global_p_depth_adelic_int.metric_space_by_bdd_depth.tendsto_iff
            dist_adelic_int_def
  by        fast

lemma adelic_int_global_depth_set_lim_closed:
  "x \<in> \<P>\<^sub>\<forall>\<^sub>p\<^sup>n"
  if  lim  : "X \<longlonglongrightarrow> x"
  and depth: "\<forall>\<^sub>F k in sequentially. X k \<in> \<P>\<^sub>\<forall>\<^sub>p\<^sup>n"
  for X :: "nat \<Rightarrow> 'a::nontrivial_factorial_unique_euclidean_bezout adelic_int"
  and x :: "'a adelic_int"
proof (
  cases "n \<le> 0", use nonpos_global_depth_set_adelic_int in blast,
  cases X x rule: adelic_int_seq_cases[case_product Abs_adelic_int_cases]
)
  case False case (Abs_adelic_int_Abs_adelic_int F a)
  with lim have "F \<longlonglongrightarrow> a" using adelic_int_limseq_abs_eq by blast
  moreover have
    "\<forall>\<^sub>F k in sequentially. F k \<in> \<P>\<^sub>\<forall>\<^sub>p\<^sup>n"
  proof-
    from depth obtain K where K: "\<forall>k\<ge>K. X k \<in> \<P>\<^sub>\<forall>\<^sub>p\<^sup>n"
      using eventually_sequentially by auto
    have "\<forall>k\<ge>K. F k \<in> \<P>\<^sub>\<forall>\<^sub>p\<^sup>n"
    proof clarify
      fix k assume "k \<ge> K"
      with False Abs_adelic_int_Abs_adelic_int(1) K obtain z
        where "z \<in> \<P>\<^sub>\<forall>\<^sub>p\<^sup>n"
        and   "Abs_adelic_int (F k) = Abs_adelic_int z"
        using nonneg_global_depth_set_adelic_int_eq_projection[of n]
        by    auto
      with False Abs_adelic_int_Abs_adelic_int(2)
        show  "F k \<in> \<P>\<^sub>\<forall>\<^sub>p\<^sup>n"
        using Abs_adelic_int_inject[of "F k" z]
              global_p_depth_p_adic_prod.global_depth_set_antimono[of 0 n]
        by    auto
    qed
    thus ?thesis using eventually_sequentially by blast
  qed
  ultimately have "a \<in> \<P>\<^sub>\<forall>\<^sub>p\<^sup>n"
    using p_adic_prod_global_depth_set_lim_closed by auto
  with False Abs_adelic_int_Abs_adelic_int(3) show ?thesis
    using nonneg_global_depth_set_adelic_int_eq_projection[of n] by auto
qed

lemma adelic_int_metric_ball_multicentre:
  "ball y e = ball x e" if "y \<in> ball x e" for x y :: "'a::nontrivial_factorial_idom adelic_int"
  using     that global_p_depth_adelic_int.bdd_global_dist_ball_multicentre
  unfolding ball_def dist_adelic_int_def
  by        blast

lemma adelic_int_metric_ball_at_0:
  "ball (0::'a::nontrivial_factorial_idom adelic_int) (inverse (2 ^ n)) = global_depth_set (int n)"
  using     global_p_depth_adelic_int.bdd_global_dist_ball_at_0
  unfolding ball_def dist_adelic_int_def global_depth_set_adelic_int_def
  by        auto

lemma adelic_int_metric_ball_at_0_normalize:
  "ball (0::'a::nontrivial_factorial_idom adelic_int) e =
    global_depth_set \<lfloor>log 2 (inverse e)\<rfloor>"
  if "e > 0" and "e \<le> 1"
  using     that global_p_depth_adelic_int.bdd_global_dist_ball_at_0_normalize
  unfolding ball_def dist_adelic_int_def global_depth_set_adelic_int_def
  by        blast

lemma adelic_int_metric_ball_translate:
  "ball x e = x +o ball 0 e" for x :: "'a::nontrivial_factorial_idom adelic_int"
  using     global_p_depth_adelic_int.bdd_global_dist_ball_translate
  unfolding ball_def dist_adelic_int_def
  by        blast

lemma adelic_int_metric_ball_UNIV:
  "ball x e = UNIV" if "e \<ge> 1" for x :: "'a::nontrivial_factorial_idom adelic_int"
proof (cases "e = 1")
  case False with that have "e > 1" by linarith
  thus ?thesis
    using     that global_p_depth_adelic_int.bdd_global_dist_ball_UNIV
    unfolding ball_def dist_adelic_int_def
    by        blast
next
  case True
  have "ball x e = x +o ball 0 e" using adelic_int_metric_ball_translate by auto
  also from True have "\<dots> = x +o \<O>\<^sub>\<forall>\<^sub>p"
    using adelic_int_metric_ball_at_0_normalize by force
  finally show ?thesis
    using global_p_depth_adelic_int.global_depth_set_elt_set_plus nonpos_global_depth_set_adelic_int
    by    fastforce
qed

lemma adelic_int_left_translate_metric_continuous:
  "continuous_on UNIV ((+) x)" for x :: "'a::nontrivial_factorial_idom adelic_int"
proof
  fix e :: real and z :: "'a adelic_int"
  assume e: "e > 0"
  moreover have "\<forall>y. dist y z < e \<longrightarrow> dist (x + y) (x + z) \<le> e"
    using global_p_depth_adelic_int.bdd_global_dist_left_translate_continuous[of
            _ _ e x
          ]
    unfolding dist_p_adic_prod_def
    by        fastforce
  ultimately show
    "\<exists>d>0. \<forall>x'\<in>UNIV.
      dist x' z < d \<longrightarrow> dist (x + x') (x + z) \<le> e"
    by    auto
qed

lemma adelic_int_right_translate_metric_continuous:
  "continuous_on UNIV (\<lambda>z. z + x)" for x :: "'a::nontrivial_factorial_idom adelic_int"
proof-
  have "(\<lambda>z. z + x) = (+) x" by (auto simp add: add.commute)
  thus ?thesis using adelic_int_left_translate_metric_continuous by metis
qed

lemma adelic_int_left_mult_bdd_metric_continuous:
  "continuous_on UNIV ((*) x)"
  for x :: "'a::nontrivial_factorial_idom adelic_int"
proof
  fix e :: real and z :: "'a adelic_int"
  assume e: "e > 0"
  moreover define d where "d \<equiv> min (e * inverse 2) 1"
  moreover have "inverse (2::real) = 2 powi (-1)" using power_int_def by force
  ultimately have "\<forall>y. dist y z < d \<longrightarrow> dist (x * y) (x * z) \<le> e"
    using global_p_depth_adelic_int.bdd_global_dist_bdd_mult_continuous[of e x 0] adelic_int_depth
    by    fastforce
  moreover from e d_def have "d > 0" by auto
  ultimately show
    "\<exists>d>0. \<forall>y\<in>UNIV. dist y z < d \<longrightarrow> dist (x * y) (x * z) \<le> e"
    by    blast
qed

lemma adelic_int_bdd_metric_limseq_mult:
  "(\<lambda>k. w * X k) \<longlonglongrightarrow> (w * x)" if "X \<longlonglongrightarrow> x"
  for w x :: "'a::nontrivial_factorial_idom adelic_int" and X :: "nat \<Rightarrow> 'a adelic_int"
  using that adelic_int_left_mult_bdd_metric_continuous continuous_on_tendsto_compose
  by    fastforce

lemma adelic_int_global_depth_set_open:
  "open ((\<P>\<^sub>\<forall>\<^sub>p\<^sup>n) :: 'a::nontrivial_factorial_idom adelic_int set)"
proof (cases "n \<ge> 0")
  case True
  hence "(\<P>\<^sub>\<forall>\<^sub>p\<^sup>n) = ball (0::'a adelic_int) (inverse (2 ^ nat n))"
    using adelic_int_metric_ball_at_0 by fastforce
  thus ?thesis by simp
next
  case False
  hence "(\<P>\<^sub>\<forall>\<^sub>p\<^sup>n) = (UNIV :: 'a adelic_int set)"
    using nonpos_global_depth_set_adelic_int[of n] by simp
  thus ?thesis using open_UNIV by fastforce
qed

lemma adelic_int_ball_abs_eq:
  "Abs_adelic_int ` ball x e = ball (Abs_adelic_int x) e"
  if "x \<in> \<O>\<^sub>\<forall>\<^sub>p" and "e \<le> 1"
  for x :: "'a::nontrivial_factorial_idom p_adic_prod"
proof safe
  fix y assume "y \<in> ball x e"
  moreover from this that(2) have "y \<in> ball x 1" by fastforce
  ultimately show "Abs_adelic_int y \<in> ball (Abs_adelic_int x) e"
    using that(1) p_adic_prod_nonpos_global_depth_set_open mem_ball dist_adelic_int_abs_eq
    by    fastforce
next
  fix y assume "y \<in> ball (Abs_adelic_int x) e"
  with that(1) show "y \<in> Abs_adelic_int ` ball x e"
    unfolding ball_def using dist_adelic_int_abs_eq by (cases y) fastforce
qed

lemma open_adelic_int_abs_eq:
  "open U = open (Abs_adelic_int ` U)" if "U \<subseteq> (\<O>\<^sub>\<forall>\<^sub>p)"
  for U :: "'a::nontrivial_factorial_idom p_adic_prod set"
proof (standard, standard, clarify)
  fix u assume u: "u \<in> U"
  moreover assume "open U"
  ultimately obtain e where e: "e > 0" "ball u e \<subseteq> U"
    by (elim Elementary_Metric_Spaces.openE)
  define e' where "e' \<equiv> min e 1"
  with e(2) have "ball u e' \<subseteq> U" by force
  with that u e'_def have "ball (Abs_adelic_int u) e' \<subseteq> Abs_adelic_int ` U"
    using adelic_int_ball_abs_eq[of u e'] by auto
  moreover from e(1) e'_def have "e' > 0" by auto
  ultimately show "\<exists>e>0. ball (Abs_adelic_int u) e \<subseteq> Abs_adelic_int ` U"
    using e(1) e'_def by blast
next
  assume U: "open (Abs_adelic_int ` U)"
  show "open U"
  proof
    have inj_abs: "inj_on Abs_adelic_int (\<O>\<^sub>\<forall>\<^sub>p)"
      using Abs_adelic_int_inject inj_onI by meson
    fix u assume u: "u \<in> U"
    with U obtain e where e: "e > 0" "ball (Abs_adelic_int u) e \<subseteq> Abs_adelic_int ` U"
      using Elementary_Metric_Spaces.openE by blast
    define e' where "e' \<equiv> min e 1"
    with that e(2) u have "Abs_adelic_int ` ball u e' \<subseteq> Abs_adelic_int ` U"
      using adelic_int_ball_abs_eq[of u e'] by fastforce
    moreover from that u e'_def have "ball u e' \<subseteq> (\<O>\<^sub>\<forall>\<^sub>p)"
      using p_adic_prod_nonpos_global_depth_set_open[of 0] by fastforce
    ultimately have "ball u e' \<subseteq> U" using that inj_on_vimage_image_eq[OF inj_abs] by blast
    moreover from e(1) e'_def have "e' > 0" by simp
    ultimately show "\<exists>e>0. ball u e \<subseteq> U" by blast
  qed
qed

text \<open>Completeness\<close>

abbreviation "adelic_int_globally_cauchy  \<equiv> global_p_depth_adelic_int.globally_cauchy"
abbreviation
  "adelic_int_global_cauchy_condition  \<equiv> global_p_depth_adelic_int.global_cauchy_condition"

lemma adelic_int_global_cauchy_condition_abs_eq:
  "adelic_int_global_cauchy_condition (\<lambda>n. Abs_adelic_int (X n)) =
    p_adic_prod_global_cauchy_condition X"
  if "range X \<subseteq> \<O>\<^sub>\<forall>\<^sub>p"
  unfolding global_p_depth_adelic_int.global_cauchy_condition_def
            global_p_depth_p_adic_prod.global_cauchy_condition_def
  by        (
              standard, standard,
              metis that subsetD rangeI p_equal_adelic_int_abs_eq p_depth_adelic_int_diff_abs_eq
            )

lemma adelic_int_globally_cauchy_abs_eq:
  "adelic_int_globally_cauchy (\<lambda>n. Abs_adelic_int (X n)) = p_adic_prod_globally_cauchy X"
  if "range X \<subseteq> \<O>\<^sub>\<forall>\<^sub>p"
  using that adelic_int_global_cauchy_condition_abs_eq by metis

lemma adelic_int_globally_cauchy_vs_bdd_metric_Cauchy:
  "adelic_int_globally_cauchy X = Cauchy X"
  for X :: "nat \<Rightarrow> 'a::nontrivial_factorial_idom adelic_int"
  using     global_p_depth_adelic_int.globally_cauchy_vs_bdd_metric_Cauchy
  unfolding global_p_depth_adelic_int.metric_space_by_bdd_depth.Cauchy_def Cauchy_def
  by        auto

lemma adelic_int_Cauchy_abs_eq:
  "Cauchy (\<lambda>n. Abs_adelic_int (X n)) = Cauchy X"
  if  "range X \<subseteq> \<O>\<^sub>\<forall>\<^sub>p"
  for X :: "nat \<Rightarrow> 'a::nontrivial_factorial_idom p_adic_prod"
  using that adelic_int_globally_cauchy_vs_bdd_metric_Cauchy adelic_int_globally_cauchy_abs_eq
        p_adic_prod_globally_cauchy_vs_bdd_metric_Cauchy
  by    fast

abbreviation
  "adelic_int_cauchy_lim X \<equiv>
    Abs_adelic_int (p_adic_prod_cauchy_lim (\<lambda>n. Rep_adelic_int (X n)))"

lemma adelic_int_bdd_metric_complete':
  "X \<longlonglongrightarrow> adelic_int_cauchy_lim X" if "Cauchy X"
  for X :: "nat \<Rightarrow> 'a::nontrivial_factorial_unique_euclidean_bezout adelic_int"
proof (cases X rule: adelic_int_seq_cases)
  case (Abs_adelic_int F)
  with that have "F \<longlonglongrightarrow> p_adic_prod_cauchy_lim F"
    using adelic_int_Cauchy_abs_eq p_adic_prod_bdd_metric_complete' by blast
  moreover from this Abs_adelic_int(2)
    have  "p_adic_prod_cauchy_lim F \<in> \<O>\<^sub>\<forall>\<^sub>p"
    using eventually_sequentially p_adic_prod_global_depth_set_lim_closed[of F]
    by    force
  ultimately have "X \<longlonglongrightarrow> Abs_adelic_int (p_adic_prod_cauchy_lim F)"
    using Abs_adelic_int adelic_int_limseq_abs_eq by blast
  moreover have "F = (\<lambda>n. Rep_adelic_int (X n))"
    unfolding Abs_adelic_int(1)
  proof
    fix n from Abs_adelic_int(2) show "F n = Rep_adelic_int (Abs_adelic_int (F n))"
      using Abs_adelic_int_inverse[of "F n"] by fastforce
  qed
  ultimately show ?thesis by meson
qed

lemma adelic_int_bdd_metric_complete:
  "complete (UNIV :: 'a::nontrivial_factorial_unique_euclidean_bezout adelic_int set)"
  using adelic_int_bdd_metric_complete' completeI by blast


end  (* theory *)
