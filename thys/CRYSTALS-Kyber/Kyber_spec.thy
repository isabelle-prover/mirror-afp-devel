theory Kyber_spec
imports Main "HOL-Computational_Algebra.Computational_Algebra" 
  "HOL-Computational_Algebra.Polynomial_Factorial"
  "Berlekamp_Zassenhaus.Poly_Mod" 
  "Berlekamp_Zassenhaus.Poly_Mod_Finite_Field"

begin
hide_type Matrix.vec
hide_const Matrix.vec_index

section \<open>Type Class for Factorial Ring $\mathbb{Z}_q[x]/(x^n+1)$.\<close>
text \<open>The Kyber algorithms work over the quotient ring $\mathbb{Z}_q[x]/(x^n+1)$
where $q$ is a prime with $q\equiv 1 \mod 4$ and $n$ is a power of $2$.
We encode this quotient ring as a type. In order to do so, we first look at the
finite field $\mathbb{Z}_q$ implemented by \<open>('a::prime_card) mod_ring\<close>. 
Then we define polynomials using the constructor \<open>poly\<close>.
For factoring out $x^n+1$, we define an equivalence relation on the polynomial ring
$\mathbb{Z}_q[x]$ via the modulo operation with modulus $x^n+1$.
Finally, we build the quotient of the equivalence relation using the construction 
\<open>quotient_type\<close>.\<close>
text \<open>The module $\mathbb{Z}_q[x]/(x^n+1)$ was formalized with help from Manuel Eberl.\<close>

text \<open>Modulo relation between two polynomials. \<close>
lemma of_int_mod_ring_eq_0_iff:
  "(of_int n :: ('n :: {finite, nontriv} mod_ring)) = 0 \<longleftrightarrow> 
    int (CARD('n)) dvd n"
  by transfer auto

lemma of_int_mod_ring_eq_of_int_iff:
  "(of_int n :: ('n :: {finite, nontriv} mod_ring)) = of_int m \<longleftrightarrow> 
    [n = m] (mod (int (CARD('n))))"
  by transfer (auto simp: cong_def)

definition mod_poly_rel :: "nat \<Rightarrow> int poly \<Rightarrow> int poly \<Rightarrow> bool" where
  "mod_poly_rel m p q \<longleftrightarrow> 
    (\<forall>n. [poly.coeff p n = poly.coeff q n] (mod (int m)))"

lemma mod_poly_rel_altdef:
  "mod_poly_rel CARD('n :: nontriv) p q \<longleftrightarrow> 
    (of_int_poly p) = (of_int_poly q :: 'n mod_ring poly)"
  by (auto simp: poly_eq_iff mod_poly_rel_def 
    of_int_mod_ring_eq_of_int_iff)

definition mod_poly_is_unit :: "nat \<Rightarrow> int poly \<Rightarrow> bool" where
  "mod_poly_is_unit m p \<longleftrightarrow> (\<exists>r. mod_poly_rel m (p * r) 1)"

lemma mod_poly_is_unit_altdef:
  "mod_poly_is_unit CARD('n :: nontriv) p \<longleftrightarrow> 
    (of_int_poly p :: 'n mod_ring poly) dvd 1"
proof
  assume "mod_poly_is_unit CARD('n) p"
  thus "(of_int_poly p :: 'n mod_ring poly) dvd 1"
    by (auto simp: mod_poly_is_unit_def dvd_def mod_poly_rel_altdef 
      of_int_poly_hom.hom_mult)
next 
  assume "(of_int_poly p :: 'n mod_ring poly) dvd 1"
  then obtain q where q: "(of_int_poly p :: 'n mod_ring poly) * q = 1"
    by auto
  also have "q = of_int_poly (map_poly to_int_mod_ring q)"
    by (simp add: of_int_of_int_mod_ring poly_eqI)
  also have "of_int_poly p * \<dots> = 
      of_int_poly (p * map_poly to_int_mod_ring q)"
    by (simp add: of_int_poly_hom.hom_mult)
  finally show "mod_poly_is_unit CARD('n) p"
    by (auto simp: mod_poly_is_unit_def mod_poly_rel_altdef)
qed

definition mod_poly_irreducible :: "nat \<Rightarrow> int poly \<Rightarrow> bool" where
  "mod_poly_irreducible m Q \<longleftrightarrow>
     \<not>mod_poly_rel m Q 0 \<and>
     \<not>mod_poly_is_unit m Q \<and>
        (\<forall>a b. mod_poly_rel m Q (a * b) \<longrightarrow>
               mod_poly_is_unit m a \<or> mod_poly_is_unit m b)"

lemma of_int_poly_to_int_poly: "of_int_poly (to_int_poly p) = p"
  by (simp add: of_int_of_int_mod_ring poly_eqI)

lemma mod_poly_irreducible_altdef:
  "mod_poly_irreducible CARD('n :: nontriv) p \<longleftrightarrow> 
    irreducible (of_int_poly p :: 'n mod_ring poly)"
proof
  assume "irreducible (of_int_poly p :: 'n mod_ring poly)"
  thus "mod_poly_irreducible CARD('n) p"
    by (auto simp: mod_poly_irreducible_def mod_poly_rel_altdef 
    mod_poly_is_unit_altdef irreducible_def of_int_poly_hom.hom_mult)
next
  assume *: "mod_poly_irreducible CARD('n) p"
  show "irreducible (of_int_poly p :: 'n mod_ring poly)"
    unfolding irreducible_def
  proof (intro conjI impI allI)
    fix a b assume ab: "(of_int_poly p :: 'n mod_ring poly) = a * b"
    have "of_int_poly (map_poly to_int_mod_ring a * 
      map_poly to_int_mod_ring b) =
      of_int_poly (map_poly to_int_mod_ring a) *
      (of_int_poly (map_poly to_int_mod_ring b) :: 'n mod_ring poly)"
      by (simp add: of_int_poly_hom.hom_mult)
    also have "\<dots> = a * b"
      by (simp add: of_int_poly_to_int_poly)
    also have "\<dots> = of_int_poly p"
      using ab by simp
    finally have "(of_int_poly p :: 'n mod_ring poly) = 
      of_int_poly (to_int_poly a * to_int_poly b)" ..
    hence "of_int_poly (to_int_poly a) dvd (1 :: 'n mod_ring poly) \<or>
           of_int_poly (to_int_poly b) dvd (1 :: 'n mod_ring poly)"
      using * unfolding mod_poly_irreducible_def mod_poly_rel_altdef 
        mod_poly_is_unit_altdef by blast
    thus "(a dvd (1 :: 'n mod_ring poly)) \<or> 
      (b dvd (1 :: 'n mod_ring poly))"
      by (simp add: of_int_poly_to_int_poly)
  qed (use * in \<open>auto simp: mod_poly_irreducible_def 
    mod_poly_rel_altdef mod_poly_is_unit_altdef\<close>)
qed
    
text \<open>Type class for quotient ring $\mathbb{Z}_q[x]/(p)$. 
  The polynomial p is represented as \<open>qr_poly'\<close> (an polynomial over the integers).\<close>

class qr_spec = prime_card +
  fixes qr_poly' :: "'a itself \<Rightarrow> int poly"
  assumes not_dvd_lead_coeff_qr_poly':  
      "\<not>int CARD('a) dvd lead_coeff (qr_poly' TYPE('a))"
  and deg_qr'_pos : "degree (qr_poly' TYPE('a)) > 0"

text \<open>\<open>qr_poly\<close> is the respective polynomial in $\mathbb{Z}_q[x]$.\<close>
definition qr_poly :: "'a :: qr_spec mod_ring poly" where
  "qr_poly = of_int_poly (qr_poly' TYPE('a))"

text \<open>Functions to get the degree of the polynomials to be factored out.\<close>
definition (in qr_spec) deg_qr :: "'a itself \<Rightarrow> nat" where
  "deg_qr _ = degree (qr_poly' TYPE('a))"

lemma degree_qr_poly': 
  "degree (qr_poly' TYPE('a :: qr_spec)) = deg_qr (TYPE('a))"
  by (simp add: deg_qr_def)

lemma degree_of_int_poly':
  assumes "of_int (lead_coeff p) \<noteq> (0 :: 'a :: ring_1)"
  shows "degree (of_int_poly p :: 'a poly) = degree p"
proof (intro antisym)
  show "degree (of_int_poly p) \<le> degree p"
    by (intro degree_le) (auto simp: coeff_eq_0)
  show "degree (of_int_poly p :: 'a poly) \<ge> degree p"
    using assms by (intro le_degree) auto
qed

lemma degree_qr_poly:
  "degree (qr_poly :: 'a :: qr_spec mod_ring poly) = deg_qr (TYPE('a))"
  unfolding qr_poly_def 
  using not_dvd_lead_coeff_qr_poly'[where ?'a = 'a]
  by (subst degree_of_int_poly') 
     (auto simp: of_int_mod_ring_eq_0_iff degree_qr_poly')

lemma deg_qr_pos : "deg_qr TYPE('a :: qr_spec) > 0"
by (metis deg_qr'_pos degree_qr_poly')

text \<open>The factor polynomial is non-zero.\<close>
lemma qr_poly_nz [simp]: "qr_poly \<noteq> 0"
  using deg_qr_pos[where ?'a = 'a] by (auto simp flip: degree_qr_poly)

text \<open>Thus, when factoring out $p$, it has no effect on the neutral element $1$.\<close>
lemma one_mod_qr_poly [simp]: 
  "1 mod (qr_poly :: 'a :: qr_spec mod_ring poly) = 1"
proof -
  have "2 ^ 1 \<le> (2 ^ deg_qr TYPE('a) :: nat)"
    using deg_qr_pos[where ?'a = 'a] 
    by (intro power_increasing) auto
  thus ?thesis by (metis degree_qr_poly deg_qr_pos degree_1 mod_poly_less)
qed

text \<open>We define a modulo relation for polynomials modulo a polynomial $p=$\<open>qr_poly\<close>.\<close>
definition qr_rel :: "'a :: qr_spec mod_ring poly \<Rightarrow> 'a mod_ring poly \<Rightarrow> bool" where
  "qr_rel P Q \<longleftrightarrow> [P = Q] (mod qr_poly)"

lemma equivp_qr_rel: "equivp qr_rel"
  by (intro equivpI sympI reflpI transpI)
     (auto simp: qr_rel_def cong_sym intro: cong_trans)

text \<open>Using this equivalence relation, we can define the quotient ring as a \<open>quotient_type\<close>.\<close>
quotient_type (overloaded) 'a qr = "'a :: qr_spec mod_ring poly" / qr_rel
  by (rule equivp_qr_rel)

text \<open>Defining the conversion functions.\<close>
lift_definition to_qr :: "'a :: qr_spec mod_ring poly \<Rightarrow> 'a qr" 
  is "\<lambda>x. (x :: 'a mod_ring poly)" .

lift_definition of_qr :: "'a qr \<Rightarrow> 'a :: qr_spec mod_ring poly" 
  is "\<lambda>P::'a mod_ring poly. P mod qr_poly"
  by (simp add: qr_rel_def cong_def)

text \<open>Simplification lemmas on conversion functions.\<close>
lemma of_qr_to_qr: "of_qr (to_qr (x)) = x mod qr_poly"
  apply (auto simp add: of_qr_def to_qr_def)
  by (metis of_qr.abs_eq of_qr.rep_eq)


lemma to_qr_of_qr: "to_qr (of_qr (x)) = x"
  apply (auto simp add: of_qr_def to_qr_def)
  by (metis (mono_tags, lifting) Quotient3_abs_rep Quotient3_qr 
    Quotient3_rel cong_def qr_rel_def mod_mod_trivial)

lemma eq_to_qr: "x = y \<Longrightarrow> to_qr x = to_qr y" by auto





text \<open>Type class instantiation for \<open>qr\<close> (quotient ring).\<close>
instantiation qr :: (qr_spec) comm_ring_1
begin

lift_definition zero_qr :: "'a qr" is "0" .

lift_definition one_qr :: "'a qr" is "1" .

lift_definition plus_qr :: "'a qr \<Rightarrow> 'a qr \<Rightarrow> 'a qr"
  is "(+)"
  unfolding qr_rel_def using cong_add by blast

lift_definition uminus_qr :: "'a qr \<Rightarrow> 'a qr"
  is "uminus"
  unfolding qr_rel_def  using cong_minus_minus_iff by blast

lift_definition minus_qr :: "'a qr \<Rightarrow> 'a qr \<Rightarrow> 'a qr"
  is "(-)"
  unfolding qr_rel_def using cong_diff by blast

lift_definition times_qr :: "'a qr \<Rightarrow> 'a qr \<Rightarrow> 'a qr"
  is "(*)"
  unfolding qr_rel_def using cong_mult by blast

instance
proof
  show "0 \<noteq> (1 :: 'a qr)"
    by transfer (simp add: qr_rel_def cong_def)
qed (transfer; simp add: qr_rel_def algebra_simps; fail)+

end

lemma of_qr_0 [simp]: "of_qr 0 = 0"
  and of_qr_1 [simp]: "of_qr 1 = 1"
  and of_qr_uminus [simp]: "of_qr (-p) = -of_qr p"
  and of_qr_add [simp]: "of_qr (p + q) = of_qr p + of_qr q"
  and of_qr_diff [simp]: "of_qr (p - q) = of_qr p - of_qr q"
  by (transfer; simp add: poly_mod_add_left poly_mod_diff_left; fail)+

lemma to_qr_0 [simp]: "to_qr 0 = 0"
  and to_qr_1 [simp]: "to_qr 1 = 1"
  and to_qr_uminus [simp]: "to_qr (-p) = -to_qr p"
  and to_qr_add [simp]: "to_qr (p + q) = to_qr p + to_qr q"
  and to_qr_diff [simp]: "to_qr (p - q) = to_qr p - to_qr q"
  and to_qr_mult [simp]: "to_qr (p * q) = to_qr p * to_qr q"
  by (transfer'; simp; fail)+

lemma to_qr_of_nat [simp]: "to_qr (of_nat n) = of_nat n"
  by (induction n) auto

lemma to_qr_of_int [simp]: "to_qr (of_int n) = of_int n"
  by (induction n) auto

lemma of_qr_of_nat [simp]: "of_qr (of_nat n) = of_nat n"
  by (induction n) auto

lemma of_qr_of_int [simp]: "of_qr (of_int n) = of_int n"
  by (induction n) auto

lemma of_qr_eq_0_iff [simp]: "of_qr p = 0 \<longleftrightarrow> p = 0"
  by transfer (simp add: qr_rel_def cong_def)

lemma to_qr_eq_0_iff:
  "to_qr p = 0 \<longleftrightarrow> qr_poly dvd p"
  by transfer (auto simp: qr_rel_def cong_def)


text \<open>Some more lemmas that will probably be useful.\<close>

lemma to_qr_eq_iff [simp]:
  "to_qr P = (to_qr Q :: 'a :: qr_spec qr) \<longleftrightarrow> [P = Q] (mod qr_poly)"
  by transfer (auto simp: qr_rel_def)

text \<open>Reduction modulo $x^n + 1$ is injective on polynomials of degree less than $n$
  in particular, this means that \<open>card(QR(q^n)) = q^n\<close>. \<close>
lemma inj_on_to_qr:
  "inj_on
     (to_qr :: 'a :: qr_spec mod_ring poly \<Rightarrow> 'a qr)
     {P. degree P < deg_qr TYPE('a)}"
  by (intro inj_onI) (auto simp: cong_def mod_poly_less 
      simp flip: degree_qr_poly)

text \<open>Characteristic of quotient ring is exactly q.\<close>

lemma of_int_qr_eq_0_iff [simp]:
  "of_int n = (0 :: 'a :: qr_spec qr) \<longleftrightarrow> int (CARD('a)) dvd n"
proof -
  have "of_int n = (0 :: 'a qr) \<longleftrightarrow> (of_int n :: 'a mod_ring poly) = 0"
    by (smt (z3) of_qr_eq_0_iff of_qr_of_int)
  also have "\<dots> \<longleftrightarrow> (of_int n :: 'a mod_ring) = 0"
    by (simp add: of_int_poly)
  also have "\<dots> \<longleftrightarrow> int (CARD('a)) dvd n"
    by (simp add: of_int_mod_ring_eq_0_iff)
  finally show ?thesis .
qed

lemma of_int_qr_eq_of_int_iff:
  "of_int n = (of_int m :: 'a :: qr_spec qr) \<longleftrightarrow> 
    [n = m] (mod (int (CARD('a))))"
  using of_int_qr_eq_0_iff[of "n - m", where ?'a = 'a]
  by (simp del: of_int_qr_eq_0_iff add: cong_iff_dvd_diff)

lemma of_nat_qr_eq_of_nat_iff:
  "of_nat n = (of_nat m :: 'a :: qr_spec qr) \<longleftrightarrow> 
    [n = m] (mod CARD('a))"
  using of_int_qr_eq_of_int_iff[of "int n" "int m"] 
  by (simp add: cong_int_iff)

lemma of_nat_qr_eq_0_iff [simp]:
  "of_nat n = (0 :: 'a :: qr_spec qr) \<longleftrightarrow> CARD('a) dvd n"
  using of_int_qr_eq_0_iff[of "int n"] by simp


section \<open>Specification of Kyber\<close>



definition to_module :: "int \<Rightarrow> 'a ::qr_spec qr" where
  "to_module x = to_qr (Poly [of_int_mod_ring x ::'a mod_ring])"

text \<open>Properties in the ring \<open>'a qr\<close>. A good representative has degree up to n.\<close>
lemma deg_mod_qr_poly:
  assumes "degree x < deg_qr TYPE('a::qr_spec)"
  shows "x mod (qr_poly :: 'a mod_ring poly) = x"
using mod_poly_less[of x qr_poly] unfolding deg_qr_def
by (metis assms degree_qr_poly) 

lemma of_qr_to_qr': 
  assumes "degree x < deg_qr TYPE('a::qr_spec)"
  shows "of_qr (to_qr x) = (x ::'a mod_ring poly)"
using deg_mod_qr_poly[OF assms] of_qr_to_qr[of x] by simp



lemma deg_of_qr: 
  "degree (of_qr (x ::'a qr)) < deg_qr TYPE('a::qr_spec)"
by (metis deg_qr_pos degree_0 degree_qr_poly degree_mod_less' 
  qr_poly_nz of_qr.rep_eq)


lemma to_qr_smult_to_module: 
  "to_qr (Polynomial.smult a p) = (to_qr (Poly [a])) * (to_qr p)"
by (metis Poly.simps(1) Poly.simps(2) mult.left_neutral 
  mult_smult_left smult_one to_qr_mult)

lemma of_qr_to_qr_smult:
  "of_qr (to_qr (Polynomial.smult a p)) = 
  Polynomial.smult a (of_qr (to_qr p))"
by (simp add: mod_smult_left of_qr_to_qr)

text \<open>The following locale comprehends all variables used in crypto schemes over $R_q$ like
Kyber and Dilithium.\<close>

locale module_spec =
fixes "type_a" :: "('a :: qr_spec) itself" 
  and "type_k" :: "('k ::finite) itself" 
  and n q::int and k n'::nat
assumes
n_powr_2: "n = 2 ^ n'" and
n'_gr_0: "n' > 0" and 
q_gr_two: "q > 2" and
q_prime : "prime q" and
CARD_a: "int (CARD('a :: qr_spec)) = q" and
CARD_k: "int (CARD('k :: finite)) = k" and
qr_poly'_eq: "qr_poly' TYPE('a) = Polynomial.monom 1 (nat n) + 1"

begin
text \<open>Some properties of the modulus q.\<close>

lemma q_nonzero: "q \<noteq> 0" 
using module_spec_axioms module_spec_def  by (smt (z3))

lemma q_gt_zero: "q>0" 
using module_spec_axioms module_spec_def by (smt (z3))

lemma q_gt_two: "q>2"
using module_spec_axioms module_spec_def by (smt (z3))

lemma q_odd: "odd q"
using module_spec_axioms module_spec_def prime_odd_int by blast

lemma nat_q: "nat q = q"
using q_gt_zero by force

text \<open>Some properties of the degree n.\<close>

lemma n_gt_1: "n > 1"
using module_spec_axioms module_spec_def
  by (simp add: n'_gr_0 n_powr_2)

lemma n_nonzero: "n \<noteq> 0" 
using n_gt_1 by auto

lemma n_gt_zero: "n>0" 
using n_gt_1 by auto

lemma nat_n: "nat n = n"
using n_gt_zero by force

lemma deg_qr_n: 
  "deg_qr TYPE('a) = n"
unfolding deg_qr_def using qr_poly'_eq n_gt_1
by (simp add: degree_add_eq_left degree_monom_eq)

end

text \<open>
We now define a locale for the specification parameters of Kyber as in \cite{kyber}.
The specifications use the parameters:

\begin{tabular}{r l}
$n$ & $=256 = 2^{n'}$\\
$n'$ & $= 8$\\
$q$ & $= 7681$ or $3329$\\
$k$ & $= 3$\\
\end{tabular}

Additionally, we need that $q$ is a prime with the property $q\equiv 1\mod 4$.
\<close>

locale kyber_spec = module_spec "TYPE ('a ::qr_spec)" "TYPE ('k::finite)" +
fixes type_a :: "('a :: qr_spec) itself" 
  and type_k :: "('k ::finite) itself" 
assumes q_mod_4: "q mod 4 = 1"
begin 
end

end