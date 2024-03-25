theory Padic_Fields
  imports Fraction_Field Padic_Ints.Hensels_Lemma

begin


(**************************************************************************************************)
(**************************************************************************************************)
section\<open>Constructing the $p$-adic Valued Field\<close>
(**************************************************************************************************)
(**************************************************************************************************)

text\<open>
  As a field, we can define the field $\mathbb{Q}_p$ immediately as the fraction field of 
  $\mathbb{Z}_p$. The valuation can then be extended from to $\mathbb{Z}_p$ to $\mathbb{Q}_p$ by 
  defining $\text{val}(a/b) = \text{val}\ a - \text{val}\ b$ where $a, b \in \mathbb{Z}_p$. \<close>

(**********************************************************************************************)
(**************************************************************************************************)
subsection\<open>A Locale for $p$-adic Fields\<close>
(**************************************************************************************************)
(**************************************************************************************************)

text\<open>
  This section builds a locale for reasoning about general $p$-adic fields for a fixed $p$. 
  The locale fixes constants for the ring of $p$-adic integers ($\mathbb{Z}_p$) and the inclusion
   map $\iota: \mathbb{Z}_p \to \mathbb{Q}_p$. \<close>
type_synonym padic_number = "((nat \<Rightarrow> int) \<times> (nat \<Rightarrow> int)) set"
locale padic_fields= 
fixes Q\<^sub>p:: "_ ring" (structure)
fixes Z\<^sub>p:: "_ ring" (structure)
fixes p
fixes \<iota>
defines "Z\<^sub>p \<equiv> padic_int p"
defines "Q\<^sub>p \<equiv> Frac Z\<^sub>p"
defines "\<iota> \<equiv> domain_frac.inc Z\<^sub>p"
assumes prime: "prime p"

sublocale padic_fields < Zp?: domain_frac Z\<^sub>p
  by (simp add: Z\<^sub>p_def domain_frac.intro padic_int_is_domain prime)

sublocale padic_fields < Qp?: ring Q\<^sub>p
  unfolding Q\<^sub>p_def 
  by (simp add: Fraction_Field.domain_frac_def domain_axioms domain_frac.fraction_field_is_field field.is_ring)
 
sublocale padic_fields < Qp?: cring Q\<^sub>p
  unfolding Q\<^sub>p_def 
  by (simp add: Fraction_Field.domain_frac_def domain.axioms(1) domain_axioms domain_frac.fraction_field_is_domain)
 
sublocale padic_fields < Qp?: field Q\<^sub>p
  unfolding Q\<^sub>p_def 
  by (simp add: Fraction_Field.domain_frac_def domain_axioms domain_frac.fraction_field_is_field)

sublocale padic_fields < Qp?: domain Q\<^sub>p
  by (simp add: Qp.domain_axioms)

sublocale padic_fields <  padic_integers Z\<^sub>p  
apply (simp add: padic_integers_def prime) 
using Z\<^sub>p_def by auto

sublocale padic_fields < UPQ?: UP_cring Q\<^sub>p "UP Q\<^sub>p"
  using Qp.is_cring UP_cring_def apply blast
  by auto 

(**************************************************************************************************)
(**************************************************************************************************)
subsection\<open>The Valuation Ring in $\mathbb{Q}_p$\<close>
(**************************************************************************************************)
(**************************************************************************************************)

text\<open>
  The valuation ring $\mathcal{O}_p$ is the subring of elements in $\mathbb{Q}_p$ with positive 
  valuation. It is an isomorphic copy of $\mathbb{Z}_p$.\<close>
context padic_fields
begin

abbreviation \<O>\<^sub>p where
"\<O>\<^sub>p \<equiv> \<iota> ` carrier Z\<^sub>p"

lemma inc_closed: 
  assumes "a \<in> carrier Z\<^sub>p"
  shows "\<iota> a \<in> carrier Q\<^sub>p"
  using Q\<^sub>p_def \<iota>_def assms Zp.inc_is_hom ring_hom_closed
  by fastforce

lemma inc_is_hom:
"\<iota> \<in> ring_hom Z\<^sub>p Q\<^sub>p"
  unfolding Q\<^sub>p_def \<iota>_def  
by(rule Zp.inc_is_hom)

text\<open>An alternate formula of the map $\iota$\<close>

lemma inc_def: 
  assumes "a \<in> carrier Z\<^sub>p"
  shows "\<iota> a = frac a \<one>\<^bsub>Z\<^sub>p\<^esub>" 
  using assms inc_equation[of a] \<iota>_def by auto

lemma inc_of_nonzero:
  assumes "a \<in> nonzero Z\<^sub>p"
  shows "\<iota> a \<in> nonzero Q\<^sub>p"
  using  \<iota>_def assms Q\<^sub>p_def Qp.nonzero_memI 
    Zp.nonzero_closed Zp.nonzero_one_closed frac_closed local.inc_def nonzero_fraction 
  by (metis Zp.nonzero_memE(2) inc_closed inc_inj1)
 
lemma inc_of_one:
"\<iota> \<one>\<^bsub>Z\<^sub>p\<^esub> = \<one>"
  by (simp add: inc_is_hom ring_hom_one)

lemma inc_of_zero:
"\<iota> \<zero>\<^bsub>Z\<^sub>p\<^esub> = \<zero>"
  apply(rule ring_hom_zero[of \<iota>], rule inc_is_hom)
  apply (simp add: Zp.ring_axioms)
  by (simp add: Qp.ring_axioms)

lemma inc_of_sum:
  assumes "a \<in> carrier Z\<^sub>p"
  assumes "b \<in> carrier Z\<^sub>p"
  shows "\<iota> (a \<oplus>\<^bsub>Z\<^sub>p\<^esub> b) = (\<iota> a) \<oplus> (\<iota> b)"
by(rule ring_hom_add[of _ Z\<^sub>p], rule inc_is_hom, rule assms, rule assms)

lemma inc_of_prod:
  assumes "a \<in> carrier Z\<^sub>p"
  assumes "b \<in> carrier Z\<^sub>p"
  shows "\<iota> (a \<otimes>\<^bsub>Z\<^sub>p\<^esub> b) = (\<iota> a) \<otimes> (\<iota> b)"
  by (simp add: assms(1) assms(2) inc_is_hom ring_hom_mult)

lemma inc_pow:
  assumes "a \<in> nonzero Z\<^sub>p"
  shows "\<iota> (a[^]\<^bsub>Z\<^sub>p\<^esub>(n::nat)) = (\<iota> a)[^] n"
  apply(induction n)
  apply (simp add: inc_of_one)
  by (simp add: assms inc_of_prod Zp.nonzero_closed)

lemma inc_of_diff:
  assumes "a \<in> carrier Z\<^sub>p"
  assumes "b \<in> carrier Z\<^sub>p"
  shows "\<iota> (a \<ominus>\<^bsub>Z\<^sub>p\<^esub>  b) = (\<iota> a) \<ominus> (\<iota> b)"
  using assms unfolding a_minus_def 
  using inc_is_hom Qp.ring_axioms Q\<^sub>p_def Zp.ring_hom_a_inv inc_of_sum by fastforce  

lemma Units_nonzero_Qp:
assumes "u \<in> Units Q\<^sub>p"
shows "u \<in> nonzero Q\<^sub>p"
  by (simp add: Qp.Units_nonzero assms) 

lemma Units_eq_nonzero:
 "Units Q\<^sub>p = nonzero Q\<^sub>p"
  using frac_nonzero_Units unfolding Q\<^sub>p_def Z\<^sub>p_def 
by blast 

lemma Units_inverse_Qp:
  assumes "u \<in> Units Q\<^sub>p"
  shows "inv\<^bsub>Q\<^sub>p\<^esub> u \<in> Units Q\<^sub>p"
  using Q\<^sub>p_def Units_eq_nonzero assms frac_nonzero_inv_Unit by auto
  
lemma nonzero_inverse_Qp:
  assumes "u \<in> nonzero Q\<^sub>p"
  shows "inv\<^bsub>Q\<^sub>p\<^esub> u \<in> nonzero Q\<^sub>p"
  using Units_eq_nonzero Units_inverse_Qp assms by auto  

lemma frac_add:
  assumes "a \<in> carrier Z\<^sub>p"
  assumes "b \<in> nonzero Z\<^sub>p"
  assumes "c \<in> carrier Z\<^sub>p"
  assumes "d \<in> nonzero Z\<^sub>p"
  shows "(frac a b) \<oplus> (frac c d) = (frac ((a \<otimes>\<^bsub>Z\<^sub>p\<^esub> d) \<oplus>\<^bsub>Z\<^sub>p\<^esub> (b \<otimes>\<^bsub>Z\<^sub>p\<^esub> c)) (b \<otimes>\<^bsub>Z\<^sub>p\<^esub> d))"
  by (simp add: Q\<^sub>p_def assms(1) assms(2) assms(3) assms(4) local.frac_add)

lemma frac_add_common_denom:
  assumes "a \<in> carrier Z\<^sub>p"
  assumes "b \<in> carrier Z\<^sub>p"
  assumes "c \<in> nonzero Z\<^sub>p"
  shows "(frac a c) \<oplus> (frac b c) = frac (a \<oplus>\<^bsub>Z\<^sub>p\<^esub> b) c"
  by (simp add: Q\<^sub>p_def assms(1) assms(2) assms(3) frac_add_common_denom)

lemma frac_mult:
  assumes "a \<in> carrier Z\<^sub>p"
  assumes "b \<in> nonzero Z\<^sub>p"
  assumes "c \<in> carrier Z\<^sub>p"
  assumes "d \<in> nonzero Z\<^sub>p"
  shows "(frac a b) \<otimes> (frac c d) = (frac (a \<otimes>\<^bsub>Z\<^sub>p\<^esub> c) (b \<otimes>\<^bsub>Z\<^sub>p\<^esub> d))"
  by (simp add: Q\<^sub>p_def assms(1) assms(2) assms(3) assms(4) frac_mult)

lemma frac_one:
  assumes "a \<in> nonzero Z\<^sub>p"
  shows "frac a a = \<one>"
  by (simp add: Q\<^sub>p_def assms frac_one)

lemma frac_closed:
  assumes "a \<in> carrier Z\<^sub>p"
  assumes "b \<in> nonzero Z\<^sub>p"
  shows "frac a b \<in> carrier Q\<^sub>p"
  by (simp add: Q\<^sub>p_def assms(1) assms(2) frac_closed)  

lemma inv_in_frac:
  assumes "a \<in> carrier Q\<^sub>p"
  assumes "a \<noteq>\<zero>"
  shows "inv\<^bsub>Q\<^sub>p\<^esub> a \<in> carrier Q\<^sub>p"
        "inv\<^bsub>Q\<^sub>p\<^esub> a \<noteq>\<zero>"
        "inv\<^bsub>Q\<^sub>p\<^esub> a \<in> nonzero Q\<^sub>p"
  apply (simp add: assms(1) assms(2) field_inv(3))
    using assms(1) assms(2) field_inv(1) apply fastforce
      using Qp.not_nonzero_memE assms(1) assms(2) nonzero_inverse_Qp by blast

lemma nonzero_numer_imp_nonzero_fraction:
  assumes "a \<in> nonzero Z\<^sub>p"
  assumes "b \<in> nonzero Z\<^sub>p"
  shows "frac a b \<noteq> \<zero>"
  by (simp add: Q\<^sub>p_def assms(1) assms(2) nonzero_fraction)

lemma nonzero_fraction_imp_numer_not_zero:
  assumes "a \<in> carrier Z\<^sub>p"
  assumes "b \<in> nonzero Z\<^sub>p"
  assumes "frac a b \<noteq> \<zero>"
  shows "a \<noteq> \<zero>\<^bsub>Z\<^sub>p\<^esub>"
  using assms fraction_zero Q\<^sub>p_def by blast

lemma nonzero_fraction_imp_nonzero_numer:
  assumes "a \<in> carrier Z\<^sub>p"
  assumes "b \<in> nonzero Z\<^sub>p"
  assumes "frac a b \<noteq> \<zero>"
  shows "a \<in> nonzero Z\<^sub>p"
  using assms(1) assms(2) assms(3) nonzero_fraction_imp_numer_not_zero not_nonzero_Zp by blast

lemma(in padic_fields) frac_inv_id:
  assumes "a \<in> nonzero Z\<^sub>p"
  assumes "b \<in> nonzero Z\<^sub>p" 
  assumes "c \<in> nonzero Z\<^sub>p"
  assumes "d \<in> nonzero Z\<^sub>p" 
  assumes "frac a b = frac c d"
  shows "frac b a = frac d c"
  using frac_inv assms  
  by metis  

lemma(in padic_fields) frac_uminus:
  assumes "a \<in> carrier Z\<^sub>p"
  assumes "b \<in> nonzero Z\<^sub>p"
  shows "\<ominus> (frac a b) = frac (\<ominus>\<^bsub>Z\<^sub>p\<^esub> a) b" 
  by (simp add: Q\<^sub>p_def assms(1) assms(2) frac_uminus)

lemma(in padic_fields) i_mult:
  assumes "a \<in> carrier Z\<^sub>p"
  assumes "c \<in> carrier Z\<^sub>p"
  assumes "d \<in> nonzero Z\<^sub>p"
  shows "(\<iota> a) \<otimes> (frac c d) = frac (a \<otimes>\<^bsub>Z\<^sub>p\<^esub> c) d"
  by (simp add: Q\<^sub>p_def \<iota>_def assms(1) assms(2) assms(3) i_mult)

lemma numer_denom_facts:
  assumes "a \<in> carrier Q\<^sub>p"
  shows "(numer a) \<in> carrier Z\<^sub>p"
        "(denom a) \<in> nonzero Z\<^sub>p"
        "a \<noteq> \<zero> \<Longrightarrow> numer a \<noteq> \<zero>\<^bsub>Z\<^sub>p\<^esub>"
        "a \<otimes> (\<iota> (denom a)) = \<iota> (numer a)"
        "a = frac (numer a) (denom a)" 
  unfolding Q\<^sub>p_def
  using Q\<^sub>p_def assms numer_denom_facts(2) apply auto[1]
    using Q\<^sub>p_def assms numer_denom_facts(3) apply blast
      using Q\<^sub>p_def assms numer_denom_facts(4) apply blast
        using Q\<^sub>p_def \<iota>_def assms numer_denom_facts(5) apply auto[1]
          using Q\<^sub>p_def assms numer_denom_facts(1) by auto

lemma get_common_denominator:
  assumes "x \<in> carrier Q\<^sub>p"
  assumes "y \<in> carrier Q\<^sub>p"
  obtains a b c where
    "a \<in> carrier Z\<^sub>p"
    "b \<in> carrier Z\<^sub>p" 
    "c \<in> nonzero Z\<^sub>p"
    "x = frac a c"
    "y = frac b c"
  using Q\<^sub>p_def assms(1) assms(2) common_denominator[of x y]
  by blast  

abbreviation fract :: "_ \<Rightarrow> _ \<Rightarrow> _" (infixl "\<div>" 50) where
"(fract a b) \<equiv> (a \<otimes> (inv\<^bsub>Q\<^sub>p\<^esub> b))"

text\<open>fract generalizes frac\<close>

lemma fract_frac:
  assumes "a \<in> carrier Z\<^sub>p"
  assumes "b \<in> nonzero Z\<^sub>p"
  shows "(frac a b) = (\<iota> a \<div> \<iota> b)" 
proof-
  have B: "b \<in> carrier Z\<^sub>p" 
    using Zp.nonzero_closed assms(2) by auto    
  have P0:"(inv\<^bsub>Q\<^sub>p\<^esub> (\<iota> b)) = frac \<one>\<^bsub>Z\<^sub>p\<^esub> b" 
    by (simp add: B Q\<^sub>p_def Zp.nonzero_one_closed assms(2) frac_inv local.inc_def)
  have P1: "(frac a b) = (\<iota> a) \<otimes> (frac \<one>\<^bsub>Z\<^sub>p\<^esub> b)"
    by (simp add: assms(1) assms(2) i_mult)    
  show ?thesis 
    by (simp add: P0 P1)
qed

lemma frac_eq:
  assumes "a \<in> nonzero Z\<^sub>p"
  assumes "b \<in> nonzero Z\<^sub>p"
  assumes "frac a b = \<one>"
  shows "a = b"
proof-
  have "frac a b = frac b b"
    by (simp add: assms(2) assms(3) frac_one)
  then have "frac a \<one>\<^bsub>Z\<^sub>p\<^esub> = frac b \<one>\<^bsub>Z\<^sub>p\<^esub>"
    using assms 
    by (metis (no_types, lifting) Zp.nonzero_closed 
        Zp.nonzero_one_closed frac_eqE frac_eqI')
  then show ?thesis
    using \<iota>_def assms(1) assms(2) inc_inj2 local.inc_def 
    by (simp add: Zp.nonzero_closed)
qed

lemma fract_cancel_right:
  assumes "a \<in> carrier Q\<^sub>p"
  assumes "b \<in> nonzero Q\<^sub>p"
  shows "b \<otimes> (a \<div> b) = a"
  by (simp add: Qp.Units_closed Qp.m_lcomm Units_eq_nonzero assms(1)
      assms(2))
  
lemma fract_cancel_left:
  assumes "a \<in> carrier Q\<^sub>p"
  assumes "b \<in> nonzero Q\<^sub>p"
  shows "(a \<div> b) \<otimes> b = a"
  by (simp add: Qp.m_comm Qp.nonzero_closed assms(1) assms(2) 
      local.fract_cancel_right nonzero_inverse_Qp)
  
lemma fract_mult:
  assumes "a \<in> carrier Q\<^sub>p"
  assumes "b \<in> nonzero Q\<^sub>p"
  assumes "c \<in> carrier Q\<^sub>p"
  assumes "d \<in> nonzero Q\<^sub>p"
  shows  "(a \<div> b) \<otimes> (c \<div> d) = ((a \<otimes> c)\<div> (b \<otimes> d))"
  using Q\<^sub>p_def assms(1) assms(2) assms(3) assms(4) 
  by (simp add: fract_mult)
  
lemma Qp_nat_pow_nonzero:
  assumes "x \<in> nonzero Q\<^sub>p"
  shows "x[^](n::nat) \<in> nonzero Q\<^sub>p"
  using Qp.Units_pow_closed Units_eq_nonzero assms by auto

lemma Qp_nonzero_nat_pow:
  assumes "x \<in> carrier Q\<^sub>p"
  assumes "n > 0"
  assumes "x[^](n::nat) \<in> nonzero Q\<^sub>p"
  shows "x \<in> nonzero Q\<^sub>p"
  using Frac_nonzero_nat_pow Q\<^sub>p_def assms(1) assms(2) assms(3) by blast
  
lemma Qp_int_pow_nonzero:
  assumes "x \<in> nonzero Q\<^sub>p"
  shows "x[^](n::int) \<in> nonzero Q\<^sub>p"
  using Frac_int_pow_nonzero Q\<^sub>p_def assms by blast

lemma Qp_nonzero_int_pow:
  assumes "x \<in> carrier Q\<^sub>p"
  assumes "n > 0"
  assumes "x[^](n::int) \<in> nonzero Q\<^sub>p"
  shows "x \<in> nonzero Q\<^sub>p"
  using Frac_nonzero_int_pow Q\<^sub>p_def assms 
  by auto 

lemma pow_p_frac_0:
  assumes "(m::int) \<ge> n"
  assumes "n \<ge>0"
  shows "(frac (\<p>[^]\<^bsub>Z\<^sub>p\<^esub>m) (\<p>[^]\<^bsub>Z\<^sub>p\<^esub>n)) = \<iota> (\<p>[^]\<^bsub>Z\<^sub>p\<^esub>(m-n))"
proof-
  have 0: "\<p>\<in>carrier Z\<^sub>p" 
    by (simp add: Zp.nat_inc_closed) 
  have 1: "m - n \<ge>0" 
    using assms(1) by auto 
  have 2: "nat (m - n) + (nat n) = nat m" 
    using "1" assms(2) by linarith 
  have 3: "m \<ge>0" 
    using assms by auto
  then have "(\<p>[^]\<^bsub>Z\<^sub>p\<^esub>(nat (m-n))) \<otimes>\<^bsub>Z\<^sub>p\<^esub> (\<p>[^]\<^bsub>Z\<^sub>p\<^esub>(nat n)) = (\<p>[^]\<^bsub>Z\<^sub>p\<^esub>(nat m))" 
    by (simp add: "2" p_natpow_prod)
  then have "(\<p>[^]\<^bsub>Z\<^sub>p\<^esub>(m-n)) \<otimes>\<^bsub>Z\<^sub>p\<^esub> (\<p>[^]\<^bsub>Z\<^sub>p\<^esub>n) = (\<p>[^]\<^bsub>Z\<^sub>p\<^esub>m)" 
    using int_pow_int 1 3 assms(2) int_nat_eq by metis  
  then have P0: "(frac (\<p>[^]\<^bsub>Z\<^sub>p\<^esub>m) (\<p>[^]\<^bsub>Z\<^sub>p\<^esub>n)) = frac ((\<p>[^]\<^bsub>Z\<^sub>p\<^esub>(m-n))\<otimes>\<^bsub>Z\<^sub>p\<^esub> (\<p>[^]\<^bsub>Z\<^sub>p\<^esub>n)) (\<p>[^]\<^bsub>Z\<^sub>p\<^esub>n)"
    by simp 
  have "\<p> \<in>carrier Z\<^sub>p" 
    by (simp add: "0") 
  have "(\<p>[^]\<^bsub>Z\<^sub>p\<^esub>(nat n)) = [(p^(nat n))] \<cdot>\<^bsub>Z\<^sub>p\<^esub> \<one>\<^bsub>Z\<^sub>p\<^esub>"
    by (simp add: p_pow_rep0) 
  then have "(\<p>[^]\<^bsub>Z\<^sub>p\<^esub>(nat n)) \<in> carrier Z\<^sub>p" 
    by (simp add: Zp_nat_inc_closed) 
  then have "(\<p>[^]\<^bsub>Z\<^sub>p\<^esub>n) \<in> carrier Z\<^sub>p" 
    using assms(2) by (metis int_nat_eq int_pow_int) 
  then have P1: "(frac (\<p>[^]\<^bsub>Z\<^sub>p\<^esub>m) (\<p>[^]\<^bsub>Z\<^sub>p\<^esub>n)) = frac ((\<p>[^]\<^bsub>Z\<^sub>p\<^esub>(m-n))\<otimes>\<^bsub>Z\<^sub>p\<^esub> (\<p>[^]\<^bsub>Z\<^sub>p\<^esub>n)) ((\<one>\<^bsub>Z\<^sub>p\<^esub> \<otimes>\<^bsub>Z\<^sub>p\<^esub> (\<p>[^]\<^bsub>Z\<^sub>p\<^esub>n)))"
    by (simp add: \<open>[p] \<cdot>\<^bsub>Z\<^sub>p\<^esub> \<one>\<^bsub>Z\<^sub>p\<^esub> [^]\<^bsub>Z\<^sub>p\<^esub> (m - n) \<otimes>\<^bsub>Z\<^sub>p\<^esub> [p] \<cdot>\<^bsub>Z\<^sub>p\<^esub> \<one>\<^bsub>Z\<^sub>p\<^esub> [^]\<^bsub>Z\<^sub>p\<^esub> n = [p] \<cdot>\<^bsub>Z\<^sub>p\<^esub> \<one>\<^bsub>Z\<^sub>p\<^esub> [^]\<^bsub>Z\<^sub>p\<^esub> m\<close>)  
  have P2: "(\<p>[^]\<^bsub>Z\<^sub>p\<^esub>(m-n)) \<in> carrier Z\<^sub>p" 
    using "1" p_pow_car by blast 
  have P3: "(\<p>[^]\<^bsub>Z\<^sub>p\<^esub>n) \<in> carrier Z\<^sub>p" 
    using \<open>\<p> [^]\<^bsub>Z\<^sub>p\<^esub> n \<in> carrier Z\<^sub>p\<close>
    by blast 
  have P4: "(\<p>[^]\<^bsub>Z\<^sub>p\<^esub>n) \<in> nonzero Z\<^sub>p" 
    using assms(2) p_int_pow_nonzero 
    by blast 
  have P5: "\<one>\<^bsub>Z\<^sub>p\<^esub> \<in> nonzero Z\<^sub>p" 
    using nonzero_def 
    by (simp add: Zp.nonzero_one_closed)   
  have "(frac (\<p>[^]\<^bsub>Z\<^sub>p\<^esub>(m-n)) \<one>\<^bsub>Z\<^sub>p\<^esub>) \<otimes> (frac (\<p>[^]\<^bsub>Z\<^sub>p\<^esub>n) (\<p>[^]\<^bsub>Z\<^sub>p\<^esub>n)) 
        = frac ((\<p>[^]\<^bsub>Z\<^sub>p\<^esub>(m-n))\<otimes>\<^bsub>Z\<^sub>p\<^esub> (\<p>[^]\<^bsub>Z\<^sub>p\<^esub>n)) ((\<one>\<^bsub>Z\<^sub>p\<^esub> \<otimes>\<^bsub>Z\<^sub>p\<^esub> (\<p>[^]\<^bsub>Z\<^sub>p\<^esub>n)))"
    by (simp add: P2 P3 P4 Zp.nonzero_one_closed local.frac_mult)    
  then have "frac ((\<p>[^]\<^bsub>Z\<^sub>p\<^esub>(m-n))\<otimes>\<^bsub>Z\<^sub>p\<^esub> (\<p>[^]\<^bsub>Z\<^sub>p\<^esub>n)) ((\<one>\<^bsub>Z\<^sub>p\<^esub> \<otimes>\<^bsub>Z\<^sub>p\<^esub> (\<p>[^]\<^bsub>Z\<^sub>p\<^esub>n))) = (frac (\<p>[^]\<^bsub>Z\<^sub>p\<^esub>(m-n)) \<one>\<^bsub>Z\<^sub>p\<^esub>) "
    by (simp add: P2 P4 Zp.nonzero_one_closed frac_cancel_lr mult_comm)  
  then have P6: "(frac (\<p>[^]\<^bsub>Z\<^sub>p\<^esub>m) (\<p>[^]\<^bsub>Z\<^sub>p\<^esub>n)) = (frac (\<p>[^]\<^bsub>Z\<^sub>p\<^esub>(m-n)) \<one>\<^bsub>Z\<^sub>p\<^esub>) " 
    using P1 by blast 
  have "(frac (\<p>[^]\<^bsub>Z\<^sub>p\<^esub>(m-n)) \<one>\<^bsub>Z\<^sub>p\<^esub>) = \<iota> (\<p>[^]\<^bsub>Z\<^sub>p\<^esub>(m-n))" 
    using inc_def  by (simp add: P2) 
  then show ?thesis 
    using P6 by blast
qed

lemma pow_p_frac:
  assumes "(m::int) \<le> n"
  assumes "m \<ge>0"
  shows "(frac (\<p>[^]\<^bsub>Z\<^sub>p\<^esub>m) (\<p>[^]\<^bsub>Z\<^sub>p\<^esub>n)) = frac \<one>\<^bsub>Z\<^sub>p\<^esub> (\<p>[^]\<^bsub>Z\<^sub>p\<^esub>(n-m))"
proof-
  have "(frac (\<p>[^]\<^bsub>Z\<^sub>p\<^esub>n) (\<p>[^]\<^bsub>Z\<^sub>p\<^esub>m)) = \<iota> (\<p>[^]\<^bsub>Z\<^sub>p\<^esub>(n-m))" 
    by (simp add: assms(1) assms(2) pow_p_frac_0) 
  then have P0:"(frac (\<p>[^]\<^bsub>Z\<^sub>p\<^esub>n) (\<p>[^]\<^bsub>Z\<^sub>p\<^esub>m)) = frac (\<p>[^]\<^bsub>Z\<^sub>p\<^esub>(n-m)) \<one>\<^bsub>Z\<^sub>p\<^esub>"
   by (simp add: assms(1) local.inc_def p_pow_car)   
  have P1: "\<one>\<^bsub>Z\<^sub>p\<^esub> \<in>nonzero Z\<^sub>p" 
    by (simp add: Zp.nonzero_one_closed)
  have P2: "\<p>[^]\<^bsub>Z\<^sub>p\<^esub>n \<in> nonzero Z\<^sub>p"
    using assms(1) assms(2) p_int_pow_nonzero by auto
  have P3: "\<p>[^]\<^bsub>Z\<^sub>p\<^esub>m \<in> nonzero Z\<^sub>p" 
    by (simp add: assms(2) p_int_pow_nonzero)    
  have P4: "(\<p>[^]\<^bsub>Z\<^sub>p\<^esub>(n-m)) \<in> nonzero Z\<^sub>p" 
    by (simp add: assms(1) p_int_pow_nonzero)
  show " frac (\<p>[^]\<^bsub>Z\<^sub>p\<^esub>m) (\<p>[^]\<^bsub>Z\<^sub>p\<^esub>n) = frac \<one>\<^bsub>Z\<^sub>p\<^esub> (\<p>[^]\<^bsub>Z\<^sub>p\<^esub>(n-m))"
    using P0 P1 P2 P3 P4 p_pow_nonzero 
    by (meson local.frac_inv_id)   
qed

text\<open>The copy of the prime \<open>p\<close> living in $\mathbb{Q}_p$:\<close>

abbreviation \<pp> where
"\<pp> \<equiv> [p] \<cdot>\<^bsub>Q\<^sub>p\<^esub> \<one>"

lemma(in domain_frac) frac_inc_of_nat:
"Frac_inc R ([(n::nat)]\<cdot> \<one>) = [n]\<cdot>\<^bsub>Frac R\<^esub>\<one>\<^bsub>Frac R\<^esub>"
  by (simp add: inc_equation nat_inc_rep)

lemma inc_of_nat:
"(\<iota> ([(n::nat)]\<cdot>\<^bsub>Z\<^sub>p\<^esub> \<one>\<^bsub>Z\<^sub>p\<^esub>)) = [n]\<cdot>\<^bsub>Q\<^sub>p\<^esub>\<one>"
  unfolding Q\<^sub>p_def \<iota>_def
  using  frac_inc_of_nat[of n]
  by auto 
  
lemma(in domain_frac) frac_inc_of_int:
"Frac_inc R ([(n::int)]\<cdot> \<one>) = [n]\<cdot>\<^bsub>Frac R\<^esub>\<one>\<^bsub>Frac R\<^esub>"
  apply(induction n)
  apply (simp add: add_pow_int_ge inc_equation nat_inc_rep)
    by (simp add: add_pow_int_lt frac_uminus inc_equation nat_inc_rep nonzero_one_closed)

lemma inc_of_int:
"(\<iota> ([(n::int)]\<cdot>\<^bsub>Z\<^sub>p\<^esub> \<one>\<^bsub>Z\<^sub>p\<^esub>)) = [n]\<cdot>\<^bsub>Q\<^sub>p\<^esub>\<one>"
  unfolding Q\<^sub>p_def \<iota>_def
  using  frac_inc_of_int[of n]
  by auto 
  
lemma p_inc:
"\<pp> = \<iota> \<p>"
  by (simp add: inc_of_int)

lemma p_nonzero:
"\<pp> \<in> nonzero Q\<^sub>p"
  using Z\<^sub>p_def Zp_nat_inc_closed inc_of_nonzero ord_Zp_p p_inc 
    p_nonzero by auto
 
lemma p_natpow_inc:
  fixes n::nat
  shows "\<pp>[^]n = \<iota> (\<p> [^]\<^bsub>Z\<^sub>p\<^esub> n)"
  by (simp add: Qp.int_nat_pow_rep inc_of_int p_pow_rep0)

lemma p_intpow_inc:
  fixes n::int
  assumes "n \<ge>0"
  shows "\<pp>[^]n = \<iota> (\<p> [^]\<^bsub>Z\<^sub>p\<^esub> n)"
  using p_natpow_inc  
  by (metis assms int_nat_eq int_pow_int)

lemma p_intpow:
  fixes n::int
  assumes "n < 0"
  shows "\<pp>[^]n = (frac \<one>\<^bsub>Z\<^sub>p\<^esub> (\<p> [^]\<^bsub>Z\<^sub>p\<^esub> (-n)))"
proof-
  have U0: "(\<pp> [^] (nat (-n))) \<in> Units Q\<^sub>p" 
    using Qp.Units_pow_closed Units_eq_nonzero p_nonzero by blast   
  have E0: "(\<pp> [^] (nat (-n))) = (\<pp> [^] (-n))" 
    using assms  by (simp add: int_pow_def nat_pow_def)
  then have U1: "(\<pp> [^]  (-n)) \<in> Units Q\<^sub>p" using U0 
    by simp
  have "(\<pp>[^]n) = inv \<^bsub>Q\<^sub>p\<^esub> (\<pp> [^] (nat (-n)))"
    using assms by (simp add: int_pow_def nat_pow_def)
  then have "(\<pp>[^]n) = inv \<^bsub>Q\<^sub>p\<^esub> (\<pp> [^] (-n))" 
    using E0 by simp
  then have "(\<pp>[^]n) = inv \<^bsub>Q\<^sub>p\<^esub> \<iota> (\<p> [^]\<^bsub>Z\<^sub>p\<^esub>(-n))" 
    using assms p_intpow_inc by auto
  then have E1: "(\<pp>[^]n) = inv \<^bsub>Q\<^sub>p\<^esub>  frac (\<p> [^]\<^bsub>Z\<^sub>p\<^esub>(-n)) \<one>\<^bsub>Z\<^sub>p\<^esub>"
    using assms local.inc_def p_pow_car by auto
  have A: "(\<p> [^]\<^bsub>Z\<^sub>p\<^esub>(-n)) \<in> nonzero Z\<^sub>p"
    using assms p_pow_nonzero  p_int_pow_nonzero 
    by auto 
  then show ?thesis 
    using A frac_inv inc_def E1 
    by (simp add: Q\<^sub>p_def Zp.nonzero_one_closed)
qed

lemma p_natpow_closed[simp]:
  fixes n::nat
  shows "(\<pp>[^]n) \<in> (carrier Q\<^sub>p)"
        "(\<pp>[^]n) \<in> (nonzero Q\<^sub>p)"
  apply blast 
    using Qp_nat_pow_nonzero p_nonzero by blast
  
lemma nonzero_int_pow_distrib:
  assumes "a \<in> nonzero Q\<^sub>p"
  assumes "b \<in> nonzero Q\<^sub>p"
  shows "(a \<otimes> b) [^](k::int) = a[^]k \<otimes> b[^]k"
proof(induction k)
  case (nonneg n)
  then show ?case using pow_nat[of n _ Q\<^sub>p] 
    by (smt Qp.nat_pow_distrib Qp.nonzero_closed assms(1) assms(2) int_pow_int)
next
  case N: (neg n)
  have "a \<otimes> b \<in> Units Q\<^sub>p"
    using assms Units_eq_nonzero by blast  
  hence "(a \<otimes> b) [^] - int (Suc n) = inv ((a \<otimes> b) [^] (Suc n))"
     by (metis Qp.int_pow_inv' int_pow_int)
   then show ?case using 
       Qp.int_pow_inv' Qp.int_pow_unit_closed Qp.inv_of_prod[of "a[^]Suc n" "b[^]Suc n"] 
       Qp.nat_pow_distrib Qp.nonzero_closed Units_eq_nonzero assms(1) assms(2) int_pow_int  by metis
qed

lemma val_ring_subring:
"subring \<O>\<^sub>p Q\<^sub>p"
  using Q\<^sub>p_def \<iota>_def inc_im_is_subring by blast

lemma val_ring_closed: 
"\<O>\<^sub>p \<subseteq> carrier Q\<^sub>p"      
  by (simp add: subringE(1) val_ring_subring)

lemma p_pow_diff: 
  fixes n::int 
  fixes m::int 
  assumes "n \<ge>0"
  assumes "m \<ge>0"
  shows "\<pp> [^] (n - m) = frac (\<p>[^]\<^bsub>Z\<^sub>p\<^esub>n) (\<p>[^]\<^bsub>Z\<^sub>p\<^esub>m)"
proof-
  have 0: "comm_monoid Q\<^sub>p"
    by (simp add: Qp.comm_monoid_axioms)
  have 1: "\<pp> \<in> Units Q\<^sub>p"
    using Units_eq_nonzero p_nonzero 
    by blast
  have 2: "\<pp> [^] (n - m) = (\<pp>[^]n) \<otimes> (\<pp> [^] -m)"
    by (metis "1" Qp.int_pow_add diff_conv_add_uminus)    
  have 3: "\<pp> [^] (n - m) = (\<pp>[^]n) \<otimes> inv\<^bsub>Q\<^sub>p\<^esub>(\<pp> [^] m)"
    by (simp add: "1" "2" Qp.int_pow_inv')  
  then show ?thesis using assms 
    using fract_frac p_int_pow_nonzero p_intpow_inc p_pow_car by presburger
qed

lemma Qp_int_pow_add: 
  fixes n::int 
  fixes m::int
  assumes "a \<in> nonzero Q\<^sub>p"
  shows "a [^] (n + m) = (a [^] n) \<otimes> (a [^] m)"
  using monoid.int_pow_add[of Q\<^sub>p a n m] Units_eq_nonzero assms 
  by (simp add: Qp.monoid_axioms)
  
lemma Qp_nat_pow_pow: 
  fixes n::nat 
  fixes m::nat
  assumes "a \<in> carrier Q\<^sub>p"
  shows "(a[^](n*m)) = ((a[^]n)[^]m)"
  by (simp add: Qp.nat_pow_pow assms)
  
lemma Qp_p_nat_pow_pow: 
  fixes n::nat 
  fixes m::nat
  shows "(\<pp> [^] (n*m)) = ((\<pp>[^]n)[^]m)"
  using Qp_nat_pow_pow 
  by simp
  
lemma Qp_units_int_pow:
  fixes n::int
  assumes "a \<in> nonzero Q\<^sub>p"
  shows "a[^]n = a[^]\<^bsub>units_of Q\<^sub>p\<^esub>n"
  apply(cases "n \<ge> 0")
  using monoid.units_of_pow[of Q\<^sub>p]
   apply (metis int_pow_def2 mult_of_is_Units nat_pow_mult_of not_le)
    by (metis Qp.Units_pow_closed Qp.units_of_inv Units_eq_nonzero assms int_pow_def2 mult_of_is_Units nat_pow_mult_of)
 
lemma Qp_int_pow_pow: 
  fixes n::int
  fixes m::int
  assumes "a \<in> nonzero Q\<^sub>p"
  shows "(a[^](n*m)) = ((a[^]n)[^]m)"
proof-
  have 0: "a \<in> carrier (units_of Q\<^sub>p)"
    by (simp add: Units_eq_nonzero assms units_of_carrier)
  have "group (units_of Q\<^sub>p)"
    using  monoid.units_group Qp.units_group 
    by blast 
  then show ?thesis 
    using 0 group.int_pow_pow[of "units_of Q\<^sub>p"] Qp_int_pow_nonzero Qp_units_int_pow assms 
    by auto
qed

lemma Qp_p_int_pow_pow: 
  fixes n::int
  fixes m::int
  shows "(\<pp> [^] (n*m)) = ((\<pp>[^]n)[^]m)"
  using Qp_int_pow_pow p_nonzero by blast
  
lemma Qp_int_nat_pow_pow: 
  fixes n::int
  fixes m::nat
  assumes "a \<in> nonzero Q\<^sub>p"
  shows "(a[^](n*m)) = ((a[^]n)[^]m)"
  by (simp add: Qp_int_pow_pow assms int_pow_int)

lemma Qp_p_int_nat_pow_pow: 
  fixes n::int
  fixes m::nat
  shows "(\<pp> [^] (n*m)) = ((\<pp>[^]n)[^]m)"
  by (simp add: Qp_int_nat_pow_pow p_nonzero)

lemma Qp_nat_int_pow_pow: 
  fixes n::nat
  fixes m::int
  assumes "a \<in> nonzero Q\<^sub>p"
  shows "(a[^](n*m)) = ((a[^]n)[^]m)"
  by (simp add: Qp_int_pow_pow assms int_pow_int)

lemma Qp_p_nat_int_pow_pow: 
  fixes n::nat
  fixes m::int
  shows "(\<pp> [^] (n*m)) = ((\<pp>[^]n)[^]m)"
  by (simp add: Qp_nat_int_pow_pow p_nonzero)

lemma p_intpow_closed:
  fixes n::int
  shows "(\<pp>[^]n) \<in> (carrier Q\<^sub>p)"
        "(\<pp>[^]n) \<in> (nonzero Q\<^sub>p)"
  apply (simp add: Qp.nonzero_closed Qp_int_pow_nonzero p_nonzero)
    by (simp add: Qp_int_pow_nonzero p_nonzero)
  
lemma p_intpow_add:
  fixes n::int 
  fixes m::int
  shows "\<pp> [^] (n + m) = (\<pp> [^] n) \<otimes> (\<pp> [^] m)"
  using Qp_int_pow_add p_nonzero by blast

lemma p_intpow_inv:
  fixes n::int
  shows  "(\<pp> [^] n) \<otimes> (\<pp> [^] -n) = \<one>"
  using Units_eq_nonzero monoid.int_pow_inv'[of Q\<^sub>p \<pp> n] 
  by (metis add.right_inverse int_pow_0 p_intpow_add)
    
lemma p_intpow_inv':
  fixes n::int
  shows  "(\<pp> [^] -n) \<otimes> (\<pp> [^] n) = \<one>"
  using p_intpow_inv 
  by (metis add.commute p_intpow_add)

lemma p_intpow_inv'':
  fixes n::int
  shows "(\<pp> [^] -n) = inv\<^bsub>Q\<^sub>p\<^esub> (\<pp> [^] n)"
  by (simp add: Qp.int_pow_inv' Units_eq_nonzero p_nonzero)

lemma p_int_pow_factor_int_pow:
  assumes "a \<in> nonzero Q\<^sub>p"
  shows "(\<pp>[^](n::int) \<otimes> a)[^](k::int) = \<pp>[^](n*k) \<otimes> a[^]k"
  using assms nonzero_int_pow_distrib p_intpow_closed(2) Qp_p_int_pow_pow by presburger

lemma p_nat_pow_factor_int_pow:
  assumes "a \<in> nonzero Q\<^sub>p"
  shows "(\<pp>[^](n::nat) \<otimes> a)[^](k::int) = \<pp>[^](n*k) \<otimes> a[^]k"
  using assms  Qp_p_int_nat_pow_pow p_natpow_closed(1) 
  by (metis int_pow_int p_int_pow_factor_int_pow)

lemma p_pow_factor:
"\<pp>[^]((int N)*l  + k) = (\<pp>[^]l)[^](N::nat) \<otimes> \<pp>[^] k"
  by (metis Qp_p_int_nat_pow_pow mult_of_nat_commute p_intpow_add)

lemma p_nat_pow_factor_nat_pow:
  assumes "a \<in> carrier Q\<^sub>p"
  shows "(\<pp>[^](n::nat) \<otimes> a)[^](k::nat) = \<pp>[^](n*k) \<otimes> a[^]k"
  using Qp.nat_pow_distrib Qp_p_nat_pow_pow assms p_natpow_closed(1) by presburger

lemma p_int_pow_factor_nat_pow:
  assumes "a \<in> carrier Q\<^sub>p"
  shows "(\<pp>[^](n::int) \<otimes> a)[^](k::nat) = \<pp>[^](n*k) \<otimes> a[^]k"
  using assms Qp.nat_pow_distrib Qp_p_int_nat_pow_pow p_intpow_closed(1) by presburger

lemma(in ring) r_minus_distr:
  assumes "a \<in> carrier R"
  assumes "b \<in> carrier R"
  assumes "c \<in> carrier R"
  shows "a \<otimes> b \<ominus> a \<otimes> c = a \<otimes> (b \<ominus> c)"
  using assms 
  unfolding a_minus_def  
  by (simp add: r_distr r_minus)


(**************************************************************************************************)
(**************************************************************************************************)
subsection\<open>The Valuation on $\mathbb{Q}_p$\<close>
(**************************************************************************************************)
(**************************************************************************************************)

      (********************************************************************************************)
      (********************************************************************************************)
      subsubsection\<open>Extending the Valuation from $\mathbb{Z}_p$ to $\mathbb{Q}_p$\<close>
      (********************************************************************************************)
      (********************************************************************************************)

text\<open>
  The valuation of a $p$-adic number can be defined as the difference of the valuations of an
  arbitrary choice of numerator and denominator.\<close>
definition ord where
"ord x = (ord_Zp (numer x)) - (ord_Zp (denom x))"

definition val where
"val x = (if x = \<zero> then (\<infinity>::eint) else eint (ord x))"

lemma val_ord[simp]:
  assumes "a \<in> nonzero Q\<^sub>p"
  shows "val a = ord a"
  using assms nonzero_def val_def by force

      (********************************************************************************************)
      (********************************************************************************************)
      subsubsection\<open>Properties of the Valuation\<close>
      (********************************************************************************************)
      (********************************************************************************************)

lemma ord_of_frac:
  assumes "a \<in> nonzero Z\<^sub>p"
  assumes "b \<in> nonzero Z\<^sub>p"
  shows "ord (frac a b) = (ord_Zp a) - (ord_Zp b)"
proof-
  have "frac a b = frac (numer (frac a b)) (denom (frac a b))"
    by (simp add: assms(1) assms(2))
  then have "a \<otimes>\<^bsub>Z\<^sub>p\<^esub> (denom (frac a b)) = b \<otimes>\<^bsub>Z\<^sub>p\<^esub> (numer (frac a b))"
    by (simp add: assms(1) assms(2) numer_denom_swap)   
  then have "(ord_Zp a) - (ord_Zp b) =  (ord_Zp (numer (frac a b))) - (ord_Zp (denom (frac a b)))"
    using ord_Zp_eq_frac Q\<^sub>p_def Z\<^sub>p_def 
    by (metis Zp.frac_closed Zp.nonzero_closed Zp.numer_denom_facts(4) assms(1) assms(2) local.numer_denom_facts(1) local.numer_denom_facts(2) nonzero_fraction ord_of_nonzero(2) ord_pos) 
  then show ?thesis 
    using ord_def 
    by presburger
qed

lemma val_zero:
"val \<zero> = \<infinity>" by (simp add: val_def)

lemma ord_one[simp]:
"ord \<one> = 0"
  using Zp.nonzero_one_closed local.frac_one ord_of_frac by fastforce
  
lemma val_one[simp]:
"val (\<one>) = 0"
  using ord_one 
  by (simp add: Qp.one_nonzero zero_eint_def)      
  
lemma val_of_frac:
  assumes "a \<in> carrier Z\<^sub>p"
  assumes "b \<in> nonzero Z\<^sub>p"
  shows "val (frac a b) = (val_Zp a) - (val_Zp b)"
proof(cases "a = \<zero>\<^bsub>Z\<^sub>p\<^esub>")
  case True
  then show ?thesis 
    using assms(1) assms(2)  local.val_zero
    by (simp add: Q\<^sub>p_def val_Zp_def)
next
  case False
  then have "a \<in> nonzero Z\<^sub>p" 
    by (simp add: assms(1) nonzero_def)
  then show ?thesis
    using ord_of_frac[of a b] assms(2)  val_def val_ord_Zp 
          nonzero_numer_imp_nonzero_fraction
  by (simp add: Zp.nonzero_memE(2))
qed

lemma Z\<^sub>p_division_Qp_0[simp]:
  assumes "u \<in> Units Z\<^sub>p"
  assumes "v \<in> Units Z\<^sub>p"
  shows "frac (u \<otimes>\<^bsub>Z\<^sub>p\<^esub> (inv\<^bsub>Z\<^sub>p\<^esub> v)) \<one>\<^bsub>Z\<^sub>p\<^esub>= frac u v"
proof-  
  have 0: "frac v v = \<one>" 
    using frac_one
    by (simp add: Q\<^sub>p_def Zp.Units_nonzero assms(2))
  have 1:"(inv\<^bsub>Z\<^sub>p\<^esub> v) \<in> carrier Z\<^sub>p"
    using assms  by blast
  have 2:"frac (u \<otimes>\<^bsub>Z\<^sub>p\<^esub> (inv\<^bsub>Z\<^sub>p\<^esub> v))  \<one>\<^bsub>Z\<^sub>p\<^esub>  \<in> carrier Q\<^sub>p"
    by (simp add: "1" Zp.Units_closed Zp.nonzero_one_closed assms(1) local.frac_closed)
  have 3: "frac (u \<otimes>\<^bsub>Z\<^sub>p\<^esub> (inv\<^bsub>Z\<^sub>p\<^esub> v)) \<one>\<^bsub>Z\<^sub>p\<^esub> =  (frac (u \<otimes>\<^bsub>Z\<^sub>p\<^esub> (inv\<^bsub>Z\<^sub>p\<^esub> v)) \<one>\<^bsub>Z\<^sub>p\<^esub>) \<otimes> frac v v"
    by (simp add: "0" "2")
  then have 4:  "frac (u \<otimes>\<^bsub>Z\<^sub>p\<^esub> (inv\<^bsub>Z\<^sub>p\<^esub> v)) \<one>\<^bsub>Z\<^sub>p\<^esub> =  (frac ((u \<otimes>\<^bsub>Z\<^sub>p\<^esub> (inv\<^bsub>Z\<^sub>p\<^esub> v)) \<otimes>\<^bsub>Z\<^sub>p\<^esub> v)  v)"
    by (simp add: Zp.Units_nonzero Zp.nonzero_closed assms(1) assms(2) frac_eqI') 
  then have 4:  "frac (u \<otimes>\<^bsub>Z\<^sub>p\<^esub> (inv\<^bsub>Z\<^sub>p\<^esub> v)) \<one>\<^bsub>Z\<^sub>p\<^esub> =  (frac (u \<otimes>\<^bsub>Z\<^sub>p\<^esub> ((inv\<^bsub>Z\<^sub>p\<^esub> v) \<otimes>\<^bsub>Z\<^sub>p\<^esub> v))  v)"
    by (simp add: mult_assoc) 
  have 5:"(inv\<^bsub>Z\<^sub>p\<^esub> v) \<otimes>\<^bsub>Z\<^sub>p\<^esub> v = \<one>\<^bsub>Z\<^sub>p\<^esub>"
    by (simp add: assms(2))
  then show  "frac (u \<otimes>\<^bsub>Z\<^sub>p\<^esub> (inv\<^bsub>Z\<^sub>p\<^esub> v)) \<one>\<^bsub>Z\<^sub>p\<^esub> =  (frac u  v)"
    by (simp add: "4" Zp.Units_closed assms(1))
qed

lemma Z\<^sub>p_division_Qp_1:
  assumes "u \<in> Units Z\<^sub>p"
  assumes "v \<in> Units Z\<^sub>p"
  obtains w where "w \<in> Units Z\<^sub>p"
                  "\<iota> w = frac u v"
proof-
  have " (inv\<^bsub>Z\<^sub>p\<^esub> v) \<in> Units Z\<^sub>p" 
    by (simp add: assms(2))
  then have "(u \<otimes>\<^bsub>Z\<^sub>p\<^esub> (inv\<^bsub>Z\<^sub>p\<^esub> v)) \<in> Units Z\<^sub>p" 
    using assms 
    by blast     
  then show ?thesis 
    using  Z\<^sub>p_division_Qp_0  Zp.Units_closed assms(1) assms(2) 
      local.inc_def that by presburger
qed

lemma val_ring_ord_criterion:
  assumes "a \<in> carrier Q\<^sub>p"
  assumes "a \<noteq> \<zero>"
  assumes "ord a \<ge> 0"
  shows "a \<in> \<O>\<^sub>p"
proof-
  obtain c d where P0: "a = frac c d" and P1: "c \<in> nonzero Z\<^sub>p" and P2: "d \<in> nonzero Z\<^sub>p"
   by (metis assms(1) assms(2) get_common_denominator nonzero_fraction_imp_nonzero_numer)  
  obtain m n where P3: "m = ord_Zp c" and P4:"n = ord_Zp d"
    by metis 
  obtain u where "u = ac_Zp c" 
    by simp
  then have P5:"c = (\<p>[^]\<^bsub>Z\<^sub>p\<^esub>m) \<otimes>\<^bsub>Z\<^sub>p\<^esub> u" and P6:"u \<in> Units Z\<^sub>p"
     apply (simp add: P1 P3 \<open>u = ac_Zp c\<close> ac_Zp_factors')
     using P1 Zp.nonzero_memE 
     by (simp add: \<open>u = ac_Zp c\<close> ac_Zp_is_Unit)
  obtain v where "v = ac_Zp d" by simp
  have  P7:"d = (\<p>[^]\<^bsub>Z\<^sub>p\<^esub>n) \<otimes>\<^bsub>Z\<^sub>p\<^esub> v" and P8:"v \<in> Units Z\<^sub>p"
     using P2 P4 \<open>v = ac_Zp d\<close> ac_Zp_factors' apply blast
     using P2 Zp.nonzero_memE 
     by (simp add: \<open>v = ac_Zp d\<close> ac_Zp_is_Unit)
  have P9: "a = frac ((\<p>[^]\<^bsub>Z\<^sub>p\<^esub>m) \<otimes>\<^bsub>Z\<^sub>p\<^esub> u) ((\<p>[^]\<^bsub>Z\<^sub>p\<^esub>n) \<otimes>\<^bsub>Z\<^sub>p\<^esub> v)"
    by (simp add: P0 P5 P7)
  have P10: "(\<p>[^]\<^bsub>Z\<^sub>p\<^esub>m) \<in> carrier Z\<^sub>p"
    using P1 P3 Z\<^sub>p_def ord_pos Zp.nonzero_closed Zp.nonzero_memE(2) p_pow_car
    by auto
  have P11: "(\<p>[^]\<^bsub>Z\<^sub>p\<^esub>n) \<in> nonzero Z\<^sub>p" 
    by (simp add: P2 P4 Zp.nonzero_closed Zp.nonzero_memE(2) ord_pos p_int_pow_nonzero)
  have P12: "u \<in> carrier Z\<^sub>p"
    using P6 Units_def 
    by blast
  have P13: "v \<in> nonzero Z\<^sub>p"
    using P8 Units_def ord_of_nonzero(2) 
    by (simp add: Zp.Units_nonzero)    
  have P14: "a = (frac (\<p>[^]\<^bsub>Z\<^sub>p\<^esub>m) (\<p>[^]\<^bsub>Z\<^sub>p\<^esub>n)) \<otimes> (frac u v)"
    using P12 P13 P10 P9 P11 Q\<^sub>p_def  frac_mult by metis 
  have P15: "m \<ge> n" 
  proof-
    have "ord_Zp c \<ge> ord_Zp d" 
      using P0 P1 P2 assms(3) ord_of_frac[of c d] 
      by (metis P3 P4 antisym eq_iff eq_iff_diff_eq_0 le_cases le_iff_diff_le_0 ord_Zp_def) 
    then show ?thesis 
      using P3 P4 by blast
  qed
  have P16: "n \<ge> 0" 
    by (simp add: P2 P4 Zp.nonzero_closed Zp.nonzero_memE(2) ord_pos)
  have P17: "a = (frac (\<p>[^]\<^bsub>Z\<^sub>p\<^esub>(m-n)) \<one>\<^bsub>Z\<^sub>p\<^esub>) \<otimes> (frac u v)" 
    using P14 P15 P16 local.inc_def[of "(\<p> [^]\<^bsub>Z\<^sub>p\<^esub> (n - m))"] pow_p_frac_0[of n m] 
    by (simp add: local.inc_def p_pow_car)    
  obtain w where P18: "w \<in> Units Z\<^sub>p" and P19: "\<iota> w = frac u v "
    using  Z\<^sub>p_division_Qp_1 P6 P8 by blast
  have P20: "w \<in> carrier Z\<^sub>p" 
    using P18 Units_def by blast
  have P21:  "a = \<iota> (\<p>[^]\<^bsub>Z\<^sub>p\<^esub>(m-n)) \<otimes> \<iota> w" 
    using P15 P17 P19 \<iota>_def inc_equation p_pow_car by auto    
  have P22:  "a = (frac (\<p>[^]\<^bsub>Z\<^sub>p\<^esub>(m-n)) \<one>\<^bsub>Z\<^sub>p\<^esub>) \<otimes> (frac w \<one>\<^bsub>Z\<^sub>p\<^esub>)" 
    using P17 P19 P20 local.inc_def by auto
  have P23: "\<p>[^]\<^bsub>Z\<^sub>p\<^esub>(m-n) \<in> carrier Z\<^sub>p" 
    by (simp add: P15 p_pow_car)   
  have P24: "a = (frac ((\<p>[^]\<^bsub>Z\<^sub>p\<^esub>(m-n)) \<otimes>\<^bsub>Z\<^sub>p\<^esub> w) \<one>\<^bsub>Z\<^sub>p\<^esub>)" 
    using P20 P22 P23 frac_mult 
    by (simp add: Zp.nonzero_one_closed)
  have P24:  "a = \<iota>((\<p>[^]\<^bsub>Z\<^sub>p\<^esub>(m-n)) \<otimes>\<^bsub>Z\<^sub>p\<^esub> w)" 
    by (simp add: P20 P23 P24  cring.cring_simprules(5) domain.axioms(1) local.inc_def)
  then show ?thesis 
    using P20 P23 by blast
qed

lemma val_ring_val_criterion:
  assumes "a \<in> carrier Q\<^sub>p"
  assumes "val a \<ge> 0"
  shows "a \<in> \<O>\<^sub>p"
  apply(cases "a = \<zero>")
  using Qp.int_inc_zero Q\<^sub>p_def inc_of_int apply blast
    using assms unfolding val_def 
    by (simp add: val_ring_ord_criterion zero_eint_def)  

lemma ord_of_inv:
  assumes "a \<in> carrier Q\<^sub>p"
  assumes "a \<noteq> \<zero>"
  shows "ord (inv\<^bsub>Q\<^sub>p\<^esub> a) = - (ord a)"
proof-
  obtain b c where 
   Frac: "a = frac b c" and 
   Car: "b \<in> carrier Z\<^sub>p" and 
   Nz_c: "c \<in> nonzero Z\<^sub>p"
    using assms(1) local.numer_denom_facts(1) local.numer_denom_facts(2)
          local.numer_denom_facts(5) by blast   
    have Nz_b: "b \<in> nonzero Z\<^sub>p" 
      using Frac Car Nz_c  assms(2) nonzero_fraction_imp_nonzero_numer by metis 
    then have "(inv\<^bsub>Q\<^sub>p\<^esub> a) = frac c b" 
      using Frac Nz_c frac_inv Q\<^sub>p_def 
      by auto
    then show ?thesis using Frac Nz_b Nz_c ord_of_frac[of b c] ord_of_frac[of c b]  
      by (simp add: nonzero_def ord_Zp_def)
qed

lemma val_of_inv:
  assumes "a \<in> carrier Q\<^sub>p"
  assumes "a \<noteq> \<zero>"
  shows "val (inv\<^bsub>Q\<^sub>p\<^esub> a) = - (val a)"
  using ord_of_inv unfolding uminus_eint_def 
  by (simp add: assms(1) assms(2) inv_in_frac(2) val_def)

text\<open>Zp is a valuation ring in Qp\<close>

lemma Z\<^sub>p_mem:
  assumes "a \<in> carrier Q\<^sub>p"
  shows "a \<in> \<O>\<^sub>p \<or> (inv\<^bsub>Q\<^sub>p\<^esub> a \<in> \<O>\<^sub>p)"
proof(cases "inv\<^bsub>Q\<^sub>p\<^esub>a \<in> \<O>\<^sub>p \<or> a = \<zero>")
  case True
  then show ?thesis 
    using val_ring_subring subringE(2) by auto
next
  case False
  then have Nz: "a \<noteq> \<zero>" by auto 
  have "\<not> (ord a < 0)"
  proof
    assume "ord a < 0"
    then have "ord (inv\<^bsub>Q\<^sub>p\<^esub> a) >0" 
      by (simp add: assms(1) Nz ord_of_inv)
    then have 0: "ord (inv\<^bsub>Q\<^sub>p\<^esub> a) \<ge>0"
      by auto
    have 1: "(inv\<^bsub>Q\<^sub>p\<^esub> a) \<in> carrier Q\<^sub>p"
      by (simp add: assms(1) Nz inv_in_frac)
    have 2: "(inv\<^bsub>Q\<^sub>p\<^esub> a) \<noteq>\<zero>" 
      by (simp add: assms(1) Nz inv_in_frac(2))
    then have "(inv\<^bsub>Q\<^sub>p\<^esub> a) \<in> \<O>\<^sub>p" 
      using  val_ring_ord_criterion  by (simp add: "0" "1")
    then show False 
      using False by blast
  qed
  then show ?thesis 
    using val_ring_ord_criterion assms(1) Nz by auto
qed 

lemma Qp_val_ringI:
  assumes "a \<in> carrier Q\<^sub>p"
  assumes "val a \<ge> 0"
  shows "a \<in> \<O>\<^sub>p" 
using assms val_ring_val_criterion by blast


text\<open>Criterion for determining when an element in Qp is zero\<close>
lemma val_nonzero:
  assumes "a \<in> carrier Q\<^sub>p"
  assumes "s > val a"
  shows "a \<in> nonzero Q\<^sub>p"
proof-
  have "val a \<noteq> \<infinity>"
    by (metis assms(2) eint_ord_simps(6))    
  then show ?thesis 
    using assms 
    by (metis (mono_tags, opaque_lifting) local.val_zero  not_nonzero_Qp)
qed

lemma val_ineq:
  assumes "a \<in> carrier Q\<^sub>p"
  assumes "val \<zero> \<le> val a"
  shows "a = \<zero>"
  using assms unfolding val_def 
  by (metis (mono_tags, lifting) eint_ord_code(5))
  
lemma ord_minus:
  assumes "a \<in>  nonzero Q\<^sub>p"
  shows "ord a = ord (\<ominus>a)"
proof-
  have "\<ominus> a = \<ominus> (frac (numer a) (denom a))"
    using assms Qp.nonzero_closed local.numer_denom_facts(5) by auto    
  then have "\<ominus> a = (frac (\<ominus>\<^bsub>Z\<^sub>p\<^esub> (numer a)) (denom a))"
    by (simp add: Qp.nonzero_closed assms local.frac_uminus local.numer_denom_facts(1) local.numer_denom_facts(2))
  then show ?thesis 
    by (metis Q\<^sub>p_def Qp.add.inv_eq_1_iff Qp.nonzero_closed Zp.add.inv_closed assms 
        local.numer_denom_facts(1) local.numer_denom_facts(2) nonzero_fraction_imp_nonzero_numer 
        numer_nonzero ord_Zp_of_a_inv ord_def ord_of_frac)
qed

lemma val_minus:
  assumes "a \<in>  carrier Q\<^sub>p"
  shows "val a = val (\<ominus>a)"
proof(cases "a = \<zero>")
  case True
  then show ?thesis 
    using Qp.minus_zero by presburger  
next
  case False
  then show ?thesis using Qp.domain_axioms assms cring.cring_simprules(21)
        cring.cring_simprules(22) domain.axioms(1) not_nonzero_Qp 
        ord_minus val_def 
    by metis 
qed

text\<open>The valuation is multiplicative:\<close>

lemma ord_mult:
  assumes "x \<in> nonzero Q\<^sub>p"
  assumes "y \<in> nonzero Q\<^sub>p"
  shows "(ord (x \<otimes> y)) = (ord x) + (ord y)"
proof-
  have 0:"x \<in> carrier Q\<^sub>p" using assms by(simp add:nonzero_def)
  have 1:"y \<in>carrier Q\<^sub>p" using assms by(simp add:nonzero_def)
  obtain a b c where
   A: "a \<in> carrier Z\<^sub>p" and
   B: "b \<in> carrier Z\<^sub>p" and
   C: "c \<in> nonzero Z\<^sub>p" and
   Fx: "x = frac a c" and
   Fy: "y = frac b c" 
    using get_common_denominator 0 1 by blast
  have An: "a \<in> nonzero Z\<^sub>p"
    using A C Fx assms(1) nonzero_def nonzero_fraction_imp_nonzero_numer 
          Qp.nonzero_memE(2) by auto
  have Bn: " b \<in> nonzero Z\<^sub>p" 
    using B C Fy assms(2) nonzero_def nonzero_fraction_imp_nonzero_numer 
          Qp.nonzero_memE(2) by auto
  have Fxy: "x \<otimes> y = frac (a \<otimes>\<^bsub>Z\<^sub>p\<^esub> b) (c \<otimes>\<^bsub>Z\<^sub>p\<^esub> c)" 
    by (simp add: A B C Fx Fy frac_mult)
  have Cn: "c \<otimes>\<^bsub>Z\<^sub>p\<^esub> c \<in> nonzero Z\<^sub>p" 
    using C Localization.submonoid.m_closed Zp.domain_axioms domain.nonzero_is_submonoid 
    by metis
  have Ordxy0: "ord (x \<otimes> y) = ord_Zp (a \<otimes>\<^bsub>Z\<^sub>p\<^esub> b) - ord_Zp (c \<otimes>\<^bsub>Z\<^sub>p\<^esub> c)"
    by (metis "0" "1" An Bn C Cn Fx Fxy Fy Qp.integral
        Zp.nonzero_mult_closed Zp.zero_closed fraction_zero 
        nonzero_fraction nonzero_fraction_imp_nonzero_numer ord_of_frac)
  have Ordxy1: "ord (x \<otimes> y) = (ord_Zp a) + (ord_Zp b) - ((ord_Zp c) + (ord_Zp c))" 
    using  An Bn C 
    by (simp add: Ordxy0 ord_Zp_mult)
  show ?thesis 
  proof-
    have "ord x + ord y = (ord_Zp a) - (ord_Zp c) + ((ord_Zp b) - (ord_Zp c))"
      using An Bn C Fx Fy ord_of_frac[of a c] ord_of_frac[of b c] by presburger 
    then show ?thesis 
      using Ordxy1 
      by presburger 
  qed
qed

lemma val_mult0:
  assumes "x \<in> nonzero Q\<^sub>p"
  assumes "y \<in> nonzero Q\<^sub>p"
  shows "(val (x \<otimes> y)) = (val x) + (val y)"
proof-
  have 0: "val x = ord x" 
    using assms(1) val_ord by metis  
  have 1: "val y = ord y" 
    using assms(2) val_ord by metis   
  have "x \<otimes> y \<noteq> \<zero>"
    using field_axioms assms(1) assms(2) integral  Qp.integral_iff 
      Qp.nonzero_closed Qp.nonzero_memE(2) by presburger
  then have 2: "val (x \<otimes> y) = ord (x \<otimes> y)" 
    by (simp add:  val_def) 
  have 3: "val x + val y = ord x + ord y "
    by (simp add: "0" "1")   
  have 4: "val (x \<otimes> y) = ord  (x \<otimes> y)" 
    using "2" by auto 
  then show ?thesis using 3 4 ord_mult assms nonzero_def 
    by (simp add: nonzero_def)   
qed  

text\<open>val is multiplicative everywhere\<close>

lemma val_mult:
  assumes "x \<in> carrier Q\<^sub>p"
  assumes "y \<in> carrier Q\<^sub>p"
  shows "(val (x \<otimes> y)) = (val x) + (val y)"
  apply(cases "x = \<zero> \<or> y = \<zero>")
  using assms local.val_zero apply auto[1]
    by (meson assms(1) assms(2) not_nonzero_Qp val_mult0)

text\<open>val and ord are compatible with inclusion\<close>

lemma ord_of_inc:
assumes "x \<in> nonzero Z\<^sub>p"
shows "ord_Zp x = ord(\<iota> x)" 
proof-
  have "\<iota> x = frac x \<one>\<^bsub>Z\<^sub>p\<^esub>"
    using assms(1) 
    by (simp add: Zp.nonzero_closed local.inc_def)
  then have "ord ( \<iota> x) = ord_Zp x - ord_Zp \<one>\<^bsub>Z\<^sub>p\<^esub>"
    using assms(1) ord_of_frac 
    by (simp add: Zp.nonzero_one_closed)
  then show ?thesis
    using ord_Zp_one 
    by (simp add: ord_Zp_def)
qed

lemma val_of_inc:
assumes "x \<in> carrier Z\<^sub>p"
shows "val_Zp x = val (\<iota> x)" 
proof(cases "x \<in> nonzero Z\<^sub>p")
  case True
  then show ?thesis 
    using inc_of_nonzero nonzero_def ord_Zp_def ord_of_inc val_Zp_def val_ord 
    by (simp add: nonzero_def)
next
  case False
  then show ?thesis 
    by (metis Zp.nonzero_memI Zp.nonzero_one_closed assms local.inc_def nonzero_fraction_imp_numer_not_zero val_Zp_def val_def)
qed

lemma Qp_inc_id:
  assumes "a \<in> nonzero Q\<^sub>p"
  assumes "ord a \<ge>0"
  obtains b where "b \<in> nonzero Z\<^sub>p" and "a = \<iota> b"
  using assms 
  by (metis (no_types, opaque_lifting) Qp.nonzero_closed Qp.nonzero_memE(2) 
      Zp.nonzero_one_closed Zp.zero_closed Zp_defs(2) val_ring_ord_criterion image_iff local.inc_def 
      nonzero_fraction_imp_numer_not_zero not_nonzero_Zp  that)

lemma val_ring_memI:
  assumes "a \<in> carrier Q\<^sub>p"
  assumes "val a \<ge> 0"
  shows "a \<in> \<O>\<^sub>p"
  using assms Qp_val_ringI by blast

lemma val_ring_memE:
  assumes "a \<in> \<O>\<^sub>p"
  shows "val a \<ge> 0" "a \<in> carrier  Q\<^sub>p"
  using assms  val_of_inc val_pos apply auto[1]
  using assms inc_closed by auto
  
lemma val_ring_add_closed: 
  assumes "a \<in> \<O>\<^sub>p"
  assumes "b \<in> \<O>\<^sub>p"
  shows "a \<oplus> b \<in> \<O>\<^sub>p"
  using val_ring_subring subringE(7) by (metis assms(1) assms(2))

lemma val_ring_times_closed: 
  assumes "a \<in> \<O>\<^sub>p"
  assumes "b \<in> \<O>\<^sub>p"
  shows "a \<otimes> b \<in> \<O>\<^sub>p"
  using val_ring_subring subringE(6)  by (metis assms(1) assms(2))

lemma val_ring_ainv_closed: 
  assumes "a \<in> \<O>\<^sub>p"
  shows "\<ominus> a \<in> \<O>\<^sub>p"
  using val_ring_subring subringE(5)  by (metis assms)

lemma val_ring_minus_closed:
  assumes "a \<in> \<O>\<^sub>p"
  assumes "b \<in> \<O>\<^sub>p"
  shows "a \<ominus> b \<in> \<O>\<^sub>p"
  using assms val_ring_subring val_ring_ainv_closed val_ring_add_closed
  unfolding a_minus_def   by blast 

lemma one_in_val_ring:
"\<one> \<in> \<O>\<^sub>p"
  apply(rule val_ring_memI)
  apply blast
  unfolding val_one by blast 

lemma zero_in_val_ring:
"\<zero> \<in> \<O>\<^sub>p"
  apply(rule val_ring_memI)
  apply blast
  unfolding val_zero 
  by simp  

lemma ord_p:
"ord \<pp> = 1"
  using p_nonzero ord_Zp_p ord_of_inc p_inc 
  by (smt Zp_int_inc_closed ord_of_nonzero(2))

lemma ord_p_pow_nat:
"ord (\<pp> [^] (n::nat)) = n"
  using p_pow_nonzero ord_Zp_p ord_of_inc p_inc ord_Zp_p_pow p_natpow_inc  p_pow_nonzero' 
  by auto

lemma ord_p_pow_int:
"ord (\<pp> [^] (n::int)) = n"
proof(cases "n \<ge>0")
  case True
  then show ?thesis 
    by (metis int_nat_eq int_pow_int ord_p_pow_nat)
next
  case False
  then have Neg: "n <0" by auto 
  then have 0: "\<pp>[^]n = frac \<one>\<^bsub>Z\<^sub>p\<^esub> (\<p>[^]\<^bsub>Z\<^sub>p\<^esub>(-n))" 
    using p_intpow by auto
  have "(\<p>[^]\<^bsub>Z\<^sub>p\<^esub>(-n)) \<in> nonzero Z\<^sub>p"
    using False p_int_pow_nonzero 
    by (simp add: nonzero_def)
  then have "ord (\<pp> [^] (n::int)) = ord_Zp \<one>\<^bsub>Z\<^sub>p\<^esub> - ord_Zp (\<p>[^]\<^bsub>Z\<^sub>p\<^esub>(-n))" 
    using "0" ord_of_frac 
    by (simp add: Zp.nonzero_one_closed)
  then have "ord (\<pp> [^] (n::int)) = - ord_Zp (\<p>[^]\<^bsub>Z\<^sub>p\<^esub>(-n))" 
    using ord_Zp_one by linarith
  then have "ord (\<pp> [^] (n::int)) = -(-n)" 
    using Neg ord_Zp_p_int_pow 
    by (metis int.lless_eq neg_0_le_iff_le)
  then show ?thesis 
    by auto 
qed

lemma ord_nonneg:
  assumes "x \<in>  \<O>\<^sub>p"
  assumes "x \<noteq> \<zero>"
  shows "ord x \<ge>0"
proof-
  obtain a where A: "x = \<iota> a \<and> a \<in> carrier Z\<^sub>p" 
    using assms(1) by blast
  then have "a \<in> nonzero Z\<^sub>p" using assms(2) 
      local.inc_def nonzero_fraction_imp_numer_not_zero not_nonzero_Zp
    using Zp.nonzero_one_closed by blast
  then have "ord_Zp a \<ge>0" 
    using A 
    by (simp add: Zp.nonzero_memE(2) ord_pos)
  then show ?thesis 
    using A \<open>a \<in> nonzero Z\<^sub>p\<close> ord_of_inc by metis 
qed

lemma val_p:
"val \<pp> = 1"
  using p_inc val_Zp_p val_of_inc val_def ord_p p_nonzero val_ord 
  by simp  

lemma val_p_int_pow:
"val (\<pp>[^](k::int)) = k"
  using ord_p_pow_int p_intpow_closed(2) val_ord by presburger

lemma val_p_int_pow_neg:
"val (\<pp>[^](-k::int)) = - eint k"
  by (metis eint.distinct(2) local.val_zero p_intpow_closed(1) p_intpow_inv'' val_of_inv val_p_int_pow)

lemma nonzero_nat_pow_ord:
  assumes "a \<in> nonzero Q\<^sub>p"
  shows "ord (a [^] (n::nat)) = n * ord a"
  apply(induction n)
  apply simp
    using Qp_nat_pow_nonzero assms semiring_normalization_rules(2) 
    by (simp add: semiring_normalization_rules(2) ord_mult)


lemma add_cancel_eint_geq:
  assumes "(eint a) + x \<ge> (eint a ) + y"
  shows "x \<ge>y"
  using assms eint_add_left_cancel_le by blast

lemma(in padic_fields) prod_equal_val_imp_equal_val:
  assumes "a \<in> nonzero Q\<^sub>p"
  assumes "b \<in> carrier Q\<^sub>p"
  assumes "c \<in> carrier Q\<^sub>p"
  assumes "val (a \<otimes> b) = val (a \<otimes> c)"
  shows "val b = val c"
proof(cases "b = \<zero>")
  case True
  then have "val (a \<otimes> b) = \<infinity>"
    using Qp.nonzero_closed Qp.r_null assms(1) local.val_zero by presburger
  then have "c = \<zero>"
    using assms True 
    by (metis Qp.integral Qp.nonzero_closed Qp.nonzero_mult_in_car Qp.not_nonzero_memI eint_ord_simps(3) not_nonzero_Qp val_ineq)   
  then show ?thesis 
    using True by blast
next
  case False
  obtain n where n_def: "val a = eint n"
    using assms val_ord by blast
  then show ?thesis using val_mult[of a b] val_mult[of a c] unfolding n_def 
  by (simp add: Qp.nonzero_closed assms(1) assms(2) assms(3) assms(4))
qed


lemma two_times_eint:
  shows "2*(x::eint) = x + x"
  by (metis eint_2_minus_1_mult eint_add_cancel_fact plus_eq_infty_iff_eint times_eint_simps(4))

lemma times_cfs_val_mono:
  assumes "u \<in> Units Q\<^sub>p"
  assumes "a \<in> carrier Q\<^sub>p"
  assumes "b \<in> carrier Q\<^sub>p"
  assumes "val (u \<otimes> a) \<le> val (u \<otimes> b)"
  shows "val a \<le> val b"
proof-
  have "eint (ord u) + val a \<le> eint (ord u) + val b"
    using assms val_ord  val_mult Qp.Units_nonzero Qp.nonzero_closed Units_eq_nonzero by metis 
  thus ?thesis  
    apply(induction "val a")
    using add_cancel_eint_geq apply blast
    using add_cancel_eint_geq by blast
qed

lemma times_cfs_val_mono':
  assumes "u \<in> Units Q\<^sub>p"
  assumes "a \<in> carrier Q\<^sub>p"
  assumes "b \<in> carrier Q\<^sub>p"
  assumes "val (u \<otimes> a) \<le> val (u \<otimes> b) + \<alpha>"
  shows "val a \<le> val b + \<alpha>"
proof-
  obtain c where c_def: "c \<in> carrier Q\<^sub>p \<and> val c = \<alpha>"
    by (metis Qp.zero_closed eint.exhaust local.val_zero p_intpow_closed(1) val_p_int_pow)     
  have 0: "val (u \<otimes> a) \<le> val (u \<otimes> (b \<otimes> c))"
    using assms val_mult[of "u \<otimes> b" c] Qp.m_assoc[of u b c] c_def Qp.Units_closed Qp.cring_simprules(5) 
    by metis
  have 1: "val a \<le> val (b \<otimes> c)" 
    apply(rule times_cfs_val_mono[of u])
    using assms apply blast using assms apply blast
     apply(rule Qp.ring_simprules) using assms apply blast using c_def apply blast
    by(rule 0)
  show ?thesis 
    using 1 val_mult[of b c] assms c_def by smt 
qed

lemma times_cfs_val_mono'':
  assumes "u \<in> Units Q\<^sub>p"
  assumes "a \<in> carrier Q\<^sub>p"
  assumes "b \<in> carrier Q\<^sub>p"
  assumes "val a \<le> val b + \<alpha>"
  shows "val (u \<otimes> a) \<le> val (u \<otimes> b) + \<alpha>"
  apply(rule times_cfs_val_mono'[of "inv u" "u \<otimes> a" "u \<otimes> b" \<alpha>])
  using assms apply blast
  apply(rule Qp.ring_simprules)
  using assms apply blast using assms apply blast
  apply(rule Qp.ring_simprules)
  using assms apply blast using assms apply blast
  using m_assoc assms 
  by (metis Qp.Units_closed Qp.cring_simprules(5) Qp.inv_cancelR(1))

lemma val_ineq_cancel_leq: 
  assumes "a \<in> nonzero Q\<^sub>p"
  assumes "b \<in> carrier Q\<^sub>p"
  assumes "c \<in> carrier Q\<^sub>p"
  assumes "val (a \<otimes> b) \<le> val (a \<otimes> c)"
  shows "val b \<le> val c"
  using Units_eq_nonzero assms(1) assms(2) assms(3) assms(4) times_cfs_val_mono by blast 

lemma val_ineq_cancel_leq': 
  assumes "a \<in> nonzero Q\<^sub>p"
  assumes "b \<in> carrier Q\<^sub>p"
  assumes "c \<in> carrier Q\<^sub>p"
  assumes "val b \<le> val c"
  shows "val (a \<otimes> b) \<le> val (a \<otimes> c)"
  apply(rule val_ineq_cancel_leq[of "inv a" "a \<otimes> b" "a \<otimes> c"])
  using assms(1) nonzero_inverse_Qp apply blast
  using Qp.nonzero_closed assms(1) assms(2) apply blast
  using Qp.nonzero_closed assms assms(2) apply blast
  by (metis Qp.inv_cancelR(1) Qp.m_closed Qp.nonzero_closed Units_eq_nonzero assms(1) assms(2) assms(3) assms(4))

lemma val_ineq_cancel_le: 
  assumes "a \<in> nonzero Q\<^sub>p"
  assumes "b \<in> carrier Q\<^sub>p"
  assumes "c \<in> carrier Q\<^sub>p"
  assumes "val (a \<otimes> b) < val (a \<otimes> c)"
  shows "val b < val c"
  using Qp.nonzero_closed assms(1) assms(2) assms(3) assms(4) val_mult by auto 

lemma val_ineq_cancel_le': 
  assumes "a \<in> nonzero Q\<^sub>p"
  assumes "b \<in> carrier Q\<^sub>p"
  assumes "c \<in> carrier Q\<^sub>p"
  assumes "val b < val c"
  shows "val (a \<otimes> b) < val (a \<otimes> c)"
  apply(rule val_ineq_cancel_le[of "inv a" "a \<otimes> b" "a \<otimes> c"])
  using assms(1) nonzero_inverse_Qp apply blast
  using Qp.nonzero_closed assms(1) assms(2) apply blast
  using Qp.nonzero_closed assms assms(2) apply blast
  by (metis Qp.inv_cancelR(1) Qp.m_closed Qp.nonzero_closed Units_eq_nonzero assms(1) assms(2) assms(3) assms(4))

lemma finite_val_imp_nonzero:
  assumes "a \<in> carrier Q\<^sub>p"
  assumes "val a \<noteq> \<infinity>"
  shows "a \<in> nonzero Q\<^sub>p"
  using assms unfolding val_def nonzero_def 
  by (metis (mono_tags, lifting) mem_Collect_eq)

lemma val_ineq_cancel_leq'': 
  assumes "a \<in> nonzero Q\<^sub>p"
  assumes "b \<in> carrier Q\<^sub>p"
  assumes "c \<in> carrier Q\<^sub>p"
  assumes "val b \<le> val c + eint N"
  shows "val (a \<otimes> b) \<le> val (a \<otimes> c) + eint N"
proof- 
  obtain d where d_def: "d = \<pp>[^]N \<otimes> c"
    by blast 
  show ?thesis 
  proof(cases "c = \<zero>")
    case True
    then show ?thesis unfolding True 
      using True Units_eq_nonzero assms(1) assms(2) assms(4) times_cfs_val_mono'' by blast
  next
    case False
    have F0: "c \<in> nonzero Q\<^sub>p"
      using False assms  Qp.not_nonzero_memE by blast
    have F1: "val (a \<otimes> c) < \<infinity>"
      using F0 assms 
      by (metis (no_types, lifting) Qp.integral Qp.nonzero_closed Qp.nonzero_memE(2) eint.distinct(1) eint_ord_simps(4) val_def) 
    have F2: "b \<in> nonzero Q\<^sub>p"
      using F0 assms 
      by (metis False Groups.add_ac(2) add_cancel_eint_geq finite_val_imp_nonzero local.val_zero plus_eint_simps(2) val_ineq)
    have F3: "ord b \<le> ord c + N"
      using assms F0
      by (metis F2 eint_ord_simps(1) plus_eint_simps(1) val_ord)
    have F4: "ord a + ord b \<le> ord a + ord c+ N"
      using assms F0 F1 F2 ord_mult F3 by presburger
    have F5: "ord (a \<otimes> b) \<le> ord (a \<otimes> c) + N"
      using F4 F2 F0 assms ord_mult by presburger
    have F6: "a \<otimes> b \<in> nonzero Q\<^sub>p"
      by (metis F2 Qp.integral Qp.nonzero_memE(1) Qp.nonzero_mult_closed Qp.not_nonzero_memE assms(1))
    have F7: "a \<otimes> c \<in> nonzero Q\<^sub>p"
      by (metis False Qp.integral Qp.nonzero_closed Qp.nonzero_memI Qp.nonzero_mult_closed assms(1) assms(3))
    show "val (a \<otimes> b) \<le> val (a \<otimes> c) + eint N"
      using val_ord[of "a \<otimes> b" ] val_ord[of "a \<otimes>c"] F7 F7 F4 
        Units_eq_nonzero assms(1) assms(2) assms(3) assms(4) times_cfs_val_mono'' by blast
  qed
qed


      (********************************************************************************************)
      (********************************************************************************************)
      subsubsection\<open>The Ultrametric Inequality on $\mathbb{Q}_p$\<close>
      (********************************************************************************************)
      (********************************************************************************************)


lemma ord_ultrametric:
  assumes "x \<in> nonzero Q\<^sub>p"
  assumes "y \<in> nonzero Q\<^sub>p"
  assumes "x \<oplus> y \<in> nonzero Q\<^sub>p"
  shows "ord (x \<oplus> y) \<ge> min (ord x) (ord y)"
proof-
  have 0:"x \<in> carrier Q\<^sub>p" using assms by(simp add:nonzero_def)
  have 1:"y \<in>carrier Q\<^sub>p" using assms by(simp add:nonzero_def)
  obtain a b c where
   A: "a \<in> carrier Z\<^sub>p" and
   B: "b \<in> carrier Z\<^sub>p" and
   C: "c \<in> nonzero Z\<^sub>p" and
   Fx: "x = frac a c" and
   Fy: "y = frac b c" 
    using  0 1  get_common_denominator by blast
  have An: "a \<in> nonzero Z\<^sub>p" 
    using A C Fx assms(1) nonzero_fraction_imp_nonzero_numer 
          Qp.nonzero_memE(2) by auto
  have Bn: " b \<in> nonzero Z\<^sub>p" 
    using B C Fy assms(2)   nonzero_fraction_imp_nonzero_numer  Qp.nonzero_memE(2) by auto
  have Fxy: "x \<oplus> y = frac (a \<oplus>\<^bsub>Z\<^sub>p\<^esub> b) c" using 0 1  
    by (simp add: A B C Fx Fy frac_add_common_denom)
  have ABn: " a \<oplus>\<^bsub>Z\<^sub>p\<^esub> b \<in> nonzero Z\<^sub>p" 
  proof-
    have "a \<oplus>\<^bsub>Z\<^sub>p\<^esub> b \<in> carrier Z\<^sub>p" 
      using A B Z\<^sub>p_def padic_add_closed prime by blast
    then show ?thesis 
      using Fxy C assms(3) Qp.nonzero_memE(2) 
        nonzero_fraction_imp_nonzero_numer by blast     
  qed
  have Ordx: "ord x = ord_Zp a - ord_Zp c"
      using Fx An C ord_of_frac by metis 
  have Ordy: "ord y = ord_Zp b - ord_Zp c" 
    using Fy Bn C ord_of_frac by metis   
  have Ordxy: "ord (x \<oplus> y) = ord_Zp (a \<oplus>\<^bsub>Z\<^sub>p\<^esub> b) - ord_Zp c"
    using Fxy ABn C ord_of_frac by metis   
  then show ?thesis
    using Ordx Ordy Ordxy ord_Zp_ultrametric[of a b] ABn An Bn 
    by linarith
qed

lemma ord_ultrametric':
  assumes "x \<in> nonzero Q\<^sub>p"
  assumes "y \<in> nonzero Q\<^sub>p"
  assumes "x \<ominus>\<^bsub>Q\<^sub>p\<^esub> y \<in> nonzero Q\<^sub>p"
  shows "ord (x \<ominus>\<^bsub>Q\<^sub>p\<^esub> y) \<ge> min (ord x) (ord y)"
proof-
  have "ord y = ord (\<ominus>y)"
    using assms(2) ord_minus by blast
  then show ?thesis 
    using assms ord_ultrametric[of x "\<ominus>y"]
    unfolding a_minus_def 
    using Qp.add.inv_closed Qp.add.inv_eq_1_iff Qp.nonzero_closed Qp.nonzero_memE(2) Qp.nonzero_memI 
    by metis
qed

lemma val_ultrametric0:
  assumes "x \<in> nonzero Q\<^sub>p"
  assumes "y \<in> nonzero Q\<^sub>p"
  assumes "x \<oplus> y \<in> nonzero Q\<^sub>p"
  shows " min (val x) (val y) \<le> val (x \<oplus> y)  "
proof-
  have 0: "val (x \<oplus> y) = ord (x \<oplus> y)" 
    using assms(3) nonzero_def val_def[of "(x \<oplus> y)"] by fastforce
  have 1: "val x = ord x" 
    using assms(1) nonzero_def val_def 
    by (simp add: nonzero_def)
  have 2: "val y = ord y" 
    using assms(2) nonzero_def val_def val_ord by auto
  have 3: "ord (x \<oplus> y) \<ge> min (ord x) (ord y)" 
    by (simp add: assms(1) assms(2) assms(3) ord_ultrametric)   
  then show ?thesis 
    by (simp add: "0" "1" "2")   
qed

lemma val_ultrametric:
  assumes "x \<in> carrier Q\<^sub>p"
  assumes "y \<in> carrier Q\<^sub>p"
  shows " min (val x) (val y) \<le> val (x \<oplus> y)"
  apply(cases "x = \<zero> \<or> y = \<zero>")
  using assms(1) assms(2) apply auto[1]
    by (metis Qp.add.m_closed assms(1) assms(2) eint_ord_code(3) local.val_zero not_nonzero_Qp val_ultrametric0)

lemma val_ultrametric':
  assumes "x \<in> carrier Q\<^sub>p"
  assumes "y \<in> carrier Q\<^sub>p"
  shows " min (val x) (val y) \<le> val (x \<ominus> y)"
  using val_ultrametric[of x "\<ominus>y"]
        val_minus[of y]
        assms 
  by (metis Qp.domain_axioms a_minus_def cring.cring_simprules(3) domain.axioms(1))

lemma diff_ord_nonzero:
  assumes "x \<in> nonzero Q\<^sub>p"
  assumes "y \<in> nonzero Q\<^sub>p"  
  assumes "ord x \<noteq> ord y"
  shows "x \<oplus> y \<in> nonzero Q\<^sub>p"
proof(rule ccontr)
  assume " x \<oplus> y \<notin> nonzero Q\<^sub>p"
  then have "x \<oplus> y = \<zero>"
    using Qp.add.m_closed Qp.nonzero_closed Qp.nonzero_memI assms(1) assms(2) by blast
  then have "x = \<ominus> y"
    using Qp.minus_equality Qp.nonzero_closed assms(1) assms(2) by blast
  then have "ord x = ord y"
    using assms(2) ord_minus by presburger
  then show False 
    using assms(3) by blast
qed

lemma ord_ultrametric_noteq:
  assumes "x \<in> nonzero Q\<^sub>p"
  assumes "y \<in> nonzero Q\<^sub>p"
  assumes "ord x > ord y"
  shows "ord (x \<oplus> y) = (ord y)"
proof(rule ccontr)
  assume "ord (x \<oplus> y) \<noteq> ord y"
  have 00:"x \<oplus> y \<in> nonzero Q\<^sub>p"
  proof(rule ccontr)
    assume "x \<oplus> y \<notin> nonzero Q\<^sub>p"
    then have "x \<oplus> y = \<zero>"
      using Qp.add.m_closed Qp.nonzero_closed Qp.nonzero_memI assms(1) assms(2) by blast
    then have "x = \<ominus> y"
      by (smt \<open>x \<oplus> y \<notin> nonzero Q\<^sub>p\<close> assms(1) assms(2) assms(3) diff_ord_nonzero)      
    then have "ord x = ord y"
      using assms(2) ord_minus by presburger
    then show False 
      using assms(3) by linarith
  qed
  then have 0: "ord (x \<oplus> y) > ord y"
    using ord_ultrametric[of x y] \<open>ord (x \<oplus> y) \<noteq> ord y\<close> assms(1) assms(2) assms(3) 
    by linarith    
  have 1: "((y \<oplus> x) \<ominus> x) = y"
    using "00" Qp.add.inv_solve_right' Qp.add.m_comm Qp.minus_eq Qp.nonzero_closed assms(1) assms(2) by presburger 
  have 2: "ord ((y \<oplus> x) \<ominus> x) \<ge> min (ord (y \<oplus> x)) (ord x) "
    using 1 assms ord_ultrametric'[of "(y \<oplus> x)" x] diff_ord_nonzero by auto
  have 3:  "ord y \<ge> min (ord x) (ord (x \<oplus> y))"
    using 2 1 Q\<^sub>p_def Qp.domain_axioms Z\<^sub>p_def assms(1) assms(2) cring.cring_simprules(10) 
          domain.axioms(1) Qp.nonzero_closed by fastforce  
  show False 
    using 3 0 assms 
    by linarith
qed

lemma ord_ultrametric_noteq':
  assumes "x \<in> nonzero Q\<^sub>p"
  assumes "y \<in> nonzero Q\<^sub>p"
  assumes "ord x > ord y"
  shows "ord (x \<ominus> y) = (ord y)"
  using assms ord_ultrametric_noteq[of x "\<ominus>y"]
  by (metis Qp.add.inv_closed Qp.minus_eq Qp.nonzero_closed Qp.nonzero_memI Qp.r_neg Qp.r_zero ord_minus)
  
lemma ord_ultrametric_noteq'':
  assumes "x \<in> nonzero Q\<^sub>p"
  assumes "y \<in> nonzero Q\<^sub>p"
  assumes "ord y > ord x"
  shows "ord (x \<ominus> y) = (ord x)"
  using assms ord_ultrametric_noteq'[of y x]
  by (metis Qp.minus_a_inv Qp.nonzero_closed Qp.not_eq_diff_nonzero ord_minus)
  
lemma val_ultrametric_noteq:
  assumes "x \<in> carrier Q\<^sub>p"
  assumes "y \<in> carrier Q\<^sub>p"
  assumes "val x > val y"
  shows "val (x \<oplus> y) = val y"
  apply(cases "x = \<zero>")
  apply (simp add: assms(2))
    using assms unfolding val_def 
    by (smt Qp.not_nonzero_memI diff_ord_nonzero eint_ord_simps(2) not_nonzero_Qp ord_ultrametric_noteq val_def val_nonzero)

lemma val_ultrametric_noteq':
  assumes "x \<in> carrier Q\<^sub>p"
  assumes "y \<in> carrier Q\<^sub>p"
  assumes "val x > val y"
  shows "val (x \<ominus> y) = val y"
  using assms  val_ultrametric_noteq[of x "\<ominus>y"]
  by (metis Qp.domain_axioms a_minus_def cring.cring_simprules(3) domain.axioms(1) val_minus)

lemma ultrametric_equal_eq:
  assumes "x \<in> carrier Q\<^sub>p"
  assumes "y \<in> carrier Q\<^sub>p"
  assumes "val (y \<ominus> x) > val x"
  shows "val x = val y"
  using assms 
  by (metis (no_types, lifting) Qp.add.inv_closed Qp.add.m_assoc Qp.l_neg Qp.minus_closed Qp.minus_eq Qp.r_zero val_ultrametric_noteq)

lemma ultrametric_equal_eq':
  assumes "x \<in> carrier Q\<^sub>p"
  assumes "y \<in> carrier Q\<^sub>p"
  assumes "val (x \<ominus> y) > val x"
  shows "val x = val y"
  using assms ultrametric_equal_eq[of x y] 
  by (metis Qp.minus_a_inv Qp.minus_closed val_minus)

lemma val_ultrametric_noteq'':
  assumes "x \<in> carrier Q\<^sub>p"
  assumes "y \<in> carrier Q\<^sub>p"
  assumes "val x > val y"
  shows "val (y \<ominus> x) = val y"
  by (metis Qp.minus_a_inv Qp.minus_closed assms(1) assms(2) assms(3) val_minus val_ultrametric_noteq')
  
text\<open>Ultrametric over finite sums:\<close>

lemma Min_mono:
  assumes "finite A"
  assumes "A \<noteq> {}"
  assumes "\<And> a. a \<in> A \<Longrightarrow>  f a \<le> a"
  shows "Min (f`A) \<le> Min A"
  by (meson Min_in Min_le_iff assms(1) assms(2) assms(3) finite_imageI image_eqI image_is_empty)

lemma Min_mono':
  assumes "finite A"
  assumes "\<And> (a::'a). a \<in> A \<Longrightarrow> (f::'a \<Rightarrow> eint)  a \<le>  g a"
  shows "Min (f`A) \<le> Min (g `A)"
proof-
  have "(\<forall>a \<in>  A. f a \<le> g a) \<longrightarrow> Min (f`A) \<le> Min (g` A)"
  apply(rule finite.induct[of A])
      apply (simp add: assms(1))
  apply simp
  proof fix A a assume F: "finite A" "(\<forall>a\<in>A. f a \<le> g a) \<longrightarrow> Min (f ` A) \<le> Min (g ` A)"
"\<forall>a\<in>insert a A. f a \<le> g a"
    show "Min (f ` insert a A) \<le> Min (g ` insert a A)"
    proof-
      obtain k where k_def: "k \<in> insert a A \<and> g k = Min (g ` insert a A)"
        using assms 
        by (metis (mono_tags, opaque_lifting) F(1) Min_eq_iff finite.insertI finite_imageI image_iff image_is_empty insert_not_empty)
      then have 0: "f k \<le> g k"
        using F(3) by blast
      thus ?thesis using k_def 
        by (metis F(1) Min_le dual_order.trans finite.insertI finite_imageI image_eqI)
    qed
  qed
  thus ?thesis using assms by blast 
qed

lemma eint_ord_trans:
  assumes "(a::eint) \<le> b"
  assumes "b \<le> c"
  shows "a \<le> c"
  using assms by auto 

lemma eint_Min_geq:
  assumes "finite (A::eint set)"
  assumes "\<And>x. x \<in> A \<Longrightarrow> x \<ge> c"
  assumes "A \<noteq> {}"
  shows "Min A \<ge> c"
  using Min_in[of A] assms(2)[of "Min A"] assms by blast 

lemma eint_Min_gr:
  assumes "finite (A::eint set)"
  assumes "\<And>x. x \<in> A \<Longrightarrow> x > c"
  assumes "A \<noteq> {}"
  shows "Min A > c"
  using Min_in[of A] assms(2)[of "Min A"] assms by blast 

lemma finsum_val_ultrametric:
  assumes "g \<in> A \<rightarrow> carrier Q\<^sub>p"
  assumes "finite A"
  assumes "A \<noteq> {}"
  shows " val (finsum Q\<^sub>p g A) \<ge> Min (val ` (g`A))"  
proof-
  have "A \<noteq> {} \<and> g \<in> A \<rightarrow> carrier Q\<^sub>p \<longrightarrow> val (finsum Q\<^sub>p g A) \<ge> Min (val ` (g`A))"  
    apply(rule finite.induct[of A])
      apply (simp add: assms(2))
      apply blast
  proof fix A a assume A: "finite A" "A \<noteq> {}\<and> g \<in> A \<rightarrow> carrier Q\<^sub>p \<longrightarrow> val (finsum Q\<^sub>p g A) \<ge> Min (val ` g ` A)"
                          " insert a A \<noteq> {} \<and> g \<in> insert a A \<rightarrow> carrier Q\<^sub>p "
    show "val (finsum Q\<^sub>p g (insert a A)) \<ge> Min (val ` g ` insert a A)"
      apply(cases "a \<in> A")
       apply (metis A(2) A(3) insert_absorb)
    proof(cases "A = {}")
      have g_closed: "g \<in> A \<rightarrow> carrier Q\<^sub>p"
        using A(3) by blast
      have g_closed': "g \<in> insert a A \<rightarrow> carrier Q\<^sub>p"
        using A(3) by linarith
      then have ga: "g a \<in> carrier Q\<^sub>p"
        by blast 
      assume a_notin: "a \<notin> A"
      case True
      have "g a \<in> carrier Q\<^sub>p" using A(3) 
        by blast
      then have 0: "(finsum Q\<^sub>p g (insert a A)) = g a"
        using A True abelian_monoid.finsum_insert[of Q\<^sub>p A a g]  abelian_monoid.finsum_empty[of Q\<^sub>p g]
              Qp.abelian_monoid_axioms Qp.add.l_cancel_one Qp.zero_closed a_notin g_closed 
        by metis  
      have 1: "Min (val ` g ` insert a A) = val (g a)"
        by (metis A(1) True Min_in finite.insertI finite_imageI image_empty 
            image_insert insert_not_empty singletonD)
      show ?thesis 
        using 0 1 
        by simp       
    next
      case False
      assume a_notin: "a \<notin> A"
      have g_closed: "g \<in> A \<rightarrow> carrier Q\<^sub>p"
        using A(3) by blast
      have g_closed': "g \<in> insert a A \<rightarrow> carrier Q\<^sub>p"
        using A(3) by linarith
      then have ga: "g a \<in> carrier Q\<^sub>p"
        by blast 
      have 0: "finsum Q\<^sub>p g (insert a A) = g a \<oplus> finsum Q\<^sub>p g A" 
        by (simp add: A(1) a_notin g_closed ga)     
      have 1: "min (val (g a)) (Min (val ` g ` A)) = Min (insert (val (g a)) (val ` g ` A))"
      proof-
        have 10: "finite (val ` g ` A) " using A
          by blast
        then have 11: "val ` g ` A \<noteq> {}"
          using False 
          by blast
        show ?thesis 
          using  10 11 Min_insert 
          by simp          
      qed
      have 2: " val (g a \<oplus> finsum Q\<^sub>p g A) \<ge> min (val (g a)) (val (finsum Q\<^sub>p g A))"
        using val_ultrametric[of "g a" "finsum Q\<^sub>p g A" ] abelian_monoid.finsum_closed[of Q\<^sub>p g A]
              g_closed ga  Qp.abelian_monoid_axioms by blast   
      have 3: " val (finsum Q\<^sub>p g A) \<ge> Min (val ` g ` A)"
        using A False 
        by blast
      have 4: " val (finsum Q\<^sub>p g (insert a A)) \<ge>  min (val (g a)) (val (finsum Q\<^sub>p g A))"
        using 2 "0" 
        by presburger
      have 5: " val (finsum Q\<^sub>p g A) \<ge> Min (val ` g ` A)"
        using False "3" by blast
      show " val (finsum Q\<^sub>p g (insert a A)) \<ge> Min (val ` g ` insert a A)"
        using 5 4 1 
        by (smt image_insert min.cobounded1 min_def order_trans)        
    qed
  qed
  then show ?thesis 
    using assms 
    by blast
qed

lemma (in padic_fields) finsum_val_ultrametric':
  assumes "g \<in> A \<rightarrow> carrier Q\<^sub>p"
  assumes "finite A"
  assumes "\<And>i. i \<in> A \<Longrightarrow> val (g i) \<ge> c"
  shows " val (finsum Q\<^sub>p g A) \<ge> c"
proof(cases "A = {}")
  case True
  then show ?thesis using assms
    unfolding True Qp.finsum_empty  
    using eint_ord_code(3) local.val_zero by presburger
next
  case False
  show ?thesis
  proof(rule eint_ord_trans[of _ "Min (val ` g ` A)"])
    have 0: "\<And>s. s \<in> val ` g ` A \<Longrightarrow> s \<ge> c" 
    proof- fix s assume A: "s \<in> val ` g ` A"
      then obtain a where a_def: "a \<in> A \<and> s = val (g a)"
        by blast
      have s_eq: "s = val (g a)"
        using a_def by blast 
      show "c \<le> s"
        using assms(3)[of a] A a_def unfolding s_eq  by blast 
    qed
    show "c \<le> Min (val ` g ` A)"
      apply(rule eint_Min_geq)
      using assms apply blast using assms apply blast
      using False by blast
    show "Min (val ` g ` A) \<le> val (finsum Q\<^sub>p g A)"
      by(rule finsum_val_ultrametric[of g A], rule assms, rule assms, rule False)
  qed
qed

lemma (in padic_fields) finsum_val_ultrametric'':
  assumes "g \<in> A \<rightarrow> carrier Q\<^sub>p"
  assumes "finite A"
  assumes "\<And>i. i \<in> A \<Longrightarrow> val (g i) > c"
  assumes "c < \<infinity>"
  shows " val (finsum Q\<^sub>p g A) > c"
proof(cases "A = {}")
  case True
  then show ?thesis using assms
    unfolding True Qp.finsum_empty  val_zero
    using eint_ord_code(3) local.val_zero  by blast   
next
  case False
  show ?thesis
  proof(rule less_le_trans[of _ "Min (val ` g ` A)"])
    have 0: "\<And>s. s \<in> val ` g ` A \<Longrightarrow> s > c" 
    proof- fix s assume A: "s \<in> val ` g ` A"
      then obtain a where a_def: "a \<in> A \<and> s = val (g a)"
        by blast
      have s_eq: "s = val (g a)"
        using a_def by blast 
      show "c < s"
        using assms(3)[of a] A a_def unfolding s_eq  by blast 
    qed
    show "c < Min (val ` g ` A)"
      apply(rule eint_Min_gr)
      using assms apply blast using assms 
      using "0" apply blast
      using False by blast
    show "Min (val ` g ` A) \<le> val (finsum Q\<^sub>p g A)"
      by(rule finsum_val_ultrametric[of g A], rule assms, rule assms, rule False)
  qed
qed

lemma Qp_diff_diff:
  assumes "x \<in> carrier Q\<^sub>p"
  assumes "c \<in> carrier Q\<^sub>p"
  assumes "d \<in> carrier Q\<^sub>p"
  shows "(x \<ominus> c) \<ominus> (d \<ominus> c) = x \<ominus> d "
  by (smt Qp.domain_axioms a_minus_def assms(1) assms(2) assms(3) cring.cring_simprules(10) 
      cring.cring_simprules(19) cring.cring_simprules(3) cring.cring_simprules(4) 
      cring.cring_simprules(7) domain.axioms(1))

text\<open>This variant of the ultrametric identity formalizes the common saying that "all triangles in $\mathbb{Q}_p$ are isosceles":\<close>
lemma Qp_isosceles:
  assumes "x \<in> carrier Q\<^sub>p"
  assumes "c \<in> carrier Q\<^sub>p"
  assumes "d \<in> carrier Q\<^sub>p"
  assumes "val (x \<ominus> c) \<ge> v"
  assumes "val (d \<ominus> c) \<ge> v"
  shows "val (x \<ominus> d) \<ge> v"
proof-
  have "val (x \<ominus> d) \<ge> min (val (x \<ominus> c)) (val (d \<ominus> c))"
    using assms Qp_diff_diff[of x c d]
    by (metis Qp.domain_axioms cring.cring_simprules(4) domain.axioms(1) val_ultrametric')
  then show ?thesis using assms 
    by (meson dual_order.trans min_le_iff_disj)    
qed

text\<open>More variants on the ultrametric inequality\<close>

lemma MinE:
  assumes "finite (A::eint set)"
  assumes "a = Min A"
  assumes "b \<in> A"
  shows "a \<le> b"
  using assms by (simp add: assms(3))

lemma MinE':
  assumes "finite (A::eint set)"
  assumes "a = Min A"
  assumes "b \<in> A - {a}"
  shows "a < b"
proof-
  have 0: "a \<le> b" 
    using assms MinE by blast 
  have 1: "a \<noteq> b" using assms by blast 
  show ?thesis using 0 1 
    by simp
qed

lemma MinE'':
  assumes "finite A"
  assumes "f \<in> A \<rightarrow> (UNIV :: eint set)"
  assumes "a = Min (f ` A)"
  assumes "b \<in> A"
  shows "a \<le> f b"
  apply(rule MinE[of "f` A"]) using assms apply blast using assms apply blast  using assms by blast

lemma finsum_val_ultrametric_diff:
  assumes "g \<in> A \<rightarrow> carrier Q\<^sub>p"
  assumes "finite A"
  assumes "A \<noteq> {}"
  assumes "\<And>a b. a \<in> A \<Longrightarrow> b \<in> A \<Longrightarrow> a \<noteq> b \<Longrightarrow> val (g a) \<noteq> val (g b)"
  shows " val (finsum Q\<^sub>p g A) = Min (val ` g`A)"
proof-
  have "Min (val ` g ` A) \<in> val ` g ` A"
    using Min_in[of "val ` g ` A"] assms by blast
  then obtain a where a_def: "a \<in> A \<and> Min (val ` g`A) = val (g a)"
    by blast 
  have 0: "\<And>b. b \<in> A \<Longrightarrow> b \<noteq> a \<Longrightarrow> val (g b) >  val (g a)"
    apply(rule MinE'[of "val ` g ` A"]) using assms apply blast 
    using a_def assms apply presburger
    using assms(4)[of a] a_def 
    by (metis image_eqI insert_Diff insert_iff)
  have 1: "g a \<oplus> finsum Q\<^sub>p g (A - {a}) = finsum Q\<^sub>p g (insert a (A - {a}))"
    using assms Qp.finsum_insert[of "A - {a}" a g] a_def finite_subset[of "A - {a}" A]  by blast 
  have 2: "finsum Q\<^sub>p g A = g a \<oplus> finsum Q\<^sub>p g (A - {a})"  
    unfolding 1 using a_def  
    by (metis insert_Diff_single insert_absorb)
  have 3: "g a \<in> carrier Q\<^sub>p"
    using a_def assms by blast 
  show "val (finsum Q\<^sub>p g A) = Min (val ` g`A)"
  proof(cases "A = {a}")
    case True
    show ?thesis using 3 Qp.finsum_empty[of g] a_def unfolding 2 unfolding True  
      by auto       
  next
    case False
    then have F0: "A - {a} \<noteq> {}"
      using assms by blast 
    have F1: "finsum Q\<^sub>p g (A - {a}) \<in> carrier Q\<^sub>p"
      apply(rule Qp.finsum_closed)
      using assms by blast 
    have F2: "val (finsum Q\<^sub>p g (A - {a})) \<ge> Min (val ` g` (A- {a}))"
      apply(rule finsum_val_ultrametric)
      using assms apply blast using assms apply blast using False a_def by blast 
    have F3: "Min (val ` g` (A- {a})) \<in> (val ` g` (A- {a}))"
      apply(rule Min_in)
      using assms apply blast using False a_def by blast 
    obtain b where b_def: "b \<in> A - {a} \<and> Min (val ` g` (A- {a})) = val (g b)"
      using F3 by blast 
    have F4: "Min (val ` g` (A- {a})) > val (g a)"
      using a_def assms b_def  by (metis "0" Diff_iff singletonI)
    have F5: "val (finsum Q\<^sub>p g (A - {a})) > val (g a)"
      using F4 F2 less_le_trans by blast  
    then show ?thesis using 2 F1 3 
      by (metis Qp.a_ac(2) a_def val_ultrametric_noteq)
  qed
qed

lemma finsum_val_ultrametric_diff':
  assumes "g \<in> A \<rightarrow> carrier Q\<^sub>p"
  assumes "finite A"
  assumes "A \<noteq> {}"
  assumes "\<And>a b. a \<in> A \<Longrightarrow> b \<in> A \<Longrightarrow> a \<noteq> b \<Longrightarrow> val (g a) \<noteq> val (g b)"
  shows " val (finsum Q\<^sub>p g A) = (MIN a \<in> A. (val (g a)))"
proof-
  have 0: "(\<lambda> a. val (g a)) ` A = (val ` g`A)"
    by blast 
  show ?thesis using assms finsum_val_ultrametric_diff[of g A] unfolding 0 by blast 
qed


(**************************************************************************************************)
(**************************************************************************************************)
subsection\<open>Constructing the Angular Component Maps on $\mathbb{Q}_p$\<close>
(**************************************************************************************************)
(**************************************************************************************************)

      (********************************************************************************************)
      (********************************************************************************************)
      subsubsection\<open>Unreduced Angular Component Map\<close>
      (********************************************************************************************)
      (********************************************************************************************)

text\<open>While one can compute the residue of a $p$-adic integer mod $p^n$, this operation does not generalize to the $p$-adic field unless we restrict our attention to the valuation ring. However, we can still define the angular component maps on the field $\mathbb{Q}_p$, which allows us to take a sort of residue for any element $x \in \mathbb{Q}_p$. Given a nonzero element $x \in \mathbb{Q}_p^{\times}$, we can normalize it to obtain $p^{-ord( x)}x$ which has of valuation zero, and then computes its residue (viewed as an element of $\mathbb{Z}_p$). The resulting map agrees with the standard residue map on elements of $\mathbb{Q}_p$ of valuation zero, but not on terms of positive or negative valuation. For example, the element $p^2$ has an order $1$ residue of $0$, but its order $1$ angular component is $1$. In the formalism below, we will use the term "\texttt{angular\_component}" to refer to the unreduced normalization map $x \mapsto p^{-ord( x)}x$, and use the notation "\texttt{ac n}" to refer to the angular component which has been reduced mod $p^n$. This is line with the terminology used in \<^cite>\<open>"denef1986"\<close>.  \<close>
definition angular_component where 
"angular_component a = (ac_Zp (numer a)) \<otimes>\<^bsub>Z\<^sub>p\<^esub>  (inv\<^bsub>Z\<^sub>p\<^esub> ac_Zp (denom a))"

lemma ac_fract:
  assumes "c \<in> carrier Q\<^sub>p"
  assumes "a \<in> nonzero Z\<^sub>p"
  assumes "b \<in> nonzero Z\<^sub>p"
  assumes "c = frac a b"
  shows "angular_component c = (ac_Zp a)\<otimes>\<^bsub>Z\<^sub>p\<^esub> inv \<^bsub>Z\<^sub>p\<^esub>(ac_Zp b)"
proof-
  have "(numer c) \<otimes>\<^bsub>Z\<^sub>p\<^esub> b = (denom c) \<otimes>\<^bsub>Z\<^sub>p\<^esub> a"
    by (simp add: assms(2) assms(3) assms(4) mult_comm numer_denom_swap)
  then have "ac_Zp ((numer c) \<otimes>\<^bsub>Z\<^sub>p\<^esub> b) = ac_Zp ((denom c) \<otimes>\<^bsub>Z\<^sub>p\<^esub> a)"
    by simp
  then have "(ac_Zp (numer c)) \<otimes>\<^bsub>Z\<^sub>p\<^esub> (ac_Zp b) = (ac_Zp (denom c)) \<otimes>\<^bsub>Z\<^sub>p\<^esub> (ac_Zp a)"
    by (metis Q\<^sub>p_def Zp.nonzero_closed Zp.numer_denom_facts(3) ac_Zp_mult assms(2) assms(3) assms(4) local.frac_closed local.numer_denom_facts(1) nonzero_fraction_imp_nonzero_numer nonzero_numer_imp_nonzero_fraction numer_denom_frac)    
  then have "(inv \<^bsub>Z\<^sub>p\<^esub> (ac_Zp (denom c))) \<otimes>\<^bsub>Z\<^sub>p\<^esub> (ac_Zp (numer c)) \<otimes>\<^bsub>Z\<^sub>p\<^esub> (ac_Zp b) =  (ac_Zp a)"
    using ac_Zp_is_Unit[of "ac_Zp (denom c)"] Zp.domain_axioms inv_cancelR(1) 
          Q\<^sub>p_def Zp.Units_closed Zp.inv_cancelR(1) Zp.m_closed Zp.nonzero_closed Zp.nonzero_memE(2) Z\<^sub>p_def ac_Zp_is_Unit assms(1) assms(2) mult_assoc padic_fields.numer_denom_facts(2) padic_fields_axioms by auto   
  then have "(inv \<^bsub>Z\<^sub>p\<^esub> (ac_Zp (denom c))) \<otimes>\<^bsub>Z\<^sub>p\<^esub> (ac_Zp (numer c))  =  (ac_Zp a) \<otimes>\<^bsub>Z\<^sub>p\<^esub> inv \<^bsub>Z\<^sub>p\<^esub> (ac_Zp b)"
    using ac_Zp_is_Unit[of "ac_Zp b"] Zp.domain_axioms inv_cancelL(2) 
    by (smt Q\<^sub>p_def Zp.Units_inv_closed Zp.Units_r_inv Zp.nonzero_closed Zp.nonzero_memE(2) Zp.r_one Z\<^sub>p_def ac_Zp_is_Unit assms(1) assms(3) mult_assoc mult_comm padic_fields.numer_denom_facts(2) padic_fields_axioms)
  then show ?thesis 
    by (simp add: angular_component_def mult_comm)
qed

lemma angular_component_closed: 
  assumes "a \<in> nonzero Q\<^sub>p"
  shows "angular_component a \<in> carrier Z\<^sub>p"
  using ac_fract assms Q\<^sub>p_def Qp.nonzero_closed Qp.nonzero_memE(2) Zp.Units_inv_closed Zp.m_closed
      Zp.nonzero_closed Zp.nonzero_memE(2) Z\<^sub>p_def ac_Zp_is_Unit angular_component_def local.numer_denom_facts(3)
      padic_fields.numer_denom_facts(1) padic_fields.numer_denom_facts(2) padic_fields_axioms padic_integers.ac_Zp_in_Zp padic_integers_def prime by auto
 
lemma angular_component_unit: 
  assumes "a \<in> nonzero Q\<^sub>p"
  shows "angular_component a \<in> Units Z\<^sub>p"
  using ac_fract[of a "numer a" "denom a"]  Q\<^sub>p_def Qp.nonzero_closed 
    Qp.nonzero_memE(2) Zp.Units_inv_Units Zp.Units_m_closed 
    Zp.nonzero_closed Zp.nonzero_memE(2) Z\<^sub>p_def ac_Zp_is_Unit 
    angular_component_def assms local.numer_denom_facts(1) 
    local.numer_denom_facts(2) padic_fields.numer_denom_facts(3) 
    padic_fields_axioms by auto

lemma angular_component_factors_x:
  assumes "x \<in> nonzero Q\<^sub>p"
  shows "x = (\<pp>[^](ord x)) \<otimes> \<iota> (angular_component x)"
proof-
  have 0: "angular_component x = (ac_Zp (numer x)) \<otimes>\<^bsub>Z\<^sub>p\<^esub>  (inv\<^bsub>Z\<^sub>p\<^esub> ac_Zp (denom x))"
    by (simp add: angular_component_def)
  have 1:  "(numer x) = (\<p>[^]\<^bsub>Z\<^sub>p\<^esub>(ord_Zp (numer x))) \<otimes>\<^bsub>Z\<^sub>p\<^esub> (ac_Zp (numer x))"
  proof-
    have "numer x \<in> nonzero Z\<^sub>p"
     using assms unfolding Q\<^sub>p_def 
     by (simp add: numer_nonzero)
    then show ?thesis using ac_Zp_factors_x[of "numer x"]
      by (simp add: ac_Zp_factors')
  qed
  have 2: "(denom x) = (\<p>[^]\<^bsub>Z\<^sub>p\<^esub>(ord_Zp (denom x))) \<otimes>\<^bsub>Z\<^sub>p\<^esub> (ac_Zp (denom x))"
  proof-
    have "denom x \<in> nonzero Z\<^sub>p"
      using nonzero_memE assms numer_denom_facts(2) 
      by (simp add: Qp.nonzero_closed)
    then show ?thesis 
      using ac_Zp_factors_x[of "denom x"] Zp.nonzero_closed Zp.nonzero_memE(2) by auto
  qed
  have 3: "\<iota> (angular_component x) = frac (ac_Zp (numer x)) (ac_Zp (denom x))"
    by (metis "0" Q\<^sub>p_def Qp.nonzero_closed Qp.nonzero_memE(2) Zp.nonzero_closed Zp.nonzero_memE(2) Zp.numer_denom_facts(2) Z\<^sub>p_def Z\<^sub>p_division_Qp_0 ac_Zp_is_Unit angular_component_closed assms local.inc_def padic_fields.numer_denom_facts(2) padic_fields.numer_denom_facts(3) padic_fields_axioms)
  have 4: "(\<pp>[^]((ord x))) \<otimes> \<iota> (angular_component x) = 
           (\<pp>[^]((ord_Zp (numer x)) - (ord_Zp (denom x)))) \<otimes> frac (ac_Zp (numer x)) (ac_Zp (denom x))"
    using "3" ord_def by presburger
  have 5: "(\<pp>[^]((ord x))) \<otimes> \<iota> (angular_component x) = 
           frac (\<p>[^]\<^bsub>Z\<^sub>p\<^esub>((ord_Zp (numer x)))) (\<p>[^]\<^bsub>Z\<^sub>p\<^esub>(ord_Zp (denom x))) \<otimes> frac (ac_Zp (numer x)) (ac_Zp (denom x))"
  proof-
    have "(\<pp>[^]((ord_Zp (numer x)) - (ord_Zp (denom x)))) 
        =  frac (\<p>[^]\<^bsub>Z\<^sub>p\<^esub>((ord_Zp (numer x)))) (\<p>[^]\<^bsub>Z\<^sub>p\<^esub>(ord_Zp (denom x)))"
      by (metis Q\<^sub>p_def Qp.nonzero_closed Z\<^sub>p_def assms domain.nonzero_memE(1) domain.nonzero_memE(2) numer_nonzero ord_pos p_pow_diff padic_fields.numer_denom_facts(2) padic_fields_axioms padic_int_is_domain prime)             
    then show ?thesis using 4 by metis 
  qed
  have 6: "(\<pp>[^]((ord x))) \<otimes> \<iota> (angular_component x) = 
           frac (\<p>[^]\<^bsub>Z\<^sub>p\<^esub>((ord_Zp (numer x))) \<otimes>\<^bsub>Z\<^sub>p\<^esub> (ac_Zp (numer x))) (\<p>[^]\<^bsub>Z\<^sub>p\<^esub>(ord_Zp (denom x)) \<otimes>\<^bsub>Z\<^sub>p\<^esub>  (ac_Zp (denom x)))"
    using 5 frac_mult[of "\<p>[^]\<^bsub>Z\<^sub>p\<^esub>((ord_Zp (numer x)))" " (\<p>[^]\<^bsub>Z\<^sub>p\<^esub>(ord_Zp (denom x)))" "(ac_Zp (numer x)) " " (ac_Zp (denom x))"] mult_comm 
    by (metis "2" Q\<^sub>p_def Qp.nonzero_closed Zp.integral_iff Zp.nonzero_closed Zp.nonzero_memE(2) ac_Zp_in_Zp assms local.numer_denom_facts(2) not_nonzero_Zp numer_nonzero ord_pos p_int_pow_nonzero)
  then show ?thesis 
    using "1" "2" nonzero_memE assms numer_denom_facts(5) Qp.nonzero_closed by auto   
qed

lemma angular_component_mult:
  assumes "x \<in> nonzero Q\<^sub>p"
  assumes "y \<in> nonzero Q\<^sub>p"
  shows "angular_component (x \<otimes> y) = (angular_component  x) \<otimes>\<^bsub>Z\<^sub>p\<^esub> (angular_component  y)"
proof-
  obtain a b where "a = numer x" and
                   "b = denom x" and 
                   a_nz: "a \<in> nonzero Z\<^sub>p" and
                   b_nz: "b \<in> nonzero Z\<^sub>p" and
                   x_frac: "x = frac a b"
    using assms Qp.nonzero_memE[of x] 
    by (meson local.numer_denom_facts(1) local.numer_denom_facts(2) 
        local.numer_denom_facts(3) local.numer_denom_facts(5) not_nonzero_Zp)
  obtain c d where "c = numer y" and
                   "d = denom y" and 
                   c_nz: "c \<in> nonzero Z\<^sub>p" and
                   d_nz: "d \<in> nonzero Z\<^sub>p" and 
                   y_frac: "y = frac c d"
        using assms Qp.nonzero_memE[of y] 
    by (meson local.numer_denom_facts(1) local.numer_denom_facts(2) local.numer_denom_facts(3) local.numer_denom_facts(5) not_nonzero_Zp)      
  have 0: "(x \<otimes> y) = frac (a \<otimes>\<^bsub>Z\<^sub>p\<^esub> c) (b \<otimes>\<^bsub>Z\<^sub>p\<^esub> d)"
    using  a_nz b_nz c_nz d_nz frac_mult x_frac y_frac
    by (simp add: Zp.nonzero_closed)
  have 1: "angular_component (x \<otimes> y) = (ac_Zp (a \<otimes>\<^bsub>Z\<^sub>p\<^esub> c)) \<otimes>\<^bsub>Z\<^sub>p\<^esub> inv\<^bsub>Z\<^sub>p\<^esub> (ac_Zp (b \<otimes>\<^bsub>Z\<^sub>p\<^esub> d))"
    by (metis (mono_tags, lifting) "0" Qp.nonzero_mult_closed Zp.integral_iff Zp.nonzero_closed Zp.nonzero_mult_closed a_nz ac_fract assms(1) assms(2) b_nz c_nz d_nz not_nonzero_Zp)   
  have 2: "angular_component (x \<otimes> y) = (ac_Zp a) \<otimes>\<^bsub>Z\<^sub>p\<^esub> (ac_Zp c) \<otimes>\<^bsub>Z\<^sub>p\<^esub> inv\<^bsub>Z\<^sub>p\<^esub> ((ac_Zp b) \<otimes>\<^bsub>Z\<^sub>p\<^esub> (ac_Zp d))"
    by (simp add: "1" a_nz ac_Zp_mult b_nz c_nz d_nz)
  have 3: "angular_component (x \<otimes> y) = (ac_Zp a) \<otimes>\<^bsub>Z\<^sub>p\<^esub> (ac_Zp c) \<otimes>\<^bsub>Z\<^sub>p\<^esub> inv\<^bsub>Z\<^sub>p\<^esub> (ac_Zp b) \<otimes>\<^bsub>Z\<^sub>p\<^esub> inv\<^bsub>Z\<^sub>p\<^esub> (ac_Zp d)"
    using 2 
    by (simp add: Zp.inv_of_prod Zp.nonzero_closed Zp.nonzero_memE(2) ac_Zp_is_Unit b_nz d_nz mult_assoc)

  have 4: "angular_component (x \<otimes> y) = (ac_Zp a) \<otimes>\<^bsub>Z\<^sub>p\<^esub>  inv\<^bsub>Z\<^sub>p\<^esub> (ac_Zp b) \<otimes>\<^bsub>Z\<^sub>p\<^esub>  (ac_Zp c) \<otimes>\<^bsub>Z\<^sub>p\<^esub> inv\<^bsub>Z\<^sub>p\<^esub> (ac_Zp d)"
    using "3"  a_nz ac_Zp_in_Zp ac_Zp_is_Unit b_nz c_nz m_assoc mult_comm 
          mult_assoc by auto  
  have 5: "angular_component (x \<otimes> y) = ((ac_Zp a) \<otimes>\<^bsub>Z\<^sub>p\<^esub>  inv\<^bsub>Z\<^sub>p\<^esub> (ac_Zp b)) \<otimes>\<^bsub>Z\<^sub>p\<^esub> ( (ac_Zp c) \<otimes>\<^bsub>Z\<^sub>p\<^esub> inv\<^bsub>Z\<^sub>p\<^esub> (ac_Zp d))"
    using 4 by (simp add: mult_assoc) 
  then show ?thesis 
    by (simp add: Z\<^sub>p_def \<open>a = numer x\<close> \<open>b = denom x\<close> \<open>c = numer y\<close> \<open>d = denom y\<close>
        padic_fields.angular_component_def padic_fields_axioms)
qed

lemma angular_component_inv:
  assumes "x \<in> nonzero Q\<^sub>p"
  shows "angular_component (inv\<^bsub>Q\<^sub>p\<^esub> x) = inv\<^bsub>Z\<^sub>p\<^esub> (angular_component x)"
  by (metis Q\<^sub>p_def Qp.one_closed Zp.Units_r_inv Zp.inv_unique' Zp.nonzero_closed Zp.nonzero_one_closed Zp.zero_not_one Z\<^sub>p_def \<iota>_def ac_Zp_is_Unit angular_component_closed angular_component_mult assms frac_nonzero_inv(1) frac_nonzero_inv(2) inc_equation inc_of_one nonzero_inverse_Qp padic_fields.ac_fract padic_fields_axioms)

lemma angular_component_one: 
"angular_component \<one> = \<one>\<^bsub>Z\<^sub>p\<^esub>"
  using \<iota>_def ac_Zp_one ac_fract inc_equation inc_of_one 
    Zp.nonzero_one_closed by fastforce

lemma angular_component_ord_zero:
  assumes "ord x = 0"
  assumes "x \<in> nonzero Q\<^sub>p"
  shows "\<iota> (angular_component x) = x"
proof-
  have 0: "ord x \<ge>0"
    using assms by auto 
  have 1: "x \<in> nonzero Q\<^sub>p"
  proof-
    have "x \<noteq> \<zero>"
      using nonzero_def assms(2)  Qp.nonzero_memE(2) by auto      
    then show ?thesis 
      by (simp add: assms(2))
  qed
  obtain a where a_def: "a \<in> nonzero Z\<^sub>p \<and> \<iota> a = x"
    using 0 1 assms Qp_inc_id[of x] 
    by metis
  then have "x = frac a \<one>\<^bsub>Z\<^sub>p\<^esub>"
    using local.inc_def Zp.nonzero_closed by blast
  then have "angular_component x = ac_Zp a \<otimes>\<^bsub>Z\<^sub>p\<^esub> inv\<^bsub>Z\<^sub>p\<^esub> (ac_Zp \<one>\<^bsub>Z\<^sub>p\<^esub>)"
    using ac_fract[of x a ]  "1" nonzero_memE Q\<^sub>p_def Zp.nonzero_closed Zp.nonzero_one_closed Z\<^sub>p_def a_def 
      local.frac_closed padic_fields.ac_fract padic_fields_axioms by auto
  then have "angular_component x = ac_Zp a \<otimes>\<^bsub>Z\<^sub>p\<^esub> inv\<^bsub>Z\<^sub>p\<^esub> \<one>\<^bsub>Z\<^sub>p\<^esub>"
    by (simp add: ac_Zp_one)
  then have 0: "angular_component x = ac_Zp a \<otimes>\<^bsub>Z\<^sub>p\<^esub> \<one>\<^bsub>Z\<^sub>p\<^esub>"
    by simp
  have "ac_Zp a \<in> nonzero Z\<^sub>p"
    using Zp.Units_nonzero Zp.nonzero_closed Zp.not_nonzero_memI a_def ac_Zp_is_Unit by auto
  thus ?thesis using 0 
    by (metis Zp.l_one Zp.nonzero_closed Zp_defs(1) Zp_defs(4) a_def ac_Zp_factors' 
        assms(1) int_pow_0 mult_comm ord_of_inc)
qed

lemma angular_component_of_inclusion:
  assumes "x \<in> nonzero Z\<^sub>p"
  assumes "y = \<iota> x"
  shows "angular_component y = ac_Zp x"
proof-
  have "y = local.frac x \<one>\<^bsub>Z\<^sub>p\<^esub>"
    using assms 
    by (simp add: Zp.nonzero_closed local.inc_def)
  then have 0: "angular_component y = (ac_Zp x) \<otimes>\<^bsub>Z\<^sub>p\<^esub> inv\<^bsub>Z\<^sub>p\<^esub> ac_Zp (\<one>\<^bsub>Z\<^sub>p\<^esub>)"
    using assms  ac_fract[of y x ] 
    by (simp add: \<open>y = \<iota> x\<close> Zp.nonzero_closed Zp.nonzero_one_closed local.frac_closed)
  have 1: "ac_Zp \<one>\<^bsub>Z\<^sub>p\<^esub> = \<one>\<^bsub>Z\<^sub>p\<^esub>"
    using ac_Zp_one by blast
  have 2: "(ac_Zp x)  \<in> carrier Z\<^sub>p"
    using Zp.Units_closed Zp.nonzero_closed ac_Zp_is_Unit assms(1) nonzero_fraction_imp_numer_not_zero nonzero_numer_imp_nonzero_fraction by auto  
  have 3: "inv \<^bsub>Z\<^sub>p\<^esub> (ac_Zp \<one>\<^bsub>Z\<^sub>p\<^esub>) = \<one>\<^bsub>Z\<^sub>p\<^esub>"
    using 1 
    by simp  
  have 4: "(ac_Zp x) \<otimes>\<^bsub>Z\<^sub>p\<^esub> inv\<^bsub>Z\<^sub>p\<^esub> ac_Zp (\<one>\<^bsub>Z\<^sub>p\<^esub>) = (ac_Zp x) \<otimes>\<^bsub>Z\<^sub>p\<^esub> \<one>\<^bsub>Z\<^sub>p\<^esub>"
    using "3" by auto
  have 5: "(ac_Zp x) \<otimes>\<^bsub>Z\<^sub>p\<^esub> inv\<^bsub>Z\<^sub>p\<^esub> ac_Zp (\<one>\<^bsub>Z\<^sub>p\<^esub>) = (ac_Zp x)"
    using 4 2 Zp.domain_axioms  by simp
  then show ?thesis 
    by (simp add: "0")
qed

lemma res_uminus:
  assumes "k > 0"
  assumes "f \<in> carrier Z\<^sub>p"
  assumes "c \<in> carrier (Zp_res_ring k)"
  assumes "c = \<ominus>\<^bsub>Zp_res_ring k\<^esub> (f k)"
  shows "c = ((\<ominus>\<^bsub>Z\<^sub>p\<^esub> f) k)"
  using Z\<^sub>p_def assms(2) assms(4)  prime  Zp_residue_a_inv(1) by auto

lemma ord_fract:
  assumes "a \<in> nonzero Q\<^sub>p"
  assumes "b \<in> nonzero Q\<^sub>p"
  shows "ord (a \<div> b) = ord a - ord b"
  using assms nonzero_memE nonzero_def nonzero_inverse_Qp ord_mult ord_of_inv 
        Qp.nonzero_closed Qp.nonzero_memE(2) by presburger

lemma val_fract:
  assumes "a \<in> carrier Q\<^sub>p"
  assumes "b \<in> nonzero Q\<^sub>p"
  shows "val (a \<div> b) = val a - val b"
  apply(cases "a = \<zero>")
   apply (simp add: Units_eq_nonzero assms(2) val_def)
proof-
  assume "a \<noteq> \<zero>"
  then have 0: "a \<in> nonzero Q\<^sub>p"
    by (simp add: Qp.nonzero_memI assms(1))
  have 1: "(a \<div> b) \<in> nonzero Q\<^sub>p"
    by (simp add: "0" Localization.submonoid.m_closed Qp.nonzero_is_submonoid assms(2) nonzero_inverse_Qp)
  show ?thesis using 0 1 assms  
    by (simp add: ord_fract)
qed
  
lemma zero_fract:
  assumes "a \<in> nonzero Q\<^sub>p"
  shows "\<zero> \<div> a = \<zero>"
  by (simp add: Units_eq_nonzero assms)

lemma fract_closed:
  assumes "a \<in> carrier Q\<^sub>p"
  assumes "b \<in> nonzero Q\<^sub>p"
  shows "(a \<div> b) \<in> carrier Q\<^sub>p"
  by (simp add: Units_eq_nonzero assms(1) assms(2))

lemma val_of_power:
  assumes "a \<in> nonzero Q\<^sub>p"
  shows "val (a[^](n::nat)) = n*(val a)"
  unfolding val_def using assms 
  by (simp add: Qp.nonzero_memE(2) Qp_nat_pow_nonzero nonzero_nat_pow_ord)

lemma val_zero_imp_val_pow_zero:
  assumes "a \<in> carrier Q\<^sub>p"
  assumes "val a = 0"
  shows "val (a[^](n::nat)) = 0"
  apply(induction n) 
  using assms apply simp
proof- 
  fix n ::nat
  assume A: "val (a [^] n) = 0"
  have 0: "a [^] Suc n = a [^] n \<otimes> a"
    by simp 
  show "val (a [^] Suc n) = 0 "
    unfolding 0 using A assms 
    by (simp add: val_mult)
qed

text\<open>val and ord of powers of p\<close>

lemma val_p_nat_pow:
"val (\<pp>[^](k::nat)) = eint k"
  by (simp add: ord_p_pow_nat)

lemma ord_p_int_pow:
"ord (\<pp>[^](k::int)) = k"
  by (simp add: ord_p_pow_int)

lemma ord_p_nat_pow:
"ord (\<pp>[^](k::nat)) = k"
  by (simp add: ord_p_pow_nat)

lemma val_nonzero_frac:
  assumes "a \<in> nonzero Q\<^sub>p"
  assumes "b \<in> nonzero Q\<^sub>p"
  assumes "val (a \<div> b) = c"
  shows "val a = val b + c"
proof-
  obtain n where n_def: "c = eint n"
    using assms val_ord by (metis (no_types, lifting) Qp.integral Qp.nonzero_closed inv_in_frac(1) inv_in_frac(2) val_def)
  have 0: "ord (a \<div> b) = n"
    by (metis assms(3) eint.distinct(2) eint.inject n_def val_def)
  have 1: "ord a - ord b = n"
    using 0 assms by (metis ord_fract)
  have 2: "ord a = ord b + n"
    using 1 by presburger 
  show "val a = val b + c"
    unfolding n_def using 2 assms 
    by (metis Qp.nonzero_memE(1) fract_closed local.fract_cancel_right n_def val_mult)
qed

lemma val_nonzero_frac':
  assumes "a \<in> nonzero Q\<^sub>p"
  assumes "b \<in> nonzero Q\<^sub>p"
  assumes "val (a \<div> b) = 0"
  shows "val a = val b"
  using val_nonzero_frac[of a b 0]
  by (metis arith_simps(50) assms(1) assms(2) assms(3))

lemma equal_val_imp_equal_ord: 
  assumes "a \<in> nonzero Q\<^sub>p"
  assumes "b \<in> carrier Q\<^sub>p"
  assumes "val a = val b"
  shows "ord a = ord b" "b \<in> nonzero Q\<^sub>p"
  using assms 
   apply (metis eint.inject eint.simps(3) eint_ord_simps(4) val_nonzero val_ord)
  using assms unfolding nonzero_def 
  using val_def by auto

lemma int_pow_ord:
  assumes "a \<in> nonzero Q\<^sub>p"
  shows "ord (a[^](i::int)) = i* (ord a)"
proof(induction i)
  show "\<And>n. ord (a [^] int n) = int n * ord a"
    using assms 
    by (metis int_pow_int mult_of_nat_commute nonzero_nat_pow_ord)
  show "\<And>n. ord (a [^] - int (Suc n)) = - int (Suc n) * ord a"
  proof- fix n 
    have "(a [^] - int (Suc n)) \<otimes> (a [^]  int (Suc n)) = a [^] (- int (Suc n) + int  (Suc n))"
      using assms Qp_int_pow_add by blast
    hence "(a [^] - int (Suc n)) \<otimes> (a [^]  int (Suc n)) = \<one>"
      using assms 
      by (metis ab_group_add_class.ab_left_minus int_pow_0)
    hence "ord (a [^] - int (Suc n)) + ord (a [^]  int (Suc n)) = 0"
      by (metis Qp_int_pow_nonzero assms ord_mult ord_one)
    thus "ord (a [^] - int (Suc n)) = - int (Suc n) * ord a"
      using nonzero_nat_pow_ord assms 
      by (metis \<open>\<And>n. ord (a [^] int n) = int n * ord a\<close> add.inverse_inverse add_left_cancel more_arith_simps(4) more_arith_simps(7))
  qed
qed

lemma int_pow_val:
  assumes "a \<in> nonzero Q\<^sub>p"
  shows "val (a[^](i::int)) = i* (val a)"
  using int_pow_ord Qp_int_pow_nonzero assms times_eint_simps(1) val_ord by presburger

lemma neg_int_pow_val:
  assumes "a \<in> nonzero Q\<^sub>p"
  shows "val (a[^]-(i::int)) = - (val (a[^]i))"
  using int_pow_val[of a i]
  by (metis Qp_int_pow_nonzero assms int_pow_ord mult_minus_left val_ord val_p_int_pow val_p_int_pow_neg)

lemma int_pow_sum_val:
  assumes "a \<in> nonzero Q\<^sub>p"
  shows "val (a[^]((i::int) + j)) =  (val (a[^]i)) + val (a[^]j)"
  using assms Qp.int_pow_add Qp_int_pow_nonzero Units_eq_nonzero val_mult0 by presburger

lemma int_pow_diff_val:
  assumes "a \<in> nonzero Q\<^sub>p"
  shows "val (a[^]((i::int) - j)) =  (val (a[^]i)) - val (a[^]j)"
proof-
  obtain k where k_def: "val a = eint k"
    using assms val_ord by blast
  have 0: "val (a[^]((i::int) - j)) = eint ((i-j)*k)"
    using assms k_def int_pow_val times_eint_simps(1) by presburger
  show ?thesis unfolding 0 using k_def 
    by (metis "0" Qp_int_pow_nonzero Rings.ring_distribs(3) assms eint.simps(1) idiff_eint_eint int_pow_ord val_ord)
qed

lemma nat_add_pow_mult_assoc:
  assumes "a \<in> carrier Q\<^sub>p"
  shows "[(n::nat)]\<cdot>a = [n]\<cdot>\<one> \<otimes> a"
  using assms Qp.add_pow_ldistr Qp.l_one Qp.one_closed by presburger

lemma(in padic_integers) equal_res_imp_equal_ord_Zp:
  assumes "N > 0"
  assumes "a \<in> carrier Zp"
  assumes "b \<in> carrier Zp"
  assumes "a N = b N"
  assumes "a N \<noteq> 0"
  shows "ord_Zp a = ord_Zp b" 
proof-
  have "(a \<ominus> b) N = 0"
    using assms(2) assms(3) assms(4) res_diff_zero_fact'' by blast 
  have "ord_Zp a < N"
    using assms zero_below_ord by force    
  then show ?thesis 
    by (smt R.minus_closed Zp_def \<open>(a \<ominus> b) N = 0\<close> above_ord_nonzero assms(2) assms(3) assms(4) assms(5) ord_Zp_ultrametric_eq' ord_Zp_ultrametric_eq'' padic_integers.ord_Zp_not_equal_imp_notequal(2) padic_integers.ord_of_nonzero(2) padic_integers.ord_pos padic_integers_axioms residue_of_zero(2))
qed

lemma(in padic_integers) equal_res_mod:
  assumes "N > k"
  assumes "a \<in> carrier Zp"
  assumes "b \<in> carrier Zp"
  assumes "a N = b N"
  shows "a k = b k"
proof-
  have 0: "a k = a N mod p^k"
    using assms 
    by (metis Zp_int_inc_rep Zp_int_inc_res less_or_eq_imp_le p_residue_padic_int)
  have 1: "b k = b N mod p^k"
    using assms 
    by (metis Zp_int_inc_rep Zp_int_inc_res less_or_eq_imp_le p_residue_padic_int) 
  show ?thesis unfolding 0 1 assms  using assms by blast 
qed

lemma Qp_char_0:
  assumes "(n::nat) \<noteq> 0"
  shows "[n]\<cdot>\<one> \<noteq> \<zero>"
proof-
  have "[n]\<cdot>\<^bsub>Z\<^sub>p\<^esub> \<one>\<^bsub>Z\<^sub>p\<^esub> \<noteq> \<zero>\<^bsub>Z\<^sub>p\<^esub>"
    using Zp_char_0' assms by blast
  thus ?thesis using inc_of_nat 
    by (metis Qp.nat_inc_zero Zp.nat_inc_zero Zp_nat_inc_closed \<iota>_def inc_inj2)
qed

lemma Qp_char_0_int:
  assumes "(n::int) \<noteq> 0"
  shows "[n]\<cdot>\<one> \<noteq> \<zero>"
proof-
  have "[n]\<cdot>\<^bsub>Z\<^sub>p\<^esub> \<one>\<^bsub>Z\<^sub>p\<^esub> \<noteq> \<zero>\<^bsub>Z\<^sub>p\<^esub>"
    using Zp_char_0 assms 
    by (metis int_inc_mult linorder_neqE_linordered_idom mult_zero_l zero_less_mult_iff)    
  thus ?thesis using inc_of_int 
    by (metis Q\<^sub>p_def Zp_int_inc_closed \<iota>_def inc_inj1)    
qed

lemma add_int_pow_inject:
  assumes "[(k::int)]\<cdot>\<one> = [(j::int)]\<cdot>\<one>"
  shows "k = j"
proof(rule ccontr)
  assume A: "k \<noteq> j"
  then have 0: "k - j \<noteq>0 "
    by presburger 
  hence 1: "[(k-j)]\<cdot>\<one> \<noteq> \<zero> "
    using Qp_char_0_int by blast
  hence 2: "[k]\<cdot>\<one> \<oplus> [(-j)]\<cdot> \<one>  \<noteq> \<zero> "
    by (metis (no_types, opaque_lifting) Qp.add.int_pow_mult Qp.one_closed diff_minus_eq_add diff_zero minus_diff_eq)
  hence 2: "[k]\<cdot>\<one> \<ominus> [j]\<cdot> \<one>  \<noteq> \<zero> "
    by (metis Qp.add.int_pow_mult Qp.int_inc_zero Qp.one_closed assms more_arith_simps(4))
  thus False using assms 
    using Qp.int_inc_closed Qp.r_right_minus_eq by blast
qed

lemma val_ord_nat_inc:
  assumes "(n::nat) > 0"
  shows "ord ([n]\<cdot>\<one>) = val([n]\<cdot>\<one>)"
  using val_ord assms Qp_char_0 
  by (metis less_irrefl_nat val_def)

lemma val_ord_int_inc:
  assumes "(n::int) \<noteq> 0"
  shows "ord ([n]\<cdot>\<one>) = val([n]\<cdot>\<one>)"
  using val_ord assms Qp_char_0_int val_def by presburger


      (********************************************************************************************)
      (********************************************************************************************)
      subsubsection\<open>Reduced Angular Component Maps\<close>
      (********************************************************************************************)
      (********************************************************************************************)
  
definition ac :: "nat \<Rightarrow> padic_number \<Rightarrow> int" where
"ac n x = (if x = \<zero> then 0 else (angular_component x) n)"

lemma ac_in_res_ring:
  assumes "x \<in> nonzero Q\<^sub>p"
  shows "ac n x \<in> carrier (Zp_res_ring n)"
  unfolding ac_def 
  using assms angular_component_closed[of x] 
  by (simp add: Qp.nonzero_memE(2) residues_closed)

lemma ac_in_res_ring'[simp]:
  assumes "x \<in> carrier Q\<^sub>p"
  shows "ac n x \<in> carrier (Zp_res_ring n)"
  apply(cases "x \<in> nonzero Q\<^sub>p")
  using ac_in_res_ring apply blast
  by (metis Qp.nonzero_memI ac_def assms mod_0 mod_in_carrier p_res_ring_car p_residue_alt_def)
  
lemma ac_mult':
  assumes "x \<in> nonzero Q\<^sub>p"
  assumes "y \<in> nonzero Q\<^sub>p"
  shows "ac n (x \<otimes> y) = (ac n x) \<otimes>\<^bsub>Zp_res_ring n\<^esub> (ac n y)"
  unfolding ac_def 
proof-
  have 0: "angular_component (x \<otimes> y) = angular_component x \<otimes>\<^bsub>Z\<^sub>p\<^esub> angular_component y"
    using assms angular_component_mult[of x y]
    by auto 
  show "(if x \<otimes> y = \<zero> then 0 else angular_component (x \<otimes> y) n) =
    (if x = \<zero> then 0 else angular_component x n) \<otimes>\<^bsub>Zp_res_ring n\<^esub> (if y = \<zero> then 0 else angular_component y n)"
    using assms angular_component_closed[of x] angular_component_closed[of y]
    by (simp add: "0" Qp.integral_iff Qp.nonzero_closed Qp.nonzero_memE(2) residue_of_prod) 
qed

lemma ac_mult:
  assumes "x \<in> carrier Q\<^sub>p"
  assumes "y \<in> carrier Q\<^sub>p"
  shows "ac n (x \<otimes> y) = (ac n x) \<otimes>\<^bsub>Zp_res_ring n\<^esub> (ac n y)"
  apply(cases "x \<in> nonzero Q\<^sub>p \<and> y \<in> nonzero Q\<^sub>p")
  apply (simp add: ac_mult')
  using assms unfolding ac_def 
  by (smt Qp.integral_iff Qp.nonzero_memI residue_times_zero_l residue_times_zero_r)
 
lemma ac_one[simp]:
  assumes "n \<ge> 1"
  shows "ac n \<one> = 1"  
proof-
  have "ac n \<one> = \<one>\<^bsub>Z\<^sub>p\<^esub> n"
    unfolding ac_def
    using angular_component_one 
    by simp    
  then show ?thesis 
    using assms residue_of_one(2) by auto   
qed

lemma ac_one':
  assumes "n > 0"
  shows "ac n \<one> = \<one>\<^bsub>Zp_res_ring n\<^esub>"
  using assms residue_ring_def 
  by auto

lemma ac_units:
  assumes "x \<in> nonzero Q\<^sub>p"
  assumes "n > 0"
  shows "ac n x \<in> Units (Zp_res_ring n)"
proof-
  obtain y where y_def: "y = inv x"
    by simp 
  have y_nz: "y \<in> nonzero Q\<^sub>p"
    using assms(1) nonzero_inverse_Qp y_def 
    by blast    
  have 0: "ac n (x \<otimes> y) = (ac n x) \<otimes>\<^bsub>Zp_res_ring n\<^esub> (ac n y)"
    using ac_mult' assms(1) y_nz by blast
  have 1: "x \<otimes> y = \<one>" 
    by (metis Qp.field_axioms Qp.nonzero_memE Qp.nonzero_memE assms(1) field.field_inv(2) y_def)
  have 2: "(ac n x) \<otimes>\<^bsub>Zp_res_ring n\<^esub> (ac n y) = \<one>\<^bsub>Zp_res_ring n\<^esub>"
    using "0" "1" ac_one' assms(2) 
    by auto
  show ?thesis 
    by (metis "2" R_comm_monoid ac_in_res_ring assms(1) assms(2) comm_monoid.UnitsI(1) nonzero_inverse_Qp y_def)
        
qed

lemma ac_inv:
  assumes "x \<in> nonzero Q\<^sub>p"
  assumes "n > 0"
  shows "ac n (inv x) = inv\<^bsub>Zp_res_ring n\<^esub> (ac n x)"
proof-
  have "x \<otimes> inv x = \<one>"  
    by (simp add: Qp.monoid_axioms Units_eq_nonzero assms(1) monoid.Units_r_inv)    
  then have "ac n (x \<otimes> inv x) = \<one>\<^bsub>Zp_res_ring n\<^esub>"
    by (simp add: \<open>(x \<div> x) = \<one>\<close> ac_one' assms(2))
  then have "ac n x \<otimes>\<^bsub>Zp_res_ring n\<^esub> ac n (inv x) = \<one>\<^bsub>Zp_res_ring n\<^esub>"
    using Units_eq_nonzero Units_inverse_Qp ac_mult' assms(1) 
    by metis    
  then show ?thesis 
    by (metis R_comm_monoid ac_in_res_ring assms(1) assms(2) comm_monoid.comm_inv_char nonzero_inverse_Qp)
qed

lemma ac_inv':
  assumes "x \<in> nonzero Q\<^sub>p"
  assumes "n > 0"
  shows "ac n (inv x) \<otimes>\<^bsub>Zp_res_ring n\<^esub> (ac n x) = \<one>\<^bsub>Zp_res_ring n\<^esub>"
  using ac_inv[of x n] ac_units[of x n] assms 
  by (metis (no_types, opaque_lifting) Qp.field_axioms Qp.nonzero_memE 
      Qp.nonzero_memE Units_eq_nonzero Units_inverse_Qp ac_mult ac_one' field.field_inv(1))  

lemma ac_inv'':
  assumes "x \<in> nonzero Q\<^sub>p"
  assumes "n > 0"
  shows " (ac n x) \<otimes>\<^bsub>Zp_res_ring n\<^esub> ac n (inv x)= \<one>\<^bsub>Zp_res_ring n\<^esub>"
  using ac_inv' assms(1) assms(2) residue_mult_comm by auto

lemma ac_inv''':
  assumes "x \<in> nonzero Q\<^sub>p"
  assumes "n > 0"
  shows "(ac n x) \<otimes>\<^bsub>Zp_res_ring n\<^esub> ac n (inv x)= 1"
        "ac n (inv x) \<otimes>\<^bsub>Zp_res_ring n\<^esub> (ac n x) = 1"
  by (auto simp add: ac_inv'' ac_inv' assms(1) assms(2) p_res_ring_one)

lemma ac_val:
  assumes  "a \<in> nonzero Q\<^sub>p"
  assumes "b \<in> nonzero Q\<^sub>p"
  assumes "val a = val b"
  assumes "val (a \<ominus> b) \<ge> val a + n" 
  shows "ac n a = ac n b"
proof-
  obtain m where m_def: "m = ord a"
    by simp 
  have 0: "a = (\<pp>[^]m) \<otimes> \<iota> (angular_component a)"
    by (simp add: angular_component_factors_x assms(1) m_def)
  have 1: "b = (\<pp>[^]m) \<otimes> \<iota> (angular_component b)"
  proof-
    have "ord b = ord a"
      using assms(1) assms(2) assms(3) by auto     
    then show ?thesis 
      by (metis angular_component_factors_x assms(2) m_def)
  qed    
  have 2: "(a \<ominus>b) = (\<pp>[^]m) \<otimes> \<iota> (angular_component a)
                      \<ominus>(\<pp>[^]m) \<otimes> \<iota> (angular_component b)"
    using "0" "1" by auto
  have 3: "(a \<ominus>b) = (\<pp>[^]m) \<otimes>( \<iota> (angular_component a)
                                     \<ominus> \<iota> (angular_component b))"
    using 2 assms angular_component_closed inc_closed Qp.cring_simprules Qp.r_minus_distr
    by (metis (no_types, lifting) p_intpow_closed(1))
  have 4: "(a \<ominus>b) = (\<pp>[^]m) \<otimes>( \<iota> ((angular_component a)
                                          \<ominus>\<^bsub>Z\<^sub>p\<^esub>(angular_component b)))"
    by (simp add: "3" angular_component_closed assms(1) assms(2) inc_of_diff)    
  have 5: "val (a \<ominus>b) = m + val (( \<iota> ((angular_component a)
                                          \<ominus>\<^bsub>Z\<^sub>p\<^esub>(angular_component b))))"
    by (metis "4" Zp.nonzero_one_closed angular_component_closed assms(1) assms(2)
        cring.cring_simprules(4) frac_closed local.inc_def ord_p_pow_int p_intpow_closed(1)
        p_intpow_closed(2) Zp.domain_axioms domain_def val_mult val_ord)
  have 6: "m = val a"
    using Q\<^sub>p_def assms(1) m_def by auto
  have 7: "m + val (\<iota> (angular_component a \<ominus>\<^bsub>Z\<^sub>p\<^esub> angular_component b)) \<ge> val a + n"
    using "5" assms(4) by presburger
  have 8: "m + val (\<iota> (angular_component a \<ominus>\<^bsub>Z\<^sub>p\<^esub> angular_component b)) \<ge> m + n"
    using "6" "7" 
    by (metis plus_eint_simps(1))
  have 9: "val (\<iota> (angular_component a \<ominus>\<^bsub>Z\<^sub>p\<^esub> angular_component b)) \<ge> n"
    using 8 add_le_cancel_left eint_ile eint_ord_simps(1) linear plus_eint_simps(1)
    by metis
  have 10: "val_Zp (angular_component a \<ominus>\<^bsub>Z\<^sub>p\<^esub> angular_component b) \<ge> n"
    using 9 
    by (metis angular_component_closed assms(1) assms(2) cring.cring_simprules(4)
        Zp.domain_axioms domain_def val_of_inc)
  have 11: "(angular_component a \<ominus>\<^bsub>Z\<^sub>p\<^esub> angular_component b) n = \<zero>\<^bsub>Zp_res_ring n\<^esub>"
    using 9 
    by (simp add: "10" angular_component_closed assms(1) assms(2) p_res_ring_zero zero_below_val_Zp)          
  have 12: "(angular_component a n) \<ominus>\<^bsub>Zp_res_ring n\<^esub> (angular_component b n) = \<zero>\<^bsub>Zp_res_ring n\<^esub>"
    using "11" angular_component_closed assms(2) residue_of_diff by auto
  have 13: "(angular_component a n) = (angular_component b n)"
    apply(cases "n = 0")
    apply (metis angular_component_closed assms(1) assms(2) p_res_ring_0' residues_closed)   
    using 12 angular_component_closed residue_closed ring.ring_simprules[of "Zp_res_ring n"] 
    by (meson assms(1) assms(2) cring_def prime residues.cring residues_n ring.r_right_minus_eq) 
  then show ?thesis 
    by (simp add: Qp.nonzero_memE ac_def assms(1) assms(2))
qed

lemma angular_component_nat_pow:
  assumes "a \<in> nonzero Q\<^sub>p"
  shows "angular_component (a [^] (k::nat)) = (angular_component a) [^]\<^bsub>Z\<^sub>p\<^esub> k"
  apply(induction k)
  apply (simp add: angular_component_one)
  by (simp add: Qp_nat_pow_nonzero angular_component_mult assms) 

lemma angular_component_int_pow:
  assumes "a \<in> nonzero Q\<^sub>p"
  shows "angular_component (a [^] (k::int)) = (angular_component a) [^]\<^bsub>Z\<^sub>p\<^esub> k"
  apply(cases "k \<ge> 0")
  using angular_component_nat_pow assms 
   apply (metis int_pow_int nonneg_int_cases)
proof-
  assume "\<not> 0 \<le>k"
  show "angular_component (a [^] k) = angular_component a [^] \<^bsub>Z\<^sub>p\<^esub> k"
    using angular_component_nat_pow[of a "nat (-k)"] assms 
        Qp_nat_pow_nonzero[of a] \<open>\<not> 0 \<le> k\<close> angular_component_inv[of "(a [^] k)"] int_pow_def2
    by (metis angular_component_nat_pow angular_component_inv)
qed

lemma ac_nat_pow:
  assumes "a \<in> nonzero Q\<^sub>p"
  shows "ac n (a [^] (k::nat)) = (ac n a)^ k mod (p^n)"
proof(cases "k = 0")
  case True
  show ?thesis apply(cases "n = 0")
  apply (metis Group.nat_pow_0 Qp.one_closed True ac_in_res_ring' mod_self p_res_ring_0' power_0)
  using True prime residues.one_cong residues.res_one_eq residues_n by auto
next
  case False
  show ?thesis 
    apply(cases "n = 0")
     apply (metis Qp_nat_pow_nonzero ac_in_res_ring assms mod_by_1 p_res_ring_0' power_0)
      using assms angular_component_nat_pow 
      by (metis Qp.nonzero_closed Qp.nonzero_pow_nonzero Qp.not_nonzero_memI ac_def angular_component_closed neq0_conv power_residue)
qed

lemma ac_nat_pow':
  assumes "a \<in> nonzero Q\<^sub>p"
  assumes "n \<noteq>0"
  shows "ac n (a [^] (k::nat)) = (ac n a)[^]\<^bsub>Zp_res_ring n\<^esub> k"
proof-
  have "(ac n a)^ k mod (p^n) = (ac n a)[^]\<^bsub>Zp_res_ring n\<^esub> k"
    apply(induction k)
    apply (metis Group.nat_pow_0 assms(2) prime residues.pow_cong residues_n)
    by (metis Group.nat_pow_Suc Qp_nat_pow_nonzero ac_mult' ac_nat_pow assms(1))
  then show ?thesis 
    by (simp add: ac_nat_pow assms(1))
qed

lemma ac_int_pow:
  assumes "a \<in> nonzero Q\<^sub>p"
  assumes "n > 0"
  shows "ac n (a [^] (k::int)) = (ac n a)[^]\<^bsub>Zp_res_ring n\<^esub> k"
  apply(cases "k \<ge>0") 
  using assms ac_nat_pow' 
  apply (metis int.lless_eq int.nat_pow_0 p_residues pow_nat residues_def)
  using assms ac_nat_pow' ac_inv[of "a [^] k"] ac_units[of "a [^] k"]
  by (metis Qp_nat_pow_nonzero ac_inv int_pow_def2 neq0_conv)  

lemma angular_component_p:
"angular_component \<pp> = \<one>\<^bsub>Z\<^sub>p\<^esub>"
proof-
  have "\<pp> = frac \<p> \<one>\<^bsub>Z\<^sub>p\<^esub>"
    by (simp add: Zp_nat_inc_closed local.inc_def p_inc)
  then have 0: "angular_component \<pp> = (ac_Zp \<p>) \<otimes>\<^bsub>Z\<^sub>p\<^esub> inv\<^bsub>Z\<^sub>p\<^esub> (ac_Zp \<one>\<^bsub>Z\<^sub>p\<^esub>)"
    using ac_Zp_one unfolding angular_component_def 
    by (metis Q\<^sub>p_def Qp.int_inc_closed Zp.one_nonzero Zp_int_inc_closed ac_fract 
        local.numer_denom_facts(2) local.numer_denom_facts(5) nonzero_fraction_imp_nonzero_numer
        nonzero_numer_imp_nonzero_fraction numer_nonzero p_nonzero)
  then have "angular_component \<pp> = (ac_Zp \<p>) \<otimes>\<^bsub>Z\<^sub>p\<^esub> inv\<^bsub>Z\<^sub>p\<^esub> \<one>\<^bsub>Z\<^sub>p\<^esub>"
    by (simp add: ac_Zp_one)
  then have "angular_component \<pp> = (ac_Zp \<p>)"
    by (simp add: ac_Zp_p)  
  then show ?thesis 
    using ac_Zp_p
    by simp
qed

lemma angular_component_p_nat_pow:
"angular_component (\<pp> [^] (n::nat)) = \<one>\<^bsub>Z\<^sub>p\<^esub>"
  apply(induction n)
  apply (simp add: angular_component_one)
  using angular_component_nat_pow angular_component_p nat_pow_one p_nonzero  Zp.nat_pow_one 
  by presburger

lemma angular_component_p_int_pow:
"angular_component (\<pp> [^] (n::int)) = \<one>\<^bsub>Z\<^sub>p\<^esub>"
  apply(cases "n \<ge> 0")
  apply (metis angular_component_p_nat_pow int_pow_int nonneg_int_cases)
  using angular_component_p_nat_pow[of "nat (-n)"] angular_component_inv[of "(\<pp> [^] n)"] angular_component_inv[of "\<pp> [^] (nat (-n))"] 
  by (metis (mono_tags, opaque_lifting) Group.nat_pow_0 Zp.inv_one add.inverse_neutral angular_component_one int_nat_eq
      int_pow_def2 nat_0_iff nat_int nat_zminus_int p_natpow_closed(2) )
  
lemma ac_p_nat_pow:
  assumes "k > 0"
  shows "ac k (\<pp> [^] (n::nat)) = 1"
proof-
  have "\<not> (\<pp> [^] n) = \<zero>"
    by (simp add: Qp.nonzero_memE)
  have " angular_component (\<pp> [^] n) k = 1"
    using assms angular_component_p_nat_pow[of n]  ac_def ac_one angular_component_one 
    by auto
  then show ?thesis 
    unfolding ac_def using angular_component_p_nat_pow[of n] 
    by (simp add: \<open>(\<pp> [^] n) \<noteq> \<zero>\<close>)
qed

lemma ac_p:
  assumes "k > 0"
  shows "ac k \<pp> = 1"
  by (metis Qp.int_inc_closed Qp.nat_pow_eone ac_p_nat_pow assms)

lemma ac_p_int_pow:
  assumes "k > 0"
  shows "ac k (\<pp> [^] (n::int)) = 1"
  using Qp.nonzero_memE(2) ac_def ac_one' angular_component_one angular_component_p_int_pow
        assms p_intpow_closed(2) p_res_ring_one by auto
  
lemma angular_component_p_nat_pow_factor:
  assumes "a \<in> nonzero Q\<^sub>p"
  shows "angular_component ((\<pp> [^] (n::nat)) \<otimes> a) = angular_component a"
proof-
  have 0: "angular_component ((\<pp> [^] n) \<otimes> a) = angular_component (\<pp> [^] n) \<otimes>\<^bsub>Z\<^sub>p\<^esub> angular_component a"
    using assms angular_component_mult[of "(\<pp> [^] (n::nat))" a] p_natpow_closed(2) 
    by blast
  have 1: "angular_component (\<pp> [^] n) = \<one>\<^bsub>Z\<^sub>p\<^esub>"
    by (simp add: angular_component_p_nat_pow)
  have 2: "angular_component ((\<pp> [^] n) \<otimes> a) = \<one>\<^bsub>Z\<^sub>p\<^esub> \<otimes>\<^bsub>Z\<^sub>p\<^esub> angular_component a"
    by (simp add: "0" "1")
  then show ?thesis using angular_component_closed[of a] assms Zp.domain_axioms
    by (simp add: assms cring.cring_simprules(12) domain.axioms(1))
qed

lemma ac_p_nat_pow_factor:
  assumes "m > 0"
  assumes "a \<in> nonzero Q\<^sub>p"
  shows "ac m ((\<pp> [^] (n::nat)) \<otimes> a) = ac m a"
  using angular_component_p_nat_pow_factor assms  ac_def 
  by (metis (no_types, lifting) Qp.field_axioms Qp_nat_pow_nonzero Qp.nonzero_memE 
      Qp.nonzero_memE Ring.integral p_nonzero)
  
lemma angular_component_p_nat_pow_factor_right:
  assumes "a \<in> nonzero Q\<^sub>p"
  shows "angular_component (a \<otimes> (\<pp> [^] (n::nat))) = angular_component a"
proof-
  have "((\<pp> [^] (n::nat)) \<otimes> a) = (a \<otimes> (\<pp> [^] (n::nat)))"
    using assms Qp.domain_axioms domain_def 
    by (simp add: assms domain_def Qp.nonzero_memE cring.cring_simprules(14))
  then show ?thesis 
    using angular_component_p_nat_pow_factor[of a n] 
    by (simp add: assms)
qed

lemma ac_p_nat_pow_factor_right:
  assumes "m > 0"
  assumes "a \<in> carrier Q\<^sub>p"
  shows "ac m (a \<otimes> (\<pp> [^] (n::nat))) = ac m a"
  using assms angular_component_p_nat_pow_factor_right[of a n] 
  unfolding ac_def 
  by (metis Qp.integral Qp.l_null Qp.not_nonzero_memE Qp.not_nonzero_memI
      angular_component_p_nat_pow_factor_right p_natpow_closed(1) p_natpow_closed(2))

lemma angular_component_p_int_pow_factor:
  assumes "a \<in> carrier Q\<^sub>p"
  shows "angular_component ((\<pp> [^] (n::int)) \<otimes> a) = angular_component a"
  by (metis Qp.integral_iff Qp.l_one Qp.nonzero_memI Qp.one_nonzero angular_component_mult
      angular_component_one angular_component_p_int_pow assms p_intpow_closed(1) p_intpow_closed(2))
  
lemma ac_p_int_pow_factor:
  assumes "a \<in> nonzero Q\<^sub>p"
  shows "ac m ((\<pp> [^] (n::int)) \<otimes> a) = ac m a"
  apply(cases "m = 0")
   apply (metis (no_types, lifting) Qp.integral Qp.nonzero_closed Qp.nonzero_memE(2) 
          ac_def angular_component_p_int_pow_factor assms p_intpow_closed(2))
  using assms angular_component_p_int_pow_factor[of a n]
  by (metis (no_types, lifting) Qp.integral Qp.nonzero_closed Qp.not_nonzero_memI ac_def 
      p_intpow_closed(2))

lemma angular_component_p_int_pow_factor_right:
  assumes "a \<in> carrier Q\<^sub>p"
  shows "angular_component (a \<otimes> (\<pp> [^] (n::int))) = angular_component a"
  using Qp.m_comm angular_component_p_int_pow_factor assms p_intpow_closed(1) by auto

lemma ac_p_int_pow_factor_right:
  assumes "a \<in> carrier Q\<^sub>p"
  shows "ac m (a \<otimes> (\<pp> [^] (n::int))) = ac m a"
  using assms angular_component_p_int_pow_factor_right unfolding ac_def 
  using Qp.integral_iff Qp.nonzero_memE(2) p_intpow_closed(1) p_intpow_closed(2) by presburger


(**************************************************************************************************)
(**************************************************************************************************)
subsection\<open>An Inverse for the inclusion map $\iota$\<close>
(**************************************************************************************************)
(**************************************************************************************************)

definition to_Zp where 
"to_Zp a = (if (a \<in> \<O>\<^sub>p) then (SOME x. x \<in> carrier Z\<^sub>p \<and> \<iota> x = a) else \<zero>\<^bsub>Z\<^sub>p\<^esub>)"

lemma to_Zp_closed:
  assumes "a \<in> carrier Q\<^sub>p"
  shows "to_Zp a \<in> carrier Z\<^sub>p"
  apply(cases "a \<in> \<O>\<^sub>p")
  using assms unfolding to_Zp_def \<iota>_def 
  apply (smt image_iff tfl_some)
    by simp

lemma to_Zp_inc: 
  assumes "a \<in> \<O>\<^sub>p"
  shows "\<iota> (to_Zp a) = a"
proof-
  obtain c where c_def: "c = (SOME x. x \<in> carrier Z\<^sub>p \<and> \<iota> x = a)"
    by simp
  have "(\<exists> x. x \<in> carrier Z\<^sub>p \<and> \<iota> x = a)"
    using assms(1) 
    by blast
  then  have "c \<in> carrier Z\<^sub>p \<and> \<iota> c = a"
    using c_def 
    by (metis (mono_tags, lifting)  tfl_some)
  then show "\<iota> (to_Zp a) = a" 
    using to_Zp_def c_def assms(1) 
    by auto 
qed

lemma inc_to_Zp: 
 assumes "b \<in> carrier Z\<^sub>p"
 shows "to_Zp (\<iota> b) = b"
proof-
  have "\<iota> (to_Zp (\<iota> b)) = (\<iota> b)"
    using assms to_Zp_inc[of "\<iota> b"]
    by blast
  then show ?thesis 
    using inc_inj2[of b "to_Zp (\<iota> b)"] assms to_Zp_closed inc_closed 
    unfolding \<iota>_def Q\<^sub>p_def 
    by auto      
qed

lemma to_Zp_add: 
  assumes "a \<in> \<O>\<^sub>p"
  assumes "b \<in> \<O>\<^sub>p"
  shows "to_Zp (a \<oplus> b) = to_Zp a \<oplus>\<^bsub>Z\<^sub>p\<^esub> (to_Zp b)"
  by (metis (no_types, lifting) Zp.domain_axioms assms(1) assms(2)
      cring.cring_simprules(1) domain.axioms(1) imageE inc_of_sum inc_to_Zp)

lemma to_Zp_mult: 
  assumes "a \<in> \<O>\<^sub>p"
  assumes "b \<in> \<O>\<^sub>p"
  shows "to_Zp (a \<otimes> b) = to_Zp a \<otimes>\<^bsub>Z\<^sub>p\<^esub> (to_Zp b)"
proof-
  have "(a \<otimes> b) \<in> \<O>\<^sub>p"
    by (simp add: val_ring_subring assms(1) assms(2) subringE(6))
  then have 
    "\<iota> ((to_Zp a) \<otimes>\<^bsub>Z\<^sub>p\<^esub> (to_Zp) b) =  ((\<iota> (to_Zp a)) \<otimes> (\<iota> (to_Zp b)))"
    using assms(1) assms(2) inc_of_prod inc_to_Zp 
    by auto
  then have "\<iota> ((to_Zp a) \<otimes>\<^bsub>Z\<^sub>p\<^esub> (to_Zp) b) =  a \<otimes>b"
    by (simp add: assms(1) assms(2) to_Zp_inc)
  then have "to_Zp ( \<iota> ((to_Zp a) \<otimes>\<^bsub>Z\<^sub>p\<^esub> (to_Zp) b)) = to_Zp (a \<otimes>b)"
    by simp
  then show ?thesis 
    by (metis (no_types, opaque_lifting) Zp.domain_axioms val_ring_subring assms(1) assms(2) 
        cring.cring_simprules(5) domain.axioms(1) inc_to_Zp subringE(1) subset_iff to_Zp_closed)
qed

lemma to_Zp_minus:
  assumes "a \<in> \<O>\<^sub>p"
  assumes "b \<in> \<O>\<^sub>p"
  shows "to_Zp (a \<ominus> b) = to_Zp a \<ominus>\<^bsub>Z\<^sub>p\<^esub> (to_Zp b)"
  by (metis (no_types, lifting) Zp.domain_axioms assms(1) assms(2) cring_def domain.axioms(1)
      image_iff inc_of_diff inc_to_Zp ring.ring_simprules(4))

lemma to_Zp_one: 
  shows "to_Zp \<one> = \<one>\<^bsub>Z\<^sub>p\<^esub>"
  using Zp_def Zp.one_closed \<iota>_def inc_of_one inc_to_Zp padic_integers_axioms 
  by fastforce

lemma to_Zp_zero: 
  shows "to_Zp \<zero> = \<zero>\<^bsub>Z\<^sub>p\<^esub>"
  using Q\<^sub>p_def Zp_def Zp.domain_axioms \<iota>_def domain_frac.inc_inj1 inc_to_Zp 
        padic_integers_axioms to_Zp_def domain_frac_axioms by fastforce

lemma to_Zp_ominus:
  assumes "a \<in> \<O>\<^sub>p"
  shows "to_Zp (\<ominus> a) = \<ominus>\<^bsub>Z\<^sub>p\<^esub> (to_Zp a)"
proof-
  have "\<ominus>a \<in> \<O>\<^sub>p"
    by (simp add: val_ring_subring assms subringE(5))
  then show ?thesis 
    by (metis (no_types, lifting) Zp.domain_axioms Zp.nonzero_one_closed assms
        cring.cring_simprules(3) domain.axioms(1) frac_uminus image_iff inc_to_Zp local.inc_def)
qed

lemma to_Zp_val:
  assumes "a \<in> \<O>\<^sub>p"
  shows "val_Zp (to_Zp a) = val a"
  by (metis assms imageE inc_to_Zp val_of_inc)

lemma val_of_nat_inc:
"val ([(k::nat)]\<cdot>\<one>) \<ge> 0"
proof-
  have "[(k::nat)]\<cdot>\<one> \<in> \<O>\<^sub>p"
    by (metis Zp.one_closed Zp_nat_mult_closed image_eqI inc_of_nat)
  thus ?thesis 
    using val_ring_memE(1) by blast
qed

lemma val_of_int_inc:
"val ([(k::int)]\<cdot>\<one>) \<ge> 0"
proof-
  have "\<iota> ([k] \<cdot>\<^bsub>Z\<^sub>p\<^esub> \<one>\<^bsub>Z\<^sub>p\<^esub>) = [k]\<cdot>\<one>"
    using inc_of_int by blast
  hence "[k]\<cdot>\<one> \<in> \<O>\<^sub>p"
    using Zp.one_closed Zp_nat_mult_closed image_eqI inc_of_int 
    by blast    
  thus ?thesis 
    using val_ring_memE(1) by blast
qed

lemma to_Zp_nat_inc:
"to_Zp ([(a::nat)]\<cdot>\<one>) = [a]\<cdot>\<^bsub>Z\<^sub>p\<^esub>\<one> \<^bsub>Z\<^sub>p\<^esub>"
  apply(induction a)
  using Qp.nat_inc_zero Zp.nat_inc_zero to_Zp_zero apply presburger
proof-
  fix a::nat assume A: "to_Zp ([a] \<cdot> \<one>) = [a] \<cdot>\<^bsub>Z\<^sub>p\<^esub> \<one>\<^bsub>Z\<^sub>p\<^esub>"
  have 0: "[(Suc a)]\<cdot>\<one> = [a]\<cdot>\<one> \<oplus> \<one>"
    using Qp.add.nat_pow_Suc by blast
  have 1: "[a]\<cdot>\<one> \<in> \<O>\<^sub>p"
    using Qp.nat_inc_closed val_of_nat_inc val_ring_memI by blast
  have 2: "to_Zp ([Suc a] \<cdot> \<one>) = (to_Zp ([a]\<cdot>\<one>)) \<oplus>\<^bsub>Z\<^sub>p\<^esub> \<one>\<^bsub>Z\<^sub>p\<^esub>"
    using A 1 unfolding 0 
    by (metis Zp.cring_simprules(6) Zp.nat_inc_closed inc_of_nat inc_of_one inc_of_sum inc_to_Zp sum_closed)
  show "to_Zp ([Suc a] \<cdot> \<one>) = [Suc a] \<cdot>\<^bsub>Z\<^sub>p\<^esub> \<one>\<^bsub>Z\<^sub>p\<^esub>"
    unfolding  2 A 
    using add_comm nat_suc by presburger
qed

lemma to_Zp_int_neg:
"to_Zp ([(-int (a::nat))]\<cdot>\<one>) = \<ominus>\<^bsub>Z\<^sub>p\<^esub>([int a]\<cdot>\<^bsub>Z\<^sub>p\<^esub>\<one> \<^bsub>Z\<^sub>p\<^esub>)"
proof-
  have 0: "[(-int (a::nat))]\<cdot>\<one> = \<ominus> ([int a]\<cdot>\<one>)"
    using Qp.add.int_pow_neg by blast
  have 1: "[int a]\<cdot>\<one> \<in> \<O>\<^sub>p"
    using Qp.int_inc_closed val_of_int_inc val_ring_memI by blast
  show ?thesis using 1 unfolding 0 
    by (metis Zp.int_inc_closed inc_of_int inc_to_Zp to_Zp_ominus)
qed

lemma(in ring) int_add_pow:
"[int n] \<cdot> \<one> = [n]\<cdot>\<one>"
  unfolding add_pow_def 
  by (simp add: int_pow_int)

lemma int_add_pow:
"[int n] \<cdot> \<one> = [n]\<cdot>\<one>"
  unfolding add_pow_def 
  by (simp add: int_pow_int)

lemma Zp_int_add_pow:
"[int n] \<cdot>\<^bsub>Z\<^sub>p\<^esub> \<one>\<^bsub>Z\<^sub>p\<^esub> = [n]\<cdot>\<^bsub>Z\<^sub>p\<^esub>\<one>\<^bsub>Z\<^sub>p\<^esub>"
  unfolding add_pow_def 
  by (simp add: int_pow_int)

lemma to_Zp_int_inc:
"to_Zp ([(a::int)]\<cdot>\<one>) = ([a]\<cdot>\<^bsub>Z\<^sub>p\<^esub>\<one> \<^bsub>Z\<^sub>p\<^esub>)"
  apply(induction a)
  unfolding int_add_pow Zp_int_add_pow
    using to_Zp_nat_inc apply blast
    unfolding to_Zp_int_neg using  Zp.add.int_pow_neg Zp.one_closed 
    by presburger

lemma to_Zp_nat_add_pow:
  assumes "a \<in> \<O>\<^sub>p"
  shows "to_Zp ([(n::nat)]\<cdot>a) = [n]\<cdot>\<^bsub>Z\<^sub>p\<^esub> to_Zp a"
  apply( induction n)
  using Qp.nat_mult_zero Zp_nat_inc_zero to_Zp_zero apply presburger
proof- fix n::nat assume A: "to_Zp ([n] \<cdot> a) = [n] \<cdot>\<^bsub>Z\<^sub>p\<^esub> to_Zp a"
  have 0: "[Suc n] \<cdot> a = [n]\<cdot>a \<oplus> a"
    using Qp.add.nat_pow_Suc by blast
  have 1: "to_Zp ([n] \<cdot> a \<oplus> a) = to_Zp ([n] \<cdot> a) \<oplus>\<^bsub>Z\<^sub>p\<^esub> to_Zp a"
    apply(rule to_Zp_add[of "[n]\<cdot>a" a] )
    apply( induction n) 
    using Qp.nat_mult_zero zero_in_val_ring apply blast
    unfolding Qp.add.nat_pow_Suc by(rule val_ring_add_closed, blast, rule assms, rule assms)
  show "to_Zp ([Suc n] \<cdot> a) = [Suc n] \<cdot>\<^bsub>Z\<^sub>p\<^esub> to_Zp a "
    unfolding Qp.add.nat_pow_Suc Zp.add.nat_pow_Suc 1 A by blast 
qed

lemma val_ring_res:
  assumes "a \<in> \<O>\<^sub>p"
  assumes "b \<in> \<O>\<^sub>p"
  shows "to_Zp (a \<ominus> b) N = to_Zp a N \<ominus>\<^bsub>Zp_res_ring N\<^esub> to_Zp b N"
proof-
  have "to_Zp (a \<ominus> b) N = (to_Zp a \<ominus>\<^bsub>Z\<^sub>p\<^esub> to_Zp b) N"
    using assms to_Zp_minus by presburger
  then show ?thesis using assms residue_of_diff to_Zp_closed val_ring_memE(2)
    by (simp add: val_ring_memE(1))
qed

lemma res_diff_in_val_ring_imp_in_val_ring:
  assumes "a \<in> \<O>\<^sub>p"
  assumes "b \<in> carrier Q\<^sub>p"
  assumes "a \<ominus> b \<in> \<O>\<^sub>p"
  shows "b \<in> \<O>\<^sub>p"
proof-
  have "b = a \<ominus> (a \<ominus> b)"
    unfolding a_minus_def 
    using assms val_ring_memE(2)[of a] Qp.r_neg2 Q\<^sub>p_def Qp.minus_sum by auto
  thus ?thesis  using assms val_ring_minus_closed[of a "a \<ominus> b"]
    by presburger
qed

lemma(in padic_fields) equal_res_imp_res_diff_zero:
  assumes "a \<in> \<O>\<^sub>p"
  assumes "b \<in> \<O>\<^sub>p"
  assumes "to_Zp a N = to_Zp b N"
  shows "to_Zp (a \<ominus> b) N = 0"
  using val_ring_res[of a b] assms 
  by (metis res_diff_zero_fact' to_Zp_closed val_ring_memE(2))

lemma(in padic_fields) equal_res_imp_val_diff_bound:
  assumes "a \<in> \<O>\<^sub>p"
  assumes "b \<in> \<O>\<^sub>p"
  assumes "to_Zp a N = to_Zp b N"
  shows "val (a \<ominus> b) \<ge> N"
  using assms equal_res_imp_res_diff_zero[of a b N]
  by (metis to_Zp_closed to_Zp_minus to_Zp_val val_Zp_dist_def val_Zp_dist_res_eq2 val_ring_memE(2) val_ring_minus_closed) 
  
lemma(in padic_fields) equal_res_equal_val:
  assumes "a \<in> \<O>\<^sub>p"
  assumes "b \<in> \<O>\<^sub>p"
  assumes "val a < N"
  assumes "to_Zp a N = to_Zp b N"
  shows "val a = val b"
proof-
  have "val (a \<ominus> b) \<ge> N"
    using assms equal_res_imp_val_diff_bound by blast 
  then have "val (a \<ominus> b) > val a"
    using assms less_le_trans by blast
  then show "val a = val b"
    using assms by (meson ultrametric_equal_eq' val_ring_memE)
qed

lemma(in padic_fields) val_ring_equal_res_imp_equal_val:
  assumes "a \<in> \<O>\<^sub>p"
  assumes "b \<in> \<O>\<^sub>p"
  assumes "val a < eint N"
  assumes "val b < eint N"
  assumes "to_Zp a N = to_Zp b N"
  shows "val a = val b"
proof-
  have "val_Zp (to_Zp (a \<ominus> b)) \<ge> N"
    using assms val_ring_memE to_Zp_closed to_Zp_minus val_Zp_dist_def val_Zp_dist_res_eq2 by presburger
  thus ?thesis 
    by (meson assms(1) assms(2) assms(3) assms(5) equal_res_equal_val) 
qed

end
end
