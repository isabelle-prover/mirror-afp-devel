section \<open>Characteristic of Rings\label{sec:ring_char}\<close>

theory Ring_Characteristic
  imports 
    "Finite_Fields_Factorization_Ext"
    "HOL-Algebra.IntRing" 
    "HOL-Algebra.Embedded_Algebras"
begin

locale finite_field = field +
  assumes finite_carrier: "finite (carrier R)"
begin

lemma finite_field_min_order:
  "order R > 1"
proof (rule ccontr)
  assume a:"\<not>(1 < order R)"
  have "{\<zero>\<^bsub>R\<^esub>,\<one>\<^bsub>R\<^esub>} \<subseteq> carrier R" by auto
  hence "card {\<zero>\<^bsub>R\<^esub>,\<one>\<^bsub>R\<^esub>} \<le> card (carrier R)"
    using card_mono finite_carrier by blast
  also have "... \<le> 1" using a by (simp add:order_def)
  finally have "card {\<zero>\<^bsub>R\<^esub>,\<one>\<^bsub>R\<^esub>} \<le> 1" by blast
  thus "False" by simp
qed

lemma (in finite_field) order_pow_eq_self:
  assumes "x \<in> carrier R"
  shows "x [^] (order R) = x"
proof (cases "x = \<zero>")
  case True
  have "order R > 0"
    using assms(1) order_gt_0_iff_finite finite_carrier by simp
  then obtain n where n_def:"order R = Suc n" 
    using lessE by blast
  have "x [^] (order R) = \<zero>" 
    unfolding n_def using True by (subst nat_pow_Suc, simp)
  thus ?thesis using True by simp
next
  case False
  have x_carr:"x \<in> carrier (mult_of R)"
    using False assms by simp

  have carr_non_empty: "card (carrier R) > 0" 
    using order_gt_0_iff_finite finite_carrier
    unfolding order_def by simp
  have "x [^] (order R) = x [^]\<^bsub>mult_of R\<^esub> (order R)"
    by (simp add:nat_pow_mult_of)
  also have "... = x [^]\<^bsub>mult_of R\<^esub> (order (mult_of R)+1)"
    using carr_non_empty unfolding order_def
    by (intro arg_cong[where f="\<lambda>t. x [^]\<^bsub>mult_of R\<^esub> t"]) (simp)
  also have "... = x"
    using x_carr
    by (simp add:mult_of.pow_order_eq_1)
  finally show "x [^] (order R) = x"
    by simp
qed

lemma (in finite_field) order_pow_eq_self':
  assumes "x \<in> carrier R"
  shows "x [^] (order R ^ d) = x"
proof (induction d)
  case 0
  then show ?case using assms by simp
next
  case (Suc d)
  have "x [^] order R ^ (Suc d) = x [^] (order R ^ d * order R)"
    by (simp add:mult.commute)
  also have "... = (x [^] (order R ^ d)) [^] order R"
    using assms by (simp add: nat_pow_pow)
  also have "... = (x [^] (order R ^ d))"
    using order_pow_eq_self assms by simp
  also have "... = x"
    using Suc by simp
  finally show ?case by simp
qed

end

lemma finite_fieldI:
  assumes "field R"
  assumes "finite (carrier R)"
  shows "finite_field R"
  using assms
  unfolding finite_field_def finite_field_axioms_def
  by auto

lemma (in domain) finite_domain_units:
  assumes "finite (carrier R)"
  shows "Units R = carrier R - {\<zero>}" (is "?lhs = ?rhs")
proof 
  have "Units R \<subseteq> carrier R" by (simp add:Units_def) 
  moreover have "\<zero> \<notin> Units R"
    by (meson zero_is_prime(1) primeE)
  ultimately show "Units R \<subseteq> carrier R - {\<zero>}" by blast
next
  have "x \<in> Units R" if a: "x \<in> carrier R - {\<zero>}" for x
  proof -
    have x_carr: "x \<in> carrier R" using a by blast
    define f where "f = (\<lambda>y. y \<otimes>\<^bsub>R\<^esub> x)"
    have "inj_on f (carrier R)" unfolding f_def
      by (rule inj_onI, metis DiffD1 DiffD2 a m_rcancel insertI1)
    hence "card (carrier R) = card (f ` carrier R)"
      by (metis card_image)
    moreover have "f ` carrier R \<subseteq> carrier R" unfolding f_def
      by (rule image_subsetI, simp add: ring.ring_simprules x_carr)
    ultimately have "f ` carrier R = carrier R"
      using card_subset_eq assms by metis
    moreover have "\<one>\<^bsub>R\<^esub> \<in> carrier R" by simp
    ultimately have "\<exists>y \<in> carrier R. f y = \<one>\<^bsub>R\<^esub>" 
      by (metis image_iff)
    then obtain y 
      where y_carrier: "y \<in> carrier R" 
        and y_left_inv: "y \<otimes>\<^bsub>R\<^esub> x = \<one>\<^bsub>R\<^esub>" 
      using f_def by blast
    hence  y_right_inv: "x \<otimes>\<^bsub>R\<^esub> y = \<one>\<^bsub>R\<^esub>"
      by (metis DiffD1 a cring_simprules(14))
    show "x \<in> Units R"
      using y_carrier y_left_inv y_right_inv
      by (metis DiffD1 a divides_one factor_def)
  qed
  thus "?rhs \<subseteq> ?lhs" by auto
qed

text \<open>The following theorem can be found in Lidl and Niederreiter~\<^cite>\<open>\<open>Theorem 1.31\<close> in "lidl1986"\<close>.\<close>

theorem finite_domains_are_fields:
  assumes "domain R"
  assumes "finite (carrier R)"
  shows "finite_field R"
proof -
  interpret domain R using assms by auto
  have "Units R = carrier R - {\<zero>\<^bsub>R\<^esub>}"
    using finite_domain_units[OF assms(2)] by simp
  then have "field R"
    by (simp add: assms(1) field.intro field_axioms.intro)
  thus ?thesis
    using assms(2) finite_fieldI by auto 
qed

definition zfact_iso :: "nat \<Rightarrow> nat \<Rightarrow> int set" where
  "zfact_iso p k = Idl\<^bsub>\<Z>\<^esub> {int p} +>\<^bsub>\<Z>\<^esub> (int k)"

context
  fixes n :: nat
  assumes n_gt_0: "n > 0"
begin

private abbreviation I where "I \<equiv> Idl\<^bsub>\<Z>\<^esub> {int n}"

private lemma ideal_I: "ideal I \<Z>"
  by (simp add: int.genideal_ideal)

lemma int_cosetI:
  assumes "u mod (int n) = v mod (int n)"
  shows "Idl\<^bsub>\<Z>\<^esub> {int n} +>\<^bsub>\<Z>\<^esub> u = Idl\<^bsub>\<Z>\<^esub> {int n} +>\<^bsub>\<Z>\<^esub> v"
proof -
  have "u - v \<in> I"
    by (metis Idl_subset_eq_dvd assms int_Idl_subset_ideal mod_eq_dvd_iff)
  thus ?thesis
    using ideal_I int.quotient_eq_iff_same_a_r_cos by simp
qed

lemma zfact_iso_inj:
  "inj_on (zfact_iso n) {..<n}"
proof (rule inj_onI)
  fix x y
  assume a:"x \<in> {..<n}" "y \<in> {..<n}"
  assume "zfact_iso n x = zfact_iso n y"
  hence "I +>\<^bsub>\<Z>\<^esub> (int x) = I +>\<^bsub>\<Z>\<^esub> (int y)"
    by (simp add:zfact_iso_def)
  hence "int x - int y \<in> I"
    by (subst int.quotient_eq_iff_same_a_r_cos[OF ideal_I], auto)
  hence "int x mod int n = int y mod int n"
    by (meson Idl_subset_eq_dvd int_Idl_subset_ideal mod_eq_dvd_iff)
  thus "x = y"
    using a by simp
qed

lemma zfact_iso_ran:
  "zfact_iso n ` {..<n} = carrier (ZFact (int n))"
proof -
  have "zfact_iso n ` {..<n} \<subseteq> carrier (ZFact (int n))"
    unfolding zfact_iso_def ZFact_def FactRing_simps 
    using int.a_rcosetsI by auto
  moreover have "x \<in> zfact_iso n ` {..<n}" 
    if a:"x \<in> carrier (ZFact (int n))" for x
  proof -
    obtain y where y_def: "x = I +>\<^bsub>\<Z>\<^esub> y"
      using a unfolding ZFact_def FactRing_simps by auto
    define z where \<open>z = nat (y mod int n)\<close>
    with n_gt_0 have z_def: \<open>int z mod int n = y mod int n\<close> \<open>z < n\<close>
      by (simp_all add: z_def nat_less_iff)
    have "x = I  +>\<^bsub>\<Z>\<^esub> y"
      by (simp add:y_def)
    also have "... = I +>\<^bsub>\<Z>\<^esub> (int z)"
      by (intro int_cosetI, simp add:z_def)
    also have "... = zfact_iso n z"
      by (simp add:zfact_iso_def)
    finally have "x = zfact_iso n z"
      by simp
    thus "x \<in> zfact_iso n ` {..<n}"
      using z_def(2) by blast
  qed
  ultimately show ?thesis by auto
qed

lemma zfact_iso_bij:
  "bij_betw (zfact_iso n) {..<n} (carrier (ZFact (int n)))"
  using  bij_betw_def zfact_iso_inj zfact_iso_ran by blast

lemma card_zfact_carr: "card (carrier (ZFact (int n))) = n"
  using bij_betw_same_card[OF zfact_iso_bij] by simp

lemma fin_zfact: "finite (carrier (ZFact (int n)))"
  using card_zfact_carr n_gt_0 card_ge_0_finite by force

end

lemma zfact_prime_is_finite_field:
  assumes "Factorial_Ring.prime p"
  shows "finite_field (ZFact (int p))"
proof -
  have p_gt_0: "p > 0" using assms(1) prime_gt_0_nat by simp
  have "Factorial_Ring.prime (int p)" 
    using assms by simp
  moreover have "finite (carrier (ZFact (int p)))" 
    using fin_zfact[OF p_gt_0] by simp
  ultimately show ?thesis
    by (intro finite_domains_are_fields ZFact_prime_is_domain, auto)
qed

definition int_embed :: "_ \<Rightarrow> int \<Rightarrow> _"  where
  "int_embed R k = add_pow R k \<one>\<^bsub>R\<^esub>"

lemma (in ring) add_pow_consistent:
  fixes i :: "int"
  assumes "subring K R"
  assumes "k \<in> K"
  shows "add_pow R i k = add_pow (R \<lparr> carrier := K \<rparr>) i k"
    (is "?lhs = ?rhs")
proof -
  have a:"subgroup K (add_monoid R)" 
    using assms(1) subring.axioms by auto
  have "add_pow R i k = k [^]\<^bsub>add_monoid R\<lparr>carrier := K\<rparr>\<^esub> i" 
    using add.int_pow_consistent[OF a assms(2)] by simp
  also have "... = ?rhs"
    unfolding add_pow_def by simp
  finally show ?thesis by simp
qed

lemma (in ring) int_embed_consistent:
  assumes "subring K R"
  shows "int_embed R i = int_embed (R \<lparr> carrier := K \<rparr>) i"
proof -
  have a:"\<one> = \<one>\<^bsub>R \<lparr> carrier := K \<rparr>\<^esub>" by simp
  have b:"\<one>\<^bsub>R\<lparr>carrier := K\<rparr>\<^esub> \<in> K" 
    using assms subringE(3) by auto
  show ?thesis
    unfolding int_embed_def a using b add_pow_consistent[OF assms(1)] by simp
qed

lemma (in ring) int_embed_closed:
  "int_embed R k \<in> carrier R"
  unfolding int_embed_def using add.int_pow_closed by simp

lemma (in ring) int_embed_range:
  assumes "subring K R"
  shows "int_embed R k \<in> K"
proof -
  let ?R' =  "R \<lparr> carrier := K \<rparr>"
  interpret x:ring ?R'
    using subring_is_ring[OF assms] by simp
  have "int_embed R k = int_embed ?R' k"
    using int_embed_consistent[OF assms] by simp
  also have "...  \<in> K"
    using x.int_embed_closed by simp
  finally show ?thesis by simp
qed

lemma (in ring) int_embed_zero:
  "int_embed R 0 = \<zero>\<^bsub>R\<^esub>"
  by (simp add:int_embed_def add_pow_def)  

lemma (in ring) int_embed_one:
  "int_embed R 1 = \<one>\<^bsub>R\<^esub>"
  by (simp add:int_embed_def)  

lemma (in ring) int_embed_add:
  "int_embed R (x+y) = int_embed R x \<oplus>\<^bsub>R\<^esub> int_embed R y"
  by (simp add:int_embed_def add.int_pow_mult)  

lemma (in ring) int_embed_inv:
  "int_embed R (-x) = \<ominus>\<^bsub>R\<^esub> int_embed R x" (is "?lhs = ?rhs")
proof -
  have "?lhs = int_embed R (-x) \<oplus> (int_embed R x \<ominus> int_embed R x)"
    using int_embed_closed by simp
  also have 
    "... = int_embed R (-x) \<oplus> int_embed R x \<oplus> (\<ominus> int_embed R x)"
    using int_embed_closed by (subst a_minus_def, subst a_assoc, auto)
  also have "... = int_embed R (-x +x) \<oplus> (\<ominus> int_embed R x)"
    by (subst int_embed_add, simp)
  also have "... = ?rhs"
    using int_embed_closed
    by (simp add:int_embed_zero)
  finally show ?thesis by simp
qed

lemma (in ring) int_embed_diff:
  "int_embed R (x-y) = int_embed R x \<ominus>\<^bsub>R\<^esub> int_embed R y"
  (is "?lhs = ?rhs")
proof -
  have "?lhs = int_embed R (x + (-y))"  by simp
  also have "... = ?rhs"
    by (subst int_embed_add, simp add:a_minus_def int_embed_inv)
  finally show ?thesis by simp
qed

lemma (in ring) int_embed_mult_aux:
  "int_embed R (x*int y) = int_embed R x \<otimes> int_embed R y"
proof (induction y)
  case 0
  then show ?case by (simp add:int_embed_closed int_embed_zero)
next
  case (Suc y)
  have "int_embed R (x * int (Suc y)) = int_embed R (x + x * int y)"
    by (simp add:algebra_simps) 
  also have "... = int_embed R x \<oplus> int_embed R (x * int y)"
    by (subst int_embed_add, simp)
  also have 
    "... = int_embed R x \<otimes> \<one> \<oplus> int_embed R x \<otimes> int_embed R y"
    using int_embed_closed
    by (subst Suc, simp)
  also have "... = int_embed R x \<otimes> (int_embed R 1 \<oplus> int_embed R y)"
    using int_embed_closed by (subst r_distr, simp_all add:int_embed_one)
  also have "... = int_embed R x \<otimes> int_embed R (1+int y)"
    by (subst int_embed_add, simp)
  also have "... = int_embed R x \<otimes> int_embed R (Suc y)"
    by simp
  finally show ?case by simp
qed

lemma (in ring) int_embed_mult:
  "int_embed R (x*y) = int_embed R x \<otimes>\<^bsub>R\<^esub> int_embed R y"
proof (cases "y \<ge> 0")
  case True
  then obtain y' where y_def: "y = int y'"
    using nonneg_int_cases by auto
  have "int_embed R (x * y) = int_embed R (x * int y')"
    unfolding y_def by simp
  also have "... = int_embed R x \<otimes> int_embed R y'"
    by (subst int_embed_mult_aux, simp)
  also have "... = int_embed R x \<otimes> int_embed R y"
    unfolding y_def by simp
  finally show ?thesis by simp
next
  case False
  then obtain y' where y_def: "y = - int y'" 
    by (meson nle_le nonpos_int_cases)
  have "int_embed R (x * y) = int_embed R (-(x * int y'))"
    unfolding y_def by simp
  also have "... = \<ominus> (int_embed R (x * int y'))"
    by (subst int_embed_inv, simp)
  also have "... = \<ominus> (int_embed R x \<otimes> int_embed R y')"
    by (subst int_embed_mult_aux, simp)
  also have "... = int_embed R x \<otimes> \<ominus> int_embed R y'"
    using int_embed_closed by algebra
  also have "... = int_embed R x \<otimes> int_embed R (-y')"
    by (subst int_embed_inv, simp)
  also have "... = int_embed R x \<otimes> int_embed R y"
    unfolding y_def by simp
  finally show ?thesis by simp
qed

lemma (in ring) int_embed_ring_hom: 
  "ring_hom_ring int_ring R (int_embed R)"
proof (rule ring_hom_ringI) 
  show "ring int_ring" using int.ring_axioms by simp
  show "ring R" using ring_axioms by simp
  show "int_embed R x \<in> carrier R" if "x \<in> carrier \<Z>" for x
    using int_embed_closed by simp
  show "int_embed R (x\<otimes>\<^bsub>\<Z>\<^esub>y) = int_embed R x \<otimes> int_embed R y" 
    if "x \<in> carrier \<Z>" "y \<in> carrier \<Z>" for x y 
    using int_embed_mult by simp
  show "int_embed R (x\<oplus>\<^bsub>\<Z>\<^esub>y) = int_embed R x \<oplus> int_embed R y" 
    if "x \<in> carrier \<Z>" "y \<in> carrier \<Z>" for x y 
    using int_embed_add by simp
  show "int_embed R \<one>\<^bsub>\<Z>\<^esub> = \<one>"
    by (simp add:int_embed_one)
qed

abbreviation char_subring where
  "char_subring R \<equiv> int_embed R ` UNIV"

definition char where 
  "char R = card (char_subring R)"

text \<open>This is a non-standard definition for the characteristic of a ring. 

Commonly~\<^cite>\<open>\<open>Definition 1.43\<close> in "lidl1986"\<close> it is defined to be the smallest natural number $n$ such
that n-times repeated addition of any number is zero. If no such number exists then it is defined 
to be $0$. In the case of rings with unit elements --- not that the locale @{locale "ring"} requires
unit elements --- the above definition can be simplified to the number of times the unit elements
needs to be repeatedly added to reach $0$.

The following three lemmas imply that the definition of the characteristic here coincides with the
latter definition.\<close>

lemma (in ring) char_bound:
  assumes "x > 0"
  assumes "int_embed R (int x) = \<zero>"
  shows "char R \<le> x" "char R > 0"
proof -
  have "char_subring R \<subseteq> int_embed R ` ({0..<int x})"
  proof (rule image_subsetI)
    fix y :: int
    assume "y \<in> UNIV"
    define u where "u = y div (int x)"
    define v where "v = y mod (int x)"
    have "int x > 0" using assms by simp
    hence y_exp: "y = u * int x + v" "v \<ge> 0" "v < int x"
      unfolding u_def v_def by simp_all
    have "int_embed R y = int_embed R v"
      using int_embed_closed unfolding y_exp
      by (simp add:int_embed_mult int_embed_add assms(2))
    also have "... \<in> int_embed R ` ({0..<int x})"
      using y_exp(2,3) by simp
    finally show "int_embed R y \<in> int_embed R ` {0..<int x}"
      by simp
  qed
  hence a:"char_subring R = int_embed R ` {0..<int x}"
    by auto
  hence "char R = card (int_embed R ` ({0..<int x}))"
    unfolding char_def a by simp
  also have "... \<le> card {0..<int x}"
    by (intro card_image_le, simp)
  also have "... = x" by simp
  finally show "char R \<le> x" by simp
  have "1 = card {int_embed R 0}" by simp
  also have "... \<le> card (int_embed R ` {0..<int x})"
    using assms(1) by (intro card_mono finite_imageI, simp_all) 
  also have "... = char R"
    unfolding char_def a by simp
  finally show "char R > 0" by simp
qed

lemma (in ring) embed_char_eq_0:
  "int_embed R (int (char R)) = \<zero>"
proof (cases "finite (char_subring R)")
  case True
  interpret h: ring_hom_ring "int_ring" R "(int_embed R)"
    using int_embed_ring_hom by simp

  define A where "A = {0..int (char R)}"
  have "card (int_embed R ` A) \<le> card (char_subring R)"
    by (intro card_mono[OF True] image_subsetI, simp)
  also have "... = char R"
    unfolding char_def by simp
  also have "... < card A"
    unfolding A_def by simp
  finally have "card (int_embed R ` A) < card A" by simp
  hence "\<not>inj_on (int_embed R) A"
    using pigeonhole by simp
  then obtain x y where xy: 
    "x \<in> A" "y \<in> A" "x \<noteq> y" "int_embed R x = int_embed R y"
    unfolding inj_on_def by auto
  define v where "v = nat (max x y - min x y)"
  have a:"int_embed R v = \<zero>"
    using xy int_embed_closed
    by (cases "x < y", simp_all add:int_embed_diff v_def)
  moreover have "v > 0"
    using xy by (cases "x < y", simp_all add:v_def)
  ultimately have "char R \<le> v" using char_bound by simp
  moreover have "v \<le> char R"
    using xy v_def A_def by (cases "x < y", simp_all)
  ultimately have "char R = v" by simp
  then show ?thesis using a by simp
next
  case False
  hence "char R = 0" 
    unfolding char_def by simp
  then show ?thesis by (simp add:int_embed_zero)
qed

lemma (in ring) embed_char_eq_0_iff:
  fixes n :: int
  shows "int_embed R n = \<zero> \<longleftrightarrow> char R dvd n"
proof (cases "char R > 0")
  case True
  define r where "r = n mod char R"
  define s where "s = n div char R"
  have rs: "r < char R" "r \<ge> 0" "n = r + s * char R" 
    using True by (simp_all add:r_def s_def)

  have "int_embed R n = int_embed R r"
    using int_embed_closed unfolding rs(3)
    by (simp add: int_embed_add  int_embed_mult embed_char_eq_0)

  moreover have "nat r < char R" using rs by simp
  hence "int_embed R (nat r) \<noteq> \<zero> \<or> nat r = 0"
    using True char_bound not_less by blast
  hence "int_embed R r \<noteq> \<zero> \<or> r = 0"
    using rs by simp

  ultimately have "int_embed R n = \<zero> \<longleftrightarrow> r = 0"
    using int_embed_zero by auto
  also have "r = 0 \<longleftrightarrow> char R dvd n"
    using r_def by auto
  finally show ?thesis by simp
next
  case False
  hence "char R = 0" by simp
  hence a:"x > 0 \<Longrightarrow> int_embed R (int x) \<noteq> \<zero>" for x
    using char_bound by auto

  have c:"int_embed R (abs x) \<noteq> \<zero> \<longleftrightarrow> int_embed R x \<noteq> \<zero>" for x
    using int_embed_closed
    by (cases "x > 0", simp, simp add:int_embed_inv)
  
  have "int_embed R x \<noteq> \<zero>" if b:"x \<noteq> 0" for x
  proof -
    have "nat (abs x) > 0" using b by simp
    hence "int_embed R (nat (abs x)) \<noteq> \<zero>"
      using a by blast
    hence "int_embed R (abs x) \<noteq> \<zero>" by simp
    thus ?thesis using c by simp
  qed
  hence "int_embed R n = \<zero> \<longleftrightarrow> n = 0" 
    using int_embed_zero by auto
  also have "n = 0 \<longleftrightarrow> char R dvd n" using False by simp
  finally show ?thesis by simp
qed

text \<open>This result can be found in \<^cite>\<open>\<open>Theorem 1.44\<close> in "lidl1986"\<close>.\<close>

lemma (in domain) characteristic_is_prime:
  assumes "char R > 0"
  shows "prime (char R)"
proof (rule ccontr)
  have "\<not>(char R = 1)"
    using embed_char_eq_0 int_embed_one by auto
  hence "\<not>(char R dvd 1)" using assms(1) by simp
  moreover assume "\<not>(prime (char R))"
  hence "\<not>(irreducible (char R))"
    using irreducible_imp_prime_elem_gcd prime_elem_nat_iff by blast
  ultimately obtain p q where pq_def: "p * q = char R" "p > 1" "q > 1" 
    using assms
    unfolding Factorial_Ring.irreducible_def by auto
  have "int_embed R p \<otimes> int_embed R q = \<zero>"
    using embed_char_eq_0 pq_def 
    by (subst int_embed_mult[symmetric]) (metis of_nat_mult)
  hence "int_embed R p = \<zero> \<or> int_embed R q = \<zero>"
    using integral int_embed_closed by simp
  hence "p*q \<le> p \<or> p*q \<le> q"
    using char_bound pq_def by auto
  thus "False"
    using pq_def(2,3) by simp
qed

lemma (in ring) char_ring_is_subring:
  "subring (char_subring R) R"
proof -
  have "subring (int_embed R ` carrier int_ring) R"
    by (intro ring.carrier_is_subring int.ring_axioms
        ring_hom_ring.img_is_subring[OF int_embed_ring_hom]) 
  thus ?thesis by simp
qed

lemma (in cring) char_ring_is_subcring:
  "subcring (char_subring R) R"
  using subcringI'[OF char_ring_is_subring] by auto

lemma (in domain) char_ring_is_subdomain:
  "subdomain (char_subring R) R"
  using subdomainI'[OF char_ring_is_subring] by auto

lemma image_set_eqI:
  assumes "\<And>x. x \<in> A \<Longrightarrow> f x \<in> B"
  assumes "\<And>x. x \<in> B \<Longrightarrow> g x \<in> A \<and> f (g x) = x" 
  shows  "f ` A = B"
  using assms by force

text \<open>This is the binomial expansion theorem for commutative rings.\<close>

lemma (in cring) binomial_expansion:
  fixes n :: nat
  assumes [simp]: "x \<in> carrier R" "y \<in> carrier R"
  shows "(x \<oplus> y) [^] n = 
    (\<Oplus>k \<in> {..n}. int_embed R (n choose k) \<otimes> x [^] k \<otimes> y [^] (n-k))" 
proof -
  define A where "A = (\<lambda>k. {A. A \<subseteq> {..<n} \<and> card A = k})"

  have fin_A: "finite (A i)" for i 
    unfolding A_def by simp
  have disj_A: "pairwise (\<lambda>i j. disjnt (A i) (A j)) {..n}" 
    unfolding pairwise_def disjnt_def A_def by auto
  have card_A: "B \<in> A i \<Longrightarrow> card B = i" if " i \<in> {..n}" for i B 
    unfolding A_def by simp
  have card_A2: "card (A i) = (n choose i)" if "i \<in> {..n}" for i 
    unfolding A_def using n_subsets[where A="{..<n}"] by simp

  have card_bound: "card A \<le> n"
    if "A \<subseteq> {..<n}" for n A 
    by (metis card_lessThan finite_lessThan card_mono that)
  have card_insert: "card (insert n A) = card A + 1"
    if "A \<subseteq> {..<(n::nat)}" for n A 
    using finite_subset that by (subst card_insert_disjoint, auto)

  have embed_distr: "[m] \<cdot> y = int_embed R (int m) \<otimes> y" 
    if "y \<in> carrier R" for m y
    unfolding int_embed_def add_pow_def using that
    by (simp add:add_pow_def[symmetric] int_pow_int add_pow_ldistr)

  have "(x \<oplus> y) [^] n = 
    (\<Oplus>A \<in> Pow {..<n}. x [^] (card A) \<otimes> y [^] (n-card A))"
  proof (induction n)
    case 0
    then show ?case by simp
  next
    case (Suc n)
    have s1: 
      "insert n ` Pow {..<n} = {A. A \<subseteq> {..<n+1} \<and> n \<in> A}" 
      by (intro image_set_eqI[where g="\<lambda>x. x \<inter> {..<n}"], auto) 
    have s2:
      "Pow {..<n} = {A. A \<subseteq> {..<n+1} \<and> n \<notin> A}" 
      using lessThan_Suc by auto

    have "(x \<oplus> y) [^] Suc n = (x \<oplus> y) [^] n \<otimes> (x \<oplus> y)" by simp
    also have "... = 
      (\<Oplus>A \<in> Pow {..<n}. x [^] (card A) \<otimes> y [^] (n-card A)) \<otimes> 
      (x \<oplus> y)"
      by (subst Suc, simp)
    also have "... = 
      (\<Oplus>A \<in> Pow {..<n}. x [^] (card A) \<otimes> y [^] (n-card A)) \<otimes> x \<oplus>
      (\<Oplus>A \<in> Pow {..<n}. x [^] (card A) \<otimes> y [^] (n-card A)) \<otimes> y"
      by (subst r_distr, auto)
    also have "... = 
      (\<Oplus>A \<in> Pow {..<n}. x [^] (card A) \<otimes> y [^] (n-card A) \<otimes> x) \<oplus>
      (\<Oplus>A \<in> Pow {..<n}. x [^] (card A) \<otimes> y [^] (n-card A) \<otimes> y)"
      by (simp add:finsum_ldistr)
    also have "... = 
      (\<Oplus>A \<in> Pow {..<n}. x [^] (card A+1) \<otimes> y [^] (n-card A)) \<oplus>
      (\<Oplus>A \<in> Pow {..<n}. x [^] (card A) \<otimes> y [^] (n-card A+1))"
      using m_assoc m_comm 
      by (intro arg_cong2[where f="(\<oplus>)"] finsum_cong', auto)
    also have "... = 
      (\<Oplus>A \<in> Pow {..<n}. x [^] (card (insert n A)) 
        \<otimes> y [^] (n+1-card (insert n A))) \<oplus>
      (\<Oplus>A \<in> Pow {..<n}. x [^] (card A) \<otimes> y [^] (n+1-card A))"
      using finite_subset card_bound card_insert Suc_diff_le
      by (intro arg_cong2[where f="(\<oplus>)"] finsum_cong', simp_all)
    also have "... = 
      (\<Oplus>A \<in> insert n ` Pow {..<n}. x [^] (card A) 
        \<otimes> y [^] (n+1-card A)) \<oplus>
      (\<Oplus>A \<in> Pow {..<n}. x [^] (card A) \<otimes> y [^] (n+1-card A))"
      by (subst finsum_reindex, auto simp add:inj_on_def) 
    also have "... = 
      (\<Oplus>A \<in> {A. A \<subseteq> {..<n+1} \<and> n \<in> A}. 
        x [^] (card A) \<otimes> y [^] (n+1-card A)) \<oplus>
      (\<Oplus>A \<in> {A. A \<subseteq> {..<n+1} \<and> n \<notin> A}. 
        x [^] (card A) \<otimes> y [^] (n+1-card A))"
      by (intro arg_cong2[where f="(\<oplus>)"] finsum_cong' s1 s2, simp_all)
    also have "... = (\<Oplus>A \<in> 
      {A. A \<subseteq> {..<n+1} \<and> n \<in> A} \<union> {A. A \<subseteq> {..<n+1} \<and> n \<notin> A}. 
        x [^] (card A) \<otimes> y [^] (n+1-card A))"
      by (subst finsum_Un_disjoint, auto)
    also have "... = 
      (\<Oplus>A \<in> Pow {..<n+1}. x [^] (card A) \<otimes> y [^] (n+1-card A))"
      by (intro finsum_cong', auto)
    finally show ?case by simp
  qed
  also have "... = 
    (\<Oplus>A \<in> (\<Union> (A ` {..n})). x [^] (card A) \<otimes> y [^] (n-card A))"
    using card_bound by (intro finsum_cong', auto simp add:A_def)
  also have "... = 
    (\<Oplus> k \<in> {..n}. (\<Oplus> A \<in> A k. x [^] (card A) \<otimes> y [^] (n-card A)))"
    using fin_A disj_A by (subst add.finprod_UN_disjoint, auto)
  also have "... = (\<Oplus> k \<in> {..n}. (\<Oplus> A \<in> A k. x [^] k \<otimes> y [^] (n-k)))"
    using card_A by (intro finsum_cong', auto)
  also have "... = 
    (\<Oplus> k \<in> {..n}. int_embed R (card (A k)) \<otimes> x [^] k \<otimes> y [^] (n-k))"
    using int_embed_closed
    by (subst add.finprod_const, simp_all add:embed_distr m_assoc)
  also have "... = 
    (\<Oplus> k \<in> {..n}. int_embed R (n choose k) \<otimes> x [^] k \<otimes> y [^] (n-k))"
    using int_embed_closed card_A2 by (intro finsum_cong', simp_all)
  finally show ?thesis by simp
qed

lemma bin_prime_factor:
  assumes "prime p"
  assumes "k > 0" "k < p"
  shows "p dvd (p choose k)"
proof -
  have "p dvd fact p" 
    using assms(1) prime_dvd_fact_iff by auto
  hence "p dvd fact k * fact (p - k) * (p choose k)"
    using binomial_fact_lemma assms by simp
  hence "p dvd fact k \<or> p dvd fact (p-k) \<or> p dvd (p choose k)"
    by (simp add: assms(1) prime_dvd_mult_eq_nat)
  thus "p dvd (p choose k)"
    using assms(1,2,3) prime_dvd_fact_iff by auto
qed

theorem (in domain) freshmans_dream:
  assumes "char R > 0"
  assumes [simp]: "x \<in> carrier R" "y \<in> carrier R"
  shows "(x \<oplus> y) [^] (char R) = x [^] char R \<oplus> y [^] char R" 
    (is "?lhs = ?rhs")
proof -
  have c:"prime (char R)"
    using assms(1) characteristic_is_prime by auto
  have a:"int_embed R (char R choose i) = \<zero>" 
    if "i \<in> {..char R} - {0, char R}" for i
  proof -
    have "i > 0" "i < char R" using that by auto
    hence "char R dvd char R choose i"
      using c bin_prime_factor by simp
    thus ?thesis using embed_char_eq_0_iff by simp
  qed

  have "?lhs = (\<Oplus>k \<in> {..char R}. int_embed R (char R choose k) 
    \<otimes> x [^] k \<otimes> y [^] (char R-k))"
    using binomial_expansion[OF assms(2,3)] by simp
  also have "... = (\<Oplus>k \<in> {0,char R}.int_embed R (char R choose k) 
    \<otimes> x [^] k \<otimes> y [^] (char R-k))"
    using a int_embed_closed
    by (intro add.finprod_mono_neutral_cong_right, simp, simp_all)
  also have "... = ?rhs"
    using int_embed_closed assms(1) by (simp add:int_embed_one a_comm)
  finally show ?thesis by simp
qed

text \<open>The following theorem is somtimes called Freshman's dream for obvious reasons,
it can be found in Lidl and Niederreiter~\<^cite>\<open>\<open>Theorem 1.46\<close> in "lidl1986"\<close>.\<close>

lemma (in domain) freshmans_dream_ext:
  fixes m
  assumes "char R > 0"
  assumes [simp]: "x \<in> carrier R" "y \<in> carrier R"
  defines "n \<equiv> char R^m" 
  shows "(x \<oplus> y) [^] n = x [^] n \<oplus> y [^] n"
    (is "?lhs = ?rhs")
  unfolding n_def
proof (induction m)
  case 0
  then show ?case by simp
next
  case (Suc m)
  have "(x \<oplus> y) [^] (char R^(m+1)) = 
    (x \<oplus> y) [^] (char R^m * char R)"
    by (simp add:mult.commute)
  also have "... = ((x \<oplus> y) [^] (char R^m)) [^] char R"
    using nat_pow_pow by simp
  also have "... = (x [^] (char R^m) \<oplus> y [^] (char R^m)) [^] char R"
    by (subst Suc, simp)
  also have "... = 
    (x [^] (char R^m)) [^] char R \<oplus> (y [^] (char R^m)) [^] char R"
    by (subst freshmans_dream[OF assms(1), symmetric], simp_all)
  also have "... = 
    x [^] (char R^m * char R) \<oplus> y [^] (char R^m * char R)"
    by (simp add:nat_pow_pow)
  also have "... = x [^] (char R^Suc m) \<oplus> y [^] (char R^Suc m)"
    by (simp add:mult.commute)
  finally show ?case by simp
qed

text \<open>The following is a generalized version of the Frobenius homomorphism. The classic version
of the theorem is the case where @{term "(k::nat) = 1"}.\<close>

theorem (in domain) frobenius_hom:
  assumes "char R  > 0"
  assumes "m = char R ^ k"
  shows "ring_hom_cring R R (\<lambda>x. x [^] m)"
proof -
  have a:"(x \<otimes> y) [^] m = x [^] m \<otimes> y [^] m" 
    if b:"x \<in> carrier R" "y \<in> carrier R" for x y 
    using b nat_pow_distrib by simp
  have b:"(x \<oplus> y) [^] m = x [^] m \<oplus> y [^] m"
    if b:"x \<in> carrier R" "y \<in> carrier R" for x y 
    unfolding assms(2) freshmans_dream_ext[OF assms(1) b] 
    by simp

  have "ring_hom_ring R R (\<lambda>x. x [^] m)"
    by  (intro ring_hom_ringI a b ring_axioms, simp_all) 

  thus "?thesis"
    using RingHom.ring_hom_cringI is_cring by blast
qed

lemma (in domain) char_ring_is_subfield:
  assumes "char R > 0"
  shows "subfield (char_subring R) R"
proof -
  interpret d:domain "R \<lparr> carrier := char_subring R \<rparr>"
    using char_ring_is_subdomain subdomain_is_domain by simp

  have "finite (char_subring R)" 
    using char_def assms by (metis card_ge_0_finite)
  hence "Units (R \<lparr> carrier := char_subring R \<rparr>) 
    = char_subring R - {\<zero>}"
    using d.finite_domain_units by simp

  thus ?thesis
    using subfieldI[OF char_ring_is_subcring] by simp
qed

lemma card_lists_length_eq': 
  fixes A :: "'a set"
  shows "card {xs. set xs \<subseteq> A \<and> length xs = n} = card A ^ n" 
proof (cases "finite A")
  case True
  then show ?thesis using card_lists_length_eq by auto
next
  case False
  hence inf_A: "infinite A" by simp
  show ?thesis
  proof (cases "n = 0")
    case True
    hence "card {xs. set xs \<subseteq> A \<and> length xs = n} = card {([] :: 'a list)}"
      by (intro arg_cong[where f="card"], auto simp add:set_eq_iff)
    also have "... = 1" by simp
    also have "... = card A^n" using True inf_A by simp
    finally show ?thesis by simp 
  next
    case False
    hence "inj (replicate n)" 
      by (meson inj_onI replicate_eq_replicate)
    hence "inj_on (replicate n) A" using inj_on_subset 
      by (metis subset_UNIV) 
    hence "infinite (replicate n ` A)"
      using inf_A finite_image_iff by auto
    moreover have 
      "replicate n ` A \<subseteq> {xs. set xs \<subseteq> A \<and> length xs  = n}"
      by (intro image_subsetI, auto)
    ultimately have "infinite {xs. set xs \<subseteq> A \<and> length xs  = n}"
      using infinite_super by auto
    hence "card {xs. set xs \<subseteq> A \<and> length xs  = n} = 0" by simp
    then show ?thesis using inf_A False by simp
  qed
qed

lemma (in ring) card_span:
  assumes "subfield K R"
  assumes "independent K w"
  assumes "set w \<subseteq> carrier R"
  shows "card (Span K w) = card K^(length w)"
proof -
  define A where "A = {x. set x \<subseteq> K \<and> length x = length w}"
  define f where "f = (\<lambda>x. combine x w)"

  have "x \<in> f ` A" if a:"x \<in> Span K w" for x
  proof -
    obtain y where "y \<in> A" "x = f y"
      unfolding A_def f_def
      using unique_decomposition[OF assms(1,2) a] by auto
    thus ?thesis by simp
  qed
  moreover have "f x \<in> Span K w" if a: "x \<in> A" for x
    using Span_eq_combine_set[OF assms(1,3)] a
    unfolding A_def f_def by auto
  ultimately have b:"Span K w = f ` A" by auto

  have "False" if a: "x \<in> A" "y \<in> A" "f x = f y" "x \<noteq> y" for x y
  proof -
    have "f x \<in> Span K w" using b a by simp
    thus "False" 
      using a unique_decomposition[OF assms(1,2)]
      unfolding f_def A_def by blast
  qed
  hence f_inj: "inj_on f A" 
    unfolding inj_on_def by auto

  have "card (Span K w) = card (f ` A)" using b by simp
  also have "... = card A" by (intro card_image f_inj) 
  also have "... = card K^length w"
    unfolding A_def by (intro card_lists_length_eq')
  finally show ?thesis by simp
qed

lemma (in ring) finite_carr_imp_char_ge_0:
  assumes "finite (carrier R)"
  shows "char R > 0"
proof -
  have "char_subring R \<subseteq> carrier R"
    using int_embed_closed by auto
  hence "finite (char_subring R)"
    using finite_subset assms by auto
  hence "card (char_subring R) > 0"
    using card_range_greater_zero by simp
  thus "char R > 0" 
    unfolding char_def by simp
qed

lemma (in ring) char_consistent:
  assumes "subring H R"
  shows "char (R \<lparr> carrier := H \<rparr>) = char R"
proof -
  show ?thesis
    using int_embed_consistent[OF assms(1)]
    unfolding char_def by simp
qed

lemma (in ring_hom_ring) char_consistent:
  assumes "inj_on h (carrier R)"
  shows "char R = char S"
proof -
  have a:"h (int_embed R (int n)) = int_embed S (int n)" for n
    using R.int_embed_range[OF R.carrier_is_subring]
    using R.int_embed_range[OF R.carrier_is_subring]
    using S.int_embed_one R.int_embed_one
    using S.int_embed_zero R.int_embed_zero
    using S.int_embed_add R.int_embed_add
    by (induction n, simp_all)

  have b:"h (int_embed R (-(int n))) = int_embed S (-(int n))" for n
    using R.int_embed_range[OF R.carrier_is_subring]
    using S.int_embed_range[OF S.carrier_is_subring] a
    by (simp add:R.int_embed_inv S.int_embed_inv)

  have c:"h (int_embed R n) = int_embed S n" for n
  proof (cases "n \<ge> 0")
    case True
    then obtain m where "n = int m"
      using nonneg_int_cases by auto
    then show ?thesis 
      by (simp add:a)
  next
    case False
    hence "n \<le> 0" by simp
    then obtain m where "n = -int m" 
      using nonpos_int_cases by auto
    then show ?thesis by (simp add:b)
  qed

  have "char S = card (h ` char_subring R)"
    unfolding char_def image_image c by simp
  also have "... = card (char_subring R)"
    using R.int_embed_range[OF R.carrier_is_subring]
    by (intro card_image inj_on_subset[OF assms(1)]) auto 
  also have "... = char R" unfolding char_def by simp
  finally show ?thesis
    by simp
qed

definition char_iso :: "_ \<Rightarrow> int set \<Rightarrow> 'a" 
  where "char_iso R x = the_elem (int_embed R ` x)"

text \<open>The function @{term "char_iso R"} denotes the isomorphism between @{term "ZFact (char R)"} and
the characteristic subring.\<close>

lemma (in ring) char_iso: "char_iso R \<in> 
  ring_iso (ZFact (char R)) (R\<lparr>carrier := char_subring R\<rparr>)"
proof -
  interpret h: ring_hom_ring "int_ring" "R" "int_embed R"
    using int_embed_ring_hom by simp

  have "a_kernel \<Z> R (int_embed R) = {x. int_embed R x = \<zero>}"
    unfolding a_kernel_def kernel_def by simp
  also have "... = {x. char R dvd x}"
    using embed_char_eq_0_iff by simp
  also have "... = PIdl\<^bsub>\<Z>\<^esub> (int (char R))" 
    unfolding cgenideal_def by auto
  also have "... = Idl\<^bsub>\<Z>\<^esub> {int (char R)}"
    using int.cgenideal_eq_genideal by simp
  finally have a:"a_kernel \<Z> R (int_embed R) = Idl\<^bsub>\<Z>\<^esub> {int (char R)}"
    by simp
  show  "?thesis"
    unfolding char_iso_def ZFact_def a[symmetric]
    by (intro h.FactRing_iso_set_aux)
qed

text \<open>The size of a finite field must be a prime power.
This can be found in Ireland and Rosen~\<^cite>\<open>\<open>Proposition 7.1.3\<close> in "ireland1982"\<close>.\<close>

theorem (in finite_field) finite_field_order:
  "\<exists>n. order R = char R ^ n \<and> n > 0"
proof -
  have a:"char R > 0"
    using finite_carr_imp_char_ge_0[OF finite_carrier]
    by simp
  let ?CR = "char_subring R"

  obtain v where v_def: "set v = carrier R"
    using finite_carrier finite_list by auto
  hence b:"set v \<subseteq> carrier R" by auto

  have "carrier R = set v" using v_def by simp
  also have "... \<subseteq> Span ?CR v"
    using Span_base_incl[OF char_ring_is_subfield[OF a] b] by simp
  finally have "carrier R \<subseteq> Span ?CR v" by simp
  moreover have "Span ?CR v \<subseteq> carrier R"
    using int_embed_closed v_def by (intro Span_in_carrier, auto)
  ultimately have Span_v: "Span ?CR v = carrier R" by simp

  obtain w where w_def: 
    "set w \<subseteq> carrier R" 
    "independent ?CR w" 
    "Span ?CR v = Span ?CR w"
    using b filter_base[OF char_ring_is_subfield[OF a]]
    by metis

  have Span_w: "Span ?CR w = carrier R"
    using w_def(3) Span_v by simp

  hence "order R = card (Span ?CR w)" by (simp add:order_def)
  also have "... = card ?CR^length w"
    by (intro card_span char_ring_is_subfield[OF a] w_def(1,2))
  finally have c:
    "order R = char R^(length w)"
    by (simp add:char_def)
  have "length w > 0"
    using finite_field_min_order c by auto
  thus ?thesis using c by auto
qed

end
