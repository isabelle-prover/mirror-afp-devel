section \<open>Finite Fields\<close>

theory Field
  imports "HOL-Algebra.Ring_Divisibility" "HOL-Algebra.IntRing"
begin

text \<open>This section contains a proof that the factor ring @{term "ZFact p"} for
@{term [names_short] "prime p"} is a field. Note that the bulk of the work has already been done in
HOL-Algebra, in particular it is established that @{term "ZFact p"} is a domain.

However, any domain with a finite carrier is already a field. This can be seen by establishing that
multiplication by a non-zero element is an injective map between the elements of the carrier of the
domain. But an injective map between sets of the same non-finite cardinality is also surjective.
Hence it is possible to find the unit element in the image of such a map.

The following definition introduces the canonical embedding of @{term "{..<(p::nat)}"} into @{term "ZFact p"}.
It will be shown that it is a bijection which establishes that @{term "ZFact p"} is finite.\<close>

definition zfact_iso :: "nat \<Rightarrow> nat \<Rightarrow> int set" where
  "zfact_iso p k = Idl\<^bsub>\<Z>\<^esub> {int p} +>\<^bsub>\<Z>\<^esub> (int k)"

context
  fixes n :: nat
  fixes I :: "int set"
  assumes n_ge_0: "n > 0"
  defines "I \<equiv> Idl\<^bsub>\<Z>\<^esub> {int n}"
begin

lemma ideal_I: "ideal I \<Z>"
  unfolding I_def by (simp add: int.genideal_ideal)

lemma zfact_iso_inj:
  "inj_on (zfact_iso n) {..<n}"
proof (rule inj_onI)
  fix x y
  assume a:"x \<in> {..<n}"
  assume b:"y \<in> {..<n}"
  assume "zfact_iso n x = zfact_iso n y"
  hence "I +>\<^bsub>\<Z>\<^esub> (int x) = I +>\<^bsub>\<Z>\<^esub> (int y)"
    by (simp add:zfact_iso_def I_def)
  hence "int x - int y \<in> I"
    by (subst int.quotient_eq_iff_same_a_r_cos[OF ideal_I], auto)
  hence "int x mod int n = int y mod int n"
    unfolding I_def 
    by (meson Idl_subset_eq_dvd int_Idl_subset_ideal mod_eq_dvd_iff)
  thus "x = y"
    using a b by simp
qed

lemma I_shift:
  assumes "u mod (int n) = v mod (int n)"
  shows "I +>\<^bsub>\<Z>\<^esub> u = I +>\<^bsub>\<Z>\<^esub> v"
proof -
  have "u - v \<in> I"
    unfolding I_def  
    by (metis Idl_subset_eq_dvd assms int_Idl_subset_ideal mod_eq_dvd_iff)
  thus ?thesis
    using ideal_I int.quotient_eq_iff_same_a_r_cos by simp
qed

lemma zfact_iso_ran:
  "zfact_iso n ` {..<n} = carrier (ZFact (int n))"
proof -
  have "zfact_iso n ` {..<n} \<subseteq> carrier (ZFact (int n))"
    unfolding zfact_iso_def ZFact_def FactRing_simps 
    using int.a_rcosetsI by auto
  moreover have "\<And>x. x \<in> carrier (ZFact (int n)) \<Longrightarrow> x \<in> zfact_iso n ` {..<n}"
  proof -
    fix x
    assume "x \<in> carrier (ZFact (int n))"
    then obtain y where y_def: "x = I  +>\<^bsub>\<Z>\<^esub> y"
      unfolding I_def ZFact_def FactRing_simps by auto
    obtain z where z_def: "(int z) mod (int n) = y mod (int n)" "z < n"
      by (metis Euclidean_Division.pos_mod_sign mod_mod_trivial n_ge_0 nonneg_int_cases
          of_nat_0_less_iff of_nat_mod unique_euclidean_semiring_numeral_class.pos_mod_bound)
    have "x = I  +>\<^bsub>\<Z>\<^esub> y"
      by (simp add:y_def)
    also have "... = I +>\<^bsub>\<Z>\<^esub> (int z)"
      by (rule I_shift, simp add:z_def)
    also have "... = zfact_iso n z"
      by (simp add:zfact_iso_def I_def)
    finally have "x = zfact_iso n z"
      by simp
    thus "x \<in> zfact_iso n ` {..<n}"
      using z_def(2) by blast
  qed
  ultimately show ?thesis by auto
qed

lemma zfact_iso_0: "zfact_iso n 0 = \<zero>\<^bsub>ZFact (int n)\<^esub>"
proof -
  interpret i:ideal "I" "\<Z>" using ideal_I by simp
  interpret s:ring_hom_ring "\<Z>" "ZFact (int n)" "(+>\<^bsub>\<Z>\<^esub>) I"
   using i.rcos_ring_hom_ring ZFact_def I_def by auto

  show ?thesis
    by (simp add:zfact_iso_def ZFact_def I_def[symmetric])
qed

lemma zfact_iso_bij:
  "bij_betw (zfact_iso n) {..<n} (carrier (ZFact (int n)))"
  using  bij_betw_def zfact_iso_inj zfact_iso_ran by blast

lemma zfact_card:
  "card (carrier (ZFact (int n))) = n"
  using bij_betw_same_card[OF zfact_iso_bij] by simp

lemma zfact_finite:
  "finite (carrier (ZFact (int n)))"
  by (metis n_ge_0 zfact_card card.infinite less_nat_zero_code)

end

lemma finite_domains_are_fields:
  assumes "domain R"
  assumes "finite (carrier R)"
  shows "field R"
proof -
  interpret domain R using assms by auto
  have "Units R = carrier R - {\<zero>\<^bsub>R\<^esub>}"
  proof 
    have "Units R \<subseteq> carrier R" by (simp add:Units_def) 
    moreover have "\<zero>\<^bsub>R\<^esub> \<notin> Units R"
      by (meson assms(1) domain.zero_is_prime(1) primeE)
    ultimately show "Units R \<subseteq> carrier R - {\<zero>\<^bsub>R\<^esub>}" by blast
  next
    show "carrier R - {\<zero>\<^bsub>R\<^esub>} \<subseteq> Units R"
    proof
      fix x
      assume a:"x \<in> carrier R - {\<zero>\<^bsub>R\<^esub>}"
      hence x_carr: "x \<in> carrier R" by blast
      define f where "f = (\<lambda>y. y \<otimes>\<^bsub>R\<^esub> x)"
      have "inj_on f (carrier R)" unfolding f_def
        by (rule inj_onI, metis DiffD1 DiffD2 a assms(1) domain.m_rcancel insertI1)
      hence "card (carrier R) = card (f ` carrier R)"
        by (metis card_image)
      moreover have "f ` carrier R \<subseteq> carrier R" unfolding f_def
        by (rule image_subsetI, simp add: ring.ring_simprules x_carr)
      ultimately have "f ` carrier R = carrier R"
        using card_subset_eq assms(2) by metis
      moreover have "\<one>\<^bsub>R\<^esub> \<in> carrier R" by simp
      ultimately have "\<exists>y \<in> carrier R. f y = \<one>\<^bsub>R\<^esub>" 
        by (metis image_iff)
      then obtain y where y_carrier: "y \<in> carrier R" and y_left_inv: "y \<otimes>\<^bsub>R\<^esub> x = \<one>\<^bsub>R\<^esub>" 
        using f_def by blast
      hence  y_right_inv: "x \<otimes>\<^bsub>R\<^esub> y = \<one>\<^bsub>R\<^esub>" using assms(1) a 
        by (metis DiffD1 a cring.cring_simprules(14) domain.axioms(1))
      show "x \<in> Units R" using y_carrier y_left_inv y_right_inv
        by (metis DiffD1 a assms(1) cring.divides_one domain.axioms(1) factor_def)
    qed
  qed
  then show "field R" by (simp add: assms(1) field.intro field_axioms.intro)
qed

lemma zfact_prime_is_field:
  assumes "Factorial_Ring.prime (p :: nat)" 
  shows "field (ZFact (int p))"
proof -
  have "finite (carrier (ZFact (int p)))"
    using zfact_finite assms prime_gt_0_nat by blast
  moreover have "domain (ZFact (int p))"
    using ZFact_prime_is_domain assms by auto
  ultimately show ?thesis
    using finite_domains_are_fields by blast
qed

text \<open>In some applications it is more convenient to work with natural numbers instead of
@{term "ZFact p"} whose elements are cosets. To support that use case the following definition
introduces an additive and multiplicative structure on @{term "{..<p}"}. After verifying that
the function @{term "zfact_iso"} and its inverse are homomorphisms, the ring and field property
can be transfered from @{term "ZFact p"} to to the structure on @{term "{..<p}"}.\<close> 

definition mod_ring :: "nat => nat ring"
  where "mod_ring n = \<lparr> 
    carrier = {..<n},
    mult = (\<lambda> x y. (x * y) mod n),
    one = 1,
    zero = 0,
    add = (\<lambda> x y. (x + y) mod n) \<rparr>"

definition zfact_iso_inv :: "nat \<Rightarrow> int set \<Rightarrow> nat" where
  "zfact_iso_inv p = inv_into {..<p} (zfact_iso p)"

lemma zfact_iso_inv_0: 
  assumes n_ge_0: "n > 0"
  shows "zfact_iso_inv n \<zero>\<^bsub>ZFact (int n)\<^esub> = 0"
  unfolding zfact_iso_inv_def zfact_iso_0[OF n_ge_0, symmetric] using n_ge_0
  by (rule inv_into_f_f[OF zfact_iso_inj], simp add:mod_ring_def)

lemma zfact_coset:
  assumes n_ge_0: "n > 0"
  assumes "x \<in> carrier (ZFact (int n))"
  defines "I \<equiv> Idl\<^bsub>\<Z>\<^esub> {int n}"
  shows "x = I +>\<^bsub>\<Z>\<^esub> (int (zfact_iso_inv n x))"
proof -
  have "x \<in> zfact_iso n ` {..<n}" 
    using assms zfact_iso_ran by simp
  hence "zfact_iso n (zfact_iso_inv n x) = x"
    unfolding zfact_iso_inv_def by (rule f_inv_into_f)
  thus ?thesis unfolding zfact_iso_def I_def by blast
qed

lemma zfact_iso_inv_is_ring_iso:
  assumes n_ge_1: "n > 1"
  shows "zfact_iso_inv n \<in> ring_iso (ZFact (int n)) (mod_ring n)"
proof (rule ring_iso_memI)
  interpret r:cring "(ZFact (int n))"
    using ZFact_is_cring by simp

  define I where "I = Idl\<^bsub>\<Z>\<^esub> {int n}"

  have n_ge_0: "n > 0" using n_ge_1 by simp

  interpret i:ideal "I" "\<Z>"
    using ideal_I[OF n_ge_0] I_def by simp

  interpret s:ring_hom_ring "\<Z>" "ZFact (int n)" "(+>\<^bsub>\<Z>\<^esub>) I"
   using i.rcos_ring_hom_ring ZFact_def I_def by auto

  show 
    "\<And>x. x \<in> carrier (ZFact (int n)) \<Longrightarrow> zfact_iso_inv n x \<in> carrier (mod_ring n)"
  proof -
    fix x 
    assume "x \<in> carrier (ZFact (int n))"
    hence "zfact_iso_inv n x \<in> {..<n}"
      unfolding zfact_iso_inv_def
      using zfact_iso_ran[OF n_ge_0] inv_into_into by metis

    thus "zfact_iso_inv n x \<in> carrier (mod_ring n)"
      unfolding mod_ring_def by simp
  qed

  show "\<And>x y. x \<in> carrier (ZFact (int n)) \<Longrightarrow> y \<in> carrier (ZFact (int n)) \<Longrightarrow>
    zfact_iso_inv n (x \<otimes>\<^bsub>ZFact (int n)\<^esub> y) = 
    zfact_iso_inv n x \<otimes>\<^bsub>mod_ring n\<^esub> zfact_iso_inv n y"
  proof -
    fix x y
    assume x_carr: "x \<in> carrier (ZFact (int n))"
    define x' where "x' = zfact_iso_inv n x"
    assume y_carr: "y \<in> carrier (ZFact (int n))"
    define y' where "y' = zfact_iso_inv n y"
    have "x \<otimes>\<^bsub>ZFact (int n)\<^esub> y = (I +>\<^bsub>\<Z>\<^esub> (int x')) \<otimes>\<^bsub>ZFact (int n)\<^esub> (I +>\<^bsub>\<Z>\<^esub> (int y'))"
      unfolding x'_def y'_def
      using x_carr y_carr zfact_coset[OF n_ge_0] I_def by simp
    also have "... = (I +>\<^bsub>\<Z>\<^esub> (int x' * int y'))"
      by simp
    also have "... = (I +>\<^bsub>\<Z>\<^esub> (int ((x' * y') mod n)))"
      unfolding I_def zmod_int by (rule I_shift[OF n_ge_0],simp)
    also have "... = (I +>\<^bsub>\<Z>\<^esub> (x' \<otimes>\<^bsub>mod_ring n\<^esub> y'))"
      unfolding mod_ring_def by simp
    also have "... = zfact_iso n (x' \<otimes>\<^bsub>mod_ring n\<^esub> y')"
      unfolding zfact_iso_def I_def by simp
    finally have a:"x \<otimes>\<^bsub>ZFact (int n)\<^esub> y = zfact_iso n (x' \<otimes>\<^bsub>mod_ring n\<^esub> y')"
      by simp
    have b:"x' \<otimes>\<^bsub>mod_ring n\<^esub> y' \<in> {..<n}" 
      using mod_ring_def n_ge_0 by auto
    have "zfact_iso_inv n (zfact_iso n (x' \<otimes>\<^bsub>mod_ring n\<^esub> y')) = x' \<otimes>\<^bsub>mod_ring n\<^esub> y'" 
      unfolding zfact_iso_inv_def
      by (rule inv_into_f_f[OF zfact_iso_inj[OF n_ge_0] b])
    thus 
      "zfact_iso_inv n (x \<otimes>\<^bsub>ZFact (int n)\<^esub> y) = 
      zfact_iso_inv n x \<otimes>\<^bsub>mod_ring n\<^esub> zfact_iso_inv n y"
      using a x'_def y'_def by simp
  qed

  show "\<And>x y. x \<in> carrier (ZFact (int n)) \<Longrightarrow> y \<in> carrier (ZFact (int n)) \<Longrightarrow>
    zfact_iso_inv n (x \<oplus>\<^bsub>ZFact (int n)\<^esub> y) = 
    zfact_iso_inv n x \<oplus>\<^bsub>mod_ring n\<^esub> zfact_iso_inv n y"
  proof -
    fix x y
    assume x_carr: "x \<in> carrier (ZFact (int n))"
    define x' where "x' = zfact_iso_inv n x"
    assume y_carr: "y \<in> carrier (ZFact (int n))"
    define y' where "y' = zfact_iso_inv n y"
    have "x \<oplus>\<^bsub>ZFact (int n)\<^esub> y = (I +>\<^bsub>\<Z>\<^esub> (int x')) \<oplus>\<^bsub>ZFact (int n)\<^esub> (I +>\<^bsub>\<Z>\<^esub> (int y'))"
      unfolding x'_def y'_def
      using x_carr y_carr zfact_coset[OF n_ge_0] I_def by simp
    also have "... = (I +>\<^bsub>\<Z>\<^esub> (int x' + int y'))"
      by simp
    also have "... = (I +>\<^bsub>\<Z>\<^esub> (int ((x' + y') mod n)))"
      unfolding I_def zmod_int by (rule I_shift[OF n_ge_0],simp)
    also have "... = (I +>\<^bsub>\<Z>\<^esub> (x' \<oplus>\<^bsub>mod_ring n\<^esub> y'))"
      unfolding mod_ring_def by simp
    also have "... = zfact_iso n (x' \<oplus>\<^bsub>mod_ring n\<^esub> y')"
      unfolding zfact_iso_def I_def by simp
    finally have a:"x \<oplus>\<^bsub>ZFact (int n)\<^esub> y = zfact_iso n (x' \<oplus>\<^bsub>mod_ring n\<^esub> y')"
      by simp
    have b:"x' \<oplus>\<^bsub>mod_ring n\<^esub> y' \<in> {..<n}" 
      using mod_ring_def n_ge_0 by auto
    have "zfact_iso_inv n (zfact_iso n (x' \<oplus>\<^bsub>mod_ring n\<^esub> y')) = x' \<oplus>\<^bsub>mod_ring n\<^esub> y'" 
      unfolding zfact_iso_inv_def
      by (rule inv_into_f_f[OF zfact_iso_inj[OF n_ge_0] b])
    thus 
      "zfact_iso_inv n (x \<oplus>\<^bsub>ZFact (int n)\<^esub> y) = 
      zfact_iso_inv n x \<oplus>\<^bsub>mod_ring n\<^esub> zfact_iso_inv n y"
      using a x'_def y'_def by simp
  qed

  have "\<one>\<^bsub>ZFact (int n)\<^esub> = zfact_iso n (\<one>\<^bsub>mod_ring n\<^esub>)"
    by (simp add:zfact_iso_def ZFact_def I_def[symmetric] mod_ring_def)

  thus "zfact_iso_inv n \<one>\<^bsub>ZFact (int n)\<^esub> = \<one>\<^bsub>mod_ring n\<^esub>"
    unfolding zfact_iso_inv_def mod_ring_def
    using inv_into_f_f[OF zfact_iso_inj] n_ge_1 by simp

  show "bij_betw (zfact_iso_inv n) (carrier (ZFact (int n))) (carrier (mod_ring n))"
    using zfact_iso_inv_def mod_ring_def zfact_iso_bij[OF n_ge_0] bij_betw_inv_into
    by force
qed

lemma mod_ring_finite:
  "finite (carrier (mod_ring n))"
  by (simp add:mod_ring_def)

lemma mod_ring_carr:
  "x \<in> carrier (mod_ring n) \<longleftrightarrow>  x < n"
  by (simp add:mod_ring_def)

lemma mod_ring_is_cring:
  assumes n_ge_1: "n > 1"
  shows "cring (mod_ring n)"
proof -
  have n_ge_0: "n > 0" using n_ge_1 by simp

  interpret cring "ZFact (int n)"
    using ZFact_is_cring by simp

  have "cring ((mod_ring n) \<lparr> zero := zfact_iso_inv n \<zero>\<^bsub>ZFact (int n)\<^esub> \<rparr>)"
    by (rule ring_iso_imp_img_cring[OF zfact_iso_inv_is_ring_iso[OF n_ge_1]])
  moreover have 
    "(mod_ring n) \<lparr> zero := zfact_iso_inv n \<zero>\<^bsub>ZFact (int n)\<^esub> \<rparr> = mod_ring n"
    using zfact_iso_inv_0[OF n_ge_0]
    by (simp add:mod_ring_def)
  ultimately show ?thesis by simp
qed

lemma zfact_iso_is_ring_iso:
  assumes n_ge_1: "n > 1"
  shows "zfact_iso n \<in> ring_iso (mod_ring n) (ZFact (int n))"
proof -
  have r:"ring (ZFact (int n))"
    using ZFact_is_cring cring.axioms(1) by blast

  interpret s: ring "(mod_ring n)"
    using mod_ring_is_cring cring.axioms(1) n_ge_1 by blast
  have n_ge_0: "n > 0" using n_ge_1 by linarith

  have 
    "inv_into (carrier (ZFact (int n))) (zfact_iso_inv n) 
      \<in> ring_iso (mod_ring n) (ZFact (int n))"
    using ring_iso_set_sym[OF r zfact_iso_inv_is_ring_iso[OF n_ge_1]] by simp
  moreover have "\<And>x. x \<in> carrier (mod_ring n) \<Longrightarrow> 
    inv_into (carrier (ZFact (int n))) (zfact_iso_inv n) x = zfact_iso n x"
  proof -
    fix x
    assume "x \<in> carrier (mod_ring n)"
    hence "x \<in> {..<n}" by (simp add:mod_ring_def)
    thus "inv_into (carrier (ZFact (int n))) (zfact_iso_inv n) x = zfact_iso n x"
      unfolding zfact_iso_inv_def
      by (simp add:inv_into_inv_into_eq[OF zfact_iso_bij[OF n_ge_0]])
  qed

  ultimately show ?thesis 
    using s.ring_iso_restrict by blast
qed

text \<open>If @{term "p"} is a prime than @{term "mod_ring p"} is a field:\<close>

lemma mod_ring_is_field:
  assumes"Factorial_Ring.prime p"
  shows "field (mod_ring p)"
proof -
  have p_ge_0: "p > 0" using assms prime_gt_0_nat by blast
  have p_ge_1: "p > 1" using assms prime_gt_1_nat by blast

  interpret field "ZFact (int p)"
    using zfact_prime_is_field[OF assms] by simp

  have "field ((mod_ring p) \<lparr> zero := zfact_iso_inv p \<zero>\<^bsub>ZFact (int p)\<^esub> \<rparr>)"
    by (rule ring_iso_imp_img_field[OF zfact_iso_inv_is_ring_iso[OF p_ge_1]])

  moreover have 
    "(mod_ring p) \<lparr> zero := zfact_iso_inv p \<zero>\<^bsub>ZFact (int p)\<^esub> \<rparr> = mod_ring p"
    using zfact_iso_inv_0[OF p_ge_0]
    by (simp add:mod_ring_def)
  ultimately show ?thesis by simp
qed

end
