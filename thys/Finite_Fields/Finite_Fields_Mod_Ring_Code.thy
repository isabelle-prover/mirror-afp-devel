section \<open>Executable Factor Rings\<close>

theory Finite_Fields_Mod_Ring_Code
  imports Finite_Fields_Indexed_Algebra_Code Ring_Characteristic
begin

definition mod_ring :: "nat \<Rightarrow> nat idx_ring_enum"
  where "mod_ring n = \<lparr>
    idx_pred = (\<lambda>x. x < n),
    idx_uminus = (\<lambda>x. (n-x) mod n),
    idx_plus = (\<lambda>x y. (x+y) mod n),
    idx_udivide = (\<lambda>x. nat (fst (bezout_coefficients (int x) (int n)) mod (int n))),
    idx_mult = (\<lambda>x y. (x*y) mod n),
    idx_zero = 0,
    idx_one = 1,
    idx_size = n,
    idx_enum = id,
    idx_enum_inv = id
   \<rparr>"

lemma zfact_iso_0:
  assumes "n > 0"
  shows "zfact_iso n 0 = \<zero>\<^bsub>ZFact (int n)\<^esub>"
proof -
  let ?I = "Idl\<^bsub>\<Z>\<^esub> {int n}"
  have ideal_I: "ideal ?I \<Z>"
    by (simp add: int.genideal_ideal)

  interpret i:ideal "?I" "\<Z>" using ideal_I by simp
  interpret s:ring_hom_ring "\<Z>" "ZFact (int n)" "(+>\<^bsub>\<Z>\<^esub>) ?I"
   using i.rcos_ring_hom_ring ZFact_def by auto

  show ?thesis
    by (simp add:zfact_iso_def ZFact_def)
qed

lemma zfact_prime_is_field:
  assumes "Factorial_Ring.prime (p :: nat)"
  shows "field (ZFact (int p))"
  using zfact_prime_is_finite_field[OF assms] finite_field_def by auto

definition zfact_iso_inv :: "nat \<Rightarrow> int set \<Rightarrow> nat" where
  "zfact_iso_inv p = the_inv_into {..<p} (zfact_iso p)"

lemma zfact_iso_inv_0:
  assumes n_ge_0: "n > 0"
  shows "zfact_iso_inv n \<zero>\<^bsub>ZFact (int n)\<^esub> = 0"
  unfolding zfact_iso_inv_def zfact_iso_0[OF n_ge_0, symmetric] using n_ge_0
  by (rule the_inv_into_f_f[OF zfact_iso_inj], simp add:mod_ring_def)

lemma zfact_coset:
  assumes n_ge_0: "n > 0"
  assumes "x \<in> carrier (ZFact (int n))"
  defines "I \<equiv> Idl\<^bsub>\<Z>\<^esub> {int n}"
  shows "x = I +>\<^bsub>\<Z>\<^esub> (int (zfact_iso_inv n x))"
proof -
  have "x \<in> zfact_iso n ` {..<n}"
    using assms zfact_iso_ran by simp
  hence "zfact_iso n (zfact_iso_inv n x) = x"
    unfolding zfact_iso_inv_def by (intro f_the_inv_into_f zfact_iso_inj) auto
  thus ?thesis unfolding zfact_iso_def I_def by blast
qed

lemma zfact_iso_inv_bij:
  assumes "n > 0"
  shows "bij_betw (zfact_iso_inv n) (carrier (ZFact (int n))) (carrier (ring_of (mod_ring n)))"
proof -
  have "bij_betw (the_inv_into {..<n} (zfact_iso n)) (carrier (ZFact (int n))) {..<n}"
    by (intro bij_betw_the_inv_into zfact_iso_bij[OF assms])
  thus ?thesis
    unfolding zfact_iso_inv_def mod_ring_def ring_of_def lessThan_def by simp
qed

lemma zfact_iso_inv_is_ring_iso:
  fixes n :: nat
  assumes n_ge_1: "n > 1"
  shows "zfact_iso_inv n \<in> ring_iso (ZFact (int n)) (ring_of (mod_ring n))" (is "?f \<in> _")
proof (rule ring_iso_memI)
  interpret r:cring "(ZFact (int n))"
    using ZFact_is_cring by simp

  define I where "I = Idl\<^bsub>\<Z>\<^esub> {int n}"

  have n_ge_0: "n > 0" using n_ge_1 by simp

  interpret i:ideal "I" "\<Z>"
    unfolding I_def using int.genideal_ideal by simp

  interpret s:ring_hom_ring "\<Z>" "ZFact (int n)" "(+>\<^bsub>\<Z>\<^esub>) I"
   using i.rcos_ring_hom_ring ZFact_def I_def by auto

  show "zfact_iso_inv n x \<in> carrier (ring_of (mod_ring n))" if "x \<in> carrier (ZFact (int n))" for x
  proof -
    have "zfact_iso_inv n x \<in> {..<n}"
      unfolding zfact_iso_inv_def using that zfact_iso_ran[OF n_ge_0]
      by (intro the_inv_into_into zfact_iso_inj n_ge_0) auto
    thus "zfact_iso_inv n x \<in> carrier (ring_of (mod_ring n))"
      by (simp add:ring_of_def mod_ring_def)
  qed

  show "?f (x \<otimes>\<^bsub>ZFact (int n)\<^esub> y) = ?f x \<otimes>\<^bsub>ring_of (mod_ring n)\<^esub> ?f y"
    if x_carr: "x \<in> carrier (ZFact (int n))" and y_carr: "y \<in> carrier (ZFact (int n))" for x y
  proof -
    define x' where "x' = zfact_iso_inv n x"
    define y' where "y' = zfact_iso_inv n y"
    have "x \<otimes>\<^bsub>ZFact (int n)\<^esub> y = (I +>\<^bsub>\<Z>\<^esub> (int x')) \<otimes>\<^bsub>ZFact (int n)\<^esub> (I +>\<^bsub>\<Z>\<^esub> (int y'))"
      unfolding x'_def y'_def
      using x_carr y_carr zfact_coset[OF n_ge_0] I_def by simp
    also have "... = (I +>\<^bsub>\<Z>\<^esub> (int x' * int y'))"
      by simp
    also have "... = (I +>\<^bsub>\<Z>\<^esub> (int ((x' * y') mod n)))"
      unfolding I_def zmod_int by (rule int_cosetI[OF n_ge_0],simp)
    also have "... = (I +>\<^bsub>\<Z>\<^esub> (x' \<otimes>\<^bsub>ring_of (mod_ring n)\<^esub> y'))"
      unfolding ring_of_def mod_ring_def by simp
    also have "... = zfact_iso n (x' \<otimes>\<^bsub>ring_of (mod_ring n)\<^esub> y')"
      unfolding zfact_iso_def I_def by simp
    finally have a:"x \<otimes>\<^bsub>ZFact (int n)\<^esub> y = zfact_iso n (x' \<otimes>\<^bsub>ring_of (mod_ring n)\<^esub> y')"
      by simp
    have b:"x' \<otimes>\<^bsub>ring_of (mod_ring n)\<^esub> y' \<in> {..<n}"
      using mod_ring_def n_ge_0 by (auto simp:ring_of_def)
    have "?f (zfact_iso n (x' \<otimes>\<^bsub>ring_of (mod_ring n)\<^esub> y')) = x' \<otimes>\<^bsub>ring_of (mod_ring n)\<^esub> y'"
      unfolding zfact_iso_inv_def
      by (rule the_inv_into_f_f[OF zfact_iso_inj[OF n_ge_0] b])
    thus
      "zfact_iso_inv n (x \<otimes>\<^bsub>ZFact (int n)\<^esub> y) =
      zfact_iso_inv n x \<otimes>\<^bsub>ring_of (mod_ring n)\<^esub> zfact_iso_inv n y"
      using a x'_def y'_def by simp
  qed

  show "zfact_iso_inv n (x \<oplus>\<^bsub>ZFact (int n)\<^esub> y) =
    zfact_iso_inv n x \<oplus>\<^bsub>ring_of (mod_ring n)\<^esub> zfact_iso_inv n y"
    if x_carr: "x \<in> carrier (ZFact (int n))" and y_carr: "y \<in> carrier (ZFact (int n))" for x y
  proof -
    define x' where "x' = zfact_iso_inv n x"
    define y' where "y' = zfact_iso_inv n y"
    have "x \<oplus>\<^bsub>ZFact (int n)\<^esub> y = (I +>\<^bsub>\<Z>\<^esub> (int x')) \<oplus>\<^bsub>ZFact (int n)\<^esub> (I +>\<^bsub>\<Z>\<^esub> (int y'))"
      unfolding x'_def y'_def
      using x_carr y_carr zfact_coset[OF n_ge_0] I_def by simp
    also have "... = (I +>\<^bsub>\<Z>\<^esub> (int x' + int y'))"
      by simp
    also have "... = (I +>\<^bsub>\<Z>\<^esub> (int ((x' + y') mod n)))"
      unfolding I_def zmod_int by (rule int_cosetI[OF n_ge_0],simp)
    also have "... = (I +>\<^bsub>\<Z>\<^esub> (x' \<oplus>\<^bsub>ring_of (mod_ring n)\<^esub> y'))"
      unfolding mod_ring_def ring_of_def by simp
    also have "... = zfact_iso n (x' \<oplus>\<^bsub>ring_of (mod_ring n)\<^esub> y')"
      unfolding zfact_iso_def I_def by simp
    finally have a:"x \<oplus>\<^bsub>ZFact (int n)\<^esub> y = zfact_iso n (x' \<oplus>\<^bsub>ring_of (mod_ring n)\<^esub> y')"
      by simp
    have b:"x' \<oplus>\<^bsub>ring_of (mod_ring n)\<^esub> y' \<in> {..<n}"
      using mod_ring_def n_ge_0 by (auto simp:ring_of_def)
    have "?f (zfact_iso n (x' \<oplus>\<^bsub>ring_of (mod_ring n)\<^esub> y')) = x' \<oplus>\<^bsub>ring_of (mod_ring n)\<^esub> y'"
      unfolding zfact_iso_inv_def
      by (rule the_inv_into_f_f[OF zfact_iso_inj[OF n_ge_0] b])
    thus "?f (x \<oplus>\<^bsub>ZFact (int n)\<^esub> y) = ?f x \<oplus>\<^bsub>ring_of (mod_ring n)\<^esub> ?f y"
      using a x'_def y'_def by simp
  qed

  have "\<one>\<^bsub>ZFact (int n)\<^esub> = zfact_iso n (\<one>\<^bsub>ring_of (mod_ring n)\<^esub>)"
    by (simp add:zfact_iso_def ZFact_def I_def[symmetric] ring_of_def mod_ring_def)

  thus "zfact_iso_inv n \<one>\<^bsub>ZFact (int n)\<^esub> = \<one>\<^bsub>ring_of (mod_ring n)\<^esub>"
    unfolding zfact_iso_inv_def mod_ring_def ring_of_def
    using the_inv_into_f_f[OF zfact_iso_inj] n_ge_1 by simp

  show "bij_betw (zfact_iso_inv n) (carrier (ZFact (int n))) (carrier (ring_of (mod_ring n)))"
    by (intro zfact_iso_inv_bij n_ge_0)
qed

lemma mod_ring_finite:
  "finite (carrier (ring_of (mod_ring n)))"
  by (simp add:mod_ring_def ring_of_def)

lemma mod_ring_carr:
  "x \<in> carrier (ring_of (mod_ring n)) \<longleftrightarrow>  x < n"
  by (simp add:mod_ring_def ring_of_def)

lemma mod_ring_is_cring:
  assumes n_ge_1: "n > 1"
  shows "cring (ring_of (mod_ring n))"
proof -
  have n_ge_0: "n > 0" using n_ge_1 by simp

  interpret cring "ZFact (int n)"
    using ZFact_is_cring by simp

  have "cring ((ring_of (mod_ring n)) \<lparr> zero := zfact_iso_inv n \<zero>\<^bsub>ZFact (int n)\<^esub> \<rparr>)"
    by (rule ring_iso_imp_img_cring[OF zfact_iso_inv_is_ring_iso[OF n_ge_1]])
  moreover have
    "ring_of (mod_ring n) \<lparr> zero := zfact_iso_inv n \<zero>\<^bsub>ZFact (int n)\<^esub> \<rparr> = ring_of (mod_ring n)"
    using zfact_iso_inv_0[OF n_ge_0] by (simp add:mod_ring_def ring_of_def)
  ultimately show ?thesis by simp
qed

lemma zfact_iso_is_ring_iso:
  assumes n_ge_1: "n > 1"
  shows "zfact_iso n \<in> ring_iso (ring_of (mod_ring n)) (ZFact (int n))"
proof -
  have r:"ring (ZFact (int n))"
    using ZFact_is_cring cring.axioms(1) by blast

  interpret s: ring "(ring_of (mod_ring n))"
    using mod_ring_is_cring cring.axioms(1) n_ge_1 by blast
  have n_ge_0: "n > 0" using n_ge_1 by linarith

  have "inv_into (carrier (ZFact (int n))) (zfact_iso_inv n)
      \<in> ring_iso (ring_of (mod_ring n)) (ZFact (int n))"
    using ring_iso_set_sym[OF r zfact_iso_inv_is_ring_iso[OF n_ge_1]] by simp
  moreover have "inv_into (carrier (ZFact (int n))) (zfact_iso_inv n) x = zfact_iso n x"
    if "x \<in> carrier (ring_of (mod_ring n))" for x
  proof -
    have "x \<in> {..<n}" using that by (simp add:mod_ring_def ring_of_def)
    thus "inv_into (carrier (ZFact (int n))) (zfact_iso_inv n) x = zfact_iso n x"
      using zfact_iso_inv_bij[OF n_ge_0] zfact_iso_bij[OF n_ge_0] unfolding zfact_iso_inv_def
      by (intro inv_into_f_eq bij_betw_apply[OF zfact_iso_inv_bij[OF n_ge_0]] the_inv_into_f_f)
       (auto intro:bij_betw_imp_inj_on simp:bij_betwE)
  qed

  ultimately show ?thesis using s.ring_iso_restrict by blast
qed

text \<open>If @{term "p"} is a prime than @{term "mod_ring p"} is a field:\<close>

lemma mod_ring_is_field:
  assumes"Factorial_Ring.prime p"
  shows "field (ring_of (mod_ring p))"
proof -
  have p_ge_0: "p > 0" using assms prime_gt_0_nat by blast
  have p_ge_1: "p > 1" using assms prime_gt_1_nat by blast

  interpret field "ZFact (int p)"
    using zfact_prime_is_field[OF assms] by simp

  have "field ((ring_of (mod_ring p)) \<lparr> zero := zfact_iso_inv p \<zero>\<^bsub>ZFact (int p)\<^esub> \<rparr>)"
    by (rule ring_iso_imp_img_field[OF zfact_iso_inv_is_ring_iso[OF p_ge_1]])

  moreover have
    "(ring_of (mod_ring p)) \<lparr> zero := zfact_iso_inv p \<zero>\<^bsub>ZFact (int p)\<^esub> \<rparr> = ring_of (mod_ring p)"
    using zfact_iso_inv_0[OF p_ge_0] by (simp add:mod_ring_def ring_of_def)
  ultimately show ?thesis by simp
qed

lemma mod_ring_is_ring_c:
  assumes "n > 1"
  shows "cring\<^sub>C (mod_ring n)"
proof (intro cring_cI mod_ring_is_cring assms)
  fix x
  assume a:"x \<in> carrier (ring_of (mod_ring n))"
  hence x_le_n: "x < n" unfolding mod_ring_def ring_of_def by simp

  interpret cring "(ring_of (mod_ring n))" by (intro mod_ring_is_cring assms)

  show "-\<^sub>C\<^bsub>mod_ring n\<^esub> x = \<ominus>\<^bsub>ring_of (mod_ring n)\<^esub> x" using x_le_n
    by (intro minus_equality[symmetric] a) (simp_all add:ring_of_def mod_ring_def mod_simps)
next
  fix x
  assume a:"x \<in> Units (ring_of (mod_ring n))"

  let ?l = "fst (bezout_coefficients (int x) (int n))"
  let ?r = "snd (bezout_coefficients (int x) (int n))"

  interpret cring "ring_of (mod_ring n)" by (intro mod_ring_is_cring assms)

  obtain y where "x \<otimes>\<^bsub>ring_of (mod_ring n)\<^esub> y = \<one>\<^bsub>ring_of (mod_ring n)\<^esub>"
    using a by (meson Units_r_inv_ex)
  hence "x * y mod n = 1" by (simp_all add:mod_ring_def ring_of_def)
  hence "gcd x n = 1" by (metis dvd_triv_left gcd.assoc gcd_1_nat gcd_nat.absorb_iff1 gcd_red_nat)
  hence 0:"gcd (int x) (int n) = 1" unfolding gcd_int_int_eq by simp

  have "int x * ?l mod int n = (?l * int x + ?r * int n) mod int n"
    using assms by (simp add:mod_simps algebra_simps)
  also have "... = (gcd (int x) (int n)) mod int n"
    by (intro arg_cong2[where f="(mod)"] refl bezout_coefficients) simp
  also have "... = 1" unfolding 0 using assms by simp
  finally have "int x * ?l mod int n = 1" by simp
  hence "int x * nat (fst (bezout_coefficients (int x) (int n)) mod int n) mod n = 1"
    using assms by (simp add:mod_simps)
  hence "x * nat (fst (bezout_coefficients (int x) (int n)) mod int n) mod n = 1"
    by (metis nat_mod_as_int nat_one_as_int of_nat_mult)
  hence "x \<otimes>\<^bsub>ring_of (mod_ring n)\<^esub> x \<inverse>\<^sub>C\<^bsub>mod_ring n\<^esub> = \<one>\<^bsub>ring_of (mod_ring n)\<^esub>"
    using assms unfolding mod_ring_def ring_of_def by simp
  moreover have "nat (fst (bezout_coefficients (int x) (int n)) mod int n) < n"
    using assms by (subst nat_less_iff) auto
  hence "x \<inverse>\<^sub>C\<^bsub>mod_ring n\<^esub> \<in> carrier (ring_of (mod_ring n))"
    using assms unfolding mod_ring_def ring_of_def by simp
  moreover have "x \<in> carrier (ring_of (mod_ring n))" using a by auto
  ultimately show "x \<inverse>\<^sub>C\<^bsub>mod_ring n\<^esub> = inv\<^bsub>ring_of (mod_ring n)\<^esub> x"
    by (intro comm_inv_char[symmetric])
qed

lemma mod_ring_is_field_c:
  assumes"Factorial_Ring.prime p"
  shows "field\<^sub>C (mod_ring p)"
  unfolding field\<^sub>C_def domain\<^sub>C_def
  by (intro conjI mod_ring_is_ring_c mod_ring_is_field assms prime_gt_1_nat
      domain.axioms(1) field.axioms(1))

lemma mod_ring_is_enum_c:
  shows "enum\<^sub>C (mod_ring n)"
  by (intro enum_cI) (simp_all add:mod_ring_def ring_of_def Coset.order_def lessThan_def)

end