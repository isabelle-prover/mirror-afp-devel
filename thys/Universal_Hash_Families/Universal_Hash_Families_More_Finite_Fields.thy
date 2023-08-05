section \<open>Finite Fields\<close>

theory Universal_Hash_Families_More_Finite_Fields
  imports
    Finite_Fields.Ring_Characteristic
    "HOL-Algebra.Ring_Divisibility"
    "HOL-Algebra.IntRing"
begin

text \<open>In some applications it is more convenient to work with natural numbers instead of
@{term "ZFact p"} whose elements are cosets. To support that use case the following definition
introduces an additive and multiplicative structure on @{term "{..<p}"}. After verifying that
the function @{term "zfact_iso"} and its inverse are homomorphisms, the ring and field property
can be transfered from @{term "ZFact p"} to to the structure on @{term "{..<p}"}.\<close>

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
    unfolding I_def using int.genideal_ideal by simp

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
      unfolding I_def zmod_int by (rule int_cosetI[OF n_ge_0],simp)
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
      unfolding I_def zmod_int by (rule int_cosetI[OF n_ge_0],simp)
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
