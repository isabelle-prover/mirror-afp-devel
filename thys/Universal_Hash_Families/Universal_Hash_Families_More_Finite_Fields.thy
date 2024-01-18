section \<open>Finite Fields\<close>

theory Universal_Hash_Families_More_Finite_Fields
  imports Finite_Fields.Finite_Fields_Mod_Ring_Code
begin

text \<open>This theory have been moved to @{theory "Finite_Fields.Finite_Fields_Mod_Ring_Code"}, where
@{term "mod_ring n"} corresponds to @{term "ring_of (mod_ring n)"}. The lemmas and definitions here
are kept to prevent merge-conflicts.\<close>

lemmas zfact_iso_0 = zfact_iso_0
lemmas zfact_prime_is_field = zfact_prime_is_field

hide_const (open) Multiset.mult

definition mod_ring :: "nat => nat ring"
  where "mod_ring n = \<lparr>
    carrier = {..<n},
    mult = (\<lambda> x y. (x * y) mod n),
    one = 1,
    zero = 0,
    add = (\<lambda> x y. (x + y) mod n) \<rparr>"

definition zfact_iso_inv :: "nat \<Rightarrow> int set \<Rightarrow> nat" where
  "zfact_iso_inv p = inv_into {..<p} (zfact_iso p)"

lemma zfact_iso_inv_compat:
  assumes "n > 0"
  assumes "x \<in> carrier (ZFact (int n))"
  shows "zfact_iso_inv n x = Finite_Fields_Mod_Ring_Code.zfact_iso_inv n x"
proof -
  have "Finite_Fields_Mod_Ring_Code.zfact_iso_inv n x \<in> {..<n}"
    using bij_betw_apply[OF zfact_iso_inv_bij[OF assms(1)] assms(2)]
    by (simp add:Finite_Fields_Mod_Ring_Code.mod_ring_def ring_of_def)
  moreover have "zfact_iso n (Finite_Fields_Mod_Ring_Code.zfact_iso_inv n x) = x"
    unfolding Finite_Fields_Mod_Ring_Code.zfact_iso_inv_def
    using zfact_iso_bij[OF assms(1)] assms(2)
    by (intro f_the_inv_into_f) (simp_all add:bij_betw_def)
  ultimately show ?thesis
    unfolding zfact_iso_inv_def by (intro inv_into_f_eq zfact_iso_inj assms) auto
qed

lemma mod_ring_compat:
  "mod_ring n = ring_of (Finite_Fields_Mod_Ring_Code.mod_ring n)"
  unfolding mod_ring_def Finite_Fields_Mod_Ring_Code.mod_ring_def ring_of_def by auto

lemma zfact_iso_inv_0:
  assumes n_ge_0: "n > 0"
  shows "zfact_iso_inv n \<zero>\<^bsub>ZFact (int n)\<^esub> = 0" (is "?L = ?R")
proof -
  interpret r:cring "(ZFact (int n))" using ZFact_is_cring by simp

  have "?L = Finite_Fields_Mod_Ring_Code.zfact_iso_inv n \<zero>\<^bsub>ZFact (int n)\<^esub>"
    by (intro zfact_iso_inv_compat[OF assms]) simp
  also have "... = 0" using zfact_iso_inv_0[OF assms] by simp
  finally show ?thesis by simp
qed

lemma zfact_coset:
  assumes n_ge_0: "n > 0"
  assumes "x \<in> carrier (ZFact (int n))"
  defines "I \<equiv> Idl\<^bsub>\<Z>\<^esub> {int n}"
  shows "x = I +>\<^bsub>\<Z>\<^esub> (int (zfact_iso_inv n x))"
proof -
  have "x = I +>\<^bsub>\<Z>\<^esub> (int (Finite_Fields_Mod_Ring_Code.zfact_iso_inv n x))"
    unfolding I_def by (intro zfact_coset[OF assms(1,2)])
  also have "... = I +>\<^bsub>\<Z>\<^esub> (int (zfact_iso_inv n x))"
    using zfact_iso_inv_compat[OF assms(1,2)] by simp
  finally show ?thesis by simp
qed

lemma zfact_iso_inv_is_ring_iso:
  assumes n_ge_1: "n > 1"
  shows "zfact_iso_inv n \<in> ring_iso (ZFact (int n)) (mod_ring n)"
proof -
  interpret r:cring "(ZFact (int n))" using ZFact_is_cring by simp

  show ?thesis
    unfolding mod_ring_compat using assms
    by (intro r.ring_iso_restrict[OF zfact_iso_inv_is_ring_iso[OF n_ge_1]]
        zfact_iso_inv_compat[symmetric]) auto
qed

lemma mod_ring_finite:
  "finite (carrier (mod_ring n))"
  using mod_ring_finite mod_ring_compat by auto

lemma mod_ring_carr:
  "x \<in> carrier (mod_ring n) \<longleftrightarrow>  x < n"
  using mod_ring_carr mod_ring_compat by auto

lemma mod_ring_is_cring:
  assumes n_ge_1: "n > 1"
  shows "cring (mod_ring n)"
  using mod_ring_is_cring[OF assms] mod_ring_compat by auto

lemma zfact_iso_is_ring_iso:
  assumes n_ge_1: "n > 1"
  shows "zfact_iso n \<in> ring_iso (mod_ring n) (ZFact (int n))"
  using zfact_iso_is_ring_iso[OF assms] mod_ring_compat by auto

text \<open>If @{term "p"} is a prime than @{term "mod_ring p"} is a field:\<close>

lemma mod_ring_is_field:
  assumes"Factorial_Ring.prime p"
  shows "field (mod_ring p)"
  using mod_ring_is_field[OF assms] mod_ring_compat by auto

end
