(*  
    Author:      René Thiemann 
                 Akihisa Yamada
    License:     BSD
*)
section \<open>Several Locales for Homomorphisms Between Types.\<close>

theory Ring_Hom
imports 
  Int
  Main
begin

locale semiring_hom = 
  fixes hom :: "'a :: comm_semiring_1 \<Rightarrow> 'b :: comm_semiring_1"
  assumes 
    hom_add: "hom (x + y) = hom x + hom y" and
    hom_mult: "hom (x * y) = hom x * hom y" and
    hom_zero: "hom 0 = 0" and
    hom_one: "hom 1 = 1"
begin

named_theorems hom_ring_simps

lemmas [hom_ring_simps,simp] = hom_zero hom_add hom_one hom_mult

lemma hom_zero_sum[hom_ring_simps,simp]: assumes "x + y = 0" shows "hom x + hom y = 0"
proof -
  have "0 = x + y" using assms..
  hence "hom 0 = hom (x + y)" by simp
  thus ?thesis by auto
qed

lemma hom_zero_prod[hom_ring_simps,simp]: assumes "x * y = 0" shows "hom x * hom y = 0"
proof -
  have "0 = x * y" using assms..
  hence "hom 0 = hom (x * y)" by simp
  thus ?thesis by auto
qed


lemma hom_power[hom_ring_simps,simp]: "hom (x ^ n) = hom x ^ n"
  by (induct n, auto)

lemma hom_sum[hom_ring_simps,simp]: "hom (sum f A) = sum (\<lambda> x. hom (f x)) A"
  by (induct A rule: infinite_finite_induct, auto)

lemma hom_setprod[hom_ring_simps,simp]: "hom (setprod f A) = setprod (\<lambda>x. hom (f x)) A"
  by (induct A rule: infinite_finite_induct, auto)

lemma hom_prod_list[hom_ring_simps,simp]: "hom (prod_list xs) = prod_list (map hom xs)"
  by (induct xs, auto)

lemma hom_sum_list[hom_ring_simps,simp]: "hom (sum_list xs) = sum_list (map hom xs)"
  by (induct xs, auto)

end

locale ring_hom = semiring_hom hom
  for hom :: "'a :: comm_ring_1 \<Rightarrow> 'b :: comm_ring_1"
begin

lemma hom_uminus[hom_ring_simps,simp]: "hom (-x) = - (hom x)"
  by(unfold eq_neg_iff_add_eq_0, auto)

sublocale semiring_hom..

lemma hom_minus [hom_ring_simps,simp]: "hom (x - y) = hom x - hom y"
  unfolding diff_conv_add_uminus hom_ring_simps..

lemma hom_dvd: assumes "p dvd q"
  shows "hom p dvd hom q"
proof -
  from assms obtain r where "q = p * r" unfolding dvd_def by auto
  from arg_cong[OF this, of hom, unfolded hom_mult] show ?thesis unfolding dvd_def by auto
qed
end

locale inj_semiring_hom = semiring_hom +
  assumes hom_inj: "hom x = hom y \<Longrightarrow> x = y"
begin
  sublocale semiring_hom..
  lemma hom_0_iff[simp]: "hom x = 0 \<longleftrightarrow> x = 0" using hom_inj[of _ 0] by auto
  lemma hom_1_iff[simp]: "hom x = 1 \<longleftrightarrow> x = 1" using hom_inj[of _ 1] by auto
  lemma hom_eq_iff[simp]: "hom x = hom y \<longleftrightarrow> x = y" using hom_inj by auto
end

locale inj_ring_hom = ring_hom hom + inj_semiring_hom hom
  for hom :: "'a :: comm_ring_1 \<Rightarrow> 'b :: comm_ring_1"
begin
  sublocale semiring_hom..
end

locale field_hom = ring_hom hom
  for hom :: "'a :: field \<Rightarrow> 'b :: field"
begin

lemma hom_inverse: "hom (inverse x) = inverse (hom x)"
  by (metis hom_mult hom_one hom_zero inverse_unique inverse_zero right_inverse)

lemma hom_divide: "hom (x / y) = hom x / hom y"
proof -
  have "hom (x / y) = hom (x * inverse y)" by (simp add: field_simps)
  thus ?thesis unfolding hom_ring_simps hom_inverse by (simp add: field_simps)
qed

declare hom_inverse[simp] hom_divide[simp]
lemmas hom_field_simps = hom_ring_simps hom_inverse hom_divide

end

locale inj_field_hom = field_hom hom + inj_semiring_hom hom
  for hom :: "'a :: field \<Rightarrow> 'b :: field"
begin
sublocale inj_ring_hom ..
end

locale inj_field_hom_0 = inj_field_hom hom
  for hom :: "'a :: field_char_0 \<Rightarrow> 'b :: field_char_0"

end
