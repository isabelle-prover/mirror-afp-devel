(*  
    Author:      René Thiemann 
                 Akihisa Yamada
    License:     BSD
*)
section \<open>Several Locales for Homomorphisms Between Types.\<close>

theory Ring_Hom
imports 
  Complex
  Main
  "~~/src/HOL/Library/Multiset"
  "~~/src/HOL/Computational_Algebra/Factorial_Ring"
begin

hide_const (open) mult

text {* Distribution lemmas for homomorphisms. *}
named_theorems hom_distribs

text {* Lemmas that will remove homomorphisms. *}
named_theorems hom_removes

locale zero_hom =
  fixes hom :: "'a :: zero \<Rightarrow> 'b :: zero"
  assumes hom_zero[simp,hom_removes]: "hom 0 = 0"

locale one_hom =
  fixes hom :: "'a :: one \<Rightarrow> 'b :: one"
  assumes hom_one[simp,hom_removes]: "hom 1 = 1"

locale times_hom =
  fixes hom :: "'a :: times \<Rightarrow> 'b :: times"
  assumes hom_mult[hom_distribs,simp]: "hom (x * y) = hom x * hom y"

locale plus_hom =
  fixes hom :: "'a :: plus \<Rightarrow> 'b :: plus"
  assumes hom_add[hom_distribs,simp]: "hom (x + y) = hom x + hom y"

locale monoid_mult_hom = one_hom hom + times_hom hom
  for hom :: "'a :: monoid_mult \<Rightarrow> 'b :: monoid_mult"
begin
  lemma hom_prod_list[hom_distribs,simp]: "hom (prod_list xs) = prod_list (map hom xs)"
    by (induct xs, auto)
  lemma hom_power[hom_distribs,simp]: "hom (x ^ n) = hom x ^ n"
    by (induct n, auto)
end

locale monoid_add_hom = zero_hom hom + plus_hom hom
  for hom :: "'a :: monoid_add \<Rightarrow> 'b :: monoid_add"
begin
  lemma hom_sum_list[hom_distribs,simp]: "hom (sum_list xs) = sum_list (map hom xs)"
    by (induct xs, auto)
  lemma hom_add_eq_zero: assumes "x + y = 0" shows "hom x + hom y = 0"
  proof -
    have "0 = x + y" using assms..
    hence "hom 0 = hom (x + y)" by simp
    thus ?thesis by auto
  qed
end

locale group_add_hom = monoid_add_hom hom
  for hom :: "'a :: group_add \<Rightarrow> 'b :: group_add"
begin
  lemma hom_uminus[hom_distribs,simp]: "hom (-x) = - hom x"
    by (simp add: eq_neg_iff_add_eq_0 hom_add_eq_zero)
  lemma hom_minus [hom_distribs,simp]: "hom (x - y) = hom x - hom y"
    unfolding diff_conv_add_uminus hom_distribs..
end

locale semiring_hom = monoid_add_hom hom + monoid_mult_hom hom
  for hom :: "'a :: semiring_1 \<Rightarrow> 'b :: semiring_1"
begin
  lemma hom_mult_eq_zero: assumes "x * y = 0" shows "hom x * hom y = 0"
  proof -
    have "0 = x * y" using assms..
    hence "hom 0 = hom (x * y)" by simp
    thus ?thesis by auto
  qed
end

locale ring_hom = semiring_hom hom
  for hom :: "'a :: ring_1 \<Rightarrow> 'b :: ring_1"
begin
  sublocale group_add_hom hom..
end

subsection {* Commutativity *}

locale comm_monoid_mult_hom = monoid_mult_hom hom
  for hom :: "'a :: comm_monoid_mult \<Rightarrow> 'b :: comm_monoid_mult"
begin
  lemma hom_prod[hom_distribs,simp]: "hom (prod f X) = (\<Prod>x \<in> X. hom (f x))"
    by (cases "finite X", induct rule:finite_induct; simp)
  lemma hom_prod_mset[hom_distribs,simp]: "hom (prod_mset X) = prod_mset (image_mset hom X)"
    by (induct X, auto)
  lemma hom_dvd[intro,simp]: assumes "p dvd q" shows "hom p dvd hom q"
  proof -
    from assms obtain r where "q = p * r" unfolding dvd_def by auto
    from arg_cong[OF this, of hom] show ?thesis unfolding dvd_def by auto
  qed
  lemma hom_dvd_1[hom_removes,simp]: "x dvd 1 \<Longrightarrow> hom x dvd 1" using hom_dvd[of x 1] by simp
end

locale comm_monoid_add_hom = monoid_add_hom hom
  for hom :: "'a :: comm_monoid_add \<Rightarrow> 'b :: comm_monoid_add"
begin
  lemma hom_sum[hom_distribs,simp]: "hom (sum f X) = (\<Sum>x \<in> X. hom (f x))"
    by (cases "finite X", induct rule:finite_induct; simp)
  lemma hom_sum_mset[hom_distribs,simp]: "hom (sum_mset X) = sum_mset (image_mset hom X)"
    by (induct X, auto)
end

locale comm_semiring_hom = semiring_hom hom
  for hom :: "'a :: comm_semiring_1 \<Rightarrow> 'b :: comm_semiring_1"
begin
  sublocale comm_monoid_mult_hom + comm_monoid_add_hom..
end

locale comm_ring_hom = ring_hom hom
  for hom :: "'a :: comm_ring_1 \<Rightarrow> 'b :: comm_ring_1"
begin
  sublocale comm_semiring_hom..
end

locale idom_hom = comm_ring_hom hom
  for hom :: "'a :: idom \<Rightarrow> 'b :: idom"

subsection {* Division *}

locale idom_divide_hom = idom_hom hom
  for hom :: "'a :: idom_divide \<Rightarrow> 'b :: idom_divide" +
  assumes hom_div[simp, hom_distribs]: "hom (x div y) = hom x div hom y"
begin

end

locale field_hom = idom_hom hom
  for hom :: "'a :: field \<Rightarrow> 'b :: field"
begin

  lemma hom_inverse[hom_distribs,simp]: "hom (inverse x) = inverse (hom x)"
    by (metis hom_mult hom_one hom_zero inverse_unique inverse_zero right_inverse)

  sublocale idom_divide_hom hom
  proof
    fix x y
    have "hom (x / y) = hom (x * inverse y)" by (simp add: field_simps)
    thus "hom (x / y) = hom x / hom y" unfolding hom_distribs by (simp add: field_simps)
  qed

end

locale field_char_0_hom = field_hom hom
  for hom :: "'a :: field_char_0 \<Rightarrow> 'b :: field_char_0"


subsection {* (Partial) Injectivitiy *}

locale zero_hom_0 = zero_hom +
  assumes hom_0: "\<And>x. hom x = 0 \<Longrightarrow> x = 0"
begin
  lemma hom_0_iff[iff,hom_removes]: "hom x = 0 \<longleftrightarrow> x = 0" using hom_0 by auto
end

locale one_hom_1 = one_hom +
  assumes hom_1: "\<And>x. hom x = 1 \<Longrightarrow> x = 1"
begin
  lemma hom_1_iff[iff,hom_removes]: "hom x = 1 \<longleftrightarrow> x = 1" using hom_1 by auto
end

locale injective =
  fixes f :: "'a \<Rightarrow> 'b" assumes injectivity: "\<And>x y. f x = f y \<Longrightarrow> x = y"
begin
  lemma eq_iff[simp,hom_removes]: "f x = f y \<longleftrightarrow> x = y" using injectivity by auto
  lemma inj_f: "inj f" by (auto intro: injI)
  lemma inv_f_f[simp]: "inv f (f x) = x" by (fact inv_f_f[OF inj_f])
end

locale inj_semiring_hom = semiring_hom + injective hom
begin
  sublocale zero_hom_0 + one_hom_1
    using injectivity[of _ 1] injectivity[of _ 0] by (unfold_locales, auto)
end

locale inj_comm_semiring_hom = comm_semiring_hom + injective hom
begin
  sublocale inj_semiring_hom ..
end

text {* For groups, injectivity is easily ensured. *}
locale inj_group_add_hom = group_add_hom + zero_hom_0
begin
  sublocale injective hom
  proof
    fix x y assume "hom x = hom y"
    then have "hom (x-y) = 0" by auto
    from this[unfolded hom_removes]
    show "x = y" by simp
  qed
end

locale inj_ring_hom = ring_hom + zero_hom_0
begin
  sublocale inj_group_add_hom..
  sublocale inj_semiring_hom..
end

locale inj_comm_ring_hom = comm_ring_hom + zero_hom_0
begin
  sublocale inj_ring_hom..
  sublocale inj_comm_semiring_hom..
end

locale inj_idom_hom = idom_hom + zero_hom_0
begin
  sublocale inj_comm_ring_hom..
end

text {* Field homomorphism is always injective. *}
context field_hom begin
  sublocale zero_hom_0
  proof (unfold_locales, rule ccontr)
    fix x
    assume "hom x = 0" and x0: "x \<noteq> 0"
    then have "inverse (hom x) = 0" by simp
    then have "hom (inverse x) = 0" by simp
    then have "hom (inverse x * x) = 0" by simp
    with x0 have "hom 1 = hom 0" by simp
    then have "(1 :: 'b) = 0" by simp
    then show False by auto
  qed
  sublocale inj_idom_hom..
end

subsection {* Surjectivity and Isomorphisms *}

locale surjective =
  fixes f :: "'a \<Rightarrow> 'b"
  assumes surj: "surj f"
begin
  lemma f_inv_f[simp]: "f (inv f x) = x"
     by (rule cong, auto simp: surj[unfolded surj_iff o_def id_def])
end

locale bijective = injective + surjective

lemma bijective_eq_bij: "bijective f = bij f"
proof(intro iffI)
  assume "bijective f"
  then interpret bijective f.
  show "bij f" using injectivity surj by (auto intro!: bijI injI)
next
  assume "bij f"
  from this[unfolded bij_def]
  show "bijective f" by (unfold_locales, auto dest: injD)
qed

context bijective
begin
  lemmas bij = bijective_axioms[unfolded bijective_eq_bij]
  lemma bijective_inv: "bijective (inv f)"
    using bijective_axioms bij_imp_bij_inv by (unfold bijective_eq_bij)
  lemma inv_inv_f_eq[simp]: "inv (inv f) = f" using inv_inv_eq[OF bij].
  lemma f_eq_iff[simp]: "f x = y \<longleftrightarrow> x = inv f y" by auto
  lemma inv_f_eq_iff[simp]: "inv f x = y \<longleftrightarrow> x = f y" by auto
end

locale semiring_isom = inj_semiring_hom hom + surjective hom for hom
begin
  sublocale bijective hom..
  sublocale inv: bijective "inv hom" by (fact bijective_inv)
  sublocale inv: inj_semiring_hom "inv hom"
  proof (unfold_locales)
    fix hx hy :: 'b
    from bij obtain x y where hx: "hx = hom x" and hy: "hy = hom y" by (meson bij_pointE)
    show "inv hom (hx+hy) = inv hom hx + inv hom hy" by (unfold hx hy, fold hom_add, simp)
    show "inv hom (hx*hy) = inv hom hx * inv hom hy" by (unfold hx hy, fold hom_mult, simp)
    have "inv hom (hom 0) = 0" by (unfold inv_f_f, simp)
    then show "inv hom 0 = 0" by simp
    have "inv hom (hom 1) = 1" by (unfold inv_f_f, simp)
    then show "inv hom 1 = 1" by simp
  qed
end

locale ring_isom = inj_ring_hom + surjective hom
begin
  sublocale semiring_isom..
  sublocale inv: semiring_isom "inv hom"..
  sublocale inv: inj_ring_hom "inv hom"..
end

locale comm_semiring_isom = inj_comm_semiring_hom hom + surjective hom for hom
begin
  sublocale semiring_isom..
  sublocale inv: semiring_isom "inv hom"..
  lemma hom_dvd_hom[simp,hom_removes]: "hom x dvd hom y \<longleftrightarrow> x dvd y"
  proof
    assume "hom x dvd hom y"
    then obtain hz where "hom y = hom x * hz" by (elim dvdE)
    moreover obtain z where "hz = hom z" using bij by (elim bij_pointE)
    ultimately have "hom y = hom (x * z)" by auto
    from this[unfolded eq_iff] have "y = x * z".
    then show "x dvd y" by (intro dvdI)
  qed (rule hom_dvd)

  lemma hom_dvd_simp[simp]:
    shows "hom x dvd y' \<longleftrightarrow> x dvd inv hom y'"
    using hom_dvd_hom[of x "inv hom y'"] by simp

  lemma inv_hom_dvd[simp]: "inv hom x' dvd y \<longleftrightarrow> x' dvd hom y"
  proof-
    interpret inv: comm_semiring_isom "inv hom"..
    show ?thesis by simp
  qed
end

locale comm_ring_isom = inj_comm_ring_hom + surjective hom
begin
  sublocale comm_semiring_isom..
  sublocale inv: comm_semiring_isom "inv hom"..
  sublocale inv: ring_isom "inv hom"..
end

locale idom_isom = inj_idom_hom + surjective hom
begin
  sublocale comm_ring_isom..
  sublocale inv: comm_ring_isom "inv hom"..
end

locale field_isom = field_hom + surjective hom
begin
  sublocale idom_isom..
  sublocale inv: idom_isom "inv hom"..
end

subsection {* Example Interpretations *}

interpretation of_int_hom: ring_hom of_int by (unfold_locales, auto)
interpretation of_int_hom: comm_ring_hom of_int by (unfold_locales, auto)
interpretation of_int_hom: idom_hom of_int by (unfold_locales, auto)
interpretation of_int_hom: inj_ring_hom "of_int :: int \<Rightarrow> 'a :: {ring_1,ring_char_0}"
  by (unfold_locales, auto)
interpretation of_int_hom: inj_comm_ring_hom "of_int :: int \<Rightarrow> 'a :: {comm_ring_1,ring_char_0}"
  by (unfold_locales, auto)
interpretation of_int_hom: inj_idom_hom "of_int :: int \<Rightarrow> 'a :: {idom,ring_char_0}"
  by (unfold_locales, auto)

text {* Somehow @{const of_rat} is defined only on @{text char_0}. *}
interpretation of_rat_hom: field_char_0_hom "of_rat"
  by (unfold_locales, auto simp: of_rat_add of_rat_mult of_rat_inverse of_rat_minus)

interpretation of_real_hom: inj_ring_hom of_real by (unfold_locales, auto)
interpretation of_real_hom: inj_comm_ring_hom of_real by (unfold_locales, auto)
interpretation of_real_hom: inj_idom_hom of_real by (unfold_locales, auto)
interpretation of_real_hom: field_hom of_real by (unfold_locales, auto)
interpretation of_real_hom: field_char_0_hom "of_real" by (unfold_locales, auto)

end
