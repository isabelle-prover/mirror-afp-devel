section \<open>Factorization into Monic Polynomials\label{sec:monic}\<close>

theory Monic_Polynomial_Factorization
imports
  Finite_Fields_Factorization_Ext
  Formal_Polynomial_Derivatives
begin

hide_const Factorial_Ring.multiplicity
hide_const Factorial_Ring.irreducible

lemma (in domain) finprod_mult_of:
  assumes "finite A"
  assumes "\<And>x. x \<in> A \<Longrightarrow> f x \<in> carrier (mult_of R)"
  shows "finprod R f A = finprod (mult_of R) f A"
  using assms by (induction A rule:finite_induct, auto) 

lemma (in ring) finite_poly:
  assumes "subring K R"
  assumes "finite K"
  shows 
    "finite {f. f \<in> carrier (K[X]) \<and> degree f = n}" (is "finite ?A")
    "finite {f. f \<in> carrier (K[X]) \<and> degree f \<le> n}" (is "finite ?B")
proof -
  have "finite {f. set f \<subseteq> K \<and> length f \<le> n + 1}" (is "finite ?C")
    using assms(2) finite_lists_length_le by auto
  moreover have "?B \<subseteq> ?C"
    by (intro subsetI) 
      (auto simp:univ_poly_carrier[symmetric] polynomial_def)
  ultimately show a: "finite ?B" 
    using finite_subset by auto
  moreover have "?A \<subseteq> ?B" 
    by (intro subsetI, simp)
  ultimately show "finite ?A"
    using finite_subset by auto
qed

definition pmult :: "_ \<Rightarrow> 'a list \<Rightarrow> 'a list \<Rightarrow> nat" ("pmult\<index>") 
  where "pmult\<^bsub>R\<^esub> d p = multiplicity (mult_of (poly_ring R)) d p" 

definition monic_poly :: "_ \<Rightarrow> 'a list \<Rightarrow> bool"
  where "monic_poly R f = 
    (f \<noteq> [] \<and> lead_coeff f = \<one>\<^bsub>R\<^esub> \<and> f \<in> carrier (poly_ring R))"

definition monic_irreducible_poly where
  "monic_irreducible_poly R f =
    (monic_poly R f \<and> pirreducible\<^bsub>R\<^esub> (carrier R) f)"

abbreviation "m_i_p \<equiv> monic_irreducible_poly"

locale polynomial_ring = field +
  fixes K
  assumes polynomial_ring_assms: "subfield K R"
begin

lemma K_subring: "subring K R"
  using polynomial_ring_assms subfieldE(1) by auto

abbreviation P where "P \<equiv> K[X]"

text \<open>This locale is used to specialize the following lemmas for a fixed coefficient ring.
It can be introduced in a context as an intepretation to be able to use the following specialized
lemmas. Because it is not (and should not) introduced as a sublocale it has no lasting effect
for the field locale itself.\<close> 

lemmas
    poly_mult_lead_coeff = poly_mult_lead_coeff[OF K_subring]
and degree_add_distinct = degree_add_distinct[OF K_subring]
and coeff_add = coeff_add[OF K_subring]
and var_closed = var_closed[OF K_subring]
and degree_prod = degree_prod[OF _ K_subring]
and degree_pow = degree_pow[OF K_subring]
and pirreducible_degree = pirreducible_degree[OF polynomial_ring_assms]
and degree_one_imp_pirreducible = 
    degree_one_imp_pirreducible[OF polynomial_ring_assms]
and var_pow_closed = var_pow_closed[OF K_subring]
and var_pow_carr = var_pow_carr[OF K_subring]
and univ_poly_a_inv_degree = univ_poly_a_inv_degree[OF K_subring]
and var_pow_degree = var_pow_degree[OF K_subring]
and pdivides_zero = pdivides_zero[OF K_subring]
and pdivides_imp_degree_le = pdivides_imp_degree_le[OF K_subring]
and var_carr = var_carr[OF K_subring]
and rupture_eq_0_iff = rupture_eq_0_iff[OF polynomial_ring_assms]
and rupture_is_field_iff_pirreducible =
    rupture_is_field_iff_pirreducible[OF polynomial_ring_assms]
and rupture_surj_hom = rupture_surj_hom[OF K_subring]
and canonical_embedding_ring_hom =
    canonical_embedding_ring_hom[OF K_subring]
and rupture_surj_norm_is_hom = rupture_surj_norm_is_hom[OF K_subring]
and rupture_surj_as_eval = rupture_surj_as_eval[OF K_subring]
and eval_cring_hom = eval_cring_hom[OF K_subring]
and coeff_range = coeff_range[OF K_subring]
and finite_poly = finite_poly[OF K_subring]
and int_embed_consistent_with_poly_of_const =
    int_embed_consistent_with_poly_of_const[OF K_subring]
and pderiv_var_pow = pderiv_var_pow[OF _ K_subring]
and pderiv_add = pderiv_add[OF K_subring]
and pderiv_inv = pderiv_inv[OF K_subring]
and pderiv_mult = pderiv_mult[OF K_subring]
and pderiv_pow = pderiv_pow[OF _ K_subring]
and pderiv_carr = pderiv_carr[OF K_subring]

sublocale p:principal_domain "poly_ring R"
  by (simp add: carrier_is_subfield univ_poly_is_principal)

end

context field
begin

interpretation polynomial_ring "R" "carrier R" 
  using carrier_is_subfield field_axioms
  by (simp add:polynomial_ring_def polynomial_ring_axioms_def)

lemma pdivides_mult_r: 
  assumes "a \<in> carrier (mult_of P)" 
  assumes "b \<in> carrier (mult_of P)" 
  assumes "c \<in> carrier (mult_of P)"
  shows "a \<otimes>\<^bsub>P\<^esub> c pdivides b \<otimes>\<^bsub>P\<^esub> c \<longleftrightarrow> a pdivides b" 
    (is "?lhs \<longleftrightarrow> ?rhs")
proof -
  have a:"b \<otimes>\<^bsub>P\<^esub> c \<in> carrier P - {\<zero>\<^bsub>P\<^esub>}"
    using assms p.mult_of.m_closed by force
  have b:"a \<otimes>\<^bsub>P\<^esub> c \<in> carrier P"
    using assms by simp
  have c:"b \<in> carrier P - {\<zero>\<^bsub>P\<^esub>}"
    using assms p.mult_of.m_closed by force
  have d:"a \<in> carrier P" using assms by simp
  have "?lhs \<longleftrightarrow> a \<otimes>\<^bsub>P\<^esub> c divides\<^bsub>mult_of P\<^esub> b \<otimes>\<^bsub>P\<^esub> c"
    unfolding pdivides_def using p.divides_imp_divides_mult a b
    by (meson divides_mult_imp_divides)
  also have "... \<longleftrightarrow> a divides\<^bsub>mult_of P\<^esub> b"
    using p.mult_of.divides_mult_r[OF assms] by simp
  also have "... \<longleftrightarrow> ?rhs"
    unfolding pdivides_def using p.divides_imp_divides_mult c d
    by (meson divides_mult_imp_divides)
  finally show ?thesis by simp
qed

lemma lead_coeff_carr:
  assumes "x \<in> carrier (mult_of P)"
  shows "lead_coeff x \<in> carrier R - {\<zero>}"
proof (cases x)
  case Nil
  then show ?thesis using assms by (simp add:univ_poly_zero)
next
  case (Cons a list)
  hence a: "polynomial (carrier R) (a # list)"
    using assms univ_poly_carrier by auto
  have "lead_coeff x = a"
    using Cons by simp
  also have "a \<in> carrier R - {\<zero>}"
    using lead_coeff_not_zero a by simp
  finally show ?thesis by simp
qed

lemma lead_coeff_poly_of_const:
  assumes "r \<noteq> \<zero>"
  shows "lead_coeff (poly_of_const r) = r"
  using assms
  by (simp add:poly_of_const_def)

lemma lead_coeff_mult:
  assumes "f \<in> carrier (mult_of P)"
  assumes "g \<in> carrier (mult_of P)"
  shows "lead_coeff (f \<otimes>\<^bsub>P\<^esub> g) = lead_coeff f \<otimes> lead_coeff g"
  unfolding univ_poly_mult using assms 
  using univ_poly_carrier[where R="R" and K="carrier R"]
  by (subst poly_mult_lead_coeff) (simp_all add:univ_poly_zero)

lemma monic_poly_carr:
  assumes "monic_poly R f"
  shows "f \<in> carrier P"
  using assms unfolding monic_poly_def by simp

lemma monic_poly_add_distinct: 
  assumes "monic_poly R f"
  assumes "g \<in> carrier P" "degree g < degree f"
  shows "monic_poly R (f \<oplus>\<^bsub>P\<^esub> g)"
proof (cases "g \<noteq> \<zero>\<^bsub>P\<^esub>")
  case True
  define n where "n = degree f"
  have "f \<in> carrier P - {\<zero>\<^bsub>P\<^esub>}"
    using assms(1) univ_poly_zero
    unfolding monic_poly_def by auto
  hence "degree (f \<oplus>\<^bsub>P\<^esub> g) = max (degree f) (degree g)"
    using assms(2,3) True
    by (subst degree_add_distinct, simp_all)
  also have "... = degree f"
    using assms(3) by simp
  finally have b: "degree (f \<oplus>\<^bsub>P\<^esub> g) = n"
    unfolding n_def by simp
  moreover have "n > 0"
    using assms(3) unfolding n_def by simp
  ultimately have "degree (f \<oplus>\<^bsub>P\<^esub> g) \<noteq> degree ([])"
    by simp
  hence a:"f \<oplus>\<^bsub>P\<^esub> g \<noteq> []" by auto

  have "degree [] = 0" by simp
  also have  "... < degree f"
    using assms(3) by simp
  finally have "degree f \<noteq> degree []" by simp
  hence c: "f \<noteq> []" by auto

  have d: "length g \<le> n" 
    using  assms(3) unfolding n_def by simp 

  have "lead_coeff (f \<oplus>\<^bsub>P\<^esub> g) = coeff (f \<oplus>\<^bsub>P\<^esub> g) n"
    using a b by (cases "f \<oplus>\<^bsub>P\<^esub> g", auto)
  also have "... = coeff f n \<oplus> coeff g n" 
    using monic_poly_carr assms
    by (subst coeff_add, auto) 
  also have "... = lead_coeff f \<oplus> coeff g n"
    using c unfolding n_def by (cases "f", auto)
  also have "... = \<one> \<oplus> \<zero>"
    using assms(1) unfolding monic_poly_def 
    unfolding subst coeff_length[OF d] by simp
  also have "... = \<one>"
    by simp
  finally have "lead_coeff (f \<oplus>\<^bsub>P\<^esub> g) = \<one>" by simp
  moreover have "f \<oplus>\<^bsub>P\<^esub> g \<in> carrier P"
    using monic_poly_carr assms by simp
  ultimately show  ?thesis
    using a  unfolding monic_poly_def by auto
next
  case False
  then show ?thesis using assms monic_poly_carr by simp
qed

lemma monic_poly_one: "monic_poly R \<one>\<^bsub>P\<^esub>"
proof -
  have "\<one>\<^bsub>P\<^esub> \<in> carrier P"
    by simp
  thus ?thesis
    by (simp add:univ_poly_one monic_poly_def)
qed

lemma monic_poly_var: "monic_poly R X"
proof -
  have "X \<in> carrier P"
    using var_closed by simp
  thus ?thesis
    by (simp add:var_def monic_poly_def)
qed

lemma monic_poly_carr_2:
  assumes "monic_poly R f"
  shows "f \<in> carrier (mult_of P)"
  using assms unfolding monic_poly_def
  by (simp add:univ_poly_zero)

lemma monic_poly_mult:
  assumes "monic_poly R f"
  assumes "monic_poly R g"
  shows "monic_poly R (f \<otimes>\<^bsub>P\<^esub> g)"
proof -
  have "lead_coeff (f \<otimes>\<^bsub>P\<^esub> g) = lead_coeff f \<otimes>\<^bsub>R\<^esub> lead_coeff g"
    using assms monic_poly_carr_2
    by (subst lead_coeff_mult) auto
  also have "... =  \<one>"
    using assms unfolding monic_poly_def by simp
  finally have "lead_coeff (f \<otimes>\<^bsub>P\<^esub> g) = \<one>\<^bsub>R\<^esub>" by simp
  moreover have "(f \<otimes>\<^bsub>P\<^esub> g) \<in> carrier (mult_of P)"
    using monic_poly_carr_2 assms by blast
  ultimately show ?thesis
    by (simp add:monic_poly_def univ_poly_zero)
qed

lemma monic_poly_pow:
  assumes "monic_poly R f"
  shows "monic_poly R (f [^]\<^bsub>P\<^esub> (n::nat))"
  using assms monic_poly_one monic_poly_mult
  by (induction n, auto)

lemma monic_poly_prod:
  assumes "finite A"
  assumes "\<And>x. x \<in> A \<Longrightarrow> monic_poly R (f x)"
  shows "monic_poly R (finprod P f A)"
  using assms 
proof (induction A rule:finite_induct)
  case empty
  then show ?case by (simp add:monic_poly_one)
next
  case (insert x F)
  have a: "f \<in> F \<rightarrow> carrier P" 
    using insert monic_poly_carr by simp
  have b: "f x \<in> carrier P" 
    using insert monic_poly_carr by simp
  have "monic_poly R (f x \<otimes>\<^bsub>P\<^esub> finprod P f F)"
    using insert by (intro monic_poly_mult) auto
  thus ?case
    using insert a b by (subst p.finprod_insert, auto)
qed

lemma monic_poly_not_assoc:
  assumes "monic_poly R f"
  assumes "monic_poly R g"
  assumes "f \<sim>\<^bsub>(mult_of P)\<^esub> g"
  shows "f = g"
proof -
  obtain u where u_def: "f = g \<otimes>\<^bsub>P\<^esub> u" "u \<in> Units (mult_of P)"
    using p.mult_of.associatedD2 assms monic_poly_carr_2
    by blast

  hence "u \<in> Units P" by simp
  then obtain v where v_def: "u = [v]" "v \<noteq> \<zero>\<^bsub>R\<^esub>" "v \<in> carrier R"
    using univ_poly_carrier_units by auto

  have "\<one> = lead_coeff f"
    using assms(1) by (simp add:monic_poly_def)
  also have  "... = lead_coeff (g \<otimes>\<^bsub>P\<^esub> u)"
    by (simp add:u_def)
  also have "... = lead_coeff g \<otimes> lead_coeff u"
    using assms(2) monic_poly_carr_2 v_def u_def(2)
    by (subst lead_coeff_mult, auto simp add:univ_poly_zero) 
  also have "... = lead_coeff g \<otimes> v"
    using v_def by simp
  also have "... = v"
    using assms(2) v_def(3) by (simp add:monic_poly_def)
  finally have "\<one> = v" by simp
  hence "u = \<one>\<^bsub>P\<^esub>" 
    using v_def by (simp add:univ_poly_one)
  thus "f = g"
    using u_def assms monic_poly_carr by simp
qed

lemma monic_poly_span:
  assumes "x \<in> carrier (mult_of P)" "irreducible (mult_of P) x"
  shows "\<exists>y. monic_irreducible_poly R y \<and> x \<sim>\<^bsub>(mult_of P)\<^esub> y"
proof -
  define z where "z = poly_of_const (inv (lead_coeff x))"
  define y where "y = x \<otimes>\<^bsub>P\<^esub> z"

  have x_carr: "x \<in> carrier (mult_of P)" using assms by simp

  hence lx_ne_0: "lead_coeff x \<noteq> \<zero>" 
    and lx_unit: "lead_coeff x \<in> Units R" 
    using lead_coeff_carr[OF x_carr] by (auto simp add:field_Units)
  have lx_inv_ne_0: "inv (lead_coeff x) \<noteq> \<zero>"  
    using lx_unit 
    by (metis Units_closed Units_r_inv r_null zero_not_one)
  have lx_inv_carr: "inv (lead_coeff x) \<in> carrier R" 
    using lx_unit by simp

  have "z \<in> carrier P"
    using lx_inv_carr poly_of_const_over_carrier
    unfolding z_def by auto
  moreover have "z \<noteq> \<zero>\<^bsub>P\<^esub>" 
    using lx_inv_ne_0
    by (simp add:z_def poly_of_const_def univ_poly_zero)
  ultimately have z_carr: "z \<in> carrier (mult_of P)" by simp
  have z_unit: "z \<in> Units (mult_of P)"
    using lx_inv_ne_0 lx_inv_carr
    by (simp add:univ_poly_carrier_units z_def poly_of_const_def)
  have y_exp: "y = x \<otimes>\<^bsub>(mult_of P)\<^esub> z" 
    by (simp add:y_def)
  hence y_carr: "y \<in> carrier (mult_of P)" 
    using x_carr z_carr p.mult_of.m_closed by simp

  have "irreducible (mult_of P) y"
    unfolding y_def using assms z_unit z_carr
    by (intro p.mult_of.irreducible_prod_rI, auto)
  moreover have "lead_coeff y = \<one>\<^bsub>R\<^esub>" 
    unfolding y_def using x_carr z_carr lx_inv_ne_0 lx_unit
    by (simp add: lead_coeff_mult z_def lead_coeff_poly_of_const)
  hence "monic_poly R y"
    using y_carr unfolding monic_poly_def
    by (simp add:univ_poly_zero) 
  ultimately have "monic_irreducible_poly R y"
    using p.irreducible_mult_imp_irreducible y_carr
    by (simp add:monic_irreducible_poly_def ring_irreducible_def)
  moreover have "y \<sim>\<^bsub>(mult_of P)\<^esub> x" 
    by (intro p.mult_of.associatedI2[OF z_unit] y_def x_carr)
  hence "x \<sim>\<^bsub>(mult_of P)\<^esub> y"
    using x_carr y_carr by (simp add:p.mult_of.associated_sym)
  ultimately show ?thesis by auto
qed

lemma monic_polys_are_canonical_irreducibles:
  "canonical_irreducibles (mult_of P) {d. monic_irreducible_poly R d}"
  (is "canonical_irreducibles (mult_of P) ?S")
proof -
  have sp_1: 
    "?S \<subseteq> {x \<in> carrier (mult_of P). irreducible (mult_of P) x}" 
    unfolding monic_irreducible_poly_def ring_irreducible_def
    using monic_poly_carr
    by (intro subsetI, simp add: p.irreducible_imp_irreducible_mult) 
  have sp_2: "x = y" 
      if "x \<in> ?S" "y \<in> ?S" "x \<sim>\<^bsub>(mult_of P)\<^esub> y" for x y 
    using that monic_poly_not_assoc
    by (simp add:monic_irreducible_poly_def)

  have sp_3: "\<exists>y \<in> ?S. x \<sim>\<^bsub>(mult_of P)\<^esub> y" 
    if "x \<in> carrier (mult_of P)" "irreducible (mult_of P) x" for x
    using that monic_poly_span by simp

  thus ?thesis using sp_1 sp_2 sp_3
    unfolding canonical_irreducibles_def by simp
qed

lemma
  assumes "monic_poly R a"
  shows factor_monic_poly: 
    "a = (\<Otimes>\<^bsub>P\<^esub>d\<in>{d. monic_irreducible_poly R d \<and> pmult d a > 0}. 
      d [^]\<^bsub>P\<^esub> pmult d a)" (is "?lhs = ?rhs")
    and factor_monic_poly_fin: 
      "finite {d. monic_irreducible_poly R d \<and> pmult d a > 0}" 
proof -
  let ?S = "{d. monic_irreducible_poly R d}"
  let ?T = "{d. monic_irreducible_poly R d \<and> pmult d a > 0}"
  let ?mip = "monic_irreducible_poly R"

  have sp_4: "a \<in> carrier (mult_of P)" 
    using assms monic_poly_carr_2
    unfolding monic_irreducible_poly_def by simp

  have b_1: "x \<in> carrier (mult_of P)" if "?mip x" for x 
    using that monic_poly_carr_2
    unfolding monic_irreducible_poly_def by simp
  have b_2:"irreducible (mult_of P) x" if "?mip x" for x
    using that
    unfolding monic_irreducible_poly_def ring_irreducible_def 
    by (simp add: monic_poly_carr p.irreducible_imp_irreducible_mult)
  have b_3:"x \<in> carrier P" if "?mip x" for x
    using that monic_poly_carr
    unfolding monic_irreducible_poly_def
    by simp

  have a_carr: "a \<in> carrier P - {\<zero>\<^bsub>P\<^esub>}" 
    using sp_4 by simp

  have "?T = {d. ?mip d \<and> multiplicity (mult_of P) d a > 0}" 
    by (simp add:pmult_def)
  also have "... = {d \<in> ?S. multiplicity (mult_of P) d a > 0}"
    using p.mult_of.multiplicity_gt_0_iff[OF b_1 b_2 sp_4]
    by (intro order_antisym subsetI, auto)
  finally have t:"?T = {d \<in> ?S. multiplicity (mult_of P) d a > 0}"
    by simp

  show fin_T: "finite ?T"
    unfolding t
    using p.mult_of.split_factors(1)
      [OF monic_polys_are_canonical_irreducibles]
    using sp_4 by auto

  have a:"x [^]\<^bsub>P\<^esub> (n::nat) \<in> carrier (mult_of P)" if "?mip x" for x n
  proof -
    have "monic_poly R (x [^]\<^bsub>P\<^esub> n)"
      using that monic_poly_pow 
      unfolding monic_irreducible_poly_def by auto
    thus ?thesis
      using monic_poly_carr_2 by simp
  qed

  have "?lhs \<sim>\<^bsub>(mult_of P)\<^esub> 
    finprod (mult_of P) 
      (\<lambda>d. d [^]\<^bsub>(mult_of P)\<^esub> (multiplicity (mult_of P) d a)) ?T"
    unfolding t 
    by (intro p.mult_of.split_factors(2)
        [OF monic_polys_are_canonical_irreducibles sp_4])
  also have "... = 
    finprod (mult_of P) (\<lambda>d. d [^]\<^bsub>P\<^esub> (multiplicity (mult_of P) d a)) ?T"
    by (simp add:nat_pow_mult_of)
  also have "... = ?rhs"
    using fin_T a
    by (subst p.finprod_mult_of, simp_all add:pmult_def) 
  finally have "?lhs \<sim>\<^bsub>(mult_of P)\<^esub> ?rhs" by simp
  moreover have "monic_poly R ?rhs" 
    using fin_T 
    by (intro monic_poly_prod monic_poly_pow)
      (auto simp:monic_irreducible_poly_def) 
  ultimately show "?lhs = ?rhs"
    using monic_poly_not_assoc assms monic_irreducible_poly_def
    by blast
qed

lemma degree_monic_poly':
  assumes "monic_poly R f"
  shows 
    "sum' (\<lambda>d. pmult d f * degree d) {d. monic_irreducible_poly R d} = 
    degree f" 
proof -
  let ?mip = "monic_irreducible_poly R"

  have b: "d \<in> carrier P - {\<zero>\<^bsub>P\<^esub>}" if "?mip d" for d 
    using that monic_poly_carr_2
    unfolding monic_irreducible_poly_def by simp
  have a: "d [^]\<^bsub>P\<^esub> n \<in> carrier P - {\<zero>\<^bsub>P\<^esub>}" if "?mip d" for d and n :: "nat"
    using b that monic_poly_pow
    unfolding monic_irreducible_poly_def 
    by (simp add: p.pow_non_zero)

  have "degree f = 
    degree (\<Otimes>\<^bsub>P\<^esub>d\<in>{d. ?mip d \<and> pmult d f > 0}. d [^]\<^bsub>P\<^esub> pmult d f)"
    using factor_monic_poly[OF assms(1)] by simp
  also have "... = 
    (\<Sum>i\<in>{d. ?mip d \<and> 0 < pmult d f}. degree (i [^]\<^bsub>P\<^esub> pmult i f))"
    using a assms(1)
    by (subst degree_prod[OF factor_monic_poly_fin])
     (simp_all add:Pi_def)
  also have "... = 
    (\<Sum>i\<in>{d. ?mip d \<and> 0 < pmult d f}. degree i * pmult i f)"
    using b degree_pow by (intro sum.cong, auto)
  also have "... = 
    (\<Sum>d\<in>{d. ?mip d \<and> 0 < pmult d f}. pmult d f * degree d)"
    by (simp add:mult.commute)
  also have "... = 
    sum' (\<lambda>d. pmult d f * degree d) {d. ?mip d \<and> 0 < pmult d f}"
    using sum.eq_sum factor_monic_poly_fin[OF assms(1)] by simp
  also have "... = sum' (\<lambda>d. pmult d f * degree d) {d. ?mip d}"
    by (intro sum.mono_neutral_cong_left' subsetI, auto)
  finally show ?thesis by simp
qed

lemma monic_poly_min_degree:
  assumes "monic_irreducible_poly R f"
  shows  "degree f \<ge> 1"
  using assms unfolding monic_irreducible_poly_def monic_poly_def
  by (intro pirreducible_degree) auto

lemma degree_one_monic_poly:
  "monic_irreducible_poly R f \<and> degree f = 1 \<longleftrightarrow> 
  (\<exists>x \<in> carrier R. f = [\<one>, \<ominus>x])"
proof 
  assume "monic_irreducible_poly R f \<and> degree f = 1"
  hence a:"monic_poly R f" "length f = 2"
    unfolding monic_irreducible_poly_def by auto
  then obtain u v where f_def: "f = [u,v]"
    by (cases f, simp, cases "tl f", auto)

  have "u = \<one>" using a unfolding monic_poly_def f_def by simp
  moreover have "v \<in> carrier R" 
    using a unfolding monic_poly_def univ_poly_carrier[symmetric]
    unfolding polynomial_def f_def by simp 
  ultimately have "f =  [\<one>, \<ominus>(\<ominus>v)]" "(\<ominus>v) \<in> carrier R"
    using a_inv_closed f_def by auto
  thus "(\<exists>x \<in> carrier R. f = [\<one>\<^bsub>R\<^esub>, \<ominus>\<^bsub>R\<^esub>x])" by auto
next
  assume "(\<exists>x \<in> carrier R. f = [\<one>, \<ominus>x])"
  then obtain x where f_def: "f = [\<one>,\<ominus>x]" "x \<in> carrier R" by auto
  have a:"degree f = 1" using f_def(2) unfolding f_def by simp
  have b:"f \<in> carrier P"
    using f_def(2) unfolding univ_poly_carrier[symmetric]
    unfolding f_def polynomial_def by simp
  have c: "pirreducible (carrier R) f"   
    by (intro degree_one_imp_pirreducible a b)
  have d: "lead_coeff f = \<one>" unfolding f_def by simp
  show "monic_irreducible_poly R f \<and> degree f = 1"
    using a b c d 
    unfolding monic_irreducible_poly_def monic_poly_def
    by auto
qed

lemma multiplicity_ge_iff:
  assumes "monic_irreducible_poly R d" 
  assumes "f \<in> carrier P - {\<zero>\<^bsub>P\<^esub>}"
  shows "pmult d f \<ge> k \<longleftrightarrow> d [^]\<^bsub>P\<^esub> k pdivides f"
proof -
  have a:"f \<in> carrier (mult_of P)" 
    using assms(2) by simp
  have b: "d \<in> carrier (mult_of P)" 
    using assms(1) monic_poly_carr_2
    unfolding monic_irreducible_poly_def by simp
  have c: "irreducible (mult_of P) d" 
    using assms(1) monic_poly_carr_2 
    using p.irreducible_imp_irreducible_mult
    unfolding monic_irreducible_poly_def 
    unfolding ring_irreducible_def monic_poly_def
    by simp
  have d: "d [^]\<^bsub>P\<^esub> k \<in> carrier P" using b by simp

  have "pmult d f \<ge> k \<longleftrightarrow> d [^]\<^bsub>(mult_of P)\<^esub> k divides\<^bsub>(mult_of P)\<^esub> f"
    unfolding pmult_def
    by (intro p.mult_of.multiplicity_ge_iff a b c)
  also have "... \<longleftrightarrow> d [^]\<^bsub>P\<^esub> k pdivides\<^bsub>R\<^esub> f"
    using p.divides_imp_divides_mult[OF d assms(2)]
    using divides_mult_imp_divides 
    unfolding pdivides_def nat_pow_mult_of
    by auto
  finally show ?thesis by simp
qed

lemma multiplicity_ge_1_iff_pdivides:
  assumes "monic_irreducible_poly R d" "f \<in> carrier P - {\<zero>\<^bsub>P\<^esub>}"
  shows "pmult d f \<ge> 1 \<longleftrightarrow> d pdivides f"
proof -
  have "d \<in> carrier P" 
    using assms(1) monic_poly_carr
    unfolding monic_irreducible_poly_def
    by simp
  thus ?thesis
    using multiplicity_ge_iff[OF assms, where k="1"]
    by simp
qed
  
lemma divides_monic_poly:
  assumes "monic_poly R f" "monic_poly R g"
  assumes "\<And>d. monic_irreducible_poly R d 
    \<Longrightarrow> pmult d f \<le> pmult d g" 
  shows "f pdivides g"
proof -
  have a:"f \<in> carrier (mult_of P)" "g \<in> carrier (mult_of P)" 
    using monic_poly_carr_2 assms(1,2) by auto

  have "f divides\<^bsub>(mult_of P)\<^esub> g"
    using assms(3) unfolding pmult_def 
    by (intro p.mult_of.divides_iff_mult_mono
        [OF a monic_polys_are_canonical_irreducibles]) simp
  thus ?thesis 
    unfolding pdivides_def using divides_mult_imp_divides by simp
qed

end

lemma monic_poly_hom:
  assumes "monic_poly R f"
  assumes "h \<in> ring_iso R S" "domain R" "domain S"
  shows "monic_poly S (map h f)"
proof -
  have c: "h \<in> ring_hom R S"
    using assms(2) ring_iso_def by auto
  have e: "f \<in> carrier (poly_ring R)" 
    using assms(1) unfolding monic_poly_def by simp

  have a:"f \<noteq> []"
    using assms(1) unfolding monic_poly_def by simp
  hence "map h f \<noteq> []" by simp
  moreover have "lead_coeff f = \<one>\<^bsub>R\<^esub>"
    using assms(1) unfolding monic_poly_def by simp
  hence "lead_coeff (map h f) = \<one>\<^bsub>S\<^esub>" 
    using ring_hom_one[OF c] by (simp add: hd_map[OF a])
  ultimately show ?thesis
    using carrier_hom[OF e assms(2-4)]
    unfolding monic_poly_def by simp
qed

lemma monic_irreducible_poly_hom:
  assumes "monic_irreducible_poly R f"
  assumes "h \<in> ring_iso R S" "domain R" "domain S"
  shows "monic_irreducible_poly S (map h f)"
proof -
  have a:
    "pirreducible\<^bsub>R\<^esub> (carrier R) f"
    "f \<in> carrier (poly_ring R)"
    "monic_poly R f"
    using assms(1)
    unfolding monic_poly_def monic_irreducible_poly_def
    by auto
 
  have "pirreducible\<^bsub>S\<^esub> (carrier S) (map h f)"
    using a pirreducible_hom assms by auto  
  moreover have "monic_poly S (map h f)"
    using a monic_poly_hom[OF _ assms(2,3,4)] by simp
  ultimately show ?thesis
    unfolding monic_irreducible_poly_def by simp
qed

end
