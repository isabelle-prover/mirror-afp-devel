(* Author: Alexander Bentkamp, Universität des Saarlandes
*)
theory PP_Univariate
imports PP_MPoly PP_More_MPoly "HOL-Computational_Algebra.Polynomial"
begin

text \<open>This file connects univariate MPolys to the theory of univariate polynomials from
  @{file "~~/src/HOL/Computational_Algebra/Polynomial.thy"}.\<close>

definition poly_to_mpoly::"nat \<Rightarrow> 'a::comm_monoid_add poly \<Rightarrow> 'a mpoly"
where "poly_to_mpoly v p = MPoly (Abs_poly_mapping (\<lambda>m. (coeff p (PP_Poly_Mapping.lookup m v)) when PP_Poly_Mapping.keys m \<subseteq> {v}))"

lemma poly_to_mpoly_finite: "finite {m::nat \<Rightarrow>\<^sub>0 nat. (coeff p (PP_Poly_Mapping.lookup m v) when PP_Poly_Mapping.keys m \<subseteq> {v}) \<noteq> 0}" (is "finite ?M")
proof -
  have "?M \<subseteq> PP_Poly_Mapping.single v ` {x. Polynomial.coeff p x \<noteq> 0}"
  proof
    fix m assume "m \<in> ?M"
    then have "\<And>v'. v'\<noteq>v \<Longrightarrow> PP_Poly_Mapping.lookup m v' = 0" by fastforce
    then have "m = PP_Poly_Mapping.single v (PP_Poly_Mapping.lookup m v)"
      using PP_Poly_Mapping.poly_mapping_eqI by (metis (full_types) lookup_single_eq lookup_single_not_eq)
    then show "m \<in> (PP_Poly_Mapping.single v) ` {x. Polynomial.coeff p x \<noteq> 0}" using \<open>m \<in> ?M\<close> by auto
  qed
  then show ?thesis using finite_surj[OF MOST_coeff_eq_0[unfolded eventually_cofinite]] by blast
qed

lemma coeff_poly_to_mpoly: "PP_MPoly.coeff (poly_to_mpoly v p) (PP_Poly_Mapping.single v k) = Polynomial.coeff p k"
  unfolding poly_to_mpoly_def coeff_def MPoly_inverse[OF Set.UNIV_I] lookup_Abs_poly_mapping[OF poly_to_mpoly_finite]
  using empty_subsetI keys_single lookup_single order_refl when_simps(1) by simp

definition mpoly_to_poly::"nat \<Rightarrow> 'a::comm_monoid_add mpoly \<Rightarrow> 'a poly"
where "mpoly_to_poly v p = Abs_poly (\<lambda>k. PP_MPoly.coeff p (PP_Poly_Mapping.single v k))"

lemma coeff_mpoly_to_poly[simp]: "Polynomial.coeff (mpoly_to_poly v p) k = PP_MPoly.coeff p (PP_Poly_Mapping.single v k)"
proof -
  have 0:"PP_Poly_Mapping.single v ` {x. PP_Poly_Mapping.lookup (mapping_of p) (PP_Poly_Mapping.single v x) \<noteq> 0}
          \<subseteq> {k. PP_Poly_Mapping.lookup (mapping_of p) k \<noteq> 0}"
    by auto
  have "\<forall>\<^sub>\<infinity> k. PP_MPoly.coeff p (PP_Poly_Mapping.single v k) = 0" unfolding coeff_def eventually_cofinite
    using  finite_imageD[OF finite_subset[OF 0 PP_Poly_Mapping.finite_lookup]] inj_single by (metis inj_eq inj_onI)
  then show ?thesis
    unfolding mpoly_to_poly_def by (simp add: Abs_poly_inverse)
qed

lemma mpoly_to_poly_inverse:
assumes "vars p \<subseteq> {v}"
shows "poly_to_mpoly v (mpoly_to_poly v p) = p"
proof -
  def f == "(\<lambda>m. Polynomial.coeff (mpoly_to_poly v p) (PP_Poly_Mapping.lookup m v) when PP_Poly_Mapping.keys m \<subseteq> {v})"
  have "finite {m. f m \<noteq> 0}" unfolding f_def using poly_to_mpoly_finite by blast
  have "Abs_poly_mapping f = mapping_of p"
  proof (rule "PP_Poly_Mapping.poly_mapping_eqI")
    fix m
    show "PP_Poly_Mapping.lookup (Abs_poly_mapping f) m = PP_Poly_Mapping.lookup (mapping_of p) m"
    proof (cases "PP_Poly_Mapping.keys m \<subseteq> {v}")
      assume "PP_Poly_Mapping.keys m \<subseteq> {v}"
      then show ?thesis unfolding "PP_Poly_Mapping.lookup_Abs_poly_mapping"[OF `finite {m. f m \<noteq> 0}`] unfolding f_def
        unfolding coeff_mpoly_to_poly coeff_def using when_simps(1) apply simp
        using keys_single lookup_not_eq_zero_eq_in_keys lookup_single_eq
        lookup_single_not_eq poly_mapping_eqI subset_singletonD
        by (metis (no_types, lifting) aux lookup_eq_zero_in_keys_contradict)
    next
      assume "\<not>PP_Poly_Mapping.keys m \<subseteq> {v}"
      then show ?thesis unfolding "PP_Poly_Mapping.lookup_Abs_poly_mapping"[OF `finite {m. f m \<noteq> 0}`] unfolding f_def
        using `vars p \<subseteq> {v}` unfolding vars_def by (metis (no_types, lifting) UN_I lookup_not_eq_zero_eq_in_keys subsetCE subsetI when_def)
    qed
  qed
  then show ?thesis
    unfolding poly_to_mpoly_def f_def  by (simp add: mapping_of_inverse)
qed

lemma poly_to_mpoly_inverse: "mpoly_to_poly v (poly_to_mpoly v p) = p"
  unfolding mpoly_to_poly_def coeff_poly_to_mpoly by (simp add: coeff_inverse)

lemma poly_to_mpoly0: "poly_to_mpoly v 0 = 0"
proof -
  have "\<And>m. (Polynomial.coeff 0 (PP_Poly_Mapping.lookup m v) when PP_Poly_Mapping.keys m \<subseteq> {v}) = 0" by simp
  have "Abs_poly_mapping (\<lambda>m. Polynomial.coeff 0 (PP_Poly_Mapping.lookup m v) when PP_Poly_Mapping.keys m \<subseteq> {v}) = 0"
    apply (rule PP_Poly_Mapping.poly_mapping_eqI) unfolding lookup_Abs_poly_mapping[OF poly_to_mpoly_finite] by auto
  then show ?thesis using poly_to_mpoly_def zero_mpoly.abs_eq by (metis (no_types))
qed

lemma mpoly_to_poly_add: "mpoly_to_poly v (p1 + p2) = mpoly_to_poly v p1 + mpoly_to_poly v p2"
  unfolding  Polynomial.plus_poly.abs_eq PP_More_MPoly.coeff_add coeff_mpoly_to_poly
  using mpoly_to_poly_def by auto

lemma poly_eq_insertion:
assumes "vars p \<subseteq> {v}"
shows "poly (mpoly_to_poly v p) x = insertion (\<lambda>v. x) p"
using assms proof (induction p rule:mpoly_induct)
  case (monom m a)
  then show ?case
  proof (cases "a=0")
    case True
    then show ?thesis
      by (metis PP_MPoly.monom.abs_eq insertion_zero monom_zero poly_0 poly_to_mpoly0 poly_to_mpoly_inverse single_zero)
  next
    case False
    then have "PP_Poly_Mapping.keys m \<subseteq> {v}" using monom unfolding vars_def PP_MPoly.mapping_of_monom keys_single by simp
    then have "\<And>v'. v'\<noteq>v \<Longrightarrow> PP_Poly_Mapping.lookup m v' = 0" unfolding vars_def by auto
    then have "m = PP_Poly_Mapping.single v (PP_Poly_Mapping.lookup m v)"
      by (metis lookup_single_eq lookup_single_not_eq poly_mapping_eqI)
    then have 0:"insertion (\<lambda>v. x) (PP_MPoly.monom m a) = a * x ^ (PP_Poly_Mapping.lookup m v)"
      using insertion_single by metis
    have "\<And>k. PP_Poly_Mapping.single v k = m \<longleftrightarrow> PP_Poly_Mapping.lookup m v = k"
      using \<open>m = PP_Poly_Mapping.single v (PP_Poly_Mapping.lookup m v)\<close> by auto
    then have "monom a (PP_Poly_Mapping.lookup m v) = (Abs_poly (\<lambda>k. if PP_Poly_Mapping.single v k = m then a else 0))"
      by (simp add: Polynomial.monom.abs_eq)
    then show ?thesis unfolding mpoly_to_poly_def PP_More_MPoly.coeff_monom 0 when_def by (metis poly_monom)
  qed
next
  case (sum p1 p2 m a)
  then have "poly (mpoly_to_poly v p1) x = insertion (\<lambda>v. x) p1"
            "poly (mpoly_to_poly v p2) x = insertion (\<lambda>v. x) p2"
    by (simp_all add: vars_add_monom)
  then show ?case unfolding insertion_add mpoly_to_poly_add by simp
qed

text \<open>Using the new connection between MPoly and univariate polynomials, we can transfer:\<close>

lemma univariate_mpoly_roots_finite:
fixes p::"'a::idom mpoly"
assumes "vars p \<subseteq> {v}" "p \<noteq> 0"
shows "finite {x. insertion (\<lambda>v. x) p = 0}"
using poly_roots_finite[of "mpoly_to_poly v p", unfolded poly_eq_insertion[OF `vars p \<subseteq> {v}`]]
using assms(1) assms(2) mpoly_to_poly_inverse poly_to_mpoly0 by fastforce

end
