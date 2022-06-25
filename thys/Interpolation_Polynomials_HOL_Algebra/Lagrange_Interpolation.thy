section \<open>Lagrange Interpolation\<close>

text \<open>This section introduces the function @{term "interpolate"}, which constructs the Lagrange
interpolation polynomials for a given set of points, followed by a theorem of its correctness.\<close>

theory Lagrange_Interpolation
  imports "HOL-Algebra.Polynomial_Divisibility"
begin

text \<open>A finite product in a domain is $0$ if and only if at least one factor is. This could be added
to @{theory "HOL-Algebra.FiniteProduct"} or @{theory "HOL-Algebra.Ring"}.\<close>
lemma (in domain) finprod_zero_iff:
  assumes "finite A"
  assumes "\<And>a. a \<in> A \<Longrightarrow> f a \<in> carrier R"
  shows "finprod R f A = \<zero> \<longleftrightarrow> (\<exists>x \<in> A. f x = \<zero>)"
  using assms
proof (induct A rule: finite_induct)
  case empty
  then show ?case by simp
next
  case (insert y F)
  moreover have "f \<in> F \<rightarrow> carrier R" using insert by blast
  ultimately show ?case by (simp add:integral_iff)
qed

lemma (in ring) poly_of_const_in_carrier:
  assumes "s \<in> carrier R"
  shows "poly_of_const s \<in> carrier (poly_ring R)"
  using poly_of_const_def assms
  by (simp add:univ_poly_carrier[symmetric] polynomial_def)

lemma (in ring) eval_poly_of_const:
  assumes "x \<in> carrier R"
  shows "eval (poly_of_const x) y = x"
  using assms by (simp add:poly_of_const_def)

lemma (in ring) eval_in_carrier_2:
  assumes "x \<in> carrier (poly_ring R)"
  assumes "y \<in> carrier R"
  shows "eval x y \<in> carrier R"
  using eval_in_carrier univ_poly_carrier polynomial_incl assms by blast

lemma (in domain) poly_mult_degree_le_1:
  assumes "x \<in> carrier (poly_ring R)"
  assumes "y \<in> carrier (poly_ring R)"
  shows "degree (x \<otimes>\<^bsub>poly_ring R\<^esub> y) \<le> degree x + degree y"
proof -
  have "degree (x \<otimes>\<^bsub>poly_ring R\<^esub> y) = (if x = [] \<or> y = [] then 0 else degree x + degree y)"
    unfolding univ_poly_mult
    by (metis univ_poly_carrier assms(1,2) carrier_is_subring poly_mult_degree_eq)
  thus ?thesis by (metis nat_le_linear zero_le)
qed

lemma (in domain) poly_mult_degree_le:
  assumes "x \<in> carrier (poly_ring R)"
  assumes "y \<in> carrier (poly_ring R)"
  assumes "degree x \<le> n"
  assumes "degree y \<le> m"
  shows "degree (x \<otimes>\<^bsub>poly_ring R\<^esub> y) \<le> n + m"
  using poly_mult_degree_le_1 assms add_mono by force

lemma (in domain) poly_add_degree_le:
  assumes "x \<in> carrier (poly_ring R)" "degree x \<le> n"
  assumes "y \<in> carrier (poly_ring R)" "degree y \<le> n"
  shows "degree (x \<oplus>\<^bsub>poly_ring R\<^esub> y) \<le> n"
  using assms poly_add_degree
  by (metis dual_order.trans max.bounded_iff univ_poly_add)

lemma (in domain) poly_sub_degree_le:
  assumes "x \<in> carrier (poly_ring R)" "degree x \<le> n"
  assumes "y \<in> carrier (poly_ring R)" "degree y \<le> n"
  shows "degree (x \<ominus>\<^bsub>poly_ring R\<^esub> y) \<le> n"
proof -
  interpret x:cring "poly_ring R"
    using carrier_is_subring domain.univ_poly_is_cring domain_axioms by auto

  show ?thesis
    unfolding a_minus_def
    using assms univ_poly_a_inv_degree carrier_is_subring poly_add_degree_le x.a_inv_closed
    by simp
qed

lemma (in domain) poly_sum_degree_le:
  assumes "finite A"
  assumes "\<And>x. x \<in> A \<Longrightarrow> degree (f x) \<le> n"
  assumes "\<And>x. x \<in> A \<Longrightarrow> f x \<in> carrier (poly_ring R)"
  shows "degree (finsum (poly_ring R) f A) \<le> n"
  using assms
proof (induct A rule:finite_induct)
  case empty
  interpret x:cring "poly_ring R"
    using carrier_is_subring domain.univ_poly_is_cring domain_axioms by auto
  show ?case using empty by (simp add:univ_poly_zero)
next
  case (insert x F)
  interpret x:cring "poly_ring R"
    using carrier_is_subring domain.univ_poly_is_cring domain_axioms by auto
  have a: "degree (f x \<oplus>\<^bsub>poly_ring R\<^esub> finsum (poly_ring R) f F) \<le> n"
    using insert poly_add_degree_le x.finsum_closed by auto
  show ?case using insert a by auto
qed

definition (in ring) lagrange_basis_polynomial_aux where
  "lagrange_basis_polynomial_aux S =
    (\<Otimes>\<^bsub>poly_ring R\<^esub> s \<in> S. X \<ominus>\<^bsub>poly_ring R\<^esub> (poly_of_const s))"

lemma (in domain) lagrange_aux_eval:
  assumes "finite S"
  assumes "S \<subseteq> carrier R"
  assumes "x \<in> carrier R"
  shows "(eval (lagrange_basis_polynomial_aux S) x) = (\<Otimes>s \<in> S. x \<ominus> s)"
proof -
  interpret x:ring_hom_cring "poly_ring R" "R" "(\<lambda>p. eval p x)"
    by (rule eval_cring_hom[OF carrier_is_subring assms(3)])

  have "\<And>a. a \<in> S \<Longrightarrow> X \<ominus>\<^bsub>poly_ring R\<^esub> poly_of_const a \<in> carrier (poly_ring R)"
    by (meson poly_of_const_in_carrier carrier_is_subring assms(2) cring.cring_simprules(4)
        domain_def subsetD univ_poly_is_domain var_closed(1))

  moreover have "\<And>s. s \<in> S \<Longrightarrow> eval (X \<ominus>\<^bsub>poly_ring R\<^esub> poly_of_const s) x = x \<ominus> s"
    using assms var_closed carrier_is_subring poly_of_const_in_carrier subsetD[OF assms(2)]
    by (simp add:eval_var eval_poly_of_const)

  moreover have "a_minus R x \<in> S \<rightarrow> carrier R"
    using assms by blast

  ultimately show ?thesis
    by (simp add:lagrange_basis_polynomial_aux_def x.hom_finprod cong:finprod_cong')
qed

lemma (in domain) lagrange_aux_poly:
  assumes "finite S"
  assumes "S \<subseteq> carrier R"
  shows "lagrange_basis_polynomial_aux S \<in> carrier (poly_ring R)"
proof -
  have a:"subring (carrier R) R"
    using carrier_is_subring assms by blast

  have b: "\<And>a. a \<in> S \<Longrightarrow> X \<ominus>\<^bsub>poly_ring R\<^esub> poly_of_const a \<in> carrier (poly_ring R)"
    by (meson poly_of_const_in_carrier a assms(2) cring.cring_simprules(4) domain_def subsetD
        univ_poly_is_domain var_closed(1))

  interpret x:cring "poly_ring R"
    using carrier_is_subring domain.univ_poly_is_cring domain_axioms by auto

  show ?thesis
    using lagrange_basis_polynomial_aux_def b x.finprod_closed[OF Pi_I] by simp
qed

lemma (in domain) poly_prod_degree_le:
  assumes "finite A"
  assumes "\<And>x. x \<in> A \<Longrightarrow> f x \<in> carrier (poly_ring R)"
  shows "degree (finprod (poly_ring R) f A) \<le> (\<Sum>x \<in> A. degree (f x))"
  using assms
proof (induct A rule:finite_induct)
  case empty
  interpret x:cring "poly_ring R"
    using carrier_is_subring domain.univ_poly_is_cring domain_axioms by auto
  show ?case by (simp add:univ_poly_one)
next
  case (insert x F)
  interpret x:cring "poly_ring R"
    using carrier_is_subring domain.univ_poly_is_cring domain_axioms by auto
  have a:"f \<in> F \<rightarrow> carrier (poly_ring R)"
    using insert by blast
  have b:"f x \<in> carrier (poly_ring R)"
    using insert by blast
  have "degree (finprod (poly_ring R) f (insert x F)) = degree (f x \<otimes>\<^bsub>poly_ring R\<^esub> finprod (poly_ring R) f F)"
    using a b insert by simp
  also have "... \<le> degree (f x) + degree (finprod (poly_ring R) f F)"
    using poly_mult_degree_le x.finprod_closed[OF a] b by auto
  also have "... \<le> degree (f x) + (\<Sum>y \<in> F. degree (f y))"
    using insert(3) a add_mono by auto
  also have "... = (\<Sum>y \<in> (insert x F). degree (f y))" using insert by simp
  finally show ?case by simp
qed

lemma (in domain) lagrange_aux_degree:
  assumes "finite S"
  assumes "S \<subseteq> carrier R"
  shows "degree (lagrange_basis_polynomial_aux S) \<le> card S"
proof -
  interpret x:cring "poly_ring R"
    using carrier_is_subring domain.univ_poly_is_cring domain_axioms by auto

  have "degree X \<le> 1" by (simp add:var_def)
  moreover have "\<And>y. y\<in> S \<Longrightarrow> degree (poly_of_const y) \<le> 1" by (simp add:poly_of_const_def)
  ultimately have a: "\<And>y. y\<in> S \<Longrightarrow> degree (X \<ominus>\<^bsub>poly_ring R\<^esub> poly_of_const y) \<le> 1"
    by (meson assms(2) in_mono poly_of_const_in_carrier poly_sub_degree_le var_closed[OF carrier_is_subring])

  have b:"\<And>y. y \<in> S \<Longrightarrow> (X \<ominus>\<^bsub>poly_ring R\<^esub> poly_of_const y) \<in> carrier (poly_ring R)"
    by (meson subsetD x.minus_closed var_closed(1)[OF carrier_is_subring] poly_of_const_in_carrier assms(2))

  have "degree (lagrange_basis_polynomial_aux S) \<le> (\<Sum>y \<in> S. degree (X \<ominus>\<^bsub>poly_ring R\<^esub> poly_of_const y))"
    using lagrange_basis_polynomial_aux_def b poly_prod_degree_le[OF assms(1)] by auto
  also have "... \<le> (\<Sum>y \<in> S. 1)"
    using sum_mono a by force
  also have "... = card S" by simp
  finally show ?thesis by simp
qed

definition (in ring) lagrange_basis_polynomial where
  "lagrange_basis_polynomial S x = lagrange_basis_polynomial_aux S
    \<otimes>\<^bsub>poly_ring R\<^esub> (poly_of_const (inv\<^bsub>R\<^esub> (\<Otimes>s \<in> S. x \<ominus> s)))"

lemma (in field)
  assumes "finite S"
  assumes "S \<subseteq> carrier R"
  assumes "x \<in> carrier R - S"
  shows
    lagrange_one: "eval (lagrange_basis_polynomial S x) x = \<one>" and
    lagrange_degree: "degree (lagrange_basis_polynomial S x) \<le> card S" and
    lagrange_zero: "\<And>s. s \<in> S \<Longrightarrow> eval (lagrange_basis_polynomial S x) s = \<zero>" and
    lagrange_poly: "lagrange_basis_polynomial S x \<in> carrier (poly_ring R)"
proof -
  interpret x:ring_hom_cring "poly_ring R" "R" "(\<lambda>p. eval p x)"
    using assms carrier_is_subring eval_cring_hom by blast

  define p where "p = lagrange_basis_polynomial_aux S"
  have a:"eval p x = (\<Otimes>s \<in> S. x \<ominus> s)"
    using assms by (simp add:p_def lagrange_aux_eval)

  have b:"p \<in> carrier (poly_ring R)" using assms
    by (simp add:p_def lagrange_aux_poly)

  have "\<And>y. y \<in> S \<Longrightarrow> a_minus R x y \<in> carrier R"
    using assms by blast

  hence c:"finprod R (a_minus R x) S \<in> Units R"
    using finprod_closed[OF Pi_I] assms
    by (auto simp add:field_Units finprod_zero_iff)

  have "eval (lagrange_basis_polynomial S x) x =
    (\<Otimes>s \<in> S. x \<ominus> s) \<otimes> eval (poly_of_const (inv finprod R (a_minus R x) S)) x"
    using poly_of_const_in_carrier Units_inv_closed c p_def[symmetric]
    by (simp add: lagrange_basis_polynomial_def x.hom_mult[OF b] a)
  also have "... =  \<one>"
    using poly_of_const_in_carrier Units_inv_closed c eval_poly_of_const by simp
  finally show "eval (lagrange_basis_polynomial S x) x = \<one>" by simp

  have "degree (lagrange_basis_polynomial S x) \<le> degree p + degree (poly_of_const (inv finprod R (a_minus R x) S))"
    unfolding lagrange_basis_polynomial_def p_def[symmetric]
    using poly_mult_degree_le[OF b] poly_of_const_in_carrier Units_inv_closed c by auto
  also have "... \<le> card S + 0"
    using add_mono lagrange_aux_degree[OF assms(1) assms(2)] p_def poly_of_const_def by auto
  finally show "degree (lagrange_basis_polynomial S x) \<le> card S" by simp

  show "\<And>s. s \<in> S \<Longrightarrow> eval (lagrange_basis_polynomial S x) s = \<zero>"
  proof -
    fix s
    assume d:"s \<in> S"

    interpret s:ring_hom_cring "poly_ring R" "R" "(\<lambda>p. eval p s)"
      using eval_cring_hom carrier_is_subring assms d by blast

    have "eval p s = finprod R (a_minus R s) S"
      using subsetD[OF assms(2) d] assms
      by (simp add:p_def lagrange_aux_eval)
    also have "... = \<zero>"
      using subsetD[OF assms(2)] d assms by (simp add: finprod_zero_iff)
    finally have "eval p s = \<zero>\<^bsub>R\<^esub>" by simp

    moreover have "eval (poly_of_const (inv finprod R (a_minus R x) S)) s \<in> carrier R"
      using s.hom_closed poly_of_const_in_carrier  Units_inv_closed c by blast

    ultimately show "eval (lagrange_basis_polynomial S x) s = \<zero>"
      using poly_of_const_in_carrier Units_inv_closed c
      by (simp add:lagrange_basis_polynomial_def Let_def p_def[symmetric] s.hom_mult[OF b])
  qed

  interpret r:cring "poly_ring R"
    using carrier_is_subring domain.univ_poly_is_cring domain_axioms by auto

  show "lagrange_basis_polynomial S x \<in> carrier (poly_ring R)"
    using lagrange_basis_polynomial_def p_def[symmetric] poly_of_const_in_carrier Units_inv_closed
      a b c by simp
qed

definition (in ring) interpolate where
  "interpolate S f =
   (\<Oplus>\<^bsub>poly_ring R\<^esub>s \<in> S. lagrange_basis_polynomial (S - {s}) s \<otimes>\<^bsub>poly_ring R\<^esub> (poly_of_const (f s)))"

text \<open>Let @{term "f"} be a function and @{term "S"} be a finite subset of the domain of the field.
Then @{term "interpolate S f"} will return a polynomial with degree less than @{term "card S"}
interpolating @{term "f"} on @{term "S"}.\<close>

theorem (in field)
  assumes "finite S"
  assumes "S \<subseteq> carrier R"
  assumes "f ` S \<subseteq> carrier R"
  shows
    interpolate_poly: "interpolate S f \<in> carrier (poly_ring R)" and
    interpolate_degree: "degree (interpolate S f) \<le> card S - 1" and
    interpolate_eval: "\<And>s. s \<in> S \<Longrightarrow> eval (interpolate S f) s = f s"
proof -
  interpret r:cring "poly_ring R"
    using carrier_is_subring domain.univ_poly_is_cring domain_axioms by auto

  have a:"\<And>x. x \<in> S \<Longrightarrow> lagrange_basis_polynomial (S - {x}) x \<in> carrier (poly_ring R)"
    by (meson lagrange_poly assms Diff_iff finite_Diff in_mono insertI1 subset_insertI2 subset_insert_iff)

  have b:"\<And>x. x \<in> S \<Longrightarrow> f x \<in> carrier R" using assms by blast

  have c:"\<And>x. x \<in> S \<Longrightarrow> degree (lagrange_basis_polynomial (S - {x}) x) \<le> card S - 1"
    by (metis (full_types) lagrange_degree  DiffI Diff_insert_absorb assms(1) assms(2)
        card_Diff_singleton finite_insert insert_subset mk_disjoint_insert)

  have d: "\<And>x. x \<in> S \<Longrightarrow>
    degree (lagrange_basis_polynomial (S - {x}) x \<otimes>\<^bsub>poly_ring R\<^esub> poly_of_const (f x)) \<le> (card S - 1) + 0"
    using poly_of_const_in_carrier[OF b] poly_mult_degree_le[OF a] c poly_of_const_def by fastforce

  show "interpolate S f \<in> carrier (poly_ring R)"
    using interpolate_def poly_of_const_in_carrier a b by simp

  show "degree (interpolate S f) \<le> card S - 1"
    using poly_sum_degree_le[OF assms(1) d] poly_of_const_in_carrier[OF b] interpolate_def a by simp

  have e:"subring (carrier R) R"
    using carrier_is_subring assms by blast

  show "\<And>s. s \<in> S \<Longrightarrow> eval (interpolate S f) s = f s"
  proof -
    fix s
    assume f:"s \<in> S"
    interpret s:ring_hom_cring "poly_ring R" "R" "(\<lambda>p. eval p s)"
      using eval_cring_hom[OF e] assms f by blast
    have g:"\<And>i. i \<in> S \<Longrightarrow>
         eval (lagrange_basis_polynomial (S - {i}) i \<otimes>\<^bsub>poly_ring R\<^esub> poly_of_const (f i)) s =
         (if s = i then f s else \<zero>)"
    proof -
      fix i
      assume i_in_S: "i \<in> S"
      have "eval (lagrange_basis_polynomial (S - {i}) i \<otimes>\<^bsub>poly_ring R\<^esub> poly_of_const (f i)) s =
        eval (lagrange_basis_polynomial (S - {i}) i) s \<otimes> f i"
        using b i_in_S poly_of_const_in_carrier
        by (simp add: s.hom_mult[OF a] eval_poly_of_const)
      also have "... = (if s = i then f s else \<zero>)"
        using b i_in_S poly_of_const_in_carrier assms f
        apply (cases "s=i", simp, subst lagrange_one, auto)
        by (subst lagrange_zero, auto)
      finally show
        "eval (lagrange_basis_polynomial (S - {i}) i \<otimes>\<^bsub>poly_ring R\<^esub> poly_of_const (f i)) s =
         (if s = i then f s else \<zero>)" by simp
    qed

    have "eval (interpolate S f) s =
    (\<Oplus>x\<in>S. eval (lagrange_basis_polynomial (S - {x}) x \<otimes>\<^bsub>poly_ring R\<^esub> poly_of_const (f x)) s)"
      using  poly_of_const_in_carrier[OF b] a e
      by (simp add: interpolate_def s.hom_finsum[OF Pi_I] comp_def)
    also have "... =  (\<Oplus>x\<in>S. if s = x then f s else \<zero>)"
      using b g by (simp cong: finsum_cong)
    also have "... = f s"
      using finsum_singleton[OF f assms(1)] f assms by auto
    finally show "eval (interpolate S f) s = f s" by simp
  qed
qed

end