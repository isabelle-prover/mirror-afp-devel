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
  have a: "f \<in> F \<rightarrow> carrier R" using insert by blast
  have b:"finprod R f F \<in> carrier R" by (rule finprod_closed[OF a])
  have c:"f y \<in> carrier R" using insert by blast
  have d:"(\<And>a. a \<in> F \<Longrightarrow> f a \<in> carrier R)" using a by blast

  show ?case
    apply (subst comm_monoid.finprod_insert[OF comm_monoid_axioms insert(1) insert(2) a c])  
    apply (subst integral_iff[OF c b])
    apply (subst insert(3)[OF d], simp)
    by blast
qed

lemma (in ring) poly_of_const_in_carrier:
  assumes "s \<in> carrier R"
  shows "poly_of_const s \<in> carrier (poly_ring R)"
  apply (cases "s = \<zero>")
  apply (simp add:poly_of_const_def univ_poly_zero_closed)
  by (simp add:poly_of_const_def univ_poly_carrier[symmetric] polynomial_def assms)

lemma (in ring) eval_poly_of_const:
  assumes "x \<in> carrier R"
  shows "eval (poly_of_const x) y = x"
  using assms by (simp add:poly_of_const_def)

lemma (in domain) poly_mult_degree_le:
  assumes "x \<in> carrier (poly_ring R)"
  assumes "y \<in> carrier (poly_ring R)"
  assumes "degree x \<le> n"
  assumes "degree y \<le> m"
  shows "degree (x \<otimes>\<^bsub>poly_ring R\<^esub> y) \<le> n + m"
proof -
  have a: "polynomial\<^bsub>R\<^esub> (carrier R) x" using assms 
    by (meson univ_poly_carrier)
  have b: "polynomial\<^bsub>R\<^esub> (carrier R) y" using assms 
    by (meson univ_poly_carrier)
  have c: "subring (carrier R) R" by (simp add: carrier_is_subring)
  have "degree (ring.poly_mult R x y) = (if x = [] \<or> y = [] then 0 else degree x + degree y)"
    using a b c poly_mult_degree_eq by blast
  hence "degree (x \<otimes>\<^bsub>poly_ring R\<^esub> y) = (if x = [] \<or> y = [] then 0 else degree x + degree y)"
    by (simp add: univ_poly_mult)
  thus ?thesis using assms 
    by (metis add_mono_thms_linordered_semiring(1) zero_le)   
qed

lemma (in domain) poly_add_degree_le:
  assumes "x \<in> carrier (poly_ring R)" "degree x \<le> n"
  assumes "y \<in> carrier (poly_ring R)" "degree y \<le> n"
  shows "degree (x \<oplus>\<^bsub>poly_ring R\<^esub> y) \<le> n"
proof -
  have "degree (x \<oplus>\<^bsub>poly_ring R\<^esub> y) \<le> n" using assms poly_add_degree 
    by (metis dual_order.trans max.bounded_iff univ_poly_add)
  then show ?thesis using assms by linarith
qed

lemma (in domain) poly_sub_degree_le:
  assumes "x \<in> carrier (poly_ring R)" "degree x \<le> n"
  assumes "y \<in> carrier (poly_ring R)" "degree y \<le> n"
  shows "degree (x \<ominus>\<^bsub>poly_ring R\<^esub> y) \<le> n"
proof -
  interpret x:cring "poly_ring R" 
    using carrier_is_subring domain.univ_poly_is_cring domain_axioms by auto

  show ?thesis
    apply (subst a_minus_def)
    apply (rule poly_add_degree_le[OF assms(1) assms(2)])
     apply (rule x.a_inv_closed[OF assms(3)])
    apply (subst univ_poly_a_inv_degree[OF carrier_is_subring assms(3)])
    by (rule assms(4)) 
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
    apply (rule poly_add_degree_le)
    using insert  x.finsum_closed by auto
  show ?case
    apply (subst x.finsum_insert[OF insert(1) insert(2)])
    using insert a by auto
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

  have a: "\<And>a. a \<in> S \<Longrightarrow> X \<ominus>\<^bsub>poly_ring R\<^esub> poly_of_const a \<in> carrier (poly_ring R)"
    by (meson poly_of_const_in_carrier carrier_is_subring assms(2) cring.cring_simprules(4) 
        domain_def subsetD univ_poly_is_domain var_closed(1))

  have b:"\<And>s. s \<in> S \<Longrightarrow> eval (X \<ominus>\<^bsub>poly_ring R\<^esub> poly_of_const s) x = x \<ominus> s"
    apply (subst x.hom_sub, rule var_closed(1)[OF carrier_is_subring])
     apply (rule poly_of_const_in_carrier, rule subsetD[OF assms(2)], simp)
    apply (subst eval_var[OF assms(3)])
    apply (subst eval_poly_of_const, metis subsetD[OF assms(2)])
    by simp

  have c:"a_minus R x \<in> S \<rightarrow> carrier R"
    using assms by blast

  show ?thesis
    apply (simp add:lagrange_basis_polynomial_aux_def)
    apply (subst x.hom_finprod, rule Pi_I, erule a)
    apply (rule finprod_cong', simp, simp add:c)
    by (simp add:b)
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
    apply (simp add:lagrange_basis_polynomial_aux_def)
    apply (rule x.finprod_closed)
    by (rule Pi_I, rule b, simp)
qed

lemma (in domain) lagrange_aux_degree:
  assumes "finite S"
  assumes "S \<subseteq> carrier R"
  shows "degree (lagrange_basis_polynomial_aux S) \<le> card S"
  using assms
proof (induct S rule: finite_induct)
  case empty
  interpret x:cring "poly_ring R" 
    using carrier_is_subring domain.univ_poly_is_cring domain_axioms by auto
  show ?case using empty by (simp add:lagrange_basis_polynomial_aux_def univ_poly_one)
next
  case (insert x F)
  interpret x:cring "poly_ring R" 
    using carrier_is_subring domain.univ_poly_is_cring domain_axioms by auto
  have a:"subring (carrier R) R"  
    using carrier_is_subring assms by blast

  have b: "\<And>a. a \<in> carrier R \<Longrightarrow> X \<ominus>\<^bsub>poly_ring R\<^esub> poly_of_const a \<in> carrier (poly_ring R)"
    by (meson poly_of_const_in_carrier a cring.cring_simprules(4) domain_def subsetD
        univ_poly_is_domain var_closed(1))

  have c:"F \<subseteq> carrier R" using insert by blast
  have d:"x \<in> carrier R" using insert by blast
  have e: "degree (X \<ominus>\<^bsub>poly_ring R\<^esub> poly_of_const x) \<le> 1"
    apply (rule poly_sub_degree_le, rule var_closed(1)[OF a])
    apply (simp add:var_def)
    using d poly_of_const_in_carrier apply blast
    by (simp add:poly_of_const_def)

  have "degree (lagrange_basis_polynomial_aux (insert x F)) \<le> 
    1 + card F"
    apply (subst lagrange_basis_polynomial_aux_def)
    apply (subst x.finprod_insert[OF insert(1) insert(2)])
      apply (rule Pi_I, rule b, metis subsetD[OF c])
     apply (rule b, rule d)
    apply (rule poly_mult_degree_le[OF b[OF d]])
      apply (rule x.finprod_closed, rule Pi_I, rule b, metis subsetD[OF c])
     apply (rule e)
    using insert(3)[OF c] lagrange_basis_polynomial_aux_def by simp
  also have "... \<le> card (insert x F)" using insert by simp
  finally show ?case by simp 
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
  have a:"subring (carrier R) R"  
    using carrier_is_subring assms by blast

  interpret x:ring_hom_cring "poly_ring R" "R" "(\<lambda>p. eval p x)"
    apply (rule eval_cring_hom[OF a]) using assms by blast

  define p where "p = lagrange_basis_polynomial_aux S"
  have b:"p \<in> carrier (poly_ring R)"
    apply (simp add:p_def)
    by (rule lagrange_aux_poly[OF assms(1) assms(2)])

  have c:"eval p x = (\<Otimes>s \<in> S. x \<ominus> s)"
    apply (simp add:p_def)
    apply (subst lagrange_aux_eval[OF assms(1) assms(2)])
    using assms(3) by auto

  have d:"a_minus R x \<in> S \<rightarrow> carrier R"
    using assms by blast

  have e:"finprod R (a_minus R x) S \<in> Units R"
    apply (simp add:field_Units)
    apply (rule conjI, rule finprod_closed[OF d])
    apply (subst finprod_zero_iff[OF assms(1)])
    using assms by auto

  show "eval (lagrange_basis_polynomial S x) x = \<one>"
    apply (simp add:lagrange_basis_polynomial_def Let_def p_def[symmetric])
    apply (subst x.hom_mult[OF b])
     apply (rule poly_of_const_in_carrier)
     apply (rule Units_inv_closed, rule e)
    apply (simp add:c)
    apply (subst eval_poly_of_const, rule Units_inv_closed[OF e])
    using e Units_r_inv by blast

  show "degree (lagrange_basis_polynomial S x) \<le> card S"
    apply (simp add:lagrange_basis_polynomial_def Let_def p_def[symmetric])
    apply (rule poly_mult_degree_le[where m="0",simplified], rule b)
      apply (rule poly_of_const_in_carrier, rule Units_inv_closed, rule e)
     apply (simp add:p_def lagrange_aux_degree[OF assms(1) assms(2), simplified])
    by (simp add:poly_of_const_def)

  show "\<And>s. s \<in> S \<Longrightarrow> eval (lagrange_basis_polynomial S x) s = \<zero>"
  proof -
    fix s
    assume f:"s \<in> S"
    have g:"eval p s = \<zero>\<^bsub>R\<^esub>"
      apply (simp add:p_def)
      apply (subst lagrange_aux_eval[OF assms(1) assms(2)])
      apply (meson in_mono f assms)
      apply (subst finprod_zero_iff[OF assms(1)])
      using assms f apply blast
      by (meson assms f in_mono r_right_minus_eq)

    interpret s:ring_hom_cring "poly_ring R" "R" "(\<lambda>p. eval p s)"
      apply (rule eval_cring_hom[OF a]) using assms f by blast
    have h:"eval (poly_of_const (inv finprod R (a_minus R x) S)) s \<in> carrier R"
      apply (rule s.hom_closed, rule poly_of_const_in_carrier)
      by (rule Units_inv_closed,  rule e)

    show "eval (lagrange_basis_polynomial S x) s = \<zero>"
      apply (simp add:lagrange_basis_polynomial_def Let_def p_def[symmetric])
      apply (subst s.hom_mult[OF b])
       apply (rule poly_of_const_in_carrier)
       apply (rule Units_inv_closed, rule e)
      by (simp add:g h)
  qed

  interpret r:cring "poly_ring R"
    using carrier_is_subring domain.univ_poly_is_cring domain_axioms by auto

  show "lagrange_basis_polynomial S x \<in> carrier (poly_ring R)"
    apply (simp add:lagrange_basis_polynomial_def Let_def p_def[symmetric])
    using poly_of_const_in_carrier[OF Units_inv_closed] c e b
    by simp
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

  show "interpolate S f \<in> carrier (poly_ring R)"
    apply (simp add:interpolate_def)
    apply (rule r.finsum_closed)
    apply (rule Pi_I)
    using poly_of_const_in_carrier[OF b] a by simp

  show "degree (interpolate S f) \<le> card S - 1"
    apply (subst interpolate_def)
    apply (rule poly_sum_degree_le[OF assms(1)])
     apply (rule order_trans[where y="(card S - 1) + 0"])
      apply (rule poly_mult_degree_le[OF a], simp, rule poly_of_const_in_carrier[OF b], simp, rule c, simp)
      apply (simp add:poly_of_const_def)
     apply simp
    using poly_of_const_in_carrier[OF b] a by simp

  have e:"subring (carrier R) R"
    using carrier_is_subring assms by blast

  show "\<And>s. s \<in> S \<Longrightarrow> eval (interpolate S f) s = f s"
  proof -
    fix s
    assume d:"s \<in> S"
    interpret s:ring_hom_cring "poly_ring R" "R" "(\<lambda>p. eval p s)"
      apply (rule eval_cring_hom[OF e]) using assms d by blast
    have e:"\<And>i. i \<in> S \<Longrightarrow>
         eval (lagrange_basis_polynomial (S - {i}) i \<otimes>\<^bsub>poly_ring R\<^esub> poly_of_const (f i)) s =
         (if s = i then f s else \<zero>)"
      apply (subst s.hom_mult[OF a], simp, rule poly_of_const_in_carrier, rule b, simp)
      apply (simp add:eval_poly_of_const b)
      apply (rule conjI, rule impI, subst lagrange_one, simp add:assms)
         using assms apply blast
        using assms apply blast
       apply (simp add:b)
      apply (rule impI, subst lagrange_zero, simp add:assms)
      using assms d by auto

    have "eval (interpolate S f) s = (\<Oplus>x\<in>S. if s = x then f s else \<zero>)"
      apply (subst interpolate_def)
      apply (subst s.hom_finsum, simp add:Pi_def poly_of_const_in_carrier[OF b] a)
      apply (simp add:comp_def)
      apply (rule finsum_cong', simp, simp add:Pi_def b)
      by (rule e, simp)
    also have "... = f s"
      apply (rule finsum_singleton[OF d assms(1)])
      using d assms by blast
    finally show "eval (interpolate S f) s = f s" by simp
  qed
qed

end