(*
  File:      Polynomial_Crit_Geometry/Polynomial_Crit_Geometry_Library.thy
  Authors:   Manuel Eberl, University of Innsbruck
*)
section \<open>Missing Library Material\<close>
theory Polynomial_Crit_Geometry_Library
imports
  "HOL-Computational_Algebra.Computational_Algebra"
  "HOL-Library.FuncSet"
  "Formal_Puiseux_Series.Formal_Puiseux_Series" (* for alg_closed_field *)
begin

(* TODO: all of this probably belongs in the library *)

subsection \<open>Multisets\<close>

lemma size_repeat_mset [simp]: "size (repeat_mset n A) = n * size A"
  by (induction n) auto

lemma count_image_mset_inj:
  "inj f \<Longrightarrow> count (image_mset f A) (f x) = count A x"
  by (induction A) (auto dest!: injD)

lemma count_le_size: "count A x \<le> size A"
  by (induction A) auto

lemma image_mset_cong_simp:
  "M = M' \<Longrightarrow> (\<And>x. x \<in># M =simp=> f x = g x) \<Longrightarrow> {#f x. x \<in># M#} = {#g x. x \<in># M'#}"
  unfolding simp_implies_def by (auto intro: image_mset_cong)

lemma sum_mset_nonneg:
  fixes A :: "'a :: ordered_comm_monoid_add multiset"
  assumes "\<And>x. x \<in># A \<Longrightarrow> x \<ge> 0"
  shows   "sum_mset A \<ge> 0"
  using assms by (induction A) auto

lemma sum_mset_pos:
  fixes A :: "'a :: ordered_comm_monoid_add multiset"
  assumes "A \<noteq> {#}"
  assumes "\<And>x. x \<in># A \<Longrightarrow> x > 0"
  shows   "sum_mset A > 0"
proof -
  from assms obtain x where "x \<in># A"
    by auto
  hence "A = {#x#} + (A - {#x#})"
    by auto
  also have "sum_mset \<dots> = x + sum_mset (A - {#x#})"
    by simp
  also have "\<dots> > 0"
  proof (rule add_pos_nonneg)
    show "x > 0"
      using \<open>x \<in># A\<close> assms by auto
    show "sum_mset (A - {#x#}) \<ge> 0"
      using assms sum_mset_nonneg by (metis in_diffD order_less_imp_le)
  qed
  finally show ?thesis .
qed


subsection \<open>Polynomials\<close>

lemma order_pos_iff: "p \<noteq> 0 \<Longrightarrow> order x p > 0 \<longleftrightarrow> poly p x = 0"
  by (cases "order x p = 0") (auto simp: order_root order_0I)

lemma order_prod_mset:
  "0 \<notin># P \<Longrightarrow> order x (prod_mset P) = sum_mset (image_mset (\<lambda>p. order x p) P)"
  by (induction P) (auto simp: order_mult)

lemma order_prod:
  "(\<And>x. x \<in> I \<Longrightarrow> f x \<noteq> 0) \<Longrightarrow> order x (prod f I) = (\<Sum>i\<in>I. order x (f i))"
  by (induction I rule: infinite_finite_induct) (auto simp: order_mult)

lemma order_linear_factor:
  assumes "a \<noteq> 0 \<or> b \<noteq> 0"
  shows "order x [:a, b:] = (if b * x + a = 0 then 1 else 0)"
proof (cases "b * x + a = 0")
  case True
  have "order x [:a, b:] \<le> degree [:a, b:]"
    using assms by (intro order_degree) auto
  also have "\<dots> \<le> 1"
    by simp
  finally have "order x [:a, b:] \<le> 1" .
  moreover have "order x [:a, b:] > 0"
    using assms True by (subst order_pos_iff) (auto simp: algebra_simps)
  ultimately have "order x [:a, b:] = 1"
    by linarith
  with True show ?thesis
    by simp
qed (auto intro!: order_0I simp: algebra_simps)

lemma order_linear_factor' [simp]:
  assumes "a \<noteq> 0 \<or> b \<noteq> 0" "b * x + a = 0"
  shows "order x [:a, b:] = 1"
  using assms by (subst order_linear_factor) auto

lemma degree_prod_mset_eq: "0 \<notin># P \<Longrightarrow> degree (prod_mset P) = (\<Sum>p\<in>#P. degree p)"
  for P :: "'a::idom poly multiset"
  by (induction P) (auto simp: degree_mult_eq)

lemma degree_prod_list_eq: "0 \<notin> set ps \<Longrightarrow> degree (prod_list ps) = (\<Sum>p\<leftarrow>ps. degree p)"
  for ps :: "'a::idom poly list"
  by (induction ps) (auto simp: degree_mult_eq)

lemma order_conv_multiplicity:
  assumes "p \<noteq> 0"
  shows   "order x p = multiplicity [:-x, 1:] p"
  using assms order[of p x] multiplicity_eqI by metis


subsection \<open>Polynomials over algebraically closed fields\<close>

lemma irreducible_alg_closed_imp_degree_1:
  assumes "irreducible (p :: 'a :: alg_closed_field poly)"
  shows   "degree p = 1"
proof -
  have "\<not>(degree p > 1)"
    using assms alg_closed_imp_reducible by blast
  moreover from assms have "degree p \<noteq> 0"
    by (intro notI) auto
  ultimately show ?thesis
    by linarith
qed

lemma prime_poly_alg_closedE:
  assumes "prime (q :: 'a :: {alg_closed_field, field_gcd} poly)"
  obtains c where "q = [:-c, 1:]" "poly q c = 0"
proof -
  from assms have "degree q = 1"
    by (intro irreducible_alg_closed_imp_degree_1 prime_elem_imp_irreducible) auto
  then obtain a b where q: "q = [:a, b:]"
    by (metis One_nat_def degree_pCons_eq_if nat.distinct(1) nat.inject pCons_cases)
  have "unit_factor q = 1"
    using assms by auto
  thus ?thesis
    using that[of "-a"] q \<open>degree q = 1\<close>
    by (auto simp: unit_factor_poly_def one_pCons split: if_splits)
qed

lemma prime_factors_alg_closed_poly_bij_betw:
  assumes "p \<noteq> (0 :: 'a :: {alg_closed_field, field_gcd} poly)"
  shows "bij_betw (\<lambda>x. [:-x, 1:]) {x. poly p x = 0} (prime_factors p)"
proof (rule bij_betwI[of _ _ _ "\<lambda>q. -poly q 0"], goal_cases)
  case 1
  have [simp]: "p div [:1:] = p" for p :: "'a poly"
    by (simp add: pCons_one)
  show ?case using assms
    by (auto simp: in_prime_factors_iff dvd_iff_poly_eq_0 prime_def 
          prime_elem_linear_field_poly normalize_poly_def one_pCons)
qed (auto simp: in_prime_factors_iff elim!: prime_poly_alg_closedE dvdE)

lemma alg_closed_imp_factorization':
  assumes "p \<noteq> (0 :: 'a :: alg_closed_field poly)"
  shows "p = smult (lead_coeff p) (\<Prod>x | poly p x = 0. [:-x, 1:] ^ order x p)"
proof -
  obtain A where A: "size A = degree p" "p = smult (lead_coeff p) (\<Prod>x\<in>#A. [:- x, 1:])"
    using alg_closed_imp_factorization[OF assms] by blast
  have "set_mset A = {x. poly p x = 0}" using assms 
    by (subst A(2)) (auto simp flip: poly_hom.prod_mset_image simp: image_image)

  note A(2)
  also have "(\<Prod>x\<in>#A. [:- x, 1:]) =
               (\<Prod>x\<in>(\<lambda>x. [:- x, 1:]) ` set_mset A. x ^ count {#[:- x, 1:]. x \<in># A#} x)"
    by (subst prod_mset_multiplicity) simp_all
  also have "set_mset A = {x. poly p x = 0}" using assms 
    by (subst A(2)) (auto simp flip: poly_hom.prod_mset_image simp: image_image)
  also have "(\<Prod>x\<in>(\<lambda>x. [:- x, 1:]) ` {x. poly p x = 0}. x ^ count {#[:- x, 1:]. x \<in># A#} x) =
             (\<Prod>x | poly p x = 0. [:- x, 1:] ^ count {#[:- x, 1:]. x \<in># A#} [:- x, 1:])"
    by (subst prod.reindex) (auto intro: inj_onI)
  also have "(\<lambda>x. count {#[:- x, 1:]. x \<in># A#} [:- x, 1:]) = count A"
    by (subst count_image_mset_inj) (auto intro!: inj_onI)
  also have "count A = (\<lambda>x. order x p)"
  proof
    fix x :: 'a
    have "order x p = order x (\<Prod>x\<in>#A. [:- x, 1:])"
      using assms by (subst A(2)) (auto simp: order_smult order_prod_mset)
    also have "\<dots> = (\<Sum>y\<in>#A. order x [:-y, 1:])"
      by (subst order_prod_mset) (auto simp: multiset.map_comp o_def)
    also have "image_mset (\<lambda>y. order x [:-y, 1:]) A = image_mset (\<lambda>y. if y = x then 1 else 0) A"
      using order_power_n_n[of y 1 for y :: 'a]
      by (intro image_mset_cong) (auto simp: order_0I)
    also have "\<dots> = replicate_mset (count A x) 1 + replicate_mset (size A - count A x) 0"
      by (induction A) (auto simp: add_ac Suc_diff_le count_le_size)
    also have "sum_mset \<dots> = count A x"
      by simp
    finally show "count A x = order x p" ..
  qed
  finally show ?thesis .
qed


subsection \<open>Complex polynomials and conjugation\<close>

lemma complex_poly_real_coeffsE:
  assumes "set (coeffs p) \<subseteq> \<real>"
  obtains p' where "p = map_poly complex_of_real p'"
proof (rule that)
  have "coeff p n \<in> \<real>" for n
    using assms by (metis Reals_0 coeff_in_coeffs in_mono le_degree zero_poly.rep_eq)
  thus "p = map_poly complex_of_real (map_poly Re p)"
    by (subst map_poly_map_poly) (auto simp: poly_eq_iff o_def coeff_map_poly)
qed

lemma order_map_poly_cnj:
  assumes "p \<noteq> 0"
  shows   "order x (map_poly cnj p) = order (cnj x) p"
proof -
  have "order x (map_poly cnj p) \<le> order (cnj x) p" if p: "p \<noteq> 0" for p :: "complex poly" and x
  proof (rule order_max)
    interpret map_poly_idom_hom cnj
      by standard auto
    interpret field_hom cnj
      by standard auto
    have "[:-x, 1:] ^ order x (map_poly cnj p) dvd map_poly cnj p"
      using order[of "map_poly cnj p" x] p by simp
    also have "[:-x, 1:] ^ order x (map_poly cnj p) =
               map_poly cnj ([:-cnj x, 1:] ^ order x (map_poly cnj p))"
      by (simp add: hom_power)
    finally show "[:-cnj x, 1:] ^ order x (map_poly cnj p) dvd p"
      by (rule dvd_map_poly_hom_imp_dvd)
  qed fact+
  from this[of p x] and this[of "map_poly cnj p" "cnj x"] and assms show ?thesis
    by (simp add: map_poly_map_poly o_def)
qed


subsection \<open>\<open>n\<close>-ary product rule for the derivative\<close>

lemma has_field_derivative_prod_mset [derivative_intros]:
  assumes "\<And>x. x \<in># A \<Longrightarrow> (f x has_field_derivative f' x) (at z)"
  shows   "((\<lambda>u. \<Prod>x\<in>#A. f x u) has_field_derivative (\<Sum>x\<in>#A. f' x * (\<Prod>y\<in>#A-{#x#}. f y z))) (at z)"
  using assms
proof (induction A)
  case (add x A)
  note [derivative_intros] = add
  note [cong] = image_mset_cong_simp
  show ?case
    by (auto simp: field_simps multiset.map_comp o_def  intro!: derivative_eq_intros)
qed auto

lemma has_field_derivative_prod [derivative_intros]:
  assumes "\<And>x. x \<in> A \<Longrightarrow> (f x has_field_derivative f' x) (at z)"
  shows   "((\<lambda>u. \<Prod>x\<in>A. f x u) has_field_derivative (\<Sum>x\<in>A. f' x * (\<Prod>y\<in>A-{x}. f y z))) (at z)"
  using assms
proof (cases "finite A")
  case [simp, intro]: True
  have "((\<lambda>u. \<Prod>x\<in>A. f x u) has_field_derivative
          (\<Sum>x\<in>A. f' x * (\<Prod>y\<in>#mset_set A-{#x#}. f y z))) (at z)"
    using has_field_derivative_prod_mset[of "mset_set A" f f' z] assms
    by (simp add: prod_unfold_prod_mset sum_unfold_sum_mset)
  also have "(\<Sum>x\<in>A. f' x * (\<Prod>y\<in>#mset_set A-{#x#}. f y z)) =
             (\<Sum>x\<in>A. f' x * (\<Prod>y\<in>#mset_set (A-{x}). f y z))"
    by (intro sum.cong) (auto simp: mset_set_Diff)
  finally show ?thesis
    by (simp add: prod_unfold_prod_mset)
qed auto

lemma has_field_derivative_prod_mset':
  assumes "\<And>x. x \<in># A \<Longrightarrow> f x z \<noteq> 0"
  assumes "\<And>x. x \<in># A \<Longrightarrow> (f x has_field_derivative f' x) (at z)"
  defines "P \<equiv> (\<lambda>A u. \<Prod>x\<in>#A. f x u)"
  shows   "(P A has_field_derivative (P A z * (\<Sum>x\<in>#A. f' x / f x z))) (at z)"
  using assms
  by (auto intro!: derivative_eq_intros cong: image_mset_cong_simp
           simp:   sum_distrib_right mult_ac prod_mset_diff image_mset_Diff multiset.map_comp o_def)

lemma has_field_derivative_prod':
  assumes "\<And>x. x \<in> A \<Longrightarrow> f x z \<noteq> 0"
  assumes "\<And>x. x \<in> A \<Longrightarrow> (f x has_field_derivative f' x) (at z)"
  defines "P \<equiv> (\<lambda>A u. \<Prod>x\<in>A. f x u)"
  shows   "(P A has_field_derivative (P A z * (\<Sum>x\<in>A. f' x / f x z))) (at z)"
proof (cases "finite A")
  case True
  show ?thesis using assms True
    by (auto intro!: derivative_eq_intros
             simp: prod_diff1 sum_distrib_left sum_distrib_right mult_ac)
qed (auto simp: P_def)


subsection \<open>Facts about complex numbers\<close>

lemma Re_sum_mset: "Re (sum_mset X) = (\<Sum>x\<in>#X. Re x)"
  by (induction X) auto

lemma Im_sum_mset: "Im (sum_mset X) = (\<Sum>x\<in>#X. Im x)"
  by (induction X) auto

lemma Re_sum_mset': "Re (\<Sum>x\<in>#X. f x) = (\<Sum>x\<in>#X. Re (f x))"
  by (induction X) auto

lemma Im_sum_mset': "Im (\<Sum>x\<in>#X. f x) = (\<Sum>x\<in>#X. Im (f x))"
  by (induction X) auto

lemma inverse_complex_altdef: "inverse z = cnj z / norm z ^ 2"
  by (metis complex_div_cnj inverse_eq_divide mult_1)

end
