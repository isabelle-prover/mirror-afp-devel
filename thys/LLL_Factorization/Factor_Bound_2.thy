(*
    Authors:    Jose Divasón
                Sebastiaan Joosten
                René Thiemann
                Akihisa Yamada
    License:    BSD
*)

section \<open>Factor bound\<close>

text \<open>This theory extends the work about factor bounds which was carried out 
  in the Berlekamp-Zassenhaus development.
\<close> 

theory Factor_Bound_2
imports Berlekamp_Zassenhaus.Factor_Bound
   LLL_Basis_Reduction.Norms
begin

(*TODO: This norm should have been defined somewhere*)
definition "norm1 p = sum_list (map abs (coeffs p))"

lemma mahler_landau_graeffe_approximation_core: 
  assumes g: "g = graeffe_poly_impl f k" 
  shows "mahler_measure f \<le> root (2 ^ Suc k) (real_of_int (\<Sum>a\<leftarrow>coeffs g. a * a))" 
proof -
  have "mahler_measure f = root (2^k) (mahler_measure f ^ (2^k))" 
    by (simp add: real_root_power_cancel mahler_measure_ge_0) 
  also have "\<dots> = root (2^k) (mahler_measure g)" 
    unfolding graeffe_poly_impl_mahler g by simp
  also have "\<dots> = root (2^k) (root 2 (((mahler_measure g)^2)))" 
    by (simp add: real_root_power_cancel mahler_measure_ge_0) 
  also have "\<dots> = root (2^Suc k) (((mahler_measure g)^2))"
    by (metis power_Suc2 real_root_mult_exp)
  also have "\<dots> \<le> root (2 ^ Suc k) (real_of_int (\<Sum>a\<leftarrow>coeffs g. a * a))" 
  proof (rule real_root_le_mono, force)
    have square_mono: "0 \<le> (x :: real) \<Longrightarrow> x \<le> y \<Longrightarrow> x * x \<le> y * y" for x y
      by (simp add: mult_mono')
    obtain gs where gs: "coeffs g = gs" by auto
    have "(mahler_measure g)\<^sup>2 \<le> real_of_int \<bar>\<Sum>a\<leftarrow>coeffs g. a * a\<bar>" 
      using square_mono[OF mahler_measure_ge_0 Landau_inequality[of "of_int_poly g", folded mahler_measure_def]]
      by (auto simp: power2_eq_square coeffs_map_poly o_def of_int_hom.hom_sum_list)
    also have "\<bar>\<Sum>a\<leftarrow>coeffs g. a * a\<bar> = (\<Sum>a\<leftarrow>coeffs g. a * a)" unfolding gs
      by (induct gs, auto)
    finally show "(mahler_measure g)\<^sup>2 \<le> real_of_int (\<Sum>a\<leftarrow>coeffs g. a * a)" .
  qed
  finally show "mahler_measure f \<le> root (2 ^ Suc k) (real_of_int (\<Sum>a\<leftarrow>coeffs g. a * a))" .
qed

lemma Landau_inequality_mahler_measure: "mahler_measure f \<le> sqrt (real_of_int (\<Sum>a\<leftarrow>coeffs f. a * a))"
  by (rule order.trans[OF mahler_landau_graeffe_approximation_core[OF refl, of _ 0]],
  auto simp: graeffe_poly_impl_def sqrt_def)

lemma mahler_landau_graeffe_approximation: (* TODO replace lemma in Mahler_Measure.thy *)
  assumes g: "g = graeffe_poly_impl f k" "dd = d^(2^(Suc k))" "kk = 2^(Suc k)" 
  shows "\<lfloor>real d * mahler_measure f\<rfloor> \<le> mahler_landau_graeffe_approximation kk dd g"
proof -
  have id1: "real_of_int (int (d ^ 2 ^ Suc k)) = (real d) ^ 2 ^ Suc k" by simp
  have id2: "root (2 ^ Suc k) (real d ^ 2 ^ Suc k) = real d" 
    by (simp add: real_root_power_cancel)
  show ?thesis unfolding mahler_landau_graeffe_approximation_def Let_def root_int_floor of_int_mult g(2-3)
    by (rule floor_mono, unfold real_root_mult id1 id2, rule mult_left_mono, 
    rule mahler_landau_graeffe_approximation_core[OF g(1)], auto)
qed

(* TODO: replace in Factor_Bound.thy*)
lemma mignotte_helper_coeff_int': "cmod (coeff_int (\<Prod>a\<leftarrow>lst. [:- a, 1:]) i)
    \<le> ((length lst - 1) choose i) * (\<Prod>a\<leftarrow>lst. (max 1 (cmod a))) 
    + min i 1 * ((length lst - 1) choose (nat (i - 1)))"
  by (rule order.trans[OF mignotte_helper_coeff_int], auto simp: choose_int_def min_def)

(* TODO: replace in Factor_Bound.thy*)
lemma mignotte_helper_coeff: 
  "cmod (coeff h i) \<le> (degree h - 1 choose i) * mahler_measure_poly h 
      + min i 1 * (degree h - 1 choose (i - 1)) * cmod (lead_coeff h)"
proof -
  let ?r = "complex_roots_complex h"
  have "cmod (coeff h i) = cmod (coeff (smult (lead_coeff h) (\<Prod>a\<leftarrow>?r. [:- a, 1:])) i)"
    unfolding complex_roots by auto
  also have "\<dots> = cmod (lead_coeff h) * cmod (coeff (\<Prod>a\<leftarrow>?r. [:- a, 1:]) i)" by(simp add:norm_mult)
  also have "\<dots> \<le> cmod (lead_coeff h) * ((degree h - 1 choose i) * mahler_measure_monic h + 
    (min i 1 * ((degree h - 1) choose nat (int i - 1))))"    
    unfolding mahler_measure_monic_def
    by (rule mult_left_mono, insert mignotte_helper_coeff_int'[of ?r i], auto)
  also have "\<dots> = (degree h - 1 choose i) * mahler_measure_poly h + cmod (lead_coeff h) * (
    min i 1 * ((degree h - 1) choose nat (int i - 1)))" 
    unfolding mahler_measure_poly_via_monic by (simp add: field_simps)
  also have "nat (int i - 1) = i - 1" by (cases i, auto)
  finally show ?thesis by (simp add: ac_simps split: if_splits)
qed

(* TODO: replace in Factor_Bound.thy *)
lemma mignotte_coeff_helper:
  "abs (coeff h i) \<le> 
   (degree h - 1 choose i) * mahler_measure h +
   (min i 1 * (degree h - 1 choose (i - 1)) * abs (lead_coeff h))"
  unfolding mahler_measure_def
  using mignotte_helper_coeff[of "of_int_poly h" i] 
  by auto



lemma mignotte_bound_main:  
  assumes "f \<noteq> 0" "g dvd f" "degree g \<le> n"
  shows "\<bar>coeff g k\<bar> \<le> \<lfloor>real (n - 1 choose k) * mahler_measure f\<rfloor> +
       int (min k 1 * (n - 1 choose (k - 1))) * \<bar>lead_coeff f\<bar>"   
proof-
  let ?bnd = 2
  let ?n = "(n - 1) choose k" 
  let ?n' = "min k 1 * ((n - 1) choose (k - 1))" 
  let ?approx = "mahler_approximation ?bnd ?n f" 
  obtain h where gh:"g * h = f" using assms by (metis dvdE)
  have nz:"g\<noteq>0" "h\<noteq>0" using gh assms(1) by auto
  have g1:"(1::real) \<le> mahler_measure h" using mahler_measure_poly_ge_1 gh assms(1) by auto
  note g0 = mahler_measure_ge_0
  have to_n: "(degree g - 1 choose k) \<le> real ?n"
    using binomial_mono_left[of "degree g - 1" "n - 1" k] assms(3) by auto
  have to_n': "min k 1 * (degree g - 1 choose (k - 1)) \<le> real ?n'"
    using binomial_mono_left[of "degree g - 1" "n - 1" "k - 1"] assms(3)
    by (simp add: min_def)
  have "\<bar>coeff g k\<bar> \<le> (degree g - 1 choose k) * mahler_measure g
    + (real (min k 1 * (degree g - 1 choose (k - 1))) * \<bar>lead_coeff g\<bar>)" 
    using mignotte_coeff_helper[of g k] by simp
  also have "\<dots> \<le> ?n * mahler_measure f + real ?n' * \<bar>lead_coeff f\<bar>"
  proof (rule add_mono[OF mult_mono[OF to_n] mult_mono[OF to_n']])
    have "mahler_measure g  \<le> mahler_measure g * mahler_measure h" using g1 g0[of g]
      using mahler_measure_poly_ge_1 nz(1) by force
    thus "mahler_measure g \<le> mahler_measure f"
      using measure_eq_prod[of "of_int_poly g" "of_int_poly h"]
      unfolding mahler_measure_def gh[symmetric] by (auto simp: hom_distribs)
    have *: "lead_coeff f = lead_coeff g * lead_coeff h" 
      unfolding arg_cong[OF gh, of lead_coeff, symmetric] by (rule lead_coeff_mult)
    have "\<bar>lead_coeff h\<bar> \<noteq> 0" using nz(2) by auto
    hence lh: "\<bar>lead_coeff h\<bar> \<ge> 1" by linarith
    have "\<bar>lead_coeff f\<bar> = \<bar>lead_coeff g\<bar> * \<bar>lead_coeff h\<bar>" unfolding * by (rule abs_mult)
    also have "\<dots> \<ge> \<bar>lead_coeff g\<bar> * 1" 
      by (rule mult_mono, insert lh, auto)
    finally have "\<bar>lead_coeff g\<bar> \<le> \<bar>lead_coeff f\<bar>" by simp
    thus "real_of_int \<bar>lead_coeff g\<bar> \<le> real_of_int \<bar>lead_coeff f\<bar>" by simp
  qed (auto simp: g0)
  finally have "\<bar>coeff g k\<bar> \<le> ?n * mahler_measure f + real_of_int (?n' * \<bar>lead_coeff f\<bar>)" by simp
  from floor_mono[OF this, folded floor_add_int]
  have "\<bar>coeff g k\<bar> \<le> floor (?n * mahler_measure f) + ?n' * \<bar>lead_coeff f\<bar>" by linarith
  thus ?thesis unfolding mignotte_bound_def Let_def using mahler_approximation[of ?n f ?bnd] by auto
qed

lemma Mignotte_bound: 
  shows "of_int \<bar>coeff g k\<bar> \<le> (degree g choose k) * mahler_measure g"
proof (cases "k \<le> degree g \<and> g \<noteq> 0")
  case False
  hence "coeff g k = 0" using le_degree by (cases "g = 0", auto)
  thus ?thesis using mahler_measure_ge_0[of g] by auto
next
  case kg: True
  hence g: "g \<noteq> 0" "g dvd g" by auto
  from mignotte_bound_main[OF g le_refl, of k]
  have "real_of_int \<bar>coeff g k\<bar>
    \<le> of_int \<lfloor>real (degree g - 1 choose k) * mahler_measure g\<rfloor> +
      of_int (int (min k 1 * (degree g - 1 choose (k - 1))) * \<bar>lead_coeff g\<bar>)" by linarith
  also have "\<dots> \<le> real (degree g - 1 choose k) * mahler_measure g 
     + real (min k 1 * (degree g - 1 choose (k - 1))) * (of_int \<bar>lead_coeff g\<bar> * 1)"
    by (rule add_mono, force, auto)
  also have "\<dots> \<le> real (degree g - 1 choose k) * mahler_measure g 
     + real (min k 1 * (degree g - 1 choose (k - 1))) * mahler_measure g"
    by (rule add_left_mono[OF mult_left_mono], 
    unfold mahler_measure_def mahler_measure_poly_def,
    rule mult_mono, auto intro!: prod_list_ge1)  
  also have "\<dots> = 
    (real ((degree g - 1 choose k) + (min k 1 * (degree g - 1 choose (k - 1))))) * mahler_measure g" 
    by (auto simp: field_simps)
  also have "(degree g - 1 choose k) + (min k 1 * (degree g - 1 choose (k - 1))) = degree g choose k"
  proof (cases "k = 0")
    case False
    then obtain kk where k: "k = Suc kk" by (cases k, auto)
    with kg obtain gg where g: "degree g = Suc gg" by (cases "degree g", auto)
    show ?thesis unfolding k g by auto
  qed auto
  finally show ?thesis .
qed

(* TODO replace proof of @{thm mignotte_bound} in Factor_Bound.thy *)
lemma mignotte_bound:  
  assumes "f \<noteq> 0" "g dvd f" "degree g \<le> n"
  shows "\<bar>coeff g k\<bar> \<le> mignotte_bound f n"  
proof -
  let ?bnd = 2
  let ?n = "(n - 1) choose ((n - 1) div 2)" 
  have to_n: "(n - 1 choose k) \<le> real ?n" for k
    using choose_approx[OF le_refl] by auto
  from mignotte_bound_main[OF assms, of k]
  have "\<bar>coeff g k\<bar> \<le> 
    \<lfloor>real (n - 1 choose k) * mahler_measure f\<rfloor> + 
    int (min k 1 * (n - 1 choose (k - 1))) * \<bar>lead_coeff f\<bar>" .
  also have "\<dots> \<le> \<lfloor>real (n - 1 choose k) * mahler_measure f\<rfloor> + 
    int ((n - 1 choose (k - 1))) * \<bar>lead_coeff f\<bar>"
    by (rule add_left_mono[OF mult_right_mono], cases k, auto)
  also have "\<dots> \<le> mignotte_bound f n" 
    unfolding mignotte_bound_def Let_def
    by (rule add_mono[OF order.trans[OF floor_mono[OF mult_right_mono] 
    mahler_approximation[of ?n f ?bnd]] mult_right_mono], insert to_n mahler_measure_ge_0, auto)
  finally show ?thesis .
qed

lemma norm_1_bound_mignotte: "norm1 f \<le> 2^(degree f) * mahler_measure f"
proof (cases "f = 0")
  case f0: False
  have cf: "coeffs f = map (\<lambda> i. coeff f i) [0 ..< Suc( degree f)]" unfolding coeffs_def 
    using f0 by auto
  have "real_of_int (sum_list (map abs (coeffs f))) 
    = sum (\<lambda> i. of_int (abs (coeff f i))) {0 .. degree f}" 
    unfolding cf of_int_hom.hom_sum_list unfolding sum_list_sum_nth 
    by (rule sum.cong, force, auto simp: o_def nth_append)
  also have "\<dots> \<le> sum (\<lambda> i. (degree f choose i) * mahler_measure f) {0 .. degree f}" 
    by (rule sum_mono, rule Mignotte_bound)
  also have "\<dots> = real (sum (\<lambda> i. (degree f choose i)) {0 .. degree f}) * mahler_measure f" 
    unfolding sum_distrib_right[symmetric] by auto
  also have "\<dots> = 2^(degree f) * mahler_measure f" unfolding choose_row_sum by auto
  finally show ?thesis unfolding norm1_def .
qed (auto simp: mahler_measure_ge_0 norm1_def)

lemma norm1_ge_0: "norm1 (f :: 'a :: {abs,ordered_semiring_0,ordered_ab_group_add_abs}poly) \<ge> 0" unfolding norm1_def 
  by (rule sum_list_nonneg, auto)

lemma mahler_measure_dvd: assumes "f \<noteq> 0" and "h dvd f" 
  shows "mahler_measure h \<le> mahler_measure f" 
proof -
  from assms obtain g where f: "f = g * h" unfolding dvd_def by auto
  from f assms have g0: "g \<noteq> 0" by auto
  hence mg: "mahler_measure g \<ge> 1" by (rule mahler_measure_poly_ge_1)
  have "1 * mahler_measure h \<le> mahler_measure f" 
    unfolding mahler_measure_def f measure_eq_prod
      of_int_poly_hom.hom_mult unfolding mahler_measure_def[symmetric]
    by (rule mult_right_mono[OF mg mahler_measure_ge_0])    
  thus ?thesis by simp
qed

lemma mahler_measure_l2norm: "mahler_measure f \<le> sqrt (of_int \<parallel>f\<parallel>\<^sup>2)" 
  using Landau_inequality_mahler_measure[of f] unfolding sq_norm_poly_def
  by (auto simp: power2_eq_square)

lemma norm2_norm1_main_equality: fixes f :: "nat \<Rightarrow> 'a :: linordered_idom" 
  shows "(\<Sum>i = 0..<n. \<bar>f i\<bar>)\<^sup>2 = (\<Sum>i = 0..<n. f i * f i)
      + (\<Sum>i = 0..<n. \<Sum>j = 0..<n. if i = j then 0 else \<bar>f i\<bar> * \<bar>f j\<bar>)"  
proof (induct n)
  case (Suc n)
  have id: "{0 ..< Suc n} = insert n {0 ..< n}" by auto
  have id: "sum f {0 ..< Suc n} = f n + sum f {0 ..< n}" for f :: "nat \<Rightarrow> 'a" 
    unfolding id by (rule sum.insert, auto)
  show ?case unfolding id power2_sum unfolding Suc
    by (auto simp: power2_eq_square sum_distrib_left sum.distrib ac_simps)
qed auto

lemma norm2_norm1_main_inequality: fixes f :: "nat \<Rightarrow> 'a :: linordered_idom" 
  shows "(\<Sum>i = 0..<n. f i * f i) \<le> (\<Sum>i = 0..<n. \<bar>f i\<bar>)\<^sup>2"  
  unfolding norm2_norm1_main_equality 
  by (auto intro!: sum_nonneg)  

lemma norm2_le_norm1_int: "\<parallel>f :: int poly\<parallel>\<^sup>2 \<le> (norm1 f)^2" 
proof -
  define F where "F = (!) (coeffs f)" 
  define n where "n = length (coeffs f)" 
  have 1: "\<parallel>f\<parallel>\<^sup>2 = (\<Sum>i = 0..<n. F i * F i)" 
    unfolding norm1_def sq_norm_poly_def sum_list_sum_nth F_def n_def
    by (subst sum.cong, auto simp: power2_eq_square)
  have 2: "norm1 f = (\<Sum>i = 0..<n. \<bar>F i\<bar>)" 
    unfolding norm1_def sq_norm_poly_def sum_list_sum_nth F_def n_def
    by (subst sum.cong, auto)
  show ?thesis unfolding 1 2 by (rule norm2_norm1_main_inequality)
qed

lemma sq_norm_factor_bound: 
  fixes f h :: "int poly"
  assumes dvd: "h dvd f" and f0: "f \<noteq> 0" 
  shows "\<parallel>h\<parallel>\<^sup>2 \<le> int (degree f + 1) * 2^(2 * degree h) * \<parallel>f\<parallel>\<^sub>\<infinity>\<^sup>2" (is ?g1)
  "\<parallel>h\<parallel>\<^sup>2 \<le> 2 ^ (2 * degree h) * \<parallel>f\<parallel>\<^sup>2" 
proof - 
  let ?r = real_of_int
  have h21: "?r \<parallel>h\<parallel>\<^sup>2 \<le> (?r (norm1 h))^2" using norm2_le_norm1_int[of h]
    by (metis of_int_le_iff of_int_power)
  also have "\<dots> \<le> (2^(degree h) * mahler_measure h)^2" 
    using power_mono[OF norm_1_bound_mignotte[of h], of 2] 
    by (auto simp: norm1_ge_0)
  also have "\<dots> = 2^(2 * degree h) * (mahler_measure h)^2"
    by (simp add: power_even_eq power_mult_distrib)
  also have "\<dots> \<le> 2^(2 * degree h) * (mahler_measure f)^2" 
    by (rule mult_left_mono[OF power_mono], auto simp: mahler_measure_ge_0
    mahler_measure_dvd[OF f0 dvd])
  also have "\<dots> \<le> 2^(2 * degree h) * ?r (\<parallel>f\<parallel>\<^sup>2)"
  proof (rule mult_left_mono)
    have "?r (\<parallel>f\<parallel>\<^sup>2) \<ge> 0" by auto
    from real_sqrt_pow2[OF this]
    show "(mahler_measure f)\<^sup>2 \<le> ?r (\<parallel>f\<parallel>\<^sup>2)" 
      using power_mono[OF mahler_measure_l2norm[of f], of 2]
      by (auto simp: mahler_measure_ge_0)
  qed auto
  also have "\<dots> = ?r (2^(2*degree h) * \<parallel>f\<parallel>\<^sup>2)" 
    by (simp add: ac_simps)
  finally show "\<parallel>h\<parallel>\<^sup>2 \<le> 2 ^ (2 * degree h) * \<parallel>f\<parallel>\<^sup>2" unfolding of_int_le_iff .
  also have "\<dots> \<le> 2^(2 * degree h) * (int (degree f + 1) * \<parallel>f\<parallel>\<^sub>\<infinity>\<^sup>2)" 
    by (rule mult_left_mono, rule sq_norm_poly_le_linf_norm, auto)
  finally show ?g1 by (simp add: ac_simps)
qed

end
