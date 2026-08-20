section \<open>Prerequisites for the Detour Calculus\<close>
theory Detour_Prerequisites
  imports 
    "HOL-Complex_Analysis.Residue_Theorem" 
    "Winding_Number_Eval.Missing_Analysis"
    "Winding_Number_Eval.Missing_Transcendental"
    "Path_Automation.Path_Automation"
    Path_Nhds
    "HOL-Library.Real_Mod"
begin

subsection \<open>Miscellaneous\<close>

lemma inverse_conv_cnj: "norm z = 1 \<Longrightarrow> inverse z = cnj z"
  by (simp add: divide_conv_cnj inverse_eq_divide)

lemma dist_cnj: "dist (cnj x) (cnj y) = dist x y"
  by (simp add: dist_norm norm_complex_def power2_commute)

lemma closed_segment_cnj: "closed_segment (cnj w) (cnj z) = cnj ` closed_segment w z"
  using closed_segment_linear_image linear_cnj by blast

lemma closed_segment_mult:
  "(*) (c :: 'a :: real_algebra_1) ` closed_segment a b = closed_segment (c * a) (c * b)"
  by (rule closed_segment_linear_image [symmetric]) auto

lemma arcsin_pos: "x \<in> {0<..1} \<Longrightarrow> arcsin x > 0"
  by (metis arcsin_0 arcsin_less_arcsin greaterThanAtMost_iff neg_le_0_iff_le zero_less_one_class.zero_le_one)

lemma sin_lt_zero': "x \<in> {-pi<..<0} \<Longrightarrow> sin x < 0"
  by (metis greaterThanLessThan_iff minus_less_iff neg_0_less_iff_less sin_gt_zero sin_minus)

lemma tan_arcsin: "x \<in> {-1..1} \<Longrightarrow> tan (arcsin x) = x / sqrt (1 - x ^ 2)"
  by (simp add: tan_def cos_arcsin)

lemma Arg_neg_real [simp]: "Im x = 0 \<Longrightarrow> Re x < 0 \<Longrightarrow> Arg x = pi"
  using Arg_eq_pi by blast

lemma cis_eq_1_iff':
  assumes "\<bar>x\<bar> < 2 * pi"
  shows   "cis x = 1 \<longleftrightarrow> x = 0"
proof
  assume "cis x = 1"
  then obtain n where n: "x = of_int n * 2 * pi"
    by (auto simp: cis_eq_1_iff)
  with assms have "n = 0"
    by (auto simp: abs_mult simp flip: of_int_abs)
  with n show "x = 0"
    by simp
qed auto

lemma DeMoivre_int: "cis x powi n = cis (of_int n * x)"
proof (cases "n \<ge> 0")
  case True
  hence "cis x powi n = cis x ^ nat n"
    by (simp add: power_int_def)
  also have "\<dots> = cis (real (nat n) * x)"
    by (rule Complex.DeMoivre)
  finally show ?thesis
    using True by simp
next
  case False
  hence "cis x powi n = cis (-x) ^ nat (-n)"
    by (simp add: power_int_def)
  also have "\<dots> = cis (-real (nat (-n)) * x)"
    by (subst Complex.DeMoivre) auto
  finally show ?thesis
    using False by simp
qed

lemma cis_of_int_times_pi_half: "cis (of_int n * pi / 2) = \<i> powi n"
 using DeMoivre_int[of "pi / 2" n] by simp

lemma cis_of_nat_times_pi_half: "cis (real n * pi / 2) = \<i> ^ n"
  using cis_of_int_times_pi_half[of "int n"] by simp

lemma cis_of_int_times_pi: "cis (of_int n * pi) = (-1) powi n"
 using DeMoivre_int[of pi n] by simp

lemma cis_of_nat_times_pi: "cis (real n * pi) = (-1) ^ n"
  using cis_of_int_times_pi[of "int n"] by simp

lemma power3_i [simp]: "\<i> ^ 3 = -\<i>"
  and power4_i [simp]: "\<i> ^ 4 = 1"
  by (simp_all add: eval_nat_numeral)

lemma i_power_mod4: "\<i> ^ n = \<i> ^ (n mod 4)"
proof -
  have "\<i> ^ n = \<i> ^ (4 * (n div 4) + n mod 4)"
    by simp
  also have "\<dots> = \<i> ^ (n mod 4)"
    by (subst power_add) (simp add: power_mult)
  finally show ?thesis .
qed

lemma cis_numeral_times_pi_half [simp]:
  "cis (numeral num * pi / 2) = \<i> ^ (numeral num mod 4)"
proof -
  have "cis (numeral num * pi / 2) = \<i> ^ numeral num"
    using cis_of_nat_times_pi_half[of "numeral num"] by simp
  also have "\<dots> = \<i> ^ (numeral num mod 4)"
    by (rule i_power_mod4)
  finally show ?thesis .
qed

lemma cis_numeral_pi_times_numeral_half [simp]:
  "cis (pi * numeral num / 2) = \<i> ^ (numeral num mod 4)"
  by (subst mult.commute) simp

lemma cis_numeral_times_pi [simp]:
  "cis (numeral num * pi) = (-1) ^ (numeral num mod 2)"
proof -
  have "cis (numeral num * pi) = (-1) ^ numeral num"
    using cis_of_nat_times_pi[of "numeral num"] by simp
  also have "\<dots> = (-1) ^ (numeral num mod 2)"
    by (metis even_mod_2_iff neg_one_even_power neg_one_odd_power)
  finally show ?thesis .
qed

lemma cis_pi_times_numeral [simp]:
  "cis (pi * numeral num) = (-1) ^ (numeral num mod 2)"
  by (subst mult.commute) simp

lemma cis_minus_numeral_times_pi_half [simp]:
  "cis (-(numeral num * pi / 2)) = (-\<i>) ^ (numeral num mod 4)"
  by (subst cis_cnj [symmetric]) auto

lemma cis_minus_numeral_times_pi [simp]:
  "cis (-(numeral num * pi)) = (-1) ^ (numeral num mod 2)"
  by (subst cis_cnj [symmetric]) auto

lemma cis_minus_pi_times_numeral_half [simp]:
  "cis (-(pi * numeral num / 2)) = (-\<i>) ^ (numeral num mod 4)"
  by (subst cis_cnj [symmetric]) auto

lemma cis_minus_pi_times_numeral_pi [simp]:
  "cis (-(pi * numeral num)) = (-1) ^ (numeral num mod 2)"
  by (subst cis_cnj [symmetric]) auto

lemma cis_minus_pi [simp]: "cis (-pi) = -1"
  by (simp flip: cis_cnj)

lemma inner_mult_both_complex: "(z * x :: complex) \<bullet> (z * y) = norm z ^ 2 * (x \<bullet> y)"
  unfolding cmod_power2 by (simp add: inner_complex_def algebra_simps power2_eq_square)

lemma orthogonal_transformation_mult_complex [intro]:
  "norm z = 1 \<Longrightarrow> orthogonal_transformation ((*) (z :: complex))"
  unfolding orthogonal_transformation_def
  by (auto intro!: linear_times simp: inner_mult_both_complex)

lemma contour_integral_affine:
  assumes "valid_path \<gamma>" "c \<noteq> 0"
  shows "contour_integral ((\<lambda>x. c * x + b) \<circ> \<gamma>) f = contour_integral \<gamma> (\<lambda>w. c * f (c * w + b))"
proof -
  define ff where "ff=(\<lambda>x. c*x+b)"
  have "contour_integral (ff \<circ> \<gamma>) f = contour_integral \<gamma> (\<lambda>w. deriv ff w * f (ff w))"
  proof (rule contour_integral_comp_analyticW)
    show "ff analytic_on UNIV" "path_image \<gamma> \<subseteq> UNIV" "valid_path \<gamma>"
    unfolding ff_def using \<open>valid_path \<gamma>\<close>
    by (auto intro: analytic_intros)
  qed
  also have "\<dots> = contour_integral \<gamma> (\<lambda>w. c * f (c * w + b))"
  proof -
    have "deriv ff  x = c" "ff x = c*x+b" for x
      unfolding ff_def by auto
    then show ?thesis by auto
  qed
  finally show ?thesis unfolding ff_def .
qed

(* TODO: unused *)
lemma finite_imp_eventually_sparse_at_0:
  assumes "finite X"
  shows   "eventually (\<lambda>\<epsilon>. sparse \<epsilon> X) (at_right 0)"
proof (cases "X = {} \<or> is_singleton X")
  case False
  hence ne: "Sigma X (\<lambda>x. X - {x}) \<noteq> {}"
    unfolding is_singleton_def by auto
  define m where "m = Min ((\<lambda>(x,y). dist x y) ` (Sigma X (\<lambda>x. X - {x})))"
  have "m > 0"
    unfolding m_def using ne by (subst Min_gr_iff) (use assms in auto)
  show ?thesis
    using eventually_at_right_real[OF \<open>m > 0\<close>]
  proof eventually_elim
    case (elim \<epsilon>)
    show ?case
    proof (intro sparseI)
      fix x y assume xy: "x \<in> X" "y \<in> X" "x \<noteq> y"
      have "\<epsilon> < m"
        using elim by simp
      also have "m \<le> dist x y"
        using xy unfolding m_def by (intro Min.coboundedI) (use assms in auto)
      finally show "dist x y > \<epsilon>" .
    qed
  qed
qed (auto elim!: is_singletonE)


subsection \<open>Lipschitz continuity\<close>

lemma complex_derivative_on_convex_imp_lipschitz:
  fixes f' :: "complex \<Rightarrow> complex"
  assumes deriv: "\<And>z. z \<in> A \<Longrightarrow> (f has_field_derivative f' z) (at z within A)"
  assumes A: "convex A" and C: "\<And>x. x \<in> A \<Longrightarrow> norm (f' x) \<le> C" "C \<ge> 0"
  shows   "C-lipschitz_on A f"
proof (rule lipschitz_onI)
  fix x y assume xy: "x \<in> A" "y \<in> A"
  let ?l = "linepath y x"
  have "(f' has_contour_integral f (pathfinish ?l) - f (pathstart ?l)) ?l"
  proof (rule contour_integral_primitive)
    show "(f has_field_derivative f' z) (at z within A)" if "z \<in> A" for z
      using deriv[OF that] .
    show "path_image (linepath y x) \<subseteq> A"
      unfolding path_image_linepath by (intro closed_segment_subset xy A)
  qed auto
  hence "norm (f (pathfinish ?l) - f (pathstart ?l)) \<le> C * norm (x - y)"
  proof (rule has_contour_integral_bound_linepath)
    fix z assume "z \<in> closed_segment y x"
    also have "closed_segment y x \<subseteq> A"
      by (intro closed_segment_subset xy A)
    finally show "norm (f' z) \<le> C"
      using C(1)[of z] by auto
  qed fact+
  thus "dist (f x) (f y) \<le> C * dist x y"
    by (simp add: dist_norm norm_minus_commute)
qed fact+

(* TODO: convex is *probably* not needed here. Just decompose into a finite union of discs. *)
lemma analytic_on_compact_convex_imp_lipschitz:
  assumes "f analytic_on A" "convex A" "compact A"
  obtains C where "C-lipschitz_on A f"
proof -
  have "deriv f analytic_on A"
    by (intro analytic_intros assms)
  define C where "C = Sup (norm ` (insert 0 (deriv f ` A)))"

  have "compact (insert 0 (deriv f ` A))"
    by (intro compact_insert compact_continuous_image analytic_imp_holomorphic
              holomorphic_on_imp_continuous_on analytic_intros assms)
  hence "bounded (insert 0 (deriv f ` A))"
    by (rule compact_imp_bounded)
  hence bdd: "bdd_above (norm ` insert 0 (deriv f ` A))"
    unfolding bdd_above_norm .

  show ?thesis
  proof (rule that[of C], rule complex_derivative_on_convex_imp_lipschitz)
    show "C \<ge> 0"
      unfolding C_def by (intro cSup_upper bdd) auto
  next
    show "(f has_field_derivative deriv f z) (at z within A)" if "z \<in> A" for z
      using that assms(1) analytic_on_holomorphic holomorphic_derivI by blast
  next
    show "norm (deriv f z) \<le> C" if "z \<in> A" for z
    proof -
      have "norm (deriv f z) \<in> norm ` insert 0 (deriv f ` A)"
        using that by auto
      moreover have "norm ` insert 0 (deriv f ` A) \<noteq> {}"
        by blast
      ultimately show "norm (deriv f z) \<le> C"
        unfolding C_def using bdd by (intro cSup_upper)
    qed
  qed fact+
qed

lemma lipschitz_on_complex_inverse:
  assumes "C > 0"
  shows   "(1/C^2)-lipschitz_on {z. Im z \<ge> C} (\<lambda>z. inverse z :: complex)"
proof (rule complex_derivative_on_convex_imp_lipschitz)
  show "((\<lambda>z. inverse z :: complex) has_field_derivative (-1 / z ^ 2)) (at z within {z. Im z \<ge> C})"
    if "z \<in> {z. Im z \<ge> C}" for z
    using that assms by (auto intro!: derivative_eq_intros simp: power2_eq_square field_simps)
  show "convex {z. Im z \<ge> C}"
    by (simp add: convex_halfspace_Im_ge)
  show "cmod (- 1 / z\<^sup>2) \<le> 1 / C\<^sup>2" if "z \<in> {z. Im z \<ge> C}" for z
  proof -
    from that and assms have [simp]: "z \<noteq> 0"
      by auto
    have "C ^ 2 \<le> Im z ^ 2"
      using assms that by (intro power_mono) auto
    also have "\<dots> \<le> norm z ^ 2"
      unfolding cmod_power2 by simp
    finally show ?thesis
      using assms by (simp add: field_simps norm_divide norm_power)
  qed
qed (use assms in auto)

lemma lipschitz_on_cnj [lipschitz_intros]:
  fixes f::"'a::metric_space \<Rightarrow> complex"
  assumes "C-lipschitz_on U f"
  shows "C-lipschitz_on U (\<lambda>x. cnj (f x))"
proof (rule lipschitz_onI)
  fix x y assume xy: "x \<in> U" "y \<in> U"
  have "dist (cnj (f x)) (cnj (f y)) = norm (cnj (f x) - cnj (f y))"
    by (simp add: dist_norm)
  also have "cnj (f x) - cnj (f y) = cnj (f x - f y)"
    by simp
  also have "norm \<dots> = dist (f x) (f y)"
    by (subst complex_mod_cnj) (auto simp: dist_norm)
  also have "\<dots> \<le> C * dist x y"
    by (rule lipschitz_onD[OF assms]) fact+
  finally show "dist (cnj (f x)) (cnj (f y)) \<le> C * dist x y"
    by (simp add: mult_ac)
qed (use assms lipschitz_on_nonneg in blast)

lemma lipschitz_on_cmult_complex [lipschitz_intros]:
  fixes f::"'a::metric_space \<Rightarrow> complex"
  assumes "C-lipschitz_on U f"
  shows "(norm c * C)-lipschitz_on U (\<lambda>x. c * f x)"
proof (rule lipschitz_onI)
  have "C \<ge> 0"
    using assms lipschitz_on_nonneg by blast
  thus "norm c * C \<ge> 0"
    by simp
next
  fix x y assume xy: "x \<in> U" "y \<in> U"
  have "dist (c * f x) (c * f y) = norm c * dist (f x) (f y)"
    by (metis dist_norm norm_mult vector_space_over_itself.scale_right_diff_distrib)
  also have "\<dots> \<le> norm c * (C * dist x y)"
    by (intro mult_left_mono lipschitz_onD[OF assms]) (use xy in auto)
  finally show "dist (c * f x) (c * f y) \<le> cmod c * C * dist x y"
    by (simp add: mult_ac)
qed

lemma lipschitz_on_cmult_complex' [lipschitz_intros]:
  fixes f::"'a::metric_space \<Rightarrow> complex"
  assumes "C-lipschitz_on U f" "C' \<ge> norm c * C"
  shows "C'-lipschitz_on U (\<lambda>x. c * f x)"
  using lipschitz_on_cmult_complex[OF assms(1), of c] assms(2) lipschitz_on_le by blast

lemma lipschitz_on_cadd_left [lipschitz_intros]:
  fixes f :: "_ \<Rightarrow> 'b :: real_normed_vector"
  assumes "C-lipschitz_on A f"
  shows   "C-lipschitz_on A (\<lambda>x. c + f x)"
proof (rule lipschitz_onI)
  fix x y assume "x \<in> A" "y \<in> A" 
  thus "dist (c + f x) (c + f y) \<le> C * dist x y"
    using lipschitz_onD[OF assms, of x y] by (simp add: dist_norm)
qed (use assms lipschitz_on_nonneg in blast)

lemma lipschitz_on_cadd_right [lipschitz_intros]:
  fixes f :: "_ \<Rightarrow> 'b :: real_normed_vector"
  assumes "C-lipschitz_on A f"
  shows   "C-lipschitz_on A (\<lambda>x. f x + c)"
  by (subst add.commute, rule lipschitz_on_cadd_left [OF assms])


subsection \<open>Homotopy\<close>

lemma simply_connected_imp_homotopic_paths:
  fixes S :: "'a :: real_normed_vector set"
  assumes "simply_connected S" "path p" "path_image p \<subseteq> S" "path q" "path_image q \<subseteq> S"
  assumes "pathstart q = pathstart p \<and> pathfinish q = pathfinish p"
  shows   "homotopic_paths S p q"
  using assms unfolding simply_connected_eq_homotopic_paths by blast

lemma homotopic_loops_part_circlepath_circlepath:
  assumes "b = a + 2 * pi" "sphere x r \<subseteq> A" "r \<ge> 0"
  shows   "homotopic_loops A (part_circlepath x r a b) (circlepath x r)"
proof -
  have "homotopic_loops A (shiftpath' (a / (2 * pi)) (circlepath x r)) (circlepath x r)"
    using assms by (intro homotopic_loops_shiftpath'_left) auto
  also have "shiftpath' (a / (2 * pi)) (circlepath x r) = part_circlepath x r a ((a / pi + 2) * pi)"
    by (simp add: shiftpath'_circlepath)
  also have "(a / pi + 2) * pi = b"
    using assms by (simp add: divide_simps del: div_mult_self3 div_mult_self4 div_mult_self2 div_mult_self1)
  finally show ?thesis .
qed

lemma homotopic_loops_reversepath_D:
  "homotopic_loops A p q \<Longrightarrow> homotopic_loops A (reversepath p) (reversepath q)"
  apply (simp add: homotopic_loops_def homotopic_with_def, clarify)
  apply (rule_tac x="h \<circ> (\<lambda>x. (fst x, 1 - snd x))" in exI)
  apply (rule conjI continuous_intros)+
  apply (auto simp: reversepath_def pathstart_def pathfinish_def elim!: continuous_on_subset)
  done

lemma homotopic_loops_reversepath:
  "homotopic_loops A (reversepath p) (reversepath q) \<longleftrightarrow> homotopic_loops A p q"
  using homotopic_loops_reversepath_D reversepath_reversepath by metis

lemmas [trans] = homotopic_loops_trans

(* TODO: could probably be generalised a lot. But do we still need it? *)
(* TODO unused *)
lemma homotopic_paths_split:
  assumes p: "path p" and A: "path_image p \<subseteq> A"
  assumes a: "a \<in> {0..1}"
  assumes eq1: "\<And>x. x \<in> {0..1} \<Longrightarrow> p1 x = subpath 0 a p x"
  assumes eq2: "\<And>x. x \<in> {0..1} \<Longrightarrow> p2 x = subpath a 1 p x"
  shows   "homotopic_paths A p (p1 +++ p2)"
proof -
  have "homotopic_paths (path_image p) (subpath 0 a p +++ subpath a 1 p) (subpath 0 1 p)"
    by (rule homotopic_join_subpaths) (use a p in auto)
  hence "homotopic_paths (path_image p) (subpath 0 1 p) (subpath 0 a p +++ subpath a 1 p)"
    by (simp add: homotopic_paths_sym_eq)
  also have "homotopic_paths (path_image p) (subpath 0 a p +++ subpath a 1 p) (p1 +++ p2)"
    using assms (* TODO cleanup *)
    apply (intro homotopic_paths_eq)
      apply auto
     apply (subst (asm) path_image_join)
    apply auto
      apply (auto simp: joinpaths_def path_image_def split: if_splits)
      apply (metis (no_types, opaque_lifting) atLeastAtMost_iff image_subset_iff le_numeral_extra(3) path_image_def path_image_subpath_subset zero_less_one_class.zero_le_one)
    apply (metis (full_types) atLeastAtMost_iff image_subset_iff le_numeral_extra(4) path_image_def path_image_subpath_subset zero_less_one_class.zero_le_one)
    done
  also have "subpath 0 1 p = p"
    by simp
  finally show ?thesis
    by (rule homotopic_paths_subset) fact
qed


subsection \<open>Winding numbers\<close>

(*
TODO: update the definition of "winding_number_prop" by incorporating 
      the condition of "path \<gamma>" "z \<notin> path_image \<gamma>" so that the following
      lemma stands unconditionally.
*)
lemma winding_number_comp_plus:
  assumes "path \<gamma>" "z \<notin> path_image \<gamma>"
  shows "winding_number ((+) c \<circ> \<gamma>) (z + c) = winding_number \<gamma> z"
proof (rule winding_number_unique)
  define f where "f = (\<lambda>x. c+x)"
  have f_alt:"f = (\<lambda>x. x+c)" unfolding f_def by auto

  show "\<exists>p. winding_number_prop (f \<circ> \<gamma>)
                (z + c) e p (winding_number \<gamma> z)"
    if "e>0" for e
  proof -
    obtain p where "winding_number_prop \<gamma> z e p (winding_number \<gamma> z)"
      using \<open>0 < e\<close> assms winding_number by blast
    then have p:"valid_path p" "z \<notin> path_image p"
        "pathstart p = pathstart \<gamma>"
        "pathfinish p = pathfinish \<gamma>"
        "(\<forall>t\<in>{0..1}. cmod (\<gamma> t - p t) < e)" and
        p_cont:"contour_integral p (\<lambda>w. 1 / (w - z)) =
          complex_of_real (2 * pi) * \<i> * winding_number \<gamma> z" 
      unfolding winding_number_prop_def by auto
    
    have "valid_path (f \<circ> p)"
      using p(1) unfolding f_def valid_path_translation_eq by simp
    moreover have "z + c \<notin> path_image (f \<circ> p)"
      using p(2) unfolding f_def by (auto simp add:path_image_def)
    moreover have "pathstart (f \<circ> p) = pathstart (f \<circ> \<gamma>)" 
      using p(3) by (simp add:pathstart_compose)
    moreover have "pathfinish (f \<circ> p) = pathfinish (f \<circ> \<gamma>)" 
      using p(4) by (simp add:pathfinish_compose)
    moreover have "(\<forall>t\<in>{0..1}. cmod ((f \<circ> \<gamma>) t 
            - (f \<circ> p) t) < e)" 
      using p(5) unfolding f_def by simp
    moreover have "contour_integral (f \<circ> p) 
              (\<lambda>w. 1 / (w - (z + c))) =
                  complex_of_real (2 * pi) * \<i> * winding_number \<gamma> z"
      unfolding f_alt
      apply (subst contour_integral_affine[where c=1,simplified])
      using p_cont p(1,2) by auto
    ultimately show ?thesis
      apply (rule_tac x="f \<circ> p" in exI)
      unfolding winding_number_prop_def by auto
  qed
  show "path (f \<circ> \<gamma>)"
    using \<open>path \<gamma>\<close> unfolding f_def by (simp add:path_translation_eq)
  show "z + c \<notin> path_image (f \<circ> \<gamma>)"
    using \<open>z \<notin> path_image \<gamma>\<close> unfolding path_image_def f_def by auto
qed

lemma winding_number_comp_times:
  assumes "path \<gamma>"
        and "z \<notin> path_image \<gamma>" 
        and "c \<noteq> 0"
      shows "winding_number ((*) c \<circ> \<gamma>) (z * c) = winding_number \<gamma> z"
proof (rule winding_number_unique)
  define f where "f = (\<lambda>x. c*x)"
  have f_alt:"f = (\<lambda>x. x*c)" unfolding f_def by auto

  show "\<exists>p. winding_number_prop (f \<circ> \<gamma>)
                (z * c) e p (winding_number \<gamma> z)"
    if "e>0" for e
  proof -
    have "cmod c>0" using \<open>c\<noteq>0\<close> by simp
    then have "(1/cmod c) * e>0"
      using that by auto
    from winding_number[OF assms(1,2) this]
    obtain p where "winding_number_prop \<gamma> z ((1/cmod c) * e) 
        p (winding_number \<gamma> z)"
      by blast
    then have p:"valid_path p" "z \<notin> path_image p"
        "pathstart p = pathstart \<gamma>"
        "pathfinish p = pathfinish \<gamma>"
        "(\<forall>t\<in>{0..1}. cmod (\<gamma> t - p t) < ((1/cmod c) * e))" and
        p_cont:"contour_integral p (\<lambda>w. 1 / (w - z)) =
          complex_of_real (2 * pi) * \<i> * winding_number \<gamma> z" 
      unfolding winding_number_prop_def by auto
    
    have "valid_path (f \<circ> p)"
      using p(1) \<open>c\<noteq>0\<close> valid_path_times 
      unfolding f_def by auto
    moreover have "z * c \<notin> path_image (f \<circ> p)"
      using p(2) \<open>c\<noteq>0\<close> unfolding f_def 
      by (auto simp add:path_image_def)
    moreover have "pathstart (f \<circ> p) = pathstart (f \<circ> \<gamma>)" 
      using p(3) by (simp add:pathstart_compose)
    moreover have "pathfinish (f \<circ> p) = pathfinish (f \<circ> \<gamma>)" 
      using p(4) by (simp add:pathfinish_compose)
    moreover have "cmod ((f \<circ> \<gamma>) t - (f \<circ> p) t) < e"
      if "t\<in>{0..1}" for t
    proof -
      have "cmod ((f \<circ> \<gamma>) t - (f \<circ> p) t) = cmod (c*(\<gamma> t - p t))"
        unfolding f_def by (auto simp:algebra_simps)
      also have "\<dots> = cmod c * cmod (\<gamma> t - p t)"
        by (auto simp:norm_mult)
      also have "\<dots> < cmod c * (1 / cmod c * e)"
        using p(5)[rule_format,OF that] \<open>cmod c>0\<close> 
        using mult_less_cancel_left_pos by blast
      also have "\<dots> = e"
        using \<open>cmod c>0\<close> by auto
      finally show ?thesis .
    qed
    moreover have "contour_integral (f \<circ> p)
              (\<lambda>w. 1 / (w - (z * c))) =
          complex_of_real (2 * pi) * \<i> * winding_number \<gamma> z" (is "?L=?R")
    proof -
      have "?L = contour_integral p (\<lambda>w. c / (c * (w - z)))"
        unfolding f_def
        apply (subst contour_integral_affine[where b=0,simplified])
        using p(1,2) \<open>c\<noteq>0\<close> by (auto simp:algebra_simps)
      also have "\<dots> = contour_integral p (\<lambda>w. 1 / ( w - z))"
        using \<open>c\<noteq>0\<close> by simp
      also have "\<dots> = ?R" using p_cont .
      finally show ?thesis .
    qed
    ultimately show ?thesis
      apply (rule_tac x="f \<circ> p" in exI)
      unfolding winding_number_prop_def by auto
  qed
  show "path (f \<circ> \<gamma>)"
    using path_mult[OF path_const \<open>path \<gamma>\<close>] unfolding f_def comp_def
    by simp
  show "z * c \<notin> path_image (f \<circ> \<gamma>)"
    using \<open>z \<notin> path_image \<gamma>\<close> \<open>c\<noteq>0\<close> 
    unfolding path_image_def f_def by auto
qed

lemma winding_number_part_circlepath_full:
  assumes "y \<in> ball x r" "\<alpha> + 2 * pi = \<beta>"
  shows   "winding_number (part_circlepath x r \<alpha> \<beta>) y = 1"
proof -
  have "0 \<le> dist x y"
    by auto
  also have "\<dots> < r"
    using assms by auto
  finally have "r > 0" .
  have "homotopic_loops (-{y}) (part_circlepath x r \<alpha> (\<alpha> + 2 * pi)) (circlepath x r)"
    by (rule homotopic_loops_part_circlepath_circlepath) (use assms \<open>r > 0\<close> in auto)
  hence "winding_number (part_circlepath x r \<alpha> (\<alpha> + 2 * pi)) y = winding_number (circlepath x r) y"
    by (rule winding_number_homotopic_loops)
  also have "\<dots> = 1"
    by (intro winding_number_circlepath) (use assms in \<open>auto simp: dist_norm norm_minus_commute\<close>)
  also have "\<alpha> + 2 * pi = \<beta>"
    using assms(2) by (simp add: algebra_simps)
  finally show ?thesis .
qed

lemma winding_number_part_circlepath_full':
  assumes "y \<in> ball x r" "\<alpha> - 2 * pi = \<beta>"
  shows   "winding_number (part_circlepath x r \<alpha> \<beta>) y = -1"
proof -
  have "0 \<le> dist x y"
    by simp
  also from assms have "dist x y < r"
    by auto
  finally have r: "r > 0"
    by simp
  have "winding_number (part_circlepath x r (\<alpha> - 2 * pi) \<alpha>) y = 1"
    by (rule winding_number_part_circlepath_full) (use assms in auto)
  also have "part_circlepath x r (\<alpha> - 2 * pi) \<alpha> = reversepath (part_circlepath x r \<alpha> (\<alpha> - 2 * pi))"
    by simp
  also have "winding_number \<dots> y = -winding_number (part_circlepath x r \<alpha> (\<alpha> - 2 * pi)) y"
    using path_image_part_circlepath_subset'[of r x \<alpha> "\<alpha> - 2 * pi"] r assms
    by (intro winding_number_reversepath) auto
  also have "\<alpha> - 2 * pi = \<beta>"
    using assms(2) by (simp add: algebra_simps)
  finally show ?thesis
    by Groebner_Basis.algebra
qed

lemma winding_number_inverse_valid_path:
  assumes "valid_path \<gamma>" "0 \<notin> path_image \<gamma>" "z \<notin> path_image \<gamma>" "z \<noteq> 0"
  shows "winding_number (inverse \<circ> \<gamma>) (inverse z) = winding_number \<gamma> z - winding_number \<gamma> 0"
proof -
  define C where "C = 1 / (complex_of_real (2 * pi) * \<i>)"
  have "winding_number (inverse \<circ> \<gamma>) (inverse z)
        = C * contour_integral \<gamma> (\<lambda>w. deriv inverse w / (inverse w - inverse z))"
    unfolding C_def
  proof (rule winding_number_comp[of "UNIV - {0,z}"])
    show "open (UNIV - {0, z})"
      by (metis Diff_insert open_UNIV open_delete)
    show "inverse holomorphic_on UNIV - {0, z}"
      by (auto intro:holomorphic_intros)
    show "path_image \<gamma> \<subseteq> UNIV - {0, z}" "inverse z \<notin> path_image (inverse \<circ> \<gamma>)"
      using \<open>0 \<notin> path_image \<gamma>\<close> \<open>z \<notin> path_image \<gamma>\<close> unfolding path_image_def
      by auto
  qed fact
  also have "\<dots> = C * (contour_integral \<gamma> (\<lambda>w. 1 / (w - z) - 1 / w))"
  proof -
    have "contour_integral \<gamma> (\<lambda>w. deriv inverse w / (inverse w - inverse z)) =
          contour_integral \<gamma> (\<lambda>w. 1 / (w - z) - 1 / w)"
    proof (rule contour_integral_cong)
      fix x assume "x \<in> path_image \<gamma>"
      then have "x\<noteq>0" "x\<noteq>z"
        using \<open>0 \<notin> path_image \<gamma>\<close> \<open>z \<notin> path_image \<gamma>\<close> unfolding path_image_def
        by auto
      then show "deriv inverse x / (inverse x - inverse z) = 1 / (x - z) - 1 / x"
        using \<open>z\<noteq>0\<close>
        by (auto simp:divide_simps power2_eq_square algebra_simps)
    qed simp
    then show ?thesis by simp
  qed
  also have "\<dots> = C * (contour_integral \<gamma> (\<lambda>w. 1 / (w - z)) - contour_integral \<gamma> (\<lambda>w. 1 / w))"
  proof (subst contour_integral_diff)
    show "(\<lambda>w. 1 / (w - z)) contour_integrable_on \<gamma>"
      by (rule contour_integrable_inversediff) fact+
    show "(/) 1 contour_integrable_on \<gamma>"
      using contour_integrable_inversediff[OF \<open>valid_path \<gamma>\<close> \<open>0 \<notin> path_image \<gamma>\<close>]
      by simp
  qed simp
  also have "\<dots> =  winding_number \<gamma> z - winding_number \<gamma> 0"
    unfolding C_def by (subst (1 2) winding_number_valid_path) (use assms in \<open>auto simp: algebra_simps\<close>)
  finally show ?thesis .
qed

lemma winding_number_inverse:
  assumes "path \<gamma>" "path_image \<gamma> \<subseteq> {z. Im z > 0}" "z \<notin> path_image \<gamma>" "Im z > 0"
  shows   "winding_number (inverse \<circ> \<gamma>) (inverse z) = winding_number \<gamma> z - winding_number \<gamma> 0"
proof -
  have compact: "compact (Im ` ({z} \<union> (path_image \<gamma>)))"
    by (intro compact_continuous_image compact_Un compact_path_image assms continuous_intros) auto
  hence bdd: "bdd_below (Im ` ({z} \<union> path_image \<gamma>))"
    by (meson bounded_imp_bdd_below compact_imp_bounded)
  define c' where "c' = Inf (Im ` ({z} \<union> path_image \<gamma>))"
  have c'_le: "Im u \<ge> c'" if "u \<in> {z} \<union> path_image \<gamma>" for u
    using that bdd unfolding c'_def by (meson cINF_lower)
  have "c' \<in> Im ` ({z} \<union> path_image \<gamma>)"
    unfolding c'_def using compact by (intro closed_contains_Inf compact_imp_closed bdd) auto
  with assms have "c' > 0"
    by auto
  define c where "c = c' / 2"
  have "c > 0" "c < c'"
    using \<open>c' > 0\<close> by (simp_all add: c_def)
  have c: "c > 0" "Im z > c" "\<And>u. u \<in> path_image \<gamma> \<Longrightarrow> Im u > c"
    using \<open>c > 0\<close> \<open>c < c'\<close> c'_le by force+

  show ?thesis
  proof (rule winding_number_comp')
    show "inverse holomorphic_on {z. Im z > c}"
      using c by (intro holomorphic_intros) auto
    have "(1/c^2)-lipschitz_on {z. Im z > c} inverse"
      by (rule lipschitz_on_subset[OF lipschitz_on_complex_inverse[of c]]) (use c in auto)
    thus "uniformly_continuous_on {z. c < Im z} inverse"
      by (rule lipschitz_on_uniformly_continuous)
    show "inj_on inverse {z. Im z > c}"
      using assms by (auto simp: inj_on_def)
    show "open {z. Im z > c}"
      by (simp add: open_halfspace_Im_gt)
    show "path \<gamma>" "path_image \<gamma> \<subseteq> {z. Im z > c}" "z \<in> {z. c < Im z}" "z \<notin> path_image \<gamma>"
      using c assms by auto
    have "\<forall>\<^sub>F p in valid_path_nhds \<gamma>. valid_path p \<and> path_image p \<inter> ({z. Im z \<le> c} \<union> {z}) = {}"
      by (intro eventually_conj eventually_valid_path_valid_path_nhds
                eventually_valid_path_nhds_avoid closed_Un closed_halfspace_Im_le)
         (use assms c in force)+
    moreover have "\<forall>\<^sub>F p in path_nhds \<gamma>. winding_number p 0 = winding_number \<gamma> 0 \<and>
                               winding_number p z = winding_number \<gamma> z"
      by (intro eventually_conj eventually_winding_number_eq_path_nhds) (use assms in auto)
    hence "\<forall>\<^sub>F p in valid_path_nhds \<gamma>. winding_number p 0 = winding_number \<gamma> 0 \<and>
                                      winding_number p z = winding_number \<gamma> z"
      by (meson filter_leD path_nhds_le_valid_path_nhds)
    ultimately have "\<forall>\<^sub>F p in valid_path_nhds \<gamma>.
            contour_integral p (\<lambda>w. deriv inverse w / (inverse w - inverse z)) =
            complex_of_real (2 * pi) * \<i> * (winding_number \<gamma> z - winding_number \<gamma> 0)"
    proof eventually_elim
      case (elim p)
      have "contour_integral p (\<lambda>w. deriv inverse w / (inverse w - inverse z)) =
            contour_integral p (\<lambda>w. 1 / (w - z) - 1 / w)"
      proof (rule contour_integral_cong)
        fix x assume "x \<in> path_image p"
        then have "x \<noteq> 0" "x \<noteq> z"
          using elim c by auto
        then show "deriv inverse x / (inverse x - inverse z) = 1 / (x - z) - 1 / x"
          using assms by (auto simp: divide_simps power2_eq_square)
      qed simp
      also have "\<dots> = contour_integral p (\<lambda>w. 1 / (w - z)) - contour_integral p ((/) 1)"
      proof (rule contour_integral_diff)
        show "(\<lambda>w. 1 / (w - z)) contour_integrable_on p"
          by (rule contour_integrable_inversediff) (use elim in auto)
        have "(\<lambda>w. 1 / (w - 0)) contour_integrable_on p"
          by (rule contour_integrable_inversediff) (use elim c in auto)
        thus "(\<lambda>w. 1 / w) contour_integrable_on p"
          by simp
      qed
      also have "\<dots> = (2 * pi * \<i>) * (winding_number p z - winding_number p 0)"
        by (subst (1 2) winding_number_valid_path) (use elim c in \<open>auto simp: algebra_simps\<close>)
      finally show ?case
        using elim by (simp add: algebra_simps)
    qed
    thus "\<exists>\<^sub>F p in valid_path_nhds \<gamma>.
            contour_integral p (\<lambda>w. deriv inverse w / (inverse w - inverse z)) =
            complex_of_real (2 * pi) * \<i> * (winding_number \<gamma> z - winding_number \<gamma> 0)"
      by (rule eventually_frequently [rotated]) (use assms in auto)
  qed
qed

lemma winding_number_inverse_valid_path_0:
  assumes "valid_path \<gamma>" "pathstart \<gamma> = pathfinish \<gamma>" "0 \<notin> path_image \<gamma>"
  shows   "winding_number (inverse \<circ> \<gamma>) 0 = -winding_number \<gamma> 0"
proof -
  have val: "valid_path (inverse \<circ> \<gamma>)" using assms
    by (intro valid_path_compose_holomorphic[of _ _ "-{0}"] assms)
       (auto intro!: holomorphic_intros)

  obtain B where B: "\<And>w. norm w \<ge> B \<Longrightarrow> winding_number \<gamma> w = 0"
    using winding_number_zero_at_infinity[of \<gamma>] val assms
    by (auto simp: valid_path_imp_path)

  have "compact (path_image \<gamma> \<union> path_image (inverse \<circ> \<gamma>))"
    using assms by (intro compact_Un compact_path_image valid_path_imp_path val) auto
  hence "open (-(path_image \<gamma> \<union> path_image (inverse \<circ> \<gamma>)))"
    by (intro open_Compl compact_imp_closed)
  moreover have "0 \<in> -(path_image \<gamma> \<union> path_image (inverse \<circ> \<gamma>))"
    using assms by (auto simp: path_image_compose)
  ultimately obtain \<epsilon> where \<epsilon>: "\<epsilon> > 0" "cball 0 \<epsilon> \<subseteq> -(path_image \<gamma> \<union> path_image (inverse \<circ> \<gamma>))"
    unfolding open_contains_cball by blast
  define w where "w = complex_of_real (min \<epsilon> (1 / max 1 B))"

  have pos: "min \<epsilon> (1 / max 1 B) > 0"
    using \<epsilon> by (auto simp: min_less_iff_disj)
  hence norm_w: "norm w = min \<epsilon> (1 / max 1 B)"
    unfolding w_def norm_of_real by simp
  from pos have "norm w \<noteq> 0"
    unfolding norm_w by linarith
  hence "w \<noteq> 0"
    by auto
  have "w \<in> cball 0 \<epsilon>"
    by (auto simp: norm_w)

  have "B \<le> max 1 B"
    by simp
  also have "max 1 B = 1 / (1 / max 1 B)"
    by (auto simp: field_simps)
  also have "\<dots> \<le> 1 / min \<epsilon> (1 / max 1 B)"
    using \<epsilon> by (intro divide_left_mono) auto
  also have "\<dots> = norm (inverse w)"
    by (simp add: \<open>norm w = _\<close> norm_inverse field_simps norm_divide)
  finally have "B \<le> norm (inverse w)" .

  have "w \<notin> inverse ` path_image \<gamma>"
    using \<open>w \<in> cball 0 \<epsilon>\<close> \<epsilon> unfolding path_image_compose by blast
  hence "inverse w \<notin> path_image \<gamma>"
    using \<open>w \<noteq> 0\<close> by (metis image_iff inverse_inverse_eq)

  have "winding_number (inverse \<circ> \<gamma>) 0 = winding_number (inverse \<circ> \<gamma>) w"
  proof (rule winding_number_eq)
    show "w \<in> cball 0 \<epsilon>" "0 \<in> cball 0 \<epsilon>" "cball 0 \<epsilon> \<inter> path_image (inverse \<circ> \<gamma>) = {}"
         "connected (cball 0 \<epsilon> :: complex set)"
      using \<epsilon> by (auto simp: w_def)
  qed (use assms val in \<open>auto intro: valid_path_imp_path simp: pathfinish_def pathstart_def\<close>)
  also have "winding_number (inverse \<circ> \<gamma>) w = winding_number (inverse \<circ> \<gamma>) (inverse (inverse w))"
    using \<open>w \<noteq> 0\<close> by simp
  also have "\<dots> = winding_number \<gamma> (inverse w) - winding_number \<gamma> 0"
    using assms \<open>w \<in> cball 0 \<epsilon>\<close> \<open>w \<noteq> 0\<close> \<epsilon> \<open>inverse w \<notin> path_image \<gamma>\<close>
    by (subst winding_number_inverse_valid_path) (auto simp: path_image_compose)
  also have "winding_number \<gamma> (inverse w) = 0"
    using \<epsilon> \<open>B \<le> norm (inverse w)\<close> by (intro B)
  finally show ?thesis by (simp add: o_def)
qed

text \<open>
  The following allows us to compute the winding number of a non-closed circular arc with
  respect to its centre.
\<close>
lemma winding_number_part_circlepath_centre:
  assumes "r > 0"
  shows   "winding_number (part_circlepath z r a b) z = (b - a) / (2 * pi)"
proof -
  have "winding_number (part_circlepath 0 r a b) 0 = (b - a) / (2 * pi)"
  proof (induction a b rule: linorder_wlog)
    case (le a b)
    show ?case
    proof (cases "a = b")
      case True
      thus ?thesis
        using assms by (simp add: part_circlepath_empty winding_number_zero_const)
    next
      case False
      let ?p = "part_circlepath 0 r a b"
      have "((\<lambda>t. \<i>) has_integral (b - a) *\<^sub>R \<i>) {a..b}"
        using has_integral_const[of \<i> a b] assms False le by (simp add: scaleR_conv_of_real mult_ac)
      hence "((\<lambda>z. 1 / z) has_contour_integral (b - a) *\<^sub>R \<i>) ?p"
        by (subst has_contour_integral_part_circlepath_iff) (use assms False le in simp_all)
      moreover have "0 \<notin> path_image ?p"
        using assms by (auto simp: path_image_part_circlepath')
      hence "((\<lambda>z. 1 / z) has_contour_integral 2 * \<i> * pi * winding_number ?p 0) ?p"
        using has_contour_integral_winding_number[of ?p 0] assms by (auto simp add: mult_ac)
      ultimately have "(b - a) *\<^sub>R \<i> = 2 * \<i> * pi * winding_number ?p 0"
        using has_contour_integral_unique by blast
      thus ?thesis
        by (simp add: scaleR_conv_of_real)
    qed
  next
    case (sym a b)
    from assms have "0 \<notin> path_image (part_circlepath 0 r a b)"
      by (auto simp: path_image_part_circlepath')
    thus ?case using assms sym
      by (simp add: reversepath_part_circlepath [symmetric, of 0 r b a]
                    winding_number_reversepath field_simps del: reversepath_part_circlepath)
  qed
  hence "winding_number ((+) z \<circ> part_circlepath 0 r a b) (0 + z) = (b - a) / (2 * pi)"
    by (subst winding_number_comp_plus) (use assms in \<open>auto simp: path_image_part_circlepath'\<close>)
  thus ?thesis
    by (subst (asm) part_circlepath_translate) auto
qed


subsection \<open>Continuous transformations that preserve the winding number in some way\<close>

locale winding_preserving =
  fixes A :: "complex set" and f :: "complex \<Rightarrow> complex" and g :: "complex \<Rightarrow> complex"
  assumes inj: "inj_on f A"
  assumes cont: "continuous_on A f"
  assumes winding_number_eq:
    "\<And>p x. path p \<Longrightarrow> path_image p \<subseteq> A \<Longrightarrow> pathstart p = pathfinish p \<Longrightarrow> x \<in> A - path_image p \<Longrightarrow>
        winding_number (f \<circ> p) (f x) = g (winding_number p x)"

lemma winding_preserving_comp:
  assumes "winding_preserving B f2 g2"
  assumes "winding_preserving A f1 g1"
  assumes subset: "f1 ` A \<subseteq> B"
  shows   "winding_preserving A (f2 \<circ> f1) (g2 \<circ> g1)"
proof
  interpret f1: winding_preserving A f1 g1
    by fact
  interpret f2: winding_preserving B f2 g2
    by fact
  show "inj_on (f2 \<circ> f1) A"
    by (intro comp_inj_on f1.inj inj_on_subset[OF f2.inj] assms)
  show "continuous_on A (f2 \<circ> f1)"
    by (intro continuous_on_compose f1.cont continuous_on_subset[OF f2.cont] subset)
  show "winding_number (f2 \<circ> f1 \<circ> p) ((f2 \<circ> f1) x) = (g2 \<circ> g1) (winding_number p x)"
    if p: "path p" "path_image p \<subseteq> A" "x \<in> A - path_image p" "pathstart p = pathfinish p" for p x
  proof -
    have [simp]: "f1 x = f1 (p t) \<longleftrightarrow> x = p t" if "t \<in> {0..1}" for t
      using f1.inj that p unfolding inj_on_def path_image_def by blast
    have "winding_number (f2 \<circ> f1 \<circ> p) ((f2 \<circ> f1) x) =
          winding_number (f2 \<circ> (f1 \<circ> p)) (f2 (f1 x))"
      by (simp add: o_def)
    also have "\<dots> = g2 (winding_number (f1 \<circ> p) (f1 x))"
    proof (rule f2.winding_number_eq)
      show "path (f1 \<circ> p)"
        using that by (intro path_continuous_image continuous_on_subset[OF f1.cont])
      show "path_image (f1 \<circ> p) \<subseteq> B"
        using that subset by (auto simp: path_image_def)
      show "f1 x \<in> B - path_image (f1 \<circ> p)"
        using that subset f1.inj by (auto simp: path_image_def)
    qed (use p in \<open>auto simp: pathstart_compose pathfinish_compose\<close>)
    also have "winding_number (f1 \<circ> p) (f1 x) = g1 (winding_number p x)"
      by (rule f1.winding_number_eq) (use p in auto)
    finally show ?thesis
      by (simp add: o_def)
  qed
qed

lemmas winding_preserving_comp' = winding_preserving_comp [unfolded o_def]

lemma winding_preserving_subset:
  assumes "winding_preserving A f g" "B \<subseteq> A"
  shows   "winding_preserving B f g"
proof -
  interpret winding_preserving A f g
    by fact
  show ?thesis
  proof
    show "inj_on f B"
      by (rule inj_on_subset[OF inj]) (use assms(2) in auto)
    show "continuous_on B f"
      by (rule continuous_on_subset[OF cont]) (use assms(2) in auto)
    show "winding_number (f \<circ> p) (f x) = g (winding_number p x)"
      if "path p" "path_image p \<subseteq> B" "x \<in> B - path_image p" "pathstart p = pathfinish p" for p x
      using that winding_number_eq[of p x] assms(2) by auto
  qed
qed

lemma winding_preserving_translate: "winding_preserving A (\<lambda>x. c + x) (\<lambda>x. x)"
proof
  show "winding_number ((+) c \<circ> p) (c + x) = winding_number p x"
    if "path p" "path_image p \<subseteq> A" "x \<in> A - path_image p" for p x
    using that winding_number_comp_plus[of p x c] by (auto simp: algebra_simps)
qed (auto intro!: inj_onI continuous_intros)

lemma winding_preserving_mult: "c \<noteq> 0 \<Longrightarrow> winding_preserving A (\<lambda>x. c * x) (\<lambda>x. x)"
proof
  assume "c \<noteq> 0"
  show "winding_number ((*) c \<circ> p) (c * x) = winding_number p x"
    if "path p" "path_image p \<subseteq> A" "x \<in> A - path_image p" for p x
    using that winding_number_comp_times[of p x c] \<open>c \<noteq> 0\<close> by (auto simp: algebra_simps)
qed (auto intro!: inj_onI continuous_intros)

lemma winding_preserving_cnj: "winding_preserving A cnj (\<lambda>x. -cnj x)"
proof
  show "winding_number (cnj \<circ> p) (cnj x) = -cnj (winding_number p x)"
    if "path p" "path_image p \<subseteq> A" "x \<in> A - path_image p" for p x
    using that winding_number_cnj[of p x] by (auto simp: algebra_simps)
qed (auto intro!: inj_onI continuous_intros)

lemma winding_preserving_uminus: "winding_preserving A (\<lambda>x. -x) (\<lambda>x. x)"
  using winding_preserving_mult[of "-1" A] by simp



subsection \<open>Paths\<close>

lemma simple_path_cnj [simp]: "simple_path (cnj \<circ> p) \<longleftrightarrow> simple_path p"
  by (rule simple_path_linear_image_eq) (auto intro!: linear_cnj simp: inj_def)

lemma part_circlepath_cnj': "cnj \<circ> part_circlepath c r a b = part_circlepath (cnj c) r (-a) (-b)"
  unfolding o_def by (intro ext part_circlepath_cnj)

lemma linepath_minus: "linepath (-a) (-b) x = -linepath a b x"
  by (simp add: linepath_def algebra_simps)

text \<open>
  The following lemma is very difficult to bypass some nasty geometric reasoning:
  If a path only touches the frontier of a set at its beginning or end,
  then it is either fully inside the set or fully outside the set.
\<close>
lemma path_fully_inside_or_fully_outside:
  fixes p :: "real \<Rightarrow> 'a :: euclidean_space"
  assumes "path p" "\<And>x. x \<in> {0<..<1} \<Longrightarrow> p x \<notin> frontier A"
  shows   "path_image p \<subseteq> closure A \<or> path_image p \<inter> interior A = {}"
proof (rule ccontr)
  assume *: "\<not>(path_image p \<subseteq> closure A \<or> path_image p \<inter> interior A = {})"
  from * obtain x y where xy: "x \<in> {0..1}" "y \<in> {0..1}" "p x \<notin> closure A" "p y \<in> interior A"
    unfolding path_image_def by blast
  define x' y' where "x' = min x y" and "y' = max x y"
  have xy': "x' \<in> {0..1}" "y' \<in> {0..1}" "x' \<le> y'"
    using xy by (auto simp: x'_def y'_def)

  define q where "q = subpath x' y' p"
  have [simp]: "path q"
    using xy' by (auto simp: q_def assms)

  have "path_image q \<inter> frontier A \<noteq> {}"
  proof (rule connected_Int_frontier)
    show "connected (path_image q)"
      by auto
  next
    have "q (if x \<le> y then 0 else 1) \<in> path_image q"
      by (auto simp: path_image_def)
    moreover have "q (if x \<le> y then 0 else 1) \<notin> A"
      using xy closure_subset by (auto simp: q_def subpath_def x'_def y'_def)
    ultimately show "path_image q - A \<noteq> {}"
      by blast
  next
    have "q (if x \<le> y then 1 else 0) \<in> path_image q"
      by (auto simp: path_image_def)
    moreover have "q (if x \<le> y then 1 else 0) \<in> A"
      using xy interior_subset by (auto simp: q_def subpath_def x'_def y'_def)
    ultimately show "path_image q \<inter> A \<noteq> {}"
      by blast
  qed
  then obtain w where w: "w \<in> {x'..y'}" "p w \<in> frontier A"
    unfolding q_def path_image_subpath using xy' by (force split: if_splits)

  have "w \<noteq> x"
    using xy w by (metis DiffE frontier_def)
  moreover have "w \<noteq> y"
    using xy w unfolding frontier_def by auto
  ultimately have "w \<in> {x'<..<y'}"
    using w(1) by (auto simp: x'_def y'_def)
  also have "\<dots> \<subseteq> {0<..<1}"
    using xy' by auto
  finally have "w \<in> {0<..<1}" .
  with assms(2)[of w] have "p w \<notin> frontier A"
    by blast
  with \<open>p w \<in> frontier A\<close> show False
    by contradiction
qed

lemma simple_path_joinE':
  assumes "simple_path (g1 +++ g2)" and "pathfinish g1 = pathstart g2"
  shows   "path_image g1 \<inter> path_image g2 \<subseteq> 
             (insert (pathstart g2) (if pathstart g1 = pathfinish g2 then {pathstart g1} else {}))"
  using assms
  by (smt (verit, del_insts) arc_join_eq insert_commute pathfinish_join pathstart_join simple_path_cases simple_path_joinE)

lemma simple_path_joinE'':
  assumes "simple_path (g1 +++ g2)" and "pathfinish g1 = pathstart g2"
          "x \<in> path_image g1" "x \<in> path_image g2"
  shows   "x = pathstart g2 \<or> x = pathfinish g2 \<and> pathstart g1 = pathfinish g2"
  using simple_path_joinE'[OF assms(1,2)] assms(3,4) by (auto split: if_splits)
  
lemma arc_continuous_image:
  assumes "arc p" "inj_on f (path_image p)" "continuous_on (path_image p) f"
  shows   "arc (f \<circ> p)"
  using assms by (auto simp: arc_def inj_on_def path_image_def intro!: path_continuous_image)

lemma eventually_path_image_cball_subset:
  fixes p :: "real \<Rightarrow> 'a :: real_normed_vector"
  assumes "path p" "path_image p \<subseteq> interior A"
  shows "eventually (\<lambda>\<epsilon>. (\<Union>x\<in>path_image p. cball x \<epsilon>) \<subseteq> A) (at_right 0)"
proof -
  from assms have "compact ( path_image p)"
    by (intro compact_path_image) auto
  moreover have "path_image p \<inter> frontier A = {}"
    using assms by (simp add: disjoint_iff frontier_def subset_eq)
  ultimately have "eventually (\<lambda>\<epsilon>. setdist_gt \<epsilon> (path_image p) (frontier A)) (at_right 0)"
    by (intro compact_closed_imp_eventually_setdist_gt_at_right_0) auto
  moreover have "eventually (\<lambda>\<epsilon>. \<epsilon> > 0) (at_right (0 :: real))"
    by (simp add: eventually_at_right_less)
  ultimately have "eventually (\<lambda>\<epsilon>. (\<Union>x\<in>path_image p. cball x \<epsilon>) \<subseteq> A) (at_right 0)"
  proof eventually_elim
    case (elim \<epsilon>)
    show "(\<Union>x\<in>path_image p. cball x \<epsilon>) \<subseteq> A"
    proof (intro subsetI, elim UN_E)
      fix x y assume xy: "x \<in> path_image p" "y \<in> cball x \<epsilon>"
      show "y \<in> A"
      proof (rule ccontr)
        assume "y \<notin> A"
        have "cball x \<epsilon> \<inter> frontier A \<noteq> {}"
        proof (rule connected_Int_frontier)
          have "x \<in> cball x \<epsilon>"
            using \<open>\<epsilon> > 0\<close> by simp
          moreover have "x \<in> A"
            using \<open>x \<in> path_image p\<close> assms interior_subset by blast
          ultimately show "cball x \<epsilon> \<inter> A \<noteq> {}"
            by blast
        next
          from xy show "cball x \<epsilon> - A \<noteq> {}"
            using \<open>y \<notin> A\<close> by blast
        qed auto
        hence "\<not>setdist_gt \<epsilon> {x} (frontier A)"
          by (force simp: setdist_gt_def)
        moreover have "setdist_gt \<epsilon> {x} (frontier A)"
          by (rule setdist_gt_mono[OF elim(1)]) (use xy in auto)
        ultimately show False by contradiction
      qed
    qed
  qed
  thus ?thesis
    by eventually_elim (use assms interior_subset in auto)
qed

lemma eventually_path_image_cball_subset':
  fixes p :: "real \<Rightarrow> 'a :: real_normed_vector"
  assumes "path p" "path_image p \<subseteq> interior A" "X \<subseteq> path_image p"
  shows "eventually (\<lambda>\<epsilon>. path_image p \<union> (\<Union>x\<in>X. cball x \<epsilon>) \<subseteq> A) (at_right 0)"
  using eventually_path_image_cball_subset[OF assms(1-2)]
        eventually_at_right_less[of 0]
proof eventually_elim
  case (elim \<epsilon>)
  have "path_image p \<union> (\<Union>x\<in>X. cball x \<epsilon>) = (\<Union>x\<in>path_image p. {x}) \<union> (\<Union>x\<in>X. cball x \<epsilon>)"
    by blast
  also have "\<dots> \<subseteq> (\<Union>x\<in>path_image p. cball x \<epsilon>) \<union> (\<Union>x\<in>X. cball x \<epsilon>)"
    using elim(2) by (intro Un_mono UN_mono) auto
  also have "\<dots> = (\<Union>x\<in>path_image p \<union> X. cball x \<epsilon>)"
    by blast
  also have "path_image p \<union> X = path_image p"
    using assms by blast
  also have "(\<Union>x\<in>path_image p. cball x \<epsilon>) \<subseteq> A"
    by fact
  finally show ?case .
qed

(* TODO: better name? *)
text \<open>
  We say that a path does not cross a set \<open>A\<close> if it enters \<open>A\<close> at most at its beginning and
  end, and never inbetween.
\<close>
definition does_not_cross :: "(real \<Rightarrow> 'a :: real_vector) \<Rightarrow> 'a set \<Rightarrow> bool" where
  "does_not_cross p A \<longleftrightarrow> (\<forall>x\<in>{0<..<1}. p x \<notin> A)"

lemma does_not_cross_simple_path:
  assumes "simple_path p"
  shows   "does_not_cross p A \<longleftrightarrow> path_image p \<inter> A \<subseteq> {pathstart p, pathfinish p}"
proof
  assume "does_not_cross p A"
  thus "path_image p \<inter> A \<subseteq> {pathstart p, pathfinish p}" using assms
    by (force simp: does_not_cross_def simple_path_def path_image_def pathstart_def pathfinish_def)
next
  assume *: "path_image p \<inter> A \<subseteq> {pathstart p, pathfinish p}"
  show "does_not_cross p A"
    unfolding does_not_cross_def
  proof safe
    fix x :: real assume x: "x \<in> {0<..<1}" "p x \<in> A"
    hence "p x \<notin> {pathstart p, pathfinish p}"
      using assms by (force simp: simple_path_def loop_free_def pathstart_def pathfinish_def)+
    moreover from x have "p x \<in> path_image p"
      by (auto simp: path_image_def)
    ultimately show False
      using * and x by blast
  qed
qed

lemma path_fully_inside_or_fully_outside':
  fixes p :: "real \<Rightarrow> 'a :: euclidean_space"
  assumes "path p" "does_not_cross p (frontier A)"
  shows   "path_image p \<subseteq> closure A \<or> path_image p \<inter> interior A = {}"
  using path_fully_inside_or_fully_outside[OF assms(1), of A] assms unfolding does_not_cross_def
  by auto

lemma in_path_image_part_circlepathI:
  assumes "y = x + rcis r u" "u \<in> closed_segment a b"
  shows   "y \<in> path_image (part_circlepath x r a b)"
proof -
  have "u \<in> path_image (linepath a b)"
    using assms by simp
  then obtain v where v: "v \<in> {0..1}" "u = linepath a b v"
    unfolding path_image_def by blast
  have "y = part_circlepath x r a b v"
    by (simp add: part_circlepath_altdef v assms)
  with v(1) show ?thesis
    unfolding path_image_def by blast
qed

lemma in_path_image_part_circlepathI':
  assumes "Arg (y - x) \<in> closed_segment a b" "dist y x = r"
  shows   "y \<in> path_image (part_circlepath x r a b)"
proof (rule in_path_image_part_circlepathI)
  show "y = x + rcis r (Arg (y - x))"
    using assms
    by (cases "x = y")
       (auto simp: rcis_def cis_Arg complex_sgn_def dist_commute scaleR_conv_of_real
                   field_simps dist_norm norm_minus_commute)
qed fact

lemma path_image_part_circlepath':
  "path_image (part_circlepath x r a b) = (\<lambda>t. x + rcis r t) ` closed_segment a b"
proof -
  have "path_image (part_circlepath x r a b) = (\<lambda>t. x + rcis r t) ` path_image (linepath a b)"
    by (simp add: path_image_def part_circlepath_altdef image_image)
  thus ?thesis
    by simp
qed

lemma path_image_part_circlepath:
  assumes "a \<in> {-pi<..pi}" "b \<in> {-pi<..pi}" "r > 0"
  shows   "path_image (part_circlepath x r a b) = {y\<in>sphere x r. Arg (y - x) \<in> closed_segment a b}"
proof safe
  fix y assume y: "y \<in> path_image (part_circlepath x r a b)"
  show "y \<in> sphere x r"
    using y path_image_part_circlepath_subset'[of r x a b] assms by auto

  from y obtain u where u: "u \<in> {0..1}" "y = part_circlepath x r a b u"
    by (auto simp: path_image_def)
  have "linepath a b u \<in> closed_segment a b"
    using linepath_in_path u(1) by blast
  also have "\<dots> \<subseteq> {-pi<..pi}"
    using assms by (intro closed_segment_subset) auto
  finally have *: "linepath a b u \<in> {-pi<..pi}" .

  have "Arg (y - x) = Arg (rcis r (linepath a b u))"
    by (simp add: u part_circlepath_altdef)
  also have "\<dots> = linepath a b u"
    using * assms by (subst Arg_rcis) auto
  also have "\<dots> \<in> closed_segment a b"
    by fact
  finally show "Arg (y - x) \<in> closed_segment a b" .
next
  fix y assume y: "y \<in> sphere x r" "Arg (y - x) \<in> closed_segment a b"
  show "y \<in> path_image (part_circlepath x r a b)"
    using y by (intro in_path_image_part_circlepathI') (auto simp: dist_commute)
qed

lemma path_image_part_circlepath_mono:
  assumes "min a' b' \<le> min a b" "max a' b' \<ge> max a b"
  shows   "path_image (part_circlepath x r a b) \<subseteq> path_image (part_circlepath x r a' b')"
proof -
  have "path_image (part_circlepath x r a b) = (\<lambda>t. x + rcis r t) ` path_image (linepath a b)"
    by (simp add: path_image_def part_circlepath_altdef image_image)
  also have "\<dots> \<subseteq> (\<lambda>t. x + rcis r t) ` path_image (linepath a' b')"
    unfolding path_image_linepath using assms
    by (intro image_mono) (auto simp: closed_segment_eq_real_ivl split: if_splits)
  also have "\<dots> = path_image (part_circlepath x r a' b')"
    by (simp add: path_image_def part_circlepath_altdef image_image)
  finally show ?thesis .
qed


subsection \<open>Topology\<close>

lemma eventually_at_within_in_open:
  assumes "open X" "x \<in> X"
  shows   "eventually (\<lambda>z. z \<in> X \<inter> A - {x}) (at x within A)"
  using eventually_nhds_in_open[OF assms] unfolding eventually_at_filter
  by eventually_elim auto

lemma filterlim_at_withinD:
  assumes "filterlim f (at L within A) F" "open X" "L \<in> X"
  shows   "eventually (\<lambda>x. f x \<in> X \<inter> A - {L}) F"
proof -
  have "eventually (\<lambda>z. z \<in> X \<inter> A - {L}) (at L within A)"
    by (rule eventually_at_within_in_open) (use assms in auto)
  moreover from assms(1) have "filtermap f F \<le> at L within A"
    unfolding filterlim_def .
  ultimately have "eventually (\<lambda>z. z \<in> X \<inter> A - {L}) (filtermap f F)"
    unfolding le_filter_def by blast
  thus ?thesis
    by (simp add: eventually_filtermap)
qed

lemma filterlim_at_withinD':
  assumes "filterlim f (at L within A) F" "open X" "L \<in> X"
  shows   "eventually (\<lambda>x. f x \<in> X \<inter> A) F"
  using filterlim_at_withinD[OF assms] by eventually_elim auto

lemma filterlim_at_rightD:
  assumes "filterlim f (at_right L) F" "a > L"
  shows   "eventually (\<lambda>x. f x \<in> {L<..<a}) F"
  using filterlim_at_withinD'[OF assms(1), of "{..<a}"] assms(2)
  by (auto elim!: eventually_mono)

lemma filterlim_at_leftD:
  assumes "filterlim f (at_left L) F" "a < L"
  shows   "eventually (\<lambda>x. f x \<in> {a<..<L}) F"
  using filterlim_at_withinD'[OF assms(1), of "{a<..}"] assms(2)
  by (auto elim!: eventually_mono)

lemma eventually_Ball_at_right_0_real:
  assumes "eventually P (at_right (0 :: real))"
  shows   "eventually (\<lambda>x. \<forall>y\<in>{0<..x}. P y) (at_right 0)"
  using assms unfolding eventually_at_right_field by force   

lemma open_segment_same_Re:
  assumes "Re a = Re b"
  shows   "open_segment a b = {z. Re z = Re a \<and> Im z \<in> open_segment (Im a) (Im b)}"
  using assms by (auto simp: open_segment_def closed_segment_same_Re complex_eq_iff)

lemma open_segment_same_Im:
  assumes "Im a = Im b"
  shows   "open_segment a b = {z. Im z = Im a \<and> Re z \<in> open_segment (Re a) (Re b)}"
  using assms by (auto simp: open_segment_def closed_segment_same_Im complex_eq_iff)

lemma interior_halfspace_Re_ge [simp]: "interior {z. Re z \<ge> x} = {z. Re z > x}"
  and interior_halfspace_Re_le [simp]: "interior {z. Re z \<le> x} = {z. Re z < x}"
  and interior_halfspace_Im_ge [simp]: "interior {z. Im z \<ge> x} = {z. Im z > x}"
  and interior_halfspace_Im_le [simp]: "interior {z. Im z \<le> x} = {z. Im z < x}"
  using interior_halfspace_ge[of "1::complex" x] interior_halfspace_le[of "1::complex" x]
        interior_halfspace_ge[of \<i> x] interior_halfspace_le[of \<i> x]
  by (simp_all add: inner_complex_def)

thm arc_def
thm simple_path_def

end
