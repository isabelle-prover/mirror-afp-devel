section \<open>Connection between complex lattices and theta functions\<close>
theory Complex_Lattices_Theta
  imports Weierstrass_Sigma_Zeta "Theta_Functions.Theta_Nullwert"
begin

(* TODO Move. Or rather, fix whatever causes these problems. *)
lemmas [simp del] = div_mult_self1 div_mult_self2 div_mult_self3 div_mult_self4

unbundle jacobi_theta_nw_notation


text \<open>
  We make the connection to theta functions. In order to do that, we first assume that the
  generators $\omega_1$ and $\omega_2$ are such that their ratio $\tau := \omega_2/\omega_1$ has
  positive imaginary part.
\<close>
locale complex_lattice_Im_pos = complex_lattice +
  assumes Im_ratio_pos: "Im ratio > 0"
begin

text \<open>
  We fix this ratio $\tau$ as the second parameter of the theta functions so that the theta
  functions become quasi-elliptic functions in one variable $z$.
\<close>
definition theta_00 ("(\<open>notation=\<open>mixfix complex_lattice_Im_pos.theta_00\<close>\<close>\<theta>\<^sub>0\<^sub>0'(_'))")
  where "theta_00 z \<equiv> jacobi_theta_00 (z / \<omega>1) \<tau>"

definition theta_01 ("(\<open>notation=\<open>mixfix complex_lattice_Im_pos.theta_00\<close>\<close>\<theta>\<^sub>0\<^sub>1'(_'))")
  where "theta_01 z \<equiv> jacobi_theta_01 (z / \<omega>1) \<tau>"

definition theta_10 ("(\<open>notation=\<open>mixfix complex_lattice_Im_pos.theta_00\<close>\<close>\<theta>\<^sub>1\<^sub>0'(_'))")
  where "theta_10 z \<equiv> jacobi_theta_10 (z / \<omega>1) \<tau>"

definition theta_11 ("(\<open>notation=\<open>mixfix complex_lattice_Im_pos.theta_00\<close>\<close>\<theta>\<^sub>1\<^sub>1'(_'))")
  where "theta_11 z \<equiv> jacobi_theta_11 (z / \<omega>1) \<tau>"

lemma theta_01_conv_00: "theta_01 z = theta_00 (z + \<omega>1 / 2)"
  by (simp add: theta_01_def jacobi_theta_01_def theta_00_def add_divide_distrib)

lemma theta_10_conv_00: "theta_10 z = to_nome (z / \<omega>1 + \<tau> / 4) * theta_00 (z + \<omega>2 / 2)"
  by (simp add: theta_10_def jacobi_theta_10_def theta_00_def add_divide_distrib ratio_def mult_ac)

lemma theta_11_conv_00:
  "theta_11 z = to_nome (z / \<omega>1 + \<tau> / 4 + 1 / 2) * theta_00 (z + (\<omega>1 + \<omega>2) / 2)"
  by (simp add: theta_11_def jacobi_theta_11_def theta_00_def add_divide_distrib
                ratio_def algebra_simps)

text \<open>
  The four zeta functions then each have their zeros at various lattice or half-lattice points.
\<close>
lemma theta_00_eq_0_iff: "\<theta>\<^sub>0\<^sub>0(z) = 0 \<longleftrightarrow> rel z ((\<omega>1 + \<omega>2) / 2)" for z
proof
  assume "\<theta>\<^sub>0\<^sub>0(z) = 0"
  then obtain m n :: int where "z / \<omega>1 = (of_int m + 1 / 2) + (of_int n + 1 / 2) * \<tau>"
    using Im_ratio_pos by (auto simp: theta_00_def jacobi_theta_00_eq_0_iff_complex)
  hence "z = (\<omega>1 + \<omega>2) / 2 + of_int m * \<omega>1 + of_int n * \<omega>2"
    by (auto simp: ratio_def divide_simps) (auto simp: algebra_simps)?
  also have "rel \<dots> ((\<omega>1 + \<omega>2) / 2)"
    by (auto simp: rel_def intro!: lattice_intros)
  finally show "rel z ((\<omega>1 + \<omega>2) / 2)" .
next
  assume "rel z ((\<omega>1 + \<omega>2) / 2)"
  then obtain m n :: int where "z = (\<omega>1 + \<omega>2) / 2 + of_int m * \<omega>1 + of_int n * \<omega>2"
    by (auto simp: rel_def of_\<omega>12_coords_def field_simps elim!: latticeE)
  also have "\<dots> / \<omega>1 = (of_int m + 1 / 2) + (of_int n + 1 / 2) * \<tau>"
    by (auto simp: ratio_def field_simps)
  also have "jacobi_theta_00 \<dots> \<tau> = 0"
    by (rule jacobi_theta_00_eq_0')
  finally show "\<theta>\<^sub>0\<^sub>0(z) = 0"
    by (simp add: theta_00_def)
qed

lemma theta_01_eq_0_iff: "\<theta>\<^sub>0\<^sub>1(z) = 0 \<longleftrightarrow> rel z (\<omega>2 / 2)"
  unfolding theta_01_conv_00 theta_00_eq_0_iff rel_def 
  by (simp add: add_divide_distrib)

lemma theta_10_eq_0_iff: "\<theta>\<^sub>1\<^sub>0(z) = 0 \<longleftrightarrow> rel z (\<omega>1 / 2)"
  unfolding theta_10_conv_00 
  by (simp add: theta_00_eq_0_iff add_divide_distrib rel_def)

lemma theta_11_eq_0_iff: "\<theta>\<^sub>1\<^sub>1(z) = 0 \<longleftrightarrow> z \<in> \<Lambda>"
  unfolding theta_11_conv_00 
  by (simp add: theta_00_eq_0_iff add_divide_distrib rel_def)

lemma zorder_theta_00: "zorder theta_00 ((\<omega>1 + \<omega>2) / 2) = 1"
proof -
  define z0 where "z0 = (\<omega>1 + \<omega>2) / 2"
  have z0_over_\<omega>1: "z0 / \<omega>1 = (\<tau> + 1) / 2"
    by (auto simp: z0_def ratio_def field_simps)
  have *: "(\<lambda>z. theta_00 (z0 + z)) = ((\<lambda>z. \<theta>\<^sub>0\<^sub>0((\<tau> + 1) / 2 + z ; \<tau>)) \<circ> (\<lambda>z. z / \<omega>1))"
    unfolding z0_over_\<omega>1 [symmetric] by (simp add: theta_00_def [abs_def] o_def add_divide_distrib)

  define F where "F = fps_expansion (\<lambda>z. \<theta>\<^sub>0\<^sub>0(z ; \<tau>)) ((\<tau> + 1) / 2)"
  have F: "(\<lambda>z. \<theta>\<^sub>0\<^sub>0((\<tau> + 1) / 2 + z ; \<tau>)) has_fps_expansion F"
    unfolding F_def by (intro analytic_at_imp_has_fps_expansion analytic_intros Im_ratio_pos)
  have F': "(\<lambda>z. theta_00 (z0 + z)) has_fps_expansion (F oo (fps_X / fps_const \<omega>1))" 
    unfolding F_def *
    by (intro fps_expansion_intros analytic_at_imp_has_fps_expansion
              analytic_intros Im_ratio_pos) auto

  have nz: "F oo (fps_X / fps_const \<omega>1) \<noteq> 0"
  proof
    assume "F oo (fps_X / fps_const \<omega>1) = 0"
    hence "(\<lambda>z. \<theta>\<^sub>0\<^sub>0(z0 + z)) has_fps_expansion 0"
      using F' by simp
    hence "\<theta>\<^sub>0\<^sub>0(z0 + (-z0)) = 0"
      by (rule has_fps_expansion_0_analytic_continuation[where A = UNIV])
         (auto intro!: holomorphic_intros simp: theta_00_def [abs_def] Im_ratio_pos)
    thus False
      by (simp add: theta_00_eq_0_iff rel_def uminus_in_lattice_iff)
  qed
  hence [simp]: "F \<noteq> 0"
    by auto

  have "1 = zorder (\<lambda>z. \<theta>\<^sub>0\<^sub>0(z ; \<tau>)) ((\<tau> + 1) / 2)"
    by (subst jacobi_theta_00_simple_zero) (simp_all add: Im_ratio_pos jacobi_theta_00_eq_0)
  also have "\<dots> = subdegree F"
    using has_fps_expansion_zorder[OF F] by simp
  also have "\<dots> = zorder theta_00 z0"
    using has_fps_expansion_zorder[OF F'] nz by simp
  finally show ?thesis
    by (simp add: z0_def)
qed

(* TODO Move *)
definition theta_11' :: "complex \<Rightarrow> complex" ("\<theta>\<^sub>1\<^sub>1'''(_')") where
  "theta_11' = deriv theta_11"

lemma has_field_derivative_theta_11' [derivative_intros]:
  assumes "(f has_field_derivative f') (at x within A)"
  shows   "((\<lambda>x. theta_11 (f x)) has_field_derivative (f' * theta_11' (f x))) (at x within A)"
proof -
  have *: "theta_11 analytic_on {f x}" using Im_ratio_pos
    by (auto simp: theta_11_def [abs_def] intro!: analytic_intros)
  have "((theta_11 \<circ> f) has_field_derivative (theta_11' (f x) * f')) (at x within A)"
    by (rule DERIV_chain) (auto simp: theta_11'_def intro!: analytic_derivI assms *)
  thus ?thesis
    by (simp add: mult_ac o_def)
qed

lemma theta_11'_uminus: "\<theta>\<^sub>1\<^sub>1'(-z) = \<theta>\<^sub>1\<^sub>1'(z)" for z
proof -
  have "((theta_11 \<circ> (\<lambda>z. -z)) has_field_derivative (\<theta>\<^sub>1\<^sub>1'(-z) * (-1))) (at z)" 
    by (rule DERIV_chain) (auto intro!: derivative_eq_intros)
  also have "theta_11 \<circ> (\<lambda>z. -z) = (\<lambda>z. -\<theta>\<^sub>1\<^sub>1(z))"
    by (auto simp: o_def theta_11_def)
  finally have "((\<lambda>z. -\<theta>\<^sub>1\<^sub>1(z)) has_field_derivative (-\<theta>\<^sub>1\<^sub>1'(-z))) (at z)"
    by simp
  moreover have "((\<lambda>z. -\<theta>\<^sub>1\<^sub>1(z)) has_field_derivative (-\<theta>\<^sub>1\<^sub>1'(z))) (at z)"
    by (auto intro!: derivative_eq_intros)
  ultimately have "-\<theta>\<^sub>1\<^sub>1'(-z) = -\<theta>\<^sub>1\<^sub>1'(z)"
    by (rule DERIV_unique)
  thus ?thesis
    by simp
qed

(* TODO Move *)
definition fps_theta_11 :: "complex fps" 
  where "fps_theta_11 = fps_expansion theta_11 0"

lemma has_fps_expansion_theta_11 [fps_expansion_intros]: "theta_11 has_fps_expansion fps_theta_11"
  unfolding fps_theta_11_def theta_11_def
  by (intro analytic_at_imp_has_fps_expansion_0 analytic_intros) (use Im_ratio_pos in auto)

lemma has_fps_expansion_theta_11' [fps_expansion_intros]:
  "theta_11' has_fps_expansion fps_deriv fps_theta_11"
  unfolding theta_11'_def by (intro fps_expansion_intros)

lemma fps_theta_11_nth_even_eq_0 [simp]:
  assumes "even n"
  shows   "fps_nth fps_theta_11 n = 0"
proof -
  have "(\<lambda>z. theta_11 z + (theta_11 \<circ> (\<lambda>z. -z)) z) has_fps_expansion 
          (fps_theta_11 + fps_compose fps_theta_11 (-fps_X))"
    by (intro fps_expansion_intros) auto
  also have "(\<lambda>z. theta_11 z + (theta_11 \<circ> (\<lambda>z. -z)) z) = (\<lambda>_. 0)"
    by (simp add: theta_11_def)
  finally have "(\<lambda>z. 0) has_fps_expansion fps_theta_11 + (fps_theta_11 oo - fps_X)" .
  moreover have "(\<lambda>z. 0) has_fps_expansion 0" by simp
  ultimately have "fps_theta_11 + (fps_compose fps_theta_11 (-fps_X)) = 0"
    using fps_expansion_unique_complex by blast
  hence "0 = fps_nth (fps_theta_11 + (fps_compose fps_theta_11 (-fps_X))) n"
    by simp
  also have "\<dots> = 2 * fps_nth fps_theta_11 n"
    using fps_nth_compose_linear[of fps_theta_11 "-1"] assms
    by (auto simp del: fps_nth_compose_linear simp flip: fps_const_neg)
  finally show ?thesis
    by simp
qed 

lemma fps_theta_11_0 [simp]: "fps_nth fps_theta_11 0 = 0"
  by simp

lemma fps_theta_11_1: "fps_nth fps_theta_11 (Suc 0) = \<theta>\<^sub>1\<^sub>1'(0)"
  using fps_nth_fps_expansion[OF has_fps_expansion_theta_11, of 1] by (simp add: theta_11'_def)

lemma theta_11'_0_eq: "\<theta>\<^sub>1\<^sub>1'(0) = -of_real pi * \<theta>\<^sub>0\<^sub>0(0) * \<theta>\<^sub>0\<^sub>1(0) * \<theta>\<^sub>1\<^sub>0(0) / \<omega>1"
proof -
  have "(((\<lambda>x. jacobi_theta_11 x \<tau>) \<circ> (\<lambda>x. x / \<omega>1)) has_field_derivative 
          (deriv (\<lambda>x. jacobi_theta_11 x \<tau>) (0 / \<omega>1) * (1 / \<omega>1))) (at 0)"
    unfolding fps_theta_11_1 using Im_ratio_pos
    by (intro DERIV_chain analytic_derivI analytic_intros)
       (auto intro!: derivative_eq_intros)
  hence "(theta_11 has_field_derivative (deriv (\<lambda>x. jacobi_theta_11 x \<tau>) 0 / \<omega>1)) (at 0)"
    by (simp add: o_def theta_11_def [abs_def])
  hence "fps_nth fps_theta_11 (Suc 0) = 
               -(of_real pi * theta_00 0 * theta_01 0 * theta_10 0 / \<omega>1)"
    unfolding fps_theta_11_1 theta_11'_def using Im_ratio_pos
    by (intro DERIV_imp_deriv) 
       (simp add: deriv_jacobi_theta_11_at_0 theta_00_def theta_01_def theta_10_def mult_ac)
  thus ?thesis
    by (simp add: fps_theta_11_1)
qed

lemma theta_11'_0_nonzero [simp]: "\<theta>\<^sub>1\<^sub>1'(0) \<noteq> 0"
  by (auto simp: theta_11'_0_eq theta_00_eq_0_iff theta_01_eq_0_iff theta_10_eq_0_iff rel_def 
                 uminus_in_lattice_iff)

lemma fps_theta_11_nonzero [simp]: "fps_theta_11 \<noteq> 0"
  using theta_11'_0_nonzero unfolding fps_theta_11_1 [symmetric] by auto

lemma subdegree_fps_theta_11 [simp]: "subdegree fps_theta_11 = 1"
  by (rule subdegreeI) (auto simp: fps_theta_11_1 theta_11'_0_nonzero)

lemma fps_theta_11_conv_theta_11_coeffs:
  "fps_nth fps_theta_11 n = \<i> * (2 * of_real pi * \<i>) ^ n / (\<omega>1 ^ n * fact n) * theta_11_coeffs n \<tau>"
proof -
  have "fps_nth fps_theta_11 n = (deriv ^^ n) theta_11 0 / fact n"
    using fps_nth_fps_expansion[OF has_fps_expansion_theta_11, of n] by simp
  also have "(deriv ^^ n) theta_11 0 = (deriv ^^ n) ((\<lambda>z. \<theta>\<^sub>1\<^sub>1(z ; \<tau>)) \<circ> (\<lambda>z. 1 / \<omega>1 * z)) 0"
    by (simp add: theta_11_def [abs_def] o_def)
  also have "\<dots> = (deriv ^^ n) (\<lambda>z. \<theta>\<^sub>1\<^sub>1(z ; \<tau>)) 0 / \<omega>1 ^ n"
    by (subst higher_deriv_scale) (auto intro!: analytic_intros simp: field_simps Im_ratio_pos)
  also have "\<dots> / fact n = \<i> * (2 * of_real pi * \<i>) ^ n / (\<omega>1 ^ n * fact n) * theta_11_coeffs n \<tau>"
    by (subst higher_deriv_jacobi_theta_11_conv_theta_11_coeffs) (auto simp: Im_ratio_pos field_simps)
  finally show ?thesis .
qed


text \<open>
  By comparing the zeros of $\wp(z) - e_2$ and $(\vartheta_{01}(z)/\vartheta_{11}(z))^2$ we
  find that the two functions are identical up to a constant factor, which we then determine
  to be $(\pi\vartheta_{10}(0)\vartheta_{00}(0)/\omega_1)^2$ by comparing the Laurent series expansions
  of the two functions at their pole at the origin.

  It follows that we can express $\wp$ in terms of the constant $e_2$ and the theta functions.
\<close>
lemma weierstrass_fun_conv_theta:
  assumes z: "z \<notin> \<Lambda>"
  shows   "\<wp> z = \<e>\<^sub>2 + (pi * \<theta>\<^sub>1\<^sub>0(0) * \<theta>\<^sub>0\<^sub>0(0) / \<omega>1) ^ 2 * \<theta>\<^sub>0\<^sub>1(z) ^ 2 / \<theta>\<^sub>1\<^sub>1(z) ^ 2" 
proof -
  define f where "f = (\<lambda>z. \<wp> z - number_e2)"
  interpret f: weierstrass_fun_minus_const \<omega>1 \<omega>2 "\<omega>2 / 2" f
    by unfold_locales (auto simp: f_def number_e2_def)
  define g where "g = (\<lambda>z. (theta_01 z / theta_11 z) ^ 2)"

  interpret g: even_elliptic_function \<omega>1 \<omega>2 g
  proof                     
    fix z :: complex
    show "g (z + \<omega>1) = g z"
      by (simp add: g_def add_divide_distrib theta_01_def theta_11_def 
                    jacobi_theta_01_left.plus_1 jacobi_theta_11_plus1_left)
  next
    fix z :: complex
    have "g (z + \<omega>2) = g z * (to_nome (\<tau> + 2 * z / \<omega>1) / to_nome (2 * z / \<omega>1 + \<tau>)) ^ 2"
      by (simp add: g_def add_divide_distrib ratio_def jacobi_theta_01_plus_quasiperiod 
                    jacobi_theta_11_plus_quasiperiod power_divide theta_01_def theta_11_def)
    also have "to_nome (\<tau> + 2 * z / \<omega>1) / to_nome (2 * z / \<omega>1 + \<tau>) = 1"
      unfolding to_nome_diff [symmetric] by simp
    finally show "g (z + \<omega>2) = g z"
      by simp
  next
    show "g meromorphic_on UNIV"
      unfolding g_def theta_01_def theta_11_def using Im_ratio_pos
      by (intro meromorphic_intros analytic_on_imp_meromorphic_on analytic_intros) auto
  next
    fix z show "g (-z) = g z"
      by (auto simp: g_def theta_01_def theta_11_def)
  qed

  define Z where "Z = {z \<in> half_fund_parallelogram \<setminus> {0}. is_pole g z \<or> isolated_zero g z}"
  define h where "h = (\<lambda>z. zorder g z div (if 2 * z \<in> \<Lambda> then 2 else 1))"
  have [analytic_intros]: "g analytic_on A" if "A \<inter> \<Lambda> = {}" for A
    using Im_ratio_pos that theta_11_eq_0_iff unfolding g_def theta_01_def theta_11_def
    by (auto intro!: analytic_intros)

  have g_nz: "\<not>(\<forall>\<^sub>\<approx>z. g z = 0)"
  proof
    assume "\<forall>\<^sub>\<approx>z. g z = 0"
    moreover have "\<forall>\<^sub>\<approx>z. g z \<noteq> 0"
      using eventually_not_rel_cosparse[of "\<omega>2 / 2"] eventually_not_in_lattice_cosparse
      by eventually_elim (auto simp: g_def theta_01_eq_0_iff theta_11_eq_0_iff)
    ultimately have "\<forall>\<^sub>\<approx>z::complex. False"
      by eventually_elim auto
    thus False
      by simp
  qed

  define z0 where "z0 = \<omega>2 / 2"
  have z0: "z0 \<in> half_fund_parallelogram" "z0 \<noteq> 0" "z0 \<notin> \<Lambda>" "rel z0 (\<omega>2 / 2)"
    by (auto simp: half_fund_parallelogram_altdef z0_def)

  have zero_at_z0: "isolated_zero g z0"
  proof (subst g.isolated_zero_analytic_iff)
    show "g analytic_on {z0}" using z0
      by (auto intro!: analytic_intros)
  next
    show "g z0 = 0" using z0
      by (auto simp: g_def theta_01_eq_0_iff)
  qed (use g_nz in auto)

  have Z_eq: "Z = {z0}"
  proof (intro equalityI subsetI)
    fix z assume "z \<in> Z"
    hence z: "z \<in> half_fund_parallelogram" "z \<noteq> 0" and z': "is_pole g z \<or> isolated_zero g z"
      by (auto simp: Z_def)
    have "z \<notin> \<Lambda>"
      using z by (metis half_fund_parallelogram_in_lattice_iff)
    hence "g analytic_on {z}"
      by (auto intro!: analytic_intros)
    hence "\<not>is_pole g z"
      by (rule analytic_at_imp_no_pole)
    with z' have "isolated_zero g z"
      by auto
    hence "g z = 0"
      using \<open>g analytic_on {z}\<close> by (simp add: zero_isolated_zero_analytic)
    with \<open>z \<notin> \<Lambda>\<close> have "rel z (\<omega>2 / 2)"
      by (auto simp: g_def theta_01_eq_0_iff theta_11_eq_0_iff)
    moreover have "\<omega>2 / 2 \<in> period_parallelogram 0"
      unfolding period_parallelogram_altdef by auto
    moreover have "z \<in> period_parallelogram 0"
      using z(1) half_fund_parallelogram_subset_period_parallelogram by blast
    ultimately show "z \<in> {z0}"
      using to_fund_parallelogram_unique' unfolding z0_def by blast
  next
    fix z assume "z \<in> {z0}"
    thus "z \<in> Z"
      using z0 zero_at_z0 by (auto simp: Z_def)
  qed

  define A where "A = fps_expansion theta_01 0"
  have A[fps_expansion_intros]: "theta_01 has_fps_expansion A"
    unfolding A_def theta_01_def
    by (intro analytic_at_imp_has_fps_expansion_0 analytic_intros) (use Im_ratio_pos in auto)

  have A0: "fps_nth A 0 = \<theta>\<^sub>0\<^sub>1(0)"
    using has_fps_expansion_imp_0_eq_fps_nth_0[OF A] by (simp add: theta_01_def)
  have [simp]: "A \<noteq> 0"
  proof -
    have "fps_nth A 0 \<noteq> 0"
      by (auto simp: A0 theta_01_eq_0_iff rel_def uminus_in_lattice_iff)
    thus "A \<noteq> 0"
      by auto
  qed
  have [simp]: "subdegree A = 0"
    by (rule subdegree_eq_0)
       (use theta_01_eq_0_iff[of 0] in \<open>auto simp: A0 rel_def uminus_in_lattice_iff\<close>)

  obtain c where "\<forall>\<^sub>\<approx>z. g z = c * (\<Prod>w\<in>Z. (\<wp> z - \<wp> w) powi h w)"
    using g.in_terms_of_weierstrass_fun_even_aux[OF g_nz]
    unfolding h_def unfolding Z_def by blast
  also have "(\<lambda>z. c * (\<Prod>w\<in>Z. (\<wp> z - \<wp> w) powi h w)) = (\<lambda>z. c * (\<wp> z - \<e>\<^sub>2) powi h z0)"
    by (simp add: Z_eq z0_def number_e2_def)
  also have "h z0 = zorder g z0 div 2"
    by (simp add: h_def z0_def)
  also have "zorder g z0 = 2"
  proof -
    (* TODO: this could probably be simplified using Laurent series *)
    have ev_nz: "\<forall>\<^sub>F z in at z0. \<theta>\<^sub>0\<^sub>1(z) \<noteq> 0" "\<forall>\<^sub>F z in at z0. \<theta>\<^sub>1\<^sub>1(z) \<noteq> 0"
      using eventually_not_rel_cosparse[of "\<omega>2/2"] eventually_not_in_lattice_cosparse
      by (auto simp: theta_01_eq_0_iff theta_11_eq_0_iff dest: eventually_cosparse_imp_eventually_at)
    from z0 have nz: "\<theta>\<^sub>1\<^sub>1(z0) \<noteq> 0"
      by (subst theta_11_eq_0_iff) auto

    have "\<forall>\<^sub>F z in at z0. \<theta>\<^sub>0\<^sub>1(z) / \<theta>\<^sub>1\<^sub>1(z) \<noteq> 0"
      using ev_nz by eventually_elim auto
    hence "zorder g z0 = 2 * zorder (\<lambda>z. \<theta>\<^sub>0\<^sub>1(z) / \<theta>\<^sub>1\<^sub>1(z)) z0 "
      unfolding g_def using ev_nz nz
      by (subst zorder_power) 
         (auto simp: theta_11_def [abs_def] theta_01_def [abs_def] Im_ratio_pos theta_11_eq_0_iff
               intro!: analytic_on_imp_meromorphic_on analytic_intros eventually_frequently)
    also have "zorder (\<lambda>z. \<theta>\<^sub>0\<^sub>1(z) / \<theta>\<^sub>1\<^sub>1(z)) z0 = zorder (\<lambda>z. \<theta>\<^sub>0\<^sub>1(z)) z0 - zorder (\<lambda>z. \<theta>\<^sub>1\<^sub>1(z)) z0"
      using ev_nz by (subst zorder_divide)
                     (auto intro!: analytic_on_imp_meromorphic_on analytic_intros eventually_frequently
                           simp: theta_01_def [abs_def] theta_11_def [abs_def] Im_ratio_pos)
    also from Im_ratio_pos and nz have "zorder (\<lambda>z. \<theta>\<^sub>1\<^sub>1(z)) z0 = 0"
      by (intro zorder_eq_0I) (auto simp: theta_11_def [abs_def] intro!: analytic_intros)
    also have "zorder theta_01 z0 = zorder theta_00 ((\<omega>1 + \<omega>2) / 2)"
      by (simp add: theta_01_conv_00 [abs_def] zorder_shift' z0_def add_ac add_divide_distrib)
    also have "\<dots> = 1"
      by (rule zorder_theta_00)
    finally show "zorder g z0 = 2"
      by simp
  qed
  finally have g_eq: "\<forall>\<^sub>\<approx>z. g z = c * (\<wp> z - \<e>\<^sub>2)"
    by simp
  
  have g_eq': "g z = c * (\<wp> z - \<e>\<^sub>2)" if "z \<notin> \<Lambda>" for z
    using g_eq
  proof (rule analytic_on_continuation)
    show "z \<in> (-\<Lambda>) \<inter> UNIV"
      using that by auto
  qed (auto intro!: analytic_intros)

  define F where "F = ((fps_to_fls A / fps_to_fls fps_theta_11) ^ 2 - 
                        fls_const c * (fls_weierstrass - fls_const \<e>\<^sub>2))"

  have "(\<lambda>z. g z - c * (\<wp> z - \<e>\<^sub>2)) has_laurent_expansion F"
    unfolding F_def g_def
    by (intro laurent_expansion_intros has_laurent_expansion_fps fps_expansion_intros)
  also have "?this \<longleftrightarrow> (\<lambda>z. 0) has_laurent_expansion F"
  proof (rule has_laurent_expansion_cong)
    have "\<forall>\<^sub>F x in at 0. g x = c * (\<wp> x - \<e>\<^sub>2)"
      using g_eq by (auto dest: eventually_cosparse_imp_eventually_at)
    thus "\<forall>\<^sub>F x in at 0. g x - c * (\<wp> x - \<e>\<^sub>2) = 0"
      by eventually_elim auto
  qed auto
  finally have "F = 0"
    by (rule zero_has_laurent_expansion_imp_eq_0)

  have "0 = fls_nth F (-2)"
    by (simp add: \<open>F = 0\<close>)
  also have "\<dots> = fls_nth ((fps_to_fls A / fps_to_fls fps_theta_11)\<^sup>2) (- 2) - c"
    by (simp add: fls_weierstrass_def F_def)
  also have "-2 = int 2 * fls_subdegree (fps_to_fls A / fps_to_fls fps_theta_11)"
    by (subst fls_divide_subdegree) (auto simp: fls_subdegree_fls_to_fps)
  also have "fls_nth ((fps_to_fls A / fps_to_fls fps_theta_11) ^ 2) \<dots> = 
               (fls_nth (fps_to_fls A / fps_to_fls fps_theta_11) (-1))\<^sup>2"
    by (subst fls_pow_base) (auto simp: fls_divide_subdegree fls_subdegree_fls_to_fps)
  also have "-1 = fls_subdegree (fps_to_fls A) - fls_subdegree (fps_to_fls fps_theta_11)"
    by (simp add: fls_subdegree_fls_to_fps)
  also have "fls_nth (fps_to_fls A / fps_to_fls fps_theta_11) \<dots> =
               \<theta>\<^sub>0\<^sub>1(0) / fps_nth fps_theta_11 (Suc 0)"
    by (subst fls_divide_nth_base) 
       (auto simp: fls_subdegree_fls_to_fps A0 theta_01_def)
  finally have c_eq: "c = (\<theta>\<^sub>0\<^sub>1(0) / fps_nth fps_theta_11 (Suc 0)) ^ 2"
    by simp

  have "\<wp> z = \<e>\<^sub>2 + (fps_nth fps_theta_11 1 / \<theta>\<^sub>0\<^sub>1(0)) ^ 2 * \<theta>\<^sub>0\<^sub>1(z) ^ 2 / \<theta>\<^sub>1\<^sub>1(z) ^ 2"
    using g_eq'[of z] theta_01_eq_0_iff[of 0] theta_11_eq_0_iff[of z] z
    by (auto simp: c_eq g_def rel_def uminus_in_lattice_iff field_simps fps_theta_11_1)
  also have "(fps_nth fps_theta_11 1 / \<theta>\<^sub>0\<^sub>1(0)) ^ 2 * \<theta>\<^sub>0\<^sub>1(z) ^ 2 / \<theta>\<^sub>1\<^sub>1(z) ^ 2 =
               (of_real pi * \<theta>\<^sub>1\<^sub>0(0) * \<theta>\<^sub>0\<^sub>0(0) / \<omega>1)\<^sup>2 * \<theta>\<^sub>0\<^sub>1(z)\<^sup>2 / \<theta>\<^sub>1\<^sub>1(z)\<^sup>2"
    by (simp add: field_simps theta_01_eq_0_iff rel_def uminus_in_lattice_iff fps_theta_11_1
                  theta_11'_0_eq)
  finally show ?thesis .
qed

text \<open>
  By plugging in values into the above identity, we derive expressions for $e_1$, $e_2$, $e_3$
  and the lattice modulus $\lambda$ purely in terms of theta functions.
\<close>
lemma e12_conv_theta: "\<e>\<^sub>1 - \<e>\<^sub>2 = (pi / \<omega>1) ^ 2 * \<theta>\<^sub>0\<^sub>0(0) ^ 4"
  and e32_conv_theta: "\<e>\<^sub>3 - \<e>\<^sub>2 = (pi / \<omega>1) ^ 2 * \<theta>\<^sub>1\<^sub>0(0) ^ 4"
  and e13_conv_theta: "\<e>\<^sub>1 - \<e>\<^sub>3 = (pi / \<omega>1) ^ 2 * \<theta>\<^sub>0\<^sub>1(0) ^ 4"
  and e1_conv_theta:  "\<e>\<^sub>1 = (pi / \<omega>1) ^ 2 / 3 * (\<theta>\<^sub>0\<^sub>0(0) ^ 4 + \<theta>\<^sub>0\<^sub>1(0) ^ 4)"
  and e2_conv_theta:  "\<e>\<^sub>2 = -(pi / \<omega>1)\<^sup>2 / 3 * (\<theta>\<^sub>0\<^sub>0(0) ^ 4 + \<theta>\<^sub>1\<^sub>0(0) ^ 4)"
  and e3_conv_theta:  "\<e>\<^sub>3 = (pi / \<omega>1)\<^sup>2 / 3 * (\<theta>\<^sub>1\<^sub>0(0) ^ 4 - \<theta>\<^sub>0\<^sub>1(0) ^ 4)"
  and modulus_conv_theta: "modulus = \<theta>\<^sub>1\<^sub>0(0) ^ 4 / \<theta>\<^sub>0\<^sub>0(0) ^ 4"
proof -
  have "\<e>\<^sub>1 - \<e>\<^sub>2 = (of_real pi * \<theta>\<^sub>1\<^sub>0(0) * \<theta>\<^sub>0\<^sub>0(0) / \<omega>1)\<^sup>2 * \<theta>\<^sub>0\<^sub>1(\<omega>1/2)\<^sup>2 / \<theta>\<^sub>1\<^sub>1(\<omega>1/2)\<^sup>2"
    using weierstrass_fun_conv_theta[of "\<omega>1 / 2"]
    unfolding number_e1_def by simp
  also have "\<theta>\<^sub>0\<^sub>1(\<omega>1/2) = \<theta>\<^sub>0\<^sub>0(0)"
    using jacobi_theta_00_left.plus_1[of 0 \<tau>]
    by (simp add: jacobi_theta_01_def theta_00_def theta_01_def)
  also have "\<theta>\<^sub>1\<^sub>1(\<omega>1/2) = -\<theta>\<^sub>1\<^sub>0(0)"
    using jacobi_theta_00_left.plus_1[of "\<tau> / 2" \<tau>]
    by (simp add: jacobi_theta_11_def algebra_simps to_nome_add jacobi_theta_10_def 
                  theta_10_def theta_11_def)
  also have "(of_real pi * \<theta>\<^sub>1\<^sub>0(0) * \<theta>\<^sub>0\<^sub>0(0) / \<omega>1)\<^sup>2 * \<theta>\<^sub>0\<^sub>0(0)\<^sup>2 / (- \<theta>\<^sub>1\<^sub>0(0))\<^sup>2 =
               (pi / \<omega>1) ^ 2 * \<theta>\<^sub>0\<^sub>0(0) ^ 4"
    using theta_10_eq_0_iff[of 0] by (simp add: field_simps rel_def uminus_in_lattice_iff)
  finally show e12: "\<e>\<^sub>1 - \<e>\<^sub>2 = (pi / \<omega>1) ^ 2 * \<theta>\<^sub>0\<^sub>0(0) ^ 4" .

  have "\<e>\<^sub>3 - \<e>\<^sub>2 = (of_real pi * \<theta>\<^sub>1\<^sub>0(0) * \<theta>\<^sub>0\<^sub>0(0) / \<omega>1)\<^sup>2 * 
                         (\<theta>\<^sub>0\<^sub>1((\<omega>1 + \<omega>2) / 2) / \<theta>\<^sub>1\<^sub>1((\<omega>1 + \<omega>2) / 2))\<^sup>2"
    using weierstrass_fun_conv_theta[of "(\<omega>1 + \<omega>2) / 2"] unfolding number_e3_def
    by (simp add: power_divide)
  also have "\<theta>\<^sub>0\<^sub>1((\<omega>1 + \<omega>2) / 2) = \<theta>\<^sub>0\<^sub>0(\<tau>/2 + 1 ; \<tau>)"
    by (simp add: theta_01_conv_00 theta_00_def add_divide_distrib ratio_def mult_ac add_ac)
  also have "\<dots> = \<theta>\<^sub>0\<^sub>0(\<tau>/2 ; \<tau>)"
    by (subst jacobi_theta_00_left.plus_1) auto
  also have "\<dots> = \<theta>\<^sub>1\<^sub>0(0) * to_nome (-\<tau>/4)"
    by (simp add: theta_10_conv_00 theta_00_def ratio_def mult_ac to_nome_minus)
  also have "\<theta>\<^sub>1\<^sub>1((\<omega>1 + \<omega>2) / 2) = -\<theta>\<^sub>0\<^sub>0(0 + \<tau> + 1 ; \<tau>) * to_nome (3/4*\<tau>)"
    by (simp add: theta_11_conv_00 theta_00_def add_divide_distrib ratio_def mult_ac add_ac to_nome_add) 
  also have "\<dots> = -\<theta>\<^sub>0\<^sub>0(0) * to_nome (3/4*\<tau> - \<tau>)"
    unfolding jacobi_theta_00_left.plus_1 jacobi_theta_00_plus_quasiperiod to_nome_diff theta_00_def
    by simp
  also have "\<theta>\<^sub>1\<^sub>0(0) * to_nome (-\<tau>/4) / \<dots> = -\<theta>\<^sub>1\<^sub>0(0) / \<theta>\<^sub>0\<^sub>0(0) * to_nome (-\<tau>/4 - 3/4 * \<tau> + \<tau>)"
    unfolding to_nome_diff to_nome_add by (simp add: field_simps)
  also have "\<dots> ^ 2 = \<theta>\<^sub>1\<^sub>0(0) ^ 2 / \<theta>\<^sub>0\<^sub>0(0) ^ 2"
    by (simp add: power_divide)
  also have "(of_real pi * \<theta>\<^sub>1\<^sub>0(0) * \<theta>\<^sub>0\<^sub>0(0) / \<omega>1)\<^sup>2 * (\<theta>\<^sub>1\<^sub>0(0)\<^sup>2 / \<theta>\<^sub>0\<^sub>0(0)\<^sup>2) = (pi / \<omega>1) ^ 2 * \<theta>\<^sub>1\<^sub>0(0) ^ 4"
    by (simp add: field_simps rel_def uminus_in_lattice_iff to_nome_minus theta_00_eq_0_iff)
  finally show e32: "\<e>\<^sub>3 - \<e>\<^sub>2 = (pi / \<omega>1) ^ 2 * \<theta>\<^sub>1\<^sub>0(0) ^ 4" .

  have "(\<e>\<^sub>1 - \<e>\<^sub>2) - (\<e>\<^sub>3 - \<e>\<^sub>2) = (pi / \<omega>1) ^ 2 * (\<theta>\<^sub>0\<^sub>0(0) ^ 4 - \<theta>\<^sub>1\<^sub>0(0) ^ 4)"
    unfolding e32 e12 by (simp add: field_simps)
  also have "\<theta>\<^sub>0\<^sub>0(0) ^ 4 - \<theta>\<^sub>1\<^sub>0(0) ^ 4 = \<theta>\<^sub>0\<^sub>1(0) ^ 4"
    using jacobi_theta_xy_0_pow4_complex[of \<tau>] Im_ratio_pos
    by (simp add: theta_00_def theta_01_def theta_10_def algebra_simps)
  finally show e13: "\<e>\<^sub>1 - \<e>\<^sub>3 = (pi / \<omega>1) ^ 2 * \<theta>\<^sub>0\<^sub>1(0) ^ 4"
    by simp

  have e3_eq: "\<e>\<^sub>3 = -(\<e>\<^sub>1 + \<e>\<^sub>2)"
    using sum_e123_0 by (Groebner_Basis.algebra)
  have "\<e>\<^sub>1 = ((\<e>\<^sub>1 - \<e>\<^sub>2) + (\<e>\<^sub>1 - \<e>\<^sub>3)) / 3"
    by (simp add: algebra_simps e3_eq)
  also have "\<dots> = (pi / \<omega>1) ^ 2 / 3 * (\<theta>\<^sub>0\<^sub>0(0) ^ 4 + \<theta>\<^sub>0\<^sub>1(0) ^ 4)"
    unfolding e12 e13 by (simp add: algebra_simps add_divide_distrib)
  finally show e1: "\<e>\<^sub>1 = (pi / \<omega>1) ^ 2 / 3 * (\<theta>\<^sub>0\<^sub>0(0) ^ 4 + \<theta>\<^sub>0\<^sub>1(0) ^ 4)" .

  have e2_eq: "\<e>\<^sub>2 = -(\<e>\<^sub>1 + \<e>\<^sub>3)"
    using sum_e123_0 by (Groebner_Basis.algebra)
  have "\<e>\<^sub>3 = ((\<e>\<^sub>1 - \<e>\<^sub>2) - 2 * (\<e>\<^sub>1 - \<e>\<^sub>3)) / 3"
    by (simp add: algebra_simps e2_eq)
  also have "\<dots> = (pi / \<omega>1) ^ 2 / 3 * (\<theta>\<^sub>0\<^sub>0(0) ^ 4 - 2 * \<theta>\<^sub>0\<^sub>1(0) ^ 4)"
    unfolding e12 e13 by (simp add: algebra_simps diff_divide_distrib)
  also have "\<theta>\<^sub>0\<^sub>0(0) ^ 4 - 2 * \<theta>\<^sub>0\<^sub>1(0) ^ 4 = \<theta>\<^sub>1\<^sub>0(0) ^ 4 - \<theta>\<^sub>0\<^sub>1(0) ^ 4"
    using jacobi_theta_xy_0_pow4_complex[of \<tau>, symmetric] Im_ratio_pos
    by (simp add: theta_00_def theta_01_def theta_10_def)
  finally show e3: "\<e>\<^sub>3 = (pi / \<omega>1)\<^sup>2 / 3 * (\<theta>\<^sub>1\<^sub>0(0) ^ 4 - \<theta>\<^sub>0\<^sub>1(0) ^ 4)" .

  show e2: "\<e>\<^sub>2 = -(pi / \<omega>1)\<^sup>2 / 3 * (\<theta>\<^sub>0\<^sub>0(0) ^ 4 + \<theta>\<^sub>1\<^sub>0(0) ^ 4)"
    unfolding e2_eq e1 e3 by (simp add: field_simps)

  have "modulus = (\<e>\<^sub>3 - \<e>\<^sub>2) / (\<e>\<^sub>1 - \<e>\<^sub>2)"
    by (simp add: modulus_def)
  also have "\<dots> = \<theta>\<^sub>1\<^sub>0(0) ^ 4 / \<theta>\<^sub>0\<^sub>0(0) ^ 4"
    unfolding e32 e12 by simp
  finally show "modulus = \<theta>\<^sub>1\<^sub>0(0) ^ 4 / \<theta>\<^sub>0\<^sub>0(0) ^ 4" .
qed

text \<open>
  Using this, we also obtain an expression of $\wp$ purely in terms of theta functions.
  This immediately shows that $\wp(z, \tau)$ (which we have not defined yet) is holomorphic in 
  both $z$ and $\tau$.
\<close>
lemma weierstrass_fun_conv_theta':
  assumes "z \<notin> \<Lambda>"
  shows   "\<wp> z = (pi / \<omega>1)\<^sup>2 * (-1/3 * (\<theta>\<^sub>0\<^sub>0(0)^4 + \<theta>\<^sub>1\<^sub>0(0)^4) + (\<theta>\<^sub>1\<^sub>0(0) * \<theta>\<^sub>0\<^sub>0(0))\<^sup>2 * \<theta>\<^sub>0\<^sub>1(z)\<^sup>2 / \<theta>\<^sub>1\<^sub>1(z)\<^sup>2)"
  by (subst weierstrass_fun_conv_theta[OF assms], subst e2_conv_theta)
     (simp_all add: field_simps)

lemma invariant_g2_conv_theta:
  "\<g>\<^sub>2 = 2 / 3 * (pi / \<omega>1) ^ 4 * (\<theta>\<^sub>0\<^sub>0(0)^8 + \<theta>\<^sub>1\<^sub>0(0)^8 + \<theta>\<^sub>0\<^sub>1(0)^8)"
proof -
  have *: "\<theta>\<^sub>0\<^sub>0(0) ^ 4 = \<theta>\<^sub>1\<^sub>0(0) ^ 4 + \<theta>\<^sub>0\<^sub>1(0) ^ 4"
    using jacobi_theta_xy_0_pow4_complex[of \<tau>] Im_ratio_pos
    by (simp add: theta_00_def theta_01_def theta_10_def)
  have **: "\<theta>\<^sub>0\<^sub>0(0) ^ 8 = (\<theta>\<^sub>1\<^sub>0(0) ^ 4 + \<theta>\<^sub>0\<^sub>1(0) ^ 4) ^ 2"
    by (subst * [symmetric]) simp_all
  show ?thesis
    apply (simp add: invariant_g2_conv_e123 e1_conv_theta e2_conv_theta e3_conv_theta)
    apply (simp add: divide_simps)
    apply (simp add: algebra_simps power2_eq_square * **)?
    done
qed

lemma invariant_g3_conv_theta:
  "\<g>\<^sub>3 = 4 / 27 * (pi / \<omega>1) ^ 6 * 
          (\<theta>\<^sub>0\<^sub>0(0)^4 + \<theta>\<^sub>0\<^sub>1(0)^4) * (\<theta>\<^sub>0\<^sub>0(0)^4 + \<theta>\<^sub>1\<^sub>0(0)^4) * (\<theta>\<^sub>0\<^sub>1(0)^4 - \<theta>\<^sub>1\<^sub>0(0)^4)"
proof -
  have *: "\<theta>\<^sub>0\<^sub>0(0) ^ 4 = \<theta>\<^sub>1\<^sub>0(0) ^ 4 + \<theta>\<^sub>0\<^sub>1(0) ^ 4"
    using jacobi_theta_xy_0_pow4_complex[of \<tau>] Im_ratio_pos
    by (simp add: theta_00_def theta_01_def theta_10_def)
  show ?thesis
    apply (simp add: invariant_g3_conv_e123 e1_conv_theta e2_conv_theta e3_conv_theta)
    apply (simp add: divide_simps)
    apply (simp add: algebra_simps power2_eq_square *)?
    done
qed

lemma discr_conv_theta:
  "discr = 16 * (pi / \<omega>1) ^ 12 * (\<theta>\<^sub>0\<^sub>0(0) * \<theta>\<^sub>0\<^sub>1(0) * \<theta>\<^sub>1\<^sub>0(0)) ^ 8"
proof -
  have "discr = (4 * (\<e>\<^sub>1 - \<e>\<^sub>2) * (\<e>\<^sub>1 - \<e>\<^sub>3) * (\<e>\<^sub>3 - \<e>\<^sub>2))\<^sup>2"
    unfolding discr_altdef by Groebner_Basis.algebra
  also have "\<dots> = 16 * (pi / \<omega>1) ^ 12 * (\<theta>\<^sub>0\<^sub>0(0) * \<theta>\<^sub>0\<^sub>1(0) * \<theta>\<^sub>1\<^sub>0(0)) ^ 8"
    unfolding e12_conv_theta e13_conv_theta e32_conv_theta
    by (simp add: power_mult_distrib power_divide)
  finally show ?thesis .
qed

text \<open>
  Next, we derive two identities relating the Weierstra\ss\ \<open>\<sigma>\<close> and \<open>\<eta>\<close> functions to the Jacobi
  theta functions. We start with the following one:
  \[\zeta(z) = \frac{\vartheta_{11}'(z)}{\vartheta_{11}(z)} + \frac{\eta(\omega_1)}{\omega_1}z\ .\]
\<close>
theorem weierstrass_zeta_conv_jacobi_theta: 
  assumes z: "z \<notin> \<Lambda>"
  shows "weierstrass_zeta z = \<theta>\<^sub>1\<^sub>1'(z) / \<theta>\<^sub>1\<^sub>1(z) + weierstrass_eta \<omega>1 / \<omega>1 * z"
proof -
  write weierstrass_zeta ("\<zeta>")
  write weierstrass_eta ("\<eta>")

  text \<open>
    First, we let 
      $f(z) = \zeta(z) - \vartheta_{11}'(z)/\vartheta_{11}(z) - \eta(\omega_1)/\omega_1 z$,
    i.e.\ the difference of the two sides of the identity.
  \<close>
  define f_aux where "f_aux = (\<lambda>z. \<zeta> z - \<theta>\<^sub>1\<^sub>1'(z) / \<theta>\<^sub>1\<^sub>1(z) - \<eta> \<omega>1 / \<omega>1 * z)"
  define f where "f = remove_sings f_aux"
  have f_aux_ana: "f_aux analytic_on {z}" if "z \<notin> \<Lambda>" for z
    unfolding f_def f_aux_def using Im_ratio_pos theta_11_eq_0_iff[of z] using that
    by (auto intro!: remove_sings_analytic_on analytic_intros
             simp: theta_11_def[abs_def] theta_11'_def)
  have f_ana: "f analytic_on {z}" if z: "z \<notin> \<Lambda>" for z
    using z unfolding f_def by (intro remove_sings_analytic_on f_aux_ana)

  text \<open>
    We note that $f$ is an odd function for later.
  \<close>
  have f_uminus: "f (-z) = -f z" if z: "z \<notin> \<Lambda>" for z
  proof -
    have "f (-z) = f_aux (-z)" unfolding f_def 
      by (rule remove_sings_at_analytic) 
         (use z in \<open>auto intro!: f_aux_ana simp: uminus_in_lattice_iff\<close>)
    also have "f_aux (-z) = -f_aux z" using z
      by (auto simp: f_aux_def weierstrass_zeta_uminus theta_11'_uminus theta_11_def)
    also have "f_aux z = f z" unfolding f_def
      by (rule sym, rule remove_sings_at_analytic) (use z in \<open>auto intro!: f_aux_ana\<close>)
    finally show ?thesis .
  qed

  text \<open>
    Next, we show that $f$ is an elliptic function. This is relatively straightforward, but it
    does require Legendre's relation in the second part. Also, for technical reasons, we must
    use the \<^const>\<open>remove_sings\<close> operator to ensure periodicity even at the singularities. 
  \<close>
  interpret f: elliptic_function \<omega>1 \<omega>2 f
  proof
    show "f meromorphic_on UNIV"
      unfolding f_def f_aux_def theta_11'_def theta_11_def [abs_def] using Im_ratio_pos
      by (intro meromorphic_intros) (auto intro!: analytic_on_imp_meromorphic_on analytic_intros)
  next
    fix z :: complex
    have eq: "f_aux (z + \<omega>1) = f_aux z" if z: "z \<notin> \<Lambda>" for z
    proof -
      have "\<theta>\<^sub>1\<^sub>1'(z+\<omega>1) = deriv (\<lambda>z. \<theta>\<^sub>1\<^sub>1(z + \<omega>1)) z"
        unfolding theta_11'_def by (simp add: deriv_shift_0' o_def add_ac)
      also have "\<dots> = deriv (\<lambda>z. -\<theta>\<^sub>1\<^sub>1(z)) z"
        by (simp add: theta_11_def add_divide_distrib jacobi_theta_11_plus1_left)
      also have "\<dots> = -\<theta>\<^sub>1\<^sub>1'(z)"
        by (auto intro!: DERIV_imp_deriv derivative_eq_intros)
      finally show "f_aux (z + \<omega>1) = f_aux z" using z
        by (simp add: f_aux_def weierstrass_zeta_plus_lattice add_divide_distrib ring_distribs
                      theta_11_def jacobi_theta_11_plus1_left)
    qed
    have "\<forall>\<^sub>F z in at z. f_aux (z + \<omega>1) = f_aux z"
      using eventually_not_in_lattice_at by eventually_elim (simp add: eq)
    hence "remove_sings (\<lambda>z. f_aux (z + \<omega>1)) z = remove_sings f_aux z"
      by (intro remove_sings_cong refl)
    thus "f (z + \<omega>1) = f z"
      by (simp add: remove_sings_shift_0' f_def add_ac)
  next
    fix z :: complex
    have eq: "f_aux (z + \<omega>2) = f_aux z" if z: "z \<notin> \<Lambda>" for z
    proof -
      have "\<theta>\<^sub>1\<^sub>1'(z+\<omega>2) = deriv (\<lambda>z. \<theta>\<^sub>1\<^sub>1(z + \<omega>2)) z"
        unfolding theta_11'_def by (simp add: deriv_shift_0' o_def add_ac)
      also have "\<dots> = deriv (\<lambda>z. -\<theta>\<^sub>1\<^sub>1(z) / to_nome (\<tau> + 2*z/\<omega>1)) z"
        by (simp add: theta_11_def add_divide_distrib jacobi_theta_11_plus_quasiperiod ratio_def)
      also have "(\<lambda>z. -\<theta>\<^sub>1\<^sub>1(z) / to_nome (\<tau> + 2*z/\<omega>1)) = (\<lambda>z. -\<theta>\<^sub>1\<^sub>1(z) * to_nome (-\<tau> - 2*z/\<omega>1))"
        unfolding to_nome_diff to_nome_minus to_nome_add by (rule ext) (auto simp: field_simps)
      also have "deriv \<dots> z = to_nome (-\<tau> - 2*z/\<omega>1) * (2 * \<i> * pi * \<theta>\<^sub>1\<^sub>1(z) / \<omega>1 - \<theta>\<^sub>1\<^sub>1'(z))"
        by (auto intro!: DERIV_imp_deriv derivative_eq_intros simp: ring_distribs mult_ac)
      finally have *: "\<theta>\<^sub>1\<^sub>1'(z+\<omega>2) = to_nome (-\<tau> - 2*z/\<omega>1) * (2 * \<i> * pi * \<theta>\<^sub>1\<^sub>1(z) / \<omega>1 - \<theta>\<^sub>1\<^sub>1'(z))" .

      have "\<theta>\<^sub>1\<^sub>1(z+\<omega>2) = \<theta>\<^sub>1\<^sub>1(z / \<omega>1 + \<tau> ; \<tau>)"
        by (simp add: theta_11_def add_divide_distrib ratio_def)
      also have "\<dots> = - \<theta>\<^sub>1\<^sub>1(z) / to_nome (\<tau> + 2*z/\<omega>1)"
        by (subst jacobi_theta_11_plus_quasiperiod) (auto simp: theta_11_def)
      finally have **: "\<theta>\<^sub>1\<^sub>1(z + \<omega>2) = - \<theta>\<^sub>1\<^sub>1(z) / to_nome (\<tau> + 2 * z / \<omega>1)" .

      have "f_aux (z + \<omega>2) = \<zeta> z - \<theta>\<^sub>1\<^sub>1'(z+\<omega>2) / \<theta>\<^sub>1\<^sub>1(z+\<omega>2) - \<eta> \<omega>1 * z / \<omega>1 - 
                               (\<omega>2 * \<eta> \<omega>1 - \<omega>1 * \<eta> \<omega>2) / \<omega>1"
        using z by (simp add: f_aux_def weierstrass_zeta_plus_lattice add_divide_distrib
                              ring_distribs diff_divide_distrib)
      also have "\<omega>2 * \<eta> \<omega>1 - \<omega>1 * \<eta> \<omega>2 = 2 * pi * \<i>"
        using Im_ratio_pos by (subst legendre_relation) (auto simp: ratio_def)
      also have "\<theta>\<^sub>1\<^sub>1'(z + \<omega>2) / \<theta>\<^sub>1\<^sub>1(z + \<omega>2) = 
                   \<theta>\<^sub>1\<^sub>1'(z) / \<theta>\<^sub>1\<^sub>1(z) - 2 * \<i> * pi / \<omega>1" using z
        unfolding * ** to_nome_diff to_nome_minus to_nome_add
        by (simp add: theta_11_eq_0_iff field_simps)
      finally show ?thesis
        by (simp add: f_aux_def)
    qed
    have "\<forall>\<^sub>F z in at z. f_aux (z + \<omega>2) = f_aux z"
      using eventually_not_in_lattice_at by eventually_elim (simp add: eq)
    hence "remove_sings (\<lambda>z. f_aux (z + \<omega>2)) z = remove_sings f_aux z"
      by (intro remove_sings_cong refl)
    thus "f (z + \<omega>2) = f z"
      by (simp add: remove_sings_shift_0' f_def add_ac)
  qed

  interpret f: nicely_elliptic_function \<omega>1 \<omega>2 f
  proof
    show "f nicely_meromorphic_on UNIV"
      unfolding f_def f_aux_def theta_11'_def theta_11_def [abs_def] using Im_ratio_pos
      by (intro meromorphic_intros remove_sings_nicely_meromorphic)
         (auto intro!: analytic_on_imp_meromorphic_on analytic_intros)
  qed

  text \<open>
    Next, we examing the series expansion of $f(z)$ at $z = 0$ to show that the poles cancel.
  \<close>

  have [simp]: "fps_nth fps_theta_11 (Suc 0) \<noteq> 0"
    by (auto simp: fps_theta_11_1 theta_11'_0_nonzero)
  have [simp]: "subdegree (fps_deriv fps_theta_11) = 0"
    by (rule subdegreeI) auto
  have [simp]: "fps_deriv fps_theta_11 \<noteq> 0"
  proof -
    have "fps_nth (fps_deriv fps_theta_11) 0 \<noteq> fps_nth 0 0"
      by auto
    thus ?thesis
      by metis
  qed

  define C where "C = fps_to_fls (fps_deriv fps_theta_11) / fps_to_fls fps_theta_11"
  have "fls_subdegree C = -1" unfolding C_def
    by (subst fls_divide_subdegree) 
       (auto simp: fls_subdegree_fls_to_fps simp del: fps_deriv_eq_0_iff)

  define F where "F = fls_weierstrass_zeta - C - fls_const (\<eta> \<omega>1 / \<omega>1) * fls_X"
  have F: "f has_laurent_expansion F"
    unfolding f_def f_aux_def theta_11'_def C_def F_def
    by (intro laurent_expansion_intros has_laurent_expansion_fps fps_expansion_intros)

  have "fls_subdegree F \<ge> 0"
  proof (rule fls_subdegree_ge0I)
    show "fls_nth F n = 0" if n: "n < 0" for n
    proof (cases "n = -1")
      case [simp]: True
      have "fls_nth C (-1) = 1"
        unfolding C_def 
        using fls_divide_nth_base[of "fps_to_fls (fps_deriv fps_theta_11)" "fps_to_fls fps_theta_11"]
        by (simp add: fls_subdegree_fls_to_fps)
      thus ?thesis
        by (auto simp: F_def fls_weierstrass_zeta_def)
    next
      case False
      have "fls_nth C n = 0"
        using \<open>fls_subdegree C = -1\<close> n False by simp
      thus ?thesis using n False
        by (auto simp: F_def fls_weierstrass_zeta_def)
    qed
  qed
  hence "\<not>is_pole f 0"
    using is_pole_0_imp_neg_fls_subdegree[OF F] by auto

  have "\<not>is_pole f z" for z
  proof (cases "z \<in> \<Lambda>")
    case True
    thus ?thesis
      using \<open>\<not>is_pole f 0\<close> f.poles.lattice_cong[of z 0] by (auto simp: rel_def)
  next
    case False
    hence "f analytic_on {z}"
      unfolding f_def f_aux_def using Im_ratio_pos theta_11_eq_0_iff[of z]
      by (auto intro!: remove_sings_analytic_on analytic_intros
               simp: theta_11_def[abs_def] theta_11'_def)
    thus ?thesis
      using analytic_at_imp_no_pole by auto
  qed

  text \<open>
    It follows that $f(z) = c$ for some constant $c$.
  \<close>
  hence "elliptic_order f = 0"
    using f.elliptic_order_eq_0_iff_no_poles by blast
  hence "f constant_on UNIV"
    using f.elliptic_order_eq_0_iff by metis
  then obtain c where c: "\<And>z. f z = c"
    by (auto simp: constant_on_def)

  text \<open>
    Since $f$ is odd, this constant must be 0. This concludes the proof.
  \<close>
  have "c = 0"
  proof -
    have "f (-(\<omega>1 / 2)) = -f (\<omega>1 / 2)"
      by (rule f_uminus) auto
    thus ?thesis
      by (simp add: c)
  qed

  have "f_aux z = f z"
    unfolding f_def by (rule sym, rule remove_sings_at_analytic) (auto intro!: f_aux_ana z)
  also have "\<dots> = 0"
    using c by (simp add: \<open>c = 0\<close>)
  finally show "\<zeta> z = \<theta>\<^sub>1\<^sub>1'(z) / \<theta>\<^sub>1\<^sub>1(z) + \<eta> \<omega>1 / \<omega>1 * z"
    unfolding f_aux_def by (simp add: field_simps)
qed

text \<open>
  Next, we show that:
    \[\sigma(z) = \frac{\vartheta_{11}(z)}{\vartheta_{11}'(0)}\,
         \exp\left(z^2 \frac{\eta(\omega_1)}{2\omega_1}\right)\]
\<close>
theorem weierstrass_sigma_conv_jacobi_theta:
  assumes z: "z \<notin> \<Lambda>"
  shows "weierstrass_sigma z = \<theta>\<^sub>1\<^sub>1(z) / \<theta>\<^sub>1\<^sub>1'(0) * exp (z ^ 2 * weierstrass_eta \<omega>1 / (2 * \<omega>1))"
proof -
  write weierstrass_sigma ("\<sigma>")
  write weierstrass_zeta ("\<zeta>")
  write weierstrass_eta ("\<eta>")

  text \<open>
    We first let $f(z) = \exp(\eta(\omega_1)z^2/(2\omega_1))$ and 
    $g(z) = \sigma(z)/(f(z)\vartheta_{11}(z))$.
  \<close>
  define f where "f = (\<lambda>z. exp (\<eta> \<omega>1 * z^2 / (2*\<omega>1)))"
  define g where "g = (\<lambda>z. \<sigma> z / (f z * \<theta>\<^sub>1\<^sub>1(z)))"

  have [derivative_intros]: "(f has_field_derivative (\<eta> \<omega>1 / \<omega>1 * z * f z)) (at z)" for z
    by (auto simp: f_def intro!: derivative_eq_intros)
  have [simp]: "f z \<noteq> 0" for z
    by (auto simp: f_def)

  text \<open>
    With our previous identity for $\zeta$, we can easily see that $g'$ vanishes everywhere and
    therefore $g$ is constant.
  \<close>
  have "g constant_on (-\<Lambda>)"
  proof (rule has_field_derivative_0_imp_constant_on)
    show "(g has_field_derivative 0) (at z)" if z: "z \<in> -\<Lambda>" for z using z
      by (auto simp: g_def theta_11_eq_0_iff field_simps weierstrass_zeta_conv_jacobi_theta
               intro!: derivative_eq_intros)
  next
    have "connected (UNIV - \<Lambda>)"
      by (rule connected_open_diff_countable) auto
    also have "UNIV - \<Lambda> = -\<Lambda>"
      by auto
    finally show "connected (-\<Lambda>)" .
  qed (use closed_lattice in auto)
  then obtain c where c: "g z = c" if "z \<notin> \<Lambda>" for z
    by (auto simp: constant_on_def)

  text \<open>
    By examining the limit of $g(z)$ as $z\to 1$, we find that $c = 1/\vartheta_{11}'(0)$.
    This concludes the proof.
  \<close>
  have c_eq: "c = 1 / \<theta>\<^sub>1\<^sub>1'(0)"
  proof -
    have "(\<lambda>z. weierstrass_sigma.f z / (f z * (\<theta>\<^sub>1\<^sub>1(z) / z))) \<midarrow>0\<rightarrow>
            (weierstrass_sigma.f 0 / (f 0 * \<theta>\<^sub>1\<^sub>1'(0)))"
    proof (intro tendsto_intros isContD[of _ weierstrass_sigma.f] isContD[of _ f])
      have "(theta_11 has_field_derivative \<theta>\<^sub>1\<^sub>1'(0)) (at 0)"
        by (auto intro!: derivative_eq_intros)
      thus "(\<lambda>x. \<theta>\<^sub>1\<^sub>1(x) / x) \<midarrow>0\<rightarrow> \<theta>\<^sub>1\<^sub>1'(0)"
        by (simp add: has_field_derivative_iff theta_11_def)
    qed (auto simp: f_def intro!: analytic_at_imp_isCont analytic_intros)
    also have "?this \<longleftrightarrow> ((\<lambda>_::complex. c) \<midarrow>0\<rightarrow> (1 / \<theta>\<^sub>1\<^sub>1'(0)))"
    proof (intro filterlim_cong arg_cong[of _ _ nhds])
      show "\<forall>\<^sub>F z in at 0. weierstrass_sigma.f z / (f z * (\<theta>\<^sub>1\<^sub>1(z) / z)) = c"
        using eventually_neq_at_within[of 0] eventually_not_in_lattice_at
      proof eventually_elim
        case (elim z)
        have "weierstrass_sigma.f z / (f z * (\<theta>\<^sub>1\<^sub>1(z) / z)) = g z"
          by (auto simp: weierstrass_sigma_def g_def)
        thus ?case
          using elim by (simp add: c)
      qed
    qed (auto simp: f_def)
    finally show "c = 1 / \<theta>\<^sub>1\<^sub>1'(0)"
      by (simp add: tendsto_const_iff)
  qed

  have "g z = c"
    using z by (rule c)
  thus ?thesis
    by (simp add: g_def c_eq f_def field_simps)
qed

text \<open>
  As a useful corollary, we deduce the following expression for the $z^3$ coefficient in
  the series expansion of $\vartheta_{11}$. This will later lead us to a formula relating
  $\eta(\omega_1)$ and $\eta(\omega_2)$ to $G_2$.
\<close>
lemma fps_theta_11_3: "fps_nth fps_theta_11 3 = -\<theta>\<^sub>1\<^sub>1'(0) * weierstrass_eta \<omega>1 / (2 * \<omega>1)"
proof -
  write weierstrass_zeta ("\<zeta>")
  write weierstrass_eta ("\<eta>")
  define B where "B = fps_nth fps_theta_11 3"
  define f where "f = (\<lambda>z. \<zeta> z - \<theta>\<^sub>1\<^sub>1'(z) / \<theta>\<^sub>1\<^sub>1(z) - \<eta> \<omega>1 / \<omega>1 * z)"
  define H where "H = fps_to_fls (fps_deriv fps_theta_11) / fps_to_fls fps_theta_11"
  define F where "F = fls_weierstrass_zeta - H - fls_const (\<eta> \<omega>1 / \<omega>1) * fls_X"

  have "F = 0"
  proof (rule zero_has_laurent_expansion_imp_eq_0)
    have "f has_laurent_expansion F" unfolding f_def F_def H_def
      by (intro laurent_expansion_intros has_laurent_expansion_fps fps_expansion_intros)
    also have "?this \<longleftrightarrow> (\<lambda>_. 0) has_laurent_expansion F"
    proof (rule has_laurent_expansion_cong)
      show "\<forall>\<^sub>F z in at 0. f z = 0"
        using eventually_not_in_lattice_at
        by eventually_elim (auto simp: f_def weierstrass_zeta_conv_jacobi_theta)
    qed auto
    finally show "(\<lambda>_. 0) has_laurent_expansion F" .
  qed

  have [simp]: "subdegree (fps_deriv fps_theta_11) = 0"
    by (rule subdegreeI) (auto simp: fps_theta_11_1)

  have H1: "fls_nth H 1 = 2 * B / \<theta>\<^sub>1\<^sub>1'(0)"
  proof -
    define H1 where "H1 = fps_deriv fps_theta_11"
    define H2 where "H2 = fps_shift 1 fps_theta_11"
    have "fps_nth H2 0 \<noteq> 0"
      by (auto simp: H2_def fps_theta_11_1)
    hence [simp]: "H2 \<noteq> 0" and [simp]: "subdegree H2 = 0"
      by auto
    note [simp] = \<open>fps_nth H2 0 \<noteq> 0\<close>
    have *: "fps_nth (inverse H2) 2 = -B / \<theta>\<^sub>1\<^sub>1'(0) ^ 2"
      by (simp add: fps_inverse_def eval_nat_numeral H2_def fps_theta_11_1 field_simps B_def)

    have "H = fps_to_fls H1 / fps_to_fls (fps_X * H2)"
      using fps_conv_fps_X_power_mult_fps_shift[of fps_theta_11 1]
      by (simp add: H_def H1_def H2_def)
    also have "\<dots> = fls_shift 1 (fps_to_fls H1 / fps_to_fls H2)"
      by (simp add: fls_times_fps_to_fls field_simps fls_X_times_conv_shift(1) fls_divide_shift_denom)
    also have "fps_to_fls H1 / fps_to_fls H2 = fps_to_fls (H1 / H2)"
      by (rule fls_divide_fps_to_fls) auto
    also have "fls_nth (fls_shift 1 \<dots>) 1 = fps_nth (H1 * inverse H2) 2"
      by (simp add: fps_divide_unit)
    also have "\<dots> = 2 * B / \<theta>\<^sub>1\<^sub>1'(0)"
      using * by (simp add: fps_mult_nth eval_nat_numeral H1_def H2_def fps_theta_11_1 field_simps B_def)
    finally show "fls_nth H 1 = 2 * B / \<theta>\<^sub>1\<^sub>1'(0)"
      by simp
  qed

  have "0 = fls_nth F 1"
    by (simp add: \<open>F = 0\<close>)
  thus ?thesis
    by (auto simp: field_simps F_def fls_weierstrass_zeta_def B_def
                   fps_weierstrass_zeta_def H1 add_eq_0_iff)
qed

end


context std_complex_lattice
begin

sublocale complex_lattice_Im_pos 1 \<tau>
  rewrites "ratio = \<tau>"
  by unfold_locales (auto simp: ratio_def Im_\<tau>_pos)

end

unbundle no jacobi_theta_nw_notation

end