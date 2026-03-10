section \<open>Connection between complex lattices and theta functions\<close>
theory Complex_Lattices_Theta
  imports "Elliptic_Functions.Eisenstein_Series" "Theta_Functions.Theta_Nullwert"
begin

(* TODO Move *)
lemma analytic_at_continuation:
  assumes "eventually (\<lambda>z. f z = g z) (at z)" "f analytic_on {z}" "g analytic_on {z}"
  shows   "f z = g z"
proof -
  have "isCont (\<lambda>z. f z - g z) z"
    by (intro analytic_at_imp_isCont analytic_intros assms)
  hence "(\<lambda>z. f z - g z) \<midarrow>z\<rightarrow> (f z - g z)"
    by (rule isContD)
  also have "?this \<longleftrightarrow> (\<lambda>z. 0) \<midarrow>z\<rightarrow> (f z - g z)"
    by (intro filterlim_cong eventually_mono[OF assms(1)]) auto
  finally show "f z = g z"
    by (simp add: tendsto_const_iff)
qed

(* TODO Move *)
lemma analytic_on_continuation:
  assumes "eventually (\<lambda>z. f z = g z) (cosparse B)" "f analytic_on A" "g analytic_on A" "z \<in> A \<inter> B"
  shows   "f z = g z"
  using analytic_at_continuation[of f g z] assms analytic_on_subset
  by (auto dest: eventually_cosparse_imp_eventually_at)

unbundle jacobi_theta_nw_notation


text \<open>
  We make the connection to theta functions. In order to do that, we first assume that the
  generators $\omega_1$ and $\omega_2$ are such that their ratio $\tau := \omega_2/\omega_1$ has
  positive imaginary part.
\<close>
locale complex_lattice_Im_pos = complex_lattice +
  assumes Im_ratio_pos': "Im (\<omega>2 / \<omega>1) > 0"
begin

definition ratio :: complex ("\<tau>") where "\<tau> = \<omega>2 / \<omega>1"

lemma Im_ratio_pos: "Im \<tau> > 0"
  using Im_ratio_pos' by (simp add: ratio_def)

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

text \<open>
  By comparing the zeros of $\wp(z) - e_2$ and $(\theta_{01}(z)/\theta_{11}(z))^2$ we
  find that the two functions are identical up to a constant factor, which we then determine
  to be $(pi\theta_{10}(0)\theta_{00}(0)/\omega_1)^2$ by comparing the Laurent series expansions
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
  define B where "B = fps_expansion theta_11 0"
  have A[fps_expansion_intros]: "theta_01 has_fps_expansion A"
    unfolding A_def theta_01_def
    by (intro analytic_at_imp_has_fps_expansion_0 analytic_intros) (use Im_ratio_pos in auto)
  have B[fps_expansion_intros]: "theta_11 has_fps_expansion B"
    unfolding B_def theta_11_def
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

  have B0: "fps_nth B 0 = 0"
    using has_fps_expansion_imp_0_eq_fps_nth_0[OF B] by (simp add: theta_11_def)
  have B1: "fps_nth B (Suc 0) = deriv theta_11 0"
    using fps_nth_fps_expansion[OF B, of 1] by simp
  have B1': "fps_nth B (Suc 0) = 
               -(of_real pi * theta_00 0 * theta_01 0 * theta_10 0 / \<omega>1)"
  proof -
    have "(((\<lambda>x. jacobi_theta_11 x \<tau>) \<circ> (\<lambda>x. x / \<omega>1)) has_field_derivative 
            (deriv (\<lambda>x. jacobi_theta_11 x \<tau>) (0 / \<omega>1) * (1 / \<omega>1))) (at 0)"
      unfolding B1 using Im_ratio_pos
      by (intro DERIV_chain analytic_derivI analytic_intros)
         (auto intro!: derivative_eq_intros)
    hence "(theta_11 has_field_derivative  (deriv (\<lambda>x. jacobi_theta_11 x \<tau>) 0 / \<omega>1)) (at 0)"
      by (simp add: o_def theta_11_def [abs_def])
    thus ?thesis
      unfolding B1 using Im_ratio_pos
      by (intro DERIV_imp_deriv) 
         (simp add: deriv_jacobi_theta_11_at_0 theta_00_def theta_01_def theta_10_def mult_ac)
  qed
  have B1_nz: "fps_nth B (Suc 0) \<noteq> 0"
    by (auto simp: B1' theta_00_eq_0_iff theta_01_eq_0_iff theta_10_eq_0_iff 
                   rel_def uminus_in_lattice_iff)
  have [simp]: "B \<noteq> 0"
    using B1_nz by auto
  have [simp]: "subdegree B = 1"
    by (rule subdegreeI) (auto simp: B1_nz B0)
  have B1_nz: "fps_nth B (Suc 0) \<noteq> 0"
    using nth_subdegree_nonzero[of B] by (simp del: nth_subdegree_nonzero)
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

  define F where "F = ((fps_to_fls A / fps_to_fls B) ^ 2 - fls_const c * (fls_weierstrass - fls_const \<e>\<^sub>2))"

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
  also have "\<dots> = fls_nth ((fps_to_fls A / fps_to_fls B)\<^sup>2) (- 2) - c"
    by (simp add: fls_weierstrass_def F_def)
  also have "-2 = int 2 * fls_subdegree (fps_to_fls A / fps_to_fls B)"
    by (subst fls_divide_subdegree) (auto simp: fls_subdegree_fls_to_fps)
  also have "fls_nth ((fps_to_fls A / fps_to_fls B) ^ 2) \<dots> = 
               (fls_nth (fps_to_fls A / fps_to_fls B) (-1))\<^sup>2"
    by (subst fls_pow_base) (auto simp: fls_divide_subdegree fls_subdegree_fls_to_fps)
  also have "-1 = fls_subdegree (fps_to_fls A) - fls_subdegree (fps_to_fls B)"
    by (simp add: fls_subdegree_fls_to_fps)
  also have "fls_nth (fps_to_fls A / fps_to_fls B) \<dots> = \<theta>\<^sub>0\<^sub>1(0) / fps_nth B (Suc 0)"
    by (subst fls_divide_nth_base) 
       (auto simp: fls_subdegree_fls_to_fps A0 B1 theta_01_def)
  finally have c_eq: "c = (\<theta>\<^sub>0\<^sub>1(0) / fps_nth B (Suc 0)) ^ 2"
    by simp

  have "\<wp> z = \<e>\<^sub>2 + (fps_nth B 1 / \<theta>\<^sub>0\<^sub>1(0)) ^ 2 * \<theta>\<^sub>0\<^sub>1(z) ^ 2 / \<theta>\<^sub>1\<^sub>1(z) ^ 2"
    using g_eq'[of z] theta_01_eq_0_iff[of 0] theta_11_eq_0_iff[of z] z B1_nz
    by (auto simp: c_eq g_def rel_def uminus_in_lattice_iff field_simps)
  also have "(fps_nth B 1 / \<theta>\<^sub>0\<^sub>1(0)) ^ 2 * \<theta>\<^sub>0\<^sub>1(z) ^ 2 / \<theta>\<^sub>1\<^sub>1(z) ^ 2 =
               (of_real pi * \<theta>\<^sub>1\<^sub>0(0) * \<theta>\<^sub>0\<^sub>0(0) / \<omega>1)\<^sup>2 * \<theta>\<^sub>0\<^sub>1(z)\<^sup>2 / \<theta>\<^sub>1\<^sub>1(z)\<^sup>2"
    by (simp add: B1' field_simps theta_01_eq_0_iff rel_def uminus_in_lattice_iff)
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

end

unbundle no jacobi_theta_nw_notation

end