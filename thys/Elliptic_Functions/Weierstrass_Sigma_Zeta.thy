section \<open>The Weierstra\ss\ \<open>\<sigma>\<close> and \<open>\<zeta>\<close> Functions\<close>
theory Weierstrass_Sigma_Zeta
  imports Eisenstein_Series Elliptic_Functions_Library
begin

(*<*)
lemmas [simp del] = div_add div_diff div_mult_self1 div_mult_self2 div_mult_self3 div_mult_self4
(*>*)

subsection \<open>The \<open>\<sigma>\<close> function\<close>

text \<open>
  We use a somewhat odd way to define the Weierstra\ss\ \<open>\<sigma>\<close> function as an infinite product.
  The product in question converges absolutely, but since at the time of writing this we had no
  theory for absolute convergence of products over infinite sets (only sequences), we pick an
  arbitrary sequence and do the product in that order.

  Now that a library of infinite products indexed by an arbitrary set is available one should
  probably switch to that. Maybe the existing Weierstra\ss\ factorisation theory can be generalised
  to the new more general products. Or maybe we can do this without using Weierstra\ss\ factorisation.
  Not sure what the best approach is.
\<close>

lemma (in weierstrass_product) zero_eq [simp]: "f 0 = 1"
proof -
  have "((\<lambda>x. 1) has_setprod f 0) I"
    using has_setprod[of 0] by simp
  moreover have "((\<lambda>x. 1) has_setprod 1) I"
    by simp
  ultimately show "f 0 = 1"
    by (rule has_setprod_unique)
qed

context complex_lattice
begin

sublocale weierstrass_sigma: weierstrass_product "\<lambda>z. z" "\<lambda>_. 2" "\<Lambda>\<^sup>*"
proof
  have "inf cofinite (principal \<Lambda>\<^sup>*) \<le> at_infinity"
  proof (rule filter_leI)
    fix P assume "eventually P (at_infinity :: complex filter)"
    then obtain R where R: "P x" if "norm x \<ge> R" for x
      by (auto simp: eventually_at_infinity)
    have "{x \<in> \<Lambda>\<^sup>*. \<not> P x} \<subseteq> \<Lambda> \<inter> ball 0 R"
      using R by force
    moreover have "finite (\<Lambda> \<inter> ball 0 R)"
      by (rule bounded_lattice_finite) auto
    ultimately have "finite {x \<in> \<Lambda>\<^sup>*. \<not> P x}"
      by (rule finite_subset)
    thus "eventually P (inf cofinite (principal \<Lambda>\<^sup>*))"
      unfolding eventually_inf_principal eventually_cofinite by simp
  qed
  thus "filterlim (\<lambda>z. z) at_infinity (inf cofinite (principal (\<Lambda>\<^sup>*)))"
    by (simp add: filterlim_def)
next
  fix r :: real
  assume r: "r > 0"
  have "(\<lambda>w. 1 / norm w ^ 3) summable_on \<Lambda>\<^sup>*"
    by (rule eisenstein_series_norm_summable) auto
  hence "(\<lambda>z. r ^ 3 * (1 / norm z ^ 3)) summable_on \<Lambda>\<^sup>*"
    by (intro summable_on_cmult_right)
  thus "(\<lambda>z. (r / norm z) ^ Suc 2) summable_on \<Lambda>\<^sup>*"
    by (simp add: field_simps)
qed auto

definition weierstrass_sigma :: "complex \<Rightarrow> complex" where
  "weierstrass_sigma z = z * weierstrass_sigma.f z"

lemma has_field_derivative_weierstrass_sigma_0:
  "(weierstrass_sigma has_field_derivative 1) (at 0)"
  unfolding weierstrass_sigma_def
  by (auto intro!: derivative_eq_intros analytic_derivI[OF weierstrass_sigma.analytic])

lemma deriv_weierstrass_sigma_0 [simp]: "deriv weierstrass_sigma 0 = 1"
  by (rule DERIV_imp_deriv, rule has_field_derivative_weierstrass_sigma_0)

lemma analytic_on_weierstrass_sigma [analytic_intros]:
  assumes "f analytic_on A"
  shows   "(\<lambda>z. weierstrass_sigma (f z)) analytic_on A"
proof -
  have "weierstrass_sigma \<circ> f analytic_on A"
    unfolding weierstrass_sigma_def [abs_def] 
    by (intro analytic_on_compose assms analytic_intros)
  thus ?thesis
    by (simp add: o_def)
qed

lemma holomorphic_on_weierstrass_sigma [holomorphic_intros]:
  assumes "f holomorphic_on A"
  shows   "(\<lambda>z. weierstrass_sigma (f z)) holomorphic_on A"
proof -
  have "weierstrass_sigma \<circ> f holomorphic_on A"
    unfolding weierstrass_sigma_def [abs_def] 
    by (intro holomorphic_on_compose assms holomorphic_intros)
  thus ?thesis
    by (simp add: o_def)
qed

lemma continuous_on_weierstrass_sigma [continuous_intros]:
  assumes "continuous_on A f"
  shows   "continuous_on A (\<lambda>z. weierstrass_sigma (f z))"
  by (rule continuous_on_compose2[OF _ assms order.refl])
     (auto intro!: holomorphic_on_imp_continuous_on holomorphic_intros)

lemma weierstrass_sigma_altdef:
  "weierstrass_sigma z = 
     z * (\<Prod>\<^sub>\<infinity>w\<in>\<Lambda>\<^sup>*. (1 - z / w) * exp (z / w + z\<^sup>2 / (2 * w\<^sup>2)))"
  unfolding weierstrass_sigma_def weierstrass_sigma.f_def weierstrass_factor_def
  by (simp add: numeral_2_eq_2 Let_def mult_ac)

text \<open>
  The $\sigma$ function is odd:
\<close>
lemma weierstrass_sigma_uminus: "weierstrass_sigma (-z) = -weierstrass_sigma z"
proof -
  have "((\<lambda>x. weierstrass_factor 2 (z / x)) has_setprod weierstrass_sigma.f z) \<Lambda>\<^sup>*"
    by (rule weierstrass_sigma.has_setprod)
  also have "?this \<longleftrightarrow> ((\<lambda>x. weierstrass_factor 2 ((-z) / x)) has_setprod weierstrass_sigma.f z) \<Lambda>\<^sup>*"
    unfolding weierstrass_factor_def
    by (rule has_setprod_reindex_bij_witness[of _ "\<lambda>w. -w" "\<lambda>w. -w"])
       (auto simp: uminus_in_lattice0_iff)
  finally have "((\<lambda>x. weierstrass_factor 2 ((-z) / x)) has_setprod weierstrass_sigma.f z) \<Lambda>\<^sup>*"
    by (simp add: weierstrass_factor_def)
  moreover have "((\<lambda>x. weierstrass_factor 2 ((-z) / x)) has_setprod weierstrass_sigma.f (-z)) \<Lambda>\<^sup>*"
    by (rule weierstrass_sigma.has_setprod)
  ultimately have "weierstrass_sigma.f (-z) = weierstrass_sigma.f z"
    using has_setprod_unique by blast
  thus ?thesis
    by (simp add: weierstrass_sigma_def)
qed

lemma weierstrass_sigma_eq_0_iff: "weierstrass_sigma z = 0 \<longleftrightarrow> z \<in> \<Lambda>"
  by (simp add: weierstrass_sigma_def lattice_lattice0 weierstrass_sigma.zero)

lemma weierstrass_sigma_eq_0 [simp]: "z \<in> \<Lambda> \<Longrightarrow> weierstrass_sigma z = 0"
  by (subst weierstrass_sigma_eq_0_iff) auto

lemma has_zorder_weierstrass_sigma [zorder_intros]:
  "has_zorder weierstrass_sigma z (if z \<in> \<Lambda> then 1 else 0)"
proof -
  have 1: "has_zorder (\<lambda>z. z) z (if z = 0 then 1 else 0)"
    by (rule zorder_intros) auto
  have 2: "has_zorder weierstrass_sigma.f z (if z \<in> \<Lambda>\<^sup>* then 1 else 0)"
    using weierstrass_sigma.has_zorder[of z] by auto
  have "has_zorder weierstrass_sigma z ((if z = 0 then 1 else 0) + (if z \<in> \<Lambda>\<^sup>* then 1 else 0))"
    unfolding weierstrass_sigma_def using has_zorder_mult[OF 1 2 refl] .
  also have "((if z = 0 then 1 else 0) + (if z \<in> \<Lambda>\<^sup>* then 1 else 0)) = (if z \<in> \<Lambda> then 1 else 0 :: int)"
    by auto
  finally show ?thesis .
qed

lemma zorder_weierstrass_sigma:
  "zorder weierstrass_sigma z = (if z \<in> \<Lambda> then 1 else 0)"
  using has_zorder_weierstrass_sigma[of z] by (simp add: has_zorder_def)


subsection \<open>The \<open>\<zeta>\<close> function\<close>

text \<open>
  The Weierstra\ss\ \<open>\<zeta>\<close> function, the logarithmic derivative of the Weierstra\ss\ \<open>\<sigma>\<close>
  function. Not to be confused with the Riemann \<open>\<zeta>\<close> function.
\<close>
definition weierstrass_zeta :: "complex \<Rightarrow> complex" where
  "weierstrass_zeta z =
     (if z \<in> \<Lambda> then 0 else deriv weierstrass_sigma z / weierstrass_sigma z)"

lemma has_field_derivative_weierstrass_sigma [derivative_intros]:
  assumes "(f has_field_derivative f') (at z within A)" "f z \<notin> \<Lambda>"
  shows   "((\<lambda>z. weierstrass_sigma (f z)) has_field_derivative
             (f' * weierstrass_sigma (f z) * weierstrass_zeta (f z))) (at z within A)"
proof -
  have deriv: "(weierstrass_sigma has_field_derivative 
                 (weierstrass_sigma z * weierstrass_zeta z)) (at z)"
    if z: "z \<notin> \<Lambda>" for z
  proof -
    have "(weierstrass_sigma has_field_derivative deriv weierstrass_sigma z) (at z)"
      by (rule analytic_derivI) (auto intro!: analytic_intros)
    also have "deriv weierstrass_sigma z = weierstrass_sigma z * weierstrass_zeta z"
      using z by (simp add: weierstrass_zeta_def weierstrass_sigma_eq_0_iff)
    finally show ?thesis .
  qed

  have "((weierstrass_sigma \<circ> f) has_field_derivative 
          (weierstrass_sigma (f z) * weierstrass_zeta (f z) * f')) (at z within A)"
    by (intro DERIV_chain assms deriv)
  thus ?thesis
    by (simp add: o_def mult_ac)
qed

lemma has_log_derivative_weierstrass_sigma [derivative_intros]:
  assumes "(f has_field_derivative f') (at z within A)" "f z \<notin> \<Lambda>"
  shows   "((\<lambda>z. weierstrass_sigma (f z)) has_log_derivative
             (f' * weierstrass_zeta (f z))) (at z within A)"
proof (cases "at z within A = bot")
  case False
  thus ?thesis using assms
    by (auto simp: has_log_derivative_def Lim_ident_at weierstrass_sigma_eq_0_iff
             intro!: derivative_eq_intros)
qed auto

lemma has_field_derivative_weierstrass_sigma_aux:
  assumes w: "w \<notin> \<Lambda>"
  shows "(weierstrass_sigma.f has_field_derivative 
           (weierstrass_zeta w - 1 / w) * weierstrass_sigma.f w) (at w)"
proof -
  write weierstrass_sigma ("\<sigma>")
  write weierstrass_zeta ("\<zeta>")
  from w have [simp]: "w \<noteq> 0"
    by auto
  from w have "((\<lambda>w. \<sigma> w / w) has_field_derivative (w * \<zeta> w - 1) * \<sigma> w / w ^ 2) (at w)"
    by (auto intro!: derivative_eq_intros simp: field_simps power2_eq_square)
  also have "?this \<longleftrightarrow> (weierstrass_sigma.f has_field_derivative 
                         ((\<zeta> w - 1 / w) * weierstrass_sigma.f w)) (at w)"
  proof (rule DERIV_cong_ev)
    have "eventually (\<lambda>w. w \<in> -{0}) (nhds w)"
      by (intro eventually_nhds_in_open) (use w in auto)
    thus "eventually (\<lambda>w. \<sigma> w / w = weierstrass_sigma.f w) (nhds w)"
      by eventually_elim (auto simp: weierstrass_sigma_def)
  qed (auto simp: weierstrass_sigma_def power2_eq_square field_simps)
  finally show ?thesis .
qed

lemma analytic_on_weierstrass_zeta [analytic_intros]:
  assumes "f analytic_on A" "\<And>z. z \<in> A \<Longrightarrow> f z \<notin> \<Lambda>"
  shows   "(\<lambda>z. weierstrass_zeta (f z)) analytic_on A"
proof -
  have "(\<lambda>z. deriv weierstrass_sigma z / weierstrass_sigma z) analytic_on (-\<Lambda>)"
    by (intro analytic_intros) (auto simp: weierstrass_sigma_eq_0_iff)
  hence "(\<lambda>z. deriv weierstrass_sigma z / weierstrass_sigma z) holomorphic_on (-\<Lambda>)"
    by (rule analytic_imp_holomorphic)
  also have "?this \<longleftrightarrow> weierstrass_zeta holomorphic_on (-\<Lambda>)"
    by (rule holomorphic_cong) (auto simp: weierstrass_zeta_def)
  finally have "weierstrass_zeta analytic_on (-\<Lambda>)"
    by (subst analytic_on_open) (auto intro: closed_subset_lattice)
  hence "weierstrass_zeta analytic_on (f ` A)"
    by (rule analytic_on_subset) (use assms(2) in auto)
  hence "weierstrass_zeta \<circ> f analytic_on A"
    by (intro analytic_on_compose assms(1)) (use assms(2) in auto)
  thus ?thesis
    by (simp add: o_def)
qed

lemma holomorphic_on_weierstrass_zeta [holomorphic_intros]:
  assumes "f holomorphic_on A" "\<And>z. z \<in> A \<Longrightarrow> f z \<notin> \<Lambda>"
  shows   "(\<lambda>z. weierstrass_zeta (f z)) holomorphic_on A"
proof -
  have "weierstrass_zeta holomorphic_on (f ` A)"
    by (intro analytic_imp_holomorphic analytic_intros) (use assms in auto)
  hence "weierstrass_zeta \<circ> f holomorphic_on A"
    by (rule holomorphic_on_compose[OF assms(1)])
  thus ?thesis
    by (simp add: o_def)
qed

lemma meromorphic_on_weierstrass_zeta [meromorphic_intros]:
  assumes "f analytic_on A"
  shows   "(\<lambda>z. weierstrass_zeta (f z)) meromorphic_on A"
proof -
  have "(\<lambda>z. deriv weierstrass_sigma z / weierstrass_sigma z) meromorphic_on UNIV"
    by (auto intro!: meromorphic_intros analytic_intros
                     analytic_on_imp_meromorphic_on[of weierstrass_sigma])
  also have "eventually (\<lambda>z. z \<notin> \<Lambda>) (cosparse UNIV)"
    by (simp add: eventually_not_in_cosparse lattice_sparse)
  hence "eventually (\<lambda>z. deriv weierstrass_sigma z / weierstrass_sigma z = 
           weierstrass_zeta z) (cosparse UNIV)"
    by eventually_elim (auto simp: weierstrass_zeta_def)
  hence "(\<lambda>z. deriv weierstrass_sigma z / weierstrass_sigma z) meromorphic_on UNIV \<longleftrightarrow>
         weierstrass_zeta meromorphic_on UNIV"
    by (rule meromorphic_on_cong') auto
  finally have "weierstrass_zeta meromorphic_on UNIV" .
  thus ?thesis
    by (rule meromorphic_on_compose[OF _ assms(1)]) auto
qed

lemma continuous_on_weierstrass_zeta [continuous_intros]:
  assumes "continuous_on A f" "\<And>z. z \<in> A \<Longrightarrow> f z \<notin> \<Lambda>"
  shows   "continuous_on A (\<lambda>z. weierstrass_zeta (f z))"
  by (rule continuous_on_compose2[OF _ assms(1) order.refl])
     (use assms(2) in \<open>auto intro!: holomorphic_on_imp_continuous_on holomorphic_intros\<close>)

lemma has_zorder_weierstrass_zeta:
  assumes z: "z \<in> \<Lambda>"
  shows   "has_zorder weierstrass_zeta z (-1)"
proof -
  have "has_zorder (\<lambda>z. deriv weierstrass_sigma z / weierstrass_sigma z) z (-1)"
    by (rule has_zorder_logderiv has_zorder_weierstrass_sigma)+ (use z in auto)
  also have "?this \<longleftrightarrow> ?thesis"
  proof (rule has_zorder_cong_ev)
    have "eventually (\<lambda>z. z \<notin> \<Lambda>) (at z)"
      using not_islimpt_lattice[of z] by (auto simp: islimpt_iff_eventually)
    thus "\<forall>\<^sub>F z in at z. deriv weierstrass_sigma z / weierstrass_sigma z = weierstrass_zeta z"
      by eventually_elim (auto simp: weierstrass_zeta_def)
  qed auto
  finally show ?thesis .
qed

lemma uniform_limit_weierstrass_zeta:
  assumes K: "compact K" "K \<inter> \<Lambda> = {}"
  shows   "uniform_limit K (\<lambda>X z. \<Sum>w\<in>X. 1 / (z - w) + 1 / w + z / w\<^sup>2) 
             (\<lambda>z. weierstrass_zeta z - 1 / z) (finite_subsets_at_top \<Lambda>\<^sup>*)"
proof -
  have "uniform_limit K (\<lambda>J z. \<Sum>x\<in>J. (z / x)\<^sup>2 / (z - x))
          (\<lambda>z. deriv weierstrass_sigma.f z / weierstrass_sigma.f z) (finite_subsets_at_top \<Lambda>\<^sup>*)"
    by (rule weierstrass_sigma.uniform_limit_logderiv) (use assms in auto)
  also have "?this \<longleftrightarrow> ?thesis"
  proof (intro uniform_limit_cong eventually_finite_subsets_at_top_weakI ballI sum.cong refl)
    fix J z w assume "finite J" "J \<subseteq> \<Lambda>\<^sup>*" and z: "z \<in> K" and w: "w \<in> J"
    hence "w \<noteq> z" "w \<noteq> 0"
      using assms by auto
    thus "(z / w)\<^sup>2 / (z - w) = 1 / (z - w) + 1 / w + z / w\<^sup>2"
      by (simp add: field_simps power2_eq_square)
  next
    fix z assume "z \<in> K"
    hence z: "z \<noteq> 0" "z \<notin> \<Lambda>" "z \<notin> \<Lambda>\<^sup>*"
      using K by auto
    have "deriv weierstrass_sigma z = z * deriv weierstrass_sigma.f z + weierstrass_sigma.f z"
      unfolding weierstrass_sigma_def
      by (subst complex_derivative_mult_at) (use assms in \<open>auto intro!: analytic_intros\<close>)
    also have "\<dots> / weierstrass_sigma z = 1 / z + deriv weierstrass_sigma.f z / weierstrass_sigma.f z"
      using z by (auto simp: weierstrass_sigma_def field_simps weierstrass_sigma.zero)
    also have "deriv weierstrass_sigma z / weierstrass_sigma z = weierstrass_zeta z"
      using z by (simp add: weierstrass_zeta_def)
    finally show "deriv weierstrass_sigma.f z / weierstrass_sigma.f z = weierstrass_zeta z - 1 / z"
      by (simp add: field_simps)
  qed
  finally show ?thesis .
qed

lemma has_sum_weierstrass_zeta:
  assumes "z \<notin> \<Lambda>"
  shows   "((\<lambda>w. 1 / (z - w) + 1 / w + z / w\<^sup>2) has_sum (weierstrass_zeta z - 1 / z)) \<Lambda>\<^sup>*"
proof -
  have "uniform_limit {z} (\<lambda>X z. \<Sum>w\<in>X. 1 / (z - w) + 1 / w + z / w\<^sup>2) 
             (\<lambda>z. weierstrass_zeta z - 1 / z) (finite_subsets_at_top \<Lambda>\<^sup>*)"
    by (rule uniform_limit_weierstrass_zeta) (use assms in auto)
  thus ?thesis
    by (simp add: has_sum_def)
qed

text \<open>
  The Weierstra\ss\ \<open>\<zeta>\<close> function is odd as well:
\<close>
lemma weierstrass_zeta_uminus: "weierstrass_zeta (-z) = -weierstrass_zeta z"
proof (cases "z \<in> \<Lambda>")
  case z: False
  have "((\<lambda>z. weierstrass_sigma z + weierstrass_sigma (-z)) has_field_derivative
          (weierstrass_sigma z * (weierstrass_zeta z + weierstrass_zeta (-z)))) (at z)"
    using z weierstrass_sigma_uminus[of z]
    by (auto intro!: derivative_eq_intros simp: uminus_in_lattice_iff ring_distribs)
  hence "((\<lambda>z. 0) has_field_derivative 
           (weierstrass_sigma z * (weierstrass_zeta z + weierstrass_zeta (-z)))) (at z)"
    by (simp add: weierstrass_sigma_uminus)
  moreover have "((\<lambda>z. 0::complex) has_field_derivative 0) (at z)"
    by simp
  ultimately have "weierstrass_sigma z * (weierstrass_zeta z + weierstrass_zeta (-z)) = 0"
    by (rule DERIV_unique)
  thus "weierstrass_zeta (-z) = -weierstrass_zeta z"
    using z by (simp add: weierstrass_sigma_eq_0_iff add_eq_0_iff)
qed (auto simp: weierstrass_zeta_def uminus_in_lattice_iff)

text \<open>
  The derivative of \<open>\<zeta>\<close> is \<open>-\<wp>\<close>:
\<close>
theorem has_field_derivative_weierstrass_zeta:
  assumes z: "z \<notin> \<Lambda>"
  shows   "(weierstrass_zeta has_field_derivative (-\<wp> z)) (at z)"
proof -
  define f where "f = (\<lambda>z. weierstrass_zeta z - 1 / z)"
  have "open (-\<Lambda>)" "z \<in> -\<Lambda>"
    using closed_lattice z by auto
  then obtain R where R: "R > 0" "cball z R \<subseteq> -\<Lambda>"
    using open_contains_cball_eq by blast

  have *: "\<forall>\<^sub>F X in finite_subsets_at_top \<Lambda>\<^sup>*.
             continuous_on (cball z R) (\<lambda>z. \<Sum>w\<in>X. 1 / (z - w) + 1 / w + z / w\<^sup>2) \<and>
             (\<forall>z\<in>ball z R. ((\<lambda>z. \<Sum>w\<in>X. 1 / (z - w) + 1 / w + z / w\<^sup>2) has_field_derivative
                                 (\<Sum>w\<in>X. 1 / w\<^sup>2 - 1 / (z - w)\<^sup>2)) (at z))"
  proof (intro eventually_finite_subsets_at_top_weakI conjI ballI, goal_cases)
    case (1 X)
    thus ?case using R by (auto intro!: continuous_intros simp: lattice0_def)
  next
    case (2 X u)
    have "u \<notin> X" "0 \<notin> X"
      using R 2 by force+
    hence "((\<lambda>z. \<Sum>w\<in>X. 1 / (z - w) + 1 / w + z / w\<^sup>2) has_field_derivative
                (\<Sum>w\<in>X. w ^ 2 / w ^ 4 - 1 / (u - w)\<^sup>2)) (at u)"
      by (auto intro!: derivative_eq_intros sum.cong simp flip: power2_eq_square)
    also have "(\<Sum>w\<in>X. w ^ 2 / w ^ 4 - 1 / (u - w)\<^sup>2) = (\<Sum>w\<in>X. 1 / w ^ 2 - 1 / (u - w)\<^sup>2)"
      by (intro sum.cong) (auto simp: field_simps power_numeral_reduce)
    finally show ?case .
  qed

  obtain g where g:
     "(f has_field_derivative g w) (at w) \<and>
        ((\<lambda>wa. 1 / wa\<^sup>2 - 1 / (w - wa)\<^sup>2) has_sum g w) \<Lambda>\<^sup>*" 
   if "w \<in> ball z R" for w
    unfolding has_sum_def f_def
    by (rule has_complex_derivative_uniform_limit[OF * uniform_limit_weierstrass_zeta])
       (use R in auto)
  have "(f has_field_derivative g z) (at z)"
    using g[of z] \<open>R > 0\<close> by auto
  hence "((\<lambda>w. f w + 1 / w) has_field_derivative (g z - 1 / z ^ 2)) (at z)"
    using z by (auto intro!: derivative_eq_intros simp: power2_eq_square)
  hence deriv: "(weierstrass_zeta has_field_derivative (g z - 1 / z ^ 2)) (at z)"
    by (simp add: f_def)

  have "((\<lambda>w. 1 / w\<^sup>2 - 1 / (z - w)\<^sup>2) has_sum g z) \<Lambda>\<^sup>*"
    using g[of z] \<open>R > 0\<close> by (auto simp: has_sum_iff)
  hence "((\<lambda>w. 1 / (z - w)\<^sup>2 - 1 / w\<^sup>2) has_sum (-g z)) \<Lambda>\<^sup>*"
    by (subst has_sum_uminus [symmetric]) auto
  moreover have "((\<lambda>w. 1 / (z - w)\<^sup>2 - 1 / w\<^sup>2) has_sum weierstrass_fun_aux z) \<Lambda>\<^sup>*"
    by (rule weierstrass_fun_aux_has_sum) (use z in auto)
  ultimately have eq: "weierstrass_fun_aux z = -g z"
    using has_sum_unique by blast

  from deriv show "(weierstrass_zeta has_field_derivative (-\<wp> z)) (at z)"
    using z by (simp add: weierstrass_fun_def eq)
qed

lemma has_field_derivative_weierstrass_zeta' [derivative_intros]:
  assumes "(f has_field_derivative f') (at z within A)" "f z \<notin> \<Lambda>"
  shows   "((\<lambda>z. weierstrass_zeta (f z)) has_field_derivative (-f' * \<wp> (f z))) (at z within A)"
proof -
  have "((weierstrass_zeta \<circ> f) has_field_derivative ((-\<wp> (f z)) * f')) (at z within A)"
    by (rule DERIV_chain[OF has_field_derivative_weierstrass_zeta[OF assms(2)] assms(1)])
  thus ?thesis
    by (simp add: o_def mult_ac)
qed

lemma deriv_weierstrass_zeta:
  assumes "z \<notin> \<Lambda>"
  shows   "deriv weierstrass_zeta z = -\<wp> z"
  by (rule DERIV_imp_deriv) (use assms in \<open>auto intro!: derivative_eq_intros\<close>)


subsection \<open>Series expansions\<close>

text \<open>
  Lastly, we look at the series expansion of $\zeta(z)$ and $\sigma(z)$ at $z = 0$.

  The expansion of $\zeta$ has the following form:
  \[\zeta(z) = \frac{1}{z} - \sum_{k\geq 3} G_{k+1} z^k\]
\<close>

definition fps_weierstrass_zeta :: "complex fps" where
  "fps_weierstrass_zeta = Abs_fps (\<lambda>k. if k < 3 then 0 else -eisenstein_series (Suc k))"

definition fls_weierstrass_zeta :: "complex fls" where
  "fls_weierstrass_zeta = fls_X_intpow (-1) + fps_to_fls fps_weierstrass_zeta"

lemma fps_deriv_weierstrass_zeta: "fps_deriv fps_weierstrass_zeta = -fps_weierstrass"
proof (rule fps_ext)
  fix n
  show "fps_nth (fps_deriv fps_weierstrass_zeta) n = fps_nth (-fps_weierstrass) n"
    by (cases "n = 1") (auto simp: fps_weierstrass_zeta_def fps_weierstrass_def not_less)
qed

lemma fls_deriv_weierstrass_zeta: "fls_deriv fls_weierstrass_zeta = -fls_weierstrass"
  by (simp add: fls_weierstrass_zeta_def fls_weierstrass_def fls_deriv_fps_to_fls
                fls_deriv_shift fps_deriv_weierstrass_zeta)

lemma has_laurent_expansion_weierstrass_zeta [laurent_expansion_intros]:
  "weierstrass_zeta has_laurent_expansion fls_weierstrass_zeta"
proof -
  have [simp]: "fls_nth fls_weierstrass_zeta 0 = 0"
    by (simp add: fls_weierstrass_zeta_def fps_weierstrass_zeta_def)
  have "weierstrass_zeta meromorphic_on {0}"
    by (auto intro!: meromorphic_intros)
  then obtain F where F: "weierstrass_zeta has_laurent_expansion F"
    by (auto simp: meromorphic_on_def)

  have "((\<lambda>z. -weierstrass_zeta z) \<circ> (\<lambda>z. -z)) has_laurent_expansion (fls_compose_fps (-F) (-fps_X))"
    by (intro has_laurent_expansion_compose F has_laurent_expansion_fps 
              laurent_expansion_intros fps_expansion_intros) auto
  hence "weierstrass_zeta has_laurent_expansion (fls_compose_fps (-F) (-fps_X))"
    by (auto simp: o_def weierstrass_zeta_uminus)
  with F have "fls_compose_fps (-F) (-fps_X) = F"
    using has_laurent_expansion_unique by blast
  hence "fls_nth (fls_compose_fps (-F) (-fps_X)) 0 = fls_nth F 0"
    by (rule arg_cong)
  hence [simp]: "fls_nth F 0 = 0"
    using fls_nth_fls_compose_fps_linear[of "-1" F 0] by (simp flip: fps_const_neg)

  have "deriv weierstrass_zeta has_laurent_expansion fls_deriv F"
    by (intro laurent_expansion_intros F)
  also have "?this \<longleftrightarrow> (\<lambda>z. -\<wp> z) has_laurent_expansion fls_deriv F"
  proof (rule has_laurent_expansion_cong)
    have "eventually (\<lambda>z. z \<notin> \<Lambda>) (at 0)"
      by (rule eventually_not_in_lattice_at)
    thus "\<forall>\<^sub>F z in at 0. deriv weierstrass_zeta z = -\<wp> z"
      by eventually_elim (auto simp: deriv_weierstrass_zeta)
  qed auto
  finally have "(\<lambda>z. -\<wp> z) has_laurent_expansion fls_deriv F" .
  moreover have "(\<lambda>z. -\<wp> z) has_laurent_expansion (-fls_weierstrass)"
    by (intro laurent_expansion_intros)
  ultimately have "fls_deriv F = fls_deriv fls_weierstrass_zeta"
    using has_laurent_expansion_unique unfolding fls_deriv_weierstrass_zeta by blast
  hence "F = fls_weierstrass_zeta"
    by (simp add: fls_deriv_eq_iff)
  thus ?thesis
    using F by simp
qed

lemma residue_weierstrass_zeta: "residue weierstrass_zeta 0 = 1"
  using has_laurent_expansion_residue_0[OF has_laurent_expansion_weierstrass_zeta]
  by (simp add: fls_weierstrass_zeta_def)



text \<open>
  The expansion for $\sigma$ has the following form:
  \[\sigma(z) = z \exp\left( \sum_{k\geq 3} \frac{G_k}{k} z^k \right)\]
\<close>

definition fps_weierstrass_sigma_aux1 :: "complex fps" where
  "fps_weierstrass_sigma_aux1 = 
     Abs_fps (\<lambda>k. if k \<le> 2 then 0 else eisenstein_series k / of_nat k)"

definition fps_weierstrass_sigma_aux2 :: "complex fps" where
  "fps_weierstrass_sigma_aux2 = fps_compose (fps_exp (-1)) fps_weierstrass_sigma_aux1"

definition fps_weierstrass_sigma :: "complex fps" where
  "fps_weierstrass_sigma = fps_X * fps_weierstrass_sigma_aux2"

lemma fps_nth_0_weierstrass_sigma_aux2 [simp]:
  "fps_nth fps_weierstrass_sigma_aux2 0 = 1"
  by (simp add: fps_weierstrass_sigma_aux2_def)

lemma fps_nth_0_weierstrass_sigma [simp]:
  "fps_nth fps_weierstrass_sigma 0 = 0"
  by (simp add: fps_weierstrass_sigma_def)

lemma fps_weierstrass_sigma_aux2_nonzero [simp]: "fps_weierstrass_sigma_aux2 \<noteq> 0"
  by (auto simp: fps_weierstrass_sigma_aux2_def fps_compose_eq_0_iff fps_weierstrass_sigma_aux1_def)

lemma fps_weierstrass_sigma_nonzero [simp]: "fps_weierstrass_sigma \<noteq> 0"
  by (auto simp: fps_weierstrass_sigma_def)

lemma fps_nth_1_weierstrass_sigma [simp]:
  "fps_nth fps_weierstrass_sigma (Suc 0) = 1"
  by (simp add: fps_weierstrass_sigma_def)

lemma subdegree_fps_weierstrass_sigma_aux2 [simp]:
  "subdegree fps_weierstrass_sigma_aux2 = 0"
  by (rule subdegreeI) auto

lemma subdegree_fps_weierstrass_sigma [simp]:
  "subdegree fps_weierstrass_sigma = 1"
  by (rule subdegreeI) auto


lemma has_fps_expansion_weierstrass_sigma_aux [fps_expansion_intros]:
  "weierstrass_sigma.f has_fps_expansion fps_weierstrass_sigma_aux2"
proof -
  write weierstrass_sigma ("\<sigma>")
  write weierstrass_zeta ("\<zeta>")

  have "weierstrass_sigma.f analytic_on {0}"
    by (auto intro!: analytic_intros)
  then obtain F where F: "weierstrass_sigma.f has_fps_expansion F"
    using analytic_at_imp_has_fps_expansion_0 by blast
  have F': "weierstrass_sigma.f has_laurent_expansion (fps_to_fls F)"
    unfolding weierstrass_sigma_def by (intro has_laurent_expansion_fps fps_expansion_intros F)

  define H1 where "H1 = fps_weierstrass_sigma_aux1"
  define H2 where "H2 = fps_weierstrass_sigma_aux2"
  obtain c where c: "F = fps_const c * H2"
  proof (rule fps_logderiv_unique)
    have "fps_nth H2 0 \<noteq> fps_nth 0 0"
      by (auto simp: H2_def fps_weierstrass_sigma_aux2_def)
    thus "H2 \<noteq> 0"
      by blast
  next      
    have "deriv weierstrass_sigma.f has_laurent_expansion fls_deriv (fps_to_fls F)"
      by (intro laurent_expansion_intros F')
    also have "?this \<longleftrightarrow> (\<lambda>z. (\<zeta> z - 1 / z) * weierstrass_sigma.f z) has_laurent_expansion 
                            fls_deriv (fps_to_fls F)"
    proof (intro has_laurent_expansion_cong)
      show "eventually (\<lambda>w. deriv weierstrass_sigma.f w = (\<zeta> w - 1 / w) * weierstrass_sigma.f w) (at 0)"
        using eventually_not_in_lattice_at
      proof eventually_elim
        case (elim w)
        thus ?case by (intro DERIV_imp_deriv has_field_derivative_weierstrass_sigma_aux)
      qed
    qed auto
    finally have "(\<lambda>z. (\<zeta> z - 1 / z) * weierstrass_sigma.f z) has_laurent_expansion fls_deriv (fps_to_fls F)" .
    moreover have "(\<lambda>z. (\<zeta> z - 1 / z) * weierstrass_sigma.f z) has_laurent_expansion
                     ((fls_weierstrass_zeta - 1 / fls_X) * fps_to_fls F)"
      by (intro laurent_expansion_intros F')
    ultimately have "fls_deriv (fps_to_fls F) = (fls_weierstrass_zeta - 1 / fls_X) * fps_to_fls F"
      using has_laurent_expansion_unique by blast
    also have "\<dots> = fps_to_fls (F * fps_weierstrass_zeta)"
      by (simp add: fls_weierstrass_zeta_def fls_times_fps_to_fls)
    also have "fls_deriv (fps_to_fls F) = fps_to_fls (fps_deriv F)"
      by (simp add: fls_deriv_fps_to_fls)
    finally show "fps_deriv F = fps_weierstrass_zeta * F"
      by (simp add: mult_ac)
  next
    have [simp]: "fps_nth H1 0 = 0"
      by (simp add: H1_def fps_weierstrass_sigma_aux1_def)
    have "fps_deriv H1 = -fps_weierstrass_zeta"
    proof (rule fps_ext)
      show "fps_nth (fps_deriv H1) n = fps_nth (-fps_weierstrass_zeta) n" for n
        by (cases "n = 2")
           (auto simp: H1_def fps_weierstrass_zeta_def fps_weierstrass_sigma_aux1_def 
                 simp del: of_nat_Suc intro!: fps_ext)
    qed
    thus "fps_deriv H2 = fps_weierstrass_zeta * H2"
      by (simp add: H2_def fps_weierstrass_sigma_aux2_def fps_compose_deriv fps_compose_uminus
               flip: fps_const_neg H1_def)
  qed

  have "c = fps_nth (fps_const c * H2) 0"
    by (auto simp: H2_def fps_weierstrass_sigma_aux2_def)
  also have "\<dots> = fps_nth F 0"
    by (simp add: c)
  also have "\<dots> = 1"
    using has_fps_expansion_imp_0_eq_fps_nth_0[OF F] by simp
  finally have [simp]: "c = 1" .

  from F and c show ?thesis
    by (simp add: H2_def)
qed

theorem has_fps_expansion_weierstrass_sigma [fps_expansion_intros]:
  "weierstrass_sigma has_fps_expansion fps_weierstrass_sigma"
  unfolding weierstrass_sigma_def fps_weierstrass_sigma_def
  by (intro fps_expansion_intros)


subsection \<open>Quasiperiodicity and Legendre's relation\<close>

definition weierstrass_eta :: "complex \<Rightarrow> complex" where
  "weierstrass_eta \<omega> = 
     weierstrass_zeta (\<omega>1 / 2 + \<omega>) - weierstrass_zeta (\<omega>1 / 2)"

text \<open>
  The Weierstra\ss\ $\eta$ function gives the shifts induced in $\zeta$ by a lattice point.
\<close>
theorem weierstrass_zeta_plus_lattice:
  assumes \<omega>: "\<omega> \<in> \<Lambda>" and z: "z \<notin> \<Lambda>"
  shows   "weierstrass_zeta (z + \<omega>) = weierstrass_zeta z + weierstrass_eta \<omega>"
proof -
  define f where "f = (\<lambda>z. weierstrass_zeta (z + \<omega>) - weierstrass_zeta z)"
  have "f constant_on (-\<Lambda>)"
  proof (rule has_field_derivative_0_imp_constant_on)
    show "(f has_field_derivative 0) (at z)" if z: "z \<in> -\<Lambda>" for z
      unfolding f_def using \<omega> z
      by (auto intro!: derivative_eq_intros weierstrass_fun.lattice_cong 
               simp: rel_def uminus_in_lattice_iff)
  next
    have "connected (UNIV - \<Lambda>)"
      by (rule connected_open_diff_countable) auto
    also have "UNIV - \<Lambda> = -\<Lambda>"
      by auto
    finally show "connected (-\<Lambda>)" .
  qed (use closed_lattice in auto)
  then obtain c where c: "f z = c" if "z \<notin> \<Lambda>" for z
    by (auto simp: constant_on_def)
  have "f z = f (\<omega>1 / 2)"
    using z by (simp add: c)
  thus ?thesis
    by (simp add: f_def weierstrass_eta_def algebra_simps)
qed


text \<open>
  The Weierstra\ss\ $\eta$ function is a group homomorphism from \<^term>\<open>\<Lambda>\<close> to \<open>\<complex>\<close>.
  Hence the values $\eta_1 = \eta(\omega_1)$ and $\eta_2 = \eta(\omega_2)$ are of particular
  interest since they generate all the remaining ones.
\<close>
lemma weierstrass_eta_0 [simp]: "weierstrass_eta 0 = 0"
  by (simp add: weierstrass_eta_def)

lemma weierstrass_eta_add:
  assumes "\<omega> \<in> \<Lambda>" "\<omega>' \<in> \<Lambda>"
  shows   "weierstrass_eta (\<omega> + \<omega>') = weierstrass_eta \<omega> + weierstrass_eta \<omega>'"
  using weierstrass_zeta_plus_lattice[of \<omega> "\<omega>1 / 2"]
        weierstrass_zeta_plus_lattice[of \<omega>' "\<omega>1 / 2 + \<omega>"]
        weierstrass_zeta_plus_lattice[of "\<omega> + \<omega>'" "\<omega>1 / 2"] assms
  by (simp add: algebra_simps)

lemma weierstrass_eta_uminus:
  assumes "\<omega> \<in> \<Lambda>"
  shows   "weierstrass_eta (-\<omega>) = -weierstrass_eta \<omega>"
  using assms uminus_in_lattice weierstrass_eta_0 weierstrass_eta_add
  by (metis diff_minus_eq_add right_minus_eq)

lemma weierstrass_eta_diff:
  assumes "\<omega> \<in> \<Lambda>" "\<omega>' \<in> \<Lambda>"
  shows   "weierstrass_eta (\<omega> - \<omega>') = weierstrass_eta \<omega> - weierstrass_eta \<omega>'"
  using weierstrass_eta_add[of \<omega> "-\<omega>'"] assms
  by (simp add: weierstrass_eta_uminus uminus_in_lattice_iff)

lemma weierstrass_eta_of_nat_times_lattice:
  assumes "\<omega> \<in> \<Lambda>"
  shows   "weierstrass_eta (of_nat n * \<omega>) = of_nat n * weierstrass_eta \<omega>"
  by (induction n)
     (simp_all add: weierstrass_eta_add assms ring_distribs weierstrass_eta_add lattice_intros)

lemma weierstrass_eta_of_int_times_lattice:
  assumes "\<omega> \<in> \<Lambda>"
  shows   "weierstrass_eta (of_int n * \<omega>) = of_int n * weierstrass_eta \<omega>"
proof (cases "n \<ge> 0")
  case True
  define m where "m = nat n"
  have n_eq: "n = int m"
    using True by (auto simp: m_def)
  show ?thesis
    by (simp add: n_eq weierstrass_eta_of_nat_times_lattice assms)
next
  case False
  define m where "m = nat (-n)"
  have n_eq: "n = -int m"
    using False by (auto simp: m_def)
  show ?thesis
    by (simp add: n_eq weierstrass_eta_of_nat_times_lattice weierstrass_eta_uminus assms lattice_intros)
qed

lemma weierstrass_eta_of_\<omega>12_coords:
  "weierstrass_eta (of_\<omega>12_coords (of_int m, of_int n)) = 
     of_int m * weierstrass_eta \<omega>1 + of_int n * weierstrass_eta \<omega>2"
  by (simp add: of_\<omega>12_coords_def weierstrass_eta_add 
                weierstrass_eta_of_int_times_lattice lattice_intros)

lemma weierstrass_eta_conv_zeta:
  assumes "\<omega> \<in> \<Lambda>" "\<omega> / 2 \<notin> \<Lambda>"
  shows   "weierstrass_eta \<omega> = 2 * weierstrass_zeta (\<omega> / 2)"
  using weierstrass_zeta_plus_lattice[of \<omega> "-\<omega>/2"] assms
  by (simp add: uminus_in_lattice_iff weierstrass_zeta_uminus)

lemma weierstrass_eta1_conv_zeta: "weierstrass_eta \<omega>1 = 2 * weierstrass_zeta (\<omega>1 / 2)"
  and weierstrass_eta2_conv_zeta: "weierstrass_eta \<omega>2 = 2 * weierstrass_zeta (\<omega>2 / 2)"
  by (rule weierstrass_eta_conv_zeta; simp; fail)+


text \<open>
  Legendre's relation links $\eta_1$ and $\eta_2$. This is proven in a straightforward way by
  integrating $\zeta$ along a parallelogram-shaped contour not containing any lattice points.
  For convenience, we choose the one that starts at $\frac{1}{2}(\omega_1 + \omega_2)$.
\<close>
theorem legendre_relation:
  "\<omega>2 * weierstrass_eta \<omega>1 - \<omega>1 * weierstrass_eta \<omega>2 = of_real (2 * pi * sgn (Im (\<omega>2 / \<omega>1))) * \<i>"
proof -                          
  write weierstrass_zeta ("\<zeta>")
  write weierstrass_eta ("\<eta>")
  define z0 where "z0 = (-(\<omega>1 + \<omega>2) / 2)"
  define P where "P = period_parallelogram z0"
  define \<gamma> where "\<gamma> = parallelogram_path z0 \<omega>1 \<omega>2"

  have closure_P: "\<Lambda> \<inter> closure P = {0}"
  proof -
    have "closure P = of_\<omega>12_coords ` (\<lambda>(a,b). (a-1/2, b-1/2)) ` (cbox (0, 0) (1, 1))"
      unfolding P_def closure_period_parallelogram image_image z0_def
      by (simp add: of_\<omega>12_coords_def case_prod_unfold diff_divide_distrib algebra_simps)
    also have "\<Lambda> \<inter> \<dots> = {0}" (is "?lhs = ?rhs")
    proof (intro equalityI subsetI)
      fix z assume "z \<in> ?lhs"
      then obtain a b 
        where ab: "z = of_\<omega>12_coords (a - 1 / 2, b - 1 / 2)" "a \<in> {0..1}" "b \<in> {0..1}" 
                  "a - 1 / 2 \<in> \<int>" "b - 1 / 2 \<in> \<int>"
        by (auto simp: of_\<omega>12_coords_in_lattice_iff mem_box Basis_pair_def)
      then obtain m n where "a - 1 / 2 = of_int m" "b - 1 / 2 = of_int n"
        by (elim Ints_cases)
      hence mn: "a = of_int m + 1 / 2" "b = of_int n + 1 / 2"
        by auto
      from ab(2,3) have "m = 0 \<and> n = 0"
        by (auto simp: mn)
      with ab(1) show "z \<in> {0}"
        by (auto simp: mn)
    next
      fix z assume "z \<in> {0::complex}"
      hence "z \<in> \<Lambda>" "z = of_\<omega>12_coords ((\<lambda>(a,b). (a - 1/2, b - 1/2)) (1/2, 1/2))"
           "(1/2, 1/2) \<in> cbox (0, 0) (1 :: real, 1 :: real)"
        by auto
      thus "z \<in> ?lhs"
        by blast
    qed
    finally show ?thesis .
  qed

  have \<gamma>: "\<Lambda> \<inter> path_image \<gamma> = {}"
  proof -
    have "path_image \<gamma> = of_\<omega>12_coords ` (\<lambda>(a,b). (a-1/2, b-1/2)) ` (cbox (0, 0) (1, 1) - box (0, 0) (1, 1))"
      unfolding \<gamma>_def path_image_parallelogram_path' image_image z0_def
      by (simp add: of_\<omega>12_coords_def case_prod_unfold diff_divide_distrib algebra_simps)
    also have "\<Lambda> \<inter> \<dots> = {}"
      by (auto simp: of_\<omega>12_coords_in_lattice_iff mem_box Basis_pair_def)
    finally show ?thesis .
  qed

  have "compact (closure P)"
    unfolding P_def by auto
  then obtain R where R: "closure P \<subseteq> ball 0 R"
    using compact_imp_bounded bounded_subset_ballD by blast
  define A :: "complex set" where "A = ball 0 R"
  have A: "closure P \<subseteq> A"
    using R by (simp add: A_def)
  have fin: "finite (\<Lambda> \<inter> A)"
    by (rule bounded_lattice_finite) (auto simp: A_def)

  have "0 = z0 + of_\<omega>12_coords (1/2, 1/2)" "(1/2 :: real, 1/2::real) \<in> box (0, 0) (1, 1)"
    by (auto simp: z0_def of_\<omega>12_coords_def field_simps mem_box Basis_pair_def)
  hence "0 \<in> interior P"
    unfolding P_def interior_period_parallelogram by blast

  define s where "s = complex_of_real (sgn (Im (\<omega>2 / \<omega>1)))"
  have s: "s \<in> {-1, 1}"
    using fundpair by (auto simp: s_def sgn_if fundpair_def complex_is_Real_iff)
  
  have "contour_integral \<gamma> \<zeta> = of_real (2 * pi) * \<i> * (\<Sum>z\<in>\<Lambda>\<inter>A. winding_number \<gamma> z * residue \<zeta> z)"
  proof (rule Residue_theorem)
    show "open A" "connected A"
      by (auto simp: A_def)
  next
    show "\<zeta> holomorphic_on A - \<Lambda> \<inter> A"
      by (auto intro!: holomorphic_intros)
  next
    show "path_image \<gamma> \<subseteq> A - \<Lambda> \<inter> A"
      using A \<gamma> path_image_parallelogram_subset_closure[of z0] 
      by (auto simp: \<gamma>_def P_def)
  next
    show "finite (\<Lambda> \<inter> A)"
      by fact
  next
    show "\<forall>z. z \<notin> A \<longrightarrow> winding_number \<gamma> z = 0"
      using A unfolding \<gamma>_def P_def by (auto intro!: winding_number_parallelogram_outside)
  qed (auto simp: \<gamma>_def)
  also have "(\<Sum>p\<in>\<Lambda>\<inter>A. winding_number \<gamma> p * residue \<zeta> p) =
             (\<Sum>p\<in>{0::complex}. s)"
  proof (intro sum.mono_neutral_cong_right ballI, goal_cases)
    case (3 z)
    have "z \<notin> closure P"
      using closure_P using 3 by auto
    hence "winding_number \<gamma> z = 0"
      unfolding \<gamma>_def P_def using winding_number_parallelogram_outside by blast
    thus ?case
      by simp
  next
    case (4 z)
    with \<open>0 \<in> interior P\<close> have "winding_number \<gamma> z = s"
      unfolding \<gamma>_def by (subst winding_number_parallelogram_inside) (auto simp: s_def P_def)
    thus ?case using residue_weierstrass_zeta 4
      by simp
  next
    show "{0} \<subseteq> \<Lambda> \<inter> A"
      using \<open>0 \<in> interior P\<close> interior_subset[of P] closure_subset[of P] A by auto
  qed (use fin in auto)
  also have "\<dots> = s"
    by simp
  also have "contour_integral \<gamma> \<zeta> =
               contour_integral (linepath z0 (z0 + \<omega>1)) (\<lambda>x. \<zeta> x - \<zeta> (x + \<omega>2)) -
               contour_integral (linepath z0 (z0 + \<omega>2)) (\<lambda>x. \<zeta> x - \<zeta> (x + \<omega>1))" unfolding \<gamma>_def
    by (rule contour_integral_parallelogram_path')
       (use \<gamma> in \<open>auto intro!: continuous_intros simp: \<gamma>_def\<close>)
  also have "contour_integral (linepath z0 (z0 + \<omega>1)) (\<lambda>x. \<zeta> x - \<zeta> (x + \<omega>2)) =
             contour_integral (linepath z0 (z0 + \<omega>1)) (\<lambda>x. -\<eta> \<omega>2)"
  proof (intro contour_integral_cong refl)
    fix z assume "z \<in> path_image (linepath z0 (z0 + \<omega>1))"
    then obtain u where u: "u \<in> {0..1}" "z = linepath z0 (z0 + \<omega>1) u"
      unfolding path_image_def by blast
    have "z = of_\<omega>12_coords (u - 1 / 2, -1 / 2)"
      by (auto simp: of_\<omega>12_coords_def u(2) linepath_def scaleR_conv_of_real field_simps z0_def)
    also have "\<dots> \<notin> \<Lambda>"
      by (auto simp: of_\<omega>12_coords_in_lattice_iff)
    finally show "\<zeta> z - \<zeta> (z + \<omega>2) = -\<eta> \<omega>2"
      by (subst weierstrass_zeta_plus_lattice) auto
  qed
  also have "\<dots> = -\<eta> \<omega>2 * \<omega>1"
    by simp
  also have "contour_integral (linepath z0 (z0 + \<omega>2)) (\<lambda>x. \<zeta> x - \<zeta> (x + \<omega>1)) =
             contour_integral (linepath z0 (z0 + \<omega>2)) (\<lambda>x. -\<eta> \<omega>1)"
  proof (intro contour_integral_cong refl)
    fix z assume "z \<in> path_image (linepath z0 (z0 + \<omega>2))"
    then obtain u where u: "u \<in> {0..1}" "z = linepath z0 (z0 + \<omega>2) u"
      unfolding path_image_def by blast
    have "z = of_\<omega>12_coords (-1 / 2, u - 1 / 2)"
      by (auto simp: of_\<omega>12_coords_def u(2) linepath_def scaleR_conv_of_real field_simps z0_def)
    also have "\<dots> \<notin> \<Lambda>"
      by (auto simp: of_\<omega>12_coords_in_lattice_iff)
    finally show "\<zeta> z - \<zeta> (z + \<omega>1) = -\<eta> \<omega>1"
      by (subst weierstrass_zeta_plus_lattice) auto
  qed
  also have "\<dots> = -\<eta> \<omega>1 * \<omega>2"
    by simp
  finally show ?thesis
    by (auto simp: mult_ac s_def)
qed


text \<open>
  The $\sigma$ function satisfies a similar quasiperiodicity. We first derive the version that
  assumes $\frac{\omega}{2} \notin \Lambda$ and then use this to prove the general version.
\<close>
lemma weierstrass_sigma_plus_lattice_weak:
  assumes \<omega>: "\<omega> \<in> \<Lambda>" "\<omega> / 2 \<notin> \<Lambda>"
  shows "weierstrass_sigma (z + \<omega>) =
           -exp (weierstrass_eta \<omega> * (z + \<omega> / 2)) * weierstrass_sigma z"
proof (cases "z \<in> \<Lambda>")
  case True
  thus ?thesis
    using \<omega> by simp
next
  case z: False
  write weierstrass_sigma ("\<sigma>")
  write weierstrass_eta ("\<eta>")
  write weierstrass_zeta ("\<zeta>")
  define g where
    "g = (\<lambda>z. \<sigma> (z + \<omega>) / (exp (\<eta> \<omega> * z) * \<sigma> z))"

  have "g constant_on (-\<Lambda>)"
  proof (rule has_field_derivative_0_imp_constant_on)
    fix z assume z: "z \<in> -\<Lambda>"
    have "(g has_field_derivative 
            (\<sigma> z * \<sigma> (z + \<omega>) * exp (\<eta> \<omega> * z) * (\<zeta> (z + \<omega>) - \<zeta> z - \<eta> \<omega>) / (exp (\<eta> \<omega> * z) * \<sigma> z) ^ 2)) (at z)"
      using z \<omega> by (auto simp: g_def weierstrass_sigma_eq_0_iff simp: algebra_simps power2_eq_square
                         intro!: derivative_eq_intros)
    also have "\<zeta> (z + \<omega>) - \<zeta> z - \<eta> \<omega> = 0"
      by (subst weierstrass_zeta_plus_lattice) (use \<omega> z in auto)
    finally show "(g has_field_derivative 0) (at z)"
      by simp
  next
    have "connected (UNIV - \<Lambda>)"
      by (rule connected_open_diff_countable) auto
    also have "UNIV - \<Lambda> = -\<Lambda>" by auto
    finally show "connected (-\<Lambda>)" .
  qed (use closed_lattice in auto)

  then obtain c where c: "g z = c" if "z \<notin> \<Lambda>" for z
    by (auto simp: constant_on_def)
  have "c = g (-\<omega>/2)"
    using \<omega> by (simp add: c uminus_in_lattice_iff)
  also have "\<dots> = -exp (\<eta> \<omega> * \<omega> / 2)" using \<omega> 
    by (simp add: g_def weierstrass_sigma_uminus weierstrass_sigma_eq_0_iff exp_minus field_simps)
  finally have c_eq: "c = -exp (\<eta> \<omega> * \<omega> / 2)" .

  show ?thesis
    using c[of z] z
    by (simp add: g_def c_eq field_simps weierstrass_sigma_eq_0_iff flip: exp_add)
qed

theorem weierstrass_sigma_plus_lattice:
  assumes \<omega>: "\<omega> \<in> \<Lambda>"
  defines "\<epsilon> \<equiv> (if \<omega>/2 \<in> \<Lambda> then 1 else -1)"
  shows "weierstrass_sigma (z + \<omega>) =
           \<epsilon> * exp (weierstrass_eta \<omega> * (z + \<omega> / 2)) * weierstrass_sigma z"
proof -
  write weierstrass_sigma ("\<sigma>")
  write weierstrass_eta ("\<eta>")

  have 1: "\<sigma> (z + of_nat n * \<omega>) = 
          (if even n then 1 else -1) * exp (of_nat n * \<eta> \<omega> * (z + of_nat n * \<omega> / 2)) * \<sigma> z"
    if \<omega>: "\<omega> \<in> \<Lambda>" "\<omega> / 2 \<notin> \<Lambda>" for n \<omega> z
  proof (induction n)
    case (Suc n)
    have "\<sigma> (z + of_nat (Suc n) * \<omega>) = \<sigma> (z + of_nat n * \<omega> + \<omega>)"
      by (simp add: algebra_simps)
    also have "\<dots> = -exp (\<eta> \<omega> * (z + of_nat n * \<omega> + \<omega> / 2)) * \<sigma> (z + of_nat n * \<omega>)"
      by (subst weierstrass_sigma_plus_lattice_weak) (use \<omega> in auto)
    also have "\<dots> = (if even (Suc n) then 1 else -1) * 
                       exp (\<eta> \<omega> * (z + of_nat n * \<omega> + \<omega> / 2) + of_nat n * \<eta> \<omega> * (z + of_nat n * \<omega> / 2)) * \<sigma> z"
      unfolding exp_add by (subst Suc.IH) (auto simp: algebra_simps)
    also have "\<eta> \<omega> * (z + of_nat n * \<omega> + \<omega> / 2) + of_nat n * \<eta> \<omega> * (z + of_nat n * \<omega> / 2) =
               of_nat (Suc n) * \<eta> \<omega> * (z + of_nat (Suc n) * \<omega> / 2)"
      by (simp add: field_simps)
    finally show ?case .
  qed auto

  have 2: "\<sigma> (z + of_int n * \<omega>) = 
            (if even n then 1 else -1) * exp (of_int n * \<eta> \<omega> * (z + of_int n * \<omega> / 2)) * \<sigma> z"
    if \<omega>: "\<omega> \<in> \<Lambda>" "\<omega> / 2 \<notin> \<Lambda>" for n \<omega> z
  proof (cases "n \<ge> 0")
    case True
    define m where "m = nat n"
    have n_eq: "n = int m"
      using True by (auto simp: m_def)
    show ?thesis
      using 1[of \<omega> z m] \<omega> by (simp add: n_eq)
  next
    case False
    define m where "m = nat (-n)"
    have n_eq: "n = -int m"
      using False by (auto simp: m_def)
    show ?thesis
      using 1[of "-\<omega>" z m] \<omega> by (simp add: n_eq uminus_in_lattice_iff weierstrass_eta_uminus)
  qed

  from assms obtain m n where \<omega>: "\<omega> = of_\<omega>12_coords (of_int m, of_int n)"
    by (auto simp: lattice_def elim!: Ints_cases)
  define c where "c = of_int (m * n) / 2 * (\<omega>2 * \<eta> \<omega>1 - \<omega>1 * \<eta> \<omega>2)"
  define s where "s = (if Im (\<omega>2 / \<omega>1) > 0 then 1 else -1 :: int)"

  have "\<sigma> (z + \<omega>) = \<sigma> (z + of_int m * \<omega>1 + of_int n * \<omega>2)"
    by (simp add: \<omega> of_\<omega>12_coords_def algebra_simps)
  also have "\<dots> = (if even n then 1 else -1) * 
                    exp (of_int n * \<eta> \<omega>2 * (z + of_int m * \<omega>1 + of_int n * \<omega>2 / 2)) *
                    \<sigma> (z + of_int m * \<omega>1)"
    by (subst 2) auto
  also have "\<dots> = (if even n = even m then 1 else -1) * 
                    exp (of_int n * \<eta> \<omega>2 * (z + of_int m * \<omega>1 + of_int n * \<omega>2 / 2) + 
                         of_int m * \<eta> \<omega>1 * (z + of_int m * \<omega>1 / 2)) * \<sigma> z"
    unfolding exp_add by (subst 2) (auto simp: mult_ac)
  also have "of_int n * \<eta> \<omega>2 * (z + of_int m * \<omega>1 + of_int n * \<omega>2 / 2) + 
               of_int m * \<eta> \<omega>1 * (z + of_int m * \<omega>1 / 2) =
             \<eta> \<omega> * (z + \<omega> / 2) - c" 
    unfolding \<omega> by (subst weierstrass_eta_of_\<omega>12_coords) 
                   (simp_all add: of_\<omega>12_coords_def field_simps c_def)
  also have "exp \<dots> = exp (\<eta> \<omega> * (z + \<omega> / 2)) / exp c"
    by (simp add: exp_diff)
  also have "c = of_int (m * n) * sgn (Im (\<omega>2 / \<omega>1)) * \<i> * pi"
    by (simp add: c_def legendre_relation)
  also have "\<dots> = of_int (m * n * s) * \<i> * pi"
    using ratio_not_in_Reals by (auto simp: s_def sgn_if ratio_def complex_is_Real_iff)
  also have "exp \<dots> = cis (of_int (m * n * s) * pi)"
    by (simp add: exp_eq_polar)
  also have "\<dots> = cis pi powi (m * n * s)"
    by (subst cis_power_int) auto
  also have "\<dots> = (-1) powi (m * n * s)"
    by simp
  also have "\<dots> = (-1) powi (m * n)"
    by (auto simp: s_def power_int_minus field_simps)
  also have "(if even n = even m then 1 else -1) * (exp (\<eta> \<omega> * (z + \<omega> / 2)) / \<dots>) * \<sigma> z =
             (if even m \<and> even n then 1 else -1) * exp (\<eta> \<omega> * (z + \<omega> / 2)) * \<sigma> z"
    by auto
  also have "even m \<and> even n \<longleftrightarrow> of_\<omega>12_coords (of_int m / 2, of_int n / 2) \<in> \<Lambda>"
    unfolding of_\<omega>12_coords_in_lattice_iff
    using of_int_div_of_int_in_Ints_iff[of m 2] of_int_div_of_int_in_Ints_iff[of n 2]
    by auto
  also have "of_\<omega>12_coords (of_int m / 2, of_int n / 2) = \<omega> / 2"
    by (auto simp: \<omega> of_\<omega>12_coords_def field_simps)
  finally show ?thesis
    by (simp add: \<epsilon>_def)
qed

end


subsection \<open>Expressing elliptic functions in terms of $\sigma$\<close>

subsubsection \<open>Multisets modulo lattice points\<close>

text \<open>
  In this section, we build some infrastructure to count the number of occurrences of a point
  in a multiset modulo the lattice.
\<close>

context complex_lattice
begin

definition count_rel :: "complex multiset \<Rightarrow> complex \<Rightarrow> nat" where
  "count_rel A z = size {# w \<in># A. rel w z #}"

lemma count_rel_eq_0_iff: "count_rel A z = 0 \<longleftrightarrow> (\<forall>w\<in>#A. \<not>rel w z)"
  by (auto simp: count_rel_def)

lemma count_rel_pos_iff: "count_rel A z > 0 \<longleftrightarrow> (\<exists>w\<in>#A. rel w z)"
  using count_rel_eq_0_iff[of A z] by auto

lemma count_rel_cong: "rel z z' \<Longrightarrow> count_rel A z = count_rel A z'"
  unfolding count_rel_def using rel_trans rel_sym by metis

lemma count_rel_to_fund_parallelogram:
  "count_rel (image_mset to_fund_parallelogram A) z = count_rel A z"
  by (simp add: count_rel_def filter_mset_image_mset)

lemma count_rel_empty [simp]: "count_rel {#} z = 0"
  by (simp_all add: count_rel_def)

lemma count_rel_add_mset [simp]:
  "count_rel (add_mset w A) z = (if rel w z then 1 else 0) + count_rel A z"
  by (auto simp: count_rel_def)

lemma count_rel_replicate_mset [simp]:
  "count_rel (replicate_mset n w) z = (if rel w z then n else 0)"
  by (induction n) (auto simp: count_rel_def)

lemma count_rel_add [simp]: "count_rel (A + B) z = count_rel A z + count_rel B z"
  by (simp_all add: count_rel_def)

lemma count_rel_sum [simp]: "count_rel (\<Sum>x\<in>A. f x) z = (\<Sum>x\<in>A. count_rel (f x) z)"
  by (induction A rule: infinite_finite_induct) auto

lemma count_rel_diff_subset:
  assumes "B \<subseteq># A"
  shows   "count_rel (A - B) z = count_rel A z - count_rel B z"
proof -
  define C where "C = A - B"
  have A_eq: "A = B + C"
    using assms unfolding C_def by (metis subset_mset.add_diff_inverse)
  have "count_rel A z - count_rel B z = count_rel C z"
    by (simp add: A_eq)
  thus ?thesis
    by (simp add: C_def)
qed

lemma sum_count_rel_eq_size:
  assumes "finite X" "\<And>x. x \<in># A \<Longrightarrow> \<exists>y\<in>X. rel x y" "X \<subseteq> period_parallelogram 0"
  shows   "(\<Sum>z\<in>X. count_rel A z) = size A"
proof -
  define A' where "A' = image_mset to_fund_parallelogram A"
  have "(\<Sum>z\<in>X. count_rel A z) = (\<Sum>z\<in>X. count_rel A' z)"
    by (simp add: A'_def count_rel_to_fund_parallelogram)
  also have "\<dots> = (\<Sum>z\<in>set_mset A'. count_rel A' z)"
  proof (intro sum.mono_neutral_right ballI)
    show "set_mset A' \<subseteq> X"
      using assms to_fund_parallelogram_unique by (auto simp: A'_def)
  next
    fix x assume "x \<in> X - set_mset A'"
    thus "count_rel A' x = 0"
      unfolding A'_def count_rel_to_fund_parallelogram
      using assms to_fund_parallelogram_unique[of _ x]
      by (fastforce simp: count_rel_def)
  qed fact+
  also have "\<dots> = (\<Sum>z\<in>set_mset A'. count A' z)"
  proof (intro sum.cong refl)
    fix z assume z: "z \<in># A'"
    hence "{# w \<in># A'. rel w z #} = {# w \<in># A'. w = z #}"
      by (intro filter_mset_cong) (auto simp: A'_def)
    thus "count_rel A' z = count A' z"
      by (simp add: count_rel_def count_conv_size_mset)
  qed
  also have "\<dots> = size A'"
    by (simp add: size_multiset_overloaded_eq)
  also have "\<dots> = size A"
    by (simp add: A'_def)
  finally show ?thesis .
qed


subsubsection \<open>Products and quotients of $\sigma$\<close>

text \<open>
  Next, we introduce a ``multiple \sigma'' function 
  \[\sigma_{A,B}(z) = \frac{\prod_{a\in A} \sigma(z-a)}{\prod_{b\in B} \sigma(z-b)}\]
  where $A$ and $B$ are multisets of complex numbers. Typically we will have $|A|=|B|$, since
  then $\sigma_{A,B}$ is elliptic.
\<close>

definition weierstrass_multi_sigma :: "complex multiset \<Rightarrow> complex multiset \<Rightarrow> complex \<Rightarrow> complex"
  where "weierstrass_multi_sigma A B = 
           (\<lambda>z. (\<Prod>w\<in>#A. weierstrass_sigma (z - w)) / (\<Prod>w\<in>#B. weierstrass_sigma (z - w)))"

lemma weierstrass_multi_sigma_eq_0_iff:
  "weierstrass_multi_sigma A B z = 0 \<longleftrightarrow> (\<exists>w\<in>#(A+B). rel w z)"
  by (force simp: weierstrass_multi_sigma_def weierstrass_sigma_eq_0_iff rel_def 
                  diff_in_lattice_commute)

lemma analytic_on_weierstrass_multi_sigma [analytic_intros]:
  assumes "f analytic_on X" "\<And>z w. z \<in> X \<Longrightarrow> w \<in># B \<Longrightarrow> \<not>rel (f z) w"
  shows   "(\<lambda>z. weierstrass_multi_sigma A B (f z)) analytic_on X"
  using assms unfolding weierstrass_multi_sigma_def
  by (auto intro!: analytic_intros simp: weierstrass_sigma_eq_0_iff rel_def)

lemma holomorphic_on_weierstrass_multi_sigma [holomorphic_intros]:
  assumes "f holomorphic_on X" "\<And>z w. z \<in> X \<Longrightarrow> w \<in># B \<Longrightarrow> \<not>rel (f z) w"
  shows   "(\<lambda>z. weierstrass_multi_sigma A B (f z)) holomorphic_on X"
  using assms unfolding weierstrass_multi_sigma_def
  by (auto intro!: holomorphic_intros simp: weierstrass_sigma_eq_0_iff rel_def)

lemma meromorphic_on_weierstrass_multi_sigma [meromorphic_intros]:
  assumes "f analytic_on X"
  shows   "(\<lambda>z. weierstrass_multi_sigma A B (f z)) meromorphic_on X"
  using assms unfolding weierstrass_multi_sigma_def
  by (intro meromorphic_intros) (auto intro!: analytic_on_imp_meromorphic_on analytic_intros)

text \<open>
  Obviously, the zero order of any point is the number of its occurrences in $A$ minus those
  in $B$, counted modulo lattice points.

  Note that this does allow points to be present in both $A$ and $B$. If that happens, they do
  cancel except for a removable singularity. This could be fixed using either a more careful
  definition or the \<^const>\<open>remove_sings\<close> operator, but it is not worth the effort.
\<close>
lemma has_zorder_weierstrass_multi_sigma:
  "has_zorder (weierstrass_multi_sigma A B) z (int (count_rel A z) - int (count_rel B z))"
proof -
  write weierstrass_sigma ("\<sigma>")
  define g where "g = (\<lambda>X z. \<Prod>w\<in>#X. \<sigma> (z - w))"
  have *: "has_zorder (g X) z (count_rel X z)" for X z
  proof -
    have "has_zorder (g X) z (\<Sum>w\<in>#X. if rel w z then 1 else 0)"
      unfolding g_def
    proof (rule zorder_intros)
      fix w assume w: "w \<in># X"
      have "has_zorder \<sigma> (z - w) (if z - w \<in> \<Lambda> then 1 else 0)"
        by (rule has_zorder_weierstrass_sigma)
      thus "has_zorder (\<lambda>z. \<sigma> (z - w)) z (if rel w z then 1 else 0)"
        by (auto simp: rel_def diff_in_lattice_commute has_zorder_shift' algebra_simps)
    qed
    also have "\<dots> = count_rel X z"
      by (induction X) auto
    finally show ?thesis .
  qed

  have "has_zorder (\<lambda>z. g A z / g B z) z 
          (int (count_rel A z) - int (count_rel B z))"
    using * * by (rule has_zorder_divide) auto
  thus ?thesis
    by (simp add: weierstrass_multi_sigma_def g_def)
qed

lemma nicely_meromorphic_weierstrass_multi_sigma [meromorphic_intros]:
  assumes "\<And>a b. a \<in># A \<Longrightarrow> b \<in># B \<Longrightarrow> \<not>rel a b"
  defines "f \<equiv> weierstrass_multi_sigma A B"
  shows "f nicely_meromorphic_on X"
  unfolding nicely_meromorphic_on_def
proof (intro conjI ballI)
  fix z assume "z \<in> X"
  show "is_pole f z \<and> f z = 0 \<or> f \<midarrow>z\<rightarrow> f z"
  proof (cases "\<exists>b\<in>#B. rel z b")
    case False
    hence "f \<midarrow>z\<rightarrow> f z"
      by (auto intro!: analytic_at_imp_isCont isContD analytic_intros simp: f_def)
    thus ?thesis by blast
  next
    case True
    with assms(1) have not_in_A: "\<forall>a\<in>#A. \<not>rel z a"
      using rel_trans rel_sym by blast
    define n where "n = int (count_rel B z)"
    have "has_zorder f z (int (count_rel A z) - int (count_rel B z))"
      unfolding f_def by (rule has_zorder_weierstrass_multi_sigma)
    also have "int (count_rel A z) = 0"
      using not_in_A by (simp add: count_rel_eq_0_iff rel_sym)
    finally have "has_zorder f z (-n)"
      by (simp add: n_def)
    moreover have "n > 0"
      using True by (auto simp: n_def count_rel_pos_iff rel_sym)
    ultimately have "is_pole f z"
      by (simp add: has_zorder_imp_is_pole_iff)
    moreover have "f z = 0"
      using True by (auto simp: f_def weierstrass_multi_sigma_eq_0_iff rel_sym)
    ultimately show ?thesis
      by blast
  qed
qed (auto intro!: meromorphic_intros simp: f_def)

end


locale elliptic_multiple_sigma = complex_lattice +
  fixes A B :: "complex multiset"
  assumes same_size: "size A = size B"
  assumes sum_eq: "sum_mset A = sum_mset B"
begin

sublocale elliptic_function \<omega>1 \<omega>2 "weierstrass_multi_sigma A B"
proof
  show "weierstrass_multi_sigma A B meromorphic_on UNIV" unfolding weierstrass_multi_sigma_def
    by (intro meromorphic_intros) (auto intro!: analytic_on_imp_meromorphic_on analytic_intros)
next
  write weierstrass_sigma ("\<sigma>")
  write weierstrass_eta ("\<eta>")
  have *: "weierstrass_multi_sigma A B (z + \<omega>) = weierstrass_multi_sigma A B z" 
    if \<omega>: "\<omega> \<in> \<Lambda>" "\<omega> / 2 \<notin> \<Lambda>" for z \<omega>
  proof -
    define n where "n = size A"
    define c where "c = (-1) ^ n * exp (of_nat n * (\<eta> \<omega> * (z + \<omega> / 2)))"
    have [simp]: "c \<noteq> 0"
      by (auto simp: c_def)

    have *: "(\<Prod>w\<in>#X. \<sigma> (z + \<omega> - w)) = c / exp (\<eta> \<omega> * sum_mset X) * (\<Prod>w\<in>#X. \<sigma> (z - w))"
      if "size X = n" for X
    proof -
      have "(\<Prod>w\<in>#X. \<sigma> (z + \<omega> - w)) = (\<Prod>w\<in>#X. -exp (\<eta> \<omega> * (z - w + \<omega> / 2)) * \<sigma> (z - w))"
      proof (intro arg_cong[of _ _ prod_mset] image_mset_cong)
        fix w assume w: "w \<in># X"
        have "\<sigma> (z + \<omega> - w) = \<sigma> (z - w + \<omega>)"
          by (simp add: algebra_simps)
        also have "\<dots> = -exp (\<eta> \<omega> * (z - w + \<omega> / 2)) * \<sigma> (z - w)"
          by (rule weierstrass_sigma_plus_lattice_weak) (use \<omega> in auto)
        finally show "\<sigma> (z + \<omega> - w) = \<dots>" .
      qed
      also have "\<dots> = (\<Prod>w\<in>#X. (-1) * exp (\<eta> \<omega> * (z - w + \<omega> / 2))) * (\<Prod>w\<in>#X. \<sigma> (z - w))"
        by (subst prod_mset.distrib) auto
      also have "\<dots> = (-1) ^ n * (\<Prod>w\<in>#X. exp (\<eta> \<omega> * (z - w + \<omega> / 2))) * (\<Prod>w\<in>#X. \<sigma> (z - w))"
        by (subst prod_mset.distrib) (auto simp: \<open>size X = n\<close>)
      also have "(\<Prod>w\<in>#X. exp (\<eta> \<omega> * (z - w + \<omega> / 2))) = exp (\<Sum>w\<in>#X. \<eta> \<omega> * (z - w + \<omega> / 2))"
        by (simp add: exp_sum_mset')
      also have "(\<Sum>w\<in>#X. \<eta> \<omega> * (z - w + \<omega> / 2)) = 
                   of_nat n * (\<eta> \<omega> * (z + \<omega> / 2)) - \<eta> \<omega> * sum_mset X"
        by (simp add: \<open>size X = n\<close> ring_distribs sum_mset.distrib sum_mset_subtractf 
                      sum_mset_distrib_left)
      finally show "(\<Prod>w\<in>#X. \<sigma> (z + \<omega> - w)) = c / exp (\<eta> \<omega> * sum_mset X) * (\<Prod>w\<in>#X. \<sigma> (z - w))"
        by (simp add: exp_diff c_def \<open>size X = n\<close>)
    qed

    show "weierstrass_multi_sigma A B (z + \<omega>) = weierstrass_multi_sigma A B z"
      using same_size by (simp add: weierstrass_multi_sigma_def * n_def exp_diff sum_eq)
  qed

  show "weierstrass_multi_sigma A B (z + \<omega>1) = weierstrass_multi_sigma A B z"
       "weierstrass_multi_sigma A B (z + \<omega>2) = weierstrass_multi_sigma A B z" for z
    using *[of \<omega>1] *[of \<omega>2] by simp_all
qed

end

locale nicely_elliptic_multiple_sigma = elliptic_multiple_sigma +
  assumes disjoint: "\<And>a b. a \<in># A \<Longrightarrow> b \<in># B \<Longrightarrow> \<not>rel a b"
begin

sublocale nicely_elliptic_function \<omega>1 \<omega>2 "weierstrass_multi_sigma A B"
  by standard (use disjoint in \<open>auto intro!: meromorphic_intros\<close>)

end



subsubsection \<open>Writing concrete elliptic functions in terms of $\sigma$\<close>

lemma (in elliptic_function) in_terms_of_sigma_explicit_aux:
  assumes "\<And>z. zorder f z = int (count_rel A z) - int (count_rel B z)"
  assumes "sum_mset A = sum_mset B"
  assumes "elliptic_order f > 0"
  shows "size A = size B"
proof -
  define P where "P = period_parallelogram 0"
  define P' where "P' = to_fund_parallelogram ` (set_mset (A + B))"

  have "((\<lambda>z. zorder f z) has_sum 0) P"
    using has_sum_zorder_0[of 0] \<open>elliptic_order f > 0\<close> by (simp add: P_def)
  also have "?this \<longleftrightarrow> ((\<lambda>z. zorder f z) has_sum 0) P'"
  proof (rule has_sum_cong_neutral)
    fix z assume "z \<in> P - P'"
    hence "count_rel A z = 0" "count_rel B z = 0"
      using to_fund_parallelogram_unique by (auto simp: P_def P'_def count_rel_eq_0_iff)
    thus "zorder f z = 0"
      by (simp add: assms(1))
  qed (auto simp: P'_def P_def)
  also have "\<dots> \<longleftrightarrow> ((\<Sum>z\<in>P'. zorder f z) = 0)"
    by (subst has_sum_finite_iff) (auto simp: P'_def)
  also have "(\<Sum>z\<in>P'. zorder f z) = int (\<Sum>z\<in>P'. count_rel A z) - int (\<Sum>z\<in>P'. count_rel B z)"
    by (simp add: assms(1) sum_subtractf)
  also have "\<dots> = int (size A) - int (size B)"
    by (subst (1 2) sum_count_rel_eq_size) (auto simp: P'_def)
  finally show "size A = size B"
    by simp
qed

text \<open>
  Consider an elliptic function $f$.
  Given a complete set of representatives of the zeros $A$ and the poles $B$
  (with the right multiplicities) such that $\sum A = \sum B$, we can write $f$ in terms of 
  the Weierstra\ss\ \<open>\<sigma>\<close> function as
  \[ f(z) = c \frac{\prod_{a\in A} \sigma(z-a)}{\prod_{b\in B} \sigma(z-b)} \]
  where $c$ is a constant. Note that $A$ and $B$ are multisets here.

  This is useful when trying to establish a relationship between \<open>\<sigma>\<close> and a particular elliptic
  function with known zeros and poles. Later, we will apply this to a function of the form
  $\wp(z) - \wp(z_0)$.
\<close>
lemma (in elliptic_function) in_terms_of_sigma_explicit:
  assumes "\<And>z. zorder f z = int (count_rel A z) - int (count_rel B z)"
  assumes "sum_mset A = sum_mset B"
  assumes "elliptic_order f > 0"
  obtains c where "c \<noteq> 0" "\<forall>\<^sub>\<approx>z. f z = c * weierstrass_multi_sigma A B z"
proof -
  define h where "h = (\<lambda>z. f z / weierstrass_multi_sigma A B z)"
  have "size A = size B"
    by (rule in_terms_of_sigma_explicit_aux) (use assms in auto)
  interpret construct: elliptic_multiple_sigma \<omega>1 \<omega>2 A B
    by standard (use \<open>size A = size B\<close> \<open>sum_mset A = sum_mset B\<close> in auto)
  interpret h: elliptic_function \<omega>1 \<omega>2 h
    unfolding h_def by (intro elliptic_function_intros)

  have "\<not>is_pole h z" for z
  proof -
    have "has_zorder h z 0"
      unfolding h_def
    proof (rule has_zorder_divide)
      show "has_zorder f z (zorder f z)"
        using avoid'[of 0] \<open>elliptic_order f > 0\<close>
        by (auto simp: has_zorder_def intro!: meromorphic_on_subset[OF meromorphic])
    next
      show "has_zorder (weierstrass_multi_sigma A B) z (zorder f z)"
        using assms(1)[of z] has_zorder_weierstrass_multi_sigma[of A B z] by simp
    qed auto
    thus "\<not>is_pole h z"
      using has_zorder_imp_is_pole_iff by blast
  qed
  hence "elliptic_order h = 0"
    using h.elliptic_order_eq_0_iff_no_poles by metis
  then obtain c where c: "\<forall>\<^sub>\<approx>z. h z = c"
    using h.elliptic_order_eq_0_iff_const_cosparse by blast

  have "\<forall>\<^sub>\<approx>z. \<forall>w\<in>#(A+B). \<not>rel z w"
    by (intro eventually_ball_finite ballI eventually_not_rel_cosparse) auto
  hence ev_nz: "\<forall>\<^sub>\<approx>z. weierstrass_multi_sigma A B z \<noteq> 0"
    by eventually_elim (auto simp: weierstrass_multi_sigma_eq_0_iff rel_sym)

  have "c \<noteq> 0"
  proof -
    have "\<forall>\<^sub>\<approx>z. f z \<noteq> 0"
      using avoid[of 0] \<open>elliptic_order f > 0\<close> by simp
    with ev_nz c have "\<forall>\<^sub>\<approx>(z::complex). c \<noteq> 0"
      by eventually_elim (auto simp: h_def)
    thus ?thesis
      by simp
  qed

  show ?thesis
  proof (rule that)
    have "\<forall>\<^sub>\<approx>z. \<forall>w\<in>#(A+B). \<not>rel z w"
      by (intro eventually_ball_finite ballI eventually_not_rel_cosparse) auto
    show "\<forall>\<^sub>\<approx>z. f z = c * weierstrass_multi_sigma A B z"
      using ev_nz c by eventually_elim (auto simp: h_def)
  qed fact+
qed

text \<open>
  For nicely elliptic functions we can slightly strengthen the conclusion from
  ``equal except at singularities'' to ``equal everywhere''.
\<close>
lemma (in nicely_elliptic_function) in_terms_of_sigma_explicit':
  assumes "\<And>z. zorder f z = int (count_rel A z) - int (count_rel B z)"
  assumes disjoint: "\<And>a b. a \<in># A \<Longrightarrow> b \<in># B \<Longrightarrow> \<not>rel a b"
  assumes "sum_mset A = sum_mset B"
  assumes "elliptic_order f > 0"
  obtains c where "c \<noteq> 0" "\<And>z. f z = c * weierstrass_multi_sigma A B z"
proof -
  obtain c where c: "c \<noteq> 0" "\<forall>\<^sub>\<approx>z. f z = c * weierstrass_multi_sigma A B z"
    by (rule in_terms_of_sigma_explicit[of A B]) (use assms in auto)
  have "size A = size B"
    by (rule in_terms_of_sigma_explicit_aux) (use assms in auto)
  interpret multi_sigma: nicely_elliptic_multiple_sigma \<omega>1 \<omega>2 A B
    by standard (use assms \<open>size A = size B\<close> in auto)
  show ?thesis
  proof (rule that[of c])
    fix z :: complex
    show "f z = c * weierstrass_multi_sigma A B z" using c(2)
      by (rule nicely_meromorphic_on_cosparse_eq_imp_eq) (auto intro!: meromorphic_intros)
  qed fact+
qed

text \<open>
  We now look at two concrete examples.

  First, we consider the function $f(z) = \wp(z) - \wp(z_0)$ for some $z_0\notin\Lambda$.
  This function has a double pole at every lattice point and a single zero at lattice equivalents
  of $\pm z_0$, except if $2z_0\in\Lambda$, in which case it has a double zero at lattice
  equivalents of $z_0$.

  In either case, the representatives $A = \{z_0, -z_0\}$ for the zeroes and $B = \{0, 0\}$ 
  for the poles satisfy the requirements of the theorem above and we obtain
  \[ \wp(z) - \wp(z_0) = c \frac{\sigma(z+z_0)\sigma(z-z_0)}{\sigma(z)^2}\]
  for some constant $c$.

  It remains to determine what the constant $c$ is. To do this, we inspect the leading coefficient
  of the Laurent series expansion of both sides at $z = 0$. More concretely, we multiply both sides
  with $z^2$ and take the limit as $z\to 0$. This way, we easily find that 
  $c = -\frac{1}{\sigma(z_0)^2}$ and therefore:
  \[\wp(z) = \wp(z_0) - \frac{\sigma(z+z_0)\sigma(z-z_0)}{\sigma(z)^2 \sigma(z_0)^2}\]
\<close>
theorem (in complex_lattice) weierstrass_fun_conv_sigma_half_period:
  assumes z0: "z0 \<notin> \<Lambda>" and z: "z \<notin> \<Lambda>"
  defines "\<sigma> \<equiv> weierstrass_sigma"
  shows "\<wp> z = \<wp> z0 - \<sigma> (z + z0) * \<sigma> (z - z0) / (\<sigma> z * \<sigma> z0)\<^sup>2"
proof -
  define g where "g = (\<lambda>z. \<wp> z - \<wp> z0)"
  interpret g: weierstrass_fun_minus_const \<omega>1 \<omega>2 z0 g
    by unfold_locales (use z0 in \<open>auto simp: g_def\<close>)
  write weierstrass_sigma ("\<sigma>")

  obtain c where c: "\<forall>\<^sub>\<approx>z. g z = c * \<sigma> (z - z0) * \<sigma> (z + z0) / \<sigma> z ^ 2"
  proof (rule g.affine.in_terms_of_sigma_explicit)
    show "elliptic_order g > 0"
      by (auto simp: g.order_eq)
  next
    show "zorder g z = int (count_rel {#z0, -z0#} z) - int (count_rel {#0, 0#} z)" for z
    proof -
      consider "z \<in> \<Lambda>" | "rel z z0 \<or> rel z (-z0)" | "z \<notin> \<Lambda>" "\<not>rel z z0 \<and> \<not>rel z (-z0)"
        by blast
      thus ?thesis
      proof cases
        assume z: "z \<in> \<Lambda>"
        have "\<not>rel z z0"
          using z0 z rel_lattice_trans_left by blast
        with z z0 show ?thesis
          by (subst g.zorder_pole_eq)
             (auto simp: is_pole_weierstrass_fun_iff zorder_weierstrass_fun_pole 
                         rel_def uminus_in_lattice_iff diff_in_lattice_commute)
      next
        assume z: "rel z z0 \<or> rel z (-z0)"
        from z have "z \<notin> \<Lambda>"
          using z0 rel_lattice_trans_left uminus_in_lattice_iff by blast
        have "2 * z0 \<in> \<Lambda> \<longleftrightarrow> rel z z0 \<and> rel z (-z0)"
        proof
          assume "2 * z0 \<in> \<Lambda>"
          hence "rel z z0 \<longleftrightarrow> rel z (-z0)"
            using add_in_lattice[of "z - z0" "2 * z0"] diff_in_lattice[of "z + z0" "2 * z0"]
            by (auto simp: add.commute rel_def)
          thus "rel z z0 \<and> rel z (-z0)"
            using z by auto
        next
          assume "rel z z0 \<and> rel z (-z0)"
          hence "rel z0 (-z0)"
            using rel_trans rel_sym by blast
          thus "2 * z0 \<in> \<Lambda>"
            by (auto simp: rel_def)
        qed
        with z \<open>z \<notin> \<Lambda>\<close> show ?thesis
          by (auto simp: g.zorder_zero_eq rel_def diff_in_lattice_commute uminus_in_lattice_iff)
      qed (auto simp: g.zorder_zero_eq' rel_def uminus_in_lattice_iff diff_in_lattice_commute)
    qed
  qed (auto simp: weierstrass_multi_sigma_def power2_eq_square mult_ac)

  have c_eq: "c = -1 / \<sigma> z0 ^ 2"
  proof -
    note [tendsto_intros] =
      isContD[of _ "\<lambda>z. \<sigma> (z - z0)"] isContD[of _ "\<lambda>z. \<sigma> (z + z0)"] isContD[of _ weierstrass_sigma.f]
    have "(\<lambda>z. z ^ 2 * \<wp> z - z ^ 2 * \<wp> z0 - c * \<sigma> (z - z0) * \<sigma> (z + z0) / weierstrass_sigma.f z ^ 2)
             \<midarrow>0\<rightarrow> (1 - 0 ^ 2 * \<wp> z0 - c * \<sigma> (0 - z0) * \<sigma> (0 + z0) / weierstrass_sigma.f 0 ^ 2)"
    proof (intro tendsto_intros analytic_at_imp_isCont analytic_intros)
      have *: "(\<lambda>z. z\<^sup>2 * \<wp> z) has_laurent_expansion (fls_X ^ 2 * fls_weierstrass)"
        by (intro laurent_expansion_intros)
      have "fls_subdegree (fls_X\<^sup>2 * fls_weierstrass) = 0"
        by (subst fls_subdegree_mult) (auto simp: fls_subdegree_weierstrass)
      hence "(\<lambda>z. z\<^sup>2 * \<wp> z) \<midarrow>0\<rightarrow> fls_nth (fls_X\<^sup>2 * fls_weierstrass) 0"
        using has_laurent_expansion_imp_tendsto_0[OF *] by simp
      also have "fls_nth (fls_X\<^sup>2 * fls_weierstrass) 0 = 1"
        by (simp add: fls_X_power_conv_shift_1 fls_X_intpow_times_conv_shift 
                      fls_weierstrass_def fps_weierstrass_def)
      finally show "(\<lambda>z. z\<^sup>2 * \<wp> z) \<midarrow>0\<rightarrow> 1" .
    qed auto
    also have "?this \<longleftrightarrow> (\<lambda>z::complex. 0) \<midarrow>0\<rightarrow> (1 + c * \<sigma> z0 ^ 2)"
    proof (rule filterlim_cong)
      have "eventually (\<lambda>z. g z = c * \<sigma> (z - z0) * \<sigma> (z + z0) / \<sigma> z ^ 2) (at 0)"
        using c by (auto simp: eventually_cosparse_open_eq)
      thus "\<forall>\<^sub>F x in at 0. x\<^sup>2 * \<wp> x - x\<^sup>2 * \<wp> z0 - c * \<sigma> (x - z0) * \<sigma> (x + z0) /
                                      (weierstrass_sigma.f x)\<^sup>2 = 0"
        using eventually_neq_at_within[of 0]
      proof eventually_elim
        case (elim z)
        thus ?case
          by (auto simp: g_def weierstrass_sigma_def[of z] field_simps power2_eq_square)
      qed
    qed (auto simp: weierstrass_sigma_uminus power2_eq_square mult_ac)
    finally have "0 = 1 + c * \<sigma> z0 ^ 2"
      by (simp add: tendsto_const_iff)
    thus "c = -1 / \<sigma> z0 ^ 2"
      using z0 by (auto simp: field_simps weierstrass_sigma_eq_0_iff add_eq_0_iff)
  qed

  have "g z = c * \<sigma> (z - z0) * \<sigma> (z + z0) / (\<sigma> z)\<^sup>2"
    using c
  proof (rule analytic_on_continuation)
    show "g analytic_on (-\<Lambda>)"
      by (auto simp: g_def intro!: analytic_intros)
    show "(\<lambda>z. c * \<sigma> (z - z0) * \<sigma> (z + z0) / \<sigma> z ^ 2) analytic_on (-\<Lambda>)"
      by (auto intro!: analytic_intros simp: weierstrass_sigma_eq_0_iff)
  qed (use z in auto)
  thus ?thesis
    by (simp add: g_def c_eq field_simps \<sigma>_def)
qed

text \<open>
  Next, we analogously derive a formula for $\wp'(z)$ interms of $\sigma$, namely:
  \[\wp'(z) = \frac{2}{\sigma(z)^3} \prod_{i=1,2,3} \frac{\sigma(z-h_i)}{\sigma(h_i)}\]
  where $h_1 = \frac{1}{2}\omega_1$, $h_2 = \frac{1}{2}\omega_2$, and 
  $h_3 = -\frac{1}{2}(\omega_1+\omega_2)$.
\<close>
theorem (in complex_lattice) weierstrass_fun_deriv_conv_sigma_half_period:
  defines "\<sigma> \<equiv> weierstrass_sigma"
  shows "\<wp>' z = 2 / \<sigma> z ^ 3 * (\<Prod>w\<leftarrow>[\<omega>1/2, \<omega>2/2, -(\<omega>1+\<omega>2)/2]. \<sigma> (z-w) / \<sigma> w)"
proof -
  write weierstrass_sigma ("\<sigma>")
  define h1 where "h1 = of_\<omega>12_coords (1/2, 0)"
  define h2 where "h2 = of_\<omega>12_coords (0, 1/2)"
  define h3 where "h3 = of_\<omega>12_coords (-1/2, -1/2)"
  have "h3 \<notin> \<Lambda>"
    using half_periods_notin_lattice(3) uminus_in_lattice_iff[of "(\<omega>1+\<omega>2)/2"]
    by (auto simp: h3_def add_divide_distrib diff_divide_distrib of_\<omega>12_coords_def minus_diff_commute)
  hence h123: "\<forall>h\<in>{h1,h2,h3}. h \<notin> \<Lambda> \<and> 2 * h \<in> \<Lambda>"
    by (auto simp: h1_def h2_def h3_def lattice_intros diff_divide_distrib of_\<omega>12_coords_def)
  have h123_unique: "\<not>rel h1 h2 \<and> \<not>rel h1 h3 \<and> \<not>rel h2 h3"
    unfolding h1_def h2_def h3_def rel_def of_\<omega>12_coords.diff [symmetric] of_\<omega>12_coords_in_lattice_iff
    by auto
  have zorder_h123: "\<forall>h\<in>{h1,h2,h3}. zorder \<wp>' h = 1"
    using h123 by (auto intro!: zorder_weierstrass_fun_deriv_zero)
  have [simp]: "zorder \<wp>' (to_fund_parallelogram z) = zorder \<wp>' z" for z
    by (rule weierstrass_fun_deriv.zorder.lattice_cong) auto
  have zorder_0: "zorder \<wp>' z = 0" if "z \<notin> \<Lambda>" "\<forall>h\<in>{h1,h2,h3}. \<not>rel z h" for z
  proof -
    have "rel ((\<omega>1 + \<omega>2) / 2) h3"
      by (auto simp: rel_def h3_def of_\<omega>12_coords_def diff_divide_distrib add_divide_distrib)
    hence *: "2 * z \<notin> \<Lambda>"
      using that rel_half_period[of z] rel_trans[of z "(\<omega>1+\<omega>2)/2" h3]
      by (auto simp: h1_def h2_def h3_def of_\<omega>12_coords_def)
    show ?thesis
    by (rule zorder_eq_0I) 
       (use that * in \<open>auto intro!: analytic_intros simp: weierstrass_fun_deriv_eq_0_iff\<close>)
  qed

  obtain c where c: "\<And>z. \<wp>' z = c * \<sigma> (z - h1) * \<sigma> (z - h2) * \<sigma> (z - h3) / \<sigma> z ^ 3"
  proof (rule weierstrass_fun_deriv.in_terms_of_sigma_explicit')
    show "elliptic_order \<wp>' > 0"
      by simp
  next
    show "zorder \<wp>' z = int (count_rel {#h1, h2, h3#} z) - int (count_rel {#0, 0, 0#} z)" for z
    proof -
      define z' where "z' = to_fund_parallelogram z"
      have rel_iff: "rel w z \<longleftrightarrow> to_fund_parallelogram w = z'" for w
        by (auto simp: z'_def simp flip: to_fund_parallelogram_eq_iff)
      have z_in_lattice_iff: "z \<in> \<Lambda> \<longleftrightarrow> z' = 0"
        by (auto simp: z'_def)
      have *: "zorder \<wp>' z = zorder \<wp>' z'"
        by (simp add: z'_def)
      show ?thesis
        using h123 h123_unique zorder_h123 zorder_0[of z]
        by (auto simp: rel_iff zorder_weierstrass_fun_deriv_pole rel_sym z_in_lattice_iff *)
    qed
  next
    fix a b :: complex
    assume "a \<in># {#h1, h2, h3#}" "b \<in># {#0, 0, 0#}"
    thus "\<not>rel a b"
      using h123 by (auto simp: rel_def)
  qed (auto simp: h1_def h2_def h3_def of_\<omega>12_coords_def weierstrass_multi_sigma_def 
                  mult_ac power_numeral_reduce)

  have c_eq: "c = 2 / (\<sigma> h1 * \<sigma> h2 * \<sigma> h3)"
  proof -
    note [tendsto_intros] =
      isContD[of _ "\<lambda>z. \<sigma> (z - w)" for w] isContD[of _ weierstrass_sigma.f]
    have "(\<lambda>z. z ^ 3 * \<wp>' z - c * \<sigma> (z - h1) * \<sigma> (z - h2) * \<sigma> (z - h3) / weierstrass_sigma.f z ^ 3)
             \<midarrow>0\<rightarrow> (-2 - c * \<sigma> (0 - h1) * \<sigma> (0 - h2) * \<sigma> (0 - h3) / weierstrass_sigma.f 0 ^ 3)"
    proof (intro tendsto_intros analytic_at_imp_isCont analytic_intros)
      have *: "(\<lambda>z. z ^ 3 * \<wp>' z) has_laurent_expansion (fls_X ^ 3 * fls_deriv fls_weierstrass)"
        by (intro laurent_expansion_intros)
      have "fls_subdegree (fls_X ^ 3 * fls_deriv fls_weierstrass) = 0"
      proof (subst fls_subdegree_mult)
        have "fls_nth (fls_deriv fls_weierstrass) (-3) \<noteq> fls_nth 0 (-3)"
          by (auto simp: fls_weierstrass_def)
        thus "fls_deriv fls_weierstrass \<noteq> 0"
          by metis
      qed (auto simp: fls_subdegree_weierstrass fls_subdegree_deriv)
      hence "(\<lambda>z. z ^ 3 * \<wp>' z) \<midarrow>0\<rightarrow> fls_nth (fls_X ^ 3 * fls_deriv fls_weierstrass) 0"
        using has_laurent_expansion_imp_tendsto_0[OF *] by simp
      also have "fls_nth (fls_X ^ 3 * fls_deriv fls_weierstrass) 0 = -2"
        by (simp add: fls_X_power_conv_shift_1 fls_X_intpow_times_conv_shift 
                      fls_weierstrass_def fps_weierstrass_def)
      finally show "(\<lambda>z. z ^ 3 * \<wp>' z) \<midarrow>0\<rightarrow> -2" .
    qed auto
    also have "?this \<longleftrightarrow> (\<lambda>z::complex. 0) \<midarrow>0\<rightarrow> (-2 + c * \<sigma> h1 * \<sigma> h2 * \<sigma> h3)"
    proof (rule filterlim_cong)
      have "eventually (\<lambda>z. \<wp>' z = c * \<sigma> (z - h1) * \<sigma> (z - h2) * \<sigma> (z - h3) / \<sigma> z ^ 3) (at 0)"
        using c by (auto simp: eventually_cosparse_open_eq)
      thus "\<forall>\<^sub>F x in at 0. x ^ 3 * \<wp>' x - c * \<sigma> (x - h1) * \<sigma> (x - h2) * \<sigma> (x - h3) /
                                      weierstrass_sigma.f x ^ 3 = 0"
        using eventually_neq_at_within[of 0]
      proof eventually_elim
        case (elim z)
        thus ?case
          by (auto simp: weierstrass_sigma_def[of z] field_simps power2_eq_square)
      qed
    qed (auto simp: weierstrass_sigma_uminus mult_ac)
    finally have "0 = -2 + c * \<sigma> h1 * \<sigma> h2 * \<sigma> h3"
      by (simp add: tendsto_const_iff)
    thus "c = 2 / (\<sigma> h1 * \<sigma> h2 * \<sigma> h3)"
      using h123 by (auto simp: field_simps weierstrass_sigma_eq_0_iff add_eq_0_iff)
  qed

  show ?thesis using c[of z]
    by (simp add: c_eq field_simps \<sigma>_def h1_def h2_def h3_def of_\<omega>12_coords_def minus_diff_commute)
qed


subsubsection \<open>Generic representation theorem in terms of $\sigma$\<close>

text \<open>
  Lastly, we prove a generic theorem for an arbitrary elliptic function, showing that it can
  be written in the form $c \cdot \sigma_{A,B}$ for an appropriate constant $c$ and
  multisets $A$ and $B$.

  The construction is fairly straightforward: $A$ consists of all zeros in the fundamental
  parallelogram (with appropriate multiplicities) and $B$ of all the poles. However, this will
  violate the condition that $\sum A = \sum B$, so we pick some arbitrary zero $a\in A$ and shift
  it by a lattice point in order to make things work out.
\<close>
theorem (in elliptic_function) in_terms_of_sigma:
  obtains c A B 
  where "size A = elliptic_order f" "\<And>z. z \<in># A \<Longrightarrow> isolated_zero f z"
        "size B = elliptic_order f" "\<And>z. z \<in># B \<Longrightarrow> is_pole f z"
        "sum_mset A = sum_mset B"
        "\<forall>\<^sub>\<approx>z. f z = c * weierstrass_multi_sigma A B z"
proof (cases "elliptic_order f = 0")
  case True
  then obtain c where c: "\<forall>\<^sub>\<approx>z. f z = c"
    using elliptic_order_eq_0_iff_const_cosparse by blast
  show ?thesis
    using that[of "{#}" "{#}" c] c True by (auto simp: weierstrass_multi_sigma_def)
next
  case False
  define P where "P = period_parallelogram 0"
  note fin = finite_poles_in_parallelogram[of 0, folded P_def]
             finite_zeros_in_parallelogram[of 0, folded P_def]
  define A where "A = (\<Sum>z | z \<in> P \<and> isolated_zero f z. replicate_mset (nat (zorder f z)) z)"
  define B where "B = (\<Sum>z | z \<in> P \<and> is_pole f z. replicate_mset (nat (-zorder f z)) z)"
  have "size A = elliptic_order f"
    using zeros_eq_elliptic_order[of 0] by (simp add: A_def P_def)
  have "size B = elliptic_order f"
    using poles_eq_elliptic_order[of 0] by (simp add: B_def P_def)
  have "A \<noteq> {#}"
    using False \<open>size A = _\<close> by auto
  then obtain a where a: "a \<in># A"
    by blast
  define d where "d = sum_mset A - sum_mset B"
  have "d \<in> \<Lambda>"
  proof -
    have "d = (\<Sum>z | z \<in> P \<and> isolated_zero f z. of_nat (nat (zorder f z)) * z) -
              (\<Sum>z | z \<in> P \<and> is_pole f z. of_nat (nat (- zorder f z)) * z)"
      by (simp add: d_def A_def B_def sum_mset_sum)
    also have "(\<Sum>z | z \<in> P \<and> isolated_zero f z. of_nat (nat (zorder f z)) * z) =
               (\<Sum>z | z \<in> P \<and> isolated_zero f z. of_int (zorder f z) * z)"
      using False by (intro sum.cong) (auto simp: isolated_zero_iff_zorder_pos)
    also have "(\<Sum>z | z \<in> P \<and> is_pole f z. of_nat (nat (- zorder f z)) * z) =
               (\<Sum>z | z \<in> P \<and> is_pole f z. -of_int (zorder f z) * z)"
      using False by (intro sum.cong) (auto simp: is_pole_iff_zorder_neg) 
    also have "(\<Sum>z | z \<in> P \<and> isolated_zero f z. of_int (zorder f z) * z) -
               (\<Sum>z | z \<in> P \<and> is_pole f z. -of_int (zorder f z) * z) =
               (\<Sum>z\<in>{z\<in>P. isolated_zero f z}\<union>{z\<in>P. is_pole f z}. of_int (zorder f z) * z)"
      using fin pole_is_not_zero[of f]
      by (subst sum.union_disjoint) (auto simp: sum_negf)
    also have "\<dots> = (\<Sum>z | z \<in> P \<and> (isolated_zero f z \<or> is_pole f z). of_int (zorder f z) * z)"
      by (rule sum.cong) auto
    also have "\<dots> \<in> \<Lambda>"
      using sum_zeros_poles_in_lattice[of 0, folded P_def] .
    finally show ?thesis .
  qed

  define a' where "a' = a - d"
  define A' where "A' = A - {#a#} + {#a'#}"
  have "size A' = elliptic_order f"
    using \<open>size A = _\<close> a by (simp add: A'_def size_Suc_Diff1)

  obtain c where c: "\<forall>\<^sub>\<approx>z. f z = c * weierstrass_multi_sigma A' B z"
  proof (rule in_terms_of_sigma_explicit[of A' B])
    fix z :: complex
    define P' where "P' = {w\<in>P. rel w z}"

    have [simp]: "card P' = 1"
    proof -
      have "P' = {to_fund_parallelogram z}"
        using to_fund_parallelogram_eq_iff[of z] to_fund_parallelogram_unique[of z]
        unfolding P'_def P_def by (auto simp: rel_sym)
      thus ?thesis
        by simp
    qed

    have 1: "count_rel A' z = nat (zorder f z)"
    proof -
      have "rel a a'"
        using \<open>d \<in> \<Lambda>\<close> by (auto simp: a'_def rel_def)
      moreover have "Suc (count_rel A z - Suc 0) = count_rel A z" if "rel a z"
        by (subst Suc_diff_Suc) (use that a in \<open>auto simp: count_rel_pos_iff\<close>)
      ultimately have "count_rel A' z = count_rel A z"
        using a rel_trans[of a a' z] rel_trans[of a' a z]
        by (auto simp: A'_def count_rel_diff_subset rel_sym)
      also have "\<dots> = (\<Sum>w | w \<in> P \<and> isolated_zero f w. if rel w z then nat (zorder f w) else 0)"
        by (auto simp: A_def count_rel_sum)
      also have "\<dots> = (\<Sum>w | w \<in> P' \<and> isolated_zero f z. nat (zorder f w))"
        by (rule sum.mono_neutral_cong_right) (use fin zeros.lattice_cong in \<open>auto simp: P'_def\<close>)
      also have "\<dots> = (\<Sum>w\<in>(if isolated_zero f z then P' else {}). nat (zorder f z))"
        by (intro sum.cong) 
           (auto intro!: arg_cong[of _ _ nat] zorder.lattice_cong simp: P'_def split: if_splits)
      also have "\<dots> = nat (zorder f z)"
        using False by (auto simp: isolated_zero_iff_zorder_pos)
      finally show "count_rel A' z = nat (zorder f z)" .
    qed

    have 2: "count_rel B z = nat (-zorder f z)"
    proof -
      have "count_rel B z = (\<Sum>w | w \<in> P \<and> is_pole f w. if rel w z then nat (-zorder f w) else 0)"
        by (auto simp: B_def count_rel_sum)
      also have "\<dots> = (\<Sum>w | w \<in> P' \<and> is_pole f z. nat (-zorder f w))"
        by (rule sum.mono_neutral_cong_right) (use fin poles.lattice_cong in \<open>auto simp: P'_def\<close>)
      also have "\<dots> = (\<Sum>w\<in>(if is_pole f z then P' else {}). nat (-zorder f z))"
        by (intro sum.cong) 
           (auto intro!: arg_cong[of _ _ nat] zorder.lattice_cong simp: P'_def split: if_splits)
      also have "\<dots> = nat (-zorder f z)"
        using False by (auto simp: is_pole_iff_zorder_neg)
      finally show "count_rel B z = nat (-zorder f z)" .
    qed

    show "zorder f z = int (count_rel A' z) - int (count_rel B z)"
      by (simp add: 1 2)
  next
    show "sum_mset A' = sum_mset B"
      using a by (simp add: A'_def sum_mset_diff a'_def d_def)
  qed (use False in auto)

  show ?thesis
  proof (rule that)
    show "size A' = elliptic_order f" "size B = elliptic_order f"
      by fact+
    from \<open>d \<in> \<Lambda>\<close> have "isolated_zero f a' \<longleftrightarrow> isolated_zero f a"
      by (intro zeros.lattice_cong) (auto simp: a'_def rel_def uminus_in_lattice_iff)
    thus "isolated_zero f z" if "z \<in># A'" for z
      using that fin a by (auto simp: A'_def A_def set_mset_sum dest!: in_diffD)
    show "is_pole f z" if "z \<in># B" for z
      using that fin by (auto simp: B_def set_mset_sum)
    show "\<forall>\<^sub>\<approx>z. f z = c * weierstrass_multi_sigma A' B z"
      by fact
    show "sum_mset A' = sum_mset B"
      using a by (simp add: A'_def sum_mset_diff a'_def d_def)
  qed
qed

lemma (in nicely_elliptic_function) in_terms_of_sigma':
  obtains c A B 
  where "size A = elliptic_order f" "\<And>z. z \<in># A \<Longrightarrow> isolated_zero f z"
        "size B = elliptic_order f" "\<And>z. z \<in># B \<Longrightarrow> is_pole f z"
        "\<And>z. f z = c * weierstrass_multi_sigma A B z"
proof -
  obtain c A B where cAB:
    "size A = elliptic_order f" "\<And>z. z \<in># A \<Longrightarrow> isolated_zero f z"
    "size B = elliptic_order f" "\<And>z. z \<in># B \<Longrightarrow> is_pole f z"
    "sum_mset A = sum_mset B"
    "\<forall>\<^sub>\<approx>z. f z = c * weierstrass_multi_sigma A B z"
    by (rule in_terms_of_sigma) auto
  have disjoint: "\<not>rel a b" if "a \<in># A" "b \<in># B" for a b
    using cAB(2,4) that pole_is_not_zero poles.lattice_cong by blast

  interpret multi_sigma: nicely_elliptic_multiple_sigma \<omega>1 \<omega>2 A B
    by standard (use cAB disjoint in auto)
  show ?thesis
  proof (rule that[of A B c])
    fix z :: complex
    show "f z = c * weierstrass_multi_sigma A B z" using cAB(6)
      by (rule nicely_meromorphic_on_cosparse_eq_imp_eq) (auto intro!: meromorphic_intros)
  qed fact+
qed


subsection \<open>Addition and duplication theorems\<close>

context complex_lattice
begin

theorem weierstrass_sigma_add_diff:
  assumes u: "u \<notin> \<Lambda>" and v: "v \<notin> \<Lambda>"
  shows "weierstrass_sigma (u + v) * weierstrass_sigma (u - v) =
           (\<wp> v - \<wp> u) * weierstrass_sigma u ^ 2 * weierstrass_sigma v ^ 2"
proof -
  write weierstrass_sigma ("\<sigma>")
  write weierstrass_eta ("\<eta>")

  text \<open>
    We consider the following function:
      \[g(u) = \frac{\sigma(u+v)\sigma(u-v)}{\sigma(u)^2\sigma(v)^2} + \wp(u)\]
  \<close>
  define g where "g = (\<lambda>u. \<sigma> (u + v) * \<sigma> (u - v) / (\<sigma> u * \<sigma> v)\<^sup>2 + \<wp> u)"

  text \<open>
    Due to the periodicity of \<open>\<wp>\<close> and the quasiperiodicity of \<open>\<sigma>\<close>, this is an ellpitic function.
  \<close>
  interpret g: elliptic_function \<omega>1 \<omega>2 g
  proof
    show "g meromorphic_on UNIV"
      by (auto simp: g_def intro!: meromorphic_intros)
         (auto intro!: analytic_on_imp_meromorphic_on analytic_intros)?
  next
    have *: "g (z + \<omega>) = g z" if \<omega>: "\<omega> \<in> \<Lambda>" "\<omega> / 2 \<notin> \<Lambda>" for \<omega> z
    proof -
      have "g (z + \<omega>) = \<sigma> (z + v + \<omega>) * \<sigma> (z - v + \<omega>) / (\<sigma> (z + \<omega>) * \<sigma> v)\<^sup>2 + \<wp> (z + \<omega>)"
        by (simp add: g_def algebra_simps)
      also have "\<dots> = exp (\<eta> \<omega> * (z + v + \<omega> / 2)) * exp (\<eta> \<omega> * (z - v + \<omega> / 2)) / 
                        exp (\<eta> \<omega> * (z + \<omega> / 2)) ^ 2 *
                      (\<sigma> (z + v) * \<sigma> (z - v) / (\<sigma> z * \<sigma> v)\<^sup>2) + \<wp> (z + \<omega>)"
        by (subst (1 2 3) weierstrass_sigma_plus_lattice_weak)
           (use \<omega> v in \<open>auto simp: weierstrass_sigma_eq_0_iff field_simps\<close>)
      also have "exp (\<eta> \<omega> * (z + v + \<omega> / 2)) * exp (\<eta> \<omega> * (z - v + \<omega> / 2)) /
                   exp (\<eta> \<omega> * (z + \<omega> / 2)) ^ 2 = 1"
        unfolding exp_of_nat_mult [symmetric] exp_add [symmetric] exp_diff [symmetric]
        by (simp add: algebra_simps)
      also have "\<wp> (z + \<omega>) = \<wp> z"
        by (rule weierstrass_fun.lattice_cong) (use \<omega> in \<open>auto simp: rel_def\<close>)
      also have "1 * (\<sigma> (z + v) * \<sigma> (z - v) / (\<sigma> z * \<sigma> v)\<^sup>2) + \<wp> z = g z"
        by (simp add: g_def)
      finally show ?thesis .
    qed
    show "g (z + \<omega>1) = g z" "g (z + \<omega>2) = g z" for z
      using *[of \<omega>1] *[of \<omega>2] by simp_all
  qed

  text \<open>
    Since the constituent functions only have poles at lattice points, our \<^term>\<open>g\<close> cannot have
    poles except at the lattice points either.
  \<close>
  have no_poles_off_lattice: "\<not>is_pole g z" if z: "z \<notin> \<Lambda>" for z
  proof -
    from z have "g analytic_on {z}" using v
      by (auto simp: g_def weierstrass_sigma_eq_0_iff intro!: analytic_intros)
    thus ?thesis
      using analytic_at_imp_no_pole by blast
  qed

  text \<open>
    Now comes the most tedious part: we show that the poles at the lattice points cancel.
    Due to ellipticity, it is of course enough to show this for the origin.
  \<close>
  have "\<not>is_pole g 0"
  proof
    assume "is_pole g 0"

    define h where "h = (\<lambda>u. \<sigma> (u + v) * \<sigma> (u - v) / \<sigma> v ^ 2)"
    define F1 where "F1 = fps_expansion h 0"
    have F1: "h has_fps_expansion F1"
      unfolding F1_def using v
      by (intro fps_expansion_intros analytic_at_imp_has_fps_expansion_0)
         (auto simp: h_def weierstrass_sigma_eq_0_iff intro!: analytic_intros)
    have "h 0 = -1" using v 
      by (simp add: h_def weierstrass_sigma_uminus power2_eq_square weierstrass_sigma_eq_0_iff)
    hence "fps_nth F1 0 = -1"
      using has_fps_expansion_imp_0_eq_fps_nth_0[OF F1] by simp
    hence "subdegree F1 = 0"
      by (intro subdegreeI) auto
    have [simp]: "F1 \<noteq> 0"
      using \<open>fps_nth F1 0 = -1\<close> by auto
    
    define F2 where "F2 = fps_weierstrass_sigma"
    have F2: "\<sigma> has_fps_expansion F2"
      unfolding F2_def by (intro fps_expansion_intros)

    define F3 where "F3 = fls_weierstrass"
    define F where "F = fps_to_fls F1 / (fps_to_fls F2)\<^sup>2 + F3"

    have F: "g has_laurent_expansion F"
    proof -
      have "(\<lambda>u. h u / \<sigma> u ^ 2 + \<wp> u) has_laurent_expansion F"
        unfolding F_def F3_def using v
        by (intro laurent_expansion_intros F1 F2 has_laurent_expansion_fps)
      also have "(\<lambda>u. h u / \<sigma> u ^ 2 + \<wp> u) = g"
        by (simp add: g_def h_def divide_simps fun_eq_iff)
      finally show ?thesis .
    qed
    have [simp]: "F \<noteq> 0"
      using F \<open>is_pole g 0\<close> is_pole_0_imp_neg_fls_subdegree by fastforce

    have "fls_subdegree F \<le> -2"
    proof -
      have "(\<Sum>z | z \<in> period_parallelogram 0 \<and> is_pole g z. nat (-zorder g z)) = elliptic_order g"
        by (rule g.poles_eq_elliptic_order)
      also have "{z. z \<in> period_parallelogram 0 \<and> is_pole g z} = {0}"
      proof (intro equalityI subsetI)
        fix z assume "z \<in> {z. z \<in> period_parallelogram 0 \<and> is_pole g z}"
        hence z: "z \<in> period_parallelogram 0" "z \<in> \<Lambda>"
          using no_poles_off_lattice by auto
        from z(2) obtain m n where z_eq: "z = of_\<omega>12_coords (of_int m, of_int n)"
          by (auto simp: lattice_def elim!: Ints_cases)
        from z(1) show "z \<in> {0}"
          by (auto simp: period_parallelogram_altdef z_eq)
      qed (use \<open>is_pole g 0\<close> in auto)
      finally have "nat (-zorder g 0) = elliptic_order g"
        by simp
      moreover have "g meromorphic_on {0}"
        by (intro meromorphic_on_subset[OF g.meromorphic]) auto
      hence "zorder g 0 < 0" using \<open>is_pole g 0\<close>
        by (intro isolated_pole_imp_neg_zorder meromorphic_on_isolated_singularity)
      ultimately have "zorder g 0 = -int (elliptic_order g)"
        by simp
      moreover have "elliptic_order g \<ge> 2"
        using g.elliptic_order_neq_1 g.elliptic_order_eq_0_iff_no_poles \<open>is_pole g 0\<close> by auto
      ultimately have "zorder g 0 \<le> -2"
        by simp
      also have "zorder g 0 = fls_subdegree F"
        using has_laurent_expansion_zorder_0[OF F] by auto
      finally show ?thesis .
    qed
    moreover have "fls_subdegree F \<ge> -2"
    proof -
      have "min (fls_subdegree (fps_to_fls F1 / (fps_to_fls F2)\<^sup>2)) (fls_subdegree F3) \<le> fls_subdegree F"
        unfolding F_def by (rule fls_plus_subdegree) (use \<open>F \<noteq> 0\<close> in \<open>auto simp: F_def\<close>)
      also have "fls_subdegree F3 = -2"
        unfolding F3_def by (simp add: fls_subdegree_weierstrass)
      also have "fls_subdegree (fps_to_fls F1 / (fps_to_fls F2)\<^sup>2) = -2"
        by (subst fls_divide_subdegree) 
           (auto simp: fls_subdegree_fls_to_fps \<open>subdegree F1 = _\<close> F2_def
                 simp flip: fps_to_fls_power)
      finally show ?thesis
        by simp
    qed
    ultimately have "fls_subdegree F = -2"
      by linarith

    have "fls_nth F (-2) = 0"
    proof -
      have "fls_nth (fps_to_fls F1 / (fps_to_fls F2)\<^sup>2) (-2) = 
              fls_nth (fps_to_fls F1 / (fps_to_fls F2)\<^sup>2) 
                (fls_subdegree (fps_to_fls F1) - fls_subdegree (fps_to_fls F2 ^ 2))"
        by (simp add: fls_subdegree_fls_to_fps \<open>subdegree F1 = _\<close> F2_def
                 flip: fps_to_fls_power)
      also have "\<dots> = fps_nth F1 0 / fps_nth (F2 ^ 2) (2 * subdegree F2)"
        by (subst fls_divide_nth_base)
           (auto simp: fls_subdegree_fls_to_fps \<open>subdegree F1 = _\<close> F2_def
                 simp flip: fps_to_fls_power)
      also have "\<dots> = -1"
        by (subst fps_pow_base) (auto simp: F2_def \<open>fps_nth F1 0 = _\<close>)
      finally show ?thesis
        by (simp add: F_def F3_def fls_weierstrass_def)
    qed
    also have "-2 = fls_subdegree F"
      by (rule sym) fact
    finally have "F = 0"
      by simp
    thus False
      using \<open>F \<noteq> 0\<close> by contradiction
  qed

  text \<open>
    It follows that the function has no poles and must therefore be constant except possibly for
    removable singularities at the lattice points.
  \<close>
  have no_poles: "\<not>is_pole g z" for z
  proof (cases "z \<in> \<Lambda>")
    case True
    hence "rel z 0"
      by (auto simp: rel_def)
    hence "is_pole g z \<longleftrightarrow> is_pole g 0"
      by (rule g.poles.lattice_cong)
    with \<open>\<not>is_pole g 0\<close> show ?thesis
      by auto
  qed (use no_poles_off_lattice in auto)
  hence "elliptic_order g = 0"
    by (simp add: elliptic_order_def)
  then obtain c where c: "\<forall>\<^sub>\<approx>z. g z = c"
    using g.elliptic_order_eq_0_iff_const_cosparse by blast

  text \<open>
    By looking at $g(v)$, we determine the constant to be $\wp(v)$, which concludes the proof.
  \<close>
  hence g_eq: "g z = c" if z: "z \<notin> \<Lambda>" for z
  proof (rule analytic_on_continuation)
    show "g analytic_on {z}"
      using z v by (auto simp: g_def weierstrass_sigma_eq_0_iff intro!: analytic_intros)
  qed auto
  have c_eq: "c = \<wp> v"
    using g_eq[of v] v by (simp add: g_def)

  have "g u = \<wp> v"
    using u by (simp add: g_eq c_eq)
  thus ?thesis
    using u v by (simp add: g_def weierstrass_sigma_eq_0_iff field_simps)
qed

text \<open>
  From the addition theorem for \<open>\<sigma>\<close>, it is also easy to derive two related three-term identities:
\<close>
corollary weierstrass_sigma_three_term:
  assumes uvw: "u \<notin> \<Lambda>" "v \<notin> \<Lambda>" "w \<notin> \<Lambda>"
  defines "\<sigma> \<equiv> weierstrass_sigma"
  shows   "\<sigma> (u+v) * \<sigma> (u-v) * \<sigma> w ^ 2 +
           \<sigma> (v+w) * \<sigma> (v-w) * \<sigma> u ^ 2 + 
           \<sigma> (w+u) * \<sigma> (w-u) * \<sigma> v ^ 2 = 0"
  unfolding \<sigma>_def
  by (subst (1 2 3) weierstrass_sigma_add_diff) (use uvw in \<open>auto simp: algebra_simps\<close>)

corollary weierstrass_sigma_sym_three_term:
  assumes uxyz: "u \<notin> \<Lambda>" "x \<notin> \<Lambda>" "y \<notin> \<Lambda>" "z \<notin> \<Lambda>"
  defines "\<sigma> \<equiv> weierstrass_sigma"
  shows   "\<sigma> (u+x) * \<sigma> (u-x) * \<sigma> (y+z) * \<sigma> (y-z) +
           \<sigma> (u+y) * \<sigma> (u-y) * \<sigma> (z+x) * \<sigma> (z-x) +
           \<sigma> (u+z) * \<sigma> (u-z) * \<sigma> (x+y) * \<sigma> (x-y) = 0"
proof -
  have *: "a * b * c * d = (a * b) * (c * d)" for a b c d :: complex
    by (simp add: mult_ac)
  show ?thesis unfolding \<sigma>_def *
    by (subst (1 2 3 4 5 6) weierstrass_sigma_add_diff) (use uxyz in \<open>auto simp: algebra_simps\<close>)
qed

text \<open>
  Taking the derivative of the addition formula for \<open>\<sigma>\<close> and setting $v = u$, we obtain the
  duplication formula:
\<close>
theorem weierstrass_sigma_duplication:
  assumes u: "u \<notin> \<Lambda>" "2 * u \<notin> \<Lambda>"
  shows "weierstrass_sigma (2 * u) = -\<wp>' u * weierstrass_sigma u ^ 4"
proof -
  write weierstrass_sigma ("\<sigma>")
  write weierstrass_zeta ("\<zeta>")
  write weierstrass_eta ("\<eta>")

  define S where "S = \<sigma> \<circ> (\<lambda>v. u - v)"
  have [derivative_intros]: "(S has_field_derivative (1 * (-1))) (at u)" unfolding S_def 
    by (intro DERIV_chain) (auto intro!: derivative_eq_intros has_field_derivative_weierstrass_sigma_0)
  have [simp]: "S u = 0"
    by (simp add: S_def)
  define g where "g = (\<lambda>v. \<sigma> (u + v) * S v - (\<wp> v - \<wp> u) * \<sigma> u ^ 2 * \<sigma> v ^ 2)"
  note [derivative_intros] = has_field_derivative_weierstrass_sigma_0[folded S_def]

  have "(g has_field_derivative (-\<sigma> (2 * u) - \<wp>' u * (\<sigma> u)\<^sup>2 * (\<sigma> u)\<^sup>2)) (at u)"
    unfolding g_def using u by (auto intro!: derivative_eq_intros)
  also have "?this \<longleftrightarrow> ((\<lambda>_. 0) has_field_derivative (-\<sigma> (2 * u) - \<wp>' u * (\<sigma> u)\<^sup>2 * (\<sigma> u)\<^sup>2)) (at u)"
  proof (rule DERIV_cong_ev)
    have "eventually (\<lambda>v. v \<in> -\<Lambda>) (nhds u)"
      by (rule eventually_nhds_in_open) (use closed_lattice u in auto)
    thus "eventually (\<lambda>v. g v = 0) (nhds u)"
    proof eventually_elim
      case (elim v)
      thus ?case
        unfolding g_def S_def using weierstrass_sigma_add_diff[of u v] u by simp
    qed
  qed auto
  finally have "((\<lambda>_. 0) has_field_derivative (-\<sigma> (2 * u) - \<wp>' u * \<sigma> u ^ 4)) (at u)"
    by (simp add: power_numeral_reduce mult_ac)
  moreover have "((\<lambda>_. 0) has_field_derivative 0) (at u)" by simp
  ultimately have "-\<sigma> (2 * u) - \<wp>' u * \<sigma> u ^ 4 = 0"
    using DERIV_unique by blast
  thus ?thesis
    by Groebner_Basis.algebra
qed


text \<open>
  By taking the logarithmic derivative of the addition formula for $\sigma$, 
  we obtain the addition formula for $\zeta$. This is only well-defined if $u\neq \pm v$.
\<close>
theorem weierstrass_zeta_add:
  assumes u: "u \<notin> \<Lambda>" and v: "v \<notin> \<Lambda>" and "\<not>rel u v" "\<not>rel u (-v)"
  shows "weierstrass_zeta (u + v) = 
           weierstrass_zeta u + weierstrass_zeta v + 1 / 2 * (\<wp>' v - \<wp>' u) / (\<wp> v - \<wp> u)"
proof -
  have uv: "u + v \<notin> \<Lambda>" "u - v \<notin> \<Lambda>"
    using assms weierstrass_fun.lattice_cong'[of u v] by (auto simp: rel_def)
  have "\<wp> u \<noteq> \<wp> v"
    using assms weierstrass_fun_eq_iff by simp
  write weierstrass_sigma ("\<sigma>")
  write weierstrass_zeta ("\<zeta>")
  write weierstrass_eta ("\<eta>")

  define g where "g = (\<lambda>u v. \<sigma> (u + v) * \<sigma> (u - v) / ((\<wp> v - \<wp> u) * \<sigma> u ^ 2 * \<sigma> v ^ 2))"
  have g1: "g u v = 1"
    using weierstrass_sigma_add_diff[of u v] u v uv by (auto simp: g_def weierstrass_sigma_eq_0_iff)

  have g2: "eventually (\<lambda>u. g u v = 1) (at u)"
  proof -
    show ?thesis
      using eventually_not_rel_at[of 0 u] eventually_not_rel_at[of v u]
            eventually_not_rel_at[of "-v" u]
    proof eventually_elim
      case (elim u)
      thus ?case
        using weierstrass_sigma_add_diff[of u v] v
        by (auto simp: g_def weierstrass_sigma_eq_0_iff rel_def)
    qed
  qed

  have g3: "eventually (\<lambda>v. g u v = 1) (at v)"
  proof -
    show ?thesis
      using eventually_not_rel_at[of 0 v] eventually_not_rel_at[of u v]
            eventually_not_rel_at[of "-u" v]
    proof eventually_elim
      case (elim v)
      thus ?case
        using weierstrass_sigma_add_diff[of u v] u
        by (auto simp: g_def weierstrass_sigma_eq_0_iff rel_def add_ac diff_in_lattice_commute)
    qed
  qed

  have 1: "\<zeta> (u - v) = -\<zeta> (u + v) + 2 * \<zeta> u - \<wp>' u / (\<wp> v - \<wp> u)"
  proof -
    define h where "h = (\<lambda>u. \<wp> v - \<wp> u)"
    define D where "D = (\<zeta> (u + v) + \<zeta> (u - v) + \<wp>' u / (\<wp> v - \<wp> u) - 2 * \<zeta> u)"
    have [derivative_intros]: "(h has_log_derivative (-\<wp>' u / (\<wp> v - \<wp> u))) (at u)"
      using u \<open>\<wp> u \<noteq> \<wp> v\<close> unfolding h_def
      by (intro has_field_derivative_imp_has_log_derivative) (auto intro!: derivative_eq_intros)
    have "((\<lambda>u. \<sigma> (u + v) * \<sigma> (u - v) / (h u * \<sigma> u ^ 2 * \<sigma> v ^ 2)) has_log_derivative D) (at u)"
      using u v uv by (auto intro!: derivative_eq_intros simp: weierstrass_sigma_eq_0_iff D_def)
    also have "?this \<longleftrightarrow> ((\<lambda>_. 1) has_log_derivative D) (at u)"
    proof (rule has_log_derivative_cong_ev)
      show "\<forall>\<^sub>F u in at u. \<sigma> (u + v) * \<sigma> (u - v) / (h u * (\<sigma> u)\<^sup>2 * (\<sigma> v)\<^sup>2) = 1"
        using g2 by eventually_elim (auto simp: g_def h_def)
    qed (use g1 in \<open>auto simp: h_def g_def\<close>)
    finally have "((\<lambda>_. 1) has_log_derivative D) (at u)" .
    moreover have "((\<lambda>_. 1) has_log_derivative 0) (at u)"
      by auto
    ultimately have "D = 0"
      by (rule has_log_derivative_unique) auto
    thus ?thesis
      by (simp add: D_def algebra_simps)
  qed

  have 2: "\<zeta> (u - v) = \<zeta> (u + v) - 2 * \<zeta> v - \<wp>' v / (\<wp> v - \<wp> u)"
  proof -
    define h where "h = (\<lambda>v. \<wp> v - \<wp> u)"
    define D where "D = (\<zeta> (u + v) - \<zeta> (u - v) - \<wp>' v / (\<wp> v - \<wp> u) - 2 * \<zeta> v)"
    have [derivative_intros]: "(h has_log_derivative (\<wp>' v / (\<wp> v - \<wp> u))) (at v)"
      using u v \<open>\<wp> u \<noteq> \<wp> v\<close> unfolding h_def
      by (intro has_field_derivative_imp_has_log_derivative) (auto intro!: derivative_eq_intros)
    have "((\<lambda>v. \<sigma> (u + v) * \<sigma> (u - v) / (h v * \<sigma> u ^ 2 * \<sigma> v ^ 2)) has_log_derivative D) (at v)"
      using u v uv by (auto intro!: derivative_eq_intros simp: weierstrass_sigma_eq_0_iff D_def)
    also have "?this \<longleftrightarrow> ((\<lambda>_. 1) has_log_derivative D) (at v)"
    proof (rule has_log_derivative_cong_ev)
      show "\<forall>\<^sub>F v in at v. \<sigma> (u + v) * \<sigma> (u - v) / (h v * (\<sigma> u)\<^sup>2 * (\<sigma> v)\<^sup>2) = 1"
        using g3 by eventually_elim (auto simp: g_def h_def)
    qed (use g1 in \<open>auto simp: h_def g_def\<close>)
    finally have "((\<lambda>_. 1) has_log_derivative D) (at v)" .
    moreover have "((\<lambda>_. 1) has_log_derivative 0) (at v)"
      by auto
    ultimately have "D = 0"
      by (rule has_log_derivative_unique) auto
    thus ?thesis
      by (simp add: D_def algebra_simps)
  qed

  have "-\<zeta> (u + v) + 2 * \<zeta> u - \<wp>' u / (\<wp> v - \<wp> u) = \<zeta> (u + v) - 2 * \<zeta> v - \<wp>' v / (\<wp> v - \<wp> u)"
    using 1 2 by simp
  hence "2 * \<zeta> (u + v) = 2 * (\<zeta> u + \<zeta> v) + \<wp>' v / (\<wp> v - \<wp> u) - \<wp>' u / (\<wp> v - \<wp> u)"
    by Groebner_Basis.algebra
  also have "\<dots> = 2 * (\<zeta> u + \<zeta> v) + (\<wp>' v - \<wp>' u) / (\<wp> v - \<wp> u)"
    by (simp add: divide_simps)
  also have "\<dots> = 2 * (\<zeta> u + \<zeta> v + 1/2 * (\<wp>' v - \<wp>' u) / (\<wp> v - \<wp> u))"
    by (simp add: algebra_simps)
  finally show "\<zeta> (u + v) = \<zeta> u + \<zeta> v + 1 / 2 * (\<wp>' v - \<wp>' u) / (\<wp> v - \<wp> u)"
    by Groebner_Basis.algebra
qed

text \<open>
  Taking the logarithmic derivative of the duplication identity for $\sigma$ gives us the
  one for $\zeta$:
\<close>
theorem weierstrass_zeta_duplication:
  assumes u: "u \<notin> \<Lambda>" "2 * u \<notin> \<Lambda>"
  shows "weierstrass_zeta (2 * u) = 2 * weierstrass_zeta u + (3 * \<wp> u ^ 2 - 15 * G 4) / \<wp>' u"
proof -
  write weierstrass_sigma ("\<sigma>")
  write weierstrass_zeta ("\<zeta>")

  define g where "g = (\<lambda>u. -\<sigma> (2 * u) / (\<wp>' u * \<sigma> u ^ 4))"
  define D where "D = 2 * \<zeta> (2 * u) - (6 * (\<wp> u)\<^sup>2 - 30 * G 4) / \<wp>' u - 4 * \<zeta> u"
  have [derivative_intros]: "(\<wp>' has_log_derivative ((6 * \<wp> u ^ 2 - 30 * G 4) / \<wp>' u)) (at u)"
    using u by (auto intro!: has_field_derivative_imp_has_log_derivative derivative_eq_intros 
                     simp: weierstrass_fun_deriv_eq_0_iff)
  have "(g has_log_derivative D) (at u)"
    using u by (auto simp: D_def g_def weierstrass_sigma_eq_0_iff intro!: derivative_eq_intros)
  also have "?this \<longleftrightarrow> ((\<lambda>_. 1) has_log_derivative D) (at u)"
  proof (rule has_log_derivative_cong_ev')
    have "eventually (\<lambda>u. u \<in> -\<Lambda>) (nhds u)"
      by (intro eventually_nhds_in_open) (use closed_lattice u in auto)
    moreover have "eventually (\<lambda>u. u \<in> (\<lambda>w. 2 * w) -` (-\<Lambda>)) (nhds u)"
      by (intro eventually_nhds_in_open open_vimage continuous_intros) (use u closed_lattice in auto)
    ultimately show "eventually (\<lambda>u. g u = 1) (nhds u)"
    proof eventually_elim
      case (elim u)
      thus ?case
        using weierstrass_sigma_duplication[of u] by (auto simp: g_def weierstrass_sigma_eq_0_iff)
    qed
  qed
  finally have "((\<lambda>_. 1) has_log_derivative D) (at u)" .
  moreover have "((\<lambda>_. 1) has_log_derivative 0) (at u)" by auto
  ultimately have "D = 0"
    by (rule has_log_derivative_unique) auto
  hence "2 * \<zeta> (2 * u) - 2 * ((3 * \<wp> u ^ 2 - 15 * G 4) / \<wp>' u) = 4 * \<zeta> u"
    by (simp add: D_def)
  thus ?thesis
    by Groebner_Basis.algebra
qed

end

end