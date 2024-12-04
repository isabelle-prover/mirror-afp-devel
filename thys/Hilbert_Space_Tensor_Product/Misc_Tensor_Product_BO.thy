section \<open>\<open>Misc_Tensor_Product_BO\<close> -- Miscelleanous results missing from \<^session>\<open>Complex_Bounded_Operators\<close>\<close>

theory Misc_Tensor_Product_BO
  imports
    Complex_Bounded_Operators.Complex_L2
    Misc_Tensor_Product  
    "HOL-Library.Function_Algebras" 
begin

no_notation Set_Algebras.elt_set_eq (infix "=o" 50)
(* no_notation Infinite_Set_Sum.abs_summable_on (infixr "abs'_summable'_on" 46) *)

unbundle cblinfun_notation

instance cblinfun :: (chilbert_space,chilbert_space) ordered_comm_monoid_add
  by intro_classes

lemma rank1_scaleR[simp]: \<open>rank1 (c *\<^sub>R a)\<close> if \<open>rank1 a\<close> and \<open>c \<noteq> 0\<close>
  by (simp add: rank1_scaleC scaleR_scaleC that(1) that(2))

lemma rank1_butterfly[simp]: \<open>rank1 (butterfly x y)\<close>
  apply (cases \<open>y = 0\<close>)
  by (auto intro: exI[of _ 0] simp: rank1_def butterfly_is_rank1)

definition \<open>cfinite_dim S \<longleftrightarrow> (\<exists>B. finite B \<and> S \<subseteq> cspan B)\<close>

lemma cfinite_dim_subspace_has_basis:
  assumes \<open>cfinite_dim S\<close> and \<open>csubspace S\<close>
  shows \<open>\<exists>B. finite B \<and> cindependent B \<and> cspan B = S\<close>
proof -
  obtain B where \<open>cindependent B\<close> and \<open>cspan B = S\<close>
    by (rule complex_vector.maximal_independent_subset[where V=S])
       (use \<open>csubspace S\<close> complex_vector.span_subspace in blast)
  from \<open>cfinite_dim S\<close>
  obtain C where \<open>finite C\<close> and \<open>S \<subseteq> cspan C\<close>
    using cfinite_dim_def by auto
  from \<open>cspan B = S\<close> and \<open>S \<subseteq> cspan C\<close>
  have \<open>B \<subseteq> cspan C\<close>
    using complex_vector.span_superset by force
  from \<open>finite C\<close> \<open>cindependent B\<close> this
  have \<open>finite B\<close>
    by (rule complex_vector.independent_span_bound[THEN conjunct1])
  from this and \<open>cindependent B\<close> and \<open>cspan B = S\<close>
  show ?thesis
    by auto
qed

lemma cfinite_dim_subspace_has_onb:
  assumes \<open>cfinite_dim S\<close> and \<open>csubspace S\<close>
  shows \<open>\<exists>B. finite B \<and> is_ortho_set B \<and> cspan B = S \<and> (\<forall>x\<in>B. norm x = 1)\<close>
proof -
  from assms
  obtain C where \<open>finite C\<close> and \<open>cindependent C\<close> and \<open>cspan C = S\<close>
    using cfinite_dim_subspace_has_basis by blast
  obtain B where \<open>finite B\<close> and \<open>is_ortho_set B\<close> and \<open>cspan B = cspan C\<close>
    and norm: \<open>x \<in> B \<Longrightarrow> norm x = 1\<close> for x
    using orthonormal_basis_of_cspan[OF \<open>finite C\<close>]
    by blast
  with \<open>cspan C = S\<close> have \<open>cspan B = S\<close>
    by simp
  with \<open>finite B\<close> and \<open>is_ortho_set B\<close> and norm
  show ?thesis
    by blast
qed

lemma cspan_finite_dim[intro]: \<open>cfinite_dim (cspan B)\<close> if \<open>finite B\<close>
  using cfinite_dim_def that by auto

lift_definition finite_dim_ccsubspace :: \<open>'a::complex_normed_vector ccsubspace \<Rightarrow> bool\<close> is cfinite_dim.

lemma ccspan_finite_dim[intro]: \<open>finite_dim_ccsubspace (ccspan B)\<close> if \<open>finite B\<close>
  using ccspan_finite finite_dim_ccsubspace.rep_eq that by fastforce


lemma finite_dim_ccsubspace_zero[iff]: \<open>finite_dim_ccsubspace 0\<close>
proof -
  have *: \<open>cfinite_dim (cspan {0})\<close>
    by blast
  show ?thesis
    apply transfer
    using * by simp
qed



lemma finite_dim_ccsubspace_bot[iff]: \<open>finite_dim_ccsubspace \<bottom>\<close>
  using finite_dim_ccsubspace_zero by auto



lemma compact_scaleC:
  fixes s :: "'a::complex_normed_vector set"
  assumes "compact s"
  shows "compact (scaleC c ` s)"
  by (auto intro!: compact_continuous_image assms continuous_at_imp_continuous_on)

lemma Proj_nearest:
  assumes \<open>x \<in> space_as_set S\<close>
  shows \<open>dist (Proj S m) m \<le> dist x m\<close>
proof -
  have \<open>is_projection_on (Proj S) (space_as_set S)\<close>
    by (simp add: Proj.rep_eq)
  then have \<open>is_arg_min (\<lambda>x. dist x m) (\<lambda>x. x \<in> space_as_set S) (Proj S m)\<close>
    by (simp add: is_projection_on_def)
  with assms show ?thesis
    by (auto simp: is_arg_min_def)
qed

lemma norm_cblinfun_bound_unit:
  assumes \<open>b \<ge> 0\<close>
  assumes \<open>\<And>\<psi>. norm \<psi> = 1 \<Longrightarrow> norm (a *\<^sub>V \<psi>) \<le> b\<close>
  shows \<open>norm a \<le> b\<close>
proof (rule norm_cblinfun_bound)
  from assms show \<open>b \<ge> 0\<close> by simp
  fix x
  show \<open>norm (a *\<^sub>V x) \<le> b * norm x\<close>
  proof (cases \<open>x = 0\<close>)
    case True
    then show ?thesis by simp
  next
    case False
    have \<open>norm (a *\<^sub>V x) = norm (a *\<^sub>V (norm x *\<^sub>C sgn x))\<close>
      by simp
    also have \<open>\<dots> = norm (a *\<^sub>V sgn x) * norm x\<close>
      by (simp add: cblinfun.scaleC_right del: norm_scaleC_sgn)
    also have \<open>\<dots> \<le> (b * norm (sgn x)) * norm x\<close>
      by (simp add: assms(2) norm_sgn)
    also have \<open>\<dots> = b * norm x\<close>
      by (simp add: norm_sgn)
    finally show ?thesis 
      by -
  qed
qed



lemma cblinfun_norm_is_Sup_cinner:
  \<comment> \<open>\<^cite>\<open>conway2013course\<close>, Proposition II.2.13\<close>
fixes A :: \<open>'a::{not_singleton,chilbert_space} \<Rightarrow>\<^sub>C\<^sub>L 'a\<close>
  assumes Aselfadj: \<open>selfadjoint A\<close>
  shows \<open>is_Sup ((\<lambda>\<psi>. cmod (\<psi> \<bullet>\<^sub>C (A *\<^sub>V \<psi>))) ` {\<psi>. norm \<psi> = 1}) (norm A)\<close>
proof (rule is_SupI)
  fix b assume \<open>b \<in> (\<lambda>\<psi>. cmod (\<psi> \<bullet>\<^sub>C (A *\<^sub>V \<psi>))) ` {\<psi>. norm \<psi> = 1}\<close>
  then obtain \<psi> where \<open>norm \<psi> = 1\<close> and b_\<psi>: \<open>b = cmod (\<psi> \<bullet>\<^sub>C (A *\<^sub>V \<psi>))\<close>
    by blast
  have \<open>b \<le> norm (A \<psi>)\<close>
    using b_\<psi> \<open>norm \<psi> = 1\<close>
    by (metis complex_inner_class.Cauchy_Schwarz_ineq2 mult_cancel_right2)
  also have \<open>\<dots> \<le> norm A\<close>
    using \<open>norm \<psi> = 1\<close> 
    by (metis mult_cancel_left2 norm_cblinfun)
  finally show \<open>b \<le> norm A\<close>
    by -
next
  fix c assume asm: \<open>(\<And>b. b \<in> (\<lambda>\<psi>. cmod (\<psi> \<bullet>\<^sub>C A \<psi>)) ` {\<psi>. norm \<psi> = 1} \<Longrightarrow> b \<le> c)\<close>
  have c_upper: \<open>cmod (\<psi> \<bullet>\<^sub>C (A *\<^sub>V \<psi>)) \<le> c\<close> if \<open>norm \<psi> = 1\<close> for \<psi>
    using that using asm[of \<open>cmod (\<psi> \<bullet>\<^sub>C (A *\<^sub>V \<psi>))\<close>] by auto
  have \<open>c \<ge> 0\<close>
    by (smt (z3) ex_norm1_not_singleton c_upper norm_ge_zero)
  have *: \<open>Re (g \<bullet>\<^sub>C A h) \<le> c\<close> if \<open>norm g = 1\<close> and \<open>norm h = 1\<close> for g h
  proof -
    have c_upper': \<open>cmod (\<psi> \<bullet>\<^sub>C (A *\<^sub>V \<psi>)) \<le> c * (norm \<psi>)\<^sup>2\<close> for \<psi>
      apply (cases \<open>\<psi> = 0\<close>, simp)
      apply (subst (2) norm_scaleC_sgn[symmetric, of \<psi>])
      apply (subst norm_scaleC_sgn[symmetric])
      apply (simp only: cinner_scaleC_left cinner_scaleC_right cblinfun.scaleC_right)
      using c_upper[of \<open>sgn \<psi>\<close>]
      by (simp add: norm_mult norm_sgn power2_eq_square)
    from Aselfadj have Aselfadj': "x \<bullet>\<^sub>C (A *\<^sub>V y) = (A *\<^sub>V x) \<bullet>\<^sub>C y" for x y
      using cinner_adj_right[of x A y] by (auto simp: selfadjoint_def)
    from Aselfadj have Aselfadj'': "(A *\<^sub>V x) \<bullet>\<^sub>C y = cnj ((A *\<^sub>V y) \<bullet>\<^sub>C x)" for x y
      by (subst cinner_commute, subst Aselfadj') auto

    have 1: \<open>(h + g) \<bullet>\<^sub>C A (h + g) = h \<bullet>\<^sub>C A h + 2 * Re (g \<bullet>\<^sub>C A h) + g \<bullet>\<^sub>C A g\<close>
      by (simp add: cblinfun.cbilinear_simps algebra_simps
            Aselfadj' Aselfadj''[of h g] complex_add_cnj del: cinner_commute')
    from Aselfadj have 2: \<open>(h - g) \<bullet>\<^sub>C A (h - g) = h \<bullet>\<^sub>C A h - 2 * Re (g \<bullet>\<^sub>C A h) + g \<bullet>\<^sub>C A g\<close>
      by (simp add: cblinfun.cbilinear_simps algebra_simps Aselfadj' 
            Aselfadj''[of h g] complex_add_cnj del: cinner_commute')
    have \<open>4 * Re (g \<bullet>\<^sub>C A h) = Re ((h + g) \<bullet>\<^sub>C A (h + g)) - Re ((h - g) \<bullet>\<^sub>C A (h - g))\<close>
      by (smt (verit, ccfv_SIG) "1" "2" Re_complex_of_real minus_complex.simps(1) plus_complex.sel(1))
    also have \<open>\<dots> \<le> c * (norm (h + g))\<^sup>2 - Re ((h - g) \<bullet>\<^sub>C A (h - g))\<close>
      using c_upper'[of \<open>h + g\<close>]
      by (smt (verit, best) complex_Re_le_cmod)
    also have \<open>\<dots> \<le> c * (norm (h + g))\<^sup>2 + c * (norm (h - g))\<^sup>2\<close>
      unfolding diff_conv_add_uminus
      by (rule add_left_mono)
         (use c_upper'[of \<open>h - g\<close>] in \<open>smt (verit) abs_Re_le_cmod add_uminus_conv_diff\<close>)
    also have \<open>\<dots> = 2 * c * ((norm h)\<^sup>2 + (norm g)\<^sup>2)\<close>
      by (auto intro!: simp: polar_identity polar_identity_minus ring_distribs)
    also have \<open>\<dots> \<le> 4 * c\<close>
      by (simp add: \<open>norm h = 1\<close> \<open>norm g = 1\<close>)
    finally show \<open>Re (g \<bullet>\<^sub>C (A *\<^sub>V h)) \<le> c\<close>
      by simp
  qed      
  have *: \<open>cmod (g \<bullet>\<^sub>C A h) \<le> c\<close> if \<open>norm g = 1\<close> and \<open>norm h = 1\<close> for g h
  proof -
    define \<gamma> where \<open>\<gamma> = (if g \<bullet>\<^sub>C A h = 0 then 1 else sgn (g \<bullet>\<^sub>C A h))\<close>
    have \<gamma>: \<open>\<gamma> * cmod (g \<bullet>\<^sub>C A h) = g \<bullet>\<^sub>C A h\<close>
      by (simp add: \<gamma>_def sgn_eq)
    have \<open>norm \<gamma> = 1\<close>
      by (simp add: \<gamma>_def norm_sgn)
    have \<open>cmod (g \<bullet>\<^sub>C A h) = Re (complex_of_real (norm (g \<bullet>\<^sub>C A h)))\<close>
      by simp
    also have \<open>\<dots> = Re (g \<bullet>\<^sub>C (A (h /\<^sub>C \<gamma>)))\<close>
      using \<gamma> \<open>cmod \<gamma> = 1\<close>
      by (smt (verit) Groups.mult_ac(2) Groups.mult_ac(3) cblinfun.scaleC_right cinner_scaleC_right left_inverse more_arith_simps(6) norm_eq_zero)
    also have \<open>\<dots> \<le> c\<close>
      using \<open>norm \<gamma> = 1\<close>
      by (auto intro!: * simp: that norm_inverse)
    finally show \<open>cmod (g \<bullet>\<^sub>C (A *\<^sub>V h)) \<le> c\<close>
      by -
  qed
  have \<open>norm (A h) \<le> c\<close> if \<open>norm h = 1\<close> for h
    by (cases \<open>A h = 0\<close>)
       (use *[OF _ that, of \<open>sgn (A h)\<close>] in \<open>simp_all add: norm_sgn \<open>0 \<le> c\<close>\<close>)
  then show \<open>norm A \<le> c\<close>
    using \<open>c \<ge> 0\<close> by (auto intro!: norm_cblinfun_bound_unit)
qed

lemma cblinfun_norm_approx_witness_cinner:
  fixes A :: \<open>'a::{not_singleton,chilbert_space} \<Rightarrow>\<^sub>C\<^sub>L 'a\<close>
  assumes \<open>selfadjoint A\<close> and \<open>\<epsilon> > 0\<close>
  shows \<open>\<exists>\<psi>. cmod (\<psi> \<bullet>\<^sub>C (A *\<^sub>V \<psi>)) \<ge> norm A - \<epsilon> \<and> norm \<psi> = 1\<close>
  using is_Sup_approx_below[OF cblinfun_norm_is_Sup_cinner[OF assms(1)] assms(2)]
  by blast

lemma cblinfun_norm_approx_witness_cinner':
  fixes A :: \<open>'a::chilbert_space \<Rightarrow>\<^sub>C\<^sub>L 'a\<close>
  assumes \<open>selfadjoint A\<close> and \<open>\<epsilon> > 0\<close>
  shows \<open>\<exists>\<psi>. cmod (\<psi> \<bullet>\<^sub>C A \<psi>) / (norm \<psi>)^2 \<ge> norm A - \<epsilon>\<close>
proof (cases \<open>class.not_singleton TYPE('a)\<close>)
  case True
  obtain \<psi> where \<open>cmod (\<psi> \<bullet>\<^sub>C A \<psi>) \<ge> norm A - \<epsilon>\<close> and \<open>norm \<psi> = 1\<close>
    apply atomize_elim
    using chilbert_space_axioms True assms
    by (rule cblinfun_norm_approx_witness_cinner[internalize_sort' 'a])
  then have \<open>cmod (\<psi> \<bullet>\<^sub>C A \<psi>) / (norm \<psi>)^2 \<ge> norm A - \<epsilon>\<close>
    by simp
  then show ?thesis 
    by auto
next
  case False
  show ?thesis
    apply (subst not_not_singleton_cblinfun_zero[OF False])
     apply simp
    apply (subst not_not_singleton_cblinfun_zero[OF False])
    using \<open>\<epsilon> > 0\<close> by simp
qed

lemma has_sum_mono_neutral_cblinfun:
  fixes f :: "'a \<Rightarrow> ('b::chilbert_space \<Rightarrow>\<^sub>C\<^sub>L 'b)"
  assumes \<open>(f has_sum a) A\<close> and "(g has_sum b) B"
  assumes \<open>\<And>x. x \<in> A\<inter>B \<Longrightarrow> f x \<le> g x\<close>
  assumes \<open>\<And>x. x \<in> A-B \<Longrightarrow> f x \<le> 0\<close>
  assumes \<open>\<And>x. x \<in> B-A \<Longrightarrow> g x \<ge> 0\<close>
  shows "a \<le> b"
proof -
  from assms 
  have sum_hfh: \<open>((\<lambda>x. h \<bullet>\<^sub>C f x h) has_sum h \<bullet>\<^sub>C a h) A\<close> for h
    by (intro has_sum_cinner_left has_sum_cblinfun_apply_left)
  from assms
  have sum_hgh: \<open>((\<lambda>x. h \<bullet>\<^sub>C g x h) has_sum h \<bullet>\<^sub>C b h) B\<close> for h
    by (intro has_sum_cinner_left has_sum_cblinfun_apply_left)
  from sum_hfh sum_hgh
  have \<open>h \<bullet>\<^sub>C a h \<le> h \<bullet>\<^sub>C b h\<close> for h
    apply (rule has_sum_mono_neutral_complex)
    using assms
    by (auto intro!: simp: less_eq_cblinfun_def)
  then show \<open>a \<le> b\<close>
    by (simp add: less_eq_cblinfun_def)
qed

lemma sums_mono_cblinfun:
  fixes f :: "nat \<Rightarrow> ('b::chilbert_space \<Rightarrow>\<^sub>C\<^sub>L 'b)"
  assumes \<open>f sums a\<close> and "g sums b"
  assumes \<open>\<And>n. f n \<le> g n\<close>
  shows "a \<le> b"
proof (rule cblinfun_leI)
  fix h
  from \<open>f sums a\<close>
  have sum1: \<open>(\<lambda>n. h \<bullet>\<^sub>C (f n *\<^sub>V h)) sums (h \<bullet>\<^sub>C (a *\<^sub>V h))\<close>
    apply (rule bounded_linear.sums[rotated])
    using bounded_clinear.bounded_linear bounded_clinear_cinner_right bounded_linear_compose cblinfun.real.bounded_linear_left by blast 
  from \<open>g sums b\<close>
  have sum2: \<open>(\<lambda>n. h \<bullet>\<^sub>C (g n *\<^sub>V h)) sums (h \<bullet>\<^sub>C (b *\<^sub>V h))\<close>
    apply (rule bounded_linear.sums[rotated])
    by (metis bounded_linear_compose cblinfun.real.bounded_linear_left cblinfun.real.bounded_linear_right cblinfun_cinner_right.rep_eq) 
  have \<open>h \<bullet>\<^sub>C (f n *\<^sub>V h) \<le> h \<bullet>\<^sub>C (g n *\<^sub>V h)\<close> for n
    using assms(3) less_eq_cblinfun_def by auto 
  with sum1 sum2
  show \<open>h \<bullet>\<^sub>C (a *\<^sub>V h) \<le> h \<bullet>\<^sub>C (b *\<^sub>V h)\<close>
    by (rule sums_le_complex[rotated])
qed

lemma scaleC_scaleR_commute: \<open>a *\<^sub>C b *\<^sub>R x = b *\<^sub>R a *\<^sub>C x\<close> for x :: \<open>_::complex_normed_vector\<close>
  by (simp add: scaleR_scaleC scaleC_left_commute)


lemma sandwich_scaleC_left: \<open>sandwich (c *\<^sub>C e) = (cmod c)^2 *\<^sub>C sandwich e\<close>
  by (auto intro!: cblinfun_eqI simp: sandwich_apply cnj_x_x abs_complex_def)

lemma sandwich_scaleR_left: \<open>sandwich (r *\<^sub>R e) = r^2 *\<^sub>R sandwich e\<close>
  by (simp add: scaleR_scaleC sandwich_scaleC_left flip: of_real_power)

lemma infsum_product:
  fixes f :: \<open>'a \<Rightarrow> 'c :: {topological_semigroup_mult,division_ring,banach}\<close>
  assumes \<open>(\<lambda>(x, y). f x * g y) summable_on X \<times> Y\<close>
  shows \<open>(\<Sum>\<^sub>\<infinity>x\<in>X. f x) * (\<Sum>\<^sub>\<infinity>y\<in>Y. g y) = (\<Sum>\<^sub>\<infinity>(x,y)\<in>X\<times>Y. f x * g y)\<close>
  using assms
  by (simp add: infsum_cmult_right' infsum_cmult_left' flip: infsum_Sigma'_banach)

lemma infsum_product':
  fixes f :: \<open>'a \<Rightarrow> 'c :: {banach,times,real_normed_algebra}\<close> and g :: \<open>'b \<Rightarrow> 'c\<close>
  assumes \<open>f abs_summable_on X\<close>
  assumes \<open>g abs_summable_on Y\<close>
  shows \<open>(\<Sum>\<^sub>\<infinity>x\<in>X. f x) * (\<Sum>\<^sub>\<infinity>y\<in>Y. g y) = (\<Sum>\<^sub>\<infinity>(x,y)\<in>X\<times>Y. f x * g y)\<close>
  using assms
  by (simp add: abs_summable_times infsum_cmult_right infsum_cmult_left abs_summable_summable flip: infsum_Sigma'_banach)

lemma Proj_o_Proj_subspace_right:
  assumes \<open>A \<ge> B\<close>
  shows \<open>Proj A o\<^sub>C\<^sub>L Proj B = Proj B\<close>
  by (simp add: Proj_compose_cancelI assms) 

lemma Proj_o_Proj_subspace_left:
  assumes \<open>A \<le> B\<close>
  shows \<open>Proj A o\<^sub>C\<^sub>L Proj B = Proj A\<close>
  by (metis Proj_o_Proj_subspace_right adj_Proj adj_cblinfun_compose assms) 

lemma orthogonal_spaces_SUP_left:
  assumes \<open>\<And>x. x \<in> X \<Longrightarrow> orthogonal_spaces (A x) B\<close>
  shows \<open>orthogonal_spaces (\<Squnion>x\<in>X. A x) B\<close>
  by (meson SUP_least assms orthogonal_spaces_leq_compl) 

lemma orthogonal_spaces_SUP_right:
  assumes \<open>\<And>x. x \<in> X \<Longrightarrow> orthogonal_spaces A (B x)\<close>
  shows \<open>orthogonal_spaces A (\<Squnion>x\<in>X. B x)\<close>
  by (meson assms orthogonal_spaces_SUP_left orthogonal_spaces_sym) 

(* Should be put next to orthogonal_bot *)
lemma orthogonal_bot_left[simp]: \<open>orthogonal_spaces bot S\<close>
  by (simp add: orthogonal_spaces_def)

lemma infsum_bounded_linear_invertible:
  assumes \<open>bounded_linear h\<close>
  assumes \<open>bounded_linear h'\<close>
  assumes \<open>h' o h = id\<close>
  shows \<open>infsum (\<lambda>x. h (f x)) A = h (infsum f A)\<close>
proof (cases \<open>f summable_on A\<close>)
  case True
  then show ?thesis
    using assms(1) infsum_bounded_linear by blast
next
  case False
  have \<open>\<not> (\<lambda>x. h (f x)) summable_on A\<close>
  proof (rule ccontr)
    assume \<open>\<not> \<not> (\<lambda>x. h (f x)) summable_on A\<close>
    with \<open>bounded_linear h'\<close> have \<open>h' o h o f summable_on A\<close>
      by (auto intro: summable_on_bounded_linear simp: o_def)
    then have \<open>f summable_on A\<close>
      by (simp add: assms(3))
    with False show False
      by blast
  qed
  then show ?thesis
    by (simp add: False assms(1) infsum_not_exists linear_simps(3))
qed

lemma cblinfun_eq_from_separatingI:
  fixes a b :: \<open>'a::complex_normed_vector \<Rightarrow>\<^sub>C\<^sub>L 'b::complex_normed_vector\<close>
  assumes \<open>separating_set (bounded_clinear :: ('a \<Rightarrow> 'b) \<Rightarrow> bool) S\<close>
  assumes \<open>\<And>x. x \<in> S \<Longrightarrow> a x = b x\<close>
  shows \<open>a = b\<close>
  apply (rule cblinfun_eqI, rule fun_cong[where f=\<open>cblinfun_apply _\<close>])
  using assms(1) apply (rule eq_from_separatingI)
  using assms(2) by (auto intro!: bounded_cbilinear_apply_bounded_clinear cblinfun.bounded_cbilinear_axioms simp: )

lemma cblinfun_eq_from_separatingI2:
  fixes a b :: \<open>'a::complex_normed_vector \<Rightarrow>\<^sub>C\<^sub>L 'b::complex_normed_vector\<close>
  assumes \<open>separating_set (bounded_clinear :: ('a \<Rightarrow> 'b) \<Rightarrow> bool) ((\<lambda>(x,y). h x y) ` (S\<times>T))\<close>
  assumes \<open>\<And>x y. x \<in> S \<Longrightarrow> y \<in> T \<Longrightarrow> a (h x y) = b (h x y)\<close>
  shows \<open>a = b\<close>
  apply (rule cblinfun_eqI, rule fun_cong[where f=\<open>cblinfun_apply _\<close>])
  using assms(1) apply (rule eq_from_separatingI2)
  using assms(2) by (auto intro!: bounded_cbilinear_apply_bounded_clinear cblinfun.bounded_cbilinear_axioms simp: )

lemma separating_set_bounded_clinear_dense:
  assumes \<open>ccspan S = \<top>\<close>
  shows \<open>separating_set bounded_clinear S\<close>
  unfolding separating_set_def
  by (intro allI impI ext, rule bounded_clinear_eq_on_closure[where G=S])
     (use assms ccspan.rep_eq in force)+

lemma separating_set_ket: \<open>separating_set bounded_clinear (range ket)\<close>
  by (simp add: bounded_clinear_equal_ket separating_setI)

lemma separating_set_bounded_cbilinear_nested:
  assumes \<open>separating_set (bounded_clinear :: (_ => 'e::complex_normed_vector) \<Rightarrow> _) ((\<lambda>(x, y). h x y) ` (UNIV \<times> UNIV))\<close>
  assumes \<open>bounded_cbilinear h\<close>
  assumes \<open>separating_set (bounded_clinear :: (_ => 'e) \<Rightarrow> _) A\<close>
  assumes \<open>separating_set (bounded_clinear :: (_ => 'e) \<Rightarrow> _) B\<close>
  shows \<open>separating_set (bounded_clinear :: (_ => 'e) \<Rightarrow> _) ((\<lambda>(x,y). h x y) ` (A \<times> B))\<close>
proof (rule separating_setI)
  fix f g :: \<open>'a \<Rightarrow> 'e\<close>
  assume [simp]: \<open>bounded_clinear f\<close> \<open>bounded_clinear g\<close>
  have [simp]: \<open>bounded_clinear (\<lambda>x. f (h x y))\<close> for y
    apply (rule bounded_clinear_compose[OF \<open>bounded_clinear f\<close>])
    using assms(2) by (rule bounded_cbilinear.bounded_clinear_left)
  have [simp]: \<open>bounded_clinear (\<lambda>x. g (h x y))\<close> for y
    apply (rule bounded_clinear_compose[OF \<open>bounded_clinear g\<close>])
    using assms(2) by (rule bounded_cbilinear.bounded_clinear_left)
  have [simp]: \<open>bounded_clinear (\<lambda>y. f (h x y))\<close> for x
    apply (rule bounded_clinear_compose[OF \<open>bounded_clinear f\<close>])
    using assms(2) by (rule bounded_cbilinear.bounded_clinear_right)
  have [simp]: \<open>bounded_clinear (\<lambda>y. g (h x y))\<close> for x
    apply (rule bounded_clinear_compose[OF \<open>bounded_clinear g\<close>])
    using assms(2) by (rule bounded_cbilinear.bounded_clinear_right)

  assume \<open>z \<in> (\<lambda>(x, y). h x y) ` (A \<times> B) \<Longrightarrow> f z = g z\<close> for z
  then have \<open>f (h x y) = g (h x y)\<close> if \<open>x \<in> A\<close> and \<open>y \<in> B\<close> for x y
    using that by auto
  then have \<open>(\<lambda>x. f (h x y)) = (\<lambda>x. g (h x y))\<close> if \<open>y \<in> B\<close> for y
    by (intro eq_from_separatingI[OF assms(3)]) (use that in auto)
  then have \<open>(\<lambda>y. f (h x y)) = (\<lambda>y. g (h x y))\<close> for x
    apply (intro eq_from_separatingI[OF assms(4)])
    subgoal by simp
    subgoal by simp
    subgoal by meson
    done
  then have \<open>f (h x y) = g (h x y)\<close> for x y
    by meson
  with \<open>bounded_clinear f\<close> \<open>bounded_clinear g\<close>
  show \<open>f = g\<close>
    by (rule eq_from_separatingI2[where f=f and g=g and P=bounded_clinear and S=UNIV and T=UNIV, rotated 1])
       (fact assms(1))
qed


lemma separating_set_bounded_clinear_antilinear:
  assumes \<open>separating_set (bounded_clinear :: (_ => 'e::complex_normed_vector conjugate_space) \<Rightarrow> _) A\<close>
  shows \<open>separating_set (bounded_antilinear :: (_ => 'e) \<Rightarrow> _) A\<close>
proof (rule separating_setI)
  fix f g :: \<open>'a \<Rightarrow> 'e\<close>
  assume \<open>bounded_antilinear f\<close>
  then have lin_f: \<open>bounded_clinear (to_conjugate_space o f)\<close>
    by (simp add: bounded_antilinear_o_bounded_antilinear')
  assume \<open>bounded_antilinear g\<close>
  then have lin_g: \<open>bounded_clinear (to_conjugate_space o g)\<close>
    by (simp add: bounded_antilinear_o_bounded_antilinear')
  assume \<open>f x = g x\<close> if \<open>x \<in> A\<close> for x
  then have \<open>(to_conjugate_space o f) x = (to_conjugate_space o g) x\<close> if \<open>x \<in> A\<close> for x
    by (simp add: that)
  with lin_f lin_g
  have \<open>to_conjugate_space o f = to_conjugate_space o g\<close>
    by (rule eq_from_separatingI[OF assms])
  then show \<open>f = g\<close>
    by (metis UNIV_I fun.inj_map_strong to_conjugate_space_inverse)
qed

lemma separating_set_bounded_sesquilinear_nested:
  assumes \<open>separating_set (bounded_clinear :: (_ => 'e::complex_normed_vector) \<Rightarrow> _) ((\<lambda>(x, y). h x y) ` (UNIV \<times> UNIV))\<close>
  assumes \<open>bounded_sesquilinear h\<close>
  assumes sep_A: \<open>separating_set (bounded_clinear :: (_ => 'e conjugate_space) \<Rightarrow> _) A\<close>
  assumes sep_B: \<open>separating_set (bounded_clinear :: (_ => 'e) \<Rightarrow> _) B\<close>
  shows \<open>separating_set (bounded_clinear :: (_ => 'e) \<Rightarrow> _) ((\<lambda>(x,y). h x y) ` (A \<times> B))\<close>
proof (rule separating_setI)
  fix f g :: \<open>'a \<Rightarrow> 'e\<close>
  assume [simp]: \<open>bounded_clinear f\<close> \<open>bounded_clinear g\<close>
  have [simp]: \<open>bounded_antilinear (\<lambda>x. f (h x y))\<close> for y
    apply (rule bounded_clinear_o_bounded_antilinear[OF \<open>bounded_clinear f\<close>])
    using assms(2) by (rule bounded_sesquilinear.bounded_antilinear_left)
  have [simp]: \<open>bounded_antilinear (\<lambda>x. g (h x y))\<close> for y
    apply (rule bounded_clinear_o_bounded_antilinear[OF \<open>bounded_clinear g\<close>])
    using assms(2) by (rule bounded_sesquilinear.bounded_antilinear_left)
  have [simp]: \<open>bounded_clinear (\<lambda>y. f (h x y))\<close> for x
    apply (rule bounded_clinear_compose[OF \<open>bounded_clinear f\<close>])
    using assms(2) by (rule bounded_sesquilinear.bounded_clinear_right)
  have [simp]: \<open>bounded_clinear (\<lambda>y. g (h x y))\<close> for x
    apply (rule bounded_clinear_compose[OF \<open>bounded_clinear g\<close>])
    using assms(2) by (rule bounded_sesquilinear.bounded_clinear_right)

  from sep_A have sep_A': \<open>separating_set (bounded_antilinear :: (_ => 'e) \<Rightarrow> _) A\<close>
    by (rule separating_set_bounded_clinear_antilinear)
  assume \<open>z \<in> (\<lambda>(x, y). h x y) ` (A \<times> B) \<Longrightarrow> f z = g z\<close> for z
  then have \<open>f (h x y) = g (h x y)\<close> if \<open>x \<in> A\<close> and \<open>y \<in> B\<close> for x y
    using that by auto
  then have \<open>(\<lambda>x. f (h x y)) = (\<lambda>x. g (h x y))\<close> if \<open>y \<in> B\<close> for y
    by (intro eq_from_separatingI[OF sep_A']) (use that in auto)
  then have \<open>(\<lambda>y. f (h x y)) = (\<lambda>y. g (h x y))\<close> for x
    apply (intro eq_from_separatingI[OF sep_B])
    subgoal by simp
    subgoal by simp
    subgoal by meson
    done
  then have \<open>f (h x y) = g (h x y)\<close> for x y
    by meson
  with \<open>bounded_clinear f\<close> \<open>bounded_clinear g\<close>
  show \<open>f = g\<close>
    by (rule eq_from_separatingI2[where f=f and g=g and P=bounded_clinear and S=UNIV and T=UNIV, rotated 1])
       (fact assms(1))
qed

lemma eq_on_ccsubspaces_Sup:
  fixes a b :: \<open>'a::complex_normed_vector \<Rightarrow>\<^sub>C\<^sub>L 'b::complex_normed_vector\<close>
  assumes \<open>\<And>i h. i \<in> I \<Longrightarrow> h \<in> space_as_set (X i) \<Longrightarrow> a h = b h\<close>
  shows \<open>\<And>h. h \<in> space_as_set (\<Squnion>i\<in>I. X i) \<Longrightarrow> a h = b h\<close>
proof -
  from assms
  have \<open>X i \<le> kernel (a - b)\<close> if \<open>i \<in> I\<close> for i
    using that by (auto intro!: ccsubspace_leI simp: kernel.rep_eq minus_cblinfun.rep_eq)
  then have \<open>(\<Squnion>i\<in>I. X i) \<le> kernel (a - b)\<close>
    by (simp add: SUP_least) 
  then show \<open>h \<in> space_as_set (\<Squnion>i\<in>I. X i) \<Longrightarrow> a h = b h\<close> for h
    using kernel_memberD less_eq_ccsubspace.rep_eq 
    by (metis (no_types, opaque_lifting) cblinfun.diff_left cblinfun.real.diff_right cblinfun.real.zero_left diff_eq_diff_eq double_diff mem_simps(6) subset_refl)
qed

lemma eq_on_ccsubspaces_sup:
  fixes a b :: \<open>'a::complex_normed_vector \<Rightarrow>\<^sub>C\<^sub>L 'b::complex_normed_vector\<close>
  assumes \<open>\<And>h i. h \<in> space_as_set S \<Longrightarrow> a h = b h\<close>
  assumes \<open>\<And>h i. h \<in> space_as_set T \<Longrightarrow> a h = b h\<close>
  shows \<open>\<And>h. h \<in> space_as_set (S \<squnion> T) \<Longrightarrow> a h = b h\<close>
  apply (rule eq_on_ccsubspaces_Sup[where I=\<open>{True,False}\<close> and X=\<open>\<lambda>i. if i then T else S\<close>])
  using assms
   apply presburger
  by fastforce


lemma ccsubspace_contains_unit:
  assumes \<open>E \<noteq> \<bottom>\<close>
  shows \<open>\<exists>h\<in>space_as_set E. norm h = 1\<close>
proof -
  from assms have \<open>space_as_set E \<noteq> {0}\<close>
    by (metis bot_ccsubspace.rep_eq space_as_set_inject)
  then obtain h\<^sub>0 where \<open>h\<^sub>0 \<in> space_as_set E\<close> and \<open>h\<^sub>0 \<noteq> 0\<close>
    by auto
  then have \<open>sgn h\<^sub>0 \<in> space_as_set E\<close>
    using csubspace_space_as_set
    by (auto intro!: complex_vector.subspace_scale
        simp add: sgn_div_norm scaleR_scaleC)
  moreover from \<open>h\<^sub>0 \<noteq> 0\<close> have \<open>norm (sgn h\<^sub>0) = 1\<close>
    by (simp add: norm_sgn)
  ultimately show ?thesis
    by auto
qed



lemma Proj_0_compl: \<open>Proj S x = 0\<close> if \<open>x \<in> space_as_set (-S)\<close>
  by (simp add: kernel_memberD that)

lemma csubspace_has_basis:
  assumes \<open>csubspace S\<close>
  shows \<open>\<exists>B. cindependent B \<and> cspan B = S\<close>
proof -
  obtain B where \<open>cindependent B\<close> and \<open>cspan B = S\<close>
    by (rule complex_vector.maximal_independent_subset[where V=S])
       (use assms complex_vector.span_subspace in blast)
  then show ?thesis
    by auto
qed

lemma inj_scaleC:
  fixes A :: \<open>'a::complex_vector set\<close>
  assumes \<open>c \<noteq> 0\<close>
  shows \<open>inj_on (scaleC c) A\<close>
  by (meson assms inj_onI scaleC_left_imp_eq)

definition diagonal_operator where \<open>diagonal_operator f = 
  (if bdd_above (range (\<lambda>x. cmod (f x))) then explicit_cblinfun (\<lambda>x y. of_bool (x=y) * f x) else 0)\<close>


lemma diagonal_operator_exists:
  assumes \<open>bdd_above (range (\<lambda>x. cmod (f x)))\<close>
  shows \<open>explicit_cblinfun_exists (\<lambda>x y. of_bool (x = y) * f x)\<close>
proof -
  from assms obtain B where B: \<open>cmod (f x) \<le> B\<close> for x
    by (auto simp: bdd_above_def)
  show ?thesis
  proof (rule explicit_cblinfun_exists_bounded)
    fix S T :: \<open>'a set\<close> and \<psi> :: \<open>'a \<Rightarrow> complex\<close>
    assume [simp]: \<open>finite S\<close> \<open>finite T\<close>
    assume \<open>\<psi> a = 0\<close> if \<open>a \<notin> T\<close> for a
    have \<open>(\<Sum>b\<in>S. (cmod (\<Sum>a\<in>T. \<psi> a *\<^sub>C (of_bool (b = a) * f b)))\<^sup>2)
        = (\<Sum>b\<in>S. (cmod (of_bool (b \<in> T) * \<psi> b * f b))\<^sup>2)\<close>
      apply (rule sum.cong[OF refl])
      subgoal for b
        apply (subst sum_single[where i=b])
        by auto
      by -
    also have \<open>\<dots> = (\<Sum>b\<in>S\<inter>T. (cmod (\<psi> b * f b))\<^sup>2)\<close>
      apply (rule sum.mono_neutral_cong_right)
      by auto
    also have \<open>\<dots> \<le> (\<Sum>b\<in>T. (cmod (\<psi> b * f b))\<^sup>2)\<close>
      by (simp add: sum_mono2)
    also have \<open>\<dots> \<le> (\<Sum>b\<in>T. B\<^sup>2 * (cmod (\<psi> b))\<^sup>2)\<close>
      by (rule sum_mono)
         (auto intro!: mult_left_mono  power_mono B
               simp: norm_mult power_mult_distrib mult.commute[of "B ^ 2"])
    also have \<open>\<dots> = B\<^sup>2 * (\<Sum>b\<in>T. (cmod (\<psi> b))\<^sup>2)\<close>
      by (simp add: vector_space_over_itself.scale_sum_right)
    finally
    show \<open>(\<Sum>b\<in>S. (cmod (\<Sum>a\<in>T. \<psi> a *\<^sub>C (of_bool (b = a) * f b)))\<^sup>2)
       \<le> B\<^sup>2 * (\<Sum>a\<in>T. (cmod (\<psi> a))\<^sup>2)\<close> .
  qed
qed


lemma diagonal_operator_ket:
  assumes \<open>bdd_above (range (\<lambda>x. cmod (f x)))\<close>
  shows \<open>diagonal_operator f (ket x) = f x *\<^sub>C ket x\<close>
proof -
  have [simp]: \<open>has_ell2_norm (\<lambda>b. of_bool (b = x) * f b)\<close>
    by (auto intro!: finite_nonzero_values_imp_summable_on simp: has_ell2_norm_def)
  have \<open>Abs_ell2 (\<lambda>b. of_bool (b = x) * f b) = f x *\<^sub>C ket x\<close>
    by (rule Rep_ell2_inject[THEN iffD1])
       (auto simp: Abs_ell2_inverse scaleC_ell2.rep_eq ket.rep_eq)
  then show ?thesis
    by (auto intro!: simp: diagonal_operator_def assms explicit_cblinfun_ket diagonal_operator_exists)
qed

lemma diagonal_operator_invalid:
  assumes \<open>\<not> bdd_above (range (\<lambda>x. cmod (f x)))\<close>
  shows \<open>diagonal_operator f = 0\<close>
  by (simp add: assms diagonal_operator_def)


lemma diagonal_operator_adj: \<open>diagonal_operator f* = diagonal_operator (\<lambda>x. cnj (f x))\<close>
  by (cases \<open>bdd_above (range (\<lambda>x. cmod (f x)))\<close>)
     (auto intro!: equal_ket cinner_ket_eqI 
           simp: diagonal_operator_ket cinner_adj_right diagonal_operator_invalid)

lemma diagonal_operator_comp:
  assumes \<open>bdd_above (range (\<lambda>x. cmod (f x)))\<close>
  assumes \<open>bdd_above (range (\<lambda>x. cmod (g x)))\<close>
  shows \<open>diagonal_operator f o\<^sub>C\<^sub>L diagonal_operator g = diagonal_operator (\<lambda>x. (f x * g x))\<close>
proof -
  have \<open>bdd_above (range (\<lambda>x. cmod (f x * g x)))\<close>
  proof -
    from assms(1) obtain F where \<open>cmod (f x) \<le> F\<close> for x
      by (auto simp: bdd_above_def)
    moreover from assms(2) obtain G where \<open>cmod (g x) \<le> G\<close> for x
      by (auto simp: bdd_above_def)
    ultimately have \<open>cmod (f x * g x) \<le> F * G\<close> for x
      by (smt (verit, del_insts) mult_right_mono norm_ge_zero norm_mult ordered_comm_semiring_class.comm_mult_left_mono)
    then show ?thesis
      by fast
  qed
  then show ?thesis
    by (auto intro!: equal_ket simp: diagonal_operator_ket assms cblinfun.scaleC_right)
qed

lemma summable_on_bdd_above_real: \<open>bdd_above (f ` M)\<close> if \<open>f summable_on M\<close> for f :: \<open>'a \<Rightarrow> real\<close>
proof -
  from that have \<open>f abs_summable_on M\<close>
    unfolding summable_on_iff_abs_summable_on_real[symmetric]
    by -
  then have \<open>bdd_above (sum (\<lambda>x. norm (f x)) ` {F. F \<subseteq> M \<and> finite F})\<close>
    unfolding abs_summable_iff_bdd_above by simp
  then have \<open>bdd_above (sum (\<lambda>x. norm (f x)) ` (\<lambda>x. {x}) ` M)\<close>
    by (rule bdd_above_mono) auto
  then have \<open>bdd_above ((\<lambda>x. norm (f x)) ` M)\<close>
    by (simp add: image_image)
  then show ?thesis
    by (simp add: bdd_above_mono2)
qed

lemma separating_set_clinear_cspan:
  assumes \<open>cspan S = UNIV\<close>
  shows \<open>separating_set clinear S\<close>
  using assms
  by (auto intro: complex_vector.linear_eq_on simp: separating_set_def)

lemma less_eq_cblinfunI:
  fixes a b :: \<open>'a \<Rightarrow>\<^sub>C\<^sub>L 'a::chilbert_space\<close>
  assumes \<open>\<And>h. h \<bullet>\<^sub>C a h \<le> h \<bullet>\<^sub>C b h\<close>
  shows \<open>a \<le> b\<close>
  using assms
  by (simp add: less_eq_cblinfun_def)

end
