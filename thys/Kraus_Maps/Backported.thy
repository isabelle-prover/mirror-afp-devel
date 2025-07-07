section \<open>Backported theorems\<close>

text \<open>This theory contains various lemmas that are already contained in a fork of the AFP but have
  not yet been ported to the official AFP. (Sessions \<^session>\<open>Complex_Bounded_Operators\<close> and
  \<^session>\<open>Hilbert_Space_Tensor_Product\<close> from \<^url>\<open>https://github.com/dominique-unruh/afp/tree/unruh-edits\<close>.)\<close>

theory Backported
  imports Hilbert_Space_Tensor_Product.Trace_Class
    Hilbert_Space_Tensor_Product.Hilbert_Space_Tensor_Product
begin

unbundle cblinfun_syntax

lemma abs_summable_norm:
  assumes \<open>f abs_summable_on A\<close>
  shows \<open>(\<lambda>x. norm (f x)) abs_summable_on A\<close>
  using assms by simp

lemma abs_summable_on_add:
  assumes \<open>f abs_summable_on A\<close> and \<open>g abs_summable_on A\<close>
  shows \<open>(\<lambda>x. f x + g x) abs_summable_on A\<close>
proof -
  from assms have \<open>(\<lambda>x. norm (f x) + norm (g x)) summable_on A\<close>
    using summable_on_add by blast
  then show ?thesis
    apply (rule Infinite_Sum.abs_summable_on_comparison_test')
    using norm_triangle_ineq by blast
qed

lemma bdd_above_transform_mono_pos:
  assumes bdd: \<open>bdd_above ((\<lambda>x. g x) ` M)\<close>
  assumes gpos: \<open>\<And>x. x \<in> M \<Longrightarrow> g x \<ge> 0\<close>
  assumes mono: \<open>mono_on (Collect ((\<le>) 0)) f\<close>
  shows \<open>bdd_above ((\<lambda>x. f (g x)) ` M)\<close>
proof (cases \<open>M = {}\<close>)
  case True
  then show ?thesis
    by simp
next
  case False
  from bdd obtain B where B: \<open>g x \<le> B\<close> if \<open>x \<in> M\<close> for x
  by (meson bdd_above.unfold imageI)
  with gpos False have \<open>B \<ge> 0\<close>
    using dual_order.trans by blast
  have \<open>f (g x) \<le> f B\<close> if \<open>x \<in> M\<close> for x
    using mono _ _ B
    apply (rule mono_onD)
    by (auto intro!: gpos that  \<open>B \<ge> 0\<close>)
  then show ?thesis
    by fast
qed

lemma Ex_iffI:
  assumes \<open>\<And>x. P x \<Longrightarrow> Q (f x)\<close>
  assumes \<open>\<And>x. Q x \<Longrightarrow> P (g x)\<close>
  shows \<open>Ex P \<longleftrightarrow> Ex Q\<close>
  using assms(1) assms(2) by auto

lemma has_sum_Sigma'_banach:
  fixes A :: "'a set" and B :: "'a \<Rightarrow> 'b set"
    and f :: \<open>'a \<Rightarrow> 'b \<Rightarrow> 'c::banach\<close>
  assumes "((\<lambda>(x,y). f x y) has_sum S) (Sigma A B)"
  shows \<open>((\<lambda>x. infsum (f x) (B x)) has_sum S) A\<close>
  by (metis (no_types, lifting) assms has_sum_cong has_sum_imp_summable has_sum_infsum infsumI infsum_Sigma'_banach summable_on_Sigma_banach)

lemma summable_on_in_cong:
  assumes "\<And>x. x\<in>A \<Longrightarrow> f x = g x"
  shows "summable_on_in T f A \<longleftrightarrow> summable_on_in T g A"
  by (simp add: summable_on_in_def has_sum_in_cong[OF assms])

lemma infsum_of_bool_scaleC: \<open>(\<Sum>\<^sub>\<infinity>x\<in>X. of_bool (x=y) *\<^sub>C f x) = of_bool (y\<in>X) *\<^sub>C f y\<close> for f :: \<open>_ \<Rightarrow> _::complex_vector\<close>
  apply (cases \<open>y\<in>X\<close>)
   apply (subst infsum_cong_neutral[where T=\<open>{y}\<close> and g=f])
      apply auto[4]
  apply (subst infsum_cong_neutral[where T=\<open>{}\<close> and g=f])
  by auto

lemma infsum_in_0:
  assumes \<open>Hausdorff_space T\<close> and \<open>0 \<in> topspace T\<close>
  assumes \<open>\<And>x. x\<in>M \<Longrightarrow> f x = 0\<close>
  shows \<open>infsum_in T f M = 0\<close>
proof -
  have \<open>has_sum_in T f M 0\<close>
    using assms
    by (auto intro!: has_sum_in_0 Hausdorff_imp_t1_space)
  then show ?thesis
    by (meson assms(1) has_sum_in_infsum_in has_sum_in_unique not_summable_infsum_in_0)
qed

lemma summable_on_in_finite:
  fixes f :: \<open>'a \<Rightarrow> 'b::{comm_monoid_add,topological_space}\<close>
  assumes "finite F"
  assumes \<open>sum f F \<in> topspace T\<close>
  shows "summable_on_in T f F"
  using assms summable_on_in_def has_sum_in_finite by blast

lemma infsum_Sigma_topological_monoid:
  fixes A :: "'a set" and B :: "'a \<Rightarrow> 'b set"
    and f :: \<open>'a \<times> 'b \<Rightarrow> 'c::{topological_comm_monoid_add, t3_space}\<close>
  assumes summableAB: "f summable_on (Sigma A B)"
  assumes summableB: \<open>\<And>x. x\<in>A \<Longrightarrow> (\<lambda>y. f (x, y)) summable_on (B x)\<close>
  shows "infsum f (Sigma A B) = (\<Sum>\<^sub>\<infinity>x\<in>A. \<Sum>\<^sub>\<infinity>y\<in>B x. f (x, y))"
proof -
  have 1: \<open>(f has_sum infsum f (Sigma A B)) (Sigma A B)\<close>
    by (simp add: assms)
  define b where \<open>b x = (\<Sum>\<^sub>\<infinity>y\<in>B x. f (x, y))\<close> for x
  have 2: \<open>((\<lambda>y. f (x, y)) has_sum b x) (B x)\<close> if \<open>x \<in> A\<close> for x
    using b_def assms(2) that by auto
  have 3: \<open>(b has_sum (\<Sum>\<^sub>\<infinity>x\<in>A. b x)) A\<close>
    using 1 2 by (metis has_sum_SigmaD infsumI)
  have 4: \<open>(f has_sum (\<Sum>\<^sub>\<infinity>x\<in>A. b x)) (Sigma A B)\<close>
    using 2 3 apply (rule has_sum_SigmaI)
    using assms by auto
  from 1 4 show ?thesis
    using b_def[abs_def] infsumI by blast
qed

lemma ballI2 [intro!]: "(\<And>x y. (x,y) \<in> A \<Longrightarrow> P x y) \<Longrightarrow> \<forall>(x,y)\<in>A. P x y"
  by auto


lemma flip_eq_const: \<open>(\<lambda>y. y = x) = ((=) x)\<close>
  by auto

lemma vector_to_cblinfun_inj: \<open>inj_on (vector_to_cblinfun :: 'a::complex_normed_vector \<Rightarrow> 'b::one_dim \<Rightarrow>\<^sub>C\<^sub>L _) X\<close>
proof (rule inj_onI)
  fix x y :: 'a
  assume \<open>vector_to_cblinfun x = (vector_to_cblinfun y :: 'b \<Rightarrow>\<^sub>C\<^sub>L _)\<close>
  then have \<open>vector_to_cblinfun x (1::'b) = vector_to_cblinfun y (1::'b)\<close>
    by simp
  then show \<open>x = y\<close>
    by simp
qed

lemma has_sum_bounded_clinear:
  assumes "bounded_clinear h" and "(f has_sum S) A"
  shows "((\<lambda>x. h (f x)) has_sum h S) A"
  apply (rule has_sum_bounded_linear[where h=h])
  by (auto intro!: bounded_clinear.bounded_linear assms)

lemma has_sum_scaleC_right:
  fixes f :: \<open>'a \<Rightarrow> 'b :: complex_normed_vector\<close>
  assumes \<open>(f has_sum s) A\<close>
  shows \<open>((\<lambda>x. c *\<^sub>C f x) has_sum c *\<^sub>C s) A\<close>
  apply (rule has_sum_bounded_clinear[where h=\<open>(*\<^sub>C) c\<close>])
  using bounded_clinear_scaleC_right assms by auto

lemma norm_cblinfun_bound_both_sides:
  fixes a :: \<open>'a::complex_normed_vector \<Rightarrow>\<^sub>C\<^sub>L 'b::complex_inner\<close>
  assumes \<open>b \<ge> 0\<close>
  assumes leq: \<open>\<And>\<psi> \<phi>. norm \<psi> = 1 \<Longrightarrow> norm \<phi> = 1 \<Longrightarrow> norm (\<psi> \<bullet>\<^sub>C a \<phi>) \<le> b\<close>
  shows \<open>norm a \<le> b\<close>
proof -
  wlog not_singleton: \<open>class.not_singleton TYPE('a)\<close>
    apply (subst not_not_singleton_cblinfun_zero)
    by (simp_all add: negation assms)
  have \<open>norm a = (\<Squnion>(\<psi>, \<phi>). cmod (\<psi> \<bullet>\<^sub>C (a *\<^sub>V \<phi>)) / (norm \<psi> * norm \<phi>))\<close>
    apply (rule cinner_sup_norm_cblinfun[internalize_sort' 'a])
     apply (rule complex_normed_vector_axioms)
    by (fact not_singleton)
  also have \<open>\<dots> \<le> b\<close>
  proof (rule cSUP_least)
    show \<open>UNIV \<noteq> {}\<close>
      by simp
    fix x :: \<open>'b \<times> 'a\<close>
    obtain \<psi> \<phi> where x: \<open>x = (\<psi>, \<phi>)\<close>
      by fastforce
    have \<open>(case x of (\<psi>, \<phi>) \<Rightarrow> cmod (\<psi> \<bullet>\<^sub>C (a *\<^sub>V \<phi>)) / (norm \<psi> * norm \<phi>)) = cmod (\<psi> \<bullet>\<^sub>C a \<phi>) / (norm \<psi> * norm \<phi>)\<close>
      using x by force
    also have \<open>\<dots> = cmod (sgn \<psi> \<bullet>\<^sub>C a (sgn \<phi>))\<close>
      by (simp add: sgn_div_norm cblinfun.scaleR_right divide_inverse_commute norm_inverse norm_mult)
    also have \<open>\<dots> \<le> b\<close>
      apply (cases \<open>\<psi> = 0\<close>, simp add: assms)
      apply (cases \<open>\<phi> = 0\<close>, simp add: assms)
      apply (rule leq)
      by (simp_all add: norm_sgn)
    finally show \<open>(case x of (\<psi>, \<phi>) \<Rightarrow> cmod (\<psi> \<bullet>\<^sub>C (a *\<^sub>V \<phi>)) / (norm \<psi> * norm \<phi>)) \<le> b\<close>
      by -
  qed
  finally show ?thesis
    by -
qed

lemma has_sum_in_weaker_topology:
  assumes \<open>continuous_map T U (\<lambda>f. f)\<close>
  assumes \<open>has_sum_in T f A l\<close>
  shows \<open>has_sum_in U f A l\<close>
  using continuous_map_limit[OF assms(1)]
  using assms(2)
  by (auto simp: has_sum_in_def o_def)

lemma summable_on_in_weaker_topology:
  assumes \<open>continuous_map T U (\<lambda>f. f)\<close>
  assumes \<open>summable_on_in T f A\<close>
  shows \<open>summable_on_in U f A\<close>
  by (meson assms(1,2) has_sum_in_weaker_topology summable_on_in_def)

lemma summable_imp_wot_summable: 
  assumes \<open>f summable_on A\<close>
  shows \<open>summable_on_in cweak_operator_topology f A\<close>
  apply (rule summable_on_in_weaker_topology)
   apply (rule cweak_operator_topology_weaker_than_euclidean)
  by (simp add: assms summable_on_euclidean_eq)

lemma triangle_ineq_wot:
  assumes \<open>f abs_summable_on A\<close>
  shows \<open>norm (infsum_in cweak_operator_topology f A) \<le> (\<Sum>\<^sub>\<infinity>x\<in>A. norm (f x))\<close>
proof -
  wlog summable: \<open>summable_on_in cweak_operator_topology f A\<close>
    by (simp add: infsum_nonneg negation not_summable_infsum_in_0)
  have \<open>cmod (\<psi> \<bullet>\<^sub>C (infsum_in cweak_operator_topology f A *\<^sub>V \<phi>)) \<le> (\<Sum>\<^sub>\<infinity>x\<in>A. norm (f x))\<close>
    if \<open>norm \<psi> = 1\<close> and \<open>norm \<phi> = 1\<close> for \<psi> \<phi>
  proof -
    have sum1: \<open>(\<lambda>a. \<psi> \<bullet>\<^sub>C (f a *\<^sub>V \<phi>)) abs_summable_on A\<close>
      by (metis local.summable summable_on_iff_abs_summable_on_complex summable_on_in_cweak_operator_topology_pointwise)
    have \<open>\<psi> \<bullet>\<^sub>C infsum_in cweak_operator_topology f A \<phi> = (\<Sum>\<^sub>\<infinity>a\<in>A. \<psi> \<bullet>\<^sub>C f a \<phi>)\<close>
      using summable by (rule infsum_in_cweak_operator_topology_pointwise)
    then have \<open>cmod (\<psi> \<bullet>\<^sub>C (infsum_in cweak_operator_topology f A *\<^sub>V \<phi>)) = norm (\<Sum>\<^sub>\<infinity>a\<in>A. \<psi> \<bullet>\<^sub>C f a \<phi>)\<close>
      by presburger
    also have \<open>\<dots> \<le> (\<Sum>\<^sub>\<infinity>a\<in>A. norm (\<psi> \<bullet>\<^sub>C f a \<phi>))\<close>
      apply (rule norm_infsum_bound)
      by (metis summable summable_on_iff_abs_summable_on_complex
          summable_on_in_cweak_operator_topology_pointwise)
    also have \<open>\<dots> \<le> (\<Sum>\<^sub>\<infinity>a\<in>A. norm (f a))\<close>
      using sum1 assms apply (rule infsum_mono)
      by (smt (verit) complex_inner_class.Cauchy_Schwarz_ineq2 mult_cancel_left1 mult_cancel_right1 norm_cblinfun that(1,2))
    finally show ?thesis
      by -
  qed
  then show ?thesis
    apply (rule_tac norm_cblinfun_bound_both_sides)
    by (auto simp: infsum_nonneg)
qed

lemma trace_tc_butterfly: \<open>trace_tc (tc_butterfly x y) = y \<bullet>\<^sub>C x\<close>
  apply (transfer fixing: x y)
  by (rule trace_butterfly)

lemma sandwich_tensor_ell2_right': \<open>sandwich (tensor_ell2_right \<psi>) *\<^sub>V a = a \<otimes>\<^sub>o selfbutter \<psi>\<close>
  apply (rule cblinfun_cinner_tensor_eqI)
  by (simp add: sandwich_apply tensor_op_ell2 cblinfun.scaleC_right)
lemma sandwich_tensor_ell2_left': \<open>sandwich (tensor_ell2_left \<psi>) *\<^sub>V a = selfbutter \<psi> \<otimes>\<^sub>o a\<close>
  apply (rule cblinfun_cinner_tensor_eqI)
  by (simp add: sandwich_apply tensor_op_ell2 cblinfun.scaleC_right)

lemma to_conjugate_space_0[simp]: \<open>to_conjugate_space 0 = 0\<close>
  by (simp add: zero_conjugate_space.abs_eq)
lemma from_conjugate_space_0[simp]: \<open>from_conjugate_space 0 = 0\<close>
  using zero_conjugate_space.rep_eq by blast

lemma antilinear_eq_0_on_span:
  assumes \<open>antilinear f\<close>
    and \<open>\<And>x. x \<in> b \<Longrightarrow> f x = 0\<close>
    and \<open>x \<in> cspan b\<close>
  shows \<open>f x = 0\<close>
proof -
  from assms(1)
  have \<open>clinear (\<lambda>x. to_conjugate_space (f x))\<close>
    apply (rule antilinear_o_antilinear[unfolded o_def])
    by simp
  then have \<open>to_conjugate_space (f x) = 0\<close>
    apply (rule complex_vector.linear_eq_0_on_span)
    using assms by auto
  then have \<open>from_conjugate_space (to_conjugate_space (f x)) = 0\<close>
    by simp
  then show ?thesis
    by (simp add: to_conjugate_space_inverse)
qed

lemma antilinear_diff:
  assumes \<open>antilinear f\<close> and \<open>antilinear g\<close>
  shows \<open>antilinear (\<lambda>x. f x - g x)\<close>
  apply (rule antilinearI)
   apply (metis add_diff_add additive.add antilinear_def assms(1,2))
  by (simp add: antilinear.scaleC assms(1,2) scaleC_right.diff)

lemma antilinear_cinner:
  shows \<open>antilinear (\<lambda>x. x \<bullet>\<^sub>C y)\<close>
  by (simp add: antilinearI cinner_add_left)


lemma cinner_extensionality_basis:
  fixes g h :: \<open>'a::complex_inner\<close>
  assumes \<open>ccspan B = \<top>\<close>
  assumes \<open>\<And>x. x \<in> B \<Longrightarrow> x \<bullet>\<^sub>C g = x \<bullet>\<^sub>C h\<close>
  shows \<open>g = h\<close>
proof (rule cinner_extensionality)
  fix y :: 'a
  have \<open>y \<in> closure (cspan B)\<close>
    using assms(1) ccspan.rep_eq by fastforce
  then obtain x where \<open>x \<longlonglongrightarrow> y\<close> and xB: \<open>x i \<in> cspan B\<close> for i
    using closure_sequential by blast
  have lin: \<open>antilinear (\<lambda>a. a \<bullet>\<^sub>C g - a \<bullet>\<^sub>C h)\<close>
    by (intro antilinear_diff antilinear_cinner)
  from lin have \<open>x i \<bullet>\<^sub>C g - x i \<bullet>\<^sub>C h = 0\<close> for i
    apply (rule antilinear_eq_0_on_span[of _ B])
    using xB assms by auto
  then have \<open>(\<lambda>i. x i \<bullet>\<^sub>C g - x i \<bullet>\<^sub>C h) \<longlonglongrightarrow> 0\<close> for i
    by simp
  moreover have \<open>(\<lambda>i. x i \<bullet>\<^sub>C g - x i \<bullet>\<^sub>C h) \<longlonglongrightarrow> y \<bullet>\<^sub>C g - y \<bullet>\<^sub>C h\<close>
    apply (rule_tac continuous_imp_tendsto[unfolded o_def, OF _ \<open>x \<longlonglongrightarrow> y\<close>])
    by simp
  ultimately have \<open>y \<bullet>\<^sub>C g - y \<bullet>\<^sub>C h = 0\<close>
    using LIMSEQ_unique by blast
  then show \<open>y \<bullet>\<^sub>C g = y \<bullet>\<^sub>C h\<close>
    by simp
qed


lemma not_not_singleton_tc_zero:
  \<open>x = 0\<close> if \<open>\<not> class.not_singleton TYPE('a)\<close> for x :: \<open>('a::chilbert_space,'b::chilbert_space) trace_class\<close>
  apply transfer'
  using that by (rule not_not_singleton_cblinfun_zero)


lemma infsum_in_finite:
  assumes "finite F"
  assumes \<open>Hausdorff_space T\<close>
  assumes \<open>sum f F \<in> topspace T\<close>
  shows "infsum_in T f F = sum f F"
  using has_sum_in_finite[OF assms(1,3)]
  using assms(2) has_sum_in_infsum_in has_sum_in_unique summable_on_in_def by blast

lemma ccspan_finite_rank_tc[simp]: \<open>ccspan (Collect finite_rank_tc) = \<top>\<close>
  apply transfer'
  apply (rule order_top_class.top_le)
  by (metis complex_vector.span_eq_iff csubspace_finite_rank_tc finite_rank_tc_dense order.refl)


lemma ccspan_rank1_tc[simp]: \<open>ccspan (Collect rank1_tc) = \<top>\<close>
  by (smt (verit, ccfv_SIG) basic_trans_rules(31) ccspan.rep_eq ccspan_finite_rank_tc ccspan_leqI ccspan_mono closure_subset
      complex_vector.span_superset cspan_eqI finite_rank_tc_def' mem_Collect_eq order_trans_rules(24))


interpretation compose_tcr: bounded_cbilinear compose_tcr
proof (intro bounded_cbilinear.intro exI[of _ 1] allI)
  fix a a' :: \<open>'a \<Rightarrow>\<^sub>C\<^sub>L 'b\<close> and b b' :: \<open>('c,'a) trace_class\<close> and r :: complex
  show \<open>compose_tcr (a + a') b = compose_tcr a b + compose_tcr a' b\<close>
    apply transfer
    by (simp add: cblinfun_compose_add_left)
  show \<open>compose_tcr a (b + b') = compose_tcr a b + compose_tcr a b'\<close>
    apply transfer
    by (simp add: cblinfun_compose_add_right)
  show \<open>compose_tcr (r *\<^sub>C a) b = r *\<^sub>C compose_tcr a b\<close>
    apply transfer
    by simp
  show \<open>compose_tcr a (r *\<^sub>C b) = r *\<^sub>C compose_tcr a b\<close>
    apply transfer
    by simp
  show \<open>norm (compose_tcr a b) \<le> norm a * norm b * 1\<close>
    by (simp add: norm_compose_tcr)
qed

declare compose_tcr.bounded_cbilinear_axioms[bounded_cbilinear]

lemma sandwich_butterfly: \<open>sandwich a (butterfly x y) = butterfly (a x) (a y)\<close>
  by (simp add: sandwich_apply butterfly_comp_cblinfun cblinfun_comp_butterfly)

lemma sandwich_tc_eq0_D:
  assumes eq0: \<open>\<And>\<rho>. \<rho> \<ge> 0 \<Longrightarrow> norm \<rho> \<le> B \<Longrightarrow> sandwich_tc a \<rho> = 0\<close>
  assumes Bpos: \<open>B > 0\<close>
  shows \<open>a = 0\<close>
proof (rule ccontr)
  assume \<open>a \<noteq> 0\<close>
  obtain h where \<open>a h \<noteq> 0\<close>
  proof (atomize_elim, rule ccontr)
    assume \<open>\<nexists>h. a *\<^sub>V h \<noteq> 0\<close>
    then have \<open>a h = 0\<close> for h
      by blast
    then have \<open>a = 0\<close>
      by (auto intro!: cblinfun_eqI)
    with \<open>a \<noteq> 0\<close>
    show False
      by simp
  qed
  then have \<open>h \<noteq> 0\<close>
    by force

  define k where \<open>k = sqrt B *\<^sub>R sgn h\<close>
  from \<open>a h \<noteq> 0\<close> Bpos have \<open>a k \<noteq> 0\<close>
    by (smt (verit, best) cblinfun.scaleR_right k_def linordered_field_class.inverse_positive_iff_positive real_sqrt_gt_zero scaleR_simps(7) sgn_div_norm zero_less_norm_iff)
  have \<open>norm (from_trace_class (sandwich_tc a (tc_butterfly k k))) = norm (butterfly (a k) (a k))\<close>
    by (simp add: from_trace_class_sandwich_tc tc_butterfly.rep_eq sandwich_butterfly)
  also have \<open>\<dots> = (norm (a k))\<^sup>2\<close>
    by (simp add: norm_butterfly power2_eq_square)
  also from \<open>a k \<noteq> 0\<close>
  have \<open>\<dots> \<noteq> 0\<close>
    by simp
  finally have sand_neq0: \<open>sandwich_tc a (tc_butterfly k k) \<noteq> 0\<close>
    by fastforce

  have \<open>norm (tc_butterfly k k) = B\<close>
    using \<open>h \<noteq> 0\<close> Bpos
    by (simp add: norm_tc_butterfly k_def norm_sgn)
  with sand_neq0 assms
  show False
    by simp
qed

lemma is_Proj_leq_id: \<open>is_Proj P \<Longrightarrow> P \<le> id_cblinfun\<close>
  by (metis diff_ge_0_iff_ge is_Proj_algebraic is_Proj_complement positive_cblinfun_squareI)

lemma sum_butterfly_leq_id: 
  assumes \<open>is_ortho_set E\<close>
  assumes \<open>\<And>e. e\<in>E \<Longrightarrow> norm e = 1\<close>
  shows \<open>(\<Sum>i\<in>E. butterfly i i) \<le> id_cblinfun\<close>
proof -
  have \<open>is_Proj (\<Sum>\<psi>\<in>E. butterfly \<psi> \<psi>)\<close>
    using assms by (rule sum_butterfly_is_Proj)
  then show ?thesis
    by (auto intro!: is_Proj_leq_id)
qed


lemma eq_from_separatingI2x:
  \<comment> \<open>When using this as a rule, best instantiate \<^term>\<open>x\<close> explicitly.\<close>
  assumes \<open>separating_set P ((\<lambda>(x,y). h x y) ` (S\<times>T))\<close>
  assumes \<open>P f\<close> and \<open>P g\<close>
  assumes \<open>\<And>x y. x \<in> S \<Longrightarrow> y \<in> T \<Longrightarrow> f (h x y) = g (h x y)\<close>
  shows \<open>f x = g x\<close>
  using assms eq_from_separatingI2 by blast

lemma sandwich_tc_butterfly: \<open>sandwich_tc c (tc_butterfly a b) = tc_butterfly (c a) (c b)\<close>
  by (metis from_trace_class_inverse from_trace_class_sandwich_tc sandwich_butterfly tc_butterfly.rep_eq)

lemma tc_butterfly_0_left[simp]: \<open>tc_butterfly 0 t = 0\<close>
  by (metis mult_eq_0_iff norm_eq_zero norm_tc_butterfly)

lemma tc_butterfly_0_right[simp]: \<open>tc_butterfly t 0 = 0\<close>
  by (metis mult_eq_0_iff norm_eq_zero norm_tc_butterfly)



end
