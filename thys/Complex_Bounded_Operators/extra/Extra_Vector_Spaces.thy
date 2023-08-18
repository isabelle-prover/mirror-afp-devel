section \<open>\<open>Extra_Vector_Spaces\<close> -- Additional facts about vector spaces\<close>

theory Extra_Vector_Spaces
  imports
    "HOL-Analysis.Inner_Product"
    "HOL-Analysis.Euclidean_Space"
    "HOL-Library.Indicator_Function"
    "HOL-Analysis.Topology_Euclidean_Space"
    "HOL-Analysis.Line_Segment"
    "HOL-Analysis.Bounded_Linear_Function"
    Extra_General
begin

subsection \<open>Euclidean spaces\<close>

typedef 'a euclidean_space = "UNIV :: ('a \<Rightarrow> real) set" ..
setup_lifting type_definition_euclidean_space

instantiation euclidean_space :: (type) real_vector begin
lift_definition plus_euclidean_space ::
  "'a euclidean_space \<Rightarrow> 'a euclidean_space \<Rightarrow> 'a euclidean_space"
  is "\<lambda>f g x. f x + g x" .
lift_definition zero_euclidean_space :: "'a euclidean_space" is "\<lambda>_. 0" .
lift_definition uminus_euclidean_space :: 
  "'a euclidean_space \<Rightarrow> 'a euclidean_space" 
  is "\<lambda>f x. - f x" .
lift_definition minus_euclidean_space :: 
  "'a euclidean_space \<Rightarrow> 'a euclidean_space \<Rightarrow> 'a euclidean_space" 
  is "\<lambda>f g x. f x - g x".
lift_definition scaleR_euclidean_space :: 
  "real \<Rightarrow> 'a euclidean_space \<Rightarrow> 'a euclidean_space" 
  is "\<lambda>c f x. c * f x" .
instance
  apply intro_classes
  by (transfer; auto intro: distrib_left distrib_right)+
end

instantiation euclidean_space :: (finite) real_inner begin
lift_definition inner_euclidean_space :: "'a euclidean_space \<Rightarrow> 'a euclidean_space \<Rightarrow> real"
  is "\<lambda>f g. \<Sum>x\<in>UNIV. f x * g x :: real" .
definition "norm_euclidean_space (x::'a euclidean_space) = sqrt (inner x x)"
definition "dist_euclidean_space (x::'a euclidean_space) y = norm (x-y)"
definition "sgn x = x /\<^sub>R norm x" for x::"'a euclidean_space"
definition "uniformity = (INF e\<in>{0<..}. principal {(x::'a euclidean_space, y). dist x y < e})"
definition "open U = (\<forall>x\<in>U. \<forall>\<^sub>F (x'::'a euclidean_space, y) in uniformity. x' = x \<longrightarrow> y \<in> U)"
instance
proof intro_classes
  fix x :: "'a euclidean_space"
    and y :: "'a euclidean_space"
    and z :: "'a euclidean_space"
  show "dist (x::'a euclidean_space) y = norm (x - y)"
    and "sgn (x::'a euclidean_space) = x /\<^sub>R norm x"
    and "uniformity = (INF e\<in>{0<..}. principal {(x, y). dist (x::'a euclidean_space) y < e})"
    and "open U = (\<forall>x\<in>U. \<forall>\<^sub>F (x', y) in uniformity. (x'::'a euclidean_space) = x \<longrightarrow> y \<in> U)"
    and "norm x = sqrt (inner x x)" for U
    unfolding dist_euclidean_space_def norm_euclidean_space_def sgn_euclidean_space_def
      uniformity_euclidean_space_def open_euclidean_space_def
    by simp_all

  show "inner x y = inner y x"
    apply transfer
    by (simp add: mult.commute)
  show "inner (x + y) z = inner x z + inner y z"
  proof transfer
    fix x y z::"'a \<Rightarrow> real"
    have "(\<Sum>i\<in>UNIV. (x i + y i) * z i) = (\<Sum>i\<in>UNIV. x i * z i + y i * z i)"
      by (simp add: distrib_left mult.commute)
    thus "(\<Sum>i\<in>UNIV. (x i + y i) * z i) = (\<Sum>j\<in>UNIV. x j * z j) + (\<Sum>k\<in>UNIV. y k * z k)"
      by (subst sum.distrib[symmetric])      
  qed

  show "inner (r *\<^sub>R x) y = r * (inner x y)" for r
  proof transfer
    fix r and x y::"'a\<Rightarrow>real"
    have "(\<Sum>i\<in>UNIV. r * x i * y i) = (\<Sum>i\<in>UNIV. r * (x i * y i))"
      by (simp add: mult.assoc)
    thus "(\<Sum>i\<in>UNIV. r * x i * y i) = r * (\<Sum>j\<in>UNIV. x j * y j)"
      by (subst sum_distrib_left)
  qed
  show "0 \<le> inner x x"
    apply transfer
    by (simp add: sum_nonneg)
  show "(inner x x = 0) = (x = 0)"
  proof (transfer, rule)
    fix f :: "'a \<Rightarrow> real"
    assume "(\<Sum>i\<in>UNIV. f i * f i) = 0"
    hence "f x * f x = 0" for x
      apply (rule_tac sum_nonneg_eq_0_iff[THEN iffD1, rule_format, where A=UNIV and x=x])
      by auto
    thus "f = (\<lambda>_. 0)"
      by auto
  qed auto
qed
end

instantiation euclidean_space :: (finite) euclidean_space begin
lift_definition euclidean_space_basis_vector :: "'a \<Rightarrow> 'a euclidean_space" is
  "\<lambda>x. indicator {x}" .
definition "Basis_euclidean_space == (euclidean_space_basis_vector ` UNIV)"
instance
proof intro_classes
  fix u :: "'a euclidean_space"
    and v :: "'a euclidean_space"
  show "(Basis::'a euclidean_space set) \<noteq> {}"
    unfolding Basis_euclidean_space_def by simp
  show "finite (Basis::'a euclidean_space set)"
    unfolding Basis_euclidean_space_def by simp
  show "inner u v = (if u = v then 1 else 0)"
    if "u \<in> Basis" and "v \<in> Basis"
    using that unfolding Basis_euclidean_space_def
    apply transfer apply auto
    by (auto simp: indicator_def)
  show "(\<forall>v\<in>Basis. inner u v = 0) = (u = 0)"
    unfolding Basis_euclidean_space_def
    apply transfer
    by auto
qed
end (* euclidean_space :: (finite) euclidean_space *)

subsection \<open>Misc\<close>

lemma closure_bounded_linear_image_subset_eq:
  assumes f: "bounded_linear f"
  shows "closure (f ` closure S) = closure (f ` S)"
  by (meson closed_closure closure_bounded_linear_image_subset closure_minimal closure_mono closure_subset f image_mono subset_antisym)

lemma not_singleton_real_normed_is_perfect_space[simp]: \<open>class.perfect_space (open :: 'a::{not_singleton,real_normed_vector} set \<Rightarrow> bool)\<close>
  apply standard
  by (metis UNIV_not_singleton clopen closed_singleton empty_not_insert)

lemma infsum_bounded_linear:
  assumes \<open>bounded_linear f\<close>
  assumes \<open>g summable_on S\<close>
  shows \<open>infsum (f \<circ> g) S = f (infsum g S)\<close>
  apply (rule infsum_comm_additive)
  using assms blinfun_apply_induct blinfun.additive_right
  by (auto simp: linear_continuous_within)

lemma has_sum_bounded_linear: 
  assumes \<open>bounded_linear f\<close>
  assumes \<open>(g has_sum x) S\<close>
  shows \<open>((f o g) has_sum (f x)) S\<close>
  apply (rule has_sum_comm_additive)
  using assms blinfun_apply_induct blinfun.additive_right apply auto
  using isCont_def linear_continuous_at by fastforce

lemma abs_summable_on_bounded_linear:
  assumes \<open>bounded_linear f\<close>
  assumes \<open>g abs_summable_on S\<close>
  shows \<open>(f o g) abs_summable_on S\<close>
proof -
  have bound: \<open>norm (f (g x)) \<le> onorm f * norm (g x)\<close> for x
    apply (rule onorm)
    by (simp add: assms(1))

  from assms(2) have \<open>(\<lambda>x. onorm f *\<^sub>R g x) abs_summable_on S\<close>
    by (auto intro!: summable_on_cmult_right)
  then have \<open>(\<lambda>x. f (g x)) abs_summable_on S\<close>
    apply (rule abs_summable_on_comparison_test)
    using bound by (auto simp: assms(1) onorm_pos_le)
  then show ?thesis
    by auto
qed

lemma norm_plus_leq_norm_prod: \<open>norm (a + b) \<le> sqrt 2 * norm (a, b)\<close>
proof -
  have \<open>(norm (a + b))\<^sup>2 \<le> (norm a + norm b)\<^sup>2\<close>
    using norm_triangle_ineq by auto
  also have \<open>\<dots> \<le> 2 * ((norm a)\<^sup>2 + (norm b)\<^sup>2)\<close>
    by (smt (verit, best) power2_sum sum_squares_bound)
  also have \<open>\<dots> \<le> (sqrt 2 * norm (a, b))\<^sup>2\<close>
    by (auto simp: power_mult_distrib norm_prod_def simp del: power_mono_iff)
  finally show ?thesis
    by auto
qed

lemma ex_norm1:
  assumes \<open>(UNIV::'a::real_normed_vector set) \<noteq> {0}\<close>
  shows \<open>\<exists>x::'a. norm x = 1\<close>
proof-
  have \<open>\<exists>x::'a. x \<noteq> 0\<close>
    using assms by fastforce
  then obtain x::'a where \<open>x \<noteq> 0\<close>
    by blast
  hence \<open>norm x \<noteq> 0\<close>
    by simp
  hence \<open>(norm x) / (norm x) = 1\<close>
    by simp
  moreover have \<open>(norm x) / (norm x) = norm (x /\<^sub>R (norm x))\<close>
    by simp
  ultimately have \<open>norm (x /\<^sub>R (norm x)) = 1\<close>
    by simp
  thus ?thesis
    by blast
qed

lemma bdd_above_norm_f:
  assumes "bounded_linear f"
  shows \<open>bdd_above {norm (f x) |x. norm x = 1}\<close>
proof-
  have \<open>\<exists>M. \<forall>x. norm x = 1 \<longrightarrow> norm (f x) \<le> M\<close>
    using assms
    by (metis bounded_linear.axioms(2) bounded_linear_axioms_def)
  thus ?thesis by auto
qed

lemma any_norm_exists:
  assumes \<open>n \<ge> 0\<close>
  shows \<open>\<exists>\<psi>::'a::{real_normed_vector,not_singleton}. norm \<psi> = n\<close>
proof -
  obtain \<psi> :: 'a where \<open>\<psi> \<noteq> 0\<close>
    using not_singleton_card
    by force
  then have \<open>norm (n *\<^sub>R sgn \<psi>) = n\<close>
    using assms by (auto simp: sgn_div_norm abs_mult)
  then show ?thesis
    by blast
qed


lemma abs_summable_on_scaleR_left [intro]:
  fixes c :: \<open>'a :: real_normed_vector\<close>
  assumes "c \<noteq> 0 \<Longrightarrow> f abs_summable_on A"
  shows   "(\<lambda>x. f x *\<^sub>R c) abs_summable_on A"
  apply (cases \<open>c = 0\<close>)
   apply simp
  by (auto intro!: summable_on_cmult_left assms simp flip: real_norm_def)

lemma abs_summable_on_scaleR_right [intro]:
  fixes f :: \<open>'a \<Rightarrow> 'b :: real_normed_vector\<close>
  assumes "c \<noteq> 0 \<Longrightarrow> f abs_summable_on A"
  shows   "(\<lambda>x. c *\<^sub>R f x) abs_summable_on A"
  apply (cases \<open>c = 0\<close>)
   apply simp
  by (auto intro!: summable_on_cmult_right assms)



end
