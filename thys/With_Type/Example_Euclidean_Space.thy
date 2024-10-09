section \<open>\<open>Example_Euclidean_Space\<close> -- Example: compactness of the sphere\<close>

theory Example_Euclidean_Space
  imports With_Type "HOL-Analysis.Euclidean_Space" "HOL-Analysis.Topology_Euclidean_Space"
begin

subsection \<open>Setting up type class \<^class>\<open>finite\<close> for \<^const>\<open>with_type\<close>\<close>

definition \<open>WITH_TYPE_CLASS_finite S u \<longleftrightarrow> finite S\<close>
  for S :: \<open>'rep set\<close> and u :: unit
definition \<open>WITH_TYPE_REL_finite r = (rel_unit_itself :: _ \<Rightarrow> 'abs itself \<Rightarrow> _)\<close>
  for r :: \<open>'rep \<Rightarrow> 'abs \<Rightarrow> bool\<close>

lemma [with_type_intros]: \<open>finite S \<Longrightarrow> WITH_TYPE_CLASS_finite S x\<close>
  using WITH_TYPE_CLASS_finite_def by blast

lemma with_type_wellformed_finite[with_type_intros]:
  \<open>with_type_wellformed WITH_TYPE_CLASS_finite S WITH_TYPE_REL_finite\<close>
  by (simp add: with_type_wellformed_def WITH_TYPE_REL_finite_def)

lemma with_type_transfer_finite:
  includes lifting_syntax
  fixes r :: \<open>'rep \<Rightarrow> 'abs \<Rightarrow> bool\<close>
  assumes [transfer_rule]: \<open>bi_unique r\<close> \<open>right_total r\<close>
  shows \<open>(WITH_TYPE_REL_finite r ===> (\<longleftrightarrow>))
         (WITH_TYPE_CLASS_finite (Collect (Domainp r))) class.finite\<close>
  unfolding WITH_TYPE_REL_finite_def
proof (rule rel_funI)
  fix x :: unit and y :: \<open>'abs itself\<close>
  assume \<open>rel_unit_itself x y\<close>
  then have [simp]: \<open>y = TYPE('abs)\<close>
    by simp
  note right_total_UNIV_transfer[transfer_rule]
  show \<open>WITH_TYPE_CLASS_finite (Collect (Domainp r)) x \<longleftrightarrow> class.finite y\<close>
    apply (simp add: WITH_TYPE_CLASS_finite_def class.finite_def)
    apply transfer
    by simp
qed

setup \<open>
With_Type.add_with_type_info_global {
  class = \<^class>\<open>finite\<close>,
  param_names = [],
  rep_class = \<^const_name>\<open>WITH_TYPE_CLASS_finite\<close>,
  rep_rel = \<^const_name>\<open>WITH_TYPE_REL_finite\<close>,
  with_type_wellformed = @{thm with_type_wellformed_finite},
  transfer = SOME @{thm with_type_transfer_finite},
  rep_rel_itself = SOME @{lemma \<open>bi_unique r \<Longrightarrow> right_total r \<Longrightarrow> (WITH_TYPE_REL_finite r) p TYPE('abs2)\<close>
      by (simp add: WITH_TYPE_REL_finite_def rel_unit_itself.simps Transfer.Rel_def)}
}
\<close>

subsection \<open>Vector space over a given basis\<close>

text \<open>\<open>'a vs_over\<close> is defined to be the vector space with an orthonormal basis enumerated by
  elements of \<^typ>\<open>'a\<close>, in other words $\mathbb R^\mathtt{'a}$. We require \<^typ>\<open>'a\<close> to be finite.\<close>
typedef 'a vs_over = \<open>UNIV :: ('a::finite\<Rightarrow>real) set\<close>
  by (rule exI[of _ \<open>\<lambda>_. 0\<close>], auto)
setup_lifting type_definition_vs_over


instantiation vs_over :: (finite) real_vector begin
lift_definition plus_vs_over :: \<open>'a vs_over \<Rightarrow> 'a vs_over \<Rightarrow> 'a vs_over\<close> is \<open>\<lambda>x y a. x a + y a\<close>.
lift_definition minus_vs_over :: \<open>'a vs_over \<Rightarrow> 'a vs_over \<Rightarrow> 'a vs_over\<close> is \<open>\<lambda>x y a. x a - y a\<close>.
lift_definition uminus_vs_over :: \<open>'a vs_over \<Rightarrow> 'a vs_over\<close> is \<open>\<lambda>x a. - x a\<close>.
lift_definition zero_vs_over :: \<open>'a vs_over\<close> is \<open>\<lambda>_. 0\<close>.
lift_definition scaleR_vs_over :: \<open>real \<Rightarrow> 'a vs_over \<Rightarrow> 'a vs_over\<close> is \<open>\<lambda>r x a. r * x a\<close>.
instance
  apply (intro_classes; transfer)
  by (auto intro!: ext simp: distrib_right distrib_left)
end

instantiation vs_over :: (finite) real_normed_vector begin
lift_definition norm_vs_over :: \<open>'a vs_over \<Rightarrow> real\<close> is \<open>\<lambda>x. L2_set x UNIV\<close>.
definition dist_vs_over :: \<open>'a vs_over \<Rightarrow> 'a vs_over \<Rightarrow> real\<close> where \<open>dist_vs_over x y = norm (x - y)\<close>
definition uniformity_vs_over :: \<open>('a vs_over \<times> 'a vs_over) filter\<close> where \<open>uniformity_vs_over = (INF e\<in>{0<..}. principal {(x, y). dist x y < e})\<close>
definition sgn_vs_over :: \<open>'a vs_over \<Rightarrow> 'a vs_over\<close> where \<open>sgn_vs_over x = x /\<^sub>R norm x\<close>
definition open_vs_over :: \<open>'a vs_over set \<Rightarrow> bool\<close> where \<open>open_vs_over U = (\<forall>x\<in>U. \<forall>\<^sub>F (x', y) in uniformity. x' = x \<longrightarrow> y \<in> U)\<close>
instance
proof intro_classes
  fix x y :: \<open>'a vs_over\<close>
  show \<open>dist x y = norm (x - y)\<close>
  using dist_vs_over_def by presburger
  show \<open>sgn x = x /\<^sub>R norm x\<close>
  using sgn_vs_over_def by blast
  show \<open>(uniformity :: ('a vs_over \<times> 'a vs_over) filter) = (INF e\<in>{0<..}. principal {(x, y). dist x y < e})\<close>
  using uniformity_vs_over_def by blast
  show \<open>(norm x = 0) = (x = 0)\<close>
    apply transfer
    by (auto simp: L2_set_eq_0_iff)
  show \<open>norm (x + y) \<le> norm x + norm y\<close>
    apply transfer
    by (rule L2_set_triangle_ineq)
  show \<open>norm (a *\<^sub>R x) = \<bar>a\<bar> * norm x\<close> for a
    apply transfer
    by (simp add: L2_set_def power_mult_distrib real_sqrt_mult flip: sum_distrib_left)
  show \<open>open U = (\<forall>x\<in>U. \<forall>\<^sub>F (x', y) in uniformity. x' = x \<longrightarrow> y \<in> U)\<close> for U :: \<open>'a vs_over set\<close>
    by (simp add: open_vs_over_def)
qed
end

instantiation vs_over :: (finite) real_inner begin
lift_definition inner_vs_over :: \<open>'a vs_over \<Rightarrow> 'a vs_over \<Rightarrow> real\<close> is \<open>\<lambda>x y. \<Sum>a\<in>UNIV. x a * y a\<close>.
instance
  apply (intro_classes; transfer)
  by (auto intro!: sum_nonneg sum.cong simp: mult.commute sum_nonneg_eq_0_iff L2_set_def
      power2_eq_square sum_distrib_left mult_ac distrib_left simp flip: sum.distrib)
end

instantiation vs_over :: (finite) euclidean_space begin
text \<open>Returns the basis vector corresponding to \<^typ>\<open>'a\<close>.\<close>
lift_definition basis_vec :: \<open>'a \<Rightarrow> 'a vs_over\<close> is \<open>\<lambda>a::'a. indicator {a}\<close>.
definition Basis_vs_over :: \<open>'a vs_over set\<close> where \<open>Basis = range basis_vec\<close>
instance
  apply (intro_classes; unfold Basis_vs_over_def; transfer)
  by (auto intro!: simp: indicator_def)
end


subsection \<open>Compactness of the sphere.\<close>

text \<open>@{thm compact_sphere} shows that a sphere in an Euclidean vector space
  (type class \<^class>\<open>euclidean_space\<close>) is compact. We wish to transfer this result to
  any space with a finite orthonormal basis. Mathematically, this is the same statement,
  but the conversion between a statement based on type classes and one based on predicates
  about bases is non-trivial in Isabelle.\<close>

lemma compact_sphere_onb:
  fixes B :: \<open>'a::real_inner set\<close>
  assumes \<open>finite B\<close> and \<open>span B = UNIV\<close> and onb: \<open>\<forall>b\<in>B. \<forall>c\<in>B. inner b c = of_bool (b=c)\<close>
  shows \<open>compact (sphere (0::'a) r)\<close>
proof (cases \<open>B = {}\<close>)
  case True
  with assms have all_0: \<open>(x :: 'a) = 0\<close> for x
    by auto
  then have \<open>sphere (0::'a) r = {0} \<or> sphere (0::'a) r = {}\<close>
    by (auto simp add: sphere_def)
  then show ?thesis
    by fastforce
next
  case False
  have \<open>let 't::finite = B in compact (sphere (0::'t vs_over) r)\<close>
  proof with_type_intro
    from False show \<open>B \<noteq> {}\<close> by -
    from assms show \<open>finite B\<close> by -
    fix rep :: \<open>'t \<Rightarrow> _\<close>
    assume \<open>bij_betw rep UNIV B\<close>
    from compact_sphere[where 'a=\<open>'t vs_over\<close>]
    show \<open>compact (sphere (0::'t vs_over) r)\<close>
      by simp
  qed
  then have \<open>let 't::finite = B in compact (sphere (0::'a) r)\<close>
  proof with_type_mp
    with_type_case

    define f :: \<open>'t vs_over \<Rightarrow> 'a\<close> where \<open>f x = (\<Sum>t\<in>UNIV. Rep_vs_over x t *\<^sub>R rep_t t)\<close> for x
    have \<open>linear f\<close>
      by (auto intro!: linearI sum.distrib simp: f_def plus_vs_over.rep_eq scaleR_vs_over.rep_eq
          scaleR_add_left scaleR_right.sum simp flip: scaleR_scaleR)
    then have \<open>continuous_on X f\<close> for X
      using linear_continuous_on linear_linear by blast
    moreover from with_type_mp.premise have \<open>compact (sphere (0::'t vs_over) r)\<close>
      by -
    ultimately have compact_fsphere: \<open>compact (f ` sphere 0 r)\<close>
      using compact_continuous_image by blast
    have \<open>surj f\<close>
    proof (unfold surj_def, rule allI)
      fix y :: 'a
      from assms have \<open>y \<in> span B\<close>
        by auto
      then show \<open>\<exists>x. y = f x\<close>
      proof (induction rule: span_induct_alt)
        case base
        then show ?case
          by (auto intro!: exI[of _ 0] simp: f_def zero_vs_over.rep_eq)
      next
        case (step c b y)
        from step.IH
        obtain x where yfx: \<open>y = f x\<close>
          by auto
        have \<open>b = f (basis_vec (inv rep_t b))\<close>
          by (simp add: f_def basis_vec.rep_eq step.hyps type_definition_t.Abs_inverse)
        then have \<open>c *\<^sub>R b + y = f (c *\<^sub>R basis_vec (inv rep_t b) + x)\<close>
          using \<open>linear f\<close>
          by (simp add: linear_add linear_scale yfx)
        then show ?case
          by auto
      qed
    qed
    have \<open>norm (f x) = norm x\<close> for x
    proof -
      have aux1: \<open>(a, b) \<notin> range (\<lambda>t. (t, t)) \<Longrightarrow> rep_t a \<bullet> rep_t b \<noteq> 0 \<Longrightarrow> Rep_vs_over x b = 0\<close> for a b
        by (metis (mono_tags, lifting) of_bool_eq(1) onb range_eqI type_definition_t.Rep type_definition_t.Rep_inverse)
      have rep_inner: \<open>inner (rep_t t) (rep_t u) = of_bool (t=u)\<close> for t u
        by (simp add: onb type_definition_t.Rep type_definition_t.Rep_inject)
      have \<open>(norm (f x))\<^sup>2 = inner (f x) (f x)\<close>
        by (simp add: dot_square_norm)
      also have \<open>\<dots> = (\<Sum>(t,t')\<in>UNIV. (Rep_vs_over x t * Rep_vs_over x t') * inner (rep_t t) (rep_t t'))\<close>
        by (auto intro!: simp: f_def inner_sum_right inner_sum_left sum_distrib_left sum.cartesian_product
            case_prod_beta inner_commute mult_ac)
      also have \<open>\<dots> = (\<Sum>(t,t')\<in>(\<lambda>t. (t,t))`UNIV. (Rep_vs_over x t * Rep_vs_over x t') * inner (rep_t t) (rep_t t'))\<close>
        by (auto intro!: sum.mono_neutral_cong_right simp: aux1)
      also have \<open>\<dots> = (\<Sum>t\<in>UNIV. (Rep_vs_over x t)\<^sup>2)\<close>
        apply (subst sum.reindex)
        by (auto intro!: injI simp: rep_inner power2_eq_square)
      also have \<open>\<dots> = (norm x)\<^sup>2\<close>
        by (simp add: norm_vs_over_def L2_set_def sum_nonneg)
      finally show ?thesis
        by simp
    qed
    then have \<open>f ` sphere 0 r = sphere 0 r\<close>
      using \<open>surj f\<close>
      by (fastforce simp: sphere_def)
    with compact_fsphere
    show \<open>compact (sphere (0::'a) r)\<close>
      by simp
  qed
  from this[cancel_with_type]
  show \<open>compact (sphere (0::'a) r)\<close>
    by -
qed

end
