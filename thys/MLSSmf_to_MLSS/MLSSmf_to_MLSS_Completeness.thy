theory MLSSmf_to_MLSS_Completeness
  imports MLSSmf_Semantics MLSSmf_to_MLSS MLSSmf_HF_Extras
          Proper_Venn_Regions Reduced_MLSS_Formula_Singleton_Model_Property
begin

locale MLSSmf_to_MLSS_complete =
  normalized_MLSSmf_clause \<C> for \<C> :: "('v, 'f) MLSSmf_clause" +
    fixes \<B> :: "('v, 'f) Composite \<Rightarrow> hf"
  assumes \<B>: "is_model_for_reduced_dnf \<B>"

    fixes \<Lambda> :: "hf \<Rightarrow> 'v set set"
  assumes \<Lambda>_subset_V: "\<Lambda> x \<subseteq> P\<^sup>+ V"
      and \<Lambda>_preserves_zero: "\<Lambda> 0 = {}"
      and \<Lambda>_inc: "a \<le> b \<Longrightarrow> \<Lambda> a \<subseteq> \<Lambda> b"
      and \<Lambda>_add: "\<Lambda> (a \<squnion> b) = \<Lambda> a \<union> \<Lambda> b"
      and \<Lambda>_mul: "\<Lambda> (a \<sqinter> b) = \<Lambda> a \<inter> \<Lambda> b"
      and \<Lambda>_discr: "l \<subseteq> P\<^sup>+ V \<Longrightarrow>
                    a = \<Squnion>HF ((\<B> \<circ> VennRegion) ` l) \<Longrightarrow> a = \<Squnion>HF ((\<B> \<circ> VennRegion) ` (\<Lambda> a))"
begin

fun discretize\<^sub>v :: "(('v, 'f) Composite \<Rightarrow> hf) \<Rightarrow> ('v \<Rightarrow> hf)" where
  "discretize\<^sub>v \<M> = \<M> \<circ> Solo"

fun discretize\<^sub>f :: "(('v, 'f) Composite \<Rightarrow> hf) \<Rightarrow> ('f \<Rightarrow> hf \<Rightarrow> hf)" where
  "discretize\<^sub>f \<M> = (\<lambda>f a. \<M> w\<^bsub>f\<^esub>\<^bsub>\<Lambda> a\<^esub>)"

interpretation proper_Venn_regions V "discretize\<^sub>v \<B>"
  using finite_V by unfold_locales

lemma all_literal_sat: "\<forall>lt \<in> set \<C>. I\<^sub>l (discretize\<^sub>v \<B>) (discretize\<^sub>f \<B>) lt"
proof
  fix lt assume "lt \<in> set \<C>"

  from \<B> obtain clause where clause: "clause \<in> reduced_dnf"
                         and \<B>_sat_clause: "\<forall>lt \<in> clause. interp I\<^sub>s\<^sub>a \<B> lt"
    unfolding is_model_for_reduced_dnf_def by blast

  from \<open>lt \<in> set \<C>\<close> have "norm_literal lt"
    using norm_\<C> by blast
  then show "I\<^sub>l (discretize\<^sub>v \<B>) (discretize\<^sub>f \<B>) lt"
  proof (cases lt rule: norm_literal.cases)
    case (inc f)
    have "s \<le> t \<Longrightarrow> discretize\<^sub>f \<B> f s \<le> discretize\<^sub>f \<B> f t" for s t
    proof -
      let ?atom = "Var w\<^bsub>f\<^esub>\<^bsub>\<Lambda> t\<^esub> =\<^sub>s Var w\<^bsub>f\<^esub>\<^bsub>\<Lambda> t\<^esub> \<squnion>\<^sub>s Var w\<^bsub>f\<^esub>\<^bsub>\<Lambda> s\<^esub>"
      assume "s \<le> t"
      then have "\<Lambda> s \<subseteq> \<Lambda> t" using \<Lambda>_inc by simp
      then have "?atom \<in> reduce_atom (inc(f))"
        using \<Lambda>_subset_V
        by (simp add: V_def)
      then have "AT ?atom \<in> clause"
        using \<open>lt = AT\<^sub>m (inc(f))\<close> \<open>lt \<in> set \<C>\<close> clause
        unfolding reduced_dnf_def reduce_clause_def by fastforce
      with \<B>_sat_clause have "I\<^sub>s\<^sub>a \<B> ?atom" by fastforce
      then have "\<B> w\<^bsub>f\<^esub>\<^bsub>\<Lambda> t\<^esub> = \<B> w\<^bsub>f\<^esub>\<^bsub>\<Lambda> t\<^esub> \<squnion> \<B> w\<^bsub>f\<^esub>\<^bsub>\<Lambda> s\<^esub>" by simp
      then have "\<B> w\<^bsub>f\<^esub>\<^bsub>\<Lambda> s\<^esub> \<le> \<B> w\<^bsub>f\<^esub>\<^bsub>\<Lambda> t\<^esub>"
        by (simp add: sup.order_iff)
      then show "discretize\<^sub>f \<B> f s \<le> discretize\<^sub>f \<B> f t" by simp
    qed
    then show ?thesis using inc by auto

  next
    case (dec f)
    have "s \<le> t \<Longrightarrow> discretize\<^sub>f \<B> f t \<le> discretize\<^sub>f \<B> f s" for s t
    proof -
      let ?atom = "Var w\<^bsub>f\<^esub>\<^bsub>\<Lambda> s\<^esub> =\<^sub>s Var w\<^bsub>f\<^esub>\<^bsub>\<Lambda> s\<^esub> \<squnion>\<^sub>s Var w\<^bsub>f\<^esub>\<^bsub>\<Lambda> t\<^esub>"
      assume "s \<le> t"
      then have "\<Lambda> s \<subseteq> \<Lambda> t" using \<Lambda>_inc by simp
      then have "?atom \<in> reduce_atom (dec(f))"
        using \<Lambda>_subset_V
        by (simp add: V_def)
      then have "AT ?atom \<in> clause"
        using \<open>lt = AT\<^sub>m (dec(f))\<close> \<open>lt \<in> set \<C>\<close> clause
        unfolding reduced_dnf_def reduce_clause_def by fastforce
      with \<B>_sat_clause have "I\<^sub>s\<^sub>a \<B> ?atom" by fastforce
      then have "\<B> w\<^bsub>f\<^esub>\<^bsub>\<Lambda> s\<^esub> = \<B> w\<^bsub>f\<^esub>\<^bsub>\<Lambda> s\<^esub> \<squnion> \<B> w\<^bsub>f\<^esub>\<^bsub>\<Lambda> t\<^esub>" by simp
      then have "\<B> w\<^bsub>f\<^esub>\<^bsub>\<Lambda> t\<^esub> \<le> \<B> w\<^bsub>f\<^esub>\<^bsub>\<Lambda> s\<^esub>"
        by (simp add: sup.order_iff)
      then show "discretize\<^sub>f \<B> f t \<le> discretize\<^sub>f \<B> f s" by simp
    qed
    then show ?thesis using dec by auto

  next
    case (add f)
    have "discretize\<^sub>f \<B> f (s \<squnion> t) = discretize\<^sub>f \<B> f s \<squnion> discretize\<^sub>f \<B> f t" for s t
    proof -
      let ?atom = "Var w\<^bsub>f\<^esub>\<^bsub>\<Lambda> (s \<squnion> t)\<^esub> =\<^sub>s Var w\<^bsub>f\<^esub>\<^bsub>\<Lambda> s\<^esub> \<squnion>\<^sub>s Var w\<^bsub>f\<^esub>\<^bsub>\<Lambda> t\<^esub>"
      have "?atom \<in> reduce_atom (add(f))"
        using \<Lambda>_subset_V \<Lambda>_add 
        by (simp add: V_def)
      then have "AT ?atom \<in> clause"
        using \<open>lt = AT\<^sub>m (add(f))\<close> \<open>lt \<in> set \<C>\<close> clause
        unfolding reduced_dnf_def reduce_clause_def by fastforce
      with \<B>_sat_clause have "I\<^sub>s\<^sub>a \<B> ?atom" by fastforce
      then have "\<B> w\<^bsub>f\<^esub>\<^bsub>\<Lambda> (s \<squnion> t)\<^esub> = \<B> w\<^bsub>f\<^esub>\<^bsub>\<Lambda> s\<^esub> \<squnion> \<B> w\<^bsub>f\<^esub>\<^bsub>\<Lambda> t\<^esub>" by simp
      then show "discretize\<^sub>f \<B> f (s \<squnion> t) = discretize\<^sub>f \<B> f s \<squnion> discretize\<^sub>f \<B> f t" by simp
    qed
    then show ?thesis using add by auto

  next
    case (mul f)
    have "discretize\<^sub>f \<B> f (s \<sqinter> t) = discretize\<^sub>f \<B> f s \<sqinter> discretize\<^sub>f \<B> f t" for s t
    proof -
      let ?atom_1 = "Var (InterOfWAux f (\<Lambda> s) (\<Lambda> t)) =\<^sub>s Var w\<^bsub>f\<^esub>\<^bsub>\<Lambda> s\<^esub> -\<^sub>s Var w\<^bsub>f\<^esub>\<^bsub>\<Lambda> t\<^esub>"
      have "?atom_1 \<in> reduce_atom (mul(f))"
        using \<Lambda>_subset_V 
        by (simp add: V_def)
      then have "AT ?atom_1 \<in> clause"
        using \<open>lt = AT\<^sub>m (mul(f))\<close> \<open>lt \<in> set \<C>\<close> clause
        unfolding reduced_dnf_def reduce_clause_def by fastforce
      with \<B>_sat_clause have "I\<^sub>s\<^sub>a \<B> ?atom_1" by fastforce
      then have "\<B> (InterOfWAux f (\<Lambda> s) (\<Lambda> t)) = \<B> w\<^bsub>f\<^esub>\<^bsub>\<Lambda> s\<^esub> - \<B> w\<^bsub>f\<^esub>\<^bsub>\<Lambda> t\<^esub>" by simp
      moreover
      let ?atom_2 = "Var w\<^bsub>f\<^esub>\<^bsub>\<Lambda> (s \<sqinter> t)\<^esub> =\<^sub>s Var w\<^bsub>f\<^esub>\<^bsub>\<Lambda> s\<^esub> -\<^sub>s Var (InterOfWAux f (\<Lambda> s) (\<Lambda> t))"
      have "?atom_2 \<in> reduce_atom (mul(f))"
        using \<Lambda>_subset_V \<Lambda>_mul
        by (simp add: V_def)
      then have "AT ?atom_2 \<in> clause"
        using \<open>lt = AT\<^sub>m (mul(f))\<close> \<open>lt \<in> set \<C>\<close> clause
        unfolding reduced_dnf_def reduce_clause_def by fastforce
      with \<B>_sat_clause have "I\<^sub>s\<^sub>a \<B> ?atom_2" by fastforce
      then have "\<B> w\<^bsub>f\<^esub>\<^bsub>\<Lambda> (s \<sqinter> t)\<^esub> = \<B> w\<^bsub>f\<^esub>\<^bsub>\<Lambda> s\<^esub> - \<B> (InterOfWAux f (\<Lambda> s) (\<Lambda> t))" by simp
      ultimately
      have "\<B> w\<^bsub>f\<^esub>\<^bsub>\<Lambda> (s \<sqinter> t)\<^esub> = \<B> w\<^bsub>f\<^esub>\<^bsub>\<Lambda> s\<^esub> \<sqinter> \<B> w\<^bsub>f\<^esub>\<^bsub>\<Lambda> t\<^esub>" by auto
      then show "discretize\<^sub>f \<B> f (s \<sqinter> t) = discretize\<^sub>f \<B> f s \<sqinter> discretize\<^sub>f \<B> f t" by simp
    qed
    then show ?thesis using mul by auto

  next
    case (le f g)
    have "discretize\<^sub>f \<B> f s \<le> discretize\<^sub>f \<B> g s" for s
    proof -
      let ?atom = "Var w\<^bsub>g\<^esub>\<^bsub>\<Lambda> s\<^esub> =\<^sub>s Var w\<^bsub>g\<^esub>\<^bsub>\<Lambda> s\<^esub> \<squnion>\<^sub>s Var w\<^bsub>f\<^esub>\<^bsub>\<Lambda> s\<^esub>"
      have "?atom \<in> reduce_atom (f \<preceq>\<^sub>m g)"
        using \<Lambda>_subset_V 
        by (simp add: V_def)
      then have "AT ?atom \<in> clause"
        using \<open>lt = AT\<^sub>m (f \<preceq>\<^sub>m g)\<close> \<open>lt \<in> set \<C>\<close> clause
        unfolding reduced_dnf_def reduce_clause_def by fastforce
      with \<B>_sat_clause have "I\<^sub>s\<^sub>a \<B> ?atom" by fastforce
      then have "\<B> w\<^bsub>g\<^esub>\<^bsub>\<Lambda> s\<^esub> = \<B> w\<^bsub>g\<^esub>\<^bsub>\<Lambda> s\<^esub> \<squnion> \<B> w\<^bsub>f\<^esub>\<^bsub>\<Lambda> s\<^esub>" by simp
      then have "\<B> w\<^bsub>f\<^esub>\<^bsub>\<Lambda> s\<^esub> \<le> \<B> w\<^bsub>g\<^esub>\<^bsub>\<Lambda> s\<^esub>"
        by (simp add: sup.orderI)
      then show "discretize\<^sub>f \<B> f s \<le> discretize\<^sub>f \<B> g s" by simp
    qed
    then show ?thesis using le by auto

  next
    case (eq_empty x n)
    let ?lt = "AT (Var (Solo x) =\<^sub>s \<emptyset> n)"
    from eq_empty have "?lt \<in> reduce_literal lt"
      using \<open>lt \<in> set \<C>\<close> by simp
    then have "?lt \<in> clause"
      using \<open>lt \<in> set \<C>\<close> clause
      unfolding reduced_dnf_def reduce_clause_def by fastforce
    with \<B>_sat_clause have "interp I\<^sub>s\<^sub>a \<B> ?lt" by fastforce
    with eq_empty show ?thesis by simp

  next
    case (eq x y)
    let ?lt = "AT (Var (Solo x) =\<^sub>s Var (Solo y))"
    from eq have "?lt \<in> reduce_literal lt"
      using \<open>lt \<in> set \<C>\<close> by simp
    then have "?lt \<in> clause"
      using \<open>lt \<in> set \<C>\<close> clause
      unfolding reduced_dnf_def reduce_clause_def by fastforce
    with \<B>_sat_clause have "interp I\<^sub>s\<^sub>a \<B> ?lt" by fastforce
    with eq show ?thesis by simp

  next
    case (neq x y)
    let ?lt = "AF (Var (Solo x) =\<^sub>s Var (Solo y))"
    from neq have "?lt \<in> reduce_literal lt"
      using \<open>lt \<in> set \<C>\<close> by simp
    then have "?lt \<in> clause"
      using \<open>lt \<in> set \<C>\<close> clause
      unfolding reduced_dnf_def reduce_clause_def by fastforce
    with \<B>_sat_clause have "interp I\<^sub>s\<^sub>a \<B> ?lt" by fastforce
    with neq show ?thesis by simp

  next
    case (union x y z)
    let ?lt = "AT (Var (Solo x) =\<^sub>s Var (Solo y) \<squnion>\<^sub>s Var (Solo z))"
    from union have "?lt \<in> reduce_literal lt"
      using \<open>lt \<in> set \<C>\<close> by simp
    then have "?lt \<in> clause"
      using neq \<open>lt \<in> set \<C>\<close> clause
      unfolding reduced_dnf_def reduce_clause_def by fastforce
    with \<B>_sat_clause have "interp I\<^sub>s\<^sub>a \<B> ?lt" by fastforce
    with union show ?thesis by simp

  next
    case (diff x y z)
    let ?lt = "AT (Var (Solo x) =\<^sub>s Var (Solo y) -\<^sub>s Var (Solo z))"
    from diff have "?lt \<in> reduce_literal lt"
      using \<open>lt \<in> set \<C>\<close> by simp
    then have "?lt \<in> clause"
      using neq \<open>lt \<in> set \<C>\<close> clause
      unfolding reduced_dnf_def reduce_clause_def by fastforce
    with \<B>_sat_clause have "interp I\<^sub>s\<^sub>a \<B> ?lt" by fastforce
    with diff show ?thesis by simp

  next
    case (single x y)
    let ?lt = "AT (Var (Solo x) =\<^sub>s Single (Var (Solo y)))"
    from single have "?lt \<in> reduce_literal lt"
      using \<open>lt \<in> set \<C>\<close> by simp
    then have "?lt \<in> clause"
      using neq \<open>lt \<in> set \<C>\<close> clause
      unfolding reduced_dnf_def reduce_clause_def by fastforce
    with \<B>_sat_clause have "interp I\<^sub>s\<^sub>a \<B> ?lt" by fastforce
    with single show ?thesis by simp

  next
    case (app x f y)
    with \<open>lt \<in> set \<C>\<close> have "f \<in> F" unfolding F_def by force
    from \<B>_sat_clause clause eval_v
    have \<B>_v: "(\<B> \<circ> VennRegion) \<alpha> = proper_Venn_region \<alpha>" if "\<alpha> \<in> P\<^sup>+ V" for \<alpha>
      unfolding reduced_dnf_def
      using proper_Venn_region.simps that by force
    from \<B>_sat_clause clause eval_w
    have \<B>_w: "\<Squnion>HF ((\<B> \<circ> VennRegion) ` l) = \<Squnion>HF ((\<B> \<circ> VennRegion) ` m) \<longrightarrow> \<B> w\<^bsub>f\<^esub>\<^bsub>l\<^esub> = \<B> w\<^bsub>f\<^esub>\<^bsub>m\<^esub>"
      if "l \<subseteq> P\<^sup>+ V" "m \<subseteq> P\<^sup>+ V" "f \<in> F" for l m f
      by (meson in_mono introduce_UnionOfVennRegions_subset_reduced_fms introduce_w_subset_reduced_fms that)
    
    from app \<open>lt \<in> set \<C>\<close> have "y \<in> V" using V_def by fastforce
    with variable_as_composition_of_proper_Venn_regions
    have "\<Squnion>HF (proper_Venn_region ` \<L> V y) = discretize\<^sub>v \<B> y" by blast
    with \<Lambda>_discr \<L>_subset_P_plus \<B>_v
    have "\<Squnion>HF ((\<B> \<circ> VennRegion) ` \<L> V y) = \<Squnion>HF ((\<B> \<circ> VennRegion) ` \<Lambda> (discretize\<^sub>v \<B> y))"
      by (smt (verit, best) HUnion_eq subset_eq)
    with \<B>_w have \<B>_w_eq: "\<B> w\<^bsub>f\<^esub>\<^bsub>\<L> V y\<^esub> = \<B> w\<^bsub>f\<^esub>\<^bsub>\<Lambda> (discretize\<^sub>v \<B> y)\<^esub>"
      using \<L>_subset_P_plus \<Lambda>_subset_V \<open>f \<in> F\<close> finite_V by meson

    let ?lt = "AT (Var (Solo x) =\<^sub>s Var w\<^bsub>f\<^esub>\<^bsub>\<L> V y\<^esub>)"
    from app have "?lt \<in> reduce_literal lt"
      using \<open>lt \<in> set \<C>\<close> by simp
    then have "?lt \<in> clause"
      using neq \<open>lt \<in> set \<C>\<close> clause
      unfolding reduced_dnf_def reduce_clause_def by fastforce
    with \<B>_sat_clause have "interp I\<^sub>s\<^sub>a \<B> ?lt" by fastforce
    then have "\<B> (Solo x) = \<B> w\<^bsub>f\<^esub>\<^bsub>\<L> V y\<^esub>" by simp
    with \<B>_w_eq have "\<B> (Solo x) = \<B> w\<^bsub>f\<^esub>\<^bsub>\<Lambda> (discretize\<^sub>v \<B> y)\<^esub>" by argo
    then have "\<B> (Solo x) = (discretize\<^sub>f \<B> f) (discretize\<^sub>v \<B> y)" by simp
    then have "discretize\<^sub>v \<B> x = (discretize\<^sub>f \<B> f) (discretize\<^sub>v \<B> y)" by simp
    with app show ?thesis by simp
  qed
qed

lemma \<C>_sat: "I\<^sub>c\<^sub>l (discretize\<^sub>v \<B>) (discretize\<^sub>f \<B>) \<C>"
  using all_literal_sat by blast

end
                          
lemma (in normalized_MLSSmf_clause) MLSSmf_to_MLSS_completeness:
  assumes "is_model_for_reduced_dnf M"
    shows "\<exists>M\<^sub>v M\<^sub>f. I\<^sub>c\<^sub>l M\<^sub>v M\<^sub>f \<C>"
proof -
  from assms singleton_model_for_reduced_MLSS_clause obtain \<M> where
    \<M>_singleton: "\<forall>\<alpha> \<in> P\<^sup>+ V. hcard (\<M> (v\<^bsub>\<alpha>\<^esub>)) \<le> 1" and
    \<M>_model: "is_model_for_reduced_dnf \<M>"
    using normalized_MLSSmf_clause_axioms V_def by blast
  then obtain clause where "clause \<in> reduced_dnf" "\<forall>lt \<in> clause. interp I\<^sub>s\<^sub>a \<M> lt"
    unfolding is_model_for_reduced_dnf_def by blast
  with normalized_clause_contains_all_v_\<alpha> have v_\<alpha>_in_vars:
    "\<forall>\<alpha>\<in>P\<^sup>+ V. v\<^bsub>\<alpha>\<^esub> \<in> \<Union> (vars ` clause)"
    by blast

  from \<M>_singleton have assigned_set_card_0_or_1:
    "\<forall>\<alpha> \<in> P\<^sup>+ V. hcard (\<M> (v\<^bsub>\<alpha>\<^esub>)) = 0 \<or> hcard (\<M> (v\<^bsub>\<alpha>\<^esub>)) = 1"
    using antisym_conv2 by blast

  let ?\<Lambda> = "\<lambda>a. {\<alpha> \<in> P\<^sup>+ V. \<M> v\<^bsub>\<alpha>\<^esub> \<sqinter> a \<noteq> 0}"

  have \<Lambda>_subset_V: "?\<Lambda> x \<subseteq> P\<^sup>+ V" for x
    by fast

  have \<Lambda>_preserves_zero: "?\<Lambda> 0 = {}" by blast

  have \<Lambda>_inc: "a \<le> b \<Longrightarrow> ?\<Lambda> a \<subseteq> ?\<Lambda> b" for a b
    by (smt (verit) Collect_mono hinter_hempty_right inf.absorb_iff1 inf_left_commute)

  have \<Lambda>_add: "?\<Lambda> (a \<squnion> b) = ?\<Lambda> a \<union> ?\<Lambda> b" for a b
  proof (standard; standard)
    fix \<alpha> assume \<alpha>: "\<alpha> \<in> {\<alpha> \<in> P\<^sup>+ V. \<M> v\<^bsub>\<alpha>\<^esub> \<sqinter> (a \<squnion> b) \<noteq> 0}"
    then have "\<alpha> \<in> P\<^sup>+ V" "\<M> v\<^bsub>\<alpha>\<^esub> \<sqinter> (a \<squnion> b) \<noteq> 0" by blast+
    then have "\<M> v\<^bsub>\<alpha>\<^esub> \<sqinter> a \<noteq> 0 \<or> \<M> v\<^bsub>\<alpha>\<^esub> \<sqinter> b \<noteq> 0"
      by (metis hunion_hempty_right inf_sup_distrib1) 
    then show "\<alpha> \<in> {\<alpha> \<in> P\<^sup>+ V. \<M> v\<^bsub>\<alpha>\<^esub> \<sqinter> a \<noteq> 0} \<union> {\<alpha> \<in> P\<^sup>+ V. \<M> v\<^bsub>\<alpha>\<^esub> \<sqinter> b \<noteq> 0}"
      using \<alpha> by blast
  next
    fix \<alpha> assume "\<alpha> \<in> {\<alpha> \<in> P\<^sup>+ V. \<M> v\<^bsub>\<alpha>\<^esub> \<sqinter> a \<noteq> 0} \<union> {\<alpha> \<in> P\<^sup>+ V. \<M> v\<^bsub>\<alpha>\<^esub> \<sqinter> b \<noteq> 0}"
    then have "\<alpha> \<in> P\<^sup>+ V" "\<M> v\<^bsub>\<alpha>\<^esub> \<sqinter> a \<noteq> 0 \<or> \<M> v\<^bsub>\<alpha>\<^esub> \<sqinter> b \<noteq> 0"
      by blast+
    then have "\<M> v\<^bsub>\<alpha>\<^esub> \<sqinter> (a \<squnion> b) \<noteq> 0"
      by (metis hinter_hempty_right hunion_hempty_left inf_sup_absorb inf_sup_distrib1)
    then show "\<alpha> \<in> {\<alpha> \<in> P\<^sup>+ V. \<M> v\<^bsub>\<alpha>\<^esub> \<sqinter> (a \<squnion> b) \<noteq> 0}"
      using \<open>\<alpha> \<in> P\<^sup>+ V\<close> by blast
  qed

  have \<Lambda>_mul: "?\<Lambda> (a \<sqinter> b) = ?\<Lambda> a \<inter> ?\<Lambda> b" for a b
  proof (standard; standard)
    fix \<alpha> assume \<alpha>: "\<alpha> \<in> {\<alpha> \<in> P\<^sup>+ V. \<M> v\<^bsub>\<alpha>\<^esub> \<sqinter> (a \<sqinter> b) \<noteq> 0}"
    then have "\<alpha> \<in> P\<^sup>+ V" "\<M> v\<^bsub>\<alpha>\<^esub> \<sqinter> (a \<sqinter> b) \<noteq> 0" by blast+
    then have "\<M> v\<^bsub>\<alpha>\<^esub> \<sqinter> a \<noteq> 0 \<and> \<M> v\<^bsub>\<alpha>\<^esub> \<sqinter> b \<noteq> 0"
      by (metis hinter_hempty_left inf_assoc inf_left_commute)
    then show "\<alpha> \<in> {\<alpha> \<in> P\<^sup>+ V. \<M> v\<^bsub>\<alpha>\<^esub> \<sqinter> a \<noteq> 0} \<inter> {\<alpha> \<in> P\<^sup>+ V. \<M> v\<^bsub>\<alpha>\<^esub> \<sqinter> b \<noteq> 0}"
      using \<alpha> by blast
  next
    fix \<alpha> assume "\<alpha> \<in> {\<alpha> \<in> P\<^sup>+ V. \<M> v\<^bsub>\<alpha>\<^esub> \<sqinter> a \<noteq> 0} \<inter> {\<alpha> \<in> P\<^sup>+ V. \<M> v\<^bsub>\<alpha>\<^esub> \<sqinter> b \<noteq> 0}"
    then have "\<alpha> \<in> P\<^sup>+ V" "\<M> v\<^bsub>\<alpha>\<^esub> \<sqinter> a \<noteq> 0" "\<M> v\<^bsub>\<alpha>\<^esub> \<sqinter> b \<noteq> 0"
      by blast+
    then have "\<M> v\<^bsub>\<alpha>\<^esub> \<noteq> 0" by force
    then have "hcard (\<M> v\<^bsub>\<alpha>\<^esub>) \<noteq> 0" using hcard_0E by blast
    then have "hcard (\<M> v\<^bsub>\<alpha>\<^esub>) = 1"
      using assigned_set_card_0_or_1 v_\<alpha>_in_vars \<open>\<alpha> \<in> P\<^sup>+ V\<close>
      by fastforce
    then obtain c where "\<M> v\<^bsub>\<alpha>\<^esub> = 0 \<triangleleft> c"
      using hcard_1E by blast
    moreover
    from \<open>\<M> v\<^bsub>\<alpha>\<^esub> = 0 \<triangleleft> c\<close> \<open>\<M> v\<^bsub>\<alpha>\<^esub> \<sqinter> a \<noteq> 0\<close>
    have "\<M> v\<^bsub>\<alpha>\<^esub> \<sqinter> a = 0 \<triangleleft> c" by auto
    moreover
    from \<open>\<M> v\<^bsub>\<alpha>\<^esub> = 0 \<triangleleft> c\<close> \<open>\<M> v\<^bsub>\<alpha>\<^esub> \<sqinter> b \<noteq> 0\<close>
    have "\<M> v\<^bsub>\<alpha>\<^esub> \<sqinter> b = 0 \<triangleleft> c" by auto
    ultimately
    have "\<M> v\<^bsub>\<alpha>\<^esub> \<sqinter> (a \<sqinter> b) = 0 \<triangleleft> c"
      by (simp add: inf_commute inf_left_commute)
    then have "\<M> v\<^bsub>\<alpha>\<^esub> \<sqinter> (a \<sqinter> b) \<noteq> 0" by simp
    then show "\<alpha> \<in> {\<alpha> \<in> P\<^sup>+ V. \<M> v\<^bsub>\<alpha>\<^esub> \<sqinter> (a \<sqinter> b) \<noteq> 0}"
      using \<open>\<alpha> \<in> P\<^sup>+ V\<close> by blast
  qed

  have "l \<subseteq> P\<^sup>+ V \<Longrightarrow>
        a = \<Squnion>HF ((\<M> \<circ> VennRegion) ` l) \<Longrightarrow> a \<le> \<Squnion>HF ((\<M> \<circ> VennRegion) ` (?\<Lambda> a))" for l a
  proof
    fix c assume l_a_c: "l \<subseteq> P\<^sup>+ V" "a = \<Squnion>HF ((\<M> \<circ> VennRegion) ` l)" "c \<^bold>\<in> a"
    then obtain \<alpha> where "\<alpha> \<in> l" "c \<^bold>\<in> \<M> v\<^bsub>\<alpha>\<^esub>" by auto
    then have "\<alpha> \<in> ?\<Lambda> a" using l_a_c by blast
    then have "\<M> v\<^bsub>\<alpha>\<^esub> \<in> (\<M> \<circ> VennRegion) ` (?\<Lambda> a)" by simp
    then have "\<M> v\<^bsub>\<alpha>\<^esub> \<^bold>\<in> HF ((\<M> \<circ> VennRegion) ` (?\<Lambda> a))" by fastforce
    with \<open>c \<^bold>\<in> \<M> v\<^bsub>\<alpha>\<^esub>\<close> show "c \<^bold>\<in> \<Squnion>HF ((\<M> \<circ> VennRegion) ` (?\<Lambda> a))" by blast
  qed
  moreover
  have "l \<subseteq> P\<^sup>+ V \<Longrightarrow>
        a = \<Squnion>HF ((\<M> \<circ> VennRegion) ` l) \<Longrightarrow> \<Squnion>HF ((\<M> \<circ> VennRegion) ` (?\<Lambda> a)) \<le> a" for l a
  proof -
    assume "l \<subseteq> P\<^sup>+ V" and a: "a = \<Squnion>HF ((\<M> \<circ> VennRegion) ` l)"
    then have "finite l"
      by (simp add: finite_V finite_subset)
    have "?\<Lambda> a \<subseteq> l"
    proof
      fix \<alpha> assume "\<alpha> \<in> ?\<Lambda> a"
      then obtain c where "c \<^bold>\<in> \<M> v\<^bsub>\<alpha>\<^esub> \<sqinter> a" by blast
      then have "c \<^bold>\<in> \<M> v\<^bsub>\<alpha>\<^esub>" "c \<^bold>\<in> a" by blast+
      then obtain \<beta> where "\<beta> \<in> l" "c \<^bold>\<in> \<M> v\<^bsub>\<beta>\<^esub>" using a by force


      interpret proper_Venn_regions V "\<M> \<circ> Solo"
        using finite_V by unfold_locales
      from \<open>\<alpha> \<in> ?\<Lambda> a\<close> have "\<alpha> \<in> P\<^sup>+ V" by auto
      moreover
      from \<open>l \<subseteq> P\<^sup>+ V\<close> \<open>\<beta> \<in> l\<close> have "\<beta> \<in> P\<^sup>+ V" by auto
      moreover
      from \<open>c \<^bold>\<in> \<M> v\<^bsub>\<alpha>\<^esub>\<close> have "c \<^bold>\<in> proper_Venn_region \<alpha>"
        using eval_v \<open>\<alpha> \<in> P\<^sup>+ V\<close> \<M>_model
        unfolding is_model_for_reduced_dnf_def reduced_dnf_def
        by fastforce
      moreover
      from \<open>c \<^bold>\<in> \<M> v\<^bsub>\<beta>\<^esub>\<close> have "c \<^bold>\<in> proper_Venn_region \<beta>"
        using eval_v \<open>\<beta> \<in> P\<^sup>+ V\<close> \<M>_model
        unfolding is_model_for_reduced_dnf_def reduced_dnf_def
        by fastforce
      ultimately
      have "\<alpha> = \<beta>"
        using finite_V proper_Venn_region_strongly_injective by auto
      with \<open>\<beta> \<in> l\<close> show "\<alpha> \<in> l" by simp
    qed
    then have "(\<M> \<circ> VennRegion) ` ?\<Lambda> a \<subseteq> (\<M> \<circ> VennRegion) ` l" by blast
    moreover
    from \<open>finite l\<close> have "finite ((\<M> \<circ> VennRegion) ` l)" by blast
    ultimately
    have "\<Squnion>HF ((\<M> \<circ> VennRegion) ` ?\<Lambda> a) \<le> \<Squnion>HF ((\<M> \<circ> VennRegion) ` l)"
      by (metis (no_types, lifting) HUnion_hunion finite_subset sup.orderE sup.orderI union_hunion)
    then show "\<Squnion>HF ((\<M> \<circ> VennRegion) ` (?\<Lambda> a)) \<le> a"
      using a by blast
  qed
  ultimately
  have \<Lambda>_discr: "l \<subseteq> P\<^sup>+ V \<Longrightarrow>
                 a = \<Squnion>HF ((\<M> \<circ> VennRegion) ` l) \<Longrightarrow> a = \<Squnion>HF ((\<M> \<circ> VennRegion) ` (?\<Lambda> a))" for l a
    by (simp add: inf.absorb_iff1 inf_commute)

  interpret \<Lambda>_plus: MLSSmf_to_MLSS_complete \<C> \<M> ?\<Lambda>
    using assms \<M>_singleton \<M>_model
          \<Lambda>_subset_V \<Lambda>_preserves_zero \<Lambda>_inc \<Lambda>_add \<Lambda>_mul \<Lambda>_discr
    by unfold_locales

  show ?thesis
    using \<Lambda>_plus.\<C>_sat by fast
qed

end