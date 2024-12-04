section \<open>\<open>Weak_Operator_Topology\<close> -- Weak operator topology on complex bounded operators\<close>

theory Weak_Operator_Topology
  imports Misc_Tensor_Product Strong_Operator_Topology Positive_Operators Wlog.Wlog
begin

unbundle cblinfun_notation

definition cweak_operator_topology::"('a::complex_normed_vector \<Rightarrow>\<^sub>C\<^sub>L'b::complex_inner) topology"
  where "cweak_operator_topology = pullback_topology UNIV (\<lambda>a (x,y). cinner x (a *\<^sub>V y)) euclidean"

lemma cweak_operator_topology_topspace[simp]:
  "topspace cweak_operator_topology = UNIV"
  unfolding cweak_operator_topology_def topspace_pullback_topology topspace_euclidean by auto

lemma cweak_operator_topology_basis:
  fixes f::"('a::complex_normed_vector \<Rightarrow>\<^sub>C\<^sub>L 'b::complex_inner)" and U::"'i \<Rightarrow> complex set" and x::"'i \<Rightarrow> 'b" and y::\<open>'i \<Rightarrow> 'a\<close>
  assumes "finite I" "\<And>i. i \<in> I \<Longrightarrow> open (U i)"
  shows "openin cweak_operator_topology {f. \<forall>i\<in>I. cinner (x i) (f *\<^sub>V y i) \<in> U i}"
proof -
  have "open {g::(('b\<times>'a)\<Rightarrow>complex). \<forall>i\<in>I. g (x i, y i) \<in> U i}"
    by (rule product_topology_basis'[OF assms])
  moreover have "{f. \<forall>i\<in>I. cinner (x i) (f *\<^sub>V y i) \<in> U i}
                = (\<lambda>f (x,y). cinner x (f *\<^sub>V y))-`\<dots> \<inter> UNIV"
    by auto
  ultimately show ?thesis
    unfolding cweak_operator_topology_def by (subst openin_pullback_topology) auto
qed

lemma wot_weaker_than_sot:
  "continuous_map cstrong_operator_topology cweak_operator_topology (\<lambda>f. f)"
proof -
  have *: \<open>continuous_on UNIV ((\<lambda>z. cinner x z) o (\<lambda>f. f y))\<close> for x :: 'b and y :: 'a
    apply (rule continuous_on_compose)
    by (auto intro: continuous_on_compose continuous_at_imp_continuous_on)
  have *: \<open>continuous_map euclidean euclidean (\<lambda>f (x::'b, y::'a). x \<bullet>\<^sub>C f y)\<close>
    apply simp
    apply (rule continuous_on_coordinatewise_then_product)
    using * by auto
  have *: \<open>continuous_map (pullback_topology UNIV (*\<^sub>V) euclidean) euclidean ((\<lambda>f (x::'b, a::'a). x \<bullet>\<^sub>C f a) \<circ> (*\<^sub>V))\<close>
    apply (rule continuous_map_pullback)
    using * by simp
  have *: \<open>continuous_map (pullback_topology UNIV (*\<^sub>V) euclidean) euclidean ((\<lambda>a (x::'b, y::'a). x \<bullet>\<^sub>C (a *\<^sub>V y)) \<circ> (\<lambda>f. f))\<close>
     apply (subst asm_rl[of \<open>((\<lambda>a (x, y). x \<bullet>\<^sub>C (a *\<^sub>V y)) \<circ> (\<lambda>f. f)) = (\<lambda>f (a,b). cinner a (f b)) o (*\<^sub>V)\<close>])
     using * by auto
   show ?thesis
    unfolding cstrong_operator_topology_def cweak_operator_topology_def
    apply (rule continuous_map_pullback')
    using * by auto
qed


lemma cweak_operator_topology_weaker_than_euclidean:
  "continuous_map euclidean cweak_operator_topology (\<lambda>f. f)"
  by (metis (mono_tags, lifting) continuous_map_compose continuous_map_eq cstrong_operator_topology_weaker_than_euclidean wot_weaker_than_sot o_def)


lemma cweak_operator_topology_cinner_continuous:
  "continuous_map cweak_operator_topology euclidean (\<lambda>f. cinner x (f *\<^sub>V y))"
proof -
  have "continuous_map cweak_operator_topology euclidean ((\<lambda>f. f (x,y)) o (\<lambda>a (x,y). cinner x (a *\<^sub>V y)))"
    unfolding cweak_operator_topology_def apply (rule continuous_map_pullback)
    using continuous_on_product_coordinates by fastforce
  then show ?thesis unfolding comp_def by simp
qed

lemma continuous_on_cweak_operator_topo_iff_coordinatewise:
  "continuous_map T cweak_operator_topology f
    \<longleftrightarrow> (\<forall>x y. continuous_map T euclidean (\<lambda>z.  cinner x (f z *\<^sub>V y)))"
proof (intro iffI allI)
  fix x::'c and y::'b
  assume "continuous_map T cweak_operator_topology f"
  with continuous_map_compose[OF this cweak_operator_topology_cinner_continuous]
  have "continuous_map T euclidean ((\<lambda>f. cinner x (f *\<^sub>V y)) o f)"
    by simp
  then show "continuous_map T euclidean (\<lambda>z.  cinner x (f z *\<^sub>V y))"
    unfolding comp_def by auto
next
  assume *: \<open>\<forall>x y. continuous_map T euclidean (\<lambda>z. x \<bullet>\<^sub>C (f z *\<^sub>V y))\<close>
  then have *: "continuous_map T euclidean ((\<lambda>a (x,y). cinner x (a *\<^sub>V y)) o f)"
    by (auto simp flip: euclidean_product_topology)
  show "continuous_map T cweak_operator_topology f"
    unfolding cweak_operator_topology_def
    apply (rule continuous_map_pullback')
    by (auto simp add: *)
qed

typedef (overloaded) ('a,'b) cblinfun_wot = \<open>UNIV :: ('a::complex_normed_vector \<Rightarrow>\<^sub>C\<^sub>L 'b::complex_inner) set\<close> ..
setup_lifting type_definition_cblinfun_wot

instantiation cblinfun_wot :: (complex_normed_vector, complex_inner) complex_vector begin
lift_definition scaleC_cblinfun_wot :: \<open>complex \<Rightarrow> ('a, 'b) cblinfun_wot \<Rightarrow> ('a, 'b) cblinfun_wot\<close> 
  is \<open>scaleC\<close> .
lift_definition uminus_cblinfun_wot :: \<open>('a, 'b) cblinfun_wot \<Rightarrow> ('a, 'b) cblinfun_wot\<close> is uminus .
lift_definition zero_cblinfun_wot :: \<open>('a, 'b) cblinfun_wot\<close> is 0 .
lift_definition minus_cblinfun_wot :: \<open>('a, 'b) cblinfun_wot \<Rightarrow> ('a, 'b) cblinfun_wot \<Rightarrow> ('a, 'b) cblinfun_wot\<close> is minus .
lift_definition plus_cblinfun_wot :: \<open>('a, 'b) cblinfun_wot \<Rightarrow> ('a, 'b) cblinfun_wot \<Rightarrow> ('a, 'b) cblinfun_wot\<close> is plus .
lift_definition scaleR_cblinfun_wot :: \<open>real \<Rightarrow> ('a, 'b) cblinfun_wot \<Rightarrow> ('a, 'b) cblinfun_wot\<close> is scaleR .
instance
  apply (intro_classes; transfer)
  by (auto simp add: scaleR_scaleC scaleC_add_right scaleC_add_left)
end

instantiation cblinfun_wot :: (complex_normed_vector, complex_inner) topological_space begin
lift_definition open_cblinfun_wot :: \<open>('a, 'b) cblinfun_wot set \<Rightarrow> bool\<close> is \<open>openin cweak_operator_topology\<close> .
instance
proof intro_classes
  show \<open>open (UNIV :: ('a,'b) cblinfun_wot set)\<close>
    apply transfer
    by (metis cweak_operator_topology_topspace openin_topspace)
  show \<open>open S \<Longrightarrow> open T \<Longrightarrow> open (S \<inter> T)\<close> for S T :: \<open>('a,'b) cblinfun_wot set\<close>
    apply transfer by auto
  show \<open>\<forall>S\<in>K. open S \<Longrightarrow> open (\<Union> K)\<close> for K :: \<open>('a,'b) cblinfun_wot set set\<close>
    apply transfer by auto
qed
end

lemma transfer_nhds_cweak_operator_topology[transfer_rule]:
  includes lifting_syntax
  shows \<open>(cr_cblinfun_wot ===> rel_filter cr_cblinfun_wot) (nhdsin cweak_operator_topology) nhds\<close>
  unfolding nhds_def nhdsin_def
  apply (simp add: cweak_operator_topology_topspace)
  by transfer_prover

lemma limitin_cweak_operator_topology: 
  \<open>limitin cweak_operator_topology f l F \<longleftrightarrow> (\<forall>a b. ((\<lambda>i. a \<bullet>\<^sub>C (f i *\<^sub>V b)) \<longlongrightarrow> a \<bullet>\<^sub>C (l *\<^sub>V b)) F)\<close>
  by (simp add: cweak_operator_topology_def limitin_pullback_topology tendsto_coordinatewise)

lemma filterlim_cweak_operator_topology: \<open>filterlim f (nhdsin cweak_operator_topology l) = limitin cweak_operator_topology f l\<close>
  by (auto simp: cweak_operator_topology_topspace simp flip: filterlim_nhdsin_iff_limitin)

instance cblinfun_wot :: (complex_normed_vector, complex_inner) t2_space
proof intro_classes
  fix a b :: \<open>('a,'b) cblinfun_wot\<close>
  show \<open>a \<noteq> b \<Longrightarrow> \<exists>U V. open U \<and> open V \<and> a \<in> U \<and> b \<in> V \<and> U \<inter> V = {}\<close>
  proof transfer
    fix a b :: \<open>'a \<Rightarrow>\<^sub>C\<^sub>L 'b\<close>
    assume \<open>a \<noteq> b\<close>
    then obtain \<phi> \<psi> where \<open>\<phi> \<bullet>\<^sub>C (a *\<^sub>V \<psi>) \<noteq> \<phi> \<bullet>\<^sub>C (b *\<^sub>V \<psi>)\<close>
      by (meson cblinfun_eqI cinner_extensionality)
    then obtain U' V' where \<open>open U'\<close> \<open>open V'\<close> and inU': \<open>\<phi> \<bullet>\<^sub>C (a *\<^sub>V \<psi>) \<in> U'\<close> and inV': \<open>\<phi> \<bullet>\<^sub>C (b *\<^sub>V \<psi>) \<in> V'\<close> and \<open>U' \<inter> V' = {}\<close>
      by (meson hausdorff)
    define U V :: \<open>('a \<Rightarrow>\<^sub>C\<^sub>L 'b) set\<close> where \<open>U = {f. \<forall>i\<in>{()}. \<phi> \<bullet>\<^sub>C (f *\<^sub>V \<psi>) \<in> U'}\<close> and \<open>V = {f. \<forall>i\<in>{()}. \<phi> \<bullet>\<^sub>C (f *\<^sub>V \<psi>) \<in> V'}\<close>
    have \<open>openin cweak_operator_topology U\<close>
      unfolding U_def apply (rule cweak_operator_topology_basis)
      using \<open>open U'\<close> by auto
    moreover have \<open>openin cweak_operator_topology V\<close>
      unfolding V_def apply (rule cweak_operator_topology_basis)
      using \<open>open V'\<close> by auto
    ultimately show \<open>\<exists>U V. openin cweak_operator_topology U \<and> openin cweak_operator_topology V \<and> a \<in> U \<and> b \<in> V \<and> U \<inter> V = {}\<close>
      apply (rule_tac exI[of _ U])
      apply (rule_tac exI[of _ V])
      using inU' inV' \<open>U' \<inter> V' = {}\<close> by (auto simp: U_def V_def)
  qed
qed

lemma Domainp_cr_cblinfun_wot[simp]: \<open>Domainp cr_cblinfun_wot = (\<lambda>_. True)\<close>
  by (metis (no_types, opaque_lifting) DomainPI cblinfun_wot.left_total left_totalE)

lemma Rangep_cr_cblinfun_wot[simp]: \<open>Rangep cr_cblinfun_wot = (\<lambda>_. True)\<close>
  by (meson RangePI cr_cblinfun_wot_def)

lemma transfer_euclidean_cweak_operator_topology[transfer_rule]:
  includes lifting_syntax
  shows \<open>(rel_topology cr_cblinfun_wot) cweak_operator_topology euclidean\<close>
proof (unfold rel_topology_def, intro conjI allI impI)
  show \<open>(rel_set cr_cblinfun_wot ===> (=)) (openin cweak_operator_topology) (openin euclidean)\<close>
    apply (auto simp: rel_topology_def cr_cblinfun_wot_def rel_set_def intro!: rel_funI)
     apply transfer
     apply auto
     apply (meson openin_subopen subsetI)
    apply transfer
    apply auto
    by (meson openin_subopen subsetI)
next
  fix U :: \<open>('a \<Rightarrow>\<^sub>C\<^sub>L 'b) set\<close>
  assume \<open>openin cweak_operator_topology U\<close>
  show \<open>Domainp (rel_set cr_cblinfun_wot) U\<close>
    by (simp add: Domainp_set)
next
  fix U :: \<open>('a, 'b) cblinfun_wot set\<close>
  assume \<open>openin euclidean U\<close>
  show \<open>Rangep (rel_set cr_cblinfun_wot) U\<close>
    by (simp add: Rangep_set)
qed

lemma openin_cweak_operator_topology: \<open>openin cweak_operator_topology U \<longleftrightarrow> (\<exists>V. open V \<and> U = (\<lambda>a (x,y). cinner x (a *\<^sub>V y)) -` V)\<close>
  by (simp add: cweak_operator_topology_def openin_pullback_topology)

lemma cweak_operator_topology_plus_cont: \<open>LIM (x,y) nhdsin cweak_operator_topology a \<times>\<^sub>F nhdsin cweak_operator_topology b.
            x + y :> nhdsin cweak_operator_topology (a + b)\<close>
proof -
  show ?thesis
    unfolding cweak_operator_topology_def
    apply (rule_tac pullback_topology_bi_cont[where f'=plus])
    by (auto simp: case_prod_unfold tendsto_add_Pair cinner_add_right cblinfun.add_left)
qed

instance cblinfun_wot :: (complex_normed_vector, complex_inner) topological_group_add
proof intro_classes
  show \<open>((\<lambda>x. fst x + snd x) \<longlongrightarrow> a + b) (nhds a \<times>\<^sub>F nhds b)\<close> for a b :: \<open>('a,'b) cblinfun_wot\<close>
    apply transfer
    using cweak_operator_topology_plus_cont
    by (auto simp: case_prod_unfold)

  have *: \<open>continuous_map cweak_operator_topology cweak_operator_topology uminus\<close>
    apply (subst continuous_on_cweak_operator_topo_iff_coordinatewise)
    apply (rewrite at \<open>(\<lambda>z. x \<bullet>\<^sub>C (- z *\<^sub>V y))\<close> in \<open>\<forall>x y. \<hole>\<close> to \<open>(\<lambda>z. - x \<bullet>\<^sub>C (z *\<^sub>V y))\<close> DEADID.rel_mono_strong)
    by (auto simp: cweak_operator_topology_cinner_continuous cblinfun.minus_left cblinfun.minus_right)
  show \<open>(uminus \<longlongrightarrow> - a) (nhds a)\<close> for a :: \<open>('a,'b) cblinfun_wot\<close>
    apply (subst tendsto_at_iff_tendsto_nhds[symmetric])
    apply (subst isCont_def[symmetric])
    apply (rule continuous_on_interior[where S=UNIV])
     apply (subst continuous_map_iff_continuous2[symmetric])
     apply transfer
    using * by auto
qed

lemma continuous_map_left_comp_wot: 
  \<open>continuous_map cweak_operator_topology cweak_operator_topology (\<lambda>a::'a::complex_normed_vector \<Rightarrow>\<^sub>C\<^sub>L _. b o\<^sub>C\<^sub>L a)\<close> 
  for b :: \<open>'b::chilbert_space \<Rightarrow>\<^sub>C\<^sub>L 'c::complex_inner\<close>
proof -
  have **: \<open>((\<lambda>f::'b \<times> 'a \<Rightarrow> complex. f (b* *\<^sub>V x, y)) -` B \<inter> UNIV) 
          = (Pi\<^sub>E UNIV (\<lambda>z. if z = (b* *\<^sub>V x, y) then B else UNIV))\<close> 
    for x :: 'c and y :: 'a and B :: \<open>complex set\<close>
    by (auto simp: PiE_def Pi_def)
  have *: \<open>continuous_on UNIV (\<lambda>f::'b \<times> 'a \<Rightarrow> complex. f (b* *\<^sub>V x, y))\<close> for x y
    unfolding continuous_on_open_vimage[OF open_UNIV]
    apply (intro allI impI)
    apply (subst **)
    apply (rule open_PiE)
    by auto
  have *: \<open>continuous_on UNIV (\<lambda>(f::'b \<times> 'a \<Rightarrow> complex) (x, y). f (b* *\<^sub>V x, y))\<close>
    apply (rule continuous_on_coordinatewise_then_product)
    using * by auto
  show ?thesis
    unfolding cweak_operator_topology_def
    apply (rule continuous_map_pullback')
     apply (subst asm_rl[of \<open>((\<lambda>(a::'a\<Rightarrow>\<^sub>C\<^sub>L'c) (x, y). x \<bullet>\<^sub>C (a *\<^sub>V y)) \<circ> (o\<^sub>C\<^sub>L) b) = (\<lambda>f (x,y). f (b* *\<^sub>V x,y)) \<circ> (\<lambda>a (x, y). x \<bullet>\<^sub>C (a *\<^sub>V y))\<close>])
      apply (auto intro!: ext simp: cinner_adj_left)[1]
     apply (rule continuous_map_pullback)
    using * by auto
qed

lemma continuous_map_scaleC_wot: \<open>continuous_map cweak_operator_topology cweak_operator_topology 
                         (scaleC c :: ('a::complex_normed_vector \<Rightarrow>\<^sub>C\<^sub>L 'b::chilbert_space) \<Rightarrow> _)\<close>
  apply (subst asm_rl[of \<open>scaleC c = (o\<^sub>C\<^sub>L) (c *\<^sub>C id_cblinfun)\<close>])
   apply auto[1]
  by (rule continuous_map_left_comp_wot)

lemma continuous_scaleC_wot: \<open>continuous_on X (scaleC c :: (_::complex_normed_vector,_::chilbert_space) cblinfun_wot \<Rightarrow> _)\<close>
  apply (rule continuous_on_subset[rotated, where s=UNIV], simp)
  apply (subst continuous_map_iff_continuous2[symmetric])
  apply transfer
  by (rule continuous_map_scaleC_wot)

lemma wot_closure_is_csubspace[simp]:
  fixes A::"('a::complex_normed_vector, 'b::chilbert_space) cblinfun_wot set"
  assumes \<open>csubspace A\<close>
  shows \<open>csubspace (closure A)\<close>
proof (rule complex_vector.subspaceI)
  include lattice_syntax
  show 0: \<open>0 \<in> closure A\<close>
    by (simp add: assms closure_def complex_vector.subspace_0)
  show \<open>x + y \<in> closure A\<close> if \<open>x \<in> closure A\<close> \<open>y \<in> closure A\<close> for x y
  proof -
    define FF where \<open>FF = ((nhds x \<sqinter> principal A) \<times>\<^sub>F (nhds y \<sqinter> principal A))\<close>
    have nt: \<open>FF \<noteq> bot\<close>
      by (simp add: prod_filter_eq_bot that(1) that(2) FF_def flip: closure_nhds_principal)
    have \<open>\<forall>\<^sub>F x in FF. fst x \<in> A\<close>
      unfolding FF_def
      by (smt (verit, ccfv_SIG) eventually_prod_filter fst_conv inf_sup_ord(2) le_principal)
    moreover have \<open>\<forall>\<^sub>F x in FF. snd x \<in> A\<close>
      unfolding FF_def
      by (smt (verit, ccfv_SIG) eventually_prod_filter snd_conv inf_sup_ord(2) le_principal)
    ultimately have FF_plus: \<open>\<forall>\<^sub>F x in FF. fst x + snd x \<in> A\<close>
      by (smt (verit, best) assms complex_vector.subspace_add eventually_elim2)

    have \<open>(fst \<longlongrightarrow> x) ((nhds x \<sqinter> principal A) \<times>\<^sub>F (nhds y \<sqinter> principal A))\<close>
      apply (simp add: filterlim_def)
      using filtermap_fst_prod_filter
      using le_inf_iff by blast
    moreover have \<open>(snd \<longlongrightarrow> y) ((nhds x \<sqinter> principal A) \<times>\<^sub>F (nhds y \<sqinter> principal A))\<close>
      apply (simp add: filterlim_def)
      using filtermap_snd_prod_filter
      using le_inf_iff by blast
    ultimately have \<open>(id \<longlongrightarrow> (x,y)) FF\<close>
      by (simp add: filterlim_def nhds_prod prod_filter_mono FF_def)

    moreover note tendsto_add_Pair[of x y]
    ultimately have \<open>(((\<lambda>x. fst x + snd x) o id) \<longlongrightarrow> (\<lambda>x. fst x + snd x) (x,y)) FF\<close>
      unfolding filterlim_def nhds_prod
      by (smt (verit, best) filterlim_compose filterlim_def filterlim_filtermap fst_conv snd_conv tendsto_compose_filtermap)

    then have \<open>((\<lambda>x. fst x + snd x) \<longlongrightarrow> (x+y)) FF\<close>
      by simp
    then show \<open>x + y \<in> closure A\<close>
      using nt FF_plus by (rule limit_in_closure)
  qed
  show \<open>c *\<^sub>C x \<in> closure A\<close> if \<open>x \<in> closure A\<close> for x c
    using  that
    using image_closure_subset[where S=A and T=\<open>closure A\<close> and f=\<open>scaleC c\<close>, OF continuous_scaleC_wot]
    apply auto
    by (metis 0 assms closure_subset csubspace_scaleC_invariant imageI in_mono scaleC_eq_0_iff)
qed


lemma [transfer_rule]:
  includes lifting_syntax
  shows \<open>(rel_set cr_cblinfun_wot ===> (=)) csubspace csubspace\<close>
  unfolding complex_vector.subspace_def
  by transfer_prover

lemma [transfer_rule]:
  includes lifting_syntax
  shows \<open>(rel_set cr_cblinfun_wot ===> (=)) (closedin cweak_operator_topology) closed\<close>
  apply (simp add: closed_def[abs_def] closedin_def[abs_def] cweak_operator_topology_topspace Compl_eq_Diff_UNIV)
  by transfer_prover

lemma [transfer_rule]:
  includes lifting_syntax
  shows \<open>(rel_set cr_cblinfun_wot ===> rel_set cr_cblinfun_wot) (Abstract_Topology.closure_of cweak_operator_topology) closure\<close>
  apply (subst closure_of_hull[where X=cweak_operator_topology, unfolded cweak_operator_topology_topspace, simplified, abs_def])
  apply (subst closure_hull[abs_def])
  unfolding hull_def
  by transfer_prover

lemma wot_closure_is_csubspace'[simp]:
  fixes A::"('a::complex_normed_vector \<Rightarrow>\<^sub>C\<^sub>L 'b::chilbert_space) set"
  assumes \<open>csubspace A\<close>
  shows \<open>csubspace (cweak_operator_topology closure_of A)\<close>
  using wot_closure_is_csubspace[of \<open>Abs_cblinfun_wot ` A\<close>] assms
  apply (transfer fixing: A)
  by simp

lemma has_sum_closed_cweak_operator_topology:
  fixes A :: \<open>('b::complex_normed_vector \<Rightarrow>\<^sub>C\<^sub>L 'c::complex_inner) set\<close>
  assumes aA: \<open>\<And>i. a i \<in> A\<close>
  assumes closed: \<open>closedin cweak_operator_topology A\<close>
  assumes subspace: \<open>csubspace A\<close>
  assumes has_sum: \<open>\<And>\<phi> \<psi>. ((\<lambda>i. \<phi> \<bullet>\<^sub>C (a i *\<^sub>V \<psi>)) has_sum \<phi> \<bullet>\<^sub>C (b *\<^sub>V \<psi>)) I\<close>
  shows \<open>b \<in> A\<close>
proof -
  have 1: \<open>range (sum a) \<subseteq> A\<close>
  proof -
    have \<open>sum a X \<in> A\<close> for X
      apply (induction X rule:infinite_finite_induct)
      by (auto simp add: subspace complex_vector.subspace_0 aA complex_vector.subspace_add)
    then show ?thesis
      by auto
  qed

  from has_sum
  have \<open>((\<lambda>F. \<Sum>i\<in>F. \<phi> \<bullet>\<^sub>C (a i *\<^sub>V \<psi>)) \<longlongrightarrow> \<phi> \<bullet>\<^sub>C (b *\<^sub>V \<psi>)) (finite_subsets_at_top I)\<close> for \<psi> \<phi>
    using has_sum_def by blast
  then have \<open>limitin cweak_operator_topology (\<lambda>F. \<Sum>i\<in>F. a i) b (finite_subsets_at_top I)\<close>
    by (auto simp add: limitin_cweak_operator_topology cblinfun.sum_left cinner_sum_right)
  then show \<open>b \<in> A\<close>
    using 1 closed apply (rule limitin_closedin)
    by simp
qed

lemma limitin_adj_wot:
  assumes \<open>limitin cweak_operator_topology f l F\<close>
  shows \<open>limitin cweak_operator_topology (\<lambda>i. (f i)*) (l*) F\<close>
proof -
  from assms
  have \<open>((\<lambda>i. a \<bullet>\<^sub>C (f i *\<^sub>V b)) \<longlongrightarrow> a \<bullet>\<^sub>C (l *\<^sub>V b)) F\<close> for a b
    by (simp add: limitin_cweak_operator_topology)
  then have \<open>((\<lambda>i. cnj (a \<bullet>\<^sub>C (f i *\<^sub>V b))) \<longlongrightarrow> cnj (a \<bullet>\<^sub>C (l *\<^sub>V b))) F\<close> for a b
    using tendsto_cnj by blast
  then have \<open>((\<lambda>i. cnj (((f i)* *\<^sub>V a) \<bullet>\<^sub>C b)) \<longlongrightarrow> cnj ((l* *\<^sub>V a) \<bullet>\<^sub>C b)) F\<close> for a b
    by (simp add: cinner_adj_left)
  then have \<open>((\<lambda>i. b \<bullet>\<^sub>C ((f i)* *\<^sub>V a)) \<longlongrightarrow> b \<bullet>\<^sub>C (l* *\<^sub>V a)) F\<close> for a b
    by simp
  then show ?thesis
    by (simp add: limitin_cweak_operator_topology)
qed

lemma hausdorff_cweak_operator_topology[simp]: \<open>Hausdorff_space cweak_operator_topology\<close>
proof (rule hausdorffI)
  fix A B :: \<open>'a \<Rightarrow>\<^sub>C\<^sub>L 'b\<close> assume \<open>A \<noteq> B\<close>
  then obtain y where \<open>A *\<^sub>V y \<noteq> B *\<^sub>V y\<close>
    by (meson cblinfun_eqI)
  then obtain x where \<open>x \<bullet>\<^sub>C (A *\<^sub>V y) \<noteq> x \<bullet>\<^sub>C (B *\<^sub>V y)\<close>
    using cinner_extensionality by blast
  then obtain U' V' where \<open>open U'\<close> \<open>open V'\<close> and inside: \<open>x \<bullet>\<^sub>C (A *\<^sub>V y) \<in> U'\<close> \<open>x \<bullet>\<^sub>C (B *\<^sub>V y) \<in> V'\<close> and disj: \<open>U' \<inter> V' = {}\<close>
    by (meson separation_t2)
  define U'' V'' where \<open>U'' = Pi\<^sub>E UNIV (\<lambda>i. if i=(x,y) then U' else UNIV)\<close> and \<open>V'' = Pi\<^sub>E UNIV (\<lambda>i. if i=(x,y) then V' else UNIV)\<close>
  from \<open>open U'\<close> \<open>open V'\<close>
  have \<open>open U''\<close> and \<open>open V''\<close>
    by (auto simp: U''_def V''_def open_fun_def intro!: product_topology_basis)
  define U V :: \<open>('a \<Rightarrow>\<^sub>C\<^sub>L 'b) set\<close> where \<open>U = (\<lambda>A (x, y). x \<bullet>\<^sub>C (A *\<^sub>V y)) -` U''\<close> and \<open>V = (\<lambda>a (x, y). x \<bullet>\<^sub>C (a *\<^sub>V y)) -` V''\<close>
  have openin: \<open>openin cweak_operator_topology U\<close> \<open>openin cweak_operator_topology V\<close>
    using U_def V_def \<open>open U''\<close> \<open>open V''\<close> openin_cweak_operator_topology by blast+
  have \<open>A \<in> U\<close> \<open>B \<in> V\<close>
    using inside by (auto simp: U_def V_def U''_def V''_def)
  have \<open>U \<inter> V = {}\<close>
    using disj apply (auto simp: U_def V_def U''_def V''_def PiE_def Pi_iff)
    by (metis disjoint_iff)
  show \<open>\<exists>U V. openin cweak_operator_topology U \<and> openin cweak_operator_topology V \<and> A \<in> U \<and> B \<in> V \<and> U \<inter> V = {}\<close>
    using \<open>A \<in> U\<close> \<open>B \<in> V\<close> \<open>U \<inter> V = {}\<close> openin by blast
qed

lemma hermitian_limit_hermitian_wot:
  assumes \<open>F \<noteq> bot\<close>
  assumes herm: \<open>\<And>i. (a i)* = a i\<close>
  assumes lim: \<open>limitin cweak_operator_topology a A F\<close>
  shows \<open>A* = A\<close>
  using _ _ \<open>F \<noteq> bot\<close> hausdorff_cweak_operator_topology
  apply (rule limitin_Hausdorff_unique)
  using lim apply (rule limitin_adj_wot)
  unfolding herm by (fact lim)

lemma wot_weaker_than_sot_openin:
  \<open>openin cweak_operator_topology x \<Longrightarrow> openin cstrong_operator_topology x\<close>
  using wot_weaker_than_sot unfolding continuous_map_def by auto

lemma wot_weaker_than_sot_limitin: \<open>limitin cweak_operator_topology a A F\<close> if \<open>limitin cstrong_operator_topology a A F\<close>
  using that unfolding filterlim_cweak_operator_topology[symmetric] filterlim_cstrong_operator_topology[symmetric]
  apply (rule filterlim_mono)
   apply (rule nhdsin_mono)
  by (auto simp: wot_weaker_than_sot_openin)

(* Logically belongs in Strong_Operator_Topology, but we use hermitian_tendsto_hermitian_wot in the proof. *)
lemma hermitian_limit_hermitian_sot:
  assumes \<open>F \<noteq> bot\<close>
  assumes \<open>\<And>i. (a i)* = a i\<close>
  assumes \<open>limitin cstrong_operator_topology a A F\<close>
  shows \<open>A* = A\<close>
  using assms(1,2) apply (rule hermitian_limit_hermitian_wot[where a=a and F=F])
  using assms(3) by (rule wot_weaker_than_sot_limitin)

lemma hermitian_sum_hermitian_sot:
  assumes herm: \<open>\<And>i. (a i)* = a i\<close>
  assumes sum: \<open>has_sum_in cstrong_operator_topology a X A\<close>
  shows \<open>A* = A\<close>
proof -
  from herm have herm_sum: \<open>(sum a F)* = sum a F\<close> for F
    by (simp add: sum_adj)
  show ?thesis
    using _ herm_sum sum[unfolded has_sum_in_def]
    apply (rule hermitian_limit_hermitian_sot)
    by simp
qed

lemma wot_is_norm_topology_findim[simp]:
  \<open>(cweak_operator_topology :: ('a::{cfinite_dim,chilbert_space} \<Rightarrow>\<^sub>C\<^sub>L 'b::{cfinite_dim,chilbert_space}) topology) = euclidean\<close>
proof -
  have \<open>continuous_map euclidean cweak_operator_topology id\<close>
    by (simp add: id_def cweak_operator_topology_weaker_than_euclidean)
  moreover have \<open>continuous_map cweak_operator_topology euclidean (id :: 'a \<Rightarrow>\<^sub>C\<^sub>L 'b \<Rightarrow> _)\<close>
  proof (rule continuous_map_iff_preserves_convergence)
    fix l and F :: \<open>('a \<Rightarrow>\<^sub>C\<^sub>L 'b) filter\<close>
    assume lim_wot: \<open>limitin cweak_operator_topology id l F\<close>
    obtain A :: \<open>'a set\<close> where \<open>is_onb A\<close>
      using is_onb_some_chilbert_basis by blast
    then have idA: \<open>id_cblinfun = (\<Sum>x\<in>A. selfbutter x)\<close>
      using butterflies_sum_id_finite by blast
    obtain B :: \<open>'b set\<close> where \<open>is_onb B\<close>
      using is_onb_some_chilbert_basis by blast
    then have idB: \<open>id_cblinfun = (\<Sum>x\<in>B. selfbutter x)\<close>
      using butterflies_sum_id_finite by blast
    from lim_wot have \<open>((\<lambda>x. b \<bullet>\<^sub>C (x *\<^sub>V a)) \<longlongrightarrow> b \<bullet>\<^sub>C (l *\<^sub>V a)) F\<close> for a b
      by (simp add: limitin_cweak_operator_topology)
    then have \<open>((\<lambda>x. (b \<bullet>\<^sub>C (x *\<^sub>V a)) *\<^sub>C butterfly b a) \<longlongrightarrow> (b \<bullet>\<^sub>C (l *\<^sub>V a)) *\<^sub>C butterfly b a) F\<close> for a b
      by (simp add: tendsto_scaleC)
    then have \<open>((\<lambda>x. selfbutter b o\<^sub>C\<^sub>L x o\<^sub>C\<^sub>L selfbutter a) \<longlongrightarrow> (selfbutter b o\<^sub>C\<^sub>L l o\<^sub>C\<^sub>L selfbutter a)) F\<close> for a b
      by (simp add: cblinfun_comp_butterfly)
    then have \<open>((\<lambda>x. \<Sum>b\<in>B. selfbutter b o\<^sub>C\<^sub>L x o\<^sub>C\<^sub>L selfbutter a) \<longlongrightarrow> (\<Sum>b\<in>B. selfbutter b o\<^sub>C\<^sub>L l o\<^sub>C\<^sub>L selfbutter a)) F\<close> for a
      by (rule tendsto_sum)
    then have \<open>((\<lambda>x. x o\<^sub>C\<^sub>L selfbutter a) \<longlongrightarrow> (l o\<^sub>C\<^sub>L selfbutter a)) F\<close> for a
      by (simp add: flip: cblinfun_compose_sum_left idB)
    then have \<open>((\<lambda>x. \<Sum>a\<in>A. x o\<^sub>C\<^sub>L selfbutter a) \<longlongrightarrow> (\<Sum>a\<in>A. l o\<^sub>C\<^sub>L selfbutter a)) F\<close>
      by (rule tendsto_sum)
    then have \<open>(id \<longlongrightarrow> l) F\<close>
      by (simp add: flip: cblinfun_compose_sum_right idA id_def)
    then show \<open>limitin euclidean id (id l) F\<close>
      by simp
  qed
  ultimately show ?thesis
    by (auto simp: topology_finer_continuous_id[symmetric] simp flip: openin_inject)
qed


lemma sot_is_norm_topology_fin_dim[simp]: 
  \<comment> \<open>Logically belongs in \<tt>\<open>Strong_Operator_Topology\<close> but the proof uses
      lemmas from here..\<close>
  \<open>(cstrong_operator_topology :: ('a::{cfinite_dim,chilbert_space} \<Rightarrow>\<^sub>C\<^sub>L 'b::{cfinite_dim,chilbert_space}) topology) = euclidean\<close>
proof -
  have 1: \<open>continuous_map euclidean cstrong_operator_topology (id :: 'a\<Rightarrow>\<^sub>C\<^sub>L'b \<Rightarrow> _)\<close>
    by (simp add: id_def cstrong_operator_topology_weaker_than_euclidean)
  have \<open>continuous_map cstrong_operator_topology cweak_operator_topology (id :: 'a\<Rightarrow>\<^sub>C\<^sub>L'b \<Rightarrow> _)\<close>
    by (metis eq_id_iff wot_weaker_than_sot)
  then have 2: \<open>continuous_map cstrong_operator_topology euclidean (id :: 'a\<Rightarrow>\<^sub>C\<^sub>L'b \<Rightarrow> _)\<close>
    by (simp only: wot_is_norm_topology_findim)
  from 1 2
  show ?thesis
    by (auto simp: topology_finer_continuous_id[symmetric] simp flip: openin_inject)
qed

lemma regular_space_wot: \<open>regular_space cweak_operator_topology\<close>
proof -
  have \<open>regular_space (product_topology (\<lambda>i::'b\<times>'a. euclidean :: complex topology) UNIV)\<close>
    by (simp add: regular_space_product_topology)
  then have \<open>regular_space (euclidean :: ('b\<times>'a \<Rightarrow> complex) topology)\<close>
    using euclidean_product_topology by metis
  then show ?thesis
    unfolding cweak_operator_topology_def
    by (rule_tac regular_space_pullback)
qed


instance cblinfun_wot :: (complex_normed_vector, complex_inner) t3_space
  apply intro_classes
  apply transfer
  using regular_space_wot
  by (auto simp add: regular_space_def disjnt_def)

instantiation cblinfun_wot :: (chilbert_space, chilbert_space) order begin
lift_definition less_eq_cblinfun_wot :: \<open>('a, 'b) cblinfun_wot \<Rightarrow> ('a, 'b) cblinfun_wot \<Rightarrow> bool\<close> is less_eq.
lift_definition less_cblinfun_wot :: \<open>('a, 'b) cblinfun_wot \<Rightarrow> ('a, 'b) cblinfun_wot \<Rightarrow> bool\<close> is less.
instance
  apply (intro_classes; transfer')
  by auto
end


instance cblinfun_wot :: (chilbert_space,chilbert_space) ordered_comm_monoid_add
proof
  fix a b c :: \<open>('a,'b) cblinfun_wot\<close>
  assume \<open>a \<le> b\<close>
  then show \<open>c + a \<le> c + b\<close>
    apply transfer'
    by simp
qed


lemma limitin_wot_add:
  assumes \<open>limitin cweak_operator_topology f a F\<close>
  assumes \<open>limitin cweak_operator_topology g b F\<close>
  shows \<open>limitin cweak_operator_topology (\<lambda>x. f x + g x) (a + b) F\<close>
proof -
  have \<open>LIM x F. (f x, g x) :> nhdsin cweak_operator_topology a \<times>\<^sub>F nhdsin cweak_operator_topology b\<close>
    apply (rule filterlim_Pair)
    using assms by (simp_all add: filterlim_cweak_operator_topology)
  then have \<open>LIM x F. case (f x, g x) of (x, y) \<Rightarrow> x + y :> nhdsin cweak_operator_topology (a + b)\<close>
    apply (rule filterlim_compose[rotated])
    by (rule cweak_operator_topology_plus_cont)
  then show ?thesis
    by (simp add: filterlim_cweak_operator_topology)
qed

lemma monotone_convergence_wot:
  \<comment> \<open>\<^cite>\<open>conway00operator\<close>, Proposition 43.1 (i), (ii), but translated to filters.\<close>
  fixes f :: \<open>'b \<Rightarrow> ('a \<Rightarrow>\<^sub>C\<^sub>L 'a::chilbert_space)\<close>
  assumes bounded: \<open>\<forall>\<^sub>F x in F. f x \<le> B\<close>
  assumes increasing: \<open>increasing_filter (filtermap f F)\<close>
  shows \<open>\<exists>L. limitin cweak_operator_topology f L F\<close>
proof -
  wlog nontrivial: \<open>F \<noteq> \<bottom>\<close>
    using negation by (auto intro!: limitin_trivial)
  wlog pos: \<open>\<forall>\<^sub>F x in F. f x \<ge> 0\<close> generalizing f B keeping bounded increasing nontrivial
  proof -
    from increasing
    have \<open>\<forall>\<^sub>F y in F. \<exists>L. limitin cweak_operator_topology f L F\<close>
      unfolding increasing_filter_def eventually_filtermap
    proof (rule eventually_mono)
      fix x0
      assume f_lower: \<open>\<forall>\<^sub>F x in F. f x0 \<le> f x\<close>
      define g where \<open>g x = f x - f x0\<close> for x
      from bounded
      have bounded_g: \<open>\<forall>\<^sub>F x in F. g x \<le> B - f x0\<close>
        apply (rule eventually_mono)
        by (simp add: g_def)
      from f_lower
      have pos_g: \<open>\<forall>\<^sub>F x in F. g x \<ge> 0\<close>
        apply (rule eventually_mono)
        by (simp add: g_def)
      from increasing
      have increasing_g: \<open>increasing_filter (filtermap g F)\<close>
        unfolding increasing_filter_def eventually_filtermap
        apply (rule eventually_mono)
        apply (erule eventually_mono)
        by (simp add: g_def[abs_def])
      obtain L where \<open>limitin cweak_operator_topology g L F\<close>
        apply atomize_elim
        using pos_g bounded_g increasing_g nontrivial by (rule hypothesis)
      then have \<open>limitin cweak_operator_topology (\<lambda>x. g x + f x0) (L + f x0) F\<close>
        apply (rule limitin_wot_add)
        by simp
      then have \<open>limitin cweak_operator_topology f (L + f x0) F\<close>
        by (auto intro!: simp: g_def[abs_def])
      then show \<open>\<exists>L. limitin cweak_operator_topology f L F\<close>
        by auto
    qed
    then show ?thesis
      by (simp add: nontrivial eventually_const)
  qed

  define surround where \<open>surround \<psi> a = \<psi> \<bullet>\<^sub>C (a *\<^sub>V \<psi>)\<close> for \<psi> :: 'a and a
  have mono_surround: \<open>mono (surround \<psi>)\<close> for \<psi>
    by (auto intro!: monoI simp: surround_def less_eq_cblinfun_def)
  obtain l' where  tendsto_l': \<open>((\<lambda>x. surround \<psi> (f x)) \<longlongrightarrow> l' \<psi>) F\<close> for \<psi>
  proof (atomize_elim, intro choice allI)
    fix \<psi> :: 'a
    from bounded
    have surround_bound: \<open>\<forall>\<^sub>F x in F. surround \<psi> (f x) \<le> surround \<psi> B\<close>
      unfolding surround_def
      apply (rule eventually_mono)
      by (simp add: less_eq_cblinfun_def)
    moreover have \<open>increasing_filter (filtermap (\<lambda>x. surround \<psi> (f x)) F)\<close>
      using increasing_filtermap[OF increasing mono_surround]
      by (simp add: filtermap_filtermap)
    ultimately obtain l' where \<open>((\<lambda>x. surround \<psi> (f x)) \<longlongrightarrow> l') F\<close>
      apply atomize_elim
      by (auto intro!: monotone_convergence_complex increasing mono_surround
          simp: eventually_filtermap)
    then show \<open>\<exists>l'. ((\<lambda>x. surround \<psi> (f x)) \<longlongrightarrow> l') F\<close>
      by auto
  qed
  define l where \<open>l \<phi> \<psi> = (l' (\<phi>+\<psi>) - l' (\<phi>-\<psi>) - \<i> * l' (\<phi> + \<i> *\<^sub>C \<psi>) + \<i> * l' (\<phi> - \<i> *\<^sub>C \<psi>)) / 4\<close> for \<phi> \<psi> :: 'a
  have polar: \<open>\<phi> \<bullet>\<^sub>C a \<psi> = (surround (\<phi>+\<psi>) a - surround (\<phi>-\<psi>) a - \<i> * surround (\<phi> + \<i> *\<^sub>C \<psi>) a + \<i> * surround (\<phi> - \<i> *\<^sub>C \<psi>) a) / 4\<close> for a :: \<open>'a \<Rightarrow>\<^sub>C\<^sub>L 'a\<close> and \<phi> \<psi>
    by (simp add: surround_def cblinfun.add_right cinner_add cblinfun.diff_right 
        cinner_diff cblinfun.scaleC_right ring_distribs)
  have tendsto_l: \<open>((\<lambda>x. \<phi> \<bullet>\<^sub>C f x \<psi>) \<longlongrightarrow> l \<phi> \<psi>) F\<close> for \<phi> \<psi>
    by (auto intro!: tendsto_divide tendsto_add tendsto_diff tendsto_l' simp: l_def polar)
  have l_bound: \<open>norm (l \<phi> \<psi>) \<le> norm B * norm \<phi> * norm \<psi>\<close> for \<phi> \<psi>
  proof -
    from bounded pos
    have \<open>\<forall>\<^sub>F x in F. norm (\<phi> \<bullet>\<^sub>C f x \<psi>) \<le> norm B * norm \<phi> * norm \<psi>\<close> for \<phi> \<psi>
    proof (rule eventually_elim2)
      fix x
      assume \<open>f x \<le> B\<close> and \<open>0 \<le> f x\<close>
      have \<open>cmod (\<phi> \<bullet>\<^sub>C (f x *\<^sub>V \<psi>)) \<le> norm \<phi> * norm (f x *\<^sub>V \<psi>)\<close>
        using complex_inner_class.Cauchy_Schwarz_ineq2 by blast
      also have \<open>\<dots> \<le> norm \<phi> * (norm (f x) * norm \<psi>)\<close>
        by (simp add: mult_left_mono norm_cblinfun)
      also from \<open>f x \<le> B\<close> \<open>0 \<le> f x\<close>
      have \<open>\<dots> \<le> norm \<phi> * (norm B * norm \<psi>)\<close>
        by (auto intro!: mult_left_mono mult_right_mono norm_cblinfun_mono simp: )
      also have \<open>\<dots> = norm B * norm \<phi> * norm \<psi>\<close>
        by simp
      finally show \<open>norm (\<phi> \<bullet>\<^sub>C f x \<psi>) \<le> norm B * norm \<phi> * norm \<psi>\<close>
        by -
    qed
    moreover from tendsto_l
    have \<open>((\<lambda>x. norm (\<phi> \<bullet>\<^sub>C f x \<psi>)) \<longlongrightarrow> norm (l \<phi> \<psi>)) F\<close> for \<phi> \<psi>
      using tendsto_norm by blast
    ultimately show ?thesis
      using nontrivial tendsto_upperbound by blast
  qed
  have \<open>bounded_sesquilinear l\<close>
  proof (rule bounded_sesquilinear.intro)
    fix \<phi> \<phi>' \<psi> \<psi>' and r :: complex
    from tendsto_l have \<open>((\<lambda>x. \<phi> \<bullet>\<^sub>C f x \<psi> + \<phi> \<bullet>\<^sub>C f x \<psi>') \<longlongrightarrow> l \<phi> \<psi> + l \<phi> \<psi>') F\<close>
      by (simp add: tendsto_add)
    moreover from tendsto_l have \<open>((\<lambda>x. \<phi> \<bullet>\<^sub>C f x \<psi> + \<phi> \<bullet>\<^sub>C f x \<psi>') \<longlongrightarrow> l \<phi> (\<psi> + \<psi>')) F\<close>
      by (simp flip: cinner_add_right cblinfun.add_right)
    ultimately show \<open>l \<phi> (\<psi> + \<psi>') = l \<phi> \<psi> + l \<phi> \<psi>'\<close>
      by (rule tendsto_unique[OF nontrivial, rotated])
    from tendsto_l have \<open>((\<lambda>x. \<phi> \<bullet>\<^sub>C f x \<psi> + \<phi>' \<bullet>\<^sub>C f x \<psi>) \<longlongrightarrow> l \<phi> \<psi> + l \<phi>' \<psi>) F\<close>
      by (simp add: tendsto_add)
    moreover from tendsto_l have \<open>((\<lambda>x. \<phi> \<bullet>\<^sub>C f x \<psi> + \<phi>' \<bullet>\<^sub>C f x \<psi>) \<longlongrightarrow> l (\<phi> + \<phi>') \<psi>) F\<close>
      by (simp flip: cinner_add_left cblinfun.add_left)
    ultimately show \<open>l (\<phi> + \<phi>') \<psi> = l \<phi> \<psi> + l \<phi>' \<psi>\<close>
      by (rule tendsto_unique[OF nontrivial, rotated])
    from tendsto_l have \<open>((\<lambda>x. r *\<^sub>C (\<phi> \<bullet>\<^sub>C f x \<psi>)) \<longlongrightarrow> r *\<^sub>C l \<phi> \<psi>) F\<close>
      using tendsto_scaleC by blast
    moreover from tendsto_l have \<open>((\<lambda>x. r *\<^sub>C (\<phi> \<bullet>\<^sub>C f x \<psi>)) \<longlongrightarrow> l \<phi> (r *\<^sub>C \<psi>)) F\<close>
      by (simp flip: cinner_scaleC_right cblinfun.scaleC_right)
    ultimately show \<open>l \<phi> (r *\<^sub>C \<psi>) = r *\<^sub>C l \<phi> \<psi>\<close>
      by (rule tendsto_unique[OF nontrivial, rotated])
    from tendsto_l have \<open>((\<lambda>x. cnj r *\<^sub>C (\<phi> \<bullet>\<^sub>C f x \<psi>)) \<longlongrightarrow> cnj r *\<^sub>C l \<phi> \<psi>) F\<close>
      using tendsto_scaleC by blast
    moreover from tendsto_l have \<open>((\<lambda>x. cnj r *\<^sub>C (\<phi> \<bullet>\<^sub>C f x \<psi>)) \<longlongrightarrow> l (r *\<^sub>C \<phi>) \<psi>) F\<close>
      by (simp flip: cinner_scaleC_left cblinfun.scaleC_left)
    ultimately show \<open>l (r *\<^sub>C \<phi>) \<psi> = cnj r *\<^sub>C l \<phi> \<psi>\<close>
      by (rule tendsto_unique[OF nontrivial, rotated])
    show \<open>\<exists>K. \<forall>a b. cmod (l a b) \<le> norm a * norm b * K\<close>
      using l_bound by (auto intro!: exI[of _ \<open>norm B\<close>] simp: mult_ac)
  qed
  define L where \<open>L = (the_riesz_rep_sesqui l)*\<close>
  then have \<open>\<phi> \<bullet>\<^sub>C L \<psi> = l \<phi> \<psi>\<close> for \<phi> \<psi>
    by (auto intro!: \<open>bounded_sesquilinear l\<close> the_riesz_rep_sesqui_apply simp: cinner_adj_right)
  with tendsto_l have \<open>((\<lambda>x. \<phi> \<bullet>\<^sub>C f x \<psi>) \<longlongrightarrow> \<phi> \<bullet>\<^sub>C L \<psi>) F\<close> for \<phi> \<psi>
    by simp
  then have \<open>limitin cweak_operator_topology f L F\<close>
    by (simp add: limitin_cweak_operator_topology)
  then show ?thesis
    by auto
qed

lemma summable_wot_boundedI:
  fixes f :: \<open>'b \<Rightarrow> ('a \<Rightarrow>\<^sub>C\<^sub>L 'a::chilbert_space)\<close>
  assumes bounded: \<open>\<And>F. finite F \<Longrightarrow> F \<subseteq> X \<Longrightarrow> sum f F \<le> B\<close>
  assumes pos: \<open>\<And>x. x \<in> X \<Longrightarrow> f x \<ge> 0\<close>
  shows \<open>summable_on_in cweak_operator_topology f X\<close>
proof -
  from pos have incr: \<open>increasing_filter (filtermap (sum f) (finite_subsets_at_top X))\<close>
    by (auto intro!: increasing_filtermap[where X=\<open>{F. finite F \<and> F \<subseteq> X}\<close>] mono_onI sum_mono2)
  show ?thesis
    apply (simp add: summable_on_in_def has_sum_in_def) 
    by (safe intro!: bounded incr monotone_convergence_wot[where B=B] eventually_finite_subsets_at_top_weakI)
qed



lemma summable_wot_boundedI':
  fixes f :: \<open>'b \<Rightarrow> ('a::chilbert_space, 'a) cblinfun_wot\<close>
  assumes bounded: \<open>\<And>F. finite F \<Longrightarrow> F \<subseteq> X \<Longrightarrow> sum f F \<le> B\<close>
  assumes pos: \<open>\<And>x. x \<in> X \<Longrightarrow> f x \<ge> 0\<close>
  shows \<open>f summable_on X\<close>
  apply (subst summable_on_euclidean_eq[symmetric])
  using assms
  apply (transfer' fixing: X)
  apply (rule summable_wot_boundedI)
  by auto

lemma has_sum_mono_neutral_wot:
  fixes f :: "'a \<Rightarrow> ('b::chilbert_space \<Rightarrow>\<^sub>C\<^sub>L 'b)"
  assumes \<open>has_sum_in cweak_operator_topology f A a\<close> and "has_sum_in cweak_operator_topology g B b"
  assumes \<open>\<And>x. x \<in> A\<inter>B \<Longrightarrow> f x \<le> g x\<close>
  assumes \<open>\<And>x. x \<in> A-B \<Longrightarrow> f x \<le> 0\<close>
  assumes \<open>\<And>x. x \<in> B-A \<Longrightarrow> g x \<ge> 0\<close>
  shows "a \<le> b"
proof -
  have \<psi>_eq: \<open>\<psi> \<bullet>\<^sub>C a \<psi> \<le> \<psi> \<bullet>\<^sub>C b \<psi>\<close> for \<psi>
  proof -
    from assms(1)
    have sumA: \<open>((\<lambda>x. \<psi> \<bullet>\<^sub>C f x \<psi>) has_sum \<psi> \<bullet>\<^sub>C a \<psi>) A\<close>
      by (simp add: has_sum_in_def has_sum_def limitin_cweak_operator_topology
          cblinfun.sum_left cinner_sum_right)
    from assms(2)
    have sumB: \<open>((\<lambda>x. \<psi> \<bullet>\<^sub>C g x \<psi>) has_sum \<psi> \<bullet>\<^sub>C b \<psi>) B\<close>
      by (simp add: has_sum_in_def has_sum_def limitin_cweak_operator_topology
          cblinfun.sum_left cinner_sum_right)
    from sumA sumB
    show ?thesis
      apply (rule has_sum_mono_neutral_complex)
      using assms(3-5)
      by (auto simp: less_eq_cblinfun_def)
  qed
  then show \<open>a \<le> b\<close>
    by (simp add: less_eq_cblinfun_def)
qed


lemma has_sum_mono_wot:
  fixes f :: "'a \<Rightarrow> ('b::chilbert_space \<Rightarrow>\<^sub>C\<^sub>L 'b)"
  assumes "has_sum_in cweak_operator_topology f A x" and "has_sum_in cweak_operator_topology g A y"
  assumes \<open>\<And>x. x \<in> A \<Longrightarrow> f x \<le> g x\<close>
  shows "x \<le> y"
  using assms has_sum_mono_neutral_wot by force



lemma infsum_mono_neutral_wot:
  fixes f :: "'a \<Rightarrow> ('b::chilbert_space \<Rightarrow>\<^sub>C\<^sub>L 'b)"
  assumes "summable_on_in cweak_operator_topology f A" and "summable_on_in cweak_operator_topology g B"
  assumes \<open>\<And>x. x \<in> A\<inter>B \<Longrightarrow> f x \<le> g x\<close>
  assumes \<open>\<And>x. x \<in> A-B \<Longrightarrow> f x \<le> 0\<close>
  assumes \<open>\<And>x. x \<in> B-A \<Longrightarrow> g x \<ge> 0\<close>
  shows "infsum_in cweak_operator_topology f A \<le> infsum_in cweak_operator_topology g B"
  using assms
  by (metis (mono_tags, lifting) has_sum_in_infsum_in has_sum_mono_neutral_wot hausdorff_cweak_operator_topology)


lemma has_sum_on_wot_transfer[transfer_rule]:
  includes lifting_syntax
  shows \<open>(((=) ===> cr_cblinfun_wot) ===> (=) ===> cr_cblinfun_wot ===> (\<longleftrightarrow>)) (has_sum_in cweak_operator_topology) HAS_SUM\<close>
  unfolding has_sum_euclidean_iff[abs_def, symmetric] has_sum_in_def[abs_def]
  by transfer_prover

lemma summable_on_wot_transfer[transfer_rule]:
  includes lifting_syntax
  shows \<open>(((=) ===> cr_cblinfun_wot) ===> (=) ===> (\<longleftrightarrow>)) (summable_on_in cweak_operator_topology) (summable_on)\<close>
  apply (auto intro!: simp: summable_on_def[abs_def] summable_on_in_def[abs_def])
  by transfer_prover

lemma Abs_cblinfun_wot_transfer[transfer_rule]:
  includes lifting_syntax
  shows \<open>((=) ===> cr_cblinfun_wot) id Abs_cblinfun_wot\<close>
  by (auto intro!: rel_funI simp: cr_cblinfun_wot_def Abs_cblinfun_wot_inverse)

lemma infsum_mono_neutral_wot':
  fixes f :: "'a \<Rightarrow> ('b::chilbert_space, 'b) cblinfun_wot"
  assumes "f summable_on A" and "g summable_on B"
  assumes \<open>\<And>x. x \<in> A\<inter>B \<Longrightarrow> f x \<le> g x\<close>
  assumes \<open>\<And>x. x \<in> A-B \<Longrightarrow> f x \<le> 0\<close>
  assumes \<open>\<And>x. x \<in> B-A \<Longrightarrow> g x \<ge> 0\<close>
  shows "infsum f A \<le> infsum g B"
  unfolding infsum_euclidean_eq[symmetric]
  using assms
  apply (transfer' fixing: A B)
  apply (rule infsum_mono_neutral_wot)
  by auto

lemma infsum_nonneg_wot':
  fixes f :: "'a \<Rightarrow> ('c::chilbert_space,'c) cblinfun_wot"
  assumes "\<And>x. x \<in> M \<Longrightarrow> 0 \<le> f x"
  shows "infsum f M \<ge> 0"
proof (cases \<open>f summable_on M\<close>)
  case True
  show ?thesis
    apply (subst infsum_0[symmetric, OF refl])
    apply (rule infsum_mono_neutral_wot'[where A=M and B=M])
    using assms True by auto
next
  case False
  then have \<open>infsum f M = 0\<close>
    using infsum_not_exists by blast
  then show ?thesis
    by simp
qed


lemma summable_on_Sigma_wotI:
  fixes f :: \<open>'a \<times> 'b \<Rightarrow> ('c::chilbert_space,'c) cblinfun_wot\<close>
  assumes \<open>\<And>x y. x \<in> A \<Longrightarrow> y \<in> B x \<Longrightarrow> f (x,y) \<ge> 0\<close>
  assumes summableA: \<open>(\<lambda>x. \<Sum>\<^sub>\<infinity>y\<in>B x. f (x,y)) summable_on A\<close>
  assumes summableB: \<open>\<And>x. x\<in>A \<Longrightarrow> (\<lambda>y. f (x, y)) summable_on (B x)\<close>
  shows \<open>f summable_on Sigma A B\<close>
proof (rule summable_wot_boundedI')
  show \<open>f x \<ge> 0\<close> if \<open>x \<in> Sigma A B\<close> for x
    using assms that by blast
  show \<open>sum f F \<le> (\<Sum>\<^sub>\<infinity>x\<in>A. \<Sum>\<^sub>\<infinity>y\<in>B x. f (x,y))\<close> if \<open>finite F\<close> and \<open>F \<subseteq> Sigma A B\<close> for F
  proof -
    define FA where \<open>FA = fst ` F\<close>
    define FB where \<open>FB x = {y. (x,y)\<in>F}\<close> for x
    have F_FAB: \<open>F = Sigma FA FB\<close>
      by (auto simp: FA_def FB_def image_iff Bex_def)
    have [simp]: \<open>finite FA\<close> \<open>finite (FB x)\<close> for x
      using \<open>finite F\<close> by (auto intro!: finite_inverse_image injI simp: FA_def FB_def)
    have FA_A: \<open>FA \<subseteq> A\<close>
      using FA_def that(2) by auto
    have FB_B: \<open>FB x \<subseteq> B x\<close> if \<open>x \<in> A\<close> for x
      using FB_def \<open>F \<subseteq> Sigma A B\<close> by auto
    have \<open>sum f F = (\<Sum>x\<in>FA. \<Sum>y\<in>FB x. f (x,y))\<close>
      apply (subst sum.Sigma)
      by (auto simp: F_FAB)
    also have \<open>\<dots> = (\<Sum>x\<in>FA. \<Sum>\<^sub>\<infinity>y\<in>FB x. f (x,y))\<close>
      by fastforce
    also have \<open>\<dots> \<le> (\<Sum>x\<in>FA. \<Sum>\<^sub>\<infinity>y\<in>B x. f (x,y))\<close>
      apply (rule sum_mono)
      apply (rule infsum_mono_neutral_wot')
      using FA_A FB_B assms by auto 
    also have \<open>\<dots> = (\<Sum>\<^sub>\<infinity>x\<in>FA. \<Sum>\<^sub>\<infinity>y\<in>B x. f (x,y))\<close>
      by fastforce
    also have \<open>\<dots> \<le> (\<Sum>\<^sub>\<infinity>x\<in>A. \<Sum>\<^sub>\<infinity>y\<in>B x. f (x,y))\<close>
      apply (rule infsum_mono_neutral_wot')
      using FA_A assms by (auto intro!: infsum_nonneg_wot')
    finally show \<open>sum f F \<le> (\<Sum>\<^sub>\<infinity>x\<in>A. \<Sum>\<^sub>\<infinity>y\<in>B x. f (x,y))\<close>
      by -
  qed
qed

lift_definition compose_wot :: \<open>('b::complex_inner,'c::complex_inner) cblinfun_wot \<Rightarrow> ('a::complex_normed_vector,'b) cblinfun_wot \<Rightarrow> ('a,'c) cblinfun_wot\<close> is
  cblinfun_compose.

lift_definition adj_wot :: \<open>('a::chilbert_space, 'b::complex_inner) cblinfun_wot \<Rightarrow> ('b, 'a) cblinfun_wot\<close> is adj.

lemma infsum_wot_is_Sup:
  fixes f :: \<open>'b \<Rightarrow> ('a \<Rightarrow>\<^sub>C\<^sub>L 'a::chilbert_space)\<close>
  assumes summable: \<open>summable_on_in cweak_operator_topology f X\<close>
    \<comment> \<open>See also @{thm [source] summable_wot_boundedI} for proving this.\<close>
  assumes pos: \<open>\<And>x. x \<in> X \<Longrightarrow> f x \<ge> 0\<close>
  defines \<open>S \<equiv> infsum_in cweak_operator_topology f X\<close>
  shows \<open>is_Sup ((\<lambda>F. \<Sum>x\<in>F. f x) ` {F. finite F \<and> F \<subseteq> X}) S\<close>
proof (rule is_SupI)
  have has_sum: \<open>has_sum_in cweak_operator_topology f X S\<close>
    unfolding S_def
    apply (rule has_sum_in_infsum_in)
    using assms by auto
  show \<open>s \<le> S\<close> if \<open>s \<in> ((\<lambda>F. \<Sum>x\<in>F. f x) ` {F. finite F \<and> F \<subseteq> X})\<close> for s
  proof -
    from that obtain F where [simp]: \<open>finite F\<close> and \<open>F \<subseteq> X\<close> and s_def: \<open>s = (\<Sum>x\<in>F. f x)\<close>
      by auto
    show ?thesis
    proof (rule has_sum_mono_neutral_wot)
      show \<open>has_sum_in cweak_operator_topology f F s\<close>
        by (auto intro!: has_sum_in_finite simp: s_def)
      show \<open>has_sum_in cweak_operator_topology f X S\<close>
        by (fact has_sum)
      show \<open>f x \<le> f x\<close> for x
        by simp
      show \<open>f x \<le> 0\<close> if \<open>x \<in> F - X\<close> for x
        using \<open>F \<subseteq> X\<close> that by auto
      show \<open>f x \<ge> 0\<close> if \<open>x \<in> X - F\<close> for x
        using that pos by auto
    qed
  qed
  show \<open>S \<le> y\<close>
    if y_bound: \<open>\<And>x. x \<in> ((\<lambda>F. \<Sum>x\<in>F. f x) ` {F. finite F \<and> F \<subseteq> X}) \<Longrightarrow> x \<le> y\<close> for y
  proof (rule cblinfun_leI, rename_tac \<psi>)
    fix \<psi> :: 'a
    define g where \<open>g x = \<psi> \<bullet>\<^sub>C Rep_cblinfun_wot x \<psi>\<close> for x
    from has_sum have lim: \<open>((\<lambda>i. \<psi> \<bullet>\<^sub>C ((\<Sum>x\<in>i. f x) *\<^sub>V \<psi>)) \<longlongrightarrow> \<psi> \<bullet>\<^sub>C (S *\<^sub>V \<psi>)) (finite_subsets_at_top X)\<close>
      by (simp add: has_sum_in_def limitin_cweak_operator_topology)
    have bound: \<open>\<psi> \<bullet>\<^sub>C (\<Sum>x\<in>F. f x) \<psi> \<le> \<psi> \<bullet>\<^sub>C y \<psi>\<close> if \<open>finite F\<close> \<open>F \<subseteq> X\<close> for F
      using y_bound less_eq_cblinfun_def that(1) that(2) by fastforce
    show \<open>\<psi> \<bullet>\<^sub>C (S *\<^sub>V \<psi>) \<le> \<psi> \<bullet>\<^sub>C y \<psi>\<close>
      using finite_subsets_at_top_neq_bot tendsto_const lim apply (rule tendsto_le_complex)
      using bound by (auto intro!: eventually_finite_subsets_at_top_weakI)
  qed
qed

lemma has_sum_in_cweak_operator_topology_pointwise:
  \<open>has_sum_in cweak_operator_topology f X s \<longleftrightarrow> (\<forall>\<psi> \<phi>. ((\<lambda>x. \<psi> \<bullet>\<^sub>C f x \<phi>) has_sum \<psi> \<bullet>\<^sub>C s \<phi>) X)\<close>
  by (simp add: has_sum_in_def has_sum_def limitin_cweak_operator_topology
      cblinfun.sum_left cinner_sum_right)

lemma summable_wot_bdd_above:
  fixes f :: \<open>'b \<Rightarrow> ('a \<Rightarrow>\<^sub>C\<^sub>L 'a::chilbert_space)\<close>
  assumes summable: \<open>summable_on_in cweak_operator_topology f X\<close>
    \<comment> \<open>See also @{thm [source] summable_wot_boundedI} for proving this.\<close>
  assumes pos: \<open>\<And>x. x \<in> X \<Longrightarrow> f x \<ge> 0\<close>
  shows \<open>bdd_above (sum f ` {F. finite F \<and> F \<subseteq> X})\<close>
  using infsum_wot_is_Sup[OF assms]
  by (auto intro!: simp: is_Sup_def bdd_above_def)

lemma summable_on_in_cweak_operator_topology_pointwise:
  assumes \<open>summable_on_in cweak_operator_topology f X\<close>
  shows \<open>(\<lambda>x. a \<bullet>\<^sub>C f x b) summable_on X\<close>
  using assms
  by (auto simp: summable_on_in_def summable_on_def has_sum_in_cweak_operator_topology_pointwise)

lemma infsum_in_cweak_operator_topology_pointwise:
  assumes \<open>summable_on_in cweak_operator_topology f X\<close>
  shows \<open>a \<bullet>\<^sub>C (infsum_in cweak_operator_topology f X) b = (\<Sum>\<^sub>\<infinity>x\<in>X. a \<bullet>\<^sub>C f x b)\<close>
  by (metis (mono_tags, lifting) assms has_sum_in_cweak_operator_topology_pointwise has_sum_in_infsum_in hausdorff_cweak_operator_topology infsumI)

instance cblinfun_wot :: (complex_normed_vector, complex_inner) topological_ab_group_add
  by intro_classes

lemma has_sum_in_wot_compose_left:
  fixes f :: \<open>'c \<Rightarrow> 'a::complex_normed_vector \<Rightarrow>\<^sub>C\<^sub>L 'b::chilbert_space\<close>
  assumes \<open>has_sum_in cweak_operator_topology f X s\<close>
  shows \<open>has_sum_in cweak_operator_topology (\<lambda>x. a o\<^sub>C\<^sub>L f x) X (a o\<^sub>C\<^sub>L s)\<close>
proof (rule has_sum_in_cweak_operator_topology_pointwise[THEN iffD2], intro allI, rename_tac g h)
  fix g h
  from assms have \<open>((\<lambda>x. (a*) g \<bullet>\<^sub>C f x h) has_sum (a*) g \<bullet>\<^sub>C s h) X\<close>
    by (metis has_sum_in_cweak_operator_topology_pointwise)
  then show \<open>((\<lambda>x. g \<bullet>\<^sub>C (a o\<^sub>C\<^sub>L f x) h) has_sum g \<bullet>\<^sub>C (a o\<^sub>C\<^sub>L s) h) X\<close>
    by (metis (no_types, lifting) cblinfun_apply_cblinfun_compose cinner_adj_left has_sum_cong)
qed

lemma has_sum_in_wot_compose_right:
  fixes f :: \<open>'c \<Rightarrow> 'a::complex_normed_vector \<Rightarrow>\<^sub>C\<^sub>L 'b::complex_inner\<close>
  assumes \<open>has_sum_in cweak_operator_topology f X s\<close>
  shows \<open>has_sum_in cweak_operator_topology (\<lambda>x. f x o\<^sub>C\<^sub>L a) X (s o\<^sub>C\<^sub>L a)\<close>
proof (rule has_sum_in_cweak_operator_topology_pointwise[THEN iffD2], intro allI, rename_tac g h)
  fix g h
  from assms have \<open>((\<lambda>x. g \<bullet>\<^sub>C f x (a h)) has_sum g \<bullet>\<^sub>C s (a h)) X\<close>
    by (metis has_sum_in_cweak_operator_topology_pointwise)
  then show \<open>((\<lambda>x. g \<bullet>\<^sub>C (f x o\<^sub>C\<^sub>L a) h) has_sum g \<bullet>\<^sub>C (s o\<^sub>C\<^sub>L a) h) X\<close>
    by simp
qed



lemma summable_on_in_wot_compose_left:
  fixes f :: \<open>'c \<Rightarrow> 'a::complex_normed_vector \<Rightarrow>\<^sub>C\<^sub>L 'b::chilbert_space\<close>
  assumes \<open>summable_on_in cweak_operator_topology f X\<close>
  shows \<open>summable_on_in cweak_operator_topology (\<lambda>x. a o\<^sub>C\<^sub>L f x) X\<close>
  using has_sum_in_wot_compose_left assms
  by (fastforce simp: summable_on_in_def)

lemma summable_on_in_wot_compose_right:
  assumes \<open>summable_on_in cweak_operator_topology f X\<close>
  shows \<open>summable_on_in cweak_operator_topology (\<lambda>x. f x o\<^sub>C\<^sub>L a) X\<close>
  using has_sum_in_wot_compose_right assms
  by (fastforce simp: summable_on_in_def)


lemma infsum_in_wot_compose_left:
  fixes f :: \<open>'c \<Rightarrow> 'a::complex_normed_vector \<Rightarrow>\<^sub>C\<^sub>L 'b::chilbert_space\<close>
  assumes \<open>summable_on_in cweak_operator_topology f X\<close>
  shows \<open>infsum_in cweak_operator_topology (\<lambda>x. a o\<^sub>C\<^sub>L f x) X = a o\<^sub>C\<^sub>L (infsum_in cweak_operator_topology f X)\<close>
  by (metis (mono_tags, lifting) assms has_sum_in_infsum_in has_sum_in_unique hausdorff_cweak_operator_topology
      has_sum_in_wot_compose_left summable_on_in_wot_compose_left)

lemma infsum_in_wot_compose_right:
  fixes f :: \<open>'c \<Rightarrow> 'a::complex_normed_vector \<Rightarrow>\<^sub>C\<^sub>L 'b::complex_inner\<close>
  assumes \<open>summable_on_in cweak_operator_topology f X\<close>
  shows \<open>infsum_in cweak_operator_topology (\<lambda>x. f x o\<^sub>C\<^sub>L a) X = (infsum_in cweak_operator_topology f X) o\<^sub>C\<^sub>L a\<close>
  by (metis (mono_tags, lifting) assms has_sum_in_infsum_in has_sum_in_unique hausdorff_cweak_operator_topology
      has_sum_in_wot_compose_right summable_on_in_wot_compose_right)


lemma infsum_wot_boundedI:
  fixes f :: \<open>'b \<Rightarrow> ('a \<Rightarrow>\<^sub>C\<^sub>L 'a::chilbert_space)\<close>
  assumes bounded: \<open>\<And>F. finite F \<Longrightarrow> F \<subseteq> X \<Longrightarrow> sum f F \<le> B\<close>
  assumes pos: \<open>\<And>x. x \<in> X \<Longrightarrow> f x \<ge> 0\<close>
  shows \<open>infsum_in cweak_operator_topology f X \<le> B\<close>
proof (rule less_eq_cblinfunI)
  fix h
  have summ: \<open>summable_on_in cweak_operator_topology f X\<close>
    using assms by (rule summable_wot_boundedI)
  then have \<open>h \<bullet>\<^sub>C (infsum_in cweak_operator_topology f X *\<^sub>V h) = (\<Sum>\<^sub>\<infinity>x\<in>X. h \<bullet>\<^sub>C (f x *\<^sub>V h))\<close>
    by (rule infsum_in_cweak_operator_topology_pointwise)
  also have \<open>\<dots> \<le> h \<bullet>\<^sub>C B h\<close>
  proof (rule less_eq_complexI)
    from summ have summ': \<open>(\<lambda>x. h \<bullet>\<^sub>C (f x *\<^sub>V h)) summable_on X\<close>
      by (auto intro!: summable_on_in_cweak_operator_topology_pointwise)
    have *: \<open>(\<Sum>x\<in>F. h \<bullet>\<^sub>C (f x *\<^sub>V h)) \<le> h \<bullet>\<^sub>C B h\<close> if \<open>finite F\<close> and \<open>F \<subseteq> X\<close> for F
      using that bounded
      by (simp add: less_eq_cblinfun_def flip: cinner_sum_right cblinfun.sum_left)
    show \<open>Im (\<Sum>\<^sub>\<infinity>x\<in>X. h \<bullet>\<^sub>C (f x *\<^sub>V h)) = Im (h \<bullet>\<^sub>C (B *\<^sub>V h))\<close>
    proof -
      from *[of \<open>{}\<close>] have \<open>h \<bullet>\<^sub>C B h \<ge> 0\<close>
        by simp
      then have \<open>Im (h \<bullet>\<^sub>C B h) = 0\<close>
        using comp_Im_same zero_complex.sel(2) by presburger
      moreover then have \<open>Im (h \<bullet>\<^sub>C (f x *\<^sub>V h)) = 0\<close> if \<open>x \<in> X\<close> for x
        using *[of \<open>{x}\<close>] that 
        by (simp add: less_eq_complex_def)
      ultimately show \<open>Im (\<Sum>\<^sub>\<infinity>x\<in>X. h \<bullet>\<^sub>C (f x *\<^sub>V h)) = Im (h \<bullet>\<^sub>C (B *\<^sub>V h))\<close>
        by (auto intro!: infsum_0 simp: summ' simp flip: infsum_Im)
    qed
    show \<open>Re (\<Sum>\<^sub>\<infinity>x\<in>X. h \<bullet>\<^sub>C (f x *\<^sub>V h)) \<le> Re (h \<bullet>\<^sub>C (B *\<^sub>V h))\<close>
      apply (auto intro!: summable_on_Re infsum_le_finite_sums simp: summ' simp flip: infsum_Re)
      using summ'
      by (metis "*" Re_sum less_eq_complex_def)
  qed
  finally show \<open>h \<bullet>\<^sub>C (infsum_in cweak_operator_topology f X *\<^sub>V h) \<le> h \<bullet>\<^sub>C (B *\<^sub>V h)\<close>
    by -
qed



end
