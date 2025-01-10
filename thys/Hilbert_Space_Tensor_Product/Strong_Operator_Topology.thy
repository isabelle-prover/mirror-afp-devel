section \<open>\<open>Strong_Operator_Topology\<close> -- Strong operator topology on complex bounded operators\<close>

theory Strong_Operator_Topology
  imports Misc_Tensor_Product_BO
begin

(* declare no_leading_Cons[rule del, simp del, iff] *)


unbundle cblinfun_notation

typedef (overloaded) ('a,'b) cblinfun_sot = \<open>UNIV :: ('a::complex_normed_vector \<Rightarrow>\<^sub>C\<^sub>L 'b::complex_normed_vector) set\<close> ..
setup_lifting type_definition_cblinfun_sot

instantiation cblinfun_sot :: (complex_normed_vector, complex_normed_vector) complex_vector begin
lift_definition scaleC_cblinfun_sot :: \<open>complex \<Rightarrow> ('a, 'b) cblinfun_sot \<Rightarrow> ('a, 'b) cblinfun_sot\<close> 
  is \<open>scaleC\<close> .
lift_definition uminus_cblinfun_sot :: \<open>('a, 'b) cblinfun_sot \<Rightarrow> ('a, 'b) cblinfun_sot\<close> is uminus .
lift_definition zero_cblinfun_sot :: \<open>('a, 'b) cblinfun_sot\<close> is 0 .
lift_definition minus_cblinfun_sot :: \<open>('a, 'b) cblinfun_sot \<Rightarrow> ('a, 'b) cblinfun_sot \<Rightarrow> ('a, 'b) cblinfun_sot\<close> is minus .
lift_definition plus_cblinfun_sot :: \<open>('a, 'b) cblinfun_sot \<Rightarrow> ('a, 'b) cblinfun_sot \<Rightarrow> ('a, 'b) cblinfun_sot\<close> is plus .
lift_definition scaleR_cblinfun_sot :: \<open>real \<Rightarrow> ('a, 'b) cblinfun_sot \<Rightarrow> ('a, 'b) cblinfun_sot\<close> is scaleR .
instance
  apply (intro_classes; transfer)
  by (auto simp add: scaleR_scaleC scaleC_add_right scaleC_add_left)
end

instantiation cblinfun_sot :: (complex_normed_vector, complex_normed_vector) topological_space begin
lift_definition open_cblinfun_sot :: \<open>('a, 'b) cblinfun_sot set \<Rightarrow> bool\<close> is \<open>openin cstrong_operator_topology\<close> .
instance
proof intro_classes
  show \<open>open (UNIV :: ('a,'b) cblinfun_sot set)\<close>
    apply transfer
    by (metis cstrong_operator_topology_topspace openin_topspace)
  show \<open>open S \<Longrightarrow> open T \<Longrightarrow> open (S \<inter> T)\<close> for S T :: \<open>('a,'b) cblinfun_sot set\<close>
    apply transfer by auto
  show \<open>\<forall>S\<in>K. open S \<Longrightarrow> open (\<Union> K)\<close> for K :: \<open>('a,'b) cblinfun_sot set set\<close>
    apply transfer by auto
qed
end

lemma transfer_nhds_cstrong_operator_topology[transfer_rule]:
  includes lifting_syntax
  shows \<open>(cr_cblinfun_sot ===> rel_filter cr_cblinfun_sot) (nhdsin cstrong_operator_topology) nhds\<close>
  unfolding nhds_def nhdsin_def
  apply (simp add: cstrong_operator_topology_topspace)
  by transfer_prover


(* (* Unused *)
lemma limitin_product_topology:
  shows \<open>limitin (product_topology T I) f l F \<longleftrightarrow> 
    l \<in> extensional I \<and> (\<forall>\<^sub>F x in F. f x \<in> (\<Pi>\<^sub>E i\<in>I. topspace (T i))) \<and> (\<forall>i\<in>I. limitin (T i) (\<lambda>j. f j i) (l i) F)\<close>
proof (intro iffI conjI ballI)
  assume asm: \<open>limitin (product_topology T I) f l F\<close>
  then have l_PiE: \<open>l \<in> (\<Pi>\<^sub>E i\<in>I. topspace (T i))\<close>
    by (metis PiE_iff limitin_topspace topspace_product_topology)
  then show \<open>l \<in> extensional I\<close>
    using PiE_iff by blast
  from asm have *: \<open>openin (product_topology T I) U \<Longrightarrow> l \<in> U \<Longrightarrow> (\<forall>\<^sub>F x in F. f x \<in> U)\<close> for U
     unfolding limitin_def by simp
   show \<open>\<forall>\<^sub>F x in F. f x \<in> (\<Pi>\<^sub>E i\<in>I. topspace (T i))\<close>
     apply (rule * )
      apply (metis openin_topspace topspace_product_topology)
     by (rule l_PiE)

  fix i assume \<open>i \<in> I\<close>
  from l_PiE have l_topspace: \<open>l i \<in> topspace (T i)\<close>
    by (metis PiE_mem \<open>i \<in> I\<close>)

  from asm
  have eventually_prod: \<open>openin (product_topology T I) V \<Longrightarrow> l \<in> V \<Longrightarrow> (\<forall>\<^sub>F x in F. f x \<in> V)\<close> for V
    unfolding limitin_def by auto

  have eventually_U: \<open>\<forall>\<^sub>F x in F. f x i \<in> U\<close>
    if open_U: \<open>openin (T i) U\<close> and \<open>l i \<in> U\<close> for U
  proof -
    from open_U have U_topspace: \<open>U \<subseteq> topspace (T i)\<close>
      by (simp add: openin_closedin_eq)
    define V where \<open>V = {f \<in> \<Pi>\<^sub>E i\<in>I. topspace (T i). f i \<in> U}\<close>
    then have V_PiE: \<open>V = PiE I (\<lambda>j. if j = i then U else topspace (T j))\<close>
      apply auto
      apply (smt (verit, best) PiE_mem U_topspace subsetD)
      using PiE_mem \<open>i \<in> I\<close> by fastforce
    have \<open>openin (product_topology T I) V\<close>
      unfolding V_PiE apply (rule product_topology_basis)
      using open_U by auto
    moreover have \<open>l \<in> V\<close>
      using V_def l_PiE that(2) by blast
    ultimately have \<open>\<forall>\<^sub>F x in F. f x \<in> V\<close>
      by (rule eventually_prod)
    then show \<open>\<forall>\<^sub>F x in F. f x i \<in> U\<close>
      apply (rule eventually_mono)
      unfolding V_def by simp
  qed

  show \<open>limitin (T i) (\<lambda>j. f j i) (l i) F\<close>
    using l_topspace eventually_U unfolding limitin_def by simp
next
  assume asm: \<open>l \<in> extensional I \<and> (\<forall>\<^sub>F x in F. f x \<in> (\<Pi>\<^sub>E i\<in>I. topspace (T i))) \<and> (\<forall>i\<in>I. limitin (T i) (\<lambda>j. f j i) (l i) F)\<close>
  then have limit: \<open>limitin (T i) (\<lambda>j. f j i) (l i) F\<close> if \<open>i\<in>I\<close> for i
    using that by simp
  have l_topspace: \<open>l \<in> topspace (product_topology T I)\<close>
    by (metis PiE_iff asm limitin_topspace topspace_product_topology)
  have eventually_U: \<open>\<forall>\<^sub>F x in F. f x \<in> U\<close>
    if \<open>openin (product_topology T I) U\<close> and \<open>l \<in> U\<close> for U
  proof -
    from product_topology_open_contains_basis[OF that]
    obtain V where l_V: \<open>l \<in> Pi\<^sub>E I V\<close> and open_V: \<open>(\<forall>i. openin (T i) (V i))\<close>
      and finite_I0: \<open>finite {i. V i \<noteq> topspace (T i)}\<close> and V_U: \<open>Pi\<^sub>E I V \<subseteq> U\<close>
      by auto
    define I0 where \<open>I0 = {i\<in>I. V i \<noteq> topspace (T i)}\<close>
    have \<open>\<forall>\<^sub>F x in F. f x i \<in> V i\<close> if \<open>i\<in>I\<close> for i
      using limit[OF that] that unfolding limitin_def
      by (meson PiE_E open_V l_V)
    then have 1: \<open>\<forall>\<^sub>F x in F. \<forall>i\<in>I0. f x i \<in> V i\<close>
      apply (subst eventually_ball_finite_distrib)
      by (simp_all add: I0_def finite_I0)
    from asm have 2: \<open>\<forall>\<^sub>F x in F. f x \<in> (\<Pi>\<^sub>E i\<in>I. topspace (T i))\<close>
      by simp
    have 3: \<open>f x i \<in> V i\<close> if \<open>f x i \<in> topspace (T i)\<close> and \<open>i \<in> I-I0\<close> for i x
      using that unfolding I0_def by blast
    from 2 3 have \<open>\<forall>\<^sub>F x in F. \<forall>i\<in>I-I0. f x i \<in> V i\<close>
      by (smt (verit) Diff_iff PiE_iff eventually_mono)
    with 1 have \<open>\<forall>\<^sub>F x in F. \<forall>i\<in>I. f x i \<in> V i\<close>
      by (smt (verit, best) DiffI eventually_elim2)
    with 2 have \<open>\<forall>\<^sub>F x in F. (\<forall>i\<in>I. f x i \<in> V i) \<and> f x \<in> (\<Pi>\<^sub>E i\<in>I. topspace (T i))\<close>
      using eventually_conj by blast
    then show \<open>\<forall>\<^sub>F x in F. f x \<in> U\<close>
      apply (rule eventually_mono)
      using V_U unfolding PiE_def by blast
  qed

  show \<open>limitin (product_topology T I) f l F\<close>
    using l_topspace eventually_U unfolding limitin_def by simp
qed *)

lemma filterlim_cstrong_operator_topology: \<open>filterlim f (nhdsin cstrong_operator_topology l) = limitin cstrong_operator_topology f l\<close>
  by (auto simp: cstrong_operator_topology_topspace simp flip: filterlim_nhdsin_iff_limitin)

lemma hausdorff_sot[simp]: \<open>Hausdorff_space cstrong_operator_topology\<close>
proof (rule hausdorffI)
  fix a b :: \<open>'a \<Rightarrow>\<^sub>C\<^sub>L 'b\<close>
  assume \<open>a \<noteq> b\<close>
  then obtain \<psi> where \<open>a *\<^sub>V \<psi> \<noteq> b *\<^sub>V \<psi>\<close>
    by (meson cblinfun_eqI)
  then obtain U' V' where \<open>open U'\<close> \<open>open V'\<close> \<open>a *\<^sub>V \<psi> \<in> U'\<close> \<open>b *\<^sub>V \<psi> \<in> V'\<close> \<open>U' \<inter> V' = {}\<close>
    by (meson hausdorff)
  define U V where \<open>U = {f. \<forall>i\<in>{()}. f *\<^sub>V \<psi> \<in> U'}\<close> and \<open>V = {f. \<forall>i\<in>{()}. f *\<^sub>V \<psi> \<in> V'}\<close>
  have 1: \<open>openin cstrong_operator_topology U\<close>
    unfolding U_def apply (rule cstrong_operator_topology_basis)
    using \<open>open U'\<close> by auto
  have 2: \<open>openin cstrong_operator_topology V\<close>
    unfolding V_def apply (rule cstrong_operator_topology_basis)
    using \<open>open V'\<close> by auto
  show \<open>\<exists>U V. openin cstrong_operator_topology U \<and> openin cstrong_operator_topology V \<and> a \<in> U \<and> b \<in> V \<and> U \<inter> V = {}\<close>
    by (rule exI[of _ U], rule exI[of _ V])
       (use 1 2 \<open>a *\<^sub>V \<psi> \<in> U'\<close> \<open>b *\<^sub>V \<psi> \<in> V'\<close> \<open>U' \<inter> V' = {}\<close> in \<open>auto simp: U_def V_def\<close>)
qed

instance cblinfun_sot :: (complex_normed_vector, complex_normed_vector) t2_space
proof intro_classes
  fix a b :: \<open>('a,'b) cblinfun_sot\<close>
  show \<open>a \<noteq> b \<Longrightarrow> \<exists>U V. open U \<and> open V \<and> a \<in> U \<and> b \<in> V \<and> U \<inter> V = {}\<close>
    apply transfer using hausdorff_sot
    by (metis UNIV_I cstrong_operator_topology_topspace Hausdorff_space_def disjnt_def)
qed

lemma Domainp_cr_cblinfun_sot[simp]: \<open>Domainp cr_cblinfun_sot = (\<lambda>_. True)\<close>
  by (metis (no_types, opaque_lifting) DomainPI cblinfun_sot.left_total left_totalE)

lemma Rangep_cr_cblinfun_sot[simp]: \<open>Rangep cr_cblinfun_sot = (\<lambda>_. True)\<close>
  by (meson RangePI cr_cblinfun_sot_def)

lemma Rangep_set[relator_domain]: "Rangep (rel_set T) = (\<lambda>A. Ball A (Rangep T))"
  by (metis (no_types, opaque_lifting) Domainp_conversep Domainp_set rel_set_conversep)


lemma transfer_euclidean_cstrong_operator_topology[transfer_rule]:
  includes lifting_syntax
  shows \<open>(rel_topology cr_cblinfun_sot) cstrong_operator_topology euclidean\<close> 
proof (unfold rel_topology_def, intro conjI allI impI)
  show \<open>(rel_set cr_cblinfun_sot ===> (=)) (openin cstrong_operator_topology) (openin euclidean)\<close>
    unfolding rel_fun_def rel_set_def open_openin [symmetric] cr_cblinfun_sot_def
    by (transfer, intro allI impI arg_cong[of _ _ "openin x" for x]) blast
next
  fix U :: \<open>('a \<Rightarrow>\<^sub>C\<^sub>L 'b) set\<close>
  assume \<open>openin cstrong_operator_topology U\<close>
  show \<open>Domainp (rel_set cr_cblinfun_sot) U\<close>
    by (simp add: Domainp_set)
next
  fix U :: \<open>('a, 'b) cblinfun_sot set\<close>
  assume \<open>openin euclidean U\<close>
  show \<open>Rangep (rel_set cr_cblinfun_sot) U\<close>
    by (simp add: Rangep_set)
qed

lemma openin_cstrong_operator_topology: \<open>openin cstrong_operator_topology U \<longleftrightarrow> (\<exists>V. open V \<and> U = (*\<^sub>V) -` V)\<close>
  by (simp add: cstrong_operator_topology_def openin_pullback_topology)

lemma cstrong_operator_topology_plus_cont: \<open>LIM (x,y) nhdsin cstrong_operator_topology a \<times>\<^sub>F nhdsin cstrong_operator_topology b.
            x + y :> nhdsin cstrong_operator_topology (a + b)\<close>
  unfolding cstrong_operator_topology_def
  by (rule pullback_topology_bi_cont[where f'=plus])
     (auto simp: case_prod_unfold tendsto_add_Pair cblinfun.add_left)

instance cblinfun_sot :: (complex_normed_vector, complex_normed_vector) topological_group_add
proof intro_classes
  show \<open>((\<lambda>x. fst x + snd x) \<longlongrightarrow> a + b) (nhds a \<times>\<^sub>F nhds b)\<close> for a b :: \<open>('a,'b) cblinfun_sot\<close>
    apply transfer
    using cstrong_operator_topology_plus_cont
    by (auto simp: case_prod_unfold)

  have *: \<open>continuous_map cstrong_operator_topology cstrong_operator_topology uminus\<close>
    apply (subst continuous_on_cstrong_operator_topo_iff_coordinatewise)
    apply (rewrite at \<open>(\<lambda>y. - y *\<^sub>V x)\<close> in \<open>\<forall>x. \<hole>\<close> to \<open>(\<lambda>y. y *\<^sub>V - x)\<close> DEADID.rel_mono_strong)
    by (auto simp: cstrong_operator_topology_continuous_evaluation cblinfun.minus_left cblinfun.minus_right)
  show \<open>(uminus \<longlongrightarrow> - a) (nhds a)\<close> for a :: \<open>('a,'b) cblinfun_sot\<close>
    apply (subst tendsto_at_iff_tendsto_nhds[symmetric])
    apply (subst isCont_def[symmetric])
    apply (rule continuous_on_interior[where S=UNIV])
     apply (subst continuous_map_iff_continuous2[symmetric])
     apply transfer
    using * by auto
qed

lemma continuous_map_left_comp_sot[continuous_intros]: 
  fixes b :: \<open>'b::complex_normed_vector \<Rightarrow>\<^sub>C\<^sub>L 'c::complex_normed_vector\<close>
    and f :: \<open>'a \<Rightarrow> 'd::complex_normed_vector \<Rightarrow>\<^sub>C\<^sub>L 'b\<close>
  assumes \<open>continuous_map T cstrong_operator_topology f\<close> 
  shows \<open>continuous_map T cstrong_operator_topology (\<lambda>x. b o\<^sub>C\<^sub>L f x)\<close> 
proof -
  have *: \<open>open B \<Longrightarrow> open ((*\<^sub>V) b -` B)\<close> for B
    by (simp add: continuous_open_vimage)
  have **: \<open>((\<lambda>a. b *\<^sub>V a \<psi>) -` B \<inter> UNIV) = (Pi\<^sub>E UNIV (\<lambda>i. if i=\<psi> then (\<lambda>a. b *\<^sub>V a) -` B else UNIV))\<close> 
    for \<psi> :: 'd and B
    by (auto simp: PiE_def Pi_def)
  have *: \<open>continuous_on UNIV (\<lambda>(a::'d \<Rightarrow> 'b). b *\<^sub>V  (a \<psi>))\<close> for \<psi>
    unfolding continuous_on_open_vimage[OF open_UNIV]
    apply (intro allI impI)
    apply (subst **)
    apply (rule open_PiE)
    using * by auto
  have *: \<open>continuous_on UNIV (\<lambda>(a::'d \<Rightarrow> 'b) \<psi>. b *\<^sub>V a \<psi>)\<close>
    apply (rule continuous_on_coordinatewise_then_product)
    by (rule *)
  have \<open>continuous_map cstrong_operator_topology cstrong_operator_topology
              (\<lambda>x :: 'd \<Rightarrow>\<^sub>C\<^sub>L 'b. b o\<^sub>C\<^sub>L x)\<close> 
    unfolding cstrong_operator_topology_def
    apply (rule continuous_map_pullback')
    subgoal
      apply (subst asm_rl[of \<open>(*\<^sub>V) \<circ> (o\<^sub>C\<^sub>L) b = (\<lambda>a x. b *\<^sub>V (a x)) \<circ> (*\<^sub>V)\<close>])
      subgoal by force
      subgoal by (rule continuous_map_pullback) (use * in auto)
      done
    subgoal using * by auto
    done
  from continuous_map_compose[OF assms this, unfolded o_def]
  show ?thesis
    by -
qed

lemma continuous_cstrong_operator_topology_plus[continuous_intros]:
  assumes \<open>continuous_map T cstrong_operator_topology f\<close>
  assumes \<open>continuous_map T cstrong_operator_topology g\<close>
  shows \<open>continuous_map T cstrong_operator_topology (\<lambda>x. f x + g x)\<close>
  using assms
  by (auto intro!: continuous_map_add
      simp: continuous_on_cstrong_operator_topo_iff_coordinatewise cblinfun.add_left)

lemma continuous_cstrong_operator_topology_uminus[continuous_intros]:
  assumes \<open>continuous_map T cstrong_operator_topology f\<close>
  shows \<open>continuous_map T cstrong_operator_topology (\<lambda>x. - f x)\<close>
  using assms
  by (auto simp add: continuous_on_cstrong_operator_topo_iff_coordinatewise cblinfun.minus_left)

lemma continuous_cstrong_operator_topology_minus[continuous_intros]:
  assumes \<open>continuous_map T cstrong_operator_topology f\<close>
  assumes \<open>continuous_map T cstrong_operator_topology g\<close>
  shows \<open>continuous_map T cstrong_operator_topology (\<lambda>x. f x - g x)\<close>
  apply (subst diff_conv_add_uminus)
  by (intro continuous_intros assms)



lemma continuous_map_right_comp_sot[continuous_intros]: 
  assumes \<open>continuous_map T cstrong_operator_topology f\<close> 
  shows \<open>continuous_map T cstrong_operator_topology (\<lambda>x. f x o\<^sub>C\<^sub>L a)\<close> 
  apply (rule continuous_map_compose[OF assms, unfolded o_def])
  by (simp add: continuous_on_cstrong_operator_topo_iff_coordinatewise cstrong_operator_topology_continuous_evaluation)

lemma continuous_map_scaleC_sot[continuous_intros]: 
  assumes \<open>continuous_map T cstrong_operator_topology f\<close> 
  shows \<open>continuous_map T cstrong_operator_topology (\<lambda>x. c *\<^sub>C f x)\<close>
  apply (subst asm_rl[of \<open>scaleC c = (o\<^sub>C\<^sub>L) (c *\<^sub>C id_cblinfun)\<close>])
   apply auto[1]
  using assms by (rule continuous_map_left_comp_sot)

lemma continuous_scaleC_sot[continuous_intros]: 
  fixes f :: \<open>'a::topological_space \<Rightarrow> (_,_) cblinfun_sot\<close>
  assumes \<open>continuous_on X f\<close>
  shows \<open>continuous_on X (\<lambda>x. c *\<^sub>C f x)\<close>
  apply (rule continuous_on_compose[OF assms, unfolded o_def])
  apply (rule continuous_on_subset[rotated, where s=UNIV], simp)
  apply (subst continuous_map_iff_continuous2[symmetric])
  apply transfer
  apply (rule continuous_map_scaleC_sot)
  by simp

lemma sot_closure_is_csubspace[simp]:
  fixes A::"('a::complex_normed_vector, 'b::complex_normed_vector) cblinfun_sot set"
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
  proof (cases "c = 0")
    case False
    have "(*\<^sub>C) c ` A \<subseteq> closure A"
      using csubspace_scaleC_invariant[of c A] assms False closure_subset[of A] by auto
    hence "(*\<^sub>C) c ` closure A \<subseteq> closure A"
      by (intro image_closure_subset) (auto intro!: continuous_intros)
    thus ?thesis
      using that by blast
  qed (use 0 in auto)
qed

lemma limitin_cstrong_operator_topology:
  \<open>limitin cstrong_operator_topology f l F \<longleftrightarrow> (\<forall>i. ((\<lambda>j. f j *\<^sub>V i) \<longlongrightarrow> l *\<^sub>V i) F)\<close>
  by (simp add: cstrong_operator_topology_def limitin_pullback_topology 
      tendsto_coordinatewise)

lemma cstrong_operator_topology_in_closureI:
  assumes \<open>\<And>M \<epsilon>. \<epsilon> > 0 \<Longrightarrow> finite M \<Longrightarrow> \<exists>a\<in>A. \<forall>v\<in>M. norm ((b-a) *\<^sub>V v) \<le> \<epsilon>\<close>
  shows \<open>b \<in> cstrong_operator_topology closure_of A\<close>
proof -
  define F :: \<open>('a set \<times> real) filter\<close> where \<open>F = finite_subsets_at_top UNIV \<times>\<^sub>F at_right 0\<close>
  obtain f where fA: \<open>f M \<epsilon> \<in> A\<close> and f: \<open>v \<in> M \<Longrightarrow> norm ((f M \<epsilon> - b) *\<^sub>V v) \<le> \<epsilon>\<close> if \<open>finite M\<close> and \<open>\<epsilon> > 0\<close> for M \<epsilon> v
    apply atomize_elim
    apply (intro allI choice2)
    using assms
    by (metis cblinfun.diff_left norm_minus_commute)
  have F_props: \<open>\<forall>\<^sub>F (M,\<epsilon>) in F. finite M \<and> \<epsilon> > 0\<close>
    by (auto intro!: eventually_prodI simp: F_def case_prod_unfold eventually_at_right_less)
  then have inA: \<open>\<forall>\<^sub>F (M,\<epsilon>) in F. f M \<epsilon> \<in> A\<close>
    apply (rule eventually_rev_mp)
    using fA by (auto intro!: always_eventually)
  have \<open>limitin cstrong_operator_topology (case_prod f) b F\<close>
  proof -
    have \<open>\<forall>\<^sub>F (M,\<epsilon>) in F. norm (f M \<epsilon> *\<^sub>V v - b *\<^sub>V v) < e\<close> if \<open>e > 0\<close> for e v
    proof -
      have 1: \<open>\<forall>\<^sub>F (M,\<epsilon>) in F. (finite M \<and> v \<in> M) \<and> (\<epsilon> > 0 \<and> \<epsilon> < e)\<close>
        apply (unfold F_def case_prod_unfold, rule eventually_prodI)
        using eventually_at_right that
        by (auto simp add: eventually_finite_subsets_at_top)
      have 2: \<open>norm (f M \<epsilon> *\<^sub>V v - b *\<^sub>V v) < e\<close> if \<open>(finite M \<and> v \<in> M) \<and> (\<epsilon> > 0 \<and> \<epsilon> < e)\<close> for M \<epsilon>
        by (smt (verit) cblinfun.diff_left f that)
      show ?thesis
        using 1 apply (rule eventually_mono)
        using 2 by auto
    qed
    then have \<open>((\<lambda>(M,\<epsilon>). f M \<epsilon> *\<^sub>V v) \<longlongrightarrow> b *\<^sub>V v) F\<close> for v
      by (simp add: tendsto_iff dist_norm case_prod_unfold)
    then show ?thesis
      by (simp add: case_prod_unfold limitin_cstrong_operator_topology)
  qed
  then show ?thesis
    apply (rule limitin_closure_of)
    using inA by (auto simp: F_def case_prod_unfold prod_filter_eq_bot)
qed




lemma sot_weaker_than_norm_limitin: \<open>limitin cstrong_operator_topology a A F\<close> if \<open>(a \<longlongrightarrow> A) F\<close>
proof -
  from that have \<open>((\<lambda>x. a x *\<^sub>V \<psi>) \<longlongrightarrow> A \<psi>) F\<close> for \<psi>
    by (auto intro!: cblinfun.tendsto)
  then show ?thesis
    by (simp add: limitin_cstrong_operator_topology)
qed

lemma [transfer_rule]:
  includes lifting_syntax
  shows \<open>(rel_set cr_cblinfun_sot ===> (=)) csubspace csubspace\<close>
  unfolding complex_vector.subspace_def
  by transfer_prover

lemma [transfer_rule]:
  includes lifting_syntax
  shows \<open>(rel_set cr_cblinfun_sot ===> (=)) (closedin cstrong_operator_topology) closed\<close>
  apply (simp add: closed_def[abs_def] closedin_def[abs_def] cstrong_operator_topology_topspace Compl_eq_Diff_UNIV)
  by transfer_prover

lemma [transfer_rule]:
  includes lifting_syntax
  shows \<open>(rel_set cr_cblinfun_sot ===> rel_set cr_cblinfun_sot) (Abstract_Topology.closure_of cstrong_operator_topology) closure\<close>
  apply (subst closure_of_hull[where X=cstrong_operator_topology, unfolded cstrong_operator_topology_topspace, simplified, abs_def])
  apply (subst closure_hull[abs_def])
  unfolding hull_def
  by transfer_prover

lemma sot_closure_is_csubspace'[simp]:
  fixes A::"('a::complex_normed_vector \<Rightarrow>\<^sub>C\<^sub>L 'b::complex_normed_vector) set"
  assumes \<open>csubspace A\<close>
  shows \<open>csubspace (cstrong_operator_topology closure_of A)\<close>
  using sot_closure_is_csubspace[of \<open>Abs_cblinfun_sot ` A\<close>] assms
  apply (transfer fixing: A)
  by simp

lemma has_sum_closed_cstrong_operator_topology:
  assumes aA: \<open>\<And>i. a i \<in> A\<close>
  assumes closed: \<open>closedin cstrong_operator_topology A\<close>
  assumes subspace: \<open>csubspace A\<close>
  assumes has_sum: \<open>\<And>\<psi>. ((\<lambda>i. a i *\<^sub>V \<psi>) has_sum (b *\<^sub>V \<psi>)) I\<close>
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
  have \<open>((\<lambda>F. \<Sum>i\<in>F. a i *\<^sub>V \<psi>) \<longlongrightarrow> b *\<^sub>V \<psi>) (finite_subsets_at_top I)\<close> for \<psi>
    using has_sum_def by blast
  then have \<open>limitin cstrong_operator_topology (\<lambda>F. \<Sum>i\<in>F. a i) b (finite_subsets_at_top I)\<close>
    by (auto simp add: limitin_cstrong_operator_topology cblinfun.sum_left)
  then show \<open>b \<in> A\<close>
    using 1 closed apply (rule limitin_closedin)
    by simp
qed


lemma has_sum_in_cstrong_operator_topology:
  \<open>has_sum_in cstrong_operator_topology f A l \<longleftrightarrow> (\<forall>\<psi>. ((\<lambda>i. f i *\<^sub>V \<psi>) has_sum (l *\<^sub>V \<psi>)) A)\<close>
  by (simp add: cblinfun.sum_left has_sum_in_def limitin_cstrong_operator_topology has_sum_def)

lemma summable_sot_absI:
  fixes b :: \<open>'a \<Rightarrow> 'b::complex_normed_vector \<Rightarrow>\<^sub>C\<^sub>L 'c::chilbert_space\<close>
  assumes \<open>\<And>F f. finite F \<Longrightarrow> (\<Sum>n\<in>F. norm (b n *\<^sub>V f)) \<le> K * norm f\<close>
  shows \<open>summable_on_in cstrong_operator_topology b UNIV\<close>
proof -
  obtain B' where B': \<open>((\<lambda>n. b n *\<^sub>V f) has_sum (B' f)) UNIV\<close> for f
  proof (atomize_elim, intro choice allI)
    fix f
    have \<open>(\<lambda>n. b n *\<^sub>V f) abs_summable_on UNIV\<close>
      apply (rule nonneg_bdd_above_summable_on)
      using assms by (auto intro!: bdd_aboveI[where M=\<open>K * norm f\<close>])
    then show \<open>\<exists>l. ((\<lambda>n. b n *\<^sub>V f) has_sum l) UNIV\<close>
      by (metis abs_summable_summable summable_on_def)
  qed
  have \<open>bounded_clinear B'\<close>
  proof (intro bounded_clinearI allI)
    fix x y :: 'b and c :: complex
    from B'[of x] B'[of y]
    have \<open>((\<lambda>n. b n *\<^sub>V x + b n *\<^sub>V y) has_sum B' x + B' y) UNIV\<close>
      by (simp add: has_sum_add)
    with B'[of \<open>x + y\<close>]
    show \<open>B' (x + y) = B' x + B' y\<close>
      by (metis (no_types, lifting) cblinfun.add_right has_sum_cong infsumI)
    from B'[of x]
    have \<open>((\<lambda>n. c *\<^sub>C (b n *\<^sub>V x)) has_sum c *\<^sub>C B' x) UNIV\<close>
      by (metis cblinfun_scaleC_right.rep_eq has_sum_cblinfun_apply)
    with B'[of \<open>c *\<^sub>C x\<close>]
    show \<open>B' (c *\<^sub>C x) = c *\<^sub>C B' x\<close>
      by (metis (no_types, lifting) cblinfun.scaleC_right has_sum_cong infsumI)
    show \<open>norm (B' x) \<le> norm x * K\<close>
    proof -
      have *: \<open>(\<lambda>n. b n *\<^sub>V x) abs_summable_on UNIV\<close>
        apply (rule nonneg_bdd_above_summable_on)
        using assms by (auto intro!: bdd_aboveI[where M=\<open>K * norm x\<close>])
      have \<open>norm (B' x) \<le> (\<Sum>\<^sub>\<infinity>n. norm (b n *\<^sub>V x))\<close>
        using _ B'[of x] apply (rule norm_has_sum_bound)
        using * summable_iff_has_sum_infsum by blast
      also have \<open>(\<Sum>\<^sub>\<infinity>n. norm (b n *\<^sub>V x)) \<le> K * norm x\<close>
        using * apply (rule infsum_le_finite_sums)
        using assms by simp
      finally show ?thesis
        by (simp add: mult.commute)
    qed
  qed
  define B where \<open>B = CBlinfun B'\<close>
  with \<open>bounded_clinear B'\<close> have BB': \<open>B *\<^sub>V f = B' f\<close> for f
    by (simp add: bounded_clinear_CBlinfun_apply)
  have \<open>has_sum_in cstrong_operator_topology b UNIV B\<close>
    using B' by (simp add: has_sum_in_cstrong_operator_topology BB')
  then show ?thesis
    using summable_on_in_def by blast
qed

declare cstrong_operator_topology_topspace[simp]

lift_definition cblinfun_compose_sot :: \<open>('a::complex_normed_vector,'b::complex_normed_vector) cblinfun_sot \<Rightarrow> ('c::complex_normed_vector,'a) cblinfun_sot \<Rightarrow> ('c,'b) cblinfun_sot\<close>
  is cblinfun_compose .

lemma isCont_cblinfun_compose_sot_right[simp]: \<open>isCont (\<lambda>F. cblinfun_compose_sot F G) x\<close>
  apply (rule continuous_on_interior[where S=UNIV, rotated], simp)
  apply (rule continuous_map_iff_continuous2[THEN iffD1])
  apply transfer
  by (simp add: continuous_map_right_comp_sot)

lemma isCont_cblinfun_compose_sot_left[simp]: \<open>isCont (\<lambda>F. cblinfun_compose_sot G F) x\<close>
  apply (rule continuous_on_interior[where S=UNIV, rotated], simp)
  apply (rule continuous_map_iff_continuous2[THEN iffD1])
  apply transfer
  by (simp add: continuous_map_left_comp_sot)

lemma additive_cblinfun_compose_sot_right[simp]: \<open>additive (\<lambda>F. cblinfun_compose_sot F G)\<close>
  unfolding additive_def
  apply transfer
  by (simp add: cblinfun_compose_add_left)

lemma additive_cblinfun_compose_sot_left[simp]: \<open>additive (\<lambda>F. cblinfun_compose_sot G F)\<close>
  unfolding additive_def
  apply transfer
  by (simp add: cblinfun_compose_add_right)

lemma transfer_infsum_sot[transfer_rule]:
  includes lifting_syntax
  assumes [transfer_rule]: \<open>bi_unique R\<close>
  shows \<open>((R ===> cr_cblinfun_sot) ===> rel_set R ===> cr_cblinfun_sot) (infsum_in cstrong_operator_topology) infsum\<close>
  apply (simp add: infsum_euclidean_eq[abs_def, symmetric])
  by transfer_prover

lemma transfer_summable_on_sot[transfer_rule]:
  includes lifting_syntax
  assumes [transfer_rule]: \<open>bi_unique R\<close>
  shows \<open>((R ===> cr_cblinfun_sot) ===> rel_set R ===> (\<longleftrightarrow>)) (summable_on_in cstrong_operator_topology) (summable_on)\<close>
  apply (simp add: summable_on_euclidean_eq[abs_def, symmetric])
  by transfer_prover


lemma sandwich_sot_cont[continuous_intros]:
  assumes \<open>continuous_map T cstrong_operator_topology f\<close>
  shows \<open>continuous_map T cstrong_operator_topology (\<lambda>x. sandwich A (f x))\<close>
  apply (simp add: sandwich_apply)
  by (intro continuous_intros assms)

lemma closed_map_sot_unitary_sandwich:
  fixes U :: \<open>'a::chilbert_space \<Rightarrow>\<^sub>C\<^sub>L 'b::chilbert_space\<close>
  assumes \<open>unitary U\<close> (* Probably holds under weaker assumptions. *)
  shows \<open>closed_map cstrong_operator_topology cstrong_operator_topology (\<lambda>x. sandwich U x)\<close>
  apply (rule closed_eq_continuous_inverse_map[where g=\<open>sandwich (U*)\<close>, THEN iffD2])
  using assms 
  by (auto intro!: continuous_intros
      simp flip: sandwich_compose cblinfun_apply_cblinfun_compose)


unbundle no_cblinfun_notation

end