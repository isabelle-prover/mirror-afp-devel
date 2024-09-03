\<^marker>\<open>creator "Niklas Krofta"\<close>
section \<open>General theory of Topological Groups\<close>
theory Topological_Group
  imports 
    "HOL-Algebra.Group" 
    "HOL-Algebra.Coset"
    "HOL-Analysis.Abstract_Topology" 
    "HOL-Analysis.Product_Topology" 
    "HOL-Analysis.T1_Spaces"
    "HOL-Analysis.Abstract_Metric_Spaces"
     Uniform_Structure 
begin

paragraph \<open>Summary\<close>
text \<open>
  In this section we define topological groups and prove basic results about them.
  We also introduce the left and right uniform structures of topological groups and
  prove the Birkhoff-Kakutani theorem.
\<close>

subsection \<open>Auxiliary definitions and results\<close>
subsubsection \<open>Miscellaneous\<close>

lemma connected_components_homeo:
  assumes homeo: "homeomorphic_map T\<^sub>1 T\<^sub>2 \<phi>" and in_space: "x \<in> topspace T\<^sub>1"
  shows "\<phi>`(connected_component_of_set T\<^sub>1 x) = connected_component_of_set T\<^sub>2 (\<phi> x)"
proof
  let ?Z = connected_component_of_set
  show "\<phi>`(?Z T\<^sub>1 x) \<subseteq> ?Z T\<^sub>2 (\<phi> x)"
    by (metis connected_component_of_eq connected_component_of_maximal connectedin_connected_component_of homeo homeomorphic_map_connectedness_eq imageI in_space mem_Collect_eq)
next
  let ?Z = connected_component_of_set
  from homeo obtain \<psi> where \<psi>_homeo: "homeomorphic_map T\<^sub>2 T\<^sub>1 \<psi>"
    and \<psi>_inv: "(\<forall>y \<in> topspace T\<^sub>1. \<psi> (\<phi> y) = y) \<and> (\<forall>y \<in> topspace T\<^sub>2. \<phi> (\<psi> y) = y)"
    by (smt (verit) homeomorphic_map_maps homeomorphic_maps_map)
  from homeo in_space have "\<phi> x \<in> topspace T\<^sub>2"
    using homeomorphic_imp_surjective_map by blast
  then have "\<psi>`(?Z T\<^sub>2 (\<phi> x)) \<subseteq> ?Z T\<^sub>1 (\<psi> (\<phi> x))"
    by (metis connected_component_of_eq connected_component_of_maximal connectedin_connected_component_of \<psi>_homeo homeomorphic_map_connectedness_eq imageI mem_Collect_eq)
  then show "?Z T\<^sub>2 (\<phi> x) \<subseteq> \<phi>`(?Z T\<^sub>1 x)"
    by (smt (verit, del_insts) \<psi>_inv connected_component_of_subset_topspace image_subset_iff in_space subsetD subsetI)
qed

lemma open_map_prod_top:
  assumes "open_map T\<^sub>1 T\<^sub>3 f" and "open_map T\<^sub>2 T\<^sub>4 g"
  shows "open_map (prod_topology T\<^sub>1 T\<^sub>2) (prod_topology T\<^sub>3 T\<^sub>4) (\<lambda>(x, y). (f x, g y))"
proof (unfold open_map_def, standard, standard)
  let ?p = "\<lambda>(x, y). (f x, g y)"
  fix U assume "openin (prod_topology T\<^sub>1 T\<^sub>2) U"
  then obtain \<U> where h\<U>: "\<U> \<subseteq> {V \<times> W | V W. openin T\<^sub>1 V \<and> openin T\<^sub>2 W} \<and> \<Union> \<U> = U"
    unfolding openin_prod_topology union_of_def using arbitrary_def by auto
  then have "?p`U = \<Union> {?p`VW | VW. VW \<in> \<U>}" by blast
  then have "?p`U = \<Union> {?p`(V \<times> W) | V W. V \<times> W \<in> \<U> \<and> openin T\<^sub>1 V \<and> openin T\<^sub>2 W}" 
    using h\<U> by blast
  moreover have "?p`(V \<times> W) = (f`V) \<times> (g`W)" for V W by fast
  ultimately have "?p`U = \<Union> {(f`V) \<times> (g`W) | V W. V \<times> W \<in> \<U> \<and> openin T\<^sub>1 V \<and> openin T\<^sub>2 W}" by presburger
  moreover have "openin (prod_topology T\<^sub>3 T\<^sub>4) ((f`V) \<times> (g`W))" if "openin T\<^sub>1 V \<and> openin T\<^sub>2 W" for V W
    using openin_prod_Times_iff assms that open_map_def by metis
  ultimately show "openin (prod_topology T\<^sub>3 T\<^sub>4) (?p`U)" by fastforce
qed

lemma injective_quotient_map_homeo:
  assumes "quotient_map T1 T2 q" and inj: "inj_on q (topspace T1)"
  shows "homeomorphic_map T1 T2 q" using assms
    unfolding homeomorphic_eq_everything_map injective_quotient_map[OF inj] by fast

lemma (in group) subgroupI_alt:
  assumes subset: "H \<subseteq> carrier G" and nonempty: "H \<noteq> {}" and 
    closed: "\<And>\<sigma> \<tau>. \<sigma> \<in> H \<and> \<tau> \<in> H \<Longrightarrow> \<sigma> \<otimes> inv \<tau> \<in> H"
  shows "subgroup H G"
proof -
  from nonempty obtain \<eta> where "\<eta> \<in> H" by blast
  then have "\<one> \<in> H" using closed[of \<eta> \<eta>] subset r_inv by fastforce
  then have closed_inv: "inv \<sigma> \<in> H" if "\<sigma> \<in> H" for \<sigma>
    using closed[of \<one> \<sigma>] r_inv r_one subset that by force
  then have "\<sigma> \<otimes> \<tau> \<in> H" if "\<sigma> \<in> H \<and> \<tau> \<in> H" for \<sigma> \<tau>
    using closed[of \<sigma> "inv \<tau>"] inv_inv subset subset_iff that by auto
  then show ?thesis using assms closed_inv by (auto intro: subgroupI)
qed

lemma subgroup_intersection: 
  assumes "subgroup H G" and "subgroup H' G"
  shows "subgroup (H \<inter> H') G"
  using assms unfolding subgroup_def by force

subsubsection \<open>Quotient topology\<close>

definition quot_topology :: "'a topology \<Rightarrow> ('a \<Rightarrow> 'b) \<Rightarrow> 'b topology" where
"quot_topology T q = topology (\<lambda>U. U \<subseteq> q`(topspace T) \<and> openin T {x \<in> topspace T. q x \<in> U})"

lemma quot_topology_open:
  fixes T :: "'a topology" and q :: "'a \<Rightarrow> 'b"
  defines "openin_quot U \<equiv> U \<subseteq> q`(topspace T) \<and> openin T {x \<in> topspace T. q x \<in> U}"
  shows "openin (quot_topology T q) = openin_quot"
proof -
  have "istopology openin_quot"
  proof -
    have "openin_quot (U\<^sub>1 \<inter> U\<^sub>2)" if "openin_quot U\<^sub>1 \<and> openin_quot U\<^sub>2" for U\<^sub>1 U\<^sub>2
    proof -
      have "{x \<in> topspace T. q x \<in> U\<^sub>1 \<inter> U\<^sub>2} = {x \<in> topspace T. q x \<in> U\<^sub>1} \<inter> {x \<in> topspace T. q x \<in> U\<^sub>2}" by blast
      then show ?thesis using that unfolding openin_quot_def by auto
    qed
    moreover have "openin_quot (\<Union> \<U>)" if "\<forall>U\<in>\<U>. openin_quot U" for \<U>
    proof -
      have "{x \<in> topspace T. q x \<in> \<Union> \<U>} = \<Union> {{x \<in> topspace T. q x \<in> U} | U. U \<in> \<U>}" by blast
      then show ?thesis using that unfolding openin_quot_def by auto
    qed
    ultimately show ?thesis using istopology_def
      by (smt (verit) Collect_cong Sup_set_def UnionI Union_iff image_eqI mem_Collect_eq mem_Collect_eq openin_topspace subsetI subset_antisym topspace_def)
  qed
  from topology_inverse'[OF this] show ?thesis using quot_topology_def unfolding openin_quot_def by metis
qed

lemma projection_quotient_map: "quotient_map T (quot_topology T q) q" 
proof (unfold quotient_map_def, intro conjI)
  have "openin (quot_topology T q) (q ` topspace T)" using quot_topology_open
    by (smt (verit) image_subset_iff mem_Collect_eq openin_subtopology_refl subsetI subtopology_superset)
  then show "q ` topspace T = topspace (quot_topology T q)" using quot_topology_open
    by (metis (no_types, opaque_lifting) openin_subset openin_topspace subset_antisym)
next
  show "\<forall>U \<subseteq> topspace (quot_topology T q).
       openin T {x \<in> topspace T. q x \<in> U} = openin (quot_topology T q) U"
    using quot_topology_open by (metis (mono_tags, lifting) openin_topspace order_trans)
qed

corollary topspace_quot_topology [simp]: "topspace (quot_topology T q) = q`(topspace T)"
  using projection_quotient_map quotient_imp_surjective_map by metis

corollary projection_continuous: "continuous_map T (quot_topology T q) q"
  using projection_quotient_map quotient_imp_continuous_map by fast

subsection \<open>Definition and basic results\<close>

locale topological_group = group +
  fixes T :: "'g topology"
  assumes group_is_space [simp]: "topspace T = carrier G"
  assumes inv_continuous: "continuous_map T T (\<lambda>\<sigma>. inv \<sigma>)"
  assumes mul_continuous: "continuous_map (prod_topology T T) T (\<lambda>(\<sigma>,\<tau>). \<sigma>\<otimes>\<tau>)"
begin

lemma in_space_iff_in_group [iff]: "\<sigma> \<in> topspace T \<longleftrightarrow> \<sigma> \<in> carrier G" 
  by auto

lemma translations_continuous [intro]:
  assumes in_group: "\<sigma> \<in> carrier G"
  shows "continuous_map T T (\<lambda>\<tau>. \<sigma>\<otimes>\<tau>)" and "continuous_map T T (\<lambda>\<tau>. \<tau>\<otimes>\<sigma>)"
proof -
  have "continuous_map T (prod_topology T T) (\<lambda>\<tau>. (\<sigma>,\<tau>))"
    by (auto intro: continuous_map_pairedI simp: in_group)
  moreover have "(\<lambda>\<tau>. \<sigma>\<otimes>\<tau>) = (\<lambda>(\<sigma>,\<tau>). \<sigma>\<otimes>\<tau>) \<circ> (\<lambda>\<tau>. (\<sigma>,\<tau>))" by auto
  ultimately show "continuous_map T T (\<lambda>\<tau>. \<sigma>\<otimes>\<tau>)"
    using mul_continuous continuous_map_compose by metis
next
  have "continuous_map T (prod_topology T T) (\<lambda>\<tau>. (\<tau>,\<sigma>))"
    by (auto intro: continuous_map_pairedI simp: in_group)
  moreover have "(\<lambda>\<tau>. \<tau>\<otimes>\<sigma>) = (\<lambda>(\<sigma>,\<tau>). \<sigma>\<otimes>\<tau>) \<circ> (\<lambda>\<tau>. (\<tau>,\<sigma>))" by auto
  ultimately show "continuous_map T T (\<lambda>\<tau>. \<tau>\<otimes>\<sigma>)"
    using mul_continuous continuous_map_compose by metis
qed

lemma translations_homeos:
  assumes in_group: "\<sigma> \<in> carrier G"
  shows "homeomorphic_map T T (\<lambda>\<tau>. \<sigma>\<otimes>\<tau>)" and "homeomorphic_map T T (\<lambda>\<tau>. \<tau>\<otimes>\<sigma>)"
proof -
  have "\<forall>\<tau>\<in>topspace T. inv \<sigma> \<otimes> (\<sigma> \<otimes> \<tau>) = \<tau>" by (simp add: group.inv_solve_left' in_group)
  moreover have "\<forall>\<tau>\<in>topspace T. \<sigma> \<otimes> (inv \<sigma> \<otimes> \<tau>) = \<tau>"
    by (metis group_is_space in_group inv_closed l_one m_assoc r_inv)
  ultimately have "homeomorphic_maps T T (\<lambda>\<tau>. \<sigma>\<otimes>\<tau>) (\<lambda>\<tau>. (inv \<sigma>)\<otimes>\<tau>)"
    using homeomorphic_maps_def in_group by blast
  then show "homeomorphic_map T T (\<lambda>\<tau>. \<sigma>\<otimes>\<tau>)" using homeomorphic_maps_map by blast
next
  have "\<forall>\<tau>\<in>topspace T. \<tau> \<otimes> \<sigma> \<otimes> inv \<sigma> = \<tau>"
    by (simp add: group.inv_solve_right' in_group)
  moreover have "\<forall>\<tau>\<in>topspace T. \<tau> \<otimes> inv \<sigma> \<otimes> \<sigma> = \<tau>" by (simp add: in_group m_assoc)
  ultimately have "homeomorphic_maps T T (\<lambda>\<tau>. \<tau>\<otimes>\<sigma>) (\<lambda>\<tau>. \<tau>\<otimes>(inv \<sigma>))"
    using homeomorphic_maps_def in_group by blast
  then show "homeomorphic_map T T (\<lambda>\<tau>. \<tau>\<otimes>\<sigma>)" using homeomorphic_maps_map by blast
qed

abbreviation conjugation :: "'g \<Rightarrow> 'g \<Rightarrow> 'g" where
"conjugation \<sigma> \<tau> \<equiv> \<sigma> \<otimes> \<tau> \<otimes> inv \<sigma>"

corollary conjugation_homeo:
  assumes in_group: "\<sigma> \<in> carrier G"
  shows "homeomorphic_map T T (conjugation \<sigma>)"
proof -
  have "conjugation \<sigma> = (\<lambda>\<tau>. \<tau> \<otimes> inv \<sigma>) \<circ> (\<lambda>\<tau>. \<sigma> \<otimes> \<tau>)" by auto
  then show ?thesis using translations_homeos homeomorphic_map_compose
    by (metis in_group inv_closed)
qed

corollary open_set_translations:
  assumes open_set: "openin T U" and in_group: "\<sigma> \<in> carrier G"
  shows "openin T (\<sigma> <# U)" and "openin T (U #> \<sigma>)"
proof -
  let ?\<phi> = "\<lambda>\<tau>. \<sigma> \<otimes> \<tau>"
  have "\<sigma> <# U = ?\<phi>`U" unfolding l_coset_def by blast
  then show "openin T (\<sigma> <# U)" using translations_homeos[OF in_group]
    by (metis homeomorphic_map_openness_eq open_set)
next
  let ?\<psi> = "\<lambda>\<tau>. \<tau> \<otimes> \<sigma>"
  have "U #> \<sigma> = ?\<psi>`U" unfolding r_coset_def by fast
  then show "openin T (U #> \<sigma>)" using translations_homeos[OF in_group]
    by (metis homeomorphic_map_openness_eq open_set)
qed

corollary closed_set_translations:
  assumes closed_set: "closedin T U" and in_group: "\<sigma> \<in> carrier G"
  shows "closedin T (\<sigma> <# U)" and "closedin T (U #> \<sigma>)"
proof -
  let ?\<phi> = "\<lambda>\<tau>. \<sigma>\<otimes>\<tau>"
  have "\<sigma> <# U = ?\<phi>`U" unfolding l_coset_def by fast
  then show "closedin T (\<sigma> <# U)" using translations_homeos[OF in_group]
    by (metis homeomorphic_map_closedness_eq closed_set)
next
  let ?\<psi> = "\<lambda>\<tau>. \<tau>\<otimes>\<sigma>"
  have "U #> \<sigma> = ?\<psi>`U" unfolding r_coset_def by fast
  then show "closedin T (U #> \<sigma>)" using translations_homeos[OF in_group]
    by (metis homeomorphic_map_closedness_eq closed_set)
qed

lemma inverse_homeo: "homeomorphic_map T T (\<lambda>\<sigma>. inv \<sigma>)"
  using homeomorphic_map_involution[OF inv_continuous] by auto

subsection \<open>Subspaces and quotient spaces\<close>

abbreviation connected_component_1 :: "'g set" where
"connected_component_1 \<equiv> connected_component_of_set T \<one>"

lemma connected_component_1_props: 
  shows "connected_component_1 \<lhd> G" and "closedin T connected_component_1"
proof -
  let ?Z = "connected_component_of_set T"
  have in_space: "(?Z \<one>) \<subseteq> topspace T"
    using connected_component_of_subset_topspace by fastforce
  have "subgroup (?Z \<one>) G"
  proof (rule subgroupI)
    show "(?Z \<one>) \<subseteq> carrier G" using in_space by auto
  next
    show "(?Z \<one>) \<noteq> {}"
      by (metis connected_component_of_eq_empty group_is_space one_closed)
  next
    fix \<sigma> assume h\<sigma>: "\<sigma> \<in> (?Z \<one>)"
    let ?\<phi> = "\<lambda>\<eta>. inv \<eta>"
    have "?\<phi>`(?Z \<one>) = ?Z \<one>" using connected_components_homeo
      by (metis group_is_space inv_one inverse_homeo one_closed)
    then show "inv \<sigma> \<in> (?Z \<one>)" using h\<sigma> by blast
  next
    fix \<sigma> \<tau> assume h\<sigma>: "\<sigma> \<in> (?Z \<one>)" and h\<tau>: "\<tau> \<in> (?Z \<one>)"
    let ?\<phi> = "\<lambda>\<eta>. \<sigma> \<otimes> \<eta>"
    have "?\<phi>`(?Z \<one>) = ?Z \<sigma>" using connected_components_homeo
      by (metis group_is_space h\<sigma> in_space one_closed r_one subset_eq translations_homeos(1))
    moreover have "?Z \<sigma> = ?Z \<one>" using h\<sigma> by (simp add: connected_component_of_equiv)
    ultimately show "\<sigma> \<otimes> \<tau> \<in> ?Z \<one>" using h\<tau> by blast
  qed
  moreover have "conjugation \<sigma> \<tau> \<in> ?Z \<one>" if h\<sigma>\<tau>: "\<sigma> \<in> carrier G \<and> \<tau> \<in> ?Z \<one>" for \<sigma> \<tau>
  proof -
    let ?\<phi> = "conjugation \<sigma>"
    have "?\<phi>`(?Z \<one>) = ?Z (?\<phi> \<one>)" using connected_components_homeo
      by (metis conjugation_homeo group_is_space one_closed h\<sigma>\<tau>)
    then show ?thesis using r_inv r_one h\<sigma>\<tau> by auto
  qed
  ultimately show "connected_component_1 \<lhd> G" using normal_inv_iff by blast
next
  show "closedin T connected_component_1" by (simp add: closedin_connected_component_of)
qed

lemma group_prod_space [simp]: "topspace (prod_topology T T) = (carrier G) \<times> (carrier G)"
  by auto

no_notation eq_closure_of ("closure'_of\<index>")

lemma subgroup_closure:
  assumes H_subgroup: "subgroup H G"
  shows "subgroup (T closure_of H) G"
proof -
  have subset: "T closure_of H \<subseteq> carrier G"
    by (metis closedin_closure_of closedin_subset group_is_space)
  have nonempty: "T closure_of H \<noteq> {}"
    by (simp add: assms closure_of_eq_empty group.subgroupE(1) subgroupE(2))
  
  let ?\<phi> = "\<lambda>(\<sigma>,\<tau>). \<sigma> \<otimes> inv \<tau>"
  have \<phi>_continuous: "continuous_map (prod_topology T T) T ?\<phi>"
  proof -
    have "continuous_map (prod_topology T T) (prod_topology T T) (\<lambda>(\<sigma>, \<tau>). (\<sigma>, inv \<tau>))"
      using continuous_map_prod_top inv_continuous by fastforce
    moreover have "?\<phi> = (\<lambda>(\<sigma>, \<tau>). \<sigma> \<otimes> \<tau>) \<circ> (\<lambda>(\<sigma>, \<tau>). (\<sigma>, inv \<tau>))" by fastforce
    ultimately show ?thesis using mul_continuous continuous_map_compose by force
  qed

  have "\<sigma> \<otimes> inv \<tau> \<in> T closure_of H" 
    if h\<sigma>\<tau>: "\<sigma> \<in> T closure_of H \<and> \<tau> \<in> T closure_of H" for \<sigma> \<tau>
  proof -
    have in_space: "\<sigma> \<otimes> inv \<tau> \<in> topspace T" using subset h\<sigma>\<tau> by fast
    have "\<exists>\<eta> \<in> H. \<eta> \<in> U" if hU: "openin T U \<and> \<sigma> \<otimes> inv \<tau> \<in> U" for U
    proof -
      let ?V = "{x \<in> topspace (prod_topology T T). ?\<phi> x \<in> U}"
      have "openin (prod_topology T T) ?V" 
        using \<phi>_continuous hU openin_continuous_map_preimage by blast
      moreover have "(\<sigma>,\<tau>) \<in> ?V"
        using hU group_prod_space h\<sigma>\<tau> subset by force
      ultimately obtain V\<^sub>1 V\<^sub>2 where 
        hV\<^sub>1V\<^sub>2: "openin T V\<^sub>1 \<and> openin T V\<^sub>2 \<and> \<sigma> \<in> V\<^sub>1 \<and> \<tau> \<in> V\<^sub>2 \<and> V\<^sub>1 \<times> V\<^sub>2 \<subseteq> ?V"
        by (smt (verit) openin_prod_topology_alt) 
      then obtain \<sigma>' \<tau>' where h\<sigma>'\<tau>': "\<sigma>' \<in> V\<^sub>1 \<inter> H \<and> \<tau>' \<in> V\<^sub>2 \<inter> H" using h\<sigma>\<tau>
        by (meson all_not_in_conv disjoint_iff openin_Int_closure_of_eq_empty)
      then have "?\<phi> (\<sigma>',\<tau>') \<in> U" using hV\<^sub>1V\<^sub>2 by blast
      moreover have "?\<phi> (\<sigma>',\<tau>') \<in> H" using h\<sigma>'\<tau>' H_subgroup subgroupE(3,4) by simp
      ultimately show ?thesis by blast
    qed
    then show ?thesis using closure_of_def in_space by force
  qed
  then show ?thesis using subgroupI_alt subset nonempty by blast
qed

lemma normal_subgroup_closure:
  assumes normal_subgroup: "N \<lhd> G"
  shows "(T closure_of N) \<lhd> G"
proof -
  have "(conjugation \<sigma>)`(T closure_of N) \<subseteq> T closure_of N" if h\<sigma>: "\<sigma> \<in> carrier G" for \<sigma> 
  proof -
    have "(conjugation \<sigma>)`N \<subseteq> N" using normal_subgroup normal_invE(2) h\<sigma> by auto
    then have "T closure_of (conjugation \<sigma>)`N \<subseteq> T closure_of N" 
      using closure_of_mono by meson
    moreover have "(conjugation \<sigma>)`(T closure_of N) \<subseteq> T closure_of (conjugation \<sigma>)`N"
      using h\<sigma> conjugation_homeo
      by (meson continuous_map_eq_image_closure_subset homeomorphic_imp_continuous_map)
    ultimately show ?thesis by blast
  qed
  moreover have "subgroup (T closure_of N) G" using subgroup_closure
    by (simp add: normal_invE(1) normal_subgroup)
  ultimately show ?thesis using normal_inv_iff by auto
qed

lemma topological_subgroup:
  assumes "subgroup H G"
  shows "topological_group (G \<lparr>carrier := H\<rparr>) (subtopology T H)"
proof -
  interpret subgroup H G by fact
  let ?\<H> = "(G \<lparr>carrier := H\<rparr>)" and ?T' = "subtopology T H"
  have H_subspace: "topspace ?T' = H" using topspace_subtopology_subset by force
  have "continuous_map ?T' T (\<lambda>\<sigma>. inv \<sigma>)" using continuous_map_from_subtopology inv_continuous by blast
  moreover have "(\<lambda>\<sigma>. inv \<sigma>) \<in> topspace ?T' \<rightarrow> H" unfolding Pi_def H_subspace by blast
  ultimately have "continuous_map ?T' ?T' (\<lambda>\<sigma>. inv \<sigma>)" using continuous_map_into_subtopology by blast
  then have sub_inv_continuous: "continuous_map ?T' ?T' (\<lambda>\<sigma>. inv\<^bsub>?\<H>\<^esub> \<sigma>)"
    using continuous_map_eq H_subspace m_inv_consistent assms by fastforce
  have "continuous_map (prod_topology ?T' ?T') T (\<lambda>(\<sigma>,\<tau>). \<sigma> \<otimes> \<tau>)" 
    unfolding subtopology_Times[symmetric] using continuous_map_from_subtopology[OF mul_continuous] by fast
  moreover have "(\<lambda>(\<sigma>,\<tau>). \<sigma> \<otimes> \<tau>) \<in> topspace (prod_topology ?T' ?T') \<rightarrow> H" 
    unfolding Pi_def topspace_prod_topology H_subspace by fast
  ultimately have "continuous_map (prod_topology ?T' ?T') ?T' (\<lambda>(\<sigma>,\<tau>). \<sigma> \<otimes> \<tau>)"
    using continuous_map_into_subtopology by blast
  then have "continuous_map (prod_topology ?T' ?T') ?T' (\<lambda>(\<sigma>,\<tau>). \<sigma> \<otimes>\<^bsub>?\<H>\<^esub> \<tau>)" by fastforce
  then show ?thesis unfolding topological_group_def topological_group_axioms_def using H_subspace sub_inv_continuous by auto
qed

text \<open>Topology on the set of cosets of some subgroup\<close>

abbreviation coset_topology :: "'g set \<Rightarrow> 'g set topology" where
"coset_topology H \<equiv> quot_topology T (r_coset G H)"

lemma coset_topology_topspace[simp]:
  shows "topspace (coset_topology H) = (r_coset G H)`(carrier G)"
  using projection_quotient_map quotient_imp_surjective_map group_is_space by metis

lemma projection_open_map:
  assumes subgroup: "subgroup H G"
  shows "open_map T (coset_topology H) (r_coset G H)"
proof (unfold open_map_def, standard, standard)
  fix U assume hU: "openin T U"
  let ?\<pi> = "r_coset G H"
  let ?V = "{\<sigma> \<in> topspace T. ?\<pi> \<sigma> \<in> ?\<pi>`U}"
  have subsets: "H \<subseteq> carrier G \<and> U \<subseteq> carrier G"
    using subgroup hU  openin_subset by (force elim!: subgroupE)
  have "?V = {\<sigma> \<in> carrier G. \<exists>\<tau> \<in> U. H #> \<sigma> = H #> \<tau>}" using image_def by blast 
  then have "?V = {\<sigma> \<in> carrier G. \<exists>\<tau> \<in> U. \<sigma> \<in> H #> \<tau>}" using subsets 
    by (smt (verit) Collect_cong rcos_self repr_independence subgroup subset_eq)
  also have "... = (\<Union>\<eta> \<in> H. \<eta> <# U)" unfolding r_coset_def l_coset_def using subsets by auto
  moreover have "openin T (\<eta> <# U)" if "\<eta> \<in> H" for \<eta>
    using open_set_translations(1)[OF hU] subsets that by blast
  ultimately have "openin T ?V" by fastforce
  then show "openin (coset_topology H) (?\<pi>`U)" using quot_topology_open hU
    by (metis (mono_tags, lifting) Collect_cong image_mono openin_subset)
qed

lemma topological_quotient_group:
  assumes normal_subgroup: "N \<lhd> G"
  shows "topological_group (G Mod N) (coset_topology N)"
proof -
  interpret normal N G by fact
  let ?\<pi> = "r_coset G N"
  let ?T' = "coset_topology N"
  have quot_space: "topspace ?T' = ?\<pi>`(carrier G)" using coset_topology_topspace by presburger
  then have quot_group_quot_space: "topspace ?T' = carrier (G Mod N)" using carrier_FactGroup by metis

  let ?quot_mul = "\<lambda>(N\<sigma>, N\<tau>). N\<sigma> \<otimes>\<^bsub>G Mod N\<^esub> N\<tau>"
  have \<pi>_prod_space: "topspace (prod_topology ?T' ?T') = ?\<pi>`(carrier G) \<times> ?\<pi>`(carrier G)"
    using quot_space topspace_prod_topology by simp
  have quot_mul_continuous: "continuous_map (prod_topology ?T' ?T') ?T' ?quot_mul"
  proof (unfold continuous_map_def, intro conjI ballI allI impI)
    show "?quot_mul \<in> topspace (prod_topology ?T' ?T') \<rightarrow> topspace ?T'" 
      using rcos_sum unfolding quot_space \<pi>_prod_space by auto
  next
    fix U assume hU: "openin ?T' U"
    let ?V = "{p \<in> topspace (prod_topology ?T' ?T'). ?quot_mul p \<in> U}"
    let ?W = "{(\<sigma>,\<tau>) \<in> topspace (prod_topology T T). N #> (\<sigma> \<otimes> \<tau>) \<in> U}"
    let ?\<pi>\<^sub>2 = "\<lambda>(\<sigma>, \<tau>). (N #> \<sigma>, N #> \<tau>)"
    have "(\<lambda>(\<sigma>,\<tau>). N #> (\<sigma> \<otimes> \<tau>)) = ?\<pi> \<circ> (\<lambda>(\<sigma>,\<tau>). \<sigma> \<otimes> \<tau>)" by fastforce
    then have "continuous_map (prod_topology T T) ?T' (\<lambda>(\<sigma>,\<tau>). N #> (\<sigma> \<otimes> \<tau>))"
      using continuous_map_compose mul_continuous projection_continuous by fastforce
    then have "openin (prod_topology T T) ?W"
      using hU openin_continuous_map_preimage
      by (smt (verit) Collect_cong case_prodE case_prodI2 case_prod_conv)
    moreover have "open_map (prod_topology T T) (prod_topology ?T' ?T') ?\<pi>\<^sub>2"
      using projection_open_map open_map_prod_top by (metis subgroup_axioms)
    ultimately have "openin (prod_topology ?T' ?T') (?\<pi>\<^sub>2`?W)" using open_map_def by blast
    moreover have "?V = ?\<pi>\<^sub>2`?W"
      using rcos_sum unfolding \<pi>_prod_space group_prod_space by auto
    ultimately show "openin (prod_topology ?T' ?T') ?V" by presburger
  qed

  let ?quot_inv = "\<lambda>N\<sigma>. inv\<^bsub>G Mod N\<^esub> N\<sigma>"
  have \<pi>_inv: "?quot_inv (N #> \<sigma>) = ?\<pi> (inv \<sigma>)" if "\<sigma> \<in> carrier G" for \<sigma> 
    using inv_FactGroup rcos_inv carrier_FactGroup that by blast 
  have "continuous_map ?T' ?T' ?quot_inv"
  proof (unfold continuous_map_def, intro conjI ballI allI impI)
    show "?quot_inv \<in> topspace ?T' \<rightarrow> topspace ?T'" using \<pi>_inv quot_space by auto
  next
    fix U assume hU: "openin ?T' U"
    let ?V = "{N\<sigma> \<in> topspace ?T'. ?quot_inv N\<sigma> \<in> U}"
    let ?W = "{\<sigma> \<in> topspace T. N #> (inv \<sigma>) \<in> U}"
    have "(\<lambda>\<sigma>. N #> (inv \<sigma>)) = ?\<pi> \<circ> (\<lambda>\<sigma>. inv \<sigma>)" by fastforce
    then have "continuous_map T ?T' (\<lambda>\<sigma>. N #> (inv \<sigma>))"
      using continuous_map_compose projection_continuous inv_continuous 
      by (metis (no_types, lifting)) 
    then have "openin T ?W" using hU openin_continuous_map_preimage by blast
    then have "openin ?T' (?\<pi>`?W)" 
      using projection_open_map by (simp add: open_map_def subgroup_axioms)
    moreover have "?V = ?\<pi>`?W" using \<pi>_inv quot_space by force
    ultimately show "openin ?T' ?V" by presburger
  qed

  then show ?thesis unfolding topological_group_def topological_group_axioms_def
    using quot_group_quot_space quot_mul_continuous factorgroup_is_group by blast
qed

text \<open>
  See \<^cite>\<open>"stackexchange_quot_groups"\<close> for our approach to proving that quotient groups
  of topological groups are topological.
\<close>

abbreviation neighborhood :: "'g \<Rightarrow> 'g set \<Rightarrow> bool" where
"neighborhood \<sigma> U \<equiv> openin T U \<and> \<sigma> \<in> U"

abbreviation symmetric :: "'g set \<Rightarrow> bool" where
"symmetric S \<equiv> {inv \<sigma> | \<sigma>. \<sigma> \<in> S} \<subseteq> S"

text 
  \<open>Note that this implies the other inclusion, so symmetric subsets are equal to their 
  image under inversion.
\<close>

lemma neighborhoods_of_1:
  assumes "neighborhood \<one> U"
  shows "\<exists>V. neighborhood \<one> V \<and> symmetric V \<and> V <#> V \<subseteq> U"
proof -
  have a: "\<exists>V\<subseteq>U'. neighborhood \<one> V \<and> symmetric V" if hU': "neighborhood \<one> U'" for U'
  proof -
    let ?W = "{\<sigma> \<in> carrier G. inv \<sigma> \<in> U'}"
    let ?V = "?W \<inter> ((\<lambda>\<sigma>. inv \<sigma>)`?W)"
    have "neighborhood \<one> ?W" using openin_continuous_map_preimage[OF inv_continuous]
        hU' inv_one by fastforce
    moreover from this have "neighborhood \<one> ((\<lambda>\<sigma>. inv \<sigma>)`?W)" using inverse_homeo 
        homeomorphic_imp_open_map inv_one image_eqI open_map_def by (metis (mono_tags, lifting))
    ultimately have neighborhood: "neighborhood \<one> ?V" by blast
    have "inv \<sigma> \<in> ?V" if "\<sigma> \<in> ?V" for \<sigma> using that by auto
    then have "symmetric ?V" by fast
    moreover have "\<sigma> \<in> U'" if "\<sigma> \<in> ?V" for \<sigma> using that by blast
    ultimately show ?thesis using neighborhood by blast
  qed
  have b: "\<exists>V. neighborhood \<one> V \<and> V <#> V \<subseteq> U'" if hU': "neighborhood \<one> U'" for U' 
  proof -
    let ?W = "{(\<sigma>,\<tau>) \<in> carrier G \<times> carrier G. \<sigma>\<otimes>\<tau> \<in> U'}"
    have preimage_mul: "?W = {x \<in> topspace (prod_topology T T). (\<lambda>(\<sigma>,\<tau>). \<sigma>\<otimes>\<tau>) x \<in> U'}"
      using topspace_prod_topology by fastforce
    then have "openin (prod_topology T T) ?W \<and> (\<one>,\<one>) \<in> ?W" 
      using openin_continuous_map_preimage[OF mul_continuous] hU' r_one by fastforce
    then obtain W\<^sub>1 W\<^sub>2 where hW\<^sub>1W\<^sub>2: "neighborhood \<one> W\<^sub>1 \<and> neighborhood \<one> W\<^sub>2 \<and> W\<^sub>1\<times>W\<^sub>2\<subseteq>?W"
      using openin_prod_topology_alt[where S="?W"] by meson
    let ?V = "W\<^sub>1 \<inter> W\<^sub>2"
    from hW\<^sub>1W\<^sub>2 have "neighborhood \<one> ?V" by fast
    moreover have "\<sigma>\<otimes>\<tau> \<in> U'" if "\<sigma>\<in>?V \<and> \<tau>\<in>?V" for \<sigma> \<tau> using preimage_mul hW\<^sub>1W\<^sub>2 that by blast
    ultimately show ?thesis unfolding set_mult_def by blast
  qed
  from b[OF assms] obtain W where hW: "neighborhood \<one> W \<and> W <#> W \<subseteq> U" by presburger
  from this a obtain V where "V\<subseteq>W \<and> neighborhood \<one> V \<and> symmetric V" by presburger
  moreover from this have "V <#> V \<subseteq> U" using hW mono_set_mult by blast
  ultimately show ?thesis unfolding set_mult_def by blast
qed

lemma Hausdorff_coset_space:
  assumes subgroup: "subgroup H G" and H_closed: "closedin T H"
  shows "Hausdorff_space (coset_topology H)"
proof (unfold Hausdorff_space_def, intro allI impI)
  interpret subgroup H G by fact
  let ?\<pi> = "r_coset G H"
  let ?T' = "coset_topology H"
  fix H\<sigma> H\<tau> assume cosets: "H\<sigma> \<in> topspace ?T' \<and> H\<tau> \<in> topspace ?T' \<and> H\<sigma> \<noteq> H\<tau>"
  then obtain \<sigma> \<tau> where h\<sigma>\<tau>: "\<sigma> \<in> carrier G \<and> \<tau> \<in> carrier G \<and> H\<sigma> = H #> \<sigma> \<and> H\<tau> = H #> \<tau>" by auto
  then have "\<sigma> \<notin> H #> \<tau>" using cosets subgroup repr_independence by blast
  have "\<one> \<notin> (inv \<sigma>) <# (H #> \<tau>)" 
  proof
    assume "\<one> \<in> inv \<sigma> <# (H #> \<tau>)"
    then obtain \<eta> where h\<eta>: "\<eta> \<in> H \<and> \<one> = (inv \<sigma>) \<otimes> (\<eta> \<otimes> \<tau>)" unfolding r_coset_def l_coset_def by auto
    then have "\<sigma> = \<eta> \<otimes> \<tau>"
      by (metis (no_types, lifting) Units_eq Units_m_closed group.inv_comm group_l_invI h\<sigma>\<tau> inv_closed inv_inv inv_unique' l_inv_ex mem_carrier)
    then show "False" using \<open>\<sigma> \<notin> H #> \<tau>\<close> h\<eta> r_coset_def by fast
  qed
  let ?U = "topspace T - ((inv \<sigma>) <# (H #> \<tau>))"
  have "closedin T ((inv \<sigma>) <# (H #> \<tau>))" 
      using closed_set_translations closed_set_translations[OF H_closed] h\<sigma>\<tau> by simp
  then have "neighborhood \<one> ?U" using \<open>\<one> \<notin> (inv \<sigma>) <# (H #> \<tau>)\<close> by blast
  then obtain V where hV: "neighborhood \<one> V \<and> symmetric V \<and> V <#> V \<subseteq> ?U"
    using neighborhoods_of_1 by presburger
  let ?V\<^sub>1 = "\<sigma> <# V" and ?V\<^sub>2 = "\<tau> <# V"
  have disjoint: "?\<pi>`?V\<^sub>1 \<inter> ?\<pi>`?V\<^sub>2 = {}"
  proof (rule ccontr)
    assume "?\<pi>`?V\<^sub>1 \<inter> ?\<pi>`?V\<^sub>2 \<noteq> {}"
    then obtain \<upsilon>\<^sub>1 \<upsilon>\<^sub>2 where h\<upsilon>\<^sub>1\<upsilon>\<^sub>2: "\<upsilon>\<^sub>1 \<in> V \<and> \<upsilon>\<^sub>2 \<in> V \<and> ?\<pi> (\<sigma>\<otimes>\<upsilon>\<^sub>1) = ?\<pi> (\<tau>\<otimes>\<upsilon>\<^sub>2)" 
      unfolding l_coset_def by auto
    moreover then have \<upsilon>\<^sub>1\<upsilon>\<^sub>2_in_group: "\<upsilon>\<^sub>1 \<in> carrier G \<and> \<upsilon>\<^sub>2 \<in> carrier G" 
      using hV openin_subset by force
    ultimately have in_H: "(\<sigma>\<otimes>\<upsilon>\<^sub>1) \<otimes> inv (\<tau>\<otimes>\<upsilon>\<^sub>2) \<in> H" 
      using subgroup repr_independenceD rcos_module_imp h\<sigma>\<tau> m_closed 
      by (metis group.rcos_self is_group subgroup.m_closed subgroup_self)
    let ?\<eta> = "(\<sigma>\<otimes>\<upsilon>\<^sub>1) \<otimes> inv (\<tau>\<otimes>\<upsilon>\<^sub>2)"
    have "?\<eta> = \<sigma> \<otimes> (\<upsilon>\<^sub>1 \<otimes> inv \<upsilon>\<^sub>2) \<otimes> inv \<tau>" using h\<sigma>\<tau> \<upsilon>\<^sub>1\<upsilon>\<^sub>2_in_group m_assoc
      by (simp add: inv_mult_group subgroupE(4) subgroup_self)
    then have "inv \<sigma> \<otimes> (?\<eta> \<otimes> \<tau>) = \<upsilon>\<^sub>1 \<otimes> inv \<upsilon>\<^sub>2" 
      using h\<sigma>\<tau> \<upsilon>\<^sub>1\<upsilon>\<^sub>2_in_group m_assoc inv_solve_left' by auto
    then have "\<upsilon>\<^sub>1 \<otimes> inv \<upsilon>\<^sub>2 \<in> (inv \<sigma>) <# (H #> \<tau>)" 
      unfolding l_coset_def r_coset_def using h\<sigma>\<tau> inv_closed in_H by force
    moreover have "\<upsilon>\<^sub>1 \<otimes> inv \<upsilon>\<^sub>2 \<in> ?U" using h\<upsilon>\<^sub>1\<upsilon>\<^sub>2 hV unfolding set_mult_def by blast
    ultimately show "False" by force 
  qed
  have "neighborhood \<sigma> ?V\<^sub>1 \<and> neighborhood \<tau> ?V\<^sub>2"
    using open_set_translations[of V] l_coset_def hV h\<sigma>\<tau> r_one by force
  then have "openin ?T' (?\<pi>`?V\<^sub>1) \<and> openin ?T' (?\<pi>`?V\<^sub>2) \<and> H\<sigma> \<in> ?\<pi>`?V\<^sub>1 \<and> H\<tau> \<in> ?\<pi>`?V\<^sub>2"
    using projection_open_map open_map_def subgroup h\<sigma>\<tau> by fast
  then show "\<exists>W\<^sub>1 W\<^sub>2. openin ?T' W\<^sub>1 \<and> openin ?T' W\<^sub>2 \<and> H\<sigma> \<in> W\<^sub>1 \<and> H\<tau> \<in> W\<^sub>2 \<and> disjnt W\<^sub>1 W\<^sub>2"
    using disjoint disjnt_def by meson
qed

lemma Hausdorff_coset_space_converse:
  assumes subgroup: "subgroup H G"
  assumes Hausdorff: "Hausdorff_space (coset_topology H)"
  shows "closedin T H"
proof -
  interpret subgroup H G by fact
  let ?T' = "coset_topology H"
  have "H \<in> topspace ?T'" using coset_topology_topspace coset_join2[of \<one> H] subgroup by auto
  then have "closedin ?T' {H}" 
    using t1_space_closedin_singleton Hausdorff_imp_t1_space[OF Hausdorff] by fast
  then have preimage_closed: "closedin T {\<sigma> \<in> carrier G. H #> \<sigma> = H}" 
    using projection_continuous closedin_continuous_map_preimage by fastforce
  have "\<sigma> \<in> H \<longleftrightarrow> H #> \<sigma> = H" if "\<sigma> \<in> carrier G" for \<sigma>
    using coset_join1 coset_join2 subgroup that by metis
  then have "H = {\<sigma> \<in> carrier G. H #> \<sigma> = H}" using subset by auto
  then show ?thesis using preimage_closed by presburger
qed

corollary Hausdorff_coset_space_iff:
  assumes subgroup: "subgroup H G"
  shows "Hausdorff_space (coset_topology H) \<longleftrightarrow> closedin T H"
  using Hausdorff_coset_space Hausdorff_coset_space_converse subgroup by blast

corollary topological_group_hausdorff_iff_one_closed:
  shows "Hausdorff_space T \<longleftrightarrow> closedin T {\<one>}"
proof -
  let ?\<pi> = "r_coset G {\<one>}"
  have "inj_on ?\<pi> (carrier G)" unfolding inj_on_def r_coset_def by simp
  then have "homeomorphic_map T (coset_topology {\<one>}) ?\<pi>"
    using projection_quotient_map injective_quotient_map_homeo group_is_space by metis
  then have "Hausdorff_space T \<longleftrightarrow> Hausdorff_space (coset_topology {\<one>})" 
    using homeomorphic_Hausdorff_space homeomorphic_map_imp_homeomorphic_space by blast
  then show ?thesis using Hausdorff_coset_space_iff triv_subgroup by blast
qed

lemma set_mult_one_subset:
  assumes "A \<subseteq> carrier G \<and> B \<subseteq> carrier G" and "\<one> \<in> B"
  shows "A \<subseteq> A <#> B" 
  unfolding set_mult_def using assms r_one by force

lemma open_set_mult_open:
  assumes "openin T U \<and> S \<subseteq> carrier G"
  shows "openin T (S <#> U)"
proof -
  have "S <#> U = (\<Union>\<sigma>\<in>S. \<sigma> <# U)" unfolding set_mult_def l_coset_def by blast
  moreover have "openin T (\<sigma> <# U)" if "\<sigma> \<in> S" for \<sigma> using open_set_translations(1) assms that by auto
  ultimately show ?thesis by auto
qed

lemma open_set_inv_open:
  assumes "openin T U"
  shows "openin T (set_inv U)"
proof -
  have "set_inv U = (\<lambda>\<sigma>. inv \<sigma>)`U" unfolding image_def SET_INV_def by blast
  then show ?thesis using inverse_homeo homeomorphic_imp_open_map open_map_def assms by metis
qed

lemma open_set_in_carrier[elim]:
  assumes "openin T U"
  shows "U \<subseteq> carrier G"
  using openin_subset assms by force

subsection \<open>Uniform structures\<close>

abbreviation left_entourage :: "'g set \<Rightarrow> ('g \<times> 'g) set" where
"left_entourage U \<equiv> {(\<sigma>,\<tau>) \<in> carrier G \<times> carrier G. inv \<sigma> \<otimes> \<tau> \<in> U}"

abbreviation right_entourage :: "'g set \<Rightarrow> ('g \<times> 'g) set" where
"right_entourage U \<equiv> {(\<sigma>,\<tau>) \<in> carrier G \<times> carrier G. \<sigma> \<otimes> inv \<tau> \<in> U}"

definition left_uniformity :: "'g uniformity" where "left_uniformity =
  uniformity (carrier G, \<lambda>E. E \<subseteq> carrier G \<times> carrier G \<and> (\<exists>U. neighborhood \<one> U \<and> left_entourage U \<subseteq> E))"

definition right_uniformity :: "'g uniformity" where "right_uniformity =
  uniformity (carrier G, \<lambda>E. E \<subseteq> carrier G \<times> carrier G \<and> (\<exists>U. neighborhood \<one> U \<and> right_entourage U \<subseteq> E))"

lemma
  uspace_left_uniformity[simp]: "uspace left_uniformity = carrier G" (is ?space_def) and
  entourage_left_uniformity: "entourage_in left_uniformity = 
    (\<lambda>E. E \<subseteq> carrier G \<times> carrier G \<and> (\<exists>U. neighborhood \<one> U \<and> left_entourage U \<subseteq> E))" (is ?entourage_def)
proof -
  let ?\<Phi> = "\<lambda>E. E \<subseteq> carrier G \<times> carrier G \<and> (\<exists>U. neighborhood \<one> U \<and> left_entourage U \<subseteq> E)"
  have "?\<Phi> (carrier G \<times> carrier G)" 
    using exI[where x="carrier G"] openin_topspace by force
  moreover have "Id_on (carrier G) \<subseteq> E \<and> ?\<Phi> (E\<inverse>) \<and> (\<exists>F. ?\<Phi> F \<and> F O F \<subseteq> E) \<and> 
    (\<forall>F. E \<subseteq> F \<and> F \<subseteq> carrier G \<times> carrier G \<longrightarrow> ?\<Phi> F)" if hE: "?\<Phi> E" for E
  proof -
    from hE obtain U where hU: "neighborhood \<one> U \<and> left_entourage U \<subseteq> E" by presburger
    then have U_subset: "U \<subseteq> carrier G" using openin_subset by force
    from hU have "Id_on (carrier G) \<subseteq> E" by fastforce
    moreover have "?\<Phi> (E\<inverse>)"
    proof -
      have "(\<tau>,\<sigma>) \<in> E" if "\<sigma> \<in> carrier G \<and> \<tau> \<in> carrier G \<and> inv \<sigma> \<otimes> \<tau> \<in> set_inv U" for \<sigma> \<tau>
      proof -
        have "inv \<tau> \<otimes> \<sigma> = inv (inv \<sigma> \<otimes> \<tau>)" using that inv_mult_group by auto
        from this have "inv \<tau> \<otimes> \<sigma> \<in> U" using that inv_inv U_subset unfolding SET_INV_def by auto
        then show ?thesis using that hU by fast
      qed
      then have "left_entourage (set_inv U) \<subseteq> E\<inverse>" by blast 
      moreover have "neighborhood \<one> (set_inv U)" using inv_one hU open_set_inv_open SET_INV_def by fastforce
      ultimately show ?thesis using hE by auto
    qed
    moreover have "\<exists>F. ?\<Phi> F \<and> F O F \<subseteq> E"
    proof -
      obtain V where hV: "neighborhood \<one> V \<and> V <#> V \<subseteq> U"
        using neighborhoods_of_1 hU by meson
      let ?F = "left_entourage V"
      have "(\<sigma>,\<rho>) \<in> E" if "(\<sigma>,\<tau>) \<in> ?F \<and> (\<tau>,\<rho>) \<in> ?F" for \<sigma> \<tau> \<rho>
      proof -
        have "\<sigma> \<in> carrier G \<and> \<tau> \<in> carrier G \<and> \<rho> \<in> carrier G" using that by force
        then have "inv \<sigma> \<otimes> \<rho> = (inv \<sigma> \<otimes> \<tau>) \<otimes> (inv \<tau> \<otimes> \<rho>)"
          using m_assoc inv_closed m_closed r_inv r_one by metis  
        moreover have "(inv \<sigma> \<otimes> \<tau>) \<otimes> (inv \<tau> \<otimes> \<rho>) \<in> U" using that hV unfolding set_mult_def by fast
        ultimately show ?thesis using hU that by force
      qed
      moreover have "?\<Phi> ?F" using hV by blast
      ultimately show ?thesis using hV by auto
    qed
    moreover have "\<forall>F. E \<subseteq> F \<and> F \<subseteq> carrier G \<times> carrier G \<longrightarrow> ?\<Phi> F" using hE by auto
    ultimately show ?thesis by blast
  qed
  moreover have "?\<Phi> (E \<inter> F)" if hEF: "?\<Phi> E \<and> ?\<Phi> F" for E F
  proof -
    from hEF obtain U V where
      hU: "neighborhood \<one> U \<and> left_entourage U \<subseteq> E" and
      hV: "neighborhood \<one> V \<and> left_entourage V \<subseteq> F" by presburger
    then have "neighborhood \<one> (U \<inter> V) \<and> left_entourage (U \<inter> V) \<subseteq> E \<inter> F" by fast
    then show ?thesis using that by auto
  qed
  ultimately have "uniformity_on (carrier G) ?\<Phi>"
    unfolding uniformity_on_def by auto
  from uniformity_inverse'[OF this] show ?space_def and ?entourage_def unfolding left_uniformity_def by auto
qed

lemma
  uspace_right_uniformity[simp]: "uspace right_uniformity = carrier G" (is ?space_def) and
  entourage_right_uniformity: "entourage_in right_uniformity =  
    (\<lambda>E. E \<subseteq> carrier G \<times> carrier G \<and> (\<exists>U. neighborhood \<one> U \<and> right_entourage U \<subseteq> E))" (is ?entourage_def)
proof -
  let ?\<Phi> = "\<lambda>E. E \<subseteq> carrier G \<times> carrier G \<and> (\<exists>U. neighborhood \<one> U \<and> right_entourage U \<subseteq> E)"
  have "?\<Phi> (carrier G \<times> carrier G)" 
    using exI[where x="carrier G"] openin_topspace by force
  moreover have "Id_on (carrier G) \<subseteq> E \<and> ?\<Phi> (E\<inverse>) \<and> (\<exists>F. ?\<Phi> F \<and> F O F \<subseteq> E) \<and> 
    (\<forall>F. E \<subseteq> F \<and> F \<subseteq> carrier G \<times> carrier G \<longrightarrow> ?\<Phi> F)" if hE: "?\<Phi> E" for E
  proof -
    from hE obtain U where 
      hU: "neighborhood \<one> U \<and> right_entourage U \<subseteq> E"
      by presburger
    then have U_subset: "U \<subseteq> carrier G" using openin_subset by force
    from hU have "Id_on (carrier G) \<subseteq> E" by fastforce
    moreover have "?\<Phi> (E\<inverse>)"
    proof -
      have "(\<tau>,\<sigma>) \<in> E" if "\<sigma> \<in> carrier G \<and> \<tau> \<in> carrier G \<and> \<sigma> \<otimes> inv \<tau> \<in> set_inv U" for \<sigma> \<tau>
      proof -
        have "\<tau> \<otimes> inv \<sigma> = inv (\<sigma> \<otimes> inv \<tau>)" using that inv_mult_group by auto
        from this have "\<tau> \<otimes> inv \<sigma> \<in> U" using that inv_inv U_subset unfolding SET_INV_def by auto
        then show ?thesis using that hU by fast
      qed
      then have "right_entourage (set_inv U) \<subseteq> E\<inverse>" by blast 
      moreover have "neighborhood \<one> (set_inv U)" using inv_one hU open_set_inv_open SET_INV_def by fastforce
      ultimately show ?thesis using hE by auto
    qed
    moreover have "\<exists>F. ?\<Phi> F \<and> F O F \<subseteq> E"
    proof -
      obtain V where hV: "neighborhood \<one> V \<and> V <#> V \<subseteq> U"
        using neighborhoods_of_1 hU by meson
      let ?F = "right_entourage V"
      have "(\<sigma>,\<rho>) \<in> E" if "(\<sigma>,\<tau>) \<in> ?F \<and> (\<tau>,\<rho>) \<in> ?F" for \<sigma> \<tau> \<rho>
      proof -
        have "\<sigma> \<in> carrier G \<and> \<tau> \<in> carrier G \<and> \<rho> \<in> carrier G" using that by force
        then have "\<sigma> \<otimes> inv \<rho> = (\<sigma> \<otimes> inv \<tau>) \<otimes> (\<tau> \<otimes> inv \<rho>)"
          using m_assoc inv_closed m_closed l_inv r_one by metis  
        moreover have "(\<sigma> \<otimes> inv \<tau>) \<otimes> (\<tau> \<otimes> inv \<rho>) \<in> U" using that hV unfolding set_mult_def by fast
        ultimately show ?thesis using hU that by force
      qed
      moreover have "?\<Phi> ?F" using hV by blast
      ultimately show ?thesis using hV by auto
    qed
    moreover have "\<forall>F. E \<subseteq> F \<and> F \<subseteq> carrier G \<times> carrier G \<longrightarrow> ?\<Phi> F" using hE by auto
    ultimately show ?thesis by blast
  qed
  moreover have "?\<Phi> (E \<inter> F)" if hEF: "?\<Phi> E \<and> ?\<Phi> F" for E F
  proof -
    from hEF obtain U V where
      hU: "neighborhood \<one> U \<and> right_entourage U \<subseteq> E" and
      hV: "neighborhood \<one> V \<and> right_entourage V \<subseteq> F"
      by presburger
    then have "neighborhood \<one> (U \<inter> V) \<and> right_entourage (U \<inter> V) \<subseteq> E \<inter> F" by fast
    then show ?thesis using that by auto
  qed
  ultimately have "uniformity_on (carrier G) ?\<Phi>"
    unfolding uniformity_on_def by auto
  from uniformity_inverse'[OF this] show ?space_def and ?entourage_def unfolding right_uniformity_def by auto
qed

lemma left_uniformity_induces_group_topology [simp]:
  shows "utopology left_uniformity = T"
proof -
  let ?\<Phi> = left_uniformity
  let ?T' = "utopology ?\<Phi>"
  have "openin T U \<longleftrightarrow> openin ?T' U" for U
  proof
    assume U_open: "openin T U"
    have "\<exists>E. entourage_in ?\<Phi> E \<and> E``{\<sigma>} \<subseteq> U" if h\<sigma>: "\<sigma> \<in> U" for \<sigma>
    proof -
      let ?E = "left_entourage (inv \<sigma> <# U)"
      have in_group: "\<sigma> \<in> carrier G" using h\<sigma> U_open open_set_in_carrier by blast
      then have "openin T (inv \<sigma> <# U)"
        using inv_closed open_set_translations(1) U_open by presburger
      then have "neighborhood \<one> (inv \<sigma> <# U)"
        using h\<sigma> in_group r_inv unfolding l_coset_def SET_INV_def by force
      then have "entourage_in ?\<Phi> ?E" unfolding entourage_left_uniformity by blast
      moreover have "\<tau> \<in> U" if "\<tau> \<in> ?E``{\<sigma>}" for \<tau>
      proof -
        from that have "inv \<sigma> \<otimes> \<tau> \<in> inv \<sigma> <# U" by force
        then obtain \<rho> where h\<rho>: "\<rho> \<in> U \<and> inv \<sigma> \<otimes> \<tau> = inv \<sigma> \<otimes> \<rho>" unfolding l_coset_def by fast
        then have "\<rho> \<in> carrier G \<and> \<tau> \<in> carrier G" using that open_set_in_carrier U_open by fast
        then have "\<tau> = \<rho>" using in_group h\<rho> inv_closed by (metis Units_eq Units_l_cancel)
        then show ?thesis using h\<rho> by simp
      qed
      ultimately show ?thesis by blast
    qed
    moreover have "U \<subseteq> uspace ?\<Phi>" using openin_subset U_open by force
    ultimately show "openin ?T' U" unfolding openin_utopology by force
  next
    assume U_open: "openin ?T' U"
    have "\<exists>W. neighborhood \<sigma> W \<and> W \<subseteq> U" if h\<sigma>: "\<sigma> \<in> U" for \<sigma>
    proof -
      have in_group: "\<sigma> \<in> carrier G" using h\<sigma> U_open openin_subset topspace_utopology by force
      from U_open h\<sigma> obtain E where hE: "entourage_in ?\<Phi> E \<and> E``{\<sigma>} \<subseteq> U"
        unfolding openin_utopology by blast
      then obtain V where hV: "neighborhood \<one> V \<and> left_entourage V \<subseteq> E"
        unfolding entourage_left_uniformity by fastforce
      let ?W = "{\<tau> \<in> carrier G. inv \<sigma> \<otimes> \<tau> \<in> V}"
      from hV have W_subset: "?W \<subseteq> E``{\<sigma>}" using in_group by fast
      have "continuous_map T T (\<lambda>\<tau>. inv \<sigma> \<otimes> \<tau>)" using translations_continuous in_group inv_closed by blast
      then have "openin T ?W" using openin_continuous_map_preimage hV by fastforce
      then have "neighborhood \<sigma> ?W" using in_group r_inv hV by simp
      then show ?thesis using W_subset hE by fast
    qed
    then show "openin T U" using openin_subopen by force
  qed
  then show ?thesis using topology_eq by blast
qed

lemma right_uniformity_induces_group_topology [simp]:
  shows "utopology right_uniformity = T"
proof -
  let ?\<Phi> = right_uniformity
  let ?T' = "utopology ?\<Phi>"
  have "openin T U \<longleftrightarrow> openin ?T' U" for U
  proof
    assume U_open: "openin T U"
    have "\<exists>E. entourage_in ?\<Phi> E \<and> E``{\<sigma>} \<subseteq> U" if h\<sigma>: "\<sigma> \<in> U" for \<sigma>
    proof -
      let ?E = "right_entourage (\<sigma> <# set_inv U)"
      have in_group: "\<sigma> \<in> carrier G" using h\<sigma> U_open open_set_in_carrier by blast
      then have "openin T (\<sigma> <# set_inv U)"
        using open_set_inv_open open_set_translations(1) U_open by presburger
      then have "neighborhood \<one> (\<sigma> <# set_inv U)"
        using h\<sigma> in_group r_inv unfolding l_coset_def SET_INV_def by force
      then have "entourage_in ?\<Phi> ?E" unfolding entourage_right_uniformity by blast
      moreover have "\<tau> \<in> U" if "\<tau> \<in> ?E``{\<sigma>}" for \<tau>
      proof -
        from that have "\<sigma> \<otimes> inv \<tau> \<in> \<sigma> <# set_inv U" by force
        then obtain \<rho> where h\<rho>: "\<rho> \<in> U \<and> \<sigma> \<otimes> inv \<tau> = \<sigma> \<otimes> inv \<rho>"
          unfolding l_coset_def SET_INV_def by fast
        then have "\<rho> \<in> carrier G \<and> \<tau> \<in> carrier G" using that open_set_in_carrier U_open by fast
        then have "\<tau> = \<rho>" using in_group h\<rho> inv_closed by (metis Units_eq Units_l_cancel inv_inv)
        then show ?thesis using h\<rho> by simp
      qed
      ultimately show ?thesis by blast
    qed
    moreover have "U \<subseteq> uspace ?\<Phi>" using openin_subset U_open by force
    ultimately show "openin ?T' U" unfolding openin_utopology by force
  next
    assume U_open: "openin ?T' U"
    have "\<exists>W. neighborhood \<sigma> W \<and> W \<subseteq> U" if h\<sigma>: "\<sigma> \<in> U" for \<sigma>
    proof -
      have in_group: "\<sigma> \<in> carrier G" using h\<sigma> U_open openin_subset topspace_utopology by force
      from U_open h\<sigma> obtain E where hE: "entourage_in ?\<Phi> E \<and> E``{\<sigma>} \<subseteq> U"
        unfolding openin_utopology by blast
      then obtain V where hV: "neighborhood \<one> V \<and> right_entourage V \<subseteq> E"
        unfolding entourage_right_uniformity by fastforce
      let ?W = "{\<tau> \<in> carrier G. \<sigma> \<otimes> inv \<tau> \<in> V}"
      from hV have W_subset: "?W \<subseteq> E``{\<sigma>}" using in_group by fast
      have "(\<lambda>\<tau>. \<sigma> \<otimes> inv \<tau>) = (\<lambda>\<tau>. \<sigma> \<otimes> \<tau>) \<circ> (\<lambda>\<tau>. inv \<tau>)" by fastforce
      then have "continuous_map T T (\<lambda>\<tau>. \<sigma> \<otimes> inv \<tau>)" using continuous_map_compose inv_continuous
          translations_continuous[OF in_group] by metis
      then have "openin T ?W" using openin_continuous_map_preimage hV by fastforce
      then have "neighborhood \<sigma> ?W" using in_group r_inv hV by simp
      then show ?thesis using W_subset hE by fast
    qed
    then show "openin T U" using openin_subopen by force
  qed
  then show ?thesis using topology_eq by blast
qed

lemma translations_ucontinuous:
  assumes in_group: "\<sigma> \<in> carrier G"
  shows "ucontinuous left_uniformity left_uniformity (\<lambda>\<tau>. \<sigma> \<otimes> \<tau>)" and
    "ucontinuous right_uniformity right_uniformity (\<lambda>\<tau>. \<tau> \<otimes> \<sigma>)"
proof -
  let ?\<Phi> = left_uniformity
  have "entourage_in ?\<Phi> {(\<tau>\<^sub>1, \<tau>\<^sub>2) \<in> uspace ?\<Phi> \<times> uspace ?\<Phi>. (\<sigma> \<otimes> \<tau>\<^sub>1, \<sigma> \<otimes> \<tau>\<^sub>2) \<in> E}"
    if hE: "entourage_in ?\<Phi> E" for E
  proof -
    let ?F = "{(\<tau>\<^sub>1, \<tau>\<^sub>2) \<in> uspace ?\<Phi> \<times> uspace ?\<Phi>. (\<sigma> \<otimes> \<tau>\<^sub>1, \<sigma> \<otimes> \<tau>\<^sub>2) \<in> E}"
    from hE obtain U where hU: "neighborhood \<one> U \<and> left_entourage U \<subseteq> E"
      unfolding entourage_left_uniformity by auto
    have "(\<tau>\<^sub>1, \<tau>\<^sub>2) \<in> ?F" if "\<tau>\<^sub>1 \<in> carrier G \<and> \<tau>\<^sub>2 \<in> carrier G \<and> inv \<tau>\<^sub>1 \<otimes> \<tau>\<^sub>2 \<in> U" for \<tau>\<^sub>1 \<tau>\<^sub>2
    proof -
      have "inv (\<sigma> \<otimes> \<tau>\<^sub>1) \<otimes> (\<sigma> \<otimes> \<tau>\<^sub>2) = inv \<tau>\<^sub>1 \<otimes> \<tau>\<^sub>2"
        using that in_group m_closed inv_closed inv_mult_group m_assoc r_inv r_one
        by (smt (verit, ccfv_threshold))
      then have "(\<sigma> \<otimes> \<tau>\<^sub>1, \<sigma> \<otimes> \<tau>\<^sub>2) \<in> E" using that hU in_group m_closed by fastforce
      then show ?thesis using that by auto
    qed
    then have "left_entourage U \<subseteq> ?F" by force
    then show ?thesis unfolding entourage_left_uniformity using hU by auto
  qed
  moreover have "(\<lambda>\<tau>. \<sigma> \<otimes> \<tau>) \<in> uspace ?\<Phi> \<rightarrow> uspace ?\<Phi>"
    unfolding Pi_def using uspace_left_uniformity in_group m_closed by force
  ultimately show "ucontinuous ?\<Phi> ?\<Phi> (\<lambda>\<tau>. \<sigma> \<otimes> \<tau>)"
    unfolding ucontinuous_def by fast
next
  let ?\<Phi> = right_uniformity
  have "entourage_in ?\<Phi> {(\<tau>\<^sub>1, \<tau>\<^sub>2) \<in> uspace ?\<Phi> \<times> uspace ?\<Phi>. (\<tau>\<^sub>1 \<otimes> \<sigma>, \<tau>\<^sub>2 \<otimes> \<sigma>) \<in> E}"
    if hE: "entourage_in ?\<Phi> E" for E
  proof -
    let ?F = "{(\<tau>\<^sub>1, \<tau>\<^sub>2) \<in> uspace ?\<Phi> \<times> uspace ?\<Phi>. (\<tau>\<^sub>1 \<otimes> \<sigma>, \<tau>\<^sub>2 \<otimes> \<sigma>) \<in> E}"
    from hE obtain U where hU: "neighborhood \<one> U \<and> right_entourage U \<subseteq> E"
      unfolding entourage_right_uniformity by auto
    have "(\<tau>\<^sub>1, \<tau>\<^sub>2) \<in> ?F" if "\<tau>\<^sub>1 \<in> carrier G \<and> \<tau>\<^sub>2 \<in> carrier G \<and> \<tau>\<^sub>1 \<otimes> inv \<tau>\<^sub>2 \<in> U" for \<tau>\<^sub>1 \<tau>\<^sub>2
    proof -
      have "(\<tau>\<^sub>1 \<otimes> \<sigma>) \<otimes> inv (\<tau>\<^sub>2 \<otimes> \<sigma>) = \<tau>\<^sub>1 \<otimes> inv \<tau>\<^sub>2"
        using that in_group m_closed inv_closed inv_mult_group m_assoc r_inv r_one
        by (smt (verit, ccfv_threshold))
      then have "(\<tau>\<^sub>1 \<otimes> \<sigma>, \<tau>\<^sub>2 \<otimes> \<sigma>) \<in> E" using that hU in_group m_closed by fastforce
      then show ?thesis using that by simp
    qed
    then have "right_entourage U \<subseteq> ?F" by force
    then show ?thesis unfolding entourage_right_uniformity using hU by auto
  qed
  moreover have "(\<lambda>\<tau>. \<tau> \<otimes> \<sigma>) \<in> uspace ?\<Phi> \<rightarrow> uspace ?\<Phi>"
    unfolding Pi_def using entourage_right_uniformity in_group m_closed by force
  ultimately show "ucontinuous ?\<Phi> ?\<Phi> (\<lambda>\<tau>. \<tau> \<otimes> \<sigma>)" 
    unfolding ucontinuous_def by fast
qed

subsection \<open>The Birkhoff-Kakutani theorem\<close>
subsubsection \<open>Prenorms on groups\<close>

definition group_prenorm :: "('g \<Rightarrow> real) \<Rightarrow> bool" where
"group_prenorm N \<longleftrightarrow>
  N \<one> = 0 \<and>
  (\<forall>\<sigma> \<tau>. \<sigma> \<in> carrier G \<and> \<tau> \<in> carrier G \<longrightarrow> N (\<sigma> \<otimes> \<tau>) \<le> N \<sigma> + N \<tau>) \<and>
  (\<forall>\<sigma> \<in> carrier G. N (inv \<sigma>) = N \<sigma>)"

lemma group_prenorm_clauses[elim]:
  assumes "group_prenorm N"
  obtains 
    "N \<one> = 0" and 
    "\<And>\<sigma> \<tau>. \<sigma> \<in> carrier G \<Longrightarrow> \<tau> \<in> carrier G \<Longrightarrow> N (\<sigma> \<otimes> \<tau>) \<le> N \<sigma> + N \<tau>" and 
    "\<And>\<sigma>. \<sigma> \<in> carrier G \<Longrightarrow> N (inv \<sigma>) = N \<sigma>"
  using assms unfolding group_prenorm_def by auto

proposition group_prenorm_nonnegative:
  assumes prenorm: "group_prenorm N"
  shows "\<forall>\<sigma> \<in> carrier G. N \<sigma> \<ge> 0"
proof
  fix \<sigma> assume "\<sigma> \<in> carrier G"
  from r_inv this have "0 \<le> N \<sigma> + N \<sigma>" using assms inv_closed group_prenorm_clauses by metis
  then show "N \<sigma> \<ge> 0" by fastforce
qed

proposition group_prenorm_reverse_triangle_ineq:
  assumes prenorm: "group_prenorm N" and in_group: "\<sigma> \<in> carrier G \<and> \<tau> \<in> carrier G"
  shows "\<bar>N \<sigma> - N \<tau>\<bar> \<le> N (\<sigma> \<otimes> inv \<tau>)"
proof -
  have "\<sigma> = \<sigma> \<otimes> inv \<tau> \<otimes> \<tau>" using in_group inv_closed r_one l_inv m_assoc by metis
  then have a: "N \<sigma> \<le> N (\<sigma> \<otimes> inv \<tau>) + N \<tau>" using in_group inv_closed m_closed prenorm group_prenorm_clauses by metis
  have "inv \<tau> = inv \<sigma> \<otimes> (\<sigma> \<otimes> inv \<tau>)" using in_group inv_closed l_one l_inv m_assoc by metis 
  then have b: "N \<tau> \<le> N \<sigma> + N (\<sigma> \<otimes> inv \<tau>)" using in_group inv_closed m_closed prenorm group_prenorm_clauses by metis
  from a b show ?thesis by linarith
qed

definition induced_group_prenorm :: "('g \<Rightarrow> real) \<Rightarrow> 'g \<Rightarrow> real" where
"induced_group_prenorm f \<sigma> = (SUP \<tau> \<in> carrier G. \<bar>f (\<tau> \<otimes> \<sigma>) - f \<tau>\<bar>)"
  
lemma induced_group_prenorm_welldefined:
  fixes f :: "'g \<Rightarrow> real"
  assumes f_bounded: "\<exists>c.\<forall>\<tau> \<in> carrier G. \<bar>f \<tau>\<bar> \<le> c" and in_group: "\<sigma> \<in> carrier G"
  shows "bdd_above ((\<lambda>\<tau>. \<bar>f (\<tau> \<otimes> \<sigma>) - f \<tau>\<bar>)`(carrier G))"
proof -
  from f_bounded obtain c where hc: "\<forall>\<tau> \<in> carrier G. \<bar>f \<tau>\<bar> \<le> c" by blast
  have "\<bar>f (\<tau> \<otimes> \<sigma>) - f \<tau>\<bar> \<le> 2*c" if "\<tau> \<in> carrier G" for \<tau>
  proof -
    have "\<bar>f (\<tau> \<otimes> \<sigma>) - f \<tau>\<bar> \<le> \<bar>f (\<tau> \<otimes> \<sigma>)\<bar> + \<bar>f \<tau>\<bar>" using abs_triangle_ineq by simp
    then show ?thesis using in_group that m_closed f_bounded hc by (smt (verit, best))
  qed
  then show ?thesis unfolding bdd_above_def image_def by blast
qed

lemma bounded_function_induces_group_prenorm:
  fixes f :: "'g \<Rightarrow> real"
  assumes f_bounded: "\<exists>c.\<forall>\<sigma> \<in> carrier G. \<bar>f \<sigma>\<bar> \<le> c"
  shows "group_prenorm (induced_group_prenorm f)"
proof -
  let ?N = "\<lambda>\<sigma>. SUP \<tau> \<in> carrier G. \<bar>f (\<tau> \<otimes> \<sigma>) - f \<tau>\<bar>"
  have "?N \<one> = (SUP \<tau> \<in> carrier G. 0)" using r_one by simp 
  then have "?N \<one> = 0" using carrier_not_empty by simp
  moreover have "?N (\<sigma> \<otimes> \<tau>) \<le> ?N \<sigma> + ?N \<tau>" if h\<sigma>\<tau>: "\<sigma> \<in> carrier G \<and> \<tau> \<in> carrier G" for \<sigma> \<tau>
  proof -
    have "\<bar>f (\<rho> \<otimes> (\<sigma> \<otimes> \<tau>)) - f \<rho>\<bar> \<le> ?N \<sigma> + ?N \<tau>" if "\<rho> \<in> carrier G" for \<rho>
    proof -
      have a: "\<bar>f (\<rho> \<otimes> (\<sigma> \<otimes> \<tau>)) - f \<rho>\<bar> \<le> \<bar>f (\<rho> \<otimes> (\<sigma> \<otimes> \<tau>)) - f (\<rho> \<otimes> \<sigma>)\<bar> + \<bar>f (\<rho> \<otimes> \<sigma>) - f \<rho>\<bar>" 
        using abs_triangle_ineq by linarith
      have "\<bar>f (\<rho> \<otimes> \<sigma> \<otimes> \<tau>) - f (\<rho> \<otimes> \<sigma>)\<bar> \<le> ?N \<tau>" 
        using induced_group_prenorm_welldefined[OF f_bounded] that h\<sigma>\<tau> m_closed cSUP_upper by meson
      then have b: "\<bar>f (\<rho> \<otimes> (\<sigma> \<otimes> \<tau>)) - f (\<rho> \<otimes> \<sigma>)\<bar> \<le> ?N \<tau>" using m_assoc that h\<sigma>\<tau> by simp
      have c: "\<bar>f (\<rho> \<otimes> \<sigma>) - f \<rho>\<bar> \<le> ?N \<sigma>" using induced_group_prenorm_welldefined[OF f_bounded] h\<sigma>\<tau> that cSUP_upper by meson
      from a b c show ?thesis by argo
    qed                              
    then show ?thesis using cSUP_least carrier_not_empty by meson
  qed
  moreover have "?N (inv \<sigma>) = ?N \<sigma>" if h\<sigma>: "\<sigma> \<in> carrier G" for \<sigma>
  proof -
    have "\<bar>f (\<tau> \<otimes> inv \<sigma>) - f \<tau>\<bar> \<in> {\<bar>f (\<rho> \<otimes> \<sigma>) - f \<rho>\<bar> | \<rho>. \<rho> \<in> carrier G }" if "\<tau> \<in> carrier G" for \<tau>
    proof -
      have "\<bar>f (\<tau> \<otimes> inv \<sigma>) - f \<tau>\<bar> = \<bar>f (\<tau> \<otimes> inv \<sigma>) - f (\<tau> \<otimes> inv \<sigma> \<otimes> \<sigma>)\<bar>" 
        using h\<sigma> that m_assoc r_one l_inv by simp
      then have "\<bar>f (\<tau> \<otimes> inv \<sigma>) - f \<tau>\<bar> = \<bar>f (\<tau> \<otimes> inv \<sigma> \<otimes> \<sigma>) - f (\<tau> \<otimes> inv \<sigma>)\<bar>" by argo
      then show ?thesis using h\<sigma> that m_closed by blast
    qed
    moreover 
    have "\<bar>f (\<rho> \<otimes> \<sigma>) - f \<rho>\<bar> \<in> {\<bar>f (\<tau> \<otimes> inv \<sigma>) - f \<tau>\<bar> | \<tau>. \<tau> \<in> carrier G }" if "\<rho> \<in> carrier G" for \<rho>
    proof -
      have "\<bar>f (\<rho> \<otimes> \<sigma>) - f \<rho>\<bar> = \<bar>f (\<rho> \<otimes> \<sigma>) - f (\<rho> \<otimes> \<sigma> \<otimes> inv \<sigma>)\<bar>" 
        using h\<sigma> that m_assoc r_one r_inv by simp
      then have "\<bar>f (\<rho> \<otimes> \<sigma>) - f \<rho>\<bar> = \<bar>f (\<rho> \<otimes> \<sigma> \<otimes> inv \<sigma>) - f (\<rho> \<otimes> \<sigma>)\<bar>" by argo
      then show ?thesis using h\<sigma> that by blast
    qed
    ultimately have "{\<bar>f (\<tau> \<otimes> inv \<sigma>) - f \<tau>\<bar> | \<tau>. \<tau> \<in> carrier G} = {\<bar>f (\<rho> \<otimes> \<sigma>) - f \<rho>\<bar> | \<rho>. \<rho> \<in> carrier G}" by blast
    then show ?thesis by (simp add: setcompr_eq_image)
  qed
  ultimately show ?thesis unfolding induced_group_prenorm_def group_prenorm_def by fast
qed

lemma neighborhood_1_translation:
  assumes "neighborhood \<one> U" and "\<sigma> \<in> carrier G \<or> \<sigma> \<in> topspace T"
  shows "neighborhood \<sigma> (\<sigma> <# U)"
proof -
  have "openin T (\<sigma> <# U)" using assms open_set_translations(1) by simp
  then show ?thesis unfolding l_coset_def using assms r_one by force
qed
           
proposition group_prenorm_continuous_if_continuous_at_1:
  assumes prenorm: "group_prenorm N" and 
    continuous_at_1: "\<forall>\<epsilon>>0.\<exists>U. neighborhood \<one> U \<and> (\<forall>\<sigma>\<in>U. N \<sigma> < \<epsilon>)"
  shows "continuous_map T euclideanreal N"
proof -
  have "\<exists>V. neighborhood \<sigma> V \<and> (\<forall>\<tau>\<in>V. N \<tau> \<in> Met_TC.mball (N \<sigma>) \<epsilon>)" 
    if h\<sigma>: "\<sigma> \<in> topspace T" and h\<epsilon>: "\<epsilon> > 0" for \<sigma> \<epsilon>
  proof -
    from continuous_at_1 obtain U where hU: "neighborhood \<one> U \<and> (\<forall>\<tau>\<in>U. N \<tau> < \<epsilon>)" using h\<epsilon> by presburger
    then have "neighborhood \<sigma> (\<sigma> <# U)" using h\<sigma> neighborhood_1_translation by blast
    moreover have "N (\<sigma> \<otimes> \<tau>) \<in> Met_TC.mball (N \<sigma>) \<epsilon>" if "\<tau> \<in> U" for \<tau>
    proof -
      have in_group: "\<sigma> \<in> carrier G \<and> \<tau> \<in> carrier G" using h\<sigma> that openin_subset hU by blast
      then have "(inv \<sigma>) \<otimes> (\<sigma> \<otimes> \<tau>) = \<tau>" using l_inv l_one m_assoc inv_closed by metis
      then have "\<bar>N (inv \<sigma>) - N (inv (\<sigma> \<otimes> \<tau>))\<bar> \<le> N \<tau>" using group_prenorm_reverse_triangle_ineq 
          in_group inv_closed m_closed by (metis inv_inv prenorm)
      then have "\<bar>N \<sigma> - N (\<sigma> \<otimes> \<tau>)\<bar> < \<epsilon>" 
        using prenorm in_group m_closed inv_closed hU that by fastforce
      then show ?thesis unfolding Met_TC.mball_def dist_real_def by fast
    qed
    ultimately show ?thesis unfolding l_coset_def by blast
  qed
  then show ?thesis using Metric_space.continuous_map_to_metric
    by (metis Met_TC.Metric_space_axioms mtopology_is_euclidean)
qed

subsubsection \<open>A prenorm respecting the group topology\<close>

context
  fixes U :: "nat \<Rightarrow> 'g set"
  assumes U_neighborhood: "\<forall>n. neighborhood \<one> (U n)"
  assumes U_props: "\<forall>n. symmetric (U n) \<and> (U (n + 1)) <#> (U (n + 1)) \<subseteq> (U n)"
begin

private fun V :: "nat \<Rightarrow> nat \<Rightarrow> 'g set" where
"V m n = (
  if m = 0 then {} else
  if m = 1 then U n else
  if m > 2^n then carrier G else
  if even m then V (m div 2) (n - 1) else
  V ((m - 1) div 2) (n - 1) <#> U n
)"

private lemma U_in_group: "U k \<subseteq> carrier G" using U_neighborhood open_set_in_carrier by fast

private lemma V_in_group:
  shows "V m n \<subseteq> carrier G"
proof (induction n arbitrary: m)
  case (Suc n)
  then have "V ((m - 1) div 2) n <#> U (Suc n) \<subseteq> carrier G"
    unfolding set_mult_def using U_in_group by fast
  then show ?case using U_in_group Suc by simp
qed (auto simp: U_in_group)

private lemma V_mult:
  shows "m \<ge> 1 \<Longrightarrow> V m n <#> U n \<subseteq> V (m + 1) n"
proof (induction n arbitrary: m)
  case 0
  then have "V (m + 1) 0 = carrier G" by simp
  then show ?case unfolding set_mult_def using V_in_group U_in_group by fast
next
  case (Suc n)
  then show ?case
  proof (cases "m + 1 > 2^(Suc n)")
    case True
    then have "V (m + 1) (Suc n) = carrier G" by force
    then show ?thesis unfolding set_mult_def using V_in_group U_in_group by blast
  next
    case m_in_bounds: False
    then show ?thesis
    proof (cases "m = 1")
      case True
      then show ?thesis using U_in_group U_props by force
    next
      case m_not_1: False
      then show ?thesis
      proof (cases "even m")
        case True
        then have "V m (Suc n) <#> U (Suc n) = V (m + 1) (Suc n)" using m_in_bounds m_not_1 Suc(2) by auto
        then show ?thesis by blast
      next
        case m_odd: False
        have U_mult: "U (Suc n) <#> U (Suc n) \<subseteq> U n" using U_props by simp 
        have not_zero: "(m - 1) div 2 \<ge> 1" using Suc(2) m_not_1 m_odd by presburger
        have arith: "(m - 1) div 2 + 1 = (m + 1) div 2" using Suc(2) by simp
        have "V m (Suc n) <#> U (Suc n) = V ((m - 1) div 2) n <#> U (Suc n) <#> U (Suc n)" using m_odd m_in_bounds m_not_1 Suc(2) by simp
        also have "... = V ((m - 1) div 2) n <#> (U (Suc n) <#> U (Suc n))" using set_mult_assoc V_in_group U_in_group by simp
        also have "... \<subseteq> V ((m - 1) div 2) n <#> U n" using mono_set_mult U_mult by blast
        also have "... \<subseteq> V ((m - 1) div 2 + 1) n" using Suc(1) not_zero by blast
        also have "...  = V ((m + 1) div 2) n" using arith by presburger
        also have "... =  V (m + 1) (Suc n)" using m_odd m_not_1 m_in_bounds Suc(2) by simp
        finally show ?thesis by blast
      qed
    qed
  qed
qed

private lemma V_mono:
  assumes smaller: "(real m\<^sub>1)/2^n\<^sub>1 \<le> (real m\<^sub>2)/2^n\<^sub>2" and not_zero: "m\<^sub>1 \<ge> 1 \<and> m\<^sub>2 \<ge> 1"
  shows "V m\<^sub>1 n\<^sub>1 \<subseteq> V m\<^sub>2 n\<^sub>2"
proof -
  have "V m n \<subseteq> V (m + 1) n" if "m \<ge> 1" for m n
  proof -
    have "V m n <#> U n \<subseteq> V (m + 1) n" using V_mult U_props that by presburger
    moreover have "V m n \<subseteq> carrier G \<and> U n \<subseteq> carrier G" using U_in_group V_in_group by auto
    ultimately show ?thesis using set_mult_one_subset U_neighborhood by blast
  qed
  then have subset_suc: "V m n \<subseteq> V (m + 1) n" for m n by simp
  have "V m n \<subseteq> V (m + k) n" for m n k
  proof (induction k)
    case (Suc k)
    then show ?case unfolding Suc_eq_plus1 using subset_suc Suc
      by (metis (no_types, opaque_lifting) add.assoc dual_order.trans)
  qed (simp)
  then have a: "V m n \<subseteq> V m' n" if "m' \<ge> m" for m m' n using that le_Suc_ex by blast
  have b: "V m n = V (m * 2^k) (n+k)" if "m \<ge> 1" for m n k
  proof (induction k)
    case (Suc k)
    have "V (m * 2^k * 2) (n + k + 1) = V (m * 2^k) (n + k)" using that by simp
    then show ?case unfolding Suc_eq_plus1 using Suc by simp
  qed (auto)
  show ?thesis
  proof (cases "n\<^sub>1 \<le> n\<^sub>2")
    case True
    have "(real m\<^sub>1)/2^n\<^sub>1 = (real (m\<^sub>1 * 2^(n\<^sub>2 - n\<^sub>1)))/(2^n\<^sub>1 * 2^(n\<^sub>2 - n\<^sub>1))" by fastforce
    also have "... = (real (m\<^sub>1 * 2^(n\<^sub>2 - n\<^sub>1)))/2^n\<^sub>2" using True by (metis le_add_diff_inverse power_add)
    finally have "(real (m\<^sub>1 * 2^(n\<^sub>2 - n\<^sub>1)))/2^n\<^sub>2 \<le> (real m\<^sub>2)/2^n\<^sub>2" using smaller by fastforce
    then have ineq: "m\<^sub>1 * 2^(n\<^sub>2 - n\<^sub>1) \<le> m\<^sub>2"
      by (smt (verit) divide_cancel_right divide_right_mono linorder_le_cases of_nat_eq_iff of_nat_mono order_antisym_conv power_not_zero zero_le_power)
    from b have "V m\<^sub>1 n\<^sub>1 = V (m\<^sub>1 * 2^(n\<^sub>2 - n\<^sub>1)) (n\<^sub>1 + (n\<^sub>2 - n\<^sub>1))" using not_zero by blast
    also have "... = V (m\<^sub>1 * 2^(n\<^sub>2 - n\<^sub>1)) n\<^sub>2" using True by force
    finally show ?thesis using a[OF ineq] by blast
  next
    case False
    then have n\<^sub>2_leq_n\<^sub>1: "n\<^sub>2 \<le> n\<^sub>1" by simp
    have "(real m\<^sub>2)/2^n\<^sub>2 = (real (m\<^sub>2 * 2^(n\<^sub>1 - n\<^sub>2)))/(2^n\<^sub>2 * 2^(n\<^sub>1 - n\<^sub>2))" by fastforce
    also have "... = (real (m\<^sub>2 * 2^(n\<^sub>1 - n\<^sub>2)))/2^n\<^sub>1" using n\<^sub>2_leq_n\<^sub>1 by (metis le_add_diff_inverse power_add)
    finally have "(real (m\<^sub>2 * 2^(n\<^sub>1 - n\<^sub>2)))/2^n\<^sub>1 \<ge> (real m\<^sub>1)/2^n\<^sub>1" using smaller by fastforce
    then have ineq: "m\<^sub>2 * 2^(n\<^sub>1 - n\<^sub>2) \<ge> m\<^sub>1"
      by (smt (verit) divide_cancel_right divide_right_mono linorder_le_cases of_nat_eq_iff of_nat_mono order_antisym_conv power_not_zero zero_le_power)
    from b have "V m\<^sub>2 n\<^sub>2 = V (m\<^sub>2 * 2^(n\<^sub>1 - n\<^sub>2)) (n\<^sub>2 + (n\<^sub>1 - n\<^sub>2))" using not_zero by blast
    also have "... = V (m\<^sub>2 * 2^(n\<^sub>1 - n\<^sub>2)) n\<^sub>1" using n\<^sub>2_leq_n\<^sub>1 by force
    finally show ?thesis using a[OF ineq] by blast
  qed
qed

private lemma approx_number_by_multiples:
  assumes hx: "x \<ge> 0" and hc: "c > 0"
  shows "\<exists>k :: nat \<ge> 1. (real (k-1))/c \<le> x \<and> x < (real k)/c"
proof -
  let ?k = "\<lfloor>x * c\<rfloor> + 1"
  have "?k \<ge> 1" using assms by simp
  moreover from this have "real (nat ?k) = ?k" by auto
  moreover have "(?k-1)/c \<le> x \<and> x < ?k/c" 
    using assms by (simp add: mult_imp_div_pos_le pos_less_divide_eq)
  ultimately show ?thesis
    by (smt (verit) nat_diff_distrib nat_le_eq_zle nat_one_as_int of_nat_nat)
qed

lemma construction_of_prenorm_respecting_topology:
  shows "\<exists>N. group_prenorm N \<and> 
    (\<forall>n. {\<sigma> \<in> carrier G. N \<sigma> < 1/2^n} \<subseteq> U n) \<and> 
    (\<forall>n. U n \<subseteq> {\<sigma> \<in> carrier G. N \<sigma> \<le> 2/2^n})"
proof -
  define f :: "'g \<Rightarrow> real" where "f \<sigma> = Inf {(real m)/2^n | m n. \<sigma> \<in> V m n}" for \<sigma>
  define N :: "'g \<Rightarrow> real" where "N = induced_group_prenorm f"

  have "\<sigma> \<in> V 2 0" if "\<sigma> \<in> carrier G" for \<sigma> using that by auto
  then have contains_2: "(real 2)/2^0 \<in> {(real m)/2^n | m n. \<sigma> \<in> V m n}" if "\<sigma> \<in> carrier G" for \<sigma> using that by blast
  then have nonempty: "{(real m)/2^n | m n. \<sigma> \<in> V m n} \<noteq> {}" if "\<sigma> \<in> carrier G" for \<sigma> using that by fast
  have positive: "(real m)/2^n \<ge> 0" for m n by simp
  then have bdd_below: "bdd_below {(real m)/2^n | m n. \<sigma> \<in> V m n}" for \<sigma> by fast
  have f_bounds: "0 \<le> f \<sigma> \<and> f \<sigma> \<le> 2" if h\<sigma>: "\<sigma> \<in> carrier G" for \<sigma>
  proof -
    from bdd_below have "f \<sigma> \<le> (real 2)/2^0" unfolding f_def using cInf_lower contains_2[OF h\<sigma>] by meson
    moreover have "0 \<le> f \<sigma>" using cInf_greatest contains_2[OF h\<sigma>] unfolding f_def using positive
      by (smt (verit, del_insts) Collect_mem_eq empty_Collect_eq mem_Collect_eq)
    ultimately show ?thesis by fastforce
  qed
  then have N_welldefined: "bdd_above ((\<lambda>\<tau>. \<bar>f (\<tau> \<otimes> \<sigma>) - f \<tau>\<bar>) ` carrier G)" if "\<sigma> \<in> carrier G" for \<sigma>
    using induced_group_prenorm_welldefined that by (metis (full_types) abs_of_nonneg)

  have in_V_if_f_smaller: "\<sigma> \<in> V m n" if h\<sigma>: "\<sigma> \<in> carrier G" and smaller: "f \<sigma> < (real m)/2^n" for \<sigma> m n
  proof -
    from cInf_lessD obtain q where hq: "q \<in> {(real m)/2^n | m n. \<sigma> \<in> V m n} \<and> q < (real m)/2^n"
      using smaller nonempty[OF h\<sigma>] unfolding f_def by (metis (mono_tags, lifting))
    then obtain m' n' where hm'n': "\<sigma> \<in> V m' n' \<and> q = (real m')/2^n'" by fast
    moreover have "m' \<ge> 1"
    proof (rule ccontr)
      assume "\<not> m' \<ge> 1"
      then have "V m' n' = {}" by force
      then show "False" using hm'n' by blast
    qed
    moreover have "m \<ge> 1" using f_bounds smaller h\<sigma>
      by (metis divide_eq_0_iff less_numeral_extra(3) less_one linorder_le_less_linear nle_le of_nat_0 order_less_imp_le)
    ultimately have "V m' n' \<subseteq> V m n" using V_mono hq U_props open_set_in_carrier by simp
    then show ?thesis using hm'n' by fast
  qed
  have f_1_vanishes: "f \<one> = 0"
  proof (rule ccontr)
    assume "f \<one> \<noteq> 0"
    then have "f \<one> > 0" using f_bounds by fastforce
    then obtain n where hn: "f \<one> > (real 1)/2^n"
      by (metis divide_less_eq_1 of_nat_1 one_less_numeral_iff power_one_over real_arch_pow_inv semiring_norm(76) zero_less_numeral)
    have "\<one> \<in> V 1 n" using U_neighborhood by simp
    then have "(real 1)/2^n \<in> {(real m)/2^n |m n. \<one> \<in> V m n}" by fast
    then show "False" using hn cInf_lower bdd_below[of \<one>] unfolding f_def by (smt (verit, ccfv_threshold))
  qed
  have in_U_if_N_small: "\<sigma> \<in> U n" if in_group: "\<sigma> \<in> carrier G" and N_small: "N \<sigma> < 1/2^n" for \<sigma> n
  proof -
    have "f \<sigma> = \<bar>f (\<one> \<otimes> \<sigma>) - f \<one>\<bar>" using in_group l_one f_1_vanishes f_bounds by force
    moreover have "... \<le> N \<sigma>" unfolding N_def induced_group_prenorm_def
      using cSUP_upper N_welldefined[OF in_group] by (metis (mono_tags, lifting) one_closed)
    ultimately have "\<sigma> \<in> V 1 n" using in_V_if_f_smaller[OF in_group] N_small by (smt (verit) of_nat_1) 
    then show ?thesis by fastforce
  qed
  have N_bounds: "N \<sigma> \<le> 2/2^n" if h\<sigma>: "\<sigma> \<in> U n" for \<sigma> n
  proof -
    have diff_bounded: "f (\<tau> \<otimes> \<sigma>) - f \<tau> \<le> 2/2^n \<and> f (\<tau> \<otimes> inv \<sigma>) - f \<tau> \<le> 2/2^n" if h\<tau>: "\<tau> \<in> carrier G" for \<tau>
    proof -
      obtain k where hk: "k \<ge> 1 \<and> (real (k-1))/2^n \<le> f \<tau> \<and> f \<tau> < (real k)/2^n"
        using approx_number_by_multiples[of "f \<tau>" "2^n"] f_bounds[OF h\<tau>] by auto
      then have "\<tau> \<in> V k n" using in_V_if_f_smaller[OF h\<tau>] by blast
      moreover have "\<sigma> \<in> V 1 n \<and> inv \<sigma> \<in> V 1 n" using h\<sigma> U_props by auto
      moreover have "V k n <#> V 1 n \<subseteq> V (k + 1) n"
        using V_mult U_props open_set_in_carrier hk by auto
      ultimately have "\<tau> \<otimes> \<sigma> \<in> V (k + 1) n \<and> \<tau> \<otimes> inv \<sigma> \<in> V (k + 1) n" 
        unfolding set_mult_def by fast
      then have a: "(real (k + 1))/2^n \<in> {(real m)/2^n | m n. \<tau> \<otimes> \<sigma> \<in> V m n}
        \<and> (real (k + 1))/2^n \<in> {(real m)/2^n | m n. \<tau> \<otimes> inv \<sigma> \<in> V m n}" by fast
      then have "f (\<tau> \<otimes> \<sigma>) \<le> (real (k + 1))/2^n" 
        unfolding f_def using cInf_lower[of "(real (k + 1))/2^n"] bdd_below by presburger
      moreover from a have "f (\<tau> \<otimes> inv \<sigma>) \<le> (real (k + 1))/2^n" 
        unfolding f_def using cInf_lower[of "(real (k + 1))/2^n"] bdd_below by presburger
      ultimately show ?thesis using hk
        by (smt (verit, ccfv_SIG) diff_divide_distrib of_nat_1 of_nat_add of_nat_diff)
    qed
    have "\<bar>f (\<rho> \<otimes> \<sigma>) - f \<rho>\<bar> \<le> 2/2^n" if h\<rho>: "\<rho> \<in> carrier G" for \<rho>
    proof -
      have in_group: "\<sigma> \<in> carrier G" using h\<sigma> U_in_group by fast
      then have "f (\<rho> \<otimes> \<sigma> \<otimes> inv \<sigma>) - f (\<rho> \<otimes> \<sigma>) \<le> 2/2^n" using diff_bounded[of "\<rho> \<otimes> \<sigma>"] h\<rho> m_closed by fast
      moreover have "\<rho> \<otimes> \<sigma> \<otimes> inv \<sigma> = \<rho>" using m_assoc r_inv r_one in_group inv_closed h\<rho> by presburger
      ultimately have "f \<rho> - f (\<rho> \<otimes> \<sigma>) \<le> 2/2^n" by force
      moreover have "f (\<rho> \<otimes> \<sigma>) - f \<rho> \<le> 2/2^n" using diff_bounded[OF h\<rho>] by fast
      ultimately show ?thesis by force
    qed
    then show ?thesis unfolding N_def induced_group_prenorm_def using cSUP_least carrier_not_empty by meson
  qed
  then have "U n \<subseteq> {\<sigma> \<in> carrier G. N \<sigma> \<le> 2/2^n}" for n using U_in_group by blast
  moreover have "group_prenorm N" unfolding N_def 
    using bounded_function_induces_group_prenorm f_bounds by (metis abs_of_nonneg)
  ultimately show ?thesis using in_U_if_N_small by blast
qed
end

subsubsection \<open>Proof of Birkhoff-Kakutani\<close>

lemma first_countable_neighborhoods_of_1_sequence:
  assumes "first_countable T"
  shows "\<exists>U :: nat \<Rightarrow> 'g set. 
    (\<forall>n. neighborhood \<one> (U n) \<and> symmetric (U n) \<and> U (n + 1) <#> U (n + 1) \<subseteq> U n) \<and> 
    (\<forall>W. neighborhood \<one> W \<longrightarrow> (\<exists>n. U n \<subseteq> W))"
proof -
  from assms obtain \<B> where h\<B>: 
    "countable \<B> \<and> (\<forall>W\<in>\<B>. openin T W) \<and> (\<forall>U. neighborhood \<one> U \<longrightarrow> (\<exists>W\<in>\<B>. \<one> \<in> W \<and> W \<subseteq> U))"
    unfolding first_countable_def by fastforce
  define \<BB> :: "'g set set" where "\<BB> = insert (carrier G) {W \<in> \<B>. \<one> \<in> W}"
  define B :: "nat \<Rightarrow> 'g set" where "B = from_nat_into \<BB>"
  have "\<BB> \<noteq> {} \<and> (\<forall>W\<in>\<BB>. neighborhood \<one> W)" unfolding \<BB>_def using h\<B>
    by (metis group_is_space insert_iff insert_not_empty mem_Collect_eq one_closed openin_topspace)
  then have B_neighborhood: "\<forall>n. neighborhood \<one> (B n)" unfolding B_def by (simp add: from_nat_into)
  define P where "P n V \<longleftrightarrow> V \<subseteq> B n \<and> neighborhood \<one> V \<and> symmetric V" for n V
  define Q where "Q (n :: nat) V W \<longleftrightarrow> W <#> W \<subseteq> V" for n V W
  have "\<exists>V. P 0 V"
  proof -
    obtain W where "neighborhood \<one> W \<and> symmetric W \<and> W <#> W \<subseteq> B 0" 
      using neighborhoods_of_1 B_neighborhood by fastforce
    moreover from this have "W \<subseteq> B 0" using set_mult_one_subset open_set_in_carrier by blast
    ultimately show ?thesis unfolding P_def by auto
  qed
  moreover have "\<exists>W. P (Suc n) W \<and> Q n V W" if "P n V" for n V
  proof -
    have "neighborhood \<one> (V \<inter> B (Suc n))" using B_neighborhood that unfolding P_def by auto
    then obtain W where "neighborhood \<one> W \<and> symmetric W \<and> W <#> W \<subseteq> V \<inter> B (Suc n)" 
      using neighborhoods_of_1 by fastforce
    moreover from this have "W \<subseteq> B (Suc n)" 
      using set_mult_one_subset[of W W] open_set_in_carrier[of W] by fast
    ultimately show ?thesis unfolding P_def Q_def by auto
  qed
  ultimately obtain U where hU: "\<forall>n. P n (U n) \<and> Q n (U n) (U (Suc n))"
    using dependent_nat_choice by metis
  moreover have "\<exists>n. U n \<subseteq> W" if "neighborhood \<one> W" for W
  proof -
    from that obtain W' where hW': "W' \<in> \<B> \<and> \<one> \<in> W' \<and> W' \<subseteq> W" using h\<B> by blast
    then have "W' \<in> \<BB> \<and> countable \<BB>" unfolding \<BB>_def using h\<B> by simp
    then obtain n where "B n = W'" unfolding B_def using from_nat_into_to_nat_on by fast
    then show ?thesis using hW' hU unfolding P_def by blast
  qed
  ultimately show ?thesis unfolding P_def Q_def by auto
qed

definition "left_invariant_metric \<Delta> \<longleftrightarrow> Metric_space (carrier G) \<Delta> \<and>
  (\<forall>\<sigma> \<tau> \<rho>. \<sigma> \<in> carrier G \<and> \<tau> \<in> carrier G \<and> \<rho> \<in> carrier G \<longrightarrow> \<Delta> (\<rho> \<otimes> \<sigma>) (\<rho> \<otimes> \<tau>) = \<Delta> \<sigma> \<tau>)"

definition "right_invariant_metric \<Delta> \<longleftrightarrow> Metric_space (carrier G) \<Delta> \<and>
  (\<forall>\<sigma> \<tau> \<rho>. \<sigma> \<in> carrier G \<and> \<tau> \<in> carrier G \<and> \<rho> \<in> carrier G \<longrightarrow> \<Delta> (\<sigma> \<otimes> \<rho>) (\<tau> \<otimes> \<rho>) = \<Delta> \<sigma> \<tau>)"

lemma left_invariant_metricE:
  assumes "left_invariant_metric \<Delta>" "\<sigma> \<in> carrier G" "\<tau> \<in> carrier G" "\<rho> \<in> carrier G"
  shows "\<Delta> (\<rho> \<otimes> \<sigma>) (\<rho> \<otimes> \<tau>) = \<Delta> \<sigma> \<tau>"
  using assms unfolding left_invariant_metric_def by blast

lemma right_invariant_metricE:
  assumes "right_invariant_metric \<Delta>" "\<sigma> \<in> carrier G" "\<tau> \<in> carrier G" "\<rho> \<in> carrier G"
  shows "\<Delta> (\<sigma> \<otimes> \<rho>) (\<tau> \<otimes> \<rho>) = \<Delta> \<sigma> \<tau>"
  using assms unfolding right_invariant_metric_def by blast

theorem Birkhoff_Kakutani_left:
  assumes Hausdorff: "Hausdorff_space T" and first_countable: "first_countable T"
  shows "\<exists>\<Delta>. left_invariant_metric \<Delta> \<and> Metric_space.mtopology (carrier G) \<Delta> = T"
proof -
  from first_countable obtain U :: "nat \<Rightarrow> 'g set" where 
    U_props: "\<forall>n. neighborhood \<one> (U n) \<and> symmetric (U n) \<and> U (n + 1) <#> U (n + 1) \<subseteq> U n" and
    neighborhood_base: "\<forall>W. neighborhood \<one> W \<longrightarrow> (\<exists>n. U n \<subseteq> W)"
    using first_countable_neighborhoods_of_1_sequence by auto
  from U_props obtain N where
    prenorm: "group_prenorm N" and
    norm_ball_in_U: "\<forall>n. {\<sigma> \<in> carrier G. N \<sigma> < 1/2^n} \<subseteq> U n" and
    U_in_norm_ball: "\<forall>n. U n \<subseteq> {\<sigma> \<in> carrier G. N \<sigma> \<le> 2/2^n}"
    using construction_of_prenorm_respecting_topology by meson
  have continuous: "continuous_map T euclideanreal N" using prenorm
  proof (rule group_prenorm_continuous_if_continuous_at_1, intro allI impI)
    fix \<epsilon> :: real assume "\<epsilon> > 0"
    then obtain n where hn: "1/2^n < \<epsilon>" 
      by (metis divide_less_eq_1_pos one_less_numeral_iff power_one_over real_arch_pow_inv semiring_norm(76) zero_less_numeral)
    then have "N \<sigma> < \<epsilon>" if "\<sigma> \<in> U (n + 1)" for \<sigma> using that U_in_norm_ball by fastforce
    then show "\<exists>U. neighborhood \<one> U \<and> (\<forall>\<sigma>\<in>U. N \<sigma> < \<epsilon>)" using U_props by meson
  qed
  let ?B = "\<lambda>\<epsilon>. {\<sigma> \<in> carrier G. N \<sigma> < \<epsilon>}"
  let ?\<Delta> = "\<lambda>\<sigma> \<tau>. N (inv \<sigma> \<otimes> \<tau>)"
  let ?\<delta> = "\<lambda>\<sigma> \<tau>. if \<sigma> \<in> carrier G \<and> \<tau> \<in> carrier G then ?\<Delta> \<sigma> \<tau> else 42"
  have "?\<Delta> \<sigma> \<tau> \<ge> 0" if "\<sigma> \<in> carrier G \<and> \<tau> \<in> carrier G" for \<sigma> \<tau>
    using group_prenorm_nonnegative prenorm that by blast
  moreover have "?\<Delta> \<sigma> \<tau> = ?\<Delta> \<tau> \<sigma>" if "\<sigma> \<in> carrier G \<and> \<tau> \<in> carrier G" for \<sigma> \<tau>
  proof -
    have "inv \<tau> \<otimes> \<sigma> = inv (inv \<sigma> \<otimes> \<tau>)" using inv_mult_group inv_inv that by auto
    then show ?thesis using prenorm that by fastforce
  qed
  moreover have "?\<Delta> \<sigma> \<tau> = 0 \<longleftrightarrow> \<sigma> = \<tau>" if "\<sigma> \<in> carrier G \<and> \<tau> \<in> carrier G" for \<sigma> \<tau>
  proof
    assume "?\<Delta> \<sigma> \<tau> = 0"
    then have "inv \<sigma> \<otimes> \<tau> \<in> U n" for n using norm_ball_in_U that by fastforce
    then have "inv \<sigma> \<otimes> \<tau> \<in> W" if "neighborhood \<one> W" for W using neighborhood_base that by auto
    then have "inv \<sigma> \<otimes> \<tau> = \<one>" using Hausdorff_space_sing_Inter_opens[of T \<one>] Hausdorff by blast
    then show "\<sigma> = \<tau>" using inv_comm inv_equality that by fastforce
  next
    assume "\<sigma> = \<tau>"
    then show "?\<Delta> \<sigma> \<tau> = 0" using that prenorm by force
  qed
  moreover have "?\<Delta> \<sigma> \<rho> \<le> ?\<Delta> \<sigma> \<tau> + ?\<Delta> \<tau> \<rho>" if "\<sigma> \<in> carrier G \<and> \<tau> \<in> carrier G \<and> \<rho> \<in> carrier G" for \<sigma> \<tau> \<rho>
  proof -
    have "inv \<sigma> \<otimes> \<rho> = (inv \<sigma> \<otimes> \<tau>) \<otimes> (inv \<tau> \<otimes> \<rho>)" using m_assoc[symmetric] that by (simp add: inv_solve_right)
    then show ?thesis using prenorm that by auto
  qed                        
  ultimately have metric: "Metric_space (carrier G) ?\<delta>" unfolding Metric_space_def by auto
  then interpret Metric_space "carrier G" ?\<delta> by blast
  have "?\<Delta> (\<rho> \<otimes> \<sigma>) (\<rho> \<otimes> \<tau>) = ?\<Delta> \<sigma> \<tau>" if "\<sigma> \<in> carrier G \<and> \<tau> \<in> carrier G \<and> \<rho> \<in> carrier G" for \<sigma> \<tau> \<rho>
  proof -
    have "inv \<sigma> \<otimes> \<tau> = inv (\<rho> \<otimes> \<sigma>) \<otimes> (\<rho> \<otimes> \<tau>)" using that m_assoc[symmetric] by (simp add: inv_solve_left inv_solve_right)
    then show ?thesis by simp
  qed
  then have left_invariant: "left_invariant_metric ?\<delta>" 
    unfolding left_invariant_metric_def using metric by auto
  have mball_coset_of_norm_ball: "mball \<sigma> \<epsilon> = \<sigma> <# ?B \<epsilon>" if h\<sigma>: "\<sigma> \<in> carrier G" for \<sigma> \<epsilon>
  proof -
    have "mball \<sigma> \<epsilon> = {\<tau> \<in> carrier G. N (inv \<sigma> \<otimes> \<tau>) < \<epsilon>}" unfolding mball_def using h\<sigma> by auto
    also have "... = \<sigma> <# (?B \<epsilon>)"
    proof -
      have "\<tau> \<in> \<sigma> <# (?B \<epsilon>)" if "\<tau> \<in> carrier G \<and> N (inv \<sigma> \<otimes> \<tau>) < \<epsilon>" for \<tau>
      proof -
        have "\<sigma> \<otimes> (inv \<sigma> \<otimes> \<tau>) = \<tau>" using h\<sigma> that by (metis inv_closed inv_solve_left m_closed)
        moreover have "inv \<sigma> \<otimes> \<tau> \<in> ?B \<epsilon>" using h\<sigma> that by fastforce
        ultimately show ?thesis unfolding l_coset_def by force
      qed
      moreover have "\<tau> \<in> carrier G \<and> N (inv \<sigma> \<otimes> \<tau>) < \<epsilon>" if "\<tau> \<in> \<sigma> <# (?B \<epsilon>)" for \<tau>
      proof -
        from that obtain \<rho> where "\<rho> \<in> ?B \<epsilon> \<and> \<tau> = \<sigma> \<otimes> \<rho>" unfolding l_coset_def by blast
        moreover from this have "inv \<sigma> \<otimes> \<tau> = \<rho>" using h\<sigma> by (simp add: inv_solve_left')
        ultimately show ?thesis using h\<sigma> by simp
      qed
      ultimately show ?thesis by blast
    qed
    finally show ?thesis by presburger
  qed
  define ball where "ball S \<longleftrightarrow> (\<exists>\<sigma> \<epsilon>. \<sigma> \<in> carrier G \<and> S = mball \<sigma> \<epsilon>)" for S
  have "openin mtopology V" if "ball V" for V using that unfolding ball_def by fast
  moreover have "\<exists>W. ball W \<and> \<sigma> \<in> W \<and> W \<subseteq> V" if "openin mtopology V \<and> \<sigma> \<in> V" for \<sigma> V
    unfolding ball_def using openin_mtopology that by (smt (verit, best) centre_in_mball_iff subset_iff)
  ultimately have openin_metric: "openin mtopology = arbitrary union_of ball" 
    by (simp add: openin_topology_base_unique)
  have "openin T V" if "ball V" for V
  proof -
    from that obtain \<sigma> \<epsilon> where "\<sigma> \<in> carrier G \<and> V = \<sigma> <# ?B \<epsilon>" 
      unfolding ball_def using mball_coset_of_norm_ball by blast
    moreover have "openin T (?B \<epsilon>)" using continuous
      by (simp add: continuous_map_upper_lower_semicontinuous_lt)
    ultimately show ?thesis using open_set_translations(1) by presburger
  qed
  moreover have "\<exists>W. ball W \<and> \<sigma> \<in> W \<and> W \<subseteq> V" if "neighborhood \<sigma> V" for \<sigma> V
  proof -
    from that have in_group: "\<sigma> \<in> carrier G" using open_set_in_carrier by fast
    then have "neighborhood \<one> (inv \<sigma> <# V)" 
      using l_coset_def open_set_translations(1) that l_inv by fastforce
    then obtain n where "U n \<subseteq> inv \<sigma> <# V" using neighborhood_base by presburger
    then have "?B (1/2^n) \<subseteq> inv \<sigma> <# V" using norm_ball_in_U by blast
    then have "\<sigma> <# ?B (1/2^n) \<subseteq> \<sigma> <# (inv \<sigma> <# V)" unfolding l_coset_def by fast
    also have "... = V" using in_group that open_set_in_carrier by (simp add: lcos_m_assoc lcos_mult_one)
    finally have "mball \<sigma> (1/2^n) \<subseteq> V" using mball_coset_of_norm_ball in_group by blast
    then show ?thesis unfolding ball_def
      by (smt (verit) centre_in_mball_iff divide_pos_pos in_group one_add_one zero_less_power zero_less_two)
  qed
  ultimately have "openin T = arbitrary union_of ball" by (simp add: openin_topology_base_unique)
  then show ?thesis using left_invariant openin_metric topology_eq by fastforce
qed

theorem Birkhoff_Kakutani_right:
  assumes Hausdorff: "Hausdorff_space T" and first_countable: "first_countable T"
  shows "\<exists>\<Delta>. right_invariant_metric \<Delta> \<and> Metric_space.mtopology (carrier G) \<Delta> = T"
proof -
  from first_countable obtain U :: "nat \<Rightarrow> 'g set" where 
    U_props: "\<forall>n. neighborhood \<one> (U n) \<and> symmetric (U n) \<and> U (n + 1) <#> U (n + 1) \<subseteq> U n" and
    neighborhood_base: "\<forall>W. neighborhood \<one> W \<longrightarrow> (\<exists>n. U n \<subseteq> W)"
    using first_countable_neighborhoods_of_1_sequence by auto
  from U_props obtain N where
    prenorm: "group_prenorm N" and
    norm_ball_in_U: "\<forall>n. {\<sigma> \<in> carrier G. N \<sigma> < 1/2^n} \<subseteq> U n" and
    U_in_norm_ball: "\<forall>n. U n \<subseteq> {\<sigma> \<in> carrier G. N \<sigma> \<le> 2/2^n}"
    using construction_of_prenorm_respecting_topology by meson
  have continuous: "continuous_map T euclideanreal N" using prenorm
  proof (rule group_prenorm_continuous_if_continuous_at_1, intro allI impI)
    fix \<epsilon> :: real assume "\<epsilon> > 0"
    then obtain n where hn: "1/2^n < \<epsilon>" 
      by (metis divide_less_eq_1_pos one_less_numeral_iff power_one_over real_arch_pow_inv semiring_norm(76) zero_less_numeral)
    then have "N \<sigma> < \<epsilon>" if "\<sigma> \<in> U (n + 1)" for \<sigma> using that U_in_norm_ball by fastforce
    then show "\<exists>U. neighborhood \<one> U \<and> (\<forall>\<sigma>\<in>U. N \<sigma> < \<epsilon>)" using U_props by meson
  qed
  let ?B = "\<lambda>\<epsilon>. {\<sigma> \<in> carrier G. N \<sigma> < \<epsilon>}"
  let ?\<Delta> = "\<lambda>\<sigma> \<tau>. N (\<sigma> \<otimes> inv \<tau>)"
  let ?\<delta> = "\<lambda>\<sigma> \<tau>. if \<sigma> \<in> carrier G \<and> \<tau> \<in> carrier G then ?\<Delta> \<sigma> \<tau> else 42"
  have "?\<Delta> \<sigma> \<tau> \<ge> 0" if "\<sigma> \<in> carrier G \<and> \<tau> \<in> carrier G" for \<sigma> \<tau>
    using group_prenorm_nonnegative prenorm that by blast
  moreover have "?\<Delta> \<sigma> \<tau> = ?\<Delta> \<tau> \<sigma>" if "\<sigma> \<in> carrier G \<and> \<tau> \<in> carrier G" for \<sigma> \<tau>
  proof -
    have "\<tau> \<otimes> inv \<sigma> = inv (\<sigma> \<otimes> inv \<tau>)" using inv_mult_group inv_inv that by auto
    then show ?thesis using prenorm that by auto 
  qed
  moreover have "?\<Delta> \<sigma> \<tau> = 0 \<longleftrightarrow> \<sigma> = \<tau>" if "\<sigma> \<in> carrier G \<and> \<tau> \<in> carrier G" for \<sigma> \<tau>
  proof
    assume "?\<Delta> \<sigma> \<tau> = 0"
    then have "\<sigma> \<otimes> inv \<tau> \<in> U n" for n using norm_ball_in_U that by fastforce
    then have "\<sigma> \<otimes> inv \<tau> \<in> W" if "neighborhood \<one> W" for W using neighborhood_base that by auto
    then have "\<sigma> \<otimes> inv \<tau> = \<one>" using Hausdorff_space_sing_Inter_opens[of T \<one>] Hausdorff by blast
    then show "\<sigma> = \<tau>" using inv_equality that by fastforce
  next
    assume "\<sigma> = \<tau>"
    then show "?\<Delta> \<sigma> \<tau> = 0" using that prenorm by force
  qed
  moreover have "?\<Delta> \<sigma> \<rho> \<le> ?\<Delta> \<sigma> \<tau> + ?\<Delta> \<tau> \<rho>" if "\<sigma> \<in> carrier G \<and> \<tau> \<in> carrier G \<and> \<rho> \<in> carrier G" for \<sigma> \<tau> \<rho>
  proof -
    have "\<sigma> \<otimes> inv \<rho> = (\<sigma> \<otimes> inv \<tau>) \<otimes> (\<tau> \<otimes> inv \<rho>)" using m_assoc that by (simp add: inv_solve_left)
    then show ?thesis using prenorm that by auto
  qed                        
  ultimately have metric: "Metric_space (carrier G) ?\<delta>" unfolding Metric_space_def by auto
  then interpret Metric_space "carrier G" ?\<delta> by blast
  have "?\<Delta> (\<sigma> \<otimes> \<rho>) (\<tau> \<otimes> \<rho>) = ?\<Delta> \<sigma> \<tau>" if "\<sigma> \<in> carrier G \<and> \<tau> \<in> carrier G \<and> \<rho> \<in> carrier G" for \<sigma> \<tau> \<rho>
  proof -
    have "\<sigma> \<otimes> inv \<tau> = (\<sigma> \<otimes> \<rho>) \<otimes> inv (\<tau> \<otimes> \<rho>)" using that m_assoc by (simp add: inv_solve_left inv_solve_right)
    then show ?thesis by simp
  qed
  then have right_invariant: "right_invariant_metric ?\<delta>" 
    unfolding right_invariant_metric_def using metric by auto
  have mball_coset_of_norm_ball: "mball \<sigma> \<epsilon> = ?B \<epsilon> #> \<sigma>" if h\<sigma>: "\<sigma> \<in> carrier G" for \<sigma> \<epsilon>
  proof -
    have "mball \<sigma> \<epsilon> = {\<tau> \<in> carrier G. N (\<sigma> \<otimes> inv \<tau>) < \<epsilon>}" unfolding mball_def using h\<sigma> by auto
    also have "... = (?B \<epsilon>) #> \<sigma>"
    proof -
      have "\<tau> \<in> (?B \<epsilon>) #> \<sigma>" if "\<tau> \<in> carrier G \<and> N (\<sigma> \<otimes> inv \<tau>) < \<epsilon>" for \<tau>
      proof -
        have "inv (\<sigma> \<otimes> inv \<tau>) \<otimes> \<sigma> = \<tau>" using h\<sigma> that by (simp add: inv_mult_group m_assoc)
        moreover have "inv (\<sigma> \<otimes> inv \<tau>) \<in> ?B \<epsilon>" using h\<sigma> that prenorm by fastforce
        ultimately show ?thesis unfolding r_coset_def by force
      qed
      moreover have "\<tau> \<in> carrier G \<and> N (\<sigma> \<otimes> inv \<tau>) < \<epsilon>" if "\<tau> \<in> (?B \<epsilon>) #> \<sigma>" for \<tau>
      proof -
        from that obtain \<rho> where "\<rho> \<in> ?B \<epsilon> \<and> \<tau> = \<rho> \<otimes> \<sigma>" unfolding r_coset_def by blast
        moreover from this have "\<sigma> \<otimes> inv \<tau> = inv \<rho>" using h\<sigma>
          by (metis (no_types, lifting) inv_closed inv_mult_group inv_solve_left m_closed mem_Collect_eq)
        ultimately show ?thesis using h\<sigma> prenorm by fastforce
      qed
      ultimately show ?thesis by blast
    qed
    finally show ?thesis by presburger
  qed
  define ball where "ball S \<longleftrightarrow> (\<exists>\<sigma> \<epsilon>. \<sigma> \<in> carrier G \<and> S = mball \<sigma> \<epsilon>)" for S
  have "openin mtopology V" if "ball V" for V using that unfolding ball_def by fast
  moreover have "\<exists>W. ball W \<and> \<sigma> \<in> W \<and> W \<subseteq> V" if "openin mtopology V \<and> \<sigma> \<in> V" for \<sigma> V
    unfolding ball_def using openin_mtopology that by (smt (verit, best) centre_in_mball_iff subset_iff)
  ultimately have openin_metric: "openin mtopology = arbitrary union_of ball" 
    by (simp add: openin_topology_base_unique)
  have "openin T V" if "ball V" for V
  proof -
    from that obtain \<sigma> \<epsilon> where "\<sigma> \<in> carrier G \<and> V = ?B \<epsilon> #> \<sigma>" 
      unfolding ball_def using mball_coset_of_norm_ball by blast
    moreover have "openin T (?B \<epsilon>)" using continuous
      by (simp add: continuous_map_upper_lower_semicontinuous_lt)
    ultimately show ?thesis using open_set_translations(2) by presburger
  qed
  moreover have "\<exists>W. ball W \<and> \<sigma> \<in> W \<and> W \<subseteq> V" if "neighborhood \<sigma> V" for \<sigma> V
  proof -
    from that have in_group: "\<sigma> \<in> carrier G" using open_set_in_carrier by fast
    then have "neighborhood \<one> (V #> inv \<sigma>)" 
      using r_coset_def open_set_translations(2) that r_inv by fastforce
    then obtain n where "U n \<subseteq> V #> inv \<sigma>" using neighborhood_base by presburger
    then have "?B (1/2^n) \<subseteq> V #> inv \<sigma>" using norm_ball_in_U by blast
    then have "?B (1/2^n) #> \<sigma> \<subseteq> (V #> inv \<sigma>) #> \<sigma>" unfolding r_coset_def by fast
    also have "...  = V" using in_group that open_set_in_carrier by (simp add: coset_mult_assoc)
    finally have "mball \<sigma> (1/2^n) \<subseteq> V" using mball_coset_of_norm_ball in_group by blast
    then show ?thesis unfolding ball_def
      by (smt (verit) centre_in_mball_iff divide_pos_pos in_group one_add_one zero_less_power zero_less_two)
  qed
  ultimately have "openin T = arbitrary union_of ball" by (simp add: openin_topology_base_unique)
  then show ?thesis using right_invariant openin_metric topology_eq by fastforce
qed                                     

corollary Birkhoff_Kakutani_iff:
  shows "metrizable_space T \<longleftrightarrow> Hausdorff_space T \<and> first_countable T"
  using Birkhoff_Kakutani_left Metric_space.metrizable_space_mtopology metrizable_imp_Hausdorff_space 
    metrizable_imp_first_countable unfolding left_invariant_metric_def by metis

end

end