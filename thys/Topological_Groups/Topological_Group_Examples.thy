\<^marker>\<open>creator "Niklas Krofta"\<close>
section \<open>Examples of Topological Groups\<close>
theory Topological_Group_Examples
  imports Topological_Group
begin

paragraph \<open>Summary\<close>
text \<open>This section gives examples of topological groups.\<close>

lemma (in group) discrete_topological_group:
  shows "topological_group G (discrete_topology (carrier G))"
proof -               
  let ?T = "discrete_topology (carrier G)"
  have "topspace ?T = carrier G" using topspace_discrete_topology by force
  moreover have "continuous_map (prod_topology ?T ?T) ?T (\<lambda>(\<sigma>,\<tau>). \<sigma> \<otimes> \<tau>)" 
    unfolding prod_topology_discrete_topology[symmetric] by auto
  ultimately show ?thesis unfolding topological_group_def topological_group_axioms_def by fastforce
qed

lemma topological_group_real_power_space:
  defines "\<RR> :: (real^'n) monoid \<equiv> \<lparr>carrier = UNIV, mult = (+), one = 0\<rparr>"
  defines "T :: (real^'n) topology \<equiv> euclidean"
  shows "topological_group \<RR> T"
proof -
  have "x \<in> Units \<RR>" for x
  proof -
    have "x \<otimes>\<^bsub>\<RR>\<^esub> -x = \<one>\<^bsub>\<RR>\<^esub>" "-x \<otimes>\<^bsub>\<RR>\<^esub> x = \<one>\<^bsub>\<RR>\<^esub>" using \<RR>_def by auto
    then show ?thesis unfolding Units_def \<RR>_def by fastforce
  qed
  then have group: "group \<RR>" by (unfold_locales) (auto simp: \<RR>_def)
  then interpret group \<RR> by auto
  have group_is_space: "topspace T = carrier \<RR>"
    unfolding \<RR>_def T_def by force
  have mul_continuous: "continuous_map (prod_topology T T) T (\<lambda>(x,y). x \<otimes>\<^bsub>\<RR>\<^esub> y)"
    using continuous_map_add[OF continuous_map_fst continuous_map_snd]
    unfolding T_def \<RR>_def by (simp add: case_prod_beta')
  have "(-x) \<otimes>\<^bsub>\<RR>\<^esub> x = \<one>\<^bsub>\<RR>\<^esub>" for x unfolding \<RR>_def by auto
  then have "inv\<^bsub>\<RR>\<^esub> x = -x" for x using inv_equality \<RR>_def by simp
  moreover have "continuous_map T T uminus" unfolding T_def by force
  ultimately have "continuous_map T T (\<lambda>x. inv\<^bsub>\<RR>\<^esub> x)" by simp
  then show ?thesis using group_is_space mul_continuous group
    unfolding topological_group_def topological_group_axioms_def by blast
qed

definition unit_group :: "('a :: field) monoid" where
"unit_group = \<lparr>carrier = UNIV - {0}, mult = (*), one = 1\<rparr>" 

lemma 
  group_unit_group: "group unit_group" and
  inv_unit_group: "x \<in> carrier unit_group \<Longrightarrow> inv\<^bsub>unit_group\<^esub> x = inverse x"
proof -
  have "x \<in> Units unit_group" if "x \<noteq> 0" for x
  proof -
    have "x \<otimes>\<^bsub>unit_group\<^esub> 1/x = \<one>\<^bsub>unit_group\<^esub>" "1/x \<otimes>\<^bsub>unit_group\<^esub> x = \<one>\<^bsub>unit_group\<^esub>" 
      using that unfolding unit_group_def by auto
    then show ?thesis unfolding Units_def unit_group_def using that by fastforce
  qed
  then show "group unit_group" by (unfold_locales) (auto simp: unit_group_def)
  then interpret group unit_group by blast
  show "inv\<^bsub>unit_group\<^esub> x = inverse x" if "x \<in> carrier unit_group"
    using that inv_equality[of "inverse x"] unfolding unit_group_def by simp
qed

lemma topological_group_real_unit_group:
  defines "T :: real topology \<equiv> subtopology euclidean (UNIV - {0})"
  shows "topological_group unit_group T"
proof -
  let ?\<RR> = "unit_group :: real monoid"
  have group_is_space: "topspace T = carrier ?\<RR>" unfolding unit_group_def T_def by force
  have "continuous_map (prod_topology euclidean euclidean) euclidean (\<lambda>(x,y). x \<otimes>\<^bsub>?\<RR>\<^esub> y)"
    using continuous_map_real_mult[OF continuous_map_fst continuous_map_snd]
    unfolding T_def unit_group_def by (simp add: case_prod_beta')
  then have "continuous_map (prod_topology T T) euclideanreal (\<lambda>(x,y). x \<otimes>\<^bsub>?\<RR>\<^esub> y)"
    unfolding T_def subtopology_Times[symmetric] using continuous_map_from_subtopology by blast
  moreover have "(\<lambda>(x,y). x \<otimes>\<^bsub>?\<RR>\<^esub> y) \<in> topspace (prod_topology T T) \<rightarrow> UNIV - {0}"
    unfolding T_def unit_group_def by fastforce
  ultimately have mul_continuous: "continuous_map (prod_topology T T) T (\<lambda>(x,y). x \<otimes>\<^bsub>?\<RR>\<^esub> y)"
    unfolding T_def using continuous_map_into_subtopology by blast
  have "continuous_map T euclideanreal inverse" 
    using continuous_map_real_inverse[of T id] unfolding T_def by auto
  moreover have "inverse \<in> topspace T \<rightarrow> topspace T" unfolding T_def by fastforce
  ultimately have "continuous_map T T inverse" 
    unfolding T_def using continuous_map_into_subtopology by auto
  then have "continuous_map T T (\<lambda>x. inv\<^bsub>?\<RR>\<^esub> x)" 
    using group_is_space continuous_map_eq inv_unit_group by metis
  then show ?thesis using group_is_space mul_continuous group_unit_group
    unfolding topological_group_def topological_group_axioms_def by blast
qed

end