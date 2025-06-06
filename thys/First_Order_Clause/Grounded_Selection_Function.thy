theory Grounded_Selection_Function
  imports
    Nonground_Selection_Function
    HOL_Extra
begin

context groundable_nonground_clause
begin

abbreviation select_subst_stability_on_clause where
  "select_subst_stability_on_clause select select\<^sub>G C\<^sub>G \<Gamma> C \<gamma> \<equiv>
    C \<cdot> \<gamma> = clause.from_ground C\<^sub>G \<and>
    select\<^sub>G C\<^sub>G = clause.to_ground ((select C) \<cdot> \<gamma>) \<and>
    is_ground_instance \<Gamma> C \<gamma>"

abbreviation uncurried_ground_instances where
  "uncurried_ground_instances C \<equiv> ground_instances (fst C) (snd C)"

abbreviation select_subst_stability_on where
  "select_subst_stability_on select select\<^sub>G N \<equiv>
    \<forall>C\<^sub>G \<in> \<Union> (uncurried_ground_instances ` N). \<exists>(e, C) \<in> N. \<exists>\<gamma>.
      select_subst_stability_on_clause select select\<^sub>G C\<^sub>G e C \<gamma>"

lemma obtain_subst_stable_on_select_grounding:
  fixes select :: "'a select"
  obtains select\<^sub>G where
    "select_subst_stability_on select select\<^sub>G N"
    "is_select_grounding select select\<^sub>G"
proof -
  let ?N\<^sub>G = "\<Union>(uncurried_ground_instances ` N)"

  {
    fix \<Gamma> C \<gamma>
    assume
      "(\<Gamma>, C) \<in> N"
      "is_ground_instance \<Gamma> C \<gamma>"

    then have
      "\<exists>\<gamma>'. \<exists>(\<Gamma>', C')\<in>N. \<exists>select\<^sub>G.
         select_subst_stability_on_clause select select\<^sub>G (clause.to_ground (C \<cdot> \<gamma>)) \<Gamma>' C' \<gamma>'"
      using is_ground_instance_is_ground
      by (intro exI[of _ \<gamma>], intro bexI[of _ "(\<Gamma>, C)"]) auto
  }

  then have
    "\<forall>C\<^sub>G \<in> ?N\<^sub>G. \<exists>\<gamma>. \<exists>(\<Gamma>, C) \<in> N. \<exists>select\<^sub>G. select_subst_stability_on_clause select select\<^sub>G C\<^sub>G \<Gamma> C \<gamma>"
    unfolding ground_instances_def
    by force

  then have select\<^sub>G_exists_for_premises:
     "\<forall>C\<^sub>G \<in> ?N\<^sub>G. \<exists>select\<^sub>G \<gamma>. \<exists>(\<Gamma>, C) \<in> N. select_subst_stability_on_clause select select\<^sub>G C\<^sub>G \<Gamma> C \<gamma>"
    by blast

  obtain select\<^sub>G_on_groundings where
    select\<^sub>G_on_groundings: "select_subst_stability_on select select\<^sub>G_on_groundings N"
    using Ball_Ex_comm(1)[OF select\<^sub>G_exists_for_premises]
    unfolding prod.case_eq_if
    by fast

  define select\<^sub>G where
    "\<And>C\<^sub>G. select\<^sub>G C\<^sub>G = (
        if C\<^sub>G \<in> ?N\<^sub>G
        then select\<^sub>G_on_groundings C\<^sub>G
        else clause.to_ground (select (clause.from_ground C\<^sub>G))
    )"

  have grounding: "is_select_grounding select select\<^sub>G"
    using select\<^sub>G_on_groundings
    unfolding is_select_grounding_def select\<^sub>G_def prod.case_eq_if
    by (metis (lifting) clause.from_ground_inverse clause.ground_is_ground clause.subst_id_subst)

  show ?thesis
    using that[OF _ grounding] select\<^sub>G_on_groundings
    unfolding select\<^sub>G_def
    by fastforce
qed

end

locale grounded_selection_function =
  nonground_selection_function where select = select and atom_subst = atom_subst +
  groundable_nonground_clause where atom_subst = atom_subst
  for               
    select :: "'a select" and
    atom_subst :: "'a \<Rightarrow> ('v \<Rightarrow> 't) \<Rightarrow> 'a" +
fixes select\<^sub>G
assumes select\<^sub>G: "is_select_grounding select select\<^sub>G"
begin

abbreviation subst_stability_on where
  "subst_stability_on N \<equiv> select_subst_stability_on select select\<^sub>G N"

lemma select\<^sub>G_subset: "select\<^sub>G C \<subseteq># C"
  using select\<^sub>G
  unfolding is_select_grounding_def
  by (metis select_subset clause.to_ground_def image_mset_subseteq_mono clause.subst_def)

lemma select\<^sub>G_negative_literals:
  assumes "l\<^sub>G \<in># select\<^sub>G C\<^sub>G"
  shows "is_neg l\<^sub>G"
proof -
  obtain C \<gamma> where
    is_ground: "clause.is_ground (C \<cdot> \<gamma>)" and
    select\<^sub>G: "select\<^sub>G C\<^sub>G = clause.to_ground (select C \<cdot> \<gamma>)"
    using select\<^sub>G
    unfolding is_select_grounding_def
    by blast

  show ?thesis
    using
      ground_literal_in_selection[
        OF select_ground_subst[OF is_ground] assms[unfolded select\<^sub>G],
        THEN select_neg_subst
        ]
    by simp

qed

sublocale ground: selection_function select\<^sub>G
  by unfold_locales (simp_all add: select\<^sub>G_subset select\<^sub>G_negative_literals)

end

end
