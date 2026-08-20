theory Ordered_Resolution_Soundness
  imports Grounded_Ordered_Resolution
begin

subsection \<open>Soundness\<close>

context grounded_ordered_resolution_calculus
begin

notation lifting.entails_\<G> (infix "\<TTurnstile>\<^sub>F" 50)

lemma factoring_sound:
  assumes factoring: "factoring D C"
  shows "{D} \<TTurnstile>\<^sub>F {C}"
  using factoring
proof (cases D C rule: factoring.cases)
  case (factoringI D l\<^sub>1 \<mu> \<V> t\<^sub>1 t\<^sub>2 l\<^sub>2 D' C)

  {
    fix I :: "'t\<^sub>G set" and \<gamma> :: 'subst

    assume
      entails_ground_instances: "\<forall>D\<^sub>G \<in> ground_instances \<V> D. I \<TTurnstile> D\<^sub>G" and
      C_grounding: "clause.is_ground (C \<cdot> \<gamma>)" and
      type_preserving_\<gamma>: "type_preserving_on (clause.vars C) \<V> \<gamma>" and
      \<V>: "term.exists_nonground \<Longrightarrow> infinite_variables_per_type \<V>"

    obtain \<gamma>' where
      D_grounding: "clause.is_ground (D \<cdot> \<mu> \<cdot> \<gamma>')" and
      type_preserving_\<gamma>': "type_preserving_on (clause.vars C \<union> clause.vars (D \<cdot> \<mu>)) \<V> \<gamma>'" and
      \<gamma>_\<gamma>': "\<forall>x\<in>clause.vars C. x \<cdot>v \<gamma> = x \<cdot>v \<gamma>'"
      using clause.type_preserving_on_ground_subst_extension[OF C_grounding type_preserving_\<gamma>] .

    let ?D\<^sub>G = "clause.to_ground (D \<cdot> \<mu> \<cdot> \<gamma>')"
    let ?D\<^sub>G' = "clause.to_ground (D' \<cdot> \<mu> \<cdot> \<gamma>')"
    let ?l\<^sub>G\<^sub>1 = "literal.to_ground (l\<^sub>1 \<cdot>l \<mu> \<cdot>l \<gamma>')"
    let ?l\<^sub>G\<^sub>2 = "literal.to_ground (l\<^sub>2 \<cdot>l \<mu> \<cdot>l \<gamma>')"
    let ?t\<^sub>G\<^sub>1 = "term.to_ground (t\<^sub>1 \<cdot>t \<mu> \<cdot>t \<gamma>')"
    let ?t\<^sub>G\<^sub>2 = "term.to_ground (t\<^sub>2 \<cdot>t \<mu> \<cdot>t \<gamma>')"
    let ?C\<^sub>G = "clause.to_ground (C \<cdot> \<gamma>')"

    have type_preserving_\<mu>: "type_preserving_on (clause.vars D) \<V> \<mu>"
      using factoringI(5)
      by blast

    have [simp]: "?t\<^sub>G\<^sub>2 = ?t\<^sub>G\<^sub>1"
      using factoringI(6) term.is_imgu_unifies_pair
      by metis

    have "?D\<^sub>G \<in> ground_instances \<V> D"
    proof(unfold ground_instances_def mem_Collect_eq fst_conv snd_conv,
          intro exI, intro impI conjI \<V>)

      show "clause.to_ground (D \<cdot> \<mu> \<cdot> \<gamma>') = clause.to_ground (D \<cdot> \<mu> \<odot> \<gamma>')"
        by simp
    next

      show "clause.is_ground (D \<cdot> \<mu> \<odot> \<gamma>')"
        using D_grounding
        by simp
    next

      have type_preserving_\<gamma>': 
        "type_preserving_on (\<Union> (term.vars ` (\<lambda>x. x \<cdot>v \<mu>) ` clause.vars D)) \<V> \<gamma>'"
        using type_preserving_\<gamma>' clause.vars_subst
        by blast

      show "type_preserving_on (clause.vars D) \<V> (\<mu> \<odot> \<gamma>')"
        using term.type_preserving_on_subst_compose[OF type_preserving_\<mu> type_preserving_\<gamma>'] .
    qed

    then have "I \<TTurnstile> ?D\<^sub>G"
      using entails_ground_instances
      by blast

    then have "I \<TTurnstile> clause.to_ground (C \<cdot> \<gamma>)"
      using clause.subst_eq[OF \<gamma>_\<gamma>'[rule_format]]
      unfolding factoringI
      by fastforce
  }

  then show ?thesis
    unfolding
      factoringI(1, 2)
      ground.G_entails_def
      true_clss_def
      ground_instances_def
    by auto
qed

lemma resolution_sound:
  assumes resolution: "resolution D E C"
  shows "{E, D} \<TTurnstile>\<^sub>F {C}"
  using resolution
proof (cases D E C rule: resolution.cases)
  case (resolutionI \<V>\<^sub>1 \<V>\<^sub>2 \<rho>\<^sub>1 \<rho>\<^sub>2 E D \<V>\<^sub>3 \<mu> t\<^sub>1 t\<^sub>2 l\<^sub>1 l\<^sub>2 E' D' C)
  
  {
    fix I :: "'t\<^sub>G set" and \<gamma> :: 'subst

    assume
      E_entails_ground_instances: "\<forall>E\<^sub>G \<in> ground_instances \<V>\<^sub>1 E. I \<TTurnstile> E\<^sub>G" and
      D_entails_ground_instances: "\<forall>D\<^sub>G \<in> ground_instances \<V>\<^sub>2 D. I \<TTurnstile> D\<^sub>G" and
      C_grounding: "clause.is_ground (C \<cdot> \<gamma>)" and
      type_preserving_\<gamma>: "type_preserving_on (clause.vars C) \<V>\<^sub>3 \<gamma>"

    obtain \<gamma>' where
      "clause.is_ground ((E \<cdot> \<rho>\<^sub>1 \<cdot> \<mu> + D \<cdot> \<rho>\<^sub>2 \<cdot> \<mu>) \<cdot> \<gamma>')" and
      type_preserving_\<gamma>':
        "type_preserving_on (clause.vars C \<union> clause.vars (E \<cdot> \<rho>\<^sub>1 \<cdot> \<mu> + D \<cdot> \<rho>\<^sub>2 \<cdot> \<mu>)) \<V>\<^sub>3 \<gamma>'" and
      \<gamma>_\<gamma>': "C \<cdot> \<gamma> = C \<cdot> \<gamma>'"
      using clause.type_preserving_on_ground_subst_extension[OF C_grounding type_preserving_\<gamma>] .

    then have 
      D_grounding: "clause.is_ground (D \<cdot> \<rho>\<^sub>2 \<cdot> \<mu> \<cdot> \<gamma>')" and 
      E_grounding: "clause.is_ground (E \<cdot> \<rho>\<^sub>1 \<cdot> \<mu> \<cdot> \<gamma>')"
      by auto

    let ?E\<^sub>G = "clause.to_ground (E \<cdot> \<rho>\<^sub>1 \<cdot> \<mu> \<cdot> \<gamma>')"
    let ?D\<^sub>G = "clause.to_ground (D \<cdot> \<rho>\<^sub>2 \<cdot> \<mu> \<cdot> \<gamma>')"

    let ?l\<^sub>G\<^sub>1 = "literal.to_ground (l\<^sub>1 \<cdot>l \<rho>\<^sub>1 \<cdot>l \<mu> \<cdot>l \<gamma>')"
    let ?l\<^sub>G\<^sub>2 = "literal.to_ground (l\<^sub>2 \<cdot>l \<rho>\<^sub>2 \<cdot>l \<mu> \<cdot>l \<gamma>')"

    let ?E\<^sub>G' = "clause.to_ground (E' \<cdot> \<rho>\<^sub>1 \<cdot> \<mu> \<cdot> \<gamma>')"
    let ?D\<^sub>G' = "clause.to_ground (D' \<cdot> \<rho>\<^sub>2 \<cdot> \<mu> \<cdot> \<gamma>')"

    let ?t\<^sub>G\<^sub>1 = "term.to_ground (t\<^sub>1 \<cdot>t \<rho>\<^sub>1 \<cdot>t \<mu> \<cdot>t \<gamma>')"
    let ?t\<^sub>G\<^sub>2 = "term.to_ground (t\<^sub>2 \<cdot>t \<rho>\<^sub>2 \<cdot>t \<mu> \<cdot>t \<gamma>')"

    let ?C\<^sub>G = "clause.to_ground (C \<cdot> \<gamma>')"


    note type_preserving_\<mu> = resolutionI(9)

    have "?E\<^sub>G \<in> ground_instances \<V>\<^sub>1 E"
      proof(
        unfold ground_instances_def mem_Collect_eq fst_conv snd_conv,
        intro exI, intro impI conjI resolutionI)

      show "clause.to_ground (E \<cdot> \<rho>\<^sub>1 \<cdot> \<mu> \<cdot> \<gamma>') = clause.to_ground (E \<cdot> \<rho>\<^sub>1 \<odot> \<mu> \<odot> \<gamma>')"
        by simp
    next

      show "clause.is_ground (E \<cdot> \<rho>\<^sub>1 \<odot> \<mu> \<odot> \<gamma>')"
        using E_grounding      
        by simp
    next

      show "type_preserving_on (clause.vars E) \<V>\<^sub>1 (\<rho>\<^sub>1 \<odot> \<mu> \<odot> \<gamma>')"
      proof (subst term.assoc,
             rule term.typed_renaming_grounding_subst_compose[OF
               resolutionI(6) _ resolutionI(18) _ resolutionI(16)], intro ballI)
        fix t
        assume "t \<in> (\<lambda>x. x \<cdot>v \<rho>\<^sub>1 \<odot> (\<mu> \<odot> \<gamma>')) ` clause.vars E" 

        then show "term.is_ground t"
          using clause.variable_grounding E_grounding clause.vars_grounded_if_is_grounding
          by force
      next

        show "type_preserving_on (\<Union> (term.vars ` (\<lambda>x. x \<cdot>v \<rho>\<^sub>1) ` clause.vars E)) \<V>\<^sub>3 (\<mu> \<odot> \<gamma>')"
          by 
            (rule term.type_preserving_on_subst_compose'[OF type_preserving_\<mu> type_preserving_\<gamma>'])
            (auto simp: clause.vars_subst)
      qed
    qed

    then have entails_E\<^sub>G: "I \<TTurnstile> ?E\<^sub>G"
      using E_entails_ground_instances
      by blast

    have "?D\<^sub>G \<in> ground_instances \<V>\<^sub>2 D"
    proof (unfold ground_instances_def mem_Collect_eq fst_conv snd_conv,
           intro exI, intro conjI impI resolutionI)

      show "clause.to_ground (D \<cdot> \<rho>\<^sub>2 \<cdot> \<mu> \<cdot> \<gamma>') = clause.to_ground (D \<cdot> \<rho>\<^sub>2 \<odot> \<mu> \<odot> \<gamma>')"
        by simp
    next

      show "clause.is_ground (D \<cdot> \<rho>\<^sub>2 \<odot> \<mu> \<odot> \<gamma>')"
        using D_grounding
        by simp
    next

      show "type_preserving_on (clause.vars D) \<V>\<^sub>2 (\<rho>\<^sub>2 \<odot> \<mu> \<odot> \<gamma>')"
      proof (subst term.assoc,
             rule term.typed_renaming_grounding_subst_compose[OF
               resolutionI(7) _ resolutionI(19) _ resolutionI(17)], 
             intro ballI)
        fix t
        assume "t \<in> (\<lambda>x. x \<cdot>v \<rho>\<^sub>2 \<odot> (\<mu> \<odot> \<gamma>')) ` clause.vars D" 

        then show "term.is_ground t"
          using clause.variable_grounding D_grounding clause.vars_grounded_if_is_grounding
          by force
      next

        show "type_preserving_on (\<Union> (term.vars ` (\<lambda>x. x \<cdot>v \<rho>\<^sub>2) ` clause.vars D)) \<V>\<^sub>3 (\<mu> \<odot> \<gamma>')"
          by 
            (rule term.type_preserving_on_subst_compose'[OF type_preserving_\<mu> type_preserving_\<gamma>'])
            (auto simp: clause.vars_subst)
      qed
    qed

    then have entails_D\<^sub>G: "I \<TTurnstile> ?D\<^sub>G"
      using D_entails_ground_instances
      by blast

    have "I \<TTurnstile> clause.to_ground (C \<cdot> \<gamma>')"
    proof -

      have [simp]: "?t\<^sub>G\<^sub>1 = ?t\<^sub>G\<^sub>2"
        using resolutionI(10) term.is_imgu_unifies_pair
        by metis

      have [simp]: "?l\<^sub>G\<^sub>1 = Neg ?t\<^sub>G\<^sub>1"
        unfolding resolutionI
        by simp

      have [simp]: "?l\<^sub>G\<^sub>2 = Pos ?t\<^sub>G\<^sub>2"
        unfolding resolutionI
        by simp

      have [simp]: "?E\<^sub>G = add_mset ?l\<^sub>G\<^sub>1 ?E\<^sub>G'"
        unfolding resolutionI
        by simp

      have [simp]: "?D\<^sub>G = add_mset ?l\<^sub>G\<^sub>2 ?D\<^sub>G'"
        unfolding resolutionI
        by simp

      have "\<not> I \<TTurnstile>l ?l\<^sub>G\<^sub>1 \<or> \<not> I \<TTurnstile>l ?l\<^sub>G\<^sub>2"
        by simp

      then have "I \<TTurnstile> ?E\<^sub>G' \<or> I \<TTurnstile> ?D\<^sub>G'"
        using entails_E\<^sub>G entails_D\<^sub>G
        by force

      moreover have "?C\<^sub>G = ?E\<^sub>G' + ?D\<^sub>G'"
        unfolding resolutionI
        by simp

      ultimately show ?thesis
        by auto
    qed

    then have "I \<TTurnstile> clause.to_ground (C \<cdot> \<gamma>)"
      by (metis \<gamma>_\<gamma>')
  }

  then show ?thesis
    unfolding ground.G_entails_def ground_instances_def true_clss_def resolutionI(1-3)
    by auto   
qed

sublocale sound_inference_system inferences "\<bottom>\<^sub>F" "(\<TTurnstile>\<^sub>F)"
proof unfold_locales
fix \<iota>

  assume "\<iota> \<in> inferences"

  then show "set (prems_of \<iota>) \<TTurnstile>\<^sub>F {concl_of \<iota>}"
    using
      factoring_sound
      resolution_sound
    unfolding inferences_def ground.G_entails_def
    by auto
qed

end

sublocale ordered_resolution_calculus \<subseteq> sound_inference_system inferences "\<bottom>\<^sub>F" entails_\<G>
proof unfold_locales
  obtain select\<^sub>G where select\<^sub>G: "select\<^sub>G \<in> select\<^sub>G\<^sub>s"
    using Q_nonempty by blast

  then interpret grounded_ordered_resolution_calculus
    where select\<^sub>G = select\<^sub>G
    by unfold_locales (simp add: select\<^sub>G\<^sub>s_def)

  fix \<iota>
  assume "\<iota> \<in> inferences"

  then show "entails_\<G> (set (prems_of \<iota>)) {concl_of \<iota>}"
    unfolding entails_def
    using sound
    by blast
qed

end
