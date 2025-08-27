theory Ordered_Resolution_Soundness
  imports Grounded_Ordered_Resolution
begin

subsection \<open>Soundness\<close>

context grounded_ordered_resolution_calculus
begin

notation lifting.entails_\<G> (infix "\<TTurnstile>\<^sub>F" 50)

lemma factoring_sound:
  assumes factoring: "factoring C D"
  shows "{C} \<TTurnstile>\<^sub>F {D}"
  using factoring
proof (cases C D rule: factoring.cases)
  case (factoringI C L\<^sub>1 \<mu> \<V> t\<^sub>1 t\<^sub>2 L\<^sub>2 C' D)

  {
    fix I :: "'t\<^sub>G set" and \<gamma> :: "'v \<Rightarrow> 't"

    assume
      entails_ground_instances: "\<forall>C\<^sub>G \<in> ground_instances \<V> C. I \<TTurnstile> C\<^sub>G" and
      D_is_ground: "clause.is_ground (D \<cdot> \<gamma>)" and
      type_preserving_\<gamma>: "type_preserving_on (clause.vars D) \<V> \<gamma>" and
      \<V>: "infinite_variables_per_type \<V>"

    obtain \<gamma>' where
      \<gamma>'_is_ground_subst: "term.is_ground_subst \<gamma>'" and
      type_preserving_\<gamma>': "type_preserving \<V> \<gamma>'" and
      \<gamma>'_\<gamma>: "\<forall>x \<in> clause.vars D. \<gamma> x = \<gamma>' x"
      using clause.type_preserving_ground_subst_extension[OF D_is_ground type_preserving_\<gamma>] .

    let ?C\<^sub>G = "clause.to_ground (C \<cdot> \<mu> \<cdot> \<gamma>')"
    let ?C\<^sub>G' = "clause.to_ground (C' \<cdot> \<mu> \<cdot> \<gamma>')"
    let ?l\<^sub>G\<^sub>1 = "literal.to_ground (L\<^sub>1 \<cdot>l \<mu> \<cdot>l \<gamma>')"
    let ?l\<^sub>G\<^sub>2 = "literal.to_ground (L\<^sub>2 \<cdot>l \<mu> \<cdot>l \<gamma>')"
    let ?t\<^sub>G\<^sub>1 = "term.to_ground (t\<^sub>1 \<cdot>t \<mu> \<cdot>t \<gamma>')"
    let ?t\<^sub>G\<^sub>2 = "term.to_ground (t\<^sub>2 \<cdot>t \<mu> \<cdot>t \<gamma>')"
    let ?D\<^sub>G = "clause.to_ground (D \<cdot> \<gamma>')"

    have type_preserving_\<mu>: "type_preserving_on (clause.vars C) \<V> \<mu>"
      using factoringI(5)
      by blast

    have [simp]: "?t\<^sub>G\<^sub>2 = ?t\<^sub>G\<^sub>1"
      using factoringI(6) term.is_imgu_unifies_pair
      by metis

    have [simp]: "t\<^sub>1 \<cdot>t \<mu> \<cdot>t \<gamma>' =  t\<^sub>1 \<cdot>t \<mu> \<cdot>t \<gamma>"
      using \<gamma>'_\<gamma> term.subst_eq 
      unfolding factoringI
      by fastforce

    have "?C\<^sub>G \<in> ground_instances \<V> C"
    proof(unfold ground_instances_def mem_Collect_eq fst_conv snd_conv,
          intro exI, intro conjI \<V>)

      show "clause.to_ground (C \<cdot> \<mu> \<cdot> \<gamma>') = clause.to_ground (C \<cdot> \<mu> \<odot> \<gamma>')"
        by simp
    next

      show "clause.is_ground (C \<cdot> \<mu> \<odot> \<gamma>')"
        using \<gamma>'_is_ground_subst clause.is_ground_subst_is_ground
        by auto
    next

      show "type_preserving_on (clause.vars C) \<V> (\<mu> \<odot> \<gamma>')"
        using 
          type_preserving_\<mu>
          type_preserving_\<gamma>'
          \<gamma>'_is_ground_subst
          term.type_preserving_ground_compose_ground_subst
        by presburger
    qed

    then have "I \<TTurnstile> ?C\<^sub>G"
      using entails_ground_instances
      by blast

    then have "I \<TTurnstile> clause.to_ground (D \<cdot> \<gamma>)"
      using clause.subst_eq[OF \<gamma>'_\<gamma>[rule_format]]
      unfolding factoringI
      by auto
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
  assumes resolution: "resolution D C R"
  shows "{C, D} \<TTurnstile>\<^sub>F {R}"
  using resolution
proof (cases D C R rule: resolution.cases)
  case (resolutionI \<V>\<^sub>1 \<V>\<^sub>2 \<rho>\<^sub>1 \<rho>\<^sub>2 C D \<V>\<^sub>3 \<mu> t\<^sub>1 t\<^sub>2 L\<^sub>1 L\<^sub>2 C' D' R)
  
  {
    fix I :: "'t\<^sub>G set" and \<gamma> :: "'v \<Rightarrow> 't"

    assume
      C_entails_ground_instances: "\<forall>C\<^sub>G \<in> ground_instances \<V>\<^sub>1 C. I \<TTurnstile> C\<^sub>G" and
      D_entails_ground_instances: "\<forall>D\<^sub>G \<in> ground_instances \<V>\<^sub>2 D. I \<TTurnstile> D\<^sub>G" and
      R_is_ground: "clause.is_ground (R \<cdot> \<gamma>)" and
      type_preserving_\<gamma>: "type_preserving_on (clause.vars R) \<V>\<^sub>3 \<gamma>"

    obtain \<gamma>' where
      \<gamma>'_is_ground_subst: "term.is_ground_subst \<gamma>'" and
      type_preserving_\<gamma>': "type_preserving \<V>\<^sub>3 \<gamma>'" and
      \<gamma>'_\<gamma>: "\<forall>x \<in> clause.vars R. \<gamma> x = \<gamma>' x"
      using clause.type_preserving_ground_subst_extension[OF R_is_ground type_preserving_\<gamma>] .

    let ?C\<^sub>G = "clause.to_ground (C \<cdot> \<rho>\<^sub>1 \<cdot> \<mu> \<cdot> \<gamma>')"
    let ?D\<^sub>G = "clause.to_ground (D \<cdot> \<rho>\<^sub>2 \<cdot> \<mu> \<cdot> \<gamma>')"

    let ?l\<^sub>G\<^sub>1 = "literal.to_ground (L\<^sub>1 \<cdot>l \<rho>\<^sub>1 \<cdot>l \<mu> \<cdot>l \<gamma>')"
    let ?l\<^sub>G\<^sub>2 = "literal.to_ground (L\<^sub>2 \<cdot>l \<rho>\<^sub>2 \<cdot>l \<mu> \<cdot>l \<gamma>')"

    let ?C\<^sub>G' = "clause.to_ground (C' \<cdot> \<rho>\<^sub>1 \<cdot> \<mu> \<cdot> \<gamma>')"
    let ?D\<^sub>G' = "clause.to_ground (D' \<cdot> \<rho>\<^sub>2 \<cdot> \<mu> \<cdot> \<gamma>')"

    let ?t\<^sub>G\<^sub>1 = "term.to_ground (t\<^sub>1 \<cdot>t \<rho>\<^sub>1 \<cdot>t \<mu> \<cdot>t \<gamma>')"
    let ?t\<^sub>G\<^sub>2 = "term.to_ground (t\<^sub>2 \<cdot>t \<rho>\<^sub>2 \<cdot>t \<mu> \<cdot>t \<gamma>')"

    let ?R\<^sub>G = "clause.to_ground (R \<cdot> \<gamma>')"

    have \<mu>_\<gamma>'_is_ground_subst: "term.is_ground_subst (\<mu> \<odot> \<gamma>')"
      using term.is_ground_subst_comp_right[OF \<gamma>'_is_ground_subst] .

    have type_preserving_\<mu>: "type_preserving_on (clause.vars (C \<cdot> \<rho>\<^sub>1) \<union> clause.vars (D \<cdot> \<rho>\<^sub>2)) \<V>\<^sub>3 \<mu>"
      using resolutionI(9)
      by blast

    have type_preserving_\<mu>_\<gamma>:
      "type_preserving_on (clause.vars (C \<cdot> \<rho>\<^sub>1) \<union> clause.vars (D \<cdot> \<rho>\<^sub>2)) \<V>\<^sub>3 (\<mu> \<odot> \<gamma>')"
      using 
        type_preserving_\<gamma>'
        type_preserving_\<mu>
        \<gamma>'_is_ground_subst 
        term.type_preserving_ground_compose_ground_subst 
      by presburger

    note type_preserving_\<rho>_\<mu>_\<gamma> = term.renaming_ground_subst[OF _ \<mu>_\<gamma>'_is_ground_subst]

    have "?C\<^sub>G \<in> ground_instances \<V>\<^sub>1 C"
      proof(
        unfold ground_instances_def mem_Collect_eq fst_conv snd_conv,
        intro exI, intro conjI resolutionI)

      show "clause.to_ground (C \<cdot> \<rho>\<^sub>1 \<cdot> \<mu> \<cdot> \<gamma>') = clause.to_ground (C \<cdot> \<rho>\<^sub>1 \<odot> \<mu> \<odot> \<gamma>')"
        by simp
    next

      show "clause.is_ground (C \<cdot> \<rho>\<^sub>1 \<odot> \<mu> \<odot> \<gamma>')"
        using \<gamma>'_is_ground_subst clause.is_ground_subst_is_ground
        by auto
    next

      show "type_preserving_on (clause.vars C) \<V>\<^sub>1 (\<rho>\<^sub>1 \<odot> \<mu> \<odot> \<gamma>')"
        using
          type_preserving_\<mu>_\<gamma>
          type_preserving_\<rho>_\<mu>_\<gamma>[OF resolutionI(6, 18) _ resolutionI(16)]
        by (simp add: term.assoc clause.vars_subst)
    qed

    then have entails_C\<^sub>G: "I \<TTurnstile> ?C\<^sub>G"
      using C_entails_ground_instances
      by blast

    have "?D\<^sub>G \<in> ground_instances \<V>\<^sub>2 D"
    proof(
        unfold ground_instances_def mem_Collect_eq fst_conv snd_conv,
        intro exI, intro conjI resolutionI)

      show "clause.to_ground (D \<cdot> \<rho>\<^sub>2 \<cdot> \<mu> \<cdot> \<gamma>') = clause.to_ground (D \<cdot> \<rho>\<^sub>2 \<odot> \<mu> \<odot> \<gamma>')"
        by simp
    next

      show "clause.is_ground (D \<cdot> \<rho>\<^sub>2 \<odot> \<mu> \<odot> \<gamma>')"
        using \<gamma>'_is_ground_subst clause.is_ground_subst_is_ground
        by auto
    next

      show "type_preserving_on (clause.vars D) \<V>\<^sub>2 (\<rho>\<^sub>2 \<odot> \<mu> \<odot> \<gamma>')"
        using
          type_preserving_\<mu>_\<gamma>
          type_preserving_\<rho>_\<mu>_\<gamma>[OF resolutionI(7, 19) _ resolutionI(17)]
        by (simp add: term.assoc clause.vars_subst)
    qed

    then have entails_D\<^sub>G: "I \<TTurnstile> ?D\<^sub>G"
      using D_entails_ground_instances
      by blast

    have "I \<TTurnstile> clause.to_ground (R \<cdot> \<gamma>')"
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

      have [simp]: "?C\<^sub>G = add_mset ?l\<^sub>G\<^sub>1 ?C\<^sub>G'"
        unfolding resolutionI
        by simp

      have [simp]: "?D\<^sub>G = add_mset ?l\<^sub>G\<^sub>2 ?D\<^sub>G'"
        unfolding resolutionI
        by simp

      have "\<not> I \<TTurnstile>l ?l\<^sub>G\<^sub>1 \<or> \<not> I \<TTurnstile>l ?l\<^sub>G\<^sub>2"
        by simp

      then have "I \<TTurnstile> ?C\<^sub>G' \<or> I \<TTurnstile> ?D\<^sub>G'"
        using entails_C\<^sub>G entails_D\<^sub>G
        by force

      moreover have "?R\<^sub>G = ?C\<^sub>G' + ?D\<^sub>G'"
        unfolding resolutionI
        by simp

      ultimately show ?thesis
        by auto
    qed

    then have "I \<TTurnstile> clause.to_ground (R \<cdot> \<gamma>)"
      by (metis \<gamma>'_\<gamma> clause.subst_eq)
  }

  then show ?thesis
    unfolding ground.G_entails_def ground_instances_def true_clss_def resolutionI(1-3)
    by auto   
qed

end

sublocale grounded_ordered_resolution_calculus \<subseteq> sound_inference_system inferences "\<bottom>\<^sub>F" "(\<TTurnstile>\<^sub>F)"
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
