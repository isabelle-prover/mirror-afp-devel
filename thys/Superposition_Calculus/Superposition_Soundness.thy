theory Superposition_Soundness
  imports
    First_Order_Clause.Nonground_Entailment

    Grounded_Superposition
    Superposition_Welltypedness_Preservation
begin

subsection \<open>Soundness\<close>

context grounded_superposition_calculus
begin

notation lifting.entails_\<G> (infix "\<TTurnstile>\<^sub>F" 50)

lemma eq_resolution_sound:
  assumes eq_resolution: "eq_resolution D C"
  shows "{D} \<TTurnstile>\<^sub>F {C}"
  using eq_resolution
proof (cases D C rule: eq_resolution.cases)
  case (eq_resolutionI D \<V> \<mu> t t' l D' C)

  {
    fix I :: "'f ground_term rel" and \<gamma> :: "'v \<Rightarrow> 't"

    let ?I = "upair ` I"

    assume
      refl_I: "refl I" and
      entails_ground_instances: "\<forall>D\<^sub>G \<in> ground_instances \<V> D. ?I \<TTurnstile> D\<^sub>G" and
      C_is_ground: "clause.is_ground (C \<cdot> \<gamma>)" and
      type_preserving_literals: "type_preserving_literals \<V> C" and
      type_preserving_\<gamma>: "type_preserving_on (clause.vars C) \<V> \<gamma>" and
      \<V>: "infinite_variables_per_type \<V>"

    obtain \<gamma>' where
      \<gamma>'_is_ground_subst: "term.is_ground_subst \<gamma>'" and
      type_preserving_\<gamma>': "type_preserving \<V> \<gamma>'" and
      \<gamma>'_\<gamma>: "\<forall>x \<in> clause.vars C. \<gamma> x = \<gamma>' x"
      using clause.type_preserving_ground_subst_extension[OF C_is_ground type_preserving_\<gamma>] .

    let ?D\<^sub>G = "clause.to_ground (D \<cdot> \<mu> \<cdot> \<gamma>')"
    let ?l\<^sub>G = "literal.to_ground (l \<cdot>l \<mu> \<cdot>l \<gamma>')"
    let ?D\<^sub>G' = "clause.to_ground (D' \<cdot> \<mu> \<cdot> \<gamma>')"
    let ?t\<^sub>G = "term.to_ground (t \<cdot>t \<mu> \<cdot>t \<gamma>')"
    let ?t\<^sub>G' = "term.to_ground (t' \<cdot>t \<mu> \<cdot>t \<gamma>')"

    note type_preserving_\<mu> = eq_resolutionI(3)

    have "?D\<^sub>G \<in> ground_instances \<V> D"
    proof (unfold ground_instances_def mem_Collect_eq fst_conv snd_conv, intro exI, intro conjI \<V>)

      show "clause.to_ground (D \<cdot> \<mu> \<cdot> \<gamma>') = clause.to_ground (D \<cdot> \<mu> \<odot> \<gamma>')"
        by simp
    next

      show "clause.is_ground (D \<cdot> \<mu> \<odot> \<gamma>')"
        using \<gamma>'_is_ground_subst clause.is_ground_subst_is_ground
        by auto
    next

      show "type_preserving_on (clause.vars D) \<V> (\<mu> \<odot> \<gamma>')"
        using 
          type_preserving_\<gamma>' type_preserving_\<mu> \<gamma>'_is_ground_subst
          term.type_preserving_ground_compose_ground_subst
        by presburger
    next

      show "type_preserving_literals \<V> D" 
        using 
          eq_resolution_type_preserving_literals[OF eq_resolution[unfolded eq_resolutionI]] 
          type_preserving_literals
        unfolding eq_resolutionI
        by satx
    qed

    then have "?I \<TTurnstile> ?D\<^sub>G"
      using entails_ground_instances
      by auto

    then obtain l\<^sub>G where l\<^sub>G_in_D: "l\<^sub>G \<in># ?D\<^sub>G" and I_models_l\<^sub>G: "?I \<TTurnstile>l l\<^sub>G"
      by (auto simp: true_cls_def)

    have "l\<^sub>G \<noteq> ?l\<^sub>G"
    proof(rule notI)
      assume "l\<^sub>G = ?l\<^sub>G"

      then have [simp]: "l\<^sub>G = ?t\<^sub>G !\<approx> ?t\<^sub>G'"
        unfolding eq_resolutionI
        by simp

      moreover have "atm_of l\<^sub>G \<in> ?I"
      proof -
        have "?t\<^sub>G = ?t\<^sub>G'"
          using eq_resolutionI(4) term.is_imgu_unifies_pair
          by metis

        then show ?thesis
          using reflD[OF refl_I, of ?t\<^sub>G]
          by auto
      qed

      ultimately show False
        using I_models_l\<^sub>G
        by auto
    qed

    then have "l\<^sub>G \<in># clause.to_ground (C \<cdot> \<gamma>')"
      using l\<^sub>G_in_D
      unfolding eq_resolutionI
      by simp

    then have "?I \<TTurnstile> clause.to_ground (C \<cdot> \<gamma>)"
      using clause.subst_eq[OF \<gamma>'_\<gamma>[rule_format]] I_models_l\<^sub>G
      by auto
  }

  then show ?thesis
    unfolding
      true_clss_def
      eq_resolutionI(1,2)
      ground_instances_def
      ground.G_entails_def
    by auto
qed

lemma eq_factoring_sound:
  assumes eq_factoring: "eq_factoring D C"
  shows "{D} \<TTurnstile>\<^sub>F {C}"
  using eq_factoring
proof (cases D C rule: eq_factoring.cases)
  case (eq_factoringI D l\<^sub>1 \<mu> t\<^sub>1 t\<^sub>1' \<V> t\<^sub>2 l\<^sub>2 D' t\<^sub>2' C)

  {
    fix I :: "'f ground_term rel" and \<gamma> :: "'v \<Rightarrow> 't"

    let ?I = "upair ` I"

    assume
      trans_I: "trans I" and
      sym_I: "sym I" and
      entails_ground_instances: "\<forall>D\<^sub>G \<in> ground_instances \<V> D. ?I \<TTurnstile> D\<^sub>G" and
      C_is_ground: "clause.is_ground (C \<cdot> \<gamma>)" and
      type_preserving_literals: "type_preserving_literals \<V> C" and
      type_preserving_\<gamma>: "type_preserving_on (clause.vars C) \<V> \<gamma>" and
      \<V>: "infinite_variables_per_type \<V>"

    obtain \<gamma>' where
      \<gamma>'_is_ground_subst: "term.is_ground_subst \<gamma>'" and
      type_preserving_\<gamma>': "type_preserving \<V> \<gamma>'" and
      \<gamma>'_\<gamma>: "\<forall>x \<in> clause.vars C. \<gamma> x = \<gamma>' x"
      using clause.type_preserving_ground_subst_extension[OF C_is_ground type_preserving_\<gamma>].

    let ?D\<^sub>G = "clause.to_ground (D \<cdot> \<mu> \<cdot> \<gamma>')"
    let ?D\<^sub>G' = "clause.to_ground (D' \<cdot> \<mu> \<cdot> \<gamma>')"
    let ?l\<^sub>G\<^sub>1 = "literal.to_ground (l\<^sub>1 \<cdot>l \<mu> \<cdot>l \<gamma>')"
    let ?l\<^sub>G\<^sub>2 = "literal.to_ground (l\<^sub>2 \<cdot>l \<mu> \<cdot>l \<gamma>')"
    let ?t\<^sub>G\<^sub>1 = "term.to_ground (t\<^sub>1 \<cdot>t \<mu> \<cdot>t \<gamma>')"
    let ?t\<^sub>G\<^sub>1' = "term.to_ground (t\<^sub>1' \<cdot>t \<mu> \<cdot>t \<gamma>')"
    let ?t\<^sub>G\<^sub>2 = "term.to_ground (t\<^sub>2 \<cdot>t \<mu> \<cdot>t \<gamma>')"
    let ?t\<^sub>G\<^sub>2' = "term.to_ground (t\<^sub>2' \<cdot>t \<mu> \<cdot>t \<gamma>')"
    let ?C\<^sub>G = "clause.to_ground (C \<cdot> \<gamma>')"

    note type_preserving_\<mu> = eq_factoringI(6)

    have "?D\<^sub>G \<in> ground_instances \<V> D"
    proof (unfold ground_instances_def mem_Collect_eq fst_conv snd_conv, intro exI, intro conjI \<V>)

      show "clause.to_ground (D \<cdot> \<mu> \<cdot> \<gamma>') = clause.to_ground (D \<cdot> \<mu> \<odot> \<gamma>')"
        by simp
    next

      show "clause.is_ground (D \<cdot> \<mu> \<odot> \<gamma>')"
        using \<gamma>'_is_ground_subst clause.is_ground_subst_is_ground
        by auto
    next
     
      show "type_preserving_on (clause.vars D) \<V> (\<mu> \<odot> \<gamma>')"
        using 
          type_preserving_\<mu> type_preserving_\<gamma>' \<gamma>'_is_ground_subst
          term.type_preserving_ground_compose_ground_subst
        by presburger
    next

      show "type_preserving_literals \<V> D"
        using type_preserving_literals
        unfolding 
          eq_factoringI
          eq_factoring_type_preserving_literals[OF eq_factoring[unfolded eq_factoringI]] .
    qed

    then have "?I \<TTurnstile> ?D\<^sub>G"
      using entails_ground_instances
      by blast

    then obtain l\<^sub>G where l\<^sub>G_in_D\<^sub>G: "l\<^sub>G \<in># ?D\<^sub>G" and I_models_l\<^sub>G: "?I \<TTurnstile>l l\<^sub>G"
      by (auto simp: true_cls_def)

    have [simp]: "?t\<^sub>G\<^sub>2 = ?t\<^sub>G\<^sub>1"
      using eq_factoringI(7) term.is_imgu_unifies_pair
      by metis

    have [simp]: "?l\<^sub>G\<^sub>1 = ?t\<^sub>G\<^sub>1 \<approx> ?t\<^sub>G\<^sub>1'"
      unfolding eq_factoringI
      by simp

    have [simp]: "?l\<^sub>G\<^sub>2 = ?t\<^sub>G\<^sub>2 \<approx> ?t\<^sub>G\<^sub>2'"
      unfolding eq_factoringI
      by simp

    have [simp]: "?C\<^sub>G = add_mset (?t\<^sub>G\<^sub>1 \<approx> ?t\<^sub>G\<^sub>2') (add_mset (?t\<^sub>G\<^sub>1' !\<approx> ?t\<^sub>G\<^sub>2') ?D\<^sub>G')"
      unfolding eq_factoringI
      by simp

    have "?I \<TTurnstile> clause.to_ground (C \<cdot> \<gamma>)"
    proof(cases "l\<^sub>G = ?l\<^sub>G\<^sub>1 \<or> l\<^sub>G = ?l\<^sub>G\<^sub>2")
      case True

      then have "?I \<TTurnstile>l ?t\<^sub>G\<^sub>1 \<approx> ?t\<^sub>G\<^sub>1' \<or> ?I \<TTurnstile>l ?t\<^sub>G\<^sub>1 \<approx> ?t\<^sub>G\<^sub>2'"
        using I_models_l\<^sub>G sym_I
        by (auto elim: symE)

      then have "?I \<TTurnstile>l ?t\<^sub>G\<^sub>1 \<approx> ?t\<^sub>G\<^sub>2' \<or> ?I \<TTurnstile>l ?t\<^sub>G\<^sub>1' !\<approx> ?t\<^sub>G\<^sub>2'"
        using sym_I trans_I
        by( auto dest: transD)

      then show ?thesis
        using clause.subst_eq[OF \<gamma>'_\<gamma>[rule_format]] sym_I
        by auto
    next
      case False

      then have "l\<^sub>G \<in># ?D\<^sub>G'"
        using l\<^sub>G_in_D\<^sub>G
        unfolding eq_factoringI
        by simp

      then have "l\<^sub>G \<in># clause.to_ground (C \<cdot> \<gamma>)"
        using clause.subst_eq[OF \<gamma>'_\<gamma>[rule_format]]
        by simp

      then show ?thesis
        using I_models_l\<^sub>G
        by blast
    qed
  }

  then show ?thesis
    unfolding
      eq_factoringI(1, 2)
      ground.G_entails_def
      true_clss_def
      ground_instances_def
    by auto
qed

lemma superposition_sound:
  assumes superposition: "superposition D E C"
  shows "{E, D} \<TTurnstile>\<^sub>F {C}"
  using superposition
proof (cases D E C rule: superposition.cases)
  case (superpositionI \<P> \<V>\<^sub>1 \<V>\<^sub>2 \<rho>\<^sub>1 \<rho>\<^sub>2 E D t\<^sub>1 \<V>\<^sub>3 \<mu> t\<^sub>2 c\<^sub>1 t\<^sub>1' t\<^sub>2' l\<^sub>1 l\<^sub>2 E' D' C)

  {
    fix I :: "'f gterm rel" and \<gamma> :: "'v \<Rightarrow> 't"

    let ?I = "(\<lambda>(x, y). Upair x y) ` I"

    assume
      refl_I: "refl I" and
      trans_I: "trans I" and
      sym_I: "sym I" and
      compatible_with_ground_context_I: "compatible_with_gctxt I" and
      E_entails_ground_instances: "\<forall>E\<^sub>G \<in> ground_instances \<V>\<^sub>1 E. ?I \<TTurnstile> E\<^sub>G" and
      D_entails_ground_instances: "\<forall>D\<^sub>G \<in> ground_instances \<V>\<^sub>2 D. ?I \<TTurnstile> D\<^sub>G" and
      C_is_ground: "clause.is_ground (C \<cdot> \<gamma>)" and
      type_preserving_literals: "type_preserving_literals \<V>\<^sub>3 C" and
      type_preserving_\<gamma>: "type_preserving_on (clause.vars C) \<V>\<^sub>3 \<gamma>"

    obtain \<gamma>' where
      \<gamma>'_is_ground_subst: "term.is_ground_subst \<gamma>'" and
      type_preserving_\<gamma>': "type_preserving \<V>\<^sub>3 \<gamma>'" and
      \<gamma>'_\<gamma>: "\<forall>x \<in> clause.vars C. \<gamma> x = \<gamma>' x"
      using clause.type_preserving_ground_subst_extension[OF C_is_ground type_preserving_\<gamma>] .

    let ?E\<^sub>G = "clause.to_ground (E \<cdot> \<rho>\<^sub>1 \<cdot> \<mu> \<cdot> \<gamma>')"
    let ?D\<^sub>G = "clause.to_ground (D \<cdot> \<rho>\<^sub>2 \<cdot> \<mu> \<cdot> \<gamma>')"

    let ?l\<^sub>G\<^sub>1 = "literal.to_ground (l\<^sub>1 \<cdot>l \<rho>\<^sub>1 \<cdot>l \<mu> \<cdot>l \<gamma>')"
    let ?l\<^sub>G\<^sub>2 = "literal.to_ground (l\<^sub>2 \<cdot>l \<rho>\<^sub>2 \<cdot>l \<mu> \<cdot>l \<gamma>')"

    let ?E\<^sub>G' = "clause.to_ground (E' \<cdot> \<rho>\<^sub>1 \<cdot> \<mu> \<cdot> \<gamma>')"
    let ?D\<^sub>G' = "clause.to_ground (D' \<cdot> \<rho>\<^sub>2 \<cdot> \<mu> \<cdot> \<gamma>')"

    let ?c\<^sub>G\<^sub>1 = "context.to_ground (c\<^sub>1 \<cdot>t\<^sub>c \<rho>\<^sub>1 \<cdot>t\<^sub>c \<mu> \<cdot>t\<^sub>c \<gamma>')"
    let ?t\<^sub>G\<^sub>1 = "term.to_ground (t\<^sub>1 \<cdot>t \<rho>\<^sub>1 \<cdot>t \<mu> \<cdot>t \<gamma>')"
    let ?t\<^sub>G\<^sub>1' = "term.to_ground (t\<^sub>1' \<cdot>t \<rho>\<^sub>1 \<cdot>t \<mu> \<cdot>t \<gamma>')"
    let ?t\<^sub>G\<^sub>2 = "term.to_ground (t\<^sub>2 \<cdot>t \<rho>\<^sub>2 \<cdot>t \<mu> \<cdot>t \<gamma>')"
    let ?t\<^sub>G\<^sub>2' = "term.to_ground (t\<^sub>2' \<cdot>t \<rho>\<^sub>2 \<cdot>t \<mu> \<cdot>t \<gamma>')"

    let ?\<P>\<^sub>G = "if \<P> = Pos then Pos else Neg"

    let ?C\<^sub>G = "clause.to_ground (C \<cdot> \<gamma>')"

    note [simp] = \<P>_simps[OF superpositionI(4)]

    have \<mu>_\<gamma>'_is_ground_subst:
      "term.is_ground_subst (\<mu> \<odot> \<gamma>')"
      using term.is_ground_subst_comp_right[OF \<gamma>'_is_ground_subst].

    note type_preserving_\<mu> = superpositionI(11)
     
    have type_preserving_\<mu>_\<gamma>:
      "type_preserving_on (clause.vars (E \<cdot> \<rho>\<^sub>1) \<union> clause.vars (D \<cdot> \<rho>\<^sub>2)) \<V>\<^sub>3 (\<mu> \<odot> \<gamma>')"
      using 
        type_preserving_\<gamma>' type_preserving_\<mu>  \<gamma>'_is_ground_subst
        term.type_preserving_ground_compose_ground_subst
      by presburger

    note type_preserving_\<rho>_\<mu>_\<gamma> = term.renaming_ground_subst[OF _ \<mu>_\<gamma>'_is_ground_subst]

    have "?E\<^sub>G \<in> ground_instances \<V>\<^sub>1 E"
    proof (unfold ground_instances_def mem_Collect_eq fst_conv snd_conv, 
            intro exI, 
            intro conjI superpositionI)

      show "clause.to_ground (E \<cdot> \<rho>\<^sub>1 \<cdot> \<mu> \<cdot> \<gamma>') = clause.to_ground (E \<cdot> \<rho>\<^sub>1 \<odot> \<mu> \<odot> \<gamma>')"
        by simp
    next

      show "clause.is_ground (E \<cdot> \<rho>\<^sub>1 \<odot> \<mu> \<odot> \<gamma>')"
        using \<gamma>'_is_ground_subst clause.is_ground_subst_is_ground
        by auto
    next

      show "type_preserving_on (clause.vars E) \<V>\<^sub>1 (\<rho>\<^sub>1 \<odot> \<mu> \<odot> \<gamma>')"
        using
          type_preserving_\<mu>_\<gamma>
          type_preserving_\<rho>_\<mu>_\<gamma>[OF superpositionI(7, 24) _ superpositionI(22)]
        by (simp add: clause.vars_subst term.assoc)
    next

      show "type_preserving_literals \<V>\<^sub>1 E"
        using 
          type_preserving_literals
          superposition_type_preserving_literals[OF superposition[unfolded superpositionI]]
        unfolding superpositionI
        by satx
    qed

    then have entails_E\<^sub>G: "?I \<TTurnstile> ?E\<^sub>G"
      using E_entails_ground_instances
      by blast

    have "?D\<^sub>G \<in> ground_instances \<V>\<^sub>2 D"
    proof (unfold ground_instances_def mem_Collect_eq fst_conv snd_conv,
            intro exI,
            intro conjI superpositionI)

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
          type_preserving_\<rho>_\<mu>_\<gamma>[OF superpositionI(8, 25) _ superpositionI(23)]
        by (simp add: term.assoc clause.vars_subst)
    next

      show "type_preserving_literals \<V>\<^sub>2 D"
        using 
          type_preserving_literals
          superposition_type_preserving_literals[OF superposition[unfolded superpositionI]]
        unfolding superpositionI
        by satx  
    qed

    then have entails_D\<^sub>G: "?I \<TTurnstile> ?D\<^sub>G"
      using D_entails_ground_instances
      by blast

    have "?I \<TTurnstile> clause.to_ground (C \<cdot> \<gamma>')"
    proof(cases "?I \<TTurnstile>l literal.to_ground (\<P> (Upair (c\<^sub>1 \<cdot>t\<^sub>c \<rho>\<^sub>1)\<langle>t\<^sub>2' \<cdot>t \<rho>\<^sub>2\<rangle> (t\<^sub>1' \<cdot>t \<rho>\<^sub>1)) \<cdot>l \<mu> \<cdot>l \<gamma>')")
      case True
      then show ?thesis
        unfolding superpositionI
        by simp
    next
      case False

      interpret clause_entailment where I = I
        by unfold_locales (rule trans_I sym_I compatible_with_ground_context_I)+

      note unfolds =
        superpositionI
        context.safe_unfolds
        clause_safe_unfolds
        literal_entails_unfolds
        term.is_imgu_unifies_pair[OF superpositionI(12)]

      from literal_cases[OF superpositionI(4)]
      have "\<not> ?I \<TTurnstile>l ?l\<^sub>G\<^sub>1 \<or> \<not> ?I \<TTurnstile>l ?l\<^sub>G\<^sub>2"
      proof cases
        case Pos: 1

        show ?thesis
          using False symmetric_upair_context_congruence
          unfolding Pos unfolds
          by (auto simp: sym term.is_imgu_unifies_pair[OF superpositionI(12)])
      next
        case Neg: 2

        show ?thesis
          using False symmetric_upair_context_congruence
          unfolding Neg unfolds
          by (auto simp: sym term.is_imgu_unifies_pair[OF superpositionI(12)])
      qed

      then have "?I \<TTurnstile> ?E\<^sub>G' \<or> ?I \<TTurnstile> ?D\<^sub>G'"
        using entails_D\<^sub>G entails_E\<^sub>G
        unfolding superpositionI
        by auto

      then show ?thesis
        unfolding superpositionI
        by simp
    qed

    then have "?I \<TTurnstile> clause.to_ground (C \<cdot> \<gamma>)"
      by (metis \<gamma>'_\<gamma> clause.subst_eq)
  }

  then show ?thesis
    unfolding
      ground.G_entails_def 
      ground_instances_def 
      true_clss_def 
      superpositionI(1-3)
    by auto   
qed

end

sublocale grounded_superposition_calculus \<subseteq> sound_inference_system inferences "\<bottom>\<^sub>F" "(\<TTurnstile>\<^sub>F)"
proof unfold_locales
  fix \<iota>

  assume "\<iota> \<in> inferences"

  then show "set (prems_of \<iota>) \<TTurnstile>\<^sub>F {concl_of \<iota>}"
    using
      eq_factoring_sound
      eq_resolution_sound
      superposition_sound
    unfolding inferences_def ground.G_entails_def
    by auto
qed

sublocale superposition_calculus \<subseteq> sound_inference_system inferences "\<bottom>\<^sub>F" entails_\<G>
proof unfold_locales

  obtain select\<^sub>G where select\<^sub>G: "select\<^sub>G \<in> select\<^sub>G\<^sub>s"
    using Q_nonempty by blast

  then interpret grounded_superposition_calculus
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
