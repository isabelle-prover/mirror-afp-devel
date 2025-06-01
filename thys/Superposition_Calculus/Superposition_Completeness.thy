theory Superposition_Completeness
  imports
    Grounded_Superposition
    Ground_Superposition_Completeness
    Superposition_Welltypedness_Preservation

    First_Order_Clause.Nonground_Entailment
begin

section \<open>Completeness\<close>

context grounded_superposition_calculus
begin

subsection \<open>Liftings\<close>

lemma eq_resolution_lifting:
  fixes
    D\<^sub>G C\<^sub>G :: "'t\<^sub>G ground_clause" and
    D C :: "'t clause" and
    \<gamma> :: "'v \<Rightarrow> 't"
  defines
    [simp]: "D\<^sub>G \<equiv> clause.to_ground (D \<cdot> \<gamma>)" and
    [simp]: "C\<^sub>G \<equiv> clause.to_ground (C \<cdot> \<gamma>)"
  assumes
    ground_eq_resolution: "ground.eq_resolution D\<^sub>G C\<^sub>G" and
    D_grounding: "clause.is_ground (D \<cdot> \<gamma>)" and
    C_grounding: "clause.is_ground (C \<cdot> \<gamma>)" and
    select: "clause.from_ground (select\<^sub>G D\<^sub>G) = (select D) \<cdot> \<gamma>" and
    type_preserving_literals: "type_preserving_literals \<V> D" and
    type_preserving_\<gamma>: "type_preserving_on (clause.vars D) \<V> \<gamma>" and
    \<V>: "infinite_variables_per_type \<V>"
  obtains C'
  where
    "eq_resolution (\<V>, D) (\<V>, C')"
    "Infer [D\<^sub>G] C\<^sub>G \<in> inference_ground_instances (Infer [(\<V>, D)] (\<V>, C'))"
    "C' \<cdot> \<gamma> = C \<cdot> \<gamma>"
  using ground_eq_resolution
proof (cases D\<^sub>G C\<^sub>G rule: ground.eq_resolution.cases)
  case ground_eq_resolutionI: (eq_resolutionI l\<^sub>G D\<^sub>G' t\<^sub>G)

  let ?select\<^sub>G_empty = "select\<^sub>G D\<^sub>G = {#}"
  let ?select\<^sub>G_not_empty = "select\<^sub>G D\<^sub>G \<noteq> {#}"

  obtain l where
    l_\<gamma>: "l \<cdot>l \<gamma> = term.from_ground t\<^sub>G !\<approx> term.from_ground t\<^sub>G" and
    l_in_D: "l \<in># D" and
    l_selected: "?select\<^sub>G_not_empty \<Longrightarrow> is_maximal l (select D)" and
    l_\<gamma>_selected: "?select\<^sub>G_not_empty \<Longrightarrow> is_maximal (l \<cdot>l \<gamma>) (select D \<cdot> \<gamma>)" and
    l_is_maximal: "?select\<^sub>G_empty \<Longrightarrow> is_maximal l D" and
    l_\<gamma>_is_maximal: "?select\<^sub>G_empty \<Longrightarrow> is_maximal (l \<cdot>l \<gamma>) (D \<cdot> \<gamma>)"
  proof-
    obtain max_l where
      "is_maximal max_l D" and
      is_max_in_D_\<gamma>: "is_maximal (max_l \<cdot>l \<gamma>) (D \<cdot> \<gamma>)"
    proof-
      have "D \<noteq> {#}"
        using ground_eq_resolutionI(1)
        by auto

      then show ?thesis
        using that D_grounding obtain_maximal_literal
        by blast
    qed

    moreover then have "max_l \<in># D"
      unfolding is_maximal_def
      by blast

    moreover have "max_l \<cdot>l \<gamma> = term.from_ground t\<^sub>G !\<approx> term.from_ground t\<^sub>G" if ?select\<^sub>G_empty
    proof(rule unique_maximal_in_ground_clause[OF D_grounding is_max_in_D_\<gamma>])
      have "ground_is_maximal l\<^sub>G D\<^sub>G"
        using ground_eq_resolutionI(3) that
        unfolding is_maximal_def
        by simp

      then show "is_maximal (term.from_ground t\<^sub>G !\<approx> term.from_ground t\<^sub>G) (D \<cdot> \<gamma>)"
        using D_grounding
        unfolding ground_eq_resolutionI(2)
        by simp
    qed

    moreover obtain selected_l where
      "selected_l \<cdot>l \<gamma> = term.from_ground t\<^sub>G !\<approx> term.from_ground t\<^sub>G" and
      "is_maximal selected_l (select D)"
      "is_maximal (selected_l \<cdot>l \<gamma>) (select D \<cdot> \<gamma>)"
    if ?select\<^sub>G_not_empty
    proof-
      have "is_maximal (term.from_ground t\<^sub>G !\<approx> term.from_ground t\<^sub>G) (select D \<cdot> \<gamma>)"
        if ?select\<^sub>G_not_empty
        using ground_eq_resolutionI(3) that select
        unfolding ground_eq_resolutionI(2)
        by simp

      then show ?thesis
        using
          that
          obtain_maximal_literal[OF _ select_ground_subst[OF D_grounding]]
          unique_maximal_in_ground_clause[OF select_ground_subst[OF D_grounding]]
        by (metis (lifting) clause.magma_subst_empty(1) is_maximal_not_empty)
    qed

    moreover then have "selected_l \<in># D" if ?select\<^sub>G_not_empty
      using that maximal_in_clause mset_subset_eqD select_subset
      by fast

    ultimately show ?thesis
      using that
      by blast
  qed

  obtain C' where D: "D = add_mset l C'"
    using multi_member_split[OF l_in_D]
    by blast

  obtain t t' where l: "l = t !\<approx> t'"
    using l_\<gamma> obtain_from_neg_literal_subst
    by meson

  obtain \<mu> \<sigma> where 
    \<gamma>: "\<gamma> = \<mu> \<odot> \<sigma>" and
    type_preserving_\<mu>: "type_preserving_on (clause.vars D) \<V> \<mu>" and
    imgu: "term.is_imgu \<mu> {{t, t'}}"
  proof (rule obtain_type_preserving_on_imgu[OF _ that], intro conjI)

    show "t \<cdot>t \<gamma> = t' \<cdot>t \<gamma>"
      using l_\<gamma>
      unfolding l
      by simp
  next

    show "type_preserving_on (term.vars t \<union> term.vars t') \<V> \<gamma>"
      using type_preserving_\<gamma>
      unfolding D l
      by simp
  qed

  show ?thesis
  proof (rule that)

    show eq_resolution: "eq_resolution (\<V>, D) (\<V>, C' \<cdot> \<mu>)"
    proof (rule eq_resolutionI, rule type_preserving_\<mu>, rule imgu)

      show "select D = {#} \<Longrightarrow> is_maximal (l \<cdot>l \<mu>) (D \<cdot> \<mu>)"
      proof -
        assume "select D = {#}"

        then have "?select\<^sub>G_empty"
          using select 
          by auto

        moreover have "l \<cdot>l \<mu> \<in># D \<cdot> \<mu>"
          using l_in_D
          by blast

        ultimately show "is_maximal (l \<cdot>l \<mu>) (D \<cdot> \<mu>)"
          using l_\<gamma>_is_maximal is_maximal_if_grounding_is_maximal D_grounding
          unfolding \<gamma>
          by simp
      qed

      show "select D \<noteq> {#} \<Longrightarrow> is_maximal (l \<cdot>l \<mu>) (select D \<cdot> \<mu>)"
      proof -
        assume "select D \<noteq> {#}"

        then have "\<not>?select\<^sub>G_empty"
          using select 
          by auto

        moreover then have "l \<cdot>l \<mu> \<in># select D \<cdot> \<mu>"
          using l_selected maximal_in_clause
          by blast

        ultimately show ?thesis
          using
            select_ground_subst[OF D_grounding]
            l_\<gamma>_selected
            is_maximal_if_grounding_is_maximal
          unfolding \<gamma>
          by auto
      qed
    qed (rule D, rule l, rule refl)

    show C'_\<mu>_\<gamma>: "C' \<cdot> \<mu> \<cdot> \<gamma> = C \<cdot> \<gamma>"
    proof-
      have "term.is_idem \<mu>"
        using imgu
        unfolding term.is_imgu_iff_is_idem_and_is_mgu
        by blast

      then have \<mu>_\<gamma>: "\<mu> \<odot> \<gamma> = \<gamma>"
        unfolding \<gamma> term.is_idem_def term.assoc[symmetric]
        by argo

      have "D \<cdot> \<gamma> = add_mset (l \<cdot>l \<gamma>) (C \<cdot> \<gamma>)"
      proof-
        have "clause.to_ground (D \<cdot> \<gamma>) = clause.to_ground (add_mset (l \<cdot>l \<gamma>) (C \<cdot> \<gamma>))"
          using ground_eq_resolutionI(1)
          unfolding ground_eq_resolutionI(2) l_\<gamma> ground_eq_resolutionI(4)[symmetric]
          by simp

        moreover have "clause.is_ground (add_mset (l \<cdot>l \<gamma>) (C \<cdot> \<gamma>))"
          using C_grounding clause.to_set_is_ground_subst[OF l_in_D D_grounding]
          by simp

        ultimately show ?thesis
          using clause.to_ground_eq[OF D_grounding]
          by blast
      qed

      then have "C' \<cdot> \<gamma> = C \<cdot> \<gamma>"
        unfolding D
        by simp

      then show ?thesis
        unfolding clause.subst_comp_subst[symmetric] \<mu>_\<gamma>.
    qed

    show "Infer [D\<^sub>G] C\<^sub>G \<in> inference_ground_instances (Infer [(\<V>, D)] (\<V>, C' \<cdot> \<mu>))"
    proof (rule is_inference_ground_instance_one_premise)

      show "is_inference_ground_instance_one_premise (\<V>, D) (\<V>, C' \<cdot> \<mu>) (Infer [D\<^sub>G] C\<^sub>G) \<gamma>"
      proof(unfold split, intro conjI; (rule type_preserving_literals refl \<V>)?)

        show "inference.is_ground (Infer [D] (C' \<cdot> \<mu>) \<cdot>\<iota> \<gamma>)"
          using D_grounding C_grounding C'_\<mu>_\<gamma>
          by auto
      next

        show "Infer [D\<^sub>G] C\<^sub>G = inference.to_ground (Infer [D] (C' \<cdot> \<mu>) \<cdot>\<iota> \<gamma>)"
          using C'_\<mu>_\<gamma>
          by simp
      next

        have "clause.vars (C' \<cdot> \<mu>) \<subseteq> clause.vars D"
          using clause.variables_in_base_imgu imgu
          unfolding D l
          by auto

        then show "type_preserving_on (clause.vars (C' \<cdot> \<mu>)) \<V> \<gamma>"
          using type_preserving_\<gamma>
          by blast
      next

        show "type_preserving_literals \<V> (C' \<cdot> \<mu>)"
          using type_preserving_literals
          unfolding eq_resolution_type_preserving_literals[OF eq_resolution] .
      qed

      show "Infer [D\<^sub>G] C\<^sub>G \<in> ground.G_Inf"
        unfolding ground.G_Inf_def
        using ground_eq_resolution
        by blast
    qed
  qed
qed

lemma eq_factoring_lifting:
  fixes
    D\<^sub>G C\<^sub>G :: "'t\<^sub>G ground_clause" and
    D C :: "'t clause" and
    \<gamma> :: "'v \<Rightarrow> 't"
  defines
    [simp]: "D\<^sub>G \<equiv> clause.to_ground (D \<cdot> \<gamma>)" and
    [simp]: "C\<^sub>G \<equiv> clause.to_ground (C \<cdot> \<gamma>)"
  assumes
    ground_eq_factoring: "ground.eq_factoring D\<^sub>G C\<^sub>G" and
    D_grounding: "clause.is_ground (D \<cdot> \<gamma>)" and
    C_grounding: "clause.is_ground (C \<cdot> \<gamma>)" and
    select: "clause.from_ground (select\<^sub>G D\<^sub>G) = (select D) \<cdot> \<gamma>" and
    type_preserving_literals: "type_preserving_literals \<V> D" and
    type_preserving_\<gamma>: "type_preserving_on (clause.vars D) \<V> \<gamma>" and
    \<V>: "infinite_variables_per_type \<V>"
  obtains C'
  where
    "eq_factoring (\<V>, D) (\<V>, C')"
    "Infer [D\<^sub>G] C\<^sub>G \<in> inference_ground_instances (Infer [(\<V>, D)] (\<V>, C'))"
    "C' \<cdot> \<gamma> = C \<cdot> \<gamma>"
  using ground_eq_factoring
proof(cases D\<^sub>G C\<^sub>G rule: ground.eq_factoring.cases)
  case ground_eq_factoringI: (eq_factoringI l\<^sub>G\<^sub>1 l\<^sub>G\<^sub>2 D\<^sub>G' t\<^sub>G\<^sub>1 t\<^sub>G\<^sub>2 t\<^sub>G\<^sub>3)

  have "D \<noteq> {#}"
    using ground_eq_factoringI(1)
    by auto

  then obtain l\<^sub>1 where
    l\<^sub>1_is_maximal: "is_maximal l\<^sub>1 D" and
    l\<^sub>1_\<gamma>_is_maximal: "is_maximal (l\<^sub>1 \<cdot>l \<gamma>) (D \<cdot> \<gamma>)"
    using that obtain_maximal_literal D_grounding
    by blast

  obtain t\<^sub>1 t\<^sub>1' where
    l\<^sub>1: "l\<^sub>1 = t\<^sub>1 \<approx> t\<^sub>1'" and
    l\<^sub>1_\<gamma>: "l\<^sub>1 \<cdot>l \<gamma> = term.from_ground t\<^sub>G\<^sub>1 \<approx> term.from_ground t\<^sub>G\<^sub>2" and
    t\<^sub>1_\<gamma>: "t\<^sub>1 \<cdot>t \<gamma> = term.from_ground t\<^sub>G\<^sub>1" and
    t\<^sub>1'_\<gamma>: "t\<^sub>1' \<cdot>t \<gamma> = term.from_ground t\<^sub>G\<^sub>2"
  proof -
    have "is_maximal (literal.from_ground l\<^sub>G\<^sub>1) (D \<cdot> \<gamma>)"
      using ground_eq_factoringI(5) D_grounding
      by simp

    then have "l\<^sub>1 \<cdot>l \<gamma> = term.from_ground t\<^sub>G\<^sub>1 \<approx> term.from_ground t\<^sub>G\<^sub>2"
      unfolding  ground_eq_factoringI(2)
      using unique_maximal_in_ground_clause[OF D_grounding l\<^sub>1_\<gamma>_is_maximal]
      by simp

    then show ?thesis
      using that
      unfolding ground_eq_factoringI(2)
      by (metis obtain_from_pos_literal_subst)
  qed

  obtain l\<^sub>2 D' where
    l\<^sub>2_\<gamma>: "l\<^sub>2 \<cdot>l \<gamma> = term.from_ground t\<^sub>G\<^sub>1 \<approx> term.from_ground t\<^sub>G\<^sub>3" and
    D: "D = add_mset l\<^sub>1 (add_mset l\<^sub>2 D')"
  proof -
    obtain D'' where D: "D = add_mset l\<^sub>1 D''"
      using maximal_in_clause[OF l\<^sub>1_is_maximal]
      by (meson multi_member_split)

    moreover have "D \<cdot> \<gamma> = clause.from_ground (add_mset l\<^sub>G\<^sub>1 (add_mset l\<^sub>G\<^sub>2 D\<^sub>G'))"
      using ground_eq_factoringI(1) D\<^sub>G_def
      by (metis D_grounding clause.to_ground_inverse)

    ultimately have "D'' \<cdot> \<gamma> =  add_mset (literal.from_ground l\<^sub>G\<^sub>2) (clause.from_ground D\<^sub>G')"
      using  l\<^sub>1_\<gamma>
      by (simp add: ground_eq_factoringI(2))

    then obtain l\<^sub>2 where "l\<^sub>2 \<cdot>l \<gamma> = term.from_ground t\<^sub>G\<^sub>1 \<approx> term.from_ground t\<^sub>G\<^sub>3" "l\<^sub>2 \<in># D''"
      unfolding clause.subst_def ground_eq_factoringI
      using msed_map_invR
      by force

    then show ?thesis
      using that
      unfolding D
      by (metis mset_add)
  qed

  then obtain t\<^sub>2 t\<^sub>2' where
    l\<^sub>2: "l\<^sub>2 = t\<^sub>2 \<approx> t\<^sub>2'" and
    t\<^sub>2_\<gamma>: "t\<^sub>2 \<cdot>t \<gamma> = term.from_ground t\<^sub>G\<^sub>1" and
    t\<^sub>2'_\<gamma>: "t\<^sub>2' \<cdot>t \<gamma> = term.from_ground t\<^sub>G\<^sub>3"
    unfolding ground_eq_factoringI(3)
    using obtain_from_pos_literal_subst
    by metis

  have D'_\<gamma>: "D' \<cdot> \<gamma> = clause.from_ground D\<^sub>G'"
    using D D_grounding ground_eq_factoringI(1,2,3) l\<^sub>1_\<gamma> l\<^sub>2_\<gamma>
    by force

  obtain \<mu> \<sigma> where 
    \<gamma>: "\<gamma> = \<mu> \<odot> \<sigma>" and 
    type_preserving_\<mu>: "type_preserving_on (clause.vars D) \<V> \<mu>" and
    imgu: "term.is_imgu \<mu> {{t\<^sub>1, t\<^sub>2}}"
  proof (rule obtain_type_preserving_on_imgu[OF _ that], intro conjI)

    show "t\<^sub>1 \<cdot>t \<gamma> = t\<^sub>2 \<cdot>t \<gamma>"
      unfolding t\<^sub>1_\<gamma> t\<^sub>2_\<gamma> ..
  next

    show "type_preserving_on (term.vars t\<^sub>1 \<union> term.vars t\<^sub>2) \<V> \<gamma>"
      using type_preserving_\<gamma>
      unfolding D l\<^sub>1 l\<^sub>2
      by auto
  qed

  let ?C'' = "add_mset (t\<^sub>1 \<approx> t\<^sub>2') (add_mset (t\<^sub>1' !\<approx> t\<^sub>2') D')"
  let ?C' = "?C'' \<cdot> \<mu>"

  show ?thesis
  proof (rule that)

    show eq_factoring: "eq_factoring (\<V>, D) (\<V>, ?C')"
    proof (rule eq_factoringI; (rule D l\<^sub>1 l\<^sub>2 type_preserving_\<mu> imgu refl \<V>)?)
      show "select D = {#}"
        using ground_eq_factoringI(4) select
        by simp
    next
      have "l\<^sub>1 \<cdot>l \<mu> \<in># D \<cdot> \<mu>"
        using l\<^sub>1_is_maximal clause.subst_in_to_set_subst maximal_in_clause
        by blast

      then show "is_maximal (l\<^sub>1 \<cdot>l \<mu>) (D \<cdot> \<mu>)"
        using is_maximal_if_grounding_is_maximal D_grounding l\<^sub>1_\<gamma>_is_maximal
        unfolding \<gamma>
        by auto
    next
      have groundings: "term.is_ground (t\<^sub>1' \<cdot>t \<mu> \<cdot>t \<sigma>)" "term.is_ground (t\<^sub>1 \<cdot>t \<mu> \<cdot>t \<sigma>)"
        using t\<^sub>1'_\<gamma> t\<^sub>1_\<gamma>
        unfolding \<gamma>
        by simp_all

      have "t\<^sub>1' \<cdot>t \<gamma> \<prec>\<^sub>t t\<^sub>1 \<cdot>t \<gamma>"
        using ground_eq_factoringI(6)
        unfolding t\<^sub>1'_\<gamma> t\<^sub>1_\<gamma> term.order.less\<^sub>G_def.

      then show "\<not> t\<^sub>1 \<cdot>t \<mu> \<preceq>\<^sub>t t\<^sub>1' \<cdot>t \<mu>"
        unfolding \<gamma>
        using term.order.ground_less_not_less_eq[OF groundings]
        by simp
    qed

    show C'_\<gamma>: "?C' \<cdot> \<gamma> = C \<cdot> \<gamma>"
    proof -
      have "term.is_idem \<mu>"
        using imgu
        unfolding term.is_imgu_iff_is_idem_and_is_mgu
        by blast

      then have \<mu>_\<gamma>: "\<mu> \<odot> \<gamma> = \<gamma>"
        unfolding \<gamma> term.is_idem_def term.assoc[symmetric]
        by argo

      have "C \<cdot> \<gamma> = clause.from_ground (add_mset (t\<^sub>G\<^sub>2 !\<approx> t\<^sub>G\<^sub>3) (add_mset (t\<^sub>G\<^sub>1 \<approx> t\<^sub>G\<^sub>3) D\<^sub>G'))"
        using ground_eq_factoringI(7) clause.to_ground_eq[OF C_grounding clause.ground_is_ground]
        unfolding C\<^sub>G_def
        by (metis clause.from_ground_inverse)

      also have "... = ?C'' \<cdot> \<gamma>"
        using t\<^sub>1_\<gamma> t\<^sub>1'_\<gamma> t\<^sub>2'_\<gamma> D'_\<gamma>
        by simp

      also have "... = ?C' \<cdot> \<gamma>"
        unfolding clause.subst_comp_subst[symmetric] \<mu>_\<gamma> ..

      finally show ?thesis ..
    qed

    show "Infer [D\<^sub>G] C\<^sub>G \<in> inference_ground_instances (Infer [(\<V>, D)] (\<V>, ?C'))"
    proof (rule is_inference_ground_instance_one_premise)

      show "is_inference_ground_instance_one_premise (\<V>, D) (\<V>, ?C') (Infer [D\<^sub>G] C\<^sub>G) \<gamma>"
      proof(unfold split, intro conjI; (rule type_preserving_literals refl \<V>)?)

        show "inference.is_ground (Infer [D] ?C' \<cdot>\<iota> \<gamma>)"
          using C_grounding D_grounding C'_\<gamma>
          by auto
      next

        show "Infer [D\<^sub>G] C\<^sub>G = inference.to_ground (Infer [D] ?C' \<cdot>\<iota> \<gamma>)"
          using C'_\<gamma>
          by simp
      next

        have imgu: "term.is_imgu \<mu> {{t\<^sub>1, t\<^sub>2}}"
          using imgu
          by blast

        have "clause.vars ?C' \<subseteq> clause.vars D"
          using clause.variables_in_base_imgu[OF imgu, of ?C'']
          unfolding D l\<^sub>1 l\<^sub>2
          by auto

        then show "type_preserving_on (clause.vars ?C') \<V> \<gamma>"
          using type_preserving_\<gamma>
          by blast
      next

        show "type_preserving_literals \<V> ?C'"
          using type_preserving_literals
          unfolding eq_factoring_type_preserving_literals[OF eq_factoring] .
      qed

      show "Infer [D\<^sub>G] C\<^sub>G \<in> ground.G_Inf"
        unfolding ground.G_Inf_def
        using ground_eq_factoring
        by blast
    qed
  qed
qed

lemma superposition_lifting:
  fixes
    E\<^sub>G D\<^sub>G C\<^sub>G :: "'t\<^sub>G ground_clause" and
    E D C :: "'t clause" and
    \<gamma> \<rho>\<^sub>1 \<rho>\<^sub>2 :: "'v \<Rightarrow> 't" and
    \<V>\<^sub>1 \<V>\<^sub>2 :: "('v, 'ty) var_types"
  defines
    [simp]: "E\<^sub>G \<equiv> clause.to_ground (E \<cdot> \<rho>\<^sub>1 \<odot> \<gamma>)" and
    [simp]: "D\<^sub>G \<equiv> clause.to_ground (D \<cdot> \<rho>\<^sub>2 \<odot> \<gamma>)" and
    [simp]: "C\<^sub>G \<equiv> clause.to_ground (C \<cdot> \<gamma>)" and
    [simp]: "N\<^sub>G \<equiv> ground_instances \<V>\<^sub>1 E \<union> ground_instances \<V>\<^sub>2 D" and
    [simp]: "\<iota>\<^sub>G \<equiv> Infer [D\<^sub>G, E\<^sub>G] C\<^sub>G"
  assumes
    ground_superposition: "ground.superposition D\<^sub>G E\<^sub>G C\<^sub>G" and
    \<rho>\<^sub>1: "term.is_renaming \<rho>\<^sub>1" and
    \<rho>\<^sub>2: "term.is_renaming \<rho>\<^sub>2" and
    rename_apart: "clause.vars (E \<cdot> \<rho>\<^sub>1) \<inter> clause.vars (D \<cdot> \<rho>\<^sub>2) = {}" and
    E_grounding: "clause.is_ground (E \<cdot> \<rho>\<^sub>1 \<odot> \<gamma>)" and
    D_grounding: "clause.is_ground (D \<cdot> \<rho>\<^sub>2 \<odot> \<gamma>)" and
    C_grounding: "clause.is_ground (C \<cdot> \<gamma>)" and
    select_from_E: "clause.from_ground (select\<^sub>G E\<^sub>G) = (select E) \<cdot> \<rho>\<^sub>1 \<odot> \<gamma>" and
    select_from_D: "clause.from_ground (select\<^sub>G D\<^sub>G) = (select D) \<cdot> \<rho>\<^sub>2 \<odot> \<gamma>" and
    type_preserving_literals_E: "type_preserving_literals \<V>\<^sub>1 E" and
    type_preserving_literals_D: "type_preserving_literals \<V>\<^sub>2 D" and
    type_preserving_\<rho>\<^sub>1_\<gamma>: "type_preserving_on (clause.vars E) \<V>\<^sub>1 (\<rho>\<^sub>1 \<odot> \<gamma>)" and
    type_preserving_\<rho>\<^sub>2_\<gamma>: "type_preserving_on (clause.vars D) \<V>\<^sub>2 (\<rho>\<^sub>2 \<odot> \<gamma>)" and
    type_preserving_\<rho>\<^sub>1: "type_preserving_on (clause.vars E) \<V>\<^sub>1 \<rho>\<^sub>1" and
    type_preserving_\<rho>\<^sub>2: "type_preserving_on (clause.vars D) \<V>\<^sub>2 \<rho>\<^sub>2" and
    \<V>\<^sub>1: "infinite_variables_per_type \<V>\<^sub>1" and
    \<V>\<^sub>2: "infinite_variables_per_type \<V>\<^sub>2" and
    not_redundant: "\<iota>\<^sub>G \<notin> ground.Red_I N\<^sub>G"
  obtains C' \<V>\<^sub>3
  where
    "superposition (\<V>\<^sub>2, D) (\<V>\<^sub>1, E) (\<V>\<^sub>3, C')"
    "\<iota>\<^sub>G \<in> inference_ground_instances (Infer [(\<V>\<^sub>2, D), (\<V>\<^sub>1, E)] (\<V>\<^sub>3, C'))"
    "C' \<cdot> \<gamma> = C \<cdot> \<gamma>"
  using ground_superposition
proof (cases D\<^sub>G E\<^sub>G C\<^sub>G rule: ground.superposition.cases)
  case ground_superpositionI: (superpositionI l\<^sub>G\<^sub>1 E\<^sub>G' l\<^sub>G\<^sub>2 D\<^sub>G' \<P>\<^sub>G c\<^sub>G t\<^sub>G\<^sub>1 t\<^sub>G\<^sub>2 t\<^sub>G\<^sub>3)

  have E_\<gamma>: "E \<cdot> \<rho>\<^sub>1 \<odot> \<gamma> = clause.from_ground (add_mset l\<^sub>G\<^sub>1 E\<^sub>G')"
    using ground_superpositionI(1)
    unfolding E\<^sub>G_def
    by (metis E_grounding clause.to_ground_inverse)

  have D_\<gamma>: "D \<cdot> \<rho>\<^sub>2 \<odot> \<gamma> = clause.from_ground (add_mset l\<^sub>G\<^sub>2 D\<^sub>G')"
    using ground_superpositionI(2) D\<^sub>G_def
    by (metis D_grounding clause.to_ground_inverse)

  obtain l\<^sub>2 where
    l\<^sub>2_\<gamma>: "l\<^sub>2 \<cdot>l \<rho>\<^sub>2 \<odot> \<gamma> = literal.from_ground l\<^sub>G\<^sub>2" and
    l\<^sub>2_is_strictly_maximal: "is_strictly_maximal l\<^sub>2 D"
  proof-
    have "is_strictly_maximal (literal.from_ground l\<^sub>G\<^sub>2) (D \<cdot> \<rho>\<^sub>2 \<odot> \<gamma>)"
      using ground_superpositionI(11) D_grounding
      by simp

    then show ?thesis
      using obtain_strictly_maximal_literal[OF D_grounding] that
      by (metis (lifting))
  qed

  then have l\<^sub>2_in_D: "l\<^sub>2 \<in># D"
    using strictly_maximal_in_clause
    by blast

  from l\<^sub>2_\<gamma> have l\<^sub>2_\<gamma>: "l\<^sub>2 \<cdot>l \<rho>\<^sub>2 \<odot> \<gamma> = term.from_ground t\<^sub>G\<^sub>1 \<approx> term.from_ground t\<^sub>G\<^sub>3"
    unfolding ground_superpositionI
    by simp

  then obtain t\<^sub>2 t\<^sub>2' where
    l\<^sub>2: "l\<^sub>2 = t\<^sub>2 \<approx> t\<^sub>2'" and
    t\<^sub>2_\<gamma>: "t\<^sub>2 \<cdot>t \<rho>\<^sub>2 \<odot> \<gamma> = term.from_ground t\<^sub>G\<^sub>1" and
    t\<^sub>2'_\<gamma>: "t\<^sub>2' \<cdot>t \<rho>\<^sub>2 \<odot> \<gamma> = term.from_ground t\<^sub>G\<^sub>3"
    using obtain_from_pos_literal_subst
    by metis

  obtain D' where D: "D = add_mset l\<^sub>2 D'"
    by (meson l\<^sub>2_in_D multi_member_split)

  then have D'_\<gamma>: "D' \<cdot> \<rho>\<^sub>2 \<odot> \<gamma> = clause.from_ground D\<^sub>G'"
    using D_\<gamma> l\<^sub>2_\<gamma>
    unfolding ground_superpositionI
    by auto

  let ?select\<^sub>G_empty = "select\<^sub>G (clause.to_ground (E \<cdot> \<rho>\<^sub>1 \<odot> \<gamma>)) = {#}"
  let ?select\<^sub>G_not_empty = "select\<^sub>G (clause.to_ground (E \<cdot> \<rho>\<^sub>1 \<odot> \<gamma>)) \<noteq> {#}"

  obtain l\<^sub>1 where
    l\<^sub>1_\<gamma>: "l\<^sub>1 \<cdot>l \<rho>\<^sub>1 \<odot> \<gamma> = literal.from_ground l\<^sub>G\<^sub>1" and
    l\<^sub>1_is_strictly_maximal: "\<P>\<^sub>G = Pos \<Longrightarrow> is_strictly_maximal l\<^sub>1 E" and
    l\<^sub>1_is_maximal: "\<P>\<^sub>G = Neg \<Longrightarrow> ?select\<^sub>G_empty \<Longrightarrow> is_maximal l\<^sub>1 E" and
    l\<^sub>1_selected: "\<P>\<^sub>G = Neg \<Longrightarrow> ?select\<^sub>G_not_empty \<Longrightarrow> is_maximal l\<^sub>1 (select E)" and
    l\<^sub>1_in_E: "l\<^sub>1 \<in># E"
  proof-

    have E_not_empty: "E \<noteq> {#}"
      using ground_superpositionI(1)
      by auto

    have "is_strictly_maximal (literal.from_ground l\<^sub>G\<^sub>1) (E \<cdot> \<rho>\<^sub>1 \<odot> \<gamma>)" if "\<P>\<^sub>G = Pos"
      using ground_superpositionI(9) that E_grounding
      by simp

    then obtain positive_l\<^sub>1 where
      "is_strictly_maximal positive_l\<^sub>1 E"
      "positive_l\<^sub>1 \<cdot>l \<rho>\<^sub>1 \<odot> \<gamma> = literal.from_ground l\<^sub>G\<^sub>1"
    if "\<P>\<^sub>G = Pos"
      using obtain_strictly_maximal_literal[OF E_grounding]
      by (metis (lifting))

    moreover then have "positive_l\<^sub>1 \<in># E" if "\<P>\<^sub>G = Pos"
      using that strictly_maximal_in_clause
      by blast

    moreover then have "is_maximal (literal.from_ground l\<^sub>G\<^sub>1) (E \<cdot> \<rho>\<^sub>1 \<odot> \<gamma>)" if ?select\<^sub>G_empty
      using that ground_superpositionI(9) is_maximal_not_empty E_grounding
      by auto

    then obtain negative_maximal_l\<^sub>1 where
      "is_maximal negative_maximal_l\<^sub>1 E"
      "negative_maximal_l\<^sub>1 \<cdot>l \<rho>\<^sub>1 \<odot> \<gamma> = literal.from_ground l\<^sub>G\<^sub>1"
    if "\<P>\<^sub>G = Neg" ?select\<^sub>G_empty
      using
        obtain_maximal_literal[OF E_not_empty E_grounding[folded clause.subst_comp_subst]]
        unique_maximal_in_ground_clause[OF E_grounding[folded clause.subst_comp_subst]]
      by (metis (lifting))

    moreover then have "negative_maximal_l\<^sub>1 \<in># E" if "\<P>\<^sub>G = Neg" ?select\<^sub>G_empty
      using that maximal_in_clause
      by blast

    moreover have "ground_is_maximal l\<^sub>G\<^sub>1 (select\<^sub>G E\<^sub>G)" if "\<P>\<^sub>G = Neg" ?select\<^sub>G_not_empty
      using ground_superpositionI(9) that
      by simp

    then obtain negative_selected_l\<^sub>1 where
      "is_maximal negative_selected_l\<^sub>1 (select E)"
      "negative_selected_l\<^sub>1 \<cdot>l \<rho>\<^sub>1 \<odot> \<gamma> = literal.from_ground l\<^sub>G\<^sub>1"
    if "\<P>\<^sub>G = Neg" ?select\<^sub>G_not_empty
      using
        select_from_E
        unique_maximal_in_ground_clause
        obtain_maximal_literal
      unfolding E\<^sub>G_def
      by (metis (no_types, lifting) clause.ground_is_ground clause.from_ground_empty'
          clause.magma_subst_empty)

    moreover then have "negative_selected_l\<^sub>1 \<in># E" if "\<P>\<^sub>G = Neg" ?select\<^sub>G_not_empty
      using that maximal_in_clause mset_subset_eqD select_subset
      by meson

    ultimately show ?thesis
      using that ground_superpositionI(9)
      by (metis (lifting) literals_distinct(1))
  qed

  obtain E' where E: "E = add_mset l\<^sub>1 E'"
    by (meson l\<^sub>1_in_E multi_member_split)

  then have E'_\<gamma>: "E' \<cdot> \<rho>\<^sub>1 \<odot> \<gamma> = clause.from_ground E\<^sub>G'"
    using l\<^sub>1_\<gamma> E_\<gamma>
    by auto

  have [simp]: "\<P>\<^sub>G \<noteq> Pos \<longleftrightarrow> \<P>\<^sub>G = Neg" "\<P>\<^sub>G \<noteq> Neg \<longleftrightarrow> \<P>\<^sub>G = Pos"
    using ground_superpositionI(4)
    by auto

  let ?\<P> = "if \<P>\<^sub>G = Pos then Pos else Neg"

  have \<P>: "?\<P> \<in> {Pos, Neg}"
    by simp

  note [simp] = \<P>_simps[OF \<P>]

  have l\<^sub>1_\<gamma>:
    "l\<^sub>1 \<cdot>l \<rho>\<^sub>1 \<odot> \<gamma> = ?\<P> (Upair (context.from_ground c\<^sub>G)\<langle>term.from_ground t\<^sub>G\<^sub>1\<rangle> (term.from_ground t\<^sub>G\<^sub>2))"
    unfolding ground_superpositionI l\<^sub>1_\<gamma>
    by simp

  obtain c\<^sub>1 t\<^sub>1 t\<^sub>1' where
    l\<^sub>1: "l\<^sub>1 = ?\<P> (Upair c\<^sub>1\<langle>t\<^sub>1\<rangle> t\<^sub>1')" and
    t\<^sub>1'_\<gamma>: "t\<^sub>1' \<cdot>t \<rho>\<^sub>1 \<odot> \<gamma> = term.from_ground t\<^sub>G\<^sub>2" and
    t\<^sub>1_\<gamma>: "t\<^sub>1 \<cdot>t \<rho>\<^sub>1 \<odot> \<gamma> = term.from_ground t\<^sub>G\<^sub>1" and
    c\<^sub>1_\<gamma>: "c\<^sub>1 \<cdot>t\<^sub>c \<rho>\<^sub>1 \<odot> \<gamma> = context.from_ground c\<^sub>G" and
    t\<^sub>1_is_Fun: "\<not>term.is_Var t\<^sub>1"
  proof-

    obtain c\<^sub>1_t\<^sub>1 t\<^sub>1' where
      l\<^sub>1: "l\<^sub>1 = ?\<P> (Upair c\<^sub>1_t\<^sub>1 t\<^sub>1')" and
      t\<^sub>1'_\<gamma>: "t\<^sub>1' \<cdot>t \<rho>\<^sub>1 \<odot> \<gamma> = term.from_ground t\<^sub>G\<^sub>2" and
      c\<^sub>1_t\<^sub>1_\<gamma>: "c\<^sub>1_t\<^sub>1 \<cdot>t \<rho>\<^sub>1 \<odot> \<gamma> = (context.from_ground c\<^sub>G)\<langle>term.from_ground t\<^sub>G\<^sub>1\<rangle>"
      using l\<^sub>1_\<gamma>
      by (smt (verit) obtain_from_literal_subst)

    let ?inference_into_Fun =
      "\<exists>c\<^sub>1 t\<^sub>1.
        c\<^sub>1_t\<^sub>1 = c\<^sub>1\<langle>t\<^sub>1\<rangle> \<and>
        t\<^sub>1 \<cdot>t \<rho>\<^sub>1 \<odot> \<gamma> = term.from_ground t\<^sub>G\<^sub>1 \<and>
        c\<^sub>1 \<cdot>t\<^sub>c \<rho>\<^sub>1 \<odot> \<gamma> = context.from_ground c\<^sub>G \<and>
        \<not>term.is_Var t\<^sub>1"

    have "\<not> ?inference_into_Fun \<Longrightarrow> ground.redundant_infer N\<^sub>G \<iota>\<^sub>G"
    proof -
      assume "\<not> ?inference_into_Fun"

      moreover have "term.is_ground (c\<^sub>1_t\<^sub>1 \<cdot>t \<rho>\<^sub>1 \<odot> \<gamma>)"
        using c\<^sub>1_t\<^sub>1_\<gamma>
        by auto     

      ultimately obtain t\<^sub>1 c\<^sub>1 c\<^sub>G' where
        c\<^sub>1_t\<^sub>1: "c\<^sub>1_t\<^sub>1 = c\<^sub>1\<langle>t\<^sub>1\<rangle>" and
        t\<^sub>1_is_Var: "term.is_Var t\<^sub>1" and
        c\<^sub>G: "context.from_ground c\<^sub>G = (c\<^sub>1 \<cdot>t\<^sub>c \<rho>\<^sub>1 \<odot> \<gamma>) \<circ>\<^sub>c c\<^sub>G'"
        using context.subst_into_Var[OF c\<^sub>1_t\<^sub>1_\<gamma>]
        by metis

      then have c\<^sub>G'_is_ground [simp]: "context.is_ground c\<^sub>G'"
        by (metis context.composed_context_is_ground context.ground_is_ground)

      obtain x where t\<^sub>1_\<rho>\<^sub>1: "t\<^sub>1 \<cdot>t \<rho>\<^sub>1 = Var x"
        using t\<^sub>1_is_Var term.id_subst_rename[OF \<rho>\<^sub>1]
        by (metis term.comp_subst_iff term.left_neutral)

      have \<iota>\<^sub>G_parts:
        "set (side_prems_of \<iota>\<^sub>G) = {D\<^sub>G}"
        "main_prem_of \<iota>\<^sub>G = E\<^sub>G"
        "concl_of \<iota>\<^sub>G = C\<^sub>G"
        by simp_all

      show ?thesis
      proof(rule ground.redundant_infer_singleton, unfold \<iota>\<^sub>G_parts, intro bexI conjI)

        let ?t\<^sub>G = "c\<^sub>G'\<langle>term.from_ground t\<^sub>G\<^sub>3\<rangle>"

        define \<gamma>' where
          "\<gamma>' \<equiv> \<gamma>(x := ?t\<^sub>G)"

        let ?E\<^sub>G' = "clause.to_ground (E \<cdot> \<rho>\<^sub>1 \<odot> \<gamma>')"

        have t\<^sub>1_\<gamma>: "t\<^sub>1 \<cdot>t \<rho>\<^sub>1 \<odot> \<gamma> = c\<^sub>G'\<langle>term.from_ground t\<^sub>G\<^sub>1\<rangle>"
        proof -

          have "context.is_ground (c\<^sub>1 \<cdot>t\<^sub>c \<rho>\<^sub>1 \<odot> \<gamma>)"
            using c\<^sub>1_t\<^sub>1_\<gamma>
            unfolding c\<^sub>1_t\<^sub>1 context.safe_unfolds
            by (metis context.apply_context_is_ground context.apply_context_subst 
                context.safe_unfolds(2) term.ground_is_ground)

          then show ?thesis
            using c\<^sub>1_t\<^sub>1_\<gamma>
            unfolding c\<^sub>1_t\<^sub>1 c\<^sub>1_t\<^sub>1_\<gamma> c\<^sub>G
            by (auto simp: context.apply_context_eq)
            
        qed

        have t\<^sub>1_\<gamma>': "t\<^sub>1 \<cdot>t \<rho>\<^sub>1 \<odot> \<gamma>' = c\<^sub>G'\<langle>term.from_ground t\<^sub>G\<^sub>3\<rangle>"
          unfolding \<gamma>'_def
          using t\<^sub>1_\<rho>\<^sub>1
          by auto         
 
        show "?E\<^sub>G' \<in> N\<^sub>G"
        proof -

          have "?E\<^sub>G' \<in> ground_instances \<V>\<^sub>1 E"
          proof (unfold ground_instances_def mem_Collect_eq fst_conv snd_conv,
              intro exI conjI \<V>\<^sub>1 type_preserving_literals_E, 
              rule refl)

            show "clause.is_ground (E \<cdot> \<rho>\<^sub>1 \<odot> \<gamma>')"
              unfolding \<gamma>'_def
              using E_grounding 
              by force
          next

            show "type_preserving_on (clause.vars E) \<V>\<^sub>1 (\<rho>\<^sub>1 \<odot> \<gamma>')"
            proof (rule term.type_preserving_on_subst_compose[OF type_preserving_\<rho>\<^sub>1])

              have \<gamma>_type_preserving: "type_preserving_on (\<Union> (term.vars ` \<rho>\<^sub>1 ` clause.vars E)) \<V>\<^sub>1 \<gamma>"
                using 
                  term.type_preserving_on_subst_compose_renaming[OF 
                    \<rho>\<^sub>1 type_preserving_\<rho>\<^sub>1 type_preserving_\<rho>\<^sub>1_\<gamma>] .

              then show "type_preserving_on (\<Union> (term.vars ` \<rho>\<^sub>1 ` clause.vars E)) \<V>\<^sub>1 \<gamma>'"
              proof (unfold \<gamma>'_def, rule type_preserving_on_subst_update, intro impI)

                assume
                  x_in_E_\<rho>\<^sub>1: "x \<in> \<Union> (term.vars ` \<rho>\<^sub>1 ` clause.vars E)" and 
                  welltyped_x: "\<V>\<^sub>1 \<turnstile> Var x : \<V>\<^sub>1 x"

                then obtain \<tau> where welltyped_t\<^sub>G\<^sub>1: "\<V>\<^sub>1 \<turnstile> term.from_ground t\<^sub>G\<^sub>1 : \<tau>"
                  using welltyped_x 
                  by (metis \<gamma>_type_preserving t\<^sub>1_\<gamma> t\<^sub>1_\<rho>\<^sub>1 
                      term.comp_subst.left.monoid_action_compatibility
                      term.comp_subst_iff term.left_neutral term.welltyped_subterm)
                
                show "\<V>\<^sub>1 \<turnstile> ?t\<^sub>G : \<V>\<^sub>1 x"
                proof (rule term.welltyped_context_compatible[OF welltyped_t\<^sub>G\<^sub>1])

                  have "\<V>\<^sub>2 \<turnstile> term.from_ground t\<^sub>G\<^sub>1 : \<tau>"
                    using welltyped_t\<^sub>G\<^sub>1 term.ground_is_ground term.is_ground_replace_\<V>
                    by blast

                  then have "\<V>\<^sub>2 \<turnstile> t\<^sub>2 : \<tau>"
                    using term.welltyped_subst_stability'[OF type_preserving_\<rho>\<^sub>2_\<gamma>]
                    unfolding D l\<^sub>2 t\<^sub>2_\<gamma>[symmetric]
                    by auto

                   then have "\<V>\<^sub>2 \<turnstile> t\<^sub>2' : \<tau>"
                    using type_preserving_literals_D
                    unfolding D l\<^sub>2
                    by auto

                  then have "\<V>\<^sub>2 \<turnstile> term.from_ground t\<^sub>G\<^sub>3 : \<tau>"
                    using term.welltyped_subst_stability'[OF type_preserving_\<rho>\<^sub>2_\<gamma>]
                    unfolding D l\<^sub>2 t\<^sub>2'_\<gamma>[symmetric]
                    by auto
                    
                  then show "\<V>\<^sub>1 \<turnstile> term.from_ground t\<^sub>G\<^sub>3 : \<tau>"
                    using term.ground_is_ground term.is_ground_replace_\<V>
                    by blast
                next

                  show "\<V>\<^sub>1 \<turnstile> c\<^sub>G'\<langle>term.from_ground t\<^sub>G\<^sub>1\<rangle> : \<V>\<^sub>1 x"
                    using welltyped_x t\<^sub>1_\<rho>\<^sub>1 \<gamma>_type_preserving x_in_E_\<rho>\<^sub>1
                    unfolding t\<^sub>1_\<gamma>[symmetric]
                    by (metis t\<^sub>1_is_Var term.comp_subst_iff term.left_neutral)
                qed
              qed
            qed
          qed

          then show ?thesis
            by simp
        qed

        show "ground.G_entails {?E\<^sub>G', D\<^sub>G} {C\<^sub>G}"
        proof(unfold ground.G_entails_def, intro allI impI)
          fix I :: "'t\<^sub>G rel"
          let ?I = "upair ` I"

          assume
            "refl I" "trans I" "sym I" "compatible_with_context I" and
            premise: "?I \<TTurnstile>s {?E\<^sub>G', D\<^sub>G}"

          then interpret clause_entailment where I = I
            by unfold_locales

          have \<gamma>_x_is_ground: "term.is_ground (\<gamma> x)"
            using t\<^sub>1_\<gamma> t\<^sub>1_\<rho>\<^sub>1 c\<^sub>G'_is_ground
            by auto

          show "?I \<TTurnstile>s {C\<^sub>G}"
          proof(cases "?I \<TTurnstile> D\<^sub>G'")
            case True

            then show ?thesis
              unfolding ground_superpositionI
              by auto
          next
            case False

            then have t\<^sub>G\<^sub>1_t\<^sub>G\<^sub>3: "Upair t\<^sub>G\<^sub>1 t\<^sub>G\<^sub>3 \<in> ?I"
              using premise sym
              unfolding ground_superpositionI
              by auto

            have "?I \<TTurnstile>l (context.to_ground c\<^sub>G')\<langle>t\<^sub>G\<^sub>1\<rangle>\<^sub>G \<approx> (context.to_ground c\<^sub>G')\<langle>t\<^sub>G\<^sub>3\<rangle>\<^sub>G"
              using upair_compatible_with_gctxtI[OF t\<^sub>G\<^sub>1_t\<^sub>G\<^sub>3]
              by auto

            then have "?I \<TTurnstile>l term.to_ground (t\<^sub>1 \<cdot>t \<rho>\<^sub>1 \<odot> \<gamma>) \<approx> term.to_ground (t\<^sub>1 \<cdot>t \<rho>\<^sub>1 \<odot> \<gamma>')"
              unfolding t\<^sub>1_\<gamma> t\<^sub>1_\<gamma>'
              by simp

            then have "(term.to_ground (\<gamma> x), (context.to_ground c\<^sub>G')\<langle>t\<^sub>G\<^sub>3\<rangle>\<^sub>G) \<in> I"
              unfolding \<gamma>'_def
              using t\<^sub>1_\<rho>\<^sub>1
              by (auto simp: sym)
 
            moreover have "?I \<TTurnstile> ?E\<^sub>G'"
              using premise
              by simp

            ultimately have "?I \<TTurnstile> E\<^sub>G"
              unfolding \<gamma>'_def
              using clause.symmetric_congruence[of _ \<gamma>, OF _ \<gamma>_x_is_ground] E_grounding
              by simp

            then have "?I \<TTurnstile> add_mset (\<P>\<^sub>G (Upair c\<^sub>G\<langle>t\<^sub>G\<^sub>3\<rangle>\<^sub>G t\<^sub>G\<^sub>2)) E\<^sub>G'"
              unfolding ground_superpositionI
              using symmetric_literal_context_congruence[OF t\<^sub>G\<^sub>1_t\<^sub>G\<^sub>3]
              by (cases "\<P>\<^sub>G = Pos") simp_all

            then show ?thesis
              unfolding ground_superpositionI
              by blast
          qed
        qed

        show "?E\<^sub>G' \<prec>\<^sub>c\<^sub>G E\<^sub>G"
        proof-

          have "\<gamma> x = t\<^sub>1 \<cdot>t \<rho>\<^sub>1 \<odot> \<gamma>"
            using t\<^sub>1_\<rho>\<^sub>1
            by (metis t\<^sub>1_is_Var term.comp_subst_iff term.left_neutral)

          then have t\<^sub>G_smaller: "?t\<^sub>G \<prec>\<^sub>t \<gamma> x"
            using ground_superpositionI(8)
            unfolding t\<^sub>1_\<gamma> term.order.less\<^sub>G_def 
            by simp

          have "add_mset (l\<^sub>1 \<cdot>l \<rho>\<^sub>1 \<odot> \<gamma>') (E' \<cdot> \<rho>\<^sub>1 \<odot> \<gamma>') \<prec>\<^sub>c add_mset (l\<^sub>1 \<cdot>l \<rho>\<^sub>1 \<odot> \<gamma>) (E' \<cdot> \<rho>\<^sub>1 \<odot> \<gamma>)"
          proof(rule less\<^sub>c_add_mset)

            have "x \<in> literal.vars (l\<^sub>1 \<cdot>l \<rho>\<^sub>1)"
              unfolding l\<^sub>1 c\<^sub>1_t\<^sub>1 literal.vars_def atom.vars_def
              using t\<^sub>1_\<rho>\<^sub>1
              by auto

            moreover have "literal.is_ground (l\<^sub>1 \<cdot>l \<rho>\<^sub>1 \<odot> \<gamma>)"
              using E_grounding
              unfolding E
              by simp

            ultimately show "l\<^sub>1 \<cdot>l \<rho>\<^sub>1 \<odot> \<gamma>' \<prec>\<^sub>l l\<^sub>1 \<cdot>l \<rho>\<^sub>1 \<odot> \<gamma>"
              unfolding \<gamma>'_def
              using literal.order.subst_update_stability t\<^sub>G_smaller
              by simp
          next

            have "clause.is_ground (E' \<cdot> \<rho>\<^sub>1 \<odot> \<gamma>)"
              using E'_\<gamma>
              by simp

            then show "E' \<cdot> \<rho>\<^sub>1 \<odot> \<gamma>' \<preceq>\<^sub>c E' \<cdot> \<rho>\<^sub>1 \<odot> \<gamma>"
              unfolding \<gamma>'_def
              using clause.order.subst_update_stability t\<^sub>G_smaller
              by (cases "x \<in> clause.vars (E' \<cdot> \<rho>\<^sub>1)") simp_all
          qed

          then have "E \<cdot> \<rho>\<^sub>1 \<odot> \<gamma>' \<prec>\<^sub>c E \<cdot> \<rho>\<^sub>1 \<odot> \<gamma>"
            unfolding E
            by simp

          moreover have "clause.is_ground (E \<cdot> \<rho>\<^sub>1 \<odot> \<gamma>')"
            unfolding \<gamma>'_def
            using E_grounding
            by simp

          ultimately show ?thesis
            using E_grounding
            unfolding clause.order.less\<^sub>G_def
            by simp
        qed
      qed
    qed

    then show ?thesis
      using not_redundant ground_superposition that l\<^sub>1 t\<^sub>1'_\<gamma> c\<^sub>1_t\<^sub>1_\<gamma>
      unfolding ground.Red_I_def ground.G_Inf_def
      by auto
  qed

  obtain \<V>\<^sub>3 where
    \<V>\<^sub>3: "infinite_variables_per_type \<V>\<^sub>3" and
    \<V>\<^sub>1_\<V>\<^sub>3: "\<forall>x\<in>clause.vars E. \<V>\<^sub>1 x = \<V>\<^sub>3 (term.rename \<rho>\<^sub>1 x)" and
    \<V>\<^sub>2_\<V>\<^sub>3: "\<forall>x\<in>clause.vars D. \<V>\<^sub>2 x = \<V>\<^sub>3 (term.rename \<rho>\<^sub>2 x)"
    using clause.obtain_merged_\<V>[OF \<rho>\<^sub>1 \<rho>\<^sub>2 rename_apart clause.finite_vars clause.finite_vars 
                                 infinite_UNIV] .

  have type_preserving_\<gamma>: "type_preserving_on (clause.vars (E \<cdot> \<rho>\<^sub>1) \<union> clause.vars (D \<cdot> \<rho>\<^sub>2)) \<V>\<^sub>3 \<gamma>"
  proof(unfold Set.ball_Un, intro conjI)

    show "type_preserving_on (clause.vars (E \<cdot> \<rho>\<^sub>1)) \<V>\<^sub>3 \<gamma>"
      using clause.renaming_grounding[OF \<rho>\<^sub>1 type_preserving_\<rho>\<^sub>1_\<gamma> E_grounding \<V>\<^sub>1_\<V>\<^sub>3] .
  next

    show "type_preserving_on (clause.vars (D \<cdot> \<rho>\<^sub>2)) \<V>\<^sub>3 \<gamma>"
      using clause.renaming_grounding[OF \<rho>\<^sub>2 type_preserving_\<rho>\<^sub>2_\<gamma> D_grounding \<V>\<^sub>2_\<V>\<^sub>3] .
  qed

  obtain \<mu> \<sigma> where
    \<gamma>: "\<gamma> = \<mu> \<odot> \<sigma>" and
    type_preserving_\<mu>: "type_preserving_on (clause.vars (E \<cdot> \<rho>\<^sub>1) \<union> clause.vars (D \<cdot> \<rho>\<^sub>2)) \<V>\<^sub>3  \<mu>" and
    imgu: "term.is_imgu \<mu> {{t\<^sub>1 \<cdot>t \<rho>\<^sub>1, t\<^sub>2 \<cdot>t \<rho>\<^sub>2}}"
  proof (rule obtain_type_preserving_on_imgu[OF _ that], intro conjI)

    show "t\<^sub>1 \<cdot>t \<rho>\<^sub>1 \<cdot>t \<gamma> = t\<^sub>2 \<cdot>t \<rho>\<^sub>2 \<cdot>t \<gamma>"
      using t\<^sub>1_\<gamma> t\<^sub>2_\<gamma>
      by simp
  next

    show "type_preserving_on (term.vars (t\<^sub>1 \<cdot>t \<rho>\<^sub>1) \<union> term.vars (t\<^sub>2 \<cdot>t \<rho>\<^sub>2)) \<V>\<^sub>3 \<gamma>"
      using type_preserving_\<gamma>
      unfolding  E D l\<^sub>1 l\<^sub>2
      by auto
  qed

  define C' where
    C': "C' = add_mset (?\<P> (Upair (c\<^sub>1 \<cdot>t\<^sub>c \<rho>\<^sub>1)\<langle>t\<^sub>2' \<cdot>t \<rho>\<^sub>2\<rangle> (t\<^sub>1' \<cdot>t \<rho>\<^sub>1))) (E' \<cdot> \<rho>\<^sub>1 + D' \<cdot> \<rho>\<^sub>2) \<cdot> \<mu>"

  show ?thesis
  proof(rule that)

    show superposition: "superposition (\<V>\<^sub>2, D) (\<V>\<^sub>1, E) (\<V>\<^sub>3, C')"
    proof(rule superpositionI;
           ((rule \<rho>\<^sub>1 \<rho>\<^sub>2 E D l\<^sub>1 l\<^sub>2 t\<^sub>1_is_Fun imgu rename_apart type_preserving_\<rho>\<^sub>1 type_preserving_\<rho>\<^sub>2
               \<V>\<^sub>1 \<V>\<^sub>2 C' type_preserving_\<mu> \<V>\<^sub>1_\<V>\<^sub>3 \<V>\<^sub>2_\<V>\<^sub>3)+)?)

      show "?\<P> \<in> {Pos, Neg}"
        by simp
    next

      show "\<not> E \<cdot> \<rho>\<^sub>1 \<odot> \<mu> \<preceq>\<^sub>c D \<cdot> \<rho>\<^sub>2 \<odot> \<mu>"
      proof(rule clause.order.ground_less_not_less_eq)

        show "clause.vars (D \<cdot> \<rho>\<^sub>2 \<odot> \<mu> \<cdot> \<sigma>) = {}"
          using D_grounding
          unfolding \<gamma>
          by simp

        show "clause.vars (E \<cdot> \<rho>\<^sub>1 \<odot> \<mu> \<cdot> \<sigma>) = {}"
          using E_grounding
          unfolding \<gamma>
          by simp

        show "D \<cdot> \<rho>\<^sub>2 \<odot> \<mu> \<cdot> \<sigma> \<prec>\<^sub>c E \<cdot> \<rho>\<^sub>1 \<odot> \<mu> \<cdot> \<sigma>"
          using ground_superpositionI(3) D_grounding E_grounding
          unfolding E\<^sub>G_def D\<^sub>G_def clause.order.less\<^sub>G_def \<gamma>
          by simp
      qed
    next
      assume "?\<P> = Pos"

      then show "select E = {#}"
        using ground_superpositionI(9) select_from_E
        by fastforce

    next
      assume Pos: "?\<P> = Pos"

      show "is_strictly_maximal (l\<^sub>1 \<cdot>l \<rho>\<^sub>1 \<odot> \<mu>) (E \<cdot> \<rho>\<^sub>1 \<odot> \<mu>)"
      proof(rule is_strictly_maximal_if_grounding_is_strictly_maximal)

        show "l\<^sub>1 \<cdot>l \<rho>\<^sub>1 \<odot> \<mu> \<in># E \<cdot> \<rho>\<^sub>1 \<odot> \<mu>"
          using l\<^sub>1_in_E
          by blast

        show "clause.is_ground (E \<cdot> \<rho>\<^sub>1 \<odot> \<mu> \<cdot> \<sigma>)"
          using E_grounding[unfolded \<gamma>]
          by simp

        show "is_strictly_maximal (l\<^sub>1 \<cdot>l \<rho>\<^sub>1 \<odot> \<mu> \<cdot>l \<sigma>) (E \<cdot> \<rho>\<^sub>1 \<odot> \<mu> \<cdot> \<sigma>)"
          using Pos l\<^sub>1_\<gamma> E_\<gamma> ground_superpositionI(9)
          unfolding \<gamma> ground_superpositionI
          by fastforce
      qed
    next
      assume Neg: "?\<P> = Neg" "select E = {#}"

      show "is_maximal (l\<^sub>1 \<cdot>l \<rho>\<^sub>1 \<odot> \<mu>) (E \<cdot> \<rho>\<^sub>1 \<odot> \<mu>)"
      proof(rule is_maximal_if_grounding_is_maximal)

          show "l\<^sub>1 \<cdot>l \<rho>\<^sub>1 \<odot> \<mu> \<in># E \<cdot> \<rho>\<^sub>1 \<odot> \<mu>"
            using l\<^sub>1_in_E
            by blast
        next

          show "clause.is_ground (E \<cdot> \<rho>\<^sub>1 \<odot> \<mu> \<cdot> \<sigma>)"
            using E_grounding \<gamma>
            by auto
        next

          show "is_maximal (l\<^sub>1 \<cdot>l \<rho>\<^sub>1 \<odot> \<mu> \<cdot>l \<sigma>) (E \<cdot> \<rho>\<^sub>1 \<odot> \<mu> \<cdot> \<sigma>) "
            using l\<^sub>1_\<gamma> \<gamma> E_\<gamma> ground_superpositionI(5,9) is_maximal_not_empty Neg select_from_E
            by auto
        qed
    next
      assume Neg: "?\<P> = Neg" "select E \<noteq> {#}"

      show "is_maximal (l\<^sub>1 \<cdot>l \<rho>\<^sub>1 \<odot> \<mu>) ((select E) \<cdot> \<rho>\<^sub>1 \<odot> \<mu>)"
      proof(rule is_maximal_if_grounding_is_maximal)

        show "l\<^sub>1 \<cdot>l \<rho>\<^sub>1 \<odot> \<mu> \<in># select E \<cdot> \<rho>\<^sub>1 \<odot> \<mu>"
          using ground_superpositionI(9) l\<^sub>1_selected maximal_in_clause Neg select_from_E
          by force
      next

        show "clause.is_ground (select E \<cdot> \<rho>\<^sub>1 \<odot> \<mu> \<cdot> \<sigma>)"
          using select_ground_subst[OF E_grounding]
          unfolding \<gamma>
          by simp
      next
        show "is_maximal (l\<^sub>1 \<cdot>l \<rho>\<^sub>1 \<odot> \<mu> \<cdot>l \<sigma>) (select E \<cdot> \<rho>\<^sub>1 \<odot> \<mu> \<cdot> \<sigma>)"
          using \<gamma> ground_superpositionI(5,9) l\<^sub>1_\<gamma> that select_from_E Neg
          by fastforce
      qed
    next

      show "select D = {#}"
        using ground_superpositionI(10) select_from_D
        by simp
    next

      show "is_strictly_maximal (l\<^sub>2 \<cdot>l \<rho>\<^sub>2 \<odot> \<mu>) (D \<cdot> \<rho>\<^sub>2 \<odot> \<mu>)"
      proof(rule is_strictly_maximal_if_grounding_is_strictly_maximal)

        show "l\<^sub>2 \<cdot>l \<rho>\<^sub>2 \<odot> \<mu> \<in># D \<cdot> \<rho>\<^sub>2 \<odot> \<mu>"
          using l\<^sub>2_in_D
          by blast
      next

        show "clause.is_ground (D \<cdot> \<rho>\<^sub>2 \<odot> \<mu> \<cdot> \<sigma>)"
          using D_grounding
          unfolding \<gamma>
          by simp
      next

        show "is_strictly_maximal (l\<^sub>2 \<cdot>l \<rho>\<^sub>2 \<odot> \<mu> \<cdot>l \<sigma>) (D \<cdot> \<rho>\<^sub>2 \<odot> \<mu> \<cdot> \<sigma>)"
          using l\<^sub>2_\<gamma> \<gamma> D_\<gamma> ground_superpositionI(6,11)
          by auto
      qed
    next

      show "\<not> c\<^sub>1\<langle>t\<^sub>1\<rangle> \<cdot>t \<rho>\<^sub>1 \<odot> \<mu> \<preceq>\<^sub>t t\<^sub>1' \<cdot>t \<rho>\<^sub>1 \<odot> \<mu>"
      proof(rule term.order.ground_less_not_less_eq)

        show "term.is_ground (t\<^sub>1' \<cdot>t \<rho>\<^sub>1 \<odot> \<mu> \<cdot>t \<sigma>)"
          using t\<^sub>1'_\<gamma> \<gamma>
          by simp
      next

        show "term.is_ground (c\<^sub>1\<langle>t\<^sub>1\<rangle> \<cdot>t \<rho>\<^sub>1 \<odot> \<mu> \<cdot>t \<sigma>)"
          using t\<^sub>1_\<gamma> c\<^sub>1_\<gamma> \<gamma>
          by simp
      next

        show "t\<^sub>1' \<cdot>t \<rho>\<^sub>1 \<odot> \<mu> \<cdot>t \<sigma> \<prec>\<^sub>t c\<^sub>1\<langle>t\<^sub>1\<rangle> \<cdot>t \<rho>\<^sub>1 \<odot> \<mu> \<cdot>t \<sigma>"
          using ground_superpositionI(7) c\<^sub>1_\<gamma> t\<^sub>1'_\<gamma> t\<^sub>1_\<gamma>
          unfolding term.order.less\<^sub>G_def \<gamma>
          by auto
      qed
    next

      show "\<not> t\<^sub>2 \<cdot>t \<rho>\<^sub>2 \<odot> \<mu> \<preceq>\<^sub>t t\<^sub>2' \<cdot>t \<rho>\<^sub>2 \<odot> \<mu>"
      proof(rule term.order.ground_less_not_less_eq)

        show "term.is_ground (t\<^sub>2' \<cdot>t \<rho>\<^sub>2 \<odot> \<mu> \<cdot>t \<sigma>)"
          using t\<^sub>2'_\<gamma> \<gamma>
          by simp
      next

        show "term.is_ground (t\<^sub>2 \<cdot>t \<rho>\<^sub>2 \<odot> \<mu> \<cdot>t \<sigma>)"
          using t\<^sub>2_\<gamma> \<gamma>
          by simp
      next

        show "t\<^sub>2' \<cdot>t \<rho>\<^sub>2 \<odot> \<mu> \<cdot>t \<sigma> \<prec>\<^sub>t t\<^sub>2 \<cdot>t \<rho>\<^sub>2 \<odot> \<mu> \<cdot>t \<sigma>"
          using ground_superpositionI(8) t\<^sub>2_\<gamma> t\<^sub>2'_\<gamma>
          unfolding \<gamma> term.order.less\<^sub>G_def
          by simp
      qed
    next

      show "\<And>\<tau>. \<V>\<^sub>2 \<turnstile> t\<^sub>2 : \<tau> \<longleftrightarrow> \<V>\<^sub>2 \<turnstile> t\<^sub>2' : \<tau>"
        using type_preserving_literals_D
        unfolding D l\<^sub>2
        by auto
    qed

    show C'_\<gamma>: "C' \<cdot> \<gamma> = C \<cdot> \<gamma>"
    proof-

      have "term.is_idem \<mu>"
        using imgu term.is_imgu_iff_is_idem_and_is_mgu
        by blast

      then have \<mu>_\<gamma>: "\<mu> \<odot> \<gamma> = \<gamma>"
        unfolding \<gamma> term.is_idem_def
        by (metis term.assoc)

      have "C \<cdot> \<gamma> =
              add_mset
                (?\<P> (Upair (context.from_ground c\<^sub>G)\<langle>term.from_ground t\<^sub>G\<^sub>3\<rangle> (term.from_ground t\<^sub>G\<^sub>2)))
                  (clause.from_ground E\<^sub>G' + clause.from_ground D\<^sub>G')"
        using ground_superpositionI(4, 12) clause.to_ground_inverse[OF C_grounding]
        by auto

      then show ?thesis
        unfolding
          C'
          E'_\<gamma>[symmetric]
          D'_\<gamma>[symmetric]
          t\<^sub>1'_\<gamma>[symmetric]
          t\<^sub>2'_\<gamma>[symmetric]
          c\<^sub>1_\<gamma>[symmetric]
          clause.subst_comp_subst[symmetric]
          \<mu>_\<gamma>
        by simp
    qed

    show "\<iota>\<^sub>G \<in> inference_ground_instances (Infer [(\<V>\<^sub>2, D), (\<V>\<^sub>1, E)] (\<V>\<^sub>3, C'))"
    proof (rule is_inference_ground_instance_two_premises)

      show "is_inference_ground_instance_two_premises (\<V>\<^sub>2, D) (\<V>\<^sub>1, E) (\<V>\<^sub>3, C') \<iota>\<^sub>G \<gamma> \<rho>\<^sub>1 \<rho>\<^sub>2"
      proof(unfold split, intro conjI;
            (rule \<rho>\<^sub>1 \<rho>\<^sub>2 rename_apart type_preserving_literals_D type_preserving_literals_E refl \<V>\<^sub>1 
              \<V>\<^sub>2 \<V>\<^sub>3)?)

        show "inference.is_ground (Infer [D \<cdot> \<rho>\<^sub>2, E \<cdot> \<rho>\<^sub>1] C' \<cdot>\<iota> \<gamma>)"
          using D_grounding E_grounding C_grounding C'_\<gamma>
          by auto
      next

        show "\<iota>\<^sub>G = inference.to_ground (Infer [D \<cdot> \<rho>\<^sub>2, E \<cdot> \<rho>\<^sub>1] C' \<cdot>\<iota> \<gamma>)"
          using C'_\<gamma>
          by simp
      next

        show "type_preserving_on (clause.vars C') \<V>\<^sub>3 \<gamma>"
        proof(rule type_preserving_on_subset[OF type_preserving_\<gamma>])

          show "clause.vars C' \<subseteq> clause.vars (E \<cdot> \<rho>\<^sub>1) \<union> clause.vars (D \<cdot> \<rho>\<^sub>2)"
          proof (unfold subset_eq, intro ballI)
            fix x

            have is_imgu: "term.is_imgu \<mu> {{t\<^sub>1 \<cdot>t \<rho>\<^sub>1, t\<^sub>2 \<cdot>t \<rho>\<^sub>2}}"
              using imgu
              by blast

            assume "x \<in> clause.vars C'"

            then consider
              (t\<^sub>2') "x \<in> term.vars (t\<^sub>2' \<cdot>t \<rho>\<^sub>2 \<odot> \<mu>)" |
              (c\<^sub>1) "x \<in> context.vars (c\<^sub>1 \<cdot>t\<^sub>c \<rho>\<^sub>1 \<odot> \<mu>)" |
              (t\<^sub>1') "x \<in> term.vars (t\<^sub>1' \<cdot>t \<rho>\<^sub>1 \<odot> \<mu>)" |
              (E') "x \<in> clause.vars (E' \<cdot> \<rho>\<^sub>1 \<odot> \<mu>)" |
              (D') "x \<in> clause.vars (D' \<cdot> \<rho>\<^sub>2 \<odot> \<mu>)"
              unfolding C'
              by auto

            then show "x \<in> clause.vars (E \<cdot> \<rho>\<^sub>1) \<union> clause.vars (D \<cdot> \<rho>\<^sub>2)"
            proof cases
              case t\<^sub>2'

              then show ?thesis
                using term.variables_in_base_imgu[OF is_imgu]
                unfolding E l\<^sub>1 D l\<^sub>2
                by auto
            next
              case c\<^sub>1

              then show ?thesis
                using context.variables_in_base_imgu[OF is_imgu]
                unfolding E l\<^sub>1 D l\<^sub>2
                by force
            next
              case t\<^sub>1'

              then show ?thesis
                using term.variables_in_base_imgu[OF is_imgu]
                unfolding E clause.add_subst l\<^sub>1 D l\<^sub>2
                by auto
            next
              case E'

              then show ?thesis
                using clause.variables_in_base_imgu[OF is_imgu]
                unfolding E l\<^sub>1 D l\<^sub>2
                by auto
            next
              case D'

              then show ?thesis
                using clause.variables_in_base_imgu[OF is_imgu]
                unfolding E l\<^sub>1 D l\<^sub>2
                by auto
            qed
          qed
        qed
      next
        
        show "type_preserving_literals \<V>\<^sub>3 C'"
          using 
            type_preserving_literals_D
            type_preserving_literals_E
            superposition_type_preserving_literals[OF superposition]
          by satx
      qed

      show "\<iota>\<^sub>G \<in> ground.G_Inf"
        unfolding ground.G_Inf_def
        using ground_superposition
        by simp
    qed
  qed
qed

subsection \<open>Ground instances\<close>

context
  fixes \<iota>\<^sub>G N
  assumes
    subst_stability: "subst_stability_on N" and
    \<iota>\<^sub>G_Inf_from: "\<iota>\<^sub>G \<in> ground.Inf_from_q select\<^sub>G (\<Union>(uncurried_ground_instances ` N))"
begin

lemma single_premise_ground_instance:
  assumes
    ground_inference: "\<iota>\<^sub>G \<in> {Infer [D] C | D C. ground_inference D C}" and
    lifting: "\<And>D \<gamma> C \<V> thesis. \<lbrakk>
    ground_inference (clause.to_ground (D \<cdot> \<gamma>)) (clause.to_ground (C \<cdot> \<gamma>));
    clause.is_ground (D \<cdot> \<gamma>);
    clause.is_ground (C \<cdot> \<gamma>);
    clause.from_ground (select\<^sub>G (clause.to_ground (D \<cdot> \<gamma>))) = select D \<cdot> \<gamma>;
    type_preserving_literals \<V> D;
    type_preserving_on (clause.vars D) \<V> \<gamma>;
    infinite_variables_per_type \<V>;
    \<And>C'. \<lbrakk>
        inference (\<V>, D) (\<V>, C');
        Infer [clause.to_ground (D \<cdot> \<gamma>)] (clause.to_ground (C \<cdot> \<gamma>))
        \<in> inference_ground_instances (Infer [(\<V>, D)] (\<V>, C'));
        C' \<cdot> \<gamma> = C \<cdot> \<gamma>\<rbrakk> \<Longrightarrow> thesis\<rbrakk>
       \<Longrightarrow> thesis" and
    inference_eq: "inference = eq_factoring \<or> inference = eq_resolution"
  obtains \<iota> where
    "\<iota> \<in> Inf_from N"
    "\<iota>\<^sub>G \<in> inference_ground_instances \<iota>"
proof-
  obtain D\<^sub>G C\<^sub>G where
    \<iota>\<^sub>G: "\<iota>\<^sub>G = Infer [D\<^sub>G] C\<^sub>G" and
    ground_inference: "ground_inference D\<^sub>G C\<^sub>G"
    using ground_inference
    by blast

  have D\<^sub>G_in_groundings: "D\<^sub>G \<in> \<Union>(uncurried_ground_instances ` N)"
    using \<iota>\<^sub>G_Inf_from
    unfolding \<iota>\<^sub>G ground.Inf_from_q_def ground.Inf_from_def
    by simp

  obtain D \<gamma> \<V> where
    D_grounding: "clause.is_ground (D \<cdot> \<gamma>)" and
    type_preserving_literals: "type_preserving_literals \<V> D" and
    type_preserving_\<gamma>: "type_preserving_on (clause.vars D) \<V> \<gamma>" and
    \<V>: "infinite_variables_per_type \<V>" and
    D_in_N: "(\<V>, D) \<in> N" and
    "select\<^sub>G D\<^sub>G = clause.to_ground (select D \<cdot> \<gamma>)"
    "D \<cdot> \<gamma> = clause.from_ground D\<^sub>G"
    using subst_stability[rule_format, OF D\<^sub>G_in_groundings]
    by blast

  then have
    D\<^sub>G: "D\<^sub>G = clause.to_ground (D \<cdot> \<gamma>)" and
    select: "clause.from_ground (select\<^sub>G D\<^sub>G) = select D \<cdot> \<gamma>"
    by (simp_all add: select_ground_subst)

  obtain C where
    C\<^sub>G: "C\<^sub>G = clause.to_ground (C \<cdot> \<gamma>)" and
    C_grounding: "clause.is_ground (C \<cdot> \<gamma>)"
    by (metis clause.all_subst_ident_iff_ground clause.from_ground_inverse
        clause.ground_is_ground)

  obtain C' where
    inference: "inference (\<V>, D) (\<V>, C')" and
    inference_ground_instances: "\<iota>\<^sub>G \<in> inference_ground_instances (Infer [(\<V>, D)] (\<V>, C'))" and
    C'_C: "C' \<cdot> \<gamma> = C \<cdot> \<gamma>"
    using
      lifting[OF
        ground_inference[unfolded D\<^sub>G C\<^sub>G]
        D_grounding
        C_grounding
        select[unfolded D\<^sub>G]
        type_preserving_literals
        type_preserving_\<gamma>
        \<V>]
    unfolding D\<^sub>G C\<^sub>G \<iota>\<^sub>G.

  let ?\<iota> = "Infer [(\<V>, D)] (\<V>, C')"

  show ?thesis
  proof(rule that[OF _ inference_ground_instances])

    show "?\<iota> \<in> Inf_from N"
      using D_in_N inference inference_eq
      unfolding Inf_from_def inferences_def inference_system.Inf_from_def
      by auto
  qed
qed

lemma eq_resolution_ground_instance:
  assumes ground_eq_resolution: "\<iota>\<^sub>G \<in> ground.eq_resolution_inferences"
  obtains \<iota> where
    "\<iota> \<in> Inf_from N"
    "\<iota>\<^sub>G \<in> inference_ground_instances \<iota>"
  using eq_resolution_lifting single_premise_ground_instance[OF ground_eq_resolution]
  by blast

lemma eq_factoring_ground_instance:
  assumes ground_eq_factoring: "\<iota>\<^sub>G \<in> ground.eq_factoring_inferences"
  obtains \<iota> where
    "\<iota> \<in> Inf_from N"
    "\<iota>\<^sub>G \<in> inference_ground_instances \<iota>"
  using eq_factoring_lifting single_premise_ground_instance[OF ground_eq_factoring]
  by blast

lemma superposition_ground_instance:
  assumes
    ground_superposition: "\<iota>\<^sub>G \<in> ground.superposition_inferences" and
    not_redundant: "\<iota>\<^sub>G \<notin> ground.GRed_I (\<Union> (uncurried_ground_instances ` N))"
  obtains \<iota> where
    "\<iota> \<in> Inf_from N"
    "\<iota>\<^sub>G \<in> inference_ground_instances \<iota>"
proof-
  obtain E\<^sub>G D\<^sub>G C\<^sub>G where
    \<iota>\<^sub>G : "\<iota>\<^sub>G = Infer [D\<^sub>G, E\<^sub>G] C\<^sub>G" and
    ground_superposition: "ground.superposition D\<^sub>G E\<^sub>G C\<^sub>G"
    using assms(1)
    by blast

  have
    E\<^sub>G_in_ground_instances: "E\<^sub>G \<in> \<Union> (uncurried_ground_instances ` N)" and
    D\<^sub>G_in_ground_instances: "D\<^sub>G \<in> \<Union> (uncurried_ground_instances ` N)"
    using \<iota>\<^sub>G_Inf_from
    unfolding \<iota>\<^sub>G ground.Inf_from_q_def ground.Inf_from_def
    by simp_all

  obtain E \<V>\<^sub>1 \<gamma>\<^sub>1 where
    E_grounding: "clause.is_ground (E \<cdot> \<gamma>\<^sub>1)" and
    type_preserving_literals_E: "type_preserving_literals \<V>\<^sub>1 E" and
    type_preserving_\<gamma>\<^sub>1: "type_preserving_on (clause.vars E) \<V>\<^sub>1 \<gamma>\<^sub>1" and
    \<V>\<^sub>1: "infinite_variables_per_type \<V>\<^sub>1" and
    E_in_N: "(\<V>\<^sub>1, E)\<in>N" and
    "select\<^sub>G E\<^sub>G = clause.to_ground (select E \<cdot> \<gamma>\<^sub>1)"
    "E \<cdot> \<gamma>\<^sub>1 = clause.from_ground E\<^sub>G"
    using subst_stability[rule_format, OF E\<^sub>G_in_ground_instances]
    by blast

  then have
    E\<^sub>G: "E\<^sub>G = clause.to_ground (E \<cdot> \<gamma>\<^sub>1)" and
    select_from_E: "clause.from_ground (select\<^sub>G E\<^sub>G) = select E \<cdot> \<gamma>\<^sub>1"
    by (simp_all add: select_ground_subst)

  obtain D \<V>\<^sub>2 \<gamma>\<^sub>2 where
    D_grounding: "clause.is_ground (D \<cdot> \<gamma>\<^sub>2)" and
    type_preserving_literals_D: "type_preserving_literals \<V>\<^sub>2 D" and
    type_preserving_\<gamma>\<^sub>2: "type_preserving_on (clause.vars D) \<V>\<^sub>2 \<gamma>\<^sub>2" and
    \<V>\<^sub>2: "infinite_variables_per_type \<V>\<^sub>2" and
    D_in_N: "(\<V>\<^sub>2, D) \<in> N" and
    "select\<^sub>G D\<^sub>G = clause.to_ground (select D \<cdot> \<gamma>\<^sub>2)"
    "D \<cdot> \<gamma>\<^sub>2 = clause.from_ground D\<^sub>G"
    using subst_stability[rule_format, OF D\<^sub>G_in_ground_instances]
    by blast

  then have
    D\<^sub>G: "D\<^sub>G = clause.to_ground (D \<cdot> \<gamma>\<^sub>2)" and
    select_from_D: "clause.from_ground (select\<^sub>G D\<^sub>G) = select D \<cdot> \<gamma>\<^sub>2"
    by (simp_all add: select_ground_subst)

  obtain \<rho>\<^sub>1 \<rho>\<^sub>2 \<gamma> :: "'v \<Rightarrow> 't" where
    \<rho>\<^sub>1: "term.is_renaming \<rho>\<^sub>1" and
    \<rho>\<^sub>2: "term.is_renaming \<rho>\<^sub>2" and
    rename_apart: "clause.vars (E \<cdot> \<rho>\<^sub>1) \<inter> clause.vars (D \<cdot> \<rho>\<^sub>2) = {}" and
    type_preserving_\<rho>\<^sub>1: "type_preserving_on (clause.vars E) \<V>\<^sub>1 \<rho>\<^sub>1" and
    type_preserving_\<rho>\<^sub>2: "type_preserving_on (clause.vars D) \<V>\<^sub>2 \<rho>\<^sub>2" and
    \<gamma>\<^sub>1_\<gamma>: "\<forall>x \<in> clause.vars E. \<gamma>\<^sub>1 x = (\<rho>\<^sub>1 \<odot> \<gamma>) x" and
    \<gamma>\<^sub>2_\<gamma>: "\<forall>x \<in> clause.vars D. \<gamma>\<^sub>2 x = (\<rho>\<^sub>2 \<odot> \<gamma>) x"
    using clause.obtain_merged_grounding[OF
            type_preserving_\<gamma>\<^sub>1 type_preserving_\<gamma>\<^sub>2 E_grounding D_grounding \<V>\<^sub>2 clause.finite_vars].

  have E_grounding: "clause.is_ground (E \<cdot> \<rho>\<^sub>1 \<odot> \<gamma>)"
    using clause.subst_eq \<gamma>\<^sub>1_\<gamma> E_grounding
    by fastforce

  have E\<^sub>G: "E\<^sub>G = clause.to_ground (E \<cdot> \<rho>\<^sub>1 \<odot> \<gamma>)"
    using clause.subst_eq \<gamma>\<^sub>1_\<gamma> E\<^sub>G
    by fastforce

  have D_grounding: "clause.is_ground (D \<cdot> \<rho>\<^sub>2 \<odot> \<gamma>)"
    using clause.subst_eq \<gamma>\<^sub>2_\<gamma> D_grounding
    by fastforce

  have D\<^sub>G: "D\<^sub>G = clause.to_ground (D \<cdot> \<rho>\<^sub>2 \<odot> \<gamma>)"
    using clause.subst_eq \<gamma>\<^sub>2_\<gamma> D\<^sub>G
    by fastforce

  have type_preserving_\<rho>\<^sub>1_\<gamma>: "type_preserving_on (clause.vars E) \<V>\<^sub>1 (\<rho>\<^sub>1 \<odot> \<gamma>)"
    using type_preserving_\<gamma>\<^sub>1 \<gamma>\<^sub>1_\<gamma>
    by fastforce

  have type_preserving_\<rho>\<^sub>2_\<gamma>: "type_preserving_on (clause.vars D) \<V>\<^sub>2 (\<rho>\<^sub>2 \<odot> \<gamma>)"
    using type_preserving_\<gamma>\<^sub>2 \<gamma>\<^sub>2_\<gamma>
    by fastforce

  have select_from_E:
    "clause.from_ground (select\<^sub>G (clause.to_ground (E \<cdot> \<rho>\<^sub>1 \<odot> \<gamma>))) = select E \<cdot> \<rho>\<^sub>1 \<odot> \<gamma>"
  proof-
    have "E \<cdot> \<gamma>\<^sub>1 = E \<cdot> \<rho>\<^sub>1 \<odot> \<gamma>"
      using \<gamma>\<^sub>1_\<gamma> clause.subst_eq
      by fast

    moreover have "select E \<cdot> \<gamma>\<^sub>1 = select E \<cdot> \<rho>\<^sub>1 \<cdot> \<gamma>"
      using clause.subst_eq \<gamma>\<^sub>1_\<gamma> select_vars_subset
      by (smt (verit, best) clause.comp_subst.left.monoid_action_compatibility subsetD)

    ultimately show ?thesis
      using select_from_E
      unfolding E\<^sub>G
      by simp
  qed

  have select_from_D:
    "clause.from_ground (select\<^sub>G (clause.to_ground (D \<cdot> \<rho>\<^sub>2 \<odot> \<gamma>))) = select D \<cdot> \<rho>\<^sub>2 \<odot> \<gamma>"
  proof-
    have "D \<cdot> \<gamma>\<^sub>2 = D \<cdot> \<rho>\<^sub>2 \<odot> \<gamma>"
      using \<gamma>\<^sub>2_\<gamma> clause.subst_eq
      by fast

    moreover have "select D \<cdot> \<gamma>\<^sub>2 = select D \<cdot> \<rho>\<^sub>2 \<cdot> \<gamma>"
      using clause.subst_eq \<gamma>\<^sub>2_\<gamma> select_vars_subset[of D]
      by (smt (verit, best) clause.comp_subst.left.monoid_action_compatibility subsetD)

    ultimately show ?thesis
      using select_from_D
      unfolding D\<^sub>G
      by simp
  qed

  obtain C where
    C_grounding: "clause.is_ground (C \<cdot> \<gamma>)" and
    C\<^sub>G: "C\<^sub>G = clause.to_ground (C \<cdot> \<gamma>)"
    by (metis clause.all_subst_ident_if_ground clause.from_ground_inverse clause.ground_is_ground)

  have "ground_instances \<V>\<^sub>1 E \<union> ground_instances \<V>\<^sub>2 D \<subseteq> \<Union> (uncurried_ground_instances ` N)"
    using E_in_N D_in_N
    by force

  then have \<iota>\<^sub>G_not_redundant: "\<iota>\<^sub>G \<notin> ground.GRed_I (ground_instances \<V>\<^sub>1 E \<union> ground_instances \<V>\<^sub>2 D)"
    using not_redundant ground.Red_I_of_subset
    by blast

  obtain C' \<V>\<^sub>3 where
    superposition: "superposition (\<V>\<^sub>2, D) (\<V>\<^sub>1, E) (\<V>\<^sub>3, C')" and
    inference_groundings: "\<iota>\<^sub>G \<in> inference_ground_instances (Infer [(\<V>\<^sub>2, D), (\<V>\<^sub>1, E)] (\<V>\<^sub>3, C'))" and
    C'_\<gamma>_C_\<gamma>: "C' \<cdot> \<gamma> = C \<cdot> \<gamma>"
    using
      superposition_lifting[OF
        ground_superposition[unfolded D\<^sub>G E\<^sub>G C\<^sub>G]
        \<rho>\<^sub>1 \<rho>\<^sub>2
        rename_apart
        E_grounding D_grounding C_grounding
        select_from_E select_from_D
        type_preserving_literals_E type_preserving_literals_D
        type_preserving_\<rho>\<^sub>1_\<gamma> type_preserving_\<rho>\<^sub>2_\<gamma>
        type_preserving_\<rho>\<^sub>1 type_preserving_\<rho>\<^sub>2
        \<V>\<^sub>1 \<V>\<^sub>2
        \<iota>\<^sub>G_not_redundant[unfolded \<iota>\<^sub>G D\<^sub>G E\<^sub>G C\<^sub>G]]
    unfolding \<iota>\<^sub>G C\<^sub>G E\<^sub>G D\<^sub>G .

  let ?\<iota> = "Infer [(\<V>\<^sub>2, D), (\<V>\<^sub>1, E)] (\<V>\<^sub>3, C')"

  show ?thesis
  proof(rule that[OF _ inference_groundings])

    show "?\<iota> \<in> Inf_from N"
      using E_in_N D_in_N superposition
      unfolding Inf_from_def inferences_def inference_system.Inf_from_def
      by auto
  qed
qed

lemma ground_instances:
  assumes not_redundant: "\<iota>\<^sub>G \<notin> ground.Red_I (\<Union> (uncurried_ground_instances ` N))"
  obtains \<iota> where
    "\<iota> \<in> Inf_from N"
    "\<iota>\<^sub>G \<in> inference_ground_instances \<iota>"
proof-
  consider
    (superposition) "\<iota>\<^sub>G \<in> ground.superposition_inferences" |
    (eq_resolution) "\<iota>\<^sub>G \<in> ground.eq_resolution_inferences" |
    (eq_factoring) "\<iota>\<^sub>G \<in> ground.eq_factoring_inferences"
    using \<iota>\<^sub>G_Inf_from
    unfolding
      ground.Inf_from_q_def
      ground.G_Inf_def
      inference_system.Inf_from_def
    by fastforce

  then show ?thesis
  proof cases
    case superposition

    then show ?thesis
      using that superposition_ground_instance not_redundant
      by blast
  next
    case eq_resolution

    then show ?thesis
      using that eq_resolution_ground_instance
      by blast
  next
    case eq_factoring

    then show ?thesis
      using that eq_factoring_ground_instance
      by blast
  qed
qed

end

end

context superposition_calculus
begin

lemma overapproximation:
  obtains select\<^sub>G where
    "ground_Inf_overapproximated select\<^sub>G premises"
    "is_grounding select\<^sub>G"
proof-
  obtain select\<^sub>G where
    subst_stability: "select_subst_stability_on select select\<^sub>G premises" and
    "is_grounding select\<^sub>G"
    using obtain_subst_stable_on_select_grounding
    by blast

  then interpret grounded_superposition_calculus
    where select\<^sub>G = select\<^sub>G
    by unfold_locales

  show thesis
  proof(rule that[OF _ select\<^sub>G])

    show "ground_Inf_overapproximated select\<^sub>G premises"
      using ground_instances[OF subst_stability]
      by auto
  qed
qed

sublocale statically_complete_calculus "\<bottom>\<^sub>F" inferences entails_\<G> Red_I_\<G> Red_F_\<G>
proof (unfold static_empty_ord_inter_equiv_static_inter,
    rule stat_ref_comp_to_non_ground_fam_inter,
    rule ballI)
  fix select\<^sub>G
  assume "select\<^sub>G \<in> select\<^sub>G\<^sub>s"

  then interpret grounded_superposition_calculus
    where select\<^sub>G = select\<^sub>G
    by unfold_locales (simp add: select\<^sub>G\<^sub>s_def)

  show "statically_complete_calculus
          ground.G_Bot
          ground.G_Inf
          ground.G_entails
          ground.Red_I
          ground.Red_F"
    by unfold_locales
next

  show "\<And>N. \<exists>select\<^sub>G \<in> select\<^sub>G\<^sub>s. ground_Inf_overapproximated select\<^sub>G N"
    using overapproximation
    unfolding select\<^sub>G\<^sub>s_def
    by (smt (verit, best) mem_Collect_eq)
qed

end

end
