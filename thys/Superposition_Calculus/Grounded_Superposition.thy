theory Grounded_Superposition
  imports
    Superposition
    Ground_Superposition

    First_Order_Clause.Grounded_Selection_Function
    First_Order_Clause.Nonground_Inference
    Saturation_Framework.Lifting_to_Non_Ground_Calculi
begin

locale grounded_superposition_calculus =
  superposition_calculus where select = select and welltyped = welltyped +
  grounded_selection_function where
  select = select and atom_subst = "(\<cdot>a)" and atom_vars = atom.vars and 
  atom_to_ground = atom.to_ground and atom_from_ground = atom.from_ground and 
  is_ground_instance = is_ground_instance 
  for
    select :: "('f, 'v :: infinite) atom select" and
    welltyped :: "('v, 'ty) var_types \<Rightarrow> ('f, 'v) term \<Rightarrow> 'ty \<Rightarrow> bool"
begin

sublocale ground: ground_superposition_calculus where
  less\<^sub>t = "(\<prec>\<^sub>t\<^sub>G)" and select = select\<^sub>G
rewrites
  "multiset_extension.multiset_extension (\<prec>\<^sub>t\<^sub>G) ground.literal_to_mset = (\<prec>\<^sub>l\<^sub>G)" and
  "multiset_extension.multiset_extension (\<prec>\<^sub>l\<^sub>G) (\<lambda>x. x) = (\<prec>\<^sub>c\<^sub>G)" and
  "\<And>l\<^sub>G C\<^sub>G. ground.is_maximal l\<^sub>G C\<^sub>G \<longleftrightarrow> ground_is_maximal l\<^sub>G C\<^sub>G" and
  "\<And>l\<^sub>G C\<^sub>G. ground.is_strictly_maximal l\<^sub>G C\<^sub>G \<longleftrightarrow> ground_is_strictly_maximal l\<^sub>G C\<^sub>G"
  unfolding is_maximal_rewrite[symmetric] is_strictly_maximal_rewrite[symmetric]
  by unfold_locales simp_all

abbreviation is_inference_ground_instance_one_premise where
  "is_inference_ground_instance_one_premise D C \<iota>\<^sub>G \<gamma> \<equiv>
     case (D, C) of ((\<V>', D), (\<V>, C)) \<Rightarrow>
      inference.is_ground (Infer [D] C \<cdot>\<iota> \<gamma>) \<and>
      \<iota>\<^sub>G = inference.to_ground (Infer [D] C \<cdot>\<iota> \<gamma>) \<and>
      type_preserving_on (clause.vars C) \<V> \<gamma> \<and>
      type_preserving_literals \<V> D \<and>
      type_preserving_literals \<V> C \<and>
      \<V> = \<V>' \<and>
      infinite_variables_per_type \<V>"

abbreviation is_inference_ground_instance_two_premises where
  "is_inference_ground_instance_two_premises D E C \<iota>\<^sub>G \<gamma> \<rho>\<^sub>1 \<rho>\<^sub>2 \<equiv>
    case (D, E, C) of ((\<V>\<^sub>2, D), (\<V>\<^sub>1, E), (\<V>\<^sub>3, C)) \<Rightarrow>
      term_subst.is_renaming \<rho>\<^sub>1 \<and>
      term_subst.is_renaming \<rho>\<^sub>2 \<and>
      clause.vars (E \<cdot> \<rho>\<^sub>1) \<inter> clause.vars (D \<cdot> \<rho>\<^sub>2) = {} \<and>
      inference.is_ground (Infer [D \<cdot> \<rho>\<^sub>2, E \<cdot> \<rho>\<^sub>1] C \<cdot>\<iota> \<gamma>) \<and>
      \<iota>\<^sub>G = inference.to_ground (Infer [D \<cdot> \<rho>\<^sub>2, E \<cdot> \<rho>\<^sub>1] C \<cdot>\<iota> \<gamma>) \<and>
      type_preserving_on (clause.vars C) \<V>\<^sub>3 \<gamma> \<and>
      type_preserving_literals \<V>\<^sub>1 E \<and>
      type_preserving_literals \<V>\<^sub>2 D \<and>
      type_preserving_literals \<V>\<^sub>3 C \<and>
      infinite_variables_per_type \<V>\<^sub>1 \<and>
      infinite_variables_per_type \<V>\<^sub>2 \<and>
      infinite_variables_per_type \<V>\<^sub>3"

abbreviation is_inference_ground_instance where
  "is_inference_ground_instance \<iota> \<iota>\<^sub>G \<gamma> \<equiv>
  (case \<iota> of
      Infer [D] C \<Rightarrow> is_inference_ground_instance_one_premise D C \<iota>\<^sub>G \<gamma>
    | Infer [D, E] C \<Rightarrow> \<exists>\<rho>\<^sub>1 \<rho>\<^sub>2. is_inference_ground_instance_two_premises D E C \<iota>\<^sub>G \<gamma> \<rho>\<^sub>1 \<rho>\<^sub>2
    | _ \<Rightarrow> False)
  \<and> \<iota>\<^sub>G \<in> ground.G_Inf"

definition inference_ground_instances where
  "inference_ground_instances \<iota> = { \<iota>\<^sub>G | \<iota>\<^sub>G \<gamma>. is_inference_ground_instance \<iota> \<iota>\<^sub>G \<gamma> }"

lemma is_inference_ground_instance:
  "is_inference_ground_instance \<iota> \<iota>\<^sub>G \<gamma> \<Longrightarrow> \<iota>\<^sub>G \<in> inference_ground_instances \<iota>"
  unfolding inference_ground_instances_def
  by blast

lemma is_inference_ground_instance_one_premise:
  assumes "is_inference_ground_instance_one_premise D C \<iota>\<^sub>G \<gamma>" "\<iota>\<^sub>G \<in> ground.G_Inf"
  shows "\<iota>\<^sub>G \<in> inference_ground_instances (Infer [D] C)"
  using assms
  unfolding inference_ground_instances_def
  by auto

lemma is_inference_ground_instance_two_premises:
  assumes "is_inference_ground_instance_two_premises D E C \<iota>\<^sub>G \<gamma> \<rho>\<^sub>1 \<rho>\<^sub>2" "\<iota>\<^sub>G \<in> ground.G_Inf"
  shows "\<iota>\<^sub>G \<in> inference_ground_instances (Infer [D, E] C)"
  using assms
  unfolding inference_ground_instances_def
  by auto

lemma ground_inference\<^sub>_concl_in_ground_instances:
  assumes "\<iota>\<^sub>G \<in> inference_ground_instances \<iota>"
  shows "concl_of \<iota>\<^sub>G \<in> uncurried_ground_instances (concl_of \<iota>)"
proof -
  obtain "premises" C \<V> where
    \<iota>: "\<iota> = Infer premises (C, \<V>)"
    using Calculus.inference.exhaust
    by (metis prod.collapse)

  show ?thesis
    using assms
    unfolding \<iota> inference_ground_instances_def ground_instances_def
    by (cases "premises" rule: list_4_cases) auto
qed

lemma ground_inference_red_in_ground_instances_of_concl:
  assumes "\<iota>\<^sub>G \<in> inference_ground_instances \<iota>"
  shows "\<iota>\<^sub>G \<in> ground.Red_I (uncurried_ground_instances (concl_of \<iota>))"
proof -
  from assms have "\<iota>\<^sub>G \<in> ground.G_Inf"
    unfolding inference_ground_instances_def
    by blast

  moreover have "concl_of \<iota>\<^sub>G \<in> uncurried_ground_instances (concl_of \<iota>)"
    using assms ground_inference\<^sub>_concl_in_ground_instances
    by auto

  ultimately show "\<iota>\<^sub>G \<in> ground.Red_I (uncurried_ground_instances (concl_of \<iota>))"
    using ground.Red_I_of_Inf_to_N
    by blast
qed

sublocale lifting:
  tiebreaker_lifting
    "\<bottom>\<^sub>F"
    inferences
    ground.G_Bot
    ground.G_entails
    ground.G_Inf
    ground.GRed_I
    ground.GRed_F
    uncurried_ground_instances
    "Some \<circ> inference_ground_instances"
    typed_tiebreakers
proof (unfold_locales; (intro impI typed_tiebreakers.wfp typed_tiebreakers.transp)?)

  show "\<bottom>\<^sub>F \<noteq> {}"
    using obtain_infinite_variables_per_type_on''[of "{}"]
    by auto
next
  fix bottom
  assume "bottom \<in> \<bottom>\<^sub>F"

  then show "uncurried_ground_instances bottom \<noteq> {}"
    unfolding ground_instances_def
    by fastforce
next
  fix bottom
  assume "bottom \<in> \<bottom>\<^sub>F"

  then show "uncurried_ground_instances bottom \<subseteq> ground.G_Bot"
    unfolding ground_instances_def
    by auto
next
  fix C :: "('f, 'v, 'ty) typed_clause"

  assume "ground_instances (fst C) (snd C) \<inter> ground.G_Bot \<noteq> {}"

  moreover then have "snd C = {#}"
    unfolding ground_instances_def
    by simp

  then have "C = (fst C, {#})"
    by (metis split_pairs)

  ultimately show "C \<in> \<bottom>\<^sub>F"
    unfolding ground_instances_def
    by blast
next
  fix \<iota> :: "('f, 'v, 'ty) typed_clause inference"

  show
    "the ((Some \<circ> inference_ground_instances) \<iota>) \<subseteq> 
      ground.GRed_I (uncurried_ground_instances (concl_of \<iota>))"
    using ground_inference_red_in_ground_instances_of_concl
    by auto
qed

end

context superposition_calculus
begin

sublocale
  lifting_intersection
    inferences
    "{{#}}"
    select\<^sub>G\<^sub>s
    "ground_superposition_calculus.G_Inf (\<prec>\<^sub>t\<^sub>G)"
    "\<lambda>_. ground_superposition_calculus.G_entails"
    "ground_superposition_calculus.GRed_I (\<prec>\<^sub>t\<^sub>G)"
    "\<lambda>_. ground_superposition_calculus.GRed_F (\<prec>\<^sub>t\<^sub>G)"
    "\<bottom>\<^sub>F"
    "\<lambda>_. uncurried_ground_instances"
    "\<lambda>select\<^sub>G. Some \<circ>
      (grounded_superposition_calculus.inference_ground_instances (\<prec>\<^sub>t) select\<^sub>G welltyped)"
    typed_tiebreakers
proof (unfold_locales; (intro ballI)?)
  show "select\<^sub>G\<^sub>s \<noteq> {}"
    using select\<^sub>G_simple
    unfolding select\<^sub>G\<^sub>s_def
    by blast
next
  fix select\<^sub>G
  assume "select\<^sub>G \<in> select\<^sub>G\<^sub>s"

  then interpret grounded_superposition_calculus
    where select\<^sub>G = select\<^sub>G
    by unfold_locales (simp add: select\<^sub>G\<^sub>s_def)

  show "consequence_relation ground.G_Bot ground.G_entails"
    using ground.consequence_relation_axioms .

  show "tiebreaker_lifting
          \<bottom>\<^sub>F
          inferences
          ground.G_Bot
          ground.G_entails
          ground.G_Inf
          ground.GRed_I
          ground.GRed_F
          uncurried_ground_instances
          (Some \<circ> inference_ground_instances)
          typed_tiebreakers"
    by unfold_locales
qed

end

end
