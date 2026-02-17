theory Nonground_Context
  imports
    Generic_Context
    Nonground_Term
begin

section \<open>Nonground Contexts and Substitutions\<close>

locale ground_context = "context" where 
    hole = ground_hole and apply_context = apply_ground_context and
    compose_context = compose_ground_context 
  for ground_hole apply_ground_context compose_ground_context
begin

notation compose_ground_context (infixl \<open>\<circ>\<^sub>c\<^sub>G\<close> 75)
notation ground_hole (\<open>\<box>\<^sub>G\<close>)
notation apply_ground_context (\<open>_\<langle>_\<rangle>\<^sub>G\<close> [1000, 0] 1000)

end

locale nonground_context =
  (* TODO: We don't want a lifting here but list the needed properties + prove then for abstract context *)
  term_based_lifting where
  sub_vars = "term_vars :: 't \<Rightarrow> 'v set" and sub_subst = "term_subst :: 't \<Rightarrow> 'subst \<Rightarrow> 't" and
  sub_from_ground = term_from_ground and sub_to_ground = "term_to_ground :: 't \<Rightarrow> 't\<^sub>G" and
  sub_is_ground = term_is_ground and to_ground_map = to_ground_context_map and
  ground_map = ground_context_map and from_ground_map = from_ground_context_map and
  map = map_context and to_set = context_to_set and to_set_ground = ground_context_to_set +

  "context" +

  ground_context: ground_context where apply_ground_context = apply_ground_context
for
  map_context :: "('t \<Rightarrow> 't) \<Rightarrow> 'c \<Rightarrow> 'c" and
  to_ground_context_map :: "('t \<Rightarrow> 't\<^sub>G) \<Rightarrow> 'c \<Rightarrow> 'c\<^sub>G" and
  from_ground_context_map :: "('t\<^sub>G \<Rightarrow> 't) \<Rightarrow> 'c\<^sub>G \<Rightarrow> 'c" and
  ground_context_map :: "('t\<^sub>G \<Rightarrow> 't\<^sub>G) \<Rightarrow> 'c\<^sub>G \<Rightarrow> 'c\<^sub>G" and
  context_to_set ground_context_to_set and
  apply_ground_context :: "'c\<^sub>G \<Rightarrow> 't\<^sub>G \<Rightarrow> 't\<^sub>G" +
assumes
  hole_if_context_ident [simp]: "c\<langle>t\<rangle> = t \<Longrightarrow> c = \<box>" and
  term_to_ground_context_to_ground [simp]:
  "\<And>c t. term.to_ground c\<langle>t\<rangle> = (to_ground c)\<langle>term.to_ground t\<rangle>\<^sub>G" and
  term_from_ground_context_from_ground [simp]:
  "\<And>c\<^sub>G t\<^sub>G. term.from_ground c\<^sub>G\<langle>t\<^sub>G\<rangle>\<^sub>G = (from_ground c\<^sub>G)\<langle>term.from_ground t\<^sub>G\<rangle>" and
  apply_context_is_ground [simp]: "\<And>c t. term.is_ground c\<langle>t\<rangle> \<longleftrightarrow> is_ground c \<and> term.is_ground t" and
  map_compose [simp]: "\<And>f c c'. map_context f (c \<circ>\<^sub>c c') = map_context f c \<circ>\<^sub>c map_context f c'" and
  from_ground_compose [simp]:
    "\<And>c c'. from_ground (c \<circ>\<^sub>c\<^sub>G c') = from_ground c \<circ>\<^sub>c from_ground c'" and
  apply_context_vars [simp]: "\<And>c t. term.vars c\<langle>t\<rangle> = vars c \<union> term.vars t" and
  apply_context_subst [simp]: "\<And>c t \<sigma>. c\<langle>t\<rangle> \<cdot>t \<sigma> = (subst c \<sigma>)\<langle>t \<cdot>t \<sigma>\<rangle>" and
  context_Var: "\<And>x t. x \<in> term.vars t \<Longrightarrow> (\<exists>c. t = c\<langle>term.Var x\<rangle>)" and
 
  (* TODO: Simplify? + Separate? *)
  subst_to_context: "t \<cdot>t \<gamma> = c\<^sub>G\<langle>t\<^sub>G\<rangle> \<Longrightarrow> term.is_ground (t \<cdot>t \<gamma>) \<Longrightarrow>
    (\<exists>c t'. t = c\<langle>t'\<rangle> \<and> t' \<cdot>t \<gamma> = t\<^sub>G \<and> subst c \<gamma> = c\<^sub>G) \<or>
    (\<exists>c c\<^sub>G' x. t = c\<langle>term.Var x\<rangle> \<and> c\<^sub>G = (subst c \<gamma>) \<circ>\<^sub>c c\<^sub>G')"
begin

notation subst (infixl "\<cdot>t\<^sub>c" 67)

lemma term_from_ground_context_to_ground:
  assumes "is_ground c"
  shows "term.from_ground (to_ground c)\<langle>t\<^sub>G\<rangle>\<^sub>G = c\<langle>term.from_ground t\<^sub>G\<rangle>"
  unfolding to_ground_def
  by (metis assms term_from_ground_context_from_ground to_ground_def to_ground_inverse)

lemmas safe_unfolds =
  term_to_ground_context_to_ground
  term_from_ground_context_from_ground

lemma composed_context_is_ground [simp]: "is_ground (c \<circ>\<^sub>c c') \<longleftrightarrow> is_ground c \<and> is_ground c'"
  by (metis term.exists_ground apply_context_is_ground compose_context_iff)

lemma ground_context_ident_iff_hole [simp]: "c\<langle>t\<rangle>\<^sub>G = t \<longleftrightarrow> c = \<box>\<^sub>G"
  by (metis hole_if_context_ident from_ground_eq ground_context.apply_hole
      term_from_ground_context_from_ground)

lemma from_ground_hole [simp]: "from_ground c\<^sub>G = \<box> \<longleftrightarrow> c\<^sub>G = \<box>\<^sub>G"
  by (metis apply_hole apply_context_is_ground from_ground_inverse ground_context_ident_iff_hole 
      term.exists_ground term_to_ground_context_to_ground to_ground_inverse)

lemma hole_simps [simp]: "from_ground \<box>\<^sub>G = \<box>" "to_ground \<box> = \<box>\<^sub>G"
  using from_ground_inverse from_ground_hole
  by metis+

(* TODO: *)
lemma to_ground_compose [simp]: 
  assumes "is_ground c" "is_ground c'"
  shows "to_ground (c \<circ>\<^sub>c c') = to_ground c \<circ>\<^sub>c\<^sub>G to_ground c'"
  using from_ground_compose assms
  unfolding to_ground_def
  by (metis from_ground_inverse to_ground_def to_ground_inverse)

lemma hole_subst [simp]: "\<box> \<cdot>t\<^sub>c \<sigma> = \<box>"
  by (metis all_subst_ident_if_ground apply_hole apply_context_is_ground term.exists_ground)

lemma subst_into_Var:
  assumes 
    t_\<gamma>: "t \<cdot>t \<gamma> = c\<^sub>G\<langle>t\<^sub>G\<rangle>" and
    t_grounding: "term.is_ground (t \<cdot>t \<gamma>)" and
    not_subst_into_Fun: "\<nexists>c t'. t = c\<langle>t'\<rangle> \<and> t' \<cdot>t \<gamma> = t\<^sub>G \<and> c \<cdot>t\<^sub>c \<gamma> = c\<^sub>G \<and> \<not> term.is_Var t'"
shows "\<exists>c t' c\<^sub>G'. t = c\<langle>t'\<rangle> \<and> term.is_Var t' \<and> c\<^sub>G = (c \<cdot>t\<^sub>c \<gamma>) \<circ>\<^sub>c c\<^sub>G'"
proof (cases "\<exists>c t'. t = c\<langle>t'\<rangle> \<and> t' \<cdot>t \<gamma> = t\<^sub>G \<and> c \<cdot>t\<^sub>c \<gamma> = c\<^sub>G")
  case True

  then obtain c t' where 
    t: "t = c\<langle>t'\<rangle>" and
    c_\<gamma>: "c \<cdot>t\<^sub>c \<gamma> = c\<^sub>G" and
    "t' \<cdot>t \<gamma> = t\<^sub>G"
    by metis

  then obtain x where t': "t' = term.Var x" and exists_nonground: "term.exists_nonground"
    using not_subst_into_Fun 
    by presburger

  show ?thesis
  proof (intro exI conjI impI; (rule t t')?)

    show "c\<^sub>G = (c \<cdot>t\<^sub>c \<gamma>) \<circ>\<^sub>c \<box>"
      by (simp add: c_\<gamma>)
  next

    show "\<not> term.is_ground t'"
      using t' term.vars_id_subst[OF exists_nonground] term.no_vars_if_is_ground
      by auto
  qed
next
  case False

  then show ?thesis
    using subst_to_context[OF t_\<gamma> t_grounding]
    by (metis apply_context_is_ground subst_ident_if_ground t_\<gamma>
        term.all_subst_ident_if_ground)
qed

end

locale occurences =
  nonground_context where map_context = map_context and term_vars = term_vars
for
  map_context :: "('t \<Rightarrow> 't) \<Rightarrow> 'c \<Rightarrow> 'c" and term_vars :: "'t \<Rightarrow> 'v set" +
fixes occurences :: "'t \<Rightarrow> 'v \<Rightarrow> nat"
assumes
  occurences:
    "\<And>t\<^sub>G c x. term.exists_nonground \<Longrightarrow> term.is_ground t\<^sub>G \<Longrightarrow>
      occurences (c\<langle>term.Var x\<rangle>) x = Suc (occurences (c\<langle>t\<^sub>G\<rangle>) x)" and
  vars_occurences: "\<And>x t. x \<in> term.vars t \<longleftrightarrow> 0 < occurences t x"
begin

lemma is_ground_no_occurences: "term.is_ground t \<Longrightarrow> occurences t x = 0"
  using vars_occurences term.no_vars_if_is_ground 
  by auto

lemma occurences_obtain_context:
  assumes update: "term.is_ground t\<^sub>G" and occurences_in_t: "occurences t x = Suc n" 
  obtains c where 
    "t = c\<langle>term.Var x\<rangle>"
    "occurences c\<langle>t\<^sub>G\<rangle> x = n"
proof -

  obtain c where t: "t = c\<langle>term.Var x\<rangle>"
    using occurences_in_t context_Var vars_occurences zero_less_Suc 
    by presburger

  moreover have "occurences c\<langle>t\<^sub>G\<rangle> x = n"
    using assms is_ground_no_occurences occurences
    unfolding t
    by fastforce

  ultimately show ?thesis
    using that
    by metis
qed

lemma one_occurence_obtain_context:
  assumes "occurences t x = 1"
  obtains c where
    "t = c\<langle>term.Var x\<rangle>"
    "x \<notin> vars c"
  using term.exists_ground occurences_obtain_context[OF _ assms[unfolded One_nat_def]]
  by (metis Un_iff apply_context_vars order_less_irrefl vars_occurences)

end

locale nonground_term_with_context =
  "term": nonground_term +
  "context": nonground_context +
  occurences
begin

(* TODO: How to not have it multiple times?*)
notation context.subst (infixl "\<cdot>t\<^sub>c" 67)

end

end
