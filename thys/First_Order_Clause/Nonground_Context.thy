theory Nonground_Context
  imports
    Generic_Context
    Ground_Context
    Nonground_Term

    Abstract_Substitution.Functional_Substitution_Lifting
begin

section \<open>Nonground Contexts and Substitutions\<close>

locale nonground_context =
  "term": nonground_term where term_vars = term_vars and term_to_ground = term_to_ground +
  term_based_lifting where
  sub_subst = "(\<cdot>t)" and sub_vars = term.vars and sub_to_ground = term.to_ground and
  sub_from_ground = term.from_ground and term_vars = term.vars and term_subst = "(\<cdot>t)" and
  term_to_ground = term.to_ground and term_from_ground = term.from_ground and
  to_ground_map = to_ground_context_map and ground_map = map_args_actxt and 
  from_ground_map = from_ground_context_map and map = map_context and to_set = context_to_set and
  to_set_ground = set2_actxt +
  "context" where subst = subst
for
  term_vars :: "'t \<Rightarrow> 'v set" and 
  term_to_ground :: "'t \<Rightarrow> 'f gterm" and
  map_context :: "('t \<Rightarrow> 't) \<Rightarrow> 'c \<Rightarrow> 'c" and
  to_ground_context_map :: "('t \<Rightarrow> 'f gterm) \<Rightarrow> 'c \<Rightarrow> 'f ground_context" and
  from_ground_context_map :: "('f gterm \<Rightarrow> 't) \<Rightarrow> 'f ground_context \<Rightarrow> 'c" and
  context_to_set +
assumes 
  term_to_ground_context_to_ground [simp]:
  "\<And>c t. term.to_ground c\<langle>t\<rangle> = (to_ground c)\<langle>term.to_ground t\<rangle>\<^sub>G" and
  term_from_ground_context_from_ground [simp]:
  "\<And>c\<^sub>G t\<^sub>G. term.from_ground c\<^sub>G\<langle>t\<^sub>G\<rangle>\<^sub>G = (from_ground c\<^sub>G)\<langle>term.from_ground t\<^sub>G\<rangle>" and
  apply_context_is_ground [simp]: "\<And>c t. term.is_ground c\<langle>t\<rangle> \<longleftrightarrow> is_ground c \<and> term.is_ground t" and
  map_compose [simp]: "\<And>f c c'. map_context f (c \<circ>\<^sub>c c') = map_context f c \<circ>\<^sub>c map_context f c'" and
  from_ground_compose [simp]:
    "\<And>c c'. from_ground (actxt_compose c c') = from_ground c \<circ>\<^sub>c from_ground c'" and
  apply_context_vars [simp]: "\<And>c t. term.vars c\<langle>t\<rangle> = vars c \<union> term.vars t" and
  apply_context_subst [simp]: "\<And>c t \<sigma>. c\<langle>t\<rangle> \<cdot>t \<sigma> = (subst c \<sigma>)\<langle>t \<cdot>t \<sigma>\<rangle>" and
  context_Var: "\<And>x t. x \<in> term.vars t \<longleftrightarrow> (\<exists>c. t = c\<langle>Var x\<rangle>)" and
 
  (* TODO: Simplify? + Separate? *)
  subst_to_context: "t \<cdot>t \<gamma> = c\<^sub>G\<langle>t\<^sub>G\<rangle> \<Longrightarrow> term.is_ground (t \<cdot>t \<gamma>) \<Longrightarrow>
    (\<exists>c t'. t = c\<langle>t'\<rangle> \<and> t' \<cdot>t \<gamma> = t\<^sub>G \<and> subst c \<gamma> = c\<^sub>G) \<or>
    (\<exists>c c\<^sub>G' x. t = c\<langle>Var x\<rangle> \<and> c\<^sub>G = (subst c \<gamma>) \<circ>\<^sub>c c\<^sub>G')"
begin

(* TODO: How to not have it multiple times?*)
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
  by (metis term.ground_exists apply_context_is_ground compose_context_iff)

lemma from_ground_hole [simp]: "from_ground c\<^sub>G = \<box> \<longleftrightarrow> c\<^sub>G = \<box>\<^sub>G"
  by (metis apply_Hole apply_context_is_ground from_ground_inverse gctxt_ident_iff_eq_GHole 
      term.ground_exists term_to_ground_context_to_ground to_ground_inverse)

lemma hole_simps [simp]: "from_ground \<box>\<^sub>G = \<box>" "to_ground \<box> = \<box>\<^sub>G"
  using from_ground_inverse from_ground_hole
  by metis+

lemma to_ground_compose [simp]: "to_ground (c \<circ>\<^sub>c c') = actxt_compose (to_ground c) (to_ground c')"
  using from_ground_compose
  unfolding to_ground_def
  by (metis conversion_map_comp from_ground_def from_ground_inverse map_compose)

lemma Hole_subst [simp]: "\<box> \<cdot>t\<^sub>c \<sigma> = \<box>"
  by (metis all_subst_ident_if_ground apply_Hole apply_context_is_ground term.ground_exists)

lemma subst_into_Var:
  assumes 
    t_\<gamma>: "t \<cdot>t \<gamma> = c\<^sub>G\<langle>t\<^sub>G\<rangle>" and
    t_grounding: "term.is_ground (t \<cdot>t \<gamma>)" and
    not_subst_into_Fun: "\<nexists>c t'. t = c\<langle>t'\<rangle> \<and> t' \<cdot>t \<gamma> = t\<^sub>G \<and> c \<cdot>t\<^sub>c \<gamma> = c\<^sub>G \<and> \<not> term.is_Var t'"
shows "\<exists>c t' c\<^sub>G'. t = c\<langle>t'\<rangle> \<and> term.is_Var t' \<and> c\<^sub>G = (c \<cdot>t\<^sub>c \<gamma>) \<circ>\<^sub>c c\<^sub>G'"
proof (cases "\<exists>c t'. t = c\<langle>t'\<rangle> \<and> t' \<cdot>t \<gamma> = t\<^sub>G \<and> c \<cdot>t\<^sub>c \<gamma> = c\<^sub>G")
  case True

  then obtain c t' where t: "t = c\<langle>t'\<rangle>" and "t' \<cdot>t \<gamma> = t\<^sub>G" "c \<cdot>t\<^sub>c \<gamma> = c\<^sub>G"
    by metis

  have "is_ground c\<^sub>G"
    using t_\<gamma> t_grounding 
    by auto

  obtain x where t': "t' = Var x"
    using \<open>c \<cdot>t\<^sub>c \<gamma> = c\<^sub>G\<close> \<open>t' \<cdot>t \<gamma> = t\<^sub>G\<close> not_subst_into_Fun t
    by blast

  show ?thesis
  proof (intro exI conjI)
    show "t = c\<langle>t'\<rangle>"
      using t .
  next
    show "t' = Var x"
      using t' .
  next

    have "to_ground c\<^sub>G = actxt_compose (to_ground (c \<cdot>t\<^sub>c \<gamma>)) \<box>\<^sub>G"
      by (simp add: \<open>c \<cdot>t\<^sub>c \<gamma> = c\<^sub>G\<close>)

    then show "c\<^sub>G = (c \<cdot>t\<^sub>c \<gamma>) \<circ>\<^sub>c \<box>"
      by (metis \<open>c \<cdot>t\<^sub>c \<gamma> = c\<^sub>G\<close> \<open>vars c\<^sub>G = {}\<close> from_ground_compose hole_simps(1) to_ground_inverse)
  qed
next
  case False

  then show ?thesis
    using subst_to_context[OF t_\<gamma> t_grounding]
    by metis
qed

end

locale occurences =
  nonground_context where map_context = map_context and Var = Var
for 
  map_context :: "('t \<Rightarrow> 't) \<Rightarrow> 'c \<Rightarrow> 'c" and
  Var :: "'v \<Rightarrow> 't" +
fixes occurences :: "'t \<Rightarrow> 'v \<Rightarrow> nat"
assumes
  occurences:
  "\<And>t\<^sub>G c x. term.is_ground t\<^sub>G \<Longrightarrow> occurences (c\<langle>Var x\<rangle>) x = Suc (occurences (c\<langle>t\<^sub>G\<rangle>) x)" and
  vars_occurences: "x \<in> term.vars t \<longleftrightarrow> 0 < occurences t x"
begin

lemma is_ground_no_occurences: "term.is_ground t \<Longrightarrow> occurences t x = 0"
  using vars_occurences 
  by auto

lemma occurences_obtain_context:
  assumes update: "term.is_ground t\<^sub>G" and occurences_in_t: "occurences t x = Suc n" 
  obtains c where 
    "t = c\<langle>Var x\<rangle>"
    "occurences c\<langle>t\<^sub>G\<rangle> x = n"
proof -

  obtain c where t: "t = c\<langle>Var x\<rangle>"
    using occurences_in_t context_Var vars_occurences zero_less_Suc 
    by presburger

  moreover have "occurences c\<langle>t\<^sub>G\<rangle> x = n"
    using assms
    unfolding t occurences[OF update]
    by linarith

  ultimately show ?thesis
    using that
    by metis
qed

lemma one_occurence_obtain_context:
  assumes "occurences t x = 1"
  obtains c where
    "t = c\<langle>Var x\<rangle>"
    "x \<notin> vars c"
  using term.ground_exists occurences_obtain_context[OF _ assms[unfolded One_nat_def]]
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
