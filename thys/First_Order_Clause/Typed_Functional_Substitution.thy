theory Typed_Functional_Substitution
  imports
    Typing
    Abstract_Substitution.Functional_Substitution
    Infinite_Variables_Per_Type
    Collect_Extra
begin

type_synonym ('var, 'ty) var_types = "'var \<Rightarrow> 'ty"

locale explicitly_typed_functional_substitution =
  base_functional_substitution where vars = vars and id_subst = id_subst
for
  id_subst :: "'var \<Rightarrow> 'base" and
  vars :: "'base \<Rightarrow> 'var set" and
  typed :: "('var, 'ty) var_types \<Rightarrow> 'base \<Rightarrow> 'ty \<Rightarrow> bool" +
assumes
  predicate_typed: "\<And>\<V>. predicate_typed (typed \<V>)" and
  typed_id_subst [intro]: "\<And>\<V> x. typed \<V> (id_subst x) (\<V> x)"
begin

sublocale predicate_typed "typed \<V>"
  using predicate_typed .

abbreviation is_typed_on :: "'var set \<Rightarrow> ('var, 'ty) var_types \<Rightarrow> ('var \<Rightarrow> 'base) \<Rightarrow> bool" where
  "\<And>\<V>. is_typed_on X \<V> \<sigma> \<equiv> \<forall>x \<in> X. typed \<V> (\<sigma> x) (\<V> x)"

lemma subst_update:
  assumes "typed \<V> (id_subst var) \<tau>" "typed \<V> update \<tau>"  "is_typed_on X \<V> \<gamma>"
  shows "is_typed_on X \<V> (\<gamma>(var := update))"
  using assms typed_id_subst
  by fastforce

lemma is_typed_on_subset:
  assumes "is_typed_on Y \<V> \<sigma>" "X \<subseteq> Y"
  shows "is_typed_on X \<V> \<sigma>"
  using assms
  by blast

lemma is_typed_id_subst [intro]: "is_typed_on X \<V> id_subst"
  using typed_id_subst
  by auto

end

locale inhabited_explicitly_typed_functional_substitution =
 explicitly_typed_functional_substitution +
 assumes types_inhabited: "\<And>\<tau>. \<exists>b. is_ground b \<and> typed \<V> b \<tau>"

locale typed_functional_substitution =
  base: explicitly_typed_functional_substitution where
  vars = base_vars and subst = base_subst and typed = base_typed +
  based_functional_substitution where vars = vars
for
  vars :: "'expr \<Rightarrow> 'var set" and
  is_typed :: "('var, 'ty) var_types \<Rightarrow> 'expr \<Rightarrow> bool" and
  base_typed :: "('var, 'ty) var_types \<Rightarrow> 'base \<Rightarrow> 'ty \<Rightarrow> bool"
begin

(* TODO: Quite specific definition *)
abbreviation is_typed_ground_instance where
  "is_typed_ground_instance expr \<V> \<gamma> \<equiv>
    is_ground (expr \<cdot> \<gamma>) \<and>
    is_typed \<V> expr \<and>
    base.is_typed_on (vars expr) \<V> \<gamma> \<and>
    infinite_variables_per_type \<V>"

end

sublocale explicitly_typed_functional_substitution \<subseteq> typed_functional_substitution where
  base_subst = subst and base_vars = vars and is_typed = is_typed and
  base_typed = typed
  by unfold_locales

locale typed_grounding_functional_substitution =
  typed_functional_substitution + grounding
begin

definition typed_ground_instances where
  "typed_ground_instances typed_expr =
    { to_ground (fst typed_expr \<cdot> \<gamma>) | \<gamma>.
      is_typed_ground_instance (fst typed_expr) (snd typed_expr) \<gamma> }"

lemma typed_ground_instances_ground_instances':
  "typed_ground_instances (expr, \<V>) \<subseteq> ground_instances' expr"
  unfolding typed_ground_instances_def ground_instances'_def
  by auto

end

locale explicitly_typed_grounding_functional_substitution =
  explicitly_typed_functional_substitution + grounding
begin

sublocale typed_grounding_functional_substitution where
  base_subst = subst and base_vars = vars and is_typed = is_typed and
  base_typed = typed
  by unfold_locales

end

locale inhabited_typed_functional_substitution =
  typed_functional_substitution +
  base: inhabited_explicitly_typed_functional_substitution where
  subst = base_subst and vars = base_vars and typed = base_typed
begin

lemma ground_subst_extension:
  assumes
    grounding: "is_ground (expr \<cdot> \<gamma>)" and
    \<gamma>_is_typed_on: "base.is_typed_on (vars expr) \<V> \<gamma>"
  obtains \<gamma>'
  where
    "base.is_ground_subst \<gamma>'"
    "base.is_typed_on UNIV \<V> \<gamma>'"
    "\<forall>x \<in> vars expr. \<gamma> x = \<gamma>' x"
proof (rule that)

  define \<gamma>' where
    "\<And>x. \<gamma>' x \<equiv>
      if x \<in> vars expr
      then \<gamma> x
      else SOME base. base.is_ground base \<and> base_typed \<V> base (\<V> x)"

  show "base.is_ground_subst \<gamma>'"
  proof(unfold base.is_ground_subst_def, intro allI)
    fix b

    {
      fix x

      have "base.is_ground (\<gamma>' x)"
      proof(cases "x \<in> vars expr")
        case True
        then show ?thesis
          unfolding \<gamma>'_def
          using variable_grounding[OF grounding]
          by auto
      next
        case False
        then show ?thesis
          unfolding \<gamma>'_def
          by (smt (verit) base.types_inhabited tfl_some)
      qed
    }

    then show "base.is_ground (base_subst b \<gamma>')"
      using base.is_grounding_iff_vars_grounded
      by auto
  qed

  show "base.is_typed_on UNIV \<V> \<gamma>'"
    unfolding \<gamma>'_def
    using \<gamma>_is_typed_on base.types_inhabited
    by (simp add: verit_sko_ex_indirect)

  show "\<forall>x \<in> vars expr. \<gamma> x = \<gamma>' x"
    by (simp add: \<gamma>'_def)
qed

lemma grounding_extension:
  assumes
    grounding: "is_ground (expr \<cdot> \<gamma>)" and
    \<gamma>_is_typed_on: "base.is_typed_on (vars expr) \<V> \<gamma>"
  obtains \<gamma>'
  where
    "is_ground (expr' \<cdot> \<gamma>')"
    "base.is_typed_on (vars expr') \<V> \<gamma>'"
    "\<forall>x \<in> vars expr. \<gamma> x = \<gamma>' x"
  using ground_subst_extension[OF grounding \<gamma>_is_typed_on]
  unfolding base.is_ground_subst_def is_grounding_iff_vars_grounded
  by (metis UNIV_I base.comp_subst_iff base.left_neutral)

end

sublocale explicitly_typed_functional_substitution \<subseteq> typed_functional_substitution where
  base_subst = subst and base_vars = vars and is_typed = is_typed and
  base_typed = typed
  by unfold_locales

locale typed_subst_stability = typed_functional_substitution +
assumes
  subst_stability [simp]:
    "\<And>\<V> expr \<sigma>. base.is_typed_on (vars expr) \<V> \<sigma> \<Longrightarrow> is_typed \<V> (expr \<cdot> \<sigma>) \<longleftrightarrow> is_typed \<V> expr"
begin

lemma subst_stability_UNIV [simp]:
  "\<And>\<V> expr \<sigma>. base.is_typed_on UNIV \<V> \<sigma> \<Longrightarrow> is_typed \<V> (expr \<cdot> \<sigma>) \<longleftrightarrow> is_typed \<V> expr"
  by simp

end

locale explicitly_typed_subst_stability = explicitly_typed_functional_substitution +
assumes
  explicit_subst_stability [simp]:
    "\<And>\<V> expr \<sigma> \<tau>. is_typed_on (vars expr) \<V> \<sigma> \<Longrightarrow> typed \<V> (expr \<cdot> \<sigma>) \<tau> \<longleftrightarrow> typed \<V> expr \<tau>"
begin

lemma explicit_subst_stability_UNIV [simp]:
  "\<And>\<V> expr \<sigma>. is_typed_on UNIV \<V> \<sigma> \<Longrightarrow> typed \<V> (expr \<cdot> \<sigma>) \<tau> \<longleftrightarrow> typed \<V> expr \<tau>"
  by simp

sublocale typed_subst_stability where
  base_vars = vars and base_subst = subst and base_typed = typed and is_typed = is_typed
  using explicit_subst_stability
  by unfold_locales blast

lemma typed_subst_compose [intro]:
  assumes
    "is_typed_on X \<V> \<sigma>"
    "is_typed_on (\<Union>(vars ` \<sigma> ` X)) \<V> \<sigma>'"
  shows "is_typed_on X \<V> (\<sigma> \<odot> \<sigma>')"
  using assms
  unfolding comp_subst_iff
  by auto

lemma typed_subst_compose_UNIV [intro]:
  assumes
    "is_typed_on UNIV \<V> \<sigma>"
    "is_typed_on UNIV \<V> \<sigma>'"
  shows "is_typed_on UNIV \<V> (\<sigma> \<odot> \<sigma>')"
  using assms
  unfolding comp_subst_iff
  by auto

end

locale replaceable_\<V> = typed_functional_substitution +
  assumes replace_\<V>:
    "\<And>expr \<V> \<V>'. \<forall>x\<in> vars expr. \<V> x = \<V>' x \<Longrightarrow> is_typed \<V> expr \<Longrightarrow> is_typed \<V>' expr"
begin

lemma replace_\<V>_iff:
  assumes "\<forall>x\<in> vars expr. \<V> x = \<V>' x"
  shows "is_typed \<V> expr \<longleftrightarrow> is_typed \<V>' expr"
  using assms
  by (metis replace_\<V>)

lemma is_ground_typed:
  assumes "is_ground expr"
  shows "is_typed \<V> expr \<longleftrightarrow> is_typed \<V>' expr"
  using replace_\<V>_iff assms
  by blast

end

locale explicitly_replaceable_\<V> = explicitly_typed_functional_substitution +
  assumes explicit_replace_\<V>:
    "\<And>expr \<V> \<V>' \<tau>. \<forall>x\<in> vars expr. \<V> x = \<V>' x \<Longrightarrow> typed \<V> expr \<tau> \<Longrightarrow>  typed \<V>' expr \<tau>"
begin

lemma explicit_replace_\<V>_iff:
  assumes "\<forall>x\<in> vars expr. \<V> x = \<V>' x"
  shows "typed \<V> expr \<tau> \<longleftrightarrow> typed \<V>' expr \<tau>"
  using assms
  by (metis explicit_replace_\<V>)

lemma explicit_is_ground_typed:
  assumes "is_ground expr"
  shows "typed \<V> expr \<tau> \<longleftrightarrow> typed \<V>' expr \<tau>"
  using explicit_replace_\<V>_iff assms
  by blast

sublocale replaceable_\<V> where
  base_vars = vars and base_subst = subst and base_typed = typed and is_typed = is_typed
  using explicit_replace_\<V>
  by unfold_locales blast

end

locale typed_renaming = typed_functional_substitution + renaming_variables +
assumes
  typed_renaming [simp]:
    "\<And>\<V> \<V>' expr \<rho>. base.is_renaming \<rho> \<Longrightarrow>
      \<forall>x \<in> vars expr. \<V> x = \<V>' (rename \<rho> x) \<Longrightarrow>
      is_typed \<V>' (expr \<cdot> \<rho>) \<longleftrightarrow> is_typed \<V> expr"

locale explicitly_typed_renaming =
  explicitly_typed_functional_substitution where typed = typed +
  renaming_variables +
  explicitly_replaceable_\<V> where typed = typed
for typed :: "('var \<Rightarrow> 'ty) \<Rightarrow> 'expr \<Rightarrow> 'ty \<Rightarrow> bool" +
assumes
  explicit_typed_renaming [simp]:
  "\<And>\<V> \<V>' expr \<rho> \<tau>. is_renaming \<rho> \<Longrightarrow>
      \<forall>x \<in> vars expr. \<V> x = \<V>' (rename \<rho> x) \<Longrightarrow>
      typed \<V>' (expr \<cdot> \<rho>) \<tau> \<longleftrightarrow> typed \<V> expr \<tau>"
begin

sublocale typed_renaming
  where base_vars = vars and base_subst = subst and base_typed = typed and is_typed = is_typed
  using explicit_typed_renaming
  by unfold_locales blast

lemma renaming_ground_subst:
  assumes
    "is_renaming \<rho>"
    "is_typed_on (\<Union>(vars ` \<rho> ` X)) \<V>' \<gamma>"
    "is_typed_on X \<V> \<rho>"
    "is_ground_subst \<gamma>"
    "\<forall>x \<in> X. \<V> x = \<V>' (rename \<rho> x)"
  shows "is_typed_on X \<V> (\<rho> \<odot> \<gamma>)"
proof(intro ballI)
  fix x
  assume x_in_X: "x \<in> X"

  then have "typed \<V> (\<rho> x) (\<V> x)"
    by (simp add: assms(3))

  define y where "y \<equiv> (rename \<rho> x)"

  have "y \<in> \<Union>(vars ` \<rho> ` X)"
    using x_in_X
    unfolding y_def
    by (metis UN_iff assms(1) id_subst_rename image_eqI singletonI vars_id_subst)

  moreover then have "typed \<V> (\<gamma> y) (\<V>' y)"
    using explicit_replace_\<V>
    by (metis assms(2,4) left_neutral emptyE is_ground_subst_is_ground comp_subst_iff)

  ultimately have "typed \<V> (\<gamma> y) (\<V> x)"
    unfolding y_def
    using assms(5) x_in_X
    by fastforce

  moreover have "\<gamma> y = (\<rho> \<odot> \<gamma>) x"
    unfolding y_def
    by (metis assms(1) comp_subst_iff id_subst_rename left_neutral)

  ultimately show "typed \<V> ((\<rho> \<odot> \<gamma>) x) (\<V> x)"
    by argo
qed

lemma inj_id_subst: "inj id_subst"
  using is_renaming_id_subst is_renaming_iff
  by blast

lemma obtain_typed_renaming:
  fixes \<V> :: "'var \<Rightarrow> 'ty"
  assumes
    "finite X"
    "infinite_variables_per_type \<V>"
  obtains \<rho> :: "'var \<Rightarrow> 'expr" where
    "is_renaming \<rho>"
    "id_subst ` X \<inter> \<rho> ` Y = {}"
    "is_typed_on Y \<V> \<rho>"
proof-

  obtain renaming :: "'var \<Rightarrow> 'var" where
    inj: "inj renaming" and
    rename_apart: "X \<inter> renaming ` Y = {}" and
    preserve_type: "\<forall>x \<in> Y. \<V> (renaming x) = \<V> x"
    using obtain_type_preserving_inj[OF assms].

  define \<rho> :: "'var \<Rightarrow> 'expr" where
    "\<And>x. \<rho> x \<equiv> id_subst (renaming x)"

  show ?thesis
  proof (rule that)

    show "is_renaming \<rho>"
      using inj inj_id_subst
      unfolding \<rho>_def is_renaming_iff inj_def
      by blast
  next

    show "id_subst ` X \<inter> \<rho> ` Y = {}"
      using rename_apart inj_id_subst
      unfolding \<rho>_def inj_def
      by blast
  next

    show "is_typed_on Y \<V> \<rho>"
      using preserve_type
      unfolding \<rho>_def
      by (metis typed_id_subst)
  qed
qed

lemma obtain_typed_renamings:
  fixes \<V>\<^sub>1 \<V>\<^sub>2 :: "'var \<Rightarrow> 'ty"
  assumes
    "finite X"
    "infinite_variables_per_type \<V>\<^sub>2"
  obtains \<rho>\<^sub>1 \<rho>\<^sub>2 :: "'var \<Rightarrow> 'expr" where
    "is_renaming \<rho>\<^sub>1"
    "is_renaming \<rho>\<^sub>2"
    "\<rho>\<^sub>1 ` X \<inter> \<rho>\<^sub>2 ` Y = {}"
    "is_typed_on X \<V>\<^sub>1 \<rho>\<^sub>1"
    "is_typed_on Y \<V>\<^sub>2 \<rho>\<^sub>2"
  using obtain_typed_renaming[OF assms] is_renaming_id_subst typed_id_subst
  by metis

lemma obtain_typed_renamings':
  fixes \<V>\<^sub>1 \<V>\<^sub>2 :: "'var \<Rightarrow> 'ty"
  assumes
    "finite Y"
    "infinite_variables_per_type \<V>\<^sub>1"
  obtains \<rho>\<^sub>1 \<rho>\<^sub>2 :: "'var \<Rightarrow> 'expr" where
    "is_renaming \<rho>\<^sub>1"
    "is_renaming \<rho>\<^sub>2"
    "\<rho>\<^sub>1 ` X \<inter> \<rho>\<^sub>2 ` Y = {}"
    "is_typed_on X \<V>\<^sub>1 \<rho>\<^sub>1"
    "is_typed_on Y \<V>\<^sub>2 \<rho>\<^sub>2"
  using obtain_typed_renamings[OF assms]
  by (metis inf_commute)

lemma renaming_subst_compose:
  assumes
    "is_renaming \<rho>"
    "is_typed_on X \<V> (\<rho> \<odot> \<sigma>)"
    "is_typed_on X \<V> \<rho>"
  shows "is_typed_on (\<Union> (vars ` \<rho> ` X)) \<V> \<sigma>"
   using assms
   unfolding is_renaming_iff
   by (smt (verit) UN_E comp_subst_iff image_iff is_typed_id_subst left_neutral right_uniqueD
       singletonD vars_id_subst)

end

lemma (in renaming_variables) obtain_merged_\<V>:
  assumes
    \<rho>\<^sub>1: "is_renaming \<rho>\<^sub>1" and
    \<rho>\<^sub>2: "is_renaming \<rho>\<^sub>2" and
    rename_apart: "vars (expr \<cdot> \<rho>\<^sub>1) \<inter> vars (expr' \<cdot> \<rho>\<^sub>2) = {}" and
    \<V>\<^sub>2: "infinite_variables_per_type \<V>\<^sub>2" and
    finite_vars: "finite (vars expr)"
  obtains \<V>\<^sub>3 where
    "\<forall>x\<in>vars expr. \<V>\<^sub>1 x = \<V>\<^sub>3 (rename \<rho>\<^sub>1 x)"
    "\<forall>x\<in>vars expr'. \<V>\<^sub>2 x = \<V>\<^sub>3 (rename \<rho>\<^sub>2 x)"
    "infinite_variables_per_type \<V>\<^sub>3"
proof (rule that)

  define \<V>\<^sub>3 where
    "\<And>x. \<V>\<^sub>3 x \<equiv>
        if x \<in> vars (expr \<cdot> \<rho>\<^sub>1)
        then \<V>\<^sub>1 (inv \<rho>\<^sub>1 (id_subst x))
        else \<V>\<^sub>2 (inv \<rho>\<^sub>2 (id_subst x))"

  show "\<forall>x\<in>vars expr. \<V>\<^sub>1 x = \<V>\<^sub>3 (rename \<rho>\<^sub>1 x)"
  proof (intro ballI)
    fix x
    assume "x\<in>vars expr"

    then have "rename \<rho>\<^sub>1 x \<in> vars (expr \<cdot> \<rho>\<^sub>1)"
      using rename_variables[OF \<rho>\<^sub>1]
      by blast

    then show "\<V>\<^sub>1 x = \<V>\<^sub>3 (rename \<rho>\<^sub>1 x)"
      unfolding \<V>\<^sub>3_def
      by (simp add: \<rho>\<^sub>1 inv_renaming)
  qed

  show "\<forall>x\<in>vars expr'. \<V>\<^sub>2 x = \<V>\<^sub>3 (rename \<rho>\<^sub>2 x)"
  proof (intro ballI)
    fix x
    assume "x\<in> vars expr'"

    then have "rename \<rho>\<^sub>2 x \<in> vars (expr' \<cdot> \<rho>\<^sub>2)"
      using rename_variables[OF \<rho>\<^sub>2]
      by blast

    then show "\<V>\<^sub>2 x = \<V>\<^sub>3 (rename \<rho>\<^sub>2 x)"
      unfolding \<V>\<^sub>3_def
      using \<rho>\<^sub>2 inv_renaming rename_apart
      by (metis (mono_tags, lifting) disjoint_iff id_subst_rename)
  qed

  have "finite {x. x \<in> vars (expr \<cdot> \<rho>\<^sub>1)}"
    using finite_vars
    by (simp add: \<rho>\<^sub>1 rename_variables)

  moreover {
    fix \<tau>

    have "infinite {x. \<V>\<^sub>2 (inv \<rho>\<^sub>2 (id_subst x)) = \<tau>}"
    proof(rule surj_infinite_set[OF surj_inv_renaming, OF \<rho>\<^sub>2])

      show "infinite {x. \<V>\<^sub>2 x = \<tau>}"
        using \<V>\<^sub>2
        unfolding infinite_variables_per_type_def
        by blast
    qed
  }

  ultimately show "infinite_variables_per_type \<V>\<^sub>3"
    unfolding infinite_variables_per_type_def \<V>\<^sub>3_def if_distrib if_distribR Collect_if_eq
      Collect_not_mem_conj_eq
    by auto
qed

lemma (in renaming_variables) obtain_merged_\<V>':
  assumes
    \<rho>\<^sub>1: "is_renaming \<rho>\<^sub>1" and
    \<rho>\<^sub>2: "is_renaming \<rho>\<^sub>2" and
    rename_apart: "vars (expr \<cdot> \<rho>\<^sub>1) \<inter> vars (expr' \<cdot> \<rho>\<^sub>2) = {}" and
    \<V>\<^sub>1: "infinite_variables_per_type \<V>\<^sub>1" and
    finite_vars: "finite (vars expr')"
  obtains \<V>\<^sub>3 where
    "\<forall>x\<in>vars expr. \<V>\<^sub>1 x = \<V>\<^sub>3 (rename \<rho>\<^sub>1 x)"
    "\<forall>x\<in>vars expr'. \<V>\<^sub>2 x = \<V>\<^sub>3 (rename \<rho>\<^sub>2 x)"
    "infinite_variables_per_type \<V>\<^sub>3"
  using obtain_merged_\<V>[OF \<rho>\<^sub>2 \<rho>\<^sub>1 _ \<V>\<^sub>1 finite_vars] rename_apart
  by (metis disjoint_iff)

locale based_typed_renaming =
  base: explicitly_typed_renaming where
  subst = base_subst and vars = "base_vars :: 'base \<Rightarrow> 'v set" and
  typed = "typed :: ('v \<Rightarrow> 'ty) \<Rightarrow> 'base \<Rightarrow> 'ty \<Rightarrow> bool" +
  base: explicitly_typed_functional_substitution where
  vars = base_vars and subst = base_subst +
  based_functional_substitution +
  renaming_variables
begin

lemma renaming_grounding:
  assumes
    renaming: "base.is_renaming \<rho>" and
    \<rho>_\<gamma>_is_welltyped: "base.is_typed_on (vars expr) \<V> (\<rho> \<odot> \<gamma>)" and
    grounding: "is_ground (expr \<cdot> \<rho> \<odot> \<gamma>)" and
    \<V>_\<V>': "\<forall>x \<in> vars expr. \<V> x = \<V>' (rename \<rho> x)"
  shows "base.is_typed_on (vars (expr \<cdot> \<rho>)) \<V>' \<gamma>"
proof(intro ballI)
  fix x

  define y where "y \<equiv> inv \<rho> (id_subst x)"

  assume x_in_expr: "x \<in> vars (expr \<cdot> \<rho>)"

  then have y_in_vars: "y \<in> vars expr"
    using base.renaming_inv_in_vars[OF renaming] base.vars_id_subst
    unfolding y_def base.vars_subst_vars vars_subst
    by fastforce

  then have "base.is_ground (base_subst (id_subst y) (\<rho> \<odot> \<gamma>))"
    using variable_grounding[OF grounding y_in_vars]
    by (metis base.comp_subst_iff base.left_neutral)

  moreover have "typed \<V> (base_subst (id_subst y) (\<rho> \<odot> \<gamma>)) (\<V> y)"
    using \<rho>_\<gamma>_is_welltyped y_in_vars
    unfolding y_def
    by (metis base.comp_subst_iff base.left_neutral)

  ultimately have "typed \<V>' (base_subst (id_subst y) (\<rho> \<odot> \<gamma>)) (\<V> y)"
    by (meson base.explicit_is_ground_typed)

  moreover have "base_subst (id_subst y) (\<rho> \<odot> \<gamma>) = \<gamma> x"
    using x_in_expr base.renaming_inv_into[OF renaming] base.left_neutral
    unfolding y_def vars_subst base.comp_subst_iff
    by (metis (no_types, lifting) UN_E f_inv_into_f)

  ultimately show "typed \<V>' (\<gamma> x) (\<V>' x)"
    using \<V>_\<V>'[rule_format]
    by (metis base.right_uniqueD base.typed_id_subst id_subst_rename renaming renaming_inv_into
        x_in_expr y_def y_in_vars)
qed

lemma obtain_merged_grounding:
  fixes \<V>\<^sub>1 \<V>\<^sub>2 :: "'v \<Rightarrow> 'ty"
  assumes
    "base.is_typed_on (vars expr) \<V>\<^sub>1 \<gamma>\<^sub>1"
    "base.is_typed_on (vars expr') \<V>\<^sub>2 \<gamma>\<^sub>2"
    "is_ground (expr \<cdot> \<gamma>\<^sub>1)"
    "is_ground (expr' \<cdot> \<gamma>\<^sub>2)" and
    \<V>\<^sub>2: "infinite_variables_per_type \<V>\<^sub>2" and
    finite_vars: "finite (vars expr)"
  obtains \<rho>\<^sub>1 \<rho>\<^sub>2 \<gamma>  where
    "base.is_renaming \<rho>\<^sub>1"
    "base.is_renaming \<rho>\<^sub>2"
    "vars (expr \<cdot> \<rho>\<^sub>1) \<inter> vars (expr' \<cdot> \<rho>\<^sub>2) = {}"
    "base.is_typed_on (vars expr) \<V>\<^sub>1 \<rho>\<^sub>1"
    "base.is_typed_on (vars expr') \<V>\<^sub>2 \<rho>\<^sub>2"
    "\<forall>X \<subseteq> vars expr. \<forall>x\<in> X. \<gamma>\<^sub>1 x = (\<rho>\<^sub>1 \<odot> \<gamma>) x"
    "\<forall>X \<subseteq> vars expr'. \<forall>x\<in> X. \<gamma>\<^sub>2 x = (\<rho>\<^sub>2 \<odot> \<gamma>) x"
proof-

  obtain \<rho>\<^sub>1 \<rho>\<^sub>2 where
    \<rho>\<^sub>1: "base.is_renaming \<rho>\<^sub>1" and
    \<rho>\<^sub>2: "base.is_renaming \<rho>\<^sub>2" and
    rename_apart: "\<rho>\<^sub>1 ` (vars expr) \<inter> \<rho>\<^sub>2 ` (vars expr') = {}" and
    \<rho>\<^sub>1_is_welltyped: "base.is_typed_on (vars expr) \<V>\<^sub>1 \<rho>\<^sub>1" and
    \<rho>\<^sub>2_is_welltyped: "base.is_typed_on (vars expr') \<V>\<^sub>2 \<rho>\<^sub>2"
    using base.obtain_typed_renamings[OF finite_vars \<V>\<^sub>2].

  have rename_apart: "vars (expr \<cdot> \<rho>\<^sub>1) \<inter> vars (expr' \<cdot> \<rho>\<^sub>2) = {}"
    using rename_apart rename_variables_id_subst[OF \<rho>\<^sub>1] rename_variables_id_subst[OF \<rho>\<^sub>2]
    by blast

  from \<rho>\<^sub>1 \<rho>\<^sub>2 obtain \<rho>\<^sub>1_inv \<rho>\<^sub>2_inv where
    \<rho>\<^sub>1_inv: "\<rho>\<^sub>1 \<odot> \<rho>\<^sub>1_inv = id_subst" and
    \<rho>\<^sub>2_inv: "\<rho>\<^sub>2 \<odot> \<rho>\<^sub>2_inv = id_subst"
    unfolding base.is_renaming_def
    by blast

  define \<gamma> where
    "\<And>x. \<gamma> x \<equiv>
       if x \<in> vars (expr \<cdot> \<rho>\<^sub>1)
       then (\<rho>\<^sub>1_inv \<odot> \<gamma>\<^sub>1) x
       else (\<rho>\<^sub>2_inv \<odot> \<gamma>\<^sub>2) x"

  show ?thesis
  proof(rule that[OF \<rho>\<^sub>1 \<rho>\<^sub>2 rename_apart \<rho>\<^sub>1_is_welltyped \<rho>\<^sub>2_is_welltyped])

    have "\<forall>x\<in> vars expr.  \<gamma>\<^sub>1 x = (\<rho>\<^sub>1 \<odot> \<gamma>) x"
    proof(intro ballI)
      fix x
      assume x_in_vars: "x \<in> vars expr"

      obtain y where y: "\<rho>\<^sub>1 x = id_subst y"
        using obtain_renamed_variable[OF \<rho>\<^sub>1].

      then have "y \<in> vars (expr \<cdot> \<rho>\<^sub>1)"
        using x_in_vars \<rho>\<^sub>1 rename_variables_id_subst
        by (metis base.inj_id_subst image_eqI inj_image_mem_iff)

      then have "\<gamma> y = base_subst (\<rho>\<^sub>1_inv y) \<gamma>\<^sub>1"
        unfolding \<gamma>_def
        using base.comp_subst_iff
        by presburger

      then show "\<gamma>\<^sub>1 x = (\<rho>\<^sub>1 \<odot> \<gamma>) x"
        by (metis \<rho>\<^sub>1_inv base.comp_subst_iff base.left_neutral y)
    qed

    then show "\<forall>X\<subseteq> vars expr. \<forall>x\<in>X. \<gamma>\<^sub>1 x = (\<rho>\<^sub>1 \<odot> \<gamma>) x"
      by auto

  next

    have "\<forall>x\<in> vars expr'. \<gamma>\<^sub>2 x = (\<rho>\<^sub>2 \<odot> \<gamma>) x"
    proof(intro ballI)
      fix x
      assume x_in_vars: "x \<in> vars expr'"

      obtain y where y: "\<rho>\<^sub>2 x = id_subst y"
        using obtain_renamed_variable[OF \<rho>\<^sub>2].

      then have "y \<in> vars (expr' \<cdot> \<rho>\<^sub>2)"
        using x_in_vars \<rho>\<^sub>2 rename_variables_id_subst
        by (metis base.inj_id_subst imageI inj_image_mem_iff)

      then have "\<gamma> y = base_subst (\<rho>\<^sub>2_inv y) \<gamma>\<^sub>2"
        unfolding \<gamma>_def
        using base.comp_subst_iff rename_apart
        by auto

      then show "\<gamma>\<^sub>2 x = (\<rho>\<^sub>2 \<odot> \<gamma>) x"
        by (metis \<rho>\<^sub>2_inv base.comp_subst_iff base.left_neutral y)
    qed

    then show "\<forall>X\<subseteq> vars expr'. \<forall>x\<in>X. \<gamma>\<^sub>2 x = (\<rho>\<^sub>2 \<odot> \<gamma>) x"
      by auto
  qed
qed

lemma obtain_merged_grounding':
  fixes \<V>\<^sub>1 \<V>\<^sub>2 :: "'v \<Rightarrow> 'ty"
  assumes
    typed_\<gamma>\<^sub>1: "base.is_typed_on (vars expr) \<V>\<^sub>1 \<gamma>\<^sub>1" and
    typed_\<gamma>\<^sub>2: "base.is_typed_on (vars expr') \<V>\<^sub>2 \<gamma>\<^sub>2" and
    expr_grounding: "is_ground (expr \<cdot> \<gamma>\<^sub>1)" and
    expr'_grounding: "is_ground (expr' \<cdot> \<gamma>\<^sub>2)" and
    \<V>\<^sub>1: "infinite_variables_per_type \<V>\<^sub>1" and
    finite_vars: "finite (vars expr')"
  obtains \<rho>\<^sub>1 \<rho>\<^sub>2 \<gamma>  where
    "base.is_renaming \<rho>\<^sub>1"
    "base.is_renaming \<rho>\<^sub>2"
    "vars (expr \<cdot> \<rho>\<^sub>1) \<inter> vars (expr' \<cdot> \<rho>\<^sub>2) = {}"
    "base.is_typed_on (vars expr) \<V>\<^sub>1 \<rho>\<^sub>1"
    "base.is_typed_on (vars expr') \<V>\<^sub>2 \<rho>\<^sub>2"
    "\<forall>X \<subseteq> vars expr. \<forall>x\<in> X. \<gamma>\<^sub>1 x = (\<rho>\<^sub>1 \<odot> \<gamma>) x"
    "\<forall>X \<subseteq> vars expr'. \<forall>x\<in> X. \<gamma>\<^sub>2 x = (\<rho>\<^sub>2 \<odot> \<gamma>) x"
  using obtain_merged_grounding[OF typed_\<gamma>\<^sub>2 typed_\<gamma>\<^sub>1 expr'_grounding expr_grounding \<V>\<^sub>1 finite_vars]
  by (smt (verit, ccfv_threshold) inf_commute)

end

sublocale explicitly_typed_renaming \<subseteq>
  based_typed_renaming where base_vars = vars and base_subst = subst
  by unfold_locales

end
