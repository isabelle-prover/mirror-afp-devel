theory Typed_Functional_Substitution
  imports
    Typing
    Abstract_Substitution.Functional_Substitution
    Infinite_Variables_Per_Type
begin

type_synonym ('v, 'ty) var_types = "'v \<Rightarrow> 'ty"

locale base_typed_functional_substitution =
  base_functional_substitution where id_subst = id_subst
for
  id_subst :: "'v \<Rightarrow> 'base" and
  welltyped :: "('v, 'ty) var_types \<Rightarrow> 'base \<Rightarrow> 'ty \<Rightarrow> bool" +
assumes
  "\<And>\<V>. typing (welltyped \<V>)" and
  welltyped_id_subst [intro]: 
  "\<And>\<V> x. welltyped \<V> (id_subst x) (\<V> x) \<or> (\<nexists>\<tau>. welltyped \<V> (id_subst x) \<tau>)" 
begin

notation welltyped (\<open>_ \<turnstile> _ : _\<close> [1000, 0, 50] 50)

sublocale typing "welltyped \<V>"
  using base_typed_functional_substitution_axioms
  unfolding base_typed_functional_substitution_axioms_def base_typed_functional_substitution_def
  by metis

abbreviation type_preserving_on :: "'v set \<Rightarrow> ('v, 'ty) var_types \<Rightarrow> ('v \<Rightarrow> 'base) \<Rightarrow> bool" where
  "type_preserving_on X \<V> \<sigma> \<equiv> \<forall>x \<in> X. \<V> \<turnstile> id_subst x : \<V> x \<longrightarrow> \<V> \<turnstile> \<sigma> x : \<V> x"

abbreviation type_preserving where
  "type_preserving \<equiv> type_preserving_on UNIV"

(* TODO: Remove *)
lemma type_preserving_on_subst_update:
  assumes "\<V> \<turnstile> id_subst var : \<tau>" "\<V> \<turnstile> update : \<tau>" "type_preserving_on X \<V> \<sigma>"
  shows "type_preserving_on X \<V> (\<sigma>(var := update))"
  using assms
  by auto

lemma type_preserving_on_subst_update': 
  assumes "type_preserving_on X \<V> \<sigma>" "x \<in> X \<longrightarrow> \<V> \<turnstile> id_subst x : \<V> x \<longrightarrow> \<V> \<turnstile> update : \<V> x"
  shows "type_preserving_on X \<V> (\<sigma>(x := update))"
  using assms
  by auto

lemma type_preserving_on_subset:
  assumes "type_preserving_on Y \<V> \<sigma>" "X \<subseteq> Y"
  shows "type_preserving_on X \<V> \<sigma>"
  using assms
  by blast

lemma type_preserving_on_id_subst [intro]: "type_preserving_on X \<V> id_subst"
  by auto



end

locale typed_functional_substitution =
  based_functional_substitution where vars = vars and id_subst = id_subst +
  base: base_typed_functional_substitution where
    subst = base_subst and vars = base_vars and welltyped = base_welltyped and id_subst = id_subst
for
  base_welltyped :: "('v, 'ty) var_types \<Rightarrow> 'base \<Rightarrow> 'ty \<Rightarrow> bool" and 
  vars :: "'expr \<Rightarrow> 'v set" and
  welltyped :: "('v, 'ty) var_types \<Rightarrow> 'expr \<Rightarrow> 'ty' \<Rightarrow> bool" and
  id_subst :: "'v \<Rightarrow> 'base" +
assumes "\<And>\<V>. typing (welltyped \<V>)"
begin

sublocale typing "welltyped \<V>"
  using typed_functional_substitution_axioms
  unfolding typed_functional_substitution_axioms_def typed_functional_substitution_def
  by metis

(* TOOD NOW *)
(* TODO: Quite specific definition 
abbreviation is_welltyped_ground_instance where
  "is_welltyped_ground_instance expr \<V> \<gamma> \<equiv>
    is_ground (expr \<cdot> \<gamma>) \<and>
    base.type_preserving_on (vars expr) \<V> \<gamma> \<and>
    infinite_variables_per_type \<V>" *)

end

locale witnessed_typed_functional_substitution =
 typed_functional_substitution +
 assumes types_witnessed: "\<And>\<V> \<tau>. \<exists>b. base.is_ground b \<and> base_welltyped \<V> b \<tau>"
begin

lemma type_preserving_ground_subst_extension:
  assumes
    grounding: "is_ground (expr \<cdot> \<gamma>)" and
    \<gamma>_type_preserving_on: "base.type_preserving_on (vars expr) \<V> \<gamma>"
  obtains \<gamma>'
  where
    "base.is_ground_subst \<gamma>'"
    "base.type_preserving_on UNIV \<V> \<gamma>'"
    "\<forall>x \<in> vars expr. \<gamma> x = \<gamma>' x"
proof (rule that)

  define \<gamma>' where
    "\<And>x. \<gamma>' x \<equiv>
      if x \<in> vars expr
      then \<gamma> x
      else SOME base. base.is_ground base \<and> base_welltyped \<V> base (\<V> x)"

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
          by (smt (verit) types_witnessed tfl_some)
      qed
    }

    then show "base.is_ground (base_subst b \<gamma>')"
      using base.is_grounding_iff_vars_grounded
      by auto
  qed

  show "base.type_preserving_on UNIV \<V> \<gamma>'"
    unfolding \<gamma>'_def
    using \<gamma>_type_preserving_on types_witnessed
    by (simp add: verit_sko_ex_indirect)

  show "\<forall>x \<in> vars expr. \<gamma> x = \<gamma>' x"
    by (simp add: \<gamma>'_def)
qed

lemma type_preserving_on_ground_subst_extension:
  assumes
    grounding: "is_ground (expr \<cdot> \<gamma>)" and
    \<gamma>_type_preserving_on: "base.type_preserving_on (vars expr) \<V> \<gamma>"
  obtains \<gamma>'
  where
    "is_ground (expr' \<cdot> \<gamma>')"
    "base.type_preserving_on (vars expr') \<V> \<gamma>'"
    "\<forall>x \<in> vars expr. \<gamma> x = \<gamma>' x"
  using type_preserving_ground_subst_extension[OF assms]
  unfolding base.is_ground_subst_def is_grounding_iff_vars_grounded
  by (metis UNIV_I base.comp_subst_iff base.left_neutral)

end

sublocale base_typed_functional_substitution \<subseteq> typed_functional_substitution where
  base_subst = subst and base_vars = vars and base_welltyped = welltyped
  by unfold_locales

locale typed_grounding_functional_substitution =
  typed_functional_substitution + grounding
begin

(*definition welltyped_ground_instances where
  "welltyped_ground_instances typed_expr =
    { to_ground (fst typed_expr \<cdot> \<gamma>) | \<gamma>.
      is_welltyped_ground_instance (fst typed_expr) (snd typed_expr) \<gamma> }"

lemma typed_ground_instances_ground_instances':
  "welltyped_ground_instances (expr, \<V>) \<subseteq> ground_instances' expr"
  unfolding welltyped_ground_instances_def ground_instances'_def
  by auto*)

end

locale typed_subst_stability = typed_functional_substitution +
assumes
  welltyped_subst_stability [simp]: "\<And>\<V> expr \<sigma> \<tau>.
    base.type_preserving_on (vars expr) \<V> \<sigma> \<Longrightarrow> welltyped \<V> (expr \<cdot> \<sigma>) \<tau> \<longleftrightarrow> welltyped \<V> expr \<tau>"
begin

lemma welltyped_subst_stability_UNIV [simp]:
  "base.type_preserving \<V> \<sigma> \<Longrightarrow> welltyped \<V> (expr \<cdot> \<sigma>) \<tau> \<longleftrightarrow> welltyped \<V> expr \<tau>"
  by simp

lemma type_preserving_unifier:
  assumes 
    unifier: "expr \<cdot> \<upsilon> = expr' \<cdot> \<upsilon>" and
    type_preserving:"base.type_preserving_on (vars expr \<union> vars expr') \<V> \<upsilon>"
  shows "\<forall>\<tau>. welltyped \<V> expr \<tau> \<longleftrightarrow> welltyped \<V> expr' \<tau>"
  using assms
  by (metis Un_iff welltyped_subst_stability)

lemma unifier_same_type:
  assumes "base.type_preserving_on (vars expr \<union> vars expr') \<V> \<mu>" "is_unifier \<mu> {expr, expr'}"
  shows "\<forall>\<tau>. welltyped \<V> expr \<tau> \<longleftrightarrow> welltyped \<V> expr' \<tau>"
  using is_unifier_two assms
  using type_preserving_unifier
  by metis
  
lemma imgu_same_type:
  assumes "base.type_preserving_on (vars expr \<union> vars expr') \<V> \<mu>" "is_imgu \<mu> {{expr, expr'}}"
  shows "\<forall>\<tau>. welltyped \<V> expr \<tau> \<longleftrightarrow> welltyped \<V> expr' \<tau>"
  using unifier_same_type assms
  unfolding is_imgu_def is_unifier_set_def
  by blast

end

locale base_typed_subst_stability = 
  base_typed_functional_substitution +
  typed_subst_stability where base_subst = subst and base_vars = vars and base_welltyped = welltyped
begin

lemma type_preserving_on_subst_compose [intro]:
  assumes
    "type_preserving_on X \<V> \<sigma>"
    "type_preserving_on (\<Union>(vars ` \<sigma> ` X)) \<V> \<sigma>'"
  shows "type_preserving_on X \<V> (\<sigma> \<odot> \<sigma>')"
  using assms
  unfolding comp_subst_iff
  by auto

lemma type_preserving_subst_compose [intro]:
  assumes
    "type_preserving \<V> \<sigma>"
    "type_preserving \<V> \<sigma>'"
  shows "type_preserving \<V> (\<sigma> \<odot> \<sigma>')"
  using type_preserving_on_subst_compose[OF assms(1)] assms(2)
  by simp 

end

locale replaceable_\<V> = typed_functional_substitution +
  assumes replace_\<V>:
    "\<And>expr \<V> \<V>' \<tau>. \<forall>x\<in> vars expr. \<V> x = \<V>' x \<Longrightarrow> welltyped \<V> expr \<tau> \<Longrightarrow> welltyped \<V>' expr \<tau>"
begin

lemma replace_\<V>_iff:
  assumes "\<forall>x\<in> vars expr. \<V> x = \<V>' x"
  shows "welltyped \<V> expr \<tau> \<longleftrightarrow> welltyped \<V>' expr \<tau>"
  using assms
  by (metis replace_\<V>)

lemma is_ground_replace_\<V>:
  assumes "is_ground expr"
  shows "welltyped \<V> expr \<tau> \<longleftrightarrow> welltyped \<V>' expr \<tau>"
  using replace_\<V>_iff assms
  by blast

end

locale typed_renaming = 
  typed_functional_substitution + 
  renaming_variables +
  assumes
    welltyped_renaming [simp]:
    "\<And>\<V> \<V>' expr \<rho> \<tau>. base.is_renaming \<rho> \<Longrightarrow>
      \<forall>x \<in> vars expr. \<V> x = \<V>' (rename \<rho> x) \<Longrightarrow>
      welltyped \<V>' (expr \<cdot> \<rho>) \<tau> \<longleftrightarrow> welltyped \<V> expr \<tau>"

locale base_typed_renaming =
  base_typed_functional_substitution where
    welltyped = welltyped +
  typed_renaming where
    base_subst = subst and base_vars = vars and base_welltyped = welltyped and
    welltyped = welltyped +
  replaceable_\<V> where
    base_subst = subst and base_vars = vars and base_welltyped = welltyped and
    welltyped = welltyped
  for welltyped :: "('v, 'ty) var_types \<Rightarrow> 'expr \<Rightarrow> 'ty \<Rightarrow> bool"
begin

lemma renaming_ground_subst:
  assumes
    \<rho>: "is_renaming \<rho>" and
    \<gamma>: "is_ground_subst \<gamma>" and
    welltyped_\<rho>: "type_preserving_on X \<V> \<rho>" and
    welltyped_\<gamma>: "type_preserving_on (\<Union>(vars ` \<rho> ` X)) \<V>' \<gamma>" and
    rename: "\<forall>x \<in> X. \<V> x = \<V>' (rename \<rho> x)"
  shows "type_preserving_on X \<V> (\<rho> \<odot> \<gamma>)"
proof(intro ballI impI iffI)
  fix x
  assume 
    x_in_X: "x \<in> X" and 
    "\<V> \<turnstile> id_subst x : \<V> x"

  then have welltyped_\<rho>_x: "\<V> \<turnstile> \<rho> x : \<V> x"
    using welltyped_\<rho>
    by metis

  define y where "y \<equiv> (rename \<rho> x)"

  have "y \<in> \<Union>(vars ` \<rho> ` X)"
    using x_in_X
    unfolding y_def
    by (metis UN_iff \<rho> id_subst_rename image_eqI singletonI vars_id_subst)

  moreover then have "\<V> \<turnstile> \<gamma> y : \<V>' y"
    using replace_\<V> \<gamma> welltyped_\<gamma> rename x_in_X welltyped_\<rho>_x id_subst_rename[OF \<rho>]
    unfolding y_def is_ground_subst_def
    by (metis is_ground_replace_\<V> right_uniqueD singleton_iff variable_grounding vars_id_subst 
        welltyped_id_subst)
 
  ultimately have "\<V> \<turnstile> \<gamma> y : \<V> x"
    unfolding y_def
    using rename x_in_X
    by fastforce

  moreover have "\<gamma> y = (\<rho> \<odot> \<gamma>) x"
    unfolding y_def
    by (metis \<rho> comp_subst_iff id_subst_rename left_neutral)

  ultimately show "\<V> \<turnstile> (\<rho> \<odot> \<gamma>) x : \<V> x"
    by argo
qed

lemma obtain_type_preserving_renaming:
  fixes \<V> :: "'v \<Rightarrow> 'ty"
  assumes
    "finite X"
    "infinite_variables_per_type \<V>"
  obtains \<rho> :: "'v \<Rightarrow> 'expr" where
    "is_renaming \<rho>"
    "id_subst ` X \<inter> \<rho> ` Y = {}"
    "type_preserving_on Y \<V> \<rho>"
proof-

  obtain renaming :: "'v \<Rightarrow> 'v" where
    inj: "inj renaming" and
    rename_apart: "X \<inter> renaming ` Y = {}" and
    preserve_type: "\<forall>x \<in> Y. \<V> (renaming x) = \<V> x"
    using obtain_type_preserving_inj[OF assms].

  define \<rho> :: "'v \<Rightarrow> 'expr" where
    "\<And>x. \<rho> x \<equiv> id_subst (renaming x)"

  have \<rho>: "is_renaming \<rho>"
      using inj inj_id_subst
      unfolding \<rho>_def is_renaming_iff inj_def
      by blast

  then show ?thesis
  proof (rule that)

    show "id_subst ` X \<inter> \<rho> ` Y = {}"
      using rename_apart inj_id_subst
      unfolding \<rho>_def inj_def
      by blast
  next

    {
      fix x
      assume x_in_Y: "x \<in> Y" and welltyped_x: "\<V> \<turnstile> id_subst x : \<V> x"

      have "\<forall>x\<in>vars (id_subst x). \<V> x = \<V> (rename \<rho> x)"
        using \<rho>
        unfolding \<rho>_def
        by (metis id_subst_rename preserve_type singletonD singletonI vars_id_subst x_in_Y)

      then have "\<V> \<turnstile> id_subst x \<cdot> \<rho> : \<V> x"
        using welltyped_renaming[OF \<rho>] welltyped_x
        by metis

       then have "\<V> \<turnstile> \<rho> x : \<V> x"
        by (metis comp_subst_iff left_neutral)
    }

    then show "type_preserving_on Y \<V> \<rho>"
      by metis
  qed
qed

lemma obtain_type_preserving_renamings:
  fixes \<V>\<^sub>1 \<V>\<^sub>2 :: "'v \<Rightarrow> 'ty"
  assumes
    "finite X"
    "infinite_variables_per_type \<V>\<^sub>2"
  obtains \<rho>\<^sub>1 \<rho>\<^sub>2 :: "'v \<Rightarrow> 'expr" where
    "is_renaming \<rho>\<^sub>1"
    "is_renaming \<rho>\<^sub>2"
    "\<rho>\<^sub>1 ` X \<inter> \<rho>\<^sub>2 ` Y = {}"
    "type_preserving_on X \<V>\<^sub>1 \<rho>\<^sub>1"
    "type_preserving_on Y \<V>\<^sub>2 \<rho>\<^sub>2"
  using obtain_type_preserving_renaming[OF assms] is_renaming_id_subst welltyped_id_subst
  by metis

lemma obtain_type_preserving_renamings':
  fixes \<V>\<^sub>1 \<V>\<^sub>2 :: "'v \<Rightarrow> 'ty"
  assumes
    "finite Y"
    "infinite_variables_per_type \<V>\<^sub>1"
  obtains \<rho>\<^sub>1 \<rho>\<^sub>2 :: "'v \<Rightarrow> 'expr" where
    "is_renaming \<rho>\<^sub>1"
    "is_renaming \<rho>\<^sub>2"
    "\<rho>\<^sub>1 ` X \<inter> \<rho>\<^sub>2 ` Y = {}"
    "type_preserving_on X \<V>\<^sub>1 \<rho>\<^sub>1"
    "type_preserving_on Y \<V>\<^sub>2 \<rho>\<^sub>2"
  using obtain_type_preserving_renamings[OF assms]
  by (metis inf_commute)

end

lemma (in renaming_variables) obtain_merged_\<V>:
  assumes
    \<rho>\<^sub>1: "is_renaming \<rho>\<^sub>1" and
    \<rho>\<^sub>2: "is_renaming \<rho>\<^sub>2" and
    rename_apart: "vars (expr \<cdot> \<rho>\<^sub>1) \<inter> vars (expr' \<cdot> \<rho>\<^sub>2) = {}" and
    finite_vars: "finite (vars expr)" "finite (vars expr')" and
    infinite_UNIV: "infinite (UNIV :: 'a set)"
  obtains \<V>\<^sub>3 where
    "infinite_variables_per_type_on X \<V>\<^sub>3"
    "\<forall>x\<in>vars expr. \<V>\<^sub>1 x = \<V>\<^sub>3 (rename \<rho>\<^sub>1 x)"
    "\<forall>x\<in>vars expr'. \<V>\<^sub>2 x = \<V>\<^sub>3 (rename \<rho>\<^sub>2 x)"
proof-

  have finite: "finite (vars (expr \<cdot> \<rho>\<^sub>1))" "finite (vars (expr' \<cdot> \<rho>\<^sub>2))"
    using finite_vars
    by (simp_all add: \<rho>\<^sub>1 \<rho>\<^sub>2 rename_variables)

  obtain \<V>\<^sub>3 where 
    \<V>\<^sub>3: "infinite_variables_per_type_on X \<V>\<^sub>3" and
    \<V>\<^sub>3_\<V>\<^sub>1: "\<forall>x\<in>vars (expr \<cdot> \<rho>\<^sub>1). \<V>\<^sub>3 x = \<V>\<^sub>1 (inv \<rho>\<^sub>1 (id_subst x))" and
    \<V>\<^sub>3_\<V>\<^sub>2: "\<forall>x\<in>vars (expr' \<cdot> \<rho>\<^sub>2). \<V>\<^sub>3 x = \<V>\<^sub>2 (inv \<rho>\<^sub>2 (id_subst x))"
    using obtain_infinite_variables_per_type_on[OF infinite_UNIV finite rename_apart].

  show ?thesis
  proof (rule that[OF \<V>\<^sub>3])

    show "\<forall>x\<in>vars expr. \<V>\<^sub>1 x = \<V>\<^sub>3 (rename \<rho>\<^sub>1 x)"
      using \<V>\<^sub>3_\<V>\<^sub>1 \<rho>\<^sub>1 inv_renaming rename_variables
      by auto
  next

    show "\<forall>x\<in>vars expr'. \<V>\<^sub>2 x = \<V>\<^sub>3 (rename \<rho>\<^sub>2 x)"
      using \<V>\<^sub>3_\<V>\<^sub>2 \<rho>\<^sub>2 inv_renaming rename_variables
      by auto
  qed
qed

lemma (in renaming_variables) obtain_merged_\<V>_infinite_variables_for_all_types:
  assumes
    \<rho>\<^sub>1: "is_renaming \<rho>\<^sub>1" and
    \<rho>\<^sub>2: "is_renaming \<rho>\<^sub>2" and
    rename_apart: "vars (expr \<cdot> \<rho>\<^sub>1) \<inter> vars (expr' \<cdot> \<rho>\<^sub>2) = {}" and
    \<V>\<^sub>2: "infinite_variables_for_all_types \<V>\<^sub>2" and
    finite_vars: "finite (vars expr)"
  obtains \<V>\<^sub>3 where
    "\<forall>x\<in>vars expr. \<V>\<^sub>1 x = \<V>\<^sub>3 (rename \<rho>\<^sub>1 x)"
    "\<forall>x\<in>vars expr'. \<V>\<^sub>2 x = \<V>\<^sub>3 (rename \<rho>\<^sub>2 x)"
    "infinite_variables_for_all_types \<V>\<^sub>3"
proof (rule that)

  define \<V>\<^sub>3 where
    "\<And>x. \<V>\<^sub>3 x \<equiv>
        if x \<in> vars (expr \<cdot> \<rho>\<^sub>1)
        then \<V>\<^sub>1 (inv \<rho>\<^sub>1 (id_subst x))
        else \<V>\<^sub>2 (inv \<rho>\<^sub>2 (id_subst x))"

  show "\<forall>x\<in>vars expr. \<V>\<^sub>1 x = \<V>\<^sub>3 (rename \<rho>\<^sub>1 x)"
  proof (intro ballI)
    fix x
    assume "x \<in> vars expr"

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
        unfolding infinite_variables_for_all_types_def
        by blast
    qed
  }

  ultimately show "infinite_variables_for_all_types \<V>\<^sub>3"
    unfolding infinite_variables_for_all_types_def \<V>\<^sub>3_def if_distrib if_distribR Collect_if_eq
      Collect_not_mem_conj_eq
    by auto
qed

lemma (in renaming_variables) obtain_merged_\<V>'_infinite_variables_for_all_types:
  assumes
    \<rho>\<^sub>1: "is_renaming \<rho>\<^sub>1" and
    \<rho>\<^sub>2: "is_renaming \<rho>\<^sub>2" and
    rename_apart: "vars (expr \<cdot> \<rho>\<^sub>1) \<inter> vars (expr' \<cdot> \<rho>\<^sub>2) = {}" and
    \<V>\<^sub>1: "infinite_variables_for_all_types \<V>\<^sub>1" and
    finite_vars: "finite (vars expr')"
  obtains \<V>\<^sub>3 where
    "\<forall>x\<in>vars expr. \<V>\<^sub>1 x = \<V>\<^sub>3 (rename \<rho>\<^sub>1 x)"
    "\<forall>x\<in>vars expr'. \<V>\<^sub>2 x = \<V>\<^sub>3 (rename \<rho>\<^sub>2 x)"
    "infinite_variables_for_all_types \<V>\<^sub>3"
  using obtain_merged_\<V>_infinite_variables_for_all_types[OF \<rho>\<^sub>2 \<rho>\<^sub>1 _ \<V>\<^sub>1 finite_vars] rename_apart
  by (metis disjoint_iff)

locale based_typed_renaming =
  base: base_typed_renaming where
    subst = base_subst and vars = "base_vars :: 'base \<Rightarrow> 'v set" and
    welltyped = "base_welltyped :: ('v \<Rightarrow> 'ty) \<Rightarrow> 'base \<Rightarrow> 'ty \<Rightarrow> bool" +
  typed_renaming
begin

lemma renaming_grounding:
  assumes
    renaming: "base.is_renaming \<rho>" and
    \<rho>_\<gamma>_type_preserving: "base.type_preserving_on (vars expr) \<V> (\<rho> \<odot> \<gamma>)" and
    grounding: "is_ground (expr \<cdot> \<rho> \<odot> \<gamma>)" and
    \<V>_\<V>': "\<forall>x \<in> vars expr. \<V> x = \<V>' (rename \<rho> x)"
  shows "base.type_preserving_on (vars (expr \<cdot> \<rho>)) \<V>' \<gamma>"
proof(intro ballI impI)
  fix x

  define y where "y \<equiv> inv \<rho> (id_subst x)"

  assume 
    x_in_expr: "x \<in> vars (expr \<cdot> \<rho>)" and 
    welltyped_x: "base_welltyped \<V>' (id_subst x) (\<V>' x)"

  then have y_in_vars: "y \<in> vars expr"
    using base.renaming_inv_in_vars[OF renaming] base.vars_id_subst
    unfolding y_def base.vars_subst_vars vars_subst
    by fastforce

  then have "base.is_ground (base_subst (id_subst y) (\<rho> \<odot> \<gamma>))"
    using variable_grounding[OF grounding y_in_vars]
    by (metis base.comp_subst_iff base.left_neutral)

  moreover have "base_welltyped \<V> (base_subst (id_subst y) (\<rho> \<odot> \<gamma>)) (\<V> y)"
    using \<rho>_\<gamma>_type_preserving y_in_vars welltyped_x x_in_expr \<V>_\<V>'
    unfolding y_def
    by (smt (verit, del_insts) base.comp_subst_iff base.left_neutral base.vars_id_subst 
        base.welltyped_id_subst base.welltyped_renaming renaming renaming_inv_into singletonD)

  ultimately have "base_welltyped \<V>' (base_subst (id_subst y) (\<rho> \<odot> \<gamma>)) (\<V> y)"
    using base.is_ground_replace_\<V> 
    by blast

  moreover have "base_subst (id_subst y) (\<rho> \<odot> \<gamma>) = \<gamma> x"
    using x_in_expr base.renaming_inv_into[OF renaming] base.left_neutral
    unfolding y_def vars_subst base.comp_subst_iff
    by (metis (no_types, lifting) UN_E f_inv_into_f)

  ultimately show "base_welltyped \<V>' (\<gamma> x) (\<V>' x)"
    using \<V>_\<V>'[rule_format] welltyped_x
    by (metis base.right_uniqueD base.welltyped_id_subst id_subst_rename renaming renaming_inv_into
        x_in_expr y_def y_in_vars)
qed

lemma obtain_merged_grounding:
  fixes \<V>\<^sub>1 \<V>\<^sub>2 :: "'v \<Rightarrow> 'ty"
  assumes
    "base.type_preserving_on (vars expr) \<V>\<^sub>1 \<gamma>\<^sub>1"
    "base.type_preserving_on (vars expr') \<V>\<^sub>2 \<gamma>\<^sub>2"
    "is_ground (expr \<cdot> \<gamma>\<^sub>1)"
    "is_ground (expr' \<cdot> \<gamma>\<^sub>2)" and
    \<V>\<^sub>2: "infinite_variables_per_type \<V>\<^sub>2" and
    finite_vars: "finite (vars expr)"
  obtains \<rho>\<^sub>1 \<rho>\<^sub>2 \<gamma>  where
    "base.is_renaming \<rho>\<^sub>1"
    "base.is_renaming \<rho>\<^sub>2"
    "vars (expr \<cdot> \<rho>\<^sub>1) \<inter> vars (expr' \<cdot> \<rho>\<^sub>2) = {}"
    "base.type_preserving_on (vars expr) \<V>\<^sub>1 \<rho>\<^sub>1"
    "base.type_preserving_on (vars expr') \<V>\<^sub>2 \<rho>\<^sub>2"
    "\<forall>x \<in> vars expr. \<gamma>\<^sub>1 x = (\<rho>\<^sub>1 \<odot> \<gamma>) x"
    "\<forall>x \<in> vars expr'. \<gamma>\<^sub>2 x = (\<rho>\<^sub>2 \<odot> \<gamma>) x"
proof -

  obtain \<rho>\<^sub>1 \<rho>\<^sub>2 where
    \<rho>\<^sub>1: "base.is_renaming \<rho>\<^sub>1" and
    \<rho>\<^sub>2: "base.is_renaming \<rho>\<^sub>2" and
    rename_apart: "\<rho>\<^sub>1 ` (vars expr) \<inter> \<rho>\<^sub>2 ` (vars expr') = {}" and
    \<rho>\<^sub>1_is_welltyped: "base.type_preserving_on (vars expr) \<V>\<^sub>1 \<rho>\<^sub>1" and
    \<rho>\<^sub>2_is_welltyped: "base.type_preserving_on (vars expr') \<V>\<^sub>2 \<rho>\<^sub>2"
    using base.obtain_type_preserving_renamings[OF finite_vars \<V>\<^sub>2].

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
  proof (rule that[OF \<rho>\<^sub>1 \<rho>\<^sub>2 rename_apart \<rho>\<^sub>1_is_welltyped \<rho>\<^sub>2_is_welltyped])

    have "\<forall>x\<in> vars expr.  \<gamma>\<^sub>1 x = (\<rho>\<^sub>1 \<odot> \<gamma>) x"
    proof (intro ballI)
      fix x
      assume x_in_vars: "x \<in> vars expr"

      obtain y where y: "\<rho>\<^sub>1 x = id_subst y"
        using obtain_renamed_variable[OF \<rho>\<^sub>1] .

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

    then show "\<forall>x \<in> vars expr. \<gamma>\<^sub>1 x = (\<rho>\<^sub>1 \<odot> \<gamma>) x"
      by auto

  next

    have "\<forall>x\<in> vars expr'. \<gamma>\<^sub>2 x = (\<rho>\<^sub>2 \<odot> \<gamma>) x"
    proof (intro ballI)
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

    then show "\<forall>x \<in> vars expr'. \<gamma>\<^sub>2 x = (\<rho>\<^sub>2 \<odot> \<gamma>) x"
      by auto
  qed
qed

lemma obtain_merged_grounding':
  fixes \<V>\<^sub>1 \<V>\<^sub>2 :: "'v \<Rightarrow> 'ty"
  assumes
    typed_\<gamma>\<^sub>1: "base.type_preserving_on (vars expr) \<V>\<^sub>1 \<gamma>\<^sub>1" and
    typed_\<gamma>\<^sub>2: "base.type_preserving_on (vars expr') \<V>\<^sub>2 \<gamma>\<^sub>2" and
    expr_grounding: "is_ground (expr \<cdot> \<gamma>\<^sub>1)" and
    expr'_grounding: "is_ground (expr' \<cdot> \<gamma>\<^sub>2)" and
    \<V>\<^sub>1: "infinite_variables_per_type \<V>\<^sub>1" and
    finite_vars: "finite (vars expr')"
  obtains \<rho>\<^sub>1 \<rho>\<^sub>2 \<gamma>  where
    "base.is_renaming \<rho>\<^sub>1"
    "base.is_renaming \<rho>\<^sub>2"
    "vars (expr \<cdot> \<rho>\<^sub>1) \<inter> vars (expr' \<cdot> \<rho>\<^sub>2) = {}"
    "base.type_preserving_on (vars expr) \<V>\<^sub>1 \<rho>\<^sub>1"
    "base.type_preserving_on (vars expr') \<V>\<^sub>2 \<rho>\<^sub>2"
    "\<forall>x \<in> vars expr. \<gamma>\<^sub>1 x = (\<rho>\<^sub>1 \<odot> \<gamma>) x"
    "\<forall>x \<in> vars expr'. \<gamma>\<^sub>2 x = (\<rho>\<^sub>2 \<odot> \<gamma>) x"
  using obtain_merged_grounding[OF typed_\<gamma>\<^sub>2 typed_\<gamma>\<^sub>1 expr'_grounding expr_grounding \<V>\<^sub>1 finite_vars]
  by (smt (verit, ccfv_threshold) inf_commute)

end

sublocale base_typed_renaming \<subseteq>
  based_typed_renaming where base_vars = vars and base_subst = subst and base_welltyped = welltyped
  by unfold_locales

end
