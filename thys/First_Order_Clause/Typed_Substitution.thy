theory Typed_Substitution
  imports
    Typing
    Abstract_Substitution.Based_Substitution
    Infinite_Variables_Per_Type
begin

(* TODO: Move Typed_Substitution to own AFP Entry *)

type_synonym ('v, 'ty) var_types = "'v \<Rightarrow> 'ty"

locale base_typed_substitution =
  base_substitution where id_subst = id_subst and apply_subst = apply_subst +
  (* TODO: separate *)
  subst_update where id_subst = id_subst and apply_subst = apply_subst
for
  id_subst :: "'subst" and
  welltyped :: "('v, 'ty) var_types \<Rightarrow> 'base \<Rightarrow> 'ty \<Rightarrow> bool" and
  apply_subst :: "'v \<Rightarrow> 'subst \<Rightarrow> 'base" (infixl "\<cdot>v" 69) +
assumes
  "\<And>\<V>. typing (welltyped \<V>)" and
  welltyped_id_subst [intro]: 
  "\<And>\<V> x. welltyped \<V> (x \<cdot>v id_subst) (\<V> x) \<or> (\<nexists>\<tau>. welltyped \<V> (x \<cdot>v id_subst) \<tau>)" 
begin

notation welltyped (\<open>_ \<turnstile> _ : _\<close> [1000, 0, 50] 50)

sublocale typing "welltyped \<V>"
  using base_typed_substitution_axioms
  unfolding base_typed_substitution_axioms_def base_typed_substitution_def
  by metis

abbreviation type_preserving_on :: "'v set \<Rightarrow> ('v, 'ty) var_types \<Rightarrow> 'subst \<Rightarrow> bool" where
  "type_preserving_on X \<V> \<sigma> \<equiv> \<forall>x \<in> X. \<V> \<turnstile> x \<cdot>v id_subst : \<V> x \<longrightarrow> \<V> \<turnstile> x \<cdot>v \<sigma> : \<V> x"

(* TODO: Could this definition make my life easier in proofs?
   I can recover the other one using `welltyped_id_subst` *)
abbreviation type_preserving_on' :: "'v set \<Rightarrow> ('v, 'ty) var_types \<Rightarrow> 'subst \<Rightarrow> bool" where
  "type_preserving_on' X \<V> \<sigma> \<equiv> \<forall>x \<in> X. \<forall>\<tau>. \<V> \<turnstile> x \<cdot>v id_subst : \<tau> \<longrightarrow> \<V> \<turnstile> x \<cdot>v \<sigma> : \<tau>"

lemma "type_preserving_on X \<V> \<sigma> \<longleftrightarrow> type_preserving_on' X \<V> \<sigma>"
  using welltyped_id_subst 
  by blast

abbreviation type_preserving where
  "type_preserving \<equiv> type_preserving_on UNIV"

lemma type_preserving_on_subst_update: 
  assumes "type_preserving_on X \<V> \<sigma>" "x \<in> X \<longrightarrow> \<V> \<turnstile> x \<cdot>v id_subst : \<V> x \<longrightarrow> \<V> \<turnstile> update : \<V> x"
  shows "type_preserving_on X \<V> (\<sigma>\<lbrakk>x := update\<rbrakk>)"
  using assms
  by (metis all_subst_ident_if_ground id_subst_subst subst_update_var(1,2))

lemma type_preserving_on_subset:
  assumes "type_preserving_on Y \<V> \<sigma>" "X \<subseteq> Y"
  shows "type_preserving_on X \<V> \<sigma>"
  using assms
  by blast

lemma type_preserving_on_union [simp]: 
  "type_preserving_on (X \<union> Y) \<V> \<mu> \<longleftrightarrow> type_preserving_on X \<V> \<mu> \<and> type_preserving_on Y \<V> \<mu>"
  by auto

lemma type_preserving_on_id_subst [intro]: "type_preserving_on X \<V> id_subst"
  by auto

abbreviation type_preserving_unifier where
  "type_preserving_unifier \<V> \<upsilon> expr expr' \<equiv>
    type_preserving_on (vars expr \<union> vars expr') \<V> \<upsilon> \<and> expr \<cdot> \<upsilon> = expr' \<cdot> \<upsilon>"

end

locale typed_substitution =
  based_substitution where vars = vars and id_subst = id_subst and apply_subst = apply_subst +
  base: base_typed_substitution where
  subst = base_subst and vars = base_vars and is_ground = base_is_ground and
  welltyped = base_welltyped and id_subst = id_subst and apply_subst = apply_subst
for
  base_welltyped :: "('v, 'ty) var_types \<Rightarrow> 'base \<Rightarrow> 'ty \<Rightarrow> bool" and 
  vars :: "'expr \<Rightarrow> 'v set" and
  welltyped :: "('v, 'ty) var_types \<Rightarrow> 'expr \<Rightarrow> 'ty' \<Rightarrow> bool" and
  id_subst :: "'subst" and 
  apply_subst :: "'v \<Rightarrow> 'subst \<Rightarrow> 'base" (infixl "\<cdot>v" 69) +
assumes "\<And>\<V>. typing (welltyped \<V>)"
begin

sublocale typing "welltyped \<V>"
  using typed_substitution_axioms
  unfolding typed_substitution_axioms_def typed_substitution_def
  by metis

lemma only_ground_infinite_variables_per_type_on: 
  assumes "\<not>exists_nonground"
  shows "infinite_variables_per_type_on (vars expr) \<V>"
  using assms
  unfolding infinite_variables_per_type_on_def
  using no_vars_if_is_ground by simp

end

locale witnessed_typed_substitution =
  typed_substitution +
  finite_variables +
  subst_update +
  (* TODO: *)
  vars_grounded_iff_is_grounding +
assumes types_witnessed: "\<And>\<V> \<tau>. \<exists>b. base_is_ground b \<and> base_welltyped \<V> b \<tau>"
begin

lemma type_preserving_on_ground_subst_extension:
  assumes
    grounding: "is_ground (expr \<cdot> \<gamma>)" and
    \<gamma>_type_preserving_on: "base.type_preserving_on (vars expr) \<V> \<gamma>"
  obtains \<gamma>'
  where
    "is_ground (expr' \<cdot> \<gamma>')"
    "base.type_preserving_on (vars expr \<union> vars expr') \<V> \<gamma>'"
    "\<forall>x \<in> vars expr. x \<cdot>v \<gamma> = x \<cdot>v \<gamma>'"
    "expr \<cdot> \<gamma> = expr \<cdot> \<gamma>'"
proof (cases base.exists_nonground)
  case exists_nonground: True

  show ?thesis
  proof (rule that)
    let ?update =
      "\<lambda>x. if x \<in> vars expr
           then x \<cdot>v \<gamma>
           else SOME b. base_is_ground b \<and> base_welltyped \<V> b (\<V> x)"

    define \<gamma>' where
      "\<gamma>' \<equiv> \<gamma>\<lbrakk>fmap_of_set (vars expr \<union> vars expr') ?update\<rbrakk>"

    show "is_ground (expr' \<cdot> \<gamma>')"
    proof (rule is_grounding_if_vars_grounded, intro ballI)
      fix x 
      assume "x \<in> vars expr'"

      moreover have "base_is_ground (SOME b. base_is_ground b \<and> base_welltyped \<V> b (\<V> x))"
        by (rule someI2_ex[OF types_witnessed]) argo

      ultimately show "base_is_ground (x \<cdot>v \<gamma>')"
        unfolding \<gamma>'_def
        using 
          base.subst_updates_fmap_of_set[OF exists_nonground] 
          finite_vars
          grounding 
          variable_grounding      
        by auto
    qed

    show "base.type_preserving_on (vars expr \<union> vars expr') \<V> \<gamma>'"
      unfolding \<gamma>'_def
      using \<gamma>_type_preserving_on types_witnessed
      by (simp add: exists_nonground finite_vars verit_sko_ex_indirect)

    show "\<forall>x\<in>vars expr. x \<cdot>v \<gamma> = x \<cdot>v \<gamma>'"
      unfolding \<gamma>'_def
      by (simp add: exists_nonground finite_vars)

    show "expr \<cdot> \<gamma> = expr \<cdot> \<gamma>'"
      unfolding \<gamma>'_def
      using redundant_subst_updates
      by (simp add: finite_vars)
  qed
next
  case False

  then show ?thesis
    using that no_vars_if_is_ground exists_nonground_iff_base_exists_nonground
    by blast
qed

end

sublocale base_typed_substitution \<subseteq> typed_substitution where
  base_subst = subst and base_vars = vars and base_is_ground = is_ground and
  base_welltyped = welltyped
  by unfold_locales

locale typed_grounding_substitution = typed_substitution + grounding

locale typed_subst_stability = typed_substitution +
  assumes
    welltyped_subst_stability [simp]: "\<And>\<V> expr \<sigma> \<tau>.
      base.type_preserving_on (vars expr) \<V> \<sigma> \<Longrightarrow> welltyped \<V> (expr \<cdot> \<sigma>) \<tau> \<longleftrightarrow> welltyped \<V> expr \<tau>"
begin

(* TODO: Name *)
lemma welltyped_subst_stability' [simp]:
  assumes "base.type_preserving_on X \<V> \<sigma>" "vars expr \<subseteq> X"
  shows "welltyped \<V> (expr \<cdot> \<sigma>) \<tau> \<longleftrightarrow> welltyped \<V> expr \<tau>"
  using assms
  by (simp add: subset_iff)

lemma type_preserving_unifier:
  assumes 
    unifier: "expr \<cdot> \<upsilon> = expr' \<cdot> \<upsilon>" and
    type_preserving: "base.type_preserving_on (vars expr \<union> vars expr') \<V> \<upsilon>"
  shows "\<And>\<tau>. welltyped \<V> expr \<tau> \<longleftrightarrow> welltyped \<V> expr' \<tau>"
  using assms
  by (smt (verit, del_insts) le_sup_iff subset_iff welltyped_subst_stability')

lemma type_preserving_is_unifier:
  assumes 
    unifier: "is_unifier \<upsilon> X" and
    type_preserving: "base.type_preserving_on (\<Union>(vars ` X)) \<V> \<upsilon>"
  shows "\<And>\<tau>. \<forall>expr\<in>X. \<forall>expr'\<in>X. welltyped \<V> expr \<tau> \<longleftrightarrow> welltyped \<V> expr' \<tau>"
  using assms
  by (smt (verit, ccfv_threshold) Un_iff Union_iff image_eqI is_unifier_iff
      type_preserving_unifier)

lemma unifier_same_type:
  assumes "base.type_preserving_on (vars expr \<union> vars expr') \<V> \<mu>" "is_unifier \<mu> {expr, expr'}"
  shows "\<forall>\<tau>. welltyped \<V> expr \<tau> \<longleftrightarrow> welltyped \<V> expr' \<tau>"
  using assms type_preserving_unifier
  by simp

lemma imgu_same_type:
  assumes "base.type_preserving_on X \<V> \<mu>" "is_imgu \<mu> {{expr, expr'}}" "vars expr \<union> vars expr' \<subseteq> X" 
  shows "\<forall>\<tau>. welltyped \<V> expr \<tau> \<longleftrightarrow> welltyped \<V> expr' \<tau>"
  using unifier_same_type assms
  unfolding is_imgu_def is_unifier_set_def
  by blast

end

locale base_typed_subst_stability = 
  base_typed_substitution +
  typed_subst_stability where 
  base_subst = subst and base_vars = vars and base_is_ground = is_ground and
  base_welltyped = welltyped
begin

lemma type_preserving_ground_compose_ground_subst:
  assumes "is_ground_subst \<gamma>'" "type_preserving_on UNIV \<V> \<gamma>'" "type_preserving_on X \<V> \<mu>"
  shows "type_preserving_on X \<V> (\<mu> \<odot> \<gamma>')"
  using assms
  by (simp add: comp_subst_iff)

lemma type_preserving_on_subst_compose [intro]:
  assumes
    \<sigma>_type_preserving: "type_preserving_on X \<V> \<sigma>" and 
    \<sigma>'_type_preserving: "type_preserving_on (\<Union>(vars ` var_subst \<sigma> ` X)) \<V> \<sigma>'"
  shows "type_preserving_on X \<V> (\<sigma> \<odot> \<sigma>')"
proof (intro ballI impI exI)
  fix x
  assume 
    x_in_X: "x \<in> X" and
    welltyped_x: "\<V> \<turnstile> x \<cdot>v id_subst : \<V> x"

  then have "\<V> \<turnstile> x \<cdot>v \<sigma> : \<V> x"
    using assms
    by blast

  then show "\<V> \<turnstile> x \<cdot>v (\<sigma> \<odot> \<sigma>') : \<V> x"
    unfolding comp_subst_iff
    using \<sigma>'_type_preserving x_in_X
    by fastforce
qed

lemma type_preserving_on_subst_compose' [intro]:
  assumes
    \<sigma>_type_preserving: "type_preserving_on Y \<V> \<sigma>" and 
    \<sigma>'_type_preserving: "type_preserving_on Z \<V> \<sigma>'" and
    X_Y: "X \<subseteq> Y" and
    X_Z: "\<Union>(vars ` var_subst \<sigma> ` X) \<subseteq> Z"
  shows "type_preserving_on X \<V> (\<sigma> \<odot> \<sigma>')"
  by (rule type_preserving_on_subst_compose) (use assms in auto)

lemma type_preserving_subst_compose [intro]:
  assumes
    \<sigma>_type_preserving: "type_preserving \<V> \<sigma>" and
    \<sigma>'_type_preserving: "type_preserving \<V> \<sigma>'"
  shows "type_preserving \<V> (\<sigma> \<odot> \<sigma>')"
  using type_preserving_on_subst_compose[OF \<sigma>_type_preserving] \<sigma>'_type_preserving
  by simp 

end

locale replaceable_\<V> = typed_substitution +
  assumes replace_\<V>:
    "\<And>expr \<V> \<V>' \<tau>. \<forall>x\<in> vars expr. \<V> x = \<V>' x \<Longrightarrow> welltyped \<V> expr \<tau> \<Longrightarrow> welltyped \<V>' expr \<tau>"
begin

lemma replace_\<V>_iff:
  assumes "\<forall>x\<in> vars expr. \<V> x = \<V>' x"
  shows "welltyped \<V> expr \<tau> \<longleftrightarrow> welltyped \<V>' expr \<tau>"
  using assms
  by (metis replace_\<V>)

lemma replace_\<V>_iff':
  assumes "\<forall>x\<in> X. \<V> x = \<V>' x" "vars expr \<subseteq> X"
  shows "welltyped \<V> expr \<tau> \<longleftrightarrow> welltyped \<V>' expr \<tau>"
  using replace_\<V>_iff
  using assms
  by (simp add: subset_iff)

lemma is_ground_replace_\<V>:
  assumes "is_ground expr"
  shows "welltyped \<V> expr \<tau> \<longleftrightarrow> welltyped \<V>' expr \<tau>"
  using replace_\<V>_iff assms
  by (metis empty_iff no_vars_if_is_ground)

end

locale base_replaceable_\<V> = 
  base_typed_substitution +
  replaceable_\<V> where
  base_subst = subst and base_vars = vars and base_is_ground = is_ground and
  base_welltyped = welltyped
begin

lemma is_ground_subst_replace_\<V>:
  assumes 
    "is_ground_subst \<gamma>"
    "type_preserving_on X \<V> \<gamma>"
    "\<forall>x\<in>X. \<V> x = \<V>' x"
  shows "type_preserving_on X \<V>' \<gamma>"
  using assms
  by (metis (no_types, lifting) singletonD id_subst_subst is_ground_replace_\<V> is_ground_subst_def
      replace_\<V>_iff' vars_id_subst_subset)

end

(* TODO: Could this be proven using replaceable_V and welltyped_subst_stability? *)
locale typed_renaming =
  typed_substitution +
  renaming_variables +
  assumes
    welltyped_renaming [simp]:
    "\<And>\<V> \<V>' expr \<rho> \<tau>. is_renaming \<rho> \<Longrightarrow>
      \<forall>x \<in> vars expr. \<V> x = \<V>' (rename \<rho> x) \<Longrightarrow>
      welltyped \<V>' (expr \<cdot> \<rho>) \<tau> \<longleftrightarrow> welltyped \<V> expr \<tau>"

locale base_typed_renaming =
  base_typed_substitution where
  welltyped = welltyped +

  typed_renaming where
  base_subst = subst and base_vars = vars and base_is_ground = is_ground and
  base_welltyped = welltyped and welltyped = welltyped +

  replaceable_\<V> where
  base_subst = subst and base_vars = vars and base_is_ground = is_ground and
  base_welltyped = welltyped and welltyped = welltyped +

  based_subst_update where
  base_subst = subst and base_vars = vars and base_is_ground = is_ground +

  create_renaming where base_subst = subst and base_vars = vars and base_is_ground = is_ground +
  (* TODO: *)
  subst_updates_compat
for welltyped :: "('v, 'ty) var_types \<Rightarrow> 'expr \<Rightarrow> 'ty \<Rightarrow> bool"
begin

lemma typed_renaming_grounding_subst_compose:
  assumes
    \<rho>: "is_renaming \<rho>" and
    grounding: "\<forall>expr \<in> (var_subst (\<rho> \<odot> \<gamma>) ` X). is_ground expr" and
    welltyped_\<rho>: "type_preserving_on X \<V> \<rho>" and
    welltyped_\<gamma>: "type_preserving_on (\<Union>(vars ` var_subst \<rho> ` X)) \<V>' \<gamma>" and
    rename: "\<forall>x \<in> X. \<V> x = \<V>' (rename \<rho> x)"
  shows "type_preserving_on X \<V> (\<rho> \<odot> \<gamma>)"
proof (cases "exists_nonground")
  case exists_nonground: True

  show ?thesis
  proof (intro ballI impI iffI)
    fix x
    assume 
      x_in_X: "x \<in> X" and 
      \<V>_x: "\<V> \<turnstile> x \<cdot>v id_subst : \<V> x"

    have "\<V> \<turnstile> x \<cdot>v \<rho> : \<V> x"
      by (metis x_in_X \<V>_x welltyped_\<rho>)

    then have "\<V>' \<turnstile> x \<cdot>v \<rho> : \<V> x"
      using welltyped_renaming[OF \<rho>] vars_id_subst[OF exists_nonground]
      by (metis \<V>_x empty_iff id_subst_subst insert_iff rename x_in_X)

    then have "\<V>' \<turnstile> x \<cdot>v \<rho> : \<V>' (rename \<rho> x)"
      by (simp add: rename x_in_X)

    then have "\<V>' \<turnstile> x \<cdot>v \<rho> \<odot> \<gamma> : \<V>' (rename \<rho> x)"
      using x_in_X welltyped_\<gamma>  vars_id_subst[OF exists_nonground]
      using id_subst_rename[OF exists_nonground \<rho>]
      unfolding comp_subst_iff
      by (smt (verit, best) UN_iff id_subst_subst image_eqI insertCI)

    then have "\<V>' \<turnstile> x \<cdot>v \<rho> \<odot> \<gamma> : \<V> x"
      by (simp add: rename x_in_X)

    then show "\<V> \<turnstile> x \<cdot>v \<rho> \<odot> \<gamma> : \<V> x"
      by (metis grounding imageI is_ground_replace_\<V> x_in_X)
  qed
next
  case False

  then show ?thesis 
    by (metis all_subst_ident_if_ground id_subst_subst)
qed

lemma typed_renaming_ground_subst_subst_compose:
  assumes
    \<rho>: "is_renaming \<rho>" and
    \<gamma>: "is_ground_subst \<gamma>" and
    welltyped_\<rho>: "type_preserving_on X \<V> \<rho>" and
    welltyped_\<gamma>: "type_preserving_on (\<Union>(vars ` var_subst \<rho> ` X)) \<V>' \<gamma>" and
    rename: "\<forall>x \<in> X. \<V> x = \<V>' (rename \<rho> x)"
  shows "type_preserving_on X \<V> (\<rho> \<odot> \<gamma>)"
  using 
    typed_renaming_grounding_subst_compose[OF \<rho> _ welltyped_\<rho> welltyped_\<gamma> rename]
    is_ground_subst_is_ground[OF \<gamma>]
  unfolding comp_subst_iff
  by auto

lemma obtain_type_preserving_renaming:
  fixes \<V> :: "('v, 'ty) var_types"
  assumes
    exists_nonground: "exists_nonground" and
    finite_X: "finite X" and finite_Y: "finite Y" and 
    \<V>: "infinite_variables_per_type_on Y \<V>"
  obtains \<rho> where
    "is_renaming \<rho>"
    "var_subst id_subst ` X \<inter> var_subst \<rho> ` Y = {}"
    "type_preserving_on Y \<V> \<rho>"
proof -

  obtain renaming :: "'v \<Rightarrow> 'v" where
    inj: "inj renaming" and
    rename_apart: "X \<inter> renaming ` Y = {}" and
    preserve_type: "\<forall>x \<in> Y. \<V> (renaming x) = \<V> x"
    using obtain_type_preserving_inj[OF finite_X \<V>] .

  have bij: "bij_betw renaming Y (renaming ` Y)"
    by (metis inj bij_betw_subset top_greatest bij_betw_def)

  define \<rho> where
    "\<rho> \<equiv> renaming_of_bij renaming Y (renaming ` Y)"
  
  have \<rho>: "is_renaming \<rho>"
    using create_renaming[OF exists_nonground finite_Y bij]
    unfolding \<rho>_def .

  then show ?thesis
  proof (rule that)

    have "\<forall>y \<in> Y. y \<cdot>v \<rho> = renaming y \<cdot>v id_subst"
      unfolding \<rho>_def
      by (simp add: bij exists_nonground finite_Y renaming_of_bij_on_S)

    then show "var_subst id_subst ` X \<inter> var_subst \<rho> ` Y = {}"
      using rename_apart
      by (smt (verit, best) disjoint_iff exists_nonground image_iff inj_def inj_id_subst)
  next

    show "type_preserving_on Y \<V> \<rho>"
    proof (intro ballI impI)
      fix x
      assume x_in_Y: "x \<in> Y" and welltyped_x: "\<V> \<turnstile> x \<cdot>v id_subst : \<V> x"

      have "\<forall>x\<in>vars (x \<cdot>v id_subst). \<V> x = \<V> (rename \<rho> x)"
        using \<rho>
        unfolding \<rho>_def
        by (metis (lifting) bij exists_nonground finite_Y id_subst_rename preserve_type 
            renaming_of_bij_on_S singleton_iff vars_id_subst x_in_Y)

      then show "\<V> \<turnstile> x \<cdot>v \<rho> : \<V> x"
        using welltyped_renaming[OF \<rho>] welltyped_x
        by (metis id_subst_subst)
    qed
  qed
qed

lemma obtain_type_preserving_renamings:
  fixes \<V>\<^sub>1 \<V>\<^sub>2 :: "('v, 'ty) var_types"
  assumes
    "exists_nonground"
    "finite X" "finite Y"
    "infinite_variables_per_type_on Y \<V>\<^sub>2"
  obtains \<rho>\<^sub>1 \<rho>\<^sub>2 where
    "is_renaming \<rho>\<^sub>1"
    "is_renaming \<rho>\<^sub>2"
    "var_subst \<rho>\<^sub>1 ` X \<inter> var_subst \<rho>\<^sub>2 ` Y = {}"
    "type_preserving_on X \<V>\<^sub>1 \<rho>\<^sub>1"
    "type_preserving_on Y \<V>\<^sub>2 \<rho>\<^sub>2"
  using obtain_type_preserving_renaming[OF assms] is_renaming_id_subst welltyped_id_subst
  by metis

lemma obtain_type_preserving_renamings':
  fixes \<V>\<^sub>1 \<V>\<^sub>2 :: "('v, 'ty) var_types"
  assumes
    "exists_nonground"
    "finite Y" "finite X"
    "infinite_variables_per_type_on X \<V>\<^sub>1"    
  obtains \<rho>\<^sub>1 \<rho>\<^sub>2 where
    "is_renaming \<rho>\<^sub>1"
    "is_renaming \<rho>\<^sub>2"
    "var_subst \<rho>\<^sub>1 ` X \<inter> var_subst \<rho>\<^sub>2 ` Y = {}"
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
    infinite_UNIV: "exists_nonground \<Longrightarrow> infinite (UNIV :: 'c set)"
  obtains \<V>\<^sub>3 where
    "exists_nonground \<Longrightarrow> infinite_variables_per_type_on X \<V>\<^sub>3"
    "\<forall>x\<in>vars expr. \<V>\<^sub>1 x = \<V>\<^sub>3 (rename \<rho>\<^sub>1 x)"
    "\<forall>x\<in>vars expr'. \<V>\<^sub>2 x = \<V>\<^sub>3 (rename \<rho>\<^sub>2 x)"
proof -

  have finite: "finite (vars (expr \<cdot> \<rho>\<^sub>1))" "finite (vars (expr' \<cdot> \<rho>\<^sub>2))"
    using finite_vars
    by (simp_all add: \<rho>\<^sub>1 \<rho>\<^sub>2 rename_variables)

  show ?thesis
  proof (cases exists_nonground)
    case True

    obtain \<V>\<^sub>3 where 
      \<V>\<^sub>3: "infinite_variables_per_type_on X \<V>\<^sub>3" and
      \<V>\<^sub>3_\<V>\<^sub>1: "\<forall>x\<in>vars (expr \<cdot> \<rho>\<^sub>1). \<V>\<^sub>3 x = \<V>\<^sub>1 (inv (var_subst \<rho>\<^sub>1) (x \<cdot>v id_subst))" and
      \<V>\<^sub>3_\<V>\<^sub>2: "\<forall>x\<in>vars (expr' \<cdot> \<rho>\<^sub>2). \<V>\<^sub>3 x = \<V>\<^sub>2 (inv (var_subst \<rho>\<^sub>2) (x \<cdot>v id_subst))"
      using obtain_infinite_variables_per_type_on[OF infinite_UNIV[OF True] finite rename_apart] .

    show ?thesis
    proof (rule that[OF \<V>\<^sub>3])

      show "\<forall>x\<in>vars expr. \<V>\<^sub>1 x = \<V>\<^sub>3 (rename \<rho>\<^sub>1 x)"
        using \<V>\<^sub>3_\<V>\<^sub>1 \<rho>\<^sub>1 inv_renaming rename_variables True
        by auto
    next

      show "\<forall>x\<in>vars expr'. \<V>\<^sub>2 x = \<V>\<^sub>3 (rename \<rho>\<^sub>2 x)"
        using \<V>\<^sub>3_\<V>\<^sub>2 \<rho>\<^sub>2 inv_renaming rename_variables True
        by simp
    qed
  next
    case False

    show ?thesis  
    proof (rule that)

      show "exists_nonground \<Longrightarrow> infinite_variables_per_type_on X \<V>\<^sub>1"
        using False
        by argo
    next

      show "\<forall>x\<in>vars expr. \<V>\<^sub>1 x = \<V>\<^sub>1 (rename \<rho>\<^sub>1 x)" "\<forall>x\<in>vars expr'. \<V>\<^sub>2 x = \<V>\<^sub>1 (rename \<rho>\<^sub>2 x)" 
        using False
        by (simp_all add: no_vars_if_is_ground)
    qed
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
proof (cases exists_nonground)
  case True

  show ?thesis
  proof (rule that)
    define \<V>\<^sub>3 where
      "\<And>x. \<V>\<^sub>3 x \<equiv>
        if x \<in> vars (expr \<cdot> \<rho>\<^sub>1)
        then \<V>\<^sub>1 (inv (var_subst \<rho>\<^sub>1) (x \<cdot>v id_subst))
        else \<V>\<^sub>2 (inv (var_subst \<rho>\<^sub>2) (x \<cdot>v id_subst))"

    show "\<forall>x\<in>vars expr. \<V>\<^sub>1 x = \<V>\<^sub>3 (rename \<rho>\<^sub>1 x)"
    proof (intro ballI)
      fix x
      assume "x \<in> vars expr"

      then have "rename \<rho>\<^sub>1 x \<in> vars (expr \<cdot> \<rho>\<^sub>1)"
        using rename_variables[OF \<rho>\<^sub>1]
        by blast

      then show "\<V>\<^sub>1 x = \<V>\<^sub>3 (rename \<rho>\<^sub>1 x)"
        using True
        unfolding \<V>\<^sub>3_def
        by (auto simp: \<rho>\<^sub>1 inv_renaming)
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
        using \<rho>\<^sub>2 inv_renaming rename_apart True
        by auto
    qed

    have "finite {x. x \<in> vars (expr \<cdot> \<rho>\<^sub>1)}"
      using finite_vars
      by (simp add: \<rho>\<^sub>1 rename_variables)

    moreover {
      fix \<tau>

      have "infinite {x. \<V>\<^sub>2 (inv (var_subst \<rho>\<^sub>2) (x \<cdot>v id_subst)) = \<tau>}"
      proof(rule surj_infinite_set[OF surj_inv_renaming, OF True \<rho>\<^sub>2])

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
next
  case False
  show ?thesis
  proof (rule that)

    show "\<forall>x\<in>vars expr. \<V>\<^sub>1 x = \<V>\<^sub>2 (rename \<rho>\<^sub>1 x)"
      using False no_vars_if_is_ground 
      by simp
  next

    show "\<forall>x\<in>vars expr'. \<V>\<^sub>2 x = \<V>\<^sub>2 (rename \<rho>\<^sub>2 x)"
      using False no_vars_if_is_ground
      by simp
  next
    show "infinite_variables_for_all_types \<V>\<^sub>2"
      using \<V>\<^sub>2 .
  qed
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
  welltyped = "base_welltyped :: ('v, 'ty) var_types \<Rightarrow> 'base \<Rightarrow> 'ty \<Rightarrow> bool" and
  is_ground = base_is_ground +
  typed_renaming +
  (* TODO: *)
  subst_updates_compat
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

  define y where "y \<equiv> inv (var_subst \<rho>) (x \<cdot>v id_subst)"

  assume 
    x_in_expr: "x \<in> vars (expr \<cdot> \<rho>)" and 
    welltyped_x: "base_welltyped \<V>' (x \<cdot>v id_subst) (\<V>' x)"

  then have y_in_vars: "y \<in> vars expr"
    using 
      base.renaming_inv_in_vars[OF renaming] 
      base.vars_id_subst
      renaming renaming_inv_in_vars 
      x_in_expr
    unfolding y_def base.vars_subst vars_subst
    by auto

  then have "base_is_ground (base_subst (y \<cdot>v id_subst) (\<rho> \<odot> \<gamma>))"
    using variable_grounding[OF grounding y_in_vars]
    by (metis base.comp_subst_iff base.left_neutral)

  moreover have inv_renaming: "(inv (\<lambda>x. x \<cdot>v \<rho>) (x \<cdot>v id_subst) \<cdot>v \<rho>) = (x \<cdot>v id_subst)"
    using renaming renaming_inv_into x_in_expr
    by blast

  then have "base_welltyped \<V> (base_subst (y \<cdot>v id_subst) (\<rho> \<odot> \<gamma>)) (\<V> y)"
    using \<rho>_\<gamma>_type_preserving y_in_vars welltyped_x x_in_expr \<V>_\<V>'
    unfolding y_def
    by (smt (verit, best) is_ground_subst_is_ground base.is_ground_subst_def base.inv_renaming
        base.vars_id_subst ground_subst_iff_base_ground_subst id_subst_subst empty_not_insert
        mk_disjoint_insert no_vars_if_is_ground renaming id_subst_rename singleton_iff
        base.welltyped_renaming)

  ultimately have "base_welltyped \<V>' (base_subst (y \<cdot>v id_subst) (\<rho> \<odot> \<gamma>)) (\<V> y)"
    using base.is_ground_replace_\<V> 
    by blast

  moreover have "base_subst (y \<cdot>v id_subst) (\<rho> \<odot> \<gamma>) = x \<cdot>v \<gamma>"
    using x_in_expr base.renaming_inv_into[OF renaming] base.left_neutral
    unfolding y_def vars_subst base.comp_subst_iff
    by (simp add: inv_renaming)

  ultimately show "base_welltyped \<V>' (x \<cdot>v \<gamma>) (\<V>' x)"
    using \<V>_\<V>'[rule_format] welltyped_x
    by (smt (verit, ccfv_threshold) base.all_subst_ident_if_ground base.id_subst_rename y_in_vars
        base.vars_id_subst ex_in_conv id_subst_subst insert_iff inv_renaming renaming y_def)
qed

lemma obtain_merged_grounding:
  fixes \<V>\<^sub>1 \<V>\<^sub>2 :: "('v, 'ty) var_types"
  assumes
    "base.type_preserving_on (vars expr) \<V>\<^sub>1 \<gamma>\<^sub>1"
    "base.type_preserving_on (vars expr') \<V>\<^sub>2 \<gamma>\<^sub>2"
    "is_ground (expr \<cdot> \<gamma>\<^sub>1)"
    "is_ground (expr' \<cdot> \<gamma>\<^sub>2)" and
    \<V>\<^sub>2: "base.exists_nonground \<Longrightarrow> infinite_variables_per_type_on (vars expr') \<V>\<^sub>2" and
    finite_vars: "finite (vars expr)" and
    finite_vars': "finite (vars expr')"
  obtains \<rho>\<^sub>1 \<rho>\<^sub>2 \<gamma>  where
    "base.is_renaming \<rho>\<^sub>1"
    "base.is_renaming \<rho>\<^sub>2"
    "vars (expr \<cdot> \<rho>\<^sub>1) \<inter> vars (expr' \<cdot> \<rho>\<^sub>2) = {}"
    "base.type_preserving_on (vars expr) \<V>\<^sub>1 \<rho>\<^sub>1"
    "base.type_preserving_on (vars expr') \<V>\<^sub>2 \<rho>\<^sub>2"
    "\<forall>x \<in> vars expr. x \<cdot>v \<gamma>\<^sub>1 =  x \<cdot>v \<rho>\<^sub>1 \<odot> \<gamma>"
    "\<forall>x \<in> vars expr'. x \<cdot>v \<gamma>\<^sub>2 = x \<cdot>v \<rho>\<^sub>2 \<odot> \<gamma>"
    "expr \<cdot> \<gamma>\<^sub>1 = expr \<cdot> \<rho>\<^sub>1 \<odot> \<gamma>"
    "expr' \<cdot> \<gamma>\<^sub>2 = expr' \<cdot> \<rho>\<^sub>2 \<odot> \<gamma>"
proof (cases "base.exists_nonground")
  case base_exists_nonground: True

  then have exists_nonground: exists_nonground
    unfolding exists_nonground_iff_base_exists_nonground .

  obtain \<rho>\<^sub>1 \<rho>\<^sub>2 where
    \<rho>\<^sub>1: "base.is_renaming \<rho>\<^sub>1" and
    \<rho>\<^sub>2: "base.is_renaming \<rho>\<^sub>2" and
    rename_apart: "var_subst \<rho>\<^sub>1 ` (vars expr) \<inter> var_subst \<rho>\<^sub>2 ` (vars expr') = {}" and
    \<rho>\<^sub>1_is_welltyped: "base.type_preserving_on (vars expr) \<V>\<^sub>1 \<rho>\<^sub>1" and
    \<rho>\<^sub>2_is_welltyped: "base.type_preserving_on (vars expr') \<V>\<^sub>2 \<rho>\<^sub>2"
    using base.obtain_type_preserving_renamings[OF 
            base_exists_nonground finite_vars finite_vars' \<V>\<^sub>2[OF base_exists_nonground]] .

  have rename_apart: "vars (expr \<cdot> \<rho>\<^sub>1) \<inter> vars (expr' \<cdot> \<rho>\<^sub>2) = {}"
    using rename_apart rename_variables_id_subst[OF \<rho>\<^sub>1] rename_variables_id_subst[OF \<rho>\<^sub>2]
    by blast

  from \<rho>\<^sub>1 \<rho>\<^sub>2 obtain \<rho>\<^sub>1_inv \<rho>\<^sub>2_inv where
    \<rho>\<^sub>1_inv: "\<rho>\<^sub>1 \<odot> \<rho>\<^sub>1_inv = id_subst" and
    \<rho>\<^sub>2_inv: "\<rho>\<^sub>2 \<odot> \<rho>\<^sub>2_inv = id_subst"
    unfolding base.is_renaming_def
    by blast

  let ?update = "\<lambda>x. if x \<in> vars (expr \<cdot> \<rho>\<^sub>1)
                     then x \<cdot>v \<rho>\<^sub>1_inv \<odot> \<gamma>\<^sub>1
                     else x \<cdot>v \<rho>\<^sub>2_inv \<odot> \<gamma>\<^sub>2"

  define \<gamma> where
    "\<gamma> \<equiv> id_subst\<lbrakk>fmap_of_set (vars (expr \<cdot> \<rho>\<^sub>1) \<union> vars (expr' \<cdot> \<rho>\<^sub>2)) ?update\<rbrakk>"

  show ?thesis
  proof (rule that[OF \<rho>\<^sub>1 \<rho>\<^sub>2 rename_apart \<rho>\<^sub>1_is_welltyped \<rho>\<^sub>2_is_welltyped])

    have "\<forall>x\<in> vars expr. x \<cdot>v \<gamma>\<^sub>1 = x \<cdot>v \<rho>\<^sub>1 \<odot> \<gamma>"
    proof (intro ballI)
      fix x
      assume x_in_vars: "x \<in> vars expr"

      obtain y where y: "x \<cdot>v \<rho>\<^sub>1 = y \<cdot>v id_subst"
        using obtain_renamed_variable[OF exists_nonground \<rho>\<^sub>1] .

      then have "y \<in> vars (expr \<cdot> \<rho>\<^sub>1)"
        using x_in_vars \<rho>\<^sub>1 rename_variables_id_subst base_exists_nonground
        by (metis base.inj_id_subst image_eqI inj_image_mem_iff)

      then have "y \<cdot>v \<gamma> = base_subst (y \<cdot>v \<rho>\<^sub>1_inv) \<gamma>\<^sub>1"
        unfolding \<gamma>_def
        using base.comp_subst_iff
        by (simp add: \<rho>\<^sub>1 \<rho>\<^sub>2 base_exists_nonground finite_vars finite_vars' rename_variables)

      then show "x \<cdot>v \<gamma>\<^sub>1 = x \<cdot>v \<rho>\<^sub>1 \<odot> \<gamma>"
        by (metis \<rho>\<^sub>1_inv base.comp_subst_iff base.left_neutral y)
    qed

    then show "\<forall>x \<in> vars expr. x \<cdot>v \<gamma>\<^sub>1 = x \<cdot>v \<rho>\<^sub>1 \<odot> \<gamma>"
      by auto
  next

    have "\<forall>x\<in> vars expr'. x \<cdot>v \<gamma>\<^sub>2 = x \<cdot>v \<rho>\<^sub>2 \<odot> \<gamma>"
    proof (intro ballI)
      fix x
      assume x_in_vars: "x \<in> vars expr'"

      obtain y where y: "x \<cdot>v \<rho>\<^sub>2 = y \<cdot>v id_subst"
        using obtain_renamed_variable[OF exists_nonground \<rho>\<^sub>2] .

      then have "y \<in> vars (expr' \<cdot> \<rho>\<^sub>2)"
        using x_in_vars \<rho>\<^sub>2 rename_variables_id_subst base_exists_nonground
        by (metis base.inj_id_subst imageI inj_image_mem_iff)

      then have "y \<cdot>v \<gamma> = base_subst (y \<cdot>v \<rho>\<^sub>2_inv) \<gamma>\<^sub>2"
        unfolding \<gamma>_def base.comp_subst_iff
        using rename_apart base_exists_nonground \<rho>\<^sub>1 \<rho>\<^sub>2 finite_vars finite_vars' rename_variables
        by auto

      then show "x \<cdot>v \<gamma>\<^sub>2 = x \<cdot>v \<rho>\<^sub>2 \<odot> \<gamma>"
        by (metis \<rho>\<^sub>2_inv base.comp_subst_iff base.left_neutral y)
    qed

    then show "\<forall>x \<in> vars expr'. x \<cdot>v \<gamma>\<^sub>2 = x \<cdot>v \<rho>\<^sub>2 \<odot> \<gamma>"
      by auto

  next

    have "expr \<cdot> \<rho>\<^sub>1 \<cdot> \<gamma> = expr \<cdot> \<rho>\<^sub>1  \<cdot> \<rho>\<^sub>1_inv \<odot> \<gamma>\<^sub>1"
      unfolding \<gamma>_def
      by (rule subst_updates_compat) (simp add: \<rho>\<^sub>1 \<rho>\<^sub>2 finite_vars finite_vars' rename_variables)      

    then show "expr \<cdot> \<gamma>\<^sub>1 = expr \<cdot> \<rho>\<^sub>1 \<odot> \<gamma>"
      using \<rho>\<^sub>1_inv subst_id_subst
      by force

    have "expr' \<cdot> \<rho>\<^sub>2 \<cdot> \<gamma> = expr' \<cdot> \<rho>\<^sub>2  \<cdot> \<rho>\<^sub>2_inv \<odot> \<gamma>\<^sub>2"
      unfolding \<gamma>_def
      by 
        (rule subst_updates_compat)
        (use \<rho>\<^sub>1 \<rho>\<^sub>2 finite_vars finite_vars' rename_apart rename_variables in auto)

    then show "expr' \<cdot> \<gamma>\<^sub>2 = expr' \<cdot> \<rho>\<^sub>2 \<odot> \<gamma>"
      using \<rho>\<^sub>2_inv subst_id_subst
      by force
  qed
next
  case base_only_ground: False

  then have only_ground: "\<not>exists_nonground"
    unfolding exists_nonground_iff_base_exists_nonground .

  obtain \<rho> where \<rho>: "base.is_renaming \<rho>"
    using base.exists_renaming
    by auto

  show ?thesis
    by (rule that[OF \<rho> \<rho>]) (use no_vars_if_is_ground only_ground in auto)
qed

lemma obtain_merged_grounding':
  fixes \<V>\<^sub>1 \<V>\<^sub>2 :: "('v, 'ty) var_types"
  assumes
    typed_\<gamma>\<^sub>1: "base.type_preserving_on (vars expr) \<V>\<^sub>1 \<gamma>\<^sub>1" and
    typed_\<gamma>\<^sub>2: "base.type_preserving_on (vars expr') \<V>\<^sub>2 \<gamma>\<^sub>2" and
    expr_grounding: "is_ground (expr \<cdot> \<gamma>\<^sub>1)" and
    expr'_grounding: "is_ground (expr' \<cdot> \<gamma>\<^sub>2)" and
    \<V>\<^sub>1: "infinite_variables_per_type_on (vars expr) \<V>\<^sub>1" and
    finite_vars: "finite (vars expr')" "finite (vars expr)"
  obtains \<rho>\<^sub>1 \<rho>\<^sub>2 \<gamma>  where
    "base.is_renaming \<rho>\<^sub>1"
    "base.is_renaming \<rho>\<^sub>2"
    "vars (expr \<cdot> \<rho>\<^sub>1) \<inter> vars (expr' \<cdot> \<rho>\<^sub>2) = {}"
    "base.type_preserving_on (vars expr) \<V>\<^sub>1 \<rho>\<^sub>1"
    "base.type_preserving_on (vars expr') \<V>\<^sub>2 \<rho>\<^sub>2"
    "\<forall>x \<in> vars expr. x \<cdot>v \<gamma>\<^sub>1 = x \<cdot>v \<rho>\<^sub>1 \<odot> \<gamma>"
    "\<forall>x \<in> vars expr'. x \<cdot>v \<gamma>\<^sub>2 = x \<cdot>v \<rho>\<^sub>2 \<odot> \<gamma>"
    "expr \<cdot> \<gamma>\<^sub>1 = expr \<cdot> \<rho>\<^sub>1 \<odot> \<gamma>"
    "expr' \<cdot> \<gamma>\<^sub>2 = expr' \<cdot> \<rho>\<^sub>2 \<odot> \<gamma>"
  using obtain_merged_grounding[OF typed_\<gamma>\<^sub>2 typed_\<gamma>\<^sub>1 expr'_grounding expr_grounding \<V>\<^sub>1 finite_vars]
  by (smt (verit, ccfv_threshold) inf_commute)

end

sublocale base_typed_renaming \<subseteq>
  based_typed_renaming where
  base_vars = vars and base_subst = subst and base_is_ground = is_ground and
  base_welltyped = welltyped
  by unfold_locales

locale type_preserving_imgu = base_typed_substitution +
  assumes
    exists_type_preserving_imgu: 
    "\<And>\<V> \<upsilon> expr expr'. type_preserving_unifier \<V> \<upsilon> expr expr' \<Longrightarrow>
      \<exists>\<mu>. type_preserving \<V> \<mu> \<and> is_imgu \<mu> {{expr, expr'}}"
begin

lemma obtain_type_preserving_imgu:
  fixes \<upsilon> 
  assumes "type_preserving_unifier \<V> \<upsilon> expr expr'"
  obtains \<mu>
  where "type_preserving \<V> \<mu>" "is_imgu \<mu> {{expr, expr'}}"
  using exists_type_preserving_imgu[OF assms] UNIV_I
  by metis

lemma obtain_type_preserving_on_imgu:
  fixes \<upsilon> 
  assumes "type_preserving_unifier \<V> \<upsilon> expr expr'"
  obtains \<mu>
  where "type_preserving_on X \<V> \<mu>" "is_imgu \<mu> {{expr, expr'}}"
  using exists_type_preserving_imgu[OF assms] UNIV_I
  by metis

end

end
