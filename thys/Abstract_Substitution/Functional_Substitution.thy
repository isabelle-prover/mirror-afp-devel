theory Functional_Substitution \<^marker>\<open>contributor \<open>Balazs Toth\<close>\<close>
  imports
    Substitution
    "HOL-Library.FSet"
begin

locale functional_substitution = substitution where
  subst = subst and is_ground = "\<lambda>expr. vars expr = {}"
  for
    subst :: "'expr \<Rightarrow> ('var \<Rightarrow> 'base) \<Rightarrow> 'expr" (infixl "\<cdot>" 69) and
    vars :: "'expr \<Rightarrow> 'var set" +
  assumes
    (* TODO: Interesting that not both directions are required *)
    subst_eq: "\<And>expr \<sigma> \<tau>. (\<And>x. x \<in> vars expr \<Longrightarrow> \<sigma> x = \<tau> x) \<Longrightarrow> expr \<cdot> \<sigma> = expr \<cdot> \<tau>" 
begin

abbreviation is_ground where "is_ground expr \<equiv> vars expr = {}"

definition vars_set :: "'expr set \<Rightarrow> 'var set" where
  "vars_set exprs \<equiv> \<Union>expr \<in> exprs. vars expr"

lemma subst_reduntant_upd [simp]:
  assumes "var \<notin> vars expr"
  shows "expr \<cdot> \<sigma>(var := update) = expr \<cdot> \<sigma>"
  using assms subst_eq
  by fastforce

lemma subst_reduntant_if [simp]:
  assumes "vars expr \<subseteq> vars'"
  shows "expr \<cdot> (\<lambda>var. if var \<in> vars' then \<sigma> var else \<sigma>' var) = expr \<cdot> \<sigma>"
  using assms
  by (smt (verit, best) subset_eq subst_eq)

lemma subst_reduntant_if' [simp]:
  assumes "vars expr \<inter> vars' = {}"
  shows "expr \<cdot> (\<lambda>var. if var \<in> vars' then \<sigma>' var else \<sigma> var) = expr \<cdot> \<sigma>"
  using assms subst_eq
  unfolding disjoint_iff
  by presburger

lemma subst_cannot_unground:
  assumes "\<not>is_ground (expr \<cdot> \<sigma>)"
  shows "\<not>is_ground expr"
  using assms by force

definition subst_domain :: "('var \<Rightarrow> 'base) \<Rightarrow> 'var set" where
  "subst_domain \<sigma> = {x. \<sigma> x \<noteq> id_subst x}"

abbreviation subst_range :: "('var \<Rightarrow> 'base) \<Rightarrow> 'base set" where
  "subst_range \<sigma> \<equiv> \<sigma> ` subst_domain \<sigma>"

lemma subst_inv:
  assumes "\<sigma> \<odot> \<sigma>_inv = id_subst" 
  shows "expr \<cdot> \<sigma> \<cdot> \<sigma>_inv = expr"
  using assms
  by (metis subst_comp_subst subst_id_subst)

(* TODO: Move *)
definition rename where
  "is_renaming \<rho> \<Longrightarrow> rename \<rho> x \<equiv> SOME x'. \<rho> x = id_subst x'"

lemma is_unifier_two: "is_unifier \<upsilon> {expr, expr'} \<Longrightarrow> expr \<cdot> \<upsilon> = expr' \<cdot> \<upsilon>"
  unfolding is_unifier_def
  using insertCI 
  by fastforce

end

locale all_subst_ident_iff_ground =
  functional_substitution +
  assumes
    all_subst_ident_iff_ground: "\<And>expr. is_ground expr \<longleftrightarrow> (\<forall>\<sigma>. subst expr \<sigma> = expr)" and
    exists_non_ident_subst:
      "\<And>expr S. finite S \<Longrightarrow> \<not>is_ground expr \<Longrightarrow> \<exists>\<sigma>. subst expr \<sigma> \<noteq> expr \<and> subst expr \<sigma> \<notin> S"

locale finite_variables = functional_substitution where vars = vars
  for vars :: "'expr \<Rightarrow> 'var set" +
  assumes finite_vars [intro]: "\<And>expr. finite (vars expr)"
begin

abbreviation finite_vars :: "'expr \<Rightarrow> 'var fset" where
  "finite_vars expr \<equiv> Abs_fset (vars expr)"

lemma fset_finite_vars [simp]: "fset (finite_vars expr) = vars expr"
  using Abs_fset_inverse finite_vars
  by blast

end

locale renaming_variables = functional_substitution +
  assumes
    is_renaming_iff: "\<And>\<rho>. is_renaming \<rho> \<longleftrightarrow> inj \<rho> \<and> (\<forall>x. \<exists>x'. \<rho> x = id_subst x')" and
    rename_variables: "\<And>expr \<rho>. is_renaming \<rho> \<Longrightarrow> vars (expr \<cdot> \<rho>) = rename \<rho> ` (vars expr)"
begin

lemma renaming_range_id_subst:
  assumes "is_renaming \<rho>"
  shows "\<rho> x \<in> range id_subst"
  using assms
  unfolding is_renaming_iff
  by auto

lemma obtain_renamed_variable:
  assumes "is_renaming \<rho>"
  obtains x' where "\<rho> x = id_subst x'"
  using renaming_range_id_subst[OF assms]
  by auto

lemma id_subst_rename [simp]:
  assumes "is_renaming \<rho>"
  shows "id_subst (rename \<rho> x) = \<rho> x"
  unfolding rename_def[OF assms]
  using obtain_renamed_variable[OF assms]
  by (metis (mono_tags, lifting) someI)

lemma rename_variables_id_subst: 
  assumes "is_renaming \<rho>" 
  shows "id_subst ` vars (expr \<cdot> \<rho>) = \<rho> ` (vars expr)"
  using rename_variables[OF assms] id_subst_rename[OF assms]
  by (metis (no_types, lifting) image_cong image_image)

lemma surj_inv_renaming:
  assumes "is_renaming \<rho>"
  shows "surj (\<lambda>x. inv \<rho> (id_subst x))"
  using assms inv_f_f
  unfolding is_renaming_iff surj_def
  by metis

lemma renaming_range:
  assumes "is_renaming \<rho>" "x \<in> vars (expr \<cdot> \<rho>)"
  shows "id_subst x \<in> range \<rho>"
  using rename_variables_id_subst[OF assms(1)] assms(2)
  by fastforce

lemma renaming_inv_into:
  assumes "is_renaming \<rho>" "x \<in> vars (expr \<cdot> \<rho>)"
  shows "\<rho> (inv \<rho> (id_subst x)) = id_subst x"
  using f_inv_into_f[OF renaming_range[OF assms]].

lemma inv_renaming:
  assumes "is_renaming \<rho>"
  shows "inv \<rho> (\<rho> x) = x"
  using assms
  unfolding is_renaming_iff
  by simp

lemma renaming_inv_in_vars:
  assumes "is_renaming \<rho>" "x \<in> vars (expr \<cdot> \<rho>)"
  shows "inv \<rho> (id_subst x) \<in> vars expr"
  using assms rename_variables_id_subst[OF assms(1)]
  by (metis image_eqI image_inv_f_f is_renaming_iff)

lemma inj_id_subst: "inj id_subst"
  using is_renaming_id_subst is_renaming_iff
  by blast

end

locale grounding = functional_substitution where vars = vars and id_subst = id_subst
  for vars :: "'expr \<Rightarrow> 'var set" and id_subst :: "'var \<Rightarrow> 'base" +
  fixes to_ground :: "'expr \<Rightarrow> 'expr\<^sub>G" and from_ground :: "'expr\<^sub>G \<Rightarrow> 'expr"
  assumes
    range_from_ground_iff_is_ground: "{expr. is_ground expr} = range from_ground" and
    from_ground_inverse [simp]: "\<And>expr\<^sub>G. to_ground (from_ground expr\<^sub>G) = expr\<^sub>G"
begin

definition ground_instances' ::"'expr \<Rightarrow> 'expr\<^sub>G set" where
  "ground_instances' expr = { to_ground (expr \<cdot> \<gamma>) | \<gamma>. is_ground (expr \<cdot> \<gamma>) }"

lemma ground_instances'_eq_ground_instances: 
  "ground_instances' expr = (to_ground ` ground_instances expr)"
  unfolding ground_instances'_def ground_instances_def generalizes_def instances_def 
  by blast

lemma to_ground_from_ground_id [simp]: "to_ground \<circ> from_ground = id"
  using from_ground_inverse
  by auto

lemma surj_to_ground: "surj to_ground"
  using from_ground_inverse
  by (metis surj_def)

lemma inj_from_ground: "inj_on from_ground domain\<^sub>G"
  by (metis from_ground_inverse inj_on_inverseI)

lemma inj_on_to_ground: "inj_on to_ground (from_ground ` domain\<^sub>G)"
  unfolding inj_on_def
  by simp

lemma bij_betw_to_ground: "bij_betw to_ground (from_ground ` domain\<^sub>G) domain\<^sub>G"
  by (smt (verit, best) bij_betwI' from_ground_inverse image_iff)

lemma bij_betw_from_ground: "bij_betw from_ground domain\<^sub>G (from_ground ` domain\<^sub>G)"
  by (simp add: bij_betw_def inj_from_ground)

lemma ground_is_ground [simp, intro]: "is_ground (from_ground expr\<^sub>G)"
  using range_from_ground_iff_is_ground
  by blast

lemma is_ground_iff_range_from_ground: "is_ground expr \<longleftrightarrow> expr \<in> range from_ground"
  using range_from_ground_iff_is_ground
  by auto

lemma to_ground_inverse [simp]:
  assumes "is_ground expr"
  shows "from_ground (to_ground expr) = expr"
  using inj_on_to_ground from_ground_inverse is_ground_iff_range_from_ground assms
  unfolding inj_on_def
  by blast

corollary obtain_grounding:
  assumes "is_ground expr"
  obtains expr\<^sub>G where "from_ground expr\<^sub>G = expr"
  using to_ground_inverse assms
  by blast

lemma from_ground_eq [simp]:
  "from_ground expr = from_ground expr' \<longleftrightarrow> expr = expr'"
  by (metis from_ground_inverse)

lemma to_ground_eq [simp]:
  assumes "is_ground expr" "is_ground expr'"
  shows "to_ground expr = to_ground expr' \<longleftrightarrow> expr = expr'"
  using assms obtain_grounding
  by fastforce

end

locale base_functional_substitution = functional_substitution
  where id_subst = id_subst and vars = vars
  for id_subst :: "'var \<Rightarrow> 'expr" and vars :: "'expr \<Rightarrow> 'var set" +
  assumes
    vars_subst_vars: "\<And>expr \<rho>. vars (expr \<cdot> \<rho>) = \<Union> (vars ` \<rho> ` vars expr)" and
    base_ground_exists: "\<exists>expr. is_ground expr" and
    vars_id_subst [simp]: "\<And>x. vars (id_subst x) = {x}" and
    comp_subst_iff: "\<And>\<sigma> \<sigma>' x. (\<sigma> \<odot> \<sigma>') x = \<sigma> x \<cdot> \<sigma>'"
begin

lemma id_subst_subst [simp]: "id_subst x \<cdot> \<sigma> = \<sigma> x"
  by (metis comp_subst_iff left_neutral)

end

locale based_functional_substitution =
  base: base_functional_substitution where subst = base_subst and vars = base_vars +
  functional_substitution where vars = vars
for
  base_subst :: "'base \<Rightarrow> ('var \<Rightarrow> 'base) \<Rightarrow> 'base" and
  base_vars and
  vars :: "'expr \<Rightarrow> 'var set" +
assumes
  ground_subst_iff_base_ground_subst [simp]: "\<And>\<gamma>. is_ground_subst \<gamma> \<longleftrightarrow> base.is_ground_subst \<gamma>" and
  vars_subst: "\<And>expr \<rho>.  vars (expr \<cdot> \<rho>) = \<Union> (base_vars ` \<rho> ` vars expr)"
begin

lemma vars_id_subst_update: "vars (expr \<cdot> id_subst(x := b)) \<subseteq> vars expr \<union> base_vars b"
  unfolding fun_upd_def vars_subst
  by (auto simp: base.vars_id_subst)

lemma is_grounding_iff_vars_grounded:
  "is_ground (expr \<cdot> \<gamma>) \<longleftrightarrow> (\<forall>var \<in> vars expr. base.is_ground (\<gamma> var))"
  using vars_subst
  by auto

lemma obtain_ground_subst:
  obtains \<gamma>
  where "is_ground_subst \<gamma>"
  unfolding ground_subst_iff_base_ground_subst base.is_ground_subst_def
  using base.base_ground_exists base.vars_subst_vars
  by (meson is_ground_subst_def is_grounding_iff_vars_grounded that)

lemma exists_ground_subst [intro]: "\<exists>\<gamma>. is_ground_subst \<gamma>"
  by (metis obtain_ground_subst)

lemma ground_subst_extension:
  assumes "is_ground (expr \<cdot> \<gamma>)"
  obtains \<gamma>'
  where "expr \<cdot> \<gamma> = expr \<cdot> \<gamma>'" and "is_ground_subst \<gamma>'"
  using obtain_ground_subst assms
  by (metis all_subst_ident_if_ground is_ground_subst_comp_right subst_comp_subst)

lemma ground_subst_extension':
  assumes "is_ground (expr \<cdot> \<gamma>)"
  obtains \<gamma>'
  where "expr \<cdot> \<gamma> = expr \<cdot> \<gamma>'" and "base.is_ground_subst \<gamma>'"
  using ground_subst_extension assms
  by auto

lemma ground_subst_update [simp]:
  assumes "base.is_ground update" "is_ground (expr \<cdot> \<gamma>)"
  shows "is_ground (expr \<cdot> \<gamma>(var := update))"
  using assms is_grounding_iff_vars_grounded
  by auto

lemma ground_exists: "\<exists>expr. is_ground expr"
  using base.base_ground_exists
  by (meson is_grounding_iff_vars_grounded)

lemma variable_grounding:
  assumes "is_ground (expr \<cdot> \<gamma>)" "var \<in> vars expr"
  shows "base.is_ground (\<gamma> var)"
  using assms is_grounding_iff_vars_grounded
  by blast

definition range_vars :: "('var \<Rightarrow> 'base) \<Rightarrow> 'var set" where
  "range_vars \<sigma> = \<Union>(base_vars ` subst_range \<sigma>)"

lemma vars_subst_subset: "vars (expr \<cdot> \<sigma>) \<subseteq> (vars expr - subst_domain \<sigma>) \<union> range_vars \<sigma>"
  unfolding subst_domain_def range_vars_def vars_subst
  using base.vars_id_subst
  by (smt (verit, del_insts) Diff_iff UN_iff UnCI image_iff mem_Collect_eq singletonD subsetI)

end

locale variables_in_base_imgu = based_functional_substitution +
  assumes variables_in_base_imgu:
    "\<And>expr \<mu> unifications.
        base.is_imgu \<mu> unifications \<Longrightarrow>
        finite unifications \<Longrightarrow>
        \<forall>unification \<in> unifications. finite unification \<Longrightarrow>
        vars (expr \<cdot> \<mu>) \<subseteq> vars expr \<union> (\<Union>(base_vars ` \<Union> unifications))"

context base_functional_substitution
begin

sublocale based_functional_substitution
  where base_subst = subst and base_vars = vars
  by unfold_locales (simp_all add: vars_subst_vars)

declare ground_subst_iff_base_ground_subst [simp del]

end

hide_fact base_functional_substitution.base_ground_exists
hide_fact base_functional_substitution.vars_subst_vars

locale exists_imgu = base_functional_substitution +
  assumes
    exists_imgu: "\<And>\<upsilon> expr expr'. expr \<cdot> \<upsilon> = expr' \<cdot> \<upsilon> \<Longrightarrow> \<exists>\<mu>. \<upsilon> = \<mu> \<odot> \<upsilon> \<and> is_imgu \<mu> {{expr, expr'}}"

end
