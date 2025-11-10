theory Based_Substitution \<^marker>\<open>contributor \<open>Balazs Toth\<close>\<close> 
  imports Substitution
begin

section \<open>Substitutions on base expressions\<close>

locale base_substitution = substitution where vars = vars and apply_subst = apply_subst
  for vars :: "'base \<Rightarrow> 'v set" and apply_subst :: "'v \<Rightarrow> 'subst \<Rightarrow> 'base" (infixl \<open>\<cdot>v\<close> 69) +
  assumes 
    vars_id_subst [simp]: "\<And>x. vars (x \<cdot>v id_subst) = {x}" and
    comp_subst_iff: "\<And>\<sigma> \<sigma>' x. x \<cdot>v \<sigma> \<odot> \<sigma>' = subst (x \<cdot>v \<sigma>) \<sigma>'" and
    base_vars_subst: "\<And>expr \<rho>. vars (expr \<cdot> \<rho>) = \<Union> (vars ` var_subst \<rho> ` vars expr)"

locale based_substitution =
  substitution where vars = vars and apply_subst = "apply_subst :: 'v \<Rightarrow> 'subst \<Rightarrow> 'base" +
  base: base_substitution where subst = base_subst and vars = base_vars 
for
  base_subst :: "'base \<Rightarrow> 'subst \<Rightarrow> 'base" and
  base_vars :: "'base \<Rightarrow> 'v set" and
  vars :: "'expr \<Rightarrow> 'v set"  +
assumes
  ground_subst_iff_base_ground_subst [simp]: "\<And>\<gamma>. is_ground_subst \<gamma> \<longleftrightarrow> base.is_ground_subst \<gamma>" and
  vars_subst: "\<And>expr \<rho>. vars (expr \<cdot> \<rho>) = \<Union> (base_vars ` var_subst \<rho> ` vars expr)"
begin

lemma id_subst_subst [simp]: "base_subst (x \<cdot>v id_subst) \<sigma> = x \<cdot>v \<sigma>"
  by (metis base.comp_subst_iff left_neutral)

lemma vars_id_subst_update: "vars (expr \<cdot> id_subst\<lbrakk>x := b\<rbrakk>) \<subseteq> vars expr \<union> base_vars b"
  unfolding fun_upd_def vars_subst
  using subst_update
  by (smt (verit, del_insts) SUP_least UnCI base.vars_id_subst image_iff singletonD subsetI)

lemma is_grounding_iff_vars_grounded:
  "is_ground (expr \<cdot> \<gamma>) \<longleftrightarrow> (\<forall>x \<in> vars expr. base.is_ground (x \<cdot>v \<gamma>))"
  using vars_subst
  by auto

lemma variable_grounding:
  assumes "is_ground (expr \<cdot> \<gamma>)" "x \<in> vars expr"
  shows "base.is_ground (x \<cdot>v \<gamma>)"
  using assms is_grounding_iff_vars_grounded
  by blast

definition range_vars :: "'subst \<Rightarrow> 'v set" where
  "range_vars \<sigma> = \<Union>(base_vars ` subst_range \<sigma>)"

lemma vars_subst_subset: "vars (expr \<cdot> \<sigma>) \<subseteq> (vars expr - subst_domain \<sigma>) \<union> range_vars \<sigma>"
  unfolding subst_domain_def range_vars_def vars_subst
  using base.vars_id_subst
  by (smt (verit, del_insts) Diff_iff UN_iff UnCI image_iff mem_Collect_eq singletonD subsetI)

lemma ground_subst_update [simp]:
  assumes "base.is_ground update" "is_ground (expr \<cdot> \<gamma>)"
  shows "is_ground (expr \<cdot> \<gamma>\<lbrakk>x := update\<rbrakk>)"
  using assms is_grounding_iff_vars_grounded
  by (metis subst_update)

end

context base_substitution
begin

sublocale based_substitution
  where base_subst = subst and base_vars = vars
  by unfold_locales (simp_all add: base_vars_subst)

declare ground_subst_iff_base_ground_subst [simp del]

end

hide_fact base_substitution.base_vars_subst


section \<open>Properties of substitutions on base expressions\<close>

locale base_exists_ground_subst = 
  base_substitution where
    vars = "vars :: 'base \<Rightarrow> 'v set" and apply_subst = "apply_subst  :: 'v \<Rightarrow> 'subst \<Rightarrow> 'base" +
  subst_updates + 
  assumes
    base_ground_exists: "\<exists>expr. is_ground expr"
begin

lemma redundant_subst_updates [simp]:
  assumes "\<And>x. x \<in> vars expr \<Longrightarrow> update x = None"
  shows "expr \<cdot> subst_updates \<sigma> update = expr \<cdot> \<sigma>"
proof (rule subst_eq)
  fix x
  assume "x \<in> vars expr"

  then have "update x = None"
    using assms
    by metis

  then show "x \<cdot>v subst_updates \<sigma> update = x \<cdot>v \<sigma>"
    by simp
qed

lemma redundant_subst_updates_vars_set [simp]:
  assumes "\<And>x. x \<in> X \<Longrightarrow> update x = None"
  shows "(\<lambda>x. x \<cdot>v subst_updates \<sigma> update) ` X = (\<lambda>x. x \<cdot>v \<sigma>) ` X"
  using assms subst_updates 
  by auto

lemma redundant_subst_updates_vars_image [simp]:
  assumes "\<And>x. x \<in> \<Union>(vars ` X) \<Longrightarrow> update x = None"
  shows "(\<lambda>expr. expr \<cdot> subst_updates \<sigma> update) ` X = (\<lambda>expr. expr \<cdot> \<sigma>) ` X"
  using assms subst_updates 
  by (meson UN_I image_cong redundant_subst_updates)

sublocale exists_ground_subst
proof unfold_locales
   obtain b where is_ground: "is_ground b"
    using base_ground_exists 
    by blast

  define \<gamma> :: 'subst where
    "\<And>x. \<gamma> \<equiv> subst_updates id_subst (\<lambda>_. Some b)"

  show "\<exists>\<gamma>. is_ground_subst \<gamma>"
  proof (rule exI)
    show "is_ground_subst \<gamma>"
      unfolding is_ground_subst_def \<gamma>_def
      by (simp add: is_ground is_grounding_iff_vars_grounded)
  qed
qed

end

locale base_exists_non_ident_subst =
  base_substitution where vars = vars + 
  finite_variables where vars = vars +
  infinite_variables where vars = vars +
  all_subst_ident_iff_ground where vars = vars
  for vars :: "'expr \<Rightarrow> 'v set" 
begin

sublocale exists_non_ident_subst
proof unfold_locales
  fix expr and S :: "'expr set"
  assume finite_S: "finite S" and vars_not_empty: "vars expr \<noteq> {}"

  obtain x where x: "x \<in> vars expr"
    using vars_not_empty
    by blast

  have "finite (vars_set S)"
    using finite_S finite_vars
    unfolding vars_set_def
    by blast

  obtain y where y: "y \<notin> vars expr" "y \<notin> vars_set S"
  proof -

    have "finite (vars_set S)"
      using finite_S finite_vars
      unfolding vars_set_def
      by blast

    then have "finite (vars expr \<union> vars_set S)"
      using finite_vars
      by simp

    then show ?thesis
      using that infinite_vars finite_vars
      by (meson UnCI ex_new_if_finite)
  qed

  define \<sigma> where "\<sigma> \<equiv> id_subst\<lbrakk>x := y \<cdot>v id_subst\<rbrakk>"

  show "\<exists>\<sigma>. expr \<cdot> \<sigma> \<noteq> expr \<and> expr \<cdot> \<sigma> \<notin> S"
  proof (intro exI conjI)

    have y_in_expr_\<sigma>: "y \<in> vars (expr \<cdot> \<sigma>)"
      unfolding \<sigma>_def
      using x vars_subst
      by fastforce

    then show "expr \<cdot> \<sigma> \<noteq> expr"
      using y
      by metis

    show "expr \<cdot> \<sigma> \<notin> S"
      using y_in_expr_\<sigma> y(2)
      unfolding vars_set_def
      by auto
  qed
qed

end

locale variables_in_base_imgu = based_substitution +
  assumes variables_in_base_imgu:
    "\<And>expr \<mu> XX.
        base.is_imgu \<mu> XX \<Longrightarrow> finite XX \<Longrightarrow> \<forall>X \<in> XX. finite X \<Longrightarrow>
        vars (expr \<cdot> \<mu>) \<subseteq> vars expr \<union> (\<Union>(base_vars ` \<Union> XX))"

locale base_variables_in_base_imgu =
  base_substitution where vars = "vars :: 'expr \<Rightarrow> 'v set" and
  subst_update = "subst_update :: 'subst \<Rightarrow> 'v \<Rightarrow> 'expr \<Rightarrow> 'subst" + 
  finite_variables +
  infinite_variables +
assumes
  not_back_to_id_subst: "\<And>expr \<sigma>. \<exists>x. expr \<cdot> \<sigma> = x \<cdot>v id_subst \<Longrightarrow> \<exists>x. expr = x \<cdot>v id_subst"
begin

lemma imgu_subst_domain_subset:
  assumes imgu: "is_imgu \<mu> XX" and finite_X: "\<forall>X\<in>XX. finite X" and finite_XX: "finite XX"
  shows "subst_domain \<mu> \<subseteq> \<Union> (vars ` \<Union> XX)"
proof (intro Set.subsetI)
  fix x
  assume "x \<in> subst_domain \<mu>"

  then have x_\<mu>: "x \<cdot>v \<mu> \<noteq> x \<cdot>v id_subst"
    unfolding subst_domain_def
    by auto

  show "x \<in> \<Union> (vars ` \<Union> XX)"
  proof (rule ccontr)
    assume x: "x \<notin> \<Union> (vars ` \<Union> XX)"

    define \<tau> where 
      "\<tau> \<equiv> \<mu>\<lbrakk>x := x \<cdot>v id_subst\<rbrakk>"

    have "x \<cdot>v \<mu> \<odot> \<tau> \<noteq> x \<cdot>v \<tau>"
    proof (cases "\<exists>y. x \<cdot>v \<mu> = y \<cdot>v id_subst")
      case True

      then obtain y where y: "x \<cdot>v \<mu> = y \<cdot>v id_subst"
        by auto

      then have "x \<noteq> y"
        using x_\<mu>
        by blast

      moreover have "y \<cdot>v \<mu> \<noteq> x \<cdot>v id_subst"
      proof (rule notI)
        assume "y \<cdot>v \<mu> = x \<cdot>v id_subst"

        then show False
          using imgu x_\<mu>
          unfolding is_imgu_def
          by (metis comp_subst_iff id_subst_subst)
      qed

      ultimately show ?thesis
        unfolding comp_subst_iff y \<tau>_def
        by auto
    next
      case False

      then show ?thesis
        unfolding \<tau>_def comp_subst_iff
        using not_back_to_id_subst
        by (metis subst_update(1))
    qed

    then have "\<mu> \<odot> \<tau> \<noteq> \<tau>"
      by metis

    moreover have "is_unifier_set \<tau> XX"
      using imgu is_imgu_def
      unfolding \<tau>_def is_unifier_set_def is_unifier_def subst_set_def
      using x
      by auto

    ultimately show False
      using imgu
      unfolding is_imgu_def
      by auto
  qed
qed

lemma imgu_subst_domain_finite:
  assumes imgu: "is_imgu \<mu> XX" and finite_X: "\<forall>X\<in>XX. finite X" and finite_XX: "finite XX"
  shows "finite (subst_domain \<mu>)"
  using imgu_subst_domain_subset[OF assms(1-3)] finite_XX finite_X finite_vars
  by (simp add: finite_subset)

lemma imgu_range_vars_finite:
  assumes imgu: "is_imgu \<mu> XX" and finite_X: "\<forall>X\<in>XX. finite X" and finite_XX: "finite XX"
  shows "finite (range_vars \<mu>)"
  using imgu_subst_domain_finite[OF assms] finite_vars
  unfolding range_vars_def
  by blast

lemma imgu_range_vars_vars_subset:
  assumes imgu: "is_imgu \<mu> XX" and finite_X: "\<forall>X\<in>XX. finite X" and finite_XX: "finite XX"
  shows "\<Union>(vars ` expr_subst \<mu> ` \<Union> XX) \<subseteq> \<Union> (vars ` \<Union> XX)"
proof (intro Set.subsetI)
  fix y
  assume y: "y \<in> \<Union> (vars ` expr_subst \<mu> ` \<Union> XX)"

  then obtain x where
    x: "x \<in> \<Union>(vars ` \<Union> XX)" "y \<in> vars (x \<cdot>v \<mu>)"
    using vars_subst
    by auto

  show "y \<in> \<Union> (vars ` \<Union> XX)"
  proof (rule ccontr)
    assume y': "y \<notin> \<Union> (vars ` \<Union> XX)"

    then have x_neq_y: "x \<noteq> y"
      using x
      by auto

    obtain z where z: "z \<notin> range_vars \<mu>" "z \<notin> subst_domain \<mu>"
      using 
        imgu_subst_domain_finite[OF assms]
        imgu_range_vars_finite[OF assms]
        infinite_vars
      by (metis Diff_iff finite_Diff2 infinite_super subsetI)

    define \<tau> where
      "\<tau> \<equiv> id_subst\<lbrakk>y := z \<cdot>v id_subst\<rbrakk> \<odot> \<mu>"

    have "x \<cdot>v \<mu> \<odot> \<tau> \<noteq> x \<cdot>v \<tau>"
    proof -

      have "z \<notin> vars (x \<cdot>v \<mu>)"
        using z(1) x(2) x_neq_y
        unfolding range_vars_def subst_domain_def
        by force

      moreover have "z \<in> vars (x \<cdot>v \<mu> \<cdot> id_subst\<lbrakk>y := z \<cdot>v id_subst\<rbrakk>)"
        using x(2) vars_subst
        by fastforce

      then have "z \<in> vars (x \<cdot>v \<mu> \<cdot> id_subst\<lbrakk>y := z \<cdot>v id_subst\<rbrakk> \<cdot> \<mu>)"
        using z(2) vars_subst
        unfolding range_vars_def subst_domain_def
        by fastforce

      ultimately show ?thesis
        using x_neq_y
        unfolding \<tau>_def comp_subst_iff
        by auto
    qed

    then have "\<mu> \<odot> \<tau> \<noteq> \<tau>"
      by metis

    moreover have "is_unifier_set \<tau> XX"
      using imgu is_imgu_def
      unfolding \<tau>_def is_unifier_set_def is_unifier_def subst_set_def
      using y'
      by auto

    ultimately show False
      using imgu
      unfolding is_imgu_def
      by auto
  qed
qed

lemma range_vars_subset_if_is_imgu:
  assumes "is_imgu \<mu> XX" "\<forall>X\<in>XX. finite X" "finite XX"
  shows "range_vars \<mu> \<subseteq> (\<Union>expr\<in>\<Union>XX. vars expr)"
proof -
  have "range_vars \<mu> = (\<Union>x \<in> subst_domain \<mu>. vars (x \<cdot>v \<mu>))"
    by (simp add: range_vars_def)

  also have "\<dots> \<subseteq> (\<Union>(vars ` (\<lambda>expr. expr \<cdot> \<mu>) ` \<Union> XX))"
    using imgu_subst_domain_subset[OF assms] subsetD vars_subst 
    by fastforce

  also have "\<dots> \<subseteq> (\<Union>expr\<in>\<Union>XX. vars expr)"
    using imgu_range_vars_vars_subset[OF assms] .

  finally show ?thesis .
qed

sublocale variables_in_base_imgu where 
  base_subst = subst and base_vars = vars
  using range_vars_subset_if_is_imgu vars_subst_subset
  by unfold_locales fastforce

end

locale range_vars_subset_if_is_imgu = base_substitution +
  assumes range_vars_subset_if_is_imgu: 
    "\<And>\<mu> XX. is_imgu \<mu> XX \<Longrightarrow> \<forall>X\<in>XX. finite X \<Longrightarrow> finite XX \<Longrightarrow>
        range_vars \<mu> \<subseteq> (\<Union>expr\<in>\<Union>XX. vars expr)"
begin

sublocale variables_in_base_imgu where 
  base_subst = subst and base_vars = vars
  using range_vars_subset_if_is_imgu vars_subst_subset
  by unfold_locales fastforce

end

end
