theory Based_Substitution \<^marker>\<open>contributor \<open>Balazs Toth\<close>\<close> 
  imports Substitution
begin             

section \<open>Substitutions on base expressions\<close>

locale base_substitution = substitution where vars = vars and apply_subst = apply_subst
  for vars :: "'base \<Rightarrow> 'v set" and apply_subst :: "'v \<Rightarrow> 'subst \<Rightarrow> 'base" (infixl \<open>\<cdot>v\<close> 69) +
  assumes
    \<comment>\<open>The precondition of the assumption ensures noop substitutions\<close>
    vars_id_subst: "\<And>x. exists_nonground \<Longrightarrow> vars (x \<cdot>v id_subst) = {x}" and
    comp_subst_iff: "\<And>\<sigma> \<sigma>' x. x \<cdot>v \<sigma> \<odot> \<sigma>' = subst (x \<cdot>v \<sigma>) \<sigma>'" and
    base_vars_subst: "\<And>expr \<rho>. vars (expr \<cdot> \<rho>) = \<Union> (vars ` var_subst \<rho> ` vars expr)" and
    base_vars_grounded_if_is_grounding:
      "\<And>expr \<gamma>. is_ground (expr \<cdot> \<gamma>) \<Longrightarrow> \<forall>x \<in> vars expr. is_ground (x \<cdot>v \<gamma>)"

locale based_substitution =
  substitution where vars = vars and apply_subst = "apply_subst :: 'v \<Rightarrow> 'subst \<Rightarrow> 'base" +
  base: base_substitution where
  subst = base_subst and vars = base_vars and is_ground = base_is_ground
for
  base_subst :: "'base \<Rightarrow> 'subst \<Rightarrow> 'base" and
  base_vars :: "'base \<Rightarrow> 'v set" and
  vars :: "'expr \<Rightarrow> 'v set" and
  base_is_ground +
assumes
  ground_subst_iff_base_ground_subst [simp]: "\<And>\<gamma>. is_ground_subst \<gamma> \<longleftrightarrow> base.is_ground_subst \<gamma>" and
  vars_subst: "\<And>expr \<rho>. vars (expr \<cdot> \<rho>) = \<Union> (base_vars ` var_subst \<rho> ` vars expr)" and
  vars_grounded_if_is_grounding:
    "\<And>expr \<gamma>. is_ground (expr \<cdot> \<gamma>) \<Longrightarrow> \<forall>x \<in> vars expr. base_is_ground (x \<cdot>v \<gamma>)"
begin

lemma exists_nonground_iff_base_exists_nonground:
  "exists_nonground \<longleftrightarrow> base.exists_nonground"
  by (metis base.is_ground_subst_def base.subst_id_subst ground_subst_iff_base_ground_subst
      is_ground_subst_def subst_id_subst)

lemma id_subst_subst [simp]: "base_subst (x \<cdot>v id_subst) \<sigma> = x \<cdot>v \<sigma>"
  by (metis base.comp_subst_iff left_neutral)

lemma variable_grounding:
  assumes "is_ground (expr \<cdot> \<gamma>)" "x \<in> vars expr"
  shows "base_is_ground (x \<cdot>v \<gamma>)"
  using assms vars_grounded_if_is_grounding
  by blast

definition range_vars :: "'subst \<Rightarrow> 'v set" where
  "range_vars \<sigma> = \<Union>(base_vars ` subst_range \<sigma>)"

lemma vars_id_subst_subset: "base_vars (x \<cdot>v id_subst) \<subseteq> {x}"
  using base.vars_id_subst base.no_vars_if_is_ground
  by blast

lemma vars_subst_subset: "vars (expr \<cdot> \<sigma>) \<subseteq> (vars expr - subst_domain \<sigma>) \<union> range_vars \<sigma>"
  unfolding subst_domain_def range_vars_def vars_subst subset_eq
  using base.vars_id_subst
  by (smt (verit, del_insts) DiffI UN_iff UN_simps(10) UnCI base.no_vars_if_is_ground empty_iff
      mem_Collect_eq singleton_iff)

end

context base_substitution
begin

sublocale based_substitution
  where base_subst = subst and base_vars = vars and base_is_ground = is_ground
  by unfold_locales (simp_all add: base_vars_grounded_if_is_grounding base_vars_subst)

declare ground_subst_iff_base_ground_subst [simp del]

end

hide_fact base_substitution.base_vars_subst
hide_fact base_substitution.base_vars_grounded_if_is_grounding


section \<open>Properties of substitutions on base expressions\<close>

locale based_subst_update =
  based_substitution + 
  subst_update +
  assumes ground_subst_update_in_vars:
    "\<And>update expr \<gamma> x. base_is_ground update \<Longrightarrow> is_ground (expr \<cdot> \<gamma>) \<Longrightarrow> x \<in> vars expr \<Longrightarrow>
      is_ground (expr \<cdot> \<gamma>\<lbrakk>x := update\<rbrakk>)"
begin

lemma vars_id_subst_update: "vars (expr \<cdot> id_subst\<lbrakk>x := b\<rbrakk>) \<subseteq> vars expr \<union> base_vars b"
proof (cases exists_nonground)
  case True
  then show ?thesis
    unfolding vars_subst 
    using subst_update base.vars_id_subst
    by (smt (verit, ccfv_threshold) SUP_least UnCI exists_nonground_iff_base_exists_nonground
        imageE singleton_iff subset_eq subst_update_var(1,2))
next
  case False
  then show ?thesis
    by simp
qed

lemma ground_subst_update [simp]:
  assumes "base_is_ground update" "is_ground (expr \<cdot> \<gamma>)"
  shows "is_ground (expr \<cdot> \<gamma>\<lbrakk>x := update\<rbrakk>)"
  using assms
proof (cases "x \<in> vars expr")
  case True

  show ?thesis
    using ground_subst_update_in_vars[OF assms True] .
next
  case False

  then show ?thesis
    by (simp add: assms(2))
qed

end

locale create_renaming = based_subst_update where 
  apply_subst = apply_subst for
  apply_subst :: "'v \<Rightarrow> 'subst \<Rightarrow> 'base" (infixl "\<cdot>v" 69) +
  assumes id_fold_subst_comp_ext:
    "\<And>(us :: ('v \<times> 'base) list) us' upd. exists_nonground \<Longrightarrow>
      (\<And>x. x \<cdot>v fold upd us id_subst \<odot> fold upd us' id_subst = x \<cdot>v id_subst) \<Longrightarrow>
      fold upd us id_subst \<odot> fold upd us' id_subst = id_subst"
begin

lemma create_renaming:
  assumes exists_nonground: exists_nonground and finite_S: "finite S" and bij: "bij_betw f S T"
  shows "is_renaming (renaming_of_bij f S T)"
proof (unfold is_renaming_def, intro exI)

  have finite_T: "finite T" and finite_S_T: "finite (S \<union> T)"
    using bij bij_betw_finite finite_S 
    by auto

  {
    fix x

    have "x \<cdot>v renaming_of_bij f S T \<odot> renaming_of_bij_inv f S T = x \<cdot>v id_subst"
    proof (cases "x \<in> S \<union> T")
      case False

      then show ?thesis
        unfolding renaming_of_bij_def renaming_of_bij_inv_def base.comp_subst_iff
        by (auto simp: exists_nonground finite_S finite_T)
    next
      case x_in_S_T: True

      show ?thesis
      proof (cases "x \<in> S")
        case x_in_S: True

        moreover then have "f x \<in> T"
          using bij
          by (simp add: bij_betwE)

        moreover have "inv_into S f (f x) = x"
          by (metis x_in_S bij bij_betw_inv_into_left)

        ultimately show ?thesis
          unfolding renaming_of_bij_def renaming_of_bij_inv_def base.comp_subst_iff
          using subst_updates_fmap_of_set exists_nonground finite_S_T
          by auto
      next
        case x_notin_S: False

        moreover then have "x \<in> T"
          using x_in_S_T
          by simp

        moreover then have 
          "bij_partition S T x \<in> (S - T)"
          "inv_into (T \<setminus> S) (bij_partition S T) (bij_partition S T x) = x"
          using 
            x_notin_S
            bij_partition[OF finite_S finite_T bij_betw_same_card[OF bij]]
            bij_betwE 
            bij_betw_inv_into_left 
          by fastforce+

        ultimately show ?thesis
          unfolding renaming_of_bij_def renaming_of_bij_inv_def base.comp_subst_iff
          using subst_updates_fmap_of_set exists_nonground finite_S_T
          by auto       
      qed
    qed
  }

  then show "renaming_of_bij f S T \<odot> renaming_of_bij_inv f S T = id_subst"
    unfolding renaming_of_bij_def renaming_of_bij_inv_def subst_updates_def
    by (rule id_fold_subst_comp_ext[OF exists_nonground])
qed

end

locale variables_in_base_imgu = based_substitution +
  assumes variables_in_base_imgu:
    "\<And>expr \<mu> XX.
        base.is_imgu \<mu> XX \<Longrightarrow> finite XX \<Longrightarrow> \<forall>X \<in> XX. finite X \<Longrightarrow>
        vars (expr \<cdot> \<mu>) \<subseteq> vars expr \<union> (\<Union>(base_vars ` \<Union> XX))"

locale range_vars_subset_if_is_imgu = base_substitution +
  assumes range_vars_subset_if_is_imgu:
    "\<And>\<mu> XX. is_imgu \<mu> XX \<Longrightarrow> \<forall>X\<in>XX. finite X \<Longrightarrow> finite XX \<Longrightarrow>
        range_vars \<mu> \<subseteq> (\<Union>expr\<in>\<Union>XX. vars expr)"
begin

sublocale variables_in_base_imgu where 
  base_subst = subst and base_vars = vars and base_is_ground = is_ground
  using range_vars_subset_if_is_imgu vars_subst_subset
  by unfold_locales fastforce

end

(* TODO Try using compactness instead of infinite variables \<exists>Y \<subseteq> X. finite Y \<and> (\<forall>\<tau>. is_unifier \<tau> X \<longleftrightarrow> is_unifier \<tau> Y)
 *)
locale base_variables_in_base_imgu =
  base_substitution where vars = "vars :: 'expr \<Rightarrow> 'v set" + 
  subst_update + 
  finite_variables +
  infinite_variables +
assumes
  not_back_to_id_subst: "\<And>expr \<sigma>. \<exists>x. expr \<cdot> \<sigma> = x \<cdot>v id_subst \<Longrightarrow> \<exists>x. expr = x \<cdot>v id_subst"
begin

lemma imgu_subst_domain_subset:
  assumes imgu: "is_imgu \<mu> XX"
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
        by (metis all_subst_ident_if_ground id_subst_subst subst_update_var)
    next
      case False

      then show ?thesis
        unfolding \<tau>_def comp_subst_iff
        using not_back_to_id_subst
        by (metis all_subst_ident_if_ground id_subst_subst subst_update_var(1))
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
  using imgu_subst_domain_subset[OF imgu] finite_XX finite_X finite_vars
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

      have "\<forall>x. x \<cdot>v \<mu> = x \<cdot>v id_subst \<or> z \<notin> vars (x \<cdot>v \<mu>)"
        using range_vars_def subst_domain_def z(1)
        by auto

      then have "z \<notin> vars (x \<cdot>v \<mu>)"
        using z(1) x(2) x_neq_y
        unfolding range_vars_def subst_domain_def
        by (metis all_not_in_conv no_vars_if_is_ground singleton_iff vars_id_subst)

      moreover have "z \<in> vars (x \<cdot>v \<mu> \<cdot> id_subst\<lbrakk>y := z \<cdot>v id_subst\<rbrakk>)"
        using x(2) vars_id_subst subst_update_var(1)
        unfolding vars_subst
        by (metis UN_I equals0D imageI insertI1 no_vars_if_is_ground)
       
      then have "z \<in> vars (x \<cdot>v \<mu> \<cdot> id_subst\<lbrakk>y := z \<cdot>v id_subst\<rbrakk> \<cdot> \<mu>)"
        using z(2) vars_id_subst no_vars_if_is_ground
        unfolding range_vars_def subst_domain_def vars_subst
        by fastforce
        
      ultimately show ?thesis
        using x_neq_y
        unfolding \<tau>_def comp_subst_iff
        by (metis id_subst_subst subst_comp_subst subst_update_var(2))
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
    using imgu_subst_domain_subset[OF assms(1)] subsetD vars_subst 
    by fastforce

  also have "\<dots> \<subseteq> (\<Union>expr\<in>\<Union>XX. vars expr)"
    using imgu_range_vars_vars_subset[OF assms] .

  finally show ?thesis .
qed

sublocale variables_in_base_imgu where 
  base_subst = subst and base_vars = vars and base_is_ground = is_ground
  using range_vars_subset_if_is_imgu vars_subst_subset
  by unfold_locales fastforce

end

locale base_exists_non_ident_subst =
  base_substitution where vars = vars + 
  finite_variables where vars = vars +
  infinite_variables where vars = vars +
  all_subst_ident_iff_ground where vars = vars +
  subst_update where vars = vars +
  is_ground_if_no_vars where vars = vars
  for vars :: "'expr \<Rightarrow> 'v set" 
begin

sublocale exists_non_ident_subst
proof unfold_locales
  fix expr and S :: "'expr set"
  assume finite_S: "finite S" and vars_not_empty: "\<not> is_ground expr"

  obtain x where x: "x \<in> vars expr"
    using is_ground_iff_no_vars vars_not_empty 
    by auto

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
      unfolding \<sigma>_def vars_subst
      using x
      by (metis UN_iff image_eqI singletonI subst_update_var(1) vars_id_subst vars_not_empty)

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

(* TODO: Not compatible with polymorphic terms *)
locale vars_grounded_iff_is_grounding = based_substitution +
  assumes is_grounding_if_vars_grounded:
    "\<And>expr \<gamma>. \<forall>x \<in> vars expr. base_is_ground (x \<cdot>v \<gamma>) \<Longrightarrow> is_ground (expr \<cdot> \<gamma>)"
begin

lemma vars_grounded_iff_is_grounding: "(\<forall>x \<in> vars b. base_is_ground (x \<cdot>v \<gamma>)) \<longleftrightarrow> is_ground (b \<cdot> \<gamma>)"
  using is_grounding_if_vars_grounded vars_grounded_if_is_grounding
  by blast

end


end
