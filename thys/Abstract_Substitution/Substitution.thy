theory Substitution \<^marker>\<open>contributor \<open>Balazs Toth\<close>\<close> 
  imports
    Abstract_Substitution
    "HOL-Library.FSet"
    Option_Extra
begin

section \<open>Substitutions on variables\<close>

locale substitution = abstract_substitution where
  subst = subst and is_ground = "\<lambda>expr. vars expr = {}"
for
  subst :: "'expr \<Rightarrow> 'subst \<Rightarrow> 'expr" (infixl "\<cdot>" 69) and
  apply_subst :: "'v \<Rightarrow> 'subst \<Rightarrow> 'base" (infixl "\<cdot>v" 69) and
  subst_update :: "'subst \<Rightarrow> 'v \<Rightarrow> 'base \<Rightarrow> 'subst" (\<open>_\<lbrakk>_ := _\<rbrakk>\<close> [1000, 0, 50] 71) and
  vars :: "'expr \<Rightarrow> 'v set" +
assumes
  (* Interesting that not both directions are required *)
  subst_eq: "\<And>expr \<sigma> \<tau>. (\<And>x. x \<in> vars expr \<Longrightarrow> x \<cdot>v \<sigma> = x \<cdot>v \<tau>) \<Longrightarrow> expr \<cdot> \<sigma> = expr \<cdot> \<tau>" and
  subst_update [simp]:
    "\<And>x update. x \<cdot>v \<sigma>\<lbrakk>x := update\<rbrakk> = update" 
    "\<And>x y update. x \<noteq> y \<Longrightarrow> x \<cdot>v \<sigma>\<lbrakk>y := update\<rbrakk> = x \<cdot>v \<sigma>"
begin

abbreviation is_ground where "is_ground expr \<equiv> vars expr = {}"

definition vars_set :: "'expr set \<Rightarrow> 'v set" where
  "vars_set exprs \<equiv> \<Union>expr \<in> exprs. vars expr"

lemma subst_reduntant_upd [simp]:
  assumes "x \<notin> vars expr"
  shows "expr \<cdot> \<sigma>\<lbrakk>x := update\<rbrakk> = expr \<cdot> \<sigma>"
  using assms subst_eq subst_update
  by metis

lemma subst_cannot_unground:
  assumes "\<not>is_ground (expr \<cdot> \<sigma>)"
  shows "\<not>is_ground expr"
  using assms 
  by force

abbreviation (input) var_subst where
  "var_subst \<sigma> x \<equiv> x \<cdot>v \<sigma>"

abbreviation (input) expr_subst where
  "expr_subst \<sigma> expr \<equiv> expr \<cdot> \<sigma>"

definition subst_domain :: "'subst \<Rightarrow> 'v set" where
  "subst_domain \<sigma> = {x. x \<cdot>v \<sigma> \<noteq> x \<cdot>v id_subst}"

abbreviation subst_range :: "'subst \<Rightarrow> 'base set" where
  "subst_range \<sigma> \<equiv> var_subst \<sigma> ` subst_domain \<sigma>"

lemma subst_inv:
  assumes "\<sigma> \<odot> \<sigma>_inv = id_subst"
  shows "expr \<cdot> \<sigma> \<cdot> \<sigma>_inv = expr"
  using assms
  by (metis subst_comp_subst subst_id_subst)

definition rename where
  "is_renaming \<rho> \<Longrightarrow> rename \<rho> x \<equiv> SOME x'. x \<cdot>v \<rho> = x' \<cdot>v id_subst"

lemma is_unifier_two_iff [simp]: "is_unifier \<upsilon> {expr, expr'} \<longleftrightarrow> expr \<cdot> \<upsilon> = expr' \<cdot> \<upsilon>"
  unfolding is_unifier_def
  using insertCI
  by fastforce

lemma is_unifier_set_two_iff [simp]: "is_unifier_set \<upsilon> {{expr, expr'}} \<longleftrightarrow> expr \<cdot> \<upsilon> = expr' \<cdot> \<upsilon>"
  unfolding is_unifier_set_def
  by simp

lemma obtain_imgu_absorption: 
  assumes "is_unifier_set \<upsilon> XX" "is_imgu \<mu> XX" 
  obtains \<sigma> where "\<upsilon> = \<mu> \<odot> \<sigma>"
  using assms
  unfolding is_imgu_def
  by metis

end


subsection \<open>Properties of substitutions\<close>

locale all_subst_ident_iff_ground =
  substitution +
  assumes all_subst_ident_iff_ground: "\<And>expr. is_ground expr \<longleftrightarrow> (\<forall>\<sigma>. expr \<cdot> \<sigma> = expr)"

locale exists_non_ident_subst =
  substitution where vars = vars
  for vars :: "'expr \<Rightarrow> 'v set" +
  assumes
    exists_non_ident_subst:
      "\<And>expr S. finite S \<Longrightarrow> \<not>is_ground expr \<Longrightarrow> \<exists>\<sigma>. expr \<cdot> \<sigma> \<noteq> expr \<and> expr \<cdot> \<sigma> \<notin> S"
begin

lemma infinite_expr:
  assumes "\<exists>expr. vars expr \<noteq> {}"
  shows "infinite (UNIV :: 'expr set)"
proof 
  assume finite: "finite (UNIV :: 'expr set)"

  obtain expr where expr: "vars expr \<noteq> {}"
    using assms
    by metis

  show False
    using exists_non_ident_subst[OF finite expr]
    by simp
qed

end

locale finite_variables = substitution where vars = vars
  for vars :: "'expr \<Rightarrow> 'v set" +
  assumes finite_vars [intro]: "\<And>expr. finite (vars expr)"
begin

abbreviation finite_vars :: "'expr \<Rightarrow> 'v fset" where
  "finite_vars expr \<equiv> Abs_fset (vars expr)"

lemma fset_finite_vars [simp]: "fset (finite_vars expr) = vars expr"
  using Abs_fset_inverse finite_vars
  by blast

end

locale infinite_variables = substitution where vars = vars
  for vars :: "'expr \<Rightarrow> 'v set" +
  assumes infinite_vars [intro]: "infinite (UNIV :: 'v set)"

locale renaming_variables = substitution +
  assumes
    is_renaming_iff:
      "\<And>\<rho>. is_renaming \<rho> \<longleftrightarrow> inj (var_subst \<rho>) \<and> (\<forall>x. \<exists>x'. x \<cdot>v \<rho> = x' \<cdot>v id_subst)" and
    rename_variables: "\<And>expr \<rho>. is_renaming \<rho> \<Longrightarrow> vars (expr \<cdot> \<rho>) = rename \<rho> ` (vars expr)"
begin

lemma renaming_range_id_subst:
  assumes "is_renaming \<rho>"
  shows "x \<cdot>v \<rho> \<in> range (var_subst id_subst)"
  using assms
  unfolding is_renaming_iff
  by auto

lemma obtain_renamed_variable:
  assumes "is_renaming \<rho>"
  obtains x' where "x \<cdot>v \<rho> = x' \<cdot>v id_subst"
  using renaming_range_id_subst[OF assms]
  by auto

lemma id_subst_rename [simp]:
  assumes "is_renaming \<rho>"
  shows "rename \<rho> x \<cdot>v id_subst = x \<cdot>v \<rho>"
  unfolding rename_def[OF assms]
  using obtain_renamed_variable[OF assms]
  by (metis (mono_tags, lifting) someI)

lemma rename_variables_id_subst: 
  assumes "is_renaming \<rho>" 
  shows "var_subst id_subst ` vars (expr \<cdot> \<rho>) = var_subst \<rho> ` (vars expr)"
  using rename_variables[OF assms] id_subst_rename[OF assms]
  by (smt (verit, best) image_cong image_image)

lemma surj_inv_renaming:
  assumes "is_renaming \<rho>"
  shows "surj (\<lambda>x. inv (var_subst \<rho>) (x \<cdot>v id_subst))"
  using assms inv_f_f
  unfolding is_renaming_iff surj_def
  by metis

lemma renaming_range:
  assumes "is_renaming \<rho>" "x \<in> vars (expr \<cdot> \<rho>)"
  shows "x \<cdot>v id_subst \<in> range (var_subst \<rho>)"
  using rename_variables_id_subst[OF assms(1)] assms(2)
  by fastforce

lemma renaming_inv_into:
  assumes "is_renaming \<rho>" "x \<in> vars (expr \<cdot> \<rho>)"
  shows "inv (var_subst \<rho>) (x \<cdot>v id_subst) \<cdot>v \<rho> = x \<cdot>v id_subst"
  using f_inv_into_f[OF renaming_range[OF assms]].

lemma inv_renaming:
  assumes "is_renaming \<rho>"
  shows "inv (var_subst \<rho>) (x \<cdot>v \<rho>)  = x"
  using assms
  unfolding is_renaming_iff
  by (simp add: inv_into_f_eq)

lemma renaming_inv_in_vars:
  assumes "is_renaming \<rho>" "x \<in> vars (expr \<cdot> \<rho>)"
  shows "inv (var_subst \<rho>) (x \<cdot>v id_subst) \<in> vars expr"
  using assms rename_variables_id_subst[OF assms(1)]
  by (metis image_eqI image_inv_f_f is_renaming_iff)

lemma inj_id_subst: "inj (var_subst id_subst)"
  using is_renaming_id_subst is_renaming_iff
  by blast

end

locale grounding = substitution where vars = vars and id_subst = id_subst
  for vars :: "'expr \<Rightarrow> 'var set" and id_subst :: "'subst" +
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

locale exists_ground_subst = substitution +
  assumes exists_ground_subst: "\<exists>\<gamma>. is_ground_subst \<gamma>"
begin

lemma obtain_ground_subst:
  obtains \<gamma> where "is_ground_subst \<gamma>"
  using exists_ground_subst
  by metis

lemma ground_exists: "\<exists>expr. is_ground expr"
proof -
  fix expr

  obtain \<gamma> where \<gamma>: "is_ground_subst \<gamma>"
    using obtain_ground_subst .

  show "\<exists>expr. is_ground expr"
  proof (rule exI)
    show "is_ground (expr \<cdot> \<gamma>)"
      using \<gamma> is_ground_subst_is_ground
      by blast
  qed
qed

lemma ground_subst_extension:
  assumes "is_ground (expr \<cdot> \<gamma>)"
  obtains \<gamma>'
  where "expr \<cdot> \<gamma> = expr \<cdot> \<gamma>'" and "is_ground_subst \<gamma>'"
  using obtain_ground_subst assms
  by (metis all_subst_ident_if_ground is_ground_subst_comp_right subst_comp_subst)

end

locale subst_updates = substitution where vars = vars and apply_subst = apply_subst
 for
    vars :: "'expr \<Rightarrow> 'v set" and
    apply_subst :: "'v \<Rightarrow> 'subst \<Rightarrow> 'base"  (infixl \<open>\<cdot>v\<close> 69) +
  fixes subst_updates :: "'subst \<Rightarrow> ('v \<rightharpoonup> 'base) \<Rightarrow> 'subst" 
  assumes
    subst_updates [simp]: "\<And>x. x \<cdot>v subst_updates \<sigma> update = get_or (update x) (x \<cdot>v \<sigma>)"

locale exists_imgu = substitution +
  assumes exists_imgu: "\<And>\<upsilon> expr expr'. expr \<cdot> \<upsilon> = expr' \<cdot> \<upsilon> \<Longrightarrow> \<exists>\<mu>. is_imgu \<mu> {{expr, expr'}}"
begin

lemma obtains_imgu:
  assumes "expr \<cdot> \<upsilon> = expr' \<cdot> \<upsilon>"
  obtains \<mu> where "is_imgu \<mu> {{expr, expr'}}"
  using exists_imgu[OF assms]
  by metis

lemma exists_imgu_set:
  assumes finite_X: "finite X" and unifier: "is_unifier \<upsilon> X" 
  shows "\<exists>\<mu>. is_imgu \<mu> {X}"
  using assms
proof (cases X)
  case emptyI

  then show ?thesis
    using is_imgu_id_subst is_unifier_id_subst is_unifier_id_subst_empty
    by blast
next
  case (insertI X' x)

  then have "X \<noteq> {}"
    by simp

  with finite_X show ?thesis
    using unifier
  proof (induction X rule: finite_ne_induct)
    case (singleton x)

    then show ?case
      using is_imgu_id_subst_empty is_imgu_insert_singleton 
      by blast
  next
    case (insert expr X')

    then obtain \<mu> where \<mu>: "is_imgu \<mu> {X'}"
      by (meson finite_insert is_unifier_subset subset_insertI)

    then have "card (subst_set X' \<mu>) = 1"
      by (simp add: is_imgu_def is_unifier_def subst_set_def insert is_unifier_set_insert le_Suc_eq)

    then obtain expr' where X'_\<mu>: "subst_set X' \<mu> = {expr'}"
      using card_1_singletonE
      by blast

    then have expr': "\<And>expr. expr \<in> X' \<Longrightarrow> expr \<cdot> \<mu> = expr'"
      unfolding subst_set_def
      by auto

    have \<mu>_absorbs_\<tau>: "\<And>expr. expr \<cdot> \<mu> \<cdot> \<upsilon> =  expr \<cdot> \<upsilon>"
        using \<mu> insert.prems insert.hyps(1)
        unfolding is_imgu_def is_unifier_set_def
        by (metis comp_subst.left.monoid_action_compatibility finite_insert is_unifier_subset
            singletonD subset_insertI)

    obtain \<mu>' where \<mu>': "is_imgu \<mu>' {{expr \<cdot> \<mu>, expr'}}"
    proof (rule obtains_imgu)

      obtain expr'' where "expr'' \<in> X'"
        using insert.hyps(2) by auto

      moreover then have expr': "expr' = expr'' \<cdot> \<mu>"
        using expr'
        by presburger

      ultimately show "expr \<cdot> \<mu> \<cdot> \<upsilon> = expr' \<cdot> \<upsilon>"
        using \<mu>_absorbs_\<tau>
        unfolding expr'
        by (metis finite.insertI insert.hyps(1) insert.prems insertI1 insertI2
            is_unifier_iff_if_finite)
    qed

    define \<mu>'' where "\<mu>'' = \<mu> \<odot> \<mu>'"

    show ?case 
    proof (rule exI)

      show "is_imgu \<mu>'' {insert expr X'}"
      proof (unfold is_imgu_def, intro conjI allI impI)

        show "is_unifier_set \<mu>'' {insert expr X'}"
          using \<mu>'
          unfolding \<mu>''_def 
          by (simp add: is_unifier_iff_if_finite is_unifier_set_insert expr' insert.hyps(1)
              subst_imgu_eq_subst_imgu)
      next
        fix \<tau>
        assume "is_unifier_set \<tau> {insert expr X'}"

        moreover then have "is_unifier_set \<tau> {{expr \<cdot> \<mu>, expr'}}"
          using \<mu> 
          unfolding is_imgu_def is_unifier_set_insert
          by (metis X'_\<mu> is_unifier_subset subst_set_insert finite_insert insert.hyps(1) 
              is_unifier_def subset_insertI subst_set_comp_subst)

        ultimately show "\<mu>'' \<odot> \<tau> = \<tau>"
          using \<mu> \<mu>'
          unfolding \<mu>''_def is_imgu_def is_unifier_set_insert
          by (metis finite.insertI insert.hyps(1) is_unifier_subset assoc subset_insertI)
      qed
    qed
  qed
qed

lemma exists_imgu_sets:
  assumes finite_XX: "finite XX" and finite_X: "\<forall>X\<in>XX. finite X" and unifier: "is_unifier_set \<upsilon> XX"
  shows "\<exists>\<mu>. is_imgu \<mu> XX"
using finite_XX finite_X unifier
proof (induction XX rule: finite_induct)
  case empty

  then show ?case
    by (metis is_imgu_id_subst_empty)
next
  case (insert X XX)

  obtain \<mu> where \<mu>: "is_imgu \<mu> XX" 
    using insert.IH insert.prems is_unifier_set_insert
    by force

  define X_\<mu> where "X_\<mu> = subst_set X \<mu>"

  then obtain \<mu>' where \<mu>': "is_imgu \<mu>' {X_\<mu>}" 
  proof -
    have "finite X_\<mu>"
      unfolding X_\<mu>_def subst_set_def
      using insert.prems(1)
      by simp

    moreover have "\<mu> \<odot> \<upsilon> = \<upsilon>"
      using \<mu> insert.prems(2)
      unfolding is_imgu_def is_unifier_set_def
      by blast

    then have "is_unifier \<upsilon> X_\<mu>"
      using insert.prems(2)
      unfolding is_unifier_set_def is_unifier_def X_\<mu>_def
      by (metis insertCI subst_set_comp_subst)

    ultimately show ?thesis
      using that exists_imgu_set
      by blast
  qed

  define \<mu>'' where "\<mu>'' = \<mu> \<odot> \<mu>'"

  show ?case
  proof (unfold is_imgu_def, intro exI conjI allI impI)

    show "is_unifier_set \<mu>'' (insert X XX)"
      using \<mu> \<mu>' insert.prems(1) is_unifier_iff_if_finite
      unfolding \<mu>''_def is_imgu_def X_\<mu>_def is_unifier_def is_unifier_set_def 
      by (smt (verit, best) comp_subst.left.monoid_action_compatibility insert_iff
          subst_set_comp_subst)
  next
    fix \<tau>
    assume "is_unifier_set \<tau> (insert X XX)"

    then show "\<mu>'' \<odot> \<tau> = \<tau>"
      using \<mu> \<mu>'
      unfolding \<mu>''_def X_\<mu>_def is_imgu_def is_unifier_set_insert is_unifier_def
      by (metis comp_subst.left.assoc is_unifier_set_empty subst_set_comp_subst)
  qed
qed

end

end
