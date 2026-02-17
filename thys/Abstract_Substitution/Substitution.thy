theory Substitution \<^marker>\<open>contributor \<open>Balazs Toth\<close>\<close> 
  imports
    Abstract_Substitution
    Option_Extra
    Finite_Map_Extra
    Fun_Extra
begin

section \<open>Substitutions on variables\<close>

locale substitution = abstract_substitution where
  subst = subst
for
  subst :: "'expr \<Rightarrow> 'subst \<Rightarrow> 'expr" (infixl "\<cdot>" 69) and
  apply_subst :: "'v \<Rightarrow> 'subst \<Rightarrow> 'base" (infixl "\<cdot>v" 69) and
  vars :: "'expr \<Rightarrow> 'v set" +
assumes no_vars_if_is_ground [intro]: "\<And>expr. is_ground expr \<Longrightarrow> vars expr = {}"
begin

abbreviation exists_nonground where
  "exists_nonground \<equiv> \<exists>expr. \<not>is_ground expr"

definition vars_set :: "'expr set \<Rightarrow> 'v set" where
  "vars_set exprs \<equiv> \<Union>expr \<in> exprs. vars expr"

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

locale subst_update_def =
   fixes subst_update :: "'subst \<Rightarrow> 'v \<Rightarrow> 'base \<Rightarrow> 'subst" 
begin

definition subst_updates :: "'subst \<Rightarrow> ('v, 'base) fmap \<Rightarrow> 'subst" (\<open>_\<lbrakk>_\<rbrakk>\<close> [1000, 0] 71) where
  "subst_updates \<sigma> m = fold (\<lambda>(x, b) \<sigma>. subst_update \<sigma> x b) (fmap_list m) \<sigma>"

end

locale subst_update =
  substitution where vars = vars and apply_subst = apply_subst +
  subst_update_def where subst_update = subst_update
for 
  vars :: "'expr \<Rightarrow> 'v set" and 
  apply_subst :: "'v \<Rightarrow> 'subst \<Rightarrow> 'base" (infixl "\<cdot>v" 69) and
  subst_update :: "'subst \<Rightarrow> 'v \<Rightarrow> 'base \<Rightarrow> 'subst" (\<open>_\<lbrakk>_ := _\<rbrakk>\<close> [1000, 0, 50] 71) +
  assumes 
    subst_update_var [simp]:
      \<comment>\<open>The precondition of the assumption ensures noop substitutions\<close>
      "\<And>x u \<sigma>. exists_nonground \<Longrightarrow> x \<cdot>v \<sigma>\<lbrakk>x := u\<rbrakk> = u" 
      "\<And>x y u \<sigma>. x \<noteq> y \<Longrightarrow> x \<cdot>v \<sigma>\<lbrakk>y := u\<rbrakk> = x \<cdot>v \<sigma>" and
    subst_update [simp]:
      "\<And>x expr u \<sigma>. x \<notin> vars expr \<Longrightarrow> expr \<cdot> \<sigma>\<lbrakk>x := u\<rbrakk> = expr \<cdot> \<sigma>"
      "\<And>\<sigma> x. \<sigma>\<lbrakk>x := x \<cdot>v \<sigma>\<rbrakk> = \<sigma>" and
    subst_update_twice [simp]:
      "\<And>\<sigma> x a b. (\<sigma>\<lbrakk>x := a\<rbrakk>)\<lbrakk>x := b\<rbrakk> = \<sigma>\<lbrakk>x := b\<rbrakk>"
begin

lemma subst_updates_empty [simp]: "\<sigma>\<lbrakk>fmempty\<rbrakk> = \<sigma>"
  unfolding subst_updates_def
  by auto

lemma fold_redundant_updates_var [simp]:
  assumes "x \<notin> set (map fst us)"
  shows "x \<cdot>v fold (\<lambda>(x, b) \<sigma>. \<sigma>\<lbrakk>x := b\<rbrakk>) us \<sigma> = x \<cdot>v \<sigma>"
  using assms
  by (induction us arbitrary: \<sigma>) (simp_all add: split_beta)

lemma fold_updates_var [simp]:
  assumes 
    exists_nonground: exists_nonground and 
    distinct_updates: "distinct (map fst us)" and 
    update_in_updates: "(x, b) \<in> set us"
  shows "x \<cdot>v fold (\<lambda>(x, b) \<sigma>. \<sigma>\<lbrakk>x := b\<rbrakk>) us \<sigma> = b"
  using distinct_updates update_in_updates
proof (induction us arbitrary: \<sigma>)
  case Nil

  then show ?case 
    by simp
next
  case (Cons u us)
 
  then show ?case
    using exists_nonground fold_redundant_updates_var
    by (cases "u = (x, b)") auto
qed

lemma fold_redundant_updates [simp]: 
  assumes "\<And>x b. (x, b) \<in> set us \<Longrightarrow> x \<notin> vars expr \<or> b = x \<cdot>v \<sigma>" "distinct (map fst us)"
  shows "expr \<cdot> fold (\<lambda>(x, b) \<sigma>. \<sigma>\<lbrakk>x := b\<rbrakk>) us \<sigma> = expr \<cdot> \<sigma>"
  using assms
proof (induction us arbitrary: \<sigma>)
  case Nil

  then show ?case
    by simp
next
  case (Cons u us)

  then show ?case
    by (smt (verit, best) distinct.simps(2) fold_simps(2) list.set_intros(1) list.simps(9) 
        prod.collapse set_subset_Cons split_beta subsetD subst_update subst_update_var(2))
qed

lemma subst_updates_var: 
  assumes exists_nonground: exists_nonground
  shows "x \<cdot>v \<sigma>\<lbrakk>u\<rbrakk> = get_or (fmlookup u x) (x \<cdot>v \<sigma>)"
proof (cases "fmlookup u x")
  case None

  have "x \<cdot>v fold (\<lambda>(x, b) \<sigma>. \<sigma>\<lbrakk>x := b\<rbrakk>) (fmap_list u) \<sigma> = x \<cdot>v \<sigma>"
  proof (rule fold_redundant_updates_var)

    show "x \<notin> set (map fst (fmap_list u))"
      unfolding set_fst_fmap_list
      by (simp add: None fmdom'_notI)
  qed

  then show ?thesis
    unfolding None subst_updates_def
    by simp
next
  case (Some b)

  then show ?thesis
    unfolding subst_updates_def
    by (simp add: exists_nonground fmap_list_mem_iff)
qed

lemma redundant_subst_updates [simp]:
  assumes "\<And>x. x \<in> vars expr \<Longrightarrow> fmlookup u x = None \<or> fmlookup u x = Some (x \<cdot>v \<sigma>)" 
  shows "expr \<cdot> \<sigma>\<lbrakk>u\<rbrakk> = expr \<cdot> \<sigma>"
proof (unfold subst_updates_def, rule fold_redundant_updates)
  fix x b
  assume "(x, b) \<in> set (fmap_list u)"

  then show "x \<notin> vars expr \<or> b = x \<cdot>v \<sigma>"
    unfolding fmap_list_mem_iff
    using assms
    by fastforce
next

  show "distinct (map fst (fmap_list u))"
    by simp
qed

lemma redundant_subst_updates_vars_set [simp]:
  assumes exists_nonground "\<And>x. x \<in> X \<Longrightarrow> fmlookup u x = None \<or> fmlookup u x = Some (x \<cdot>v \<sigma>)"
  shows "(\<lambda>x. x \<cdot>v \<sigma>\<lbrakk>u\<rbrakk>) ` X = (\<lambda>x. x \<cdot>v \<sigma>) ` X"
  using assms(2) subst_updates_var[OF assms(1)]
  by force

lemma redundant_subst_updates_vars_image [simp]:
  assumes "\<And>x. x \<in> \<Union>(vars ` X) \<Longrightarrow> fmlookup u x = None \<or> fmlookup u x = Some (x \<cdot>v \<sigma>)"
  shows "(\<lambda>expr. expr \<cdot> \<sigma>\<lbrakk>u\<rbrakk>) ` X = (\<lambda>expr. expr \<cdot> \<sigma>) ` X"
  using assms redundant_subst_updates
  by (meson UN_I image_cong)

lemma subst_updates_fmap_of_set [simp]:
  assumes exists_nonground "x \<in> X" "finite X"
  shows "x \<cdot>v \<sigma>\<lbrakk>fmap_of_set X f\<rbrakk> = f x"
  using assms subst_updates_var 
  by simp

lemma redundant_subst_updates_fmap_of_set [simp]:
  assumes exists_nonground "x \<notin> X" "finite X" 
  shows "x \<cdot>v \<sigma>\<lbrakk>fmap_of_set X f\<rbrakk> = x \<cdot>v \<sigma>"
  using assms subst_updates_var
  by simp

definition renaming_of_bij where
  "renaming_of_bij f S T \<equiv>
    id_subst\<lbrakk>fmap_of_set (S \<union> T) (\<lambda>x. (if x \<in> S then f x else bij_partition S T x) \<cdot>v id_subst)\<rbrakk>"

definition renaming_of_bij_inv where
  "renaming_of_bij_inv f S T \<equiv>
     id_subst\<lbrakk>fmap_of_set (S \<union> T)
       (\<lambda>x. (if x \<in> T then inv_into S f x else inv_into (T - S) (bij_partition S T) x) \<cdot>v id_subst)\<rbrakk>"

lemma redundant_renaming_of_bij:
  assumes exists_nonground "finite S" "bij_betw f S T" "x \<notin> S \<union> T"
  shows "x \<cdot>v renaming_of_bij f S T = x \<cdot>v id_subst"
  unfolding renaming_of_bij_def
  using assms
  by (simp add: bij_betw_finite)

lemma renaming_of_bij_on_S:
  assumes exists_nonground "finite S" "bij_betw f S T" "x \<in> S" 
  shows "x \<cdot>v renaming_of_bij f S T = f x \<cdot>v id_subst"
  unfolding renaming_of_bij_def
  using assms
  by (simp add: bij_betw_finite)

end

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

lemma infinite_exprs:
  assumes "exists_nonground"
  shows "infinite (UNIV :: 'expr set)"
  using assms exists_non_ident_subst
  by auto

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
     \<comment>\<open>The precondition of the assumption ensures noop substitutions\<close>
    is_renaming_imp:
      "\<And>\<rho>. exists_nonground \<Longrightarrow>
           is_renaming \<rho> \<Longrightarrow> inj (var_subst \<rho>) \<and> (\<forall>x. \<exists>x'. x \<cdot>v \<rho> = x' \<cdot>v id_subst)" and
    rename_variables: "\<And>expr \<rho>. is_renaming \<rho> \<Longrightarrow> vars (expr \<cdot> \<rho>) = rename \<rho> ` (vars expr)"
begin

lemma renaming_range_id_subst:
  assumes exists_nonground: "exists_nonground" and \<rho>: "is_renaming \<rho>"
  shows "x \<cdot>v \<rho> \<in> range (var_subst id_subst)"
  using is_renaming_imp[OF exists_nonground \<rho>]
  by auto

lemma obtain_renamed_variable:
  assumes "exists_nonground" "is_renaming \<rho>"
  obtains x' where "x \<cdot>v \<rho> = x' \<cdot>v id_subst"
  using renaming_range_id_subst[OF assms]
  by auto

lemma id_subst_rename [simp]:
  assumes "exists_nonground" and \<rho>: "is_renaming \<rho>"
  shows "rename \<rho> x \<cdot>v id_subst = x \<cdot>v \<rho>"
  unfolding rename_def[OF \<rho>]
  using obtain_renamed_variable[OF assms]
  by (metis (mono_tags, lifting) someI)

lemma rename_variables_id_subst: 
  assumes "is_renaming \<rho>" 
  shows "var_subst id_subst ` vars (expr \<cdot> \<rho>) = var_subst \<rho> ` (vars expr)"
  using rename_variables[OF assms] id_subst_rename[OF _ assms]
  by (smt (verit, best) empty_is_image image_cong image_image no_vars_if_is_ground)

lemma surj_inv_renaming:
  assumes exists_nonground: "exists_nonground" and \<rho>: "is_renaming \<rho>"
  shows "surj (\<lambda>x. inv (var_subst \<rho>) (x \<cdot>v id_subst))"
  using inv_f_f is_renaming_imp[OF exists_nonground \<rho>]
  unfolding surj_def
  by metis

lemma renaming_range:
  assumes \<rho>: "is_renaming \<rho>" and x: "x \<in> vars (expr \<cdot> \<rho>)"
  shows "x \<cdot>v id_subst \<in> range (var_subst \<rho>)"
  using rename_variables_id_subst[OF \<rho>] x
  by fastforce

lemma renaming_inv_into:
  assumes "is_renaming \<rho>" "x \<in> vars (expr \<cdot> \<rho>)"
  shows "inv (var_subst \<rho>) (x \<cdot>v id_subst) \<cdot>v \<rho> = x \<cdot>v id_subst"
  using f_inv_into_f[OF renaming_range[OF assms]].

lemma inv_renaming:
  assumes exists_nonground: "exists_nonground" and \<rho>: "is_renaming \<rho>"
  shows "inv (var_subst \<rho>) (x \<cdot>v \<rho>) = x"
  using is_renaming_imp[OF exists_nonground \<rho>]
  by (simp add: inv_into_f_eq)

lemma renaming_inv_in_vars:
  assumes \<rho>: "is_renaming \<rho>" and x: "x \<in> vars (expr \<cdot> \<rho>)"
  shows "inv (var_subst \<rho>) (x \<cdot>v id_subst) \<in> vars expr"
  using assms rename_variables_id_subst[OF \<rho>]
  by (metis no_vars_if_is_ground imageI image_inv_f_f insert_not_empty is_renaming_imp
      mk_disjoint_insert)

lemma inj_id_subst: 
  assumes "exists_nonground"
  shows "inj (var_subst id_subst)"
  using is_renaming_id_subst is_renaming_imp[OF assms]
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

locale exists_ground = substitution +
  assumes exists_ground: "\<exists>expr. is_ground expr"

locale exists_ground_subst = substitution +
  assumes exists_ground_subst: "\<exists>\<gamma>. is_ground_subst \<gamma>"
begin

lemma obtain_ground_subst:
  obtains \<gamma> where "is_ground_subst \<gamma>"
  using exists_ground_subst
  by metis

sublocale exists_ground
proof unfold_locales
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

locale exists_imgu = substitution +
  assumes
    "\<And>\<upsilon> expr expr'. exists_nonground \<Longrightarrow> expr \<cdot> \<upsilon> = expr' \<cdot> \<upsilon> \<Longrightarrow> \<exists>\<mu>. is_imgu \<mu> {{expr, expr'}}"
begin

lemma exists_imgu:
  assumes "expr \<cdot> \<upsilon> = expr' \<cdot> \<upsilon>" 
  shows "\<exists>\<mu>. is_imgu \<mu> {{expr, expr'}}"
proof (cases exists_nonground)
  case True

  then show ?thesis
    by (metis assms exists_imgu_axioms exists_imgu_axioms_def exists_imgu_def)
next
  case False

  then have "expr = expr'"
    using assms
    by simp

  then show ?thesis
    by (metis insert_absorb2 is_imgu_id_subst_empty is_imgu_insert_singleton)
qed

lemma obtains_imgu:
  assumes "expr \<cdot> \<upsilon> = expr' \<cdot> \<upsilon>"
  obtains \<mu> where "is_imgu \<mu> {{expr, expr'}}"
  using exists_imgu[OF assms]
  by metis

(* TODO: Add version with "\<exists>Y \<subseteq> X. finite Y \<and> (\<forall>\<tau>. is_unifier \<tau> X \<longleftrightarrow> is_unifier \<tau> Y)" +
  prove under this assumption compactness of substitions  *)
lemma exists_imgu_set:
  assumes
    finite_X: "finite X" and
    unifier: "is_unifier \<upsilon> X"
  shows "\<exists>\<mu>. is_imgu \<mu> {X}"
  using finite_X unifier
proof (cases X)
  case emptyI

  then show ?thesis
    using is_imgu_id_subst
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
        by (metis is_unifier_subset comp_subst.left.monoid_action_compatibility
             singletonD subset_insertI)

    obtain \<mu>' where \<mu>': "is_imgu \<mu>' {{expr \<cdot> \<mu>, expr'}}"
    proof (rule obtains_imgu)

      obtain expr'' where "expr'' \<in> X'"
        using insert.hyps(2)
        by auto

      moreover then have expr': "expr' = expr'' \<cdot> \<mu>"
        using expr'
        by presburger

      ultimately show "expr \<cdot> \<mu> \<cdot> \<upsilon> = expr' \<cdot> \<upsilon>"
        using \<mu>_absorbs_\<tau>
        unfolding expr'
        by (metis insert.prems insertCI is_unifier_iff)
    qed

    define \<mu>'' where "\<mu>'' = \<mu> \<odot> \<mu>'"

    show ?case 
    proof (rule exI)

      show "is_imgu \<mu>'' {insert expr X'}"
      proof (unfold is_imgu_def, intro conjI allI impI)

        show "is_unifier_set \<mu>'' {insert expr X'}"
          using \<mu>'
          unfolding \<mu>''_def 
          by (simp add: expr' is_unifier_iff is_unifier_set_insert subst_imgu_eq_subst_imgu)
      next
        fix \<tau>
        assume "is_unifier_set \<tau> {insert expr X'}"

        moreover then have "is_unifier_set \<tau> {{expr \<cdot> \<mu>, expr'}}"
          using \<mu> 
          unfolding is_imgu_def is_unifier_set_insert
          by (metis X'_\<mu> is_unifier_def is_unifier_subset subst_set_insert empty_iff insertCI 
              subset_insertI subst_set_comp_subst)

        ultimately show "\<mu>'' \<odot> \<tau> = \<tau>"
          using \<mu> \<mu>'
          unfolding \<mu>''_def is_imgu_def is_unifier_set_insert
          by (metis is_unifier_subset assoc subset_insertI)
      qed
    qed
  qed
qed

lemma exists_imgu_sets:
  assumes
    finite_XX: "finite XX" and
    finite_X: "\<forall>X\<in>XX. finite X" and
    unifier: "is_unifier_set \<upsilon> XX"
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
      unfolding is_unifier_set_def is_unifier_iff X_\<mu>_def subst_set_def
      by (smt (verit, ccfv_threshold) comp_subst.left.monoid_action_compatibility image_iff 
          insertCI)

    ultimately show ?thesis
      using that exists_imgu_set
      by blast
  qed

  define \<mu>'' where "\<mu>'' = \<mu> \<odot> \<mu>'"

  show ?case
  proof (unfold is_imgu_def, intro exI conjI allI impI)

    show "is_unifier_set \<mu>'' (insert X XX)"
      using \<mu> \<mu>' insert.prems(1) 
      unfolding \<mu>''_def is_imgu_def X_\<mu>_def is_unifier_iff is_unifier_set_def
      by (metis comp_subst.left.monoid_action_compatibility insert_absorb insert_iff 
          subst_set_insert)
     
  next
    fix \<tau>
    assume "is_unifier_set \<tau> (insert X XX)"

    then show "\<mu>'' \<odot> \<tau> = \<tau>"
      using \<mu> \<mu>'
      unfolding \<mu>''_def X_\<mu>_def is_imgu_def is_unifier_set_insert is_unifier_def
      by (metis abstract_substitution_ops.subst_set_empty comp_subst.left.assoc 
          is_unifier_set_empty subst_set_comp_subst)
  qed
qed

end

(* TODO: Not compatible with polymorphic terms *)
locale subst_updates_compat =
  subst_update +
  assumes subst_updates_compat: 
    "\<And>expr \<sigma>. \<forall>x \<in> vars expr. fmlookup u x = Some (x \<cdot>v \<sigma>) \<Longrightarrow> expr \<cdot> id_subst\<lbrakk>u\<rbrakk> = expr \<cdot> \<sigma>"

locale subst_eq =
  substitution +
  assumes subst_eq: "\<And>expr \<sigma> \<tau>. (\<And>x. x \<in> vars expr \<Longrightarrow> x \<cdot>v \<sigma> = x \<cdot>v \<tau>) \<Longrightarrow> expr \<cdot> \<sigma> = expr \<cdot> \<tau>"
begin

lemma subset_subst_eq:
  assumes "\<forall>x\<in>vars C. x \<cdot>v \<sigma>\<^sub>1 = x \<cdot>v \<sigma>\<^sub>2" "vars D \<subseteq> vars C" 
  shows "D \<cdot> \<sigma>\<^sub>1 = D \<cdot> \<sigma>\<^sub>2"
  using assms
  by (meson subset_iff subst_eq)

end

locale is_ground_if_no_vars = substitution + 
  assumes is_ground_if_no_vars: "\<And>expr. vars expr = {} \<Longrightarrow> is_ground expr"
begin

lemma is_ground_iff_no_vars: "is_ground expr \<longleftrightarrow> vars expr = {}"
  by (metis is_ground_if_no_vars no_vars_if_is_ground)

end

end
