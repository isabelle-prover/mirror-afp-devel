theory Substitution_First_Order_Term
  imports
    Based_Substitution
    "First_Order_Terms.Unification"
    "Regular_Tree_Relations.Ground_Terms"
begin

section \<open>Substitutions for first order terms\<close>

subsection \<open>Interpretations for first order terms\<close> \<^marker>\<open>contributor \<open>Balazs Toth\<close>\<close> 

abbreviation (input) subst_updates where
  "subst_updates \<sigma> update x \<equiv> get_or (update x) (\<sigma> x)"

abbreviation (input) apply_subst where
  "apply_subst x \<sigma> \<equiv> \<sigma> x"

global_interpretation "term": base_substitution where
  comp_subst = "(\<circ>\<^sub>s)" and id_subst = Var and subst = "(\<cdot>)" and vars = vars_term and
  subst_update = fun_upd and apply_subst = apply_subst
proof unfold_locales
  fix t :: "('f, 'v) term"  and \<sigma> \<tau> :: "('f, 'v) subst"

  assume "\<And>x. x \<in> vars_term t \<Longrightarrow> \<sigma> x = \<tau> x"

  then show "t \<cdot> \<sigma> = t \<cdot> \<tau>"
    by (rule term_subst_eq)
next
  fix x :: 'v

  show "vars_term (Var x) = {x}"
    by simp
next
  fix \<sigma> \<sigma>' :: "('f, 'v) subst" and x

  show "(\<sigma> \<circ>\<^sub>s \<sigma>') x = \<sigma> x \<cdot> \<sigma>'"
    unfolding subst_compose_def ..
next
  fix t :: "('f, 'v) term" and \<rho> :: "('f, 'v) subst"

  show "vars_term (t \<cdot> \<rho>) = \<Union> (vars_term ` \<rho> ` vars_term t)"
    using vars_term_subst .
next
  fix t :: "('f, 'v) term"

  assume "vars_term t = {}"

  then show "\<forall>\<sigma>. t \<cdot> \<sigma> = t"
    by (simp add: ground_term_subst)
qed auto

locale term_properties =
  base_substitution +
  all_subst_ident_iff_ground +
  exists_non_ident_subst +
  grounding +
  finite_variables +
  renaming_variables +
  base_exists_ground_subst

global_interpretation "term": term_properties where
  comp_subst = "(\<circ>\<^sub>s)" and id_subst = Var and subst = "(\<cdot>)" and subst_update = fun_upd and
  subst_updates = subst_updates and apply_subst = apply_subst and vars = vars_term and
  to_ground = gterm_of_term and from_ground = term_of_gterm
proof unfold_locales
  fix t :: "('f, 'v) term"

  show "finite (vars_term t)"
    by simp
next
  fix t :: "('f, 'v) term"

  show "term.is_ground t \<longleftrightarrow> (\<forall>\<sigma>. t \<cdot> \<sigma> = t)"
  proof(induction t)
    case Var
    then show ?case
      by auto
  next
    case Fun

    moreover have "\<And>xs x \<sigma>. \<forall>\<sigma>. map (\<lambda>s. s \<cdot> \<sigma>) xs = xs \<Longrightarrow> x \<in> set xs \<Longrightarrow> x \<cdot> \<sigma> = x"
      by (metis list.map_ident map_eq_conv)

    ultimately show ?case
      by (auto simp: map_idI)
  qed
next
  fix t :: "('f, 'v) term" and ts :: "('f, 'v) term set"

  assume "finite ts" "\<not>term.is_ground t"

  then show "\<exists>\<sigma>. t \<cdot> \<sigma> \<noteq> t \<and> t \<cdot> \<sigma> \<notin> ts"
  proof(induction t arbitrary: ts)
    case (Var x)

    obtain t' where t': "t' \<notin> ts" "is_Fun t'"
      using Var.prems(1) finite_list by blast

    define \<sigma> :: "('f, 'v) subst" where "\<And>x. \<sigma> x = t'"

    have "Var x \<cdot> \<sigma> \<noteq> Var x"
      using t'
      unfolding \<sigma>_def
      by auto

    moreover have "Var x \<cdot> \<sigma> \<notin> ts"
      using t'
      unfolding \<sigma>_def
      by simp

    ultimately show ?case
      using Var
      by blast
  next
    case (Fun f args)

    obtain a where a: "a \<in> set args" and a_vars: "vars_term a \<noteq> {}"
      using Fun.prems
      by fastforce

    then obtain \<sigma> where
      \<sigma>: "a \<cdot> \<sigma> \<noteq> a" and
      a_\<sigma>_not_in_args: "a \<cdot> \<sigma> \<notin> \<Union> (set `  term.args ` ts)"
      by (metis Fun.IH Fun.prems(1) List.finite_set finite_UN finite_imageI)

    then have "Fun f args \<cdot> \<sigma> \<noteq> Fun f args"
       using a map_eq_conv
       by fastforce

    moreover have "Fun f args \<cdot> \<sigma> \<notin> ts"
      using a a_\<sigma>_not_in_args
      by auto

    ultimately show ?case
      using Fun
      by blast
  qed
next
   {
    fix t :: "('f, 'v) term"
    assume t_is_ground: "term.is_ground t"

    have "\<exists>g. term_of_gterm g = t"
    proof(intro exI)

      from t_is_ground
      show "term_of_gterm (gterm_of_term t) = t"
        by (induction t) (simp_all add: map_idI)

    qed
  }

  then show "{t :: ('f, 'v) term. term.is_ground t} = range term_of_gterm"
    by fastforce
next
  fix t\<^sub>G :: "'f gterm"

  show "gterm_of_term (term_of_gterm t\<^sub>G) = t\<^sub>G"
    by simp
next
  fix \<rho> :: "('f, 'v) subst" and t

  show is_renaming_iff: "term.is_renaming \<rho> \<longleftrightarrow> inj \<rho> \<and> (\<forall>x. \<exists>x'. \<rho> x = Var x')"
  proof (rule iffI)

    show "term.is_renaming \<rho> \<Longrightarrow> inj \<rho> \<and> (\<forall>x. \<exists>x'. \<rho> x = Var x')"
      unfolding term.is_renaming_def
      unfolding subst_compose_def inj_def
      by (metis subst_apply_eq_Var term.inject(1))
  next

    show "inj \<rho> \<and> (\<forall>x. \<exists>x'. \<rho> x = Var x') \<Longrightarrow> term.is_renaming \<rho>"
      using ex_inverse_of_renaming
      unfolding term.is_renaming_def is_Var_def
      by metis
  qed

  assume \<rho>: "term.is_renaming \<rho>"

  show "vars_term (t \<cdot> \<rho>) = term.rename \<rho> ` vars_term t"
  proof(induction t)
    case (Var x)
    have "\<rho> x = Var (term.rename \<rho> x)"
      using \<rho>
      unfolding term.rename_def[OF \<rho>] is_renaming_iff is_Var_def
      by (meson someI_ex)

    then show ?case
      by auto
  next
    case (Fun f ts)
    then show ?case
      by auto
  qed
next

  show "\<exists>t. term.is_ground t"
    by (metis vars_term_of_gterm)
qed simp


subsection \<open>Compatibility with First_Order_Term\<close> \<^marker>\<open>contributor \<open>Balazs Toth\<close>\<close> 

text \<open>Prefer @{thm [source] term.subst_id_subst} to @{thm [source] subst_apply_term_empty}.\<close>
declare subst_apply_term_empty[no_atp]

declare Term_Context.ground_vars_term_empty [simp del]

lemma term_context_ground_iff_term_is_ground [simp]: "ground t = term.is_ground t"
  by (induction t) simp_all

text \<open>The other direction does not hold!\<close>
lemma Term_is_renaming_if_is_renaming:
  assumes "term.is_renaming \<rho>"
  shows "Term.is_renaming \<rho>"
  using assms
  by (simp add: inj_on_def is_renaming_def term.is_renaming_iff is_Var_def)

lemma Term_subst_domain_eq_subst_domain [simp]: "Term.subst_domain \<sigma> = term.subst_domain \<sigma>"
  by (simp add: subst_domain_def term.subst_domain_def)

lemma Term_range_vars_eq_range_vars [simp]: "Term.range_vars \<sigma> = term.range_vars \<sigma>"
  by (simp add: range_vars_def term.range_vars_def)

lemma Unifiers_unifiers_Times_iff_is_unifier:
  assumes "finite X"
  shows "\<mu> \<in> Unifiers.unifiers (X \<times> X) \<longleftrightarrow> term.is_unifier \<mu> X "
  unfolding term.is_unifier_iff_if_finite[OF assms] unifiers_def
  by simp

lemma Unifiers_unifiers_Union_Times_iff_is_unifier_set:
  assumes "\<forall>X\<in> XX. finite X"
  shows "\<mu> \<in> Unifiers.unifiers (\<Union>X\<in>XX. X \<times> X) \<longleftrightarrow> term.is_unifier_set \<mu> XX "
  using Unifiers_unifiers_Times_iff_is_unifier assms
  unfolding term.is_unifier_set_def unifiers_def
  by fast

lemma Unifiers_is_mgu_Union_Times_iff_is_mgu:
  assumes "\<forall>X\<in> XX. finite X"
  shows "Unifiers.is_mgu \<mu> (\<Union>X\<in>XX. X \<times> X) \<longleftrightarrow> term.is_mgu \<mu> XX"
  unfolding term.is_mgu_def is_mgu_def 
  using Unifiers_unifiers_Union_Times_iff_is_unifier_set[OF assms]
  by (metis (lifting))

lemma Unifiers_is_imgu_Union_Times_iff_is_imgu:
  assumes "\<forall>X\<in> XX. finite X"
  shows "Unifiers.is_imgu \<mu> (\<Union>X\<in>XX. X \<times> X) \<longleftrightarrow> term.is_imgu \<mu> XX"
  unfolding term.is_imgu_def is_imgu_def
  using Unifiers_unifiers_Union_Times_iff_is_unifier_set[OF assms]
  by auto

lemma Unifiers_is_mgu_iff_is_imgu_image_set_prod: \<^marker>\<open>contributor \<open>Balazs Toth\<close>\<close>
  fixes \<mu> :: "('f, 'v) subst" and X :: "(('f, 'v) term \<times> ('f, 'v) term) set"
  shows "Unifiers.is_imgu \<mu> X \<longleftrightarrow> term.is_imgu \<mu> (set_prod ` X)"
proof (rule iffI)
  assume "is_imgu \<mu> X"

  moreover then have
    "\<forall>e\<in>X. fst e \<cdot> \<mu> = snd e \<cdot> \<mu>"
    "\<forall>\<tau> :: ('f, 'v) subst. (\<forall>e\<in>X. fst e \<cdot> \<tau> = snd e \<cdot> \<tau>) \<longrightarrow> \<tau> = \<mu> \<circ>\<^sub>s \<tau>"
    unfolding is_imgu_def unifiers_def
    by auto

  moreover then have
    "\<And>\<tau> :: ('f, 'v) subst. \<forall>e\<in>X. \<forall>t t'. e = (t, t') \<longrightarrow> card {t \<cdot> \<tau>, t' \<cdot> \<tau>} \<le> Suc 0 \<Longrightarrow> \<mu> \<circ>\<^sub>s \<tau> = \<tau>"
    by (metis Suc_n_not_le_n card_1_singleton_iff card_Suc_eq insert_iff prod.collapse)

  ultimately show "term.is_imgu \<mu> (set_prod ` X)"
    unfolding term.is_imgu_def term.is_unifier_set_def term.is_unifier_def
    by (auto split: prod.splits)
next
  assume is_imgu: "term.is_imgu \<mu> (set_prod ` X)"

  show "is_imgu \<mu> X"
  proof(unfold is_imgu_def unifiers_def, intro conjI ballI)

    show "\<mu> \<in> {\<sigma>. \<forall>e\<in>X. fst e \<cdot> \<sigma> = snd e \<cdot> \<sigma>}"
      using term.is_imgu_unifies[OF is_imgu]
      by fastforce
  next
    fix \<tau> :: "('f, 'v) subst"
    assume "\<tau> \<in> {\<sigma>. \<forall>e\<in>X. fst e \<cdot> \<sigma> = snd e \<cdot> \<sigma>}"

    then have "\<forall>e\<in>X. fst e \<cdot> \<tau> = snd e \<cdot> \<tau>"
      by blast

    then show "\<tau> = \<mu> \<circ>\<^sub>s \<tau>"
      using is_imgu
      unfolding term.is_imgu_def term.is_unifier_set_def
      by (smt (verit, del_insts) case_prod_conv empty_iff finite.emptyI finite.insertI image_iff
          insert_iff prod.collapse term.is_unifier_iff_if_finite)
  qed
qed


subsection \<open>Interpretations for IMGUs\<close> \<^marker>\<open>contributor \<open>Balazs Toth\<close>\<close> 

text \<open>We could also use @{locale base_variables_in_base_imgu},
      but would then require infinite variables.\<close>
global_interpretation "term": range_vars_subset_if_is_imgu where
  comp_subst = "(\<circ>\<^sub>s)" and id_subst = Var and subst = "(\<cdot>)" and subst_update = fun_upd and
  apply_subst = apply_subst and vars = vars_term
proof unfold_locales
  fix \<mu> :: "('f, 'v) subst" and XX

  assume imgu: "term.is_imgu \<mu> XX" and finite: "\<forall>X\<in>XX. finite X" "finite XX"

  then have is_imgu: "Unifiers.is_imgu \<mu> (\<Union>X\<in>XX. X \<times> X)"
    using Unifiers_is_imgu_Union_Times_iff_is_imgu[of "XX"]
    by simp

  have finite_prod: "finite (\<Union>X\<in>XX. X \<times> X)"
    using finite
    by blast

  have "(\<Union>e\<in>\<Union>X\<in>XX. X \<times> X. vars_term (fst e) \<union> vars_term (snd e)) = (\<Union>t\<in>\<Union>XX. vars_term t)"
    by fastforce

  then show "term.range_vars \<mu> \<subseteq> \<Union> (vars_term ` \<Union> XX)"
    using imgu_range_vars_subset[OF is_imgu finite_prod]
    by simp
qed

global_interpretation "term": exists_imgu where
  comp_subst = "(\<circ>\<^sub>s)" and id_subst = Var and subst = "(\<cdot>)" and subst_update = fun_upd and
  apply_subst = apply_subst and vars = vars_term
proof unfold_locales
  fix \<upsilon> :: "('f, 'v) subst" and t t'
  assume unifier: "t \<cdot> \<upsilon> = t' \<cdot> \<upsilon>"

  show "\<exists>\<mu>. term.is_imgu \<mu> {{t, t'}}"
  proof (rule exI)

    show "term.is_imgu (the_mgu t t') {{t, t'}}"
      using the_mgu_is_imgu unifier
      unfolding Unifiers_is_mgu_iff_is_imgu_image_set_prod
      by auto
  qed
qed


subsection \<open>Additional lemmas\<close>

lemma infinite_terms [intro]: "infinite (UNIV :: ('f, 'v) term set)" \<^marker>\<open>contributor \<open>Balazs Toth\<close>\<close> 
proof -
  have "infinite (UNIV :: ('f, 'v) term list set)"
    using infinite_UNIV_listI .

  then have "\<And>f :: 'f. infinite ((Fun f) ` (UNIV :: ('f, 'v) term list set))"
    by (meson finite_imageD injI term.inject(2))

  then show "infinite (UNIV :: ('f, 'v) term set)"
    using infinite_super top_greatest 
    by blast
qed

lemma is_renaming_iff_ex_inj_fun_on_vars: "term.is_renaming \<rho> \<longleftrightarrow> (\<exists>f. inj f \<and> \<rho> = Var \<circ> f)"
proof (rule iffI)
  assume "term.is_renaming \<rho>"

  hence "inj \<rho>" and all_Var: "\<forall>x. is_Var (\<rho> x)"
    unfolding term.is_renaming_iff is_Var_def
    by simp_all

  from all_Var obtain f where "\<forall>x. \<rho> x = Var (f x)"
    by (metis comp_apply term.collapse(1))

  hence "\<rho> = Var \<circ> f"
    using \<open>\<forall>x. \<rho> x = Var (f x)\<close>
    by (intro ext) simp

  moreover have "inj f"
      using \<open>inj \<rho>\<close> unfolding \<open>\<rho> = Var \<circ> f\<close>
      using inj_on_imageI2 by metis

  ultimately show "\<exists>f. inj f \<and> \<rho> = Var \<circ> f"
    by metis
next

  show "\<exists>f. inj f \<and> \<rho> = Var \<circ> f \<Longrightarrow> term.is_renaming \<rho>"
    unfolding term.is_renaming_iff comp_apply inj_def
    by auto
qed

end
