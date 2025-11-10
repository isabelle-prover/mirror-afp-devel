theory IsaFoR_Nonground_Term
  imports
    "Regular_Tree_Relations.Ground_Terms"
    Nonground_Term
    Abstract_Substitution.Substitution_First_Order_Term
begin

text \<open>Prefer @{thm [source] term_subst.subst_id_subst} to @{thm [source] subst_apply_term_empty}.\<close>
declare subst_apply_term_empty[no_atp]

global_interpretation "term": base_functional_substitution where
  comp_subst = "(\<circ>\<^sub>s)" and id_subst = Var and subst = "(\<cdot>)" and vars = vars_term
proof unfold_locales
  fix t :: "('f, 'v) term"  and \<sigma> \<tau> :: "('f, 'v) subst"

  assume "\<And>x. x \<in> vars_term t \<Longrightarrow> \<sigma> x = \<tau> x"

  then show "t \<cdot> \<sigma> = t \<cdot> \<tau>"
    by (rule term_subst_eq)
next

  show "\<exists>t. is_ground_trm t"
    using vars_term_of_gterm
    by metis
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
qed

global_interpretation "term" : nonground_term where
  comp_subst = "(\<circ>\<^sub>s)" and Var = Var and term_subst = "(\<cdot>)" and term_vars = vars_term and
  term_to_ground = gterm_of_term and term_from_ground = term_of_gterm
proof unfold_locales
  fix t :: "('f, 'v) term"

  show "finite (vars_term t)"
    by simp
next
  fix t :: "('f, 'v) term"

  show "(vars_term t = {}) \<longleftrightarrow> (\<forall>\<sigma>. t \<cdot> \<sigma> = t)"
    using is_ground_trm_iff_ident_forall_subst .
next
  fix t :: "('f, 'v) term" and ts :: "('f, 'v) term set"

  assume "finite ts" "vars_term t \<noteq> {}"

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
      by (metis a subsetI term.set_intros(4) term_subst.comp_subst.left.action_neutral
          vars_term_subset_subst_eq)

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
    assume t_is_ground: "is_ground_trm t"

    have "\<exists>g. term_of_gterm g = t"
    proof(intro exI)

      from t_is_ground
      show "term_of_gterm (gterm_of_term t) = t"
        by (induction t) (simp_all add: map_idI)

    qed
  }

  then show "{t :: ('f, 'v) term. is_ground_trm t} = range term_of_gterm"
    by fastforce
next
  fix t\<^sub>G :: "'f gterm"

  show "gterm_of_term (term_of_gterm t\<^sub>G) = t\<^sub>G"
    by simp
next
  fix \<rho> :: "('f, 'v) subst"

  show "term_subst.is_renaming \<rho> \<longleftrightarrow> inj \<rho> \<and> (\<forall>x. \<exists>x'. \<rho> x = Var x')"
    using term_subst_is_renaming_iff
    unfolding is_Var_def .
next
   fix \<rho> :: "('f, 'v) subst" and t
  assume \<rho>: "term_subst.is_renaming \<rho>"
  show "vars_term (t \<cdot> \<rho>) = term.rename \<rho> ` vars_term t"
  proof(induction t)
    case (Var x)
    have "\<rho> x = Var (term.rename \<rho> x)"
      using \<rho>
      unfolding term.rename_def[OF \<rho>] term_subst_is_renaming_iff is_Var_def
      by (meson someI_ex)

    then show ?case
      by auto
  next
    case (Fun f ts)
    then show ?case
      by auto
  qed
next
  fix t :: "('f, 'v) term" and \<mu> :: "('f, 'v) subst" and unifications

  assume imgu:
    "term_subst.is_imgu \<mu> unifications"
    "\<forall>unification\<in>unifications. finite unification"
    "finite unifications"

  show "vars_term (t \<cdot> \<mu>) \<subseteq> vars_term t \<union> \<Union> (vars_term ` \<Union> unifications)"
    using range_vars_subset_if_is_imgu[OF imgu] vars_term_subst_apply_term_subset
    by fastforce
qed

lemma term_context_ground_iff_term_is_ground [simp]: "Term.ground t = term.is_ground t"
  by (rule Term.ground_vars_term_empty)

declare Term_Context.ground_vars_term_empty [simp del]

lemma infinite_terms [intro]: "infinite (UNIV :: ('f, 'v) term set)"
proof -
  have "infinite (UNIV :: ('f, 'v) term list set)"
    using infinite_UNIV_listI .

  then have "\<And>f :: 'f. infinite ((Fun f) ` (UNIV :: ('f, 'v) term list set))"
    by (meson finite_imageD injI term.inject(2))

  then show "infinite (UNIV :: ('f, 'v) term set)"
    using infinite_super top_greatest 
    by blast
qed

end
