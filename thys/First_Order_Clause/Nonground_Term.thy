theory Nonground_Term
 imports
    Abstract_Substitution.Substitution_First_Order_Term
    Abstract_Substitution.Functional_Substitution_Lifting
    Ground_Term_Extra
begin

no_notation subst_compose (infixl "\<circ>\<^sub>s" 75)
notation subst_compose (infixl "\<odot>" 75)

no_notation subst_apply_term (infixl "\<cdot>" 67)
notation subst_apply_term (infixl "\<cdot>t" 67)

text \<open>Prefer @{thm [source] term_subst.subst_id_subst} to @{thm [source] subst_apply_term_empty}.\<close>
declare subst_apply_term_empty[no_atp]

section \<open>Nonground Terms and Substitutions\<close>

type_synonym 'f ground_term = "'f gterm"


subsection \<open>Unified naming\<close>

locale vars_def =
  fixes vars_def :: "'expr \<Rightarrow> 'var"
begin

abbreviation "vars \<equiv> vars_def"

end

locale grounding_def =
  fixes
    to_ground_def :: "'expr \<Rightarrow> 'expr\<^sub>G" and
    from_ground_def :: "'expr\<^sub>G \<Rightarrow> 'expr"
begin

abbreviation "to_ground \<equiv> to_ground_def"

abbreviation "from_ground \<equiv> from_ground_def"

end

subsection \<open>Term\<close>

locale nonground_term_properties =
  base_functional_substitution +
  finite_variables +
  all_subst_ident_iff_ground

locale term_grounding =
  variables_in_base_imgu where base_vars = vars and base_subst = subst +
  grounding

(* TODO: Is there a better way for this? *)
locale nonground_term
begin

sublocale vars_def where vars_def = vars_term .

sublocale grounding_def where
  to_ground_def = gterm_of_term and from_ground_def = term_of_gterm .

lemma infinite_terms [intro]: "infinite (UNIV :: ('f, 'v) term set)"
proof-
  have "infinite (UNIV :: ('f, 'v) term list set)"
    using infinite_UNIV_listI.

  then have "\<And>f :: 'f. infinite ((Fun f) ` (UNIV :: ('f, 'v) term list set))"
    by (meson finite_imageD injI term.inject(2))

  then show "infinite (UNIV :: ('f, 'v) term set)"
    using infinite_super top_greatest by blast
qed

sublocale nonground_term_properties where
  subst = "(\<cdot>t)" and id_subst = Var and comp_subst = "(\<odot>)" and
  vars = "vars :: ('f, 'v) term \<Rightarrow> 'v set"
proof unfold_locales
  fix t :: "('f, 'v) term"  and \<sigma> \<tau> :: "('f, 'v) subst"
  assume "\<And>x. x \<in> vars t \<Longrightarrow> \<sigma> x = \<tau> x"
  then show "t \<cdot>t \<sigma> = t \<cdot>t \<tau>"
    by(rule term_subst_eq)
next
  fix t :: "('f, 'v) term"
  show "finite (vars t)"
    by simp
next
  fix t :: "('f, 'v) term"
  show "(vars t = {}) = (\<forall>\<sigma>. t \<cdot>t \<sigma> = t)"
    using is_ground_trm_iff_ident_forall_subst.
next
  fix t :: "('f, 'v) term" and ts :: "('f, 'v) term set"

  assume "finite ts" "vars t \<noteq> {}"
  then show "\<exists>\<sigma>. t \<cdot>t \<sigma> \<noteq> t \<and> t \<cdot>t \<sigma> \<notin> ts"
  proof(induction t arbitrary: ts)
    case (Var x)

    obtain t' where t': "t' \<notin> ts" "is_Fun t'"
      using Var.prems(1) finite_list by blast

    define \<sigma> :: "('f, 'v) subst" where "\<And>x. \<sigma> x = t'"

    have "Var x \<cdot>t \<sigma> \<noteq> Var x"
      using t'
      unfolding \<sigma>_def
      by auto

    moreover have "Var x \<cdot>t \<sigma> \<notin> ts"
      using t'
      unfolding \<sigma>_def
      by simp

    ultimately show ?case
      using Var
      by blast
  next
    case (Fun f args)

    obtain a where a: "a \<in> set args" and a_vars: "vars a \<noteq> {}"
      using Fun.prems
      by fastforce

    then obtain \<sigma> where
      \<sigma>: "a \<cdot>t \<sigma> \<noteq> a" and
      a_\<sigma>_not_in_args: "a \<cdot>t \<sigma> \<notin> \<Union> (set `  term.args ` ts)"
      by (metis Fun.IH Fun.prems(1) List.finite_set finite_UN finite_imageI)

    then have "Fun f args \<cdot>t \<sigma> \<noteq> Fun f args"
      by (metis a subsetI term.set_intros(4) term_subst.comp_subst.left.action_neutral
          vars_term_subset_subst_eq)

    moreover have "Fun f args \<cdot>t \<sigma> \<notin> ts"
      using a a_\<sigma>_not_in_args
      by auto

    ultimately show ?case
      using Fun
      by blast
  qed
next
  fix t :: "('f, 'v) term" and \<rho> :: "('f, 'v) subst"

  show "vars (t \<cdot>t \<rho>) = \<Union> (vars ` \<rho> ` vars t)"
    using vars_term_subst.
next
  show "\<exists>t. vars t = {}"
    using vars_term_of_gterm
    by metis
next
  fix x :: 'v
  show "vars (Var x) = {x}"
    by simp
next
  fix \<sigma> \<sigma>' :: "('f, 'v) subst" and x
  show "(\<sigma> \<odot> \<sigma>') x = \<sigma> x \<cdot>t \<sigma>'"
    unfolding subst_compose_def ..
qed

sublocale renaming_variables where
  vars = "vars :: ('f, 'v) term \<Rightarrow> 'v set" and subst = "(\<cdot>t)" and id_subst = Var and
  comp_subst = "(\<odot>)"
proof unfold_locales
  fix \<rho> :: "('f, 'v) subst"

  show "term_subst.is_renaming \<rho> \<longleftrightarrow> inj \<rho> \<and> (\<forall>x. \<exists>x'. \<rho> x = Var x')"
    using term_subst_is_renaming_iff
    unfolding is_Var_def.
next
  fix \<rho> :: "('f, 'v) subst" and t
  assume \<rho>: "term_subst.is_renaming \<rho>"
  show "vars (t \<cdot>t \<rho>) = rename \<rho> ` vars t"
  proof(induction t)
    case (Var x)
    have "\<rho> x = Var (rename \<rho> x)"
      using \<rho>
      unfolding rename_def[OF \<rho>] term_subst_is_renaming_iff is_Var_def
      by (meson someI_ex)

    then show ?case
      by auto
  next
    case (Fun f ts)
    then show ?case
      by auto
  qed
qed

sublocale term_grounding where
  subst = "(\<cdot>t)" and id_subst = Var and comp_subst = "(\<odot>)" and
  vars = "vars :: ('f, 'v) term \<Rightarrow> 'v set" and from_ground = from_ground and
  to_ground = to_ground
proof unfold_locales
   fix t :: "('f, 'v) term" and \<mu> :: "('f, 'v) subst" and unifications

  assume imgu:
    "term_subst.is_imgu \<mu> unifications"
    "\<forall>unification\<in>unifications. finite unification"
    "finite unifications"

  show "vars (t \<cdot>t \<mu>) \<subseteq> vars t \<union> \<Union> (vars ` \<Union> unifications)"
    using range_vars_subset_if_is_imgu[OF imgu] vars_term_subst_apply_term_subset
    by fastforce
next
  {
    fix t :: "('f, 'v) term"
    assume t_is_ground: "is_ground t"

    have "\<exists>g. from_ground g = t"
    proof(intro exI)

      from t_is_ground
      show "from_ground (to_ground t) = t"
        by(induction t)(simp_all add: map_idI)

    qed
  }

  then show "{t :: ('f, 'v) term. is_ground t} = range from_ground"
    by fastforce
next
  fix t\<^sub>G :: "('f) ground_term"
  show "to_ground (from_ground t\<^sub>G) = t\<^sub>G"
    by simp
qed

lemma term_context_ground_iff_term_is_ground [simp]: "Term_Context.ground t = is_ground t"
  by(induction t) simp_all

declare Term_Context.ground_vars_term_empty [simp del]

lemma obtain_ground_fun:
  assumes "is_ground t"
  obtains f ts where "t = Fun f ts"
  using assms
  by(cases t) auto

end

subsection \<open>Setup for lifting from terms\<close>

locale lifting =
  based_functional_substitution_lifting +
  all_subst_ident_iff_ground_lifting +
  grounding_lifting +
  renaming_variables_lifting +
  variables_in_base_imgu_lifting

locale term_based_lifting =
  "term": nonground_term +
  lifting where
  comp_subst = "(\<odot>)" and id_subst = Var and base_subst = "(\<cdot>t)" and base_vars = term.vars

end
