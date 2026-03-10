theory Substitution_HOL_ex_Unification
  imports
    Based_Substitution
    "HOL-ex.Unification"
    Fresh_Identifiers.Fresh
begin

(* TODO: Make sure to interpret everything that is interpreted for other representation *)

section \<open>Substitutions for first order terms as binary tree\<close>

no_notation Comb (infix \<open>\<cdot>\<close> 60)

quotient_type 'v subst = "('v \<times> 'v trm) list" / "(\<doteq>)"
proof (rule equivpI)
  show "reflp (\<doteq>)"
    using reflpI subst_refl by metis
next
  show "symp (\<doteq>)"
    using sympI subst_sym by metis
next
  show "transp (\<doteq>)"
    using transpI subst_trans by metis
qed


subsection \<open>Substitution monoid\<close>

lift_definition subst_comp :: "'v subst \<Rightarrow> 'v subst \<Rightarrow> 'v subst" (infixl \<open>\<odot>\<close> 67)
  is Unification.comp
  using Unification.subst_cong .

lift_definition subst_id :: "'v subst"
  is "[]" .

global_interpretation subst_comp: monoid subst_comp subst_id
proof unfold_locales
  fix \<sigma> \<sigma>' \<sigma>'' :: "'v subst"

  show "\<sigma> \<odot> \<sigma>' \<odot> \<sigma>'' = \<sigma> \<odot> (\<sigma>' \<odot>  \<sigma>'')"
    by transfer auto
next
  fix \<sigma> :: "'v subst"

  show "subst_id \<odot> \<sigma> = \<sigma>"
    by transfer simp

  show "\<sigma> \<odot> subst_id = \<sigma>"
    by transfer simp
qed


subsection \<open>Transfer definitions and lemmas from HOL-ex.Unification\<close> \<^marker>\<open>contributor \<open>Balazs Toth\<close>\<close> 

lift_definition subst_apply :: "'v trm \<Rightarrow> 'v subst \<Rightarrow> 'v trm" (infixl \<open>\<cdot>\<close> 61)
  is Unification.subst
  using Unification.subst_eq_dest .

lift_definition subst_domain :: "'v subst \<Rightarrow> 'v set"
  is Unification.subst_domain
  by (metis (no_types, lifting) ext subst_domain_def subst_eq_def)

lift_definition range_vars :: "'v subst \<Rightarrow> 'v set"
  is Unification.range_vars
  by (metis (no_types, lifting) ext range_vars_def subst_eq_def)

lift_definition Unifier :: "'v subst \<Rightarrow> 'v trm \<Rightarrow> 'v trm \<Rightarrow> bool"
  is Unification.Unifier
  unfolding subst_eq_def Unifier_def
  by auto

lift_definition IMGU :: "'v subst \<Rightarrow> 'v trm \<Rightarrow> 'v trm \<Rightarrow> bool"
  is Unification.IMGU
  unfolding subst_eq_def IMGU_def
  by (simp add: Unification.Unifier_def)

lift_definition unify :: "'v trm \<Rightarrow> 'v trm \<Rightarrow> 'v subst option"
  is Unification.unify .

lemma unify_eq_Some_if_Unifier:
  assumes "Unifier \<sigma> t t'"
  shows "\<exists>\<tau>. unify t t' = Some \<tau>"
proof -
  obtain rep_\<sigma> where \<sigma>_def: "\<sigma> = abs_subst rep_\<sigma>"
    by transfer simp

  from assms have "Unification.Unifier rep_\<sigma> t t'"
    unfolding \<sigma>_def
    by transfer

  then obtain rep_\<tau> where "Unification.unify t t' = Some rep_\<tau>"
    using Unification.unify_eq_Some_if_Unifier
    by blast

  then have "unify t t' = Some (abs_subst rep_\<tau>)"
    by (simp add: unify.abs_eq)

  thus ?thesis
    by blast
qed

lemma unify_computes_IMGU:
  assumes "unify t t' = Some \<sigma>"
  shows "IMGU \<sigma> t t'"
proof -
  obtain rep_\<sigma> where \<sigma>_def: "\<sigma> = abs_subst rep_\<sigma>"
    by transfer simp

  have "map_option abs_subst (Unification.unify t t') = Some (abs_subst rep_\<sigma>)"
    using assms \<sigma>_def
    by (simp add: unify.abs_eq)

  then obtain rep_\<sigma>' where
    "Unification.unify t t' = Some rep_\<sigma>'" and
    rep_\<sigma>': "abs_subst rep_\<sigma>' = abs_subst rep_\<sigma>"
    by (cases "Unification.unify t t'") auto

  then have "Unification.IMGU rep_\<sigma>' t t'"
    using Unification.unify_computes_IMGU
    by blast

  hence "IMGU (abs_subst rep_\<sigma>') t t'"
    by transfer

  thus "IMGU \<sigma> t t'"
    using rep_\<sigma>' \<sigma>_def
    by simp
qed

lift_definition subst_update :: "'v \<times> 'v trm \<Rightarrow> 'v subst \<Rightarrow> 'v subst"
  is "(#)"
proof -
  fix update and \<sigma> \<sigma>' :: "('v \<times> 'v trm) list"
  assume subst_eq: "\<sigma> \<doteq> \<sigma>'"

  {
    fix t 
    have "t \<lhd> update # \<sigma> = t \<lhd> update # \<sigma>'"
    proof (induction t)
      case Var

      then show ?case
        using subst_eq
        unfolding subst_eq_def
        by (metis assoc.simps(2) prod.exhaust subst.simps(1))     
    qed simp_all
  }

  then show "update # \<sigma> \<doteq> update # \<sigma>' "
    unfolding subst_eq_def
    by satx
qed

abbreviation (input) is_ground where
  "is_ground t \<equiv> vars_of t = {}"

subsection \<open>Base Substitution\<close> \<^marker>\<open>contributor \<open>Balazs Toth\<close>\<close> 

global_interpretation "term": base_substitution where
  comp_subst = subst_comp and id_subst = subst_id and subst = subst_apply and vars = vars_of and
  apply_subst = "\<lambda>x \<sigma>. subst_apply (Var x) \<sigma>" and is_ground = is_ground
proof unfold_locales
  fix t and \<sigma> \<sigma>' :: "'v subst"

  show "t \<cdot> \<sigma> \<odot> \<sigma>' = t \<cdot> \<sigma> \<cdot> \<sigma>'"
    by transfer simp
next
  fix t :: "'v trm"

  show "t \<cdot> subst_id = t"
    by transfer simp
next
  fix t :: "'v trm"

  assume "vars_of t = {}"

  then show "\<forall>\<sigma>. t \<cdot> \<sigma> = t"
    by transfer (metis agreement empty_iff subst_Nil)
next
  fix x :: 'v

  show "vars_of (Var x \<cdot> subst_id) = {x}"
    by transfer simp
next
  fix \<sigma> \<sigma>' :: "'v subst" and x

  show "Var x \<cdot> \<sigma> \<odot> \<sigma>' = Var x \<cdot> \<sigma> \<cdot> \<sigma>'"
    by transfer simp
next
  fix t and \<sigma> :: "'v subst"

  show "vars_of (t \<cdot> \<sigma>) = \<Union> (vars_of ` (\<lambda>x. Var x \<cdot> \<sigma>) ` vars_of t)"
    by transfer (simp add: vars_of_subst_conv_Union)
next
  fix t and \<gamma> :: "'v subst"
  assume "is_ground (t \<cdot> \<gamma>)"

  then show "\<forall>x\<in>vars_of t. is_ground (Var x \<cdot> \<gamma>)"
    by transfer (metis occs_vars_subset subset_empty subst_mono vars_iff_occseq)
qed simp


subsection \<open>Substitution Properties\<close> \<^marker>\<open>contributor \<open>Balazs Toth\<close>\<close> 

global_interpretation "term": create_renaming where
  comp_subst = subst_comp and id_subst = subst_id and subst = subst_apply and vars = vars_of and
  is_ground = is_ground and apply_subst = "\<lambda>x \<sigma>. subst_apply (Var x) \<sigma>" and
  subst_update = "\<lambda>\<sigma> x update. subst_update (x, update) \<sigma>" and
  base_subst = subst_apply and base_vars = vars_of and base_is_ground = is_ground
proof unfold_locales
  fix \<sigma> x and update :: "'v trm"
  
  show "Var x \<cdot> subst_update (x, update) \<sigma> = update"
    by transfer simp
next
  fix \<sigma> :: "'v subst" and x y :: 'v and update
  assume "x \<noteq> y"

  then show "Var x \<cdot> subst_update (y, update) \<sigma> = Var x \<cdot> \<sigma>"
    by transfer simp
next
  fix x :: "'v" and t update and \<sigma> :: "'v subst"
  assume "x \<notin> vars_of t"

  then show "t \<cdot> subst_update (x, update) \<sigma> = t \<cdot> \<sigma>"
    by transfer (simp add: repl_invariance)
next
  fix \<sigma> :: "'v subst" and x

  show "subst_update (x, Var x \<cdot> \<sigma>) \<sigma> = \<sigma>"
    by transfer (simp add: agreement subst_eq_intro)
next
  fix \<sigma>  :: "'v subst" and x a b

  show "subst_update (x, b)(subst_update (x, a) \<sigma>) = subst_update (x, b) \<sigma>"
    by transfer (simp add: agreement subst_eq_def)
next
  fix \<gamma> :: "'v subst" and u t :: "'v trm" and x
  assume "is_ground u" "is_ground (t \<cdot> \<gamma>)" "x \<in> vars_of t"

  then show "is_ground (t \<cdot> subst_update (x, u) \<gamma>)"
  proof (induction t)
    case (Var x')
    
    then show ?case
      by transfer simp
  next
    case (Const x')

    then show ?case 
      by transfer simp
  next
    case (Comb t1 t2)

    then show ?case
      by transfer (fastforce simp: repl_invariance)
  qed
next
  fix us us' :: "('v \<times> 'v trm) list"

  let ?upd = "\<lambda>(x, b). subst_update (x, b)"

  assume "\<And>x. Var x \<cdot> fold ?upd us subst_id \<odot> fold ?upd us' subst_id = Var x \<cdot> subst_id"

  then show "fold ?upd us subst_id \<odot> fold ?upd us' subst_id = subst_id"
    by transfer (use agreement in blast)
qed 

global_interpretation "term": finite_variables where
  comp_subst = subst_comp and id_subst = subst_id and subst = subst_apply and vars = vars_of and
  apply_subst = "\<lambda>x \<sigma>. subst_apply (Var x) \<sigma>" and is_ground = is_ground
proof unfold_locales
  fix t :: "'v trm"

  show "finite (vars_of t)"
    by blast
qed

text\<open>We could also prove @{locale all_subst_ident_iff_ground} and
     @{locale exists_non_ident_subst} directly without needing infinite variables.\<close>
global_interpretation "term": base_exists_non_ident_subst where
  comp_subst = subst_comp and id_subst = "subst_id :: 'v :: infinite subst" and
  subst = subst_apply and vars = vars_of and is_ground = is_ground and
  subst_update = "\<lambda>\<sigma> x update. subst_update (x, update) \<sigma>" and
  apply_subst = "\<lambda>x \<sigma>. subst_apply (Var x) \<sigma>" 
proof unfold_locales
  fix t :: "'v trm"
  
  show "is_ground t = (\<forall>\<sigma>. t \<cdot> \<sigma> = t)"
    by transfer (metis agreement all_not_in_conv remove_var subst_Nil vars_of.simps(2))
   
next

  show "infinite (UNIV :: 'v set)"
    using infinite_UNIV
    by simp
qed

global_interpretation "term": renaming_variables where
  comp_subst = subst_comp and id_subst = "subst_id :: 'v subst" and
  subst = subst_apply and vars = vars_of and is_ground = is_ground and
  apply_subst = "\<lambda>x \<sigma>. subst_apply (Var x) \<sigma>" 
proof (unfold_locales, intro conjI)
  fix \<rho> :: "'v subst" and t
  assume \<rho>: "term.is_renaming \<rho>"

  then show "inj (\<lambda>x. Var x \<cdot> \<rho>)"
    unfolding inj_def term.is_renaming_def
    by (metis term.subst_inv trm.inject(1))

  show rename: "\<forall>x. \<exists>x'. Var x \<cdot> \<rho> = Var x' \<cdot> subst_id"
    using \<rho> term.subst_inv term.comp_subst_iff
    unfolding term.is_renaming_def subst_apply.rep_eq 
    by (metis subst_apply_eq_Var)

  show "vars_of (t \<cdot> \<rho>) = term.rename \<rho> ` vars_of t"
  proof (induction t)
    case (Var y)

    have "Var y \<cdot> \<rho> = Var (term.rename \<rho> y)"
      using rename someI_ex[of "\<lambda>x'. Var y \<cdot> \<rho> = Var x' \<cdot> subst_id"] 
      unfolding term.rename_def[OF \<rho>]
      by auto

    then show ?case
      by simp
  next
    case (Const c)

    then show ?case
      by auto
  next
    case (Comb t1 t2)

    then show ?case
      by (simp add: image_Un subst_apply.rep_eq)
  qed
qed


subsection \<open>Compatibility with HOL-ex.Unification\<close> \<^marker>\<open>contributor \<open>Balazs Toth\<close>\<close> 

lemma subst_domain_eq_term_subst_domain [simp]: "subst_domain \<sigma> = term.subst_domain \<sigma>"
  unfolding term.subst_domain_def 
  by transfer (simp add: Unification.subst_domain_def)

lemma range_vars_eq_term_range_vars [simp]: "range_vars \<sigma> = term.range_vars \<sigma>"
  unfolding term.range_vars_def subst_domain_eq_term_subst_domain[symmetric]
  by transfer (auto simp: Unification.range_vars_def Unification.subst_domain_def)

lemma Unifier_iff_term_is_unifier:
   "Unifier \<mu> t t' \<longleftrightarrow> term.is_unifier \<mu> {t, t'}"
  unfolding term.is_unifier_def term.subst_set_def
  by transfer (use Unification.Unifier_def subset_singleton_iff in fastforce)

lemma Unifier_iff_is_unifier_set:
   "Unifier \<mu> t t' \<longleftrightarrow> term.is_unifier_set \<mu> {{t, t'}}"
  using Unifier_iff_term_is_unifier
  unfolding term.is_unifier_set_def
  by auto

lemma IMGU_iff_term_is_mgu:
  "IMGU \<mu> t t' \<longleftrightarrow> term.is_imgu \<mu> {{t, t'}}" 
  unfolding term.is_imgu_def Unifier_iff_is_unifier_set[symmetric]
  by transfer (meson Unification.IMGU_def subst_sym)

lemma IMGU_range_vars_subset:
  assumes "IMGU \<mu> t u"
  shows "range_vars \<mu> \<subseteq> vars_of t \<union> vars_of u"
  using assms
  by transfer (rule IMGU_range_vars_subset)


subsection \<open>Interpretations for IMGUs\<close> \<^marker>\<open>contributor \<open>Balazs Toth\<close>\<close> 

text\<open>We could also prove @{locale range_vars_subset_if_is_imgu}
     without needing infinite variables.\<close>
global_interpretation "term": base_variables_in_base_imgu where
  comp_subst = subst_comp and id_subst = "subst_id :: 'v :: infinite subst" and
  subst = subst_apply and vars = vars_of and is_ground = is_ground and
  subst_update = "\<lambda>\<sigma> x update. subst_update (x, update) \<sigma>" and
  apply_subst = "\<lambda>x \<sigma>. subst_apply (Var x) \<sigma>"
proof(unfold_locales, transfer)
  fix t :: "'v trm" and \<sigma>

  show "\<exists>x. t \<lhd> \<sigma> = Var x \<lhd> [] \<Longrightarrow> \<exists>x. t = Var x \<lhd> []"
    using subst_apply_eq_Var 
    by fastforce
qed

global_interpretation "term": exists_imgu where
  comp_subst = subst_comp and id_subst = subst_id and subst = subst_apply and vars = vars_of and
  is_ground = is_ground and apply_subst = "\<lambda>x \<sigma>. subst_apply (Var x) \<sigma>"
proof unfold_locales
  fix \<upsilon> and t t' :: "'v trm"
  assume "t \<cdot> \<upsilon> = t' \<cdot> \<upsilon>"

  then have "Unifier \<upsilon> t t'"
    by transfer (simp add: Unification.Unifier_def)

  then obtain \<mu> where "unify t t' = Some \<mu>"
    using unify_eq_Some_if_Unifier
    by blast

  then have IMGU: "IMGU \<mu> t t'"
    by (simp add: unify_computes_IMGU)

  show "\<exists>\<mu>. term.is_imgu \<mu> {{t, t'}}"
  proof (rule exI)

    show "term.is_imgu \<mu> {{t, t'}}"
      using IMGU IMGU_iff_term_is_mgu 
      by auto
  qed
qed
  
end
