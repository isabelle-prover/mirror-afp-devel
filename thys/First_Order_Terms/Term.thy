(*
Author:  Christian Sternagel <c.sternagel@gmail.com>
Author:  René Thiemann <rene.thiemann@uibk.ac.at>
License: LGPL
*)
section \<open>First-Order Terms\<close>

theory Term
  imports 
    Main
    "HOL-Library.Multiset"
begin

datatype (funs_term : 'f, vars_term : 'v) "term" =
  is_Var: Var (the_Var: 'v) |
  Fun 'f (args : "('f, 'v) term list")
where
  "args (Var _) = []"

abbreviation "is_Fun t \<equiv> \<not> is_Var t"

lemma is_VarE [elim]:
  "is_Var t \<Longrightarrow> (\<And>x. t = Var x \<Longrightarrow> P) \<Longrightarrow> P"
  by (cases t) auto

lemma is_FunE [elim]:
  "is_Fun t \<Longrightarrow> (\<And>f ts. t = Fun f ts \<Longrightarrow> P) \<Longrightarrow> P"
  by (cases t) auto

lemma inj_on_Var[simp]: \<^marker>\<open>contributor \<open>Martin Desharnais\<close>\<close>
  "inj_on Var A"
  by (rule inj_onI) simp

lemma member_image_the_Var_image_subst: \<^marker>\<open>contributor \<open>Martin Desharnais\<close>\<close>
  assumes is_var_\<sigma>: "\<forall>x. is_Var (\<sigma> x)"
  shows "x \<in> the_Var ` \<sigma> ` V \<longleftrightarrow> Var x \<in> \<sigma> ` V"
  using is_var_\<sigma> image_iff
  by (metis (no_types, opaque_lifting) term.collapse(1) term.sel(1))

lemma image_the_Var_image_subst_renaming_eq: \<^marker>\<open>contributor \<open>Martin Desharnais\<close>\<close>
  assumes is_var_\<sigma>: "\<forall>x. is_Var (\<rho> x)"
  shows "the_Var ` \<rho> ` V = (\<Union>x \<in> V. vars_term (\<rho> x))"
proof (rule Set.equalityI; rule Set.subsetI)
  from is_var_\<sigma> show "\<And>x. x \<in> the_Var ` \<rho> ` V \<Longrightarrow> x \<in> (\<Union>x\<in>V. vars_term (\<rho> x))"
    using term.set_sel(3) by force
next
  from is_var_\<sigma> show "\<And>x. x \<in> (\<Union>x\<in>V. vars_term (\<rho> x)) \<Longrightarrow> x \<in> the_Var ` \<rho> ` V"
    by (smt (verit, best) Term.term.simps(17) UN_iff image_eqI singletonD term.collapse(1))
qed

text \<open>The variables of a term as multiset.\<close>
fun vars_term_ms :: "('f, 'v) term \<Rightarrow> 'v multiset"
  where
    "vars_term_ms (Var x) = {#x#}" |
    "vars_term_ms (Fun f ts) = \<Sum>\<^sub># (mset (map vars_term_ms ts))"

lemma set_mset_vars_term_ms [simp]:
  "set_mset (vars_term_ms t) = vars_term t"
  by (induct t) auto


text \<open>Reorient equations of the form @{term "Var x = t"} and @{term "Fun f ss = t"} to facilitate
  simplification.\<close>
setup \<open>
  Reorient_Proc.add
    (fn Const (@{const_name Var}, _) $ _ => true | _ => false)
  #> Reorient_Proc.add
    (fn Const (@{const_name Fun}, _) $ _ $ _ => true | _ => false)
\<close>

simproc_setup reorient_Var ("Var x = t") = \<open>K Reorient_Proc.proc\<close>
simproc_setup reorient_Fun ("Fun f ss = t") = \<open>K Reorient_Proc.proc\<close>

text \<open>The \emph{root symbol} of a term is defined by:\<close>
fun root :: "('f, 'v) term \<Rightarrow> ('f \<times> nat) option"
where
  "root (Var x) = None" |
  "root (Fun f ts) = Some (f, length ts)"

lemma finite_vars_term [simp]:
  "finite (vars_term t)"
  by (induct t) simp_all

lemma finite_Union_vars_term:
  "finite (\<Union>t \<in> set ts. vars_term t)"
  by auto

text \<open>We define the evaluation of terms, under interpretation of function symbols and assignment of
  variables, as follows:\<close>

fun eval_term ("_\<lbrakk>(2_)\<rbrakk>_" [999,1,100]100) where
  "I\<lbrakk>Var x\<rbrakk>\<alpha> = \<alpha> x"
| "I\<lbrakk>Fun f ss\<rbrakk>\<alpha> = I f [I\<lbrakk>s\<rbrakk>\<alpha>. s \<leftarrow> ss]"

notation eval_term ("_\<lbrakk>(2_)\<rbrakk>" [999,1]100)
notation eval_term ("_\<lbrakk>(2_)\<rbrakk>_" [999,1,100]100)

lemma eval_same_vars:
  assumes "\<forall>x \<in> vars_term s. \<alpha> x = \<beta> x"
  shows "I\<lbrakk>s\<rbrakk>\<alpha> = I\<lbrakk>s\<rbrakk>\<beta>"
  by (insert assms, induct s, auto intro!:map_cong[OF refl] cong[of "I _"])

lemma eval_same_vars_cong:
  assumes ref: "s = t" and v: "\<And>x. x \<in> vars_term s \<Longrightarrow> \<alpha> x = \<beta> x"
  shows "I\<lbrakk>s\<rbrakk>\<alpha> = I\<lbrakk>t\<rbrakk>\<beta>"
  by (fold ref, rule eval_same_vars, auto dest:v)

lemma eval_with_fresh_var: "x \<notin> vars_term s \<Longrightarrow> I\<lbrakk>s\<rbrakk>\<alpha>(x:=a) = I\<lbrakk>s\<rbrakk>\<alpha>"
  by (auto intro: eval_same_vars)

lemma eval_map_term: "I\<lbrakk>map_term ff fv s\<rbrakk>\<alpha> = (I \<circ> ff)\<lbrakk>s\<rbrakk>(\<alpha> \<circ> fv)"
  by (induct s, auto intro: cong[of "I _"])


text \<open>A substitution is a mapping \<open>\<sigma>\<close> from variables to terms. We call a substitution that
  alters the type of variables a generalized substitution, since it does not have all properties
  that are expected of (standard) substitutions (e.g., there is no empty substitution).\<close>
type_synonym ('f, 'v, 'w) gsubst = "'v \<Rightarrow> ('f, 'w) term"
type_synonym ('f, 'v) subst  = "('f, 'v, 'v) gsubst"

abbreviation subst_apply_term :: "('f, 'v) term \<Rightarrow> ('f, 'v, 'w) gsubst \<Rightarrow> ('f, 'w) term"  (infixl "\<cdot>" 67)
  where "subst_apply_term \<equiv> eval_term Fun"

definition
  subst_compose :: "('f, 'u, 'v) gsubst \<Rightarrow> ('f, 'v, 'w) gsubst \<Rightarrow> ('f, 'u, 'w) gsubst"
  (infixl "\<circ>\<^sub>s" 75)
  where
    "\<sigma> \<circ>\<^sub>s \<tau> = (\<lambda>x. (\<sigma> x) \<cdot> \<tau>)"

lemma subst_subst_compose [simp]:
  "t \<cdot> (\<sigma> \<circ>\<^sub>s \<tau>) = t \<cdot> \<sigma> \<cdot> \<tau>"
  by (induct t) (simp_all add: subst_compose_def)

lemma subst_compose_assoc:
  "\<sigma> \<circ>\<^sub>s \<tau> \<circ>\<^sub>s \<mu> = \<sigma> \<circ>\<^sub>s (\<tau> \<circ>\<^sub>s \<mu>)"
proof (rule ext)
  fix x show "(\<sigma> \<circ>\<^sub>s \<tau> \<circ>\<^sub>s \<mu>) x = (\<sigma> \<circ>\<^sub>s (\<tau> \<circ>\<^sub>s \<mu>)) x"
  proof -
    have "(\<sigma> \<circ>\<^sub>s \<tau> \<circ>\<^sub>s \<mu>) x = \<sigma>(x) \<cdot> \<tau> \<cdot> \<mu>" by (simp add: subst_compose_def)
    also have "\<dots> = \<sigma>(x) \<cdot> (\<tau> \<circ>\<^sub>s \<mu>)" by simp
    finally show ?thesis by (simp add: subst_compose_def)
  qed
qed

lemma subst_apply_term_empty [simp]:
  "t \<cdot> Var = t"
proof (induct t)
  case (Fun f ts)
  from map_ext [rule_format, of ts _ id, OF Fun] show ?case by simp
qed simp

interpretation subst_monoid_mult: monoid_mult "Var" "(\<circ>\<^sub>s)"
  by (unfold_locales) (simp add: subst_compose_assoc, simp_all add: subst_compose_def)

lemma term_subst_eq:
  assumes "\<And>x. x \<in> vars_term t \<Longrightarrow> \<sigma> x = \<tau> x"
  shows "t \<cdot> \<sigma> = t \<cdot> \<tau>"
  using assms by (induct t) (auto)

lemma term_subst_eq_rev:
  "t \<cdot> \<sigma> = t \<cdot> \<tau> \<Longrightarrow> \<forall>x \<in> vars_term t. \<sigma> x = \<tau> x"
  by (induct t) simp_all

lemma term_subst_eq_conv:
  "t \<cdot> \<sigma> = t \<cdot> \<tau> \<longleftrightarrow> (\<forall>x \<in> vars_term t. \<sigma> x = \<tau> x)"
  by (auto intro!: term_subst_eq term_subst_eq_rev)

lemma subst_term_eqI:
  assumes "(\<And>t. t \<cdot> \<sigma> = t \<cdot> \<tau>)"
  shows "\<sigma> = \<tau>"
  using assms [of "Var x" for x] by (intro ext) simp

definition subst_domain :: "('f, 'v) subst \<Rightarrow> 'v set"
  where
    "subst_domain \<sigma> = {x. \<sigma> x \<noteq> Var x}"

fun subst_range :: "('f, 'v) subst \<Rightarrow> ('f, 'v) term set"
  where
    "subst_range \<sigma> = \<sigma> ` subst_domain \<sigma>"

lemma vars_term_ms_subst [simp]:
  "vars_term_ms (t \<cdot> \<sigma>) =
    (\<Sum>x\<in>#vars_term_ms t. vars_term_ms (\<sigma> x))" (is "_ = ?V t")
proof (induct t)
  case (Fun f ts)
  have IH: "map (\<lambda> t. vars_term_ms (t \<cdot> \<sigma>)) ts = map (\<lambda> t. ?V t) ts"
    by (rule map_cong[OF refl Fun])
  show ?case by (simp add: o_def IH, induct ts, auto)
qed simp

lemma vars_term_ms_subst_mono:
  assumes "vars_term_ms s \<subseteq># vars_term_ms t"
  shows "vars_term_ms (s \<cdot> \<sigma>) \<subseteq># vars_term_ms (t \<cdot> \<sigma>)"
proof -
  from assms[unfolded mset_subset_eq_exists_conv] obtain u where t: "vars_term_ms t = vars_term_ms s + u" by auto
  show ?thesis unfolding vars_term_ms_subst unfolding t by auto
qed


text \<open>The variables introduced by a substitution.\<close>
definition range_vars :: "('f, 'v) subst \<Rightarrow> 'v set"
where
  "range_vars \<sigma> = \<Union>(vars_term ` subst_range \<sigma>)"

lemma mem_range_varsI: \<^marker>\<open>contributor \<open>Martin Desharnais\<close>\<close>
  assumes "\<sigma> x = Var y" and "x \<noteq> y"
  shows "y \<in> range_vars \<sigma>"
  unfolding range_vars_def UN_iff
proof (rule bexI[of _ "Var y"])
  show "y \<in> vars_term (Var y)"
    by simp
next
  from assms show "Var y \<in> subst_range \<sigma>"
    by (simp_all add: subst_domain_def)
qed

lemma subst_domain_Var [simp]:
  "subst_domain Var = {}"
  by (simp add: subst_domain_def)

lemma subst_range_Var[simp]: \<^marker>\<open>contributor \<open>Martin Desharnais\<close>\<close>
  "subst_range Var = {}"
  by simp

lemma range_vars_Var[simp]: \<^marker>\<open>contributor \<open>Martin Desharnais\<close>\<close>
  "range_vars Var = {}"
  by (simp add: range_vars_def)

lemma subst_apply_term_ident: \<^marker>\<open>contributor \<open>Martin Desharnais\<close>\<close>
  "vars_term t \<inter> subst_domain \<sigma> = {} \<Longrightarrow> t \<cdot> \<sigma> = t"
proof (induction t)
  case (Var x)
  thus ?case
    by (simp add: subst_domain_def)
next
  case (Fun f ts)
  thus ?case
    by (auto intro: list.map_ident_strong)
qed

lemma vars_term_subst_apply_term: \<^marker>\<open>contributor \<open>Martin Desharnais\<close>\<close>
  "vars_term (t \<cdot> \<sigma>) = (\<Union>x \<in> vars_term t. vars_term (\<sigma> x))"
  by (induction t) (auto simp add: insert_Diff_if subst_domain_def)

corollary vars_term_subst_apply_term_subset: \<^marker>\<open>contributor \<open>Martin Desharnais\<close>\<close>
  "vars_term (t \<cdot> \<sigma>) \<subseteq> vars_term t - subst_domain \<sigma> \<union> range_vars \<sigma>"
  unfolding vars_term_subst_apply_term
proof (induction t)
  case (Var x)
  show ?case
    by (cases "\<sigma> x = Var x") (auto simp add: range_vars_def subst_domain_def)
next
  case (Fun f xs)
  thus ?case by auto
qed

definition is_renaming :: "('f, 'v) subst \<Rightarrow> bool"
  where
    "is_renaming \<sigma> \<longleftrightarrow> (\<forall>x. is_Var (\<sigma> x)) \<and> inj_on \<sigma> (subst_domain \<sigma>)"

lemma inv_renaming_sound: \<^marker>\<open>contributor \<open>Martin Desharnais\<close>\<close>
  assumes is_var_\<rho>: "\<forall>x. is_Var (\<rho> x)" and "inj \<rho>"
  shows "\<rho> \<circ>\<^sub>s (Var \<circ> (inv (the_Var \<circ> \<rho>))) = Var"
proof -
  define \<rho>' where "\<rho>' = the_Var \<circ> \<rho>"
  have \<rho>_def: "\<rho> = Var \<circ> \<rho>'"
    unfolding \<rho>'_def using is_var_\<rho> by auto

  from is_var_\<rho> \<open>inj \<rho>\<close> have "inj \<rho>'"
    unfolding inj_def \<rho>_def comp_def by fast
  hence "inv \<rho>' \<circ> \<rho>' = id"
    using inv_o_cancel[of \<rho>'] by simp
  hence "Var \<circ> (inv \<rho>' \<circ> \<rho>') = Var"
    by simp
  hence "\<forall>x. (Var \<circ> (inv \<rho>' \<circ> \<rho>')) x = Var x"
    by metis
  hence "\<forall>x. ((Var \<circ> \<rho>') \<circ>\<^sub>s (Var \<circ> (inv \<rho>'))) x = Var x"
    unfolding subst_compose_def by auto
  thus "\<rho> \<circ>\<^sub>s (Var \<circ> (inv \<rho>')) = Var"
    using \<rho>_def by auto
qed

lemma ex_inverse_of_renaming: \<^marker>\<open>contributor \<open>Martin Desharnais\<close>\<close>
  assumes "\<forall>x. is_Var (\<rho> x)" and "inj \<rho>"
  shows "\<exists>\<tau>. \<rho> \<circ>\<^sub>s \<tau> = Var"
  using inv_renaming_sound[OF assms] by blast

lemma vars_term_subst:
  "vars_term (t \<cdot> \<sigma>) = \<Union>(vars_term ` \<sigma> ` vars_term t)"
  by (induct t) simp_all

lemma range_varsE [elim]:
  assumes "x \<in> range_vars \<sigma>"
    and "\<And>t. x \<in> vars_term t \<Longrightarrow> t \<in> subst_range \<sigma> \<Longrightarrow> P"
  shows "P"
  using assms by (auto simp: range_vars_def)

lemma range_vars_subst_compose_subset:
  "range_vars (\<sigma> \<circ>\<^sub>s \<tau>) \<subseteq> (range_vars \<sigma> - subst_domain \<tau>) \<union> range_vars \<tau>" (is "?L \<subseteq> ?R")
proof
  fix x
  assume "x \<in> ?L"
  then obtain y where "y \<in> subst_domain (\<sigma> \<circ>\<^sub>s \<tau>)"
    and "x \<in> vars_term ((\<sigma> \<circ>\<^sub>s \<tau>) y)" by (auto simp: range_vars_def)
  then show "x \<in> ?R"
  proof (cases)
    assume "y \<in> subst_domain \<sigma>" and "x \<in> vars_term ((\<sigma> \<circ>\<^sub>s \<tau>) y)"
    moreover then obtain v where "v \<in> vars_term (\<sigma> y)"
      and "x \<in> vars_term (\<tau> v)" by (auto simp: subst_compose_def vars_term_subst)
    ultimately show ?thesis
      by (cases "v \<in> subst_domain \<tau>") (auto simp: range_vars_def subst_domain_def)
  qed (auto simp: range_vars_def subst_compose_def subst_domain_def)
qed

definition "subst x t = Var (x := t)"

lemma subst_simps [simp]:
  "subst x t x = t"
  "subst x (Var x) = Var"
  by (auto simp: subst_def)

lemma subst_subst_domain [simp]:
  "subst_domain (subst x t) = (if t = Var x then {} else {x})"
proof -
  { fix y
    have "y \<in> {y. subst x t y \<noteq> Var y} \<longleftrightarrow> y \<in> (if t = Var x then {} else {x})"
      by (cases "x = y", auto simp: subst_def) }
  then show ?thesis by (simp add: subst_domain_def)
qed

lemma subst_subst_range [simp]:
  "subst_range (subst x t) = (if t = Var x then {} else {t})"
  by (cases "t = Var x") (auto simp: subst_domain_def subst_def)

lemma subst_apply_left_idemp [simp]:
  assumes "\<sigma> x = t \<cdot> \<sigma>"
  shows "s \<cdot> subst x t \<cdot> \<sigma> = s \<cdot> \<sigma>"
  using assms by (induct s) (auto simp: subst_def)

lemma subst_compose_left_idemp [simp]:
  assumes "\<sigma> x = t \<cdot> \<sigma>"
  shows "subst x t \<circ>\<^sub>s \<sigma> = \<sigma>"
  by (rule subst_term_eqI) (simp add: assms)

lemma subst_ident [simp]:
  assumes "x \<notin> vars_term t"
  shows "t \<cdot> subst x u = t"
proof -
  have "t \<cdot> subst x u = t \<cdot> Var"
    by (rule term_subst_eq) (auto simp: assms subst_def)
  then show ?thesis by simp
qed

lemma subst_self_idemp [simp]:
  "x \<notin> vars_term t \<Longrightarrow> subst x t \<circ>\<^sub>s subst x t = subst x t"
  by (metis subst_simps(1) subst_compose_left_idemp subst_ident)

type_synonym ('f, 'v) terms = "('f, 'v) term set"

text \<open>Applying a substitution to every term of a given set.\<close>
abbreviation
  subst_apply_set :: "('f, 'v) terms \<Rightarrow> ('f, 'v, 'w) gsubst \<Rightarrow> ('f, 'w) terms" (infixl "\<cdot>\<^sub>s\<^sub>e\<^sub>t" 60)
  where
    "T \<cdot>\<^sub>s\<^sub>e\<^sub>t \<sigma> \<equiv> (\<lambda>t. t \<cdot> \<sigma>) ` T"

text \<open>Composition of substitutions\<close>
lemma subst_compose: "(\<sigma> \<circ>\<^sub>s \<tau>) x = \<sigma> x \<cdot> \<tau>" by (auto simp: subst_compose_def)

lemmas subst_subst = subst_subst_compose [symmetric]

lemma subst_apply_eq_Var:
  assumes "s \<cdot> \<sigma> = Var x"
  obtains y where "s = Var y" and "\<sigma> y = Var x"
  using assms by (induct s) auto

lemma subst_domain_subst_compose:
  "subst_domain (\<sigma> \<circ>\<^sub>s \<tau>) =
    (subst_domain \<sigma> - {x. \<exists>y. \<sigma> x = Var y \<and> \<tau> y = Var x}) \<union>
    (subst_domain \<tau> - subst_domain \<sigma>)"
  by (auto simp: subst_domain_def subst_compose_def elim: subst_apply_eq_Var)


text \<open>A substitution is idempotent iff the variables in its range are disjoint from its domain.
  (See also "Term Rewriting and All That" \<^cite>\<open>\<open>Lemma 4.5.7\<close> in "AllThat"\<close>.)\<close>
lemma subst_idemp_iff:
  "\<sigma> \<circ>\<^sub>s \<sigma> = \<sigma> \<longleftrightarrow> subst_domain \<sigma> \<inter> range_vars \<sigma> = {}"
proof
  assume "\<sigma> \<circ>\<^sub>s \<sigma> = \<sigma>"
  then have "\<And>x. \<sigma> x \<cdot> \<sigma> = \<sigma> x \<cdot> Var" by simp (metis subst_compose_def)
  then have *: "\<And>x. \<forall>y\<in>vars_term (\<sigma> x). \<sigma> y = Var y"
    unfolding term_subst_eq_conv by simp
  { fix x y
    assume "\<sigma> x \<noteq> Var x" and "x \<in> vars_term (\<sigma> y)"
    with * [of y] have False by simp }
  then show "subst_domain \<sigma> \<inter> range_vars \<sigma> = {}"
    by (auto simp: subst_domain_def range_vars_def)
next
  assume "subst_domain \<sigma> \<inter> range_vars \<sigma> = {}"
  then have *: "\<And>x y. \<sigma> x = Var x \<or> \<sigma> y = Var y \<or> x \<notin> vars_term (\<sigma> y)"
    by (auto simp: subst_domain_def range_vars_def)
  have "\<And>x. \<forall>y\<in>vars_term (\<sigma> x). \<sigma> y = Var y"
  proof
    fix x y
    assume "y \<in> vars_term (\<sigma> x)"
    with * [of y x] show "\<sigma> y = Var y" by auto
  qed
  then show "\<sigma> \<circ>\<^sub>s \<sigma> = \<sigma>"
    by (simp add: subst_compose_def term_subst_eq_conv [symmetric])
qed

lemma subst_compose_apply_eq_apply_lhs: \<^marker>\<open>contributor \<open>Martin Desharnais\<close>\<close>
  assumes
    "range_vars \<sigma> \<inter> subst_domain \<delta> = {}"
    "x \<notin> subst_domain \<delta>"
  shows "(\<sigma> \<circ>\<^sub>s \<delta>) x = \<sigma> x"
proof (cases "\<sigma> x")
  case (Var y)
  show ?thesis
  proof (cases "x = y")
    case True
    with Var have \<open>\<sigma> x = Var x\<close>
      by simp
    moreover from \<open>x \<notin> subst_domain \<delta>\<close> have "\<delta> x = Var x"
      by (simp add: disjoint_iff subst_domain_def)
    ultimately show ?thesis
      by (simp add: subst_compose_def)
  next
    case False
    have "y \<in> range_vars \<sigma>"
      unfolding range_vars_def UN_iff
    proof (rule bexI)
      show "y \<in> vars_term (Var y)"
        by simp
    next
      from Var False show "Var y \<in> subst_range \<sigma>"
        by (simp_all add: subst_domain_def)
    qed
    hence "y \<notin> subst_domain \<delta>"
      using \<open>range_vars \<sigma> \<inter> subst_domain \<delta> = {}\<close>
      by (simp add: disjoint_iff)
    with Var show ?thesis
      unfolding subst_compose_def
      by (simp add: subst_domain_def)
  qed
next
  case (Fun f ys)
  hence "Fun f ys \<in> subst_range \<sigma> \<or> (\<forall>y\<in>set ys. y \<in> subst_range \<sigma>)"
    using subst_domain_def by fastforce
  hence "\<forall>x \<in> vars_term (Fun f ys). x \<in> range_vars \<sigma>"
    by (metis UN_I range_vars_def term.distinct(1) term.sel(4) term.set_cases(2))
  hence "Fun f ys \<cdot> \<delta> = Fun f ys \<cdot> Var"
    unfolding term_subst_eq_conv
    using \<open>range_vars \<sigma> \<inter> subst_domain \<delta> = {}\<close>
    by (simp add: disjoint_iff subst_domain_def)
  from this[unfolded subst_apply_term_empty] Fun show ?thesis
    by (simp add: subst_compose_def)
qed

lemma subst_apply_term_subst_apply_term_eq_subst_apply_term_lhs: \<^marker>\<open>contributor \<open>Martin Desharnais\<close>\<close>
  assumes "range_vars \<sigma> \<inter> subst_domain \<delta> = {}" and "vars_term t \<inter> subst_domain \<delta> = {}"
  shows "t \<cdot> \<sigma> \<cdot> \<delta> = t \<cdot> \<sigma>"
proof -
  from assms have "\<And>x. x \<in> vars_term t \<Longrightarrow> (\<sigma> \<circ>\<^sub>s \<delta>) x = \<sigma> x"
    using subst_compose_apply_eq_apply_lhs by fastforce
  hence "t \<cdot> \<sigma> \<circ>\<^sub>s \<delta> = t \<cdot> \<sigma>"
    using term_subst_eq_conv by metis
  thus ?thesis
    by simp
qed

fun num_funs :: "('f, 'v) term \<Rightarrow> nat"
  where
    "num_funs (Var x) = 0" |
    "num_funs (Fun f ts) = Suc (sum_list (map num_funs ts))"

lemma num_funs_0:
  assumes "num_funs t = 0"
  obtains x where "t = Var x"
  using assms by (induct t) auto

lemma num_funs_subst:
  "num_funs (t \<cdot> \<sigma>) \<ge> num_funs t"
  by (induct t) (simp_all, metis comp_apply sum_list_mono)

lemma sum_list_map_num_funs_subst:
  assumes "sum_list (map (num_funs \<circ> (\<lambda>t. t \<cdot> \<sigma>)) ts) = sum_list (map num_funs ts)"
  shows "\<forall>i < length ts. num_funs (ts ! i \<cdot> \<sigma>) = num_funs (ts ! i)"
  using assms
proof (induct ts)
  case (Cons t ts)
  then have "num_funs (t \<cdot> \<sigma>) + sum_list (map (num_funs \<circ> (\<lambda>t. t \<cdot> \<sigma>)) ts)
    = num_funs t + sum_list (map num_funs ts)" by (simp add: o_def)
  moreover have "num_funs (t \<cdot> \<sigma>) \<ge> num_funs t" by (metis num_funs_subst)
  moreover have "sum_list (map (num_funs \<circ> (\<lambda>t. t \<cdot> \<sigma>)) ts) \<ge> sum_list (map num_funs ts)"
    using num_funs_subst [of _ \<sigma>] by (induct ts) (auto intro: add_mono)
  ultimately show ?case using Cons by (auto) (case_tac i, auto)
qed simp

lemma is_Fun_num_funs_less:
  assumes "x \<in> vars_term t" and "is_Fun t"
  shows "num_funs (\<sigma> x) < num_funs (t \<cdot> \<sigma>)"
  using assms
proof (induct t)
  case (Fun f ts)
  then obtain u where u: "u \<in> set ts" "x \<in> vars_term u" by auto
  then have "num_funs (u \<cdot> \<sigma>) \<le> sum_list (map (num_funs \<circ> (\<lambda>t. t \<cdot> \<sigma>)) ts)"
    by (intro member_le_sum_list) simp
  moreover have "num_funs (\<sigma> x) \<le> num_funs (u \<cdot> \<sigma>)"
    using Fun.hyps [OF u] and u  by (cases u; simp)
  ultimately show ?case by simp
qed simp

lemma finite_subst_domain_subst:
  "finite (subst_domain (subst x y))"
  by simp

lemma subst_domain_compose:
  "subst_domain (\<sigma> \<circ>\<^sub>s \<tau>) \<subseteq> subst_domain \<sigma> \<union> subst_domain \<tau>"
  by (auto simp: subst_domain_def subst_compose_def)

lemma vars_term_disjoint_imp_unifier:
  fixes \<sigma> :: "('f, 'v, 'w) gsubst"
  assumes "vars_term s \<inter> vars_term t = {}"
    and "s \<cdot> \<sigma> = t \<cdot> \<tau>"
  shows "\<exists>\<mu> :: ('f, 'v, 'w) gsubst. s \<cdot> \<mu> = t \<cdot> \<mu>"
proof -
  let ?\<mu> = "\<lambda>x. if x \<in> vars_term s then \<sigma> x else \<tau> x"
  have "s \<cdot> \<sigma> = s \<cdot> ?\<mu>"
    unfolding term_subst_eq_conv
    by (induct s) (simp_all)
  moreover have "t \<cdot> \<tau> = t \<cdot> ?\<mu>"
    using assms(1)
    unfolding term_subst_eq_conv
    by (induct s arbitrary: t) (auto)
  ultimately have "s \<cdot> ?\<mu> = t \<cdot> ?\<mu>" using assms(2) by simp
  then show ?thesis by blast
qed

lemma vars_term_subset_subst_eq:
  assumes "vars_term t \<subseteq> vars_term s"
    and "s \<cdot> \<sigma> = s \<cdot> \<tau>"
  shows "t \<cdot> \<sigma> = t \<cdot> \<tau>"
  using assms by (induct t) (induct s, auto)


subsection \<open>Restrict the Domain of a Substitution\<close>

definition restrict_subst_domain where \<^marker>\<open>contributor \<open>Martin Desharnais\<close>\<close>
  "restrict_subst_domain V \<sigma> x \<equiv> (if x \<in> V then \<sigma> x else Var x)"

lemma restrict_subst_domain_empty[simp]: \<^marker>\<open>contributor \<open>Martin Desharnais\<close>\<close>
  "restrict_subst_domain {} \<sigma> = Var"
  unfolding restrict_subst_domain_def by auto

lemma restrict_subst_domain_Var[simp]: \<^marker>\<open>contributor \<open>Martin Desharnais\<close>\<close>
  "restrict_subst_domain V Var = Var"
  unfolding restrict_subst_domain_def by auto

lemma subst_domain_restrict_subst_domain[simp]: \<^marker>\<open>contributor \<open>Martin Desharnais\<close>\<close>
  "subst_domain (restrict_subst_domain V \<sigma>) = V \<inter> subst_domain \<sigma>"
  unfolding restrict_subst_domain_def subst_domain_def by auto

lemma subst_apply_term_restrict_subst_domain: \<^marker>\<open>contributor \<open>Martin Desharnais\<close>\<close>
  "vars_term t \<subseteq> V \<Longrightarrow> t \<cdot> restrict_subst_domain V \<sigma> = t \<cdot> \<sigma>"
  by (rule term_subst_eq) (simp add: restrict_subst_domain_def subsetD)


subsection \<open>Rename the Domain of a Substitution\<close>

definition rename_subst_domain where \<^marker>\<open>contributor \<open>Martin Desharnais\<close>\<close>
  "rename_subst_domain \<rho> \<sigma> x =
    (if Var x \<in> \<rho> ` subst_domain \<sigma> then
      \<sigma> (the_inv \<rho> (Var x))
    else
      Var x)"

lemma rename_subst_domain_Var_lhs[simp]: \<^marker>\<open>contributor \<open>Martin Desharnais\<close>\<close>
  "rename_subst_domain Var \<sigma> = \<sigma>"
  by (rule ext) (simp add: rename_subst_domain_def inj_image_mem_iff the_inv_f_f subst_domain_def)

lemma rename_subst_domain_Var_rhs[simp]: \<^marker>\<open>contributor \<open>Martin Desharnais\<close>\<close>
  "rename_subst_domain \<rho> Var = Var"
  by (rule ext) (simp add: rename_subst_domain_def)

lemma subst_domain_rename_subst_domain_subset: \<^marker>\<open>contributor \<open>Martin Desharnais\<close>\<close>
  assumes is_var_\<rho>: "\<forall>x. is_Var (\<rho> x)"
  shows "subst_domain (rename_subst_domain \<rho> \<sigma>) \<subseteq> the_Var ` \<rho> ` subst_domain \<sigma>"
  by (auto simp add: subst_domain_def rename_subst_domain_def
      member_image_the_Var_image_subst[OF is_var_\<rho>])

lemma subst_range_rename_subst_domain_subset: \<^marker>\<open>contributor \<open>Martin Desharnais\<close>\<close>
  assumes "inj \<rho>"
  shows "subst_range (rename_subst_domain \<rho> \<sigma>) \<subseteq> subst_range \<sigma>"
proof (intro Set.equalityI Set.subsetI)
  fix t assume "t \<in> subst_range (rename_subst_domain \<rho> \<sigma>)"
  then obtain x where
    t_def: "t = rename_subst_domain \<rho> \<sigma> x" and
    "rename_subst_domain \<rho> \<sigma> x \<noteq> Var x"
    by (auto simp: image_iff subst_domain_def)

  show "t \<in> subst_range \<sigma>"
  proof (cases \<open>Var x \<in> \<rho> ` subst_domain \<sigma>\<close>)
    case True
    then obtain x' where "\<rho> x' = Var x" and "x' \<in> subst_domain \<sigma>"
      by auto
    then show ?thesis
      using the_inv_f_f[OF \<open>inj \<rho>\<close>, of x']
      by (simp add: t_def rename_subst_domain_def)
  next
    case False
    hence False
      using \<open>rename_subst_domain \<rho> \<sigma> x \<noteq> Var x\<close>
      by (simp add: t_def rename_subst_domain_def)
    thus ?thesis ..
  qed
qed

lemma range_vars_rename_subst_domain_subset: \<^marker>\<open>contributor \<open>Martin Desharnais\<close>\<close>
  assumes "inj \<rho>"
  shows "range_vars (rename_subst_domain \<rho> \<sigma>) \<subseteq> range_vars \<sigma>"
  unfolding range_vars_def
  using subst_range_rename_subst_domain_subset[OF \<open>inj \<rho>\<close>]
  by (metis Union_mono image_mono)

lemma renaming_cancels_rename_subst_domain: \<^marker>\<open>contributor \<open>Martin Desharnais\<close>\<close>
  assumes is_var_\<rho>: "\<forall>x. is_Var (\<rho> x)" and "inj \<rho>" and vars_t: "vars_term t \<subseteq> subst_domain \<sigma>"
  shows "t \<cdot> \<rho> \<cdot> rename_subst_domain \<rho> \<sigma> = t \<cdot> \<sigma>"
  unfolding subst_subst
proof (intro term_subst_eq ballI)
  fix x assume "x \<in> vars_term t"
  with vars_t have x_in: "x \<in> subst_domain \<sigma>"
    by blast

  obtain x' where \<rho>_x: "\<rho> x = Var x'"
    using is_var_\<rho> by (meson is_Var_def)
  with x_in have x'_in: "Var x' \<in> \<rho> ` subst_domain \<sigma>"
    by (metis image_eqI)

  have "(\<rho> \<circ>\<^sub>s rename_subst_domain \<rho> \<sigma>) x = \<rho> x \<cdot> rename_subst_domain \<rho> \<sigma>"
    by (simp add: subst_compose_def)
  also have "\<dots> = rename_subst_domain \<rho> \<sigma> x'"
    using \<rho>_x by simp
  also have "\<dots> = \<sigma> (the_inv \<rho> (Var x'))"
    by (simp add: rename_subst_domain_def if_P[OF x'_in])
  also have "\<dots> = \<sigma> (the_inv \<rho> (\<rho> x))"
    by (simp add: \<rho>_x)
  also have "\<dots> = \<sigma> x"
    using \<open>inj \<rho>\<close> by (simp add: the_inv_f_f)
  finally show "(\<rho> \<circ>\<^sub>s rename_subst_domain \<rho> \<sigma>) x = \<sigma> x"
    by simp
qed


subsection \<open>Rename the Domain and Range of a Substitution\<close>

definition rename_subst_domain_range where \<^marker>\<open>contributor \<open>Martin Desharnais\<close>\<close>
  "rename_subst_domain_range \<rho> \<sigma> x =
    (if Var x \<in> \<rho> ` subst_domain \<sigma> then
      ((Var o the_inv \<rho>) \<circ>\<^sub>s \<sigma> \<circ>\<^sub>s \<rho>) (Var x)
    else
      Var x)"

lemma rename_subst_domain_range_Var_lhs[simp]: \<^marker>\<open>contributor \<open>Martin Desharnais\<close>\<close>
  "rename_subst_domain_range Var \<sigma> = \<sigma>"
  by (rule ext) (simp add: rename_subst_domain_range_def inj_image_mem_iff the_inv_f_f
      subst_domain_def subst_compose_def)

lemma rename_subst_domain_range_Var_rhs[simp]: \<^marker>\<open>contributor \<open>Martin Desharnais\<close>\<close>
  "rename_subst_domain_range \<rho> Var = Var"
  by (rule ext) (simp add: rename_subst_domain_range_def)

lemma subst_compose_renaming_rename_subst_domain_range: \<^marker>\<open>contributor \<open>Martin Desharnais\<close>\<close>
  fixes \<sigma> \<rho> :: "('f, 'v) subst"
  assumes is_var_\<rho>: "\<forall>x. is_Var (\<rho> x)" and "inj \<rho>"
  shows "\<rho> \<circ>\<^sub>s rename_subst_domain_range \<rho> \<sigma> = \<sigma> \<circ>\<^sub>s \<rho>"
proof (rule ext)
  fix x
  from is_var_\<rho> obtain x' where "\<rho> x = Var x'"
    by (meson is_Var_def is_renaming_def)
  with \<open>inj \<rho>\<close> have inv_\<rho>_x': "the_inv \<rho> (Var x') = x"
    by (metis the_inv_f_f)

  show "(\<rho> \<circ>\<^sub>s rename_subst_domain_range \<rho> \<sigma>) x = (\<sigma> \<circ>\<^sub>s \<rho>) x"
  proof (cases "x \<in> subst_domain \<sigma>")
    case True
    hence "Var x' \<in> \<rho> ` subst_domain \<sigma>"
      using \<open>\<rho> x = Var x'\<close> by (metis imageI)
    thus ?thesis
      by (simp add: \<open>\<rho> x = Var x'\<close> rename_subst_domain_range_def subst_compose_def inv_\<rho>_x')
  next
    case False
    hence "Var x' \<notin> \<rho> ` subst_domain \<sigma>"
    proof (rule contrapos_nn)
      assume "Var x' \<in> \<rho> ` subst_domain \<sigma>"
      hence "\<rho> x \<in> \<rho> ` subst_domain \<sigma>"
        unfolding \<open>\<rho> x = Var x'\<close> .
      thus "x \<in> subst_domain \<sigma>"
        unfolding inj_image_mem_iff[OF \<open>inj \<rho>\<close>] .
    qed
    with False \<open>\<rho> x = Var x'\<close> show ?thesis
      by (simp add: subst_compose_def subst_domain_def rename_subst_domain_range_def)
  qed
qed

corollary subst_apply_term_renaming_rename_subst_domain_range: \<^marker>\<open>contributor \<open>Martin Desharnais\<close>\<close>
  \<comment> \<open>This might be easier to find with @{command find_theorems}.\<close>
  fixes t :: "('f, 'v) term" and \<sigma> \<rho> :: "('f, 'v) subst"
  assumes is_var_\<rho>: "\<forall>x. is_Var (\<rho> x)" and "inj \<rho>"
  shows "t \<cdot> \<rho> \<cdot> rename_subst_domain_range \<rho> \<sigma> = t \<cdot> \<sigma> \<cdot> \<rho>"
  unfolding subst_subst
  unfolding subst_compose_renaming_rename_subst_domain_range[OF assms]
  by (rule refl)


text \<open>A term is called \<^emph>\<open>ground\<close> if it does not contain any variables.\<close>
fun ground :: "('f, 'v) term \<Rightarrow> bool"
  where
    "ground (Var x) \<longleftrightarrow> False" |
    "ground (Fun f ts) \<longleftrightarrow> (\<forall>t \<in> set ts. ground t)"

lemma ground_vars_term_empty:
  "ground t \<longleftrightarrow> vars_term t = {}"
  by (induct t) simp_all

lemma ground_subst [simp]:
  "ground (t \<cdot> \<sigma>) \<longleftrightarrow> (\<forall>x \<in> vars_term t. ground (\<sigma> x))"
  by (induct t) simp_all

lemma ground_subst_apply:
  assumes "ground t"
  shows "t \<cdot> \<sigma> = t"
proof -
  have "t = t \<cdot> Var" by simp
  also have "\<dots> = t \<cdot> \<sigma>"
    by (rule term_subst_eq, insert assms[unfolded ground_vars_term_empty], auto)
  finally show ?thesis by simp
qed

text \<open>Just changing the variables in a term\<close>

abbreviation "map_vars_term f \<equiv> term.map_term (\<lambda>x. x) f"

lemma map_vars_term_as_subst:
  "map_vars_term f t = t \<cdot> (\<lambda> x. Var (f x))"
  by (induct t) simp_all

lemma map_vars_term_eq:
  "map_vars_term f s = s \<cdot> (Var \<circ> f)"
by (induct s) auto

lemma ground_map_vars_term [simp]:
  "ground (map_vars_term f t) = ground t"
  by (induct t) simp_all

lemma map_vars_term_subst [simp]:
  "map_vars_term f (t \<cdot> \<sigma>) = t \<cdot> (\<lambda> x. map_vars_term f (\<sigma> x))"
  by (induct t) simp_all

lemma map_vars_term_compose:
  "map_vars_term m1 (map_vars_term m2 t) = map_vars_term (m1 o m2) t"
  by (induct t) simp_all

lemma map_vars_term_id [simp]:
  "map_vars_term id t = t"
  by (induct t) (auto intro: map_idI)

lemma apply_subst_map_vars_term:
  "map_vars_term m t \<cdot> \<sigma> = t \<cdot> (\<sigma> \<circ> m)"
  by (induct t) (auto)


end
