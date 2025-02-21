theory Typed_Functional_Substitution_Example
  imports
    Functional_Substitution_Typing
    Typed_Functional_Substitution
    Abstract_Substitution.Functional_Substitution_Example
begin

type_synonym ('f, 'ty) fun_types = "'f \<Rightarrow> 'ty list \<times> 'ty"

text \<open>Inductive predicates defining well-typed terms.\<close>
inductive typed :: "('f, 'ty) fun_types \<Rightarrow> ('v, 'ty) var_types \<Rightarrow> ('f,'v) term \<Rightarrow> 'ty \<Rightarrow> bool"
  for \<F> \<V> where
    Var: "\<V> x = \<tau> \<Longrightarrow> typed \<F> \<V> (Var x) \<tau>"
  | Fun: "\<F> f = (\<tau>s, \<tau>) \<Longrightarrow> typed \<F> \<V> (Fun f ts) \<tau>"

inductive welltyped :: "('f, 'ty) fun_types \<Rightarrow> ('v, 'ty) var_types \<Rightarrow> ('f,'v) term \<Rightarrow> 'ty \<Rightarrow> bool"
  for \<F> \<V> where
    Var: "\<V> x = \<tau> \<Longrightarrow> welltyped \<F> \<V> (Var x) \<tau>"
  | Fun: "\<F> f = (\<tau>s, \<tau>) \<Longrightarrow> list_all2 (welltyped \<F> \<V>) ts \<tau>s \<Longrightarrow> welltyped \<F> \<V> (Fun f ts) \<tau>"

global_interpretation "term": explicit_typing "typed \<F> \<V>" "welltyped \<F> \<V>"
proof unfold_locales
  show "right_unique (typed \<F> \<V>)"
  proof (rule right_uniqueI)
    fix t \<tau>\<^sub>1 \<tau>\<^sub>2
    assume "typed \<F> \<V> t \<tau>\<^sub>1" and "typed \<F> \<V> t \<tau>\<^sub>2"
    thus "\<tau>\<^sub>1 = \<tau>\<^sub>2"
      by (auto elim!: typed.cases)
  qed
next
  show "right_unique (welltyped \<F> \<V>)"
  proof (rule right_uniqueI)
    fix t \<tau>\<^sub>1 \<tau>\<^sub>2
    assume "welltyped \<F> \<V> t \<tau>\<^sub>1" and "welltyped \<F> \<V> t \<tau>\<^sub>2"
    thus "\<tau>\<^sub>1 = \<tau>\<^sub>2"
      by (auto elim!: welltyped.cases)
  qed
next
  fix t \<tau>
  assume "welltyped \<F> \<V> t \<tau>"
  then show "typed \<F> \<V> t \<tau>"
    by (metis (full_types) typed.simps welltyped.cases)
qed

global_interpretation "term": base_functional_substitution_typing where
  typed = "typed (\<F> :: ('f, 'ty) fun_types)" and welltyped = "welltyped \<F>" and
  subst = subst_apply_term and id_subst = Var and comp_subst = subst_compose and
  vars = "vars_term :: ('f, 'v) term \<Rightarrow> 'v set"
  by (unfold_locales; intro typed.Var welltyped.Var refl)

text \<open>A selection of substitution properties for typed terms.\<close>
locale typed_term_subst_properties =
  typed: explicitly_typed_subst_stability where typed = "typed \<F>" +
  welltyped: explicitly_typed_subst_stability where typed = "welltyped \<F>"
for \<F> :: "('f, 'ty) fun_types"

global_interpretation "term": typed_term_subst_properties where
  subst = subst_apply_term and id_subst = Var and comp_subst = subst_compose and
  vars = "vars_term :: ('f, 'v) term \<Rightarrow> 'v set" and \<F> = \<F>
for \<F> :: "'f \<Rightarrow> 'ty list \<times> 'ty"
proof (unfold_locales)
  fix \<tau> and \<V> and t :: "('f, 'v) term" and \<sigma>
  assume is_typed_on: "\<forall>x \<in> vars_term t. typed \<F> \<V> (\<sigma> x) (\<V> x)"

  show "typed \<F> \<V> (t \<cdot> \<sigma>) \<tau> \<longleftrightarrow> typed \<F> \<V> t \<tau>"
  proof(rule iffI)
    assume "typed \<F> \<V> t \<tau>"
    then show "typed \<F> \<V> (t \<cdot> \<sigma>) \<tau>"
      using is_typed_on
      by(induction rule: typed.induct)(auto simp: typed.Fun)
  next
    assume "typed \<F> \<V> (t \<cdot> \<sigma>) \<tau>"
    then show "typed \<F> \<V> t \<tau>"
      using is_typed_on
      by(induction t)(auto simp: typed.simps)
  qed
next
  fix \<V> :: "('v, 'ty) var_types" and t :: "('f, 'v) term" and \<sigma> \<tau>
  assume is_welltyped_on: "\<forall>x \<in> vars_term t. welltyped \<F> \<V> (\<sigma> x) (\<V> x)"

  show "welltyped \<F> \<V> (t \<cdot> \<sigma>) \<tau> \<longleftrightarrow> welltyped \<F> \<V> t \<tau>"
  proof(rule iffI)
    assume "welltyped \<F> \<V> t \<tau>"
    then show "welltyped \<F> \<V> (t \<cdot> \<sigma>) \<tau>"
      using is_welltyped_on
      by(induction rule: welltyped.induct)
        (auto simp: list.rel_mono_strong list_all2_map1 welltyped.simps)
  next
    assume "welltyped \<F> \<V> (t \<cdot> \<sigma>) \<tau>"
    then show "welltyped \<F> \<V> t \<tau>"
      using is_welltyped_on
    proof(induction "t \<cdot> \<sigma>" \<tau> arbitrary: t rule: welltyped.induct)
      case (Var x \<tau>)

      then obtain x' where t: "t = Var x'"
        by (metis subst_apply_eq_Var)

      have "welltyped \<F> \<V> t (\<V> x')"
        unfolding t
        by (simp add: welltyped.Var)

      moreover have "welltyped \<F> \<V> t (\<V> x)"
        using Var
        unfolding t
        by (simp add: welltyped.simps)

      ultimately have \<V>_x': "\<tau> = \<V> x'"
        using Var.hyps
        by (simp add: t welltyped.simps)

      show ?case
        unfolding t \<V>_x'
        by (simp add: welltyped.Var)
    next
      case (Fun f \<tau>s \<tau> ts)

      then show ?case
        by (cases t) (simp_all add: list.rel_mono_strong list_all2_map1 welltyped.simps)
    qed
  qed
qed

text \<open>Examples of generated lemmas and definitions\<close>
thm
  term.welltyped.right_unique
  term.welltyped.explicit_subst_stability
  term.welltyped.subst_stability
  term.welltyped.subst_update

  term.typed.right_unique
  term.typed.explicit_subst_stability
  term.typed.subst_stability
  term.typed.subst_update

  term.is_welltyped_on_subset
  term.is_typed_on_subset
  term.is_welltyped_id_subst
  term.is_typed_id_subst

term term.is_welltyped
term term.subst.is_welltyped_on
term term.subst.is_welltyped
term term.is_typed
term term.subst.is_typed_on
term term.subst.is_typed

end
