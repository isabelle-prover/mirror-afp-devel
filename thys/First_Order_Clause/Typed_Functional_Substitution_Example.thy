theory Typed_Functional_Substitution_Example
  imports
    Typed_Functional_Substitution
    Abstract_Substitution.Functional_Substitution_Example
begin

type_synonym ('f, 'ty) fun_types = "'f \<Rightarrow> 'ty list \<times> 'ty"

text \<open>Inductive predicate defining well-typed terms.\<close>

inductive welltyped :: "('f, 'ty) fun_types \<Rightarrow> ('v, 'ty) var_types \<Rightarrow> ('f,'v) term \<Rightarrow> 'ty \<Rightarrow> bool"
  for \<F> \<V> where
    Var: "\<V> x = \<tau> \<Longrightarrow> welltyped \<F> \<V> (Var x) \<tau>"
  | Fun: "\<F> f = (\<tau>s, \<tau>) \<Longrightarrow> list_all2 (welltyped \<F> \<V>) ts \<tau>s \<Longrightarrow> welltyped \<F> \<V> (Fun f ts) \<tau>"

global_interpretation "term": base_typing "welltyped \<F> \<V>"
proof unfold_locales
  show "right_unique (welltyped \<F> \<V>)"
  proof (rule right_uniqueI)
    fix t \<tau>\<^sub>1 \<tau>\<^sub>2
    assume "welltyped \<F> \<V> t \<tau>\<^sub>1" and "welltyped \<F> \<V> t \<tau>\<^sub>2"
    thus "\<tau>\<^sub>1 = \<tau>\<^sub>2"
      by (auto elim!: welltyped.cases)
  qed
qed

global_interpretation base_typed_functional_substitution where
  welltyped = "welltyped \<F>" and
  subst = subst_apply_term and id_subst = Var and comp_subst = subst_compose and
  vars = "vars_term :: ('f, 'v) term \<Rightarrow> 'v set"
  for \<F> :: "('f, 'ty) fun_types"
  by unfold_locales (simp_all add: welltyped.Var)

text \<open>A selection of substitution properties for typed terms.\<close>
locale typed_term_subst_properties =
  base_typed_subst_stability where welltyped = "welltyped \<F>"
  for \<F> :: "('f, 'ty) fun_types"

global_interpretation "term": typed_term_subst_properties where
  subst = subst_apply_term and id_subst = Var and comp_subst = subst_compose and
  vars = "vars_term :: ('f, 'v) term \<Rightarrow> 'v set" and \<F> = \<F>
  for \<F> :: "'f \<Rightarrow> 'ty list \<times> 'ty"
proof (unfold_locales)
  fix \<V> :: "('v, 'ty) var_types" and t :: "('f, 'v) term" and \<sigma> \<tau>
  assume is_welltyped_on: 
    "\<forall>x \<in> vars_term t. welltyped \<F> \<V> (Var x) (\<V> x) \<longrightarrow> welltyped \<F> \<V> (\<sigma> x) (\<V> x)"

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
  term.right_unique
  term.welltyped_subst_stability

  type_preserving_on_subst_update
  type_preserving_on_subset
  type_preserving_on_id_subst

term term.is_welltyped
term type_preserving_on
term type_preserving

end
