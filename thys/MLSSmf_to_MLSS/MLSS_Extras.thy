theory MLSS_Extras
  imports MLSS_Decision_Proc.MLSS_Semantics
begin

inductive normalized_MLSS_literal :: "'a pset_fm \<Rightarrow> bool" where
  eq_empty:
  "normalized_MLSS_literal (AT (Var x =\<^sub>s \<emptyset> n))"
| eq:
  "normalized_MLSS_literal (AT (Var x =\<^sub>s Var y))"
| neq:
  "normalized_MLSS_literal (AF (Var x =\<^sub>s Var y))"
| union: 
  "normalized_MLSS_literal (AT (Var x =\<^sub>s Var y \<squnion>\<^sub>s Var z))"
| diff:
  "normalized_MLSS_literal (AT (Var x =\<^sub>s Var y -\<^sub>s Var z))"
| singleton: 
  "normalized_MLSS_literal (AT (Var x =\<^sub>s Single (Var y)))"

locale normalized_MLSS_clause =
    fixes \<C> :: "'a pset_fm set"
  assumes norm_\<C>: "\<forall>lt \<in> \<C>. normalized_MLSS_literal lt"
      and finite_\<C>: "finite \<C>"
begin

\<comment>\<open>only valid for normalized literals\<close>
fun singleton_vars :: "'a pset_fm \<Rightarrow> 'a set" where
  "singleton_vars (AT (Var x =\<^sub>s Single (Var y))) = {y}"
| "singleton_vars _ = {}"

lemma singleton_vars_subset_vars: "singleton_vars \<phi> \<subseteq> vars \<phi>"
  apply (cases \<phi>)
     apply simp_all
  by (smt (z3) Un_iff subset_iff empty_iff
      fm.inject(1) pset_atom.simps(16) pset_term.simps(92) pset_term.simps(96) singleton_vars.elims)

abbreviation "V \<equiv> \<Union> (vars ` \<C>)"
abbreviation "W \<equiv> \<Union> (singleton_vars ` \<C>)"

lemma W_subset_V: "W \<subseteq> V"
  using singleton_vars_subset_vars by fast

lemma memW_E[elim]:
  assumes "w \<in> W"
    shows "\<exists>x. AT (Var x =\<^sub>s Single (Var w)) \<in> \<C>"
proof -
  from \<open>w \<in> W\<close> obtain lt where lt: "lt \<in> \<C>" "w \<in> singleton_vars lt" by blast
  then obtain x where "lt = AT (Var x =\<^sub>s Single (Var w))"
    by (cases lt rule: singleton_vars.cases) auto
  with lt show ?thesis by blast
qed

end

lemma AT_inj: "inj AT"
  by (standard; rule ccontr) auto

end