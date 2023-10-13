\<^marker>\<open>creator "Kevin Kappelmann"\<close>
subsection \<open>Lattice\<close>
theory Predicates_Lattice
  imports
    HOL_Syntax_Bundles_Lattices
    HOL.Boolean_Algebras
begin

lemma inf_predI [intro]:
  assumes "P x"
  and "Q x"
  shows "(P \<sqinter> Q) x"
  using assms by (intro inf1I)

lemma inf_predE [elim]:
  assumes "(P \<sqinter> Q) x"
  obtains "P x" "Q x"
  using assms by (rule inf1E)

lemma inf_predD:
  assumes "(P \<sqinter> Q) x"
  shows "P x" and "Q x"
  using assms by auto


end