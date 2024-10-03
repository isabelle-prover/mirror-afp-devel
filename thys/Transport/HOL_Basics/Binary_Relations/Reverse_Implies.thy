\<^marker>\<open>creator "Kevin Kappelmann"\<close>
theory Reverse_Implies
  imports Binary_Relation_Functions
begin

definition "rev_implies \<equiv> (\<longrightarrow>)\<inverse>"

open_bundle rev_implies_syntax
begin
notation rev_implies (infixr \<open>\<longleftarrow>\<close> 25)
end

bundle no_rev_implies_syntax
begin
no_notation rev_implies (infixr \<open>\<longleftarrow>\<close> 25)
end

lemma rev_imp_eq_imp_inv [simp]: "(\<longleftarrow>) = (\<longrightarrow>)\<inverse>"
  unfolding rev_implies_def by simp

lemma rev_impI [intro!]:
  assumes "Q \<Longrightarrow> P"
  shows "P \<longleftarrow> Q"
  using assms by auto

lemma rev_impD [dest!]:
  assumes "P \<longleftarrow> Q"
  shows "Q \<Longrightarrow> P"
  using assms by auto

lemma rev_imp_iff_imp: "(P \<longleftarrow> Q) \<longleftrightarrow> (Q \<longrightarrow> P)" by auto

end