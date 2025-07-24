\<^marker>\<open>creator "Kevin Kappelmann"\<close>
subsection \<open>Fact Tactic\<close>
theory Unify_Fact_Tactic
  imports
    Unify_Fact_Tactic_Base
    ML_Unifiers
begin

paragraph \<open>Summary\<close>
text \<open>Setup of fact tactic and examples.\<close>

ML\<open>
\<^functor_instance>\<open>struct_name = Standard_Unify_Fact
  and functor_name = Unify_Fact
  and id = \<open>""\<close>
  and more_args = \<open>val init_args = {
    normalisers = SOME Standard_Mixed_Unification.norms_first_higherp_decomp_comb_higher_unify,
    unifier = SOME Standard_Mixed_Unification.first_higherp_decomp_comb_higher_unify
  }\<close>\<close>
\<close>
local_setup \<open>Standard_Unify_Fact.setup_attribute NONE\<close>
local_setup \<open>Standard_Unify_Fact.setup_method NONE\<close>

paragraph \<open>Examples\<close>

experiment
begin
lemma
  assumes h: "\<And>x y. PROP P x y"
  shows "PROP P x y"
  by (ufact h)

lemma
  assumes "\<And>P y. PROP P y x"
  shows "PROP P x"
  (* by (ufact assms where unifier = Higher_Order_Unification.unify) \<comment>\<open>the line below is equivalent\<close> *)
  supply [[ufact unifier = Higher_Order_Unification.unify]] by (ufact assms)

lemma
  assumes "\<And>x y. PROP A x \<Longrightarrow> PROP B x \<Longrightarrow> PROP P x"
  shows "\<And>x y. PROP A x \<Longrightarrow> PROP B x \<Longrightarrow> PROP P x"
  using assms by ufact
end

end
