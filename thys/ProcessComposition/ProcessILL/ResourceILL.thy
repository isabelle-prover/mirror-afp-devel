theory ResourceILL
  imports
    ResTermILL
    ProcessComposition.Resource
begin

section\<open>Resources as ILL Propositions\<close>

text\<open>ILL translation of a resource is the translation of its normal form representative\<close>
definition resource_to_ill :: "('a, 'b) resource \<Rightarrow> ('a + 'b) ill_prop"
  where [simp]: "resource_to_ill x = res_term_to_ill (of_resource x)"

text\<open>This translation is injective because the term translation is injective on normalised terms\<close>
lemma resource_to_ill_inject:
  fixes x y :: "('a, 'b) resource"
  shows "resource_to_ill x = resource_to_ill y \<Longrightarrow> x = y"
  unfolding resource_to_ill_def
proof transfer
  fix x y :: "('a, 'b) res_term"
  assume "res_term_to_ill (normal_rewr x) = res_term_to_ill (normal_rewr y)"
  then show "x \<sim> y"
    using res_term_to_ill_inject res_term_equiv_is_normal_rewr normal_rewr_normalised by blast
qed

end