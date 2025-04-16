theory Tiebreakers
  imports Restricted_Order Nonground_Clause_Generic
begin

type_synonym ('g, 'a) tiebreakers = 
  "'g clause \<Rightarrow> 'a clause \<Rightarrow> 'a clause \<Rightarrow> bool"

locale tiebreakers =
  fixes tiebreakers :: "('g, 'a) tiebreakers"
  assumes "\<And>C\<^sub>G. wfp (tiebreakers C\<^sub>G) \<and> transp (tiebreakers C\<^sub>G)"
begin

sublocale wellfounded_strict_order "tiebreakers C\<^sub>G"
  using tiebreakers_axioms tiebreakers_def wfp_imp_asymp
  by unfold_locales auto  

end

end
