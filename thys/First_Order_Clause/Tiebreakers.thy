theory Tiebreakers
  imports Restricted_Order Nonground_Clause
begin

type_synonym ('f, 'v) tiebreakers = 
  "'f gatom clause \<Rightarrow> ('f, 'v) atom clause \<Rightarrow> ('f, 'v) atom clause \<Rightarrow> bool"

locale tiebreakers =
  fixes tiebreakers :: "('f, 'v) tiebreakers"
  assumes "\<And>C\<^sub>G. wfp (tiebreakers C\<^sub>G) \<and> transp (tiebreakers C\<^sub>G)"
begin

sublocale wellfounded_strict_order "tiebreakers C\<^sub>G"
  using tiebreakers_axioms tiebreakers_def wfp_imp_asymp
  by unfold_locales auto  

end

end
