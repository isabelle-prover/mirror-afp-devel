(*  
    Title:      Code_Set.thy
    Author:     Jose Divasón <jose.divasonm at unirioja.es>
    Author:     Jesús Aransay <jesus-maria.aransay at unirioja.es>
*)

section "Code set"

theory Code_Set
imports
  "HOL-Library.Code_Cardinality"
begin

lemma [code]:
  \<open>UNIV = set Enum.enum\<close>
  by (fact UNIV_enum)

lemma [code_unfold]:
  \<open>- (Collect P) = Set.filter (Not \<circ> P) UNIV\<close>
  by auto

end
