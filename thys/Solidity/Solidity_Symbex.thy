section\<open>Towards a Setup for Symbolic Evaluation of Solidity\<close>
text\<open>
  In this chapter, we lay out the foundations for a tactic for executing 
  Solidity statements and expressions symbolically.
\<close>
theory Solidity_Symbex
imports
  Main
  "HOL-Eisbach.Eisbach"
begin

lemma string_literal_cat: "a+b = String.implode ((String.explode a) @ (String.explode b))"
  by (metis String.implode_explode_eq plus_literal.rep_eq)


lemma string_literal_conv: "(map String.ascii_of y = y) \<Longrightarrow>  (x = String.implode y) = (String.explode x = y) "
  by auto

lemmas string_literal_opt = Literal.rep_eq zero_literal.rep_eq plus_literal.rep_eq
                            string_literal_cat  string_literal_conv

named_theorems solidity_symbex
method solidity_symbex declares solidity_symbex =
   ((simp add:solidity_symbex cong:unit.case), (simp add:string_literal_opt)?; (code_simp|simp add:string_literal_opt)+)

declare Let_def [solidity_symbex]
        o_def [solidity_symbex]

end 
