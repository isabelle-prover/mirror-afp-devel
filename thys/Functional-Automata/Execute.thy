(*  Author:    Lukas Bulwahn, TUM 2011 *)

section {* Executing Automata and membership of Regular Expressions  *}

theory Execute
imports AutoRegExp
begin

subsection {* Example *}

definition example_expression
where
  "example_expression = (let r0 = Atom (0::nat); r1 = Atom (1::nat)
     in Times (Star (Plus (Times r1 r1) r0)) (Star (Plus (Times r0 r0) r1)))"

value "NA.accepts (rexp2na example_expression) [0,1,1,0,0,1]"

value "DA.accepts (na2da (rexp2na example_expression)) [0,1,1,0,0,1]"

end
