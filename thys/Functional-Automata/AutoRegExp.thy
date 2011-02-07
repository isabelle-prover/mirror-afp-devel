(*  Author:     Tobias Nipkow
    Copyright   1998 TUM
*)

header "Combining automata and regular expressions, including code generation"

theory AutoRegExp
imports Automata RegExp2NA RegExp2NAe "~~/src/HOL/Library/Executable_Set"
begin

theorem "DA.accepts (na2da(rexp2na r)) w = (w : lang r)"
by (simp add: NA_DA_equiv[THEN sym] accepts_rexp2na)

theorem  "DA.accepts (nae2da(rexp2nae r)) w = (w : lang r)"
by (simp add: NAe_DA_equiv accepts_rexp2nae)

(* Testing code generation: *)

declare RegExp2NA.star_def [unfolded RegExp2NA.epsilon_def, code]
declare rexp2na.simps(2) [unfolded RegExp2NA.epsilon_def, code]
        rexp2na.simps(1,3-)[code]

code_module Generated
contains
  test =
  "let r0 = Atom(0::nat);
       r1 = Atom(1::nat);
       re = Times (Star(Plus(Times r1 r1)r0))
              (Star(Plus(Times r0 r0)r1));
       N = rexp2na re;
       D = na2da N
  in (NA.accepts N [0,1,1,0,0,1], DA.accepts D [0,1,1,0,0,1])"

end
