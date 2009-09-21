(*  ID:         $Id: AutoRegExp.thy,v 1.14 2009-08-11 09:46:50 fhaftmann Exp $
    Author:     Tobias Nipkow
    Copyright   1998 TUM
*)

header "Combining automata and regular expressions, including code generation"

theory AutoRegExp
imports Automata RegExp2NA RegExp2NAe Executable_Set
begin

theorem "DA.accepts (na2da(rexp2na r)) w = (w : lang r)"
by (simp add: NA_DA_equiv[THEN sym] accepts_rexp2na)

theorem  "DA.accepts (nae2da(rexp2nae r)) w = (w : lang r)"
by (simp add: NAe_DA_equiv accepts_rexp2nae)

(* Testing code generation: *)

declare RegExp2NA.star_def [unfolded epsilon_def, code]

code_module Generated
contains
  test =
  "let r0 = Atom(0::nat);
       r1 = Atom(1::nat);
       re = Conc (Star(Or(Conc r1 r1)r0))
              (Star(Or(Conc r0 r0)r1));
       N = rexp2na re;
       D = na2da N
  in (NA.accepts N [0,1,1,0,0,1], DA.accepts D [0,1,1,0,0,1])"

end
