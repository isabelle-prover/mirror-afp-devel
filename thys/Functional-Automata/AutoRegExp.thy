(*  ID:         $Id: AutoRegExp.thy,v 1.5 2004-08-19 10:54:14 nipkow Exp $
    Author:     Tobias Nipkow
    Copyright   1998 TUM
*)

header "Combining automata and regular expressions, including code generation"

theory AutoRegExp
imports Automata RegExp2NA RegExp2NAe
begin

theorem "DA.accepts (na2da(rexp2na r)) w = (w : lang r)"
by (simp add: NA_DA_equiv[THEN sym] accepts_rexp2na)

theorem  "DA.accepts (nae2da(rexp2nae r)) w = (w : lang r)"
by (simp add: NAe_DA_equiv accepts_rexp2nae)

(* Testing code generation: *)

types_code
  set ("_ list")

consts_code
  "{}"     ("[]")
  "insert" ("(_ ins _)")
  "op :"   ("(_ mem _)")
  "op Un"  ("(_ union _)")
  "image"  ("map")
  "UNION"  ("(fn A => fn f => flat(map f A))")
  "Bex"    ("(fn A => fn f => exists f A)")

generate_code
  test = "let r0 = Atom(0::nat);
              r1 = Atom(1::nat);
              re = Conc (Star(Or(Conc r1 r1)r0))
                        (Star(Or(Conc r0 r0)r1));
              N = rexp2na re;
              D = na2da N
          in (NA.accepts N [0,1,1,0,0,1], DA.accepts D [0,1,1,0,0,1])"
ML test

end
