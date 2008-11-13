(*File: Lattice.thy*)
(*Authors: Lennart Beringer and Martin Hofmann, LMU Munich 2008*)
theory Lattice imports Main begin
section{*Lattices*}

text{*In preparation of the encoding of the type system of Hunt and
Sands, we define some abstract type of lattices, together with the
operations $\bot$, $\sqsubseteq$ and $\sqcup$, and some obvious
axioms.*}

typedecl L (*The lattice*)

consts bottom :: L
consts LEQ :: "L \<Rightarrow> L \<Rightarrow> bool"
consts LUB :: "L \<Rightarrow> L \<Rightarrow> L"

axioms LAT1[rule_format]:"LEQ bottom p"
axioms LAT2[rule_format]:
  "LEQ p1 p2 \<longrightarrow> LEQ p2 p3 \<longrightarrow> LEQ p1 p3"
axioms LAT3[rule_format]:"LEQ p (LUB p q)"
axioms LAT4[rule_format]:"LUB p q = LUB q p"
axioms LAT5[rule_format]:"LUB p (LUB q r) = LUB (LUB p q) r"
axioms LAT6[rule_format]:"LEQ x x"
axioms LAT7:"p = LUB p p"
text{*End of theory Lattice*}
end