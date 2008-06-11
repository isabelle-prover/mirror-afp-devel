(*  Title:      RSAPSS/Mod.thy
    ID:         $Id: Mod.thy,v 1.4 2008-06-11 14:22:59 lsf37 Exp $
    Author:     Christina Lindenberg, Kai Wirt, Technische Universität Darmstadt
    Copyright:  2005 - Technische Universität Darmstadt 
*)

header "Leammata for modular arithmetic"

theory Mod
imports Main Efficient_Nat
begin

lemma divmultassoc: "a div (b*c) * (b*c) = ((a div (b * c)) * b)*(c::nat)"
  by (auto)

lemma delmod: "(a::nat) mod (b*c) mod c = a mod c"
  apply (subst mod_div_equality [THEN sym, of a "b*c"]);
  back
  apply (subst add_commute)
  apply (subst divmultassoc);
  by (simp add: mod_mult_self1);

lemma timesmod1: "((x::nat)*((y::nat) mod n)) mod (n::nat) = ((x*y) mod n)"
  apply (subst mod_mult_distrib2);
  apply (subst delmod);
  by (auto);

lemma timesmod3: "((a mod (n::nat)) * b) mod n = (a*b) mod n"
  apply (subst mult_commute);
  apply (subst timesmod1);
  apply (subst mult_commute);
  by (auto)

lemma remainderexplemma: "(y mod (a::nat) = z mod a) \<Longrightarrow> (x*y) mod a = (x*z) mod a"
  apply (subst timesmod1 [THEN sym]);
  apply (auto);
  apply (subst timesmod1);
  by (auto);

lemma remainderexp: "((a mod (n::nat))^i) mod n = (a^i) mod n"
  apply (induct_tac i);
  apply (auto);
  apply (subst timesmod3);
  apply (rule remainderexplemma);
  by (auto)

lemma oneexp: "(1::nat)^n = 1"
  apply (induct_tac n);
  by (auto);

lemma sucis: "Suc 0 = (1::nat)"
  by (auto);

end
