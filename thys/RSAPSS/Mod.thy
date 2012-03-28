(*  Title:      RSAPSS/Mod.thy

    Author:     Christina Lindenberg, Kai Wirt, Technische Universität Darmstadt
    Copyright:  2005 - Technische Universität Darmstadt 
*)

header "Leammata for modular arithmetic"

theory Mod
imports Main
begin

lemma divmultassoc: "a div (b*c) * (b*c) = ((a div (b * c)) * b)*(c::nat)"
  by auto

lemma delmod: "(a::nat) mod (b*c) mod c = a mod c"
  apply (subst (2) mod_div_equality [symmetric, of a "b*c"])
  apply (subst add_commute)
  apply (subst divmultassoc)
  apply (simp add: mod_mult_self1)
  done

lemma timesmod1: "((x::nat)*((y::nat) mod n)) mod (n::nat) = ((x*y) mod n)"
  apply (subst mult_mod_right)
  apply (subst delmod)
  apply auto
  done

lemma timesmod3: "((a mod (n::nat)) * b) mod n = (a*b) mod n"
  apply (subst mult_commute)
  apply (subst timesmod1)
  apply (subst mult_commute)
  apply auto
  done

lemma remainderexplemma: "(y mod (a::nat) = z mod a) \<Longrightarrow> (x*y) mod a = (x*z) mod a"
  apply (subst timesmod1 [symmetric])
  apply auto
  apply (subst timesmod1)
  apply auto
  done

lemma remainderexp: "((a mod (n::nat))^i) mod n = (a^i) mod n"
  apply (induct i)
  apply auto
  apply (subst timesmod3)
  apply (rule remainderexplemma)
  apply auto
  done

end
