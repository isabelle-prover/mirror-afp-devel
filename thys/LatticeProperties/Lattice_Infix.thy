header{* Lattice with infix operations *}

(*
    Author: Viorel Preoteasa
*)

theory Lattice_Infix
imports Main
begin

text{*
This theory introduces the inf and sup operators as clasess
and it redefines the lattice as subclass of inf and sup classes.
Some siplifications lemmas are also proved.
*}

notation inf (infixl "\<sqinter>" 70)

notation sup (infixl "\<squnion>" 65)

context semilattice_inf begin
lemma [simp]: "x \<sqinter> y \<sqinter> z \<le> x"
  by (metis inf_le1 order_trans)

lemma [simp]: "x \<sqinter> y \<sqinter> z \<le> y"
  by (rule_tac y = "x \<sqinter> y" in order_trans, rule inf_le1, simp)

lemma [simp]: "x \<sqinter> (y \<sqinter> z) \<le> y"
  by (rule_tac y = "y \<sqinter> z" in order_trans, rule inf_le2, simp)

lemma [simp]: "x \<sqinter> (y \<sqinter> z) \<le> z"
  by (rule_tac y = "y \<sqinter> z" in order_trans, rule inf_le2, simp)
end

context semilattice_sup begin

lemma [simp]: "x \<le> x \<squnion> y \<squnion> z"
  by (rule_tac y = "x \<squnion> y" in order_trans, simp_all) 

lemma [simp]: "y \<le> x \<squnion> y \<squnion> z"
  by (rule_tac y = "x \<squnion> y" in order_trans, simp_all)

lemma [simp]: "y \<le> x \<squnion> (y \<squnion> z)"
  by (rule_tac y = "y \<squnion> z" in order_trans, simp_all)

lemma [simp]: "z \<le> x \<squnion> (y \<squnion> z)"
  by (rule_tac y = "y \<squnion> z" in order_trans, simp_all)
end

context lattice begin

lemma [simp]: "x \<sqinter> y \<le> x \<squnion> z"
  by (rule_tac y = x in order_trans, simp_all)

lemma [simp]: "y \<sqinter> x \<le> x \<squnion> z"
  by (rule_tac y = x in order_trans, simp_all)

lemma [simp]: "x \<sqinter> y \<le> z \<squnion> x"
  by (rule_tac y = x in order_trans, simp_all)

lemma [simp]: "y \<sqinter> x \<le> z \<squnion> x"
  by (rule_tac y = x in order_trans, simp_all)

end

end