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

class inf = 
  fixes inf :: "'a => 'a => 'a" (infixl "\<sqinter>" 70)

class sup = 
  fixes sup :: "'a => 'a => 'a" (infixl "\<squnion>" 65)

class semilattice_inf_infix = order + inf +
  assumes semilattice_inf: "class.semilattice_inf (op \<le>) (op <) inf"

sublocale semilattice_inf_infix < semilattice_inf "op \<le>" "op <" inf
  by (rule semilattice_inf)

context semilattice_inf_infix begin
lemma [simp]: "x \<sqinter> y \<sqinter> z \<le> x"
  by (metis inf_le1 order_trans)

lemma [simp]: "x \<sqinter> y \<sqinter> z \<le> y"
  by (rule_tac y = "x \<sqinter> y" in order_trans, rule inf_le1, simp)

lemma [simp]: "x \<sqinter> (y \<sqinter> z) \<le> y"
  by (rule_tac y = "y \<sqinter> z" in order_trans, rule inf_le2, simp)

lemma [simp]: "x \<sqinter> (y \<sqinter> z) \<le> z"
  by (rule_tac y = "y \<sqinter> z" in order_trans, rule inf_le2, simp)
end

class semilattice_sup_infix = order + sup +
  assumes semilattice_sup: "class.semilattice_sup (op \<le>) (op <) sup"

sublocale semilattice_sup_infix < semilattice_sup  "op \<le>" "op <" sup
  by (rule semilattice_sup)

context semilattice_sup_infix begin

lemma [simp]: "x \<le> x \<squnion> y \<squnion> z"
  by (rule_tac y = "x \<squnion> y" in order_trans, simp_all) 

lemma [simp]: "y \<le> x \<squnion> y \<squnion> z"
  by (rule_tac y = "x \<squnion> y" in order_trans, simp_all)

lemma [simp]: "y \<le> x \<squnion> (y \<squnion> z)"
  by (rule_tac y = "y \<squnion> z" in order_trans, simp_all)

lemma [simp]: "z \<le> x \<squnion> (y \<squnion> z)"
  by (rule_tac y = "y \<squnion> z" in order_trans, simp_all)
end

class lattice_infix = order + inf + sup +
  assumes lattice: "class.lattice (op \<le>) (op <) inf sup"

sublocale lattice_infix < lattice  "op \<le>" "op <" inf sup
  by (rule lattice)

context lattice_infix begin

subclass semilattice_inf_infix
  proof qed

subclass semilattice_sup_infix
  proof qed

lemma [simp]: "x \<sqinter> y \<le> x \<squnion> z"
  by (rule_tac y = x in order_trans, simp_all)

lemma [simp]: "y \<sqinter> x \<le> x \<squnion> z"
  by (rule_tac y = x in order_trans, simp_all)

lemma [simp]: "x \<sqinter> y \<le> z \<squnion> x"
  by (rule_tac y = x in order_trans, simp_all)

lemma [simp]: "y \<sqinter> x \<le> z \<squnion> x"
  by (rule_tac y = x in order_trans, simp_all)

end

class distrib_lattice_infix = lattice_infix +
  assumes distrib_lattice: "class.distrib_lattice op \<le> op < inf sup"

sublocale distrib_lattice_infix < distrib_lattice "op \<le>" "op <" inf sup
  by (rule distrib_lattice)

end