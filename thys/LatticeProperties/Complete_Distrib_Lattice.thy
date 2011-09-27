header {* Complete Distributive Lattices  *}

(*
    Author: Viorel Preoteasa
*)

theory Complete_Distrib_Lattice
imports Main
begin

text {*
This theory introduces complete distributive lattices and
complete Boolean algebras and proves the De Morgan's laws
for arbitrary conjunctions and disjunctions.
*}

context complete_distrib_lattice
begin

lemma inf_Sup_distrib1: "inf x (Sup Y) = (SUP y: Y . (inf x y))"
  by (rule inf_Sup)

lemma sup_Inf_distrib1: "(sup x (Inf Y)) = (INF y: Y . (sup x y))"
  by (rule sup_Inf)

lemma inf_Sup_distrib2: "inf (Sup Y) x = (SUP y: Y . (inf y x))"
  proof -
    have "inf (Sup Y) x = inf x (Sup Y)" by (simp add: inf_commute)
    also have "... = (SUP y: Y . (inf x y))" by (rule inf_Sup_distrib1)
    also have "... = (SUP y: Y . (inf y x))" by  (simp add: inf_commute)
    finally show ?thesis .
  qed

lemma sup_Inf_distrib2: "(sup (Inf Y) x) = (INF y: Y . (sup y x))"
  proof -
    have "sup (Inf Y) x = sup x (Inf Y)" by (simp add: sup_commute)
    also have "... = (INF y: Y . (sup x y))" by (rule sup_Inf_distrib1)
    also have "... = (INF y: Y . (sup y x))" by  (simp add: sup_commute)
    finally show ?thesis .
  qed

end

context complete_boolean_algebra
begin


lemma compl_Inf:
  "- (Inf X) = (SUP x : X . -x)"
  by (simp only: uminus_Inf SUP_def)

lemma compl_Sup:
  "- (Sup X) = (INF x : X . -x)"
  by (simp only: uminus_Sup INF_def)

end

end

