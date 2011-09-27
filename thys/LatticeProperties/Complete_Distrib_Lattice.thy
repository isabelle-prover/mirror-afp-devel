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

class complete_distrib_lattice = complete_lattice +
  assumes inf_Sup_distrib1: "inf x (Sup Y) = (SUP y: Y . (inf x y))"
  and sup_Inf_distrib1: "(sup x (Inf Y)) = (INF y: Y . (sup x y))"

begin

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

subclass distrib_lattice
  proof
    fix x y z
    have "sup x (inf y z) = sup x (Inf {y, z})" by (simp add: Inf_binary)
    also have "... = Inf {sup x y, sup x z}" by (simp add: sup_Inf_distrib1 INFI_def)
    also have "... = inf (sup x y) (sup x z)" by  (simp add: Inf_binary)
    finally show "sup x (inf y z) = inf (sup x y) (sup x z)" .
  qed
end

instantiation "fun" :: (type, complete_distrib_lattice) complete_distrib_lattice
begin
  instance proof
  fix x::"('a \<Rightarrow> 'b)" fix Y
    show  "inf x (Sup Y) = (SUP y:Y. (inf x y))"
    apply (simp_all add: fun_eq_iff inf_fun_def SUPR_def Sup_fun_def inf_Sup_distrib1)
    apply safe
    apply (subgoal_tac " (inf (x xa) ` {y. \<exists>f\<in>Y. y = f xa}) = {y. \<exists>f\<in>Y. y = inf (x xa) (f xa)}")
    by auto
  next
  fix x::"('a \<Rightarrow> 'b)" fix Y
    show  "sup x (Inf Y) = (INF y:Y. (sup x y))"
    apply (simp_all add: fun_eq_iff INFI_def Inf_fun_def sup_fun_def sup_Inf_distrib1)
    apply safe
    apply (case_tac "(sup (x xa) ` {y. \<exists>f\<in>Y. y = f xa}) = {y. \<exists>f\<in>Y. y = sup (x xa) (f xa)}")
    by auto
  qed

end

instantiation "bool" :: complete_distrib_lattice
begin
  instance proof
  fix x::bool fix Y
    show  "inf x (Sup Y) = (SUP y:Y. (inf x y))"
    by (simp_all add: inf_bool_def SUPR_def Sup_bool_def)
  next
  fix x::bool fix Y
    show  "sup x (Inf Y) = (INF y:Y. (sup x y))"
    by (simp_all add: sup_bool_def INFI_def Inf_bool_def)
  qed
end

class complete_boolean_algebra = complete_distrib_lattice + boolean_algebra
begin


lemma compl_Inf:
  "- (Inf X) = (SUP x : X . -x)"
  apply (rule compl_unique)
  apply (simp add: SUPR_def)
  apply (unfold inf_Sup_distrib1)
  apply (simp add: SUPR_def)
  apply (rule antisym, simp_all)
  apply (rule_tac Sup_least)
  apply safe
  apply (rule_tac y = "inf xb (- xb)"  in order_trans, simp_all)
  apply (rule_tac y = "Inf X"  in order_trans, simp_all)
  apply (rule Inf_lower, simp)
  apply (unfold inf_compl_bot)
  apply simp
  apply (unfold sup_Inf_distrib2)
  apply (simp add: INFI_def)
  apply (rule antisym, simp_all)
  apply (rule Inf_greatest, safe)
  apply (rule_tac y = "sup y (-y)"  in order_trans, simp_all)
  apply (simp add: sup_compl_top)
  apply (rule_tac y = "SUPR X uminus"  in order_trans, simp_all)
  apply (simp add: SUPR_def)
  apply (rule Sup_upper)
  by (simp add: image_def)

lemma compl_Sup:
  "- (Sup X) = (INF x : X . -x)"
  apply (subst compl_eq_compl_iff [THEN sym])
  apply (simp add: INFI_def compl_Inf SUPR_def)
  apply (subgoal_tac "X = uminus ` uminus ` X")
  apply (simp_all add: image_def)
  by auto

end

instantiation "fun" :: (type, complete_boolean_algebra) complete_boolean_algebra
begin
  instance proof qed
end

instantiation "bool" :: complete_boolean_algebra
begin
  instance proof qed
end

end

