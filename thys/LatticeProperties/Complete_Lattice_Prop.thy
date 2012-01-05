header {* Fixpoints and Complete Lattices *}

(*
    Author: Viorel Preoteasa
*)

theory Complete_Lattice_Prop
imports WellFoundedTransitive
begin

text{*
This theory introduces some results about fixpoints of functions on 
complete lattices. The main result is that a monotonic function 
mapping momotonic functions to monotonic functions has the least 
fixpoint monotonic.
*}

context complete_lattice begin

lemma inf_Inf: assumes nonempty: "A \<noteq> {}"
   shows "inf x (Inf A) = Inf ((inf x) ` A)"
  apply (rule antisym, simp_all)
  apply (rule Inf_greatest)
  apply (simp add: image_def, safe, simp)
  apply (rule_tac y = "Inf A" in order_trans, simp_all)
  apply (rule Inf_lower, simp)
  apply (cut_tac nonempty)
  apply safe
  apply (erule notE)
  apply (rule_tac y = "inf x xa" in order_trans)
  apply (rule Inf_lower, simp add: image_def, blast)
  apply simp
  apply (rule Inf_greatest)
  apply (rule_tac y = "inf x xa" in order_trans)
  apply (rule Inf_lower)
  apply (simp add: image_def)
  by auto

end


(*
Monotonic applications which map monotonic to monotonic have monotonic fixpoints
*)

definition
  "mono_mono F = (mono F \<and> (\<forall> f . mono f \<longrightarrow> mono (F f)))"

theorem lfp_mono [simp]:
  "mono_mono F \<Longrightarrow> mono (lfp F)"
  apply (simp add: mono_mono_def)
  apply (rule_tac f="F" and P = "mono" in lfp_ordinal_induct)
  apply auto
  apply (simp add: mono_def)
  apply auto
  apply (simp_all add: Sup_fun_def)
  apply (rule SUP_least)
  apply (rule_tac y = "f y" in order_trans)
  apply auto
  apply (rule SUP_upper)
  by auto

context complete_lattice begin

definition
  "Sup_less x (w::'b::well_founded) = Sup {y ::'a . \<exists> v < w . y = x v}"

lemma Sup_less_upper:
  "v < w \<Longrightarrow> P v \<le> Sup_less P w"
  by (simp add: Sup_less_def, rule Sup_upper, blast)


lemma Sup_less_least:
  "(!! v . v < w \<Longrightarrow> P v \<le> Q) \<Longrightarrow> Sup_less P w \<le> Q"
  by (simp add: Sup_less_def, rule Sup_least, blast)

end

lemma Sup_less_fun_eq:
  "((Sup_less P w) i) = (Sup_less (\<lambda> v . P v i)) w"
  apply (simp add: Sup_less_def Sup_fun_def SUP_def)
  by (rule_tac f = Sup in arg_cong, auto)

theorem fp_wf_induction:
  "f x  = x \<Longrightarrow> mono f \<Longrightarrow> (\<forall> w . (y w) \<le> f (Sup_less y w)) \<Longrightarrow> Sup (range y) \<le> x"
  apply (rule Sup_least)
  apply (simp add: image_def, safe, simp)
  apply (rule less_induct1, simp_all)
  apply (rule_tac y = "f (Sup_less y xa)" in order_trans, simp)
  apply (drule_tac x = "Sup_less y xa" and y = "x" in monoD)
  by (simp add: Sup_less_least, auto)

end
