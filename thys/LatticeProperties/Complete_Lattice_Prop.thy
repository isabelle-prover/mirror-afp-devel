header {* Complete Lattice Properties *}

(*
    Author: Viorel Preoteasa
*)

theory Complete_Lattice_Prop
imports Main
begin

text{*
This theory introduces some results about complete lattices. The
main result is that a monotonic function mapping momotonic
functions to monotonic functions has the least fixpoint monotonic.
*}

context complete_lattice begin

theorem Sup_bottom:
  "(Sup X = bot) = (\<forall> x \<in> X . x = bot)"
  by (rule Sup_bot_conv)

theorem Inf_top:
  "(Inf X = top) = (\<forall> x \<in> X . x = top)"
  by (rule Inf_top_conv)

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


class well_founded_transitive = ord +
  assumes order_trans1: "x < y \<Longrightarrow> y < z \<Longrightarrow> x < z"
  and less_eq_def: "x \<le> y <-> x = y \<or> x < y"
  and less_induct1 [case_names less]: "(!!x . (!!y . y < x \<Longrightarrow> P y) \<Longrightarrow> P x) \<Longrightarrow> P a"


context complete_lattice begin

definition
  "Sup_less x (w::'b::well_founded_transitive) = Sup {y . \<exists> v < w . y = x v}"

end

theorem fp_wf_induction:
  "f x  = x \<Longrightarrow> mono f \<Longrightarrow> (\<forall> w . (y w) \<le> f (Sup_less y w)) \<Longrightarrow> Sup (range y) \<le> x"
  apply (rule Sup_least)
  apply (simp add: image_def, safe, simp)
  apply (rule less_induct1, simp_all)
  apply (rule_tac y = "f (Sup_less y xa)" in order_trans, simp)
  apply (drule_tac x = "Sup_less y xa" and y = "x" in monoD)
  apply (simp add: Sup_less_def)
  apply (rule Sup_least)
  by auto

locale conjunctive =
  fixes inf_b :: "'b \<Rightarrow> 'b \<Rightarrow> 'b"
  and inf_c :: "'c \<Rightarrow> 'c \<Rightarrow> 'c"
  and times_abc :: "'a \<Rightarrow> 'b \<Rightarrow> 'c"
begin

definition
  "conjunctive = {x . (\<forall> y z . times_abc x (inf_b y z) = inf_c (times_abc x y) (times_abc x z))}"

lemma conjunctiveD: "x \<in> conjunctive \<Longrightarrow> times_abc x (inf_b y z) = inf_c (times_abc x y) (times_abc x z)"
  by (simp add: conjunctive_def)

end

interpretation Apply: conjunctive "inf::'a::semilattice_inf \<Rightarrow> 'a \<Rightarrow> 'a"
  "inf::'b::semilattice_inf \<Rightarrow> 'b \<Rightarrow> 'b" "\<lambda> f . f"
  done

interpretation Comp: conjunctive "inf::('a::lattice \<Rightarrow> 'a) \<Rightarrow> ('a \<Rightarrow> 'a) \<Rightarrow> ('a \<Rightarrow> 'a)" 
  "inf::('a::lattice \<Rightarrow> 'a) \<Rightarrow> ('a \<Rightarrow> 'a) \<Rightarrow> ('a \<Rightarrow> 'a)" "(op o)"
  done

lemma "Apply.conjunctive = Comp.conjunctive"
  apply (simp add: Apply.conjunctive_def Comp.conjunctive_def)
  apply safe
  apply (simp_all add: fun_eq_iff inf_fun_def)
  apply (drule_tac x = "\<lambda> u . y" in spec)
  apply (drule_tac x = "\<lambda> u . z" in spec)
  by simp

locale disjunctive =
  fixes sup_b :: "'b \<Rightarrow> 'b \<Rightarrow> 'b"
  and sup_c :: "'c \<Rightarrow> 'c \<Rightarrow> 'c"
  and times_abc :: "'a \<Rightarrow> 'b \<Rightarrow> 'c"
begin

definition
  "disjunctive = {x . (\<forall> y z . times_abc x (sup_b y z) = sup_c (times_abc x y) (times_abc x z))}"

lemma disjunctiveD: "x \<in> disjunctive \<Longrightarrow> times_abc x (sup_b y z) = sup_c (times_abc x y) (times_abc x z)"
  by (simp add: disjunctive_def)

end

interpretation Apply: disjunctive "sup::'a::semilattice_sup \<Rightarrow> 'a \<Rightarrow> 'a"
  "sup::'b::semilattice_sup \<Rightarrow> 'b \<Rightarrow> 'b" "\<lambda> f . f"
  done

interpretation Comp: disjunctive "sup::('a::lattice \<Rightarrow> 'a) \<Rightarrow> ('a \<Rightarrow> 'a) \<Rightarrow> ('a \<Rightarrow> 'a)" 
  "sup::('a::lattice \<Rightarrow> 'a) \<Rightarrow> ('a \<Rightarrow> 'a) \<Rightarrow> ('a \<Rightarrow> 'a)" "(op o)"
  done

lemma apply_comp_disjunctive: "Apply.disjunctive = Comp.disjunctive"
  apply (simp add: Apply.disjunctive_def Comp.disjunctive_def)
  apply safe
  apply (simp_all add: fun_eq_iff sup_fun_def)
  apply (drule_tac x = "\<lambda> u . y" in spec)
  apply (drule_tac x = "\<lambda> u . z" in spec)
  by simp

locale Conjunctive =
  fixes Inf_b :: "'b set \<Rightarrow> 'b"
  and Inf_c :: "'c set \<Rightarrow> 'c"
  and times_abc :: "'a \<Rightarrow> 'b \<Rightarrow> 'c"
begin

definition
  "Conjunctive = {x . (\<forall> X . times_abc x (Inf_b X) = Inf_c ((times_abc x) ` X) )}"
end

interpretation Apply: Conjunctive Inf Inf "\<lambda> f . f"
  done

interpretation Comp: Conjunctive "Inf::(('a::complete_lattice \<Rightarrow> 'a) set) \<Rightarrow> ('a \<Rightarrow> 'a)" 
  "Inf::(('a::complete_lattice \<Rightarrow> 'a) set) \<Rightarrow> ('a \<Rightarrow> 'a)" "(op o)"
  done

lemma fun_eq: "x = y \<Longrightarrow> f x = f y"
  by simp

lemma "Apply.Conjunctive = Comp.Conjunctive"
  apply (simp add: Apply.Conjunctive_def Comp.Conjunctive_def)
  apply safe
  apply (simp add: fun_eq_iff  Inf_fun_def comp_def image_def)
  apply (simp only: INF_def)
  apply safe
  apply (rule_tac f = Inf in fun_eq)
  apply auto
  apply (drule_tac x = "{x . \<exists> y \<in> X . x = (\<lambda> u . y)}" in spec)
  apply (simp add: fun_eq_iff  Inf_fun_def comp_def image_def)
  apply (drule_tac x = "bot" in spec)
  apply (subgoal_tac "{y\<Colon>'a. \<exists>f . (\<exists>y \<in> X. \<forall>x::'a . f x = y) \<and> y = f bot} = X \<and> {y\<Colon>'a. \<exists>f. (\<exists>xa. (\<exists>y \<in> X. \<forall>x\<Colon>'a. xa x = y) \<and> (\<forall>xb\<Colon>'a. f xb = x (xa xb))) \<and> y = f bot} = {y\<Colon>'a. \<exists>xa\<Colon>'a\<in>X. y = x xa}")
  apply (simp add: INF_def image_def, safe)
  apply simp_all
  apply auto[1]
  apply auto [1]
  apply (rule_tac x = "\<lambda> u . x xaa" in exI)
  by auto


locale Disjunctive =
  fixes Sup_b :: "'b set \<Rightarrow> 'b"
  and Sup_c :: "'c set \<Rightarrow> 'c"
  and times_abc :: "'a \<Rightarrow> 'b \<Rightarrow> 'c"
begin

definition
  "Disjunctive = {x . (\<forall> X . times_abc x (Sup_b X) = Sup_c ((times_abc x) ` X) )}"
end

interpretation Apply: Disjunctive Sup Sup "\<lambda> f . f"
  done

interpretation Comp: Disjunctive "Sup::(('a::complete_lattice \<Rightarrow> 'a) set) \<Rightarrow> ('a \<Rightarrow> 'a)" 
  "Sup::(('a::complete_lattice \<Rightarrow> 'a) set) \<Rightarrow> ('a \<Rightarrow> 'a)" "(op o)"
  done

lemma "Apply.Disjunctive = Comp.Disjunctive"
  apply (simp add: Apply.Disjunctive_def Comp.Disjunctive_def)
  apply safe
  apply (simp add: fun_eq_iff  Sup_fun_def comp_def image_def)
  apply (simp only: SUP_def)
  apply safe
  apply (rule_tac f = Sup in fun_eq)
  apply auto
  apply (drule_tac x = "{x . \<exists> y \<in> X . x = (\<lambda> u . y)}" in spec)
  apply (simp add: fun_eq_iff  Sup_fun_def comp_def image_def)
  apply (drule_tac x = "bot" in spec)
  apply (subgoal_tac "{y. \<exists>f::'a \<Rightarrow> 'a. (\<exists>y\<in>X. \<forall>x. f x = y) \<and> y = f bot} = X 
    \<and> {y. \<exists>f::'a \<Rightarrow> 'a. (\<exists>xa. (\<exists>y\<in>X. \<forall>x. xa x = y) \<and> (\<forall>xb. f xb = x (xa xb))) \<and> y = f bot} = {y. \<exists>xa\<in>X. y = x xa}")
  apply (simp add: SUP_def image_def, safe)
  apply simp_all
  apply auto[1]
  apply auto [1]
  apply (rule_tac x = "\<lambda> u . x xaa" in exI)
  by auto


lemma [simp]: "(F::'a::complete_lattice \<Rightarrow> 'b::complete_lattice) \<in> Apply.Conjunctive \<Longrightarrow> F \<in> Apply.conjunctive"
  apply (simp add: Apply.Conjunctive_def Apply.conjunctive_def)
  apply safe
  apply (drule_tac x = "{y, z}" in spec)
  by simp

lemma [simp]: "F \<in> Apply.conjunctive \<Longrightarrow> mono F"
  apply (simp add: Apply.conjunctive_def mono_def)
  apply safe
  apply (drule_tac x = "x" in spec)
  apply (drule_tac x = "y" in spec)
  apply (subgoal_tac "inf x y = x")
  apply simp
  apply (subgoal_tac "inf (F x) (F y) \<le> F y")
  apply simp
  apply (rule inf_le2)
  apply (rule antisym)
  by simp_all

lemma [simp]: "(F::'a::complete_lattice \<Rightarrow> 'b::complete_lattice) \<in> Apply.Conjunctive \<Longrightarrow> F top = top"
  apply (simp add: Apply.Conjunctive_def)
  apply (drule_tac x="{}" in spec)
  by (simp add: Inf_empty)

lemma [simp]: "(F::'a::complete_lattice \<Rightarrow> 'b::complete_lattice) \<in> Apply.Disjunctive \<Longrightarrow> F \<in> Apply.disjunctive"
  apply (simp add: Apply.Disjunctive_def Apply.disjunctive_def)
  apply safe
  apply (drule_tac x = "{y, z}" in spec)
  by simp

lemma [simp]: "F \<in> Apply.disjunctive \<Longrightarrow> mono F"
  apply (simp add: Apply.disjunctive_def mono_def)
  apply safe
  apply (drule_tac x = "x" in spec)
  apply (drule_tac x = "y" in spec)
  apply (subgoal_tac "sup x y = y")
  apply simp
  apply (subgoal_tac "F x \<le> sup (F x) (F y)")
  apply simp
  apply (rule sup_ge1)
  apply (rule antisym)
  apply simp
  by (rule sup_ge2)

lemma [simp]: "(F::'a::complete_lattice \<Rightarrow> 'b::complete_lattice) \<in> Apply.Disjunctive \<Longrightarrow> F bot = bot"
  apply (simp add: Apply.Disjunctive_def)
  apply (drule_tac x="{}" in spec)
  by (simp add: Sup_empty)

end
