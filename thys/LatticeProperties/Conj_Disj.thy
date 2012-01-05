header {* Conjunctive and Disjunctive Functions *}

(*
    Author: Viorel Preoteasa
*)

theory Conj_Disj
imports Main
begin

text{*
This theory introduces the definitions and some properties for 
conjunctive, disjunctive, universally conjunctive, and universally 
disjunctive functions.
*}

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
  apply (subgoal_tac "{y\<Colon>'a. \<exists>f . (\<exists>y \<in> X. \<forall>x::'a . f x = y) \<and> y = f bot} = X \<and> 
      {y\<Colon>'a. \<exists>f. (\<exists>xa. (\<exists>y \<in> X. \<forall>x\<Colon>'a. xa x = y) \<and> 
      (\<forall>xb\<Colon>'a. f xb = x (xa xb))) \<and> y = f bot} = {y\<Colon>'a. \<exists>xa\<Colon>'a\<in>X. y = x xa}")
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

lemma apply_comp_Disjunctive: "Apply.Disjunctive = Comp.Disjunctive"
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
  by simp

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
  by simp

end
