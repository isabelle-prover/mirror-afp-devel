section \<open>Monotone Formulas\<close>

text \<open>We define monotone formulas, i.e., without negation, 
  and show that usually the constant TRUE is not required.\<close>

theory Monotone_Formula
  imports Main
begin

subsection \<open>Definition\<close>

datatype 'a mformula =
  TRUE | FALSE |            \<comment> \<open>True and False\<close>
  Var 'a |                  \<comment> \<open>propositional variables\<close>
  Conj "'a mformula" "'a mformula" |  \<comment> \<open>conjunction\<close>
  Disj "'a mformula" "'a mformula"    \<comment> \<open>disjunction\<close>

text \<open>the set of subformulas of a mformula\<close>

fun SUB :: "'a mformula \<Rightarrow> 'a mformula set" where
  "SUB (Conj \<phi> \<psi>) = {Conj \<phi> \<psi>} \<union> SUB \<phi> \<union> SUB \<psi>" 
| "SUB (Disj \<phi> \<psi>) = {Disj \<phi> \<psi>} \<union> SUB \<phi> \<union> SUB \<psi>" 
| "SUB (Var x) = {Var x}" 
| "SUB FALSE = {FALSE}" 
| "SUB TRUE = {TRUE}" 

text \<open>the variables of a mformula\<close>

fun vars :: "'a mformula \<Rightarrow> 'a set" where
  "vars (Var x) = {x}" 
| "vars (Conj \<phi> \<psi>) = vars \<phi> \<union> vars \<psi>" 
| "vars (Disj \<phi> \<psi>) = vars \<phi> \<union> vars \<psi>" 
| "vars FALSE = {}" 
| "vars TRUE = {}" 

lemma finite_SUB[simp, intro]: "finite (SUB \<phi>)" 
  by (induct \<phi>, auto)

text \<open>The circuit-size of a mformula: number of subformulas\<close>

definition cs :: "'a mformula \<Rightarrow> nat" where 
  "cs \<phi> = card (SUB \<phi>)" 

text \<open>variable assignments\<close>

type_synonym 'a VAS = "'a \<Rightarrow> bool" 

text \<open>evaluation of mformulas\<close>

fun eval :: "'a VAS \<Rightarrow> 'a mformula \<Rightarrow> bool" where
  "eval \<theta> FALSE = False" 
| "eval \<theta> TRUE = True" 
| "eval \<theta> (Var x) = \<theta> x" 
| "eval \<theta> (Disj \<phi> \<psi>) = (eval \<theta> \<phi> \<or> eval \<theta> \<psi>)" 
| "eval \<theta> (Conj \<phi> \<psi>) = (eval \<theta> \<phi> \<and> eval \<theta> \<psi>)" 

lemma eval_vars: assumes "\<And> x. x \<in> vars \<phi> \<Longrightarrow> \<theta>1 x = \<theta>2 x" 
  shows "eval \<theta>1 \<phi> = eval \<theta>2 \<phi>" 
  using assms by (induct \<phi>, auto)

subsection \<open>Conversion of mformulas to true-free mformulas\<close>

inductive_set tf_mformula :: "'a mformula set" where
  tf_False: "FALSE \<in> tf_mformula" 
| tf_Var: "Var x \<in> tf_mformula" 
| tf_Disj: "\<phi> \<in> tf_mformula \<Longrightarrow> \<psi> \<in> tf_mformula \<Longrightarrow> Disj \<phi> \<psi> \<in> tf_mformula" 
| tf_Conj: "\<phi> \<in> tf_mformula \<Longrightarrow> \<psi> \<in> tf_mformula \<Longrightarrow> Conj \<phi> \<psi> \<in> tf_mformula" 

fun to_tf_formula where
  "to_tf_formula (Disj phi psi) = (let phi' = to_tf_formula phi; psi' = to_tf_formula psi
    in (if phi' = TRUE \<or> psi' = TRUE then TRUE else Disj phi' psi'))" 
| "to_tf_formula (Conj phi psi) = (let phi' = to_tf_formula phi; psi' = to_tf_formula psi
    in (if phi' = TRUE then psi' else if psi' = TRUE then phi' else Conj phi' psi'))" 
| "to_tf_formula phi = phi" 

lemma eval_to_tf_formula: "eval \<theta> (to_tf_formula \<phi>) = eval \<theta> \<phi>" 
  by (induct \<phi> rule: to_tf_formula.induct, auto simp: Let_def)

lemma to_tf_formula: "to_tf_formula \<phi> \<noteq> TRUE \<Longrightarrow> to_tf_formula \<phi> \<in> tf_mformula" 
  by (induct \<phi>, auto simp: Let_def intro: tf_mformula.intros)

lemma vars_to_tf_formula: "vars (to_tf_formula \<phi>) \<subseteq> vars \<phi>" 
  by (induct \<phi> rule: to_tf_formula.induct, auto simp: Let_def)

lemma SUB_to_tf_formula: "SUB (to_tf_formula \<phi>) \<subseteq> to_tf_formula ` SUB \<phi>" 
  by (induct \<phi> rule: to_tf_formula.induct, auto simp: Let_def)

lemma cs_to_tf_formula: "cs (to_tf_formula \<phi>) \<le> cs \<phi>" 
proof -
  have "cs (to_tf_formula \<phi>) \<le> card (to_tf_formula ` SUB \<phi>)" 
    unfolding cs_def by (rule card_mono[OF finite_imageI[OF finite_SUB] SUB_to_tf_formula])
  also have "\<dots> \<le> cs \<phi>" unfolding cs_def
    by (rule card_image_le[OF finite_SUB])
  finally show "cs (to_tf_formula \<phi>) \<le> cs \<phi>" .
qed

lemma to_tf_mformula: assumes "\<not> eval \<theta> \<phi>"
  shows "\<exists> \<psi> \<in> tf_mformula. (\<forall> \<theta>. eval \<theta> \<phi> = eval \<theta> \<psi>) \<and> vars \<psi> \<subseteq> vars \<phi> \<and> cs \<psi> \<le> cs \<phi>" 
proof (intro bexI[of _ "to_tf_formula \<phi>"] conjI allI eval_to_tf_formula[symmetric] vars_to_tf_formula to_tf_formula)
  from assms have "\<not> eval \<theta> (to_tf_formula \<phi>)" by (simp add: eval_to_tf_formula)
  thus "to_tf_formula \<phi> \<noteq> TRUE" by auto
  show "cs (to_tf_formula \<phi>) \<le> cs \<phi>" by (rule cs_to_tf_formula)
qed 

end