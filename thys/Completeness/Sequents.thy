section "Sequents"

theory Sequents
imports Formula
begin 

type_synonym sequent = "formula list"

definition
  evalS :: "[model,vbl \<Rightarrow> object,formula list] \<Rightarrow> bool" where
  "evalS M phi fs \<equiv> (\<exists>f \<in> set fs . evalF M phi f = True)"

lemma evalS_nil[simp]: "evalS M phi [] = False"
  by(simp add: evalS_def)

lemma evalS_cons[simp]: "evalS M phi (A # \<Gamma>) = (evalF M phi A \<or> evalS M phi \<Gamma>)"
  by(simp add: evalS_def)

lemma evalS_append: "evalS M phi (\<Gamma> @ \<Delta>) = (evalS M phi \<Gamma> \<or> evalS M phi \<Delta>)"
  by(force simp add: evalS_def)

lemma evalS_equiv: "(equalOn (freeVarsFL \<Gamma>) f g) \<Longrightarrow> (evalS M f \<Gamma> = evalS M g \<Gamma>)"
  by (induction \<Gamma>) (auto simp: equalOn_Un evalF_equiv freeVarsFL_cons)


definition
  modelAssigns :: "[model] \<Rightarrow> (vbl \<Rightarrow> object) set" where
  "modelAssigns M = { phi . range phi \<subseteq> objects M }"

lemma modelAssigns_iff [simp]: "f \<in> modelAssigns M \<longleftrightarrow> range f \<subseteq> objects M" 
  by(simp add: modelAssigns_def)
  
definition
  validS :: "formula list \<Rightarrow> bool" where
  "validS fs \<equiv> (\<forall>M. \<forall>phi \<in> modelAssigns M . evalS M phi fs = True)"


subsection "Rules"

type_synonym rule = "sequent * (sequent set)"

definition
  concR :: "rule \<Rightarrow> sequent" where
  "concR = (\<lambda>(conc,prems). conc)"

definition
  premsR :: "rule \<Rightarrow> sequent set" where
  "premsR = (\<lambda>(conc,prems). prems)"

definition
  mapRule :: "(formula \<Rightarrow> formula) \<Rightarrow> rule \<Rightarrow> rule" where
  "mapRule = (\<lambda>f (conc,prems) . (map f conc,(map f) ` prems))"

lemma mapRuleI: "\<lbrakk>A = map f a; B = map f ` b\<rbrakk> \<Longrightarrow> (A, B) = mapRule f (a, b)"
  by(simp add: mapRule_def)
    \<comment> \<open>FIXME tjr would like symmetric\<close>


subsection "Deductions"

(*FIXME. I don't see why plain Pow_mono is rejected.*)
lemmas Powp_mono [mono] = Pow_mono [to_pred pred_subset_eq]

inductive_set
  deductions  :: "rule set \<Rightarrow> formula list set"
  for rules :: "rule set"
  (******
   * Given a set of rules,
   *   1. Given a rule conc/prem(i) in rules,
   *       and the prem(i) are deductions from rules,
   *       then conc is a deduction from rules.
   *   2. can derive permutation of any deducible formula list.
   *      (supposed to be multisets not lists).
   ******)
  where
    inferI: "\<lbrakk>(conc,prems) \<in> rules; prems \<in> Pow(deductions(rules))
           \<rbrakk> \<Longrightarrow> conc \<in> deductions(rules)"
 
lemma mono_deductions: "\<lbrakk>A \<subseteq> B\<rbrakk> \<Longrightarrow> deductions(A) \<subseteq> deductions(B)"
  apply(best intro: deductions.inferI elim: deductions.induct) done
  
(*lemmas deductionsMono = mono_deductions*)

(*
-- "tjr following should be subsetD?"
lemmas deductionSubsetI = mono_deductions[THEN subsetD]
thm deductionSubsetI
*)





subsection "Basic Rule sets"

definition
  "Axioms  = {z. \<exists>p vs.              z = ([FAtom Pos p vs,FAtom Neg p vs],{}) }"

definition
  "Conjs   = {z. \<exists>A0 A1 \<Delta> \<Gamma>. z = (FConj Pos A0 A1#\<Gamma> @ \<Delta>,{A0#\<Gamma>,A1#\<Delta>}) }"

definition
  "Disjs   = {z. \<exists>A0 A1       \<Gamma>. z = (FConj Neg A0 A1#\<Gamma>,{A0#A1#\<Gamma>}) }"

definition
  "Alls    = {z. \<exists>A x         \<Gamma>. z = (FAll Pos A#\<Gamma>,{instanceF x A#\<Gamma>}) \<and> x \<notin> freeVarsFL (FAll Pos A#\<Gamma>) }"

definition
  "Exs     = {z. \<exists>A x         \<Gamma>. z = (FAll Neg A#\<Gamma>,{instanceF x A#\<Gamma>})}"

definition
  "Weaks   = {z. \<exists>A           \<Gamma>. z = (A#\<Gamma>,{\<Gamma>})}"

definition
  "Contrs  = {z. \<exists>A           \<Gamma>. z = (A#\<Gamma>,{A#A#\<Gamma>})}"

definition
  "Cuts    = {z. \<exists>C \<Delta>     \<Gamma>. z = (\<Gamma> @ \<Delta>,{C#\<Gamma>,FNot C#\<Delta>})}"

definition
  "Perms   = {z. \<exists>\<Gamma> \<Delta>     . z = (\<Gamma>,{\<Delta>}) \<and> mset \<Gamma> = mset \<Delta>}"

definition
  "DAxioms = {z. \<exists>p vs.              z = ([FAtom Neg p vs,FAtom Pos p vs],{}) }"


lemma AxiomI: "\<lbrakk>Axioms \<subseteq> A\<rbrakk> \<Longrightarrow> [FAtom Pos p vs,FAtom Neg p vs] \<in> deductions(A)"
  by (auto simp: Axioms_def deductions.simps)

lemma DAxiomsI: "\<lbrakk>DAxioms \<subseteq> A\<rbrakk> \<Longrightarrow> [FAtom Neg p vs,FAtom Pos p vs] \<in> deductions(A)"
  by (auto simp: DAxioms_def deductions.simps)

lemma DisjI: "\<lbrakk>A0#A1#\<Gamma> \<in> deductions(A); Disjs \<subseteq> A\<rbrakk> \<Longrightarrow> (FConj Neg A0 A1#\<Gamma>) \<in> deductions(A)"
  by (force simp: Disjs_def deductions.simps)

lemma ConjI: "\<lbrakk>(A0#\<Gamma>) \<in> deductions(A); (A1#\<Delta>) \<in> deductions(A); Conjs \<subseteq> A\<rbrakk> \<Longrightarrow> FConj Pos A0 A1#\<Gamma> @ \<Delta> \<in> deductions(A)"
  by (force simp: Conjs_def deductions.simps)

lemma AllI: "\<lbrakk>instanceF w A#\<Gamma> \<in> deductions(R); w \<notin> freeVarsFL (FAll Pos A#\<Gamma>); Alls \<subseteq> R\<rbrakk> \<Longrightarrow> (FAll Pos A#\<Gamma>) \<in> deductions(R)"
  by (force simp: Alls_def deductions.simps)

lemma ExI: "\<lbrakk>instanceF w A#\<Gamma> \<in> deductions(R); Exs \<subseteq> R\<rbrakk> \<Longrightarrow> (FAll Neg A#\<Gamma>) \<in> deductions(R)"
  by (force simp: Exs_def deductions.simps)

lemma WeakI: "\<lbrakk>\<Gamma> \<in> deductions R; Weaks \<subseteq> R\<rbrakk> \<Longrightarrow> A#\<Gamma> \<in> deductions(R)"
  by (force simp: Weaks_def deductions.simps)

lemma ContrI: "\<lbrakk>A#A#\<Gamma> \<in> deductions R; Contrs \<subseteq> R\<rbrakk> \<Longrightarrow> A#\<Gamma> \<in> deductions(R)"
  by (force simp: Contrs_def deductions.simps)

lemma PermI: "\<lbrakk>Gamma' \<in> deductions R; mset \<Gamma> = mset Gamma'; Perms \<subseteq> R\<rbrakk> \<Longrightarrow> \<Gamma> \<in> deductions(R)"
  using deductions.inferI [where prems="{Gamma'}"] Perms_def by blast


subsection "Derived Rules"

lemma WeakI1: "\<lbrakk>\<Gamma> \<in> deductions(A); Weaks \<subseteq> A\<rbrakk> \<Longrightarrow> (\<Delta> @ \<Gamma>) \<in> deductions(A)"
  by (induct \<Delta>) (use WeakI in force)+

lemma WeakI2: "\<lbrakk>\<Gamma> \<in> deductions(A); Perms \<subseteq> A; Weaks \<subseteq> A\<rbrakk> \<Longrightarrow> (\<Gamma> @ \<Delta>) \<in> deductions(A)"
  by (metis PermI WeakI1 mset_append union_commute)

lemma SATAxiomI: "\<lbrakk>Axioms \<subseteq> A; Weaks \<subseteq> A; Perms \<subseteq> A; forms = [FAtom Pos n vs,FAtom Neg n vs] @ \<Gamma>\<rbrakk> \<Longrightarrow> forms \<in> deductions(A)"
  using AxiomI WeakI2 by presburger
    
lemma DisjI1: "\<lbrakk>(A1#\<Gamma>) \<in> deductions(A); Disjs \<subseteq> A; Weaks \<subseteq> A\<rbrakk> \<Longrightarrow> FConj Neg A0 A1#\<Gamma> \<in> deductions(A)"
  using DisjI WeakI by presburger

lemma DisjI2: "\<lbrakk>(A0#\<Gamma>) \<in> deductions(A); Disjs \<subseteq> A; Weaks \<subseteq> A; Perms \<subseteq> A\<rbrakk> \<Longrightarrow> FConj Neg A0 A1#\<Gamma> \<in> deductions(A)"
  using PermI [of \<open>A1 # A0 # \<Gamma>\<close>]
  by (metis DisjI WeakI append_Cons mset_append mset_rev rev.simps(2))

    \<comment> \<open>FIXME the following 4 lemmas could all be proved for the standard rule sets using monotonicity as below\<close>
    \<comment> \<open>we keep proofs as in original, but they are slightly ugly, and do not state what is intuitively happening\<close>
lemma perm_tmp4: "Perms \<subseteq> R \<Longrightarrow> A @ (a # list) @ (a # list) \<in> deductions R \<Longrightarrow> (a # a # A) @ list @ list \<in> deductions R"
  by (rule PermI, auto)

lemma weaken_append:
  "Contrs \<subseteq> R \<Longrightarrow> Perms \<subseteq> R \<Longrightarrow> A @ \<Gamma> @ \<Gamma> \<in> deductions(R) \<Longrightarrow> A @ \<Gamma> \<in> deductions(R)"
proof (induction \<Gamma> arbitrary: A)
  case Nil
  then show ?case
    by auto
next
  case (Cons a \<Gamma>)
  then have "(a # a # A) @ \<Gamma> \<in> deductions R"
    using perm_tmp4 by blast
  then have "a # A @ \<Gamma> \<in> deductions R"
    by (metis Cons.prems(1) ContrI append_Cons)
  then show ?case
    using Cons.prems(2) PermI by force
qed

lemma ListWeakI: "Perms \<subseteq> R \<Longrightarrow> Contrs \<subseteq> R \<Longrightarrow> x # \<Gamma> @ \<Gamma> \<in> deductions(R) \<Longrightarrow> x # \<Gamma> \<in> deductions(R)"
  by (metis append.left_neutral append_Cons weaken_append)
    
lemma ConjI': "\<lbrakk>(A0#\<Gamma>) \<in> deductions(A);  (A1#\<Gamma>) \<in> deductions(A); Contrs \<subseteq> A; Conjs \<subseteq> A; Perms \<subseteq> A\<rbrakk> \<Longrightarrow> FConj Pos A0 A1#\<Gamma> \<in> deductions(A)"
  by (metis ConjI ListWeakI)


subsection "Standard Rule Sets For Predicate Calculus"

definition
  PC :: "rule set" where
  "PC = Union {Perms,Axioms,Conjs,Disjs,Alls,Exs,Weaks,Contrs,Cuts}"

definition
  CutFreePC :: "rule set" where
  "CutFreePC = Union {Perms,Axioms,Conjs,Disjs,Alls,Exs,Weaks,Contrs}"

lemma rulesInPCs: "Axioms \<subseteq> PC" "Axioms \<subseteq> CutFreePC"
  "Conjs  \<subseteq> PC" "Conjs  \<subseteq> CutFreePC"
  "Disjs  \<subseteq> PC" "Disjs  \<subseteq> CutFreePC"
  "Alls   \<subseteq> PC" "Alls   \<subseteq> CutFreePC"
  "Exs    \<subseteq> PC" "Exs    \<subseteq> CutFreePC"
  "Weaks  \<subseteq> PC" "Weaks  \<subseteq> CutFreePC"
  "Contrs \<subseteq> PC" "Contrs \<subseteq> CutFreePC"
  "Perms  \<subseteq> PC" "Perms  \<subseteq> CutFreePC"
  "Cuts   \<subseteq> PC"
  "CutFreePC \<subseteq> PC"
  by(auto simp: PC_def CutFreePC_def)


subsection "Monotonicity for CutFreePC deductions"

  \<comment> \<open>these lemmas can be used to replace complicated permutation reasoning above\<close>
  \<comment> \<open>essentially if x is a deduction, and set x subset set y, then y is a deduction\<close>

definition
  inDed :: "formula list \<Rightarrow> bool" where
  "inDed xs \<equiv> xs \<in> deductions CutFreePC"

lemma perm: "mset xs = mset ys \<Longrightarrow> (inDed xs = inDed ys)"
  by (metis PermI inDed_def rulesInPCs(16))

lemma contr: "inDed (x#x#xs) \<Longrightarrow> inDed (x#xs)"
  using ContrI inDed_def rulesInPCs(14) by blast

lemma weak: "inDed xs \<Longrightarrow> inDed (x#xs)"
  by (simp add: WeakI inDed_def rulesInPCs(12))

lemma inDed_mono'[simplified inDed_def]: "set x \<subseteq> set y \<Longrightarrow> inDed x \<Longrightarrow> inDed y"
  using contr perm perm_weak_contr_mono weak by blast

lemma inDed_mono[simplified inDed_def]: "inDed x \<Longrightarrow> set x \<subseteq> set y \<Longrightarrow> inDed y"
  using inDed_def inDed_mono' by auto

end
