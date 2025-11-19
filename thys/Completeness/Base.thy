section "Base"

theory Base
imports PermutationLemmas
begin

subsection "Integrate with Isabelle libraries?"

    \<comment> \<open>Misc\<close>

  \<comment> \<open>FIXME added by tjr, forms basis of a lot of proofs of existence of inf sets\<close>
  \<comment> \<open>something like this should be in FiniteSet, asserting nats are not finite\<close>
lemma natset_finite_max: 
  assumes a: "finite A"
  shows "Suc (Max A) \<notin> A"
  using Max_ge Suc_n_not_le_n assms by blast


subsection "Summation"

primrec summation :: "(nat \<Rightarrow> nat) \<Rightarrow> nat \<Rightarrow> nat"
  where
    "summation f 0 = f 0"
  | "summation f (Suc n) = f (Suc n) + summation f n"


subsection "Termination Measure"

primrec sumList     :: "nat list \<Rightarrow> nat"
  where
    "sumList []     = 0"
  | "sumList (x#xs) = x + sumList xs"


subsection "Functions"

abbreviation (input) "preImage \<equiv> vimage"

abbreviation (input) "pre f a \<equiv> f-` {a}"

definition
  equalOn :: "['a set,'a => 'b,'a => 'b] => bool" where
  "equalOn A f g = (\<forall>x\<in>A. f x = g x)"    

lemma preImage_insert: "preImage f (insert a A) = pre f a \<union> preImage f A"
  by auto

lemma equalOn_Un:  "equalOn (A \<union> B) f g = (equalOn A f g \<and> equalOn B f g)"
  by(auto simp add: equalOn_def) 

lemma equalOnD: "equalOn A f g \<Longrightarrow> (\<forall> x \<in> A . f x = g x)"
  by(simp add: equalOn_def)

lemma equalOnI:"(\<forall> x \<in> A . f x = g x) \<Longrightarrow> equalOn A f g"
  by(simp add: equalOn_def)

lemma equalOn_UnD: "equalOn (A Un B) f g ==> equalOn A f g & equalOn B f g"
  by(auto simp: equalOn_def)

lemma inj_inv_singleton[simp]: "\<lbrakk> inj f; f z = y \<rbrakk> \<Longrightarrow> {x. f x = y} = {z}"
  using inj_eq by fastforce

lemma finite_pre[simp]: "inj f \<Longrightarrow> finite (pre f x)"
  by (simp add: finite_vimageI)

declare finite_vimageI [simp]

end
