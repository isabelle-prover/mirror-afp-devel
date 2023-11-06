
section "Ramsey's Theorem"

theory Ramsey
  imports Main "HOL-Library.Infinite_Set" "HOL-Library.Ramsey" 

begin

text \<open>Please note: this entire development has been updated and incorporated into 
@{theory "HOL-Library.Ramsey"}  above. Below, some of the results of the original development are 
linked to their current versions elsewhere in the Isabelle libraries. \<close>

subsection "Library lemmas"

lemma infinite_inj_infinite_image: "infinite Z \<Longrightarrow> inj_on f Z \<Longrightarrow> infinite (f ` Z)"
  using finite_imageD by blast

lemma infinite_dom_finite_rng: "[| infinite A; finite (f ` A) |] ==> \<exists>b \<in> f ` A. infinite {a : A. f a = b}"
  by (simp add: pigeonhole_infinite)

lemma infinite_mem: "infinite X \<Longrightarrow> \<exists>x. x \<in> X"
  using finite_insert by fastforce

lemma not_empty_least: "(Y::nat set) \<noteq> {} \<Longrightarrow> \<exists>m. m \<in> Y \<and> (\<forall>m'. m' \<in> Y \<longrightarrow> m \<le> m')"
  by (meson Inf_nat_def1 bdd_below_bot cInf_lower)


subsection "Dependent Choice Variant"
  
lemma dc:
  assumes trans: "trans r"
    and P0: "P x0"
    and Pstep: "\<And>x. P x \<Longrightarrow> \<exists>y. P y \<and> (x, y) \<in> r"
  obtains f :: "nat \<Rightarrow> 'a" where "\<And>n. P (f n)" and "\<And>n m. n < m \<Longrightarrow> (f n, f m) \<in> r"
  by (metis P0 Pstep dependent_choice local.trans)

subsection "Ramsey's theorem"

lemma ramsey: "\<forall>(s::nat) (r::nat) (YY::'a set) (f::'a set \<Rightarrow> nat).
  infinite YY 
  \<and> (\<forall>X. X \<subseteq> YY \<and> finite X \<and> card X = r \<longrightarrow> f X < s)
  \<longrightarrow> (\<exists>Y' t'.
  Y' \<subseteq> YY 
  \<and> infinite Y' 
  \<and> t' < s 
  \<and> (\<forall>X. X \<subseteq> Y' \<and> finite X \<and> card X = r \<longrightarrow> f X = t'))"
  using Ramsey by fastforce

end
