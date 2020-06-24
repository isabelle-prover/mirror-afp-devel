section \<open>Library additions\<close>

theory Nash_Extras
  imports "HOL-Library.Ramsey" "HOL-Library.Countable_Set"

begin

lemma disjoint_iff: "A \<inter> B = {} \<longleftrightarrow> (\<forall>x. x\<in>A \<longrightarrow> x \<notin> B)"
  by auto

definition less_sets :: "['a::order set, 'a::order set] \<Rightarrow> bool" where
  "less_sets A B \<equiv> \<forall>x\<in>A. \<forall>y\<in>B. x < y"

lemma less_setsD: "\<lbrakk>less_sets A B; a \<in> A; b \<in> B\<rbrakk> \<Longrightarrow> a < b"
  by (auto simp: less_sets_def)

lemma less_sets_irrefl [simp]: "less_sets A A \<longleftrightarrow> A = {}"
  by (auto simp: less_sets_def)

lemma less_sets_trans: "\<lbrakk>less_sets A B; less_sets B C; B \<noteq> {}\<rbrakk> \<Longrightarrow> less_sets A C"
  unfolding less_sets_def using less_trans by blast

lemma less_sets_weaken1: "\<lbrakk>less_sets A' B; A \<subseteq> A'\<rbrakk> \<Longrightarrow> less_sets A B"
  by (auto simp: less_sets_def)

lemma less_sets_weaken2: "\<lbrakk>less_sets A B'; B \<subseteq> B'\<rbrakk> \<Longrightarrow> less_sets A B"
  by (auto simp: less_sets_def)

lemma less_sets_imp_disjnt: "less_sets A B \<Longrightarrow> disjnt A B"
  by (auto simp: less_sets_def disjnt_def)

lemma less_sets_UN1: "less_sets (\<Union>\<A>) B \<longleftrightarrow> (\<forall>A\<in>\<A>. less_sets A B)"
  by (auto simp: less_sets_def)

lemma less_sets_UN2: "less_sets A (\<Union> \<B>) \<longleftrightarrow> (\<forall>B\<in>\<B>. less_sets A B)"
  by (auto simp: less_sets_def)

lemma Sup_nat_less_sets_singleton:
  fixes n::nat
  assumes "Sup T < n" "finite T"
  shows "less_sets T {n}"
  using assms Max_less_iff
  by (auto simp: Sup_nat_def less_sets_def split: if_split_asm)
  
end



