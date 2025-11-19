(*
  Title:  Refutations and Maximal Consistent Sets
  Author: Asta Halkjær From
*)

chapter \<open>Refutations\<close>

theory Refutations imports Maximal_Consistent_Sets begin

lemma split_finite_sets:
  assumes \<open>finite A\<close> \<open>finite B\<close>
    and \<open>A \<subseteq> B \<union> S\<close>
  shows \<open>\<exists>B' C. finite C \<and> A = B' \<union> C \<and> B' = A \<inter> B \<and> C \<subseteq> S\<close>
  using assms subset_UnE by auto

lemma split_list:
  assumes \<open>set A \<subseteq> set B \<union> S\<close>
  shows \<open>\<exists>B' C. set (B' @ C) = set A \<and> set B' = set A \<inter> set B \<and> set C \<subseteq> S\<close>
  using assms split_finite_sets[where A=\<open>set A\<close> and B=\<open>set B\<close> and S=S]
  by (metis List.finite_set finite_Un finite_list set_append)

section \<open>Rearranging Refutations\<close>

locale Refutations =
  fixes refute :: \<open>'fm list \<Rightarrow> bool\<close>
  assumes refute_set: \<open>\<And>A B. refute A \<Longrightarrow> set A = set B \<Longrightarrow> refute B\<close>
begin

theorem refute_split:
  assumes \<open>set A \<subseteq> set B \<union> X\<close> \<open>refute A\<close>
  shows \<open>\<exists>B' C. set B' = set A \<inter> set B \<and> set C \<subseteq> X \<and> refute (B' @ C)\<close>
  using assms refute_set split_list[where A=A and B=B] by metis

corollary refute_split1:
  assumes \<open>set A \<subseteq> {q} \<union> X\<close> \<open>refute A\<close> \<open>q \<in> set A\<close>
  shows \<open>\<exists>C. set C \<subseteq> X \<and> refute (q # C)\<close>
  using assms refute_split[where A=A and X=X and B=\<open>[q]\<close>] refute_set by auto

end

section \<open>MCSs and Refutability\<close>

locale Refutations_MCS = MCS_Base + Refutations +
  assumes consistent_refute: \<open>\<And>S. consistent S \<longleftrightarrow> (\<forall>A. set A \<subseteq> S \<longrightarrow> \<not> refute A)\<close>
begin

theorem MCS_refute:
  assumes \<open>consistent S\<close> \<open>maximal S\<close>
  shows \<open>p \<notin> S \<longleftrightarrow> (\<exists>A. set A \<subseteq> S \<and> refute (p # A))\<close>
proof safe
  assume \<open>p \<notin> S\<close>
  then obtain B where B: \<open>set B \<subseteq> {p} \<union> S\<close> \<open>p \<in> set B\<close> \<open>refute B\<close>
    using assms unfolding consistent_refute maximal_def by blast
  moreover have \<open>set (p # removeAll p B) = set B\<close>
    using B(2) by auto
  ultimately have \<open>refute (p # removeAll p B)\<close>
    using refute_set by metis
  then show \<open>\<exists>A. set A \<subseteq> S \<and> refute (p # A)\<close>
    using B(1) by (metis Diff_subset_conv set_removeAll)
next
  fix A
  assume \<open>set A \<subseteq> S\<close> \<open>refute (p # A)\<close> \<open>p \<in> S\<close>
  then show False
    using assms unfolding consistent_refute
    by (metis (no_types, lifting) insert_subsetI list.simps(15))
qed

end

end
