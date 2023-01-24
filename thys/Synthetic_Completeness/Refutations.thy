(*
  Title:  Refutations and Maximal Consistent Sets
  Author: Asta Halkjær From
*)

chapter \<open>Refutations\<close>

theory Refutations imports Maximal_Consistent_Sets begin

section \<open>Rearranging Refutations\<close>

locale Refutations =
  fixes refute :: \<open>'a list \<Rightarrow> bool\<close>
  assumes refute_struct: \<open>\<And>A B. refute A \<Longrightarrow> set A \<subseteq> set B \<Longrightarrow> refute B\<close>
begin

theorem refute_split:
  assumes \<open>set A \<subseteq> set B \<union> X\<close> \<open>refute A\<close>
  shows \<open>\<exists>C. set C \<subseteq> X \<and> refute (B @ C)\<close>
  using struct_split[where P=refute] refute_struct assms by blast

corollary refute_split1:
  assumes \<open>set A \<subseteq> {q} \<union> X\<close> \<open>refute A\<close>
  shows \<open>\<exists>C. set C \<subseteq> X \<and> refute (q # C)\<close>
  using assms refute_split[where B=\<open>[q]\<close>] by simp

end

section \<open>MCSs and Refutability\<close>

locale Refutations_MCS = Refutations + MCS_Base +
  assumes consistent_refute: \<open>\<And>S. consistent S = (\<nexists>S'. set S' \<subseteq> S \<and> refute S')\<close>
begin

theorem MCS_refute:
  assumes \<open>consistent S\<close> \<open>maximal S\<close>
  shows \<open>p \<notin> S \<longleftrightarrow> (\<exists>S'. set S' \<subseteq> S \<and> refute (p # S'))\<close>
proof
  assume \<open>p \<notin> S\<close>
  then show \<open>\<exists>S'. set S' \<subseteq> S \<and> refute (p # S')\<close>
    using assms refute_split1 consistent_refute unfolding maximal_def by metis
next
  assume \<open>\<exists>S'. set S' \<subseteq> S \<and> refute (p # S')\<close>
  then show \<open>p \<notin> S\<close>
    using assms consistent_refute by fastforce
qed

end

end
