(*
  Title:  Derivations and Maximal Consistent Sets
  Author: Asta Halkjær From
*)

chapter \<open>Derivations\<close>

theory Derivations imports Maximal_Consistent_Sets begin

section \<open>Rearranging Assumptions\<close>

locale Derivations =
  fixes derive :: \<open>'a list \<Rightarrow> 'a \<Rightarrow> bool\<close>
  assumes derive_struct: \<open>\<And>A B p. derive A p \<Longrightarrow> set A \<subseteq> set B \<Longrightarrow> derive B p\<close>
begin

theorem derive_split:
  assumes \<open>set A \<subseteq> set B \<union> X\<close> \<open>derive A p\<close>
  shows \<open>\<exists>C. set C \<subseteq> X \<and> derive (B @ C) p\<close>
  using struct_split[where P=\<open>\<lambda>A. derive A p\<close>] derive_struct assms by blast

corollary derive_split1:
  assumes \<open>set A \<subseteq> {q} \<union> X\<close> \<open>derive A p\<close>
  shows \<open>\<exists>C. set C \<subseteq> X \<and> derive (q # C) p\<close>
  using assms derive_split[where B=\<open>[q]\<close>] by simp

end

section \<open>MCSs and Deriving Falsity\<close>

locale Derivations_MCS = Derivations + MCS_Base +
  fixes fls
  assumes consistent_derive_fls: \<open>\<And>S. consistent S = (\<nexists>S'. set S' \<subseteq> S \<and> derive S' fls)\<close>
begin

theorem MCS_derive_fls:
  assumes \<open>consistent S\<close> \<open>maximal S\<close>
  shows \<open>p \<notin> S \<longleftrightarrow> (\<exists>S'. set S' \<subseteq> S \<and> derive (p # S') fls)\<close>
proof
  assume \<open>p \<notin> S\<close>
  then show \<open>\<exists>S'. set S' \<subseteq> S \<and> derive (p # S') fls\<close>
    using assms derive_split1 consistent_derive_fls unfolding maximal_def by metis
next
  assume \<open>\<exists>S'. set S' \<subseteq> S \<and> derive (p # S') fls\<close>
  then show \<open>p \<notin> S\<close>
    using assms consistent_derive_fls by fastforce
qed

end

section \<open>MCSs and Derivability\<close>

locale Derivations_MCS_Cut = Derivations_MCS +
  assumes derive_assm: \<open>\<And>A p. p \<in> set A \<Longrightarrow> derive A p\<close>
    and derive_cut: \<open>\<And>A B p q. derive A p \<Longrightarrow> derive (p # B) q \<Longrightarrow> derive (A @ B) q\<close>
begin

theorem MCS_derive:
  assumes \<open>consistent S\<close> \<open>maximal S\<close>
  shows \<open>p \<in> S \<longleftrightarrow> (\<exists>S'. set S' \<subseteq> S \<and> derive S' p)\<close>
proof
  assume \<open>p \<in> S\<close>
  then show \<open>\<exists>S'. set S' \<subseteq> S \<and> derive S' p\<close>
    using derive_assm by (metis List.set_insert empty_set empty_subsetI insert_subset singletonI)
next
  assume \<open>\<exists>A. set A \<subseteq> S \<and> derive A p\<close>
  then obtain A where A: \<open>set A \<subseteq> S\<close> \<open>derive A p\<close>
    by blast
  have \<open>consistent ({p} \<union> S)\<close>
    unfolding consistent_derive_fls
  proof safe
    fix B
    assume B: \<open>set B \<subseteq> {p} \<union> S\<close> \<open>derive B fls\<close>
    then obtain C where C: \<open>derive (p # C) fls\<close> \<open>set C \<subseteq> S\<close>
      using derive_split1 by blast
    then have \<open>derive (A @ C) fls\<close>
      using A derive_cut by blast
    then show False
      using A(1) B(1) C assms(1) consistent_derive_fls by simp
  qed
  then show \<open>p \<in> S\<close>
    using assms unfolding maximal_def by auto
qed

end

end
