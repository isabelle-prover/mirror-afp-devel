(*
  Title:  Derivations and Maximal Consistent Sets
  Author: Asta Halkjær From
*)

chapter \<open>Derivations\<close>

theory Derivations imports Maximal_Consistent_Sets begin

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

section \<open>Derivations\<close>

locale Derivations =
  fixes derive :: \<open>'a list \<Rightarrow> 'a \<Rightarrow> bool\<close>
  assumes derive_assm [simp]: \<open>\<And>A p. p \<in> set A \<Longrightarrow> derive A p\<close>
    and derive_set: \<open>\<And>A B r. derive A r \<Longrightarrow> set A = set B \<Longrightarrow> derive B r\<close>
begin

theorem derive_split:
  assumes \<open>set A \<subseteq> set B \<union> X\<close> \<open>derive A p\<close>
  shows \<open>\<exists>B' C. set B' = set A \<inter> set B \<and> set C \<subseteq> X \<and> derive (B' @ C) p\<close>
  using assms derive_set split_list[where A=A and B=B] by metis

corollary derive_split1:
  assumes \<open>set A \<subseteq> {q} \<union> X\<close> \<open>derive A p\<close> \<open>q \<in> set A\<close>
  shows \<open>\<exists>C. set C \<subseteq> X \<and> derive (q # C) p\<close>
  using assms derive_split[where A=A and X=X and B=\<open>[q]\<close> and p=p] derive_set by auto

end

section \<open>MCSs and Explosion\<close>

locale Derivations_MCS = Derivations + MCS_Base +
  fixes bot
  assumes consistent_underivable: \<open>\<And>S. consistent S \<longleftrightarrow> (\<forall>A. set A \<subseteq> S \<longrightarrow> \<not> derive A bot)\<close>
begin

theorem MCS_explode:
  assumes \<open>consistent S\<close> \<open>maximal S\<close>
  shows \<open>p \<notin> S \<longleftrightarrow> (\<exists>A. set A \<subseteq> S \<and> derive (p # A) bot)\<close>
proof -
  have \<open>p \<notin> S \<longleftrightarrow> (\<exists>A. set A \<subseteq> {p} \<union> S \<and> p \<in> set A \<and> (\<exists>B. set B \<subseteq> set A \<and> derive B bot))\<close>
    using MCS_inconsistent[OF assms] unfolding consistent_underivable
    by (metis List.finite_set finite_list)
  moreover have \<open>\<forall>B. set B \<subseteq> {p} \<union> S \<longrightarrow> derive B bot \<longrightarrow> p \<in> set B\<close>
    using assms unfolding consistent_underivable by blast
  then have \<open>\<forall>B. set B \<subseteq> {p} \<union> S \<longrightarrow> derive B bot \<longrightarrow> (\<exists>B'. set B' \<subseteq> S \<and> derive (p # B') bot)\<close>
    using derive_split1 by blast
  ultimately show \<open>p \<notin> S \<longleftrightarrow> (\<exists>A. set A \<subseteq> S \<and> derive (p # A) bot)\<close>
    using assms(1) consistent_underivable by auto
qed

end

section \<open>MCSs and Derivability\<close>

locale Derivations_Cut_MCS = Derivations_MCS +
  assumes derive_cut: \<open>\<And>A B p. derive A p \<Longrightarrow> derive (p # B) bot \<Longrightarrow> derive (A @ B) bot\<close>
begin

theorem MCS_derive:
  assumes \<open>consistent S\<close> \<open>maximal S\<close>
  shows \<open>p \<in> S \<longleftrightarrow> (\<exists>A. set A \<subseteq> S \<and> derive A p)\<close>
proof safe
  assume \<open>p \<in> S\<close>
  then show \<open>\<exists>S'. set S' \<subseteq> S \<and> derive S' p\<close>
    using derive_assm by (metis List.set_insert empty_set empty_subsetI insert_subset singletonI)
next
  fix A
  assume A: \<open>set A \<subseteq> S\<close> \<open>derive A p\<close>

  have bot: \<open>\<forall>A. set A \<subseteq> S \<longrightarrow> \<not> derive A bot\<close>
    using assms(1) unfolding consistent_underivable by blast

  have \<open>consistent ({p} \<union> S)\<close>
    unfolding consistent_underivable
  proof safe
    fix B
    assume \<open>set B \<subseteq> {p} \<union> S\<close> \<open>derive B bot\<close>
    then obtain B' where B': \<open>set B' \<subseteq> S\<close> \<open>derive (p # B') bot\<close>
      using bot derive_split1 by (metis insert_is_Un subset_insert)
    then have \<open>derive (A @ B') bot\<close>
      using A derive_cut by blast
    then show False
      using A(1) B'(1) bot by simp
  qed
  then show \<open>p \<in> S\<close>
    using assms unfolding maximal_def by auto
qed

end

locale Derivations_Bot = Derivations_Cut_MCS +
  assumes botE: \<open>\<And>A r. derive A bot \<Longrightarrow> derive A r\<close>
begin

corollary MCS_botE [simp]:
  assumes \<open>consistent S\<close> \<open>maximal S\<close>
  shows \<open>bot \<notin> S\<close>
  using assms botE MCS_derive consistent_underivable by blast

end

locale Derivations_Top = Derivations_Cut_MCS +
  fixes top
  assumes topI: \<open>\<And>A. derive A top\<close>
begin

corollary MCS_topI [simp]:
  assumes \<open>consistent S\<close> \<open>maximal S\<close>
  shows \<open>top \<in> S\<close>
  using assms topI MCS_derive by (metis empty_set empty_subsetI)

end

locale Derivations_Not = Derivations_Bot +
  fixes not :: \<open>'a \<Rightarrow> 'a\<close>
  assumes
    notI: \<open>\<And>A p. derive (p # A) bot \<Longrightarrow> derive A (not p)\<close> and
    notE: \<open>\<And>A p. derive A p \<Longrightarrow> derive A (not p) \<Longrightarrow> derive A bot\<close>
begin

corollary MCS_not_both:
  assumes \<open>consistent S\<close> \<open>maximal S\<close>
  shows \<open>p \<notin> S \<or> not p \<notin> S\<close>
  using assms notE
  by (metis MCS_derive MCS_explode derive_assm insert_subset list.simps(15) set_subset_Cons)

corollary MCS_not_neither:
  assumes \<open>consistent S\<close> \<open>maximal S\<close>
  shows \<open>p \<in> S \<or> not p \<in> S\<close>
  using assms notI by (meson MCS_explode MCS_derive derive_assm)

corollary MCS_not_xor:
  assumes \<open>consistent S\<close> \<open>maximal S\<close>
  shows \<open>p \<in> S \<longleftrightarrow> not p \<notin> S\<close>
  using assms MCS_not_both MCS_not_neither by blast

end

locale Derivations_Con = Derivations_Cut_MCS +
  fixes con :: \<open>'a \<Rightarrow> 'a \<Rightarrow> 'a\<close>
  assumes
    conI: \<open>\<And>A p q. derive A p \<Longrightarrow> derive A q \<Longrightarrow> derive A (con p q)\<close> and
    conE: \<open>\<And>A p q r. derive A (con p q) \<Longrightarrow> derive (p # q # A) r \<Longrightarrow> derive A r\<close>
begin

corollary MCS_conI [intro]:
  assumes \<open>consistent S\<close> \<open>maximal S\<close>
    and \<open>p \<in> S\<close> \<open>q \<in> S\<close>
  shows \<open>con p q \<in> S\<close>
  using assms MCS_derive derive_assm conI
  by (metis (mono_tags, lifting) insert_subset list.set_intros(1) list.simps(15) set_subset_Cons)

corollary MCS_conE [elim]:
  assumes \<open>consistent S\<close> \<open>maximal S\<close>
    and \<open>con p q \<in> S\<close>
  shows \<open>p \<in> S \<and> q \<in> S\<close>
proof -
  have \<open>derive (p # q # A) p\<close> \<open>derive (p # q # A) q\<close> for A
    using derive_assm by simp_all
  then show ?thesis
    using assms MCS_derive conE by blast
qed

end

locale Derivations_Dis = Derivations_Cut_MCS +
  fixes dis :: \<open>'a \<Rightarrow> 'a \<Rightarrow> 'a\<close>
  assumes
    disI1: \<open>\<And>A p q. derive A p \<Longrightarrow> derive A (dis p q)\<close> and
    disI2: \<open>\<And>A p q. derive A q \<Longrightarrow> derive A (dis p q)\<close> and
    disE: \<open>\<And>A p q r. derive A (dis p q) \<Longrightarrow> derive (p # A) r \<Longrightarrow> derive (q # A) r \<Longrightarrow> derive A r\<close>
begin

corollary MCS_disI1 [intro]:
  assumes \<open>consistent S\<close> \<open>maximal S\<close>
    and \<open>p \<in> S\<close>
  shows \<open>dis p q \<in> S\<close>
  using assms disI1 MCS_derive by auto

corollary MCS_disI2 [intro]:
  assumes \<open>consistent S\<close> \<open>maximal S\<close>
    and \<open>q \<in> S\<close>
  shows \<open>dis p q \<in> S\<close>
  using assms disI2 MCS_derive by auto

corollary MCS_disE [elim]:
  assumes \<open>consistent S\<close> \<open>maximal S\<close>
    and \<open>dis p q \<in> S\<close>
  shows \<open>p \<in> S \<or> q \<in> S\<close>
proof (rule ccontr)
  have bot: \<open>\<forall>A. set A \<subseteq> S \<longrightarrow> \<not> derive A bot\<close>
    using assms(1) unfolding consistent_underivable by blast

  assume \<open>\<not> (p \<in> S \<or> q \<in> S)\<close>
  then obtain P Q where
    P: \<open>set P \<subseteq> S\<close> \<open>derive (p # P) bot\<close> and
    Q: \<open>set Q \<subseteq> S\<close> \<open>derive (q # Q) bot\<close>
    using assms MCS_explode by auto

  have \<open>derive (p # dis p q # Q) p\<close>
    by simp
  then have \<open>derive (p # dis p q # Q @ P) bot\<close>
    using P derive_cut[of _ p] by fastforce
  then have \<open>derive (p # dis p q # P @ Q) bot\<close>
    using derive_set[where B=\<open>p # dis p q # P @ Q\<close>] by fastforce
  moreover have \<open>derive (q # dis p q # P) q\<close>
    by simp
  then have \<open>derive (q # dis p q # P @ Q) bot\<close>
    using Q derive_cut[of _ q] by fastforce
  moreover have \<open>derive (dis p q # P @ Q) (dis p q)\<close>
    by simp
  ultimately have \<open>derive (dis p q # P @ Q) bot\<close>
    using disE by blast
  moreover have \<open>set (dis p q # P @ Q) \<subseteq> S\<close>
    using assms(3) P Q by simp
  ultimately show False
    using assms(1) unfolding consistent_underivable by blast
qed

end

locale Derivations_Imp = Derivations_Bot +
  fixes imp :: \<open>'a \<Rightarrow> 'a \<Rightarrow> 'a\<close>
  assumes
    impI: \<open>\<And>A p q. derive (p # A) q \<Longrightarrow> derive A (imp p q)\<close> and
    impE: \<open>\<And>A p q. derive A p \<Longrightarrow> derive A (imp p q) \<Longrightarrow> derive A q\<close>
begin

corollary MCS_impI [intro]:
  assumes \<open>consistent S\<close> \<open>maximal S\<close>
    and \<open>p \<in> S \<longrightarrow> q \<in> S\<close>
  shows \<open>imp p q \<in> S\<close>
proof (cases \<open>p \<in> S\<close>)
  case True
  then show ?thesis
    using impI impE MCS_derive[OF assms(1-2)] derive_assm assms(3)
    by (meson list.set_intros(1) list.set_intros(2))
next
  case False
  then show ?thesis
    using assms(3) impI botE MCS_derive[OF assms(1-2)] MCS_explode[OF assms(1-2)]
    by metis
qed

corollary MCS_impE [elim]:
  assumes \<open>consistent S\<close> \<open>maximal S\<close>
    and \<open>imp p q \<in> S\<close> \<open>p \<in> S\<close>
  shows \<open>q \<in> S\<close>
  using assms(3-4) impE MCS_derive[OF assms(1-2)] derive_assm
  by (metis insert_subset list.set_intros(1) list.simps(15) set_subset_Cons)

end

sublocale Derivations_Imp \<subseteq> Derivations_Not derive consistent bot \<open>\<lambda>p. imp p bot\<close>
proof
  show \<open>\<And>A p. derive (p # A) bot \<Longrightarrow> derive A (imp p bot)\<close>
    using impI by blast
  show \<open>\<And>A p. derive A p \<Longrightarrow> derive A (imp p bot) \<Longrightarrow> derive A bot\<close>
    using impE by blast
qed

end
