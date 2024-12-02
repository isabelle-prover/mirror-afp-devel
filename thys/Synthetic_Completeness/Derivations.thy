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
  fixes derive :: \<open>'fm list \<Rightarrow> 'fm \<Rightarrow> bool\<close> (infix \<open>\<turnstile>\<close> 50)
  assumes derive_assm [simp]: \<open>\<And>A p. p \<in> set A \<Longrightarrow> A \<turnstile> p\<close>
    and derive_set: \<open>\<And>A B r. A \<turnstile> r \<Longrightarrow> set A = set B \<Longrightarrow> B \<turnstile> r\<close>
begin

theorem derive_split:
  assumes \<open>set A \<subseteq> set B \<union> X\<close> \<open>A \<turnstile> p\<close>
  shows \<open>\<exists>B' C. set B' = set A \<inter> set B \<and> set C \<subseteq> X \<and> B' @ C \<turnstile> p\<close>
  using assms derive_set split_list[where A=A and B=B] by metis

corollary derive_split1:
  assumes \<open>set A \<subseteq> {q} \<union> X\<close> \<open>A \<turnstile> p\<close> \<open>q \<in> set A\<close>
  shows \<open>\<exists>C. set C \<subseteq> X \<and> q # C \<turnstile> p\<close>
  using assms derive_split[where A=A and X=X and B=\<open>[q]\<close> and p=p] derive_set[where B=\<open>q # _\<close>]
  by auto

end

section \<open>MCSs and Explosion\<close>

locale Derivations_MCS = MCS_Base consistent + Derivations derive
  for consistent :: \<open>'fm set \<Rightarrow> bool\<close>
    and derive :: \<open>'fm list \<Rightarrow> 'fm \<Rightarrow> bool\<close> (infix \<open>\<turnstile>\<close> 50) +
  assumes consistent_underivable: \<open>\<And>S. consistent S \<longleftrightarrow> (\<forall>A. set A \<subseteq> S \<longrightarrow> (\<exists>q. \<not> A \<turnstile> q))\<close>
begin

theorem MCS_explode:
  assumes \<open>consistent S\<close> \<open>maximal S\<close>
  shows \<open>p \<notin> S \<longleftrightarrow> (\<exists>A. set A \<subseteq> S \<and> (\<forall>q. p # A \<turnstile> q))\<close>
proof safe
  assume \<open>p \<notin> S\<close>
  then obtain B where B: \<open>set B \<subseteq> {p} \<union> S\<close> \<open>p \<in> set B\<close> \<open>\<forall>q. B \<turnstile> q\<close>
    using assms unfolding consistent_underivable maximal_def by blast
  moreover have \<open>set (p # removeAll p B) = set B\<close>
    using B(2) by auto
  ultimately have \<open>\<forall>q. p # removeAll p B \<turnstile> q\<close>
    using derive_set by metis
  then show \<open>\<exists>A. set A \<subseteq> S \<and> (\<forall>q. p # A \<turnstile> q)\<close>
    using B(1) by (metis Diff_subset_conv set_removeAll)
next
  fix A
  assume \<open>set A \<subseteq> S\<close> \<open>\<forall>q. p # A \<turnstile> q\<close> \<open>p \<in> S\<close>
  then show False
    using assms unfolding consistent_underivable
    by (metis (no_types, lifting) insert_subsetI list.simps(15))
qed

end

section \<open>MCSs and Derivability\<close>

locale Derivations_Cut_MCS = Derivations_MCS consistent derive
  for consistent :: \<open>'fm set \<Rightarrow> bool\<close>
    and derive :: \<open>'fm list \<Rightarrow> 'fm \<Rightarrow> bool\<close> (infix \<open>\<turnstile>\<close> 50) +
  assumes derive_cut: \<open>\<And>A B p q. A \<turnstile> p \<Longrightarrow> p # B \<turnstile> q \<Longrightarrow> A @ B \<turnstile> q\<close>
begin

theorem MCS_derive:
  assumes \<open>consistent S\<close> \<open>maximal S\<close>
  shows \<open>p \<in> S \<longleftrightarrow> (\<exists>A. set A \<subseteq> S \<and> A \<turnstile> p)\<close>
proof safe
  assume \<open>p \<in> S\<close>
  then show \<open>\<exists>A. set A \<subseteq> S \<and> A \<turnstile> p\<close>
    using derive_assm by (metis List.set_insert empty_set empty_subsetI insert_subset singletonI)
next
  fix A
  assume A: \<open>set A \<subseteq> S\<close> \<open>A \<turnstile> p\<close>

  have bot: \<open>\<forall>A. set A \<subseteq> S \<longrightarrow> (\<exists>q. \<not> A \<turnstile> q)\<close>
    using assms(1) unfolding consistent_underivable by blast

  have \<open>consistent ({p} \<union> S)\<close>
    unfolding consistent_underivable
  proof safe
    fix B
    assume B: \<open>set B \<subseteq> {p} \<union> S\<close>
    show \<open>\<exists>q. \<not> B \<turnstile> q\<close>
    proof (rule ccontr)
      assume *: \<open>\<nexists>q. \<not> B \<turnstile> q\<close>
      then have \<open>\<forall>q. B \<turnstile> q\<close>
        by blast
      show False
      proof (cases \<open>p \<in> set B\<close>)
        case True
        then have \<open>set (p # removeAll p B) = set B\<close>
          by auto
        then have \<open>\<forall>q. p # removeAll p B \<turnstile> q\<close>
          using \<open>\<forall>q. B \<turnstile> q\<close> derive_set by blast
        then have \<open>\<forall>q. A @ removeAll p B \<turnstile> q\<close>
          using A(2) derive_cut by blast
        moreover have \<open>set (A @ removeAll p B) \<subseteq> S\<close>
          using A(1) B by auto
        ultimately show False
          using bot by blast
      next
        case False
        then show False
          using * B bot by auto
      qed
    qed
  qed
  then show \<open>p \<in> S\<close>
    using assms unfolding maximal_def by auto
qed

end

section \<open>Proof Rules\<close>

locale Derivations_Bot = Derivations_Cut_MCS consistent derive
  for consistent :: \<open>'fm set \<Rightarrow> bool\<close>
    and derive :: \<open>'fm list \<Rightarrow> 'fm \<Rightarrow> bool\<close> (infix \<open>\<turnstile>\<close> 50) +
  fixes bot :: 'fm (\<open>\<^bold>\<bottom>\<close>)
  assumes botE: \<open>\<And>A p. A \<turnstile> \<^bold>\<bottom> \<Longrightarrow> A \<turnstile> p\<close>
begin

corollary MCS_botE [elim]:
  assumes \<open>consistent S\<close> \<open>maximal S\<close>
    and \<open>\<^bold>\<bottom> \<in> S\<close>
  shows \<open>p \<in> S\<close>
  using assms botE MCS_derive by blast

corollary MCS_bot [simp]:
  assumes \<open>consistent S\<close> \<open>maximal S\<close>
  shows \<open>\<^bold>\<bottom> \<notin> S\<close>
  using assms botE MCS_derive consistent_underivable by blast

end

locale Derivations_Top = Derivations_Cut_MCS +
  fixes top (\<open>\<^bold>\<top>\<close>)
  assumes topI: \<open>\<And>A. A \<turnstile> \<^bold>\<top>\<close>
begin

corollary MCS_topI [simp]:
  assumes \<open>consistent S\<close> \<open>maximal S\<close>
  shows \<open>\<^bold>\<top> \<in> S\<close>
  using assms topI MCS_derive by (metis empty_set empty_subsetI)

end

locale Derivations_Not = Derivations_Bot consistent derive bot
  for consistent :: \<open>'fm set \<Rightarrow> bool\<close>
    and derive :: \<open>'fm list \<Rightarrow> 'fm \<Rightarrow> bool\<close> (infix \<open>\<turnstile>\<close> 50)
    and bot :: 'fm (\<open>\<^bold>\<bottom>\<close>) +
  fixes not :: \<open>'fm \<Rightarrow> 'fm\<close> (\<open>\<^bold>\<not>\<close>)
  assumes
    notI: \<open>\<And>A p. p # A \<turnstile> \<^bold>\<bottom> \<Longrightarrow> A  \<turnstile> \<^bold>\<not> p\<close> and
    notE: \<open>\<And>A p. A \<turnstile> p \<Longrightarrow> A \<turnstile> \<^bold>\<not> p \<Longrightarrow> A \<turnstile> \<^bold>\<bottom>\<close>
begin

corollary MCS_not_xor:
  assumes \<open>consistent S\<close> \<open>maximal S\<close>
  shows \<open>p \<in> S \<longleftrightarrow> \<^bold>\<not> p \<notin> S\<close>
proof safe
  assume \<open>p \<in> S\<close> \<open>\<^bold>\<not> p \<in> S\<close>
  then have \<open>set [p, \<^bold>\<not> p] \<subseteq> S\<close>
    by simp
  moreover have \<open>[p, \<^bold>\<not> p] \<turnstile> \<^bold>\<bottom>\<close>
    using notE derive_assm by (meson list.set_intros(1) list.set_intros(2))
  ultimately have \<open>\<^bold>\<bottom> \<in> S\<close>
    using assms MCS_derive by blast
  then show False
    using assms MCS_bot by blast
next
  assume *: \<open>\<^bold>\<not> p \<notin> S\<close>
  show \<open>p \<in> S\<close>
  proof (rule ccontr)
    assume \<open>p \<notin> S\<close>
    then obtain A where A: \<open>set A \<subseteq> S\<close> \<open>\<forall>q. p # A \<turnstile> q\<close>
      using assms MCS_explode by blast
    then have \<open>p # A \<turnstile> \<^bold>\<bottom>\<close>
      by fast
    then have \<open>A \<turnstile> \<^bold>\<not> p\<close>
      using notI by blast
    then have \<open>\<^bold>\<not> p \<in> S\<close>
      using A(1) assms MCS_derive by blast
    then show False
      using * by blast
  qed
qed
    
corollary MCS_not_both:
  assumes \<open>consistent S\<close> \<open>maximal S\<close>
  shows \<open>p \<notin> S \<or> \<^bold>\<not> p \<notin> S\<close>
  using assms MCS_not_xor by blast

corollary MCS_not_neither:
  assumes \<open>consistent S\<close> \<open>maximal S\<close>
  shows \<open>p \<in> S \<or> \<^bold>\<not> p \<in> S\<close>
  using assms MCS_not_xor by blast

end

locale Derivations_Con = Derivations_Cut_MCS consistent derive
  for consistent :: \<open>'fm set \<Rightarrow> bool\<close>
    and derive :: \<open>'fm list \<Rightarrow> 'fm \<Rightarrow> bool\<close> (infix \<open>\<turnstile>\<close> 50)  +
  fixes con :: \<open>'fm \<Rightarrow> 'fm \<Rightarrow> 'fm\<close> (\<open>_ \<^bold>\<and> _\<close>)
  assumes
    conI: \<open>\<And>A p q. A \<turnstile> p \<Longrightarrow> A \<turnstile> q \<Longrightarrow> A \<turnstile> (p \<^bold>\<and> q)\<close> and
    conE: \<open>\<And>A p q r. A \<turnstile> (p \<^bold>\<and> q) \<Longrightarrow> p # q # A \<turnstile> r \<Longrightarrow> A \<turnstile> r\<close>
begin

corollary MCS_conI [intro]:
  assumes \<open>consistent S\<close> \<open>maximal S\<close>
    and \<open>p \<in> S\<close> \<open>q \<in> S\<close>
  shows \<open>(p \<^bold>\<and> q) \<in> S\<close>
  using assms MCS_derive derive_assm conI
  by (metis (mono_tags, lifting) insert_subset list.set_intros(1) list.simps(15) set_subset_Cons)

corollary MCS_conE [dest]:
  assumes \<open>consistent S\<close> \<open>maximal S\<close>
    and \<open>(p \<^bold>\<and> q) \<in> S\<close>
  shows \<open>p \<in> S \<and> q \<in> S\<close>
proof -
  have \<open>p # q # A \<turnstile> p\<close> \<open>p # q # A \<turnstile> q\<close> for A
    using derive_assm by simp_all
  then show ?thesis
    using assms MCS_derive conE by blast
qed

corollary MCS_con:
  assumes \<open>consistent S\<close> \<open>maximal S\<close>
  shows \<open>(p \<^bold>\<and> q) \<in> S \<longleftrightarrow> p \<in> S \<and> q \<in> S\<close>
  using assms MCS_conI MCS_conE by blast

end

locale Derivations_Dis = Derivations_Cut_MCS consistent derive
  for consistent :: \<open>'fm set \<Rightarrow> bool\<close>
    and derive :: \<open>'fm list \<Rightarrow> 'fm \<Rightarrow> bool\<close> (infix \<open>\<turnstile>\<close> 50)  +
  fixes dis :: \<open>'fm \<Rightarrow> 'fm \<Rightarrow> 'fm\<close> (\<open>_ \<^bold>\<or> _\<close>)
  assumes
    disI1: \<open>\<And>A p q. A \<turnstile> p \<Longrightarrow> A \<turnstile> (p \<^bold>\<or> q)\<close> and
    disI2: \<open>\<And>A p q. A \<turnstile> q \<Longrightarrow> A \<turnstile> (p \<^bold>\<or> q)\<close> and
    disE: \<open>\<And>A p q r. A \<turnstile> (p \<^bold>\<or> q) \<Longrightarrow> p # A \<turnstile> r \<Longrightarrow> q # A \<turnstile> r \<Longrightarrow> A \<turnstile> r\<close>
begin

corollary MCS_disI1 [intro]:
  assumes \<open>consistent S\<close> \<open>maximal S\<close>
    and \<open>p \<in> S\<close>
  shows \<open>(p \<^bold>\<or> q) \<in> S\<close>
  using assms disI1 MCS_derive by auto

corollary MCS_disI2 [intro]:
  assumes \<open>consistent S\<close> \<open>maximal S\<close>
    and \<open>q \<in> S\<close>
  shows \<open>(p \<^bold>\<or> q) \<in> S\<close>
  using assms disI2 MCS_derive by auto

corollary MCS_disE [elim]:
  assumes \<open>consistent S\<close> \<open>maximal S\<close>
    and \<open>(p \<^bold>\<or> q) \<in> S\<close>
  shows \<open>p \<in> S \<or> q \<in> S\<close>
proof (rule ccontr)
  have bot: \<open>\<forall>A. set A \<subseteq> S \<longrightarrow> (\<exists>q. \<not> A \<turnstile> q)\<close>
    using assms(1) unfolding consistent_underivable by blast

  assume \<open>\<not> (p \<in> S \<or> q \<in> S)\<close>
  then obtain P Q where
    P: \<open>set P \<subseteq> S\<close> \<open>\<forall>r. p # P \<turnstile> r\<close> and
    Q: \<open>set Q \<subseteq> S\<close> \<open>\<forall>r. q # Q \<turnstile> r\<close>
    using assms MCS_explode by auto

  have \<open>p # (p \<^bold>\<or> q) # Q \<turnstile> p\<close>
    by simp
  then have \<open>p # (p \<^bold>\<or> q) # Q @ P \<turnstile> r\<close> for r
    using P derive_cut[of _ p] by (metis append_Cons)
  then have \<open>p # (p \<^bold>\<or> q) # P @ Q \<turnstile> r\<close> for r
    using derive_set[where B=\<open>p # (p \<^bold>\<or> q) # P @ Q\<close>] by fastforce
  moreover have \<open>q # (p \<^bold>\<or> q) # P \<turnstile> q\<close>
    by simp
  then have \<open>q # (p \<^bold>\<or> q) # P @ Q \<turnstile> r\<close> for r
    using Q derive_cut[of _ q] by (metis append_Cons)
  moreover have \<open>(p \<^bold>\<or> q) # P @ Q \<turnstile> (p \<^bold>\<or> q)\<close>
    by simp
  ultimately have \<open>(p \<^bold>\<or> q) # P @ Q \<turnstile> r\<close> for r
    using disE by blast
  moreover have \<open>set ((p \<^bold>\<or> q) # P @ Q) \<subseteq> S\<close>
    using assms(3) P Q by simp
  ultimately show False
    using assms(1) unfolding consistent_underivable by blast
qed

corollary MCS_dis:
  assumes \<open>consistent S\<close> \<open>maximal S\<close>
  shows \<open>(p \<^bold>\<or> q) \<in> S \<longleftrightarrow> p \<in> S \<or> q \<in> S\<close>
  using assms MCS_disI1 MCS_disI2 MCS_disE by blast

end

locale Derivations_Imp = Derivations_Cut_MCS consistent derive
  for consistent :: \<open>'fm set \<Rightarrow> bool\<close>
    and derive :: \<open>'fm list \<Rightarrow> 'fm \<Rightarrow> bool\<close> (infix \<open>\<turnstile>\<close> 50)  +
  fixes imp :: \<open>'fm \<Rightarrow> 'fm \<Rightarrow> 'fm\<close> (\<open>_ \<^bold>\<rightarrow> _\<close>)
  assumes
    impI: \<open>\<And>A p q. p # A \<turnstile> q \<Longrightarrow> A \<turnstile> (p \<^bold>\<rightarrow> q)\<close> and
    impE: \<open>\<And>A p q. A \<turnstile> p \<Longrightarrow> A \<turnstile> (p \<^bold>\<rightarrow> q) \<Longrightarrow> A \<turnstile> q\<close>
begin

corollary MCS_impI [intro]:
  assumes \<open>consistent S\<close> \<open>maximal S\<close>
    and \<open>p \<in> S \<longrightarrow> q \<in> S\<close>
  shows \<open>(p \<^bold>\<rightarrow> q) \<in> S\<close>
    using assms impI derive_assm MCS_derive MCS_explode
    by (metis insert_subset list.simps(15) subsetI)

corollary MCS_impE [dest]:
  assumes \<open>consistent S\<close> \<open>maximal S\<close>
    and \<open>(p \<^bold>\<rightarrow> q) \<in> S\<close> \<open>p \<in> S\<close>
  shows \<open>q \<in> S\<close>
  using assms(3-4) impE MCS_derive[OF assms(1-2)] derive_assm
  by (metis insert_subset list.set_intros(1) list.simps(15) set_subset_Cons)

corollary MCS_imp:
  assumes \<open>consistent S\<close> \<open>maximal S\<close>
  shows \<open>(p \<^bold>\<rightarrow> q) \<in> S \<longleftrightarrow> (p \<in> S \<longrightarrow> q \<in> S)\<close>
  using assms MCS_impI MCS_impE by blast

end

locale Derivations_Exi = MCS_Witness consistent witness params + Derivations_Cut_MCS consistent derive
  for consistent :: \<open>'fm set \<Rightarrow> bool\<close>
    and witness params
    and derive :: \<open>'fm list \<Rightarrow> 'fm \<Rightarrow> bool\<close> (infix \<open>\<turnstile>\<close> 50)  +
  fixes exi :: \<open>'fm \<Rightarrow> 'fm\<close> (\<open>\<^bold>\<exists>\<close>)
    and inst :: \<open>'t \<Rightarrow> 'fm \<Rightarrow> 'fm\<close> (\<open>\<langle>_\<rangle>\<close>)
  assumes
    exi_witness: \<open>\<And>S S' p. MCS S \<Longrightarrow> witness (\<^bold>\<exists>p) S' \<subseteq> S \<Longrightarrow> \<exists>t. \<langle>t\<rangle>p \<in> S\<close> and
    exiI: \<open>\<And>A p t. A \<turnstile> \<langle>t\<rangle>p \<Longrightarrow> A \<turnstile> \<^bold>\<exists>p\<close>
begin

corollary MCS_exiI [intro]:
  assumes \<open>consistent S\<close> \<open>maximal S\<close>
    and \<open>\<langle>t\<rangle>p \<in> S\<close>
  shows \<open>\<^bold>\<exists>p \<in> S\<close>
  using assms MCS_derive exiI by blast

corollary MCS_exiE [dest]:
  assumes \<open>consistent S\<close> \<open>maximal S\<close> \<open>witnessed S\<close>
    and \<open>\<^bold>\<exists>p \<in> S\<close>
  shows \<open>\<exists>t. \<langle>t\<rangle>p \<in> S\<close>
  using assms exi_witness unfolding witnessed_def by blast

corollary MCS_exi:
  assumes \<open>consistent S\<close> \<open>maximal S\<close> \<open>witnessed S\<close>
  shows \<open>\<^bold>\<exists>p \<in> S \<longleftrightarrow> (\<exists>t. \<langle>t\<rangle>p \<in> S)\<close>
  using assms MCS_exiI MCS_exiE by blast

end

locale Derivations_Uni = MCS_Witness consistent witness params + Derivations_Not consistent derive bot not
  for consistent :: \<open>'fm set \<Rightarrow> bool\<close>
    and witness params
    and derive :: \<open>'fm list \<Rightarrow> 'fm \<Rightarrow> bool\<close> (infix \<open>\<turnstile>\<close> 50)
    and bot :: 'fm (\<open>\<^bold>\<bottom>\<close>)
    and not :: \<open>'fm \<Rightarrow> 'fm\<close> (\<open>\<^bold>\<not>\<close>) +
  fixes uni :: \<open>'fm \<Rightarrow> 'fm\<close> (\<open>\<^bold>\<forall>\<close>)
    and inst :: \<open>'t \<Rightarrow> 'fm \<Rightarrow> 'fm\<close> (\<open>\<langle>_\<rangle>\<close>)
  assumes
    uni_witness: \<open>\<And>S S' p. MCS S \<Longrightarrow> witness (\<^bold>\<not> (\<^bold>\<forall>p)) S' \<subseteq> S \<Longrightarrow> \<exists>t. \<^bold>\<not> (\<langle>t\<rangle>p) \<in> S\<close> and
    uniE: \<open>\<And>A p t. A \<turnstile> \<^bold>\<forall>p \<Longrightarrow> A \<turnstile> \<langle>t\<rangle>p\<close>
begin

corollary MCS_uniE [dest]:
  assumes \<open>consistent S\<close> \<open>maximal S\<close>
    and \<open>\<^bold>\<forall>p \<in> S\<close>
  shows \<open>\<langle>t\<rangle>p \<in> S\<close>
  using assms MCS_derive uniE by blast

corollary MCS_uniI [intro]:
  assumes \<open>consistent S\<close> \<open>maximal S\<close> \<open>witnessed S\<close>
    and \<open>\<forall>t. \<langle>t\<rangle>p \<in> S\<close>
  shows \<open>\<^bold>\<forall>p \<in> S\<close>
proof (rule ccontr)
  assume \<open>\<^bold>\<forall>p \<notin> S\<close>
  then have \<open>\<^bold>\<not> (\<^bold>\<forall>p) \<in> S\<close>
    using assms MCS_not_xor by blast
  then have \<open>\<exists>t. \<^bold>\<not> (\<langle>t\<rangle>p) \<in> S\<close>
    using assms uni_witness unfolding witnessed_def by blast
  then show False
    using assms MCS_not_xor by blast
qed

corollary MCS_uni:
  assumes \<open>consistent S\<close> \<open>maximal S\<close> \<open>witnessed S\<close>
  shows \<open>\<^bold>\<forall>p \<in> S \<longleftrightarrow> (\<forall>t. \<langle>t\<rangle>p \<in> S)\<close>
  using assms MCS_uniI MCS_uniE by blast

end

end
