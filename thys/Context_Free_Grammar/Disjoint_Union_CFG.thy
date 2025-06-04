(*
Authors: Markus Gschoßmann, Tobias Nipkow
*)

section \<open>Disjoint Union of Sets of Productions\<close>

theory Disjoint_Union_CFG
imports
  "Regular-Sets.Regular_Set"
  Context_Free_Grammar
begin

text \<open>This theory provides lemmas relevant when combining the productions of two grammars
with disjoint sets of nonterminals. In particular that the languages of the nonterminals of
one grammar is unchanged by adding productions involving only disjoint nonterminals.\<close>

lemma derivel_disj_Un_if:
  assumes "Rhs_Nts P \<inter> Lhss P' = {}"
      and "P \<union> P' \<turnstile> u \<Rightarrow>l v"
      and "nts_syms u \<inter> Lhss P' = {}"
    shows "P \<turnstile> u \<Rightarrow>l v \<and> nts_syms v \<inter> Lhss P' = {}"
proof -
  from assms(2) obtain A w u' v' where
        A_w: "(A, w)\<in>(P \<union> P')"
      and u: "u = map Tm u' @ Nt A # v'"
      and v: "v = map Tm u' @ w @ v'"
    unfolding derivel_iff by fast
  then have "(A,w) \<notin> P'" using assms(3) unfolding nts_syms_def Lhss_def by auto
  then have "(A,w) \<in> P" using A_w by blast
  with u v have "(A, w) \<in> P"
      and u: "u = map Tm u' @ Nt A # v'"
      and v: "v = map Tm u' @ w @ v'" by auto
  then have "P \<turnstile> u \<Rightarrow>l v" using derivel.intros by fastforce
  moreover have "nts_syms v \<inter> Lhss P' = {}"
    using u v assms \<open>(A, w) \<in> P\<close> unfolding nts_syms_def Nts_def Rhs_Nts_def by auto
  ultimately show ?thesis by fast
qed

lemma derive_disj_Un_if:
  assumes "Rhs_Nts P \<inter> Lhss P' = {}"
      and "P \<union> P' \<turnstile> u \<Rightarrow> v"
      and "nts_syms u \<inter> Lhss P' = {}"
    shows "P \<turnstile> u \<Rightarrow> v \<and> nts_syms v \<inter> Lhss P' = {}"
proof -
  from assms(2) obtain A w u' v' where
        A_w: "(A, w) \<in> P \<union> P'"
      and u: "u = u' @ Nt A # v'"
      and v: "v = u' @ w @ v'"
    unfolding derive_iff by fast
  then have "(A,w) \<notin> P'" using assms(3) unfolding nts_syms_def Lhss_def by auto
  then have "(A,w) \<in> P" using A_w by blast
  with u v have "(A, w) \<in> P" and u: "u = u' @ Nt A # v'" and v: "v = u' @ w @ v'" by auto
  then have "P \<turnstile> u \<Rightarrow> v" using derive.intros by fastforce
  moreover have "nts_syms v \<inter> Lhss P' = {}"
    using u v assms \<open>(A, w) \<in> P\<close> unfolding nts_syms_def Nts_def Rhs_Nts_def by auto
  ultimately show ?thesis by blast
qed

lemma deriveln_disj_Un_if:
assumes "Rhs_Nts P \<inter> Lhss P' = {}"
shows "\<lbrakk> P \<union> P' \<turnstile> u \<Rightarrow>l(n) v;  nts_syms u \<inter> Lhss P' = {} \<rbrakk> \<Longrightarrow>
  P \<turnstile> u \<Rightarrow>l(n) v \<and> nts_syms v \<inter> Lhss P' = {}"
proof (induction n arbitrary: v)
  case 0
  then show ?case by simp
next
  case (Suc n')
  then obtain v' where split: "P \<union> P' \<turnstile> u \<Rightarrow>l(n') v' \<and> P \<union> P' \<turnstile> v' \<Rightarrow>l v"
    by (meson relpowp_Suc_E)
  with Suc have "P \<turnstile> u \<Rightarrow>l(n') v' \<and> nts_syms v' \<inter> Lhss P' = {}"
    by fast
  with Suc show ?case using assms derivel_disj_Un_if
    by (metis split relpowp_Suc_I)
qed

lemma deriven_disj_Un_if:
assumes "Rhs_Nts P \<inter> Lhss P' = {}"
shows "\<lbrakk> P \<union> P' \<turnstile> u \<Rightarrow>(n) v;  nts_syms u \<inter> Lhss P' = {} \<rbrakk> \<Longrightarrow>
  P \<turnstile> u \<Rightarrow>(n) v \<and> nts_syms v \<inter> Lhss P' = {}"
proof (induction n arbitrary: v)
  case 0
  then show ?case by simp
next
  case (Suc n')
  then obtain v' where split: "P \<union> P' \<turnstile> u \<Rightarrow>(n') v' \<and> P \<union> P' \<turnstile> v' \<Rightarrow> v"
    by (meson relpowp_Suc_E)
  with Suc have "P \<turnstile> u \<Rightarrow>(n') v' \<and> nts_syms v' \<inter> Lhss P' = {}"
    by fast
  with Suc show ?case using assms derive_disj_Un_if
    by (metis split relpowp_Suc_I)
qed

lemma derivel_disj_Un_iff:
  assumes "Rhs_Nts P \<inter> Lhss P' = {}"
      and "nts_syms u \<inter> Lhss P' = {}"
    shows "P \<union> P' \<turnstile> u \<Rightarrow>l v \<longleftrightarrow> P \<turnstile> u \<Rightarrow>l v"
using assms Un_derivel derivel_disj_Un_if by fastforce

lemma derive_disj_Un_iff:
  assumes "Rhs_Nts P \<inter> Lhss P' = {}"
      and "nts_syms u \<inter> Lhss P' = {}"
    shows "P \<union> P' \<turnstile> u \<Rightarrow> v \<longleftrightarrow> P \<turnstile> u \<Rightarrow> v"
using assms Un_derive derive_disj_Un_if by fastforce

lemma deriveln_disj_Un_iff:
  assumes "Rhs_Nts P \<inter> Lhss P' = {}"
      and "nts_syms u \<inter> Lhss P' = {}"
    shows "P \<union> P' \<turnstile> u \<Rightarrow>l(n) v \<longleftrightarrow> P \<turnstile> u \<Rightarrow>l(n) v"
by (metis Un_derivel assms(1,2) deriveln_disj_Un_if relpowp_mono)

lemma deriven_disj_Un_iff:
  assumes "Rhs_Nts P \<inter> Lhss P' = {}"
      and "nts_syms u \<inter> Lhss P' = {}"
    shows "P \<union> P' \<turnstile> u \<Rightarrow>(n) v \<longleftrightarrow> P \<turnstile> u \<Rightarrow>(n) v"
by (metis Un_derive assms(1,2) deriven_disj_Un_if relpowp_mono)

lemma derives_disj_Un_iff:
  assumes "Rhs_Nts P \<inter> Lhss P' = {}"
      and "nts_syms u \<inter> Lhss P' = {}"
    shows "P \<union> P' \<turnstile> u \<Rightarrow>* v \<longleftrightarrow> P \<turnstile> u \<Rightarrow>* v"
by (simp add: deriven_disj_Un_iff[OF assms] rtranclp_power)

lemma Lang_disj_Un1:
  assumes "Rhs_Nts P \<inter> Lhss P' = {}"
  and "S \<notin> Lhss P'"
shows "Lang P S = Lang (P \<union> P') S"
proof -
  from assms(2) have "nts_syms [Nt S] \<inter> Lhss P' = {}" unfolding nts_syms_def Lhss_def by simp
  then show ?thesis unfolding Lang_def
    by (simp add: derives_disj_Un_iff[OF assms(1)])
qed


subsection \<open>Disjoint Concatenation\<close>

lemma Lang_concat_disj:
assumes "Nts P1 \<inter> Nts P2 = {}" "S \<notin> Nts P1 \<union> Nts P2 \<union> {S1,S2}" "S1 \<notin> Nts P2" "S2 \<notin> Nts P1"
shows "Lang ({(S, [Nt S1,Nt S2])} \<union> (P1 \<union> P2)) S = Lang P1 S1 @@ Lang P2 S2"
proof -
  let ?P = "{(S, [Nt S1,Nt S2])} \<union> (P1 \<union> P2)"
  let ?L1 = "Lang P1 S1"
  let ?L2 = "Lang P2 S2"
  have "Lang ?P S \<subseteq> ?L1 @@ ?L2" 
    proof
      fix w
      assume "w \<in> Lang ?P S"
      then have "?P \<turnstile> [Nt S] \<Rightarrow>* map Tm w" using Lang_def by fastforce
      then obtain \<alpha> where "?P \<turnstile> \<alpha> \<Rightarrow>* map Tm w \<and> (S, \<alpha>) \<in> ?P" using derives_start1 by fast
      then have dervs: "?P \<turnstile> [Nt S1, Nt S2] \<Rightarrow>* map Tm w" using assms unfolding Nts_def by auto
      then obtain w1 w2 where "?P \<turnstile> [Nt S1] \<Rightarrow>* map Tm w1" "?P \<turnstile> [Nt S2] \<Rightarrow>* map Tm w2" "w = w1 @ w2"
        using derives_append_decomp[of ?P "[Nt S1]" "[Nt S2]"] by (auto simp: map_eq_append_conv)
      then have "P1 \<union> ({(S, [Nt S1,Nt S2])} \<union> P2) \<turnstile> [Nt S1] \<Rightarrow>* map Tm w1"
        and "P2 \<union> ({(S, [Nt S1,Nt S2])} \<union> P1) \<turnstile> [Nt S2] \<Rightarrow>* map Tm w2" by (simp_all add: Un_commute)
      from derives_disj_Un_iff[THEN iffD1, OF _ _ this(1)]
        derives_disj_Un_iff[THEN iffD1, OF _ _ this(2)] assms
      have "P1 \<turnstile> [Nt S1] \<Rightarrow>* map Tm w1" "P2 \<turnstile> [Nt S2] \<Rightarrow>* map Tm w2"
        by (auto simp: Nts_Lhss_Rhs_Nts)
      then have "w1 \<in> ?L1" "w2 \<in> ?L2" unfolding Lang_def by simp_all
      with \<open>w = _\<close> show "w \<in> ?L1 @@ ?L2" by blast
    qed
    moreover
    have "?L1 @@ ?L2 \<subseteq> Lang ?P S" 
    proof
      fix w
      assume "w \<in> ?L1 @@ ?L2"
      then obtain w1 w2 where w12_src: "w1 \<in> ?L1 \<and> w2 \<in> ?L2 \<and> w = w1 @ w2" using assms by blast
      have "P1 \<subseteq> ?P" "P2 \<subseteq> ?P" by auto
      from w12_src have 1: "P1 \<turnstile> [Nt S1] \<Rightarrow>* map Tm w1" and 2: "P2 \<turnstile> [Nt S2] \<Rightarrow>* map Tm w2"
        using Lang_def by fast+
      have "?P \<turnstile> [Nt S] \<Rightarrow> [Nt S1, Nt S2]" 
        using derive.intros[of "S" "[Nt S1, Nt S2]" ?P "[]"] by auto
      also have "?P \<turnstile> ... \<Rightarrow>* map Tm w1 @ [Nt S2]" using derives_append derives_mono[OF \<open>P1 \<subseteq> ?P\<close>]
        using derives_append[OF derives_mono[OF \<open>P1 \<subseteq> ?P\<close> 1], of "[Nt S2]"] by simp
      also have "?P \<turnstile> \<dots> \<Rightarrow>* map Tm w1 @ map Tm w2"
        using derives_prepend[OF derives_mono[OF \<open>P2 \<subseteq> ?P\<close> 2]] by simp
      ultimately have "?P \<turnstile> [Nt S] \<Rightarrow>* map Tm w" using w12_src by simp
      then show "w \<in> Lang ?P S" unfolding Lang_def by auto
    qed
    ultimately show ?thesis by blast
qed


subsection \<open>Disjoint Union including start fork\<close>

lemma derive_from_isolated_fork:
  "\<lbrakk> A \<notin> Lhss P;  {(A,\<alpha>1),(A,\<alpha>2)} \<union> P \<turnstile> [Nt A] \<Rightarrow> \<beta> \<rbrakk> \<Longrightarrow> \<beta> = \<alpha>1 \<or> \<beta> = \<alpha>2"
unfolding derive_singleton by(auto simp: Lhss_def)

lemma derives_fork_if_derives1:
  assumes "P \<turnstile> [Nt B1] \<Rightarrow>* map Tm w"
  shows "{(A,[Nt B1]), (A,[Nt B2])} \<union> P \<turnstile> [Nt A] \<Rightarrow>* map Tm w" (is "?P \<turnstile> _ \<Rightarrow>* _")
proof -
  have "?P \<turnstile> [Nt A] \<Rightarrow> [Nt B1]" using derive_singleton by auto
  also have "?P \<turnstile> [Nt B1] \<Rightarrow>* map Tm w" using assms
    by (meson derives_mono sup_ge2)
  finally show ?thesis .
qed

lemma derives_disj_if_derives_fork:
  assumes "A \<notin> Nts P \<union> {B1,B2}"
  and "{(A,[Nt B1]), (A,[Nt B2])} \<union> P \<turnstile> [Nt A] \<Rightarrow>* map Tm w" (is "?P \<turnstile> _ \<Rightarrow>* _")
  shows "P \<turnstile> [Nt B1] \<Rightarrow>* map Tm w \<or> P \<turnstile> [Nt B2] \<Rightarrow>* map Tm w"
proof -
  obtain \<beta> where steps: "?P \<turnstile> [Nt A] \<Rightarrow> \<beta>" "?P \<turnstile> \<beta> \<Rightarrow>* map Tm w"
    using converse_rtranclpE[OF assms(2)] by blast
  have "\<beta> = [Nt B1] \<or> \<beta> = [Nt B2]"
    using steps(1) derive_from_isolated_fork[of A P] assms(1) by(auto simp: Nts_Lhss_Rhs_Nts)
  then show ?thesis
    using steps(2) derives_disj_Un_iff[of P "{(A,[Nt B1]), (A,[Nt B2])}" \<beta>] assms
    by(auto simp: Nts_Lhss_Rhs_Nts)
qed

lemma Lang_distrib_eq_Un_Lang2:
  assumes "A \<notin> Nts P \<union> {B1,B2}"
  shows "Lang ({(A,[Nt B1]),(A,[Nt B2])} \<union> P) A = (Lang P B1 \<union> Lang P B2)"
    (is "Lang ?P _ = _" is "?L1 = ?L2")
proof
  show "?L2 \<subseteq> ?L1" unfolding Lang_def
    using derives_fork_if_derives1[of P B1 _ A B2] derives_fork_if_derives1[of P B2 _ A B1]
    by (auto simp add: insert_commute)
next
  show "?L1 \<subseteq> ?L2"
    unfolding Lang_def using derives_disj_if_derives_fork[OF assms] by auto
qed

lemma Lang_disj_Un2:
assumes "Nts P1 \<inter> Nts P2 = {}" "S \<notin> Nts(P1 \<union> P2) \<union> {S1,S2}" "S1 \<notin> Nts P2" "S2 \<notin> Nts P1"
shows "Lang ({(S,[Nt S1]), (S,[Nt S2])} \<union> (P1 \<union> P2)) S = Lang P1 S1 \<union> Lang P2 S2"
proof -
  let ?P = "{(S, [Nt S1]), (S, [Nt S2])} \<union> (P1 \<union> P2)"
  have "Lang ?P S = Lang (P1 \<union> P2) S1 \<union> Lang (P1 \<union> P2) S2"
    using Lang_distrib_eq_Un_Lang2[OF assms(2)] by simp
  moreover have "Lang (P1 \<union> P2) S1 = Lang P1 S1" using assms(1,3)
    apply(subst Lang_disj_Un1[of P1 P2 S1]) unfolding Nts_Lhss_Rhs_Nts by blast+
  moreover  have "Lang (P2 \<union> P1) S2 = Lang P2 S2" using assms(1,4)
    apply(subst Lang_disj_Un1[of P2 P1 S2]) unfolding Nts_Lhss_Rhs_Nts by blast+
  ultimately show ?thesis
    by (metis sup_commute)
qed

end