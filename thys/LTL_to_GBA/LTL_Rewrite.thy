section \<open>Rewriting LTL formulas\<close>
(* Author: Alexander Schimpf *)
theory LTL_Rewrite
imports 
  LTL 
begin

context begin interpretation LTL_Syntax .

inductive_set ltln_pure_eventual_frmls :: "'a ltln set"
where
  "\<diamond>\<^sub>n \<phi> \<in> ltln_pure_eventual_frmls"
| "\<lbrakk> \<nu> \<in> ltln_pure_eventual_frmls; \<mu> \<in> ltln_pure_eventual_frmls \<rbrakk>
      \<Longrightarrow> \<nu> and\<^sub>n \<mu> \<in> ltln_pure_eventual_frmls"
| "\<lbrakk> \<nu> \<in> ltln_pure_eventual_frmls; \<mu> \<in> ltln_pure_eventual_frmls \<rbrakk>
      \<Longrightarrow> \<nu> or\<^sub>n \<mu> \<in> ltln_pure_eventual_frmls"
| "\<lbrakk> \<nu> \<in> ltln_pure_eventual_frmls; \<mu> \<in> ltln_pure_eventual_frmls \<rbrakk>
      \<Longrightarrow> \<nu> U\<^sub>n \<mu> \<in> ltln_pure_eventual_frmls"
| "\<lbrakk> \<nu> \<in> ltln_pure_eventual_frmls; \<mu> \<in> ltln_pure_eventual_frmls \<rbrakk>
      \<Longrightarrow> \<nu> V\<^sub>n \<mu> \<in> ltln_pure_eventual_frmls"

theorem ltln_pure_eventual_frmls_equiv:
  assumes "\<psi> \<in> ltln_pure_eventual_frmls"
  shows "\<xi> \<Turnstile>\<^sub>n \<phi> U\<^sub>n \<psi> \<longleftrightarrow> \<xi> \<Turnstile>\<^sub>n \<psi>"
  using assms
proof (induct \<psi> arbitrary:\<xi> \<phi>)
  case 1 
  then show ?case 
    by force
next
  case prems: 2 show ?case using prems(2)[of \<xi> \<phi>] prems(4)[of \<xi> \<phi>]
    by (auto, metis less_nat_zero_code suffix_0)
next
  case prems: 3 show ?case
    using prems(2)[of \<xi> \<phi>] prems(4)[of \<xi> \<phi>] by auto
next
  case prems: (4 \<nu> \<mu>)
    let ?\<psi> = "\<nu> U\<^sub>n \<mu>"
    { assume "\<xi> \<Turnstile>\<^sub>n \<phi> U\<^sub>n ?\<psi>"
      then obtain i where "suffix i \<xi> \<Turnstile>\<^sub>n ?\<psi>" and "\<forall>j<i. suffix j \<xi> \<Turnstile>\<^sub>n \<phi>"
        by auto
      moreover with prems(4)[of "suffix i \<xi>" \<nu>] have "suffix i \<xi> \<Turnstile>\<^sub>n \<mu>" 
        by blast
      ultimately have "\<xi> \<Turnstile>\<^sub>n ?\<psi>" using prems(4)[of \<xi> \<phi>] prems(4)[of \<xi> \<nu>] 
        by auto }
    moreover
    { assume "\<xi> \<Turnstile>\<^sub>n ?\<psi>"
      with prems have "\<xi> \<Turnstile>\<^sub>n \<phi> U\<^sub>n \<mu>" by auto
      then obtain i where "suffix i \<xi> \<Turnstile>\<^sub>n \<mu>" and "\<forall>j<i. suffix j \<xi> \<Turnstile>\<^sub>n \<phi>" 
        by auto
      moreover with prems(4)[of "suffix i \<xi>" \<nu>] have "suffix i \<xi> \<Turnstile>\<^sub>n \<nu> U\<^sub>n \<mu>" 
        by blast
      ultimately have "\<xi> \<Turnstile>\<^sub>n \<phi> U\<^sub>n ?\<psi>" by auto }
    ultimately show ?case by fast
next
  case prems: (5 \<nu> \<mu>)
    let ?\<psi> = "\<nu> V\<^sub>n \<mu>"
    { assume "\<xi> \<Turnstile>\<^sub>n \<phi> U\<^sub>n ?\<psi>"
      then obtain i where 
        V_suf_i: "suffix i \<xi> \<Turnstile>\<^sub>n \<nu> V\<^sub>n \<mu>" 
        and phi_all_less_i: "\<forall>j<i. suffix j \<xi> \<Turnstile>\<^sub>n \<phi>"
        unfolding ltln_Release_alterdef[symmetric] by auto
      then have \<mu>_suf_i: "suffix i \<xi> \<Turnstile>\<^sub>n \<mu>" 
        by (metis ltln_expand_Release ltln_semantics.simps(5))
      have \<mu>_less_i: "\<forall>j<i. suffix j \<xi> \<Turnstile>\<^sub>n \<mu>"
      proof(clarify)
        fix k
        assume "k<i"
        then have "suffix (i-k) (suffix k \<xi>) \<Turnstile>\<^sub>n \<mu>" 
          and "\<forall>j<i-k. suffix j (suffix k \<xi>) \<Turnstile>\<^sub>n \<phi>"
        using V_suf_i phi_all_less_i \<mu>_suf_i by auto
        then show "suffix k \<xi> \<Turnstile>\<^sub>n \<mu>" using prems(4)[of "suffix k \<xi>" \<phi>]
          using ltln_semantics.simps(8) by blast
      qed
      have "\<xi> \<Turnstile>\<^sub>n ?\<psi>"
      proof -
        { fix i'
          { assume "i' < i"
            then have "suffix i' \<xi> \<Turnstile>\<^sub>n \<mu>" using \<mu>_less_i by auto }
          moreover
          { assume "i' \<ge> i"
            then obtain i'' where i'_eq: "i' = i + i''" and "i'\<ge>i''"
              by (metis Nat.diff_le_self le_add_diff_inverse2 add.commute)
            then have "suffix i' \<xi> \<Turnstile>\<^sub>n \<mu> \<or> (\<exists>j<i'. suffix j \<xi> \<Turnstile>\<^sub>n \<nu>)" 
              using V_suf_i by auto }
          ultimately have "suffix i' \<xi> \<Turnstile>\<^sub>n \<mu> \<or> (\<exists>j<i'. suffix j \<xi> \<Turnstile>\<^sub>n \<nu>)" 
            by (metis linorder_not_less) }
        then show ?thesis by auto
      qed }
    moreover
    { assume "\<xi> \<Turnstile>\<^sub>n ?\<psi>"
      then have "suffix 0 \<xi> \<Turnstile>\<^sub>n ?\<psi> \<and> (\<forall>j<0. suffix j \<xi> \<Turnstile>\<^sub>n \<phi>)" by auto
      then have "\<xi> \<Turnstile>\<^sub>n \<phi> U\<^sub>n ?\<psi>" unfolding ltln_semantics.simps by blast }
    ultimately show ?case by fast
qed

corollary ltln_pure_eventual_frmls_equiv_diamond:
  assumes "\<psi> \<in> ltln_pure_eventual_frmls"
  shows "\<xi> \<Turnstile>\<^sub>n \<diamond>\<^sub>n \<psi> \<longleftrightarrow> \<xi> \<Turnstile>\<^sub>n \<psi>"
by (rule ltln_pure_eventual_frmls_equiv[OF assms])


inductive_set ltln_pure_universal_frmls :: "'a ltln set"
where
  "\<box>\<^sub>n \<phi> \<in> ltln_pure_universal_frmls"
| "\<lbrakk> \<nu> \<in> ltln_pure_universal_frmls; \<mu> \<in> ltln_pure_universal_frmls \<rbrakk>
      \<Longrightarrow> \<nu> and\<^sub>n \<mu> \<in> ltln_pure_universal_frmls"
| "\<lbrakk> \<nu> \<in> ltln_pure_universal_frmls; \<mu> \<in> ltln_pure_universal_frmls \<rbrakk>
      \<Longrightarrow> \<nu> or\<^sub>n \<mu> \<in> ltln_pure_universal_frmls"
| "\<lbrakk> \<nu> \<in> ltln_pure_universal_frmls; \<mu> \<in> ltln_pure_universal_frmls \<rbrakk>
      \<Longrightarrow> \<nu> U\<^sub>n \<mu> \<in> ltln_pure_universal_frmls"
| "\<lbrakk> \<nu> \<in> ltln_pure_universal_frmls; \<mu> \<in> ltln_pure_universal_frmls \<rbrakk>
      \<Longrightarrow> \<nu> V\<^sub>n \<mu> \<in> ltln_pure_universal_frmls"

theorem ltln_pure_universal_frmls_equiv:
  assumes "\<psi> \<in> ltln_pure_universal_frmls"
  shows "\<xi> \<Turnstile>\<^sub>n \<phi> V\<^sub>n \<psi> \<longleftrightarrow> \<xi> \<Turnstile>\<^sub>n \<psi>"
  using assms
proof (induct \<psi> arbitrary:\<xi> \<phi>)
  case 1 
  then show ?case by force
next
  case prems: 2 
  show ?case 
    using prems(2)[of \<xi> \<phi>] prems(4)[of \<xi> \<phi>] by auto
next
  case prems: 3 show ?case
    using prems(2)[of \<xi> \<phi>] prems(4)[of \<xi> \<phi>] 
    by (auto, metis less_nat_zero_code suffix_0)
next
  case prems: (4 \<nu> \<mu>)
    let ?\<psi> = "\<nu> U\<^sub>n \<mu>"
    { assume assm: "\<xi> \<Turnstile>\<^sub>n \<phi> V\<^sub>n ?\<psi>"
      { assume "\<xi> \<Turnstile>\<^sub>n \<box>\<^sub>n ?\<psi>"
        then have "suffix 0 \<xi> \<Turnstile>\<^sub>n ?\<psi>" 
          by (metis ltln_semantics.simps(9) ltln_semantics.simps(2))
        then have "\<xi> \<Turnstile>\<^sub>n ?\<psi>" by auto }
      moreover
      { assume "\<not> \<xi> \<Turnstile>\<^sub>n \<box>\<^sub>n ?\<psi>"
        then have  "\<xi> \<Turnstile>\<^sub>n ?\<psi> U\<^sub>n (\<phi> and\<^sub>n ?\<psi>)" 
          using assm ltln_Release_alterdef[of \<xi> \<phi> ?\<psi>] 
          by (metis ltln_semantics.simps(6))
        then obtain i 
          where "suffix i \<xi> \<Turnstile>\<^sub>n \<phi> and\<^sub>n ?\<psi>" and "\<forall>j<i. suffix j \<xi> \<Turnstile>\<^sub>n ?\<psi>" 
          by auto
        then have "\<xi> \<Turnstile>\<^sub>n ?\<psi>" 
          by (cases "i=0") (metis suffix_0 ltln_semantics.simps(5) 
            neq0_conv suffix_0)+ }
      ultimately have "\<xi> \<Turnstile>\<^sub>n ?\<psi>" by fast }
    moreover
    { assume "\<xi> \<Turnstile>\<^sub>n ?\<psi>"
      then obtain i where 
        \<mu>_suf_i: "suffix i \<xi> \<Turnstile>\<^sub>n \<mu>" 
        and \<nu>_less_i: "\<forall>j<i. suffix j \<xi> \<Turnstile>\<^sub>n \<nu>" 
        by auto
      with prems(4)[of "suffix i \<xi>"] \<mu>_suf_i 
      have "suffix i \<xi> \<Turnstile>\<^sub>n \<box>\<^sub>n \<mu> or\<^sub>n (\<mu> U\<^sub>n (\<phi> and\<^sub>n \<mu>))"
        using ltln_Release_alterdef[of "suffix i \<xi>" \<phi> \<mu>] by blast
      moreover
      { assume "suffix i \<xi> \<Turnstile>\<^sub>n \<box>\<^sub>n \<mu>"
        then have \<psi>_suf_i: "suffix i \<xi> \<Turnstile>\<^sub>n \<phi> V\<^sub>n ?\<psi>" 
          by auto (metis ac_simps ltln_expand_Until ltln_semantics.simps)
        from \<nu>_less_i have \<psi>_less_i: "\<forall>j<i. suffix j \<xi> \<Turnstile>\<^sub>n ?\<psi>"
        proof(clarify, goal_cases)
          case (1 j)
            then obtain j' where "i = j + j'" by (metis less_imp_add_positive)
            then have "suffix j' (suffix j \<xi>) \<Turnstile>\<^sub>n \<mu>" 
              and "\<forall>k<j'. suffix k (suffix j \<xi>) \<Turnstile>\<^sub>n \<nu>"
            using \<mu>_suf_i by auto (metis \<nu>_less_i \<open>i = j + j'\<close> 
              add_less_cancel_right add.commute)
            then show ?case by auto
        qed
        have "\<xi> \<Turnstile>\<^sub>n \<phi> V\<^sub>n ?\<psi>"
        proof -
          { fix k
            { assume "k < i"
              with \<psi>_less_i have "suffix k \<xi> \<Turnstile>\<^sub>n ?\<psi>" by auto }
            moreover
            { assume "k \<ge> i"
              then obtain i' where "k = i + i'" by (metis Nat.le_iff_add)
              with \<psi>_suf_i have "suffix k \<xi> \<Turnstile>\<^sub>n ?\<psi> \<or> (\<exists>j<k. suffix j \<xi> \<Turnstile>\<^sub>n \<phi>)" 
                by auto }
            ultimately have "suffix k \<xi> \<Turnstile>\<^sub>n ?\<psi> \<or> (\<exists>j<k. suffix j \<xi> \<Turnstile>\<^sub>n \<phi>)"
              by (metis linorder_not_less) }
          then show ?thesis by auto
        qed }
      moreover
      { assume "suffix i \<xi> \<Turnstile>\<^sub>n \<mu> U\<^sub>n (\<phi> and\<^sub>n \<mu>)"
        then obtain k where "suffix (i+k) \<xi> \<Turnstile>\<^sub>n \<phi>"
                        and "suffix (i+k) \<xi> \<Turnstile>\<^sub>n \<mu>"
                        and "\<forall>j<k. suffix j (suffix i \<xi>) \<Turnstile>\<^sub>n \<mu>" by auto
        then have "\<forall>j\<le>i+k. suffix j \<xi> \<Turnstile>\<^sub>n ?\<psi>"
        proof(clarify, goal_cases)
          case prems: (1 j)
            { assume "j < i"
              then obtain j' where "i = j + j'" by (metis less_imp_add_positive)
              with \<mu>_suf_i \<nu>_less_i have ?case by auto }
            moreover
            { assume "j \<ge> i" 
              then obtain i' where "j = i + i'" by (metis Nat.le_iff_add)
              with prems have ?case 
                by (auto, metis (full_types) add.comm_neutral add_Suc_right
                  le_neq_implies_less less_nat_zero_code) }
            ultimately show ?case by (metis less_or_eq_imp_le linorder_neqE_nat)
        qed
        with \<open>suffix (i+k) \<xi> \<Turnstile>\<^sub>n \<phi>\<close> have "\<xi> \<Turnstile>\<^sub>n \<phi> V\<^sub>n ?\<psi>" 
          by (auto, metis linorder_not_less) }
      ultimately have "\<xi> \<Turnstile>\<^sub>n \<phi> V\<^sub>n ?\<psi>" by auto }
    ultimately show ?case by fast
next
  case prems: (5 \<nu> \<mu>)
    let ?\<psi> = "\<nu> V\<^sub>n \<mu>"
    { assume "\<xi> \<Turnstile>\<^sub>n \<phi> V\<^sub>n ?\<psi>"
      moreover
      { assume "\<xi> \<Turnstile>\<^sub>n \<box>\<^sub>n ?\<psi>"
        then have "\<xi> \<Turnstile>\<^sub>n ?\<psi>" 
          by (metis prems(4) ltln_semantics.simps(2) ltln_semantics.simps(9)) }
      moreover
      { assume "\<xi> \<Turnstile>\<^sub>n ?\<psi> U\<^sub>n (\<phi> and\<^sub>n ?\<psi>)"
        then obtain i where "suffix i \<xi> \<Turnstile>\<^sub>n ?\<psi>" and "\<forall>j<i. suffix j \<xi> \<Turnstile>\<^sub>n ?\<psi>" 
          by auto
        then have "\<xi> \<Turnstile>\<^sub>n ?\<psi>" by (cases "i=0") (auto, metis suffix_0 suffix_suffix) }
      ultimately have "\<xi> \<Turnstile>\<^sub>n ?\<psi>" using ltln_Release_alterdef[of \<xi> \<phi> ?\<psi>] by auto }
    moreover
    { assume "\<xi> \<Turnstile>\<^sub>n ?\<psi>"
      { assume "\<xi> \<Turnstile>\<^sub>n \<box>\<^sub>n \<mu>"
        then have "\<xi> \<Turnstile>\<^sub>n \<phi> V\<^sub>n ?\<psi>" by auto }
      moreover
      { assume assm: "\<not> \<xi> \<Turnstile>\<^sub>n \<box>\<^sub>n \<mu>"
        then have "\<xi> \<Turnstile>\<^sub>n \<mu> U\<^sub>n (\<nu> and\<^sub>n \<mu>)" 
          using ltln_Release_alterdef[of \<xi> \<nu> \<mu>] \<open>\<xi> \<Turnstile>\<^sub>n ?\<psi>\<close> by auto
        then have "\<xi> \<Turnstile>\<^sub>n \<mu>" using \<open>\<xi> \<Turnstile>\<^sub>n ?\<psi>\<close>  by (auto, metis calculation(1) prems(4))
        with prems(4)[of \<xi> \<phi>] have "\<xi> \<Turnstile>\<^sub>n \<phi> V\<^sub>n \<mu>" by auto
        then have "\<xi> \<Turnstile>\<^sub>n \<mu> U\<^sub>n (\<phi> and\<^sub>n \<mu>)" 
          using assm ltln_Release_alterdef[of \<xi> \<phi> \<mu>] by auto
        then obtain i 
          where "suffix i \<xi> \<Turnstile>\<^sub>n \<phi> and\<^sub>n \<mu>" and "\<forall>j<i. suffix j \<xi> \<Turnstile>\<^sub>n \<mu>" 
          by auto
        moreover then have "\<forall>j\<le>i. suffix j \<xi> \<Turnstile>\<^sub>n \<nu> V\<^sub>n \<mu>"
          by (metis \<open>\<xi> \<Turnstile>\<^sub>n \<mu>\<close> assm prems(4))
        ultimately have "\<xi> \<Turnstile>\<^sub>n \<phi> V\<^sub>n ?\<psi>" by (auto, metis linorder_not_le) }
      ultimately have "\<xi> \<Turnstile>\<^sub>n \<phi> V\<^sub>n ?\<psi>" by fast }
    ultimately show ?case by fast
qed


text\<open>Some simple rewrite rules\<close>

fun ltln_rewrite_step :: "'a ltln \<Rightarrow> 'a ltln"
where
  "ltln_rewrite_step (_ U\<^sub>n true\<^sub>n) = true\<^sub>n"
| "ltln_rewrite_step (_ V\<^sub>n false\<^sub>n) = false\<^sub>n"
| "ltln_rewrite_step (true\<^sub>n U\<^sub>n (_ U\<^sub>n \<mu>)) = true\<^sub>n U\<^sub>n \<mu>"
| "ltln_rewrite_step (false\<^sub>n V\<^sub>n (_ V\<^sub>n \<mu>)) = false\<^sub>n V\<^sub>n \<mu>"
| "ltln_rewrite_step \<psi> = (case \<psi> of 
    \<phi> U\<^sub>n \<phi>' \<Rightarrow> 
      if \<phi> = \<phi>' then \<phi> 
      else if \<phi>' \<in> ltln_pure_eventual_frmls then \<phi>' 
      else \<psi>
  | \<phi> V\<^sub>n \<phi>' \<Rightarrow> 
      if \<phi> = \<phi>' then \<phi> 
      else if \<phi>' \<in> ltln_pure_universal_frmls then \<phi>' 
      else \<psi>
  | (\<phi> U\<^sub>n \<mu>) and\<^sub>n (\<nu> U\<^sub>n \<mu>') \<Rightarrow> if \<mu> = \<mu>' then (\<phi> and\<^sub>n \<nu>) U\<^sub>n \<mu> else \<psi>
  | (\<phi> U\<^sub>n \<nu>) or\<^sub>n (\<phi>' U\<^sub>n \<mu>) \<Rightarrow> if \<phi> = \<phi>' then \<phi> U\<^sub>n (\<nu> or\<^sub>n \<mu>) else \<psi>
  | (\<phi> V\<^sub>n \<nu>) and\<^sub>n (\<phi>' V\<^sub>n \<mu>) \<Rightarrow> if \<phi> = \<phi>' then \<phi> V\<^sub>n (\<nu> and\<^sub>n \<mu>) else \<psi>
  | (\<phi> V\<^sub>n \<mu>) or\<^sub>n (\<nu> V\<^sub>n \<mu>') \<Rightarrow> if \<mu> = \<mu>' then (\<phi> or\<^sub>n \<nu>) V\<^sub>n \<mu> else \<psi>
  | _ \<Rightarrow> \<psi>) "

lemma ltln_rewrite_step__size_less:
  assumes "ltln_rewrite_step \<psi> \<noteq> \<psi>"
  shows "size (ltln_rewrite_step \<psi>) < size \<psi>"
proof (cases \<psi>)
  case (LTLnUntil \<nu> \<mu>)
  with assms show ?thesis
    by (cases \<mu>, cases \<nu>) (auto split:ltln.split, 
      metis+, cases \<nu>, auto split:ltln.split, metis+)
next
  case (LTLnRelease \<nu> \<mu>)
  with assms show ?thesis
    by (cases \<mu>, cases \<nu>) (auto split:ltln.split, 
      metis+, cases \<nu>, auto split:ltln.split, metis+)
qed (insert assms, auto split:ltln.split)

lemma ltln_rewrite_step__size_leq:
  "size (ltln_rewrite_step \<psi>) \<le> size \<psi>"
  using ltln_rewrite_step__size_less[of \<psi>] 
  by (cases "ltln_rewrite_step \<psi> = \<psi>") auto


theorem ltln_rewrite_step__equiv:
  "\<xi> \<Turnstile>\<^sub>n ltln_rewrite_step \<psi> \<longleftrightarrow> \<xi> \<Turnstile>\<^sub>n \<psi>"
proof (cases \<psi>)
  case \<psi>: (LTLnAnd \<nu> \<mu>)
  show ?thesis
  proof (cases \<nu>)
    case \<nu>: LTLnUntil
    show ?thesis
    proof (cases \<mu>)
      case \<mu>: LTLnUntil
      with \<psi> \<nu> \<mu> show ?thesis by (auto, metis nat_neq_iff order_less_trans)
    qed (insert \<psi> \<nu>, auto)
  qed (insert \<psi>, auto split:ltln.split)
next
  case \<psi>: (LTLnOr \<nu> \<mu>)
  show ?thesis
  proof (cases \<nu>)
    case \<nu>: LTLnRelease
    show ?thesis
    proof (cases \<mu>)
      case LTLnRelease
      with \<psi> \<nu> show ?thesis by (auto, metis nat_neq_iff order_less_trans)
    qed (insert \<psi> \<nu>, auto)
  qed (insert \<psi>, auto split:ltln.split)
next
  case \<psi>: (LTLnUntil \<nu> \<mu>)
  show ?thesis
  proof(cases "\<mu> \<noteq> true\<^sub>n \<and> \<not> (\<nu> = true\<^sub>n \<and> (\<exists>\<nu>' \<mu>'. \<mu> = \<nu>' U\<^sub>n \<mu>')) \<and> \<nu> \<noteq> \<mu>")
    case True
      with \<psi> have "\<xi> \<Turnstile>\<^sub>n (if \<mu> \<in> ltln_pure_eventual_frmls then \<mu> else \<psi>) \<longleftrightarrow> \<xi> \<Turnstile>\<^sub>n \<psi>"
      using ltln_pure_eventual_frmls_equiv by auto
      with \<psi> True show ?thesis by (cases \<mu>) (cases \<nu>, auto split:ltln.split)+
  next
    case False
    with \<psi> show ?thesis 
      by (cases \<mu>, auto split:ltln.split) (metis less_nat_zero_code neq0_conv
        suffix_0 add.comm_neutral add_0)+
  qed
next
  case \<psi>: (LTLnRelease \<nu> \<mu>)
  show ?thesis
  proof(cases "\<mu> \<noteq> false\<^sub>n \<and> \<not> (\<nu> = false\<^sub>n \<and> (\<exists>\<nu>' \<mu>'. \<mu> = \<nu>' V\<^sub>n \<mu>')) \<and> \<nu> \<noteq> \<mu>")
    case True
      with \<psi> have "\<xi> \<Turnstile>\<^sub>n (if \<mu> \<in> ltln_pure_universal_frmls then \<mu> else \<psi>) \<longleftrightarrow> \<xi> \<Turnstile>\<^sub>n \<psi>"
      using ltln_pure_universal_frmls_equiv by auto
      with \<psi> True show ?thesis by (cases \<mu>) (cases \<nu>, auto split:ltln.split)+
  next
    case False
    with \<psi> show ?thesis 
      by (cases \<mu>, auto split:ltln.split) (metis less_nat_zero_code neq0_conv
        suffix_0 add.comm_neutral add_0)+
  qed
qed (auto split:ltln.split)

function ltln_rewrite_rec
where
  "ltln_rewrite_rec \<psi> = (case ltln_rewrite_step \<psi> of
    \<nu> and\<^sub>n \<mu> \<Rightarrow> (ltln_rewrite_rec \<nu>) and\<^sub>n (ltln_rewrite_rec \<mu>)
  | \<nu> or\<^sub>n \<mu> \<Rightarrow> (ltln_rewrite_rec \<nu>) or\<^sub>n (ltln_rewrite_rec \<mu>)
  | X\<^sub>n \<nu> \<Rightarrow> X\<^sub>n (ltln_rewrite_rec \<nu>)
  | \<nu> U\<^sub>n \<mu> \<Rightarrow> (ltln_rewrite_rec \<nu>) U\<^sub>n (ltln_rewrite_rec \<mu>)
  | \<nu> V\<^sub>n \<mu> \<Rightarrow> (ltln_rewrite_rec \<nu>) V\<^sub>n (ltln_rewrite_rec \<mu>)
  | \<phi> \<Rightarrow> \<phi>)"
by pat_completeness auto
termination proof -
  {
    fix \<psi> \<phi> :: "'a ltln" and thesis
    assume "ltln_rewrite_step \<psi> = \<phi>"
    thm ltln_rewrite_step__size_leq
    moreover assume "\<lbrakk>ltln_rewrite_step \<psi> = \<phi>; 
      size (local.ltln_rewrite_step \<psi>) \<le> size \<psi>\<rbrakk> \<Longrightarrow> thesis"
    ultimately have thesis using ltln_rewrite_step__size_leq[of \<psi>]
      by blast
  } note AUX=this
  show ?thesis
    apply (relation "inv_image less_than size")
    apply simp_all
    apply (erule AUX, simp)+
    done
qed

declare ltln_rewrite_rec.simps [simp del]

lemma ltln_rewrite_rec__size_less:
  assumes "ltln_rewrite_rec \<psi> \<noteq> \<psi>"
  shows "size (ltln_rewrite_rec \<psi>) < size \<psi>"
  using assms
proof (induct "ltln_rewrite_rec \<psi>" arbitrary: \<psi>)
  case LTLnTrue
  then show ?case 
    using ltln_rewrite_step__size_less[of \<psi>] ltln_rewrite_rec.simps[of \<psi>]
    by (cases "ltln_rewrite_step \<psi>") auto
next
  case LTLnFalse
  then show ?case 
    using ltln_rewrite_step__size_less[of \<psi>] ltln_rewrite_rec.simps[of \<psi>]
    by (cases "ltln_rewrite_step \<psi>") auto
next
  case LTLnProp
  then show ?case 
    using ltln_rewrite_step__size_less[of \<psi>] ltln_rewrite_rec.simps[of \<psi>]
    by (cases "ltln_rewrite_step \<psi>") auto
next
  case LTLnNProp
  then show ?case 
    using ltln_rewrite_step__size_less[of \<psi>] ltln_rewrite_rec.simps[of \<psi>]
    by (cases "ltln_rewrite_step \<psi>") auto
next
  case (LTLnAnd \<nu> \<mu>)
  show ?case
  proof (cases "ltln_rewrite_step \<psi>")
    case \<psi>: (LTLnAnd \<nu>' \<mu>')
    show ?thesis
      using LTLnAnd ltln_rewrite_step__size_less[of \<psi>]
      unfolding \<psi> ltln_rewrite_rec.simps[of \<psi>]
      by (cases "\<nu>' and\<^sub>n \<mu>' = \<psi>") fastforce+
  qed (insert LTLnAnd, auto simp add: ltln_rewrite_rec.simps[of \<psi>])
next
  case (LTLnOr \<nu> \<mu>)
  show ?case
  proof (cases "ltln_rewrite_step \<psi>")
    case \<psi>: (LTLnOr \<nu>' \<mu>')
    show ?thesis
      using LTLnOr ltln_rewrite_step__size_less[of \<psi>]
      unfolding \<psi> ltln_rewrite_rec.simps[of \<psi>]
      by (cases "\<nu>' or\<^sub>n \<mu>' = \<psi>") fastforce+
  qed (insert LTLnOr, auto simp add: ltln_rewrite_rec.simps[of \<psi>])
next
  case (LTLnNext \<nu>)
  show ?case
  proof (cases "ltln_rewrite_step \<psi>")
    case \<psi>: (LTLnNext \<nu>')
    show ?thesis
      using LTLnNext ltln_rewrite_step__size_less[of \<psi>]
      unfolding \<psi> ltln_rewrite_rec.simps[of \<psi>]
      by (cases "X\<^sub>n \<nu>' = \<psi>") fastforce+
  qed (insert LTLnNext, auto simp add: ltln_rewrite_rec.simps[of \<psi>])
next
  case (LTLnUntil \<nu> \<mu>)
  show ?case
  proof (cases "ltln_rewrite_step \<psi>")
    case \<psi>: (LTLnUntil \<nu>' \<mu>') 
    show ?thesis
      using LTLnUntil ltln_rewrite_step__size_less[of \<psi>]
      unfolding \<psi> ltln_rewrite_rec.simps[of \<psi>]
      by (cases "\<nu>' U\<^sub>n \<mu>' = \<psi>") fastforce+
  qed (insert LTLnUntil, auto simp add: ltln_rewrite_rec.simps[of \<psi>])
next
  case (LTLnRelease \<nu> \<mu>)
  show ?case
  proof (cases "ltln_rewrite_step \<psi>")
    case \<psi>: (LTLnRelease \<nu>' \<mu>') 
    show ?thesis
      using LTLnRelease ltln_rewrite_step__size_less[of \<psi>]
      unfolding \<psi> ltln_rewrite_rec.simps[of \<psi>]
      by (cases "\<nu>' V\<^sub>n \<mu>' = \<psi>") fastforce+
  qed (insert LTLnRelease, auto simp add: ltln_rewrite_rec.simps[of \<psi>])
qed

lemma ltln_rewrite_rec__size_leq:
  "size (ltln_rewrite_rec \<psi>) \<le> size \<psi>"
using ltln_rewrite_rec__size_less[of \<psi>] by (cases "ltln_rewrite_rec \<psi> = \<psi>") auto


theorem ltln_rewrite_rec__equiv: "\<xi> \<Turnstile>\<^sub>n ltln_rewrite_rec \<psi> \<longleftrightarrow> \<xi> \<Turnstile>\<^sub>n \<psi>"
proof (induct "ltln_rewrite_rec \<psi>" arbitrary: \<xi> \<psi>)
  case LTLnTrue
  then show ?case 
    using ltln_rewrite_step__equiv[of _ \<psi>] ltln_rewrite_rec.simps[of \<psi>]
    by (cases "ltln_rewrite_step \<psi>") auto
next
  case LTLnFalse
  then show ?case 
    using ltln_rewrite_step__equiv[of _ \<psi>] ltln_rewrite_rec.simps[of \<psi>]
    by (cases "ltln_rewrite_step \<psi>") auto
next
  case LTLnProp
  then show ?case
    using ltln_rewrite_step__equiv[of _ \<psi>] ltln_rewrite_rec.simps[of \<psi>]
    by (cases "ltln_rewrite_step \<psi>") auto
next
  case LTLnNProp
  then show ?case 
    using ltln_rewrite_step__equiv[of _ \<psi>] ltln_rewrite_rec.simps[of \<psi>]
    by (cases "ltln_rewrite_step \<psi>") auto
next
  case LTLnAnd
  then show ?case 
    using ltln_rewrite_step__equiv[of _ \<psi>] ltln_rewrite_rec.simps[of \<psi>]
    by (cases "ltln_rewrite_step \<psi>") auto
next
  case LTLnOr
  then show ?case 
    using ltln_rewrite_step__equiv[of _ \<psi>] ltln_rewrite_rec.simps[of \<psi>]
    by (cases "ltln_rewrite_step \<psi>") auto
next
  case LTLnNext
  then show ?case 
    using ltln_rewrite_step__equiv[of _ \<psi>] ltln_rewrite_rec.simps[of \<psi>]
    by (cases "ltln_rewrite_step \<psi>") auto
next
  case LTLnUntil
  then show ?case 
    using ltln_rewrite_step__equiv[of _ \<psi>] ltln_rewrite_rec.simps[of \<psi>]
    by (cases "ltln_rewrite_step \<psi>") auto
next
  case LTLnRelease
  then show ?case 
    using ltln_rewrite_step__equiv[of _ \<psi>] ltln_rewrite_rec.simps[of \<psi>]
    by (cases "ltln_rewrite_step \<psi>") auto
qed


function ltln_rewrite
where
  "ltln_rewrite \<psi> =
    (let \<phi> = ltln_rewrite_rec \<psi>
     in if \<phi> \<noteq> \<psi> then ltln_rewrite \<phi> else \<psi>)"
by pat_completeness auto

termination
proof (relation "inv_image less_than size", goal_cases)
  case 1
  show ?case by auto
next
  case (2 \<psi>)
  then show ?case
    using ltln_rewrite_rec__size_less[of \<psi>] by auto
qed

declare ltln_rewrite.simps [simp del]


lemma ltln_rewrite__size_less:
  assumes "ltln_rewrite \<psi> \<noteq> \<psi>"
  shows "size (ltln_rewrite \<psi>) < size \<psi>"
  using assms
proof (induct \<psi> rule: ltln_rewrite.induct)
  case prems: (1 \<psi>)
  show ?case
  proof (cases "ltln_rewrite_rec \<psi> = \<psi>")
    case True
    then show ?thesis
      using prems(2) unfolding ltln_rewrite.simps[of \<psi>] by auto
  next
    case False
    then have rw_\<psi>_eq: "ltln_rewrite \<psi> = ltln_rewrite (ltln_rewrite_rec \<psi>)" 
      unfolding ltln_rewrite.simps[of \<psi>] by auto
    from prems(1)[OF refl False, folded rw_\<psi>_eq] 
      and ltln_rewrite_rec__size_less[OF False]
    show ?thesis
      by (cases "ltln_rewrite \<psi> = ltln_rewrite_rec \<psi>") auto
  qed
qed

lemma ltln_rewrite__size_leq: "size (ltln_rewrite \<psi>) \<le> size \<psi>"
  using ltln_rewrite__size_less[of \<psi>] by (cases "ltln_rewrite \<psi> = \<psi>") auto


lemma ltln_rewrite__equiv: "\<xi> \<Turnstile>\<^sub>n ltln_rewrite \<psi> \<longleftrightarrow> \<xi> \<Turnstile>\<^sub>n \<psi>"
proof (induct \<psi> rule: ltln_rewrite.induct)
  case prems: (1 \<psi>)
    show ?case
      using prems[OF refl] ltln_rewrite_rec__equiv[of \<xi> \<psi>]
      unfolding ltln_rewrite.simps[of \<psi>]
      by (cases "ltln_rewrite_rec \<psi> = \<psi>") auto
qed


fun ltln_pure_eventual_frmls_impl
where
  "ltln_pure_eventual_frmls_impl (\<diamond>\<^sub>n \<phi>) = True"
| "ltln_pure_eventual_frmls_impl (\<nu> and\<^sub>n \<mu>) 
  = (ltln_pure_eventual_frmls_impl \<nu> \<and> ltln_pure_eventual_frmls_impl \<mu>)"
| "ltln_pure_eventual_frmls_impl (\<nu> or\<^sub>n \<mu>) 
  = (ltln_pure_eventual_frmls_impl \<nu> \<and> ltln_pure_eventual_frmls_impl \<mu>)"
| "ltln_pure_eventual_frmls_impl (\<nu> U\<^sub>n \<mu>) 
  = (ltln_pure_eventual_frmls_impl \<nu> \<and> ltln_pure_eventual_frmls_impl \<mu>)"
| "ltln_pure_eventual_frmls_impl (\<nu> V\<^sub>n \<mu>) 
  = (ltln_pure_eventual_frmls_impl \<nu> \<and> ltln_pure_eventual_frmls_impl \<mu>)"
| "ltln_pure_eventual_frmls_impl _ = False"

lemma ltln_pure_eventual_frmls_unfold[code_unfold]:
  "\<phi> \<in> ltln_pure_eventual_frmls \<longleftrightarrow> ltln_pure_eventual_frmls_impl \<phi>"
  (is "?lhs = ?rhs")
proof
  assume ?lhs
  then show ?rhs
  proof (induct rule: ltln_pure_eventual_frmls.induct)
    case (4 \<nu>)
    then show ?case by (cases "\<nu> = true\<^sub>n") (cases \<nu>, auto)+
  qed auto
next
  assume ?rhs
  then show ?lhs
  proof (induct \<phi>)
    case (LTLnUntil \<nu> \<mu>) 
    then show ?case 
      by (cases "\<nu> = true\<^sub>n") (cases \<nu>, 
        auto intro: ltln_pure_eventual_frmls.intros)+
  qed (auto intro: ltln_pure_eventual_frmls.intros)
qed

fun ltln_pure_universal_frmls_impl
where
  "ltln_pure_universal_frmls_impl (\<box>\<^sub>n \<phi>) = True"
| "ltln_pure_universal_frmls_impl (\<nu> and\<^sub>n \<mu>) 
  = (ltln_pure_universal_frmls_impl \<nu> \<and> ltln_pure_universal_frmls_impl \<mu>)"
| "ltln_pure_universal_frmls_impl (\<nu> or\<^sub>n \<mu>)
  = (ltln_pure_universal_frmls_impl \<nu> \<and> ltln_pure_universal_frmls_impl \<mu>)"
| "ltln_pure_universal_frmls_impl (\<nu> U\<^sub>n \<mu>)
  = (ltln_pure_universal_frmls_impl \<nu> \<and> ltln_pure_universal_frmls_impl \<mu>)"
| "ltln_pure_universal_frmls_impl (\<nu> V\<^sub>n \<mu>)
  = (ltln_pure_universal_frmls_impl \<nu> \<and> ltln_pure_universal_frmls_impl \<mu>)"
| "ltln_pure_universal_frmls_impl _ = False"

lemma ltln_pure_universal_frmls_unfold[code_unfold]:
  "\<phi> \<in> ltln_pure_universal_frmls \<longleftrightarrow> ltln_pure_universal_frmls_impl \<phi>" 
  (is "?lhs = ?rhs")
proof
  assume ?lhs
  then show ?rhs
  proof (induct rule: ltln_pure_universal_frmls.induct)
    case (5 \<nu>)
    then show ?case by (cases "\<nu> = false\<^sub>n") (cases \<nu>, auto)+
  qed auto
next
  assume ?rhs
  then show ?lhs
  proof (induct \<phi>)
    case (LTLnRelease \<nu> \<mu>) 
    then show ?case 
      by (cases "\<nu> = false\<^sub>n") (cases \<nu>, auto intro: ltln_pure_universal_frmls.intros)+
  qed (auto intro: ltln_pure_universal_frmls.intros)
qed

definition
  "ltln_rewrite_step_impl \<psi> \<equiv> case \<psi> of 
    \<nu> U\<^sub>n \<mu> \<Rightarrow> if \<mu> = true\<^sub>n then true\<^sub>n
              else (
                case (\<nu>, \<mu>) of 
                  (true\<^sub>n, _ U\<^sub>n \<mu>') \<Rightarrow> true\<^sub>n U\<^sub>n \<mu>'
                | _ \<Rightarrow> if \<nu> = \<mu> then \<nu> 
                       else if \<mu>\<in>ltln_pure_eventual_frmls then \<mu> 
                       else \<psi>)
  | \<nu> V\<^sub>n \<mu> \<Rightarrow> if \<mu> = false\<^sub>n then false\<^sub>n
              else (
                case (\<nu>, \<mu>) of 
                  (false\<^sub>n, _ V\<^sub>n \<mu>') \<Rightarrow> false\<^sub>n V\<^sub>n \<mu>'
                | _ \<Rightarrow> if \<nu> = \<mu> then \<nu> 
                       else if \<mu>\<in>ltln_pure_universal_frmls then \<mu> 
                       else \<psi>)
  | \<psi>1 and\<^sub>n \<psi>2 \<Rightarrow> ( 
      case (\<psi>1, \<psi>2) of 
        (\<phi> U\<^sub>n \<mu>, \<nu> U\<^sub>n \<mu>') \<Rightarrow> if \<mu> = \<mu>' then (\<phi> and\<^sub>n \<nu>) U\<^sub>n \<mu> else \<psi>
      | (\<phi> V\<^sub>n \<nu>, \<phi>' V\<^sub>n \<mu>) \<Rightarrow> if \<phi> = \<phi>' then \<phi> V\<^sub>n (\<nu> and\<^sub>n \<mu>) else \<psi>
      | _ \<Rightarrow> \<psi>)
  | \<psi>1 or\<^sub>n \<psi>2 \<Rightarrow> (
      case (\<psi>1, \<psi>2) of 
        (\<phi> U\<^sub>n \<nu>, \<phi>' U\<^sub>n \<mu>) \<Rightarrow> if \<phi> = \<phi>' then \<phi> U\<^sub>n (\<nu> or\<^sub>n \<mu>) else \<psi>
      | (\<phi> V\<^sub>n \<mu>, \<nu> V\<^sub>n \<mu>') \<Rightarrow> if \<mu> = \<mu>' then (\<phi> or\<^sub>n \<nu>) V\<^sub>n \<mu> else \<psi>
      | _ \<Rightarrow> \<psi>)
  | _ \<Rightarrow> \<psi>"

lemma ltln_rewrite_step_unfold[code_unfold]: 
  "ltln_rewrite_step = ltln_rewrite_step_impl"
proof -
  { fix \<psi> :: "'a ltln"
    have "ltln_rewrite_step \<psi> = ltln_rewrite_step_impl \<psi>"
    unfolding ltln_rewrite_step_impl_def by (cases \<psi>) (auto split:ltln.split) }
  then show ?thesis by auto
qed

end

end
