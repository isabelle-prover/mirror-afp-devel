section \<open>Prover\<close>

theory Prover imports "Abstract_Completeness.Abstract_Completeness" Encoding Fair_Stream begin

function eff :: \<open>rule \<Rightarrow> sequent \<Rightarrow> (sequent fset) option\<close> where
  \<open>eff Idle (A, B) = Some {| (A, B) |}\<close>
| \<open>eff (Axiom P ts) (A, B) = (if \<^bold>\<ddagger>P ts [\<in>] A \<and> \<^bold>\<ddagger>P ts [\<in>] B then Some {||} else None)\<close>
| \<open>eff FlsL (A, B) = (if \<^bold>\<bottom> [\<in>] A then Some {||} else None)\<close>
| \<open>eff FlsR (A, B) = (if \<^bold>\<bottom> [\<in>] B then Some {| (A, B [\<div>] \<^bold>\<bottom>) |} else None)\<close>
| \<open>eff (ImpL p q) (A, B) = (if (p \<^bold>\<longrightarrow> q) [\<in>] A then
    Some {| (A [\<div>] (p \<^bold>\<longrightarrow> q), p # B), (q # A [\<div>] (p \<^bold>\<longrightarrow> q), B) |} else None)\<close>
| \<open>eff (ImpR p q) (A, B) = (if (p \<^bold>\<longrightarrow> q) [\<in>] B then
    Some {| (p # A, q # B [\<div>] (p \<^bold>\<longrightarrow> q)) |} else None)\<close>
| \<open>eff (UniL t p) (A, B) = (if \<^bold>\<forall>p [\<in>] A then Some {| (\<langle>t\<rangle>p # A, B) |} else None)\<close>
| \<open>eff (UniR p) (A, B) = (if \<^bold>\<forall>p [\<in>] B then
    Some {| (A, \<langle>\<^bold>#(fresh (A @ B))\<rangle>p # B [\<div>] \<^bold>\<forall>p) |} else None)\<close>
  by pat_completeness auto
termination by (relation \<open>measure size\<close>) standard

definition rules :: \<open>rule stream\<close> where
  \<open>rules \<equiv> fair_stream rule_of_nat\<close>

lemma UNIV_rules: \<open>sset rules = UNIV\<close>
  unfolding rules_def using UNIV_stream surj_rule_of_nat .

interpretation RuleSystem \<open>\<lambda>r s ss. eff r s = Some ss\<close> rules UNIV
  by unfold_locales (auto simp: UNIV_rules intro: exI[of _ Idle])

lemma per_rules':
  assumes \<open>enabled r (A, B)\<close> \<open>\<not> enabled r (A', B')\<close> \<open>eff r' (A, B) = Some ss'\<close> \<open>(A', B') |\<in>| ss'\<close>
  shows \<open>r' = r\<close>
  using assms by (cases r r' rule: rule.exhaust[case_product rule.exhaust])
    (unfold enabled_def, auto split: if_splits)

lemma per_rules: \<open>per r\<close>
  unfolding per_def UNIV_rules using per_rules' by fast

interpretation PersistentRuleSystem \<open>\<lambda>r s ss. eff r s = Some ss\<close> rules UNIV
  using per_rules by unfold_locales

definition \<open>prover \<equiv> mkTree rules\<close>

end
