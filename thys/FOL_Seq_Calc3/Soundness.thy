section \<open>Soundness\<close>

theory Soundness imports "Abstract_Soundness.Finite_Proof_Soundness" Prover Semantics begin

lemma eff_sound:
  assumes \<open>eff r (A, B) = Some ss\<close> \<open>\<forall>A B. (A, B) |\<in>| ss \<longrightarrow> (\<forall>(E :: _ \<Rightarrow> 'a). sc (E, F, G) (A, B))\<close>
  shows \<open>sc (E, F, G) (A, B)\<close>
  using assms
proof (induct r \<open>(A, B)\<close> rule: eff.induct)
  case (5 p q)
  then have \<open>sc (E, F, G) (A [\<div>] (p \<^bold>\<longrightarrow> q), p # B)\<close> \<open>sc (E, F, G) (q # A [\<div>] (p \<^bold>\<longrightarrow> q), B)\<close>
    by (metis eff.simps(5) finsertCI option.inject option.simps(3))+
  then show ?case
    using "5.prems"(1) by (force split: if_splits)
next
  case (7 t p)
  then have \<open>sc (E, F, G) (\<langle>t\<rangle>p # A, B)\<close>
    by (metis eff.simps(7) finsert_iff option.inject option.simps(3))
  then show ?case
    using "7.prems"(1) by (fastforce split: if_splits)
next
  case (8 p)
  let ?n = \<open>fresh (A @ B)\<close>
  have A: \<open>\<forall>p [\<in>] A. max_list (vars_fm p) < ?n\<close> and B: \<open>\<forall>p [\<in>] B. max_list (vars_fm p) < ?n\<close>
    unfolding fresh_def using max_list_vars_fms max_list_mono vars_fms_member
    by (metis Un_iff le_imp_less_Suc set_append)+
  from 8 have \<open>sc (E(?n := x), F, G) (A, \<langle>\<^bold>#?n\<rangle>p # B [\<div>] \<^bold>\<forall>p)\<close> for x
    by (metis eff.simps(8) finsert_iff option.inject option.simps(3))
  then have \<open>(\<forall>p [\<in>] A. \<lbrakk>E, F, G\<rbrakk> p) \<longrightarrow>
      (\<forall>x. \<lbrakk>(x \<Zsemi> \<lambda>m. (E(?n := x)) m), F, G\<rbrakk> p) \<or> (\<exists>q [\<in>] B [\<div>] \<^bold>\<forall>p. \<lbrakk>E, F, G\<rbrakk> q)\<close>
    using A B upd_vars_fm by fastforce
  then have \<open>(\<forall>p [\<in>] A. \<lbrakk>E, F, G\<rbrakk> p) \<longrightarrow>
      (\<forall>x. \<lbrakk>((x \<Zsemi> E)(Suc ?n := x)), F, G\<rbrakk> p) \<or> (\<exists>q [\<in>] B [\<div>] \<^bold>\<forall>p. \<lbrakk>E, F, G\<rbrakk> q)\<close>
    unfolding add_upd_commute by blast
  moreover have \<open>max_list (vars_fm p) < ?n\<close>
    using B "8.prems"(1) by (metis eff.simps(8) option.distinct(1) vars_fm.simps(4))
  ultimately have \<open>sc (E, F, G) (A, \<^bold>\<forall>p # (B [\<div>] \<^bold>\<forall>p))\<close>
    by auto
  moreover have \<open>\<^bold>\<forall>p [\<in>] B\<close>
    using "8.prems"(1) by (simp split: if_splits)
  ultimately show ?case
    by (metis (full_types) Diff_iff sc.simps set_ConsD set_removeAll)
qed (fastforce split: if_splits)+

interpretation Soundness \<open>\<lambda>r s ss. eff r s = Some ss\<close> rules UNIV sc
  unfolding Soundness_def using eff_sound by fast

theorem prover_soundness:
  assumes \<open>tfinite t\<close> and \<open>wf t\<close>
  shows \<open>sc (E, F, G) (fst (root t))\<close>
  using assms soundness by fast

end
