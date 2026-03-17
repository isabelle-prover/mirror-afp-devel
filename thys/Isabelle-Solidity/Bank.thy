theory Bank
  imports Solidity_Main
begin

section \<open>Banking Contract\<close>

subsection \<open>Specification\<close>

abbreviation "balances \<equiv> STR ''balances''"
abbreviation "bal \<equiv> STR ''bal''"

contract Bank
  for balances: "SType.TMap (SType.TValue TAddress) (SType.TValue TSint)"

constructor
where
  "\<langle>skip\<rangle>"

cfunction deposit external payable
where
  "balances [\<langle>sender\<rangle>] ::=\<^sub>s balances ~\<^sub>s [\<langle>sender\<rangle>] \<langle>+\<rangle> \<langle>value\<rangle>" ,

cfunction reset
where
  "balances [\<langle>sender\<rangle>] ::=\<^sub>s \<langle>sint\<rangle> 0" ,

cfunction withdraw external
where
  "do {
    bal :: TSint;
    bal [] ::= balances ~\<^sub>s [\<langle>sender\<rangle>];
    icall reset;
    \<langle>transfer\<rangle> \<langle>sender\<rangle> (bal ~ [])
  }"

context bank
begin
  thm constructor_def
  thm deposit_def
  thm withdraw_def
end

subsection \<open>Verifying an Invariant\<close>

abbreviation "SUMM x \<equiv> \<Sum>ad\<in>UNIV. unat (valtype.uint (storage_data.vt (x (Address ad))))"

context Solidity
begin

lemma 1:
    fixes bal
  assumes "SUMM bal \<le> Balances s this"
      and "bal (Address msg_sender) = storage_data.Value (Uint y)"
      and "unat y + unat msg_value < 2^256"
    shows "(\<Sum>ad\<in>UNIV. unat (valtype.uint (storage_data.vt (if ad = msg_sender then storage_data.Value (Uint (y + msg_value)) else bal (Address ad)))))
           \<le> Balances s this + unat msg_value"
proof -
  from sum_addr[of _ msg_sender] have "(\<Sum>ad|ad \<in> UNIV \<and> ad \<noteq> msg_sender. unat (valtype.uint (storage_data.vt (bal (Address ad))))) +
    unat (valtype.uint (storage_data.vt (bal (Address msg_sender)))) + unat msg_value \<le> Balances s this + unat msg_value"
  using assms(1) by simp
  moreover have "unat (valtype.uint (storage_data.vt (storage_data.Value (Uint (y + msg_value))))) \<le> unat (valtype.uint (storage_data.vt (bal (Address msg_sender)))) + unat msg_value"
    using assms(2,3) unat_add_lem[where ?'a =256] by simp
  ultimately show ?thesis using sum_addr[of _ msg_sender] by simp
qed

lemma 21:
    fixes bal bal'
  assumes "SUMM bal \<le> Balances s this"
      and "bal (Address msg_sender) = storage_data.Value (Uint y)"
      and "bal' (Address msg_sender) = storage_data.Value (Uint 0)"
      and "Balances s' this = Balances s this"
      and "\<And>x. x \<noteq> msg_sender \<Longrightarrow> bal' (Address x) = bal (Address x)"
    shows "SUMM bal' \<le> Balances s' this - unat y"
proof -
  from sum_addr[of _ msg_sender] have
    "(\<Sum>ad|ad \<in> UNIV \<and> ad \<noteq> msg_sender. unat (valtype.uint (storage_data.vt (bal (Address ad))))) +
      (unat (valtype.uint (storage_data.vt (bal (Address msg_sender)))) - unat y)
    \<le> Balances s this - unat y"
    using assms(1,2) by simp
  moreover have "unat (valtype.uint (storage_data.vt (storage_data.Value (Uint 0)))) \<le> unat (valtype.uint (storage_data.vt (bal (Address msg_sender)))) + unat msg_value - unat y"
    using assms(2) unat_add_lem[where ?'a =256] by simp
  ultimately show ?thesis using assms sum_addr[of _ msg_sender] by auto
qed

lemma 22:
    fixes bal bal'
  assumes "SUMM bal \<le> Balances s this"
      and "bal (Address msg_sender) = storage_data.Value (Uint y)"
      and "bal' (Address msg_sender) = storage_data.Value (Uint 0)"
      and "Balances s' this = Balances s this"
      and "\<And>x. x \<noteq> msg_sender \<Longrightarrow> bal' (Address x) = bal (Address x)"
    shows "SUMM bal' \<le> Balances s' this"
  using 21[OF assms] by simp

lemma(in Solidity) bal_msg_sender:
  fixes bal
  assumes "\<forall>x. \<exists>y. bal x = storage_data.Value (Uint y)"
  obtains y where "bal (Address msg_sender) = storage_data.Value (Uint y)"
  using assms by auto

text \<open>
  Now we can start verifying the invariant.
  To this end our package provides a keyword invariant which takes a property as parameter and generates proof obligations.
\<close>
end

invariant sum_bal sb where
    "\<forall>x. (fst sb) balances = storage_data.Map x \<longrightarrow> (snd sb) \<ge> SUMM x"
  for "Bank"

abbreviation(in Solidity) reset_post where
"reset_post start_state return_value end_state \<equiv>
  Balances start_state = Balances end_state \<and>
  (\<forall>mp. state.Storage start_state this balances = storage_data.Map mp \<and>
  (\<forall>y. \<exists>si. mp y = storage_data.Value (Uint si))
  \<longrightarrow> (\<exists>mp'. state.Storage end_state this balances = storage_data.Map mp'
    \<and> mp' (Address msg_sender) = storage_data.Value (valtype.Uint 0)
    \<and> (\<forall>x \<noteq> msg_sender. mp' (Address x) = mp (Address x))
    \<and> (\<forall>y. \<exists>si. mp' y = storage_data.Value (Uint si))))"

declare(in bank) sum_balI[wprules del]

verification sum_bal:
  sum_bal
  "K True" "K (K (K True))"
  deposit "K True" "K (K (K True))" and
  withdraw "K True" "K (K (K True))" and
  reset "K True" reset_post
  for "Bank"
proof -
  show "\<And>call.
       (\<And>x h r. effect (call x) h r \<Longrightarrow> vcond x h r) \<Longrightarrow>
       effect (constructor call) s r \<Longrightarrow> post s r sum_bal (K True) (K (K (K True)))"
    unfolding constructor_def
    apply (erule post_exc_true, erule_tac post_wp)
    unfolding  inv_state_def
    by (vcg wprules: sum_balI | auto)+

  show "\<And>call. effect (reset call) s r \<Longrightarrow>
       (\<And>x h r. effect (call x) h r \<Longrightarrow> vcond x h r) \<Longrightarrow> post s r (K True) (K True) reset_post"
    unfolding reset_def
    apply (erule post_exc_true, erule_tac post_wp)
    unfolding inv_state_def
    apply vcg
    by auto

  show "\<And>call.
       (\<And>x h r. effect (call x) h r \<Longrightarrow> vcond x h r) \<Longrightarrow>
       effect (deposit call) s r \<Longrightarrow> inv_state sum_bal s \<Longrightarrow> post s r sum_bal (K True) (K (K (K True)))"
    unfolding deposit_def
    apply (erule post_exc_true, erule_tac post_wp)
    unfolding inv_state_def
    apply vcg
    apply (auto simp add: wpsimps)
    apply (rule bal_msg_sender, assumption)
    apply vcg
    apply (auto simp add: wpsimps intro!: sum_balI 1)
    apply vcg
    apply (auto simp add: wpsimps)
    apply (rule bal_msg_sender, assumption)
    by vcg

  show "\<And>call.
       (\<And>x h r. effect (call x) h r \<Longrightarrow> vcond x h r) \<Longrightarrow>
       effect (withdraw call) s r \<Longrightarrow> inv_state sum_bal s \<Longrightarrow> post s r sum_bal (K True) (K (K (K True)))"
    unfolding withdraw_def
    apply (erule post_exc_true, erule_tac post_wp)
    unfolding inv_state_def icall_def
    apply (case_tac "msg_sender = this")
    apply (vcg)
    apply (rule_tac s = msg_sender in subst,assumption)
    apply (vcg)
    (* Apply precondition for internal method call *)
    apply (subgoal_tac "(\<And>x h r. effect (call x) h r \<Longrightarrow> vcond x h r)")
            apply (rule_tac c=call and x=Reset_m and P'=reset_post in wp_post)
    using vcond(3) apply simp apply blast
    (* End: Apply precondition for internal method call *)
    apply (vcg)
    apply (rule_tac s=msg_sender in subst, assumption)
    apply (vcg)
    apply (auto simp add:wpsimps)
    apply (vcg)
    apply (auto simp add:wpsimps)
    apply (rule bal_msg_sender, assumption)
    apply (vcg)
    apply (rule_tac mp = mp' in sum_balI)
    apply (auto simp add:wpsimps intro: 22)
    apply (vcg)
    apply (rule_tac mp = mpa in sum_balI)
    apply (vcg)
    (* Apply precondition for internal method call *)
    apply (subgoal_tac "(\<And>x h r. effect (call x) h r \<Longrightarrow> vcond x h r)")
    apply (rule_tac c=call and x=Reset_m and P'=reset_post in wp_post)
    using vcond(3) apply simp apply blast
    (* End: Apply precondition for internal method call *)
    apply vcg
    apply (auto simp add:wpsimps)
    apply vcg
    apply (auto simp add:wpsimps)
    apply (rule bal_msg_sender, assumption)
    apply vcg
    apply (rule_tac mp = mp' in sum_balI)
    apply (auto simp add:wpsimps intro: 21)
    apply vcg
    apply (rule_tac mp = mpa in sum_balI)
    apply vcg
  done
qed

context bank_external
begin
  thm sum_bal
  thm vcond_def
end

end