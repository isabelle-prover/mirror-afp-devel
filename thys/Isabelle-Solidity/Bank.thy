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

abbreviation
  "SUMM x \<equiv>
    \<Sum>ad\<in>UNIV. unat (valtype.uint (storage_data.vt (storage_data.mp (x balances) (Address ad))))"

context Solidity
begin

lemma sum_leq_value:
    fixes bal mp
  assumes "(\<Sum>ad\<in>UNIV. unat (valtype.uint (storage_data.vt (mp (Address ad))))) \<le> Balances s this"
      and "mp (Address msg_sender) = storage_data.Value (Uint y)"
      and "unat y + unat msg_value < 2^256"
    shows "(\<Sum>ad\<in>UNIV. unat (valtype.uint (storage_data.vt
             (if ad = msg_sender then storage_data.Value (Uint (y + msg_value))
              else mp (Address ad)))))
           \<le> Balances s this + unat msg_value"
proof -
  from sum_addr[of _ msg_sender]
  have "(\<Sum>ad|ad \<in> UNIV \<and> ad \<noteq> msg_sender.
    unat (valtype.uint (storage_data.vt (mp (Address ad))))) +
    unat (valtype.uint (storage_data.vt (mp (Address msg_sender)))) + unat msg_value
    \<le> Balances s this + unat msg_value"
  using assms(1) by simp
  moreover have "unat (valtype.uint (storage_data.vt (storage_data.Value (Uint (y + msg_value)))))
    \<le> unat (valtype.uint (storage_data.vt (mp (Address msg_sender)))) + unat msg_value"
    using assms(2,3) unat_add_lem[where ?'a =256] by simp
  ultimately show ?thesis using sum_addr[of _ msg_sender] by simp
qed

lemma sum_leq_this:
    fixes bal bal' mp
  assumes "(\<Sum>ad\<in>UNIV. unat (valtype.uint (storage_data.vt (mp (Address ad))))) \<le> Balances sa this"
      and "mp (Address this) = storage_data.Value (Uint y)"
      and "mp' (Address this) = storage_data.Value (Uint 0)"
      and "Balances s = Balances sa"
      and "\<And>x. x \<noteq> this \<Longrightarrow> mp' (Address x) = mp (Address x)"
    shows "(\<Sum>ad\<in>UNIV. unat (valtype.uint (storage_data.vt (mp' (Address ad))))) \<le> Balances sa this"
proof -
  from sum_addr[of _ this] have
    "(\<Sum>ad|ad \<in> UNIV \<and> ad \<noteq> this. unat (valtype.uint (storage_data.vt (mp (Address ad))))) +
      (unat (valtype.uint (storage_data.vt (mp (Address this)))) - unat y)
    \<le> Balances sa this - unat y"
    using assms(1,2) by simp
  moreover have "unat (valtype.uint (storage_data.vt (storage_data.Value (Uint 0))))
    \<le> unat (valtype.uint (storage_data.vt (mp (Address msg_sender)))) + unat msg_value - unat y"
    using assms(2) unat_add_lem[where ?'a =256] by simp
  ultimately show ?thesis using assms sum_addr[of _ this] by auto
qed

lemma sum_leq_sender:
    fixes bal bal' mp
  assumes "(\<Sum>ad\<in>UNIV. unat (valtype.uint (storage_data.vt (mp (Address ad))))) \<le> Balances sa this"
      and "mp (Address msg_sender) = storage_data.Value (Uint y)"
      and "mp' (Address msg_sender) = storage_data.Value (Uint 0)"
      and "Balances s = Balances sa"
      and "\<And>x. x \<noteq> msg_sender \<longrightarrow> mp' (Address x) = mp (Address x)"
    shows "(\<Sum>ad\<in>UNIV. unat (valtype.uint (storage_data.vt (mp' (Address ad))))) \<le> Balances sa this - unat y"
proof -
  from sum_addr[of _ msg_sender] have
    "(\<Sum>ad|ad \<in> UNIV \<and> ad \<noteq> msg_sender. unat (valtype.uint (storage_data.vt (mp (Address ad))))) +
      (unat (valtype.uint (storage_data.vt (mp (Address msg_sender)))) - unat y)
    \<le> Balances sa this - unat y"
    using assms(1,2) by simp
  moreover have "unat (valtype.uint (storage_data.vt (storage_data.Value (Uint 0))))
    \<le> unat (valtype.uint (storage_data.vt (mp (Address msg_sender)))) + unat msg_value - unat y"
    using assms(2) unat_add_lem[where ?'a =256] by simp
  ultimately show ?thesis using assms sum_addr[of _ msg_sender] by auto
qed

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
    "snd sb \<ge> SUMM (fst sb)"
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

abbreviation(in Solidity) true_pre where
"true_pre _  \<equiv> True"

abbreviation(in Solidity) true_post where
"true_post _ _ _  \<equiv> True"

declare(in bank) sum_balI[wprules del]

verification sum_bal:
  sum_bal
  deposit and
  withdraw and
  reset (true_pre, reset_post)
  for "Bank"
proof -
  show
    "\<And>call.
       (\<And>x h r. effect (call x) h r \<Longrightarrow> vcond x h r)
        \<Longrightarrow> effect (constructor call) s r
        \<Longrightarrow> post s r (K (K (inv_state sum_bal))) (K True)"
    unfolding constructor_def
    apply (erule post_exc_true, erule_tac post_wp)
    unfolding  inv_state_def
    by (vcg wprules: sum_balI | auto)+

  show
    b: "\<And>call.
      effect (reset call) s r
        \<Longrightarrow> (\<And>x h r. effect (call x) h r \<Longrightarrow> vcond x h r)
        \<Longrightarrow> True \<Longrightarrow> (post s r reset_post (K True))"
    unfolding reset_def
    apply (erule post_exc_true, erule_tac post_wp)
    unfolding inv_state_def
    apply vcg
    by auto

  show
    c: "\<And>call.
      (\<And>x h r. effect (call x) h r \<Longrightarrow> vcond x h r)
        \<Longrightarrow> effect (deposit call) s r
        \<Longrightarrow> inv_state sum_bal s
        \<Longrightarrow> post s r (K (K (inv_state sum_bal))) (K True)"
    unfolding deposit_def
    apply (erule post_exc_true, erule_tac post_wp)
    unfolding inv_state_def
    apply vcg
         apply (auto simp add: wpsimps)
     apply (rule bal_msg_sender, assumption)
     apply vcg
    by (auto simp add: wpsimps elim: allE[of _ "Address msg_sender"] intro!: sum_balI sum_leq_value)

  show
    d: "\<And>call.
      (\<And>x h r. effect (call x) h r \<Longrightarrow> vcond x h r)
        \<Longrightarrow> effect (withdraw call) s r
        \<Longrightarrow> inv_state sum_bal s
        \<Longrightarrow> post s r (K (K (inv_state sum_bal))) (K True)"
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
          apply (auto simp add:wpsimps intro: sum_leq_this)
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
         apply (auto simp add:wpsimps intro: sum_leq_sender)
      defer
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