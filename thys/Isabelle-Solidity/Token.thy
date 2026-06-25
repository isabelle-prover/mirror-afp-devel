theory Token
  imports Solidity_Main
begin

section \<open>Token Contract\<close>

text \<open>
  In the following we verify a simple token contract from
  \<^url>\<open>https://www.isa-afp.org/entries/Solidity.html/\<close>.
\<close>

subsection \<open>Specification\<close>

abbreviation "balances \<equiv> STR ''balances''"
abbreviation "bal \<equiv> STR ''bal''"

contract Bank
  for balances: "SType.TMap (SType.TValue TAddress) (SType.TValue TSint)"

constructor payable
where
  "\<langle>skip\<rangle>"

cfunction deposit external payable
where
  "balances [\<langle>sender\<rangle>] ::=\<^sub>s balances ~\<^sub>s [\<langle>sender\<rangle>] \<langle>+\<rangle> \<langle>value\<rangle>" ,

cfunction withdraw external payable
where
  "do {
    bal :: TSint;
    bal [] ::= balances ~\<^sub>s [\<langle>sender\<rangle>];
    balances [\<langle>sender\<rangle>] ::=\<^sub>s \<langle>sint\<rangle> 0;
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

lemma 2:
    fixes bal
  assumes "SUMM bal \<le> Balances s this"
      and "bal (Address msg_sender) = storage_data.Value (Uint y)"
    shows "(\<Sum>ad \<in> UNIV. unat (valtype.uint (storage_data.vt (if ad = msg_sender then storage_data.Value (Uint 0) else bal (Address ad)))))
          \<le> Balances s this + unat msg_value - unat y"
proof -
  from sum_addr[of _ msg_sender] have "(\<Sum>ad|ad \<in> UNIV \<and> ad \<noteq> msg_sender. unat (valtype.uint (storage_data.vt (bal (Address ad))))) +
    (unat (valtype.uint (storage_data.vt (bal (Address msg_sender)))) + unat msg_value - unat y) \<le> Balances s this + unat msg_value - unat y"
  using assms(1,2) by simp
  moreover have "unat (valtype.uint (storage_data.vt (storage_data.Value (Uint 0)))) \<le> unat (valtype.uint (storage_data.vt (bal (Address msg_sender)))) + unat msg_value - unat y"
    using assms(2) unat_add_lem[where ?'a =256] by simp
  ultimately show ?thesis using sum_addr[of _ msg_sender] by simp
qed

lemma 3:
    fixes bal
  assumes "SUMM bal \<le> Balances s this"
     and "bal (Address msg_sender) = storage_data.Value (Uint y)"
  shows "(\<Sum>ad\<in>UNIV. unat (valtype.uint (storage_data.vt (if ad = msg_sender then storage_data.Value (Uint 0) else bal (Address ad)))))
       \<le> Balances s this + unat msg_value"
  using 2[OF assms] by simp

lemma 4:
    fixes bal
  assumes "SUMM bal \<le> Balances s this"
     and "bal (Address msg_sender) = storage_data.Value (Uint y)"
     and " msg_sender = this"
  shows "(\<Sum>ad\<in>UNIV. unat (valtype.uint (storage_data.vt (if ad = this then storage_data.Value (Uint 0) else bal (Address ad)))))
       \<le> Balances s this + unat msg_value"
  using 3[OF assms(1-2)] assms(3) by simp

text \<open>We need to create introduction and elimination rules for the invariant and add it to the wprules and wperule lists.\<close>

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

definition(in Solidity) deposit_post where
"deposit_post start_state return_value end_state \<equiv>
  \<exists>x y. state.Storage start_state this STR ''balances'' = storage_data.Map x
  \<and> state.Storage end_state this STR ''balances'' = storage_data.Map y
  \<and> valtype.uint (storage_data.vt (y (Address msg_sender))) = valtype.uint (storage_data.vt (x (Address msg_sender))) + msg_value"

declare(in bank) sum_balI[wprules del]

verification sum_bal:
  sum_bal
  deposit ("K True", deposit_post) and
  withdraw
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
    "\<And>call.
      (\<And>x h r. effect (call x) h r \<Longrightarrow> vcond x h r)
      \<Longrightarrow> effect (deposit call) s r
      \<Longrightarrow> inv_state sum_bal s
      \<Longrightarrow> post s r (K (K (inv_state sum_bal))) (K True)"
    unfolding deposit_def
    apply (erule post_exc_true, erule_tac post_wp)
    unfolding inv_state_def deposit_post_def
    apply vcg
         apply (auto simp add:wpsimps)
     apply (rule bal_msg_sender, assumption)
     apply vcg
      apply (auto simp add: wpsimps intro!: sum_balI 1)
    apply vcg
      apply (auto simp add:wpsimps)
    apply (rule bal_msg_sender, assumption)
    by vcg

  show
    "\<And>call.
      (\<And>x h r. effect (call x) h r \<Longrightarrow> vcond x h r)
      \<Longrightarrow> effect (deposit call) s r
      \<Longrightarrow> inv_state sum_bal s
      \<Longrightarrow> K True s
      \<Longrightarrow> post s r deposit_post (K True)"
    unfolding deposit_def
    apply (erule post_exc_true, erule_tac post_wp)
    unfolding inv_state_def deposit_post_def
    apply vcg
         apply (auto simp add:wpsimps)
     apply (rule bal_msg_sender, assumption)
     apply vcg
      apply (auto simp add: wpsimps intro!: sum_balI 1)
    apply vcg
      apply (auto simp add:wpsimps)
    apply (rule bal_msg_sender, assumption)
    by vcg

  show
    "\<And>call.
      (\<And>x h r. effect (call x) h r \<Longrightarrow> vcond x h r)
      \<Longrightarrow> effect (withdraw call) s r
      \<Longrightarrow> inv_state sum_bal s
      \<Longrightarrow> post s r (K (K (inv_state sum_bal))) (K True)"
    unfolding withdraw_def
    apply (erule post_exc_true, erule_tac post_wp)
    unfolding inv_state_def
    apply (case_tac "msg_sender = this")
     apply (vcg)
     apply (auto simp add:wpsimps)
     apply (rule_tac bal_msg_sender, assumption)
    apply (vcg)
     apply (rule_tac s = msg_sender in subst,assumption)
     apply (vcg)
    apply (rule subst,assumption)
           apply (vcg)
             apply (rule subst,assumption)
             apply (vcg)
             apply (auto simp add:wpsimps)
     apply (vcg)
        apply (auto simp add:wpsimps)
     apply (vcg)
        apply (rule_tac mp = "mp(Address msg_sender := storage_data.Value (Uint 0))" in sum_balI)
         apply vcg
         apply (auto simp add:wpsimps 4)
      apply vcg
      apply (rule_tac mp = mpa in sum_balI)
       apply vcg
          apply (auto)
     apply vcg
        apply (auto simp add:wpsimps)
     apply (rule bal_msg_sender, assumption)
     apply vcg
        apply (rule_tac mp = "mp(Address msg_sender := storage_data.Value (Uint 0))" in sum_balI)
         apply (simp add:2 wpsimps)
        apply (simp add:wpsimps)
       apply vcg
    done
qed

context bank_external
begin
  thm sum_bal
  thm vcond_def
end

end