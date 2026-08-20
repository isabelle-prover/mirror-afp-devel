theory SimpleAuction
  imports Solidity_Main
begin

section \<open>Simple Auction Contract\<close>

abbreviation "SUMM x \<equiv> \<Sum>ad\<in>UNIV. unat (valtype.uint (storage_data.vt (x (Address ad))))"

text \<open>
  In the following we verify the Blind Auction contract from the official Solidity documentation:
  \<^url>\<open>https://docs.soliditylang.org/en/v0.8.25/solidity-by-example.html#blind-auction\<close>.
\<close>

subsection \<open>Specification\<close>

text \<open>
  The contract can now be specified using the "contract" command.
  This command requires the following:
  \<^item> A sequence of member variables
  \<^item> A constructor
  \<^item> A sequence of methods\<close>

contract simpleauction
  for "STR ''Beneficiary''" : "SType.TValue TAddress"
  and "STR ''auctionEndTime''" :  "SType.TValue TSint"
  and "STR ''highestBidder''" : "SType.TValue TAddress"
  and "STR ''highestBid''" : "SType.TValue TSint"
  and "STR ''pendingReturns''" : "SType.TMap (SType.TValue TAddress) (SType.TValue TSint)"
  and "STR ''ended''" : "SType.TValue TBool"

constructor payable
param "STR ''biddingTime''": "SType.TValue TSint"  
and  "STR ''beneficiaryAddress''": "SType.TValue TAddress"
  where
  "do {
      assign_storage_monad (STR ''Beneficiary'') [] (stackLookup (STR ''beneficiaryAddress'') []);
      assign_storage_monad (STR ''auctionEndTime'') []  (plus_monad_safe (stackLookup (STR ''biddingTime'') []) (block_timestamp_monad))
      }
   "
cfunction bid external payable
where
"do
{ 
assert_monad (not_monad (less_monad  (storeLookup (STR ''auctionEndTime'') []) (block_timestamp_monad)));
assert_monad (less_monad  (storeLookup (STR ''highestBid'') []) (value_monad));
 cond_monad (not_monad (equals_monad (storeLookup (STR ''highestBid'') []) (sint_monad 0)))
  (do { 
      init (Uint 0) (STR ''temp_stack_variable'');
      assign_stack_monad  (STR ''temp_stack_variable'') [] (plus_monad_safe (storeLookup (STR ''pendingReturns'') [storeLookup (STR ''highestBidder'') []]) ((storeLookup (STR ''highestBid'') []))); 
      assign_storage_monad  (STR ''pendingReturns'') [storeLookup (STR ''highestBidder'') []] (stackLookup (STR ''temp_stack_variable'') [])
        }) (skip_monad);
      assign_storage_monad (STR ''highestBidder'') [] (sender_monad);
      assign_storage_monad (STR ''highestBid'') [] (value_monad)
}",

cfunction withdraw external payable
where
  "do {
  init (Uint 0) (STR ''amount'');
  assign_stack_monad (STR ''amount'') [] (storeLookup (STR ''pendingReturns'') [sender_monad] );
  cond_monad (less_monad (sint_monad 0) (stackLookup (STR ''amount'') []))
  (do {
      assign_storage_monad (STR ''pendingReturns'') [sender_monad] (sint_monad 0);
      transfer_monad (sender_monad) (stackLookup  (STR ''amount'') [])
   }) (skip_monad)
   }",

cfunction auctionEnded external payable
where
(* sum pending returns + highest bid < balance*)
  "do {
  assert_monad ((not_monad (less_monad  (block_timestamp_monad) (storeLookup (STR ''auctionEndTime'') []))));
  assert_monad (equals_monad (storeLookup (STR ''ended'') []) (false_monad));
  assign_storage_monad (STR ''ended'') [] (true_monad);
   transfer_monad (storeLookup (STR ''Beneficiary'') []) (storeLookup  (STR ''highestBid'') [])
          }"

section \<open>Verifying an invariant\<close>


invariant pr_less_Balance s
  where "(\<forall>x y e.
            (fst s) (STR ''ended'') = storage_data.Value (Bool e) \<and>
            (fst s) (STR ''pendingReturns'') = storage_data.Map x \<and>
            (fst s) (STR ''highestBid'') =  storage_data.Value (Uint y)
          \<longrightarrow> (if e = False then ((snd s) \<ge> SUMM x + unat y) else  (snd s) \<ge> SUMM x ))"
  for "simpleauction"

thm simpleauction.pr_less_BalanceI

lemma kdequals_true[wpdrules]:
  assumes "kdequals (rvalue.Value (Address x)) (rvalue.Value (Address y)) = Some (rvalue.Value (Bool True))"
  shows "x = y"
  using assms unfolding kdequals_def by simp

lemma kdequals_false:
  assumes "kdequals (rvalue.Value (Address x)) (rvalue.Value (Address y)) = Some (rvalue.Value (Bool False))"
  shows "x \<noteq> y"
  using assms unfolding kdequals_def by simp

lemma kdnot[wpdrules]:
  assumes "kdnot (rvalue.Value (Bool t)) = Some (rvalue.Value (Bool True))"
  shows "\<not> t"
  using assms unfolding kdnot_def vtnot_def by simp

lemma kdnot2[wpdrules]:
  assumes "kdnot x = Some (rvalue.Value (Bool t))"
  shows "x = (rvalue.Value (Bool (\<not> t)))"
  using assms unfolding kdnot_def vtnot_def
  apply (case_tac x)
  apply (auto)
  apply (case_tac x4)
  by auto

lemma kdequals_true_arg_rvalue_true:
  assumes "kdequals yb (rvalue.Value (Bool True)) = Some (rvalue.Value (Bool True))"
  shows "yb = rvalue.Value (Bool True)"
  using assms
  apply (cases yb; simp add:kdequals_def)
  by (case_tac x4; simp add: kdequals_def)

lemma rvalue_equal_kdequals_true:
  assumes "kdequals y x = Some (rvalue.Value (Bool True))"
  shows "y = x"
  using assms unfolding kdequals_def apply (cases y; cases x) apply (auto)
  apply (case_tac x4; case_tac x4a) apply (auto split: if_split if_split_asm)
  done

lemma kdequals_true_arg_rvalue_false:
  assumes "kdequals (rvalue.Value (Bool xe)) (rvalue.Value (Bool False)) = Some (rvalue.Value (Bool True))"
  shows "xe = False" using assms unfolding kdequals_def by simp

   
lemma kdplus_safe_storage_none[wpsimps]:
  shows "kdplus_safe x (rvalue.Storage p) = None"
  unfolding kdplus_safe_def by simp

lemma kdplus_safe_storage_some_false[wpdrules]:
  assumes "kdplus_safe x (rvalue.Storage p) = Some a"
  shows "False"
  using assms by (simp add:wpsimps)


lemma storage_data_value_is_value [wpsimps]:
  assumes "storage_data.Value (Uint xc) = y"
  shows "storage_data.is_Value y"
  using assms
  by (auto)

lemma kdplussafe_sint [wpsimps]:
  assumes "\<forall>a. \<exists>y. x a = storage_data.Value (Uint y)"
  obtains y where "x a = storage_data.Value (Uint y)" using assms by auto

section \<open>Verifying an Invariant\<close>

lemma notwp[wperules]: "\<not> wp m P E s \<Longrightarrow> wp m P E s \<Longrightarrow> R" using notE by simp

lemma kdequals_rvalue_false_larg_inf: assumes "kdequals yi (rvalue.Value (Bool i)) = Some (rvalue.Value (Bool False))"
  shows "yi = (rvalue.Value (Bool (\<not> i)))"
  using assms unfolding kdequals_def apply (cases yi) apply (auto) apply (case_tac x4) apply (auto)
  done

lemma add_right_lessineq:
  assumes  "xb (Address msg_sender) = storage_data.Value (Uint y)"
      and" (\<Sum>ad\<in>UNIV. unat (valtype.uint (storage_data.vt (xb (Address ad))))) + unat xd \<le> Balances s this"
    shows "(\<Sum>ad\<in>UNIV. unat (valtype.uint (storage_data.vt (if ad = this then storage_data.Value (Uint (0)) else xb (Address ad)))))
           + unat xd \<le> Balances s this + unat msg_value"
  using assms sum_addr[of _ this] by simp

lemma sub_right_lessineq:
   assumes "xb (Address msg_sender) = storage_data.Value (Uint y)"
      and" (\<Sum>ad\<in>UNIV. unat (valtype.uint (storage_data.vt (xb (Address ad))))) + unat xd \<le> Balances s this"
      shows "  (\<Sum>ad\<in>UNIV. unat (valtype.uint (storage_data.vt (if ad = msg_sender then storage_data.Value (Uint 0) else xb (Address ad))))) + unat xd
       \<le> Balances s this + unat msg_value - unat y"
  using assms sum_addr[of _ msg_sender] by simp

lemma selfcall_balance_ineq:
  assumes  "xb (Address msg_sender) = storage_data.Value (Uint y)"
      and" (\<Sum>ad\<in>UNIV. unat (valtype.uint (storage_data.vt (xb (Address ad))))) \<le> Balances s msg_sender"
      and "msg_sender = this"
    shows " (\<Sum>ad\<in>UNIV. unat (valtype.uint (storage_data.vt (if ad = msg_sender then storage_data.Value (Uint 0) else xb (Address ad)))))
       \<le> Balances s msg_sender + unat msg_value"
  using assms sum_addr[of _ msg_sender] by simp

lemma notselfcall_balance_ineq:
  assumes "(\<Sum>ad\<in>UNIV. unat (valtype.uint (storage_data.vt (xb (Address ad))))) \<le> Balances s this"
      and "xb (Address msg_sender) = storage_data.Value (Uint ya)"
      and "unat ya \<le> Balances s this + unat msg_value"
      and "this \<noteq> msg_sender" 
    shows " (\<Sum>ad\<in>UNIV. unat (valtype.uint (storage_data.vt (if ad = msg_sender then storage_data.Value (Uint 0) else xb (Address ad)))))
       \<le> Balances s this + unat msg_value - unat ya"
   proof -
  from sum_addr[of _ msg_sender] have "(\<Sum>ad|ad \<in> UNIV \<and> ad \<noteq> msg_sender. unat (valtype.uint (storage_data.vt (xb (Address ad))))) +
    (unat (valtype.uint (storage_data.vt (xb (Address msg_sender)))) - unat ya) \<le> Balances s this + unat msg_value - unat ya"
  using assms(1,2, 3) by auto
  moreover have "unat (valtype.uint (storage_data.vt (storage_data.Value (Uint 0)))) \<le> unat (valtype.uint (storage_data.vt (xb (Address msg_sender)))) + unat msg_value - unat ya"
    using assms(1, 2) unat_add_lem[where ?'a =256] by simp
  ultimately show ?thesis using sum_addr[of _ msg_sender] by simp
qed

lemma sum_def_spec:  
        assumes "SUMM xb + unat xd \<le> Balances s this"
            and "xb (Address xc) = storage_data.Value (Uint yf)"
            and "unat yf + unat xd < 2^256"
      shows "  (\<Sum>ad\<in>UNIV. unat (valtype.uint (storage_data.vt (if ad = xc then storage_data.Value (Uint (yf + xd)) else xb (Address ad)))))
       \<le> Balances s this" 
proof-
  from sum_addr[of _ xc] have "(\<Sum>ad|ad \<in> UNIV \<and> ad \<noteq> xc. unat (valtype.uint (storage_data.vt (xb (Address ad))))) +
    (unat (valtype.uint (storage_data.vt (xb (Address xc))))) + unat xd \<le> Balances s this" using assms (1) by simp 
  moreover have "unat (valtype.uint (storage_data.vt (storage_data.Value (Uint (yf + xd))))) \<le> unat (valtype.uint (storage_data.vt (xb (Address xc)))) + unat xd" 
  using assms (2-3) unat_add_lem[where ?'a =256] by auto
  ultimately show ?thesis using sum_addr[of _ xc] by simp
   qed

lemma highestbid_update:
        assumes "SUMM xb  \<le> Balances s this"
            and "xb (Address xc) = storage_data.Value (Uint yf)"
            and "unat yf + unat xd < 2^256"
            and "xd < msg_value"
      shows "  (\<Sum>ad\<in>UNIV. unat (valtype.uint (storage_data.vt (if ad = xc then storage_data.Value (Uint (yf + xd)) else xb (Address ad)))))
       \<le> Balances s this + unat msg_value" 
proof-
  from sum_addr[of _ xc] have "(\<Sum>ad|ad \<in> UNIV \<and> ad \<noteq> xc. unat (valtype.uint (storage_data.vt (xb (Address ad))))) +
    (unat (valtype.uint (storage_data.vt (xb (Address xc))))) + unat msg_value \<le> Balances s this + unat msg_value" using assms (1) by simp
  moreover have "unat xd < unat msg_value" using assms(4) using Word.unat_mono[of xd] by simp
  ultimately have "(\<Sum>ad|ad \<in> UNIV \<and> ad \<noteq> xc. unat (valtype.uint (storage_data.vt (xb (Address ad))))) +
    unat (yf + xd) \<le> Balances s this + unat msg_value" using assms(2,3) unat_add_lem[where ?'a =256] by simp
  then show ?thesis using sum_addr[of _ xc] by simp
qed

abbreviation (in Solidity) post_bid where
"post_bid start_state return_value end_state \<equiv>
  state.Storage end_state this STR ''highestBidder'' = storage_data.Value (Address msg_sender) \<and>
  state.Storage end_state this STR ''highestBid'' = storage_data.Value (Uint msg_value) \<and>
  \<not> (state.Storage start_state this STR ''highestBid'' = storage_data.Value (Uint 0))
    \<longrightarrow> (\<forall>mo mn b h prn pro. 
          state.Storage start_state this STR ''pendingReturns'' = storage_data.Map mo \<and>
          state.Storage end_state this STR ''pendingReturns'' = storage_data.Map mn \<and>
          state.Storage start_state this STR ''highestBidder'' = storage_data.Value (Address b) \<and>
          state.Storage start_state this STR ''highestBid'' = storage_data.Value (Uint h) \<and>
          mn (Address b) = storage_data.Value (Uint prn) \<and>
          mo (Address b) = storage_data.Value (Uint pro)
          \<longrightarrow> prn = pro + h)"

abbreviation (in Contract) post_bid2 where
"post_bid2 start_state return_value end_state \<equiv> True"

lemma kdless_true_arg_true: assumes "kdless (rvalue.Value (Uint xd)) (rvalue.Value (Uint msg_value)) = Some (rvalue.Value (Bool True))"
  shows "xd < msg_value"
  using assms unfolding kdless_def vtless_def by simp

declare(in simpleauction) pr_less_BalanceI[wprules del]

verification pr_less_Balance:
  pr_less_Balance
  bid (\<open>K (True)\<close>, post_bid) and
  withdraw and
  auctionEnded
  for "simpleauction"
proof -
  show
    "\<And>call.
      effect (constructor call si ad) s r
      \<Longrightarrow> (\<And>x h r. effect (call x) h r \<Longrightarrow> vcond x h r)
      \<Longrightarrow> post s r (K (K (inv_state pr_less_Balance))) (K True)"
    unfolding constructor_def
    apply (erule post_exc_true, erule_tac post_wp)
    unfolding  inv_state_def
    apply (wp wprules: pr_less_BalanceI | auto simp add:wpsimps dest:sym)+
    done

  show
    "\<And>call.
      effect (bid call) s r
      \<Longrightarrow> (\<And>x h r. effect (call x) h r \<Longrightarrow> vcond x h r)
      \<Longrightarrow> inv_state pr_less_Balance s
      \<Longrightarrow> post s r (K (K (inv_state pr_less_Balance))) (K True)"
    unfolding bid_def
    apply (erule post_exc_true, erule_tac post_wp)
    unfolding  inv_state_def
    apply (vcg wprules: pr_less_BalanceI|auto simp add:wpsimps)+
          apply (rule_tac[!] x="mp" and a="Address ada" in kdplussafe_sint, assumption)
                apply (vcg wprules: pr_less_BalanceI|auto simp add: wpsimps sum_def_spec highestbid_update dest:sym dest!: rvalue_equal_kdequals_true kdnot2 kdequals_rvalue_false_larg_inf kdequals_true_arg_rvalue_true kdless_true_arg_true)+
    done

  show
    "\<And>call.
      effect (bid call) s r
      \<Longrightarrow> (\<And>x h r. effect (call x) h r \<Longrightarrow> vcond x h r)
      \<Longrightarrow> inv_state pr_less_Balance s
      \<Longrightarrow> K True s
      \<Longrightarrow> post s r post_bid (K True)"
    unfolding bid_def
    apply (erule post_exc_true, erule_tac post_wp)
    unfolding  inv_state_def
    apply (vcg wprules: pr_less_BalanceI|auto simp add:wpsimps)+
          apply (rule_tac[!] x="mp" and a="Address ada" in kdplussafe_sint, assumption)
                apply (vcg wprules: pr_less_BalanceI|auto simp add: wpsimps sum_def_spec highestbid_update dest:sym dest!: rvalue_equal_kdequals_true kdnot2 kdequals_rvalue_false_larg_inf kdequals_true_arg_rvalue_true kdless_true_arg_true)+
    done

  show
    "\<And>call.
      effect (withdraw call) s r
      \<Longrightarrow> (\<And>x h r. effect (call x) h r \<Longrightarrow> vcond x h r)
      \<Longrightarrow> inv_state pr_less_Balance s
      \<Longrightarrow> post s r (K (K (inv_state pr_less_Balance))) (K True)"
    unfolding withdraw_def
    apply (erule post_exc_true, erule_tac post_wp)
    unfolding  inv_state_def
    apply (wp | auto | simp add:wpsimps)+
           apply (vcg | auto simp add:wpsimps)+
       apply (frule_tac x = "Address msg_sender" in spec)
       apply (erule_tac exE)
       apply (wp | auto simp add:wpsimps)+
         apply (case_tac "msg_sender = this")
          apply (auto simp add:wpsimps add_right_lessineq sub_right_lessineq)
          apply (rule_tac pr_less_BalanceI)
                apply (auto simp add:wpsimps add_right_lessineq selfcall_balance_ineq)
         apply (rule_tac pr_less_BalanceI)
               apply (auto simp add:wpsimps sub_right_lessineq notselfcall_balance_ineq)
        apply vcg
        apply (rule_tac pr_less_BalanceI)
              apply (auto simp add:wpsimps)
       apply vcg
      apply (rule_tac pr_less_BalanceI)
            apply (auto simp add:wpsimps)
     apply vcg
    done

  show
    "\<And>call.
      effect (auctionEnded call) s r
      \<Longrightarrow> (\<And>x h r. effect (call x) h r \<Longrightarrow> vcond x h r)
      \<Longrightarrow> inv_state pr_less_Balance s
      \<Longrightarrow> post s r (K (K (inv_state pr_less_Balance))) (K True)"
    unfolding auctionEnded_def
    apply (erule post_exc_true, erule_tac post_wp)
    unfolding  inv_state_def
    apply (vcg)
                       apply (rule_tac pr_less_BalanceI)
                        apply (auto simp add:wpsimps split:if_split_asm dest:sym)
             apply (case_tac "ad=this")
              apply (auto simp add:wpsimps dest: kdequals_true_arg_rvalue_true kdequals_true_arg_rvalue_false)
        apply(vcg)
        apply (rule_tac pr_less_BalanceI)
              apply (auto simp add:wpsimps split:if_split_asm dest:sym)
       apply(vcg)
    done
qed

end