theory Voting
  imports Solidity_Main
begin

section \<open>Voting Contract\<close>

text \<open>
  In the following we verify the Voting contract from the official Solidity documentation:
  \<^url>\<open>https://docs.soliditylang.org/en/v0.8.25/solidity-by-example.html#voting\<close>.
\<close>

lemma kdequals_true[wpdrules]:
  assumes "kdequals (rvalue.Value (Uint w)) (rvalue.Value (Uint x)) = Some (rvalue.Value (Bool True))"
  shows "w = x"
  using assms unfolding kdequals_def by simp

subsection \<open>Specification\<close>

abbreviation TT::"((String.literal \<Rightarrow> 'a storage_data) \<times> nat) \<Rightarrow> bool" where "TT a \<equiv> True"

context Solidity
begin

abbreviation Voter where "Voter \<equiv> storage_data.Array [storage_data.Value (Uint 0),storage_data.Value (Bool False),storage_data.Value (Address null),storage_data.Value (Uint 0::'a valtype)]"
abbreviation "weight \<equiv> return (rvalue.Value ((Uint 0)::'a valtype))"
abbreviation "voted \<equiv> 1::nat"
abbreviation "sdelegate \<equiv> 2::nat"
abbreviation "svote \<equiv> 3::nat"

abbreviation "Proposal name voteCount \<equiv> storage_data.Array [name::'a valtype storage_data, voteCount]"
abbreviation "name \<equiv> 0::nat"
abbreviation "voteCount \<equiv> 1::nat"

end

text \<open>
  The contract can now be specified using the "contract" command.
  This command requires the following:
  \<^item> A sequence of member variables
  \<^item> A constructor
  \<^item> A sequence of methods
\<close>

context Solidity
begin

abbreviation "SUMM (x::('a valtype \<Rightarrow> 'a valtype storage_data)) \<equiv> \<Sum>ad|\<exists>v. x (Address ad) = storage_data.Array v \<and> valtype.bool (storage_data.vt (v ! 1)). (THE y. \<exists>v. x (Address ad) = storage_data.Array v \<and> y=unat (valtype.uint (storage_data.vt (v ! 0))))"
abbreviation "SUMM2 (x::'a valtype storage_data list) \<equiv> \<Sum>i<length x. (THE y. \<exists>p. x ! i = storage_data.Array p \<and> y=unat (valtype.uint (storage_data.vt (p ! 1))))"

definition inv':: "(id \<Rightarrow> 'a valtype storage_data) \<Rightarrow> bool"
  where "inv' s \<equiv> (\<forall>x y. s (STR ''voters'') = storage_data.Map x
                       \<and> s (STR ''proposals'') = storage_data.Array y
                            \<longrightarrow> (SUMM2 y \<le> SUMM x))"

end

contract Ballot
  for "STR ''chairperson''": "SType.TValue TAddress"
  and "STR ''voters''": "SType.TMap (SType.TValue TAddress) (SType.TEnum [SType.TValue TSint, SType.TValue TBool, SType.TValue TAddress, SType.TValue TSint])"
  and "STR ''proposals''": "SType.DArray (SType.TEnum [SType.TValue (TBytes 32), SType.TValue TSint])"

constructor payable
  memory "STR ''proposalNames''": "SType.DArray (SType.TValue (TBytes 32))"
where
  "do {
    assign_storage_monad (STR ''chairperson'') [] sender_monad;
    assign_storage_monad (STR ''voters'') [stackLookup (STR ''chairperson'') [], weight] (sint_monad 1);
    init (Uint 0) (STR ''i'');
    while_monad (less_monad (stackLookup (STR ''i'') []) (arrayLength (STR ''proposalNames'') []))
      (do {
        allocate (STR ''proposals'') [] (Proposal (storage_data.Value (Bytes (array 32 (CHR 0x00)))) (storage_data.Value (Uint 0)));
        assign_storage_monad (STR ''proposals'') [storeArrayLength (STR ''proposals'') [], sint_monad 0] (stackLookup (STR ''proposalNames'') [stackLookup (STR ''i'') []]);
        assign_storage_monad (STR ''proposals'') [storeArrayLength (STR ''proposals'') [], sint_monad 1] (sint_monad 0);
        assign_stack_monad (STR ''i'') [] (plus_monad (stackLookup (STR ''i'') []) (sint_monad 1))
      })
   }"

cfunction giveRightToVote external payable
  param "STR ''voter''": "SType.TValue TAddress"
where
  "do {
    require_monad (equals_monad sender_monad (storeLookup (STR ''chairperson'') []));
    require_monad (not_monad (storeLookup (STR ''voters'') [stackLookup (STR ''voter'') [], sint_monad 1]));
    require_monad (equals_monad (storeLookup (STR ''voters'') [stackLookup (STR ''voter'') [], sint_monad 0]) (sint_monad 0));
    assign_storage_monad (STR ''voters'') [stackLookup (STR ''voter'') [], sint_monad 0] (sint_monad 1)
  }",

cfunction delegate external payable
  param "STR ''to''": "SType.TValue TAddress"
where
  "do {
    sdecl (SType.TEnum [SType.TValue TSint, SType.TValue TBool, SType.TValue TAddress, SType.TValue TSint]) (STR ''sender'');
    assign_stack_monad (STR ''sender'') [] (storeLookup (STR ''voters'') [sender_monad]);
    require_monad (not_monad (equals_monad (stackLookup (STR ''sender'') [sint_monad 0]) (sint_monad 0)));
    require_monad (not_monad (stackLookup (STR ''sender'') [sint_monad 1]));
    require_monad (not_monad (equals_monad (stackLookup (STR ''to'') []) sender_monad));
    while_monad (equals_monad (storeLookup (STR ''voters'') [stackLookup (STR ''to'') [], sint_monad 2]) (address_monad null))
      (do {
        assign_stack_monad (STR ''to'') [] (storeLookup (STR ''voters'') [stackLookup (STR ''to'') [], sint_monad 2]);
        require_monad (not_monad (equals_monad (stackLookup (STR ''to'') []) sender_monad))
      });
    sdecl (SType.TEnum [SType.TValue TSint, SType.TValue TBool, SType.TValue TAddress, SType.TValue TSint]) (STR ''delegate_'');
    assign_stack_monad (STR ''delegate_'') [] (storeLookup (STR ''voters'') [stackLookup (STR ''to'') []]);
    require_monad (not_monad (less_monad (stackLookup (STR ''delegate_'') [sint_monad 0]) (sint_monad 1)));
    assign_stack_monad (STR ''sender'') [sint_monad 1] (true_monad);
    assign_stack_monad (STR ''delegate_'') [sint_monad 2] (stackLookup (STR ''to'') []);
    require_monad (not_monad (stackLookup (STR ''delegate_'') [sint_monad 1]));
    cond_monad (stackLookup (STR ''delegate_'') [sint_monad 1])
      (assign_storage_monad (STR ''proposals'') [stackLookup (STR ''delegate_'') [sint_monad 3], sint_monad 1] (plus_monad_safe (storeLookup (STR ''proposals'') [stackLookup (STR ''delegate_'') [sint_monad 3], sint_monad 1]) (stackLookup (STR ''sender'') [sint_monad 0])))
      (assign_stack_monad (STR ''delegate_'') [sint_monad 0] (plus_monad_safe (stackLookup (STR ''delegate_'') [sint_monad 0]) (stackLookup (STR ''sender'') [sint_monad 0])))
  }",

cfunction vote external payable
  param "STR ''proposal''": "SType.TValue TSint"
where
  "do {
    sdecl (SType.TEnum [SType.TValue TSint, SType.TValue TBool, SType.TValue TAddress, SType.TValue TSint]) (STR ''sender'');
    assign_stack_monad (STR ''sender'') [] (storeLookup (STR ''voters'') [sender_monad]);
    require_monad (not_monad (equals_monad (stackLookup (STR ''sender'') [sint_monad 0]) (sint_monad 0)));
    require_monad (not_monad (stackLookup (STR ''sender'') [sint_monad 1]));
    assign_stack_monad (STR ''sender'') [sint_monad 1] (true_monad);
    assign_stack_monad (STR ''sender'') [sint_monad 4] (stackLookup (STR ''proposal'') []);
    assign_storage_monad (STR ''proposals'') [stackLookup (STR ''proposal'') [], sint_monad 1] (plus_monad_safe (storeLookup (STR ''proposals'') [stackLookup (STR ''proposal'') [], sint_monad 1]) (stackLookup (STR ''sender'') [sint_monad 0]))
  }",

cfunction winningProposal external payable
  param "STR ''winningProposalu''": "SType.TValue TSint"
where
  "do {
    init (Uint 0) (STR ''winningVoteCount'');
    init (Uint 0) (STR ''p'');
    while_monad (less_monad (stackLookup (STR ''p'') []) (storeArrayLength (STR ''proposals'') []))
      (do {
        cond_monad (less_monad (stackLookup (STR ''winningVoteCount'') []) (storeLookup (STR ''proposals'') [stackLookup (STR ''p'') [], sint_monad 1]))
          (do {
            assign_stack_monad (STR ''winningVoteCount'') [] (storeLookup (STR ''proposals'') [stackLookup (STR ''p'') [], sint_monad 1]);
            assign_stack_monad (STR ''winningProposalu'') [] (stackLookup (STR ''p'') [])
          })
          (skip_monad)
      })
  }"

invariant sum_votes s
  where "inv' (fst s)"
  for "Ballot"

context ballot
begin

lemma obtain_props:
  assumes "\<forall>ya < length a. \<exists>ema. a ! ya = storage_data.Array ema \<and> (\<exists>bt sib. ema = [storage_data.Value (Bytes bt), storage_data.Value (Uint sib)])"
      and "unat ya < length a"
  obtains bt sib where "a ! unat ya = storage_data.Array [storage_data.Value (Bytes bt), storage_data.Value (Uint sib)]"
  using assms by fastforce

lemma obtain_voters:
  assumes "\<forall>x. \<exists>em. voters x = storage_data.Array em \<and> (\<exists>w t d v. em =
    [storage_data.Value (Uint w), storage_data.Value (Bool t), storage_data.Value (Address d), storage_data.Value (Uint v)])"
  obtains w t d v where "voters x =
    storage_data.Array [storage_data.Value (Uint w), storage_data.Value (Bool t), storage_data.Value (Address d), storage_data.Value (Uint v)]"
  using assms by blast

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

lemma inv_0:
  assumes "state.Storage s this STR ''voters'' = Map voters"
     and  "state.Storage s this STR ''proposals'' = storage_data.Array proposals"
     and "inv' (state.Storage s this)"
     and "voters (Address x) = storage_data.Array [storage_data.Value (Uint 0), storage_data.Value (Bool False), storage_data.Value (Address d), storage_data.Value (Uint v)]"
   shows "inv' (state.Storage
            (storage_update STR ''voters'' (Map (voters (Address x := storage_data.Array [storage_data.Value (Uint 1), storage_data.Value (Bool False), storage_data.Value (Address d), storage_data.Value (Uint v)])))
            (stack_update STR ''voter'' (kdata.Value (Address x))
            (balance_update (Balances s this + unat msg_value)
            s\<lparr>Stack := {$$}, Memory := [], Calldata := {$$}\<rparr>))) this)"
  unfolding inv'_def
proof ((rule allI | rule impI)+, erule conjE)
  fix xa y
  define sum1 where "sum1 = (\<lambda>(y::'a valtype storage_data list) i . THE ya. \<exists>p. y ! i = storage_data.Array p \<and> ya = unat (valtype.uint (storage_data.vt (p ! 1))))"
  define sum2 where "sum2 = (\<lambda>(xa::'a valtype \<Rightarrow> 'a valtype storage_data) ad. THE y. \<exists>v. xa (Address ad) = storage_data.Array v \<and> y = unat (valtype.uint (storage_data.vt (v ! 0))))"
  assume *:"state.Storage (storage_update STR ''voters'' (Map (voters(Address x := storage_data.Array [storage_data.Value (Uint 1), storage_data.Value (Bool False), storage_data.Value (Address d), storage_data.Value (Uint v)])))
             (stack_update STR ''voter'' (kdata.Value (Address x))
             (balance_update (Balances s this + unat msg_value)
             s\<lparr>Stack := {$$}, Memory := [], Calldata := {$$}\<rparr>)))
            this STR ''voters'' = Map xa"
     and **: "state.Storage (storage_update STR ''voters'' (Map (voters(Address x := storage_data.Array [storage_data.Value (Uint 1), storage_data.Value (Bool False), storage_data.Value (Address d), storage_data.Value (Uint v)])))
               (stack_update STR ''voter'' (kdata.Value (Address x))
               (balance_update (Balances s this + unat msg_value)
               s\<lparr>Stack := {$$}, Memory := [], Calldata := {$$}\<rparr>)))
              this STR ''proposals'' = storage_data.Array y"
  show "(\<Sum>i < length y. sum1 y i) \<le> (\<Sum>ad | \<exists>v. xa (Address ad) = storage_data.Array v \<and> valtype.bool (storage_data.vt (v ! 1)). sum2 xa ad)"
  proof -
    from assms have "(\<Sum>i < length proposals. sum1 proposals i) \<le> (\<Sum>ad | \<exists>v. voters (Address ad) = storage_data.Array v \<and> valtype.bool (storage_data.vt (v ! 1)). sum2 voters ad)" unfolding inv'_def sum1_def sum2_def by simp
    moreover have "(\<Sum>i < length proposals. sum1 proposals i) = (\<Sum>i < length y. sum1 y i)" using assms ** unfolding sum1_def by (simp add:wpsimps)
    moreover have "(\<Sum>ad | \<exists>v. voters (Address ad) = storage_data.Array v \<and> valtype.bool (storage_data.vt (v ! 1)). sum2 voters ad) = (\<Sum>ad | \<exists>v. xa (Address ad) = storage_data.Array v \<and> valtype.bool (storage_data.vt (v ! 1)). sum2 xa ad)"
    proof -
      from assms have " \<nexists>v. voters (Address x) = storage_data.Array v \<and> valtype.bool (storage_data.vt (v ! 1))" by simp
      then have "(\<Sum>ad | \<exists>v. voters (Address ad) = storage_data.Array v \<and> valtype.bool (storage_data.vt (v ! 1)). sum2 voters ad) = 
                 (\<Sum>ad | (\<exists>v. voters (Address ad) = storage_data.Array v \<and> valtype.bool (storage_data.vt (v ! 1))) \<and> ad \<noteq> x. sum2 voters ad)" using sum_addr3[of x "{ad.  \<exists>v. voters (Address ad) = storage_data.Array v \<and> valtype.bool (storage_data.vt (v ! 1))}" "sum2 voters"] by simp
      moreover have "\<not> (\<exists>v. xa (Address x) = storage_data.Array v \<and> valtype.bool (storage_data.vt (v ! 1)))" using * by (auto simp add:wpsimps)
      then have "(\<Sum>ad | \<exists>v. xa (Address ad) = storage_data.Array v \<and> valtype.bool (storage_data.vt (v ! 1)). sum2 xa ad) = 
                 (\<Sum>ad | (\<exists>v. xa (Address ad) = storage_data.Array v \<and> valtype.bool (storage_data.vt (v ! 1))) \<and> ad \<noteq> x. sum2 xa ad)" using sum_addr3[of x "{ad.  \<exists>v. xa (Address ad) = storage_data.Array v \<and> valtype.bool (storage_data.vt (v ! 1))}" "sum2 xa"] by simp
      moreover have "(\<Sum>ad | (\<exists>v. voters (Address ad) = storage_data.Array v \<and> valtype.bool (storage_data.vt (v ! 1))) \<and> ad \<noteq> x. sum2 voters ad)
                   = (\<Sum>ad | (\<exists>v. xa (Address ad) = storage_data.Array v \<and> valtype.bool (storage_data.vt (v ! 1))) \<and> ad \<noteq> x. sum2 xa ad)"
      proof (rule sum.mono_neutral_cong_right)
        show "finite {ad. (\<exists>v. voters (Address ad) = storage_data.Array v \<and> valtype.bool (storage_data.vt (v ! 1))) \<and> ad \<noteq> x}" using finite finite_subset subset_UNIV by blast
        show "{ad. (\<exists>v. xa (Address ad) = storage_data.Array v \<and> valtype.bool (storage_data.vt (v ! 1))) \<and> ad \<noteq> x}
        \<subseteq> {ad. (\<exists>v. voters (Address ad) = storage_data.Array v \<and> valtype.bool (storage_data.vt (v ! 1))) \<and> ad \<noteq> x}" using * by (auto simp add:wpsimps)
        show " \<forall>i\<in>{ad. (\<exists>v. voters (Address ad) = storage_data.Array v \<and> valtype.bool (storage_data.vt (v ! 1))) \<and> ad \<noteq> x} -
        {ad. (\<exists>v. xa (Address ad) = storage_data.Array v \<and> valtype.bool (storage_data.vt (v ! 1))) \<and> ad \<noteq> x}.
         sum2 voters i = 0" using * by (auto simp add:wpsimps)
        show " \<And>xb. xb \<in> {ad. (\<exists>v. xa (Address ad) = storage_data.Array v \<and> valtype.bool (storage_data.vt (v ! 1))) \<and> ad \<noteq> x} \<Longrightarrow> sum2 voters xb = sum2 xa xb"  using * unfolding sum2_def by (auto simp add:wpsimps)
      qed
      ultimately show ?thesis by simp
    qed
    ultimately show ?thesis by simp
  qed
qed

lemma inv_1:
  assumes "state.Storage s this STR ''voters'' = Map voters"
      and "state.Storage s this STR ''proposals'' = storage_data.Array proposals"
      and "inv' (state.Storage s this)"
      and "voters (Address msg_sender) = storage_data.Array [storage_data.Value (Uint w), storage_data.Value (Bool False), storage_data.Value (Address d), storage_data.Value (Uint v)]"
      and "state.Storage sa this STR ''proposals'' = storage_data.Array proposals"
      and "xa \<noteq> msg_sender"
      and "voters (Address xa) = storage_data.Array [storage_data.Value (Uint wb), storage_data.Value (Bool False), storage_data.Value (Address da), storage_data.Value (Uint va)]"
      shows "inv' (state.Storage
          (storage_update STR ''voters'' (Map (voters
                  (Address msg_sender := storage_data.Array [storage_data.Value (Uint w), storage_data.Value (Bool True), storage_data.Value (Address d), storage_data.Value (Uint v)],
                   Address xa := storage_data.Array [storage_data.Value (Uint (wb + w)), storage_data.Value (Bool False), storage_data.Value (Address xa), storage_data.Value (Uint va)])))
          (storage_update STR ''voters'' (Map (voters
                  (Address msg_sender := storage_data.Array [storage_data.Value (Uint w), storage_data.Value (Bool True), storage_data.Value (Address d), storage_data.Value (Uint v)],
                   Address xa := storage_data.Array [storage_data.Value (Uint wb), storage_data.Value (Bool False), storage_data.Value (Address xa), storage_data.Value (Uint va)])))
          (storage_update STR ''voters'' (Map (voters
                (Address msg_sender := storage_data.Array [storage_data.Value (Uint w), storage_data.Value (Bool True), storage_data.Value (Address d), storage_data.Value (Uint v)])))
          (stack_update STR ''delegate_'' (kdata.Storage (Some \<lparr>Location=STR ''voters'', Offset= [Address xa]\<rparr>)) (stack_update STR ''delegate_'' (kdata.Storage None)
          sa))))) this)"
  unfolding inv'_def
proof ((rule allI | rule impI)+, erule conjE)
  fix x y
  define sum1 where "sum1 = (\<lambda>(y::'a valtype storage_data list) i . THE ya. \<exists>p. y ! i = storage_data.Array p \<and> ya = unat (valtype.uint (storage_data.vt (p ! 1))))"
  define sum2 where "sum2 = (\<lambda>(xa::'a valtype \<Rightarrow> 'a valtype storage_data) ad. THE y. \<exists>v. xa (Address ad) = storage_data.Array v \<and> y = unat (valtype.uint (storage_data.vt (v ! 0))))"
  assume *:"state.Storage
            (storage_update STR ''voters'' (Map (voters
              (Address msg_sender := storage_data.Array [storage_data.Value (Uint w), storage_data.Value (Bool True), storage_data.Value (Address d), storage_data.Value (Uint v)],
               Address xa := storage_data.Array [storage_data.Value (Uint (wb + w)), storage_data.Value (Bool False), storage_data.Value (Address xa), storage_data.Value (Uint va)])))
            (storage_update STR ''voters'' (Map (voters
              (Address msg_sender := storage_data.Array [storage_data.Value (Uint w), storage_data.Value (Bool True), storage_data.Value (Address d), storage_data.Value (Uint v)],
               Address xa := storage_data.Array [storage_data.Value (Uint wb), storage_data.Value (Bool False), storage_data.Value (Address xa), storage_data.Value (Uint va)])))
            (storage_update STR ''voters'' (Map (voters
              (Address msg_sender := storage_data.Array [storage_data.Value (Uint w), storage_data.Value (Bool True), storage_data.Value (Address d), storage_data.Value (Uint v)])))
            (stack_update STR ''delegate_'' (kdata.Storage (Some \<lparr>Location=STR ''voters'', Offset= [Address xa]\<rparr>))
            (stack_update STR ''delegate_'' (kdata.Storage None)
            sa))))) this STR ''voters'' = Map x"
    and **: " state.Storage
            (storage_update STR ''voters'' (Map (voters
              (Address msg_sender := storage_data.Array [storage_data.Value (Uint w), storage_data.Value (Bool True), storage_data.Value (Address d), storage_data.Value (Uint v)],
               Address xa := storage_data.Array [storage_data.Value (Uint (wb + w)), storage_data.Value (Bool False), storage_data.Value (Address xa), storage_data.Value (Uint va)])))
            (storage_update STR ''voters'' (Map (voters
              (Address msg_sender := storage_data.Array [storage_data.Value (Uint w), storage_data.Value (Bool True), storage_data.Value (Address d), storage_data.Value (Uint v)],
               Address xa := storage_data.Array [storage_data.Value (Uint wb), storage_data.Value (Bool False), storage_data.Value (Address xa), storage_data.Value (Uint va)])))
            (storage_update STR ''voters'' (Map (voters
              (Address msg_sender := storage_data.Array [storage_data.Value (Uint w), storage_data.Value (Bool True), storage_data.Value (Address d), storage_data.Value (Uint v)])))
            (stack_update STR ''delegate_'' (kdata.Storage (Some \<lparr>Location=STR ''voters'', Offset= [Address xa]\<rparr>))
            (stack_update STR ''delegate_'' (kdata.Storage None)
            sa))))) this STR ''proposals'' = storage_data.Array y"
  show "(\<Sum>i < length y. sum1 y i) \<le> (\<Sum>ad | \<exists>v. x (Address ad) = storage_data.Array v \<and> valtype.bool (storage_data.vt (v ! 1)). sum2 x ad)"
  proof -
    from assms have "(\<Sum>i < length proposals. sum1 proposals i) \<le> (\<Sum>ad | \<exists>v. voters (Address ad) = storage_data.Array v \<and> valtype.bool (storage_data.vt (v ! 1)). sum2 voters ad)" unfolding inv'_def sum1_def sum2_def by simp
    moreover have "(\<Sum>i < length y. sum1 y i) = (\<Sum>i < length proposals. sum1 proposals i)"
      using * ** assms by (simp add:wpsimps)
    moreover have "(\<Sum>ad | \<exists>v. voters (Address ad) = storage_data.Array v \<and> valtype.bool (storage_data.vt (v ! 1)). sum2 voters ad) \<le> (\<Sum>ad | \<exists>v. x (Address ad) = storage_data.Array v \<and> valtype.bool (storage_data.vt (v ! 1)). sum2 x ad)"
    proof -
      have "(\<Sum>ad | (\<exists>v. x (Address ad) = storage_data.Array v \<and> valtype.bool (storage_data.vt (v ! 1)) \<and> ad \<noteq> xa) \<and> ad \<noteq> msg_sender. sum2 x ad) = (\<Sum>ad | (\<exists>v. voters (Address ad) = storage_data.Array v \<and> valtype.bool (storage_data.vt (v ! 1)) \<and> ad \<noteq> xa) \<and> ad \<noteq> msg_sender. sum2 voters ad)"
      proof (rule sum.mono_neutral_cong_right)
        show "finite {ad. (\<exists>v. x (Address ad) = storage_data.Array v \<and> valtype.bool (storage_data.vt (v ! 1)) \<and> ad \<noteq> xa) \<and> ad \<noteq> msg_sender}"  using finite finite_subset subset_UNIV by blast
        show "{ad. (\<exists>v. voters (Address ad) = storage_data.Array v \<and> valtype.bool (storage_data.vt (v ! 1)) \<and> ad \<noteq> xa) \<and> ad \<noteq> msg_sender}
              \<subseteq> {ad. (\<exists>v. x (Address ad) = storage_data.Array v \<and> valtype.bool (storage_data.vt (v ! 1)) \<and> ad \<noteq> xa) \<and> ad \<noteq> msg_sender}" using * by (auto simp add:wpsimps)
        show "\<forall>i\<in>{ad. (\<exists>v. x (Address ad) = storage_data.Array v \<and> valtype.bool (storage_data.vt (v ! 1)) \<and> ad \<noteq> xa) \<and> ad \<noteq> msg_sender} -
              {ad. (\<exists>v. voters (Address ad) = storage_data.Array v \<and> valtype.bool (storage_data.vt (v ! 1)) \<and> ad \<noteq> xa) \<and> ad \<noteq> msg_sender}.
              sum2 x i = 0"  using * by (auto simp add:wpsimps)
        show "\<And>x'. x' \<in> {ad. (\<exists>v. voters (Address ad) = storage_data.Array v \<and> valtype.bool (storage_data.vt (v ! 1)) \<and> ad \<noteq> xa) \<and> ad \<noteq> msg_sender} \<Longrightarrow> sum2 x x' = sum2 voters x'"  using * unfolding sum2_def by (auto simp add:wpsimps)
      qed
      moreover have "(\<Sum>ad | (\<exists>v. x (Address ad) = storage_data.Array v \<and> valtype.bool (storage_data.vt (v ! 1)) \<and> ad \<noteq> xa) \<and> ad \<noteq> msg_sender. sum2 x ad)
                     = (\<Sum>ad | (\<exists>v. x (Address ad) = storage_data.Array v \<and> valtype.bool (storage_data.vt (v ! 1))) \<and> ad \<noteq> msg_sender. sum2 x ad)" using * ** by (auto simp add:wpsimps)
      moreover have "(\<Sum>ad | (\<exists>v. voters (Address ad) = storage_data.Array v \<and> valtype.bool (storage_data.vt (v ! 1)) \<and> ad \<noteq> xa) \<and> ad \<noteq> msg_sender. sum2 voters ad)
                     = (\<Sum>ad | (\<exists>v. voters (Address ad) = storage_data.Array v \<and> valtype.bool (storage_data.vt (v ! 1))) \<and> ad \<noteq> msg_sender. sum2 voters ad)" using assms(7) apply (simp add:wpsimps) unfolding sum2_def
        by (metis (no_types, lifting) nth_Cons_0 nth_Cons_Suc storage_data.inject(2) storage_data.sel(1) valtype.sel(1))
      ultimately have "(\<Sum>ad | (\<exists>v. x (Address ad) = storage_data.Array v \<and> valtype.bool (storage_data.vt (v ! 1))) \<and> ad \<noteq> msg_sender. sum2 x ad)
                    = (\<Sum>ad | (\<exists>v. voters (Address ad) = storage_data.Array v \<and> valtype.bool (storage_data.vt (v ! 1))) \<and> ad \<noteq> msg_sender. sum2 voters ad)" by simp
      moreover have "sum2 voters msg_sender = sum2 x msg_sender" using * assms unfolding sum2_def by (auto simp add:wpsimps)
      moreover have "(\<Sum>ad | \<exists>v. voters (Address ad) = storage_data.Array v \<and> valtype.bool (storage_data.vt (v ! 1)). sum2 voters ad)
                      = (\<Sum>ad | (\<exists>v. voters (Address ad) = storage_data.Array v \<and> valtype.bool (storage_data.vt (v ! 1))) \<and> ad \<noteq> msg_sender. sum2 voters ad)"
      proof -
        have "\<not> (\<exists>v. voters (Address msg_sender) = storage_data.Array v \<and> valtype.bool (storage_data.vt (v ! 1)))" using assms by (auto simp add:wpsimps)
        then have "(\<Sum>ad | \<exists>v. voters (Address ad) = storage_data.Array v \<and> valtype.bool (storage_data.vt (v ! 1)). sum2 voters ad) = 
                 (\<Sum>ad | (\<exists>v. voters (Address ad) = storage_data.Array v \<and> valtype.bool (storage_data.vt (v ! 1))) \<and> ad \<noteq> msg_sender. sum2 voters ad)" using sum_addr3[of msg_sender "{ad.  \<exists>v. voters (Address ad) = storage_data.Array v \<and> valtype.bool (storage_data.vt (v ! 1))}" "sum2 voters"] by simp
        then show ?thesis by simp
      qed
      moreover have "(\<Sum>ad | \<exists>v. x (Address ad) = storage_data.Array v \<and> valtype.bool (storage_data.vt (v ! 1)). sum2 x ad)
                      = (\<Sum>ad | (\<exists>v. x (Address ad) = storage_data.Array v \<and> valtype.bool (storage_data.vt (v ! 1))) \<and> ad \<noteq> msg_sender. sum2 x ad) + sum2 x msg_sender"
      proof -
        have "(\<exists>v. x (Address msg_sender) = storage_data.Array v \<and> valtype.bool (storage_data.vt (v ! 1)))" using assms * by (auto simp add:wpsimps)
        then have "(\<Sum>ad | \<exists>v. x (Address ad) = storage_data.Array v \<and> valtype.bool (storage_data.vt (v ! 1)). sum2 x ad) = 
                   (\<Sum>ad | (\<exists>v. x (Address ad) = storage_data.Array v \<and> valtype.bool (storage_data.vt (v ! 1))) \<and> ad \<noteq> msg_sender. sum2 x ad) + sum2 x msg_sender" using sum_addr2[of msg_sender "{ad.  \<exists>v. x (Address ad) = storage_data.Array v \<and> valtype.bool (storage_data.vt (v ! 1))}" "sum2 x"] by simp
        then show ?thesis by simp
      qed
      ultimately show ?thesis by simp
    qed
    ultimately show ?thesis by simp
  qed
qed

lemma wp_assign_storage[wprules]:
  assumes "\<And>y. updateStore is (K (storage_data.Value v)) (state.Storage s this i) = Some y \<Longrightarrow> P Empty (storage_update i y s)"
      and "updateStore ([] @ is) (K (storage_data.Value v)) (state.Storage s this i) = None \<Longrightarrow> E Err s"
    shows "wp (assign_storage i is (rvalue.Value v)) P E s"
  apply vcg using assms by auto

lemma slookup_some[wpdrules]:
  assumes "proposals $ x \<bind> slookup [Uint 1] = Some yp"
  shows "x < length proposals \<and> slookup [Uint 1] (proposals ! x) = Some yp"
  using assms unfolding nth_safe_def by (auto split:if_split_asm simp add:wpsimps)
    
lemma kdplus_safe_storage_none[wpsimps]:
  shows "kdplus_safe x (rvalue.Storage p) = None"
  unfolding kdplus_safe_def by simp

lemma kdplus_safe_storage_some_false[wpdrules]:
  assumes "kdplus_safe x (rvalue.Storage p) = Some a"
  shows "False"
  using assms by (simp add:wpsimps)

lemma kdequals2[wpdrules]:
  assumes "kdequals x y = Some (rvalue.Value (Bool True))"
  shows "x = y"
  using assms
  apply (cases x;simp add: kdequals_def)
  apply (cases y;simp add: kdequals_def)
  by (case_tac x4;case_tac x4a;simp add: kdequals_def split: if_split_asm)

lemma kdequals3[wpdrules]:
  assumes "kdequals x y = Some (rvalue.Value (Bool False))"
  shows "\<not> x = y"
  using assms
  apply (cases x;simp add: kdequals_def)
  apply (cases y;simp add: kdequals_def)
  by (case_tac x4;case_tac x4a;simp add: kdequals_def split: if_split_asm)

lemma wp_less_monad[wprules]:
  assumes "wp lm (\<lambda>a. wp (rm \<bind> (\<lambda>rv. option Err (K (kdless a rv)) \<bind> return)) P E) E s"
  shows "wp (less_monad lm rm) P E s"
  unfolding less_monad_def apply (rule wp_lift_op_monad) using assms .

lemma kdnot_true[wpdrules]:
  assumes "kdnot y = Some (rvalue.Value (Bool True))"
  shows "y=rvalue.Value (Bool False)"
  using assms apply (cases y;simp add:assms kdnot_def)
  by (case_tac x4;simp add:assms vtnot_def)

lemma list_update_safe_simps1[wpsimps]:
  assumes "i < length xs"
  shows "list_update_safe xs i a = Some (list_update xs i a)"
  unfolding list_update_safe_def using assms by simp
end

lemma notwp[wperules]: "\<not> wp m P E s \<Longrightarrow> wp m P E s \<Longrightarrow> R" using notE by simp
method solve methods m = (m ; fail)

context ballot
begin

declare sum_votesI[wprules del]

end

verification sum_votes:
  sum_votes
  giveRightToVote and
  delegate and
  vote and
  winningProposal
  for "Ballot"
proof -
  show
    "\<And>call.
      (\<And>x h r. effect (call x) h r \<Longrightarrow> vcond x h r)
      \<Longrightarrow> \<exists>da. ar = adata.Array da \<and> (\<forall>y<length da. \<exists>bt. da ! y = adata.Value (Bytes bt))
      \<Longrightarrow> effect (constructor call ar) s r
      \<Longrightarrow> post s r (K (K (inv_state sum_votes))) (K True)"
    unfolding constructor_def
    apply (erule post_exc_true, erule_tac post_wp)
    unfolding  inv_state_def
    by (vcg wprules: sum_votesI | auto)+

  show
    "\<And>call voter.
      (\<And>x h r. effect (call x) h r \<Longrightarrow> vcond x h r)
      \<Longrightarrow> effect (giveRightToVote call voter) s r
      \<Longrightarrow> inv_state sum_votes s
      \<Longrightarrow> post s r (K (K (inv_state sum_votes))) (K True)"
    unfolding giveRightToVote_def
    apply (erule post_exc_true, erule_tac post_wp)
    unfolding inv_state_def
    apply (vcg | solve\<open>auto simp add:wpsimps\<close>)+
                        apply (auto simp add:wpsimps intro!: wpthrow)
       apply (rule_tac voters=mp and x="Address voter" in obtain_voters, assumption)
       apply (wp | auto simp add:wpsimps)+
       apply (rule_tac mp="mp(Address voter := storage_data.Array [storage_data.Value (Uint 1), storage_data.Value (Bool False), storage_data.Value (Address d), storage_data.Value (Uint v)])" in sum_votesI)
          apply (wp | auto simp add:wpsimps dest:sym)+
      apply (rule inv_0;assumption)
     apply (wp | auto simp add:wpsimps)+
    done

  show
    "\<And>call to.
      (\<And>x h r. effect (call x) h r \<Longrightarrow> vcond x h r)
      \<Longrightarrow> effect (delegate call to) s r
      \<Longrightarrow> inv_state sum_votes s
      \<Longrightarrow> post s r (K (K (inv_state sum_votes))) (K True)"
    unfolding delegate_def
    apply (erule post_exc_true, erule_tac post_wp)
    unfolding  inv_state_def
    apply wp
    apply wp
    apply wp
    apply (rule_tac voters=mp and x="Address msg_sender" in obtain_voters, blast)
    apply (vcg | solve\<open>auto simp add:wpsimps\<close>)+
                        apply (rule_tac iv ="\<lambda>s'. state.Storage s' this STR ''voters'' = state.Storage s this STR ''voters'' \<and>
                                                  state.Storage s' this STR ''proposals'' = state.Storage s this STR ''proposals'' \<and>
                                                  state.Storage s' this STR ''chairperson'' = state.Storage s this STR ''chairperson'' \<and>
                                                  state.Stack s' $$ (STR ''sender'') = Some (kdata.Storage (Some \<lparr>Location=STR ''voters'', Offset= [Address msg_sender]\<rparr>)) \<and>
                                                  (\<exists>x. (Stack s' $$ STR ''to'' = Some (kdata.Value (Address x)) \<and> x \<noteq> msg_sender))" in wpwhile)
                        apply (vcg | solve\<open>auto simp add:wpsimps\<close>)+
                        apply (safe)[1]
                        apply (auto simp add:wpsimps intro!: wpthrow)
      apply (vcg | solve\<open>auto simp add:wpsimps\<close>)+
                    apply (auto simp add:wpsimps intro!: wpthrow)
      apply (auto simp add:wpsimps dest: sym)[1]
     apply (vcg | solve\<open>auto simp add:wpsimps\<close>)+
                        apply (auto simp add:wpsimps intro!: wpthrow)
         apply (rule_tac voters=mp and x="Address x" in obtain_voters, assumption)
         apply (auto simp add:wpsimps)[1]
         apply (rule_tac voters=mp and x="Address x" in obtain_voters, assumption)
         apply (auto simp add:wpsimps)[1]
         apply (rule_tac voters=mp and x="Address x" in obtain_voters, assumption)
         apply (auto simp add:wpsimps)[1]
         apply (rule_tac voters=mp and x="Address x" in obtain_voters, assumption)
         apply (auto simp add:wpsimps)[1]
         apply (vcg | solve\<open>auto simp add:wpsimps\<close>)+
                apply (auto simp add:wpsimps intro!: wpthrow)
         apply (rule_tac voters=mp and x="Address x" in obtain_voters, assumption)
         apply (auto simp add:wpsimps)[1]
         apply (rule_tac mp="mp
                (Address msg_sender := storage_data.Array [storage_data.Value (Uint w), storage_data.Value (Bool True), storage_data.Value (Address d), storage_data.Value (Uint v)],
                 Address x := storage_data.Array [storage_data.Value (Uint (wa + w)), storage_data.Value (Bool False), storage_data.Value (Address x), storage_data.Value (Uint va)])" in sum_votesI)
            apply (auto simp add:wpsimps intro!: wpthrow)
         apply (rule inv_1;assumption)
        apply (rule_tac voters=mp and x="Address x" in obtain_voters, assumption)
        apply (auto simp add:wpsimps)[1]
       apply (rule_tac voters=mp and x="Address x" in obtain_voters, assumption)
       apply (auto simp add:wpsimps)[1]
      apply (rule_tac voters=mp and x="Address x" in obtain_voters, assumption)
      apply (auto simp add:wpsimps)[1]
     apply (rule_tac voters=mp and x="Address x" in obtain_voters, assumption)
     apply (auto simp add:wpsimps)[1]
    apply (rule_tac voters=mp and x="Address x" in obtain_voters, assumption)
    apply (auto simp add:wpsimps)[1]
    done

  show
    "\<And>call proposal.
      (\<And>x h r. effect (call x) h r \<Longrightarrow> vcond x h r)
      \<Longrightarrow> effect (vote call proposal) s r
      \<Longrightarrow> inv_state sum_votes s
      \<Longrightarrow> post s r (K (K (inv_state sum_votes))) (K True)"
    unfolding vote_def
    apply (erule post_exc_true, erule_tac post_wp)
    unfolding  inv_state_def
    apply (wp)
    apply (wp)
    apply (wp)
    apply (rule_tac voters=mp and x="Address msg_sender" in obtain_voters, blast)
    by (auto simp add:wpsimps intro!: wprules)+

  show
    "\<And>call winningProposalu.
      (\<And>x h r. effect (call x) h r \<Longrightarrow> vcond x h r)
      \<Longrightarrow> effect (winningProposal call winningProposalu) s r
      \<Longrightarrow> inv_state sum_votes s
      \<Longrightarrow> post s r (K (K (inv_state sum_votes))) (K True)"
    unfolding winningProposal_def
    apply (erule post_exc_true, erule_tac post_wp)
    unfolding  inv_state_def
    apply (wp)
    apply (wp)
    apply (wp)
    apply (rule_tac voters=mp and x="Address msg_sender" in obtain_voters, blast)
    apply (auto simp add:wpsimps intro!:wprules dest!:wpdrules elim!:wperules)
    apply (rule_tac iv ="\<lambda>s'. state.Storage s' = state.Storage s
                  \<and> (\<exists>x. (Stack s' $$ STR ''p'' = Some (kdata.Value (Uint x))))
                  \<and> (\<exists>x. (Stack s' $$ STR ''winningVoteCount'' = Some (kdata.Value (Uint x))))
                  \<and> (\<exists>x. (Stack s' $$ STR ''winningProposalu'' = Some (kdata.Value (Uint x))))" in wpwhile)
     apply (vcg | solve\<open>auto simp add:wpsimps\<close>)+
            apply (auto simp add:wpsimps intro!: wpthrow)
     apply vcg
                        apply (rule_tac ya=x in obtain_props, assumption)
                        apply (auto simp add:wpsimps intro!: wpthrow)
        apply (vcg | solve\<open>auto simp add:wpsimps\<close>)+
    apply (rule_tac mp=mp and da=a in sum_votesI)
       apply (auto simp add:wpsimps intro!: wpthrow)
    done
qed

context ballot_external
begin
  thm sum_votes
  thm vcond_def
end

end
