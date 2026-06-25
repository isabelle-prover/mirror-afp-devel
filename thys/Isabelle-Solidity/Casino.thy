theory Casino 
  imports Solidity_Main "HOL-Eisbach.Eisbach" "HOL-Eisbach.Eisbach_Tools"
begin

section \<open>Casino Contract\<close>
text \<open>
  In the following we verify the Casino contract from the VerifyThis Long-Term Challenge:
  \<^url>\<open>https://verifythis.github.io/02casino/\<close>
  \<^url>\<open>https://verifythis.github.io/ltc/02casino/\<close>.
\<close>

subsection \<open>Specification\<close>

text \<open>
  In the following we describe the specification of the contract.
\<close>

text \<open>
  Method modifiers are formalized as abbreviations.
  They need to be formalized in the Solidity context to provide access to various contextual information.
\<close>
abbreviation "state \<equiv> STR ''state''"
abbreviation "operator \<equiv> STR ''operator''"
abbreviation "player \<equiv> STR ''player''"
abbreviation "pot \<equiv> STR ''pot''"
abbreviation "hashedNumber \<equiv> STR ''hashedNumber''"
abbreviation "bet \<equiv> STR ''bet''"
abbreviation "guess \<equiv> STR ''guess''"
abbreviation "hashNum \<equiv> STR ''hashNum''"
abbreviation "secret \<equiv> STR ''secret''"
abbreviation "bet_old \<equiv> STR ''bet_old''"
abbreviation "secretNumber \<equiv> STR ''secretNumber''"
abbreviation "amount \<equiv> STR ''amount''"


abbreviation "IDLE \<equiv> 0"
abbreviation "GAME_AVAILABLE \<equiv> 1"
abbreviation "BET_PLACED \<equiv> 2"
abbreviation "HEADS \<equiv> 0"
abbreviation "TAILS \<equiv> 1"
abbreviation "CoinT \<equiv> SType.TValue TSint"
abbreviation "StateT \<equiv> SType.TValue TSint"
abbreviation "AddressT \<equiv> SType.TValue TAddress"
abbreviation "IntT \<equiv> SType.TValue TSint"
abbreviation "Bytes32T \<equiv> SType.TValue (TBytes 32)"


context Solidity
begin

abbreviation byOperator::"(unit, ex, 'a state) state_monad" where
  "byOperator \<equiv> assert Err (\<lambda>s. storage_data.Value (valtype.Address msg_sender) = state.Storage s this operator)"

abbreviation inState:: "'a valtype \<Rightarrow> (unit, ex, 'a state) state_monad" where
  "inState st \<equiv> assert Err (\<lambda>s. state.Storage s this state = storage_data.Value st)"

abbreviation noActiveBet::"(unit, ex, ('a, 'b) state_scheme) state_monad" where
  "noActiveBet \<equiv> assert Err (\<lambda>s. state.Storage s this state \<noteq> storage_data.Value (Uint 2))"

end

text \<open>
  The contract can now be specified using the "contract" command.
  This command requires the following:
  \<^item> A sequence of member variables
  \<^item> A constructor
  \<^item> A sequence of methods
\<close>

contract Casino
  for state: StateT
  and operator: AddressT
  and player: AddressT
  and pot: IntT
  and hashedNumber: Bytes32T
  and bet: IntT
  and guess: CoinT

constructor payable
where
  "\<langle>skip\<rangle>"

cfunction createGame external payable
  param hashNum: "SType.TValue (TBytes 32)"
where
  "do {
    byOperator;
    inState (valtype.Uint 0);
    hashedNumber [] ::=\<^sub>s hashNum ~ [];
    state [] ::=\<^sub>s \<langle>sint\<rangle> 1
   }",

cfunction placeBet external payable
  param guess: "SType.TValue TSint"
where
  "do {
    inState (valtype.Uint 1);
    \<langle>assert\<rangle> (\<langle>\<not>\<rangle> (\<langle>sender\<rangle> \<langle>=\<rangle> operator ~\<^sub>s []));
    \<langle>assert\<rangle> (\<langle>value\<rangle> \<langle><\<rangle> (pot  ~\<^sub>s []) \<langle>\<or>\<rangle> \<langle>value\<rangle> \<langle>=\<rangle> (pot ~\<^sub>s []));
    state [] ::=\<^sub>s \<langle>sint\<rangle> 2;
    player [] ::=\<^sub>s \<langle>sender\<rangle>;
    bet [] ::=\<^sub>s \<langle>value\<rangle>;
    guess [] ::=\<^sub>s guess ~ []
  }",

cfunction decideBet external payable
  param secretNumber: IntT
where
  "do {
    byOperator;
    inState (Uint BET_PLACED);
    \<langle>assert\<rangle> (hashedNumber ~\<^sub>s [] \<langle>=\<rangle> (\<langle>keccak256\<rangle> (secretNumber ~ [])));
    decl TSint secret;
    secret [] ::= IF ((secretNumber ~ []) \<langle>%\<rangle> \<langle>sint\<rangle> 2) \<langle>=\<rangle> (\<langle>sint\<rangle> 0) THEN \<langle>sint\<rangle> HEADS ELSE \<langle>sint\<rangle> TAILS;
    IF (secret ~ []) \<langle>=\<rangle> (guess ~\<^sub>s []) THEN
      do {
        pot [] ::=\<^sub>s ((pot ~\<^sub>s []) \<langle>-\<rangle> (bet ~\<^sub>s []));
        bet [] ::=\<^sub>s \<langle>sint\<rangle> 0;
        \<langle>transfer\<rangle> (player ~\<^sub>s []) ((bet ~\<^sub>s []) \<langle>*\<rangle> (\<langle>sint\<rangle> 2))
      }
    ELSE
      do {
        pot [] ::=\<^sub>s pot ~\<^sub>s [] \<langle>+\<rangle> bet ~\<^sub>s [];
        bet [] ::=\<^sub>s \<langle>sint\<rangle> 0
      };
    state [] ::=\<^sub>s \<langle>sint\<rangle> IDLE
  }",

cfunction addToPot external payable
where
  "do {
    byOperator;
    pot [] ::=\<^sub>s pot ~\<^sub>s [] \<langle>+\<rangle> \<langle>value\<rangle>
  }",

cfunction removeFromPot external payable
  param amount: "SType.TValue TSint"
where
  "do {
    byOperator;
    noActiveBet;
    pot [] ::=\<^sub>s ((pot ~\<^sub>s []) \<langle>-\<rangle> (amount ~ []));
    \<langle>transfer\<rangle> (operator ~\<^sub>s []) (amount ~ [])
  }"

thm casino.addToPot_def

invariant pot_balance sb where
    "(fst sb state = storage_data.Value (Uint BET_PLACED)
      \<longrightarrow> snd sb \<ge> unat (valtype.uint (storage_data.vt (fst sb pot))) + unat (valtype.uint (storage_data.vt (fst sb bet)))
        \<and> valtype.uint (storage_data.vt (fst sb bet)) \<le> valtype.uint (storage_data.vt (fst sb pot))) \<and>
    (fst sb state \<noteq> storage_data.Value (Uint BET_PLACED)
      \<longrightarrow> snd sb \<ge> unat (valtype.uint (storage_data.vt (fst sb pot))))"
  for "casino"

section \<open>Verifying an Invariant\<close>

text \<open>
  We start by verifying an invariant regarding the relationship between pot and balance.
  To this end we need to add type information to the invariant.
  Note that an invariant is formalized as a predicate over the contracts state and balance.
\<close>

text \<open>We need to create introduction and elimination rules for the invariant and add it to the wprules and wperule lists.\<close>

text \<open>
  Now we can start verifying the invariant.
  To this end our package provides a keyword invariant which takes a property as parameter and generates proof obligations.
\<close>

context casino
begin

lemma sym2:
  assumes "storage_data.Value v = state.Storage s this x"
    shows "state.Storage s this x = storage_data.Value v"
  using assms by simp

lemma kdequals_true_dest[wpdrules]:
  assumes "kdequals a b = Some (rvalue.Value (Bool True))"
  shows "a = b"
  using assms
  apply (cases a;simp add: kdequals_def)
  apply (cases b;simp add: kdequals_def)
  by (case_tac x4;case_tac x4a;simp add: kdequals_def split: if_split_asm)


lemma kdequals_false_dest[wpdrules]:
assumes "kdequals a b = Some (rvalue.Value (Bool False))"
shows "a \<noteq> b"
  using assms
  apply (cases a;simp add: kdequals_def)
  apply (cases b;simp add: kdequals_def)
  by (case_tac x4;case_tac x4a;simp add: kdequals_def split: if_split_asm)

lemma kdnot_dest[wpdrules]:
  assumes "kdnot ya = Some (rvalue.Value (Bool True))"
  shows "ya=rvalue.Value (Bool False)"
  using assms apply (cases ya;simp add:assms kdnot_def)
  by (case_tac x4;simp add:assms vtnot_def)

lemma vt_or_dest:
  assumes "lift_value_binary vtor ye yg = Some (rvalue.Value (Bool True))"
  shows "ye = rvalue.Value (Bool True) \<or> yg = rvalue.Value (Bool True)"
 using assms
  apply (cases ye;simp add: vtor_def)
  apply (cases yg;simp add: vtor_def)
  by (case_tac x4;case_tac x4a;simp)
 

lemma kdless_dest[wpdrules]:
  assumes "kdless (rvalue.Value (Uint x)) (rvalue.Value (Uint y)) = Some (rvalue.Value (Bool True))"
  shows "x < y"
 using assms
  apply (cases x;simp add: kdless_def)
  apply (cases y;simp add: kdless_def)
  by (case_tac n;case_tac na;simp add: vtless_def)

lemma kdequals_bool_sint[wpsimps]: "kdequals (rvalue.Value (Bool x)) (rvalue.Value (Uint y)) = None"
  unfolding kdequals_def by simp 

lemma unat_add_imp:
  assumes "(unat (x::256 word) + unat y < 115792089237316195423570985008687907853269984665640564039457584007913129639936)"
    shows "(unat (x + y) = unat x + unat y)" using assms Word.unat_add_lem[where ?'a=256, of x y] by simp

lemma unat_mult_imp:
  assumes "(unat (x::256 word) * unat y < 115792089237316195423570985008687907853269984665640564039457584007913129639936)"
    shows "(unat (x * y) = unat x * unat y)" using assms Word.unat_mult_lem[where ?'a=256, of x y] by simp

lemma unat_sub_imp:
  assumes "(y::256 word) \<le> (x::256 word)"
    shows "(unat (x - y) = unat x - unat y)" using assms Word.unat_sub[where ?'a=256, of y x] by simp

lemma no_plus_overflow_leq:
  assumes a:"(x ::256 word) \<le> y"
      and b: "unat y + unat z < 2 ^ 256"
    shows "x \<le> y + z" using no_plus_overflow_unat_size[of z y] le_no_overflow[OF a, of z]
proof -
  have "size z = 256" using word_size[of z] by simp
  with b have "z \<le> z + y" using no_plus_overflow_unat_size[of z y] by simp
  then have "x \<le> z + y" using le_no_overflow[OF a, of z] by simp
  then show ?thesis by (simp add: add.commute)
qed

lemma 111:
  fixes pot
  assumes "unat pot \<le> Balances s this"
      and *: "x \<le> pot"
    shows "unat (pot - x) \<le> Balances s this + unat msg_value - unat x"
 using assms unat_sub[OF *]  by simp

lemma 222: "\<And>pot. unat pot \<le> Balances s this \<Longrightarrow>
       x \<le> pot \<Longrightarrow>
    unat (pot - x) \<le> Balances s this + unat msg_value"
  using 111 by fastforce

end

method solve methods m = (m ; fail)

lemma (in Contract) wp_assign_storage111[wperules]:
  assumes "rvalue.Value v=y"
      and "wp (storage_update_monad [] is (K (storage_data.Value v)) i) P E s"
    shows "wp (assign_storage i is y) P E s"
  using assms by auto

lemma notwp[wperules]: "\<not> wp m P E s \<Longrightarrow> wp m P E s \<Longrightarrow> R" using notE by simp

abbreviation(in Contract) createGame_post where
"createGame_post hN start_state return_value end_state \<equiv>
  state.Storage end_state this STR ''state'' = storage_data.Value (Uint 1)"

abbreviation(in Contract) placeBet_post where
"placeBet_post hn start_state return_value end_state \<equiv>
  state.Storage end_state this STR ''state'' = storage_data.Value (Uint 2)"

abbreviation(in Contract) decideBet_post where
"decideBet_post hn start_state return_value end_state \<equiv>
  state.Storage end_state this STR ''state'' = storage_data.Value (Uint 0)"

declare(in casino) pot_balanceI[wprules del]

verification pot_balance:
  pot_balance
  createGame (\<open>K (K True)\<close>, createGame_post) and
  placeBet (\<open>K (K True)\<close>, placeBet_post) and
  decideBet (\<open>K (K True)\<close>, decideBet_post) and
  addToPot and
  removeFromPot
  for "casino"
proof -
  show
    "\<And>call.
      (\<And>x h r. effect (call x) h r \<Longrightarrow> vcond x h r)
      \<Longrightarrow> effect (constructor call) s r
      \<Longrightarrow> post s r (K (K (inv_state pot_balance))) (K True)"
    unfolding constructor_def
    apply (erule post_exc_true, erule_tac post_wp)
    unfolding  inv_state_def
    by (vcg wprules: pot_balanceI | auto)+

  show
    "\<And>call hashNum.
      (\<And>x h r. effect (call x) h r \<Longrightarrow> vcond x h r)
      \<Longrightarrow> effect (createGame call hashNum) s r
      \<Longrightarrow> inv_state pot_balance s
      \<Longrightarrow> post s r (K (K (inv_state pot_balance))) (K True)"
    unfolding createGame_def
    apply (erule post_exc_true, erule_tac post_wp)
    unfolding  inv_state_def
    by (vcg wprules: pot_balanceI | solve\<open>auto simp add:wpsimps\<close>)+

  show
    "\<And>call hashNum.
      (\<And>x h r. effect (call x) h r \<Longrightarrow> vcond x h r)
      \<Longrightarrow> effect (createGame call hashNum) s r
      \<Longrightarrow> inv_state pot_balance s
      \<Longrightarrow> K (K True) hashNum s
      \<Longrightarrow> post s r (createGame_post hashNum) (K True)"
    unfolding createGame_def
    apply (erule post_exc_true, erule_tac post_wp)
    unfolding  inv_state_def
    by (vcg wprules: pot_balanceI | solve\<open>auto simp add:wpsimps\<close>)+

  show
    "\<And>call guess.
      (\<And>x h r. effect (call x) h r \<Longrightarrow> vcond x h r)
      \<Longrightarrow> effect (placeBet call guess) s r
      \<Longrightarrow> inv_state pot_balance s
      \<Longrightarrow> post s r (K (K (inv_state pot_balance))) (K True)"
    unfolding placeBet_def
    apply (erule post_exc_true, erule_tac post_wp)
    unfolding  inv_state_def
    apply (vcg | solve\<open>auto simp add:wpsimps dest:sym\<close>)+
                        apply (auto dest!: vt_or_dest)[1]
                        apply (vcg wprules: pot_balanceI | solve\<open>auto simp add:wpsimps dest:sym\<close>)+
    done

  show
    "\<And>call guess.
      (\<And>x h r. effect (call x) h r \<Longrightarrow> vcond x h r)
      \<Longrightarrow> effect (placeBet call guess) s r
      \<Longrightarrow> inv_state pot_balance s
      \<Longrightarrow> post s r (placeBet_post guess) (K True)"
    unfolding placeBet_def
    apply (erule post_exc_true, erule_tac post_wp)
    unfolding inv_state_def
    by (vcg | solve\<open>auto simp add:wpsimps dest:sym\<close>)+

  show
    "\<And>call secretNumber.
      (\<And>x h r. effect (call x) h r \<Longrightarrow> vcond x h r)
       \<Longrightarrow> effect (decideBet call secretNumber) s r
       \<Longrightarrow> inv_state pot_balance s
       \<Longrightarrow> post s r (K (K (inv_state pot_balance))) (K True)"
    unfolding decideBet_def
    apply (erule post_exc_true, erule_tac post_wp)
    unfolding  inv_state_def
    apply (vcg wprules: pot_balanceI)
                        apply (auto simp add:wpsimps)
                  apply (vcg wprules: pot_balanceI)
                        apply (auto simp add:wpsimps)
                       apply (case_tac "this = ada")
                        apply (vcg wprules: pot_balanceI)
                        apply (auto simp add:wpsimps dest:unat_sub_imp)
                      apply (case_tac "this = ada")
                       apply (vcg wprules: pot_balanceI)
                       apply (auto simp add:wpsimps dest:sym)
             apply (vcg wprules: pot_balanceI)
                     apply (auto simp add:wpsimps)
            apply (vcg wprules: pot_balanceI)
                        apply (auto simp add:wpsimps)
                apply (case_tac "this = ada")
                 apply (vcg wprules: pot_balanceI)
                 apply (auto simp add:wpsimps unat_add_imp)
               apply (case_tac "this = ada")
                apply (vcg wprules: pot_balanceI)
                apply (auto simp add:wpsimps dest:sym)
           apply (vcg wprules: pot_balanceI)
                        apply (auto simp add:wpsimps)
                apply (vcg wprules: pot_balanceI)
                        apply (auto simp add:wpsimps)
                    apply (case_tac "this = ada")
                     apply (vcg wprules: pot_balanceI)
                     apply (auto simp add:wpsimps dest:sym unat_sub_imp)
            apply (vcg wprules: pot_balanceI)
                    apply (auto simp add:wpsimps)
           apply (vcg wprules: pot_balanceI)
                        apply (auto simp add:wpsimps dest:sym unat_add_imp)
          apply (vcg wprules: pot_balanceI)
    done

  show
    "\<And>call secretNumber.
      (\<And>x h r. effect (call x) h r \<Longrightarrow> vcond x h r)
       \<Longrightarrow> effect (decideBet call secretNumber) s r
       \<Longrightarrow> inv_state pot_balance s
       \<Longrightarrow> K (K True) secretNumber s
       \<Longrightarrow> post s r (decideBet_post secretNumber) (K True)"
    unfolding decideBet_def
    apply (erule post_exc_true, erule_tac post_wp)
    unfolding inv_state_def
    apply (vcg wprules: pot_balanceI)
                        apply (auto simp add:wpsimps)
                  apply (vcg wprules: pot_balanceI)
                        apply (auto simp add:wpsimps)
                       apply (case_tac "this = ada")
                        apply (vcg wprules: pot_balanceI)
                        apply (auto simp add:wpsimps dest:unat_sub_imp)
                      apply (case_tac "this = ada")
                       apply (vcg wprules: pot_balanceI)
                       apply (auto simp add:wpsimps dest:sym)
             apply (vcg wprules: pot_balanceI)
                apply (auto simp add:wpsimps)
             apply (case_tac "this = ada")
              apply (vcg wprules: pot_balanceI)
              apply (auto simp add:wpsimps dest:sym)
           apply (vcg wprules: pot_balanceI)
                        apply (auto simp add:wpsimps)
                apply (vcg wprules: pot_balanceI)
                        apply (auto simp add:wpsimps)
                    apply (case_tac "this = ada")
                     apply (vcg wprules: pot_balanceI)
                     apply (auto simp add:wpsimps dest:sym unat_sub_imp)
            apply (vcg wprules: pot_balanceI)
               apply (auto simp add:wpsimps dest:sym unat_add_imp)
          apply (vcg wprules: pot_balanceI)
    done

  show
    "\<And>call.
      (\<And>x h r. effect (call x) h r \<Longrightarrow> vcond x h r)
      \<Longrightarrow> effect (addToPot call) s r
      \<Longrightarrow> inv_state pot_balance s
      \<Longrightarrow> post s r (K (K (inv_state pot_balance))) (K True)"
    unfolding addToPot_def
    apply (erule post_exc_true, erule_tac post_wp)
    unfolding  inv_state_def
    apply (vcg wprules: pot_balanceI | solve\<open>auto simp add:wpsimps dest:unat_add_imp sym\<close>)+
                apply (auto simp add:wpsimps no_plus_overflow_leq unat_sub_imp unat_mult_imp unat_add_imp dest:sym)
      apply (vcg wprules: pot_balanceI | solve\<open>auto simp add:wpsimps dest:unat_add_imp sym\<close>)+
    done
      
  show
    "\<And>call amount.
      (\<And>x h r. effect (call x) h r \<Longrightarrow> vcond x h r)
      \<Longrightarrow> effect (removeFromPot call amount) s r
      \<Longrightarrow> inv_state pot_balance s
      \<Longrightarrow> post s r (K (K (inv_state pot_balance))) (K True)"
    unfolding removeFromPot_def
    apply (erule post_exc_true, erule_tac post_wp)
    apply (cases "msg_sender=this")
    unfolding inv_state_def
     apply (vcg | solve\<open>auto simp add:wpsimps dest:unat_add_imp sym\<close>)+
         apply (drule_tac s = this in sym)
         apply (auto simp add:wpsimps dest:unat_add_imp sym)
         apply (vcg | solve\<open>auto simp add:wpsimps dest:unat_add_imp sym\<close>)+
             apply (auto simp add:wpsimps dest:unat_add_imp sym)
         apply (vcg | solve\<open>auto simp add:wpsimps dest:unat_add_imp sym\<close>)+
               apply (auto simp add:wpsimps dest:unat_add_imp sym)
         apply (vcg | solve\<open>auto simp add:wpsimps dest:unat_add_imp sym\<close>)+
            apply (rule_tac pot_balanceI)
                   apply (auto simp add:wpsimps intro: 111 222 dest:unat_add_imp sym)
          apply (vcg | solve\<open>auto simp add:wpsimps dest:unat_add_imp sym\<close>)+
          apply (rule_tac pot_balanceI)
                 apply (auto simp add:wpsimps dest:unat_add_imp sym)
         apply (vcg | solve\<open>auto simp add:wpsimps dest:unat_add_imp sym\<close>)+
            apply (auto simp add:wpsimps dest:unat_add_imp sym)
      apply (vcg | solve\<open>auto simp add:wpsimps dest:unat_add_imp sym\<close>)+
            apply (auto simp add:wpsimps dest:unat_add_imp sym)
      apply (vcg | solve\<open>auto simp add:wpsimps dest:unat_add_imp sym\<close>)+
         apply (rule_tac pot_balanceI)
                apply (auto simp add:wpsimps intro: 111 dest:unat_add_imp sym)
       apply (vcg | solve\<open>auto simp add:wpsimps dest:unat_add_imp sym\<close>)+
       apply (rule_tac pot_balanceI)
              apply (auto simp add:wpsimps dest:unat_add_imp sym)
      apply (vcg | solve\<open>auto simp add:wpsimps dest:unat_add_imp sym\<close>)+
    done
qed

context casino_external
begin
  thm pot_balance
  thm vcond_def
end

end