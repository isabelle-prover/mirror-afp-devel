section\<open>Reentrancy\<close>

text \<open>
  In the following we use our calculus to verify a contract implementing a simple token.
  The contract is defined by definition *bank* and consist of one state variable and two methods:
  \<^item> The state variable "balance" is a mapping which assigns a balance to each address.
  \<^item> Method "deposit" allows to send money to the contract which is then added to the sender's balance.
  \<^item> Method "withdraw" allows to withdraw the callers balance.
\<close>

text \<open>
  We then verify that the following invariant (defined by *BANK*) is preserved by both methods:
  The difference between
  \<^item> the contracts own account-balance and
  \<^item> the sum of all the balances kept in the contracts state variable
  is larger than a certain threshold.
\<close>

text \<open>
  There are two things to note here:
  First, Solidity implicitly triggers the call of a so-called fallback method whenever we transfer money to a contract.
  In particular if another contract calls "withdraw", this triggers an implicit call to the callee's fallback method.
  This functionality was exploited in the infamous DAO attack which we demonstrate it in terms of an example later on.
  Since we do not know all potential contracts which call "withdraw", we need to verify our invariant for all possible Solidity programs.
\<close>

text \<open>
  The second thing to note is that we were not able to verify that the difference is indeed constant.
  During verification it turned out that this is not the case since in the fallback method a contract could just send us additional money without calling "deposit".
  In such a case the difference would change. In particular it would grow. However, we were able to verify that the difference does never shrink which is what we actually want to ensure.
\<close>

theory Reentrancy
  imports Weakest_Precondition Solidity_Evaluator
  "HOL-Eisbach.Eisbach_Tools"
begin

subsection\<open>Example of Re-entrancy\<close>

definition[solidity_symbex]:"example_env \<equiv>
              loadProc (STR ''Attacker'')
                ([],
                ([], SKIP),
                 ITE (LESS (BALANCE THIS) (UINT 256 125))
                   (EXTERNAL (ADDRESS (STR ''BankAddress'')) (STR ''withdraw'') [] (UINT 256 0))
                   SKIP)
              (loadProc (STR ''Bank'')
                ([(STR ''balance'', Var (STMap TAddr (STValue (TUInt 256)))),
                (STR ''deposit'', Method ([], True,
                  ASSIGN
                    (Ref (STR ''balance'') [SENDER])
                    (PLUS (LVAL (Ref (STR ''balance'') [SENDER])) VALUE))),
                (STR ''withdraw'', Method ([], True,
                  ITE (LESS (UINT 256 0) (LVAL (Ref (STR ''balance'') [SENDER])))
                    (COMP
                      (TRANSFER SENDER (LVAL (Ref (STR ''balance'') [SENDER])))
                      (ASSIGN (Ref (STR ''balance'') [SENDER]) (UINT 256 0)))
                    SKIP))],
                ([], SKIP),
                SKIP)
                fmempty)"

global_interpretation reentrancy: statement_with_gas costs_ex example_env costs_min
  defines stmt = "reentrancy.stmt"
      and lexp = reentrancy.lexp 
      and expr = reentrancy.expr
      and ssel = reentrancy.ssel
      and rexp = reentrancy.rexp
      and msel = reentrancy.msel
      and load = reentrancy.load
      and eval = reentrancy.eval
  by unfold_locales auto

lemma "eval 1000
          (COMP
            (EXTERNAL (ADDRESS (STR ''BankAddress'')) (STR ''deposit'') [] (UINT 256 10))
            (EXTERNAL (ADDRESS (STR ''BankAddress'')) (STR ''withdraw'') [] (UINT 256 0)))
          (STR ''AttackerAddress'')
          (STR ''Attacker'')
          (STR '''')
          (STR ''0'')
          [(STR ''BankAddress'', STR ''100'', Contract (STR ''Bank''), 0), (STR ''AttackerAddress'', STR ''100'', Contract (STR ''Attacker''), 0)]
          []
  = STR ''BankAddress: balance==70 - Bank(balance[AttackerAddress]==0\<newline>)\<newline>AttackerAddress: balance==130 - Attacker()''"
  by eval

subsection\<open>Definition of Contract\<close>

abbreviation myrexp::L
  where "myrexp \<equiv> Ref (STR ''balance'') [SENDER]"

abbreviation mylval::E
  where "mylval \<equiv> LVAL myrexp"

abbreviation assign::S
  where "assign \<equiv> ASSIGN (Ref (STR ''balance'') [SENDER]) (UINT 256 0)"

abbreviation transfer::S
  where "transfer \<equiv> TRANSFER SENDER (LVAL (Id (STR ''bal'')))"

abbreviation comp::S
  where "comp \<equiv> COMP assign transfer"

abbreviation keep::S
  where "keep \<equiv> BLOCK ((STR ''bal'', Value (TUInt 256)), Some mylval) comp"

abbreviation deposit::S
  where "deposit \<equiv> ASSIGN (Ref (STR ''balance'') [SENDER]) (PLUS (LVAL (Ref (STR ''balance'') [SENDER])) VALUE)"

abbreviation "banklist \<equiv> [
          (STR ''balance'', Var (STMap TAddr (STValue (TUInt 256)))),
          (STR ''deposit'', Method ([], True, deposit)),
          (STR ''withdraw'', Method ([], True, keep))]"

definition bank::"(Identifier, Member) fmap"
  where "bank \<equiv> fmap_of_list banklist"

subsection\<open>Verification\<close>

locale Reentrancy = Calculus +
  assumes r0: "cname = STR ''Bank''"
      and r1: "members = bank"
      and r2: "fb = SKIP"
      and r3: "const = ([], SKIP)"
begin

subsubsection\<open>Method lemmas\<close>
text \<open>
  These lemmas are required by @{term vcg_external}.
\<close>

lemma mwithdraw[mcontract]:
  "members $$ STR ''withdraw'' = Some (Method ([], True, keep))"
  using r1 unfolding bank_def by simp

lemma mdeposit[mcontract]:
  "members $$ STR ''deposit'' = Some (Method ([], True, deposit))"
  using r1 unfolding bank_def by simp

subsubsection\<open>Variable lemma\<close>

lemma balance:
  "members $$ (STR ''balance'') = Some (Var (STMap TAddr (STValue (TUInt 256))))"
  using r1 bank_def fmlookup_of_list[of "[(STR ''balance'', Var (STMap TAddr (STValue (TUInt 256)))), (STR ''deposit'', Method ([], True, ASSIGN myrexp (PLUS mylval VALUE))),
      (STR ''withdraw'', Method ([], True, BLOCK ((STR ''bal'', Value (TUInt 256)), Some mylval) (COMP (ASSIGN myrexp (UINT 256 0)) Reentrancy.transfer)))]"] by simp

subsubsection\<open>Case lemmas\<close>
text \<open>
  These lemmas are required by @{term vcg_transfer}.
\<close>
lemma cases_ext: 
  assumes "members $$ mid = Some (Method (fp,True,f))"
      and "fp = [] \<Longrightarrow> P deposit"
      and "fp = [] \<Longrightarrow> P keep"
    shows "P f"
proof -
  from assms(1) r1 consider (withdraw) "mid = STR ''withdraw''" | (deposit) "mid = STR ''deposit''" using bank_def fmap_of_list_SomeD[of "[(STR ''balance'', Var (STMap TAddr (STValue (TUInt 256)))), (STR ''deposit'', Method ([], True, deposit)), (STR ''withdraw'', Method ([], True, keep))]"] by auto
  then show ?thesis
  proof (cases)
    case withdraw
    then have "f = keep" and "fp = []" using assms(1) bank_def r1 fmlookup_of_list[of banklist] by simp+
    then show ?thesis using assms(3) by simp
  next
    case deposit
    then have "f = deposit" and "fp = []" using assms(1) bank_def r1 fmlookup_of_list[of banklist] by simp+
    then show ?thesis using assms(2) by simp
  qed
qed

lemma cases_int: 
  assumes "members $$ mid = Some (Method (fp,False,f))"
    shows "P fp f"
  using assms r1 bank_def fmap_of_list_SomeD[of "[(STR ''balance'', Var (STMap TAddr (STValue (TUInt 256)))), (STR ''deposit'', Method ([], True, deposit)), (STR ''withdraw'', Method ([], True, keep))]"] by auto

lemma cases_fb: 
  assumes "P SKIP"
  shows "P fb"
using assms bank_def r2 by simp

lemma cases_cons: 
  assumes "fst const = [] \<Longrightarrow> P (fst const, SKIP)"
  shows "P const"
using assms bank_def r3 by simp

subsubsection\<open>Definition of Invariant\<close>

abbreviation "SUMM s \<equiv> \<Sum>(ad,x)|fmlookup s (ad + (STR ''.'' + STR ''balance'')) = Some x. ReadL\<^sub>i\<^sub>n\<^sub>t x"

abbreviation "POS s \<equiv> \<forall>ad x. fmlookup s (ad + (STR ''.'' + STR ''balance'')) = Some x \<longrightarrow> ReadL\<^sub>i\<^sub>n\<^sub>t x \<ge> 0"

definition "iv s a \<equiv> a \<ge> SUMM s \<and> POS s"

lemma weaken:
  assumes "iv (storage st ad) (ReadL\<^sub>i\<^sub>n\<^sub>t (bal (acc ad)) - ReadL\<^sub>i\<^sub>n\<^sub>t v)"
      and "ReadL\<^sub>i\<^sub>n\<^sub>t v \<ge>0"
    shows "iv (storage st ad) (ReadL\<^sub>i\<^sub>n\<^sub>t (bal (acc ad)))"
using assms unfolding iv_def by simp

subsubsection\<open>Additional lemmas\<close>

lemma expr_0:
  assumes "load True [] xe (ffold (init members) (emptyEnv ad cname (address env) v) (fmdom members)) emptyStore emptyStore emptyStore env cd (st\<lparr>gas := g1\<rparr>) g1 = Normal ((e\<^sub>l, cd\<^sub>l, k\<^sub>l, m\<^sub>l), g1')"
      and "decl STR ''bal'' (Value (TUInt 256)) (Some (lv, lt)) False cd\<^sub>l m\<^sub>l s (cd\<^sub>l, m\<^sub>l, k\<^sub>l, e\<^sub>l) =  Some (cd', mem', sck', e')"
      and "expr (UINT 256 0) ev0 cd0 st0 g0 = Normal ((rv, rt),g''a)"
    shows "rv= KValue (ShowL\<^sub>i\<^sub>n\<^sub>t 0)" and "rt=Value (TUInt 256)"
  using assms(3) by (simp add:expr.simps createUInt_def split:if_split_asm)+

lemma load_empty_par:
  assumes "load True [] xe (ffold (init members) (emptyEnv ad cname (address env) v) (fmdom members)) emptyStore emptyStore emptyStore env cd (st\<lparr>gas := g1\<rparr>) g1 = Normal ((e\<^sub>l, cd\<^sub>l, k\<^sub>l, m\<^sub>l), g1')"
    shows "load True [] [] (ffold (init members) (emptyEnv ad cname (address env) v) (fmdom members)) emptyStore emptyStore emptyStore env cd (st\<lparr>gas := g1\<rparr>) g1 = Normal ((e\<^sub>l, cd\<^sub>l, k\<^sub>l, m\<^sub>l), g1')"
proof -
  have "xe=[]"
  proof (rule ccontr)
    assume "\<not> xe=[]"
    then obtain x and xa where "xe=x # xa" by (meson list.exhaust)
    then have "load True [] xe (ffold (init members) (emptyEnv ad cname (address env) v) (fmdom members)) emptyStore emptyStore emptyStore env cd (st\<lparr>gas := g1\<rparr>) g1 = throw Err g1" by (simp add:load.simps)
    with assms show False by simp
  qed
  then show ?thesis using assms(1) by simp
qed

lemma lexp_myrexp_decl:
  assumes "load True [] xe (ffold (init members) (emptyEnv ad cname (address env) v) (fmdom members)) emptyStore emptyStore emptyStore env cd (st\<lparr>gas := g1\<rparr>) g1 = Normal ((e\<^sub>l, cd\<^sub>l, k\<^sub>l, m\<^sub>l), g1')"
      and "decl STR ''bal'' (Value (TUInt 256)) (Some (lv, lt)) False cd\<^sub>l m\<^sub>l s (cd\<^sub>l, m\<^sub>l, k\<^sub>l, e\<^sub>l) =  Some (cd', mem', sck', e')"
      and "lexp myrexp e' cd' (st0\<lparr>accounts := acc, stack := sck', memory := mem', gas := g'a\<rparr>) g'a = Normal ((rv,rt), g''a)"
    shows "rv= LStoreloc (address env + (STR ''.'' + STR ''balance''))" and "rt=Storage (STValue (TUInt 256))"
proof -
  have "fmlookup (denvalue (ffold (init members) (emptyEnv ad cname (address env) v) (fmdom members))) (STR ''balance'') = Some (Storage (STMap TAddr (STValue (TUInt 256))), Storeloc (STR ''balance''))" unfolding emptyEnv_def using ffold_init_fmdom balance by simp
  moreover have el_def: "e\<^sub>l = (ffold (init members) (emptyEnv ad cname (address env) v) (fmdom members))" using load_empty_par[OF assms(1)] by (simp add:load.simps)
  ultimately have "fmlookup (denvalue e\<^sub>l) (STR ''balance'') = Some (Storage (STMap TAddr (STValue (TUInt 256))), Storeloc (STR ''balance''))" using assms by auto
  then have *: "fmlookup (denvalue e') (STR ''balance'') = Some (Storage (STMap TAddr (STValue (TUInt 256))), Storeloc (STR ''balance''))" using decl_env[OF assms(2)] by simp

  moreover obtain g'' where "ssel (STMap TAddr (STValue (TUInt 256))) (STR ''balance'') [SENDER] e' cd' (st0\<lparr>accounts := acc, stack := sck', memory := mem', gas := g'a\<rparr>) g'a = Normal (((address env) + (STR ''.'' + STR ''balance''), STValue (TUInt 256)), g'')"
  proof -
    have "g'a > costs\<^sub>e SENDER e' cd' (st0\<lparr>accounts := acc, stack := sck', memory := mem', gas := g'a\<rparr>)" using assms(3) * by (simp add:expr.simps ssel.simps lexp.simps split:if_split_asm)
    then obtain g'' where "expr SENDER e' cd' (st0\<lparr>accounts := acc, stack := sck', memory := mem', gas := g'a\<rparr>) g'a = Normal ((KValue (sender e'), Value TAddr), g'')" by (simp add:expr.simps)
    moreover have "sender e\<^sub>l = address env" using el_def ffold_init_ad_same[of members "(emptyEnv ad cname (address env) v)" "fmdom members" e\<^sub>l] unfolding emptyEnv_def by simp
    then have "sender e' = address env" using decl_env[OF assms(2)] by simp
    ultimately show ?thesis using that hash_def by (simp add:ssel.simps)
  qed
  ultimately show "rv= LStoreloc (address env + (STR ''.'' + STR ''balance''))" and "rt=Storage (STValue (TUInt 256))" using assms(3) by (simp add:lexp.simps)+
qed

lemma expr_bal: 
  assumes "expr (LVAL (L.Id STR ''bal'')) e' cd' (st\<lparr>accounts := acc, stack := sck', memory := mem', gas := g''a, storage := (storage st) (address e' := fmupd l v' s'), gas := g''\<rparr>) g'' = Normal ((KValue lv, Value t), g''')"
      and "(sck', e') = astack STR ''bal'' (Value (TUInt 256)) (KValue (accessStorage (TUInt 256) (address env + (STR ''.'' + STR ''balance'')) s')) (k\<^sub>l, e\<^sub>l)"
    shows "(\<lceil>accessStorage (TUInt 256) (address env + (STR ''.'' + STR ''balance'')) s'\<rceil>::int) = ReadL\<^sub>i\<^sub>n\<^sub>t lv" (is ?G1) and "t = TUInt 256"
proof -
  from assms(1)
  have "expr (LVAL (L.Id STR ''bal'')) e' cd' (st\<lparr>accounts := acc, stack := sck', memory := mem', gas := g''a, storage := (storage st) (address e' := fmupd l v' s'), gas := g''\<rparr>) g'' = rexp ((L.Id STR ''bal'')) e' cd' ((st\<lparr>accounts := acc, stack := sck', memory := mem', gas := g''a, storage := (storage st) (address e' := fmupd l v' s'), gas := g''\<rparr>)) (g'' - costs\<^sub>e (LVAL (L.Id STR ''bal'')) e' cd' (st\<lparr>accounts := acc, stack := sck', memory := mem', gas := g''a, storage := (storage st) (address e' := fmupd l v' s'), gas := g''\<rparr>))" by (simp add:expr.simps split:if_split_asm)
  moreover have "rexp ((L.Id STR ''bal'')) e' cd' ((st\<lparr>accounts := acc, stack := sck', memory := mem', gas := g''a, storage := (storage st) (address e' := fmupd l v' s'), gas := g''\<rparr>)) (g'' - costs\<^sub>e (LVAL (L.Id STR ''bal'')) e' cd' (st\<lparr>accounts := acc, stack := sck', memory := mem', gas := g''a, storage := (storage st) (address e' := fmupd l v' s'), gas := g''\<rparr>)) = Normal ((KValue (accessStorage (TUInt 256) (address env + (STR ''.'' + STR ''balance'')) s'), (Value (TUInt 256))),(g'' - costs\<^sub>e (LVAL (L.Id STR ''bal'')) e' cd' (st\<lparr>accounts := acc, stack := sck', memory := mem', gas := g''a, storage := (storage st) (address e' := fmupd l v' s'), gas := g''\<rparr>)) )"
  proof -
    from assms(2) have "fmlookup (denvalue e') (STR ''bal'') = Some (Value (TUInt 256), Stackloc \<lfloor>toploc k\<^sub>l\<rfloor>)" by (simp add:push_def allocate_def updateStore_def )
    moreover have "accessStore (\<lfloor>toploc k\<^sub>l\<rfloor>) sck' = Some (KValue (accessStorage (TUInt 256) (address env + (STR ''.'' + STR ''balance'')) s'))" using assms(2) by (simp add:push_def allocate_def updateStore_def accessStore_def)
    ultimately show ?thesis by (simp add:rexp.simps)
  qed
  ultimately have "expr (LVAL (L.Id STR ''bal'')) e' cd' (st\<lparr>accounts := acc, stack := sck', memory := mem', gas := g''a, storage := (storage st) (address e' := fmupd l v' s'), gas := g''\<rparr>) g'' = Normal ((KValue (accessStorage (TUInt 256) (address env + (STR ''.'' + STR ''balance'')) s'), (Value (TUInt 256))),(g'' - costs\<^sub>e (LVAL (L.Id STR ''bal'')) e' cd' (st\<lparr>accounts := acc, stack := sck', memory := mem', gas := g''a, storage := (storage st) (address e' := fmupd l v' s'), gas := g''\<rparr>)))" and "t = TUInt 256" using assms(1) by simp+
  then have "lv = accessStorage (TUInt 256) (address env + (STR ''.'' + STR ''balance'')) s'" using assms(1) by (auto)
  with `t = TUInt 256` show ?G1 and "t = TUInt 256" by simp+
qed

lemma lexp_myrexp:
  assumes "load True [] xe (ffold (init members) (emptyEnv ad cname (address env) v) (fmdom members)) emptyStore emptyStore emptyStore env cd (st\<lparr>gas := g1\<rparr>) g1 = Normal ((e\<^sub>l, cd\<^sub>l, k\<^sub>l, m\<^sub>l), g1')"
      and "lexp myrexp e\<^sub>l cd\<^sub>l (st'\<lparr>gas := g2\<rparr>) g2 = Normal ((rv,rt), g2')"
    shows "rv= LStoreloc (address env + (STR ''.'' + STR ''balance''))" and "rt=Storage (STValue (TUInt 256))"
proof -
  have "fmlookup (denvalue (ffold (init members) (emptyEnv ad cname (address env) v) (fmdom members))) (STR ''balance'') = Some (Storage (STMap TAddr (STValue (TUInt 256))), Storeloc (STR ''balance''))" unfolding emptyEnv_def using ffold_init_fmdom balance by simp
  moreover have el_def: "e\<^sub>l = (ffold (init members) (emptyEnv ad cname (address env) v) (fmdom members))" using load_empty_par[OF assms(1)] by (simp add:load.simps)
  ultimately have *: "fmlookup (denvalue e\<^sub>l) (STR ''balance'') = Some (Storage (STMap TAddr (STValue (TUInt 256))), Storeloc (STR ''balance''))" using assms by auto

  moreover obtain g'' where "ssel (STMap TAddr (STValue (TUInt 256))) (STR ''balance'') [SENDER] e\<^sub>l cd\<^sub>l (st'\<lparr>gas := g2\<rparr>) g2 = Normal (((address env) + (STR ''.'' + STR ''balance''), STValue (TUInt 256)), g'')"
  proof -
    have "g2 > costs\<^sub>e SENDER e\<^sub>l cd\<^sub>l (st'\<lparr>gas := g2\<rparr>)" using assms(2) * by (simp add:expr.simps ssel.simps lexp.simps split:if_split_asm)
    then obtain g'' where "expr SENDER e\<^sub>l cd\<^sub>l (st'\<lparr>gas := g2\<rparr>) g2 = Normal ((KValue (sender e\<^sub>l), Value TAddr), g'')" by (simp add: expr.simps)
    moreover have "sender e\<^sub>l = address env" using el_def ffold_init_ad_same[of members "(emptyEnv ad cname (address env) v)" "fmdom members" e\<^sub>l] unfolding emptyEnv_def by simp
    ultimately show ?thesis using that hash_def by (simp add:ssel.simps)
  qed
  ultimately show "rv= LStoreloc (address env + (STR ''.'' + STR ''balance''))" and "rt=Storage (STValue (TUInt 256))" using assms(2) by (simp add: lexp.simps)+
qed

lemma expr_balance:
  assumes "load True [] xe (ffold (init members) (emptyEnv ad cname (address env) v) (fmdom members)) emptyStore emptyStore emptyStore env cd (st\<lparr>gas := g1\<rparr>) g1 = Normal ((e\<^sub>l, cd\<^sub>l, k\<^sub>l, m\<^sub>l), g1')"
      and "expr (LVAL (Ref (STR ''balance'') [SENDER])) e\<^sub>l cd\<^sub>l (st\<lparr>accounts := acc, stack := k\<^sub>l, memory := m\<^sub>l, gas := g2\<rparr>) g2 = Normal ((va, ta), g'a)"
    shows "va= KValue (accessStorage (TUInt 256) (address env + (STR ''.'' + STR ''balance'')) (storage st ad))"
      and "ta = Value (TUInt 256)"
proof -
  have "fmlookup (denvalue (ffold (init members) (emptyEnv ad cname (address env) v) (fmdom members))) (STR ''balance'') = Some (Storage (STMap TAddr (STValue (TUInt 256))), Storeloc (STR ''balance''))" unfolding emptyEnv_def using ffold_init_fmdom balance by simp
  moreover have el_def: "e\<^sub>l = (ffold (init members) (emptyEnv ad cname (address env) v) (fmdom members))" using load_empty_par[OF assms(1)] by (simp add:load.simps)
  ultimately have *: "fmlookup (denvalue e\<^sub>l) (STR ''balance'') = Some (Storage (STMap TAddr (STValue (TUInt 256))), Storeloc (STR ''balance''))" using assms by auto

  moreover obtain g'' where "ssel (STMap TAddr (STValue (TUInt 256))) (STR ''balance'') [SENDER] e\<^sub>l cd\<^sub>l (st\<lparr>accounts := acc, stack := k\<^sub>l, memory := m\<^sub>l, gas := g2\<rparr>) g2 = Normal (((address env) + (STR ''.'' + STR ''balance''), STValue (TUInt 256)), g'')"
  proof -
    have "g2 > costs\<^sub>e SENDER e\<^sub>l cd\<^sub>l (st\<lparr>accounts := acc, stack := k\<^sub>l, memory := m\<^sub>l, gas := g2\<rparr>)" using assms(2) * by (simp add: expr.simps ssel.simps rexp.simps split:if_split_asm)
    then obtain g'' where "expr SENDER e\<^sub>l cd\<^sub>l (st\<lparr>accounts := acc, stack := k\<^sub>l, memory := m\<^sub>l, gas := g2\<rparr>) g2 = Normal ((KValue (sender e\<^sub>l), Value TAddr), g'')" by (simp add:expr.simps ssel.simps rexp.simps)
    moreover have "sender e\<^sub>l = address env" using el_def ffold_init_ad_same[of members "(emptyEnv ad cname (address env) v)" "fmdom members" e\<^sub>l] unfolding emptyEnv_def by simp
    ultimately show ?thesis using that hash_def by (simp add:expr.simps ssel.simps rexp.simps)
  qed
  moreover have "ad = address e\<^sub>l" using el_def ffold_init_ad_same[of members "(emptyEnv ad cname (address env) v)" "fmdom members" e\<^sub>l] unfolding emptyEnv_def by simp
  ultimately show "va= KValue (accessStorage (TUInt 256) (address env + (STR ''.'' + STR ''balance'')) (storage st ad))" and "ta = Value (TUInt 256)" using assms(2) by (simp add:expr.simps ssel.simps rexp.simps split:if_split_asm)+
qed

lemma balance_inj: "inj_on (\<lambda>(ad, x). (ad + (STR ''.'' + STR ''balance''),x)) {(ad, x). (fmlookup y \<circ> f) ad = Some x}"
proof
  fix v v' assume asm1: "v \<in> {(ad, x). (fmlookup y \<circ> f) ad = Some x}" and asm2: "v' \<in> {(ad, x). (fmlookup y \<circ> f) ad = Some x}"
  and *:"(case v of (ad, x) \<Rightarrow> (ad + (STR ''.'' + STR ''balance''),x)) = (case v' of (ad, x) \<Rightarrow> (ad + (STR ''.'' + STR ''balance''),x))"
  then obtain ad ad' x x' where **: "v = (ad,x)" and ***: "v'=(ad',x')" by auto
  moreover from * ** *** have "ad + (STR ''.'' + STR ''balance'') = ad' + (STR ''.'' + STR ''balance'')" by simp
  with * ** have "ad = ad'" using String_Cancel[of ad "STR ''.'' + STR ''balance''" ad' ] by simp
  moreover from asm1 asm2 ** *** have "(fmlookup y \<circ> f) ad = Some x" and "(fmlookup y \<circ> f) ad' = Some x'" by auto
  with calculation(3) have "x=x'" by simp
  ultimately show "v=v'" by simp
qed

lemma fmfinite: "finite ({(ad, x). fmlookup y ad = Some x})"
proof -
  have "{(ad, x). fmlookup y ad = Some x} \<subseteq> dom (fmlookup y) \<times> ran (fmlookup y)"
  proof
    fix x assume "x \<in> {(ad, x). fmlookup y ad = Some x}"
    then have "fmlookup y (fst x) = Some (snd x)" by auto
    then have "fst x \<in> dom (fmlookup y)" and "snd x \<in> ran (fmlookup y)" using Map.ranI by (blast,metis)
    then show "x \<in> dom (fmlookup y) \<times> ran (fmlookup y)" by (simp add: mem_Times_iff)
  qed
  thus ?thesis by (simp add: finite_ran finite_subset)
qed

lemma fmlookup_finite:
  fixes f :: "'a \<Rightarrow> 'a"
    and y :: "('a, 'b) fmap"
  assumes "inj_on (\<lambda>(ad, x). (f ad, x)) {(ad, x). (fmlookup y \<circ> f) ad = Some x}"
  shows "finite {(ad, x). (fmlookup y \<circ> f) ad = Some x}"
proof (cases rule: inj_on_finite[OF assms(1), of "{(ad, x)|ad x. (fmlookup y) ad = Some x}"])
  case 1
  then show ?case by auto
next
  case 2
  then have *: "finite {(ad, x) |ad x. fmlookup y ad = Some x}" using fmfinite[of y] by simp
  show ?case using finite_image_set[OF *, of "\<lambda>(ad, x). (ad, x)"] by simp
qed

lemma expr_plus:
  assumes "load True [] xe (ffold (init members) (emptyEnv ad cname (address env) v) (fmdom members)) emptyStore emptyStore emptyStore env cd (st\<lparr>gas := g3\<rparr>) g3 = Normal ((e\<^sub>l, cd\<^sub>l, k\<^sub>l, m\<^sub>l), g3')"
      and "expr (PLUS a0 b0) ev0 cd0 st0 g0 = Normal ((xs, t'0), g'0)"
    shows "\<exists>s. xs = KValue (s)"
  using assms by (auto simp add:expr.simps split:if_split_asm result.split_asm prod.split_asm Stackvalue.split_asm Type.split_asm option.split_asm)

lemma summ_eq_sum:
  "SUMM s' = (\<Sum>(ad,x)|fmlookup s' (ad + (STR ''.'' + STR ''balance'')) = Some x \<and> ad \<noteq> adr. ReadL\<^sub>i\<^sub>n\<^sub>t x)
           + ReadL\<^sub>i\<^sub>n\<^sub>t (accessStorage (TUInt 256) (adr + (STR ''.'' + STR ''balance'')) s')"
proof (cases "fmlookup s' (adr + (STR ''.'' + STR ''balance'')) = None")
  case True
  then have "accessStorage (TUInt 256) (adr + (STR ''.'' + STR ''balance'')) s' = ShowL\<^sub>i\<^sub>n\<^sub>t 0" unfolding accessStorage_def by simp
  moreover have "{(ad,x). fmlookup s' (ad + (STR ''.'' + STR ''balance'')) = Some x} = {(ad,x). fmlookup s' (ad + (STR ''.'' + STR ''balance'')) = Some x \<and> ad \<noteq> adr}"
  proof
    show "{(ad, x). fmlookup s' (ad + (STR ''.'' + STR ''balance'')) = Some x} \<subseteq> {(ad, x). fmlookup s' (ad + (STR ''.'' + STR ''balance'')) = Some x \<and> ad \<noteq> adr}"
    proof
      fix x
      assume "x \<in> {(ad, x). fmlookup s' (ad + (STR ''.'' + STR ''balance'')) = Some x}"
      then show "x \<in> {(ad, x). fmlookup s' (ad + (STR ''.'' + STR ''balance'')) = Some x \<and> ad \<noteq> adr}" using True by auto
    qed
  next
    show "{(ad, x). fmlookup s' (ad + (STR ''.'' + STR ''balance'')) = Some x \<and> ad \<noteq> adr} \<subseteq> {(ad, x). fmlookup s' (ad + (STR ''.'' + STR ''balance'')) = Some x }"
    proof
      fix x
      assume "x \<in> {(ad, x). fmlookup s' (ad + (STR ''.'' + STR ''balance'')) = Some x \<and> ad \<noteq> adr}"
      then show "x \<in> {(ad, x). fmlookup s' (ad + (STR ''.'' + STR ''balance'')) = Some x}" using True by auto
    qed
  qed
  then have "SUMM s' = (\<Sum>(ad,x)|fmlookup s' (ad + (STR ''.'' + STR ''balance'')) = Some x \<and> ad \<noteq> adr. ReadL\<^sub>i\<^sub>n\<^sub>t x)" by simp
  ultimately show ?thesis using Read_ShowL_id by simp
next
  case False
  then obtain val where val_def: "fmlookup s' (adr + (STR ''.'' + STR ''balance'')) = Some val" by auto

  have "inj_on (\<lambda>(ad, x). (ad + (STR ''.'' + STR ''balance''), x)) {(ad, x). (fmlookup s' \<circ> (\<lambda>ad. ad + (STR ''.'' + STR ''balance''))) ad = Some x}" using balance_inj by simp
  then have "finite {(ad, x). (fmlookup s' \<circ> (\<lambda>ad. ad + (STR ''.'' + STR ''balance''))) ad = Some x}" using fmlookup_finite[of "\<lambda>ad. (ad + (STR ''.'' + STR ''balance''))" s'] by simp
  then have sum1: "finite ({(ad,x). fmlookup s' (ad + (STR ''.'' + STR ''balance'')) = Some x \<and> ad \<noteq> adr})" using finite_subset[of "{(ad, x). fmlookup s' (ad + (STR ''.'' + STR ''balance'')) = Some x \<and> ad \<noteq> adr}" "{(ad, x). fmlookup s' (ad + (STR ''.'' + STR ''balance'')) = Some x}"] by auto
  moreover have sum2: "(adr,val) \<notin> {(ad,x). fmlookup s' (ad + (STR ''.'' + STR ''balance'')) = Some x \<and> ad \<noteq> adr}" by simp
  moreover from sum1 val_def have "insert (adr,val) {(ad, x). fmlookup s' (ad + (STR ''.'' + STR ''balance'')) = Some x \<and> ad \<noteq> adr} = {(ad, x). fmlookup s' (ad + (STR ''.'' + STR ''balance'')) = Some x}" by auto
  ultimately show ?thesis using sum.insert[OF sum1 sum2, of "\<lambda>(ad,x). ReadL\<^sub>i\<^sub>n\<^sub>t x"] val_def unfolding accessStorage_def by simp
qed

lemma sum_eq_update:
  assumes s''_def: "s'' = fmupd (adr + (STR ''.'' + STR ''balance'')) v' s'"
    shows "(\<Sum>(ad,x)|fmlookup s'' (ad + (STR ''.'' + STR ''balance'')) = Some x \<and> ad \<noteq> adr. ReadL\<^sub>i\<^sub>n\<^sub>t x)
          =(\<Sum>(ad,x)|fmlookup s' (ad + (STR ''.'' + STR ''balance'')) = Some x \<and> ad \<noteq> adr. ReadL\<^sub>i\<^sub>n\<^sub>t x)"
proof -
  have "{(ad,x). fmlookup s'' (ad + (STR ''.'' + STR ''balance'')) = Some x \<and> ad \<noteq> adr} = {(ad,x). fmlookup s' (ad + (STR ''.'' + STR ''balance'')) = Some x \<and> ad \<noteq> adr}"
  proof
    show "{(ad, x). fmlookup s'' (ad + (STR ''.'' + STR ''balance'')) = Some x \<and> ad \<noteq> adr}
       \<subseteq> {(ad, x). fmlookup s' (ad + (STR ''.'' + STR ''balance'')) = Some x \<and> ad \<noteq> adr}"
    proof
      fix xx
      assume "xx \<in> {(ad, x). fmlookup s'' (ad + (STR ''.'' + STR ''balance'')) = Some x \<and> ad \<noteq> adr}"
      then obtain ad x where "xx = (ad,x)" and "fmlookup s'' (ad + (STR ''.'' + STR ''balance'')) = Some x" and "ad \<noteq> adr" by auto
      then have "fmlookup s' (ad + (STR ''.'' + STR ''balance'')) = Some x" using String_Cancel[of ad "(STR ''.'' + STR ''balance'')" "adr"] s''_def by (simp split:if_split_asm)
      with `ad \<noteq> adr` `xx = (ad,x)` show "xx \<in> {(ad, x). fmlookup s' (ad + (STR ''.'' + STR ''balance'')) = Some x \<and> ad \<noteq> adr}" by simp
    qed
  next
    show "{(ad, x). fmlookup s' (ad + (STR ''.'' + STR ''balance'')) = Some x \<and> ad \<noteq> adr}
       \<subseteq> {(ad, x). fmlookup s'' (ad + (STR ''.'' + STR ''balance'')) = Some x \<and> ad \<noteq> adr}"
    proof
      fix xx
      assume "xx \<in> {(ad, x). fmlookup s' (ad + (STR ''.'' + STR ''balance'')) = Some x \<and> ad \<noteq> adr}"
      then obtain ad x where "xx = (ad,x)" and "fmlookup s' (ad + (STR ''.'' + STR ''balance'')) = Some x" and "ad \<noteq> adr" by auto
      then have "fmlookup s'' (ad + (STR ''.'' + STR ''balance'')) = Some x" using String_Cancel[of ad "(STR ''.'' + STR ''balance'')" "adr"] s''_def by (auto split:if_split_asm)
      with `ad \<noteq> adr` `xx = (ad,x)` show "xx \<in> {(ad, x). fmlookup s'' (ad + (STR ''.'' + STR ''balance'')) = Some x \<and> ad \<noteq> adr}" by simp
    qed
  qed
  thus ?thesis by simp
qed

lemma adapt_deposit:
  assumes "address env \<noteq> ad"
      and "load True [] xe (ffold (init members) (emptyEnv ad cname (address env) v) (fmdom members)) emptyStore emptyStore emptyStore env cd (st0\<lparr>gas := g3\<rparr>) g3 = Normal ((e\<^sub>l, cd\<^sub>l, k\<^sub>l, m\<^sub>l), g3')"
      and "Accounts.transfer (address env) ad v a = Some acc"
      and "iv (storage st0 ad) (ReadL\<^sub>i\<^sub>n\<^sub>t (bal (acc ad)) - ReadL\<^sub>i\<^sub>n\<^sub>t v)"
      and "lexp myrexp e\<^sub>l cd\<^sub>l (st0\<lparr>gas := g'', accounts := acc, stack := k\<^sub>l, memory := m\<^sub>l, gas := g'\<rparr>) g' = Normal ((LStoreloc l, Storage (STValue t')), g''a)"
      and "expr (PLUS mylval VALUE) e\<^sub>l cd\<^sub>l (st0\<lparr>gas := g'', accounts := acc, stack := k\<^sub>l, memory := m\<^sub>l, gas := g\<rparr>) g = Normal ((KValue va, Value ta), g')"
      and "Valuetypes.convert ta t' va = Some v'"
    shows "(ad = address e\<^sub>l \<longrightarrow> iv (storage st0 (address e\<^sub>l)(l $$:= v')) \<lceil>bal (acc (address e\<^sub>l))\<rceil>) \<and>
           (ad \<noteq> address e\<^sub>l \<longrightarrow> iv (storage st0 ad) (ReadL\<^sub>i\<^sub>n\<^sub>t (bal (acc ad))))"
proof (rule conjI; rule impI)
  assume "ad = address e\<^sub>l"
  define s' s'' where "s' = storage st0 (address e\<^sub>l)" and "s'' = storage st0 (address e\<^sub>l)(l $$:= v')"
  then have "s'' = fmupd l v' s'" by simp
  moreover from lexp_myrexp[OF assms(2) assms(5)] have "l = address env + (STR ''.'' + STR ''balance'')" and "t'=TUInt 256" by simp+
  ultimately have s''_s': "s'' = s' (address env + (STR ''.'' + STR ''balance'') $$:= v')" by simp

  have "fmlookup (denvalue (ffold (init members) (emptyEnv ad cname (address env) v) (fmdom members))) (STR ''balance'') = Some (Storage (STMap TAddr (STValue (TUInt 256))), Storeloc (STR ''balance''))" unfolding emptyEnv_def using ffold_init_fmdom balance by simp
  moreover have "e\<^sub>l = (ffold (init members) (emptyEnv ad cname (address env) v) (fmdom members))" using load_empty_par[OF assms(2)] by (simp add:load.simps)
  ultimately have "fmlookup (denvalue e\<^sub>l) (STR ''balance'') = Some (Storage (STMap TAddr (STValue (TUInt 256))), Storeloc (STR ''balance''))" by simp
  then have va_def: "va = (createUInt 256 ((ReadL\<^sub>i\<^sub>n\<^sub>t (accessStorage (TUInt 256) ((sender e\<^sub>l) + (STR ''.'' + STR ''balance'')) s') + ReadL\<^sub>i\<^sub>n\<^sub>t (svalue e\<^sub>l))))" 
   and "ta = (TUInt 256)" 
  using assms(6) Read_ShowL_id unfolding s'_def by (auto split:if_split_asm simp add: expr.simps ssel.simps rexp.simps add_def olift.simps hash_def)

  have "svalue e\<^sub>l = v" and "sender e\<^sub>l = address env" and "address e\<^sub>l = ad" using ffold_init_ad_same msel_ssel_expr_load_rexp_gas(4)[OF assms(2)] unfolding emptyEnv_def by simp+
  then have a_frame: "iv s' (ReadL\<^sub>i\<^sub>n\<^sub>t (bal (acc ad)) - ReadL\<^sub>i\<^sub>n\<^sub>t v)" using assms(4) unfolding s'_def by simp

  from assms(1) have  "ReadL\<^sub>i\<^sub>n\<^sub>t (bal (a ad)) + ReadL\<^sub>i\<^sub>n\<^sub>t v < 2^256" using transfer_val2[OF assms(3)] by simp
  moreover from `address env \<noteq> ad` have "ReadL\<^sub>i\<^sub>n\<^sub>t (bal (acc ad)) = ReadL\<^sub>i\<^sub>n\<^sub>t (bal (a ad)) + ReadL\<^sub>i\<^sub>n\<^sub>t v" using transfer_add[OF assms(3)] by simp
  ultimately have a_bal: "ReadL\<^sub>i\<^sub>n\<^sub>t (bal (acc ad)) < 2^256" by simp

  moreover have a_bounds:
      "ReadL\<^sub>i\<^sub>n\<^sub>t (accessStorage (TUInt 256) (sender e\<^sub>l + (STR ''.'' + STR ''balance'')) s')  + \<lceil>svalue e\<^sub>l\<rceil> < 2 ^ 256 \<and>
      ReadL\<^sub>i\<^sub>n\<^sub>t (accessStorage (TUInt 256) (sender e\<^sub>l + (STR ''.'' + STR ''balance'')) s')  + \<lceil>svalue e\<^sub>l\<rceil> \<ge> 0"
  proof (cases "fmlookup s' (sender e\<^sub>l + (STR ''.'' + STR ''balance'')) = None")
    case True
    hence "(accessStorage (TUInt 256) (sender e\<^sub>l + (STR ''.'' + STR ''balance'')) s') = ShowL\<^sub>i\<^sub>n\<^sub>t 0" unfolding accessStorage_def by simp
    moreover have "(\<lceil>svalue e\<^sub>l\<rceil>::int) < 2 ^ 256"
    proof -
      from a_frame have "\<lceil>svalue e\<^sub>l\<rceil> + SUMM s' \<le> ReadL\<^sub>i\<^sub>n\<^sub>t (bal (acc ad))" unfolding iv_def using `svalue e\<^sub>l = v` by simp
      moreover have "0 \<le> SUMM s'"
      using a_frame sum_nonneg[of "{(ad,x). fmlookup s' (ad + (STR ''.'' + STR ''balance'')) = Some x}" "\<lambda>(ad,x). ReadL\<^sub>i\<^sub>n\<^sub>t x"] unfolding iv_def by auto
      ultimately have "\<lceil>svalue e\<^sub>l\<rceil> \<le> ReadL\<^sub>i\<^sub>n\<^sub>t (bal (acc ad))" by simp
      then show "(\<lceil>svalue e\<^sub>l\<rceil>::int) < 2 ^ 256" using a_bal by simp
    qed
    moreover have "ReadL\<^sub>i\<^sub>n\<^sub>t v \<ge> 0" using transfer_val1[OF assms(3)] by simp
    with `svalue e\<^sub>l = v` have "(\<lceil>svalue e\<^sub>l\<rceil>::int) \<ge> 0" by simp
    ultimately show ?thesis using Read_ShowL_id by simp
  next
    case False
    then obtain x where x_def: "fmlookup s'  (sender e\<^sub>l + (STR ''.'' + STR ''balance'')) = Some x" by auto
    moreover from a_frame have "\<lceil>svalue e\<^sub>l\<rceil> + SUMM s' \<le> ReadL\<^sub>i\<^sub>n\<^sub>t (bal (acc ad))" unfolding iv_def using `svalue e\<^sub>l = v` by simp
    moreover have "(case (sender e\<^sub>l, x) of (ad, x) \<Rightarrow> \<lceil>x\<rceil>) \<le> (\<Sum>(ad, x)\<in>{(ad, x). fmlookup s' (ad + (STR ''.'' + STR ''balance'')) = Some x}. ReadL\<^sub>i\<^sub>n\<^sub>t x)"
    proof (cases rule: member_le_sum[of "(sender e\<^sub>l,x)" "{(ad,x). fmlookup s' (ad + (STR ''.'' + STR ''balance'')) = Some x}" "\<lambda>(ad,x). ReadL\<^sub>i\<^sub>n\<^sub>t x"])
      case 1
      then show ?case using x_def by simp
    next
      case (2 x)
      with a_frame show ?case unfolding iv_def by auto
    next
      case 3
      have "inj_on (\<lambda>(ad, x). (ad + (STR ''.'' + STR ''balance''), x)) {(ad, x). (fmlookup s' \<circ> (\<lambda>ad. ad + (STR ''.'' + STR ''balance''))) ad = Some x}" using balance_inj by simp
      then have "finite {(ad, x). (fmlookup s' \<circ> (\<lambda>ad. ad + (STR ''.'' + STR ''balance''))) ad = Some x}" using fmlookup_finite[of "\<lambda>ad. (ad + (STR ''.'' + STR ''balance''))" s'] by simp
      then show ?case using finite_subset[of "{(ad, x). fmlookup s' (ad + (STR ''.'' + STR ''balance'')) = Some x}" "{(ad, x). fmlookup s' (ad + (STR ''.'' + STR ''balance'')) = Some x}"] by auto
    qed
    then have "ReadL\<^sub>i\<^sub>n\<^sub>t x \<le> SUMM s'" by simp
    ultimately have "\<lceil>svalue e\<^sub>l\<rceil> + ReadL\<^sub>i\<^sub>n\<^sub>t x \<le> ReadL\<^sub>i\<^sub>n\<^sub>t (bal (acc ad))" by simp
    then have "\<lceil>svalue e\<^sub>l\<rceil> + ReadL\<^sub>i\<^sub>n\<^sub>t x \<le> ReadL\<^sub>i\<^sub>n\<^sub>t (bal (acc ad))" by simp
    with a_bal have "\<lceil>svalue e\<^sub>l\<rceil> + ReadL\<^sub>i\<^sub>n\<^sub>t x < 2^256" by simp
    then have "\<lceil>svalue e\<^sub>l\<rceil> \<le> \<lceil>bal (acc ad)\<rceil> - SUMM s'" and lck: "fmlookup s' (sender e\<^sub>l + (STR ''.'' + STR ''balance'')) = Some x"  and "ReadL\<^sub>i\<^sub>n\<^sub>t x + \<lceil>svalue e\<^sub>l\<rceil> < 2 ^ 256" using a_frame x_def `svalue e\<^sub>l = v` unfolding iv_def by auto
    moreover from lck have "(accessStorage (TUInt 256) (sender e\<^sub>l + (STR ''.'' + STR ''balance'')) s') = x" unfolding accessStorage_def by simp
    moreover have "\<lceil>svalue e\<^sub>l\<rceil> + ReadL\<^sub>i\<^sub>n\<^sub>t x \<ge> 0"
    proof -
      have "ReadL\<^sub>i\<^sub>n\<^sub>t v \<ge> 0" using transfer_val1[OF assms(3)] by simp
      with `svalue e\<^sub>l = v` have "(\<lceil>svalue e\<^sub>l\<rceil>::int) \<ge> 0" by simp
      moreover from a_frame have "ReadL\<^sub>i\<^sub>n\<^sub>t x \<ge> 0" unfolding iv_def using x_def by simp
      ultimately show ?thesis by simp
    qed
    ultimately show ?thesis using Read_ShowL_id by simp
  qed
  ultimately have "va = ShowL\<^sub>i\<^sub>n\<^sub>t (ReadL\<^sub>i\<^sub>n\<^sub>t (accessStorage (TUInt 256) (sender e\<^sub>l + (STR ''.'' + STR ''balance'')) s') + ReadL\<^sub>i\<^sub>n\<^sub>t (svalue e\<^sub>l))" using createUInt_id[where ?v="ReadL\<^sub>i\<^sub>n\<^sub>t (accessStorage (TUInt 256) (sender e\<^sub>l + (STR ''.'' + STR ''balance'')) s') + ReadL\<^sub>i\<^sub>n\<^sub>t (svalue e\<^sub>l)"] va_def by simp
  then have v'_def: "v' = ShowL\<^sub>i\<^sub>n\<^sub>t (ReadL\<^sub>i\<^sub>n\<^sub>t (accessStorage (TUInt 256) (address env + (STR ''.'' + STR ''balance'')) s') + ReadL\<^sub>i\<^sub>n\<^sub>t v)" using `sender e\<^sub>l = address env` `svalue e\<^sub>l = v` `t'=TUInt 256` `ta = (TUInt 256)` using assms(7) by auto

  have "SUMM s'' \<le> \<lceil>bal (acc ad)\<rceil>"
  proof -
    have "SUMM s' \<le> ReadL\<^sub>i\<^sub>n\<^sub>t (bal (acc ad)) - ReadL\<^sub>i\<^sub>n\<^sub>t v" using a_frame unfolding iv_def by simp
    moreover have "SUMM s'' = SUMM s' + ReadL\<^sub>i\<^sub>n\<^sub>t v"
    proof -
      from summ_eq_sum have s1: "SUMM s' = (\<Sum>(ad,x)|fmlookup s' (ad + (STR ''.'' + STR ''balance'')) = Some x \<and> ad \<noteq> address env. ReadL\<^sub>i\<^sub>n\<^sub>t x) + ReadL\<^sub>i\<^sub>n\<^sub>t (accessStorage (TUInt 256) (address env + (STR ''.'' + STR ''balance'')) s')" by simp
      have s2: "SUMM s'' = (\<Sum>(ad,x)|fmlookup s'' (ad + (STR ''.'' + STR ''balance'')) = Some x \<and> ad \<noteq> address env. ReadL\<^sub>i\<^sub>n\<^sub>t x) + ReadL\<^sub>i\<^sub>n\<^sub>t (accessStorage (TUInt 256) (address env + (STR ''.'' + STR ''balance'')) s') + ReadL\<^sub>i\<^sub>n\<^sub>t v"
      proof -
        have "inj_on (\<lambda>(ad, x). (ad + (STR ''.'' + STR ''balance''), x)) {(ad, x). (fmlookup s'' \<circ> (\<lambda>ad. ad + (STR ''.'' + STR ''balance''))) ad = Some x}" using balance_inj by simp
        then have "finite {(ad, x). (fmlookup s'' \<circ> (\<lambda>ad. ad + (STR ''.'' + STR ''balance''))) ad = Some x}" using fmlookup_finite[of "\<lambda>ad. (ad + (STR ''.'' + STR ''balance''))" s''] by simp
        then have sum1: "finite ({(ad,x). fmlookup s'' (ad + (STR ''.'' + STR ''balance'')) = Some x \<and> ad \<noteq> address env})" using finite_subset[of "{(ad, x). fmlookup s'' (ad + (STR ''.'' + STR ''balance'')) = Some x \<and> ad \<noteq> address env}" "{(ad, x). fmlookup s'' (ad + (STR ''.'' + STR ''balance'')) = Some x}"] by auto
        moreover have sum2: "(address env, ShowL\<^sub>i\<^sub>n\<^sub>t (ReadL\<^sub>i\<^sub>n\<^sub>t (accessStorage (TUInt 256) (address env + (STR ''.'' + STR ''balance'')) s') + ReadL\<^sub>i\<^sub>n\<^sub>t v)) \<notin> {(ad,x). fmlookup s'' (ad + (STR ''.'' + STR ''balance'')) = Some x \<and> ad \<noteq> address env}" by simp
        moreover from v'_def s''_s' have "insert (address env, ShowL\<^sub>i\<^sub>n\<^sub>t (ReadL\<^sub>i\<^sub>n\<^sub>t (accessStorage (TUInt 256) (address env + (STR ''.'' + STR ''balance'')) s') + ReadL\<^sub>i\<^sub>n\<^sub>t v)) {(ad, x). fmlookup s'' (ad + (STR ''.'' + STR ''balance'')) = Some x \<and> ad \<noteq> address env} = {(ad, x). fmlookup s'' (ad + (STR ''.'' + STR ''balance'')) = Some x}" by auto
        then show ?thesis using sum.insert[OF sum1 sum2, of "\<lambda>(ad,x). ReadL\<^sub>i\<^sub>n\<^sub>t x"] Read_ShowL_id by simp
      qed
      from sum_eq_update[OF s''_s'] have s3: "(\<Sum>(ad,x)|fmlookup s'' (ad + (STR ''.'' + STR ''balance'')) = Some x \<and> ad \<noteq> address env. ReadL\<^sub>i\<^sub>n\<^sub>t x)
                    =(\<Sum>(ad,x)|fmlookup s' (ad + (STR ''.'' + STR ''balance'')) = Some x \<and> ad \<noteq> address env. ReadL\<^sub>i\<^sub>n\<^sub>t x)" by simp
      moreover from s''_s' v'_def have "ReadL\<^sub>i\<^sub>n\<^sub>t (accessStorage (TUInt 256) (address env + (STR ''.'' + STR ''balance'')) s'') = ReadL\<^sub>i\<^sub>n\<^sub>t (accessStorage (TUInt 256) (address env + (STR ''.'' + STR ''balance'')) s') + ReadL\<^sub>i\<^sub>n\<^sub>t v" using Read_ShowL_id unfolding accessStorage_def by simp
      ultimately have "SUMM s''= SUMM s' + ReadL\<^sub>i\<^sub>n\<^sub>t v"
      proof -
        from s2 have "SUMM s'' = (\<Sum>(ad,x)|fmlookup s'' (ad + (STR ''.'' + STR ''balance'')) = Some x \<and> ad \<noteq> address env. ReadL\<^sub>i\<^sub>n\<^sub>t x) + ReadL\<^sub>i\<^sub>n\<^sub>t (accessStorage (TUInt 256) (address env + (STR ''.'' + STR ''balance'')) s') + ReadL\<^sub>i\<^sub>n\<^sub>t v" by simp
        also from s3 have "\<dots> = (\<Sum>(ad,x)|fmlookup s' (ad + (STR ''.'' + STR ''balance'')) = Some x \<and> ad \<noteq> address env. ReadL\<^sub>i\<^sub>n\<^sub>t x) + ReadL\<^sub>i\<^sub>n\<^sub>t (accessStorage (TUInt 256) (address env + (STR ''.'' + STR ''balance'')) s') + ReadL\<^sub>i\<^sub>n\<^sub>t v" by simp
        also from s1 have "\<dots> = SUMM s' - ReadL\<^sub>i\<^sub>n\<^sub>t (accessStorage (TUInt 256) (address env + (STR ''.'' + STR ''balance'')) s') + ReadL\<^sub>i\<^sub>n\<^sub>t (accessStorage (TUInt 256) (address env + (STR ''.'' + STR ''balance'')) s') + ReadL\<^sub>i\<^sub>n\<^sub>t v" by simp
        finally show ?thesis by simp
      qed
      then show ?thesis by simp
    qed
    ultimately show ?thesis by simp
  qed
  moreover have "POS s''"
  proof (rule allI[OF allI])
    fix x xa
    show "fmlookup s'' (x + (STR ''.'' + STR ''balance'')) = Some xa \<longrightarrow> 0 \<le> (\<lceil>xa\<rceil>::int)"
    proof
      assume a_lookup: "fmlookup s'' (x + (STR ''.'' + STR ''balance'')) = Some xa"
      show "0 \<le> (\<lceil>xa\<rceil>::int)"
      proof (cases "x = address env")
        case True
        then show ?thesis using s''_s' a_lookup using Read_ShowL_id v'_def a_bounds `sender e\<^sub>l = address env` `svalue e\<^sub>l = v` by auto
      next
        case False
        then have "fmlookup s' (x + (STR ''.'' + STR ''balance'')) = Some xa" using s''_s' a_lookup String_Cancel[of "address env" "(STR ''.'' + STR ''balance'')" x] by (simp split:if_split_asm)
        then show ?thesis using a_frame unfolding iv_def by simp
      qed
    qed
  qed
  ultimately show "iv (storage st0 (address e\<^sub>l)(l $$:= v')) \<lceil>bal (acc (address e\<^sub>l))\<rceil>" unfolding iv_def s''_def using `ad = address e\<^sub>l` by simp
next
  assume "ad \<noteq> address e\<^sub>l"
  moreover have "ad = address e\<^sub>l" using ffold_init_ad_same msel_ssel_expr_load_rexp_gas(4)[OF assms(2)] unfolding emptyEnv_def by simp
  ultimately show "iv (storage st0 ad) \<lceil>bal (acc ad)\<rceil>" by simp
qed

lemma adapt_withdraw:
  fixes st acc sck' mem' g''a e' l v' xe
  defines "st' \<equiv> st\<lparr>accounts := acc, stack := sck', memory := mem', gas := g''a, storage := (storage st) (address e' := (storage st (address e')) (l $$:= v'))\<rparr>"
  assumes "iv (storage st ad) (ReadL\<^sub>i\<^sub>n\<^sub>t (bal (acc ad)) - ReadL\<^sub>i\<^sub>n\<^sub>t v)"
      and "load True [] xe (ffold (init members) (emptyEnv ad cname (address env) v) (fmdom members)) emptyStore
           emptyStore emptyStore env cd (st\<lparr>gas := g'\<rparr>) g' = Normal ((e\<^sub>l, cd\<^sub>l, k\<^sub>l, m\<^sub>l), g'')"
      and "decl STR ''bal'' (Value (TUInt 256)) (Some (va, ta)) False cd\<^sub>l m\<^sub>l (storage st) (cd\<^sub>l, m\<^sub>l, k\<^sub>l, e\<^sub>l) =
           Some (cd', mem', sck', e')"
      and "expr (UINT 256 0) e' cd' (st\<lparr>accounts := acc, stack := sck', memory := mem', gas := ga\<rparr>) ga =
           Normal ((KValue vb, Value tb), g'b)"
      and "Valuetypes.convert tb t' vb = Some v'"
      and "lexp myrexp e' cd' (st\<lparr>accounts := acc, stack := sck', memory := mem', gas := g'b\<rparr>) g'b =
           Normal ((LStoreloc l, Storage (STValue t')), g''a)"
      and "expr mylval e\<^sub>l cd\<^sub>l (st\<lparr>accounts := acc, stack := k\<^sub>l, memory := m\<^sub>l,
           gas := g'' - costs keep e\<^sub>l cd\<^sub>l (st\<lparr>gas := g'', accounts := acc, stack := k\<^sub>l, memory := m\<^sub>l\<rparr>)\<rparr>)
           (g'' - costs keep e\<^sub>l cd\<^sub>l (st\<lparr>gas := g'', accounts := acc, stack := k\<^sub>l, memory := m\<^sub>l\<rparr>)) = Normal ((va, ta), g'a)"
      and "Accounts.transfer (address env) ad v (accounts st) = Some acc"
      and "expr SENDER e' cd' (st' \<lparr>gas := g\<rparr>) g =  Normal ((KValue adv, Value TAddr), g'x)"
      and adv_def: "adv \<noteq> ad"
      and bal: "expr (LVAL (L.Id STR ''bal'')) e' cd' (st'\<lparr>gas := g''b\<rparr>) g''b = Normal ((KValue lv, Value t), g''')"
      and con: "Valuetypes.convert t (TUInt 256) lv = Some lv'"
    shows "iv (storage st' ad) (ReadL\<^sub>i\<^sub>n\<^sub>t (bal (accounts st' ad)) - (ReadL\<^sub>i\<^sub>n\<^sub>t lv'))"
proof -
  define acca where "acca = accounts st' ad"
  define s' where "s' = storage st (address e')"
  define s'a where "s'a = storage st' ad"
  moreover have "address e' = ad"
  proof -
    have "address e' = address e\<^sub>l" using decl_env[OF assms(4)] by simp
    also have "address e\<^sub>l = address (ffold (init members) (emptyEnv ad cname (address env) v) (fmdom members))" using msel_ssel_expr_load_rexp_gas(4)[OF assms(3)] by simp
    also have "\<dots> = ad" unfolding emptyEnv_def using ffold_init_ad_same by simp
    finally show ?thesis .
  qed
  ultimately have s'a_def: "s'a = fmupd l v' s'" unfolding s'_def st'_def by simp

  have "sender e' = address env"
  proof -
    have "sender e' = sender e\<^sub>l" using decl_env[OF assms(4)] by simp
    also have "sender e\<^sub>l = sender (ffold (init members) (emptyEnv ad cname (address env) v) (fmdom members))" using msel_ssel_expr_load_rexp_gas(4)[OF assms(3)] by simp
    also have "\<dots> = address env" unfolding emptyEnv_def using ffold_init_ad_same by simp
    finally show ?thesis .
  qed

  have "iv s'a (\<lceil>bal acca\<rceil> - \<lceil>lv'\<rceil>)" unfolding iv_def
  proof intros
    have "SUMM s' \<le> \<lceil>bal acca\<rceil>"
    proof -
      from `address e' = ad` have "iv s' (ReadL\<^sub>i\<^sub>n\<^sub>t (bal acca) - ReadL\<^sub>i\<^sub>n\<^sub>t v)" using assms(2,5) unfolding s'_def st'_def acca_def by simp
      then have "SUMM s' \<le> \<lceil>bal (acca)\<rceil> - \<lceil>v\<rceil>" unfolding iv_def by simp
      moreover have "ReadL\<^sub>i\<^sub>n\<^sub>t v \<ge> 0" using transfer_val1[OF assms(9)] by simp
      ultimately show ?thesis by simp
    qed
    moreover have "SUMM s'a = SUMM s' - ReadL\<^sub>i\<^sub>n\<^sub>t lv'"
    proof -
      from summ_eq_sum have "SUMM s'a = (\<Sum>(ad,x)|fmlookup s'a (ad + (STR ''.'' + STR ''balance'')) = Some x \<and> ad \<noteq> sender e'. ReadL\<^sub>i\<^sub>n\<^sub>t x) + ReadL\<^sub>i\<^sub>n\<^sub>t (accessStorage (TUInt 256) (sender e' + (STR ''.'' + STR ''balance'')) s'a)" by simp
      moreover from summ_eq_sum have "SUMM s' = (\<Sum>(ad,x)|fmlookup s' (ad + (STR ''.'' + STR ''balance'')) = Some x \<and> ad \<noteq> sender e'. ReadL\<^sub>i\<^sub>n\<^sub>t x) + ReadL\<^sub>i\<^sub>n\<^sub>t (accessStorage (TUInt 256) (sender e' + (STR ''.'' + STR ''balance'')) s')" by simp
      moreover from s'a_def lexp_myrexp_decl(1)[OF assms(3,4) assms(7)] have " s'a = s'((sender e' + (STR ''.'' + STR ''balance''))$$:= v')" using `sender e' = address env` by simp
      with sum_eq_update have "(\<Sum>(ad,x)|fmlookup s'a (ad + (STR ''.'' + STR ''balance'')) = Some x \<and> ad \<noteq> sender e'. ReadL\<^sub>i\<^sub>n\<^sub>t x) = (\<Sum>(ad,x)|fmlookup s' (ad + (STR ''.'' + STR ''balance'')) = Some x \<and> ad \<noteq> sender e'. ReadL\<^sub>i\<^sub>n\<^sub>t x)"  by simp
      moreover have "ReadL\<^sub>i\<^sub>n\<^sub>t (accessStorage (TUInt 256) (sender e' + (STR ''.'' + STR ''balance'')) s'a) = ReadL\<^sub>i\<^sub>n\<^sub>t (accessStorage (TUInt 256) (sender e' + (STR ''.'' + STR ''balance'')) s') - ReadL\<^sub>i\<^sub>n\<^sub>t lv'"
      proof -
        have "ReadL\<^sub>i\<^sub>n\<^sub>t (accessStorage (TUInt 256) (sender e' + (STR ''.'' + STR ''balance'')) s') = ReadL\<^sub>i\<^sub>n\<^sub>t lv'"
        proof -
          from expr_balance[OF assms(3) assms(8)] have "va= KValue (accessStorage (TUInt 256) (address env + (STR ''.'' + STR ''balance'')) s')" and "ta = Value (TUInt 256)" using `address e' = ad` unfolding s'_def by simp+
          then have "(sck',e') =  astack STR ''bal'' (Value (TUInt 256)) (KValue (accessStorage (TUInt 256) (address env + (STR ''.'' + STR ''balance'')) s')) (k\<^sub>l, e\<^sub>l)" using decl.simps(2) assms(4) by simp
          then have "ReadL\<^sub>i\<^sub>n\<^sub>t (accessStorage (TUInt 256) (address env + (STR ''.'' + STR ''balance'')) s') = ReadL\<^sub>i\<^sub>n\<^sub>t lv" and "t = TUInt 256" using expr_bal bal unfolding s'_def st'_def by auto
          moreover from `t = TUInt 256` have "lv = lv'" using con by simp
          ultimately show ?thesis using `sender e' = address env` by simp
        qed
        moreover have "ReadL\<^sub>i\<^sub>n\<^sub>t (accessStorage (TUInt 256) (sender e' + (STR ''.'' + STR ''balance'')) s'a) = ReadL\<^sub>i\<^sub>n\<^sub>t (ShowL\<^sub>i\<^sub>n\<^sub>t 0)"
        proof -
          have "v' = ShowL\<^sub>i\<^sub>n\<^sub>t 0"
          proof -
            have "vb = createUInt 256 0" and "tb=TUInt 256" using assms(5) by (simp add: expr.simps load.simps split:if_split_asm)+
            moreover have "t'=TUInt 256" using lexp_myrexp_decl(2)[OF assms(3,4) assms(7)] by simp
            ultimately show ?thesis using assms(6) by (simp add: createUInt_id)
          qed
          moreover have "l= (sender e' + (STR ''.'' + STR ''balance''))" using lexp_myrexp_decl(1)[OF assms(3,4) assms(7)] `sender e' = address env` by simp
          ultimately show ?thesis using s'a_def accessStorage_def by simp
        qed
        ultimately show ?thesis using Read_ShowL_id by simp
      qed
      ultimately show ?thesis by simp
    qed
    ultimately show "SUMM s'a \<le> \<lceil>bal acca\<rceil> - \<lceil>lv'\<rceil>" by simp
  next
    fix ad' x
    assume *: "fmlookup s'a (ad' + (STR ''.'' + STR ''balance'')) = Some x"
    show "0 \<le> ReadL\<^sub>i\<^sub>n\<^sub>t x"
    proof (cases "ad' = sender e'")
      case True
      moreover have "v' = ShowL\<^sub>i\<^sub>n\<^sub>t 0"
      proof -
        have "vb = createUInt 256 0" and "tb=TUInt 256" using assms(5) by (simp add:expr.simps split:if_split_asm)+
        moreover have "t'=TUInt 256" using lexp_myrexp_decl(2)[OF assms(3,4) assms(7)] by simp
        ultimately show ?thesis using assms(6) by (simp add: createUInt_id)
      qed
      moreover have "l= (sender e' + (STR ''.'' + STR ''balance''))" using lexp_myrexp_decl(1)[OF assms(3,4) assms(7)] `sender e' = address env` by simp
      ultimately show ?thesis using Read_ShowL_id s'a_def * by auto
    next
      case False
      moreover from `address e' = ad` have "iv s' (ReadL\<^sub>i\<^sub>n\<^sub>t (bal (acc ad)) - ReadL\<^sub>i\<^sub>n\<^sub>t v)" using assms(2) unfolding s'_def by simp
      then have "POS s'" unfolding iv_def by simp
      moreover have "l= (sender e' + (STR ''.'' + STR ''balance''))" using lexp_myrexp_decl(1)[OF assms(3,4) assms(7)] `sender e' = address env` by simp
      ultimately show ?thesis using s'a_def * String_Cancel by (auto split:if_split_asm)
    qed
  qed
  then show ?thesis unfolding s'a_def s'_def acca_def st'_def `address e' = ad` by simp
qed

lemma wp_deposit[external]:
  assumes "address ev \<noteq> ad"
      and "expr adex ev cd (st\<lparr>gas := gas st0 - costs (EXTERNAL adex mid xe val) ev cd st0\<rparr>) (gas st0 - costs (EXTERNAL adex mid xe val) ev cd st0) = Normal ((KValue ad, Value TAddr), g)"
      and "expr val ev cd (st0\<lparr>gas := g\<rparr>) g = Normal ((KValue v, Value t), g')"
      and "Valuetypes.convert t (TUInt 256) v = Some v'"
      and "load True [] xe (ffold (init members) (emptyEnv ad cname (address ev) v') (fmdom members)) emptyStore emptyStore emptyStore ev cd (st0\<lparr>gas := g'\<rparr>) g' = Normal ((e\<^sub>l, cd\<^sub>l, k\<^sub>l, m\<^sub>l), g'')"
      and "Accounts.transfer (address ev) ad v' (accounts st0) = Some acc"
      and "iv (storage st0 ad) (ReadL\<^sub>i\<^sub>n\<^sub>t (bal (acc ad)) - ReadL\<^sub>i\<^sub>n\<^sub>t v')"
    shows "wpS (stmt (ASSIGN myrexp (PLUS mylval VALUE)) e\<^sub>l cd\<^sub>l)
           (\<lambda>st. (iv (storage st ad) (ReadL\<^sub>i\<^sub>n\<^sub>t (bal (accounts st ad))))) (\<lambda>e. e = Gas \<or> e = Err)
           (st0\<lparr>gas := g'', accounts := acc, stack := k\<^sub>l, memory := m\<^sub>l\<rparr>)"
  apply (vcg_assign expr_rule: expr_plus[OF assms(5)] lexp_rule: lexp_myrexp(1)[OF assms(5)])
  by (simp add: adapt_deposit[OF assms(1,5,6,7)])

lemma wptransfer:
  fixes st0 acc sck' mem' g''a e' l v'
  defines "st' \<equiv> st0\<lparr>accounts := acc, stack := sck', memory := mem', gas := g''a,
        storage := (storage st0)(address e' := storage st0 (address e')(l $$:= v'))\<rparr>"
  assumes "Pfe ad iv st'"
      and "address ev \<noteq> ad"
      and "g'' \<le> gas st"
      and "type (acc ad) = Some (Contract cname)"
      and "expr adex ev cd (st0\<lparr>gas := gas st0 - costs (EXTERNAL adex mid xe val) ev cd st0\<rparr>)
           (gas st0 - costs (EXTERNAL adex mid xe val) ev cd st0) =
           Normal ((KValue ad, Value TAddr), g)"
      and "expr val ev cd (st0\<lparr>gas := g\<rparr>) g = Normal ((KValue gv, Value gt), g')"
      and "Valuetypes.convert gt (TUInt 256) gv = Some gv'"
      and "load True [] xe (ffold (init members) (emptyEnv ad cname (address ev) gv') (fmdom members)) emptyStore
           emptyStore emptyStore ev cd (st0\<lparr>gas := g'\<rparr>) g' =
          Normal ((e\<^sub>l, cd\<^sub>l, k\<^sub>l, m\<^sub>l), g'')"
      and "Accounts.transfer (address ev) ad gv' (accounts st0) = Some acc"
      and "iv (storage st0 ad) (ReadL\<^sub>i\<^sub>n\<^sub>t (bal (acc ad)) - ReadL\<^sub>i\<^sub>n\<^sub>t gv')"
      and "decl STR ''bal'' (Value (TUInt 256)) (Some (v, t)) False cd\<^sub>l m\<^sub>l (storage st0)
           (cd\<^sub>l, m\<^sub>l, k\<^sub>l, e\<^sub>l) =  Some (cd', mem', sck', e')"
      and "Valuetypes.convert ta t' va = Some v'"
      and "lexp myrexp e' cd' (st0\<lparr>accounts := acc, stack := sck', memory := mem', gas := g'a\<rparr>) g'a =
           Normal ((LStoreloc l, Storage (STValue t')), g''a)"
      and "expr mylval e\<^sub>l cd\<^sub>l (st0\<lparr>accounts := acc, stack := k\<^sub>l, memory := m\<^sub>l,
           gas := g'' - costs (BLOCK ((STR ''bal'', Value (TUInt 256)), Some mylval)
           (COMP (ASSIGN myrexp (UINT 256 0)) Reentrancy.transfer)) e\<^sub>l cd\<^sub>l (st0\<lparr>gas := g'', accounts := acc, stack := k\<^sub>l, memory := m\<^sub>l\<rparr>)\<rparr>)
           (g'' - costs (BLOCK ((STR ''bal'', Value (TUInt 256)), Some mylval) (COMP (ASSIGN myrexp (UINT 256 0)) Reentrancy.transfer)) e\<^sub>l
           cd\<^sub>l (st0\<lparr>gas := g'', accounts := acc, stack := k\<^sub>l, memory := m\<^sub>l\<rparr>)) =
           Normal ((v, t), g''')"
      and "expr (UINT 256 0) e' cd' (st0\<lparr>accounts := acc, stack := sck', memory := mem', gas := ga\<rparr>) ga = Normal ((KValue va, Value ta), g'a)"
    shows "wpS (stmt Reentrancy.transfer e' cd') (\<lambda>st. iv (storage st ad) (ReadL\<^sub>i\<^sub>n\<^sub>t (bal (accounts st ad))))
        (\<lambda>e. e = Gas \<or> e = Err) st'"
proof (rule meta_eq_to_obj_eq[THEN iffD1, OF Pfe_def assms(2),rule_format], (rule conjI; (rule conjI)?))
  show "address e' = ad"
  proof -
    have "address e' = address e\<^sub>l" using decl_env[OF assms(12)] by simp
    also have "address e\<^sub>l = address (ffold (init members) (emptyEnv ad cname (address ev) gv') (fmdom members))" using msel_ssel_expr_load_rexp_gas(4)[OF assms(9)] by simp
    also have "\<dots> = ad" unfolding emptyEnv_def using ffold_init_ad_same by simp
    finally show ?thesis .
  qed
next
  show "\<forall>adv g. expr SENDER e' cd' (st'\<lparr>gas := gas st' - costs Reentrancy.transfer e' cd' st'\<rparr>) (gas st' - costs Reentrancy.transfer e' cd' st') = Normal ((KValue adv, Value TAddr), g)
    \<longrightarrow> adv \<noteq> ad"
  proof (intros)
    fix adv g
    assume "expr SENDER e' cd' (st'\<lparr>gas := gas st' - costs Reentrancy.transfer e' cd' st'\<rparr>) (gas st' - costs Reentrancy.transfer e' cd' st') = Normal ((KValue adv, Value TAddr), g)"
    moreover have "sender e' \<noteq> ad"
    proof -
      have "sender e' = sender e\<^sub>l" using decl_env[OF assms(12)] by simp
      also have "sender e\<^sub>l = sender (ffold (init members) (emptyEnv ad cname (address ev) gv') (fmdom members))" using msel_ssel_expr_load_rexp_gas(4)[OF assms(9)] by simp
      also have "\<dots> = address ev" unfolding emptyEnv_def using ffold_init_ad_same by simp
      finally show ?thesis using assms(3) by simp
    qed
    ultimately show "adv \<noteq> ad" by (simp add:expr.simps split:result.split_asm if_split_asm prod.split_asm)
  qed
next
  show "\<forall>adv g v t g' v'.
       local.expr SENDER e' cd' (st'\<lparr>gas := gas st' - costs Reentrancy.transfer e' cd' st'\<rparr>)
        (gas st' - costs Reentrancy.transfer e' cd' st') = Normal ((KValue adv, Value TAddr), g) \<and>
       adv \<noteq> ad \<and>
       local.expr (LVAL (L.Id STR ''bal'')) e' cd' (st'\<lparr>gas := g\<rparr>) g = Normal ((KValue v, Value t), g') \<and>
       Valuetypes.convert t (TUInt 256) v = Some v' \<longrightarrow>
       iv (storage st' ad) (\<lceil>bal (accounts st' ad)\<rceil> - ReadL\<^sub>i\<^sub>n\<^sub>t v')"
  proof elims
     fix adv lg lv lt lg' lv'
  assume a1:"expr SENDER e' cd' (st'\<lparr>gas := gas st' - costs Reentrancy.transfer e' cd' st'\<rparr>) (gas st' - costs Reentrancy.transfer e' cd' st') =
          Normal ((KValue adv, Value TAddr), lg)"
     and adv_def: "adv \<noteq> ad"
     and bal: "expr (LVAL (L.Id STR ''bal'')) e' cd' (st'\<lparr>gas := lg\<rparr>) lg = Normal ((KValue lv, Value lt), lg')"
     and con: "Valuetypes.convert lt (TUInt 256) lv = Some lv'"
    show "iv (storage st' ad) (\<lceil>bal (accounts st' ad)\<rceil> - ReadL\<^sub>i\<^sub>n\<^sub>t lv')"
     using adapt_withdraw[where ?acc=acc, OF assms(11) load_empty_par[OF assms(9)] assms(12,16,13,14,15,10) _ adv_def _] a1 bal con unfolding st'_def by simp
  qed
qed

lemma wp_withdraw[external]:
  assumes "\<And>st'. gas st' \<le> gas st \<and> type (accounts st' ad) = Some (Contract cname) \<Longrightarrow> Pe ad iv st' \<and> Pi ad (\<lambda>_ _. True) (\<lambda>_ _. True) st' \<and> Pfi ad (\<lambda>_. True) (\<lambda>_. True) st' \<and> Pfe ad iv st'"
      and "address ev \<noteq> ad"
      and "g'' \<le> gas st"
      and "type (acc ad) = Some (Contract cname)"
      and "expr adex ev cd (st0\<lparr>gas := gas st0 - costs (EXTERNAL adex mid xe val) ev cd st0\<rparr>)
           (gas st0 - costs (EXTERNAL adex mid xe val) ev cd st0) = Normal ((KValue ad, Value TAddr), g)"
      and "expr val ev cd (st0\<lparr>gas := g\<rparr>) g = Normal ((KValue v, Value t), g')"
      and "Valuetypes.convert t (TUInt 256) v = Some v'"
      and "load True [] xe (ffold (init members) (emptyEnv ad cname (address ev) v') (fmdom members))
           emptyStore emptyStore emptyStore ev cd (st0\<lparr>gas := g'\<rparr>) g' = Normal ((e\<^sub>l, cd\<^sub>l, k\<^sub>l, m\<^sub>l), g'')"
      and "Accounts.transfer (address ev) ad v' (accounts st0) = Some acc"
      and "iv (storage st0 ad) (ReadL\<^sub>i\<^sub>n\<^sub>t (bal (acc ad)) - ReadL\<^sub>i\<^sub>n\<^sub>t v')"
    shows "wpS (stmt keep e\<^sub>l cd\<^sub>l)
           (\<lambda>st. iv (storage st ad) (ReadL\<^sub>i\<^sub>n\<^sub>t (bal (accounts st ad)))) (\<lambda>e. e = Gas \<or> e = Err)
           (st0\<lparr>gas := g'', accounts := acc, stack := k\<^sub>l, memory := m\<^sub>l\<rparr>)"
  apply vcg_block_some
  apply vcg_comp
  apply (vcg_assign expr_rule: expr_0[OF assms(8)] lexp_rule: lexp_myrexp_decl[OF assms(8)])
  apply (rule wptransfer[OF _ assms(2-10)])
  apply (rule_tac assms(1)[THEN conjunct2,THEN conjunct2,THEN conjunct2])
    using assms(3,4) by simp

lemma wp_fallback:
  assumes "Accounts.transfer (address ev) ad v (accounts st0) = Some acca"
      and "iv (storage st0 ad) (ReadL\<^sub>i\<^sub>n\<^sub>t (bal (acca ad)) - ReadL\<^sub>i\<^sub>n\<^sub>t v)"
    shows "wpS (stmt SKIP (ffold (init members) (emptyEnv ad cname (address ev) vc) (fmdom members)) emptyStore)
          (\<lambda>st. iv (storage st ad) (ReadL\<^sub>i\<^sub>n\<^sub>t (bal (accounts st ad)))) (\<lambda>e. e = Gas \<or> e = Err)
          (st0\<lparr>gas := g'c, accounts := acca, stack := emptyStore, memory := emptyStore\<rparr>)"
  apply vcg_skip
  using weaken[where ?acc=acca, OF assms(2) transfer_val1[OF assms(1)]] by auto

lemma wp_construct:
  assumes "Accounts.transfer (address ev) (hash (address ev) \<lfloor>contracts (accounts st (address ev))\<rfloor>) v
        ((accounts st) (hash (address ev) \<lfloor>contracts (accounts st (address ev))\<rfloor> := \<lparr>bal = ShowL\<^sub>i\<^sub>n\<^sub>t 0, type = Some (Contract i), contracts = 0\<rparr>)) =
       Some acc"
    shows "iv fmempty \<lceil>bal (acc (hash (address ev) \<lfloor>contracts (accounts st (address ev))\<rfloor>))\<rceil>"
proof -
  define adv where "adv = (hash (address ev) \<lfloor>contracts (accounts st (address ev))\<rfloor>)"
  moreover have "ReadL\<^sub>i\<^sub>n\<^sub>t (bal (((accounts st) (adv := \<lparr>bal = ShowL\<^sub>i\<^sub>n\<^sub>t 0, type = Some (Contract i), contracts = 0\<rparr>)) adv)) = 0" using Read_ShowL_id[of 0] by simp
  ultimately have "ReadL\<^sub>i\<^sub>n\<^sub>t (bal (acc (hash (address ev) \<lfloor>contracts (accounts st (address ev))\<rfloor>))) \<ge> 0" using transfer_mono[OF assms(1)] by simp
  then show ?thesis unfolding iv_def by simp
qed

lemma wp_true[external]:
  assumes "E Gas"
      and "E Err"
  shows "wpS (stmt f e cd) (\<lambda>st. True) E st"
  unfolding wpS_def wp_def
proof ((split result.split, (split prod.split)?); rule conjI; (rule allI)+; (rule impI)+)
  fix x1 x1a s
  assume "x1 = (x1a, s)" and "stmt f e cd st = Normal x1"
  then show "gas s \<le> gas st \<and> True" using stmt_gas by simp
next
  fix x2
  assume "stmt f e cd st = Exception x2"
  show "E x2" using assms Ex.nchotomy by metis
qed

subsubsection\<open>Final results\<close>

interpretation vcg:VCG costs\<^sub>e ep costs cname members const fb "\<lambda>_. True" "\<lambda>_. True" "\<lambda>_ _. True" "\<lambda>_ _. True"
by (simp add: VCG.intro Calculus_axioms)

lemma safe_external: "Qe ad iv (st::State)"
  apply (external cases: cases_ext)
  apply (rule wp_deposit;assumption)
  apply vcg_block_some
  apply vcg_comp
  apply (vcg_assign expr_rule: expr_0 lexp_rule: lexp_myrexp_decl)
  apply (vcg.vcg_transfer_ext ad fallback_int: wp_true fallback_ext: wp_fallback cases_ext:cases_ext cases_int:cases_fb cases_fb:cases_int invariant:adapt_withdraw)
  done

lemma safe_fallback: "Qfe ad iv st"
  apply (fallback cases: cases_fb)
  apply (rule wp_fallback; assumption)
  done

lemma safe_constructor: "constructor iv"
  apply (constructor cases: cases_cons)
  apply vcg_skip
  apply (simp add:wp_construct)
  done

theorem safe:
  assumes "\<forall>ad. address ev \<noteq> ad \<and> type (accounts st ad) = Some (Contract cname) \<longrightarrow> iv (storage st ad) (ReadL\<^sub>i\<^sub>n\<^sub>t (bal (accounts st ad)))"
    shows "\<forall>(st'::State) ad. stmt f ev cd st = Normal ((), st') \<and> type (accounts st' ad) = Some (Contract cname) \<and> address ev \<noteq> ad
            \<longrightarrow> iv (storage st' ad) (ReadL\<^sub>i\<^sub>n\<^sub>t (bal (accounts st' ad)))"
  apply (rule invariant) using assms safe_external safe_fallback safe_constructor by auto

end

end
