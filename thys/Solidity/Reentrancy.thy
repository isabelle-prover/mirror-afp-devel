section\<open>Reentrancy\<close>

text \<open>
  In the following we use our calculus to verify a contract implementing a simple token.
  The contract is defined by definition *bank* and consist of one state variable and two methods:
  \<^item> The state variable "balance" is a Mapping which assigns a balance to each address.
  \<^item> Method "deposit" allows to send money to the contract which is then added to the sender's balance.
  \<^item> Method "withdraw" allows to withdraw the callers balance.
\<close>

text \<open>
  We then verify that the following invariant (defined by *BANK*) is preserved by both methods:
  The difference between
  \<^item> the Contracts own account-balance and
  \<^item> the sum of all the balances kept in the Contracts state variable
  is larger than a certain threshold.
\<close>

text \<open>
  There are two things to note here:
  First, Solidity implicitly triggers the call of a so-called fallback method whenever we transfer money to a contract.
  In particular if another contract calls "withdraw", this triggers an implicit call to the callee's fallback method.
  This functionality was exploited in the infamous DAO attack which we demonstrate it in terms of an example later on.
  Since we do not know all potential Contracts which call "withdraw", we need to verify our invariant for all possible Solidity programs.
\<close>

text \<open>
  The second thing to note is that we were not able to verify that the difference is indeed constant.
  During verification it turned out that this is not the case since in the fallback method a contract could just send us additional money without calling "deposit".
  In such a case the difference would change. In particular it would grow. However, we were able to verify that the difference does never shrink which is what we actually want to ensure.
\<close>

theory Reentrancy
  imports Weakest_Precondition Solidity_Evaluator
begin

subsection\<open>Example of Re-entrancy\<close>

definition "example_env \<equiv>
              loadProc (STR ''Attacker'')
                ([],
                ([], SKIP),
                 ITE (LESS (BALANCE THIS) (UINT b256 125))
                   (EXTERNAL (ADDRESS (STR ''BankAddress'')) (STR ''withdraw'') [] (UINT b256 0))
                   SKIP)
              (loadProc (STR ''Bank'')
                ([(STR ''balance'', Var (STMap TAddr (STValue (TUInt b256)))),
                (STR ''deposit'', Method ([], True,
                  ASSIGN
                    (Ref (STR ''balance'') [SENDER])
                    (PLUS (LVAL (Ref (STR ''balance'') [SENDER])) VALUE))),
                (STR ''withdraw'', Method ([], True,
                  ITE (LESS (UINT b256 0) (LVAL (Ref (STR ''balance'') [SENDER])))
                    (COMP
                      (TRANSFER SENDER (LVAL (Ref (STR ''balance'') [SENDER])))
                      (ASSIGN (Ref (STR ''balance'') [SENDER]) (UINT b256 0)))
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
            (EXTERNAL (ADDRESS (STR ''BankAddress'')) (STR ''deposit'') [] (UINT b256 10))
            (EXTERNAL (ADDRESS (STR ''BankAddress'')) (STR ''withdraw'') [] (UINT b256 0)))
          (STR ''AttackerAddress'')
          (STR ''Attacker'')
          (STR '''')
          (STR ''0'')
          [(STR ''BankAddress'', STR ''100'', atype.Contract (STR ''Bank''), 0), (STR ''AttackerAddress'', STR ''100'', atype.Contract (STR ''Attacker''), 0)]
          []
  = STR ''BankAddress: balance==70 - Bank(balance[AttackerAddress]==0\<newline>)\<newline>AttackerAddress: balance==130 - Attacker()''"
  by eval

subsection\<open>Definition of contract\<close>

abbreviation myrexp::l
  where "myrexp \<equiv> Ref (STR ''balance'') [SENDER]"

abbreviation mylval::e
  where "mylval \<equiv> LVAL myrexp"

abbreviation assign::s
  where "assign \<equiv> ASSIGN myrexp (UINT b256 0)"

abbreviation transfer::s
  where "transfer \<equiv> TRANSFER SENDER (LVAL (Id (STR ''bal'')))"

abbreviation comp::s
  where "comp \<equiv> COMP assign transfer"

abbreviation keep::s
  where "keep \<equiv> BLOCK (STR ''bal'', Value (TUInt b256), Some mylval) comp"

abbreviation deposit::s
  where "deposit \<equiv> ASSIGN myrexp (PLUS mylval VALUE)"

abbreviation "banklist \<equiv> [
          (STR ''balance'', Var (STMap TAddr (STValue (TUInt b256)))),
          (STR ''deposit'', Method ([], True, deposit)),
          (STR ''withdraw'', Method ([], True, keep))]"

definition bank::"(Identifier, member) fmap"
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

lemma mwithdraw[simp]:
  "members $$ STR ''withdraw'' = Some (Method ([], True, keep))"
  using r1 unfolding bank_def by simp

lemma mdeposit[simp]:
  "members $$ STR ''deposit'' = Some (Method ([], True, deposit))"
  using r1 unfolding bank_def by simp

subsubsection\<open>Variable lemma\<close>

lemma balance[simp]:
  "members $$ (STR ''balance'') = Some (Var (STMap TAddr (STValue (TUInt b256))))"
  using r1 bank_def fmlookup_of_list[of "[(STR ''balance'', Var (STMap TAddr (STValue (TUInt b256)))), (STR ''deposit'', Method ([], True, ASSIGN myrexp (PLUS mylval VALUE))),
      (STR ''withdraw'', Method ([], True, BLOCK (STR ''bal'', Value (TUInt b256), Some mylval) (COMP (ASSIGN myrexp (UINT b256 0)) Reentrancy.transfer)))]"] by simp

lemma balAcc:
  "members $$ (STR ''bal'') = None"
  using r1 bank_def fmlookup_of_list[of "[(STR ''balance'', Var (STMap TAddr (STValue (TUInt b256)))), (STR ''deposit'', Method ([], True, ASSIGN myrexp (PLUS mylval VALUE))),
      (STR ''withdraw'', Method ([], True, BLOCK (STR ''bal'', Value (TUInt b256), Some mylval) (COMP (ASSIGN myrexp (UINT b256 0)) Reentrancy.transfer)))]"] by simp


subsubsection\<open>Case lemmas\<close>
text \<open>
  These lemmas are required by @{term vcg_transfer}.
\<close>
lemma cases_ext: 
  assumes "members $$ mid = Some (Method (fp,True,f))"
      and "fp = [] \<Longrightarrow> f = deposit \<Longrightarrow> P"
      and "fp = [] \<Longrightarrow> f = keep \<Longrightarrow> P"
    shows "P"
proof -
  from assms(1) r1 consider (withdraw) "mid = STR ''withdraw''" | (deposit) "mid = STR ''deposit''" using bank_def fmap_of_list_SomeD[of "[(STR ''balance'', Var (STMap TAddr (STValue (TUInt b256)))), (STR ''deposit'', Method ([], True, deposit)), (STR ''withdraw'', Method ([], True, keep))]"] by auto
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
    shows "P"
  using assms r1 bank_def fmap_of_list_SomeD[of "[(STR ''balance'', Var (STMap TAddr (STValue (TUInt b256)))), (STR ''deposit'', Method ([], True, deposit)), (STR ''withdraw'', Method ([], True, keep))]"] by auto

lemma cases_fb: 
  assumes "fb = SKIP \<Longrightarrow> P"
  shows "P"
using assms bank_def r2 by simp

lemma cases_cons:
  assumes "fst const = [] \<Longrightarrow> snd const = SKIP \<Longrightarrow> P"
  shows "P"
using assms bank_def r3 by simp

subsubsection\<open>Definition of Invariant\<close>

abbreviation "SUMM s \<equiv> \<Sum>(ad,x)|fmlookup s (ad + (STR ''.'' + STR ''balance'')) = Some x. ReadL\<^sub>i\<^sub>n\<^sub>t x"

abbreviation "POS s \<equiv> \<forall>ad x. fmlookup s (ad + (STR ''.'' + STR ''balance'')) = Some x \<longrightarrow> ReadL\<^sub>i\<^sub>n\<^sub>t x \<ge> 0"

definition "iv s a \<equiv> a \<ge> SUMM s \<and> POS s"

lemma weaken:
  assumes "iv (Storage st ad) (ReadL\<^sub>i\<^sub>n\<^sub>t (Bal (acc ad)) - ReadL\<^sub>i\<^sub>n\<^sub>t v)"
      and "ReadL\<^sub>i\<^sub>n\<^sub>t v \<ge>0"
    shows "iv (Storage st ad) (ReadL\<^sub>i\<^sub>n\<^sub>t (Bal (acc ad)))"
using assms unfolding iv_def by simp

subsubsection\<open>Additional lemmas\<close>

lemma expr_0:
  assumes "expr (UINT b256 0) ev0 cd0 st0 g0 = Normal ((rv, rt),g''a)"
    shows "is_KValue rv" and "is_Value rt"
  using assms by (auto simp add:expr.simps split:if_split_asm)

lemma load_empty_par:
  assumes "load True [] xe (ffold (init members) (emptyEnv ad cname (Address env) v) (fmdom members)) emptyTypedStore emptyStore emptyTypedStore env cd (st\<lparr>Gas := g1\<rparr>) g1 = Normal ((e\<^sub>l, cd\<^sub>l, k\<^sub>l, m\<^sub>l), g1')"
    shows "load True [] [] (ffold (init members) (emptyEnv ad cname (Address env) v) (fmdom members)) emptyTypedStore emptyStore emptyTypedStore env cd (st\<lparr>Gas := g1\<rparr>) g1 = Normal ((e\<^sub>l, cd\<^sub>l, k\<^sub>l, m\<^sub>l), g1')"
proof -
  have "xe=[]"
  proof (rule ccontr)
    assume "\<not> xe=[]"
    then obtain x and xa where "xe=x # xa" by (meson list.exhaust)
    then have "load True [] xe (ffold (init members) (emptyEnv ad cname (Address env) v) (fmdom members)) emptyTypedStore emptyStore emptyTypedStore env cd (st\<lparr>Gas := g1\<rparr>) g1 = throw Err g1" by (simp add:load.simps)
    with assms show False by simp
  qed
  then show ?thesis using assms(1) by simp
qed

lemma lexp_myrexp_decl:
  assumes "load True [] xe (ffold (init members) (emptyEnv ad cname (Address env) v) (fmdom members)) emptyTypedStore emptyStore emptyTypedStore env cd (st0\<lparr>Gas := g1\<rparr>) g1 = Normal ((e\<^sub>l, cd\<^sub>l, k\<^sub>l, m\<^sub>l), g1')"
      and "decl STR ''bal'' (Value (TUInt b256)) (Some (lv, lt)) False cd\<^sub>l m\<^sub>l (Storage st0 (Address e\<^sub>l)) (cd\<^sub>l, m\<^sub>l, k\<^sub>l, e\<^sub>l) =  Some (cd', mem', sck', e')"
      and "lexp myrexp e' cd' (st0\<lparr>Accounts := acc, Stack := sck', Memory := mem', Gas := g'a\<rparr>) g'a = Normal ((rv,rt), g''a)"
    shows "rv= LStoreloc (Address env + (STR ''.'' + STR ''balance''))" and "rt=type.Storage (STValue (TUInt b256))"
proof -
  have "fmlookup (Denvalue (ffold (init members) (emptyEnv ad cname (Address env) v) (fmdom members))) (STR ''balance'') = Some (type.Storage (STMap TAddr (STValue (TUInt b256))), Storeloc (STR ''balance''))" unfolding emptyEnv_def using ffold_init_fmdom by simp
  moreover have el_def: "e\<^sub>l = (ffold (init members) (emptyEnv ad cname (Address env) v) (fmdom members))" using load_empty_par[OF assms(1)] by (simp add:load.simps)
  ultimately have "fmlookup (Denvalue e\<^sub>l) (STR ''balance'') = Some (type.Storage (STMap TAddr (STValue (TUInt b256))), Storeloc (STR ''balance''))" using assms by auto
  then have *: "fmlookup (Denvalue e') (STR ''balance'') = Some (type.Storage (STMap TAddr (STValue (TUInt b256))), Storeloc (STR ''balance''))" 
    using decl_env[OF assms(2)] 
    using assms(2) decl_env_monotonic by presburger

  moreover obtain g'' where "ssel (STMap TAddr (STValue (TUInt b256))) (STR ''balance'') [SENDER] e' cd' (st0\<lparr>Accounts := acc, Stack := sck', Memory := mem', Gas := g'a\<rparr>) g'a = Normal (((Address env) + (STR ''.'' + STR ''balance''), STValue (TUInt b256)), g'')"
  proof -
    have "g'a > costs\<^sub>e SENDER e' cd' (st0\<lparr>Accounts := acc, Stack := sck', Memory := mem', Gas := g'a\<rparr>)" using assms(3) * by (simp add:expr.simps ssel.simps lexp.simps split:if_split_asm)
    then obtain g'' where "expr SENDER e' cd' (st0\<lparr>Accounts := acc, Stack := sck', Memory := mem', Gas := g'a\<rparr>) g'a = Normal ((KValue (Sender e'), Value TAddr), g'')" by (simp add:expr.simps)
    moreover have "Sender e\<^sub>l = Address env" using el_def ffold_init_ad_same[of members "(emptyEnv ad cname (Address env) v)" "fmdom members" e\<^sub>l] unfolding emptyEnv_def by simp
    then have "Sender e' = Address env" using decl_env[OF assms(2)] by simp
    ultimately show ?thesis using that hash_def by (simp add:ssel.simps)
  qed
  ultimately show "rv= LStoreloc (Address env + (STR ''.'' + STR ''balance''))" and "rt=type.Storage (STValue (TUInt b256))" using assms(3) by (simp add:lexp.simps)+
qed

lemma lexp_myrexp_decl2:
  assumes "load True [] xe (ffold (init members) (emptyEnv ad cname (Address env) v) (fmdom members)) emptyTypedStore emptyStore emptyTypedStore env cd (st0\<lparr>Gas := g1\<rparr>) g1 = Normal ((e\<^sub>l, cd\<^sub>l, k\<^sub>l, m\<^sub>l), g1')"
      and "decl STR ''bal'' (Value (TUInt b256)) (Some (lv, lt)) False cd\<^sub>l m\<^sub>l (Storage st0 (Address e\<^sub>l)) (cd\<^sub>l, m\<^sub>l, k\<^sub>l, e\<^sub>l) =  Some (cd', mem', sck', e')"
      and "lexp myrexp e' cd' (st0\<lparr>Accounts := acc, Stack := sck', Memory := mem', Gas := g'a\<rparr>) g'a = Normal ((rv,rt), g''a)"
    shows "is_LStoreloc rv" and "(\<exists>lt. rt = type.Storage lt \<and> is_STValue lt)"
  using lexp_myrexp_decl[OF assms] by auto

lemma expr_bal: 
  assumes "expr (LVAL (l.Id STR ''bal'')) e' cd' (st\<lparr>Accounts := acc, Stack := sck', Memory := mem', Gas := g''a, Storage := (Storage st) (Address e' := fmupd l v' s'), Gas := g''\<rparr>) g'' = Normal ((KValue lv, Value t), g''')"
      and "(sck', e') = astack_dup STR ''bal'' (Value (TUInt b256)) (KValue (accessStorage (TUInt b256) (Address env + (STR ''.'' + STR ''balance'')) s')) (k\<^sub>l, e\<^sub>l)"
      and "Denvalue e\<^sub>l $$ STR ''bal'' = None"
    shows "(\<lceil>accessStorage (TUInt b256) (Address env + (STR ''.'' + STR ''balance'')) s'\<rceil>::int) = ReadL\<^sub>i\<^sub>n\<^sub>t lv" (is ?G1) and "t = TUInt b256"
proof -
  from assms(1)
  have "expr (LVAL (l.Id STR ''bal'')) e' cd' (st\<lparr>Accounts := acc, Stack := sck', Memory := mem', Gas := g''a, Storage := (Storage st) (Address e' := fmupd l v' s'), Gas := g''\<rparr>) g'' = rexp ((l.Id STR ''bal'')) e' cd' ((st\<lparr>Accounts := acc, Stack := sck', Memory := mem', Gas := g''a, Storage := (Storage st) (Address e' := fmupd l v' s'), Gas := g''\<rparr>)) (g'' - costs\<^sub>e (LVAL (l.Id STR ''bal'')) e' cd' (st\<lparr>Accounts := acc, Stack := sck', Memory := mem', Gas := g''a, Storage := (Storage st) (Address e' := fmupd l v' s'), Gas := g''\<rparr>))" by (simp add:expr.simps split:if_split_asm)
  moreover have "rexp ((l.Id STR ''bal'')) e' cd' ((st\<lparr>Accounts := acc, Stack := sck', Memory := mem', Gas := g''a, Storage := (Storage st) (Address e' := fmupd l v' s'), Gas := g''\<rparr>)) (g'' - costs\<^sub>e (LVAL (l.Id STR ''bal'')) e' cd' (st\<lparr>Accounts := acc, Stack := sck', Memory := mem', Gas := g''a, Storage := (Storage st) (Address e' := fmupd l v' s'), Gas := g''\<rparr>)) = Normal ((KValue (accessStorage (TUInt b256) (Address env + (STR ''.'' + STR ''balance'')) s'), (Value (TUInt b256))),(g'' - costs\<^sub>e (LVAL (l.Id STR ''bal'')) e' cd' (st\<lparr>Accounts := acc, Stack := sck', Memory := mem', Gas := g''a, Storage := (Storage st) (Address e' := fmupd l v' s'), Gas := g''\<rparr>)) )"
  proof -
    from assms(2) have "fmlookup (Denvalue e') (STR ''bal'') = Some (Value (TUInt b256), Stackloc \<lfloor>Toploc k\<^sub>l\<rfloor>)" 
      using assms(3)
      by (simp add:push_def allocate_def updateStore_def option.split)
    moreover have "accessStore (\<lfloor>Toploc k\<^sub>l\<rfloor>) sck' = Some (KValue (accessStorage (TUInt b256) (Address env + (STR ''.'' + STR ''balance'')) s'))" 
      using assms(2,3) by (simp add:push_def allocate_def updateStore_def accessStore_def)
    ultimately show ?thesis by (simp add:rexp.simps)
  qed
  ultimately have "expr (LVAL (l.Id STR ''bal'')) e' cd' (st\<lparr>Accounts := acc, Stack := sck', Memory := mem', Gas := g''a, Storage := (Storage st) (Address e' := fmupd l v' s'), Gas := g''\<rparr>) g'' = Normal ((KValue (accessStorage (TUInt b256) (Address env + (STR ''.'' + STR ''balance'')) s'), (Value (TUInt b256))),(g'' - costs\<^sub>e (LVAL (l.Id STR ''bal'')) e' cd' (st\<lparr>Accounts := acc, Stack := sck', Memory := mem', Gas := g''a, Storage := (Storage st) (Address e' := fmupd l v' s'), Gas := g''\<rparr>)))" and "t = TUInt b256" using assms(1) by simp+
  then have "lv = accessStorage (TUInt b256) (Address env + (STR ''.'' + STR ''balance'')) s'" using assms(1) by (auto)
  with `t = TUInt b256` show ?G1 and "t = TUInt b256" by simp+
qed

lemma lexp_myrexp:
  assumes "load True [] xe (ffold (init members) (emptyEnv ad cname (Address env) v) (fmdom members)) emptyTypedStore emptyStore emptyTypedStore env cd (st\<lparr>Gas := g1\<rparr>) g1 = Normal ((e\<^sub>l, cd\<^sub>l, k\<^sub>l, m\<^sub>l), g1')"
      and "lexp myrexp e\<^sub>l cd\<^sub>l (st'\<lparr>Gas := g2\<rparr>) g2 = Normal ((rv,rt), g2')"
    shows "rv= LStoreloc (Address env + (STR ''.'' + STR ''balance''))" and "rt=type.Storage (STValue (TUInt b256))"
proof -
  have "fmlookup (Denvalue (ffold (init members) (emptyEnv ad cname (Address env) v) (fmdom members))) (STR ''balance'') = Some (type.Storage (STMap TAddr (STValue (TUInt b256))), Storeloc (STR ''balance''))" unfolding emptyEnv_def using ffold_init_fmdom by simp
  moreover have el_def: "e\<^sub>l = (ffold (init members) (emptyEnv ad cname (Address env) v) (fmdom members))" using load_empty_par[OF assms(1)] by (simp add:load.simps)
  ultimately have *: "fmlookup (Denvalue e\<^sub>l) (STR ''balance'') = Some (type.Storage (STMap TAddr (STValue (TUInt b256))), Storeloc (STR ''balance''))" using assms by auto

  moreover obtain g'' where "ssel (STMap TAddr (STValue (TUInt b256))) (STR ''balance'') [SENDER] e\<^sub>l cd\<^sub>l (st'\<lparr>Gas := g2\<rparr>) g2 = Normal (((Address env) + (STR ''.'' + STR ''balance''), STValue (TUInt b256)), g'')"
  proof -
    have "g2 > costs\<^sub>e SENDER e\<^sub>l cd\<^sub>l (st'\<lparr>Gas := g2\<rparr>)" using assms(2) * by (simp add:expr.simps ssel.simps lexp.simps split:if_split_asm)
    then obtain g'' where "expr SENDER e\<^sub>l cd\<^sub>l (st'\<lparr>Gas := g2\<rparr>) g2 = Normal ((KValue (Sender e\<^sub>l), Value TAddr), g'')" by (simp add: expr.simps)
    moreover have "Sender e\<^sub>l = Address env" using el_def ffold_init_ad_same[of members "(emptyEnv ad cname (Address env) v)" "fmdom members" e\<^sub>l] unfolding emptyEnv_def by simp
    ultimately show ?thesis using that hash_def by (simp add:ssel.simps)
  qed
  ultimately show "rv= LStoreloc (Address env + (STR ''.'' + STR ''balance''))" and "rt=type.Storage (STValue (TUInt b256))" using assms(2) by (simp add: lexp.simps)+
qed

lemma expr_balance:
  assumes "load True [] xe (ffold (init members) (emptyEnv ad cname (Address env) v) (fmdom members)) emptyTypedStore emptyStore emptyTypedStore env cd (st\<lparr>Gas := g1\<rparr>) g1 = Normal ((e\<^sub>l, cd\<^sub>l, k\<^sub>l, m\<^sub>l), g1')"
      and "expr (LVAL (Ref (STR ''balance'') [SENDER])) e\<^sub>l cd\<^sub>l (st\<lparr>Accounts := acc, Stack := k\<^sub>l, Memory := m\<^sub>l, Gas := g2\<rparr>) g2 = Normal ((va, ta), g'a)"
    shows "va= KValue (accessStorage (TUInt b256) (Address env + (STR ''.'' + STR ''balance'')) (Storage st ad))"
      and "ta = Value (TUInt b256)"
proof -
  have "fmlookup (Denvalue (ffold (init members) (emptyEnv ad cname (Address env) v) (fmdom members))) (STR ''balance'') = Some (type.Storage (STMap TAddr (STValue (TUInt b256))), Storeloc (STR ''balance''))" unfolding emptyEnv_def using ffold_init_fmdom by simp
  moreover have el_def: "e\<^sub>l = (ffold (init members) (emptyEnv ad cname (Address env) v) (fmdom members))" using load_empty_par[OF assms(1)] by (simp add:load.simps)
  ultimately have *: "fmlookup (Denvalue e\<^sub>l) (STR ''balance'') = Some (type.Storage (STMap TAddr (STValue (TUInt b256))), Storeloc (STR ''balance''))" using assms by auto

  moreover obtain g'' where "ssel (STMap TAddr (STValue (TUInt b256))) (STR ''balance'') [SENDER] e\<^sub>l cd\<^sub>l (st\<lparr>Accounts := acc, Stack := k\<^sub>l, Memory := m\<^sub>l, Gas := g2\<rparr>) g2 = Normal (((Address env) + (STR ''.'' + STR ''balance''), STValue (TUInt b256)), g'')"
  proof -
    have "g2 > costs\<^sub>e SENDER e\<^sub>l cd\<^sub>l (st\<lparr>Accounts := acc, Stack := k\<^sub>l, Memory := m\<^sub>l, Gas := g2\<rparr>)" using assms(2) * by (simp add: expr.simps ssel.simps rexp.simps split:if_split_asm)
    then obtain g'' where "expr SENDER e\<^sub>l cd\<^sub>l (st\<lparr>Accounts := acc, Stack := k\<^sub>l, Memory := m\<^sub>l, Gas := g2\<rparr>) g2 = Normal ((KValue (Sender e\<^sub>l), Value TAddr), g'')" by (simp add:expr.simps ssel.simps rexp.simps)
    moreover have "Sender e\<^sub>l = Address env" using el_def ffold_init_ad_same[of members "(emptyEnv ad cname (Address env) v)" "fmdom members" e\<^sub>l] unfolding emptyEnv_def by simp
    ultimately show ?thesis using that hash_def by (simp add:expr.simps ssel.simps rexp.simps)
  qed
  moreover have "ad = Address e\<^sub>l" using el_def ffold_init_ad_same[of members "(emptyEnv ad cname (Address env) v)" "fmdom members" e\<^sub>l] unfolding emptyEnv_def by simp
  ultimately show "va= KValue (accessStorage (TUInt b256) (Address env + (STR ''.'' + STR ''balance'')) (Storage st ad))" and "ta = Value (TUInt b256)" using assms(2) by (simp add:expr.simps ssel.simps rexp.simps split:if_split_asm)+
qed

lemma expr_plus:
  assumes "load True [] xe (ffold (init members) (emptyEnv ad cname (Address env) v) (fmdom members)) emptyTypedStore emptyStore emptyTypedStore env cd (st\<lparr>Gas := g3\<rparr>) g3 = Normal ((e\<^sub>l, cd\<^sub>l, k\<^sub>l, m\<^sub>l), g3')"
      and "expr (PLUS a0 b0) ev0 cd0 st0 g0 = Normal ((xs, t'0), g'0)"
    shows "is_KValue xs" and "is_Value t'0"
  using assms by (auto simp add:expr.simps split:if_split_asm result.split_asm prod.split_asm stackvalue.split_asm type.split_asm option.split_asm)

lemma lexp_myrexp2:
  assumes "load True [] xe (ffold (init members) (emptyEnv ad cname (Address env) v) (fmdom members)) emptyTypedStore emptyStore emptyTypedStore env cd (st\<lparr>Gas := g1\<rparr>) g1 = Normal ((e\<^sub>l, cd\<^sub>l, k\<^sub>l, m\<^sub>l), g1')"
      and "lexp myrexp e\<^sub>l cd\<^sub>l (st'\<lparr>Gas := g2\<rparr>) g2 = Normal ((rv,rt), g2')"
    shows "is_LStoreloc rv" and "\<exists>x. rt=type.Storage x \<and> is_STValue x"
  using lexp_myrexp[OF assms] by auto

lemma summ_eq_sum:
  "SUMM s' = (\<Sum>(ad,x)|fmlookup s' (ad + (STR ''.'' + STR ''balance'')) = Some x \<and> ad \<noteq> adr. ReadL\<^sub>i\<^sub>n\<^sub>t x)
           + ReadL\<^sub>i\<^sub>n\<^sub>t (accessStorage (TUInt b256) (adr + (STR ''.'' + STR ''balance'')) s')"
proof (cases "fmlookup s' (adr + (STR ''.'' + STR ''balance'')) = None")
  case True
  then have "accessStorage (TUInt b256) (adr + (STR ''.'' + STR ''balance'')) s' = ShowL\<^sub>i\<^sub>n\<^sub>t 0" unfolding accessStorage_def by simp
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
  assumes "Address env \<noteq> ad"
      and "load True [] xe (ffold (init members) (emptyEnv ad cname (Address env) v) (fmdom members)) emptyTypedStore emptyStore emptyTypedStore env cd (st0\<lparr>Gas := g3\<rparr>) g3 = Normal ((e\<^sub>l, cd\<^sub>l, k\<^sub>l, m\<^sub>l), g3')"
      and "Accounts.transfer (Address env) ad v a = Some acc"
      and "iv (Storage st0 ad) (ReadL\<^sub>i\<^sub>n\<^sub>t (Bal (acc ad)) - ReadL\<^sub>i\<^sub>n\<^sub>t v)"
      and "lexp myrexp e\<^sub>l cd\<^sub>l (st0\<lparr>Gas := g'', Accounts := acc, Stack := k\<^sub>l, Memory := m\<^sub>l, Gas := g'\<rparr>) g' = Normal ((LStoreloc l, type.Storage (STValue t')), g''a)"
      and "expr (PLUS mylval VALUE) e\<^sub>l cd\<^sub>l (st0\<lparr>Gas := g'', Accounts := acc, Stack := k\<^sub>l, Memory := m\<^sub>l, Gas := g\<rparr>) g = Normal ((KValue va, Value ta), g')"
      and "Valuetypes.convert ta t' va = Some v'"
    shows "(ad = Address e\<^sub>l \<longrightarrow> iv (Storage st0 (Address e\<^sub>l)(l $$:= v')) \<lceil>Bal (acc (Address e\<^sub>l))\<rceil>) \<and>
           (ad \<noteq> Address e\<^sub>l \<longrightarrow> iv (Storage st0 ad) (ReadL\<^sub>i\<^sub>n\<^sub>t (Bal (acc ad))))"
proof (rule conjI; rule impI)
  assume "ad = Address e\<^sub>l"
  define s' s'' where "s' = Storage st0 (Address e\<^sub>l)" and "s'' = Storage st0 (Address e\<^sub>l)(l $$:= v')"
  then have "s'' = fmupd l v' s'" by simp
  moreover from lexp_myrexp[OF assms(2) assms(5)] have "l = Address env + (STR ''.'' + STR ''balance'')" and "t'=TUInt b256" by simp+
  ultimately have s''_s': "s'' = s' (Address env + (STR ''.'' + STR ''balance'') $$:= v')" by simp

  have "fmlookup (Denvalue (ffold (init members) (emptyEnv ad cname (Address env) v) (fmdom members))) (STR ''balance'') = Some (type.Storage (STMap TAddr (STValue (TUInt b256))), Storeloc (STR ''balance''))" unfolding emptyEnv_def using ffold_init_fmdom by simp
  moreover have "e\<^sub>l = (ffold (init members) (emptyEnv ad cname (Address env) v) (fmdom members))" using load_empty_par[OF assms(2)] by (simp add:load.simps)
  ultimately have "fmlookup (Denvalue e\<^sub>l) (STR ''balance'') = Some (type.Storage (STMap TAddr (STValue (TUInt b256))), Storeloc (STR ''balance''))" by simp
  then have va_def: "va = createUInt b256 ((ReadL\<^sub>i\<^sub>n\<^sub>t (accessStorage (TUInt b256) ((Sender e\<^sub>l) + (STR ''.'' + STR ''balance'')) s') + ReadL\<^sub>i\<^sub>n\<^sub>t (Svalue e\<^sub>l)))" 
   and "ta = TUInt b256" 
  using assms(6) Read_ShowL_id unfolding s'_def by (auto split:if_split_asm simp add: expr.simps ssel.simps rexp.simps add_def olift.simps hash_def)

  have "Svalue e\<^sub>l = v" and "Sender e\<^sub>l = Address env" and "Address e\<^sub>l = ad" using ffold_init_ad_same msel_ssel_expr_load_rexp_gas(4)[OF assms(2)] unfolding emptyEnv_def by simp+
  then have a_frame: "iv s' (ReadL\<^sub>i\<^sub>n\<^sub>t (Bal (acc ad)) - ReadL\<^sub>i\<^sub>n\<^sub>t v)" using assms(4) unfolding s'_def by simp

  from assms(1) have  "ReadL\<^sub>i\<^sub>n\<^sub>t (Bal (a ad)) + ReadL\<^sub>i\<^sub>n\<^sub>t v < 2^256" using transfer_val2[OF assms(3)] by simp
  moreover from `Address env \<noteq> ad` have "ReadL\<^sub>i\<^sub>n\<^sub>t (Bal (acc ad)) = ReadL\<^sub>i\<^sub>n\<^sub>t (Bal (a ad)) + ReadL\<^sub>i\<^sub>n\<^sub>t v" using transfer_add[OF assms(3)] by simp
  ultimately have a_bal: "ReadL\<^sub>i\<^sub>n\<^sub>t (Bal (acc ad)) < 2^256" by simp

  moreover have a_bounds:
      "ReadL\<^sub>i\<^sub>n\<^sub>t (accessStorage (TUInt b256) (Sender e\<^sub>l + (STR ''.'' + STR ''balance'')) s')  + \<lceil>Svalue e\<^sub>l\<rceil> < 2 ^ 256 \<and>
      ReadL\<^sub>i\<^sub>n\<^sub>t (accessStorage (TUInt b256) (Sender e\<^sub>l + (STR ''.'' + STR ''balance'')) s')  + \<lceil>Svalue e\<^sub>l\<rceil> \<ge> 0"
  proof (cases "fmlookup s' (Sender e\<^sub>l + (STR ''.'' + STR ''balance'')) = None")
    case True
    hence "(accessStorage (TUInt b256) (Sender e\<^sub>l + (STR ''.'' + STR ''balance'')) s') = ShowL\<^sub>i\<^sub>n\<^sub>t 0" unfolding accessStorage_def by simp
    moreover have "(\<lceil>Svalue e\<^sub>l\<rceil>::int) < 2 ^ 256"
    proof -
      from a_frame have "\<lceil>Svalue e\<^sub>l\<rceil> + SUMM s' \<le> ReadL\<^sub>i\<^sub>n\<^sub>t (Bal (acc ad))" unfolding iv_def using `Svalue e\<^sub>l = v` by simp
      moreover have "0 \<le> SUMM s'"
      using a_frame sum_nonneg[of "{(ad,x). fmlookup s' (ad + (STR ''.'' + STR ''balance'')) = Some x}" "\<lambda>(ad,x). ReadL\<^sub>i\<^sub>n\<^sub>t x"] unfolding iv_def by auto
      ultimately have "\<lceil>Svalue e\<^sub>l\<rceil> \<le> ReadL\<^sub>i\<^sub>n\<^sub>t (Bal (acc ad))" by simp
      then show "(\<lceil>Svalue e\<^sub>l\<rceil>::int) < 2 ^ 256" using a_bal by simp
    qed
    moreover have "ReadL\<^sub>i\<^sub>n\<^sub>t v \<ge> 0" using transfer_val1[OF assms(3)] by simp
    with `Svalue e\<^sub>l = v` have "(\<lceil>Svalue e\<^sub>l\<rceil>::int) \<ge> 0" by simp
    ultimately show ?thesis using Read_ShowL_id by simp
  next
    case False
    then obtain x where x_def: "fmlookup s'  (Sender e\<^sub>l + (STR ''.'' + STR ''balance'')) = Some x" by auto
    moreover from a_frame have "\<lceil>Svalue e\<^sub>l\<rceil> + SUMM s' \<le> ReadL\<^sub>i\<^sub>n\<^sub>t (Bal (acc ad))" unfolding iv_def using `Svalue e\<^sub>l = v` by simp
    moreover have "(case (Sender e\<^sub>l, x) of (ad, x) \<Rightarrow> \<lceil>x\<rceil>) \<le> (\<Sum>(ad, x)\<in>{(ad, x). fmlookup s' (ad + (STR ''.'' + STR ''balance'')) = Some x}. ReadL\<^sub>i\<^sub>n\<^sub>t x)"
    proof (cases rule: member_le_sum[of "(Sender e\<^sub>l,x)" "{(ad,x). fmlookup s' (ad + (STR ''.'' + STR ''balance'')) = Some x}" "\<lambda>(ad,x). ReadL\<^sub>i\<^sub>n\<^sub>t x"])
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
    ultimately have "\<lceil>Svalue e\<^sub>l\<rceil> + ReadL\<^sub>i\<^sub>n\<^sub>t x \<le> ReadL\<^sub>i\<^sub>n\<^sub>t (Bal (acc ad))" by simp
    then have "\<lceil>Svalue e\<^sub>l\<rceil> + ReadL\<^sub>i\<^sub>n\<^sub>t x \<le> ReadL\<^sub>i\<^sub>n\<^sub>t (Bal (acc ad))" by simp
    with a_bal have "\<lceil>Svalue e\<^sub>l\<rceil> + ReadL\<^sub>i\<^sub>n\<^sub>t x < 2^256" by simp
    then have "\<lceil>Svalue e\<^sub>l\<rceil> \<le> \<lceil>Bal (acc ad)\<rceil> - SUMM s'" and lck: "fmlookup s' (Sender e\<^sub>l + (STR ''.'' + STR ''balance'')) = Some x"  and "ReadL\<^sub>i\<^sub>n\<^sub>t x + \<lceil>Svalue e\<^sub>l\<rceil> < 2 ^ 256" using a_frame x_def `Svalue e\<^sub>l = v` unfolding iv_def by auto
    moreover from lck have "(accessStorage (TUInt b256) (Sender e\<^sub>l + (STR ''.'' + STR ''balance'')) s') = x" unfolding accessStorage_def by simp
    moreover have "\<lceil>Svalue e\<^sub>l\<rceil> + ReadL\<^sub>i\<^sub>n\<^sub>t x \<ge> 0"
    proof -
      have "ReadL\<^sub>i\<^sub>n\<^sub>t v \<ge> 0" using transfer_val1[OF assms(3)] by simp
      with `Svalue e\<^sub>l = v` have "(\<lceil>Svalue e\<^sub>l\<rceil>::int) \<ge> 0" by simp
      moreover from a_frame have "ReadL\<^sub>i\<^sub>n\<^sub>t x \<ge> 0" unfolding iv_def using x_def by simp
      ultimately show ?thesis by simp
    qed
    ultimately show ?thesis using Read_ShowL_id by simp
  qed
  ultimately have "va = ShowL\<^sub>i\<^sub>n\<^sub>t (ReadL\<^sub>i\<^sub>n\<^sub>t (accessStorage (TUInt b256) (Sender e\<^sub>l + (STR ''.'' + STR ''balance'')) s') + ReadL\<^sub>i\<^sub>n\<^sub>t (Svalue e\<^sub>l))" using createUInt_id[where ?v="ReadL\<^sub>i\<^sub>n\<^sub>t (accessStorage (TUInt b256) (Sender e\<^sub>l + (STR ''.'' + STR ''balance'')) s') + ReadL\<^sub>i\<^sub>n\<^sub>t (Svalue e\<^sub>l)"] va_def by simp
  then have v'_def: "v' = ShowL\<^sub>i\<^sub>n\<^sub>t (ReadL\<^sub>i\<^sub>n\<^sub>t (accessStorage (TUInt b256) (Address env + (STR ''.'' + STR ''balance'')) s') + ReadL\<^sub>i\<^sub>n\<^sub>t v)" using `Sender e\<^sub>l = Address env` `Svalue e\<^sub>l = v` `t'=TUInt b256` `ta = (TUInt b256)` using assms(7) by auto

  have "SUMM s'' \<le> \<lceil>Bal (acc ad)\<rceil>"
  proof -
    have "SUMM s' \<le> ReadL\<^sub>i\<^sub>n\<^sub>t (Bal (acc ad)) - ReadL\<^sub>i\<^sub>n\<^sub>t v" using a_frame unfolding iv_def by simp
    moreover have "SUMM s'' = SUMM s' + ReadL\<^sub>i\<^sub>n\<^sub>t v"
    proof -
      from summ_eq_sum have s1: "SUMM s' = (\<Sum>(ad,x)|fmlookup s' (ad + (STR ''.'' + STR ''balance'')) = Some x \<and> ad \<noteq> Address env. ReadL\<^sub>i\<^sub>n\<^sub>t x) + ReadL\<^sub>i\<^sub>n\<^sub>t (accessStorage (TUInt b256) (Address env + (STR ''.'' + STR ''balance'')) s')" by simp
      have s2: "SUMM s'' = (\<Sum>(ad,x)|fmlookup s'' (ad + (STR ''.'' + STR ''balance'')) = Some x \<and> ad \<noteq> Address env. ReadL\<^sub>i\<^sub>n\<^sub>t x) + ReadL\<^sub>i\<^sub>n\<^sub>t (accessStorage (TUInt b256) (Address env + (STR ''.'' + STR ''balance'')) s') + ReadL\<^sub>i\<^sub>n\<^sub>t v"
      proof -
        have "inj_on (\<lambda>(ad, x). (ad + (STR ''.'' + STR ''balance''), x)) {(ad, x). (fmlookup s'' \<circ> (\<lambda>ad. ad + (STR ''.'' + STR ''balance''))) ad = Some x}" using balance_inj by simp
        then have "finite {(ad, x). (fmlookup s'' \<circ> (\<lambda>ad. ad + (STR ''.'' + STR ''balance''))) ad = Some x}" using fmlookup_finite[of "\<lambda>ad. (ad + (STR ''.'' + STR ''balance''))" s''] by simp
        then have sum1: "finite ({(ad,x). fmlookup s'' (ad + (STR ''.'' + STR ''balance'')) = Some x \<and> ad \<noteq> Address env})" using finite_subset[of "{(ad, x). fmlookup s'' (ad + (STR ''.'' + STR ''balance'')) = Some x \<and> ad \<noteq> Address env}" "{(ad, x). fmlookup s'' (ad + (STR ''.'' + STR ''balance'')) = Some x}"] by auto
        moreover have sum2: "(Address env, ShowL\<^sub>i\<^sub>n\<^sub>t (ReadL\<^sub>i\<^sub>n\<^sub>t (accessStorage (TUInt b256) (Address env + (STR ''.'' + STR ''balance'')) s') + ReadL\<^sub>i\<^sub>n\<^sub>t v)) \<notin> {(ad,x). fmlookup s'' (ad + (STR ''.'' + STR ''balance'')) = Some x \<and> ad \<noteq> Address env}" by simp
        moreover from v'_def s''_s' have "insert (Address env, ShowL\<^sub>i\<^sub>n\<^sub>t (ReadL\<^sub>i\<^sub>n\<^sub>t (accessStorage (TUInt b256) (Address env + (STR ''.'' + STR ''balance'')) s') + ReadL\<^sub>i\<^sub>n\<^sub>t v)) {(ad, x). fmlookup s'' (ad + (STR ''.'' + STR ''balance'')) = Some x \<and> ad \<noteq> Address env} = {(ad, x). fmlookup s'' (ad + (STR ''.'' + STR ''balance'')) = Some x}" by auto
        then show ?thesis using sum.insert[OF sum1 sum2, of "\<lambda>(ad,x). ReadL\<^sub>i\<^sub>n\<^sub>t x"] Read_ShowL_id by simp
      qed
      from sum_eq_update[OF s''_s'] have s3: "(\<Sum>(ad,x)|fmlookup s'' (ad + (STR ''.'' + STR ''balance'')) = Some x \<and> ad \<noteq> Address env. ReadL\<^sub>i\<^sub>n\<^sub>t x)
                    =(\<Sum>(ad,x)|fmlookup s' (ad + (STR ''.'' + STR ''balance'')) = Some x \<and> ad \<noteq> Address env. ReadL\<^sub>i\<^sub>n\<^sub>t x)" by simp
      moreover from s''_s' v'_def have "ReadL\<^sub>i\<^sub>n\<^sub>t (accessStorage (TUInt b256) (Address env + (STR ''.'' + STR ''balance'')) s'') = ReadL\<^sub>i\<^sub>n\<^sub>t (accessStorage (TUInt b256) (Address env + (STR ''.'' + STR ''balance'')) s') + ReadL\<^sub>i\<^sub>n\<^sub>t v" using Read_ShowL_id unfolding accessStorage_def by simp
      ultimately have "SUMM s''= SUMM s' + ReadL\<^sub>i\<^sub>n\<^sub>t v"
      proof -
        from s2 have "SUMM s'' = (\<Sum>(ad,x)|fmlookup s'' (ad + (STR ''.'' + STR ''balance'')) = Some x \<and> ad \<noteq> Address env. ReadL\<^sub>i\<^sub>n\<^sub>t x) + ReadL\<^sub>i\<^sub>n\<^sub>t (accessStorage (TUInt b256) (Address env + (STR ''.'' + STR ''balance'')) s') + ReadL\<^sub>i\<^sub>n\<^sub>t v" by simp
        also from s3 have "\<dots> = (\<Sum>(ad,x)|fmlookup s' (ad + (STR ''.'' + STR ''balance'')) = Some x \<and> ad \<noteq> Address env. ReadL\<^sub>i\<^sub>n\<^sub>t x) + ReadL\<^sub>i\<^sub>n\<^sub>t (accessStorage (TUInt b256) (Address env + (STR ''.'' + STR ''balance'')) s') + ReadL\<^sub>i\<^sub>n\<^sub>t v" by simp
        also from s1 have "\<dots> = SUMM s' - ReadL\<^sub>i\<^sub>n\<^sub>t (accessStorage (TUInt b256) (Address env + (STR ''.'' + STR ''balance'')) s') + ReadL\<^sub>i\<^sub>n\<^sub>t (accessStorage (TUInt b256) (Address env + (STR ''.'' + STR ''balance'')) s') + ReadL\<^sub>i\<^sub>n\<^sub>t v" by simp
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
      proof (cases "x = Address env")
        case True
        then show ?thesis using s''_s' a_lookup using Read_ShowL_id v'_def a_bounds `Sender e\<^sub>l = Address env` `Svalue e\<^sub>l = v` by auto
      next
        case False
        then have "fmlookup s' (x + (STR ''.'' + STR ''balance'')) = Some xa" using s''_s' a_lookup String_Cancel[of "Address env" "(STR ''.'' + STR ''balance'')" x] by (simp split:if_split_asm)
        then show ?thesis using a_frame unfolding iv_def by simp
      qed
    qed
  qed
  ultimately show "iv (Storage st0 (Address e\<^sub>l)(l $$:= v')) \<lceil>Bal (acc (Address e\<^sub>l))\<rceil>" unfolding iv_def s''_def using `ad = Address e\<^sub>l` by simp
next
  assume "ad \<noteq> Address e\<^sub>l"
  moreover have "ad = Address e\<^sub>l" using ffold_init_ad_same msel_ssel_expr_load_rexp_gas(4)[OF assms(2)] unfolding emptyEnv_def by simp
  ultimately show "iv (Storage st0 ad) \<lceil>Bal (acc ad)\<rceil>" by simp
qed

lemma adapt_withdraw:
  fixes st acc sck' mem' g''a e' l v' xe
  defines "st' \<equiv> st\<lparr>Accounts := acc, Stack := sck', Memory := mem', Gas := g''a, Storage := (Storage st) (Address e' := (Storage st (Address e')) (l $$:= v'))\<rparr>"
  assumes "iv (Storage st ad) (ReadL\<^sub>i\<^sub>n\<^sub>t (Bal (acc ad)) - ReadL\<^sub>i\<^sub>n\<^sub>t v)"
      and "load True [] xe (ffold (init members) (emptyEnv ad cname (Address env) v) (fmdom members)) emptyTypedStore
           emptyStore emptyTypedStore env cd (st\<lparr>Gas := g'\<rparr>) g' = Normal ((e\<^sub>l, cd\<^sub>l, k\<^sub>l, m\<^sub>l), g'')"
      and "decl STR ''bal'' (Value (TUInt b256)) (Some (va, ta)) False cd\<^sub>l m\<^sub>l (Storage st (Address e\<^sub>l)) (cd\<^sub>l, m\<^sub>l, k\<^sub>l, e\<^sub>l) =
           Some (cd', mem', sck', e')"
      and "expr (UINT b256 0) e' cd' (st\<lparr>Accounts := acc, Stack := sck', Memory := mem', Gas := ga\<rparr>) ga =
           Normal ((KValue vb, Value tb), g'b)"
      and "Valuetypes.convert tb t' vb = Some v'"
      and "lexp myrexp e' cd' (st\<lparr>Accounts := acc, Stack := sck', Memory := mem', Gas := g'b\<rparr>) g'b =
           Normal ((LStoreloc l, type.Storage (STValue t')), g''a)"
      and "expr mylval e\<^sub>l cd\<^sub>l (st\<lparr>Accounts := acc, Stack := k\<^sub>l, Memory := m\<^sub>l,
           Gas := g'' - costs keep e\<^sub>l cd\<^sub>l (st\<lparr>Gas := g'', Accounts := acc, Stack := k\<^sub>l, Memory := m\<^sub>l\<rparr>)\<rparr>)
           (g'' - costs keep e\<^sub>l cd\<^sub>l (st\<lparr>Gas := g'', Accounts := acc, Stack := k\<^sub>l, Memory := m\<^sub>l\<rparr>)) = Normal ((va, ta), g'a)"
      and "Accounts.transfer (Address env) ad v (Accounts st) = Some acc"
      and Bal: "expr (LVAL (l.Id STR ''bal'')) e' cd' (st'\<lparr>Gas := g''b\<rparr>) g''b = Normal ((KValue lv, Value t), g''')"
      and con: "Valuetypes.convert t (TUInt b256) lv = Some lv'"
    shows "iv (Storage st' ad) (ReadL\<^sub>i\<^sub>n\<^sub>t (Bal (Accounts st' ad)) - (ReadL\<^sub>i\<^sub>n\<^sub>t lv'))"
proof -
  define acca where "acca = Accounts st' ad"
  define s' where "s' = Storage st (Address e')"
  define s'a where "s'a = Storage st' ad"
  moreover have "Address e' = ad"
  proof -
    have "Address e' = Address e\<^sub>l" using decl_env[OF assms(4)] by simp
    also have "Address e\<^sub>l = Address (ffold (init members) (emptyEnv ad cname (Address env) v) (fmdom members))" using msel_ssel_expr_load_rexp_gas(4)[OF assms(3)] by simp
    also have "\<dots> = ad" unfolding emptyEnv_def using ffold_init_ad_same by simp
    finally show ?thesis .
  qed
  ultimately have s'a_def: "s'a = fmupd l v' s'" unfolding s'_def st'_def by simp

  have "Sender e' = Address env"
  proof -
    have "Sender e' = Sender e\<^sub>l" using decl_env[OF assms(4)] by simp
    also have "Sender e\<^sub>l = Sender (ffold (init members) (emptyEnv ad cname (Address env) v) (fmdom members))" using msel_ssel_expr_load_rexp_gas(4)[OF assms(3)] by simp
    also have "\<dots> = Address env" unfolding emptyEnv_def using ffold_init_ad_same by simp
    finally show ?thesis .
  qed

  have elDef:"e\<^sub>l = (ffold (init members) (emptyEnv ad cname (Address env) v) (fmdom members))" 
    using load_empty_par[OF assms(3)] by (simp add:load.simps)

  have balIsNone:"Denvalue e\<^sub>l $$ STR ''bal'' = None" 
  proof(rule ccontr)
    assume in1:"Denvalue e\<^sub>l $$ STR ''bal'' \<noteq> None"
    then obtain v' where in2:"Denvalue e\<^sub>l $$ STR ''bal'' = Some v'" by blast
    then show False using elDef unfolding emptyEnv_def
    using ffold_init_emptyDen[of members ad cname "Address env" v "fmdom members" "STR ''bal''"] 
    unfolding emptyEnv_def using balAcc by fastforce
  qed
    

  have "iv s'a (\<lceil>Bal acca\<rceil> - \<lceil>lv'\<rceil>)" unfolding iv_def
  proof intros
    have "SUMM s' \<le> \<lceil>Bal acca\<rceil>"
    proof -
      from `Address e' = ad` have "iv s' (ReadL\<^sub>i\<^sub>n\<^sub>t (Bal acca) - ReadL\<^sub>i\<^sub>n\<^sub>t v)" using assms(2,5) unfolding s'_def st'_def acca_def by simp
      then have "SUMM s' \<le> \<lceil>Bal (acca)\<rceil> - \<lceil>v\<rceil>" unfolding iv_def by simp
      moreover have "ReadL\<^sub>i\<^sub>n\<^sub>t v \<ge> 0" using transfer_val1[OF assms(9)] by simp
      ultimately show ?thesis by simp
    qed
    moreover have "SUMM s'a = SUMM s' - ReadL\<^sub>i\<^sub>n\<^sub>t lv'"
    proof -
      from summ_eq_sum have "SUMM s'a = (\<Sum>(ad,x)|fmlookup s'a (ad + (STR ''.'' + STR ''balance'')) = Some x \<and> ad \<noteq> Sender e'. ReadL\<^sub>i\<^sub>n\<^sub>t x) + ReadL\<^sub>i\<^sub>n\<^sub>t (accessStorage (TUInt b256) (Sender e' + (STR ''.'' + STR ''balance'')) s'a)" by simp
      moreover from summ_eq_sum have "SUMM s' = (\<Sum>(ad,x)|fmlookup s' (ad + (STR ''.'' + STR ''balance'')) = Some x \<and> ad \<noteq> Sender e'. ReadL\<^sub>i\<^sub>n\<^sub>t x) + ReadL\<^sub>i\<^sub>n\<^sub>t (accessStorage (TUInt b256) (Sender e' + (STR ''.'' + STR ''balance'')) s')" by simp
      moreover from s'a_def lexp_myrexp_decl(1)[OF assms(3,4) assms(7)] have " s'a = s'((Sender e' + (STR ''.'' + STR ''balance''))$$:= v')" using `Sender e' = Address env` by simp
      with sum_eq_update have "(\<Sum>(ad,x)|fmlookup s'a (ad + (STR ''.'' + STR ''balance'')) = Some x \<and> ad \<noteq> Sender e'. ReadL\<^sub>i\<^sub>n\<^sub>t x) = (\<Sum>(ad,x)|fmlookup s' (ad + (STR ''.'' + STR ''balance'')) = Some x \<and> ad \<noteq> Sender e'. ReadL\<^sub>i\<^sub>n\<^sub>t x)"  by simp
      moreover have "ReadL\<^sub>i\<^sub>n\<^sub>t (accessStorage (TUInt b256) (Sender e' + (STR ''.'' + STR ''balance'')) s'a) = ReadL\<^sub>i\<^sub>n\<^sub>t (accessStorage (TUInt b256) (Sender e' + (STR ''.'' + STR ''balance'')) s') - ReadL\<^sub>i\<^sub>n\<^sub>t lv'"
      proof -
        have "ReadL\<^sub>i\<^sub>n\<^sub>t (accessStorage (TUInt b256) (Sender e' + (STR ''.'' + STR ''balance'')) s') = ReadL\<^sub>i\<^sub>n\<^sub>t lv'"
        proof -
          from expr_balance[OF assms(3) assms(8)] have "va= KValue (accessStorage (TUInt b256) (Address env + (STR ''.'' + STR ''balance'')) s')" and "ta = Value (TUInt b256)" using `Address e' = ad` unfolding s'_def by simp+
          then have "(sck',e') =  astack_dup STR ''bal'' (Value (TUInt b256)) (KValue (accessStorage (TUInt b256) (Address env + (STR ''.'' + STR ''balance'')) s')) (k\<^sub>l, e\<^sub>l)" 
            using decl.simps(2) assms(4) by simp
          moreover have "Denvalue e\<^sub>l $$ STR ''bal'' = None" 
            using balIsNone by blast
          ultimately have "ReadL\<^sub>i\<^sub>n\<^sub>t (accessStorage (TUInt b256) (Address env + (STR ''.'' + STR ''balance'')) s') = ReadL\<^sub>i\<^sub>n\<^sub>t lv" and "t = TUInt b256"
            using Bal unfolding s'_def st'_def using expr_bal(1,2)[of e' cd' _ st l v' "state.Storage st (Address e')" g''a mem' sck' acc lv t g''' env k\<^sub>l e\<^sub>l] 
            by  blast+
          moreover from `t = TUInt b256` have "lv = lv'" using con by simp
          ultimately show ?thesis using `Sender e' = Address env` by simp
        qed
        moreover have "ReadL\<^sub>i\<^sub>n\<^sub>t (accessStorage (TUInt b256) (Sender e' + (STR ''.'' + STR ''balance'')) s'a) = ReadL\<^sub>i\<^sub>n\<^sub>t (ShowL\<^sub>i\<^sub>n\<^sub>t 0)"
        proof -
          have "v' = ShowL\<^sub>i\<^sub>n\<^sub>t 0"
          proof -
            have "vb = createUInt b256 0" and "tb=TUInt b256" using assms(5) by (simp add: expr.simps load.simps split:if_split_asm)+
            moreover have "t'=TUInt b256" using lexp_myrexp_decl(2)[OF assms(3,4) assms(7)] by simp
            ultimately show ?thesis using assms(6) by (simp add: createUInt_id)
          qed
          moreover have "l= (Sender e' + (STR ''.'' + STR ''balance''))" using lexp_myrexp_decl(1)[OF assms(3,4) assms(7)] `Sender e' = Address env` by simp
          ultimately show ?thesis using s'a_def accessStorage_def by simp
        qed
        ultimately show ?thesis using Read_ShowL_id by simp
      qed
      ultimately show ?thesis by simp
    qed
    ultimately show "SUMM s'a \<le> \<lceil>Bal acca\<rceil> - \<lceil>lv'\<rceil>" by simp
  next
    fix ad' x
    assume *: "fmlookup s'a (ad' + (STR ''.'' + STR ''balance'')) = Some x"
    show "0 \<le> ReadL\<^sub>i\<^sub>n\<^sub>t x"
    proof (cases "ad' = Sender e'")
      case True
      moreover have "v' = ShowL\<^sub>i\<^sub>n\<^sub>t 0"
      proof -
        have "vb = createUInt b256 0" and "tb=TUInt b256" using assms(5) by (simp add:expr.simps split:if_split_asm)+
        moreover have "t'=TUInt b256" using lexp_myrexp_decl(2)[OF assms(3,4) assms(7)] by simp
        ultimately show ?thesis using assms(6) by (simp add: createUInt_id)
      qed
      moreover have "l= (Sender e' + (STR ''.'' + STR ''balance''))" using lexp_myrexp_decl(1)[OF assms(3,4) assms(7)] `Sender e' = Address env` by simp
      ultimately show ?thesis using Read_ShowL_id s'a_def * by auto
    next
      case False
      moreover from `Address e' = ad` have "iv s' (ReadL\<^sub>i\<^sub>n\<^sub>t (Bal (acc ad)) - ReadL\<^sub>i\<^sub>n\<^sub>t v)" using assms(2) unfolding s'_def by simp
      then have "POS s'" unfolding iv_def by simp
      moreover have "l= (Sender e' + (STR ''.'' + STR ''balance''))" using lexp_myrexp_decl(1)[OF assms(3,4) assms(7)] `Sender e' = Address env` by simp
      ultimately show ?thesis using s'a_def * String_Cancel by (auto split:if_split_asm)
    qed
  qed
  then show ?thesis unfolding s'a_def s'_def acca_def st'_def `Address e' = ad` by simp
qed

lemma expr_ex:
  assumes "local.expr x ev cd st g = Exception e"
  shows "e = ex.Gas \<or> e = Err"
  using ex.nchotomy by simp

lemma lexp_ex:
  assumes "local.lexp x ev cd st g = Exception e"
  shows "e = ex.Gas \<or> e = Err"
  using ex.nchotomy by simp

lemma wp_deposit[external]:
  assumes "Address ev \<noteq> ad"
      and "load True [] xe (ffold (init members) (emptyEnv ad cname (Address ev) v) (fmdom members)) emptyTypedStore emptyStore emptyTypedStore ev cd (st\<lparr>Gas := g'\<rparr>) g' = Normal ((e\<^sub>l, cd\<^sub>l, k\<^sub>l, m\<^sub>l), g'')"
      and "Accounts.transfer (Address ev) ad v (Accounts st) = Some acc"
      and "iv (Storage st ad) (ReadL\<^sub>i\<^sub>n\<^sub>t (Bal (acc ad)) - ReadL\<^sub>i\<^sub>n\<^sub>t v)"
    shows "wpS deposit
           (\<lambda>st. (iv (Storage st ad) (ReadL\<^sub>i\<^sub>n\<^sub>t (Bal (Accounts st ad))))) (\<lambda>e. e = Gas \<or> e = Err) e\<^sub>l cd\<^sub>l
           (st\<lparr>Gas := g'', Accounts := acc, Stack := k\<^sub>l, Memory := m\<^sub>l\<rparr>)"
  apply (vcg_assign wp_rule: wp_Assign2 expr_rule: expr_plus[OF assms(2)] lexp_rule: lexp_myrexp2[OF assms(2)])
  by (simp_all add: adapt_deposit[OF assms] expr_ex lexp_ex)

lemma wptransfer:
  fixes st0 acc sck' mem' g''a e' l v'
  defines "st' \<equiv> st0\<lparr>Accounts := acc, Stack := sck', Memory := mem', Gas := g''a,
        Storage := (Storage st0)(Address e' := Storage st0 (Address e')(l $$:= v'))\<rparr>"
  assumes "Pfe ad iv st'"
      and "Address ev \<noteq> ad"
      and "load True [] xe (ffold (init members) (emptyEnv ad cname (Address ev) gv') (fmdom members)) emptyTypedStore
           emptyStore emptyTypedStore ev cd (st0\<lparr>Gas := g'\<rparr>) g' =
          Normal ((e\<^sub>l, cd\<^sub>l, k\<^sub>l, m\<^sub>l), g'')"
      and "Accounts.transfer (Address ev) ad gv' (Accounts st0) = Some acc"
      and "iv (Storage st0 ad) (ReadL\<^sub>i\<^sub>n\<^sub>t (Bal (acc ad)) - ReadL\<^sub>i\<^sub>n\<^sub>t gv')"
      and "decl STR ''bal'' (Value (TUInt b256)) (Some (v, t)) False cd\<^sub>l m\<^sub>l (Storage st0 (Address e\<^sub>l))
           (cd\<^sub>l, m\<^sub>l, k\<^sub>l, e\<^sub>l) =  Some (cd', mem', sck', e')"
      and "Valuetypes.convert ta t' va = Some v'"
      and "lexp myrexp e' cd' (st0\<lparr>Accounts := acc, Stack := sck', Memory := mem', Gas := g'a\<rparr>) g'a =
           Normal ((LStoreloc l, type.Storage (STValue t')), g''a)"
      and "expr mylval e\<^sub>l cd\<^sub>l (st0\<lparr>Accounts := acc, Stack := k\<^sub>l, Memory := m\<^sub>l,
           Gas := g'' - costs (BLOCK (STR ''bal'', Value (TUInt b256), Some mylval)
           (COMP (ASSIGN myrexp (UINT b256 0)) Reentrancy.transfer)) e\<^sub>l cd\<^sub>l (st0\<lparr>Gas := g'', Accounts := acc, Stack := k\<^sub>l, Memory := m\<^sub>l\<rparr>)\<rparr>)
           (g'' - costs (BLOCK (STR ''bal'', Value (TUInt b256), Some mylval) (COMP (ASSIGN myrexp (UINT b256 0)) Reentrancy.transfer)) e\<^sub>l
           cd\<^sub>l (st0\<lparr>Gas := g'', Accounts := acc, Stack := k\<^sub>l, Memory := m\<^sub>l\<rparr>)) =
           Normal ((v, t), g''')"
      and "expr (UINT b256 0) e' cd' (st0\<lparr>Accounts := acc, Stack := sck', Memory := mem', Gas := ga\<rparr>) ga = Normal ((KValue va, Value ta), g'a)"
    shows "wpS Reentrancy.transfer (\<lambda>st. iv (Storage st ad) (ReadL\<^sub>i\<^sub>n\<^sub>t (Bal (Accounts st ad)))) (\<lambda>e. e = Gas \<or> e = Err) e' cd' st'"
proof (rule meta_eq_to_obj_eq[THEN iffD1, OF Pfe_def assms(2),rule_format], (rule conjI; (rule conjI)?))
  show "Address e' = ad"
  proof -
    have "Address e' = Address e\<^sub>l" using decl_env[OF assms(7)] by simp
    also have "Address e\<^sub>l = Address (ffold (init members) (emptyEnv ad cname (Address ev) gv') (fmdom members))" using msel_ssel_expr_load_rexp_gas(4)[OF assms(4)] by simp
    also have "\<dots> = ad" unfolding emptyEnv_def using ffold_init_ad_same by simp
    finally show ?thesis .
  qed
next
  show "\<forall>adv g. expr SENDER e' cd' (st'\<lparr>Gas := state.Gas st' - costs Reentrancy.transfer e' cd' st'\<rparr>) (state.Gas st' - costs Reentrancy.transfer e' cd' st') = Normal ((KValue adv, Value TAddr), g)
    \<longrightarrow> adv \<noteq> ad"
  proof (intros)
    fix adv g
    assume "expr SENDER e' cd' (st'\<lparr>Gas := state.Gas st' - costs Reentrancy.transfer e' cd' st'\<rparr>) (state.Gas st' - costs Reentrancy.transfer e' cd' st') = Normal ((KValue adv, Value TAddr), g)"
    moreover have "Sender e' \<noteq> ad"
    proof -
      have "Sender e' = Sender e\<^sub>l" using decl_env[OF assms(7)] by simp
      also have "Sender e\<^sub>l = Sender (ffold (init members) (emptyEnv ad cname (Address ev) gv') (fmdom members))" using msel_ssel_expr_load_rexp_gas(4)[OF assms(4)] by simp
      also have "\<dots> = Address ev" unfolding emptyEnv_def using ffold_init_ad_same by simp
      finally show ?thesis using assms(3) by simp
    qed
    ultimately show "adv \<noteq> ad" by (simp add:expr.simps split:result.split_asm if_split_asm prod.split_asm)
  qed
next
  show "\<forall>adv g v t g' v'.
       local.expr SENDER e' cd' (st'\<lparr>Gas := state.Gas st' - costs Reentrancy.transfer e' cd' st'\<rparr>)
        (state.Gas st' - costs Reentrancy.transfer e' cd' st') = Normal ((KValue adv, Value TAddr), g) \<and>
       adv \<noteq> ad \<and>
       local.expr (LVAL (l.Id STR ''bal'')) e' cd' (st'\<lparr>Gas := g\<rparr>) g = Normal ((KValue v, Value t), g') \<and>
       Valuetypes.convert t (TUInt b256) v = Some v' \<longrightarrow>
       iv (Storage st' ad) (\<lceil>Bal (Accounts st' ad)\<rceil> - ReadL\<^sub>i\<^sub>n\<^sub>t v')"
  proof elims
     fix adv lg lv lt lg' lv'
  assume a1:"expr SENDER e' cd' (st'\<lparr>Gas := state.Gas st' - costs Reentrancy.transfer e' cd' st'\<rparr>) (state.Gas st' - costs Reentrancy.transfer e' cd' st') =
          Normal ((KValue adv, Value TAddr), lg)"
     and adv_def: "adv \<noteq> ad"
     and Bal: "expr (LVAL (l.Id STR ''bal'')) e' cd' (st'\<lparr>Gas := lg\<rparr>) lg = Normal ((KValue lv, Value lt), lg')"
     and con: "Valuetypes.convert lt (TUInt b256) lv = Some lv'"
    show "iv (Storage st' ad) (\<lceil>Bal (Accounts st' ad)\<rceil> - ReadL\<^sub>i\<^sub>n\<^sub>t lv')"
     using adapt_withdraw[where ?acc=acc, OF assms(6) load_empty_par[OF assms(4)] assms(7,11,8,9,10,5)] a1 Bal con unfolding st'_def by simp
  qed
qed

lemma wp_withdraw[external]:
  assumes "\<And>st'. state.Gas st' \<le> state.Gas st \<and> Type (Accounts st' ad) = Some (atype.Contract cname) \<Longrightarrow> Pe ad iv st' \<and> Pi ad (\<lambda>_ _. True) (\<lambda>_ _. True) st' \<and> Pfi ad (\<lambda>_. True) (\<lambda>_. True) st' \<and> Pfe ad iv st'"
      and "Address ev \<noteq> ad"
      and "g'' \<le> state.Gas st"
      and "Type (acc ad) = Some (atype.Contract cname)"
      and "load True [] xe (ffold (init members) (emptyEnv ad cname (Address ev) v') (fmdom members))
           emptyTypedStore emptyStore emptyTypedStore ev cd (st0\<lparr>Gas := g'\<rparr>) g' = Normal ((e\<^sub>l, cd\<^sub>l, k\<^sub>l, m\<^sub>l), g'')"
      and "Accounts.transfer (Address ev) ad v' (Accounts st0) = Some acc"
      and "iv (Storage st0 ad) (ReadL\<^sub>i\<^sub>n\<^sub>t (Bal (acc ad)) - ReadL\<^sub>i\<^sub>n\<^sub>t v')"
    shows "wpS keep (\<lambda>st. iv (Storage st ad) (ReadL\<^sub>i\<^sub>n\<^sub>t (Bal (Accounts st ad)))) (\<lambda>e. e = Gas \<or> e = Err) e\<^sub>l cd\<^sub>l
           (st0\<lparr>Gas := g'', Accounts := acc, Stack := k\<^sub>l, Memory := m\<^sub>l\<rparr>)"
  apply vcg_block_some
  apply vcg_comp
  apply (vcg_assign wp_rule: wp_Assign2 expr_rule: expr_0 lexp_rule: lexp_myrexp_decl2[OF assms(5)])
  apply (rule wptransfer[OF _ assms(2) assms(5-7)])
  apply (drule msel_ssel_expr_load_rexp_gas lexp_gas)+
  using assms(3,4) by (simp_all add: assms(1)[THEN conjunct2,THEN conjunct2,THEN conjunct2] expr_ex lexp_ex)

lemma wp_fallback:
  assumes "Accounts.transfer (Address ev) ad v (Accounts st) = Some acc"
      and "iv (Storage st ad) (ReadL\<^sub>i\<^sub>n\<^sub>t (Bal (acc ad)) - ReadL\<^sub>i\<^sub>n\<^sub>t v)"
    shows "wpS SKIP (\<lambda>st. iv (Storage st ad) (ReadL\<^sub>i\<^sub>n\<^sub>t (Bal (Accounts st ad)))) (\<lambda>e. e = Gas \<or> e = Err)
          (ffold (init members) (emptyEnv ad cname (Address ev) v) (fmdom members)) emptyTypedStore
          (st\<lparr>Gas := g, Accounts := acc, Stack := emptyStore, Memory := emptyTypedStore\<rparr>)"
  apply vcg_skip
  using weaken[where ?acc=acc, OF assms(2) transfer_val1[OF assms(1)]] by simp

lemma wp_construct:
  fixes ev st
  defines "adv \<equiv> hash_version (Address ev) \<lfloor>Contracts (Accounts st (Address ev))\<rfloor>"
  assumes "Accounts.transfer (Address ev) adv v ((Accounts st) (adv := \<lparr>Bal = ShowL\<^sub>i\<^sub>n\<^sub>t 0, Type = Some (atype.Contract i), Contracts = 0\<rparr>)) = Some acc"
    shows "iv fmempty \<lceil>Bal (acc adv)\<rceil>"
proof -
  have "ReadL\<^sub>i\<^sub>n\<^sub>t (Bal (((Accounts st) (adv := \<lparr>Bal = ShowL\<^sub>i\<^sub>n\<^sub>t 0, Type = Some (atype.Contract i), Contracts = 0\<rparr>)) adv)) = 0" using Read_ShowL_id[of 0] by simp
  then have "ReadL\<^sub>i\<^sub>n\<^sub>t (Bal (acc (hash_version (Address ev) \<lfloor>Contracts (Accounts st (Address ev))\<rfloor>))) \<ge> 0" using transfer_mono[OF assms(2)] assms(1) by simp
  then show ?thesis unfolding iv_def assms(1) by simp
qed

lemma wp_true:
  assumes "E Gas"
      and "E Err"
  shows "wpS f (\<lambda>st. True) E e cd st"
  unfolding wpS_def wp_def using assms ex.nchotomy by (simp split: result.split, metis (full_types))

subsubsection\<open>Final results\<close>

interpretation vcg:VCG costs\<^sub>e ep costs cname members const fb iv "\<lambda>_. True" "\<lambda>_. True" "\<lambda>_ _. True" "\<lambda>_ _. True"
by (simp add: VCG.intro Calculus_axioms)

lemma safe_external: "Qe ad iv (st::state)"
  apply (external cases: cases_ext)
  apply (rule wp_deposit;assumption)
  apply vcg_block_some
  apply vcg_comp
  apply (vcg_assign wp_rule: wp_Assign2 expr_rule: expr_0 lexp_rule: lexp_myrexp_decl2)
  apply (vcg.vcg_transfer_ext ad fallback_int: wp_true fallback_ext: wp_fallback cases_ext:cases_ext cases_int:cases_int cases_fb:cases_fb invariant:adapt_withdraw)
  by (simp_all add: expr_ex lexp_ex)

lemma safe_fallback: "Qfe ad iv st"
  apply (fallback cases: cases_fb)
  by (rule wp_fallback, assumption)

lemma safe_constructor: "constructor iv"
  apply (constructor cases: cases_cons)
  apply vcg_skip
  by (simp add:wp_construct)

theorem safe:
  assumes "\<forall>ad. Type (Accounts st ad) = Some (atype.Contract cname) \<longrightarrow> iv (Storage st ad) (ReadL\<^sub>i\<^sub>n\<^sub>t (Bal (Accounts st ad)))"
    shows "\<forall>(st'::state) ad. stmt f ev cd st = Normal ((), st') \<and> Type (Accounts st' ad) = Some (atype.Contract cname) \<and> Address ev \<noteq> ad
            \<longrightarrow> iv (Storage st' ad) (ReadL\<^sub>i\<^sub>n\<^sub>t (Bal (Accounts st' ad)))"
  apply (rule invariant) using assms safe_external safe_fallback safe_constructor by auto

end

end
