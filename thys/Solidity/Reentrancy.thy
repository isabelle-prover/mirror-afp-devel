section\<open>Reentrancy\<close>

text \<open>
  In the following we use our semantics to verify a contract implementing a simple token.
  The contract is defined by definition \<^emph>\<open>victim\<close> and consist of one state variable and two methods:
  \<^item> The state variable "balance" is a mapping which assigns a balance to each address.
  \<^item> Method "deposit" allows to send money to the contract which is then added to the sender's balance.
  \<^item> Method "withdraw" allows to withdraw the callers balance.
\<close>

text \<open>
  We then verify that the following invariant (defined by \<^emph>\<open>INV\<close>) is preserved by both methods:
  The difference between
  \<^item> the contracts own account-balance and
  \<^item> the sum of all the balances kept in the contracts state variable
  is larger than a certain threshold.
\<close>

text \<open>
  There are two things to note here:
  First, Solidity implicitly triggers the call of a so-called fallback method whenever we transfer money to a contract.
  In particular if another contract calls "withdraw", this triggers an implict call to the callee's fallback method.
  This functionality was exploited in the infamous DAO attack which we demonstrate it in terms of an example later on.
  Since we do not know all potential contracts which call "withdraw", we need to verify our invariant for all possible Solidity programs.
  Thus, the core result here is a lemma which shows that the invariant is preserved by every Solidity program which is not executed in the context of our own contract.
  For our own methods we show that the invariant holds after executing it.
  Since our own program as well as the unknown program may depend on each other both properties are encoded in a single lemma (\<^emph>\<open>secure\<close>) which is then proved by induction over all statements.
  The final result is then given in terms of two corollaries for the corresponding methods of our contract.
\<close>

text \<open>
  The second thing to note is that we were not able to verify that the difference is indeed constant.
  During verification it turned out that this is not the case since in the fallback method a contract could just send us additional money withouth calling "deposit".
  In such a case the difference would change. In particular it would grow. However, we were able to verify that the difference does never shrink which is what we actually want to ensure.
\<close>

theory Reentrancy
imports Solidity_Evaluator
begin

subsection\<open>Example of Re-entrancy\<close>

(* The following value can take several minutes to process. *)
value "eval 1000
          stmt
          (COMP
            (EXTERNAL (ADDRESS (STR ''Victim'')) (STR ''deposit'') [] (UINT 256 10))
            (EXTERNAL (ADDRESS (STR ''Victim'')) (STR ''withdraw'') [] (UINT 256 0)))
          (STR ''Attacker'')
          (STR '''')
          (STR ''0'')
          [(STR ''Victim'', STR ''100''), (STR ''Attacker'', STR ''100'')]
          [
            (STR ''Attacker'',
              [],
              ITE
                (LESS (BALANCE THIS) (UINT 256 125))
                (EXTERNAL (ADDRESS (STR ''Victim'')) (STR ''withdraw'') [] (UINT 256 0))
                SKIP),
            (STR ''Victim'',
              [
                (STR ''balance'', Var (STMap TAddr (STValue (TUInt 256)))),
                (STR ''deposit'', Method ([], ASSIGN (Ref (STR ''balance'') [SENDER]) VALUE, None)),
                (STR ''withdraw'', Method ([],
                ITE
                  (LESS (UINT 256 0) (LVAL (Ref (STR ''balance'') [SENDER])))
                  (COMP
                    (TRANSFER SENDER (LVAL (Ref (STR ''balance'') [SENDER])))
                    (ASSIGN (Ref (STR ''balance'') [SENDER]) (UINT 256 0)))
                  SKIP
                , None))],
              SKIP)
          ]
          []"

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

definition victim::"(Identifier, Member) fmap"
  where "victim \<equiv> fmap_of_list [
          (STR ''balance'', Var (STMap TAddr (STValue (TUInt 256)))),
          (STR ''deposit'', Method ([], deposit, None)),
          (STR ''withdraw'', Method ([], keep, None))]"

subsection\<open>Definition of Invariant\<close>

abbreviation "SUMM s \<equiv> \<Sum>(ad,x)|fmlookup s (ad + (STR ''.'' + STR ''balance'')) = Some x. ReadL\<^sub>i\<^sub>n\<^sub>t x"

abbreviation "POS s \<equiv> \<forall>ad x. fmlookup s (ad + (STR ''.'' + STR ''balance'')) = Some x \<longrightarrow> ReadL\<^sub>i\<^sub>n\<^sub>t x \<ge> 0"

abbreviation "INV st s val bal \<equiv>
  fmlookup (storage st) (STR ''Victim'') = Some s \<and> ReadL\<^sub>i\<^sub>n\<^sub>t (accessBalance (accounts st) (STR ''Victim'')) - val \<ge> bal \<and> bal \<ge> 0"

definition frame_def: "frame bal st \<equiv> (\<exists>s. INV st s (SUMM s) bal \<and> POS s)"

subsection\<open>Verification\<close>

lemma conj3: "P \<Longrightarrow> Q \<Longrightarrow> R \<Longrightarrow> P \<and> (Q \<and> R)" by simp

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
  
lemma transfer_frame:
assumes "Accounts.transfer ad adv v (accounts st) = Some acc"
    and "frame bal st"
    and "ad \<noteq> STR ''Victim''"
  shows "frame bal (st\<lparr>accounts := acc\<rparr>)"
proof (cases "adv = STR ''Victim''")
  case True
  define st' where "st' = st\<lparr>accounts := acc, stack := emptyStore, memory := emptyStore\<rparr>"
  from True assms(2) transfer_mono[OF assms(1)] have "(\<exists>s. fmlookup (storage st) (STR ''Victim'') = Some s \<and> ReadL\<^sub>i\<^sub>n\<^sub>t (accessBalance acc (STR ''Victim'')) - (SUMM s) \<ge> bal \<and> bal \<ge> 0)" by (auto simp add:frame_def)
  then have "(\<exists>s. fmlookup (storage st') (STR ''Victim'') = Some s \<and> ReadL\<^sub>i\<^sub>n\<^sub>t (accessBalance (accounts st') (STR ''Victim'')) - (SUMM s) \<ge> bal \<and> bal \<ge> 0)" by (auto simp add: st'_def)
  then show ?thesis using assms(2) by (auto simp add:st'_def frame_def)
next
  case False
  define st' where "st' = st\<lparr>accounts := acc, stack := emptyStore, memory := emptyStore\<rparr>"
  from False assms(2) assms(3) transfer_eq[OF assms(1)] have "(\<exists>s. fmlookup (storage st) (STR ''Victim'') = Some s \<and> ReadL\<^sub>i\<^sub>n\<^sub>t (accessBalance acc (STR ''Victim'')) - (SUMM s) \<ge> bal \<and> bal \<ge> 0)" by (auto simp add:frame_def)
  then have "(\<exists>s. fmlookup (storage st') (STR ''Victim'') = Some s \<and> ReadL\<^sub>i\<^sub>n\<^sub>t (accessBalance (accounts st') (STR ''Victim'')) - (SUMM s) \<ge> bal \<and> bal \<ge> 0)" by (auto simp add: st'_def)
  then show ?thesis using assms(2) by (auto simp add:st'_def frame_def)
qed 

lemma decl_frame:
  assumes "frame bal st"
      and "decl a1 a2 a3 cp cd mem c env st = Normal (rv, st')"
    shows "frame bal st'"
proof (cases a2)
  case (Value t)
  then show ?thesis
  proof (cases a3)
    case None
    with Value show ?thesis using assms by (auto simp add:frame_def)
  next
    case (Some a)
    show ?thesis
    proof (cases a)
      case (Pair a b)
      then show ?thesis
      proof (cases a)
        case (KValue v)
        then show ?thesis
        proof (cases b)
          case v2: (Value t')
          show ?thesis
          proof (cases "Valuetypes.convert t' t v")
            case None
            with Some Pair KValue Value v2 show ?thesis using assms by simp
          next
            case s2: (Some a)
            show ?thesis
            proof (cases a)
              case p2: (Pair a b)
              with Some Pair KValue Value v2 s2 show ?thesis using assms by (auto simp add:frame_def)
            qed
          qed
        next
          case (Calldata x2)
          with Some Pair KValue Value show ?thesis using assms by simp
        next
          case (Memory x3)
          with Some Pair KValue Value show ?thesis using assms by simp
        next
          case (Storage x4)
          with Some Pair KValue Value show ?thesis using assms by simp
        qed
      next
        case (KCDptr x2)
        with Some Pair Value show ?thesis using assms by simp
      next
        case (KMemptr x3)
        with Some Pair Value show ?thesis using assms by simp
      next
        case (KStoptr x4)
        with Some Pair Value show ?thesis using assms by simp
      qed
    qed
  qed
next
  case (Calldata x2)
  then show ?thesis
  proof (cases cp)
    case True
    then show ?thesis
    proof (cases x2)
      case (MTArray x t)
      then show ?thesis
      proof (cases a3)
        case None
        with Calldata show ?thesis using assms by simp
      next
        case (Some a)
        show ?thesis
        proof (cases a)
          case (Pair a b)
          then show ?thesis
          proof (cases a)
            case (KValue x1)
            with Calldata Some Pair show ?thesis using assms by simp
          next
            case (KCDptr p)
            define l where "l = ShowL\<^sub>n\<^sub>a\<^sub>t (toploc c)"
            obtain c' where c_def: "\<exists>x. (x, c') = allocate c" by simp
            show ?thesis
            proof (cases "cpm2m p l x t cd c'")
              case None
              with Calldata MTArray Some Pair KCDptr l_def c_def True show ?thesis using assms by simp
            next
              case s2: (Some a)
              with Calldata MTArray Some Pair KCDptr l_def c_def True show ?thesis using assms by (auto simp add:frame_def)
            qed
          next
            case (KMemptr p)
            define l where "l = ShowL\<^sub>n\<^sub>a\<^sub>t (toploc c)"
            obtain c' where c_def: "\<exists>x. (x, c') = allocate c" by simp
            show ?thesis
            proof (cases "cpm2m p l x t mem c'")
              case None
              with Calldata MTArray Some Pair KMemptr l_def c_def True show ?thesis using assms by simp
            next
              case s2: (Some a)
              with Calldata MTArray Some Pair KMemptr l_def c_def True show ?thesis using assms by (auto simp add:frame_def)
            qed
          next
            case (KStoptr x4)
            with Calldata Some Pair show ?thesis using assms by simp
          qed
        qed
      qed
    next
      case (MTValue x2)
      with Calldata show ?thesis using assms by simp
    qed
  next
    case False
    with Calldata show ?thesis using assms by simp
  qed
next
  case (Memory x3)
  then show ?thesis
  proof (cases x3)
    case (MTArray x t)
    then show ?thesis
    proof (cases a3)
      case None
      with Memory MTArray None show ?thesis using assms by (auto simp add:frame_def simp add:Let_def)
    next
      case (Some a)
      then show ?thesis
      proof (cases a)
        case (Pair a b)
        then show ?thesis
        proof (cases a)
          case (KValue x1)
          with Memory MTArray Some Pair show ?thesis using assms by simp
        next
          case (KCDptr p)
          define m l where "m = memory st" and "l = ShowL\<^sub>n\<^sub>a\<^sub>t (toploc m)"
          obtain m' where m'_def: "\<exists>x. (x, m') = allocate m" by simp
          then show ?thesis
          proof (cases "cpm2m p l x t cd m'")
            case None
            with Memory MTArray Some Pair KCDptr m_def l_def m'_def show ?thesis using assms by simp
          next
            case s2: (Some a)
            with Memory MTArray Some Pair KCDptr m_def l_def m'_def show ?thesis using assms by (auto simp add:frame_def)
          qed
        next
          case (KMemptr p)
          then show ?thesis
          proof (cases cp)
            case True
            define m l where "m = memory st" and "l = ShowL\<^sub>n\<^sub>a\<^sub>t (toploc m)"
            obtain m' where m'_def: "\<exists>x. (x, m') = allocate m" by simp
            then show ?thesis
            proof (cases "cpm2m p l x t mem m'")
              case None
              with Memory MTArray Some Pair KMemptr True m_def l_def m'_def show ?thesis using assms by simp
            next
              case s2: (Some a)
              with Memory MTArray Some Pair KMemptr True m_def l_def m'_def show ?thesis using assms by (auto simp add:frame_def)
            qed
          next
            case False
            with Memory MTArray Some Pair KMemptr show ?thesis using assms by (auto simp add:frame_def)
          qed
        next
          case (KStoptr p)
          then show ?thesis
          proof (cases b)
            case (Value x1)
            with Memory MTArray Some Pair KStoptr show ?thesis using assms by simp
          next
            case (Calldata x2)
            with Memory MTArray Some Pair KStoptr show ?thesis using assms by simp
          next
            case m2: (Memory x3)
            with Memory MTArray Some Pair KStoptr show ?thesis using assms by simp
          next
            case (Storage x4)
            then show ?thesis
            proof (cases x4)
              case (STArray x' t')
              define m l where "m = memory st" and "l = ShowL\<^sub>n\<^sub>a\<^sub>t (toploc m)"
              obtain m' where m'_def: "\<exists>x. (x, m') = allocate m" by simp
              from assms(2) Memory MTArray Some Pair KStoptr Storage STArray m_def l_def m'_def
              obtain s where *: "fmlookup (storage st) (address env) = Some s" using Let_def by (auto simp add: Let_def split:option.split_asm)
              then show ?thesis
              proof (cases "cps2m p l x' t' s m'")
                case None
                with Memory MTArray Some Pair KStoptr Storage STArray m_def l_def m'_def * show ?thesis using assms by simp
              next
                case s2: (Some a)
                with Memory MTArray Some Pair KStoptr Storage STArray m_def l_def m'_def * show ?thesis using assms by (auto simp add:frame_def)
              qed
            next
              case (STMap x21 x22)
              with Memory MTArray Some Pair KStoptr Storage show ?thesis using assms by simp
            next
              case (STValue x3)
              with Memory MTArray Some Pair KStoptr Storage show ?thesis using assms by simp
            qed
          qed
        qed
      qed
    qed
  next
    case (MTValue x2)
    with Memory show ?thesis using assms by simp
  qed
next
  case (Storage x4)
  then show ?thesis
  proof (cases x4)
    case (STArray x t)
    then show ?thesis
    proof (cases a3)
      case None
      with Storage STArray show ?thesis using assms by simp
    next
      case (Some a)
      then show ?thesis
      proof (cases a)
        case (Pair a b)
        then show ?thesis
        proof (cases a)
          case (KValue x1)
          with Storage STArray Some Pair show ?thesis using assms by simp
        next
          case (KCDptr x2)
          with Storage STArray Some Pair show ?thesis using assms by simp
        next
          case (KMemptr x3)
          with Storage STArray Some Pair show ?thesis using assms by simp
        next
          case (KStoptr x4)
          with Storage STArray Some Pair show ?thesis using assms by (auto simp add:frame_def)
        qed
      qed
    qed
  next
    case (STMap t t')
    then show ?thesis
    proof (cases a3)
      case None
      with Storage STMap show ?thesis using assms by simp
    next
      case (Some a)
      then show ?thesis
      proof (cases a)
        case (Pair a b)
        then show ?thesis
        proof (cases a)
          case (KValue x1)
          with Storage STMap Some Pair show ?thesis using assms by simp
        next
          case (KCDptr x2)
          with Storage STMap Some Pair show ?thesis using assms by simp
        next
          case (KMemptr x3)
          with Storage STMap Some Pair show ?thesis using assms by simp
        next
          case (KStoptr x4)
          with Storage STMap Some Pair show ?thesis using assms by (auto simp add:frame_def)
        qed
      qed
    qed
  next
    case (STValue x3)
    with Storage show ?thesis using assms by simp
  qed
qed


context statement_with_gas
begin

lemma secureassign:
  assumes "stmt assign ep env cd st = Normal((), st')"
      and "fmlookup (storage st) (STR ''Victim'') = Some s"
      and "address env = (STR ''Victim'')"
      and "fmlookup (denvalue env) (STR ''balance'') = Some (Storage (STMap TAddr (STValue (TUInt 256))), Storeloc STR ''balance'')"
      and "accessStore x (stack st) = Some (KValue (accessStorage (TUInt 256) (sender env + (STR ''.'' + STR ''balance'')) s))"
      and "ReadL\<^sub>i\<^sub>n\<^sub>t (accessBalance (accounts st) (STR ''Victim'')) - (SUMM s) \<ge> bal"
      and "POS s"
    obtains s'
    where "fmlookup (storage st') (STR ''Victim'') = Some s'"
      and "ReadL\<^sub>i\<^sub>n\<^sub>t (accessBalance (accounts st') (STR ''Victim'')) - (SUMM s' + ReadL\<^sub>i\<^sub>n\<^sub>t (accessStorage (TUInt 256) (sender env + (STR ''.'' + STR ''balance'')) s)) \<ge> bal"
      and "accessStore x (stack st') = Some (KValue (accessStorage (TUInt 256) (sender env + (STR ''.'' + STR ''balance'')) s))"
      and "POS s'"
proof -
  define st'' where "st'' = st\<lparr>gas := gas st - costs assign ep env cd st\<rparr>"
  define st''' where "st''' = st''\<lparr>gas := gas st'' - costs\<^sub>e (UINT 256 0) ep env cd st''\<rparr>"
  define st'''' where "st'''' = st'''\<lparr>gas := gas st''' - costs\<^sub>e SENDER ep env cd st'''\<rparr>"

  from assms(1) have c1: "gas st > costs assign ep env cd st" by (auto split:if_split_asm)
  have c2: "gas st'' > costs\<^sub>e (UINT 256 0) ep env cd st''"
  proof (rule ccontr)
    assume "\<not> costs\<^sub>e (UINT 256 0) ep env cd st'' < gas st''"
    with c1 show False using assms(1) st''_def st'''_def by auto
  qed
  hence *:"expr (UINT 256 0) ep env cd st'' = Normal ((KValue (createUInt 256 0),Value (TUInt 256)), st''')" using expr.simps(2)[of 256 0 ep env cd "st\<lparr>gas := gas st - costs assign ep env cd st\<rparr>"] st''_def st'''_def by simp
  moreover have "gas st''' > costs\<^sub>e SENDER ep env cd st'''"
  proof (rule ccontr)
    assume "\<not> costs\<^sub>e SENDER ep env cd st''' < gas st'''"
    with c1 c2 show False using assms(1,4) st''_def st'''_def by auto
  qed    
  with assms(4) have **:"lexp (Ref (STR ''balance'') [SENDER]) ep env cd st''' = Normal ((LStoreloc ((sender env) + (STR ''.'' +  STR ''balance'')), Storage (STValue (TUInt 256))), st'''')" using st''''_def by simp
  moreover have "Valuetypes.convert (TUInt 256) (TUInt 256) (ShowL\<^sub>i\<^sub>n\<^sub>t 0) = Some (ShowL\<^sub>i\<^sub>n\<^sub>t 0, TUInt 256)" by simp
  moreover from * ** st''_def assms(1) obtain s'' where ***: "fmlookup (storage st'''') (address env) = Some s''" by (auto split:if_split_asm option.split_asm)
  ultimately have ****:"st' = st''''\<lparr>storage := fmupd (STR ''Victim'') (fmupd ((sender env) + (STR ''.'' + STR ''balance'')) (ShowL\<^sub>i\<^sub>n\<^sub>t 0) s'') (storage st)\<rparr>" using c1 st''_def st'''_def st''''_def assms(1,3) by auto
  moreover define s' where s'_def: "s' = (fmupd ((sender env) + (STR ''.'' + STR ''balance'')) (ShowL\<^sub>i\<^sub>n\<^sub>t 0) s'')"
  ultimately have "fmlookup (storage st') (STR ''Victim'') = Some s'"
              and *****:"fmlookup s' ((sender env) + (STR ''.'' +  STR ''balance'')) = Some (ShowL\<^sub>i\<^sub>n\<^sub>t 0)" by simp_all
  moreover have "SUMM s' + ReadL\<^sub>i\<^sub>n\<^sub>t (accessStorage (TUInt 256) (sender env + (STR ''.'' + STR ''balance'')) s) = SUMM s"
  proof -
    have s1: "SUMM s = (\<Sum>(ad,x)|fmlookup s (ad + (STR ''.'' + STR ''balance'')) = Some x \<and> ad \<noteq> sender env. ReadL\<^sub>i\<^sub>n\<^sub>t x) + ReadL\<^sub>i\<^sub>n\<^sub>t (accessStorage (TUInt 256) (sender env + (STR ''.'' + STR ''balance'')) s)"
    proof (cases "fmlookup s (sender env + (STR ''.'' + STR ''balance'')) = None")
      case True
      then have "accessStorage (TUInt 256) (sender env + (STR ''.'' + STR ''balance'')) s = ShowL\<^sub>i\<^sub>n\<^sub>t 0" by simp
      moreover have "{(ad,x). fmlookup s (ad + (STR ''.'' + STR ''balance'')) = Some x} = {(ad,x). fmlookup s (ad + (STR ''.'' + STR ''balance'')) = Some x \<and> ad \<noteq> sender env}"
      proof
        show "{(ad, x). fmlookup s (ad + (STR ''.'' + STR ''balance'')) = Some x} \<subseteq> {(ad, x). fmlookup s (ad + (STR ''.'' + STR ''balance'')) = Some x \<and> ad \<noteq> sender env}"
        proof
          fix x
          assume "x \<in> {(ad, x). fmlookup s (ad + (STR ''.'' + STR ''balance'')) = Some x}"
          then show "x \<in> {(ad, x). fmlookup s (ad + (STR ''.'' + STR ''balance'')) = Some x \<and> ad \<noteq> sender env}" using True by auto
        qed
      next
        show "{(ad, x). fmlookup s (ad + (STR ''.'' + STR ''balance'')) = Some x \<and> ad \<noteq> sender env} \<subseteq> {(ad, x). fmlookup s (ad + (STR ''.'' + STR ''balance'')) = Some x }"
        proof
          fix x
          assume "x \<in> {(ad, x). fmlookup s (ad + (STR ''.'' + STR ''balance'')) = Some x \<and> ad \<noteq> sender env}"
          then show "x \<in> {(ad, x). fmlookup s (ad + (STR ''.'' + STR ''balance'')) = Some x}" using True by auto
        qed
      qed
      then have "SUMM s = (\<Sum>(ad,x)|fmlookup s (ad + (STR ''.'' + STR ''balance'')) = Some x \<and> ad \<noteq> sender env. ReadL\<^sub>i\<^sub>n\<^sub>t x)" by simp
      ultimately show ?thesis using Read_ShowL_id by simp
    next
      case False
      then obtain val where val_def: "fmlookup s (sender env + (STR ''.'' + STR ''balance'')) = Some val" by auto

      have "inj_on (\<lambda>(ad, x). (ad + (STR ''.'' + STR ''balance''), x)) {(ad, x). (fmlookup s \<circ> (\<lambda>ad. ad + (STR ''.'' + STR ''balance''))) ad = Some x}" using balance_inj by simp
      then have "finite {(ad, x). (fmlookup s \<circ> (\<lambda>ad. ad + (STR ''.'' + STR ''balance''))) ad = Some x}" using fmlookup_finite[of "\<lambda>ad. (ad + (STR ''.'' + STR ''balance''))" s] by simp
      then have sum1: "finite ({(ad,x). fmlookup s (ad + (STR ''.'' + STR ''balance'')) = Some x \<and> ad \<noteq> sender env})" using finite_subset[of "{(ad, x). fmlookup s (ad + (STR ''.'' + STR ''balance'')) = Some x \<and> ad \<noteq> sender env}" "{(ad, x). fmlookup s (ad + (STR ''.'' + STR ''balance'')) = Some x}"] by auto
      moreover have sum2: "(sender env,val) \<notin> {(ad,x). fmlookup s (ad + (STR ''.'' + STR ''balance'')) = Some x \<and> ad \<noteq> sender env}" by simp
      moreover from sum1 x1 val_def have "insert (sender env,val) {(ad, x). fmlookup s (ad + (STR ''.'' + STR ''balance'')) = Some x \<and> ad \<noteq> sender env} = {(ad, x). fmlookup s (ad + (STR ''.'' + STR ''balance'')) = Some x}" by auto
      ultimately show ?thesis using sum.insert[OF sum1 sum2, of "\<lambda>(ad,x). ReadL\<^sub>i\<^sub>n\<^sub>t x"] val_def by simp
    qed
    moreover have s2: "SUMM s' = (\<Sum>(ad,x)|fmlookup s' (ad + (STR ''.'' + STR ''balance'')) = Some x \<and> ad \<noteq> sender env. ReadL\<^sub>i\<^sub>n\<^sub>t x)"
    proof -
      have "inj_on (\<lambda>(ad, x). (ad + (STR ''.'' + STR ''balance''), x)) {(ad, x). (fmlookup s' \<circ> (\<lambda>ad. ad + (STR ''.'' + STR ''balance''))) ad = Some x}" using balance_inj by simp
      then have "finite {(ad, x). (fmlookup s' \<circ> (\<lambda>ad. ad + (STR ''.'' + STR ''balance''))) ad = Some x}" using fmlookup_finite[of "\<lambda>ad. (ad + (STR ''.'' + STR ''balance''))" s'] by simp
      then have sum1: "finite ({(ad,x). fmlookup s' (ad + (STR ''.'' + STR ''balance'')) = Some x \<and> ad \<noteq> sender env})" using finite_subset[of "{(ad, x). fmlookup s' (ad + (STR ''.'' + STR ''balance'')) = Some x \<and> ad \<noteq> sender env}" "{(ad, x). fmlookup s' (ad + (STR ''.'' + STR ''balance'')) = Some x}"] by auto
      moreover have sum2: "(sender env,ShowL\<^sub>i\<^sub>n\<^sub>t 0) \<notin> {(ad,x). fmlookup s' (ad + (STR ''.'' + STR ''balance'')) = Some x \<and> ad \<noteq> sender env}" by simp
      moreover from ***** have "insert (sender env,ShowL\<^sub>i\<^sub>n\<^sub>t 0) {(ad, x). fmlookup s' (ad + (STR ''.'' + STR ''balance'')) = Some x \<and> ad \<noteq> sender env} = {(ad, x). fmlookup s' (ad + (STR ''.'' + STR ''balance'')) = Some x}" by auto
      ultimately show ?thesis using sum.insert[OF sum1 sum2, of "\<lambda>(ad,x). ReadL\<^sub>i\<^sub>n\<^sub>t x"] Read_ShowL_id by simp
    qed
    moreover have s3: "(\<Sum>(ad,x)|fmlookup s' (ad + (STR ''.'' + STR ''balance'')) = Some x \<and> ad \<noteq> sender env. ReadL\<^sub>i\<^sub>n\<^sub>t x)
                  =(\<Sum>(ad,x)|fmlookup s (ad + (STR ''.'' + STR ''balance'')) = Some x \<and> ad \<noteq> sender env. ReadL\<^sub>i\<^sub>n\<^sub>t x)"
    proof -
      have "{(ad,x). fmlookup s' (ad + (STR ''.'' + STR ''balance'')) = Some x \<and> ad \<noteq> sender env} = {(ad,x). fmlookup s (ad + (STR ''.'' + STR ''balance'')) = Some x \<and> ad \<noteq> sender env}"
      proof
        show "{(ad, x). fmlookup s' (ad + (STR ''.'' + STR ''balance'')) = Some x \<and> ad \<noteq> sender env}
           \<subseteq> {(ad, x). fmlookup s (ad + (STR ''.'' + STR ''balance'')) = Some x \<and> ad \<noteq> sender env}"
        proof
          fix xx
          assume "xx \<in> {(ad, x). fmlookup s' (ad + (STR ''.'' + STR ''balance'')) = Some x \<and> ad \<noteq> sender env}"
          then obtain ad x where "xx = (ad,x)" and "fmlookup s' (ad + (STR ''.'' + STR ''balance'')) = Some x" and "ad \<noteq> sender env" by auto
          moreover have "s''=s" using assms(2,3) s'_def *** st''''_def st'''_def st''_def by simp
          moreover from `ad \<noteq> sender env` have "ad + (STR ''.'' + STR ''balance'') \<noteq> (sender env) + (STR ''.'' + STR ''balance'')" using String_Cancel[where c="(STR ''.'' + STR ''balance'')"] by auto
          ultimately show "xx \<in> {(ad, x). fmlookup s (ad + (STR ''.'' + STR ''balance'')) = Some x \<and> ad \<noteq> sender env}" using s'_def by simp
        qed
      next
        show "{(ad, x). fmlookup s (ad + (STR ''.'' + STR ''balance'')) = Some x \<and> ad \<noteq> sender env}
           \<subseteq> {(ad, x). fmlookup s' (ad + (STR ''.'' + STR ''balance'')) = Some x \<and> ad \<noteq> sender env}"
        proof
          fix xx
          assume "xx \<in> {(ad, x). fmlookup s (ad + (STR ''.'' + STR ''balance'')) = Some x \<and> ad \<noteq> sender env}"
          then obtain ad x where "xx = (ad,x)" and "fmlookup s (ad + (STR ''.'' + STR ''balance'')) = Some x" and "ad \<noteq> sender env" by auto
          moreover have "s''=s" using assms(2,3) s'_def *** st''''_def st'''_def st''_def by simp
          moreover from `ad \<noteq> sender env` have "ad + (STR ''.'' + STR ''balance'') \<noteq> (sender env) + (STR ''.'' + STR ''balance'')" using String_Cancel[where c="(STR ''.'' + STR ''balance'')"] by auto
          ultimately show "xx \<in> {(ad, x). fmlookup s' (ad + (STR ''.'' + STR ''balance'')) = Some x \<and> ad \<noteq> sender env}" using s'_def by simp
        qed
      qed
      thus ?thesis by simp
    qed
    ultimately have "SUMM s' = SUMM s - ReadL\<^sub>i\<^sub>n\<^sub>t (accessStorage (TUInt 256) (sender env + (STR ''.'' + STR ''balance'')) s) "
    proof -
      from s2 have "SUMM s' = (\<Sum>(ad,x)|fmlookup s' (ad + (STR ''.'' + STR ''balance'')) = Some x \<and> ad \<noteq> sender env. ReadL\<^sub>i\<^sub>n\<^sub>t x)" by simp
      also from s3 have "\<dots> = (\<Sum>(ad,x)|fmlookup s (ad + (STR ''.'' + STR ''balance'')) = Some x \<and> ad \<noteq> sender env. ReadL\<^sub>i\<^sub>n\<^sub>t x)" by simp
      also from s1 have "\<dots> = SUMM s - ReadL\<^sub>i\<^sub>n\<^sub>t (accessStorage (TUInt 256) (sender env + (STR ''.'' + STR ''balance'')) s) " by simp
      finally show ?thesis .
    qed
    then show ?thesis by simp
  qed
  moreover have "POS s'"
  proof (rule allI[OF allI])
    fix x xa
    show "fmlookup s' (x + (STR ''.'' + STR ''balance'')) = Some xa \<longrightarrow> 0 \<le> (\<lceil>xa\<rceil>::int)"
    proof
      assume a1: "fmlookup s' (x + (STR ''.'' + STR ''balance'')) = Some xa"
      show "0 \<le> (\<lceil>xa\<rceil>::int)"
      proof (cases "x = sender env")
        case True
        then show ?thesis using s'_def a1 using Read_ShowL_id by auto
      next
        case False
        moreover have "s''=s" using assms(2,3) s'_def *** st''''_def st'''_def st''_def by simp
        ultimately have "fmlookup s (x + (STR ''.'' + STR ''balance'')) = Some xa" using s'_def a1 String_Cancel by (auto split:if_split_asm)
        then show ?thesis using assms(7) by simp
      qed
    qed
  qed
  moreover have "ReadL\<^sub>i\<^sub>n\<^sub>t (accessBalance (accounts st') (STR ''Victim'')) = ReadL\<^sub>i\<^sub>n\<^sub>t (accessBalance (accounts st) (STR ''Victim''))" using **** st''_def st'''_def st''''_def by simp
  moreover from assms(5) have "accessStore x (stack st') = Some (KValue (accessStorage (TUInt 256) (sender env + (STR ''.'' + STR ''balance'')) s) )"using **** st''_def st'''_def st''''_def by simp
  ultimately show ?thesis using assms(6) that by simp
qed


lemma securesender:
  assumes "expr SENDER ep env cd st = Normal((KValue v,t), st')"
      and "fmlookup (storage st) (STR ''Victim'') = Some s"
      and "ReadL\<^sub>i\<^sub>n\<^sub>t (accessBalance (accounts st) (STR ''Victim'')) - SUMM s \<ge> bal \<and> POS s"
    obtains s' where
      "v = sender env" 
      and "t = Value TAddr"
      and "fmlookup (storage st') (STR ''Victim'') = Some s'"
      and "ReadL\<^sub>i\<^sub>n\<^sub>t (accessBalance (accounts st') (STR ''Victim'')) - SUMM s' \<ge> bal \<and> POS s'"
  using assms by (auto split:if_split_asm)

lemma securessel:
  assumes "ssel type loc [] ep env cd st = Normal (x, st')"
      and "fmlookup (storage st) (STR ''Victim'') = Some s"
      and "ReadL\<^sub>i\<^sub>n\<^sub>t (accessBalance (accounts st) (STR ''Victim'')) - SUMM s \<ge> bal \<and> POS s"
    obtains s' where
      "x = (loc, type)"
      and "fmlookup (storage st') (STR ''Victim'') = Some s'"
      and "ReadL\<^sub>i\<^sub>n\<^sub>t (accessBalance (accounts st') (STR ''Victim'')) - SUMM s' \<ge> bal \<and> POS s'"
  using assms by auto

lemma securessel2:
  assumes "ssel (STMap TAddr (STValue (TUInt 256))) (STR ''balance'') [SENDER] ep env cd st = Normal ((loc, type), st')"
      and "fmlookup (storage st) (STR ''Victim'') = Some s"
      and "ReadL\<^sub>i\<^sub>n\<^sub>t (accessBalance (accounts st) (STR ''Victim'')) - SUMM s \<ge> bal \<and> POS s"
    obtains s' where
      "loc = sender env + (STR ''.'' + STR ''balance'')"
      and "type = STValue (TUInt 256)"
      and "fmlookup (storage st') (STR ''Victim'') = Some s'"
      and "ReadL\<^sub>i\<^sub>n\<^sub>t (accessBalance (accounts st') (STR ''Victim'')) - SUMM s' \<ge> bal \<and> POS s'"
proof -
  from assms(1) obtain v t st'' st''' x
    where *: "expr SENDER ep env cd st = Normal ((KValue v, t), st'')"
      and **: "ssel (STValue (TUInt 256)) (hash (STR ''balance'') v) [] ep env cd st'' = Normal (x,st''')"
      and "st' = st'''"
    by (auto split:if_split_asm)
  moreover obtain s'' where "v =sender env" 
      and "t = Value TAddr"
      and ***:"fmlookup (storage st'') (STR ''Victim'') = Some s''"
      and ****: "ReadL\<^sub>i\<^sub>n\<^sub>t (accessBalance (accounts st'') (STR ''Victim'')) - SUMM s'' \<ge> bal \<and> POS s''"
    using securesender[OF * assms(2,3)] by auto
  moreover obtain s''' where "x = (hash (STR ''balance'') v, STValue (TUInt 256))"
      and "fmlookup (storage st''') (STR ''Victim'') = Some s'''"
      and "ReadL\<^sub>i\<^sub>n\<^sub>t (accessBalance (accounts st''') (STR ''Victim'')) - SUMM s''' \<ge> bal \<and> POS s'''"
    using securessel[OF ** *** ****] by auto
  ultimately show ?thesis using assms(1) that by simp
qed

lemma securerexp:
  assumes "rexp myrexp e\<^sub>p env cd st = Normal ((v, t), st')"
      and "fmlookup (denvalue env) (STR ''balance'') = Some (Storage (STMap TAddr (STValue (TUInt 256))), Storeloc STR ''balance'')"
      and "fmlookup (storage st) (STR ''Victim'') = Some s"
      and "ReadL\<^sub>i\<^sub>n\<^sub>t (accessBalance (accounts st) (STR ''Victim'')) - SUMM s \<ge> bal \<and> POS s"
      and "address env = STR ''Victim''"
    obtains s' where
      "fmlookup (storage st') (address env) = Some s'"
      and "v = KValue (accessStorage (TUInt 256) (sender env + (STR ''.'' + STR ''balance'')) s')"
      and "t = Value (TUInt 256)"
      and "ReadL\<^sub>i\<^sub>n\<^sub>t (accessBalance (accounts st') (STR ''Victim'')) - SUMM s' \<ge> bal \<and> POS s'"
proof -
  from assms(1,2) obtain l' t'' st'' s
    where *: "ssel (STMap TAddr (STValue (TUInt 256))) (STR ''balance'') [SENDER] e\<^sub>p env cd st = Normal ((l', STValue t''), st'')"
      and "fmlookup (storage st'') (address env) = Some s"
      and "v = KValue (accessStorage t'' l' s)"
      and "t = Value t''" and "st'=st''"
    by (simp split:if_split_asm option.split_asm)
  moreover obtain s'' where
      "fmlookup (storage st'') (STR ''Victim'') = Some s''"
      and "ReadL\<^sub>i\<^sub>n\<^sub>t (accessBalance (accounts st'') (STR ''Victim'')) - SUMM s'' \<ge> bal \<and> POS s''"
      and "l'=sender env + (STR ''.'' + STR ''balance'')" and "t'' = TUInt 256" using securessel2[OF * assms(3,4)] by blast
  ultimately show ?thesis using assms(1,5) that by auto
qed

lemma securelval:
  assumes "expr mylval ep env cd st = Normal((v,t), st')"
      and "fmlookup (denvalue env) (STR ''balance'') = Some (Storage (STMap TAddr (STValue (TUInt 256))), Storeloc STR ''balance'')"
      and "fmlookup (storage st) (STR ''Victim'') = Some s"
      and "ReadL\<^sub>i\<^sub>n\<^sub>t (accessBalance (accounts st) (STR ''Victim'')) - SUMM s \<ge> bal \<and> bal \<ge> 0 \<and> POS s"
      and "address env = STR ''Victim''"
    obtains s' where "fmlookup (storage st') (STR ''Victim'') = Some s'"
      and "v = KValue (accessStorage (TUInt 256) (sender env + (STR ''.'' + STR ''balance'')) s')"
      and "t = Value (TUInt 256)"
      and "ReadL\<^sub>i\<^sub>n\<^sub>t (accessBalance (accounts st') (STR ''Victim'')) - SUMM s' \<ge> bal \<and> bal \<ge> 0 \<and> POS s'"
proof -
  define st'' where "st'' = st\<lparr>gas := gas st - costs\<^sub>e mylval ep env cd st\<rparr>"
  with assms(3,4) have *: "fmlookup (storage st'') (STR ''Victim'') = Some s"
    and **: "ReadL\<^sub>i\<^sub>n\<^sub>t (accessBalance (accounts st'') (STR ''Victim'')) - SUMM s \<ge> bal \<and> POS s" by simp+

  from assms(1) st''_def obtain v' t' st''' where ***: "rexp myrexp ep env cd st'' =  Normal ((v, t), st''')"
  and "v' = v"
  and "t' = t"
  and "st''' = st'"
    by (simp split:if_split_asm)

  with securerexp[OF *** assms(2) * **] show ?thesis using assms(1,4,5) that by auto
qed

lemma plus_frame:
  assumes "expr (PLUS (LVAL (Ref (STR ''balance'') [SENDER])) VALUE) ep env cd st = Normal (kv, st')"
      and "ReadL\<^sub>i\<^sub>n\<^sub>t (accessStorage (TUInt 256) (sender env + (STR ''.'' + STR ''balance'')) s) + ReadL\<^sub>i\<^sub>n\<^sub>t (svalue env) < 2^256"
      and "ReadL\<^sub>i\<^sub>n\<^sub>t (accessStorage (TUInt 256) (sender env + (STR ''.'' + STR ''balance'')) s) + ReadL\<^sub>i\<^sub>n\<^sub>t (svalue env) \<ge> 0"
      and "fmlookup (storage st) (STR ''Victim'') = Some s"
      and "ReadL\<^sub>i\<^sub>n\<^sub>t (accessBalance (accounts st) (STR ''Victim'')) - SUMM s \<ge> bal"
      and "fmlookup (denvalue env) (STR ''balance'') = Some (Storage (STMap TAddr (STValue (TUInt 256))), Storeloc STR ''balance'')"
      and "address env = (STR ''Victim'')"
    shows "kv = (KValue (ShowL\<^sub>i\<^sub>n\<^sub>t (ReadL\<^sub>i\<^sub>n\<^sub>t (accessStorage (TUInt 256) (sender env + (STR ''.'' + STR ''balance'')) s) + ReadL\<^sub>i\<^sub>n\<^sub>t (svalue env))), Value (TUInt 256))"
      and "fmlookup (storage st') (STR ''Victim'') = Some s"
      and "ReadL\<^sub>i\<^sub>n\<^sub>t (accessBalance (accounts st') (STR ''Victim'')) = ReadL\<^sub>i\<^sub>n\<^sub>t (accessBalance (accounts st) (STR ''Victim''))"
proof -
  define st0 where "st0 = st\<lparr>gas := gas st - costs\<^sub>e (PLUS (LVAL (Ref (STR ''balance'') [SENDER])) VALUE) ep env cd st\<rparr>"
  define st1 where "st1 = st0\<lparr>gas := gas st0 - costs\<^sub>e (LVAL (Ref (STR ''balance'') [SENDER])) ep env cd st0\<rparr>"
  define st2 where "st2 = st1\<lparr>gas := gas st1 - costs\<^sub>e SENDER ep env cd st1\<rparr>"

  define st3 where "st3 = st2\<lparr>gas := gas st2 - costs\<^sub>e VALUE ep env cd st2\<rparr>"
  from assms(1) obtain v1 t1 v2 t2 st'' st''' st'''' v t where
    *: "expr (LVAL (Ref (STR ''balance'') [SENDER])) ep env cd st0 = Normal ((KValue v1, Value t1), st'')"
    and **: "expr VALUE ep env cd st'' = Normal ((KValue v2, Value t2), st''')"
    and ***: "add t1 t2 v1 v2 = Some (v,t)"
    and ****: "expr (PLUS (LVAL (Ref (STR ''balance'') [SENDER])) VALUE) ep env cd st = Normal ((KValue v, Value t), st'''')"
    using st0_def by (auto simp del: expr.simps simp add:expr.simps(11) split:if_split_asm result.split_asm Stackvalue.split_asm Type.split_asm option.split_asm)
 
  moreover have "expr (LVAL (Ref (STR ''balance'') [SENDER])) ep env cd st0 = Normal ((KValue (accessStorage (TUInt 256) (sender env + (STR ''.'' + STR ''balance'')) s), Value (TUInt 256)), st'')"
    and "st'' = st2"
  proof -
    from * obtain l' t' s'' where *****: "ssel (STMap TAddr (STValue (TUInt 256))) (STR ''balance'') [SENDER] ep env cd st1 = Normal ((l', STValue t'), st'')"
      and ******: "fmlookup (storage st'') (address env) = Some s''" and "v1 = (accessStorage t' l' s'')" and "t' = t1"
      using st0_def st1_def assms(4,6) by (auto simp del: accessStorage.simps ssel.simps split:if_split_asm option.split_asm STypes.split_asm result.split_asm)
    moreover from ***** have "expr SENDER ep env cd st1 = Normal ((KValue (sender env), Value TAddr), st2)" using st2_def by (simp split:if_split_asm)
    with ***** have "st'' = st2" and "l' = sender env + (STR ''.'' + STR ''balance'')" and "t' = TUInt 256" by auto
    moreover from ****** `st'' = st2` have "s''=s" using st0_def st1_def st2_def assms(4,7) by auto
    ultimately show "expr (LVAL (Ref (STR ''balance'') [SENDER])) ep env cd st0 = Normal ((KValue (accessStorage (TUInt 256) (sender env + (STR ''.'' + STR ''balance'')) s), Value (TUInt 256)), st'')"
    and "st'' = st2" using * by (auto split:if_split_asm)
  qed
    
  moreover from ** `st'' = st2` have "expr VALUE ep env cd st2 = Normal ((KValue (svalue env), Value (TUInt 256)), st3)" and "st''' = st3" using st1_def st3_def by (auto split:if_split_asm)
  moreover have "add (TUInt 256) (TUInt 256) (accessStorage (TUInt 256) (sender env + (STR ''.'' + STR ''balance'')) s) (svalue env) = Some (ShowL\<^sub>i\<^sub>n\<^sub>t (ReadL\<^sub>i\<^sub>n\<^sub>t (accessStorage (TUInt 256) (sender env + (STR ''.'' + STR ''balance'')) s) + ReadL\<^sub>i\<^sub>n\<^sub>t (svalue env)), TUInt 256)" (is "?LHS = ?RHS")
  proof -
    have "?LHS = Some (createUInt 256 (\<lceil>(accessStorage (TUInt 256) (sender env + (STR ''.'' + STR ''balance'')) s)\<rceil>+ \<lceil>(svalue env)\<rceil>), TUInt 256)" using add_def olift.simps(2)[of "(+)" 256 256] by simp
    with assms(2,3) show "?LHS = ?RHS" by simp
  qed
  ultimately have "v= (ShowL\<^sub>i\<^sub>n\<^sub>t (ReadL\<^sub>i\<^sub>n\<^sub>t (accessStorage (TUInt 256) (sender env + (STR ''.'' + STR ''balance'')) s) + ReadL\<^sub>i\<^sub>n\<^sub>t (svalue env)))" and "t = TUInt 256" and "st' = st3" using st0_def assms(1) by (auto split:if_split_asm)
  with assms(1) **** have "kv = (KValue (ShowL\<^sub>i\<^sub>n\<^sub>t (ReadL\<^sub>i\<^sub>n\<^sub>t (accessStorage (TUInt 256) (sender env + (STR ''.'' + STR ''balance'')) s) + ReadL\<^sub>i\<^sub>n\<^sub>t (svalue env))), Value (TUInt 256))" using st0_def by simp
  moreover from assms(4) st0_def st1_def st2_def st3_def `st' = st3` have "fmlookup (storage st') (STR ''Victim'') = Some s" by simp
  moreover from assms(5) st0_def st1_def st2_def st3_def `st' = st3` have "ReadL\<^sub>i\<^sub>n\<^sub>t (accessBalance (accounts st') (STR ''Victim'')) - SUMM s \<ge> bal" by simp
  moreover have "ReadL\<^sub>i\<^sub>n\<^sub>t (accessBalance (accounts st') (STR ''Victim'')) = ReadL\<^sub>i\<^sub>n\<^sub>t (accessBalance (accounts st) (STR ''Victim''))" using st0_def st1_def st2_def st3_def `st' = st3` by simp
  ultimately show "kv = (KValue (ShowL\<^sub>i\<^sub>n\<^sub>t (ReadL\<^sub>i\<^sub>n\<^sub>t (accessStorage (TUInt 256) (sender env + (STR ''.'' + STR ''balance'')) s) + ReadL\<^sub>i\<^sub>n\<^sub>t (svalue env))), Value (TUInt 256))"
   and "fmlookup (storage st') (STR ''Victim'') = Some s"
   and "ReadL\<^sub>i\<^sub>n\<^sub>t (accessBalance (accounts st') (STR ''Victim'')) = ReadL\<^sub>i\<^sub>n\<^sub>t (accessBalance (accounts st) (STR ''Victim''))" by auto
qed



lemma deposit_frame:
  assumes "stmt deposit ep env cd st = Normal ((), st')"
      and "fmlookup (storage st) (STR ''Victim'') = Some s"
      and "address env = (STR ''Victim'')"
      and "fmlookup (denvalue env) (STR ''balance'') = Some (Storage (STMap TAddr (STValue (TUInt 256))), Storeloc STR ''balance'')"
      and "ReadL\<^sub>i\<^sub>n\<^sub>t (accessBalance (accounts st) (STR ''Victim'')) - SUMM s \<ge> bal + ReadL\<^sub>i\<^sub>n\<^sub>t (svalue env)"
      and "ReadL\<^sub>i\<^sub>n\<^sub>t (accessStorage (TUInt 256) (sender env + (STR ''.'' + STR ''balance'')) s) + ReadL\<^sub>i\<^sub>n\<^sub>t (svalue env) < 2^256"
      and "ReadL\<^sub>i\<^sub>n\<^sub>t (accessStorage (TUInt 256) (sender env + (STR ''.'' + STR ''balance'')) s) + ReadL\<^sub>i\<^sub>n\<^sub>t (svalue env) \<ge> 0"
      and "POS s"
    obtains s'
    where "fmlookup (storage st') (STR ''Victim'') = Some s'"
      and "ReadL\<^sub>i\<^sub>n\<^sub>t (accessBalance (accounts st') (STR ''Victim'')) - SUMM s' \<ge> bal"
      and "POS s'"
proof -
  define st0 where "st0 = st\<lparr>gas := gas st - costs deposit ep env cd st\<rparr>"

  from assms(1) st0_def obtain kv st'' where *: "expr (PLUS (LVAL (Ref (STR ''balance'') [SENDER])) VALUE) ep env cd st0 = Normal (kv, st'')" by (auto simp del: expr.simps split:if_split_asm result.split_asm)
  moreover have "fmlookup (storage st0) (STR ''Victim'') = Some s" using st0_def assms(2) by simp
  moreover from assms(5) have "ReadL\<^sub>i\<^sub>n\<^sub>t (accessBalance (accounts st0) (STR ''Victim'')) - SUMM s \<ge> bal + ReadL\<^sub>i\<^sub>n\<^sub>t (svalue env)" using st0_def by simp
  ultimately have **: "kv = (KValue \<lfloor>(\<lceil>accessStorage (TUInt 256) (sender env + (STR ''.'' + STR ''balance'')) s\<rceil>::int) + \<lceil>svalue env\<rceil>\<rfloor>, Value (TUInt 256))"
    and st''_s:"fmlookup (storage st'') STR ''Victim'' = Some s"
    and ac: "ReadL\<^sub>i\<^sub>n\<^sub>t (accessBalance (accounts st'') (STR ''Victim'')) = ReadL\<^sub>i\<^sub>n\<^sub>t (accessBalance (accounts st0) (STR ''Victim''))"
    using plus_frame[OF _ assms(6,7) _ _ assms(4,3), of ep cd st0 kv st''] by auto

  define v where "v= (\<lceil>accessStorage (TUInt 256) (sender env + (STR ''.'' + STR ''balance'')) s\<rceil>::int) + \<lceil>svalue env\<rceil>"
  moreover from * ** assms(1) st0_def obtain rl st''' where ***: "lexp (Ref (STR ''balance'') [SENDER]) ep env cd st'' = Normal (rl, st''')" by (auto simp del:expr.simps lexp.simps accessStorage.simps split:if_split_asm result.split_asm)
  moreover from *** assms have "rl = (LStoreloc ((sender env) + (STR ''.'' +  STR ''balance'')), Storage (STValue (TUInt 256)))" and st'''_def: "st''' = st''\<lparr>gas := gas st'' - costs\<^sub>e SENDER ep env cd st''\<rparr>"
  proof -
    from *** assms(4) obtain l' t' where
      "fmlookup (denvalue env) (STR ''balance'') = Some (Storage (STMap TAddr (STValue (TUInt 256))), Storeloc (STR ''balance''))"
      and *:"ssel (STMap TAddr (STValue (TUInt 256))) (STR ''balance'') [SENDER] ep env cd st'' = Normal ((l',t'), st''')"
      and "rl = (LStoreloc l', Storage t')"
      by (auto simp del: ssel.simps split:if_split_asm option.split_asm result.split_asm)
    moreover from * have "ssel (STMap TAddr (STValue (TUInt 256))) (STR ''balance'') [SENDER] ep env cd st'' = Normal ((((sender env) + (STR ''.'' +  STR ''balance'')), STValue (TUInt 256)), st''\<lparr>gas := gas st'' - costs\<^sub>e SENDER ep env cd st''\<rparr>)" by (simp split:if_split_asm)
    ultimately show "rl = (LStoreloc ((sender env) + (STR ''.'' +  STR ''balance'')), Storage (STValue (TUInt 256)))" and st'''_def: "st''' = st''\<lparr>gas := gas st'' - costs\<^sub>e SENDER ep env cd st''\<rparr>" by auto
  qed
  moreover have "Valuetypes.convert (TUInt 256) (TUInt 256) (ShowL\<^sub>i\<^sub>n\<^sub>t v) = Some (ShowL\<^sub>i\<^sub>n\<^sub>t v, TUInt 256)" by simp

  moreover from st''_s st'''_def have s'''_s: "fmlookup (storage st''') (STR ''Victim'') = Some s" by simp
  ultimately have ****:"st' = st'''\<lparr>storage := fmupd (STR ''Victim'') (fmupd ((sender env) + (STR ''.'' + STR ''balance'')) (ShowL\<^sub>i\<^sub>n\<^sub>t v) s) (storage st''')\<rparr>"
    using assms(1) * ** st0_def assms(3) by (auto simp del:expr.simps lexp.simps accessStorage.simps split:if_split_asm)

  moreover define s' where "s' = (fmupd ((sender env) + (STR ''.'' + STR ''balance'')) (ShowL\<^sub>i\<^sub>n\<^sub>t v) s)"
  ultimately have "fmlookup (storage st') (STR ''Victim'') = Some s'"
              and *****:"fmlookup s' ((sender env) + (STR ''.'' +  STR ''balance'')) = Some (ShowL\<^sub>i\<^sub>n\<^sub>t v)" by simp_all

  moreover have "SUMM s' = SUMM s + \<lceil>svalue env\<rceil>"
  proof -
    have s1: "SUMM s = (\<Sum>(ad,x)|fmlookup s (ad + (STR ''.'' + STR ''balance'')) = Some x \<and> ad \<noteq> sender env. ReadL\<^sub>i\<^sub>n\<^sub>t x) + ReadL\<^sub>i\<^sub>n\<^sub>t (accessStorage (TUInt 256) (sender env + (STR ''.'' + STR ''balance'')) s)"
    proof (cases "fmlookup s (sender env + (STR ''.'' + STR ''balance'')) = None")
      case True
      then have "accessStorage (TUInt 256) (sender env + (STR ''.'' + STR ''balance'')) s = ShowL\<^sub>i\<^sub>n\<^sub>t 0" by simp
      moreover have "{(ad,x). fmlookup s (ad + (STR ''.'' + STR ''balance'')) = Some x} = {(ad,x). fmlookup s (ad + (STR ''.'' + STR ''balance'')) = Some x \<and> ad \<noteq> sender env}"
      proof
        show "{(ad, x). fmlookup s (ad + (STR ''.'' + STR ''balance'')) = Some x} \<subseteq> {(ad, x). fmlookup s (ad + (STR ''.'' + STR ''balance'')) = Some x \<and> ad \<noteq> sender env}"
        proof
          fix x
          assume "x \<in> {(ad, x). fmlookup s (ad + (STR ''.'' + STR ''balance'')) = Some x}"
          then show "x \<in> {(ad, x). fmlookup s (ad + (STR ''.'' + STR ''balance'')) = Some x \<and> ad \<noteq> sender env}" using True by auto
        qed
      next
        show "{(ad, x). fmlookup s (ad + (STR ''.'' + STR ''balance'')) = Some x \<and> ad \<noteq> sender env} \<subseteq> {(ad, x). fmlookup s (ad + (STR ''.'' + STR ''balance'')) = Some x }"
        proof
          fix x
          assume "x \<in> {(ad, x). fmlookup s (ad + (STR ''.'' + STR ''balance'')) = Some x \<and> ad \<noteq> sender env}"
          then show "x \<in> {(ad, x). fmlookup s (ad + (STR ''.'' + STR ''balance'')) = Some x}" using True by auto
        qed
      qed
      then have "SUMM s = (\<Sum>(ad,x)|fmlookup s (ad + (STR ''.'' + STR ''balance'')) = Some x \<and> ad \<noteq> sender env. ReadL\<^sub>i\<^sub>n\<^sub>t x)" by simp
      ultimately show ?thesis using Read_ShowL_id by simp
    next
      case False
      then obtain val where val_def: "fmlookup s (sender env + (STR ''.'' + STR ''balance'')) = Some val" by auto

      have "inj_on (\<lambda>(ad, x). (ad + (STR ''.'' + STR ''balance''), x)) {(ad, x). (fmlookup s \<circ> (\<lambda>ad. ad + (STR ''.'' + STR ''balance''))) ad = Some x}" using balance_inj by simp
      then have "finite {(ad, x). (fmlookup s \<circ> (\<lambda>ad. ad + (STR ''.'' + STR ''balance''))) ad = Some x}" using fmlookup_finite[of "\<lambda>ad. (ad + (STR ''.'' + STR ''balance''))" s] by simp
      then have sum1: "finite ({(ad,x). fmlookup s (ad + (STR ''.'' + STR ''balance'')) = Some x \<and> ad \<noteq> sender env})" using finite_subset[of "{(ad, x). fmlookup s (ad + (STR ''.'' + STR ''balance'')) = Some x \<and> ad \<noteq> sender env}" "{(ad, x). fmlookup s (ad + (STR ''.'' + STR ''balance'')) = Some x}"] by auto
      moreover have sum2: "(sender env,val) \<notin> {(ad,x). fmlookup s (ad + (STR ''.'' + STR ''balance'')) = Some x \<and> ad \<noteq> sender env}" by simp
      moreover from sum1 x1 val_def have "insert (sender env,val) {(ad, x). fmlookup s (ad + (STR ''.'' + STR ''balance'')) = Some x \<and> ad \<noteq> sender env} = {(ad, x). fmlookup s (ad + (STR ''.'' + STR ''balance'')) = Some x}" by auto
      ultimately show ?thesis using sum.insert[OF sum1 sum2, of "\<lambda>(ad,x). ReadL\<^sub>i\<^sub>n\<^sub>t x"] val_def by simp
    qed
    moreover have s2: "SUMM s' = (\<Sum>(ad,x)|fmlookup s' (ad + (STR ''.'' + STR ''balance'')) = Some x \<and> ad \<noteq> sender env. ReadL\<^sub>i\<^sub>n\<^sub>t x) + v"
    proof -
      have "inj_on (\<lambda>(ad, x). (ad + (STR ''.'' + STR ''balance''), x)) {(ad, x). (fmlookup s' \<circ> (\<lambda>ad. ad + (STR ''.'' + STR ''balance''))) ad = Some x}" using balance_inj by simp
      then have "finite {(ad, x). (fmlookup s' \<circ> (\<lambda>ad. ad + (STR ''.'' + STR ''balance''))) ad = Some x}" using fmlookup_finite[of "\<lambda>ad. (ad + (STR ''.'' + STR ''balance''))" s'] by simp
      then have sum1: "finite ({(ad,x). fmlookup s' (ad + (STR ''.'' + STR ''balance'')) = Some x \<and> ad \<noteq> sender env})" using finite_subset[of "{(ad, x). fmlookup s' (ad + (STR ''.'' + STR ''balance'')) = Some x \<and> ad \<noteq> sender env}" "{(ad, x). fmlookup s' (ad + (STR ''.'' + STR ''balance'')) = Some x}"] by auto
      moreover have sum2: "(sender env,ShowL\<^sub>i\<^sub>n\<^sub>t v) \<notin> {(ad,x). fmlookup s' (ad + (STR ''.'' + STR ''balance'')) = Some x \<and> ad \<noteq> sender env}" by simp
      moreover from ***** have "insert (sender env,ShowL\<^sub>i\<^sub>n\<^sub>t v) {(ad, x). fmlookup s' (ad + (STR ''.'' + STR ''balance'')) = Some x \<and> ad \<noteq> sender env} = {(ad, x). fmlookup s' (ad + (STR ''.'' + STR ''balance'')) = Some x}" by auto
      ultimately show ?thesis using sum.insert[OF sum1 sum2, of "\<lambda>(ad,x). ReadL\<^sub>i\<^sub>n\<^sub>t x"] Read_ShowL_id by simp
    qed
    moreover have s3: "(\<Sum>(ad,x)|fmlookup s' (ad + (STR ''.'' + STR ''balance'')) = Some x \<and> ad \<noteq> sender env. ReadL\<^sub>i\<^sub>n\<^sub>t x)
                  =(\<Sum>(ad,x)|fmlookup s (ad + (STR ''.'' + STR ''balance'')) = Some x \<and> ad \<noteq> sender env. ReadL\<^sub>i\<^sub>n\<^sub>t x)"
    proof -
      have "{(ad,x). fmlookup s' (ad + (STR ''.'' + STR ''balance'')) = Some x \<and> ad \<noteq> sender env} = {(ad,x). fmlookup s (ad + (STR ''.'' + STR ''balance'')) = Some x \<and> ad \<noteq> sender env}"
      proof
        show "{(ad, x). fmlookup s' (ad + (STR ''.'' + STR ''balance'')) = Some x \<and> ad \<noteq> sender env}
           \<subseteq> {(ad, x). fmlookup s (ad + (STR ''.'' + STR ''balance'')) = Some x \<and> ad \<noteq> sender env}"
        proof
          fix xx
          assume "xx \<in> {(ad, x). fmlookup s' (ad + (STR ''.'' + STR ''balance'')) = Some x \<and> ad \<noteq> sender env}"
          then obtain ad x where "xx = (ad,x)" and "fmlookup s' (ad + (STR ''.'' + STR ''balance'')) = Some x" and "ad \<noteq> sender env" by auto
          then have "fmlookup s (ad + (STR ''.'' + STR ''balance'')) = Some x" using s'_def String_Cancel[of ad "(STR ''.'' + STR ''balance'')" "sender env"] by (simp split:if_split_asm)
          with `ad \<noteq> sender env` `xx = (ad,x)` show "xx \<in> {(ad, x). fmlookup s (ad + (STR ''.'' + STR ''balance'')) = Some x \<and> ad \<noteq> sender env}" by simp
        qed
      next
        show "{(ad, x). fmlookup s (ad + (STR ''.'' + STR ''balance'')) = Some x \<and> ad \<noteq> sender env}
           \<subseteq> {(ad, x). fmlookup s' (ad + (STR ''.'' + STR ''balance'')) = Some x \<and> ad \<noteq> sender env}"
        proof
          fix xx
          assume "xx \<in> {(ad, x). fmlookup s (ad + (STR ''.'' + STR ''balance'')) = Some x \<and> ad \<noteq> sender env}"
          then obtain ad x where "xx = (ad,x)" and "fmlookup s (ad + (STR ''.'' + STR ''balance'')) = Some x" and "ad \<noteq> sender env" by auto
          then have "fmlookup s' (ad + (STR ''.'' + STR ''balance'')) = Some x" using s'_def String_Cancel[of ad "(STR ''.'' + STR ''balance'')" "sender env"] by (auto split:if_split_asm)
          with `ad \<noteq> sender env` `xx = (ad,x)` show "xx \<in> {(ad, x). fmlookup s' (ad + (STR ''.'' + STR ''balance'')) = Some x \<and> ad \<noteq> sender env}" by simp
        qed
      qed
      thus ?thesis by simp
    qed
    moreover from s'_def v_def have "ReadL\<^sub>i\<^sub>n\<^sub>t (accessStorage (TUInt 256) (sender env + (STR ''.'' + STR ''balance'')) s') = ReadL\<^sub>i\<^sub>n\<^sub>t (accessStorage (TUInt 256) (sender env + (STR ''.'' + STR ''balance'')) s) + \<lceil>svalue env\<rceil>" using Read_ShowL_id by (simp split:option.split_asm)
    ultimately have "SUMM s' = SUMM s + \<lceil>svalue env\<rceil>"
    proof -
      from s2 have "SUMM s' = (\<Sum>(ad,x)|fmlookup s' (ad + (STR ''.'' + STR ''balance'')) = Some x \<and> ad \<noteq> sender env. ReadL\<^sub>i\<^sub>n\<^sub>t x) + v" by simp
      also from s3 have "\<dots> = (\<Sum>(ad,x)|fmlookup s (ad + (STR ''.'' + STR ''balance'')) = Some x \<and> ad \<noteq> sender env. ReadL\<^sub>i\<^sub>n\<^sub>t x) + v" by simp
      also from s1 have "\<dots> = SUMM s - ReadL\<^sub>i\<^sub>n\<^sub>t (accessStorage (TUInt 256) (sender env + (STR ''.'' + STR ''balance'')) s) + v" by simp
      finally show ?thesis using v_def by simp
    qed
    then show ?thesis by simp
  qed
  moreover have "POS s'"
  proof (rule allI[OF allI])
    fix ad xa
    show "fmlookup s' (ad + (STR ''.'' + STR ''balance'')) = Some xa \<longrightarrow> 0 \<le> (\<lceil>xa\<rceil>::int)"
    proof
      assume a1: "fmlookup s' (ad + (STR ''.'' + STR ''balance'')) = Some xa"
      show "0 \<le> (\<lceil>xa\<rceil>::int)"
      proof (cases "ad = sender env")
        case True
        then show ?thesis using s'_def assms(7) Read_ShowL_id a1 v_def by auto
      next
        case False
        then show ?thesis using s'_def assms(7,8) using Read_ShowL_id a1 v_def by (auto split:if_split_asm)
      qed
    qed
  qed
  moreover have "ReadL\<^sub>i\<^sub>n\<^sub>t (accessBalance (accounts st') (STR ''Victim'')) = ReadL\<^sub>i\<^sub>n\<^sub>t (accessBalance (accounts st) (STR ''Victim''))" using **** ac st0_def st'''_def by simp
  ultimately show ?thesis using that assms(5) by simp
qed


lemma secure:
        "address ev1 \<noteq> (STR ''Victim'') \<and> fmlookup ep1 (STR ''Victim'') = Some (victim, SKIP) \<longrightarrow> (\<forall>rv1 st1' bal. frame bal st1 \<and> msel c1 t1 l1 xe1 ep1 ev1 cd1 st1 = Normal (rv1, st1') \<longrightarrow> frame bal st1')"
        "address ev2 \<noteq> (STR ''Victim'') \<and> fmlookup ep2 (STR ''Victim'') = Some (victim, SKIP) \<longrightarrow> (\<forall>rv2 st2' bal. frame bal st2 \<and> ssel t2 l2 xe2 ep2 ev2 cd2 st2 = Normal (rv2, st2') \<longrightarrow> frame bal st2')"
        "address ev5 \<noteq> (STR ''Victim'') \<and> fmlookup ep5 (STR ''Victim'') = Some (victim, SKIP) \<longrightarrow> (\<forall>rv3 st5' bal. frame bal st5 \<and> lexp l5 ep5 ev5 cd5 st5 = Normal (rv3, st5') \<longrightarrow> frame bal st5')"
        "address ev4 \<noteq> (STR ''Victim'') \<and> fmlookup ep4 (STR ''Victim'') = Some (victim, SKIP) \<longrightarrow> (\<forall>rv4 st4' bal. frame bal st4 \<and> expr e4 ep4 ev4 cd4 st4 = Normal (rv4, st4') \<longrightarrow> frame bal st4')"
        "address lev \<noteq> (STR ''Victim'') \<and> fmlookup lep (STR ''Victim'') = Some (victim, SKIP) \<longrightarrow> (\<forall>ev cd st st' bal. load lcp lis lxs lep lev0 lcd0 lst0 lev lcd lst = Normal ((ev, cd, st), st') \<longrightarrow> (frame bal lst0 \<longrightarrow> frame bal st) \<and> (frame bal lst \<longrightarrow> frame bal st') \<and> address lev0 = address ev \<and> sender lev0 = sender ev \<and> svalue lev0 = svalue ev)"
        "address ev3 \<noteq> (STR ''Victim'') \<and> fmlookup ep3 (STR ''Victim'') = Some (victim, SKIP) \<longrightarrow> (\<forall>rv3 st3' bal. frame bal st3 \<and> rexp l3 ep3 ev3 cd3 st3 = Normal (rv3, st3') \<longrightarrow> frame bal st3')"
        "(fmlookup ep6 (STR ''Victim'') = Some (victim, SKIP) \<longrightarrow>
          (\<forall>st6'. stmt s6 ep6 ev6 cd6 st6 = Normal((), st6') \<longrightarrow>
            ((address ev6 \<noteq> (STR ''Victim'') \<longrightarrow> (\<forall>bal. frame bal st6 \<longrightarrow> frame bal st6'))
           \<and> (address ev6 = (STR ''Victim'') \<longrightarrow>
              (\<forall>s val bal x. s6 = transfer
              \<and> INV st6 s (SUMM s + ReadL\<^sub>i\<^sub>n\<^sub>t val) bal \<and> POS s
              \<and> fmlookup (denvalue ev6) (STR ''bal'') = Some (Value (TUInt 256), Stackloc x)
              \<and> accessStore x (stack st6) = Some (KValue val)
              \<and> sender ev6 \<noteq> address ev6
              \<longrightarrow> (\<exists>s'. fmlookup (storage st6') (STR ''Victim'') = Some s'
                  \<and> ReadL\<^sub>i\<^sub>n\<^sub>t (accessBalance (accounts st6') (STR ''Victim'')) - (SUMM s') \<ge> bal \<and> bal \<ge> 0 \<and> POS s')) \<and>
              (\<forall>s bal x. s6 = comp
              \<and> INV st6 s (SUMM s) bal \<and> POS s
              \<and> fmlookup (denvalue ev6) (STR ''bal'') = Some (Value (TUInt 256), Stackloc x)
              \<and> fmlookup (denvalue ev6) (STR ''balance'') = Some (Storage (STMap TAddr (STValue (TUInt 256))), Storeloc STR ''balance'')
              \<and> accessStore x (stack st6) = Some (KValue (accessStorage (TUInt 256) (sender ev6 + (STR ''.'' + STR ''balance'')) s))
              \<and> sender ev6 \<noteq> address ev6
              \<longrightarrow> (\<exists>s'. fmlookup (storage st6') (STR ''Victim'') = Some s'
                  \<and> ReadL\<^sub>i\<^sub>n\<^sub>t (accessBalance (accounts st6') (STR ''Victim'')) - (SUMM s') \<ge> bal \<and> bal \<ge> 0 \<and> POS s')) \<and>
              (\<forall>s bal. s6 = keep
              \<and> INV st6 s (SUMM s) bal \<and> POS s
              \<and> fmlookup (denvalue ev6) (STR ''balance'') = Some (Storage (STMap TAddr (STValue (TUInt 256))), Storeloc STR ''balance'')
              \<and> sender ev6 \<noteq> address ev6
              \<longrightarrow> (\<exists>s'. fmlookup (storage st6') (STR ''Victim'') = Some s'
                  \<and> ReadL\<^sub>i\<^sub>n\<^sub>t (accessBalance (accounts st6') (STR ''Victim'')) - (SUMM s') \<ge> bal \<and> bal \<ge> 0 \<and> POS s'))
))))"
proof (induct rule: msel_ssel_lexp_expr_load_rexp_stmt.induct
[where ?P1.0="\<lambda>c1 t1 l1 xe1 ep1 ev1 cd1 st1. address ev1 \<noteq> (STR ''Victim'') \<and> fmlookup ep1 (STR ''Victim'') = Some (victim, SKIP) \<longrightarrow> (\<forall>rv1 st1' bal. frame bal st1 \<and> msel c1 t1 l1 xe1 ep1 ev1 cd1 st1 = Normal (rv1, st1') \<longrightarrow> frame bal st1')"
   and ?P2.0="\<lambda>t2 l2 xe2 ep2 ev2 cd2 st2. address ev2 \<noteq> (STR ''Victim'') \<and> fmlookup ep2 (STR ''Victim'') = Some (victim, SKIP) \<longrightarrow> (\<forall>rv2 st2' bal. frame bal st2 \<and> ssel t2 l2 xe2 ep2 ev2 cd2 st2 = Normal (rv2, st2') \<longrightarrow> frame bal st2')"
   and ?P3.0="\<lambda>l5 ep5 ev5 cd5 st5. address ev5 \<noteq> (STR ''Victim'') \<and> fmlookup ep5 (STR ''Victim'') = Some (victim, SKIP) \<longrightarrow> (\<forall>rv5 st5' bal. frame bal st5 \<and> lexp l5 ep5 ev5 cd5 st5 = Normal (rv5, st5') \<longrightarrow> frame bal st5')"
   and ?P4.0="\<lambda>e4 ep4 ev4 cd4 st4. address ev4 \<noteq> (STR ''Victim'') \<and> fmlookup ep4 (STR ''Victim'') = Some (victim, SKIP) \<longrightarrow> (\<forall>rv4 st4' bal. frame bal st4 \<and> expr e4 ep4 ev4 cd4 st4 = Normal (rv4, st4') \<longrightarrow> frame bal st4')"
   and ?P5.0="\<lambda>lcp lis lxs lep lev0 lcd0 lst0 lev lcd lst. address lev \<noteq> (STR ''Victim'') \<and> fmlookup lep (STR ''Victim'') = Some (victim, SKIP) \<longrightarrow> (\<forall>ev cd st st' bal. load lcp lis lxs lep lev0 lcd0 lst0 lev lcd lst = Normal ((ev, cd, st), st') \<longrightarrow> (frame bal lst0 \<longrightarrow> frame bal st) \<and> (frame bal lst \<longrightarrow> frame bal st') \<and> address lev0 = address ev \<and> sender lev0 = sender ev \<and> svalue lev0 = svalue ev)"
   and ?P6.0="\<lambda>l3 ep3 ev3 cd3 st3. address ev3 \<noteq> (STR ''Victim'') \<and> fmlookup ep3 (STR ''Victim'') = Some (victim, SKIP) \<longrightarrow> (\<forall>rv3 st3' bal. frame bal st3 \<and> rexp l3 ep3 ev3 cd3 st3 = Normal (rv3, st3') \<longrightarrow> frame bal st3')"
   and ?P7.0="\<lambda>s6 ep6 ev6 cd6 st6.
(fmlookup ep6 (STR ''Victim'') = Some (victim, SKIP) \<longrightarrow>
          (\<forall>st6'. stmt s6 ep6 ev6 cd6 st6 = Normal((), st6') \<longrightarrow>
            ((address ev6 \<noteq> (STR ''Victim'') \<longrightarrow> (\<forall>bal. frame bal st6 \<longrightarrow> frame bal st6'))
           \<and> (address ev6 = (STR ''Victim'') \<longrightarrow>
              (\<forall>s val bal x. s6 = transfer
              \<and> INV st6 s (SUMM s + ReadL\<^sub>i\<^sub>n\<^sub>t val) bal \<and> POS s
              \<and> fmlookup (denvalue ev6) (STR ''bal'') = Some (Value (TUInt 256), Stackloc x)
              \<and> accessStore x (stack st6) = Some (KValue val)
              \<and> sender ev6 \<noteq> address ev6
              \<longrightarrow> (\<exists>s'. fmlookup (storage st6') (STR ''Victim'') = Some s'
                  \<and> ReadL\<^sub>i\<^sub>n\<^sub>t (accessBalance (accounts st6') (STR ''Victim'')) - (SUMM s') \<ge> bal \<and> bal \<ge> 0 \<and> POS s')) \<and>
              (\<forall>s bal x. s6 = comp
              \<and> INV st6 s (SUMM s) bal \<and> POS s
              \<and> fmlookup (denvalue ev6) (STR ''bal'') = Some (Value (TUInt 256), Stackloc x)
              \<and> fmlookup (denvalue ev6) (STR ''balance'') = Some (Storage (STMap TAddr (STValue (TUInt 256))), Storeloc STR ''balance'')
              \<and> accessStore x (stack st6) = Some (KValue (accessStorage (TUInt 256) (sender ev6 + (STR ''.'' + STR ''balance'')) s))
              \<and> sender ev6 \<noteq> address ev6
              \<longrightarrow> (\<exists>s'. fmlookup (storage st6') (STR ''Victim'') = Some s'
                  \<and> ReadL\<^sub>i\<^sub>n\<^sub>t (accessBalance (accounts st6') (STR ''Victim'')) - (SUMM s') \<ge> bal \<and> bal \<ge> 0 \<and> POS s')) \<and>
              (\<forall>s bal. s6 = keep
              \<and> INV st6 s (SUMM s) bal \<and> POS s
              \<and> fmlookup (denvalue ev6) (STR ''balance'') = Some (Storage (STMap TAddr (STValue (TUInt 256))), Storeloc STR ''balance'')
              \<and> sender ev6 \<noteq> address ev6
              \<longrightarrow> (\<exists>s'. fmlookup (storage st6') (STR ''Victim'') = Some s'
                  \<and> ReadL\<^sub>i\<^sub>n\<^sub>t (accessBalance (accounts st6') (STR ''Victim'')) - (SUMM s') \<ge> bal \<and> bal \<ge> 0 \<and> POS s'))
))))"
])
  case (1 uu uv uw ux uy uz st)
  then show ?case by simp
next
  case (2 va vb vc vd ve vf vg st)
  then show ?case by simp
next
  case (3 vh al t loc x e\<^sub>p env cd st)
  show ?case (is "_ \<longrightarrow> ?RHS")
  proof
    assume asm: "address env \<noteq> (STR ''Victim'') \<and> fmlookup e\<^sub>p (STR ''Victim'') = Some (victim, SKIP)"
    show ?RHS
    proof (rule allI[OF allI[OF allI[OF impI]]])
      fix rv1 and st' and bal
      assume *: "frame bal st \<and> msel vh (MTArray al t) loc [x] e\<^sub>p env cd st = Normal (rv1, st')"
      moreover from * obtain v4 t4 st4' where **: "expr x e\<^sub>p env cd st = Normal ((v4, t4), st4')" by (auto split: result.split_asm)
      moreover from * ** have "frame bal st4'" using 3(1) asm by (auto split:if_split_asm)
      ultimately show "frame bal st'" by (simp split:Stackvalue.split_asm Type.split_asm if_split_asm)
    qed
  qed
next
  case (4 mm al t loc x y ys e\<^sub>p env cd st)
  show ?case (is "_ \<longrightarrow> ?RHS")
  proof
    assume asm: "address env \<noteq> (STR ''Victim'') \<and> fmlookup e\<^sub>p (STR ''Victim'') = Some (victim, SKIP)"
    show ?RHS
    proof (rule allI[OF allI[OF allI[OF impI]]])
      fix rv1 and st' and bal
      assume *: "frame bal st \<and> msel mm (MTArray al t) loc (x # y # ys) e\<^sub>p env cd st = Normal (rv1, st')"
      moreover from * obtain v4 t4 st'' where **: "expr x e\<^sub>p env cd st = Normal ((KValue v4, Value t4), st'')" by (auto split: result.split_asm Stackvalue.split_asm Type.split_asm)
      moreover from * ** have f1: "frame bal st''" using 4(1) asm by (auto split:if_split_asm)
      moreover from * ** have ***: "Valuetypes.less t4 (TUInt 256) v4 \<lfloor>al\<rfloor> = Some (\<lceil>True\<rceil>, TBool)" by (auto split: result.split_asm Stackvalue.split_asm Type.split_asm if_split_asm)
      moreover from * ** *** obtain vb st''' where ****: "(applyf (\<lambda>st. if mm then memory st else cd) st'') = Normal (vb, st''')"
        and f2: "frame bal st'''" using f1 by (simp split:Stackvalue.split_asm Type.split_asm if_split_asm)
      moreover from * ** *** **** obtain ll where *****: "accessStore (hash loc v4) vb = Some (MPointer ll)"
        by (simp split: Type.split_asm if_split_asm option.split_asm Memoryvalue.split_asm)
      moreover from * ** *** **** ***** obtain l1' st'''' where ******: "msel mm t ll (y # ys) e\<^sub>p env cd st''' = Normal (l1', st'''')"
        by (simp split: Type.split_asm if_split_asm option.split_asm Memoryvalue.split_asm)
      ultimately have "st' = st''''" by simp
      moreover have x1: "\<forall>rv1' st1' bal. (frame bal st''') \<and> local.msel mm t ll (y # ys) e\<^sub>p env cd st''' = Normal (rv1', st1') \<longrightarrow> frame bal st1'" using 4(2)[OF ** _ _ _ *** _ *****] **** asm apply safe by auto
      ultimately show "frame bal st'" using f2 ****** by blast
    qed
  qed
next
  case (5 tp loc vi vj vk st)
  then show ?case by simp
next
  case (6 vl vm vn vo vp vq vr st)
  then show ?case by simp
next
  case (7 al t loc x xs e\<^sub>p env cd st)
  show ?case (is "_ \<longrightarrow> ?RHS")
  proof
    assume asm: "address env \<noteq> (STR ''Victim'') \<and> fmlookup e\<^sub>p (STR ''Victim'') = Some (victim, SKIP)"
    show ?RHS
    proof (rule allI[OF allI[OF allI[OF impI]]])
      fix rv1 and st' and bal
      assume *: "frame bal st \<and> ssel (STArray al t) loc (x # xs) e\<^sub>p env cd st = Normal (rv1, st')"
      moreover from * obtain v4 t4 st4' where **: "expr x e\<^sub>p env cd st = Normal ((KValue v4, Value t4), st4')" by (auto split: result.split_asm Stackvalue.split_asm Type.split_asm)
      moreover from * ** have f1: "frame bal st4'" using 7(1) asm by (auto split:if_split_asm)
      moreover from * ** have ***: "Valuetypes.less t4 (TUInt 256) v4 \<lfloor>al\<rfloor> = Some (\<lceil>True\<rceil>, TBool)" by (auto split: result.split_asm Stackvalue.split_asm Type.split_asm if_split_asm)
      moreover from * ** *** obtain l1' st''' where ****: "ssel t (hash loc v4) xs e\<^sub>p env cd st4' = Normal (l1', st''')" by (simp split: Type.split_asm if_split_asm option.split_asm Memoryvalue.split_asm)
      ultimately have "st' = st'''" by simp
      moreover have "\<forall>rv' st2' bal. (frame bal  st4') \<and> ssel t (hash loc v4) xs e\<^sub>p env cd st4' = Normal (rv', st2') \<longrightarrow> frame bal st2'" using 7(2)[OF ** _ _ _ ***] asm apply safe by auto
      ultimately show "frame bal st'" using f1 **** by blast
    qed
  qed
next
  case (8 vs t loc x xs e\<^sub>p env cd st)
  show ?case (is "_ \<longrightarrow> ?RHS")
  proof
    assume asm: "address env \<noteq> (STR ''Victim'') \<and> fmlookup e\<^sub>p (STR ''Victim'') = Some (victim, SKIP)"
    show ?RHS
    proof (rule allI[OF allI[OF allI[OF impI]]])
      fix rv1 and st' and bal
      assume *: "frame bal st \<and> ssel (STMap vs t) loc (x # xs) e\<^sub>p env cd st = Normal (rv1, st')"
      moreover from * obtain v4 t4 st4' where **: "expr x e\<^sub>p env cd st = Normal ((KValue v4, t4), st4')" by (auto split: result.split_asm Stackvalue.split_asm)
      moreover from * ** have ***: "frame bal st4'" using 8(1) asm by (auto split:if_split_asm)
      moreover from * ** *** obtain l1' st''' where ****:"ssel t (hash loc v4) xs e\<^sub>p env cd st4' = Normal (l1', st''')" by simp
      moreover from *** **** have "frame bal st'''" using 8(2)[OF **,of "KValue v4" t4 v4] asm by blast
      ultimately show "frame bal st'" by (simp split:Stackvalue.split_asm)
    qed
  qed
next
  case (9 i vt e vu st)
  then show ?case by (auto split:option.split_asm result.split_asm Denvalue.split_asm)
next
  case (10 i r e\<^sub>p e cd st)
  show ?case (is "_ \<longrightarrow> ?RHS")
  proof
    assume asm: "address e \<noteq> (STR ''Victim'') \<and> fmlookup e\<^sub>p (STR ''Victim'') = Some (victim, SKIP)"
    show ?RHS
    proof (rule allI[OF allI[OF allI[OF impI]]])
      fix rv1 and st' and bal
      assume *: "frame bal st \<and> lexp (Ref i r) e\<^sub>p e cd st = Normal (rv1, st')"
      show "frame bal st'"
      proof (cases "fmlookup (denvalue e) i")
        case None
        with * show ?thesis by simp
      next
        case (Some a)
        then show ?thesis
        proof (cases a)
          case (Pair tp b)
          then show ?thesis
          proof (cases b)
            case (Stackloc l')
            then show ?thesis
            proof (cases "accessStore l' (stack st)")
              case None
              with * show ?thesis using Some Pair Stackloc by simp
            next
              case s2: (Some k)
              then show ?thesis
              proof (cases k)
                case (KValue x1)
                with * show ?thesis using Some Pair Stackloc s2 by simp
              next
                case (KCDptr x2)
                with * show ?thesis using Some Pair Stackloc s2 by simp
              next
                case (KMemptr l'')
                then show ?thesis
                proof (cases tp)
                  case (Value x1)
                  with * show ?thesis using Some Pair Stackloc s2 KMemptr by simp
                next
                  case (Calldata x2)
                  with * show ?thesis using Some Pair Stackloc s2 KMemptr by simp
                next
                  case (Memory x3)
                  with * Some Pair Stackloc KMemptr s2 obtain l1' t1' where "msel True x3 l'' r e\<^sub>p e cd st = Normal ((l1', t1'), st')" by (auto split: result.split_asm)
                  with * 10(1)[OF Some Pair Stackloc _ _ KMemptr, of "Some k" st x3] show ?thesis using s2 Memory asm by auto
                next
                  case (Storage x4)
                  with * show ?thesis using Some Pair Stackloc s2 KMemptr by simp
                qed
              next
                case (KStoptr l'')
                then show ?thesis
                proof (cases tp)
                  case (Value x1)
                  with * show ?thesis using Some Pair Stackloc s2 KStoptr by simp
                next
                  case (Calldata x2)
                  with * show ?thesis using Some Pair Stackloc s2 KStoptr by simp
                next
                  case (Memory x3)
                  with * show ?thesis using Some Pair Stackloc s2 KStoptr by simp
                next
                  case (Storage x4)
                  with * Some Pair Stackloc KStoptr s2 obtain l1' t1' where "ssel x4 l'' r e\<^sub>p e cd st = Normal ((l1', t1'), st')" by (auto split: result.split_asm)
                  with * 10(2)[OF Some Pair Stackloc _ _ KStoptr, of "Some k" st x4] show ?thesis using s2 Storage asm by auto
                qed
              qed
            qed        
          next
            case (Storeloc l'')
            then show ?thesis
            proof (cases tp)
              case (Value x1)
              with * show ?thesis using Some Pair Storeloc by simp
            next
              case (Calldata x2)
              with * show ?thesis using Some Pair Storeloc by simp
            next
              case (Memory x3)
              with * show ?thesis using Some Pair Storeloc by simp
            next
              case (Storage x4)
              with * Some Pair Storeloc obtain l1' t1' where "ssel x4 l'' r e\<^sub>p e cd st = Normal ((l1', t1'), st')" by (auto split: result.split_asm)
              with * 10(3)[OF Some Pair Storeloc Storage] asm show ?thesis by auto
            qed
          qed
        qed
      qed
    qed
  qed
next
  case (11 b x e\<^sub>p e cd st)
  then show ?case by (simp add:frame_def)
next
  case (12 b x e\<^sub>p e cd st)
  then show ?case by (simp add:frame_def)
next
  case (13 ad e\<^sub>p e cd st)
  then show ?case by (simp add:frame_def)
next
  case (14 ad e\<^sub>p e cd st)
  show ?case (is "_ \<longrightarrow> ?RHS")
  proof
    assume asm: "address e \<noteq> (STR ''Victim'') \<and> fmlookup e\<^sub>p (STR ''Victim'') = Some (victim, SKIP)"
    show ?RHS
    proof (rule allI[OF allI[OF allI[OF impI]]])
      fix rv1 and st' and bal
      assume *: "frame bal st \<and> expr (BALANCE ad) e\<^sub>p e cd st = Normal (rv1, st')"
      moreover from * obtain adv st'' where **:"expr ad e\<^sub>p e cd (st\<lparr>gas:=gas st - (costs\<^sub>e (BALANCE ad) e\<^sub>p e cd st)\<rparr>) = Normal ((KValue adv, Value TAddr),st'')" by (auto split:if_split_asm result.split_asm Stackvalue.split_asm Types.split_asm Type.split_asm)
      with * ** have "frame bal st''" using 14(1) asm by (auto simp add:frame_def split:if_split_asm)
      moreover from * ** have "st' = st''" by (simp split:if_split_asm)
      ultimately show "frame bal st'" by simp
    qed
  qed
next
  case (15 e\<^sub>p e cd st)
  then show ?case by (simp add:frame_def)
next
  case (16 e\<^sub>p e cd st)
  then show ?case by (simp add:frame_def)
next
  case (17 e\<^sub>p e cd st)
  then show ?case by (simp add:frame_def)
next
  case (18 e\<^sub>p e cd st)
  then show ?case by (simp add:frame_def)
next
  case (19 e\<^sub>p e cd st)
  then show ?case by (simp add:frame_def)
next
  case (20 x e\<^sub>p e cd st)
  show ?case (is "_ \<longrightarrow> ?RHS")
  proof
    assume asm: "address e \<noteq> (STR ''Victim'') \<and> fmlookup e\<^sub>p (STR ''Victim'') = Some (victim, SKIP)"
    show ?RHS
    proof (rule allI[OF allI[OF allI[OF impI]]])
      fix rv1 and st' and bal
      assume *: "frame bal st \<and> expr (NOT x) e\<^sub>p e cd st = Normal (rv1, st')"
      then have f1: "frame bal (st\<lparr>gas:=gas st - (costs\<^sub>e (NOT x) e\<^sub>p e cd st)\<rparr>)" by (simp add:frame_def)
      moreover from * obtain v t st'' where **: "expr x e\<^sub>p e cd (st\<lparr>gas:=gas st - (costs\<^sub>e (NOT x) e\<^sub>p e cd st)\<rparr>) = Normal ((KValue v, Value t), st'')"
        by (auto split:if_split_asm result.split_asm prod.split_asm Stackvalue.split_asm Type.split_asm)
      moreover from * ** have ***: "frame bal st''" using 20(1) asm by (auto simp add:frame_def split:if_split_asm)
      show "frame bal st'"
      proof (cases "v = ShowL\<^sub>b\<^sub>o\<^sub>o\<^sub>l True")
        case True
        with * ** *** obtain x st''' where "expr FALSE e\<^sub>p e cd st'' = Normal (x, st''')"
          and "frame bal st'''" by (auto simp add:frame_def split:if_split_asm)
        with * ** *** True show ?thesis by (auto split: if_split_asm)
      next
        case False
        with * ** *** obtain x st''' where "expr TRUE e\<^sub>p e cd st'' = Normal (x, st''')"
          and "frame bal st'''" by (auto simp add:frame_def split:if_split_asm)
        with * ** *** False show ?thesis by (auto split: if_split_asm)
      qed
    qed
  qed
next
  case (21 e1 e2 e\<^sub>p e cd st)
  show ?case (is "_ \<longrightarrow> ?RHS")
  proof
    assume asm: "address e \<noteq> (STR ''Victim'') \<and> fmlookup e\<^sub>p (STR ''Victim'') = Some (victim, SKIP)"
    show ?RHS
    proof (rule allI[OF allI[OF allI[OF impI]]])
      fix rv1 and st' and bal
      assume *: "frame bal st \<and> expr (PLUS e1 e2) e\<^sub>p e cd st = Normal (rv1, st')"
      moreover from * obtain v1 t1 st'' where **: "expr e1 e\<^sub>p e cd (st\<lparr>gas:=gas st - (costs\<^sub>e (PLUS e1 e2) e\<^sub>p e cd st)\<rparr>) = Normal ((KValue v1, Value t1), st'')"
        by (auto split:if_split_asm result.split_asm prod.split_asm Stackvalue.split_asm Type.split_asm)
      moreover from * ** have ***: "frame bal st''" using 21(1) asm by (auto simp add:frame_def split:if_split_asm)
      moreover from * ** *** obtain v2 t2 st''' where ****: "expr e2 e\<^sub>p e cd st'' = Normal ((KValue v2, Value t2), st''')"
        by (auto split:if_split_asm result.split_asm prod.split_asm Stackvalue.split_asm Type.split_asm)
      moreover from * ** *** **** have "frame bal st'''" using 21(2)[OF _ **] asm by (auto split:if_split_asm)
      moreover from * ** **** obtain v t where "add t1 t2 v1 v2 = Some (v, t)" by (auto split:if_split_asm option.split_asm)
      ultimately show "frame bal st'" by (auto split:if_split_asm)
    qed
  qed
next
  case (22 e1 e2 e\<^sub>p e cd st)
  show ?case (is "_ \<longrightarrow> ?RHS")
  proof
    assume asm: "address e \<noteq> (STR ''Victim'') \<and> fmlookup e\<^sub>p (STR ''Victim'') = Some (victim, SKIP)"
    show ?RHS
    proof (rule allI[OF allI[OF allI[OF impI]]])
      fix rv1 and st' and bal
      assume *: "frame bal st \<and> expr (MINUS e1 e2) e\<^sub>p e cd st = Normal (rv1, st')"
      moreover from * obtain v1 t1 st'' where **: "expr e1 e\<^sub>p e cd (st\<lparr>gas:=gas st - (costs\<^sub>e (MINUS e1 e2) e\<^sub>p e cd st)\<rparr>) = Normal ((KValue v1, Value t1), st'')"
        by (auto split:if_split_asm result.split_asm prod.split_asm Stackvalue.split_asm Type.split_asm)
      moreover from * ** have ***: "frame bal st''" using 22(1) asm by (auto simp add:frame_def split:if_split_asm)
      moreover from * ** *** obtain v2 t2 st''' where ****: "expr e2 e\<^sub>p e cd st'' = Normal ((KValue v2, Value t2), st''')"
        by (auto split:if_split_asm result.split_asm prod.split_asm Stackvalue.split_asm Type.split_asm)
      moreover from * ** *** **** have "frame bal st'''" using 22(2)[OF _ **] asm by (auto split:if_split_asm)
      moreover from * ** **** obtain v t where "sub t1 t2 v1 v2 = Some (v, t)" by (auto split:if_split_asm option.split_asm)
      ultimately show "frame bal st'" by (auto split:if_split_asm)
    qed
  qed
next
  case (23 e1 e2 e\<^sub>p e cd st)
  show ?case (is "_ \<longrightarrow> ?RHS")
  proof
    assume asm: "address e \<noteq> (STR ''Victim'') \<and> fmlookup e\<^sub>p (STR ''Victim'') = Some (victim, SKIP)"
    show ?RHS
    proof (rule allI[OF allI[OF allI[OF impI]]])
      fix rv1 and st' and bal
      assume *: "frame bal st \<and> expr (LESS e1 e2) e\<^sub>p e cd st = Normal (rv1, st')"
      moreover from * obtain v1 t1 st'' where **: "expr e1 e\<^sub>p e cd (st\<lparr>gas:=gas st - (costs\<^sub>e (LESS e1 e2) e\<^sub>p e cd st)\<rparr>) = Normal ((KValue v1, Value t1), st'')"
        by (auto split:if_split_asm result.split_asm prod.split_asm Stackvalue.split_asm Type.split_asm)
      moreover from * ** have ***: "frame bal st''" using 23(1) asm by (auto simp add:frame_def split:if_split_asm)
      moreover from * ** *** obtain v2 t2 st''' where ****: "expr e2 e\<^sub>p e cd st'' = Normal ((KValue v2, Value t2), st''')"
        by (auto split:if_split_asm result.split_asm prod.split_asm Stackvalue.split_asm Type.split_asm)
      moreover from * ** *** **** have "frame bal st'''" using 23(2)[OF _ **] asm by (auto split:if_split_asm)
      moreover from * ** **** obtain v t where "Valuetypes.less t1 t2 v1 v2 = Some (v, t)" by (auto split:if_split_asm option.split_asm)
      ultimately show "frame bal st'" by (auto split:if_split_asm)
    qed
  qed
next
  case (24 e1 e2 e\<^sub>p e cd st)
  show ?case (is "_ \<longrightarrow> ?RHS")
  proof
    assume asm: "address e \<noteq> (STR ''Victim'') \<and> fmlookup e\<^sub>p (STR ''Victim'') = Some (victim, SKIP)"
    show ?RHS
    proof (rule allI[OF allI[OF allI[OF impI]]])
      fix rv1 and st' and bal
      assume *: "frame bal st \<and> expr (EQUAL e1 e2) e\<^sub>p e cd st = Normal (rv1, st')"
      moreover from * obtain v1 t1 st'' where **: "expr e1 e\<^sub>p e cd (st\<lparr>gas:=gas st - (costs\<^sub>e (EQUAL e1 e2) e\<^sub>p e cd st)\<rparr>) = Normal ((KValue v1, Value t1), st'')"
        by (auto split:if_split_asm result.split_asm prod.split_asm Stackvalue.split_asm Type.split_asm)
      moreover from * ** have ***: "frame bal st''" using 24(1) asm by (auto simp add:frame_def split:if_split_asm)
      moreover from * ** *** obtain v2 t2 st''' where ****: "expr e2 e\<^sub>p e cd st'' = Normal ((KValue v2, Value t2), st''')"
        by (auto split:if_split_asm result.split_asm prod.split_asm Stackvalue.split_asm Type.split_asm)
      moreover from * ** *** **** have "frame bal st'''" using 24(2)[OF _ **] asm by (auto split:if_split_asm)
      moreover from * ** **** obtain v t where "Valuetypes.equal t1 t2 v1 v2 = Some (v, t)" by (auto split:if_split_asm option.split_asm)
      ultimately show "frame bal st'" by (auto split:if_split_asm)
    qed
  qed
next
  case (25 e1 e2 e\<^sub>p e cd st)
  show ?case (is "_ \<longrightarrow> ?RHS")
  proof
    assume asm: "address e \<noteq> (STR ''Victim'') \<and> fmlookup e\<^sub>p (STR ''Victim'') = Some (victim, SKIP)"
    show ?RHS
    proof (rule allI[OF allI[OF allI[OF impI]]])
      fix rv1 and st' and bal
      assume *: "frame bal st \<and> expr (AND e1 e2) e\<^sub>p e cd st = Normal (rv1, st')"
      moreover from * obtain v1 t1 st'' where **: "expr e1 e\<^sub>p e cd (st\<lparr>gas:=gas st - (costs\<^sub>e (AND e1 e2) e\<^sub>p e cd st)\<rparr>) = Normal ((KValue v1, Value t1), st'')"
        by (auto split:if_split_asm result.split_asm prod.split_asm Stackvalue.split_asm Type.split_asm)
      moreover from * ** have ***: "frame bal st''" using 25(1) asm by (auto simp add:frame_def split:if_split_asm)
      moreover from * ** *** obtain v2 t2 st''' where ****: "expr e2 e\<^sub>p e cd st'' = Normal ((KValue v2, Value t2), st''')"
        by (auto split:if_split_asm result.split_asm prod.split_asm Stackvalue.split_asm Type.split_asm)
      moreover from * ** *** **** have "frame bal st'''" using 25(2)[OF _ **] asm by (auto split:if_split_asm)
      moreover from * ** **** obtain v t where "Valuetypes.vtand t1 t2 v1 v2 = Some (v, t)" by (auto split:if_split_asm option.split_asm)
      ultimately show "frame bal st'" by (auto split:if_split_asm)
    qed
  qed
next
  case (26 e1 e2 e\<^sub>p e cd st)
  show ?case (is "_ \<longrightarrow> ?RHS")
  proof
    assume asm: "address e \<noteq> (STR ''Victim'') \<and> fmlookup e\<^sub>p (STR ''Victim'') = Some (victim, SKIP)"
    show ?RHS
    proof (rule allI[OF allI[OF allI[OF impI]]])
      fix rv1 and st' and bal
      assume *: "frame bal st \<and> expr (OR e1 e2) e\<^sub>p e cd st = Normal (rv1, st')"
      moreover from * obtain v1 t1 st'' where **: "expr e1 e\<^sub>p e cd (st\<lparr>gas:=gas st - (costs\<^sub>e (OR e1 e2) e\<^sub>p e cd st)\<rparr>) = Normal ((KValue v1, Value t1), st'')"
        by (auto split:if_split_asm result.split_asm prod.split_asm Stackvalue.split_asm Type.split_asm)
      moreover from * ** have ***: "frame bal st''" using 26(1) asm by (auto simp add:frame_def split:if_split_asm)
      moreover from * ** *** obtain v2 t2 st''' where ****: "expr e2 e\<^sub>p e cd st'' = Normal ((KValue v2, Value t2), st''')"
        by (auto split:if_split_asm result.split_asm prod.split_asm Stackvalue.split_asm Type.split_asm)
      moreover from * ** *** **** have "frame bal st'''" using 26(2)[OF _ **] asm by (auto split:if_split_asm)
      moreover from * ** **** obtain v t where "Valuetypes.vtor t1 t2 v1 v2 = Some (v, t)" by (auto split:if_split_asm option.split_asm)
      ultimately show "frame bal st'" by (auto split:if_split_asm)
    qed
  qed
next
  case (27 i e\<^sub>p e cd st)
  show ?case using 27(1)[of "()" "st\<lparr>gas:=gas st - (costs\<^sub>e (LVAL i) e\<^sub>p e cd st)\<rparr>"] apply safe by (auto simp add:frame_def split:if_split_asm)
next
  case (28 i xe e\<^sub>p e cd st)
  show ?case (is "_ \<longrightarrow> ?RHS")
  proof
    assume asm: "address e \<noteq> (STR ''Victim'') \<and> fmlookup e\<^sub>p (STR ''Victim'') = Some (victim, SKIP)"
    show ?RHS
    proof (rule allI[OF allI[OF allI[OF impI]]])
      fix rv1 and st' and bal
      assume *: "frame bal st \<and> expr (CALL i xe) e\<^sub>p e cd st = Normal (rv1, st')"
      moreover from * have a1: "(applyf (costs\<^sub>e (CALL i xe) e\<^sub>p e cd) \<bind> (\<lambda>g. assert Gas (\<lambda>st. gas st \<le> g) (modify (\<lambda>st. st\<lparr>gas := gas st - g\<rparr>))))  st = Normal ((), st\<lparr>gas := gas st - costs\<^sub>e (CALL i xe) e\<^sub>p e cd st\<rparr>)" by auto
      moreover from * obtain ct bla where **: "fmlookup e\<^sub>p (address e) = Some (ct, bla)"
        by (auto split:if_split_asm option.split_asm)
      moreover from * ** obtain fp f x where ***: "fmlookup ct i = Some (Method (fp, f, Some x))"
        by (auto split:if_split_asm option.split_asm Member.split_asm)
      moreover define e' where "e' = ffold_init ct (emptyEnv (address e) (sender e) (svalue e)) (fmdom ct)"
      moreover from * ** *** obtain e'' cd' st'' st''' where ****: "load False fp xe e\<^sub>p e' emptyStore (st\<lparr>gas:=gas st - (costs\<^sub>e (CALL i xe) e\<^sub>p e cd st), stack:=emptyStore\<rparr>) e cd (st\<lparr>gas:=gas st - (costs\<^sub>e (CALL i xe) e\<^sub>p e cd st)\<rparr>) = Normal ((e'', cd', st''), st''')"
        using e'_def by (auto split:if_split_asm result.split_asm)
      moreover from * **** have f1: "frame bal st''" and ad: "address e' = address e''"
        using asm 28(1)[OF _ ** _ *** _ _ _ _ e'_def, of _ "st\<lparr>gas := gas st - costs\<^sub>e (CALL i xe) e\<^sub>p e cd st\<rparr>" bla "(fp, f, Some x)" fp "(f, Some x)" f "Some x" x "st\<lparr>gas := gas st - costs\<^sub>e (CALL i xe) e\<^sub>p e cd st, stack := emptyStore\<rparr>" "st\<lparr>gas := gas st - costs\<^sub>e (CALL i xe) e\<^sub>p e cd st\<rparr>"] by (auto simp add:frame_def split:if_split_asm result.split_asm)
      moreover from e'_def have ad2: "address e = address e'" using ffold_init_ad_same[of ct "(emptyEnv (address e) (sender e) (svalue e))" "(fmdom ct)" e'] by simp
      moreover from * ** *** **** e'_def obtain st'''' where *****: "stmt f e\<^sub>p e'' cd' st'' = Normal ((), st'''')" by (auto split:if_split_asm result.split_asm)
      moreover from f1 ad ad2 asm ***** have f2:"frame bal st''''"
        using 28(2)[OF a1 ** _ *** _ _ _ _ e'_def _ ****, of bla "(fp, f, Some x)" "(f, Some x)" f "Some x" x e'' "(cd', st'')" "cd'" "st''" st''' st''' "()" st''] by (simp add:frame_def)
      moreover from * ** *** **** ***** f1 f2 e'_def obtain rv st''''' where ******: "expr x e\<^sub>p e'' cd' st'''' = Normal (rv, st''''')" by (auto split:if_split_asm result.split_asm)
      ultimately have "st' = st'''''\<lparr>stack:=stack st''', memory := memory st'''\<rparr>" apply safe by auto
      moreover from f1 f2 ad ad2 asm a1 ***** ****** have "\<forall>rv4 st4' bal.
        frame bal st'''' \<and>
        local.expr x e\<^sub>p e'' cd' st'''' = Normal (rv4, st4') \<longrightarrow>
        frame bal st4'" using e'_def asm 28(3)[OF a1 ** _ *** _ _ _ _ e'_def _ **** _ _ _ _ *****, of bla "(fp, f, Some x)" " (f, Some x)" "Some x" x "(cd', st'')" st'' st''' st''' "()"] apply safe by auto
      with ****** f2 have "frame bal st'''''" by blast
      ultimately show "frame bal st'" by (simp add:frame_def)
    qed
  qed
next
  case (29 ad i xe val e\<^sub>p e cd st)
  show ?case (is "_ \<longrightarrow> ?RHS")
  proof
    assume asm: "address e \<noteq> (STR ''Victim'') \<and> fmlookup e\<^sub>p (STR ''Victim'') = Some (victim, SKIP)"
    show ?RHS
    proof (rule allI[OF allI[OF allI[OF impI]]])
      fix rv1 and st' and bal
      assume *: "frame bal st \<and> expr (ECALL ad i xe val) e\<^sub>p e cd st = Normal (rv1, st')"
      moreover from * have a1: "(applyf (costs\<^sub>e (ECALL ad i xe val) e\<^sub>p e cd) \<bind> (\<lambda>g. assert Gas (\<lambda>st. gas st \<le> g) (modify (\<lambda>st. st\<lparr>gas := gas st - g\<rparr>))))  st = Normal ((), st\<lparr>gas := gas st - costs\<^sub>e (ECALL ad i xe val) e\<^sub>p e cd st\<rparr>)" by auto
      moreover from * obtain adv st'' where **: "expr ad e\<^sub>p e cd (st\<lparr>gas:=gas st - (costs\<^sub>e (ECALL ad i xe val) e\<^sub>p e cd st)\<rparr>) = Normal ((KValue adv, Value TAddr), st'')"
        by (auto split:if_split_asm result.split_asm Stackvalue.split_asm Type.split_asm Types.split_asm)
      moreover from * ** have f1: "frame bal st''"using asm 29(1) by (auto simp add:frame_def split:if_split_asm)
      moreover from * ** obtain ct bla where ***: "fmlookup e\<^sub>p adv = Some (ct, bla)"
        by (auto split:if_split_asm option.split_asm)
      moreover from * ** *** obtain fp f x where ****: "fmlookup ct i = Some (Method (fp, f, Some x))"
        by (auto split:if_split_asm option.split_asm Member.split_asm)
      moreover from * ** *** **** obtain v t st''' where *****: "expr val e\<^sub>p e cd st'' = Normal ((KValue v, Value t), st''')" by (auto split:if_split_asm result.split_asm Stackvalue.split_asm Type.split_asm)
      moreover from f1 ***** asm have f2: "frame bal st'''" and f3: "frame bal (st'''\<lparr>stack := emptyStore, memory := emptyStore\<rparr>)" using asm 29(2)[OF a1 ** _ _ _ _ *** _ ****] by (auto simp add:frame_def)
      moreover define e' where "e' = ffold_init ct (emptyEnv adv (address e) v) (fmdom ct)"
      moreover from * ** *** **** ***** obtain e'' cd' st'''' st''''' where *******: "load True fp xe e\<^sub>p e' emptyStore (st'''\<lparr>stack:=emptyStore, memory:=emptyStore\<rparr>) e cd st''' = Normal ((e'', cd', st''''), st''''')"
        using e'_def by (auto split:if_split_asm result.split_asm option.split_asm)
      moreover have "(\<forall>ev cda st st' bal.
        local.load True fp xe e\<^sub>p e' emptyStore (st'''\<lparr>stack := emptyStore, memory := emptyStore\<rparr>) e cd st''' = Normal ((ev, cda, st), st') \<longrightarrow>
        (frame bal (st'''\<lparr>stack := emptyStore, memory := emptyStore\<rparr>) \<longrightarrow> frame bal st) \<and>
        (frame bal st''' \<longrightarrow> frame bal st') \<and> address e' = address ev \<and> sender e' = sender ev \<and> svalue e' = svalue ev)"
        using 29(3)[OF a1 ** _ _ _ _ *** _ **** _ _ _ _ ***** _ _ _ e'_def, of "KValue adv" "Value TAddr" TAddr bla "(fp, f, Some x)" fp "(f, Some x)" f "Some x" x "KValue v" "Value t" t "st'''\<lparr>stack := emptyStore, memory := emptyStore\<rparr>" st'''] asm ******* by simp
      then have "frame bal st'''' \<and> frame bal st''''' \<and> address e' = address e''" using ******* f2 f3 by blast
      then have f4: "frame bal st''''" and ad1: "address e' = address e''" by auto
      moreover from * ** *** **** ***** ******* e'_def obtain acc where ******: "Accounts.transfer (address e) adv v (accounts st'''') = Some acc" by (auto split:if_split_asm option.split_asm)
      then have ******: "Accounts.transfer (address e) adv v (accounts st'''') = Some acc" by (auto split:if_split_asm option.split_asm)
      moreover from f4 have f5: "frame bal (st''''\<lparr>accounts := acc\<rparr>)" using transfer_frame[OF ******] asm by simp
      moreover from e'_def have ad2: "adv = address e'" using ffold_init_ad_same[of ct "(emptyEnv adv (address e) v)" "(fmdom ct)" e'] by simp
      moreover from * ** *** **** ***** ****** ******* ****** obtain st'''''' where ********: "stmt f e\<^sub>p e'' cd' (st''''\<lparr>accounts := acc\<rparr>) = Normal ((), st'''''')"
        using e'_def by (auto simp del: transfer.simps split:if_split_asm result.split_asm)
      moreover have "adv \<noteq> STR ''Victim''"
      proof (rule ccontr)
        assume "\<not> adv \<noteq> STR ''Victim''"
        with asm ** *** **** show False using victim_def fmap_of_list_SomeD[of "[(STR ''balance'', Var (STMap TAddr (STValue (TUInt 256)))), (STR ''deposit'', Method ([], deposit, None)), (STR ''withdraw'', Method ([], keep, None))]"] by auto
      qed
      with ad1 ad2 have ad: "address e'' \<noteq> STR ''Victim'' \<and> fmlookup e\<^sub>p (STR ''Victim'') = Some (victim, SKIP)" using asm by simp
      then have "(\<forall>bal. frame bal (st''''\<lparr>accounts := acc\<rparr>) \<longrightarrow> frame bal st'''''')" using 29(4)[OF a1 ** _ _ _ _ *** _ **** _ _ _ _ ***** _ _ _ _ _ ******* _ _ _ ******, of "KValue adv" "Value TAddr" TAddr bla "(fp, f, Some x)" "(f, Some x)" f "Some x" x "KValue v" "Value t" t e'' "(cd', st'''')" cd'  st'''''  st''''' "()" "st''''\<lparr>accounts := acc\<rparr>"] ******** e'_def by auto
      then have f4: "frame bal st''''''" using f5 ******** by auto
      moreover from * ** *** **** ***** ****** ******* ******** obtain rv st''''''' where *********: "expr x e\<^sub>p e'' cd' st'''''' = Normal (rv, st''''''')"
        using e'_def by (auto split:if_split_asm result.split_asm)
      ultimately have "st' = st'''''''\<lparr>stack:=stack st''''', memory := memory st'''''\<rparr>" apply safe by auto
      moreover from ad have "\<forall>rv4 st4' bal.
        frame bal st'''''' \<and>
        local.expr x e\<^sub>p e'' cd' st'''''' = Normal (rv4, st4') \<longrightarrow>
        frame bal st4'"
        using e'_def 29(5)[OF a1 ** _ _ _ _ *** _ **** _ _ _ _ ***** _ _ _ _ _ ******* _ _ _ ****** _ ********, of "KValue adv" "Value TAddr" TAddr bla "(fp, f, Some x)"] by auto
      then have"frame bal st'''''''" using f4 ********* by blast
      ultimately show "frame bal st'" by (simp add:frame_def)
    qed
  qed
next
  case (30 cp i\<^sub>p t\<^sub>p pl e el e\<^sub>p e\<^sub>v' cd' st' e\<^sub>v cd st)
  show ?case (is "_ \<longrightarrow> ?RHS")
  proof
    assume asm: "address e\<^sub>v \<noteq> (STR ''Victim'') \<and> fmlookup e\<^sub>p (STR ''Victim'') = Some (victim, SKIP)"
    show ?RHS
    proof (rule allI[OF allI[OF allI[OF allI[OF allI[OF impI]]]]])
      fix ev and cda and sta and st'a and bal
      assume *: "local.load cp ((i\<^sub>p, t\<^sub>p) # pl) (e # el) e\<^sub>p e\<^sub>v' cd' st' e\<^sub>v cd st = Normal ((ev, cda, sta), st'a)"
      moreover from * obtain v t st'' where **: "expr e e\<^sub>p e\<^sub>v cd st = Normal ((v,t),st'')" by (auto split: result.split_asm)
      moreover from * ** obtain cd'' e\<^sub>v'' st''' where ***: "decl i\<^sub>p t\<^sub>p (Some (v,t)) cp cd (memory st'') cd' e\<^sub>v' st' = Normal ((cd'', e\<^sub>v''),st''')" by (auto split: result.split_asm)
      moreover from *** have ad: "address e\<^sub>v' = address e\<^sub>v'' \<and> sender e\<^sub>v' = sender e\<^sub>v'' \<and> svalue e\<^sub>v' = svalue e\<^sub>v''" using decl_gas_address by simp
      moreover from * ** *** obtain ev' cda' sta' st'a' where ****: "local.load cp pl el e\<^sub>p e\<^sub>v'' cd'' st''' e\<^sub>v cd st''= Normal ((ev', cda', sta'), st'a')" by (auto split: result.split_asm)
      ultimately have "ev = ev'" and "sta = sta'" and "st'a = st'a'" by simp+
      
      from **** asm have IH: "(frame bal st''' \<longrightarrow> frame bal sta') \<and>
        (frame bal st'' \<longrightarrow> frame bal st'a') \<and> 
        address e\<^sub>v'' = address ev' \<and> sender e\<^sub>v'' = sender ev' \<and> svalue e\<^sub>v'' = svalue ev'" using 30(2)[OF ** _ _ _ ***, of st'' "()" cd'' e\<^sub>v'' st''' st''' "()" st''] apply safe by (auto simp add:frame_def)
      show "(frame bal st' \<longrightarrow> frame bal sta) \<and> (frame bal st \<longrightarrow> frame bal st'a) \<and> address e\<^sub>v' = address ev \<and> sender e\<^sub>v' = sender ev \<and> svalue e\<^sub>v' = svalue ev"
      proof (rule conj3)
        show "frame bal st' \<longrightarrow> frame bal sta"
        proof
          assume "frame bal st'"
          with * ** *** have "frame bal st'''" using decl_frame by simp
          with IH have "frame bal sta'" by simp
          with `sta = sta'` show "frame bal sta" by simp
        qed
      next
        show "frame bal st \<longrightarrow> frame bal st'a"
        proof
          assume "frame bal st"
          with ** have "frame bal st''" using 30(1) asm by simp
          with IH have "frame bal st'a'" by simp
          with `st'a = st'a'` show "frame bal st'a" by simp
        qed
      next
        from ad IH show "address e\<^sub>v' = address ev \<and> sender e\<^sub>v' = sender ev \<and> svalue e\<^sub>v' = svalue ev" using `ev = ev'` by simp
      qed
    qed
  qed
next
  case (31 vv vw vx vy vz wa wb wc wd st)
  then show ?case by simp
next
  case (32 we wf wg wh wi wj wk wl wm st)
  then show ?case by simp
next
  case (33 wn wo e\<^sub>v' cd' st' e\<^sub>v cd st)
  then show ?case by simp
next
  case (34 i e\<^sub>p e cd st)
  show ?case (is "_ \<longrightarrow> ?RHS")
  proof
    assume asm: "address e \<noteq> (STR ''Victim'') \<and> fmlookup e\<^sub>p (STR ''Victim'') = Some (victim, SKIP)"
    show ?RHS
    proof (rule allI[OF allI[OF allI[OF impI]]])
      fix rv3 and st3' and bal
      assume *: "frame bal st \<and> local.rexp (L.Id i) e\<^sub>p e cd st = Normal (rv3, st3')"
      show "frame bal st3'"
      proof (cases "fmlookup (denvalue e) i")
        case None
        with * show ?thesis by simp
      next
        case (Some a)
        then show ?thesis
        proof (cases a)
          case (Pair tp b)
          then show ?thesis
          proof (cases b)
            case (Stackloc l)
            then show ?thesis
            proof (cases "accessStore l (stack st)")
              case None
              with * Some Pair Stackloc show ?thesis by (auto split: Type.split_asm STypes.split_asm)
            next
              case s2: (Some a)
              with * Some Pair Stackloc s2 show ?thesis by (auto split: Type.split_asm STypes.split_asm Stackvalue.split_asm)
            qed
          next
            case (Storeloc x2)
            with * Some Pair Storeloc show ?thesis by (auto split: Type.split_asm STypes.split_asm option.split_asm)
          qed
        qed
      qed
    qed
  qed
next
  case (35 i r e\<^sub>p e cd st)
  show ?case (is "_ \<longrightarrow> ?RHS")
  proof
    assume asm: "address e \<noteq> (STR ''Victim'') \<and> fmlookup e\<^sub>p (STR ''Victim'') = Some (victim, SKIP)"
    show ?RHS
    proof (rule allI[OF allI[OF allI[OF impI]]])
      fix rv3 and st3' and bal
      assume *: "frame bal st \<and> local.rexp (L.Ref i r) e\<^sub>p e cd st = Normal (rv3, st3')"
      show "frame bal st3'"
      proof (cases "fmlookup (denvalue e) i")
        case None
        with * show ?thesis by simp
      next
        case (Some a)
        then show ?thesis
        proof (cases a)
          case (Pair tp b)
          then show ?thesis
          proof (cases b)
            case (Stackloc l')
            then show ?thesis
            proof (cases "accessStore l' (stack st)")
              case None
              with * Some Pair Stackloc show ?thesis by simp
            next
              case s2: (Some a)
              then show ?thesis
              proof (cases a)
                case (KValue x1)
                with * Some Pair Stackloc s2 show ?thesis by simp
              next
                case (KCDptr l'')
                then show ?thesis
                proof (cases tp)
                  case (Value x1)
                  with * Some Pair Stackloc s2 KCDptr show ?thesis by simp
                next
                  case (Calldata t)
                  with * Some Pair Stackloc s2 KCDptr obtain l''' t' st' where **: "msel False t l'' r e\<^sub>p e cd st = Normal ((l''',t'), st')" by (auto split: Type.split_asm STypes.split_asm result.split_asm)
                  then have "\<forall>rv1 st1' bal.
                  frame bal st \<and>
                  local.msel False t l'' r e\<^sub>p e cd st = Normal (rv1, st1') \<longrightarrow>
                  frame bal st1'" using asm 35(1)[OF Some Pair Stackloc _ s2 KCDptr Calldata] by auto
                  with * ** have f2: "frame bal st'" by blast
                  then show ?thesis
                  proof (cases t')
                    case (MTArray x t'')
                    then show ?thesis
                    proof (cases "accessStore l''' cd")
                      case None
                      with * ** Some Pair Stackloc s2 KCDptr Calldata MTArray show ?thesis by simp
                    next
                      case s3: (Some a)
                      then show ?thesis
                      proof (cases a)
                        case (MValue x1)
                        with * ** Some Pair Stackloc s2 KCDptr Calldata MTArray s3 show ?thesis by simp
                      next
                        case (MPointer x2)
                        with * ** f2 Some Pair Stackloc s2 KCDptr Calldata MTArray s3 show ?thesis by simp
                      qed
                    qed
                  next
                    case (MTValue t''')
                    then show ?thesis
                    proof (cases "accessStore l''' cd")
                      case None
                      with * ** Some Pair Stackloc s2 KCDptr Calldata MTValue show ?thesis by simp
                    next
                      case s3: (Some a)
                      then show ?thesis
                      proof (cases a)
                        case (MValue x1)
                        with * ** f2 Some Pair Stackloc s2 KCDptr Calldata MTValue s3 show ?thesis by simp
                      next
                        case (MPointer x2)
                        with * ** Some Pair Stackloc s2 KCDptr Calldata MTValue s3 show ?thesis by simp
                      qed
                    qed
                  qed
                next
                  case (Memory x3)
                  with * Some Pair Stackloc s2 KCDptr show ?thesis by simp
                next
                  case (Storage x4)
                  with * Some Pair Stackloc s2 KCDptr show ?thesis by simp
                qed
              next
                case (KMemptr l'')
                then show ?thesis
                proof (cases tp)
                  case (Value x1)
                  with * Some Pair Stackloc s2 KMemptr show ?thesis by simp
                next
                  case (Calldata x2)
                  with * Some Pair Stackloc s2 KMemptr show ?thesis by simp
                next
                  case (Memory t)
                  with * Some Pair Stackloc s2 KMemptr obtain l''' t' st' where **: "msel True t l'' r e\<^sub>p e cd st = Normal ((l''',t'), st')" by (auto split: Type.split_asm STypes.split_asm result.split_asm)
                  then have "\<forall>rv1 st1' bal. frame bal st \<and>
                  local.msel True t l'' r e\<^sub>p e cd st = Normal (rv1, st1') \<longrightarrow>
                  frame bal st1'" using asm 35(2)[OF Some Pair Stackloc _ s2 KMemptr Memory, of st] by auto
                  with * ** have f2: "frame bal st'" by blast
                  then show ?thesis
                  proof (cases t')
                    case (MTArray x11 x12)
                    then show ?thesis
                    proof (cases "accessStore l''' (memory st')")
                      case None
                      with * ** Some Pair Stackloc s2 KMemptr Memory MTArray show ?thesis by simp
                    next
                      case s3: (Some a)
                      then show ?thesis
                      proof (cases a)
                        case (MValue x1)
                        with * ** Some Pair Stackloc s2 KMemptr Memory MTArray s3 show ?thesis by simp
                      next
                        case (MPointer x2)
                        with * ** f2 Some Pair Stackloc s2 KMemptr Memory MTArray s3 show ?thesis by simp
                      qed
                    qed
                  next
                    case (MTValue x2)
                    then show ?thesis
                    proof (cases "accessStore l''' (memory st')")
                      case None
                      with * ** Some Pair Stackloc s2 KMemptr Memory MTValue show ?thesis by simp
                    next
                      case s3: (Some a)
                      then show ?thesis
                      proof (cases a)
                        case (MValue x1)
                        with * ** f2 Some Pair Stackloc s2 KMemptr Memory MTValue s3 show ?thesis by simp
                      next
                        case (MPointer x2)
                        with * ** Some Pair Stackloc s2 KMemptr Memory MTValue s3 show ?thesis by simp
                      qed
                    qed
                  qed
                next
                  case (Storage x4)
                  with * Some Pair Stackloc s2 KMemptr show ?thesis by simp
                qed
              next
                case (KStoptr l'')
                then show ?thesis
                proof (cases tp)
                  case (Value x1)
                  with * Some Pair Stackloc s2 KStoptr show ?thesis by simp
                next
                  case (Calldata x2)
                  with * Some Pair Stackloc s2 KStoptr show ?thesis by simp
                next
                  case (Memory x3)
                  with * Some Pair Stackloc s2 KStoptr show ?thesis by simp
                next
                  case (Storage t)
                  with * Some Pair Stackloc s2 KStoptr obtain l''' t' st' where **: "ssel t l'' r e\<^sub>p e cd st = Normal ((l''',t'), st')" by (auto split: Type.split_asm STypes.split_asm result.split_asm)
                  then have "\<forall>rv2 st2' bal.
                  frame bal st \<and>
                  local.ssel t l'' r e\<^sub>p e cd st = Normal (rv2, st2') \<longrightarrow>
                  frame bal st2'" using asm 35(3)[OF Some Pair Stackloc _ s2 KStoptr Storage, of st] by auto
                  with * ** have "frame bal st'" by blast
                  with * ** Some Pair Stackloc s2 KStoptr Storage show ?thesis by (simp split: STypes.split_asm option.split_asm)
                qed
              qed
            qed
          next
            case (Storeloc l')
            then show ?thesis
            proof (cases tp)
              case (Value x1)
              with * Some Pair Storeloc show ?thesis by simp
            next
              case (Calldata x2)
              with * Some Pair Storeloc show ?thesis by simp
            next
              case (Memory x3)
              with * Some Pair Storeloc show ?thesis by simp
            next
              case (Storage t)
              with * Some Pair Storeloc obtain l'' t' st' where **: "ssel t l' r e\<^sub>p e cd st = Normal ((l'',t'), st')" by (auto split: result.split_asm)
              then have "\<forall>rv2 st2' bal.
              frame bal st \<and>
              local.ssel t l' r e\<^sub>p e cd st = Normal (rv2, st2') \<longrightarrow>
              frame bal st2'" using asm 35(4)[OF Some Pair Storeloc Storage] by auto
              with * ** have "frame bal st'" by blast
              with * ** Some Pair Storeloc Storage show ?thesis by (simp split: STypes.split_asm option.split_asm)
            qed
          qed
        qed
      qed
    qed
  qed
next
  case (36 e\<^sub>p e cd st)
  show ?case (is "?LHS \<longrightarrow> ?RHS")
  proof
    assume *: "fmlookup e\<^sub>p STR ''Victim'' = Some (victim, SKIP)"
    show ?RHS (is "\<forall>st6'. ?RHS st6'")
    proof
      fix st6'
      show "?RHS st6'" (is "?LHS \<longrightarrow> ?RHS")
      proof
        assume t0: "stmt SKIP e\<^sub>p e cd st = Normal ((), st6')"
        show ?RHS (is "?LHS \<and> ?RHS")
        proof
          show "?LHS"
          proof
            assume ad: "address e \<noteq> STR ''Victim''"
            show "\<forall>bal. frame bal st \<longrightarrow> frame bal st6'"
            proof
              fix bal
              show "frame bal st \<longrightarrow> frame bal st6'"
              proof
                assume "frame bal st"
                with t0 * show "frame bal st6'" by (auto simp add: frame_def split:if_split_asm)
              qed
            qed
          qed
        next
          show "?RHS" (is "?LHS \<longrightarrow> ?RHS")
          proof
            assume "address e = STR ''Victim''"
            show ?RHS (is "?A \<and> (?B \<and> ?C)")
            proof (rule conj3)
              show ?A (is "\<forall>s val bal x. ?LHS s val bal x")
              proof (rule allI[OF allI[OF allI[OF allI]]])
                fix s val bal x
                show "?LHS s val bal x" (is "?LHS \<longrightarrow> ?RHS")
                proof
                  assume ?LHS
                  then show ?RHS by simp
                qed
              qed
            next
              show ?B (is "\<forall>s bal x. ?LHS s bal x")
              proof (rule allI[OF allI[OF allI]])
                fix s bal x
                show "?LHS s bal x" (is "?LHS \<longrightarrow> ?RHS")
                proof
                  assume ?LHS
                  then show ?RHS by simp
                qed
              qed
            next
              show ?C (is "\<forall>s bal. ?LHS s bal")
              proof (rule allI[OF allI])
                fix s bal
                show "?LHS s bal" (is "?LHS \<longrightarrow> ?RHS")
                proof
                  assume ?LHS
                  then show ?RHS by simp
                qed
              qed
            qed
          qed
        qed
      qed
    qed
  qed
next
  case (37 lv ex e\<^sub>p env cd st)
  show ?case (is "?LHS \<longrightarrow> ?RHS")
  proof
    assume 0: "fmlookup e\<^sub>p STR ''Victim'' = Some (victim, SKIP)"
    show ?RHS (is "\<forall>st6'. ?RHS st6'")
    proof
      fix st6'
      show "?RHS st6'" (is "?LHS \<longrightarrow> ?RHS")
      proof
        assume *: "stmt (ASSIGN lv ex) e\<^sub>p env cd st = Normal ((), st6')"
        show ?RHS (is "?LHS \<and> ?RHS")
        proof
          show "?LHS"
          proof
            assume asm: "address env \<noteq> STR ''Victim''"
            show "\<forall>bal. frame bal st \<longrightarrow> frame bal st6'"
            proof
              fix bal
              show "frame bal st \<longrightarrow> frame bal st6'"
              proof
                assume "frame bal st"
                with * have a1: "(applyf (costs (ASSIGN lv ex) e\<^sub>p env cd) \<bind> (\<lambda>g. assert Gas (\<lambda>st. gas st \<le> g) (modify (\<lambda>st. st\<lparr>gas := gas st - g\<rparr>)))) st =
                  Normal ((), st\<lparr>gas:=gas st - costs (ASSIGN lv ex) e\<^sub>p env cd st\<rparr>)" 
                  and f1: "frame bal (st\<lparr>gas:=gas st - costs (ASSIGN lv ex) e\<^sub>p env cd st\<rparr>)" by (auto simp add:frame_def)
                moreover from * obtain kv kt st' where **: "expr ex e\<^sub>p env cd (st\<lparr>gas:=gas st - costs (ASSIGN lv ex) e\<^sub>p env cd st\<rparr>) = Normal ((kv, kt), st')" by (auto split:if_split_asm result.split_asm)
                ultimately have "\<forall>rv4 st4' (ev4'::Environment) bal.
                  frame bal (st\<lparr>gas := gas st - costs (ASSIGN lv ex) e\<^sub>p env cd st\<rparr>) \<and>
                  local.expr ex e\<^sub>p env cd (st\<lparr>gas := gas st - costs (ASSIGN lv ex) e\<^sub>p env cd st\<rparr>) = Normal (rv4, st4') \<longrightarrow>
                  frame bal st4'" using asm 0 37(1) by simp
                with f1 ** have f2: "frame bal st'" by blast
                show "frame bal st6'"
                proof (cases kv)
                  case (KValue v)
                  then show ?thesis
                  proof (cases kt)
                    case (Value t)
                    with * ** KValue obtain rv rt st'' where ***: "lexp lv e\<^sub>p env cd st' = Normal ((rv,rt), st'')" by (auto split:if_split_asm result.split_asm)
                    with KValue Value have "\<forall>rv5 st5' (ev5'::Environment) bal.
                    frame bal st' \<and>
                    local.lexp lv e\<^sub>p env cd st' = Normal (rv5, st5') \<longrightarrow>
                    frame bal st5'" using asm 0 37(2)[OF a1 **] by simp
                    with f2 *** have f3: "frame bal st''" by blast
                    then show ?thesis
                    proof (cases rv)
                      case (LStackloc l')
                      then show ?thesis
                      proof (cases rt)
                        case v2: (Value t')
                        then show ?thesis
                        proof (cases "Valuetypes.convert t t' v")
                          case None
                          with * ** *** KValue Value LStackloc v2 show ?thesis by (auto split:if_split_asm)
                        next
                          case (Some a)
                          then show ?thesis
                          proof (cases a)
                            case (Pair v' b)
                            with * ** *** KValue Value LStackloc v2 Some have "st6' = st'' \<lparr>stack := updateStore l' (KValue v') (stack st'')\<rparr>" by (auto split:if_split_asm)
                            with f3 show ?thesis by (simp add:frame_def)
                          qed
                        qed
                      next
                        case (Calldata x2)
                        with * ** *** KValue Value LStackloc show ?thesis by (auto split:if_split_asm)
                      next
                        case (Memory x3)
                        with * ** *** KValue Value LStackloc show ?thesis by (auto split:if_split_asm)
                      next
                        case (Storage x4)
                        with * ** *** KValue Value LStackloc show ?thesis by (auto split:if_split_asm)
                      qed
                    next
                      case (LMemloc l')
                      then show ?thesis
                      proof (cases rt)
                        case v2: (Value t')
                        with * ** *** KValue Value LMemloc show ?thesis by (auto split:if_split_asm)
                      next
                        case (Calldata x2)
                        with * ** *** KValue Value LMemloc show ?thesis by (auto split:if_split_asm)
                      next
                        case (Memory x3)
                        then show ?thesis
                        proof (cases x3)
                          case (MTArray x11 x12)
                          with * ** *** KValue Value LMemloc Memory show ?thesis by (auto split:if_split_asm)
                        next
                          case (MTValue t')
                          then show ?thesis
                          proof (cases "Valuetypes.convert t t' v")
                            case None
                            with * ** *** KValue Value LMemloc Memory MTValue show ?thesis by (auto split:if_split_asm)
                          next
                            case (Some a)
                            then show ?thesis
                            proof (cases a)
                              case (Pair v' b)
                              with * ** *** KValue Value LMemloc Memory MTValue Some have "st6' = st'' \<lparr>memory := updateStore l' (MValue v') (memory st'')\<rparr>" by (auto split:if_split_asm)
                              with f3 show ?thesis by (simp add:frame_def)
                            qed
                          qed
                        qed
                      next
                        case (Storage x4)
                        with * ** *** KValue Value LMemloc Storage show ?thesis by (auto split:if_split_asm)
                      qed
                    next
                      case (LStoreloc l')
                      then show ?thesis
                      proof (cases rt)
                        case v2: (Value x1)
                        with * ** *** KValue Value LStoreloc show ?thesis by (auto split:if_split_asm)
                      next
                        case (Calldata x2)
                        with * ** *** KValue Value LStoreloc show ?thesis by (auto split:if_split_asm)
                      next
                        case (Memory x3)
                        with * ** *** KValue Value LStoreloc show ?thesis by (auto split:if_split_asm)
                      next
                        case (Storage x4)
                        then show ?thesis
                        proof (cases x4)
                          case (STArray x11 x12)
                          with * ** *** KValue Value LStoreloc Storage show ?thesis by (auto split:if_split_asm)
                        next
                          case (STMap x21 x22)
                          with * ** *** KValue Value LStoreloc Storage show ?thesis by (auto split:if_split_asm)
                        next
                          case (STValue t')
                          then show ?thesis
                          proof (cases "Valuetypes.convert t t' v")
                            case None
                            with * ** *** KValue Value LStoreloc Storage STValue show ?thesis by (auto split:if_split_asm)
                          next
                            case (Some a)
                            then show ?thesis
                            proof (cases a)
                              case (Pair v' b)
                              then show ?thesis
                              proof (cases "fmlookup (storage st'') (address env)")
                                case None
                                with * ** *** KValue Value LStoreloc Storage STValue Some Pair show ?thesis by (auto split:if_split_asm)
                              next
                                case s2: (Some s)
                                with * ** *** KValue Value LStoreloc Storage STValue Some Pair have "st6' = st''\<lparr>storage := fmupd (address env) (fmupd l' v' s) (storage st'')\<rparr>" by (auto split:if_split_asm)
                                with f3 show ?thesis using asm by (simp add:frame_def)
                              qed
                            qed
                          qed
                        qed
                      qed
                    qed
                  next
                    case (Calldata x2)
                    with * ** KValue show ?thesis by (auto split:if_split_asm)
                  next
                    case (Memory x3)
                    with * ** KValue show ?thesis by (auto split:if_split_asm)
                  next
                    case (Storage x4)
                    with * ** KValue show ?thesis by (auto split:if_split_asm)
                  qed
                next
                  case (KCDptr p)
                  then show ?thesis
                  proof (cases kt)
                    case (Value t)
                    with * ** KCDptr show ?thesis by (auto split:if_split_asm)
                  next
                    case (Calldata x2)
                    then show ?thesis
                    proof (cases x2)
                      case (MTArray x t)
                      with * ** KCDptr Calldata obtain rv rt st'' where ***: "lexp lv e\<^sub>p env cd st' = Normal ((rv,rt), st'')" by (auto split:if_split_asm result.split_asm)
                      with KCDptr Calldata MTArray have "\<forall>rv5 st5' (ev5'::Environment) bal.
                      frame bal st' \<and>
                      local.lexp lv e\<^sub>p env cd st' = Normal (rv5, st5') \<longrightarrow>
                      frame bal st5'" using asm 0 37(3)[OF a1 **] by auto
                      with f2 *** have f3: "frame bal st''" by blast
                      then show ?thesis
                      proof (cases rv)
                        case (LStackloc l')
                        then show ?thesis
                        proof (cases rt)
                          case (Value x1)
                          with * ** *** KCDptr Calldata MTArray LStackloc show ?thesis by (auto split:if_split_asm)
                        next
                          case c2: (Calldata x2)
                          with * ** *** KCDptr Calldata MTArray LStackloc show ?thesis by (auto split:if_split_asm)
                        next
                          case (Memory x3)
                          with f3 * ** *** KCDptr Calldata MTArray LStackloc show ?thesis by (auto simp add:frame_def split:if_split_asm)
                        next
                          case (Storage x4)
                          then show ?thesis
                          proof (cases "accessStore l' (stack st'')")
                            case None
                            with * ** *** KCDptr Calldata MTArray LStackloc Storage show ?thesis by (simp split:if_split_asm)
                          next
                            case (Some sv)
                            then show ?thesis
                            proof (cases sv)
                              case (KValue x1)
                              with * ** *** KCDptr Calldata MTArray LStackloc Storage Some show ?thesis by (simp split:if_split_asm)
                            next
                              case c2: (KCDptr x2)
                              with * ** *** KCDptr Calldata MTArray LStackloc Storage Some show ?thesis by (simp split:if_split_asm)
                            next
                              case (KMemptr x3)
                              with * ** *** KCDptr Calldata MTArray LStackloc Storage Some show ?thesis by (simp split:if_split_asm)
                            next
                              case (KStoptr p')
                              then show ?thesis
                              proof (cases "fmlookup (storage st'') (address env)")
                                case None
                                with * ** *** KCDptr Calldata MTArray LStackloc Storage Some KStoptr show ?thesis by (simp split:if_split_asm)
                              next
                                case s2: (Some s)
                                then show ?thesis
                                proof (cases "cpm2s p p' x t cd s")
                                  case None
                                  with * ** *** KCDptr Calldata MTArray LStackloc Storage Some KStoptr s2 show ?thesis by (simp split:if_split_asm)
                                next
                                  case s3: (Some s')
                                  with * ** *** KCDptr Calldata MTArray LStackloc Storage Some KStoptr s2 have "st6' = st'' \<lparr>storage := fmupd (address env) s' (storage st'')\<rparr>" by (auto split:if_split_asm)
                                  with f3 show ?thesis using asm by (simp add:frame_def)
                                qed
                              qed
                            qed
                          qed
                        qed
                      next
                        case (LMemloc l')
                        then show ?thesis
                        proof (cases "cpm2m p l' x t cd (memory st'')")
                          case None
                          with * ** *** KCDptr Calldata MTArray LMemloc show ?thesis by (auto split:if_split_asm)
                        next
                          case (Some m)
                          with * ** *** KCDptr Calldata MTArray LMemloc have "st6' = st'' \<lparr>memory := m\<rparr>" by (auto split:if_split_asm)
                          with f3 show ?thesis using asm by (simp add:frame_def)
                        qed
                      next
                        case (LStoreloc l')
                        then show ?thesis
                        proof (cases "fmlookup (storage st'') (address env)")
                          case None
                          with * ** *** KCDptr Calldata MTArray LStoreloc show ?thesis by (auto split:if_split_asm)
                        next
                          case (Some s)
                          then show ?thesis
                          proof (cases "cpm2s p l' x t cd s")
                            case None
                            with * ** *** KCDptr Calldata MTArray LStoreloc Some show ?thesis by (auto split:if_split_asm)
                          next
                            case s2: (Some s')
                            with * ** *** KCDptr Calldata MTArray LStoreloc Some s2 have "st6' = st'' \<lparr>storage := fmupd (address env) s' (storage st'')\<rparr>" by (auto split:if_split_asm)
                            with f3 show ?thesis using asm by (simp add:frame_def)
                          qed
                        qed
                      qed
                    next
                      case (MTValue x2)
                      with * ** KCDptr Calldata show ?thesis by (simp split:if_split_asm)
                    qed
                  next
                    case (Memory x3)
                    with * ** KCDptr show ?thesis by (simp split:if_split_asm)
                  next
                    case (Storage x4)
                    with * ** KCDptr show ?thesis by (simp split:if_split_asm)
                  qed
                next
                  case (KMemptr p)
                  then show ?thesis
                  proof (cases kt)
                    case (Value t)
                    with * ** KMemptr show ?thesis by (auto split:if_split_asm)
                  next
                    case (Calldata x2)
                    with * ** KMemptr show ?thesis by (simp split:if_split_asm)
                  next
                    case (Memory x3)
                    then show ?thesis
                    proof (cases x3)
                      case (MTArray x t)
                      with * ** KMemptr Memory obtain rv rt st'' where ***: "lexp lv e\<^sub>p env cd st' = Normal ((rv,rt), st'')" by (auto split:if_split_asm result.split_asm)
                      with KMemptr Memory MTArray have "\<forall>rv5 st5' (ev5'::Environment) bal.
                      frame bal st' \<and>
                      local.lexp lv e\<^sub>p env cd st' = Normal (rv5, st5') \<longrightarrow>
                      frame bal st5'" using asm 0 37(4)[OF a1 **] by auto
                      with f2 *** have f3: "frame bal st''" by blast
                      then show ?thesis
                      proof (cases rv)
                        case (LStackloc l')
                        then show ?thesis
                        proof (cases rt)
                          case (Value x1)
                          with * ** *** KMemptr Memory MTArray LStackloc show ?thesis by (auto split:if_split_asm)
                        next
                          case (Calldata x2)
                          with * ** *** KMemptr Memory MTArray LStackloc show ?thesis by (auto split:if_split_asm)
                        next
                          case m3: (Memory x3)
                          with f3 * ** *** KMemptr Memory MTArray LStackloc show ?thesis by (auto simp add:frame_def split:if_split_asm)
                        next
                          case (Storage x4)
                          then show ?thesis
                          proof (cases "accessStore l' (stack st'')")
                            case None
                            with * ** *** KMemptr Memory MTArray LStackloc Storage show ?thesis by (simp split:if_split_asm)
                          next
                            case (Some sv)
                            then show ?thesis
                            proof (cases sv)
                              case (KValue x1)
                              with * ** *** KMemptr Memory MTArray LStackloc Storage Some show ?thesis by (simp split:if_split_asm)
                            next
                              case (KCDptr x2)
                              with * ** *** KMemptr Memory MTArray LStackloc Storage Some show ?thesis by (simp split:if_split_asm)
                            next
                              case m2: (KMemptr x3)
                              with * ** *** KMemptr Memory MTArray LStackloc Storage Some show ?thesis by (simp split:if_split_asm)
                            next
                              case (KStoptr p')
                              then show ?thesis
                              proof (cases "fmlookup (storage st'') (address env)")
                                case None
                                with * ** *** KMemptr Memory MTArray LStackloc Storage Some KStoptr show ?thesis by (simp split:if_split_asm)
                              next
                                case s2: (Some s)
                                then show ?thesis
                                proof (cases "cpm2s p p' x t (memory st'') s")
                                  case None
                                  with * ** *** KMemptr Memory MTArray LStackloc Storage Some KStoptr s2 show ?thesis by (simp split:if_split_asm)
                                next
                                  case s3: (Some s')
                                  with * ** *** KMemptr Memory MTArray LStackloc Storage Some KStoptr s2 have "st6' = st'' \<lparr>storage := fmupd (address env) s' (storage st'')\<rparr>" by (auto split:if_split_asm)
                                  with f3 show ?thesis using asm by (simp add:frame_def)
                                qed
                              qed
                            qed
                          qed
                        qed
                      next
                        case (LMemloc l')
                        with * ** *** KMemptr Memory MTArray LMemloc have "st6' = st'' \<lparr>memory := updateStore l' (MPointer p) (memory st'')\<rparr>" by (auto split:if_split_asm)
                        with f3 show ?thesis using asm by (simp add:frame_def)
                      next
                        case (LStoreloc l')
                        then show ?thesis
                        proof (cases "fmlookup (storage st'') (address env)")
                          case None
                          with * ** *** KMemptr Memory MTArray LStoreloc show ?thesis by (auto split:if_split_asm)
                        next
                          case (Some s)
                          then show ?thesis
                          proof (cases "cpm2s p l' x t (memory st'') s")
                            case None
                            with * ** *** KMemptr Memory MTArray LStoreloc Some show ?thesis by (auto split:if_split_asm)
                          next
                            case s2: (Some s')
                            with * ** *** KMemptr Memory MTArray LStoreloc Some s2 have "st6' = st'' \<lparr>storage := fmupd (address env) s' (storage st'')\<rparr>" by (auto split:if_split_asm)
                            with f3 show ?thesis using asm by (simp add:frame_def)
                          qed
                        qed
                      qed
                    next
                      case (MTValue x2)
                      with * ** KMemptr Memory show ?thesis by (simp split:if_split_asm)
                    qed
                  next
                    case (Storage x4)
                    with * ** KMemptr show ?thesis by (simp split:if_split_asm)
                  qed
                next
                  case (KStoptr p)
                  then show ?thesis
                  proof (cases kt)
                    case (Value t)
                    with * ** KStoptr show ?thesis by (auto split:if_split_asm)
                  next
                    case (Calldata x2)
                    with * ** KStoptr show ?thesis by (simp split:if_split_asm)
                  next
                    case (Storage x3)
                    then show ?thesis
                    proof (cases x3)
                      case (STArray x t)
                      with * ** KStoptr Storage obtain rv rt st'' where ***: "lexp lv e\<^sub>p env cd st' = Normal ((rv,rt), st'')" by (auto split:if_split_asm result.split_asm)
                      with KStoptr Storage STArray have "\<forall>rv5 st5' bal.
                      frame bal st' \<and>
                      local.lexp lv e\<^sub>p env cd st' = Normal (rv5, st5') \<longrightarrow>
                      frame bal st5'" using asm 0 37(5)[OF a1 **] by auto
                      with f2 *** have f3: "frame bal st''" by blast
                      then show ?thesis
                      proof (cases rv)
                        case (LStackloc l')
                        then show ?thesis
                        proof (cases rt)
                          case (Value x1)
                          with * ** *** KStoptr Storage STArray LStackloc show ?thesis by (auto split:if_split_asm)
                        next
                          case (Calldata x2)
                          with * ** *** KStoptr Storage STArray LStackloc show ?thesis by (auto split:if_split_asm)
                        next
                          case (Memory x3)
                          then show ?thesis
                          proof (cases "accessStore l' (stack st'')")
                            case None
                            with * ** *** KStoptr Storage STArray LStackloc Memory show ?thesis by (simp split:if_split_asm)
                          next
                            case (Some sv)
                            then show ?thesis
                            proof (cases sv)
                              case (KValue x1)
                              with * ** *** KStoptr Storage STArray LStackloc Memory Some show ?thesis by (simp split:if_split_asm)
                            next
                              case (KCDptr x2)
                              with * ** *** KStoptr Storage STArray LStackloc Memory Some show ?thesis by (simp split:if_split_asm)
                            next
                              case (KMemptr p')
                              then show ?thesis
                              proof (cases "fmlookup (storage st'') (address env)")
                                case None
                                with * ** *** KStoptr Storage STArray LStackloc Memory Some KMemptr show ?thesis by (simp split:if_split_asm)
                              next
                                case s2: (Some s)
                                then show ?thesis
                                proof (cases "cps2m p p' x t s (memory st'')")
                                  case None
                                  with * ** *** KStoptr Storage STArray LStackloc Memory Some KMemptr s2 show ?thesis by (simp split:if_split_asm)
                                next
                                  case s3: (Some m)
                                  with * ** *** KStoptr Storage STArray LStackloc Memory Some KMemptr s2 have "st6' = st'' \<lparr>memory := m\<rparr>" by (auto split:if_split_asm)
                                  with f3 show ?thesis using asm by (simp add:frame_def)
                                qed
                              qed
                            next
                              case m2: (KStoptr x3)
                              with * ** *** KStoptr Storage STArray LStackloc Memory Some show ?thesis by (simp split:if_split_asm)
                            qed
                          qed
                        next
                          case st2: (Storage x4)
                          with f3 * ** *** KStoptr Storage STArray LStackloc show ?thesis by (auto simp add:frame_def split:if_split_asm)
                        qed
                      next
                        case (LStoreloc l')
                        then show ?thesis
                        proof (cases "fmlookup (storage st'') (address env)")
                          case None
                          with * ** *** KStoptr Storage STArray LStoreloc show ?thesis by (auto split:if_split_asm)
                        next
                          case (Some s)
                          then show ?thesis
                          proof (cases "copy p l' x t s")
                            case None
                            with * ** *** KStoptr Storage STArray LStoreloc Some show ?thesis by (auto split:if_split_asm)
                          next
                            case s2: (Some s')
                            with * ** ***  KStoptr Storage STArray LStoreloc Some s2 have "st6' = st'' \<lparr>storage := fmupd (address env) s' (storage st'')\<rparr>" by (auto split:if_split_asm)
                            with f3 show ?thesis using asm by (simp add:frame_def)
                          qed
                        qed
                      next
                        case (LMemloc l')
                        then show ?thesis
                        proof (cases "fmlookup (storage st'') (address env)")
                          case None
                          with * ** *** KStoptr Storage STArray LMemloc show ?thesis by (auto split:if_split_asm)
                        next
                          case (Some s)
                          then show ?thesis
                          proof (cases "cps2m p l' x t s (memory st'')")
                            case None
                            with * ** *** KStoptr Storage STArray LMemloc Some show ?thesis by (auto split:if_split_asm)
                          next
                            case s2: (Some m)
                            with * ** ***  KStoptr Storage STArray LMemloc Some s2 have "st6' = st'' \<lparr>memory := m\<rparr>" by (auto split:if_split_asm)
                            with f3 show ?thesis using asm by (simp add:frame_def)
                          qed
                        qed
                      qed
                    next
                      case (STMap t t')
                      with * ** KStoptr Storage obtain l' rt st'' where ***: "lexp lv e\<^sub>p env cd st' = Normal ((LStackloc l',rt), st'')" by (auto split:if_split_asm result.split_asm LType.split_asm)
                      with KStoptr Storage STMap have "\<forall>rv5 st5' (ev5'::Environment) bal.
                      frame bal st' \<and>
                      local.lexp lv e\<^sub>p env cd st' = Normal (rv5, st5') \<longrightarrow>
                      frame bal st5'" using asm 0 37(6)[OF a1 **] by auto
                      with f2 *** have f3: "frame bal st''" by blast
                      moreover from * ** *** KStoptr Storage STMap have "st6' = st'' \<lparr>stack := updateStore l' (KStoptr p) (stack st'')\<rparr>" by (auto split:if_split_asm)
                      ultimately show ?thesis using asm f3 by (simp add:frame_def)
                    next
                      case (STValue x2)
                      with * ** KStoptr Storage show ?thesis by (simp split:if_split_asm)
                    qed
                  next
                    case (Memory x4)
                    with * ** KStoptr show ?thesis by (simp split:if_split_asm)
                  qed
                qed
              qed
            qed
          qed
        next
          show "?RHS" (is "?LHS \<longrightarrow> ?RHS")
          proof
            assume "address env = STR ''Victim''"
            show ?RHS (is "?A \<and> (?B \<and> ?C)")
            proof (rule conj3)
              show ?A (is "\<forall>s val bal x. ?LHS s val bal x")
              proof (rule allI[OF allI[OF allI[OF allI]]])
                fix s val bal x
                show "?LHS s val bal x" (is "?LHS \<longrightarrow> ?RHS")
                proof
                  assume ?LHS
                  then show ?RHS by simp
                qed
              qed
            next
              show ?B (is "\<forall>s bal x. ?LHS s bal x")
              proof (rule allI[OF allI[OF allI]])
                fix s bal x
                show "?LHS s bal x" (is "?LHS \<longrightarrow> ?RHS")
                proof
                  assume ?LHS
                  then show ?RHS by simp
                qed
              qed
            next
              show ?C (is "\<forall>s bal. ?LHS s bal")
              proof (rule allI[OF allI])
                fix s bal
                show "?LHS s bal" (is "?LHS \<longrightarrow> ?RHS")
                proof
                  assume ?LHS
                  then show ?RHS by simp
                qed
              qed
            qed
          qed
        qed
      qed
    qed
  qed
next
  case (38 s1 s2 e\<^sub>p e cd st)
  show ?case (is "?LHS \<longrightarrow> ?RHS")
  proof
    assume 0: "fmlookup e\<^sub>p STR ''Victim'' = Some (victim, SKIP)"
    show ?RHS (is "\<forall>st6'. ?RHS st6'")
    proof
      fix st6'
      show "?RHS st6'" (is "?LHS \<longrightarrow> ?RHS")
      proof
        assume *: "stmt (COMP s1 s2) e\<^sub>p e cd st = Normal ((), st6')"
        show ?RHS (is "?LHS \<and> ?RHS")
        proof
          show "?LHS"
          proof
            assume asm: "address e \<noteq> STR ''Victim''"
            show "\<forall>bal. frame bal st \<longrightarrow> frame bal st6'"
            proof
              fix bal
              show "frame bal st \<longrightarrow> frame bal st6'"
              proof
                assume "frame bal st"
                with * have a1: "(applyf (costs (COMP s1 s2) e\<^sub>p e cd) \<bind> (\<lambda>g. assert Gas (\<lambda>st. gas st \<le> g) (modify (\<lambda>st. st\<lparr>gas := gas st - g\<rparr>)))) st =
                  Normal ((), st\<lparr>gas:=gas st - costs (COMP s1 s2) e\<^sub>p e cd st\<rparr>)" 
                  and f1: "frame bal (st\<lparr>gas:=gas st - costs (COMP s1 s2) e\<^sub>p e cd st\<rparr>)" by (auto simp add:frame_def)
                then have "\<forall>rv4 st4' bal.
                  frame bal (st\<lparr>gas := gas st - costs (COMP s1 s2) e\<^sub>p e cd st\<rparr>) \<and>
                  stmt s1 e\<^sub>p e cd (st\<lparr>gas := gas st - costs (COMP s1 s2) e\<^sub>p e cd st\<rparr>) = Normal (rv4, st4') \<longrightarrow>
                  frame bal st4'" using asm 0 38(1) by (simp add:frame_def)
                moreover from * obtain st' where **: "stmt s1 e\<^sub>p e cd (st\<lparr>gas:=gas st - costs (COMP s1 s2) e\<^sub>p e cd st\<rparr>) = Normal ((), st')" by (auto split:if_split_asm result.split_asm)
                ultimately have f2: "frame bal st'" using f1 by blast
                
                have "\<forall>rv4 st4' bal.
                  frame bal st' \<and>
                  stmt s2 e\<^sub>p e cd st' = Normal (rv4, st4') \<longrightarrow>
                  frame bal st4'" using asm 0 38(2)[OF a1 **]  by (simp add:frame_def)
                moreover from * ** obtain st'' where ***: "stmt s2 e\<^sub>p e cd st' = Normal ((), st'')" by (auto split:if_split_asm result.split_asm)
                ultimately have f3: "frame bal st''" using f2 by blast
          
                from a1 * ** *** have "st6' = st''" by (simp split:if_split_asm)
                with f3 asm show "frame bal st6'" by simp
              qed
            qed
          qed
        next
          show "?RHS" (is "?LHS \<longrightarrow> ?RHS")
          proof
            assume ad: "address e = STR ''Victim''"
            show ?RHS (is "?A \<and> ?B \<and> ?C")
            proof (rule conj3)
              show ?A (is "\<forall>s val bal x. ?LHS s val bal x")
              proof (rule allI[OF allI[OF allI[OF allI]]])
                fix s val bal x
                show "?LHS s val bal x" (is "?LHS \<longrightarrow> ?RHS")
                proof
                  assume ?LHS
                  then show ?RHS by simp
                qed
              qed
            next
              show ?B (is "\<forall>s bal x. ?LHS s bal x")
              proof (rule allI[OF allI[OF allI]])
                fix s bal x
                show "?LHS s bal x" (is "?LHS \<longrightarrow> ?RHS")
                proof
                  assume ?LHS(is "?A1 \<and> ?A2 \<and> ?A3 \<and> ?A4 \<and> ?A5 \<and> ?A6")
                  then have ?A1 and ?A2 and ?A3 and ?A4 and ?A5 and ?A6 by auto
                  with * have c1: "gas st > costs comp e\<^sub>p e cd st" by (auto split:if_split_asm)
                  with `?A1` * obtain st'' where 00: "stmt assign e\<^sub>p e cd (st\<lparr>gas := gas st - costs comp e\<^sub>p e cd st\<rparr>) = Normal((), st'')" by (auto split:result.split_asm)
                  moreover from `?A2` have "fmlookup (storage (st\<lparr>gas := gas st - costs comp e\<^sub>p e cd st\<rparr>)) (STR ''Victim'') = Some s" by simp
                  moreover from `?A2` have "ReadL\<^sub>i\<^sub>n\<^sub>t (accessBalance (accounts (st\<lparr>gas := gas st - costs comp e\<^sub>p e cd st\<rparr>)) (STR ''Victim'')) - (SUMM s) \<ge> bal \<and> bal \<ge> 0" by simp
                  moreover from `?A3` have "POS s" by simp
                  moreover from `?A6` have "accessStore x (stack (st\<lparr>gas := gas st - costs comp e\<^sub>p e cd st\<rparr>)) = Some (KValue (accessStorage (TUInt 256) (sender e + (STR ''.'' + STR ''balance'')) s))" by simp
                  ultimately obtain s'' where "fmlookup (storage st'') (STR ''Victim'') = Some s''"
                      and "ReadL\<^sub>i\<^sub>n\<^sub>t (accessBalance (accounts st'') (STR ''Victim'')) - (SUMM s'' + ReadL\<^sub>i\<^sub>n\<^sub>t (accessStorage (TUInt 256) (sender e + (STR ''.'' + STR ''balance'')) s)) \<ge> bal \<and> bal \<ge> 0"
                      and **: "accessStore x (stack st'') = Some (KValue (accessStorage (TUInt 256) (sender e + (STR ''.'' + STR ''balance'')) s))"
                      and "POS s''"
                    using secureassign[OF 00 _ ad `?A5`] that by blast
                  moreover from c1 `?A1` * 00 obtain st''' where ***: "stmt transfer e\<^sub>p e cd st'' = Normal((), st''')" and "st6' = st'''" by auto
    
                  moreover from `?A1` 00 have x1: "stmt s1 e\<^sub>p e cd (st\<lparr>gas := gas st - costs (COMP s1 s2) e\<^sub>p e cd st\<rparr>) = Normal((), st'')" by simp
                  moreover from * have x2: "(applyf (costs (COMP s1 s2) e\<^sub>p e cd) \<bind> (\<lambda>g. assert Gas
                                                     (\<lambda>st. gas st \<le> g)
                                                     (modify (\<lambda>st. st\<lparr>gas := gas st - g\<rparr>))))
                   st = Normal ((), st\<lparr>gas:=gas st - costs (COMP s1 s2) e\<^sub>p e cd st\<rparr>)" by (simp split: if_split_asm)
                  ultimately show "\<exists>s'. fmlookup (storage st6') (STR ''Victim'') = Some s'
                      \<and> ReadL\<^sub>i\<^sub>n\<^sub>t (accessBalance (accounts st6') (STR ''Victim'')) - (SUMM s') \<ge> bal \<and> bal \<ge> 0 \<and> POS s'"
                    using 38(2)[OF x2 x1] `?A1` `?A4` ad 0 ** `?A6` by simp
                qed
              qed
            next
              show ?C (is "\<forall>s bal. ?LHS s bal")
              proof (rule allI[OF allI])
                fix s bal
                show "?LHS s bal" (is "?LHS \<longrightarrow> ?RHS")
                proof
                  assume ?LHS
                  then show ?RHS by simp
                qed
              qed
            qed
          qed
        qed
      qed
    qed
  qed
next
  case (39 ex s1 s2 e\<^sub>p e cd st)
  show ?case (is "?LHS \<longrightarrow> ?RHS")
  proof
    assume 0: "fmlookup e\<^sub>p STR ''Victim'' = Some (victim, SKIP)"
    show ?RHS (is "\<forall>st6'. ?RHS st6'")
    proof
      fix st6'
      show "?RHS st6'" (is "?LHS \<longrightarrow> ?RHS")
      proof
        assume *: "stmt (ITE ex s1 s2) e\<^sub>p e cd st = Normal ((), st6')"
        show ?RHS (is "?LHS \<and> ?RHS")
        proof
          show "?LHS"
          proof
            assume asm: "address e \<noteq> STR ''Victim''"
            show "\<forall>bal. frame bal st \<longrightarrow> frame bal st6'"
            proof
              fix bal
              show "frame bal st \<longrightarrow> frame bal st6'"
              proof
                assume "frame bal st"
                with * have a1: "(applyf (costs (ITE ex s1 s2) e\<^sub>p e cd) \<bind> (\<lambda>g. assert Gas (\<lambda>st. gas st \<le> g) (modify (\<lambda>st. st\<lparr>gas := gas st - g\<rparr>)))) st =
                Normal ((), st\<lparr>gas:=gas st - costs (ITE ex s1 s2) e\<^sub>p e cd st\<rparr>)" 
                and f1: "frame bal (st\<lparr>gas:=gas st - costs (ITE ex s1 s2) e\<^sub>p e cd st\<rparr>)" by (auto simp add:frame_def)
        
                from * obtain b st' where **: "expr ex e\<^sub>p e cd (st\<lparr>gas:=gas st - costs (ITE ex s1 s2) e\<^sub>p e cd st\<rparr>) = Normal ((KValue b, Value TBool), st')" by (auto split:if_split_asm result.split_asm prod.split_asm Stackvalue.split_asm Type.split_asm Types.split_asm)
                moreover from asm have "\<forall>rv4 st4' bal.
                  frame bal (st\<lparr>gas := gas st - costs (ITE ex s1 s2) e\<^sub>p e cd st\<rparr>) \<and>
                  expr ex e\<^sub>p e cd (st\<lparr>gas := gas st - costs (ITE ex s1 s2) e\<^sub>p e cd st\<rparr>) = Normal (rv4, st4') \<longrightarrow>
                  frame bal st4'" using 0 39(1)[OF a1] by (simp add:frame_def)
                ultimately have f2: "frame bal st'" using f1 by blast 
      
                show "frame bal st6'"
                proof (cases "b = ShowL\<^sub>b\<^sub>o\<^sub>o\<^sub>l True")
                  case True
                  then have "\<forall>st6' bal.
                  frame bal st' \<and>
                  local.stmt s1 e\<^sub>p e cd st' = Normal ((), st6') \<longrightarrow>
                  frame bal st6'" using asm 0 39(2)[OF a1 **, of "KValue b" "Value TBool" b TBool] by (simp add:frame_def)
                  moreover from * ** True obtain st'' where ***: "stmt s1 e\<^sub>p e cd st' = Normal ((), st'')" by (auto split:if_split_asm result.split_asm)
                  ultimately have "frame bal st''" using f2 by blast
                  moreover from a1 * ** True *** have "st6' = st''" by (simp split:if_split_asm)
                  ultimately show "frame bal st6'" using asm by simp
                next
                  case False
                  then have "\<forall>st6' bal.
                  frame bal st' \<and>
                  local.stmt s2 e\<^sub>p e cd st' = Normal ((), st6') \<longrightarrow>
                  frame bal st6'" using 0 asm 39(3)[OF a1 **, of "KValue b" "Value TBool" b TBool] by (simp add:frame_def)
                  moreover from * ** False obtain st'' where ***: "stmt s2 e\<^sub>p e cd st' = Normal ((), st'')" by (auto split:if_split_asm result.split_asm)
                  ultimately have "frame bal st''" using f2 by blast
                  moreover from a1 * ** False *** have "st6' = st''" by (simp split:if_split_asm)
                  ultimately show "frame bal st6'" using asm by simp
                qed
              qed
            qed
          qed
        next
          show "?RHS" (is "?LHS \<longrightarrow> ?RHS")
          proof
            assume "address e = STR ''Victim''"
            show ?RHS (is "?A \<and> (?B \<and> ?C)")
            proof (rule conj3)
              show ?A (is "\<forall>s val bal x. ?LHS s val bal x")
              proof (rule allI[OF allI[OF allI[OF allI]]])
                fix s val bal x
                show "?LHS s val bal x" (is "?LHS \<longrightarrow> ?RHS")
                proof
                  assume ?LHS
                  then show ?RHS by simp
                qed
              qed
            next
              show ?B (is "\<forall>s bal x. ?LHS s bal x")
              proof (rule allI[OF allI[OF allI]])
                fix s bal x
                show "?LHS s bal x" (is "?LHS \<longrightarrow> ?RHS")
                proof
                  assume ?LHS
                  then show ?RHS by simp
                qed
              qed
            next
              show ?C (is "\<forall>s bal. ?LHS s bal")
              proof (rule allI[OF allI])
                fix s bal
                show "?LHS s bal" (is "?LHS \<longrightarrow> ?RHS")
                proof
                  assume ?LHS
                  then show ?RHS by simp
                qed
              qed
            qed
          qed
        qed
      qed
    qed
  qed
next
  case (40 ex s0 e\<^sub>p e cd st)
  show ?case (is "?LHS \<longrightarrow> ?RHS")
  proof
    assume 0: "fmlookup e\<^sub>p STR ''Victim'' = Some (victim, SKIP)"
    show ?RHS (is "\<forall>st6'. ?RHS st6'")
    proof
      fix st6'
      show "?RHS st6'" (is "?LHS \<longrightarrow> ?RHS")
      proof
        assume *: "stmt (WHILE ex s0) e\<^sub>p e cd st = Normal ((), st6')"
        show ?RHS (is "?LHS \<and> ?RHS")
        proof
          show "?LHS"
          proof
            assume asm: "address e \<noteq> STR ''Victim''"
            show "\<forall>bal. frame bal st \<longrightarrow> frame bal st6'"
            proof
              fix bal
              show "frame bal st \<longrightarrow> frame bal st6'"
              proof
                assume "frame bal st"
                with * have a1: "(applyf (costs (WHILE ex s0) e\<^sub>p e cd) \<bind> (\<lambda>g. assert Gas (\<lambda>st. gas st \<le> g) (modify (\<lambda>st. st\<lparr>gas := gas st - g\<rparr>)))) st =
                Normal ((), st\<lparr>gas:=gas st - costs (WHILE ex s0) e\<^sub>p e cd st\<rparr>)" 
                and f1: "frame bal (st\<lparr>gas:=gas st - costs (WHILE ex s0) e\<^sub>p e cd st\<rparr>)" by (auto simp add:frame_def)
        
                from * obtain b st' where **: "expr ex e\<^sub>p e cd (st\<lparr>gas:=gas st - costs (WHILE ex s0) e\<^sub>p e cd st\<rparr>) = Normal ((KValue b, Value TBool), st')" by (auto split:if_split_asm result.split_asm prod.split_asm Stackvalue.split_asm Type.split_asm Types.split_asm)
                moreover from asm have "\<forall>rv4 st4' bal.
                  frame bal (st\<lparr>gas := gas st - costs (WHILE ex s0) e\<^sub>p e cd st\<rparr>) \<and>
                  expr ex e\<^sub>p e cd (st\<lparr>gas := gas st - costs (WHILE ex s0) e\<^sub>p e cd st\<rparr>) = Normal (rv4, st4') \<longrightarrow>
                  frame bal st4'" using 0 40(1)[OF a1] by (simp add:frame_def)
                ultimately have f2: "frame bal st'" using f1 by blast 
          
                show "frame bal st6'"
                proof (cases "b = ShowL\<^sub>b\<^sub>o\<^sub>o\<^sub>l True")
                  case True
                  then have "\<forall>st6' bal.
                  frame bal st' \<and>
                  local.stmt s0 e\<^sub>p e cd st' = Normal ((), st6') \<longrightarrow>
                  frame bal st6'" using 0 asm 40(2)[OF a1 **, of "KValue b" "Value TBool" b TBool]  by (simp add:frame_def)
                  moreover from * ** True obtain st'' where ***: "stmt s0 e\<^sub>p e cd st' = Normal ((), st'')" by (auto split:if_split_asm result.split_asm)
                  ultimately have f3: "frame bal st''" using f2 by blast
          
                  have "\<forall>st6' bal.
                  frame bal st'' \<and>
                  local.stmt (WHILE ex s0) e\<^sub>p e cd st'' = Normal ((), st6') \<longrightarrow>
                  frame bal st6'" using 0 asm 40(3)[OF a1 ** _ _ _ _ True ***] by (simp add:frame_def)
                  moreover from * ** True *** obtain st''' where ****: "stmt (WHILE ex s0) e\<^sub>p e cd st'' = Normal ((), st''')" by (auto split:if_split_asm result.split_asm)
                  ultimately have "frame bal st'''" using f3 by blast
                  
                  moreover from a1 * ** True *** **** have "st6' = st'''" by (simp split:if_split_asm)
                  ultimately show "frame bal st6'" using asm by simp
                next
                  case False
                  then show "frame bal st6'" using * ** f1 f2 asm by (simp split:if_split_asm)
                qed
              qed
            qed
          qed
        next
          show "?RHS" (is "?LHS \<longrightarrow> ?RHS")
          proof
            assume "address e = STR ''Victim''"
            show ?RHS (is "?A \<and> (?B \<and> ?C)")
            proof (rule conj3)
              show ?A (is "\<forall>s val bal x. ?LHS s val bal x")
              proof (rule allI[OF allI[OF allI[OF allI]]])
                fix s val bal x
                show "?LHS s val bal x" (is "?LHS \<longrightarrow> ?RHS")
                proof
                  assume ?LHS
                  then show ?RHS by simp
                qed
              qed
            next
              show ?B (is "\<forall>s bal x. ?LHS s bal x")
              proof (rule allI[OF allI[OF allI]])
                fix s bal x
                show "?LHS s bal x" (is "?LHS \<longrightarrow> ?RHS")
                proof
                  assume ?LHS
                  then show ?RHS by simp
                qed
              qed
            next
              show ?C (is "\<forall>s bal. ?LHS s bal")
              proof (rule allI[OF allI])
                fix s bal
                show "?LHS s bal" (is "?LHS \<longrightarrow> ?RHS")
                proof
                  assume ?LHS
                  then show ?RHS by simp
                qed
              qed
            qed
          qed
        qed
      qed
    qed
  qed
next
  case (41 i xe e\<^sub>p e cd st)
  show ?case (is "?LHS \<longrightarrow> ?RHS")
  proof
    assume 0: "fmlookup e\<^sub>p STR ''Victim'' = Some (victim, SKIP)"
    show ?RHS (is "\<forall>st6'. ?RHS st6'")
    proof
      fix st'
      show "?RHS st'" (is "?LHS \<longrightarrow> ?RHS")
      proof
        assume *: "stmt (INVOKE i xe) e\<^sub>p e cd st = Normal ((), st')"
        show ?RHS (is "?LHS \<and> ?RHS")
        proof
          show "?LHS"
          proof
            assume asm: "address e \<noteq> STR ''Victim''"
            show "\<forall>bal. frame bal st \<longrightarrow> frame bal st'"
            proof
              fix bal
              show "frame bal st \<longrightarrow> frame bal st'"
              proof
                assume ff: "frame bal st"
                moreover from * have a1: "(applyf (costs (INVOKE i xe) e\<^sub>p e cd) \<bind> (\<lambda>g. assert Gas (\<lambda>st. gas st \<le> g) (modify (\<lambda>st. st\<lparr>gas := gas st - g\<rparr>))))  st = Normal ((), st\<lparr>gas := gas st - costs (INVOKE i xe) e\<^sub>p e cd st\<rparr>)" by auto
                moreover from * obtain ct bla where **: "fmlookup e\<^sub>p (address e) = Some (ct, bla)"
                  by (auto split:if_split_asm option.split_asm)
                moreover from * ** obtain fp f where ***: "fmlookup ct i = Some (Method (fp, f, None))"
                  by (auto split:if_split_asm option.split_asm Member.split_asm)
                moreover define e' where "e' = ffold_init ct (emptyEnv (address e) (sender e) (svalue e)) (fmdom ct)"
                moreover from * ** *** obtain e'' cd' st'' st''' where ****: "load False fp xe e\<^sub>p e' emptyStore (st\<lparr>gas:=gas st - (costs (INVOKE i xe) e\<^sub>p e cd st), stack:=emptyStore\<rparr>) e cd (st\<lparr>gas:=gas st - (costs (INVOKE i xe) e\<^sub>p e cd st)\<rparr>) = Normal ((e'', cd', st''), st''')"
                  using e'_def by (auto split:if_split_asm result.split_asm)
                moreover from * **** have f1: "frame bal st''" and ad: "address e' = address e''"
                  using asm ff 0 41(1)[OF a1 ** _ *** _ _ _ _ e'_def, of bla "(fp, f, None)" fp "(f, None)" f None] by (auto simp add:frame_def)
                moreover from e'_def have ad2: "address e = address e'" using ffold_init_ad_same[of ct "(emptyEnv (address e) (sender e) (svalue e))" "(fmdom ct)" e'] by simp
                moreover from * ** *** **** e'_def obtain st'''' where *****: "stmt f e\<^sub>p e'' cd' st'' = Normal ((), st'''')" by (auto split:if_split_asm result.split_asm)
                ultimately have "st' = st''''\<lparr>stack:=stack st''', memory := memory st'''\<rparr>" using * apply safe by simp
                moreover from f1 ad ad2 asm ***** have f2:"frame bal st''''"
                  using 41(2)[OF a1 ** _ *** _ _ _ _ e'_def _ ****] using 0 * by (auto simp add:frame_def)
                ultimately show "frame bal st'" by (simp add:frame_def)
              qed
            qed
          qed
        next
          show "?RHS" (is "?LHS \<longrightarrow> ?RHS")
          proof
            assume "address e = STR ''Victim''"
            show ?RHS (is "?A \<and> (?B \<and> ?C)")
            proof (rule conj3)
              show ?A (is "\<forall>s val bal x. ?LHS s val bal x")
              proof (rule allI[OF allI[OF allI[OF allI]]])
                fix s val bal x
                show "?LHS s val bal x" (is "?LHS \<longrightarrow> ?RHS")
                proof
                  assume ?LHS
                  then show ?RHS by simp
                qed
              qed
            next
              show ?B (is "\<forall>s bal x. ?LHS s bal x")
              proof (rule allI[OF allI[OF allI]])
                fix s bal x
                show "?LHS s bal x" (is "?LHS \<longrightarrow> ?RHS")
                proof
                  assume ?LHS
                  then show ?RHS by simp
                qed
              qed
            next
              show ?C (is "\<forall>s bal. ?LHS s bal")
              proof (rule allI[OF allI])
                fix s bal
                show "?LHS s bal" (is "?LHS \<longrightarrow> ?RHS")
                proof
                  assume ?LHS
                  then show ?RHS by simp
                qed
              qed
            qed
          qed
        qed
      qed
    qed
  qed
next
  case (42 ad i xe val e\<^sub>p e cd st)
  show ?case (is "?LHS \<longrightarrow> ?RHS")
  proof
    assume 0: "fmlookup e\<^sub>p STR ''Victim'' = Some (victim, SKIP)"
    show ?RHS (is "\<forall>st6'. ?RHS st6'")
    proof
      fix st'
      show "?RHS st'" (is "?LHS \<longrightarrow> ?RHS")
      proof
        assume *: "stmt (EXTERNAL ad i xe val) e\<^sub>p e cd st = Normal ((), st')"
        show ?RHS (is "?LHS \<and> ?RHS")
        proof
          show "?LHS"
          proof
            assume asm: "address e \<noteq> STR ''Victim''"
            show "\<forall>bal. frame bal st \<longrightarrow> frame bal st'"
            proof
              fix bal
              show "frame bal st \<longrightarrow> frame bal st'"
              proof
                assume ff: "frame bal st"
                moreover from * have a1: "(applyf (costs (EXTERNAL ad i xe val) e\<^sub>p e cd) \<bind> (\<lambda>g. assert Gas (\<lambda>st. gas st \<le> g) (modify (\<lambda>st. st\<lparr>gas := gas st - g\<rparr>))))  st = Normal ((), st\<lparr>gas := gas st - costs (EXTERNAL ad i xe val) e\<^sub>p e cd st\<rparr>)" by auto
                moreover from * obtain adv st'' where **: "expr ad e\<^sub>p e cd (st\<lparr>gas:=gas st - (costs (EXTERNAL ad i xe val) e\<^sub>p e cd st)\<rparr>) = Normal ((KValue adv, Value TAddr), st'')"
                  by (auto split:if_split_asm result.split_asm Stackvalue.split_asm Type.split_asm Types.split_asm)
                moreover from * ** ff have f1: "frame bal st''" using asm 0 42(1) by (simp add:frame_def split:if_split_asm)
                moreover from * ** obtain ct fb where ***: "fmlookup e\<^sub>p adv = Some (ct, fb)"
                  by (auto split:if_split_asm option.split_asm)
                moreover from * ** *** f1 obtain v t st''' where ****: "expr val e\<^sub>p e cd st'' = Normal ((KValue v, Value t), st''')"
                  by (auto split:if_split_asm result.split_asm Stackvalue.split_asm Type.split_asm)
                moreover from **** f1 have "frame bal st'''" using asm 42(2)[OF a1 ** _ _ _ _ ***] 0 by (simp split:if_split_asm)
                then have f2: "frame bal (st'''\<lparr>stack := emptyStore, memory := emptyStore\<rparr>)" by (simp add:frame_def)
                show "frame bal st'"
                proof (cases "fmlookup ct i")
                  case None
                  with * ** *** **** obtain acc where trans: "Accounts.transfer (address e) adv v (accounts st''') = Some acc" by (auto split:if_split_asm option.split_asm)
                  with * ** *** **** None obtain st'''' where *****: "stmt fb e\<^sub>p (emptyEnv adv (address e) v) cd (st'''\<lparr>accounts := acc,stack:=emptyStore, memory:=emptyStore\<rparr>) = Normal ((), st'''')"
                    by (auto split:if_split_asm result.split_asm)
                  moreover have f4: "frame bal (st''''\<lparr>stack:=stack st'', memory := memory st''\<rparr>)"
                  proof (cases "adv = STR ''Victim''")
                    case True
                    with 0 *** have "fb = SKIP" by simp
                    moreover from f2 have "frame bal (st'''\<lparr>accounts := acc,stack:=emptyStore, memory:=emptyStore\<rparr>)" using transfer_frame[OF trans] asm by (simp add:frame_def)
                    ultimately show ?thesis using ***** by (auto split:if_split_asm simp add:frame_def)
                  next
                    case False
                    moreover from f2 have "frame bal (st'''\<lparr>accounts := acc,stack:=emptyStore, memory:=emptyStore\<rparr>)" using transfer_frame[OF trans] asm by (simp add:frame_def)
                    then have "frame bal st''''" using f2 0 42(5)[OF a1 ** _ _ _ _ *** _ **** _ _ _ None _ trans, of "KValue adv" "Value TAddr" TAddr fb "KValue v" "Value t" t st''' st''' st'''] asm ***** False by (auto simp add:frame_def)
                    then show ?thesis by (simp add:frame_def)
                  qed
                  ultimately show "frame bal st'" using a1 * ** *** **** None trans by (auto simp add:frame_def)
                next
                  case (Some a)
                  with * ** *** **** obtain fp f where *****: "fmlookup ct i = Some (Method (fp, f, None))"
                    by (auto split:if_split_asm option.split_asm Member.split_asm)
                  moreover define e' where e'_def: "e' = ffold_init ct (emptyEnv adv (address e) v) (fmdom ct)"
                  moreover from * ** *** ***** **** obtain e'' cd' st'''' st''''' where *******: "load True fp xe e\<^sub>p e' emptyStore (st'''\<lparr>stack:=emptyStore, memory:=emptyStore\<rparr>) e cd st''' = Normal ((e'', cd', st''''), st''''')"
                    using e'_def by (auto split:if_split_asm result.split_asm option.split_asm)
                  moreover from e'_def have ad2: "address e' = adv" and send2: "sender e' = address e" and sval2: "svalue e' = v" using ffold_init_ad_same[of ct "(emptyEnv adv (address e) v)" "(fmdom ct)" e'] by auto
                  moreover from * ** *** ***** **** ******* e'_def obtain acc where trans: "Accounts.transfer (address e) adv v (accounts st'''') = Some acc" by (auto split:if_split_asm option.split_asm)
                  then have ******: "Accounts.transfer (address e) adv v (accounts st'''') = Some acc" by (auto split:if_split_asm option.split_asm)
                  moreover from * ** *** ***** **** ****** ******* obtain st'''''' where ********: "stmt f e\<^sub>p e'' cd' (st''''\<lparr>accounts := acc\<rparr>) = Normal ((), st'''''')"
                    using e'_def by (auto split:if_split_asm result.split_asm)
                  moreover have f4: "frame bal st''''''"
                  proof (cases "adv = STR ''Victim''")
                    case True
                    with 0 *** have ct_def: "ct = victim" by simp
  
                    moreover have
                      "(\<forall>(ev::Environment) cda st st' bal.
                              local.load True fp xe e\<^sub>p e' emptyStore (st'''\<lparr>stack := emptyStore, memory := emptyStore\<rparr>) e cd st''' = Normal ((ev, cda, st), st') \<longrightarrow>
                              (frame bal (st'''\<lparr>stack := emptyStore, memory := emptyStore\<rparr>) \<longrightarrow> frame bal st) \<and>
                              (frame bal st''' \<longrightarrow> frame bal st') \<and> address e' = address ev \<and> sender e' = sender ev \<and> svalue e' = svalue ev)"
                      using 0 42(3)[OF a1 ** _ _ _ _ *** _ **** _ _ _ ***** _ _ _ _ e'_def] asm by simp
                    with f2 ******* have f3: "frame bal st''''" and ad1: "address e' = address e''" and send1: "sender e' = sender e''" and sval1: "svalue e' = svalue e''" by auto
  
                    from ct_def ***** consider (withdraw) "i = STR ''withdraw''" | (deposit) "i = STR ''deposit''" using victim_def fmap_of_list_SomeD[of "[(STR ''balance'', Var (STMap TAddr (STValue (TUInt 256)))), (STR ''deposit'', Method ([], deposit, None)), (STR ''withdraw'', Method ([], keep, None))]"] by auto
                    then show ?thesis
                    proof cases
                      case withdraw
                      moreover have "fmlookup victim (STR ''withdraw'') = Some (Method ([], keep, None))" using victim_def by eval 
                      ultimately have "f=keep" and "fp = []" using *** ***** True 0 by auto
                      with ******** have *********: "stmt keep e\<^sub>p e'' cd' (st''''\<lparr>accounts := acc\<rparr>) = Normal ((), st'''''')" by simp
                      have "fmlookup (denvalue e'') STR ''balance'' = Some (Storage (STMap TAddr (STValue (TUInt 256))), Storeloc STR ''balance'')"
                      proof -
                        from victim_def have some: "fmlookup victim (STR ''balance'') = Some (Var (STMap TAddr (STValue (TUInt 256))))" by eval
                        with ct_def have "fmlookup ct (STR ''balance'') = Some (Var (STMap TAddr (STValue (TUInt 256))))" by simp
                        moreover have "STR ''balance'' |\<notin>| fmdom (denvalue (emptyEnv adv (address e) v))" by simp
                        moreover from ct_def some have "STR ''balance'' |\<in>| fmdom ct" using fmdomI by simp
                        ultimately have "fmlookup (denvalue e') STR ''balance'' = Some (Storage (STMap TAddr (STValue (TUInt 256))), Storeloc STR ''balance'')" using e'_def ffold_init_fmap[of ct "STR ''balance''" "(STMap TAddr (STValue (TUInt 256)))" "(emptyEnv adv (address e) v)" "(fmdom ct)"] by simp
                        moreover have "e'' = e'"
                        proof (cases "xe=[]")
                          case True
                          with ******* `fp = []` show ?thesis by simp
                        next
                          case False
                          then obtain xx xe' where "xe = xx # xe'" using list.exhaust by auto
                          with ******* `fp = []` show ?thesis by simp
                        qed
                        ultimately show ?thesis by simp
                      qed
  
                      moreover from ad1 ad2 True have ad: "address e'' = STR ''Victim''" by simp
                      moreover from ad send1 send2 asm have "sender e'' \<noteq> address e''" by simp
                      moreover from f3 have f4: "frame bal (st''''\<lparr>accounts := acc\<rparr>)" using transfer_frame[OF ******] asm by simp
                      then obtain s'''' where "fmlookup (storage (st''''\<lparr>accounts := acc\<rparr>)) (STR ''Victim'') = Some s'''' \<and> ReadL\<^sub>i\<^sub>n\<^sub>t (accessBalance (accounts (st''''\<lparr>accounts := acc\<rparr>)) (STR ''Victim'')) - (SUMM s'''') \<ge> bal \<and> bal \<ge> 0 \<and> POS s''''" by (auto simp add:frame_def)
                      ultimately have "(\<exists>s'. fmlookup (storage st'''''') (STR ''Victim'') = Some s'
                      \<and> ReadL\<^sub>i\<^sub>n\<^sub>t (accessBalance (accounts st'''''') (STR ''Victim'')) - (SUMM s') \<ge> bal \<and> bal \<ge> 0 \<and> POS s')"
                        using 0 ******** `f=keep` 42(4)[OF a1 ** _ _ _ _ *** _ **** _ _ _ *****  _ _ _ _ e'_def _ ******* _ _ _ trans, of "KValue adv" "Value TAddr" TAddr fb "KValue v" "Value t" t "(fp, f, None)" "(f, None)" f None e'' "(cd', st'''')" cd' st''''' st''''' "()" "st''''\<lparr>accounts := acc\<rparr>"] apply safe by auto
                      then show ?thesis by (simp add:frame_def)
                    next
                      case deposit
                      moreover from f2 have "frame bal (st'''\<lparr>stack:=emptyStore, memory:=emptyStore\<rparr>)" using transfer_frame[OF ******] asm by simp
                      moreover have "fmlookup victim (STR ''deposit'') = Some (Method ([], deposit, None))" using victim_def by eval
                      ultimately have "f=deposit" and "fp = []" using *** ***** True 0 by auto
                      with ******** have *: "stmt deposit e\<^sub>p e'' cd' (st''''\<lparr>accounts := acc\<rparr>) = Normal ((), st'''''')" by simp
  
                      have f4: "frame (bal + ReadL\<^sub>i\<^sub>n\<^sub>t v) (st''''\<lparr>accounts := acc\<rparr>)" and ad1: "address e' = address e''" and send1: "sender e' = sender e''" and sval1: "svalue e' = svalue e''"
                      proof -
                        have "ReadL\<^sub>i\<^sub>n\<^sub>t (accessBalance acc (STR ''Victim'')) = ReadL\<^sub>i\<^sub>n\<^sub>t (accessBalance (accounts st'''') (STR ''Victim'')) + ReadL\<^sub>i\<^sub>n\<^sub>t v" using transfer_add[OF ******] asm True by simp
                        moreover have "ReadL\<^sub>i\<^sub>n\<^sub>t v \<ge> 0" using transfer_val1[OF  ******] by simp
                        ultimately have "frame (bal + ReadL\<^sub>i\<^sub>n\<^sub>t v) (st''''\<lparr>accounts := acc\<rparr>)" using f3 by (auto simp add:frame_def)
                        then show "frame (bal + ReadL\<^sub>i\<^sub>n\<^sub>t v) (st''''\<lparr>accounts := acc\<rparr>)" and "address e' = address e''" and "sender e' = sender e''" and "svalue e' = svalue e''" using f2 0 42(3)[OF a1 ** _ _ _ _ *** _ **** _ _ _ ***** _ _ _ _ e'_def, of "KValue adv" "Value TAddr" TAddr fb "KValue v" "Value t"] asm ******* by (auto simp add:frame_def)
                      qed
                      moreover from sval1 sval2 have "v = svalue e''" by simp
                      ultimately have "frame (bal + ReadL\<^sub>i\<^sub>n\<^sub>t (svalue e'')) (st''''\<lparr>accounts := acc\<rparr>)" by simp
                      then obtain s''''' where II: "INV (st''''\<lparr>accounts := acc\<rparr>) s''''' (SUMM s''''') (bal + ReadL\<^sub>i\<^sub>n\<^sub>t (svalue e''))" and III:"POS s'''''" by (auto simp add:frame_def)
                      then have s'''''_def: "fmlookup (storage (st''''\<lparr>accounts := acc\<rparr>)) STR ''Victim'' = Some s'''''" by simp
  
                      have yyy: "fmlookup (denvalue e'') STR ''balance'' = Some (Storage (STMap TAddr (STValue (TUInt 256))), Storeloc STR ''balance'')"
                      proof -
                        from victim_def have some: "fmlookup victim (STR ''balance'') = Some (Var (STMap TAddr (STValue (TUInt 256))))" by eval
                        with ct_def have "fmlookup ct (STR ''balance'') = Some (Var (STMap TAddr (STValue (TUInt 256))))" by simp
                        moreover have "STR ''balance'' |\<notin>| fmdom (denvalue (emptyEnv adv (address e) v))" by simp
                        moreover from ct_def some have "STR ''balance'' |\<in>| fmdom ct" using fmdomI by simp
                        ultimately have "fmlookup (denvalue e') STR ''balance'' = Some (Storage (STMap TAddr (STValue (TUInt 256))), Storeloc STR ''balance'')" using e'_def ffold_init_fmap[of ct "STR ''balance''" "(STMap TAddr (STValue (TUInt 256)))" "(emptyEnv adv (address e) v)" "(fmdom ct)"] by simp
                        moreover have "e'' = e'"
                        proof (cases "xe=[]")
                          case True
                          with ******* `fp = []` show ?thesis by simp
                        next
                          case False
                          then obtain xx xe' where "xe = xx # xe'" using list.exhaust by auto
                          with ******* `fp = []` show ?thesis by simp
                        qed
                        ultimately show ?thesis by simp
                      qed
  
                      from asm True have "address e \<noteq> (STR ''Victim'')" by simp
                      then have  "ReadL\<^sub>i\<^sub>n\<^sub>t (accessBalance (accounts st'''')  (STR ''Victim'')) + ReadL\<^sub>i\<^sub>n\<^sub>t v < 2^256" using transfer_val2[OF  ******] True by simp
                      moreover from `address e \<noteq> (STR ''Victim'')` have "ReadL\<^sub>i\<^sub>n\<^sub>t (accessBalance acc  (STR ''Victim'')) = ReadL\<^sub>i\<^sub>n\<^sub>t (accessBalance (accounts st'''')  (STR ''Victim'')) + ReadL\<^sub>i\<^sub>n\<^sub>t v" using transfer_add[OF ******] (******) True by simp
                      ultimately have abc: "ReadL\<^sub>i\<^sub>n\<^sub>t (accessBalance (accounts (st''''\<lparr>accounts := acc\<rparr>))  (STR ''Victim'')) < 2^256" by simp
  
                      from II have "fmlookup (storage (st''''\<lparr>accounts := acc\<rparr>)) (STR ''Victim'') = Some s'''''  \<and> ReadL\<^sub>i\<^sub>n\<^sub>t (accessBalance (accounts (st''''\<lparr>accounts := acc\<rparr>)) (STR ''Victim'')) - (SUMM s''''') \<ge> bal + ReadL\<^sub>i\<^sub>n\<^sub>t  (svalue e'') \<and> bal + ReadL\<^sub>i\<^sub>n\<^sub>t  (svalue e'') \<ge> 0" by (auto)
                      moreover have "ReadL\<^sub>i\<^sub>n\<^sub>t (accessStorage (TUInt 256) (sender e'' + (STR ''.'' + STR ''balance'')) s''''')  + \<lceil>svalue e''\<rceil> < 2 ^ 256 \<and>
                          ReadL\<^sub>i\<^sub>n\<^sub>t (accessStorage (TUInt 256) (sender e'' + (STR ''.'' + STR ''balance'')) s''''')  + \<lceil>svalue e''\<rceil> \<ge> 0"
                      proof (cases "fmlookup s''''' (sender e'' + (STR ''.'' + STR ''balance'')) = None")
                        case True
                        hence "(accessStorage (TUInt 256) (sender e'' + (STR ''.'' + STR ''balance'')) s''''') = ShowL\<^sub>i\<^sub>n\<^sub>t 0" by simp
                        moreover have "(\<lceil>svalue e''\<rceil>::int) < 2 ^ 256"
                        proof -
                          from II have "bal + \<lceil>svalue e''\<rceil> + SUMM s''''' \<le> ReadL\<^sub>i\<^sub>n\<^sub>t (accessBalance (accounts (st''''\<lparr>accounts := acc\<rparr>)) (STR ''Victim''))" by simp
                          moreover have "0 \<le> SUMM s'''''"
                          using III sum_nonneg[of "{(ad,x). fmlookup s''''' (ad + (STR ''.'' + STR ''balance'')) = Some x}" "\<lambda>(ad,x). ReadL\<^sub>i\<^sub>n\<^sub>t x"] by auto
                          ultimately have "bal + \<lceil>svalue e''\<rceil> \<le> ReadL\<^sub>i\<^sub>n\<^sub>t (accessBalance (accounts (st''''\<lparr>accounts := acc\<rparr>)) (STR ''Victim''))" by simp
                          moreover from ff have "bal\<ge>0" by (auto simp add:frame_def)
                          ultimately show "(\<lceil>svalue e''\<rceil>::int) < 2 ^ 256" using abc by simp
                        qed
                        moreover have "ReadL\<^sub>i\<^sub>n\<^sub>t v \<ge> 0" using transfer_val1[OF  ******] by simp
                        with `svalue e' = v` sval1 have "(\<lceil>svalue e''\<rceil>::int) \<ge> 0" by simp
                        ultimately show ?thesis using Read_ShowL_id by simp
                      next
                        case False
                        then obtain x where x_def: "fmlookup s'''''  (sender e'' + (STR ''.'' + STR ''balance'')) = Some x" by auto
                        moreover from II have "bal + \<lceil>svalue e''\<rceil> + SUMM s''''' \<le> ReadL\<^sub>i\<^sub>n\<^sub>t (accessBalance (accounts (st''''\<lparr>accounts := acc\<rparr>)) (STR ''Victim''))" by simp
                        moreover have "(case (sender e'', x) of (ad, x) \<Rightarrow> \<lceil>x\<rceil>) \<le> (\<Sum>(ad, x)\<in>{(ad, x). fmlookup s''''' (ad + (STR ''.'' + STR ''balance'')) = Some x}. ReadL\<^sub>i\<^sub>n\<^sub>t x)"
                        proof (cases rule: member_le_sum[of "(sender e'',x)" "{(ad,x). fmlookup s''''' (ad + (STR ''.'' + STR ''balance'')) = Some x}" "\<lambda>(ad,x). ReadL\<^sub>i\<^sub>n\<^sub>t x"])
                          case 1
                          then show ?case using x_def by simp
                        next
                          case (2 x)
                          with III show ?case by auto
                        next
                          case 3
                          have "inj_on (\<lambda>(ad, x). (ad + (STR ''.'' + STR ''balance''), x)) {(ad, x). (fmlookup s''''' \<circ> (\<lambda>ad. ad + (STR ''.'' + STR ''balance''))) ad = Some x}" using balance_inj by simp
                          then have "finite {(ad, x). (fmlookup s''''' \<circ> (\<lambda>ad. ad + (STR ''.'' + STR ''balance''))) ad = Some x}" using fmlookup_finite[of "\<lambda>ad. (ad + (STR ''.'' + STR ''balance''))" s'''''] by simp
                          then show ?case using finite_subset[of "{(ad, x). fmlookup s''''' (ad + (STR ''.'' + STR ''balance'')) = Some x}" "{(ad, x). fmlookup s''''' (ad + (STR ''.'' + STR ''balance'')) = Some x}"] by auto
                        qed
                        then have "ReadL\<^sub>i\<^sub>n\<^sub>t x \<le> SUMM s'''''" by simp
                        ultimately have "bal + \<lceil>svalue e''\<rceil> + ReadL\<^sub>i\<^sub>n\<^sub>t x \<le> ReadL\<^sub>i\<^sub>n\<^sub>t (accessBalance (accounts (st''''\<lparr>accounts := acc\<rparr>)) (STR ''Victim''))" by simp
                        moreover from ff have "bal\<ge>0" by (auto simp add:frame_def)
                        ultimately have "\<lceil>svalue e''\<rceil> + ReadL\<^sub>i\<^sub>n\<^sub>t x \<le> ReadL\<^sub>i\<^sub>n\<^sub>t (accessBalance (accounts (st''''\<lparr>accounts := acc\<rparr>)) (STR ''Victim''))" by simp
                        with abc have "\<lceil>svalue e''\<rceil> + ReadL\<^sub>i\<^sub>n\<^sub>t x < 2^256" by simp
                        moreover have "fmlookup s''''' (sender e' + (STR ''.'' + STR ''balance'')) = fmlookup s'''''  (sender e'' + (STR ''.'' + STR ''balance''))" using send1 by simp
                        ultimately have "bal + \<lceil>svalue e''\<rceil> \<le> \<lceil>accessBalance (accounts (st''''\<lparr>accounts := acc\<rparr>)) STR ''Victim''\<rceil> - SUMM s'''''" and lck: "fmlookup s''''' (sender e'' + (STR ''.'' + STR ''balance'')) = Some x"  and "ReadL\<^sub>i\<^sub>n\<^sub>t x + \<lceil>svalue e''\<rceil> < 2 ^ 256" using ad1 ad2 True II x_def by simp+
                        moreover from lck have "(accessStorage (TUInt 256) (sender e'' + (STR ''.'' + STR ''balance'')) s''''') = x" by simp
                        moreover have "\<lceil>svalue e''\<rceil> + ReadL\<^sub>i\<^sub>n\<^sub>t x \<ge> 0"
                        proof -
                          have "ReadL\<^sub>i\<^sub>n\<^sub>t v \<ge> 0" using transfer_val1[OF  ******] by simp
                          with `svalue e' = v` sval1 have "(\<lceil>svalue e''\<rceil>::int) \<ge> 0" by simp
                          moreover from III have "ReadL\<^sub>i\<^sub>n\<^sub>t x \<ge> 0" using x_def by simp
                          ultimately show ?thesis by simp
                        qed
                        ultimately show ?thesis using Read_ShowL_id by simp
                      qed
                      moreover have "address e'' = STR ''Victim''" using ad1 ad2 True by simp
                      ultimately obtain s'''''' where "fmlookup (storage st'''''') (STR ''Victim'') = Some s''''''" and "ReadL\<^sub>i\<^sub>n\<^sub>t (accessBalance (accounts st'''''') (STR ''Victim'')) - SUMM s'''''' \<ge> bal" and "POS s''''''"
                      using deposit_frame[OF * s'''''_def _ yyy] III by auto
                      then show ?thesis using ff by (auto simp add:frame_def)
                    qed
                  next
                    case False
                    moreover from f2 have "frame bal (st'''\<lparr>stack:=emptyStore, memory:=emptyStore\<rparr>)" using transfer_frame[OF ******] asm by simp
                    then have "frame bal st''''" and ad1: "address e' = address e''" using f2 0 42(3)[OF a1 ** _ _ _ _ *** _ **** _ _ _ ***** _ _ _ _ e'_def, of "KValue adv" "Value TAddr" TAddr fb "KValue v" "Value t"] asm ******* by (auto simp add:frame_def)
                    then have f4: "frame bal (st''''\<lparr>accounts := acc\<rparr>)" using transfer_frame[OF ******] asm by simp
                    
                    moreover from ad1 ad2 have "address e'' \<noteq> STR ''Victim'' \<and> fmlookup e\<^sub>p (STR ''Victim'') = Some (victim, SKIP)" using 0 False by simp
                    then have "\<forall>st6' bal.
                    frame bal (st''''\<lparr>accounts := acc\<rparr>) \<and>
                    local.stmt f e\<^sub>p e'' cd' (st''''\<lparr>accounts := acc\<rparr>) = Normal ((), st6') \<longrightarrow>
                    frame bal st6'" using 42(4)[OF a1 ** _ _ _ _ *** _ **** _ _ _ ***** _ _ _ _ e'_def _ ******* _ _ _ ******] False asm by (auto simp add:frame_def)
                    ultimately show ?thesis using ******** by blast
                  qed
                  ultimately show "frame bal st'" using a1 * ** *** **** by (auto simp add:frame_def)
                qed
              qed
            qed
          qed
        next
          show "?RHS" (is "?LHS \<longrightarrow> ?RHS")
          proof
            assume "address e = STR ''Victim''"
            show ?RHS (is "?A \<and> (?B \<and> ?C)")
            proof (rule conj3)
              show ?A (is "\<forall>s val bal x. ?LHS s val bal x")
              proof (rule allI[OF allI[OF allI[OF allI]]])
                fix s val bal x
                show "?LHS s val bal x" (is "?LHS \<longrightarrow> ?RHS")
                proof
                  assume ?LHS
                  then show ?RHS by simp
                qed
              qed
            next
              show ?B (is "\<forall>s bal x. ?LHS s bal x")
              proof (rule allI[OF allI[OF allI]])
                fix s bal x
                show "?LHS s bal x" (is "?LHS \<longrightarrow> ?RHS")
                proof
                  assume ?LHS
                  then show ?RHS by simp
                qed
              qed
            next
              show ?C (is "\<forall>s bal. ?LHS s bal")
              proof (rule allI[OF allI])
                fix s bal
                show "?LHS s bal" (is "?LHS \<longrightarrow> ?RHS")
                proof
                  assume ?LHS
                  then show ?RHS by simp
                qed
              qed
            qed
          qed
        qed
      qed
    qed
  qed
next
  case (43 ad ex e\<^sub>p e cd st)
  show ?case (is "?LHS \<longrightarrow> ?RHS")
  proof
    assume 0: "fmlookup e\<^sub>p STR ''Victim'' = Some (victim, SKIP)"
    show ?RHS (is "\<forall>st6'. ?RHS st6'")
    proof
      fix st'
      show "?RHS st'" (is "?LHS \<longrightarrow> ?RHS")
      proof
        assume *: "stmt (TRANSFER ad ex) e\<^sub>p e cd st = Normal ((), st')"
        show ?RHS (is "?LHS \<and> ?RHS")
        proof
          show "?LHS"
          proof
            assume asm: "address e \<noteq> STR ''Victim''"
            show "\<forall>bal. frame bal st \<longrightarrow> frame bal st'"
            proof
              fix bal
              show "frame bal st \<longrightarrow> frame bal st'"
              proof
                assume ff: "frame bal st"
                from * have a1: "(applyf (costs (TRANSFER ad ex) e\<^sub>p e cd) \<bind> (\<lambda>g. assert Gas (\<lambda>st. gas st \<le> g) (modify (\<lambda>st. st\<lparr>gas := gas st - g\<rparr>))))  st = Normal ((), st\<lparr>gas := gas st - costs (TRANSFER ad ex) e\<^sub>p e cd st\<rparr>)" by auto
                from * obtain v t st'' where **: "expr ex e\<^sub>p e cd (st\<lparr>gas:=gas st - (costs (TRANSFER ad ex) e\<^sub>p e cd st)\<rparr>) = Normal ((KValue v, Value t), st'')"
                  by (auto split:if_split_asm result.split_asm Stackvalue.split_asm Type.split_asm)
                from asm ff * ** have f1: "frame bal st''" using 43(1)[OF a1] 0 by (simp add:frame_def)
                from * ** obtain adv st''' where ***: "expr ad e\<^sub>p e cd st'' = Normal ((KValue adv, Value TAddr), st''')"
                  by (auto split:if_split_asm result.split_asm Stackvalue.split_asm Type.split_asm Types.split_asm)
                from asm * *** f1 have f2: "frame bal st'''" using asm 43(2)[OF a1 **] 0 by (simp add:frame_def)
                from * ** *** obtain acc where *****: "Accounts.transfer (address e) adv v (accounts st''') = Some acc" by (auto split:if_split_asm option.split_asm)
                from f2 have f3: "frame bal (st'''\<lparr>accounts := acc\<rparr>)" using transfer_frame[OF *****] asm by simp
                show "frame bal st'"
                proof (cases "fmlookup e\<^sub>p adv")
                  case None
                  with a1 * ** *** ***** show ?thesis using f3 by auto
                next
                  case (Some a)
                  then show ?thesis
                  proof (cases a)
                    case (Pair ct f)
                    moreover define e' where "e' = ffold_init ct (emptyEnv adv (address e) v) (fmdom ct)"
                    moreover from * ** *** Some Pair ***** e'_def obtain st'''' where ******: "stmt f e\<^sub>p e' emptyStore (st'''\<lparr>accounts := acc, stack:=emptyStore, memory:=emptyStore\<rparr>) = Normal ((), st'''')" by (auto split:if_split_asm option.split_asm result.split_asm)
                    moreover from e'_def have ad: "adv = address e'" using ffold_init_ad_same[of ct "(emptyEnv adv (address e) v)" "(fmdom ct)" e'] by simp
              
                    moreover have f4: "frame bal st''''" 
                    proof (cases "adv = STR ''Victim''")
                      case True
                      with 0 ** *** Some Pair have "f = SKIP" using victim_def by simp
                      with ****** have "st''''=  st'''
                      \<lparr>accounts := acc, stack := emptyStore, memory := emptyStore,
                      gas := gas st''' - costs SKIP e\<^sub>p e' emptyStore (st'''\<lparr>accounts := acc, stack := emptyStore, memory := emptyStore\<rparr>)\<rparr>" by (simp split:if_split_asm)
                      with f3 show ?thesis by (simp add:frame_def)
                    next
                      case False
                      with asm ad have "\<forall>st6' bal.
                      frame bal (st'''\<lparr>accounts := acc\<rparr>) \<and>
                      local.stmt f e\<^sub>p e' emptyStore (st'''\<lparr>accounts := acc, stack := emptyStore, memory := emptyStore\<rparr>) = Normal ((), st6') \<longrightarrow>
                      frame bal st6'" using asm Some Pair 43(3)[OF a1 ** _ _ _ *** _ _ _ _ _ ***** _ _ e'_def, where s'e = "st'''\<lparr>accounts := acc, stack:=emptyStore, memory:=emptyStore\<rparr>", of "KValue v" "Value t" t "KValue adv" "Value TAddr" TAddr st''' _ f st''' st''' "()"] using 0 by (simp add:frame_def)
                      with f3 ****** show ?thesis by blast
                    qed
                    moreover from * ** *** Some Pair ***** ****** e'_def have st'_def: "st' = st''''\<lparr>stack:=stack st''', memory := memory st'''\<rparr>" by (simp split:if_split_asm)
                    ultimately show "frame bal st'" apply safe by (simp_all add:frame_def)
                  qed
                qed
              qed
            qed
          qed
        next
          show "?RHS" (is "?LHS \<longrightarrow> ?RHS")
          proof
            assume ad: "address e = STR ''Victim''"
            show ?RHS (is "?A \<and> ?B \<and> ?C")
            proof (rule conj3)
              show ?A (is "\<forall>s val bal x. ?LHS s val bal x")
              proof (rule allI[OF allI[OF allI[OF allI]]])
                fix s val bal x
                show "?LHS s val bal x" (is "?LHS \<longrightarrow> ?RHS")
                proof
                  assume ?LHS (is "?A1 \<and> ?A2 \<and> ?A3 \<and> ?A4 \<and> ?A5")
                  then have ?A1 and ?A2 and ?A3 and ?A4 and ?A5 by auto
                  define st'' where "st'' = st\<lparr>gas := gas st - costs transfer e\<^sub>p e cd st\<rparr>"
                  define st''' where "st''' = st''\<lparr>gas := gas st'' - costs\<^sub>e (LVAL (Id (STR ''bal''))) e\<^sub>p e cd st''\<rparr>"
                  define st'''' where "st'''' = st'''\<lparr>gas := gas st''' - costs\<^sub>e SENDER e\<^sub>p e cd st'''\<rparr>"
                  from `?A1` * have c1: "gas st > costs transfer e\<^sub>p e cd st" by (auto split:if_split_asm)
                  have c2: "gas st'' > costs\<^sub>e (LVAL (Id (STR ''bal''))) e\<^sub>p e cd st''"
                  proof (rule ccontr)
                    assume "\<not> costs\<^sub>e (LVAL (Id (STR ''bal''))) e\<^sub>p e cd st'' < gas st''"
                    with c1 show False using `?A1` * st''_def st'''_def by auto
                  qed
                  with `?A4` `?A5` have 00:"expr (LVAL (Id (STR ''bal''))) e\<^sub>p e cd st'' = Normal ((KValue val, Value (TUInt 256)), st''')" using st'''_def st''_def by simp
                  moreover have "gas st'''>costs\<^sub>e SENDER e\<^sub>p e cd st'''"
                  proof (rule ccontr)
                    assume "\<not> costs\<^sub>e SENDER e\<^sub>p e cd st''' < gas st'''"
                    with c1 c2 show False using `?A1` `?A4` `?A5` * st''_def st'''_def by auto
                  qed      
                  then have **:"expr SENDER e\<^sub>p e cd st''' = Normal ((KValue (sender e), Value TAddr), st'''')" using st''''_def by simp
                  then obtain acc where ***:"Accounts.transfer (address e) (sender e) val (accounts st'''') = Some acc"
                    and ****: "ReadL\<^sub>i\<^sub>n\<^sub>t (accessBalance acc (STR ''Victim'')) = ReadL\<^sub>i\<^sub>n\<^sub>t (accessBalance (accounts st'''') (STR ''Victim'')) - (ReadL\<^sub>i\<^sub>n\<^sub>t val)"
                  proof -
                    from `?A1` * c1 00 ** obtain acc where acc_def: "Accounts.transfer (address e) (sender e) val (accounts st'''') = Some acc" using st''''_def st'''_def st''_def by (auto split: option.split_asm)
                    with ad obtain acc' where *: "subBalance (STR ''Victim'') val (accounts st'''') = Some acc'"
                      and "addBalance (sender e) val acc' = Some acc" by (simp split: option.split_asm)
                    moreover from * have "acc' = updateBalance(STR ''Victim'') (ShowL\<^sub>i\<^sub>n\<^sub>t (ReadL\<^sub>i\<^sub>n\<^sub>t (accessBalance (accounts st'''') (STR ''Victim'')) - ReadL\<^sub>i\<^sub>n\<^sub>t val)) (accounts st'''')" by (simp split: if_split_asm)
                    then have "ReadL\<^sub>i\<^sub>n\<^sub>t (accessBalance acc' (STR ''Victim'')) = ReadL\<^sub>i\<^sub>n\<^sub>t (accessBalance (accounts st'''') (STR ''Victim'')) - (ReadL\<^sub>i\<^sub>n\<^sub>t val)" using Read_ShowL_id by simp
                    moreover from `?A5` ad have "sender e \<noteq> (STR ''Victim'')" by simp
                    ultimately have "ReadL\<^sub>i\<^sub>n\<^sub>t (accessBalance acc (STR ''Victim'')) = ReadL\<^sub>i\<^sub>n\<^sub>t (accessBalance (accounts st'''') (STR ''Victim'')) - (ReadL\<^sub>i\<^sub>n\<^sub>t val)" using addBalance_eq[of "sender e" val acc' acc " STR ''Victim''"] by simp
                    with acc_def show ?thesis using that by simp
                  qed
                  show ?RHS
                  proof (cases "fmlookup e\<^sub>p (sender e)")
                    case None
                    with `?A1` 00 * ** *** have "st' = st''''\<lparr>accounts := acc\<rparr>" using c1 st''_def by auto
                    moreover from `?A2` have "fmlookup (storage st'''') (STR ''Victim'') = Some s" using st''_def st'''_def st''''_def by simp
                    moreover from `?A2` have "ReadL\<^sub>i\<^sub>n\<^sub>t (accessBalance (accounts st'''') (STR ''Victim'')) - (SUMM s + ReadL\<^sub>i\<^sub>n\<^sub>t val) \<ge> bal \<and> bal \<ge> 0"  using st''_def st'''_def st''''_def by simp
                    with **** have "ReadL\<^sub>i\<^sub>n\<^sub>t (accessBalance acc (STR ''Victim'')) - SUMM s \<ge> bal \<and> bal \<ge> 0" by simp
                    then have "ReadL\<^sub>i\<^sub>n\<^sub>t (accessBalance (accounts (st''''\<lparr>accounts := acc\<rparr>)) (STR ''Victim'')) - SUMM s \<ge> bal \<and> bal \<ge> 0" by simp
                    ultimately show ?thesis using `?A3` by (simp add:frame_def)
                  next
                    case (Some a)
                    then show ?thesis
                    proof (cases a)
                      case (Pair ct f)
                      moreover define e' where e'_def: "e'=ffold_init ct (emptyEnv (sender e) (address e) val) (fmdom ct)"
                      ultimately obtain st''''' where *****: "stmt f e\<^sub>p e' emptyStore (st''''\<lparr>accounts := acc, stack:=emptyStore, memory:=emptyStore\<rparr>) = Normal ((), st''''')" 
                        and ******: "st' = st'''''\<lparr>stack:=stack st'''', memory := memory st''''\<rparr>"  using `?A1` 00 ** *** Some *  stmt.simps(8)[of SENDER "(LVAL (Id (STR ''bal'')))" e\<^sub>p e cd st] c1 st''_def st'''_def st''''_def by (auto split: result.split_asm unit.split_asm)
                      from `?A1` * have x1: "(applyf (costs (TRANSFER ad ex) e\<^sub>p e cd) \<bind> (\<lambda>g. assert Gas
                                                                           (\<lambda>st. gas st \<le> g)
                                                                           (modify (\<lambda>st. st\<lparr>gas := gas st - g\<rparr>))))
                       st =
                      Normal ((), st'')" using st''_def by (simp split:if_split_asm)
                      from 00 `?A1` have x2: "expr ex e\<^sub>p e cd st'' = Normal ((KValue val, Value (TUInt 256)), st''')" by simp
                      have x3: "(KValue val, Value (TUInt 256)) = (KValue val, Value (TUInt 256))" by simp
                      have x4: "KValue val = KValue val" by simp
                      have  x5: "Value (TUInt 256) = Value (TUInt 256)" by simp
                      from  ** `?A1` have x6: "expr ad e\<^sub>p e cd st''' = Normal ((KValue (sender e), Value TAddr), st'''')" by simp
                      have x7: "(KValue (sender e), Value TAddr) = (KValue (sender e), Value TAddr)" by simp
                      have x8: "KValue (sender e) = KValue (sender e)" by simp
                      have x9: "Value TAddr = Value TAddr" by simp
                      have x10: "TAddr = TAddr" by simp
                      have x11: "applyf accounts st'''' = Normal (accounts st'''', st'''')" by simp
                      from *** have x12: "Accounts.transfer (address e) (sender e) val (accounts st'''') = Some acc" by simp
                      from Some Pair have x13: "fmlookup e\<^sub>p (sender e) = Some (ct,f)" by simp
                      have x14: "(ct, f) = (ct, f)" by simp
                      from e'_def have x15: "e' = ffold_init ct (emptyEnv (sender e) (address e) val) (fmdom ct)" by simp
                      have x16: "get st'''' = Normal (st'''', st'''')" by simp
                      have x17: "modify (\<lambda>st. st\<lparr>accounts := acc, stack := emptyStore, memory := emptyStore\<rparr>) st'''' = Normal ((), st''''\<lparr>accounts := acc, stack := emptyStore, memory := emptyStore\<rparr>)" by simp
                      
                      from `?A2` have "fmlookup (storage st'''') (STR ''Victim'') = Some s" using st''_def st'''_def st''''_def by simp
                      moreover from `?A2` have "ReadL\<^sub>i\<^sub>n\<^sub>t (accessBalance (accounts st'''') (STR ''Victim'')) - (SUMM s + ReadL\<^sub>i\<^sub>n\<^sub>t val) \<ge> bal \<and> bal \<ge> 0"  using st''_def st'''_def st''''_def by simp
                      with **** have "ReadL\<^sub>i\<^sub>n\<^sub>t (accessBalance acc (STR ''Victim'')) - SUMM s \<ge> bal \<and> bal \<ge> 0" by simp
                      then have "ReadL\<^sub>i\<^sub>n\<^sub>t (accessBalance (accounts (st''''\<lparr>accounts := acc, stack:=emptyStore, memory:=emptyStore\<rparr>)) (STR ''Victim'')) - SUMM s \<ge> bal \<and> bal \<ge> 0" by simp
                      moreover from `?A5` ad have "sender e \<noteq> (STR ''Victim'')" by simp
                      with e'_def have "address e' \<noteq> STR ''Victim''" using ffold_init_ad_same[of ct "(emptyEnv (sender e) (address e) val)" "(fmdom ct)" e'] by simp
                      ultimately have "frame bal st'''''" using 0 ***** 43(3)[OF x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17] `?A3` apply safe by (auto simp add:frame_def)
                      with "******" show ?RHS by (auto simp add:frame_def)
                    qed
                  qed
                qed
              qed
            next
              show ?B (is "\<forall>s bal x. ?LHS s bal x")
              proof (rule allI[OF allI[OF allI]])
                fix s bal x
                show "?LHS s bal x" (is "?LHS \<longrightarrow> ?RHS")
                proof
                  assume ?LHS
                  then show ?RHS by simp
                qed
              qed
            next
              show ?C (is "\<forall>s bal. ?LHS s bal")
              proof (rule allI[OF allI])
                fix s bal
                show "?LHS s bal" (is "?LHS \<longrightarrow> ?RHS")
                proof
                  assume ?LHS
                  then show ?RHS by simp
                qed
              qed
            qed
          qed
        qed
      qed
    qed
  qed
next
  case (44 id0 tp ex smt e\<^sub>p e\<^sub>v cd st)
  show ?case (is "?LHS \<longrightarrow> ?RHS")
  proof
    assume 0: "fmlookup e\<^sub>p STR ''Victim'' = Some (victim, SKIP)"
    show ?RHS (is "\<forall>st6'. ?RHS st6'")
    proof
      fix st6'
      show "?RHS st6'" (is "?LHS \<longrightarrow> ?RHS")
      proof
        assume *: "stmt (BLOCK ((id0, tp), ex) smt) e\<^sub>p e\<^sub>v cd st = Normal ((), st6')"
        show ?RHS (is "?LHS \<and> ?RHS")
        proof
          show "?LHS"
          proof
            assume asm: "address e\<^sub>v \<noteq> STR ''Victim''"
            show "\<forall>bal. frame bal st \<longrightarrow> frame bal st6'"
            proof
              fix bal
              show "frame bal st \<longrightarrow> frame bal st6'"
              proof
                assume ff: "frame bal st"
                with * have a1: "(applyf (costs(BLOCK ((id0, tp), ex) smt) e\<^sub>p e\<^sub>v cd) \<bind> (\<lambda>g. assert Gas (\<lambda>st. gas st \<le> g) (modify (\<lambda>st. st\<lparr>gas := gas st - g\<rparr>))))  st = Normal ((), st\<lparr>gas := gas st - costs (BLOCK ((id0, tp), ex) smt) e\<^sub>p e\<^sub>v cd st\<rparr>)" by auto
                from * ff have f1: "frame bal (st\<lparr>gas := gas st - costs (BLOCK ((id0, tp), ex) smt) e\<^sub>p e\<^sub>v cd st\<rparr>)" by (simp add:frame_def)
    
                show "frame bal st6'"
                proof (cases ex)
                  case None
                  with * obtain cd' e' st' where **:"decl id0 tp None False cd (memory (st\<lparr>gas := gas st - costs (BLOCK ((id0, tp), ex) smt) e\<^sub>p e\<^sub>v cd st\<rparr>)) cd e\<^sub>v (st\<lparr>gas := gas st - costs (BLOCK ((id0, tp), ex) smt) e\<^sub>p e\<^sub>v cd st\<rparr>) = Normal ((cd', e'), st')" by (auto split:result.split_asm if_split_asm)
                  with * have f2: "frame bal st'" using decl_frame[OF f1 **] by simp
                  moreover from * None ** obtain st'' where ***: "stmt smt e\<^sub>p e' cd' st' = Normal ((), st'')" by (simp split:if_split_asm)
                  moreover from ** have ad: "address e' = address e\<^sub>v" using decl_gas_address by simp
                  moreover from *** asm f2 ad 0 have "frame bal st''" using 44(3)[OF a1 None _ **, of cd' e'] by (simp add:frame_def)
                  moreover from * None ** *** have "st6' = st''" by (auto split:if_split_asm)
                  ultimately show ?thesis using f1 asm by auto
                next
                  case (Some ex')
                  with * obtain v t st' where **:"expr ex' e\<^sub>p e\<^sub>v cd (st\<lparr>gas := gas st - costs (BLOCK ((id0, tp), ex) smt) e\<^sub>p e\<^sub>v cd st\<rparr>) = Normal ((v, t), st')" by (auto split:result.split_asm if_split_asm)
                  with * f1 Some have f2: "frame bal st'" using 44(1)[OF a1 Some] asm 0 by simp
                  moreover from Some * ** obtain cd' e' st'' where ***:"decl id0 tp (Some (v,t)) False cd (memory st') cd e\<^sub>v st' = Normal ((cd', e'), st'')" by (auto split:result.split_asm if_split_asm)
                  with * have f3: "frame bal st''" using decl_frame[OF f2 ***] by simp
                  moreover from ** *** have ad: "address e' = address e\<^sub>v" using decl_gas_address by simp
                  moreover from * Some ** *** obtain st''' where ****: "stmt smt e\<^sub>p e' cd' st'' = Normal ((), st''')" by (simp split:if_split_asm)
                  moreover from **** asm f3 ad have "frame bal st'''" using 44(2)[OF a1 Some ** _ _ ***] 0 by (simp add:frame_def)
                  moreover from * Some ** *** **** have "st6' = st'''" by (auto split:if_split_asm)
                  ultimately show ?thesis using f1 asm by auto
                qed
              qed
            qed
          qed
        next
          show "?RHS" (is "?LHS \<longrightarrow> ?RHS")
          proof
            assume ad: "address e\<^sub>v = STR ''Victim''"
            show ?RHS (is "?A \<and> (?B \<and> ?C)")
            proof (rule conj3)
              show ?A (is "\<forall>s val bal x. ?LHS s val bal x")
              proof (rule allI[OF allI[OF allI[OF allI]]])
                fix s val bal x
                show "?LHS s val bal x" (is "?LHS \<longrightarrow> ?RHS")
                proof
                  assume ?LHS
                  then show ?RHS by simp
                qed
              qed
            next
              show ?B (is "\<forall>s bal x. ?LHS s bal x")
              proof (rule allI[OF allI[OF allI]])
                fix s bal x
                show "?LHS s bal x" (is "?LHS \<longrightarrow> ?RHS")
                proof
                  assume ?LHS
                  then show ?RHS by simp
                qed
              qed
            next
              show ?C (is "\<forall>s bal. ?LHS s bal")
              proof (rule allI[OF allI])
                fix s bal
                show "?LHS s bal" (is "?LHS \<longrightarrow> ?RHS")
                proof
                  assume ?LHS (is "?A1 \<and> ?A2 \<and> ?A3 \<and> ?A4 \<and> ?A5")
                  then have ?A1 and ?A2 and ?A3 and ?A4 and ?A5 by auto

                  define st'' where "st'' = st\<lparr>gas := gas st - costs keep e\<^sub>p e\<^sub>v cd st\<rparr>"
                  with `?A2` `?A3` have 00: "fmlookup (storage st'') (STR ''Victim'') = Some s"
                      and **: "ReadL\<^sub>i\<^sub>n\<^sub>t (accessBalance (accounts st'') (STR ''Victim'')) - (SUMM s) \<ge> bal \<and> bal \<ge> 0 \<and> POS s" by simp+
                
                  from `?A1` * st''_def obtain v t st''' cd' e' st'''' st'''''
                    where ***: "expr mylval e\<^sub>p e\<^sub>v cd st'' = Normal ((v,t), st''')"
                      and ****: "decl (STR ''bal'') (Value (TUInt 256)) (Some (v, t)) False cd (memory st''') cd e\<^sub>v st''' = Normal ((cd', e'),st'''')"
                      and *****: "stmt comp e\<^sub>p e' cd' st'''' = Normal ((), st''''')"
                      and "st6' = st'''''"
                    by (auto split:if_split_asm result.split_asm)
                
                  obtain s''' where
                      f1: "fmlookup (storage st''') (STR ''Victim'') = Some s'''"
                      and v_def: "v = KValue (accessStorage (TUInt 256) (sender e\<^sub>v + (STR ''.'' + STR ''balance'')) s''')"
                      and t_def: "t = Value (TUInt 256)"
                      and f2: "ReadL\<^sub>i\<^sub>n\<^sub>t (accessBalance (accounts st''') (STR ''Victim'')) - (SUMM s''') \<ge> bal \<and> bal \<ge> 0 \<and> POS s'''"
                    using securelval[OF *** `?A4` 00 ** ad] by auto
                
                  with **** obtain s'''' where 
                    *******: "fmlookup (storage st'''') (STR ''Victim'') = Some s''''"
                    and bbal: "ReadL\<^sub>i\<^sub>n\<^sub>t (accessBalance (accounts st'''') (STR ''Victim'')) - (SUMM s'''') \<ge> bal \<and> bal \<ge> 0 \<and> POS s''''" using decl_frame frame_def by auto
                
                  from ad `?A5` have 
                    ad2: "address e' = STR ''Victim''"
                    and ss: "sender e'\<noteq>address e'" using decl_gas_address[OF ****] by auto
                
                  then obtain x where 
                    ******: "fmlookup (denvalue e') (STR ''bal'') = Some (Value (TUInt 256), (Stackloc x))"
                    and lkup: "fmlookup (denvalue e') STR ''balance'' = Some (Storage (STMap TAddr (STValue (TUInt 256))), Storeloc STR ''balance'')"
                    and "accessStore x (stack st'''') = Some (KValue (accessStorage (TUInt 256) (sender e\<^sub>v + (STR ''.'' + STR ''balance'')) s''''))"
                  proof -
                    have "Valuetypes.convert (TUInt 256) (TUInt 256) (accessStorage (TUInt 256) (sender e\<^sub>v + (STR ''.'' + STR ''balance'')) s''') = Some (accessStorage (TUInt 256) (sender e\<^sub>v + (STR ''.'' + STR ''balance'')) s''', TUInt 256)" by simp
                    with **** v_def t_def have "append (STR ''bal'') (Value (TUInt 256)) (KValue (accessStorage (TUInt 256) (sender e\<^sub>v + (STR ''.'' + STR ''balance'')) s''')) cd e\<^sub>v st''' = Normal ((cd', e'),st'''')" by simp
                    with f1 v_def t_def have st''''_def: "st'''' = st'''\<lparr>stack := push v (stack st''')\<rparr>" and "e' = updateEnv (STR ''bal'') t (Stackloc (ShowL\<^sub>n\<^sub>a\<^sub>t (toploc (stack st''')))) e\<^sub>v" by auto
                    moreover from ******* f1 st''''_def have "Some (KValue (accessStorage (TUInt 256) (sender e\<^sub>v + (STR ''.'' + STR ''balance'')) s''')) = Some (KValue (accessStorage (TUInt 256) (sender e\<^sub>v + (STR ''.'' + STR ''balance'')) s''''))" by simp
                    ultimately show ?thesis using t_def v_def `?A4` that by simp
                  qed
                  with decl_gas_address **** have sck: "accessStore x (stack st'''') = Some (KValue (accessStorage (TUInt 256) (sender e' + (STR ''.'' + STR ''balance'')) s''''))" by simp

                  from * have a1: "(applyf (costs(BLOCK ((id0, tp), ex) smt) e\<^sub>p e\<^sub>v cd) \<bind> (\<lambda>g. assert Gas (\<lambda>st. gas st \<le> g) (modify (\<lambda>st. st\<lparr>gas := gas st - g\<rparr>))))  st = Normal ((), st\<lparr>gas := gas st - costs (BLOCK ((id0, tp), ex) smt) e\<^sub>p e\<^sub>v cd st\<rparr>)" by auto
                  from `?A1` have a2: "ex = Some (LVAL (Ref STR ''balance'' [SENDER]))" by simp
                  from `?A1` *** have a3: "local.expr (LVAL (Ref STR ''balance'' [SENDER])) e\<^sub>p e\<^sub>v cd
                       (st\<lparr>gas := gas st - costs (BLOCK ((id0, tp), ex) smt) e\<^sub>p e\<^sub>v cd st\<rparr>) =
                      Normal ((v, t), st''')" using st''_def by simp
                  from `?A1` **** have a4: "decl id0 tp (Some (v, t)) False cd (memory st''') cd e\<^sub>v st''' = Normal ((cd', e'), st'''')" by simp
                  from `?A1` ***** `st6' = st'''''` have a5: "local.stmt smt e\<^sub>p e' cd' st'''' = Normal ((), st6')" by simp
                  show "(\<exists>s'. fmlookup (storage st6') STR ''Victim'' = Some s' \<and>
                         ReadL\<^sub>i\<^sub>n\<^sub>t (accessBalance (accounts st6') (STR ''Victim'')) - (SUMM s') \<ge> bal \<and> bal \<ge> 0 \<and> POS s')"
                    using 44(2)[OF a1 a2 a3 _ _ a4, of cd' e'] 0 a5 ad2 `?A1` ******* bbal ****** lkup sck `?A4` ss apply safe by auto
                qed
              qed
            qed
          qed
        qed
      qed
    qed
  qed
qed

corollary final1:
  assumes "fmlookup ep (STR ''Victim'') = Some (victim, SKIP)"
      and "stmt (EXTERNAL (ADDRESS (STR ''Victim'')) (STR ''withdraw'') [] val) ep env cd st = Normal((), st')"
      and "address env \<noteq> (STR ''Victim'')"
      and "frame bal st"
      shows "frame bal st'"
  using assms secure(7)[of ep "(EXTERNAL (ADDRESS (STR ''Victim'')) (STR ''withdraw'') [] val)" env cd st] by simp

corollary final2:
  assumes "fmlookup ep (STR ''Victim'') = Some (victim, SKIP)"
      and "stmt (EXTERNAL (ADDRESS (STR ''Victim'')) (STR ''deposit'') [] val) ep env cd st = Normal((), st')"
      and "address env \<noteq> (STR ''Victim'')"
      and "frame bal st"
      shows "frame bal st'"
  using assms secure(7)[of ep "(EXTERNAL (ADDRESS (STR ''Victim'')) (STR ''deposit'') [] val)" env cd st] by simp

end

end
