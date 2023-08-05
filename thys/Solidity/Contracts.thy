section \<open>Contracts\<close>
theory Contracts
  imports Environment
begin

subsection \<open>Syntax of Contracts\<close>

datatype L = Id Identifier
           | Ref Identifier "E list"
and      E = INT nat int
           | UINT nat int
           | ADDRESS String.literal
           | BALANCE E
           | THIS
           | SENDER
           | VALUE
           | TRUE
           | FALSE
           | LVAL L
           | PLUS E E
           | MINUS E E
           | EQUAL E E
           | LESS E E
           | AND E E
           | OR E E
           | NOT E
           | CALL Identifier "E list"
           | ECALL E Identifier "E list"
           | CONTRACTS

datatype S = SKIP
           | BLOCK "(Identifier \<times> Type) \<times> (E option)" S
           | ASSIGN L E
           | TRANSFER E E
           | COMP S S
           | ITE E S S
           | WHILE E S
           | INVOKE Identifier "E list"
           | EXTERNAL E Identifier "E list" E
           | NEW Identifier "E list" E

abbreviation
  "vbits\<equiv>{8,16,24,32,40,48,56,64,72,80,88,96,104,112,120,128,
          136,144,152,160,168,176,184,192,200,208,216,224,232,240,248,256}"

lemma vbits_max[simp]:
  assumes "b1 \<in> vbits"
    and "b2 \<in> vbits"
  shows "(max b1 b2) \<in> vbits"
proof -
  consider (b1) "max b1 b2 = b1" | (b2) "max b1 b2 = b2" by (metis max_def)
  then show ?thesis
  proof cases
    case b1
    then show ?thesis using assms(1) by simp
  next
    case b2
    then show ?thesis using assms(2) by simp
  qed
qed

lemma vbits_ge_0: "(x::nat)\<in>vbits \<Longrightarrow> x>0" by auto

subsection \<open>State\<close>

type_synonym Gas = nat

record State =   
  accounts :: Accounts
  stack :: Stack
  memory :: MemoryT
  storage :: "Address \<Rightarrow> StorageT"
  gas :: Gas

lemma all_gas_le:
  assumes "gas x<(gas y::nat)"
      and "\<forall>z. gas z < gas y \<longrightarrow> P z \<longrightarrow> Q z"
    shows "\<forall>z. gas z \<le> gas x \<and> P z \<longrightarrow> Q z" using assms by simp

lemma all_gas_less:
  assumes "\<forall>z. gas z < gas y \<longrightarrow> P z"
      and "gas x\<le>(gas y::nat)"
    shows "\<forall>z. gas z < gas x \<longrightarrow> P z" using assms by simp

definition incrementAccountContracts :: "Address \<Rightarrow> State \<Rightarrow> State"
  where "incrementAccountContracts ad st = st \<lparr>accounts := (accounts st)(ad := (accounts st ad)\<lparr>contracts := Suc (contracts (accounts st ad))\<rparr>)\<rparr>"

declare incrementAccountContracts_def [solidity_symbex]

lemma incrementAccountContracts_type[simp]:
  "type (accounts (incrementAccountContracts ad st) ad') = type (accounts st ad')"
  using incrementAccountContracts_def by simp

lemma incrementAccountContracts_bal[simp]:
  "bal (accounts (incrementAccountContracts ad st) ad') = bal (accounts st ad')"
  using incrementAccountContracts_def by simp

lemma incrementAccountContracts_stack[simp]:
  "stack (incrementAccountContracts ad st) = stack st"
  using incrementAccountContracts_def by simp

lemma incrementAccountContracts_memory[simp]:
  "memory (incrementAccountContracts ad st) = memory st"
  using incrementAccountContracts_def by simp

lemma incrementAccountContracts_storage[simp]:
  "storage (incrementAccountContracts ad st) = storage st"
  using incrementAccountContracts_def by simp

lemma incrementAccountContracts_gas[simp]:
  "gas (incrementAccountContracts ad st) = gas st"
  using incrementAccountContracts_def by simp

lemma gas_induct:
  assumes "\<And>s. \<forall>s'. gas s' < gas s \<longrightarrow> P s' \<Longrightarrow> P s"
  shows "P s" using assms by (rule Nat.measure_induct[of "\<lambda>s. gas s"])

definition emptyStorage :: "Address \<Rightarrow> StorageT"
where
  "emptyStorage _ = {$$}"

declare emptyStorage_def [solidity_symbex]

abbreviation mystate::State
  where "mystate \<equiv> \<lparr>
    accounts = emptyAccount,
    stack = emptyStore,
    memory = emptyStore,
    storage = emptyStorage,
    gas = 0
  \<rparr>"

datatype Ex = Gas | Err

subsection \<open>Contracts\<close>

text \<open>
  A contract consists of methods, functions, and storage variables.

  A method is a triple consisting of
  \<^item> A list of formal parameters
  \<^item> A flag to signal external methods
  \<^item> A statement


  A function is a pair consisting of
  \<^item> A list of formal parameters
  \<^item> A flag to signal external functions
  \<^item> An expression
\<close>
datatype(discs_sels) Member = Method "(Identifier \<times> Type) list \<times> bool \<times> S"
                | Function "(Identifier \<times> Type) list \<times> bool \<times> E"
                | Var STypes

text \<open>
  A procedure environment assigns a contract to an address.
  A contract consists of
  \<^item> An assignment of contract to identifiers
  \<^item> A constructor
  \<^item> A fallback statement which is executed after money is beeing transferred to the contract.

  \url{https://docs.soliditylang.org/en/v0.8.6/contracts.html#fallback-function}
\<close>

type_synonym Contract = "(Identifier, Member) fmap \<times> ((Identifier \<times> Type) list \<times> S) \<times> S"

type_synonym Environment\<^sub>P = "(Identifier, Contract) fmap"

definition init::"(Identifier, Member) fmap \<Rightarrow> Identifier \<Rightarrow> Environment \<Rightarrow> Environment"
  where "init ct i e = (case fmlookup ct i of
                                Some (Var tp) \<Rightarrow> updateEnvDup i (Storage tp) (Storeloc i) e
                               | _ \<Rightarrow> e)"

declare init_def [solidity_symbex]

lemma init_s11[simp]:
  assumes "fmlookup ct i = Some (Var tp)"
  shows "init ct i e = updateEnvDup i (Storage tp) (Storeloc i) e"
  using assms init_def by simp

lemma init_s12[simp]:
  assumes "i |\<in>| fmdom (denvalue e)"
  shows "init ct i e = e"
proof (cases "fmlookup ct i")
  case None
  then show ?thesis using init_def by simp
next
  case (Some a)
  then show ?thesis
  proof (cases a)
    case (Method _)
    with Some show ?thesis using init_def by simp
  next
    case (Function _)
    with Some show ?thesis using init_def by simp
  next
    case (Var tp)
    with Some have "init ct i e = updateEnvDup i (Storage tp) (Storeloc i) e" using init_def by simp
    moreover from assms have "updateEnvDup i (Storage tp) (Storeloc i) e = e" by auto
    ultimately show ?thesis by simp
  qed
qed

lemma init_s13[simp]:
  assumes "fmlookup ct i = Some (Var tp)"
      and "\<not> i |\<in>| fmdom (denvalue e)"
  shows "init ct i e = updateEnv i (Storage tp) (Storeloc i) e"
  using assms init_def by auto

lemma init_s21[simp]:
  assumes "fmlookup ct i = None"
  shows "init ct i e = e"
  using assms init_def by auto

lemma init_s22[simp]:
  assumes "fmlookup ct i = Some (Method m)"
  shows "init ct i e = e"
  using assms init_def by auto

lemma init_s23[simp]:
  assumes "fmlookup ct i = Some (Function f)"
  shows "init ct i e = e"
  using assms init_def by auto

lemma init_commte: "comp_fun_commute (init ct)"
proof
  fix x y
  show "init ct y \<circ> init ct x = init ct x \<circ> init ct y"
  proof
    fix e
    show "(init ct y \<circ> init ct x) e = (init ct x \<circ> init ct y) e"
    proof (cases "fmlookup ct x")
      case None
      then show ?thesis by simp
    next
      case s1: (Some a)
      then show ?thesis
      proof (cases a)
        case (Method _)
        with s1 show ?thesis by simp
      next
        case (Function _)
        with s1 show ?thesis by simp
      next
        case v1: (Var tp)
        then show ?thesis
        proof (cases "x |\<in>| fmdom (denvalue e)")
          case True
          with s1 v1 have *: "init ct x e = e" by auto
          then show ?thesis
          proof (cases "fmlookup ct y")
            case None
            then show ?thesis by simp
          next
            case s2: (Some a)
            then show ?thesis
            proof (cases a)
              case (Method _)
              with s2 show ?thesis by simp
            next
              case (Function _)
              with s2 show ?thesis by simp
            next
              case v2: (Var tp')
              then show ?thesis
              proof (cases "y |\<in>| fmdom (denvalue e)")
                case t1: True
                with s1 v1 True s2 v2 show ?thesis by fastforce
              next
                define e' where "e' = updateEnv y (Storage tp') (Storeloc y) e"
                case False
                with s2 v2 have "init ct y e = e'" using e'_def by auto
                with s1 v1 True e'_def * show ?thesis by auto
              qed
            qed
          qed
        next
          define e' where "e' = updateEnv x (Storage tp) (Storeloc x) e"
          case f1: False
          with s1 v1 have *: "init ct x e = e'" using e'_def by auto
          then show ?thesis
          proof (cases "fmlookup ct y")
            case None
            then show ?thesis by simp
          next
            case s3: (Some a)
            then show ?thesis
            proof (cases a)
              case (Method _)
              with s3 show ?thesis by simp
            next
              case (Function _)
              with s3 show ?thesis by simp
            next
              case v2: (Var tp')
              then show ?thesis
              proof (cases "y |\<in>| fmdom (denvalue e)")
                case t1: True
                with e'_def have "y |\<in>| fmdom (denvalue e')" by simp
                with s1 s3 v1 f1 v2 show ?thesis using e'_def by fastforce
              next
                define f' where "f' = updateEnv y (Storage tp') (Storeloc y) e"
                define e'' where "e'' = updateEnv y (Storage tp') (Storeloc y) e'"
                case f2: False
                with s3 v2 have **: "init ct y e = f'" using f'_def by auto
                show ?thesis
                proof (cases "y = x")
                  case True
                  with s3 v2 e'_def have "init ct y e' = e'" by simp
                  moreover from s3 v2 True f'_def have "init ct x f' = f'" by simp
                  ultimately show ?thesis using True by simp
                next
                  define f'' where "f'' = updateEnv x (Storage tp) (Storeloc x) f'"
                  case f3: False
                  with f2 have "\<not> y |\<in>| fmdom (denvalue e')" using e'_def by simp
                  with s3 v2 e''_def have "init ct y e' = e''" by auto
                  with * have "(init ct y \<circ> init ct x) e = e''" by simp
                  moreover have "init ct x f' = f''"
                  proof -
                    from s1 v1 have "init ct x f' = updateEnvDup x (Storage tp) (Storeloc x) f'" by simp
                    moreover from f1 f3 have "x |\<notin>| fmdom (denvalue f')" using f'_def by simp
                    ultimately show ?thesis using f''_def by auto
                  qed
                  moreover from f''_def e''_def f'_def e'_def f3 have "Some f'' = Some e''" using env_reorder_neq by simp
                  ultimately show ?thesis using ** by simp
                qed
              qed
            qed
          qed
        qed
      qed
    qed
  qed
qed

lemma init_address[simp]:
  "address (init ct i e) = address e"
proof (cases "fmlookup ct i")
  case None
  then show ?thesis by simp
next
  case (Some a)
  show ?thesis
  proof (cases a)
    case (Method _)
    with Some show ?thesis by simp
  next
    case (Function _)
    with Some show ?thesis by simp
  next
    case (Var _)
    with Some show ?thesis using updateEnvDup_address updateEnvDup_sender by simp
  qed 
qed

lemma init_sender[simp]:
"sender (init ct i e) = sender e"
proof (cases "fmlookup ct i")
  case None
  then show ?thesis by simp
next
  case (Some a)
  show ?thesis
  proof (cases a)
    case (Method _)
    with Some show ?thesis by simp
  next
    case (Function _)
    with Some show ?thesis by simp
  next
    case (Var _)
    with Some show ?thesis using updateEnvDup_sender by simp
  qed 
qed

lemma init_svalue[simp]:
"svalue (init ct i e) = svalue e"
proof (cases "fmlookup ct i")
  case None
  then show ?thesis by simp
next
  case (Some a)
  show ?thesis
  proof (cases a)
    case (Method _)
    with Some show ?thesis by simp
  next
    case (Function _)
    with Some show ?thesis by simp
  next
    case (Var _)
    with Some show ?thesis using updateEnvDup_svalue by simp
  qed
qed

lemma ffold_init_ad_same[rule_format]: "\<forall>e'. ffold (init ct) e xs = e' \<longrightarrow> address e' = address e \<and> sender e' = sender e \<and> svalue e' = svalue e"
proof (induct xs)
  case empty
  then show ?case by (simp add: ffold_def)
next
  case (insert x xs)
  then have *: "ffold (init ct) e (finsert x xs) =
    init ct x (ffold (init ct) e xs)" using FSet.comp_fun_commute.ffold_finsert[OF init_commte] by simp
  show ?case
  proof (rule allI[OF impI])
    fix e' assume **: "ffold (init ct) e (finsert x xs) = e'"
    with * obtain e'' where ***: "ffold (init ct) e xs = e''" by simp
    with insert have "address e'' = address e \<and> sender e'' = sender e \<and> svalue e'' = svalue e" by blast
    with * ** *** show "address e' = address e \<and> sender e' = sender e \<and> svalue e' = svalue e" using init_address init_sender init_svalue by metis
  qed
qed

lemma ffold_init_ad[simp]: "address (ffold (init ct) e xs) = address e"
  using ffold_init_ad_same by simp

lemma ffold_init_sender[simp]: "sender (ffold (init ct) e xs) = sender e"
  using ffold_init_ad_same by simp

lemma ffold_init_dom:
  "fmdom (denvalue (ffold (init ct) e xs)) |\<subseteq>| fmdom (denvalue e) |\<union>| xs"
proof (induct "xs")
  case empty
  then show ?case
  proof
    fix x
    assume "x |\<in>| fmdom (denvalue (ffold (init ct) e {||}))"
    moreover have "ffold (init ct) e {||} = e" using FSet.comp_fun_commute.ffold_empty[OF init_commte, of ct e] by simp
    ultimately show "x |\<in>| fmdom (denvalue e) |\<union>| {||}" by simp
  qed
next
  case (insert x xs)
  then have *: "ffold (init ct) e (finsert x xs) =
    init ct x (ffold (init ct) e xs)" using FSet.comp_fun_commute.ffold_finsert[OF init_commte] by simp

  show ?case
  proof
    fix x' assume "x' |\<in>| fmdom (denvalue (ffold (init ct) e (finsert x xs)))"
    with * have **: "x' |\<in>| fmdom (denvalue (init ct x (ffold (init ct) e xs)))" by simp
    then consider "x' |\<in>| fmdom (denvalue (ffold (init ct) e xs))" | "x'=x"
    proof (cases "fmlookup ct x")
      case None
      then show ?thesis using that ** by simp
    next
      case (Some a)
      then show ?thesis
      proof (cases a)
        case (Method _)
        then show ?thesis using Some ** that by simp
      next
        case (Function _)
        then show ?thesis using Some ** that by simp
      next
        case (Var x2)
        show ?thesis
        proof (cases "x=x'")
          case True
          then show ?thesis using that by simp
        next
          case False
          then have "fmlookup (denvalue (updateEnvDup x (Storage x2) (Storeloc x) (ffold (init ct) e xs))) x' = fmlookup (denvalue (ffold (init ct) e xs)) x'" using updateEnvDup_dup by simp
          moreover from ** Some Var have ***:"x' |\<in>| fmdom (denvalue (updateEnvDup x (Storage x2) (Storeloc x) (ffold (init ct) e xs)))" by simp
          ultimately have "x' |\<in>| fmdom (denvalue (ffold (init ct) e xs))" by (simp add: fmlookup_dom_iff)
          then show ?thesis using that by simp
        qed
      qed 
    qed
    then show "x' |\<in>| fmdom (denvalue e) |\<union>| finsert x xs"
    proof cases
      case 1
      then show ?thesis using insert.hyps by auto
    next
      case 2
      then show ?thesis by simp
    qed
  qed
qed

lemma ffold_init_fmap: 
  assumes "fmlookup ct i = Some (Var tp)"
      and "i |\<notin>| fmdom (denvalue e)"
  shows "i|\<in>|xs \<Longrightarrow> fmlookup (denvalue (ffold (init ct) e xs)) i = Some (Storage tp, Storeloc i)"
proof (induct "xs")
  case empty
  then show ?case by simp
next
  case (insert x xs)
  then have *: "ffold (init ct) e (finsert x xs) =
    init ct x (ffold (init ct) e xs)" using FSet.comp_fun_commute.ffold_finsert[OF init_commte] by simp

  from insert.prems consider (a) "i |\<in>| xs" | (b) "\<not> i |\<in>| xs \<and> i = x" by auto
  then show "fmlookup (denvalue (ffold (init ct) e (finsert x xs))) i = Some (Storage tp, Storeloc i)"
  proof cases
    case a
    with insert.hyps(2) have "fmlookup (denvalue (ffold (init ct) e xs)) i = Some (Storage tp, Storeloc i)" by simp
    moreover have "fmlookup (denvalue (init ct x (ffold (init ct) e xs))) i = fmlookup (denvalue (ffold (init ct) e xs)) i"
    proof (cases "fmlookup ct x")
      case None
      then show ?thesis by simp
    next
      case (Some a)
      then show ?thesis
      proof (cases a)
        case (Method _)
        with Some show ?thesis by simp
      next
        case (Function _)
        with Some show ?thesis by simp
      next
        case (Var x2)
        with Some have "init ct x (ffold (init ct) e xs) = updateEnvDup x (Storage x2) (Storeloc x) (ffold (init ct) e xs)" using init_def[of ct x "(ffold (init ct) e xs)"] by simp
        moreover from insert a have "i\<noteq>x" by auto
        then have "fmlookup (denvalue (updateEnvDup x (Storage x2) (Storeloc x) (ffold (init ct) e xs))) i = fmlookup (denvalue (ffold (init ct) e xs)) i" using updateEnvDup_dup[of x i] by simp
        ultimately show ?thesis by simp
      qed
    qed
    ultimately show ?thesis using * by simp
  next
    case b
    with assms(1) have "fmlookup ct x = Some (Var tp)" by simp
    moreover from b assms(2) have "\<not> x |\<in>| fmdom (denvalue (ffold (init ct) e xs))" using ffold_init_dom by auto
    ultimately have "init ct x (ffold (init ct) e xs) = updateEnv x (Storage tp) (Storeloc x) (ffold (init ct) e xs)" by auto
    with b * show ?thesis by simp
  qed
qed

lemma ffold_init_fmdom: 
  assumes "fmlookup ct i = Some (Var tp)"
      and "i |\<notin>| fmdom (denvalue e)"
    shows "fmlookup (denvalue (ffold (init ct) e (fmdom ct))) i = Some (Storage tp, Storeloc i)"
proof -
  from assms(1) have "i |\<in>| fmdom ct" by (rule Finite_Map.fmdomI)
  then show ?thesis using ffold_init_fmap[OF assms] by simp
qed

text\<open>The following definition allows for a more fine-grained configuration of the 
     code generator.
\<close>
definition ffold_init::"(String.literal, Member) fmap \<Rightarrow> Environment \<Rightarrow> String.literal fset \<Rightarrow> Environment" where
          \<open>ffold_init ct a c = ffold (init ct) a c\<close>
declare ffold_init_def [simp,solidity_symbex]

lemma ffold_init_code [code]:
     \<open>ffold_init ct a c = fold (init ct) (remdups (sorted_list_of_set (fset c))) a\<close>
  using  comp_fun_commute_on.fold_set_fold_remdups ffold.rep_eq 
            ffold_init_def init_commte sorted_list_of_fset.rep_eq 
            sorted_list_of_fset_simps(1)
  by (metis comp_fun_commute.comp_fun_commute comp_fun_commute_on.intro order_refl)

lemma bind_case_stackvalue_cong [fundef_cong]:
  assumes "x = x'"
      and "\<And>v. x = KValue v \<Longrightarrow> f v s = f' v s"
      and "\<And>p. x = KCDptr p \<Longrightarrow> g p s = g' p s"
      and "\<And>p. x = KMemptr p \<Longrightarrow> h p s = h' p s"
      and "\<And>p. x = KStoptr p \<Longrightarrow> i p s = i' p s"
    shows "(case x of KValue v \<Rightarrow> f v | KCDptr p \<Rightarrow> g p | KMemptr p \<Rightarrow> h p | KStoptr p \<Rightarrow> i p) s
         = (case x' of KValue v \<Rightarrow> f' v | KCDptr p \<Rightarrow> g' p | KMemptr p \<Rightarrow> h' p | KStoptr p \<Rightarrow> i' p) s"
  using assms by (cases x, auto)

lemma bind_case_type_cong [fundef_cong]:
  assumes "x = x'"
      and "\<And>t. x = Value t \<Longrightarrow> f t s = f' t s"
      and "\<And>t. x = Calldata t \<Longrightarrow> g t s = g' t s"
      and "\<And>t. x = Memory t \<Longrightarrow> h t s = h' t s"
      and "\<And>t. x = Storage t \<Longrightarrow> i t s = i' t s"
    shows "(case x of Value t \<Rightarrow> f t | Calldata t \<Rightarrow> g t | Memory t \<Rightarrow> h t | Storage t \<Rightarrow> i t ) s
         = (case x' of Value t \<Rightarrow> f' t | Calldata t \<Rightarrow> g' t | Memory t \<Rightarrow> h' t | Storage t \<Rightarrow> i' t) s"
  using assms by (cases x, auto)

lemma bind_case_denvalue_cong [fundef_cong]:
  assumes "x = x'"
      and "\<And>a. x = (Stackloc a) \<Longrightarrow> f a s = f' a s"
      and "\<And>a. x = (Storeloc a) \<Longrightarrow> g a s = g' a s"
    shows "(case x of (Stackloc a) \<Rightarrow> f a | (Storeloc a) \<Rightarrow> g a) s
         = (case x' of (Stackloc a) \<Rightarrow> f' a | (Storeloc a) \<Rightarrow> g' a) s"
  using assms by (cases x, auto)

lemma bind_case_mtypes_cong [fundef_cong]:
  assumes "x = x'"
      and "\<And>a t. x = (MTArray a t) \<Longrightarrow> f a t s = f' a t s"
      and "\<And>p. x = (MTValue p) \<Longrightarrow> g p s = g' p s"
    shows "(case x of (MTArray a t) \<Rightarrow> f a t | (MTValue p) \<Rightarrow> g p) s
         = (case x' of (MTArray a t) \<Rightarrow> f' a t | (MTValue p) \<Rightarrow> g' p) s"
  using assms by (cases x, auto)

lemma bind_case_stypes_cong [fundef_cong]:
  assumes "x = x'"
      and "\<And>a t. x = (STArray a t) \<Longrightarrow> f a t s = f' a t s"
      and "\<And>a t. x = (STMap a t) \<Longrightarrow> g a t s = g' a t s"
      and "\<And>p. x = (STValue p) \<Longrightarrow> h p s = h' p s"
    shows "(case x of (STArray a t) \<Rightarrow> f a t | (STMap a t) \<Rightarrow> g a t | (STValue p) \<Rightarrow> h p) s
         = (case x' of (STArray a t) \<Rightarrow> f' a t | (STMap a t) \<Rightarrow> g' a t | (STValue p) \<Rightarrow> h' p) s"
  using assms by (cases x, auto)

lemma bind_case_types_cong [fundef_cong]:
  assumes "x = x'"
      and "\<And>a. x = (TSInt a) \<Longrightarrow> f a s = f' a s"
      and "\<And>a. x = (TUInt a) \<Longrightarrow> g a s = g' a s"
      and "x = TBool \<Longrightarrow> h s = h' s"
      and "x = TAddr \<Longrightarrow> i s = i' s"
    shows "(case x of (TSInt a) \<Rightarrow> f a | (TUInt a) \<Rightarrow> g a | TBool \<Rightarrow> h | TAddr \<Rightarrow> i) s
         = (case x' of (TSInt a) \<Rightarrow> f' a | (TUInt a) \<Rightarrow> g' a | TBool \<Rightarrow> h' | TAddr \<Rightarrow> i') s"
  using assms by (cases x, auto)

lemma bind_case_contract_cong [fundef_cong]:
  assumes "x = x'"
      and "\<And>a. x = Method a \<Longrightarrow> f a s = f' a s"
      and "\<And>a. x = Function a \<Longrightarrow> g a s = g' a s"
      and "\<And>a. x = Var a \<Longrightarrow> h a s = h' a s"
    shows "(case x of Method a \<Rightarrow> f a | Function a \<Rightarrow> g a | Var a \<Rightarrow> h a) s
         = (case x' of Method a \<Rightarrow> f' a | Function a \<Rightarrow> g' a | Var a \<Rightarrow> h' a) s"
  using assms by (cases x, auto)

lemma bind_case_memoryvalue_cong [fundef_cong]:
  assumes "x = x'"
      and "\<And>a. x = MValue a \<Longrightarrow> f a s = f' a s"
      and "\<And>a. x = MPointer a \<Longrightarrow> g a s = g' a s"
    shows "(case x of (MValue a) \<Rightarrow> f a | (MPointer a) \<Rightarrow> g a) s
         = (case x' of (MValue a) \<Rightarrow> f' a | (MPointer a) \<Rightarrow> g' a) s"
  using assms by (cases x, auto)

end
