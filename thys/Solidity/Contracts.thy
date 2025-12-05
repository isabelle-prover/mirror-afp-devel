section \<open>Contracts\<close>
theory Contracts
  imports Environment
begin

subsection \<open>Syntax of Contracts\<close>

datatype l = Id Identifier
           | Ref Identifier "e list"
and      e = INT bits int
           | UINT bits int
           | ADDRESS String.literal
           | BALANCE e
           | THIS
           | SENDER
           | VALUE
           | TRUE
           | FALSE
           | LVAL l
           | PLUS e e
           | MINUS e e
           | EQUAL e e
           | LESS e e
           | AND e e
           | OR e e
           | NOT e
           | CALL Identifier "e list"
           | ECALL e Identifier "e list"
           | CONTRACTS

datatype s = SKIP
           | BLOCK "Identifier \<times> type \<times> (e option)" s
           | ASSIGN l e
           | TRANSFER e e
           | COMP s s
           | ITE e s s
           | WHILE e s
           | INVOKE Identifier "e list"
           | EXTERNAL e Identifier "e list" e
           | NEW Identifier "e list" e

subsection \<open>state\<close>

type_synonym gas = nat

record state =   
  Accounts :: accounts
  Stack :: stack
  Memory :: memoryT
  Storage :: "address \<Rightarrow> storageT"
  Gas :: gas

lemma all_gas_le:
  assumes "state.Gas x<(state.Gas y::nat)"
      and "\<forall>z. state.Gas z < state.Gas y \<longrightarrow> P z \<longrightarrow> Q z"
    shows "\<forall>z. state.Gas z \<le> state.Gas x \<and> P z \<longrightarrow> Q z" using assms by simp

lemma all_gas_less:
  assumes "\<forall>z. state.Gas z < state.Gas y \<longrightarrow> P z"
      and "state.Gas x\<le>(state.Gas y::nat)"
    shows "\<forall>z. state.Gas z < state.Gas x \<longrightarrow> P z" using assms by simp

definition incrementAccountContracts :: "address \<Rightarrow> state \<Rightarrow> state"
  where "incrementAccountContracts ad st = st \<lparr>Accounts := (Accounts st)(ad := (Accounts st ad)\<lparr>Contracts := Suc (Contracts (Accounts st ad))\<rparr>)\<rparr>"

declare incrementAccountContracts_def [solidity_symbex]

lemma incrementAccountContracts_type[simp]:
  "Type (Accounts (incrementAccountContracts ad st) ad') = Type (Accounts st ad')"
  using incrementAccountContracts_def by simp

lemma incrementAccountContracts_bal[simp]:
  "Bal (Accounts (incrementAccountContracts ad st) ad') = Bal (Accounts st ad')"
  using incrementAccountContracts_def by simp

lemma incrementAccountContracts_stack[simp]:
  "Stack (incrementAccountContracts ad st) = Stack st"
  using incrementAccountContracts_def by simp

lemma incrementAccountContracts_memory[simp]:
  "Memory (incrementAccountContracts ad st) = Memory st"
  using incrementAccountContracts_def by simp

lemma incrementAccountContracts_storage[simp]:
  "Storage (incrementAccountContracts ad st) = Storage st"
  using incrementAccountContracts_def by simp

lemma incrementAccountContracts_gas[simp]:
  "Gas (incrementAccountContracts ad st) = Gas st"
  using incrementAccountContracts_def by simp

lemma gas_induct:
  assumes "\<And>s. \<forall>s'. Gas s' < Gas s \<longrightarrow> P s' \<Longrightarrow> P s"
  shows "P s" using assms by (rule Nat.measure_induct[of Gas])

definition emptyStorage :: "address \<Rightarrow> storageT"
where
  "emptyStorage _ = {$$}"

declare emptyStorage_def [solidity_symbex]

abbreviation mystate::state
  where "mystate \<equiv> \<lparr>
    Accounts = emptyAccount,
    Stack = emptyStore,
    Memory = emptyTypedStore,
    Storage = emptyStorage,
    Gas = 0
  \<rparr>"

datatype ex = Gas | Err

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
datatype(discs_sels) member = Method "(Identifier \<times> type) list \<times> bool \<times> s"
                | Function "(Identifier \<times> type) list \<times> bool \<times> e"
                | Var stypes

text \<open>
  A procedure environment assigns a contract to an address.
  A contract consists of
  \<^item> An assignment of contract to identifiers
  \<^item> A constructor
  \<^item> A fallback statement which is executed after money is beeing transferred to the contract.

  \url{https://docs.soliditylang.org/en/v0.8.6/Contracts.html#fallback-function}
\<close>

type_synonym contract = "(Identifier, member) fmap \<times> ((Identifier \<times> type) list \<times> s) \<times> s"

type_synonym environment\<^sub>p = "(Identifier, contract) fmap"

definition init::"(Identifier, member) fmap \<Rightarrow> Identifier \<Rightarrow> environment \<Rightarrow> environment"
  where "init ct i e = (case ct $$ i of
                                Some (Var tp) \<Rightarrow> updateEnvDup i (type.Storage tp) (Storeloc i) e
                               | _ \<Rightarrow> e)"

declare init_def [solidity_symbex]

lemma init_s11[simp]:
  assumes "fmlookup ct i = Some (Var tp)"
  shows "init ct i e = updateEnvDup i (type.Storage tp) (Storeloc i) e"
  using assms init_def by simp

lemma init_s12[simp]:
  assumes "i |\<in>| fmdom (Denvalue e)"
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
    with Some have "init ct i e = updateEnvDup i (type.Storage tp) (Storeloc i) e" using init_def by simp
    moreover from assms have "updateEnvDup i (type.Storage tp) (Storeloc i) e = e" by auto
    ultimately show ?thesis by simp
  qed
qed

lemma init_s13[simp]:
  assumes "fmlookup ct i = Some (Var tp)"
      and "\<not> i |\<in>| fmdom (Denvalue e)"
  shows "init ct i e = updateEnv i (type.Storage tp) (Storeloc i) e"
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
        proof (cases "x |\<in>| fmdom (Denvalue e)")
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
              proof (cases "y |\<in>| fmdom (Denvalue e)")
                case t1: True
                with s1 v1 True s2 v2 show ?thesis by fastforce
              next
                define e' where "e' = updateEnv y (type.Storage tp') (Storeloc y) e"
                case False
                with s2 v2 have "init ct y e = e'" using e'_def by auto
                with s1 v1 True e'_def * show ?thesis by auto
              qed
            qed
          qed
        next
          define e' where "e' = updateEnv x (type.Storage tp) (Storeloc x) e"
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
              proof (cases "y |\<in>| fmdom (Denvalue e)")
                case t1: True
                with e'_def have "y |\<in>| fmdom (Denvalue e')" by simp
                with s1 s3 v1 f1 v2 show ?thesis using e'_def by fastforce
              next
                define f' where "f' = updateEnv y (type.Storage tp') (Storeloc y) e"
                define e'' where "e'' = updateEnv y (type.Storage tp') (Storeloc y) e'"
                case f2: False
                with s3 v2 have **: "init ct y e = f'" using f'_def by auto
                show ?thesis
                proof (cases "y = x")
                  case True
                  with s3 v2 e'_def have "init ct y e' = e'" by simp
                  moreover from s3 v2 True f'_def have "init ct x f' = f'" by simp
                  ultimately show ?thesis using True by simp
                next
                  define f'' where "f'' = updateEnv x (type.Storage tp) (Storeloc x) f'"
                  case f3: False
                  with f2 have "\<not> y |\<in>| fmdom (Denvalue e')" using e'_def by simp
                  with s3 v2 e''_def have "init ct y e' = e''" by auto
                  with * have "(init ct y \<circ> init ct x) e = e''" by simp
                  moreover have "init ct x f' = f''"
                  proof -
                    from s1 v1 have "init ct x f' = updateEnvDup x (type.Storage tp) (Storeloc x) f'" by simp
                    moreover from f1 f3 have "x |\<notin>| fmdom (Denvalue f')" using f'_def by simp
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
  "Address (init ct i e) = Address e"
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
"Sender (init ct i e) = Sender e"
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
"Svalue (init ct i e) = Svalue e"
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

lemma init_contract[simp]:
"Contract (init ct i e) = Contract e"
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
    with Some show ?thesis using updateEnvDup_contract by simp
  qed
qed

lemma ffold_init_ad_same[rule_format]: "\<forall>e'. ffold (init ct) e xs = e' \<longrightarrow> Address e' = Address e \<and> Sender e' = Sender e \<and> Svalue e' = Svalue e \<and> Contract e' = Contract e"
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
    with insert have "Address e'' = Address e \<and> Sender e'' = Sender e \<and> Svalue e'' = Svalue e \<and> Contract e'' = Contract e" by blast
    with * ** *** show "Address e' = Address e \<and> Sender e' = Sender e \<and> Svalue e' = Svalue e \<and> environment.Contract e' = environment.Contract e" 
      using init_address init_sender init_svalue init_contract by metis
  qed
qed

lemma ffold_init_ad[simp]: "Address (ffold (init ct) e xs) = Address e"
  using ffold_init_ad_same by simp

lemma ffold_init_sender[simp]: "Sender (ffold (init ct) e xs) = Sender e"
  using ffold_init_ad_same by simp

lemma ffold_init_contract[simp]: "Contract (ffold (init ct) e xs) = Contract e"
  using ffold_init_ad_same by simp


lemma ffold_init_dom:
  "fmdom (Denvalue (ffold (init ct) e xs)) |\<subseteq>| fmdom (Denvalue e) |\<union>| xs"
proof (induct "xs")
  case empty
  then show ?case
  proof
    fix x
    assume "x |\<in>| fmdom (Denvalue (ffold (init ct) e {||}))"
    moreover have "ffold (init ct) e {||} = e" using FSet.comp_fun_commute.ffold_empty[OF init_commte, of ct e] by simp
    ultimately show "x |\<in>| fmdom (Denvalue e) |\<union>| {||}" by simp
  qed
next
  case (insert x xs)
  then have *: "ffold (init ct) e (finsert x xs) =
    init ct x (ffold (init ct) e xs)" using FSet.comp_fun_commute.ffold_finsert[OF init_commte] by simp

  show ?case
  proof
    fix x' assume "x' |\<in>| fmdom (Denvalue (ffold (init ct) e (finsert x xs)))"
    with * have **: "x' |\<in>| fmdom (Denvalue (init ct x (ffold (init ct) e xs)))" by simp
    then consider "x' |\<in>| fmdom (Denvalue (ffold (init ct) e xs))" | "x'=x"
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
          then have "fmlookup (Denvalue (updateEnvDup x (type.Storage x2) (Storeloc x) (ffold (init ct) e xs))) x' = fmlookup (Denvalue (ffold (init ct) e xs)) x'" using updateEnvDup_dup by simp
          moreover from ** Some Var have ***:"x' |\<in>| fmdom (Denvalue (updateEnvDup x (type.Storage x2) (Storeloc x) (ffold (init ct) e xs)))" by simp
          ultimately have "x' |\<in>| fmdom (Denvalue (ffold (init ct) e xs))" by (simp add: fmlookup_dom_iff)
          then show ?thesis using that by simp
        qed
      qed 
    qed
    then show "x' |\<in>| fmdom (Denvalue e) |\<union>| finsert x xs"
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
  assumes "ct $$ i = Some (Var tp)"
      and "i |\<notin>| fmdom (Denvalue e)"
  shows "i|\<in>|xs \<Longrightarrow> Denvalue (ffold (init ct) e xs) $$ i = Some (type.Storage tp, Storeloc i)"
proof (induct "xs")
  case empty
  then show ?case by simp
next
  case (insert x xs)
  then have *: "ffold (init ct) e (finsert x xs) =
    init ct x (ffold (init ct) e xs)" using FSet.comp_fun_commute.ffold_finsert[OF init_commte] by simp

  from insert.prems consider (a) "i |\<in>| xs" | (b) "\<not> i |\<in>| xs \<and> i = x" by auto
  then show "fmlookup (Denvalue (ffold (init ct) e (finsert x xs))) i = Some (type.Storage tp, Storeloc i)"
  proof cases
    case a
    with insert.hyps(2) have "fmlookup (Denvalue (ffold (init ct) e xs)) i = Some (type.Storage tp, Storeloc i)" by simp
    moreover have "fmlookup (Denvalue (init ct x (ffold (init ct) e xs))) i = fmlookup (Denvalue (ffold (init ct) e xs)) i"
    proof (cases "ct $$ x")
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
        with Some have "init ct x (ffold (init ct) e xs) = updateEnvDup x (type.Storage x2) (Storeloc x) (ffold (init ct) e xs)" using init_def[of ct x "(ffold (init ct) e xs)"] by simp
        moreover from insert a have "i\<noteq>x" by auto
        then have "Denvalue (updateEnvDup x (type.Storage x2) (Storeloc x) (ffold (init ct) e xs)) $$ i = Denvalue (ffold (init ct) e xs) $$ i" using updateEnvDup_dup[of x i] by simp
        ultimately show ?thesis by simp
      qed
    qed
    ultimately show ?thesis using * by simp
  next
    case b
    with assms(1) have "fmlookup ct x = Some (Var tp)" by simp
    moreover from b assms(2) have "\<not> x |\<in>| fmdom (Denvalue (ffold (init ct) e xs))" using ffold_init_dom by auto
    ultimately have "init ct x (ffold (init ct) e xs) = updateEnv x (type.Storage tp) (Storeloc x) (ffold (init ct) e xs)" by auto
    with b * show ?thesis by simp
  qed
qed

lemma ffold_init_fmdom: 
  assumes "fmlookup ct i = Some (Var tp)"
      and "i |\<notin>| fmdom (Denvalue e)"
    shows "fmlookup (Denvalue (ffold (init ct) e (fmdom ct))) i = Some (type.Storage tp, Storeloc i)"
proof -
  from assms(1) have "i |\<in>| fmdom ct" by (rule Finite_Map.fmdomI)
  then show ?thesis using ffold_init_fmap[OF assms] by simp
qed

lemma ffold_init_emptyDen:
  shows " fmlookup (Denvalue (ffold (init ct) (emptyEnv a b c d) xs)) i = Some x \<longrightarrow> i |\<in>| xs"
proof(induct xs)
  case empty
  then show ?case 
    by (simp add: comp_fun_commute.ffold_empty init_commte)
next
  case (insert x xs)
 then have *: "ffold (init ct) (emptyEnv a b c d) (finsert x xs) =
    init ct x (ffold (init ct) (emptyEnv a b c d) xs)" 
   using FSet.comp_fun_commute.ffold_finsert[OF init_commte] by simp
  then show ?case 
    by (metis Environment.select_convs(5) emptyEnv_def femptyE ffold_init_dom finsert_absorb finsert_fsubset fmdomI
        fmdom_empty funionE)
qed

lemma ffold_init_emptyDen_ran:
  shows "fmlookup (Denvalue (ffold (init ct) (emptyEnv a b c d) xs)) i = Some (type.Storage tp, Storeloc i)
          \<longrightarrow> ct $$ i = Some(Var tp) "
proof(induct xs)
  case empty
  then show ?case 
    by (simp add: comp_fun_commute.ffold_empty init_commte)
next
  case (insert x xs)
 then have *: "ffold (init ct) (emptyEnv a b c d) (finsert x xs) =
    init ct x (ffold (init ct) (emptyEnv a b c d) xs)" 
   using FSet.comp_fun_commute.ffold_finsert[OF init_commte] by simp

  then show ?case 
  proof(cases "x = i")
    case True
    then show ?thesis using * 
      by (smt (z3) member.exhaust Option.option.simps(4) type.inject(4) domIff emptyEnv_denvalue femptyE
          ffold_init_emptyDen ffold_init_fmap fmdom.rep_eq fmdom_empty fmlookup_dom_iff init_commte init_def init_s22
          init_s23 insert.hyps(1) option.inject prod.inject)
  next
    case False
    show ?thesis
    proof intros
      assume **:"Denvalue (ffold (init ct) (emptyEnv a b c d) (finsert x xs)) $$ i = Some (type.Storage tp, Storeloc i)"
      then have "Denvalue (init ct x (ffold (init ct) (emptyEnv a b c d) xs)) $$ i = Some (type.Storage tp, Storeloc i)" using * by simp
      then show " ct $$ i = Some (Var tp) " using False 
        by (metis (lifting) member.exhaust_sel domIff fmdom.rep_eq fmdomE init_s11 init_s21 init_s22 init_s23
            insert.hyps(2) updateEnvDup_dup)
    qed
  qed
qed

text\<open>The following definition allows for a more fine-grained configuration of the 
     code generator.
\<close>
definition ffold_init::"(String.literal, member) fmap \<Rightarrow> environment \<Rightarrow> String.literal fset \<Rightarrow> environment" where
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
      and "\<And>t. x = type.Memory t \<Longrightarrow> h t s = h' t s"
      and "\<And>t. x = type.Storage t \<Longrightarrow> i t s = i' t s"
    shows "(case x of Value t \<Rightarrow> f t | Calldata t \<Rightarrow> g t | type.Memory t \<Rightarrow> h t | type.Storage t \<Rightarrow> i t ) s
         = (case x' of Value t \<Rightarrow> f' t | Calldata t \<Rightarrow> g' t | type.Memory t \<Rightarrow> h' t | type.Storage t \<Rightarrow> i' t) s"
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
