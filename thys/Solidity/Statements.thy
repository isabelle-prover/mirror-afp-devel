section \<open>Statements\<close>
theory Statements
  imports Environment StateMonad
begin

subsection \<open>Syntax\<close>

subsubsection \<open>Expressions\<close>
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
           | ECALL E Identifier "E list" E

subsubsection \<open>Statements\<close>
datatype S = SKIP
           | BLOCK "(Identifier \<times> Type) \<times> (E option)" S
           | ASSIGN L E
           | TRANSFER E E
           | COMP S S
           | ITE E S S
           | WHILE E S
           | INVOKE Identifier "E list"
           | EXTERNAL E Identifier "E list" E

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

subsection \<open>Contracts\<close>

text \<open>
  A contract consists of methods or storage variables.
  A method is a triple consisting of
  \begin{itemize}
    \item A list of formal parameters
    \item A statement
    \item An optional return value
  \end{itemize}
\<close>

datatype Member = Method "(Identifier \<times> Type) list \<times> S \<times> E option"
                  | Var STypes

text \<open>
  A procedure environment assigns a contract to an address.
  A contract consists of
  \begin{itemize}
    \item An assignment of members to identifiers
    \item An optional fallback statement which is executed after money is beeing transferred to the contract.
  \end{itemize}
  \url{https://docs.soliditylang.org/en/v0.8.6/contracts.html#fallback-function}
\<close>

type_synonym Environment\<^sub>P = "(Address, (Identifier, Member) fmap \<times> S) fmap"

definition init::"(Identifier, Member) fmap \<Rightarrow> Identifier \<Rightarrow> Environment \<Rightarrow> Environment"
  where "init ct i e = (case fmlookup ct i of
                                Some (Var tp) \<Rightarrow> updateEnvDup i (Storage tp) (Storeloc i) e
                               | _ \<Rightarrow> e)"

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
    case (Method x1)
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
        case (Method x1)
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
              case (Method x1)
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
              case (Method x1)
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
  "address (init ct i e) = address e \<and> sender (init ct i e) = sender e"
proof (cases "fmlookup ct i")
  case None
  then show ?thesis by simp
next
  case (Some a)
  show ?thesis
  proof (cases a)
    case (Method x1)
    with Some show ?thesis by simp
  next
    case (Var tp)
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
    case (Method x1)
    with Some show ?thesis by simp
  next
    case (Var tp)
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
    case (Method x1)
    with Some show ?thesis by simp
  next
    case (Var tp)
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

lemma ffold_init_dom:
  "fmdom (denvalue (ffold (init ct) e xs)) |\<subseteq>| fmdom (denvalue e) |\<union>| xs"
proof (induct "xs")
  case empty
  then show ?case
  proof
    fix x
    assume "x |\<in>| fmdom (denvalue (ffold (init ct) e {||}))"
    moreover have "ffold (init ct) e {||} = e" using FSet.comp_fun_commute.ffold_empty[OF init_commte, of "init ct" e] by simp
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
        case (Method x1)
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
        case (Method x1)
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

text\<open>The following definition allows for a more fine-grained configuration of the 
     code generator.
\<close>
definition ffold_init::"(String.literal, Member) fmap \<Rightarrow> Environment \<Rightarrow> String.literal fset \<Rightarrow> Environment" where
          \<open>ffold_init ct a c = ffold (init ct) a c\<close>
declare ffold_init_def [simp]

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
      and "\<And>a. x = Var a \<Longrightarrow> g a s = g' a s"
    shows "(case x of (Method a) \<Rightarrow> f a | (Var a) \<Rightarrow> g a) s
         = (case x' of (Method a) \<Rightarrow> f' a | (Var a) \<Rightarrow> g' a) s"
  using assms by (cases x, auto)

lemma bind_case_memoryvalue_cong [fundef_cong]:
  assumes "x = x'"
      and "\<And>a. x = MValue a \<Longrightarrow> f a s = f' a s"
      and "\<And>a. x = MPointer a \<Longrightarrow> g a s = g' a s"
    shows "(case x of (MValue a) \<Rightarrow> f a | (MPointer a) \<Rightarrow> g a) s
         = (case x' of (MValue a) \<Rightarrow> f' a | (MPointer a) \<Rightarrow> g' a) s"
  using assms by (cases x, auto)

abbreviation lift ::
  "(E \<Rightarrow> Environment\<^sub>P \<Rightarrow> Environment \<Rightarrow> CalldataT \<Rightarrow> (Stackvalue * Type, Ex, State) state_monad)
  \<Rightarrow> (Types \<Rightarrow> Types \<Rightarrow> Valuetype \<Rightarrow> Valuetype \<Rightarrow> (Valuetype * Types) option)
  \<Rightarrow> E \<Rightarrow> E \<Rightarrow> Environment\<^sub>P \<Rightarrow> Environment \<Rightarrow> CalldataT \<Rightarrow> (Stackvalue * Type, Ex, State) state_monad"
where
  "lift expr f e1 e2 e\<^sub>p e cd \<equiv>
    (do {
      kv1 \<leftarrow> expr e1 e\<^sub>p e cd;
      (case kv1 of
        (KValue v1, Value t1) \<Rightarrow> (do
          {
            kv2 \<leftarrow> expr e2 e\<^sub>p e cd;
            (case kv2 of
              (KValue v2, Value t2) \<Rightarrow>
                (case f t1 t2 v1 v2 of
                  Some (v, t) \<Rightarrow> return (KValue v, Value t)
                | None \<Rightarrow> throw Err)
            | _ \<Rightarrow> (throw Err::(Stackvalue * Type, Ex, State) state_monad))
          })
      | _ \<Rightarrow> (throw Err::(Stackvalue * Type, Ex, State) state_monad))
    })"

abbreviation gascheck ::
  "(State \<Rightarrow> Gas) \<Rightarrow> (unit, Ex, State) state_monad"
where
  "gascheck check \<equiv>
  do {
    g \<leftarrow> (applyf check::(Gas, Ex, State) state_monad);
    (assert Gas (\<lambda>st. gas st \<le> g) (modify (\<lambda>st. st \<lparr>gas:=gas st - g\<rparr>)::(unit, Ex, State) state_monad))
  }"

subsection \<open>Semantics\<close>

datatype LType = LStackloc Location
               | LMemloc Location
               | LStoreloc Location


locale statement_with_gas =
  fixes costs :: "S\<Rightarrow> Environment\<^sub>P \<Rightarrow> Environment \<Rightarrow> CalldataT \<Rightarrow> State \<Rightarrow> Gas"
    and costs\<^sub>e :: "E\<Rightarrow> Environment\<^sub>P \<Rightarrow> Environment \<Rightarrow> CalldataT \<Rightarrow> State \<Rightarrow> Gas"
  assumes while_not_zero[termination_simp]: "\<And>e e\<^sub>p cd st ex s0. 0 < (costs (WHILE ex s0) e\<^sub>p e cd st) "
      and call_not_zero[termination_simp]: "\<And>e e\<^sub>p cd st i ix. 0 < (costs\<^sub>e (CALL i ix) e\<^sub>p e cd st)"
      and ecall_not_zero[termination_simp]: "\<And>e e\<^sub>p cd st a i ix val. 0 < (costs\<^sub>e (ECALL a i ix val) e\<^sub>p e cd st)"
      and invoke_not_zero[termination_simp]: "\<And>e e\<^sub>p cd st i xe. 0 < (costs (INVOKE i xe) e\<^sub>p e cd st)"
      and external_not_zero[termination_simp]: "\<And>e e\<^sub>p cd st ad i xe val. 0 < (costs (EXTERNAL ad i xe val) e\<^sub>p e cd st)"
      and transfer_not_zero[termination_simp]: "\<And>e e\<^sub>p cd st ex ad. 0 < (costs (TRANSFER ad ex) e\<^sub>p e cd st)"
begin

function msel::"bool \<Rightarrow> MTypes \<Rightarrow> Location \<Rightarrow> E list \<Rightarrow> Environment\<^sub>P \<Rightarrow> Environment \<Rightarrow> CalldataT \<Rightarrow> (Location * MTypes, Ex, State) state_monad"
     and ssel::"STypes \<Rightarrow> Location \<Rightarrow> E list \<Rightarrow> Environment\<^sub>P \<Rightarrow> Environment \<Rightarrow> CalldataT \<Rightarrow> (Location * STypes, Ex, State) state_monad"
     and lexp :: "L \<Rightarrow> Environment\<^sub>P \<Rightarrow> Environment \<Rightarrow> CalldataT \<Rightarrow> (LType * Type, Ex, State) state_monad"
     and expr::"E \<Rightarrow> Environment\<^sub>P \<Rightarrow> Environment \<Rightarrow> CalldataT \<Rightarrow> (Stackvalue * Type, Ex, State) state_monad"
     and load :: "bool \<Rightarrow> (Identifier \<times> Type) list \<Rightarrow> E list \<Rightarrow> Environment\<^sub>P \<Rightarrow> Environment \<Rightarrow> CalldataT \<Rightarrow> State \<Rightarrow> Environment \<Rightarrow> CalldataT \<Rightarrow> (Environment \<times> CalldataT \<times> State, Ex, State) state_monad"
     and rexp::"L \<Rightarrow> Environment\<^sub>P \<Rightarrow> Environment \<Rightarrow> CalldataT \<Rightarrow> (Stackvalue * Type, Ex, State) state_monad"
     and stmt :: "S \<Rightarrow> Environment\<^sub>P \<Rightarrow> Environment \<Rightarrow> CalldataT \<Rightarrow> (unit, Ex, State) state_monad"
where
  "msel _ _ _ [] _ _ _ st = throw Err st"
| "msel _ (MTValue _) _ _ _ _ _ st = throw Err st"
| "msel _ (MTArray al t) loc [x] e\<^sub>p env cd st =
    (do {
      kv \<leftarrow> expr x e\<^sub>p env cd;
      (case kv of
        (KValue v, Value t') \<Rightarrow>
          (if less t' (TUInt 256) v (ShowL\<^sub>i\<^sub>n\<^sub>t al) = Some (ShowL\<^sub>b\<^sub>o\<^sub>o\<^sub>l True, TBool)
            then return (hash loc v, t)
            else throw Err)
      | _ \<Rightarrow> throw Err)
    }) st"
(*
  Note that it is indeed possible to modify the state while evaluating the expression
  to determine the index of the array to look up.
*)
| "msel mm (MTArray al t) loc (x # y # ys) e\<^sub>p env cd st =
    (do {
      kv \<leftarrow> expr x e\<^sub>p env cd;
      (case kv of
        (KValue v, Value t') \<Rightarrow>
          (if less t' (TUInt 256) v (ShowL\<^sub>i\<^sub>n\<^sub>t al) = Some (ShowL\<^sub>b\<^sub>o\<^sub>o\<^sub>l True, TBool)
            then do {
              s \<leftarrow> applyf (\<lambda>st. if mm then memory st else cd);
              (case accessStore (hash loc v) s of
                Some (MPointer l) \<Rightarrow> msel mm t l (y#ys) e\<^sub>p env cd
              | _ \<Rightarrow> throw Err)
            } else throw Err)
      | _ \<Rightarrow> throw Err)
    }) st"
| "ssel tp loc Nil _ _ _ st = return (loc, tp) st"
| "ssel (STValue _) _ (_ # _) _ _ _ st = throw Err st"
| "ssel (STArray al t) loc (x # xs) e\<^sub>p env cd st =
    (do {
      kv \<leftarrow> expr x e\<^sub>p env cd;
      (case kv of
        (KValue v, Value t') \<Rightarrow>
          (if less t' (TUInt 256) v (ShowL\<^sub>i\<^sub>n\<^sub>t al) = Some (ShowL\<^sub>b\<^sub>o\<^sub>o\<^sub>l True, TBool)
            then ssel t (hash loc v) xs e\<^sub>p env cd
            else throw Err)
      | _ \<Rightarrow> throw Err)
    }) st"
| "ssel (STMap _ t) loc (x # xs) e\<^sub>p env cd st =
    (do {
      kv \<leftarrow> expr x e\<^sub>p env cd;
      (case kv of
        (KValue v, _) \<Rightarrow> ssel t (hash loc v) xs e\<^sub>p env cd
      | _ \<Rightarrow> throw Err)
    }) st"
| "lexp (Id i) _ e _ st =
    (case fmlookup (denvalue e) i of
      Some (tp, (Stackloc l)) \<Rightarrow> return (LStackloc l, tp)
    | Some (tp, (Storeloc l)) \<Rightarrow> return (LStoreloc l, tp)
    | _ \<Rightarrow> throw Err) st"
| "lexp (Ref i r) e\<^sub>p e cd st =
    (case fmlookup (denvalue e) i of
      Some (tp, Stackloc l) \<Rightarrow>
        do {
          k \<leftarrow> applyf (\<lambda>st. accessStore l (stack st));
          (case k of
            Some (KCDptr _) \<Rightarrow> throw Err
          | Some (KMemptr l') \<Rightarrow>
            (case tp of
              Memory t \<Rightarrow>
                do {
                  (l'', t') \<leftarrow> msel True t l' r e\<^sub>p e cd;
                  return (LMemloc l'', Memory t')
                }
            | _ \<Rightarrow> throw Err)
          | Some (KStoptr l') \<Rightarrow>
            (case tp of
              Storage t \<Rightarrow>
                do {
                  (l'', t') \<leftarrow> ssel t l' r e\<^sub>p e cd;
                  return (LStoreloc l'', Storage t')
                }
            | _ \<Rightarrow> throw Err)
          | Some (KValue _) \<Rightarrow> throw Err
          | None \<Rightarrow> throw Err)
        }
      | Some (tp, Storeloc l) \<Rightarrow>
          (case tp of
            Storage t \<Rightarrow>
              do {
                (l', t') \<leftarrow> ssel t l r e\<^sub>p e cd;
                return (LStoreloc l', Storage t')
              }
          | _ \<Rightarrow> throw Err)
      | None \<Rightarrow> throw Err) st"
| "expr (E.INT b x) e\<^sub>p e cd st =
    (do {
      gascheck (costs\<^sub>e (E.INT b x) e\<^sub>p e cd);
      (if (b \<in> vbits)
        then (return (KValue (createSInt b x), Value (TSInt b)))
        else (throw Err))
    }) st"
| "expr (UINT b x) e\<^sub>p e cd st =
    (do {
      gascheck (costs\<^sub>e (UINT b x) e\<^sub>p e cd);
      (if (b \<in> vbits)
        then (return (KValue (createUInt b x), Value (TUInt b)))
        else (throw Err))
  }) st"
| "expr (ADDRESS ad) e\<^sub>p e cd st =
    (do {
      gascheck (costs\<^sub>e (ADDRESS ad) e\<^sub>p e cd);
      return (KValue ad, Value TAddr)
    }) st"
| "expr (BALANCE ad) e\<^sub>p e cd st =
    (do {
      gascheck (costs\<^sub>e (BALANCE ad) e\<^sub>p e cd);
      kv \<leftarrow> expr ad e\<^sub>p e cd;
      (case kv of
        (KValue adv, Value TAddr) \<Rightarrow>
          return (KValue (accessBalance (accounts st) adv), Value (TUInt 256))
      | _ \<Rightarrow> throw Err)
    }) st"
| "expr THIS e\<^sub>p e cd st =
    (do {
      gascheck (costs\<^sub>e THIS e\<^sub>p e cd);
      return (KValue (address e), Value TAddr)
    }) st"
| "expr SENDER e\<^sub>p e cd st =
    (do {
      gascheck (costs\<^sub>e SENDER e\<^sub>p e cd);
      return (KValue (sender e), Value TAddr)
    }) st"
| "expr VALUE e\<^sub>p e cd st =
    (do {
      gascheck (costs\<^sub>e VALUE e\<^sub>p e cd);
      return (KValue (svalue e), Value (TUInt 256))
    }) st"
| "expr TRUE e\<^sub>p e cd st =
    (do {
      gascheck (costs\<^sub>e TRUE e\<^sub>p e cd);
      return (KValue (ShowL\<^sub>b\<^sub>o\<^sub>o\<^sub>l True), Value TBool)
    }) st"
| "expr FALSE e\<^sub>p e cd st =
    (do {
      gascheck (costs\<^sub>e FALSE e\<^sub>p e cd);
      return (KValue (ShowL\<^sub>b\<^sub>o\<^sub>o\<^sub>l False), Value TBool)
    }) st"
| "expr (NOT x) e\<^sub>p e cd st =
    (do {
      gascheck (costs\<^sub>e (NOT x) e\<^sub>p e cd);
      kv \<leftarrow> expr x e\<^sub>p e cd;
      (case kv of
        (KValue v, Value t) \<Rightarrow>
          (if v = ShowL\<^sub>b\<^sub>o\<^sub>o\<^sub>l True
            then expr FALSE e\<^sub>p e cd
            else (if v = ShowL\<^sub>b\<^sub>o\<^sub>o\<^sub>l False
              then expr TRUE e\<^sub>p e cd
              else throw Err))
      | _ \<Rightarrow> throw Err)
    }) st"
| "expr (PLUS e1 e2) e\<^sub>p e cd st = (gascheck (costs\<^sub>e (PLUS e1 e2) e\<^sub>p e cd) \<bind> (\<lambda>_. lift expr add e1 e2 e\<^sub>p e cd)) st"
| "expr (MINUS e1 e2) e\<^sub>p e cd st = (gascheck (costs\<^sub>e (MINUS e1 e2) e\<^sub>p e cd) \<bind> (\<lambda>_. lift expr sub e1 e2 e\<^sub>p e cd)) st"
| "expr (LESS e1 e2) e\<^sub>p e cd st = (gascheck (costs\<^sub>e (LESS e1 e2) e\<^sub>p e cd) \<bind> (\<lambda>_. lift expr less e1 e2 e\<^sub>p e cd)) st"
| "expr (EQUAL e1 e2) e\<^sub>p e cd st = (gascheck (costs\<^sub>e (EQUAL e1 e2) e\<^sub>p e cd) \<bind> (\<lambda>_. lift expr equal e1 e2 e\<^sub>p e cd)) st"
| "expr (AND e1 e2) e\<^sub>p e cd st = (gascheck (costs\<^sub>e (AND e1 e2) e\<^sub>p e cd) \<bind> (\<lambda>_. lift expr vtand e1 e2 e\<^sub>p e cd)) st"
| "expr (OR e1 e2) e\<^sub>p e cd st = (gascheck (costs\<^sub>e (OR e1 e2) e\<^sub>p e cd) \<bind> (\<lambda>_. lift expr vtor e1 e2 e\<^sub>p e cd)) st"
| "expr (LVAL i) e\<^sub>p e cd st =
    (do {
      gascheck (costs\<^sub>e (LVAL i) e\<^sub>p e cd);
      rexp i e\<^sub>p e cd
    }) st"
(* Notes about method calls:
   - Internal method calls use a fresh environment and stack but keep the memory [1]
   - External method calls use a fresh environment and stack and memory [2]
   [1]: https://docs.soliditylang.org/en/v0.8.5/control-structures.html#internal-function-calls
   [2]: https://docs.soliditylang.org/en/v0.8.5/control-structures.html#external-function-calls

TODO: Functions with no return value should be able to execute
*)
| "expr (CALL i xe) e\<^sub>p e cd st =
    (do {
      gascheck (costs\<^sub>e (CALL i xe) e\<^sub>p e cd);
      (case fmlookup e\<^sub>p (address e) of
         Some (ct, _) \<Rightarrow>
           (case fmlookup ct i of
             Some (Method (fp, f, Some x)) \<Rightarrow>
               let e' = ffold_init ct (emptyEnv (address e) (sender e) (svalue e)) (fmdom ct)
               in (do {
                 st' \<leftarrow> applyf (\<lambda>st. st\<lparr>stack:=emptyStore\<rparr>);
                 (e'', cd', st'') \<leftarrow> load False fp xe e\<^sub>p e' emptyStore st' e cd;
                 st''' \<leftarrow> get;
                 put st'';
                 stmt f e\<^sub>p e'' cd';
                 rv \<leftarrow> expr x e\<^sub>p e'' cd';
                 modify (\<lambda>st. st\<lparr>stack:=stack st''', memory := memory st'''\<rparr>);
                 return rv
               })
           | _ \<Rightarrow> throw Err)
       | None \<Rightarrow> throw Err)
    }) st"
| "expr (ECALL ad i xe val) e\<^sub>p e cd st =
    (do {
      gascheck (costs\<^sub>e (ECALL ad i xe val) e\<^sub>p e cd);
      kad \<leftarrow> expr ad e\<^sub>p e cd;
      (case kad of
        (KValue adv, Value TAddr) \<Rightarrow>
        (case fmlookup e\<^sub>p adv of
           Some (ct, _) \<Rightarrow>
             (case fmlookup ct i of
               Some (Method (fp, f, Some x)) \<Rightarrow>
               (do {
                 kv \<leftarrow> expr val e\<^sub>p e cd;
                 (case kv of
                   (KValue v, Value t) \<Rightarrow>
                     let e' = ffold_init ct (emptyEnv adv (address e) v) (fmdom ct)
                     in (do {
                       st' \<leftarrow> applyf (\<lambda>st. st\<lparr>stack:=emptyStore, memory:=emptyStore\<rparr>);
                       (e'', cd', st'') \<leftarrow> load True fp xe e\<^sub>p e' emptyStore st' e cd;
                       st''' \<leftarrow> get;
                       (case transfer (address e) adv v (accounts st'') of
                         Some acc \<Rightarrow>
                           do {
                             put (st''\<lparr>accounts := acc\<rparr>);
                             stmt f e\<^sub>p e'' cd';
                             rv \<leftarrow> expr x e\<^sub>p e'' cd';
                             modify (\<lambda>st. st\<lparr>stack:=stack st''', memory := memory st'''\<rparr>);
                             return rv
                          }
                       | None \<Rightarrow> throw Err)
                     })
                 | _ \<Rightarrow> throw Err)
               })
             | _ \<Rightarrow> throw Err)
        | None \<Rightarrow> throw Err)
      | _ \<Rightarrow> throw Err)
    }) st"
| "load cp ((i\<^sub>p, t\<^sub>p)#pl) (e#el) e\<^sub>p e\<^sub>v' cd' st' e\<^sub>v cd st =
    (do {
      (v, t) \<leftarrow> expr e e\<^sub>p e\<^sub>v cd;
      st'' \<leftarrow> get;
      put st';
      (cd'', e\<^sub>v'') \<leftarrow> decl i\<^sub>p t\<^sub>p (Some (v,t)) cp cd (memory st'') cd' e\<^sub>v';
      st''' \<leftarrow> get;
      put st'';
      load cp pl el e\<^sub>p e\<^sub>v'' cd'' st''' e\<^sub>v cd
    }) st"
| "load _ [] (_#_) _ _ _ _ _ _ st = throw Err st"
| "load _ (_#_) [] _ _ _ _ _ _ st = throw Err st"
| "load _ [] [] _ e\<^sub>v' cd' st' e\<^sub>v cd st = return (e\<^sub>v', cd', st') st"
(*TODO: Should be possible to simplify*)
| "rexp (Id i) e\<^sub>p e cd st =
    (case fmlookup (denvalue e) i of
      Some (tp, Stackloc l) \<Rightarrow>
        do {
          s \<leftarrow> applyf (\<lambda>st. accessStore l (stack st));
          (case s of
            Some (KValue v) \<Rightarrow> return (KValue v, tp)
          | Some (KCDptr p) \<Rightarrow> return (KCDptr p, tp)
          | Some (KMemptr p) \<Rightarrow> return (KMemptr p, tp)
          | Some (KStoptr p) \<Rightarrow> return (KStoptr p, tp)
          | _ \<Rightarrow> throw Err)
        }
    | Some (Storage (STValue t), Storeloc l) \<Rightarrow>
      do {
        so \<leftarrow> applyf (\<lambda>st. fmlookup (storage st) (address e));
        (case so of
          Some s \<Rightarrow> return (KValue (accessStorage t l s), Value t)
        | None \<Rightarrow> throw Err)
      }
    | Some (Storage (STArray x t), Storeloc l) \<Rightarrow> return (KStoptr l, Storage (STArray x t))
    | _ \<Rightarrow> throw Err) st"
| "rexp (Ref i r) e\<^sub>p e cd st =
    (case fmlookup (denvalue e) i of
      Some (tp, (Stackloc l)) \<Rightarrow>
        do {
          kv \<leftarrow> applyf (\<lambda>st. accessStore l (stack st));
          (case kv of
            Some (KCDptr l') \<Rightarrow>
              (case tp of
                Calldata t \<Rightarrow>
                  do {
                    (l'', t') \<leftarrow> msel False t l' r e\<^sub>p e cd;
                    (case t' of
                      MTValue t'' \<Rightarrow>
                        (case accessStore l'' cd of
                          Some (MValue v) \<Rightarrow> return (KValue v, Value t'')
                        | _ \<Rightarrow> throw Err)
                    | MTArray x t'' \<Rightarrow>
                        (case accessStore l'' cd of
                          Some (MPointer p) \<Rightarrow> return (KCDptr p, Calldata (MTArray x t''))
                        | _ \<Rightarrow> throw Err))
                  }
              | _ \<Rightarrow> throw Err)
          | Some (KMemptr l') \<Rightarrow>
              (case tp of
                Memory t \<Rightarrow>
                do {
                  (l'', t') \<leftarrow> msel True t l' r e\<^sub>p e cd;
                  (case t' of
                    MTValue t'' \<Rightarrow>
                    do {
                      mv \<leftarrow> applyf (\<lambda>st. accessStore l'' (memory st));
                      (case mv of
                        Some (MValue v) \<Rightarrow> return (KValue v, Value t'')
                      | _ \<Rightarrow> throw Err)
                    }
                  | MTArray x t'' \<Rightarrow>
                    do {
                      mv \<leftarrow> applyf (\<lambda>st. accessStore l'' (memory st));
                      (case mv of
                        Some (MPointer p) \<Rightarrow> return (KMemptr p, Memory (MTArray x t''))
                      | _ \<Rightarrow> throw Err)
                    }
                  )
                }
              | _ \<Rightarrow> throw Err)
          | Some (KStoptr l') \<Rightarrow>
              (case tp of
                Storage t \<Rightarrow>
                do {
                  (l'', t') \<leftarrow> ssel t l' r e\<^sub>p e cd;
                  (case t' of
                    STValue t'' \<Rightarrow>
                      do {
                        so \<leftarrow> applyf (\<lambda>st. fmlookup (storage st) (address e));
                        (case so of
                          Some s \<Rightarrow> return (KValue (accessStorage t'' l'' s), Value t'')
                        | None \<Rightarrow> throw Err)
                      }
                  | STArray _ _ \<Rightarrow> return (KStoptr l'', Storage t')
                  | STMap _ _ \<Rightarrow> return (KStoptr l'', Storage t'))
                }
              | _ \<Rightarrow> throw Err)
          | _ \<Rightarrow> throw Err)
        }
    | Some (tp, (Storeloc l)) \<Rightarrow>
        (case tp of
          Storage t \<Rightarrow>
          do {
            (l', t') \<leftarrow> ssel t l r e\<^sub>p e cd;
            (case t' of
              STValue t'' \<Rightarrow>
                do {
                  so \<leftarrow> applyf (\<lambda>st. fmlookup (storage st) (address e));
                  (case so of
                    Some s \<Rightarrow> return (KValue (accessStorage t'' l' s), Value t'')
                  | None \<Rightarrow> throw Err)
                }
            | STArray _ _ \<Rightarrow> return (KStoptr l', Storage t')
            | STMap _ _ \<Rightarrow> return (KStoptr l', Storage t'))
          }
        | _ \<Rightarrow> throw Err)
    | None \<Rightarrow> throw Err) st"
| "stmt SKIP e\<^sub>p e cd st = gascheck (costs SKIP e\<^sub>p e cd) st"
| "stmt (ASSIGN lv ex) e\<^sub>p env cd st =
    (do {
      gascheck (costs (ASSIGN lv ex) e\<^sub>p env cd);
      re \<leftarrow> expr ex e\<^sub>p env cd;
      (case re of
        (KValue v, Value t) \<Rightarrow>
          do {
            rl \<leftarrow> lexp lv e\<^sub>p env cd;
            (case rl of
              (LStackloc l, Value t') \<Rightarrow> 
                (case convert t t' v of
                   Some (v', _) \<Rightarrow> modify (\<lambda>st. st \<lparr>stack := updateStore l (KValue v') (stack st)\<rparr>)
                 | None \<Rightarrow> throw Err)
            | (LStoreloc l, Storage (STValue t')) \<Rightarrow>
                (case convert t t' v of
                  Some (v', _) \<Rightarrow>
                    do {
                      so \<leftarrow> applyf (\<lambda>st. fmlookup (storage st) (address env));
                      (case so of
                        Some s \<Rightarrow> modify (\<lambda>st. st\<lparr>storage := fmupd (address env) (fmupd l v' s) (storage st)\<rparr>)
                      | None \<Rightarrow> throw Err)
                  }
                | None \<Rightarrow> throw Err)
            | (LMemloc l, Memory (MTValue t')) \<Rightarrow>
                (case convert t t' v of
                  Some (v', _) \<Rightarrow> modify (\<lambda>st. st\<lparr>memory := updateStore l (MValue v') (memory st)\<rparr>)
                | None \<Rightarrow> throw Err)
            | _ \<Rightarrow> throw Err)
          }
        | (KCDptr p, Calldata (MTArray x t)) \<Rightarrow>
          do {
            rl \<leftarrow> lexp lv e\<^sub>p env cd;
            (case rl of
              (LStackloc l, Memory _) \<Rightarrow> modify (\<lambda>st. st \<lparr>stack := updateStore l (KCDptr p) (stack st)\<rparr>)
            | (LStackloc l, Storage _) \<Rightarrow>
                do {
                  sv \<leftarrow> applyf (\<lambda>st. accessStore l (stack st));
                  (case sv of
                    Some (KStoptr p') \<Rightarrow>
                      do {
                        so \<leftarrow> applyf (\<lambda>st. fmlookup (storage st) (address env));
                        (case so of
                          Some s \<Rightarrow> 
                            (case cpm2s p p' x t cd s of
                              Some s' \<Rightarrow> modify (\<lambda>st. st \<lparr>storage := fmupd (address env) s' (storage st)\<rparr>)
                            | None \<Rightarrow> throw Err)
                        | None \<Rightarrow> throw Err)
                    }
                  | _ \<Rightarrow> throw Err)
                }
             | (LStoreloc l, _) \<Rightarrow>
                do {
                  so \<leftarrow> applyf (\<lambda>st. fmlookup (storage st) (address env));
                  (case so of
                    Some s \<Rightarrow> 
                      (case cpm2s p l x t cd s of
                         Some s' \<Rightarrow> modify (\<lambda>st. st \<lparr>storage := fmupd (address env) s' (storage st)\<rparr>)
                       | None \<Rightarrow> throw Err)
                  | None \<Rightarrow> throw Err)
                }
             | (LMemloc l, _) \<Rightarrow>
                do {
                  cs \<leftarrow> applyf (\<lambda>st. cpm2m p l x t cd (memory st));
                  (case cs of
                    Some m \<Rightarrow> modify (\<lambda>st. st \<lparr>memory := m\<rparr>)
                  | None \<Rightarrow> throw Err)
                }
             | _ \<Rightarrow> throw Err)
          }
        | (KMemptr p, Memory (MTArray x t)) \<Rightarrow>
            do {
              rl \<leftarrow> lexp lv e\<^sub>p env cd;
              (case rl of
                (LStackloc l, Memory _) \<Rightarrow> modify (\<lambda>st. st\<lparr>stack := updateStore l (KMemptr p) (stack st)\<rparr>)
              | (LStackloc l, Storage _) \<Rightarrow>
                  do {
                    sv \<leftarrow> applyf (\<lambda>st. accessStore l (stack st));
                    (case sv of
                      Some (KStoptr p') \<Rightarrow>
                      do {
                        so \<leftarrow> applyf (\<lambda>st. fmlookup (storage st) (address env));
                        (case so of
                          Some s \<Rightarrow> 
                            do {
                              cs \<leftarrow> applyf (\<lambda>st. cpm2s p p' x t (memory st) s);
                              (case cs of
                              Some s' \<Rightarrow> modify (\<lambda>st. st \<lparr>storage := fmupd (address env) s' (storage st)\<rparr>)
                            | None \<Rightarrow> throw Err)
                            }
                        | None \<Rightarrow> throw Err)
                      }
                    | _ \<Rightarrow> throw Err)
                  }
              | (LStoreloc l, _) \<Rightarrow>
                  do {
                    so \<leftarrow> applyf (\<lambda>st. fmlookup (storage st) (address env));
                    (case so of
                      Some s \<Rightarrow> 
                        do {
                          cs \<leftarrow> applyf (\<lambda>st. cpm2s p l x t (memory st) s);
                          (case cs of
                            Some s' \<Rightarrow> modify (\<lambda>st. st \<lparr>storage := fmupd (address env) s' (storage st)\<rparr>)
                          | None \<Rightarrow> throw Err)
                        }
                    | None \<Rightarrow> throw Err)
                  }
              | (LMemloc l, _) \<Rightarrow> modify (\<lambda>st. st \<lparr>memory := updateStore l (MPointer p) (memory st)\<rparr>)
              | _ \<Rightarrow> throw Err)
            }
        | (KStoptr p, Storage (STArray x t)) \<Rightarrow>
            do {
              rl \<leftarrow> lexp lv e\<^sub>p env cd;
              (case rl of
                (LStackloc l, Memory _) \<Rightarrow>
                  do {
                    sv \<leftarrow> applyf (\<lambda>st. accessStore l (stack st));
                    (case sv of
                      Some (KMemptr p') \<Rightarrow>
                        do {
                          so \<leftarrow> applyf (\<lambda>st. fmlookup (storage st) (address env));
                          (case so of
                            Some s \<Rightarrow> 
                              do {
                                cs \<leftarrow> applyf (\<lambda>st. cps2m p p' x t s (memory st));
                                (case cs of
                                  Some m \<Rightarrow> modify (\<lambda>st. st\<lparr>memory := m\<rparr>)
                                | None \<Rightarrow> throw Err)
                              }
                          | None \<Rightarrow> throw Err)
                        }
                    | _ \<Rightarrow> throw Err)
                  }
              | (LStackloc l, Storage _) \<Rightarrow> modify (\<lambda>st. st\<lparr>stack := updateStore l (KStoptr p) (stack st)\<rparr>)
              | (LStoreloc l, _) \<Rightarrow>
                  do {
                    so \<leftarrow> applyf (\<lambda>st. fmlookup (storage st) (address env));
                    (case so of
                      Some s \<Rightarrow> 
                        (case copy p l x t s of
                          Some s' \<Rightarrow> modify (\<lambda>st. st \<lparr>storage := fmupd (address env) s' (storage st)\<rparr>)
                        | None \<Rightarrow> throw Err)
                     | None \<Rightarrow> throw Err)
                  }
              | (LMemloc l, _) \<Rightarrow>
                  do {
                    so \<leftarrow> applyf (\<lambda>st. fmlookup (storage st) (address env));
                    (case so of
                      Some s \<Rightarrow> 
                        do {
                          cs \<leftarrow> applyf (\<lambda>st. cps2m p l x t s (memory st));
                          (case cs of
                            Some m \<Rightarrow> modify (\<lambda>st. st\<lparr>memory := m\<rparr>)
                          | None \<Rightarrow> throw Err)
                        }
                    | None \<Rightarrow> throw Err)
                  }
              | _ \<Rightarrow> throw Err)
            }
        | (KStoptr p, Storage (STMap t t')) \<Rightarrow>
            do {
              rl \<leftarrow> lexp lv e\<^sub>p env cd;
              (case rl of
                (LStackloc l, _) \<Rightarrow> modify (\<lambda>st. st\<lparr>stack := updateStore l (KStoptr p) (stack st)\<rparr>)
              | _ \<Rightarrow> throw Err)
            }
        | _ \<Rightarrow> throw Err)
    }) st"
| "stmt (COMP s1 s2) e\<^sub>p e cd st =
    (do {
      gascheck (costs (COMP s1 s2) e\<^sub>p e cd);
      stmt s1 e\<^sub>p e cd;
      stmt s2 e\<^sub>p e cd
    }) st"
| "stmt (ITE ex s1 s2) e\<^sub>p e cd st =
    (do {
      gascheck (costs (ITE ex s1 s2)  e\<^sub>p e cd);
      v \<leftarrow> expr ex e\<^sub>p e cd;
      (case v of
        (KValue b, Value TBool) \<Rightarrow>
            (if b = ShowL\<^sub>b\<^sub>o\<^sub>o\<^sub>l True
              then stmt s1 e\<^sub>p e cd
              else stmt s2 e\<^sub>p e cd)
      | _ \<Rightarrow> throw Err)
    }) st"
| "stmt (WHILE ex s0) e\<^sub>p e cd st =
    (do {
      gascheck (costs (WHILE ex s0) e\<^sub>p e cd);
      v \<leftarrow> expr ex e\<^sub>p e cd;
      (case v of
        (KValue b, Value TBool) \<Rightarrow>
          (if b = ShowL\<^sub>b\<^sub>o\<^sub>o\<^sub>l True
            then do {
              stmt s0 e\<^sub>p e cd;
              stmt (WHILE ex s0) e\<^sub>p e cd
            }
            else return ())
      | _ \<Rightarrow> throw Err)
    }) st"
| "stmt (INVOKE i xe) e\<^sub>p e cd st =
    (do {
      gascheck (costs (INVOKE i xe) e\<^sub>p e cd);
      (case fmlookup e\<^sub>p (address e) of
          Some (ct, _) \<Rightarrow>
            (case fmlookup ct i of
              Some (Method (fp, f, None)) \<Rightarrow>
                 (let e' = ffold_init ct (emptyEnv (address e) (sender e) (svalue e)) (fmdom ct)
                 in (do {
                    st' \<leftarrow> applyf (\<lambda>st. (st\<lparr>stack:=emptyStore\<rparr>));
                    (e'', cd', st'') \<leftarrow> load False fp xe e\<^sub>p e' emptyStore st' e cd;
                    st''' \<leftarrow> get;
                    put st'';
                    stmt f e\<^sub>p e'' cd';
                    modify (\<lambda>st. st\<lparr>stack:=stack st''', memory := memory st'''\<rparr>)
                  }))
            | _ \<Rightarrow> throw Err)
        | None  \<Rightarrow> throw Err)
    }) st"
(*External Method calls allow to send some money val with it*)
(*However this transfer does NOT trigger a fallback*)
| "stmt (EXTERNAL ad i xe val) e\<^sub>p e cd st =
    (do {
      gascheck (costs (EXTERNAL ad i xe val) e\<^sub>p e cd);
      kad \<leftarrow> expr ad e\<^sub>p e cd;
      (case kad of
        (KValue adv, Value TAddr) \<Rightarrow>
          (case fmlookup e\<^sub>p adv of
            Some (ct, fb) \<Rightarrow>
              (do {
                kv \<leftarrow> expr val e\<^sub>p e cd;
                (case kv of
                  (KValue v, Value t) \<Rightarrow>
                    (case fmlookup ct i of
                      Some (Method (fp, f, None)) \<Rightarrow>
                      let e' = ffold_init ct (emptyEnv adv (address e) v) (fmdom ct)
                      in (do {
                        st' \<leftarrow> applyf (\<lambda>st. st\<lparr>stack:=emptyStore, memory:=emptyStore\<rparr>);
                        (e'', cd', st'') \<leftarrow> load True fp xe e\<^sub>p e' emptyStore st' e cd;
                        st''' \<leftarrow> get;
                        (case transfer (address e) adv v (accounts st'') of
                          Some acc \<Rightarrow>
                            do {
                              put (st''\<lparr>accounts := acc\<rparr>);
                              stmt f e\<^sub>p e'' cd';
                              modify (\<lambda>st. st\<lparr>stack:=stack st''', memory := memory st'''\<rparr>)
                            }
                          | None \<Rightarrow> throw Err)
                       })
                    | None \<Rightarrow>
                      do {
                        st' \<leftarrow> get;
                        (case transfer (address e) adv v (accounts st') of
                          Some acc \<Rightarrow>
                            do {
                              st'' \<leftarrow> get;
                              modify (\<lambda>st. st\<lparr>accounts := acc,stack:=emptyStore, memory:=emptyStore\<rparr>);
                              stmt fb e\<^sub>p (emptyEnv adv (address e) v) cd;
                              modify (\<lambda>st. st\<lparr>stack:=stack st'', memory := memory st''\<rparr>)
                            }
                        | None \<Rightarrow> throw Err)
                      }
                    | _ \<Rightarrow> throw Err)
                | _ \<Rightarrow> throw Err)
              })
          | None \<Rightarrow> throw Err)
      | _ \<Rightarrow> throw Err)
    }) st"
| "stmt (TRANSFER ad ex) e\<^sub>p e cd st =
    (do {
      gascheck (costs (TRANSFER ad ex) e\<^sub>p e cd);
      kv \<leftarrow> expr ex e\<^sub>p e cd;
      (case kv of
        (KValue v, Value t) \<Rightarrow>
          (do {
            kv' \<leftarrow> expr ad e\<^sub>p e cd;
            (case kv' of
              (KValue adv, Value TAddr) \<Rightarrow>
                (do {
                  acs \<leftarrow> applyf accounts;
                  (case transfer (address e) adv v acs of
                    Some acc \<Rightarrow> (case fmlookup e\<^sub>p adv of
                                  Some (ct, f) \<Rightarrow>
                                    let e' = ffold_init ct (emptyEnv adv (address e) v) (fmdom ct)
                                    in (do {
                                      st' \<leftarrow> get;
                                      modify (\<lambda>st. (st\<lparr>accounts := acc, stack:=emptyStore, memory:=emptyStore\<rparr>));
                                      stmt f e\<^sub>p e' emptyStore;
                                      modify (\<lambda>st. st\<lparr>stack:=stack st', memory := memory st'\<rparr>)
                                    })
                                | None \<Rightarrow> modify (\<lambda>st. (st\<lparr>accounts := acc\<rparr>)))
                  | None \<Rightarrow> throw Err)
                })
            | _ \<Rightarrow> throw Err)
          })
      | _ \<Rightarrow> throw Err)
    }) st"
| "stmt (BLOCK ((id0, tp), ex) s) e\<^sub>p e\<^sub>v cd st =
    (do {
      gascheck (costs (BLOCK ((id0, tp), ex) s) e\<^sub>p e\<^sub>v cd);
      (case ex of
         None \<Rightarrow> (do {
           mem \<leftarrow> applyf memory;
           (cd', e') \<leftarrow> decl id0 tp None False cd mem cd e\<^sub>v;
           stmt s e\<^sub>p e' cd'
         })
       | Some ex' \<Rightarrow> (do {
           (v, t) \<leftarrow> expr ex' e\<^sub>p e\<^sub>v cd;
           mem \<leftarrow> applyf memory;
           (cd', e') \<leftarrow> decl id0 tp (Some (v, t)) False cd mem cd e\<^sub>v;
           stmt s e\<^sub>p e' cd'
         }))
    }) st"
  by pat_completeness auto

subsection \<open>Gas Consumption\<close>

lemma lift_gas:
  assumes "lift expr f e1 e2 e\<^sub>p e cd st = Normal ((v, t), st4')"
      and "\<And>st4' v4 t4. expr e1 e\<^sub>p e cd st = Normal ((v4, t4), st4') \<Longrightarrow> gas st4' \<le> gas st"
      and "\<And>x1 x y xa ya x1a x1b st4' v4 t4. expr e1 e\<^sub>p e cd st = Normal (x, y)
            \<Longrightarrow> (xa, ya) = x
            \<Longrightarrow> xa = KValue x1a
            \<Longrightarrow> ya = Value x1b
            \<Longrightarrow> expr e2 e\<^sub>p e cd y = Normal ((v4, t4), st4')
          \<Longrightarrow> gas st4' \<le> gas y"
      shows "gas st4' \<le> gas st"
proof (cases "expr e1 e\<^sub>p e cd st")
  case (n a st')
  then show ?thesis
  proof (cases a)
    case (Pair b c)
    then show ?thesis
    proof (cases b)
      case (KValue v1)
      then show ?thesis
      proof (cases c)
        case (Value t1)
        then show ?thesis
        proof (cases "expr e2 e\<^sub>p e cd st'")
          case r2: (n a' st'')
          then show ?thesis
          proof (cases a')
            case p2: (Pair b c)
            then show ?thesis
            proof (cases b)
              case v2: (KValue v2)
              then show ?thesis
              proof (cases c)
                case t2: (Value t2)
                then show ?thesis
                proof (cases "f t1 t2 v1 v2")
                  case None
                  with assms n Pair KValue Value r2 p2 v2 t2 show ?thesis by simp
                next
                  case (Some a'')
                  then show ?thesis
                  proof (cases a'')
                    case p3: (Pair v t)
                    with assms n Pair KValue Value r2 p2 v2 t2 Some have "gas st4'\<le>gas st''" by simp
                    moreover from assms n Pair KValue Value r2 p2 v2 t2 Some have "gas st''\<le>gas st'" by simp
                    moreover from assms n Pair KValue Value r2 p2 v2 t2 Some have "gas st'\<le>gas st" by simp
                    ultimately show ?thesis by arith
                  qed
                qed
              next
                case (Calldata x2)
                with assms n Pair KValue Value r2 p2 v2 show ?thesis by simp
              next
                case (Memory x3)
                with assms n Pair KValue Value r2 p2 v2 show ?thesis by simp
              next
                case (Storage x4)
                with assms n Pair KValue Value r2 p2 v2 show ?thesis by simp
              qed
            next
              case (KCDptr x2)
              with assms n Pair KValue Value r2 p2 show ?thesis by simp
            next
              case (KMemptr x3)
              with assms n Pair KValue Value r2 p2 show ?thesis by simp
            next
              case (KStoptr x4)
              with assms n Pair KValue Value r2 p2 show ?thesis by simp
            qed
          qed
        next
          case (e x)
          with assms n Pair KValue Value show ?thesis by simp
        qed
      next
        case (Calldata x2)
        with assms n Pair KValue show ?thesis by simp
      next
        case (Memory x3)
        with assms n Pair KValue show ?thesis by simp
      next
        case (Storage x4)
        with assms n Pair KValue show ?thesis by simp
      qed
    next
      case (KCDptr x2)
      with assms n Pair show ?thesis by simp
    next
      case (KMemptr x3)
      with assms n Pair show ?thesis by simp
    next
      case (KStoptr x4)
      with assms n Pair show ?thesis by simp
    qed
  qed
next
  case (e x)
  with assms show ?thesis by simp
qed
 
lemma msel_ssel_lexp_expr_load_rexp_stmt_dom_gas:
    "msel_ssel_lexp_expr_load_rexp_stmt_dom (Inl (Inl (c1, t1, l1, xe1, ep1, ev1, cd1, st1)))
      \<Longrightarrow> (\<forall>l1' t1' st1'. msel c1 t1 l1 xe1 ep1 ev1 cd1 st1 = Normal ((l1', t1'), st1') \<longrightarrow> gas st1' \<le> gas st1)"
    "msel_ssel_lexp_expr_load_rexp_stmt_dom (Inl (Inr (Inl (t2, l2, xe2, ep2, ev2, cd2, st2))))
      \<Longrightarrow> (\<forall>l2' t2' st2'. ssel t2 l2 xe2 ep2 ev2 cd2 st2 = Normal ((l2', t2'), st2') \<longrightarrow> gas st2' \<le> gas st2)"
    "msel_ssel_lexp_expr_load_rexp_stmt_dom (Inl (Inr (Inr (l5, ep5, ev5, cd5, st5))))
      \<Longrightarrow> (\<forall>l5' t5' st5'. lexp l5 ep5 ev5 cd5 st5 = Normal ((l5', t5'), st5') \<longrightarrow> gas st5' \<le> gas st5)"
    "msel_ssel_lexp_expr_load_rexp_stmt_dom (Inr (Inl (Inl (e4, ep4, ev4, cd4, st4))))
      \<Longrightarrow> (\<forall>st4' v4 t4. expr e4 ep4 ev4 cd4 st4 = Normal ((v4, t4), st4') \<longrightarrow> gas st4' \<le> gas st4)"
    "msel_ssel_lexp_expr_load_rexp_stmt_dom (Inr (Inl (Inr (lcp, lis, lxs, lep, lev0, lcd0, lst0, lev, lcd, lst))))
      \<Longrightarrow> (\<forall>ev cd st st'. load lcp lis lxs lep lev0 lcd0 lst0 lev lcd lst = Normal ((ev, cd, st), st') \<longrightarrow> gas st \<le> gas lst0 \<and> gas st' \<le> gas lst \<and> address ev = address lev0)"
    "msel_ssel_lexp_expr_load_rexp_stmt_dom (Inr (Inr (Inl (l3, ep3, ev3, cd3, st3))))
      \<Longrightarrow> (\<forall>l3' t3' st3'. rexp l3 ep3 ev3 cd3 st3 = Normal ((l3', t3'), st3') \<longrightarrow> gas st3' \<le> gas st3)"
    "msel_ssel_lexp_expr_load_rexp_stmt_dom (Inr (Inr (Inr (s6, ep6, ev6, cd6, st6))))
      \<Longrightarrow> (\<forall>st6'. stmt s6 ep6 ev6 cd6 st6 = Normal((), st6') \<longrightarrow> gas st6' \<le> gas st6)"
proof (induct rule: msel_ssel_lexp_expr_load_rexp_stmt.pinduct
[where ?P1.0="\<lambda>c1 t1 l1 xe1 ep1 ev1 cd1 st1. (\<forall>l1' t1' st1'. msel c1 t1 l1 xe1 ep1 ev1 cd1 st1 = Normal ((l1', t1'), st1') \<longrightarrow> gas st1' \<le> gas st1)"
   and ?P2.0="\<lambda>t2 l2 xe2 ep2 ev2 cd2 st2. (\<forall>l2' t2' st2'. ssel t2 l2 xe2 ep2 ev2 cd2 st2 = Normal ((l2', t2'), st2') \<longrightarrow> gas st2' \<le> gas st2)"
   and ?P3.0="\<lambda>l5 ep5 ev5 cd5 st5. (\<forall>l5' t5' st5'. lexp l5 ep5 ev5 cd5 st5 = Normal ((l5', t5'), st5') \<longrightarrow> gas st5' \<le> gas st5)"
   and ?P4.0="\<lambda>e4 ep4 ev4 cd4 st4. (\<forall>st4' v4 t4. expr e4 ep4 ev4 cd4 st4 = Normal ((v4, t4), st4') \<longrightarrow> gas st4' \<le> gas st4)"
   and ?P5.0="\<lambda>lcp lis lxs lep lev0 lcd0 lst0 lev lcd lst. (\<forall>ev cd st st'. load lcp lis lxs lep lev0 lcd0 lst0 lev lcd lst = Normal ((ev, cd, st), st') \<longrightarrow> gas st \<le> gas lst0 \<and> gas st' \<le> gas lst \<and> address ev = address lev0)"
   and ?P6.0="\<lambda>l3 ep3 ev3 cd3 st3. (\<forall>l3' t3' st3'. rexp l3 ep3 ev3 cd3 st3 = Normal ((l3', t3'), st3') \<longrightarrow> gas st3' \<le> gas st3)"
   and ?P7.0="\<lambda>s6 ep6 ev6 cd6 st6. (\<forall>st6'. stmt s6 ep6 ev6 cd6 st6 = Normal ((), st6') \<longrightarrow> gas st6' \<le> gas st6)"
])
  case (1 uu uv uw ux uy uz va)
  then show ?case using msel.psimps(1) by auto
next
  case (2 vb vc vd ve vf vg vh vi)
  then show ?case using msel.psimps(2) by auto
next                                                                                                                                                                         
  case (3 vj al t loc x e\<^sub>p env cd st)
  then show ?case using msel.psimps(3) by (auto split: if_split_asm Type.split_asm Stackvalue.split_asm prod.split_asm StateMonad.result.split_asm)
next
  case (4 mm al t loc x y ys e\<^sub>p env cd st)
  show ?case
  proof (rule allI[THEN allI, THEN allI, OF impI])
    fix l1' t1' st1' assume a1: "msel mm (MTArray al t) loc (x # y # ys) e\<^sub>p env cd st = Normal ((l1', t1'), st1')"
    show "gas st1' \<le> gas st"
    proof (cases "expr x e\<^sub>p env cd st")
      case (n a st')
      then show ?thesis
      proof (cases a)
        case (Pair b c)
        then show ?thesis
        proof (cases b)
          case (KValue v)
          then show ?thesis
          proof (cases c)
            case (Value t')
            then show ?thesis
            proof (cases)
              assume l: "less t' (TUInt 256) v (ShowL\<^sub>i\<^sub>n\<^sub>t al) = Some (ShowL\<^sub>b\<^sub>o\<^sub>o\<^sub>l True, TBool)"
              then show ?thesis
              proof (cases "accessStore (hash loc v) (if mm then memory st' else cd)")
                case None
                with 4 a1 n Pair KValue Value l show ?thesis using msel.psimps(4) by simp
              next
                case (Some a)
                then show ?thesis
                proof (cases a)
                  case (MValue x1)
                  with 4 a1 n Pair KValue Value Some l show ?thesis using msel.psimps(4) by simp
                next
                  case (MPointer l)
                  with n Pair KValue Value l Some
                  have "msel mm (MTArray al t) loc (x # y # ys) e\<^sub>p env cd st = msel mm t l (y # ys) e\<^sub>p env cd st'"
                    using msel.psimps(4) 4(1) by simp
                  moreover from n Pair have "gas st' \<le> gas st" using 4(2) by simp
                  moreover from a1 MPointer n Pair KValue Value l Some
                  have "gas st1' \<le> gas st'" using msel.psimps(4) 4(3) 4(1) by simp
                  ultimately show ?thesis by simp
                qed
              qed
            next
              assume "\<not> less t' (TUInt 256) v (ShowL\<^sub>i\<^sub>n\<^sub>t al) = Some (ShowL\<^sub>b\<^sub>o\<^sub>o\<^sub>l True, TBool)"
              with 4 a1 n Pair KValue Value show ?thesis using msel.psimps(4) by simp
            qed
          next
            case (Calldata x2)
            with 4 a1 n Pair KValue show ?thesis using msel.psimps(4) by simp
          next
            case (Memory x3)
            with 4 a1 n Pair KValue show ?thesis using msel.psimps(4) by simp
          next
            case (Storage x4)
            with 4 a1 n Pair KValue show ?thesis using msel.psimps(4) by simp
          qed
        next
          case (KCDptr x2)
          with 4 a1 n Pair show ?thesis using msel.psimps(4) by simp
        next
          case (KMemptr x3)
          with 4 a1 n Pair show ?thesis using msel.psimps(4) by simp
        next
          case (KStoptr x4)
          with 4 a1 n Pair show ?thesis using msel.psimps(4) by simp
        qed
      qed
    next
      case (e x)
      with 4 a1 show ?thesis using msel.psimps(4) by simp
    qed
  qed
next
  case (5 tp loc vk vl vm st)
  then show ?case using ssel.psimps(1) by auto
next
  case (6 vn vo vp vq vr vs vt vu)
  then show ?case using ssel.psimps(2) by auto
next
  case (7 al t loc x xs e\<^sub>p env cd st)
  show ?case
  proof (rule allI[THEN allI, THEN allI, OF impI])
    fix l2' t2' st2' assume a1: "ssel (STArray al t) loc (x # xs) e\<^sub>p env cd st = Normal ((l2', t2'), st2')"
    show "gas st2' \<le> gas st"
    proof (cases "expr x e\<^sub>p env cd st")
      case (n a st'')
      then show ?thesis
      proof (cases a)
        case (Pair b c)
        then show ?thesis
        proof (cases b)
          case (KValue v)
          then show ?thesis
          proof (cases c)
            case (Value t')
            then show ?thesis
            proof (cases)
              assume l: "less t' (TUInt 256) v (ShowL\<^sub>i\<^sub>n\<^sub>t al) = Some (ShowL\<^sub>b\<^sub>o\<^sub>o\<^sub>l True, TBool)"
              with n Pair KValue Value l
              have "ssel (STArray al t) loc (x # xs) e\<^sub>p env cd st = ssel t (hash loc v) xs e\<^sub>p env cd st''"
              using ssel.psimps(3) 7(1) by simp
              moreover from n Pair have "gas st'' \<le> gas st" using 7(2) by simp
              moreover from a1 n Pair KValue Value l
              have "gas st2' \<le> gas st''" using ssel.psimps(3) 7(3) 7(1) by simp
              ultimately show ?thesis by simp
            next
              assume "\<not> less t' (TUInt 256) v (ShowL\<^sub>i\<^sub>n\<^sub>t al) = Some (ShowL\<^sub>b\<^sub>o\<^sub>o\<^sub>l True, TBool)"
              with 7 a1 n Pair KValue Value show ?thesis using ssel.psimps(3) by simp
            qed
          next
            case (Calldata x2)
            with 7 a1 n Pair KValue show ?thesis using ssel.psimps(3) by simp
          next
            case (Memory x3)
            with 7 a1 n Pair KValue show ?thesis using ssel.psimps(3) by simp
          next
            case (Storage x4)
            with 7 a1 n Pair KValue show ?thesis using ssel.psimps(3) by simp
          qed
        next
          case (KCDptr x2)
          with 7 a1 n Pair show ?thesis using ssel.psimps(3) by simp
        next
          case (KMemptr x3)
          with 7 a1 n Pair show ?thesis using ssel.psimps(3) by simp
        next
          case (KStoptr x4)
          with 7 a1 n Pair show ?thesis using ssel.psimps(3) by simp
        qed
      qed
    next
      case (e e)
      with 7 a1 show ?thesis using ssel.psimps(3) by simp
    qed
  qed
next
  case (8 vv t loc x xs e\<^sub>p env cd st)
  show ?case
  proof (rule allI[THEN allI, THEN allI, OF impI])
    fix l2' t2' st2' assume a1: "ssel (STMap vv t) loc (x # xs) e\<^sub>p env cd st = Normal ((l2', t2'), st2')"
    show "gas st2' \<le> gas st"
    proof (cases "expr x e\<^sub>p env cd st")
      case (n a st')
      then show ?thesis
      proof (cases a)
        case (Pair b c)
        then show ?thesis
        proof (cases b)
          case (KValue v)
          with 8 n Pair have "ssel (STMap vv t) loc (x # xs) e\<^sub>p env cd st = ssel t (hash loc v) xs e\<^sub>p env cd st'" using ssel.psimps(4) by simp
          moreover from n Pair have "gas st' \<le> gas st" using 8(2) by simp
          moreover from a1 n Pair KValue
          have "gas st2' \<le> gas st'" using ssel.psimps(4) 8(3) 8(1) by simp
          ultimately show ?thesis by simp
        next
          case (KCDptr x2)
          with 8 a1 n Pair show ?thesis using ssel.psimps(4) by simp
        next
          case (KMemptr x3)
          with 8 a1 n Pair show ?thesis using ssel.psimps(4) by simp
        next
          case (KStoptr x4)
          with 8 a1 n Pair show ?thesis using ssel.psimps(4) by simp
        qed
      qed
    next
      case (e x)
      with 8 a1 show ?thesis using ssel.psimps(4) by simp
    qed
  qed
next
  case (9 i vw e vx st)
  then show ?case using lexp.psimps(1)[of i vw e vx st] by (simp split: option.split_asm Denvalue.split_asm prod.split_asm)
next
  case (10 i r e\<^sub>p e cd st)
  show ?case
  proof (rule allI[THEN allI, THEN allI, OF impI])
    fix st5' xa xaa
    assume a1: "lexp (Ref i r) e\<^sub>p e cd st = Normal ((st5', xa), xaa)"
    then show "gas xaa \<le> gas st"
    proof (cases "fmlookup (denvalue e) i")
      case None
      with 10 a1 show ?thesis using lexp.psimps(2) by simp
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
            with 10 a1 Some Pair Stackloc show ?thesis using lexp.psimps(2) by simp
          next
            case s2: (Some a)
            then show ?thesis
            proof (cases a)
              case (KValue x1)
              with 10 a1 Some Pair Stackloc s2 show ?thesis using lexp.psimps(2) by simp
            next
              case (KCDptr x2)
              with 10 a1 Some Pair Stackloc s2 show ?thesis using lexp.psimps(2) by simp
            next
              case (KMemptr l')
              then show ?thesis
              proof (cases tp)
                case (Value x1)
                with 10 a1 Some Pair Stackloc s2 KMemptr show ?thesis using lexp.psimps(2) by simp
              next
                case (Calldata x2)
                with 10 a1 Some Pair Stackloc s2 KMemptr show ?thesis using lexp.psimps(2) by simp
              next
                case (Memory t)
                then show ?thesis
                proof (cases "msel True t l' r e\<^sub>p e cd st")
                  case (n a s)
                  with 10 a1 Some Pair Stackloc s2 KMemptr Memory show ?thesis using lexp.psimps(2) by (simp split: prod.split_asm)
                next
                  case (e e)
                  with 10 a1 Some Pair Stackloc s2 KMemptr Memory show ?thesis using lexp.psimps(2) by simp
                qed
              next
                case (Storage x4)
                with 10 a1 Some Pair Stackloc s2 KMemptr show ?thesis using lexp.psimps(2) by simp
              qed
            next
              case (KStoptr l')
              then show ?thesis
              proof (cases tp)
                case (Value x1)
                with 10 a1 Some Pair Stackloc s2 KStoptr show ?thesis using lexp.psimps(2) by simp
              next
                case (Calldata x2)
                with 10 a1 Some Pair Stackloc s2 KStoptr show ?thesis using lexp.psimps(2) by simp
              next
                case (Memory t)
                with 10 a1 Some Pair Stackloc s2 KStoptr show ?thesis using lexp.psimps(2) by simp
              next
                case (Storage t)
                then show ?thesis
                proof (cases "ssel t l' r e\<^sub>p e cd st")
                  case (n a s)
                  with 10 a1 Some Pair Stackloc s2 KStoptr Storage show ?thesis using lexp.psimps(2) by (auto split: prod.split_asm)
                next
                  case (e x)
                  with 10 a1 Some Pair Stackloc s2 KStoptr Storage show ?thesis using lexp.psimps(2) by simp
                qed
              qed
            qed
          qed
        next
          case (Storeloc l)
          then show ?thesis
          proof (cases tp)
            case (Value x1)
            with 10 a1 Some Pair Storeloc show ?thesis using lexp.psimps(2) by simp
          next
            case (Calldata x2)
            with 10 a1 Some Pair Storeloc show ?thesis using lexp.psimps(2) by simp
          next
            case (Memory t)
            with 10 a1 Some Pair Storeloc show ?thesis using lexp.psimps(2) by simp
          next
            case (Storage t)
            then show ?thesis
            proof (cases "ssel t l r e\<^sub>p e cd st")
              case (n a s)
              with 10 a1 Some Pair Storeloc Storage show ?thesis using lexp.psimps(2) by (auto split: prod.split_asm)
            next
              case (e x)
              with 10 a1 Some Pair Storeloc Storage show ?thesis using lexp.psimps(2) by simp
            qed
          qed
        qed
      qed
    qed
  qed
next
  case (11 b x e\<^sub>p e vy st)
  then show ?case using expr.psimps(1) by (simp split:if_split_asm)
next
  case (12 b x e\<^sub>p e vz st)
  then show ?case using expr.psimps(2) by (simp split:if_split_asm)
next
  case (13 ad e\<^sub>p e wa st)
  then show ?case using expr.psimps(3) by simp
next
  case (14 ad e\<^sub>p e wb st)
  define g where "g = costs\<^sub>e (BALANCE ad) e\<^sub>p e wb st"
  show ?case
  proof (rule allI[THEN allI, THEN allI, OF impI])
    fix t4 xa xaa
    assume *: "expr (BALANCE ad) e\<^sub>p e wb st = Normal ((xa, xaa), t4)"
    show "gas t4 \<le> gas st"
    proof (cases)
      assume "gas st \<le> g"
      with 14 g_def * show ?thesis using expr.psimps(4) by simp
    next
      assume gcost: "\<not> gas st \<le> g"
      then show ?thesis
      proof (cases "expr ad e\<^sub>p e wb (st\<lparr>gas := gas st - g\<rparr>)")
        case (n a s)
        show ?thesis
        proof (cases a)
          case (Pair b c)
          then show ?thesis
          proof (cases b)
            case (KValue x1)
            then show ?thesis
            proof (cases c)
              case (Value x1)
              then show ?thesis
              proof (cases x1)
                case (TSInt x1)
                with 14 g_def * gcost n Pair KValue Value show ?thesis using expr.psimps(4)[of ad e\<^sub>p e wb st] by simp
              next
                case (TUInt x2)
                with 14 g_def * gcost n Pair KValue Value show ?thesis using expr.psimps(4)[of ad e\<^sub>p e wb st] by simp
              next
                case TBool
                with 14 g_def * gcost n Pair KValue Value show ?thesis using expr.psimps(4)[of ad e\<^sub>p e wb st] by simp
              next
                case TAddr
                with 14 g_def * gcost n Pair KValue Value show "gas t4 \<le> gas st" using expr.psimps(4)[of ad e\<^sub>p e wb st] by simp
              qed
            next
              case (Calldata x2)
              with 14 g_def * gcost n Pair KValue show ?thesis using expr.psimps(4)[of ad e\<^sub>p e wb st] by simp
            next
              case (Memory x3)
              with 14 g_def * gcost n Pair KValue show ?thesis using expr.psimps(4)[of ad e\<^sub>p e wb st] by simp
            next
              case (Storage x4)
              with 14 g_def * gcost n Pair KValue show ?thesis using expr.psimps(4)[of ad e\<^sub>p e wb st] by simp
            qed
          next
            case (KCDptr x2)
            with 14 g_def * gcost n Pair show ?thesis using expr.psimps(4)[of ad e\<^sub>p e wb st] by simp
          next
            case (KMemptr x3)
            with 14 g_def * gcost n Pair show ?thesis using expr.psimps(4)[of ad e\<^sub>p e wb st] by simp
          next
            case (KStoptr x4)
            with 14 g_def * gcost n Pair show ?thesis using expr.psimps(4)[of ad e\<^sub>p e wb st] by simp
          qed
        qed
      next
        case (e _)
        with 14 g_def * gcost show ?thesis using expr.psimps(4)[of ad e\<^sub>p e wb st] by simp
      qed
    qed
  qed
next
  case (15 e\<^sub>p e wc st)
  then show ?case using expr.psimps(5) by simp
next
  case (16 e\<^sub>p e wd st)
  then show ?case using expr.psimps(6) by simp
next
  case (17 e\<^sub>p e wd st)
  then show ?case using expr.psimps(7) by simp
next
  case (18 e\<^sub>p e wd st)
  then show ?case using expr.psimps(8) by simp
next
  case (19 e\<^sub>p e wd st)
  then show ?case using expr.psimps(9) by simp
next
  case (20 x e\<^sub>p e cd st)
  define g where "g = costs\<^sub>e (NOT x) e\<^sub>p e cd st"
  show ?case
  proof (rule allI[THEN allI, THEN allI, OF impI])
    fix st4' v4 t4 assume a1: "expr (NOT x) e\<^sub>p e cd st = Normal ((v4, t4), st4')"
    show "gas st4' \<le> gas st"
    proof (cases)
      assume "gas st \<le> g"
      with 20 g_def a1 show ?thesis using expr.psimps by simp
    next
      assume gcost: "\<not> gas st \<le> g"
      then show ?thesis
      proof (cases "expr x e\<^sub>p e cd (st\<lparr>gas := gas st - g\<rparr>)")
        case (n a st')
        then show ?thesis
        proof (cases a)
          case (Pair b c)
          then show ?thesis
          proof (cases b)
            case (KValue v)
            then show ?thesis
            proof (cases c)
              case (Value t)
              then show ?thesis
              proof (cases)
                assume v_def: "v = ShowL\<^sub>b\<^sub>o\<^sub>o\<^sub>l True"
                with 20(1) g_def gcost n Pair KValue Value have "expr (NOT x) e\<^sub>p e cd st = expr FALSE e\<^sub>p e cd st'" using expr.psimps(10) by simp
                moreover from 20(2) g_def gcost n Pair have "gas st' \<le> gas st" by simp
                moreover from 20(1) 20(3) a1 g_def gcost n Pair KValue Value v_def have "gas st4' \<le> gas st'" using expr.psimps(10) by simp
                ultimately show ?thesis by arith
               next
                assume v_def: "\<not> v = ShowL\<^sub>b\<^sub>o\<^sub>o\<^sub>l True"
                then show ?thesis
                proof (cases)
                  assume v_def2: "v = ShowL\<^sub>b\<^sub>o\<^sub>o\<^sub>l False"
                  with 20(1) g_def gcost n Pair KValue Value v_def have "expr (NOT x) e\<^sub>p e cd st = expr TRUE e\<^sub>p e cd st'" using expr.psimps(10) by simp
                  moreover from 20(2) g_def gcost n Pair have "gas st' \<le> gas st" by simp
                  moreover from 20 a1 g_def gcost n Pair KValue Value v_def v_def2 have "gas st4' \<le> gas st'" using expr.psimps(10) by simp
                  ultimately show ?thesis by arith
                next
                  assume "\<not> v = ShowL\<^sub>b\<^sub>o\<^sub>o\<^sub>l False"
                  with 20 a1 g_def gcost n Pair KValue Value v_def show ?thesis using expr.psimps(10) by simp
                qed
              qed
            next
              case (Calldata x2)
              with 20 a1 g_def gcost n Pair KValue show ?thesis using expr.psimps(10) by simp
            next
              case (Memory x3)
              with 20 a1 g_def gcost n Pair KValue show ?thesis using expr.psimps(10) by simp
            next
              case (Storage x4)
              with 20 a1 g_def gcost n Pair KValue show ?thesis using expr.psimps(10) by simp
            qed
          next
            case (KCDptr x2)
            with 20 a1 g_def gcost n Pair show ?thesis using expr.psimps(10) by simp
          next
            case (KMemptr x3)
            with 20 a1 g_def gcost n Pair show ?thesis using expr.psimps(10) by simp
          next
            case (KStoptr x4)
            with 20 a1 g_def gcost n Pair show ?thesis using expr.psimps(10) by simp
          qed
        qed
      next
        case (e e)
        with 20 a1 g_def gcost show ?thesis using expr.psimps(10) by simp
      qed
    qed
  qed
next
  case (21 e1 e2 e\<^sub>p e cd st)
  define g where "g = costs\<^sub>e (PLUS e1 e2) e\<^sub>p e cd st"
  show ?case
  proof (rule allI[THEN allI, THEN allI, OF impI])
    fix t4 xa xaa assume e_def: "expr (PLUS e1 e2) e\<^sub>p e cd st = Normal ((xa, xaa), t4)"
    then show "gas t4 \<le> gas st"
    proof (cases)
      assume "gas st \<le> g"
      with 21(1) e_def show ?thesis using expr.psimps(11) g_def by simp
    next
      assume "\<not> gas st \<le> g"
      with 21(1) e_def g_def have "lift expr add e1 e2 e\<^sub>p e cd (st\<lparr>gas := gas st - g\<rparr>) = Normal ((xa, xaa), t4)" using expr.psimps(11)[of e1 e2 e\<^sub>p e cd st] by simp
      moreover from 21(2) `\<not> gas st \<le> g` g_def have "(\<And>st4' v4 t4. expr e1 e\<^sub>p e cd (st\<lparr>gas := gas st - g\<rparr>) = Normal ((v4, t4), st4') \<Longrightarrow> gas st4' \<le> gas (st\<lparr>gas := gas st - g\<rparr>))" by simp
      moreover from 21(3) `\<not> gas st \<le> g` g_def have "(\<And>x1 x y xa ya x1a x1b st4' v4 t4.
          expr e1 e\<^sub>p e cd (st\<lparr>gas := gas st - g\<rparr>) = Normal (x, y) \<Longrightarrow>
          (xa, ya) = x \<Longrightarrow>
          xa = KValue x1a \<Longrightarrow>
          ya = Value x1b \<Longrightarrow> expr e2 e\<^sub>p e cd y = Normal ((v4, t4), st4') \<Longrightarrow> gas st4' \<le> gas y)" by auto
      ultimately show "gas t4 \<le> gas st" using lift_gas[of e1 e\<^sub>p e cd e2 "add" "st\<lparr>gas := gas st - g\<rparr>" xa xaa t4] by simp
    qed
  qed
next
  case (22 e1 e2 e\<^sub>p e cd st)
  define g where "g = costs\<^sub>e (MINUS e1 e2) e\<^sub>p e cd st"
  show ?case
  proof (rule allI[THEN allI, THEN allI, OF impI])
    fix t4 xa xaa assume e_def: "expr (MINUS e1 e2) e\<^sub>p e cd st = Normal ((xa, xaa), t4)"
    then show "gas t4 \<le> gas st"
    proof (cases)
      assume "gas st \<le> g"
      with 22(1) e_def show ?thesis using expr.psimps(12) g_def by simp
    next
      assume "\<not> gas st \<le> g"
      with 22(1) e_def g_def have "lift expr sub e1 e2 e\<^sub>p e cd (st\<lparr>gas := gas st - g\<rparr>) = Normal ((xa, xaa), t4)" using expr.psimps(12)[of e1 e2 e\<^sub>p e cd st] by simp
      moreover from 22(2) `\<not> gas st \<le> g` g_def have "(\<And>st4' v4 t4. expr e1 e\<^sub>p e cd (st\<lparr>gas := gas st - g\<rparr>) = Normal ((v4, t4), st4') \<Longrightarrow> gas st4' \<le> gas (st\<lparr>gas := gas st - g\<rparr>))" by simp
      moreover from 22(3) `\<not> gas st \<le> g` g_def have "(\<And>x1 x y xa ya x1a x1b st4' v4 t4.
          expr e1 e\<^sub>p e cd (st\<lparr>gas := gas st - g\<rparr>) = Normal (x, y) \<Longrightarrow>
          (xa, ya) = x \<Longrightarrow>
          xa = KValue x1a \<Longrightarrow>
          ya = Value x1b \<Longrightarrow> expr e2 e\<^sub>p e cd y = Normal ((v4, t4), st4') \<Longrightarrow> gas st4' \<le> gas y)" by auto
      ultimately show "gas t4 \<le> gas st" using lift_gas[of e1 e\<^sub>p e cd e2 "sub" "st\<lparr>gas := gas st - g\<rparr>" xa xaa t4] by simp
    qed
  qed
next
  case (23 e1 e2 e\<^sub>p e cd st)
  define g where "g = costs\<^sub>e (LESS e1 e2) e\<^sub>p e cd st"
  show ?case
  proof (rule allI[THEN allI, THEN allI, OF impI])
    fix t4 xa xaa assume e_def: "expr (LESS e1 e2) e\<^sub>p e cd st = Normal ((xa, xaa), t4)"
    then show "gas t4 \<le> gas st"
    proof (cases)
      assume "gas st \<le> g"
      with 23(1) e_def show ?thesis using expr.psimps(13) g_def by simp
    next
      assume "\<not> gas st \<le> g"
      with 23(1) e_def g_def have "lift expr less e1 e2 e\<^sub>p e cd (st\<lparr>gas := gas st - g\<rparr>) = Normal ((xa, xaa), t4)" using expr.psimps(13)[of e1 e2 e\<^sub>p e cd st] by simp
      moreover from 23(2) `\<not> gas st \<le> g` g_def have "(\<And>st4' v4 t4. expr e1 e\<^sub>p e cd (st\<lparr>gas := gas st - g\<rparr>) = Normal ((v4, t4), st4') \<Longrightarrow> gas st4' \<le> gas (st\<lparr>gas := gas st - g\<rparr>))" by simp
      moreover from 23(3) `\<not> gas st \<le> g` g_def have "(\<And>x1 x y xa ya x1a x1b st4' v4 t4.
          expr e1 e\<^sub>p e cd (st\<lparr>gas := gas st - g\<rparr>) = Normal (x, y) \<Longrightarrow>
          (xa, ya) = x \<Longrightarrow>
          xa = KValue x1a \<Longrightarrow>
          ya = Value x1b \<Longrightarrow> expr e2 e\<^sub>p e cd y = Normal ((v4, t4), st4') \<Longrightarrow> gas st4' \<le> gas y)" by auto
      ultimately show "gas t4 \<le> gas st" using lift_gas[of e1 e\<^sub>p e cd e2 "less" "st\<lparr>gas := gas st - g\<rparr>" xa xaa t4] by simp
    qed
  qed
next
  case (24 e1 e2 e\<^sub>p e cd st)
  define g where "g = costs\<^sub>e (EQUAL e1 e2) e\<^sub>p e cd st"
  show ?case
  proof (rule allI[THEN allI, THEN allI, OF impI])
    fix t4 xa xaa assume e_def: "expr (EQUAL e1 e2) e\<^sub>p e cd st = Normal ((xa, xaa), t4)"
    then show "gas t4 \<le> gas st"
    proof (cases)
      assume "gas st \<le> g"
      with 24(1) e_def show ?thesis using expr.psimps(14) g_def by simp
    next
      assume "\<not> gas st \<le> g"
      with 24(1) e_def g_def have "lift expr equal e1 e2 e\<^sub>p e cd (st\<lparr>gas := gas st - g\<rparr>) = Normal ((xa, xaa), t4)" using expr.psimps(14)[of e1 e2 e\<^sub>p e cd st] by simp
      moreover from 24(2) `\<not> gas st \<le> g` g_def have "(\<And>st4' v4 t4. expr e1 e\<^sub>p e cd (st\<lparr>gas := gas st - g\<rparr>) = Normal ((v4, t4), st4') \<Longrightarrow> gas st4' \<le> gas (st\<lparr>gas := gas st - g\<rparr>))" by simp
      moreover from 24(3) `\<not> gas st \<le> g` g_def have "(\<And>x1 x y xa ya x1a x1b st4' v4 t4.
          expr e1 e\<^sub>p e cd (st\<lparr>gas := gas st - g\<rparr>) = Normal (x, y) \<Longrightarrow>
          (xa, ya) = x \<Longrightarrow>
          xa = KValue x1a \<Longrightarrow>
          ya = Value x1b \<Longrightarrow> expr e2 e\<^sub>p e cd y = Normal ((v4, t4), st4') \<Longrightarrow> gas st4' \<le> gas y)" by auto
      ultimately show "gas t4 \<le> gas st" using lift_gas[of e1 e\<^sub>p e cd e2 "equal" "st\<lparr>gas := gas st - g\<rparr>" xa xaa t4] by simp
    qed
  qed
next
  case (25 e1 e2 e\<^sub>p e cd st)
  define g where "g = costs\<^sub>e (AND e1 e2) e\<^sub>p e cd st"
  show ?case
  proof (rule allI[THEN allI, THEN allI, OF impI])
    fix t4 xa xaa assume e_def: "expr (AND e1 e2) e\<^sub>p e cd st = Normal ((xa, xaa), t4)"
    then show "gas t4 \<le> gas st"
    proof (cases)
      assume "gas st \<le> g"
      with 25(1) e_def show ?thesis using expr.psimps(15) g_def by simp
    next
      assume "\<not> gas st \<le> g"
      with 25(1) e_def g_def have "lift expr vtand e1 e2 e\<^sub>p e cd (st\<lparr>gas := gas st - g\<rparr>) = Normal ((xa, xaa), t4)" using expr.psimps(15)[of e1 e2 e\<^sub>p e cd st] by simp
      moreover from 25(2) `\<not> gas st \<le> g` g_def have "(\<And>st4' v4 t4. expr e1 e\<^sub>p e cd (st\<lparr>gas := gas st - g\<rparr>) = Normal ((v4, t4), st4') \<Longrightarrow> gas st4' \<le> gas (st\<lparr>gas := gas st - g\<rparr>))" by simp
      moreover from 25(3) `\<not> gas st \<le> g` g_def have "(\<And>x1 x y xa ya x1a x1b st4' v4 t4.
          expr e1 e\<^sub>p e cd (st\<lparr>gas := gas st - g\<rparr>) = Normal (x, y) \<Longrightarrow>
          (xa, ya) = x \<Longrightarrow>
          xa = KValue x1a \<Longrightarrow>
          ya = Value x1b \<Longrightarrow> expr e2 e\<^sub>p e cd y = Normal ((v4, t4), st4') \<Longrightarrow> gas st4' \<le> gas y)" by auto
      ultimately show "gas t4 \<le> gas st" using lift_gas[of e1 e\<^sub>p e cd e2 "vtand" "st\<lparr>gas := gas st - g\<rparr>" xa xaa t4] by simp
    qed
  qed
next
  case (26 e1 e2 e\<^sub>p e cd st)
  define g where "g = costs\<^sub>e (OR e1 e2) e\<^sub>p e cd st"
  show ?case
  proof (rule allI[THEN allI, THEN allI, OF impI])
    fix t4 xa xaa assume e_def: "expr (OR e1 e2) e\<^sub>p e cd st = Normal ((xa, xaa), t4)"
    then show "gas t4 \<le> gas st"
    proof (cases)
      assume "gas st \<le> g"
      with 26(1) e_def show ?thesis using expr.psimps(16) g_def by simp
    next
      assume "\<not> gas st \<le> g"
      with 26(1) e_def g_def have "lift expr vtor e1 e2 e\<^sub>p e cd (st\<lparr>gas := gas st - g\<rparr>) = Normal ((xa, xaa), t4)" using expr.psimps(16)[of e1 e2 e\<^sub>p e cd st] by simp
      moreover from 26(2) `\<not> gas st \<le> g` g_def have "(\<And>st4' v4 t4. expr e1 e\<^sub>p e cd (st\<lparr>gas := gas st - g\<rparr>) = Normal ((v4, t4), st4') \<Longrightarrow> gas st4' \<le> gas (st\<lparr>gas := gas st - g\<rparr>))" by simp
      moreover from 26(3) `\<not> gas st \<le> g` g_def have "(\<And>x1 x y xa ya x1a x1b st4' v4 t4.
          expr e1 e\<^sub>p e cd (st\<lparr>gas := gas st - g\<rparr>) = Normal (x, y) \<Longrightarrow>
          (xa, ya) = x \<Longrightarrow>
          xa = KValue x1a \<Longrightarrow>
          ya = Value x1b \<Longrightarrow> expr e2 e\<^sub>p e cd y = Normal ((v4, t4), st4') \<Longrightarrow> gas st4' \<le> gas y)" by auto
      ultimately show "gas t4 \<le> gas st" using lift_gas[of e1 e\<^sub>p e cd e2 "vtor" "st\<lparr>gas := gas st - g\<rparr>" xa xaa t4] by simp
    qed
  qed
next
  case (27 i e\<^sub>p e cd st)
  then show ?case using expr.psimps(17) by (auto split: prod.split_asm option.split_asm StateMonad.result.split_asm)
next
  case (28 i xe e\<^sub>p e cd st)
  define g where "g = costs\<^sub>e (CALL i xe) e\<^sub>p e cd st"
  show ?case
  proof (rule allI[THEN allI, THEN allI, OF impI])
    fix st4' v4 t4 assume a1: "expr (CALL i xe) e\<^sub>p e cd st = Normal ((v4, t4), st4')"
    show "gas st4' \<le> gas st"
    proof (cases)
      assume "gas st \<le> g"
      with 28 g_def a1 show ?thesis using expr.psimps by simp
    next
      assume gcost: "\<not> gas st \<le> g"
      then show ?thesis
      proof (cases "fmlookup e\<^sub>p (address e)")
        case None
        with 28(1) a1 g_def gcost show ?thesis using expr.psimps(18) by simp
      next
        case (Some a)
        then show ?thesis
        proof (cases a)
          case (Pair ct _)
          then show ?thesis
          proof (cases "fmlookup ct i")
            case None
            with 28(1) a1 g_def gcost Some Pair show ?thesis using expr.psimps(18) by simp
          next
            case s1: (Some a)
            then show ?thesis
            proof (cases a)
              case (Method x1)
              then show ?thesis
              proof (cases x1)
                case (fields fp f c)
                then show ?thesis
                proof (cases c)
                  case None
                  with 28(1) a1 g_def gcost Some Pair s1 Method fields show ?thesis using expr.psimps(18) by simp
                next
                  case s2: (Some x)
                  define st' e'
                    where "st' = st\<lparr>gas := gas st - g\<rparr>\<lparr>stack:=emptyStore\<rparr>"
                      and "e' = ffold (init ct) (emptyEnv (address e) (sender e) (svalue e)) (fmdom ct)"
                  then show ?thesis
                  proof (cases "load False fp xe e\<^sub>p e' emptyStore st' e cd (st\<lparr>gas := gas st - g\<rparr>)")
                    case s4: (n a st''')
                    then show ?thesis
                    proof (cases a)
                      case f2: (fields e'' cd' st'')
                      then show ?thesis
                      proof (cases "stmt f e\<^sub>p e'' cd' st''")
                        case n2: (n a st'''')
                        then show ?thesis
                        proof (cases "expr x e\<^sub>p e'' cd' st''''")
                          case n3: (n a st''''')
                          then show ?thesis
                          proof (cases a)
                            case p1: (Pair sv tp)
                            with 28(1) a1 g_def gcost Some Pair s1 Method fields s2 st'_def e'_def s4 f2 n2 n3
                            have "expr (CALL i xe) e\<^sub>p e cd st = Normal ((sv, tp), st'''''\<lparr>stack:=stack st''', memory := memory st'''\<rparr>)" and *: "gas st' \<le> gas (st\<lparr>gas := gas st - g\<rparr>)"
                                using expr.psimps(18)[of i xe e\<^sub>p e cd st] by (auto simp add: Let_def split: unit.split_asm)
                            with a1 have "gas st4' \<le> gas st'''''" by auto
                            also from 28(4)[of "()" "st\<lparr>gas := gas st - g\<rparr>" _ ct] g_def gcost Some Pair s1 Method fields s2 st'_def e'_def s4 f2 n2 n3
                              have "\<dots> \<le> gas st''''" by auto
                            also from 28(3)[of "()" "st\<lparr>gas := gas st - g\<rparr>" _ ct _ _ x1 fp _ f c x e' st' "st\<lparr>gas := gas st - g\<rparr>" _ st''' e'' _ cd' st'' st''' st''' "()" st''] a1 g_def gcost Some Pair s1 Method fields s2 st'_def e'_def s4 f2 n2
                              have "\<dots> \<le> gas st''" by auto
                            also have "\<dots> \<le> gas st - g"
                            proof -
                              from g_def gcost have "(applyf (costs\<^sub>e (CALL i xe) e\<^sub>p e cd) \<bind> (\<lambda>g. assert Gas (\<lambda>st. gas st \<le> g) (modify (\<lambda>st. st\<lparr>gas := gas st - g\<rparr>)))) st = Normal ((), st\<lparr>gas := gas st - g\<rparr>)" by simp
                              moreover from e'_def have "e' = ffold_init ct (emptyEnv (address e) (sender e) (svalue e)) (fmdom ct)" by simp
                              moreover from st'_def have "applyf (\<lambda>st. st\<lparr>stack := emptyStore\<rparr>) (st\<lparr>gas := gas st - g\<rparr>) =   Normal (st', st\<lparr>gas := gas st - g\<rparr>)" by simp
                              ultimately have "\<forall>ev cda sta st'a. load False fp xe e\<^sub>p e' emptyStore st' e cd (st\<lparr>gas := gas st - g\<rparr>) = Normal ((ev, cda, sta), st'a) \<longrightarrow> gas sta \<le> gas st' \<and> gas st'a \<le> gas (st\<lparr>gas := gas st - g\<rparr>) \<and> address ev = address e'" using 28(2)[of "()" "st\<lparr>gas := gas st - g\<rparr>" _ ct _ _ x1 fp "(f,c)" f c x e' st' "st\<lparr>gas := gas st - g\<rparr>"] using Some Pair s1 Method fields s2 by blast
                              thus ?thesis using st'_def s4 f2 by auto
                            qed
                            finally show ?thesis by simp
                          qed
                        next
                          case (e x)
                          with 28(1) a1 g_def gcost Some Pair s1 Method fields s2 st'_def e'_def s4 f2 n2 show ?thesis using expr.psimps(18)[of i xe e\<^sub>p e cd st] by (auto simp add:Let_def split:unit.split_asm)
                        qed
                      next
                        case (e x)
                        with 28(1) a1 g_def gcost Some Pair s1 Method fields s2 st'_def e'_def s4 f2 show ?thesis using expr.psimps(18)[of i xe e\<^sub>p e cd st] by (auto split:unit.split_asm)
                      qed
                    qed
                  next
                    case (e x)
                    with 28(1) a1 g_def gcost Some Pair s1 Method fields s2 st'_def e'_def show ?thesis using expr.psimps(18)[of i xe e\<^sub>p e cd st] by auto
                  qed
                qed
              qed
            next
              case (Var x2)
              with 28(1) a1 g_def gcost Some Pair s1 show ?thesis using expr.psimps(18) by simp
            qed
          qed
        qed
      qed
    qed
  qed
next
  case (29 ad i xe val e\<^sub>p e cd st)
  define g where "g = costs\<^sub>e (ECALL ad i xe val) e\<^sub>p e cd st"
  show ?case
  proof (rule allI[THEN allI, THEN allI, OF impI])
    fix st4' v4 t4 assume a1: "expr (ECALL ad i xe val) e\<^sub>p e cd st = Normal ((v4, t4), st4')"
    show "gas st4' \<le> gas st"
    proof (cases)
      assume "gas st \<le> g"
      with 29 g_def a1 show ?thesis using expr.psimps by simp
    next
      assume gcost: "\<not> gas st \<le> g"
      then show ?thesis
      proof (cases "expr ad e\<^sub>p e cd (st\<lparr>gas := gas st - g\<rparr>)")
        case (n a st')
        then show ?thesis
        proof (cases a)
          case (Pair a b)
          then show ?thesis
          proof (cases a)
            case (KValue adv)
            then show ?thesis
            proof (cases b)
              case (Value x1)
              then show ?thesis
              proof (cases x1)
                case (TSInt x1)
                with 29(1) a1 g_def gcost n Pair KValue Value show ?thesis using expr.psimps(19)[of ad i xe val e\<^sub>p e cd st] by simp
              next
                case (TUInt x2)
                with 29(1) a1 g_def gcost n Pair KValue Value show ?thesis using expr.psimps(19)[of ad i xe val e\<^sub>p e cd st] by simp
              next
                case TBool
                with 29(1) a1 g_def gcost n Pair KValue Value show ?thesis using expr.psimps(19)[of ad i xe val e\<^sub>p e cd st] by simp
              next
                case TAddr
                then show ?thesis
                proof (cases "fmlookup e\<^sub>p adv")
                  case None
                  with 29(1) a1 g_def gcost n Pair KValue Value TAddr show ?thesis using expr.psimps(19)[of ad i xe val e\<^sub>p e cd st] by simp
                next
                  case (Some a)
                  then show ?thesis
                  proof (cases a)
                    case p2: (Pair ct _)
                    then show ?thesis
                    proof (cases "fmlookup ct i")
                      case None
                      with 29(1) a1 g_def gcost n Pair KValue Value TAddr Some p2 show ?thesis using expr.psimps(19) by simp
                    next
                      case s1: (Some a)
                      then show ?thesis
                      proof (cases a)
                        case (Method x1)
                        then show ?thesis
                        proof (cases x1)
                          case (fields fp f c)
                          then show ?thesis
                          proof (cases c)
                            case None
                            with 29(1) a1 g_def gcost n Pair KValue Value TAddr Some p2 s1 Method fields show ?thesis using expr.psimps(19) by simp
                          next
                            case s2: (Some x)
                            then show ?thesis
                            proof (cases "expr val e\<^sub>p e cd st'")
                              case n1: (n kv st'')
                              then show ?thesis
                              proof (cases kv)
                                case p3: (Pair a b)
                                then show ?thesis
                                proof (cases a)
                                  case k1: (KValue v)
                                  then show ?thesis
                                  proof (cases b)
                                    case v1: (Value t)
                                    define stl e'
                                    where "stl = st''\<lparr>stack:=emptyStore, memory:=emptyStore\<rparr>"
                                      and "e' = ffold (init ct) (emptyEnv adv (address e) v) (fmdom ct)"
                                    then show ?thesis
                                    proof (cases "load True fp xe e\<^sub>p e' emptyStore stl e cd st''")
                                      case s4: (n a st''')
                                      then show ?thesis
                                      proof (cases a)
                                        case f2: (fields e'' cd' st'''')
                                        then show ?thesis
                                        proof (cases "transfer (address e) adv v (accounts st'''')")
                                          case n2: None
                                          with 29(1) a1 g_def gcost n Pair KValue Value TAddr Some p2 s1 Method fields s2 n1 p3 k1 v1 stl_def e'_def s4 f2 show ?thesis using expr.psimps(19) by simp
                                        next
                                          case s3: (Some acc)
                                          show ?thesis
                                          proof (cases "stmt f e\<^sub>p e'' cd' (st''''\<lparr>accounts:=acc\<rparr>)")
                                            case n2: (n a st''''')
                                            then show ?thesis
                                            proof (cases "expr x e\<^sub>p e'' cd' st'''''")
                                              case n3: (n a st'''''')
                                              then show ?thesis
                                              proof (cases a)
                                                case p1: (Pair sv tp)
                                                with 29(1) a1 g_def gcost n Pair KValue Value TAddr Some p2 s1 Method fields s2 n1 p3 k1 v1 s3 stl_def e'_def s4 f2 n2 n3
                                                have "expr (ECALL ad i xe val) e\<^sub>p e cd st = Normal ((sv, tp), st''''''\<lparr>stack:=stack st''', memory := memory st'''\<rparr>)"
                                                    using expr.psimps(19)[of ad i xe val e\<^sub>p e cd st] by (auto simp add: Let_def split: unit.split_asm)
                                                with a1 have "gas st4' \<le> gas st''''''" by auto
                                                also from 29(6)[of "()" "st\<lparr>gas := gas st - g\<rparr>" _ st' _ _ adv _ _ ct _ _ x1 fp "(f,c)" f c x kv st'' _ b v t] a1 g_def gcost n Pair KValue Value TAddr Some p2 s1 Method fields s2 n1 p3 k1 v1 s3 stl_def e'_def s4 f2 n2 n3
                                                  have "\<dots> \<le> gas st'''''" by auto
                                                also from 29(5)[OF _ n Pair KValue Value TAddr Some p2 s1 Method fields _ s2 n1 p3 k1 v1 _ _ s4 f2 _ _ _, of "()" f cd' st'''' st''' st''' acc]  f2 s3 stl_def e'_def   n2 n3 a1 g_def gcost
                                                  have "\<dots> \<le> gas (st''''\<lparr>accounts:=acc\<rparr>)" by auto
                                                also have "\<dots> \<le> gas stl"
                                                proof -
                                                  from g_def gcost have "(applyf (costs\<^sub>e (ECALL ad i xe val) e\<^sub>p e cd) \<bind> (\<lambda>g. assert Gas (\<lambda>st. gas st \<le> g) (modify (\<lambda>st. st\<lparr>gas := gas st - g\<rparr>)))) st = Normal ((), st\<lparr>gas := gas st - g\<rparr>)" by simp
                                                  moreover from e'_def have "e' = ffold_init ct (emptyEnv adv (address e) v) (fmdom ct)" by simp
                                                  moreover from n1 have "expr val e\<^sub>p e cd st' = Normal (kv, st'')" by simp
                                                  moreover from stl_def have "applyf (\<lambda>st. st\<lparr>stack := emptyStore, memory := emptyStore\<rparr>) st'' = Normal (stl, st'')" by simp
                                                  moreover have "applyf accounts st'' = Normal ((accounts st''), st'')" by simp
                                                  ultimately have "\<forall>ev cda sta st'a. load True fp xe e\<^sub>p e' emptyStore stl e cd st'' = Normal ((ev, cda, sta), st'a) \<longrightarrow> gas sta \<le> gas stl \<and> gas st'a \<le> gas st'' \<and> address ev = address e'" using 29(4)[of "()" "st\<lparr>gas := gas st - g\<rparr>" _ st' _ _ adv _ _ ct _ _ x1 fp "(f,c)" f c x kv st'' _ b v t] a1 g_def gcost n Pair KValue Value TAddr Some p2 s1 Method fields s2 n1 p3 k1 v1 s3 stl_def e'_def s4 f2 n2 n3 by blast
                                                  thus ?thesis using stl_def s4 f2 by auto
                                                qed
                                                also from stl_def have "\<dots> \<le> gas st''" by simp
                                                also from 29(3)[of "()" "st\<lparr>gas := gas st - g\<rparr>" _ st' _ _ adv _ _ ct _ _ x1 fp "(f,c)" f c x] a1 g_def gcost n Pair KValue Value TAddr Some p2 s1 Method fields s2 n1 p3 k1 v1 s3 stl_def e'_def s4 f2 n2 n3
                                                  have "\<dots> \<le> gas st'" by (auto split:unit.split_asm)
                                                also from 29(2)[of "()" "st\<lparr>gas := gas st - g\<rparr>"] a1 g_def gcost n Pair KValue Value TAddr Some p2 s1 Method fields s2 n1 p3 k1 v1 s3 stl_def e'_def s4 f2 n2 n3
                                                  have "\<dots> \<le> gas (st\<lparr>gas := gas st - g\<rparr>)" by simp
                                                finally show ?thesis by simp
                                              qed
                                            next
                                              case (e x)
                                              with 29(1) a1 g_def gcost n Pair KValue Value TAddr Some p2 s1 Method fields s2 n1 p3 k1 v1 s3 stl_def e'_def s4 f2 n2 show ?thesis using expr.psimps(19)[of ad i xe val e\<^sub>p e cd st] by simp
                                            qed
                                          next
                                            case (e x)
                                            with 29(1) a1 g_def gcost n Pair KValue Value TAddr Some p2 s1 Method fields s2 n1 p3 k1 v1 s3 stl_def e'_def s4 f2 show ?thesis using expr.psimps(19)[of ad i xe val e\<^sub>p e cd st] by simp
                                          qed
                                        qed
                                      qed
                                    next
                                      case (e x)
                                      with 29(1) a1 g_def gcost n Pair KValue Value TAddr Some p2 s1 Method fields s2 n1 p3 k1 v1 stl_def e'_def show ?thesis using expr.psimps(19)[of ad i xe val e\<^sub>p e cd st] by simp
                                    qed
                                  next
                                    case (Calldata x2)
                                    with 29(1) a1 g_def gcost n Pair KValue Value TAddr Some p2 s1 Method fields s2 n1 p3 k1 show ?thesis using expr.psimps(19)[of ad i xe val e\<^sub>p e cd st] by simp
                                  next
                                    case (Memory x3)
                                    with 29(1) a1 g_def gcost n Pair KValue Value TAddr Some p2 s1 Method fields s2 n1 p3 k1 show ?thesis using expr.psimps(19)[of ad i xe val e\<^sub>p e cd st] by simp
                                  next
                                    case (Storage x4)
                                    with 29(1) a1 g_def gcost n Pair KValue Value TAddr Some p2 s1 Method fields s2 n1 p3 k1 show ?thesis using expr.psimps(19)[of ad i xe val e\<^sub>p e cd st] by simp
                                  qed
                                next
                                  case (KCDptr x2)
                                  with 29(1) a1 g_def gcost n Pair KValue Value TAddr Some p2 s1 Method fields s2 n1 p3 show ?thesis using expr.psimps(19)[of ad i xe val e\<^sub>p e cd st] by simp
                                next
                                  case (KMemptr x3)
                                  with 29(1) a1 g_def gcost n Pair KValue Value TAddr Some p2 s1 Method fields s2 n1 p3 show ?thesis using expr.psimps(19)[of ad i xe val e\<^sub>p e cd st] by simp
                                next
                                  case (KStoptr x4)
                                  with 29(1) a1 g_def gcost n Pair KValue Value TAddr Some p2 s1 Method fields s2 n1 p3 show ?thesis using expr.psimps(19)[of ad i xe val e\<^sub>p e cd st] by simp
                                qed
                              qed
                            next
                              case n2: (e x)
                              with 29(1) a1 g_def gcost n Pair KValue Value TAddr Some p2 s1 Method fields s2 show ?thesis using expr.psimps(19)[of ad i xe val e\<^sub>p e cd st] by simp
                            qed
                          qed
                        qed
                      next
                        case (Var x2)
                        with 29(1) a1 g_def gcost n Pair KValue Value TAddr Some p2 s1 show ?thesis using expr.psimps(19)[of ad i xe val e\<^sub>p e cd st] by simp
                      qed
                    qed
                  qed
                qed
              qed
            next
              case (Calldata x2)
              with 29(1) a1 g_def gcost n Pair KValue show ?thesis using expr.psimps(19)[of ad i xe val e\<^sub>p e cd st] by simp
            next
              case (Memory x3)
              with 29(1) a1 g_def gcost n Pair KValue show ?thesis using expr.psimps(19)[of ad i xe val e\<^sub>p e cd st] by simp
            next
              case (Storage x4)
              with 29(1) a1 g_def gcost n Pair KValue show ?thesis using expr.psimps(19)[of ad i xe val e\<^sub>p e cd st] by simp
            qed
          next
            case (KCDptr x2)
            with 29(1) a1 g_def gcost n Pair show ?thesis using expr.psimps(19)[of ad i xe val e\<^sub>p e cd st] by simp
          next
            case (KMemptr x3)
            with 29(1) a1 g_def gcost n Pair show ?thesis using expr.psimps(19)[of ad i xe val e\<^sub>p e cd st] by simp
          next
            case (KStoptr x4)
            with 29(1) a1 g_def gcost n Pair show ?thesis using expr.psimps(19)[of ad i xe val e\<^sub>p e cd st] by simp
          qed
        qed
      next
        case (e _)
        with 29(1) a1 g_def gcost show ?thesis using expr.psimps(19)[of ad i xe val e\<^sub>p e cd st] by simp
      qed
    qed
  qed
next
  case (30 cp i\<^sub>p t\<^sub>p pl e el e\<^sub>p e\<^sub>v' cd' st' e\<^sub>v cd st)
  then show ?case
  proof (cases "expr e e\<^sub>p e\<^sub>v cd st")
    case (n a st'')
    then show ?thesis
    proof (cases a)
      case (Pair v t)
      then show ?thesis
      proof (cases "decl i\<^sub>p t\<^sub>p (Some (v,t)) cp cd (memory st'') cd' e\<^sub>v' st'")
        case n2: (n a' st''')
        then show ?thesis
        proof (cases a')
          case f2: (Pair cd'' e\<^sub>v'')
          show ?thesis
          proof (rule allI[THEN allI, THEN allI, THEN allI, OF impI])
            fix ev xa xaa xaaa assume load_def: "load cp ((i\<^sub>p, t\<^sub>p) # pl) (e # el) e\<^sub>p e\<^sub>v' cd' st' e\<^sub>v cd st = Normal ((ev, xa, xaa), xaaa)"
            with 30(1) n Pair n2 f2 have "load cp ((i\<^sub>p, t\<^sub>p) # pl) (e # el) e\<^sub>p e\<^sub>v' cd' st' e\<^sub>v cd st = load cp pl el e\<^sub>p e\<^sub>v'' cd'' st''' e\<^sub>v cd st''" using load.psimps(1)[of cp i\<^sub>p t\<^sub>p pl e el e\<^sub>p e\<^sub>v' cd' st' e\<^sub>v cd st] by simp
            with load_def have "load cp pl el e\<^sub>p e\<^sub>v'' cd'' st''' e\<^sub>v cd st'' = Normal ((ev, xa, xaa), xaaa)" by simp
            with n Pair n2 f2 have "gas xaa \<le> gas st''' \<and> gas xaaa \<le> gas st'' \<and> address ev = address e\<^sub>v''" using 30(3)[of a st'' v t st'' st'' "()" st' a' st''' cd'' e\<^sub>v'' st''' st''' "()" st''] by simp
            moreover from n Pair have "gas st'' \<le> gas st" using 30(2) by simp
            moreover from n2 f2 have " address e\<^sub>v'' =  address e\<^sub>v'" and "gas st''' \<le> gas st'" using decl_gas_address by auto
            ultimately show "gas xaa \<le> gas st' \<and> gas xaaa \<le> gas st \<and> address ev = address e\<^sub>v'" by simp
          qed
        qed
      next
        case (e x)
        with 30(1) n Pair show ?thesis using load.psimps(1) by simp
      qed
    qed
  next
    case (e x)
    with 30(1) show ?thesis using load.psimps(1) by simp
  qed
next
  case (31 we wf wg wh wi wj wk st)
  then show ?case using load.psimps(2) by auto
next
  case (32 wl wm wn wo wp wq wr st)
  then show ?case using load.psimps(3)[of wl wm wn wo wp wq wr] by auto
next
  case (33 ws wt wu wv cd e\<^sub>v s st)
  then show ?case using load.psimps(4)[of ws wt wu wv cd e\<^sub>v s st] by auto
next
  case (34 i e\<^sub>p e cd st)
  show ?case
  proof (rule allI[THEN allI, THEN allI, OF impI])
    fix st3' xa xaa assume "rexp (L.Id i) e\<^sub>p e cd st = Normal ((st3', xa), xaa)"
    then show "gas xaa \<le> gas st" using 34(1) rexp.psimps(1) by (simp split: option.split_asm Denvalue.split_asm Stackvalue.split_asm prod.split_asm Type.split_asm STypes.split_asm)
  qed
next
  case (35 i r e\<^sub>p e cd st)
  show ?case
  proof (rule allI[THEN allI, THEN allI, OF impI])
    fix st3' xa xaa assume rexp_def: "rexp (Ref i r) e\<^sub>p e cd st = Normal ((st3', xa), xaa)"
    show "gas xaa \<le> gas st"
    proof (cases "fmlookup (denvalue e) i")
      case None
      with 35(1) show ?thesis using rexp.psimps rexp_def by simp
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
            with 35(1) Some Pair Stackloc show ?thesis using rexp.psimps(2) rexp_def by simp
          next
            case s1: (Some a)
            then show ?thesis
            proof (cases a)
              case (KValue x1)
              with 35(1) Some Pair Stackloc s1 show ?thesis using rexp.psimps(2) rexp_def by simp
            next
              case (KCDptr l')
              with 35 Some Pair Stackloc s1 show ?thesis using rexp.psimps(2)[of i r e\<^sub>p e cd st] rexp_def by (simp split: option.split_asm Memoryvalue.split_asm MTypes.split_asm prod.split_asm Type.split_asm StateMonad.result.split_asm)
            next
              case (KMemptr x3)
              with 35 Some Pair Stackloc s1 show ?thesis using rexp.psimps(2)[of i r e\<^sub>p e cd st] rexp_def by (simp split: option.split_asm Memoryvalue.split_asm MTypes.split_asm prod.split_asm Type.split_asm StateMonad.result.split_asm)
            next
              case (KStoptr x4)
              with 35 Some Pair Stackloc s1 show ?thesis using rexp.psimps(2)[of i r e\<^sub>p e cd st] rexp_def by (simp split: option.split_asm STypes.split_asm prod.split_asm Type.split_asm StateMonad.result.split_asm)
            qed
          qed
        next
          case (Storeloc x2)
          with 35 Some Pair show ?thesis using rexp.psimps rexp_def by (simp split: option.split_asm STypes.split_asm prod.split_asm Type.split_asm  StateMonad.result.split_asm)
        qed
      qed
    qed
  qed
next
  case (36 e\<^sub>p e cd st)
  then show ?case using stmt.psimps(1) by simp
next
  case (37 lv ex e\<^sub>p env cd st)
  define g where "g = costs (ASSIGN lv ex) e\<^sub>p env cd st"
  show ?case
  proof (rule allI[OF impI])
    fix st6'
    assume stmt_def: "stmt (ASSIGN lv ex) e\<^sub>p env cd st = Normal ((), st6')"
    then show "gas st6' \<le> gas st"
    proof cases
      assume "gas st \<le> g"
      with 37 stmt_def show ?thesis using stmt.psimps(2) g_def by simp
    next
      assume "\<not> gas st \<le> g"
      show ?thesis
      proof (cases "expr ex e\<^sub>p env cd (st\<lparr>gas := gas st - g\<rparr>)")
        case (n a st')
        then show ?thesis
        proof (cases a)
          case (Pair b c)
          then show ?thesis
          proof (cases b)
            case (KValue v)
            then show ?thesis
            proof (cases c)
              case (Value t)
              then show ?thesis
              proof (cases "lexp lv e\<^sub>p env cd st'")
                case n2: (n a st'')
                then show ?thesis
                proof (cases a)
                  case p1: (Pair a b)
                  then show ?thesis
                  proof (cases a)
                    case (LStackloc l)
                    then show ?thesis
                    proof (cases b)
                      case v2: (Value t')
                      then show ?thesis
                      proof (cases "convert t t' v ")
                        case None
                        with 37(1) stmt_def `\<not> gas st \<le> g` n Pair KValue Value n2 p1 LStackloc v2 show ?thesis using stmt.psimps(2) g_def by simp
                      next
                        case s3: (Some a)
                        then show ?thesis
                        proof (cases a)
                          case p2: (Pair v' b)
                          with 37(1) `\<not> gas st \<le> g` n Pair KValue Value n2 p1 LStackloc v2 s3
                          have "stmt (ASSIGN lv ex) e\<^sub>p env cd st = Normal ((), st'' \<lparr>stack := updateStore l (KValue v') (stack st'')\<rparr>)"
                            using stmt.psimps(2) g_def by simp
                          with stmt_def have "st6'= (st''\<lparr>stack := updateStore l (KValue v') (stack st'')\<rparr>)" by simp
                          moreover from 37(3) `\<not> gas st \<le> g` n Pair KValue Value n2 p1 have "gas st'' \<le> gas st'" using g_def by simp
                          moreover from 37(2) `\<not> gas st \<le> g` n Pair KValue Value n2 p2 have "gas st' \<le> gas st" using g_def by simp
                          ultimately show ?thesis by simp
                        qed
                      qed
                    next
                      case (Calldata x2)
                      with 37(1) stmt_def `\<not> gas st \<le> g` n Pair KValue Value n2 p1 LStackloc show ?thesis using stmt.psimps(2) g_def by simp
                    next
                      case (Memory x3)
                      with 37(1) stmt_def `\<not> gas st \<le> g` n Pair KValue Value n2 p1 LStackloc show ?thesis using stmt.psimps(2) g_def by simp
                    next
                      case (Storage x4)
                      with 37(1) stmt_def `\<not> gas st \<le> g` n Pair KValue Value n2 p1 LStackloc show ?thesis using stmt.psimps(2) g_def by simp
                    qed
                  next
                    case (LMemloc l)
                    then show ?thesis
                    proof (cases b)
                      case v2: (Value t')
                      with 37(1) stmt_def `\<not> gas st \<le> g` n Pair KValue Value n2 p1 LMemloc show ?thesis using stmt.psimps(2) g_def by simp
                    next
                      case (Calldata x2)
                      with 37(1) stmt_def `\<not> gas st \<le> g` n Pair KValue Value n2 p1 LMemloc show ?thesis using stmt.psimps(2) g_def by simp
                    next
                      case (Memory x3)
                      then show ?thesis
                      proof (cases x3)
                        case (MTArray x11 x12)
                        with 37(1) stmt_def `\<not> gas st \<le> g` n Pair KValue Value n2 p1 LMemloc Memory show ?thesis using stmt.psimps(2) g_def by simp
                      next
                        case (MTValue t')
                        then show ?thesis
                        proof (cases "convert t t' v ")
                          case None
                          with 37(1) stmt_def `\<not> gas st \<le> g` n Pair KValue Value n2 p1 LMemloc Memory MTValue show ?thesis using stmt.psimps(2) g_def by simp
                        next
                          case s3: (Some a)
                          then show ?thesis
                          proof (cases a)
                            case p2: (Pair v' b)
                            with 37(1) `\<not> gas st \<le> g` n Pair KValue Value n2 p1 LMemloc Memory MTValue s3
                            have "stmt (ASSIGN lv ex) e\<^sub>p env cd st = Normal ((), st'' \<lparr>memory := updateStore l (MValue v') (memory st'')\<rparr>)"
                              using stmt.psimps(2) g_def by simp
                            with stmt_def have "st6'= (st''\<lparr>memory := updateStore l (MValue v') (memory st'')\<rparr>)" by simp
                            moreover from 37(3) `\<not> gas st \<le> g` n Pair KValue Value n2 p1 have "gas st'' \<le> gas st'" using g_def by simp
                            moreover from 37(2) `\<not> gas st \<le> g` n Pair KValue Value n2 p1 have "gas st' \<le> gas st" using g_def by simp
                            ultimately show ?thesis by simp
                          qed
                        qed
                      qed
                    next
                      case (Storage x4)
                      with 37(1) stmt_def `\<not> gas st \<le> g` n Pair KValue Value n2 p1 LMemloc show ?thesis using stmt.psimps(2) g_def by simp
                    qed
                  next
                    case (LStoreloc l)
                    then show ?thesis
                    proof (cases b)
                      case v2: (Value t')
                      with 37(1) stmt_def `\<not> gas st \<le> g` n Pair KValue Value n2 p1 LStoreloc show ?thesis using stmt.psimps(2) g_def by simp
                    next
                      case (Calldata x2)
                      with 37(1) stmt_def `\<not> gas st \<le> g` n Pair KValue Value n2 p1 LStoreloc show ?thesis using stmt.psimps(2) g_def by simp
                    next
                      case (Memory x3)
                      with 37(1) stmt_def `\<not> gas st \<le> g` n Pair KValue Value n2 p1 LStoreloc show ?thesis using stmt.psimps(2) g_def by simp
                    next
                      case (Storage x4)
                      then show ?thesis
                      proof (cases x4)
                        case (STArray x11 x12)
                        with 37(1) stmt_def `\<not> gas st \<le> g` n Pair KValue Value n2 p1 LStoreloc Storage show ?thesis using stmt.psimps(2) g_def by simp
                      next
                        case (STMap x21 x22)
                        with 37(1) stmt_def `\<not> gas st \<le> g` n Pair KValue Value n2 p1 LStoreloc Storage show ?thesis using stmt.psimps(2) g_def by simp
                      next
                        case (STValue t')
                        then show ?thesis
                        proof (cases "convert t t' v ")
                          case None
                          with 37(1) stmt_def `\<not> gas st \<le> g` n Pair KValue Value n2 p1 LStoreloc Storage STValue show ?thesis using stmt.psimps(2) g_def by simp
                        next
                          case s3: (Some a)
                          then show ?thesis
                          proof (cases a)
                            case p2: (Pair v' b)
                            then show ?thesis
                            proof (cases "fmlookup (storage st'') (address env)")
                              case None
                              with 37(1) stmt_def `\<not> gas st \<le> g` n Pair KValue Value n2 p1 LStoreloc Storage STValue s3 p2 show ?thesis using stmt.psimps(2) g_def by simp
                            next
                              case s4: (Some s)
                              with 37(1) `\<not> gas st \<le> g` n Pair KValue Value n2 p1 LStoreloc Storage STValue s3 p2
                              have "stmt (ASSIGN lv ex) e\<^sub>p env cd st = Normal ((), st'' \<lparr>storage := fmupd (address env) (fmupd l v' s) (storage st'')\<rparr>)"
                                using stmt.psimps(2) g_def by simp
                              with stmt_def have "st6'= st'' \<lparr>storage := fmupd (address env) (fmupd l v' s) (storage st'')\<rparr>" by simp
                              moreover from 37(3) `\<not> gas st \<le> g` n Pair KValue Value n2 p1 have "gas st'' \<le> gas st'" using g_def by simp
                              moreover from 37(2) `\<not> gas st \<le> g` n Pair KValue Value n2 p1 have "gas st' \<le> gas st" using g_def by simp
                              ultimately show ?thesis by simp
                            qed
                          qed
                        qed
                      qed
                    qed
                  qed
                qed
              next
                case (e x)
                with 37(1) stmt_def `\<not> gas st \<le> g` n Pair KValue Value show ?thesis using stmt.psimps(2) g_def by simp
              qed
            next
              case (Calldata x2)
              with 37(1) stmt_def `\<not> gas st \<le> g` n Pair KValue show ?thesis using stmt.psimps(2) g_def by simp
            next
              case (Memory x3)
              with 37(1) stmt_def `\<not> gas st \<le> g` n Pair KValue show ?thesis using stmt.psimps(2) g_def by simp
            next
              case (Storage x4)
              with 37(1) stmt_def `\<not> gas st \<le> g` n Pair KValue show ?thesis using stmt.psimps(2) g_def by simp
            qed
          next
            case (KCDptr p)
            then show ?thesis
            proof (cases c)
              case (Value x1)
              with 37(1) stmt_def `\<not> gas st \<le> g` n Pair KCDptr show ?thesis using stmt.psimps(2) g_def by simp
            next
              case (Calldata x2)
              then show ?thesis
              proof (cases x2)
                case (MTArray x t)
                then show ?thesis
                proof (cases "lexp lv e\<^sub>p env cd st'")
                  case n2: (n a st'')
                  then show ?thesis
                  proof (cases a)
                    case p2: (Pair a b)
                    then show ?thesis
                    proof (cases a)
                      case (LStackloc l)
                      then show ?thesis
                      proof (cases b)
                        case v2: (Value t')
                        with 37(1) stmt_def `\<not> gas st \<le> g` n Pair KCDptr Calldata MTArray n2 p2 LStackloc show ?thesis using stmt.psimps(2) g_def by simp
                      next
                        case c2: (Calldata x2)
                        with 37(1) stmt_def `\<not> gas st \<le> g` n Pair KCDptr Calldata MTArray n2 p2 LStackloc show ?thesis using stmt.psimps(2) g_def by simp
                      next
                        case (Memory x3)
                        with 37(1) `\<not> gas st \<le> g` n Pair KCDptr Calldata MTArray n2 p2 LStackloc
                        have "stmt (ASSIGN lv ex) e\<^sub>p env cd st = Normal ((), st'' \<lparr>stack := updateStore l (KCDptr p) (stack st'')\<rparr>)"
                          using stmt.psimps(2) g_def by simp
                        with stmt_def have "st6'= (st''\<lparr>stack := updateStore l (KCDptr p) (stack st'')\<rparr>)" by simp
                        moreover from 37(4) `\<not> gas st \<le> g` n Pair KCDptr Calldata MTArray n2 p2 have "gas st'' \<le> gas st'" using g_def by simp
                        moreover from 37(2) `\<not> gas st \<le> g` n Pair have "gas st' \<le> gas st" using g_def by simp
                        ultimately show ?thesis by simp
                      next
                        case (Storage x4)
                        then show ?thesis
                        proof (cases "accessStore l (stack st'')")
                          case None
                          with 37(1) stmt_def `\<not> gas st \<le> g` n Pair KCDptr Calldata MTArray n2 p2 LStackloc Storage show ?thesis using stmt.psimps(2) g_def by simp
                        next
                          case s3: (Some a)
                          then show ?thesis
                          proof (cases a)
                            case (KValue x1)
                            with 37(1) stmt_def `\<not> gas st \<le> g` n Pair KCDptr Calldata MTArray n2 p2 LStackloc Storage s3 show ?thesis using stmt.psimps(2) g_def by simp
                          next
                            case c3: (KCDptr x2)
                            with 37(1) stmt_def `\<not> gas st \<le> g` n Pair KCDptr Calldata MTArray n2 p2 LStackloc Storage s3 show ?thesis using stmt.psimps(2) g_def by simp
                          next
                            case (KMemptr x3)
                            with 37(1) stmt_def `\<not> gas st \<le> g` n Pair KCDptr Calldata MTArray n2 p2 LStackloc Storage s3 show ?thesis using stmt.psimps(2) g_def by simp
                          next
                            case (KStoptr p')
                            then show ?thesis
                            proof (cases "fmlookup (storage st'') (address env)")
                              case None
                              with 37(1) stmt_def `\<not> gas st \<le> g` n Pair KCDptr Calldata MTArray n2 p2 LStackloc Storage s3 KStoptr show ?thesis using stmt.psimps(2) g_def by simp
                            next
                              case s4: (Some s)
                              then show ?thesis
                              proof (cases "cpm2s p p' x t cd s")
                                case None
                                with 37(1) stmt_def `\<not> gas st \<le> g` n Pair KCDptr Calldata MTArray n2 p2 LStackloc Storage s3 KStoptr s4 show ?thesis using stmt.psimps(2) g_def by simp
                              next
                                case (Some s')
                                with 37(1) `\<not> gas st \<le> g` n Pair KCDptr Calldata MTArray n2 p2 LStackloc Storage s3 KStoptr s4
                                have "stmt (ASSIGN lv ex) e\<^sub>p env cd st = Normal ((), st'' \<lparr>storage := fmupd (address env) s' (storage st'')\<rparr>)"
                                  using stmt.psimps(2) g_def by simp
                                with stmt_def have "st6'= st'' \<lparr>storage := fmupd (address env) s' (storage st'')\<rparr>" by simp
                                moreover from 37(4) `\<not> gas st \<le> g` n Pair KCDptr Calldata MTArray n2 p2 have "gas st'' \<le> gas st'" using g_def by simp
                                moreover from 37(2) `\<not> gas st \<le> g` n Pair have "gas st' \<le> gas st" using g_def by simp
                                ultimately show ?thesis by simp
                              qed
                            qed
                          qed
                        qed
                      qed
                    next
                      case (LMemloc l)
                      then show ?thesis
                      proof (cases "cpm2m p l x t cd (memory st'')")
                        case None
                        with 37(1) stmt_def `\<not> gas st \<le> g` n Pair KCDptr Calldata MTArray n2 p2 LMemloc show ?thesis using stmt.psimps(2) g_def by simp
                      next
                        case (Some m)
                        with 37(1) `\<not> gas st \<le> g` n Pair KCDptr Calldata MTArray n2 p2 LMemloc
                        have "stmt (ASSIGN lv ex) e\<^sub>p env cd st = Normal ((), st'' \<lparr>memory := m\<rparr>)"
                          using stmt.psimps(2) g_def by simp
                        with stmt_def have "st6'= (st''\<lparr>memory := m\<rparr>)" by simp
                        moreover from 37(4) `\<not> gas st \<le> g` n Pair KCDptr Calldata MTArray n2 p2 have "gas st'' \<le> gas st'" using g_def by simp
                        moreover from 37(2) `\<not> gas st \<le> g` n Pair have "gas st' \<le> gas st" using g_def by simp
                        ultimately show ?thesis by simp
                      qed
                    next
                      case (LStoreloc l)
                      then show ?thesis
                      proof (cases "fmlookup (storage st'') (address env)")
                        case None
                        with 37(1) stmt_def `\<not> gas st \<le> g` n Pair KCDptr Calldata MTArray n2 p2 LStoreloc show ?thesis using stmt.psimps(2) g_def by simp
                      next
                        case s4: (Some s)
                        then show ?thesis
                        proof (cases "cpm2s p l x t cd s")
                          case None
                          with 37(1) stmt_def `\<not> gas st \<le> g` n Pair KCDptr Calldata MTArray n2 p2 LStoreloc s4 show ?thesis using stmt.psimps(2) g_def by simp
                        next
                          case (Some s')
                          with 37(1) `\<not> gas st \<le> g` n Pair KCDptr Calldata MTArray n2 p2 LStoreloc s4
                          have "stmt (ASSIGN lv ex) e\<^sub>p env cd st = Normal ((), st'' \<lparr>storage := fmupd (address env) s' (storage st'')\<rparr>)"
                            using stmt.psimps(2) g_def by simp
                          with stmt_def have "st6'= (st''\<lparr>storage := fmupd (address env) s' (storage st'')\<rparr>)" by simp
                          moreover from 37(4) `\<not> gas st \<le> g` n Pair KCDptr Calldata MTArray n2 p2 have "gas st'' \<le> gas st'" using g_def by simp
                          moreover from 37(2) `\<not> gas st \<le> g` n Pair have "gas st' \<le> gas st" using g_def by simp
                          ultimately show ?thesis by simp
                        qed
                      qed
                    qed
                  qed
                next
                  case (e x)
                  with 37(1) stmt_def `\<not> gas st \<le> g` n Pair KCDptr Calldata MTArray show ?thesis using stmt.psimps(2) g_def by simp
                qed
              next
                case (MTValue x2)
                with 37(1) stmt_def `\<not> gas st \<le> g` n Pair KCDptr Calldata show ?thesis using stmt.psimps(2) g_def by simp
              qed
            next
              case (Memory x3)
              with 37(1) stmt_def `\<not> gas st \<le> g` n Pair KCDptr show ?thesis using stmt.psimps(2) g_def by simp
            next
              case (Storage x4)
              with 37(1) stmt_def `\<not> gas st \<le> g` n Pair KCDptr show ?thesis using stmt.psimps(2) g_def by simp
            qed
          next
            case (KMemptr p)
            then show ?thesis
            proof (cases c)
              case (Value x1)
              with 37(1) stmt_def `\<not> gas st \<le> g` n Pair KMemptr show ?thesis using stmt.psimps(2) g_def by simp
            next
              case (Calldata x2)
              with 37(1) stmt_def `\<not> gas st \<le> g` n Pair KMemptr show ?thesis using stmt.psimps(2) g_def by simp
            next
              case (Memory x3)
              then show ?thesis
              proof (cases x3)
                case (MTArray x t)
                then show ?thesis
                proof (cases "lexp lv e\<^sub>p env cd st'")
                  case n2: (n a st'')
                  then show ?thesis
                  proof (cases a)
                    case p2: (Pair a b)
                    then show ?thesis
                    proof (cases a)
                      case (LStackloc l)
                      then show ?thesis
                      proof (cases b)
                        case v2: (Value t')
                        with 37(1) stmt_def `\<not> gas st \<le> g` n Pair KMemptr Memory MTArray n2 p2 LStackloc show ?thesis using stmt.psimps(2) g_def by simp
                      next
                        case c2: (Calldata x2)
                        with 37(1) stmt_def `\<not> gas st \<le> g` n Pair KMemptr Memory MTArray n2 p2 LStackloc show ?thesis using stmt.psimps(2) g_def by simp
                      next
                        case m2: (Memory x3)
                        with 37(1) `\<not> gas st \<le> g` n Pair KMemptr Memory MTArray n2 p2 LStackloc
                        have "stmt (ASSIGN lv ex) e\<^sub>p env cd st = Normal ((), st'' \<lparr>stack := updateStore l (KMemptr p) (stack st'')\<rparr>)"
                          using stmt.psimps(2) g_def by simp
                        with stmt_def have "st6'= (st''\<lparr>stack := updateStore l (KMemptr p) (stack st'')\<rparr>)" by simp
                        moreover from 37(5) `\<not> gas st \<le> g` n Pair KMemptr Memory MTArray n2 p2 have "gas st'' \<le> gas st'" using g_def by simp
                        moreover from 37(2) `\<not> gas st \<le> g` n Pair have "gas st' \<le> gas st" using g_def by simp
                        ultimately show ?thesis by simp
                      next
                        case (Storage x4)
                        then show ?thesis
                        proof (cases "accessStore l (stack st'')")
                          case None
                          with 37(1) stmt_def `\<not> gas st \<le> g` n Pair KMemptr Memory MTArray n2 p2 LStackloc Storage show ?thesis using stmt.psimps(2) g_def by simp
                        next
                          case s3: (Some a)
                          then show ?thesis
                          proof (cases a)
                            case (KValue x1)
                            with 37(1) stmt_def `\<not> gas st \<le> g` n Pair KMemptr Memory MTArray n2 p2 LStackloc Storage s3 show ?thesis using stmt.psimps(2) g_def by simp
                          next
                            case c3: (KCDptr x2)
                            with 37(1) stmt_def `\<not> gas st \<le> g` n Pair KMemptr Memory MTArray n2 p2 LStackloc Storage s3 show ?thesis using stmt.psimps(2) g_def by simp
                          next
                            case m3: (KMemptr x3)
                            with 37(1) stmt_def `\<not> gas st \<le> g` n Pair KMemptr Memory MTArray n2 p2 LStackloc Storage s3 show ?thesis using stmt.psimps(2) g_def by simp
                          next
                            case (KStoptr p')
                            then show ?thesis
                            proof (cases "fmlookup (storage st'') (address env)")
                              case None
                              with 37(1) stmt_def `\<not> gas st \<le> g` n Pair KMemptr Memory MTArray n2 p2 LStackloc Storage s3 KStoptr show ?thesis using stmt.psimps(2) g_def by simp
                            next
                              case s4: (Some s)
                              then show ?thesis
                              proof (cases "cpm2s p p' x t (memory st'') s")
                                case None
                                with 37(1) stmt_def `\<not> gas st \<le> g` n Pair KMemptr Memory MTArray n2 p2 LStackloc Storage s3 KStoptr s4 show ?thesis using stmt.psimps(2) g_def by simp
                              next
                                case (Some s')
                                with 37(1) `\<not> gas st \<le> g` n Pair KMemptr Memory MTArray n2 p2 LStackloc Storage s3 KStoptr s4
                                have "stmt (ASSIGN lv ex) e\<^sub>p env cd st =  Normal ((), st'' \<lparr>storage := fmupd (address env) s' (storage st'')\<rparr>)"
                                  using stmt.psimps(2) g_def by simp
                                with stmt_def have "st6'= (st''\<lparr>storage := fmupd (address env) s' (storage st'')\<rparr>)" by simp
                                moreover from 37(5) `\<not> gas st \<le> g` n Pair KMemptr Memory MTArray n2 p2 have "gas st'' \<le> gas st'" using g_def by simp
                                moreover from 37(2) `\<not> gas st \<le> g` n Pair have "gas st' \<le> gas st" using g_def by simp
                                ultimately show ?thesis by simp
                              qed
                            qed
                          qed
                        qed
                      qed
                    next
                      case (LMemloc l)
                      with 37(1) `\<not> gas st \<le> g` n Pair KMemptr Memory MTArray n2 p2 LMemloc
                      have "stmt (ASSIGN lv ex) e\<^sub>p env cd st =  Normal ((), st'' \<lparr>memory := updateStore l (MPointer p) (memory st'')\<rparr>)"
                        using stmt.psimps(2) g_def by simp
                      with stmt_def have "st6'= st'' \<lparr>memory := updateStore l (MPointer p) (memory st'')\<rparr>" by simp
                      moreover from 37(5) `\<not> gas st \<le> g` n Pair KMemptr Memory MTArray n2 p2 have "gas st'' \<le> gas st'" using g_def by simp
                      moreover from 37(2) `\<not> gas st \<le> g` n Pair have "gas st' \<le> gas st" using g_def by simp
                      ultimately show ?thesis by simp
                    next
                      case (LStoreloc l)
                      then show ?thesis
                      proof (cases "fmlookup (storage st'') (address env)")
                        case None
                        with 37(1) stmt_def `\<not> gas st \<le> g` n Pair KMemptr Memory MTArray n2 p2 LStoreloc show ?thesis using stmt.psimps(2) g_def by simp
                      next
                        case s3: (Some s)
                        then show ?thesis
                        proof (cases "cpm2s p l x t (memory st'') s")
                          case None
                          with 37(1) stmt_def `\<not> gas st \<le> g` n Pair KMemptr Memory MTArray n2 p2 LStoreloc s3 show ?thesis using stmt.psimps(2) g_def by simp
                        next
                          case (Some s')
                          with 37(1) `\<not> gas st \<le> g` n Pair KMemptr Memory MTArray n2 p2 LStoreloc s3
                          have "stmt (ASSIGN lv ex) e\<^sub>p env cd st =  Normal ((), st'' \<lparr>storage := fmupd (address env) s' (storage st'')\<rparr>)"
                            using stmt.psimps(2) g_def by simp
                          with stmt_def have "st6'= st''\<lparr>storage := fmupd (address env) s' (storage st'')\<rparr>" by simp
                          moreover from 37(5) `\<not> gas st \<le> g` n Pair KMemptr Memory MTArray n2 p2 have "gas st'' \<le> gas st'" using g_def by simp
                          moreover from 37(2) `\<not> gas st \<le> g` n Pair have "gas st' \<le> gas st" using g_def by simp
                          ultimately show ?thesis by simp
                        qed
                      qed
                    qed
                  qed
                next
                  case (e x)
                  with 37(1) stmt_def `\<not> gas st \<le> g` n Pair KMemptr Memory MTArray show ?thesis using stmt.psimps(2) g_def by simp
                qed
              next
                case (MTValue x2)
                with 37(1) stmt_def `\<not> gas st \<le> g` n Pair KMemptr Memory show ?thesis using stmt.psimps(2) g_def by simp
              qed
            next
              case (Storage x4)
              with 37(1) stmt_def `\<not> gas st \<le> g` n Pair KMemptr show ?thesis using stmt.psimps(2) g_def by simp
            qed
          next
            case (KStoptr p)
            then show ?thesis
            proof (cases c)
              case (Value x1)
              with 37(1) stmt_def `\<not> gas st \<le> g` n Pair KStoptr show ?thesis using stmt.psimps(2) g_def by simp
            next
              case (Calldata x2)
              with 37(1) stmt_def `\<not> gas st \<le> g` n Pair KStoptr show ?thesis using stmt.psimps(2) g_def by simp
            next
              case (Memory x3)
              with 37(1) stmt_def `\<not> gas st \<le> g` n Pair KStoptr show ?thesis using stmt.psimps(2) g_def by simp
            next
              case (Storage x4)
              then show ?thesis
              proof (cases x4)
                case (STArray x t)
                then show ?thesis
                proof (cases "lexp lv e\<^sub>p env cd st'")
                  case n2: (n a st'')
                  then show ?thesis
                  proof (cases a)
                    case p2: (Pair a b)
                    then show ?thesis
                    proof (cases a)
                      case (LStackloc l)
                      then show ?thesis
                      proof (cases b)
                        case v2: (Value t')
                        with 37(1) stmt_def `\<not> gas st \<le> g` n Pair KStoptr Storage STArray n2 p2 LStackloc show ?thesis using stmt.psimps(2) g_def by simp
                      next
                        case c2: (Calldata x2)
                        with 37(1) stmt_def `\<not> gas st \<le> g` n Pair KStoptr Storage STArray n2 p2 LStackloc show ?thesis using stmt.psimps(2) g_def by simp
                      next
                        case (Memory x3)
                        then show ?thesis
                        proof (cases "accessStore l (stack st'')")
                          case None
                          with 37(1) stmt_def `\<not> gas st \<le> g` n Pair KStoptr Storage STArray n2 p2 LStackloc Memory show ?thesis using stmt.psimps(2) g_def by simp
                        next
                          case s3: (Some a)
                          then show ?thesis
                          proof (cases a)
                            case (KValue x1)
                            with 37(1) stmt_def `\<not> gas st \<le> g` n Pair KStoptr Storage STArray n2 p2 LStackloc Memory s3 show ?thesis using stmt.psimps(2) g_def by simp
                          next
                            case c3: (KCDptr x2)
                            with 37(1) stmt_def `\<not> gas st \<le> g` n Pair KStoptr Storage STArray n2 p2 LStackloc Memory s3 show ?thesis using stmt.psimps(2) g_def by simp
                          next
                            case (KMemptr p')
                            then show ?thesis
                            proof (cases "fmlookup (storage st'') (address env)")
                              case None
                              with 37(1) stmt_def `\<not> gas st \<le> g` n Pair KStoptr Storage STArray n2 p2 LStackloc Memory s3 KMemptr show ?thesis using stmt.psimps(2) g_def by simp
                            next
                              case s4: (Some s)
                              then show ?thesis
                              proof (cases "cps2m p p' x t s (memory st'')")
                                case None
                                with 37(1) stmt_def `\<not> gas st \<le> g` n Pair KStoptr Storage STArray n2 p2 LStackloc Memory s3 KMemptr s4 show ?thesis using stmt.psimps(2) g_def by simp
                              next
                                case (Some m)
                                with 37(1) `\<not> gas st \<le> g` n Pair KStoptr Storage STArray n2 p2 LStackloc Memory s3 KMemptr s4
                                have "stmt (ASSIGN lv ex) e\<^sub>p env cd st =  Normal ((), st'' \<lparr>memory := m\<rparr>)"
                                  using stmt.psimps(2) g_def by simp
                                with stmt_def have "st6'= (st''\<lparr>memory := m\<rparr>)" by simp
                                moreover from 37(6) `\<not> gas st \<le> g` n Pair KStoptr Storage STArray n2 p2 have "gas st'' \<le> gas st'" using g_def by simp
                                moreover from 37(2) `\<not> gas st \<le> g` n Pair have "gas st' \<le> gas st" using g_def by simp
                                ultimately show ?thesis by simp
                              qed
                            qed
                          next
                            case sp2: (KStoptr p')
                            with 37(1) stmt_def `\<not> gas st \<le> g` n Pair KStoptr Storage STArray n2 p2 LStackloc Memory s3 show ?thesis using stmt.psimps(2) g_def by simp
                          qed
                        qed
                      next
                        case st2: (Storage x4)
                        with 37(1) `\<not> gas st \<le> g` n Pair KStoptr Storage STArray n2 p2 LStackloc
                        have "stmt (ASSIGN lv ex) e\<^sub>p env cd st =  Normal ((), st'' \<lparr>stack := updateStore l (KStoptr p) (stack st'')\<rparr>)"
                          using stmt.psimps(2) g_def by simp
                        with stmt_def have "st6'= (st''\<lparr>stack := updateStore l (KStoptr p) (stack st'')\<rparr>)" by simp
                        moreover from 37(6) `\<not> gas st \<le> g` n Pair KStoptr Storage STArray n2 p2 have "gas st'' \<le> gas st'" using g_def by simp
                        moreover from 37(2) `\<not> gas st \<le> g` n Pair have "gas st' \<le> gas st" using g_def by simp
                        ultimately show ?thesis by simp
                      qed
                    next
                      case (LMemloc l)
                      then show ?thesis
                      proof (cases "fmlookup (storage st'') (address env)")
                        case None
                        with 37(1) stmt_def `\<not> gas st \<le> g` n Pair KStoptr Storage STArray n2 p2 LMemloc show ?thesis using stmt.psimps(2) g_def by simp
                      next
                        case s4: (Some s)
                        then show ?thesis
                        proof (cases "cps2m p l x t s (memory st'')")
                          case None
                          with 37(1) stmt_def `\<not> gas st \<le> g` n Pair KStoptr Storage STArray n2 p2 LMemloc s4 show ?thesis using stmt.psimps(2) g_def by simp
                        next
                          case (Some m)
                          with 37(1) `\<not> gas st \<le> g` n Pair KStoptr Storage STArray n2 p2 LMemloc s4
                          have "stmt (ASSIGN lv ex) e\<^sub>p env cd st =  Normal ((), st'' \<lparr>memory := m\<rparr>)"
                            using stmt.psimps(2) g_def by simp
                          with stmt_def have "st6'= (st''\<lparr>memory := m\<rparr>)" by simp
                          moreover from 37(6) `\<not> gas st \<le> g` n Pair KStoptr Storage STArray n2 p2 have "gas st'' \<le> gas st'" using g_def by simp
                          moreover from 37(2) `\<not> gas st \<le> g` n Pair have "gas st' \<le> gas st" using g_def by simp
                          ultimately show ?thesis by simp
                        qed
                      qed
                    next
                      case (LStoreloc l)
                      then show ?thesis
                      proof (cases "fmlookup (storage st'') (address env)")
                        case None
                        with 37(1) stmt_def `\<not> gas st \<le> g` n Pair KStoptr Storage STArray n2 p2 LStoreloc show ?thesis using stmt.psimps(2) g_def by simp
                      next
                        case s4: (Some s)
                        then show ?thesis 
                        proof (cases "copy p l x t s")
                          case None
                          with 37(1) stmt_def `\<not> gas st \<le> g` n Pair KStoptr Storage STArray n2 p2 LStoreloc s4 show ?thesis using stmt.psimps(2) g_def by simp
                        next
                          case (Some s')
                          with 37(1) `\<not> gas st \<le> g` n Pair KStoptr Storage STArray n2 p2 LStoreloc s4
                          have "stmt (ASSIGN lv ex) e\<^sub>p env cd st = Normal ((), st'' \<lparr>storage := fmupd (address env) s' (storage st'')\<rparr>)"
                            using stmt.psimps(2) g_def by simp
                          with stmt_def have "st6'= st''\<lparr>storage := fmupd (address env) s' (storage st'')\<rparr>" by simp
                          moreover from 37(6) `\<not> gas st \<le> g` n Pair KStoptr Storage STArray n2 p2 have "gas st'' \<le> gas st'" using g_def by simp
                          moreover from 37(2) `\<not> gas st \<le> g` n Pair have "gas st' \<le> gas st" using g_def by simp
                          ultimately show ?thesis by simp
                        qed
                      qed
                    qed
                  qed
                next
                  case (e x)
                  with 37(1) stmt_def `\<not> gas st \<le> g` n Pair KStoptr Storage STArray show ?thesis using stmt.psimps(2) g_def by simp
                qed
              next
                case (STMap t t')
                then show ?thesis
                proof (cases "lexp lv e\<^sub>p env cd st'")
                  case n2: (n a st'')
                  then show ?thesis
                  proof (cases a)
                    case p2: (Pair a b)
                    then show ?thesis
                    proof (cases a)
                      case (LStackloc l)
                      with 37(1) `\<not> gas st \<le> g` n Pair KStoptr Storage STMap n2 p2
                      have "stmt (ASSIGN lv ex) e\<^sub>p env cd st = Normal ((), st'' \<lparr>stack := updateStore l (KStoptr p) (stack st'')\<rparr>)"
                        using stmt.psimps(2) g_def by simp
                      with stmt_def have "st6'= st''\<lparr>stack := updateStore l (KStoptr p) (stack st'')\<rparr>" by simp
                      moreover from 37(7) `\<not> gas st \<le> g` n Pair KStoptr Storage STMap n2 p2 have "gas st'' \<le> gas st'" using g_def by simp
                      moreover from 37(2) `\<not> gas st \<le> g` n Pair have "gas st' \<le> gas st" using g_def by simp
                      ultimately show ?thesis by simp
                    next
                      case (LMemloc x2)
                      with 37(1) stmt_def `\<not> gas st \<le> g` n Pair KStoptr Storage STMap n2 p2 show ?thesis using stmt.psimps(2) g_def by simp
                    next
                      case (LStoreloc x3)
                      with 37(1) stmt_def `\<not> gas st \<le> g` n Pair KStoptr Storage STMap n2 p2 show ?thesis using stmt.psimps(2) g_def by simp
                    qed
                  qed
                next
                  case (e x)
                  with 37(1) stmt_def `\<not> gas st \<le> g` n Pair KStoptr Storage STMap show ?thesis using stmt.psimps(2) g_def by simp
                qed
              next
                case (STValue x3)
                with 37(1) stmt_def `\<not> gas st \<le> g` n Pair KStoptr Storage show ?thesis using stmt.psimps(2) g_def by simp
              qed
            qed
          qed
        qed
      next
        case (e x)
        with 37(1) stmt_def `\<not> gas st \<le> g` show ?thesis using stmt.psimps(2) g_def by (simp split: Ex.split_asm)
      qed
    qed
  qed
next
  case (38 s1 s2 e\<^sub>p e cd st)
  define g where "g = costs (COMP s1 s2) e\<^sub>p e cd st"
  show ?case
  proof (rule allI[OF impI])
    fix st6'
    assume stmt_def: "stmt (COMP s1 s2) e\<^sub>p e cd st = Normal ((), st6')"
    then show "gas st6' \<le> gas st"
    proof cases
      assume "gas st \<le> g"
      with 38 stmt_def g_def show ?thesis using stmt.psimps(3) by simp
    next
      assume "\<not> gas st \<le> g"
      show ?thesis
      proof (cases "stmt s1 e\<^sub>p e cd (st\<lparr>gas := gas st - g\<rparr>)")
        case (n a st')
        with 38(1) stmt_def `\<not> gas st \<le> g` have "stmt (COMP s1 s2) e\<^sub>p e cd st = stmt s2 e\<^sub>p e cd st'" using stmt.psimps(3)[of s1 s2 e\<^sub>p e cd st] g_def by (simp add:Let_def split:unit.split_asm)
        with 38(3)[of _ "(st\<lparr>gas := gas st - g\<rparr>)" _ st'] stmt_def \<open>\<not> gas st \<le> g\<close> n have "gas st6' \<le> gas st'" using g_def by fastforce
        moreover from 38(2) \<open>\<not> gas st \<le> g\<close> n have "gas st' \<le> gas st" using g_def by simp
        ultimately show ?thesis by simp
      next
        case (e x)
        with 38 stmt_def `\<not> gas st \<le> g` show ?thesis using stmt.psimps(3)[of s1 s2 e\<^sub>p e cd st] g_def by (simp split: Ex.split_asm)
      qed
    qed
  qed
next
  case (39 ex s1 s2 e\<^sub>p e cd st)
  define g where "g = costs (ITE ex s1 s2) e\<^sub>p e cd st"
  show ?case
  proof (rule allI[OF impI])
    fix st6'
    assume stmt_def: "stmt (ITE ex s1 s2) e\<^sub>p e cd st = Normal ((), st6')"
    then show "gas st6' \<le> gas st"
    proof cases
      assume "gas st \<le> g"
      with 39 stmt_def show ?thesis using stmt.psimps(4) g_def by simp
    next
      assume "\<not> gas st \<le> g"
      show ?thesis
      proof (cases "expr ex e\<^sub>p e cd (st\<lparr>gas := gas st - g\<rparr>)")
        case (n a st')
        then show ?thesis
        proof (cases a)
          case (Pair b c)
          then show ?thesis
          proof (cases b)
            case (KValue b)
            then show ?thesis
            proof (cases c)
              case (Value x1)
              then show ?thesis
              proof (cases x1)
                case (TSInt x1)
                with 39(1) stmt_def `\<not> gas st \<le> g` n Pair KValue Value show ?thesis using stmt.psimps(4) g_def by simp
              next
                case (TUInt x2)
                with 39(1) stmt_def `\<not> gas st \<le> g` n Pair KValue Value show ?thesis using stmt.psimps(4) g_def by simp
              next
                case TBool
                then show ?thesis
                proof cases
                  assume "b = ShowL\<^sub>b\<^sub>o\<^sub>o\<^sub>l True"
                  with 39(1) `\<not> gas st \<le> g` n Pair KValue Value TBool have "stmt (ITE ex s1 s2) e\<^sub>p e cd st = stmt s1 e\<^sub>p e cd st'" using stmt.psimps(4) g_def by simp
                  with 39(3) stmt_def `\<not> gas st \<le> g` n Pair KValue Value TBool `b = ShowL\<^sub>b\<^sub>o\<^sub>o\<^sub>l True` have "gas st6' \<le> gas st'" using g_def by simp
                  moreover from 39(2) `\<not> gas st \<le> g` n Pair have "gas st' \<le> gas st" using g_def by simp
                  ultimately show ?thesis by arith
                next
                  assume "\<not> b = ShowL\<^sub>b\<^sub>o\<^sub>o\<^sub>l True"
                  with 39(1) `\<not> gas st \<le> g` n Pair KValue Value TBool have "stmt (ITE ex s1 s2) e\<^sub>p e cd st = stmt s2 e\<^sub>p e cd st'" using stmt.psimps(4) g_def by simp
                  with 39(4) stmt_def `\<not> gas st \<le> g` n Pair KValue Value TBool `\<not> b = ShowL\<^sub>b\<^sub>o\<^sub>o\<^sub>l True` have "gas st6' \<le> gas st'" using g_def by simp
                  moreover from 39(2) `\<not> gas st \<le> g` n Pair have "gas st' \<le> gas st" using g_def by simp
                  ultimately show ?thesis by arith
                qed
              next
                case TAddr
                with 39(1) stmt_def `\<not> gas st \<le> g` n Pair KValue Value show ?thesis using stmt.psimps(4) g_def by simp
              qed
            next
              case (Calldata x2)
              with 39(1) stmt_def `\<not> gas st \<le> g` n Pair KValue show ?thesis using stmt.psimps(4) g_def by simp
            next
              case (Memory x3)
              with 39(1) stmt_def `\<not> gas st \<le> g` n Pair KValue show ?thesis using stmt.psimps(4) g_def by simp
            next
              case (Storage x4)
              with 39(1) stmt_def `\<not> gas st \<le> g` n Pair KValue show ?thesis using stmt.psimps(4) g_def by simp
            qed
          next
            case (KCDptr x2)
            with 39(1) stmt_def `\<not> gas st \<le> g` n Pair show ?thesis using stmt.psimps(4) g_def by simp
          next
            case (KMemptr x3)
            with 39(1) stmt_def `\<not> gas st \<le> g` n Pair show ?thesis using stmt.psimps(4) g_def by simp
          next
            case (KStoptr x4)
            with 39(1) stmt_def `\<not> gas st \<le> g` n Pair show ?thesis using stmt.psimps(4) g_def by simp
          qed
        qed
      next
        case (e e)
        with 39(1) stmt_def `\<not> gas st \<le> g` show ?thesis using stmt.psimps(4) g_def by simp
      qed
    qed
  qed
next
  case (40 ex s0 e\<^sub>p e cd st)
  define g where "g = costs (WHILE ex s0) e\<^sub>p e cd st"
  show ?case
  proof (rule allI[OF impI])
    fix st6'
    assume stmt_def: "stmt (WHILE ex s0) e\<^sub>p e cd st = Normal ((), st6')"
    then show "gas st6' \<le> gas st"
    proof cases
      assume "gas st \<le> costs (WHILE ex s0) e\<^sub>p e cd st"
      with 40(1) stmt_def show ?thesis using stmt.psimps(5) by simp
    next
      assume gcost: "\<not> gas st \<le> costs (WHILE ex s0) e\<^sub>p e cd st"
      show ?thesis
      proof (cases "expr ex e\<^sub>p e cd (st\<lparr>gas := gas st - g\<rparr>)")
        case (n a st')
        then show ?thesis
        proof (cases a)
          case (Pair b c)
          then show ?thesis
          proof (cases b)
            case (KValue b)
            then show ?thesis
            proof (cases c)
              case (Value x1)
              then show ?thesis
              proof (cases x1)
                case (TSInt x1)
                with 40(1) stmt_def gcost n Pair KValue Value show ?thesis using stmt.psimps(5) g_def by simp
              next
                case (TUInt x2)
                with 40(1) stmt_def gcost n Pair KValue Value show ?thesis using stmt.psimps(5) g_def by simp
              next
                case TBool
                then show ?thesis
                proof cases
                  assume "b = ShowL\<^sub>b\<^sub>o\<^sub>o\<^sub>l True"
                  then show ?thesis
                  proof (cases "stmt s0 e\<^sub>p e cd st'")
                    case n2: (n a st'')
                    with 40(1) gcost n Pair KValue Value TBool `b = ShowL\<^sub>b\<^sub>o\<^sub>o\<^sub>l True` have "stmt (WHILE ex s0) e\<^sub>p e cd st = stmt (WHILE ex s0) e\<^sub>p e cd st''" using stmt.psimps(5)[of ex s0 e\<^sub>p e cd st] g_def by (simp add: Let_def split:unit.split_asm)
                    with 40(4) stmt_def gcost n2 Pair KValue Value TBool `b = ShowL\<^sub>b\<^sub>o\<^sub>o\<^sub>l True` n have "gas st6' \<le> gas st''" using g_def by simp
                    moreover from 40(3) gcost n2 Pair KValue Value TBool `b = ShowL\<^sub>b\<^sub>o\<^sub>o\<^sub>l True` n have "gas st'' \<le> gas st'" using g_def by simp
                    moreover from 40(2)[of _ "st\<lparr>gas := gas st - g\<rparr>"] gcost n Pair have "gas st' \<le> gas st" using g_def by simp
                    ultimately show ?thesis by simp
                  next
                    case (e x)
                    with 40(1) stmt_def gcost n Pair KValue Value TBool `b = ShowL\<^sub>b\<^sub>o\<^sub>o\<^sub>l True` show ?thesis using stmt.psimps(5) g_def by (simp split: Ex.split_asm)
                  qed
                next
                  assume "\<not> b = ShowL\<^sub>b\<^sub>o\<^sub>o\<^sub>l True"
                  with 40(1) gcost n Pair KValue Value TBool have "stmt (WHILE ex s0) e\<^sub>p e cd st = return () st'" using stmt.psimps(5) g_def by simp
                  with stmt_def have "gas st6' \<le> gas st'" by simp
                  moreover from 40(2)[of _ "st\<lparr>gas := gas st - g\<rparr>"] gcost n have "gas st' \<le> gas st" using g_def by simp
                  ultimately show ?thesis by simp
                qed
              next
                case TAddr
                with 40(1) stmt_def gcost n Pair KValue Value show ?thesis using stmt.psimps(5) g_def by simp
              qed
            next
              case (Calldata x2)
              with 40(1) stmt_def gcost n Pair KValue show ?thesis using stmt.psimps(5) g_def by simp
            next
              case (Memory x3)
              with 40(1) stmt_def gcost n Pair KValue show ?thesis using stmt.psimps(5) g_def by simp
            next
              case (Storage x4)
              with 40(1) stmt_def gcost n Pair KValue show ?thesis using stmt.psimps(5) g_def by simp
            qed
          next
            case (KCDptr x2)
            with 40(1) stmt_def gcost n Pair show ?thesis using stmt.psimps(5) g_def by simp
          next
            case (KMemptr x3)
            with 40(1) stmt_def gcost n Pair show ?thesis using stmt.psimps(5) g_def by simp
          next
            case (KStoptr x4)
            with 40(1) stmt_def gcost n Pair show ?thesis using stmt.psimps(5) g_def by simp
          qed
        qed
      next
        case (e e)
        with 40(1) stmt_def gcost show ?thesis using stmt.psimps(5) g_def by simp
      qed
    qed
  qed
next
  case (41 i xe e\<^sub>p e cd st)
  define g where "g = costs (INVOKE i xe) e\<^sub>p e cd st"
  show ?case
  proof (rule allI[OF impI])
    fix st6' assume a1: "stmt (INVOKE i xe) e\<^sub>p e cd st = Normal ((), st6')"
    show "gas st6' \<le> gas st"
    proof (cases)
      assume "gas st \<le> costs (INVOKE i xe) e\<^sub>p e cd st"
      with 41(1) a1 show ?thesis using stmt.psimps(6) by simp
    next
      assume gcost: "\<not> gas st \<le> costs (INVOKE i xe) e\<^sub>p e cd st"
      then show ?thesis
      proof (cases "fmlookup e\<^sub>p (address e)")
        case None
        with 41(1) a1 gcost show ?thesis using stmt.psimps(6) by simp
      next
        case (Some x)
        then show ?thesis
        proof (cases x)
          case (Pair ct _)
          then show ?thesis
          proof (cases "fmlookup ct i")
            case None
            with 41(1) g_def a1 gcost Some Pair show ?thesis using stmt.psimps(6) by simp
          next
            case s1: (Some a)
            then show ?thesis
            proof (cases a)
              case (Method x1)
              then show ?thesis
              proof (cases x1)
                case (fields fp f c)
                then show ?thesis
                proof (cases c)
                  case None
                  define st' e'
                    where "st' = st\<lparr>gas := gas st - g\<rparr>\<lparr>stack:=emptyStore\<rparr>"
                      and "e' = ffold (init ct) (emptyEnv (address e) (sender e) (svalue e)) (fmdom ct)"
                  then show ?thesis
                  proof (cases "load False fp xe e\<^sub>p e' emptyStore st' e cd (st\<lparr>gas := gas st - g\<rparr>)")
                    case s3: (n a st''')
                    then show ?thesis
                    proof (cases a)
                      case f1: (fields e'' cd' st'')
                      then show ?thesis
                      proof (cases "stmt f e\<^sub>p e'' cd' st''")
                        case n2: (n a st'''')
                        with 41(1) g_def a1 gcost Some Pair s1 Method fields None st'_def e'_def s3 f1
                        have "stmt (INVOKE i xe) e\<^sub>p e cd st = Normal ((), st''''\<lparr>stack:=stack st''', memory := memory st'''\<rparr>)" and *: "gas st' \<le> gas (st\<lparr>gas := gas st - g\<rparr>)"
                          using stmt.psimps(6)[of i xe e\<^sub>p e cd st] by (auto simp add:Let_def split:unit.split_asm)
                        with a1 have "gas st6' \<le> gas st''''" by auto
                        also from 41(3) gcost g_def Some Pair s1 Method fields None st'_def e'_def s3 f1 n2
                          have "\<dots> \<le> gas st''" by (auto split:unit.split_asm)
                        also have "\<dots> \<le> gas st'"
                          proof -
                            from g_def gcost have "(applyf (costs (INVOKE i xe) e\<^sub>p e cd) \<bind> (\<lambda>g. assert Gas (\<lambda>st. gas st \<le> g) (modify (\<lambda>st. st\<lparr>gas := gas st - g\<rparr>)))) st = Normal ((), st\<lparr>gas := gas st - g\<rparr>)" by simp
                            moreover from e'_def have "e' = ffold_init ct (emptyEnv (address e) (sender e) (svalue e)) (fmdom ct)" by simp
                            moreover from st'_def have "applyf (\<lambda>st. st\<lparr>stack := emptyStore\<rparr>) (st\<lparr>gas := gas st - g\<rparr>) = Normal (st', st\<lparr>gas := gas st - g\<rparr>)" by simp
                            ultimately have "\<forall>ev cda sta st'a. load False fp xe e\<^sub>p e' emptyStore st' e cd (st\<lparr>gas := gas st - g\<rparr>) = Normal ((ev, cda, sta), st'a) \<longrightarrow> gas sta \<le> gas st' \<and> gas st'a \<le> gas (st\<lparr>gas := gas st - g\<rparr>) \<and> address ev = address e'" using a1 g_def gcost Some Pair s1 Method fields None st'_def e'_def s3 f1 41(2)[of _ "st\<lparr>gas := gas st - g\<rparr>" x ct _ _ x1 fp _ f c e' st' "st\<lparr>gas := gas st - g\<rparr>"] by blast
                            then show ?thesis using s3 f1 by auto
                          qed
                        also from * have "\<dots> \<le> gas (st\<lparr>gas := gas st - g\<rparr>)" .
                        finally show ?thesis by simp
                      next
                        case (e x)
                        with 41(1) g_def a1 gcost Some Pair s1 Method fields None st'_def e'_def s3 f1 show ?thesis using stmt.psimps(6)[of i xe e\<^sub>p e cd st] by auto
                      qed
                    qed
                  next
                    case n2: (e x)
                    with 41(1) g_def a1 gcost Some Pair s1 Method fields None st'_def e'_def show ?thesis using stmt.psimps(6) by auto
                  qed
                next
                  case s2: (Some a)
                  with 41(1) g_def a1 gcost Some Pair s1 Method fields show ?thesis using stmt.psimps(6) by simp
                qed
              qed
            next
              case (Var x2)
              with 41(1) g_def a1 gcost Some Pair s1 show ?thesis using stmt.psimps(6) by simp
            qed
          qed
        qed
      qed
    qed
  qed
next
  case (42 ad i xe val e\<^sub>p e cd st)
  define g where "g = costs (EXTERNAL ad i xe val) e\<^sub>p e cd st"
  show ?case
  proof (rule allI[OF impI])
    fix st6' assume a1: "stmt (EXTERNAL ad i xe val) e\<^sub>p e cd st = Normal ((), st6')"
    show "gas st6' \<le> gas st"
    proof (cases)
      assume "gas st \<le> costs (EXTERNAL ad i xe val) e\<^sub>p e cd st"
      with 42(1) a1 show ?thesis using stmt.psimps(7) by simp
    next
      assume gcost: "\<not> gas st \<le> costs (EXTERNAL ad i xe val) e\<^sub>p e cd st"
      then show ?thesis
      proof (cases "expr ad e\<^sub>p e cd (st\<lparr>gas := gas st - g\<rparr>)")
        case (n a st')
        then show ?thesis
        proof (cases a)
          case (Pair b c)
          then show ?thesis
          proof (cases b)
            case (KValue adv)
            then show ?thesis
            proof (cases c)
              case (Value x1)
              then show ?thesis
              proof (cases x1)
                case (TSInt x1)
                with 42(1) g_def a1 gcost n Pair KValue Value show ?thesis using stmt.psimps(7) by auto
              next
                case (TUInt x2)
                with 42(1) g_def a1 gcost n Pair KValue Value show ?thesis using stmt.psimps(7) by simp
              next
                case TBool
                with 42(1) g_def a1 gcost n Pair KValue Value show ?thesis using stmt.psimps(7) by simp
              next
                case TAddr
                then show ?thesis
                proof (cases "fmlookup e\<^sub>p adv")
                  case None
                  with 42(1) g_def a1 gcost n Pair KValue Value TAddr show ?thesis using stmt.psimps(7) by simp
                next
                  case (Some x)
                  then show ?thesis
                  proof (cases x)
                    case p2: (Pair ct fb)
                    then show ?thesis
                    proof (cases "expr val e\<^sub>p e cd st'")
                      case n1: (n kv st'')
                      then show ?thesis
                      proof (cases kv)
                        case p3: (Pair a b)
                        then show ?thesis
                        proof (cases a)
                          case k2: (KValue v)
                          then show ?thesis
                          proof (cases b)
                            case v: (Value t)
                            show ?thesis
                            proof (cases "fmlookup ct i")
                              case None
                              show ?thesis
                              proof (cases "transfer (address e) adv v (accounts st'')")
                                case n2: None
                                with 42(1) g_def a1 gcost n Pair KValue Value TAddr Some p2 None n1 p3 k2 v show ?thesis using stmt.psimps(7)[of ad i xe val e\<^sub>p e cd st] by simp
                              next
                                case s4: (Some acc)
                                show ?thesis
                                proof (cases "stmt fb e\<^sub>p (emptyEnv adv (address e) v) cd (st''\<lparr>accounts := acc,stack:=emptyStore, memory:=emptyStore\<rparr>)")
                                  case n2: (n a st''')
                                  with 42(1) g_def a1 gcost n Pair KValue Value TAddr Some p2 None n1 p3 k2 v s4
                                  have "stmt (EXTERNAL ad i xe val) e\<^sub>p e cd st = Normal ((), st'''\<lparr>stack:=stack st'', memory := memory st''\<rparr>)"
                                    using stmt.psimps(7)[of ad i xe val e\<^sub>p e cd st] by (auto simp add:Let_def split:unit.split_asm)
                                  with a1 have "gas st6' \<le> gas st'''" by auto
                                  also from 42(6)[OF _ n Pair KValue Value TAddr Some p2 n1 p3 k2 v None _ s4, of _ st'' st'' st'' "()"] n2 g_def gcost
                                    have "\<dots> \<le> gas (st''\<lparr>accounts := acc,stack:=emptyStore, memory:=emptyStore\<rparr>)" by auto
                                  also from 42(3)[of _ "st\<lparr>gas := gas st - g\<rparr>" _ st' _ _ adv _ x ct] g_def a1 gcost n Pair KValue Value TAddr Some p2 None n1 p3 k2 v s4 n2
                                    have "\<dots> \<le> gas st'" by auto
                                  also from 42(2)[of _ "st\<lparr>gas := gas st - g\<rparr>"] g_def a1 gcost n Pair KValue Value TAddr Some p2 None n1 p3 k2 v s4 n2
                                    have "\<dots> \<le> gas (st\<lparr>gas := gas st - g\<rparr>)" by auto
                                  finally show ?thesis by simp
                                next
                                  case (e x)
                                  with 42(1) g_def a1 gcost n Pair KValue Value TAddr Some p2 None n1 p3 k2 v s4 show ?thesis using stmt.psimps(7)[of ad i xe val e\<^sub>p e cd st] by simp
                                qed
                              qed
                            next
                              case s1: (Some a)
                              then show ?thesis
                              proof (cases a)
                                case (Method x1)
                                then show ?thesis
                                proof (cases x1)
                                  case (fields fp f c)
                                  then show ?thesis
                                  proof (cases c)
                                    case None
                                    define stl e'
                                    where "stl = st''\<lparr>stack:=emptyStore, memory:=emptyStore\<rparr>"
                                      and "e' = ffold (init ct) (emptyEnv adv (address e) v) (fmdom ct)"
                                    then show ?thesis
                                    proof (cases "load True fp xe e\<^sub>p e' emptyStore stl e cd st''")
                                      case s3: (n a st''')
                                      then show ?thesis
                                      proof (cases a)
                                        case f1: (fields e'' cd' st'''')
                                        show ?thesis
                                        proof (cases "transfer (address e) adv v (accounts st'''')")
                                          case n2: None
                                          with 42(1) g_def a1 gcost n Pair KValue Value TAddr Some p2 s1 Method fields None n1 p3 k2 v s3 f1 stl_def e'_def show ?thesis using stmt.psimps(7)[of ad i xe val e\<^sub>p e cd st] by simp
                                        next
                                          case s4: (Some acc)
                                          show ?thesis
                                          proof (cases "stmt f e\<^sub>p e'' cd' (st''''\<lparr>accounts := acc\<rparr>)")
                                            case n2: (n a st''''')
                                            with 42(1) g_def a1 gcost n Pair KValue Value TAddr Some p2 s1 Method fields None n1 p3 k2 v stl_def e'_def s3 f1 s4
                                            have "stmt (EXTERNAL ad i xe val) e\<^sub>p e cd st = Normal ((), st'''''\<lparr>stack:=stack st''', memory := memory st'''\<rparr>)"
                                              using stmt.psimps(7)[of ad i xe val e\<^sub>p e cd st] by (auto simp add:Let_def split:unit.split_asm)
                                            with a1 have "gas st6' \<le> gas (st''''')" by auto
                                            also from 42(5)[OF _ n Pair KValue Value TAddr Some p2 n1 p3 k2 v s1 Method fields _ None _ _ s3 _ _ _ _, of "()" f e'' "(cd', st'''')" cd' st'''' st''' st''' acc "()" "st''''\<lparr>accounts := acc\<rparr>"] s4 stl_def e'_def f1 n2 g_def gcost
                                              have "\<dots> \<le> gas (st''''\<lparr>accounts := acc\<rparr>)" by auto
                                            also have "\<dots> \<le> gas stl"
                                            proof -
                                              from g_def gcost have "(applyf (costs (EXTERNAL ad i xe val) e\<^sub>p e cd) \<bind> (\<lambda>g. assert Gas (\<lambda>st. gas st \<le> g) (modify (\<lambda>st. st\<lparr>gas := gas st - g\<rparr>)))) st = Normal ((), st\<lparr>gas := gas st - g\<rparr>)" by simp
                                              moreover from e'_def have "e' = ffold_init ct (emptyEnv adv (address e) v) (fmdom ct)" by simp
                                              moreover from n1 have "expr val e\<^sub>p e cd st' = Normal (kv, st'')" by simp
                                              moreover from stl_def have "applyf (\<lambda>st. st\<lparr>stack := emptyStore, memory := emptyStore\<rparr>) st'' = Normal (stl, st'')" by simp
                                              moreover have "applyf accounts st'' = Normal ((accounts st''), st'')" by simp
                                              ultimately have "\<forall>ev cda sta st'a. load True fp xe e\<^sub>p e' emptyStore stl e cd st'' = Normal ((ev, cda, sta), st'a) \<longrightarrow> gas sta \<le> gas stl \<and> gas st'a \<le> gas st'' \<and> address ev = address e'" using 42(4)[of _ "st\<lparr>gas := gas st - g\<rparr>" _ st' _ _ adv _ x ct _ _ st'' _ b v t _ x1 fp "(f,c)" f c e'] g_def a1 gcost n Pair KValue Value TAddr Some p2 s1 Method fields None n1 p3 k2 v stl_def e'_def s3 f1 s4 n2 by blast
                                              then show ?thesis using s3 f1 by auto
                                            qed
                                            also from stl_def have "\<dots> \<le> gas st''" by simp
                                            also from 42(3)[of _ "st\<lparr>gas := gas st - g\<rparr>" _ st' _ _ adv _ x ct] g_def a1 gcost n Pair KValue Value TAddr Some p2 s1 Method fields None n1 p3 k2 v stl_def e'_def s3 f1 s4 n2
                                              have "\<dots> \<le> gas st'" by auto
                                            also from 42(2)[of _ "st\<lparr>gas := gas st - g\<rparr>"] g_def a1 gcost n Pair KValue Value TAddr Some p2 s1 Method fields None n1 p3 k2 v stl_def e'_def s3 f1 s4 n2
                                              have "\<dots> \<le> gas (st\<lparr>gas := gas st - g\<rparr>)" by auto
                                            finally show ?thesis by simp
                                          next
                                            case (e x)
                                            with 42(1) g_def a1 gcost n Pair KValue Value TAddr Some p2 s1 Method fields None n1 p3 k2 v stl_def e'_def s3 f1 s4 show ?thesis using stmt.psimps(7)[of ad i xe val e\<^sub>p e cd st] by simp
                                          qed
                                        qed
                                      qed
                                    next
                                      case (e x)
                                      with 42(1) g_def a1 gcost n Pair KValue Value TAddr Some p2 s1 Method fields None n1 p3 k2 v stl_def e'_def show ?thesis using stmt.psimps(7)[of ad i xe val e\<^sub>p e cd st] by simp
                                    qed
                                  next
                                    case s2: (Some a)
                                    with 42(1) g_def a1 gcost n Pair KValue Value TAddr Some p2 s1 Method fields n1 p3 k2 v show ?thesis using stmt.psimps(7)[of ad i xe val e\<^sub>p e cd st] by simp
                                  qed
                                qed
                              next
                                case (Var x2)
                                with 42(1) g_def a1 gcost n Pair KValue Value TAddr Some p2 s1 n1 p3 k2 v show ?thesis using stmt.psimps(7)[of ad i xe val e\<^sub>p e cd st] by simp
                              qed
                            qed
                          next
                            case (Calldata x2)
                            with 42(1) g_def a1 gcost n Pair KValue Value TAddr Some p2 n1 p3 k2 show ?thesis using stmt.psimps(7)[of ad i xe val e\<^sub>p e cd st] by simp
                          next
                            case (Memory x3)
                            with 42(1) g_def a1 gcost n Pair KValue Value TAddr Some p2 n1 p3 k2 show ?thesis using stmt.psimps(7)[of ad i xe val e\<^sub>p e cd st] by simp
                          next
                            case (Storage x4)
                            with 42(1) g_def a1 gcost n Pair KValue Value TAddr Some p2 n1 p3 k2 show ?thesis using stmt.psimps(7)[of ad i xe val e\<^sub>p e cd st] by simp
                          qed
                        next
                          case (KCDptr x2)
                          with 42(1) g_def a1 gcost n Pair KValue Value TAddr Some p2 n1 p3 show ?thesis using stmt.psimps(7)[of ad i xe val e\<^sub>p e cd st] by simp
                        next
                          case (KMemptr x3)
                          with 42(1) g_def a1 gcost n Pair KValue Value TAddr Some p2 n1 p3 show ?thesis using stmt.psimps(7)[of ad i xe val e\<^sub>p e cd st] by simp
                        next
                          case (KStoptr x4)
                          with 42(1) g_def a1 gcost n Pair KValue Value TAddr Some p2 n1 p3 show ?thesis using stmt.psimps(7)[of ad i xe val e\<^sub>p e cd st] by simp
                        qed
                      qed
                    next
                      case n2: (e x)
                      with 42(1) g_def a1 gcost n Pair KValue Value TAddr Some p2 show ?thesis using stmt.psimps(7)[of ad i xe val e\<^sub>p e cd st] by simp
                    qed
                  qed
                qed
              qed
            next
              case (Calldata x2)
              with 42(1) g_def a1 gcost n Pair KValue show ?thesis using stmt.psimps(7)[of ad i xe val e\<^sub>p e cd st] by simp
            next
              case (Memory x3)
              with 42(1) g_def a1 gcost n Pair KValue show ?thesis using stmt.psimps(7)[of ad i xe val e\<^sub>p e cd st] by simp
            next
              case (Storage x4)
              with 42(1) g_def a1 gcost n Pair KValue show ?thesis using stmt.psimps(7)[of ad i xe val e\<^sub>p e cd st] by simp
            qed
          next
            case (KCDptr x2)
            with 42(1) g_def a1 gcost n Pair show ?thesis using stmt.psimps(7)[of ad i xe val e\<^sub>p e cd st] by simp
          next
            case (KMemptr x3)
            with 42(1) g_def a1 gcost n Pair show ?thesis using stmt.psimps(7)[of ad i xe val e\<^sub>p e cd st] by simp
          next
            case (KStoptr x4)
            with 42(1) g_def a1 gcost n Pair show ?thesis using stmt.psimps(7)[of ad i xe val e\<^sub>p e cd st] by simp
          qed
        qed
      next
        case (e _)
        with 42(1) g_def a1 gcost show ?thesis using stmt.psimps(7)[of ad i xe val e\<^sub>p e cd st] by simp
      qed
    qed
  qed
next
  case (43 ad ex e\<^sub>p e cd st)
  define g where "g = costs (TRANSFER ad ex) e\<^sub>p e cd st"
  show ?case
  proof (rule allI[OF impI])
    fix st6' assume stmt_def: "stmt (TRANSFER ad ex) e\<^sub>p e cd st = Normal ((), st6')"
    show "gas st6' \<le> gas st"
    proof cases
      assume "gas st \<le> g"
      with 43 stmt_def g_def show ?thesis using stmt.psimps(8)[of ad ex e\<^sub>p e cd st] by simp
    next
      assume "\<not> gas st \<le> g"
      show ?thesis
      proof (cases "expr ex e\<^sub>p e cd (st\<lparr>gas := gas st - g\<rparr>)")
        case (n a st')
        then show ?thesis
        proof (cases a)
          case (Pair b c)
          then show ?thesis
          proof (cases b)
            case (KValue v)
            then show ?thesis
            proof (cases c)
              case (Value t)
              then show ?thesis
              proof (cases "expr ad e\<^sub>p e cd st'")
                case n2: (n a st'')
                then show ?thesis
                proof (cases a)
                  case p2: (Pair b c)
                  then show ?thesis
                  proof (cases b)
                    case k2: (KValue adv)
                    then show ?thesis
                    proof (cases c)
                      case v2: (Value x1)
                      then show ?thesis
                      proof (cases x1)
                        case (TSInt x1)
                        with 43(1) stmt_def `\<not> gas st \<le> g` n Pair KValue Value n2 p2 k2 v2 g_def show ?thesis using stmt.psimps(8) by simp
                      next
                        case (TUInt x2)
                        with 43(1) stmt_def `\<not> gas st \<le> g` n Pair KValue Value n2 p2 k2 v2 g_def show ?thesis using stmt.psimps(8) by simp
                      next
                        case TBool
                        with 43(1) stmt_def `\<not> gas st \<le> g` n Pair KValue Value n2 p2 k2 v2 g_def show ?thesis using stmt.psimps(8) by simp
                      next
                        case TAddr
                        then show ?thesis
                        proof (cases "transfer (address e) adv v (accounts st'')")
                          case None
                          with 43(1) stmt_def g_def `\<not> gas st \<le> g` n Pair KValue Value n2 p2 k2 v2 TAddr show ?thesis using stmt.psimps(8) by simp
                        next
                          case (Some acc)
                          then show ?thesis
                          proof (cases "fmlookup e\<^sub>p adv")
                            case None
                            with 43(1) `\<not> gas st \<le> g` n Pair KValue Value n2 p2 k2 v2 TAddr Some g_def
                            have "stmt (TRANSFER ad ex) e\<^sub>p e cd st = Normal ((),st''\<lparr>accounts:=acc\<rparr>)" using stmt.psimps(8)[of ad ex e\<^sub>p e cd st] by simp
                            with stmt_def have "gas st6' \<le> gas st''" by auto
                            also from 43(3)[of "()" "(st\<lparr>gas := gas st - g\<rparr>)" _ st'] `\<not> gas st \<le> g` n Pair KValue Value n2 g_def have "\<dots> \<le> gas st'" by simp
                            also from 43(2)[of "()" "(st\<lparr>gas := gas st - g\<rparr>)"] `\<not> gas st \<le> g` n g_def have "\<dots> \<le> gas st" by simp
                            finally show ?thesis .
                          next
                            case s2: (Some a)
                            then show ?thesis
                            proof (cases a)
                              case p3: (Pair ct f)
                              define e' where "e' = ffold_init ct (emptyEnv adv (address e) v) (fmdom ct)"
                              show ?thesis
                              proof (cases "stmt f e\<^sub>p e' emptyStore (st''\<lparr>accounts := acc, stack:=emptyStore, memory:=emptyStore\<rparr>)")
                                case n3: (n a st''')
                                with 43(1) `\<not> gas st \<le> g` n Pair KValue Value n2 p2 k2 v2 TAddr Some s2 p3 g_def
                                have "stmt (TRANSFER ad ex) e\<^sub>p e cd st = Normal ((),st'''\<lparr>stack:=stack st'', memory := memory st''\<rparr>)" using e'_def stmt.psimps(8)[of ad ex e\<^sub>p e cd st] by simp
                                with stmt_def have "gas st6' \<le> gas st'''" by auto
                                also from 43(4)[of "()" "st\<lparr>gas := gas st - g\<rparr>" _ st' _ _ v t _ st'' _ _ adv x1 "accounts st''" st'' acc _ ct f e' _ st'' "()" "st''\<lparr>accounts := acc, stack:=emptyStore, memory:=emptyStore\<rparr>"] `\<not> gas st \<le> g` n Pair KValue Value n2 p2 k2 v2 TAddr Some s2 p3 g_def n2 e'_def n3
                                  have "\<dots> \<le> gas (st''\<lparr>accounts := acc, stack := emptyStore, memory := emptyStore\<rparr>)" by simp
                                also from 43(3)[of "()" "(st\<lparr>gas := gas st - g\<rparr>)" _ st'] `\<not> gas st \<le> g` n Pair KValue Value n2 g_def have "\<dots> \<le> gas st'" by simp
                                also from 43(2)[of "()" "(st\<lparr>gas := gas st - g\<rparr>)"] `\<not> gas st \<le> g` n g_def have "\<dots> \<le> gas st" by simp
                                finally show ?thesis .
                              next
                                case (e x)
                                with 43(1) `\<not> gas st \<le> g` n Pair KValue Value n2 p2 k2 v2 TAddr Some s2 p3 g_def e'_def stmt_def show ?thesis using stmt.psimps(8)[of ad ex e\<^sub>p e cd st] by simp
                              qed
                            qed
                          qed
                        qed
                      qed
                    next
                      case (Calldata x2)
                      with 43(1) stmt_def `\<not> gas st \<le> g` n Pair KValue Value n2 p2 k2 g_def show ?thesis using stmt.psimps(8) by simp
                    next
                      case (Memory x3)
                      with 43(1) stmt_def `\<not> gas st \<le> g` n Pair KValue Value n2 p2 k2 g_def show ?thesis using stmt.psimps(8) by simp
                    next
                      case (Storage x4)
                      with 43(1) stmt_def `\<not> gas st \<le> g` n Pair KValue Value n2 p2 k2 g_def show ?thesis using stmt.psimps(8) by simp
                    qed
                  next
                    case (KCDptr x2)
                    with 43(1) stmt_def `\<not> gas st \<le> g` n Pair KValue Value n2 p2 g_def show ?thesis using stmt.psimps(8) by simp
                  next
                    case (KMemptr x3)
                    with 43(1) stmt_def `\<not> gas st \<le> g` n Pair KValue Value n2 p2 g_def show ?thesis using stmt.psimps(8) by simp
                  next
                    case (KStoptr x4)
                    with 43(1) stmt_def `\<not> gas st \<le> g` n Pair KValue Value n2 p2 g_def show ?thesis using stmt.psimps(8) by simp
                  qed
                qed
              next
                case (e e)
                with 43(1) stmt_def `\<not> gas st \<le> g` n Pair KValue Value g_def show ?thesis using stmt.psimps(8) by simp
              qed
            next
              case (Calldata x2)
              with 43(1) stmt_def `\<not> gas st \<le> g` n Pair KValue g_def show ?thesis using stmt.psimps(8) by simp
            next
              case (Memory x3)
              with 43(1) stmt_def `\<not> gas st \<le> g` n Pair KValue g_def show ?thesis using stmt.psimps(8) by simp
            next
              case (Storage x4)
              with 43(1) stmt_def `\<not> gas st \<le> g` n Pair KValue g_def show ?thesis using stmt.psimps(8) by simp
            qed
          next
            case (KCDptr x2)
            with 43(1) stmt_def `\<not> gas st \<le> g` n Pair g_def show ?thesis using stmt.psimps(8) by simp
          next
            case (KMemptr x3)
            with 43(1) stmt_def `\<not> gas st \<le> g` n Pair g_def show ?thesis using stmt.psimps(8) by simp
          next
            case (KStoptr x4)
            with 43(1) stmt_def `\<not> gas st \<le> g` n Pair g_def show ?thesis using stmt.psimps(8) by simp
          qed
        qed
      next
        case (e e)
        with 43(1) stmt_def `\<not> gas st \<le> g` g_def show ?thesis using stmt.psimps(8) by simp
      qed
    qed
  qed
next
  case (44 id0 tp ex s e\<^sub>p e\<^sub>v cd st)
  define g where "g = costs (BLOCK ((id0, tp), ex) s) e\<^sub>p e\<^sub>v cd st"
  show ?case
  proof (rule allI[OF impI])
    fix st6' assume stmt_def: "stmt (BLOCK ((id0, tp), ex) s) e\<^sub>p e\<^sub>v cd st = Normal ((), st6')"
    show "gas st6' \<le> gas st"
    proof cases
      assume "gas st \<le> g"
      with 44 stmt_def g_def show ?thesis using stmt.psimps(9) by simp
    next
      assume "\<not> gas st \<le> g"
      show ?thesis
      proof (cases ex)
        case None
        then show ?thesis
        proof (cases "decl id0 tp None False cd (memory (st\<lparr>gas := gas st - g\<rparr>)) cd e\<^sub>v (st\<lparr>gas := gas st - g\<rparr>)")
          case (n a st')
          then show ?thesis
          proof (cases a)
            case (Pair cd' e')
            with 44(1) stmt_def `\<not> gas st \<le> g` None n g_def have "stmt (BLOCK ((id0, tp), ex) s) e\<^sub>p e\<^sub>v cd st = stmt s e\<^sub>p e' cd' st'" using stmt.psimps(9)[of id0 tp ex s e\<^sub>p e\<^sub>v cd st] by (simp split:unit.split_asm)
            with 44(4)[of "()" "st\<lparr>gas := gas st - g\<rparr>"] stmt_def `\<not> gas st \<le> g` None n Pair g_def have "gas st6' \<le> gas st'" by simp
            moreover from n Pair have "gas st' \<le> gas st" using decl_gas_address by simp
            ultimately show ?thesis by simp
          qed
        next
          case (e x)
          with 44 stmt_def `\<not> gas st \<le> g` None g_def show ?thesis using stmt.psimps(9) by simp
        qed
      next
        case (Some ex')
        then show ?thesis
        proof (cases "expr ex' e\<^sub>p e\<^sub>v cd (st\<lparr>gas := gas st - g\<rparr>)")
          case (n a st')
          then show ?thesis
          proof (cases a)
            case (Pair v t)
            then show ?thesis
            proof (cases "decl id0 tp (Some (v, t)) False cd (memory st') cd e\<^sub>v st'")
              case s2: (n a st'')
              then show ?thesis
              proof (cases a)
                case f2: (Pair cd' e')
                with 44(1) stmt_def `\<not> gas st \<le> g` Some n Pair s2 g_def have "stmt (BLOCK ((id0, tp), ex) s) e\<^sub>p e\<^sub>v cd st = stmt s e\<^sub>p e' cd' st''" using stmt.psimps(9)[of id0 tp ex s e\<^sub>p e\<^sub>v cd st] by (simp split:unit.split_asm)
                with 44(3)[of "()" "st\<lparr>gas := gas st - g\<rparr>" ex' _ st'] stmt_def `\<not> gas st \<le> g` Some n Pair s2 f2 g_def have "gas st6' \<le> gas st''" by simp
                moreover from Some n Pair s2 f2 g_def have "gas st'' \<le> gas st'" using decl_gas_address by simp
                moreover from 44(2)[of "()" "st\<lparr>gas := gas st - g\<rparr>" ex'] `\<not> gas st \<le> g` Some n Pair g_def have "gas st' \<le> gas st" by simp
                ultimately show ?thesis by simp
              qed
            next
              case (e x)
              with 44(1) stmt_def `\<not> gas st \<le> g` Some n Pair g_def show ?thesis using stmt.psimps(9) by simp
            qed
          qed
        next
          case (e e)
          with 44 stmt_def `\<not> gas st \<le> g` Some g_def show ?thesis using stmt.psimps(9) by simp
        qed
      qed
    qed
  qed
qed

subsection \<open>Termination\<close>

lemma x1:
  assumes "expr x e\<^sub>p env cd st = Normal (val, s')"
      and "msel_ssel_lexp_expr_load_rexp_stmt_dom (Inr (Inl (Inl (x, e\<^sub>p, env, cd, st))))"
    shows "gas s' < gas st \<or> gas s' = gas st"
  using assms msel_ssel_lexp_expr_load_rexp_stmt_dom_gas(4)[of x e\<^sub>p env cd st] by auto

lemma x2:
assumes "(if gas st \<le> c then throw Gas st else (get \<bind> (\<lambda>s. put (s\<lparr>gas := gas s - c\<rparr>))) st) = Normal ((), s')"
    and "expr x e\<^sub>p e cd s' = Normal (val, s'a)"
    and "msel_ssel_lexp_expr_load_rexp_stmt_dom (Inr (Inl (Inl (x, e\<^sub>p, e, cd, s'))))"
  shows "gas s'a < gas st \<or> gas s'a = gas st"
proof -
  from assms have "gas s' < gas st \<or> gas s' = gas st" by (auto split:if_split_asm)
  with assms show ?thesis using x1[of x e\<^sub>p e cd s' val s'a] by auto
qed

lemma x2sub:
  assumes "(if gas st \<le> costs (TRANSFER ad ex) e\<^sub>p e cd st then throw Gas st
        else (get \<bind> (\<lambda>s. put (s\<lparr>gas := gas s - costs (TRANSFER ad ex) e\<^sub>p e cd st\<rparr>))) st) =
       Normal ((), s')" and 
" expr ex e\<^sub>p e cd s' = Normal ((KValue vb, Value t), s'a)"
and " msel_ssel_lexp_expr_load_rexp_stmt_dom (Inr (Inl (Inl (ex, e\<^sub>p, e, cd, s'))))"
and "(\<And>ad i xe val e\<^sub>p e cd st. 0 < costs (EXTERNAL ad i xe val) e\<^sub>p e cd st)" and "gas s'a \<noteq> gas st" shows "gas s'a < gas st"
proof -
  from assms have "gas s' < gas st \<or> gas s' = gas st" by (auto split:if_split_asm)
  with assms show ?thesis using x1[of ex e\<^sub>p e cd s' "(KValue vb, Value t)" s'a] by auto
qed

lemma x3:
  assumes "(if gas st \<le> c then throw Gas st else (get \<bind> (\<lambda>s. put (s\<lparr>gas := gas s - c\<rparr>))) st) = Normal ((), s')"
      and "s'\<lparr>stack := emptyStore\<rparr> = va"
      and "load False ad xe e\<^sub>p(ffold (init aa) \<lparr>address = address e, sender = sender e, svalue = svalue e, denvalue = fmempty\<rparr> (fmdom aa)) emptyStore va e cd s' = Normal ((ag, ah, s'd), vc)"
      and "msel_ssel_lexp_expr_load_rexp_stmt_dom (Inr (Inl (Inr (False, ad, xe, e\<^sub>p, ffold (init aa) \<lparr>address = address e, sender = sender e, svalue = svalue e, denvalue = fmempty\<rparr> (fmdom aa), emptyStore, va, e, cd, s'))))"
      and "c>0"
    shows "gas s'd < gas st"
proof -
  from assms have "gas s'd \<le> gas va" using msel_ssel_lexp_expr_load_rexp_stmt_dom_gas(5)[of False ad xe e\<^sub>p "ffold (init aa) \<lparr>address = address e, sender = sender e, svalue = svalue e, denvalue = fmempty\<rparr> (fmdom aa)" emptyStore va e cd s'] by blast
  also from assms(2) have "\<dots> = gas s'" by auto
  also from assms(1,5) have "\<dots> < gas st" by (auto split:if_split_asm)
  finally show ?thesis .
qed

lemma x4:
  assumes "(if gas st \<le> c then throw Gas st else (get \<bind> (\<lambda>s. put (s\<lparr>gas := gas s - c\<rparr>))) st) = Normal ((), s')"
      and "s'\<lparr>stack := emptyStore\<rparr> = va"
      and "load False ad xe e\<^sub>p (ffold (init aa) \<lparr>address = address e, sender = sender e, svalue = svalue e, denvalue = fmempty\<rparr> (fmdom aa)) emptyStore va e cd s' =  Normal ((ag, ah, s'd), vc)"
      and "stmt ae e\<^sub>p ag ah s'd = Normal ((), s'e)"
      and "msel_ssel_lexp_expr_load_rexp_stmt_dom (Inr (Inr (Inr (ae, e\<^sub>p, ag, ah, s'd))))"
      and "msel_ssel_lexp_expr_load_rexp_stmt_dom (Inr (Inl (Inr (False, ad, xe, e\<^sub>p, ffold (init aa) \<lparr>address = address e, sender = sender e, svalue = svalue e, denvalue = fmempty\<rparr> (fmdom aa), emptyStore, va, e, cd, s'))))"
      and "c>0"
    shows "gas s'e < gas st"
proof -
  from assms have "gas s'e \<le> gas s'd" using msel_ssel_lexp_expr_load_rexp_stmt_dom_gas(7) by blast
  with assms show ?thesis using x3[OF assms(1) assms(2) assms(3) assms(6)] by simp
qed

lemma x5:
  assumes "(if gas st \<le> costs (COMP s1 s2) e\<^sub>p e cd st then throw Gas st else (get \<bind> (\<lambda>s. put (s\<lparr>gas := gas s - costs (COMP s1 s2) e\<^sub>p e cd st\<rparr>))) st) = Normal ((), s')"
      and "stmt s1 e\<^sub>p e cd s' = Normal ((), s'a)"
      and "msel_ssel_lexp_expr_load_rexp_stmt_dom (Inr (Inr (Inr (s1, e\<^sub>p, e, cd, s'))))"
    shows "gas s'a < gas st \<or> gas s'a = gas st"
    using assms msel_ssel_lexp_expr_load_rexp_stmt_dom_gas(7)[of s1 e\<^sub>p e cd s'] by (auto split:if_split_asm)

lemma x6:
  assumes "(if gas st \<le> costs (WHILE ex s0) e\<^sub>p e cd st then throw Gas st else (get \<bind> (\<lambda>s. put (s\<lparr>gas := gas s - costs (WHILE ex s0) e\<^sub>p e cd st\<rparr>))) st) = Normal ((), s')"
      and "expr ex e\<^sub>p e cd s' = Normal (val, s'a)"
      and "stmt s0 e\<^sub>p e cd s'a = Normal ((), s'b)"
      and "msel_ssel_lexp_expr_load_rexp_stmt_dom (Inr (Inr (Inr (s0, e\<^sub>p, e, cd, s'a))))"
      and "msel_ssel_lexp_expr_load_rexp_stmt_dom (Inr (Inl (Inl (ex, e\<^sub>p, e, cd, s'))))"
    shows "gas s'b < gas st"
proof -
  from assms have "gas s'b \<le> gas s'a" using msel_ssel_lexp_expr_load_rexp_stmt_dom_gas(7)[of s0 e\<^sub>p e cd s'a] by blast
  also from assms have "\<dots> \<le> gas s'" using msel_ssel_lexp_expr_load_rexp_stmt_dom_gas(4)[of ex e\<^sub>p e cd s'] by auto
  also from assms(1) have "\<dots> < gas st" using while_not_zero by (auto split:if_split_asm)
  finally show ?thesis .
qed

lemma x7:
  assumes "(if gas st \<le> c then throw Gas st else (get \<bind> (\<lambda>s. put (s\<lparr>gas := gas s - c\<rparr>))) st) = Normal ((), s')"
      and "expr ad e\<^sub>p e cd s' = Normal ((KValue vb, Value TAddr), s'a)"
      and "expr val e\<^sub>p e cd s'a = Normal ((KValue vd, Value ta), s'b)"
      and "msel_ssel_lexp_expr_load_rexp_stmt_dom (Inr (Inl (Inl (val, e\<^sub>p, e, cd, s'a))))"
      and "msel_ssel_lexp_expr_load_rexp_stmt_dom (Inr (Inl (Inl (ad, e\<^sub>p, e, cd, s'))))"
      and "c>0"
    shows "gas s'b < gas st"
proof -
  from assms(4,3) have "gas s'b \<le> gas s'a" using msel_ssel_lexp_expr_load_rexp_stmt_dom_gas(4)[of val e\<^sub>p e cd s'a] by simp
  also from assms(5,2) have "\<dots> \<le> gas s'" using msel_ssel_lexp_expr_load_rexp_stmt_dom_gas(4)[of ad e\<^sub>p e cd s'] by simp
  also from assms(1,6) have "\<dots> < gas st" by (auto split:if_split_asm)
  finally show ?thesis .
qed

lemma x8:
  assumes "(if gas st \<le> costs (TRANSFER ad ex) e\<^sub>p e cd st then throw Gas st else (get \<bind> (\<lambda>s. put (s\<lparr>gas := gas s - costs (TRANSFER ad ex) e\<^sub>p e cd st\<rparr>))) st) = Normal ((), s')"
      and "expr ex e\<^sub>p e cd s' = Normal ((KValue vb, Value t), s'a)"
      and "expr ad e\<^sub>p e cd s'a = Normal ((KValue vd, Value TAddr), s'b)"
      and "s'b\<lparr>accounts := ab, stack := emptyStore, memory := emptyStore\<rparr> = s'e"
      and "msel_ssel_lexp_expr_load_rexp_stmt_dom (Inr (Inl (Inl (ad, e\<^sub>p, e, cd, s'a))))"
      and "msel_ssel_lexp_expr_load_rexp_stmt_dom (Inr (Inl (Inl (ex, e\<^sub>p, e, cd, s'))))"
    shows "gas s'e < gas st"
proof -
  from assms(4) have "gas s'e = gas s'b" by auto
  also from assms(5,3) have "\<dots> \<le> gas s'a" using msel_ssel_lexp_expr_load_rexp_stmt_dom_gas(4)[of ad e\<^sub>p e cd s'a] by simp
  also from assms(6,2) have "\<dots> \<le> gas s'" using msel_ssel_lexp_expr_load_rexp_stmt_dom_gas(4)[of ex e\<^sub>p e cd s'] by simp
  also from assms(1) have "\<dots> < gas st" using transfer_not_zero by (auto split:if_split_asm)
  finally show ?thesis .
qed

lemma x9:
  assumes "(if gas st \<le> costs (BLOCK ((id0, tp), Some a) s) e\<^sub>p e\<^sub>v cd st then throw Gas st else (get \<bind> (\<lambda>sa. put (sa\<lparr>gas := gas sa - costs (BLOCK ((id0, tp), Some a) s) e\<^sub>p e\<^sub>v cd st\<rparr>))) st) = Normal ((), s')"
      and "expr a e\<^sub>p e\<^sub>v cd s' = Normal ((aa, b), s'a)"
      and "decl id0 tp (Some (aa, b)) False cd vb cd e\<^sub>v s'a = Normal ((ab, ba), s'c)"
      and "msel_ssel_lexp_expr_load_rexp_stmt_dom (Inr (Inl (Inl (a, e\<^sub>p, e\<^sub>v, cd, s'))))"
    shows "gas s'c < gas st \<or> gas s'c = gas st"
proof -
  from assms have "gas s'c = gas s'a" using decl_gas_address[of id0 tp "(Some (aa, b))" False cd vb cd e\<^sub>v s'a] by simp
  also from assms have "\<dots> \<le> gas s'" using msel_ssel_lexp_expr_load_rexp_stmt_dom_gas(4)[of a e\<^sub>p e\<^sub>v cd s'] by simp
  also from assms(1) have "\<dots> \<le> gas st" by (auto split:if_split_asm)
  finally show ?thesis by auto
qed

lemma x10:
  assumes "(if gas st \<le> costs (BLOCK ((id0, tp), None) s) e\<^sub>p e\<^sub>v cd st then throw Gas st else (get \<bind> (\<lambda>sa. put (sa\<lparr>gas := gas sa - costs (BLOCK ((id0, tp), None) s) e\<^sub>p e\<^sub>v cd st\<rparr>))) st) = Normal ((), s')"
      and "decl id0 tp None False cd va cd e\<^sub>v s' = Normal ((a, b), s'b)"
    shows "gas s'b < gas st \<or> gas s'b = gas st"
proof -
  from assms have "gas s'b = gas s'" using decl_gas_address[of id0 tp None False cd va cd e\<^sub>v s'] by simp
  also from assms(1) have "\<dots> \<le> gas st" by (auto split:if_split_asm)
  finally show ?thesis by auto
qed

lemma x11:
  assumes "(if gas st \<le> c then throw Gas st else (get \<bind> (\<lambda>s. put (s\<lparr>gas := gas s - c\<rparr>))) st) = Normal ((), s')"
      and "expr ad e\<^sub>p e cd s' = Normal ((KValue vb, Value TAddr), s'a)"
      and "expr val e\<^sub>p e cd s'a = Normal ((KValue vd, Value ta), s'b)"
      and "load True af xe e\<^sub>p (ffold (init ab) \<lparr>address = vb, sender = address e, svalue = vd, denvalue = fmempty\<rparr> (fmdom ab)) emptyStore (s'b\<lparr>stack := emptyStore, memory := emptyStore\<rparr>) e cd s'b = Normal ((ak, al, s'g), vh)"
      and "msel_ssel_lexp_expr_load_rexp_stmt_dom (Inr (Inl (Inr (True, af, xe, e\<^sub>p, ffold (init ab) \<lparr>address = vb, sender = address e, svalue = vd, denvalue = fmempty\<rparr> (fmdom ab), emptyStore, s'b\<lparr>stack := emptyStore, memory := emptyStore\<rparr>, e, cd, s'b))))"
      and "msel_ssel_lexp_expr_load_rexp_stmt_dom (Inr (Inl (Inl (val, e\<^sub>p, e, cd, s'a))))"
      and "msel_ssel_lexp_expr_load_rexp_stmt_dom (Inr (Inl (Inl (ad, e\<^sub>p, e, cd, s'))))"
      and "c>0"
    shows "gas s'g < gas st"
proof -
  from assms have "gas s'g \<le> gas (s'b\<lparr>stack := emptyStore, memory := emptyStore\<rparr>)" using msel_ssel_lexp_expr_load_rexp_stmt_dom_gas(5)[of True af xe e\<^sub>p "ffold (init ab) \<lparr>address = vb, sender = address e, svalue = vd, denvalue = fmempty\<rparr> (fmdom ab)" emptyStore "s'b\<lparr>stack := emptyStore, memory := emptyStore\<rparr>" e cd s'b] by blast
  also have "\<dots> = gas s'b" by simp
  also from assms have "\<dots> < gas st" using x7[OF assms(1) assms(2) assms(3) assms(6)] by auto
  finally show ?thesis .
qed

lemma x12:
  assumes "(if gas st \<le> c then throw Gas st else (get \<bind> (\<lambda>s. put (s\<lparr>gas := gas s - c\<rparr>))) st) = Normal ((), s')"
      and "expr ad e\<^sub>p e cd s' = Normal ((KValue vb, Value TAddr), s'a)"
      and "expr val e\<^sub>p e cd s'a = Normal ((KValue vd, Value ta), s'b)"
      and "load True af xe e\<^sub>p (ffold (init ab) \<lparr>address = vb, sender = address e, svalue = vd, denvalue = fmempty\<rparr> (fmdom ab)) emptyStore (s'b\<lparr>stack := emptyStore, memory := emptyStore\<rparr>) e cd s'b = Normal ((ak, al, s'g), vh)"
      and "stmt ag e\<^sub>p ak al (s'g\<lparr>accounts := ala\<rparr>) = Normal ((), s'h)"
      and "msel_ssel_lexp_expr_load_rexp_stmt_dom (Inr (Inl (Inr (True, af, xe, e\<^sub>p, ffold (init ab) \<lparr>address = vb, sender = address e, svalue = vd, denvalue = fmempty\<rparr> (fmdom ab), emptyStore, s'b\<lparr>stack := emptyStore, memory := emptyStore\<rparr>, e, cd, s'b))))"
      and "msel_ssel_lexp_expr_load_rexp_stmt_dom (Inr (Inl (Inl (val, e\<^sub>p, e, cd, s'a))))"
      and "msel_ssel_lexp_expr_load_rexp_stmt_dom (Inr (Inl (Inl (ad, e\<^sub>p, e, cd, s'))))"
      and "msel_ssel_lexp_expr_load_rexp_stmt_dom (Inr (Inr (Inr (ag, e\<^sub>p, ak, al, (s'g\<lparr>accounts := ala\<rparr>)))))"
      and "c>0"
    shows "gas s'h < gas st"
proof -
  from assms have "gas s'h \<le> gas (s'g\<lparr>accounts := ala\<rparr>)" using msel_ssel_lexp_expr_load_rexp_stmt_dom_gas(7) by blast
  also from assms have "\<dots> < gas st" using x11[OF assms(1) assms(2) assms(3) assms(4)] by auto
  finally show ?thesis .
qed

termination
  apply (relation
      "measures [\<lambda>x. case x of Inr (Inr (Inr l)) \<Rightarrow> gas (snd (snd (snd (snd l))))
                             | Inr (Inr (Inl l)) \<Rightarrow> gas (snd (snd (snd (snd l))))
                             | Inr (Inl (Inr l)) \<Rightarrow> gas (snd (snd (snd (snd (snd (snd (snd (snd (snd l)))))))))
                             | Inr (Inl (Inl l)) \<Rightarrow> gas (snd (snd (snd (snd l))))
                             | Inl (Inr (Inr l)) \<Rightarrow> gas (snd (snd (snd (snd l))))
                             | Inl (Inr (Inl l)) \<Rightarrow> gas (snd (snd (snd (snd (snd (snd l))))))
                             | Inl (Inl l) \<Rightarrow> gas (snd (snd (snd (snd (snd (snd (snd l))))))),
                 \<lambda>x. case x of Inr (Inr (Inr l)) \<Rightarrow> 1
                             | Inr (Inr (Inl l)) \<Rightarrow> 0
                             | Inr (Inl (Inr l)) \<Rightarrow> 0
                             | Inr (Inl (Inl l)) \<Rightarrow> 0
                             | Inl (Inr (Inr l)) \<Rightarrow> 0
                             | Inl (Inr (Inl l)) \<Rightarrow> 0
                             | Inl (Inl l) \<Rightarrow> 0,
                 \<lambda>x. case x of Inr (Inr (Inr l)) \<Rightarrow> size (fst l)
                             | Inr (Inr (Inl l)) \<Rightarrow> size (fst l)
                             | Inr (Inl (Inr l)) \<Rightarrow> size_list size (fst (snd (snd l)))
                             | Inr (Inl (Inl l)) \<Rightarrow> size (fst l)
                             | Inl (Inr (Inr l)) \<Rightarrow> size (fst l)
                             | Inl (Inr (Inl l)) \<Rightarrow> size_list size (fst (snd (snd l)))
                             | Inl (Inl l) \<Rightarrow> size_list size (fst (snd (snd (snd l))))]
  ")
  apply simp_all
  apply (simp only: x1)
  apply (simp only: x1)
  apply (simp only: x1)
  apply (auto split: if_split_asm)[1]
  apply (auto split: if_split_asm)[1]
  apply (simp only: x2)
  apply (simp only: x2)
  apply (auto split: if_split_asm)[1]
  apply (simp only: x2)
  apply (auto split: if_split_asm)[1]
  apply (simp only: x2)
  apply (auto split: if_split_asm)[1]
  apply (simp only: x2)
  apply (auto split: if_split_asm)[1]
  apply (simp only: x2)
  apply (auto split: if_split_asm)[1]
  apply (simp only: x2)
  apply (auto split: if_split_asm)[1]
  apply (simp only: x2)
  apply (auto split: if_split_asm)[1]
  apply (auto split: if_split_asm)[1]
  using call_not_zero apply (simp only: x3)
  using call_not_zero apply (simp add: x4)
  apply (auto split: if_split_asm)[1]
  apply (simp only: x2)
  using ecall_not_zero apply (simp add: x7)
  using ecall_not_zero apply (auto simp add: x11)[1]
  using ecall_not_zero apply (auto simp add: x12)[1]
  apply (simp only: x1)
  apply (auto split: if_split_asm)[1]
  apply (simp only: x2)
  apply (simp only: x2)                       
  apply (simp only: x2)
  apply (simp only: x2)
  apply (simp only: x2)
  apply (auto split: if_split_asm)[1]
  apply (simp only: x5)
  apply (auto split: if_split_asm)[1]
  apply (simp only: x2)
  apply (simp only: x2)
  apply (auto split: if_split_asm)[1]
  apply (simp only: x2)
  apply (simp only: x6)
  apply (auto split: if_split_asm)[1]
  using invoke_not_zero apply (simp only: x3)
  apply (auto split: if_split_asm)[1]
  apply (simp only: x2)
  using external_not_zero apply (simp add: x7)
  using external_not_zero apply (auto simp add: x11)[1]
  using external_not_zero apply (auto simp add: x7)[1]
  apply (auto split: if_split_asm)[1]
  apply (simp add: x2)
  apply (simp add: x8)
  apply (auto split: if_split_asm)[1]
  apply (simp only: x9)
  apply (simp only: x10)
  done
end

subsection \<open>A minimal cost model\<close>

fun costs_min :: "S\<Rightarrow> Environment\<^sub>P \<Rightarrow> Environment \<Rightarrow> CalldataT \<Rightarrow> State \<Rightarrow> Gas"
  where
  "costs_min SKIP e\<^sub>p e cd st = 0"
| "costs_min (ASSIGN lv ex) e\<^sub>p e cd st = 0"
| "costs_min (COMP s1 s2) e\<^sub>p e cd st = 0"
| "costs_min (ITE ex s1 s2) e\<^sub>p e cd st = 0"
| "costs_min (WHILE ex s0) e\<^sub>p e cd st = 1"
| "costs_min (TRANSFER ad ex) e\<^sub>p e cd st = 1"
| "costs_min (BLOCK ((id0, tp), ex) s) e\<^sub>p e cd st =0"
| "costs_min (INVOKE _ _) e\<^sub>p e cd st = 1"
| "costs_min (EXTERNAL _ _ _ _) e\<^sub>p e cd st = 1"

fun costs_ex :: "E \<Rightarrow> Environment\<^sub>P \<Rightarrow> Environment \<Rightarrow> CalldataT \<Rightarrow> State \<Rightarrow> Gas"
  where
  "costs_ex (E.INT _ _) e\<^sub>p e cd st = 0"
| "costs_ex (UINT _ _) e\<^sub>p e cd st = 0"
| "costs_ex (ADDRESS _) e\<^sub>p e cd st = 0"
| "costs_ex (BALANCE _) e\<^sub>p e cd st = 0"
| "costs_ex THIS e\<^sub>p e cd st = 0"
| "costs_ex SENDER e\<^sub>p e cd st = 0"
| "costs_ex VALUE e\<^sub>p e cd st = 0"
| "costs_ex (TRUE) e\<^sub>p e cd st = 0"
| "costs_ex (FALSE) e\<^sub>p e cd st = 0"
| "costs_ex (LVAL _) e\<^sub>p e cd st = 0"
| "costs_ex (PLUS _ _) e\<^sub>p e cd st = 0"
| "costs_ex (MINUS _ _) e\<^sub>p e cd st = 0"
| "costs_ex (EQUAL _ _) e\<^sub>p e cd st = 0"
| "costs_ex (LESS _ _) e\<^sub>p e cd st = 0"
| "costs_ex (AND _ _) e\<^sub>p e cd st = 0"
| "costs_ex (OR _ _) e\<^sub>p e cd st = 0"
| "costs_ex (NOT _) e\<^sub>p e cd st = 0"
| "costs_ex (CALL _ _) e\<^sub>p e cd st = 1"
| "costs_ex (ECALL _ _ _ _) e\<^sub>p e cd st = 1"

global_interpretation solidity: statement_with_gas costs_min costs_ex
  defines stmt = "solidity.stmt" 
      and lexp   = solidity.lexp
      and expr   = solidity.expr
      and ssel   = solidity.ssel
      and rexp   = solidity.rexp
      and msel   = solidity.msel
      and load   = solidity.load
  by unfold_locales auto

end
