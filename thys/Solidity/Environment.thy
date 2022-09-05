section\<open>Environment and State\<close>
theory Environment
imports Accounts Storage StateMonad
begin

subsection \<open>Environment\<close>

datatype Type = Value Types
              | Calldata MTypes
              | Memory MTypes
              | Storage STypes
 
datatype Denvalue = Stackloc Location
                  | Storeloc Location

type_synonym Identifier = String.literal
 
record Environment =
  address :: Address (*address of executing contract*)
  sender :: Address (*address of calling contract*)
  svalue :: Valuetype (*money send*)
  denvalue :: "(Identifier, Type \<times> Denvalue) fmap" 
 
fun identifiers :: "Environment \<Rightarrow> Identifier fset"
  where "identifiers e = fmdom (denvalue e)"
 
fun emptyEnv :: "Address \<Rightarrow> Address \<Rightarrow> Valuetype \<Rightarrow> Environment"
  where "emptyEnv a s v = \<lparr>address = a, sender = s, svalue =v, denvalue = fmempty\<rparr>"
 
definition eempty :: "Environment"
  where "eempty = emptyEnv (STR '''') (STR '''') (STR '''')"

declare eempty_def [solidity_symbex]

fun updateEnv :: "Identifier \<Rightarrow> Type \<Rightarrow> Denvalue \<Rightarrow> Environment \<Rightarrow> Environment"
  where "updateEnv i t v e = e \<lparr> denvalue := fmupd i (t,v) (denvalue e) \<rparr>"

fun updateEnvOption :: "Identifier \<Rightarrow> Type \<Rightarrow> Denvalue \<Rightarrow> Environment \<Rightarrow> Environment option"
  where "updateEnvOption i t v e = (case fmlookup (denvalue e) i of 
              Some _ \<Rightarrow> None
            | None \<Rightarrow> Some (updateEnv i t v e))"

lemma updateEnvOption_address: "updateEnvOption i t v e = Some e' \<Longrightarrow> address e = address e'"
by (auto split:option.split_asm)

fun updateEnvDup :: "Identifier \<Rightarrow> Type \<Rightarrow> Denvalue \<Rightarrow> Environment \<Rightarrow> Environment"
  where "updateEnvDup i t v e = (case fmlookup (denvalue e) i of 
              Some _ \<Rightarrow> e
            | None \<Rightarrow> updateEnv i t v e)"

lemma updateEnvDup_address[simp]: "address (updateEnvDup i t v e) = address e"
  by (auto split:option.split)

lemma updateEnvDup_sender[simp]: "sender (updateEnvDup i t v e) = sender e"
  by (auto split:option.split)

lemma updateEnvDup_svalue[simp]: "svalue (updateEnvDup i t v e) = svalue e"
  by (auto split:option.split)

lemma updateEnvDup_dup:
  assumes "i\<noteq>i'" shows "fmlookup (denvalue (updateEnvDup i t v e)) i' = fmlookup (denvalue e) i'"
proof (cases "fmlookup (denvalue e) i = None")
  case True
  then show ?thesis using assms by simp
next
  case False
  then obtain e' where "fmlookup (denvalue e) i = Some e'" by auto
  then show ?thesis using assms by simp
qed

lemma env_reorder_neq:
  assumes "x\<noteq>y"
  shows "updateEnv x t1 v1 (updateEnv y t2 v2 e) = updateEnv y t2 v2 (updateEnv x t1 v1 e)"
proof -
  have "address (updateEnv x t1 v1 (updateEnv y t2 v2 e)) = address (updateEnv y t2 v2 (updateEnv x t1 v1 e))" by simp
  moreover from assms have "denvalue (updateEnv x t1 v1 (updateEnv y t2 v2 e)) = denvalue (updateEnv y t2 v2 (updateEnv x t1 v1 e))" using Finite_Map.fmupd_reorder_neq[of x y "(t1,v1)" "(t2,v2)"] by simp
  ultimately show ?thesis by simp
qed

lemma uEO_in:
  assumes "i |\<in>| fmdom (denvalue e)"
  shows "updateEnvOption i t v e = None"
  using assms by auto

lemma uEO_n_In:
  assumes "\<not> i |\<in>| fmdom (denvalue e)"
  shows "updateEnvOption i t v e = Some (updateEnv i t v e)"
  using assms by auto

fun astack :: "Identifier \<Rightarrow> Type \<Rightarrow> Stackvalue \<Rightarrow> Stack * Environment \<Rightarrow> Stack * Environment"
  where "astack i t v (s, e) = (push v s, (updateEnv i t (Stackloc (ShowL\<^sub>n\<^sub>a\<^sub>t (toploc s))) e))"

subsection \<open>State\<close>

type_synonym Gas = nat

record State =
  accounts :: Accounts
  stack :: Stack
  memory :: MemoryT
  storage :: "(Address,StorageT) fmap"
  gas :: Gas

datatype Ex = Gas | Err

fun append :: "Identifier \<Rightarrow> Type \<Rightarrow> Stackvalue
  \<Rightarrow> CalldataT \<Rightarrow> Environment \<Rightarrow> (CalldataT \<times> Environment, Ex, State) state_monad"
where
  "append id0 tp v cd e st =
    (let (k, e') = astack id0 tp v (stack st, e)
    in do {
      modify (\<lambda>st. st \<lparr>stack := k\<rparr>);
      return (cd, e')
    }) st"

subsection \<open>Declarations\<close>

text \<open>This function is used to declare a new variable: decl id tp val copy cd mem cd' env st
\begin{description}
  \item[id] is the name of the variable
  \item[tp] is the type of the variable
  \item[val] is an optional initialization parameter. If it is None, the types default value is taken.
  \item[copy] is a flag to indicate whether memory should be copied (from mem parameter) or not (copying is required for example for external method calls).
  \item[cd] is the original calldata which is used as a source
  \item[mem] is the original memory which is used as a source
  \item[cd'] is the new calldata
  \item[env] is the new environment
  \item[st] is the new state
\end{description}\<close>
fun decl :: "Identifier \<Rightarrow> Type \<Rightarrow> (Stackvalue * Type) option \<Rightarrow> bool \<Rightarrow> CalldataT \<Rightarrow> MemoryT
    \<Rightarrow> CalldataT \<Rightarrow> Environment \<Rightarrow> (CalldataT \<times> Environment, Ex, State) state_monad"
  where
(* Declaring stack variables *)
  "decl i (Value t) None _ _ _ c env st = append i (Value t) (KValue (ival t)) c env st"
| "decl i (Value t) (Some (KValue v, Value t')) _ _ _ c env st =
    (case convert t' t v of
      Some (v', t'') \<Rightarrow> append i (Value t'') (KValue v') c env
    | None \<Rightarrow> throw Err) st"
| "decl _ (Value _) (Some _) _ _ _ _ _ st = throw Err st"

(* Declaring calldata variables *)
| "decl i (Calldata (MTArray x t)) (Some (KCDptr p, _)) True cd _ c env st =
    (let l = ShowL\<^sub>n\<^sub>a\<^sub>t (toploc c);
         (_, c') = allocate c
     in (case cpm2m p l x t cd c' of
          Some c'' \<Rightarrow> append i (Calldata (MTArray x t)) (KCDptr l) c'' env
        | None \<Rightarrow> throw Err)) st"
| "decl i (Calldata (MTArray x t)) (Some (KMemptr p, _)) True _ mem c env st =
    (let l = ShowL\<^sub>n\<^sub>a\<^sub>t (toploc c);
         (_, c') = allocate c
     in (case cpm2m p l x t mem c' of
          Some c'' \<Rightarrow> append i (Calldata (MTArray x t)) (KCDptr l) c'' env
        | None \<Rightarrow> throw Err)) st"
| "decl i (Calldata _) _ _ _ _ _ _ st = throw Err st"

(* Declaring memory variables *)
| "decl i (Memory (MTArray x t)) None _ _ _ c env st =
    (do {
      m \<leftarrow> applyf (\<lambda>st. memory st);
      modify (\<lambda>st. st \<lparr>memory := minit x t m\<rparr>);
      append i (Memory (MTArray x t)) (KMemptr (ShowL\<^sub>n\<^sub>a\<^sub>t (toploc m))) c env
    }) st"
| "decl i (Memory (MTArray x t)) (Some (KMemptr p, _)) True _ mem c env st =
    (do {
      m \<leftarrow> (applyf (\<lambda>st. memory st));
      (case cpm2m p (ShowL\<^sub>n\<^sub>a\<^sub>t (toploc m)) x t mem (snd (allocate m)) of
         Some m' \<Rightarrow>
          do {
           modify (\<lambda>st. st \<lparr>memory := m'\<rparr>);
           append i (Memory (MTArray x t)) (KMemptr (ShowL\<^sub>n\<^sub>a\<^sub>t (toploc m))) c env
          }
       | None \<Rightarrow> throw Err)
    }) st"
| "decl i (Memory (MTArray x t)) (Some (KMemptr p, _)) False _ _ c env st =
   append i (Memory (MTArray x t)) (KMemptr p) c env st"
| "decl i (Memory (MTArray x t)) (Some (KCDptr p, _)) _ cd _ c env st =
    (do {
      m \<leftarrow> (applyf (\<lambda>st. memory st));
      (case cpm2m p (ShowL\<^sub>n\<^sub>a\<^sub>t (toploc m)) x t cd (snd (allocate m)) of
        Some m' \<Rightarrow>
          do {
          modify (\<lambda>st. st \<lparr>memory := m'\<rparr>);
          append i (Memory (MTArray x t)) (KMemptr (ShowL\<^sub>n\<^sub>a\<^sub>t (toploc m))) c env
          }
     | None \<Rightarrow> throw Err)
    }) st"
| "decl i (Memory (MTArray x t)) (Some (KStoptr p, Storage (STArray x' t'))) _ _ _ c env st =
    (do {
      s \<leftarrow> (applyf (\<lambda>st. storage st));
      (case fmlookup s (address env) of
        Some s' \<Rightarrow>
        (do {
          m \<leftarrow> (applyf (\<lambda>st. memory st));
          (case cps2m p (ShowL\<^sub>n\<^sub>a\<^sub>t (toploc m)) x' t' s' (snd (allocate m)) of
              Some m'' \<Rightarrow>
              do {
                modify (\<lambda>st. st \<lparr>memory := m''\<rparr>);
              append i (Memory (MTArray x t)) (KMemptr (ShowL\<^sub>n\<^sub>a\<^sub>t (toploc m))) c env
              }
            | None \<Rightarrow> throw Err)
        })
      | None \<Rightarrow> throw Err)
    }) st"
| "decl _ (Memory (MTArray _ _)) (Some _) _ _ _ _ _ st = throw Err st"
| "decl _ (Memory (MTValue _)) _ _ _ _ _ _ st = throw Err st"

(* Declaring storage variables *)
| "decl _ (Storage (STArray _ _)) None _ _ _ _ _ st = throw Err st" (* Uninitialized storage arrays not allowed *)
| "decl i (Storage (STArray x t)) (Some (KStoptr p, _)) _ _ _ c env st =
    append i (Storage (STArray x t)) (KStoptr p) c env st"
| "decl _ (Storage (STArray _ _)) (Some _) _ _ _ _ _ st = throw Err st"
| "decl _ (Storage (STMap _ _)) None _ _ _ _ _ st = throw Err st"  (* Uninitialized storage maps not allowed *)
| "decl i (Storage (STMap t t')) (Some (KStoptr p, _)) _ _ _ c env st =
  append i (Storage (STMap t t')) (KStoptr p) c env st"
| "decl _ (Storage (STMap _ _)) (Some _) _ _ _ _ _ st = throw Err st"
| "decl _ (Storage (STValue _)) _ _ _ _ _ _ st = throw Err st"

(*TODO: refactor with decl.elims*)
lemma decl_gas_address:
  assumes "decl a1 a2 a3 cp cd mem c env st = Normal ((l1', t1'), st1')"
    shows "gas st1' = gas st \<and> address env = address t1' \<and> sender env = sender t1' \<and> svalue env = svalue t1'"
proof (cases a2)
  case (Value t)
  then show ?thesis
  proof (cases a3)
    case None
    with Value show ?thesis using assms by auto
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
          proof (cases "convert t' t v")
            case None
            with Some Pair KValue Value v2 show ?thesis using assms by simp
          next
            case s2: (Some a)
            show ?thesis
            proof (cases a)
              case p2: (Pair a b)
              with Some Pair KValue Value v2 s2 show ?thesis using assms by auto
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
              with Calldata MTArray Some Pair KCDptr l_def c_def True show ?thesis using assms by auto
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
              with Calldata MTArray Some Pair KMemptr l_def c_def True show ?thesis using assms by auto
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
      with Memory MTArray None show ?thesis using assms by (auto simp add:Let_def)
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
            with Memory MTArray Some Pair KCDptr m_def l_def m'_def show ?thesis using assms by auto
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
              with Memory MTArray Some Pair KMemptr True m_def l_def m'_def show ?thesis using assms by auto
            qed
          next
            case False
            with Memory MTArray Some Pair KMemptr show ?thesis using assms by auto
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
              from assms(1) Memory MTArray Some Pair KStoptr Storage STArray m_def l_def m'_def
              obtain s where *: "fmlookup (storage st) (address env) = Some s" using Let_def by (auto simp add: Let_def split:option.split_asm)
              then show ?thesis
              proof (cases "cps2m p l x' t' s m'")
                case None
                with Memory MTArray Some Pair KStoptr Storage STArray m_def l_def m'_def * show ?thesis using assms by simp
              next
                case s2: (Some a)
                with Memory MTArray Some Pair KStoptr Storage STArray m_def l_def m'_def * show ?thesis using assms by auto
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
          with Storage STArray Some Pair show ?thesis using assms by auto
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
          with Storage STMap Some Pair show ?thesis using assms by auto
        qed
      qed
    qed
  next
    case (STValue x3)
    with Storage show ?thesis using assms by simp
  qed
qed

end
