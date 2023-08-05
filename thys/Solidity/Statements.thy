section \<open>Statements\<close>
theory Statements
  imports Expressions StateMonad
begin

locale statement_with_gas = expressions_with_gas +
  fixes costs :: "S \<Rightarrow> Environment \<Rightarrow> CalldataT \<Rightarrow> State \<Rightarrow> Gas"
  assumes while_not_zero[termination_simp]: "\<And>e cd st ex s0. 0 < (costs (WHILE ex s0) e cd st) "
      and invoke_not_zero[termination_simp]: "\<And>e cd st i xe. 0 < (costs (INVOKE i xe) e cd st)"
      and external_not_zero[termination_simp]: "\<And>e cd st ad i xe val. 0 < (costs (EXTERNAL ad i xe val) e cd st)"
      and transfer_not_zero[termination_simp]: "\<And>e cd st ex ad. 0 < (costs (TRANSFER ad ex) e cd st)"
      and new_not_zero[termination_simp]: "\<And>e cd st i xe val. 0 < (costs (NEW i xe val) e cd st)"
begin

subsection \<open>Semantics of left expressions\<close>

text \<open>We first introduce lexp.\<close>

fun lexp :: "L \<Rightarrow> Environment \<Rightarrow> CalldataT \<Rightarrow> State \<Rightarrow> (LType * Type, Ex, Gas) state_monad"
  where "lexp (Id i) e _ st g =
    (case (denvalue e) $$ i of
      Some (tp, (Stackloc l)) \<Rightarrow> return (LStackloc l, tp)
    | Some (tp, (Storeloc l)) \<Rightarrow> return (LStoreloc l, tp)
    | _ \<Rightarrow> throw Err) g"
| "lexp (Ref i r) e cd st g =
    (case (denvalue e) $$ i of
      Some (tp, Stackloc l) \<Rightarrow>
        (case accessStore l (stack st) of
          Some (KCDptr _) \<Rightarrow> throw Err
        | Some (KMemptr l') \<Rightarrow>
          do {
            t \<leftarrow> (case tp of Memory t \<Rightarrow> return t | _ \<Rightarrow> throw Err);
            (l'', t') \<leftarrow> msel True t l' r e cd st;
            return (LMemloc l'', Memory t')
          }
        | Some (KStoptr l') \<Rightarrow>
          do {
            t \<leftarrow> (case tp of Storage t \<Rightarrow> return t | _ \<Rightarrow> throw Err);
            (l'', t') \<leftarrow> ssel t l' r e cd st;
            return (LStoreloc l'', Storage t')
          }
        | Some (KValue _) \<Rightarrow> throw Err
        | None \<Rightarrow> throw Err)
    | Some (tp, Storeloc l) \<Rightarrow>
        do {
          t \<leftarrow> (case tp of Storage t \<Rightarrow> return t | _ \<Rightarrow> throw Err);
          (l', t') \<leftarrow> ssel t l r e cd st;
          return (LStoreloc l', Storage t')
        }
    | None \<Rightarrow> throw Err) g"

lemma lexp_gas[rule_format]:
    "\<forall>l5' t5' g5'. lexp l5 ev5 cd5 st5 g5 = Normal ((l5', t5'), g5') \<longrightarrow> g5' \<le> g5"
proof (induct rule: lexp.induct[where ?P="\<lambda>l5 ev5 cd5 st5 g5. (\<forall>l5' t5' g5'. lexp l5 ev5 cd5 st5 g5 = Normal ((l5', t5'), g5') \<longrightarrow> g5' \<le> g5)"])
  case (1 i e uv st g)
  then show ?case using lexp.simps(1) by (simp split: option.split Denvalue.split prod.split)
next
  case (2 i r e cd st g)
  show ?case
  proof (rule allI[THEN allI, THEN allI, OF impI])
    fix st5' xa xaa
    assume a1: "lexp (Ref i r) e cd st g = Normal ((st5', xa), xaa)"
    then show "xaa \<le> g"
    proof (cases "fmlookup (denvalue e) i")
      case None
      with a1 show ?thesis using lexp.simps(2) by simp
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
            with a1 Some Pair Stackloc show ?thesis using lexp.psimps(2) by simp
          next
            case s2: (Some a)
            then show ?thesis
            proof (cases a)
              case (KValue x1)
              with a1 Some Pair Stackloc s2 show ?thesis using lexp.psimps(2) by simp
            next
              case (KCDptr x2)
              with a1 Some Pair Stackloc s2 show ?thesis using lexp.psimps(2) by simp
            next
              case (KMemptr l')
              then show ?thesis
              proof (cases tp)
                case (Value _)
                with a1 Some Pair Stackloc s2 KMemptr show ?thesis using lexp.simps(2) by simp
              next
                case (Calldata _)
                with a1 Some Pair Stackloc s2 KMemptr show ?thesis using lexp.simps(2) by simp
              next
                case (Memory t)
                then show ?thesis
                proof (cases "msel True t l' r e cd st g")
                  case (n _ _)
                  with 2 a1 Some Pair Stackloc s2 KMemptr Memory show ?thesis using msel_ssel_expr_load_rexp_gas(1) by (simp split: prod.split_asm)
                next
                  case (e _)
                  with a1 Some Pair Stackloc s2 KMemptr Memory show ?thesis using lexp.psimps(2) by simp
                qed
              next
                case (Storage _)
                with a1 Some Pair Stackloc s2 KMemptr show ?thesis using lexp.psimps(2) by simp
              qed
            next
              case (KStoptr l')
              then show ?thesis
              proof (cases tp)
                case (Value _)
                with a1 Some Pair Stackloc s2 KStoptr show ?thesis using lexp.psimps(2) by simp
              next
                case (Calldata _)
                with a1 Some Pair Stackloc s2 KStoptr show ?thesis using lexp.psimps(2) by simp
              next
                case (Memory _)
                with a1 Some Pair Stackloc s2 KStoptr show ?thesis using lexp.psimps(2) by simp
              next
                case (Storage t)
                then show ?thesis
                proof (cases "ssel t l' r e cd st g")
                  case (n _ _)
                  with a1 Some Pair Stackloc s2 KStoptr Storage show ?thesis using msel_ssel_expr_load_rexp_gas(2) by (auto split: prod.split_asm)
                next
                  case (e _)
                  with a1 Some Pair Stackloc s2 KStoptr Storage show ?thesis using lexp.psimps(2) by simp
                qed
              qed
            qed
          qed
        next
          case (Storeloc l)
          then show ?thesis
          proof (cases tp)
            case (Value _)
            with a1 Some Pair Storeloc show ?thesis using lexp.psimps(2) by simp
          next
            case (Calldata _)
            with  a1 Some Pair Storeloc show ?thesis using lexp.psimps(2) by simp
          next
            case (Memory _)
            with a1 Some Pair Storeloc show ?thesis using lexp.psimps(2) by simp
          next
            case (Storage t)
            then show ?thesis
            proof (cases "ssel t l r e cd st g")
              case (n _ _)
              with a1 Some Pair Storeloc Storage show ?thesis using msel_ssel_expr_load_rexp_gas(2) by (auto split: prod.split_asm)
            next
              case (e _)
              with a1 Some Pair Storeloc Storage show ?thesis using lexp.psimps(2) by simp
            qed
          qed
        qed
      qed
    qed
  qed
qed

subsection \<open>Semantics of statements\<close>

text \<open>The following is a helper function to connect the gas monad with the state monad.\<close>

fun
  toState :: "(State \<Rightarrow> ('a, 'e, Gas) state_monad) \<Rightarrow> ('a, 'e, State) state_monad" where
 "toState gm = (\<lambda>s. case gm s (gas s) of
                     Normal (a,g) \<Rightarrow> Normal(a,s\<lparr>gas:=g\<rparr>)
                    | Exception e \<Rightarrow> Exception e)"

lemma wptoState[wprule]:
  assumes "\<And>a g. gm s (gas s) = Normal (a, g) \<Longrightarrow> P a (s\<lparr>gas:=g\<rparr>)"
      and "\<And>e. gm s (gas s) = Exception e \<Longrightarrow> E e"
    shows "wp (toState gm) P E s"
  using assms unfolding wp_def by (simp split:result.split result.split_asm)

text \<open>Now we define the semantics of statements.\<close>
function (domintros) stmt :: "S \<Rightarrow> Environment \<Rightarrow> CalldataT \<Rightarrow> (unit, Ex, State) state_monad"
  where "stmt SKIP e cd st =
    (do {
      assert Gas (\<lambda>st. gas st > costs SKIP e cd st);
      modify (\<lambda>st. st\<lparr>gas := gas st - costs SKIP e cd st\<rparr>)
    }) st"
| "stmt (ASSIGN lv ex) env cd st =
    (do {
      assert Gas (\<lambda>st. gas st > costs (ASSIGN lv ex) env cd st);
      modify (\<lambda>st. st\<lparr>gas := gas st - costs (ASSIGN lv ex) env cd st\<rparr>);
      re \<leftarrow> toState (expr ex env cd);
      case re of
        (KValue v, Value t) \<Rightarrow>
          do {
            rl \<leftarrow> toState (lexp lv env cd);
            case rl of
              (LStackloc l, Value t') \<Rightarrow>
                do {
                  v' \<leftarrow> option Err (\<lambda>_. convert t t' v);
                  modify (\<lambda>st. st \<lparr>stack := updateStore l (KValue v') (stack st)\<rparr>)
                }
            | (LStoreloc l, Storage (STValue t')) \<Rightarrow>
                do {
                  v' \<leftarrow> option Err (\<lambda>_. convert t t' v);
                  modify (\<lambda>st. st\<lparr>storage := (storage st) (address env := fmupd l v' (storage st (address env)))\<rparr>)
                }
            | (LMemloc l, Memory (MTValue t')) \<Rightarrow>
                do {
                  v' \<leftarrow> option Err (\<lambda>_. convert t t' v);
                  modify (\<lambda>st. st\<lparr>memory := updateStore l (MValue v') (memory st)\<rparr>)
                }
            | _ \<Rightarrow> throw Err
          }
      | (KCDptr p, Calldata (MTArray x t)) \<Rightarrow>
          do {
            rl \<leftarrow> toState (lexp lv env cd);
            case rl of
              (LStackloc l, Memory _) \<Rightarrow>
                do {
                  sv \<leftarrow> applyf (\<lambda>st. accessStore l (stack st));
                  p' \<leftarrow> case sv of Some (KMemptr p') \<Rightarrow> return p' | _ \<Rightarrow> throw Err;
                  m \<leftarrow> option Err (\<lambda>st. cpm2m p p' x t cd (memory st));
                  modify (\<lambda>st. st\<lparr>memory := m\<rparr>)
                }
            | (LStackloc l, Storage _) \<Rightarrow>
                do {
                  sv \<leftarrow> applyf (\<lambda>st. accessStore l (stack st));
                  p' \<leftarrow> case sv of Some (KStoptr p') \<Rightarrow> return p' | _ \<Rightarrow> throw Err;
                  s \<leftarrow> option Err (\<lambda>st. cpm2s p p' x t cd (storage st (address env)));
                  modify (\<lambda>st. st \<lparr>storage := (storage st) (address env := s)\<rparr>)
                }
            | (LStoreloc l, _) \<Rightarrow>
                do {
                  s \<leftarrow> option Err (\<lambda>st. cpm2s p l x t cd (storage st (address env)));
                  modify (\<lambda>st. st \<lparr>storage := (storage st) (address env := s)\<rparr>)
                }
            | (LMemloc l, _) \<Rightarrow>
                do {
                  m \<leftarrow> option Err (\<lambda>st. cpm2m p l x t cd (memory st));
                  modify (\<lambda>st. st \<lparr>memory := m\<rparr>)
                }
            | _ \<Rightarrow> throw Err
          }
      | (KMemptr p, Memory (MTArray x t)) \<Rightarrow>
          do {
            rl \<leftarrow> toState (lexp lv env cd);
            case rl of
              (LStackloc l, Memory _) \<Rightarrow> modify (\<lambda>st. st\<lparr>stack := updateStore l (KMemptr p) (stack st)\<rparr>)
            | (LStackloc l, Storage _) \<Rightarrow>
                do {
                  sv \<leftarrow> applyf (\<lambda>st. accessStore l (stack st));
                  p' \<leftarrow> case sv of Some (KStoptr p') \<Rightarrow> return p' | _ \<Rightarrow> throw Err;
                  s \<leftarrow> option Err (\<lambda>st. cpm2s p p' x t (memory st) (storage st (address env)));
                  modify (\<lambda>st. st \<lparr>storage := (storage st) (address env := s)\<rparr>)
                }
            | (LStoreloc l, _) \<Rightarrow>
                do {
                  s \<leftarrow> option Err (\<lambda>st. cpm2s p l x t (memory st) (storage st (address env)));
                  modify (\<lambda>st. st \<lparr>storage := (storage st) (address env := s)\<rparr>)
                }
            | (LMemloc l, _) \<Rightarrow> modify (\<lambda>st. st \<lparr>memory := updateStore l (MPointer p) (memory st)\<rparr>)
            | _ \<Rightarrow> throw Err
          }
      | (KStoptr p, Storage (STArray x t)) \<Rightarrow>
          do {
            rl \<leftarrow> toState (lexp lv env cd);
            case rl of
              (LStackloc l, Memory _) \<Rightarrow>
                do {
                  sv \<leftarrow> applyf (\<lambda>st. accessStore l (stack st));
                  p' \<leftarrow> case sv of Some (KMemptr p') \<Rightarrow> return p' | _ \<Rightarrow> throw Err;
                  m \<leftarrow> option Err (\<lambda>st. cps2m p p' x t (storage st (address env)) (memory st));
                  modify (\<lambda>st. st\<lparr>memory := m\<rparr>)
                }
            | (LStackloc l, Storage _) \<Rightarrow> modify (\<lambda>st. st\<lparr>stack := updateStore l (KStoptr p) (stack st)\<rparr>)
            | (LStoreloc l, _) \<Rightarrow>
                do {
                  s \<leftarrow> option Err (\<lambda>st. copy p l x t (storage st (address env)));
                  modify (\<lambda>st. st \<lparr>storage := (storage st) (address env := s)\<rparr>)
                }
            | (LMemloc l, _) \<Rightarrow>
                do {
                  m \<leftarrow> option Err (\<lambda>st. cps2m p l x t (storage st (address env)) (memory st));
                  modify (\<lambda>st. st\<lparr>memory := m\<rparr>)
                }
            | _ \<Rightarrow> throw Err
          }
      | (KStoptr p, Storage (STMap t t')) \<Rightarrow>
          do {
            rl \<leftarrow> toState (lexp lv env cd);
            l \<leftarrow> case rl of (LStackloc l, _) \<Rightarrow> return l | _ \<Rightarrow> throw Err;
            modify (\<lambda>st. st\<lparr>stack := updateStore l (KStoptr p) (stack st)\<rparr>)
          }
      | _ \<Rightarrow> throw Err
    }) st"
| "stmt (COMP s1 s2) e cd st =
    (do {
      assert Gas (\<lambda>st. gas st > costs (COMP s1 s2) e cd st);
      modify (\<lambda>st. st\<lparr>gas := gas st - costs (COMP s1 s2) e cd st\<rparr>);
      stmt s1 e cd;
      stmt s2 e cd
    }) st"
| "stmt (ITE ex s1 s2) e cd st =
    (do {
      assert Gas (\<lambda>st. gas st > costs (ITE ex s1 s2) e cd st);
      modify (\<lambda>st. st\<lparr>gas := gas st - costs (ITE ex s1 s2) e cd st\<rparr>);
      v \<leftarrow> toState (expr ex e cd);
      b \<leftarrow> (case v of (KValue b, Value TBool) \<Rightarrow> return b | _ \<Rightarrow> throw Err);
      if b = ShowL\<^sub>b\<^sub>o\<^sub>o\<^sub>l True then stmt s1 e cd
      else if b = ShowL\<^sub>b\<^sub>o\<^sub>o\<^sub>l False then stmt s2 e cd
      else throw Err
    }) st"
| "stmt (WHILE ex s0) e cd st =
    (do {
      assert Gas (\<lambda>st. gas st > costs (WHILE ex s0) e cd st);
      modify (\<lambda>st. st\<lparr>gas := gas st - costs (WHILE ex s0) e cd st\<rparr>);
      v \<leftarrow> toState (expr ex e cd);
      b \<leftarrow> (case v of (KValue b, Value TBool) \<Rightarrow> return b | _ \<Rightarrow> throw Err);
      if b = ShowL\<^sub>b\<^sub>o\<^sub>o\<^sub>l True then
        do {
          stmt s0 e cd;
          stmt (WHILE ex s0) e cd
        }
      else if b = ShowL\<^sub>b\<^sub>o\<^sub>o\<^sub>l False then return ()
      else throw Err
    }) st"
| "stmt (INVOKE i xe) e cd st =
    (do {
      assert Gas (\<lambda>st. gas st > costs (INVOKE i xe) e cd st);
      modify (\<lambda>st. st\<lparr>gas := gas st - costs (INVOKE i xe) e cd st\<rparr>);
      (ct, _) \<leftarrow> option Err (\<lambda>_. ep $$ contract e);
      (fp, f) \<leftarrow> case ct $$ i of Some (Method (fp, False, f)) \<Rightarrow> return (fp, f) | _ \<Rightarrow> throw Err;
      let e' = ffold_init ct (emptyEnv (address e) (contract e) (sender e) (svalue e)) (fmdom ct);
      m\<^sub>o \<leftarrow> applyf memory;
      (e\<^sub>l, cd\<^sub>l, k\<^sub>l, m\<^sub>l) \<leftarrow> toState (load False fp xe e' emptyStore emptyStore m\<^sub>o e cd);
      k\<^sub>o \<leftarrow> applyf stack;
      modify (\<lambda>st. st\<lparr>stack:=k\<^sub>l, memory:=m\<^sub>l\<rparr>);
      stmt f e\<^sub>l cd\<^sub>l;
      modify (\<lambda>st. st\<lparr>stack:=k\<^sub>o\<rparr>)
    }) st"
(*External Method calls allow to send some money val with it*)
(*However this transfer does NOT trigger a fallback*)
(*External methods can only be called from externally*)
| "stmt (EXTERNAL ad i xe val) e cd st =
    (do {
      assert Gas (\<lambda>st. gas st > costs (EXTERNAL ad i xe val) e cd st);
      modify (\<lambda>st. st\<lparr>gas := gas st - costs (EXTERNAL ad i xe val) e cd st\<rparr>);
      kad \<leftarrow> toState (expr ad e cd);
      adv \<leftarrow> case kad of (KValue adv, Value TAddr) \<Rightarrow> return adv | _ \<Rightarrow> throw Err;
      assert Err (\<lambda>_. adv \<noteq> address e);
      c \<leftarrow> (\<lambda>st. case type (accounts st adv) of Some (Contract c) \<Rightarrow> return c st | _ \<Rightarrow> throw Err st);
      (ct, _, fb) \<leftarrow> option Err (\<lambda>_. ep $$ c);
      kv \<leftarrow> toState (expr val e cd);
      (v, t) \<leftarrow> case kv of (KValue v, Value t) \<Rightarrow> return (v, t) | _ \<Rightarrow> throw Err;
      v' \<leftarrow> option Err (\<lambda>_. convert t (TUInt 256) v);
      let e' = ffold_init ct (emptyEnv adv c (address e) v') (fmdom ct);
      case ct $$ i of
        Some (Method (fp, True, f)) \<Rightarrow>
          do {
            (e\<^sub>l, cd\<^sub>l, k\<^sub>l, m\<^sub>l) \<leftarrow> toState (load True fp xe e' emptyStore emptyStore emptyStore e cd);
            acc \<leftarrow> option Err (\<lambda>st. transfer (address e) adv v' (accounts st));
            (k\<^sub>o, m\<^sub>o) \<leftarrow> applyf (\<lambda>st. (stack st, memory st));
            modify (\<lambda>st. st\<lparr>accounts := acc, stack:=k\<^sub>l,memory:=m\<^sub>l\<rparr>);
            stmt f e\<^sub>l cd\<^sub>l;
            modify (\<lambda>st. st\<lparr>stack:=k\<^sub>o, memory := m\<^sub>o\<rparr>)
          }
      | None \<Rightarrow>
          do {
            acc \<leftarrow> option Err (\<lambda>st. transfer (address e) adv v' (accounts st));
            (k\<^sub>o, m\<^sub>o) \<leftarrow> applyf (\<lambda>st. (stack st, memory st));
            modify (\<lambda>st. st\<lparr>accounts := acc,stack:=emptyStore, memory:=emptyStore\<rparr>);
            stmt fb e' emptyStore;
            modify (\<lambda>st. st\<lparr>stack:=k\<^sub>o, memory := m\<^sub>o\<rparr>)
          }
      | _ \<Rightarrow> throw Err
    }) st"
| "stmt (TRANSFER ad ex) e cd st =
    (do {
      assert Gas (\<lambda>st. gas st > costs (TRANSFER ad ex) e cd st);
      modify (\<lambda>st. st\<lparr>gas := gas st - costs (TRANSFER ad ex) e cd st\<rparr>);
      kv \<leftarrow> toState (expr ad e cd);
      adv \<leftarrow> case kv of (KValue adv, Value TAddr) \<Rightarrow> return adv | _ \<Rightarrow> throw Err;
      kv' \<leftarrow> toState (expr ex e cd);
      (v, t) \<leftarrow> case kv' of (KValue v, Value t) \<Rightarrow> return (v, t) | _ \<Rightarrow> throw Err;
      v' \<leftarrow> option Err (\<lambda>_. convert t (TUInt 256) v);
      acc \<leftarrow> applyf accounts;
      case type (acc adv) of
        Some (Contract c) \<Rightarrow>
          do {
            (ct, _, f) \<leftarrow> option Err (\<lambda>_. ep $$ c);
            let e' = ffold_init ct (emptyEnv adv c (address e) v') (fmdom ct);
            (k\<^sub>o, m\<^sub>o) \<leftarrow> applyf (\<lambda>st. (stack st, memory st));
            acc' \<leftarrow> option Err (\<lambda>st. transfer (address e) adv v' (accounts st));
            modify (\<lambda>st. st\<lparr>accounts := acc', stack:=emptyStore, memory:=emptyStore\<rparr>);
            stmt f e' emptyStore;
            modify (\<lambda>st. st\<lparr>stack:=k\<^sub>o, memory := m\<^sub>o\<rparr>)
          }
      | Some EOA \<Rightarrow>
          do {
            acc' \<leftarrow> option Err (\<lambda>st. transfer (address e) adv v' (accounts st));
            modify (\<lambda>st. (st\<lparr>accounts := acc'\<rparr>))
          }
      | None \<Rightarrow> throw Err
    }) st"
| "stmt (BLOCK ((id0, tp), None) s) e\<^sub>v cd st =
    (do {
      assert Gas (\<lambda>st. gas st > costs (BLOCK ((id0, tp), None) s) e\<^sub>v cd st);
      modify (\<lambda>st. st\<lparr>gas := gas st - costs (BLOCK ((id0, tp), None) s) e\<^sub>v cd st\<rparr>);
      (cd', mem', sck', e') \<leftarrow> option Err (\<lambda>st. decl id0 tp None False cd (memory st) (storage st) (cd, memory st, stack st, e\<^sub>v));
      modify (\<lambda>st. st\<lparr>stack := sck', memory := mem'\<rparr>);
      stmt s e' cd'
    }) st"
| "stmt (BLOCK ((id0, tp), Some ex') s) e\<^sub>v cd st =
    (do {
      assert Gas (\<lambda>st. gas st > costs(BLOCK ((id0, tp), Some ex') s) e\<^sub>v cd st);
      modify (\<lambda>st. st\<lparr>gas := gas st - costs (BLOCK ((id0, tp), Some ex') s) e\<^sub>v cd st\<rparr>);
      (v, t) \<leftarrow> toState (expr ex' e\<^sub>v cd);
      (cd', mem', sck', e') \<leftarrow> option Err (\<lambda>st. decl id0 tp (Some (v, t)) False cd (memory st) (storage st) (cd, memory st, stack st, e\<^sub>v));
      modify (\<lambda>st. st\<lparr>stack := sck', memory := mem'\<rparr>);
      stmt s e' cd'
    }) st"
(*
  Note: We cannot use (ct, (fp, cn), fb) <- option Err (\<lambda>_. ep $$ i)
*)
| "stmt (NEW i xe val) e cd st =
    (do {
      assert Gas (\<lambda>st. gas st > costs (NEW i xe val) e cd st);
      modify (\<lambda>st. st\<lparr>gas := gas st - costs (NEW i xe val) e cd st\<rparr>);
      adv \<leftarrow> applyf (\<lambda>st. hash (address e) (ShowL\<^sub>n\<^sub>a\<^sub>t (contracts (accounts st (address e)))));
      assert Err (\<lambda>st. type (accounts st adv) = None);
      kv \<leftarrow> toState (expr val e cd);
      (v, t) \<leftarrow> case kv of (KValue v, Value t) \<Rightarrow> return (v, t) | _ \<Rightarrow> throw Err;
      (ct, cn, _) \<leftarrow> option Err (\<lambda>_. ep $$ i);
      let e' = ffold_init ct (emptyEnv adv i (address e) v) (fmdom ct);
      (e\<^sub>l, cd\<^sub>l, k\<^sub>l, m\<^sub>l) \<leftarrow> toState (load True (fst cn) xe e' emptyStore emptyStore emptyStore e cd);
      modify (\<lambda>st. st\<lparr>accounts := (accounts st)(adv := \<lparr>bal = ShowL\<^sub>i\<^sub>n\<^sub>t 0, type = Some (Contract i), contracts = 0\<rparr>), storage:=(storage st)(adv := {$$})\<rparr>);
      acc \<leftarrow> option Err (\<lambda>st. transfer (address e) adv v (accounts st));
      (k\<^sub>o, m\<^sub>o) \<leftarrow> applyf (\<lambda>st. (stack st, memory st));
      modify (\<lambda>st. st\<lparr>accounts := acc, stack:=k\<^sub>l, memory:=m\<^sub>l\<rparr>);
      stmt (snd cn) e\<^sub>l cd\<^sub>l;
      modify (\<lambda>st. st\<lparr>stack:=k\<^sub>o, memory := m\<^sub>o\<rparr>);
      modify (incrementAccountContracts (address e))
    }) st"
by pat_completeness auto

subsection \<open>Termination\<close>

text \<open>Again, to prove termination we need a lemma regarding gas consumption.\<close>

lemma stmt_dom_gas[rule_format]:
    "stmt_dom (s6, ev6, cd6, st6) \<Longrightarrow> (\<forall>st6'. stmt s6 ev6 cd6 st6 = Normal((), st6') \<longrightarrow> gas st6' \<le> gas st6)"
proof (induct rule: stmt.pinduct[where ?P="\<lambda>s6 ev6 cd6 st6. (\<forall>st6'. stmt s6 ev6 cd6 st6 = Normal ((), st6') \<longrightarrow> gas st6' \<le> gas st6)"])
  case (1 e cd st)
  then show ?case using stmt.psimps(1) by simp
next
  case (2 lv ex env cd st)
  define g where "g = costs (ASSIGN lv ex) env cd st"
  show ?case
  proof (rule allI[OF impI])
    fix st6'
    assume stmt_def: "stmt (ASSIGN lv ex) env cd st = Normal ((), st6')"
    then show "gas st6' \<le> gas st"
    proof cases
      assume "gas st \<le> g"
      with 2(1) stmt_def show ?thesis using stmt.psimps(2) g_def by simp
    next
      assume "\<not> gas st \<le> g"
      define st' where "st' = st\<lparr>gas := gas st - g\<rparr>"
      show ?thesis
      proof (cases "expr ex env cd st' (gas st - g)")
        case (n a g')
        define st'' where "st'' = st'\<lparr>gas := g'\<rparr>"
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
              proof (cases "lexp lv env cd st'' g'")
                case n2: (n a g'')
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
                        with stmt_def `\<not> gas st \<le> g` n Pair KValue Value n2 p1 LStackloc v2 show ?thesis using stmt.psimps(2)[OF 2(1)] g_def st'_def st''_def by simp
                      next
                        case s3: (Some v')
                        with 2(1) `\<not> gas st \<le> g` n Pair KValue Value n2 p1 LStackloc v2 s3
                        have "stmt (ASSIGN lv ex) env cd st = Normal ((), st''\<lparr>gas := g'', stack := updateStore l (KValue v') (stack st)\<rparr>)"
                          using stmt.psimps(2) g_def st'_def st''_def by simp
                        with stmt_def have "st6'= st''\<lparr>gas := g'', stack := updateStore l (KValue v') (stack st)\<rparr>" by simp
                        moreover from lexp_gas `\<not> gas st \<le> g` n2 p1 have "gas (st''\<lparr>gas := g'', stack := updateStore l (KValue v') (stack st)\<rparr>) \<le> gas (st'\<lparr>gas := g'\<rparr>)" using g_def st'_def by simp
                        moreover from msel_ssel_expr_load_rexp_gas(3)[of ex env cd st' "gas st - g"] `\<not> gas st \<le> g` n Pair KValue Value have "gas (st'\<lparr>gas := g'\<rparr>) \<le> gas (st\<lparr>gas := gas st - g\<rparr>)" using g_def by simp
                        ultimately show ?thesis by simp
                      qed
                    next
                      case (Calldata x2)
                      with 2(1) stmt_def `\<not> gas st \<le> g` n Pair KValue Value n2 p1 LStackloc show ?thesis using stmt.psimps(2) g_def st'_def st''_def by simp
                    next
                      case (Memory x3)
                      with 2(1) stmt_def `\<not> gas st \<le> g` n Pair KValue Value n2 p1 LStackloc show ?thesis using stmt.psimps(2) g_def st'_def st''_def by simp
                    next
                      case (Storage x4)
                      with 2(1) stmt_def `\<not> gas st \<le> g` n Pair KValue Value n2 p1 LStackloc show ?thesis using stmt.psimps(2) g_def st'_def st''_def by simp
                    qed
                  next
                    case (LMemloc l)
                    then show ?thesis
                    proof (cases b)
                      case v2: (Value t')
                      with 2(1) stmt_def `\<not> gas st \<le> g` n Pair KValue Value n2 p1 LMemloc show ?thesis using stmt.psimps(2) g_def st'_def st''_def by simp
                    next
                      case (Calldata x2)
                      with 2(1) stmt_def `\<not> gas st \<le> g` n Pair KValue Value n2 p1 LMemloc show ?thesis using stmt.psimps(2) g_def st'_def st''_def by simp
                    next
                      case (Memory x3)
                      then show ?thesis
                      proof (cases x3)
                        case (MTArray x11 x12)
                        with 2(1) stmt_def `\<not> gas st \<le> g` n Pair KValue Value n2 p1 LMemloc Memory show ?thesis using stmt.psimps(2) g_def st'_def st''_def by simp
                      next
                        case (MTValue t')
                        then show ?thesis
                        proof (cases "convert t t' v ")
                          case None
                          with 2(1) stmt_def `\<not> gas st \<le> g` n Pair KValue Value n2 p1 LMemloc Memory MTValue show ?thesis using stmt.psimps(2) g_def st'_def st''_def by simp
                        next
                          case s3: (Some v')
                          with 2(1) `\<not> gas st \<le> g` n Pair KValue Value n2 p1 LMemloc Memory MTValue s3
                          have "stmt (ASSIGN lv ex) env cd st = Normal ((), st''\<lparr>gas := g'', memory := updateStore l (MValue v') (memory st'')\<rparr>)"
                            using stmt.psimps(2) g_def st'_def st''_def by simp
                          with stmt_def have "st6'= (st''\<lparr>gas := g'', memory := updateStore l (MValue v') (memory st'')\<rparr>)" by simp
                          moreover from lexp_gas `\<not> gas st \<le> g` n2 p1 have "gas (st''\<lparr>gas := g'', stack := updateStore l (KValue v') (stack st)\<rparr>) \<le> gas (st'\<lparr>gas := g'\<rparr>)" using g_def st'_def by simp
                          moreover from msel_ssel_expr_load_rexp_gas(3)[of ex env cd st' "gas st - g"] `\<not> gas st \<le> g` n Pair KValue Value n2 p1 have "gas (st'\<lparr>gas := g'\<rparr>) \<le> gas (st\<lparr>gas := gas st - g\<rparr>)" using g_def by simp
                          ultimately show ?thesis by simp
                        qed
                      qed
                    next
                      case (Storage x4)
                      with 2(1) stmt_def `\<not> gas st \<le> g` n Pair KValue Value n2 p1 LMemloc show ?thesis using stmt.psimps(2) g_def st'_def st''_def by simp
                    qed
                  next
                    case (LStoreloc l)
                    then show ?thesis
                    proof (cases b)
                      case v2: (Value t')
                      with 2(1) stmt_def `\<not> gas st \<le> g` n Pair KValue Value n2 p1 LStoreloc show ?thesis using stmt.psimps(2) g_def st'_def st''_def by simp
                    next
                      case (Calldata x2)
                      with 2(1) stmt_def `\<not> gas st \<le> g` n Pair KValue Value n2 p1 LStoreloc show ?thesis using stmt.psimps(2) g_def st'_def st''_def by simp
                    next
                      case (Memory x3)
                      with 2(1) stmt_def `\<not> gas st \<le> g` n Pair KValue Value n2 p1 LStoreloc show ?thesis using stmt.psimps(2) g_def st'_def st''_def by simp
                    next
                      case (Storage x4)
                      then show ?thesis
                      proof (cases x4)
                        case (STArray x11 x12)
                        with 2(1) stmt_def `\<not> gas st \<le> g` n Pair KValue Value n2 p1 LStoreloc Storage show ?thesis using stmt.psimps(2) g_def st'_def st''_def by simp
                      next
                        case (STMap x21 x22)
                        with 2(1) stmt_def `\<not> gas st \<le> g` n Pair KValue Value n2 p1 LStoreloc Storage show ?thesis using stmt.psimps(2) g_def st'_def st''_def by simp
                      next
                        case (STValue t')
                        then show ?thesis
                        proof (cases "convert t t' v ")
                          case None
                          with 2(1) stmt_def `\<not> gas st \<le> g` n Pair KValue Value n2 p1 LStoreloc Storage STValue show ?thesis using stmt.psimps(2) g_def st'_def st''_def by simp
                        next
                          case s3: (Some v')
                          with 2(1) `\<not> gas st \<le> g` n Pair KValue Value n2 p1 LStoreloc Storage STValue s3
                          have "stmt (ASSIGN lv ex) env cd st = Normal ((), st'' \<lparr>gas := g'', storage := (storage st'') (address env := fmupd l v' (storage st'' (address env)))\<rparr>)"
                            using stmt.psimps(2) g_def st'_def st''_def by simp
                          with stmt_def have "st6'= st'' \<lparr>gas := g'', storage := (storage st'') (address env := fmupd l v' (storage st'' (address env)))\<rparr>" by simp
                          moreover from lexp_gas `\<not> gas st \<le> g` n Pair KValue Value n2 p1 have "gas (st''\<lparr>gas := g'', stack := updateStore l (KValue v') (stack st)\<rparr>) \<le> gas (st'\<lparr>gas := g'\<rparr>)" using g_def by simp
                          moreover from msel_ssel_expr_load_rexp_gas(3)[of ex env cd st' "gas st - g"] `\<not> gas st \<le> g` n Pair KValue Value n2 p1 have "gas (st'\<lparr>gas := g'\<rparr>) \<le> gas (st\<lparr>gas := gas st - g\<rparr>)" using g_def by simp
                          ultimately show ?thesis by simp
                        qed
                      qed
                    qed
                  qed
                qed
              next
                case (e x)
                with 2(1) stmt_def `\<not> gas st \<le> g` n Pair KValue Value show ?thesis using stmt.psimps(2) g_def st'_def st''_def by simp
              qed
            next
              case (Calldata x2)
              with 2(1) stmt_def `\<not> gas st \<le> g` n Pair KValue show ?thesis using stmt.psimps(2) g_def st'_def by simp
            next
              case (Memory x3)
              with 2(1) stmt_def `\<not> gas st \<le> g` n Pair KValue show ?thesis using stmt.psimps(2) g_def st'_def by simp
            next
              case (Storage x4)
              with 2(1) stmt_def `\<not> gas st \<le> g` n Pair KValue show ?thesis using stmt.psimps(2) g_def st'_def by simp
            qed
          next
            case (KCDptr p)
            then show ?thesis
            proof (cases c)
              case (Value x1)
              with 2(1) stmt_def `\<not> gas st \<le> g` n Pair KCDptr show ?thesis using stmt.psimps(2) g_def st'_def by simp
            next
              case (Calldata x2)
              then show ?thesis
              proof (cases x2)
                case (MTArray x t)
                then show ?thesis
                proof (cases "lexp lv env cd st'' g'")
                  case n2: (n a g'')
                  define st''' where "st''' = st''\<lparr>gas := g''\<rparr>"
                  then show ?thesis
                  proof (cases a)
                    case p2: (Pair a b)
                    then show ?thesis
                    proof (cases a)
                      case (LStackloc l)
                      then show ?thesis
                      proof (cases b)
                        case v2: (Value t')
                        with 2(1) stmt_def `\<not> gas st \<le> g` n Pair KCDptr Calldata MTArray n2 p2 LStackloc show ?thesis using stmt.psimps(2) g_def st'_def st''_def by simp
                      next
                        case c2: (Calldata x2)
                        with 2(1) stmt_def `\<not> gas st \<le> g` n Pair KCDptr Calldata MTArray n2 p2 LStackloc show ?thesis using stmt.psimps(2) g_def st'_def st''_def by simp
                      next
                        case (Memory x3)
                        then show ?thesis
                        proof (cases "accessStore l (stack st''')")
                          case None
                          with 2(1) stmt_def `\<not> gas st \<le> g` n Pair KCDptr Calldata MTArray n2 p2 LStackloc Memory show ?thesis using stmt.psimps(2) g_def st'_def st''_def st'''_def by simp
                        next
                          case s3: (Some a)
                          then show ?thesis
                          proof (cases a)
                            case (KValue x1)
                            with 2(1) stmt_def `\<not> gas st \<le> g` n Pair KCDptr Calldata MTArray n2 p2 LStackloc Memory s3 show ?thesis using stmt.psimps(2) g_def st'_def st''_def st'''_def by simp
                          next
                            case c3: (KCDptr x2)
                            with 2(1) stmt_def `\<not> gas st \<le> g` n Pair KCDptr Calldata MTArray n2 p2 LStackloc Memory s3 show ?thesis using stmt.psimps(2) g_def st'_def st''_def st'''_def by simp
                          next
                            case (KMemptr p')
                            then show ?thesis
                            proof (cases "cpm2m p p' x t cd (memory st''')")
                              case None
                              with 2(1) stmt_def `\<not> gas st \<le> g` n Pair KCDptr Calldata MTArray n2 p2 LStackloc Memory s3 KMemptr show ?thesis using stmt.psimps(2) g_def st'_def st''_def st'''_def by (simp split:if_split_asm)
                            next
                              case (Some m')
                              with `\<not> gas st \<le> g` n Pair KCDptr Calldata MTArray n2 p2 LStackloc Memory s3 KMemptr
                              have "stmt (ASSIGN lv ex) env cd st = Normal ((), st''' \<lparr>memory := m'\<rparr>)"
                                using stmt.psimps(2)[OF 2(1)] g_def st'_def st''_def st'''_def by simp
                              with stmt_def have "st6'= st''' \<lparr>memory := m'\<rparr>" by simp
                              moreover from lexp_gas `\<not> gas st \<le> g` n Pair KCDptr Calldata MTArray n2 p2 have "gas (st'''\<lparr>memory := m'\<rparr>) \<le> gas st''" using st''_def st'''_def by simp
                              moreover from msel_ssel_expr_load_rexp_gas(3)[of ex env cd st' "gas st - g"] `\<not> gas st \<le> g` n Pair have "gas st'' \<le> gas st'" using st'_def st''_def by simp
                              ultimately show ?thesis using st'_def by simp
                            qed
                          next
                            case (KStoptr p')
                            with 2(1) stmt_def `\<not> gas st \<le> g` n Pair KCDptr Calldata MTArray n2 p2 LStackloc Memory s3 show ?thesis using stmt.psimps(2) g_def st'_def st''_def st'''_def by simp
                          qed
                        qed
                      next
                        case (Storage x4)
                        then show ?thesis
                        proof (cases "accessStore l (stack st'')")
                          case None
                          with 2(1) stmt_def `\<not> gas st \<le> g` n Pair KCDptr Calldata MTArray n2 p2 LStackloc Storage show ?thesis using stmt.psimps(2) g_def st'_def st''_def st'''_def by simp
                        next
                          case s3: (Some a)
                          then show ?thesis
                          proof (cases a)
                            case (KValue x1)
                            with 2(1) stmt_def `\<not> gas st \<le> g` n Pair KCDptr Calldata MTArray n2 p2 LStackloc Storage s3 show ?thesis using stmt.psimps(2) g_def st'_def st''_def st'''_def by simp
                          next
                            case c3: (KCDptr x2)
                            with 2(1) stmt_def `\<not> gas st \<le> g` n Pair KCDptr Calldata MTArray n2 p2 LStackloc Storage s3 show ?thesis using stmt.psimps(2) g_def st'_def st''_def st'''_def by simp
                          next
                            case (KMemptr x3)
                            with 2(1) stmt_def `\<not> gas st \<le> g` n Pair KCDptr Calldata MTArray n2 p2 LStackloc Storage s3 show ?thesis using stmt.psimps(2) g_def st'_def st''_def st'''_def by simp
                          next
                            case (KStoptr p')
                            then show ?thesis
                            proof (cases "cpm2s p p' x t cd (storage st'' (address env))")
                              case None
                              with 2(1) stmt_def `\<not> gas st \<le> g` n Pair KCDptr Calldata MTArray n2 p2 LStackloc Storage s3 KStoptr show ?thesis using stmt.psimps(2) g_def st'_def st''_def st'''_def by simp
                            next
                              case (Some s')
                              with 2(1) `\<not> gas st \<le> g` n Pair KCDptr Calldata MTArray n2 p2 LStackloc Storage s3 KStoptr
                              have "stmt (ASSIGN lv ex) env cd st = Normal ((), st''' \<lparr>storage := (storage st'') (address env := s')\<rparr>)"
                                using stmt.psimps(2) g_def st'_def st''_def st'''_def by simp
                              with stmt_def have "st6'= st''' \<lparr>storage := (storage st'') (address env := s')\<rparr>" by simp
                              moreover from lexp_gas `\<not> gas st \<le> g` n Pair KCDptr Calldata MTArray n2 p2 have "gas st''' \<le> gas st''" using g_def st''_def st'''_def by simp
                              moreover from msel_ssel_expr_load_rexp_gas(3)[of ex env cd st' "gas st - g"] `\<not> gas st \<le> g` n Pair have "gas st'' \<le> gas st'" using g_def st'_def st''_def by simp
                              ultimately show ?thesis using st'_def by simp
                            qed
                          qed
                        qed
                      qed
                    next
                      case (LMemloc l)
                      then show ?thesis
                      proof (cases "cpm2m p l x t cd (memory st''')")
                        case None
                        with 2(1) stmt_def `\<not> gas st \<le> g` n Pair KCDptr Calldata MTArray n2 p2 LMemloc show ?thesis using stmt.psimps(2) g_def st'_def st''_def st'''_def by (simp split:if_split_asm)
                      next
                        case (Some m)
                        with `\<not> gas st \<le> g` n Pair KCDptr Calldata MTArray n2 p2 LMemloc
                        have "stmt (ASSIGN lv ex) env cd st = Normal ((), st'''\<lparr>memory := m\<rparr>)"
                          using stmt.psimps(2)[OF 2(1)] g_def st'_def st''_def st'''_def by simp
                        with stmt_def have "st6'= (st'''\<lparr>memory := m\<rparr>)" by simp
                        moreover from lexp_gas `\<not> gas st \<le> g` n Pair KCDptr Calldata MTArray n2 p2 have "gas st''' \<le> gas st''" using st''_def st'''_def by simp
                        moreover from msel_ssel_expr_load_rexp_gas(3)[of ex env cd st' "gas st - g"] `\<not> gas st \<le> g` n Pair have "gas st'' \<le> gas st'" using st'_def st''_def by simp
                        ultimately show ?thesis using st'_def by simp
                      qed
                    next
                      case (LStoreloc l)
                      then show ?thesis
                      proof (cases "cpm2s p l x t cd (storage st'' (address env))")
                        case None
                        with 2(1) stmt_def `\<not> gas st \<le> g` n Pair KCDptr Calldata MTArray n2 p2 LStoreloc show ?thesis using stmt.psimps(2) g_def st'_def st''_def st'''_def by simp
                      next
                        case (Some s)
                        with `\<not> gas st \<le> g` n Pair KCDptr Calldata MTArray n2 p2 LStoreloc
                        have "stmt (ASSIGN lv ex) env cd st = Normal ((), st''' \<lparr>storage := (storage st'') (address env := s)\<rparr>)"
                          using stmt.psimps(2)[OF 2(1)] g_def st'_def st''_def st'''_def by simp
                        with stmt_def have "st6'= (st'''\<lparr>storage := (storage st'') (address env := s)\<rparr>)" by simp
                        moreover from lexp_gas `\<not> gas st \<le> g` n Pair KCDptr Calldata MTArray n2 p2 have "gas st''' \<le> gas st''" using st''_def st'''_def by simp
                        moreover from msel_ssel_expr_load_rexp_gas(3)[of ex env cd st' "gas st - g"] `\<not> gas st \<le> g` n Pair have "gas st'' \<le> gas st'" using st'_def st''_def by simp
                        ultimately show ?thesis using st'_def by simp
                      qed
                    qed
                  qed
                next
                  case (e x)
                  with 2(1) stmt_def `\<not> gas st \<le> g` n Pair KCDptr Calldata MTArray show ?thesis using stmt.psimps(2) g_def st'_def st''_def by simp
                qed
              next
                case (MTValue x2)
                with 2(1) stmt_def `\<not> gas st \<le> g` n Pair KCDptr Calldata show ?thesis using stmt.psimps(2) g_def st'_def st''_def by simp
              qed
            next
              case (Memory x3)
              with 2(1) stmt_def `\<not> gas st \<le> g` n Pair KCDptr show ?thesis using stmt.psimps(2) g_def st'_def st''_def by simp
            next
              case (Storage x4)
              with 2(1) stmt_def `\<not> gas st \<le> g` n Pair KCDptr show ?thesis using stmt.psimps(2) g_def st'_def st''_def by simp
            qed
          next
            case (KMemptr p)
            then show ?thesis
            proof (cases c)
              case (Value x1)
              with 2(1) stmt_def `\<not> gas st \<le> g` n Pair KMemptr show ?thesis using stmt.psimps(2) g_def st'_def st''_def by simp
            next
              case (Calldata x2)
              with 2(1) stmt_def `\<not> gas st \<le> g` n Pair KMemptr show ?thesis using stmt.psimps(2) g_def st'_def st''_def by simp
            next
              case (Memory x3)
              then show ?thesis
              proof (cases x3)
                case (MTArray x t)
                then show ?thesis
                proof (cases "lexp lv env cd st'' g'")
                  case n2: (n a g'')
                  define st''' where "st''' = st''\<lparr>gas := g''\<rparr>"
                  then show ?thesis
                  proof (cases a)
                    case p2: (Pair a b)
                    then show ?thesis
                    proof (cases a)
                      case (LStackloc l)
                      then show ?thesis
                      proof (cases b)
                        case v2: (Value t')
                        with 2(1) stmt_def `\<not> gas st \<le> g` n Pair KMemptr Memory MTArray n2 p2 LStackloc show ?thesis using stmt.psimps(2) g_def st'_def st''_def by simp
                      next
                        case c2: (Calldata x2)
                        with 2(1) stmt_def `\<not> gas st \<le> g` n Pair KMemptr Memory MTArray n2 p2 LStackloc show ?thesis using stmt.psimps(2) g_def st'_def st''_def by simp
                      next
                        case m2: (Memory x3)
                        with 2(1) `\<not> gas st \<le> g` n Pair KMemptr Memory MTArray n2 p2 LStackloc
                        have "stmt (ASSIGN lv ex) env cd st = Normal ((), st'''\<lparr>stack := updateStore l (KMemptr p) (stack st'')\<rparr>)"
                          using stmt.psimps(2)[OF 2(1)] g_def st'_def st''_def st'''_def by simp
                        with stmt_def have "st6'= st'''\<lparr>stack := updateStore l (KMemptr p) (stack st'')\<rparr>" by simp
                        moreover from lexp_gas `\<not> gas st \<le> g` n Pair KMemptr Memory MTArray n2 p2 have "gas st''' \<le> gas st''" using st''_def st'''_def by simp
                        moreover from msel_ssel_expr_load_rexp_gas(3)[of ex env cd st' "gas st - g"] `\<not> gas st \<le> g` n Pair have "gas st'' \<le> gas st'" using st'_def st''_def by simp
                        ultimately show ?thesis using st'_def by simp
                      next
                        case (Storage x4)
                        then show ?thesis
                        proof (cases "accessStore l (stack st''')")
                          case None
                          with 2(1) stmt_def `\<not> gas st \<le> g` n Pair KMemptr Memory MTArray n2 p2 LStackloc Storage show ?thesis using stmt.psimps(2) g_def st'_def st''_def st'''_def by simp
                        next
                          case s3: (Some a)
                          then show ?thesis
                          proof (cases a)
                            case (KValue x1)
                            with 2(1) stmt_def `\<not> gas st \<le> g` n Pair KMemptr Memory MTArray n2 p2 LStackloc Storage s3 show ?thesis using stmt.psimps(2) g_def st'_def st''_def st'''_def by simp
                          next
                            case c3: (KCDptr x2)
                            with 2(1) stmt_def `\<not> gas st \<le> g` n Pair KMemptr Memory MTArray n2 p2 LStackloc Storage s3 show ?thesis using stmt.psimps(2) g_def st'_def st''_def st'''_def by simp
                          next
                            case m3: (KMemptr x3)
                            with 2(1) stmt_def `\<not> gas st \<le> g` n Pair KMemptr Memory MTArray n2 p2 LStackloc Storage s3 show ?thesis using stmt.psimps(2) g_def st'_def st''_def st'''_def by simp
                          next
                            case (KStoptr p')
                            then show ?thesis
                            proof (cases "cpm2s p p' x t (memory st''') (storage st''' (address env))")
                              case None
                              with 2(1) stmt_def `\<not> gas st \<le> g` n Pair KMemptr Memory MTArray n2 p2 LStackloc Storage s3 KStoptr show ?thesis using stmt.psimps(2) g_def st'_def st''_def st'''_def by simp
                            next
                              case (Some s)
                              with 2(1) `\<not> gas st \<le> g` n Pair KMemptr Memory MTArray n2 p2 LStackloc Storage s3 KStoptr
                              have "stmt (ASSIGN lv ex) env cd st = Normal ((), st'''\<lparr>storage := (storage st''') (address env := s)\<rparr>)"
                                using stmt.psimps(2) g_def st'_def st''_def st'''_def by simp
                              with stmt_def have "st6'= st'''\<lparr>storage := (storage st''') (address env := s)\<rparr>" by simp
                              moreover from lexp_gas `\<not> gas st \<le> g` n Pair KMemptr Memory MTArray n2 p2 have "gas st''' \<le> gas st''" using g_def st'_def st''_def st'''_def by simp
                              moreover from msel_ssel_expr_load_rexp_gas(3)[of ex env cd st' "gas st - g"] `\<not> gas st \<le> g` n Pair have "gas st'' \<le> gas st'" using st'_def st''_def by simp
                              ultimately show ?thesis using st'_def by simp
                            qed
                          qed
                        qed
                      qed
                    next
                      case (LMemloc l)
                      with 2(1) `\<not> gas st \<le> g` n Pair KMemptr Memory MTArray n2 p2 LMemloc
                      have "stmt (ASSIGN lv ex) env cd st =  Normal ((), st'''\<lparr>memory := updateStore l (MPointer p) (memory st''')\<rparr>)"
                        using stmt.psimps(2) g_def st'_def st''_def st'''_def by simp
                      with stmt_def have "st6'= st'''\<lparr>memory := updateStore l (MPointer p) (memory st''')\<rparr>" by simp
                      moreover from lexp_gas `\<not> gas st \<le> g` n Pair KMemptr Memory MTArray n2 p2 have "gas st''' \<le> gas st''" using g_def st'_def st''_def st'''_def by simp
                      moreover from msel_ssel_expr_load_rexp_gas(3)[of ex env cd st' "gas st - g"] `\<not> gas st \<le> g` n Pair have "gas st'' \<le> gas st'" using st'_def st''_def by simp
                      ultimately show ?thesis using st'_def by simp
                    next
                      case (LStoreloc l)
                      then show ?thesis
                      proof (cases "cpm2s p l x t (memory st''') (storage st'' (address env))")
                        case None
                        with 2(1) stmt_def `\<not> gas st \<le> g` n Pair KMemptr Memory MTArray n2 p2 LStoreloc show ?thesis using stmt.psimps(2) g_def using st'_def st''_def st'''_def by simp
                      next
                        case (Some s)
                        with 2(1) `\<not> gas st \<le> g` n Pair KMemptr Memory MTArray n2 p2 LStoreloc
                        have "stmt (ASSIGN lv ex) env cd st =  Normal ((), st'''\<lparr>storage := (storage st''') (address env := s)\<rparr>)"
                          using stmt.psimps(2) g_def st'_def st''_def st'''_def by simp
                        with stmt_def have "st6'= st'''\<lparr>storage := (storage st''') (address env := s)\<rparr>" by simp
                        moreover from lexp_gas `\<not> gas st \<le> g` n Pair KMemptr Memory MTArray n2 p2 have "gas st''' \<le> gas st''" using g_def st'_def st''_def st'''_def by simp
                        moreover from msel_ssel_expr_load_rexp_gas(3)[of ex env cd st' "gas st - g"] `\<not> gas st \<le> g` n Pair have "gas st'' \<le> gas st'" using st'_def st''_def by simp
                        ultimately show ?thesis using st'_def by simp
                      qed
                    qed
                  qed
                next
                  case (e _)
                  with 2(1) stmt_def `\<not> gas st \<le> g` n Pair KMemptr Memory MTArray show ?thesis using stmt.psimps(2) g_def st'_def st''_def by simp
                qed
              next
                case (MTValue _)
                with 2(1) stmt_def `\<not> gas st \<le> g` n Pair KMemptr Memory show ?thesis using stmt.psimps(2) g_def st'_def st''_def by simp
              qed
            next
              case (Storage x4)
              with 2(1) stmt_def `\<not> gas st \<le> g` n Pair KMemptr show ?thesis using stmt.psimps(2) g_def st'_def st''_def by simp
            qed
          next
            case (KStoptr p)
            then show ?thesis
            proof (cases c)
              case (Value x1)
              with 2(1) stmt_def `\<not> gas st \<le> g` n Pair KStoptr show ?thesis using stmt.psimps(2) g_def st'_def st''_def by simp
            next
              case (Calldata x2)
              with 2(1) stmt_def `\<not> gas st \<le> g` n Pair KStoptr show ?thesis using stmt.psimps(2) g_def st'_def st''_def by simp
            next
              case (Memory x3)
              with 2(1) stmt_def `\<not> gas st \<le> g` n Pair KStoptr show ?thesis using stmt.psimps(2) g_def st'_def st''_def by simp
            next
              case (Storage x4)
              then show ?thesis
              proof (cases x4)
                case (STArray x t)
                then show ?thesis
                proof (cases "lexp lv env cd st'' g'")
                  case n2: (n a g'')
                  define st''' where "st''' = st''\<lparr>gas := g''\<rparr>"
                  then show ?thesis
                  proof (cases a)
                    case p2: (Pair a b)
                    then show ?thesis
                    proof (cases a)
                      case (LStackloc l)
                      then show ?thesis
                      proof (cases b)
                        case v2: (Value t')
                        with 2(1) stmt_def `\<not> gas st \<le> g` n Pair KStoptr Storage STArray n2 p2 LStackloc show ?thesis using stmt.psimps(2) g_def st'_def st''_def by simp
                      next
                        case c2: (Calldata x2)
                        with 2(1) stmt_def `\<not> gas st \<le> g` n Pair KStoptr Storage STArray n2 p2 LStackloc show ?thesis using stmt.psimps(2) g_def st'_def st''_def by simp
                      next
                        case (Memory x3)
                        then show ?thesis
                        proof (cases "accessStore l (stack st''')")
                          case None
                          with 2(1) stmt_def `\<not> gas st \<le> g` n Pair KStoptr Storage STArray n2 p2 LStackloc Memory show ?thesis using stmt.psimps(2) g_def st'_def st''_def st'''_def by simp
                        next
                          case s3: (Some a)
                          then show ?thesis
                          proof (cases a)
                            case (KValue x1)
                            with 2(1) stmt_def `\<not> gas st \<le> g` n Pair KStoptr Storage STArray n2 p2 LStackloc Memory s3 show ?thesis using stmt.psimps(2) g_def st'_def st''_def st'''_def by simp
                          next
                            case c3: (KCDptr x2)
                            with 2(1) stmt_def `\<not> gas st \<le> g` n Pair KStoptr Storage STArray n2 p2 LStackloc Memory s3 show ?thesis using stmt.psimps(2) g_def st'_def st''_def st'''_def by simp
                          next
                            case (KMemptr p')
                            then show ?thesis
                            proof (cases "cps2m p p' x t (storage st''' (address env)) (memory st''')")
                              case None
                              with 2(1) stmt_def `\<not> gas st \<le> g` n Pair KStoptr Storage STArray n2 p2 LStackloc Memory s3 KMemptr show ?thesis using stmt.psimps(2) g_def st'_def st''_def st'''_def by simp
                            next
                              case (Some m)
                              with 2(1) `\<not> gas st \<le> g` n Pair KStoptr Storage STArray n2 p2 LStackloc Memory s3 KMemptr
                              have "stmt (ASSIGN lv ex) env cd st =  Normal ((), st'''\<lparr>memory := m\<rparr>)"
                                using stmt.psimps(2) g_def st'_def st''_def st'''_def by simp
                              with stmt_def have "st6'= st'''\<lparr>memory := m\<rparr>" by simp
                              moreover from lexp_gas `\<not> gas st \<le> g` n Pair KMemptr Storage STArray n2 p2 have "gas (st'''\<lparr>memory := m\<rparr>) \<le> gas st''" using g_def st'_def st''_def st'''_def by simp
                              moreover from msel_ssel_expr_load_rexp_gas(3)[of ex env cd st' "gas st - g"] `\<not> gas st \<le> g` n Pair have "gas st'' \<le> gas st'" using st'_def st''_def by simp
                              ultimately show ?thesis using st'_def by simp
                            qed
                          next
                            case sp2: (KStoptr p')
                            with 2(1) stmt_def `\<not> gas st \<le> g` n Pair KStoptr Storage STArray n2 p2 LStackloc Memory s3 show ?thesis using stmt.psimps(2) g_def st'_def st''_def st'''_def by simp
                          qed
                        qed
                      next
                        case st2: (Storage x4)
                        with 2(1) `\<not> gas st \<le> g` n Pair KStoptr Storage STArray n2 p2 LStackloc
                        have "stmt (ASSIGN lv ex) env cd st =  Normal ((), st'''\<lparr>stack := updateStore l (KStoptr p) (stack st''')\<rparr>)"
                          using stmt.psimps(2) g_def st'_def st''_def st'''_def by simp
                        with stmt_def have "st6'= st'''\<lparr>stack := updateStore l (KStoptr p) (stack st''')\<rparr>" by simp
                        moreover from lexp_gas `\<not> gas st \<le> g` n Pair KStoptr Storage STArray n2 p2 have "gas (st'''\<lparr>stack := updateStore l (KStoptr p) (stack st''')\<rparr>) \<le> gas st''" using g_def st'_def st''_def st'''_def by simp
                        moreover from msel_ssel_expr_load_rexp_gas(3)[of ex env cd st' "gas st - g"] `\<not> gas st \<le> g` n Pair have "gas st'' \<le> gas st'" using st'_def st''_def by simp
                        ultimately show ?thesis using st'_def by simp
                      qed
                    next
                      case (LMemloc l)
                      then show ?thesis
                      proof (cases "cps2m p l x t (storage st'' (address env)) (memory st'')")
                        case None
                        with 2(1) stmt_def `\<not> gas st \<le> g` n Pair KStoptr Storage STArray n2 p2 LMemloc show ?thesis using stmt.psimps(2) g_def st'_def st''_def st'''_def by simp
                      next
                        case (Some m)
                        with 2(1) `\<not> gas st \<le> g` n Pair KStoptr Storage STArray n2 p2 LMemloc
                        have "stmt (ASSIGN lv ex) env cd st =  Normal ((), st'''\<lparr>memory := m\<rparr>)"
                          using stmt.psimps(2) g_def st'_def st''_def st'''_def by simp
                        with stmt_def have "st6'= (st'''\<lparr>memory := m\<rparr>)" by simp
                        moreover from lexp_gas `\<not> gas st \<le> g` n Pair KStoptr Storage STArray n2 p2 have "gas (st'''\<lparr>memory := m\<rparr>) \<le> gas st''" using g_def st'_def st''_def st'''_def by simp
                        moreover from msel_ssel_expr_load_rexp_gas(3)[of ex env cd st' "gas st - g"] `\<not> gas st \<le> g` n Pair have "gas st'' \<le> gas st'" using st'_def st''_def by simp
                        ultimately show ?thesis using st'_def by simp
                      qed
                    next
                      case (LStoreloc l)
                      then show ?thesis
                      proof (cases "copy p l x t (storage st'' (address env))")
                        case None
                        with 2(1) stmt_def `\<not> gas st \<le> g` n Pair KStoptr Storage STArray n2 p2 LStoreloc show ?thesis using stmt.psimps(2) g_def st'_def st''_def st'''_def by simp
                      next
                        case (Some s)
                        with 2(1) `\<not> gas st \<le> g` n Pair KStoptr Storage STArray n2 p2 LStoreloc
                        have "stmt (ASSIGN lv ex) env cd st = Normal ((), st'''\<lparr>storage := (storage st''') (address env := s)\<rparr>)"
                          using stmt.psimps(2) g_def st'_def st''_def st'''_def by simp
                        with stmt_def have "st6'= st'''\<lparr>storage := (storage st''') (address env := s)\<rparr>" by simp
                        moreover from lexp_gas `\<not> gas st \<le> g` n Pair KStoptr Storage STArray n2 p2 have "gas (st'''\<lparr>storage := (storage st''') (address env := s')\<rparr>) \<le> gas st''" using g_def st'_def st''_def st'''_def by simp
                        moreover from msel_ssel_expr_load_rexp_gas(3)[of ex env cd st' "gas st - g"] `\<not> gas st \<le> g` n Pair have "gas st'' \<le> gas st'" using st'_def st''_def by simp
                        ultimately show ?thesis using st'_def by simp
                      qed
                    qed
                  qed
                next
                  case (e x)
                  with 2(1) stmt_def `\<not> gas st \<le> g` n Pair KStoptr Storage STArray show ?thesis using stmt.psimps(2) g_def st'_def st''_def by simp
                qed
              next
                case (STMap t t')
                then show ?thesis
                proof (cases "lexp lv env cd st'' g'")
                  case n2: (n a g'')
                  define st''' where "st''' = st''\<lparr>gas := g''\<rparr>"
                  then show ?thesis
                  proof (cases a)
                    case p2: (Pair a b)
                    then show ?thesis
                    proof (cases a)
                      case (LStackloc l)
                      with 2(1) `\<not> gas st \<le> g` n Pair KStoptr Storage STMap n2 p2
                      have "stmt (ASSIGN lv ex) env cd st = Normal ((), st''' \<lparr>stack := updateStore l (KStoptr p) (stack st''')\<rparr>)"
                        using stmt.psimps(2) g_def st'_def st''_def st'''_def by simp
                      with stmt_def have "st6'= st'''\<lparr>stack := updateStore l (KStoptr p) (stack st''')\<rparr>" by simp
                      moreover from lexp_gas `\<not> gas st \<le> g` n Pair KStoptr Storage STMap n2 p2 have "gas (st'''\<lparr>stack := updateStore l (KStoptr p) (stack st''')\<rparr>) \<le> gas st''" using g_def st'_def st''_def st'''_def by simp
                      moreover from msel_ssel_expr_load_rexp_gas(3)[of ex env cd st' "gas st - g"] `\<not> gas st \<le> g` n Pair have "gas st'' \<le> gas st'" using st'_def st''_def by simp
                      ultimately show ?thesis using st'_def by simp
                    next
                      case (LMemloc x2)
                      with 2(1) stmt_def `\<not> gas st \<le> g` n Pair KStoptr Storage STMap n2 p2 show ?thesis using stmt.psimps(2) g_def st'_def st''_def by simp
                    next
                      case (LStoreloc x3)
                      with 2(1) stmt_def `\<not> gas st \<le> g` n Pair KStoptr Storage STMap n2 p2 show ?thesis using stmt.psimps(2) g_def st'_def st''_def by simp
                    qed
                  qed
                next
                  case (e x)
                  with 2(1) stmt_def `\<not> gas st \<le> g` n Pair KStoptr Storage STMap show ?thesis using stmt.psimps(2) g_def st'_def st''_def by simp
                qed
              next
                case (STValue x3)
                with 2(1) stmt_def `\<not> gas st \<le> g` n Pair KStoptr Storage show ?thesis using stmt.psimps(2) g_def st'_def st''_def by simp
              qed
            qed
          qed
        qed
      next
        case (e x)
        with 2(1) stmt_def `\<not> gas st \<le> g` show ?thesis using stmt.psimps(2) g_def st'_def by simp
      qed
    qed
  qed
next
  case (3 s1 s2 e cd st)
  define g where "g = costs (COMP s1 s2) e cd st"
  show ?case
  proof (rule allI[OF impI])
    fix st6'
    assume stmt_def: "stmt (COMP s1 s2) e cd st = Normal ((), st6')"
    then show "gas st6' \<le> gas st"
    proof cases
      assume "gas st \<le> g"
      with 3(1) stmt_def g_def show ?thesis using stmt.psimps(3) by simp
    next
      assume "\<not> gas st \<le> g"
      show ?thesis
      proof (cases "stmt s1 e cd (st\<lparr>gas := gas st - g\<rparr>)")
        case (n a st')
        with 3(1) stmt_def `\<not> gas st \<le> g` have "stmt (COMP s1 s2) e cd st = stmt s2 e cd st'" using stmt.psimps(3)[of s1 s2 e cd st] g_def by (simp add:Let_def split:unit.split_asm)
        with 3(3) stmt_def \<open>\<not> gas st \<le> g\<close> n have "gas st6' \<le> gas st'" using g_def by simp
        moreover from 3(2)[where ?s'a="st\<lparr>gas := gas st - g\<rparr>"] \<open>\<not> gas st \<le> g\<close> n have "gas st' \<le> gas st" using g_def by simp
        ultimately show ?thesis by simp
      next
        case (e x)
        with 3 stmt_def `\<not> gas st \<le> g` show ?thesis using stmt.psimps(3)[of s1 s2 e cd st] g_def by (simp split: Ex.split_asm)
      qed
    qed
  qed
next
  case (4 ex s1 s2 e cd st)
  define g where "g = costs (ITE ex s1 s2) e cd st"
  show ?case
  proof (rule allI[OF impI])
    fix st6'
    assume stmt_def: "stmt (ITE ex s1 s2) e cd st = Normal ((), st6')"
    then show "gas st6' \<le> gas st"
    proof cases
      assume "gas st \<le> g"
      with 4(1) stmt_def show ?thesis using stmt.psimps(4) g_def by simp
    next
      assume "\<not> gas st \<le> g"
      then have l1: "assert Gas (\<lambda>st. costs (ITE ex s1 s2) e cd st < gas st) st = Normal ((), st) " using g_def by simp
      define st' where "st' = st\<lparr>gas := gas st - g\<rparr>"
      then have l2: " modify (\<lambda>st. st\<lparr>gas := gas st - costs (ITE ex s1 s2) e cd st\<rparr>) st = Normal ((), st')" using g_def by simp
      show ?thesis
      proof (cases "expr ex e cd st' (gas st - g)")
        case (n a g')
        define st'' where "st'' = st'\<lparr>gas := g'\<rparr>"
        with n have l3: "toState (expr ex e cd) st' = Normal (a, st'')" using st'_def by simp
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
                with 4(1) stmt_def `\<not> gas st \<le> g` n Pair KValue Value show ?thesis using stmt.psimps(4) g_def st'_def by simp
              next
                case (TUInt x2)
                with 4(1) stmt_def `\<not> gas st \<le> g` n Pair KValue Value show ?thesis using stmt.psimps(4) g_def st'_def by simp
              next
                case TBool
                then show ?thesis
                proof cases
                  assume "b = ShowL\<^sub>b\<^sub>o\<^sub>o\<^sub>l True"
                  with 4(1) `\<not> gas st \<le> g` n Pair KValue Value TBool have "stmt (ITE ex s1 s2) e cd st = stmt s1 e cd st''" using stmt.psimps(4) g_def st'_def st''_def by simp
                  with 4(2)[OF l1 l2 l3] stmt_def `\<not> gas st \<le> g` n Pair KValue Value TBool `b = ShowL\<^sub>b\<^sub>o\<^sub>o\<^sub>l True` have "gas st6' \<le> gas st''" using g_def by simp
                  moreover from msel_ssel_expr_load_rexp_gas(3)[of ex e cd st' "gas st - g"] `\<not> gas st \<le> g` n Pair KValue Value TBool have "gas st'' \<le> gas st'" using st'_def st''_def by simp
                  ultimately show ?thesis using st'_def by simp
                next
                  assume nt: "\<not> b = ShowL\<^sub>b\<^sub>o\<^sub>o\<^sub>l True"
                  show ?thesis
                  proof cases
                    assume "b = ShowL\<^sub>b\<^sub>o\<^sub>o\<^sub>l False"
                    with 4(1) `\<not> gas st \<le> g` n Pair KValue Value TBool nt have "stmt (ITE ex s1 s2) e cd st = stmt s2 e cd st''" using stmt.psimps(4) g_def st'_def st''_def by simp
                    with 4(3)[OF l1 l2 l3] stmt_def `\<not> gas st \<le> g` n Pair KValue Value TBool nt `b = ShowL\<^sub>b\<^sub>o\<^sub>o\<^sub>l False` have "gas st6' \<le> gas st''" using g_def by simp
                    moreover from msel_ssel_expr_load_rexp_gas(3)[of ex e cd st' "gas st - g"] `\<not> gas st \<le> g` n Pair KValue Value TBool have "gas st'' \<le> gas st'" using st'_def st''_def by simp
                    ultimately show ?thesis using st'_def by simp
                  next
                    assume "\<not> b = ShowL\<^sub>b\<^sub>o\<^sub>o\<^sub>l False"
                    with 4(1) stmt_def `\<not> gas st \<le> g` n Pair KValue Value TBool nt show ?thesis using stmt.psimps(4) g_def st'_def st''_def by simp
                  qed
                qed
              next
                case TAddr
                with 4(1) stmt_def `\<not> gas st \<le> g` n Pair KValue Value show ?thesis using stmt.psimps(4) g_def st'_def st''_def by simp
              qed
            next
              case (Calldata x2)
              with 4(1) stmt_def `\<not> gas st \<le> g` n Pair KValue show ?thesis using stmt.psimps(4) g_def st'_def st''_def by simp
            next
              case (Memory x3)
              with 4(1) stmt_def `\<not> gas st \<le> g` n Pair KValue show ?thesis using stmt.psimps(4) g_def st'_def st''_def by simp
            next
              case (Storage x4)
              with 4(1) stmt_def `\<not> gas st \<le> g` n Pair KValue show ?thesis using stmt.psimps(4) g_def st'_def st''_def by simp
            qed
          next
            case (KCDptr x2)
            with 4(1) stmt_def `\<not> gas st \<le> g` n Pair show ?thesis using stmt.psimps(4) g_def st'_def st''_def by simp
          next
            case (KMemptr x3)
            with 4(1) stmt_def `\<not> gas st \<le> g` n Pair show ?thesis using stmt.psimps(4) g_def st'_def st''_def by simp
          next
            case (KStoptr x4)
            with 4(1) stmt_def `\<not> gas st \<le> g` n Pair show ?thesis using stmt.psimps(4) g_def st'_def st''_def by simp
          qed
        qed
      next
        case (e e)
        with 4(1) stmt_def `\<not> gas st \<le> g` show ?thesis using stmt.psimps(4) g_def st'_def by simp
      qed
    qed
  qed
next
  case (5 ex s0 e cd st)
  define g where "g = costs (WHILE ex s0) e cd st"
  show ?case
  proof (rule allI[OF impI])
    fix st6'
    assume stmt_def: "stmt (WHILE ex s0) e cd st = Normal ((), st6')"
    then show "gas st6' \<le> gas st"
    proof cases
      assume "gas st \<le> g"
      with 5(1) stmt_def show ?thesis using stmt.psimps(5) g_def by simp
    next
      assume gcost: "\<not> gas st \<le> g"
      then have l1: "assert Gas (\<lambda>st. costs (WHILE ex s0) e cd st < gas st) st = Normal ((), st) " using g_def by simp
      define st' where "st' = st\<lparr>gas := gas st - g\<rparr>"
      then have l2: " modify (\<lambda>st. st\<lparr>gas := gas st - costs (WHILE ex s0) e cd st\<rparr>) st = Normal ((), st')" using g_def by simp
      show ?thesis
      proof (cases "expr ex e cd st' (gas st - g)")
        case (n a g')
        define st'' where "st'' = st'\<lparr>gas := g'\<rparr>"
        with n have l3: "toState (expr ex e cd) st' = Normal (a, st'')" using st'_def by simp
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
                with 5(1) stmt_def gcost n Pair KValue Value show ?thesis using stmt.psimps(5) g_def st'_def by simp
              next
                case (TUInt x2)
                with 5(1) stmt_def gcost n Pair KValue Value show ?thesis using stmt.psimps(5) g_def st'_def by simp
              next
                case TBool
                then show ?thesis
                proof cases
                  assume "b = ShowL\<^sub>b\<^sub>o\<^sub>o\<^sub>l True"
                  then show ?thesis
                  proof (cases "stmt s0 e cd st''")
                    case n2: (n a st''')
                    with 5(1) gcost n Pair KValue Value TBool `b = ShowL\<^sub>b\<^sub>o\<^sub>o\<^sub>l True` have "stmt (WHILE ex s0) e cd st = stmt (WHILE ex s0) e cd st'''" using stmt.psimps(5)[of ex s0 e cd st] g_def st'_def st''_def by (simp add: Let_def split:unit.split_asm)
                    with 5(3) stmt_def gcost n2 Pair KValue Value TBool `b = ShowL\<^sub>b\<^sub>o\<^sub>o\<^sub>l True` n have "gas st6' \<le> gas st'''" using g_def st'_def st''_def by simp
                    moreover from 5(2)[OF l1 l2 l3] gcost n2 Pair KValue Value TBool `b = ShowL\<^sub>b\<^sub>o\<^sub>o\<^sub>l True` n have "gas st''' \<le> gas st''" using g_def by simp
                    moreover from msel_ssel_expr_load_rexp_gas(3)[of ex e cd st' "gas st - g"] `\<not> gas st \<le> g` n Pair KValue Value TBool have "gas st'' \<le> gas st'" using st'_def st''_def by simp
                    ultimately show ?thesis using st'_def by simp
                  next
                    case (e x)
                    with 5(1) stmt_def gcost n Pair KValue Value TBool `b = ShowL\<^sub>b\<^sub>o\<^sub>o\<^sub>l True` show ?thesis using stmt.psimps(5) g_def st'_def st''_def by simp
                  qed
                next
                  assume nt: "\<not> b = ShowL\<^sub>b\<^sub>o\<^sub>o\<^sub>l True"
                  show ?thesis
                  proof cases
                    assume "b = ShowL\<^sub>b\<^sub>o\<^sub>o\<^sub>l False"
                    with 5(1) gcost n Pair KValue Value TBool nt have "stmt (WHILE ex s0) e cd st = return () st''" using stmt.psimps(5) g_def st'_def st''_def by simp
                    with stmt_def have "gas st6' \<le> gas st''" by simp
                    moreover from msel_ssel_expr_load_rexp_gas(3)[of ex e cd st' "gas st - g"] `\<not> gas st \<le> g` n Pair KValue Value TBool have "gas st'' \<le> gas st'" using st'_def st''_def by simp
                    ultimately show ?thesis using g_def st'_def st''_def by simp
                  next
                    assume "\<not> b = ShowL\<^sub>b\<^sub>o\<^sub>o\<^sub>l False"
                    with 5(1) stmt_def gcost n Pair KValue Value TBool nt show ?thesis using stmt.psimps(5) g_def st'_def st''_def by simp
                  qed
                qed
              next
                case TAddr
                with 5(1) stmt_def gcost n Pair KValue Value show ?thesis using stmt.psimps(5) g_def st'_def st''_def by simp
              qed
            next
              case (Calldata x2)
              with 5(1) stmt_def gcost n Pair KValue show ?thesis using stmt.psimps(5) g_def st'_def st''_def by simp
            next
              case (Memory x3)
              with 5(1) stmt_def gcost n Pair KValue show ?thesis using stmt.psimps(5) g_def st'_def st''_def by simp
            next
              case (Storage x4)
              with 5(1) stmt_def gcost n Pair KValue show ?thesis using stmt.psimps(5) g_def st'_def st''_def by simp
            qed
          next
            case (KCDptr x2)
            with 5(1) stmt_def gcost n Pair show ?thesis using stmt.psimps(5) g_def st'_def st''_def by simp
          next
            case (KMemptr x3)
            with 5(1) stmt_def gcost n Pair show ?thesis using stmt.psimps(5) g_def st'_def st''_def by simp
          next
            case (KStoptr x4)
            with 5(1) stmt_def gcost n Pair show ?thesis using stmt.psimps(5) g_def st'_def st''_def by simp
          qed
        qed
      next
        case (e e)
        with 5(1) stmt_def gcost show ?thesis using stmt.psimps(5) g_def st'_def by simp
      qed
    qed
  qed
next
  case (6 i xe e cd st)
  define g where "g = costs (INVOKE i xe) e cd st"
  show ?case
  proof (rule allI[OF impI])
    fix st6' assume a1: "stmt (INVOKE i xe) e cd st = Normal ((), st6')"
    show "gas st6' \<le> gas st"
    proof (cases)
      assume "gas st \<le> g"
      with 6(1) a1 show ?thesis using stmt.psimps(6) g_def by simp
    next
      assume gcost: "\<not> gas st \<le> g"
      then have l1: "assert Gas (\<lambda>st. costs (INVOKE i xe) e cd st < gas st) st = Normal ((), st) " using g_def by simp
      define st' where "st' = st\<lparr>gas := gas st - g\<rparr>"
      then have l2: "modify (\<lambda>st. st\<lparr>gas := gas st - costs (INVOKE i xe) e cd st\<rparr>) st = Normal ((), st')" using g_def by simp
      then show ?thesis
      proof (cases "ep $$ contract e")
        case None
        with 6(1) a1 gcost show ?thesis using stmt.psimps(6) g_def by simp
      next
        case (Some x)
        then have l3: "option Err (\<lambda>_. ep $$ contract e) st' = Normal (x, st')" by simp
        then show ?thesis
        proof (cases x)
          case (fields ct _ _)
          then show ?thesis
          proof (cases "fmlookup ct i")
            case None
            with 6(1) g_def a1 gcost Some fields show ?thesis using stmt.psimps(6) by simp
          next
            case s1: (Some a)
            then show ?thesis
            proof (cases a)
              case (Method x1)
              then show ?thesis
              proof (cases x1)
                case p1: (fields fp ext f)
                then show ?thesis
                proof (cases ext)
                  case True
                  with 6(1) a1 g_def gcost Some fields s1 Method p1 show ?thesis using stmt.psimps(6) st'_def by auto
                next
                  case False
                  then have l4: "(case ct $$ i of None \<Rightarrow> throw Err | Some (Method (fp, True, f)) \<Rightarrow> throw Err
                       | Some (Method (fp, False, f)) \<Rightarrow> return (fp, f) | Some _ \<Rightarrow> throw Err) st' = Normal ((fp,f),st')" using s1 Method p1 by simp
                  define m\<^sub>o e'
                  where "m\<^sub>o = memory st'"
                    and "e' = ffold (init ct) (emptyEnv (address e) (contract e) (sender e) (svalue e)) (fmdom ct)"
                  then show ?thesis
                  proof (cases "load False fp xe e' emptyStore emptyStore m\<^sub>o e cd st' (gas st - g)")
                    case s4: (n a g')
                    define st'' where "st'' = st'\<lparr>gas := g'\<rparr>"
                    then show ?thesis
                    proof (cases a)
                      case f2: (fields e\<^sub>l cd\<^sub>l k\<^sub>l m\<^sub>l)
                      then have l5: "toState (load False fp xe e' emptyStore emptyStore m\<^sub>o e cd) st' = Normal ((e\<^sub>l, cd\<^sub>l, k\<^sub>l, m\<^sub>l), st'')" using st'_def st''_def s4 by simp
                      define k\<^sub>o where "k\<^sub>o = stack st'"
                      then show ?thesis
                      proof (cases "stmt f e\<^sub>l cd\<^sub>l (st''\<lparr>stack:=k\<^sub>l, memory:=m\<^sub>l\<rparr>)")
                        case n2: (n a st''')
                        with  a1 g_def gcost Some fields s1 Method p1 m\<^sub>o_def e'_def s4 f2 k\<^sub>o_def False
                        have "stmt (INVOKE i xe) e cd st = Normal ((), st'''\<lparr>stack:=k\<^sub>o\<rparr>)"
                          using stmt.psimps(6)[OF 6(1)] st'_def st''_def by auto
                        with a1 have "gas st6' \<le> gas st'''" by auto
                        also from 6(2)[OF l1 l2 l3 fields l4 _ _ _ l5, where ?s'g="st''\<lparr>stack := k\<^sub>l, memory := m\<^sub>l\<rparr>"] n2 m\<^sub>o_def e'_def
                          have "\<dots> \<le> gas st''" by auto
                        also from msel_ssel_expr_load_rexp_gas(4)[of False fp xe e' emptyStore emptyStore m\<^sub>o e cd st' "(gas st - g)"] have "\<dots> \<le> gas st'" using s4 st'_def st''_def f2 by auto
                        finally show ?thesis using st'_def by simp
                      next
                        case (e x)
                        with 6(1) a1 g_def gcost Some fields s1 Method p1 m\<^sub>o_def e'_def s4 f2 show ?thesis using stmt.psimps(6) st'_def st''_def False by auto
                      qed
                    qed
                  next
                    case (e x)
                    with 6(1) a1 g_def gcost Some fields s1 Method p1 m\<^sub>o_def e'_def show ?thesis using stmt.psimps(6) st'_def False by auto
                  qed
                qed
              qed
            next
              case (Function _)
              with 6(1) g_def a1 gcost Some fields s1 show ?thesis using stmt.psimps(6) by simp
            next
              case (Var _)
              with 6(1) g_def a1 gcost Some fields s1 show ?thesis using stmt.psimps(6) by simp
            qed
          qed
        qed
      qed
    qed
  qed
next
  case (7 ad i xe val e cd st)
  define g where "g = costs (EXTERNAL ad i xe val) e cd st"
  show ?case
  proof (rule allI[OF impI])
    fix st6' assume a1: "stmt (EXTERNAL ad i xe val) e cd st = Normal ((), st6')"
    show "gas st6' \<le> gas st"
    proof (cases)
      assume "gas st \<le> g"
      with 7(1) a1 show ?thesis using stmt.psimps(7) g_def by simp
    next
      assume gcost: "\<not> gas st \<le> g"
      then have l1: "assert Gas (\<lambda>st. costs (EXTERNAL ad i xe val) e cd st < gas st) st = Normal ((), st) " using g_def by simp
      define st' where "st' = st\<lparr>gas := gas st - g\<rparr>"
      then have l2: " modify (\<lambda>st. st\<lparr>gas := gas st - costs (EXTERNAL ad i xe val) e cd st\<rparr>) st = Normal ((), st')" using g_def by simp
      then show ?thesis
      proof (cases "expr ad e cd st' (gas st - g)")
        case (n a0 g')
        define st'' where "st'' = st'\<lparr>gas := g'\<rparr>"
        with n have l3: "toState (expr ad e cd) st' = Normal (a0, st'')" using st'_def by simp
        then show ?thesis
        proof (cases a0)
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
                with 7(1) g_def a1 gcost n Pair KValue Value show ?thesis using stmt.psimps(7) st'_def by auto
              next
                case (TUInt x2)
                with 7(1) g_def a1 gcost n Pair KValue Value show ?thesis using stmt.psimps(7) st'_def by auto
              next
                case TBool
                with 7(1) g_def a1 gcost n Pair KValue Value show ?thesis using stmt.psimps(7) st'_def by auto
              next
                case TAddr
                then have l4: "(case a0 of (KValue adv, Value TAddr) \<Rightarrow> return adv | (KValue adv, Value _) \<Rightarrow> throw Err | (KValue adv, _) \<Rightarrow> throw Err
                       | (_, b) \<Rightarrow> throw Err) st'' = Normal (adv, st'')" using Pair KValue Value by simp
                then show ?thesis
                proof (cases "adv = address e")
                  case True
                  with 7(1) g_def a1 gcost n Pair KValue Value TAddr show ?thesis using stmt.psimps(7) st'_def by auto
                next
                  case False
                  then have l5: "assert Err (\<lambda>_. adv \<noteq> address e) st'' = Normal ((), st'')" by simp
                  then show ?thesis
                  proof (cases "type (accounts st'' adv)")
                    case None
                    with 7(1) g_def a1 gcost n Pair KValue Value TAddr False show ?thesis using stmt.psimps(7) st'_def st''_def by auto
                  next
                    case (Some x2)
                    then show ?thesis
                    proof (cases x2)
                      case EOA
                      with 7(1) g_def a1 gcost n Pair KValue Value TAddr False Some show ?thesis using stmt.psimps(7) st'_def st''_def by auto
                    next
                      case (Contract c)
                      then have l6: "(\<lambda>st. case type (accounts st adv) of Some (Contract c) \<Rightarrow> return c st | _ \<Rightarrow> throw Err st) st'' = Normal (c, st'')" using Some by (simp split:atype.split option.split)
                      then show ?thesis
                      proof (cases "ep $$ c")
                        case None
                        with 7(1) g_def a1 gcost n Pair KValue Value TAddr False Contract Some show ?thesis using stmt.psimps(7) st'_def st''_def by auto
                      next
                        case s2: (Some x)
                        then show ?thesis
                        proof (cases x)
                          case p2: (fields ct x0 fb)
                          then have l7: "option Err (\<lambda>_. ep $$ c) st'' = Normal ((ct, x0, fb), st'')" using s2 by simp
                          then show ?thesis
                          proof (cases "expr val e cd st'' (gas st'')")
                            case n1: (n kv g'')
                            define st''' where "st''' = st''\<lparr>gas := g''\<rparr>"
                            with n1 have l8: "toState (expr val e cd) st'' = Normal (kv, st''')" by simp
                            then show ?thesis
                            proof (cases kv)
                              case p3: (Pair a b)
                              then show ?thesis
                              proof (cases a)
                                case k2: (KValue v)
                                then show ?thesis
                                proof (cases b)
                                  case v: (Value t)
                                  then have l9: "(case kv of (KValue v, Value t) \<Rightarrow> return (v, t) | (KValue v, _) \<Rightarrow> throw Err | (_, b) \<Rightarrow> throw Err) st''' = Normal ((v,t), st''')" using n1 p3 k2 by simp
                                  show ?thesis
                                  proof (cases "convert t (TUInt 256) v")
                                    case None
                                    with 7(1) g_def a1 gcost n Pair KValue Value TAddr False Contract Some s2 p2 None n1 p3 k2 v False show ?thesis using stmt.psimps(7)[OF 7(1)] st'_def st''_def st'''_def by simp
                                  next
                                    case s3: (Some v')
                                    define e' where "e' = ffold (init ct) (emptyEnv adv c (address e) v') (fmdom ct)"
                                    show ?thesis
                                    proof (cases "fmlookup ct i")
                                      case None
                                      show ?thesis
                                      proof (cases "transfer (address e) adv v' (accounts st''')")
                                        case n2: None
                                        with 7(1) g_def a1 gcost n Pair KValue Value TAddr False Contract Some s2 p2 None n1 p3 k2 v False s3 show ?thesis using stmt.psimps(7)[OF 7(1)] st'_def st''_def st'''_def by simp
                                      next
                                        case s4: (Some acc)
                                        then have l10: "option Err (\<lambda>st. transfer (address e) adv v' (accounts st)) st''' = Normal (acc, st''')" by simp
                                        define k\<^sub>o m\<^sub>o
                                          where "k\<^sub>o = stack st'''"
                                            and "m\<^sub>o = memory st'''"
                                        show ?thesis
                                        proof (cases "stmt fb e' emptyStore (st'''\<lparr>accounts := acc, stack:=emptyStore, memory:=emptyStore\<rparr>)")
                                          case n2: (n a st'''')
                                          with g_def a1 gcost n Pair KValue Value TAddr False Contract Some s2 p2 None n1 p3 k2 v s4
                                          have "stmt (EXTERNAL ad i xe val) e cd st = Normal ((), st''''\<lparr>stack:=stack st''', memory := memory st'''\<rparr>)"
                                            using stmt.psimps(7)[OF 7(1)] st'_def st''_def st'''_def e'_def False s3 by simp
                                          with a1 have "gas st6' \<le> gas st''''" by auto
                                          also from 7(3)[OF l1 l2 l3 l4 l5 l6 l7 _ _ l8 l9 _ _ _ None l10, where ?s'k="st'''" and ?s'l="st'''\<lparr>accounts := acc,stack:=emptyStore, memory:=emptyStore\<rparr>" and ?x=e', of "(x0,fb)" x0 fb] n2 
                                            have "\<dots> \<le> gas (st'''\<lparr>accounts := acc,stack:=emptyStore, memory:=emptyStore\<rparr>)" using e'_def s3 by simp
                                          also from msel_ssel_expr_load_rexp_gas(3)[of val e cd st'' "gas st''"]
                                            have "\<dots> \<le> gas st''" using n1 st'_def st''_def st'''_def p3 by simp
                                          also from msel_ssel_expr_load_rexp_gas(3)[of  ad e cd st' "gas st - g"]
                                            have "\<dots> \<le> gas st'" using n st'_def st''_def st'''_def p3 by fastforce
                                          finally show ?thesis using st'_def by simp
                                        next
                                          case (e x)
                                          with 7(1) g_def a1 gcost n Pair KValue Value TAddr False Some s2 Contract p2 None n1 p3 k2 v s4 s3 show ?thesis using stmt.psimps(7)[of ad i xe val e cd st] st'_def st''_def st'''_def e'_def by simp
                                        qed
                                      qed
                                    next
                                      case s1: (Some a)
                                      then show ?thesis
                                      proof (cases a)
                                        case (Method x1)
                                        then show ?thesis
                                        proof (cases x1)
                                          case p4: (fields fp ext f)
                                          then show ?thesis
                                          proof (cases ext)
                                            case True
                                            then show ?thesis
                                            proof (cases "load True fp xe e' emptyStore emptyStore emptyStore e cd st''' (gas st''')")
                                              case s4: (n a g''')
                                              define st'''' where "st'''' = st'''\<lparr>gas := g'''\<rparr>"
                                              then show ?thesis
                                              proof (cases a)
                                                case f1: (fields e\<^sub>l cd\<^sub>l k\<^sub>l m\<^sub>l)
                                                then have l10: "toState (load True fp xe e' emptyStore emptyStore emptyStore e cd) st''' = Normal ((e\<^sub>l, cd\<^sub>l, k\<^sub>l, m\<^sub>l), st'''')" using s4 st''''_def by simp
                                                show ?thesis
                                                proof (cases "transfer (address e) adv v' (accounts st'''')")
                                                  case n2: None
                                                  with 7(1) g_def a1 gcost n Pair KValue Value TAddr False Some s2 Contract p2 s1 Method p4 n1 p3 k2 v s3 f1 e'_def True s4 show ?thesis using stmt.psimps(7)[of ad i xe val e cd st] st'_def st''_def st'''_def st''''_def by simp
                                                next
                                                  case s5: (Some acc)
                                                  then have l11: "option Err (\<lambda>st. transfer (address e) adv v' (accounts st)) st'''' = Normal (acc, st'''')" by simp
                                                  define k\<^sub>o where "k\<^sub>o = accounts st''''"
                                                  define m\<^sub>o where "m\<^sub>o = accounts st''''"
                                                  show ?thesis
                                                  proof (cases "stmt f e\<^sub>l cd\<^sub>l (st''''\<lparr>accounts := acc, stack:=k\<^sub>l,memory:=m\<^sub>l\<rparr>)")
                                                    case n2: (n a st''''')
                                                    with 7(1) g_def a1 gcost n Pair KValue Value TAddr Some s2 Contract p2 s1 Method p4 n1 p3 k2 v k\<^sub>o_def m\<^sub>o_def e'_def s3 f1 s4 s5
                                                    have "stmt (EXTERNAL ad i xe val) e cd st = Normal ((), st'''''\<lparr>stack:=stack st'''', memory := memory st''''\<rparr>)"
                                                      using stmt.psimps(7)[of ad i xe val e cd st] st'_def st''_def st'''_def st''''_def True False by simp
                                                    with a1 have "gas st6' \<le> gas st'''''" by auto
                                                    also from 7(2)[OF l1 l2 l3 l4 l5 l6 l7 _ _ l8 l9 _ _ _ s1 Method _ _ _ l10 _ _ _ l11, where ?s'm="st''''\<lparr>accounts := acc, stack := k\<^sub>l, memory := m\<^sub>l\<rparr>" and ?s'l=st''''] p4 n2 e'_def True s3
                                                      have "\<dots> \<le> gas (st''''\<lparr>accounts := acc, stack := k\<^sub>l, memory := m\<^sub>l\<rparr>)" by simp
                                                    also from msel_ssel_expr_load_rexp_gas(4)[of True fp xe e' emptyStore emptyStore emptyStore e cd st''' "gas st'''"]
                                                      have "\<dots> \<le> gas st'''" using s3 st'_def st''_def st'''_def st''''_def f1 s4 by simp
                                                    also from msel_ssel_expr_load_rexp_gas(3)[of val e cd st'' "gas st''"]
                                                      have "\<dots> \<le> gas st''" using n1 st'_def st''_def st'''_def by fastforce
                                                    also from msel_ssel_expr_load_rexp_gas(3)[of ad e cd st' "gas st - g"]
                                                      have "\<dots> \<le> gas st'" using n st'_def st''_def st'''_def by fastforce
                                                    finally show ?thesis using st'_def by simp
                                                  next
                                                    case (e x)
                                                    with 7(1) g_def a1 gcost n Pair KValue Value TAddr False Some s2 Contract p2 s1 Method p4 n1 p3 k2 v k\<^sub>o_def m\<^sub>o_def e'_def s3 f1 s4 s5 True show ?thesis using stmt.psimps(7) st'_def st''_def st'''_def st''''_def by simp
                                                  qed
                                                qed
                                              qed
                                            next
                                              case (e x)
                                              with 7(1) g_def a1 gcost n Pair KValue Value TAddr False Some s2 Contract p2 s1 Method p4 n1 p3 k2 v e'_def True s3 show ?thesis using stmt.psimps(7) st'_def st''_def st'''_def by simp
                                            qed
                                          next
                                            case f: False
                                            with 7(1) g_def a1 gcost n Pair KValue Value TAddr False Some s2 Contract p2 s1 Method p4 n1 p3 k2 v s3 show ?thesis using stmt.psimps(7) st'_def st''_def st'''_def by simp
                                          qed
                                        qed
                                      next
                                        case (Function _)
                                        with 7(1) g_def a1 gcost n Pair KValue Value TAddr False Some s2 Contract p2 s1 n1 p3 k2 v s3 show ?thesis using stmt.psimps(7) st'_def st''_def st'''_def by simp
                                      next
                                        case (Var _)
                                        with 7(1) g_def a1 gcost n Pair KValue Value TAddr False Some s2 Contract p2 s1 n1 p3 k2 v s3 show ?thesis using stmt.psimps(7) st'_def st''_def st'''_def by simp
                                      qed
                                    qed
                                  qed
                                next
                                  case (Calldata x2)
                                  with 7(1) g_def a1 gcost n Pair KValue Value TAddr False Some s2 Contract p2 n1 p3 k2 show ?thesis using stmt.psimps(7) st'_def st''_def st'''_def by simp
                                next
                                  case (Memory x3)
                                  with 7(1) g_def a1 gcost n Pair KValue Value TAddr False Some s2 Contract p2 n1 p3 k2 show ?thesis using stmt.psimps(7) st'_def st''_def st'''_def by simp
                                next
                                  case (Storage x4)
                                  with 7(1) g_def a1 gcost n Pair KValue Value TAddr False Some s2 Contract p2 n1 p3 k2 show ?thesis using stmt.psimps(7) st'_def st''_def st'''_def by simp
                                qed
                              next
                                case (KCDptr x2)
                                with 7(1) g_def a1 gcost n Pair KValue Value TAddr False Some s2 Contract p2 n1 p3 show ?thesis using stmt.psimps(7) st'_def st''_def st'''_def by simp
                              next
                                case (KMemptr x3)
                                with 7(1) g_def a1 gcost n Pair KValue Value TAddr False Some s2 Contract p2 n1 p3 show ?thesis using stmt.psimps(7) st'_def st''_def st'''_def by simp
                              next
                                case (KStoptr x4)
                                with 7(1) g_def a1 gcost n Pair KValue Value TAddr False Some s2 Contract p2 n1 p3 show ?thesis using stmt.psimps(7) st'_def st''_def st'''_def by simp
                              qed
                            qed
                          next
                            case n2: (e x)
                            with 7(1) g_def a1 gcost n Pair KValue Value TAddr False Some s2 Contract p2 show ?thesis using stmt.psimps(7) st'_def st''_def by simp
                          qed
                        qed
                      qed
                    qed
                  qed
                qed
              qed
            next
              case (Calldata x2)
              with 7(1) g_def a1 gcost n Pair KValue show ?thesis using stmt.psimps(7) st'_def st''_def by simp
            next
              case (Memory x3)
              with 7(1) g_def a1 gcost n Pair KValue show ?thesis using stmt.psimps(7) st'_def st''_def by simp
            next
              case (Storage x4)
              with 7(1) g_def a1 gcost n Pair KValue show ?thesis using stmt.psimps(7) st'_def st''_def by simp
            qed
          next
            case (KCDptr x2)
            with 7(1) g_def a1 gcost n Pair show ?thesis using stmt.psimps(7) st'_def st''_def by simp
          next
            case (KMemptr x3)
            with 7(1) g_def a1 gcost n Pair show ?thesis using stmt.psimps(7) st'_def st''_def by simp
          next
            case (KStoptr x4)
            with 7(1) g_def a1 gcost n Pair show ?thesis using stmt.psimps(7) st'_def st''_def by simp
          qed
        qed
      next
        case (e _)
        with 7(1) g_def a1 gcost show ?thesis using stmt.psimps(7) st'_def by simp
      qed
    qed
  qed
next
  case (8 ad ex e cd st)
  define g where "g = costs (TRANSFER ad ex) e cd st"
  show ?case
  proof (rule allI[OF impI])
    fix st6' assume stmt_def: "stmt (TRANSFER ad ex) e cd st = Normal ((), st6')"
    show "gas st6' \<le> gas st"
    proof cases
      assume "gas st \<le> g"
      with 8 stmt_def g_def show ?thesis using stmt.psimps(8)[of ad ex e cd st] by simp
    next
      assume "\<not> gas st \<le> g"
      then have l1: "assert Gas (\<lambda>st. costs (TRANSFER ad ex) e cd st < gas st) st = Normal ((), st) " using g_def by simp
      define st' where "st' = st\<lparr>gas := gas st - g\<rparr>"
      then have l2: " modify (\<lambda>st. st\<lparr>gas := gas st - costs (TRANSFER ad ex) e cd st\<rparr>) st = Normal ((), st')" using g_def by simp
      show ?thesis
      proof (cases "expr ad e cd st' (gas st - g)")
        case (n a0 g')
        define st'' where "st'' = st'\<lparr>gas := g'\<rparr>"
        with n have l3: "toState (expr ad e cd) st' = Normal (a0, st'')" using st'_def by simp
        then show ?thesis
        proof (cases a0)
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
                with 8(1) stmt_def `\<not> gas st \<le> g` n Pair KValue Value g_def show ?thesis using stmt.psimps(8) st'_def st''_def by simp
              next
                case (TUInt x2)
                with 8(1) stmt_def `\<not> gas st \<le> g` n Pair KValue Value g_def show ?thesis using stmt.psimps(8) st'_def st''_def by simp
              next
                case TBool
                with 8(1) stmt_def `\<not> gas st \<le> g` n Pair KValue Value g_def show ?thesis using stmt.psimps(8) st'_def st''_def by simp
              next
                case TAddr
                then have l4: "(case a0 of (KValue adv, Value TAddr) \<Rightarrow> return adv | (KValue adv, Value _) \<Rightarrow> throw Err | (KValue adv, _) \<Rightarrow> throw Err
                       | (_, b) \<Rightarrow> throw Err) st'' = Normal (adv, st'')" using Pair KValue Value by simp
                then show ?thesis
                proof (cases "expr ex e cd st'' (gas st'')")
                  case n2: (n a1 g'')
                  define st''' where "st''' = st''\<lparr>gas := g''\<rparr>"
                  with n2 have l5: "toState (expr ex e cd) st'' = Normal (a1, st''')" by simp
                  then show ?thesis
                  proof (cases a1)
                    case p2: (Pair b c)
                    then show ?thesis
                    proof (cases b)
                      case k2: (KValue v)
                      then show ?thesis
                      proof (cases c)
                        case v2: (Value t)
                        then have l6: "(case a1 of (KValue v, Value t) \<Rightarrow> return (v, t) | (KValue v, _) \<Rightarrow> throw Err | (_, b) \<Rightarrow> throw Err) st''' = Normal ((v,t), st''')" using p2 k2 by simp
                        then show ?thesis
                        proof (cases "convert t (TUInt 256) v")
                          case None
                          with 8(1) stmt_def g_def `\<not> gas st \<le> g` n Pair KValue Value n2 p2 k2 v2 TAddr show ?thesis using stmt.psimps(8) st'_def st''_def st'''_def by simp
                        next
                          case (Some v')
                          then show ?thesis
                          proof (cases "type (accounts st''' adv)")
                            case None
                            with 8(1) stmt_def g_def `\<not> gas st \<le> g` n Pair KValue Value n2 p2 k2 v2 TAddr Some show ?thesis using stmt.psimps(8) st'_def st''_def st'''_def by simp
                          next
                            case s0: (Some a)
                            then show ?thesis
                            proof (cases a)
                              case EOA
                              then show ?thesis
                              proof (cases "transfer (address e) adv v' (accounts st''')")
                                case None
                                with 8(1) stmt_def g_def `\<not> gas st \<le> g` n Pair KValue Value n2 p2 k2 v2 TAddr Some EOA s0 show ?thesis using stmt.psimps(8) st'_def st''_def st'''_def by simp
                              next
                                case s1: (Some acc)
                                then have l7: "option Err (\<lambda>st. transfer (address e) adv v' (accounts st)) st''' = Normal (acc, st''')" using st'''_def by simp
                                with 8(1) `\<not> gas st \<le> g` n Pair KValue Value n2 p2 k2 v2 TAddr Some EOA g_def s0
                                  have "stmt (TRANSFER ad ex) e cd st = Normal ((),st'''\<lparr>accounts:=acc\<rparr>)" using stmt.psimps(8)[of ad ex e cd st] st'_def st''_def st'''_def by simp
                                with stmt_def have "gas st6' = gas (st'''\<lparr>accounts:=acc\<rparr>)" by auto
                                also from msel_ssel_expr_load_rexp_gas(3)[of ex e cd st'' "gas st''"]
                                  have "\<dots> \<le> gas st''" using st'_def st''_def st'''_def n2 by fastforce
                                also from msel_ssel_expr_load_rexp_gas(3)[of ad e cd st' "gas st - g"]
                                  have "\<dots> \<le> gas st'" using st'_def st''_def n by fastforce
                                  finally show ?thesis using st'_def by simp
                              qed
                            next
                              case (Contract c)
                              then show ?thesis
                              proof (cases "ep $$ c")
                                case None
                                with 8(1) stmt_def g_def `\<not> gas st \<le> g` n Pair KValue Value n2 p2 k2 v2 TAddr Contract Some s0 show ?thesis using stmt.psimps(8) st'_def st''_def st'''_def by simp
                              next
                                case s2: (Some a)
                                then show ?thesis
                                proof (cases a)
                                  case p3: (fields ct cn f)
                                  with s2 have l7: "option Err (\<lambda>_. ep $$ c) st''' = Normal ((ct, cn, f), st''')" by simp
                                  define e' where "e' = ffold_init ct (emptyEnv adv c (address e) v') (fmdom ct)"
                                  show ?thesis
                                  proof (cases "transfer (address e) adv v' (accounts st''')")
                                    case None
                                    with 8(1) stmt_def g_def `\<not> gas st \<le> g` n Pair KValue Value n2 p2 k2 v2 TAddr Contract Some s2 p3 s0 show ?thesis using stmt.psimps(8) st'_def st''_def st'''_def by simp
                                  next
                                    case s3: (Some acc)
                                    then have l8: "option Err (\<lambda>st. transfer (address e) adv v' (accounts st)) st''' = Normal (acc, st''')" by simp
                                    then show ?thesis
                                    proof (cases "stmt f e' emptyStore (st'''\<lparr>accounts := acc, stack:=emptyStore, memory:=emptyStore\<rparr>)")
                                      case n3: (n a st'''')
                                      with 8(1) `\<not> gas st \<le> g` n Pair KValue Value n2 p2 k2 v2 TAddr Some s2 p3 g_def Contract s3 s0
                                      have "stmt (TRANSFER ad ex) e cd st = Normal ((),st''''\<lparr>stack:=stack st''', memory := memory st'''\<rparr>)" using e'_def stmt.psimps(8)[of ad ex e cd st] st'_def st''_def st'''_def by simp
                                      with stmt_def have "gas st6' \<le> gas st''''" by auto
                                      also from 8(2)[OF l1 l2 l3 l4 l5 l6, of v t _ _ "accounts st'''" "st'''", OF _ _ _ s0 Contract l7 _ _ _ _ _ l8, where ?s'k="st'''\<lparr>accounts := acc, stack := emptyStore, memory := emptyStore\<rparr>"] `\<not> gas st \<le> g` e'_def n3 Some
                                        have "\<dots> \<le> gas (st'''\<lparr>accounts := acc, stack := emptyStore, memory := emptyStore\<rparr>)" by simp
                                      also from msel_ssel_expr_load_rexp_gas(3)[of ex e cd st'' "gas st''"]
                                        have "\<dots> \<le> gas st''" using st'_def st''_def st'''_def n2 by fastforce
                                      also from msel_ssel_expr_load_rexp_gas(3)[of ad e cd st' "gas st - g"]
                                        have "\<dots> \<le> gas st'" using st'_def st''_def n by fastforce
                                      finally show ?thesis using st'_def by simp
                                    next
                                      case (e x)
                                      with 8(1) `\<not> gas st \<le> g` n Pair KValue Value n2 p2 k2 v2 TAddr Some s2 p3 g_def e'_def stmt_def Contract s3 s0 show ?thesis using stmt.psimps(8)[of ad ex e cd st] st'_def st''_def st'''_def by simp
                                    qed
                                  qed
                                qed
                              qed
                            qed
                          qed
                        qed
                      next
                        case (Calldata x2)
                        with 8(1) stmt_def `\<not> gas st \<le> g` n Pair KValue Value TAddr n2 p2 k2 g_def show ?thesis using stmt.psimps(8) st'_def st''_def st'''_def by simp
                      next
                        case (Memory x3)
                        with 8(1) stmt_def `\<not> gas st \<le> g` n Pair KValue Value TAddr n2 p2 k2 g_def show ?thesis using stmt.psimps(8) st'_def st''_def st'''_def by simp
                      next
                        case (Storage x4)
                        with 8(1) stmt_def `\<not> gas st \<le> g` n Pair KValue Value TAddr n2 p2 k2 g_def show ?thesis using stmt.psimps(8) st'_def st''_def st'''_def by simp
                      qed
                    next
                      case (KCDptr x2)
                      with 8(1) stmt_def `\<not> gas st \<le> g` n Pair KValue Value TAddr n2 p2 g_def show ?thesis using stmt.psimps(8) st'_def st''_def st'''_def by simp
                    next
                      case (KMemptr x3)
                      with 8(1) stmt_def `\<not> gas st \<le> g` n Pair KValue Value TAddr n2 p2 g_def show ?thesis using stmt.psimps(8) st'_def st''_def st'''_def by simp
                    next
                      case (KStoptr x4)
                      with 8(1) stmt_def `\<not> gas st \<le> g` n Pair KValue Value TAddr n2 p2 g_def show ?thesis using stmt.psimps(8) st'_def st''_def st'''_def by simp
                    qed
                  qed
                next
                  case (e e)
                  with 8(1) stmt_def `\<not> gas st \<le> g` n Pair KValue Value TAddr g_def show ?thesis using stmt.psimps(8) st'_def st''_def by simp
                qed
              qed
            next
              case (Calldata x2)
              with 8(1) stmt_def `\<not> gas st \<le> g` n Pair KValue g_def show ?thesis using stmt.psimps(8) st'_def st''_def by simp
            next
              case (Memory x3)
              with 8(1) stmt_def `\<not> gas st \<le> g` n Pair KValue g_def show ?thesis using stmt.psimps(8) st'_def st''_def by simp
            next
              case (Storage x4)
              with 8(1) stmt_def `\<not> gas st \<le> g` n Pair KValue g_def show ?thesis using stmt.psimps(8) st'_def st''_def by simp
            qed
          next
            case (KCDptr x2)
            with 8(1) stmt_def `\<not> gas st \<le> g` n Pair g_def show ?thesis using stmt.psimps(8) st'_def st''_def by simp
          next
            case (KMemptr x3)
            with 8(1) stmt_def `\<not> gas st \<le> g` n Pair g_def show ?thesis using stmt.psimps(8) st'_def st''_def by simp
          next
            case (KStoptr x4)
            with 8(1) stmt_def `\<not> gas st \<le> g` n Pair g_def show ?thesis using stmt.psimps(8) st'_def st''_def by simp
          qed
        qed
      next
        case (e e)
        with 8(1) stmt_def `\<not> gas st \<le> g` g_def show ?thesis using stmt.psimps(8) st'_def by simp
      qed
    qed
  qed
next
  case (9 id0 tp s e\<^sub>v cd st)
  define g where "g = costs (BLOCK ((id0, tp), None) s) e\<^sub>v cd st"
  show ?case
  proof (rule allI[OF impI])
    fix st6' assume stmt_def: "stmt (BLOCK ((id0, tp), None) s) e\<^sub>v cd st = Normal ((), st6')"
    show "gas st6' \<le> gas st"
    proof cases
      assume "gas st \<le> g"
      with 9 stmt_def g_def show ?thesis using stmt.psimps(9) by simp
    next
      assume "\<not> gas st \<le> g"
      then have l1: "assert Gas (\<lambda>st. costs (BLOCK ((id0, tp), None) s) e\<^sub>v cd st < gas st) st = Normal ((), st) " using g_def by simp
      define st' where "st' = st\<lparr>gas := gas st - g\<rparr>"
      then have l2: "modify (\<lambda>st. st\<lparr>gas := gas st - costs (BLOCK ((id0, tp), None) s) e\<^sub>v cd st\<rparr>) st = Normal ((), st')" using g_def by simp
      show ?thesis
      proof (cases "decl id0 tp None False cd (memory st') (storage st') (cd, (memory st'), (stack st'), e\<^sub>v)")
        case n2: None
        with 9 stmt_def `\<not> gas st \<le> g` g_def show ?thesis using stmt.psimps(9) st'_def by simp
      next
        case (Some a)
        then have l3: "option Err (\<lambda>st. decl id0 tp None False cd (memory st) (storage st) (cd, memory st, stack st, e\<^sub>v)) st' = Normal (a, st')" by simp
        then show ?thesis
        proof (cases a)
          case (fields cd' mem' sck' e')
          with 9(1) stmt_def `\<not> gas st \<le> g` g_def have "stmt (BLOCK ((id0, tp), None) s) e\<^sub>v cd st = stmt s e' cd' (st\<lparr>gas := gas st - g, stack := sck', memory := mem'\<rparr>)" using stmt.psimps(9)[OF 9(1)] Some st'_def by simp
          with 9(2)[OF l1 l2 l3] stmt_def `\<not> gas st \<le> g` fields g_def have "gas st6' \<le> gas (st\<lparr>gas := gas st - g, stack := sck', memory := mem'\<rparr>)" using st'_def by fastforce
          then show ?thesis by simp
        qed
      qed
    qed
  qed
next
  case (10 id0 tp ex' s e\<^sub>v cd st)
  define g where "g = costs (BLOCK ((id0, tp), Some ex') s) e\<^sub>v cd st"
  show ?case
  proof (rule allI[OF impI])
    fix st6' assume stmt_def: "stmt (BLOCK ((id0, tp), Some ex') s) e\<^sub>v cd st = Normal ((), st6')"
    show "gas st6' \<le> gas st"
    proof cases
      assume "gas st \<le> g"
      with 10 stmt_def g_def show ?thesis using stmt.psimps(10) by simp
    next
      assume "\<not> gas st \<le> g"
      then have l1: "assert Gas (\<lambda>st. costs (BLOCK ((id0, tp), Some ex') s) e\<^sub>v cd st < gas st) st = Normal ((), st) " using g_def by simp
      define st' where "st' = st\<lparr>gas := gas st - g\<rparr>"
      then have l2: "modify (\<lambda>st. st\<lparr>gas := gas st - costs (BLOCK ((id0, tp), Some ex') s) e\<^sub>v cd st\<rparr>) st = Normal ((), st')" using g_def by simp
      show ?thesis
      proof (cases "expr ex' e\<^sub>v cd st' (gas st - g)")
        case (n a g')
        define st'' where "st'' = st'\<lparr>gas := g'\<rparr>"
        with n have l3: "toState (expr ex' e\<^sub>v cd) st' = Normal (a, st'')" using st''_def st'_def by simp
        then show ?thesis
        proof (cases a)
          case (Pair v t)
          then show ?thesis
          proof (cases "decl id0 tp (Some (v, t)) False cd (memory st'') (storage st'') (cd, memory st'', stack st'', e\<^sub>v)")
            case None
            with 10(1) stmt_def `\<not> gas st \<le> g` n Pair g_def show ?thesis using stmt.psimps(10) st'_def st''_def by simp
          next
            case s2: (Some a)
            then have l4: "option Err (\<lambda>st. decl id0 tp (Some (v, t)) False cd (memory st) (storage st) (cd, memory st, stack st, e\<^sub>v)) st'' = Normal (a, st'')" by simp
            then show ?thesis
            proof (cases a)
              case (fields cd' mem' sck' e')
              with 10(1) stmt_def `\<not> gas st \<le> g` n Pair s2 g_def have "stmt (BLOCK ((id0, tp), Some ex') s) e\<^sub>v cd st = stmt s e' cd' (st''\<lparr>stack := sck', memory := mem'\<rparr>)" using stmt.psimps(10)[of id0 tp ex' s e\<^sub>v cd st] st'_def st''_def by simp
              with 10(2)[OF l1 l2 l3 Pair l4 fields, where s'd="st''\<lparr>stack := sck', memory := mem'\<rparr>"] n stmt_def `\<not> gas st \<le> g` s2 fields g_def have "gas st6' \<le> gas st''" by simp
              moreover from msel_ssel_expr_load_rexp_gas(3)[of ex' e\<^sub>v cd st' "gas st - g"] n have "gas st'' \<le> gas st'" using st'_def st''_def by fastforce
              ultimately show ?thesis using st'_def by simp
            qed
          qed
        qed
      next
        case (e e)
        with 10 stmt_def `\<not> gas st \<le> g` g_def show ?thesis using stmt.psimps(10) st'_def by simp
      qed
    qed
  qed
next
  case (11 i xe val e cd st)
  define g where "g = costs (NEW i xe val) e cd st"
  show ?case
  proof (rule allI[OF impI])
    fix st6' assume a1: "stmt (NEW i xe val) e cd st = Normal ((), st6')"
    show "gas st6' \<le> gas st"
    proof (cases)
      assume "gas st \<le> g"
      with 11(1) a1 show ?thesis using stmt.psimps(11) g_def by simp
    next
      assume gcost: "\<not> gas st \<le> g"
      then have l1: "assert Gas (\<lambda>st. costs (NEW i xe val) e cd st < gas st) st = Normal ((), st) " using g_def by simp
      define st' where "st' = st\<lparr>gas := gas st - g\<rparr>"
      then have l2: "modify (\<lambda>st. st\<lparr>gas := gas st - costs (NEW i xe val) e cd st\<rparr>) st = Normal ((), st')" using g_def by simp
      define adv where "adv = hash (address e) (ShowL\<^sub>n\<^sub>a\<^sub>t (contracts (accounts st' (address e))))"
      then show ?thesis
      proof (cases "type (accounts st' adv) = None")
        case True
        then show ?thesis
        proof (cases "expr val e cd st' (gas st')")
          case n0: (n kv g')
          define st'' where "st'' = st'\<lparr>gas := g'\<rparr>"
          then have l4: "toState (expr val e cd) st' = Normal (kv, st'')" using n0 by simp
          then show ?thesis
          proof (cases kv)
            case p0: (Pair a b)
            then show ?thesis
            proof (cases a)
              case k0: (KValue v)
              then show ?thesis
              proof (cases b)
                case v0: (Value t)
                then show ?thesis
                proof (cases "ep $$ i")
                  case None
                  with a1 gcost g_def True n0 p0 k0 v0
                  show ?thesis using stmt.psimps(11)[OF 11(1)] adv_def st'_def st''_def by simp
                next
                  case s0: (Some a)
                  then have l5: "option Err (\<lambda>_. ep $$ i) st'' = Normal (a, st'')" by simp
                  then show ?thesis
                  proof (cases a)
                    case f0: (fields ct cn _)
                    define e' where "e' = ffold_init ct (emptyEnv adv i (address e) v) (fmdom ct)"
                    then show ?thesis
                    proof (cases "load True (fst cn) xe e' emptyStore emptyStore emptyStore e cd st'' (gas st'')")
                      case n1: (n a g'')
                      define st''' where "st''' = st''\<lparr>gas := g''\<rparr>"
                      then have l6: "toState (load True (fst cn) xe e' emptyStore emptyStore emptyStore e cd) st'' = Normal (a, st''')" using n1 by simp
                      then show ?thesis
                      proof (cases a)
                        case f1: (fields e\<^sub>l cd\<^sub>l k\<^sub>l m\<^sub>l)
                        define st'''' where "st'''' = st'''\<lparr>accounts:=(accounts st''')(adv := \<lparr>bal = ShowL\<^sub>i\<^sub>n\<^sub>t 0, type = Some (Contract i), contracts = 0\<rparr>), storage:=(storage st''')(adv := {$$})\<rparr>"
                        then show ?thesis
                        proof (cases "transfer (address e) adv v (accounts st'''')")
                          case None
                          with a1 gcost g_def True n0 p0 k0 v0 s0 f0 n1 f1
                          show ?thesis using stmt.psimps(11)[OF 11(1)] adv_def e'_def st'_def st''_def st'''_def st''''_def by (simp add:Let_def)
                        next
                          case s1: (Some acc)
                          define st''''' where "st''''' = st''''\<lparr>accounts := acc, stack:=k\<^sub>l, memory:=m\<^sub>l\<rparr>"
                          then show ?thesis
                          proof (cases "stmt (snd cn) e\<^sub>l cd\<^sub>l st'''''")
                            case (n a st'''''')
                            define st''''''' where "st''''''' = st''''''\<lparr>stack:=stack st'''', memory := memory st''''\<rparr>"
                            define st'''''''' where "st'''''''' = incrementAccountContracts (address e) st'''''''"
                            from a1 gcost g_def True n0 p0 k0 v0 s0 f0 n1 f1 s1 n have "st6' = st''''''''"
                              using st'_def st''_def st'''_def st''''_def st'''''_def st'''''''_def st''''''''_def
                              stmt.psimps(11)[OF 11(1)] adv_def e'_def by (simp add:Let_def)
                            then have "gas st6' = gas st''''''''" by simp
                            also have "\<dots> \<le> gas st'''''''" using st''''''''_def incrementAccountContracts_def by simp
                            also have "\<dots> \<le> gas st''''''" using st'''''''_def by simp
                            also have "\<dots> \<le> gas st'''''" using 11(2)[OF l1 l2 _ _ l4 _ _ l5 _ _ e'_def l6, where ?s'h="st''''" and ?s'i="st''''" and ?s'j="st''''" and ?s'k="st''''\<lparr>accounts := acc, stack := k\<^sub>l, memory := m\<^sub>l\<rparr>", of st' "()"] p0 k0 v0 f0 f1 s1 n True st''''_def st'''''_def adv_def by simp
                            also have "\<dots> \<le> gas st''''" using st'''''_def by simp
                            also have "\<dots> \<le> gas st'''" using st''''_def by simp
                            also have "\<dots> \<le> gas st''" using st'''_def msel_ssel_expr_load_rexp_gas(4) n1 f1 by simp
                            also have "\<dots> \<le> gas st'" using st''_def msel_ssel_expr_load_rexp_gas(3) n0 p0 by simp
                            also have "\<dots> \<le> gas st" using st'_def by simp
                            finally show ?thesis .
                          next
                            case (e e)
                            with a1 gcost g_def n0 True p0 k0 v0 s0 f0 n1 f1 s1
                            show ?thesis using stmt.psimps(11)[OF 11(1)] adv_def e'_def st'_def st''_def st'''_def st''''_def st'''''_def by (simp add:Let_def)
                          qed
                        qed
                      qed
                    next
                      case (e e)
                      with a1 gcost g_def n0 True p0 k0 v0 s0 f0
                      show ?thesis using stmt.psimps(11)[OF 11(1)] adv_def e'_def st'_def st''_def by (simp add:Let_def)
                    qed
                  qed
                qed
              next
                case (Calldata x2)
                with a1 gcost g_def n0 True p0 k0
                show ?thesis using stmt.psimps(11)[OF 11(1)] adv_def st'_def by simp
              next
                case (Memory x3)
                with a1 gcost g_def n0 True p0 k0
                show ?thesis using stmt.psimps(11)[OF 11(1)] adv_def st'_def by simp
              next
                case (Storage x4)
                with a1 gcost g_def n0 True p0 k0
                show ?thesis using stmt.psimps(11)[OF 11(1)] adv_def st'_def by simp
              qed
            next
              case (KCDptr x2)
              with a1 gcost g_def n0 True p0
              show ?thesis using stmt.psimps(11)[OF 11(1)] adv_def st'_def by simp
            next
              case (KMemptr x3)
              with a1 gcost g_def n0 True p0
              show ?thesis using stmt.psimps(11)[OF 11(1)] adv_def st'_def by simp
            next
              case (KStoptr x4)
              with a1 gcost g_def n0 True p0
              show ?thesis using stmt.psimps(11)[OF 11(1)] adv_def st'_def by simp
            qed
          qed
        next
          case (e e)
          with a1 gcost g_def True
          show ?thesis using stmt.psimps(11)[OF 11(1)] adv_def st'_def by simp
        qed
      next
        case False
        with a1 gcost g_def
        show ?thesis using stmt.psimps(11)[OF 11(1)] adv_def st'_def by (simp split:if_split_asm)
      qed
    qed
  qed
qed

subsection \<open>Termination function\<close>

text \<open>Now we can prove termination using the lemma above.\<close>

fun sgas
  where "sgas l = gas (snd (snd (snd l)))"

fun ssize
  where "ssize l = size (fst l)"

method stmt_dom_gas =
  match premises in s: "stmt _ _ _ _ = Normal (_,_)" and d[thin]: "stmt_dom _" \<Rightarrow> \<open>insert stmt_dom_gas[OF d s]\<close>
method msel_ssel_expr_load_rexp =
  match premises in e[thin]: "expr _ _ _ _ _ = Normal (_,_)" \<Rightarrow> \<open>insert msel_ssel_expr_load_rexp_gas(3)[OF e]\<close> |
  match premises in l[thin]: "load _ _ _ _ _ _ _ _ _ _ _ = Normal (_,_)" \<Rightarrow> \<open>insert msel_ssel_expr_load_rexp_gas(4)[OF l, THEN conjunct1]\<close>
method costs =
  match premises in "costs (WHILE ex s0) e cd st < _" for ex s0 and e::Environment and cd::CalldataT and st::State \<Rightarrow> \<open>insert while_not_zero[of (unchecked) ex s0 e cd st]\<close> |
  match premises in "costs (INVOKE i xe) e cd st < _" for i xe and e::Environment and cd::CalldataT and st::State \<Rightarrow> \<open>insert invoke_not_zero[of (unchecked) i xe e cd st]\<close> |
  match premises in "costs (EXTERNAL ad i xe val) e cd st < _" for ad i xe val and e::Environment and cd::CalldataT and st::State \<Rightarrow> \<open>insert external_not_zero[of (unchecked) ad i xe val e cd st]\<close> |
  match premises in "costs (TRANSFER ad ex) e cd st < _" for ad ex and e::Environment and cd::CalldataT and st::State \<Rightarrow> \<open>insert transfer_not_zero[of (unchecked) ad ex e cd st]\<close> |
  match premises in "costs (NEW i xe val) e cd st < _" for i xe val and e::Environment and cd::CalldataT and st::State \<Rightarrow> \<open>insert new_not_zero[of (unchecked) i xe val e cd st]\<close>

termination stmt
  apply (relation "measures [sgas, ssize]")
  apply (auto split: if_split_asm result.split_asm Stackvalue.split_asm Type.split_asm Types.split_asm option.split_asm Member.split_asm bool.split_asm atype.split_asm)
  apply ((stmt_dom_gas | msel_ssel_expr_load_rexp)+, costs?, simp)+
  done

subsection \<open>Gas Reduction\<close>

text \<open>
  The following corollary is a generalization of @{thm [source] msel_ssel_expr_load_rexp_dom_gas}.
  We first prove that the function is defined for all input values and then obtain the final result as a corollary.
\<close>
lemma stmt_dom: "stmt_dom (s6, ev6, cd6, st6)"
  apply (induct rule: stmt.induct[where ?P="\<lambda>s6 ev6 cd6 st6. stmt_dom (s6, ev6, cd6, st6)"])
  apply (simp_all add: stmt.domintros(1-10))
  apply (rule stmt.domintros(11), force)
  done

lemmas stmt_gas = stmt_dom_gas[OF stmt_dom]

lemma skip:
  assumes "stmt SKIP ev cd st = Normal (x, st')"
    shows "gas st > costs SKIP ev cd st"
      and "st' = st\<lparr>gas := gas st - costs SKIP ev cd st\<rparr>"
  using assms by (auto split:if_split_asm)

lemma assign:
  assumes "stmt (ASSIGN lv ex) ev cd st  = Normal (xx, st')"
  obtains (1) v t g l t' g' v'
    where "expr ex ev cd (st\<lparr>gas := gas st - costs  (ASSIGN lv ex) ev cd st\<rparr>) (gas st - costs  (ASSIGN lv ex) ev cd st) = Normal ((KValue v, Value t), g)"
      and "lexp lv ev cd (st\<lparr>gas := g\<rparr>) g = Normal((LStackloc l, Value t'),g')"
      and "convert t t' v = Some v'"
      and "st' = st\<lparr>gas := g', stack := updateStore l (KValue v') (stack st)\<rparr>"
  | (2) v t g l t' g' v'
    where "expr ex ev cd (st\<lparr>gas := gas st - costs  (ASSIGN lv ex) ev cd st\<rparr>) (gas st - costs  (ASSIGN lv ex) ev cd st) = Normal ((KValue v, Value t), g)"
      and "lexp lv ev cd (st\<lparr>gas := g\<rparr>) g = Normal((LStoreloc l, Storage (STValue t')),g')"
      and "convert t t' v = Some v'"
      and "st' = st\<lparr>gas := g', storage := (storage st) (address ev := (fmupd l v' (storage st (address ev))))\<rparr>"
  | (3) v t g l t' g' v'
    where "expr ex ev cd (st\<lparr>gas := gas st - costs  (ASSIGN lv ex) ev cd st\<rparr>) (gas st - costs  (ASSIGN lv ex) ev cd st) = Normal ((KValue v, Value t), g)"
      and "lexp lv ev cd (st\<lparr>gas := g\<rparr>) g = Normal((LMemloc l, Memory (MTValue t')),g')"
      and "convert t t' v = Some v'"
      and "st' = st\<lparr>gas := g', memory := updateStore l (MValue v') (memory st)\<rparr>"
  | (4) p x t g l t' g' p' m
    where "expr ex ev cd (st\<lparr>gas := gas st - costs  (ASSIGN lv ex) ev cd st\<rparr>) (gas st - costs  (ASSIGN lv ex) ev cd st) = Normal ((KCDptr p, Calldata (MTArray x t)), g)"
      and "lexp lv ev cd (st\<lparr>gas := g\<rparr>) g = Normal((LStackloc l, Memory t'),g')"
      and "accessStore l (stack st) = Some (KMemptr p')"
      and "cpm2m p p' x t cd (memory st) = Some m"
      and "st' = st\<lparr>gas := g', memory := m\<rparr>"
  | (5) p x t g l t' g' p' s
    where "expr ex ev cd (st\<lparr>gas := gas st - costs  (ASSIGN lv ex) ev cd st\<rparr>) (gas st - costs  (ASSIGN lv ex) ev cd st) = Normal ((KCDptr p, Calldata (MTArray x t)), g)"
      and "lexp lv ev cd (st\<lparr>gas := g\<rparr>) g = Normal((LStackloc l, Storage t'),g')"
      and "accessStore l (stack st) = Some (KStoptr p')"
      and "cpm2s p p' x t cd (storage st (address ev)) = Some s"
      and "st' = st\<lparr>gas := g', storage := (storage st) (address ev := s)\<rparr>"
  | (6) p x t g l t' g' s
    where "expr ex ev cd (st\<lparr>gas := gas st - costs  (ASSIGN lv ex) ev cd st\<rparr>) (gas st - costs  (ASSIGN lv ex) ev cd st) = Normal ((KCDptr p, Calldata (MTArray x t)), g)"
      and "lexp lv ev cd (st\<lparr>gas := g\<rparr>) g = Normal((LStoreloc l, t'),g')"
      and "cpm2s p l x t cd (storage st (address ev)) = Some s"
      and "st' = st\<lparr>gas := g', storage := (storage st) (address ev := s)\<rparr>"
  | (7) p x t g l t' g' m
    where "expr ex ev cd (st\<lparr>gas := gas st - costs  (ASSIGN lv ex) ev cd st\<rparr>) (gas st - costs  (ASSIGN lv ex) ev cd st) = Normal ((KCDptr p, Calldata (MTArray x t)), g)"
      and "lexp lv ev cd (st\<lparr>gas := g\<rparr>) g = Normal((LMemloc l, t'),g')"
      and "cpm2m p l x t cd (memory st) = Some m"
      and "st' = st\<lparr>gas := g', memory := m\<rparr>"
  | (8) p x t g l t' g'
    where "expr ex ev cd (st\<lparr>gas := gas st - costs  (ASSIGN lv ex) ev cd st\<rparr>) (gas st - costs  (ASSIGN lv ex) ev cd st) = Normal ((KMemptr p, Memory (MTArray x t)), g)"
      and "lexp lv ev cd (st\<lparr>gas := g\<rparr>) g = Normal((LStackloc l, Memory t'),g')"
      and "st' = st\<lparr>gas := g', stack := updateStore l (KMemptr p) (stack st)\<rparr>"
  | (9) p x t g l t' g' p' s
    where "expr ex ev cd (st\<lparr>gas := gas st - costs  (ASSIGN lv ex) ev cd st\<rparr>) (gas st - costs  (ASSIGN lv ex) ev cd st) = Normal ((KMemptr p, Memory (MTArray x t)), g)"
      and "lexp lv ev cd (st\<lparr>gas := g\<rparr>) g = Normal((LStackloc l, Storage t'),g')"
      and "accessStore l (stack st) = Some (KStoptr p')"
      and "cpm2s p p' x t (memory st) (storage st (address ev)) = Some s"
      and "st' = st\<lparr>gas := g', storage := (storage st) (address ev := s)\<rparr>"
  | (10) p x t g l t' g' s
    where "expr ex ev cd (st\<lparr>gas := gas st - costs  (ASSIGN lv ex) ev cd st\<rparr>) (gas st - costs  (ASSIGN lv ex) ev cd st) = Normal ((KMemptr p, Memory (MTArray x t)), g)"
      and "lexp lv ev cd (st\<lparr>gas := g\<rparr>) g = Normal((LStoreloc l, t'),g')"
      and "cpm2s p l x t (memory st) (storage st (address ev)) = Some s"
      and "st' = st\<lparr>gas := g', storage := (storage st) (address ev := s)\<rparr>"
  | (11) p x t g l t' g'
    where "expr ex ev cd (st\<lparr>gas := gas st - costs  (ASSIGN lv ex) ev cd st\<rparr>) (gas st - costs  (ASSIGN lv ex) ev cd st) = Normal ((KMemptr p, Memory (MTArray x t)), g)"
      and "lexp lv ev cd (st\<lparr>gas := g\<rparr>) g = Normal((LMemloc l, t'),g')"
      and "st' = st\<lparr>gas := g', memory := updateStore l (MPointer p) (memory st)\<rparr>"
  | (12) p x t g l t' g' p' m
    where "expr ex ev cd (st\<lparr>gas := gas st - costs  (ASSIGN lv ex) ev cd st\<rparr>) (gas st - costs  (ASSIGN lv ex) ev cd st) = Normal ((KStoptr p, Storage (STArray x t)), g)"
      and "lexp lv ev cd (st\<lparr>gas := g\<rparr>) g = Normal((LStackloc l, Memory t'),g')"
      and "accessStore l (stack st) = Some (KMemptr p')"
      and "cps2m p p' x t (storage st (address ev)) (memory st) = Some m"
      and "st' = st\<lparr>gas := g', memory := m\<rparr>"
  | (13) p x t g l t' g'
    where "expr ex ev cd (st\<lparr>gas := gas st - costs  (ASSIGN lv ex) ev cd st\<rparr>) (gas st - costs  (ASSIGN lv ex) ev cd st) = Normal ((KStoptr p, Storage (STArray x t)), g)"
      and "lexp lv ev cd (st\<lparr>gas := g\<rparr>) g = Normal((LStackloc l, Storage t'),g')"
      and "st' = st\<lparr>gas := g', stack := updateStore l (KStoptr p) (stack st)\<rparr>"
  | (14) p x t g l t' g' s
    where "expr ex ev cd (st\<lparr>gas := gas st - costs  (ASSIGN lv ex) ev cd st\<rparr>) (gas st - costs  (ASSIGN lv ex) ev cd st) = Normal ((KStoptr p, Storage (STArray x t)), g)"
      and "lexp lv ev cd (st\<lparr>gas := g\<rparr>) g = Normal((LStoreloc l, t'),g')"
      and "copy p l x t (storage st (address ev)) = Some s"
      and "st' = st\<lparr>gas := g', storage := (storage st) (address ev := s)\<rparr>"
  | (15) p x t g l t' g' m
    where "expr ex ev cd (st\<lparr>gas := gas st - costs  (ASSIGN lv ex) ev cd st\<rparr>) (gas st - costs  (ASSIGN lv ex) ev cd st) = Normal ((KStoptr p, Storage (STArray x t)), g)"
      and "lexp lv ev cd (st\<lparr>gas := g\<rparr>) g = Normal((LMemloc l, t'),g')"
      and "cps2m p l x t (storage st (address ev)) (memory st) = Some m"
      and "st' = st\<lparr>gas := g', memory := m\<rparr>"
  | (16) p t t' g l t'' g'
    where "expr ex ev cd (st\<lparr>gas := gas st - costs  (ASSIGN lv ex) ev cd st\<rparr>) (gas st - costs  (ASSIGN lv ex) ev cd st) = Normal ((KStoptr p, Storage (STMap t t')), g)"
      and "lexp lv ev cd (st\<lparr>gas := g\<rparr>) g = Normal((LStackloc l, t''),g')"
      and "st' = st\<lparr>gas := g', stack := updateStore l (KStoptr p) (stack st)\<rparr>"
proof -
  from assms consider
    (1) v t g where "expr ex ev cd (st\<lparr>gas := gas st - costs  (ASSIGN lv ex) ev cd st\<rparr>) (gas st - costs  (ASSIGN lv ex) ev cd st) = Normal ((KValue v, Value t), g)"
  | (2) p x t g where "expr ex ev cd (st\<lparr>gas := gas st - costs  (ASSIGN lv ex) ev cd st\<rparr>) (gas st - costs  (ASSIGN lv ex) ev cd st) = Normal ((KCDptr p, Calldata (MTArray x t)), g)"
  | (3) p x t g where "expr ex ev cd (st\<lparr>gas := gas st - costs  (ASSIGN lv ex) ev cd st\<rparr>) (gas st - costs  (ASSIGN lv ex) ev cd st) = Normal ((KMemptr p, Memory (MTArray x t)), g)"
  | (4) p x t g where "expr ex ev cd (st\<lparr>gas := gas st - costs  (ASSIGN lv ex) ev cd st\<rparr>) (gas st - costs  (ASSIGN lv ex) ev cd st) = Normal ((KStoptr p, Storage (STArray x t)), g)"
  | (5) p t t' g where "expr ex ev cd (st\<lparr>gas := gas st - costs  (ASSIGN lv ex) ev cd st\<rparr>) (gas st - costs  (ASSIGN lv ex) ev cd st) = Normal ((KStoptr p, Storage (STMap t t')), g)"
    by (auto split:if_split_asm result.split_asm Stackvalue.split_asm Type.split_asm MTypes.split_asm STypes.split_asm)
  then show ?thesis
  proof cases
    case 1
    with assms consider
      (11) l t' g' where "lexp lv ev cd (st\<lparr>gas := g\<rparr>) g = Normal((LStackloc l, Value t'),g')"
    | (12) l t' g' where "lexp lv ev cd (st\<lparr>gas := g\<rparr>) g = Normal((LStoreloc l, Storage (STValue t')),g')"
    | (13) l t' g' where "lexp lv ev cd (st\<lparr>gas := g\<rparr>) g = Normal((LMemloc l, Memory (MTValue t')),g')"
      by (auto split:if_split_asm result.split_asm Type.split_asm LType.split_asm MTypes.split_asm STypes.split_asm)
    then show ?thesis
    proof cases
      case 11
      with 1 assms show ?thesis using that(1) by (auto split:if_split_asm result.split_asm Type.split_asm LType.split_asm MTypes.split_asm STypes.split_asm option.split_asm)
    next
      case 12
      with 1 assms show ?thesis using that(2) by (auto split:if_split_asm result.split_asm Type.split_asm LType.split_asm MTypes.split_asm STypes.split_asm option.split_asm)
    next
      case 13
      with 1 assms show ?thesis using that(3) by (auto split:if_split_asm result.split_asm Type.split_asm LType.split_asm MTypes.split_asm STypes.split_asm option.split_asm)
    qed
  next
    case 2
    with assms consider
      (21) l t' g' where "lexp lv ev cd (st\<lparr>gas := g\<rparr>) g = Normal((LStackloc l, Memory t'),g')"
    | (22) l t' g' where "lexp lv ev cd (st\<lparr>gas := g\<rparr>) g = Normal((LStackloc l, Storage t'),g')"
    | (23) l t' g' where "lexp lv ev cd (st\<lparr>gas := g\<rparr>) g = Normal((LStoreloc l, t'),g')"
    | (24) l t' g' where "lexp lv ev cd (st\<lparr>gas := g\<rparr>) g = Normal((LMemloc l, t'),g')"
      by (auto split:if_split_asm result.split_asm Type.split_asm LType.split_asm MTypes.split_asm STypes.split_asm)
    then show ?thesis
    proof cases
      case 21
      moreover from assms 2 21 obtain p' where 3: "accessStore l (stack st) = Some (KMemptr p')"
        by (auto split:if_split_asm result.split_asm Type.split_asm LType.split_asm MTypes.split_asm STypes.split_asm option.split_asm Stackvalue.split_asm)
      moreover from assms 2 21 3 obtain m where "cpm2m p p' x t cd (memory st) = Some m"
        by (auto split:if_split_asm result.split_asm Type.split_asm LType.split_asm MTypes.split_asm STypes.split_asm option.split_asm Stackvalue.split_asm)
      ultimately show ?thesis using that(4) assms 2 21
        by (auto split:if_split_asm result.split_asm Type.split_asm LType.split_asm MTypes.split_asm STypes.split_asm option.split_asm Stackvalue.split_asm)
    next
      case 22
      moreover from assms 2 22 obtain p' where 3: "accessStore l (stack st) = Some (KStoptr p')"
        by (auto split:if_split_asm result.split_asm Type.split_asm LType.split_asm MTypes.split_asm STypes.split_asm option.split_asm Stackvalue.split_asm)
      moreover from assms 2 22 3 4 obtain s where "cpm2s p p' x t cd (storage st (address ev)) = Some s"
        by (auto split:if_split_asm result.split_asm Type.split_asm LType.split_asm MTypes.split_asm STypes.split_asm option.split_asm Stackvalue.split_asm)
      ultimately show ?thesis using that(5) assms 2 22
        by (auto split:if_split_asm result.split_asm Type.split_asm LType.split_asm MTypes.split_asm STypes.split_asm option.split_asm Stackvalue.split_asm)
    next
      case 23
      moreover from assms 2 23 3 4 obtain s where "cpm2s p l x t cd (storage st (address ev)) = Some s"
        by (auto split:if_split_asm result.split_asm Type.split_asm LType.split_asm MTypes.split_asm STypes.split_asm option.split_asm Stackvalue.split_asm)
      ultimately show ?thesis using that(6) assms 2
        by (auto split:if_split_asm result.split_asm Type.split_asm LType.split_asm MTypes.split_asm STypes.split_asm option.split_asm Stackvalue.split_asm)
    next
      case 24
      moreover from assms 2 24 obtain m where "cpm2m p l x t cd (memory st) = Some m"
        by (auto split:if_split_asm result.split_asm Type.split_asm LType.split_asm MTypes.split_asm STypes.split_asm option.split_asm Stackvalue.split_asm)
      ultimately show ?thesis using that(7) assms 2
        by (auto split:if_split_asm result.split_asm Type.split_asm LType.split_asm MTypes.split_asm STypes.split_asm option.split_asm Stackvalue.split_asm)
    qed
  next
    case 3
    with assms consider
      (31) l t' g' where "lexp lv ev cd (st\<lparr>gas := g\<rparr>) g = Normal((LStackloc l, Memory t'),g')"
    | (32) l t' g' where "lexp lv ev cd (st\<lparr>gas := g\<rparr>) g = Normal((LStackloc l, Storage t'),g')"
    | (33) l t' g' where "lexp lv ev cd (st\<lparr>gas := g\<rparr>) g = Normal((LStoreloc l, t'),g')"
    | (34) l t' g' where "lexp lv ev cd (st\<lparr>gas := g\<rparr>) g = Normal((LMemloc l, t'),g')"
      by (auto split:if_split_asm result.split_asm Type.split_asm LType.split_asm MTypes.split_asm STypes.split_asm)
    then show ?thesis
    proof cases
      case 31
      then show ?thesis using that(8) assms 3 by (auto split:if_split_asm)
    next
      case 32
      moreover from assms 3 32 obtain p' where 4: "accessStore l (stack st) = Some (KStoptr p')"
        by (auto split:if_split_asm result.split_asm Type.split_asm LType.split_asm MTypes.split_asm STypes.split_asm option.split_asm Stackvalue.split_asm)
      moreover from assms 3 32 4 5 obtain s where "cpm2s p p' x t (memory st) (storage st (address ev)) = Some s"
        by (auto split:if_split_asm result.split_asm Type.split_asm LType.split_asm MTypes.split_asm STypes.split_asm option.split_asm Stackvalue.split_asm)
      ultimately show ?thesis using that(9) assms 3
        by (auto split:if_split_asm result.split_asm Type.split_asm LType.split_asm MTypes.split_asm STypes.split_asm option.split_asm Stackvalue.split_asm)
    next
      case 33
      moreover from assms 3 33 3 4 obtain s where "cpm2s p l x t (memory st) (storage st (address ev)) = Some s"
        by (auto split:if_split_asm result.split_asm Type.split_asm LType.split_asm MTypes.split_asm STypes.split_asm option.split_asm Stackvalue.split_asm)
      ultimately show ?thesis using that(10) assms 3
        by (auto split:if_split_asm result.split_asm Type.split_asm LType.split_asm MTypes.split_asm STypes.split_asm option.split_asm Stackvalue.split_asm)
    next
      case 34
      then show ?thesis using that(11) assms 3
        by (auto split:if_split_asm result.split_asm Type.split_asm LType.split_asm MTypes.split_asm STypes.split_asm option.split_asm Stackvalue.split_asm)
    qed
  next
    case 4
    with assms consider
      (41) l t' g' where "lexp lv ev cd (st\<lparr>gas := g\<rparr>) g = Normal((LStackloc l, Memory t'),g')"
    | (42) l t' g' where "lexp lv ev cd (st\<lparr>gas := g\<rparr>) g = Normal((LStackloc l, Storage t'),g')"
    | (43) l t' g' where "lexp lv ev cd (st\<lparr>gas := g\<rparr>) g = Normal((LStoreloc l, t'),g')"
    | (44) l t' g' where "lexp lv ev cd (st\<lparr>gas := g\<rparr>) g = Normal((LMemloc l, t'),g')"
      by (auto split:if_split_asm result.split_asm Type.split_asm LType.split_asm MTypes.split_asm STypes.split_asm)
    then show ?thesis
    proof cases
      case 41
      moreover from assms 4 41 obtain p' where 5: "accessStore l (stack st) = Some (KMemptr p')"
        by (auto split:if_split_asm result.split_asm Type.split_asm LType.split_asm MTypes.split_asm STypes.split_asm option.split_asm Stackvalue.split_asm)
      moreover from assms 4 41 5 6 obtain m where "cps2m p p' x t (storage st (address ev)) (memory st) = Some m"
        by (auto split:if_split_asm result.split_asm Type.split_asm LType.split_asm MTypes.split_asm STypes.split_asm option.split_asm Stackvalue.split_asm)
      ultimately show ?thesis using that(12) assms 4
        by (auto split:if_split_asm result.split_asm Type.split_asm LType.split_asm MTypes.split_asm STypes.split_asm option.split_asm Stackvalue.split_asm)
    next
      case 42
      then show ?thesis using that(13) assms 4
        by (auto split:if_split_asm result.split_asm Type.split_asm LType.split_asm MTypes.split_asm STypes.split_asm option.split_asm Stackvalue.split_asm)
    next
      case 43
      moreover from assms 4 43 5 obtain s where "copy p l x t (storage st (address ev)) = Some s"
        by (auto split:if_split_asm result.split_asm Type.split_asm LType.split_asm MTypes.split_asm STypes.split_asm option.split_asm Stackvalue.split_asm)
      ultimately show ?thesis using that(14) assms 4
        by (auto split:if_split_asm result.split_asm Type.split_asm LType.split_asm MTypes.split_asm STypes.split_asm option.split_asm Stackvalue.split_asm)
    next
      case 44
      moreover from assms 4 44 5 obtain m where "cps2m p l x t (storage st (address ev)) (memory st) = Some m"
        by (auto split:if_split_asm result.split_asm Type.split_asm LType.split_asm MTypes.split_asm STypes.split_asm option.split_asm Stackvalue.split_asm)
      ultimately show ?thesis using that(15) assms 4
        by (auto split:if_split_asm result.split_asm Type.split_asm LType.split_asm MTypes.split_asm STypes.split_asm option.split_asm Stackvalue.split_asm)
    qed
  next
    case 5
    then show ?thesis using that(16) assms
      by (auto split:if_split_asm result.split_asm Type.split_asm LType.split_asm MTypes.split_asm STypes.split_asm option.split_asm Stackvalue.split_asm)
  qed
qed

lemma comp:
  assumes "stmt (COMP s1 s2) ev cd st = Normal (x, st')"
  obtains (1) st''
  where "gas st > costs (COMP s1 s2) ev cd st"
    and "stmt s1 ev cd (st\<lparr>gas := gas st - costs (COMP s1 s2) ev cd st\<rparr>) = Normal((), st'')"
    and "stmt s2 ev cd st'' = Normal((), st')"
  using assms by (simp split:if_split_asm result.split_asm prod.split_asm)

lemma ite:
  assumes "stmt (ITE ex s1 s2) ev cd st = Normal (x, st')"
  obtains (True) g
  where "gas st > costs (ITE ex s1 s2) ev cd st"
    and "expr ex ev cd (st\<lparr>gas := gas st - costs (ITE ex s1 s2) ev cd st\<rparr>) (gas st - costs (ITE ex s1 s2) ev cd st) = Normal((KValue (ShowL\<^sub>b\<^sub>o\<^sub>o\<^sub>l True), Value TBool), g)"
    and "stmt s1 ev cd (st\<lparr>gas := g\<rparr>) = Normal((), st')"
| (False) g
  where "gas st > costs (ITE ex s1 s2) ev cd st"
    and "expr ex ev cd (st\<lparr>gas := gas st - costs (ITE ex s1 s2) ev cd st\<rparr>) (gas st - costs (ITE ex s1 s2) ev cd st) = Normal((KValue (ShowL\<^sub>b\<^sub>o\<^sub>o\<^sub>l False), Value TBool), g)"
    and "stmt s2 ev cd (st\<lparr>gas := g\<rparr>) = Normal((), st')"
  using assms by (simp split:if_split_asm result.split_asm prod.split_asm Stackvalue.split_asm Type.split_asm Types.split_asm)

lemma while:           
  assumes "stmt (WHILE ex s0) ev cd st = Normal (x, st')"
  obtains (True) g st''
    where "gas st > costs (WHILE ex s0) ev cd st"
      and "expr ex ev cd (st\<lparr>gas := gas st - costs (WHILE ex s0) ev cd st\<rparr>) (gas st - costs (WHILE ex s0) ev cd st) = Normal((KValue (ShowL\<^sub>b\<^sub>o\<^sub>o\<^sub>l True), Value TBool), g)"
      and "stmt s0 ev cd (st\<lparr>gas := g\<rparr>) = Normal((), st'')"
      and "stmt (WHILE ex s0) ev cd st'' = Normal ((), st')"
    | (False) g
  where "gas st > costs (WHILE ex s0) ev cd st"
    and "expr ex ev cd (st\<lparr>gas := gas st - costs (WHILE ex s0) ev cd st\<rparr>) (gas st - costs (WHILE ex s0) ev cd st) = Normal((KValue (ShowL\<^sub>b\<^sub>o\<^sub>o\<^sub>l False), Value TBool), g)"
    and "st' = st\<lparr>gas := g\<rparr>"
  using assms
proof -
  from assms have 1: "gas st > costs (WHILE ex s0) ev cd st" by (simp split:if_split_asm)
  moreover from assms 1 have 2: "modify (\<lambda>st. st\<lparr>gas := gas st - costs (WHILE ex s0) ev cd st\<rparr>) st = Normal ((), st\<lparr>gas := gas st - costs (WHILE ex s0) ev cd st\<rparr>)" by simp
  moreover from assms 1 2 obtain b g where 3: "expr ex ev cd (st\<lparr>gas := gas st - costs (WHILE ex s0) ev cd st\<rparr>) (gas st - costs (WHILE ex s0) ev cd st) = Normal ((KValue b, Value TBool), g)" by (simp split:result.split_asm prod.split_asm Stackvalue.split_asm Type.split_asm Types.split_asm)
  ultimately consider (True) "b = ShowL\<^sub>b\<^sub>o\<^sub>o\<^sub>l True" | (False) "b = ShowL\<^sub>b\<^sub>o\<^sub>o\<^sub>l False" | (None) "b \<noteq> ShowL\<^sub>b\<^sub>o\<^sub>o\<^sub>l True \<and> b \<noteq> ShowL\<^sub>b\<^sub>o\<^sub>o\<^sub>l False" by auto
  then show ?thesis
  proof cases
    case True
    moreover from assms 1 2 3 True obtain st' where 4: "stmt s0 ev cd (st\<lparr>gas := g\<rparr>) = Normal ((), st')" by (simp split:result.split_asm prod.split_asm)
    moreover from assms 1 2 3 4 True obtain st'' where 5: "stmt (WHILE ex s0) ev cd st' = Normal ((), st'')" by (simp split:result.split_asm prod.split_asm)
    ultimately show ?thesis using 1 2 3 that(1) assms by simp
  next
    case False
    then show ?thesis using 1 2 3 that(2) assms true_neq_false by simp
  next
    case None
    then show ?thesis using 1 2 3 assms by simp
  qed
qed  

lemma invoke:
  fixes ev
  defines "e' members \<equiv> ffold (init members) (emptyEnv (address ev) (contract ev) (sender ev) (svalue ev)) (fmdom members)"
  assumes "stmt (INVOKE i xe) ev cd st = Normal (x, st')"
  obtains ct fb fp f e\<^sub>l cd\<^sub>l k\<^sub>l m\<^sub>l g st''
    where "gas st > costs (INVOKE i xe) ev cd st"
      and "ep $$ contract ev = Some (ct, fb)"
      and "ct $$ i = Some (Method (fp, False, f))"
      and "load False fp xe (e' ct) emptyStore emptyStore (memory (st\<lparr>gas := gas st - costs (INVOKE i xe) ev cd st\<rparr>)) ev cd (st\<lparr>gas := gas st - costs (INVOKE i xe) ev cd st\<rparr>) (gas st - costs (INVOKE i xe) ev cd st) = Normal ((e\<^sub>l, cd\<^sub>l, k\<^sub>l, m\<^sub>l), g)"
      and "stmt f e\<^sub>l cd\<^sub>l (st\<lparr>gas:= g, stack:=k\<^sub>l, memory:=m\<^sub>l\<rparr>) = Normal ((), st'')"
      and "st' = st''\<lparr>stack:=stack st\<rparr>"
proof -
  from assms have 1: "gas st > costs (INVOKE i xe) ev cd st" by (simp split:if_split_asm)
  moreover from assms 1 obtain ct fb where 2: "ep $$ (contract ev) = Some (ct, fb)" by (simp split: prod.split_asm result.split_asm option.split_asm)
  moreover from assms 1 2 obtain fp f where 3: "ct $$ i = Some (Method (fp, False, f))" by (simp split: prod.split_asm result.split_asm option.split_asm Member.split_asm bool.split_asm)
  moreover from assms 1 2 3 obtain e\<^sub>l cd\<^sub>l k\<^sub>l m\<^sub>l g where 4: "load False fp xe (e' ct) emptyStore emptyStore (memory (st\<lparr>gas := gas st - costs (INVOKE i xe) ev cd st\<rparr>)) ev cd (st\<lparr>gas := gas st - costs (INVOKE i xe) ev cd st\<rparr>) (gas st - costs (INVOKE i xe) ev cd st) = Normal ((e\<^sub>l, cd\<^sub>l, k\<^sub>l, m\<^sub>l), g)" by (simp split: prod.split_asm result.split_asm)
  moreover from assms 1 2 3 4 obtain st'' where 5: "stmt f e\<^sub>l cd\<^sub>l (st\<lparr>gas:= g, stack:=k\<^sub>l, memory:=m\<^sub>l\<rparr>) = Normal ((), st'')" by (simp split: prod.split_asm result.split_asm)
  moreover from assms 1 2 3 4 5 have "st' = st''\<lparr>stack:=stack st\<rparr>" by (simp split: prod.split_asm result.split_asm)
  ultimately show ?thesis using that by simp
qed

lemma external:
  fixes ev
  defines "e' members adv c v \<equiv> ffold (init members) (emptyEnv adv c (address ev) v) (fmdom members)"
  assumes "stmt (EXTERNAL ad' i xe val) ev cd st = Normal (x, st')"
  obtains (Some) adv c g ct cn fb' v t g' v' fp f e\<^sub>l cd\<^sub>l k\<^sub>l m\<^sub>l g'' acc st''
    where "gas st > costs (EXTERNAL ad' i xe val) ev cd st"
      and "expr ad' ev cd (st\<lparr>gas := gas st - costs (EXTERNAL ad' i xe val) ev cd st\<rparr>) (gas st - costs  (EXTERNAL ad' i xe val) ev cd st) = Normal ((KValue adv, Value TAddr), g)"
      and "adv \<noteq> address ev"
      and "type (accounts (st\<lparr>gas := g\<rparr>) adv) = Some (Contract c)"
      and "ep $$ c = Some (ct, cn, fb')"
      and "expr val ev cd (st\<lparr>gas := g\<rparr>) g = Normal ((KValue v, Value t), g')"
      and "convert t (TUInt 256) v = Some v'"
      and "fmlookup ct i = Some (Method (fp, True, f))"
      and "load True fp xe (e' ct adv c v') emptyStore emptyStore emptyStore ev cd (st\<lparr>gas := g'\<rparr>) g' = Normal ((e\<^sub>l, cd\<^sub>l, k\<^sub>l, m\<^sub>l), g'')"
      and "transfer (address ev) adv v' (accounts (st\<lparr>gas := g''\<rparr>)) = Some acc"
      and "stmt f e\<^sub>l cd\<^sub>l (st\<lparr>gas := g'', accounts := acc, stack:=k\<^sub>l, memory:=m\<^sub>l\<rparr>) = Normal ((), st'')"
      and "st' = st''\<lparr>stack:=stack st, memory := memory st\<rparr>"
    | (None) adv c g ct cn fb' v t g' v' acc st''
    where "gas st > costs (EXTERNAL ad' i xe val) ev cd st"
      and "expr ad' ev cd (st\<lparr>gas := gas st - costs  (EXTERNAL ad' i xe val) ev cd st\<rparr>) (gas st - costs  (EXTERNAL ad' i xe val) ev cd st) = Normal ((KValue adv, Value TAddr), g)"
      and "adv \<noteq> address ev"
      and "type (accounts (st\<lparr>gas := g\<rparr>) adv) = Some (Contract c)"
      and "ep $$ c = Some (ct, cn, fb')"
      and "expr val ev cd (st\<lparr>gas := g\<rparr>) g = Normal ((KValue v, Value t), g')"
      and "convert t (TUInt 256) v = Some v'"
      and "ct $$ i = None"
      and "transfer (address ev) adv v' (accounts st) = Some acc"
      and "stmt fb' (e' ct adv c v') emptyStore (st\<lparr>gas := g', accounts := acc, stack:=emptyStore, memory:=emptyStore\<rparr>) = Normal ((), st'')"
      and "st' = st''\<lparr>stack:=stack st, memory := memory st\<rparr>"
proof -
  from assms have 1: "gas st > costs (EXTERNAL ad' i xe val) ev cd st" by (simp split:if_split_asm)
  moreover from assms 1 obtain adv g where 2: "expr ad' ev cd (st\<lparr>gas := gas st - costs  (EXTERNAL ad' i xe val) ev cd st\<rparr>) (gas st - costs  (EXTERNAL ad' i xe val) ev cd st) = Normal ((KValue adv, Value TAddr), g)" by (simp split: prod.split_asm result.split_asm Stackvalue.split_asm Type.split_asm Types.split_asm)
  moreover from assms 1 2 obtain c where 3: "type (accounts (st\<lparr>gas := g\<rparr>) adv) = Some (Contract c)" by (simp split: if_split_asm prod.split_asm result.split_asm Stackvalue.split_asm Type.split_asm Types.split_asm option.split_asm atype.split_asm)
  moreover from assms 1 2 3 obtain ct cn fb' where 4: "ep $$ c = Some (ct, cn, fb')" by (simp add: Let_def split: if_split_asm prod.split_asm result.split_asm Stackvalue.split_asm Type.split_asm Types.split_asm option.split_asm)
  moreover from assms 1 2 3 4 obtain v t g' where 5: "expr val ev cd (st\<lparr>gas := g\<rparr>) g = Normal ((KValue v, Value t), g')" using 1 2 by (simp split: if_split_asm prod.split_asm result.split_asm Stackvalue.split_asm Type.split_asm Types.split_asm option.split_asm)
  moreover from assms 1 2 3 4 5 have 6: "adv \<noteq> address ev" by (simp add: Let_def split: if_split_asm prod.split_asm result.split_asm Stackvalue.split_asm Type.split_asm Types.split_asm option.split_asm)
  moreover from assms 1 2 3 4 5 6 obtain v' where 7: "convert t (TUInt 256) v = Some v'" by (simp add: Let_def split: if_split_asm prod.split_asm result.split_asm Stackvalue.split_asm Type.split_asm Types.split_asm option.split_asm)
  ultimately consider (Some) fp f where "ct $$ i = Some (Method (fp, True, f))" | (None) "fmlookup ct i = None" using assms by (simp add: Let_def split: if_split_asm prod.split_asm result.split_asm Stackvalue.split_asm Type.split_asm Types.split_asm option.split_asm Member.split_asm bool.split_asm)
  then show ?thesis
  proof cases
    case (Some fp f)
    moreover from assms 1 2 3 4 5 6 7 Some obtain e\<^sub>l cd\<^sub>l k\<^sub>l m\<^sub>l g'' where 8: "load True fp xe (e' ct adv c v') emptyStore emptyStore emptyStore ev cd (st\<lparr>gas := g'\<rparr>) g' = Normal ((e\<^sub>l, cd\<^sub>l, k\<^sub>l, m\<^sub>l), g'')" by (simp add: Let_def split: if_split_asm prod.split_asm result.split_asm Stackvalue.split_asm Type.split_asm Types.split_asm option.split_asm Member.split_asm)
    moreover from assms 1 2 3 4 5 6 7 Some 8 obtain acc where 9: "transfer (address ev) adv v' (accounts st) = Some acc" by (simp add: Let_def split: if_split_asm prod.split_asm result.split_asm Stackvalue.split_asm Type.split_asm Types.split_asm option.split_asm Member.split_asm)
    moreover from assms 1 2 3 4 5 6 7 Some 8 9 obtain st'' where 10: "stmt f e\<^sub>l cd\<^sub>l (st\<lparr>gas := g'', accounts := acc, stack:=k\<^sub>l, memory:=m\<^sub>l\<rparr>) = Normal ((), st'')" by (simp add: Let_def transfer_def split: if_split_asm prod.split_asm result.split_asm Stackvalue.split_asm Type.split_asm Types.split_asm option.split_asm Member.split_asm)
    moreover from assms 1 2 3 4 5 6 7 Some 8 9 10 have "st' = st''\<lparr>stack:=stack st, memory := memory st\<rparr>" by (simp add: Let_def transfer_def split: if_split_asm prod.split_asm result.split_asm Stackvalue.split_asm Type.split_asm Types.split_asm option.split_asm Member.split_asm)
    ultimately show ?thesis using 1 2 3 4 5 6 7 that(1) by simp
  next
    case None
    moreover from assms 1 2 3 4 5 6 7 None obtain acc where 8: "transfer (address ev) adv v' (accounts st) = Some acc" by (simp add: Let_def split: if_split_asm prod.split_asm result.split_asm Stackvalue.split_asm Type.split_asm Types.split_asm option.split_asm Member.split_asm)
    moreover from assms 1 2 3 4 5 6 7 None 8 obtain st'' where 9: "stmt fb' (e' ct adv c v') emptyStore (st\<lparr>gas := g', accounts := acc, stack:=emptyStore, memory:=emptyStore\<rparr>) = Normal ((), st'')" by (simp add: Let_def transfer_def split: if_split_asm prod.split_asm result.split_asm Stackvalue.split_asm Type.split_asm Types.split_asm option.split_asm Member.split_asm)
    moreover from assms 1 2 3 4 5 6 7 None 8 9 have "st' = st''\<lparr>stack:=stack st, memory := memory st\<rparr>" by (simp add: Let_def transfer_def split: if_split_asm prod.split_asm result.split_asm Stackvalue.split_asm Type.split_asm Types.split_asm option.split_asm Member.split_asm)
    ultimately show ?thesis using 1 2 3 4 5 6 7 that(2) by simp
  qed
qed

lemma transfer:
  fixes ev
  defines "e' members adv c st v \<equiv> ffold (init members) (emptyEnv adv c (address ev) v) (fmdom members)"
  assumes "stmt (TRANSFER ad ex) ev cd st = Normal (x, st')"
  obtains (Contract) v t g adv c g' v' acc ct cn f st''
    where "gas st > costs (TRANSFER ad ex) ev cd st"
      and "expr ad ev cd (st\<lparr>gas := gas st - costs (TRANSFER ad ex) ev cd st\<rparr>) (gas st - costs (TRANSFER ad ex) ev cd st) = Normal ((KValue adv, Value TAddr), g)"
      and "expr ex ev cd (st\<lparr>gas := g\<rparr>) g = Normal ((KValue v, Value t), g')"
      and "convert t (TUInt 256) v = Some v'"
      and "type (accounts (st\<lparr>gas := g\<rparr>) adv) = Some (Contract c)"
      and "ep $$ c = Some (ct, cn, f)"
      and "transfer (address ev) adv v' (accounts st) = Some acc"
      and "stmt f (e' ct adv c (st\<lparr>gas := g'\<rparr>) v') emptyStore (st\<lparr>gas := g', accounts := acc, stack:=emptyStore, memory:=emptyStore\<rparr>) = Normal ((), st'')"
      and "st' = st''\<lparr>stack:=stack st, memory := memory st\<rparr>"
    | (EOA) v t g adv g' v' acc
    where "gas st > costs (TRANSFER ad ex) ev cd st"
      and "expr ad ev cd (st\<lparr>gas := gas st - costs  (TRANSFER ad ex) ev cd st\<rparr>) (gas st - costs (TRANSFER ad ex) ev cd st) = Normal ((KValue adv, Value TAddr), g)"
      and "expr ex ev cd (st\<lparr>gas := g\<rparr>) g = Normal ((KValue v, Value t), g')"
      and "convert t (TUInt 256) v = Some v'"
      and "type (accounts (st\<lparr>gas := g\<rparr>) adv) = Some EOA"
      and "transfer (address ev) adv v' (accounts st) = Some acc"
      and "st' = st\<lparr>gas:=g', accounts:=acc\<rparr>"
proof -
  from assms have 1: "gas st > costs (TRANSFER ad ex) ev cd st" by (simp split:if_split_asm)
  moreover from assms 1 obtain adv g where 2: "expr ad ev cd (st\<lparr>gas := gas st - costs  (TRANSFER ad ex) ev cd st\<rparr>) (gas st - costs (TRANSFER ad ex) ev cd st) = Normal ((KValue adv, Value TAddr), g)" by (simp add: Let_def split: if_split_asm prod.split_asm result.split_asm Stackvalue.split_asm Type.split_asm Types.split_asm)
  moreover from assms 1 2 obtain v t g' where 3: "expr ex ev cd (st\<lparr>gas := g\<rparr>) g = Normal ((KValue v, Value t), g')" by (simp add: Let_def split: if_split_asm prod.split_asm result.split_asm Stackvalue.split_asm Type.split_asm Types.split_asm)
  moreover from assms 1 2 3 obtain v' where 4: "convert t (TUInt 256) v = Some v'" by (simp add: Let_def split: if_split_asm prod.split_asm result.split_asm Stackvalue.split_asm Type.split_asm Types.split_asm option.split_asm)
  ultimately consider (Contract) c where "type (accounts (st\<lparr>gas := g'\<rparr>) adv) = Some (Contract c)" | (EOA) "type (accounts (st\<lparr>gas := g'\<rparr>) adv) = Some EOA" using assms by (simp add: Let_def split: if_split_asm prod.split_asm result.split_asm Stackvalue.split_asm Type.split_asm Types.split_asm option.split_asm Member.split_asm atype.split_asm)
  then show ?thesis
  proof cases
    case (Contract c)
    moreover from assms 1 2 3 4 Contract obtain ct cn f where 5: "ep $$ c = Some (ct, cn, f)" by (simp add: Let_def split: if_split_asm prod.split_asm result.split_asm Stackvalue.split_asm Type.split_asm Types.split_asm option.split_asm atype.split_asm atype.split_asm)
    moreover from assms 1 2 3 4 Contract 5 obtain acc where 6: "transfer (address ev) adv v' (accounts st) = Some acc" by (simp add: Let_def split: if_split_asm prod.split_asm result.split_asm Stackvalue.split_asm Type.split_asm Types.split_asm option.split_asm Member.split_asm)
    moreover from assms 1 2 3 4 Contract 5 6 obtain st'' where 7: "stmt f (e' ct adv c (st\<lparr>gas := g'\<rparr>) v') emptyStore (st\<lparr>gas := g', accounts := acc, stack:=emptyStore, memory:=emptyStore\<rparr>) = Normal ((), st'')" by (simp add: Let_def split: if_split_asm prod.split_asm result.split_asm Stackvalue.split_asm Type.split_asm Types.split_asm option.split_asm Member.split_asm)
    moreover from assms 1 2 3 4 Contract 5 6 7 have "st' = st''\<lparr>stack:=stack st, memory := memory st\<rparr>" by (simp add: Let_def split: if_split_asm prod.split_asm result.split_asm Stackvalue.split_asm Type.split_asm Types.split_asm option.split_asm Member.split_asm)
    ultimately show ?thesis using 1 2 3 4 that(1) by simp
  next
    case EOA
    moreover from assms 1 2 3 4 EOA obtain acc where 5: "transfer (address ev) adv v' (accounts st) = Some acc" by (simp add: Let_def split: if_split_asm prod.split_asm result.split_asm Stackvalue.split_asm Type.split_asm Types.split_asm option.split_asm Member.split_asm)
    moreover from assms 1 2 3 4 EOA 5 have "st' = st\<lparr>gas:=g', accounts:=acc\<rparr>" by (simp add: Let_def split: if_split_asm prod.split_asm result.split_asm Stackvalue.split_asm Type.split_asm Types.split_asm option.split_asm Member.split_asm)
    ultimately show ?thesis using 1 2 3 4 that(2) by simp
  qed
qed

lemma blockNone:
  fixes ev
  assumes "stmt (BLOCK ((id0, tp), None) s) ev cd st = Normal (x, st')"
  obtains cd' mem' sck' e'
    where "gas st > costs (BLOCK ((id0, tp), None) s) ev cd st"
      and "decl id0 tp None False cd (memory (st\<lparr>gas := gas st - costs (BLOCK ((id0, tp), None) s) ev cd st\<rparr>)) (storage (st\<lparr>gas := gas st - costs (BLOCK ((id0, tp), None) s) ev cd st\<rparr>)) (cd, memory (st\<lparr>gas := gas st - costs (BLOCK ((id0, tp), None) s) ev cd st\<rparr>), stack (st\<lparr>gas := gas st - costs (BLOCK ((id0, tp), None) s) ev cd st\<rparr>), ev) = Some (cd', mem', sck', e')"
      and "stmt s e' cd' (st\<lparr>gas := gas st - costs (BLOCK ((id0, tp), None) s) ev cd st, stack := sck', memory := mem'\<rparr>) = Normal ((), st')"
  using assms by (simp split:if_split_asm prod.split_asm option.split_asm)

lemma blockSome:
  fixes ev
  assumes "stmt (BLOCK ((id0, tp), Some ex') s) ev cd st = Normal (x, st')"
  obtains v t g cd' mem' sck' e'
    where "gas st > costs (BLOCK ((id0, tp), Some ex') s) ev cd st"
      and "expr ex' ev cd (st\<lparr>gas := gas st - costs (BLOCK ((id0, tp), Some ex') s) ev cd st\<rparr>) (gas st - costs (BLOCK ((id0, tp), Some ex') s) ev cd st) = Normal((v,t),g)"
      and "decl id0 tp (Some (v, t)) False cd (memory (st\<lparr>gas := g\<rparr>)) (storage (st\<lparr>gas := g\<rparr>)) (cd, memory (st\<lparr>gas := g\<rparr>), stack (st\<lparr>gas := g\<rparr>), ev) = Some (cd', mem', sck', e')"
      and "stmt s e' cd' (st\<lparr>gas := g, stack := sck', memory := mem'\<rparr>) = Normal ((), st')"
  using assms by (auto split:if_split_asm result.split_asm prod.split_asm option.split_asm)

lemma new:
  fixes i xe val ev cd st
  defines "st0 \<equiv> st\<lparr>gas := gas st - costs (NEW i xe val) ev cd st\<rparr>"
  defines "adv0 \<equiv> hash (address ev) (ShowL\<^sub>n\<^sub>a\<^sub>t (contracts (accounts st0 (address ev))))"
  defines "st1 g \<equiv> st\<lparr>gas := g, accounts := (accounts st)(adv0 := \<lparr>bal = ShowL\<^sub>i\<^sub>n\<^sub>t 0, type = Some (Contract i), contracts = 0\<rparr>), storage:=(storage st)(adv0 := {$$})\<rparr>"
  defines "e' members c v \<equiv> ffold (init members) (emptyEnv adv0 c (address ev) v) (fmdom members)"
  assumes "stmt (NEW i xe val) ev cd st = Normal (x, st')"
  obtains v t g ct cn fb e\<^sub>l cd\<^sub>l k\<^sub>l m\<^sub>l g' acc st''
    where "gas st > costs (NEW i xe val) ev cd st"
      and "type (accounts st adv0) = None"
      and "expr val ev cd st0 (gas st0) = Normal((KValue v, Value t),g)"
      and "ep $$ i = Some (ct, cn, fb)"
      and "load True (fst cn) xe (e' ct i v) emptyStore emptyStore emptyStore ev cd (st0\<lparr>gas := g\<rparr>) g = Normal ((e\<^sub>l, cd\<^sub>l, k\<^sub>l, m\<^sub>l), g')"
      and "transfer (address ev) adv0 v (accounts (st1 g')) = Some acc"
      and "stmt (snd cn) e\<^sub>l cd\<^sub>l (st1 g'\<lparr>accounts := acc, stack:=k\<^sub>l, memory:=m\<^sub>l\<rparr>) = Normal ((), st'')"
      and "st' = incrementAccountContracts (address ev) (st''\<lparr>stack:=stack st, memory := memory st\<rparr>)"
proof -
  from assms have 1: "gas st > costs (NEW i xe val) ev cd st" by (simp split:if_split_asm)
  moreover from st0_def assms 1 have 2: "type (accounts st adv0) = None" by (simp split: if_split_asm)
  moreover from st0_def assms 1 2 obtain v t g where 3: "expr val ev cd st0 (gas st0) = Normal((KValue v, Value t),g)" by (simp split: prod.split_asm result.split_asm Stackvalue.split_asm Type.split_asm)
  moreover from assms 1 st0_def 2 3 obtain ct cn fb where 4: "ep $$ i = Some(ct, cn, fb)" by (simp split: prod.split_asm result.split_asm option.split_asm)
  moreover from st0_def adv0_def e'_def assms 1 2 3 4 obtain e\<^sub>l cd\<^sub>l k\<^sub>l m\<^sub>l g' where 5: "load True (fst cn) xe (e' ct i v) emptyStore emptyStore emptyStore ev cd (st0\<lparr>gas := g\<rparr>) g = Normal ((e\<^sub>l, cd\<^sub>l, k\<^sub>l, m\<^sub>l), g')" by (simp add:Let_def split: prod.split_asm result.split_asm option.split_asm)
  moreover from st0_def adv0_def e'_def assms 1 2 3 4 5 obtain acc where 6: "transfer (address ev) adv0 v (accounts (st1 g')) = Some acc" by (simp add:Let_def split: prod.split_asm result.split_asm option.split_asm)
  moreover from st0_def st1_def adv0_def e'_def assms 1 2 3 4 5 6 obtain st'' where "stmt (snd cn) e\<^sub>l cd\<^sub>l (st1 g'\<lparr>accounts := acc, stack:=k\<^sub>l, memory:=m\<^sub>l\<rparr>) = Normal ((), st'')" by (simp add:Let_def split: prod.split_asm result.split_asm option.split_asm)
  ultimately show ?thesis using that assms by simp
qed

lemma atype_same:
  assumes "stmt stm ev cd st = Normal (x, st')"
      and "type (accounts st ad) = Some ctype"
    shows "type (accounts st' ad) = Some ctype"
using assms
proof (induction arbitrary: st' rule: stmt.induct)
  case (1 e cd st)
  then show ?case using skip[OF 1(1)] by auto    
next
  case (2 lv ex env cd st)
  show ?case by (cases rule: assign[OF 2(1)]; simp add: 2(2))
next
  case (3 s1 s2 e cd st)
  show ?case
  proof (cases rule: comp[OF 3(3)])
    case (1 st'')
    then show ?thesis using 3 by simp
  qed
next
  case (4 ex s1 s2 e cd st)
  show ?case
  proof (cases rule: ite[OF 4(3)])
    case (1 g)
    then show ?thesis using 4 by simp
  next
    case (2 g)
    then show ?thesis using 4 by (simp split: if_split_asm)
  qed
next
  case (5 ex s0 e cd st)
  show ?case
  proof (cases rule: while[OF 5(3)])
    case (1 g st'')
    then show ?thesis using 5 by simp
  next
    case (2 g)
    then show ?thesis using 5 by simp
  qed
next
  case (6 i xe e cd st)
  show ?case
  proof (cases rule: invoke[OF 6(2)])
    case (1 ct fb fp f e\<^sub>l cd\<^sub>l k\<^sub>l m\<^sub>l g st'')
    then show ?thesis using 6 by simp
  qed
next
  case (7 ad' i xe val e cd st)
  show ?case
  proof (cases rule: external[OF 7(3)])
    case (1 adv c g ct cn fb' v t g' v' fp f e\<^sub>l cd\<^sub>l k\<^sub>l m\<^sub>l g'' acc st'')
    moreover from 7(4) have "type (acc ad) = Some ctype" using transfer_type_same[OF 1(10)] by simp
    ultimately show ?thesis using 7(1) by simp
  next
    case (2 adv c g ct cn fb' v t g' v' acc st'')
    moreover from 7(4) have "type (acc ad) = Some ctype" using transfer_type_same[OF 2(9)] by simp
    ultimately show ?thesis using 7(2) by simp
  qed
next
  case (8 ad' ex e cd st)
  show ?case
  proof (cases rule: transfer[OF 8(2)])
    case (1 v t g adv c g' v' acc ct cn f st'')
    moreover from 8(3) have "type (acc ad) = Some ctype" using transfer_type_same[OF 1(7)] by simp
    ultimately show ?thesis using 8(1) by simp
  next
    case (2 v t g adv g' v' acc)
    moreover from 8(3) have "type (acc ad) = Some ctype" using transfer_type_same[OF 2(6)] by simp
    ultimately show ?thesis by simp
  qed
next
  case (9 id0 tp s e\<^sub>v cd st)
  show ?case
  proof (cases rule: blockNone[OF 9(2)])
    case (1 cd' mem' sck' e')
    then show ?thesis using 9 by simp
  qed
next
  case (10 id0 tp ex' s e\<^sub>v cd st)
  show ?case
  proof (cases rule: blockSome[OF 10(2)])
    case (1 v t g cd' mem' sck' e')
    then show ?thesis using 10 by simp
  qed
next
  case (11 i xe val e cd st)
  show ?case
  proof (cases rule: new[OF 11(2)])
    case (1 v t g ct cn fb e\<^sub>l cd\<^sub>l k\<^sub>l m\<^sub>l g' acc st'')
    moreover have "hash (address e) \<lfloor>contracts (accounts st (address e))\<rfloor> \<noteq> ad" using 11(3) 1(2) by auto
    ultimately show ?thesis
      using 11 transfer_type_same[OF 1(6)] incrementAccountContracts_type by simp
  qed
qed

declare lexp.simps[simp del, solidity_symbex add]
declare stmt.simps[simp del, solidity_symbex add]

end

subsection \<open>A minimal cost model\<close>

fun costs_min :: "S \<Rightarrow> Environment \<Rightarrow> CalldataT \<Rightarrow> State \<Rightarrow> Gas"
  where
  "costs_min SKIP e cd st = 0"
| "costs_min (ASSIGN lv ex) e cd st = 0"
| "costs_min (COMP s1 s2) e cd st = 0"
| "costs_min (ITE ex s1 s2) e cd st = 0"
| "costs_min (WHILE ex s0) e cd st = 1"
| "costs_min (TRANSFER ad ex) e cd st = 1"
| "costs_min (BLOCK ((id0, tp), ex) s) e cd st =0"
| "costs_min (INVOKE _ _) e cd st = 1"
| "costs_min (EXTERNAL _ _ _ _) e cd st = 1"
| "costs_min (NEW _ _ _) e cd st = 1"

fun costs_ex :: "E \<Rightarrow> Environment \<Rightarrow> CalldataT \<Rightarrow> State \<Rightarrow> Gas"
  where
  "costs_ex (E.INT _ _) e cd st = 0"
| "costs_ex (UINT _ _) e cd st = 0"
| "costs_ex (ADDRESS _) e cd st = 0"
| "costs_ex (BALANCE _) e cd st = 0"
| "costs_ex THIS e cd st = 0"
| "costs_ex SENDER e cd st = 0"
| "costs_ex VALUE e cd st = 0"
| "costs_ex (TRUE) e cd st = 0"
| "costs_ex (FALSE) e cd st = 0"
| "costs_ex (LVAL _) e cd st = 0"
| "costs_ex (PLUS _ _) e cd st = 0"
| "costs_ex (MINUS _ _) e cd st = 0"
| "costs_ex (EQUAL _ _) e cd st = 0"
| "costs_ex (LESS _ _) e cd st = 0"
| "costs_ex (AND _ _) e cd st = 0"
| "costs_ex (OR _ _) e cd st = 0"
| "costs_ex (NOT _) e cd st = 0"
| "costs_ex (CALL _ _) e cd st = 1"
| "costs_ex (ECALL _ _ _) e cd st = 1"
| "costs_ex CONTRACTS e cd st = 0"

global_interpretation solidity: statement_with_gas costs_ex fmempty costs_min
  defines stmt = "solidity.stmt" 
      and lexp = solidity.lexp
      and expr = solidity.expr
      and ssel = solidity.ssel
      and rexp = solidity.rexp
      and msel = solidity.msel
      and load = solidity.load
  by unfold_locales auto

section \<open>Examples\<close>

subsection \<open>msel\<close>

abbreviation mymemory2::MemoryT
  where "mymemory2 \<equiv>
    \<lparr>mapping = fmap_of_list
      [(STR ''3.2'', MPointer STR ''5'')],
     toploc = 1\<rparr>"

lemma "msel True (MTArray 5 (MTArray 6 (MTValue TBool))) (STR ''2'') [UINT 8 3] eempty emptyStore (mystate\<lparr>gas:=1\<rparr>) 1
= Normal ((STR ''3.2'', MTArray 6 (MTValue TBool)), 1)"  by Solidity_Symbex.solidity_symbex

lemma "msel True (MTArray 5 (MTArray 6 (MTValue TBool))) (STR ''2'') [UINT 8 3, UINT 8 4] eempty emptyStore (mystate\<lparr>gas:=1,memory:=mymemory2\<rparr>) 1
= Normal ((STR ''4.5'', MTValue TBool), 1)" by Solidity_Symbex.solidity_symbex

lemma "msel True (MTArray 5 (MTArray 6 (MTValue TBool))) (STR ''2'') [UINT 8 5] eempty emptyStore (mystate\<lparr>gas:=1,memory:=mymemory2\<rparr>) 1
= Exception (Err)" by Solidity_Symbex.solidity_symbex

end
