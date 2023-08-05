section \<open>Expressions\<close>
theory Expressions
  imports Contracts StateMonad
begin

subsection \<open>Semantics of Expressions\<close>

definition lift ::
  "(E \<Rightarrow> Environment \<Rightarrow> CalldataT \<Rightarrow> State \<Rightarrow> (Stackvalue * Type, Ex, Gas) state_monad)
  \<Rightarrow> (Types \<Rightarrow> Types \<Rightarrow> Valuetype \<Rightarrow> Valuetype \<Rightarrow> (Valuetype * Types) option)
  \<Rightarrow> E \<Rightarrow> E \<Rightarrow> Environment \<Rightarrow> CalldataT \<Rightarrow> State \<Rightarrow> (Stackvalue * Type, Ex, Gas) state_monad"
where
  "lift expr f e1 e2 e cd st \<equiv>
    (do {
      kv1 \<leftarrow> expr e1 e cd st;
      (v1, t1) \<leftarrow> case kv1 of (KValue v1, Value t1) \<Rightarrow> return (v1, t1) | _ \<Rightarrow> (throw Err::(Valuetype * Types, Ex, Gas) state_monad);
      kv2 \<leftarrow> expr e2 e cd st;
      (v2, t2) \<leftarrow> case kv2 of (KValue v2, Value t2) \<Rightarrow> return (v2, t2) | _ \<Rightarrow> (throw Err::(Valuetype * Types, Ex, Gas) state_monad);
      (v, t) \<leftarrow> (option Err (\<lambda>_::Gas. f t1 t2 v1 v2))::(Valuetype * Types, Ex, Gas) state_monad;
      return (KValue v, Value t)::(Stackvalue * Type, Ex, Gas) state_monad
    })"
declare lift_def[simp, solidity_symbex]

lemma lift_cong [fundef_cong]:
  assumes "expr e1 e cd st g = expr' e1 e cd st g"
      and "\<And>v g'. expr' e1 e cd st g = Normal (v,g') \<Longrightarrow> expr e2 e cd st g' = expr' e2 e cd st g'"
  shows "lift expr f e1 e2 e cd st g = lift expr' f e1 e2 e cd st g"
  unfolding lift_def using assms by (auto split: prod.split_asm result.split option.split_asm option.split Stackvalue.split Type.split)

datatype LType = LStackloc Location
               | LMemloc Location
               | LStoreloc Location

locale expressions_with_gas =
  fixes costs\<^sub>e :: "E \<Rightarrow> Environment \<Rightarrow> CalldataT \<Rightarrow> State \<Rightarrow> Gas"
    and ep::Environment\<^sub>P
  assumes call_not_zero[termination_simp]: "\<And>e cd st i ix. 0 < (costs\<^sub>e (CALL i ix) e cd st)"
      and ecall_not_zero[termination_simp]: "\<And>e cd st a i ix. 0 < (costs\<^sub>e (ECALL a i ix) e cd st)"
begin
function (domintros) msel::"bool \<Rightarrow> MTypes \<Rightarrow> Location \<Rightarrow> E list \<Rightarrow> Environment \<Rightarrow> CalldataT \<Rightarrow> State \<Rightarrow> (Location * MTypes, Ex, Gas) state_monad"
     and ssel::"STypes \<Rightarrow> Location \<Rightarrow> E list \<Rightarrow> Environment \<Rightarrow> CalldataT \<Rightarrow> State \<Rightarrow> (Location * STypes, Ex, Gas) state_monad"
     and expr::"E \<Rightarrow> Environment \<Rightarrow> CalldataT \<Rightarrow> State \<Rightarrow> (Stackvalue * Type, Ex, Gas) state_monad"
     and load :: "bool \<Rightarrow> (Identifier \<times> Type) list \<Rightarrow> E list \<Rightarrow> Environment \<Rightarrow> CalldataT \<Rightarrow> Stack \<Rightarrow> MemoryT \<Rightarrow> Environment \<Rightarrow> CalldataT \<Rightarrow> State \<Rightarrow> (Environment \<times> CalldataT \<times> Stack \<times> MemoryT, Ex, Gas) state_monad"
     and rexp::"L \<Rightarrow> Environment \<Rightarrow> CalldataT \<Rightarrow> State \<Rightarrow> (Stackvalue * Type, Ex, Gas) state_monad"
where
  "msel _ _ _ [] _ _ _ g = throw Err g"
| "msel _ (MTValue _) _ _ _ _ _ g = throw Err g"
| "msel _ (MTArray al t) loc [x] env cd st g =
    (do {
      kv \<leftarrow> expr x env cd st;
      (v, t') \<leftarrow> case kv of (KValue v, Value t') \<Rightarrow> return (v, t') | _ \<Rightarrow> throw Err;
      assert Err (\<lambda>_. less t' (TUInt 256) v (ShowL\<^sub>i\<^sub>n\<^sub>t al) = Some (ShowL\<^sub>b\<^sub>o\<^sub>o\<^sub>l True, TBool));
      return (hash loc v, t)
    }) g"
(*
  Note that it is indeed possible to modify the state while evaluating the expression
  to determine the index of the array to look up.
*)
| "msel mm (MTArray al t) loc (x # y # ys) env cd st g =
    (do {
      kv \<leftarrow> expr x env cd st;
      (v, t') \<leftarrow> case kv of (KValue v, Value t') \<Rightarrow> return (v,t') | _ \<Rightarrow> throw Err;
      assert Err (\<lambda>_. less t' (TUInt 256) v (ShowL\<^sub>i\<^sub>n\<^sub>t al) = Some (ShowL\<^sub>b\<^sub>o\<^sub>o\<^sub>l True, TBool));
      l \<leftarrow> case accessStore (hash loc v) (if mm then memory st else cd) of Some (MPointer l) \<Rightarrow> return l | _ \<Rightarrow> throw Err;
      msel mm t l (y#ys) env cd st
    }) g"
| "ssel tp loc Nil _ _ _ g = return (loc, tp) g"
| "ssel (STValue _) _ (_ # _) _ _ _ g = throw Err g"
| "ssel (STArray al t) loc (x # xs) env cd st g =
    (do {
      kv \<leftarrow> expr x env cd st;
      (v, t') \<leftarrow> case kv of (KValue v, Value t') \<Rightarrow> return (v, t') | _ \<Rightarrow> throw Err;
      assert Err (\<lambda>_. less t' (TUInt 256) v (ShowL\<^sub>i\<^sub>n\<^sub>t al) = Some (ShowL\<^sub>b\<^sub>o\<^sub>o\<^sub>l True, TBool));
      ssel t (hash loc v) xs env cd st
    }) g"
| "ssel (STMap _ t) loc (x # xs) env cd st g =
    (do {
      kv \<leftarrow> expr x env cd st;
      v \<leftarrow> case kv of (KValue v, _) \<Rightarrow> return v | _ \<Rightarrow> throw Err;
      ssel t (hash loc v) xs env cd st
    }) g"
| "expr (E.INT b x) e cd st g =
    (do {
      assert Gas (\<lambda>g. g > costs\<^sub>e (E.INT b x) e cd st);
      modify (\<lambda>g. g - costs\<^sub>e (E.INT b x) e cd st);
      assert Err (\<lambda>_. b \<in> vbits);
      return (KValue (createSInt b x), Value (TSInt b))
    }) g"
| "expr (UINT b x) e cd st g =
    (do {
      assert Gas (\<lambda>g. g > costs\<^sub>e (UINT b x) e cd st);
      modify (\<lambda>g. g - costs\<^sub>e (UINT b x) e cd st);
      assert Err (\<lambda>_. b \<in> vbits);
      return (KValue (createUInt b x), Value (TUInt b))
  }) g"
| "expr (ADDRESS ad) e cd st g =
    (do {
      assert Gas (\<lambda>g. g > costs\<^sub>e (ADDRESS ad) e cd st);
      modify (\<lambda>g. g - costs\<^sub>e  (ADDRESS ad) e cd st);
      return (KValue ad, Value TAddr)
    }) g"
| "expr (BALANCE ad) e cd st g =
    (do {
      assert Gas (\<lambda>g. g > costs\<^sub>e (BALANCE ad) e cd st);
      modify (\<lambda>g. g - costs\<^sub>e  (BALANCE ad) e cd st);
      kv \<leftarrow> expr ad e cd st;
      adv \<leftarrow> case kv of (KValue adv, Value TAddr) \<Rightarrow> return adv | _ \<Rightarrow> throw Err; 
      return (KValue (bal ((accounts st) adv)), Value (TUInt 256))
    }) g"
| "expr THIS e cd st g =
    (do {
      assert Gas (\<lambda>g. g > costs\<^sub>e THIS e cd st);
      modify (\<lambda>g. g - costs\<^sub>e THIS e cd st);
      return (KValue (address e), Value TAddr)
    }) g"
| "expr SENDER e cd st g =
    (do {
      assert Gas (\<lambda>g. g > costs\<^sub>e SENDER e cd st);
      modify (\<lambda>g. g - costs\<^sub>e SENDER e cd st);
      return (KValue (sender e), Value TAddr)
    }) g"
| "expr VALUE e cd st g =
    (do {
      assert Gas (\<lambda>g. g > costs\<^sub>e VALUE e cd st);
      modify (\<lambda>g. g - costs\<^sub>e VALUE e cd st);
      return (KValue (svalue e), Value (TUInt 256))
    }) g"
| "expr TRUE e cd st g =
    (do {
      assert Gas (\<lambda>g. g > costs\<^sub>e TRUE e cd st);
      modify (\<lambda>g. g - costs\<^sub>e TRUE e cd st);
      return (KValue (ShowL\<^sub>b\<^sub>o\<^sub>o\<^sub>l True), Value TBool)
    }) g"
| "expr FALSE e cd st g =
    (do {
      assert Gas (\<lambda>g. g > costs\<^sub>e FALSE e cd st);
      modify (\<lambda>g. g - costs\<^sub>e FALSE e cd st);
      return (KValue (ShowL\<^sub>b\<^sub>o\<^sub>o\<^sub>l False), Value TBool)
    }) g"
| "expr (NOT x) e cd st g =
    (do {
      assert Gas (\<lambda>g. g > costs\<^sub>e (NOT x) e cd st);
      modify (\<lambda>g. g - costs\<^sub>e (NOT x) e cd st);
      kv \<leftarrow> expr x e cd st;
      v \<leftarrow> case kv of (KValue v, Value TBool) \<Rightarrow> return v | _ \<Rightarrow> throw Err;
      (if v = ShowL\<^sub>b\<^sub>o\<^sub>o\<^sub>l True then expr FALSE e cd st
       else if v = ShowL\<^sub>b\<^sub>o\<^sub>o\<^sub>l False then expr TRUE e cd st
       else throw Err)
    }) g"
| "expr (PLUS e1 e2) e cd st g =
    (do {
      assert Gas (\<lambda>g. g > costs\<^sub>e (PLUS e1 e2) e cd st);
      modify (\<lambda>g. g - costs\<^sub>e (PLUS e1 e2) e cd st);
      lift expr add e1 e2 e cd st
    }) g"
| "expr (MINUS e1 e2) e cd st g =
    (do {
      assert Gas (\<lambda>g. g > costs\<^sub>e (MINUS e1 e2) e cd st);
      modify (\<lambda>g. g - costs\<^sub>e (MINUS e1 e2) e cd st);
      lift expr sub e1 e2 e cd st
    }) g"
| "expr (LESS e1 e2) e cd st g =
    (do {
      assert Gas (\<lambda>g. g > costs\<^sub>e (LESS e1 e2) e cd st);
      modify (\<lambda>g. g - costs\<^sub>e (LESS e1 e2) e cd st);
      lift expr less e1 e2 e cd st
    }) g"
| "expr (EQUAL e1 e2) e cd st g =
    (do {
      assert Gas (\<lambda>g. g > costs\<^sub>e (EQUAL e1 e2) e cd st);
      modify (\<lambda>g. g - costs\<^sub>e (EQUAL e1 e2) e cd st);
      lift expr equal e1 e2 e cd st
    }) g"
| "expr (AND e1 e2) e cd st g =
    (do {
      assert Gas (\<lambda>g. g > costs\<^sub>e (AND e1 e2) e cd st);
      modify (\<lambda>g. g - costs\<^sub>e (AND e1 e2) e cd st);
      lift expr vtand e1 e2 e cd st
    }) g"
| "expr (OR e1 e2) e cd st g =
    (do {
      assert Gas (\<lambda>g. g > costs\<^sub>e (OR e1 e2) e cd st);
      modify (\<lambda>g. g - costs\<^sub>e (OR e1 e2) e cd st);
      lift expr vtor e1 e2 e cd st
    }) g"
| "expr (LVAL i) e cd st g =
    (do {
      assert Gas (\<lambda>g. g > costs\<^sub>e (LVAL i) e cd st);
      modify (\<lambda>g. g - costs\<^sub>e (LVAL i) e cd st);
      rexp i e cd st
    }) g"
(* Notes about method calls:
   - Internal method calls use a fresh environment and stack but keep the memory [1]
   - External method calls use a fresh environment and stack and memory [2]
   [1]: https://docs.soliditylang.org/en/v0.8.5/control-structures.html#internal-function-calls
   [2]: https://docs.soliditylang.org/en/v0.8.5/control-structures.html#external-function-calls
*)
| "expr (CALL i xe) e cd st g =
    (do {
      assert Gas (\<lambda>g. g > costs\<^sub>e (CALL i xe) e cd st);
      modify (\<lambda>g. g - costs\<^sub>e (CALL i xe) e cd st);
      (ct, _) \<leftarrow> option Err (\<lambda>_. ep $$ (contract e));
      (fp, x) \<leftarrow> case ct $$ i of Some (Function (fp, False, x)) \<Rightarrow> return (fp, x) | _ \<Rightarrow> throw Err;
      let e' = ffold_init ct (emptyEnv (address e) (contract e) (sender e) (svalue e)) (fmdom ct);
      (e\<^sub>l, cd\<^sub>l, k\<^sub>l, m\<^sub>l) \<leftarrow> load False fp xe e' emptyStore emptyStore (memory st) e cd st;
      expr x e\<^sub>l cd\<^sub>l (st\<lparr>stack:=k\<^sub>l, memory:=m\<^sub>l\<rparr>)
    }) g"
(*It is not allowed to transfer money to external function calls*)
| "expr (ECALL ad i xe) e cd st g =
    (do {
      assert Gas (\<lambda>g. g > costs\<^sub>e (ECALL ad i xe) e cd st);
      modify (\<lambda>g. g - costs\<^sub>e (ECALL ad i xe) e cd st);
      kad \<leftarrow> expr ad e cd st;
      adv \<leftarrow> case kad of (KValue adv, Value TAddr) \<Rightarrow> return adv | _ \<Rightarrow> throw Err;
      assert Err (\<lambda>_. adv \<noteq> address e);
      c \<leftarrow> case type (accounts st adv) of Some (Contract c) \<Rightarrow> return c | _ \<Rightarrow> throw Err;
      (ct, _) \<leftarrow> option Err (\<lambda>_. ep $$ c);
      (fp, x) \<leftarrow> case ct $$ i of Some (Function (fp, True, x)) \<Rightarrow> return (fp, x) | _ \<Rightarrow> throw Err;
      let e' = ffold_init ct (emptyEnv adv c (address e) (ShowL\<^sub>n\<^sub>a\<^sub>t 0)) (fmdom ct);
      (e\<^sub>l, cd\<^sub>l, k\<^sub>l, m\<^sub>l) \<leftarrow> load True fp xe e' emptyStore emptyStore emptyStore e cd st;
      expr x e\<^sub>l cd\<^sub>l (st\<lparr>stack:=k\<^sub>l, memory:=m\<^sub>l\<rparr>)
    }) g"
| "load cp ((i\<^sub>p, t\<^sub>p)#pl) (ex#el) e\<^sub>v' cd' sck' mem' e\<^sub>v cd st g =
    (do {
      (v, t) \<leftarrow> expr ex e\<^sub>v cd st;
      (c, m, k, e) \<leftarrow> case decl i\<^sub>p t\<^sub>p (Some (v,t)) cp cd (memory st) (storage st) (cd', mem',  sck', e\<^sub>v') of Some (c, m, k, e) \<Rightarrow> return (c, m, k, e) | None \<Rightarrow> throw Err;
      load cp pl el e c k m e\<^sub>v cd st
    }) g"
| "load _ [] (_#_) _ _ _ _ _ _ _ g = throw Err g"
| "load _ (_#_) [] _ _ _ _ _ _ _ g = throw Err g"
| "load _ [] [] e\<^sub>v' cd' sck' mem' e\<^sub>v cd st g = return (e\<^sub>v', cd', sck', mem') g"

| "rexp (Id i) e cd st g =
    (case fmlookup (denvalue e) i of
      Some (tp, Stackloc l) \<Rightarrow>
        (case accessStore l (stack st) of
          Some (KValue v) \<Rightarrow> return (KValue v, tp)
        | Some (KCDptr p) \<Rightarrow> return (KCDptr p, tp)
        | Some (KMemptr p) \<Rightarrow> return (KMemptr p, tp)
        | Some (KStoptr p) \<Rightarrow> return (KStoptr p, tp)
        | _ \<Rightarrow> throw Err)
    | Some (Storage (STValue t), Storeloc l) \<Rightarrow> return (KValue (accessStorage t l (storage st (address e))), Value t)
    | Some (Storage (STArray x t), Storeloc l) \<Rightarrow> return (KStoptr l, Storage (STArray x t))
    | _ \<Rightarrow> throw Err) g"
| "rexp (Ref i r) e cd st g =
    (case fmlookup (denvalue e) i of
      Some (tp, (Stackloc l)) \<Rightarrow>
        (case accessStore l (stack st) of
          Some (KCDptr l') \<Rightarrow>
            do {
              t \<leftarrow> case tp of Calldata t \<Rightarrow> return t | _ \<Rightarrow> throw Err;
              (l'', t') \<leftarrow> msel False t l' r e cd st;
              (case t' of
                MTValue t'' \<Rightarrow>
                  do {
                    v \<leftarrow> case accessStore l'' cd of Some (MValue v) \<Rightarrow> return v | _ \<Rightarrow> throw Err;
                    return (KValue v, Value t'')
                  }
              | MTArray x t'' \<Rightarrow>
                  do {
                    p \<leftarrow> case accessStore l'' cd of Some (MPointer p) \<Rightarrow> return p | _ \<Rightarrow> throw Err;
                    return (KCDptr p, Calldata (MTArray x t''))
                  }
              )
            }
        | Some (KMemptr l') \<Rightarrow>
            do {
              t \<leftarrow> case tp of Memory t \<Rightarrow> return t | _ \<Rightarrow> throw Err;
              (l'', t') \<leftarrow> msel True t l' r e cd st;
              (case t' of
                MTValue t'' \<Rightarrow>
                  do {
                    v \<leftarrow> case accessStore l'' (memory st) of Some (MValue v) \<Rightarrow> return v | _ \<Rightarrow> throw Err;
                    return (KValue v, Value t'')
                  }
              | MTArray x t'' \<Rightarrow>
                  do {
                    p \<leftarrow> case accessStore l'' (memory st) of Some (MPointer p) \<Rightarrow> return p | _ \<Rightarrow> throw Err;
                    return (KMemptr p, Memory (MTArray x t''))
                  }
              )
            }
        | Some (KStoptr l') \<Rightarrow>
            do {
              t \<leftarrow> case tp of Storage t \<Rightarrow> return t | _ \<Rightarrow> throw Err;
              (l'', t') \<leftarrow> ssel t l' r e cd st;
              (case t' of
                STValue t'' \<Rightarrow> return (KValue (accessStorage t'' l'' (storage st (address e))), Value t'')
              | STArray _ _ \<Rightarrow> return (KStoptr l'', Storage t')
              | STMap _ _   \<Rightarrow> return (KStoptr l'', Storage t'))
             }
        | _ \<Rightarrow> throw Err)
    | Some (tp, (Storeloc l)) \<Rightarrow>
          do {
            t \<leftarrow> case tp of Storage t \<Rightarrow> return t | _ \<Rightarrow> throw Err;
            (l', t') \<leftarrow> ssel t l r e cd st;
            (case t' of
              STValue t'' \<Rightarrow> return (KValue (accessStorage t'' l' (storage st (address e))), Value t'')
            | STArray _ _ \<Rightarrow> return (KStoptr l', Storage t')
            | STMap _ _   \<Rightarrow> return (KStoptr l', Storage t'))
          }
    | None \<Rightarrow> throw Err) g"
| "expr CONTRACTS e cd st g =
    (do {
      assert Gas (\<lambda>g. g > costs\<^sub>e CONTRACTS e cd st);
      modify (\<lambda>g. g - costs\<^sub>e CONTRACTS e cd st);
      prev \<leftarrow> case contracts (accounts st (address e)) of 0 \<Rightarrow> throw Err | Suc n \<Rightarrow> return n;
      return (KValue (hash (address e) (ShowL\<^sub>n\<^sub>a\<^sub>t prev)), Value TAddr)
    }) g"
  by pat_completeness auto

subsection \<open>Termination\<close>

text \<open>To prove termination we first need to show that expressions do not increase gas\<close>

lemma lift_gas:
  assumes "lift expr f e1 e2 e cd st g = Normal (v, g')"
      and "\<And>v g'. expr e1 e cd st g = Normal (v, g') \<Longrightarrow> g' \<le> g"
      and "\<And>v g' v' t' g''. expr e1 e cd st g = Normal (v, g')
            \<Longrightarrow> expr e2 e cd st g' = Normal (v', g'')
          \<Longrightarrow> g'' \<le> g'"
      shows "g' \<le> g"
proof (cases "expr e1 e cd st g")
  case (n a g0')
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
        proof (cases "expr e2 e cd st g0'")
          case r2: (n a' g0'')
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
                    with assms n Pair KValue Value r2 p2 v2 t2 Some have "g0'\<le> g" by simp
                    moreover from assms n Pair KValue Value r2 p2 v2 t2 Some have "g0''\<le>g0'" by simp
                    moreover from assms n Pair KValue Value r2 p2 v2 t2 Some have "g'=g0''" by (simp split:prod.split_asm)
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

lemma msel_ssel_expr_load_rexp_dom_gas[rule_format]:
    "msel_ssel_expr_load_rexp_dom (Inl (Inl (c1, t1, l1, xe1, ev1, cd1, st1, g1)))
      \<Longrightarrow> (\<forall>v1' g1'. msel c1 t1 l1 xe1 ev1 cd1 st1 g1 = Normal (v1', g1') \<longrightarrow> g1' \<le> g1)"
    "msel_ssel_expr_load_rexp_dom (Inl (Inr (t2, l2, xe2, ev2, cd2, st2, g2)))
      \<Longrightarrow> (\<forall>v2' g2'. ssel t2 l2 xe2 ev2 cd2 st2 g2 = Normal (v2', g2') \<longrightarrow> g2' \<le> g2)"
    "msel_ssel_expr_load_rexp_dom (Inr (Inl (e4, ev4, cd4, st4, g4)))
      \<Longrightarrow> (\<forall>v4' g4'. expr e4 ev4 cd4 st4 g4 = Normal (v4', g4') \<longrightarrow> g4' \<le> g4)"
    "msel_ssel_expr_load_rexp_dom (Inr (Inr (Inl (lcp, lis, lxs, lev0, lcd0, lk, lm, lev, lcd, lst, lg))))
      \<Longrightarrow> (\<forall>ev cd k m g'. load lcp lis lxs lev0 lcd0 lk lm lev lcd lst lg = Normal ((ev, cd, k, m), g') \<longrightarrow> g' \<le> lg \<and> address ev = address lev0 \<and> sender ev = sender lev0 \<and> svalue ev = svalue lev0)"
    "msel_ssel_expr_load_rexp_dom (Inr (Inr (Inr (l3, ev3, cd3, st3, g3))))
      \<Longrightarrow> (\<forall>v3' g3'. rexp l3 ev3 cd3 st3 g3 = Normal (v3', g3') \<longrightarrow> g3' \<le> g3)"
proof (induct rule: msel_ssel_expr_load_rexp.pinduct
[where ?P1.0="\<lambda>c1 t1 l1 xe1 ev1 cd1 st1 g1. (\<forall>l1' g1'. msel c1 t1 l1 xe1 ev1 cd1 st1 g1 = Normal (l1', g1') \<longrightarrow> g1' \<le> g1)"
   and ?P2.0="\<lambda>t2 l2 xe2 ev2 cd2 st2 g2. (\<forall>v2' g2'. ssel t2 l2 xe2 ev2 cd2 st2 g2 = Normal (v2', g2') \<longrightarrow> g2' \<le> g2)"
   and ?P3.0="\<lambda>e4 ev4 cd4 st4 g4. (\<forall>v4' g4'. expr e4 ev4 cd4 st4 g4 = Normal (v4', g4') \<longrightarrow> g4' \<le> g4)"
   and ?P4.0="\<lambda>lcp lis lxs lev0 lcd0 lk lm lev lcd lst lg. (\<forall>ev cd k m g'. load lcp lis lxs lev0 lcd0 lk lm lev lcd lst lg = Normal ((ev, cd, k, m), g') \<longrightarrow> g' \<le> lg \<and> address ev = address lev0 \<and> sender ev = sender lev0 \<and> svalue ev = svalue lev0)"
   and ?P5.0="\<lambda>l3 ev3 cd3 st3 g3. (\<forall>v3' g3'. rexp l3 ev3 cd3 st3 g3 = Normal (v3', g3') \<longrightarrow> g3' \<le> g3)"
])
  case 1
  then show ?case using msel.psimps(1) by auto
next
  case 2
  then show ?case using msel.psimps(2) by auto
next                                                                                                                                                                         
  case 3
  then show ?case using msel.psimps(3) by (auto split: if_split_asm Type.split_asm Stackvalue.split_asm prod.split_asm StateMonad.result.split_asm)
next
  case (4 mm al t loc x y ys env cd st g)
  show ?case
  proof (rule allI[THEN allI, OF impI])
    fix v1' g1' assume a1: "msel mm (MTArray al t) loc (x # y # ys) env cd st g = Normal (v1', g1')"
    show "g1' \<le> g"
    proof (cases v1')
      case (Pair l1' t1')
      then show ?thesis
      proof (cases "expr x env cd st g")
        case (n a g')
        then show ?thesis
        proof (cases a)
          case p2: (Pair b c)
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
                proof (cases "accessStore (hash loc v) (if mm then memory st else cd)")
                  case None
                  with 4 a1 n p2 KValue Value l show ?thesis using msel.psimps(4) by simp
                next
                  case (Some a)
                  then show ?thesis
                  proof (cases a)
                    case (MValue _)
                    with 4 a1 n p2 KValue Value Some l show ?thesis using msel.psimps(4) by simp
                  next
                    case (MPointer l)
                    with n p2 KValue Value l Some
                    have "msel mm (MTArray al t) loc (x # y # ys) env cd st g = msel mm t l (y # ys) env cd st g'"
                      using msel.psimps(4) 4(1) by simp
                    moreover from n have "g' \<le> g" using 4(2) by simp
                    moreover from a1 MPointer n Pair p2 KValue Value l Some
                    have "g1' \<le> g'" using msel.psimps(4) 4(3) 4(1) by simp
                    ultimately show ?thesis by simp
                  qed
                qed
              next
                assume "\<not> less t' (TUInt 256) v (ShowL\<^sub>i\<^sub>n\<^sub>t al) = Some (ShowL\<^sub>b\<^sub>o\<^sub>o\<^sub>l True, TBool)"
                with 4 a1 n p2 KValue Value show ?thesis using msel.psimps(4) by simp
              qed
            next
              case (Calldata _)
              with 4 a1 n p2 KValue show ?thesis using msel.psimps(4) by simp
            next
              case (Memory _)
              with 4 a1 n p2 KValue show ?thesis using msel.psimps(4) by simp
            next
              case (Storage _)
              with 4 a1 n p2 KValue show ?thesis using msel.psimps(4) by simp
            qed
          next
            case (KCDptr _)
            with 4 a1 n p2 show ?thesis using msel.psimps(4) by simp
          next
            case (KMemptr _)
            with 4 a1 n p2 show ?thesis using msel.psimps(4) by simp
          next
            case (KStoptr _)
            with 4 a1 n p2 show ?thesis using msel.psimps(4) by simp
          qed
        qed
      next
        case (e _)
        with 4 a1 show ?thesis using msel.psimps(4) by simp
      qed
    qed
  qed
next
  case 5
  then show ?case using ssel.psimps(1) by auto
next
  case 6
  then show ?case using ssel.psimps(2) by auto
next
  case (7 al t loc x xs env cd st g)
  show ?case
  proof (rule allI[THEN allI, OF impI])
    fix v2' g2' assume a1: "ssel (STArray al t) loc (x # xs) env cd st g = Normal (v2', g2')"
    show "g2' \<le> g"
    proof (cases v2')
      case (Pair l2' t2')
      then show ?thesis
      proof (cases "expr x env cd st g")
        case (n a g'')
        then show ?thesis
        proof (cases a)
          case p2: (Pair b c)
          then show ?thesis
          proof (cases b)
            case (KValue v)
            then show ?thesis
            proof (cases c)
              case (Value t')
              then show ?thesis
              proof (cases)
                assume l: "less t' (TUInt 256) v (ShowL\<^sub>i\<^sub>n\<^sub>t al) = Some (ShowL\<^sub>b\<^sub>o\<^sub>o\<^sub>l True, TBool)"
                with n p2 KValue Value l
                have "ssel (STArray al t) loc (x # xs) env cd st g = ssel t (hash loc v) xs env cd st g''"
                using ssel.psimps(3) 7(1) by simp
                moreover from n have "g'' \<le> g" using 7(2) by simp
                moreover from a1 n Pair p2 KValue Value l
                have "g2' \<le> g''" using ssel.psimps(3) 7(3) 7(1) by simp
                ultimately show ?thesis by simp
              next
                assume "\<not> less t' (TUInt 256) v (ShowL\<^sub>i\<^sub>n\<^sub>t al) = Some (ShowL\<^sub>b\<^sub>o\<^sub>o\<^sub>l True, TBool)"
                with 7 a1 n p2 KValue Value show ?thesis using ssel.psimps(3) by simp
              qed
            next
              case (Calldata _)
              with 7 a1 n p2 KValue show ?thesis using ssel.psimps(3) by simp
            next
              case (Memory _)
              with 7 a1 n p2 KValue show ?thesis using ssel.psimps(3) by simp
            next
              case (Storage _)
              with 7 a1 n p2 KValue show ?thesis using ssel.psimps(3) by simp
            qed
          next
            case (KCDptr _)
            with 7 a1 n p2 show ?thesis using ssel.psimps(3) by simp
          next
            case (KMemptr _)
            with 7 a1 n p2 show ?thesis using ssel.psimps(3) by simp
          next
            case (KStoptr x4)
            with 7 a1 n p2 show ?thesis using ssel.psimps(3) by simp
          qed
        qed
      next
        case (e _)
        with 7 a1 show ?thesis using ssel.psimps(3) by simp
      qed
    qed
  qed
next
  case (8 vv t loc x xs env cd st g)
  show ?case
  proof (rule allI[THEN allI, OF impI])
    fix v2' g2' assume a1: "ssel (STMap vv t) loc (x # xs) env cd st g = Normal (v2', g2')"
    show "g2' \<le> g"
    proof (cases v2')
      case (Pair l2' t2')
      then show ?thesis
      proof (cases "expr x env cd st g")
        case (n a g')
        then show ?thesis
        proof (cases a)
          case p2: (Pair b c)
          then show ?thesis
          proof (cases b)
            case (KValue v)
            with 8 n p2 have "ssel (STMap vv t) loc (x # xs) env cd st g = ssel t (hash loc v) xs env cd st g'" using ssel.psimps(4) by simp
            moreover from n have "g' \<le> g" using 8(2) by simp
            moreover from a1 n Pair p2 KValue
            have "g2' \<le> g'" using ssel.psimps(4) 8(3) 8(1) by simp
            ultimately show ?thesis by simp
          next
            case (KCDptr _)
            with 8 a1 n p2 show ?thesis using ssel.psimps(4) by simp
          next
            case (KMemptr _)
            with 8 a1 n p2 show ?thesis using ssel.psimps(4) by simp
          next
            case (KStoptr _)
            with 8 a1 n p2 show ?thesis using ssel.psimps(4) by simp
          qed
        qed
      next
        case (e _)
        with 8 a1 show ?thesis using ssel.psimps(4) by simp
      qed
    qed
  qed
next
  case 9
  then show ?case using expr.psimps(1) by (simp split:if_split_asm)
next
  case 10
  then show ?case using expr.psimps(2) by (simp split:if_split_asm)
next
  case 11
  then show ?case using expr.psimps(3) by simp
next
  case (12 ad e cd st g)
  define gc where "gc = costs\<^sub>e (BALANCE ad) e cd st"
  show ?case
  proof (rule allI[THEN allI, OF impI])
    fix g4 xa
    assume *: "expr (BALANCE ad) e cd st g = Normal (xa, g4)"
    show "g4 \<le> g"
    proof (cases)
      assume "g \<le> gc"
      with 12 gc_def * show ?thesis using expr.psimps(4) by simp
    next
      assume gcost: "\<not> g \<le> gc"
      then show ?thesis
      proof (cases "expr ad e cd st (g - gc)")
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
                case (TSInt _)
                with 12 gc_def * gcost n Pair KValue Value show ?thesis using expr.psimps(4)[of ad e cd st] by simp
              next
                case (TUInt _)
                with 12 gc_def * gcost n Pair KValue Value show ?thesis using expr.psimps(4)[of ad e cd st] by simp
              next
                case TBool
                with 12 gc_def * gcost n Pair KValue Value show ?thesis using expr.psimps(4)[of ad e cd st] by simp
              next
                case TAddr
                with 12(2)[where ?s'a="g-costs\<^sub>e (BALANCE ad) e cd st"] gc_def * gcost n Pair KValue Value show "g4 \<le> g" using expr.psimps(4)[OF 12(1)] by simp
              qed
            next
              case (Calldata _)
              with 12 gc_def * gcost n Pair KValue show ?thesis using expr.psimps(4)[of ad e cd st] by simp
            next
              case (Memory _)
              with 12 gc_def * gcost n Pair KValue show ?thesis using expr.psimps(4)[of ad e cd st] by simp
            next
              case (Storage _)
              with 12 gc_def * gcost n Pair KValue show ?thesis using expr.psimps(4)[of ad e cd st] by simp
            qed
          next
            case (KCDptr _)
            with 12 gc_def * gcost n Pair show ?thesis using expr.psimps(4)[of ad e cd st] by simp
          next
            case (KMemptr _)
            with 12 gc_def * gcost n Pair show ?thesis using expr.psimps(4)[of ad e cd st] by simp
          next
            case (KStoptr _)
            with 12 gc_def * gcost n Pair show ?thesis using expr.psimps(4)[of ad e cd st] by simp
          qed
        qed
      next
        case (e _)
        with 12 gc_def * gcost show ?thesis using expr.psimps(4)[of ad e cd st] by simp
      qed
    qed
  qed
next
  case 13
  then show ?case using expr.psimps(5) by simp
next
  case 14
  then show ?case using expr.psimps(6) by simp
next
  case 15
  then show ?case using expr.psimps(7) by simp
next
  case 16
  then show ?case using expr.psimps(8) by simp
next
  case 17
  then show ?case using expr.psimps(9) by simp
next
  case (18 x e cd st g)
  define gc where "gc = costs\<^sub>e (NOT x) e cd st"
  show ?case
  proof (rule allI[THEN allI, OF impI])
    fix v4 g4' assume a1: "expr (NOT x) e cd st g = Normal (v4, g4')"
    show "g4' \<le> g"
    proof (cases v4)
      case (Pair l4 t4)
      show ?thesis
      proof (cases)
        assume "g \<le> gc"
        with gc_def a1 show ?thesis using expr.psimps(10)[OF 18(1)] by simp
      next
        assume gcost: "\<not> g \<le> gc"
        then show ?thesis
        proof (cases "expr x e cd st (g - gc)")
          case (n a g')
          then show ?thesis
          proof (cases a)
            case p2: (Pair b c)
            then show ?thesis
            proof (cases b)
              case (KValue v)
              then show ?thesis
              proof (cases c)
                case (Value t)
                then show ?thesis
                proof (cases t)
                  case (TSInt x1)
                  with a1 gc_def gcost n p2 KValue Value show ?thesis using expr.psimps(10)[OF 18(1)] by simp
                next
                  case (TUInt x2)
                  with a1 gc_def gcost n p2 KValue Value show ?thesis using expr.psimps(10)[OF 18(1)] by simp
                next
                  case TBool
                  then show ?thesis
                  proof (cases)
                    assume v_def: "v = ShowL\<^sub>b\<^sub>o\<^sub>o\<^sub>l True"
                    with 18(1) gc_def gcost n p2 KValue Value TBool have "expr (NOT x) e cd st g = expr FALSE e cd st g' " using expr.psimps(10)[OF 18(1)] by simp
                    moreover from 18(2) gc_def gcost n p2 have "g' \<le> g-gc" by simp
                    moreover from 18(3)[OF _ _ n] a1 gc_def gcost have "g4' \<le> g'" using expr.psimps(10)[OF 18(1)] n Pair p2 KValue Value TBool v_def by simp
                    ultimately show ?thesis by arith
                   next
                    assume v_def: "\<not> v = ShowL\<^sub>b\<^sub>o\<^sub>o\<^sub>l True"
                    then show ?thesis
                    proof (cases)
                      assume v_def2: "v = ShowL\<^sub>b\<^sub>o\<^sub>o\<^sub>l False"
                      with 18(1) gc_def gcost n p2 KValue Value v_def TBool have "expr (NOT x) e cd st g = expr TRUE e cd st g'" using expr.psimps(10) by simp
                      moreover from 18(2)[where ?s'a="g-costs\<^sub>e (NOT x) e cd st"] gc_def gcost n p2 have "g' \<le> g" by simp
                      moreover from 18(4)[OF _ _ n] a1 gc_def gcost have "g4' \<le> g'" using expr.psimps(10)[OF 18(1)] n Pair p2 KValue Value TBool v_def v_def2 by simp
                      ultimately show ?thesis by arith
                    next
                      assume "\<not> v = ShowL\<^sub>b\<^sub>o\<^sub>o\<^sub>l False"
                      with 18(1) a1 gc_def gcost n p2 KValue Value v_def TBool show ?thesis using expr.psimps(10) by simp
                    qed
                  qed
                next
                  case TAddr
                  with 18(1) a1 gc_def gcost n p2 KValue Value show ?thesis using expr.psimps(10) by simp
                qed
              next
                case (Calldata _)
                with 18(1) a1 gc_def gcost n p2 KValue show ?thesis using expr.psimps(10) by simp
              next
                case (Memory _)
                with 18(1) a1 gc_def gcost n p2 KValue show ?thesis using expr.psimps(10) by simp
              next
                case (Storage _)
                with 18(1) a1 gc_def gcost n p2 KValue show ?thesis using expr.psimps(10) by simp
              qed
            next
              case (KCDptr _)
              with 18(1) a1 gc_def gcost n p2 show ?thesis using expr.psimps(10) by simp
            next
              case (KMemptr _)
              with 18(1) a1 gc_def gcost n p2 show ?thesis using expr.psimps(10) by simp
            next
              case (KStoptr _)
              with 18(1) a1 gc_def gcost n p2 show ?thesis using expr.psimps(10) by simp
            qed
          qed
        next
          case (e _)
          with 18(1) a1 gc_def gcost show ?thesis using expr.psimps(10) by simp
        qed
      qed
    qed
  qed
next
  case (19 e1 e2 e cd st g)
  define gc where "gc = costs\<^sub>e (PLUS e1 e2) e cd st"
  show ?case
  proof (rule allI[THEN allI, OF impI])
    fix g4 xa assume e_def: "expr (PLUS e1 e2) e cd st g = Normal (xa, g4)"
    then show "g4 \<le> g"
    proof (cases)
      assume "g \<le> gc"
      with 19(1) e_def show ?thesis using expr.psimps(11) gc_def by simp
    next
      assume "\<not> g \<le> gc"
      then have *: "assert Gas ((<) (costs\<^sub>e (PLUS e1 e2) e cd st)) g = Normal ((), g)" using gc_def by simp
      with 19(1) e_def gc_def have lift:"lift expr add e1 e2 e cd st (g - gc) = Normal (xa, g4)" using expr.psimps(11)[OF 19(1)] by simp
      moreover have **: "modify (\<lambda>g. g - costs\<^sub>e (PLUS e1 e2) e cd st) g = Normal ((), g - costs\<^sub>e (PLUS e1 e2) e cd st)" by simp
      with 19(2)[OF * **] have "\<And>g4' v4 t4. expr e1 e cd st (g-gc) = Normal ((v4, t4), g4') \<Longrightarrow> g4' \<le> g - gc" unfolding gc_def by simp
      moreover obtain v g' where ***: "expr e1 e cd st (g - costs\<^sub>e (PLUS e1 e2) e cd st) = Normal (v, g')" using expr.psimps(11)[OF 19(1)] e_def by (simp split:if_split_asm result.split_asm prod.split_asm)
      with 19(3)[OF * ** ***] have "\<And>v t g' v' t' g''. expr e1 e cd st (g-gc) = Normal ((KValue v, Value t), g') \<Longrightarrow> expr e2 e cd st g' = Normal ((v', t'), g'') \<Longrightarrow> g'' \<le> g'" unfolding gc_def by simp
      ultimately show "g4 \<le> g" using lift_gas[OF lift] `\<not> g \<le> gc` by (simp split:result.split_asm Stackvalue.split_asm Type.split_asm prod.split_asm)
    qed
  qed
next
  case (20 e1 e2 e cd st g)
  define gc where "gc = costs\<^sub>e (MINUS e1 e2) e cd st"
  show ?case
  proof (rule allI[THEN allI, OF impI])
    fix g4 xa assume e_def: "expr (MINUS e1 e2) e cd st g = Normal (xa, g4)"
    then show "g4 \<le> g"
    proof (cases)
      assume "g \<le> gc"
      with 20(1) e_def show ?thesis using expr.psimps(12) gc_def by simp
    next
      assume "\<not> g \<le> gc"
      then have *: "assert Gas ((<) (costs\<^sub>e (MINUS e1 e2) e cd st)) g = Normal ((), g)" using gc_def by simp
      with 20(1) e_def gc_def have lift:"lift expr sub e1 e2 e cd st (g - gc) = Normal (xa, g4)" using expr.psimps(12)[OF 20(1)] by simp
      moreover have **: "modify (\<lambda>g. g - costs\<^sub>e (MINUS e1 e2) e cd st) g = Normal ((), g - costs\<^sub>e (MINUS e1 e2) e cd st)" by simp
      with 20(2)[OF * **] have "\<And>g4' v4 t4. expr e1 e cd st (g-gc) = Normal ((v4, t4), g4') \<Longrightarrow> g4' \<le> g - gc" unfolding gc_def by simp
      moreover obtain v g' where ***: "expr e1 e cd st (g - costs\<^sub>e (MINUS e1 e2) e cd st) = Normal (v, g')" using expr.psimps(12)[OF 20(1)] e_def by (simp split:if_split_asm result.split_asm prod.split_asm)
      with 20(3)[OF * ** ***] have "\<And>v t g' v' t' g''. expr e1 e cd st (g-gc) = Normal ((KValue v, Value t), g') \<Longrightarrow> expr e2 e cd st g' = Normal ((v', t'), g'') \<Longrightarrow> g'' \<le> g'" unfolding gc_def by simp
      ultimately show "g4 \<le> g" using lift_gas[OF lift] `\<not> g \<le> gc` by (simp split:result.split_asm Stackvalue.split_asm Type.split_asm prod.split_asm)
    qed
  qed
next
  case (21 e1 e2 e cd st g)
  define gc where "gc = costs\<^sub>e (LESS e1 e2) e cd st"
  show ?case
  proof (rule allI[THEN allI, OF impI])
    fix g4 xa assume e_def: "expr (LESS e1 e2) e cd st g = Normal (xa, g4)"
    then show "g4 \<le> g"
    proof (cases)
      assume "g \<le> gc"
      with 21(1) e_def show ?thesis using expr.psimps(13) gc_def by simp
    next
      assume "\<not> g \<le> gc"
      then have *: "assert Gas ((<) (costs\<^sub>e (LESS e1 e2) e cd st)) g = Normal ((), g)" using gc_def by simp
      with 21(1) e_def gc_def have lift:"lift expr less e1 e2 e cd st (g - gc) = Normal (xa, g4)" using expr.psimps(13)[OF 21(1)] by simp
      moreover have **: "modify (\<lambda>g. g - costs\<^sub>e (LESS e1 e2) e cd st) g = Normal ((), g - costs\<^sub>e (LESS e1 e2) e cd st)" by simp
      with 21(2)[OF * **] have "\<And>g4' v4 t4. expr e1 e cd st (g-gc) = Normal ((v4, t4), g4') \<Longrightarrow> g4' \<le> g - gc" unfolding gc_def by simp
      moreover obtain v g' where ***: "expr e1 e cd st (g - costs\<^sub>e (LESS e1 e2) e cd st) = Normal (v, g')" using expr.psimps(13)[OF 21(1)] e_def by (simp split:if_split_asm result.split_asm prod.split_asm)
      with 21(3)[OF * ** ***] have "\<And>v t g' v' t' g''. expr e1 e cd st (g-gc) = Normal ((KValue v, Value t), g') \<Longrightarrow> expr e2 e cd st g' = Normal ((v', t'), g'') \<Longrightarrow> g'' \<le> g'" unfolding gc_def by simp
      ultimately show "g4 \<le> g" using lift_gas[OF lift] `\<not> g \<le> gc` by (simp split:result.split_asm Stackvalue.split_asm Type.split_asm prod.split_asm)
    qed
  qed
next
  case (22 e1 e2 e cd st g)
  define gc where "gc = costs\<^sub>e (EQUAL e1 e2) e cd st"
  show ?case
  proof (rule allI[THEN allI, OF impI])
    fix g4 xa assume e_def: "expr (EQUAL e1 e2) e cd st g = Normal (xa, g4)"
    then show "g4 \<le> g"
    proof (cases)
      assume "g \<le> gc"
      with 22(1) e_def show ?thesis using expr.psimps(14) gc_def by simp
    next
      assume "\<not> g \<le> gc"
      then have *: "assert Gas ((<) (costs\<^sub>e (EQUAL e1 e2) e cd st)) g = Normal ((), g)" using gc_def by simp
      with 22(1) e_def gc_def have lift:"lift expr equal e1 e2 e cd st (g - gc) = Normal (xa, g4)" using expr.psimps(14)[OF 22(1)] by simp
      moreover have **: "modify (\<lambda>g. g - costs\<^sub>e (EQUAL e1 e2) e cd st) g = Normal ((), g - costs\<^sub>e (EQUAL e1 e2) e cd st)" by simp
      with 22(2)[OF * **] have "\<And>g4' v4 t4. expr e1 e cd st (g-gc) = Normal ((v4, t4), g4') \<Longrightarrow> g4' \<le> g - gc" unfolding gc_def by simp
      moreover obtain v g' where ***: "expr e1 e cd st (g - costs\<^sub>e (EQUAL e1 e2) e cd st) = Normal (v, g')" using expr.psimps(14)[OF 22(1)] e_def by (simp split:if_split_asm result.split_asm prod.split_asm)
      with 22(3)[OF * ** ***] have "\<And>v t g' v' t' g''. expr e1 e cd st (g-gc) = Normal ((KValue v, Value t), g') \<Longrightarrow> expr e2 e cd st g' = Normal ((v', t'), g'') \<Longrightarrow> g'' \<le> g'" unfolding gc_def by simp
      ultimately show "g4 \<le> g" using lift_gas[OF lift] `\<not> g \<le> gc` by (simp split:result.split_asm Stackvalue.split_asm Type.split_asm prod.split_asm)
    qed
  qed
next
  case (23 e1 e2 e cd st g)
  define gc where "gc = costs\<^sub>e (AND e1 e2) e cd st"
  show ?case
  proof (rule allI[THEN allI, OF impI])
    fix g4 xa assume e_def: "expr (AND e1 e2) e cd st g = Normal (xa, g4)"
    then show "g4 \<le> g"
    proof (cases)
      assume "g \<le> gc"
      with 23(1) e_def show ?thesis using expr.psimps(15) gc_def by simp
    next
      assume "\<not> g \<le> gc"
      then have *: "assert Gas ((<) (costs\<^sub>e (AND e1 e2) e cd st)) g = Normal ((), g)" using gc_def by simp
      with 23(1) e_def gc_def have lift:"lift expr vtand e1 e2 e cd st (g - gc) = Normal (xa, g4)" using expr.psimps(15)[OF 23(1)] by simp
      moreover have **: "modify (\<lambda>g. g - costs\<^sub>e (AND e1 e2) e cd st) g = Normal ((), g - costs\<^sub>e (AND e1 e2) e cd st)" by simp
      with 23(2)[OF * **] have "\<And>g4' v4 t4. expr e1 e cd st (g-gc) = Normal ((v4, t4), g4') \<Longrightarrow> g4' \<le> g - gc" unfolding gc_def by simp
      moreover obtain v g' where ***: "expr e1 e cd st (g - costs\<^sub>e (AND e1 e2) e cd st) = Normal (v, g')" using expr.psimps(15)[OF 23(1)] e_def by (simp split:if_split_asm result.split_asm prod.split_asm)
      with 23(3)[OF * ** ***] have "\<And>v t g' v' t' g''. expr e1 e cd st (g-gc) = Normal ((KValue v, Value t), g') \<Longrightarrow> expr e2 e cd st g' = Normal ((v', t'), g'') \<Longrightarrow> g'' \<le> g'" unfolding gc_def by simp
      ultimately show "g4 \<le> g" using lift_gas[OF lift] `\<not> g \<le> gc` by (simp split:result.split_asm Stackvalue.split_asm Type.split_asm prod.split_asm)
    qed
  qed
next
  case (24 e1 e2 e cd st g)
  define gc where "gc = costs\<^sub>e (OR e1 e2) e cd st"
  show ?case
  proof (rule allI[THEN allI, OF impI])
    fix g4 xa assume e_def: "expr (OR e1 e2) e cd st g = Normal (xa, g4)"
    then show "g4 \<le> g"
    proof (cases)
      assume "g \<le> gc"
      with 24(1) e_def show ?thesis using expr.psimps(16) gc_def by simp
    next
      assume "\<not> g \<le> gc"
      then have *: "assert Gas ((<) (costs\<^sub>e (OR e1 e2) e cd st)) g = Normal ((), g)" using gc_def by simp
      with 24(1) e_def gc_def have lift:"lift expr vtor e1 e2 e cd st (g - gc) = Normal (xa, g4)" using expr.psimps(16)[OF 24(1)] by simp
      moreover have **: "modify (\<lambda>g. g - costs\<^sub>e (OR e1 e2) e cd st) g = Normal ((), g - costs\<^sub>e (OR e1 e2) e cd st)" by simp
      with 24(2)[OF * **] have "\<And>g4' v4 t4. expr e1 e cd st (g-gc) = Normal ((v4, t4), g4') \<Longrightarrow> g4' \<le> g - gc" unfolding gc_def by simp
      moreover obtain v g' where ***: "expr e1 e cd st (g - costs\<^sub>e (OR e1 e2) e cd st) = Normal (v, g')" using expr.psimps(16)[OF 24(1)] e_def by (simp split:if_split_asm result.split_asm prod.split_asm)
      with 24(3)[OF * ** ***] have "\<And>v t g' v' t' g''. expr e1 e cd st (g-gc) = Normal ((KValue v, Value t), g') \<Longrightarrow> expr e2 e cd st g' = Normal ((v', t'), g'') \<Longrightarrow> g'' \<le> g'" unfolding gc_def by simp
      ultimately show "g4 \<le> g" using lift_gas[OF lift] `\<not> g \<le> gc` by (simp split:result.split_asm Stackvalue.split_asm Type.split_asm prod.split_asm)
    qed
  qed
next
  case (25 i e cd st g)
  define gc where "gc = costs\<^sub>e (LVAL i) e cd st"
  show ?case
  proof (rule allI[THEN allI, OF impI])
    fix g4 xa xaa assume e_def: "expr (LVAL i) e cd st g = Normal (xa, g4)"
    then show "g4 \<le> g"
    proof (cases)
      assume "g \<le> gc"
      with 25(1) e_def show ?thesis using expr.psimps(17) gc_def by simp
    next
      assume "\<not> g \<le> gc"
      then have *: "assert Gas ((<) (costs\<^sub>e (LVAL i) e cd st)) g = Normal ((), g)" using gc_def by simp
      then have "expr (LVAL i) e cd st g = rexp i e cd st (g - gc)" using expr.psimps(17)[OF 25(1)] gc_def by simp
      then have "rexp i e cd st (g - gc) = Normal (xa, g4)" using e_def by simp
      moreover have **: "modify (\<lambda>g. g - costs\<^sub>e (LVAL i) e cd st) g = Normal ((), g - costs\<^sub>e (LVAL i) e cd st)" by simp
      ultimately show ?thesis using 25(2)[OF * **] unfolding gc_def by (simp split:result.split_asm Stackvalue.split_asm Type.split_asm prod.split_asm)
    qed
  qed
next
  case (26 i xe e cd st g)
  define gc where "gc = costs\<^sub>e (CALL i xe) e cd st"
  show ?case
  proof (rule allI[THEN allI, OF impI])
    fix g4' v4 assume a1: "expr (CALL i xe) e cd st g = Normal (v4, g4')"
    then have *: "assert Gas ((<) (costs\<^sub>e (CALL i xe) e cd st)) g = Normal ((), g)" using gc_def using expr.psimps(18)[OF 26(1)] by (simp split:if_split_asm)
    have **: "modify (\<lambda>g. g - costs\<^sub>e (CALL i xe) e cd st) g = Normal ((), g - gc)" unfolding gc_def by simp
    show "g4' \<le> g"
    proof (cases)
      assume "g \<le> gc"
      with 26(1) gc_def a1 show ?thesis using expr.psimps(18) by simp
    next
      assume gcost: "\<not> g \<le> gc"
      then show ?thesis
      proof (cases v4)
        case (Pair l4 t4)
        then show ?thesis
        proof (cases "ep $$ contract e")
          case None
          with 26(1) a1 gc_def gcost show ?thesis using expr.psimps(18) by simp
        next
          case (Some a)
          then show ?thesis
          proof (cases a)
            case p2: (fields ct x0 x1)
            then have 1: "option Err (\<lambda>_. ep $$ contract e) (g - gc) = Normal ((ct, x0, x1), (g - gc))" using Some by simp
            then show ?thesis
            proof (cases "fmlookup ct i")
              case None
              with 26(1) a1 gc_def gcost Some p2 show ?thesis using expr.psimps(18) by simp
            next
              case s1: (Some a)
              then show ?thesis
              proof (cases a)
                case (Function x1)
                then show ?thesis
                proof (cases x1)
                  case p1: (fields fp ext x)
                  then show ?thesis
                  proof (cases ext)
                    case True
                    with 26(1) a1 gc_def gcost Some p2 s1 Function p1 show ?thesis using expr.psimps(18)[of i xe e cd st] by (auto split:unit.split_asm)
                  next
                    case False
                    then have 2: "(case ct $$ i of None \<Rightarrow> throw Err | Some (Function (fp, True, xa)) \<Rightarrow> throw Err | Some (Function (fp, False, xa)) \<Rightarrow> return (fp, xa) | Some _ \<Rightarrow> throw Err) (g - gc) = Normal ((fp, x), (g - gc))" using s1 Function p1 by simp
                    define e' where "e' = ffold (init ct) (emptyEnv (address e) (contract e) (sender e) (svalue e)) (fmdom ct)"
                    then show ?thesis
                    proof (cases "load False fp xe e' emptyStore emptyStore (memory st) e cd st (g - gc)")
                      case s4: (n a g')
                      then show ?thesis
                      proof (cases a)
                        case f2: (fields e\<^sub>l cd\<^sub>l k\<^sub>l m\<^sub>l)
                        then show ?thesis
                        proof (cases "expr x e\<^sub>l cd\<^sub>l (st\<lparr>stack:=k\<^sub>l, memory:=m\<^sub>l\<rparr>) g'")
                          case n2: (n a g'')
                          then show ?thesis
                          proof (cases a)
                            case p3: (Pair sv tp)
                            with 26(1) a1 gc_def gcost Some p2 s1 Function p1 e'_def s4 f2 n2 False
                            have "expr (CALL i xe) e cd st g = Normal ((sv, tp), g'')"
                              using expr.psimps(18)[OF 26(1)] by simp
                            with a1 have "g4' \<le> g''" by simp
                            also from 26(3)[OF * ** 1 _ 2 _ _ s4] e'_def f2 n2 p3 gcost gc_def
                              have "\<dots> \<le> g'" by auto
                            also from 26(2)[OF * ** 1 _ 2 _] False e'_def f2 s4
                              have "\<dots> \<le> g - gc" unfolding ffold_init_def gc_def by blast
                            finally show ?thesis by simp
                          qed
                        next
                          case (e _)
                          with 26(1) a1 gc_def gcost Some p2 s1 Function p1 e'_def s4 f2 False show ?thesis using expr.psimps(18)[of i xe e cd st] by (auto simp add:Let_def split:unit.split_asm)
                        qed
                      qed
                    next
                      case (e _)
                      with 26(1) a1 gc_def gcost Some p2 s1 Function p1 e'_def False show ?thesis using expr.psimps(18)[of i xe e cd st] by (auto split:unit.split_asm)
                    qed
                  qed
                qed
              next
                case (Method _)
                with 26(1) a1 gc_def gcost Some p2 s1 show ?thesis using expr.psimps(18) by simp
              next
                case (Var _)
                with 26(1) a1 gc_def gcost Some p2 s1 show ?thesis using expr.psimps(18) by simp
              qed
            qed
          qed
        qed
      qed
    qed
  qed
next
  case (27 ad i xe e cd st g)
  define gc where "gc = costs\<^sub>e (ECALL ad i xe) e cd st"
  show ?case
  proof (rule allI[THEN allI, OF impI])
    fix g4' v4 assume a1: "expr (ECALL ad i xe) e cd st g = Normal (v4, g4')"
    show "g4' \<le> g"
    proof (cases v4)
      case (Pair l4 t4)
      then show ?thesis
      proof (cases)
        assume "g \<le> gc"
        with gc_def a1 show ?thesis using expr.psimps(19)[OF 27(1)] by simp
      next
        assume gcost: "\<not> g \<le> gc"
        then have *: "assert Gas ((<) (costs\<^sub>e (ECALL ad i xe) e cd st)) g = Normal ((), g)" using gc_def using expr.psimps(19)[OF 27(1)] by (simp split:if_split_asm)
        have **: "modify (\<lambda>g. g - costs\<^sub>e (ECALL ad i xe) e cd st) g = Normal ((), g - gc)" unfolding gc_def by simp
        then show ?thesis
        proof (cases "expr ad e cd st (g-gc)")
          case (n a0 g')
          then show ?thesis
          proof (cases a0)
            case p0: (Pair a b)
            then show ?thesis
            proof (cases a)
              case (KValue adv)
              then show ?thesis
              proof (cases b)
                case (Value x1)
                then show ?thesis
                proof (cases x1)
                  case (TSInt x1)
                  with a1 gc_def gcost n p0 KValue Value show ?thesis using expr.psimps(19)[OF 27(1)] by simp
                next
                  case (TUInt x2)
                  with a1 gc_def gcost n p0 KValue Value show ?thesis using expr.psimps(19)[OF 27(1)] by simp
                next
                  case TBool
                  with a1 gc_def gcost n p0 KValue Value show ?thesis using expr.psimps(19)[OF 27(1)] by simp
                next
                  case TAddr
                  then have 1: "(case a0 of (KValue adv, Value TAddr) \<Rightarrow> return adv | (KValue adv, Value _) \<Rightarrow> throw Err | (KValue adv, _) \<Rightarrow> throw Err | (_, b) \<Rightarrow> throw Err) g' = Normal (adv, g')" using p0 KValue Value by simp
                  then show ?thesis
                  proof (cases "adv = address e")
                    case True
                    with a1 gc_def gcost n p0 KValue Value TAddr show ?thesis using expr.psimps(19)[OF 27(1)] by simp
                  next
                    case False
                    then have 2: "assert Err (\<lambda>_. adv \<noteq> address e) g' = Normal ((), g')" by simp
                    then show ?thesis
                    proof (cases "type (accounts st adv)")
                      case None
                      with a1 gc_def gcost n p0 KValue Value TAddr False show ?thesis using expr.psimps(19)[OF 27(1)] by simp
                    next
                      case (Some x2)
                      then show ?thesis
                      proof (cases x2)
                        case EOA
                        with a1 gc_def gcost n p0 KValue Value TAddr False Some show ?thesis using expr.psimps(19)[OF 27(1)] by simp
                      next
                        case c: (Contract c)
                        then have 3: "(case type (accounts st adv) of Some (Contract c) \<Rightarrow> return c | _ \<Rightarrow> throw Err) g' = Normal (c, g')" using Some by simp
                        then show ?thesis
                        proof (cases "ep $$ c")
                          case None
                          with a1 gc_def gcost n p0 KValue Value TAddr False Some c show ?thesis using expr.psimps(19)[OF 27(1)] by simp
                        next
                          case s0: (Some a)
                          then show ?thesis
                          proof (cases a)
                            case p1: (fields ct xa xb)
                            then have 4: "option Err (\<lambda>_. ep $$ c) g' = Normal ((ct, xa, xb), g')" using Some s0 by simp
                            then show ?thesis
                            proof (cases "ct $$ i")
                              case None
                              with a1 gc_def gcost n p0 KValue Value TAddr Some p1 False c s0 show ?thesis using expr.psimps(19)[OF 27(1)] by simp
                            next
                              case s1: (Some a)
                              then show ?thesis
                              proof (cases a)
                                case (Function x1)
                                then show ?thesis
                                proof (cases x1)
                                  case p2: (fields fp ext x)
                                  then show ?thesis
                                  proof (cases ext)
                                    case True
                                    then have 5: "(case ct $$ i of None \<Rightarrow> throw Err | Some (Function (fp, True, xa)) \<Rightarrow> return (fp, xa) | Some (Function (fp, False, xa)) \<Rightarrow> throw Err | Some _ \<Rightarrow> throw Err) g' = Normal ((fp, x), g')" using s1 Function p2 by simp
                                    define e' where "e' = ffold (init ct) (emptyEnv adv c (address e) (ShowL\<^sub>n\<^sub>a\<^sub>t 0)) (fmdom ct)"
                                    then show ?thesis
                                    proof (cases "load True fp xe e' emptyStore emptyStore emptyStore e cd st g'")
                                      case n1: (n a g'')
                                      then show ?thesis
                                      proof (cases a)
                                        case f2: (fields e\<^sub>l cd\<^sub>l k\<^sub>l m\<^sub>l)
                                        show ?thesis
                                        proof (cases "expr x e\<^sub>l cd\<^sub>l (st\<lparr>stack:=k\<^sub>l, memory:=m\<^sub>l\<rparr>) g''")
                                          case n2: (n a g''')
                                          then show ?thesis
                                          proof (cases a)
                                            case p3: (Pair sv tp)
                                            with a1 gc_def gcost n p2 KValue Value TAddr Some p1 s1 Function p0 e'_def n1 f2 n2 True False s0 c
                                            have "expr (ECALL ad i xe) e cd st g = Normal ((sv, tp), g''')"
                                                using expr.psimps(19)[OF 27(1)] by auto
                                            with a1 have "g4' \<le> g'''" by auto
                                            also from 27(4)[OF * ** n 1 2 3 4 _ 5 _ _ n1] p3 f2 e'_def n2
                                              have "\<dots> \<le> g''" by simp
                                            also from 27(3)[OF * ** n 1 2 3 4 _ 5, of "(xa, xb)" fp x e'] e'_def n1 f2
                                              have "\<dots> \<le> g'" by auto
                                            also from 27(2)[OF * **] n
                                              have "\<dots> \<le> g" by simp
                                            finally show ?thesis by simp
                                          qed
                                        next
                                          case (e _)
                                          with a1 gc_def gcost n p0 KValue Value TAddr False Some p1 s1 Function p2 e'_def n1 f2 True s0 c show ?thesis using expr.psimps(19)[OF 27(1)] by simp
                                        qed
                                      qed
                                    next
                                      case (e _)
                                      with a1 gc_def gcost n p0 KValue Value TAddr False Some p1 s1 Function p2 e'_def True s0 c show ?thesis using expr.psimps(19)[OF 27(1)] by simp
                                    qed
                                  next
                                    case f: False
                                    with a1 gc_def gcost n p0 KValue Value TAddr Some p1 s1 Function p2 False s0 c show ?thesis using expr.psimps(19)[OF 27(1)] by simp
                                  qed
                                qed
                              next
                                case (Method _)
                                with a1 gc_def gcost n p0 KValue Value TAddr Some p1 s1 False s0 c show ?thesis using expr.psimps(19)[OF 27(1)] by simp
                              next
                                case (Var _)
                                with a1 gc_def gcost n p0 KValue Value TAddr Some p1 s1 False s0 c show ?thesis using expr.psimps(19)[OF 27(1)] by simp
                              qed
                            qed
                          qed
                        qed
                      qed
                    qed
                  qed
                qed
              next
                case (Calldata _)
                with a1 gc_def gcost n p0 KValue show ?thesis using expr.psimps(19)[OF 27(1)] by simp
              next
                case (Memory _)
                with a1 gc_def gcost n p0 KValue show ?thesis using expr.psimps(19)[OF 27(1)] by simp
              next
                case (Storage _)
                with a1 gc_def gcost n p0 KValue show ?thesis using expr.psimps(19)[OF 27(1)] by simp
              qed
            next
              case (KCDptr _)
              with a1 gc_def gcost n p0 show ?thesis using expr.psimps(19)[OF 27(1)] by simp
            next
              case (KMemptr _)
              with a1 gc_def gcost n p0 show ?thesis using expr.psimps(19)[OF 27(1)] by simp
            next
              case (KStoptr _)
              with a1 gc_def gcost n p0 show ?thesis using expr.psimps(19)[OF 27(1)] by simp
            qed
          qed
        next
          case (e _)
          with a1 gc_def gcost show ?thesis using expr.psimps(19)[OF 27(1)] by simp
        qed
      qed
    qed
  qed
next
  case (28 cp i\<^sub>p t\<^sub>p pl e el e\<^sub>v' cd' sck' mem' e\<^sub>v cd st g)
  then show ?case
  proof (cases "expr e e\<^sub>v cd st g")
    case (n a g'')
    then show ?thesis
    proof (cases a)
      case (Pair v t)
      then show ?thesis
      proof (cases "decl i\<^sub>p t\<^sub>p (Some (v,t)) cp cd (memory st) (storage st) (cd', mem',  sck', e\<^sub>v')")
        case None
        with 28(1) n Pair show ?thesis using load.psimps(1) by simp
      next
        case (Some a)
        show ?thesis
        proof (cases a)
          case (fields cd'' m'' k'' e\<^sub>v'')
          then have 1: "(case decl i\<^sub>p t\<^sub>p (Some (v, t)) cp cd (memory st) (storage st) (cd', mem', sck', e\<^sub>v') of None \<Rightarrow> throw Err | Some (c, m, k, e) \<Rightarrow> return (c, m, k, e)) g'' = Normal ((cd'',m'',k'',e\<^sub>v''), g'')" using Some by simp
          show ?thesis
          proof ((rule allI)+,(rule impI))
            fix ev cda k m g' assume load_def: "load cp ((i\<^sub>p, t\<^sub>p) # pl) (e # el) e\<^sub>v' cd' sck' mem' e\<^sub>v cd st g = Normal ((ev, cda, k, m), g')"
            with n Pair Some fields have "load cp ((i\<^sub>p, t\<^sub>p) # pl) (e # el) e\<^sub>v' cd' sck' mem' e\<^sub>v cd st g = load cp pl el e\<^sub>v'' cd'' k'' m'' e\<^sub>v cd st g''" using load.psimps(1)[OF 28(1)] by simp
            with load_def have "load cp pl el e\<^sub>v'' cd'' k'' m'' e\<^sub>v cd st g'' = Normal ((ev, cda, k, m), g')" by simp
            with Pair fields have "g' \<le> g'' \<and> address ev = address e\<^sub>v'' \<and> sender ev = sender e\<^sub>v'' \<and> svalue ev = svalue e\<^sub>v''" using 28(3)[OF n Pair 1, of cd'' _ m''] by simp
            moreover from n have "g'' \<le> g" using 28(2) by simp
            moreover from Some fields have "address e\<^sub>v'' =  address e\<^sub>v' \<and> sender e\<^sub>v'' = sender e\<^sub>v' \<and> svalue e\<^sub>v'' = svalue e\<^sub>v'" using decl_env by auto
            ultimately show "g' \<le> g \<and> address ev = address e\<^sub>v' \<and> sender ev = sender e\<^sub>v' \<and> svalue ev = svalue e\<^sub>v'" by auto
          qed
        qed
      qed
    qed
  next
    case (e _)
    with 28(1) show ?thesis using load.psimps(1) by simp
  qed
next
  case 29
  then show ?case using load.psimps(2) by auto
next
  case 30
  then show ?case using load.psimps(3) by auto
next
  case 31
  then show ?case using load.psimps(4) by auto
next
  case (32 i e cd st g)
  show ?case
  proof (rule allI[THEN allI, OF impI])
    fix xa xaa assume "rexp (L.Id i) e cd st g = Normal (xa, xaa)"
    then show "xaa \<le> g" using 32(1) rexp.psimps(1) by (simp split: option.split_asm Denvalue.split_asm Stackvalue.split_asm prod.split_asm Type.split_asm STypes.split_asm)
  qed
next
  case (33 i r e cd st g)
  show ?case
  proof (rule allI[THEN allI,OF impI])
    fix xa xaa assume rexp_def: "rexp (Ref i r) e cd st g = Normal (xa, xaa)"
    show "xaa \<le> g"
    proof (cases "fmlookup (denvalue e) i")
      case None
      with 33(1) show ?thesis using rexp.psimps rexp_def by simp
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
            with 33(1) Some Pair Stackloc show ?thesis using rexp.psimps(2) rexp_def by simp
          next
            case s1: (Some a)
            then show ?thesis
            proof (cases a)
              case (KValue x1)
              with 33(1) Some Pair Stackloc s1 show ?thesis using rexp.psimps(2) rexp_def by simp
            next
              case (KCDptr l')
              with 33 Some Pair Stackloc s1 show ?thesis using rexp.psimps(2)[of i r e cd st] rexp_def by (simp split: option.split_asm Memoryvalue.split_asm MTypes.split_asm prod.split_asm Type.split_asm StateMonad.result.split_asm)
            next
              case (KMemptr x3)
              with 33 Some Pair Stackloc s1 show ?thesis using rexp.psimps(2)[of i r e cd st] rexp_def by (simp split: option.split_asm Memoryvalue.split_asm MTypes.split_asm prod.split_asm Type.split_asm StateMonad.result.split_asm)
            next
              case (KStoptr x4)
              with 33 Some Pair Stackloc s1 show ?thesis using rexp.psimps(2)[of i r e cd st] rexp_def by (simp split: option.split_asm STypes.split_asm prod.split_asm Type.split_asm StateMonad.result.split_asm)
            qed
          qed
        next
          case (Storeloc x2)
          with 33 Some Pair show ?thesis using rexp.psimps rexp_def by (simp split: option.split_asm STypes.split_asm prod.split_asm Type.split_asm  StateMonad.result.split_asm)
        qed
      qed
    qed
  qed
next
  case (34 e cd st g)
  then show ?case using expr.psimps(20) by (simp split:nat.split)
qed

text \<open>Now we can define the termination function\<close>

fun mgas
  where "mgas (Inr (Inr (Inr l))) = snd (snd (snd (snd l)))" (*rexp*)
        | "mgas (Inr (Inr (Inl l))) = snd (snd (snd (snd (snd (snd (snd (snd (snd (snd l)))))))))" (*load*)
        | "mgas (Inr (Inl l)) = snd (snd (snd (snd l)))" (*expr*)
        | "mgas (Inl (Inr l)) = snd (snd (snd (snd (snd (snd l)))))"  (*ssel*)
        | "mgas (Inl (Inl l)) = snd (snd (snd (snd (snd (snd (snd l))))))" (*msel*)

fun msize
  where "msize (Inr (Inr (Inr l))) = size (fst l)"
        | "msize (Inr (Inr (Inl l))) = size_list size (fst (snd (snd l)))"
        | "msize (Inr (Inl l)) = size (fst l)"
        | "msize (Inl (Inr l)) = size_list size (fst (snd (snd l)))"
        | "msize (Inl (Inl l)) = size_list size (fst (snd (snd (snd l))))"

method msel_ssel_expr_load_rexp_dom =
  match premises in e: "expr _ _ _ _ _ = Normal (_,_)" and d[thin]: "msel_ssel_expr_load_rexp_dom (Inr (Inl _))" \<Rightarrow> \<open>insert msel_ssel_expr_load_rexp_dom_gas(3)[OF d e]\<close> |
  match premises in l: "load _ _ _ _ _ _ _ _ _ _ _ = Normal (_,_)" and d[thin]: "msel_ssel_expr_load_rexp_dom (Inr (Inr (Inl _)))" \<Rightarrow> \<open>insert msel_ssel_expr_load_rexp_dom_gas(4)[OF d l, THEN conjunct1]\<close>

method costs =
  match premises in "costs\<^sub>e (CALL i xe) e cd st < _" for i xe and e::Environment and cd::CalldataT and st::State \<Rightarrow> \<open>insert call_not_zero[of (unchecked) i xe e cd st]\<close> |
  match premises in "costs\<^sub>e (ECALL ad i xe) e cd st < _" for ad i xe and e::Environment and cd::CalldataT and st::State \<Rightarrow> \<open>insert ecall_not_zero[of (unchecked) ad i xe e cd st]\<close>

termination msel
  apply (relation "measures [mgas, msize]")
  apply (auto split:Member.split_asm prod.split_asm bool.split_asm if_split_asm Stackvalue.split_asm option.split_asm Type.split_asm Types.split_asm Memoryvalue.split_asm atype.split_asm)
  apply (msel_ssel_expr_load_rexp_dom+, costs?, arith)+
  done

subsection \<open>Gas Reduction\<close>

text \<open>
  The following corollary is a generalization of @{thm [source] msel_ssel_expr_load_rexp_dom_gas}.
  We first prove that the function is defined for all input values and then obtain the final result as a corollary.
\<close>

lemma msel_ssel_expr_load_rexp_dom:
    "msel_ssel_expr_load_rexp_dom (Inl (Inl (c1, t1, l1, xe1, ev1, cd1, st1, g1)))"
    "msel_ssel_expr_load_rexp_dom (Inl (Inr (t2, l2, xe2, ev2, cd2, st2, g2)))"
    "msel_ssel_expr_load_rexp_dom (Inr (Inl (e4, ev4, cd4, st4, g4)))"
    "msel_ssel_expr_load_rexp_dom (Inr (Inr (Inl (lcp, lis, lxs, lev0, lcd0, lk, lm, lev, lcd, lst, lg))))"
    "msel_ssel_expr_load_rexp_dom (Inr (Inr (Inr (l3, ev3, cd3, st3, g3))))"
by (induct rule: msel_ssel_expr_load_rexp.induct
[where ?P1.0="\<lambda>c1 t1 l1 xe1 ev1 cd1 st1 g1. msel_ssel_expr_load_rexp_dom (Inl (Inl (c1, t1, l1, xe1, ev1, cd1, st1, g1)))"
   and ?P2.0="\<lambda>t2 l2 xe2 ev2 cd2 st2 g2. msel_ssel_expr_load_rexp_dom (Inl (Inr (t2, l2, xe2, ev2, cd2, st2, g2)))"
   and ?P3.0="\<lambda>e4 ev4 cd4 st4 g4. msel_ssel_expr_load_rexp_dom (Inr (Inl (e4, ev4, cd4, st4, g4)))"
   and ?P4.0="\<lambda>lcp lis lxs lev0 lcd0 lk lm lev lcd lst lg. msel_ssel_expr_load_rexp_dom (Inr (Inr (Inl (lcp, lis, lxs, lev0, lcd0, lk, lm, lev, lcd, lst, lg))))"
   and ?P5.0="\<lambda>l3 ev3 cd3 st3 g3. msel_ssel_expr_load_rexp_dom (Inr (Inr (Inr (l3, ev3, cd3, st3, g3))))"
], simp_all add: msel_ssel_expr_load_rexp.domintros)

lemmas msel_ssel_expr_load_rexp_gas =
  msel_ssel_expr_load_rexp_dom_gas(1)[OF msel_ssel_expr_load_rexp_dom(1)]
  msel_ssel_expr_load_rexp_dom_gas(2)[OF msel_ssel_expr_load_rexp_dom(2)]
  msel_ssel_expr_load_rexp_dom_gas(3)[OF msel_ssel_expr_load_rexp_dom(3)]
  msel_ssel_expr_load_rexp_dom_gas(4)[OF msel_ssel_expr_load_rexp_dom(4)]
  msel_ssel_expr_load_rexp_dom_gas(5)[OF msel_ssel_expr_load_rexp_dom(5)]

lemma expr_sender:
  assumes "expr SENDER e cd st g = Normal ((KValue adv, Value TAddr), g')"
  shows "adv = sender e" using assms by (simp split:if_split_asm)

declare expr.simps[simp del, solidity_symbex add]
declare load.simps[simp del, solidity_symbex add]
declare ssel.simps[simp del, solidity_symbex add]
declare msel.simps[simp del, solidity_symbex add]
declare rexp.simps[simp del, solidity_symbex add]

end

end
