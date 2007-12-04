(*  Title:      JinjaThreads/J/Expr.thy
    Author:     Tobias Nipkow, Andreas Lochbihler

    Based on the Jinja Theory J/Expr by Tobias Nipkow
*)

header {* \isaheader{Expressions} *}

theory Expr imports "../Common/Exceptions" begin

datatype bop = Eq | Add     -- "names of binary operations"

datatype 'a exp
  = new cname      -- "class instance creation"
  | newArray ty "'a exp" ("newA _\<lfloor>_\<rceil>" [99,0] 90)    -- "array instance creation: type, size in outermost dimension"
  | Cast ty "('a exp)"      -- "type cast"
  | Val val      -- "value"
  | BinOp "('a exp)" bop "('a exp)"     ("_ \<guillemotleft>_\<guillemotright> _" [80,0,81] 80)      -- "binary operation"
  | Var 'a                                               -- "local variable (incl. parameter)"
  | LAss 'a "('a exp)"            ("_:=_" [90,90]90)                    -- "local assignment"
  | AAcc "'a exp" "'a exp"            ("_\<lfloor>_\<rceil>" [99,0] 90)          -- "array cell read"
  | AAss "'a exp" "'a exp" "'a exp" ("_\<lfloor>_\<rceil> := _" [10,99,90] 90)    -- "array cell assignment"
  | FAcc "('a exp)" vname cname     ("_\<bullet>_{_}" [10,90,99]90)       -- "field access"
  | FAss "('a exp)" vname cname "('a exp)"     ("_\<bullet>_{_} := _" [10,90,99,90]90)      -- "field assignment"
  | Call "('a exp)" mname "('a exp list)"     ("_\<bullet>_'(_')" [90,99,0] 90)            -- "method call"
  | Block 'a ty "('a exp)"     ("'{_:_; _}")
  | Synchronized "'a exp" "'a exp" ("sync'(_') _" [99,90] 90)
  | Seq "('a exp)" "('a exp)"     ("_;;/ _"             [61,60]60)
  | Cond "('a exp)" "('a exp)" "('a exp)"     ("if '(_') _/ else _" [80,79,79]70)
  | While "('a exp)" "('a exp)"     ("while '(_') _"     [80,79]70)
  | throw "('a exp)"
  | TryCatch "('a exp)" cname 'a "('a exp)"     ("try _/ catch'(_ _') _"  [0,99,80,79] 70)

types
  expr = "vname exp"            -- "Jinja expression"
  J_mb = "vname list \<times> expr"    -- "Jinja method body: parameter names and expression"
  J_prog = "J_mb prog"          -- "Jinja program"

text{*The semantics of binary operators: *}

consts
  binop :: "bop \<times> val \<times> val \<Rightarrow> val option"
recdef binop "{}"
  "binop(Eq,v\<^isub>1,v\<^isub>2) = Some(Bool (v\<^isub>1 = v\<^isub>2))"
  "binop(Add,Intg i\<^isub>1,Intg i\<^isub>2) = Some(Intg(i\<^isub>1+i\<^isub>2))"
  "binop(bop,v\<^isub>1,v\<^isub>2) = None"

lemma [simp]:
  "(binop(Add,v\<^isub>1,v\<^isub>2) = Some v) = (\<exists>i\<^isub>1 i\<^isub>2. v\<^isub>1 = Intg i\<^isub>1 \<and> v\<^isub>2 = Intg i\<^isub>2 \<and> v = Intg(i\<^isub>1+i\<^isub>2))"
(*<*)
apply(cases v\<^isub>1)
apply auto
apply(cases v\<^isub>2)
apply auto
done
(*>*)


subsection "Syntactic sugar"

syntax
  InitBlock:: "vname \<Rightarrow> ty \<Rightarrow> 'a exp \<Rightarrow> 'a exp \<Rightarrow> 'a exp"   ("(1'{_:_ := _;/ _})")
translations
  "InitBlock V T e1 e2" => "{V:T; V := e1;; e2}"

syntax
 unit :: "'a exp"
 null :: "'a exp"
 addr :: "addr \<Rightarrow> 'a exp"
 true :: "'a exp"
 false :: "'a exp"
translations
 "unit" == "Val Unit"
 "null" == "Val Null"
 "addr a" == "Val(Addr a)"
 "true" == "Val(Bool True)"
 "false" == "Val(Bool False)"

syntax
  Throw :: "addr \<Rightarrow> 'a exp"
  THROW :: "cname \<Rightarrow> 'a exp"
translations
  "Throw a" == "throw(Val(Addr a))"
  "THROW xc" == "Throw(addr_of_sys_xcpt xc)"

syntax
  lock :: "addr \<Rightarrow> 'a exp" ( "locked'(_')" 100 )
translations
  "locked(a)" == "unit;;addr a"

subsection{*Free Variables*}

consts
  fv  :: "expr      \<Rightarrow> vname set"
  fvs :: "expr list \<Rightarrow> vname set"
primrec
  "fv(new C) = {}"
  "fv(newA T\<lfloor>e\<rceil>) = fv e"
  "fv(Cast C e) = fv e"
  "fv(Val v) = {}"
  "fv(e\<^isub>1 \<guillemotleft>bop\<guillemotright> e\<^isub>2) = fv e\<^isub>1 \<union> fv e\<^isub>2"
  "fv(Var V) = {V}"
  "fv(a\<lfloor>i\<rceil>) = fv a \<union> fv i"
  "fv(a\<lfloor>i\<rceil> := e) = fv a \<union> fv i \<union> fv e"
  "fv(LAss V e) = {V} \<union> fv e"
  "fv(e\<bullet>F{D}) = fv e"
  "fv(e\<^isub>1\<bullet>F{D}:=e\<^isub>2) = fv e\<^isub>1 \<union> fv e\<^isub>2"
  "fv(e\<bullet>M(es)) = fv e \<union> fvs es"
  "fv({V:T; e}) = fv e - {V}"
  "fv(sync(h) e) = fv h \<union> fv e"
  "fv(e\<^isub>1;;e\<^isub>2) = fv e\<^isub>1 \<union> fv e\<^isub>2"
  "fv(if (b) e\<^isub>1 else e\<^isub>2) = fv b \<union> fv e\<^isub>1 \<union> fv e\<^isub>2"
  "fv(while (b) e) = fv b \<union> fv e"
  "fv(throw e) = fv e"
  "fv(try e\<^isub>1 catch(C V) e\<^isub>2) = fv e\<^isub>1 \<union> (fv e\<^isub>2 - {V})"

  "fvs([]) = {}"
  "fvs(e#es) = fv e \<union> fvs es"

lemma [simp]: "fvs(es\<^isub>1 @ es\<^isub>2) = fvs es\<^isub>1 \<union> fvs es\<^isub>2"
(*<*)by (induct es\<^isub>1 type:list) auto(*>*)

lemma [simp]: "fvs(map Val vs) = {}"
(*<*)by (induct vs) auto(*>*)


subsection{*Locks and addresses*}

constdefs
  lock_granted :: "expr \<Rightarrow> bool"
  "lock_granted o' \<equiv> \<exists>a. o' = locked(a)"

lemma [simp]:
  "lock_granted(locked(a))"
by(simp add: lock_granted_def)

consts
  contains_addr :: "expr \<Rightarrow> bool"
  contains_addrs :: "expr list \<Rightarrow> bool"
primrec
"contains_addr (new C) = False"
"contains_addr (newA T\<lfloor>i\<rceil>) = contains_addr i"
"contains_addr (Cast T e) = contains_addr e"
"contains_addr (Val v) = (\<exists>a. v = Addr a)"
"contains_addr (Var v) = False"
"contains_addr (e \<guillemotleft>bop\<guillemotright> e') = (contains_addr e \<or> contains_addr e')"
"contains_addr (V := e) = contains_addr e"
"contains_addr (a\<lfloor>i\<rceil>) = (contains_addr a \<or> contains_addr i)"
"contains_addr (a\<lfloor>i\<rceil> := e) = (contains_addr a \<or> contains_addr i \<or> contains_addr e)"
"contains_addr (e\<bullet>F{E}) = contains_addr e"
"contains_addr (e\<bullet>F{E} := e') = (contains_addr e \<or> contains_addr e')"
"contains_addr (e\<bullet>m(ps)) = (contains_addr e \<or> contains_addrs ps)"
"contains_addr ({V : T; e}) = contains_addr e"
"contains_addr (sync(o') e) = (contains_addr e \<or> contains_addr o')"
"contains_addr (e;;e') = (contains_addr e \<or> contains_addr e')"
"contains_addr (if (b) e else e') = (contains_addr b \<or> contains_addr e \<or> contains_addr e')"
"contains_addr (while (b) e) = (contains_addr b \<or> contains_addr e)"
"contains_addr (throw e) = contains_addr e"
"contains_addr (try e catch(C v) e') = (contains_addr e \<or> contains_addr e')"
"contains_addrs [] = False"
"contains_addrs (x # xs) = (contains_addr x \<or> contains_addrs xs)"

lemma contains_addrs_append [simp]: "contains_addrs (es @ fs) = (contains_addrs es \<or> contains_addrs fs)"
apply(induct es)
apply(auto)
done

consts
  expr_locks :: "expr \<Rightarrow> addr \<Rightarrow> nat"
  expr_lockss :: "expr list \<Rightarrow> addr \<Rightarrow> nat"

primrec
"expr_locks (new C) = (\<lambda>ad. 0)"
"expr_locks (newA T\<lfloor>e\<rceil>) = expr_locks e"
"expr_locks (Cast T e) = expr_locks e"
"expr_locks (Val v) = (\<lambda>ad. 0)"
"expr_locks (Var v) = (\<lambda>ad. 0)"
"expr_locks (e \<guillemotleft>bop\<guillemotright> e') = (\<lambda>ad. expr_locks e ad + expr_locks e' ad)"
"expr_locks (V := e) = expr_locks e"
"expr_locks (a\<lfloor>i\<rceil>) = (\<lambda>ad. expr_locks a ad + expr_locks i ad)"
"expr_locks (a\<lfloor>i\<rceil> := e) = (\<lambda>ad. expr_locks a ad + expr_locks i ad + expr_locks e ad)"
"expr_locks (e\<bullet>F{D}) = expr_locks e"
"expr_locks (e\<bullet>F{D} := e') = (\<lambda>ad. expr_locks e ad + expr_locks e' ad)"
"expr_locks (e\<bullet>m(ps)) = (\<lambda>ad. expr_locks e ad + expr_lockss ps ad)"
"expr_locks ({V : T; e}) = expr_locks e"
"expr_locks (sync(o') e) = (\<lambda>ad. if (o' = locked(ad)) then Suc (expr_locks e ad) else (expr_locks o' ad + expr_locks e ad))"
"expr_locks (e;;e') = (\<lambda>ad. expr_locks e ad + expr_locks e' ad)"
"expr_locks (if (b) e else e') = (\<lambda>ad. expr_locks b ad + expr_locks e ad + expr_locks e' ad)"
"expr_locks (while (b) e) = (\<lambda>ad. expr_locks b ad + expr_locks e ad)"
"expr_locks (throw e) = expr_locks e"
"expr_locks (try e catch(C v) e') = (\<lambda>ad. expr_locks e ad + expr_locks e' ad)"
"expr_lockss [] = (\<lambda>a. 0)"
"expr_lockss (x#xs) = (\<lambda>ad. expr_locks x ad + expr_lockss xs ad)"

lemma expr_lockss_append [simp]: "expr_lockss (es @ es') = (\<lambda>ad. expr_lockss es ad + expr_lockss es' ad)"
apply(induct es)
apply(auto intro: ext)
done

lemma expr_lockss_map_Val [simp]: "expr_lockss (map Val vs) = (\<lambda>ad. 0)"
apply(induct vs)
apply(auto)
done

lemma expr_locks_contains_addr: "expr_locks e a > 0 \<Longrightarrow> contains_addr e"
  and expr_lockss_contains_addrs: "expr_lockss es a > 0 \<Longrightarrow> contains_addrs es"
apply(induct e and es)
apply(auto simp add: lock_granted_def split:if_splits)
done

lemma contains_addr_expr_locks: "\<not> contains_addr e \<Longrightarrow> expr_locks e l = 0"
by(auto intro: expr_locks_contains_addr)

lemma contains_addrs_expr_lockss: "\<not> contains_addrs es \<Longrightarrow> expr_lockss es l = 0"
by(auto intro: expr_lockss_contains_addrs)

end
