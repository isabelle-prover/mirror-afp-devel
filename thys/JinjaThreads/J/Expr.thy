(*  Title:      JinjaThreads/J/Expr.thy
    Author:     Tobias Nipkow, Andreas Lochbihler
*)

header {* \isaheader{Expressions} *}

theory Expr imports
  "../Common/Exceptions"
  "../Common/BinOp"
  "../Common/ExternalCall"
begin

datatype ('a,'b) exp
  = new cname      -- "class instance creation"
  | newArray ty "('a,'b) exp" ("newA _\<lfloor>_\<rceil>" [99,0] 90)    -- "array instance creation: type, size in outermost dimension"
  | Cast ty "('a,'b) exp"      -- "type cast"
  | Val val      -- "value"
  | BinOp "('a,'b) exp" bop "('a,'b) exp"     ("_ \<guillemotleft>_\<guillemotright> _" [80,0,81] 80)      -- "binary operation"
  | Var 'a                                               -- "local variable (incl. parameter)"
  | LAss 'a "('a,'b) exp"            ("_:=_" [90,90]90)                    -- "local assignment"
  | AAcc "('a,'b) exp" "('a,'b) exp"            ("_\<lfloor>_\<rceil>" [99,0] 90)          -- "array cell read"
  | AAss "('a,'b) exp" "('a,'b) exp" "('a,'b) exp" ("_\<lfloor>_\<rceil> := _" [10,99,90] 90)    -- "array cell assignment"
  | ALen "('a,'b) exp"                 ("_\<bullet>length" [10] 90)          -- "array length"
  | FAcc "('a,'b) exp" vname cname     ("_\<bullet>_{_}" [10,90,99]90)       -- "field access"
  | FAss "('a,'b) exp" vname cname "('a,'b) exp"     ("_\<bullet>_{_} := _" [10,90,99,90]90)      -- "field assignment"
  | Call "('a,'b) exp" mname "('a,'b) exp list"     ("_\<bullet>_'(_')" [90,99,0] 90)            -- "method call"
  | Block 'a ty "val option" "('a,'b) exp"    ("'{_:_=_; _}")
  | Synchronized 'b "('a,'b) exp" "('a,'b) exp" ("sync\<^bsub>_\<^esub> '(_') _" [99,99,90] 90)
  | InSynchronized 'b addr "('a,'b) exp" ("insync\<^bsub>_\<^esub> '(_') _" [99,99,90] 90)
  | Seq "('a,'b) exp" "('a,'b) exp"     ("_;;/ _"             [61,60]60)
  | Cond "('a,'b) exp" "('a,'b) exp" "('a,'b) exp"     ("if '(_') _/ else _" [80,79,79]70)
  | While "('a,'b) exp" "('a,'b) exp"     ("while '(_') _"     [80,79]70)
  | throw "('a,'b) exp"
  | TryCatch "('a,'b) exp" cname 'a "('a,'b) exp"     ("try _/ catch'(_ _') _"  [0,99,80,79] 70)

types
  expr = "(vname, unit) exp"    -- "Jinja expression"
  J_mb = "vname list \<times> expr"    -- "Jinja method body: parameter names and expression"
  J_prog = "J_mb prog"          -- "Jinja program"

translations
  "expr" <= (type) "(message_string, unit) exp"
  "J_prog" <= (type) "(message_string list \<times> expr) prog"


subsection "Syntactic sugar"

abbreviation unit :: "('a,'b) exp"
where "unit \<equiv> Val Unit"

abbreviation null :: "('a,'b) exp"
where "null \<equiv> Val Null"

abbreviation addr :: "addr \<Rightarrow> ('a,'b) exp"
where "addr a == Val (Addr a)"

abbreviation true :: "('a,'b) exp"
where "true == Val (Bool True)"

abbreviation false :: "('a,'b) exp"
where "false == Val (Bool False)"

abbreviation Throw :: "addr \<Rightarrow> ('a,'b) exp"
where "Throw a == throw (Val (Addr a))"

abbreviation THROW :: "cname \<Rightarrow> ('a,'b) exp"
where "THROW xc == Throw (addr_of_sys_xcpt xc)"

abbreviation sync_unit_syntax :: "('a,unit) exp \<Rightarrow> ('a,unit) exp \<Rightarrow> ('a,unit) exp" ("sync'(_') _" [99,90] 90)
where "sync(e1) e2 \<equiv> sync\<^bsub>()\<^esub> (e1) e2"

abbreviation insync_unit_syntax :: "addr \<Rightarrow> ('a,unit) exp \<Rightarrow> ('a,unit) exp" ("insync'(_') _" [99,90] 90)
where "insync(a) e2 \<equiv> insync\<^bsub>()\<^esub> (a) e2"

lemma inj_Val [simp]: "inj Val"
by(rule inj_onI)(simp)

lemma expr_ineqs [simp]: "Val v ;; e \<noteq> e" "if (e1) e else e2 \<noteq> e" "if (e1) e2 else e \<noteq> e"
by(induct e) auto

subsection{*Free Variables*}

consts
  fv  :: "('a,'b) exp      \<Rightarrow> 'a set"
  fvs :: "('a,'b) exp list \<Rightarrow> 'a set"
primrec
  "fv(new C) = {}"
  "fv(newA T\<lfloor>e\<rceil>) = fv e"
  "fv(Cast C e) = fv e"
  "fv(Val v) = {}"
  "fv(e\<^isub>1 \<guillemotleft>bop\<guillemotright> e\<^isub>2) = fv e\<^isub>1 \<union> fv e\<^isub>2"
  "fv(Var V) = {V}"
  "fv(a\<lfloor>i\<rceil>) = fv a \<union> fv i"
  "fv(AAss a i e) = fv a \<union> fv i \<union> fv e"
  "fv(a\<bullet>length) = fv a"
  "fv(LAss V e) = {V} \<union> fv e"
  "fv(e\<bullet>F{D}) = fv e"
  "fv(FAss e\<^isub>1 F D e\<^isub>2) = fv e\<^isub>1 \<union> fv e\<^isub>2"
  "fv(e\<bullet>M(es)) = fv e \<union> fvs es"
  "fv({V:T=vo; e}) = fv e - {V}"
  "fv(sync\<^bsub>V\<^esub> (h) e) = fv h \<union> fv e"
  "fv(insync\<^bsub>V\<^esub> (a) e) = fv e"
  "fv(e\<^isub>1;;e\<^isub>2) = fv e\<^isub>1 \<union> fv e\<^isub>2"
  "fv(if (b) e\<^isub>1 else e\<^isub>2) = fv b \<union> fv e\<^isub>1 \<union> fv e\<^isub>2"
  "fv(while (b) e) = fv b \<union> fv e"
  "fv(throw e) = fv e"
  "fv(try e\<^isub>1 catch(C V) e\<^isub>2) = fv e\<^isub>1 \<union> (fv e\<^isub>2 - {V})"

  "fvs([]) = {}"
  "fvs(e#es) = fv e \<union> fvs es"

lemma [simp]: "fvs(es @ es') = fvs es \<union> fvs es'"
by(induct es) auto

lemma [simp]: "fvs(map Val vs) = {}"
by (induct vs) auto

subsection{*Locks and addresses*}

consts
  expr_locks :: "('a,'b) exp \<Rightarrow> addr \<Rightarrow> nat"
  expr_lockss :: "('a,'b) exp list \<Rightarrow> addr \<Rightarrow> nat"

primrec
"expr_locks (new C) = (\<lambda>ad. 0)"
"expr_locks (newA T\<lfloor>e\<rceil>) = expr_locks e"
"expr_locks (Cast T e) = expr_locks e"
"expr_locks (Val v) = (\<lambda>ad. 0)"
"expr_locks (Var v) = (\<lambda>ad. 0)"
"expr_locks (e \<guillemotleft>bop\<guillemotright> e') = (\<lambda>ad. expr_locks e ad + expr_locks e' ad)"
"expr_locks (V := e) = expr_locks e"
"expr_locks (a\<lfloor>i\<rceil>) = (\<lambda>ad. expr_locks a ad + expr_locks i ad)"
"expr_locks (AAss a i e) = (\<lambda>ad. expr_locks a ad + expr_locks i ad + expr_locks e ad)"
"expr_locks (a\<bullet>length) = expr_locks a"
"expr_locks (e\<bullet>F{D}) = expr_locks e"
"expr_locks (FAss e F D e') = (\<lambda>ad. expr_locks e ad + expr_locks e' ad)"
"expr_locks (e\<bullet>m(ps)) = (\<lambda>ad. expr_locks e ad + expr_lockss ps ad)"
"expr_locks ({V : T=vo; e}) = expr_locks e"
"expr_locks (sync\<^bsub>V\<^esub> (o') e) = (\<lambda>ad. expr_locks o' ad + expr_locks e ad)"
"expr_locks (insync\<^bsub>V\<^esub> (a) e) = (\<lambda>ad. if (a = ad) then Suc (expr_locks e ad) else expr_locks e ad)"
"expr_locks (e;;e') = (\<lambda>ad. expr_locks e ad + expr_locks e' ad)"
"expr_locks (if (b) e else e') = (\<lambda>ad. expr_locks b ad + expr_locks e ad + expr_locks e' ad)"
"expr_locks (while (b) e) = (\<lambda>ad. expr_locks b ad + expr_locks e ad)"
"expr_locks (throw e) = expr_locks e"
"expr_locks (try e catch(C v) e') = (\<lambda>ad. expr_locks e ad + expr_locks e' ad)"
"expr_lockss [] = (\<lambda>a. 0)"
"expr_lockss (x#xs) = (\<lambda>ad. expr_locks x ad + expr_lockss xs ad)"

lemma expr_lockss_append [simp]:
  "expr_lockss (es @ es') = (\<lambda>ad. expr_lockss es ad + expr_lockss es' ad)"
apply(induct es)
apply(auto intro: ext)
done

lemma expr_lockss_map_Val [simp]: "expr_lockss (map Val vs) = (\<lambda>ad. 0)"
apply(induct vs)
apply(auto)
done

consts
  contains_insync :: "('a,'b) exp \<Rightarrow> bool"
  contains_insyncs :: "('a,'b) exp list \<Rightarrow> bool"

primrec
  "contains_insync (new C) = False"
  "contains_insync (newA T\<lfloor>i\<rceil>) = contains_insync i"
  "contains_insync (Cast T e) = contains_insync e"
  "contains_insync (Val v) = False"
  "contains_insync (Var v) = False"
  "contains_insync (e \<guillemotleft>bop\<guillemotright> e') = (contains_insync e \<or> contains_insync e')"
  "contains_insync (V := e) = contains_insync e"
  "contains_insync (a\<lfloor>i\<rceil>) = (contains_insync a \<or> contains_insync i)"
  "contains_insync (AAss a i e) = (contains_insync a \<or> contains_insync i \<or> contains_insync e)"
  "contains_insync (a\<bullet>length) = contains_insync a"
  "contains_insync (e\<bullet>F{D}) = contains_insync e"
  "contains_insync (FAss e F D e') = (contains_insync e \<or> contains_insync e')"
  "contains_insync (e\<bullet>m(pns)) = (contains_insync e \<or> contains_insyncs pns)"
  "contains_insync ({V : T=vo; e}) = contains_insync e"
  "contains_insync (sync\<^bsub>V\<^esub> (o') e) = (contains_insync o' \<or> contains_insync e)"
  "contains_insync (insync\<^bsub>V\<^esub> (a) e) = True"
  "contains_insync (e;;e') = (contains_insync e \<or> contains_insync e')"
  "contains_insync (if (b) e else e') = (contains_insync b \<or> contains_insync e \<or> contains_insync e')"
  "contains_insync (while (b) e) = (contains_insync b \<or> contains_insync e)"
  "contains_insync (throw e) = contains_insync e"
  "contains_insync (try e catch(C v) e') = (contains_insync e \<or> contains_insync e')"
  "contains_insyncs [] = False"
  "contains_insyncs (x # xs) = (contains_insync x \<or> contains_insyncs xs)"
  
lemma contains_insyncs_append [simp]:
  "contains_insyncs (es @ es') \<longleftrightarrow> contains_insyncs es \<or> contains_insyncs es'"
by(induct es, auto)

lemma fixes e :: "('a, 'b) exp"
  and es :: "('a, 'b) exp list"
  shows contains_insync_conv: "(contains_insync e \<longleftrightarrow> (\<exists>ad. expr_locks e ad > 0))"
    and contains_insyncs_conv: "(contains_insyncs es \<longleftrightarrow> (\<exists>ad. expr_lockss es ad > 0))"
by(induct e and es)(auto)

lemma contains_insyncs_map_Val [simp]: "\<not> contains_insyncs (map Val vs)"
by(induct vs) auto

lemma fixes e :: "('a, 'b) exp" and es :: "('a, 'b) exp list"
  shows contains_insync_expr_locks_conv: "contains_insync e \<longleftrightarrow> (\<exists>l. expr_locks e l > 0)"
  and contains_insyncs_expr_lockss_conv: "contains_insyncs es \<longleftrightarrow> (\<exists>l. expr_lockss es l > 0)"
apply(induct e and es)
apply auto
done


subsection {* Value expressions *}

inductive is_val :: "('a,'b) exp \<Rightarrow> bool" where
  "is_val (Val v)"

declare is_val.intros [simp]
declare is_val.cases [elim!]

lemma is_val_iff: "is_val e \<longleftrightarrow> (\<exists>v. e = Val v)"
by(auto)

fun is_vals :: "('a,'b) exp list \<Rightarrow> bool" where
  "is_vals [] = True"
| "is_vals (e#es) = (is_val e \<and> is_vals es)"

lemma is_vals_append [simp]: "is_vals (es @ es') \<longleftrightarrow> is_vals es \<and> is_vals es'"
apply(induct es, auto)
done

lemma is_vals_conv: "is_vals es = (\<exists>vs. es = map Val vs)"
apply(induct es, auto)
apply(rule_tac x="v#vsa" in exI, simp)
done

lemma is_vals_map_Vals [simp]: "is_vals (map Val vs) = True"
unfolding is_vals_conv by auto


inductive is_addr :: "('a,'b) exp \<Rightarrow> bool"
where "is_addr (addr a)"

declare is_addr.intros[intro!]
declare is_addr.cases[elim!]

lemma [simp]: "(is_addr e) \<longleftrightarrow> (\<exists>a. e = addr a)"
by auto


end
