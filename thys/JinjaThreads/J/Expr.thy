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
  | InstanceOf "('a, 'b) exp" ty ("_ instanceof _" [99, 99] 90) -- "instance of"
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
  (type) "expr" <= (type) "(String.literal, unit) exp"
  (type) "J_prog" <= (type) "(String.literal list \<times> expr) prog"


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

abbreviation (in heap_base) THROW :: "cname \<Rightarrow> ('a,'b) exp"
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

primrec fv  :: "('a,'b) exp      \<Rightarrow> 'a set"
  and fvs :: "('a,'b) exp list \<Rightarrow> 'a set"
where
  "fv(new C) = {}"
| "fv(newA T\<lfloor>e\<rceil>) = fv e"
| "fv(Cast C e) = fv e"
| "fv(e instanceof T) = fv e"
| "fv(Val v) = {}"
| "fv(e\<^isub>1 \<guillemotleft>bop\<guillemotright> e\<^isub>2) = fv e\<^isub>1 \<union> fv e\<^isub>2"
| "fv(Var V) = {V}"
| "fv(a\<lfloor>i\<rceil>) = fv a \<union> fv i"
| "fv(AAss a i e) = fv a \<union> fv i \<union> fv e"
| "fv(a\<bullet>length) = fv a"
| "fv(LAss V e) = {V} \<union> fv e"
| "fv(e\<bullet>F{D}) = fv e"
| "fv(FAss e\<^isub>1 F D e\<^isub>2) = fv e\<^isub>1 \<union> fv e\<^isub>2"
| "fv(e\<bullet>M(es)) = fv e \<union> fvs es"
| "fv({V:T=vo; e}) = fv e - {V}"
| "fv(sync\<^bsub>V\<^esub> (h) e) = fv h \<union> fv e"
| "fv(insync\<^bsub>V\<^esub> (a) e) = fv e"
| "fv(e\<^isub>1;;e\<^isub>2) = fv e\<^isub>1 \<union> fv e\<^isub>2"
| "fv(if (b) e\<^isub>1 else e\<^isub>2) = fv b \<union> fv e\<^isub>1 \<union> fv e\<^isub>2"
| "fv(while (b) e) = fv b \<union> fv e"
| "fv(throw e) = fv e"
| "fv(try e\<^isub>1 catch(C V) e\<^isub>2) = fv e\<^isub>1 \<union> (fv e\<^isub>2 - {V})"

| "fvs([]) = {}"
| "fvs(e#es) = fv e \<union> fvs es"

lemma [simp]: "fvs(es @ es') = fvs es \<union> fvs es'"
by(induct es) auto

lemma [simp]: "fvs(map Val vs) = {}"
by (induct vs) auto

subsection{*Locks and addresses*}

primrec expr_locks :: "('a,'b) exp \<Rightarrow> addr \<Rightarrow> nat"
  and expr_lockss :: "('a,'b) exp list \<Rightarrow> addr \<Rightarrow> nat"
where
  "expr_locks (new C) = (\<lambda>ad. 0)"
| "expr_locks (newA T\<lfloor>e\<rceil>) = expr_locks e"
| "expr_locks (Cast T e) = expr_locks e"
| "expr_locks (e instanceof T) = expr_locks e"
| "expr_locks (Val v) = (\<lambda>ad. 0)"
| "expr_locks (Var v) = (\<lambda>ad. 0)"
| "expr_locks (e \<guillemotleft>bop\<guillemotright> e') = (\<lambda>ad. expr_locks e ad + expr_locks e' ad)"
| "expr_locks (V := e) = expr_locks e"
| "expr_locks (a\<lfloor>i\<rceil>) = (\<lambda>ad. expr_locks a ad + expr_locks i ad)"
| "expr_locks (AAss a i e) = (\<lambda>ad. expr_locks a ad + expr_locks i ad + expr_locks e ad)"
| "expr_locks (a\<bullet>length) = expr_locks a"
| "expr_locks (e\<bullet>F{D}) = expr_locks e"
| "expr_locks (FAss e F D e') = (\<lambda>ad. expr_locks e ad + expr_locks e' ad)"
| "expr_locks (e\<bullet>m(ps)) = (\<lambda>ad. expr_locks e ad + expr_lockss ps ad)"
| "expr_locks ({V : T=vo; e}) = expr_locks e"
| "expr_locks (sync\<^bsub>V\<^esub> (o') e) = (\<lambda>ad. expr_locks o' ad + expr_locks e ad)"
| "expr_locks (insync\<^bsub>V\<^esub> (a) e) = (\<lambda>ad. if (a = ad) then Suc (expr_locks e ad) else expr_locks e ad)"
| "expr_locks (e;;e') = (\<lambda>ad. expr_locks e ad + expr_locks e' ad)"
| "expr_locks (if (b) e else e') = (\<lambda>ad. expr_locks b ad + expr_locks e ad + expr_locks e' ad)"
| "expr_locks (while (b) e) = (\<lambda>ad. expr_locks b ad + expr_locks e ad)"
| "expr_locks (throw e) = expr_locks e"
| "expr_locks (try e catch(C v) e') = (\<lambda>ad. expr_locks e ad + expr_locks e' ad)"

| "expr_lockss [] = (\<lambda>a. 0)"
| "expr_lockss (x#xs) = (\<lambda>ad. expr_locks x ad + expr_lockss xs ad)"

lemma expr_lockss_append [simp]:
  "expr_lockss (es @ es') = (\<lambda>ad. expr_lockss es ad + expr_lockss es' ad)"
apply(induct es)
apply(auto intro: ext)
done

lemma expr_lockss_map_Val [simp]: "expr_lockss (map Val vs) = (\<lambda>ad. 0)"
apply(induct vs)
apply(auto)
done

primrec contains_insync :: "('a,'b) exp \<Rightarrow> bool"
  and contains_insyncs :: "('a,'b) exp list \<Rightarrow> bool"
where
  "contains_insync (new C) = False"
| "contains_insync (newA T\<lfloor>i\<rceil>) = contains_insync i"
| "contains_insync (Cast T e) = contains_insync e"
| "contains_insync (e instanceof T) = contains_insync e"
| "contains_insync (Val v) = False"
| "contains_insync (Var v) = False"
| "contains_insync (e \<guillemotleft>bop\<guillemotright> e') = (contains_insync e \<or> contains_insync e')"
| "contains_insync (V := e) = contains_insync e"
| "contains_insync (a\<lfloor>i\<rceil>) = (contains_insync a \<or> contains_insync i)"
| "contains_insync (AAss a i e) = (contains_insync a \<or> contains_insync i \<or> contains_insync e)"
| "contains_insync (a\<bullet>length) = contains_insync a"
| "contains_insync (e\<bullet>F{D}) = contains_insync e"
| "contains_insync (FAss e F D e') = (contains_insync e \<or> contains_insync e')"
| "contains_insync (e\<bullet>m(pns)) = (contains_insync e \<or> contains_insyncs pns)"
| "contains_insync ({V : T=vo; e}) = contains_insync e"
| "contains_insync (sync\<^bsub>V\<^esub> (o') e) = (contains_insync o' \<or> contains_insync e)"
| "contains_insync (insync\<^bsub>V\<^esub> (a) e) = True"
| "contains_insync (e;;e') = (contains_insync e \<or> contains_insync e')"
| "contains_insync (if (b) e else e') = (contains_insync b \<or> contains_insync e \<or> contains_insync e')"
| "contains_insync (while (b) e) = (contains_insync b \<or> contains_insync e)"
| "contains_insync (throw e) = contains_insync e"
| "contains_insync (try e catch(C v) e') = (contains_insync e \<or> contains_insync e')"

| "contains_insyncs [] = False"
| "contains_insyncs (x # xs) = (contains_insync x \<or> contains_insyncs xs)"
  
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

subsection {* @{text "blocks"} *}

fun blocks :: "'a list \<Rightarrow> ty list \<Rightarrow> val list \<Rightarrow> ('a,'b) exp \<Rightarrow> ('a,'b) exp"
where
  "blocks (V # Vs) (T # Ts) (v # vs) e = {V:T=\<lfloor>v\<rfloor>; blocks Vs Ts vs e}"
| "blocks []       []       []       e = e"

lemma [simp]:
  "\<lbrakk> size vs = size Vs; size Ts = size Vs \<rbrakk> \<Longrightarrow> fv (blocks Vs Ts vs e) = fv e - set Vs"
apply(induct rule:blocks.induct)
apply simp_all
apply blast
done

lemma expr_locks_blocks:
  "\<lbrakk> length vs = length pns; length Ts = length pns \<rbrakk>
  \<Longrightarrow> expr_locks (blocks pns Ts vs e) = expr_locks e"
by(induct pns Ts vs e rule: blocks.induct)(auto)

subsection {* Final expressions *}

inductive final :: "('a,'b) exp \<Rightarrow> bool" where
  "final (Val v)"
| "final (Throw a)"

declare final.cases [elim]
declare final.intros[simp]

lemmas finalE[consumes 1, case_names Val Throw] = final.cases

lemma final_iff: "final e \<longleftrightarrow> (\<exists>v. e = Val v) \<or> (\<exists>a. e = Throw a)"
by(auto)

lemma final_locks: "final e \<Longrightarrow> expr_locks e l = 0"
by(auto elim: finalE)

definition finals:: "('a,'b) exp list \<Rightarrow> bool"
where "finals es  \<equiv>  (\<exists>vs. es = map Val vs) \<or> (\<exists>vs a es'. es = map Val vs @ Throw a # es')"

lemma [iff]: "finals []"
by(simp add:finals_def)

lemma [iff]: "finals (Val v # es) = finals es"
apply(clarsimp simp add: finals_def)
apply(rule iffI)
 apply(erule disjE)
  apply fastsimp
 apply(rule disjI2)
 apply clarsimp
 apply(case_tac vs)
  apply simp
 apply fastsimp
apply(erule disjE)
 apply clarsimp
 apply(rule_tac x="v#vs" in exI)
 apply(simp)
apply(rule disjI2)
apply clarsimp
apply(rule_tac x = "v#vs" in exI)
apply simp
done

lemma finals_app_map[iff]: "finals (map Val vs @ es) = finals es"
(*<*)by(induct_tac vs, auto)(*>*)

lemma [iff]: "finals (map Val vs)"
(*<*)using finals_app_map[of vs "[]"]by(simp)(*>*)

lemma [iff]: "finals (throw e # es) = (\<exists>a. e = addr a)"
(*<*)
apply(simp add:finals_def)
apply(rule iffI)
 apply(erule disjE)
  apply(fastsimp)
 apply clarsimp
 apply(case_tac vs)
  apply simp
 apply fastsimp
apply clarsimp
apply(rule_tac x = "[]" in exI)
apply simp
apply(erule_tac x="[]" in allE)
apply(fastsimp)
done
(*>*)

lemma not_finals_ConsI: "\<not> final e \<Longrightarrow> \<not> finals(e#es)"
 (*<*)
apply(clarsimp simp add:finals_def final_iff)
apply(rule conjI)
 apply(fastsimp)
apply(clarsimp)
apply(case_tac vs)
apply auto
done
(*>*)

subsection {* converting results from external calls *}

primrec extRet2J :: "('a, 'b) exp \<Rightarrow> extCallRet \<Rightarrow> ('a, 'b) exp"
where
  "extRet2J e (RetVal v) = Val v"
| "extRet2J e (RetExc a) = Throw a"
| "extRet2J e RetStaySame = e"

lemma fv_extRet2J [simp]: "fv (extRet2J e va) \<subseteq> fv e"
by(cases va) simp_all

subsection {* expressions at a call *}

primrec call :: "('a,'b) exp \<Rightarrow> (addr \<times> mname \<times> val list) option"
  and calls :: "('a,'b) exp list \<Rightarrow> (addr \<times> mname \<times> val list) option"
where
  "call (new C) = None"
| "call (newA T\<lfloor>e\<rceil>) = call e"
| "call (Cast C e) = call e"
| "call (e instanceof T) = call e"
| "call (Val v) = None"
| "call (Var V) = None"
| "call (V:=e) = call e"
| "call (e \<guillemotleft>bop\<guillemotright> e') = (if is_val e then call e' else call e)"
| "call (a\<lfloor>i\<rceil>) = (if is_val a then call i else call a)"
| "call (AAss a i e) = (if is_val a then (if is_val i then call e else call i) else call a)"
| "call (a\<bullet>length) = call a"
| "call (e\<bullet>F{D}) = call e"
| "call (FAss e F D e') = (if is_val e then call e' else call e)"
| "call (e\<bullet>M(es)) = (if is_val e then
                     (if is_vals es \<and> is_addr e then \<lfloor>(THE a. e = addr a, M, THE vs. es = map Val vs)\<rfloor> else calls es) 
                     else call e)"
| "call ({V:T=vo; e}) = call e"
| "call (sync\<^bsub>V\<^esub> (o') e) = call o'"
| "call (insync\<^bsub>V\<^esub> (a) e) = call e"
| "call (e;;e') = call e"
| "call (if (e) e1 else e2) = call e"
| "call (while(b) e) = None"
| "call (throw e) = call e"
| "call (try e1 catch(C V) e2) = call e1"

| "calls [] = None"
| "calls (e#es) = (if is_val e then calls es else call e)"

lemma calls_append [simp]:
  "calls (es @ es') = (if calls es = None \<and> is_vals es then calls es' else calls es)"
by(induct es) auto

lemma call_callE [consumes 1, case_names CallObj CallParams Call]:
  "\<lbrakk> call (obj\<bullet>M(pns)) = \<lfloor>(a, M', vs)\<rfloor>;
     call obj = \<lfloor>(a, M', vs)\<rfloor> \<Longrightarrow> thesis; 
     \<And>v. \<lbrakk> obj = Val v; calls pns = \<lfloor>(a, M', vs)\<rfloor> \<rbrakk> \<Longrightarrow> thesis;
     \<lbrakk> obj = addr a; pns = map Val vs; M = M' \<rbrakk> \<Longrightarrow> thesis \<rbrakk> \<Longrightarrow> thesis"
by(auto split: split_if_asm simp add: is_vals_conv)

lemma calls_conv:
  "calls es = \<lfloor>aMvs\<rfloor> \<longleftrightarrow> (\<exists>vs e es'. es = map Val vs @ e # es' \<and> call e = \<lfloor>aMvs\<rfloor>)"
proof(induct es)
  case Nil thus ?case by simp
next
  case (Cons e es)
  note IH = `(calls es = \<lfloor>aMvs\<rfloor>) = (\<exists>vs e es'. es = map Val vs @ e # es' \<and> call e = \<lfloor>aMvs\<rfloor>)`
  show ?case
  proof(cases "is_val e")
    case True
    then obtain v where e: "e = Val v" by auto
    hence "calls (e # es) = calls es" by(auto)
    moreover from e
    have "(calls es = \<lfloor>aMvs\<rfloor>) = (\<exists>vs e' es'. e # es = map Val (v # vs) @ e' # es' \<and> call e' = \<lfloor>aMvs\<rfloor>)"
      unfolding IH by(auto)
    also from e have "\<dots> = (\<exists>vs e' es'. e # es = map Val vs @ e' # es' \<and> call e' = \<lfloor>aMvs\<rfloor>)"
      apply(auto simp add: Cons_eq_append_conv)
      apply(rule_tac x="v # vs" in exI)
      by(clarsimp)
    finally show ?thesis .
  next
    case False
    show ?thesis
    proof(rule iffI)
      assume "calls (e # es) = \<lfloor>aMvs\<rfloor>"
      with False have "call e = \<lfloor>aMvs\<rfloor>" by(auto)
      hence "e # es = map Val [] @ e # es" "call e = \<lfloor>aMvs\<rfloor>" by auto
      thus "\<exists>vs e' es'. e # es = map Val vs @ e' # es' \<and> call e' = \<lfloor>aMvs\<rfloor>" by blast
    next
      assume "\<exists>vs e' es'. e # es = map Val vs @ e' # es' \<and> call e' = \<lfloor>aMvs\<rfloor>"
      then obtain vs e' es' where "e # es = map Val vs @ e' # es'" "call e' = \<lfloor>aMvs\<rfloor>" by(blast)
      moreover
      with False have "vs = []" 
	by-(erule contrapos_np, auto simp add: neq_Nil_conv)
      ultimately show "calls (e # es) = \<lfloor>aMvs\<rfloor>" by(auto)
    qed
  qed
qed

lemma calls_map_Val [simp]:
  "calls (map Val vs) = None"
by(induct vs) auto

lemma call_not_is_val [dest]: "call e = \<lfloor>aMvs\<rfloor> \<Longrightarrow> \<not> is_val e"
by(cases e) auto

lemma is_calls_not_is_vals [dest]: "calls es = \<lfloor>aMvs\<rfloor> \<Longrightarrow> \<not> is_vals es"
by(induct es) auto


end
