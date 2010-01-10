(*  Title:      JinjaThreads/Compiler/WellType1.thy
    Author:     Andreas Lochbihler, Tobias Nipkow
*)

header {* \isaheader{Well-Formedness of Intermediate Language} *}

theory J1WellForm
imports "../J/JWellForm" J1
begin

subsection "Well-Typedness"

types 
  env1  = "ty list"   --"type environment indexed by variable number"

inductive WT1 :: "J1_prog \<Rightarrow> env1 \<Rightarrow> expr1 \<Rightarrow> ty \<Rightarrow> bool" ("_,_ \<turnstile>1 _ :: _"   [51,0,0,51] 50)
  and WTs1 :: "J1_prog \<Rightarrow> env1 \<Rightarrow> expr1 list \<Rightarrow> ty list \<Rightarrow> bool" ("_,_ \<turnstile>1 _ [::] _"   [51,0,0,51]50)
  for P :: J1_prog
  where

  WT1New:
  "is_class P C  \<Longrightarrow>
  P,E \<turnstile>1 new C :: Class C"

| WT1NewArray:
  "\<lbrakk> P,E \<turnstile>1 e :: Integer; is_type P T \<rbrakk> \<Longrightarrow>
  P,E \<turnstile>1 newA T\<lfloor>e\<rceil> :: T\<lfloor>\<rceil>"

| WT1Cast:
  "\<lbrakk> P,E \<turnstile>1 e :: T; P \<turnstile> U \<le> T \<or> P \<turnstile> T \<le> U; is_type P U \<rbrakk>
  \<Longrightarrow> P,E \<turnstile>1 Cast U e :: U"

| WT1Val:
  "typeof v = Some T \<Longrightarrow>
  P,E \<turnstile>1 Val v :: T"

| WT1Var:
  "\<lbrakk> E!V = T; V < size E \<rbrakk> \<Longrightarrow>
  P,E \<turnstile>1 Var V :: T"

| WT1BinOp:
  "\<lbrakk> P,E \<turnstile>1 e1 :: T1; P,E \<turnstile>1 e2 :: T2; P \<turnstile> T1\<guillemotleft>bop\<guillemotright>T2 :: T \<rbrakk>
  \<Longrightarrow> P,E \<turnstile>1 e1\<guillemotleft>bop\<guillemotright>e2 :: T"

| WT1LAss:
  "\<lbrakk> E!i = T;  i < size E; P,E \<turnstile>1 e :: T';  P \<turnstile> T' \<le> T \<rbrakk>
  \<Longrightarrow> P,E \<turnstile>1 i:=e :: Void"

| WT1AAcc:
  "\<lbrakk> P,E \<turnstile>1 a :: T\<lfloor>\<rceil>; P,E \<turnstile>1 i :: Integer \<rbrakk>
  \<Longrightarrow> P,E \<turnstile>1 a\<lfloor>i\<rceil> :: T"

| WT1AAss:
  "\<lbrakk> P,E \<turnstile>1 a :: T\<lfloor>\<rceil>; P,E \<turnstile>1 i :: Integer; P,E \<turnstile>1 e :: T'; P \<turnstile> T' \<le> T \<rbrakk>
  \<Longrightarrow> P,E \<turnstile>1 a\<lfloor>i\<rceil> := e :: Void"

| WT1ALength:
  "P,E \<turnstile>1 a :: T\<lfloor>\<rceil> \<Longrightarrow> P,E \<turnstile>1 a\<bullet>length :: Integer"

| WTFAcc1:
  "\<lbrakk> P,E \<turnstile>1 e :: Class C;  P \<turnstile> C sees F:T in D \<rbrakk>
  \<Longrightarrow> P,E \<turnstile>1 e\<bullet>F{D} :: T"

| WTFAss1:
  "\<lbrakk> P,E \<turnstile>1 e1 :: Class C;  P \<turnstile> C sees F:T in D;  P,E \<turnstile>1 e2 :: T';  P \<turnstile> T' \<le> T \<rbrakk>
  \<Longrightarrow> P,E \<turnstile>1 e1\<bullet>F{D} := e2 :: Void"

| WT1Call:
  "\<lbrakk> P,E \<turnstile>1 e :: Class C; \<not> is_external_call P (Class C) M; P \<turnstile> C sees M:Ts \<rightarrow> T = m in D;
     P,E \<turnstile>1 es [::] Ts'; P \<turnstile> Ts' [\<le>] Ts \<rbrakk>
  \<Longrightarrow> P,E \<turnstile>1 e\<bullet>M(es) :: T"

| WT1External:
  "\<lbrakk> P,E \<turnstile>1 e :: T; P,E \<turnstile>1 es [::] Ts; P \<turnstile> T\<bullet>M(Ts) :: U \<rbrakk>
  \<Longrightarrow> P,E \<turnstile>1 e\<bullet>M(es) :: U"

| WT1Block:
  "\<lbrakk> is_type P T;  P,E@[T] \<turnstile>1 e :: T'; case vo of None \<Rightarrow> True | \<lfloor>v\<rfloor> \<Rightarrow> \<exists>T'. typeof v = \<lfloor>T'\<rfloor> \<and> P \<turnstile> T' \<le> T \<rbrakk>
  \<Longrightarrow>  P,E \<turnstile>1 {V:T=vo; e} :: T'"

| WT1Synchronized:
  "\<lbrakk> P,E \<turnstile>1 o' :: T; is_refT T; T \<noteq> NT; P,E@[Class Object] \<turnstile>1 e :: T' \<rbrakk>
  \<Longrightarrow> P,E \<turnstile>1 sync\<^bsub>V\<^esub> (o') e :: T'"

| WT1Seq:
  "\<lbrakk> P,E \<turnstile>1 e\<^isub>1::T\<^isub>1;  P,E \<turnstile>1 e\<^isub>2::T\<^isub>2 \<rbrakk>
  \<Longrightarrow>  P,E \<turnstile>1 e\<^isub>1;;e\<^isub>2 :: T\<^isub>2"

| WT1Cond:
  "\<lbrakk> P,E \<turnstile>1 e :: Boolean;  P,E \<turnstile>1 e\<^isub>1::T\<^isub>1;  P,E \<turnstile>1 e\<^isub>2::T\<^isub>2;
     P \<turnstile> T\<^isub>1 \<le> T\<^isub>2 \<or> P \<turnstile> T\<^isub>2 \<le> T\<^isub>1;  P \<turnstile> T\<^isub>1 \<le> T\<^isub>2 \<longrightarrow> T = T\<^isub>2;  P \<turnstile> T\<^isub>2 \<le> T\<^isub>1 \<longrightarrow> T = T\<^isub>1 \<rbrakk>
  \<Longrightarrow> P,E \<turnstile>1 if (e) e\<^isub>1 else e\<^isub>2 :: T"

| WT1While:
  "\<lbrakk> P,E \<turnstile>1 e :: Boolean;  P,E \<turnstile>1 c::T \<rbrakk>
  \<Longrightarrow> P,E \<turnstile>1 while (e) c :: Void"

| WT1Throw:
  "\<lbrakk> P,E \<turnstile>1 e :: Class C; P \<turnstile> C \<preceq>\<^sup>* Throwable \<rbrakk> \<Longrightarrow> 
  P,E \<turnstile>1 throw e :: Void"

| WT1Try:
  "\<lbrakk> P,E \<turnstile>1 e\<^isub>1 :: T;  P,E@[Class C] \<turnstile>1 e\<^isub>2 :: T; is_class P C \<rbrakk>
  \<Longrightarrow> P,E \<turnstile>1 try e\<^isub>1 catch(C V) e\<^isub>2 :: T"

| WT1Nil: "P,E \<turnstile>1 [] [::] []"

| WT1Cons: "\<lbrakk> P,E \<turnstile>1 e :: T; P,E \<turnstile>1 es [::] Ts \<rbrakk> \<Longrightarrow> P,E \<turnstile>1 e#es [::] T#Ts"

declare WT1_WTs1.intros[intro!]
declare WT1Nil[iff]
declare WT1Call[rule del, intro]
declare WT1External[rule del, intro]

inductive_cases WT1_WTs1_cases[elim!]:
  "P,E \<turnstile>1 Val v :: T"
  "P,E \<turnstile>1 Var i :: T"
  "P,E \<turnstile>1 Cast D e :: T"
  "P,E \<turnstile>1 i:=e :: T"
  "P,E \<turnstile>1 {i:U=vo; e} :: T"
  "P,E \<turnstile>1 e1;;e2 :: T"
  "P,E \<turnstile>1 if (e) e1 else e2 :: T"
  "P,E \<turnstile>1 while (e) c :: T"
  "P,E \<turnstile>1 throw e :: T"
  "P,E \<turnstile>1 try e1 catch(C i) e2 :: T"
  "P,E \<turnstile>1 e\<bullet>F{D} :: T"
  "P,E \<turnstile>1 e1\<bullet>F{D}:=e2 :: T"
  "P,E \<turnstile>1 e1 \<guillemotleft>bop\<guillemotright> e2 :: T"
  "P,E \<turnstile>1 new C :: T"
  "P,E \<turnstile>1 newA T'\<lfloor>e\<rceil> :: T"
  "P,E \<turnstile>1 a\<lfloor>i\<rceil> := e :: T"
  "P,E \<turnstile>1 a\<lfloor>i\<rceil> :: T"
  "P,E \<turnstile>1 a\<bullet>length :: T"
  "P,E \<turnstile>1 e\<bullet>M(es) :: T"
  "P,E \<turnstile>1 sync\<^bsub>V\<^esub> (o') e :: T"
  "P,E \<turnstile>1 insync\<^bsub>V\<^esub> (a) e :: T"
  "P,E \<turnstile>1 [] [::] Ts"
  "P,E \<turnstile>1 e#es [::] Ts"

lemma WTs1_same_size: "P,E \<turnstile>1 es [::] Ts \<Longrightarrow> size es = size Ts"
by (induct es arbitrary: Ts) auto

lemma WTs1_snoc_cases:
  assumes wt: "P,E \<turnstile>1 es @ [e] [::] Ts"
  obtains T Ts' where "P,E \<turnstile>1 es [::] Ts'" "P,E \<turnstile>1 e :: T"
proof -
  from wt have "\<exists>T Ts'. P,E \<turnstile>1 es [::] Ts' \<and> P,E \<turnstile>1 e :: T"
    by(induct es arbitrary: Ts) auto
  thus thesis by(auto intro: that)
qed

lemma WTs1_append:
  assumes wt: "P,Env \<turnstile>1 es @ es' [::] Ts"
  obtains Ts' Ts'' where "P,Env \<turnstile>1 es [::] Ts'" "P,Env \<turnstile>1 es' [::] Ts''"
proof -
  from wt have "\<exists>Ts' Ts''. P,Env \<turnstile>1 es [::] Ts' \<and> P,Env \<turnstile>1 es' [::] Ts''"
    by(induct es arbitrary: Ts) auto
  thus ?thesis by(auto intro: that)
qed

lemma WT1_not_contains_insync: "P,E \<turnstile>1 e :: T \<Longrightarrow> \<not> contains_insync e"
  and WTs1_not_contains_insyncs: "P,E \<turnstile>1 es [::] Ts \<Longrightarrow> \<not> contains_insyncs es"
by(induct rule: WT1_WTs1.inducts) auto

lemma WT1_expr_locks: "P,E \<turnstile>1 e :: T \<Longrightarrow> expr_locks e = (\<lambda>a. 0)"
  and WTs1_expr_lockss: "P,E \<turnstile>1 es [::] Ts \<Longrightarrow> expr_lockss es = (\<lambda>a. 0)"
by(induct rule: WT1_WTs1.inducts)(auto)

lemma assumes wf: "wf_prog wfmd P"
  shows WT1_unique: "P,E \<turnstile>1 e :: T1 \<Longrightarrow> P,E \<turnstile>1 e :: T2 \<Longrightarrow> T1 = T2" 
  and WTs1_unique: "P,E \<turnstile>1 es [::] Ts1 \<Longrightarrow> P,E \<turnstile>1 es [::] Ts2 \<Longrightarrow> Ts1 = Ts2"
apply(induct arbitrary: T2 and Ts2 rule:WT1_WTs1.inducts)
apply blast
apply blast
apply blast
apply clarsimp
apply blast
apply(blast dest: WT_binop_fun)
apply blast
apply blast
apply blast
apply blast
apply (blast dest:sees_field_idemp sees_field_fun)
apply blast

apply(erule WT1_WTs1_cases)
 apply (blast dest:sees_method_idemp sees_method_fun)
apply(fastsimp dest: external_WT_is_external_call list_all2_lengthD WTs1_same_size)

apply(fastsimp dest: external_WT_is_external_call list_all2_lengthD WTs1_same_size external_WT_determ)
apply blast
apply blast
apply blast
apply blast
apply blast
apply blast
apply blast
apply blast
apply blast
done

lemma assumes wf: "wf_prog p P"
  shows WT1_is_type: "P,E \<turnstile>1 e :: T \<Longrightarrow> set E \<subseteq> is_type P \<Longrightarrow> is_type P T"
  and "P,E \<turnstile>1 es [::] Ts \<Longrightarrow> set E \<subseteq> is_type P \<Longrightarrow> set Ts \<subseteq> is_type P"
apply(induct rule:WT1_WTs1.inducts)
apply simp
apply simp
apply simp
apply (simp add:typeof_lit_is_type)
apply (fastsimp intro:nth_mem simp add: mem_def)
apply(simp add: WT_binop_is_type)
apply(simp)
apply(simp)
apply(simp)
apply(simp)
apply (simp add:sees_field_is_type[OF _ wf])
apply simp
apply(fastsimp dest!: sees_wf_mdecl[OF wf] simp:wf_mdecl_def)
apply(fastsimp dest: WT_external_is_type)
apply(simp add: mem_def)
apply(simp add: is_class_Object[OF wf] mem_def)
apply simp
apply blast
apply simp
apply simp
apply simp
apply simp
apply(simp add: mem_def)
done

lemma blocks1_WT:
  "\<lbrakk> P,Env @ Ts \<turnstile>1 body :: T; set Ts \<subseteq> is_type P \<rbrakk> \<Longrightarrow> P,Env \<turnstile>1 blocks1 (length Env) Ts body :: T"
proof(induct n\<equiv>"length Env" Ts body arbitrary: Env rule: blocks1.induct)
  case 1 thus ?case by simp
next
  case (2 T' Ts e)
  note IH = `\<And>Env'. \<lbrakk>Suc (length Env) = length Env'; P,Env' @ Ts \<turnstile>1 e :: T; set Ts \<subseteq> is_type P\<rbrakk>
              \<Longrightarrow> P,Env' \<turnstile>1 blocks1 (length Env') Ts e :: T`
  from `set (T' # Ts) \<subseteq> is_type P` have "set Ts \<subseteq> is_type P" "is_type P T'" by(auto simp add: mem_def)
  moreover from `P,Env @ T' # Ts \<turnstile>1 e :: T` have "P,(Env @ [T']) @ Ts \<turnstile>1 e :: T" by simp
  note IH[OF _ this]
  ultimately show ?case by auto
qed

subsection{* Well-formedness*}

--"Indices in blocks increase by 1"

consts
  \<B> :: "expr1 \<Rightarrow> nat \<Rightarrow> bool"
  \<B>s :: "expr1 list \<Rightarrow> nat \<Rightarrow> bool"
primrec
"\<B> (new C) i = True"
"\<B> (newA T\<lfloor>e\<rceil>) i = \<B> e i"
"\<B> (Cast C e) i = \<B> e i"
"\<B> (Val v) i = True"
"\<B> (e1 \<guillemotleft>bop\<guillemotright> e2) i = (\<B> e1 i \<and> \<B> e2 i)"
"\<B> (Var j) i = True"
"\<B> (j:=e) i = \<B> e i"
"\<B> (a\<lfloor>j\<rceil>) i = (\<B> a i \<and> \<B> j i)"
"\<B> (a\<lfloor>j\<rceil>:=e) i = (\<B> a i \<and> \<B> j i \<and> \<B> e i)"
"\<B> (a\<bullet>length) i = \<B> a i"
"\<B> (e\<bullet>F{D}) i = \<B> e i"
"\<B> (e1\<bullet>F{D} := e2) i = (\<B> e1 i \<and> \<B> e2 i)"
"\<B> (e\<bullet>M(es)) i = (\<B> e i \<and> \<B>s es i)"
"\<B> ({j:T=vo; e}) i = (i = j \<and> \<B> e (i+1))"
"\<B> (sync\<^bsub>V\<^esub> (o') e) i = (i = V \<and> \<B> o' i \<and> \<B> e (i+1))"
"\<B> (insync\<^bsub>V\<^esub> (a) e) i = (i = V \<and> \<B> e (i+1))"
"\<B> (e1;;e2) i = (\<B> e1 i \<and> \<B> e2 i)"
"\<B> (if (e) e1 else e2) i = (\<B> e i \<and> \<B> e1 i \<and> \<B> e2 i)"
"\<B> (throw e) i = \<B> e i"
"\<B> (while (e) c) i = (\<B> e i \<and> \<B> c i)"
"\<B> (try e1 catch(C j) e2) i = (\<B> e1 i \<and> i=j \<and> \<B> e2 (i+1))"

"\<B>s [] i = True"
"\<B>s (e#es) i = (\<B> e i \<and> \<B>s es i)"

lemma Bs_append [simp]: "\<B>s (es @ es') n \<longleftrightarrow> \<B>s es n \<and> \<B>s es' n"
by(induct es) auto

lemma Bs_map_Val [simp]: "\<B>s (map Val vs) n"
by(induct vs) auto

lemma B_blocks1 [intro]: "\<B> body (n + length Ts) \<Longrightarrow> \<B> (blocks1 n Ts body) n"
by(induct n Ts body rule: blocks1.induct)(auto)

lemma B_extRet2J [simp]: "\<B> (extRet2J va) n"
by(cases va) auto

lemma B_inline_call: "\<lbrakk> \<B> e n; \<And>n. \<B> e' n \<rbrakk> \<Longrightarrow> \<B> (inline_call e' e) n"
  and Bs_inline_calls: "\<lbrakk> \<B>s es n; \<And>n. \<B> e' n \<rbrakk> \<Longrightarrow> \<B>s (inline_calls e' es) n"
by(induct e and es arbitrary: n and n) auto

lemma red1_preserves_B: "\<lbrakk> P \<turnstile>1 \<langle>e, s\<rangle> -ta\<rightarrow> \<langle>e', s'\<rangle>; \<B> e n\<rbrakk> \<Longrightarrow> \<B> e' n"
  and reds1_preserves_Bs: "\<lbrakk> P \<turnstile>1 \<langle>es, s\<rangle> [-ta\<rightarrow>] \<langle>es', s'\<rangle>; \<B>s es n\<rbrakk> \<Longrightarrow> \<B>s es' n"
by(induct arbitrary: n and n rule: red1_reds1.inducts)(auto)


primrec syncvars :: "('a, 'a) exp \<Rightarrow> bool"
  and syncvarss :: "('a, 'a) exp list \<Rightarrow> bool"
where
  "syncvars (new C) = True"
| "syncvars (newA T\<lfloor>e\<rceil>) = syncvars e"
| "syncvars (Cast T e) = syncvars e"
| "syncvars (Val v) = True"
| "syncvars (e1 \<guillemotleft>bop\<guillemotright> e2) = (syncvars e1 \<and> syncvars e2)"
| "syncvars (Var V) = True"
| "syncvars (V:=e) = syncvars e"
| "syncvars (a\<lfloor>i\<rceil>) = (syncvars a \<and> syncvars i)"
| "syncvars (a\<lfloor>i\<rceil> := e) = (syncvars a \<and> syncvars i \<and> syncvars e)"
| "syncvars (a\<bullet>length) = syncvars a"
| "syncvars (e\<bullet>F{D}) = syncvars e"
| "syncvars (e\<bullet>F{D} := e2) = (syncvars e \<and> syncvars e2)"
| "syncvars (e\<bullet>M(es)) = (syncvars e \<and> syncvarss es)"
| "syncvars {V:T=vo;e} = syncvars e"
| "syncvars (sync\<^bsub>V\<^esub> (e1) e2) = (syncvars e1 \<and> syncvars e2 \<and> V \<notin> fv e2)"
| "syncvars (insync\<^bsub>V\<^esub> (a) e) = (syncvars e \<and> V \<notin> fv e)"
| "syncvars (e1;;e2) = (syncvars e1 \<and> syncvars e2)"
| "syncvars (if (b) e1 else e2) = (syncvars b \<and> syncvars e1 \<and> syncvars e2)"
| "syncvars (while (b) c) = (syncvars b \<and> syncvars c)"
| "syncvars (throw e) = syncvars e"
| "syncvars (try e1 catch(C V) e2) = (syncvars e1 \<and> syncvars e2)"

| "syncvarss [] = True"
| "syncvarss (e#es) = (syncvars e \<and> syncvarss es)"

lemma syncvarss_append [simp]: "syncvarss (es @ es') \<longleftrightarrow> syncvarss es \<and> syncvarss es'"
by(induct es) auto

lemma syncvarss_map_Val [simp]: "syncvarss (map Val vs)"
by(induct vs) auto

definition bsok :: "expr1 \<Rightarrow> nat \<Rightarrow> bool"
where "bsok e n \<equiv> \<B> e n \<and> expr_locks e = (\<lambda>ad. 0)"

definition bsoks :: "expr1 list \<Rightarrow> nat \<Rightarrow> bool"
where "bsoks es n \<equiv> \<B>s es n \<and> expr_lockss es = (\<lambda>ad. 0)"

lemma bsok_simps [simp]:
  "bsok (new C) n = True"
  "bsok (newA T\<lfloor>e\<rceil>) n = bsok e n"
  "bsok (Cast T e) n = bsok e n"
  "bsok (e1 \<guillemotleft>bop\<guillemotright> e2) n = (bsok e1 n \<and> bsok e2 n)"
  "bsok (Var V) n = True"
  "bsok (Val v) n = True"
  "bsok (V := e) n = bsok e n"
  "bsok (a\<lfloor>i\<rceil>) n = (bsok a n \<and> bsok i n)"
  "bsok (a\<lfloor>i\<rceil> := e) n = (bsok a n \<and> bsok i n \<and> bsok e n)"
  "bsok (a\<bullet>length) n = bsok a n"
  "bsok (e\<bullet>F{D}) n = bsok e n"
  "bsok (e\<bullet>F{D} := e') n = (bsok e n \<and> bsok e' n)"
  "bsok (e\<bullet>M(ps)) n = (bsok e n \<and> bsoks ps n)"
  "bsok {V:T=vo; e} n = (bsok e (Suc n) \<and> V = n)"
  "bsok (sync\<^bsub>V\<^esub> (e) e') n = (bsok e n \<and> bsok e' (Suc n) \<and> V = n)"
  "bsok (insync\<^bsub>V\<^esub> (ad) e) n = False"
  "bsok (e;; e') n = (bsok e n \<and> bsok e' n)"
  "bsok (if (e) e1 else e2) n = (bsok e n \<and> bsok e1 n \<and> bsok e2 n)"
  "bsok (while (b) c) n = (bsok b n \<and> bsok c n)"
  "bsok (throw e) n = bsok e n"
  "bsok (try e catch(C V) e') n = (bsok e n \<and> bsok e' (Suc n) \<and> V = n)"
  and bsoks_simps [simp]:
  "bsoks [] n = True"
  "bsoks (e # es) n = (bsok e n \<and> bsoks es n)"
by(auto simp add: bsok_def bsoks_def expand_fun_eq)

lemma WT1_fv: "\<lbrakk> P,E \<turnstile>1 e :: T; \<B> e (length E); syncvars e \<rbrakk> \<Longrightarrow> fv e \<subseteq> {0..<length E}"
  and WTs1_fvs: "\<lbrakk> P,E \<turnstile>1 es [::] Ts; \<B>s es (length E); syncvarss es \<rbrakk> \<Longrightarrow> fvs es \<subseteq> {0..<length E}"
proof(induct rule: WT1_WTs1.inducts)
  case (WT1Synchronized E e1 T e2 T' V)
  note IH1 = `\<lbrakk>\<B> e1 (length E); syncvars e1\<rbrakk> \<Longrightarrow> fv e1 \<subseteq> {0..<length E}`
  note IH2 = `\<lbrakk>\<B> e2 (length (E @ [Class Object])); syncvars e2\<rbrakk> \<Longrightarrow> fv e2 \<subseteq> {0..<length (E @ [Class Object])}`
  from `\<B> (sync\<^bsub>V\<^esub> (e1) e2) (length E)` have [simp]: "V = length E"
    and B1: "\<B> e1 (length E)" and B2: "\<B> e2 (Suc (length E))" by auto
  from `syncvars (sync\<^bsub>V\<^esub> (e1) e2)` have sync1: "syncvars e1" and sync2: "syncvars e2" and V: "V \<notin> fv e2" by auto
  have "fv e2 \<subseteq> {0..<length E}"
  proof
    fix x
    assume x: "x \<in> fv e2"
    with V have "x \<noteq> length E" by auto
    moreover from IH2 B2 sync2 have "fv e2 \<subseteq> {0..<Suc (length E)}" by auto
    with x have "x < Suc (length E)" by auto
    ultimately show "x \<in> {0..<length E}" by auto
  qed
  with IH1[OF B1 sync1] show ?case by(auto)
next
  case (WT1Cond E e e1 T1 e2 T2 T)
  thus ?case by(auto del: subsetI)
qed fastsimp+


definition wf_J1_mdecl :: "J1_prog \<Rightarrow> cname \<Rightarrow> expr1 mdecl \<Rightarrow> bool"
where
  "wf_J1_mdecl P C  \<equiv>  \<lambda>(M,Ts,T,body).
    (\<exists>T'. P,Class C#Ts \<turnstile>1 body :: T' \<and> P \<turnstile> T' \<le> T) \<and>
    \<D> body \<lfloor>{..size Ts}\<rfloor> \<and> \<B> body (size Ts + 1) \<and> syncvars body"

lemma wf_J1_mdecl[simp]:
  "wf_J1_mdecl P C (M,Ts,T,body) \<equiv>
    ((\<exists>T'. P,Class C#Ts \<turnstile>1 body :: T' \<and> P \<turnstile> T' \<le> T) \<and>
     \<D> body \<lfloor>{..size Ts}\<rfloor> \<and> \<B> body (size Ts + 1)) \<and> syncvars body"
by (simp add:wf_J1_mdecl_def)

abbreviation wf_J1_prog :: "J1_prog \<Rightarrow> bool"
where "wf_J1_prog == wf_prog wf_J1_mdecl"

end
