(*  Title:      JinjaThreads/J/WellType.thy
    Author:     Tobias Nipkow, Andreas Lochbihler
*)

header {* \isaheader{Well-typedness of Jinja expressions} *}

theory WellType
imports Expr State "../Common/ExternalCall"
begin

types 
  env  = "vname \<rightharpoonup> ty"

inductive WT :: "J_prog \<Rightarrow> env \<Rightarrow> expr \<Rightarrow> ty \<Rightarrow> bool" ("_,_ \<turnstile> _ :: _"   [51,51,51]50)
  and WTs :: "J_prog \<Rightarrow> env \<Rightarrow> expr list \<Rightarrow> ty list \<Rightarrow> bool" ("_,_ \<turnstile> _ [::] _"   [51,51,51]50)
  for P :: "J_prog"
  where

  WTNew:
  "is_class P C  \<Longrightarrow>
  P,E \<turnstile> new C :: Class C"

| WTNewArray:
  "\<lbrakk> P,E \<turnstile> e :: Integer; is_type P T \<rbrakk> \<Longrightarrow>
  P,E \<turnstile> newA T\<lfloor>e\<rceil> :: T\<lfloor>\<rceil>"

| WTCast:
  "\<lbrakk> P,E \<turnstile> e :: T; P \<turnstile> U \<le> T \<or> P \<turnstile> T \<le> U; is_type P U \<rbrakk>
  \<Longrightarrow> P,E \<turnstile> Cast U e :: U"

| WTInstanceOf:
  "\<lbrakk> P,E \<turnstile> e :: T; P \<turnstile> U \<le> T \<or> P \<turnstile> T \<le> U; is_type P U; is_refT T; is_refT U \<rbrakk>
  \<Longrightarrow> P,E \<turnstile> e instanceof U :: Boolean"

| WTVal:
  "typeof v = Some T \<Longrightarrow>
  P,E \<turnstile> Val v :: T"

| WTVar:
  "E V = Some T \<Longrightarrow>
  P,E \<turnstile> Var V :: T"

| WTBinOp:
  "\<lbrakk> P,E \<turnstile> e1 :: T1; P,E \<turnstile> e2 :: T2; P \<turnstile> T1\<guillemotleft>bop\<guillemotright>T2 :: T \<rbrakk>
  \<Longrightarrow> P,E \<turnstile> e1\<guillemotleft>bop\<guillemotright>e2 :: T"

| WTLAss:
  "\<lbrakk> E V = Some T;  P,E \<turnstile> e :: T';  P \<turnstile> T' \<le> T;  V \<noteq> this \<rbrakk>
  \<Longrightarrow> P,E \<turnstile> V:=e :: Void"

| WTAAcc:
  "\<lbrakk> P,E \<turnstile> a :: T\<lfloor>\<rceil>; P,E \<turnstile> i :: Integer \<rbrakk>
  \<Longrightarrow> P,E \<turnstile> a\<lfloor>i\<rceil> :: T"

| WTAAss:
  "\<lbrakk> P,E \<turnstile> a :: T\<lfloor>\<rceil>; P,E \<turnstile> i :: Integer; P,E \<turnstile> e :: T'; P \<turnstile> T' \<le> T \<rbrakk>
  \<Longrightarrow> P,E \<turnstile> a\<lfloor>i\<rceil> := e :: Void"

| WTALength:
  "P,E \<turnstile> a :: T\<lfloor>\<rceil> \<Longrightarrow> P,E \<turnstile> a\<bullet>length :: Integer"

| WTFAcc:
  "\<lbrakk> P,E \<turnstile> e :: Class C;  P \<turnstile> C sees F:T in D \<rbrakk>
  \<Longrightarrow> P,E \<turnstile> e\<bullet>F{D} :: T"

| WTFAss:
  "\<lbrakk> P,E \<turnstile> e\<^isub>1 :: Class C;  P \<turnstile> C sees F:T in D;  P,E \<turnstile> e\<^isub>2 :: T';  P \<turnstile> T' \<le> T \<rbrakk>
  \<Longrightarrow> P,E \<turnstile> e\<^isub>1\<bullet>F{D}:=e\<^isub>2 :: Void"

| WTCall:
  "\<lbrakk> P,E \<turnstile> e :: Class C; \<not> is_external_call P (Class C) M; P \<turnstile> C sees M:Ts \<rightarrow> T = (pns,body) in D;
     P,E \<turnstile> es [::] Ts'; P \<turnstile> Ts' [\<le>] Ts \<rbrakk>
  \<Longrightarrow> P,E \<turnstile> e\<bullet>M(es) :: T"

| WTExternal:
  "\<lbrakk> P,E \<turnstile> e :: T; P,E \<turnstile> es [::] Ts; P \<turnstile> T\<bullet>M(Ts') :: U; P \<turnstile> Ts [\<le>] Ts' \<rbrakk>
  \<Longrightarrow> P,E \<turnstile> e\<bullet>M(es) :: U"

| WTBlock:
  "\<lbrakk> is_type P T;  P,E(V \<mapsto> T) \<turnstile> e :: T'; case vo of None \<Rightarrow> True | \<lfloor>v\<rfloor> \<Rightarrow> \<exists>T'. typeof v = \<lfloor>T'\<rfloor> \<and> P \<turnstile> T' \<le> T \<rbrakk>
  \<Longrightarrow>  P,E \<turnstile> {V:T=vo; e} :: T'"

| WTSynchronized:
  "\<lbrakk> P,E \<turnstile> o' :: T; is_refT T; T \<noteq> NT; P,E \<turnstile> e :: T' \<rbrakk>
  \<Longrightarrow> P,E \<turnstile> sync(o') e :: T'"

-- "Note that insync is not statically typable."

| WTSeq:
  "\<lbrakk> P,E \<turnstile> e\<^isub>1::T\<^isub>1;  P,E \<turnstile> e\<^isub>2::T\<^isub>2 \<rbrakk>
  \<Longrightarrow>  P,E \<turnstile> e\<^isub>1;;e\<^isub>2 :: T\<^isub>2"
| WTCond:
  "\<lbrakk> P,E \<turnstile> e :: Boolean;  P,E \<turnstile> e\<^isub>1::T\<^isub>1;  P,E \<turnstile> e\<^isub>2::T\<^isub>2;
     P \<turnstile> T\<^isub>1 \<le> T\<^isub>2 \<or> P \<turnstile> T\<^isub>2 \<le> T\<^isub>1;  P \<turnstile> T\<^isub>1 \<le> T\<^isub>2 \<longrightarrow> T = T\<^isub>2;  P \<turnstile> T\<^isub>2 \<le> T\<^isub>1 \<longrightarrow> T = T\<^isub>1 \<rbrakk>
  \<Longrightarrow> P,E \<turnstile> if (e) e\<^isub>1 else e\<^isub>2 :: T"

| WTWhile:
  "\<lbrakk> P,E \<turnstile> e :: Boolean;  P,E \<turnstile> c::T \<rbrakk>
  \<Longrightarrow> P,E \<turnstile> while (e) c :: Void"

| WTThrow:
  "\<lbrakk> P,E \<turnstile> e :: Class C; P \<turnstile> C \<preceq>\<^sup>* Throwable \<rbrakk> \<Longrightarrow> 
  P,E \<turnstile> throw e :: Void"

| WTTry:
  "\<lbrakk> P,E \<turnstile> e\<^isub>1 :: T;  P,E(V \<mapsto> Class C) \<turnstile> e\<^isub>2 :: T; P \<turnstile> C \<preceq>\<^sup>* Throwable \<rbrakk>
  \<Longrightarrow> P,E \<turnstile> try e\<^isub>1 catch(C V) e\<^isub>2 :: T"

| WTNil: "P,E \<turnstile> [] [::] []"

| WTCons: "\<lbrakk> P,E \<turnstile> e :: T; P,E \<turnstile> es [::] Ts \<rbrakk> \<Longrightarrow> P,E \<turnstile> e#es [::] T#Ts"


declare WT_WTs.intros[intro!]
declare WTCall[rule del, intro] WTExternal[rule del, intro]

lemma [iff]: "(P,E \<turnstile> [] [::] Ts) = (Ts = [])"
by (auto elim: WTs.cases)


lemma [iff]: "(P,E \<turnstile> e#es [::] T#Ts) = (P,E \<turnstile> e :: T \<and> P,E \<turnstile> es [::] Ts)"
by (auto elim: WTs.cases)

lemma WTs_conv_list_all2: "P,E \<turnstile> es [::] Ts = list_all2 (WT P E) es Ts"
by(induct es arbitrary: Ts)(auto simp add: list_all2_Cons1 elim: WTs.cases)

lemma [iff]: "(P,E \<turnstile> (e#es) [::] Ts) =
  (\<exists>U Us. Ts = U#Us \<and> P,E \<turnstile> e :: U \<and> P,E \<turnstile> es [::] Us)"
by(simp add: WTs_conv_list_all2 list_all2_Cons1)

lemma [iff]: "\<And>Ts. (P,E \<turnstile> es\<^isub>1 @ es\<^isub>2 [::] Ts) =
  (\<exists>Ts\<^isub>1 Ts\<^isub>2. Ts = Ts\<^isub>1 @ Ts\<^isub>2 \<and> P,E \<turnstile> es\<^isub>1 [::] Ts\<^isub>1 \<and> P,E \<turnstile> es\<^isub>2[::]Ts\<^isub>2)"
by(auto simp add: WTs_conv_list_all2 list_all2_append1 dest: list_all2_lengthD[symmetric])

lemma [iff]: "P,E \<turnstile> Val v :: T = (typeof v = Some T)"
by (auto elim: WT.cases)

lemma [iff]: "P,E \<turnstile> Var V :: T = (E V = Some T)"
by (auto elim: WT.cases)

lemma [iff]: "P,E \<turnstile> e\<^isub>1;;e\<^isub>2 :: T\<^isub>2 = (\<exists>T\<^isub>1. P,E \<turnstile> e\<^isub>1::T\<^isub>1 \<and> P,E \<turnstile> e\<^isub>2::T\<^isub>2)"
by (auto elim: WT.cases)

lemma [iff]: "(P,E \<turnstile> {V:T=vo; e} :: T') \<longleftrightarrow> is_type P T \<and> P,E(V\<mapsto>T) \<turnstile> e :: T' \<and> (case vo of None \<Rightarrow> True | Some v \<Rightarrow> \<exists>T'. typeof v = \<lfloor>T'\<rfloor> \<and> P \<turnstile> T' \<le> T)"
by (auto elim: WT.cases)

inductive_cases WT_elim_cases[elim!]:
  "P,E \<turnstile> V :=e :: T"
  "P,E \<turnstile> sync(o') e :: T"
  "P,E \<turnstile> if (e) e\<^isub>1 else e\<^isub>2 :: T"
  "P,E \<turnstile> while (e) c :: T"
  "P,E \<turnstile> throw e :: T"
  "P,E \<turnstile> try e\<^isub>1 catch(C V) e\<^isub>2 :: T"
  "P,E \<turnstile> Cast D e :: T"
  "P,E \<turnstile> e instanceof U :: T"
  "P,E \<turnstile> a\<bullet>F{D} :: T"
  "P,E \<turnstile> a\<bullet>F{D} := v :: T"
  "P,E \<turnstile> e\<^isub>1 \<guillemotleft>bop\<guillemotright> e\<^isub>2 :: T"
  "P,E \<turnstile> new C :: T"
  "P,E \<turnstile> newA T\<lfloor>e\<rceil> :: T'"
  "P,E \<turnstile> a\<lfloor>i\<rceil> := e :: T"
  "P,E \<turnstile> a\<lfloor>i\<rceil> :: T"
  "P,E \<turnstile> a\<bullet>length :: T"
  "P,E \<turnstile> e\<bullet>M(ps) :: T"
  "P,E \<turnstile> sync(o') e :: T"
  "P,E \<turnstile> insync(a) e :: T"

inductive_cases WT_callE:
  "P,E \<turnstile> e\<bullet>M(es) :: T"

lemma WT_unique: "\<lbrakk> P,E \<turnstile> e :: T; P,E \<turnstile> e :: T' \<rbrakk> \<Longrightarrow> T = T'"
  and WTs_unique: "\<lbrakk> P,E \<turnstile> es [::] Ts; P,E \<turnstile> es [::] Ts' \<rbrakk> \<Longrightarrow> Ts = Ts'"
apply(induct arbitrary: T' and Ts' rule: WT_WTs.inducts)
apply blast
apply blast
apply blast
apply blast
apply fastsimp
apply fastsimp
apply(fastsimp dest: WT_binop_fun)
apply fastsimp
apply fastsimp
apply fastsimp
apply fastsimp
apply(fastsimp dest: sees_field_fun)
apply(fastsimp dest: sees_field_fun)
apply(erule WT_callE)
 apply(fastsimp dest: sees_method_fun)
apply(fastsimp dest: external_WT_is_external_call)
apply(erule WT_callE)
 apply(fastsimp dest: external_WT_is_external_call)
apply(fastsimp dest: external_WT_determ)
apply fastsimp
apply fastsimp
apply fastsimp
apply force
apply fastsimp
apply fastsimp
apply blast
apply fastsimp
apply fastsimp
done

lemma wt_env_mono: "P,E \<turnstile> e :: T \<Longrightarrow> (\<And>E'. E \<subseteq>\<^sub>m E' \<Longrightarrow> P,E' \<turnstile> e :: T)"
  and wts_env_mono: "P,E \<turnstile> es [::] Ts \<Longrightarrow> (\<And>E'. E \<subseteq>\<^sub>m E' \<Longrightarrow> P,E' \<turnstile> es [::] Ts)"
apply(induct rule: WT_WTs.inducts)
apply(simp add: WTNew)
apply(simp add: WTNewArray)
apply(fastsimp simp: WTCast)
apply(fastsimp simp: WTInstanceOf)
apply(fastsimp simp: WTVal)
apply(simp add: WTVar map_le_def dom_def)
apply(fastsimp simp: WTBinOp)
apply(force simp:map_le_def)
apply(simp add: WTAAcc)
apply(simp add: WTAAss, fastsimp)
apply(simp add: WTALength, fastsimp)
apply(fastsimp simp: WTFAcc)
apply(fastsimp simp: WTFAss del:WT_WTs.intros WT_elim_cases)
apply(clarsimp, rule WTCall, blast+)[1]
apply(fastsimp)
apply(fastsimp simp: map_le_def WTBlock)
apply(fastsimp simp: WTSynchronized)
apply(fastsimp simp: WTSeq)
apply(fastsimp simp: WTCond)
apply(fastsimp simp: WTWhile)
apply(fastsimp simp: WTThrow)
apply(fastsimp simp: WTTry map_le_def dom_def)
apply(fastsimp)+
done


lemma WT_fv: "P,E \<turnstile> e :: T \<Longrightarrow> fv e \<subseteq> dom E"
  and WT_fvs: "P,E \<turnstile> es [::] Ts \<Longrightarrow> fvs es \<subseteq> dom E"
apply(induct rule:WT_WTs.inducts)
apply(simp_all del: fun_upd_apply)
apply fast+
done

lemma WT_expr_locks: "P,E \<turnstile> e :: T \<Longrightarrow> expr_locks e = (\<lambda>ad. 0)"
  and WTs_expr_lockss: "P,E \<turnstile> es [::] Ts \<Longrightarrow> expr_lockss es = (\<lambda>ad. 0)"
by(induct rule: WT_WTs.inducts)(auto)


subsection {* Code generation *}

text {*
  Alternative introduction rules for WT.
  To avoid manually stating an elimination rule for the new
  alternative introduction rules, we define a new predicate with
  appropriate rules and show that it is the same as @{term "WT"}
*}
inductive WT_code ::"J_prog \<Rightarrow> env \<Rightarrow> expr \<Rightarrow> ty \<Rightarrow> bool" ("_,_ \<turnstile>c _ :: _"   [51,51,51]50)
  for P :: "J_prog"
where
  WTNew_code: "is_class P C \<Longrightarrow> P,E \<turnstile>c new C :: Class C"
| WTNewArray_code: "\<lbrakk> P,E \<turnstile> e :: Integer; is_type P T \<rbrakk> \<Longrightarrow> P,E \<turnstile>c newA T\<lfloor>e\<rceil> :: T\<lfloor>\<rceil>"
| WTCast_code: "\<lbrakk> P,E \<turnstile> e :: T; P \<turnstile> U \<le> T \<or> P \<turnstile> T \<le> U; is_type P U \<rbrakk> \<Longrightarrow> P,E \<turnstile>c Cast U e :: U"
| WTInstanceof_code: "\<lbrakk> P,E \<turnstile> e :: T; P \<turnstile> U \<le> T \<or> P \<turnstile> T \<le> U; is_type P U; is_refT T; is_refT U \<rbrakk> 
  \<Longrightarrow> P,E \<turnstile>c e instanceof U ::Boolean"

| WTVal_code1: "P,E \<turnstile>c Val (Intg i) :: Integer" -- new
| WTVal_code2: "P,E \<turnstile>c Val (Bool b) :: Boolean" -- new 
| WTVal_code3: "P,E \<turnstile>c null :: NT" -- new 
| WTVal_code4: "P,E \<turnstile>c unit :: Void" -- new

| WTVar_code: "E V \<noteq> None \<Longrightarrow> P,E \<turnstile>c Var V :: the (E V)" -- new

| WTBinop_code: "\<lbrakk> P,E \<turnstile> e1 :: T1; P,E \<turnstile> e2 :: T2; P \<turnstile> T1\<guillemotleft>bop\<guillemotright>T2 :: T \<rbrakk> \<Longrightarrow> P,E \<turnstile>c e1\<guillemotleft>bop\<guillemotright>e2 :: T"

| WTLAss_code: "\<lbrakk> E V \<noteq> None; P,E \<turnstile> e :: T'; P \<turnstile> T' \<le> the (E V); V \<noteq> this \<rbrakk> \<Longrightarrow> P,E \<turnstile>c V := e :: Void" -- new

| WTAAcc_code: "\<lbrakk> P,E \<turnstile> a :: T\<lfloor>\<rceil>; P,E \<turnstile> i :: Integer \<rbrakk> \<Longrightarrow> P,E \<turnstile>c a\<lfloor>i\<rceil> :: T"
| WTAAss_code: "\<lbrakk> P,E \<turnstile> a :: T\<lfloor>\<rceil>; P,E \<turnstile> i :: Integer; P,E \<turnstile> e :: T'; P \<turnstile> T' \<le> T \<rbrakk> \<Longrightarrow> P,E \<turnstile>c a\<lfloor>i\<rceil> := e :: Void"
| WTALength_code: "P,E \<turnstile> a :: T\<lfloor>\<rceil> \<Longrightarrow> P,E \<turnstile>c a\<bullet>length :: Integer"
| WTFAcc_code: "\<lbrakk> P,E \<turnstile> e :: Class C;  P \<turnstile> C sees F:T in D \<rbrakk> \<Longrightarrow> P,E \<turnstile>c e\<bullet>F{D} :: T"
| WTFAss_code: "\<lbrakk> P,E \<turnstile> e\<^isub>1 :: Class C;  P \<turnstile> C sees F:T in D;  P,E \<turnstile> e\<^isub>2 :: T'; P \<turnstile> T' \<le> T \<rbrakk> \<Longrightarrow> P,E \<turnstile>c e\<^isub>1\<bullet>F{D}:=e\<^isub>2 :: Void"
| WTCall_code: "\<lbrakk> P,E \<turnstile> e :: Class C; \<not> is_external_call P (Class C) M; P \<turnstile> C sees M:Ts \<rightarrow> T = (pns,body) in D;
     P,E \<turnstile> es [::] Ts'; P \<turnstile> Ts' [\<le>] Ts \<rbrakk> \<Longrightarrow> P,E \<turnstile>c e\<bullet>M(es) :: T"
| WTCall_external_code: "\<lbrakk> P,E \<turnstile> e :: T; P,E \<turnstile> es [::] Ts; P \<turnstile> T\<bullet>M(Ts') :: U; P \<turnstile> Ts [\<le>] Ts' \<rbrakk> \<Longrightarrow> P,E \<turnstile>c e\<bullet>M(es) :: U"

| WTBlock_code: 
  "\<lbrakk> is_type P T; P,E(V \<mapsto> T) \<turnstile> e :: T'; case vo of None \<Rightarrow> True | \<lfloor>v\<rfloor> \<Rightarrow> typeof v \<noteq> None \<and> P \<turnstile> the (typeof v) \<le> T \<rbrakk>
  \<Longrightarrow> P,E \<turnstile>c {V:T=vo; e} :: T'" -- new 

| WTSync_code: "\<lbrakk> P,E \<turnstile> o' :: T; is_refT T; T \<noteq> NT; P,E \<turnstile> e :: T' \<rbrakk> \<Longrightarrow> P,E \<turnstile>c sync(o') e :: T'"
| WTSeq_code: "\<lbrakk> P,E \<turnstile> e\<^isub>1::T\<^isub>1;  P,E \<turnstile> e\<^isub>2::T\<^isub>2 \<rbrakk> \<Longrightarrow> P,E \<turnstile>c e\<^isub>1;;e\<^isub>2 :: T\<^isub>2"

| WTCond_code1:
  "\<lbrakk>P,E \<turnstile> e :: Boolean; P,E \<turnstile> e\<^isub>1 :: T\<^isub>1; P,E \<turnstile> e\<^isub>2 :: T\<^isub>2; P \<turnstile> T\<^isub>1 \<le> T\<^isub>2; P \<turnstile> T\<^isub>2 \<le> T\<^isub>1 \<longrightarrow> T\<^isub>1 = T\<^isub>2 \<rbrakk>
   \<Longrightarrow> P,E \<turnstile>c if (e) e\<^isub>1 else e\<^isub>2 :: T\<^isub>2" -- new 
| WTCond_code2:
  "\<lbrakk>P,E \<turnstile> e :: Boolean; P,E \<turnstile> e\<^isub>1 :: T\<^isub>1; P,E \<turnstile> e\<^isub>2 :: T\<^isub>2; P \<turnstile> T\<^isub>2 \<le> T\<^isub>1; P \<turnstile> T\<^isub>1 \<le> T\<^isub>2 \<longrightarrow> T\<^isub>1 = T\<^isub>2 \<rbrakk>
  \<Longrightarrow> P,E \<turnstile>c if (e) e\<^isub>1 else e\<^isub>2 :: T\<^isub>1" -- new 

| WTWhile_code: "\<lbrakk> P,E \<turnstile> e :: Boolean;  P,E \<turnstile> c::T \<rbrakk> \<Longrightarrow> P,E \<turnstile>c while (e) c :: Void"
| WTThrow_code: "\<lbrakk> P,E \<turnstile> e :: Class C; P \<turnstile> C \<preceq>\<^sup>* Throwable \<rbrakk> \<Longrightarrow> P,E \<turnstile>c throw e :: Void"
| WTTry_code: "\<lbrakk> P,E \<turnstile> e\<^isub>1 :: T;  P,E(V \<mapsto> Class C) \<turnstile> e\<^isub>2 :: T; P \<turnstile> C \<preceq>\<^sup>* Throwable \<rbrakk> \<Longrightarrow> P,E \<turnstile>c try e\<^isub>1 catch(C V) e\<^isub>2 :: T"

lemma WT_code_eq_WT:
  "P,E \<turnstile>c e :: T \<longleftrightarrow> P,E \<turnstile> e :: T"
proof
  assume "P,E \<turnstile>c e :: T"
  thus "P,E \<turnstile> e :: T"
  proof cases
    case WTCall_code thus ?thesis
      by(clarsimp)(rule WTCall)
  qed(auto)
next
  assume "P,E \<turnstile> e :: T"
  thus "P,E \<turnstile>c e :: T"
  proof cases
    case (WTVal v)
    thus ?thesis by(cases v)(auto intro: WT_code.intros)
  next
    case (WTVar V)
    thus ?thesis using WTVar_code[of E V] by auto
  qed(auto intro: WT_code.intros)
qed

lemmas [code_pred_intro] = WT_code.intros[unfolded WT_code_eq_WT] WTNil WTCons

code_pred [detect_switches, skip_proof] WT
proof -
  case WT thus thesis
    by(rule WT_code.cases[unfolded WT_code_eq_WT])(assumption|rule refl)+
next
  case WTs thus thesis
    by(rule WTs.cases)(assumption|rule refl)+
qed
(* FIXME: WT.equation uses widen_i_o_i (which need not terminate) instead of widen_i_i_i *)

text {* Define a function that computes a potential type. *}

primrec WT_code' :: "J_prog \<Rightarrow> env \<Rightarrow> expr \<Rightarrow> ty option"
  and WTs_code' :: "J_prog \<Rightarrow> env \<Rightarrow> expr list \<Rightarrow> ty list option"
where
  "WT_code' P E (new C) = (if is_class P C then Some (Class C) else None)"
| "WT_code' P E (newA T\<lfloor>e\<rceil>) =
  (if is_type P T then (case WT_code' P E e of None \<Rightarrow> None |
                                           Some T' \<Rightarrow> (if T' = Integer then Some (T\<lfloor>\<rceil>) else None))
   else None)"
| "WT_code' P E (Cast U e) =
  (if is_type P U then (case WT_code' P E e of None \<Rightarrow> None |
                                            Some T \<Rightarrow> (if P \<turnstile> U \<le> T \<or> P \<turnstile> T \<le> U then Some U else None)) 
   else None)"
| "WT_code' P E (e instanceof U) =
  (if is_type P U \<and> is_refT U then (case WT_code' P E e of None \<Rightarrow> None |
                                                        Some T \<Rightarrow> (if (P \<turnstile> U \<le> T \<or> P \<turnstile> T \<le> U) \<and> is_refT T
                                                                   then Some Boolean else None))
   else None)"
| "WT_code' P E (Val v) = 
  (case v of Intg i \<Rightarrow> Some Integer | Bool b \<Rightarrow> Some Boolean | Null \<Rightarrow> Some NT | Unit \<Rightarrow> Some Void | Addr a \<Rightarrow> None)"
| "WT_code' P E (Var V) = E V"
| "WT_code' P E (e1 \<guillemotleft>bop\<guillemotright> e2) =
  (case WT_code' P E e1 of None \<Rightarrow> None
                     | Some T1 \<Rightarrow> case WT_code' P E e2 of None \<Rightarrow> None
                                                    | Some T2 \<Rightarrow> let T = WT_binop_i_i_i_i_o P T1 bop T2
                                                                 in (if Predicate.is_empty T then None 
                                                                     else Some (Predicate.the T)))"
| "WT_code' P E (V := e) =
  (if V = this then None 
   else (case E V of None \<Rightarrow> None
                 | Some T \<Rightarrow> case WT_code' P E e of None \<Rightarrow> None | Some T' \<Rightarrow> (if P \<turnstile> T' \<le> T then Some Void else None)))"
| "WT_code' P E (a\<lfloor>i\<rceil>) =
  (case WT_code' P E a of None \<Rightarrow> None
   | Some T \<Rightarrow> case T of Ta\<lfloor>\<rceil> \<Rightarrow> (case WT_code' P E i of None \<Rightarrow> None 
                                                  | Some Ti \<Rightarrow> (if Ti = Integer then Some Ta else None))
                         | _ \<Rightarrow> None)"
| "WT_code' P E (a\<lfloor>i\<rceil> := e) =
  (case WT_code' P E a of None \<Rightarrow> None
   | Some T \<Rightarrow> (case T of Ta\<lfloor>\<rceil> \<Rightarrow> (case WT_code' P E i of None \<Rightarrow> None
                                 | Some Ti \<Rightarrow> (if Ti = Integer then (case WT_code' P E e of None \<Rightarrow> None
                                                                     | Some Te \<Rightarrow> (if P \<turnstile> Te \<le> Ta then Some Void else None))
                                               else None))
                          | _ \<Rightarrow> None))"
| "WT_code' P E (a\<bullet>length) =
  (case WT_code' P E a of None \<Rightarrow> None
   | Some T \<Rightarrow> case T of Ta\<lfloor>\<rceil> \<Rightarrow> Some Integer | _ \<Rightarrow> None)"
| "WT_code' P E (e\<bullet>F{D}) =
  (case WT_code' P E e of None \<Rightarrow> None
  | Some T \<Rightarrow> case T of Class C \<Rightarrow> let Tf = sees_field_i_i_i_o_i P C F D
                                  in (if Predicate.is_empty Tf then None else Some (Predicate.the Tf))
                           | _ \<Rightarrow> None)"
| "WT_code' P E (e\<bullet>F{D} := e') =
  (case WT_code' P E e of None \<Rightarrow> None
  | Some T \<Rightarrow> (case T of Class C \<Rightarrow> let Tf = sees_field_i_i_i_o_i P C F D
                                   in (if Predicate.is_empty Tf then None
                                       else (case WT_code' P E e' of None \<Rightarrow> None
                                             | Some T' \<Rightarrow> (if P \<turnstile> T' \<le> Predicate.the Tf then Some Void else None)))
                            | _ \<Rightarrow> None))"
| "WT_code' P E (e\<bullet>M(es)) =
  (case WT_code' P E e of None \<Rightarrow> None
   | Some T \<Rightarrow> case WTs_code' P E es of None \<Rightarrow> None
               | Some Ts \<Rightarrow> let Text = external_WT_i_i_i_o_o P T M
                            in (if Predicate.is_empty Text 
                                then (case T of Class C \<Rightarrow> (if is_external_call P (Class C) M then None
                                                            else (let see = Method_i_i_i_o_o_o_o P C M
                                                                  in (if Predicate.is_empty see then None
                                                                     else let (Ts', T, meth, D) = Predicate.the see
                                                                          in (if P \<turnstile> Ts [\<le>] Ts' then Some T else None))))
                                                    | _ \<Rightarrow> None)
                                else let (Ts', U) = Predicate.the Text
                                     in if P \<turnstile> Ts [\<le>] Ts' then Some U else None))"
| "WT_code' P E {V:T=vo; e} =
   (if is_type P T
    then (case WT_code' P (E(V \<mapsto> T)) e of None \<Rightarrow> None
          | Some T' \<Rightarrow> (case vo of None \<Rightarrow> Some T'
                              | Some v \<Rightarrow> case typeof v of None \<Rightarrow> None | Some Tv \<Rightarrow> if P \<turnstile> Tv \<le> T then Some T' else None))
    else None)"
| "WT_code' P E (sync\<^bsub>V\<^esub>(e) e') =
  (case WT_code' P E e of None \<Rightarrow> None
   | Some T \<Rightarrow> (if is_refT T \<and> T \<noteq> NT then WT_code' P E e' else None))"
| "WT_code' P E (insync\<^bsub>V\<^esub>(a) e) = None"
| "WT_code' P E (e;;e') = (case WT_code' P E e of None \<Rightarrow> None | Some T \<Rightarrow> WT_code' P E e')"
| "WT_code' P E (if (e) e1 else e2) =
  (case WT_code' P E e of None \<Rightarrow> None
   | Some T \<Rightarrow> (if T = Boolean 
                then (case WT_code' P E e1 of None \<Rightarrow> None
                      | Some T1 \<Rightarrow> case WT_code' P E e2 of None \<Rightarrow> None
                                   | Some T2 \<Rightarrow> if P \<turnstile> T1 \<le> T2 \<and> (P \<turnstile> T2 \<le> T1 \<longrightarrow> T1 = T2) then Some T2
                                                else if P \<turnstile> T2 \<le> T1 \<and> (P \<turnstile> T1 \<le> T2 \<longrightarrow> T1 = T2) then Some T1 else None)
                else None))"
| "WT_code' P E (while (e) c) =
  (case WT_code' P E e of None \<Rightarrow> None
   | Some T \<Rightarrow> if T = Boolean \<and> WT_code' P E c \<noteq> None then Some Void else None)"
| "WT_code' P E (throw e) =
  (case WT_code' P E e of None \<Rightarrow> None
   | Some T \<Rightarrow> case T of Class C \<Rightarrow> if P \<turnstile> C \<preceq>\<^sup>* Throwable then Some Void else None | _ \<Rightarrow> None)"
| "WT_code' P E (try e catch(C V) e') =
  (if P \<turnstile> C \<preceq>\<^sup>* Throwable
   then (case WT_code' P (E(V \<mapsto> Class C)) e' of None \<Rightarrow> None
         | Some T \<Rightarrow> if WT_code' P E e = Some T then Some T else None)
   else None)"
 
| "WTs_code' P E [] = Some []"
| "WTs_code' P E (e # es) =
  (case WT_code' P E e of None \<Rightarrow> None
   | Some T \<Rightarrow> case WTs_code' P E es of None \<Rightarrow> None
               | Some Ts \<Rightarrow> Some (T # Ts))"


lemma WT_imp_WT_code': "P,E \<turnstile> e :: T \<Longrightarrow> WT_code' P E e = Some T"
  and WTs_imp_WTs_code': "P,E \<turnstile> es [::] Ts \<Longrightarrow> WTs_code' P E es = Some Ts"
proof(induct rule: WT_WTs.inducts)
  case (WTBinOp E e1 T1 e2 T2 bop T)
  from `P \<turnstile> T1\<guillemotleft>bop\<guillemotright>T2 :: T`
  have "Predicate.eval (WT_binop_i_i_i_i_o P T1 bop T2) T"
    by(rule WT_binop_i_i_i_i_oI)
  moreover hence "\<not> Predicate.is_empty (WT_binop_i_i_i_i_o P T1 bop T2)"
    by(auto simp add: is_empty_def bot_pred_def)
  ultimately show ?case using WTBinOp
    by(auto elim: WT_binop_i_i_i_i_oE simp add: Predicate.the_def)
next
  case (WTFAcc E e C F T D)
  from `P \<turnstile> C sees F:T in D`
  have "Predicate.eval (sees_field_i_i_i_o_i P C F D) T"
    by(rule sees_field_i_i_i_o_iI)
  moreover hence "\<not> Predicate.is_empty (sees_field_i_i_i_o_i P C F D)"
    by(auto simp add: is_empty_def bot_pred_def)
  ultimately show ?case using WTFAcc
    by(auto elim: sees_field_i_i_i_o_iE simp add: Predicate.the_def dest: sees_field_fun)
next
  case (WTFAss E e C F T D e' T')
  from `P \<turnstile> C sees F:T in D`
  have "Predicate.eval (sees_field_i_i_i_o_i P C F D) T"
    by(rule sees_field_i_i_i_o_iI)
  hence "\<not> Predicate.is_empty (sees_field_i_i_i_o_i P C F D)"
    by(auto simp add: is_empty_def bot_pred_def)
  moreover have "Predicate.the (sees_field_i_i_i_o_i P C F D) = T"
    using `Predicate.eval (sees_field_i_i_i_o_i P C F D) T` `P \<turnstile> C sees F:T in D`
    by(auto simp add: Predicate.the_def dest: sees_field_fun elim: sees_field_i_i_i_o_iE)
  ultimately show ?case using WTFAss by auto
next
  case (WTCall E e C M Ts T pns body D es Ts')
  from `P \<turnstile> C sees M: Ts\<rightarrow>T = (pns, body) in D`
  have sees: "Predicate.eval (Method_i_i_i_o_o_o_o P C M) (Ts, T, (pns, body), D)"
    by(rule Method_i_i_i_o_o_o_oI)
  hence "\<not> Predicate.is_empty (Method_i_i_i_o_o_o_o P C M)"
    by(auto simp add: is_empty_def bot_pred_def)
  moreover have "Predicate.the (Method_i_i_i_o_o_o_o P C M) = (Ts, T, (pns, body), D)"
    using sees `P \<turnstile> C sees M: Ts\<rightarrow>T = (pns, body) in D`
    by(fastsimp simp add: Predicate.the_def dest: sees_method_fun elim: Method_i_i_i_o_o_o_oE)
  moreover from `\<not> is_external_call P (Class C) M`
  have "Predicate.is_empty (external_WT_i_i_i_o_o P (Class C) M)"
    by(auto simp add: is_empty_def bot_pred_def intro!: pred_iffI elim: external_WT_i_i_i_o_oE dest: external_WT_is_external_call)
  ultimately show ?case using WTCall by simp
next
  case (WTExternal E e T es Ts M Ts' U)
  have "Predicate.eval (external_WT_i_i_i_o_o P T M) (Ts', U)"
    using `P \<turnstile> T\<bullet>M(Ts') :: U` by(blast intro: external_WT_i_i_i_o_oI)
  moreover
  hence "\<not> Predicate.is_empty (external_WT_i_i_i_o_o P T M)"
    by(auto simp add: is_empty_def bot_pred_def)
  moreover from `Predicate.eval (external_WT_i_i_i_o_o P T M) (Ts', U)`
  have "The (Predicate.eval (external_WT_i_i_i_o_o P T M)) = (Ts', U)"
    by(auto intro!: the_equality elim: external_WT_i_i_i_o_oE dest: external_WT_determ)
  ultimately show ?case using WTExternal by(auto simp add: Predicate.the_def)
qed(fastsimp simp del: fun_upd_apply split: val.split)+

lemma not_is_emptyE:
  assumes "\<not> Predicate.is_empty P"
  obtains x where "Predicate.eval P x"
using assms
by(fastsimp simp add: Predicate.is_empty_def bot_pred_def intro!: pred_iffI)

lemma WT_code'_imp_WT: "WT_code' P E e = \<lfloor>T\<rfloor> \<Longrightarrow> P,E \<turnstile> e :: T"
  and WTs_code'_imp_WTs: "WTs_code' P E es = \<lfloor>Ts\<rfloor> \<Longrightarrow> P,E \<turnstile> es [::] Ts"
proof(induct e and es arbitrary: E T and E Ts)
  case (BinOp e1 bop e2)
  thus ?case
    apply(auto split: split_if_asm elim!: not_is_emptyE WT_binop_i_i_i_i_oE simp add: Predicate.the_def)
    apply(rule theI2)
    apply(erule WT_binop_i_i_i_i_oI)
    apply(auto elim: WT_binop_i_i_i_i_oE dest: WT_binop_fun)
    done
next
  case AAss thus ?case by(auto split: split_if_asm ty.split_asm)
next
  case (FAcc e F D)
  thus ?case
    apply(auto split: split_if_asm ty.split_asm elim!: not_is_emptyE sees_field_i_i_i_o_iE simp add: Predicate.the_def)
    apply(rule theI2)
    apply(erule sees_field_i_i_i_o_iI)
    apply(auto elim: sees_field_i_i_i_o_iE dest: sees_field_fun)
    done
next
  case (FAss e F D e')
  thus ?case
    apply(auto split: split_if_asm ty.split_asm elim!: not_is_emptyE sees_field_i_i_i_o_iE simp add: Predicate.the_def)
    apply(subgoal_tac "The (Predicate.eval (sees_field_i_i_i_o_i P literal F D)) = x", simp)
    apply(rule the_equality)
    apply(erule sees_field_i_i_i_o_iI)
    apply(auto elim: sees_field_i_i_i_o_iE dest: sees_field_fun)
    done
next
  case (Call e M es)
  thus ?case
    apply(auto split: split_if_asm ty.split_asm elim!: not_is_emptyE Method_i_i_i_o_o_o_oE external_WT_i_i_i_i_oE simp add: split_beta Predicate.the_def)
     apply(rule WTCall)
     apply blast
     apply blast
     apply(rule theI2)
     apply(auto elim!: Method_i_i_i_o_o_o_oE dest: sees_method_fun intro: Method_i_i_i_o_o_o_oI)
    apply(rule theI2)
    apply(auto elim!: external_WT_i_i_i_o_oE dest: external_WT_determ intro!: WTExternal intro: external_WT_i_i_i_o_oI)
    apply(subgoal_tac "The (Predicate.eval (external_WT_i_i_i_o_o P a M)) = (ac, ba)")
     apply simp
    apply(rule the_equality)
     apply(erule external_WT_i_i_i_o_oI)
    apply(auto elim!: external_WT_i_i_i_o_oE dest: external_WT_determ)
    done
next
  case Cond thus ?case
    by(simp split: split_if_asm) fastsimp+
qed(fastsimp split: split_if_asm val.split_asm ty.split_asm)+

lemma WT_eq_WT_code' [code]: "P,E \<turnstile> e :: T \<longleftrightarrow> WT_code' P E e = \<lfloor>T\<rfloor>"
  and WTs_eq_WTs_code' [code]: "P,E \<turnstile> es [::] Ts \<longleftrightarrow> WTs_code' P E es = \<lfloor>Ts\<rfloor>"
by(blast intro: WT_code'_imp_WT WTs_code'_imp_WTs WT_imp_WT_code' WTs_imp_WTs_code')+

lemma WT_i_i_i_o_code [code]:
  "WT_i_i_i_o P E e = (case WT_code' P E e of None \<Rightarrow> bot | Some T \<Rightarrow> Predicate.single T)"
apply(rule pred_iffI)
apply(auto elim!: WT_i_i_i_oE singleE simp add: WT_eq_WT_code' intro: singleI WT_i_i_i_oI )
done

lemma WT_i_i_i_i_code [code]:
  "WT_i_i_i_i P E e T = (if WT_code' P E e = Some T then Predicate.single () else bot)"
apply(rule pred_iffI)
apply(auto elim!: WT_i_i_i_iE intro: singleI WT_i_i_i_iI simp add: WT_eq_WT_code' split: split_if_asm)
done

end
