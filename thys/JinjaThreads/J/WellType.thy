(*  Title:      JinjaThreads/J/WellType.thy
    Author:     Tobias Nipkow, Andreas Lochbihler
*)

header {* \isaheader{Well-typedness of Jinja expressions} *}

theory WellType imports
  Expr
  State
  "../Common/ExternalCall"
  "../Common/WellForm"
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
  "\<lbrakk> P,E \<turnstile> e :: Class C;  P \<turnstile> C sees F:T (fm) in D \<rbrakk>
  \<Longrightarrow> P,E \<turnstile> e\<bullet>F{D} :: T"

| WTFAss:
  "\<lbrakk> P,E \<turnstile> e\<^isub>1 :: Class C;  P \<turnstile> C sees F:T (fm) in D;  P,E \<turnstile> e\<^isub>2 :: T';  P \<turnstile> T' \<le> T \<rbrakk>
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
  "\<lbrakk> P,E \<turnstile> e :: Boolean;  P,E \<turnstile> e\<^isub>1::T\<^isub>1;  P,E \<turnstile> e\<^isub>2::T\<^isub>2; P \<turnstile> lub(T\<^isub>1, T\<^isub>2) = T \<rbrakk>
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

inductive_simps WTs_iffs [iff]:
  "P,E \<turnstile> [] [::] Ts"
  "P,E \<turnstile> e#es [::] T#Ts"
  "P,E \<turnstile> e#es [::] Ts"

lemma WTs_conv_list_all2: "P,E \<turnstile> es [::] Ts = list_all2 (WT P E) es Ts"
by(induct es arbitrary: Ts)(auto simp add: list_all2_Cons1 elim: WTs.cases)

lemma WTs_append [iff]: "\<And>Ts. (P,E \<turnstile> es\<^isub>1 @ es\<^isub>2 [::] Ts) =
  (\<exists>Ts\<^isub>1 Ts\<^isub>2. Ts = Ts\<^isub>1 @ Ts\<^isub>2 \<and> P,E \<turnstile> es\<^isub>1 [::] Ts\<^isub>1 \<and> P,E \<turnstile> es\<^isub>2[::]Ts\<^isub>2)"
by(auto simp add: WTs_conv_list_all2 list_all2_append1 dest: list_all2_lengthD[symmetric])

inductive_simps WT_iffs [iff]:
  "P,E \<turnstile> Val v :: T"
  "P,E \<turnstile> Var V :: T"
  "P,E \<turnstile> e\<^isub>1;;e\<^isub>2 :: T\<^isub>2"
  "P,E \<turnstile> {V:T=vo; e} :: T'"

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

lemma assumes wf: "wf_prog wfmd P"
  shows WT_unique: "\<lbrakk> P,E \<turnstile> e :: T; P,E \<turnstile> e :: T' \<rbrakk> \<Longrightarrow> T = T'"
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
apply(blast dest: is_lub_unique[OF wf])
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


end
