(*  Title:      JinjaThreads/J/WellTypeRT.thy
    Author:     Tobias Nipkow, Andreas Lochbihler
*)

header {* \isaheader{Runtime Well-typedness} *}

theory WellTypeRT
imports WellType
begin

inductive WTrt :: "J_prog \<Rightarrow> heap \<Rightarrow> env \<Rightarrow> expr \<Rightarrow> ty \<Rightarrow> bool"
  and WTrts :: "J_prog \<Rightarrow> heap \<Rightarrow> env \<Rightarrow> expr list \<Rightarrow> ty list \<Rightarrow> bool"
  for P :: "J_prog" and h :: "heap"
  where

  WTrtNew:
    "is_class P C  \<Longrightarrow> WTrt P h E (new C) (Class C)"

| WTrtNewArray:
    "\<lbrakk> WTrt P h E e Integer; is_type P T \<rbrakk>
    \<Longrightarrow> WTrt P h E (newA T\<lfloor>e\<rceil>) (T\<lfloor>\<rceil>)"

| WTrtCast:
    "\<lbrakk> WTrt P h E e T; is_type P U \<rbrakk> \<Longrightarrow> WTrt P h E (Cast U e) U"

| WTrtVal:
    "typeof\<^bsub>h\<^esub> v = Some T \<Longrightarrow> WTrt P h E (Val v) T"

| WTrtVar:
    "E V = Some T  \<Longrightarrow> WTrt P h E (Var V) T"

| WTrtBinOpEq:
    "\<lbrakk> WTrt P h E e1 T1; WTrt P h E e2 T2 \<rbrakk>
    \<Longrightarrow> WTrt P h E (e1 \<guillemotleft>Eq\<guillemotright> e2) Boolean"

| WTrtBinOpAdd:
    "\<lbrakk> WTrt P h E e1 Integer; WTrt P h E e2 Integer \<rbrakk>
  \<Longrightarrow> WTrt P h E (e1 \<guillemotleft>Add\<guillemotright> e2) Integer"

| WTrtLAss:
    "\<lbrakk> E V = Some T; WTrt P h E e T'; P \<turnstile> T' \<le> T \<rbrakk>
     \<Longrightarrow> WTrt P h E (V:=e) Void"

| WTrtAAcc:
    "\<lbrakk> WTrt P h E a (T\<lfloor>\<rceil>); WTrt P h E i Integer \<rbrakk>
    \<Longrightarrow> WTrt P h E (a\<lfloor>i\<rceil>) T"

| WTrtAAccNT:
    "\<lbrakk> WTrt P h E a NT; WTrt P h E i Integer \<rbrakk>
    \<Longrightarrow> WTrt P h E (a\<lfloor>i\<rceil>) T"

| WTrtAAss:
    "\<lbrakk>  WTrt P h E a (T\<lfloor>\<rceil>); WTrt P h E i Integer; WTrt P h E e T' \<rbrakk>
    \<Longrightarrow> WTrt P h E (a\<lfloor>i\<rceil> := e) Void"

| WTrtAAssNT:
    "\<lbrakk>  WTrt P h E a NT; WTrt P h E i Integer; WTrt P h E e T' \<rbrakk>
    \<Longrightarrow> WTrt P h E (a\<lfloor>i\<rceil> := e) Void"

| WTrtALength:
  "WTrt P h E a (T\<lfloor>\<rceil>) \<Longrightarrow> WTrt P h E (a\<bullet>length) Integer"

| WTrtALengthNT:
  "WTrt P h E a NT \<Longrightarrow> WTrt P h E (a\<bullet>length) T"

| WTrtFAcc:
    "\<lbrakk> WTrt P h E e (Class C); P \<turnstile> C has F:T in D \<rbrakk> \<Longrightarrow>
    WTrt P h E (e\<bullet>F{D}) T"

| WTrtFAccNT:
    "WTrt P h E e NT \<Longrightarrow> WTrt P h E (e\<bullet>F{D}) T"

| WTrtFAss:
    "\<lbrakk> WTrt P h E e1 (Class C);  P \<turnstile> C has F:T in D; WTrt P h E e2 T2;  P \<turnstile> T2 \<le> T \<rbrakk>
    \<Longrightarrow> WTrt P h E (e1\<bullet>F{D}:=e2) Void"

| WTrtFAssNT:
    "\<lbrakk> WTrt P h E e1 NT; WTrt P h E e2 T2 \<rbrakk>
    \<Longrightarrow> WTrt P h E (e1\<bullet>F{D}:=e2) Void"

| WTrtCall:
    "\<lbrakk> WTrt P h E e (Class C); \<not> is_external_call P (Class C) M (length es); P \<turnstile> C sees M:Ts \<rightarrow> T = (pns,body) in D;
       WTrts P h E es Ts'; P \<turnstile> Ts' [\<le>] Ts \<rbrakk>
    \<Longrightarrow> WTrt P h E (e\<bullet>M(es)) T"

| WTrtCallNT:
    "\<lbrakk> WTrt P h E e NT; WTrts P h E es Ts \<rbrakk>
    \<Longrightarrow> WTrt P h E (e\<bullet>M(es)) T"

| WTrtCallExternal:
    "\<lbrakk> WTrt P h E e T; WTrts P h E es Ts; P \<turnstile> T\<bullet>M(Ts) :: U \<rbrakk>
    \<Longrightarrow> WTrt P h E (e\<bullet>M(es)) U"

| WTrtBlock:
    "\<lbrakk> WTrt P h (E(V\<mapsto>T)) e T'; case vo of None \<Rightarrow> True | \<lfloor>v\<rfloor> \<Rightarrow> \<exists>T'. typeof\<^bsub>h\<^esub> v = \<lfloor>T'\<rfloor> \<and> P \<turnstile> T' \<le> T \<rbrakk>
  \<Longrightarrow> WTrt P h E {V:T=vo; e}\<^bsub>cr\<^esub> T'"

| WTrtSynchronized:
    "\<lbrakk> WTrt P h E o' T; is_refT T; T \<noteq> NT; WTrt P h E e T' \<rbrakk>
    \<Longrightarrow> WTrt P h E (sync(o') e) T'"

| WTrtSynchronizedNT:
    "\<lbrakk> WTrt P h E o' NT; WTrt P h E e T \<rbrakk>
    \<Longrightarrow> WTrt P h E (sync(o') e) T'"

| WTrtInSynchronized:
    "\<lbrakk> WTrt P h E (addr a) T; WTrt P h E e T' \<rbrakk>
    \<Longrightarrow> WTrt P h E (insync(a) e) T'"

| WTrtSeq:
    "\<lbrakk> WTrt P h E e1 T1; WTrt P h E e2 T2 \<rbrakk>
    \<Longrightarrow> WTrt P h E (e1;;e2) T2"

| WTrtCond:
    "\<lbrakk> WTrt P h E e Boolean; WTrt P h E e1 T1; WTrt P h E e2 T2; 
       P \<turnstile> T1 \<le> T2 \<or> P \<turnstile> T2 \<le> T1; P \<turnstile> T1 \<le> T2 \<longrightarrow> T = T2; P \<turnstile> T2 \<le> T1 \<longrightarrow> T = T1 \<rbrakk>
    \<Longrightarrow> WTrt P h E (if (e) e1 else e2) T"

| WTrtWhile:
    "\<lbrakk> WTrt P h E e Boolean; WTrt P h E c T \<rbrakk>
    \<Longrightarrow> WTrt P h E (while(e) c) Void"

| WTrtThrow:
    "\<lbrakk> WTrt P h E e T; P \<turnstile> T \<le> Class Throwable \<rbrakk>
    \<Longrightarrow> WTrt P h E (throw e) T'"

| WTrtTry:
    "\<lbrakk> WTrt P h E e1 T1; WTrt P h (E(V \<mapsto> Class C)) e2 T2; P \<turnstile> T1 \<le> T2 \<rbrakk>
    \<Longrightarrow> WTrt P h E (try e1 catch(C V) e2) T2"

| WTrtNil: "WTrts P h E [] []"

| WTrtCons: "\<lbrakk> WTrt P h E e T; WTrts P h E es Ts \<rbrakk> \<Longrightarrow> WTrts P h E (e # es) (T # Ts)"

abbreviation
  WTrt_syntax :: "J_prog \<Rightarrow> env \<Rightarrow> heap \<Rightarrow> expr \<Rightarrow> ty \<Rightarrow> bool" ("_,_,_ \<turnstile> _ : _"   [51,51,51]50)
where
  "P,E,h \<turnstile> e : T \<equiv> WTrt P h E e T"

abbreviation
  WTrts_syntax :: "J_prog \<Rightarrow> env \<Rightarrow> heap \<Rightarrow> expr list \<Rightarrow> ty list \<Rightarrow> bool" ("_,_,_ \<turnstile> _ [:] _"   [51,51,51]50)
where
  "P,E,h \<turnstile> es [:] Ts \<equiv> WTrts P h E es Ts"

declare WTrt_WTrts.intros[intro!]
declare
  WTrtFAcc[rule del] WTrtFAccNT[rule del]
  WTrtFAss[rule del] WTrtFAssNT[rule del]
  WTrtCall[rule del] WTrtCallNT[rule del]
  WTrtCallExternal[rule del]
  WTrtAAcc[rule del, intro] WTrtAAccNT[rule del, intro]
  WTrtAAss[rule del, intro] WTrtAAssNT[rule del, intro]
  WTrtALength[rule del, intro] WTrtALengthNT[rule del, intro]
  WTrtSynchronized[rule del, intro] WTrtSynchronizedNT[rule del, intro]

subsection{*Easy consequences*}

lemma [iff]: "(P,E,h \<turnstile> [] [:] Ts) = (Ts = [])"
by (auto elim: WTrts.cases)

lemma [iff]: "(P,E,h \<turnstile> e#es [:] T#Ts) = (P,E,h \<turnstile> e : T \<and> P,E,h \<turnstile> es [:] Ts)"
by (auto elim: WTrts.cases)

lemma WTrts_conv_list_all2: "P,E,h \<turnstile> es [:] Ts = list_all2 (WTrt P h E) es Ts"
by(induct es arbitrary: Ts)(auto simp add: list_all2_Cons1 elim: WTrts.cases)

lemma [iff]: "(P,E,h \<turnstile> (e#es) [:] Ts) =
  (\<exists>U Us. Ts = U#Us \<and> P,E,h \<turnstile> e : U \<and> P,E,h \<turnstile> es [:] Us)"
by(auto simp add: WTrts_conv_list_all2 list_all2_Cons1)

lemma [simp]: "(P,E,h \<turnstile> es\<^isub>1 @ es\<^isub>2 [:] Ts) =
  (\<exists>Ts\<^isub>1 Ts\<^isub>2. Ts = Ts\<^isub>1 @ Ts\<^isub>2 \<and> P,E,h \<turnstile> es\<^isub>1 [:] Ts\<^isub>1 & P,E,h \<turnstile> es\<^isub>2[:]Ts\<^isub>2)"
by(auto simp add: WTrts_conv_list_all2 list_all2_append1 dest: list_all2_lengthD[symmetric])

lemma [iff]: "P,E,h \<turnstile> Val v : T = (typeof\<^bsub>h\<^esub> v = Some T)"
proof
  assume "P,E,h \<turnstile> Val v : T"
  thus "typeof\<^bsub>h\<^esub> v = Some T" by - (erule WTrt.cases, auto)
next
  assume "typeof\<^bsub>h\<^esub> v = \<lfloor>T\<rfloor>"
  thus "P,E,h \<turnstile> Val v : T" by - (rule WTrtVal)
qed

lemma [iff]: "P,E,h \<turnstile> Var v : T = (E v = Some T)"
by (auto elim: WTrt.cases)

lemma [iff]: "P,E,h \<turnstile> e\<^isub>1;;e\<^isub>2 : T\<^isub>2 = (\<exists>T\<^isub>1. P,E,h \<turnstile> e\<^isub>1:T\<^isub>1 \<and> P,E,h \<turnstile> e\<^isub>2:T\<^isub>2)"
by (auto elim: WTrt.cases)

lemma [iff]: "P,E,h \<turnstile> {V:T=vo; e}\<^bsub>cr\<^esub> : T'  =  (P,E(V\<mapsto>T),h \<turnstile> e : T' \<and> (case vo of None \<Rightarrow> True | \<lfloor>v\<rfloor> \<Rightarrow> \<exists>T'. typeof\<^bsub>h\<^esub> v = \<lfloor>T'\<rfloor> \<and> P \<turnstile> T' \<le> T))"
by (auto elim: WTrt.cases)

inductive_cases WTrt_elim_cases[elim!]:
  "P,E,h \<turnstile> newA T\<lfloor>i\<rceil> : U"
  "P,E,h \<turnstile> v :=e : T"
  "P,E,h \<turnstile> if (e) e\<^isub>1 else e\<^isub>2 : T"
  "P,E,h \<turnstile> while(e) c : T"
  "P,E,h \<turnstile> throw e : T"
  "P,E,h \<turnstile> try e\<^isub>1 catch(C V) e\<^isub>2 : T"
  "P,E,h \<turnstile> Cast D e : T"
  "P,E,h \<turnstile> a\<lfloor>i\<rceil> : T"
  "P,E,h \<turnstile> a\<lfloor>i\<rceil> := e : T"
  "P,E,h \<turnstile> a\<bullet>length : T"
  "P,E,h \<turnstile> e\<bullet>F{D} : T"
  "P,E,h \<turnstile> e\<bullet>F{D} := v : T"
  "P,E,h \<turnstile> e\<^isub>1 \<guillemotleft>bop\<guillemotright> e\<^isub>2 : T"
  "P,E,h \<turnstile> new C : T"
  "P,E,h \<turnstile> e\<bullet>M(es) : T"
  "P,E,h \<turnstile> sync(o') e : T"
  "P,E,h \<turnstile> insync(a) e : T"

subsection{*Some interesting lemmas*}

lemma WTrts_Val[simp]:
 "P,E,h \<turnstile> map Val vs [:] Ts \<longleftrightarrow> map (typeof\<^bsub>h\<^esub>) vs = map Some Ts"
apply(induct vs arbitrary: Ts)
 apply simp
apply(case_tac Ts)
 apply simp
apply simp
done

lemma WTrt_env_mono: "P,E,h \<turnstile> e : T \<Longrightarrow> (\<And>E'. E \<subseteq>\<^sub>m E' \<Longrightarrow> P,E',h \<turnstile> e : T)"
  and WTrts_env_mono: "P,E,h \<turnstile> es [:] Ts \<Longrightarrow> (\<And>E'. E \<subseteq>\<^sub>m E' \<Longrightarrow> P,E',h \<turnstile> es [:] Ts)"
apply(induct rule: WTrt_WTrts.inducts)
apply(simp add: WTrtNew)
apply(fastsimp simp: WTrtNewArray)
apply(fastsimp simp: WTrtCast)
apply(fastsimp simp: WTrtVal)
apply(simp add: WTrtVar map_le_def dom_def)
apply(fastsimp simp add: WTrtBinOpEq)
apply(fastsimp simp add: WTrtBinOpAdd)
apply(force simp: map_le_def)
apply(force simp: WTrtAAcc)
apply(force simp: WTrtAAccNT)
apply(rule WTrtAAss, fastsimp, blast, blast)
apply(fastsimp)
apply(rule WTrtALength, blast)
apply(blast)
apply(fastsimp simp: WTrtFAcc)
apply(simp add: WTrtFAccNT)
apply(fastsimp simp: WTrtFAss)
apply(fastsimp simp: WTrtFAssNT)
apply(fastsimp simp: WTrtCall)
apply(fastsimp simp: WTrtCallNT)
apply(fastsimp intro: WTrtCallExternal)
apply(fastsimp simp: map_le_def)
apply(rule WTrtSynchronized)
  apply(blast)
 apply(assumption)
apply(fastsimp)
apply(fastsimp intro: WTrtInSynchronized)
apply(fastsimp)
apply(fastsimp)
apply(fastsimp simp: WTrtSeq)
apply(fastsimp simp: WTrtCond)
apply(fastsimp simp: WTrtWhile)
apply(fastsimp simp: WTrtThrow)
apply(auto simp: WTrtTry map_le_def dom_def)
done



lemma WTrt_hext_mono: "P,E,h \<turnstile> e : T \<Longrightarrow> h \<unlhd> h' \<Longrightarrow> P,E,h' \<turnstile> e : T"
  and WTrts_hext_mono: "P,E,h \<turnstile> es [:] Ts \<Longrightarrow> h \<unlhd> h' \<Longrightarrow> P,E,h' \<turnstile> es [:] Ts"
apply(induct rule: WTrt_WTrts.inducts)
apply(simp add: WTrtNew)
apply(fastsimp simp: WTrtNewArray)
apply(fastsimp simp: WTrtCast)
apply(fastsimp simp: WTrtVal dest:hext_typeof_mono)
apply(simp add: WTrtVar)
apply(fastsimp simp add: WTrtBinOpEq)
apply(fastsimp simp add: WTrtBinOpAdd)
apply(fastsimp simp add: WTrtLAss)
apply(rule WTrtAAcc)
  apply(simp)
 apply(simp)
apply(rule WTrtAAccNT)
  apply(simp)
 apply(simp)
apply(rule WTrtAAss)
   apply(simp)
  apply(simp)
 apply(simp)
apply(simp)
apply(rule WTrtAAssNT)
  apply(simp)
 apply(simp)
apply(simp)
apply(rule WTrtALength, blast)
apply(rule WTrtALengthNT, blast)
apply(fast intro: WTrtFAcc)
apply(simp add: WTrtFAccNT)
apply(fastsimp simp: WTrtFAss del:WTrt_WTrts.intros WTrt_elim_cases)
apply(fastsimp simp: WTrtFAssNT)
apply(fastsimp simp: WTrtCall)
apply(fastsimp simp: WTrtCallNT)
apply(fastsimp intro: WTrtCallExternal)
apply(fastsimp intro: hext_typeof_mono)
apply(rule WTrtSynchronized)
  apply(blast)
 apply(assumption)
apply(fastsimp)
apply(fastsimp)
apply(fastsimp)
apply(fastsimp intro: WTrtInSynchronized)
apply(fastsimp simp add: WTrtSeq)
apply(fastsimp simp add: WTrtCond)
apply(fastsimp simp add: WTrtWhile)
apply(fastsimp simp add: WTrtThrow)
apply(fastsimp simp: WTrtTry)
apply(fastsimp)+
done


lemma WT_implies_WTrt: "P,E \<turnstile> e :: T \<Longrightarrow> P,E,h \<turnstile> e : T"
  and WTs_implies_WTrts: "P,E \<turnstile> es [::] Ts \<Longrightarrow> P,E,h \<turnstile> es [:] Ts"
apply(induct rule: WT_WTs.inducts)
apply fast
apply fast
apply fast
apply(fastsimp dest:typeof_lit_typeof)
apply(simp)
apply(fastsimp)
apply(fastsimp)
apply(fastsimp)
apply(erule WTrtAAcc)
apply(assumption)
apply(erule WTrtAAss)
apply(assumption)+
apply(erule WTrtALength)
apply(fastsimp simp: WTrtFAcc has_visible_field)
apply(fastsimp simp: WTrtFAss dest: has_visible_field)
apply(fastsimp simp: WTrtCall)
apply(fastsimp intro: WTrtCallExternal)
apply(clarsimp simp del: fun_upd_apply, blast intro: typeof_lit_typeof)
apply(erule WTrtSynchronized)
 apply(assumption)+
apply(fastsimp)
apply(fastsimp)
apply(fastsimp)
apply(fastsimp)
apply(fastsimp)
apply(fastsimp)
apply(fastsimp)
done



end
