(*  Title:      Jinja/J/WellTypeRT.thy
    Author:     Tobias Nipkow, Andreas Lochbihler

    Based on the Jinja theory J/WellTypeRT by Tobias Nipkow
*)

header {* \isaheader{Runtime Well-typedness} *}

theory WellTypeRT
imports WellType
begin

lemma WTrtCall_mono:
  "(\<And>E e T. A E e T \<longrightarrow> B E e T) \<Longrightarrow> list_all2 (\<lambda>e T. A E e T) es Ts' \<longrightarrow> list_all2 (\<lambda>e T. B E e T) es Ts'"
apply(rule impI)
apply(erule list_all2_mono)
apply(auto)
done

inductive WTrt :: "J_prog \<Rightarrow> heap \<Rightarrow> env \<Rightarrow> expr \<Rightarrow> ty \<Rightarrow> bool"
  for P :: "J_prog" and h :: "heap" where
  WTrtNew:
    "is_class P C  \<Longrightarrow> WTrt P h E (new C) (Class C)"

| WTrtNewArray:
    "\<lbrakk> WTrt P h E e Integer; is_type P T \<rbrakk>
    \<Longrightarrow> WTrt P h E (newA T\<lfloor>e\<rceil>) (T\<lfloor>\<rceil>)"

| WTrtCast:
    "WTrt P h E e  T \<Longrightarrow> WTrt P h E (Cast U e) U"

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
    "\<lbrakk> WTrt P h E e (Class C); P \<turnstile> C sees M:Ts \<rightarrow> T = (pns,body) in D;
       list_all2 (WTrt P h E) es Ts'; P \<turnstile> Ts' [\<le>] Ts \<rbrakk>
    \<Longrightarrow> WTrt P h E (e\<bullet>M(es)) T"

| WTrtCallNT:
    "\<lbrakk> WTrt P h E e NT; list_all2 (WTrt P h E) es Ts \<rbrakk>
    \<Longrightarrow> WTrt P h E (e\<bullet>M(es)) T"

| WTrtNewThread:
    "\<lbrakk> WTrt P h E e (Class C); P \<turnstile> C \<preceq>\<^sup>* Thread \<rbrakk>
    \<Longrightarrow> WTrt P h E (e\<bullet>start([])) Void"

| WTrtWait:
    "\<lbrakk> WTrt P h E e T; is_refT T; T \<noteq> NT \<rbrakk>
    \<Longrightarrow> WTrt P h E (e\<bullet>wait([])) Void"

| WTrtNotify:
    "\<lbrakk> WTrt P h E e T; is_refT T; T \<noteq> NT \<rbrakk>
    \<Longrightarrow> WTrt P h E (e\<bullet>notify([])) Void"

| WTrtNotifyAll:
    "\<lbrakk> WTrt P h E e T; is_refT T; T \<noteq> NT \<rbrakk>
    \<Longrightarrow> WTrt P h E (e\<bullet>notifyAll([])) Void"

| WTrtBlock:
    "WTrt P h (E(V\<mapsto>T)) e T' \<Longrightarrow> WTrt P h E {V:T; e} T'"

| WTrtSynchronized:
    "\<lbrakk> WTrt P h E o' T; is_refT T; T \<noteq> NT; WTrt P h E e T' \<rbrakk>
    \<Longrightarrow> WTrt P h E (sync(o') e) T'"

| WTrtSynchronizedNT:
    "\<lbrakk> WTrt P h E o' NT; WTrt P h E e T \<rbrakk>
    \<Longrightarrow> WTrt P h E (sync(o') e) T'"

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
    "\<lbrakk> WTrt P h E e T; is_refT_class T; T \<noteq> Class Object \<rbrakk>
    \<Longrightarrow> WTrt P h E (throw e) T'"

| WTrtTry:
    "\<lbrakk> WTrt P h E e1 T1; WTrt P h (E(V \<mapsto> Class C)) e2 T2; P \<turnstile> T1 \<le> T2 \<rbrakk>
    \<Longrightarrow> WTrt P h E (try e1 catch(C V) e2) T2"
monos WTrtCall_mono

abbreviation
  WTrt_syntax :: "J_prog \<Rightarrow> env \<Rightarrow> heap \<Rightarrow> expr \<Rightarrow> ty \<Rightarrow> bool" ("_,_,_ \<turnstile> _ : _"   [51,51,51]50)
where
  "P,E,h \<turnstile> e : T \<equiv> WTrt P h E e T"

declare WTrt.intros[intro!]
declare
  WTrtFAcc[rule del] WTrtFAccNT[rule del]
  WTrtFAss[rule del] WTrtFAssNT[rule del]
  WTrtCall[rule del] WTrtCallNT[rule del]
  WTrtNewThread[rule del]
  WTrtWait[rule del]
  WTrtNotify[rule del]
  WTrtNotifyAll[rule del]

subsection{*Easy consequences*}

lemma [iff]: "P,E,h \<turnstile> Val v : T = (typeof\<^bsub>h\<^esub> v = Some T)"
proof
  assume "P,E,h \<turnstile> Val v : T"
  thus "typeof\<^bsub>h\<^esub> v = Some T" by - (erule WTrt.cases, auto)
next
  assume "typeof\<^bsub>h\<^esub> v = \<lfloor>T\<rfloor>"
  thus "P,E,h \<turnstile> Val v : T" by - (rule WTrtVal)
qed

lemma [iff]: "P,E,h \<turnstile> Var v : T = (E v = Some T)"
(*<*)
apply(rule iffI)
apply (auto elim: WTrt.cases)
done
(*>*)

lemma [iff]: "P,E,h \<turnstile> e\<^isub>1;;e\<^isub>2 : T\<^isub>2 = (\<exists>T\<^isub>1. P,E,h \<turnstile> e\<^isub>1:T\<^isub>1 \<and> P,E,h \<turnstile> e\<^isub>2:T\<^isub>2)"
(*<*)
apply(rule iffI)
apply (auto elim: WTrt.cases)
done
(*>*)

lemma [iff]: "P,E,h \<turnstile> {V:T; e} : T'  =  (P,E(V\<mapsto>T),h \<turnstile> e : T')"
(*<*)
apply(rule iffI)
apply (auto elim: WTrt.cases)
done
(*>*)

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
  "P,E,h \<turnstile> e\<bullet>F{D} : T"
  "P,E,h \<turnstile> e\<bullet>F{D} := v : T"
  "P,E,h \<turnstile> e\<^isub>1 \<guillemotleft>bop\<guillemotright> e\<^isub>2 : T"
  "P,E,h \<turnstile> new C : T"
  "P,E,h \<turnstile> e\<bullet>start([]) : T"
  "P,E,h \<turnstile> e\<bullet>wait([]) : T"
  "P,E,h \<turnstile> e\<bullet>notify([]) : T"
  "P,E,h \<turnstile> e\<bullet>notifyAll([]) : T"
  "P,E,h \<turnstile> e\<bullet>M(es) : T"
  "P,E,h \<turnstile> sync(o') e : T"

subsection{*Some interesting lemmas*}

lemma WTrts_Val[simp]:
 "(list_all2 (\<lambda>e T. P,E,h \<turnstile> e : T) (map Val vs) Ts) = (map (typeof\<^bsub>h\<^esub>) vs = map Some Ts)"
apply(induct vs arbitrary: Ts)
 apply simp
apply(case_tac Ts)
 apply simp
apply simp
done

lemma WTrt_env_mono:
  "P,E,h \<turnstile> e : T \<Longrightarrow> (\<And>E'. E \<subseteq>\<^sub>m E' \<Longrightarrow> P,E',h \<turnstile> e : T)"
apply(induct rule: WTrt.induct)
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
apply(rule WTrtAAss)
apply(fastsimp)+
apply(fastsimp simp: WTrtFAcc)
apply(simp add: WTrtFAccNT)
apply(fastsimp simp: WTrtFAss)
apply(fastsimp simp: WTrtFAssNT)
apply(rule WTrtCall)
   apply(blast)
  apply(assumption)
 apply(erule list_all2_mono)
 apply(blast)
apply(assumption)
apply(rule WTrtCallNT)
 apply(blast)
apply(erule list_all2_mono)
apply(blast)
apply(fastsimp intro: WTrtNewThread)
apply(fastsimp intro: WTrtWait)
apply(fastsimp intro: WTrtNotify)
apply(fastsimp intro: WTrtNotifyAll)
apply(fastsimp simp: map_le_def)
apply(rule WTrtSynchronized)
  apply(blast)
 apply(assumption)
apply(fastsimp)
apply(fastsimp)
apply(fastsimp)
apply(fastsimp simp: WTrtSeq)
apply(fastsimp simp: WTrtCond)
apply(fastsimp simp: WTrtWhile)
apply(fastsimp simp: WTrtThrow)
apply(auto simp: WTrtTry map_le_def dom_def)
done
(*>*)


lemma WTrt_hext_mono: "P,E,h \<turnstile> e : T \<Longrightarrow> h \<unlhd> h' \<Longrightarrow> P,E,h' \<turnstile> e : T"
apply(induct rule: WTrt.induct)
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
apply(fast intro: WTrtFAcc)
apply(simp add: WTrtFAccNT)
apply(fastsimp simp: WTrtFAss del:WTrt.intros WTrt_elim_cases)
apply(fastsimp simp: WTrtFAssNT)
apply(rule WTrtCall)
   apply(blast)
  apply(assumption)
 apply(erule list_all2_mono)
 apply(blast)
apply(assumption) 
apply(rule WTrtCallNT)
 apply(blast)
apply(erule list_all2_mono)
apply(blast)
apply(fastsimp intro: WTrtNewThread)
apply(fastsimp intro: WTrtWait)
apply(fastsimp intro: WTrtNotify)
apply(fastsimp intro: WTrtNotifyAll)
apply(fastsimp)
apply(rule WTrtSynchronized)
  apply(blast)
 apply(assumption)
apply(fastsimp)
apply(fastsimp)
apply(fastsimp)
apply(fastsimp simp add: WTrtSeq)
apply(fastsimp simp add: WTrtCond)
apply(fastsimp simp add: WTrtWhile)
apply(fastsimp simp add: WTrtThrow)
apply(fastsimp simp: WTrtTry)
done
(*>*)

lemma WT_implies_WTrt: "P,E \<turnstile> e :: T \<Longrightarrow> P,E,h \<turnstile> e : T"
apply(induct rule: WT.induct)
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
apply(fastsimp simp: WTrtFAcc has_visible_field)
apply(fastsimp simp: WTrtFAss dest: has_visible_field)
apply(erule WTrtCall)
  apply(assumption)
 apply(erule list_all2_mono)
 apply(clarify)
apply(assumption)
apply(fastsimp intro: WTrtNewThread)
apply(fastsimp intro: WTrtWait)
apply(fastsimp intro: WTrtNotify)
apply(fastsimp intro: WTrtNotifyAll)
apply(fastsimp)
apply(erule WTrtSynchronized)
 apply(assumption)+
apply(fastsimp)
apply(fastsimp)
apply(fastsimp)
apply(fastsimp)
apply(fastsimp)
done
(*>*)


end
