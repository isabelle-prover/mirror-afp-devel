(*  Title:      Jinja/J/WellType.thy
    Author:     Tobias Nipkow, Andreas Lochbihler

    Based on the Jinja theory J/WellType by Tobias Nipkow
*)

header {* \isaheader{Well-typedness of Jinja expressions} *}

theory WellType
imports "../Common/Objects" Expr
begin

types 
  env  = "vname \<rightharpoonup> ty"

lemma WTCall_mono:
  "(\<And>E e T. A E e T \<longrightarrow> B E e T) \<Longrightarrow> list_all2 (\<lambda>e T. A E e T) es Ts' \<longrightarrow> list_all2 (\<lambda>e T. B E e T) es Ts'"
apply(rule impI)
apply(erule list_all2_mono)
apply(auto)
done

inductive WT :: "J_prog \<Rightarrow> env \<Rightarrow> expr \<Rightarrow> ty \<Rightarrow> bool" ("_,_ \<turnstile> _ :: _"   [51,51,51]50)
  for P :: "J_prog" where
WTNew:
  "is_class P C  \<Longrightarrow>
  P,E \<turnstile> new C :: Class C"

| WTNewArray:
  "\<lbrakk> P,E \<turnstile> e :: Integer; is_type P T \<rbrakk> \<Longrightarrow>
  P,E \<turnstile> newA T\<lfloor>e\<rceil> :: T\<lfloor>\<rceil>"

| WTCast:
  "\<lbrakk> P,E \<turnstile> e :: T; P \<turnstile> U \<le> T \<or> P \<turnstile> T \<le> U \<rbrakk>
  \<Longrightarrow> P,E \<turnstile> Cast U e :: U"

| WTVal:
  "typeof v = Some T \<Longrightarrow>
  P,E \<turnstile> Val v :: T"

| WTVar:
  "E V = Some T \<Longrightarrow>
  P,E \<turnstile> Var V :: T"

| WTBinOpEq:
  "\<lbrakk> P,E \<turnstile> e\<^isub>1 :: T\<^isub>1;  P,E \<turnstile> e\<^isub>2 :: T\<^isub>2; P \<turnstile> T\<^isub>1 \<le> T\<^isub>2 \<or> P \<turnstile> T\<^isub>2 \<le> T\<^isub>1 \<rbrakk>
  \<Longrightarrow> P,E \<turnstile> e\<^isub>1 \<guillemotleft>Eq\<guillemotright> e\<^isub>2 :: Boolean"

| WTBinOpAdd:
  "\<lbrakk> P,E \<turnstile> e\<^isub>1 :: Integer;  P,E \<turnstile> e\<^isub>2 :: Integer \<rbrakk>
  \<Longrightarrow> P,E \<turnstile> e\<^isub>1 \<guillemotleft>Add\<guillemotright> e\<^isub>2 :: Integer"

| WTLAss:
  "\<lbrakk> E V = Some T;  P,E \<turnstile> e :: T';  P \<turnstile> T' \<le> T;  V \<noteq> this \<rbrakk>
  \<Longrightarrow> P,E \<turnstile> V:=e :: Void"

| WTAAcc:
  "\<lbrakk> P,E \<turnstile> a :: T\<lfloor>\<rceil>; P,E \<turnstile> i :: Integer \<rbrakk>
  \<Longrightarrow> P,E \<turnstile> a\<lfloor>i\<rceil> :: T"

| WTAAss:
  "\<lbrakk> P,E \<turnstile> a :: T\<lfloor>\<rceil>; P,E \<turnstile> i :: Integer; P,E \<turnstile> e :: T'; P \<turnstile> T' \<le> T \<rbrakk>
  \<Longrightarrow> P,E \<turnstile> a\<lfloor>i\<rceil> := e :: Void"

| WTFAcc:
  "\<lbrakk> P,E \<turnstile> e :: Class C;  P \<turnstile> C sees F:T in D \<rbrakk>
  \<Longrightarrow> P,E \<turnstile> e\<bullet>F{D} :: T"

| WTFAss:
  "\<lbrakk> P,E \<turnstile> e\<^isub>1 :: Class C;  P \<turnstile> C sees F:T in D;  P,E \<turnstile> e\<^isub>2 :: T';  P \<turnstile> T' \<le> T \<rbrakk>
  \<Longrightarrow> P,E \<turnstile> e\<^isub>1\<bullet>F{D}:=e\<^isub>2 :: Void"

| WTCall:
  "\<lbrakk> P,E \<turnstile> e :: Class C;  P \<turnstile> C sees M:Ts \<rightarrow> T = (pns,body) in D;
     list_all2 (\<lambda>e T. P,E \<turnstile> e :: T) es Ts';  P \<turnstile> Ts' [\<le>] Ts \<rbrakk>
  \<Longrightarrow> P,E \<turnstile> e\<bullet>M(es) :: T"

| WTNewThread:
  "\<lbrakk> P,E \<turnstile> e :: Class C; P \<turnstile> C \<preceq>\<^sup>* Thread \<rbrakk>
  \<Longrightarrow> P,E \<turnstile> e\<bullet>start([]) :: Void"

| WTWait:
  "\<lbrakk> P,E \<turnstile> e :: T; is_refT T; T \<noteq> NT \<rbrakk>
  \<Longrightarrow> P,E \<turnstile> e\<bullet>wait([]) :: Void"

| WTNotify:
  "\<lbrakk> P,E \<turnstile> e :: T; is_refT T; T \<noteq> NT \<rbrakk>
  \<Longrightarrow> P,E \<turnstile> e\<bullet>notify([]) :: Void"

| WTNotifyAll:
  "\<lbrakk> P,E \<turnstile> e :: T; is_refT T; T \<noteq> NT \<rbrakk>
  \<Longrightarrow> P,E \<turnstile> e\<bullet>notifyAll([]) :: Void"

| WTBlock:
  "\<lbrakk> is_type P T;  P,E(V \<mapsto> T) \<turnstile> e :: T' \<rbrakk>
  \<Longrightarrow>  P,E \<turnstile> {V:T; e} :: T'"

| WTSynchronized:
  "\<lbrakk> P,E \<turnstile> o' :: T; is_refT T; T \<noteq> NT; P,E \<turnstile> e :: T' \<rbrakk>
  \<Longrightarrow> P,E \<turnstile> sync(o') e :: T'"

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
  "\<lbrakk> P,E \<turnstile> e :: Class C; C \<noteq> Object \<rbrakk> \<Longrightarrow> 
  P,E \<turnstile> throw e :: Void"

| WTTry:
  "\<lbrakk> P,E \<turnstile> e\<^isub>1 :: T;  P,E(V \<mapsto> Class C) \<turnstile> e\<^isub>2 :: T; is_class P C \<rbrakk>
  \<Longrightarrow> P,E \<turnstile> try e\<^isub>1 catch(C V) e\<^isub>2 :: T"
monos WTCall_mono

declare WT.intros[intro!]

lemma [iff]: "P,E \<turnstile> Val v :: T = (typeof v = Some T)"
(*<*)
apply(rule iffI)
apply (auto elim: WT.cases)
done
(*>*)

lemma [iff]: "P,E \<turnstile> Var V :: T = (E V = Some T)"
(*<*)
apply(rule iffI)
apply (auto elim: WT.cases)
done
(*>*)

lemma [iff]: "P,E \<turnstile> e\<^isub>1;;e\<^isub>2 :: T\<^isub>2 = (\<exists>T\<^isub>1. P,E \<turnstile> e\<^isub>1::T\<^isub>1 \<and> P,E \<turnstile> e\<^isub>2::T\<^isub>2)"
(*<*)
apply(rule iffI)
apply (auto elim: WT.cases)
done
(*>*)

lemma [iff]: "(P,E \<turnstile> {V:T; e} :: T') = (is_type P T \<and> P,E(V\<mapsto>T) \<turnstile> e :: T')"
(*<*)
apply(rule iffI)
apply (auto elim: WT.cases)
done
(*>*)

(*<*)
inductive_cases WT_elim_cases[elim!]:
  "P,E \<turnstile> V :=e :: T"
  "P,E \<turnstile> sync(o') e :: T"
  "P,E \<turnstile> if (e) e\<^isub>1 else e\<^isub>2 :: T"
  "P,E \<turnstile> while (e) c :: T"
  "P,E \<turnstile> throw e :: T"
  "P,E \<turnstile> try e\<^isub>1 catch(C V) e\<^isub>2 :: T"
  "P,E \<turnstile> Cast D e :: T"
  "P,E \<turnstile> a\<bullet>F{D} :: T"
  "P,E \<turnstile> a\<bullet>F{D} := v :: T"
  "P,E \<turnstile> e\<^isub>1 \<guillemotleft>bop\<guillemotright> e\<^isub>2 :: T"
  "P,E \<turnstile> new C :: T"
  "P,E \<turnstile> newA T\<lfloor>e\<rceil> :: T'"
  "P,E \<turnstile> a\<lfloor>i\<rceil> := e :: T"
  "P,E \<turnstile> a\<lfloor>i\<rceil> :: T"
  "P,E \<turnstile> e\<bullet>start([]) :: T"
  "P,E \<turnstile> e\<bullet>wait([]) :: T"
  "P,E \<turnstile> e\<bullet>notify([]) :: T"
  "P,E \<turnstile> e\<bullet>notifyAll([]) :: T"
  "P,E \<turnstile> e\<bullet>M(ps) :: T"
  "P,E \<turnstile> sync(o') e :: T"
(*>*)


lemma wt_env_mono:
  "P,E \<turnstile> e :: T \<Longrightarrow> (\<And>E'. E \<subseteq>\<^sub>m E' \<Longrightarrow> P,E' \<turnstile> e :: T)"
apply(induct rule: WT.induct)
apply(simp add: WTNew)
apply(simp add: WTNewArray)
apply(fastsimp simp: WTCast)
apply(fastsimp simp: WTVal)
apply(simp add: WTVar map_le_def dom_def)
apply(fastsimp simp: WTBinOpEq)
apply(fastsimp simp: WTBinOpAdd)
apply(force simp:map_le_def)
apply(simp add: WTAAcc)
apply(simp add: WTAAss, fastsimp)
apply(fastsimp simp: WTFAcc)
apply(fastsimp simp: WTFAss del:WT.intros WT_elim_cases)
apply(rule WTCall)
   apply(blast)
  apply(assumption)
 apply(rule list_all2_mono)
  apply(assumption)
 apply(blast)
apply(assumption)
apply(fastsimp)
apply(fastsimp)
apply(fastsimp)
apply(fastsimp)
apply(fastsimp simp: map_le_def WTBlock)
apply(fastsimp simp: WTSynchronized)
apply(fastsimp simp: WTSeq)
apply(fastsimp simp: WTCond)
apply(fastsimp simp: WTWhile)
apply(fastsimp simp: WTThrow)
apply(fastsimp simp: WTTry map_le_def dom_def)
done
(*>*)

lemma WTCall_fv:
  "list_all2 (\<lambda>e T. P,E \<turnstile> e :: T \<and> fv e \<subseteq> dom E) es Ts' \<Longrightarrow> fvs es \<subseteq> dom E"
apply(induct es arbitrary: Ts')
 apply(simp)
apply(auto simp add: list_all2_Cons1)
done

lemma WT_fv: "P,E \<turnstile> e :: T \<Longrightarrow> fv e \<subseteq> dom E"
(*<*)
apply(induct rule:WT.inducts)
apply(simp_all del: fun_upd_apply)
apply fast+
apply(erule WTCall_fv)
apply(fast+)
done

lemma WTs_contains_addrs: "list_all2 (\<lambda>e T. P,E \<turnstile> e :: T \<and> \<not> contains_addr e) es Ts' \<Longrightarrow> \<not> contains_addrs es"
apply(induct es arbitrary: Ts')
by(auto simp add: list_all2_Cons1 list_all2_Cons2 )

lemma WT_contains_addr: "P,E \<turnstile> e :: T \<Longrightarrow> \<not> contains_addr e"
apply(induct rule: WT.induct)
by(auto intro!: WTs_contains_addrs )


end
(*>*)
