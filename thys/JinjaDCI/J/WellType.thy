(*  Title:      JinjaDCI/J/WellType.thy

    Author:     Tobias Nipkow, Susannah Mansky
    Copyright   2003 Technische Universitaet Muenchen, 2019-20 UIUC

    Based on the Jinja theory J/WellType.thy by Tobias Nipkow
*)

section \<open> Well-typedness of Jinja expressions \<close>

theory WellType
imports "../Common/Objects" Expr
begin

type_synonym
  env  = "vname \<rightharpoonup> ty"

inductive
  WT :: "[J_prog,env, expr     , ty     ] \<Rightarrow> bool"
         (\<open>_,_ \<turnstile> _ :: _\<close>   [51,51,51]50)
  and WTs :: "[J_prog,env, expr list, ty list] \<Rightarrow> bool"
         (\<open>_,_ \<turnstile> _ [::] _\<close> [51,51,51]50)
  for P :: J_prog
where
  
  WTNew:
  "is_class P C  \<Longrightarrow>
  P,E \<turnstile> new C :: Class C"

| WTCast:
  "\<lbrakk> P,E \<turnstile> e :: Class D;  is_class P C;  P \<turnstile> C \<preceq>\<^sup>* D \<or> P \<turnstile> D \<preceq>\<^sup>* C \<rbrakk>
  \<Longrightarrow> P,E \<turnstile> Cast C e :: Class C"

| WTVal:
  "typeof v = Some T \<Longrightarrow>
  P,E \<turnstile> Val v :: T"

| WTVar:
  "E V = Some T \<Longrightarrow>
  P,E \<turnstile> Var V :: T"

| WTBinOpEq:
  "\<lbrakk> P,E \<turnstile> e\<^sub>1 :: T\<^sub>1;  P,E \<turnstile> e\<^sub>2 :: T\<^sub>2; P \<turnstile> T\<^sub>1 \<le> T\<^sub>2 \<or> P \<turnstile> T\<^sub>2 \<le> T\<^sub>1 \<rbrakk>
  \<Longrightarrow> P,E \<turnstile> e\<^sub>1 \<guillemotleft>Eq\<guillemotright> e\<^sub>2 :: Boolean"

| WTBinOpAdd:
  "\<lbrakk> P,E \<turnstile> e\<^sub>1 :: Integer;  P,E \<turnstile> e\<^sub>2 :: Integer \<rbrakk>
  \<Longrightarrow> P,E \<turnstile> e\<^sub>1 \<guillemotleft>Add\<guillemotright> e\<^sub>2 :: Integer"

| WTLAss:
  "\<lbrakk> E V = Some T;  P,E \<turnstile> e :: T';  P \<turnstile> T' \<le> T; V \<noteq> this \<rbrakk>
  \<Longrightarrow> P,E \<turnstile> V:=e :: Void"

| WTFAcc:
  "\<lbrakk> P,E \<turnstile> e :: Class C;  P \<turnstile> C sees F,NonStatic:T in D \<rbrakk>
  \<Longrightarrow> P,E \<turnstile> e\<bullet>F{D} :: T"

| WTSFAcc:
  "\<lbrakk> P \<turnstile> C sees F,Static:T in D \<rbrakk>
  \<Longrightarrow> P,E \<turnstile> C\<bullet>\<^sub>sF{D} :: T"

| WTFAss:
  "\<lbrakk> P,E \<turnstile> e\<^sub>1 :: Class C;  P \<turnstile> C sees F,NonStatic:T in D;  P,E \<turnstile> e\<^sub>2 :: T';  P \<turnstile> T' \<le> T \<rbrakk>
  \<Longrightarrow> P,E \<turnstile> e\<^sub>1\<bullet>F{D}:=e\<^sub>2 :: Void"

| WTSFAss:
  "\<lbrakk>  P \<turnstile> C sees F,Static:T in D;  P,E \<turnstile> e\<^sub>2 :: T';  P \<turnstile> T' \<le> T \<rbrakk>
  \<Longrightarrow> P,E \<turnstile> C\<bullet>\<^sub>sF{D}:=e\<^sub>2 :: Void"

| WTCall:
  "\<lbrakk> P,E \<turnstile> e :: Class C;  P \<turnstile> C sees M,NonStatic:Ts \<rightarrow> T = (pns,body) in D;
     P,E \<turnstile> es [::] Ts';  P \<turnstile> Ts' [\<le>] Ts \<rbrakk>
  \<Longrightarrow> P,E \<turnstile> e\<bullet>M(es) :: T"

| WTSCall:
  "\<lbrakk> P \<turnstile> C sees M,Static:Ts \<rightarrow> T = (pns,body) in D;
     P,E \<turnstile> es [::] Ts';  P \<turnstile> Ts' [\<le>] Ts; M \<noteq> clinit \<rbrakk>
  \<Longrightarrow> P,E \<turnstile> C\<bullet>\<^sub>sM(es) :: T"

| WTBlock:
  "\<lbrakk> is_type P T;  P,E(V \<mapsto> T) \<turnstile> e :: T' \<rbrakk>
  \<Longrightarrow>  P,E \<turnstile> {V:T; e} :: T'"

| WTSeq:
  "\<lbrakk> P,E \<turnstile> e\<^sub>1::T\<^sub>1;  P,E \<turnstile> e\<^sub>2::T\<^sub>2 \<rbrakk>
  \<Longrightarrow>  P,E \<turnstile> e\<^sub>1;;e\<^sub>2 :: T\<^sub>2"

| WTCond:
  "\<lbrakk> P,E \<turnstile> e :: Boolean;  P,E \<turnstile> e\<^sub>1::T\<^sub>1;  P,E \<turnstile> e\<^sub>2::T\<^sub>2;
     P \<turnstile> T\<^sub>1 \<le> T\<^sub>2 \<or> P \<turnstile> T\<^sub>2 \<le> T\<^sub>1;  P \<turnstile> T\<^sub>1 \<le> T\<^sub>2 \<longrightarrow> T = T\<^sub>2;  P \<turnstile> T\<^sub>2 \<le> T\<^sub>1 \<longrightarrow> T = T\<^sub>1 \<rbrakk>
  \<Longrightarrow> P,E \<turnstile> if (e) e\<^sub>1 else e\<^sub>2 :: T"

| WTWhile:
  "\<lbrakk> P,E \<turnstile> e :: Boolean;  P,E \<turnstile> c::T \<rbrakk>
  \<Longrightarrow> P,E \<turnstile> while (e) c :: Void"

| WTThrow:
  "P,E \<turnstile> e :: Class C  \<Longrightarrow> 
  P,E \<turnstile> throw e :: Void"

| WTTry:
  "\<lbrakk> P,E \<turnstile> e\<^sub>1 :: T;  P,E(V \<mapsto> Class C) \<turnstile> e\<^sub>2 :: T; is_class P C \<rbrakk>
  \<Longrightarrow> P,E \<turnstile> try e\<^sub>1 catch(C V) e\<^sub>2 :: T"

\<comment> \<open>well-typed expression lists\<close>

| WTNil:
  "P,E \<turnstile> [] [::] []"

| WTCons:
  "\<lbrakk> P,E \<turnstile> e :: T; P,E \<turnstile> es [::] Ts \<rbrakk>
  \<Longrightarrow>  P,E \<turnstile> e#es [::] T#Ts"

(*<*)
declare WT_WTs.intros[intro!] (* WTNil[iff] *)

lemmas WT_WTs_induct = WT_WTs.induct [split_format (complete)]
  and WT_WTs_inducts = WT_WTs.inducts [split_format (complete)]
(*>*)

lemma init_nwt [simp]:"\<not>P,E \<turnstile> INIT C (Cs,b) \<leftarrow> e :: T"
 by(auto elim:WT.cases)
lemma ri_nwt [simp]:"\<not>P,E \<turnstile> RI(C,e);Cs \<leftarrow> e' :: T"
 by(auto elim:WT.cases)

lemma [iff]: "(P,E \<turnstile> [] [::] Ts) = (Ts = [])"
(*<*)by (rule iffI) (auto elim: WTs.cases)(*>*)

lemma [iff]: "(P,E \<turnstile> e#es [::] T#Ts) = (P,E \<turnstile> e :: T \<and> P,E \<turnstile> es [::] Ts)"
(*<*)by (rule iffI) (auto elim: WTs.cases)(*>*)

lemma [iff]: "(P,E \<turnstile> (e#es) [::] Ts) =
  (\<exists>U Us. Ts = U#Us \<and> P,E \<turnstile> e :: U \<and> P,E \<turnstile> es [::] Us)"
(*<*)by (rule iffI) (auto elim: WTs.cases)(*>*)

lemma [iff]: "\<And>Ts. (P,E \<turnstile> es\<^sub>1 @ es\<^sub>2 [::] Ts) =
  (\<exists>Ts\<^sub>1 Ts\<^sub>2. Ts = Ts\<^sub>1 @ Ts\<^sub>2 \<and> P,E \<turnstile> es\<^sub>1 [::] Ts\<^sub>1 \<and> P,E \<turnstile> es\<^sub>2[::]Ts\<^sub>2)"
(*<*)
proof(induct es\<^sub>1 type:list)
  case (Cons a list)
  let ?lhs = "(\<exists>U Us. Ts = U # Us \<and> P,E \<turnstile> a :: U \<and>
        (\<exists>Ts\<^sub>1 Ts\<^sub>2. Us = Ts\<^sub>1 @ Ts\<^sub>2 \<and> P,E \<turnstile> list [::] Ts\<^sub>1 \<and> P,E \<turnstile> es\<^sub>2 [::] Ts\<^sub>2))"
  let ?rhs = "(\<exists>Ts\<^sub>1 Ts\<^sub>2. Ts = Ts\<^sub>1 @ Ts\<^sub>2 \<and>
        (\<exists>U Us. Ts\<^sub>1 = U # Us \<and> P,E \<turnstile> a :: U \<and> P,E \<turnstile> list [::] Us) \<and> P,E \<turnstile> es\<^sub>2 [::] Ts\<^sub>2)"
  { assume ?lhs
    then have ?rhs by (auto intro: Cons_eq_appendI)
  }
  moreover {
    assume ?rhs
    then have ?lhs by fastforce
  }
  ultimately have "?lhs = ?rhs" by(rule iffI)
  then show ?case by (clarsimp simp: Cons)
qed simp
(*>*)

lemma [iff]: "P,E \<turnstile> Val v :: T = (typeof v = Some T)"
(*<*)proof(rule iffI) qed (auto elim: WT.cases)(*>*)

lemma [iff]: "P,E \<turnstile> Var V :: T = (E V = Some T)"
(*<*)proof(rule iffI) qed (auto elim: WT.cases)(*>*)

lemma [iff]: "P,E \<turnstile> e\<^sub>1;;e\<^sub>2 :: T\<^sub>2 = (\<exists>T\<^sub>1. P,E \<turnstile> e\<^sub>1::T\<^sub>1 \<and> P,E \<turnstile> e\<^sub>2::T\<^sub>2)"
(*<*)proof(rule iffI) qed (auto elim: WT.cases)(*>*)

lemma [iff]: "(P,E \<turnstile> {V:T; e} :: T') = (is_type P T \<and> P,E(V\<mapsto>T) \<turnstile> e :: T')"
(*<*)proof(rule iffI) qed (auto elim: WT.cases)(*>*)

(*<*)
inductive_cases WT_elim_cases[elim!]:
  "P,E \<turnstile> V :=e :: T"
  "P,E \<turnstile> if (e) e\<^sub>1 else e\<^sub>2 :: T"
  "P,E \<turnstile> while (e) c :: T"
  "P,E \<turnstile> throw e :: T"
  "P,E \<turnstile> try e\<^sub>1 catch(C V) e\<^sub>2 :: T"
  "P,E \<turnstile> Cast D e :: T"
  "P,E \<turnstile> a\<bullet>F{D} :: T"
  "P,E \<turnstile> C\<bullet>\<^sub>sF{D} :: T"
  "P,E \<turnstile> a\<bullet>F{D} := v :: T"
  "P,E \<turnstile> C\<bullet>\<^sub>sF{D} := v :: T"
  "P,E \<turnstile> e\<^sub>1 \<guillemotleft>bop\<guillemotright> e\<^sub>2 :: T"
  "P,E \<turnstile> new C :: T"
  "P,E \<turnstile> e\<bullet>M(ps) :: T"
  "P,E \<turnstile> C\<bullet>\<^sub>sM(ps) :: T"
(*>*)


lemma wt_env_mono:
  "P,E \<turnstile> e :: T \<Longrightarrow> (\<And>E'. E \<subseteq>\<^sub>m E' \<Longrightarrow> P,E' \<turnstile> e :: T)" and 
  "P,E \<turnstile> es [::] Ts \<Longrightarrow> (\<And>E'. E \<subseteq>\<^sub>m E' \<Longrightarrow> P,E' \<turnstile> es [::] Ts)"
(*<*)
proof(induct rule: WT_WTs_inducts)
  case WTVar then show ?case by(simp add: map_le_def dom_def)
next
  case WTLAss then show ?case by(force simp:map_le_def)
qed fastforce+
(*>*)


lemma WT_fv: "P,E \<turnstile> e :: T \<Longrightarrow> fv e \<subseteq> dom E"
and "P,E \<turnstile> es [::] Ts \<Longrightarrow> fvs es \<subseteq> dom E"
(*<*)
proof(induct rule:WT_WTs.inducts)
  case WTVar then show ?case by fastforce
next
  case WTLAss then show ?case by fastforce
next
  case WTBlock then show ?case by fastforce
next
  case WTTry then show ?case by fastforce
qed simp_all
(*>*)

lemma WT_nsub_RI: "P,E \<turnstile> e :: T \<Longrightarrow> \<not>sub_RI e"
 and WTs_nsub_RIs: "P,E \<turnstile> es [::] Ts \<Longrightarrow> \<not>sub_RIs es"
(*<*)proof(induct rule: WT_WTs.inducts) qed(simp_all)

end
(*>*)
