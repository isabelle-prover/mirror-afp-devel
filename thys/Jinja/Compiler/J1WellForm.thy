(*  Title:      Jinja/Compiler/WellType1.thy
    ID:         $Id: J1WellForm.thy,v 1.6 2008-06-24 22:23:30 makarius Exp $
    Author:     Tobias Nipkow
    Copyright   2003 Technische Universitaet Muenchen
*)

header {* \isaheader{Well-Formedness of Intermediate Language} *}

theory J1WellForm
imports "../J/JWellForm" J1
begin

subsection "Well-Typedness"

types 
  env\<^isub>1  = "ty list"   --"type environment indexed by variable number"

inductive
  WT\<^isub>1 :: "[J\<^isub>1_prog,env\<^isub>1, expr\<^isub>1     , ty     ] \<Rightarrow> bool"
         ("(_,_ \<turnstile>\<^sub>1/ _ :: _)"   [51,51,51]50)
  and WTs\<^isub>1 :: "[J\<^isub>1_prog,env\<^isub>1, expr\<^isub>1 list, ty list] \<Rightarrow> bool"
         ("(_,_ \<turnstile>\<^sub>1/ _ [::] _)" [51,51,51]50)
  for P :: J\<^isub>1_prog
where
  
  WTNew\<^isub>1:
  "is_class P C  \<Longrightarrow>
  P,E \<turnstile>\<^sub>1 new C :: Class C"

| WTCast\<^isub>1:
  "\<lbrakk> P,E \<turnstile>\<^sub>1 e :: Class D;  is_class P C;  P \<turnstile> C \<preceq>\<^sup>* D \<or> P \<turnstile> D \<preceq>\<^sup>* C \<rbrakk>
  \<Longrightarrow> P,E \<turnstile>\<^sub>1 Cast C e :: Class C"

| WTVal\<^isub>1:
  "typeof v = Some T \<Longrightarrow>
  P,E \<turnstile>\<^sub>1 Val v :: T"

| WTVar\<^isub>1:
  "\<lbrakk> E!i = T; i < size E \<rbrakk>
  \<Longrightarrow> P,E \<turnstile>\<^sub>1 Var i :: T"

| WTBinOp\<^isub>1:
  "\<lbrakk> P,E \<turnstile>\<^sub>1 e\<^isub>1 :: T\<^isub>1;  P,E \<turnstile>\<^sub>1 e\<^isub>2 :: T\<^isub>2;
     case bop of Eq \<Rightarrow> (P \<turnstile> T\<^isub>1 \<le> T\<^isub>2 \<or> P \<turnstile> T\<^isub>2 \<le> T\<^isub>1) \<and> T = Boolean
               | Add \<Rightarrow> T\<^isub>1 = Integer \<and> T\<^isub>2 = Integer \<and> T = Integer \<rbrakk>
  \<Longrightarrow> P,E \<turnstile>\<^sub>1 e\<^isub>1 \<guillemotleft>bop\<guillemotright> e\<^isub>2 :: T"

| WTLAss\<^isub>1:
  "\<lbrakk> E!i = T;  i < size E; P,E \<turnstile>\<^sub>1 e :: T';  P \<turnstile> T' \<le> T \<rbrakk>
  \<Longrightarrow> P,E \<turnstile>\<^sub>1 i:=e :: Void"

| WTFAcc\<^isub>1:
  "\<lbrakk> P,E \<turnstile>\<^sub>1 e :: Class C;  P \<turnstile> C sees F:T in D \<rbrakk>
  \<Longrightarrow> P,E \<turnstile>\<^sub>1 e\<bullet>F{D} :: T"

| WTFAss\<^isub>1:
  "\<lbrakk> P,E \<turnstile>\<^sub>1 e\<^isub>1 :: Class C;  P \<turnstile> C sees F:T in D;  P,E \<turnstile>\<^sub>1 e\<^isub>2 :: T';  P \<turnstile> T' \<le> T \<rbrakk>
  \<Longrightarrow> P,E \<turnstile>\<^sub>1 e\<^isub>1\<bullet>F{D} := e\<^isub>2 :: Void"

| WTCall\<^isub>1:
  "\<lbrakk> P,E \<turnstile>\<^sub>1 e :: Class C; P \<turnstile> C sees M:Ts' \<rightarrow> T = m in D;
    P,E \<turnstile>\<^sub>1 es [::] Ts;  P \<turnstile> Ts [\<le>] Ts' \<rbrakk>
  \<Longrightarrow> P,E \<turnstile>\<^sub>1 e\<bullet>M(es) :: T"

| WTBlock\<^isub>1:
  "\<lbrakk> is_type P T; P,E@[T] \<turnstile>\<^sub>1 e::T' \<rbrakk>
  \<Longrightarrow>  P,E \<turnstile>\<^sub>1 {i:T; e} :: T'"

| WTSeq\<^isub>1:
  "\<lbrakk> P,E \<turnstile>\<^sub>1 e\<^isub>1::T\<^isub>1;  P,E \<turnstile>\<^sub>1 e\<^isub>2::T\<^isub>2 \<rbrakk>
  \<Longrightarrow>  P,E \<turnstile>\<^sub>1 e\<^isub>1;;e\<^isub>2 :: T\<^isub>2"

| WTCond\<^isub>1:
  "\<lbrakk> P,E \<turnstile>\<^sub>1 e :: Boolean;  P,E \<turnstile>\<^sub>1 e\<^isub>1::T\<^isub>1;  P,E \<turnstile>\<^sub>1 e\<^isub>2::T\<^isub>2;
    P \<turnstile> T\<^isub>1 \<le> T\<^isub>2 \<or> P \<turnstile> T\<^isub>2 \<le> T\<^isub>1;  P \<turnstile> T\<^isub>1 \<le> T\<^isub>2 \<longrightarrow> T = T\<^isub>2; P \<turnstile> T\<^isub>2 \<le> T\<^isub>1 \<longrightarrow> T = T\<^isub>1 \<rbrakk>
  \<Longrightarrow> P,E \<turnstile>\<^sub>1 if (e) e\<^isub>1 else e\<^isub>2 :: T"

| WTWhile\<^isub>1:
  "\<lbrakk> P,E \<turnstile>\<^sub>1 e :: Boolean;  P,E \<turnstile>\<^sub>1 c::T \<rbrakk>
  \<Longrightarrow> P,E \<turnstile>\<^sub>1 while (e) c :: Void"

| WTThrow\<^isub>1:
  "P,E \<turnstile>\<^sub>1 e :: Class C  \<Longrightarrow>
  P,E \<turnstile>\<^sub>1 throw e :: Void"

| WTTry\<^isub>1:
  "\<lbrakk> P,E \<turnstile>\<^sub>1 e\<^isub>1 :: T;  P,E@[Class C] \<turnstile>\<^sub>1 e\<^isub>2 :: T; is_class P C \<rbrakk>
  \<Longrightarrow> P,E \<turnstile>\<^sub>1 try e\<^isub>1 catch(C i) e\<^isub>2 :: T"

| WTNil\<^isub>1:
  "P,E \<turnstile>\<^sub>1 [] [::] []"

| WTCons\<^isub>1:
  "\<lbrakk> P,E \<turnstile>\<^sub>1 e :: T;  P,E \<turnstile>\<^sub>1 es [::] Ts \<rbrakk>
  \<Longrightarrow>  P,E \<turnstile>\<^sub>1 e#es [::] T#Ts"

(*<*)
declare  WT\<^isub>1_WTs\<^isub>1.intros[intro!]
declare WTNil\<^isub>1[iff]

lemmas WT\<^isub>1_WTs\<^isub>1_induct = WT\<^isub>1_WTs\<^isub>1.induct [split_format (complete)]
  and WT\<^isub>1_WTs\<^isub>1_inducts = WT\<^isub>1_WTs\<^isub>1.inducts [split_format (complete)]

inductive_cases eee[elim!]:
  "P,E \<turnstile>\<^sub>1 Val v :: T"
  "P,E \<turnstile>\<^sub>1 Var i :: T"
  "P,E \<turnstile>\<^sub>1 Cast D e :: T"
  "P,E \<turnstile>\<^sub>1 i:=e :: T"
  "P,E \<turnstile>\<^sub>1 {i:U; e} :: T"
  "P,E \<turnstile>\<^sub>1 e\<^isub>1;;e\<^isub>2 :: T"
  "P,E \<turnstile>\<^sub>1 if (e) e\<^isub>1 else e\<^isub>2 :: T"
  "P,E \<turnstile>\<^sub>1 while (e) c :: T"
  "P,E \<turnstile>\<^sub>1 throw e :: T"
  "P,E \<turnstile>\<^sub>1 try e\<^isub>1 catch(C i) e\<^isub>2 :: T"
  "P,E \<turnstile>\<^sub>1 e\<bullet>F{D} :: T"
  "P,E \<turnstile>\<^sub>1 e\<^isub>1\<bullet>F{D}:=e\<^isub>2 :: T"
  "P,E \<turnstile>\<^sub>1 e\<^isub>1 \<guillemotleft>bop\<guillemotright> e\<^isub>2 :: T"
  "P,E \<turnstile>\<^sub>1 new C :: T"
  "P,E \<turnstile>\<^sub>1 e\<bullet>M(es) :: T"
  "P,E \<turnstile>\<^sub>1 [] [::] Ts"
  "P,E \<turnstile>\<^sub>1 e#es [::] Ts"
(*>*)

lemma WTs\<^isub>1_same_size: "\<And>Ts. P,E \<turnstile>\<^sub>1 es [::] Ts \<Longrightarrow> size es = size Ts"
(*<*)by (induct es type:list) auto(*>*)


lemma WT\<^isub>1_unique:
  "P,E \<turnstile>\<^sub>1 e :: T\<^isub>1 \<Longrightarrow> (\<And>T\<^isub>2. P,E \<turnstile>\<^sub>1 e :: T\<^isub>2 \<Longrightarrow> T\<^isub>1 = T\<^isub>2)" and
  "P,E \<turnstile>\<^sub>1 es [::] Ts\<^isub>1 \<Longrightarrow> (\<And>Ts\<^isub>2. P,E \<turnstile>\<^sub>1 es [::] Ts\<^isub>2 \<Longrightarrow> Ts\<^isub>1 = Ts\<^isub>2)"
(*<*)
apply(induct rule:WT\<^isub>1_WTs\<^isub>1.inducts)
apply blast
apply blast
apply clarsimp
apply blast
apply clarsimp
apply(case_tac bop)
apply clarsimp
apply clarsimp
apply blast
apply (blast dest:sees_field_idemp sees_field_fun)
apply blast
apply (blast dest:sees_method_idemp sees_method_fun)
apply blast
apply blast
apply blast
apply blast
apply clarify
apply blast
apply blast
apply blast
done
(*>*)


lemma assumes wf: "wf_prog p P"
shows WT\<^isub>1_is_type: "P,E \<turnstile>\<^sub>1 e :: T \<Longrightarrow> set E \<subseteq> types P \<Longrightarrow> is_type P T"
and "P,E \<turnstile>\<^sub>1 es [::] Ts \<Longrightarrow> True"
(*<*)
apply(induct rule:WT\<^isub>1_WTs\<^isub>1.inducts)
apply simp
apply simp
apply (simp add:typeof_lit_is_type)
apply (blast intro:nth_mem)
apply(simp split:bop.splits)
apply simp
apply (simp add:sees_field_is_type[OF _ wf])
apply simp
apply(fastsimp dest!: sees_wf_mdecl[OF wf] simp:wf_mdecl_def)
apply simp
apply simp
apply blast
apply simp
apply simp
apply simp
apply simp
apply simp
done
(*>*)


subsection{* Well-formedness*}

--"Indices in blocks increase by 1"

primrec \<B> :: "expr\<^isub>1 \<Rightarrow> nat \<Rightarrow> bool"
  and \<B>s :: "expr\<^isub>1 list \<Rightarrow> nat \<Rightarrow> bool" where
"\<B> (new C) i = True" |
"\<B> (Cast C e) i = \<B> e i" |
"\<B> (Val v) i = True" |
"\<B> (e\<^isub>1 \<guillemotleft>bop\<guillemotright> e\<^isub>2) i = (\<B> e\<^isub>1 i \<and> \<B> e\<^isub>2 i)" |
"\<B> (Var j) i = True" |
"\<B> (e\<bullet>F{D}) i = \<B> e i" |
"\<B> (j:=e) i = \<B> e i" |
"\<B> (e\<^isub>1\<bullet>F{D} := e\<^isub>2) i = (\<B> e\<^isub>1 i \<and> \<B> e\<^isub>2 i)" |
"\<B> (e\<bullet>M(es)) i = (\<B> e i \<and> \<B>s es i)" |
"\<B> ({j:T ; e}) i = (i = j \<and> \<B> e (i+1))" |
"\<B> (e\<^isub>1;;e\<^isub>2) i = (\<B> e\<^isub>1 i \<and> \<B> e\<^isub>2 i)" |
"\<B> (if (e) e\<^isub>1 else e\<^isub>2) i = (\<B> e i \<and> \<B> e\<^isub>1 i \<and> \<B> e\<^isub>2 i)" |
"\<B> (throw e) i = \<B> e i" |
"\<B> (while (e) c) i = (\<B> e i \<and> \<B> c i)" |
"\<B> (try e\<^isub>1 catch(C j) e\<^isub>2) i = (\<B> e\<^isub>1 i \<and> i=j \<and> \<B> e\<^isub>2 (i+1))" |

"\<B>s [] i = True" |
"\<B>s (e#es) i = (\<B> e i \<and> \<B>s es i)"


definition wf_J\<^isub>1_mdecl :: "J\<^isub>1_prog \<Rightarrow> cname \<Rightarrow> expr\<^isub>1 mdecl \<Rightarrow> bool"
where
  "wf_J\<^isub>1_mdecl P C  \<equiv>  \<lambda>(M,Ts,T,body).
    (\<exists>T'. P,Class C#Ts \<turnstile>\<^sub>1 body :: T' \<and> P \<turnstile> T' \<le> T) \<and>
    \<D> body \<lfloor>{..size Ts}\<rfloor> \<and> \<B> body (size Ts + 1)"

lemma wf_J\<^isub>1_mdecl[simp]:
  "wf_J\<^isub>1_mdecl P C (M,Ts,T,body) \<equiv>
    ((\<exists>T'. P,Class C#Ts \<turnstile>\<^sub>1 body :: T' \<and> P \<turnstile> T' \<le> T) \<and>
     \<D> body \<lfloor>{..size Ts}\<rfloor> \<and> \<B> body (size Ts + 1))"
(*<*)by (simp add:wf_J\<^isub>1_mdecl_def)(*>*)

abbreviation "wf_J\<^isub>1_prog == wf_prog wf_J\<^isub>1_mdecl"

end
