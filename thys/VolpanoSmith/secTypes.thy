theory secTypes
imports Semantics
begin

section {* Security types *}

subsection {* Security definitions *}


datatype secLevel = Low | High

type_synonym typeEnv = "vname \<rightharpoonup> secLevel"

inductive secExprTyping :: "typeEnv \<Rightarrow> expr \<Rightarrow> secLevel \<Rightarrow> bool" ("_ \<turnstile> _ : _")
where typeVal:  "\<Gamma> \<turnstile> Val V : lev"

  | typeVar:    "\<Gamma> Vn = Some lev \<Longrightarrow> \<Gamma> \<turnstile> Var Vn : lev"

  | typeBinOp1: "\<lbrakk>\<Gamma> \<turnstile> e1 : Low; \<Gamma> \<turnstile> e2 : Low\<rbrakk> \<Longrightarrow> \<Gamma> \<turnstile> e1 \<guillemotleft>bop\<guillemotright> e2 : Low"

  | typeBinOp2: "\<lbrakk>\<Gamma> \<turnstile> e1 : High; \<Gamma> \<turnstile> e2 : lev\<rbrakk> \<Longrightarrow> \<Gamma> \<turnstile> e1 \<guillemotleft>bop\<guillemotright> e2 : High"

  | typeBinOp3: "\<lbrakk>\<Gamma> \<turnstile> e1 : lev; \<Gamma> \<turnstile> e2 : High\<rbrakk> \<Longrightarrow> \<Gamma> \<turnstile> e1 \<guillemotleft>bop\<guillemotright> e2 : High"



inductive secComTyping :: "typeEnv \<Rightarrow> secLevel \<Rightarrow> com \<Rightarrow> bool" ("_,_ \<turnstile> _")
where typeSkip:  "\<Gamma>,T \<turnstile> Skip"

  | typeAssH:    "\<Gamma> V = Some High \<Longrightarrow> \<Gamma>,T \<turnstile> V := e"

  | typeAssL:    "\<lbrakk>\<Gamma> \<turnstile> e : Low; \<Gamma> V = Some Low\<rbrakk> \<Longrightarrow> \<Gamma>,Low \<turnstile> V := e"

  | typeSeq:     "\<lbrakk>\<Gamma>,T \<turnstile> c1; \<Gamma>,T \<turnstile> c2\<rbrakk> \<Longrightarrow> \<Gamma>,T \<turnstile> c1;;c2"

  | typeWhile:   "\<lbrakk>\<Gamma> \<turnstile> b : T; \<Gamma>,T \<turnstile> c\<rbrakk> \<Longrightarrow> \<Gamma>,T \<turnstile> while (b) c"

  | typeIf:      "\<lbrakk>\<Gamma> \<turnstile> b : T; \<Gamma>,T \<turnstile> c1; \<Gamma>,T \<turnstile> c2\<rbrakk> \<Longrightarrow> \<Gamma>,T \<turnstile> if (b) c1 else c2"

  | typeConvert: "\<Gamma>,High \<turnstile> c \<Longrightarrow> \<Gamma>,Low \<turnstile> c"


subsection {* Lemmas concerning expressions *}

lemma exprTypeable:
  assumes "fv e \<subseteq> dom \<Gamma>" obtains T where "\<Gamma> \<turnstile> e : T"
proof -
  from `fv e \<subseteq> dom \<Gamma>` have "\<exists>T. \<Gamma> \<turnstile> e : T"
  proof(induct e)
    case (Val V)
    have "\<Gamma> \<turnstile> Val V : Low" by(rule typeVal)
    thus ?case by (rule exI)
  next
    case (Var V)
    have "V \<in> fv (Var V)" by simp
    with `fv (Var V) \<subseteq> dom \<Gamma>` have "V \<in> dom \<Gamma>" by simp
    then obtain T where "\<Gamma> V = Some T" by auto
    hence "\<Gamma> \<turnstile> Var V : T" by (rule typeVar)
    thus ?case by (rule exI)
  next
    case (BinOp e1 bop e2)
    note IH1 = `fv e1 \<subseteq> dom \<Gamma> \<Longrightarrow> \<exists>T. \<Gamma> \<turnstile> e1 : T`
    note IH2 = `fv e2 \<subseteq> dom \<Gamma> \<Longrightarrow> \<exists>T. \<Gamma> \<turnstile> e2 : T`
    from `fv (e1 \<guillemotleft>bop\<guillemotright> e2) \<subseteq> dom \<Gamma>`
    have "fv e1 \<subseteq> dom \<Gamma>" and "fv e2 \<subseteq> dom \<Gamma>" by auto
    from IH1[OF `fv e1 \<subseteq> dom \<Gamma>`] obtain T1 where "\<Gamma> \<turnstile> e1 : T1" by auto
    from IH2[OF `fv e2 \<subseteq> dom \<Gamma>`] obtain T2 where "\<Gamma> \<turnstile> e2 : T2" by auto
    show ?case
    proof (cases T1)
      case Low
      show ?thesis
      proof (cases T2)
        case Low
        with `\<Gamma> \<turnstile> e1 : T1` `\<Gamma> \<turnstile> e2 : T2` `T1 = Low`
        have "\<Gamma> \<turnstile> e1 \<guillemotleft>bop\<guillemotright> e2 : Low" by(simp add:typeBinOp1)
        thus ?thesis by(rule exI)
      next
        case High
        with `\<Gamma> \<turnstile> e1 : T1` `\<Gamma> \<turnstile> e2 : T2` `T1 = Low`
        have "\<Gamma> \<turnstile> e1 \<guillemotleft>bop\<guillemotright> e2 : High" by(simp add:typeBinOp3)
        thus ?thesis by(rule exI)
      qed
    next
      case High
      with `\<Gamma> \<turnstile> e1 : T1` `\<Gamma> \<turnstile> e2 : T2`
      have "\<Gamma> \<turnstile> e1 \<guillemotleft>bop\<guillemotright> e2 : High" by (simp add: typeBinOp2)
      thus ?thesis by (rule exI)
    qed
  qed
  with that show ?thesis by blast
qed


lemma exprBinopTypeable: 
  assumes "\<Gamma> \<turnstile> e1 \<guillemotleft>bop\<guillemotright> e2 : T"
  shows "(\<exists>T1. \<Gamma> \<turnstile> e1 : T1) \<and> (\<exists>T2. \<Gamma> \<turnstile> e2 : T2)"
using assms by(auto elim:secExprTyping.cases)



lemma exprTypingHigh: 
  assumes "\<Gamma> \<turnstile> e : T" and "x \<in> fv e" and "\<Gamma> x = Some High"
  shows "\<Gamma> \<turnstile> e : High"
using assms
proof (induct e arbitrary:T)
  case (Val V) show ?case by (rule typeVal)
next
  case (Var V)
  from `x \<in> fv (Var V)` have "x = V" by simp
  with `\<Gamma> x = Some High` show ?case by(simp add:typeVar)
next
  case (BinOp e1 bop e2)
  note IH1 = `\<And>T. \<lbrakk>\<Gamma> \<turnstile> e1 : T; x \<in> fv e1; \<Gamma> x = Some High\<rbrakk> \<Longrightarrow> \<Gamma> \<turnstile> e1 : High`
  note IH2 = `\<And>T. \<lbrakk>\<Gamma> \<turnstile> e2 : T; x \<in> fv e2; \<Gamma> x = Some High\<rbrakk> \<Longrightarrow> \<Gamma> \<turnstile> e2 : High`
  from `\<Gamma> \<turnstile> e1 \<guillemotleft>bop\<guillemotright> e2 : T` 
  have T:"(\<exists>T1. \<Gamma> \<turnstile> e1 : T1) \<and> (\<exists>T2. \<Gamma> \<turnstile> e2 : T2)" by (auto intro!:exprBinopTypeable)
  then obtain T1 where "\<Gamma> \<turnstile> e1 : T1" by auto
  from T obtain T2 where "\<Gamma> \<turnstile> e2 : T2" by auto
  from `x \<in> fv (e1 \<guillemotleft>bop\<guillemotright> e2)` have "x \<in> (fv e1 \<union> fv e2)" by simp
  hence "x \<in> fv e1 \<or> x \<in> fv e2" by auto
  thus ?case
  proof
    assume "x \<in> fv e1"
    from IH1[OF `\<Gamma> \<turnstile> e1 : T1` this `\<Gamma> x = Some High`] have "\<Gamma> \<turnstile> e1 : High" .
    with `\<Gamma> \<turnstile> e2 : T2` show ?thesis by(simp add:typeBinOp2)
  next 
    assume "x \<in> fv e2" 
    from IH2[OF `\<Gamma> \<turnstile> e2 : T2` this `\<Gamma> x = Some High`] have "\<Gamma> \<turnstile> e2 : High" .
    with `\<Gamma> \<turnstile> e1 : T1` show ?thesis by(simp add:typeBinOp3)
  qed
qed


lemma exprTypingLow: 
  assumes "\<Gamma> \<turnstile> e : Low" and "x \<in> fv e" shows "\<Gamma> x = Some Low"
using assms
proof (induct e)
  case (Val V)
  have "fv (Val V) =  {}" by (rule FVc)
  with `x \<in> fv (Val V)` have False by auto
  thus ?thesis by simp
next
  case (Var V)
  from `x \<in> fv (Var V)` have xV: "x = V" by simp
  from `\<Gamma> \<turnstile> Var V : Low` have "\<Gamma> V = Some Low" by (auto elim:secExprTyping.cases)
  with xV show ?thesis by simp
next
  case (BinOp e1 bop e2)
  note IH1 = `\<lbrakk>\<Gamma> \<turnstile> e1 : Low; x \<in> fv e1\<rbrakk> \<Longrightarrow> \<Gamma> x = Some Low`
  note IH2=`\<lbrakk>\<Gamma> \<turnstile> e2 : Low; x \<in> fv e2\<rbrakk> \<Longrightarrow> \<Gamma> x = Some Low`
  from `\<Gamma> \<turnstile> e1 \<guillemotleft>bop\<guillemotright> e2 : Low` have "\<Gamma> \<turnstile> e1 : Low" and "\<Gamma> \<turnstile> e2 : Low"
    by(auto elim:secExprTyping.cases)
  from `x \<in> fv (e1 \<guillemotleft>bop\<guillemotright> e2)` have "x \<in> fv e1 \<union> fv e2" by (simp add:FVe)
  hence "x \<in> fv e1 \<or> x \<in> fv e2" by auto
  thus ?case
  proof
    assume "x \<in> fv e1"
    with IH1[OF `\<Gamma> \<turnstile> e1 : Low`] show ?thesis by auto
  next
    assume "x \<in> fv e2" 
    with IH2[OF `\<Gamma> \<turnstile> e2 : Low`] show ?thesis by auto
  qed
qed


lemma typeableFreevars:
  assumes "\<Gamma> \<turnstile> e : T" shows "fv e \<subseteq> dom \<Gamma>"
using assms
proof(induct e arbitrary:T)
  case (Val V)
  have "fv (Val V) = {}" by (rule FVc)
  thus ?case by simp
next
  case (Var V)
  show ?case
  proof
    fix x assume "x \<in> fv (Var V)"
    hence "x = V" by simp 
    from `\<Gamma> \<turnstile> Var V : T` have  "\<Gamma> V = Some T" by (auto elim:secExprTyping.cases)
    with `x = V` show "x \<in> dom \<Gamma>" by auto
  qed
next
  case (BinOp e1 bop e2)
  note IH1 = `\<And>T. \<Gamma> \<turnstile> e1 : T  \<Longrightarrow> fv e1 \<subseteq> dom \<Gamma>`
  note IH2 = `\<And>T. \<Gamma> \<turnstile> e2 : T  \<Longrightarrow> fv e2 \<subseteq> dom \<Gamma>`
  show ?case
  proof
    fix x assume "x \<in> fv (e1 \<guillemotleft>bop\<guillemotright> e2)"
    from `\<Gamma> \<turnstile> e1 \<guillemotleft>bop\<guillemotright> e2 : T` 
    have Q:"(\<exists>T1. \<Gamma> \<turnstile> e1 : T1) \<and> (\<exists>T2. \<Gamma> \<turnstile> e2 : T2)" 
      by(rule exprBinopTypeable)
    then obtain T1 where "\<Gamma> \<turnstile> e1 : T1" by blast
    from Q obtain T2 where "\<Gamma> \<turnstile> e2 : T2" by blast
    from IH1[OF `\<Gamma> \<turnstile> e1 : T1`] have "fv e1 \<subseteq> dom \<Gamma>" .
    moreover
    from IH2[OF `\<Gamma> \<turnstile> e2 : T2`] have "fv e2 \<subseteq> dom \<Gamma>" .
    ultimately have "(fv e1) \<union> (fv e2) \<subseteq> dom \<Gamma>" by auto
    hence "fv (e1 \<guillemotleft>bop\<guillemotright> e2) \<subseteq> dom \<Gamma>" by(simp add:FVe)
    with `x \<in> fv (e1 \<guillemotleft>bop\<guillemotright> e2)` show "x \<in> dom \<Gamma>" by auto
  qed
qed


(* We assume that expressions are type correct and thus never evaluate to None.
   In this setting, the first premise is not needed.
   But for further extensions of the language with a standard type system 
   we do not remove it. *)
lemma exprNotNone:
assumes "\<Gamma> \<turnstile> e : T" and "fv e \<subseteq> dom s"
shows "\<lbrakk>e\<rbrakk> s \<noteq> None"
using assms
proof (induct e arbitrary: \<Gamma> T s)
  case (Val v)
  show ?case by(simp add:Val)
next
  case (Var V)
  have "\<lbrakk>Var V\<rbrakk> s = s V" by (simp add:Var)
  have "V \<in> fv (Var V)" by (auto simp add:FVv)
  with `fv (Var V) \<subseteq> dom s` have "V \<in> dom s" by simp
  thus ?case by auto
next
  case (BinOp e1 bop e2)
  note IH1 = `\<And>T. \<lbrakk>\<Gamma> \<turnstile> e1 : T; fv e1 \<subseteq> dom s \<rbrakk>  \<Longrightarrow> \<lbrakk>e1\<rbrakk> s \<noteq> None`
  note IH2 = `\<And>T. \<lbrakk>\<Gamma> \<turnstile> e2 : T; fv e2 \<subseteq> dom s \<rbrakk>  \<Longrightarrow> \<lbrakk>e2\<rbrakk> s \<noteq> None`
  from `\<Gamma> \<turnstile> e1 \<guillemotleft>bop\<guillemotright> e2 :  T` have "(\<exists>T1. \<Gamma> \<turnstile> e1 : T1) \<and> (\<exists>T2. \<Gamma> \<turnstile> e2 : T2)"
    by(rule exprBinopTypeable)
  then obtain T1 T2 where "\<Gamma> \<turnstile> e1 : T1" and "\<Gamma> \<turnstile> e2 : T2" by blast
  from `fv (e1 \<guillemotleft>bop\<guillemotright> e2)  \<subseteq> dom s` have "fv e1 \<union> fv e2 \<subseteq> dom s" by(simp add:FVe)
  hence "fv e1 \<subseteq> dom s" and "fv e2 \<subseteq> dom s" by auto
  from IH1[OF `\<Gamma> \<turnstile> e1 : T1` `fv e1 \<subseteq> dom s`] have "\<lbrakk>e1\<rbrakk>s \<noteq> None" .
  moreover from IH2[OF `\<Gamma> \<turnstile> e2 : T2` `fv e2 \<subseteq> dom s`] have "\<lbrakk>e2\<rbrakk>s \<noteq> None" .
  ultimately show ?case
    apply(cases bop) apply auto
    apply(case_tac y,auto,case_tac ya,auto)+
    done
qed



subsection {* Noninterference definitions *}

subsubsection {* Low Equivalence  *}

text {* Low Equivalence is reflexive even if the involved states are undefined. 
  But in non-reflexive situations low variables must be initialized 
  (i.e. @{text "\<in> dom state"}), otherwise the proof will not work. This is not 
  a restriction, but a natural requirement, and could be formalized as part of 
  a standard type system.

  Low equivalence is also symmetric and transitiv (see lemmas) hence an
  equivalence relation. *}


definition lowEquiv :: "typeEnv \<Rightarrow> state \<Rightarrow> state \<Rightarrow> bool" ("_ \<turnstile> _ \<approx>\<^sub>L _")
where "\<Gamma> \<turnstile> s1 \<approx>\<^sub>L s2 \<equiv> \<forall>v\<in>dom \<Gamma>. \<Gamma> v = Some Low \<longrightarrow> (s1 v = s2 v)"


lemma lowEquivReflexive: "\<Gamma> \<turnstile> s1 \<approx>\<^sub>L s1" 
by(simp add:lowEquiv_def)

lemma lowEquivSymmetric:
  "\<Gamma> \<turnstile> s1 \<approx>\<^sub>L s2 \<Longrightarrow> \<Gamma> \<turnstile> s2 \<approx>\<^sub>L s1"
by(simp add:lowEquiv_def)

lemma lowEquivTransitive:
  "\<lbrakk>\<Gamma> \<turnstile> s1 \<approx>\<^sub>L s2; \<Gamma> \<turnstile> s2 \<approx>\<^sub>L s3\<rbrakk> \<Longrightarrow> \<Gamma> \<turnstile> s1 \<approx>\<^sub>L s3"
by(simp add:lowEquiv_def)



subsubsection {* Non Interference *}


definition nonInterference :: "typeEnv \<Rightarrow> com \<Rightarrow> bool"
where "nonInterference \<Gamma> c \<equiv> 
  (\<forall>s1 s2 s1' s2'. (\<Gamma> \<turnstile> s1 \<approx>\<^sub>L s2 \<and> \<langle>c,s1\<rangle> \<rightarrow>* \<langle>Skip,s1'\<rangle> \<and> \<langle>c,s2\<rangle> \<rightarrow>* \<langle>Skip,s2'\<rangle>) 
    \<longrightarrow> \<Gamma> \<turnstile> s1' \<approx>\<^sub>L s2')"

lemma nonInterferenceI: 
  "\<lbrakk>\<And>s1 s2 s1' s2'. \<lbrakk>\<Gamma> \<turnstile> s1 \<approx>\<^sub>L s2; \<langle>c,s1\<rangle> \<rightarrow>* \<langle>Skip,s1'\<rangle>; \<langle>c,s2\<rangle> \<rightarrow>* \<langle>Skip,s2'\<rangle>\<rbrakk>
  \<Longrightarrow> \<Gamma> \<turnstile> s1' \<approx>\<^sub>L s2'\<rbrakk> \<Longrightarrow> nonInterference \<Gamma> c"
by(auto simp:nonInterference_def)


lemma interpretLow:
  assumes "\<Gamma> \<turnstile> s1 \<approx>\<^sub>L s2" and all:"\<forall>V\<in>fv e. \<Gamma> V = Some Low"
  shows "\<lbrakk>e\<rbrakk> s1 = \<lbrakk>e\<rbrakk> s2"
using all
proof (induct e)
  case (Val v)
  show ?case by (simp add: Val)
next
  case (Var V)
  have "\<lbrakk>Var V\<rbrakk> s1 = s1 V" and "\<lbrakk>Var V\<rbrakk> s2 = s2 V" by(auto simp:Var)
  have "V \<in> fv (Var V)" by(simp add:FVv)
  from `V \<in> fv (Var V)` `\<forall>X\<in>fv (Var V). \<Gamma> X = Some Low` have "\<Gamma> V = Some Low" by simp
  with assms have "s1 V = s2 V" by(auto simp add:lowEquiv_def)
  thus ?case by auto
next
  case (BinOp e1 bop e2)
  note IH1 = `\<forall>V\<in>fv e1. \<Gamma> V = Some Low \<Longrightarrow> \<lbrakk>e1\<rbrakk>s1 = \<lbrakk>e1\<rbrakk>s2`
  note IH2 = `\<forall>V\<in>fv e2. \<Gamma> V = Some Low \<Longrightarrow> \<lbrakk>e2\<rbrakk>s1 = \<lbrakk>e2\<rbrakk>s2`
  from `\<forall>V\<in>fv (e1 \<guillemotleft>bop\<guillemotright> e2). \<Gamma> V = Some Low` have "\<forall>V\<in>fv e1. \<Gamma> V = Some Low"
    and "\<forall>V\<in> fv e2. \<Gamma> V = Some Low" by auto
  from IH1[OF `\<forall>V\<in>fv e1. \<Gamma> V = Some Low`] have "\<lbrakk>e1\<rbrakk> s1 = \<lbrakk>e1\<rbrakk> s2" .
  moreover
  from IH2[OF `\<forall>V\<in>fv e2. \<Gamma> V = Some Low`] have "\<lbrakk>e2\<rbrakk> s1 = \<lbrakk>e2\<rbrakk> s2" .
  ultimately show ?case by(cases "\<lbrakk>e1\<rbrakk> s2",auto)
qed


lemma interpretLow2:
  assumes "\<Gamma> \<turnstile> e : Low" and "\<Gamma> \<turnstile> s1 \<approx>\<^sub>L s2" shows "\<lbrakk>e\<rbrakk> s1 = \<lbrakk>e\<rbrakk> s2"
proof -
  from `\<Gamma> \<turnstile> e : Low` have "fv e \<subseteq> dom \<Gamma>" by(auto dest:typeableFreevars)
  have "\<forall>x\<in> fv e. \<Gamma> x = Some Low"
  proof
    fix x assume "x \<in> fv e"
    with `\<Gamma> \<turnstile> e : Low` show "\<Gamma> x = Some Low" by(auto intro:exprTypingLow)
  qed
  with `\<Gamma> \<turnstile> s1 \<approx>\<^sub>L s2` show ?thesis by(rule interpretLow)
qed


lemma assignNIhighlemma:
  assumes "\<Gamma> \<turnstile> s1 \<approx>\<^sub>L s2"  and "\<Gamma> V = Some High" and "s1' = s1(V:= \<lbrakk>e\<rbrakk> s1)" 
  and "s2' = s2(V:= \<lbrakk>e\<rbrakk> s2)"
  shows "\<Gamma> \<turnstile> s1' \<approx>\<^sub>L s2'"
proof -
  { fix V' assume "V' \<in> dom \<Gamma>" and  "\<Gamma> V' = Some Low"
    from `\<Gamma> \<turnstile> s1 \<approx>\<^sub>L s2`  `\<Gamma> V' = Some Low` have "s1 V' = s2 V'" 
      by(auto simp add:lowEquiv_def)
    have "s1' V' = s2' V'"
    proof(cases "V' = V")
      case True
      with `\<Gamma> V' = Some Low` `\<Gamma> V = Some High` have False by simp
      thus ?thesis by simp
    next
      case False
      with `s1' = s1(V:= \<lbrakk>e\<rbrakk> s1)` `s2' = s2(V:= \<lbrakk>e\<rbrakk> s2)`
      have "s1 V' = s1' V'" and "s2 V' = s2' V'" by auto
      with `s1 V' = s2 V'` show ?thesis by simp
    qed
  }
  thus ?thesis by(auto simp add:lowEquiv_def)
qed



lemma assignNIlowlemma:
  assumes "\<Gamma> \<turnstile> s1 \<approx>\<^sub>L s2"  and "\<Gamma> V = Some Low" and "\<Gamma> \<turnstile> e : Low" 
  and "s1' = s1(V:= \<lbrakk>e\<rbrakk> s1)" and "s2' = s2(V:= \<lbrakk>e\<rbrakk> s2)"
  shows "\<Gamma> \<turnstile> s1' \<approx>\<^sub>L s2'" 
proof -
  { fix V' assume "V' \<in> dom \<Gamma>" and  "\<Gamma> V' = Some Low"
    from `\<Gamma> \<turnstile> s1 \<approx>\<^sub>L s2`  `\<Gamma> V' = Some Low`
    have "s1 V' = s2 V'" by(auto simp add:lowEquiv_def)
    have "s1' V' = s2' V'"
    proof(cases "V' = V")
      case True
      with `s1' = s1(V:= \<lbrakk>e\<rbrakk> s1)` `s2' = s2(V:= \<lbrakk>e\<rbrakk> s2)`
      have "s1' V' = \<lbrakk>e\<rbrakk> s1" and "s2' V' = \<lbrakk>e\<rbrakk> s2" by auto
      from `\<Gamma> \<turnstile> e : Low` `\<Gamma> \<turnstile> s1 \<approx>\<^sub>L s2` have "\<lbrakk>e\<rbrakk> s1 = \<lbrakk>e\<rbrakk> s2" 
        by(auto intro:interpretLow2)
      with `s1' V' = \<lbrakk>e\<rbrakk> s1` `s2' V' = \<lbrakk>e\<rbrakk> s2` show ?thesis by simp
    next
      case False
      with `s1' = s1(V:= \<lbrakk>e\<rbrakk> s1)` `s2' = s2(V:= \<lbrakk>e\<rbrakk> s2)`
      have "s1' V' = s1 V'" and "s2' V' = s2 V'" by auto
      with `s1 V' = s2 V'` have "s1' V' = s2' V'" by simp
      with False `s1' V' = s1 V'` `s2' V' = s2 V'`
      show ?thesis by auto
    qed
  }
  thus ?thesis by(simp add:lowEquiv_def)
qed


text {* Sequential Compositionality is given the status of a theorem because 
  compositionality is no longer valid in case of concurrency *}

theorem SeqCompositionality:
  assumes "nonInterference \<Gamma> c1" and "nonInterference \<Gamma> c2" 
  shows "nonInterference \<Gamma> (c1;;c2)"
proof(rule nonInterferenceI)
  fix s1 s2 s1' s2'
  assume "\<Gamma> \<turnstile> s1 \<approx>\<^sub>L s2" and "\<langle>c1;;c2,s1\<rangle> \<rightarrow>* \<langle>Skip,s1'\<rangle>" 
    and "\<langle>c1;;c2,s2\<rangle> \<rightarrow>* \<langle>Skip,s2'\<rangle>"
  from `\<langle>c1;;c2,s1\<rangle> \<rightarrow>* \<langle>Skip,s1'\<rangle>` obtain s1'' where "\<langle>c1,s1\<rangle> \<rightarrow>* \<langle>Skip,s1''\<rangle>"
    and "\<langle>c2,s1''\<rangle> \<rightarrow>* \<langle>Skip,s1'\<rangle>" by(auto dest:Seq_reds)
  from `\<langle>c1;;c2,s2\<rangle> \<rightarrow>* \<langle>Skip,s2'\<rangle>` obtain s2'' where "\<langle>c1,s2\<rangle> \<rightarrow>* \<langle>Skip,s2''\<rangle>"
    and "\<langle>c2,s2''\<rangle> \<rightarrow>* \<langle>Skip,s2'\<rangle>" by(auto dest:Seq_reds)
  from `\<Gamma> \<turnstile> s1 \<approx>\<^sub>L s2` `\<langle>c1,s1\<rangle> \<rightarrow>* \<langle>Skip,s1''\<rangle>` `\<langle>c1,s2\<rangle> \<rightarrow>* \<langle>Skip,s2''\<rangle>`
    `nonInterference \<Gamma> c1`
  have "\<Gamma> \<turnstile> s1'' \<approx>\<^sub>L s2''" by(auto simp:nonInterference_def)
  with `\<langle>c2,s1''\<rangle> \<rightarrow>* \<langle>Skip,s1'\<rangle>` `\<langle>c2,s2''\<rangle> \<rightarrow>* \<langle>Skip,s2'\<rangle>` `nonInterference \<Gamma> c2` 
  show "\<Gamma> \<turnstile> s1' \<approx>\<^sub>L s2'" by(auto simp:nonInterference_def)
qed



lemma WhileStepInduct:
  assumes while:"\<langle>while (b) c,s1\<rangle> \<rightarrow>* \<langle>Skip,s2\<rangle>"
  and body:"\<And>s1 s2. \<langle>c,s1\<rangle> \<rightarrow>* \<langle>Skip,s2\<rangle>  \<Longrightarrow> \<Gamma> \<turnstile> s1 \<approx>\<^sub>L s2" and "\<Gamma>,High \<turnstile> c"
  shows "\<Gamma> \<turnstile> s1 \<approx>\<^sub>L s2"
using while
proof (induct rule:while_reds_induct)
  case (false s) thus ?case by(auto simp add:lowEquiv_def)
next 
  case (true s1 s3)
  from body[OF `\<langle>c,s1\<rangle> \<rightarrow>* \<langle>Skip,s3\<rangle>`] have "\<Gamma> \<turnstile> s1 \<approx>\<^sub>L s3" by simp
  with `\<Gamma> \<turnstile> s3 \<approx>\<^sub>L s2` show ?case by(auto intro:lowEquivTransitive)
qed



text {* In case control conditions from if/while are high, the body of an
  if/while must not change low variables in order to prevent implicit flow.
  That is, start and end state of any if/while body must be low equivalent. *}

theorem highBodies:
  assumes "\<Gamma>,High \<turnstile> c" and "\<langle>c,s1\<rangle> \<rightarrow>* \<langle>Skip,s2\<rangle>"
  shows "\<Gamma> \<turnstile> s1 \<approx>\<^sub>L s2"
  -- {* all intermediate states must be well formed, otherwise the proof does not 
  work for uninitialized variables. Thus it is propagated through the 
  theorem conclusion *}
using assms
proof(induct c arbitrary:s1 s2 rule:com.induct)
  case Skip
  from `\<langle>Skip,s1\<rangle> \<rightarrow>* \<langle>Skip,s2\<rangle>` have "s1 = s2" by (auto dest:Skip_reds)
  thus ?case by(simp add:lowEquiv_def)
next
  case (LAss V e)
  from `\<Gamma>,High \<turnstile> V:=e` have "\<Gamma> V = Some High" by(auto elim:secComTyping.cases)
  from `\<langle>V:=e,s1\<rangle> \<rightarrow>* \<langle>Skip,s2\<rangle>` have "s2 = s1(V:= \<lbrakk>e\<rbrakk>s1)" by (auto intro:LAss_reds)
  { fix V' assume "V' \<in> dom \<Gamma>" and "\<Gamma> V' = Some Low"
    have "s1 V' = s2 V'"
    proof(cases "V' = V")
      case True
      with `\<Gamma> V' = Some Low` `\<Gamma> V = Some High` have False by simp
      thus ?thesis by simp
    next
      case False
      with `s2 = s1(V:= \<lbrakk>e\<rbrakk>s1)` show ?thesis by simp 
    qed
  }
  thus ?case by(auto simp add:lowEquiv_def)
next
  case (Seq c1 c2)
  note IH1 = `\<And>s1 s2. \<lbrakk>\<Gamma>,High \<turnstile> c1; \<langle>c1,s1\<rangle> \<rightarrow>* \<langle>Skip,s2\<rangle>\<rbrakk> \<Longrightarrow> \<Gamma> \<turnstile> s1 \<approx>\<^sub>L s2`
  note IH2 = `\<And>s1 s2. \<lbrakk>\<Gamma>,High \<turnstile> c2; \<langle>c2,s1\<rangle> \<rightarrow>* \<langle>Skip,s2\<rangle>\<rbrakk> \<Longrightarrow> \<Gamma> \<turnstile> s1 \<approx>\<^sub>L s2`
  from `\<Gamma>,High \<turnstile> c1;;c2` have "\<Gamma>,High \<turnstile> c1" and "\<Gamma>,High \<turnstile> c2"
    by(auto elim:secComTyping.cases)
  from `\<langle>c1;;c2,s1\<rangle> \<rightarrow>* \<langle>Skip,s2\<rangle>` 
  have "\<exists>s3. \<langle>c1,s1\<rangle> \<rightarrow>* \<langle>Skip,s3\<rangle> \<and> \<langle>c2,s3\<rangle> \<rightarrow>* \<langle>Skip,s2\<rangle>" by(auto intro:Seq_reds)
  then obtain s3 where "\<langle>c1,s1\<rangle> \<rightarrow>* \<langle>Skip,s3\<rangle>" and "\<langle>c2,s3\<rangle> \<rightarrow>* \<langle>Skip,s2\<rangle>" by auto
  from IH1[OF `\<Gamma>,High \<turnstile> c1` `\<langle>c1,s1\<rangle> \<rightarrow>* \<langle>Skip,s3\<rangle>`]
  have "\<Gamma> \<turnstile> s1 \<approx>\<^sub>L s3" by simp
  from IH2[OF `\<Gamma>,High \<turnstile> c2` `\<langle>c2,s3\<rangle> \<rightarrow>* \<langle>Skip,s2\<rangle>`]
  have "\<Gamma> \<turnstile> s3 \<approx>\<^sub>L s2" by simp
  from `\<Gamma> \<turnstile> s1 \<approx>\<^sub>L s3` `\<Gamma> \<turnstile> s3 \<approx>\<^sub>L s2` show ?case
    by(auto intro:lowEquivTransitive)
next
  case (Cond b c1 c2)
  note IH1 = `\<And>s1 s2. \<lbrakk>\<Gamma>,High \<turnstile> c1; \<langle>c1,s1\<rangle> \<rightarrow>* \<langle>Skip,s2\<rangle>\<rbrakk> \<Longrightarrow> \<Gamma> \<turnstile> s1 \<approx>\<^sub>L s2`
  note IH2 = `\<And>s1 s2. \<lbrakk>\<Gamma>,High \<turnstile> c2; \<langle>c2,s1\<rangle> \<rightarrow>* \<langle>Skip,s2\<rangle>\<rbrakk> \<Longrightarrow> \<Gamma> \<turnstile> s1 \<approx>\<^sub>L s2`
  from `\<Gamma>,High \<turnstile> if (b) c1 else c2` have "\<Gamma>,High \<turnstile> c1" and "\<Gamma>,High \<turnstile> c2"
    by(auto elim:secComTyping.cases)
  from `\<langle>if (b) c1 else c2,s1\<rangle> \<rightarrow>* \<langle>Skip,s2\<rangle>` 
  have "\<lbrakk>b\<rbrakk> s1 = Some true \<or> \<lbrakk>b\<rbrakk> s1 = Some false" by(auto dest:Cond_True_or_False)
  thus ?case
  proof
    assume "\<lbrakk>b\<rbrakk> s1 = Some true"
    with `\<langle>if (b) c1 else c2,s1\<rangle> \<rightarrow>* \<langle>Skip,s2\<rangle>` have "\<langle>c1,s1\<rangle> \<rightarrow>* \<langle>Skip,s2\<rangle>"
      by (auto intro:CondTrue_reds)
    from IH1[OF `\<Gamma>,High \<turnstile> c1` this] show ?thesis .
  next
    assume "\<lbrakk>b\<rbrakk> s1 = Some false"
    with `\<langle>if (b) c1 else c2,s1\<rangle> \<rightarrow>* \<langle>Skip,s2\<rangle>` have "\<langle>c2,s1\<rangle> \<rightarrow>* \<langle>Skip,s2\<rangle>"
      by(auto intro:CondFalse_reds)
    from IH2[OF `\<Gamma>,High \<turnstile> c2` this] show ?thesis .
  qed
next
  case (While b c')
  note IH = `\<And>s1 s2. \<lbrakk>\<Gamma>,High \<turnstile> c'; \<langle>c',s1\<rangle> \<rightarrow>* \<langle>Skip,s2\<rangle>\<rbrakk> \<Longrightarrow> \<Gamma> \<turnstile> s1 \<approx>\<^sub>L s2`
  from `\<Gamma>,High \<turnstile> while (b) c'` have "\<Gamma>,High \<turnstile> c'" by(auto elim:secComTyping.cases)
  from IH[OF this] 
  have "\<And>s1 s2. \<lbrakk>\<langle>c',s1\<rangle> \<rightarrow>* \<langle>Skip,s2\<rangle>\<rbrakk> \<Longrightarrow> \<Gamma> \<turnstile> s1 \<approx>\<^sub>L s2" .
  with `\<langle>while (b) c',s1\<rangle> \<rightarrow>* \<langle>Skip,s2\<rangle>` `\<Gamma>,High \<turnstile> c'` 
  show ?case by(auto dest:WhileStepInduct)
qed



lemma CondHighCompositionality:
  assumes "\<Gamma>,High \<turnstile> if (b) c1 else c2"
  shows "nonInterference \<Gamma> (if (b) c1 else c2)"
proof(rule nonInterferenceI)
  fix s1 s2 s1' s2'
  assume "\<Gamma> \<turnstile> s1 \<approx>\<^sub>L s2" and "\<langle>if (b) c1 else c2,s1\<rangle> \<rightarrow>* \<langle>Skip,s1'\<rangle>" 
    and "\<langle>if (b) c1 else c2,s2\<rangle> \<rightarrow>* \<langle>Skip,s2'\<rangle>"
  show "\<Gamma> \<turnstile> s1' \<approx>\<^sub>L s2'"
  proof -
    from `\<Gamma>,High \<turnstile> if (b) c1 else c2` `\<langle>if (b) c1 else c2,s1\<rangle> \<rightarrow>* \<langle>Skip,s1'\<rangle>`
    have "\<Gamma> \<turnstile> s1 \<approx>\<^sub>L s1'" by(auto dest:highBodies)
    from `\<Gamma>,High \<turnstile> if (b) c1 else c2` `\<langle>if (b) c1 else c2,s2\<rangle> \<rightarrow>* \<langle>Skip,s2'\<rangle>`
    have "\<Gamma> \<turnstile> s2 \<approx>\<^sub>L s2'" by(auto dest:highBodies)
    with `\<Gamma> \<turnstile> s1 \<approx>\<^sub>L s2` have "\<Gamma> \<turnstile> s1 \<approx>\<^sub>L s2'" by(auto intro:lowEquivTransitive)
    from `\<Gamma> \<turnstile> s1 \<approx>\<^sub>L s1'` have "\<Gamma> \<turnstile> s1' \<approx>\<^sub>L s1" by(auto intro:lowEquivSymmetric)
    with `\<Gamma> \<turnstile> s1 \<approx>\<^sub>L s2'` show ?thesis by(auto intro:lowEquivTransitive)
  qed
qed



lemma CondLowCompositionality:
  assumes "nonInterference \<Gamma> c1" and "nonInterference \<Gamma> c2" and "\<Gamma> \<turnstile> b : Low" 
  shows "nonInterference \<Gamma> (if (b) c1 else c2)"
proof(rule nonInterferenceI)
  fix s1 s2 s1' s2'
  assume "\<Gamma> \<turnstile> s1 \<approx>\<^sub>L s2" and "\<langle>if (b) c1 else c2,s1\<rangle> \<rightarrow>* \<langle>Skip,s1'\<rangle>" 
    and "\<langle>if (b) c1 else c2,s2\<rangle> \<rightarrow>* \<langle>Skip,s2'\<rangle>"
  from `\<Gamma> \<turnstile> b : Low` `\<Gamma> \<turnstile> s1 \<approx>\<^sub>L s2` have "\<lbrakk>b\<rbrakk> s1 = \<lbrakk>b\<rbrakk> s2"
    by(auto intro:interpretLow2)
  from `\<langle>if (b) c1 else c2,s1\<rangle> \<rightarrow>* \<langle>Skip,s1'\<rangle>` 
  have "\<lbrakk>b\<rbrakk> s1 = Some true \<or> \<lbrakk>b\<rbrakk> s1 = Some false" by(auto dest:Cond_True_or_False)
  thus "\<Gamma> \<turnstile> s1' \<approx>\<^sub>L s2'"
  proof
    assume "\<lbrakk>b\<rbrakk> s1 = Some true"
    with `\<lbrakk>b\<rbrakk> s1 = \<lbrakk>b\<rbrakk> s2` have "\<lbrakk>b\<rbrakk> s2 = Some true" by(auto intro:CondTrue_reds)
    from `\<lbrakk>b\<rbrakk> s1 = Some true` `\<langle>if (b) c1 else c2,s1\<rangle> \<rightarrow>* \<langle>Skip,s1'\<rangle>`
    have "\<langle>c1,s1\<rangle> \<rightarrow>* \<langle>Skip,s1'\<rangle>" by(auto intro:CondTrue_reds)
    from `\<lbrakk>b\<rbrakk> s2 = Some true` `\<langle>if (b) c1 else c2,s2\<rangle> \<rightarrow>* \<langle>Skip,s2'\<rangle>`
    have "\<langle>c1,s2\<rangle> \<rightarrow>* \<langle>Skip,s2'\<rangle>" by(auto intro:CondTrue_reds)
    with `\<langle>c1,s1\<rangle> \<rightarrow>* \<langle>Skip,s1'\<rangle>` `\<Gamma> \<turnstile> s1 \<approx>\<^sub>L s2` `nonInterference \<Gamma> c1`
    show ?thesis by(auto simp:nonInterference_def)
  next
    assume "\<lbrakk>b\<rbrakk> s1 = Some false"
    with `\<lbrakk>b\<rbrakk> s1 = \<lbrakk>b\<rbrakk> s2` have "\<lbrakk>b\<rbrakk> s2 = Some false" by(auto intro:CondTrue_reds)
    from `\<lbrakk>b\<rbrakk> s1 = Some false` `\<langle>if (b) c1 else c2,s1\<rangle> \<rightarrow>* \<langle>Skip,s1'\<rangle>`
    have "\<langle>c2,s1\<rangle> \<rightarrow>* \<langle>Skip,s1'\<rangle>" by(auto intro:CondFalse_reds)
    from `\<lbrakk>b\<rbrakk> s2 = Some false` `\<langle>if (b) c1 else c2,s2\<rangle> \<rightarrow>* \<langle>Skip,s2'\<rangle>`
    have "\<langle>c2,s2\<rangle> \<rightarrow>* \<langle>Skip,s2'\<rangle>" by(auto intro:CondFalse_reds)
    with `\<langle>c2,s1\<rangle> \<rightarrow>* \<langle>Skip,s1'\<rangle>` `\<Gamma> \<turnstile> s1 \<approx>\<^sub>L s2` `nonInterference \<Gamma> c2`
    show ?thesis by(auto simp:nonInterference_def)
  qed
qed


lemma WhileHighCompositionality:
  assumes "\<Gamma>,High \<turnstile> while (b) c'"
  shows "nonInterference \<Gamma> (while (b) c')"
proof(rule nonInterferenceI)
  fix s1 s2 s1' s2'
  assume "\<Gamma> \<turnstile> s1 \<approx>\<^sub>L s2" and "\<langle>while (b) c',s1\<rangle> \<rightarrow>* \<langle>Skip,s1'\<rangle>"
    and "\<langle>while (b) c',s2\<rangle> \<rightarrow>* \<langle>Skip,s2'\<rangle>"
  show "\<Gamma> \<turnstile> s1' \<approx>\<^sub>L s2'"
  proof -
    from `\<Gamma>,High \<turnstile> while (b) c'` `\<langle>while (b) c',s1\<rangle> \<rightarrow>* \<langle>Skip,s1'\<rangle>`
    have "\<Gamma> \<turnstile> s1 \<approx>\<^sub>L s1'" by(auto dest:highBodies)
    from `\<Gamma>,High \<turnstile> while (b) c'` `\<langle>while (b) c',s2\<rangle> \<rightarrow>* \<langle>Skip,s2'\<rangle>`
    have "\<Gamma> \<turnstile> s2 \<approx>\<^sub>L s2'" by(auto dest:highBodies)
    with `\<Gamma> \<turnstile> s1 \<approx>\<^sub>L s2` have "\<Gamma> \<turnstile> s1 \<approx>\<^sub>L s2'" by(auto intro:lowEquivTransitive)
    from `\<Gamma> \<turnstile> s1 \<approx>\<^sub>L s1'` have "\<Gamma> \<turnstile> s1' \<approx>\<^sub>L s1" by(auto intro:lowEquivSymmetric)
    with `\<Gamma> \<turnstile> s1 \<approx>\<^sub>L s2'` show ?thesis by(auto intro:lowEquivTransitive)
  qed
qed



lemma WhileLowStepInduct:
  assumes  while1: "\<langle>while (b) c',s1\<rangle> \<rightarrow>* \<langle>Skip,s1'\<rangle>"   
  and      while2: "\<langle>while (b) c',s2\<rangle>\<rightarrow>*\<langle>Skip,s2'\<rangle>" 
  and      "\<Gamma> \<turnstile> b : Low"
  and      body:"\<And>s1 s1' s2 s2'. \<lbrakk>\<langle>c',s1\<rangle> \<rightarrow>* \<langle>Skip,s1'\<rangle>; \<langle>c',s2\<rangle> \<rightarrow>* \<langle>Skip,s2'\<rangle>;
                                   \<Gamma> \<turnstile> s1 \<approx>\<^sub>L s2\<rbrakk>  \<Longrightarrow>  \<Gamma> \<turnstile> s1' \<approx>\<^sub>L s2'"
  and      le: "\<Gamma> \<turnstile> s1 \<approx>\<^sub>L s2"
  shows    "\<Gamma> \<turnstile> s1' \<approx>\<^sub>L s2'"
using while1 le while2
proof (induct arbitrary:s2 rule:while_reds_induct)
  case (false s1)
  from `\<Gamma> \<turnstile> b : Low` `\<Gamma> \<turnstile> s1 \<approx>\<^sub>L s2` have "\<lbrakk>b\<rbrakk> s1 = \<lbrakk>b\<rbrakk> s2" by(auto intro:interpretLow2)
  with `\<lbrakk>b\<rbrakk> s1 = Some false` have "\<lbrakk>b\<rbrakk> s2 = Some false" by simp
  with `\<langle>while (b) c',s2\<rangle>\<rightarrow>*\<langle>Skip,s2'\<rangle>` have "s2 = s2'" by(auto intro:WhileFalse_reds)
  with `\<Gamma> \<turnstile> s1 \<approx>\<^sub>L s2` show ?case by auto
next 
  case (true s1 s1'')
  note IH = `\<And>s2''. \<lbrakk>\<Gamma> \<turnstile> s1'' \<approx>\<^sub>L s2''; \<langle>while (b) c',s2''\<rangle> \<rightarrow>* \<langle>Skip,s2'\<rangle>\<rbrakk> 
    \<Longrightarrow> \<Gamma> \<turnstile> s1' \<approx>\<^sub>L s2'`
  from `\<Gamma> \<turnstile> b : Low` `\<Gamma> \<turnstile> s1 \<approx>\<^sub>L s2` have "\<lbrakk>b\<rbrakk> s1 = \<lbrakk>b\<rbrakk> s2" by(auto intro:interpretLow2)
  with `\<lbrakk>b\<rbrakk> s1 = Some true` have "\<lbrakk>b\<rbrakk> s2 = Some true" by simp
  with `\<langle>while (b) c',s2\<rangle> \<rightarrow>* \<langle>Skip,s2'\<rangle>` obtain s2'' where "\<langle>c',s2\<rangle> \<rightarrow>* \<langle>Skip,s2''\<rangle>"
    and "\<langle>while (b) c',s2''\<rangle> \<rightarrow>* \<langle>Skip,s2'\<rangle>" by(auto dest:WhileTrue_reds)
  from body[OF `\<langle>c',s1\<rangle> \<rightarrow>* \<langle>Skip,s1''\<rangle>` `\<langle>c',s2\<rangle> \<rightarrow>* \<langle>Skip,s2''\<rangle>` `\<Gamma> \<turnstile> s1 \<approx>\<^sub>L s2`]
  have "\<Gamma> \<turnstile> s1'' \<approx>\<^sub>L s2''" .
  from IH[OF this `\<langle>while (b) c',s2''\<rangle> \<rightarrow>* \<langle>Skip,s2'\<rangle>`] show ?case .
qed



lemma WhileLowCompositionality:
  assumes "nonInterference \<Gamma> c'" and "\<Gamma> \<turnstile> b : Low" and "\<Gamma>,Low \<turnstile> c'"
  shows "nonInterference \<Gamma> (while (b) c')"
proof(rule nonInterferenceI)
  fix s1 s2 s1' s2'
  assume "\<Gamma> \<turnstile> s1 \<approx>\<^sub>L s2" and "\<langle>while (b) c',s1\<rangle> \<rightarrow>* \<langle>Skip,s1'\<rangle>" 
    and "\<langle>while (b) c',s2\<rangle> \<rightarrow>* \<langle>Skip,s2'\<rangle>"
  { fix s1 s2 s1'' s2''
    assume "\<langle>c',s1\<rangle> \<rightarrow>* \<langle>Skip,s1''\<rangle>" and "\<langle>c',s2\<rangle> \<rightarrow>* \<langle>Skip,s2''\<rangle>" 
      and  "\<Gamma> \<turnstile> s1 \<approx>\<^sub>L s2"  
    with `nonInterference \<Gamma> c'` have "\<Gamma> \<turnstile> s1'' \<approx>\<^sub>L s2''"
      by(auto simp:nonInterference_def)
  }
  hence "\<And>s1 s1'' s2 s2''. \<lbrakk>\<langle>c',s1\<rangle> \<rightarrow>* \<langle>Skip,s1''\<rangle>; \<langle>c',s2\<rangle> \<rightarrow>* \<langle>Skip,s2''\<rangle>;
                             \<Gamma> \<turnstile> s1 \<approx>\<^sub>L s2\<rbrakk>  \<Longrightarrow>  \<Gamma> \<turnstile> s1'' \<approx>\<^sub>L s2''" by auto
  with `\<langle>while (b) c',s1\<rangle> \<rightarrow>* \<langle>Skip,s1'\<rangle>` `\<langle>while (b) c',s2\<rangle> \<rightarrow>* \<langle>Skip,s2'\<rangle>`
    `\<Gamma> \<turnstile> b : Low` `\<Gamma> \<turnstile> s1 \<approx>\<^sub>L s2` show "\<Gamma> \<turnstile> s1' \<approx>\<^sub>L s2'"
    by(auto intro:WhileLowStepInduct)
qed



text {* and now: the main theorem: *}

theorem secTypeImpliesNonInterference:
  "\<Gamma>,T \<turnstile> c \<Longrightarrow> nonInterference \<Gamma> c"
proof (induct c arbitrary:T rule:com.induct)
  case Skip
  show ?case
  proof(rule nonInterferenceI)
    fix s1 s2 s1' s2'
    assume "\<Gamma> \<turnstile> s1 \<approx>\<^sub>L s2" and "\<langle>Skip,s1\<rangle> \<rightarrow>* \<langle>Skip,s1'\<rangle>" and "\<langle>Skip,s2\<rangle> \<rightarrow>* \<langle>Skip,s2'\<rangle>"
    from `\<langle>Skip,s1\<rangle> \<rightarrow>* \<langle>Skip,s1'\<rangle>` have "s1 = s1'" by(auto dest:Skip_reds)
    from `\<langle>Skip,s2\<rangle> \<rightarrow>* \<langle>Skip,s2'\<rangle>` have "s2 = s2'" by(auto dest:Skip_reds)
    from `\<Gamma> \<turnstile> s1 \<approx>\<^sub>L s2` and `s1 = s1'` and `s2 = s2'`
    show "\<Gamma> \<turnstile> s1' \<approx>\<^sub>L s2'" by simp
  qed
next
  case (LAss V e)
  from `\<Gamma>,T \<turnstile> V:=e` 
  have varprem:"(\<Gamma> V = Some High) \<or> (\<Gamma> V = Some Low \<and> \<Gamma> \<turnstile> e : Low \<and> T = Low)"
    by (auto elim:secComTyping.cases)
  show ?case
  proof(rule nonInterferenceI)
    fix s1 s2 s1' s2'
    assume "\<Gamma> \<turnstile> s1 \<approx>\<^sub>L s2" and "\<langle>V:=e,s1\<rangle> \<rightarrow>* \<langle>Skip,s1'\<rangle>" and "\<langle>V:=e,s2\<rangle> \<rightarrow>* \<langle>Skip,s2'\<rangle>"
    from `\<langle>V:=e,s1\<rangle> \<rightarrow>* \<langle>Skip,s1'\<rangle>` have "s1' = s1(V:=\<lbrakk>e\<rbrakk> s1)" by(auto intro:LAss_reds)
    from `\<langle>V:=e,s2\<rangle> \<rightarrow>* \<langle>Skip,s2'\<rangle>` have "s2' = s2(V:=\<lbrakk>e\<rbrakk> s2)" by(auto intro:LAss_reds)
    from varprem show "\<Gamma> \<turnstile> s1' \<approx>\<^sub>L s2'"
    proof
      assume "\<Gamma> V = Some High"
      with `\<Gamma> \<turnstile> s1 \<approx>\<^sub>L s2` `s1' = s1(V:=\<lbrakk>e\<rbrakk> s1)` `s2' = s2(V:=\<lbrakk>e\<rbrakk> s2)`
      show ?thesis by(auto intro:assignNIhighlemma)
    next
      assume "\<Gamma> V = Some Low \<and> \<Gamma> \<turnstile> e : Low \<and> T = Low"
      with `\<Gamma> \<turnstile> s1 \<approx>\<^sub>L s2` `s1' = s1(V:=\<lbrakk>e\<rbrakk> s1)` `s2' = s2(V:=\<lbrakk>e\<rbrakk> s2)`
      show ?thesis by(auto intro:assignNIlowlemma)
    qed
  qed
next
  case (Seq c1 c2)
  note IH1 = `\<And>T. \<Gamma>,T \<turnstile> c1 \<Longrightarrow> nonInterference \<Gamma> c1`
  note IH2 = `\<And>T. \<Gamma>,T \<turnstile> c2 \<Longrightarrow> nonInterference \<Gamma> c2`
  show ?case
  proof (cases T)
    case High
    with `\<Gamma>,T \<turnstile> c1;;c2` have "\<Gamma>,High \<turnstile> c1" and "\<Gamma>,High \<turnstile> c2"
      by(auto elim:secComTyping.cases)
    from IH1[OF `\<Gamma>,High \<turnstile> c1`] have "nonInterference \<Gamma> c1" .
    moreover
    from IH2[OF `\<Gamma>,High \<turnstile> c2`] have "nonInterference \<Gamma> c2" .
    ultimately show ?thesis by (auto intro:SeqCompositionality)
  next
    case Low
    with `\<Gamma>,T \<turnstile> c1;;c2`
    have "(\<Gamma>,Low \<turnstile> c1 \<and> \<Gamma>,Low \<turnstile> c2) \<or> \<Gamma>,High \<turnstile> c1;;c2"
      by(auto elim:secComTyping.cases)
    thus ?thesis 
    proof
      assume "\<Gamma>,Low \<turnstile> c1 \<and> \<Gamma>,Low \<turnstile> c2"
      hence "\<Gamma>,Low \<turnstile> c1" and "\<Gamma>,Low \<turnstile> c2" by simp_all
      from IH1[OF `\<Gamma>,Low \<turnstile> c1`] have "nonInterference \<Gamma> c1" .
      moreover
      from IH2[OF `\<Gamma>,Low \<turnstile> c2`] have "nonInterference \<Gamma> c2" .
      ultimately show ?thesis by(auto intro:SeqCompositionality)
    next
      assume "\<Gamma>,High \<turnstile> c1;;c2"
      hence "\<Gamma>,High \<turnstile> c1" and "\<Gamma>,High \<turnstile> c2" by(auto elim:secComTyping.cases)
      from IH1[OF `\<Gamma>,High \<turnstile> c1`] have "nonInterference \<Gamma> c1" .
      moreover
      from IH2[OF `\<Gamma>,High \<turnstile> c2`] have "nonInterference \<Gamma> c2" .
      ultimately show ?thesis by(auto intro:SeqCompositionality)
    qed
  qed
next
  case (Cond b c1 c2)
  note IH1 = `\<And>T. \<Gamma>,T \<turnstile> c1 \<Longrightarrow> nonInterference \<Gamma> c1`
  note IH2 = `\<And>T. \<Gamma>,T \<turnstile> c2 \<Longrightarrow> nonInterference \<Gamma> c2`
  show ?case
  proof (cases T)
    case High
    with `\<Gamma>,T \<turnstile> if (b) c1 else c2` show ?thesis
      by(auto intro:CondHighCompositionality)
  next
    case Low
    with `\<Gamma>,T \<turnstile> if (b) c1 else c2` 
    have "(\<Gamma> \<turnstile> b : Low \<and> \<Gamma>,Low \<turnstile> c1 \<and>\<Gamma>,Low \<turnstile> c2) \<or> \<Gamma>,High \<turnstile> if (b) c1 else c2"
      by(auto elim:secComTyping.cases)
    thus ?thesis
    proof
      assume "\<Gamma> \<turnstile> b : Low \<and> \<Gamma>,Low \<turnstile> c1 \<and> \<Gamma>,Low \<turnstile> c2"
      hence "\<Gamma> \<turnstile> b : Low" and "\<Gamma>,Low \<turnstile> c1" and "\<Gamma>,Low \<turnstile> c2" by simp_all
      from IH1[OF `\<Gamma>,Low \<turnstile> c1`] have "nonInterference \<Gamma> c1" .
      moreover
      from IH2[OF `\<Gamma>,Low \<turnstile> c2`] have "nonInterference \<Gamma> c2" .
      ultimately show ?thesis using `\<Gamma> \<turnstile> b : Low`
        by(auto intro:CondLowCompositionality)
    next
      assume "\<Gamma>,High \<turnstile> if (b) c1 else c2"
      thus ?thesis by(auto intro:CondHighCompositionality)
    qed
  qed
next
  case (While b c')
  note IH = `\<And>T. \<Gamma>,T \<turnstile> c' \<Longrightarrow> nonInterference \<Gamma> c'`
  show ?case
  proof(cases T)
    case High
    with `\<Gamma>,T \<turnstile> while (b) c'` show ?thesis by(auto intro:WhileHighCompositionality)
  next
    case Low
    with `\<Gamma>,T \<turnstile> while (b) c'` 
    have "(\<Gamma> \<turnstile> b : Low \<and> \<Gamma>,Low \<turnstile> c') \<or> \<Gamma>,High \<turnstile> while (b) c'"
      by(auto elim:secComTyping.cases)
    thus ?thesis
    proof
      assume "\<Gamma> \<turnstile> b : Low \<and> \<Gamma>,Low \<turnstile> c'"
      hence "\<Gamma> \<turnstile> b : Low" and "\<Gamma>,Low \<turnstile> c'" by simp_all
      moreover
      from IH[OF `\<Gamma>,Low \<turnstile> c'`] have "nonInterference \<Gamma> c'" .
      ultimately show ?thesis by(auto intro:WhileLowCompositionality)
    next
      assume "\<Gamma>,High \<turnstile> while (b) c'"
      thus ?thesis by(auto intro:WhileHighCompositionality)
    qed
  qed
qed

end
