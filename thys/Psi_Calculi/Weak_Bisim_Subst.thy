(* 
   Title: Psi-calculi   
   Author/Maintainer: Jesper Bengtson (jebe@itu.dk), 2012
*)
theory Weak_Bisim_Subst
  imports Weak_Bisim_Struct_Cong Weak_Bisim_Pres Bisim_Subst
begin

context env begin

abbreviation
  weakBisimSubstJudge ("_ \<rhd> _ \<approx>\<^sub>s _" [70, 70, 70] 65) where "\<Psi> \<rhd> P \<approx>\<^sub>s Q \<equiv> (\<Psi>, P, Q) \<in> closeSubst weakBisim"
abbreviation
  weakBisimSubstNilJudge ("_ \<approx>\<^sub>s _" [70, 70] 65) where "P \<approx>\<^sub>s Q \<equiv> \<one> \<rhd> P \<approx>\<^sub>s Q"

lemmas weakBisimSubstClosed[eqvt] = closeSubstClosed[OF weakBisimEqvt]
lemmas weakBisimEqvt[simp] = closeSubstEqvt[OF weakBisimEqvt]

lemma strongBisimSubstWeakBisimSubst:
  fixes \<Psi> :: 'b
  and   P :: "('a, 'b, 'c) psi"
  and   Q :: "('a, 'b, 'c) psi"

  assumes "\<Psi> \<rhd> P \<sim>\<^sub>s Q"

  shows "\<Psi> \<rhd> P \<approx>\<^sub>s Q"
using assms
by(metis closeSubstI closeSubstE strongBisimWeakBisim)

lemma weakBisimSubstOutputPres:
  fixes \<Psi> :: 'b
  and   P :: "('a, 'b, 'c) psi"
  and   Q :: "('a, 'b, 'c) psi"
  and   M :: 'a
  and   N :: 'a
  
  assumes "\<Psi> \<rhd> P \<approx>\<^sub>s Q"

  shows "\<Psi> \<rhd> M\<langle>N\<rangle>.P \<approx>\<^sub>s M\<langle>N\<rangle>.Q"
using assms
by(fastforce intro: closeSubstI closeSubstE weakBisimOutputPres)

lemma bisimSubstInputPres:
  fixes \<Psi>    :: 'b
  and   P    :: "('a, 'b, 'c) psi"
  and   Q    :: "('a, 'b, 'c) psi"
  and   M    :: 'a
  and   xvec :: "name list"
  and   N    :: 'a

  assumes "\<Psi> \<rhd> P \<approx>\<^sub>s Q"
  and     "xvec \<sharp>* \<Psi>"
  and     "distinct xvec"

  shows "\<Psi> \<rhd> M\<lparr>\<lambda>*xvec N\<rparr>.P \<approx>\<^sub>s M\<lparr>\<lambda>*xvec N\<rparr>.Q"
proof(rule_tac closeSubstI)
  fix yvec Tvec
  assume "length(yvec::name list) = length (Tvec::'a list)" and "distinct yvec"
  obtain p where "(p \<bullet> xvec) \<sharp>* yvec" and "(p \<bullet> xvec) \<sharp>* Tvec"
             and "(p \<bullet> xvec) \<sharp>* P" and "(p \<bullet> xvec) \<sharp>* Q" and "(p \<bullet> xvec) \<sharp>* \<Psi>" and "(p \<bullet> xvec) \<sharp>* N"
             and S: "set p \<subseteq> set xvec \<times> set (p \<bullet> xvec)"
      by(rule_tac c="(yvec, Tvec, P, Q, \<Psi>, N)" in name_list_avoiding) auto
    
  from `\<Psi> \<rhd> P \<approx>\<^sub>s Q` have "(p \<bullet> \<Psi>) \<rhd> (p \<bullet> P) \<approx>\<^sub>s (p \<bullet> Q)"
    by(rule weakBisimSubstClosed)
  with `xvec \<sharp>* \<Psi>` `(p \<bullet> xvec) \<sharp>* \<Psi>` S have "\<Psi> \<rhd> (p \<bullet> P) \<approx>\<^sub>s (p \<bullet> Q)"
    by simp

  {
    fix Tvec' :: "'a list"

    note  `\<Psi> \<rhd> (p \<bullet> P) \<approx>\<^sub>s (p \<bullet> Q)`
    moreover assume "length xvec = length Tvec'"
    with `length yvec = length Tvec` have "length(yvec@(p \<bullet> xvec)) = length(Tvec@Tvec')"
      by auto
    moreover from `distinct xvec` `distinct yvec` `(p \<bullet> xvec) \<sharp>* yvec` have "distinct(yvec@(p \<bullet> xvec))"
      by(auto simp add: fresh_star_def fresh_def name_list_supp)
    ultimately have "\<Psi> \<rhd> (p \<bullet> P)[(yvec@(p \<bullet> xvec))::=(Tvec@Tvec')] \<approx> (p \<bullet> Q)[(yvec@(p \<bullet> xvec))::=(Tvec@Tvec')]"
      by(rule closeSubstE)
    with `length yvec = length Tvec` `length xvec = length Tvec'` `distinct xvec` `distinct yvec` `(p \<bullet> xvec) \<sharp>* yvec` `(p \<bullet> xvec) \<sharp>* Tvec` have "\<Psi> \<rhd> ((p \<bullet> P)[yvec::=Tvec])[(p \<bullet> xvec)::=Tvec'] \<approx> ((p \<bullet> Q)[yvec::=Tvec])[(p \<bullet> xvec)::=Tvec']"
      by(subst subst5[symmetric], auto)+
  }

  with `(p \<bullet> xvec) \<sharp>* yvec` `(p \<bullet> xvec) \<sharp>* Tvec`
  have "\<Psi> \<rhd> (M\<lparr>\<lambda>*(p \<bullet> xvec) (p \<bullet> N)\<rparr>.(p \<bullet> P))[yvec::=Tvec] \<approx> (M\<lparr>\<lambda>*(p \<bullet> xvec) (p \<bullet> N)\<rparr>.(p \<bullet> Q))[yvec::=Tvec]"
    by(force intro: weakBisimInputPres)
  moreover from `(p \<bullet> xvec) \<sharp>* N` `(p \<bullet> xvec) \<sharp>* P` S have "M\<lparr>\<lambda>*(p \<bullet> xvec) (p \<bullet> N)\<rparr>.(p \<bullet> P) = M\<lparr>\<lambda>*xvec N\<rparr>.P" 
    apply(simp add: psi.inject) by(rule inputChainAlpha[symmetric]) auto
  moreover from `(p \<bullet> xvec) \<sharp>* N` `(p \<bullet> xvec) \<sharp>* Q` S have "M\<lparr>\<lambda>*(p \<bullet> xvec) (p \<bullet> N)\<rparr>.(p \<bullet> Q) = M\<lparr>\<lambda>*xvec N\<rparr>.Q"
    apply(simp add: psi.inject) by(rule inputChainAlpha[symmetric]) auto
  ultimately show "\<Psi> \<rhd> (M\<lparr>\<lambda>*xvec N\<rparr>.P)[yvec::=Tvec] \<approx> (M\<lparr>\<lambda>*xvec N\<rparr>.Q)[yvec::=Tvec]"
    by force
qed
(*
lemma bisimSubstCasePresAux:
  fixes \<Psi>   :: 'b
  and   CsP :: "('c \<times> ('a, 'b, 'c) psi) list"
  and   CsQ :: "('c \<times> ('a, 'b, 'c) psi) list"
  
  assumes C1: "\<And>\<phi> P. (\<phi>, P) mem CsP \<Longrightarrow> \<exists>Q. (\<phi>, Q) mem CsQ \<and> guarded Q \<and> \<Psi> \<rhd> P \<sim>\<^sub>s Q"
  and     C2: "\<And>\<phi> Q. (\<phi>, Q) mem CsQ \<Longrightarrow> \<exists>P. (\<phi>, P) mem CsP \<and> guarded P \<and> \<Psi> \<rhd> P \<sim>\<^sub>s Q"

  shows "\<Psi> \<rhd> Cases CsP \<sim>\<^sub>s Cases CsQ"
proof -
  {
    fix xvec :: "name list"
    and Tvec :: "'a list"

    assume "length xvec = length Tvec"
    and    "distinct xvec"

    have "\<Psi> \<rhd> Cases(caseListSubst CsP xvec Tvec) \<sim> Cases(caseListSubst CsQ xvec Tvec)"
    proof(rule bisimCasePres)
      fix \<phi> P
      assume "(\<phi>, P) mem (caseListSubst CsP xvec Tvec)"
      then obtain \<phi>' P' where "(\<phi>', P') mem CsP" and "\<phi> = substCond \<phi>' xvec Tvec" and PeqP': "P = (P'[xvec::=Tvec])"
        by(induct CsP) force+
      from `(\<phi>', P') mem CsP` obtain Q' where "(\<phi>', Q') mem CsQ" and "guarded Q'" and "\<Psi> \<rhd> P' \<sim>\<^sub>s Q'" by(blast dest: C1)
      from `(\<phi>', Q') mem CsQ` `\<phi> = substCond \<phi>' xvec Tvec` obtain Q where "(\<phi>, Q) mem (caseListSubst CsQ xvec Tvec)" and "Q = Q'[xvec::=Tvec]"
        by(induct CsQ) auto
      with PeqP' `guarded Q'` `\<Psi> \<rhd> P' \<sim>\<^sub>s Q'` `length xvec = length Tvec` `distinct xvec` show "\<exists>Q. (\<phi>, Q) mem (caseListSubst CsQ xvec Tvec) \<and> guarded Q \<and> \<Psi> \<rhd> P \<sim> Q"
        by(blast dest: bisimSubstE guardedSubst)
    next
      fix \<phi> Q
      assume "(\<phi>, Q) mem (caseListSubst CsQ xvec Tvec)"
      then obtain \<phi>' Q' where "(\<phi>', Q') mem CsQ" and "\<phi> = substCond \<phi>' xvec Tvec" and QeqQ': "Q = Q'[xvec::=Tvec]"
        by(induct CsQ) force+
      from `(\<phi>', Q') mem CsQ` obtain P' where "(\<phi>', P') mem CsP" and "guarded P'" and "\<Psi> \<rhd> P' \<sim>\<^sub>s Q'" by(blast dest: C2)
      from `(\<phi>', P') mem CsP` `\<phi> = substCond \<phi>' xvec Tvec` obtain P where "(\<phi>, P) mem (caseListSubst CsP xvec Tvec)" and "P = P'[xvec::=Tvec]"
        by(induct CsP) auto
      with QeqQ' `guarded P'` `\<Psi> \<rhd> P' \<sim>\<^sub>s Q'` `length xvec = length Tvec` `distinct xvec` show "\<exists>P. (\<phi>, P) mem (caseListSubst CsP xvec Tvec) \<and> guarded P \<and> \<Psi> \<rhd> P \<sim> Q"
        by(blast dest: bisimSubstE guardedSubst)
    qed
  }
  thus ?thesis
    by(rule_tac bisimSubstI) auto
qed
*)
lemma weakBisimSubstReflexive:
  fixes \<Psi> :: 'b
  and   P :: "('a, 'b, 'c) psi"

  shows "\<Psi> \<rhd> P \<approx>\<^sub>s P"
by(auto intro: closeSubstI weakBisimReflexive)

lemma bisimSubstTransitive:
  fixes \<Psi> :: 'b
  and   P :: "('a, 'b, 'c) psi"
  and   Q :: "('a, 'b, 'c) psi"
  and   R :: "('a, 'b, 'c) psi"

  assumes "\<Psi> \<rhd> P \<approx>\<^sub>s Q"
  and     "\<Psi> \<rhd> Q \<approx>\<^sub>s R"

  shows "\<Psi> \<rhd> P \<approx>\<^sub>s R"
using assms
by(auto intro: closeSubstI closeSubstE weakBisimTransitive)

lemma weakBisimSubstSymmetric:
  fixes \<Psi> :: 'b
  and   P :: "('a, 'b, 'c) psi"
  and   Q :: "('a, 'b, 'c) psi"

  assumes "\<Psi> \<rhd> P \<approx>\<^sub>s Q"

  shows "\<Psi> \<rhd> Q \<approx>\<^sub>s P"
using assms
by(auto intro: closeSubstI closeSubstE weakBisimE)
(*
lemma bisimSubstCasePres:
  fixes \<Psi>   :: 'b
  and   CsP :: "('c \<times> ('a, 'b, 'c) psi) list"
  and   CsQ :: "('c \<times> ('a, 'b, 'c) psi) list"
  
  assumes "length CsP = length CsQ"
  and     C: "\<And>(i::nat) \<phi> P \<phi>' Q. \<lbrakk>i <= length CsP; (\<phi>, P) = nth CsP i; (\<phi>', Q) = nth CsQ i\<rbrakk> \<Longrightarrow> \<phi> = \<phi>' \<and> \<Psi> \<rhd> P \<sim> Q"

  shows "\<Psi> \<rhd> Cases CsP \<sim>\<^sub>s Cases CsQ"
proof -
  {
    fix \<phi> 
    and P

    assume "(\<phi>, P) mem CsP"

    with `length CsP = length CsQ` have "\<exists>Q. (\<phi>, Q) mem CsQ \<and> \<Psi> \<rhd> P \<sim>\<^sub>s Q"
      apply(induct n=="length CsP" arbitrary: CsP CsQ rule: nat.induct)
      apply simp
      apply simp
      apply auto

  }
using `length CsP = length CsQ`
proof(induct n=="length CsP" rule: nat.induct)
  case zero
  thus ?case by(fastforce intro: bisimSubstReflexive)
next
  case(Suc n)
next
apply auto
apply(blast intro: bisimSubstReflexive)
apply auto
apply(simp add: nth.simps)
apply(auto simp add: nth.simps)
apply blast
apply(rule_tac bisimSubstCasePresAux)
apply auto
*)
lemma weakBisimSubstParPres:
  fixes \<Psi> :: 'b
  and   P :: "('a, 'b, 'c) psi"
  and   Q :: "('a, 'b, 'c) psi"
  and   R :: "('a, 'b, 'c) psi"
  
  assumes "\<Psi> \<rhd> P \<approx>\<^sub>s Q"

  shows "\<Psi> \<rhd> P \<parallel> R \<approx>\<^sub>s Q \<parallel> R"
using assms
by(fastforce intro: closeSubstI closeSubstE weakBisimParPres)

lemma weakBisimSubstResPres:
  fixes \<Psi> :: 'b
  and   P :: "('a, 'b, 'c) psi"
  and   Q :: "('a, 'b, 'c) psi"
  and   x :: name

  assumes "\<Psi> \<rhd> P \<approx>\<^sub>s Q"
  and     "x \<sharp> \<Psi>"

  shows "\<Psi> \<rhd> \<lparr>\<nu>x\<rparr>P \<approx>\<^sub>s \<lparr>\<nu>x\<rparr>Q"
proof(rule_tac closeSubstI)
  fix xvec Tvec
  assume "length(xvec::name list) = length(Tvec::'a list)" and "distinct xvec"
  obtain y::name where "y \<sharp> \<Psi>" and "y \<sharp> P" and "y \<sharp> Q" and "y \<sharp> xvec" and "y \<sharp> Tvec"
    by(generate_fresh "name") (auto simp add: fresh_prod)

  from `\<Psi> \<rhd> P \<approx>\<^sub>s Q` have "([(x, y)] \<bullet> \<Psi>) \<rhd> ([(x, y)] \<bullet> P) \<approx>\<^sub>s ([(x, y)] \<bullet> Q)"
    by(rule weakBisimSubstClosed)
  with `x \<sharp> \<Psi>` `y \<sharp> \<Psi>` have "\<Psi> \<rhd> ([(x, y)] \<bullet> P) \<approx>\<^sub>s ([(x, y)] \<bullet> Q)"
    by simp
  hence "\<Psi> \<rhd> ([(x, y)] \<bullet> P)[xvec::=Tvec] \<approx> ([(x, y)] \<bullet> Q)[xvec::=Tvec]" using `length xvec = length Tvec` `distinct xvec`
    by(rule closeSubstE)
  hence "\<Psi> \<rhd> \<lparr>\<nu>y\<rparr>(([(x, y)] \<bullet> P)[xvec::=Tvec]) \<approx> \<lparr>\<nu>y\<rparr>(([(x, y)] \<bullet> Q)[xvec::=Tvec])" using `y \<sharp> \<Psi>`
    by(rule weakBisimResPres)
  with `y \<sharp> P` `y \<sharp> Q` `y \<sharp> xvec` `y \<sharp> Tvec` 
  show "\<Psi> \<rhd> (\<lparr>\<nu>x\<rparr>P)[xvec::=Tvec] \<approx> (\<lparr>\<nu>x\<rparr>Q)[xvec::=Tvec]"
    by(simp add: alphaRes)
qed
(*
lemma bisimSubstBangPres:
  fixes \<Psi> :: 'b
  and   P :: "('a, 'b, 'c) psi"
  and   Q :: "('a, 'b, 'c) psi"
 
  assumes "\<Psi> \<rhd> P \<sim>\<^sub>s Q"
  and     "guarded P"
  and     "guarded Q"

  shows "\<Psi> \<rhd> !P \<sim>\<^sub>s !Q"
using assms
by(fastforce intro: bisimSubstI bisimSubstE bisimBangPres)
*)

lemma weakBisimSubstParNil:
  fixes \<Psi> :: 'b
  and   P :: "('a, 'b, 'c) psi"

  shows "\<Psi> \<rhd> P \<parallel> \<zero> \<approx>\<^sub>s P"
by(metis strongBisimSubstWeakBisimSubst bisimSubstParNil) 

lemma weakBisimSubstParComm:
  fixes \<Psi> :: 'b
  and   P :: "('a, 'b, 'c) psi"
  and   Q :: "('a, 'b, 'c) psi"

  shows "\<Psi> \<rhd> P \<parallel> Q \<approx>\<^sub>s Q \<parallel> P"
by(metis strongBisimSubstWeakBisimSubst bisimSubstParComm) 

lemma weakBisimSubstParAssoc:
  fixes \<Psi> :: 'b
  and   P :: "('a, 'b, 'c) psi"
  and   Q :: "('a, 'b, 'c) psi"
  and   R :: "('a, 'b, 'c) psi"

  shows "\<Psi> \<rhd> (P \<parallel> Q) \<parallel> R \<approx>\<^sub>s P \<parallel> (Q \<parallel> R)"
by(metis strongBisimSubstWeakBisimSubst bisimSubstParAssoc) 

lemma weakBisimSubstResNil:
  fixes \<Psi> :: 'b
  and   x :: name

  shows "\<Psi> \<rhd> \<lparr>\<nu>x\<rparr>\<zero> \<sim>\<^sub>s \<zero>"
by(metis strongBisimSubstWeakBisimSubst bisimSubstResNil) 

lemma weakBisimSubstScopeExt:
  fixes \<Psi> :: 'b
  and   x :: name
  and   P :: "('a, 'b, 'c) psi"
  and   Q :: "('a, 'b, 'c) psi"

  assumes "x \<sharp> P"

  shows "\<Psi> \<rhd> \<lparr>\<nu>x\<rparr>(P \<parallel> Q) \<approx>\<^sub>s P \<parallel> \<lparr>\<nu>x\<rparr>Q" 
using assms
by(metis strongBisimSubstWeakBisimSubst bisimSubstScopeExt) 

lemma weakBisimSubstCasePushRes:
  fixes x  :: name
  and   \<Psi>  :: 'b
  and   Cs :: "('c \<times> ('a, 'b, 'c) psi) list"

  assumes "x \<sharp> map fst Cs"

  shows "\<Psi> \<rhd> \<lparr>\<nu>x\<rparr>(Cases Cs) \<approx>\<^sub>s Cases map (\<lambda>(\<phi>, P). (\<phi>, \<lparr>\<nu>x\<rparr>P)) Cs"
using assms
by(metis strongBisimSubstWeakBisimSubst bisimSubstCasePushRes) 

lemma weakBisimSubstOutputPushRes:
  fixes x :: name
  and   \<Psi> :: 'b
  and   M :: 'a
  and   N :: 'a
  and   P :: "('a, 'b, 'c) psi"

  assumes "x \<sharp> \<Psi>"
  and     "x \<sharp> M"
  and     "x \<sharp> N"

  shows "\<Psi> \<rhd> \<lparr>\<nu>x\<rparr>(M\<langle>N\<rangle>.P) \<approx>\<^sub>s M\<langle>N\<rangle>.\<lparr>\<nu>x\<rparr>P"
using assms
by(metis strongBisimSubstWeakBisimSubst bisimSubstOutputPushRes) 

lemma weakBisimSubstInputPushRes:
  fixes x    :: name
  and   \<Psi>    :: 'b
  and   M    :: 'a
  and   xvec :: "name list"
  and   N    :: 'a

  assumes "x \<sharp> M"
  and     "x \<sharp> xvec"
  and     "x \<sharp> N"

  shows "\<Psi> \<rhd> \<lparr>\<nu>x\<rparr>(M\<lparr>\<lambda>*xvec N\<rparr>.P) \<approx>\<^sub>s M\<lparr>\<lambda>*xvec N\<rparr>.\<lparr>\<nu>x\<rparr>P"
using assms
by(metis strongBisimSubstWeakBisimSubst bisimSubstInputPushRes) 

lemma weakBisimSubstResComm:
  fixes x :: name
  and   y :: name

  shows "\<Psi> \<rhd> \<lparr>\<nu>x\<rparr>(\<lparr>\<nu>y\<rparr>P) \<approx>\<^sub>s \<lparr>\<nu>y\<rparr>(\<lparr>\<nu>x\<rparr>P)"
by(metis strongBisimSubstWeakBisimSubst bisimSubstResComm) 

lemma weakBisimSubstExtBang:
  fixes \<Psi> :: 'b
  and   P :: "('a, 'b, 'c) psi"
  
  assumes "guarded P"

  shows "\<Psi> \<rhd> !P \<approx>\<^sub>s P \<parallel> !P"
using assms
by(metis strongBisimSubstWeakBisimSubst bisimSubstExtBang) 

end

end
