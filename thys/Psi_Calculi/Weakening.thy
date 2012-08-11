(* 
   Title: Psi-calculi   
   Author/Maintainer: Jesper Bengtson (jebe@itu.dk), 2012
*)
theory Weakening
  imports Weak_Bisimulation
begin

locale weak = env + 
  assumes weaken: "\<Psi> \<hookrightarrow> \<Psi> \<otimes> \<Psi>'"
begin

lemma entWeaken:
  fixes \<Psi> :: 'b
  and   \<phi> :: 'c

  assumes "\<Psi> \<turnstile> \<phi>"

  shows "\<Psi> \<otimes> \<Psi>' \<turnstile> \<phi>"
using assms weaken
by(auto simp add: AssertionStatImp_def)

lemma assertWeaken:
  fixes \<Psi>  :: 'b
  and   \<Psi>' :: 'b

  shows "\<Psi> \<hookrightarrow> \<Psi> \<otimes> \<Psi>'"
by(auto simp add: AssertionStatImp_def entWeaken)

lemma frameWeaken:
  fixes F :: "'b frame"
  and   G :: "'b frame"

  shows "F \<hookrightarrow>\<^sub>F F \<otimes>\<^sub>F G"
proof -
  obtain A\<^isub>F \<Psi>\<^isub>F where FrF: "F = \<langle>A\<^isub>F, \<Psi>\<^isub>F\<rangle>" and "A\<^isub>F \<sharp>* F" and  "A\<^isub>F \<sharp>* G"
    by(rule_tac F=F and C="(F, G)" in freshFrame) auto
  obtain A\<^isub>G \<Psi>\<^isub>G where FrG: "G = \<langle>A\<^isub>G, \<Psi>\<^isub>G\<rangle>" and "A\<^isub>G \<sharp>* F" and  "A\<^isub>G \<sharp>* G" and "A\<^isub>G \<sharp>* A\<^isub>F" and "A\<^isub>G \<sharp>* \<Psi>\<^isub>F"
    by(rule_tac F=G and C="(F, G, A\<^isub>F, \<Psi>\<^isub>F)" in freshFrame) auto
  from FrG `A\<^isub>F \<sharp>* G` `A\<^isub>G \<sharp>* A\<^isub>F` have "A\<^isub>F \<sharp>* \<Psi>\<^isub>G" by auto
  have "\<Psi>\<^isub>F \<hookrightarrow> \<Psi>\<^isub>F \<otimes> \<Psi>\<^isub>G" by(rule weaken)
  hence "\<langle>A\<^isub>G, \<Psi>\<^isub>F\<rangle> \<hookrightarrow>\<^sub>F \<langle>A\<^isub>G, \<Psi>\<^isub>F \<otimes> \<Psi>\<^isub>G\<rangle>" by(rule_tac frameImpResChainPres) auto
  with `A\<^isub>G \<sharp>* \<Psi>\<^isub>F` have "\<langle>\<epsilon>, \<Psi>\<^isub>F\<rangle> \<hookrightarrow>\<^sub>F \<langle>A\<^isub>G, \<Psi>\<^isub>F \<otimes> \<Psi>\<^isub>G\<rangle>" using frameResFreshChain
    by(rule_tac FrameStatImpTrans) (auto simp add: FrameStatEq_def)
  with FrF FrG `A\<^isub>G \<sharp>* A\<^isub>F` `A\<^isub>G \<sharp>* \<Psi>\<^isub>F` `A\<^isub>F \<sharp>* \<Psi>\<^isub>G` show ?thesis
    by(force simp add: frameChainAppend intro: frameImpResChainPres)
qed

lemma unitAssertWeaken:
  fixes \<Psi> :: 'b

  shows "\<one> \<hookrightarrow> \<Psi>"
proof -
  have "\<one> \<hookrightarrow> \<one> \<otimes> \<Psi>" by(rule assertWeaken)
  moreover have "\<one> \<otimes> \<Psi> \<hookrightarrow> \<Psi>" by(metis Identity AssertionStatEq_def Commutativity AssertionStatEqTrans)
  ultimately show ?thesis by(rule AssertionStatImpTrans)
qed

lemma unitFrameWeaken:
  fixes F :: "'b frame"

  shows "\<langle>\<epsilon>, \<one>\<rangle> \<hookrightarrow>\<^sub>F F"
proof -
  have "\<langle>\<epsilon>, \<one>\<rangle> \<hookrightarrow>\<^sub>F ((\<langle>\<epsilon>, \<one>\<rangle>) \<otimes>\<^sub>F F)" by(rule frameWeaken)
  moreover obtain A\<^isub>F \<Psi>\<^isub>F where FrF: "F = \<langle>A\<^isub>F, \<Psi>\<^isub>F\<rangle>"
    by(rule_tac F=F and C="()" in freshFrame) auto
  hence "(\<langle>\<epsilon>, \<one>\<rangle>) \<otimes>\<^sub>F F \<simeq>\<^sub>F F" 
    by simp (metis frameIntIdentity frameIntCommutativity FrameStatEqTrans FrameStatEqSym)
  ultimately show ?thesis by(metis FrameStatImpTrans FrameStatEq_def)
qed

lemma insertAssertionWeaken:
  fixes F :: "'b frame"
  and   \<Psi> :: 'b

  shows "\<langle>\<epsilon>, \<Psi>\<rangle> \<hookrightarrow>\<^sub>F insertAssertion F \<Psi>"
proof -
  have "\<langle>\<epsilon>, \<Psi>\<rangle> \<hookrightarrow>\<^sub>F (\<langle>\<epsilon>, \<Psi>\<rangle>) \<otimes>\<^sub>F F" by(rule frameWeaken)
  thus ?thesis by simp
qed

lemma frameImpStatEq:
  fixes A\<^isub>F  :: "name list"
  and   \<Psi>  :: 'b
  and   \<Psi>' :: 'b
  and   \<phi>  :: 'c

  assumes "(\<langle>A\<^isub>F, \<Psi>\<rangle>) \<turnstile>\<^sub>F \<phi>"
  and     "\<Psi> \<simeq> \<Psi>'"

  shows "(\<langle>A\<^isub>F, \<Psi>'\<rangle>) \<turnstile>\<^sub>F \<phi>"
proof -
  obtain p::"name prm" where "(p \<bullet> A\<^isub>F) \<sharp>* \<phi>" and "(p \<bullet> A\<^isub>F) \<sharp>* \<Psi>" and "(p \<bullet> A\<^isub>F) \<sharp>* \<Psi>'"
                         and "distinctPerm p" and S: "set p \<subseteq> set A\<^isub>F \<times> set(p \<bullet> A\<^isub>F)"
    by(rule_tac c="(\<phi>, \<Psi>, \<Psi>')" in name_list_avoiding) auto
  from `(\<langle>A\<^isub>F, \<Psi>\<rangle>) \<turnstile>\<^sub>F \<phi>` `(p \<bullet> A\<^isub>F) \<sharp>* \<Psi>` S have "(\<langle>(p \<bullet> A\<^isub>F), p \<bullet> \<Psi>\<rangle>) \<turnstile>\<^sub>F \<phi>" by(simp add: frameChainAlpha)
  hence "(p \<bullet> \<Psi>) \<turnstile> \<phi>" using `(p \<bullet> A\<^isub>F) \<sharp>* \<phi>` by(rule frameImpE)
  moreover from `\<Psi> \<simeq> \<Psi>'` have "(p \<bullet> \<Psi>) \<simeq> (p \<bullet> \<Psi>')" by(rule AssertionStatEqClosed)
  ultimately have "(p \<bullet> \<Psi>') \<turnstile> \<phi>" by(simp add: AssertionStatEq_def AssertionStatImp_def)
  hence "(\<langle>(p \<bullet> A\<^isub>F), p \<bullet> \<Psi>'\<rangle>) \<turnstile>\<^sub>F \<phi>" using `(p \<bullet> A\<^isub>F) \<sharp>* \<phi>` 
    by(rule_tac frameImpI) auto
  with `(p \<bullet> A\<^isub>F) \<sharp>* \<Psi>'` S show ?thesis by(simp add: frameChainAlpha)
qed

lemma statImpTauDerivative:
  fixes \<Psi>   :: 'b
  and   P    :: "('a, 'b, 'c) psi"
  and   P'   :: "('a, 'b, 'c) psi"

  assumes "\<Psi> \<rhd> P \<longmapsto>\<tau> \<prec> P'"

  shows "insertAssertion (extractFrame P) \<Psi> \<hookrightarrow>\<^sub>F insertAssertion (extractFrame P') \<Psi>"
proof(auto simp add: FrameStatImp_def)
  fix \<phi> :: 'c
  obtain A\<^isub>P \<Psi>\<^isub>P where FrP: "extractFrame P = \<langle>A\<^isub>P, \<Psi>\<^isub>P\<rangle>" and "A\<^isub>P \<sharp>* P" and "A\<^isub>P \<sharp>* \<phi>" and "A\<^isub>P \<sharp>* \<Psi>" and "distinct A\<^isub>P" 
    by(rule_tac C="(P, \<phi>, \<Psi>)" in freshFrame) auto
  with `\<Psi> \<rhd> P \<longmapsto>\<tau> \<prec> P'` obtain \<Psi>' A\<^isub>P' \<Psi>\<^isub>P' where FrP': "extractFrame P' = \<langle>A\<^isub>P', \<Psi>\<^isub>P'\<rangle>" and "\<Psi>\<^isub>P \<otimes> \<Psi>' \<simeq> \<Psi>\<^isub>P'" 
                                              and "A\<^isub>P' \<sharp>* P'" and "A\<^isub>P' \<sharp>* \<phi>"  and "A\<^isub>P' \<sharp>* \<Psi>" 
    by(rule_tac C="(\<Psi>, \<phi>)" in expandTauFrame) auto
  assume "insertAssertion (extractFrame P) \<Psi> \<turnstile>\<^sub>F \<phi>"
  with FrP `A\<^isub>P \<sharp>* \<phi>` `A\<^isub>P \<sharp>* \<Psi>` have "\<Psi> \<otimes> \<Psi>\<^isub>P \<turnstile> \<phi>" by(auto dest: frameImpE)
  hence "(\<Psi> \<otimes> \<Psi>\<^isub>P) \<otimes> \<Psi>' \<turnstile> \<phi>" by(rule entWeaken)
  hence "\<Psi> \<otimes> \<Psi>\<^isub>P' \<turnstile> \<phi>" using `\<Psi>\<^isub>P \<otimes> \<Psi>' \<simeq> \<Psi>\<^isub>P'`
    by(rule_tac statEqEnt, auto) (metis Associativity compositionSym AssertionStatEqTrans AssertionStatEqSym Commutativity)
  with `A\<^isub>P' \<sharp>* \<phi>` `A\<^isub>P' \<sharp>* \<Psi>` FrP' show "insertAssertion (extractFrame P') \<Psi> \<turnstile>\<^sub>F \<phi>"
    by(force intro: frameImpI)
qed

lemma weakenTransition:
  fixes \<Psi>  :: 'b
  and   P  :: "('a, 'b, 'c) psi"
  and   Rs :: "('a, 'b, 'c) residual"
  and   \<Psi>' :: 'b

  assumes "\<Psi> \<rhd> P \<longmapsto> Rs"

  shows "\<Psi> \<otimes> \<Psi>' \<rhd> P \<longmapsto> Rs"
using assms
proof(nominal_induct avoiding: \<Psi>' rule: semantics.strong_induct)
  case(cInput \<Psi> M K xvec N Tvec P \<Psi>')
  from `\<Psi> \<turnstile> M \<leftrightarrow> K` have "\<Psi> \<otimes> \<Psi>' \<turnstile> M \<leftrightarrow> K" by(rule entWeaken)
  thus ?case using `distinct xvec` `set xvec \<subseteq> (supp N)` `length xvec = length Tvec` 
    by(rule Input)
next
  case(Output \<Psi> M K N P \<Psi>')
  from `\<Psi> \<turnstile> M \<leftrightarrow> K` have "\<Psi> \<otimes> \<Psi>' \<turnstile> M \<leftrightarrow> K" by(rule entWeaken)
  thus ?case by(rule semantics.Output)
next
  case(Case \<Psi> P Rs \<phi> Cs \<Psi>')
  have "\<Psi> \<otimes> \<Psi>' \<rhd> P \<longmapsto> Rs" by(rule Case)
  moreover note `(\<phi>, P) mem Cs`
  moreover from `\<Psi> \<turnstile> \<phi>` have "\<Psi> \<otimes> \<Psi>' \<turnstile> \<phi>" by(rule entWeaken)
  ultimately show ?case using `guarded P`
    by(rule semantics.Case)
next
  case(cPar1 \<Psi> \<Psi>\<^isub>Q P \<alpha> P' Q A\<^isub>Q \<Psi>')
  have "(\<Psi> \<otimes> \<Psi>\<^isub>Q) \<otimes> \<Psi>' \<rhd> P \<longmapsto>\<alpha> \<prec> P'" by(rule cPar1)
  hence "(\<Psi> \<otimes> \<Psi>') \<otimes> \<Psi>\<^isub>Q \<rhd> P \<longmapsto>\<alpha> \<prec> P'"
    by(metis statEqTransition Composition Associativity Commutativity AssertionStatEqTrans)
  thus ?case using `extractFrame Q = \<langle>A\<^isub>Q, \<Psi>\<^isub>Q\<rangle>` `bn \<alpha> \<sharp>* Q` `A\<^isub>Q \<sharp>* \<Psi>` `A\<^isub>Q \<sharp>* \<Psi>'` `A\<^isub>Q \<sharp>* P` `A\<^isub>Q \<sharp>* \<alpha>`
    by(rule_tac Par1) auto
next
  case(cPar2 \<Psi> \<Psi>\<^isub>P Q \<alpha> Q' P A\<^isub>P \<Psi>')
  have "(\<Psi> \<otimes> \<Psi>\<^isub>P) \<otimes> \<Psi>' \<rhd> Q \<longmapsto>\<alpha> \<prec> Q'" by(rule cPar2)
  hence "(\<Psi> \<otimes> \<Psi>') \<otimes> \<Psi>\<^isub>P \<rhd> Q \<longmapsto>\<alpha> \<prec> Q'"
    by(metis statEqTransition Composition Associativity Commutativity AssertionStatEqTrans)
  thus ?case using `extractFrame P = \<langle>A\<^isub>P, \<Psi>\<^isub>P\<rangle>` `bn \<alpha> \<sharp>* P` `A\<^isub>P \<sharp>* \<Psi>` `A\<^isub>P \<sharp>* \<Psi>'` `A\<^isub>P \<sharp>* Q` `A\<^isub>P \<sharp>* \<alpha>`
    by(rule_tac Par2) auto
next
  case(cComm1 \<Psi> \<Psi>\<^isub>Q P M N P' A\<^isub>P \<Psi>\<^isub>P Q K xvec Q' A\<^isub>Q \<Psi>')
  have "(\<Psi> \<otimes> \<Psi>\<^isub>Q) \<otimes> \<Psi>' \<rhd> P \<longmapsto>M\<lparr>N\<rparr> \<prec> P'" by(rule cComm1)
  hence "(\<Psi> \<otimes> \<Psi>') \<otimes> \<Psi>\<^isub>Q \<rhd> P \<longmapsto>M\<lparr>N\<rparr> \<prec> P'"
    by(metis statEqTransition Composition Associativity Commutativity AssertionStatEqTrans)
  moreover note `extractFrame P = \<langle>A\<^isub>P, \<Psi>\<^isub>P\<rangle>`
  moreover have "(\<Psi> \<otimes> \<Psi>\<^isub>P) \<otimes> \<Psi>' \<rhd> Q \<longmapsto>K\<lparr>\<nu>*xvec\<rparr>\<langle>N\<rangle> \<prec> Q'" by(rule cComm1)
  hence "(\<Psi> \<otimes> \<Psi>') \<otimes> \<Psi>\<^isub>P \<rhd> Q \<longmapsto>K\<lparr>\<nu>*xvec\<rparr>\<langle>N\<rangle> \<prec> Q'"
    by(metis statEqTransition Composition Associativity Commutativity AssertionStatEqTrans)
  moreover note `extractFrame Q = \<langle>A\<^isub>Q, \<Psi>\<^isub>Q\<rangle>`
  moreover from `\<Psi> \<otimes> \<Psi>\<^isub>P \<otimes> \<Psi>\<^isub>Q \<turnstile> M \<leftrightarrow> K` have "(\<Psi> \<otimes> \<Psi>\<^isub>P \<otimes> \<Psi>\<^isub>Q) \<otimes> \<Psi>' \<turnstile> M \<leftrightarrow> K" by(rule entWeaken)
  hence "(\<Psi> \<otimes> \<Psi>') \<otimes> \<Psi>\<^isub>P \<otimes> \<Psi>\<^isub>Q \<turnstile> M \<leftrightarrow> K" by(metis statEqEnt Composition Associativity Commutativity AssertionStatEqTrans)
  ultimately show ?case using `A\<^isub>P \<sharp>* \<Psi>` `A\<^isub>P \<sharp>* \<Psi>'` `A\<^isub>P \<sharp>* P` `A\<^isub>P \<sharp>* Q` `A\<^isub>P \<sharp>* M` `A\<^isub>P \<sharp>* A\<^isub>Q`
                              `A\<^isub>Q \<sharp>* \<Psi>` `A\<^isub>Q \<sharp>* \<Psi>'` `A\<^isub>Q \<sharp>* P` `A\<^isub>Q \<sharp>* Q` `A\<^isub>Q \<sharp>* K` `xvec \<sharp>* P`
    by(rule_tac Comm1) (assumption | auto)+
next
  case(cComm2 \<Psi> \<Psi>\<^isub>Q P M xvec N P' A\<^isub>P \<Psi>\<^isub>P Q K Q' A\<^isub>Q \<Psi>')
  have "(\<Psi> \<otimes> \<Psi>\<^isub>Q) \<otimes> \<Psi>' \<rhd> P \<longmapsto>M\<lparr>\<nu>*xvec\<rparr>\<langle>N\<rangle> \<prec> P'" by(rule cComm2)
  hence "(\<Psi> \<otimes> \<Psi>') \<otimes> \<Psi>\<^isub>Q \<rhd> P \<longmapsto>M\<lparr>\<nu>*xvec\<rparr>\<langle>N\<rangle> \<prec> P'"
    by(metis statEqTransition Composition Associativity Commutativity AssertionStatEqTrans)
  moreover note `extractFrame P = \<langle>A\<^isub>P, \<Psi>\<^isub>P\<rangle>`
  moreover have "(\<Psi> \<otimes> \<Psi>\<^isub>P) \<otimes> \<Psi>' \<rhd> Q \<longmapsto>K\<lparr>N\<rparr> \<prec> Q'" by(rule cComm2)
  hence "(\<Psi> \<otimes> \<Psi>') \<otimes> \<Psi>\<^isub>P \<rhd> Q \<longmapsto>K\<lparr>N\<rparr> \<prec> Q'"
    by(metis statEqTransition Composition Associativity Commutativity AssertionStatEqTrans)
  moreover note `extractFrame Q = \<langle>A\<^isub>Q, \<Psi>\<^isub>Q\<rangle>`
  moreover from `\<Psi> \<otimes> \<Psi>\<^isub>P \<otimes> \<Psi>\<^isub>Q \<turnstile> M \<leftrightarrow> K` have "(\<Psi> \<otimes> \<Psi>\<^isub>P \<otimes> \<Psi>\<^isub>Q) \<otimes> \<Psi>' \<turnstile> M \<leftrightarrow> K" by(rule entWeaken)
  hence "(\<Psi> \<otimes> \<Psi>') \<otimes> \<Psi>\<^isub>P \<otimes> \<Psi>\<^isub>Q \<turnstile> M \<leftrightarrow> K" by(metis statEqEnt Composition Associativity Commutativity AssertionStatEqTrans)
  ultimately show ?case using `A\<^isub>P \<sharp>* \<Psi>` `A\<^isub>P \<sharp>* \<Psi>'` `A\<^isub>P \<sharp>* P` `A\<^isub>P \<sharp>* Q` `A\<^isub>P \<sharp>* M` `A\<^isub>P \<sharp>* A\<^isub>Q`
                              `A\<^isub>Q \<sharp>* \<Psi>` `A\<^isub>Q \<sharp>* \<Psi>'` `A\<^isub>Q \<sharp>* P` `A\<^isub>Q \<sharp>* Q` `A\<^isub>Q \<sharp>* K` `xvec \<sharp>* Q`
    by(rule_tac Comm2) (assumption | auto)+
next
  case(cOpen \<Psi> P M xvec yvec N P' x \<Psi>')
  have "\<Psi> \<otimes> \<Psi>' \<rhd> P \<longmapsto>M\<lparr>\<nu>*(xvec@yvec)\<rparr>\<langle>N\<rangle> \<prec> P'" by(rule cOpen)
  thus ?case using `x \<in> supp N` `x \<sharp> \<Psi>` `x \<sharp> \<Psi>'` `x \<sharp> M` `x \<sharp> xvec` `x \<sharp> yvec`
    by(rule_tac Open) auto
next  
  case(cScope \<Psi> P \<alpha> P' x \<Psi>')
  have "\<Psi> \<otimes> \<Psi>' \<rhd> P \<longmapsto>\<alpha> \<prec> P'" by(rule cScope)
  thus ?case using `x \<sharp> \<Psi>` `x \<sharp> \<Psi>'` `x \<sharp> \<alpha>` by(rule_tac Scope) auto
next
  case(Bang \<Psi> P Rs \<Psi>')
  have "\<Psi> \<otimes> \<Psi>' \<rhd> P \<parallel> !P\<longmapsto> Rs" by(rule Bang)
  thus ?case using `guarded P` by(rule semantics.Bang)
qed

end

end
