(* 
   Title: Psi-calculi   
   Author/Maintainer: Jesper Bengtson (jebe@itu.dk), 2012
*)
theory Weak_Stat_Imp_Pres
  imports Weak_Stat_Imp
begin

context env begin

lemma weakStatImpInputPres:
  fixes \<Psi>    :: 'b
  and   P    :: "('a, 'b, 'c) psi"
  and   Rel  :: "('b \<times> ('a, 'b, 'c) psi \<times> ('a, 'b, 'c) psi) set"
  and   Q    :: "('a, 'b, 'c) psi"
  and   M    :: 'a
  and   xvec :: "name list"
  and   N    :: 'a

  assumes PRelQ: "\<And>\<Psi>'. (\<Psi> \<otimes> \<Psi>', M\<lparr>\<lambda>*xvec N\<rparr>.P, M\<lparr>\<lambda>*xvec N\<rparr>.Q) \<in> Rel"

  shows "\<Psi> \<rhd> M\<lparr>\<lambda>*xvec N\<rparr>.P \<lessapprox><Rel> M\<lparr>\<lambda>*xvec N\<rparr>.Q"
using assms
by(fastforce simp add: weakStatImp_def)

lemma weakStatImpOutputPres:
  fixes \<Psi>   :: 'b
  and   P   :: "('a, 'b, 'c) psi"
  and   Rel :: "('b \<times> ('a, 'b, 'c) psi \<times> ('a, 'b, 'c) psi) set"
  and   Q   :: "('a, 'b, 'c) psi"
  and   M   :: 'a
  and   N   :: 'a

  assumes PRelQ: "\<And>\<Psi>'. (\<Psi> \<otimes> \<Psi>', M\<langle>N\<rangle>.P, M\<langle>N\<rangle>.Q) \<in> Rel"

  shows "\<Psi> \<rhd> M\<langle>N\<rangle>.P \<lessapprox><Rel> M\<langle>N\<rangle>.Q"
using assms
by(fastforce simp add: weakStatImp_def)
(*
lemma weakStatImpCasePres:
  fixes \<Psi>    :: 'b
  and   CsP  :: "('c \<times> ('a, 'b, 'c) psi) list"
  and   Rel  :: "('b \<times> ('a, 'b, 'c) psi \<times> ('a, 'b, 'c) psi) set"
  and   CsQ  :: "('c \<times> ('a, 'b, 'c) psi) list"
  and   M    :: 'a
  and   N    :: 'a

  assumes PRelQ: "\<And>\<phi> Q. (\<phi>, Q) mem CsQ \<Longrightarrow> \<exists>P. (\<phi>, P) mem CsP \<and> guarded P \<and> Eq P Q"
  and     Sim:   "\<And>\<Psi> P Q. (\<Psi>, P, Q) \<in> Rel \<Longrightarrow> \<Psi> \<rhd> P \<lessapprox><Rel> Q"
  and     EqRel: "\<And>\<Psi> P Q. Eq P Q \<Longrightarrow> (\<Psi>, P, Q) \<in> Rel"

  shows "\<Psi> \<rhd> Cases CsP \<lessapprox><Rel> Cases CsQ"
using assms
apply(auto simp add: weakStatImp_def)
apply(rule_tac x="Cases CsQ" in exI)
apply auto
apply(rule_tac x="Cases CsQ" in exI)
apply auto
apply blast
proof(induct rule: weakSimI2)
  case(cAct \<Psi>' \<alpha> Q')
  from `bn \<alpha> \<sharp>* (Cases CsP)` have "bn \<alpha> \<sharp>* CsP" by auto
  from `\<Psi> \<rhd> Cases CsQ \<longmapsto>\<alpha> \<prec> Q'`
  show ?case
  proof(induct rule: caseCases)
    case(cCase \<phi> Q)
    from `(\<phi>, Q) mem CsQ` obtain P where "(\<phi>, P) mem CsP" and "guarded P" and "Eq P Q"
      by(metis PRelQ)
    from `Eq P Q` have "\<Psi> \<rhd> P \<leadsto><Rel> Q" by(metis EqRel Sim)
    moreover note `\<Psi> \<rhd> Q \<longmapsto>\<alpha> \<prec> Q'` `bn \<alpha> \<sharp>* \<Psi>`
    moreover from `bn \<alpha> \<sharp>* CsP` `(\<phi>, P) mem CsP` have "bn \<alpha> \<sharp>* P" by(auto dest: memFreshChain)
    ultimately obtain P'' P' where PTrans: "\<Psi> : Q \<rhd> P \<Longrightarrow>\<alpha> \<prec> P''"
                               and P''Chain: "\<Psi> \<otimes> \<Psi>' \<rhd> P'' \<Longrightarrow>\<^sup>^\<^sub>\<tau> P'" and P'RelQ': "(\<Psi> \<otimes> \<Psi>', P', Q') \<in> Rel"
      using `\<alpha> \<noteq> \<tau>`
      by(blast dest: weakSimE)
    note PTrans `(\<phi>, P) mem CsP` `\<Psi> \<turnstile> \<phi>` `guarded P`
    moreover from `guarded Q` have "insertAssertion (extractFrame Q) \<Psi> \<simeq>\<^sub>F \<langle>\<epsilon>, \<Psi> \<otimes> \<one>\<rangle>"
      by(rule insertGuardedAssertion)
    hence "insertAssertion (extractFrame(Cases CsQ)) \<Psi> \<hookrightarrow>\<^sub>F insertAssertion (extractFrame Q) \<Psi>"
      by(auto simp add: FrameStatEq_def)
    moreover from Identity have "insertAssertion (extractFrame(Cases CsQ)) \<Psi> \<hookrightarrow>\<^sub>F \<langle>\<epsilon>, \<Psi>\<rangle>"
      by(auto simp add: AssertionStatEq_def)
    ultimately have "\<Psi> : (Cases CsQ) \<rhd> Cases CsP \<Longrightarrow>\<alpha> \<prec> P''"
      by(rule weakCase)
    with P''Chain P'RelQ' show ?case by blast
  qed
next
  case(cTau Q')
  from `\<Psi> \<rhd> Cases CsQ \<longmapsto>\<tau> \<prec> Q'` show ?case
  proof(induct rule: caseCases)
    case(cCase \<phi> Q)
    from `(\<phi>, Q) mem CsQ` obtain P where "(\<phi>, P) mem CsP" and "guarded P" and "Eq P Q"
      by(metis PRelQ)
    from `Eq P Q` `\<Psi> \<rhd> Q \<longmapsto>\<tau> \<prec> Q'`
    obtain P' where PChain: "\<Psi> \<rhd> P \<Longrightarrow>\<^sub>\<tau> P'" and P'RelQ': "(\<Psi>, P', Q') \<in> Rel"
      by(blast dest: EqSim weakCongSimE)
    from PChain `(\<phi>, P) mem CsP` `\<Psi> \<turnstile> \<phi>` `guarded P` have "\<Psi> \<rhd> Cases CsP \<Longrightarrow>\<^sub>\<tau> P'"
      by(rule tauStepChainCase)
    hence "\<Psi> \<rhd> Cases CsP \<Longrightarrow>\<^sup>^\<^sub>\<tau> P'" by(simp add: trancl_into_rtrancl)
    with P'RelQ' show ?case by blast
  qed
qed
*)
lemma weakStatImpResPres:
  fixes \<Psi>    :: 'b
  and   P    :: "('a, 'b, 'c) psi"
  and   Rel  :: "('b \<times> ('a, 'b, 'c) psi \<times> ('a, 'b, 'c) psi) set"
  and   Q    :: "('a, 'b, 'c) psi"
  and   x    :: name
  and   Rel' :: "('b \<times> ('a, 'b, 'c) psi \<times> ('a, 'b, 'c) psi) set"

  assumes PSimQ: "\<Psi> \<rhd> P \<lessapprox><Rel> Q"
  and     "eqvt Rel"
  and     "x \<sharp> \<Psi>"
  and     C1: "\<And>\<Psi>' R S y. \<lbrakk>(\<Psi>', R, S) \<in> Rel; y \<sharp> \<Psi>'\<rbrakk> \<Longrightarrow> (\<Psi>', \<lparr>\<nu>y\<rparr>R, \<lparr>\<nu>y\<rparr>S) \<in> Rel'"

  shows   "\<Psi> \<rhd> \<lparr>\<nu>x\<rparr>P \<lessapprox><Rel'> \<lparr>\<nu>x\<rparr>Q"
proof(induct rule: weakStatImpI)
  case(cStatImp \<Psi>')
  obtain y::name where "y \<sharp> \<Psi>" and "y \<sharp> \<Psi>'" and "y \<sharp> P" and "y \<sharp> Q" by(generate_fresh "name") auto
  from `eqvt Rel` `\<Psi> \<rhd> P \<lessapprox><Rel> Q`  have "([(x, y)] \<bullet> \<Psi>) \<rhd> ([(x, y)] \<bullet> P) \<lessapprox><Rel> ([(x, y)] \<bullet> Q)" by(rule weakStatImpClosed)
  with `x \<sharp> \<Psi>` `y \<sharp> \<Psi>` have "\<Psi> \<rhd> ([(x, y)] \<bullet> P) \<lessapprox><Rel> ([(x, y)] \<bullet> Q)" by simp
  then obtain Q' Q'' where QChain: "\<Psi> \<rhd> ([(x, y)] \<bullet> Q) \<Longrightarrow>\<^sup>^\<^sub>\<tau> Q'"
                       and PimpQ': "insertAssertion (extractFrame ([(x, y)] \<bullet> P)) \<Psi> \<hookrightarrow>\<^sub>F insertAssertion (extractFrame Q') \<Psi>"
                       and Q'Chain: "\<Psi> \<otimes> \<Psi>' \<rhd> Q' \<Longrightarrow>\<^sup>^\<^sub>\<tau> Q''" and "(\<Psi> \<otimes> \<Psi>', ([(x, y)] \<bullet> P), Q'') \<in> Rel"
    by(rule weakStatImpE)
  from QChain `y \<sharp> \<Psi>` have "\<Psi> \<rhd> \<lparr>\<nu>y\<rparr>([(x, y)] \<bullet> Q) \<Longrightarrow>\<^sup>^\<^sub>\<tau> \<lparr>\<nu>y\<rparr>Q'" by(rule tauChainResPres)
  with `y \<sharp> Q` have "\<Psi> \<rhd> \<lparr>\<nu>x\<rparr>Q \<Longrightarrow>\<^sup>^\<^sub>\<tau> \<lparr>\<nu>y\<rparr>Q'" by(simp add: alphaRes)
  moreover from PimpQ' `y \<sharp> \<Psi>` have "insertAssertion (extractFrame(\<lparr>\<nu>y\<rparr>([(x, y)] \<bullet> P))) \<Psi> \<hookrightarrow>\<^sub>F insertAssertion (extractFrame(\<lparr>\<nu>y\<rparr>Q')) \<Psi>"
    by(force intro: frameImpResPres)
  with `y \<sharp> P` have "insertAssertion (extractFrame(\<lparr>\<nu>x\<rparr>P)) \<Psi> \<hookrightarrow>\<^sub>F insertAssertion (extractFrame(\<lparr>\<nu>y\<rparr>Q')) \<Psi>"
    by(simp add: alphaRes)
  moreover from Q'Chain `y \<sharp> \<Psi>` `y \<sharp> \<Psi>'` have "\<Psi> \<otimes> \<Psi>' \<rhd> \<lparr>\<nu>y\<rparr>Q' \<Longrightarrow>\<^sup>^\<^sub>\<tau> \<lparr>\<nu>y\<rparr>Q''" by(rule_tac tauChainResPres) auto
  moreover from `(\<Psi> \<otimes> \<Psi>', ([(x, y)] \<bullet> P), Q'') \<in> Rel` `y \<sharp> \<Psi>` `y \<sharp> \<Psi>'` have "(\<Psi> \<otimes> \<Psi>', \<lparr>\<nu>y\<rparr>([(x, y)] \<bullet> P), \<lparr>\<nu>y\<rparr>Q'') \<in> Rel'" 
    by(blast intro: C1)
  with `y \<sharp> P` have "(\<Psi> \<otimes> \<Psi>', \<lparr>\<nu>x\<rparr>P, \<lparr>\<nu>y\<rparr>Q'') \<in> Rel'" by(simp add: alphaRes)
  ultimately show ?case
    by blast
qed

lemma weakStatImpParPres:
  fixes \<Psi>    :: 'b
  and   P    :: "('a, 'b, 'c) psi"
  and   Rel  :: "('b \<times> ('a, 'b, 'c) psi \<times> ('a, 'b, 'c) psi) set"
  and   Q    :: "('a, 'b, 'c) psi"
  and   R    :: "('a, 'b, 'c) psi"
  and   Rel' :: "('b \<times> ('a, 'b, 'c) psi \<times> ('a, 'b, 'c) psi) set"
  
  assumes PStatImpQ: "\<And>A\<^sub>R \<Psi>\<^sub>R. \<lbrakk>extractFrame R = \<langle>A\<^sub>R, \<Psi>\<^sub>R\<rangle>; A\<^sub>R \<sharp>* \<Psi>; A\<^sub>R \<sharp>* P; A\<^sub>R \<sharp>* Q\<rbrakk> \<Longrightarrow> \<Psi> \<otimes> \<Psi>\<^sub>R \<rhd> P \<lessapprox><Rel> Q"
  and     "xvec \<sharp>* \<Psi>"
  and     Eqvt:  "eqvt Rel"

  and     C1: "\<And>\<Psi>' S T A\<^sub>U \<Psi>\<^sub>U U. \<lbrakk>(\<Psi>' \<otimes> \<Psi>\<^sub>U, S, T) \<in> Rel; extractFrame U = \<langle>A\<^sub>U, \<Psi>\<^sub>U\<rangle>; A\<^sub>U \<sharp>* \<Psi>'; A\<^sub>U \<sharp>* S; A\<^sub>U \<sharp>* T\<rbrakk> \<Longrightarrow> (\<Psi>', S \<parallel> U, T \<parallel> U) \<in> Rel'"
  and     C2: "\<And>\<Psi>' S T yvec. \<lbrakk>(\<Psi>', S, T) \<in> Rel'; yvec \<sharp>* \<Psi>'\<rbrakk> \<Longrightarrow> (\<Psi>', \<lparr>\<nu>*yvec\<rparr>S, \<lparr>\<nu>*yvec\<rparr>T) \<in> Rel'"
  and     C3: "\<And>\<Psi>' S T \<Psi>''. \<lbrakk>(\<Psi>', S, T) \<in> Rel; \<Psi>' \<simeq> \<Psi>''\<rbrakk> \<Longrightarrow> (\<Psi>'', S, T) \<in> Rel"

  shows "\<Psi> \<rhd> \<lparr>\<nu>*xvec\<rparr>(P \<parallel> R) \<lessapprox><Rel'> \<lparr>\<nu>*xvec\<rparr>(Q \<parallel> R)"
proof(induct rule: weakStatImpI)
  case(cStatImp \<Psi>')
  obtain A\<^sub>R \<Psi>\<^sub>R where FrR: "extractFrame R = \<langle>A\<^sub>R, \<Psi>\<^sub>R\<rangle>" and "A\<^sub>R \<sharp>* \<Psi>" and "A\<^sub>R \<sharp>* \<Psi>'" and "A\<^sub>R \<sharp>* P" and "A\<^sub>R \<sharp>* Q" and "A\<^sub>R \<sharp>* R" and "A\<^sub>R \<sharp>* xvec"
    by(rule_tac F="extractFrame R" and C="(xvec, \<Psi>, \<Psi>', P, Q, R, xvec)" in freshFrame) auto

  hence "\<Psi> \<otimes> \<Psi>\<^sub>R \<rhd> P \<lessapprox><Rel> Q" by(rule_tac PStatImpQ)
    
  obtain p::"name prm" where "(p \<bullet> xvec) \<sharp>* P" and "(p \<bullet> xvec) \<sharp>* Q" and "(p \<bullet> xvec) \<sharp>* \<Psi>" and "(p \<bullet> xvec) \<sharp>* \<Psi>'" and  "(p \<bullet> xvec) \<sharp>* \<Psi>\<^sub>R" 
                         and  "(p \<bullet> xvec) \<sharp>* A\<^sub>R" and "(p \<bullet> xvec) \<sharp>* R" and "(p \<bullet> xvec) \<sharp>* P"
                         and "distinctPerm p" and S: "set p \<subseteq> set xvec \<times> set (p \<bullet> xvec)"
    by(rule_tac c="(P, Q, R, \<Psi>, \<Psi>', A\<^sub>R, \<Psi>\<^sub>R, P)" in name_list_avoiding) auto
    
  from FrR have "(p \<bullet> extractFrame R) = (p \<bullet> \<langle>A\<^sub>R, \<Psi>\<^sub>R\<rangle>)" by(rule pt_bij3)
  with `A\<^sub>R \<sharp>* xvec` `(p \<bullet> xvec) \<sharp>* A\<^sub>R` S have FrpR: "extractFrame(p \<bullet> R) = \<langle>A\<^sub>R, p \<bullet> \<Psi>\<^sub>R\<rangle>" by(simp add: eqvts)
  from `eqvt Rel` `\<Psi> \<otimes> \<Psi>\<^sub>R \<rhd> P \<lessapprox><Rel> Q` have "(p \<bullet> (\<Psi> \<otimes> \<Psi>\<^sub>R)) \<rhd> (p \<bullet> P) \<lessapprox><Rel> (p \<bullet> Q)" by(rule weakStatImpClosed)
  with `xvec \<sharp>* \<Psi>` `(p \<bullet> xvec) \<sharp>* \<Psi>` S have "\<Psi> \<otimes> (p \<bullet> \<Psi>\<^sub>R) \<rhd> (p \<bullet> P) \<lessapprox><Rel> (p \<bullet> Q)" by(simp add: eqvts)
  then obtain Q' Q'' where QChain: "\<Psi> \<otimes> (p \<bullet> \<Psi>\<^sub>R) \<rhd> (p \<bullet> Q) \<Longrightarrow>\<^sup>^\<^sub>\<tau> Q'"
                       and PimpQ': "insertAssertion (extractFrame (p \<bullet> P)) (\<Psi> \<otimes> (p \<bullet> \<Psi>\<^sub>R)) \<hookrightarrow>\<^sub>F insertAssertion (extractFrame Q') (\<Psi> \<otimes> (p \<bullet> \<Psi>\<^sub>R))"
                       and Q'Chain: "(\<Psi> \<otimes> (p \<bullet> \<Psi>\<^sub>R)) \<otimes> \<Psi>' \<rhd> Q' \<Longrightarrow>\<^sup>^\<^sub>\<tau> Q''" and "((\<Psi> \<otimes> (p \<bullet> \<Psi>\<^sub>R)) \<otimes> \<Psi>', (p \<bullet> P), Q'') \<in> Rel"
    by(rule weakStatImpE)
    
  from `A\<^sub>R \<sharp>* xvec` `(p \<bullet> xvec) \<sharp>* A\<^sub>R` `A\<^sub>R \<sharp>* Q` S have "A\<^sub>R \<sharp>* (p \<bullet> Q)" by(simp add: freshChainSimps)
  moreover from `(p \<bullet> xvec) \<sharp>* Q` have "(p \<bullet> p \<bullet> xvec) \<sharp>* (p \<bullet> Q)"
    by(simp only: pt_fresh_star_bij[OF pt_name_inst, OF at_name_inst])
  hence "xvec \<sharp>* (p \<bullet> Q)" using `distinctPerm p` by simp
  ultimately have "A\<^sub>R \<sharp>* Q'" and "A\<^sub>R \<sharp>* Q''" and "xvec \<sharp>* Q'" and "xvec \<sharp>* Q''" using QChain Q'Chain
    by(metis tauChainFreshChain)+

  obtain A\<^sub>P \<Psi>\<^sub>P where FrP: "extractFrame(p \<bullet> P) = \<langle>A\<^sub>P, \<Psi>\<^sub>P\<rangle>" and "A\<^sub>P \<sharp>* \<Psi>" "A\<^sub>P \<sharp>* \<Psi>'" and "A\<^sub>P \<sharp>* A\<^sub>R" and "A\<^sub>P \<sharp>* (p \<bullet> \<Psi>\<^sub>R)"
    by(rule_tac C="(\<Psi>, \<Psi>', A\<^sub>R, p \<bullet> \<Psi>\<^sub>R)" in freshFrame) auto
  obtain A\<^sub>Q' \<Psi>\<^sub>Q' where FrQ': "extractFrame Q' = \<langle>A\<^sub>Q', \<Psi>\<^sub>Q'\<rangle>" and "A\<^sub>Q' \<sharp>* \<Psi>"and "A\<^sub>Q' \<sharp>* \<Psi>'" and "A\<^sub>Q' \<sharp>* A\<^sub>R" and "A\<^sub>Q' \<sharp>* (p \<bullet> \<Psi>\<^sub>R)"
    by(rule_tac C="(\<Psi>, \<Psi>', A\<^sub>R, p \<bullet> \<Psi>\<^sub>R)" in freshFrame) auto
  from `A\<^sub>R \<sharp>* xvec` `(p \<bullet> xvec) \<sharp>* A\<^sub>R` `A\<^sub>R \<sharp>* P` S have "A\<^sub>R \<sharp>* (p \<bullet> P)" by(simp add: freshChainSimps)
  with `A\<^sub>R \<sharp>* Q'` `A\<^sub>P \<sharp>* A\<^sub>R` `A\<^sub>Q' \<sharp>* A\<^sub>R` FrP FrQ' have "A\<^sub>R \<sharp>* \<Psi>\<^sub>P" and  "A\<^sub>R \<sharp>* \<Psi>\<^sub>Q'"
    by(force dest: extractFrameFreshChain)+

  from QChain FrpR `A\<^sub>R \<sharp>* \<Psi>` `A\<^sub>R \<sharp>* (p \<bullet> Q)` have "\<Psi> \<rhd> (p \<bullet> Q) \<parallel> (p \<bullet> R) \<Longrightarrow>\<^sup>^\<^sub>\<tau> Q' \<parallel> (p \<bullet> R)" by(rule tauChainPar1)
  hence "(p \<bullet> \<Psi>) \<rhd> (p \<bullet> ((p \<bullet> Q) \<parallel> (p \<bullet> R))) \<Longrightarrow>\<^sup>^\<^sub>\<tau> p \<bullet> (Q' \<parallel> (p \<bullet> R))" by(rule eqvts)
  with `xvec \<sharp>* \<Psi>` `(p \<bullet> xvec) \<sharp>* \<Psi>` S `distinctPerm p` have "\<Psi> \<rhd> Q \<parallel> R \<Longrightarrow>\<^sup>^\<^sub>\<tau> (p \<bullet> Q') \<parallel> R" by(simp add: eqvts)
  hence "\<Psi> \<rhd> \<lparr>\<nu>*xvec\<rparr>(Q \<parallel> R) \<Longrightarrow>\<^sup>^\<^sub>\<tau> \<lparr>\<nu>*xvec\<rparr>((p \<bullet> Q') \<parallel> R)" using `xvec \<sharp>* \<Psi>` by(rule tauChainResChainPres)
  moreover have "\<langle>(A\<^sub>P@A\<^sub>R), \<Psi> \<otimes> \<Psi>\<^sub>P \<otimes> (p \<bullet> \<Psi>\<^sub>R)\<rangle> \<hookrightarrow>\<^sub>F \<langle>(A\<^sub>Q'@A\<^sub>R), \<Psi> \<otimes> \<Psi>\<^sub>Q' \<otimes> (p \<bullet> \<Psi>\<^sub>R)\<rangle>"
  proof -
    have "\<langle>A\<^sub>P, \<Psi> \<otimes> \<Psi>\<^sub>P \<otimes> (p \<bullet> \<Psi>\<^sub>R)\<rangle> \<simeq>\<^sub>F \<langle>A\<^sub>P, (\<Psi> \<otimes> (p \<bullet> \<Psi>\<^sub>R)) \<otimes> \<Psi>\<^sub>P\<rangle>"
      by(metis frameResChainPres frameNilStatEq Associativity Commutativity AssertionStatEqTrans Composition)
    moreover with FrP FrQ' PimpQ' `A\<^sub>P \<sharp>* \<Psi>` `A\<^sub>P \<sharp>* (p \<bullet> \<Psi>\<^sub>R)` `A\<^sub>Q' \<sharp>* \<Psi>` `A\<^sub>Q' \<sharp>* (p \<bullet> \<Psi>\<^sub>R)`
    have "\<langle>A\<^sub>P, (\<Psi> \<otimes> (p \<bullet> \<Psi>\<^sub>R)) \<otimes> \<Psi>\<^sub>P\<rangle> \<hookrightarrow>\<^sub>F \<langle>A\<^sub>Q', (\<Psi> \<otimes> (p \<bullet> \<Psi>\<^sub>R)) \<otimes> \<Psi>\<^sub>Q'\<rangle>"  using freshCompChain
      by simp
    moreover have "\<langle>A\<^sub>Q', (\<Psi> \<otimes> (p \<bullet> \<Psi>\<^sub>R)) \<otimes> \<Psi>\<^sub>Q'\<rangle> \<simeq>\<^sub>F \<langle>A\<^sub>Q', \<Psi> \<otimes> \<Psi>\<^sub>Q' \<otimes> (p \<bullet> \<Psi>\<^sub>R)\<rangle>"
      by(metis frameResChainPres frameNilStatEq Associativity Commutativity AssertionStatEqTrans Composition)
    ultimately have "\<langle>A\<^sub>P, \<Psi> \<otimes> \<Psi>\<^sub>P \<otimes> (p \<bullet> \<Psi>\<^sub>R)\<rangle> \<hookrightarrow>\<^sub>F \<langle>A\<^sub>Q', \<Psi> \<otimes> \<Psi>\<^sub>Q' \<otimes> (p \<bullet> \<Psi>\<^sub>R)\<rangle>"
      by(rule FrameStatEqImpCompose)
    hence "\<langle>(A\<^sub>R@A\<^sub>P), \<Psi> \<otimes> \<Psi>\<^sub>P \<otimes> (p \<bullet> \<Psi>\<^sub>R)\<rangle> \<hookrightarrow>\<^sub>F \<langle>(A\<^sub>R@A\<^sub>Q'), \<Psi> \<otimes> \<Psi>\<^sub>Q' \<otimes> (p \<bullet> \<Psi>\<^sub>R)\<rangle>"
      by(drule_tac frameImpResChainPres) (simp add: frameChainAppend)
    thus ?thesis
      apply(simp add: frameChainAppend)
      by(metis frameImpChainComm FrameStatImpTrans)
  qed
  with FrP FrpR FrQ' `A\<^sub>P \<sharp>* A\<^sub>R` `A\<^sub>P \<sharp>* (p \<bullet> \<Psi>\<^sub>R)` `A\<^sub>Q' \<sharp>* A\<^sub>R` `A\<^sub>Q' \<sharp>* (p \<bullet> \<Psi>\<^sub>R)` `A\<^sub>R \<sharp>* \<Psi>\<^sub>P` `A\<^sub>R \<sharp>* \<Psi>\<^sub>Q'`
      `A\<^sub>P \<sharp>* \<Psi>` `A\<^sub>Q' \<sharp>* \<Psi>` `A\<^sub>R \<sharp>* \<Psi>`
  have "insertAssertion(extractFrame((p \<bullet> P) \<parallel> (p \<bullet> R))) \<Psi> \<hookrightarrow>\<^sub>F insertAssertion(extractFrame(Q' \<parallel> (p \<bullet> R))) \<Psi>"
    by simp
  hence "(p \<bullet> insertAssertion(extractFrame((p \<bullet> P) \<parallel> (p \<bullet> R))) \<Psi>) \<hookrightarrow>\<^sub>F (p \<bullet> insertAssertion(extractFrame(Q' \<parallel> (p \<bullet> R))) \<Psi>)"
    by(rule FrameStatImpClosed)
  with `xvec \<sharp>* \<Psi>` `(p \<bullet> xvec) \<sharp>* \<Psi>` S `distinctPerm p`
  have "insertAssertion(extractFrame(P \<parallel> R)) \<Psi> \<hookrightarrow>\<^sub>F insertAssertion(extractFrame((p \<bullet> Q') \<parallel> R)) \<Psi>"
    by(simp add: eqvts)
  with `xvec \<sharp>* \<Psi>` have "insertAssertion(extractFrame(\<lparr>\<nu>*xvec\<rparr>(P \<parallel> R))) \<Psi> \<hookrightarrow>\<^sub>F insertAssertion(extractFrame(\<lparr>\<nu>*xvec\<rparr>((p \<bullet> Q') \<parallel> R))) \<Psi>"
    by(force intro: frameImpResChainPres)
  moreover from Q'Chain have "(\<Psi> \<otimes> \<Psi>') \<otimes> (p \<bullet> \<Psi>\<^sub>R) \<rhd> Q' \<Longrightarrow>\<^sup>^\<^sub>\<tau> Q''"
    by(rule tauChainStatEq) (metis Associativity AssertionStatEqTrans Commutativity Composition)
  hence "\<Psi> \<otimes> \<Psi>' \<rhd> Q' \<parallel> (p \<bullet> R) \<Longrightarrow>\<^sup>^\<^sub>\<tau> Q'' \<parallel> (p \<bullet> R)" using FrpR `A\<^sub>R \<sharp>* \<Psi>` `A\<^sub>R \<sharp>* \<Psi>'` `A\<^sub>R \<sharp>* Q'` `A\<^sub>R \<sharp>* xvec` `(p \<bullet> xvec) \<sharp>* A\<^sub>R` S
    by(force intro: tauChainPar1 simp add: freshChainSimps)
  hence "\<Psi> \<otimes> \<Psi>' \<rhd> \<lparr>\<nu>*(p \<bullet> xvec)\<rparr>(Q' \<parallel> (p \<bullet> R)) \<Longrightarrow>\<^sup>^\<^sub>\<tau> \<lparr>\<nu>*(p \<bullet> xvec)\<rparr>(Q'' \<parallel> (p \<bullet> R))" using `(p \<bullet> xvec) \<sharp>* \<Psi>` `(p \<bullet> xvec) \<sharp>* \<Psi>'`
    by(rule_tac tauChainResChainPres) auto
  hence "\<Psi> \<otimes> \<Psi>' \<rhd> \<lparr>\<nu>*xvec\<rparr>((p \<bullet> Q') \<parallel> R) \<Longrightarrow>\<^sup>^\<^sub>\<tau> \<lparr>\<nu>*xvec\<rparr>((p \<bullet> Q'') \<parallel> R)" using `xvec \<sharp>* Q'` `xvec \<sharp>* Q''` `(p \<bullet> xvec) \<sharp>* R` S `distinctPerm p`
    apply(subst resChainAlpha) apply(auto simp add: pt_fresh_star_bij[OF pt_name_inst, OF at_name_inst])
    by(subst resChainAlpha[of _ xvec]) (auto simp add: pt_fresh_star_bij[OF pt_name_inst, OF at_name_inst])
  moreover from `((\<Psi> \<otimes> (p \<bullet> \<Psi>\<^sub>R)) \<otimes> \<Psi>', (p \<bullet> P), Q'') \<in> Rel` have "((\<Psi> \<otimes> \<Psi>') \<otimes> (p \<bullet> \<Psi>\<^sub>R), (p \<bullet> P),  Q'') \<in> Rel"
    by(rule C3) (metis Associativity AssertionStatEqTrans Commutativity Composition)
  hence "(\<Psi> \<otimes> \<Psi>', (p \<bullet> P) \<parallel> (p \<bullet> R), Q'' \<parallel> (p \<bullet> R)) \<in> Rel'" 
    using FrpR `A\<^sub>R \<sharp>* \<Psi>` `A\<^sub>R \<sharp>* \<Psi>'` `A\<^sub>R \<sharp>* Q''` `A\<^sub>R \<sharp>* P` `A\<^sub>R \<sharp>* xvec` `(p \<bullet> xvec) \<sharp>* A\<^sub>R` S
    by(rule_tac C1) (auto simp add: freshChainSimps)
  hence "(\<Psi> \<otimes> \<Psi>', \<lparr>\<nu>*(p \<bullet> xvec)\<rparr>((p \<bullet> P) \<parallel> (p \<bullet> R)), \<lparr>\<nu>*(p \<bullet> xvec)\<rparr>(Q'' \<parallel> (p \<bullet> R))) \<in> Rel'"  using `(p \<bullet> xvec) \<sharp>* \<Psi>` `(p \<bullet> xvec) \<sharp>* \<Psi>'`
    by(rule_tac C2) auto
  hence "(\<Psi> \<otimes> \<Psi>', \<lparr>\<nu>*xvec\<rparr>(P \<parallel> R), \<lparr>\<nu>*xvec\<rparr>((p \<bullet> Q'') \<parallel> R)) \<in> Rel'" using `(p \<bullet> xvec) \<sharp>* P` `xvec \<sharp>* Q''` `(p \<bullet> xvec) \<sharp>* R` S `distinctPerm p`
    apply(subst resChainAlpha[where p=p]) 
    apply simp
    apply simp
    apply(subst resChainAlpha[where xvec=xvec and p=p]) 
    by(auto simp add: pt_fresh_star_bij[OF pt_name_inst, OF at_name_inst])
  ultimately show ?case 
    by blast
qed

end

end