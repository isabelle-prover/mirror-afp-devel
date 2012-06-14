(* 
   Title: Psi-calculi   
   Author/Maintainer: Jesper Bengtson (jebe@itu.dk), 2012
*)
theory Sim_Pres
  imports Simulation
begin

context env begin

lemma inputPres:
  fixes \<Psi>    :: 'b
  and   P    :: "('a, 'b, 'c) psi"
  and   Rel  :: "('b \<times> ('a, 'b, 'c) psi \<times> ('a, 'b, 'c) psi) set"
  and   Q    :: "('a, 'b, 'c) psi"
  and   M    :: 'a
  and   xvec :: "name list"
  and   N    :: 'a

  assumes PRelQ: "\<And>Tvec. length xvec = length Tvec \<Longrightarrow> (\<Psi>, P[xvec::=Tvec], Q[xvec::=Tvec]) \<in> Rel"

  shows "\<Psi> \<rhd> M\<lparr>\<lambda>*xvec N\<rparr>.P \<leadsto>[Rel] M\<lparr>\<lambda>*xvec N\<rparr>.Q"
proof(auto simp add: simulation_def residual.inject psi.inject)
  fix \<alpha> Q'
  assume "\<Psi> \<rhd> M\<lparr>\<lambda>*xvec N\<rparr>.Q \<longmapsto>\<alpha> \<prec> Q'"
  thus "\<exists>P'. \<Psi> \<rhd> M\<lparr>\<lambda>*xvec N\<rparr>.P \<longmapsto>\<alpha> \<prec> P' \<and> (\<Psi>, P', Q') \<in> Rel"
    by(induct rule: inputCases) (auto intro: Input PRelQ)
qed

lemma outputPres:
  fixes \<Psi>    :: 'b
  and   P    :: "('a, 'b, 'c) psi"
  and   Rel  :: "('b \<times> ('a, 'b, 'c) psi \<times> ('a, 'b, 'c) psi) set"
  and   Q    :: "('a, 'b, 'c) psi"
  and   M    :: 'a
  and   N    :: 'a

  assumes PRelQ: "(\<Psi>, P, Q) \<in> Rel"

  shows "\<Psi> \<rhd> M\<langle>N\<rangle>.P \<leadsto>[Rel] M\<langle>N\<rangle>.Q"
proof(auto simp add: simulation_def residual.inject psi.inject)
  fix \<alpha> Q'
  assume "\<Psi> \<rhd> M\<langle>N\<rangle>.Q \<longmapsto>\<alpha> \<prec> Q'"
  thus "\<exists>P'. \<Psi> \<rhd> M\<langle>N\<rangle>.P \<longmapsto>\<alpha> \<prec> P' \<and> (\<Psi>, P', Q') \<in> Rel"
    by(induct rule: outputCases) (auto intro: Output PRelQ)
qed

lemma casePres:
  fixes \<Psi>    :: 'b
  and   CsP  :: "('c \<times> ('a, 'b, 'c) psi) list"
  and   Rel  :: "('b \<times> ('a, 'b, 'c) psi \<times> ('a, 'b, 'c) psi) set"
  and   CsQ  :: "('c \<times> ('a, 'b, 'c) psi) list"
  and   M    :: 'a
  and   N    :: 'a

  assumes PRelQ: "\<And>\<phi> Q. (\<phi>, Q) mem CsQ \<Longrightarrow> \<exists>P. (\<phi>, P) mem CsP \<and> guarded P \<and> (\<Psi>, P, Q) \<in> Rel"
  and     Sim: "\<And>\<Psi>' R S. (\<Psi>', R, S) \<in> Rel \<Longrightarrow> \<Psi>' \<rhd> R \<leadsto>[Rel] S"
  and          "Rel \<subseteq> Rel'"

  shows "\<Psi> \<rhd> Cases CsP \<leadsto>[Rel'] Cases CsQ"
proof(auto simp add: simulation_def residual.inject psi.inject)
  fix \<alpha> Q'
  assume "\<Psi> \<rhd> Cases CsQ \<longmapsto>\<alpha> \<prec> Q'" and "bn \<alpha> \<sharp>* CsP" and "bn \<alpha> \<sharp>* \<Psi>"
  thus "\<exists>P'. \<Psi> \<rhd> Cases CsP \<longmapsto>\<alpha> \<prec> P' \<and> (\<Psi>, P', Q') \<in> Rel'"
  proof(induct rule: caseCases)
    case(cCase \<phi> Q)
    from `(\<phi>, Q) mem CsQ` obtain P where "(\<phi>, P) mem CsP" and "guarded P" and "(\<Psi>, P, Q) \<in> Rel"
      by(metis PRelQ)
    from `(\<Psi>, P, Q) \<in> Rel` have "\<Psi> \<rhd> P \<leadsto>[Rel] Q" by(rule Sim)
    moreover from `bn \<alpha> \<sharp>* CsP` `(\<phi>, P) mem CsP` have "bn \<alpha> \<sharp>* P" by(auto dest: memFreshChain)
    moreover note `\<Psi> \<rhd> Q \<longmapsto>\<alpha> \<prec> Q'` `bn \<alpha> \<sharp>* \<Psi>`
    ultimately obtain P' where PTrans: "\<Psi> \<rhd> P \<longmapsto>\<alpha> \<prec> P'" and P'RelQ': "(\<Psi>, P', Q') \<in> Rel"
      by(blast dest: simE)
    from PTrans `(\<phi>, P) mem CsP` `\<Psi> \<turnstile> \<phi>` `guarded P` have "\<Psi> \<rhd> Cases CsP \<longmapsto>\<alpha> \<prec> P'"
      by(rule Case)
    moreover from P'RelQ' `Rel \<subseteq> Rel'` have "(\<Psi>, P', Q') \<in> Rel'" by blast
    ultimately show ?case by blast
  qed
qed

lemma resPres:
  fixes \<Psi>    :: 'b
  and   P    :: "('a, 'b, 'c) psi"
  and   Rel  :: "('b \<times> ('a, 'b, 'c) psi \<times> ('a, 'b, 'c) psi) set"
  and   Q    :: "('a, 'b, 'c) psi"
  and   x    :: name
  and   Rel' :: "('b \<times> ('a, 'b, 'c) psi \<times> ('a, 'b, 'c) psi) set"

  assumes PSimQ: "\<Psi> \<rhd> P \<leadsto>[Rel] Q"
  and     "eqvt Rel'"
  and     "x \<sharp> \<Psi>"
  and     "Rel \<subseteq> Rel'"
  and     C1:    "\<And>\<Psi>' R S y. \<lbrakk>(\<Psi>', R, S) \<in> Rel; y \<sharp> \<Psi>'\<rbrakk> \<Longrightarrow> (\<Psi>', \<lparr>\<nu>y\<rparr>R, \<lparr>\<nu>y\<rparr>S) \<in> Rel'"

  shows   "\<Psi> \<rhd> \<lparr>\<nu>x\<rparr>P \<leadsto>[Rel'] \<lparr>\<nu>x\<rparr>Q"
proof -
  note `eqvt Rel'` `x \<sharp> \<Psi>`
  moreover have "x \<sharp> \<lparr>\<nu>x\<rparr>P" and "x \<sharp> \<lparr>\<nu>x\<rparr>Q" by(simp add: abs_fresh)+
  ultimately show ?thesis
  proof(induct rule: simIFresh[where C="()"])
    case(cSim \<alpha> Q') 
    from `bn \<alpha> \<sharp>* \<lparr>\<nu>x\<rparr>P` `bn \<alpha> \<sharp>* \<lparr>\<nu>x\<rparr>Q` `x \<sharp> \<alpha>` have "bn \<alpha> \<sharp>* P" and "bn \<alpha> \<sharp>* Q" by simp+
    from `\<Psi> \<rhd> \<lparr>\<nu>x\<rparr>Q \<longmapsto>\<alpha> \<prec> Q'` `x \<sharp> \<Psi>` `x \<sharp> \<alpha>` `x \<sharp> Q'`  `bn \<alpha> \<sharp>* \<Psi>` `bn \<alpha> \<sharp>* Q` `bn \<alpha> \<sharp>* subject \<alpha>` 
         `bn \<alpha> \<sharp>* \<Psi>` `bn \<alpha> \<sharp>* P` `x \<sharp> \<alpha>`
    show ?case
    proof(induct rule: resCases)
      case(cOpen M xvec1 xvec2 y N Q')
      from `bn (M\<lparr>\<nu>*(xvec1@y#xvec2)\<rparr>\<langle>N\<rangle>) \<sharp>* \<Psi>` have "xvec1 \<sharp>* \<Psi>" and "y \<sharp> \<Psi>" and "xvec2 \<sharp>* \<Psi>" by simp+
      from `bn (M\<lparr>\<nu>*(xvec1@y#xvec2)\<rparr>\<langle>N\<rangle>) \<sharp>* P` have "xvec1 \<sharp>* P" and "y \<sharp> P" and "xvec2 \<sharp>* P" by simp+
      from `x \<sharp> (M\<lparr>\<nu>*(xvec1@y#xvec2)\<rparr>\<langle>N\<rangle>)` have "x \<sharp> xvec1" and "x \<noteq> y" and "x \<sharp> xvec2" and "x \<sharp> M" by simp+
      from PSimQ `\<Psi> \<rhd> Q \<longmapsto>M\<lparr>\<nu>*(xvec1@xvec2)\<rparr>\<langle>([(x, y)] \<bullet> N)\<rangle> \<prec> ([(x, y)] \<bullet> Q')` 
           `xvec1 \<sharp>* \<Psi>` `xvec2 \<sharp>* \<Psi>` `xvec1 \<sharp>* P` `xvec2 \<sharp>* P`
      obtain P' where PTrans: "\<Psi> \<rhd> P \<longmapsto>M\<lparr>\<nu>*(xvec1@xvec2)\<rparr>\<langle>([(x, y)] \<bullet> N)\<rangle> \<prec> P'" and P'RelQ': "(\<Psi>, P', ([(x, y)] \<bullet> Q')) \<in> Rel"
	by(force dest: simE)
      from `y \<in> supp N` `x \<noteq> y` have "x \<in> supp([(x, y)] \<bullet> N)" 
	by(drule_tac pt_set_bij2[OF pt_name_inst, OF at_name_inst, where pi="[(x, y)]"]) (simp add: eqvts calc_atm)
      with PTrans `x \<sharp> \<Psi>` `x \<sharp> M` `x \<sharp> xvec1` `x \<sharp> xvec2`
      have "\<Psi> \<rhd> \<lparr>\<nu>x\<rparr>P \<longmapsto>M\<lparr>\<nu>*(xvec1@x#xvec2)\<rparr>\<langle>([(x, y)] \<bullet> N)\<rangle> \<prec> P'"
	by(rule_tac Open)
      hence "([(x, y)] \<bullet> \<Psi>) \<rhd> ([(x, y)] \<bullet> \<lparr>\<nu>x\<rparr>P) \<longmapsto>([(x, y)] \<bullet> (M\<lparr>\<nu>*(xvec1@x#xvec2)\<rparr>\<langle>([(x, y)] \<bullet> N)\<rangle> \<prec> P'))"
	by(rule eqvts)
      with `x \<sharp> \<Psi>` `y \<sharp> \<Psi>` `y \<sharp> P` `x \<sharp> M` `y \<sharp> M` `x \<sharp> xvec1` `y \<sharp> xvec1` `x \<sharp> xvec2` `y \<sharp> xvec2` `x \<noteq> y`
      have "\<Psi> \<rhd> \<lparr>\<nu>x\<rparr>P \<longmapsto>M\<lparr>\<nu>*(xvec1@y#xvec2)\<rparr>\<langle>N\<rangle> \<prec> ([(x, y)] \<bullet> P')" by(simp add: eqvts calc_atm alphaRes)
      moreover from P'RelQ' `Rel \<subseteq> Rel'` `eqvt Rel'` have "([(y, x)] \<bullet> \<Psi>, [(y, x)] \<bullet> P', [(y, x)] \<bullet> [(x, y)] \<bullet> Q') \<in> Rel'"
	by(force simp add: eqvt_def)
      with `x \<sharp> \<Psi>` `y \<sharp> \<Psi>` have "(\<Psi>, [(x, y)] \<bullet> P', Q') \<in> Rel'" by(simp add: name_swap)
      ultimately show ?case by blast
    next
      case(cRes Q')
      from PSimQ `\<Psi> \<rhd> Q \<longmapsto>\<alpha> \<prec> Q'` `bn \<alpha> \<sharp>* \<Psi>` `bn \<alpha> \<sharp>* P`
      obtain P' where PTrans: "\<Psi> \<rhd> P \<longmapsto>\<alpha> \<prec> P'" and P'RelQ': "(\<Psi>, P', Q') \<in> Rel"
	by(blast dest: simE)
      from PTrans `x \<sharp> \<Psi>` `x \<sharp> \<alpha>` have "\<Psi> \<rhd> \<lparr>\<nu>x\<rparr>P \<longmapsto>\<alpha> \<prec> \<lparr>\<nu>x\<rparr>P'"
	by(rule Scope)
      moreover from P'RelQ' `x \<sharp> \<Psi>` have "(\<Psi>, \<lparr>\<nu>x\<rparr>P', \<lparr>\<nu>x\<rparr>Q') \<in> Rel'" by(rule C1)
      ultimately show ?case by blast
    qed
  qed
qed

lemma resChainPres:
  fixes \<Psi>    :: 'b
  and   P    :: "('a, 'b, 'c) psi"
  and   Rel  :: "('b \<times> ('a, 'b, 'c) psi \<times> ('a, 'b, 'c) psi) set"
  and   Q    :: "('a, 'b, 'c) psi"
  and   xvec :: "name list"

  assumes PSimQ: "\<Psi> \<rhd> P \<leadsto>[Rel] Q"
  and     "eqvt Rel"
  and     "xvec \<sharp>* \<Psi>"
  and     C1:    "\<And>\<Psi>' R S y. \<lbrakk>(\<Psi>', R, S) \<in> Rel; y \<sharp> \<Psi>'\<rbrakk> \<Longrightarrow> (\<Psi>', \<lparr>\<nu>y\<rparr>R, \<lparr>\<nu>y\<rparr>S) \<in> Rel"

  shows   "\<Psi> \<rhd> \<lparr>\<nu>*xvec\<rparr>P \<leadsto>[Rel] \<lparr>\<nu>*xvec\<rparr>Q"
using `xvec \<sharp>* \<Psi>`
proof(induct xvec)
  case Nil
  from PSimQ show ?case by simp
next
  case(Cons x xvec)
  from `(x#xvec) \<sharp>* \<Psi>` have "x \<sharp> \<Psi>" and "xvec \<sharp>* \<Psi>" by simp+
  from `xvec \<sharp>* \<Psi>` have "\<Psi> \<rhd> \<lparr>\<nu>*xvec\<rparr>P \<leadsto>[Rel] \<lparr>\<nu>*xvec\<rparr>Q" by(rule Cons)
  moreover note `eqvt Rel` `x \<sharp> \<Psi>`
  moreover have "Rel \<subseteq> Rel" by simp
  ultimately have "\<Psi> \<rhd> \<lparr>\<nu>x\<rparr>(\<lparr>\<nu>*xvec\<rparr>P) \<leadsto>[Rel] \<lparr>\<nu>x\<rparr>(\<lparr>\<nu>*xvec\<rparr>Q)" using C1
    by(rule resPres)
  thus ?case by simp
qed

lemma parPres:
  fixes \<Psi>    :: 'b
  and   P    :: "('a, 'b, 'c) psi"
  and   Rel  :: "('b \<times> ('a, 'b, 'c) psi \<times> ('a, 'b, 'c) psi) set"
  and   Q    :: "('a, 'b, 'c) psi"
  and   R    :: "('a, 'b, 'c) psi"
  and   Rel' :: "('b \<times> ('a, 'b, 'c) psi \<times> ('a, 'b, 'c) psi) set"
  
  assumes PRelQ: "\<And>A\<^isub>R \<Psi>\<^isub>R. \<lbrakk>extractFrame R = \<langle>A\<^isub>R, \<Psi>\<^isub>R\<rangle>; A\<^isub>R \<sharp>* \<Psi>; A\<^isub>R \<sharp>* P; A\<^isub>R \<sharp>* Q\<rbrakk> \<Longrightarrow> (\<Psi> \<otimes> \<Psi>\<^isub>R, P, Q) \<in> Rel" 
  and     Eqvt: "eqvt Rel"
  and     Eqvt': "eqvt Rel'"

  and     StatImp: "\<And>\<Psi>' S T. (\<Psi>', S, T) \<in> Rel \<Longrightarrow> insertAssertion (extractFrame T) \<Psi>' \<hookrightarrow>\<^sub>F insertAssertion (extractFrame S) \<Psi>'"
  and     Sim:     "\<And>\<Psi>' S T. (\<Psi>', S, T) \<in> Rel \<Longrightarrow> \<Psi>' \<rhd> S \<leadsto>[Rel] T"
  and     Ext: "\<And>\<Psi>' S T \<Psi>''. \<lbrakk>(\<Psi>', S, T) \<in> Rel\<rbrakk> \<Longrightarrow> (\<Psi>' \<otimes> \<Psi>'', S, T) \<in> Rel"


  and     C1: "\<And>\<Psi>' S T A\<^isub>U \<Psi>\<^isub>U U. \<lbrakk>(\<Psi>' \<otimes> \<Psi>\<^isub>U, S, T) \<in> Rel; extractFrame U = \<langle>A\<^isub>U, \<Psi>\<^isub>U\<rangle>; A\<^isub>U \<sharp>* \<Psi>'; A\<^isub>U \<sharp>* S; A\<^isub>U \<sharp>* T\<rbrakk> \<Longrightarrow> (\<Psi>', S \<parallel> U, T \<parallel> U) \<in> Rel'"
  and     C2: "\<And>\<Psi>' S T xvec. \<lbrakk>(\<Psi>', S, T) \<in> Rel'; xvec \<sharp>* \<Psi>'\<rbrakk> \<Longrightarrow> (\<Psi>', \<lparr>\<nu>*xvec\<rparr>S, \<lparr>\<nu>*xvec\<rparr>T) \<in> Rel'"
  and     C3: "\<And>\<Psi>' S T \<Psi>''. \<lbrakk>(\<Psi>', S, T) \<in> Rel; \<Psi>' \<simeq> \<Psi>''\<rbrakk> \<Longrightarrow> (\<Psi>'', S, T) \<in> Rel"

  shows "\<Psi> \<rhd> P \<parallel> R \<leadsto>[Rel'] Q \<parallel> R"
using Eqvt'
proof(induct rule: simI[of _ _ _ _ "()"])
  case(cSim \<alpha> QR)
  from `bn \<alpha> \<sharp>* (P \<parallel> R)` `bn \<alpha> \<sharp>* (Q \<parallel> R)`
  have "bn \<alpha> \<sharp>* P" and "bn \<alpha> \<sharp>* Q" and "bn \<alpha> \<sharp>* R"
    by simp+
  from `\<Psi> \<rhd> Q \<parallel> R \<longmapsto>\<alpha> \<prec> QR` `bn \<alpha> \<sharp>* \<Psi>` `bn \<alpha> \<sharp>* Q` `bn \<alpha> \<sharp>* R` `bn \<alpha> \<sharp>* subject \<alpha>`
  show ?case
  proof(induct rule: parCases[where C = "(P, R)"])
    case(cPar1 Q' A\<^isub>R \<Psi>\<^isub>R)
    from `A\<^isub>R \<sharp>* (P, R)` have "A\<^isub>R \<sharp>* P" by simp
    have FrR: "extractFrame R = \<langle>A\<^isub>R, \<Psi>\<^isub>R\<rangle>" by fact
    from `A\<^isub>R \<sharp>* \<alpha>` `bn \<alpha> \<sharp>* R` FrR
    have "bn \<alpha> \<sharp>* \<Psi>\<^isub>R" by(drule_tac extractFrameFreshChain) auto
    from FrR `A\<^isub>R \<sharp>* \<Psi>` `A\<^isub>R \<sharp>* P` `A\<^isub>R \<sharp>* Q` have "\<Psi> \<otimes> \<Psi>\<^isub>R \<rhd> P \<leadsto>[Rel] Q"
      by(blast intro: Sim PRelQ)
    moreover have QTrans: "\<Psi> \<otimes> \<Psi>\<^isub>R \<rhd> Q \<longmapsto>\<alpha> \<prec> Q'" by fact
    ultimately obtain P' where PTrans: "\<Psi> \<otimes> \<Psi>\<^isub>R \<rhd> P \<longmapsto>\<alpha> \<prec> P'"
                           and P'RelQ': "(\<Psi> \<otimes> \<Psi>\<^isub>R, P', Q') \<in> Rel"
    using `bn \<alpha> \<sharp>* \<Psi>` `bn \<alpha> \<sharp>* \<Psi>\<^isub>R` `bn \<alpha> \<sharp>* P`
      by(force dest: simE)
    from PTrans QTrans `A\<^isub>R \<sharp>* P` `A\<^isub>R \<sharp>* Q` `A\<^isub>R \<sharp>* \<alpha>` `bn \<alpha> \<sharp>* subject \<alpha>` `distinct(bn \<alpha>)` have "A\<^isub>R \<sharp>* P'" and "A\<^isub>R \<sharp>* Q'"
      by(blast dest: freeFreshChainDerivative)+
    from PTrans `bn \<alpha> \<sharp>* R` FrR  `A\<^isub>R \<sharp>* \<Psi>` `A\<^isub>R \<sharp>* P` `A\<^isub>R \<sharp>* \<alpha>` have "\<Psi> \<rhd> P \<parallel> R \<longmapsto>\<alpha> \<prec> (P' \<parallel> R)" 
      by(rule_tac Par1) 
    moreover from P'RelQ' FrR `A\<^isub>R \<sharp>* \<Psi>` `A\<^isub>R \<sharp>* P'` `A\<^isub>R \<sharp>* Q'` have "(\<Psi>, P' \<parallel> R, Q' \<parallel> R) \<in> Rel'" by(rule C1)
    ultimately show ?case by blast
  next
    case(cPar2 R' A\<^isub>Q \<Psi>\<^isub>Q)
    from `A\<^isub>Q \<sharp>* (P, R)` have "A\<^isub>Q \<sharp>* P" and "A\<^isub>Q \<sharp>* R" by simp+
    obtain A\<^isub>P \<Psi>\<^isub>P where FrP: "extractFrame P = \<langle>A\<^isub>P, \<Psi>\<^isub>P\<rangle>" and "A\<^isub>P \<sharp>* (\<Psi>, A\<^isub>Q, \<Psi>\<^isub>Q, \<alpha>, R)"
      by(rule freshFrame)
    hence "A\<^isub>P \<sharp>* \<Psi>" and "A\<^isub>P \<sharp>* A\<^isub>Q" and "A\<^isub>P \<sharp>* \<Psi>\<^isub>Q" and "A\<^isub>P \<sharp>* \<alpha>" and "A\<^isub>P \<sharp>* R"
      by simp+

    have FrQ: "extractFrame Q = \<langle>A\<^isub>Q, \<Psi>\<^isub>Q\<rangle>" by fact
    from `A\<^isub>Q \<sharp>* P` FrP `A\<^isub>P \<sharp>* A\<^isub>Q` have "A\<^isub>Q \<sharp>* \<Psi>\<^isub>P"
      by(drule_tac extractFrameFreshChain) auto

    from FrP FrQ `bn \<alpha> \<sharp>* P` `bn \<alpha> \<sharp>* Q` `A\<^isub>P \<sharp>* \<alpha>` `A\<^isub>Q \<sharp>* \<alpha>`
    have "bn \<alpha> \<sharp>* \<Psi>\<^isub>P" and "bn \<alpha> \<sharp>* \<Psi>\<^isub>Q"
      by(force dest: extractFrameFreshChain)+


    obtain A\<^isub>R \<Psi>\<^isub>R where FrR: "extractFrame R = \<langle>A\<^isub>R, \<Psi>\<^isub>R\<rangle>" and "A\<^isub>R \<sharp>* (\<Psi>, P, Q, A\<^isub>Q, A\<^isub>P, \<Psi>\<^isub>Q, \<Psi>\<^isub>P, \<alpha>, R)" and "distinct A\<^isub>R"
      by(rule freshFrame)
    then have "A\<^isub>R \<sharp>* \<Psi>" and "A\<^isub>R \<sharp>* P" and "A\<^isub>R \<sharp>* Q" and "A\<^isub>R \<sharp>* A\<^isub>Q" and  "A\<^isub>R \<sharp>* A\<^isub>P" and  "A\<^isub>R \<sharp>* \<Psi>\<^isub>Q" and  "A\<^isub>R \<sharp>* \<Psi>\<^isub>P" and "A\<^isub>R \<sharp>* \<alpha>" and "A\<^isub>R \<sharp>* R"
      by simp+

    from `A\<^isub>Q \<sharp>* R`  FrR `A\<^isub>R \<sharp>* A\<^isub>Q` have "A\<^isub>Q \<sharp>* \<Psi>\<^isub>R"
      by(drule_tac extractFrameFreshChain) auto
    from `A\<^isub>P \<sharp>* R` `A\<^isub>R \<sharp>* A\<^isub>P` FrR  have "A\<^isub>P \<sharp>* \<Psi>\<^isub>R"
      by(drule_tac extractFrameFreshChain) auto

    have RTrans: "\<Psi> \<otimes> \<Psi>\<^isub>Q \<rhd> R \<longmapsto>\<alpha> \<prec> R'" by fact
    moreover have "\<langle>A\<^isub>Q, (\<Psi> \<otimes> \<Psi>\<^isub>Q) \<otimes> \<Psi>\<^isub>R\<rangle> \<hookrightarrow>\<^sub>F \<langle>A\<^isub>P, (\<Psi> \<otimes> \<Psi>\<^isub>P) \<otimes> \<Psi>\<^isub>R\<rangle>"
    proof -
      have "\<langle>A\<^isub>Q, (\<Psi> \<otimes> \<Psi>\<^isub>Q) \<otimes> \<Psi>\<^isub>R\<rangle> \<simeq>\<^sub>F \<langle>A\<^isub>Q, (\<Psi> \<otimes> \<Psi>\<^isub>R) \<otimes> \<Psi>\<^isub>Q\<rangle>"
	by(metis frameIntAssociativity Commutativity FrameStatEqTrans frameIntCompositionSym FrameStatEqSym)
      moreover from FrR `A\<^isub>R \<sharp>* \<Psi>` `A\<^isub>R \<sharp>* P` `A\<^isub>R \<sharp>* Q`
      have "(insertAssertion (extractFrame Q) (\<Psi> \<otimes> \<Psi>\<^isub>R)) \<hookrightarrow>\<^sub>F (insertAssertion (extractFrame P) (\<Psi> \<otimes> \<Psi>\<^isub>R))"
	by(blast intro: PRelQ StatImp)
      with FrP FrQ `A\<^isub>P \<sharp>* \<Psi>` `A\<^isub>Q \<sharp>* \<Psi>` `A\<^isub>P \<sharp>* \<Psi>\<^isub>R` `A\<^isub>Q \<sharp>* \<Psi>\<^isub>R`
      have "\<langle>A\<^isub>Q, (\<Psi> \<otimes> \<Psi>\<^isub>R) \<otimes> \<Psi>\<^isub>Q\<rangle> \<hookrightarrow>\<^sub>F \<langle>A\<^isub>P, (\<Psi> \<otimes> \<Psi>\<^isub>R) \<otimes> \<Psi>\<^isub>P\<rangle>" using freshCompChain by auto
      moreover have "\<langle>A\<^isub>P, (\<Psi> \<otimes> \<Psi>\<^isub>R) \<otimes> \<Psi>\<^isub>P\<rangle> \<simeq>\<^sub>F \<langle>A\<^isub>P, (\<Psi> \<otimes> \<Psi>\<^isub>P) \<otimes> \<Psi>\<^isub>R\<rangle>"
	by(metis frameIntAssociativity Commutativity FrameStatEqTrans frameIntCompositionSym frameIntAssociativity[THEN FrameStatEqSym])
      ultimately show ?thesis
	by(rule FrameStatEqImpCompose)
    qed

    ultimately have "\<Psi> \<otimes> \<Psi>\<^isub>P \<rhd> R \<longmapsto>\<alpha> \<prec> R'"
      using `A\<^isub>P \<sharp>* \<Psi>` `A\<^isub>P \<sharp>* \<Psi>\<^isub>Q` `A\<^isub>Q \<sharp>* \<Psi>` `A\<^isub>Q \<sharp>* \<Psi>\<^isub>P` `A\<^isub>P \<sharp>* R` `A\<^isub>Q \<sharp>* R` `A\<^isub>P \<sharp>* \<alpha>` `A\<^isub>Q \<sharp>* \<alpha>`
            `A\<^isub>R \<sharp>* A\<^isub>P` `A\<^isub>R \<sharp>* A\<^isub>Q` `A\<^isub>R \<sharp>* \<Psi>\<^isub>P` `A\<^isub>R \<sharp>* \<Psi>\<^isub>Q` `A\<^isub>R \<sharp>* \<Psi>` FrR `distinct A\<^isub>R`
      by(force intro: transferFrame)
    with `bn \<alpha> \<sharp>* P` `A\<^isub>P \<sharp>* \<Psi>`  `A\<^isub>P \<sharp>* R`  `A\<^isub>P \<sharp>* \<alpha>` FrP have "\<Psi> \<rhd> P \<parallel> R \<longmapsto>\<alpha> \<prec> (P \<parallel> R')"
      by(force intro: Par2)
    moreover obtain A\<^isub>R' \<Psi>\<^isub>R' where "extractFrame R' = \<langle>A\<^isub>R', \<Psi>\<^isub>R'\<rangle>" and "A\<^isub>R' \<sharp>* \<Psi>" and "A\<^isub>R' \<sharp>* P" and "A\<^isub>R' \<sharp>* Q"
      by(rule_tac freshFrame[where C="(\<Psi>, P, Q)"]) auto

    moreover from RTrans FrR `distinct A\<^isub>R` `A\<^isub>R \<sharp>* \<Psi>` `A\<^isub>R \<sharp>* P` `A\<^isub>R \<sharp>* Q` `A\<^isub>R \<sharp>* R` `A\<^isub>R \<sharp>* \<alpha>` `bn \<alpha> \<sharp>* \<Psi>` `bn \<alpha>  \<sharp>* P` `bn \<alpha>  \<sharp>* Q` `bn \<alpha>  \<sharp>* R` `bn \<alpha> \<sharp>* subject \<alpha>` `distinct(bn \<alpha>)`
    obtain p \<Psi>' A\<^isub>R' \<Psi>\<^isub>R' where S: "set p \<subseteq> set(bn \<alpha>) \<times> set(bn(p \<bullet> \<alpha>))" and "(p \<bullet> \<Psi>\<^isub>R) \<otimes> \<Psi>' \<simeq> \<Psi>\<^isub>R'" and FrR': "extractFrame R' = \<langle>A\<^isub>R', \<Psi>\<^isub>R'\<rangle>"
                           and "bn(p \<bullet> \<alpha>) \<sharp>* R" and "bn(p \<bullet> \<alpha>) \<sharp>* \<Psi>" and "bn(p \<bullet> \<alpha>) \<sharp>* P" and "bn(p \<bullet> \<alpha>) \<sharp>* Q" and "bn(p \<bullet> \<alpha>) \<sharp>* R"
                           and "A\<^isub>R' \<sharp>* \<Psi>" and "A\<^isub>R' \<sharp>* P" and "A\<^isub>R' \<sharp>* Q"
      by(rule_tac C="(\<Psi>, P, Q, R)" and C'="(\<Psi>, P, Q, R)" in expandFrame) (assumption | simp)+

    from `A\<^isub>R \<sharp>* \<Psi>` have "(p \<bullet> A\<^isub>R) \<sharp>* (p \<bullet> \<Psi>)" by(simp add: pt_fresh_star_bij[OF pt_name_inst, OF at_name_inst])
    with `bn \<alpha> \<sharp>* \<Psi>` `bn(p \<bullet> \<alpha>) \<sharp>* \<Psi>` S have "(p \<bullet> A\<^isub>R) \<sharp>* \<Psi>" by simp
    from `A\<^isub>R \<sharp>* P` have "(p \<bullet> A\<^isub>R) \<sharp>* (p \<bullet> P)" by(simp add: pt_fresh_star_bij[OF pt_name_inst, OF at_name_inst])
    with `bn \<alpha> \<sharp>* P` `bn(p \<bullet> \<alpha>) \<sharp>* P` S have "(p \<bullet> A\<^isub>R) \<sharp>* P" by simp
    from `A\<^isub>R \<sharp>* Q` have "(p \<bullet> A\<^isub>R) \<sharp>* (p \<bullet> Q)" by(simp add: pt_fresh_star_bij[OF pt_name_inst, OF at_name_inst])
    with `bn \<alpha> \<sharp>* Q` `bn(p \<bullet> \<alpha>) \<sharp>* Q` S have "(p \<bullet> A\<^isub>R) \<sharp>* Q" by simp

    from FrR have "(p \<bullet> extractFrame R) = p \<bullet> \<langle>A\<^isub>R, \<Psi>\<^isub>R\<rangle>" by simp
    with `bn \<alpha> \<sharp>* R` `bn(p \<bullet> \<alpha>) \<sharp>* R` S have "extractFrame R = \<langle>(p \<bullet> A\<^isub>R), (p \<bullet> \<Psi>\<^isub>R)\<rangle>"
      by(simp add: eqvts)

    with `(p \<bullet> A\<^isub>R) \<sharp>* \<Psi>` `(p \<bullet> A\<^isub>R) \<sharp>* P` `(p \<bullet> A\<^isub>R) \<sharp>* Q` have "(\<Psi> \<otimes> (p \<bullet> \<Psi>\<^isub>R), P, Q) \<in> Rel" by(rule_tac PRelQ)

    hence "((\<Psi> \<otimes> (p \<bullet> \<Psi>\<^isub>R)) \<otimes> \<Psi>', P, Q) \<in> Rel" by(rule Ext)
    with `(p \<bullet> \<Psi>\<^isub>R) \<otimes> \<Psi>' \<simeq> \<Psi>\<^isub>R'` have "(\<Psi> \<otimes> \<Psi>\<^isub>R', P, Q) \<in> Rel" by(blast intro: C3 Associativity compositionSym)
    with FrR' `A\<^isub>R' \<sharp>* \<Psi>` `A\<^isub>R' \<sharp>* P` `A\<^isub>R' \<sharp>* Q` have "(\<Psi>, P \<parallel> R', Q \<parallel> R') \<in> Rel'" by(rule_tac C1) 
    ultimately show ?case by blast
  next
    case(cComm1 \<Psi>\<^isub>R M N Q' A\<^isub>Q \<Psi>\<^isub>Q K xvec R' A\<^isub>R)
    have  FrQ: "extractFrame Q = \<langle>A\<^isub>Q, \<Psi>\<^isub>Q\<rangle>" by fact
    from `A\<^isub>Q \<sharp>* (P, R)` have "A\<^isub>Q \<sharp>* P" and "A\<^isub>Q \<sharp>* R" by simp+

    have  FrR: "extractFrame R = \<langle>A\<^isub>R, \<Psi>\<^isub>R\<rangle>" by fact
    from `A\<^isub>R \<sharp>* (P, R)` have "A\<^isub>R \<sharp>* P" and "A\<^isub>R \<sharp>* R" by simp+

    from `xvec \<sharp>* (P, R)` have "xvec \<sharp>* P" and "xvec \<sharp>* R" by simp+
  
    obtain A\<^isub>P \<Psi>\<^isub>P where FrP: "extractFrame P = \<langle>A\<^isub>P, \<Psi>\<^isub>P\<rangle>" and "A\<^isub>P \<sharp>* (\<Psi>, A\<^isub>Q, \<Psi>\<^isub>Q, A\<^isub>R, M, N, K, R, P, xvec)" and "distinct A\<^isub>P"
      by(rule freshFrame)
    hence "A\<^isub>P \<sharp>* \<Psi>" and "A\<^isub>P \<sharp>* A\<^isub>Q" and "A\<^isub>P \<sharp>* \<Psi>\<^isub>Q" and "A\<^isub>P \<sharp>* M" and "A\<^isub>P \<sharp>* R"
      and "A\<^isub>P \<sharp>* N" and "A\<^isub>P \<sharp>* K" and "A\<^isub>P \<sharp>* A\<^isub>R" and "A\<^isub>P \<sharp>* P" and "A\<^isub>P \<sharp>* xvec"
      by simp+

    have QTrans: "\<Psi> \<otimes> \<Psi>\<^isub>R \<rhd> Q \<longmapsto>M\<lparr>N\<rparr> \<prec> Q'" and RTrans: "\<Psi> \<otimes> \<Psi>\<^isub>Q \<rhd> R \<longmapsto>K\<lparr>\<nu>*xvec\<rparr>\<langle>N\<rangle> \<prec> R'"
      and MeqK: "\<Psi> \<otimes> \<Psi>\<^isub>Q \<otimes> \<Psi>\<^isub>R \<turnstile> M \<leftrightarrow>K" by fact+

    from FrP FrR `A\<^isub>Q \<sharp>* P` `A\<^isub>P \<sharp>* R` `A\<^isub>R \<sharp>* P` `A\<^isub>P \<sharp>* A\<^isub>Q` `A\<^isub>P \<sharp>* A\<^isub>R` `A\<^isub>P \<sharp>* xvec` `xvec \<sharp>* P`
    have "A\<^isub>P \<sharp>* \<Psi>\<^isub>R" and "A\<^isub>Q \<sharp>* \<Psi>\<^isub>P" and  "A\<^isub>R \<sharp>* \<Psi>\<^isub>P" and "xvec \<sharp>* \<Psi>\<^isub>P"
      by(fastsimp dest!: extractFrameFreshChain)+
  
  from RTrans FrR `distinct A\<^isub>R` `A\<^isub>R \<sharp>* R` `A\<^isub>R \<sharp>* xvec` `xvec \<sharp>* R` `xvec \<sharp>* Q` `xvec \<sharp>* \<Psi>` `xvec \<sharp>* \<Psi>\<^isub>Q` `A\<^isub>R \<sharp>* Q`
                  `A\<^isub>R \<sharp>* \<Psi>` `A\<^isub>R \<sharp>* \<Psi>\<^isub>Q` `xvec \<sharp>* K` `A\<^isub>R \<sharp>* K` `A\<^isub>R \<sharp>* N` `A\<^isub>R \<sharp>* R` `xvec \<sharp>* R` `A\<^isub>R \<sharp>* P` `xvec \<sharp>* P` `A\<^isub>P \<sharp>* A\<^isub>R` `A\<^isub>P \<sharp>* xvec`
                  `A\<^isub>Q \<sharp>* A\<^isub>R` `A\<^isub>Q \<sharp>* xvec` `A\<^isub>R \<sharp>* \<Psi>\<^isub>P` `xvec \<sharp>* \<Psi>\<^isub>P` `distinct xvec` `xvec \<sharp>* M`
  obtain p \<Psi>' A\<^isub>R' \<Psi>\<^isub>R' where S: "set p \<subseteq> set xvec \<times> set(p \<bullet> xvec)" and FrR': "extractFrame R' = \<langle>A\<^isub>R', \<Psi>\<^isub>R'\<rangle>"
                         and "(p \<bullet> \<Psi>\<^isub>R) \<otimes> \<Psi>' \<simeq> \<Psi>\<^isub>R'" and "A\<^isub>R' \<sharp>* Q" and "A\<^isub>R' \<sharp>* \<Psi>" and "(p \<bullet> xvec) \<sharp>* \<Psi>"
                         and "(p \<bullet> xvec) \<sharp>* Q" and "(p \<bullet> xvec) \<sharp>* \<Psi>\<^isub>Q" and "(p \<bullet> xvec) \<sharp>* K" and "(p \<bullet> xvec) \<sharp>* R"
                         and "(p \<bullet> xvec) \<sharp>* P" and "(p \<bullet> xvec) \<sharp>* A\<^isub>P" and "(p \<bullet> xvec) \<sharp>* A\<^isub>Q" and "(p \<bullet> xvec) \<sharp>* \<Psi>\<^isub>P"
                         and "A\<^isub>R' \<sharp>* P" and "A\<^isub>R' \<sharp>* N"
    by(rule_tac C="(\<Psi>, Q, \<Psi>\<^isub>Q, K, R, P, A\<^isub>P, A\<^isub>Q, \<Psi>\<^isub>P)" and C'="(\<Psi>, Q, \<Psi>\<^isub>Q, K, R, P, A\<^isub>P, A\<^isub>Q, \<Psi>\<^isub>P)" in expandFrame) 
      (assumption | simp)+

  from `A\<^isub>R \<sharp>* \<Psi>` have "(p \<bullet> A\<^isub>R) \<sharp>* (p \<bullet> \<Psi>)" by(simp add: pt_fresh_star_bij[OF pt_name_inst, OF at_name_inst])
  with `xvec \<sharp>* \<Psi>` `(p \<bullet> xvec) \<sharp>* \<Psi>` S have "(p \<bullet> A\<^isub>R) \<sharp>* \<Psi>" by simp
  from `A\<^isub>R \<sharp>* P` have "(p \<bullet> A\<^isub>R) \<sharp>* (p \<bullet> P)" by(simp add: pt_fresh_star_bij[OF pt_name_inst, OF at_name_inst])
  with `xvec \<sharp>* P` `(p \<bullet> xvec) \<sharp>* P` S have "(p \<bullet> A\<^isub>R) \<sharp>* P" by simp
  from `A\<^isub>R \<sharp>* Q` have "(p \<bullet> A\<^isub>R) \<sharp>* (p \<bullet> Q)" by(simp add: pt_fresh_star_bij[OF pt_name_inst, OF at_name_inst])
  with `xvec \<sharp>* Q` `(p \<bullet> xvec) \<sharp>* Q` S have "(p \<bullet> A\<^isub>R) \<sharp>* Q" by simp
  from `A\<^isub>R \<sharp>* R` have "(p \<bullet> A\<^isub>R) \<sharp>* (p \<bullet> R)" by(simp add: pt_fresh_star_bij[OF pt_name_inst, OF at_name_inst])
  with `xvec \<sharp>* R` `(p \<bullet> xvec) \<sharp>* R` S have "(p \<bullet> A\<^isub>R) \<sharp>* R" by simp
  from `A\<^isub>R \<sharp>* K` have "(p \<bullet> A\<^isub>R) \<sharp>* (p \<bullet> K)" by(simp add: pt_fresh_star_bij[OF pt_name_inst, OF at_name_inst])
  with `xvec \<sharp>* K` `(p \<bullet> xvec) \<sharp>* K` S have "(p \<bullet> A\<^isub>R) \<sharp>* K" by simp
  
  from `A\<^isub>P \<sharp>* xvec` `(p \<bullet> xvec) \<sharp>* A\<^isub>P` `A\<^isub>P \<sharp>* M` S have "A\<^isub>P \<sharp>* (p \<bullet> M)" by(simp add: freshChainSimps)
  from `A\<^isub>Q \<sharp>* xvec` `(p \<bullet> xvec) \<sharp>* A\<^isub>Q` `A\<^isub>Q \<sharp>* M` S have "A\<^isub>Q \<sharp>* (p \<bullet> M)" by(simp add: freshChainSimps)
  from `A\<^isub>P \<sharp>* xvec` `(p \<bullet> xvec) \<sharp>* A\<^isub>P` `A\<^isub>P \<sharp>* A\<^isub>R` S have "(p \<bullet> A\<^isub>R) \<sharp>* A\<^isub>P" by(simp add: freshChainSimps)
  from `A\<^isub>Q \<sharp>* xvec` `(p \<bullet> xvec) \<sharp>* A\<^isub>Q` `A\<^isub>Q \<sharp>* A\<^isub>R` S have "(p \<bullet> A\<^isub>R) \<sharp>* A\<^isub>Q" by(simp add: freshChainSimps)
  
  from QTrans S `xvec \<sharp>* Q` `(p \<bullet> xvec) \<sharp>* Q` have "(p \<bullet> (\<Psi> \<otimes> \<Psi>\<^isub>R)) \<rhd> Q \<longmapsto> (p \<bullet> M)\<lparr>N\<rparr> \<prec> Q'"
    by(rule_tac inputPermFrameSubject) (assumption | auto simp add: fresh_star_def)+
  with `xvec \<sharp>* \<Psi>` `(p \<bullet> xvec) \<sharp>* \<Psi>` S have QTrans: "(\<Psi> \<otimes> (p \<bullet> \<Psi>\<^isub>R)) \<rhd> Q \<longmapsto> (p \<bullet> M)\<lparr>N\<rparr> \<prec> Q'"
    by(simp add: eqvts)

  from FrR have "(p \<bullet> extractFrame R) = p \<bullet> \<langle>A\<^isub>R, \<Psi>\<^isub>R\<rangle>" by simp
  with `xvec \<sharp>* R` `(p \<bullet> xvec) \<sharp>* R` S have FrR: "extractFrame R = \<langle>(p \<bullet> A\<^isub>R), (p \<bullet> \<Psi>\<^isub>R)\<rangle>"
    by(simp add: eqvts)

  note RTrans FrR
  moreover from FrR `(p \<bullet> A\<^isub>R) \<sharp>* \<Psi>` `(p \<bullet> A\<^isub>R) \<sharp>* P` `(p \<bullet> A\<^isub>R) \<sharp>* Q` have "\<Psi> \<otimes> (p \<bullet> \<Psi>\<^isub>R) \<rhd> P \<leadsto>[Rel] Q"
    by(metis Sim PRelQ)
  with QTrans obtain P' where PTrans: "\<Psi> \<otimes> (p \<bullet> \<Psi>\<^isub>R) \<rhd> P \<longmapsto>(p \<bullet> M)\<lparr>N\<rparr> \<prec> P'" and P'RelQ': "(\<Psi> \<otimes> (p \<bullet> \<Psi>\<^isub>R), P', Q') \<in> Rel"
    by(force dest: simE)
  from PTrans QTrans `A\<^isub>R' \<sharp>* P` `A\<^isub>R' \<sharp>* Q` `A\<^isub>R' \<sharp>* N` have "A\<^isub>R' \<sharp>* P'" and "A\<^isub>R' \<sharp>* Q'"
    by(blast dest: inputFreshChainDerivative)+
    
  note PTrans
  moreover from MeqK have "(p \<bullet> (\<Psi> \<otimes> \<Psi>\<^isub>Q \<otimes> \<Psi>\<^isub>R)) \<turnstile> (p \<bullet> M) \<leftrightarrow> (p \<bullet> K)" by(rule chanEqClosed)
  with `xvec \<sharp>* \<Psi>` `(p \<bullet> xvec) \<sharp>* \<Psi>` `xvec \<sharp>* \<Psi>\<^isub>Q` `(p \<bullet> xvec) \<sharp>* \<Psi>\<^isub>Q` `xvec \<sharp>* K` `(p \<bullet> xvec) \<sharp>* K` S
  have MeqK: "\<Psi> \<otimes> \<Psi>\<^isub>Q \<otimes> (p \<bullet> \<Psi>\<^isub>R) \<turnstile> (p \<bullet> M) \<leftrightarrow> K" by(simp add: eqvts)
  
  moreover have "\<langle>A\<^isub>Q, (\<Psi> \<otimes> \<Psi>\<^isub>Q) \<otimes> (p \<bullet> \<Psi>\<^isub>R)\<rangle> \<hookrightarrow>\<^sub>F \<langle>A\<^isub>P, (\<Psi> \<otimes> \<Psi>\<^isub>P) \<otimes> (p \<bullet> \<Psi>\<^isub>R)\<rangle>"
  proof -
    have "\<langle>A\<^isub>P, (\<Psi> \<otimes> (p \<bullet> \<Psi>\<^isub>R)) \<otimes> \<Psi>\<^isub>P\<rangle> \<simeq>\<^sub>F \<langle>A\<^isub>P, (\<Psi> \<otimes> \<Psi>\<^isub>P) \<otimes> (p \<bullet> \<Psi>\<^isub>R)\<rangle>"
      by(metis frameResChainPres frameNilStatEq Commutativity AssertionStatEqTrans Composition Associativity)
    moreover from FrR `(p \<bullet> A\<^isub>R) \<sharp>* \<Psi>` `(p \<bullet> A\<^isub>R) \<sharp>* P` `(p \<bullet> A\<^isub>R) \<sharp>* Q`
    have "(insertAssertion (extractFrame Q) (\<Psi> \<otimes> (p \<bullet> \<Psi>\<^isub>R))) \<hookrightarrow>\<^sub>F (insertAssertion (extractFrame P) (\<Psi> \<otimes> (p \<bullet> \<Psi>\<^isub>R)))"
      by(metis PRelQ StatImp)
    with FrP FrQ `A\<^isub>P \<sharp>* \<Psi>` `A\<^isub>Q \<sharp>* \<Psi>` `A\<^isub>P \<sharp>* \<Psi>\<^isub>R` `A\<^isub>Q \<sharp>* \<Psi>\<^isub>R` `A\<^isub>P \<sharp>* xvec` `(p \<bullet> xvec) \<sharp>* A\<^isub>P` `A\<^isub>Q \<sharp>* xvec` `(p \<bullet> xvec) \<sharp>* A\<^isub>Q` S
    have "\<langle>A\<^isub>Q, (\<Psi> \<otimes> (p \<bullet> \<Psi>\<^isub>R)) \<otimes> \<Psi>\<^isub>Q\<rangle> \<hookrightarrow>\<^sub>F \<langle>A\<^isub>P, (\<Psi> \<otimes> (p \<bullet> \<Psi>\<^isub>R)) \<otimes> \<Psi>\<^isub>P\<rangle>" using freshCompChain
      by(simp add: freshChainSimps)
    moreover have "\<langle>A\<^isub>Q, (\<Psi> \<otimes> \<Psi>\<^isub>Q) \<otimes> (p \<bullet> \<Psi>\<^isub>R)\<rangle> \<simeq>\<^sub>F \<langle>A\<^isub>Q, (\<Psi> \<otimes> (p \<bullet> \<Psi>\<^isub>R)) \<otimes> \<Psi>\<^isub>Q\<rangle>" 
      by(metis frameResChainPres frameNilStatEq Commutativity AssertionStatEqTrans Composition Associativity)
    ultimately show ?thesis by(rule_tac FrameStatEqImpCompose)
  qed
  moreover note FrP FrQ `distinct A\<^isub>P`
  moreover from `distinct A\<^isub>R` have "distinct(p \<bullet> A\<^isub>R)" by simp
  moreover note `(p \<bullet> A\<^isub>R) \<sharp>* A\<^isub>P`  `(p \<bullet> A\<^isub>R) \<sharp>* A\<^isub>Q` `(p \<bullet> A\<^isub>R) \<sharp>* \<Psi>` `(p \<bullet> A\<^isub>R) \<sharp>* P` `(p \<bullet> A\<^isub>R) \<sharp>* Q` `(p \<bullet> A\<^isub>R) \<sharp>* R` `(p \<bullet> A\<^isub>R) \<sharp>* K`
                `A\<^isub>P \<sharp>* \<Psi>` `A\<^isub>P \<sharp>* R` `A\<^isub>P \<sharp>* P` `A\<^isub>P \<sharp>* (p \<bullet> M)` `A\<^isub>Q \<sharp>* R` `A\<^isub>Q \<sharp>* (p \<bullet> M)` `A\<^isub>P \<sharp>* xvec` `xvec \<sharp>* P` `A\<^isub>P \<sharp>* R`
  ultimately obtain K' where "\<Psi> \<otimes> \<Psi>\<^isub>P \<rhd> R \<longmapsto>K'\<lparr>\<nu>*xvec\<rparr>\<langle>N\<rangle> \<prec> R'" and "\<Psi> \<otimes> \<Psi>\<^isub>P \<otimes> (p \<bullet> \<Psi>\<^isub>R) \<turnstile> (p \<bullet> M) \<leftrightarrow> K'" and "(p \<bullet> A\<^isub>R) \<sharp>* K'"
    by(rule_tac comm1Aux)

  with PTrans FrP have "\<Psi> \<rhd> P \<parallel> R \<longmapsto>\<tau> \<prec> \<lparr>\<nu>*xvec\<rparr>(P' \<parallel> R')" using FrR `(p \<bullet> A\<^isub>R) \<sharp>* \<Psi>` `(p \<bullet> A\<^isub>R) \<sharp>* P` `(p \<bullet> A\<^isub>R) \<sharp>* R`
    `xvec \<sharp>* P` `A\<^isub>P \<sharp>* \<Psi>` `A\<^isub>P \<sharp>* P` `A\<^isub>P \<sharp>* R` `A\<^isub>P \<sharp>* (p \<bullet> M)` `(p \<bullet> A\<^isub>R) \<sharp>* K'` `(p \<bullet> A\<^isub>R) \<sharp>* A\<^isub>P`
    by(rule_tac Comm1) (assumption | simp)+

  moreover from P'RelQ' have  "((\<Psi> \<otimes> (p \<bullet> \<Psi>\<^isub>R)) \<otimes> \<Psi>', P', Q') \<in> Rel" by(rule Ext)
  with `(p \<bullet> \<Psi>\<^isub>R) \<otimes> \<Psi>' \<simeq> \<Psi>\<^isub>R'` have "(\<Psi> \<otimes> \<Psi>\<^isub>R', P', Q') \<in> Rel" by(metis C3 Associativity compositionSym)
  with FrR' `A\<^isub>R' \<sharp>* P'` `A\<^isub>R' \<sharp>* Q'` `A\<^isub>R' \<sharp>* \<Psi>` have "(\<Psi>, P' \<parallel> R', Q' \<parallel> R') \<in> Rel'" by(rule_tac C1)
  with `xvec \<sharp>* \<Psi>` have "(\<Psi>, \<lparr>\<nu>*xvec\<rparr>(P' \<parallel> R'), \<lparr>\<nu>*xvec\<rparr>(Q' \<parallel> R')) \<in> Rel'" by(rule_tac C2)
  ultimately show ?case by blast
next
    case(cComm2 \<Psi>\<^isub>R M xvec N Q' A\<^isub>Q \<Psi>\<^isub>Q K R' A\<^isub>R)
    have  FrQ: "extractFrame Q = \<langle>A\<^isub>Q, \<Psi>\<^isub>Q\<rangle>" by fact
    from `A\<^isub>Q \<sharp>* (P, R)` have "A\<^isub>Q \<sharp>* P" and "A\<^isub>Q \<sharp>* R" by simp+

    have  FrR: "extractFrame R = \<langle>A\<^isub>R, \<Psi>\<^isub>R\<rangle>" by fact
    from `A\<^isub>R \<sharp>* (P, R)` have "A\<^isub>R \<sharp>* P" and "A\<^isub>R \<sharp>* R" by simp+

    from `xvec \<sharp>* (P, R)` have "xvec \<sharp>* P" and "xvec \<sharp>* R" by simp+

    obtain A\<^isub>P \<Psi>\<^isub>P where FrP: "extractFrame P = \<langle>A\<^isub>P, \<Psi>\<^isub>P\<rangle>" and "A\<^isub>P \<sharp>* (\<Psi>, A\<^isub>Q, \<Psi>\<^isub>Q, A\<^isub>R, M, N, K, R, P, xvec)" and "distinct A\<^isub>P"
      by(rule freshFrame)
    hence "A\<^isub>P \<sharp>* \<Psi>" and "A\<^isub>P \<sharp>* A\<^isub>Q" and "A\<^isub>P \<sharp>* \<Psi>\<^isub>Q" and "A\<^isub>P \<sharp>* M" and "A\<^isub>P \<sharp>* R"
      and "A\<^isub>P \<sharp>* N" "A\<^isub>P \<sharp>* K" and "A\<^isub>P \<sharp>* A\<^isub>R" and "A\<^isub>P \<sharp>* P"  and "A\<^isub>P \<sharp>* xvec" 
      by simp+

    from FrP FrR `A\<^isub>Q \<sharp>* P` `A\<^isub>P \<sharp>* R` `A\<^isub>R \<sharp>* P` `A\<^isub>P \<sharp>* A\<^isub>Q` `A\<^isub>P \<sharp>* A\<^isub>R` `A\<^isub>P \<sharp>* xvec` `xvec \<sharp>* P`
    have "A\<^isub>P \<sharp>* \<Psi>\<^isub>R" and "A\<^isub>Q \<sharp>* \<Psi>\<^isub>P" and  "A\<^isub>R \<sharp>* \<Psi>\<^isub>P" and "xvec \<sharp>* \<Psi>\<^isub>P"
      by(fastsimp dest!: extractFrameFreshChain)+

    have QTrans: "\<Psi> \<otimes> \<Psi>\<^isub>R \<rhd> Q \<longmapsto>M\<lparr>\<nu>*xvec\<rparr>\<langle>N\<rangle> \<prec> Q'" by fact 

    note `\<Psi> \<otimes> \<Psi>\<^isub>Q \<rhd> R \<longmapsto>K\<lparr>N\<rparr> \<prec> R'` FrR `\<Psi> \<otimes> \<Psi>\<^isub>Q \<otimes> \<Psi>\<^isub>R \<turnstile> M \<leftrightarrow> K`
    moreover from FrR `A\<^isub>R \<sharp>* \<Psi>` `A\<^isub>R \<sharp>* P` `A\<^isub>R \<sharp>* Q` have "\<Psi> \<otimes> \<Psi>\<^isub>R \<rhd> P \<leadsto>[Rel] Q" by(metis PRelQ Sim)
    with QTrans obtain P' where PTrans: "\<Psi> \<otimes> \<Psi>\<^isub>R \<rhd> P \<longmapsto>M\<lparr>\<nu>*xvec\<rparr>\<langle>N\<rangle> \<prec> P'" and P'RelQ': "(\<Psi> \<otimes> \<Psi>\<^isub>R, P', Q') \<in> Rel"
      using `xvec \<sharp>* \<Psi>` `xvec \<sharp>* \<Psi>\<^isub>R` `xvec \<sharp>* P`
      by(force dest: simE)
    from PTrans QTrans `A\<^isub>R \<sharp>* P` `A\<^isub>R \<sharp>* Q` `A\<^isub>R \<sharp>* xvec` `xvec \<sharp>* M` `distinct xvec` have "A\<^isub>R \<sharp>* P'" and "A\<^isub>R \<sharp>* Q'"
      by(blast dest: outputFreshChainDerivative)+
    note PTrans `\<Psi> \<otimes> \<Psi>\<^isub>Q \<otimes> \<Psi>\<^isub>R \<turnstile> M \<leftrightarrow> K`
    moreover have "\<langle>A\<^isub>Q, (\<Psi> \<otimes> \<Psi>\<^isub>Q) \<otimes> \<Psi>\<^isub>R\<rangle> \<hookrightarrow>\<^sub>F \<langle>A\<^isub>P, (\<Psi> \<otimes> \<Psi>\<^isub>P) \<otimes> \<Psi>\<^isub>R\<rangle>"
    proof -
      have "\<langle>A\<^isub>P, (\<Psi> \<otimes> \<Psi>\<^isub>R) \<otimes> \<Psi>\<^isub>P\<rangle> \<simeq>\<^sub>F \<langle>A\<^isub>P, (\<Psi> \<otimes> \<Psi>\<^isub>P) \<otimes> \<Psi>\<^isub>R\<rangle>"
	by(metis frameResChainPres frameNilStatEq Commutativity AssertionStatEqTrans Composition Associativity)
      moreover from FrR `A\<^isub>R \<sharp>* \<Psi>` `A\<^isub>R \<sharp>* P` `A\<^isub>R \<sharp>* Q`
      have "(insertAssertion (extractFrame Q) (\<Psi> \<otimes> \<Psi>\<^isub>R)) \<hookrightarrow>\<^sub>F (insertAssertion (extractFrame P) (\<Psi> \<otimes> \<Psi>\<^isub>R))"
	by(metis PRelQ StatImp)
      with FrP FrQ `A\<^isub>P \<sharp>* \<Psi>` `A\<^isub>Q \<sharp>* \<Psi>` `A\<^isub>P \<sharp>* \<Psi>\<^isub>R` `A\<^isub>Q \<sharp>* \<Psi>\<^isub>R`
      have "\<langle>A\<^isub>Q, (\<Psi> \<otimes> \<Psi>\<^isub>R) \<otimes> \<Psi>\<^isub>Q\<rangle> \<hookrightarrow>\<^sub>F \<langle>A\<^isub>P, (\<Psi> \<otimes> \<Psi>\<^isub>R) \<otimes> \<Psi>\<^isub>P\<rangle>" using freshCompChain by simp
      moreover have "\<langle>A\<^isub>Q, (\<Psi> \<otimes> \<Psi>\<^isub>Q) \<otimes> \<Psi>\<^isub>R\<rangle> \<simeq>\<^sub>F \<langle>A\<^isub>Q, (\<Psi> \<otimes> \<Psi>\<^isub>R) \<otimes> \<Psi>\<^isub>Q\<rangle>" 
	by(metis frameResChainPres frameNilStatEq Commutativity AssertionStatEqTrans Composition Associativity)
      ultimately show ?thesis by(rule_tac FrameStatEqImpCompose)
    qed
    moreover note FrP FrQ `distinct A\<^isub>P` `distinct A\<^isub>R`
    moreover from `A\<^isub>P \<sharp>* A\<^isub>R` `A\<^isub>Q \<sharp>* A\<^isub>R` have "A\<^isub>R \<sharp>* A\<^isub>P" and "A\<^isub>R \<sharp>* A\<^isub>Q" by simp+
    moreover note `A\<^isub>R \<sharp>* \<Psi>` `A\<^isub>R \<sharp>* P` `A\<^isub>R \<sharp>* Q` `A\<^isub>R \<sharp>* R` `A\<^isub>R \<sharp>* K`  `A\<^isub>P \<sharp>* \<Psi>` `A\<^isub>P \<sharp>* P`
                  `A\<^isub>P \<sharp>* R` `A\<^isub>P \<sharp>* M` `A\<^isub>Q \<sharp>* R` `A\<^isub>Q \<sharp>* M` `A\<^isub>R \<sharp>* xvec` `xvec \<sharp>* M`
    ultimately obtain K' where "\<Psi> \<otimes> \<Psi>\<^isub>P \<rhd> R \<longmapsto>K'\<lparr>N\<rparr> \<prec> R'" and "\<Psi> \<otimes> \<Psi>\<^isub>P \<otimes> \<Psi>\<^isub>R \<turnstile> M \<leftrightarrow> K'" and "A\<^isub>R \<sharp>* K'"
      by(rule_tac comm2Aux) assumption+

    with PTrans FrP have "\<Psi> \<rhd> P \<parallel> R \<longmapsto>\<tau> \<prec> \<lparr>\<nu>*xvec\<rparr>(P' \<parallel> R')" using FrR `A\<^isub>R \<sharp>* \<Psi>` `A\<^isub>R \<sharp>* P` `A\<^isub>R \<sharp>* R`
      `A\<^isub>R \<sharp>* \<Psi>` `A\<^isub>R \<sharp>* P` `A\<^isub>R \<sharp>* R` and `xvec \<sharp>* R` `A\<^isub>P \<sharp>* \<Psi>` `A\<^isub>P \<sharp>* P` `A\<^isub>P \<sharp>* R` `A\<^isub>P \<sharp>* A\<^isub>R` `A\<^isub>P \<sharp>* M` `A\<^isub>R \<sharp>* K'`
      by(force intro: Comm2)

    moreover from `\<Psi> \<otimes> \<Psi>\<^isub>P \<rhd> R \<longmapsto>K'\<lparr>N\<rparr> \<prec> R'` FrR `distinct A\<^isub>R` `A\<^isub>R \<sharp>* \<Psi>` `A\<^isub>R \<sharp>* R` `A\<^isub>R \<sharp>* P'` `A\<^isub>R \<sharp>* Q'` `A\<^isub>R \<sharp>* N` `A\<^isub>R \<sharp>* K'`
    obtain \<Psi>' A\<^isub>R' \<Psi>\<^isub>R' where  ReqR': "\<Psi>\<^isub>R \<otimes> \<Psi>' \<simeq> \<Psi>\<^isub>R'" and FrR': "extractFrame R' = \<langle>A\<^isub>R', \<Psi>\<^isub>R'\<rangle>" 
                         and "A\<^isub>R' \<sharp>* \<Psi>" and "A\<^isub>R' \<sharp>* P'" and "A\<^isub>R' \<sharp>* Q'"
      by(rule_tac C="(\<Psi>, P', Q')" and C'="\<Psi>" in expandFrame) auto

    from P'RelQ' have "((\<Psi> \<otimes> \<Psi>\<^isub>R) \<otimes> \<Psi>', P', Q') \<in> Rel" by(rule Ext)
    with ReqR' have "(\<Psi> \<otimes> \<Psi>\<^isub>R', P', Q') \<in> Rel" by(metis C3 Associativity compositionSym)
    with FrR' `A\<^isub>R' \<sharp>* P'` `A\<^isub>R' \<sharp>* Q'` `A\<^isub>R' \<sharp>* \<Psi>` have "(\<Psi>, P' \<parallel> R', Q' \<parallel> R') \<in> Rel'"
      by(rule_tac C1)
    with `xvec \<sharp>* \<Psi>` have "(\<Psi>, \<lparr>\<nu>*xvec\<rparr>(P' \<parallel> R'), \<lparr>\<nu>*xvec\<rparr>(Q' \<parallel> R')) \<in> Rel'" by(rule_tac C2)
    ultimately show ?case by blast
  qed
qed
no_notation relcomp (infixr "O" 75)
lemma bangPres:
  fixes \<Psi>   :: 'b
  and   P    :: "('a, 'b, 'c) psi"
  and   Q    :: "('a, 'b, 'c) psi"
  and   R    :: "('a, 'b, 'c) psi"
  and   Rel  :: "('b \<times> ('a, 'b, 'c) psi \<times> ('a, 'b, 'c) psi) set"
  and   Rel' :: "('b \<times> ('a, 'b, 'c) psi \<times> ('a, 'b, 'c) psi) set"

  assumes "(\<Psi>, P, Q) \<in> Rel"
  and     "eqvt Rel'"
  and     "guarded P"
  and     "guarded Q"
  and     cSim: "\<And>\<Psi>' S T. (\<Psi>', S, T) \<in> Rel \<Longrightarrow> \<Psi>' \<rhd> S \<leadsto>[Rel] T"
  and     cExt: "\<And>\<Psi>' S T \<Psi>''. (\<Psi>', S, T) \<in> Rel \<Longrightarrow> (\<Psi>' \<otimes> \<Psi>'', S, T) \<in> Rel"
  and     cSym: "\<And>\<Psi>' S T. (\<Psi>', S, T) \<in> Rel \<Longrightarrow> (\<Psi>', T, S) \<in> Rel"
  and     StatEq: "\<And>\<Psi>' S T \<Psi>''. \<lbrakk>(\<Psi>', S, T) \<in> Rel; \<Psi>' \<simeq> \<Psi>''\<rbrakk> \<Longrightarrow> (\<Psi>'', S, T) \<in> Rel"
  and     Closed: "\<And>\<Psi>' S T p. (\<Psi>', S, T) \<in> Rel \<Longrightarrow> ((p::name prm) \<bullet> \<Psi>', p \<bullet> S, p \<bullet> T) \<in> Rel"
  and     Assoc: "\<And>\<Psi>' S T U. (\<Psi>', S \<parallel> (T \<parallel> U), (S \<parallel> T) \<parallel> U) \<in> Rel"
  and     ParPres: "\<And>\<Psi>' S T U. (\<Psi>', S, T) \<in> Rel \<Longrightarrow> (\<Psi>', S \<parallel> U, T \<parallel> U) \<in> Rel"
  and     FrameParPres: "\<And>\<Psi>' \<Psi>\<^isub>U S T U A\<^isub>U. \<lbrakk>(\<Psi>' \<otimes> \<Psi>\<^isub>U, S, T) \<in> Rel; extractFrame U = \<langle>A\<^isub>U, \<Psi>\<^isub>U\<rangle>; A\<^isub>U \<sharp>* \<Psi>'; A\<^isub>U \<sharp>* S; A\<^isub>U \<sharp>* T\<rbrakk> \<Longrightarrow>
                                            (\<Psi>', U \<parallel> S, U \<parallel> T) \<in> Rel"
  and     ResPres: "\<And>\<Psi>' S T xvec. \<lbrakk>(\<Psi>', S, T) \<in> Rel; xvec \<sharp>* \<Psi>'\<rbrakk> \<Longrightarrow> (\<Psi>', \<lparr>\<nu>*xvec\<rparr>S, \<lparr>\<nu>*xvec\<rparr>T) \<in> Rel"
  and     ScopeExt: "\<And>xvec \<Psi>' S T. \<lbrakk>xvec \<sharp>* \<Psi>'; xvec \<sharp>* T\<rbrakk> \<Longrightarrow> (\<Psi>', \<lparr>\<nu>*xvec\<rparr>(S \<parallel> T), (\<lparr>\<nu>*xvec\<rparr>S) \<parallel> T) \<in> Rel"
  and     Trans: "\<And>\<Psi>' S T U. \<lbrakk>(\<Psi>', S, T) \<in> Rel; (\<Psi>', T, U) \<in> Rel\<rbrakk> \<Longrightarrow> (\<Psi>', S, U) \<in> Rel"
  and     Compose: "\<And>\<Psi>' S T U O. \<lbrakk>(\<Psi>', S, T) \<in> Rel; (\<Psi>', T, U) \<in> Rel'; (\<Psi>', U, O) \<in> Rel\<rbrakk> \<Longrightarrow> (\<Psi>', S, O) \<in> Rel'"
  and     C1: "\<And>\<Psi> S T U. \<lbrakk>(\<Psi>, S, T) \<in> Rel; guarded S; guarded T\<rbrakk> \<Longrightarrow> (\<Psi>, U \<parallel> !S, U \<parallel> !T) \<in> Rel'"
  and     Der: "\<And>\<Psi>' S \<alpha> S' T. \<lbrakk>\<Psi>' \<rhd> !S \<longmapsto>\<alpha> \<prec> S'; (\<Psi>', S, T) \<in> Rel; bn \<alpha> \<sharp>* \<Psi>'; bn \<alpha> \<sharp>* S; bn \<alpha> \<sharp>* T; guarded T; bn \<alpha> \<sharp>* subject \<alpha>\<rbrakk> \<Longrightarrow>
                                      \<exists>T' U O.  \<Psi>' \<rhd> !T \<longmapsto>\<alpha> \<prec> T' \<and> (\<Psi>', S', U \<parallel> !S) \<in> Rel \<and> (\<Psi>', T', O \<parallel> !T) \<in> Rel \<and>
                                                (\<Psi>', U, O) \<in> Rel \<and> ((supp U)::name set) \<subseteq> supp S' \<and> 
                                                 ((supp O)::name set) \<subseteq> supp T'"

  shows "\<Psi> \<rhd> R \<parallel> !P \<leadsto>[Rel'] R \<parallel> !Q"
using `eqvt Rel'`
proof(induct rule: simI[of _ _ _ _ "()"])
  case(cSim \<alpha> RQ')
  from `bn \<alpha> \<sharp>* (R \<parallel> !P)` `bn \<alpha> \<sharp>* (R \<parallel> !Q)` have "bn \<alpha> \<sharp>* P" and "bn \<alpha> \<sharp>* (!Q)" and "bn \<alpha> \<sharp>* Q" and "bn \<alpha> \<sharp>* R" by simp+
  from `\<Psi> \<rhd> R \<parallel> !Q \<longmapsto>\<alpha> \<prec> RQ'` `bn \<alpha> \<sharp>* \<Psi>` `bn \<alpha> \<sharp>* R` `bn \<alpha> \<sharp>* !Q` `bn \<alpha> \<sharp>* subject \<alpha>` show ?case
  proof(induct rule: parCases[where C=P])
    case(cPar1 R' A\<^isub>Q \<Psi>\<^isub>Q)
    from `extractFrame (!Q) = \<langle>A\<^isub>Q, \<Psi>\<^isub>Q\<rangle>` have "A\<^isub>Q = []" and "\<Psi>\<^isub>Q = SBottom'" by simp+
    with `\<Psi> \<otimes> \<Psi>\<^isub>Q \<rhd> R \<longmapsto>\<alpha> \<prec> R'` `bn \<alpha> \<sharp>* P` have "\<Psi> \<rhd> R \<parallel> !P \<longmapsto>\<alpha> \<prec> (R' \<parallel> !P)"
      by(rule_tac Par1) (assumption | simp)+
    moreover from `(\<Psi>, P, Q) \<in> Rel` `guarded P` `guarded Q` have "(\<Psi>, R' \<parallel> !P, R' \<parallel> !Q) \<in> Rel'"
      by(rule C1)
    ultimately show ?case by blast
  next
    case(cPar2 Q' A\<^isub>R \<Psi>\<^isub>R)
    have QTrans: "\<Psi> \<otimes> \<Psi>\<^isub>R \<rhd> !Q \<longmapsto>\<alpha> \<prec> Q'" and FrR: "extractFrame R = \<langle>A\<^isub>R, \<Psi>\<^isub>R\<rangle>" by fact+
    with `bn \<alpha> \<sharp>* R` `A\<^isub>R \<sharp>* \<alpha>` have "bn \<alpha> \<sharp>* \<Psi>\<^isub>R" by(force dest: extractFrameFreshChain)
    with QTrans `(\<Psi>, P, Q) \<in> Rel` `bn \<alpha> \<sharp>* \<Psi>``bn \<alpha> \<sharp>* P` `bn \<alpha> \<sharp>* Q` `guarded P` `bn \<alpha> \<sharp>* subject \<alpha>`
    obtain P' S T where PTrans: "\<Psi> \<otimes> \<Psi>\<^isub>R \<rhd> !P \<longmapsto>\<alpha> \<prec> P'" and "(\<Psi> \<otimes> \<Psi>\<^isub>R, P', T \<parallel> !P) \<in> Rel"
                    and "(\<Psi> \<otimes> \<Psi>\<^isub>R, Q', S \<parallel> !Q) \<in> Rel" and "(\<Psi> \<otimes> \<Psi>\<^isub>R, S, T) \<in> Rel"
                    and suppT: "((supp T)::name set) \<subseteq> supp P'" and suppS: "((supp S)::name set) \<subseteq> supp Q'"
      by(drule_tac cSym) (auto dest: Der cExt)
    from PTrans FrR `A\<^isub>R \<sharp>* \<Psi>` `A\<^isub>R \<sharp>* P` `A\<^isub>R \<sharp>* \<alpha>` `bn \<alpha> \<sharp>* R` have "\<Psi> \<rhd> R \<parallel> !P \<longmapsto>\<alpha> \<prec> (R \<parallel> P')"
      by(rule_tac Par2) auto
    moreover 
    { 
      from `A\<^isub>R \<sharp>* P` `A\<^isub>R \<sharp>* (!Q)` `A\<^isub>R \<sharp>* \<alpha>` PTrans QTrans `bn \<alpha> \<sharp>* subject \<alpha>` `distinct(bn \<alpha>)` have "A\<^isub>R \<sharp>* P'" and "A\<^isub>R \<sharp>* Q'"
	by(force dest: freeFreshChainDerivative)+
      from `(\<Psi> \<otimes> \<Psi>\<^isub>R, P', T \<parallel> !P) \<in> Rel` FrR `A\<^isub>R \<sharp>* \<Psi>` `A\<^isub>R \<sharp>* P'` `A\<^isub>R \<sharp>* P` suppT have "(\<Psi>, R \<parallel> P', R \<parallel> (T \<parallel> !P)) \<in> Rel"
	by(rule_tac FrameParPres) (auto simp add: fresh_star_def fresh_def psi.supp)
      hence "(\<Psi>, R \<parallel> P', (R \<parallel> T) \<parallel> !P) \<in> Rel" by(blast intro: Assoc Trans)
      moreover from `(\<Psi>, P, Q) \<in> Rel` `guarded P` `guarded Q` have "(\<Psi>, (R \<parallel> T) \<parallel> !P, (R \<parallel> T) \<parallel> !Q) \<in> Rel'"
	by(rule C1)
      moreover from `(\<Psi> \<otimes> \<Psi>\<^isub>R, Q', S \<parallel> !Q) \<in> Rel` `(\<Psi> \<otimes> \<Psi>\<^isub>R, S, T) \<in> Rel` have "(\<Psi> \<otimes> \<Psi>\<^isub>R, Q', T \<parallel> !Q) \<in> Rel"
	by(blast intro: ParPres Trans)
      with FrR `A\<^isub>R \<sharp>* \<Psi>` `A\<^isub>R \<sharp>* P'` `A\<^isub>R \<sharp>* Q'` `A\<^isub>R \<sharp>* (!Q)` suppT suppS have "(\<Psi>, R \<parallel> Q', R \<parallel> (T \<parallel> !Q)) \<in> Rel"
	by(rule_tac FrameParPres) (auto simp add: fresh_star_def fresh_def psi.supp)
      hence "(\<Psi>, R \<parallel> Q', (R \<parallel> T) \<parallel> !Q) \<in> Rel" by(blast intro: Assoc Trans)
      ultimately have "(\<Psi>, R \<parallel> P', R \<parallel> Q') \<in> Rel'" by(blast intro: cSym Compose)
    }
    ultimately show ?case by blast
  next
    case(cComm1 \<Psi>\<^isub>Q M N R' A\<^isub>R \<Psi>\<^isub>R K xvec Q' A\<^isub>Q)
    from `extractFrame (!Q) = \<langle>A\<^isub>Q, \<Psi>\<^isub>Q\<rangle>` have "A\<^isub>Q = []" and "\<Psi>\<^isub>Q = SBottom'" by simp+
    have RTrans: "\<Psi> \<otimes> \<Psi>\<^isub>Q \<rhd> R \<longmapsto>M\<lparr>N\<rparr> \<prec> R'" and FrR: "extractFrame R = \<langle>A\<^isub>R, \<Psi>\<^isub>R\<rangle>" by fact+
    moreover have QTrans: "\<Psi> \<otimes> \<Psi>\<^isub>R \<rhd> !Q \<longmapsto>K\<lparr>\<nu>*xvec\<rparr>\<langle>N\<rangle> \<prec> Q'" by fact
    from FrR `xvec \<sharp>* R` `A\<^isub>R \<sharp>* xvec` have "xvec \<sharp>* \<Psi>\<^isub>R" by(force dest: extractFrameFreshChain)
    with QTrans `(\<Psi>, P, Q) \<in> Rel` `xvec \<sharp>* \<Psi>``xvec \<sharp>* P` `xvec \<sharp>* (!Q)` `guarded P` `xvec \<sharp>* K`
    obtain P' S T where PTrans: "\<Psi> \<otimes> \<Psi>\<^isub>R \<rhd> !P \<longmapsto>K\<lparr>\<nu>*xvec\<rparr>\<langle>N\<rangle> \<prec> P'" and "(\<Psi> \<otimes> \<Psi>\<^isub>R, P', T \<parallel> !P) \<in> Rel"
                    and "(\<Psi> \<otimes> \<Psi>\<^isub>R, Q', S \<parallel> !Q) \<in> Rel" and "(\<Psi> \<otimes> \<Psi>\<^isub>R, S, T) \<in> Rel"
                    and suppT: "((supp T)::name set) \<subseteq> supp P'" and suppS: "((supp S)::name set) \<subseteq> supp Q'"
      by(drule_tac cSym) (fastsimp dest: Der intro: cExt)
    note `\<Psi> \<otimes> \<Psi>\<^isub>R \<otimes> \<Psi>\<^isub>Q \<turnstile> M \<leftrightarrow> K`
    ultimately have "\<Psi> \<rhd> R \<parallel> !P \<longmapsto>\<tau> \<prec> \<lparr>\<nu>*xvec\<rparr>(R' \<parallel> P')" 
      using PTrans `\<Psi>\<^isub>Q = SBottom'` `xvec \<sharp>* R` `A\<^isub>R \<sharp>* \<Psi>` `A\<^isub>R \<sharp>* R` `A\<^isub>R \<sharp>* M` `A\<^isub>R \<sharp>* P`
      by(rule_tac Comm1) (assumption | simp)+

    moreover from `A\<^isub>R \<sharp>* P` `A\<^isub>R \<sharp>* (!Q)` `A\<^isub>R \<sharp>* xvec` PTrans QTrans `xvec \<sharp>* K` `distinct xvec` 
    have "A\<^isub>R \<sharp>* P'" and "A\<^isub>R \<sharp>* Q'" by(force dest: outputFreshChainDerivative)+
    moreover with RTrans FrR `distinct A\<^isub>R` `A\<^isub>R \<sharp>* R` `A\<^isub>R \<sharp>* N` `A\<^isub>R \<sharp>* \<Psi>` `A\<^isub>R \<sharp>* P` `A\<^isub>R \<sharp>* (!Q)` `A\<^isub>R \<sharp>* M`
    obtain \<Psi>' A\<^isub>R' \<Psi>\<^isub>R' where FrR': "extractFrame R' = \<langle>A\<^isub>R', \<Psi>\<^isub>R'\<rangle>" and "\<Psi>\<^isub>R \<otimes> \<Psi>' \<simeq> \<Psi>\<^isub>R'" and "A\<^isub>R' \<sharp>* \<Psi>"
                         and "A\<^isub>R' \<sharp>* P'" and "A\<^isub>R' \<sharp>* Q'" and "A\<^isub>R' \<sharp>* P" and "A\<^isub>R' \<sharp>* Q"
      by(rule_tac C="(\<Psi>, P, P', Q, Q')" and C'=\<Psi> in expandFrame) auto

    moreover 
    { 
      from `(\<Psi> \<otimes> \<Psi>\<^isub>R, P', T \<parallel> !P) \<in> Rel` have "((\<Psi> \<otimes> \<Psi>\<^isub>R) \<otimes> \<Psi>', P', T \<parallel> !P) \<in> Rel" by(rule cExt)
      with `\<Psi>\<^isub>R \<otimes> \<Psi>' \<simeq> \<Psi>\<^isub>R'` have "(\<Psi> \<otimes> \<Psi>\<^isub>R', P', T \<parallel> !P) \<in> Rel"
	by(metis Associativity StatEq compositionSym) 
      with FrR' `A\<^isub>R' \<sharp>* \<Psi>` `A\<^isub>R' \<sharp>* P'` `A\<^isub>R' \<sharp>* P` suppT have "(\<Psi>, R' \<parallel> P', R' \<parallel> (T \<parallel> !P)) \<in> Rel"
	by(rule_tac FrameParPres) (auto simp add: fresh_star_def fresh_def psi.supp)
      hence "(\<Psi>, R' \<parallel> P', (R' \<parallel> T) \<parallel> !P) \<in> Rel" by(blast intro: Assoc Trans)
      with `xvec \<sharp>* \<Psi>` `xvec \<sharp>* P` have "(\<Psi>, \<lparr>\<nu>*xvec\<rparr>(R' \<parallel> P'), (\<lparr>\<nu>*xvec\<rparr>(R' \<parallel> T)) \<parallel> !P) \<in> Rel"
	by(metis ResPres psiFreshVec ScopeExt Trans)
      moreover from `(\<Psi>, P, Q) \<in> Rel` `guarded P` `guarded Q` have "(\<Psi>, (\<lparr>\<nu>*xvec\<rparr>(R' \<parallel> T)) \<parallel> !P, (\<lparr>\<nu>*xvec\<rparr>(R' \<parallel> T)) \<parallel> !Q) \<in> Rel'"
	by(rule C1)
      moreover from `(\<Psi> \<otimes> \<Psi>\<^isub>R, Q', S \<parallel> !Q) \<in> Rel` `(\<Psi> \<otimes> \<Psi>\<^isub>R, S, T) \<in> Rel` have "(\<Psi> \<otimes> \<Psi>\<^isub>R, Q', T \<parallel> !Q) \<in> Rel"
	by(blast intro: ParPres Trans)
      hence "((\<Psi> \<otimes> \<Psi>\<^isub>R) \<otimes> \<Psi>', Q', T \<parallel> !Q) \<in> Rel" by(rule cExt)
      with `\<Psi>\<^isub>R \<otimes> \<Psi>' \<simeq> \<Psi>\<^isub>R'` have "(\<Psi> \<otimes> \<Psi>\<^isub>R', Q', T \<parallel> !Q) \<in> Rel"
	by(metis Associativity StatEq compositionSym) 
      with FrR' `A\<^isub>R' \<sharp>* \<Psi>` `A\<^isub>R' \<sharp>* P'` `A\<^isub>R' \<sharp>* Q'` `A\<^isub>R' \<sharp>* Q` suppT suppS have "(\<Psi>, R' \<parallel> Q', R' \<parallel> (T \<parallel> !Q)) \<in> Rel"
	by(rule_tac FrameParPres) (auto simp add: fresh_star_def fresh_def psi.supp)
      hence "(\<Psi>, R' \<parallel> Q', (R' \<parallel> T) \<parallel> !Q) \<in> Rel" by(blast intro: Assoc Trans)
      with `xvec \<sharp>* \<Psi>` `xvec \<sharp>* (!Q)` have "(\<Psi>, \<lparr>\<nu>*xvec\<rparr>(R' \<parallel> Q'), (\<lparr>\<nu>*xvec\<rparr>(R' \<parallel> T)) \<parallel> !Q) \<in> Rel"
	by(metis ResPres psiFreshVec ScopeExt Trans)
      ultimately have "(\<Psi>, \<lparr>\<nu>*xvec\<rparr>(R' \<parallel> P'), \<lparr>\<nu>*xvec\<rparr>(R' \<parallel> Q')) \<in> Rel'" by(blast intro: cSym Compose)
    }
    ultimately show ?case by blast
  next
    case(cComm2 \<Psi>\<^isub>Q M xvec N R' A\<^isub>R \<Psi>\<^isub>R K Q' A\<^isub>Q)
    from `extractFrame (!Q) = \<langle>A\<^isub>Q, \<Psi>\<^isub>Q\<rangle>` have "A\<^isub>Q = []" and "\<Psi>\<^isub>Q = SBottom'" by simp+
    have RTrans: "\<Psi> \<otimes> \<Psi>\<^isub>Q \<rhd> R \<longmapsto>M\<lparr>\<nu>*xvec\<rparr>\<langle>N\<rangle> \<prec> R'" and FrR: "extractFrame R = \<langle>A\<^isub>R, \<Psi>\<^isub>R\<rangle>" by fact+
    then obtain p \<Psi>' A\<^isub>R' \<Psi>\<^isub>R' where S: "set p \<subseteq> set xvec \<times> set(p \<bullet> xvec)"
                                and FrR': "extractFrame R' = \<langle>A\<^isub>R', \<Psi>\<^isub>R'\<rangle>" and "(p \<bullet> \<Psi>\<^isub>R) \<otimes> \<Psi>' \<simeq> \<Psi>\<^isub>R'" and "A\<^isub>R' \<sharp>* \<Psi>"
                                and "A\<^isub>R' \<sharp>* N" and "A\<^isub>R' \<sharp>* R'" and "A\<^isub>R' \<sharp>* P" and "A\<^isub>R' \<sharp>* Q" and "(p \<bullet> xvec) \<sharp>* \<Psi>"
                                and "(p \<bullet> xvec) \<sharp>* P" and "(p \<bullet> xvec) \<sharp>* Q" and "xvec \<sharp>* A\<^isub>R'" and "(p \<bullet> xvec) \<sharp>* A\<^isub>R'"
                                and "distinctPerm p" and "(p \<bullet> xvec) \<sharp>* R'" and "(p \<bullet> xvec) \<sharp>* N" 
      using `distinct A\<^isub>R` `A\<^isub>R \<sharp>* R` `A\<^isub>R \<sharp>* M` `A\<^isub>R \<sharp>* xvec` `A\<^isub>R \<sharp>* N` `A\<^isub>R \<sharp>* \<Psi>` `A\<^isub>R \<sharp>* P` `A\<^isub>R \<sharp>* (!Q)`
            `xvec \<sharp>* \<Psi>` `xvec \<sharp>* P` `xvec \<sharp>* (!Q)` `xvec \<sharp>* R` `xvec \<sharp>* M` `distinct xvec`
     by(rule_tac C="(\<Psi>, P, Q)" and C'="(\<Psi>, P, Q)" in expandFrame) (assumption | simp)+

    from RTrans S `(p \<bullet> xvec) \<sharp>* N` `(p \<bullet> xvec) \<sharp>* R'` have "\<Psi> \<otimes> \<Psi>\<^isub>Q \<rhd> R \<longmapsto>M\<lparr>\<nu>*(p \<bullet> xvec)\<rparr>\<langle>(p \<bullet> N)\<rangle> \<prec> (p \<bullet> R')"
      apply(simp add: residualInject)
      by(subst boundOutputChainAlpha''[symmetric]) auto

    moreover have QTrans: "\<Psi> \<otimes> \<Psi>\<^isub>R \<rhd> !Q \<longmapsto>K\<lparr>N\<rparr> \<prec> Q'" by fact
    with QTrans S `(p \<bullet> xvec) \<sharp>* N` have "\<Psi> \<otimes> \<Psi>\<^isub>R \<rhd> !Q \<longmapsto>K\<lparr>(p \<bullet> N)\<rparr> \<prec> (p \<bullet> Q')" using `distinctPerm p` `xvec \<sharp>* (!Q)` `(p \<bullet> xvec) \<sharp>* Q`
      by(rule_tac inputAlpha) auto
    with `(\<Psi>, P, Q) \<in> Rel` `guarded P`
    obtain P' S T where PTrans: "\<Psi> \<otimes> \<Psi>\<^isub>R \<rhd> !P \<longmapsto>K\<lparr>(p \<bullet> N)\<rparr> \<prec> P'" and "(\<Psi> \<otimes> \<Psi>\<^isub>R, P', T \<parallel> !P) \<in> Rel"
                    and "(\<Psi> \<otimes> \<Psi>\<^isub>R, (p \<bullet> Q'), S \<parallel> !Q) \<in> Rel" and "(\<Psi> \<otimes> \<Psi>\<^isub>R, S, T) \<in> Rel"
                    and suppT: "((supp T)::name set) \<subseteq> supp P'" and suppS: "((supp S)::name set) \<subseteq> supp(p \<bullet> Q')"
      by(drule_tac cSym) (auto dest: Der cExt)
    note `\<Psi> \<otimes> \<Psi>\<^isub>R \<otimes> \<Psi>\<^isub>Q \<turnstile> M \<leftrightarrow> K`
    ultimately have "\<Psi> \<rhd> R \<parallel> !P \<longmapsto>\<tau> \<prec> \<lparr>\<nu>*(p \<bullet> xvec)\<rparr>((p \<bullet> R') \<parallel> P')" 
      using PTrans FrR `\<Psi>\<^isub>Q = SBottom'` `(p \<bullet> xvec) \<sharp>* P` `A\<^isub>R \<sharp>* \<Psi>` `A\<^isub>R \<sharp>* R` `A\<^isub>R \<sharp>* M` `A\<^isub>R \<sharp>* P`
      by(rule_tac Comm2) (assumption | simp)+

    moreover from `A\<^isub>R' \<sharp>* P` `A\<^isub>R' \<sharp>* Q` `A\<^isub>R' \<sharp>* N` S `xvec \<sharp>* A\<^isub>R'` `(p \<bullet> xvec) \<sharp>* A\<^isub>R'` PTrans QTrans `distinctPerm p` have "A\<^isub>R' \<sharp>* P'" and "A\<^isub>R' \<sharp>* Q'"
      apply -
      apply(drule_tac inputFreshChainDerivative, auto)
      apply(subst pt_fresh_star_bij[OF pt_name_inst, OF at_name_inst, symmetric, of _ _ p], simp)
      by(force dest: inputFreshChainDerivative)+
    from `xvec \<sharp>* P` `(p \<bullet> xvec) \<sharp>* N` PTrans `distinctPerm p` have "(p \<bullet> xvec) \<sharp>* (p \<bullet> P')"
      apply(drule_tac inputFreshChainDerivative, simp)
      apply(subst pt_fresh_star_bij[OF pt_name_inst, OF at_name_inst, symmetric, of _ _ p], simp)
      by(subst pt_fresh_star_bij[OF pt_name_inst, OF at_name_inst, symmetric, of _ _ p], simp)

    { 
      from `(\<Psi> \<otimes> \<Psi>\<^isub>R, P', T \<parallel> !P) \<in> Rel` have "(p \<bullet> (\<Psi> \<otimes> \<Psi>\<^isub>R), (p \<bullet> P'), p \<bullet> (T \<parallel> !P)) \<in> Rel"
	by(rule Closed)
      with `xvec \<sharp>* \<Psi>` `(p \<bullet> xvec) \<sharp>* \<Psi>` `xvec \<sharp>* P` `(p \<bullet> xvec) \<sharp>* P` S have "(\<Psi> \<otimes> (p \<bullet> \<Psi>\<^isub>R), p \<bullet> P', (p \<bullet> T) \<parallel> !P) \<in> Rel"
	by(simp add: eqvts)     
      hence "((\<Psi> \<otimes> (p \<bullet> \<Psi>\<^isub>R)) \<otimes> \<Psi>', p \<bullet> P', (p \<bullet> T) \<parallel> !P) \<in> Rel" by(rule cExt)
      with `(p \<bullet> \<Psi>\<^isub>R) \<otimes> \<Psi>' \<simeq> \<Psi>\<^isub>R'` have "(\<Psi> \<otimes> \<Psi>\<^isub>R', (p \<bullet> P'), (p \<bullet> T) \<parallel> !P) \<in> Rel"
	by(metis Associativity StatEq compositionSym) 
      with FrR' `A\<^isub>R' \<sharp>* \<Psi>` `A\<^isub>R' \<sharp>* P'` `A\<^isub>R' \<sharp>* P` `xvec \<sharp>* A\<^isub>R'` `(p \<bullet> xvec) \<sharp>* A\<^isub>R'` S `distinctPerm p` suppT
      have "(\<Psi>, R' \<parallel> (p \<bullet> P'), R' \<parallel> ((p \<bullet> T) \<parallel> !P)) \<in> Rel"
	apply(rule_tac FrameParPres)
	apply(assumption | simp add: freshChainSimps)+
	by(auto simp add: fresh_star_def fresh_def)
      hence "(\<Psi>, R' \<parallel> (p \<bullet> P'), (R' \<parallel> (p \<bullet> T)) \<parallel> !P) \<in> Rel" by(blast intro: Assoc Trans)
      with `xvec \<sharp>* \<Psi>` `xvec \<sharp>* P` have "(\<Psi>, \<lparr>\<nu>*xvec\<rparr>(R' \<parallel> (p \<bullet> P')), (\<lparr>\<nu>*xvec\<rparr>(R' \<parallel> (p \<bullet> T))) \<parallel> !P) \<in> Rel"
	by(metis ResPres psiFreshVec ScopeExt Trans)
      hence "(\<Psi>, \<lparr>\<nu>*(p \<bullet> xvec)\<rparr>((p \<bullet> R') \<parallel> P'), (\<lparr>\<nu>*xvec\<rparr>(R' \<parallel> (p \<bullet> T))) \<parallel> !P) \<in> Rel"
      using `(p \<bullet> xvec) \<sharp>* R'` `(p \<bullet> xvec) \<sharp>* (p \<bullet> P')` S `distinctPerm p`
      apply(erule_tac rev_mp) by(subst resChainAlpha[of p]) auto
      moreover from `(\<Psi>, P, Q) \<in> Rel` `guarded P` `guarded Q` have "(\<Psi>, (\<lparr>\<nu>*xvec\<rparr>(R' \<parallel> (p \<bullet> T))) \<parallel> !P, (\<lparr>\<nu>*xvec\<rparr>(R' \<parallel> (p \<bullet> T))) \<parallel> !Q) \<in> Rel'"
	by(rule C1)
      moreover from `(\<Psi> \<otimes> \<Psi>\<^isub>R, (p \<bullet> Q'), S \<parallel> !Q) \<in> Rel` `(\<Psi> \<otimes> \<Psi>\<^isub>R, S, T) \<in> Rel` have "(\<Psi> \<otimes> \<Psi>\<^isub>R, (p \<bullet> Q'), T \<parallel> !Q) \<in> Rel"
	by(blast intro: ParPres Trans)
      hence "(p \<bullet> (\<Psi> \<otimes> \<Psi>\<^isub>R), p \<bullet> p \<bullet> Q', p \<bullet> (T \<parallel> !Q)) \<in> Rel" by(rule Closed)
      with S `xvec \<sharp>* \<Psi>` `(p \<bullet> xvec) \<sharp>* \<Psi>` `xvec \<sharp>* (!Q)` `(p \<bullet> xvec) \<sharp>* Q` `distinctPerm p`
      have "(\<Psi> \<otimes> (p \<bullet> \<Psi>\<^isub>R), Q', (p \<bullet> T) \<parallel> !Q) \<in> Rel" by(simp add: eqvts)
      hence "((\<Psi> \<otimes> (p \<bullet> \<Psi>\<^isub>R)) \<otimes> \<Psi>', Q', (p \<bullet> T) \<parallel> !Q) \<in> Rel" by(rule cExt)
      with `(p \<bullet> \<Psi>\<^isub>R) \<otimes> \<Psi>' \<simeq> \<Psi>\<^isub>R'` have "(\<Psi> \<otimes> \<Psi>\<^isub>R', Q', (p \<bullet> T) \<parallel> !Q) \<in> Rel"
	by(metis Associativity StatEq compositionSym) 
      with FrR' `A\<^isub>R' \<sharp>* \<Psi>` `A\<^isub>R' \<sharp>* P'` `A\<^isub>R' \<sharp>* Q'` `A\<^isub>R' \<sharp>* Q` suppT suppS `xvec \<sharp>* A\<^isub>R'` `(p \<bullet> xvec) \<sharp>* A\<^isub>R'` S `distinctPerm p` 
      have "(\<Psi>, R' \<parallel> Q', R' \<parallel> ((p \<bullet> T) \<parallel> !Q)) \<in> Rel"
	apply(rule_tac FrameParPres)
	apply(assumption | simp)+
	apply(simp add: freshChainSimps)
	by(auto simp add: fresh_star_def fresh_def)
      hence "(\<Psi>, R' \<parallel> Q', (R' \<parallel> (p \<bullet> T)) \<parallel> !Q) \<in> Rel" by(blast intro: Assoc Trans)
      with `xvec \<sharp>* \<Psi>` `xvec \<sharp>* (!Q)` have "(\<Psi>, \<lparr>\<nu>*xvec\<rparr>(R' \<parallel> Q'), (\<lparr>\<nu>*xvec\<rparr>(R' \<parallel> (p \<bullet> T))) \<parallel> !Q) \<in> Rel"
	by(metis ResPres psiFreshVec ScopeExt Trans)
      ultimately have "(\<Psi>, \<lparr>\<nu>*(p \<bullet> xvec)\<rparr>((p \<bullet> R') \<parallel> P'), \<lparr>\<nu>*xvec\<rparr>(R' \<parallel> Q')) \<in> Rel'" by(blast intro: cSym Compose)
    }
    ultimately show ?case by blast
  qed
qed
notation relcomp (infixr "O" 75)
end

end
