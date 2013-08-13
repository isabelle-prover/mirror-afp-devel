(* 
   Title: Psi-calculi   
   Author/Maintainer: Jesper Bengtson (jebe@itu.dk), 2012
*)
theory Weak_Semantics
  imports Semantics
begin

context env begin

inductive tauChain :: "'b \<Rightarrow> ('a, 'b, 'c) psi \<Rightarrow> ('a, 'b, 'c) psi \<Rightarrow> bool" ("_ \<rhd> _ \<Longrightarrow>\<^sub>\<tau> _" [80, 80, 80] 80)
  where
  TauBase: "\<Psi> \<rhd> P \<Longrightarrow>\<^sub>\<tau> P"
| TauStep: "\<lbrakk>\<Psi> \<rhd> P \<longmapsto>\<tau> \<prec> P'; \<Psi> \<rhd> P' \<Longrightarrow>\<^sub>\<tau> P''\<rbrakk> \<Longrightarrow> \<Psi> \<rhd> P \<Longrightarrow>\<^sub>\<tau> P''"

equivariance env.tauChain

lemma tauChainFresh:
  fixes \<Psi> :: 'b
  and   P  :: "('a, 'b, 'c) psi"
  and   P' :: "('a, 'b, 'c) psi"
  and   x  :: name

  assumes "\<Psi> \<rhd> P \<Longrightarrow>\<^sub>\<tau> P'"
  and     "x \<sharp> P"

  shows "x \<sharp> P'"
using assms
by(induct rule: Tau_Chain.induct) (auto dest: tauFreshDerivative)

lemma tauChainFreshChain:
  fixes \<Psi>    :: 'b
  and   P     :: "('a, 'b, 'c) psi"
  and   P'    :: "('a, 'b, 'c) psi"
  and   xvec  :: "name list"

  assumes "\<Psi> \<rhd> P \<Longrightarrow>\<^sub>\<tau> P'"
  and     "xvec \<sharp>* P"

  shows "xvec \<sharp>* P'"
using assms
by(induct xvec) (auto intro: tauChainFresh)

lemma tauChainConcat:
  fixes \<Psi>   :: 'b
  and   P   :: "('a, 'b, 'c) psi"
  and   P'  :: "('a, 'b, 'c) psi"
  and   P'' :: "('a, 'b, 'c) psi"

  assumes "\<Psi> \<rhd> P \<Longrightarrow>\<^sub>\<tau> P'"
  and     "\<Psi> \<rhd> P' \<longmapsto>\<tau> \<prec> P''"

  shows "\<Psi> \<rhd> P \<Longrightarrow>\<^sub>\<tau> P''"
using assms
by(induct rule: Tau_Chain.induct) (auto intro: TauBase TauStep)

lemma tauChainAppend:
  fixes \<Psi>   :: 'b
  and   P   :: "('a, 'b, 'c) psi"
  and   P'  :: "('a, 'b, 'c) psi"
  and   P'' :: "('a, 'b, 'c) psi"
  
  assumes "\<Psi> \<rhd> P \<Longrightarrow>\<^sub>\<tau> P'"
  and     "\<Psi> \<rhd> P' \<Longrightarrow>\<^sub>\<tau> P''"

  shows "\<Psi> \<rhd> P \<Longrightarrow>\<^sub>\<tau> P''"
using `\<Psi> \<rhd> P' \<Longrightarrow>\<^sub>\<tau> P''` `\<Psi> \<rhd> P \<Longrightarrow>\<^sub>\<tau> P'`
by(induct arbitrary: P rule: Tau_Chain.induct) (auto intro: tauChainConcat)

lemma tauChainResPres:
  fixes \<Psi> :: 'b
  and   P  :: "('a, 'b, 'c) psi"
  and   P' :: "('a, 'b, 'c) psi"
  and   x  :: name  

  assumes "\<Psi> \<rhd> P \<Longrightarrow>\<^sub>\<tau> P'"
  and     "x \<sharp> \<Psi>"

  shows "\<Psi> \<rhd> \<lparr>\<nu>x\<rparr>P \<Longrightarrow>\<^sub>\<tau> \<lparr>\<nu>x\<rparr>P'"
using assms
proof(induct rule: Tau_Chain.induct)
  case(TauBase \<Psi> P)
  show ?case by(rule Tau_Chain.TauBase)
next
  case(TauStep \<Psi> P P' P'')
  thus ?case by(force intro: Tau_Chain.TauStep ScopeF)
qed

lemma tauChainResChainPres:
  fixes \<Psi>    :: 'b
  and   P    :: "('a, 'b, 'c) psi"
  and   P'   :: "('a, 'b, 'c) psi"
  and   xvec :: "name list"

  assumes "\<Psi> \<rhd> P \<Longrightarrow>\<^sub>\<tau> P'"
  and     "xvec \<sharp>* \<Psi>"

  shows "\<Psi> \<rhd> \<lparr>\<nu>*xvec\<rparr>P \<Longrightarrow>\<^sub>\<tau> \<lparr>\<nu>*xvec\<rparr>P'"
using assms
by(induct xvec) (auto intro: tauChainResPres)

lemma tauChainPar1:
  fixes \<Psi>  :: 'b
  and   \<Psi>\<^sub>Q :: 'b
  and   P   :: "('a, 'b, 'c) psi"
  and   P'  :: "('a, 'b, 'c) psi"
  and   Q   :: "('a, 'b, 'c) psi"
  and   A\<^sub>Q :: "name list"

  assumes "\<Psi> \<otimes> \<Psi>\<^sub>Q \<rhd> P \<Longrightarrow>\<^sub>\<tau> P'"
  and     "extractFrame Q = \<langle>A\<^sub>Q, \<Psi>\<^sub>Q\<rangle>"
  and     "A\<^sub>Q \<sharp>* \<Psi>"
  and     "A\<^sub>Q \<sharp>* P"

  shows "\<Psi> \<rhd> P \<parallel> Q \<Longrightarrow>\<^sub>\<tau> P' \<parallel> Q"
using assms
proof(induct \<Psi>=="\<Psi> \<otimes> \<Psi>\<^sub>Q" P P' rule: Tau_Chain.induct)
  case(TauBase \<Psi>' P)
  show ?case by(rule Tau_Chain.TauBase)
next
  case(TauStep \<Psi>' P P' P'')
  thus ?case by(fastforce intro: Tau_Chain.TauStep Par1F dest: tauFreshChainDerivative)
qed

lemma tauChainPar2:
  fixes \<Psi>  :: 'b
  and   \<Psi>\<^sub>P :: 'b
  and   Q   :: "('a, 'b, 'c) psi"
  and   Q'  :: "('a, 'b, 'c) psi"
  and   P   :: "('a, 'b, 'c) psi"
  and   A\<^sub>P :: "name list"

  assumes "\<Psi> \<otimes> \<Psi>\<^sub>P \<rhd> Q \<Longrightarrow>\<^sub>\<tau> Q'"
  and     "extractFrame P = \<langle>A\<^sub>P, \<Psi>\<^sub>P\<rangle>"
  and     "A\<^sub>P \<sharp>* \<Psi>"
  and     "A\<^sub>P \<sharp>* Q"

  shows "\<Psi> \<rhd> P \<parallel> Q \<Longrightarrow>\<^sub>\<tau> P \<parallel> Q'"
using assms
proof(induct \<Psi>=="\<Psi> \<otimes> \<Psi>\<^sub>P" Q Q' rule: Tau_Chain.induct)
  case(TauBase \<Psi>' Q)
  show ?case by(rule Tau_Chain.TauBase)
next
  case(TauStep \<Psi>' Q Q' Q'')
  thus ?case by(fastforce intro: Tau_Chain.TauStep Par2F dest: tauFreshChainDerivative)
qed

lemma tauChainCases:
  fixes \<Psi>  :: 'b
  and   P   :: "('a, 'b, 'c) psi"
  and   P'  :: "('a, 'b, 'c) psi"
  and   \<Psi>' :: 'b

  assumes "\<Psi> \<rhd> P \<Longrightarrow>\<^sub>\<tau> P'"
  and     "P \<noteq> P'"
  and     "(\<phi>, P) mem Cs"
  and     "\<Psi> \<turnstile> \<phi>"
  and     "guarded P"

  shows "\<Psi> \<rhd> Cases Cs \<Longrightarrow>\<^sub>\<tau> P'"
using assms
proof(induct rule: Tau_Chain.induct)
  case(TauBase \<Psi> P)
  from `P \<noteq> P` show ?case by simp
next
  case(TauStep \<Psi> P P' P'')
  from `\<Psi> \<rhd> P \<longmapsto>\<tau> \<prec> P'` `(\<phi>, P) mem Cs` `\<Psi> \<turnstile> \<phi>` `guarded P`
  have "\<Psi> \<rhd> Cases Cs \<longmapsto>\<tau> \<prec> P'" by(rule Case)
  thus ?case using `\<Psi> \<rhd> P' \<Longrightarrow>\<^sub>\<tau> P''` by(rule Tau_Chain.TauStep)
qed

lemma tauChainStatEq:
  fixes \<Psi>  :: 'b
  and   P   :: "('a, 'b, 'c) psi"
  and   P'  :: "('a, 'b, 'c) psi"
  and   \<Psi>' :: 'b

  assumes "\<Psi> \<rhd> P \<Longrightarrow>\<^sub>\<tau> P'"
  and     "\<Psi> \<simeq> \<Psi>'"

  shows "\<Psi>' \<rhd> P \<Longrightarrow>\<^sub>\<tau> P'"
using assms
proof(induct rule: Tau_Chain.induct)
  case(TauBase \<Psi> P)
  show ?case by(rule Tau_Chain.TauBase)
next
  case(TauStep \<Psi> P P' P'')
  thus ?case by(auto intro: Tau_Chain.TauStep dest: statEqTransition)
qed

definition weakOutputTransition :: "'b \<Rightarrow> ('a, 'b, 'c) psi \<Rightarrow>  ('a, 'b, 'c) psi \<Rightarrow> 'a \<Rightarrow> name list \<Rightarrow> 'a \<Rightarrow> ('a, 'b, 'c) psi \<Rightarrow> bool" ("_ : _ \<rhd> _ \<Longrightarrow>_\<lparr>\<nu>*_\<rparr>\<langle>_\<rangle> \<prec> _" [80, 80, 80, 80, 80, 80, 80] 80)
where
  "\<Psi> : Q \<rhd> P \<Longrightarrow>M\<lparr>\<nu>*xvec\<rparr>\<langle>N\<rangle> \<prec> P' \<equiv> \<exists>P''. \<Psi> \<rhd> P \<Longrightarrow>\<^sub>\<tau> P'' \<and> (insertAssertion (extractFrame Q) \<Psi>) \<hookrightarrow>\<^sub>F (insertAssertion (extractFrame P'') \<Psi>) \<and>
                                          \<Psi> \<rhd> P'' \<longmapsto>M\<lparr>\<nu>*xvec\<rparr>\<langle>N\<rangle> \<prec> P'"

definition weakInputTransition :: "'b \<Rightarrow> ('a, 'b, 'c) psi \<Rightarrow> ('a, 'b, 'c) psi \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> ('a, 'b, 'c) psi \<Rightarrow> bool" ("_ : _ \<rhd> _ \<Longrightarrow>_\<lparr>_\<rparr> \<prec> _" [80, 80, 80, 80, 80] 80)
where
  "\<Psi> : Q \<rhd> P \<Longrightarrow>M\<lparr>N\<rparr> \<prec> P' \<equiv> (\<exists>P''. \<Psi> \<rhd> P \<Longrightarrow>\<^sub>\<tau> P'' \<and> insertAssertion (extractFrame Q) \<Psi> \<hookrightarrow>\<^sub>F insertAssertion (extractFrame P'') \<Psi> \<and> 
                                    \<Psi> \<rhd> P'' \<longmapsto>M\<lparr>N\<rparr> \<prec> P')"

abbreviation
  weakOutputJudge ("_ : _ \<rhd> _ \<Longrightarrow>_\<langle>_\<rangle> \<prec> _" [80, 80, 80, 80, 80] 80) where "\<Psi> : Q \<rhd> P \<Longrightarrow>M\<langle>N\<rangle> \<prec> P' \<equiv> \<Psi> : Q \<rhd> P \<Longrightarrow>M\<lparr>\<nu>*([])\<rparr>\<langle>N\<rangle> \<prec> P'"

lemma weakOutputTransitionI:
  fixes \<Psi>   :: 'b
  and   Q    :: "('a, 'b, 'c) psi"
  and   P    :: "('a, 'b, 'c) psi"
  and   P''  :: "('a, 'b, 'c) psi"
  and   M    :: 'a
  and   xvec :: "name list"
  and   N    :: 'a
  and   P'   :: "('a, 'b, 'c) psi"

  assumes "\<Psi> \<rhd> P \<Longrightarrow>\<^sub>\<tau> P''"
  and     "insertAssertion (extractFrame Q) \<Psi> \<hookrightarrow>\<^sub>F insertAssertion (extractFrame P'') \<Psi>"
  and     "\<Psi> \<rhd> P'' \<longmapsto>M\<lparr>\<nu>*xvec\<rparr>\<langle>N\<rangle> \<prec> P'"

  shows "\<Psi> : Q \<rhd> P \<Longrightarrow>M\<lparr>\<nu>*xvec\<rparr>\<langle>N\<rangle> \<prec> P'"
using assms
by(auto simp add: weakOutputTransition_def)

lemma weakOutputTransitionE:
  fixes \<Psi>   :: 'b
  and   Q    :: "('a, 'b, 'c) psi"
  and   P    :: "('a, 'b, 'c) psi"
  and   M    :: 'a
  and   xvec :: "name list"
  and   N    :: 'a
  and   P'   :: "('a, 'b, 'c) psi"

  assumes "\<Psi> : Q \<rhd> P \<Longrightarrow>M\<lparr>\<nu>*xvec\<rparr>\<langle>N\<rangle> \<prec> P'"

  obtains P'' where "\<Psi> \<rhd> P \<Longrightarrow>\<^sub>\<tau> P''" and "insertAssertion (extractFrame Q) \<Psi> \<hookrightarrow>\<^sub>F insertAssertion (extractFrame P'') \<Psi>"
                 and "\<Psi> \<rhd> P'' \<longmapsto>M\<lparr>\<nu>*xvec\<rparr>\<langle>N\<rangle> \<prec> P'"
using assms
by(auto simp add: weakOutputTransition_def)

lemma weakInputTransitionE:
  fixes \<Psi>  :: 'b
  and   Q   :: "('a, 'b, 'c) psi"
  and   P   :: "('a, 'b, 'c) psi"
  and   M   :: 'a
  and   N   :: 'a
  and   P'  :: "('a, 'b, 'c) psi"

  assumes "\<Psi> : Q \<rhd> P \<Longrightarrow>M\<lparr>N\<rparr> \<prec> P'"

  obtains P'' where "\<Psi> \<rhd> P \<Longrightarrow>\<^sub>\<tau> P''" and "insertAssertion (extractFrame Q) \<Psi> \<hookrightarrow>\<^sub>F insertAssertion (extractFrame P'') \<Psi>"
                 and "\<Psi> \<rhd> P'' \<longmapsto>M\<lparr>N\<rparr> \<prec> P'"
using assms
by(auto simp add: weakInputTransition_def)

lemma weakInputTransitionI:
  fixes \<Psi>   :: 'b
  and   Q    :: "('a, 'b, 'c) psi"
  and   P    :: "('a, 'b, 'c) psi"
  and   P''' :: "('a, 'b, 'c) psi"
  and   M    :: 'a
  and   N    :: 'a
  and   \<Psi>'  :: 'b
  and   P''  :: "('a, 'b, 'c) psi"
  and   P'   :: "('a, 'b, 'c) psi"

  assumes "\<Psi> \<rhd> P \<Longrightarrow>\<^sub>\<tau> P''"
  and     "insertAssertion (extractFrame Q) \<Psi> \<hookrightarrow>\<^sub>F insertAssertion (extractFrame P'') \<Psi>"
  and     "\<Psi> \<rhd> P'' \<longmapsto>M\<lparr>N\<rparr> \<prec> P'"

  shows "\<Psi> : Q \<rhd> P \<Longrightarrow>M\<lparr>N\<rparr> \<prec> P'"
using assms
by(auto simp add: weakInputTransition_def)

lemma weakInputTransitionClosed[eqvt]:
  fixes \<Psi>  :: 'b
  and   Q   :: "('a, 'b, 'c) psi"
  and   P   :: "('a, 'b, 'c) psi"
  and   M   :: 'a
  and   N   :: 'a
  and   P'  :: "('a, 'b, 'c) psi"
  and   p   :: "name prm"

  assumes "\<Psi> : Q \<rhd> P \<Longrightarrow>M\<lparr>N\<rparr> \<prec> P'"

  shows "(p \<bullet> \<Psi>) : (p \<bullet> Q) \<rhd> (p \<bullet> P) \<Longrightarrow>(p \<bullet> M)\<lparr>(p \<bullet> N)\<rparr> \<prec> (p \<bullet> P')"
proof -
  from assms obtain P'' where "\<Psi> \<rhd> P \<Longrightarrow>\<^sub>\<tau> P''" and "insertAssertion (extractFrame Q) \<Psi> \<hookrightarrow>\<^sub>F insertAssertion (extractFrame P'') \<Psi>"
                           and "\<Psi> \<rhd> P'' \<longmapsto>M\<lparr>N\<rparr> \<prec> P'"
    by(rule weakInputTransitionE)
  from `\<Psi> \<rhd> P \<Longrightarrow>\<^sub>\<tau> P''` have "(p \<bullet> \<Psi>) \<rhd> (p \<bullet> P) \<Longrightarrow>\<^sub>\<tau> (p \<bullet> P'')"
    by(rule Tau_Chain.eqvt)
  moreover from `insertAssertion (extractFrame Q) \<Psi> \<hookrightarrow>\<^sub>F insertAssertion (extractFrame P'') \<Psi>`
  have "(p \<bullet> (insertAssertion (extractFrame Q) \<Psi>)) \<hookrightarrow>\<^sub>F (p \<bullet> (insertAssertion (extractFrame P'') \<Psi>))"
    by(rule FrameStatImpClosed)
  hence "insertAssertion (extractFrame(p \<bullet> Q)) (p \<bullet> \<Psi>) \<hookrightarrow>\<^sub>F insertAssertion (extractFrame(p \<bullet> P'')) (p \<bullet> \<Psi>)" by(simp add: eqvts)
  moreover from `\<Psi> \<rhd> P'' \<longmapsto>M\<lparr>N\<rparr> \<prec> P'` have "(p \<bullet> \<Psi>) \<rhd> (p \<bullet> P'') \<longmapsto>(p \<bullet> (M\<lparr>N\<rparr> \<prec> P'))"
    by(rule semantics.eqvt)
  hence "(p \<bullet> \<Psi>) \<rhd> (p \<bullet> P'') \<longmapsto>(p \<bullet> M)\<lparr>(p \<bullet> N)\<rparr> \<prec> (p \<bullet> P')" by(simp add: eqvts)
  ultimately show ?thesis by(rule weakInputTransitionI)
qed

lemma weakOutputTransitionClosed[eqvt]:
  fixes \<Psi>   :: 'b
  and   Q    :: "('a, 'b, 'c) psi"
  and   P    :: "('a, 'b, 'c) psi"
  and   M    :: 'a
  and   xvec :: "name list"
  and   N    :: 'a
  and   P'   :: "('a, 'b, 'c) psi"
  and   p    :: "name prm"

  assumes "\<Psi> : Q \<rhd> P \<Longrightarrow>M\<lparr>\<nu>*xvec\<rparr>\<langle>N\<rangle> \<prec> P'"

  shows "(p \<bullet> \<Psi>) : (p \<bullet> Q) \<rhd> (p \<bullet> P) \<Longrightarrow>(p \<bullet> M)\<lparr>\<nu>*(p \<bullet> xvec)\<rparr>\<langle>(p \<bullet> N)\<rangle> \<prec> (p \<bullet> P')"
proof -
  from assms obtain P'' where "\<Psi> \<rhd> P \<Longrightarrow>\<^sub>\<tau> P''" and "insertAssertion (extractFrame Q) \<Psi> \<hookrightarrow>\<^sub>F insertAssertion (extractFrame P'') \<Psi>"
                           and "\<Psi> \<rhd> P'' \<longmapsto>M\<lparr>\<nu>*xvec\<rparr>\<langle>N\<rangle> \<prec> P'"
    by(rule weakOutputTransitionE)

  from `\<Psi> \<rhd> P \<Longrightarrow>\<^sub>\<tau> P''` have "(p \<bullet> \<Psi>) \<rhd> (p \<bullet> P) \<Longrightarrow>\<^sub>\<tau> (p \<bullet> P'')"
    by(rule Tau_Chain.eqvt)
  moreover from `insertAssertion (extractFrame Q) \<Psi> \<hookrightarrow>\<^sub>F insertAssertion (extractFrame P'') \<Psi>` 
  have "(p \<bullet> (insertAssertion (extractFrame Q) \<Psi>)) \<hookrightarrow>\<^sub>F (p \<bullet> (insertAssertion (extractFrame P'') \<Psi>))"
    by(rule FrameStatImpClosed)
  hence "insertAssertion (extractFrame(p \<bullet> Q)) (p \<bullet> \<Psi>) \<hookrightarrow>\<^sub>F insertAssertion (extractFrame(p \<bullet> P'')) (p \<bullet> \<Psi>)" by(simp add: eqvts)
  moreover from `\<Psi> \<rhd> P'' \<longmapsto>M\<lparr>\<nu>*xvec\<rparr>\<langle>N\<rangle> \<prec> P'` have "(p \<bullet> \<Psi>) \<rhd> (p \<bullet> P'') \<longmapsto>(p \<bullet> (M\<lparr>\<nu>*xvec\<rparr>\<langle>N\<rangle> \<prec> P'))"
    by(rule semantics.eqvt)
  hence "(p \<bullet> \<Psi>) \<rhd> (p \<bullet> P'') \<longmapsto>(p \<bullet> M)\<lparr>\<nu>*(p \<bullet> xvec)\<rparr>\<langle>(p \<bullet> N)\<rangle> \<prec> (p \<bullet> P')" by(simp add: eqvts)
  ultimately show ?thesis by(rule weakOutputTransitionI)
qed

lemma weakOutputAlpha:
  fixes \<Psi>   :: 'b
  and   Q    :: "('a, 'b, 'c) psi"
  and   P    :: "('a, 'b, 'c) psi"
  and   M    :: 'a
  and   xvec :: "name list"
  and   N    :: 'a
  and   P'   :: "('a, 'b, 'c) psi"
  and   p    :: "name prm"
  and   yvec :: "name list"

  assumes PTrans: "\<Psi> : Q \<rhd> P \<Longrightarrow>M\<lparr>\<nu>*xvec\<rparr>\<langle>N\<rangle> \<prec> P'"
  and     S: "set p \<subseteq> set xvec \<times> set(p \<bullet> xvec)"
  and     "xvec \<sharp>* (p \<bullet> xvec)"
  and     "(p \<bullet> xvec) \<sharp>* P"
  and     "(p \<bullet> xvec) \<sharp>* N"

  shows "\<Psi> : Q \<rhd> P \<Longrightarrow>M\<lparr>\<nu>*(p \<bullet> xvec)\<rparr>\<langle>(p \<bullet> N)\<rangle> \<prec> (p \<bullet> P')"
proof -
  from PTrans obtain P'' where PChain: "\<Psi> \<rhd> P \<Longrightarrow>\<^sub>\<tau> P''" and QeqP'': "insertAssertion (extractFrame Q) \<Psi> \<hookrightarrow>\<^sub>F insertAssertion (extractFrame P'') \<Psi>"
                           and P''Trans: "\<Psi> \<rhd> P'' \<longmapsto>M\<lparr>\<nu>*xvec\<rparr>\<langle>N\<rangle> \<prec> P'"
    by(rule weakOutputTransitionE)

  note PChain QeqP''
  moreover from PChain `(p \<bullet> xvec) \<sharp>* P` have "(p \<bullet> xvec) \<sharp>* P''" by(rule tauChainFreshChain)
  with P''Trans `xvec \<sharp>* (p \<bullet> xvec)` `(p \<bullet> xvec) \<sharp>* N` have "(p \<bullet> xvec) \<sharp>* P'"
    by(force intro: outputFreshChainDerivative)
  with P''Trans S `(p \<bullet> xvec) \<sharp>* N` have "\<Psi> \<rhd> P'' \<longmapsto>M\<lparr>\<nu>*(p \<bullet> xvec)\<rparr>\<langle>(p \<bullet> N)\<rangle> \<prec> (p \<bullet> P')"
    by(simp add: boundOutputChainAlpha'')
  ultimately show ?thesis by(rule weakOutputTransitionI)
qed

lemma weakOutputAlpha':
  fixes \<Psi>   :: 'b
  and   Q    :: "('a, 'b, 'c) psi"
  and   P    :: "('a, 'b, 'c) psi"
  and   M    :: 'a
  and   xvec :: "name list"
  and   N    :: 'a
  and   P'   :: "('a, 'b, 'c) psi"
  and   p    :: "name prm"
  and   yvec :: "name list"

  assumes PTrans: "\<Psi> : Q \<rhd> P \<Longrightarrow>M\<lparr>\<nu>*(p \<bullet> xvec)\<rparr>\<langle>(p \<bullet> N)\<rangle> \<prec> P'"
  and     S: "set p \<subseteq> set xvec \<times> set(p \<bullet> xvec)"
  and     "distinctPerm p"
  and     "xvec \<sharp>* P"
  and     "xvec \<sharp>* (p \<bullet> xvec)"

  shows "\<Psi> : Q \<rhd> P \<Longrightarrow>M\<lparr>\<nu>*xvec\<rparr>\<langle>N\<rangle> \<prec> (p \<bullet> P')"
proof -
  from PTrans obtain P'' where PChain: "\<Psi> \<rhd> P \<Longrightarrow>\<^sub>\<tau> P''" and QeqP'': "insertAssertion (extractFrame Q) \<Psi> \<hookrightarrow>\<^sub>F insertAssertion (extractFrame P'') \<Psi>"
                           and P''Trans: "\<Psi> \<rhd> P'' \<longmapsto>M\<lparr>\<nu>*(p \<bullet> xvec)\<rparr>\<langle>(p \<bullet> N)\<rangle> \<prec> P'"
    by(rule weakOutputTransitionE)


  note PChain QeqP''
  moreover from PChain `xvec \<sharp>* P` have "xvec \<sharp>* P''" by(rule tauChainFreshChain)
  with P''Trans `xvec \<sharp>* (p \<bullet> xvec)` have "xvec \<sharp>* (p \<bullet> N)" and "xvec \<sharp>* P'"
    by(force intro: outputFreshChainDerivative)+
  hence "(p \<bullet> xvec) \<sharp>* (p \<bullet> p \<bullet> N)" and "(p \<bullet> xvec) \<sharp>* (p \<bullet> P')"
    by(simp add: pt_fresh_star_bij[OF pt_name_inst, OF at_name_inst])+
  with `distinctPerm p` have "(p \<bullet> xvec) \<sharp>* N" and "(p \<bullet> xvec) \<sharp>* (p \<bullet> P')" by simp+
  with P''Trans S `distinctPerm p` have "\<Psi> \<rhd> P'' \<longmapsto>M\<lparr>\<nu>*xvec\<rparr>\<langle>N\<rangle> \<prec> (p \<bullet> P')"
    by(subst boundOutputChainAlpha) auto
  ultimately show ?thesis by(rule weakOutputTransitionI)
qed

lemma weakOutputFreshDerivative:
  fixes \<Psi>   :: 'b
  and   Q    :: "('a, 'b, 'c) psi"
  and   P    :: "('a, 'b, 'c) psi"
  and   M    :: 'a
  and   xvec :: "name list"
  and   N    :: 'a
  and   P'   :: "('a, 'b, 'c) psi"
  and   x    :: name

  assumes PTrans: "\<Psi> : Q \<rhd> P \<Longrightarrow>M\<lparr>\<nu>*xvec\<rparr>\<langle>N\<rangle> \<prec> P'"
  and     "x \<sharp> P"
  and     "x \<sharp> xvec"

  shows "x \<sharp> N"
  and   "x \<sharp> P'"
proof -
  from PTrans obtain P'' where PChain: "\<Psi> \<rhd> P \<Longrightarrow>\<^sub>\<tau> P''" and P''Trans: "\<Psi> \<rhd> P'' \<longmapsto>M\<lparr>\<nu>*xvec\<rparr>\<langle>N\<rangle> \<prec> P'"
    by(rule weakOutputTransitionE)

  from PChain `x \<sharp> P` have "x \<sharp> P''" by(rule tauChainFresh)
  with P''Trans show "x \<sharp> N" and "x \<sharp> P'" using `x \<sharp> xvec` 
    by(force intro: outputFreshDerivative)+
qed

lemma weakOutputFreshChainDerivative:
  fixes \<Psi>   :: 'b
  and   Q    :: "('a, 'b, 'c) psi"
  and   P    :: "('a, 'b, 'c) psi"
  and   M    :: 'a
  and   xvec :: "name list"
  and   N    :: 'a
  and   P'   :: "('a, 'b, 'c) psi"
  and   yvec :: "name list"

  assumes PTrans: "\<Psi> : Q \<rhd> P \<Longrightarrow>M\<lparr>\<nu>*xvec\<rparr>\<langle>N\<rangle> \<prec> P'"
  and     "yvec \<sharp>* P"
  and     "yvec \<sharp>* xvec"

  shows "yvec \<sharp>* N"
  and   "yvec \<sharp>* P'"
using assms
by(induct yvec) (auto intro: weakOutputFreshDerivative)

lemma weakInputFreshDerivative:
  fixes \<Psi>   :: 'b
  and   Q    :: "('a, 'b, 'c) psi"
  and   P    :: "('a, 'b, 'c) psi"
  and   M    :: 'a
  and   N    :: 'a
  and   P'   :: "('a, 'b, 'c) psi"
  and   x    :: name

  assumes PTrans: "\<Psi> : Q \<rhd> P \<Longrightarrow>M\<lparr>N\<rparr> \<prec> P'"
  and     "x \<sharp> P"
  and     "x \<sharp> N"

  shows "x \<sharp> P'"
proof -
  from PTrans obtain P'' where PChain: "\<Psi> \<rhd> P \<Longrightarrow>\<^sub>\<tau> P''" and P''Trans: "\<Psi> \<rhd> P'' \<longmapsto>M\<lparr>N\<rparr> \<prec> P'"
    by(rule weakInputTransitionE)

  from PChain `x \<sharp> P` have "x \<sharp> P''" by(rule tauChainFresh)
  with P''Trans show "x \<sharp> P'" using `x \<sharp> N` 
    by(force intro: inputFreshDerivative)
qed

lemma weakInputFreshChainDerivative:
  fixes \<Psi>   :: 'b
  and   Q    :: "('a, 'b, 'c) psi"
  and   P    :: "('a, 'b, 'c) psi"
  and   M    :: 'a
  and   N    :: 'a
  and   P'   :: "('a, 'b, 'c) psi"
  and   xvec :: "name list"

  assumes PTrans: "\<Psi> : Q \<rhd> P \<Longrightarrow>M\<lparr>N\<rparr> \<prec> P'"
  and     "xvec \<sharp>* P"
  and     "xvec \<sharp>* N"

  shows "xvec \<sharp>* P'"
using assms
by(induct xvec) (auto intro: weakInputFreshDerivative)

lemma weakOutputPermSubject:
  fixes \<Psi>   :: 'b
  and   P    :: "('a, 'b, 'c) psi"
  and   M    :: 'a
  and   xvec :: "name list"
  and   N    :: 'a
  and   P'   :: "('a, 'b, 'c) psi"
  and   p    :: "name prm"
  and   yvec :: "name list"
  and   zvec :: "name list"

  assumes PTrans: "\<Psi> : Q \<rhd> P \<Longrightarrow>M\<lparr>\<nu>*xvec\<rparr>\<langle>N\<rangle> \<prec> P'"
  and     S: "set p \<subseteq> set yvec \<times> set zvec"
  and     "yvec \<sharp>* \<Psi>"
  and     "zvec \<sharp>* \<Psi>"
  and     "yvec \<sharp>* P"
  and     "zvec \<sharp>* P"

  shows "\<Psi> : Q \<rhd> P \<Longrightarrow>(p \<bullet> M)\<lparr>\<nu>*xvec\<rparr>\<langle>N\<rangle> \<prec> P'"
proof -
  from PTrans obtain P'' where PChain: "\<Psi> \<rhd> P \<Longrightarrow>\<^sub>\<tau> P''" and QeqP'': "insertAssertion (extractFrame Q) \<Psi> \<hookrightarrow>\<^sub>F insertAssertion (extractFrame P'') \<Psi>" 
                            and P''Trans: "\<Psi> \<rhd> P'' \<longmapsto>M\<lparr>\<nu>*xvec\<rparr>\<langle>N\<rangle> \<prec> P'"
    by(rule weakOutputTransitionE)

  from PChain `yvec \<sharp>* P` `zvec \<sharp>* P` have "yvec \<sharp>* P''" and "zvec \<sharp>* P''"
    by(force intro: tauChainFreshChain)+

  note PChain QeqP''
  moreover from P''Trans S `yvec \<sharp>* \<Psi>` `zvec \<sharp>* \<Psi>` `yvec \<sharp>* P''` `zvec \<sharp>* P''` have "\<Psi> \<rhd> P'' \<longmapsto>(p \<bullet> M)\<lparr>\<nu>*xvec\<rparr>\<langle>N\<rangle> \<prec> P'"
    by(rule_tac outputPermSubject) auto
  ultimately show ?thesis by(rule weakOutputTransitionI)
qed

lemma weakInputPermSubject:
  fixes \<Psi>   :: 'b
  and   Q    :: "('a, 'b, 'c) psi"
  and   P    :: "('a, 'b, 'c) psi"
  and   M    :: 'a
  and   N    :: 'a
  and   P'   :: "('a, 'b, 'c) psi"
  and   p    :: "name prm"
  and   yvec :: "name list"
  and   zvec :: "name list"

  assumes PTrans: "\<Psi> : Q \<rhd> P \<Longrightarrow>M\<lparr>N\<rparr> \<prec> P'"
  and     S: "set p \<subseteq> set yvec \<times> set zvec"
  and     "yvec \<sharp>* \<Psi>"
  and     "zvec \<sharp>* \<Psi>"
  and     "yvec \<sharp>* P"
  and     "zvec \<sharp>* P"

  shows "\<Psi> : Q \<rhd> P \<Longrightarrow>(p \<bullet> M)\<lparr>N\<rparr> \<prec> P'"
proof -
  from PTrans obtain P'' where PChain: "\<Psi> \<rhd> P \<Longrightarrow>\<^sub>\<tau> P''" and QeqP'': "insertAssertion (extractFrame Q) \<Psi> \<hookrightarrow>\<^sub>F insertAssertion (extractFrame P'') \<Psi>" 
                            and P''Trans: "\<Psi> \<rhd> P'' \<longmapsto>M\<lparr>N\<rparr> \<prec> P'"
    by(rule weakInputTransitionE)

  from PChain `yvec \<sharp>* P` `zvec \<sharp>* P` have "yvec \<sharp>* P''" and "zvec \<sharp>* P''"
    by(force intro: tauChainFreshChain)+

  note PChain QeqP''
  moreover from P''Trans S `yvec \<sharp>* \<Psi>` `zvec \<sharp>* \<Psi>` `yvec \<sharp>* P''` `zvec \<sharp>* P''` have "\<Psi> \<rhd> P'' \<longmapsto>(p \<bullet> M)\<lparr>N\<rparr> \<prec> P'"
    by(rule_tac inputPermSubject) auto
  ultimately show ?thesis by(rule weakInputTransitionI)
qed

lemma weakInput:
  fixes \<Psi>   :: 'b
  and   Q    :: "('a, 'b, 'c) psi"
  and   M    :: 'a
  and   K    :: 'a
  and   xvec :: "name list"
  and   N    :: 'a
  and   Tvec :: "'a list"
  and   P    :: "('a, 'b, 'c) psi"

  assumes "\<Psi> \<turnstile> M \<leftrightarrow> K"
  and     "distinct xvec" 
  and     "set xvec \<subseteq> supp N"
  and     "length xvec = length Tvec"
  and     Qeq\<Psi>: "insertAssertion (extractFrame Q) \<Psi> \<hookrightarrow>\<^sub>F \<langle>\<epsilon>, \<Psi> \<otimes> \<one>\<rangle>"

  shows "\<Psi> : Q \<rhd> M\<lparr>\<lambda>*xvec N\<rparr>.P \<Longrightarrow>K\<lparr>(N[xvec::=Tvec])\<rparr> \<prec> P[xvec::=Tvec]"
proof -
  have "\<Psi> \<rhd>  M\<lparr>\<lambda>*xvec N\<rparr>.P \<Longrightarrow>\<^sub>\<tau> M\<lparr>\<lambda>*xvec N\<rparr>.P" by(rule TauBase)
  moreover from Qeq\<Psi> have "insertAssertion (extractFrame Q) \<Psi> \<hookrightarrow>\<^sub>F insertAssertion (extractFrame(M\<lparr>\<lambda>*xvec N\<rparr>.P)) \<Psi>"
    by auto
  moreover from assms have "\<Psi> \<rhd> M\<lparr>\<lambda>*xvec N\<rparr>.P \<longmapsto>K\<lparr>(N[xvec::=Tvec])\<rparr> \<prec> P[xvec::=Tvec]"
    by(rule_tac Input)
  ultimately show ?thesis by(rule weakInputTransitionI)
qed

lemma weakOutput:
  fixes \<Psi>   :: 'b
  and   Q    :: "('a, 'b, 'c) psi"
  and   M    :: 'a
  and   K    :: 'a
  and   N    :: 'a
  and   P    :: "('a, 'b, 'c) psi"
  
  assumes "\<Psi> \<turnstile> M \<leftrightarrow> K"
  and     Qeq\<Psi>: "insertAssertion (extractFrame Q) \<Psi> \<hookrightarrow>\<^sub>F \<langle>\<epsilon>, \<Psi> \<otimes> \<one>\<rangle>"

  shows "\<Psi> : Q \<rhd> M\<langle>N\<rangle>.P \<Longrightarrow>K\<langle>N\<rangle> \<prec> P"
proof -
  have "\<Psi> \<rhd>  M\<langle>N\<rangle>.P \<Longrightarrow>\<^sub>\<tau> M\<langle>N\<rangle>.P" by(rule TauBase)
  moreover from Qeq\<Psi> have "insertAssertion (extractFrame Q) \<Psi> \<hookrightarrow>\<^sub>F insertAssertion (extractFrame(M\<langle>N\<rangle>.P)) \<Psi>"
    by auto
  moreover have "insertAssertion (extractFrame(M\<langle>N\<rangle>.P)) \<Psi> \<hookrightarrow>\<^sub>F insertAssertion (extractFrame(M\<langle>N\<rangle>.P)) \<Psi>" by simp
  moreover from `\<Psi> \<turnstile> M \<leftrightarrow> K` have "\<Psi> \<rhd> M\<langle>N\<rangle>.P \<longmapsto>K\<langle>N\<rangle> \<prec> P"
    by(rule Output)
  ultimately show ?thesis by(rule_tac weakOutputTransitionI) auto
qed

lemma insertGuardedAssertion:
  fixes P :: "('a, 'b, 'c) psi"

  assumes "guarded P"

  shows "insertAssertion(extractFrame P) \<Psi> \<simeq>\<^sub>F \<langle>\<epsilon>, \<Psi> \<otimes> \<one>\<rangle>"
proof -
  obtain A\<^sub>P \<Psi>\<^sub>P where FrP: "extractFrame P = \<langle>A\<^sub>P, \<Psi>\<^sub>P\<rangle>" and "A\<^sub>P \<sharp>* \<Psi>" by(rule freshFrame)
  from `guarded P` FrP have "\<Psi>\<^sub>P \<simeq> \<one>" and "supp \<Psi>\<^sub>P = ({}::name set)"
    by(blast dest: guardedStatEq)+
  
  from FrP `A\<^sub>P \<sharp>* \<Psi>` `\<Psi>\<^sub>P \<simeq> \<one>` have "insertAssertion(extractFrame P) \<Psi> \<simeq>\<^sub>F \<langle>A\<^sub>P, \<Psi> \<otimes> \<one>\<rangle>"
    by simp (metis frameIntCompositionSym)
  moreover from `A\<^sub>P \<sharp>* \<Psi>` have "\<langle>A\<^sub>P, \<Psi> \<otimes> \<one>\<rangle> \<simeq>\<^sub>F \<langle>\<epsilon>, \<Psi> \<otimes> \<one>\<rangle>"
    by(rule_tac frameResFreshChain) auto
  ultimately show ?thesis by(rule FrameStatEqTrans)
qed
  
lemma weakOutputCase:
  fixes \<Psi>   :: 'b 
  and   Q    :: "('a, 'b, 'c) psi"
  and   P    :: "('a, 'b, 'c) psi"
  and   M    :: 'a
  and   xvec :: "name list"
  and   N    :: 'a
  and   P'   :: "('a, 'b, 'c) psi"
  and   R    :: "('a, 'b, 'c) psi"

  assumes PTrans: "\<Psi> : Q \<rhd> P \<Longrightarrow>M\<lparr>\<nu>*xvec\<rparr>\<langle>N\<rangle> \<prec> P'"
  and     "(\<phi>, P) mem CsP"
  and     "\<Psi> \<turnstile> \<phi>"
  and     "guarded P"
  and     "guarded Q"
  and     "guarded R"

  shows "\<Psi> : R \<rhd> Cases CsP \<Longrightarrow>M\<lparr>\<nu>*xvec\<rparr>\<langle>N\<rangle> \<prec> P'"
proof -
  from PTrans obtain P'' where PChain: "\<Psi> \<rhd> P \<Longrightarrow>\<^sub>\<tau> P''"
                           and QeqP'': "insertAssertion (extractFrame Q) \<Psi> \<hookrightarrow>\<^sub>F insertAssertion (extractFrame P'') \<Psi>"
                           and P''Trans: "\<Psi> \<rhd> P'' \<longmapsto>M\<lparr>\<nu>*xvec\<rparr>\<langle>N\<rangle> \<prec> P'"
    by(rule weakOutputTransitionE)
  show ?thesis
  proof(case_tac "P = P''")
    assume "P = P''"
    have "\<Psi> \<rhd> Cases CsP \<Longrightarrow>\<^sub>\<tau> Cases CsP" by(rule TauBase)
    moreover from `guarded R` have "insertAssertion(extractFrame R) \<Psi> \<hookrightarrow>\<^sub>F insertAssertion(extractFrame(Cases CsP)) \<Psi>"
      by(auto dest: insertGuardedAssertion[simplified FrameStatEq_def])
    moreover from P''Trans `(\<phi>, P) mem CsP` `\<Psi> \<turnstile> \<phi>` `guarded P` `P = P''` have "\<Psi> \<rhd> Cases CsP \<longmapsto>M\<lparr>\<nu>*xvec\<rparr>\<langle>N\<rangle> \<prec> P'"
      by(blast intro: Case)
    ultimately show ?thesis
      by(rule weakOutputTransitionI)
  next
    assume "P \<noteq> P''"
    with PChain `(\<phi>, P) mem CsP` `\<Psi> \<turnstile> \<phi>` `guarded P` have "\<Psi> \<rhd> Cases CsP \<Longrightarrow>\<^sub>\<tau> P''" by(rule_tac tauChainCases)
    moreover have "insertAssertion(extractFrame R) \<Psi> \<hookrightarrow>\<^sub>F insertAssertion(extractFrame P'') \<Psi>"
    proof -
       from `guarded R` have "insertAssertion(extractFrame R) \<Psi> \<simeq>\<^sub>F \<langle>\<epsilon>, \<Psi> \<otimes> \<one>\<rangle>" by(rule insertGuardedAssertion)
       moreover from `guarded Q` have "\<langle>\<epsilon>, \<Psi> \<otimes> \<one>\<rangle> \<simeq>\<^sub>F insertAssertion(extractFrame Q) \<Psi>"
         by(metis insertGuardedAssertion FrameStatEqSym)
       ultimately show ?thesis using QeqP'' by(metis FrameStatEq_def FrameStatImpTrans)
     qed
    ultimately show ?thesis using P''Trans by(rule weakOutputTransitionI)
  qed
qed

lemma weakInputCase:
  fixes \<Psi>   :: 'b 
  and   Q   :: "('a, 'b, 'c) psi"
  and   P   :: "('a, 'b, 'c) psi"
  and   M   :: 'a
  and   N   :: 'a
  and   P'  :: "('a, 'b, 'c) psi"
  and   R   :: "('a, 'b, 'c) psi"

  assumes PTrans: "\<Psi> : Q \<rhd> P \<Longrightarrow>M\<lparr>N\<rparr> \<prec> P'"
  and     "(\<phi>, P) mem CsP"
  and     "\<Psi> \<turnstile> \<phi>"
  and     "guarded P"
  and     "guarded Q"
  and     "guarded R"

  shows "\<Psi> : R \<rhd> Cases CsP \<Longrightarrow>M\<lparr>N\<rparr> \<prec> P'"
proof -
  from PTrans obtain P'' where PChain: "\<Psi> \<rhd> P \<Longrightarrow>\<^sub>\<tau> P''"
                           and QeqP'': "insertAssertion (extractFrame Q) \<Psi> \<hookrightarrow>\<^sub>F insertAssertion (extractFrame P'') \<Psi>"
                           and P''Trans: "\<Psi> \<rhd> P'' \<longmapsto>M\<lparr>N\<rparr> \<prec> P'"
    by(rule weakInputTransitionE)
  show ?thesis
  proof(case_tac "P = P''")
    assume "P = P''"
    have "\<Psi> \<rhd> Cases CsP \<Longrightarrow>\<^sub>\<tau> Cases CsP" by(rule TauBase)
    moreover from `guarded R` have "insertAssertion(extractFrame R) \<Psi> \<hookrightarrow>\<^sub>F insertAssertion(extractFrame(Cases CsP)) \<Psi>"
      by(auto dest: insertGuardedAssertion[simplified FrameStatEq_def])
    moreover from P''Trans `(\<phi>, P) mem CsP` `\<Psi> \<turnstile> \<phi>` `guarded P` `P = P''` have "\<Psi> \<rhd> Cases CsP \<longmapsto>M\<lparr>N\<rparr> \<prec> P'"
      by(blast intro: Case)
    ultimately show ?thesis
      by(rule weakInputTransitionI)
  next
    assume "P \<noteq> P''"
    with PChain `(\<phi>, P) mem CsP` `\<Psi> \<turnstile> \<phi>` `guarded P` have "\<Psi> \<rhd> Cases CsP \<Longrightarrow>\<^sub>\<tau> P''" by(rule_tac tauChainCases)
    moreover have "insertAssertion(extractFrame R) \<Psi> \<hookrightarrow>\<^sub>F insertAssertion(extractFrame P'') \<Psi>"
    proof -
       from `guarded R` have "insertAssertion(extractFrame R) \<Psi> \<simeq>\<^sub>F \<langle>\<epsilon>, \<Psi> \<otimes> \<one>\<rangle>" by(rule insertGuardedAssertion)
       moreover from `guarded Q` have "\<langle>\<epsilon>, \<Psi> \<otimes> \<one>\<rangle> \<simeq>\<^sub>F insertAssertion(extractFrame Q) \<Psi>"
         by(metis insertGuardedAssertion FrameStatEqSym)
       ultimately show ?thesis using QeqP'' by(metis FrameStatEq_def FrameStatImpTrans)
     qed
    ultimately show ?thesis using P''Trans by(rule weakInputTransitionI)
  qed
qed

lemma weakOpen:
  fixes \<Psi>   :: 'b
  and   Q    :: "('a, 'b, 'c) psi"
  and   P    :: "('a, 'b, 'c) psi"
  and   M    :: 'a
  and   xvec :: "name list"
  and   yvec :: "name list"
  and   N    :: 'a
  and   P'   :: "('a, 'b, 'c) psi"

  assumes PTrans: "\<Psi> : Q \<rhd> P \<Longrightarrow>M\<lparr>\<nu>*(xvec@yvec)\<rparr>\<langle>N\<rangle> \<prec> P'"
  and     "x \<in> supp N"
  and     "x \<sharp> \<Psi>"
  and     "x \<sharp> M"
  and     "x \<sharp> xvec"
  and     "x \<sharp> yvec"

  shows "\<Psi> : \<lparr>\<nu>x\<rparr>Q \<rhd> \<lparr>\<nu>x\<rparr>P \<Longrightarrow>M\<lparr>\<nu>*(xvec@x#yvec)\<rparr>\<langle>N\<rangle> \<prec> P'"
proof -
  from PTrans obtain P'' where PChain: "\<Psi> \<rhd> P \<Longrightarrow>\<^sub>\<tau> P''" and QeqP'': "insertAssertion (extractFrame Q) \<Psi> \<hookrightarrow>\<^sub>F insertAssertion (extractFrame P'') \<Psi>"
                           and P''Trans: "\<Psi> \<rhd> P'' \<longmapsto>M\<lparr>\<nu>*(xvec@yvec)\<rparr>\<langle>N\<rangle> \<prec> P'"
    by(rule weakOutputTransitionE)

  from PChain `x \<sharp> \<Psi>` have "\<Psi> \<rhd> \<lparr>\<nu>x\<rparr>P \<Longrightarrow>\<^sub>\<tau> \<lparr>\<nu>x\<rparr>P''" by(rule tauChainResPres)
  moreover from QeqP'' `x \<sharp> \<Psi>` have "insertAssertion (extractFrame(\<lparr>\<nu>x\<rparr>Q)) \<Psi> \<hookrightarrow>\<^sub>F insertAssertion (extractFrame(\<lparr>\<nu>x\<rparr>P'')) \<Psi>" by(force intro: frameImpResPres)
  moreover from P''Trans `x \<in> supp N` `x \<sharp> \<Psi>` `x \<sharp> M` `x \<sharp> xvec` `x \<sharp> yvec` have "\<Psi> \<rhd> \<lparr>\<nu>x\<rparr>P'' \<longmapsto>M\<lparr>\<nu>*(xvec@x#yvec)\<rparr>\<langle>N\<rangle> \<prec> P'"
    by(rule Open)
  ultimately show ?thesis by(rule weakOutputTransitionI)
qed

lemma weakScopeB:
  fixes \<Psi>   :: 'b
  and   Q    :: "('a, 'b, 'c) psi"
  and   P    :: "('a, 'b, 'c) psi"
  and   M    :: 'a
  and   xvec :: "name list"
  and   N    :: 'a
  and   P'   :: "('a, 'b, 'c) psi"

  assumes PTrans: "\<Psi> : Q \<rhd> P \<Longrightarrow>M\<lparr>\<nu>*xvec\<rparr>\<langle>N\<rangle> \<prec> P'"
  and     "x \<sharp> \<Psi>"
  and     "x \<sharp> \<Psi>'"
  and     "x \<sharp> M"
  and     "x \<sharp> xvec"
  and     "x \<sharp> N"

  shows "\<Psi> : \<lparr>\<nu>x\<rparr>Q \<rhd> \<lparr>\<nu>x\<rparr>P \<Longrightarrow>M\<lparr>\<nu>*xvec\<rparr>\<langle>N\<rangle> \<prec> \<lparr>\<nu>x\<rparr>P'"
proof -
  from PTrans obtain P'' where PChain: "\<Psi> \<rhd> P \<Longrightarrow>\<^sub>\<tau> P''" and QeqP'': "insertAssertion (extractFrame Q) \<Psi> \<hookrightarrow>\<^sub>F insertAssertion (extractFrame P'') \<Psi>"
                           and P''Trans: "\<Psi> \<rhd> P'' \<longmapsto>M\<lparr>\<nu>*xvec\<rparr>\<langle>N\<rangle> \<prec> P'"
    by(rule weakOutputTransitionE)

  from PChain `x \<sharp> \<Psi>` have "\<Psi> \<rhd> \<lparr>\<nu>x\<rparr>P \<Longrightarrow>\<^sub>\<tau> \<lparr>\<nu>x\<rparr>P''" by(rule tauChainResPres)
  moreover from QeqP'' `x \<sharp> \<Psi>` have "insertAssertion (extractFrame(\<lparr>\<nu>x\<rparr>Q)) \<Psi> \<hookrightarrow>\<^sub>F insertAssertion (extractFrame(\<lparr>\<nu>x\<rparr>P'')) \<Psi>" by(force intro: frameImpResPres)
  moreover from P''Trans `x \<sharp> \<Psi>` `x \<sharp> M` `x \<sharp> xvec` `x \<sharp> N` have "\<Psi> \<rhd> \<lparr>\<nu>x\<rparr>P'' \<longmapsto>M\<lparr>\<nu>*xvec\<rparr>\<langle>N\<rangle> \<prec> \<lparr>\<nu>x\<rparr>P'"
    by(rule ScopeB)
  ultimately show ?thesis by(rule weakOutputTransitionI)
qed

lemma weakScopeF:
  fixes \<Psi>  :: 'b
  and   Q    :: "('a, 'b, 'c) psi"
  and   P   :: "('a, 'b, 'c) psi"
  and   M   :: 'a
  and   N   :: 'a
  and   P'  :: "('a, 'b, 'c) psi"

  assumes PTrans: "\<Psi> : Q \<rhd> P \<Longrightarrow>M\<lparr>N\<rparr> \<prec> P'"
  and     "x \<sharp> \<Psi>"
  and     "x \<sharp> M"
  and     "x \<sharp> N"
  and     "x \<sharp> \<Psi>'"

  shows "\<Psi> : \<lparr>\<nu>x\<rparr>Q \<rhd> \<lparr>\<nu>x\<rparr>P \<Longrightarrow>M\<lparr>N\<rparr> \<prec> \<lparr>\<nu>x\<rparr>P'"
proof -
  from PTrans obtain P'' where PChain: "\<Psi> \<rhd> P \<Longrightarrow>\<^sub>\<tau> P''" and P''Trans: "\<Psi> \<rhd> P'' \<longmapsto>M\<lparr>N\<rparr> \<prec> P'"
                           and QeqP'': "insertAssertion (extractFrame Q) \<Psi> \<hookrightarrow>\<^sub>F insertAssertion (extractFrame P'') \<Psi>"
    by(rule weakInputTransitionE)
  from PChain `x \<sharp> \<Psi>` have "\<Psi> \<rhd> \<lparr>\<nu>x\<rparr>P \<Longrightarrow>\<^sub>\<tau> \<lparr>\<nu>x\<rparr>P''" by(rule tauChainResPres)
  moreover from QeqP'' `x \<sharp> \<Psi>`
  have "insertAssertion (extractFrame(\<lparr>\<nu>x\<rparr>Q)) \<Psi> \<hookrightarrow>\<^sub>F insertAssertion (extractFrame(\<lparr>\<nu>x\<rparr>P'')) \<Psi>"
    by(force intro: frameImpResPres)
  moreover from P''Trans  `x \<sharp> \<Psi>` `x \<sharp> M` `x \<sharp> N` have "\<Psi> \<rhd> \<lparr>\<nu>x\<rparr>P'' \<longmapsto>M\<lparr>N\<rparr> \<prec> \<lparr>\<nu>x\<rparr>P'"
    by(rule_tac ScopeF) auto
  ultimately show ?thesis by(rule weakInputTransitionI)
qed

lemma weakPar1B:
  fixes \<Psi>   :: 'b
  and   R    :: "('a, 'b, 'c) psi"
  and   P    :: "('a, 'b, 'c) psi"
  and   M    :: 'a
  and   xvec :: "name list"
  and   N    :: 'a
  and   P'   :: "('a, 'b, 'c) psi"
  and   Q    :: "('a, 'b, 'c) psi"
  and   A\<^sub>Q   :: "name list"
  and   \<Psi>\<^sub>Q   :: 'b

  assumes PTrans: "\<Psi> \<otimes> \<Psi>\<^sub>Q : R \<rhd> P \<Longrightarrow>M\<lparr>\<nu>*xvec\<rparr>\<langle>N\<rangle> \<prec> P'"
  and     FrQ: "extractFrame Q = \<langle>A\<^sub>Q, \<Psi>\<^sub>Q\<rangle>"
  and     "xvec \<sharp>* Q"
  and     "A\<^sub>Q \<sharp>* \<Psi>"
  and     "A\<^sub>Q \<sharp>* P"
  and     "A\<^sub>Q \<sharp>* M"
  and     "A\<^sub>Q \<sharp>* xvec"
  and     "A\<^sub>Q \<sharp>* R"

  shows "\<Psi> : R \<parallel> Q \<rhd> P \<parallel> Q \<Longrightarrow>M\<lparr>\<nu>*xvec\<rparr>\<langle>N\<rangle> \<prec> P' \<parallel> Q"
proof -
  from PTrans obtain P'' where PChain: "\<Psi> \<otimes> \<Psi>\<^sub>Q \<rhd> P \<Longrightarrow>\<^sub>\<tau> P''"
                           and ReqP'': "insertAssertion (extractFrame R) (\<Psi> \<otimes> \<Psi>\<^sub>Q) \<hookrightarrow>\<^sub>F insertAssertion (extractFrame P'') (\<Psi> \<otimes> \<Psi>\<^sub>Q)"
                           and P''Trans: "\<Psi> \<otimes> \<Psi>\<^sub>Q \<rhd> P'' \<longmapsto>M\<lparr>\<nu>*xvec\<rparr>\<langle>N\<rangle> \<prec> P'"
    by(rule weakOutputTransitionE)

  from PChain `A\<^sub>Q \<sharp>* P` have "A\<^sub>Q \<sharp>* P''" by(rule tauChainFreshChain)
  with P''Trans have "A\<^sub>Q \<sharp>* P'" using `A\<^sub>Q \<sharp>* xvec` by(rule outputFreshChainDerivative)

  from PChain FrQ `A\<^sub>Q \<sharp>* \<Psi>` `A\<^sub>Q \<sharp>* P` have "\<Psi> \<rhd> P \<parallel> Q \<Longrightarrow>\<^sub>\<tau> P'' \<parallel> Q" by(rule tauChainPar1)
  moreover have "insertAssertion (extractFrame(R \<parallel> Q)) \<Psi> \<hookrightarrow>\<^sub>F insertAssertion (extractFrame(P'' \<parallel> Q)) \<Psi>"
  proof -
    obtain A\<^sub>R \<Psi>\<^sub>R where FrR: "extractFrame R = \<langle>A\<^sub>R, \<Psi>\<^sub>R\<rangle>" and "A\<^sub>R \<sharp>* A\<^sub>Q" and "A\<^sub>R \<sharp>* \<Psi>\<^sub>Q" and "A\<^sub>R \<sharp>* \<Psi>"
      by(rule_tac C="(A\<^sub>Q, \<Psi>\<^sub>Q, \<Psi>)" in freshFrame) auto
    obtain A\<^sub>P'' \<Psi>\<^sub>P'' where FrP'': "extractFrame P'' = \<langle>A\<^sub>P'', \<Psi>\<^sub>P''\<rangle>" and "A\<^sub>P'' \<sharp>* A\<^sub>Q" and "A\<^sub>P'' \<sharp>* \<Psi>\<^sub>Q" and "A\<^sub>P'' \<sharp>* \<Psi>"
      by(rule_tac C="(A\<^sub>Q, \<Psi>\<^sub>Q, \<Psi>)" in freshFrame) auto

    from FrR FrP'' `A\<^sub>Q \<sharp>* R` `A\<^sub>Q \<sharp>* P''` `A\<^sub>R \<sharp>* A\<^sub>Q` `A\<^sub>P'' \<sharp>* A\<^sub>Q` have "A\<^sub>Q \<sharp>* \<Psi>\<^sub>R" and "A\<^sub>Q \<sharp>* \<Psi>\<^sub>P''"
      by(force dest: extractFrameFreshChain)+
    have "\<langle>A\<^sub>R, \<Psi> \<otimes> \<Psi>\<^sub>R \<otimes> \<Psi>\<^sub>Q\<rangle> \<simeq>\<^sub>F \<langle>A\<^sub>R, (\<Psi> \<otimes> \<Psi>\<^sub>Q) \<otimes> \<Psi>\<^sub>R\<rangle>"
      by(metis frameNilStatEq frameResChainPres Associativity Commutativity Composition AssertionStatEqTrans)
    moreover from ReqP'' FrR FrP'' `A\<^sub>R \<sharp>* \<Psi>` `A\<^sub>R \<sharp>* \<Psi>\<^sub>Q` `A\<^sub>P'' \<sharp>* \<Psi>` `A\<^sub>P'' \<sharp>* \<Psi>\<^sub>Q`
    have "\<langle>A\<^sub>R, (\<Psi> \<otimes> \<Psi>\<^sub>Q) \<otimes> \<Psi>\<^sub>R\<rangle> \<hookrightarrow>\<^sub>F \<langle>A\<^sub>P'', (\<Psi> \<otimes> \<Psi>\<^sub>Q) \<otimes> \<Psi>\<^sub>P''\<rangle>" using freshCompChain by auto
    moreover have "\<langle>A\<^sub>P'', (\<Psi> \<otimes> \<Psi>\<^sub>Q) \<otimes> \<Psi>\<^sub>P''\<rangle> \<simeq>\<^sub>F \<langle>A\<^sub>P'', \<Psi> \<otimes> \<Psi>\<^sub>P'' \<otimes> \<Psi>\<^sub>Q\<rangle>"
      by(metis frameNilStatEq frameResChainPres Associativity Commutativity Composition AssertionStatEqTrans)
    ultimately have "\<langle>A\<^sub>R, \<Psi> \<otimes> \<Psi>\<^sub>R \<otimes> \<Psi>\<^sub>Q\<rangle> \<hookrightarrow>\<^sub>F \<langle>A\<^sub>P'', \<Psi> \<otimes> \<Psi>\<^sub>P'' \<otimes> \<Psi>\<^sub>Q\<rangle>"
      by(force dest: FrameStatImpTrans simp add: FrameStatEq_def)

    hence "\<langle>(A\<^sub>R@A\<^sub>Q), \<Psi> \<otimes> \<Psi>\<^sub>R \<otimes> \<Psi>\<^sub>Q\<rangle> \<hookrightarrow>\<^sub>F \<langle>(A\<^sub>P''@A\<^sub>Q), \<Psi> \<otimes> \<Psi>\<^sub>P'' \<otimes> \<Psi>\<^sub>Q\<rangle>"
      apply(simp add: frameChainAppend)
      apply(drule_tac xvec=A\<^sub>Q in frameImpResChainPres)
      by(metis frameImpChainComm FrameStatImpTrans)
    with FrR FrQ FrP'' `A\<^sub>R \<sharp>* A\<^sub>Q` `A\<^sub>R \<sharp>* \<Psi>\<^sub>Q` `A\<^sub>Q \<sharp>* \<Psi>\<^sub>R` `A\<^sub>P'' \<sharp>* A\<^sub>Q` `A\<^sub>P'' \<sharp>* \<Psi>\<^sub>Q` `A\<^sub>Q \<sharp>* \<Psi>\<^sub>P''` `A\<^sub>R \<sharp>* \<Psi>` `A\<^sub>P'' \<sharp>* \<Psi>` `A\<^sub>Q \<sharp>* \<Psi>` ReqP''
    show ?thesis by simp
  qed
  moreover from P''Trans FrQ `xvec \<sharp>* Q` `A\<^sub>Q \<sharp>* \<Psi>` `A\<^sub>Q \<sharp>* P''` `A\<^sub>Q \<sharp>* M` have "\<Psi> \<rhd> P'' \<parallel> Q \<longmapsto>M\<lparr>\<nu>*xvec\<rparr>\<langle>N\<rangle> \<prec> (P' \<parallel> Q)"
    by(rule Par1B)  
  ultimately show ?thesis by(rule weakOutputTransitionI)
qed
  
lemma weakPar1F:
  fixes \<Psi>  :: 'b
  and   R    :: "('a, 'b, 'c) psi"
  and   P   :: "('a, 'b, 'c) psi"
  and   M   :: 'a
  and   N   :: 'a
  and   P'  :: "('a, 'b, 'c) psi"
  and   Q   :: "('a, 'b, 'c) psi"
  and   A\<^sub>Q :: "name list"
  and   \<Psi>\<^sub>Q :: 'b

  assumes PTrans: "\<Psi> \<otimes> \<Psi>\<^sub>Q : R \<rhd> P \<Longrightarrow>M\<lparr>N\<rparr> \<prec> P'"
  and     FrQ: "extractFrame Q = \<langle>A\<^sub>Q, \<Psi>\<^sub>Q\<rangle>"
  and     "A\<^sub>Q \<sharp>* \<Psi>"
  and     "A\<^sub>Q \<sharp>* P"
  and     "A\<^sub>Q \<sharp>* M"
  and     "A\<^sub>Q \<sharp>* N"
  and     "A\<^sub>Q \<sharp>* R"

  shows "\<Psi> : R \<parallel> Q \<rhd> P \<parallel> Q \<Longrightarrow>M\<lparr>N\<rparr> \<prec> P' \<parallel> Q"
proof -
  from PTrans obtain P'' where PChain: "\<Psi> \<otimes> \<Psi>\<^sub>Q \<rhd> P \<Longrightarrow>\<^sub>\<tau> P''"
                           and ReqP'': "insertAssertion (extractFrame R) (\<Psi> \<otimes> \<Psi>\<^sub>Q) \<hookrightarrow>\<^sub>F insertAssertion (extractFrame P'') (\<Psi> \<otimes> \<Psi>\<^sub>Q)"
                           and P''Trans: "\<Psi> \<otimes> \<Psi>\<^sub>Q \<rhd> P'' \<longmapsto>M\<lparr>N\<rparr> \<prec> P'"
    by(rule weakInputTransitionE)

  from PChain `A\<^sub>Q \<sharp>* P` have "A\<^sub>Q \<sharp>* P''" by(rule tauChainFreshChain)
  with P''Trans have "A\<^sub>Q \<sharp>* P'" using `A\<^sub>Q \<sharp>* N` by(rule inputFreshChainDerivative)

  from PChain FrQ `A\<^sub>Q \<sharp>* \<Psi>` `A\<^sub>Q \<sharp>* P` have "\<Psi> \<rhd> P \<parallel> Q \<Longrightarrow>\<^sub>\<tau> P'' \<parallel> Q" by(rule tauChainPar1)
  moreover have "insertAssertion (extractFrame(R \<parallel> Q)) \<Psi> \<hookrightarrow>\<^sub>F insertAssertion (extractFrame(P'' \<parallel> Q)) \<Psi>"
  proof -
    obtain A\<^sub>R \<Psi>\<^sub>R where FrR: "extractFrame R = \<langle>A\<^sub>R, \<Psi>\<^sub>R\<rangle>" and "A\<^sub>R \<sharp>* A\<^sub>Q" and "A\<^sub>R \<sharp>* \<Psi>\<^sub>Q" and "A\<^sub>R \<sharp>* \<Psi>"
      by(rule_tac C="(A\<^sub>Q, \<Psi>\<^sub>Q, \<Psi>)" in freshFrame) auto
    obtain A\<^sub>P'' \<Psi>\<^sub>P'' where FrP'': "extractFrame P'' = \<langle>A\<^sub>P'', \<Psi>\<^sub>P''\<rangle>" and "A\<^sub>P'' \<sharp>* A\<^sub>Q" and "A\<^sub>P'' \<sharp>* \<Psi>\<^sub>Q" and "A\<^sub>P'' \<sharp>* \<Psi>"
      by(rule_tac C="(A\<^sub>Q, \<Psi>\<^sub>Q, \<Psi>)" in freshFrame) auto

    from FrR FrP'' `A\<^sub>Q \<sharp>* R` `A\<^sub>Q \<sharp>* P''` `A\<^sub>R \<sharp>* A\<^sub>Q` `A\<^sub>P'' \<sharp>* A\<^sub>Q` have "A\<^sub>Q \<sharp>* \<Psi>\<^sub>R" and "A\<^sub>Q \<sharp>* \<Psi>\<^sub>P''"
      by(force dest: extractFrameFreshChain)+
    have "\<langle>A\<^sub>R, \<Psi> \<otimes> \<Psi>\<^sub>R \<otimes> \<Psi>\<^sub>Q\<rangle> \<simeq>\<^sub>F \<langle>A\<^sub>R, (\<Psi> \<otimes> \<Psi>\<^sub>Q) \<otimes> \<Psi>\<^sub>R\<rangle>"
      by(metis frameNilStatEq frameResChainPres Associativity Commutativity Composition AssertionStatEqTrans)

    moreover from ReqP'' FrR FrP'' `A\<^sub>R \<sharp>* \<Psi>` `A\<^sub>R \<sharp>* \<Psi>\<^sub>Q` `A\<^sub>P'' \<sharp>* \<Psi>` `A\<^sub>P'' \<sharp>* \<Psi>\<^sub>Q`
    have "\<langle>A\<^sub>R, (\<Psi> \<otimes> \<Psi>\<^sub>Q) \<otimes> \<Psi>\<^sub>R\<rangle> \<hookrightarrow>\<^sub>F \<langle>A\<^sub>P'', (\<Psi> \<otimes> \<Psi>\<^sub>Q) \<otimes> \<Psi>\<^sub>P''\<rangle>" using freshCompChain by simp
    moreover have "\<langle>A\<^sub>P'', (\<Psi> \<otimes> \<Psi>\<^sub>Q) \<otimes> \<Psi>\<^sub>P''\<rangle> \<simeq>\<^sub>F \<langle>A\<^sub>P'', \<Psi> \<otimes> \<Psi>\<^sub>P'' \<otimes> \<Psi>\<^sub>Q\<rangle>"
      by(metis frameNilStatEq frameResChainPres Associativity Commutativity Composition AssertionStatEqTrans)
    ultimately have "\<langle>A\<^sub>R, \<Psi> \<otimes> \<Psi>\<^sub>R \<otimes> \<Psi>\<^sub>Q\<rangle> \<hookrightarrow>\<^sub>F \<langle>A\<^sub>P'', \<Psi> \<otimes> \<Psi>\<^sub>P'' \<otimes> \<Psi>\<^sub>Q\<rangle>"
      by(force dest: FrameStatImpTrans simp add: FrameStatEq_def)
    hence "\<langle>(A\<^sub>R@A\<^sub>Q), \<Psi> \<otimes> \<Psi>\<^sub>R \<otimes> \<Psi>\<^sub>Q\<rangle> \<hookrightarrow>\<^sub>F \<langle>(A\<^sub>P''@A\<^sub>Q), \<Psi> \<otimes> \<Psi>\<^sub>P'' \<otimes> \<Psi>\<^sub>Q\<rangle>"
      apply(simp add: frameChainAppend)
      apply(drule_tac xvec=A\<^sub>Q in frameImpResChainPres)
      by(metis frameImpChainComm FrameStatImpTrans)
    with FrR FrQ FrP'' `A\<^sub>R \<sharp>* A\<^sub>Q` `A\<^sub>R \<sharp>* \<Psi>\<^sub>Q` `A\<^sub>Q \<sharp>* \<Psi>\<^sub>R` `A\<^sub>P'' \<sharp>* A\<^sub>Q` `A\<^sub>P'' \<sharp>* \<Psi>\<^sub>Q` `A\<^sub>Q \<sharp>* \<Psi>\<^sub>P''` `A\<^sub>R \<sharp>* \<Psi>` `A\<^sub>P'' \<sharp>* \<Psi>` `A\<^sub>Q \<sharp>* \<Psi>` ReqP''
    show ?thesis by simp
  qed
  moreover from P''Trans FrQ `A\<^sub>Q \<sharp>* \<Psi>` `A\<^sub>Q \<sharp>* P''` `A\<^sub>Q \<sharp>* M` `A\<^sub>Q \<sharp>* N` have "\<Psi> \<rhd> P'' \<parallel> Q \<longmapsto>M\<lparr>N\<rparr> \<prec> (P' \<parallel> Q)"
    by(rule_tac Par1F) auto
  ultimately show ?thesis by(rule weakInputTransitionI)
qed

lemma weakPar2F:
  fixes \<Psi>  :: 'b
  and   R    :: "('a, 'b, 'c) psi"
  and   Q   :: "('a, 'b, 'c) psi"
  and   M   :: 'a
  and   N   :: 'a
  and   Q'  :: "('a, 'b, 'c) psi"
  and   P   :: "('a, 'b, 'c) psi"
  and   A\<^sub>P :: "name list"
  and   \<Psi>\<^sub>P :: 'b

  assumes QTrans: "\<Psi> \<otimes> \<Psi>\<^sub>P : R \<rhd> Q \<Longrightarrow>M\<lparr>N\<rparr> \<prec> Q'"
  and     FrP: "extractFrame P = \<langle>A\<^sub>P, \<Psi>\<^sub>P\<rangle>"
  and     "A\<^sub>P \<sharp>* \<Psi>"
  and     "A\<^sub>P \<sharp>* Q"
  and     "A\<^sub>P \<sharp>* M"
  and     "A\<^sub>P \<sharp>* N"
  and     "A\<^sub>P \<sharp>* R"

  shows "\<Psi> : P \<parallel> R \<rhd> P \<parallel> Q \<Longrightarrow>M\<lparr>N\<rparr> \<prec> P \<parallel> Q'"
proof -
  from QTrans obtain Q'' where QChain: "\<Psi> \<otimes> \<Psi>\<^sub>P \<rhd> Q \<Longrightarrow>\<^sub>\<tau> Q''"
                           and ReqQ'': "insertAssertion (extractFrame R) (\<Psi> \<otimes> \<Psi>\<^sub>P) \<hookrightarrow>\<^sub>F insertAssertion (extractFrame Q'') (\<Psi> \<otimes> \<Psi>\<^sub>P)"
                           and Q''Trans: "\<Psi> \<otimes> \<Psi>\<^sub>P \<rhd> Q'' \<longmapsto>M\<lparr>N\<rparr> \<prec> Q'"
    by(rule weakInputTransitionE)

  from QChain `A\<^sub>P \<sharp>* Q` have "A\<^sub>P \<sharp>* Q''" by(rule tauChainFreshChain)
  with Q''Trans have "A\<^sub>P \<sharp>* Q'" using `A\<^sub>P \<sharp>* N` by(rule inputFreshChainDerivative)

  from QChain FrP `A\<^sub>P \<sharp>* \<Psi>` `A\<^sub>P \<sharp>* Q` have "\<Psi> \<rhd> P \<parallel> Q \<Longrightarrow>\<^sub>\<tau> P \<parallel> Q''" by(rule tauChainPar2)
  moreover have "insertAssertion (extractFrame(P \<parallel> R)) \<Psi> \<hookrightarrow>\<^sub>F insertAssertion (extractFrame(P \<parallel> Q'')) \<Psi>"
  proof -
    obtain A\<^sub>R \<Psi>\<^sub>R where FrR: "extractFrame R = \<langle>A\<^sub>R, \<Psi>\<^sub>R\<rangle>" and "A\<^sub>R \<sharp>* A\<^sub>P" and "A\<^sub>R \<sharp>* \<Psi>\<^sub>P" and "A\<^sub>R \<sharp>* \<Psi>"
      by(rule_tac C="(A\<^sub>P, \<Psi>\<^sub>P, \<Psi>)" in freshFrame) auto
    obtain A\<^sub>Q'' \<Psi>\<^sub>Q'' where FrQ'': "extractFrame Q'' = \<langle>A\<^sub>Q'', \<Psi>\<^sub>Q''\<rangle>" and "A\<^sub>Q'' \<sharp>* A\<^sub>P" and "A\<^sub>Q'' \<sharp>* \<Psi>\<^sub>P" and "A\<^sub>Q'' \<sharp>* \<Psi>"
      by(rule_tac C="(A\<^sub>P, \<Psi>\<^sub>P, \<Psi>)" in freshFrame) auto

    from FrR FrQ'' `A\<^sub>P \<sharp>* R` `A\<^sub>P \<sharp>* Q''` `A\<^sub>R \<sharp>* A\<^sub>P` `A\<^sub>Q'' \<sharp>* A\<^sub>P` have "A\<^sub>P \<sharp>* \<Psi>\<^sub>R" and "A\<^sub>P \<sharp>* \<Psi>\<^sub>Q''"
      by(force dest: extractFrameFreshChain)+
    have "\<langle>A\<^sub>R, \<Psi> \<otimes> \<Psi>\<^sub>P \<otimes> \<Psi>\<^sub>R\<rangle> \<simeq>\<^sub>F \<langle>A\<^sub>R, (\<Psi> \<otimes> \<Psi>\<^sub>P) \<otimes> \<Psi>\<^sub>R\<rangle>"
      by(metis frameNilStatEq frameResChainPres Associativity Commutativity Composition AssertionStatEqTrans)

    moreover from ReqQ'' FrR FrQ'' `A\<^sub>R \<sharp>* \<Psi>` `A\<^sub>R \<sharp>* \<Psi>\<^sub>P` `A\<^sub>Q'' \<sharp>* \<Psi>` `A\<^sub>Q'' \<sharp>* \<Psi>\<^sub>P`
    have "\<langle>A\<^sub>R, (\<Psi> \<otimes> \<Psi>\<^sub>P) \<otimes> \<Psi>\<^sub>R\<rangle> \<hookrightarrow>\<^sub>F \<langle>A\<^sub>Q'', (\<Psi> \<otimes> \<Psi>\<^sub>P) \<otimes> \<Psi>\<^sub>Q''\<rangle>" using freshCompChain by simp
    moreover have "\<langle>A\<^sub>Q'', (\<Psi> \<otimes> \<Psi>\<^sub>P) \<otimes> \<Psi>\<^sub>Q''\<rangle> \<simeq>\<^sub>F \<langle>A\<^sub>Q'', \<Psi> \<otimes> \<Psi>\<^sub>P \<otimes> \<Psi>\<^sub>Q''\<rangle>"
      by(metis frameNilStatEq frameResChainPres Associativity Commutativity Composition AssertionStatEqTrans)
    ultimately have "\<langle>A\<^sub>R, \<Psi> \<otimes> \<Psi>\<^sub>P \<otimes> \<Psi>\<^sub>R\<rangle> \<hookrightarrow>\<^sub>F \<langle>A\<^sub>Q'', \<Psi> \<otimes> \<Psi>\<^sub>P \<otimes> \<Psi>\<^sub>Q''\<rangle>"
      by(force dest: FrameStatImpTrans simp add: FrameStatEq_def)
    hence "\<langle>(A\<^sub>P@A\<^sub>R), \<Psi> \<otimes> \<Psi>\<^sub>P \<otimes> \<Psi>\<^sub>R\<rangle> \<hookrightarrow>\<^sub>F \<langle>(A\<^sub>P@A\<^sub>Q''), \<Psi> \<otimes> \<Psi>\<^sub>P \<otimes> \<Psi>\<^sub>Q''\<rangle>"
      apply(simp add: frameChainAppend)
      apply(drule_tac xvec=A\<^sub>P in frameImpResChainPres)
      by(metis frameImpChainComm FrameStatImpTrans)
    with FrR FrP FrQ'' `A\<^sub>R \<sharp>* A\<^sub>P` `A\<^sub>R \<sharp>* \<Psi>\<^sub>P` `A\<^sub>P \<sharp>* \<Psi>\<^sub>R` `A\<^sub>Q'' \<sharp>* A\<^sub>P` `A\<^sub>Q'' \<sharp>* \<Psi>\<^sub>P` `A\<^sub>P \<sharp>* \<Psi>\<^sub>Q''` `A\<^sub>R \<sharp>* \<Psi>` `A\<^sub>Q'' \<sharp>* \<Psi>` `A\<^sub>P \<sharp>* \<Psi>` ReqQ''
    show ?thesis by simp
  qed
  moreover from Q''Trans FrP `A\<^sub>P \<sharp>* \<Psi>` `A\<^sub>P \<sharp>* Q''` `A\<^sub>P \<sharp>* M` `A\<^sub>P \<sharp>* N` have "\<Psi> \<rhd> P \<parallel> Q'' \<longmapsto>M\<lparr>N\<rparr> \<prec> (P \<parallel> Q')"
    by(rule_tac Par2F) auto
  ultimately show ?thesis by(rule weakInputTransitionI)
qed

lemma weakPar2B:
  fixes \<Psi>   :: 'b
  and   R    :: "('a, 'b, 'c) psi"
  and   Q    :: "('a, 'b, 'c) psi"
  and   M    :: 'a
  and   xvec :: "name list"
  and   N    :: 'a
  and   Q'   :: "('a, 'b, 'c) psi"
  and   P    :: "('a, 'b, 'c) psi"
  and   A\<^sub>P   :: "name list"
  and   \<Psi>\<^sub>P  :: 'b

  assumes QTrans: "\<Psi> \<otimes> \<Psi>\<^sub>P : R \<rhd> Q \<Longrightarrow>M\<lparr>\<nu>*xvec\<rparr>\<langle>N\<rangle> \<prec> Q'"
  and     FrP: "extractFrame P = \<langle>A\<^sub>P, \<Psi>\<^sub>P\<rangle>"
  and     "xvec \<sharp>* P"
  and     "A\<^sub>P \<sharp>* \<Psi>"
  and     "A\<^sub>P \<sharp>* Q"
  and     "A\<^sub>P \<sharp>* M"
  and     "A\<^sub>P \<sharp>* xvec"
  and     "A\<^sub>P \<sharp>* R"

  shows "\<Psi> : P \<parallel> R \<rhd> P \<parallel> Q \<Longrightarrow>M\<lparr>\<nu>*xvec\<rparr>\<langle>N\<rangle> \<prec> P \<parallel> Q'"
proof -
  from QTrans obtain Q'' where QChain: "\<Psi> \<otimes> \<Psi>\<^sub>P \<rhd> Q \<Longrightarrow>\<^sub>\<tau> Q''"
                           and ReqQ'': "insertAssertion (extractFrame R) (\<Psi> \<otimes> \<Psi>\<^sub>P) \<hookrightarrow>\<^sub>F insertAssertion (extractFrame Q'') (\<Psi> \<otimes> \<Psi>\<^sub>P)"
                           and Q''Trans: "\<Psi> \<otimes> \<Psi>\<^sub>P \<rhd> Q'' \<longmapsto>M\<lparr>\<nu>*xvec\<rparr>\<langle>N\<rangle> \<prec> Q'"
    by(rule weakOutputTransitionE)

  from QChain `A\<^sub>P \<sharp>* Q` have "A\<^sub>P \<sharp>* Q''" by(rule tauChainFreshChain)
  with Q''Trans have "A\<^sub>P \<sharp>* Q'" using `A\<^sub>P \<sharp>* xvec` by(rule outputFreshChainDerivative)

  from QChain FrP `A\<^sub>P \<sharp>* \<Psi>` `A\<^sub>P \<sharp>* Q` have "\<Psi> \<rhd> P \<parallel> Q \<Longrightarrow>\<^sub>\<tau> P \<parallel> Q''" by(rule tauChainPar2)
  moreover have "insertAssertion (extractFrame(P \<parallel> R)) \<Psi> \<hookrightarrow>\<^sub>F insertAssertion (extractFrame(P \<parallel> Q'')) \<Psi>"
  proof -
    obtain A\<^sub>R \<Psi>\<^sub>R where FrR: "extractFrame R = \<langle>A\<^sub>R, \<Psi>\<^sub>R\<rangle>" and "A\<^sub>R \<sharp>* A\<^sub>P" and "A\<^sub>R \<sharp>* \<Psi>\<^sub>P" and "A\<^sub>R \<sharp>* \<Psi>"
      by(rule_tac C="(A\<^sub>P, \<Psi>\<^sub>P, \<Psi>)" in freshFrame) auto
    obtain A\<^sub>Q'' \<Psi>\<^sub>Q'' where FrQ'': "extractFrame Q'' = \<langle>A\<^sub>Q'', \<Psi>\<^sub>Q''\<rangle>" and "A\<^sub>Q'' \<sharp>* A\<^sub>P" and "A\<^sub>Q'' \<sharp>* \<Psi>\<^sub>P" and "A\<^sub>Q'' \<sharp>* \<Psi>"
      by(rule_tac C="(A\<^sub>P, \<Psi>\<^sub>P, \<Psi>)" in freshFrame) auto

    from FrR FrQ'' `A\<^sub>P \<sharp>* R` `A\<^sub>P \<sharp>* Q''` `A\<^sub>R \<sharp>* A\<^sub>P` `A\<^sub>Q'' \<sharp>* A\<^sub>P` have "A\<^sub>P \<sharp>* \<Psi>\<^sub>R" and "A\<^sub>P \<sharp>* \<Psi>\<^sub>Q''"
      by(force dest: extractFrameFreshChain)+
    have "\<langle>A\<^sub>R, \<Psi> \<otimes> \<Psi>\<^sub>P \<otimes> \<Psi>\<^sub>R\<rangle> \<simeq>\<^sub>F \<langle>A\<^sub>R, (\<Psi> \<otimes> \<Psi>\<^sub>P) \<otimes> \<Psi>\<^sub>R\<rangle>"
      by(metis frameNilStatEq frameResChainPres Associativity Commutativity Composition AssertionStatEqTrans)

    moreover from ReqQ'' FrR FrQ'' `A\<^sub>R \<sharp>* \<Psi>` `A\<^sub>R \<sharp>* \<Psi>\<^sub>P` `A\<^sub>Q'' \<sharp>* \<Psi>` `A\<^sub>Q'' \<sharp>* \<Psi>\<^sub>P`
    have "\<langle>A\<^sub>R, (\<Psi> \<otimes> \<Psi>\<^sub>P) \<otimes> \<Psi>\<^sub>R\<rangle> \<hookrightarrow>\<^sub>F \<langle>A\<^sub>Q'', (\<Psi> \<otimes> \<Psi>\<^sub>P) \<otimes> \<Psi>\<^sub>Q''\<rangle>" using freshCompChain by simp
    moreover have "\<langle>A\<^sub>Q'', (\<Psi> \<otimes> \<Psi>\<^sub>P) \<otimes> \<Psi>\<^sub>Q''\<rangle> \<simeq>\<^sub>F \<langle>A\<^sub>Q'', \<Psi> \<otimes> \<Psi>\<^sub>P \<otimes> \<Psi>\<^sub>Q''\<rangle>"
      by(metis frameNilStatEq frameResChainPres Associativity Commutativity Composition AssertionStatEqTrans)
    ultimately have "\<langle>A\<^sub>R, \<Psi> \<otimes> \<Psi>\<^sub>P \<otimes> \<Psi>\<^sub>R\<rangle> \<hookrightarrow>\<^sub>F \<langle>A\<^sub>Q'', \<Psi> \<otimes> \<Psi>\<^sub>P \<otimes> \<Psi>\<^sub>Q''\<rangle>"
      by(force dest: FrameStatImpTrans simp add: FrameStatEq_def)
    hence "\<langle>(A\<^sub>P@A\<^sub>R), \<Psi> \<otimes> \<Psi>\<^sub>P \<otimes> \<Psi>\<^sub>R\<rangle> \<hookrightarrow>\<^sub>F \<langle>(A\<^sub>P@A\<^sub>Q''), \<Psi> \<otimes> \<Psi>\<^sub>P \<otimes> \<Psi>\<^sub>Q''\<rangle>"
      apply(simp add: frameChainAppend)
      apply(drule_tac xvec=A\<^sub>P in frameImpResChainPres)
      by(metis frameImpChainComm FrameStatImpTrans)
    with FrR FrP FrQ'' `A\<^sub>R \<sharp>* A\<^sub>P` `A\<^sub>R \<sharp>* \<Psi>\<^sub>P` `A\<^sub>P \<sharp>* \<Psi>\<^sub>R` `A\<^sub>Q'' \<sharp>* A\<^sub>P` `A\<^sub>Q'' \<sharp>* \<Psi>\<^sub>P` `A\<^sub>P \<sharp>* \<Psi>\<^sub>Q''` `A\<^sub>R \<sharp>* \<Psi>` `A\<^sub>Q'' \<sharp>* \<Psi>` `A\<^sub>P \<sharp>* \<Psi>` ReqQ''
    show ?thesis by simp
  qed
  moreover from Q''Trans FrP `xvec \<sharp>* P` `A\<^sub>P \<sharp>* \<Psi>` `A\<^sub>P \<sharp>* Q''` `A\<^sub>P \<sharp>* M` `A\<^sub>P \<sharp>* xvec` have "\<Psi> \<rhd> P \<parallel> Q'' \<longmapsto>M\<lparr>\<nu>*xvec\<rparr>\<langle>N\<rangle> \<prec> (P \<parallel> Q')"
    by(rule_tac Par2B) auto
  ultimately show ?thesis by(rule weakOutputTransitionI)
qed

lemma frameImpIntComposition:
  fixes \<Psi>  :: 'b
  and   \<Psi>' :: 'b
  and   A\<^sub>F :: "name list"
  and   \<Psi>\<^sub>F :: 'b

  assumes "\<Psi> \<simeq> \<Psi>'"

  shows "\<langle>A\<^sub>F, \<Psi> \<otimes> \<Psi>\<^sub>F\<rangle> \<hookrightarrow>\<^sub>F \<langle>A\<^sub>F, \<Psi>' \<otimes> \<Psi>\<^sub>F\<rangle>"
proof -
  from assms have "\<langle>A\<^sub>F, \<Psi> \<otimes> \<Psi>\<^sub>F\<rangle> \<simeq>\<^sub>F \<langle>A\<^sub>F, \<Psi>' \<otimes> \<Psi>\<^sub>F\<rangle>" by(rule frameIntComposition)
  thus ?thesis by(simp add: FrameStatEq_def)
qed

lemma insertAssertionStatImp:
  fixes F  :: "'b frame"
  and   \<Psi>  :: 'b
  and   G  :: "'b frame"
  and   \<Psi>' :: 'b

  assumes FeqG: "insertAssertion F \<Psi> \<hookrightarrow>\<^sub>F insertAssertion G \<Psi>"
  and     "\<Psi> \<simeq> \<Psi>'"

  shows "insertAssertion F \<Psi>' \<hookrightarrow>\<^sub>F insertAssertion G \<Psi>'"
proof -
  obtain A\<^sub>F \<Psi>\<^sub>F where FrF: "F = \<langle>A\<^sub>F, \<Psi>\<^sub>F\<rangle>" and "A\<^sub>F \<sharp>* \<Psi>" and "A\<^sub>F \<sharp>* \<Psi>'"
    by(rule_tac C="(\<Psi>, \<Psi>')" in freshFrame) auto
  obtain A\<^sub>G \<Psi>\<^sub>G where FrG: "G = \<langle>A\<^sub>G, \<Psi>\<^sub>G\<rangle>" and "A\<^sub>G \<sharp>* \<Psi>" and "A\<^sub>G \<sharp>* \<Psi>'"
    by(rule_tac C="(\<Psi>, \<Psi>')" in freshFrame) auto

  from `\<Psi> \<simeq> \<Psi>'` have "\<langle>A\<^sub>F, \<Psi>' \<otimes> \<Psi>\<^sub>F\<rangle> \<simeq>\<^sub>F \<langle>A\<^sub>F, \<Psi> \<otimes> \<Psi>\<^sub>F\<rangle>" by (metis frameIntComposition FrameStatEqSym)
  moreover from `\<Psi> \<simeq> \<Psi>'` have "\<langle>A\<^sub>G, \<Psi> \<otimes> \<Psi>\<^sub>G\<rangle> \<simeq>\<^sub>F \<langle>A\<^sub>G, \<Psi>' \<otimes> \<Psi>\<^sub>G\<rangle>" by(rule frameIntComposition)
  ultimately have "\<langle>A\<^sub>F, \<Psi>' \<otimes> \<Psi>\<^sub>F\<rangle> \<hookrightarrow>\<^sub>F \<langle>A\<^sub>G, \<Psi>' \<otimes> \<Psi>\<^sub>G\<rangle>" using FeqG FrF FrG `A\<^sub>F \<sharp>* \<Psi>` `A\<^sub>G \<sharp>* \<Psi>` `\<Psi> \<simeq> \<Psi>'`
    by(force simp add: FrameStatEq_def dest: FrameStatImpTrans)
  with FrF FrG `A\<^sub>F \<sharp>* \<Psi>'` `A\<^sub>G \<sharp>* \<Psi>'` show ?thesis by simp
qed

lemma insertAssertionStatEq:
  fixes F  :: "'b frame"
  and   \<Psi>  :: 'b
  and   G  :: "'b frame"
  and   \<Psi>' :: 'b

  assumes FeqG: "insertAssertion F \<Psi> \<simeq>\<^sub>F insertAssertion G \<Psi>"
  and     "\<Psi> \<simeq> \<Psi>'"

  shows "insertAssertion F \<Psi>' \<simeq>\<^sub>F insertAssertion G \<Psi>'"
proof -
  obtain A\<^sub>F \<Psi>\<^sub>F where FrF: "F = \<langle>A\<^sub>F, \<Psi>\<^sub>F\<rangle>" and "A\<^sub>F \<sharp>* \<Psi>" and "A\<^sub>F \<sharp>* \<Psi>'"
    by(rule_tac C="(\<Psi>, \<Psi>')" in freshFrame) auto
  obtain A\<^sub>G \<Psi>\<^sub>G where FrG: "G = \<langle>A\<^sub>G, \<Psi>\<^sub>G\<rangle>" and "A\<^sub>G \<sharp>* \<Psi>" and "A\<^sub>G \<sharp>* \<Psi>'"
    by(rule_tac C="(\<Psi>, \<Psi>')" in freshFrame) auto

  from FeqG FrF FrG `A\<^sub>F \<sharp>* \<Psi>` `A\<^sub>G \<sharp>* \<Psi>` `\<Psi> \<simeq> \<Psi>'`
  have "\<langle>A\<^sub>F, \<Psi>' \<otimes> \<Psi>\<^sub>F\<rangle> \<simeq>\<^sub>F \<langle>A\<^sub>G, \<Psi>' \<otimes> \<Psi>\<^sub>G\<rangle>"
    by simp (metis frameIntComposition FrameStatEqTrans FrameStatEqSym)
  with FrF FrG `A\<^sub>F \<sharp>* \<Psi>'` `A\<^sub>G \<sharp>* \<Psi>'` show ?thesis by simp
qed

lemma weakOutputStatEq:
  fixes \<Psi>   :: 'b
  and   Q    :: "('a, 'b, 'c) psi"
  and   P    :: "('a, 'b, 'c) psi"
  and   M    :: 'a
  and   xvec :: "name list"
  and   N    :: 'a
  and   P'   :: "('a, 'b, 'c) psi"
  and   \<Psi>'  :: 'b

  assumes PTrans: "\<Psi> : Q \<rhd> P \<Longrightarrow>M\<lparr>\<nu>*xvec\<rparr>\<langle>N\<rangle> \<prec> P'"
  and     "\<Psi> \<simeq> \<Psi>'"

  shows "\<Psi>' : Q \<rhd> P \<Longrightarrow>M\<lparr>\<nu>*xvec\<rparr>\<langle>N\<rangle> \<prec> P'"
proof -
  from PTrans obtain P'' where PChain: "\<Psi> \<rhd> P \<Longrightarrow>\<^sub>\<tau> P''"
                           and QeqP'': "insertAssertion (extractFrame Q) \<Psi> \<hookrightarrow>\<^sub>F insertAssertion (extractFrame P'') \<Psi>"
                           and P''Trans: "\<Psi> \<rhd> P'' \<longmapsto>M\<lparr>\<nu>*xvec\<rparr>\<langle>N\<rangle> \<prec> P'"
    by(rule weakOutputTransitionE)

  from PChain `\<Psi> \<simeq> \<Psi>'` have "\<Psi>' \<rhd> P \<Longrightarrow>\<^sub>\<tau> P''" by(rule tauChainStatEq)
  moreover from QeqP'' `\<Psi> \<simeq> \<Psi>'` have "insertAssertion (extractFrame Q) \<Psi>' \<hookrightarrow>\<^sub>F insertAssertion (extractFrame P'') \<Psi>'"
    by(rule insertAssertionStatImp)
  moreover from P''Trans `\<Psi> \<simeq> \<Psi>'` have "\<Psi>' \<rhd> P'' \<longmapsto>M\<lparr>\<nu>*xvec\<rparr>\<langle>N\<rangle> \<prec> P'"
    by(rule statEqTransition)
  ultimately show ?thesis by(rule weakOutputTransitionI)
qed

lemma weakInputStatEq:
  fixes \<Psi>   :: 'b
  and   Q    :: "('a, 'b, 'c) psi"
  and   P    :: "('a, 'b, 'c) psi"
  and   M    :: 'a
  and   N    :: 'a
  and   P''  :: "('a, 'b, 'c) psi"
  and   \<Psi>'  :: 'b

  assumes PTrans: "\<Psi> : Q \<rhd> P \<Longrightarrow>M\<lparr>N\<rparr> \<prec> P'"
  and     "\<Psi> \<simeq> \<Psi>'"

  shows "\<Psi>' : Q \<rhd> P \<Longrightarrow>M\<lparr>N\<rparr> \<prec> P'"
proof -
  from PTrans obtain P'' where PChain: "\<Psi> \<rhd> P \<Longrightarrow>\<^sub>\<tau> P''"
                           and QeqP'': "insertAssertion (extractFrame Q) \<Psi> \<hookrightarrow>\<^sub>F insertAssertion (extractFrame P'') \<Psi>"
                           and P''Trans: "\<Psi> \<rhd> P'' \<longmapsto>M\<lparr>N\<rparr> \<prec> P'"
    by(rule weakInputTransitionE)

  from PChain `\<Psi> \<simeq> \<Psi>'` have "\<Psi>' \<rhd> P \<Longrightarrow>\<^sub>\<tau> P''" by(rule tauChainStatEq)
  moreover from QeqP'' `\<Psi> \<simeq> \<Psi>'` have "insertAssertion (extractFrame Q) \<Psi>' \<hookrightarrow>\<^sub>F insertAssertion (extractFrame P'') \<Psi>'"
    by(rule insertAssertionStatImp)
  moreover from P''Trans `\<Psi> \<simeq> \<Psi>'` have "\<Psi>' \<rhd> P'' \<longmapsto>M\<lparr>N\<rparr> \<prec> P'"
    by(rule statEqTransition)
  ultimately show ?thesis by(rule weakInputTransitionI)
qed

lemma outputWeakOutput:
  fixes \<Psi>   :: 'b
  and   Q    :: "('a, 'b, 'c) psi"
  and   P    :: "('a, 'b, 'c) psi"
  and   M    :: 'a
  and   xvec :: "name list"
  and   N    :: 'a
  and   P'   :: "('a, 'b, 'c) psi"
  
  assumes "\<Psi> \<rhd> P \<longmapsto>M\<lparr>\<nu>*xvec\<rparr>\<langle>N\<rangle> \<prec> P'"
  and     "insertAssertion(extractFrame Q) \<Psi> \<hookrightarrow>\<^sub>F insertAssertion(extractFrame P) \<Psi>"

  shows "\<Psi> : Q \<rhd> P \<Longrightarrow>M\<lparr>\<nu>*xvec\<rparr>\<langle>N\<rangle> \<prec> P'"
using assms
by(fastforce intro: TauBase weakOutputTransitionI)

lemma inputWeakInput:
  fixes \<Psi>  :: 'b
  and   Q    :: "('a, 'b, 'c) psi"
  and   P   :: "('a, 'b, 'c) psi"
  and   M   :: 'a
  and   N   :: 'a
  and   P'  :: "('a, 'b, 'c) psi"
  
  assumes "\<Psi> \<rhd> P \<longmapsto>M\<lparr>N\<rparr> \<prec> P'"
  and     "insertAssertion(extractFrame Q) \<Psi> \<hookrightarrow>\<^sub>F insertAssertion(extractFrame P) \<Psi>"

  shows "\<Psi> : Q \<rhd> P \<Longrightarrow>M\<lparr>N\<rparr> \<prec> P'"
using assms
by(fastforce intro: TauBase weakInputTransitionI)

lemma weakPar1GuardedF:
  fixes \<Psi>  :: 'b
  and   R    :: "('a, 'b, 'c) psi"
  and   P   :: "('a, 'b, 'c) psi"
  and   M   :: 'a
  and   N   :: 'a
  and   P'  :: "('a, 'b, 'c) psi"
  and   Q   :: "('a, 'b, 'c) psi"

  assumes PTrans: "\<Psi> : R \<rhd> P \<Longrightarrow>M\<lparr>N\<rparr> \<prec> P'"
  and     "guarded Q"

  shows "\<Psi> : (R \<parallel> Q) \<rhd> P \<parallel> Q \<Longrightarrow>M\<lparr>N\<rparr> \<prec> P' \<parallel> Q"
proof -
  obtain A\<^sub>Q \<Psi>\<^sub>Q where FrQ: "extractFrame Q = \<langle>A\<^sub>Q, \<Psi>\<^sub>Q\<rangle>" and "A\<^sub>Q \<sharp>* \<Psi>" and "A\<^sub>Q \<sharp>* P" and "A\<^sub>Q \<sharp>* M" and "A\<^sub>Q \<sharp>* N" and "A\<^sub>Q \<sharp>* R"
    by(rule_tac C="(\<Psi>, P, M, N, R)" in freshFrame) auto
  from `guarded Q` FrQ have "\<Psi>\<^sub>Q \<simeq> \<one>" by(blast dest: guardedStatEq)
  with PTrans have "\<Psi> \<otimes> \<Psi>\<^sub>Q : R \<rhd> P \<Longrightarrow>M\<lparr>N\<rparr> \<prec> P'" by(metis weakInputStatEq Identity AssertionStatEqSym compositionSym)
  thus ?thesis using FrQ `A\<^sub>Q \<sharp>* \<Psi>` `A\<^sub>Q \<sharp>* P` `A\<^sub>Q \<sharp>* M` `A\<^sub>Q \<sharp>* N` `A\<^sub>Q \<sharp>* R` 
    by(rule weakPar1F)
qed

lemma weakBangF:
  fixes \<Psi>  :: 'b
  and   R    :: "('a, 'b, 'c) psi"
  and   P   :: "('a, 'b, 'c) psi"
  and   M   :: 'a
  and   N   :: 'a
  and   P'  :: "('a, 'b, 'c) psi"
  and   Q   :: "('a, 'b, 'c) psi"

  assumes PTrans: "\<Psi> : R \<rhd> P \<parallel> !P \<Longrightarrow>M\<lparr>N\<rparr> \<prec> P'"
  and     "guarded P"

  shows "\<Psi> : R \<rhd> !P \<Longrightarrow>M\<lparr>N\<rparr> \<prec> P'"
proof -
  from PTrans obtain P'' where PChain: "\<Psi> \<rhd> P \<parallel> !P \<Longrightarrow>\<^sub>\<tau> P''"
                           and RImpP'': "insertAssertion(extractFrame R) \<Psi> \<hookrightarrow>\<^sub>F insertAssertion(extractFrame P'') \<Psi>"
                           and P''Trans: "\<Psi> \<rhd> P'' \<longmapsto>M\<lparr>N\<rparr> \<prec> P'"
    by(rule weakInputTransitionE)
  moreover obtain A\<^sub>P \<Psi>\<^sub>P where FrP: "extractFrame P = \<langle>A\<^sub>P, \<Psi>\<^sub>P\<rangle>" and "A\<^sub>P \<sharp>* \<Psi>" by(rule freshFrame)
  moreover from `guarded P` FrP have "\<Psi>\<^sub>P \<simeq> \<one>" by(blast dest: guardedStatEq)
  ultimately show ?thesis
  proof(cases rule: Tau_Chain.cases, auto)
    have "\<Psi> \<rhd> !P \<Longrightarrow>\<^sub>\<tau> !P" by(rule TauBase)
    moreover assume RimpP: "insertAssertion(extractFrame R) \<Psi> \<hookrightarrow>\<^sub>F \<langle>A\<^sub>P, \<Psi> \<otimes> \<Psi>\<^sub>P \<otimes> \<one>\<rangle>"
    have "insertAssertion(extractFrame R) \<Psi> \<hookrightarrow>\<^sub>F insertAssertion(extractFrame(!P)) \<Psi>"
    proof -
      from `\<Psi>\<^sub>P \<simeq> \<one>` have "\<langle>A\<^sub>P, \<Psi> \<otimes> \<Psi>\<^sub>P \<otimes> \<one>\<rangle> \<simeq>\<^sub>F \<langle>A\<^sub>P, \<Psi> \<otimes> \<one>\<rangle>"
        by(metis frameIntCompositionSym frameIntAssociativity frameIntCommutativity frameIntIdentity FrameStatEqTrans FrameStatEqSym)
      moreover from `A\<^sub>P \<sharp>* \<Psi>` have "\<langle>A\<^sub>P, \<Psi> \<otimes> \<one>\<rangle> \<simeq>\<^sub>F \<langle>\<epsilon>, \<Psi> \<otimes> \<one>\<rangle>"
        by(force intro: frameResFreshChain)
      ultimately show ?thesis using RimpP by(auto simp add: FrameStatEq_def dest: FrameStatImpTrans)
    qed
    moreover assume "\<Psi> \<rhd> P \<parallel> !P \<longmapsto>M\<lparr>N\<rparr> \<prec> P'"
    hence "\<Psi> \<rhd> !P \<longmapsto>M\<lparr>N\<rparr> \<prec> P'" using `guarded P` by(rule Bang)
   ultimately show ?thesis by(rule weakInputTransitionI)
  next
    fix P'''
    assume "\<Psi> \<rhd> P \<parallel> !P \<longmapsto>\<tau> \<prec>  P'''"
    hence "\<Psi> \<rhd> !P \<longmapsto>\<tau> \<prec> P'''" using `guarded P` by(rule Bang)
    moreover assume "\<Psi> \<rhd> P''' \<Longrightarrow>\<^sub>\<tau> P''"
    ultimately have "\<Psi> \<rhd> !P \<Longrightarrow>\<^sub>\<tau> P''" by(rule TauStep)
    moreover assume "insertAssertion(extractFrame R) \<Psi> \<hookrightarrow>\<^sub>F insertAssertion(extractFrame P'') \<Psi>"
                and "\<Psi> \<rhd> P'' \<longmapsto>M\<lparr>N\<rparr> \<prec> P'"
    ultimately show ?thesis by(rule weakInputTransitionI)
  qed
qed

lemma weakInputTransitionFrameImp:
  fixes \<Psi> :: 'b
  and   Q  :: "('a, 'b, 'c) psi"
  and   P  :: "('a, 'b, 'c) psi"
  and   M  :: 'a
  and   N  :: 'a
  and   P' :: "('a, 'b, 'c) psi"
  and   R  :: "('a, 'b, 'c) psi"

  assumes PTrans: "\<Psi> : Q \<rhd> P \<Longrightarrow>M\<lparr>N\<rparr> \<prec> P'"
  and             "insertAssertion(extractFrame R) \<Psi> \<hookrightarrow>\<^sub>F insertAssertion(extractFrame Q) \<Psi>"

  shows "\<Psi> : R \<rhd> P \<Longrightarrow>M\<lparr>N\<rparr> \<prec> P'"
using assms
by(auto simp add: weakInputTransition_def intro: FrameStatImpTrans)

lemma weakOutputTransitionFrameImp:
  fixes \<Psi>   :: 'b
  and   Q    :: "('a, 'b, 'c) psi"
  and   P    :: "('a, 'b, 'c) psi"
  and   M    :: 'a
  and   xvec :: "name list"
  and   N    :: 'a
  and   P'   :: "('a, 'b, 'c) psi"
  and   R    :: "('a, 'b, 'c) psi"

  assumes PTrans: "\<Psi> : Q \<rhd> P \<Longrightarrow>M\<lparr>\<nu>*xvec\<rparr>\<langle>N\<rangle> \<prec> P'"
  and             "insertAssertion(extractFrame R) \<Psi> \<hookrightarrow>\<^sub>F insertAssertion(extractFrame Q) \<Psi>"

  shows "\<Psi> : R \<rhd> P \<Longrightarrow>M\<lparr>\<nu>*xvec\<rparr>\<langle>N\<rangle> \<prec> P'"
using assms
by(auto simp add: weakOutputTransition_def intro: FrameStatImpTrans)

lemma guardedFrameStatEq:
  fixes P :: "('a, 'b, 'c) psi"

  assumes "guarded P"

  shows "extractFrame P \<simeq>\<^sub>F \<langle>\<epsilon>, \<one>\<rangle>"
proof -
  obtain A\<^sub>P \<Psi>\<^sub>P where FrP: "extractFrame P = \<langle>A\<^sub>P, \<Psi>\<^sub>P\<rangle>" by(rule freshFrame)
  from `guarded P` FrP have "\<Psi>\<^sub>P \<simeq> \<one>" by(blast dest: guardedStatEq)
  hence "\<langle>A\<^sub>P, \<Psi>\<^sub>P\<rangle> \<simeq>\<^sub>F \<langle>A\<^sub>P, \<one>\<rangle>" by(rule_tac frameResChainPres) auto
  moreover have "\<langle>A\<^sub>P, \<one>\<rangle> \<simeq>\<^sub>F \<langle>\<epsilon>, \<one>\<rangle>" by(rule_tac frameResFreshChain) auto
  ultimately show ?thesis using FrP by(force intro: FrameStatEqTrans)
qed

lemma weakInputGuardedTransition:
  fixes \<Psi> :: 'b
  and   Q  :: "('a, 'b, 'c) psi"
  and   P  :: "('a, 'b, 'c) psi"
  and   M  :: 'a
  and   N  :: 'a
  and   P' :: "('a, 'b, 'c) psi"
  and   R  :: "('a, 'b, 'c) psi"

  assumes PTrans: "\<Psi> : Q \<rhd> P \<Longrightarrow>M\<lparr>N\<rparr> \<prec> P'"
  and    "guarded Q"

  shows "\<Psi> : \<zero> \<rhd> P \<Longrightarrow>M\<lparr>N\<rparr> \<prec> P'"
proof -
  obtain A\<^sub>Q \<Psi>\<^sub>Q where FrQ: "extractFrame Q = \<langle>A\<^sub>Q, \<Psi>\<^sub>Q\<rangle>" and "A\<^sub>Q \<sharp>* \<Psi>" by(rule freshFrame)
  moreover from `guarded Q` FrQ have "\<Psi>\<^sub>Q \<simeq> \<one>" by(blast dest: guardedStatEq)
  hence "\<langle>A\<^sub>Q, \<Psi> \<otimes> \<Psi>\<^sub>Q\<rangle> \<simeq>\<^sub>F \<langle>A\<^sub>Q, \<Psi> \<otimes> \<one>\<rangle>" by(metis frameIntCompositionSym)
  moreover from `A\<^sub>Q \<sharp>* \<Psi>` have "\<langle>A\<^sub>Q, \<Psi> \<otimes> \<one>\<rangle> \<simeq>\<^sub>F \<langle>\<epsilon>, \<Psi> \<otimes> \<one>\<rangle>" by(rule_tac frameResFreshChain) auto
  ultimately have "insertAssertion(extractFrame Q) \<Psi> \<simeq>\<^sub>F insertAssertion (extractFrame (\<zero>)) \<Psi>"
    using FrQ `A\<^sub>Q \<sharp>* \<Psi>` by simp (blast intro: FrameStatEqTrans)
  with PTrans show ?thesis by(rule_tac weakInputTransitionFrameImp) (auto simp add: FrameStatEq_def) 
qed

lemma weakOutputGuardedTransition:
  fixes \<Psi>   :: 'b
  and   Q    :: "('a, 'b, 'c) psi"
  and   P    :: "('a, 'b, 'c) psi"
  and   M    :: 'a
  and   xvec :: "name list"
  and   N    :: 'a
  and   P'   :: "('a, 'b, 'c) psi"
  and   R    :: "('a, 'b, 'c) psi"

  assumes PTrans: "\<Psi> : Q \<rhd> P \<Longrightarrow>M\<lparr>\<nu>*xvec\<rparr>\<langle>N\<rangle> \<prec> P'"
  and    "guarded Q"

  shows "\<Psi> : \<zero> \<rhd> P \<Longrightarrow>M\<lparr>\<nu>*xvec\<rparr>\<langle>N\<rangle> \<prec> P'"
proof -
  obtain A\<^sub>Q \<Psi>\<^sub>Q where FrQ: "extractFrame Q = \<langle>A\<^sub>Q, \<Psi>\<^sub>Q\<rangle>" and "A\<^sub>Q \<sharp>* \<Psi>" by(rule freshFrame)
  moreover from `guarded Q` FrQ have "\<Psi>\<^sub>Q \<simeq> \<one>" by(blast dest: guardedStatEq)
  hence "\<langle>A\<^sub>Q, \<Psi> \<otimes> \<Psi>\<^sub>Q\<rangle> \<simeq>\<^sub>F \<langle>A\<^sub>Q, \<Psi> \<otimes> \<one>\<rangle>" by(metis frameIntCompositionSym)
  moreover from `A\<^sub>Q \<sharp>* \<Psi>` have "\<langle>A\<^sub>Q, \<Psi> \<otimes> \<one>\<rangle> \<simeq>\<^sub>F \<langle>\<epsilon>, \<Psi> \<otimes> \<one>\<rangle>" by(rule_tac frameResFreshChain) auto
  ultimately have "insertAssertion(extractFrame Q) \<Psi> \<simeq>\<^sub>F insertAssertion (extractFrame (\<zero>)) \<Psi>"
    using FrQ `A\<^sub>Q \<sharp>* \<Psi>` by simp (blast intro: FrameStatEqTrans)
  with PTrans show ?thesis by(rule_tac weakOutputTransitionFrameImp) (auto simp add: FrameStatEq_def) 
qed

end 

end
