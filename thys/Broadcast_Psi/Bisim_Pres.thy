theory Bisim_Pres
  imports Bisimulation Sim_Pres
begin

text \<open>This file is a (heavily modified) variant of the theory {\it Psi\_Calculi.Bisim\_Pres}
from~\cite{DBLP:journals/afp/Bengtson12}.\<close>

context env begin

lemma bisimInputPres:
  fixes \<Psi>    :: 'b
    and P    :: "('a, 'b, 'c) psi"
    and Q    :: "('a, 'b, 'c) psi"
    and M    :: 'a
    and xvec :: "name list"
    and N    :: 'a

assumes "\<And>Tvec. length xvec = length Tvec \<Longrightarrow> \<Psi> \<rhd> P[xvec::=Tvec] \<sim> Q[xvec::=Tvec]"

shows "\<Psi> \<rhd> M\<lparr>\<lambda>*xvec N\<rparr>.P \<sim> M\<lparr>\<lambda>*xvec N\<rparr>.Q"
proof -
  let ?X = "{(\<Psi>, M\<lparr>\<lambda>*xvec N\<rparr>.P, M\<lparr>\<lambda>*xvec N\<rparr>.Q) | \<Psi> M xvec N P Q. \<forall>Tvec. length xvec = length Tvec \<longrightarrow> \<Psi> \<rhd> P[xvec::=Tvec] \<sim> Q[xvec::=Tvec]}"

  from assms have "(\<Psi>, M\<lparr>\<lambda>*xvec N\<rparr>.P, M\<lparr>\<lambda>*xvec N\<rparr>.Q) \<in> ?X" by blast
  then show ?thesis
  proof(coinduct rule: bisimCoinduct)
    case(cStatEq \<Psi> P Q)
    then show ?case by auto
  next
    case(cSim \<Psi> P Q)
    then show ?case by(blast intro: inputPres)
  next
    case(cExt \<Psi> P Q \<Psi>')
    then show ?case by(blast dest: bisimE)
  next
    case(cSym \<Psi> P Q)
    then show ?case by(blast dest: bisimE)
  qed
qed

lemma bisimOutputPres:
  fixes \<Psi> :: 'b
    and P :: "('a, 'b, 'c) psi"
    and Q :: "('a, 'b, 'c) psi"
    and M :: 'a
    and N :: 'a

assumes "\<Psi> \<rhd> P \<sim> Q"

shows "\<Psi> \<rhd> M\<langle>N\<rangle>.P \<sim> M\<langle>N\<rangle>.Q"
proof -
  let ?X = "{(\<Psi>, M\<langle>N\<rangle>.P, M\<langle>N\<rangle>.Q) | \<Psi> M N P Q. \<Psi> \<rhd> P \<sim> Q}"
  from \<open>\<Psi> \<rhd> P \<sim> Q\<close> have "(\<Psi>, M\<langle>N\<rangle>.P, M\<langle>N\<rangle>.Q) \<in> ?X" by auto
  then show ?thesis
    by(coinduct rule: bisimCoinduct, auto) (blast intro: outputPres dest: bisimE)+
qed

lemma bisimCasePres:
  fixes \<Psi>   :: 'b
    and CsP :: "('c \<times> ('a, 'b, 'c) psi) list"
    and CsQ :: "('c \<times> ('a, 'b, 'c) psi) list"

assumes "\<And>\<phi> P. (\<phi>, P) \<in> set CsP \<Longrightarrow> \<exists>Q. (\<phi>, Q) \<in> set CsQ \<and> guarded Q \<and> \<Psi> \<rhd> P \<sim> Q"
  and   "\<And>\<phi> Q. (\<phi>, Q) \<in> set CsQ \<Longrightarrow> \<exists>P. (\<phi>, P) \<in> set CsP \<and> guarded P \<and> \<Psi> \<rhd> P \<sim> Q"

shows "\<Psi> \<rhd> Cases CsP \<sim> Cases CsQ"
proof -
  let ?X = "{(\<Psi>, Cases CsP, Cases CsQ) | \<Psi> CsP CsQ. (\<forall>\<phi> P. (\<phi>, P) \<in> set CsP \<longrightarrow> (\<exists>Q. (\<phi>, Q) \<in> set CsQ \<and> guarded Q \<and> \<Psi> \<rhd> P \<sim> Q)) \<and>
                                                     (\<forall>\<phi> Q. (\<phi>, Q) \<in> set CsQ \<longrightarrow> (\<exists>P. (\<phi>, P) \<in> set CsP \<and> guarded P \<and> \<Psi> \<rhd> P \<sim> Q))}"
  from assms have "(\<Psi>, Cases CsP, Cases CsQ) \<in> ?X" by auto
  then show ?thesis
  proof(coinduct rule: bisimCoinduct)
    case(cStatEq \<Psi> P Q)
    then show ?case by auto
  next
    case(cSim \<Psi> CasesP CasesQ)
    then obtain CsP CsQ where C1: "\<And>\<phi> Q. (\<phi>, Q) \<in> set CsQ \<Longrightarrow> \<exists>P. (\<phi>, P) \<in> set CsP \<and> guarded P \<and> \<Psi> \<rhd> P \<sim> Q"
      and A: "CasesP = Cases CsP" and B: "CasesQ = Cases CsQ"
      by auto
    note C1
    moreover have "\<And>\<Psi> P Q. \<Psi> \<rhd> P \<sim> Q \<Longrightarrow> \<Psi> \<rhd> P \<leadsto>[bisim] Q" by(rule bisimE)
    moreover have "bisim \<subseteq> ?X \<union> bisim" by blast
    ultimately have "\<Psi> \<rhd> Cases CsP \<leadsto>[(?X \<union> bisim)] Cases CsQ"
      by(rule casePres)
    then show ?case using A B by blast
  next
    case(cExt \<Psi> P Q)
    then show ?case by(blast dest: bisimE)
  next
    case(cSym \<Psi> P Q)
    then show ?case by(blast dest: bisimE)
  qed
qed

lemma bisimResPres:
  fixes \<Psi> :: 'b
    and P :: "('a, 'b, 'c) psi"
    and Q :: "('a, 'b, 'c) psi"
    and x :: name

assumes "\<Psi> \<rhd> P \<sim> Q"
  and   "x \<sharp> \<Psi>"

shows "\<Psi> \<rhd> \<lparr>\<nu>x\<rparr>P \<sim> \<lparr>\<nu>x\<rparr>Q"
proof -
  let ?X = "{(\<Psi>, \<lparr>\<nu>*xvec\<rparr>P, \<lparr>\<nu>*xvec\<rparr>Q) | \<Psi> xvec P Q. \<Psi> \<rhd> P \<sim> Q \<and> xvec \<sharp>* \<Psi>}"
  have "eqvt ?X" using bisimClosed pt_fresh_star_bij[OF pt_name_inst, OF at_name_inst]
    by(auto simp add: eqvts eqvt_def) blast
  have "(\<Psi>, \<lparr>\<nu>x\<rparr>P, \<lparr>\<nu>x\<rparr>Q) \<in> ?X"
  proof -
    from \<open>x \<sharp> \<Psi>\<close> have "[x] \<sharp>* \<Psi>"
      by auto
    with \<open>\<Psi> \<rhd> P \<sim> Q\<close> show ?thesis
      by (smt mem_Collect_eq resChain.base resChain.step)
  qed
  then show ?thesis
  proof(coinduct rule: bisimCoinduct)
    case(cStatEq \<Psi> xP xQ)
    from \<open>(\<Psi>, xP, xQ) \<in> ?X\<close> obtain xvec P Q where "\<Psi> \<rhd> P \<sim> Q" and "xvec \<sharp>* \<Psi>" and "xP = \<lparr>\<nu>*xvec\<rparr>P" and "xQ = \<lparr>\<nu>*xvec\<rparr>Q"
      by auto
    moreover from \<open>\<Psi> \<rhd> P \<sim> Q\<close> have PeqQ: "insertAssertion(extractFrame P) \<Psi> \<simeq>\<^sub>F insertAssertion(extractFrame Q) \<Psi>"
      by(rule bisimE)
    ultimately show ?case by(auto intro: frameResChainPres)
  next
    case(cSim \<Psi> xP xQ)
    from \<open>(\<Psi>, xP, xQ) \<in> ?X\<close> obtain xvec P Q where "\<Psi> \<rhd> P \<sim> Q" and "xvec \<sharp>* \<Psi>" and "xP = \<lparr>\<nu>*xvec\<rparr>P" and "xQ = \<lparr>\<nu>*xvec\<rparr>Q"
      by auto
    from \<open>\<Psi> \<rhd> P \<sim> Q\<close> have "\<Psi> \<rhd> P \<leadsto>[bisim] Q" by(rule bisimE)
    note \<open>eqvt ?X\<close>
    then have "eqvt(?X \<union> bisim)" by auto
    from \<open>xvec \<sharp>* \<Psi>\<close>
    have "\<Psi> \<rhd> \<lparr>\<nu>*xvec\<rparr>P \<leadsto>[(?X \<union> bisim)] \<lparr>\<nu>*xvec\<rparr>Q"
    proof(induct xvec)
      case Nil
      have "\<Psi> \<rhd> \<lparr>\<nu>*[]\<rparr>P \<leadsto>[bisim] \<lparr>\<nu>*[]\<rparr>Q" using \<open>\<Psi> \<rhd> P \<sim> Q\<close>
        unfolding resChain.simps
        by(rule bisimE)
      then show ?case by(rule monotonic) auto
    next
      case(Cons x xvec)
      then have "x \<sharp> \<Psi>" and "xvec \<sharp>* \<Psi>"
        by auto
      from \<open>xvec \<sharp>* \<Psi>\<close> have "\<Psi> \<rhd> \<lparr>\<nu>*xvec\<rparr>P \<leadsto>[(?X \<union> bisim)] \<lparr>\<nu>*xvec\<rparr>Q"
        by(rule Cons)
      moreover note \<open>eqvt(?X \<union> bisim)\<close>
      moreover note \<open>x \<sharp> \<Psi>\<close>
      moreover have "?X \<union> bisim \<subseteq> ?X \<union> bisim" by auto
      moreover have "\<And>\<Psi> P Q xvec. \<lbrakk>(\<Psi>, P, Q) \<in> ?X \<union> bisim; xvec \<sharp>* \<Psi>\<rbrakk> \<Longrightarrow> (\<Psi>, \<lparr>\<nu>*xvec\<rparr>P, \<lparr>\<nu>*xvec\<rparr>Q) \<in> ?X \<union> bisim"
        by (smt (verit, ccfv_threshold) Un_iff freshChainAppend mem_Collect_eq prod.inject resChainAppend)
      ultimately have "\<Psi> \<rhd> \<lparr>\<nu>x\<rparr>(\<lparr>\<nu>*xvec\<rparr>P) \<leadsto>[(?X \<union> bisim)] \<lparr>\<nu>x\<rparr>(\<lparr>\<nu>*xvec\<rparr>Q)"
        by(rule resPres)
      then show ?case unfolding resChain.simps by -
    next
    qed
    with \<open>xP = \<lparr>\<nu>*xvec\<rparr>P\<close> \<open>xQ = \<lparr>\<nu>*xvec\<rparr>Q\<close> show ?case
      by simp
  next
    case(cExt \<Psi> xP xQ \<Psi>')
    from \<open>(\<Psi>, xP, xQ) \<in> ?X\<close> obtain xvec P Q where "\<Psi> \<rhd> P \<sim> Q" and "xvec \<sharp>* \<Psi>" and xpe: "xP = \<lparr>\<nu>*xvec\<rparr>P" and xqe: "xQ = \<lparr>\<nu>*xvec\<rparr>Q"
      by auto
    obtain p::"name prm" where "(p\<bullet>xvec) \<sharp>* \<Psi>" and "(p\<bullet>xvec) \<sharp>* \<Psi>'" and "(p\<bullet>xvec) \<sharp>* P" and "(p\<bullet>xvec) \<sharp>* Q" and "(p\<bullet>xvec) \<sharp>* xvec" and "distinctPerm p" and "set p \<subseteq> (set xvec) \<times> (set (p\<bullet>xvec))"
      by(rule name_list_avoiding[where c="(\<Psi>,\<Psi>',P,Q,xvec)"]) auto
    from \<open>\<Psi> \<rhd> P \<sim> Q\<close> have "\<Psi> \<otimes> (p\<bullet>\<Psi>') \<rhd> P \<sim> Q"
      by(rule bisimE)
    moreover have "xvec \<sharp>* (\<Psi> \<otimes> (p\<bullet>\<Psi>'))" using \<open>xvec \<sharp>* \<Psi>\<close> \<open>(p\<bullet>xvec) \<sharp>* \<Psi>'\<close> \<open>distinctPerm p\<close>
      apply(intro freshCompChain)
       apply assumption
      apply(subst perm_bool[where pi=p,symmetric])
      by(simp add: eqvts)
    ultimately have "(\<Psi> \<otimes> (p\<bullet>\<Psi>'),\<lparr>\<nu>*xvec\<rparr>P,\<lparr>\<nu>*xvec\<rparr>Q) \<in> ?X"
      by auto
    then have "(p\<bullet>(\<Psi> \<otimes> (p\<bullet>\<Psi>'),\<lparr>\<nu>*xvec\<rparr>P,\<lparr>\<nu>*xvec\<rparr>Q)) \<in> ?X" using \<open>eqvt ?X\<close>
      by(intro eqvtI)
    then have "(\<Psi> \<otimes> \<Psi>',\<lparr>\<nu>*(p\<bullet>xvec)\<rparr>(p\<bullet>P),\<lparr>\<nu>*(p\<bullet>xvec)\<rparr>(p\<bullet>Q)) \<in> ?X" using \<open>distinctPerm p\<close> \<open>set p \<subseteq> (set xvec) \<times> (set (p\<bullet>xvec))\<close> \<open>xvec \<sharp>* \<Psi>\<close> \<open>(p\<bullet>xvec) \<sharp>* \<Psi>\<close>
      by(simp add: eqvts)
    then have "(\<Psi> \<otimes> \<Psi>',\<lparr>\<nu>*xvec\<rparr>P,\<lparr>\<nu>*xvec\<rparr>Q) \<in> ?X" using \<open>(p \<bullet> xvec) \<sharp>* Q\<close> \<open>(p \<bullet> xvec) \<sharp>* P\<close> \<open>set p \<subseteq> set xvec \<times> set (p \<bullet> xvec)\<close> \<open>distinctPerm p\<close>
      by(subst (1 2) resChainAlpha[where p=p]) auto
    then show ?case unfolding xpe xqe
      by blast
  next
    case(cSym \<Psi> P Q)
    then show ?case
      by(blast dest: bisimE)
  qed
qed

lemma bisimResChainPres:
  fixes \<Psi>   :: 'b
    and P    :: "('a, 'b, 'c) psi"
    and Q    :: "('a, 'b, 'c) psi"
    and xvec :: "name list"

assumes "\<Psi> \<rhd> P \<sim> Q"
  and   "xvec \<sharp>* \<Psi>"

shows "\<Psi> \<rhd> \<lparr>\<nu>*xvec\<rparr>P \<sim> \<lparr>\<nu>*xvec\<rparr>Q"
  using assms
  by(induct xvec) (auto intro: bisimResPres)

lemma bisimParPresAux:
  fixes \<Psi>  :: 'b
    and \<Psi>\<^sub>R :: 'b
    and P  :: "('a, 'b, 'c) psi"
    and Q  :: "('a, 'b, 'c) psi"
    and R  :: "('a, 'b, 'c) psi"
    and A\<^sub>R :: "name list"

assumes "\<Psi> \<otimes> \<Psi>\<^sub>R \<rhd> P \<sim> Q"
  and   FrR: "extractFrame R = \<langle>A\<^sub>R, \<Psi>\<^sub>R\<rangle>"
  and   "A\<^sub>R \<sharp>* \<Psi>"
  and   "A\<^sub>R \<sharp>* P"
  and   "A\<^sub>R \<sharp>* Q"

shows "\<Psi> \<rhd> P \<parallel> R \<sim> Q \<parallel> R"
proof -
  let ?X = "{(\<Psi>, \<lparr>\<nu>*xvec\<rparr>(P \<parallel> R), \<lparr>\<nu>*xvec\<rparr>(Q \<parallel> R)) | xvec \<Psi> P Q R. xvec \<sharp>* \<Psi> \<and> (\<forall>A\<^sub>R \<Psi>\<^sub>R. (extractFrame R = \<langle>A\<^sub>R, \<Psi>\<^sub>R\<rangle> \<and> A\<^sub>R \<sharp>* \<Psi> \<and> A\<^sub>R \<sharp>* P \<and> A\<^sub>R \<sharp>* Q) \<longrightarrow>
                                                                                          \<Psi> \<otimes> \<Psi>\<^sub>R \<rhd> P \<sim> Q)}"
  {
    fix xvec :: "name list"
      and \<Psi>    :: 'b
      and P    :: "('a, 'b, 'c) psi"
      and Q    :: "('a, 'b, 'c) psi"
      and R    :: "('a, 'b, 'c) psi"

    assume "xvec \<sharp>* \<Psi>"
      and  "\<And>A\<^sub>R \<Psi>\<^sub>R. \<lbrakk>extractFrame R = \<langle>A\<^sub>R, \<Psi>\<^sub>R\<rangle>; A\<^sub>R \<sharp>* \<Psi>; A\<^sub>R \<sharp>* P; A\<^sub>R \<sharp>* Q\<rbrakk> \<Longrightarrow> \<Psi> \<otimes> \<Psi>\<^sub>R \<rhd> P \<sim> Q"

    then have "(\<Psi>, \<lparr>\<nu>*xvec\<rparr>(P \<parallel> R), \<lparr>\<nu>*xvec\<rparr>(Q \<parallel> R)) \<in> ?X"
      by auto blast
  }

  note XI = this
  {
    fix xvec :: "name list"
      and \<Psi>    :: 'b
      and P    :: "('a, 'b, 'c) psi"
      and Q    :: "('a, 'b, 'c) psi"
      and R    :: "('a, 'b, 'c) psi"
      and C    :: "'d::fs_name"

    assume "xvec \<sharp>* \<Psi>"
      and  A: "\<And>A\<^sub>R \<Psi>\<^sub>R. \<lbrakk>extractFrame R = \<langle>A\<^sub>R, \<Psi>\<^sub>R\<rangle>; A\<^sub>R \<sharp>* \<Psi>; A\<^sub>R \<sharp>* P; A\<^sub>R \<sharp>* Q; A\<^sub>R \<sharp>* C\<rbrakk> \<Longrightarrow> \<Psi> \<otimes> \<Psi>\<^sub>R \<rhd> P \<sim> Q"

    from \<open>xvec \<sharp>* \<Psi>\<close> have "(\<Psi>, \<lparr>\<nu>*xvec\<rparr>(P \<parallel> R), \<lparr>\<nu>*xvec\<rparr>(Q \<parallel> R)) \<in> ?X"
    proof(rule XI)
      fix A\<^sub>R \<Psi>\<^sub>R
      assume FrR: "extractFrame R = \<langle>A\<^sub>R, \<Psi>\<^sub>R\<rangle>"
      obtain p::"name prm" where "(p \<bullet> A\<^sub>R) \<sharp>* \<Psi>" and "(p \<bullet> A\<^sub>R) \<sharp>* P" and "(p \<bullet> A\<^sub>R) \<sharp>* Q" and "(p \<bullet> A\<^sub>R) \<sharp>* R" and "(p \<bullet> A\<^sub>R) \<sharp>* C"
        and "(p \<bullet> A\<^sub>R) \<sharp>* \<Psi>\<^sub>R" and S: "(set p) \<subseteq> (set A\<^sub>R) \<times> (set(p \<bullet> A\<^sub>R))" and "distinctPerm p"
        by(rule name_list_avoiding[where c="(\<Psi>, P, Q, R, \<Psi>\<^sub>R, C)"]) auto
      from FrR \<open>(p \<bullet> A\<^sub>R) \<sharp>* \<Psi>\<^sub>R\<close> S have "extractFrame R = \<langle>(p \<bullet> A\<^sub>R), p \<bullet> \<Psi>\<^sub>R\<rangle>" by(simp add: frameChainAlpha')

      moreover assume "A\<^sub>R \<sharp>* \<Psi>"
      then have "(p \<bullet> A\<^sub>R) \<sharp>* (p \<bullet> \<Psi>)" by(simp add: pt_fresh_star_bij[OF pt_name_inst, OF at_name_inst])
      with \<open>A\<^sub>R \<sharp>* \<Psi>\<close> \<open>(p \<bullet> A\<^sub>R) \<sharp>* \<Psi>\<close> S have "(p \<bullet> A\<^sub>R) \<sharp>* \<Psi>" by simp
      moreover assume "A\<^sub>R \<sharp>* P"
      then have "(p \<bullet> A\<^sub>R) \<sharp>* (p \<bullet> P)" by(simp add: pt_fresh_star_bij[OF pt_name_inst, OF at_name_inst])
      with \<open>A\<^sub>R \<sharp>* P\<close> \<open>(p \<bullet> A\<^sub>R) \<sharp>* P\<close> S have "(p \<bullet> A\<^sub>R) \<sharp>* P" by simp
      moreover assume "A\<^sub>R \<sharp>* Q"
      then have "(p \<bullet> A\<^sub>R) \<sharp>* (p \<bullet> Q)" by(simp add: pt_fresh_star_bij[OF pt_name_inst, OF at_name_inst])
      with \<open>A\<^sub>R \<sharp>* Q\<close> \<open>(p \<bullet> A\<^sub>R) \<sharp>* Q\<close> S have "(p \<bullet> A\<^sub>R) \<sharp>* Q" by simp
      ultimately have "\<Psi> \<otimes> (p \<bullet> \<Psi>\<^sub>R) \<rhd> P \<sim> Q" using \<open>(p \<bullet> A\<^sub>R) \<sharp>* C\<close> A by blast
      then have "(p \<bullet> (\<Psi> \<otimes> (p \<bullet> \<Psi>\<^sub>R))) \<rhd> (p \<bullet> P) \<sim> (p \<bullet> Q)" by(rule bisimClosed)
      with \<open>A\<^sub>R \<sharp>* \<Psi>\<close> \<open>(p \<bullet> A\<^sub>R) \<sharp>* \<Psi>\<close> \<open>A\<^sub>R \<sharp>* P\<close> \<open>(p \<bullet> A\<^sub>R) \<sharp>* P\<close> \<open>A\<^sub>R \<sharp>* Q\<close> \<open>(p \<bullet> A\<^sub>R) \<sharp>* Q\<close> S \<open>distinctPerm p\<close>
      show "\<Psi> \<otimes> \<Psi>\<^sub>R \<rhd> P \<sim> Q" by(simp add: eqvts)
    qed
  }
  note XI' = this

  have "eqvt ?X"
    unfolding eqvt_def
  proof
    fix x
    assume "x \<in> ?X"
    then obtain xvec \<Psi> P Q R where 1: "x = (\<Psi>, \<lparr>\<nu>*xvec\<rparr>P \<parallel> R, \<lparr>\<nu>*xvec\<rparr>Q \<parallel> R)" and 2: "xvec \<sharp>* \<Psi>" and
      3: "\<forall>A\<^sub>R \<Psi>\<^sub>R. extractFrame R = \<langle>A\<^sub>R, \<Psi>\<^sub>R\<rangle> \<and> A\<^sub>R \<sharp>* \<Psi> \<and> A\<^sub>R \<sharp>* P \<and> A\<^sub>R \<sharp>* Q \<longrightarrow> \<Psi> \<otimes> \<Psi>\<^sub>R \<rhd> P \<sim> Q"
      by blast
    show "\<forall>p::(name \<times> name) list. p \<bullet> x \<in> ?X"
    proof
      fix p :: "(name \<times> name) list"
      from 1 have "p \<bullet> x = (p \<bullet> \<Psi>, \<lparr>\<nu>*p \<bullet> xvec\<rparr>(p \<bullet> P) \<parallel> (p \<bullet> R), \<lparr>\<nu>*p \<bullet> xvec\<rparr>(p \<bullet> Q) \<parallel> (p \<bullet> R))"
        by (simp add: eqvts)
      moreover from 2 have "(p \<bullet> xvec) \<sharp>* (p \<bullet> \<Psi>)"
        by (simp add: fresh_star_bij(2))
      moreover have "\<forall>A\<^sub>R \<Psi>\<^sub>R. extractFrame (p \<bullet> R) = \<langle>A\<^sub>R, \<Psi>\<^sub>R\<rangle> \<and> A\<^sub>R \<sharp>* (p \<bullet> \<Psi>) \<and> A\<^sub>R \<sharp>* (p \<bullet> P) \<and> A\<^sub>R \<sharp>* (p \<bullet> Q) \<longrightarrow> (p \<bullet> \<Psi>) \<otimes> \<Psi>\<^sub>R \<rhd> (p \<bullet> P) \<sim> (p \<bullet> Q)"
      proof (rule allI, rule allI, rule impI, (erule conjE)+)
        fix A\<^sub>R \<Psi>\<^sub>R
        assume exF: "extractFrame (p \<bullet> R) = \<langle>A\<^sub>R, \<Psi>\<^sub>R\<rangle>" and freshPsi: "A\<^sub>R \<sharp>* (p \<bullet> \<Psi>)" and freshP: "A\<^sub>R \<sharp>* (p \<bullet> P)" and freshQ: "A\<^sub>R \<sharp>* (p \<bullet> Q)"
        from exF have "extractFrame R = \<langle>rev p \<bullet> A\<^sub>R, rev p \<bullet> \<Psi>\<^sub>R\<rangle>"
          by (metis Chain.simps(5) extractFrameEqvt(1) frame.perm(1) frameResChainEqvt)
        moreover from freshPsi have "(rev p \<bullet> A\<^sub>R) \<sharp>* \<Psi>"
          by (metis fresh_star_bij(2) perm_pi_simp(1))
        moreover from freshP have "(rev p \<bullet> A\<^sub>R) \<sharp>* P"
          by (metis fresh_star_bij(2) perm_pi_simp(1))
        moreover from freshQ have "(rev p \<bullet> A\<^sub>R) \<sharp>* Q"
          by (metis fresh_star_bij(2) perm_pi_simp(1))
        ultimately show "(p \<bullet> \<Psi>) \<otimes> \<Psi>\<^sub>R \<rhd> p \<bullet> P \<sim> p \<bullet> Q"
          using 3 by (metis (no_types, opaque_lifting) bisimClosed perm_pi_simp(2) statEqvt')
      qed
      ultimately show "p \<bullet> x \<in> ?X"
        by blast
    qed
  qed

  moreover have Res: "\<And>\<Psi> P Q x. \<lbrakk>(\<Psi>, P, Q) \<in> ?X \<union> bisim; x \<sharp> \<Psi>\<rbrakk> \<Longrightarrow> (\<Psi>, \<lparr>\<nu>x\<rparr>P, \<lparr>\<nu>x\<rparr>Q) \<in> ?X \<union> bisim"
  proof -
    fix \<Psi> P Q x
    assume "(\<Psi>, P, Q) \<in> ?X \<union> bisim" and "(x::name) \<sharp> \<Psi>"
    show "(\<Psi>, \<lparr>\<nu>x\<rparr>P, \<lparr>\<nu>x\<rparr>Q) \<in> ?X \<union> bisim"
    proof(cases "(\<Psi>, P, Q) \<in> ?X")
      assume "(\<Psi>, P, Q) \<in> ?X"
      then obtain xvec P' Q' R where "P = \<lparr>\<nu>*xvec\<rparr>P' \<parallel> R" and "Q = \<lparr>\<nu>*xvec\<rparr>Q' \<parallel> R" and "xvec \<sharp>* \<Psi>"
          and "\<forall>A\<^sub>R \<Psi>\<^sub>R. extractFrame R = \<langle>A\<^sub>R, \<Psi>\<^sub>R\<rangle> \<and> A\<^sub>R \<sharp>* \<Psi> \<and> A\<^sub>R \<sharp>* P' \<and> A\<^sub>R \<sharp>* Q' \<longrightarrow> \<Psi> \<otimes> \<Psi>\<^sub>R \<rhd> P' \<sim> Q'"
        by blast
      moreover have "\<lparr>\<nu>x\<rparr>(\<lparr>\<nu>*xvec\<rparr>P' \<parallel> R) = \<lparr>\<nu>*(x # xvec)\<rparr>P' \<parallel> R"
        by simp
      moreover have "\<lparr>\<nu>x\<rparr>(\<lparr>\<nu>*xvec\<rparr>Q' \<parallel> R) = \<lparr>\<nu>*(x # xvec)\<rparr>Q' \<parallel> R"
        by simp
      moreover from \<open>x \<sharp> \<Psi>\<close> \<open>xvec \<sharp>* \<Psi>\<close> have "(x # xvec) \<sharp>* \<Psi>"
        by simp
      ultimately have "(\<Psi>, \<lparr>\<nu>x\<rparr>P, \<lparr>\<nu>x\<rparr>Q) \<in> ?X"
        by blast
      then show ?thesis by simp
    next
      assume "\<not>(\<Psi>, P, Q) \<in> ?X"
      with \<open>(\<Psi>, P, Q) \<in> ?X \<union> bisim\<close> have "\<Psi> \<rhd> P \<sim> Q"
        by blast
      then have "\<Psi> \<rhd> \<lparr>\<nu>x\<rparr>P \<sim> \<lparr>\<nu>x\<rparr>Q" using \<open>x \<sharp> \<Psi>\<close>
        by(rule bisimResPres)
      then show ?thesis
        by simp
    qed
  qed
  have ResChain: "\<And>\<Psi> P Q xvec. \<lbrakk>(\<Psi>, P, Q) \<in> ?X \<union> bisim; xvec \<sharp>* \<Psi>\<rbrakk> \<Longrightarrow> (\<Psi>, \<lparr>\<nu>*xvec\<rparr>P, \<lparr>\<nu>*xvec\<rparr>Q) \<in> ?X \<union> bisim"
  proof -
    fix \<Psi> P Q
      and xvec::"name list"
    assume "(\<Psi>, P, Q) \<in> ?X \<union> bisim"
      and "xvec \<sharp>* \<Psi>"
    then show "(\<Psi>, \<lparr>\<nu>*xvec\<rparr>P, \<lparr>\<nu>*xvec\<rparr>Q) \<in> ?X \<union> bisim"
    proof(induct xvec)
      case Nil then show ?case by simp
    next
      case(Cons x xvec)
      then have "(\<Psi>, \<lparr>\<nu>*xvec\<rparr>P, \<lparr>\<nu>*xvec\<rparr>Q) \<in> ?X \<union> bisim"
        by simp
      moreover have "x \<sharp> \<Psi>" using Cons by simp
      ultimately show ?case unfolding resChain.simps
        by(rule Res)
    qed
  qed
  have "(\<Psi>, P \<parallel> R, Q \<parallel> R) \<in> ?X"
  proof -
    {
      fix A\<^sub>R' :: "name list"
        and \<Psi>\<^sub>R' :: 'b

      assume FrR': "extractFrame R = \<langle>A\<^sub>R', \<Psi>\<^sub>R'\<rangle>"
        and  "A\<^sub>R' \<sharp>* \<Psi>"
        and  "A\<^sub>R' \<sharp>* P"
        and  "A\<^sub>R' \<sharp>* Q"

      obtain p where "(p \<bullet> A\<^sub>R') \<sharp>* A\<^sub>R" and "(p \<bullet> A\<^sub>R') \<sharp>* \<Psi>\<^sub>R'" and "(p \<bullet> A\<^sub>R') \<sharp>* \<Psi>" and "(p \<bullet> A\<^sub>R') \<sharp>* P" and "(p \<bullet> A\<^sub>R') \<sharp>* Q"
        and Sp: "(set p) \<subseteq> (set A\<^sub>R') \<times> (set(p \<bullet> A\<^sub>R'))" and "distinctPerm p"
        by(rule name_list_avoiding[where c="(A\<^sub>R, \<Psi>, \<Psi>\<^sub>R', P, Q)"]) auto

      from FrR' \<open>(p \<bullet> A\<^sub>R') \<sharp>*  \<Psi>\<^sub>R'\<close> Sp have "extractFrame R = \<langle>(p \<bullet> A\<^sub>R'), p \<bullet> \<Psi>\<^sub>R'\<rangle>"
        by(simp add: frameChainAlpha eqvts)
      with FrR \<open>(p \<bullet> A\<^sub>R') \<sharp>* A\<^sub>R\<close> obtain q::"name prm"
        where Sq: "set q \<subseteq> set(p \<bullet> A\<^sub>R') \<times> set A\<^sub>R" and "distinctPerm q" and "\<Psi>\<^sub>R = q \<bullet> p \<bullet> \<Psi>\<^sub>R'"
        by(force elim: frameChainEq)

      from \<open>\<Psi> \<otimes> \<Psi>\<^sub>R \<rhd> P \<sim> Q\<close> \<open>\<Psi>\<^sub>R = q \<bullet> p \<bullet> \<Psi>\<^sub>R'\<close> have "\<Psi> \<otimes> (q \<bullet> p \<bullet> \<Psi>\<^sub>R') \<rhd> P \<sim> Q" by simp
      then have "(q \<bullet> (\<Psi> \<otimes> (q \<bullet> p \<bullet> \<Psi>\<^sub>R'))) \<rhd> (q \<bullet> P) \<sim> (q \<bullet> Q)" by(rule bisimClosed)
      with Sq \<open>A\<^sub>R \<sharp>* \<Psi>\<close> \<open>(p \<bullet> A\<^sub>R') \<sharp>* \<Psi>\<close> \<open>A\<^sub>R \<sharp>* P\<close> \<open>(p \<bullet> A\<^sub>R') \<sharp>* P\<close> \<open>A\<^sub>R \<sharp>* Q\<close> \<open>(p \<bullet> A\<^sub>R') \<sharp>* Q\<close> \<open>distinctPerm q\<close>
      have "\<Psi> \<otimes> (p \<bullet> \<Psi>\<^sub>R') \<rhd> P \<sim> Q" by(simp add: eqvts)
      then have "(p \<bullet> (\<Psi> \<otimes> (p \<bullet> \<Psi>\<^sub>R'))) \<rhd> (p \<bullet> P) \<sim> (p \<bullet> Q)" by(rule bisimClosed)
      with Sp \<open>A\<^sub>R' \<sharp>* \<Psi>\<close> \<open>(p \<bullet> A\<^sub>R') \<sharp>* \<Psi>\<close> \<open>A\<^sub>R' \<sharp>* P\<close> \<open>(p \<bullet> A\<^sub>R') \<sharp>* P\<close> \<open>A\<^sub>R' \<sharp>* Q\<close> \<open>(p \<bullet> A\<^sub>R') \<sharp>* Q\<close> \<open>distinctPerm p\<close>
      have "\<Psi> \<otimes> \<Psi>\<^sub>R' \<rhd> P \<sim> Q" by(simp add: eqvts)
    }
    then show ?thesis
      apply clarsimp
      apply(rule exI[where x="[]"])
      by auto blast
  qed
  then show ?thesis
  proof(coinduct rule: bisimCoinduct)
    case(cStatEq \<Psi> PR QR)
    from \<open>(\<Psi>, PR, QR) \<in> ?X\<close>
    obtain xvec P Q R where PFrR: "PR = \<lparr>\<nu>*xvec\<rparr>(P \<parallel> R)" and QFrR: "QR = \<lparr>\<nu>*xvec\<rparr>(Q \<parallel> R)"
      and "xvec \<sharp>* \<Psi>" and *: "\<forall>A\<^sub>R \<Psi>\<^sub>R. extractFrame R = \<langle>A\<^sub>R, \<Psi>\<^sub>R\<rangle> \<and> A\<^sub>R \<sharp>* \<Psi> \<and> A\<^sub>R \<sharp>* P \<and> A\<^sub>R \<sharp>* Q \<longrightarrow> \<Psi> \<otimes> \<Psi>\<^sub>R \<rhd> P \<sim> Q"
      by blast
    obtain A\<^sub>R \<Psi>\<^sub>R where FrR: "extractFrame R = \<langle>A\<^sub>R, \<Psi>\<^sub>R\<rangle>" and fresh: "A\<^sub>R \<sharp>* (\<Psi>, P, Q, R)"
      using freshFrame by metis
    from fresh have "A\<^sub>R \<sharp>* \<Psi>" and "A\<^sub>R \<sharp>* P" and "A\<^sub>R \<sharp>* Q" and "A\<^sub>R \<sharp>* R"
      by auto
    with FrR have PSimQ: "\<Psi> \<otimes> \<Psi>\<^sub>R \<rhd> P \<sim> Q"
      using * by blast

    obtain A\<^sub>P \<Psi>\<^sub>P where FrP: "extractFrame P = \<langle>A\<^sub>P, \<Psi>\<^sub>P\<rangle>" and "A\<^sub>P \<sharp>* \<Psi>" and "A\<^sub>P \<sharp>* A\<^sub>R" and "A\<^sub>P \<sharp>* \<Psi>\<^sub>R"
      by(rule freshFrame[where C="(\<Psi>, A\<^sub>R, \<Psi>\<^sub>R)"]) auto
    obtain A\<^sub>Q \<Psi>\<^sub>Q where FrQ: "extractFrame Q = \<langle>A\<^sub>Q, \<Psi>\<^sub>Q\<rangle>" and "A\<^sub>Q \<sharp>* \<Psi>" and "A\<^sub>Q \<sharp>* A\<^sub>R" and "A\<^sub>Q \<sharp>* \<Psi>\<^sub>R"
      by(rule freshFrame[where C="(\<Psi>, A\<^sub>R, \<Psi>\<^sub>R)"]) auto
    from \<open>A\<^sub>R \<sharp>* P\<close> \<open>A\<^sub>R \<sharp>* Q\<close> \<open>A\<^sub>P \<sharp>* A\<^sub>R\<close> \<open>A\<^sub>Q \<sharp>* A\<^sub>R\<close> FrP FrQ have "A\<^sub>R \<sharp>* \<Psi>\<^sub>P" and  "A\<^sub>R \<sharp>* \<Psi>\<^sub>Q"
      by(force dest: extractFrameFreshChain)+

    have "\<langle>(A\<^sub>P@A\<^sub>R), \<Psi> \<otimes> \<Psi>\<^sub>P \<otimes> \<Psi>\<^sub>R\<rangle> \<simeq>\<^sub>F \<langle>(A\<^sub>Q@A\<^sub>R), \<Psi> \<otimes> \<Psi>\<^sub>Q \<otimes> \<Psi>\<^sub>R\<rangle>"
    proof -
      have "\<langle>A\<^sub>P, \<Psi> \<otimes> \<Psi>\<^sub>P \<otimes> \<Psi>\<^sub>R\<rangle> \<simeq>\<^sub>F \<langle>A\<^sub>P, (\<Psi> \<otimes> \<Psi>\<^sub>R) \<otimes> \<Psi>\<^sub>P\<rangle>"
        by(metis frameResChainPres frameNilStatEq Associativity Commutativity AssertionStatEqTrans Composition)
      moreover from PSimQ have "insertAssertion(extractFrame P) (\<Psi> \<otimes> \<Psi>\<^sub>R) \<simeq>\<^sub>F insertAssertion(extractFrame Q) (\<Psi> \<otimes> \<Psi>\<^sub>R)"
        by(rule bisimE)
      with FrP FrQ freshCompChain \<open>A\<^sub>P \<sharp>* \<Psi>\<close> \<open>A\<^sub>P \<sharp>* \<Psi>\<^sub>R\<close> \<open>A\<^sub>Q \<sharp>* \<Psi>\<close> \<open>A\<^sub>Q \<sharp>* \<Psi>\<^sub>R\<close> have "\<langle>A\<^sub>P, (\<Psi> \<otimes> \<Psi>\<^sub>R) \<otimes> \<Psi>\<^sub>P\<rangle> \<simeq>\<^sub>F \<langle>A\<^sub>Q, (\<Psi> \<otimes> \<Psi>\<^sub>R) \<otimes> \<Psi>\<^sub>Q\<rangle>"
        by auto
      moreover have "\<langle>A\<^sub>Q, (\<Psi> \<otimes> \<Psi>\<^sub>R) \<otimes> \<Psi>\<^sub>Q\<rangle> \<simeq>\<^sub>F \<langle>A\<^sub>Q, \<Psi> \<otimes> \<Psi>\<^sub>Q \<otimes> \<Psi>\<^sub>R\<rangle>"
        by(metis frameResChainPres frameNilStatEq Associativity Commutativity AssertionStatEqTrans Composition)
      ultimately have "\<langle>A\<^sub>P, \<Psi> \<otimes> \<Psi>\<^sub>P \<otimes> \<Psi>\<^sub>R\<rangle> \<simeq>\<^sub>F \<langle>A\<^sub>Q, \<Psi> \<otimes> \<Psi>\<^sub>Q \<otimes> \<Psi>\<^sub>R\<rangle>"
        by(blast intro: FrameStatEqTrans)
      then have "\<langle>(A\<^sub>R@A\<^sub>P), \<Psi> \<otimes> \<Psi>\<^sub>P \<otimes> \<Psi>\<^sub>R\<rangle> \<simeq>\<^sub>F \<langle>(A\<^sub>R@A\<^sub>Q), \<Psi> \<otimes> \<Psi>\<^sub>Q \<otimes> \<Psi>\<^sub>R\<rangle>"
        by(drule_tac frameResChainPres) (simp add: frameChainAppend)
      then show ?thesis
        apply(simp add: frameChainAppend)
        by(metis frameResChainComm FrameStatEqTrans)
    qed
    moreover from \<open>A\<^sub>P \<sharp>* \<Psi>\<close> \<open>A\<^sub>R \<sharp>* \<Psi>\<close> have "(A\<^sub>P@A\<^sub>R) \<sharp>* \<Psi>" by simp
    moreover from \<open>A\<^sub>Q \<sharp>* \<Psi>\<close> \<open>A\<^sub>R \<sharp>* \<Psi>\<close> have "(A\<^sub>Q@A\<^sub>R) \<sharp>* \<Psi>" by simp
    ultimately have PFrRQR: "insertAssertion(extractFrame(P \<parallel> R)) \<Psi> \<simeq>\<^sub>F insertAssertion(extractFrame(Q \<parallel> R)) \<Psi>"
      using FrP FrQ FrR \<open>A\<^sub>P \<sharp>* A\<^sub>R\<close> \<open>A\<^sub>P \<sharp>* \<Psi>\<^sub>R\<close> \<open>A\<^sub>Q \<sharp>* A\<^sub>R\<close> \<open>A\<^sub>Q \<sharp>* \<Psi>\<^sub>R\<close> \<open>A\<^sub>R \<sharp>* \<Psi>\<^sub>P\<close> \<open>A\<^sub>R \<sharp>* \<Psi>\<^sub>Q\<close>
      by simp

    from \<open>xvec \<sharp>* \<Psi>\<close> have "insertAssertion (extractFrame(\<lparr>\<nu>*xvec\<rparr>P \<parallel> R)) \<Psi> \<simeq>\<^sub>F \<lparr>\<nu>*xvec\<rparr>(insertAssertion (extractFrame(P \<parallel> R)) \<Psi>)"
      by(rule insertAssertionExtractFrameFresh)
    moreover from PFrRQR have "\<lparr>\<nu>*xvec\<rparr>(insertAssertion (extractFrame(P \<parallel> R)) \<Psi>) \<simeq>\<^sub>F \<lparr>\<nu>*xvec\<rparr>(insertAssertion (extractFrame(Q \<parallel> R)) \<Psi>)"
      by(induct xvec) (auto intro: frameResPres)
    moreover from \<open>xvec \<sharp>* \<Psi>\<close> have "\<lparr>\<nu>*xvec\<rparr>(insertAssertion (extractFrame(Q \<parallel> R)) \<Psi>) \<simeq>\<^sub>F insertAssertion (extractFrame(\<lparr>\<nu>*xvec\<rparr>Q \<parallel> R)) \<Psi>"
      by(rule FrameStatEqSym[OF insertAssertionExtractFrameFresh])
    ultimately show ?case using PFrR QFrR
      by(blast intro: FrameStatEqTrans)
  next
    case(cSim \<Psi> PR QR)
    {
      fix \<Psi> P Q R xvec
      assume "\<And>A\<^sub>R \<Psi>\<^sub>R. \<lbrakk>extractFrame R = \<langle>A\<^sub>R, \<Psi>\<^sub>R\<rangle>; A\<^sub>R \<sharp>* \<Psi>; A\<^sub>R \<sharp>* P; A\<^sub>R \<sharp>* Q\<rbrakk> \<Longrightarrow> \<Psi> \<otimes> \<Psi>\<^sub>R \<rhd> P \<sim> Q"
      moreover have "eqvt bisim" by simp
      moreover from \<open>eqvt ?X\<close> have "eqvt(?X \<union> bisim)" by auto
      moreover from bisimE(1) have "\<And>\<Psi> P Q. \<Psi> \<rhd> P \<sim> Q \<Longrightarrow> insertAssertion (extractFrame Q) \<Psi> \<hookrightarrow>\<^sub>F insertAssertion (extractFrame P) \<Psi>" by(simp add: FrameStatEq_def)
      moreover note bisimE(2) bisimE(3)
      moreover
      {
        fix \<Psi> P Q A\<^sub>R \<Psi>\<^sub>R R
        assume PSimQ: "\<Psi> \<otimes> \<Psi>\<^sub>R \<rhd> P \<sim> Q"
          and FrR: "extractFrame R = \<langle>A\<^sub>R, \<Psi>\<^sub>R\<rangle>"
          and "A\<^sub>R \<sharp>* \<Psi>"
          and "A\<^sub>R \<sharp>* P"
          and "A\<^sub>R \<sharp>* Q"
        then have "(\<Psi>, P \<parallel> R, Q \<parallel> R) \<in> ?X"
        proof -
          have "P \<parallel> R = \<lparr>\<nu>*[]\<rparr>(P \<parallel> R)" by simp
          moreover have "Q \<parallel> R = \<lparr>\<nu>*[]\<rparr>(Q \<parallel> R)" by simp
          moreover have "([]::name list) \<sharp>* \<Psi>" by simp
          moreover
          {
            fix A\<^sub>R' \<Psi>\<^sub>R'

            assume FrR': "extractFrame R = \<langle>A\<^sub>R', \<Psi>\<^sub>R'\<rangle>"
              and "A\<^sub>R' \<sharp>* \<Psi>"
              and "A\<^sub>R' \<sharp>* P"
              and "A\<^sub>R' \<sharp>* Q"
            obtain p where "(p \<bullet> A\<^sub>R') \<sharp>* A\<^sub>R"
              and "(p \<bullet> A\<^sub>R') \<sharp>* \<Psi>\<^sub>R'"
              and "(p \<bullet> A\<^sub>R') \<sharp>* \<Psi>"
              and "(p \<bullet> A\<^sub>R') \<sharp>* P"
              and "(p \<bullet> A\<^sub>R') \<sharp>* Q"
              and S: "(set p) \<subseteq> (set A\<^sub>R') \<times> (set(p \<bullet> A\<^sub>R'))" and "distinctPerm p"
              by(rule name_list_avoiding[where c="(A\<^sub>R, \<Psi>, \<Psi>\<^sub>R', P, Q)"]) auto

            from \<open>(p \<bullet> A\<^sub>R') \<sharp>* \<Psi>\<^sub>R'\<close> S have "\<langle>A\<^sub>R', \<Psi>\<^sub>R'\<rangle> = \<langle>p \<bullet> A\<^sub>R', p \<bullet> \<Psi>\<^sub>R'\<rangle>"
              by(simp add: frameChainAlpha)

            with FrR' have FrR'': "extractFrame R = \<langle>p \<bullet> A\<^sub>R', p \<bullet> \<Psi>\<^sub>R'\<rangle>" by simp
            with FrR \<open>(p \<bullet> A\<^sub>R') \<sharp>* A\<^sub>R\<close>
            obtain q where "p \<bullet> \<Psi>\<^sub>R' = (q::name prm) \<bullet> \<Psi>\<^sub>R" and S': "set q \<subseteq> (set A\<^sub>R) \<times> set(p \<bullet> A\<^sub>R')" and "distinctPerm q"
              apply clarsimp
              apply(drule sym)
              apply simp
              by(drule frameChainEq) auto
            from PSimQ have "(q \<bullet> (\<Psi> \<otimes> \<Psi>\<^sub>R)) \<rhd> (q \<bullet> P) \<sim> (q \<bullet> Q)"
              by(rule bisimClosed)
            with \<open>A\<^sub>R \<sharp>* \<Psi>\<close> \<open>A\<^sub>R \<sharp>* P\<close> \<open>A\<^sub>R \<sharp>* Q\<close> \<open>(p \<bullet> A\<^sub>R') \<sharp>* \<Psi>\<close> \<open>(p \<bullet> A\<^sub>R') \<sharp>* P\<close> \<open>(p \<bullet> A\<^sub>R') \<sharp>* Q\<close> S'
            have "\<Psi> \<otimes> (q \<bullet> \<Psi>\<^sub>R) \<rhd> P \<sim> Q" by(simp add: eqvts)
            then have "(p \<bullet> (\<Psi> \<otimes> (q \<bullet> \<Psi>\<^sub>R))) \<rhd> (p \<bullet> P) \<sim> (p \<bullet> Q)" by(rule bisimClosed)
            with \<open>A\<^sub>R' \<sharp>* \<Psi>\<close> \<open>A\<^sub>R' \<sharp>* P\<close> \<open>A\<^sub>R' \<sharp>* Q\<close> \<open>(p \<bullet> A\<^sub>R') \<sharp>* \<Psi>\<close> \<open>(p \<bullet> A\<^sub>R') \<sharp>* P\<close> \<open>(p \<bullet> A\<^sub>R') \<sharp>* Q\<close> S \<open>distinctPerm p\<close> \<open>(p \<bullet> \<Psi>\<^sub>R') = q \<bullet> \<Psi>\<^sub>R\<close>
            have "\<Psi> \<otimes> \<Psi>\<^sub>R' \<rhd> P \<sim> Q"
              by(drule_tac sym) (simp add: eqvts)
          }
          ultimately show ?thesis
            by blast
        qed
        then have "(\<Psi>, P \<parallel> R, Q \<parallel> R) \<in> ?X \<union> bisim"
          by simp
      }
      moreover have "\<And>\<Psi> P Q xvec. \<lbrakk>(\<Psi>, P, Q) \<in> ?X \<union> bisim; (xvec::name list) \<sharp>* \<Psi>\<rbrakk> \<Longrightarrow> (\<Psi>, \<lparr>\<nu>*xvec\<rparr>P, \<lparr>\<nu>*xvec\<rparr>Q) \<in> ?X \<union> bisim"
      proof -
        fix \<Psi> P Q xvec
        assume "(\<Psi>, P, Q) \<in> ?X \<union> bisim"
        assume "(xvec::name list) \<sharp>* \<Psi>"
        then show "(\<Psi>, \<lparr>\<nu>*xvec\<rparr>P, \<lparr>\<nu>*xvec\<rparr>Q) \<in> ?X \<union> bisim"
        proof(induct xvec)
          case Nil
          then show ?case using \<open>(\<Psi>, P, Q) \<in> ?X \<union> bisim\<close> by simp
        next
          case(Cons x xvec)
          then show ?case by(simp only: resChain.simps) (rule Res, auto)
        qed
      qed
      ultimately have "\<Psi> \<rhd> P \<parallel> R \<leadsto>[(?X \<union> bisim)] Q \<parallel> R" using statEqBisim
        by(rule parPres)
      moreover assume "(xvec::name list) \<sharp>* \<Psi>"
      moreover from \<open>eqvt ?X\<close> have "eqvt(?X \<union> bisim)" by auto
      ultimately have "\<Psi> \<rhd> \<lparr>\<nu>*xvec\<rparr>(P \<parallel> R) \<leadsto>[(?X \<union> bisim)] \<lparr>\<nu>*xvec\<rparr>(Q \<parallel> R)" using ResChain
        by(intro resChainPres)
    }
    with \<open>(\<Psi>, PR, QR) \<in> ?X\<close> show ?case by blast
  next
    case(cExt \<Psi> PR QR \<Psi>')

    from \<open>(\<Psi>, PR, QR) \<in> ?X\<close>
    obtain xvec P Q R A\<^sub>R \<Psi>\<^sub>R where PFrR: "PR = \<lparr>\<nu>*xvec\<rparr>(P \<parallel> R)" and QFrR: "QR = \<lparr>\<nu>*xvec\<rparr>(Q \<parallel> R)"
      and "xvec \<sharp>* \<Psi>" and A: "\<forall>A\<^sub>R \<Psi>\<^sub>R. (extractFrame R = \<langle>A\<^sub>R, \<Psi>\<^sub>R\<rangle> \<and> A\<^sub>R \<sharp>* \<Psi> \<and> A\<^sub>R \<sharp>* P \<and> A\<^sub>R \<sharp>* Q) \<longrightarrow> \<Psi> \<otimes> \<Psi>\<^sub>R \<rhd> P \<sim> Q"
      by auto

    obtain p where "(p \<bullet> xvec) \<sharp>* \<Psi>"
      and "(p \<bullet> xvec) \<sharp>* P"
      and "(p \<bullet> xvec) \<sharp>* Q"
      and "(p \<bullet> xvec) \<sharp>* R"
      and "(p \<bullet> xvec) \<sharp>* \<Psi>'"
      and S: "(set p) \<subseteq> (set xvec) \<times> (set(p \<bullet> xvec))" and "distinctPerm p"
      by(rule name_list_avoiding[where c="(\<Psi>, P, Q, R, \<Psi>')"]) auto

    from \<open>(p \<bullet> xvec) \<sharp>* P\<close> \<open>(p \<bullet> xvec) \<sharp>* R\<close> S have "\<lparr>\<nu>*xvec\<rparr>(P \<parallel> R) = \<lparr>\<nu>*(p \<bullet> xvec)\<rparr>(p \<bullet> (P \<parallel> R))"
      by(subst resChainAlpha) auto
    then have PRAlpha: "\<lparr>\<nu>*xvec\<rparr>(P \<parallel> R) = \<lparr>\<nu>*(p \<bullet> xvec)\<rparr>((p \<bullet> P) \<parallel> (p \<bullet> R))"
      by(simp add: eqvts)

    from \<open>(p \<bullet> xvec) \<sharp>* Q\<close> \<open>(p \<bullet> xvec) \<sharp>* R\<close> S have "\<lparr>\<nu>*xvec\<rparr>(Q \<parallel> R) = \<lparr>\<nu>*(p \<bullet> xvec)\<rparr>(p \<bullet> (Q \<parallel> R))"
      by(subst resChainAlpha) auto
    then have QRAlpha: "\<lparr>\<nu>*xvec\<rparr>(Q \<parallel> R) = \<lparr>\<nu>*(p \<bullet> xvec)\<rparr>((p \<bullet> Q) \<parallel> (p \<bullet> R))"
      by(simp add: eqvts)

    have "(\<Psi> \<otimes> \<Psi>', \<lparr>\<nu>*(p \<bullet> xvec)\<rparr>((p \<bullet> P) \<parallel> (p \<bullet> R)), \<lparr>\<nu>*(p \<bullet> xvec)\<rparr>((p \<bullet> Q) \<parallel> (p \<bullet> R))) \<in> ?X"
    proof(rule XI'[where C2="(\<Psi>, (p \<bullet> P), (p \<bullet> Q), R, \<Psi>', xvec, p \<bullet> xvec)"])
      show "(p \<bullet> xvec) \<sharp>* (\<Psi> \<otimes> \<Psi>')"
        using \<open>(p \<bullet> xvec) \<sharp>* \<Psi>\<close> \<open>(p \<bullet> xvec) \<sharp>* \<Psi>'\<close> by auto
    next
      fix A\<^sub>R \<Psi>\<^sub>R
      assume FrR: "extractFrame (p \<bullet> R) = \<langle>A\<^sub>R, \<Psi>\<^sub>R\<rangle>" and "A\<^sub>R \<sharp>* (\<Psi> \<otimes> \<Psi>')" and "A\<^sub>R \<sharp>* (p \<bullet> P)" and "A\<^sub>R \<sharp>* (\<Psi>, p \<bullet> P, p \<bullet> Q, R, \<Psi>', xvec, p \<bullet> xvec)"
      then have "A\<^sub>R \<sharp>* \<Psi>" and "A\<^sub>R \<sharp>* (p \<bullet> Q)"
        by simp_all
      from FrR have "(p \<bullet> (extractFrame (p \<bullet> R))) = (p \<bullet> \<langle>A\<^sub>R, \<Psi>\<^sub>R\<rangle>)"
        by simp
      with \<open>distinctPerm p\<close> have "extractFrame R = \<langle>p \<bullet> A\<^sub>R, p \<bullet> \<Psi>\<^sub>R\<rangle>"
        by(simp add: eqvts)
      moreover from \<open>A\<^sub>R \<sharp>* \<Psi>\<close> have "(p \<bullet> A\<^sub>R) \<sharp>* (p \<bullet> \<Psi>)"
        by(simp add: pt_fresh_star_bij[OF pt_name_inst, OF at_name_inst])
      with \<open>xvec \<sharp>* \<Psi>\<close> \<open>(p \<bullet> xvec) \<sharp>* \<Psi>\<close> S have "(p \<bullet> A\<^sub>R) \<sharp>* \<Psi>"
        by simp
      moreover from \<open>A\<^sub>R \<sharp>* (p \<bullet> P)\<close> have "(p \<bullet> A\<^sub>R) \<sharp>* (p \<bullet> p \<bullet> P)"
        by(simp add: pt_fresh_star_bij[OF pt_name_inst, OF at_name_inst])
      with \<open>distinctPerm p\<close> have "(p \<bullet> A\<^sub>R) \<sharp>* P"
        by simp
      moreover from \<open>A\<^sub>R \<sharp>* (p \<bullet> Q)\<close> have "(p \<bullet> A\<^sub>R) \<sharp>* (p \<bullet> p \<bullet> Q)"
        by(simp add: pt_fresh_star_bij[OF pt_name_inst, OF at_name_inst])
      with \<open>distinctPerm p\<close> have "(p \<bullet> A\<^sub>R) \<sharp>* Q"
        by simp
      ultimately have "\<Psi> \<otimes> (p \<bullet> \<Psi>\<^sub>R) \<rhd> P \<sim> Q"
        using A by blast
      then have "(\<Psi> \<otimes> (p \<bullet> \<Psi>\<^sub>R)) \<otimes> (p \<bullet> \<Psi>') \<rhd> P \<sim> Q"
        by(rule bisimE)
      moreover have "(\<Psi> \<otimes> (p \<bullet> \<Psi>\<^sub>R)) \<otimes> (p \<bullet> \<Psi>') \<simeq> (\<Psi> \<otimes> (p \<bullet> \<Psi>')) \<otimes> (p \<bullet> \<Psi>\<^sub>R)"
        by(metis Associativity Commutativity Composition AssertionStatEqTrans AssertionStatEqSym)
      ultimately have "(\<Psi> \<otimes> (p \<bullet> \<Psi>')) \<otimes> (p \<bullet> \<Psi>\<^sub>R) \<rhd> P \<sim> Q"
        by(rule statEqBisim)
      then have "(p \<bullet> ((\<Psi> \<otimes> (p \<bullet> \<Psi>')) \<otimes> (p \<bullet> \<Psi>\<^sub>R))) \<rhd> (p \<bullet> P) \<sim> (p \<bullet> Q)"
        by(rule bisimClosed)
      with \<open>distinctPerm p\<close> \<open>xvec \<sharp>* \<Psi>\<close> \<open>(p \<bullet> xvec) \<sharp>* \<Psi>\<close> S show "(\<Psi> \<otimes> \<Psi>') \<otimes> \<Psi>\<^sub>R \<rhd> (p \<bullet> P) \<sim> (p \<bullet> Q)"
        by(simp add: eqvts)
    qed
    with PFrR QFrR PRAlpha QRAlpha show ?case by simp
  next
    case(cSym \<Psi> PR QR)
    then show ?case by(blast dest: bisimE)
  qed
qed

lemma bisimParPres:
  fixes \<Psi> :: 'b
    and P :: "('a, 'b, 'c) psi"
    and Q :: "('a, 'b, 'c) psi"
    and R :: "('a, 'b, 'c) psi"

assumes "\<Psi> \<rhd> P \<sim> Q"

shows "\<Psi> \<rhd> P \<parallel> R \<sim> Q \<parallel> R"
proof -
  obtain A\<^sub>R \<Psi>\<^sub>R where "extractFrame R = \<langle>A\<^sub>R, \<Psi>\<^sub>R\<rangle>" and "A\<^sub>R \<sharp>* \<Psi>" and "A\<^sub>R \<sharp>* P" and "A\<^sub>R \<sharp>* Q"
    by(rule freshFrame[where C="(\<Psi>, P, Q)"]) auto
  moreover from \<open>\<Psi> \<rhd> P \<sim> Q\<close> have "\<Psi> \<otimes> \<Psi>\<^sub>R \<rhd> P \<sim> Q" by(rule bisimE)
  ultimately show ?thesis by(intro bisimParPresAux)
qed

end

end
