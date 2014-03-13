(* 
   Title: Psi-calculi   
   Author/Maintainer: Jesper Bengtson (jebe@itu.dk), 2012
*)
theory Bisim_Pres
  imports Bisimulation Sim_Pres
begin

context env begin

lemma bisimInputPres:
  fixes \<Psi>    :: 'b
  and   P    :: "('a, 'b, 'c) psi"
  and   Q    :: "('a, 'b, 'c) psi"
  and   M    :: 'a
  and   xvec :: "name list"
  and   N    :: 'a

  assumes "\<And>Tvec. length xvec = length Tvec \<Longrightarrow> \<Psi> \<rhd> P[xvec::=Tvec] \<sim> Q[xvec::=Tvec]"

  shows "\<Psi> \<rhd> M\<lparr>\<lambda>*xvec N\<rparr>.P \<sim> M\<lparr>\<lambda>*xvec N\<rparr>.Q"
proof -
  let ?X = "{(\<Psi>, M\<lparr>\<lambda>*xvec N\<rparr>.P, M\<lparr>\<lambda>*xvec N\<rparr>.Q) | \<Psi> M xvec N P Q. \<forall>Tvec. length xvec = length Tvec \<longrightarrow> \<Psi> \<rhd> P[xvec::=Tvec] \<sim> Q[xvec::=Tvec]}"

  from assms have "(\<Psi>, M\<lparr>\<lambda>*xvec N\<rparr>.P, M\<lparr>\<lambda>*xvec N\<rparr>.Q) \<in> ?X" by blast
  thus ?thesis
  proof(coinduct rule: bisimCoinduct)
    case(cStatEq \<Psi> P Q)
    thus ?case by auto
  next
    case(cSim \<Psi> P Q)
    thus ?case by(blast intro: inputPres)
  next
    case(cExt \<Psi> P Q \<Psi>')
    thus ?case by(blast dest: bisimE)
  next
    case(cSym \<Psi> P Q)
    thus ?case by(blast dest: bisimE)
  qed
qed
  
lemma bisimOutputPres:
  fixes \<Psi> :: 'b
  and   P :: "('a, 'b, 'c) psi"
  and   Q :: "('a, 'b, 'c) psi"
  and   M :: 'a
  and   N :: 'a

  assumes "\<Psi> \<rhd> P \<sim> Q"

  shows "\<Psi> \<rhd> M\<langle>N\<rangle>.P \<sim> M\<langle>N\<rangle>.Q"
proof -
  let ?X = "{(\<Psi>, M\<langle>N\<rangle>.P, M\<langle>N\<rangle>.Q) | \<Psi> M N P Q. \<Psi> \<rhd> P \<sim> Q}"
  from `\<Psi> \<rhd> P \<sim> Q` have "(\<Psi>, M\<langle>N\<rangle>.P, M\<langle>N\<rangle>.Q) \<in> ?X" by auto
  thus ?thesis
    by(coinduct rule: bisimCoinduct, auto) (blast intro: outputPres dest: bisimE)+
qed

lemma bisimCasePres:
  fixes \<Psi>   :: 'b
  and   CsP :: "('c \<times> ('a, 'b, 'c) psi) list"
  and   CsQ :: "('c \<times> ('a, 'b, 'c) psi) list"

  assumes "\<And>\<phi> P. (\<phi>, P) mem CsP \<Longrightarrow> \<exists>Q. (\<phi>, Q) mem CsQ \<and> guarded Q \<and> \<Psi> \<rhd> P \<sim> Q"
  and     "\<And>\<phi> Q. (\<phi>, Q) mem CsQ \<Longrightarrow> \<exists>P. (\<phi>, P) mem CsP \<and> guarded P \<and> \<Psi> \<rhd> P \<sim> Q"

  shows "\<Psi> \<rhd> Cases CsP \<sim> Cases CsQ"
proof -
  let ?X = "{(\<Psi>, Cases CsP, Cases CsQ) | \<Psi> CsP CsQ. (\<forall>\<phi> P. (\<phi>, P) mem CsP \<longrightarrow> (\<exists>Q. (\<phi>, Q) mem CsQ \<and> guarded Q \<and> \<Psi> \<rhd> P \<sim> Q)) \<and>
                                                     (\<forall>\<phi> Q. (\<phi>, Q) mem CsQ \<longrightarrow> (\<exists>P. (\<phi>, P) mem CsP \<and> guarded P \<and> \<Psi> \<rhd> P \<sim> Q))}"
  from assms have "(\<Psi>, Cases CsP, Cases CsQ) \<in> ?X" by auto
  thus ?thesis
  proof(coinduct rule: bisimCoinduct)
    case(cStatEq \<Psi> P Q)
    thus ?case by auto
  next
    case(cSim \<Psi> CasesP CasesQ)
    then obtain CsP CsQ where C1: "\<And>\<phi> Q. (\<phi>, Q) mem CsQ \<Longrightarrow> \<exists>P. (\<phi>, P) mem CsP \<and> guarded P \<and> \<Psi> \<rhd> P \<sim> Q"
                          and A: "CasesP = Cases CsP" and B: "CasesQ = Cases CsQ"
      by auto
    note C1
    moreover have "\<And>\<Psi> P Q. \<Psi> \<rhd> P \<sim> Q \<Longrightarrow> \<Psi> \<rhd> P \<leadsto>[bisim] Q" by(rule bisimE)
    moreover have "bisim \<subseteq> ?X \<union> bisim" by blast
    ultimately have "\<Psi> \<rhd> Cases CsP \<leadsto>[(?X \<union> bisim)] Cases CsQ"
      by(rule casePres)
    thus ?case using A B by blast
  next
    case(cExt \<Psi> P Q)
    thus ?case by(blast dest: bisimE)
  next
    case(cSym \<Psi> P Q)
    thus ?case by(blast dest: bisimE)
  qed
qed

lemma bisimResPres:
  fixes \<Psi> :: 'b
  and   P :: "('a, 'b, 'c) psi"
  and   Q :: "('a, 'b, 'c) psi"
  and   x :: name
  
  assumes "\<Psi> \<rhd> P \<sim> Q"
  and     "x \<sharp> \<Psi>"

  shows "\<Psi> \<rhd> \<lparr>\<nu>x\<rparr>P \<sim> \<lparr>\<nu>x\<rparr>Q"
proof -
  let ?X = "{(\<Psi>, \<lparr>\<nu>x\<rparr>P, \<lparr>\<nu>x\<rparr>Q) | \<Psi> x P Q. \<Psi> \<rhd> P \<sim> Q \<and> x \<sharp> \<Psi>}"
  
  from assms have "(\<Psi>, \<lparr>\<nu>x\<rparr>P, \<lparr>\<nu>x\<rparr>Q) \<in> ?X" by auto
  thus ?thesis
  proof(coinduct rule: bisimCoinduct)
    case(cStatEq \<Psi> xP xQ)
    from `(\<Psi>, xP, xQ) \<in> ?X` obtain x P Q where "\<Psi> \<rhd> P \<sim> Q" and "x \<sharp> \<Psi>" and "xP = \<lparr>\<nu>x\<rparr>P" and "xQ = \<lparr>\<nu>x\<rparr>Q"
      by auto
    moreover from `\<Psi> \<rhd> P \<sim> Q` have PeqQ: "insertAssertion(extractFrame P) \<Psi> \<simeq>\<^sub>F insertAssertion(extractFrame Q) \<Psi>"
      by(rule bisimE)
    ultimately show ?case by(auto intro: frameResPres)
  next
    case(cSim \<Psi> xP xQ)
    from `(\<Psi>, xP, xQ) \<in> ?X` obtain x P Q where "\<Psi> \<rhd> P \<sim> Q" and "x \<sharp> \<Psi>" and "xP = \<lparr>\<nu>x\<rparr>P" and "xQ = \<lparr>\<nu>x\<rparr>Q"
      by auto
    from `\<Psi> \<rhd> P \<sim> Q` have "\<Psi> \<rhd> P \<leadsto>[bisim] Q" by(rule bisimE)
    moreover have "eqvt ?X"
      by(force simp add: eqvt_def bisimClosed pt_fresh_bij[OF pt_name_inst, OF at_name_inst])
    hence "eqvt(?X \<union> bisim)" by auto
    moreover note `x \<sharp> \<Psi>`
    moreover have "bisim \<subseteq> ?X \<union> bisim" by auto
    moreover have "\<And>\<Psi> P Q x. \<lbrakk>(\<Psi>, P, Q) \<in> bisim; x \<sharp> \<Psi>\<rbrakk> \<Longrightarrow> (\<Psi>, \<lparr>\<nu>x\<rparr>P, \<lparr>\<nu>x\<rparr>Q) \<in> ?X \<union> bisim"
      by auto
    ultimately have "\<Psi> \<rhd> \<lparr>\<nu>x\<rparr>P \<leadsto>[(?X \<union> bisim)] \<lparr>\<nu>x\<rparr>Q"
      by(rule resPres)
    with `xP = \<lparr>\<nu>x\<rparr>P` `xQ = \<lparr>\<nu>x\<rparr>Q` show ?case
      by simp
  next
    case(cExt \<Psi> xP xQ \<Psi>')
    from `(\<Psi>, xP, xQ) \<in> ?X` obtain x P Q where "\<Psi> \<rhd> P \<sim> Q" and "x \<sharp> \<Psi>" and "xP = \<lparr>\<nu>x\<rparr>P" and "xQ = \<lparr>\<nu>x\<rparr>Q"
      by auto
    obtain y::name where "y \<sharp> P" and "y \<sharp> Q" and "y \<sharp> \<Psi>" and "y \<sharp> \<Psi>'"
     by(generate_fresh "name", auto simp add: fresh_prod)
   from `\<Psi> \<rhd> P \<sim> Q` have "\<Psi> \<otimes> ([(x, y)] \<bullet> \<Psi>') \<rhd> P \<sim> Q"
     by(rule bisimE)
   hence "([(x, y)] \<bullet> (\<Psi> \<otimes> ([(x, y)] \<bullet> \<Psi>'))) \<rhd> ([(x, y)] \<bullet> P) \<sim> ([(x, y)] \<bullet> Q)"
     by(rule bisimClosed)
   with `x \<sharp> \<Psi>` `y \<sharp> \<Psi>` have "\<Psi> \<otimes> \<Psi>' \<rhd> ([(x, y)] \<bullet> P) \<sim> ([(x, y)] \<bullet> Q)"
     by(simp add: eqvts)
   with `y \<sharp> \<Psi>` `y \<sharp> \<Psi>'` have "(\<Psi> \<otimes> \<Psi>', \<lparr>\<nu>y\<rparr>([(x, y)] \<bullet> P), \<lparr>\<nu>y\<rparr>([(x, y)] \<bullet> Q)) \<in> ?X"
     by auto
   moreover from `y \<sharp> P` `y \<sharp> Q` have "\<lparr>\<nu>x\<rparr>P = \<lparr>\<nu>y\<rparr>([(x, y)] \<bullet> P)" and "\<lparr>\<nu>x\<rparr>Q = \<lparr>\<nu>y\<rparr>([(x, y)] \<bullet> Q)"
     by(simp add: alphaRes)+
   ultimately show ?case using `xP = \<lparr>\<nu>x\<rparr>P` `xQ = \<lparr>\<nu>x\<rparr>Q` by simp
 next
    case(cSym \<Psi> P Q)
    thus ?case
      by(blast dest: bisimE)
  qed
qed

lemma bisimResChainPres:
  fixes \<Psi>   :: 'b
  and   P    :: "('a, 'b, 'c) psi"
  and   Q    :: "('a, 'b, 'c) psi"
  and   xvec :: "name list"

  assumes "\<Psi> \<rhd> P \<sim> Q"
  and     "xvec \<sharp>* \<Psi>"

  shows "\<Psi> \<rhd> \<lparr>\<nu>*xvec\<rparr>P \<sim> \<lparr>\<nu>*xvec\<rparr>Q"
using assms
by(induct xvec) (auto intro: bisimResPres)

lemma bisimParPresAux:
  fixes \<Psi>  :: 'b
  and   \<Psi>\<^sub>R :: 'b
  and   P  :: "('a, 'b, 'c) psi"
  and   Q  :: "('a, 'b, 'c) psi"
  and   R  :: "('a, 'b, 'c) psi"
  and   A\<^sub>R :: "name list"
  
  assumes "\<Psi> \<otimes> \<Psi>\<^sub>R \<rhd> P \<sim> Q"
  and     FrR: "extractFrame R = \<langle>A\<^sub>R, \<Psi>\<^sub>R\<rangle>"
  and     "A\<^sub>R \<sharp>* \<Psi>"
  and     "A\<^sub>R \<sharp>* P"
  and     "A\<^sub>R \<sharp>* Q"

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
    and    "\<And>A\<^sub>R \<Psi>\<^sub>R. \<lbrakk>extractFrame R = \<langle>A\<^sub>R, \<Psi>\<^sub>R\<rangle>; A\<^sub>R \<sharp>* \<Psi>; A\<^sub>R \<sharp>* P; A\<^sub>R \<sharp>* Q\<rbrakk> \<Longrightarrow> \<Psi> \<otimes> \<Psi>\<^sub>R \<rhd> P \<sim> Q"

    hence "(\<Psi>, \<lparr>\<nu>*xvec\<rparr>(P \<parallel> R), \<lparr>\<nu>*xvec\<rparr>(Q \<parallel> R)) \<in> ?X"
      apply auto
      by blast
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
    and    A: "\<And>A\<^sub>R \<Psi>\<^sub>R. \<lbrakk>extractFrame R = \<langle>A\<^sub>R, \<Psi>\<^sub>R\<rangle>; A\<^sub>R \<sharp>* \<Psi>; A\<^sub>R \<sharp>* P; A\<^sub>R \<sharp>* Q; A\<^sub>R \<sharp>* C\<rbrakk> \<Longrightarrow> \<Psi> \<otimes> \<Psi>\<^sub>R \<rhd> P \<sim> Q"

    from `xvec \<sharp>* \<Psi>` have "(\<Psi>, \<lparr>\<nu>*xvec\<rparr>(P \<parallel> R), \<lparr>\<nu>*xvec\<rparr>(Q \<parallel> R)) \<in> ?X"
    proof(rule XI)
      fix A\<^sub>R \<Psi>\<^sub>R
      assume FrR: "extractFrame R = \<langle>A\<^sub>R, \<Psi>\<^sub>R\<rangle>"
      obtain p::"name prm" where "(p \<bullet> A\<^sub>R) \<sharp>* \<Psi>" and "(p \<bullet> A\<^sub>R) \<sharp>* P" and "(p \<bullet> A\<^sub>R) \<sharp>* Q" and "(p \<bullet> A\<^sub>R) \<sharp>* R" and "(p \<bullet> A\<^sub>R) \<sharp>* C"
                             and "(p \<bullet> A\<^sub>R) \<sharp>* \<Psi>\<^sub>R" and S: "(set p) \<subseteq> (set A\<^sub>R) \<times> (set(p \<bullet> A\<^sub>R))" and "distinctPerm p"
        by(rule_tac c="(\<Psi>, P, Q, R, \<Psi>\<^sub>R, C)" in name_list_avoiding) auto
      from FrR `(p \<bullet> A\<^sub>R) \<sharp>* \<Psi>\<^sub>R` S have "extractFrame R = \<langle>(p \<bullet> A\<^sub>R), p \<bullet> \<Psi>\<^sub>R\<rangle>" by(simp add: frameChainAlpha')

      moreover assume "A\<^sub>R \<sharp>* \<Psi>"
      hence "(p \<bullet> A\<^sub>R) \<sharp>* (p \<bullet> \<Psi>)" by(simp add: pt_fresh_star_bij[OF pt_name_inst, OF at_name_inst])
      with `A\<^sub>R \<sharp>* \<Psi>` `(p \<bullet> A\<^sub>R) \<sharp>* \<Psi>` S have "(p \<bullet> A\<^sub>R) \<sharp>* \<Psi>" by simp
      moreover assume "A\<^sub>R \<sharp>* P"
      hence "(p \<bullet> A\<^sub>R) \<sharp>* (p \<bullet> P)" by(simp add: pt_fresh_star_bij[OF pt_name_inst, OF at_name_inst])
      with `A\<^sub>R \<sharp>* P` `(p \<bullet> A\<^sub>R) \<sharp>* P` S have "(p \<bullet> A\<^sub>R) \<sharp>* P" by simp
      moreover assume "A\<^sub>R \<sharp>* Q"
      hence "(p \<bullet> A\<^sub>R) \<sharp>* (p \<bullet> Q)" by(simp add: pt_fresh_star_bij[OF pt_name_inst, OF at_name_inst])
      with `A\<^sub>R \<sharp>* Q` `(p \<bullet> A\<^sub>R) \<sharp>* Q` S have "(p \<bullet> A\<^sub>R) \<sharp>* Q" by simp
      ultimately have "\<Psi> \<otimes> (p \<bullet> \<Psi>\<^sub>R) \<rhd> P \<sim> Q" using `(p \<bullet> A\<^sub>R) \<sharp>* C` A by blast
      hence "(p \<bullet> (\<Psi> \<otimes> (p \<bullet> \<Psi>\<^sub>R))) \<rhd> (p \<bullet> P) \<sim> (p \<bullet> Q)" by(rule bisimClosed)
      with `A\<^sub>R \<sharp>* \<Psi>` `(p \<bullet> A\<^sub>R) \<sharp>* \<Psi>` `A\<^sub>R \<sharp>* P` `(p \<bullet> A\<^sub>R) \<sharp>* P` `A\<^sub>R \<sharp>* Q` `(p \<bullet> A\<^sub>R) \<sharp>* Q` S `distinctPerm p`
      show "\<Psi> \<otimes> \<Psi>\<^sub>R \<rhd> P \<sim> Q" by(simp add: eqvts)
    qed
  }
  note XI' = this

  have "eqvt ?X"
    apply(auto simp add: eqvt_def)
    apply(rule_tac x="p \<bullet> xvec" in exI)
    apply(rule_tac x="p \<bullet> P" in exI)
    apply(rule_tac x="p \<bullet> Q" in exI)
    apply(rule_tac x="p \<bullet> R" in exI)
    apply(simp add: eqvts)
    apply(simp add: fresh_star_bij)
    apply(clarify)
    apply(erule_tac x="(rev p) \<bullet> A\<^sub>R" in allE)
    apply(erule_tac x="(rev p) \<bullet> \<Psi>\<^sub>R" in allE)
    apply(drule mp)
    apply(rule conjI)
    apply(rule_tac pi=p in pt_bij4[OF pt_name_inst, OF at_name_inst])
    apply(simp add: eqvts)
    defer
    apply(drule_tac p=p in bisimClosed)
    apply(simp add: eqvts)
    apply(subst pt_fresh_star_bij[OF pt_name_inst,OF at_name_inst, of p, THEN sym])
    apply simp
    apply(subst pt_fresh_star_bij[OF pt_name_inst,OF at_name_inst, of p, THEN sym])
    apply simp
    apply(subst pt_fresh_star_bij[OF pt_name_inst,OF at_name_inst, of p, THEN sym])
    by simp

  moreover have Res: "\<And>\<Psi> P Q x. \<lbrakk>(\<Psi>, P, Q) \<in> ?X \<union> bisim; x \<sharp> \<Psi>\<rbrakk> \<Longrightarrow> (\<Psi>, \<lparr>\<nu>x\<rparr>P, \<lparr>\<nu>x\<rparr>Q) \<in> ?X \<union> bisim"
  proof -
    fix \<Psi> P Q x
    assume "(\<Psi>, P, Q) \<in> ?X \<union> bisim" and "(x::name) \<sharp> \<Psi>"
    show "(\<Psi>, \<lparr>\<nu>x\<rparr>P, \<lparr>\<nu>x\<rparr>Q) \<in> ?X \<union> bisim"
    proof(case_tac "(\<Psi>, P, Q) \<in> ?X")
      assume "(\<Psi>, P, Q) \<in> ?X"
      with `x \<sharp> \<Psi>` have "(\<Psi>, \<lparr>\<nu>x\<rparr>P, \<lparr>\<nu>x\<rparr>Q) \<in> ?X"
        apply auto
        by(rule_tac x="x#xvec" in exI) auto
      thus ?thesis by simp
    next
      assume "\<not>(\<Psi>, P, Q) \<in> ?X"
      with `(\<Psi>, P, Q) \<in> ?X \<union> bisim` have "\<Psi> \<rhd> P \<sim> Q"
        by blast
      hence "\<Psi> \<rhd> \<lparr>\<nu>x\<rparr>P \<sim> \<lparr>\<nu>x\<rparr>Q" using `x \<sharp> \<Psi>`
        by(rule bisimResPres)
      thus ?thesis
        by simp
    qed
  qed

  have "(\<Psi>, P \<parallel> R, Q \<parallel> R) \<in> ?X" 
  proof -
    {
      fix A\<^sub>R' :: "name list"
      and \<Psi>\<^sub>R' :: 'b

      assume FrR': "extractFrame R = \<langle>A\<^sub>R', \<Psi>\<^sub>R'\<rangle>"
      and    "A\<^sub>R' \<sharp>* \<Psi>"
      and    "A\<^sub>R' \<sharp>* P"
      and    "A\<^sub>R' \<sharp>* Q"

      obtain p where "(p \<bullet> A\<^sub>R') \<sharp>* A\<^sub>R" and "(p \<bullet> A\<^sub>R') \<sharp>* \<Psi>\<^sub>R'" and "(p \<bullet> A\<^sub>R') \<sharp>* \<Psi>" and "(p \<bullet> A\<^sub>R') \<sharp>* P" and "(p \<bullet> A\<^sub>R') \<sharp>* Q"
                 and Sp: "(set p) \<subseteq> (set A\<^sub>R') \<times> (set(p \<bullet> A\<^sub>R'))" and "distinctPerm p"
        by(rule_tac c="(A\<^sub>R, \<Psi>, \<Psi>\<^sub>R', P, Q)" in name_list_avoiding) auto
            
      from FrR' `(p \<bullet> A\<^sub>R') \<sharp>*  \<Psi>\<^sub>R'` Sp have "extractFrame R = \<langle>(p \<bullet> A\<^sub>R'), p \<bullet> \<Psi>\<^sub>R'\<rangle>"
        by(simp add: frameChainAlpha eqvts)
      with FrR `(p \<bullet> A\<^sub>R') \<sharp>* A\<^sub>R` obtain q::"name prm" 
        where Sq: "set q \<subseteq> set(p \<bullet> A\<^sub>R') \<times> set A\<^sub>R" and "distinctPerm q" and "\<Psi>\<^sub>R = q \<bullet> p \<bullet> \<Psi>\<^sub>R'"
        by(force elim: frameChainEq)

      from `\<Psi> \<otimes> \<Psi>\<^sub>R \<rhd> P \<sim> Q` `\<Psi>\<^sub>R = q \<bullet> p \<bullet> \<Psi>\<^sub>R'` have "\<Psi> \<otimes> (q \<bullet> p \<bullet> \<Psi>\<^sub>R') \<rhd> P \<sim> Q" by simp
      hence "(q \<bullet> (\<Psi> \<otimes> (q \<bullet> p \<bullet> \<Psi>\<^sub>R'))) \<rhd> (q \<bullet> P) \<sim> (q \<bullet> Q)" by(rule bisimClosed)
      with Sq `A\<^sub>R \<sharp>* \<Psi>` `(p \<bullet> A\<^sub>R') \<sharp>* \<Psi>` `A\<^sub>R \<sharp>* P` `(p \<bullet> A\<^sub>R') \<sharp>* P` `A\<^sub>R \<sharp>* Q` `(p \<bullet> A\<^sub>R') \<sharp>* Q` `distinctPerm q`
      have "\<Psi> \<otimes> (p \<bullet> \<Psi>\<^sub>R') \<rhd> P \<sim> Q" by(simp add: eqvts)
      hence "(p \<bullet> (\<Psi> \<otimes> (p \<bullet> \<Psi>\<^sub>R'))) \<rhd> (p \<bullet> P) \<sim> (p \<bullet> Q)" by(rule bisimClosed)
      with Sp `A\<^sub>R' \<sharp>* \<Psi>` `(p \<bullet> A\<^sub>R') \<sharp>* \<Psi>` `A\<^sub>R' \<sharp>* P` `(p \<bullet> A\<^sub>R') \<sharp>* P` `A\<^sub>R' \<sharp>* Q` `(p \<bullet> A\<^sub>R') \<sharp>* Q` `distinctPerm p`
      have "\<Psi> \<otimes> \<Psi>\<^sub>R' \<rhd> P \<sim> Q" by(simp add: eqvts)
    }
    thus ?thesis
      apply auto
      apply(rule_tac x="[]" in exI)
      by auto blast
  qed
  thus ?thesis
  proof(coinduct rule: bisimCoinduct)
    case(cStatEq \<Psi> PR QR)
    from `(\<Psi>, PR, QR) \<in> ?X`
    obtain xvec P Q R A\<^sub>R \<Psi>\<^sub>R where PFrR: "PR = \<lparr>\<nu>*xvec\<rparr>(P \<parallel> R)" and QFrR: "QR = \<lparr>\<nu>*xvec\<rparr>(Q \<parallel> R)"
                              and "xvec \<sharp>* \<Psi>" and FrR: "extractFrame R = \<langle>A\<^sub>R, \<Psi>\<^sub>R\<rangle>" and PSimQ: "\<Psi> \<otimes> \<Psi>\<^sub>R \<rhd> P \<sim> Q"
                              and "A\<^sub>R \<sharp>* xvec" and "A\<^sub>R \<sharp>* \<Psi>" and "A\<^sub>R \<sharp>* P" and "A\<^sub>R \<sharp>* Q" and "A\<^sub>R \<sharp>* R"
      apply auto
      apply(subgoal_tac "\<exists>A\<^sub>R \<Psi>\<^sub>R. extractFrame R = \<langle>A\<^sub>R, \<Psi>\<^sub>R\<rangle> \<and> A\<^sub>R \<sharp>* (xvec, \<Psi>, P, Q, R)")
      apply auto
      apply(rule_tac F="extractFrame R" and C="(xvec, \<Psi>, P, Q, R)" in freshFrame)
      by auto

    obtain A\<^sub>P \<Psi>\<^sub>P where FrP: "extractFrame P = \<langle>A\<^sub>P, \<Psi>\<^sub>P\<rangle>" and "A\<^sub>P \<sharp>* \<Psi>" and "A\<^sub>P \<sharp>* A\<^sub>R" and "A\<^sub>P \<sharp>* \<Psi>\<^sub>R"
      by(rule_tac C="(\<Psi>, A\<^sub>R, \<Psi>\<^sub>R)" in freshFrame) auto
    obtain A\<^sub>Q \<Psi>\<^sub>Q where FrQ: "extractFrame Q = \<langle>A\<^sub>Q, \<Psi>\<^sub>Q\<rangle>" and "A\<^sub>Q \<sharp>* \<Psi>" and "A\<^sub>Q \<sharp>* A\<^sub>R" and "A\<^sub>Q \<sharp>* \<Psi>\<^sub>R"
      by(rule_tac C="(\<Psi>, A\<^sub>R, \<Psi>\<^sub>R)" in freshFrame) auto
    from `A\<^sub>R \<sharp>* P` `A\<^sub>R \<sharp>* Q` `A\<^sub>P \<sharp>* A\<^sub>R` `A\<^sub>Q \<sharp>* A\<^sub>R` FrP FrQ have "A\<^sub>R \<sharp>* \<Psi>\<^sub>P" and  "A\<^sub>R \<sharp>* \<Psi>\<^sub>Q"
      by(force dest: extractFrameFreshChain)+
    
    have "\<langle>(A\<^sub>P@A\<^sub>R), \<Psi> \<otimes> \<Psi>\<^sub>P \<otimes> \<Psi>\<^sub>R\<rangle> \<simeq>\<^sub>F \<langle>(A\<^sub>Q@A\<^sub>R), \<Psi> \<otimes> \<Psi>\<^sub>Q \<otimes> \<Psi>\<^sub>R\<rangle>"
    proof -
      have "\<langle>A\<^sub>P, \<Psi> \<otimes> \<Psi>\<^sub>P \<otimes> \<Psi>\<^sub>R\<rangle> \<simeq>\<^sub>F \<langle>A\<^sub>P, (\<Psi> \<otimes> \<Psi>\<^sub>R) \<otimes> \<Psi>\<^sub>P\<rangle>"
        by(metis frameResChainPres frameNilStatEq Associativity Commutativity AssertionStatEqTrans Composition)
      moreover from PSimQ have "insertAssertion(extractFrame P) (\<Psi> \<otimes> \<Psi>\<^sub>R) \<simeq>\<^sub>F insertAssertion(extractFrame Q) (\<Psi> \<otimes> \<Psi>\<^sub>R)"
        by(rule bisimE)
      with FrP FrQ freshCompChain `A\<^sub>P \<sharp>* \<Psi>` `A\<^sub>P \<sharp>* \<Psi>\<^sub>R` `A\<^sub>Q \<sharp>* \<Psi>` `A\<^sub>Q \<sharp>* \<Psi>\<^sub>R` have "\<langle>A\<^sub>P, (\<Psi> \<otimes> \<Psi>\<^sub>R) \<otimes> \<Psi>\<^sub>P\<rangle> \<simeq>\<^sub>F \<langle>A\<^sub>Q, (\<Psi> \<otimes> \<Psi>\<^sub>R) \<otimes> \<Psi>\<^sub>Q\<rangle>"
        by auto
      moreover have "\<langle>A\<^sub>Q, (\<Psi> \<otimes> \<Psi>\<^sub>R) \<otimes> \<Psi>\<^sub>Q\<rangle> \<simeq>\<^sub>F \<langle>A\<^sub>Q, \<Psi> \<otimes> \<Psi>\<^sub>Q \<otimes> \<Psi>\<^sub>R\<rangle>"
        by(metis frameResChainPres frameNilStatEq Associativity Commutativity AssertionStatEqTrans Composition)
      ultimately have "\<langle>A\<^sub>P, \<Psi> \<otimes> \<Psi>\<^sub>P \<otimes> \<Psi>\<^sub>R\<rangle> \<simeq>\<^sub>F \<langle>A\<^sub>Q, \<Psi> \<otimes> \<Psi>\<^sub>Q \<otimes> \<Psi>\<^sub>R\<rangle>"
        by(blast intro: FrameStatEqTrans)
      hence "\<langle>(A\<^sub>R@A\<^sub>P), \<Psi> \<otimes> \<Psi>\<^sub>P \<otimes> \<Psi>\<^sub>R\<rangle> \<simeq>\<^sub>F \<langle>(A\<^sub>R@A\<^sub>Q), \<Psi> \<otimes> \<Psi>\<^sub>Q \<otimes> \<Psi>\<^sub>R\<rangle>"
        by(drule_tac frameResChainPres) (simp add: frameChainAppend)
      thus ?thesis
        apply(simp add: frameChainAppend)
        by(metis frameResChainComm FrameStatEqTrans)
    qed
    moreover from `A\<^sub>P \<sharp>* \<Psi>` `A\<^sub>R \<sharp>* \<Psi>` have "(A\<^sub>P@A\<^sub>R) \<sharp>* \<Psi>" by simp
    moreover from `A\<^sub>Q \<sharp>* \<Psi>` `A\<^sub>R \<sharp>* \<Psi>` have "(A\<^sub>Q@A\<^sub>R) \<sharp>* \<Psi>" by simp
    ultimately have PFrRQR: "insertAssertion(extractFrame(P \<parallel> R)) \<Psi> \<simeq>\<^sub>F insertAssertion(extractFrame(Q \<parallel> R)) \<Psi>"
      using FrP FrQ FrR `A\<^sub>P \<sharp>* A\<^sub>R` `A\<^sub>P \<sharp>* \<Psi>\<^sub>R` `A\<^sub>Q \<sharp>* A\<^sub>R` `A\<^sub>Q \<sharp>* \<Psi>\<^sub>R` `A\<^sub>R \<sharp>* \<Psi>\<^sub>P` `A\<^sub>R \<sharp>* \<Psi>\<^sub>Q`
      by simp
      
    from `xvec \<sharp>* \<Psi>` have "insertAssertion (extractFrame(\<lparr>\<nu>*xvec\<rparr>P \<parallel> R)) \<Psi> \<simeq>\<^sub>F \<lparr>\<nu>*xvec\<rparr>(insertAssertion (extractFrame(P \<parallel> R)) \<Psi>)"
      by(rule insertAssertionExtractFrameFresh)
    moreover from PFrRQR have "\<lparr>\<nu>*xvec\<rparr>(insertAssertion (extractFrame(P \<parallel> R)) \<Psi>) \<simeq>\<^sub>F \<lparr>\<nu>*xvec\<rparr>(insertAssertion (extractFrame(Q \<parallel> R)) \<Psi>)"
      by(induct xvec) (auto intro: frameResPres)
    moreover from `xvec \<sharp>* \<Psi>` have "\<lparr>\<nu>*xvec\<rparr>(insertAssertion (extractFrame(Q \<parallel> R)) \<Psi>) \<simeq>\<^sub>F insertAssertion (extractFrame(\<lparr>\<nu>*xvec\<rparr>Q \<parallel> R)) \<Psi>"
      by(rule FrameStatEqSym[OF insertAssertionExtractFrameFresh])
    ultimately show ?case using PFrR QFrR
      by(blast intro: FrameStatEqTrans)
  next
    case(cSim \<Psi> PR QR)
    {
      fix \<Psi> P Q R xvec
      assume "\<And>A\<^sub>R \<Psi>\<^sub>R. \<lbrakk>extractFrame R = \<langle>A\<^sub>R, \<Psi>\<^sub>R\<rangle>; A\<^sub>R \<sharp>* \<Psi>; A\<^sub>R \<sharp>* P; A\<^sub>R \<sharp>* Q\<rbrakk> \<Longrightarrow> \<Psi> \<otimes> \<Psi>\<^sub>R \<rhd> P \<sim> Q"
      moreover have "eqvt bisim" by simp
      moreover from `eqvt ?X` have "eqvt(?X \<union> bisim)" by auto
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
        hence "(\<Psi>, P \<parallel> R, Q \<parallel> R) \<in> ?X"
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
              by(rule_tac c="(A\<^sub>R, \<Psi>, \<Psi>\<^sub>R', P, Q)" in name_list_avoiding) auto


            from `(p \<bullet> A\<^sub>R') \<sharp>* \<Psi>\<^sub>R'` S have "\<langle>A\<^sub>R', \<Psi>\<^sub>R'\<rangle> = \<langle>p \<bullet> A\<^sub>R', p \<bullet> \<Psi>\<^sub>R'\<rangle>"
              by(simp add: frameChainAlpha)

            with FrR' have FrR'': "extractFrame R = \<langle>p \<bullet> A\<^sub>R', p \<bullet> \<Psi>\<^sub>R'\<rangle>" by simp
            with FrR `(p \<bullet> A\<^sub>R') \<sharp>* A\<^sub>R`
            obtain q where "p \<bullet> \<Psi>\<^sub>R' = (q::name prm) \<bullet> \<Psi>\<^sub>R" and S': "set q \<subseteq> (set A\<^sub>R) \<times> set(p \<bullet> A\<^sub>R')" and "distinctPerm q"
              apply auto
              apply(drule_tac sym) apply simp
              by(drule_tac frameChainEq) auto
            from PSimQ have "(q \<bullet> (\<Psi> \<otimes> \<Psi>\<^sub>R)) \<rhd> (q \<bullet> P) \<sim> (q \<bullet> Q)"
              by(rule bisimClosed)
            with `A\<^sub>R \<sharp>* \<Psi>` `A\<^sub>R \<sharp>* P` `A\<^sub>R \<sharp>* Q` `(p \<bullet> A\<^sub>R') \<sharp>* \<Psi>` `(p \<bullet> A\<^sub>R') \<sharp>* P` `(p \<bullet> A\<^sub>R') \<sharp>* Q` S'
            have "\<Psi> \<otimes> (q \<bullet> \<Psi>\<^sub>R) \<rhd> P \<sim> Q" by(simp add: eqvts)
            hence "(p \<bullet> (\<Psi> \<otimes> (q \<bullet> \<Psi>\<^sub>R))) \<rhd> (p \<bullet> P) \<sim> (p \<bullet> Q)" by(rule bisimClosed)
            with `A\<^sub>R' \<sharp>* \<Psi>` `A\<^sub>R' \<sharp>* P` `A\<^sub>R' \<sharp>* Q` `(p \<bullet> A\<^sub>R') \<sharp>* \<Psi>` `(p \<bullet> A\<^sub>R') \<sharp>* P` `(p \<bullet> A\<^sub>R') \<sharp>* Q` S `distinctPerm p` `(p \<bullet> \<Psi>\<^sub>R') = q \<bullet> \<Psi>\<^sub>R` 
            have "\<Psi> \<otimes> \<Psi>\<^sub>R' \<rhd> P \<sim> Q"
              by(drule_tac sym) (simp add: eqvts)
          }
          ultimately show ?thesis
            by blast
        qed
        hence "(\<Psi>, P \<parallel> R, Q \<parallel> R) \<in> ?X \<union> bisim"
          by simp
      }
      moreover have "\<And>\<Psi> P Q xvec. \<lbrakk>(\<Psi>, P, Q) \<in> ?X \<union> bisim; (xvec::name list) \<sharp>* \<Psi>\<rbrakk> \<Longrightarrow> (\<Psi>, \<lparr>\<nu>*xvec\<rparr>P, \<lparr>\<nu>*xvec\<rparr>Q) \<in> ?X \<union> bisim"
      proof -
        fix \<Psi> P Q xvec
        assume "(\<Psi>, P, Q) \<in> ?X \<union> bisim"
        assume "(xvec::name list) \<sharp>* \<Psi>"
        thus "(\<Psi>, \<lparr>\<nu>*xvec\<rparr>P, \<lparr>\<nu>*xvec\<rparr>Q) \<in> ?X \<union> bisim"
        proof(induct xvec)
          case Nil
          thus ?case using `(\<Psi>, P, Q) \<in> ?X \<union> bisim` by simp
        next
          case(Cons x xvec)
          thus ?case by(simp only: resChain.simps) (rule_tac Res, auto)
        qed
      qed
      ultimately have "\<Psi> \<rhd> P \<parallel> R \<leadsto>[(?X \<union> bisim)] Q \<parallel> R" using statEqBisim
        by(rule parPres)
      moreover assume "(xvec::name list) \<sharp>* \<Psi>"
      moreover from `eqvt ?X` have "eqvt(?X \<union> bisim)" by auto
      ultimately have "\<Psi> \<rhd> \<lparr>\<nu>*xvec\<rparr>(P \<parallel> R) \<leadsto>[(?X \<union> bisim)] \<lparr>\<nu>*xvec\<rparr>(Q \<parallel> R)" using Res
        by(rule_tac resChainPres)
    }
    with `(\<Psi>, PR, QR) \<in> ?X` show ?case by blast
  next
    case(cExt \<Psi> PR QR \<Psi>')

    from `(\<Psi>, PR, QR) \<in> ?X`
    obtain xvec P Q R A\<^sub>R \<Psi>\<^sub>R where PFrR: "PR = \<lparr>\<nu>*xvec\<rparr>(P \<parallel> R)" and QFrR: "QR = \<lparr>\<nu>*xvec\<rparr>(Q \<parallel> R)"
                               and "xvec \<sharp>* \<Psi>" and A: "\<forall>A\<^sub>R \<Psi>\<^sub>R. (extractFrame R = \<langle>A\<^sub>R, \<Psi>\<^sub>R\<rangle> \<and> A\<^sub>R \<sharp>* \<Psi> \<and> A\<^sub>R \<sharp>* P \<and> A\<^sub>R \<sharp>* Q) \<longrightarrow> \<Psi> \<otimes> \<Psi>\<^sub>R \<rhd> P \<sim> Q"
      by auto
    
    obtain p where "(p \<bullet> xvec) \<sharp>* \<Psi>"
               and "(p \<bullet> xvec) \<sharp>* P"
               and "(p \<bullet> xvec) \<sharp>* Q"
               and "(p \<bullet> xvec) \<sharp>* R"
               and "(p \<bullet> xvec) \<sharp>* \<Psi>'"
               and S: "(set p) \<subseteq> (set xvec) \<times> (set(p \<bullet> xvec))" and "distinctPerm p"
      by(rule_tac c="(\<Psi>, P, Q, R, \<Psi>')" in name_list_avoiding) auto

    from `(p \<bullet> xvec) \<sharp>* P` `(p \<bullet> xvec) \<sharp>* R` S have "\<lparr>\<nu>*xvec\<rparr>(P \<parallel> R) = \<lparr>\<nu>*(p \<bullet> xvec)\<rparr>(p \<bullet> (P \<parallel> R))"
      by(subst resChainAlpha) auto
    hence PRAlpha: "\<lparr>\<nu>*xvec\<rparr>(P \<parallel> R) = \<lparr>\<nu>*(p \<bullet> xvec)\<rparr>((p \<bullet> P) \<parallel> (p \<bullet> R))"
      by(simp add: eqvts)

    from `(p \<bullet> xvec) \<sharp>* Q` `(p \<bullet> xvec) \<sharp>* R` S have "\<lparr>\<nu>*xvec\<rparr>(Q \<parallel> R) = \<lparr>\<nu>*(p \<bullet> xvec)\<rparr>(p \<bullet> (Q \<parallel> R))"
      by(subst resChainAlpha) auto
    hence QRAlpha: "\<lparr>\<nu>*xvec\<rparr>(Q \<parallel> R) = \<lparr>\<nu>*(p \<bullet> xvec)\<rparr>((p \<bullet> Q) \<parallel> (p \<bullet> R))"
      by(simp add: eqvts)

    from `(p \<bullet> xvec) \<sharp>* \<Psi>` `(p \<bullet> xvec) \<sharp>* \<Psi>'` have "(\<Psi> \<otimes> \<Psi>', \<lparr>\<nu>*(p \<bullet> xvec)\<rparr>((p \<bullet> P) \<parallel> (p \<bullet> R)), \<lparr>\<nu>*(p \<bullet> xvec)\<rparr>((p \<bullet> Q) \<parallel> (p \<bullet> R))) \<in> ?X"
    proof(rule_tac C2="(\<Psi>, (p \<bullet> P), (p \<bullet> Q), R, \<Psi>', xvec, p \<bullet> xvec)" in XI', auto)
      fix A\<^sub>R \<Psi>\<^sub>R
      assume FrR: "extractFrame (p \<bullet> R) = \<langle>A\<^sub>R, \<Psi>\<^sub>R\<rangle>" and "A\<^sub>R \<sharp>* \<Psi>" and "A\<^sub>R \<sharp>* \<Psi>'" and "A\<^sub>R \<sharp>* (p \<bullet> P)" and "A\<^sub>R \<sharp>* (p \<bullet> Q)"
      from FrR have "(p \<bullet> (extractFrame (p \<bullet> R))) = (p \<bullet> \<langle>A\<^sub>R, \<Psi>\<^sub>R\<rangle>)" by simp
      with `distinctPerm p` have "extractFrame R = \<langle>p \<bullet> A\<^sub>R, p \<bullet> \<Psi>\<^sub>R\<rangle>" by(simp add: eqvts)
      moreover from `A\<^sub>R \<sharp>* \<Psi>` have "(p \<bullet> A\<^sub>R) \<sharp>* (p \<bullet> \<Psi>)" by(simp add: pt_fresh_star_bij[OF pt_name_inst, OF at_name_inst])
      with `xvec \<sharp>* \<Psi>` `(p \<bullet> xvec) \<sharp>* \<Psi>` S have "(p \<bullet> A\<^sub>R) \<sharp>* \<Psi>" by simp
      moreover from `A\<^sub>R \<sharp>* (p \<bullet> P)` have "(p \<bullet> A\<^sub>R) \<sharp>* (p \<bullet> p \<bullet> P)" by(simp add: pt_fresh_star_bij[OF pt_name_inst, OF at_name_inst])
      with `distinctPerm p` have "(p \<bullet> A\<^sub>R) \<sharp>* P" by simp
      moreover from `A\<^sub>R \<sharp>* (p \<bullet> Q)` have "(p \<bullet> A\<^sub>R) \<sharp>* (p \<bullet> p \<bullet> Q)" by(simp add: pt_fresh_star_bij[OF pt_name_inst, OF at_name_inst])
      with `distinctPerm p` have "(p \<bullet> A\<^sub>R) \<sharp>* Q" by simp
      ultimately have "\<Psi> \<otimes> (p \<bullet> \<Psi>\<^sub>R) \<rhd> P \<sim> Q" using A by blast
      hence "(\<Psi> \<otimes> (p \<bullet> \<Psi>\<^sub>R)) \<otimes> (p \<bullet> \<Psi>') \<rhd> P \<sim> Q" by(rule bisimE)
      moreover have "(\<Psi> \<otimes> (p \<bullet> \<Psi>\<^sub>R)) \<otimes> (p \<bullet> \<Psi>') \<simeq> (\<Psi> \<otimes> (p \<bullet> \<Psi>')) \<otimes> (p \<bullet> \<Psi>\<^sub>R)"
        by(metis Associativity Commutativity Composition AssertionStatEqTrans AssertionStatEqSym)
      ultimately have "(\<Psi> \<otimes> (p \<bullet> \<Psi>')) \<otimes> (p \<bullet> \<Psi>\<^sub>R) \<rhd> P \<sim> Q" 
        by(rule statEqBisim)
      hence "(p \<bullet> ((\<Psi> \<otimes> (p \<bullet> \<Psi>')) \<otimes> (p \<bullet> \<Psi>\<^sub>R))) \<rhd> (p \<bullet> P) \<sim> (p \<bullet> Q)"
        by(rule bisimClosed)
      with `distinctPerm p` `xvec \<sharp>* \<Psi>` `(p \<bullet> xvec) \<sharp>* \<Psi>` S show "(\<Psi> \<otimes> \<Psi>') \<otimes> \<Psi>\<^sub>R \<rhd> (p \<bullet> P) \<sim> (p \<bullet> Q)"
        by(simp add: eqvts)
    qed
    with PFrR QFrR PRAlpha QRAlpha show ?case by simp
  next
    case(cSym \<Psi> PR QR)
    thus ?case by(blast dest: bisimE)
  qed
qed

lemma bisimParPres:
  fixes \<Psi> :: 'b
  and   P :: "('a, 'b, 'c) psi"
  and   Q :: "('a, 'b, 'c) psi"
  and   R :: "('a, 'b, 'c) psi"
  
  assumes "\<Psi> \<rhd> P \<sim> Q"

  shows "\<Psi> \<rhd> P \<parallel> R \<sim> Q \<parallel> R"
proof -
  obtain A\<^sub>R \<Psi>\<^sub>R where "extractFrame R = \<langle>A\<^sub>R, \<Psi>\<^sub>R\<rangle>" and "A\<^sub>R \<sharp>* \<Psi>" and "A\<^sub>R \<sharp>* P" and "A\<^sub>R \<sharp>* Q"
    by(rule_tac C="(\<Psi>, P, Q)" in freshFrame) auto
  moreover from `\<Psi> \<rhd> P \<sim> Q` have "\<Psi> \<otimes> \<Psi>\<^sub>R \<rhd> P \<sim> Q" by(rule bisimE)
  ultimately show ?thesis by(rule_tac bisimParPresAux)
qed

end

end

