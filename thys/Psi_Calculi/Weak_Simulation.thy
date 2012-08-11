(* 
   Title: Psi-calculi   
   Author/Maintainer: Jesper Bengtson (jebe@itu.dk), 2012
*)
theory Weak_Simulation
  imports Simulation Tau_Chain
begin

context env begin

definition
  "weakSimulation" :: "'b \<Rightarrow> ('a, 'b, 'c) psi \<Rightarrow>
                       ('b \<times> ('a, 'b, 'c) psi \<times> ('a, 'b, 'c) psi) set \<Rightarrow> 
                       ('a, 'b, 'c) psi \<Rightarrow> bool" ("_ \<rhd> _ \<leadsto><_> _" [80, 80, 80, 80] 80)
where
  "\<Psi> \<rhd> P \<leadsto><Rel> Q \<equiv> (\<forall>\<Psi>' \<alpha> Q'. \<Psi> \<rhd> Q \<longmapsto>\<alpha> \<prec> Q' \<longrightarrow> bn \<alpha> \<sharp>* \<Psi> \<longrightarrow> bn \<alpha> \<sharp>* P \<longrightarrow> \<alpha> \<noteq> \<tau> \<longrightarrow>
                      (\<exists>P''. \<Psi> : Q \<rhd> P \<Longrightarrow>\<alpha> \<prec> P'' \<and> (\<exists>P'. \<Psi> \<otimes> \<Psi>' \<rhd> P'' \<Longrightarrow>\<^sup>^\<^sub>\<tau> P' \<and> (\<Psi> \<otimes> \<Psi>', P', Q') \<in> Rel))) \<and> 
                      (\<forall>Q'. \<Psi> \<rhd> Q \<longmapsto>\<tau> \<prec> Q' \<longrightarrow> (\<exists>P'. \<Psi> \<rhd> P \<Longrightarrow>\<^sup>^\<^sub>\<tau> P' \<and> (\<Psi>, P', Q') \<in> Rel))"

abbreviation
  weakSimulationNilJudge ("_ \<leadsto><_> _" [80, 80, 80] 80) where "P \<leadsto><Rel> Q \<equiv> SBottom' \<rhd> P \<leadsto><Rel> Q"

lemma weakSimI[consumes 1, case_names cAct cTau]:
  fixes \<Psi>   :: 'b
  and   P   :: "('a, 'b, 'c) psi"
  and   Rel :: "('b \<times> ('a, 'b, 'c) psi \<times> ('a, 'b, 'c) psi) set"
  and   Q   :: "('a, 'b, 'c) psi"
  and   C   :: "'d::fs_name"

  assumes Eqvt: "eqvt Rel"
  and     rAct: "\<And>\<Psi>' \<alpha> Q'. \<lbrakk>\<Psi> \<rhd> Q \<longmapsto>\<alpha> \<prec> Q';  bn \<alpha> \<sharp>* \<Psi>; bn \<alpha> \<sharp>* P; bn \<alpha> \<sharp>* Q;
                              bn \<alpha> \<sharp>* subject \<alpha>; bn \<alpha> \<sharp>* C; distinct(bn \<alpha>); \<alpha> \<noteq> \<tau>\<rbrakk> \<Longrightarrow>
                                         
                              \<exists>P''. \<Psi> : Q \<rhd> P \<Longrightarrow>\<alpha> \<prec> P'' \<and> (\<exists>P'. \<Psi> \<otimes> \<Psi>' \<rhd> P'' \<Longrightarrow>\<^sup>^\<^sub>\<tau> P' \<and> (\<Psi> \<otimes> \<Psi>', P', Q') \<in> Rel)"
  and     rTau:  "\<And>Q'. \<Psi> \<rhd> Q \<longmapsto>\<tau> \<prec> Q' \<Longrightarrow> \<exists>P'. \<Psi> \<rhd> P \<Longrightarrow>\<^sup>^\<^sub>\<tau> P' \<and> (\<Psi>, P', Q') \<in> Rel"

  shows "\<Psi> \<rhd> P \<leadsto><Rel> Q"
proof(auto simp add: weakSimulation_def)
  fix \<Psi>' \<alpha> Q'
  assume "\<Psi> \<rhd> Q \<longmapsto>\<alpha> \<prec> Q'" and "bn \<alpha> \<sharp>* \<Psi>" and "bn \<alpha> \<sharp>* P" and "\<alpha> \<noteq> \<tau>"
  thus "\<exists>P''. \<Psi> : Q \<rhd> P \<Longrightarrow>\<alpha> \<prec> P'' \<and> (\<exists>P'. \<Psi> \<otimes> \<Psi>' \<rhd> P'' \<Longrightarrow>\<^sup>^\<^sub>\<tau> P' \<and> (\<Psi> \<otimes> \<Psi>', P', Q') \<in> Rel)"
  proof(nominal_induct \<alpha> rule: action.strong_induct)
    case(In M N)
    thus ?case by(rule_tac rAct) auto
  next
    case(Out M xvec N)
    from `bn(M\<lparr>\<nu>*xvec\<rparr>\<langle>N\<rangle>) \<sharp>* \<Psi>` `bn(M\<lparr>\<nu>*xvec\<rparr>\<langle>N\<rangle>) \<sharp>* P` have "xvec \<sharp>* \<Psi>" and "xvec \<sharp>* P" by simp+
    from `\<Psi> \<rhd> Q \<longmapsto>M\<lparr>\<nu>*xvec\<rparr>\<langle>N\<rangle> \<prec> Q'` have "distinct xvec" by(force dest: boundOutputDistinct)
    obtain p where "(p \<bullet> xvec) \<sharp>* \<Psi>" and "(p \<bullet> xvec) \<sharp>* M" and "(p \<bullet> xvec) \<sharp>* xvec"
               and"(p \<bullet> xvec) \<sharp>* P" and "(p \<bullet> xvec) \<sharp>* Q" and "(p \<bullet> xvec) \<sharp>* Q'" and "(p \<bullet> xvec) \<sharp>* \<Psi>'"
               and "(p \<bullet> xvec) \<sharp>* C" and "(p \<bullet> xvec) \<sharp>* xvec" and "(p \<bullet> xvec) \<sharp>* N"
               and S: "(set p) \<subseteq> (set xvec) \<times> (set(p \<bullet> xvec))" and "distinctPerm p"
      by(rule_tac xvec=xvec and c="(\<Psi>, M, Q, N, P, Q', xvec, C, \<Psi>')" in name_list_avoiding)
        (auto simp add: eqvts fresh_star_prod)
    from `distinct xvec` have "distinct(p \<bullet> xvec)" by simp
    from `\<Psi> \<rhd> Q \<longmapsto>M\<lparr>\<nu>*xvec\<rparr>\<langle>N\<rangle> \<prec> Q'` `(p \<bullet> xvec) \<sharp>* N` `(p \<bullet> xvec) \<sharp>* Q'` S 
    have "\<Psi> \<rhd> Q \<longmapsto>M\<lparr>\<nu>*(p \<bullet> xvec)\<rparr>\<langle>(p \<bullet> N)\<rangle> \<prec> (p \<bullet> Q')" by(simp add: boundOutputChainAlpha'' residualInject)

    then obtain P'' P' where PTrans: "\<Psi> : Q \<rhd> P \<Longrightarrow>M\<lparr>\<nu>*(p \<bullet> xvec)\<rparr>\<langle>(p \<bullet> N)\<rangle> \<prec> P''" 
                         and P''Chain: "\<Psi> \<otimes> (p \<bullet> \<Psi>') \<rhd> P'' \<Longrightarrow>\<^sup>^\<^sub>\<tau> P'"
                         and P'RelQ': "(\<Psi> \<otimes> (p \<bullet> \<Psi>'), P', p \<bullet> Q') \<in> Rel"
      using `(p \<bullet> xvec) \<sharp>* \<Psi>` `(p \<bullet> xvec) \<sharp>* P` `(p \<bullet> xvec) \<sharp>* Q` `(p \<bullet> xvec) \<sharp>* M` `(p \<bullet> xvec) \<sharp>* C` `distinct(p \<bullet> xvec)`
      by(drule_tac \<Psi>'="p \<bullet> \<Psi>'" in rAct) auto

    from PTrans S `distinctPerm p` `xvec \<sharp>* P` `(p \<bullet> xvec) \<sharp>* xvec` `(p \<bullet> xvec) \<sharp>* M` `distinct xvec` 
    have "\<Psi> : Q \<rhd> P \<Longrightarrow>M\<lparr>\<nu>*xvec\<rparr>\<langle>N\<rangle> \<prec> (p \<bullet> P'')" 
      by(rule_tac weakOutputAlpha) auto
    moreover from P''Chain have "(p \<bullet> (\<Psi> \<otimes> (p \<bullet> \<Psi>'))) \<rhd> (p \<bullet> P'') \<Longrightarrow>\<^sup>^\<^sub>\<tau> (p \<bullet> P')" by(rule eqvts)
    with `xvec \<sharp>* \<Psi>` `(p \<bullet> xvec) \<sharp>* \<Psi>` `(p \<bullet> xvec) \<sharp>* \<Psi>'` S `distinctPerm p`
    have "\<Psi> \<otimes> \<Psi>' \<rhd> (p \<bullet> P'') \<Longrightarrow>\<^sup>^\<^sub>\<tau> (p \<bullet> P')" by(simp add: eqvts)
    moreover from P'RelQ' Eqvt S `distinctPerm p` have "(p \<bullet> (\<Psi> \<otimes> (p \<bullet> \<Psi>')), p \<bullet> P', p \<bullet> p \<bullet> Q') \<in> Rel"
      apply(simp add: eqvt_def eqvts)
      apply(erule_tac x="(\<Psi> \<otimes> (p \<bullet> \<Psi>'), P', p \<bullet> Q')" in ballE)
      apply(erule_tac x="p" in allE)
      by(auto simp add: eqvts)
    with `xvec \<sharp>* \<Psi>` `(p \<bullet> xvec) \<sharp>* \<Psi>` S `distinctPerm p`
    have "(\<Psi> \<otimes> \<Psi>', p \<bullet> P', Q') \<in> Rel" by(simp add: eqvts)
    ultimately show ?case by blast
  next
    case Tau
    thus ?case by simp
  qed
next
  fix Q'
  assume "\<Psi> \<rhd> Q \<longmapsto>\<tau> \<prec> Q'"
  thus "\<exists>P'. \<Psi> \<rhd> P \<Longrightarrow>\<^sup>^\<^sub>\<tau> P' \<and> (\<Psi>, P', Q') \<in> Rel"
    by(rule rTau)
qed

lemma weakSimI2[case_names cAct cTau]:
  fixes \<Psi>   :: 'b
  and   P   :: "('a, 'b, 'c) psi"
  and   Rel :: "('b \<times> ('a, 'b, 'c) psi \<times> ('a, 'b, 'c) psi) set"
  and   Q   :: "('a, 'b, 'c) psi"
  and   C   :: "'d::fs_name"

  assumes rOutput: "\<And>\<Psi>' \<alpha> Q'. \<lbrakk>\<Psi> \<rhd> Q \<longmapsto>\<alpha> \<prec> Q';  bn \<alpha> \<sharp>* \<Psi>; bn \<alpha> \<sharp>* P; \<alpha> \<noteq> \<tau>\<rbrakk> \<Longrightarrow>
                                \<exists>P''. \<Psi> : Q \<rhd> P \<Longrightarrow>\<alpha> \<prec> P'' \<and> (\<exists>P'. \<Psi> \<otimes> \<Psi>' \<rhd> P'' \<Longrightarrow>\<^sup>^\<^sub>\<tau> P' \<and> (\<Psi> \<otimes> \<Psi>', P', Q') \<in> Rel)"
  and     rTau:  "\<And>Q'. \<Psi> \<rhd> Q \<longmapsto>\<tau> \<prec> Q' \<Longrightarrow> \<exists>P'. \<Psi> \<rhd> P \<Longrightarrow>\<^sup>^\<^sub>\<tau> P' \<and> (\<Psi>, P', Q') \<in> Rel"

  shows "\<Psi> \<rhd> P \<leadsto><Rel> Q"
using assms by(simp add: weakSimulation_def)

lemma weakSimIChainFresh[consumes 4, case_names cOutput cInput]:
  fixes \<Psi>    :: 'b
  and   P    :: "('a, 'b, 'c) psi"
  and   Rel  :: "('b \<times> ('a, 'b, 'c) psi \<times> ('a, 'b, 'c) psi) set"
  and   Q    :: "('a, 'b, 'c) psi"
  and   yvec :: "name list"
  and   C    :: "'d::fs_name"

  assumes Eqvt: "eqvt Rel"
  and     "yvec \<sharp>* \<Psi>"
  and     "yvec \<sharp>* P"
  and     "yvec \<sharp>* Q"
  and     rAct: "\<And>\<Psi>' \<alpha> Q'. \<lbrakk>\<Psi> \<rhd> Q \<longmapsto>\<alpha> \<prec> Q'; bn \<alpha> \<sharp>* \<Psi>; bn \<alpha> \<sharp>* P; bn \<alpha> \<sharp>* Q; \<alpha> \<noteq> \<tau>;
                             bn \<alpha> \<sharp>* subject \<alpha>; bn \<alpha> \<sharp>* C; yvec \<sharp>* \<alpha>; yvec \<sharp>* Q'; yvec \<sharp>* \<Psi>'\<rbrakk> \<Longrightarrow>
                             \<exists>P''. \<Psi> : Q \<rhd> P \<Longrightarrow>\<alpha> \<prec> P'' \<and> (\<exists>P'. \<Psi> \<otimes> \<Psi>' \<rhd> P'' \<Longrightarrow>\<^sup>^\<^sub>\<tau> P' \<and> (\<Psi> \<otimes> \<Psi>', P', Q') \<in> Rel)"
  and     rTau: "\<And>Q'. \<lbrakk>\<Psi> \<rhd> Q \<longmapsto>\<tau> \<prec> Q'; yvec \<sharp>* Q'\<rbrakk> \<Longrightarrow> \<exists>P'. \<Psi> \<rhd> P \<Longrightarrow>\<^sup>^\<^sub>\<tau> P' \<and> (\<Psi>, P', Q') \<in> Rel"

  shows "\<Psi> \<rhd> P \<leadsto><Rel> Q"
using `eqvt Rel`
proof(induct rule: weakSimI[of _ _ _ _ "(yvec, C)"])
  case(cAct \<Psi>' \<alpha> Q')
  obtain p::"name prm" where "(p \<bullet> yvec) \<sharp>* \<Psi>" and "(p \<bullet> yvec) \<sharp>* P" and  "(p \<bullet> yvec) \<sharp>* Q"
                         and  "(p \<bullet> yvec) \<sharp>* \<alpha>" and "(p \<bullet> yvec) \<sharp>* \<Psi>'"
                         and "(p \<bullet> yvec) \<sharp>* Q'" and S: "(set p) \<subseteq> set yvec \<times> set(p \<bullet> yvec)"
                         and "distinctPerm p"
    by(rule_tac c="(\<Psi>, P, Q, \<alpha>, Q', \<Psi>')" and xvec=yvec in name_list_avoiding) auto
  from `bn \<alpha> \<sharp>* (yvec, C)` have "bn \<alpha> \<sharp>* yvec" and "bn \<alpha> \<sharp>* C" by(simp add: freshChainSym)+ 
  show ?case
  proof(cases rule: actionCases[where \<alpha> = \<alpha>])
    case(cInput M N)
    from `(p \<bullet> yvec) \<sharp>* \<alpha>` `\<alpha> = M\<lparr>N\<rparr>` have "(p \<bullet> yvec) \<sharp>* M" and  "(p \<bullet> yvec) \<sharp>* N" by simp+
    from `\<Psi> \<rhd> Q \<longmapsto>\<alpha> \<prec> Q'` `\<alpha> = M\<lparr>N\<rparr>` `yvec \<sharp>* \<Psi>` `(p \<bullet> yvec) \<sharp>* \<Psi>` `yvec \<sharp>* Q` `(p \<bullet> yvec) \<sharp>* Q` S
    have "\<Psi> \<rhd> Q \<longmapsto>(p \<bullet> M)\<lparr>(p \<bullet> N)\<rparr> \<prec> (p \<bullet> Q')" 
      by(drule_tac pi=p in semantics.eqvt) (simp add: eqvts)
    moreover from `(p \<bullet> yvec) \<sharp>* M` have "(p \<bullet> (p \<bullet> yvec)) \<sharp>* (p \<bullet> M)"
      by(simp add: pt_fresh_star_bij[OF pt_name_inst, OF at_name_inst])
    with `distinctPerm p` have "yvec \<sharp>* (p \<bullet> M)" by simp
    moreover from `(p \<bullet> yvec) \<sharp>* N` have "(p \<bullet> p \<bullet> yvec) \<sharp>* (p \<bullet> N)" 
      by(simp add: pt_fresh_star_bij[OF pt_name_inst, OF at_name_inst])
    with `distinctPerm p` have "yvec \<sharp>* (p \<bullet> N)" by simp
    moreover from `(p \<bullet> yvec) \<sharp>* Q'` have "(p \<bullet> p \<bullet> yvec) \<sharp>* (p \<bullet> Q')" 
      by(simp add: pt_fresh_star_bij[OF pt_name_inst, OF at_name_inst])
    with `distinctPerm p` have "yvec \<sharp>* (p \<bullet> Q')" by simp
    moreover from `(p \<bullet> yvec) \<sharp>* \<Psi>'` have "(p \<bullet> p \<bullet> yvec) \<sharp>* (p \<bullet> \<Psi>')"
      by(simp add: pt_fresh_star_bij[OF pt_name_inst, OF at_name_inst])
    with `distinctPerm p` have "yvec \<sharp>* (p \<bullet> \<Psi>')" by simp
    ultimately obtain P' P'' where PTrans: "\<Psi> : Q \<rhd> P \<Longrightarrow>(p \<bullet> M)\<lparr>(p \<bullet> N)\<rparr> \<prec> P''" and P''Chain: "\<Psi> \<otimes> (p \<bullet> \<Psi>') \<rhd> P'' \<Longrightarrow>\<^sup>^\<^sub>\<tau> P'"
                               and P'RelQ': "(\<Psi> \<otimes> (p \<bullet> \<Psi>'), P', (p \<bullet> Q')) \<in> Rel"
      by(auto dest: rAct)
    from PTrans have "(p \<bullet> \<Psi>) : (p \<bullet> Q) \<rhd> (p \<bullet> P) \<Longrightarrow>p \<bullet> ((p \<bullet> M)\<lparr>(p \<bullet> N)\<rparr>) \<prec> (p \<bullet> P'')"
      by(rule weakTransitionClosed)
    with S `yvec \<sharp>* \<Psi>` `(p \<bullet> yvec) \<sharp>* \<Psi>` `yvec \<sharp>* Q` `(p \<bullet> yvec) \<sharp>* Q` `yvec \<sharp>* P` `(p \<bullet> yvec) \<sharp>* P` `distinctPerm p`
    have "\<Psi> : Q \<rhd> P \<Longrightarrow>M\<lparr>N\<rparr> \<prec> (p \<bullet> P'')" by(simp add: eqvts)
    moreover from P''Chain have  "(p \<bullet> (\<Psi> \<otimes> (p \<bullet> \<Psi>'))) \<rhd> (p \<bullet> P'') \<Longrightarrow>\<^sup>^\<^sub>\<tau> (p \<bullet> P')" by(rule eqvts)
    with `yvec \<sharp>* \<Psi>` `(p \<bullet> yvec) \<sharp>* \<Psi>` S `distinctPerm p` 
    have "\<Psi> \<otimes> \<Psi>' \<rhd> (p \<bullet> P'') \<Longrightarrow>\<^sup>^\<^sub>\<tau> (p \<bullet> P')" by(simp add: eqvts)
    moreover from P'RelQ' Eqvt have "(p \<bullet> (\<Psi> \<otimes> (p \<bullet> \<Psi>')), p \<bullet> P', p \<bullet> p \<bullet> Q') \<in> Rel"
      apply(simp add: eqvt_def eqvts)
      apply(erule_tac x="(\<Psi> \<otimes> (p \<bullet> \<Psi>'), P', p \<bullet> Q')" in ballE)
      apply(erule_tac x="p" in allE)
      by(auto simp add: eqvts)
    with `yvec \<sharp>* \<Psi>` `(p \<bullet> yvec) \<sharp>* \<Psi>` S `distinctPerm p` have "(\<Psi> \<otimes> \<Psi>', p \<bullet> P', Q') \<in> Rel" by(simp add: eqvts)
    ultimately show ?thesis using `\<alpha>=M\<lparr>N\<rparr>` by blast
  next
    case(cOutput M xvec N)
    from `bn \<alpha> \<sharp>* \<Psi>` `bn \<alpha> \<sharp>* P` `bn \<alpha> \<sharp>* Q`  `bn \<alpha> \<sharp>* subject \<alpha>` `\<alpha>=M\<lparr>\<nu>*xvec\<rparr>\<langle>N\<rangle>` `bn \<alpha> \<sharp>* yvec`
         `(p \<bullet> yvec) \<sharp>* \<alpha>` `bn \<alpha> \<sharp>* C` `bn \<alpha> \<sharp>* subject \<alpha>` `distinct(bn \<alpha>)`
    have "xvec \<sharp>* \<Psi>" and "xvec \<sharp>* P" and "xvec \<sharp>* Q" and "xvec \<sharp>* M" and "yvec \<sharp>* xvec"
     and "(p \<bullet> yvec) \<sharp>* M" and "(p \<bullet> yvec) \<sharp>* xvec" and "xvec \<sharp>* C" and "xvec \<sharp>* M" and "(p \<bullet> yvec) \<sharp>* N" 
     and "distinct xvec" by simp+
    from `\<Psi> \<rhd> Q \<longmapsto>\<alpha> \<prec> Q'` `yvec \<sharp>* \<Psi>` `(p \<bullet> yvec) \<sharp>* \<Psi>` `yvec \<sharp>* Q` `(p \<bullet> yvec) \<sharp>* Q` S `\<alpha>=M\<lparr>\<nu>*xvec\<rparr>\<langle>N\<rangle>`
    have "\<Psi> \<rhd> Q \<longmapsto>(p \<bullet> M)\<lparr>\<nu>*xvec\<rparr>\<langle>N\<rangle> \<prec> Q'"
      by(rule_tac outputPermSubject) (assumption | simp add: fresh_star_def)+
    moreover note `xvec \<sharp>* \<Psi>` `xvec \<sharp>* P` 
    moreover note `xvec \<sharp>* Q`
    moreover from `xvec \<sharp>* M` have "(p \<bullet> xvec) \<sharp>* (p \<bullet> M)"
      by(simp add: pt_fresh_star_bij[OF pt_name_inst, OF at_name_inst])
    with `yvec \<sharp>* xvec` `(p \<bullet> yvec) \<sharp>* xvec` S have "xvec \<sharp>* (p \<bullet> M)"
      by simp
    moreover note `xvec \<sharp>* C`
    moreover from `(p \<bullet> yvec) \<sharp>* M` have "(p \<bullet> (p \<bullet> yvec)) \<sharp>* (p \<bullet> M)"
      by(simp add: pt_fresh_star_bij[OF pt_name_inst, OF at_name_inst])
    with `distinctPerm p` have "yvec \<sharp>* (p \<bullet> M)" by simp
    moreover note `yvec \<sharp>* xvec`
    moreover from `\<Psi> \<rhd> Q \<longmapsto>\<alpha> \<prec> Q'` `yvec \<sharp>* Q` `yvec \<sharp>* xvec` `\<alpha>=M\<lparr>\<nu>*xvec\<rparr>\<langle>N\<rangle>` `xvec \<sharp>* M` `distinct xvec`
    have "yvec \<sharp>* N" and "yvec \<sharp>* Q'"  by(force dest: outputFreshChainDerivative)+
    moreover from `(p \<bullet> yvec) \<sharp>* \<Psi>'` have "(p \<bullet> p \<bullet> yvec) \<sharp>* (p \<bullet> \<Psi>')"
      by(simp add: pt_fresh_star_bij[OF pt_name_inst, OF at_name_inst])
    with `distinctPerm p` have "yvec \<sharp>* (p \<bullet> \<Psi>')" by simp
    ultimately obtain P'' P' where PTrans: "\<Psi> : Q \<rhd> P \<Longrightarrow>(p \<bullet> M)\<lparr>\<nu>*xvec\<rparr>\<langle>N\<rangle> \<prec> P''"
                               and PChain: "\<Psi> \<otimes> (p \<bullet> \<Psi>') \<rhd> P'' \<Longrightarrow>\<^sup>^\<^sub>\<tau> P'"
                               and P'RelQ': "(\<Psi> \<otimes> (p \<bullet> \<Psi>'), P', Q') \<in> Rel"
      by(drule_tac rAct) auto
    from PTrans have "(p \<bullet> \<Psi>) : (p \<bullet> Q) \<rhd> (p \<bullet> P) \<Longrightarrow>(p \<bullet> ((p \<bullet> M)\<lparr>\<nu>*xvec\<rparr>\<langle>N\<rangle>)) \<prec> (p \<bullet> P'')" 
      by(rule eqvts)
    with S `yvec \<sharp>* \<Psi>` `(p \<bullet> yvec) \<sharp>* \<Psi>` `yvec \<sharp>* P` `(p \<bullet> yvec) \<sharp>* P` `yvec \<sharp>* Q` `(p \<bullet> yvec) \<sharp>* Q` `yvec \<sharp>* xvec` `(p \<bullet> yvec) \<sharp>* xvec` 
      `yvec \<sharp>* N` `(p \<bullet> yvec) \<sharp>* N` `distinctPerm p` have "\<Psi> : Q \<rhd> P \<Longrightarrow>M\<lparr>\<nu>*xvec\<rparr>\<langle>N\<rangle> \<prec> (p \<bullet> P'')"
      by(simp add: eqvts)
    moreover from PChain have "(p \<bullet> (\<Psi> \<otimes> (p \<bullet> \<Psi>'))) \<rhd> (p \<bullet> P'') \<Longrightarrow>\<^sup>^\<^sub>\<tau> (p \<bullet> P')" by(rule eqvts)
    with S `yvec \<sharp>* \<Psi>` `(p \<bullet> yvec) \<sharp>* \<Psi>` `distinctPerm p` have "\<Psi> \<otimes> \<Psi>' \<rhd> (p \<bullet> P'') \<Longrightarrow>\<^sup>^\<^sub>\<tau> (p \<bullet> P')" by(simp add: eqvts)
    moreover from P'RelQ' `eqvt Rel` have "p \<bullet> (\<Psi> \<otimes> (p \<bullet> \<Psi>'), P', Q') \<in> Rel"
      by(simp add: eqvt_def) auto
    with `yvec \<sharp>* \<Psi>` `(p \<bullet> yvec) \<sharp>* \<Psi>``yvec \<sharp>* Q'` `(p \<bullet> yvec) \<sharp>* Q'` S `distinctPerm p` 
    have "(\<Psi> \<otimes> \<Psi>', p \<bullet> P', Q') \<in> Rel" by(simp add: eqvts)
    ultimately show ?thesis using `\<alpha>=M\<lparr>\<nu>*xvec\<rparr>\<langle>N\<rangle>` by blast
  next
    case cTau
    from `\<alpha> = \<tau>` `\<alpha> \<noteq> \<tau>` have "False" by simp
    thus ?thesis by simp
  qed
next
  case(cTau Q')
  from `\<Psi> \<rhd> Q \<longmapsto>\<tau> \<prec> Q'` `yvec \<sharp>* Q` have "yvec \<sharp>* Q'"
    by(force dest: tauFreshChainDerivative)
  with `\<Psi> \<rhd> Q \<longmapsto>\<tau> \<prec> Q'` show ?case
    by(rule rTau)
qed

lemma weakSimIFresh[consumes 4, case_names cAct cTau]:
  fixes \<Psi>   :: 'b
  and   P   :: "('a, 'b, 'c) psi"
  and   Rel :: "('b \<times> ('a, 'b, 'c) psi \<times> ('a, 'b, 'c) psi) set"
  and   Q   :: "('a, 'b, 'c) psi"
  and   x   :: name
  and   C   :: "'d::fs_name"

  assumes Eqvt: "eqvt Rel"
  and     "x \<sharp> \<Psi>"
  and     "x \<sharp> P"
  and     "x \<sharp> Q"
  and     "\<And>\<alpha> Q' \<Psi>'. \<lbrakk>\<Psi> \<rhd> Q \<longmapsto>\<alpha> \<prec> Q'; bn \<alpha> \<sharp>* \<Psi>; bn \<alpha> \<sharp>* P; bn \<alpha> \<sharp>* Q; \<alpha> \<noteq> \<tau>;
                       bn \<alpha> \<sharp>* subject \<alpha>; bn \<alpha> \<sharp>* C; x \<sharp> \<alpha>; x \<sharp> Q'; x \<sharp> \<Psi>'\<rbrakk> \<Longrightarrow>
                       \<exists>P''. \<Psi> : Q \<rhd> P \<Longrightarrow>\<alpha> \<prec> P'' \<and> (\<exists>P'. \<Psi> \<otimes> \<Psi>' \<rhd> P'' \<Longrightarrow>\<^sup>^\<^sub>\<tau> P' \<and> (\<Psi> \<otimes> \<Psi>', P', Q') \<in> Rel)"
  and     "\<And>Q'. \<lbrakk>\<Psi> \<rhd> Q \<longmapsto>\<tau> \<prec> Q'; x \<sharp> Q'\<rbrakk> \<Longrightarrow> \<exists>P'. \<Psi> \<rhd> P \<Longrightarrow>\<^sup>^\<^sub>\<tau> P' \<and> (\<Psi>, P', Q') \<in> Rel"

  shows "\<Psi> \<rhd> P \<leadsto><Rel> Q"
using assms
by(rule_tac yvec="[x]" and C=C in weakSimIChainFresh) auto

lemma weakSimE:
  fixes F   :: 'b
  and   P   :: "('a, 'b, 'c) psi"
  and   Rel :: "('b \<times> ('a, 'b, 'c) psi \<times> ('a, 'b, 'c) psi) set"
  and   Q   :: "('a, 'b, 'c) psi"

  assumes "\<Psi> \<rhd> P \<leadsto><Rel> Q"

  shows "\<And>\<Psi>' \<alpha> Q'. \<lbrakk>\<Psi> \<rhd> Q \<longmapsto>\<alpha> \<prec> Q'; bn \<alpha> \<sharp>* \<Psi>; bn \<alpha> \<sharp>* P; \<alpha> \<noteq> \<tau>\<rbrakk> \<Longrightarrow> 
                            \<exists>P''. \<Psi> : Q \<rhd> P \<Longrightarrow>\<alpha> \<prec> P'' \<and> (\<exists>P'. \<Psi> \<otimes> \<Psi>' \<rhd> P'' \<Longrightarrow>\<^sup>^\<^sub>\<tau> P' \<and> (\<Psi> \<otimes> \<Psi>', P', Q') \<in> Rel)"
  and   "\<And>Q'. \<Psi> \<rhd> Q \<longmapsto>\<tau> \<prec> Q' \<Longrightarrow> \<exists>P'. \<Psi> \<rhd> P \<Longrightarrow>\<^sup>^\<^sub>\<tau> P' \<and> (\<Psi>, P', Q') \<in> Rel"
using assms
by(auto simp add: weakSimulation_def)

lemma weakSimClosedAux:
  fixes \<Psi>   :: 'b
  and   P   :: "('a, 'b, 'c) psi"
  and   Rel :: "('b \<times> ('a, 'b, 'c) psi \<times> ('a, 'b, 'c) psi) set"
  and   Q   :: "('a, 'b, 'c) psi"
  and   p   :: "name prm"

  assumes EqvtRel: "eqvt Rel"
  and     PSimQ: "\<Psi> \<rhd> P \<leadsto><Rel> Q"

  shows "(p \<bullet> \<Psi>) \<rhd> (p \<bullet> P) \<leadsto><Rel> (p \<bullet> Q)"
using EqvtRel
proof(induct rule: weakSimI[of _ _ _ _ "(\<Psi>, P, p)"])
  case(cAct \<Psi>' \<alpha> Q')
  from `p \<bullet> \<Psi> \<rhd> p \<bullet> Q \<longmapsto>\<alpha> \<prec> Q'` 
  have "(rev p \<bullet> p \<bullet> \<Psi>) \<rhd> (rev p \<bullet> p \<bullet> Q) \<longmapsto>(rev p \<bullet> (\<alpha> \<prec> Q'))"
    by(blast dest: semantics.eqvt)
  hence "\<Psi> \<rhd> Q \<longmapsto>(rev p \<bullet> \<alpha>) \<prec> (rev p \<bullet> Q')"
    by(simp add: eqvts)
  moreover with `bn \<alpha> \<sharp>* (\<Psi>, P, p)` have "bn \<alpha>  \<sharp>* \<Psi>" and "bn \<alpha>  \<sharp>* P" and "bn \<alpha>  \<sharp>* p" by simp+
  moreover from `\<alpha> \<noteq> \<tau>` have "(rev p \<bullet> \<alpha>) \<noteq> \<tau>"
    by(cases rule: actionCases[where \<alpha>=\<alpha>]) auto
  ultimately obtain P'' P' where PTrans: "\<Psi> : Q \<rhd> P \<Longrightarrow>(rev p \<bullet> \<alpha>) \<prec> P''"
                          and P''Chain: "\<Psi> \<otimes> (rev p \<bullet> \<Psi>') \<rhd> P'' \<Longrightarrow>\<^sup>^\<^sub>\<tau> P'" and P'RelQ': "(\<Psi> \<otimes> (rev p \<bullet> \<Psi>'), P', rev p \<bullet> Q') \<in> Rel"
    using `\<alpha> \<noteq> \<tau>` PSimQ
    by(drule_tac \<Psi>'="rev p \<bullet> \<Psi>'" in weakSimE(1)) (auto simp add: freshChainPermSimp bnEqvt[symmetric])

  from PTrans have "(p \<bullet> \<Psi>) : (p \<bullet> Q) \<rhd> (p \<bullet> P) \<Longrightarrow>(p \<bullet> (rev p \<bullet> \<alpha>)) \<prec> (p \<bullet> P'')"
    by(rule eqvts)
  hence "(p \<bullet> \<Psi>) : (p \<bullet> Q) \<rhd> (p \<bullet> P) \<Longrightarrow>\<alpha> \<prec> (p \<bullet> P'')" by(simp add: eqvts freshChainPermSimp)
  moreover from P''Chain have  "(p \<bullet> (\<Psi> \<otimes> (rev p \<bullet> \<Psi>'))) \<rhd> (p \<bullet> P'') \<Longrightarrow>\<^sup>^\<^sub>\<tau> (p \<bullet> P')" by(rule eqvts)
  hence "(p \<bullet> \<Psi>) \<otimes> \<Psi>' \<rhd> (p \<bullet> P'') \<Longrightarrow>\<^sup>^\<^sub>\<tau> (p \<bullet> P')" by(simp add: eqvts)
  moreover from P'RelQ' EqvtRel have "(p \<bullet> ((\<Psi> \<otimes> (rev p \<bullet> \<Psi>')), P', rev p \<bullet> Q')) \<in> Rel"
    by(simp only: eqvt_def)
  hence "((p \<bullet> \<Psi>) \<otimes> \<Psi>', p \<bullet> P', Q') \<in> Rel" by(simp add: eqvts)
  ultimately show ?case by blast
next
  case(cTau Q')
  from `p \<bullet> \<Psi> \<rhd> p \<bullet> Q \<longmapsto>\<tau> \<prec> Q'` 
  have "(rev p \<bullet> p \<bullet> \<Psi>) \<rhd> (rev p \<bullet> p \<bullet> Q) \<longmapsto>(rev p \<bullet> (\<tau> \<prec> Q'))"
    by(blast dest: semantics.eqvt)
  hence "\<Psi> \<rhd> Q \<longmapsto>\<tau> \<prec> (rev p \<bullet> Q')" by(simp add: eqvts)
  with PSimQ obtain P' where PChain: "\<Psi> \<rhd> P \<Longrightarrow>\<^sup>^\<^sub>\<tau> P'" and P'RelQ': "(\<Psi>, P', rev p \<bullet> Q') \<in> Rel"
    by(blast dest: weakSimE)
  from PChain have "(p \<bullet> \<Psi>) \<rhd> (p \<bullet> P) \<Longrightarrow>\<^sup>^\<^sub>\<tau> (p \<bullet> P')" by(rule tauChainEqvt)
  moreover from P'RelQ' EqvtRel have "(p \<bullet> (\<Psi>,  P', rev p \<bullet> Q')) \<in> Rel"
    by(simp only: eqvt_def)
  hence "(p \<bullet> \<Psi>, p \<bullet> P', Q') \<in> Rel" by(simp add: eqvts)
  ultimately show ?case
    by blast
qed

lemma weakSimClosed:
  fixes \<Psi>   :: 'b
  and   P   :: "('a, 'b, 'c) psi"
  and   Rel :: "('b \<times> ('a, 'b, 'c) psi \<times> ('a, 'b, 'c) psi) set"
  and   Q   :: "('a, 'b, 'c) psi"
  and   p   :: "name prm"

  assumes EqvtRel: "eqvt Rel"

  shows "\<Psi> \<rhd> P \<leadsto><Rel> Q \<Longrightarrow> (p \<bullet> \<Psi>) \<rhd> (p \<bullet> P) \<leadsto><Rel> (p \<bullet> Q)"
  and   "P \<leadsto><Rel> Q \<Longrightarrow> (p \<bullet> P) \<leadsto><Rel> (p \<bullet> Q)"
using EqvtRel
by(force dest: weakSimClosedAux simp add: permBottom)+

lemma weakSimReflexive:
  fixes Rel :: "('b \<times> ('a, 'b, 'c) psi \<times> ('a, 'b, 'c) psi) set"
  and   \<Psi>   :: 'b
  and   P   :: "('a, 'b, 'c) psi"

  assumes "{(\<Psi>, P, P) | \<Psi> P. True} \<subseteq> Rel"

  shows "\<Psi> \<rhd> P \<leadsto><Rel> P"
using assms
by(auto simp add: weakSimulation_def weakTransition_def dest: rtrancl_into_rtrancl) force+

lemma weakSimTauChain:
  fixes \<Psi>   :: 'b
  and   Q   :: "('a, 'b, 'c) psi"
  and   Q'  :: "('a, 'b, 'c) psi"
  and   P   :: "('a, 'b, 'c) psi"
  and   Rel :: "('b \<times> ('a, 'b, 'c) psi \<times> ('a, 'b, 'c) psi) set"

  assumes "\<Psi> \<rhd> Q \<Longrightarrow>\<^sup>^\<^sub>\<tau> Q'"
  and     "(\<Psi>, P, Q) \<in> Rel"
  and     Sim: "\<And>\<Psi>' R S. (\<Psi>', R, S) \<in> Rel \<Longrightarrow> \<Psi>' \<rhd> R \<leadsto><Rel> S"
  
  obtains P' where "\<Psi> \<rhd> P \<Longrightarrow>\<^sup>^\<^sub>\<tau> P'" and "(\<Psi>, P', Q') \<in> Rel"
proof -
  assume A: "\<And>P'. \<lbrakk>\<Psi> \<rhd> P \<Longrightarrow>\<^sup>^\<^sub>\<tau> P'; (\<Psi>, P', Q') \<in> Rel\<rbrakk> \<Longrightarrow> thesis"
  from `\<Psi> \<rhd> Q \<Longrightarrow>\<^sup>^\<^sub>\<tau> Q'` `(\<Psi>, P, Q) \<in> Rel` A show ?thesis
  proof(induct arbitrary: P thesis rule: tauChainInduct)
    case(TauBase Q P)
    moreover have "\<Psi> \<rhd> P \<Longrightarrow>\<^sup>^\<^sub>\<tau> P" by simp
    ultimately show ?case by blast
  next
    case(TauStep Q Q' Q'' P)
    from `(\<Psi>, P, Q) \<in> Rel` obtain P' where PChain: "\<Psi> \<rhd> P \<Longrightarrow>\<^sup>^\<^sub>\<tau> P'" and "(\<Psi>, P', Q') \<in> Rel"
      by(rule TauStep)
    from `(\<Psi>, P', Q') \<in> Rel` have "\<Psi> \<rhd> P' \<leadsto><Rel> Q'" by(rule Sim)
    then obtain P'' where P'Chain: "\<Psi> \<rhd> P' \<Longrightarrow>\<^sup>^\<^sub>\<tau> P''" and "(\<Psi>, P'', Q'') \<in> Rel"
      using `\<Psi> \<rhd> Q' \<longmapsto>\<tau> \<prec> Q''` by(blast dest: weakSimE)
    from PChain P'Chain have "\<Psi> \<rhd> P \<Longrightarrow>\<^sup>^\<^sub>\<tau> P''" by simp
    thus ?case using `(\<Psi>, P'', Q'') \<in> Rel` by(rule TauStep)
  qed
qed

lemma weakSimE2:
  fixes \<Psi>  :: 'b
  and   P   :: "('a, 'b, 'c) psi"
  and   Rel :: "('b \<times> ('a, 'b, 'c) psi \<times> ('a, 'b, 'c) psi) set" 
  and   Q   :: "('a, 'b, 'c) psi"

  assumes PRelQ: "(\<Psi>, P, Q) \<in> Rel"
  and     Sim: "\<And>\<Psi>' R S. (\<Psi>', R, S) \<in> Rel \<Longrightarrow> \<Psi>' \<rhd> R \<leadsto><Rel> S"
  and     QTrans: "\<Psi> : R \<rhd> Q \<Longrightarrow>\<alpha> \<prec> Q'"
  and     "bn \<alpha> \<sharp>* \<Psi>"
  and     "bn \<alpha> \<sharp>* P"
  and     "\<alpha> \<noteq> \<tau>"

  obtains P'' P' where "\<Psi> : R \<rhd> P \<Longrightarrow>\<alpha> \<prec> P''" and "\<Psi> \<otimes> \<Psi>' \<rhd> P'' \<Longrightarrow>\<^sup>^\<^sub>\<tau> P'" and "(\<Psi> \<otimes> \<Psi>', P', Q') \<in> Rel"
proof -
  assume A: "\<And>P'' P'. \<lbrakk>\<Psi> : R \<rhd> P \<Longrightarrow>\<alpha> \<prec> P''; \<Psi> \<otimes> \<Psi>' \<rhd> P'' \<Longrightarrow>\<^sup>^\<^sub>\<tau> P'; (\<Psi> \<otimes> \<Psi>', P', Q') \<in> Rel\<rbrakk> \<Longrightarrow> thesis"
  from QTrans obtain Q'' 
    where QChain: "\<Psi> \<rhd> Q \<Longrightarrow>\<^sup>^\<^sub>\<tau> Q''" 
      and ReqQ'': "insertAssertion (extractFrame R) \<Psi> \<hookrightarrow>\<^sub>F insertAssertion (extractFrame Q'') \<Psi>"
      and Q''Trans: "\<Psi> \<rhd> Q'' \<longmapsto>\<alpha> \<prec> Q'"
    by(rule weakTransitionE)

  from QChain PRelQ Sim
  obtain P'' where PChain: "\<Psi> \<rhd> P \<Longrightarrow>\<^sup>^\<^sub>\<tau> P''" and P''RelQ'': "(\<Psi>, P'', Q'') \<in> Rel" by(rule weakSimTauChain)

  from PChain `bn \<alpha> \<sharp>* P` have "bn \<alpha> \<sharp>* P''" by(rule tauChainFreshChain)
  from P''RelQ'' have "\<Psi> \<rhd> P'' \<leadsto><Rel> Q''" by(rule Sim)
  with Q''Trans `bn \<alpha> \<sharp>* \<Psi>` `bn \<alpha> \<sharp>* P''` `\<alpha> \<noteq> \<tau>`
  obtain P''' P' where P''Trans: "\<Psi> : Q'' \<rhd> P'' \<Longrightarrow>\<alpha> \<prec> P'''" and P'''Chain: "\<Psi> \<otimes> \<Psi>' \<rhd> P''' \<Longrightarrow>\<^sup>^\<^sub>\<tau> P'"
                   and P'RelQ': "(\<Psi> \<otimes> \<Psi>', P', Q') \<in> Rel"
    by(blast dest: weakSimE)
  
  from P''Trans obtain P'''' where P''Chain: "\<Psi> \<rhd> P'' \<Longrightarrow>\<^sup>^\<^sub>\<tau> P''''"
                               and Q''eqP'''': "insertAssertion (extractFrame Q'') \<Psi> \<hookrightarrow>\<^sub>F insertAssertion (extractFrame P'''') \<Psi>"
                               and P''''Trans: "\<Psi> \<rhd> P'''' \<longmapsto>\<alpha> \<prec> P'''"
    by(rule weakTransitionE)
  from PChain P''Chain have "\<Psi> \<rhd> P \<Longrightarrow>\<^sup>^\<^sub>\<tau> P''''" by simp
  moreover from ReqQ'' Q''eqP'''' have "insertAssertion (extractFrame R) \<Psi> \<hookrightarrow>\<^sub>F insertAssertion (extractFrame P'''') \<Psi>"
    by(rule FrameStatImpTrans)
  ultimately have "\<Psi> : R \<rhd> P \<Longrightarrow>\<alpha> \<prec> P'''" using P''''Trans by(rule weakTransitionI)
  with P'''Chain P'RelQ' A show ?thesis by blast
qed

lemma weakSimTransitive:
  fixes \<Psi>     :: 'b
  and   P     :: "('a, 'b, 'c) psi"
  and   Rel   :: "('b \<times> ('a, 'b, 'c) psi \<times> ('a, 'b, 'c) psi) set"
  and   Q     :: "('a, 'b, 'c) psi"
  and   Rel'  :: "('b \<times> ('a, 'b, 'c) psi \<times> ('a, 'b, 'c) psi) set"
  and   T     :: "('a, 'b, 'c) psi"
  and   Rel'' :: "('b \<times> ('a, 'b, 'c) psi \<times> ('a, 'b, 'c) psi) set"

  assumes PRelQ: "(\<Psi>, P, Q) \<in> Rel"
  and     QSimR: "\<Psi> \<rhd> Q \<leadsto><Rel'> R"
  and     Eqvt: "eqvt Rel''"
  and     Set: "{(\<Psi>, P, R) | \<Psi> P R. \<exists>Q. (\<Psi>, P, Q) \<in> Rel \<and> (\<Psi>, Q, R) \<in> Rel'} \<subseteq> Rel''"
  and     Sim: "\<And>\<Psi>' R S. (\<Psi>', R, S) \<in> Rel \<Longrightarrow> \<Psi>' \<rhd> R \<leadsto><Rel> S"

  shows "\<Psi> \<rhd> P \<leadsto><Rel''> R"
using `eqvt Rel''`
proof(induct rule: weakSimI[of _ _ _ _ Q])
  case(cAct \<Psi>' \<alpha> R')
  from QSimR `\<Psi> \<rhd> R \<longmapsto>\<alpha> \<prec> R'` `bn \<alpha> \<sharp>* \<Psi>` `bn \<alpha> \<sharp>* Q` `\<alpha> \<noteq> \<tau>`
  obtain Q'' Q' where QTrans: "\<Psi> : R \<rhd> Q \<Longrightarrow>\<alpha> \<prec> Q''" and Q''Chain: "\<Psi> \<otimes> \<Psi>' \<rhd> Q'' \<Longrightarrow>\<^sup>^\<^sub>\<tau> Q'"
                  and Q'RelR': "(\<Psi> \<otimes> \<Psi>', Q', R') \<in> Rel'"
    by(blast dest: weakSimE)
  with PRelQ Sim QTrans `bn \<alpha> \<sharp>* \<Psi>` `bn \<alpha> \<sharp>* P` `\<alpha> \<noteq> \<tau>`
  obtain P''' P'' where PTrans: "\<Psi> : R \<rhd> P \<Longrightarrow>\<alpha> \<prec> P'''" 
                and P'''Chain: "\<Psi> \<otimes> \<Psi>' \<rhd> P''' \<Longrightarrow>\<^sup>^\<^sub>\<tau> P''" and P''RelQ'': "(\<Psi> \<otimes> \<Psi>', P'', Q'') \<in> Rel"
    by(drule_tac weakSimE2) auto

  note PTrans
  moreover from Q''Chain P''RelQ'' Sim obtain P' where P''Chain: "\<Psi> \<otimes> \<Psi>' \<rhd> P'' \<Longrightarrow>\<^sup>^\<^sub>\<tau> P'" and P'RelQ': "(\<Psi> \<otimes> \<Psi>', P', Q') \<in> Rel"
    by(rule weakSimTauChain)
  from P'''Chain P''Chain have "\<Psi> \<otimes> \<Psi>' \<rhd> P''' \<Longrightarrow>\<^sup>^\<^sub>\<tau> P'" by simp
  moreover from P'RelQ' Q'RelR' Set have "(\<Psi> \<otimes> \<Psi>', P', R') \<in> Rel''" by blast
  ultimately show ?case by blast
next
  case(cTau R')
  from QSimR `\<Psi> \<rhd> R \<longmapsto>\<tau> \<prec> R'` obtain Q' where QChain: "\<Psi> \<rhd> Q \<Longrightarrow>\<^sup>^\<^sub>\<tau> Q'" and Q'RelR': "(\<Psi>, Q', R') \<in> Rel'" 
    by(blast dest: weakSimE)
  from QChain PRelQ Sim obtain P' where PChain: "\<Psi> \<rhd> P \<Longrightarrow>\<^sup>^\<^sub>\<tau> P'" and P'RelQ': "(\<Psi>, P', Q') \<in> Rel"
    by(rule weakSimTauChain)
  note PChain
  moreover from P'RelQ' Q'RelR' Set have "(\<Psi>, P', R') \<in> Rel''" by blast
  ultimately show ?case by blast
qed

lemma weakSimStatEq:
  fixes \<Psi>   :: 'b
  and   P   :: "('a, 'b, 'c) psi"
  and   Rel :: "('b \<times> ('a, 'b, 'c) psi \<times> ('a, 'b, 'c) psi) set"
  and   Q   :: "('a, 'b, 'c) psi"
  and   \<Psi>'  :: 'b

  assumes PSimQ: "\<Psi> \<rhd> P \<leadsto><Rel> Q"
  and     "eqvt Rel'"
  and     "\<Psi> \<simeq> \<Psi>'"
  and     C1: "\<And>\<Psi>' R S \<Psi>''. \<lbrakk>(\<Psi>', R, S) \<in> Rel; \<Psi>' \<simeq> \<Psi>''\<rbrakk> \<Longrightarrow> (\<Psi>'', R, S) \<in> Rel'"

  shows "\<Psi>' \<rhd> P \<leadsto><Rel'> Q"
using `eqvt Rel'`
proof(induct rule: weakSimI[of _ _ _ _ \<Psi>])
  case(cAct \<Psi>'' \<alpha> Q')
  from `\<Psi>' \<rhd> Q \<longmapsto>\<alpha> \<prec> Q'` `\<Psi> \<simeq> \<Psi>'`
  have "\<Psi> \<rhd> Q \<longmapsto>\<alpha> \<prec> Q'" by(metis statEqTransition AssertionStatEqSym)
  with PSimQ `bn \<alpha> \<sharp>* \<Psi>` `bn \<alpha> \<sharp>* P` `\<alpha> \<noteq> \<tau>`
  obtain P'' P' where PTrans: "\<Psi> : Q \<rhd> P \<Longrightarrow>\<alpha> \<prec> P''" and P''Chain: "\<Psi> \<otimes> \<Psi>'' \<rhd> P'' \<Longrightarrow>\<^sup>^\<^sub>\<tau> P'" 
                  and P'RelQ': "(\<Psi> \<otimes> \<Psi>'', P', Q') \<in> Rel"
    by(blast dest: weakSimE)

  from PTrans `\<Psi> \<simeq> \<Psi>'` have "\<Psi>' : Q \<rhd> P \<Longrightarrow>\<alpha> \<prec> P''" by(rule weakTransitionStatEq)
  moreover from P''Chain `\<Psi> \<simeq> \<Psi>'` have "\<Psi>' \<otimes> \<Psi>'' \<rhd> P'' \<Longrightarrow>\<^sup>^\<^sub>\<tau> P'" by(metis tauChainStatEq Composition)
  moreover from P'RelQ' `\<Psi> \<simeq> \<Psi>'` have "(\<Psi>' \<otimes> \<Psi>'', P', Q') \<in> Rel'"
    by(metis C1 Composition)
  ultimately show ?case
    by blast
next
  case(cTau Q')
  from `\<Psi>' \<rhd> Q \<longmapsto>\<tau> \<prec> Q'` `\<Psi> \<simeq> \<Psi>'`
  have "\<Psi> \<rhd> Q \<longmapsto>\<tau> \<prec> Q'" by(metis statEqTransition AssertionStatEqSym)
  with PSimQ obtain P' where PChain: "\<Psi> \<rhd> P \<Longrightarrow>\<^sup>^\<^sub>\<tau> P'" and P'RelQ': "(\<Psi>, P', Q') \<in> Rel"
    by(blast dest: weakSimE)
  
  from PChain `\<Psi> \<simeq> \<Psi>'` have "\<Psi>' \<rhd> P \<Longrightarrow>\<^sup>^\<^sub>\<tau> P'" by(rule tauChainStatEq)
  moreover from `(\<Psi>, P', Q') \<in> Rel` `\<Psi> \<simeq> \<Psi>'` have "(\<Psi>', P', Q') \<in> Rel'"
    by(rule C1)
  ultimately show ?case by blast
qed

lemma weakSimMonotonic: 
  fixes \<Psi> :: 'b
  and   P :: "('a, 'b, 'c) psi"
  and   A :: "('b \<times> ('a, 'b, 'c) psi \<times> ('a, 'b, 'c) psi) set"
  and   Q :: "('a, 'b, 'c) psi"
  and   B :: "('b \<times> ('a, 'b, 'c) psi \<times> ('a, 'b, 'c) psi) set"

  assumes "\<Psi> \<rhd> P \<leadsto><A> Q"
  and     "A \<subseteq> B"

  shows "\<Psi> \<rhd> P \<leadsto><B> Q"
using assms
by(simp (no_asm) add: weakSimulation_def) (blast dest: weakSimE)+

lemma strongSimWeakSim:
  fixes \<Psi>   :: 'b
  and   P   :: "('a, 'b, 'c) psi"
  and   Q   :: "('a, 'b, 'c) psi"
  and   Rel :: "('b \<times> ('a, 'b, 'c) psi \<times> ('a, 'b, 'c) psi) set"

  assumes PRelQ: "(\<Psi>, P, Q) \<in> Rel"
  and     StatImp: "\<And>\<Psi>' R S. (\<Psi>', R, S) \<in> Rel \<Longrightarrow> insertAssertion(extractFrame S) \<Psi>' \<hookrightarrow>\<^sub>F insertAssertion(extractFrame R) \<Psi>'"
  and     Sim:     "\<And>\<Psi>' R S. (\<Psi>', R, S) \<in> Rel \<Longrightarrow> \<Psi>' \<rhd> R \<leadsto>[Rel] S"
  and     Ext:     "\<And>\<Psi>' R S \<Psi>''. (\<Psi>', R, S) \<in> Rel \<Longrightarrow> (\<Psi>' \<otimes> \<Psi>'', R, S) \<in> Rel"

  shows "\<Psi> \<rhd> P \<leadsto><Rel> Q"
proof(induct rule: weakSimI2)
  case(cAct \<Psi>' \<alpha> Q')
  from PRelQ have "\<Psi> \<rhd> P \<leadsto>[Rel] Q" by(rule Sim)
  with `\<Psi> \<rhd> Q \<longmapsto>\<alpha> \<prec> Q'` `bn \<alpha> \<sharp>* \<Psi>` `bn \<alpha> \<sharp>* P`
  obtain P' where PTrans: "\<Psi> \<rhd> P \<longmapsto>\<alpha> \<prec> P'" and P'RelQ': "(\<Psi>, P', Q') \<in> Rel"
    by(blast dest: simE)
  
  from PRelQ have "insertAssertion(extractFrame Q) \<Psi> \<hookrightarrow>\<^sub>F insertAssertion(extractFrame P) \<Psi>" by(rule StatImp)
  with PTrans have "\<Psi> : Q \<rhd> P \<Longrightarrow>\<alpha> \<prec> P'" by(rule transitionWeakTransition)
  moreover from P'RelQ' have "\<forall>\<Psi>'. \<exists>P''. \<Psi> \<otimes> \<Psi>' \<rhd> P' \<Longrightarrow>\<^sup>^\<^sub>\<tau> P'' \<and> (\<Psi> \<otimes> \<Psi>', P'', Q') \<in> Rel"
    by(force intro: Ext)
  ultimately show ?case by blast
next
  case(cTau Q')
  from PRelQ have "\<Psi> \<rhd> P \<leadsto>[Rel] Q" by(rule Sim)
  with `\<Psi> \<rhd> Q \<longmapsto>\<tau> \<prec> Q'` obtain P' where PTrans: "\<Psi> \<rhd> P \<longmapsto>\<tau> \<prec> P'" and P'RelQ': "(\<Psi>, P', Q') \<in> Rel"
    by(force dest: simE)
  with PTrans have "\<Psi> \<rhd> P \<Longrightarrow>\<^sup>^\<^sub>\<tau> P'" by auto
  thus ?case using P'RelQ' by blast
qed

lemma strongAppend:
  fixes \<Psi>    :: 'b
  and   P     :: "('a, 'b, 'c) psi"
  and   Q     :: "('a, 'b, 'c) psi"
  and   R     :: "('a, 'b, 'c) psi"
  and   Rel   :: "('b \<times> ('a, 'b, 'c) psi \<times> ('a, 'b, 'c) psi) set"
  and   Rel'  :: "('b \<times> ('a, 'b, 'c) psi \<times> ('a, 'b, 'c) psi) set"
  and   Rel'' :: "('b \<times> ('a, 'b, 'c) psi \<times> ('a, 'b, 'c) psi) set"

  assumes PSimQ: "\<Psi> \<rhd> P \<leadsto><Rel> Q"
  and     QSimR: "\<Psi> \<rhd> Q \<leadsto>[Rel'] R"
  and     Eqvt'': "eqvt Rel''"
  and     RimpQ: "insertAssertion (extractFrame R) \<Psi> \<hookrightarrow>\<^sub>F insertAssertion (extractFrame Q) \<Psi>"
  and     Set: "{(\<Psi>, P, R) | \<Psi> P R. \<exists>Q. (\<Psi>, P, Q) \<in> Rel \<and> (\<Psi>, Q, R) \<in> Rel'} \<subseteq> Rel''"
  and     C1: "\<And>\<Psi> P Q \<Psi>'. (\<Psi>, P, Q) \<in> Rel' \<Longrightarrow> (\<Psi> \<otimes> \<Psi>', P, Q) \<in> Rel'"

  shows "\<Psi> \<rhd> P \<leadsto><Rel''> R"
proof -
  from Eqvt'' show ?thesis
  proof(induct rule: weakSimI[of _ _ _ _ Q])
    case(cAct \<Psi>' \<alpha> R')
    from `\<Psi> \<rhd> Q \<leadsto>[Rel'] R` `\<Psi> \<rhd> R \<longmapsto>\<alpha> \<prec> R'` `bn \<alpha> \<sharp>* \<Psi>` `bn \<alpha> \<sharp>* Q`
    obtain Q' where QTrans: "\<Psi> \<rhd> Q \<longmapsto>\<alpha> \<prec> Q'" and "(\<Psi>, Q', R') \<in> Rel'"
      by(blast dest: simE)

    from `(\<Psi>, Q', R') \<in> Rel'` have Q'RelR': "(\<Psi> \<otimes> \<Psi>', Q', R') \<in> Rel'" by(rule C1)

    from `\<Psi> \<rhd> P \<leadsto><Rel> Q` QTrans `bn \<alpha> \<sharp>* \<Psi>` `bn \<alpha> \<sharp>* P` `\<alpha> \<noteq> \<tau>` 
    obtain P'' P' where PTrans: "\<Psi> : Q \<rhd> P \<Longrightarrow>\<alpha> \<prec> P''" and P''Chain: "\<Psi> \<otimes> \<Psi>' \<rhd> P'' \<Longrightarrow>\<^sup>^\<^sub>\<tau> P'"
                    and P'RelQ': "(\<Psi> \<otimes> \<Psi>', P', Q') \<in> Rel"
      by(blast dest: weakSimE)

    from PTrans RimpQ have "\<Psi> : R \<rhd> P \<Longrightarrow>\<alpha> \<prec> P''" by(rule weakTransitionFrameImp)
    moreover note P''Chain
    moreover from P'RelQ' Q'RelR' Set have "(\<Psi> \<otimes> \<Psi>', P', R') \<in> Rel''" by blast
    ultimately show ?case by blast
  next
    case(cTau R')
    from `\<Psi> \<rhd> Q \<leadsto>[Rel'] R` `\<Psi> \<rhd> R \<longmapsto>\<tau> \<prec> R'`
    obtain Q' where QTrans: "\<Psi> \<rhd> Q \<longmapsto>\<tau> \<prec> Q'" and Q'RelR': "(\<Psi>, Q', R') \<in> Rel'"
      by(force dest: simE)

    from `\<Psi> \<rhd> P \<leadsto><Rel> Q` QTrans
    obtain P' where PTrans: "\<Psi> \<rhd> P \<Longrightarrow>\<^sup>^\<^sub>\<tau> P'" and P'RelQ': "(\<Psi>, P', Q') \<in> Rel"
      by(blast dest: weakSimE)

    note PTrans
    moreover from P'RelQ' Q'RelR' Set have "(\<Psi>, P', R') \<in> Rel''" by blast
    ultimately show ?case by blast
  qed
qed

lemma quietSim:
  fixes \<Psi> :: 'b
  and   P :: "('a, 'b, 'c) psi"

  assumes "quiet P"
  and     "eqvt Rel"
  and     cQuiet: "\<And>P. quiet P \<Longrightarrow> (\<Psi>, \<zero>, P) \<in> Rel"

  shows "\<Psi> \<rhd> \<zero> \<leadsto><Rel> P"
using `eqvt Rel`
proof(induct rule: weakSimI[of _ _ _ _ "()"])
  case(cAct \<Psi>' \<alpha> P')
  from `\<Psi> \<rhd> P \<longmapsto>\<alpha> \<prec> P'` `\<alpha> \<noteq> \<tau>` have False using `quiet P` 
    by(cases rule: actionCases[where \<alpha>=\<alpha>]) (auto intro: quietOutput quietInput)
  thus ?case by simp
next
  case(cTau P')
  from `\<Psi> \<rhd> P \<longmapsto>\<tau> \<prec> P'` `quiet P` have "quiet P'"
    by(erule_tac quiet.cases) (force simp add: residualInject)
  have "\<Psi> \<rhd> P \<Longrightarrow>\<^sup>^\<^sub>\<tau> P" by simp
  moreover from `quiet P'` have "(\<Psi>, \<zero>, P') \<in> Rel" by(rule cQuiet)
  ultimately show ?case by blast
qed


end

end


