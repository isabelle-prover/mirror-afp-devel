(* 
   Title: Psi-calculi   
   Author/Maintainer: Jesper Bengtson (jebe@itu.dk), 2012
*)
theory Frame
  imports Agent
begin

lemma permLength[simp]:
  fixes p    :: "name prm"
  and   xvec :: "'a::pt_name list"

  shows "length(p \<bullet> xvec) = length xvec"
by(induct xvec) auto

nominal_datatype 'assertion frame =
    FAssert "'assertion::fs_name"
  | FRes "\<guillemotleft>name\<guillemotright> ('assertion frame)" ("\<lparr>\<nu>_\<rparr>_" [80, 80] 80)

primrec frameResChain :: "name list \<Rightarrow> ('a::fs_name) frame \<Rightarrow> 'a frame" where
  base: "frameResChain [] F = F"
| step: "frameResChain (x#xs) F = \<lparr>\<nu>x\<rparr>(frameResChain xs F)"

notation frameResChain ("\<lparr>\<nu>*_\<rparr>_" [80, 80] 80)
notation FAssert  ("\<langle>\<epsilon>, _\<rangle>" [80] 80)
abbreviation FAssertJudge ("\<langle>_, _\<rangle>" [80, 80] 80) where "\<langle>A\<^isub>F, \<Psi>\<^isub>F\<rangle> \<equiv> frameResChain A\<^isub>F (FAssert \<Psi>\<^isub>F)"

lemma frameResChainEqvt[eqvt]:
  fixes perm :: "name prm"
  and   lst  :: "name list"
  and   F    :: "'a::fs_name frame"
  
  shows "perm \<bullet> (\<lparr>\<nu>*xvec\<rparr>F) = \<lparr>\<nu>*(perm \<bullet> xvec)\<rparr>(perm \<bullet> F)"
by(induct_tac xvec, auto)

lemma frameResChainFresh: 
  fixes x    :: name
  and   xvec :: "name list"
  and   F    :: "'a::fs_name frame"

  shows "x \<sharp> \<lparr>\<nu>*xvec\<rparr>F = (x \<in> set xvec \<or> x \<sharp> F)"
by (induct xvec) (simp_all add: abs_fresh)

lemma frameResChainFreshSet: 
  fixes Xs   :: "name set"
  and   xvec :: "name list"
  and   F    :: "'a::fs_name frame"

  shows "Xs \<sharp>* (\<lparr>\<nu>*xvec\<rparr>F) = (\<forall>x\<in>Xs. x \<in> set xvec \<or> x \<sharp> F)"
by (simp add: fresh_star_def frameResChainFresh)

lemma frameChainAlpha:
  fixes p    :: "name prm"
  and   xvec :: "name list"
  and   F    :: "'a::fs_name frame"

  assumes xvecFreshF: "(p \<bullet> xvec) \<sharp>* F"
  and     S: "set p \<subseteq> set xvec \<times> set (p \<bullet> xvec)"

  shows "\<lparr>\<nu>*xvec\<rparr>F = \<lparr>\<nu>*(p \<bullet> xvec)\<rparr>(p \<bullet> F)"
proof -
  note pt_name_inst at_name_inst S
  moreover have "set xvec \<sharp>* (\<lparr>\<nu>*xvec\<rparr>F)"
    by (simp add: frameResChainFreshSet)
  moreover from xvecFreshF have "set (p \<bullet> xvec) \<sharp>* (\<lparr>\<nu>*xvec\<rparr>F)"
    by (simp add: frameResChainFreshSet) (simp add: fresh_star_def)
  ultimately have "\<lparr>\<nu>*xvec\<rparr>F = p \<bullet> (\<lparr>\<nu>*xvec\<rparr>F)"
    by (rule_tac pt_freshs_freshs [symmetric])
  then show ?thesis by(simp add: eqvts)
qed

lemma frameChainAlpha':
  fixes p    :: "name prm"
  and   A\<^isub>P   :: "name list"
  and   \<Psi>\<^isub>P  :: "'a::fs_name"

  assumes "(p \<bullet> A\<^isub>P) \<sharp>* \<Psi>\<^isub>P"
  and     S: "set p \<subseteq> set A\<^isub>P \<times> set (p \<bullet> A\<^isub>P)"

  shows "\<langle>A\<^isub>P, \<Psi>\<^isub>P\<rangle> = \<langle>(p \<bullet> A\<^isub>P), p \<bullet> \<Psi>\<^isub>P\<rangle>"
using assms
by(subst frameChainAlpha) (auto simp add: fresh_star_def)

lemma alphaFrameRes:
  fixes x :: name
  and   F :: "'a::fs_name frame"
  and   y :: name

  assumes "y \<sharp> F"

  shows "\<lparr>\<nu>x\<rparr>F = \<lparr>\<nu>y\<rparr>([(x, y)] \<bullet> F)"
proof(cases "x = y")
  assume "x=y"
  thus ?thesis by simp
next
  assume "x \<noteq> y"
  with `y \<sharp> F` show ?thesis
    by(perm_simp add: frame.inject alpha calc_atm fresh_left)
qed

lemma frameChainAppend:
  fixes xvec :: "name list"
  and   yvec :: "name list"
  and   F    :: "'a::fs_name frame"
  
  shows "\<lparr>\<nu>*(xvec@yvec)\<rparr>F = \<lparr>\<nu>*xvec\<rparr>(\<lparr>\<nu>*yvec\<rparr>F)"
by(induct xvec) auto

lemma frameChainEqLength:
  fixes xvec :: "name list"
  and   \<Psi>    :: "'a::fs_name"
  and   yvec :: "name list"
  and   \<Psi>'   :: "'a::fs_name"

  assumes "\<langle>xvec, \<Psi>\<rangle> = \<langle>yvec, \<Psi>'\<rangle>"

  shows "length xvec = length yvec"
proof -
  obtain n where "n = length xvec" by auto
  with assms show ?thesis
  proof(induct n arbitrary: xvec yvec \<Psi> \<Psi>')
    case(0 xvec yvec \<Psi> \<Psi>')
    from `0 = length xvec` have "xvec = []" by auto
    moreover with `\<langle>xvec, \<Psi>\<rangle> = \<langle>yvec, \<Psi>'\<rangle>` have "yvec = []"
      by(case_tac yvec) auto
    ultimately show ?case by simp
  next
    case(Suc n xvec yvec \<Psi> \<Psi>')
    from `Suc n = length xvec`
    obtain x xvec' where "xvec = x#xvec'" and "length xvec' = n"
      by(case_tac xvec) auto
    from `\<langle>xvec, \<Psi>\<rangle> = \<langle>yvec, \<Psi>'\<rangle>` `xvec = x # xvec'`
    obtain y yvec' where "\<langle>(x#xvec'), \<Psi>\<rangle> = \<langle>(y#yvec'), \<Psi>'\<rangle>"
      and "yvec = y#yvec'"
      by(case_tac yvec) auto
    hence EQ: "\<lparr>\<nu>x\<rparr>\<lparr>\<nu>*xvec'\<rparr>(FAssert \<Psi>) = \<lparr>\<nu>y\<rparr>\<lparr>\<nu>*yvec'\<rparr>(FAssert \<Psi>')"
      by simp
    have IH: "\<And>xvec yvec \<Psi> \<Psi>'. \<lbrakk>\<langle>xvec, (\<Psi>::'a)\<rangle> = \<langle>yvec, (\<Psi>'::'a)\<rangle>; n = length xvec\<rbrakk> \<Longrightarrow> length xvec = length yvec"
      by fact
    show ?case
    proof(case_tac "x = y")
      assume "x = y"
      with EQ have "\<langle>xvec', \<Psi>\<rangle> = \<langle>yvec', \<Psi>'\<rangle>"
        by(simp add: alpha frame.inject)
      with IH `length xvec' = n` have "length xvec' = length yvec'"
        by blast
      with `xvec = x#xvec'` `yvec=y#yvec'`
      show ?case by simp
    next
      assume "x \<noteq> y"
      with EQ have "\<langle>xvec', \<Psi>\<rangle> = [(x, y)] \<bullet> \<langle>yvec', \<Psi>'\<rangle>"
        by(simp add: alpha frame.inject)
      hence "\<langle>xvec', \<Psi>\<rangle> = \<langle>([(x, y)] \<bullet> yvec'), ([(x, y)] \<bullet> \<Psi>')\<rangle>"
        by(simp add: eqvts)
      with IH `length xvec' = n` have "length xvec' = length ([(x, y)] \<bullet> yvec')"
        by blast
      hence "length xvec' = length yvec'"
        by simp
      with `xvec = x#xvec'` `yvec=y#yvec'`
      show ?case by simp
    qed
  qed
qed

lemma frameEqFresh:
  fixes F :: "('a::fs_name) frame"
  and   G :: "'a frame"
  and   x :: name
  and   y :: name

  assumes "\<lparr>\<nu>x\<rparr>F = \<lparr>\<nu>y\<rparr>G"
  and     "x \<sharp> F"
  
  shows "y \<sharp> G"
using assms
by(auto simp add: frame.inject alpha fresh_left calc_atm)  

lemma frameEqSupp:
  fixes F :: "('a::fs_name) frame"
  and   G :: "'a frame"
  and   x :: name
  and   y :: name

  assumes "\<lparr>\<nu>x\<rparr>F = \<lparr>\<nu>y\<rparr>G"
  and     "x \<in> supp F"
  
  shows "y \<in> supp G"
using assms
apply(auto simp add: frame.inject alpha fresh_left calc_atm)
apply(drule_tac pi="[(x, y)]" in pt_set_bij2[OF pt_name_inst, OF at_name_inst])
by(simp add: eqvts calc_atm)

lemma frameChainEqSuppEmpty[dest]:
  fixes xvec :: "name list"
  and   \<Psi>    :: "'a::fs_name"
  and   yvec :: "name list"
  and   \<Psi>'   :: "'a::fs_name"

  assumes "\<langle>xvec, \<Psi>\<rangle> = \<langle>yvec, \<Psi>'\<rangle>"
  and     "supp \<Psi> = ({}::name set)"

  shows "\<Psi> = \<Psi>'"
proof -
  obtain n where "n = length xvec" by auto
  with assms show ?thesis
  proof(induct n arbitrary: xvec yvec \<Psi> \<Psi>')
    case(0 xvec yvec \<Psi> \<Psi>')
    from `0 = length xvec` have "xvec = []" by auto
    moreover with `\<langle>xvec, \<Psi>\<rangle> = \<langle>yvec, \<Psi>'\<rangle>` have "yvec = []"
      by(case_tac yvec) auto
    ultimately show ?case  using `\<langle>xvec, \<Psi>\<rangle> = \<langle>yvec, \<Psi>'\<rangle>`
      by(simp add: frame.inject) 
  next
    case(Suc n xvec yvec \<Psi> \<Psi>')
    from `Suc n = length xvec`
    obtain x xvec' where "xvec = x#xvec'" and "length xvec' = n"
      by(case_tac xvec) auto
    from `\<langle>xvec, \<Psi>\<rangle> = \<langle>yvec, \<Psi>'\<rangle>` `xvec = x # xvec'`
    obtain y yvec' where "\<langle>(x#xvec'), \<Psi>\<rangle> = \<langle>(y#yvec'), \<Psi>'\<rangle>"
      and "yvec = y#yvec'"
      by(case_tac yvec) auto
    hence EQ: "\<lparr>\<nu>x\<rparr>\<lparr>\<nu>*xvec'\<rparr>(FAssert \<Psi>) = \<lparr>\<nu>y\<rparr>\<lparr>\<nu>*yvec'\<rparr>(FAssert \<Psi>')"
      by simp
    have IH: "\<And>xvec yvec \<Psi> \<Psi>'. \<lbrakk>\<langle>xvec, (\<Psi>::'a)\<rangle> = \<langle>yvec, (\<Psi>'::'a)\<rangle>; supp \<Psi> = ({}::name set); n = length xvec\<rbrakk> \<Longrightarrow> \<Psi> = \<Psi>'"
      by fact
    show ?case
    proof(case_tac "x = y")
      assume "x = y"
      with EQ have "\<langle>xvec', \<Psi>\<rangle> = \<langle>yvec', \<Psi>'\<rangle>"
        by(simp add: alpha frame.inject)
      with IH `length xvec' = n` `supp \<Psi> = {}` show ?case
        by simp
    next
      assume "x \<noteq> y"
      with EQ have "\<langle>xvec', \<Psi>\<rangle> = [(x, y)] \<bullet> \<langle>yvec', \<Psi>'\<rangle>"
        by(simp add: alpha frame.inject)
      hence "\<langle>xvec', \<Psi>\<rangle> = \<langle>([(x, y)] \<bullet> yvec'), ([(x, y)] \<bullet> \<Psi>')\<rangle>"
        by(simp add: eqvts)
      with IH `length xvec' = n` `supp \<Psi> = {}` have "\<Psi> = [(x, y)] \<bullet> \<Psi>'"
        by(simp add: eqvts)
      moreover with `supp \<Psi> = {}` have "supp([(x, y)] \<bullet> \<Psi>') = ({}::name set)"
        by simp
      hence "x \<sharp> ([(x, y)] \<bullet> \<Psi>')" and "y \<sharp> ([(x, y)] \<bullet> \<Psi>')"
        by(simp add: fresh_def)+
      with `x \<noteq> y` have "x \<sharp> \<Psi>'" and "y \<sharp> \<Psi>'"
        by(simp add: fresh_left calc_atm)+
      ultimately show ?case by simp
    qed
  qed
qed

lemma frameChainEq:
  fixes xvec :: "name list"
  and   \<Psi>    :: "'a::fs_name"
  and   yvec :: "name list"
  and   \<Psi>'   :: "'a::fs_name"

  assumes "\<langle>xvec, \<Psi>\<rangle> = \<langle>yvec, \<Psi>'\<rangle>"
  and     "xvec \<sharp>* yvec"

  obtains p where "(set p) \<subseteq> (set xvec) \<times> set (yvec)" and "distinctPerm p" and "\<Psi>' = p \<bullet> \<Psi>"
proof -
  assume "\<And>p. \<lbrakk>set p \<subseteq> set xvec \<times> set yvec; distinctPerm p; \<Psi>' = p \<bullet> \<Psi>\<rbrakk> \<Longrightarrow> thesis"
  moreover obtain n where "n = length xvec" by auto
  with assms have "\<exists>p. (set p) \<subseteq> (set xvec) \<times> set (yvec) \<and> distinctPerm p \<and>  \<Psi>' = p \<bullet> \<Psi>"
  proof(induct n arbitrary: xvec yvec \<Psi> \<Psi>')
    case(0 xvec yvec \<Psi> \<Psi>')
    have Eq: "\<langle>xvec, \<Psi>\<rangle> = \<langle>yvec, \<Psi>'\<rangle>" by fact
    from `0 = length xvec` have "xvec = []" by auto
    moreover with Eq have "yvec = []"
      by(case_tac yvec) auto
    ultimately show ?case using Eq
      by(simp add: frame.inject)
  next
    case(Suc n xvec yvec \<Psi> \<Psi>')
    from `Suc n = length xvec`
    obtain x xvec' where "xvec = x#xvec'" and "length xvec' = n"
      by(case_tac xvec) auto
    from `\<langle>xvec, \<Psi>\<rangle> = \<langle>yvec, \<Psi>'\<rangle>` `xvec = x # xvec'`
    obtain y yvec' where "\<langle>(x#xvec'), \<Psi>\<rangle> = \<langle>(y#yvec'), \<Psi>'\<rangle>"
      and "yvec = y#yvec'"
      by(case_tac yvec) auto
    hence EQ: "\<lparr>\<nu>x\<rparr>\<lparr>\<nu>*xvec'\<rparr>(FAssert \<Psi>) = \<lparr>\<nu>y\<rparr>\<lparr>\<nu>*yvec'\<rparr>(FAssert \<Psi>')"
      by simp
    from `xvec = x#xvec'` `yvec=y#yvec'` `xvec \<sharp>* yvec`
    have "x \<noteq> y" and "xvec' \<sharp>* yvec'" and "x \<sharp> yvec'" and "y \<sharp> xvec'"
      by auto
    have IH: "\<And>xvec yvec \<Psi> \<Psi>'. \<lbrakk>\<langle>xvec, (\<Psi>::'a)\<rangle> = \<langle>yvec, (\<Psi>'::'a)\<rangle>; xvec \<sharp>* yvec; n = length xvec\<rbrakk> \<Longrightarrow>
                                 \<exists>p. (set p) \<subseteq> (set xvec) \<times> (set yvec) \<and> distinctPerm p \<and>  \<Psi>' = p \<bullet> \<Psi>"
      by fact

    from EQ `x \<noteq> y` have EQ': "\<langle>xvec', \<Psi>\<rangle> = ([(x, y)] \<bullet> \<langle>yvec', \<Psi>'\<rangle>)" 
                     and xFresh_\<Psi>': "x \<sharp> \<lparr>\<nu>*yvec'\<rparr>(FAssert \<Psi>')"
      by(simp add: frame.inject alpha)+

    show ?case
    proof(case_tac "x \<sharp> \<langle>xvec', \<Psi>\<rangle>")
      assume "x \<sharp> \<langle>xvec', \<Psi>\<rangle>"
      with EQ have "y \<sharp> \<langle>yvec', \<Psi>'\<rangle>"
        by(rule frameEqFresh)
      with xFresh_\<Psi>' EQ' have "\<langle>xvec', \<Psi>\<rangle> = \<langle>yvec', \<Psi>'\<rangle>" 
        by(simp)
      with `xvec' \<sharp>* yvec'` `length xvec' = n` IH
      obtain p where S: "(set p) \<subseteq> (set xvec') \<times> (set yvec')" and "distinctPerm p"  and "\<Psi>' = p \<bullet> \<Psi>"
        by blast
      from S have "(set p) \<subseteq> set(x#xvec') \<times> set(y#yvec')" by auto
      with `xvec = x#xvec'` `yvec=y#yvec'` `distinctPerm p` `\<Psi>' = p \<bullet> \<Psi>`
      show ?case by blast
    next
      assume "\<not>(x \<sharp> \<lparr>\<nu>*xvec'\<rparr>(FAssert \<Psi>))"
      hence xSupp_\<Psi>: "x \<in> supp(\<langle>xvec', \<Psi>\<rangle>)"
        by(simp add: fresh_def)
      with EQ have "y \<in> supp (\<langle>yvec', \<Psi>'\<rangle>)"
        by(rule frameEqSupp)
      hence "y \<sharp> yvec'"
        by(induct yvec') (auto simp add: frame.supp abs_supp)      
      with `x \<sharp> yvec'` EQ' have "\<langle>xvec', \<Psi>\<rangle> = \<langle>yvec', ([(x, y)] \<bullet> \<Psi>')\<rangle>"
        by(simp add: eqvts)
      with  `xvec' \<sharp>* yvec'` `length xvec' = n` IH
      obtain p where S: "(set p) \<subseteq> (set xvec') \<times> (set yvec')" and "distinctPerm p" and "([(x, y)] \<bullet> \<Psi>') = p \<bullet> \<Psi>"
        by blast

      from xSupp_\<Psi> have "x \<sharp> xvec'"
        by(induct xvec') (auto simp add: frame.supp abs_supp)      
      with `x \<sharp> yvec'` `y \<sharp> xvec'` `y \<sharp> yvec'` S have "x \<sharp> p" and "y \<sharp> p"
        apply(induct p)
        by(auto simp add: name_list_supp) (auto simp add: fresh_def) 
      from S have "(set ((x, y)#p)) \<subseteq> (set(x#xvec')) \<times> (set(y#yvec'))"
        by force
      moreover from `x \<noteq> y` `x \<sharp> p` `y \<sharp> p` S `distinctPerm p`
      have "distinctPerm((x,y)#p)" by simp
      moreover from `x \<sharp> p` `y \<sharp> p` `x \<sharp> xvec'` `y \<sharp> xvec'` have "y#(p \<bullet> xvec') = ((x, y)#p) \<bullet> (x#xvec')" 
        by(simp add: eqvts calc_atm freshChainSimps)
      moreover from `([(x, y)] \<bullet> \<Psi>') = p \<bullet> \<Psi>`
      have "([(x, y)] \<bullet> [(x, y)] \<bullet> \<Psi>') = [(x, y)] \<bullet> p \<bullet> \<Psi>"
        by(simp add: pt_bij)
      hence "\<Psi>' = ((x, y)#p) \<bullet> \<Psi>" by simp
      ultimately show ?case using `xvec=x#xvec'` `yvec=y#yvec'`
        by blast
    qed
  qed
  ultimately show ?thesis by blast
qed
(*
lemma frameChainEq'':
  fixes xvec :: "name list"
  and   \<Psi>    :: "'a::fs_name"
  and   yvec :: "name list"
  and   \<Psi>'   :: "'a::fs_name"

  assumes "\<langle>xvec, \<Psi>\<rangle> = \<langle>yvec, \<Psi>'\<rangle>"

  obtains p where "(set p) \<subseteq> (set xvec) \<times> set (yvec)" and "\<Psi>' = p \<bullet> \<Psi>"
proof -
  assume "\<And>p. \<lbrakk>set p \<subseteq> set xvec \<times> set yvec; \<Psi>' = p \<bullet> \<Psi>\<rbrakk> \<Longrightarrow> thesis"
  moreover obtain n where "n = length xvec" by auto
  with assms have "\<exists>p. (set p) \<subseteq> (set xvec) \<times> set (yvec) \<and> \<Psi>' = p \<bullet> \<Psi>"
  proof(induct n arbitrary: xvec yvec \<Psi> \<Psi>')
    case(0 xvec yvec \<Psi> \<Psi>')
    have Eq: "\<langle>xvec, \<Psi>\<rangle> = \<langle>yvec, \<Psi>'\<rangle>" by fact
    from `0 = length xvec` have "xvec = []" by auto
    moreover with Eq have "yvec = []"
      by(case_tac yvec) auto
    ultimately show ?case using Eq
      by(simp add: frame.inject)
  next
    case(Suc n xvec yvec \<Psi> \<Psi>')
    from `Suc n = length xvec`
    obtain x xvec' where "xvec = x#xvec'" and "length xvec' = n"
      by(case_tac xvec) auto
    from `\<langle>xvec, \<Psi>\<rangle> = \<langle>yvec, \<Psi>'\<rangle>` `xvec = x # xvec'`
    obtain y yvec' where "\<langle>(x#xvec'), \<Psi>\<rangle> = \<langle>(y#yvec'), \<Psi>'\<rangle>"
      and "yvec = y#yvec'"
      by(case_tac yvec) auto
    hence EQ: "\<lparr>\<nu>x\<rparr>\<lparr>\<nu>*xvec'\<rparr>(FAssert \<Psi>) = \<lparr>\<nu>y\<rparr>\<lparr>\<nu>*yvec'\<rparr>(FAssert \<Psi>')"
      by simp
    have IH: "\<And>xvec yvec \<Psi> \<Psi>'. \<lbrakk>\<langle>xvec, (\<Psi>::'a)\<rangle> = \<langle>yvec, (\<Psi>'::'a)\<rangle>; n = length xvec\<rbrakk> \<Longrightarrow>
                                 \<exists>p. (set p) \<subseteq> (set xvec) \<times> (set yvec) \<and> \<Psi>' = p \<bullet> \<Psi>"
      by fact
    show ?case
    proof(cases "x=y")
      case True
      from EQ `x = y` have "\<langle>xvec', \<Psi>\<rangle> = \<langle>yvec', \<Psi>'\<rangle>" by(simp add: alpha frame.inject)
      then obtain p where S: "set p \<subseteq> set xvec' \<times> set yvec'" and "\<Psi>' = p \<bullet> \<Psi>" using `length xvec' = n` IH
        by blast
      from S have "set((x, y)#p) \<subseteq> set(x#xvec') \<times> set (y#yvec')" by auto
      moreover from `x = y` `\<Psi>' = p \<bullet> \<Psi>` have "\<Psi>' = ((x, y)#p) \<bullet> \<Psi>" by auto
      ultimately show ?thesis using `xvec = x#xvec'` `yvec = y#yvec'` by blast
    next
      case False
      from EQ `x \<noteq> y` have EQ': "\<langle>xvec', \<Psi>\<rangle> = ([(x, y)] \<bullet> \<langle>yvec', \<Psi>'\<rangle>)" 
                       and xFresh_\<Psi>': "x \<sharp> \<lparr>\<nu>*yvec'\<rparr>(FAssert \<Psi>')"
        by(simp add: frame.inject alpha)+
    
      show ?thesis
      proof(cases "x \<sharp> \<langle>xvec', \<Psi>\<rangle>")
        case True
        from EQ `x \<sharp> \<langle>xvec', \<Psi>\<rangle>` have "y \<sharp> \<langle>yvec', \<Psi>'\<rangle>"
          by(rule frameEqFresh)
        with xFresh_\<Psi>' EQ' have "\<langle>xvec', \<Psi>\<rangle> = \<langle>yvec', \<Psi>'\<rangle>" 
          by(simp)
        with `length xvec' = n` IH
        obtain p where S: "(set p) \<subseteq> (set xvec') \<times> (set yvec')" and "\<Psi>' = p \<bullet> \<Psi>"
          by blast
        from S have "(set p) \<subseteq> set(x#xvec') \<times> set(y#yvec')" by auto
        with `xvec = x#xvec'` `yvec=y#yvec'` `\<Psi>' = p \<bullet> \<Psi>`
        show ?thesis by blast
      next
        case False
        from `\<not>(x \<sharp> \<lparr>\<nu>*xvec'\<rparr>(FAssert \<Psi>))` have xSupp_\<Psi>: "x \<in> supp(\<langle>xvec', \<Psi>\<rangle>)"
          by(simp add: fresh_def)
        with EQ have "y \<in> supp (\<langle>yvec', \<Psi>'\<rangle>)"
          by(rule frameEqSupp)
        hence "y \<sharp> yvec'"
          by(induct yvec') (auto simp add: frame.supp abs_supp)

        with `x \<sharp> yvec'` EQ' have "\<langle>xvec', \<Psi>\<rangle> = \<langle>yvec', ([(x, y)] \<bullet> \<Psi>')\<rangle>"
          by(simp add: eqvts)
        with  `xvec' \<sharp>* yvec'` `length xvec' = n` IH
        obtain p where S: "(set p) \<subseteq> (set xvec') \<times> (set yvec')" and "distinctPerm p" and "([(x, y)] \<bullet> \<Psi>') = p \<bullet> \<Psi>"
          by blast
        
        from xSupp_\<Psi> have "x \<sharp> xvec'"
          by(induct xvec') (auto simp add: frame.supp abs_supp)      
        with `x \<sharp> yvec'` `y \<sharp> xvec'` `y \<sharp> yvec'` S have "x \<sharp> p" and "y \<sharp> p"
          apply(induct p)
          by(auto simp add: name_list_supp) (auto simp add: fresh_def) 
        from S have "(set ((x, y)#p)) \<subseteq> (set(x#xvec')) \<times> (set(y#yvec'))"
          by force
        moreover from `x \<noteq> y` `x \<sharp> p` `y \<sharp> p` S `distinctPerm p`
        have "distinctPerm((x,y)#p)" by simp
        moreover from `x \<sharp> p` `y \<sharp> p` `x \<sharp> xvec'` `y \<sharp> xvec'` have "y#(p \<bullet> xvec') = ((x, y)#p) \<bullet> (x#xvec')" 
          by(simp add: eqvts calc_atm freshChainSimps)
        moreover from `([(x, y)] \<bullet> \<Psi>') = p \<bullet> \<Psi>`
        have "([(x, y)] \<bullet> [(x, y)] \<bullet> \<Psi>') = [(x, y)] \<bullet> p \<bullet> \<Psi>"
          by(simp add: pt_bij)
        hence "\<Psi>' = ((x, y)#p) \<bullet> \<Psi>" by simp
        ultimately show ?case using `xvec=x#xvec'` `yvec=y#yvec'`
          by blast
      qed
    qed
    ultimately show ?thesis by blast
qed
*)
lemma frameChainEq':
  fixes xvec :: "name list"
  and   \<Psi>    :: "'a::fs_name"
  and   yvec :: "name list"
  and   \<Psi>'   :: "'a::fs_name"

  assumes "\<langle>xvec, \<Psi>\<rangle> = \<langle>yvec, \<Psi>'\<rangle>"
  and     "xvec \<sharp>* yvec"
  and     "distinct xvec"
  and     "distinct yvec"

  obtains p where "(set p) \<subseteq> (set xvec) \<times> set (p \<bullet> xvec)" and "distinctPerm p" and "yvec = p \<bullet> xvec" and "\<Psi>' = p \<bullet> \<Psi>"
proof -
  assume "\<And>p. \<lbrakk>set p \<subseteq> set xvec \<times> set (p \<bullet> xvec); distinctPerm p; yvec = p \<bullet> xvec; \<Psi>' = p \<bullet> \<Psi>\<rbrakk> \<Longrightarrow> thesis"
  moreover obtain n where "n = length xvec" by auto
  with assms have "\<exists>p. (set p) \<subseteq> (set xvec) \<times> set (yvec) \<and> distinctPerm p \<and>  yvec = p \<bullet> xvec \<and> \<Psi>' = p \<bullet> \<Psi>"
  proof(induct n arbitrary: xvec yvec \<Psi> \<Psi>')
    case(0 xvec yvec \<Psi> \<Psi>')
    have Eq: "\<langle>xvec, \<Psi>\<rangle> = \<langle>yvec, \<Psi>'\<rangle>" by fact
    from `0 = length xvec` have "xvec = []" by auto
    moreover with Eq have "yvec = []"
      by(case_tac yvec) auto
    ultimately show ?case using Eq
      by(simp add: frame.inject)
  next
    case(Suc n xvec yvec \<Psi> \<Psi>')
    from `Suc n = length xvec`
    obtain x xvec' where "xvec = x#xvec'" and "length xvec' = n"
      by(case_tac xvec) auto
    from `\<langle>xvec, \<Psi>\<rangle> = \<langle>yvec, \<Psi>'\<rangle>` `xvec = x # xvec'`
    obtain y yvec' where "\<langle>(x#xvec'), \<Psi>\<rangle> = \<langle>(y#yvec'), \<Psi>'\<rangle>"
      and "yvec = y#yvec'"
      by(case_tac yvec) auto
    hence EQ: "\<lparr>\<nu>x\<rparr>\<lparr>\<nu>*xvec'\<rparr>(FAssert \<Psi>) = \<lparr>\<nu>y\<rparr>\<lparr>\<nu>*yvec'\<rparr>(FAssert \<Psi>')"
      by simp
    from `xvec = x#xvec'` `yvec=y#yvec'` `xvec \<sharp>* yvec`
    have "x \<noteq> y" and "xvec' \<sharp>* yvec'" and "x \<sharp> yvec'" and "y \<sharp> xvec'"
      by auto
    from `distinct xvec` `distinct yvec` `xvec=x#xvec'` `yvec=y#yvec'` have "x \<sharp> xvec'" and "y \<sharp> yvec'" and "distinct xvec'" and "distinct yvec'"
      by simp+
    have IH: "\<And>xvec yvec \<Psi> \<Psi>'. \<lbrakk>\<langle>xvec, (\<Psi>::'a)\<rangle> = \<langle>yvec, (\<Psi>'::'a)\<rangle>; xvec \<sharp>* yvec; distinct xvec; distinct yvec; n = length xvec\<rbrakk> \<Longrightarrow> \<exists>p. (set p) \<subseteq> (set xvec) \<times> (set yvec) \<and> distinctPerm p \<and>  yvec = p \<bullet> xvec \<and> \<Psi>' = p \<bullet> \<Psi>"
      by fact
    from EQ `x \<noteq> y`  `x \<sharp> yvec'` `y \<sharp> yvec'` have "\<langle>xvec', \<Psi>\<rangle> = \<langle>yvec', ([(x, y)] \<bullet> \<Psi>')\<rangle>"
      by(simp add: frame.inject alpha eqvts)
    with `xvec' \<sharp>* yvec'` `distinct xvec'` `distinct yvec'` `length xvec' = n` IH
    obtain p where S: "(set p) \<subseteq> (set xvec') \<times> (set yvec')" and "distinctPerm p" and "yvec' = p \<bullet> xvec'" and "[(x, y)] \<bullet> \<Psi>' = p \<bullet> \<Psi>"
      by metis
    from S have "set((x, y)#p) \<subseteq> set(x#xvec') \<times> set(y#yvec')" by auto
    moreover from `x \<sharp> xvec'` `x \<sharp> yvec'` `y \<sharp> xvec'` `y \<sharp> yvec'` S have "x \<sharp> p" and "y \<sharp> p"
      apply(induct p)
      by(auto simp add: name_list_supp) (auto simp add: fresh_def) 

    with S `distinctPerm p` `x \<noteq> y` have "distinctPerm((x, y)#p)" by auto
    moreover from `yvec' = p \<bullet> xvec'` `x \<sharp> p` `y \<sharp> p` `x \<sharp> xvec'` `y \<sharp> xvec'` have "(y#yvec') = ((x, y)#p) \<bullet> (x#xvec')"
      by(simp add: freshChainSimps calc_atm)
    moreover from `([(x, y)] \<bullet> \<Psi>') = p \<bullet> \<Psi>`
    have "([(x, y)] \<bullet> [(x, y)] \<bullet> \<Psi>') = [(x, y)] \<bullet> p \<bullet> \<Psi>"
      by(simp add: pt_bij)
    hence "\<Psi>' = ((x, y)#p) \<bullet> \<Psi>"
      by simp
    ultimately show ?case using `xvec=x#xvec'` `yvec=y#yvec'`
      by blast
  qed
  ultimately show ?thesis by blast
qed

lemma frameEq[simp]:
  fixes A\<^isub>F :: "name list"
  and   \<Psi>  :: "'a::fs_name"
  and   \<Psi>'  :: 'a

  shows "\<langle>A\<^isub>F, \<Psi>\<rangle> = \<langle>\<epsilon>, \<Psi>'\<rangle> = (A\<^isub>F = [] \<and> \<Psi> = \<Psi>')"
  and   "\<langle>\<epsilon>, \<Psi>'\<rangle> = \<langle>A\<^isub>F, \<Psi>\<rangle>  = (A\<^isub>F = [] \<and> \<Psi> = \<Psi>')"
proof -
  {
    assume "\<langle>A\<^isub>F, \<Psi>\<rangle> = \<langle>\<epsilon>, \<Psi>'\<rangle>"
    hence A: "\<langle>A\<^isub>F, \<Psi>\<rangle> = \<langle>[], \<Psi>'\<rangle>" by simp
    hence "length A\<^isub>F = length ([]::name list)"
      by(rule frameChainEqLength)
    with A have "A\<^isub>F = []" and "\<Psi> = \<Psi>'" by(auto simp add: frame.inject)
  }
  thus "\<langle>A\<^isub>F, \<Psi>\<rangle> = \<langle>\<epsilon>, \<Psi>'\<rangle> = (A\<^isub>F = [] \<and> \<Psi> = \<Psi>')"
  and  "\<langle>\<epsilon>, \<Psi>'\<rangle> = \<langle>A\<^isub>F, \<Psi>\<rangle>  = (A\<^isub>F = [] \<and> \<Psi> = \<Psi>')"
    by auto
qed

lemma distinctFrame:
  fixes A\<^isub>F :: "name list"
  and   \<Psi>\<^isub>F :: "'a::fs_name"
  and   C  :: "'b::fs_name"
  
  assumes "A\<^isub>F \<sharp>* C"

  obtains A\<^isub>F' where  "\<langle>A\<^isub>F, \<Psi>\<^isub>F\<rangle> = \<langle>A\<^isub>F', \<Psi>\<^isub>F\<rangle>" and "distinct A\<^isub>F'" and "A\<^isub>F' \<sharp>* C"
proof -
  assume "\<And>A\<^isub>F'. \<lbrakk>\<langle>A\<^isub>F, \<Psi>\<^isub>F\<rangle> = \<langle>A\<^isub>F', \<Psi>\<^isub>F\<rangle>; distinct A\<^isub>F'; A\<^isub>F' \<sharp>* C\<rbrakk> \<Longrightarrow> thesis"
  moreover from assms have "\<exists>A\<^isub>F'. \<langle>A\<^isub>F, \<Psi>\<^isub>F\<rangle> = \<langle>A\<^isub>F', \<Psi>\<^isub>F\<rangle> \<and> distinct A\<^isub>F' \<and> A\<^isub>F' \<sharp>* C"
  proof(induct A\<^isub>F)
    case Nil
    thus ?case by simp
  next
    case(Cons a A\<^isub>F)
    then obtain A\<^isub>F' where Eq: "\<langle>A\<^isub>F, \<Psi>\<^isub>F\<rangle> = \<langle>A\<^isub>F', \<Psi>\<^isub>F\<rangle>" and "distinct A\<^isub>F'" and "A\<^isub>F' \<sharp>* C" by force
    from `(a#A\<^isub>F) \<sharp>* C` have "a \<sharp> C" and "A\<^isub>F \<sharp>* C" by simp+
    show ?case
    proof(case_tac "a \<sharp> \<langle>A\<^isub>F', \<Psi>\<^isub>F\<rangle>")
      assume "a \<sharp> \<langle>A\<^isub>F', \<Psi>\<^isub>F\<rangle>"
      obtain b::name where "b \<sharp> A\<^isub>F'" and "b \<sharp> \<Psi>\<^isub>F" and "b \<sharp> C" by(generate_fresh "name", auto)
      have "\<langle>(a#A\<^isub>F), \<Psi>\<^isub>F\<rangle> = \<langle>(b#A\<^isub>F'), \<Psi>\<^isub>F\<rangle>"
      proof -
        from Eq have "\<langle>(a#A\<^isub>F), \<Psi>\<^isub>F\<rangle> = \<langle>(a#A\<^isub>F'), \<Psi>\<^isub>F\<rangle>" by(simp add: frame.inject)
        moreover from `b \<sharp> \<Psi>\<^isub>F` have "\<dots> = \<lparr>\<nu>b\<rparr>([(a, b)] \<bullet> \<lparr>\<nu>*A\<^isub>F'\<rparr>(FAssert \<Psi>\<^isub>F))"
          by(force intro: alphaFrameRes simp add: frameResChainFresh)
        ultimately show ?thesis using `a \<sharp> \<langle>A\<^isub>F', \<Psi>\<^isub>F\<rangle>` `b \<sharp> \<Psi>\<^isub>F`
          by(simp add: frameResChainFresh)
      qed
      moreover from `distinct A\<^isub>F'` `b \<sharp> A\<^isub>F'` have "distinct(b#A\<^isub>F')" by simp
      moreover from `A\<^isub>F' \<sharp>* C` `b \<sharp> C` have "(b#A\<^isub>F') \<sharp>* C" by simp+
      ultimately show ?case by blast
    next
      from Eq have "\<langle>(a#A\<^isub>F), \<Psi>\<^isub>F\<rangle> = \<langle>(a#A\<^isub>F'), \<Psi>\<^isub>F\<rangle>" by(simp add: frame.inject)
      moreover assume "\<not>(a \<sharp> \<langle>A\<^isub>F', \<Psi>\<^isub>F\<rangle>)"
      hence "a \<sharp> A\<^isub>F'" apply(simp add: fresh_def)
        by(induct A\<^isub>F') (auto simp add: supp_list_nil supp_list_cons supp_atm frame.supp abs_supp)
      with `distinct A\<^isub>F'` have "distinct(a#A\<^isub>F')" by simp
      moreover from `A\<^isub>F' \<sharp>* C` `a \<sharp> C` have "(a#A\<^isub>F') \<sharp>* C" by simp+
      ultimately show ?case by blast
    qed
  qed
  ultimately show ?thesis using `A\<^isub>F \<sharp>* C`
    by blast
qed

lemma freshFrame:
  fixes F  :: "('a::fs_name) frame"
  and   C  :: "'b ::fs_name"

  obtains A\<^isub>F \<Psi>\<^isub>F where "F = \<langle>A\<^isub>F, \<Psi>\<^isub>F\<rangle>" and "distinct A\<^isub>F" and "A\<^isub>F \<sharp>* C"
proof -
  assume "\<And>A\<^isub>F \<Psi>\<^isub>F. \<lbrakk>F = \<langle>A\<^isub>F, \<Psi>\<^isub>F\<rangle>; distinct A\<^isub>F; A\<^isub>F \<sharp>* C\<rbrakk> \<Longrightarrow> thesis"
  moreover have "\<exists>A\<^isub>F \<Psi>\<^isub>F. F = \<langle>A\<^isub>F, \<Psi>\<^isub>F\<rangle> \<and> A\<^isub>F \<sharp>* C"
  proof(nominal_induct F avoiding: C rule: frame.strong_induct)
    case(FAssert \<Psi>\<^isub>F)
    have "FAssert \<Psi>\<^isub>F = \<langle>[], \<Psi>\<^isub>F\<rangle>" by simp
    moreover have "([]::name list) \<sharp>* C" by simp
    ultimately show ?case by force
  next
    case(FRes a F)
    from `\<And>C. \<exists>A\<^isub>F \<Psi>\<^isub>F. F = \<langle>A\<^isub>F, \<Psi>\<^isub>F\<rangle> \<and> A\<^isub>F \<sharp>* C`
    obtain A\<^isub>F \<Psi>\<^isub>F  where "F = \<langle>A\<^isub>F, \<Psi>\<^isub>F\<rangle>" and "A\<^isub>F \<sharp>* C"
      by blast
    with `a \<sharp> C` have "\<lparr>\<nu>a\<rparr>F = \<lparr>\<nu>*(a#A\<^isub>F)\<rparr>(FAssert \<Psi>\<^isub>F)" and "(a#A\<^isub>F) \<sharp>* C"
      by simp+
    thus ?case by blast
  qed
  ultimately show ?thesis
    by(auto, rule_tac distinctFrame) auto
qed

locale assertionAux = 
  fixes SCompose :: "'b::fs_name \<Rightarrow> 'b \<Rightarrow> 'b"   (infixr "\<otimes>" 80)
  and   SImp     :: "'b \<Rightarrow> 'c::fs_name \<Rightarrow> bool" ("_ \<turnstile> _" [70, 70] 70)
  and   SBottom  :: 'b                         ("\<bottom>" 90) 
  and   SChanEq  :: "'a::fs_name \<Rightarrow> 'a \<Rightarrow> 'c"   ("_ \<leftrightarrow> _" [80, 80] 80)

  assumes statEqvt[eqvt]:   "\<And>p::name prm. p \<bullet> (\<Psi> \<turnstile> \<Phi>) = (p \<bullet> \<Psi>) \<turnstile> (p \<bullet> \<Phi>)"
  and     statEqvt'[eqvt]:  "\<And>p::name prm. p \<bullet> (\<Psi> \<otimes> \<Psi>') = (p \<bullet> \<Psi>) \<otimes> (p \<bullet> \<Psi>')" 
  and     statEqvt''[eqvt]: "\<And>p::name prm. p \<bullet> (M \<leftrightarrow> N) = (p \<bullet> M) \<leftrightarrow> (p \<bullet> N)"
  and     permBottom[eqvt]: "\<And>p::name prm. (p \<bullet> SBottom) = SBottom"

begin

lemma statClosed:
  fixes \<Psi> :: 'b
  and   \<phi> :: 'c
  and   p :: "name prm"
  
  assumes "\<Psi> \<turnstile> \<phi>"

  shows "(p \<bullet> \<Psi>) \<turnstile> (p \<bullet> \<phi>)"
using assms statEqvt
by(simp add: perm_bool)

lemma compSupp:
  fixes \<Psi>  :: 'b
  and   \<Psi>' :: 'b

  shows "(supp(\<Psi> \<otimes> \<Psi>')::name set) \<subseteq> ((supp \<Psi>) \<union> (supp \<Psi>'))"
proof(auto simp add: eqvts supp_def)
  fix x::name
  let ?P = "\<lambda>y. ([(x, y)] \<bullet> \<Psi>) \<otimes> [(x, y)] \<bullet> \<Psi>' \<noteq> \<Psi> \<otimes> \<Psi>'"
  let ?Q = "\<lambda>y \<Psi>. ([(x, y)] \<bullet> \<Psi>) \<noteq> \<Psi>"
  assume "finite {y. ?Q y \<Psi>'}"
  moreover assume "finite {y. ?Q y \<Psi>}" and "infinite {y. ?P(y)}"
  hence "infinite({y. ?P(y)} - {y. ?Q y \<Psi>})" by(rule Diff_infinite_finite)
  ultimately have "infinite(({y. ?P(y)} - {y. ?Q y \<Psi>}) - {y. ?Q y \<Psi>'})" by(rule Diff_infinite_finite)
  hence "infinite({y. ?P(y) \<and> \<not>(?Q y \<Psi>) \<and> \<not> (?Q y \<Psi>')})" by(simp add: set_diff_eq)
  moreover have "{y. ?P(y) \<and> \<not>(?Q y \<Psi>) \<and> \<not> (?Q y \<Psi>')} = {}" by auto
  ultimately have "infinite {}" by(drule_tac Infinite_cong) auto
  thus False by simp
qed

lemma chanEqSupp:
  fixes M :: 'a
  and   N :: 'a

  shows "(supp(M \<leftrightarrow> N)::name set) \<subseteq> ((supp M) \<union> (supp N))"
proof(auto simp add: eqvts supp_def)
  fix x::name
  let ?P = "\<lambda>y. ([(x, y)] \<bullet> M) \<leftrightarrow> [(x, y)] \<bullet> N \<noteq> M \<leftrightarrow> N"
  let ?Q = "\<lambda>y M. ([(x, y)] \<bullet> M) \<noteq> M"
  assume "finite {y. ?Q y N}"
  moreover assume "finite {y. ?Q y M}" and "infinite {y. ?P(y)}"
  hence "infinite({y. ?P(y)} - {y. ?Q y M})" by(rule Diff_infinite_finite)
  ultimately have "infinite(({y. ?P(y)} - {y. ?Q y M}) - {y. ?Q y N})" by(rule Diff_infinite_finite)
  hence "infinite({y. ?P(y) \<and> \<not>(?Q y M) \<and> \<not> (?Q y N)})" by(simp add: set_diff_eq)
  moreover have "{y. ?P(y) \<and> \<not>(?Q y M) \<and> \<not> (?Q y N)} = {}" by auto
  ultimately have "infinite {}" by(drule_tac Infinite_cong) auto
  thus False by simp
qed

lemma freshComp[intro]:
  fixes x  :: name
  and   \<Psi>  :: 'b
  and   \<Psi>' :: 'b

  assumes "x \<sharp> \<Psi>"
  and     "x \<sharp> \<Psi>'"

  shows "x \<sharp> \<Psi> \<otimes> \<Psi>'"
using assms compSupp
by(auto simp add: fresh_def)

lemma freshCompChain[intro]:
  fixes xvec  :: "name list"
  and   Xs    :: "name set"
  and   \<Psi>     :: 'b
  and   \<Psi>'    :: 'b

  shows "\<lbrakk>xvec \<sharp>* \<Psi>; xvec \<sharp>* \<Psi>'\<rbrakk> \<Longrightarrow> xvec \<sharp>* (\<Psi> \<otimes> \<Psi>')"
  and   "\<lbrakk>Xs \<sharp>* \<Psi>; Xs \<sharp>* \<Psi>'\<rbrakk> \<Longrightarrow> Xs \<sharp>* (\<Psi> \<otimes> \<Psi>')"
by(auto simp add: fresh_star_def)

lemma freshChanEq[intro]:
  fixes x :: name
  and   M :: 'a
  and   N :: 'a

  assumes "x \<sharp> M"
  and     "x \<sharp> N"

  shows "x \<sharp> M \<leftrightarrow> N"
using assms chanEqSupp
by(auto simp add: fresh_def)

lemma freshChanEqChain[intro]:
  fixes xvec :: "name list"
  and   Xs   :: "name set"
  and   M    :: 'a
  and   N    :: 'a

  shows "\<lbrakk>xvec \<sharp>* M; xvec \<sharp>* N\<rbrakk> \<Longrightarrow> xvec \<sharp>* (M \<leftrightarrow> N)"
  and   "\<lbrakk>Xs \<sharp>* M; Xs \<sharp>* N\<rbrakk> \<Longrightarrow> Xs \<sharp>* (M \<leftrightarrow> N)"
by(auto simp add: fresh_star_def)

lemma suppBottom[simp]:
  shows "((supp SBottom)::name set) = {}"
by(auto simp add: supp_def permBottom)

lemma freshBottom[simp]:
  fixes x :: name
  
  shows "x \<sharp> \<bottom>"
by(simp add: fresh_def)

lemma freshBottoChain[simp]:
  fixes xvec :: "name list"
  and   Xs   :: "name set"

  shows "xvec \<sharp>* (\<bottom>)"
  and   "Xs   \<sharp>* (\<bottom>)"
by(auto simp add: fresh_star_def)

lemma chanEqClosed:
  fixes \<Psi> :: 'b
  and   M :: 'a
  and   N :: 'a
  and   p :: "name prm"
 
  assumes "\<Psi> \<turnstile> M \<leftrightarrow> N"

  shows "(p \<bullet> \<Psi>) \<turnstile> (p \<bullet> M) \<leftrightarrow> (p \<bullet> N)"
proof -
  from `\<Psi> \<turnstile> M \<leftrightarrow> N` have "(p \<bullet> \<Psi>) \<turnstile> p \<bullet> (M \<leftrightarrow> N)"
    by(rule statClosed)
  thus ?thesis by(simp add: eqvts)
qed

definition
  AssertionStatImp :: "'b \<Rightarrow> 'b \<Rightarrow> bool" (infix "\<hookrightarrow>" 70)
  where "(\<Psi> \<hookrightarrow> \<Psi>') \<equiv> (\<forall>\<Phi>. \<Psi> \<turnstile> \<Phi> \<longrightarrow> \<Psi>' \<turnstile> \<Phi>)"

definition
  AssertionStatEq :: "'b \<Rightarrow> 'b \<Rightarrow> bool" (infix "\<simeq>" 70)
  where "(\<Psi> \<simeq> \<Psi>') \<equiv> \<Psi> \<hookrightarrow> \<Psi>' \<and> \<Psi>' \<hookrightarrow> \<Psi>"

lemma statImpEnt:
  fixes \<Psi>  :: 'b
  and   \<Psi>' :: 'b
  and   \<Phi>  :: 'c

  assumes "\<Psi> \<hookrightarrow> \<Psi>'"
  and     "\<Psi> \<turnstile> \<Phi>"

  shows "\<Psi>' \<turnstile> \<Phi>"
using assms
by(simp add: AssertionStatImp_def)

lemma statEqEnt:
  fixes \<Psi>  :: 'b
  and   \<Psi>' :: 'b
  and   \<Phi>  :: 'c

  assumes "\<Psi> \<simeq> \<Psi>'"
  and     "\<Psi> \<turnstile> \<Phi>"

  shows "\<Psi>' \<turnstile> \<Phi>"
using assms
by(auto simp add: AssertionStatEq_def intro: statImpEnt)

lemma AssertionStatImpClosed:
  fixes \<Psi>  :: 'b
  and   \<Psi>' :: 'b
  and   p  :: "name prm"

  assumes "\<Psi> \<hookrightarrow> \<Psi>'"

  shows "(p \<bullet> \<Psi>) \<hookrightarrow> (p \<bullet> \<Psi>')"
proof(auto simp add: AssertionStatImp_def)
  fix \<phi>
  assume "(p \<bullet> \<Psi>) \<turnstile> \<phi>"
  hence "\<Psi> \<turnstile> rev p \<bullet> \<phi>" by(drule_tac p="rev p" in statClosed) auto
  with `\<Psi> \<hookrightarrow> \<Psi>'` have "\<Psi>' \<turnstile> rev p \<bullet> \<phi>" by(simp add: AssertionStatImp_def)
  thus "(p \<bullet> \<Psi>') \<turnstile> \<phi>" by(drule_tac p=p in statClosed) auto
qed

lemma AssertionStatEqClosed:
  fixes \<Psi>  :: 'b
  and   \<Psi>' :: 'b
  and   p  :: "name prm"

  assumes "\<Psi> \<simeq> \<Psi>'"

  shows "(p \<bullet> \<Psi>) \<simeq> (p \<bullet> \<Psi>')"
using assms
by(auto simp add: AssertionStatEq_def intro: AssertionStatImpClosed)

lemma AssertionStatImpEqvt[eqvt]:
  fixes \<Psi>  :: 'b
  and   \<Psi>' :: 'b
  and   p  :: "name prm"

  shows "(p \<bullet> (\<Psi> \<hookrightarrow> \<Psi>')) = ((p \<bullet> \<Psi>) \<hookrightarrow> (p \<bullet> \<Psi>'))"
by(simp add: AssertionStatImp_def eqvts)

lemma AssertionStatEqEqvt[eqvt]:
  fixes \<Psi>  :: 'b
  and   \<Psi>' :: 'b
  and   p  :: "name prm"

  shows "(p \<bullet> (\<Psi> \<simeq> \<Psi>')) = ((p \<bullet> \<Psi>) \<simeq> (p \<bullet> \<Psi>'))"
by(simp add: AssertionStatEq_def eqvts)

lemma AssertionStatImpRefl[simp]:
  fixes \<Psi> :: 'b

  shows "\<Psi> \<hookrightarrow> \<Psi>"
by(simp add: AssertionStatImp_def)

lemma AssertionStatEqRefl[simp]:
  fixes \<Psi> :: 'b

  shows "\<Psi> \<simeq> \<Psi>"
by(simp add: AssertionStatEq_def)

lemma AssertionStatEqSym:
  fixes \<Psi>   :: 'b
  and   \<Psi>'  :: 'b

  assumes "\<Psi> \<simeq> \<Psi>'"

  shows "\<Psi>' \<simeq> \<Psi>"
using assms
by(auto simp add: AssertionStatEq_def)

lemma AssertionStatImpTrans:
  fixes \<Psi>   :: 'b
  and   \<Psi>'  :: 'b
  and   \<Psi>'' :: 'b

  assumes "\<Psi> \<hookrightarrow> \<Psi>'"
  and     "\<Psi>' \<hookrightarrow> \<Psi>''"

  shows "\<Psi> \<hookrightarrow> \<Psi>''"
using assms
by(simp add: AssertionStatImp_def)

lemma AssertionStatEqTrans:
  fixes \<Psi>   :: 'b
  and   \<Psi>'  :: 'b
  and   \<Psi>'' :: 'b

  assumes "\<Psi> \<simeq> \<Psi>'"
  and     "\<Psi>' \<simeq> \<Psi>''"

  shows "\<Psi> \<simeq> \<Psi>''"
using assms
by(auto simp add: AssertionStatEq_def intro: AssertionStatImpTrans)

definition 
  FrameImp :: "'b::fs_name frame \<Rightarrow> 'c \<Rightarrow> bool"   (infixl "\<turnstile>\<^sub>F" 70)
  where "(F \<turnstile>\<^sub>F \<Phi>) = (\<exists>A\<^isub>F \<Psi>\<^isub>F. F = \<langle>A\<^isub>F, \<Psi>\<^isub>F\<rangle> \<and> A\<^isub>F \<sharp>* \<Phi> \<and> (\<Psi>\<^isub>F \<turnstile> \<Phi>))"

lemma frameImpI:
  fixes F  :: "'b frame"
  and   \<phi>  :: 'c
  and   A\<^isub>F :: "name list"
  and   \<Psi>\<^isub>F :: 'b

  assumes "F = \<langle>A\<^isub>F, \<Psi>\<^isub>F\<rangle>"
  and     "A\<^isub>F \<sharp>* \<phi>"
  and     "\<Psi>\<^isub>F \<turnstile> \<phi>"

  shows "F \<turnstile>\<^sub>F \<phi>"
using assms
by(force simp add: FrameImp_def)

lemma frameImpAlphaEnt:
  fixes A\<^isub>F  :: "name list"
  and   \<Psi>\<^isub>F  :: 'b
  and   A\<^isub>F' :: "name list"
  and   \<Psi>\<^isub>F' :: 'b
  and   \<phi>   :: 'c

  assumes "\<langle>A\<^isub>F, \<Psi>\<^isub>F\<rangle> = \<langle>A\<^isub>F', \<Psi>\<^isub>F'\<rangle>" 
  and     "A\<^isub>F \<sharp>* \<phi>"
  and     "A\<^isub>F' \<sharp>* \<phi>"
  and     "\<Psi>\<^isub>F' \<turnstile> \<phi>"

  shows "\<Psi>\<^isub>F \<turnstile> \<phi>"
proof -
  from `\<langle>A\<^isub>F, \<Psi>\<^isub>F\<rangle> = \<langle>A\<^isub>F', \<Psi>\<^isub>F'\<rangle>`
  obtain n where "n = length A\<^isub>F" by blast
  moreover from `\<langle>A\<^isub>F, \<Psi>\<^isub>F\<rangle> = \<langle>A\<^isub>F', \<Psi>\<^isub>F'\<rangle>`
  have "length A\<^isub>F = length A\<^isub>F'"
    by(rule frameChainEqLength)
  ultimately show ?thesis using assms
  proof(induct n arbitrary: A\<^isub>F A\<^isub>F' \<Psi>\<^isub>F' rule: nat.induct)
    case(zero A\<^isub>F A\<^isub>F' \<Psi>\<^isub>F')
    thus ?case by(auto simp add: frame.inject)
  next
    case(Suc n A\<^isub>F A\<^isub>F' \<Psi>\<^isub>F')
    from `Suc n = length A\<^isub>F`
    obtain x xs where "A\<^isub>F = x#xs" and "n = length xs"
      by(case_tac A\<^isub>F) auto
    from `\<langle>A\<^isub>F, \<Psi>\<^isub>F\<rangle> = \<langle>A\<^isub>F', \<Psi>\<^isub>F'\<rangle>` `A\<^isub>F = x # xs`
    obtain y ys where "\<langle>(x#xs), \<Psi>\<^isub>F\<rangle> = \<langle>(y#ys), \<Psi>\<^isub>F'\<rangle>" and "A\<^isub>F' = y#ys"
      by(case_tac A\<^isub>F') auto
    hence EQ: "\<lparr>\<nu>x\<rparr>\<lparr>\<nu>*xs\<rparr>(FAssert \<Psi>\<^isub>F) = \<lparr>\<nu>y\<rparr>\<lparr>\<nu>*ys\<rparr>(FAssert \<Psi>\<^isub>F')"
      by simp
    from `A\<^isub>F = x # xs` `A\<^isub>F' = y # ys` `length A\<^isub>F = length A\<^isub>F'` `A\<^isub>F \<sharp>* \<phi>` `A\<^isub>F' \<sharp>* \<phi>`
    have "length xs = length ys" and "xs \<sharp>* \<phi>" and "ys \<sharp>* \<phi>" and "x \<sharp> \<phi>" and "y \<sharp> \<phi>" 
      by auto
    
    have IH: "\<And>xs ys \<Psi>\<^isub>F'. \<lbrakk>n = length xs; length xs = length ys; \<langle>xs, \<Psi>\<^isub>F\<rangle> = \<langle>ys, (\<Psi>\<^isub>F'::'b)\<rangle>; xs \<sharp>* \<phi>; ys \<sharp>* \<phi>; \<Psi>\<^isub>F' \<turnstile> \<phi>\<rbrakk> \<Longrightarrow> \<Psi>\<^isub>F \<turnstile> \<phi>"
      by fact
    show ?case
    proof(case_tac "x = y")
      assume "x = y"
      with EQ have "\<langle>xs, \<Psi>\<^isub>F\<rangle> = \<langle>ys, \<Psi>\<^isub>F'\<rangle>" by(simp add: alpha frame.inject)
      with IH `n = length xs` `length xs = length ys` `xs \<sharp>* \<phi>`  `ys \<sharp>* \<phi>` `\<Psi>\<^isub>F' \<turnstile> \<phi>`
      show ?case by blast
    next
      assume "x \<noteq> y"
      with EQ have "\<langle>xs, \<Psi>\<^isub>F\<rangle> = [(x, y)] \<bullet> \<langle>ys, \<Psi>\<^isub>F'\<rangle>" by(simp add: alpha frame.inject)
      hence "\<langle>xs, \<Psi>\<^isub>F\<rangle> = \<langle>([(x, y)] \<bullet> ys), ([(x, y)] \<bullet> \<Psi>\<^isub>F')\<rangle>" by(simp add: eqvts)
      moreover from `length xs = length ys` have "length xs = length([(x, y)] \<bullet> ys)"
        by auto
      moreover from `ys \<sharp>* \<phi>` have "([(x, y)] \<bullet> ys) \<sharp>* ([(x, y)] \<bullet> \<phi>)"
        by(simp add: fresh_star_bij)
      with `x \<sharp> \<phi>` `y \<sharp> \<phi>` have "([(x, y)] \<bullet> ys) \<sharp>* \<phi>"
        by simp
      moreover with `\<Psi>\<^isub>F' \<turnstile> \<phi>` have "([(x, y)] \<bullet> \<Psi>\<^isub>F') \<turnstile> ([(x, y)] \<bullet> \<phi>)"
        by(simp add: statClosed)
      with `x \<sharp> \<phi>` `y \<sharp> \<phi>` have "([(x, y)] \<bullet> \<Psi>\<^isub>F') \<turnstile> \<phi>"
        by simp
      ultimately show ?case using IH `n = length xs` `xs \<sharp>* \<phi>`
        by blast
    qed
  qed
qed

lemma frameImpEAux:
  fixes F  :: "'b frame"
  and   \<Phi>  :: 'c

  assumes  "F \<turnstile>\<^sub>F \<Phi>"
  and      "F = \<langle>A\<^isub>F, \<Psi>\<^isub>F\<rangle>"
  and      "A\<^isub>F \<sharp>* \<Phi>"
  
  shows "\<Psi>\<^isub>F \<turnstile> \<Phi>"
using assms
by(auto simp add: FrameImp_def dest: frameImpAlphaEnt)

lemma frameImpE:
  fixes F  :: "'b frame"
  and   \<Phi>  :: 'c

  assumes  "\<langle>A\<^isub>F, \<Psi>\<^isub>F\<rangle> \<turnstile>\<^sub>F \<Phi>"
  and      "A\<^isub>F \<sharp>* \<Phi>"
  
  shows "\<Psi>\<^isub>F \<turnstile> \<Phi>"
using assms
by(auto elim: frameImpEAux)

lemma frameImpClosed:
  fixes F :: "'b frame"
  and   \<Phi> :: 'c
  and   p :: "name prm"

  assumes "F \<turnstile>\<^sub>F \<Phi>"

  shows "(p \<bullet> F) \<turnstile>\<^sub>F (p \<bullet> \<Phi>)"
using assms
by(force simp add: FrameImp_def eqvts pt_fresh_star_bij[OF pt_name_inst, OF at_name_inst]
         intro: statClosed)

lemma frameImpEqvt[eqvt]:
  fixes F :: "'b frame"
  and   \<Phi> :: 'c
  and   p :: "name prm"

  shows "(p \<bullet> (F \<turnstile>\<^sub>F \<Phi>)) = (p \<bullet> F) \<turnstile>\<^sub>F (p \<bullet> \<Phi>)"
proof -
  have "F \<turnstile>\<^sub>F \<Phi> \<Longrightarrow> (p \<bullet> F) \<turnstile>\<^sub>F (p \<bullet> \<Phi>)"
    by(rule frameImpClosed)
  moreover have "(p \<bullet> F) \<turnstile>\<^sub>F (p \<bullet> \<Phi>) \<Longrightarrow> F \<turnstile>\<^sub>F \<Phi>"
    by(drule_tac p = "rev p" in frameImpClosed) simp
  ultimately show ?thesis
    by(auto simp add: perm_bool)
qed

lemma frameImpEmpty[simp]:
  fixes \<Psi> :: 'b
  and   \<phi> :: 'c

  shows "\<langle>\<epsilon>, \<Psi>\<rangle> \<turnstile>\<^sub>F \<phi> = \<Psi> \<turnstile> \<phi>" 
by(auto simp add: FrameImp_def)

definition
  FrameStatImp :: "'b frame \<Rightarrow> 'b frame\<Rightarrow> bool" (infix "\<hookrightarrow>\<^sub>F" 70)
  where "(F \<hookrightarrow>\<^sub>F G) \<equiv> (\<forall>\<phi>. F \<turnstile>\<^sub>F \<phi> \<longrightarrow> G \<turnstile>\<^sub>F \<phi>)"

definition
  FrameStatEq :: "'b frame \<Rightarrow> 'b frame\<Rightarrow> bool" (infix "\<simeq>\<^sub>F" 70)
  where "(F \<simeq>\<^sub>F G) \<equiv> F \<hookrightarrow>\<^sub>F G \<and> G \<hookrightarrow>\<^sub>F F"

lemma FrameStatImpClosed:
  fixes F :: "'b frame"
  and   G :: "'b frame"
  and   p :: "name prm"

  assumes "F \<hookrightarrow>\<^sub>F G"

  shows "(p \<bullet> F) \<hookrightarrow>\<^sub>F (p \<bullet> G)"
proof(auto simp add: FrameStatImp_def)
  fix \<phi>
  assume "(p \<bullet> F) \<turnstile>\<^sub>F \<phi>"
  hence "F \<turnstile>\<^sub>F rev p \<bullet> \<phi>" by(drule_tac p="rev p" in frameImpClosed) auto
  with `F \<hookrightarrow>\<^sub>F G` have "G \<turnstile>\<^sub>F rev p \<bullet> \<phi>" by(simp add: FrameStatImp_def)
  thus "(p \<bullet> G) \<turnstile>\<^sub>F \<phi>" by(drule_tac p=p in frameImpClosed) auto
qed

lemma FrameStatEqClosed:
  fixes F :: "'b frame"
  and   G :: "'b frame"
  and   p :: "name prm"

  assumes "F \<simeq>\<^sub>F G"

  shows "(p \<bullet> F) \<simeq>\<^sub>F (p \<bullet> G)"
using assms
by(auto simp add: FrameStatEq_def intro: FrameStatImpClosed)

lemma FrameStatImpEqvt[eqvt]:
  fixes F :: "'b frame"
  and   G :: "'b frame"
  and   p :: "name prm"

  shows "(p \<bullet> (F \<hookrightarrow>\<^sub>F G)) = ((p \<bullet> F) \<hookrightarrow>\<^sub>F (p \<bullet> G))"
by(simp add: FrameStatImp_def eqvts)

lemma FrameStatEqEqvt[eqvt]:
  fixes F :: "'b frame"
  and   G :: "'b frame"
  and   p :: "name prm"

  shows "(p \<bullet> (F \<simeq>\<^sub>F G)) = ((p \<bullet> F) \<simeq>\<^sub>F (p \<bullet> G))"
by(simp add: FrameStatEq_def eqvts)

lemma FrameStatImpRefl[simp]:
  fixes F :: "'b frame"

  shows "F \<hookrightarrow>\<^sub>F F"
by(simp add: FrameStatImp_def)

lemma FrameStatEqRefl[simp]:
  fixes F :: "'b frame"

  shows "F \<simeq>\<^sub>F F"
by(simp add: FrameStatEq_def)

lemma FrameStatEqSym:
  fixes F  :: "'b frame"
  and   G  :: "'b frame"

  assumes "F \<simeq>\<^sub>F G"

  shows "G \<simeq>\<^sub>F F"
using assms
by(auto simp add: FrameStatEq_def)

lemma FrameStatImpTrans:
  fixes F :: "'b frame"
  and   G :: "'b frame" 
  and   H :: "'b frame"

  assumes "F \<hookrightarrow>\<^sub>F G"
  and     "G \<hookrightarrow>\<^sub>F H"

  shows "F \<hookrightarrow>\<^sub>F H"
using assms
by(simp add: FrameStatImp_def)

lemma FrameStatEqTrans:
  fixes F :: "'b frame"
  and   G :: "'b frame"
  and   H :: "'b frame"

  assumes "F \<simeq>\<^sub>F G"
  and     "G \<simeq>\<^sub>F H"

  shows "F \<simeq>\<^sub>F H"
using assms
by(auto simp add: FrameStatEq_def intro: FrameStatImpTrans)

lemma fsCompose[simp]: "finite((supp SCompose)::name set)"
by(simp add: supp_def perm_fun_def eqvts)

nominal_primrec 
   insertAssertion :: "'b frame \<Rightarrow> 'b \<Rightarrow> 'b frame"
where
  "insertAssertion (FAssert \<Psi>) \<Psi>' = FAssert (\<Psi>' \<otimes> \<Psi>)"
| "x \<sharp> \<Psi>' \<Longrightarrow> insertAssertion (\<lparr>\<nu>x\<rparr>F) \<Psi>' = \<lparr>\<nu>x\<rparr>(insertAssertion F \<Psi>')"
apply(finite_guess add: fsCompose)+
apply(rule TrueI)+
apply(simp add: abs_fresh)
apply(rule supports_fresh[of "supp \<Psi>'"])
apply(force simp add: perm_fun_def eqvts fresh_def[symmetric] supports_def)
apply(simp add: fs_name1)
apply(simp add: fresh_def[symmetric])
apply(fresh_guess)+
done

lemma insertAssertionEqvt[eqvt]:
  fixes p :: "name prm"
  and   F :: "'b frame"
  and   \<Psi> :: 'b

  shows "p \<bullet> (insertAssertion F \<Psi>) = insertAssertion (p \<bullet> F) (p \<bullet> \<Psi>)"
by(nominal_induct F avoiding: p \<Psi> rule: frame.strong_induct)
  (auto simp add: at_prm_fresh[OF at_name_inst] 
                  pt_fresh_perm_app[OF pt_name_inst, OF at_name_inst] eqvts)


nominal_primrec 
   mergeFrame :: "'b frame \<Rightarrow> 'b frame \<Rightarrow> 'b frame"
where
  "mergeFrame (FAssert \<Psi>) G = insertAssertion G \<Psi>"
| "x \<sharp> G \<Longrightarrow> mergeFrame (\<lparr>\<nu>x\<rparr>F) G = \<lparr>\<nu>x\<rparr>(mergeFrame F G)"
apply(finite_guess add: fsCompose)+
apply(rule TrueI)+
apply(simp add: abs_fresh)
apply(simp add: fs_name1)
apply(rule supports_fresh[of "supp G"])
apply(force simp add: perm_fun_def eqvts fresh_def[symmetric] supports_def)
apply(simp add: fs_name1)
apply(simp add: fresh_def[symmetric])
apply(fresh_guess)+
done

notation mergeFrame (infixr "\<otimes>\<^sub>F" 80)

abbreviation
  frameBottomJudge ("\<bottom>\<^sub>F") where "\<bottom>\<^sub>F \<equiv> (FAssert SBottom)"

lemma mergeFrameEqvt[eqvt]:
  fixes p :: "name prm"
  and   F :: "'b frame"
  and   G :: "'b frame"

  shows "p \<bullet> (mergeFrame F G) = mergeFrame (p \<bullet> F) (p \<bullet> G)"
by(nominal_induct F avoiding: p G rule: frame.strong_induct)
  (auto simp add: at_prm_fresh[OF at_name_inst] 
                  pt_fresh_perm_app[OF pt_name_inst, OF at_name_inst] eqvts)

nominal_primrec
    extractFrame   :: "('a, 'b, 'c) psi \<Rightarrow> 'b frame"
and extractFrame'  :: "('a, 'b, 'c) input \<Rightarrow> 'b frame"
and extractFrame'' :: "('a, 'b, 'c) psiCase \<Rightarrow> 'b frame"

where
  "extractFrame (\<zero>) =  \<langle>\<epsilon>, \<bottom>\<rangle>"
| "extractFrame (M\<lparr>I) = \<langle>\<epsilon>, \<bottom>\<rangle>"
| "extractFrame (M\<langle>N\<rangle>.P) = \<langle>\<epsilon>, \<bottom>\<rangle>"
| "extractFrame (Case C) = \<langle>\<epsilon>, \<bottom>\<rangle>"
| "extractFrame (P \<parallel> Q) = (extractFrame P) \<otimes>\<^sub>F (extractFrame Q)"
| "extractFrame ((\<lbrace>\<Psi>\<rbrace>::('a, 'b, 'c) psi)) = \<langle>\<epsilon>, \<Psi>\<rangle>" 

| "extractFrame (\<lparr>\<nu>x\<rparr>P) = \<lparr>\<nu>x\<rparr>(extractFrame P)"
| "extractFrame (!P) = \<langle>\<epsilon>, \<bottom>\<rangle>" 

| "extractFrame' ((Trm M P)::('a::fs_name, 'b::fs_name, 'c::fs_name) input) = \<langle>\<epsilon>, \<bottom>\<rangle>" 
| "extractFrame' (Bind x I) = \<langle>\<epsilon>, \<bottom>\<rangle>" 

| "extractFrame'' (\<bottom>\<^sub>c::('a::fs_name, 'b::fs_name, 'c::fs_name) psiCase) = \<langle>\<epsilon>, \<bottom>\<rangle>" 
| "extractFrame'' (\<box>\<Phi> \<Rightarrow> P C) = \<langle>\<epsilon>, \<bottom>\<rangle>" 
apply(finite_guess add: fsCompose)+
apply(rule TrueI)+
apply(simp add: abs_fresh)+
apply(fresh_guess add: freshBottom)+
apply(rule supports_fresh[of "{}"])
apply(force simp add: perm_fun_def eqvts fresh_def[symmetric] supports_def)
apply(simp add: fs_name1)
apply(simp add: fresh_def[symmetric])
apply(fresh_guess add: freshBottom)+
apply(rule supports_fresh[of "{}"])
apply(force simp add: perm_fun_def eqvts fresh_def[symmetric] supports_def)
apply(simp add: fs_name1)
apply(simp add: fresh_def[symmetric])
apply(fresh_guess add: freshBottom)+
done

lemmas extractFrameSimps = extractFrame_extractFrame'_extractFrame''.simps

lemma extractFrameEqvt[eqvt]:
  fixes p :: "name prm"
  and   P :: "('a, 'b, 'c) psi"
  and   I :: "('a, 'b, 'c) input"
  and   C :: "('a, 'b, 'c) psiCase"

  shows "p \<bullet> (extractFrame P) = extractFrame (p \<bullet> P)"
  and   "p \<bullet> (extractFrame' I) = extractFrame' (p \<bullet> I)"
  and   "p \<bullet> (extractFrame'' C) = extractFrame'' (p \<bullet> C)"
by(nominal_induct P and I and C avoiding: p rule: psi_input_psiCase.strong_inducts)
   (auto simp add: at_prm_fresh[OF at_name_inst] eqvts permBottom
                  pt_fresh_perm_app[OF pt_name_inst, OF at_name_inst])

lemma insertAssertionFresh[intro]:
  fixes F :: "'b frame"
  and   \<Psi> :: 'b
  and   x :: name

  assumes "x \<sharp> F"
  and     "x \<sharp> \<Psi>"

  shows "x \<sharp> (insertAssertion F \<Psi>)"
using assms
by(nominal_induct F avoiding: x \<Psi> rule: frame.strong_induct)
  (auto simp add: abs_fresh)

lemma insertAssertionFreshChain[intro]:
  fixes F    :: "'b frame"
  and   \<Psi>    :: 'b
  and   xvec :: "name list"
  and   Xs   :: "name set"

  shows "\<lbrakk>xvec \<sharp>* F; xvec \<sharp>* \<Psi>\<rbrakk> \<Longrightarrow> xvec \<sharp>* (insertAssertion F \<Psi>)"
  and   "\<lbrakk>Xs \<sharp>* F; Xs \<sharp>* \<Psi>\<rbrakk> \<Longrightarrow> Xs \<sharp>* (insertAssertion F \<Psi>)"
by(auto simp add: fresh_star_def)

lemma mergeFrameFresh[intro]:
  fixes F :: "'b frame"
  and   G :: "'b frame"
  and   x :: name

  shows "\<lbrakk>x \<sharp> F; x \<sharp> G\<rbrakk> \<Longrightarrow> x \<sharp> (mergeFrame F G)"
by(nominal_induct F avoiding: x G rule: frame.strong_induct)
  (auto simp add: abs_fresh)

lemma mergeFrameFreshChain[intro]:
  fixes F    :: "'b frame"
  and   G    :: "'b frame"
  and   xvec :: "name list"
  and   Xs   :: "name set"

  shows "\<lbrakk>xvec \<sharp>* F; xvec \<sharp>* G\<rbrakk> \<Longrightarrow> xvec \<sharp>* (mergeFrame F G)"
  and   "\<lbrakk>Xs \<sharp>* F; Xs \<sharp>* G\<rbrakk> \<Longrightarrow> Xs \<sharp>* (mergeFrame F G)"
by(auto simp add: fresh_star_def)

lemma extractFrameFresh:
  fixes P :: "('a, 'b, 'c) psi"
  and   I :: "('a, 'b, 'c) input"
  and   C :: "('a, 'b, 'c) psiCase"
  and   x :: name

  shows "x \<sharp> P \<Longrightarrow> x \<sharp> extractFrame P"
  and   "x \<sharp> I \<Longrightarrow> x \<sharp> extractFrame' I"
  and   "x \<sharp> C \<Longrightarrow> x \<sharp> extractFrame'' C"
by(nominal_induct P and I and C avoiding: x rule: psi_input_psiCase.strong_inducts)
  (auto simp add: abs_fresh)

lemma extractFrameFreshChain:
  fixes P    :: "('a, 'b, 'c) psi"
  and   I    :: "('a, 'b, 'c) input"
  and   C    :: "('a, 'b, 'c) psiCase"
  and   xvec :: "name list"
  and   Xs   :: "name set"

  shows "xvec \<sharp>* P \<Longrightarrow> xvec \<sharp>* extractFrame P"
  and   "xvec \<sharp>* I \<Longrightarrow> xvec \<sharp>* extractFrame' I"
  and   "xvec \<sharp>* C \<Longrightarrow> xvec \<sharp>* extractFrame'' C"
  and   "Xs \<sharp>* P \<Longrightarrow> Xs \<sharp>* extractFrame P"
  and   "Xs \<sharp>* I \<Longrightarrow> Xs \<sharp>* extractFrame' I"
  and   "Xs \<sharp>* C \<Longrightarrow> Xs \<sharp>* extractFrame'' C"
by(auto simp add: fresh_star_def intro: extractFrameFresh)


lemma guardedFrameSupp[simp]:
  fixes P :: "('a, 'b, 'c) psi"
  and   I :: "('a, 'b, 'c) input"
  and   C :: "('a, 'b, 'c) psiCase"
  and   x :: name 

  shows "guarded P \<Longrightarrow> x \<sharp> (extractFrame P)"
  and   "guarded' I \<Longrightarrow> x \<sharp> (extractFrame' I)"
  and   "guarded'' C \<Longrightarrow> x \<sharp> (extractFrame'' C)"
by(nominal_induct P and I and C arbitrary: x rule: psi_input_psiCase.strong_inducts)
  (auto simp add: frameResChainFresh abs_fresh)

lemma frameResChainFresh': 
  fixes xvec :: "name list"
  and   yvec :: "name list"
  and   F    :: "'b frame"

  shows "(xvec \<sharp>* (\<lparr>\<nu>*yvec\<rparr>F)) = (\<forall>x \<in> set xvec. x \<in> set yvec \<or> x \<sharp> F)"
by(simp add: frameResChainFresh fresh_star_def)

lemma frameChainFresh[simp]:
  fixes xvec :: "name list"
  and   \<Psi>    :: 'b
  and   Xs   :: "name set"

  shows "xvec \<sharp>* (FAssert \<Psi>) = xvec \<sharp>* \<Psi>"
  and   "Xs \<sharp>* (FAssert \<Psi>) = Xs \<sharp>* \<Psi>"
by(simp add: fresh_star_def)+

lemma frameResChainFresh''[simp]:
  fixes xvec :: "name list"
  and   yvec :: "name list"
  and   F    :: "'b frame"
  
  assumes "xvec \<sharp>* yvec"

  shows "xvec \<sharp>* (\<lparr>\<nu>*yvec\<rparr>F) = xvec \<sharp>* F"

using assms
by(simp_all add: frameResChainFresh')
  (auto simp add: fresh_star_def fresh_def name_list_supp)

lemma frameResChainFresh'''[simp]:
  fixes x    :: name
  and   xvec :: "name list"
  and   F    :: "'b frame"
  
  assumes "x \<sharp> xvec"

  shows "x \<sharp> (\<lparr>\<nu>*xvec\<rparr>F) = x \<sharp> F"
using assms
by(induct xvec) (auto simp add: abs_fresh)

lemma FFreshBottom[simp]:
  fixes xvec :: "name list"
  and   Xs   :: "name set"

  shows "xvec \<sharp>* (\<bottom>\<^sub>F)"
  and   "Xs \<sharp>* (\<bottom>\<^sub>F)"
by(auto simp add: fresh_star_def)

lemma SFreshBottom[simp]:
  fixes xvec :: "name list"
  and   Xs   :: "name set"

  shows "xvec \<sharp>* (SBottom)"
  and   "Xs \<sharp>* (SBottom)"
by(auto simp add: fresh_star_def)
(*
lemma freshChainComp[simp]:
  fixes xvec :: "name list"
  and   Xs   :: "name set"
  and   \<Psi>    :: 'b
  and   \<Psi>'   :: 'b

  shows "xvec \<sharp>* (\<Psi> \<otimes> \<Psi>') = ((xvec \<sharp>* \<Psi>) \<and> xvec \<sharp>* \<Psi>')"
  and   "Xs \<sharp>* (\<Psi> \<otimes> \<Psi>') = ((Xs \<sharp>* \<Psi>) \<and> Xs \<sharp>* \<Psi>')"
by(auto simp add: fresh_star_def)
*)
lemma freshFrameDest[dest]:
  fixes A\<^isub>F    :: "name list"
  and   \<Psi>\<^isub>F   :: 'b
  and   xvec  :: "name list"

  assumes "xvec \<sharp>* (\<langle>A\<^isub>F, \<Psi>\<^isub>F\<rangle>)"

  shows "xvec \<sharp>* A\<^isub>F \<Longrightarrow> xvec \<sharp>* \<Psi>\<^isub>F"
  and   "A\<^isub>F \<sharp>* xvec \<Longrightarrow> xvec \<sharp>* \<Psi>\<^isub>F"
proof -
  from assms have "(set xvec) \<sharp>* (\<langle>A\<^isub>F, \<Psi>\<^isub>F\<rangle>)"
    by(simp add: fresh_star_def)
  moreover assume "xvec \<sharp>* A\<^isub>F"
  ultimately show "xvec \<sharp>* \<Psi>\<^isub>F"
    by(simp add: frameResChainFreshSet) (force simp add: fresh_def name_list_supp fresh_star_def)
next
  from assms have "(set xvec) \<sharp>* (\<langle>A\<^isub>F, \<Psi>\<^isub>F\<rangle>)"
    by(simp add: fresh_star_def)
  moreover assume "A\<^isub>F \<sharp>* xvec"
  ultimately show "xvec \<sharp>* \<Psi>\<^isub>F"
    by(simp add: frameResChainFreshSet) (force simp add: fresh_def name_list_supp fresh_star_def)
qed

lemma insertAssertionSimps[simp]:
  fixes A\<^isub>F :: "name list"
  and   \<Psi>\<^isub>F :: 'b
  and   \<Psi>  :: 'b
  
  assumes "A\<^isub>F \<sharp>* \<Psi>"

  shows "insertAssertion (\<langle>A\<^isub>F, \<Psi>\<^isub>F\<rangle>) \<Psi> = \<langle>A\<^isub>F, \<Psi> \<otimes> \<Psi>\<^isub>F\<rangle>"
using assms
by(induct A\<^isub>F arbitrary: F) auto

lemma mergeFrameSimps[simp]:
  fixes A\<^isub>F :: "name list"
  and   \<Psi>\<^isub>F :: 'b
  and   \<Psi>  :: 'b

  assumes "A\<^isub>F \<sharp>* \<Psi>"

  shows "(\<langle>A\<^isub>F, \<Psi>\<^isub>F\<rangle>) \<otimes>\<^sub>F \<langle>\<epsilon>, \<Psi>\<rangle> = \<langle>A\<^isub>F, \<Psi>\<^isub>F \<otimes> \<Psi>\<rangle>"
using assms
by(induct A\<^isub>F arbitrary: F) auto

lemma mergeFrames[simp]:
  fixes A\<^isub>F  :: "name list"
  and   \<Psi>\<^isub>F :: 'b
  and   A\<^isub>G  :: "name list"
  and   \<Psi>\<^isub>G :: 'b

  assumes "A\<^isub>F \<sharp>* A\<^isub>G"
  and     "A\<^isub>F \<sharp>* \<Psi>\<^isub>G"
  and     "A\<^isub>G \<sharp>* \<Psi>\<^isub>F"

  shows "(\<langle>A\<^isub>F, \<Psi>\<^isub>F\<rangle>) \<otimes>\<^sub>F (\<langle>A\<^isub>G, \<Psi>\<^isub>G\<rangle>) = (\<langle>(A\<^isub>F@A\<^isub>G), \<Psi>\<^isub>F \<otimes> \<Psi>\<^isub>G\<rangle>)"
using assms
by(induct A\<^isub>F) auto

lemma frameImpResFreshLeft:
  fixes F :: "'b frame"
  and   x :: name
  
  assumes "x \<sharp> F"

  shows "\<lparr>\<nu>x\<rparr>F \<hookrightarrow>\<^sub>F F"
proof(auto simp add: FrameStatImp_def)
  fix \<phi>::'c
  obtain A\<^isub>F \<Psi>\<^isub>F where Feq: "F = \<langle>A\<^isub>F, \<Psi>\<^isub>F\<rangle>" and "A\<^isub>F \<sharp>* (x, \<phi>)"
    by(rule freshFrame)
  from `A\<^isub>F \<sharp>* (x, \<phi>)` have "x \<sharp> A\<^isub>F" and "A\<^isub>F \<sharp>* \<phi>" by simp+
  obtain y where "y \<sharp> \<phi>" and "y \<sharp> F" and "x \<noteq> y"
    by(generate_fresh "name", auto)
  
  assume "\<lparr>\<nu>x\<rparr>F \<turnstile>\<^sub>F \<phi>"
  with `y \<sharp> F` have "\<lparr>\<nu>y\<rparr>([(x, y)] \<bullet> F) \<turnstile>\<^sub>F \<phi>" by(simp add: alphaFrameRes)
  with `x \<sharp> F` `y \<sharp> F` have "\<lparr>\<nu>y\<rparr>F \<turnstile>\<^sub>F \<phi>" by simp
  with Feq have "\<langle>(y#A\<^isub>F), \<Psi>\<^isub>F\<rangle> \<turnstile>\<^sub>F \<phi>" by simp
  with Feq `A\<^isub>F \<sharp>* \<phi>` `y \<sharp> \<phi>` show "F \<turnstile>\<^sub>F \<phi>"
    by(force intro: frameImpI dest: frameImpE simp del: frameResChain.simps)
qed

lemma frameImpResFreshRight:
  fixes F :: "'b frame"
  and   x :: name
  
  assumes "x \<sharp> F"

  shows "F \<hookrightarrow>\<^sub>F \<lparr>\<nu>x\<rparr>F"
proof(auto simp add: FrameStatImp_def)
  fix \<phi>::'c
  obtain A\<^isub>F \<Psi>\<^isub>F where Feq: "F = \<langle>A\<^isub>F, \<Psi>\<^isub>F\<rangle>" and "A\<^isub>F \<sharp>* (x, \<phi>)"
    by(rule freshFrame)
  from `A\<^isub>F \<sharp>* (x, \<phi>)` have "x \<sharp> A\<^isub>F" and "A\<^isub>F \<sharp>* \<phi>" by simp+
  obtain y where "y \<sharp> \<phi>" and "y \<sharp> F" and "x \<noteq> y"
    by(generate_fresh "name", auto)
  
  assume "F \<turnstile>\<^sub>F \<phi>"
  with Feq `A\<^isub>F \<sharp>* \<phi>` `y \<sharp> \<phi>` have "\<langle>(y#A\<^isub>F), \<Psi>\<^isub>F\<rangle> \<turnstile>\<^sub>F \<phi>"
    by(force intro: frameImpI dest: frameImpE simp del: frameResChain.simps)
  moreover with `y \<sharp> F` `x \<sharp> F` Feq show "\<lparr>\<nu>x\<rparr>F \<turnstile>\<^sub>F \<phi>"
    by(subst alphaFrameRes) auto
qed

lemma frameResFresh:
  fixes F :: "'b frame"
  and   x :: name
  
  assumes "x \<sharp> F"

  shows "\<lparr>\<nu>x\<rparr>F \<simeq>\<^sub>F F"
using assms
by(auto simp add: FrameStatEq_def intro: frameImpResFreshLeft frameImpResFreshRight)

lemma frameImpResPres:
  fixes F :: "'b frame"
  and   G :: "'b frame"
  and   x :: name
  
  assumes "F \<hookrightarrow>\<^sub>F G"

  shows "\<lparr>\<nu>x\<rparr>F \<hookrightarrow>\<^sub>F \<lparr>\<nu>x\<rparr>G"
proof(auto simp add: FrameStatImp_def)
  fix \<phi>::'c
  obtain A\<^isub>F \<Psi>\<^isub>F where Feq: "F = \<langle>A\<^isub>F, \<Psi>\<^isub>F\<rangle>" and "A\<^isub>F \<sharp>* (x, \<phi>)"
    by(rule freshFrame)
  from `A\<^isub>F \<sharp>* (x, \<phi>)` have "x \<sharp> A\<^isub>F" and "A\<^isub>F \<sharp>* \<phi>" by simp+
  obtain y where "y \<sharp> A\<^isub>F" and "y \<sharp> F" and "y \<sharp> G"
             and "x \<noteq> y" and "y \<sharp> \<phi>"
    by(generate_fresh "name", auto)
  assume "\<lparr>\<nu>x\<rparr>F \<turnstile>\<^sub>F \<phi>"
  with `y \<sharp> F` have "\<lparr>\<nu>y\<rparr>([(x, y)] \<bullet> F) \<turnstile>\<^sub>F \<phi>" by(simp add: alphaFrameRes)
  with Feq `x \<sharp> A\<^isub>F` `y \<sharp> A\<^isub>F` have "\<langle>(y#A\<^isub>F), [(x, y)] \<bullet> \<Psi>\<^isub>F\<rangle> \<turnstile>\<^sub>F \<phi>" by(simp add: eqvts)
  with `y \<sharp> \<phi>` `A\<^isub>F \<sharp>* \<phi>` have "\<langle>A\<^isub>F, [(x, y)] \<bullet> \<Psi>\<^isub>F\<rangle> \<turnstile>\<^sub>F \<phi>"
    by(force intro: frameImpI dest: frameImpE simp del: frameResChain.simps)
  hence "([(x, y)] \<bullet> \<langle>A\<^isub>F, [(x, y)] \<bullet> \<Psi>\<^isub>F\<rangle>) \<turnstile>\<^sub>F ([(x, y)] \<bullet> \<phi>)"
    by(rule frameImpClosed)
  with `x \<sharp> A\<^isub>F` `y \<sharp> A\<^isub>F` Feq have "F \<turnstile>\<^sub>F [(x, y)] \<bullet> \<phi>"
    by(simp add: eqvts)
  with `F \<hookrightarrow>\<^sub>F G` have "G \<turnstile>\<^sub>F [(x, y)] \<bullet> \<phi>" by(simp add: FrameStatImp_def)
  
  obtain A\<^isub>G \<Psi>\<^isub>G where Geq: "G = \<langle>A\<^isub>G, \<Psi>\<^isub>G\<rangle>" and "A\<^isub>G \<sharp>* (x, y, \<phi>)"
    by(rule freshFrame)
  from `A\<^isub>G \<sharp>* (x, y, \<phi>)` have "x \<sharp> A\<^isub>G" and "y \<sharp> A\<^isub>G" and "A\<^isub>G \<sharp>* \<phi>" by simp+
  from `G \<turnstile>\<^sub>F [(x, y)] \<bullet> \<phi>` have "([(x, y)] \<bullet> G) \<turnstile>\<^sub>F [(x, y)] \<bullet> [(x, y)] \<bullet> \<phi>"
    by(rule frameImpClosed)
  with Geq `x \<sharp> A\<^isub>G` `y \<sharp> A\<^isub>G` have "\<langle>A\<^isub>G, [(x, y)] \<bullet> \<Psi>\<^isub>G\<rangle> \<turnstile>\<^sub>F \<phi>" by(simp add: eqvts)
  with `y \<sharp> \<phi>` `A\<^isub>G \<sharp>* \<phi>` have "\<langle>(y#A\<^isub>G), [(x, y)] \<bullet> \<Psi>\<^isub>G\<rangle> \<turnstile>\<^sub>F \<phi>"
    by(force intro: frameImpI dest: frameImpE simp del: frameResChain.simps)
  with `y \<sharp> G` `x \<sharp> A\<^isub>G` `y \<sharp> A\<^isub>G` Geq show "\<lparr>\<nu>x\<rparr>G \<turnstile>\<^sub>F \<phi>"
    by(subst alphaFrameRes) (fastforce simp add: eqvts)+
qed

lemma frameResPres:
  fixes F :: "'b frame"
  and   G :: "'b frame"
  and   x :: name
  
  assumes "F \<simeq>\<^sub>F G"

  shows "\<lparr>\<nu>x\<rparr>F \<simeq>\<^sub>F \<lparr>\<nu>x\<rparr>G"
using assms
by(auto simp add: FrameStatEq_def intro: frameImpResPres)

lemma frameImpResComm:
  fixes x :: name
  and   y :: name
  and   F :: "'b frame"

  shows "\<lparr>\<nu>x\<rparr>(\<lparr>\<nu>y\<rparr>F) \<hookrightarrow>\<^sub>F \<lparr>\<nu>y\<rparr>(\<lparr>\<nu>x\<rparr>F)"
proof(case_tac "x = y")
  assume "x = y"
  thus ?thesis by simp
next
  assume "x \<noteq> y"
  show ?thesis
  proof(auto simp add: FrameStatImp_def)
    fix \<phi>::'c
    obtain A\<^isub>F \<Psi>\<^isub>F where Feq: "F = \<langle>A\<^isub>F, \<Psi>\<^isub>F\<rangle>" and "A\<^isub>F \<sharp>* (x, y, \<phi>)"
      by(rule freshFrame)
    then have "x \<sharp> A\<^isub>F" and "y \<sharp> A\<^isub>F" and "A\<^isub>F \<sharp>* \<phi>" by simp+

    obtain x'::name where "x' \<noteq> x" and "x' \<noteq> y" and "x' \<sharp> F" and "x' \<sharp> \<phi>" and "x' \<sharp> A\<^isub>F"
      by(generate_fresh "name") auto
    obtain y'::name where "y' \<noteq> x" and "y' \<noteq> y" and "y' \<noteq> x'" and "y' \<sharp> F" and "y' \<sharp> \<phi>" and "y' \<sharp> A\<^isub>F"
      by(generate_fresh "name") auto
  
    from `y' \<sharp> F` have "\<lparr>\<nu>x\<rparr>(\<lparr>\<nu>y\<rparr>F) = \<lparr>\<nu>x\<rparr>(\<lparr>\<nu>y'\<rparr>([(y, y')] \<bullet> F))"
      by(simp add: alphaFrameRes)
    moreover from `x' \<sharp> F` `x' \<noteq> y` `y' \<noteq> x'` have "\<dots> = \<lparr>\<nu>x'\<rparr>([(x, x')] \<bullet> (\<lparr>\<nu>y'\<rparr>([(y, y')] \<bullet> F)))"
      by(rule_tac alphaFrameRes) (simp add: abs_fresh fresh_left)
    moreover with  `y' \<noteq> x'` `y' \<noteq> x` have "\<dots> = \<lparr>\<nu>x'\<rparr>(\<lparr>\<nu>y'\<rparr>([(x, x')] \<bullet> [(y, y')] \<bullet> F))"
      by(simp add: eqvts calc_atm)
    ultimately have A: "\<lparr>\<nu>x\<rparr>(\<lparr>\<nu>y\<rparr>F)= \<lparr>\<nu>x'\<rparr>(\<lparr>\<nu>y'\<rparr>(\<lparr>\<nu>*A\<^isub>F\<rparr>(FAssert([(x, x')] \<bullet> [(y, y')] \<bullet> \<Psi>\<^isub>F))))"
      using  Feq `x \<sharp> A\<^isub>F` `x' \<sharp> A\<^isub>F` `y \<sharp> A\<^isub>F` `y' \<sharp> A\<^isub>F`
      by(simp add: eqvts)

    from `x' \<sharp> F` have "\<lparr>\<nu>y\<rparr>(\<lparr>\<nu>x\<rparr>F) = \<lparr>\<nu>y\<rparr>(\<lparr>\<nu>x'\<rparr>([(x, x')] \<bullet> F))"
      by(simp add: alphaFrameRes)
    moreover from `y' \<sharp> F` `y' \<noteq> x` `y' \<noteq> x'` have "\<dots> = \<lparr>\<nu>y'\<rparr>([(y, y')] \<bullet> (\<lparr>\<nu>x'\<rparr>([(x, x')] \<bullet> F)))"
      by(rule_tac alphaFrameRes) (simp add: abs_fresh fresh_left)
    moreover with  `y' \<noteq> x'` `x' \<noteq> y` have "\<dots> = \<lparr>\<nu>y'\<rparr>(\<lparr>\<nu>x'\<rparr>([(y, y')] \<bullet> [(x, x')] \<bullet> F))"
      by(simp add: eqvts calc_atm)
    moreover with `x' \<noteq> x` `x' \<noteq> y` `y' \<noteq> x` `y' \<noteq> y` `y' \<noteq> x'` `x \<noteq> y`
      have "\<dots> = \<lparr>\<nu>y'\<rparr>(\<lparr>\<nu>x'\<rparr>([(x, x')] \<bullet> [(y, y')] \<bullet> F))"
      apply(simp add: eqvts)
      by(subst perm_compose) (simp add: calc_atm)
    ultimately have B: "\<lparr>\<nu>y\<rparr>(\<lparr>\<nu>x\<rparr>F)= \<lparr>\<nu>y'\<rparr>(\<lparr>\<nu>x'\<rparr>(\<lparr>\<nu>*A\<^isub>F\<rparr>(FAssert([(x, x')] \<bullet> [(y, y')] \<bullet> \<Psi>\<^isub>F))))"
      using  Feq `x \<sharp> A\<^isub>F` `x' \<sharp> A\<^isub>F` `y \<sharp> A\<^isub>F` `y' \<sharp> A\<^isub>F`
      by(simp add: eqvts)

    from `x' \<sharp> \<phi>` `y' \<sharp> \<phi>` `A\<^isub>F \<sharp>* \<phi>`
    have "\<langle>(x'#y'#A\<^isub>F), [(x, x')] \<bullet> [(y, y')] \<bullet> \<Psi>\<^isub>F\<rangle> \<turnstile>\<^sub>F \<phi> = \<langle>(y'#x'#A\<^isub>F), [(x, x')] \<bullet> [(y, y')] \<bullet> \<Psi>\<^isub>F\<rangle> \<turnstile>\<^sub>F \<phi>"
      by(force dest: frameImpE intro: frameImpI simp del: frameResChain.simps)
    with A B have "(\<lparr>\<nu>x\<rparr>(\<lparr>\<nu>y\<rparr>F)) \<turnstile>\<^sub>F \<phi> = (\<lparr>\<nu>y\<rparr>(\<lparr>\<nu>x\<rparr>F)) \<turnstile>\<^sub>F \<phi>"
      by simp
    moreover assume "(\<lparr>\<nu>x\<rparr>(\<lparr>\<nu>y\<rparr>F)) \<turnstile>\<^sub>F \<phi>"
    ultimately show "(\<lparr>\<nu>y\<rparr>(\<lparr>\<nu>x\<rparr>F)) \<turnstile>\<^sub>F \<phi>" by simp
  qed
qed

lemma frameResComm:
  fixes x :: name
  and   y :: name
  and   F :: "'b frame"

  shows "\<lparr>\<nu>x\<rparr>(\<lparr>\<nu>y\<rparr>F) \<simeq>\<^sub>F \<lparr>\<nu>y\<rparr>(\<lparr>\<nu>x\<rparr>F)"
by(auto simp add: FrameStatEq_def intro: frameImpResComm)

lemma frameImpResCommLeft':
  fixes x    :: name
  and   xvec :: "name list"
  and   F    :: "'b frame"

  shows "\<lparr>\<nu>x\<rparr>(\<lparr>\<nu>*xvec\<rparr>F) \<hookrightarrow>\<^sub>F \<lparr>\<nu>*xvec\<rparr>(\<lparr>\<nu>x\<rparr>F)"
by(induct xvec) (auto intro: frameImpResComm FrameStatImpTrans frameImpResPres)

lemma frameImpResCommRight':
  fixes x    :: name
  and   xvec :: "name list"
  and   F    :: "'b frame"

  shows "\<lparr>\<nu>*xvec\<rparr>(\<lparr>\<nu>x\<rparr>F) \<hookrightarrow>\<^sub>F \<lparr>\<nu>x\<rparr>(\<lparr>\<nu>*xvec\<rparr>F)"
by(induct xvec) (auto intro: frameImpResComm FrameStatImpTrans frameImpResPres)

lemma frameResComm':
  fixes x    :: name
  and   xvec :: "name list"
  and   F    :: "'b frame"

  shows "\<lparr>\<nu>x\<rparr>(\<lparr>\<nu>*xvec\<rparr>F) \<simeq>\<^sub>F \<lparr>\<nu>*xvec\<rparr>(\<lparr>\<nu>x\<rparr>F)"
by(induct xvec) (auto intro: frameResComm FrameStatEqTrans frameResPres)

lemma frameImpChainComm:
  fixes xvec :: "name list"
  and   yvec :: "name list"
  and   F    :: "'b frame"

  shows "\<lparr>\<nu>*xvec\<rparr>(\<lparr>\<nu>*yvec\<rparr>F) \<hookrightarrow>\<^sub>F \<lparr>\<nu>*yvec\<rparr>(\<lparr>\<nu>*xvec\<rparr>F)"
by(induct xvec) (auto intro: frameImpResCommLeft' FrameStatImpTrans frameImpResPres)

lemma frameResChainComm:
  fixes xvec :: "name list"
  and   yvec :: "name list"
  and   F    :: "'b frame"

  shows "\<lparr>\<nu>*xvec\<rparr>(\<lparr>\<nu>*yvec\<rparr>F) \<simeq>\<^sub>F \<lparr>\<nu>*yvec\<rparr>(\<lparr>\<nu>*xvec\<rparr>F)"
by(induct xvec) (auto intro: frameResComm' FrameStatEqTrans frameResPres)

lemma frameImpNilStatEq[simp]:
  fixes \<Psi>  :: 'b
  and   \<Psi>' :: 'b

  shows "(\<langle>\<epsilon>, \<Psi>\<rangle> \<hookrightarrow>\<^sub>F \<langle>\<epsilon>, \<Psi>'\<rangle>) = (\<Psi> \<hookrightarrow> \<Psi>')"
by(simp add: FrameStatImp_def AssertionStatImp_def FrameImp_def)


lemma frameNilStatEq[simp]:
  fixes \<Psi>  :: 'b
  and   \<Psi>' :: 'b

  shows "(\<langle>\<epsilon>, \<Psi>\<rangle> \<simeq>\<^sub>F \<langle>\<epsilon>, \<Psi>'\<rangle>) = (\<Psi> \<simeq> \<Psi>')"
by(simp add: FrameStatEq_def AssertionStatEq_def FrameImp_def)

lemma extractFrameChainStatImp:
  fixes xvec :: "name list"
  and   P    :: "('a, 'b, 'c) psi"

  shows "extractFrame(\<lparr>\<nu>*xvec\<rparr>P) \<hookrightarrow>\<^sub>F \<lparr>\<nu>*xvec\<rparr>(extractFrame P)"
by(induct xvec) (auto intro: frameImpResPres)

lemma extractFrameChainStatEq:
  fixes xvec :: "name list"
  and   P    :: "('a, 'b, 'c) psi"

  shows "extractFrame(\<lparr>\<nu>*xvec\<rparr>P) \<simeq>\<^sub>F \<lparr>\<nu>*xvec\<rparr>(extractFrame P)"
by(induct xvec) (auto intro: frameResPres)

lemma insertAssertionExtractFrameFreshImp:
  fixes xvec :: "name list"
  and   \<Psi>   :: 'b
  and   P    :: "('a, 'b, 'c) psi"

  assumes "xvec \<sharp>* \<Psi>"

  shows "insertAssertion(extractFrame(\<lparr>\<nu>*xvec\<rparr>P)) \<Psi> \<hookrightarrow>\<^sub>F \<lparr>\<nu>*xvec\<rparr>(insertAssertion (extractFrame P) \<Psi>)"
using assms
by(induct xvec) (auto intro: frameImpResPres)

lemma insertAssertionExtractFrameFresh:
  fixes xvec :: "name list"
  and   \<Psi>   :: 'b
  and   P    :: "('a, 'b, 'c) psi"

  assumes "xvec \<sharp>* \<Psi>"

  shows "insertAssertion(extractFrame(\<lparr>\<nu>*xvec\<rparr>P)) \<Psi> \<simeq>\<^sub>F \<lparr>\<nu>*xvec\<rparr>(insertAssertion (extractFrame P) \<Psi>)"
using assms
by(induct xvec) (auto intro: frameResPres)

lemma frameImpResChainPres:
  fixes F    :: "'b frame"
  and   G    :: "'b frame"
  and   xvec :: "name list"

  assumes "F \<hookrightarrow>\<^sub>F G"

  shows "\<lparr>\<nu>*xvec\<rparr>F \<hookrightarrow>\<^sub>F \<lparr>\<nu>*xvec\<rparr>G"
using assms
by(induct xvec) (auto intro: frameImpResPres)

lemma frameResChainPres:
  fixes F    :: "'b frame"
  and   G    :: "'b frame"
  and   xvec :: "name list"

  assumes "F \<simeq>\<^sub>F G"

  shows "\<lparr>\<nu>*xvec\<rparr>F \<simeq>\<^sub>F \<lparr>\<nu>*xvec\<rparr>G"
using assms
by(induct xvec) (auto intro: frameResPres)

lemma insertAssertionE:
  fixes F  :: "('b::fs_name) frame"
  and   \<Psi>  :: 'b
  and   \<Psi>' :: 'b
  and   A\<^isub>F :: "name list"

  assumes "insertAssertion F \<Psi> = \<langle>A\<^isub>F, \<Psi>'\<rangle>"
  and     "A\<^isub>F \<sharp>* F"
  and     "A\<^isub>F \<sharp>* \<Psi>"
  and     "distinct A\<^isub>F"

  obtains \<Psi>\<^isub>F where "F = \<langle>A\<^isub>F, \<Psi>\<^isub>F\<rangle>" and "\<Psi>' = \<Psi> \<otimes> \<Psi>\<^isub>F"
proof -
  assume A: "\<And>\<Psi>\<^isub>F. \<lbrakk>F = \<langle>A\<^isub>F, \<Psi>\<^isub>F\<rangle>; \<Psi>' = \<Psi> \<otimes> \<Psi>\<^isub>F\<rbrakk> \<Longrightarrow> thesis"
  from assms have "\<exists>\<Psi>\<^isub>F. F = \<langle>A\<^isub>F, \<Psi>\<^isub>F\<rangle> \<and> \<Psi>' = \<Psi> \<otimes> \<Psi>\<^isub>F"
  proof(nominal_induct F avoiding: \<Psi> A\<^isub>F \<Psi>' rule: frame.strong_induct)
    case(FAssert \<Psi> A\<^isub>F \<Psi>')
    thus ?case by auto
  next
    case(FRes x F \<Psi> A\<^isub>F \<Psi>')
    from `insertAssertion (\<lparr>\<nu>x\<rparr>F) \<Psi> = \<langle>A\<^isub>F, \<Psi>'\<rangle>` `x \<sharp> \<Psi>`
    moreover obtain y A\<^isub>F' where "A\<^isub>F = y#A\<^isub>F'" by(induct A\<^isub>F) auto
    with `insertAssertion (\<lparr>\<nu>x\<rparr>F) \<Psi> = \<langle>A\<^isub>F, \<Psi>'\<rangle>` `x \<sharp> \<Psi>` `x \<sharp> A\<^isub>F`
    have A: "insertAssertion F \<Psi> = \<langle>([(x, y)] \<bullet> A\<^isub>F'), [(x, y)] \<bullet> \<Psi>'\<rangle>"
      by(simp add: frame.inject alpha eqvts)
    from `A\<^isub>F = y#A\<^isub>F'` `A\<^isub>F \<sharp>* \<Psi>` have "y \<sharp> \<Psi>" and "A\<^isub>F' \<sharp>* \<Psi>" by simp+
    from `distinct A\<^isub>F` `A\<^isub>F = y#A\<^isub>F'` have "y \<sharp> A\<^isub>F'" and "distinct A\<^isub>F'" by auto
    from `A\<^isub>F \<sharp>* (\<lparr>\<nu>x\<rparr>F)` `x \<sharp> A\<^isub>F` `A\<^isub>F = y#A\<^isub>F'` have "y \<sharp> F" and "A\<^isub>F' \<sharp>* F" and "x \<sharp> A\<^isub>F'"
      apply -
      apply(auto simp add: abs_fresh)
      apply(subst fresh_star_def)
      apply(erule rev_mp)
      apply(subst fresh_star_def)
      apply(clarify)
      apply(erule_tac x=xa in ballE)
      apply(simp add: abs_fresh)
      apply auto
      by(simp add: fresh_def name_list_supp)
    with `x \<sharp> A\<^isub>F'` `y \<sharp> A\<^isub>F'` have "([(x, y)] \<bullet> A\<^isub>F') \<sharp>* F" by simp
    from `A\<^isub>F' \<sharp>* \<Psi>` have "([(x, y)] \<bullet> A\<^isub>F') \<sharp>* ([(x, y)] \<bullet> \<Psi>)" by(simp add: pt_fresh_star_bij[OF pt_name_inst, OF at_name_inst])
    with `x \<sharp> \<Psi>` `y \<sharp> \<Psi>` have "([(x, y)] \<bullet> A\<^isub>F') \<sharp>* \<Psi>" by simp
    with `\<And>\<Psi> A\<^isub>F \<Psi>'. \<lbrakk>insertAssertion F \<Psi> = \<langle>A\<^isub>F, \<Psi>'\<rangle>; A\<^isub>F \<sharp>* F; A\<^isub>F \<sharp>* \<Psi>; distinct A\<^isub>F\<rbrakk> \<Longrightarrow> \<exists>\<Psi>\<^isub>F. F = \<langle>A\<^isub>F, \<Psi>\<^isub>F\<rangle> \<and> \<Psi>' = \<Psi> \<otimes> \<Psi>\<^isub>F` A 
         `([(x, y)] \<bullet> A\<^isub>F') \<sharp>* F` `distinct A\<^isub>F'` `x \<sharp> A\<^isub>F'` `y \<sharp> A\<^isub>F'`
    obtain \<Psi>\<^isub>F where Feq: "F = \<langle>A\<^isub>F', \<Psi>\<^isub>F\<rangle>" and \<Psi>_eq: "([(x, y)] \<bullet> \<Psi>') = \<Psi> \<otimes> \<Psi>\<^isub>F"
      by force
    
    from Feq have "\<lparr>\<nu>x\<rparr>F =  \<langle>(x#A\<^isub>F'), \<Psi>\<^isub>F\<rangle>" by(simp add: frame.inject)
    hence "([(x, y)] \<bullet> \<lparr>\<nu>x\<rparr>F) = [(x, y)] \<bullet> \<langle>(x#A\<^isub>F'), \<Psi>\<^isub>F\<rangle>" by simp
    hence "\<lparr>\<nu>x\<rparr>F = \<langle>A\<^isub>F, [(x, y)] \<bullet> \<Psi>\<^isub>F\<rangle>" using `y \<sharp> F` `A\<^isub>F = y#A\<^isub>F'` `x \<sharp> A\<^isub>F` `y \<sharp> A\<^isub>F'`
      by(simp add: eqvts calc_atm alphaFrameRes)

    moreover from \<Psi>_eq have "[(x, y)] \<bullet> ([(x, y)] \<bullet> \<Psi>') = [(x, y)] \<bullet> (\<Psi> \<otimes> \<Psi>\<^isub>F)"
      by simp
    with `x \<sharp> \<Psi>` `y \<sharp> \<Psi>` have "\<Psi>' = \<Psi> \<otimes> ([(x, y)] \<bullet> \<Psi>\<^isub>F)" by(simp add: eqvts)
    ultimately show ?case
      by blast
  qed
  with A show ?thesis
    by blast
qed

lemma mergeFrameE:
  fixes F   :: "'b frame"
  and   G   :: "'b frame"
  and   A\<^isub>F\<^isub>G :: "name list"
  and   \<Psi>\<^isub>F\<^isub>G :: 'b

  assumes "mergeFrame F G = \<langle>A\<^isub>F\<^isub>G, \<Psi>\<^isub>F\<^isub>G\<rangle>"
  and     "distinct A\<^isub>F\<^isub>G"
  and     "A\<^isub>F\<^isub>G \<sharp>* F"
  and     "A\<^isub>F\<^isub>G \<sharp>* G"

  obtains A\<^isub>F \<Psi>\<^isub>F A\<^isub>G \<Psi>\<^isub>G where "A\<^isub>F\<^isub>G = A\<^isub>F@A\<^isub>G" and "\<Psi>\<^isub>F\<^isub>G = \<Psi>\<^isub>F \<otimes> \<Psi>\<^isub>G" and "F = \<langle>A\<^isub>F, \<Psi>\<^isub>F\<rangle>" and "G = \<langle>A\<^isub>G, \<Psi>\<^isub>G\<rangle>" and "A\<^isub>F \<sharp>* \<Psi>\<^isub>G" and "A\<^isub>G \<sharp>* \<Psi>\<^isub>F"
proof -
  assume A: "\<And>A\<^isub>F A\<^isub>G \<Psi>\<^isub>F \<Psi>\<^isub>G. \<lbrakk>A\<^isub>F\<^isub>G = A\<^isub>F@A\<^isub>G; \<Psi>\<^isub>F\<^isub>G = \<Psi>\<^isub>F \<otimes> \<Psi>\<^isub>G; F = \<langle>A\<^isub>F, \<Psi>\<^isub>F\<rangle>; G = \<langle>A\<^isub>G, \<Psi>\<^isub>G\<rangle>; A\<^isub>F \<sharp>* \<Psi>\<^isub>G; A\<^isub>G \<sharp>* \<Psi>\<^isub>F\<rbrakk> \<Longrightarrow> thesis"
  from assms have "\<exists>A\<^isub>F \<Psi>\<^isub>F A\<^isub>G \<Psi>\<^isub>G. A\<^isub>F\<^isub>G = A\<^isub>F@A\<^isub>G \<and> \<Psi>\<^isub>F\<^isub>G = \<Psi>\<^isub>F \<otimes> \<Psi>\<^isub>G \<and> F = \<langle>A\<^isub>F, \<Psi>\<^isub>F\<rangle> \<and> G = \<langle>A\<^isub>G, \<Psi>\<^isub>G\<rangle> \<and> A\<^isub>F \<sharp>* \<Psi>\<^isub>G \<and> A\<^isub>G \<sharp>* \<Psi>\<^isub>F"
  proof(nominal_induct F avoiding: G A\<^isub>F\<^isub>G \<Psi>\<^isub>F\<^isub>G rule: frame.strong_induct)
    case(FAssert \<Psi> G A\<^isub>F\<^isub>G \<Psi>\<^isub>F\<^isub>G)
    thus ?case
      apply auto
      apply(rule_tac x="[]" in exI) 
      by(drule_tac insertAssertionE) auto
  next
    case(FRes x F G A\<^isub>F\<^isub>G \<Psi>\<^isub>F\<^isub>G)
    from `mergeFrame (\<lparr>\<nu>x\<rparr>F) G = \<langle>A\<^isub>F\<^isub>G, \<Psi>\<^isub>F\<^isub>G\<rangle>` `x \<sharp> G`
    obtain y A\<^isub>F\<^isub>G' where "A\<^isub>F\<^isub>G = y#A\<^isub>F\<^isub>G'" by(induct A\<^isub>F\<^isub>G) auto
    with `A\<^isub>F\<^isub>G \<sharp>* (\<lparr>\<nu>x\<rparr>F)` `x \<sharp> A\<^isub>F\<^isub>G` have "A\<^isub>F\<^isub>G' \<sharp>* F" and "x \<sharp> A\<^isub>F\<^isub>G'"
      by(auto simp add: supp_list_cons fresh_star_def fresh_def name_list_supp abs_supp frame.supp)
    from `A\<^isub>F\<^isub>G = y#A\<^isub>F\<^isub>G'` `A\<^isub>F\<^isub>G \<sharp>* G` have "y \<sharp> G" and "A\<^isub>F\<^isub>G' \<sharp>* G" by simp+
    from `A\<^isub>F\<^isub>G = y#A\<^isub>F\<^isub>G'` `A\<^isub>F\<^isub>G \<sharp>* (\<lparr>\<nu>x\<rparr>F)` `x \<sharp> A\<^isub>F\<^isub>G` have "y \<sharp> F" and "A\<^isub>F\<^isub>G' \<sharp>* F"
      apply(auto simp add: abs_fresh frameResChainFreshSet)
      by(induct A\<^isub>F\<^isub>G') (auto simp add: abs_fresh)
    from `distinct A\<^isub>F\<^isub>G` `A\<^isub>F\<^isub>G = y#A\<^isub>F\<^isub>G'` have "y \<sharp> A\<^isub>F\<^isub>G'" and "distinct A\<^isub>F\<^isub>G'" by auto
    
    with `A\<^isub>F\<^isub>G = y#A\<^isub>F\<^isub>G'` `mergeFrame (\<lparr>\<nu>x\<rparr>F) G = \<langle>A\<^isub>F\<^isub>G, \<Psi>\<^isub>F\<^isub>G\<rangle>` `x \<sharp> G` `x \<sharp> A\<^isub>F\<^isub>G` `y \<sharp> A\<^isub>F\<^isub>G'`
    have "mergeFrame F G = \<langle>A\<^isub>F\<^isub>G', [(x, y)] \<bullet> \<Psi>\<^isub>F\<^isub>G\<rangle>"
      by(simp add: frame.inject alpha eqvts)
    with `distinct A\<^isub>F\<^isub>G'` `A\<^isub>F\<^isub>G' \<sharp>* F` `A\<^isub>F\<^isub>G' \<sharp>* G`
         `\<And>G A\<^isub>F\<^isub>G \<Psi>\<^isub>F\<^isub>G. \<lbrakk>mergeFrame F G = \<langle>A\<^isub>F\<^isub>G, \<Psi>\<^isub>F\<^isub>G\<rangle>; distinct A\<^isub>F\<^isub>G; A\<^isub>F\<^isub>G \<sharp>* F; A\<^isub>F\<^isub>G \<sharp>* G\<rbrakk> \<Longrightarrow> \<exists>A\<^isub>F \<Psi>\<^isub>F A\<^isub>G \<Psi>\<^isub>G. A\<^isub>F\<^isub>G = A\<^isub>F@A\<^isub>G \<and> \<Psi>\<^isub>F\<^isub>G = \<Psi>\<^isub>F \<otimes> \<Psi>\<^isub>G \<and> F = \<langle>A\<^isub>F, \<Psi>\<^isub>F\<rangle> \<and> G = \<langle>A\<^isub>G, \<Psi>\<^isub>G\<rangle> \<and> A\<^isub>F \<sharp>* \<Psi>\<^isub>G \<and> A\<^isub>G \<sharp>* \<Psi>\<^isub>F`
    obtain A\<^isub>F \<Psi>\<^isub>F A\<^isub>G \<Psi>\<^isub>G where "A\<^isub>F\<^isub>G' = A\<^isub>F@A\<^isub>G" and "([(x, y)] \<bullet> \<Psi>\<^isub>F\<^isub>G) = \<Psi>\<^isub>F \<otimes> \<Psi>\<^isub>G" and FrF: "F = \<langle>A\<^isub>F, \<Psi>\<^isub>F\<rangle>" and FrG: "G = \<langle>A\<^isub>G, \<Psi>\<^isub>G\<rangle>" and "A\<^isub>F \<sharp>* \<Psi>\<^isub>G" and "A\<^isub>G \<sharp>* \<Psi>\<^isub>F"
      by metis

    from `A\<^isub>F\<^isub>G' = A\<^isub>F@A\<^isub>G` `A\<^isub>F\<^isub>G = y#A\<^isub>F\<^isub>G'` have  "A\<^isub>F\<^isub>G = (y#A\<^isub>F)@A\<^isub>G" by simp
    moreover from `A\<^isub>F\<^isub>G' = A\<^isub>F@A\<^isub>G` `y \<sharp> A\<^isub>F\<^isub>G'` `x \<sharp> A\<^isub>F\<^isub>G'` have "x \<sharp> A\<^isub>F" and "y \<sharp> A\<^isub>F" and "x \<sharp> A\<^isub>G" and "y \<sharp> A\<^isub>G" by simp+
    with `y \<sharp> G` `x \<sharp> G` `x \<sharp> A\<^isub>F\<^isub>G` FrG have "y \<sharp> \<Psi>\<^isub>G" and "x \<sharp> \<Psi>\<^isub>G" 
      by auto
    from `([(x, y)] \<bullet> \<Psi>\<^isub>F\<^isub>G) = \<Psi>\<^isub>F \<otimes> \<Psi>\<^isub>G` have "([(x, y)] \<bullet> [(x, y)] \<bullet> \<Psi>\<^isub>F\<^isub>G) = [(x, y)] \<bullet> (\<Psi>\<^isub>F \<otimes> \<Psi>\<^isub>G)"
      by simp
    with `x \<sharp> \<Psi>\<^isub>G` `y \<sharp> \<Psi>\<^isub>G` have "\<Psi>\<^isub>F\<^isub>G = ([(x, y)] \<bullet> \<Psi>\<^isub>F) \<otimes> \<Psi>\<^isub>G" by(simp add: eqvts)
    moreover from FrF have "([(x, y)] \<bullet> F) = [(x, y)] \<bullet> \<langle>A\<^isub>F, \<Psi>\<^isub>F\<rangle>" by simp
    with `x \<sharp> A\<^isub>F` `y \<sharp> A\<^isub>F` have "([(x, y)] \<bullet> F) = \<langle>A\<^isub>F, [(x, y)] \<bullet> \<Psi>\<^isub>F\<rangle>" by(simp add: eqvts)
    hence "\<lparr>\<nu>y\<rparr>([(x, y)] \<bullet> F) = \<langle>(y#A\<^isub>F), [(x, y)] \<bullet> \<Psi>\<^isub>F\<rangle>" by(simp add: frame.inject)
    with `y \<sharp> F` have "\<lparr>\<nu>x\<rparr>F = \<langle>(y#A\<^isub>F), [(x, y)] \<bullet> \<Psi>\<^isub>F\<rangle>" by(simp add: alphaFrameRes)
    moreover with `A\<^isub>G \<sharp>* \<Psi>\<^isub>F` have "([(x, y)] \<bullet> A\<^isub>G) \<sharp>* ([(x, y)] \<bullet> \<Psi>\<^isub>F)" by(simp add: pt_fresh_star_bij[OF pt_name_inst, OF at_name_inst])
    with `x \<sharp> A\<^isub>G` `y \<sharp> A\<^isub>G` have "A\<^isub>G \<sharp>* ([(x, y)] \<bullet> \<Psi>\<^isub>F)" by simp
    moreover from `A\<^isub>F \<sharp>* \<Psi>\<^isub>G` `y \<sharp> \<Psi>\<^isub>G` have "(y#A\<^isub>F) \<sharp>* \<Psi>\<^isub>G" by simp
    ultimately show ?case using FrG 
      by blast
  qed
  with A show ?thesis by blast
qed

lemma mergeFrameRes1[simp]:
  fixes A\<^isub>F :: "name list"
  and   \<Psi>\<^isub>F :: 'b
  and   x   :: name
  and   A\<^isub>G :: "name list"
  and   \<Psi>\<^isub>G :: 'b
  
  assumes "A\<^isub>F \<sharp>* \<Psi>\<^isub>G"
  and     "A\<^isub>F \<sharp>* A\<^isub>G"
  and     "x \<sharp> A\<^isub>F"
  and     "x \<sharp> \<Psi>\<^isub>F"
  and     "A\<^isub>G \<sharp>* \<Psi>\<^isub>F"
  
  shows "(\<langle>A\<^isub>F, \<Psi>\<^isub>F\<rangle>) \<otimes>\<^sub>F (\<lparr>\<nu>x\<rparr>(\<langle>A\<^isub>G, \<Psi>\<^isub>G\<rangle>)) = (\<langle>(A\<^isub>F@x#A\<^isub>G), \<Psi>\<^isub>F \<otimes> \<Psi>\<^isub>G\<rangle>)"
using assms
apply(fold frameResChain.simps)
by(rule mergeFrames) auto

lemma mergeFrameRes2[simp]:
  fixes A\<^isub>F :: "name list"
  and   \<Psi>\<^isub>F :: 'b
  and   x   :: name
  and   A\<^isub>G :: "name list"
  and   \<Psi>\<^isub>G :: 'b
  
  assumes "A\<^isub>F \<sharp>* \<Psi>\<^isub>G"
  and     "A\<^isub>G \<sharp>* A\<^isub>F"
  and     "x \<sharp> A\<^isub>F"
  and     "x \<sharp> \<Psi>\<^isub>F"
  and     "A\<^isub>G \<sharp>* \<Psi>\<^isub>F"
  
  shows "(\<langle>A\<^isub>F, \<Psi>\<^isub>F\<rangle>) \<otimes>\<^sub>F (\<lparr>\<nu>x\<rparr>(\<langle>A\<^isub>G, \<Psi>\<^isub>G\<rangle>)) = (\<langle>(A\<^isub>F@x#A\<^isub>G), \<Psi>\<^isub>F \<otimes> \<Psi>\<^isub>G\<rangle>)"
using assms
apply(fold frameResChain.simps)
by(rule mergeFrames) auto

lemma insertAssertionResChain[simp]:
  fixes xvec :: "name list"
  and   F    :: "'b frame"
  and   \<Psi>   :: 'b

  assumes "xvec \<sharp>* \<Psi>"

  shows "insertAssertion (\<lparr>\<nu>*xvec\<rparr>F) \<Psi> = \<lparr>\<nu>*xvec\<rparr>(insertAssertion F \<Psi>)"
using assms
by(induct xvec) auto

lemma extractFrameResChain[simp]:
  fixes xvec :: "name list"
  and   P    :: "('a, 'b, 'c) psi"

  shows "extractFrame(\<lparr>\<nu>*xvec\<rparr>P) = \<lparr>\<nu>*xvec\<rparr>(extractFrame P)"
by(induct xvec) auto

lemma frameResFreshChain:
  fixes xvec :: "name list"
  and   F    :: "'b frame"

  assumes "xvec \<sharp>* F"

  shows "\<lparr>\<nu>*xvec\<rparr>F \<simeq>\<^sub>F F"
using assms
proof(induct xvec)
  case Nil
  thus ?case by simp
next
  case(Cons x xvec)
  thus ?case
    by auto (metis frameResPres frameResFresh FrameStatEqTrans)
qed

end

locale assertion = assertionAux SCompose SImp SBottom SChanEq
  for SCompose  :: "'b::fs_name \<Rightarrow> 'b \<Rightarrow> 'b"
  and SImp      :: "'b \<Rightarrow> 'c::fs_name \<Rightarrow> bool"
  and SBottom   :: 'b
  and SChanEq   :: "'a::fs_name \<Rightarrow> 'a \<Rightarrow> 'c" +

  assumes chanEqSym:     "SImp \<Psi> (SChanEq M N) \<Longrightarrow> SImp \<Psi> (SChanEq N M)"
  and     chanEqTrans:   "\<lbrakk>SImp \<Psi> (SChanEq M N); SImp \<Psi> (SChanEq N L)\<rbrakk> \<Longrightarrow> SImp \<Psi> (SChanEq M L)"
  and     Composition:   "assertionAux.AssertionStatEq SImp \<Psi> \<Psi>' \<Longrightarrow> assertionAux.AssertionStatEq SImp (SCompose \<Psi> \<Psi>'') (SCompose \<Psi>' \<Psi>'')"
  and     Identity:      "assertionAux.AssertionStatEq SImp (SCompose \<Psi> SBottom) \<Psi>"
  and     Associativity: "assertionAux.AssertionStatEq SImp (SCompose (SCompose \<Psi> \<Psi>') \<Psi>'') (SCompose \<Psi> (SCompose \<Psi>' \<Psi>''))"
  and     Commutativity: "assertionAux.AssertionStatEq SImp (SCompose \<Psi> \<Psi>') (SCompose \<Psi>' \<Psi>)"

begin

notation SCompose (infixr "\<otimes>" 90)
notation SImp ("_ \<turnstile> _" [85, 85] 85)
notation SChanEq ("_ \<leftrightarrow> _" [90, 90] 90)
notation SBottom ("\<bottom>" 90)

lemma compositionSym:
  fixes \<Psi>   :: 'b
  and   \<Psi>'  :: 'b
  and   \<Psi>'' :: 'b

  assumes "\<Psi> \<simeq> \<Psi>'"

  shows "\<Psi>'' \<otimes> \<Psi> \<simeq> \<Psi>'' \<otimes> \<Psi>'"
proof -
  have "\<Psi>'' \<otimes> \<Psi> \<simeq> \<Psi> \<otimes> \<Psi>''" by(rule Commutativity)
  moreover from assms have "\<Psi> \<otimes> \<Psi>'' \<simeq> \<Psi>' \<otimes> \<Psi>''" by(rule Composition)
  moreover have "\<Psi>' \<otimes> \<Psi>'' \<simeq> \<Psi>'' \<otimes> \<Psi>'" by(rule Commutativity)
  ultimately show ?thesis by(blast intro: AssertionStatEqTrans)
qed

lemma Composition':
  fixes \<Psi>    :: 'b
  and   \<Psi>'   :: 'b
  and   \<Psi>''  :: 'b
  and   \<Psi>''' :: 'b

  assumes "\<Psi> \<simeq> \<Psi>'"
  and     "\<Psi>'' \<simeq> \<Psi>'''"
  
  shows "\<Psi> \<otimes> \<Psi>'' \<simeq> \<Psi>' \<otimes> \<Psi>'''"
using assms
by(metis Composition Commutativity AssertionStatEqTrans)
  

lemma composition':
  fixes \<Psi>    :: 'b
  and   \<Psi>'   :: 'b
  and   \<Psi>''  :: 'b
  and   \<Psi>''' :: 'b

  assumes "\<Psi> \<simeq> \<Psi>'"

  shows "(\<Psi> \<otimes> \<Psi>'') \<otimes> \<Psi>''' \<simeq> (\<Psi>' \<otimes> \<Psi>'') \<otimes> \<Psi>'''"
proof -
  have "(\<Psi> \<otimes> \<Psi>'') \<otimes> \<Psi>''' \<simeq> \<Psi> \<otimes> (\<Psi>'' \<otimes> \<Psi>''')"
    by(rule Associativity)
  moreover from assms have "\<Psi> \<otimes> (\<Psi>'' \<otimes> \<Psi>''') \<simeq> \<Psi>' \<otimes> (\<Psi>'' \<otimes> \<Psi>''')"
    by(rule Composition)
  moreover have "\<Psi>' \<otimes> (\<Psi>'' \<otimes> \<Psi>''') \<simeq> (\<Psi>' \<otimes> \<Psi>'') \<otimes> \<Psi>'''"
    by(rule Associativity[THEN AssertionStatEqSym])
  ultimately show ?thesis by(blast dest: AssertionStatEqTrans)
qed

lemma associativitySym:
  fixes \<Psi>   :: 'b
  and   \<Psi>'  :: 'b
  and   \<Psi>'' :: 'b
  
  shows "(\<Psi> \<otimes> \<Psi>') \<otimes> \<Psi>'' \<simeq> (\<Psi> \<otimes> \<Psi>'') \<otimes> \<Psi>'"
proof -
  have "(\<Psi> \<otimes> \<Psi>') \<otimes> \<Psi>'' \<simeq> \<Psi> \<otimes> (\<Psi>' \<otimes> \<Psi>'')"
    by(rule Associativity)
  moreover have "\<Psi> \<otimes> (\<Psi>' \<otimes> \<Psi>'') \<simeq> \<Psi> \<otimes> (\<Psi>'' \<otimes> \<Psi>')"
    by(rule compositionSym[OF Commutativity])
  moreover have "\<Psi> \<otimes> (\<Psi>'' \<otimes> \<Psi>') \<simeq> (\<Psi> \<otimes> \<Psi>'') \<otimes> \<Psi>'"
    by(rule AssertionStatEqSym[OF Associativity])
  ultimately show ?thesis
    by(blast dest: AssertionStatEqTrans)
qed
(*
lemma frameChanEqSym:
  fixes F :: "'b frame"
  and   M :: 'a
  and   N :: 'a

  assumes "F \<turnstile>\<^sub>F M \<leftrightarrow> N"
  
  shows "F \<turnstile>\<^sub>F N \<leftrightarrow> M"
using assms
apply(auto simp add: FrameImp_def)
by(force intro: chanEqSym simp add: FrameImp_def)

lemma frameChanEqTrans:
  fixes F :: "'b frame"
  and   M :: 'a
  and   N :: 'a

  assumes "F \<turnstile>\<^sub>F M \<leftrightarrow> N"
  and     "F \<turnstile>\<^sub>F N \<leftrightarrow> L"
  
  shows "F \<turnstile>\<^sub>F M \<leftrightarrow> L"
proof -
  obtain A\<^isub>F \<Psi>\<^isub>F where "F = \<langle>A\<^isub>F, \<Psi>\<^isub>F\<rangle>" and "A\<^isub>F \<sharp>* (M, N, L)"
    by(rule freshFrame)
  with assms show ?thesis
    by(force dest: frameImpE intro: frameImpI chanEqTrans)
qed
*)
lemma frameIntAssociativity:
  fixes A\<^isub>F  :: "name list"
  and   \<Psi>   :: 'b
  and   \<Psi>'  :: 'b
  and   \<Psi>'' :: 'b

  shows "\<langle>A\<^isub>F, (\<Psi> \<otimes> \<Psi>') \<otimes> \<Psi>''\<rangle> \<simeq>\<^sub>F \<langle>A\<^isub>F, \<Psi> \<otimes> (\<Psi>' \<otimes> \<Psi>'')\<rangle>"
by(induct A\<^isub>F) (auto intro: Associativity frameResPres)

lemma frameIntCommutativity:
  fixes A\<^isub>F  :: "name list"
  and   \<Psi>   :: 'b
  and   \<Psi>'  :: 'b

  shows "\<langle>A\<^isub>F, \<Psi> \<otimes> \<Psi>'\<rangle> \<simeq>\<^sub>F \<langle>A\<^isub>F, \<Psi>' \<otimes> \<Psi>\<rangle>"
by(induct A\<^isub>F) (auto intro: Commutativity frameResPres)

lemma frameIntIdentity:
  fixes A\<^isub>F :: "name list"
  and   \<Psi>\<^isub>F :: 'b 

  shows "\<langle>A\<^isub>F, \<Psi>\<^isub>F \<otimes> SBottom\<rangle> \<simeq>\<^sub>F \<langle>A\<^isub>F, \<Psi>\<^isub>F\<rangle>"
by(induct A\<^isub>F) (auto intro: Identity frameResPres)

lemma frameIntComposition:
  fixes \<Psi>  :: 'b
  and   \<Psi>' :: 'b
  and   A\<^isub>F :: "name list"
  and   \<Psi>\<^isub>F :: 'b

  assumes "\<Psi> \<simeq> \<Psi>'"

  shows "\<langle>A\<^isub>F, \<Psi> \<otimes> \<Psi>\<^isub>F\<rangle> \<simeq>\<^sub>F \<langle>A\<^isub>F, \<Psi>' \<otimes> \<Psi>\<^isub>F\<rangle>"
using assms
by(induct A\<^isub>F) (auto intro: Composition frameResPres)

lemma frameIntCompositionSym:
  fixes \<Psi>  :: 'b
  and   \<Psi>' :: 'b
  and   A\<^isub>F :: "name list"
  and   \<Psi>\<^isub>F :: 'b

  assumes "\<Psi> \<simeq> \<Psi>'"

  shows "\<langle>A\<^isub>F, \<Psi>\<^isub>F \<otimes> \<Psi>\<rangle> \<simeq>\<^sub>F \<langle>A\<^isub>F, \<Psi>\<^isub>F \<otimes> \<Psi>'\<rangle>"
using assms
by(induct A\<^isub>F) (auto intro: compositionSym frameResPres)

lemma frameCommutativity:
  fixes F :: "'b frame"
  and   G :: "'b frame"

  shows "F \<otimes>\<^sub>F G \<simeq>\<^sub>F G \<otimes>\<^sub>F F"
proof -
  obtain A\<^isub>F \<Psi>\<^isub>F where "F = \<langle>A\<^isub>F, \<Psi>\<^isub>F\<rangle>" and "A\<^isub>F \<sharp>* G"
    by(rule freshFrame)
  moreover obtain A\<^isub>G \<Psi>\<^isub>G where "G = \<langle>A\<^isub>G, \<Psi>\<^isub>G\<rangle>" and "A\<^isub>G \<sharp>* \<Psi>\<^isub>F" and "A\<^isub>G \<sharp>* A\<^isub>F"
    by(rule_tac C="(A\<^isub>F, \<Psi>\<^isub>F)" in freshFrame) auto
  moreover from `A\<^isub>F \<sharp>* G` `G = \<langle>A\<^isub>G, \<Psi>\<^isub>G\<rangle>` `A\<^isub>G \<sharp>* A\<^isub>F` have "A\<^isub>F \<sharp>* \<Psi>\<^isub>G"
    by auto
  ultimately show ?thesis
    by auto (metis FrameStatEqTrans frameChainAppend frameResChainComm frameIntCommutativity)
qed
  
lemma frameScopeExt:
  fixes x :: name
  and   F :: "'b frame"
  and   G :: "'b frame"

  assumes "x \<sharp> F"

  shows "\<lparr>\<nu>x\<rparr>(F \<otimes>\<^sub>F G) \<simeq>\<^sub>F F \<otimes>\<^sub>F (\<lparr>\<nu>x\<rparr>G)"
proof -
  have "\<lparr>\<nu>x\<rparr>(F \<otimes>\<^sub>F G) \<simeq>\<^sub>F \<lparr>\<nu>x\<rparr>(G \<otimes>\<^sub>F F)"
    by(metis frameResPres frameCommutativity)
  with `x \<sharp> F` have "\<lparr>\<nu>x\<rparr>(F \<otimes>\<^sub>F G) \<simeq>\<^sub>F (\<lparr>\<nu>x\<rparr>G) \<otimes>\<^sub>F F"
    by simp
  moreover have "(\<lparr>\<nu>x\<rparr>G) \<otimes>\<^sub>F F \<simeq>\<^sub>F F \<otimes>\<^sub>F (\<lparr>\<nu>x\<rparr>G)"
    by(rule frameCommutativity)
  ultimately show ?thesis by(rule FrameStatEqTrans)
qed

lemma insertDoubleAssertionStatEq:
  fixes F  :: "'b frame"
  and   \<Psi>  :: 'b
  and   \<Psi>' :: 'b

  shows "insertAssertion(insertAssertion F \<Psi>) \<Psi>' \<simeq>\<^sub>F (insertAssertion F) (\<Psi> \<otimes> \<Psi>')"
proof -
  obtain A\<^isub>F \<Psi>\<^isub>F where "F = \<langle>A\<^isub>F, \<Psi>\<^isub>F\<rangle>" and "A\<^isub>F \<sharp>* \<Psi>" and "A\<^isub>F \<sharp>* \<Psi>'" and "A\<^isub>F \<sharp>* (\<Psi> \<otimes> \<Psi>')"
    by(rule_tac C="(\<Psi>, \<Psi>')" in freshFrame) auto
  thus ?thesis
    by auto (metis frameIntComposition Commutativity frameIntAssociativity FrameStatEqTrans FrameStatEqSym)
qed

lemma guardedStatEq:
  fixes P  :: "('a, 'b, 'c) psi"
  and   I  :: "('a, 'b, 'c) input"
  and   C  :: "('a, 'b, 'c) psiCase"
  and   A\<^isub>P :: "name list"
  and   \<Psi>\<^isub>P :: 'b

  shows "\<lbrakk>guarded P; extractFrame P = \<langle>A\<^isub>P, \<Psi>\<^isub>P\<rangle>\<rbrakk> \<Longrightarrow> \<Psi>\<^isub>P \<simeq> \<bottom> \<and> supp \<Psi>\<^isub>P = ({}::name set)"
  and   "\<lbrakk>guarded' I; extractFrame' I = \<langle>A\<^isub>P, \<Psi>\<^isub>P\<rangle>\<rbrakk> \<Longrightarrow> \<Psi>\<^isub>P \<simeq> \<bottom> \<and> supp \<Psi>\<^isub>P = ({}::name set)"
  and   "\<lbrakk>guarded'' C; extractFrame'' C = \<langle>A\<^isub>P, \<Psi>\<^isub>P\<rangle>\<rbrakk> \<Longrightarrow> \<Psi>\<^isub>P \<simeq> \<bottom> \<and> supp \<Psi>\<^isub>P = ({}::name set)"
proof(nominal_induct P and I and C arbitrary: A\<^isub>P \<Psi>\<^isub>P rule: psi_input_psiCase.strong_inducts)
  case(PsiNil A\<^isub>P \<Psi>\<^isub>P)
  thus ?case by simp
next
  case(Output M N P A\<^isub>P \<Psi>\<^isub>P)
  thus ?case by simp
next
  case(Input M In  A\<^isub>P \<Psi>\<^isub>P)
  thus ?case by simp
next
  case(Case psiCase A\<^isub>P \<Psi>\<^isub>P)
  thus ?case by simp
next
  case(Par P Q A\<^isub>P\<^isub>Q \<Psi>\<^isub>P\<^isub>Q)
  from `guarded(P \<parallel> Q)` have "guarded P" and "guarded Q" by simp+
  obtain A\<^isub>P \<Psi>\<^isub>P where FrP: "extractFrame P = \<langle>A\<^isub>P, \<Psi>\<^isub>P\<rangle>" and "A\<^isub>P \<sharp>* Q" by(rule freshFrame)
  obtain A\<^isub>Q \<Psi>\<^isub>Q where FrQ: "extractFrame Q = \<langle>A\<^isub>Q, \<Psi>\<^isub>Q\<rangle>" and "A\<^isub>Q \<sharp>* A\<^isub>P" and "A\<^isub>Q \<sharp>* \<Psi>\<^isub>P" 
    by(rule_tac C="(A\<^isub>P, \<Psi>\<^isub>P)" in freshFrame) auto
  
  from `\<And>A\<^isub>P \<Psi>\<^isub>P. \<lbrakk>guarded P; extractFrame P = \<langle>A\<^isub>P, \<Psi>\<^isub>P\<rangle>\<rbrakk> \<Longrightarrow> \<Psi>\<^isub>P \<simeq> \<bottom> \<and> (supp \<Psi>\<^isub>P = ({}::name set))` `guarded P` FrP
  have "\<Psi>\<^isub>P \<simeq> \<bottom>" and "supp \<Psi>\<^isub>P = ({}::name set)" by simp+
  from `\<And>A\<^isub>Q \<Psi>\<^isub>Q. \<lbrakk>guarded Q; extractFrame Q = \<langle>A\<^isub>Q, \<Psi>\<^isub>Q\<rangle>\<rbrakk> \<Longrightarrow> \<Psi>\<^isub>Q \<simeq> \<bottom> \<and> (supp \<Psi>\<^isub>Q = ({}::name set))` `guarded Q` FrQ
  have "\<Psi>\<^isub>Q \<simeq> \<bottom>" and "supp \<Psi>\<^isub>Q = ({}::name set)" by simp+
  
  from `A\<^isub>P \<sharp>* Q` FrQ `A\<^isub>Q \<sharp>* A\<^isub>P` have "A\<^isub>P \<sharp>* \<Psi>\<^isub>Q" by(drule_tac extractFrameFreshChain) auto
  with `A\<^isub>Q \<sharp>* A\<^isub>P` `A\<^isub>Q \<sharp>* \<Psi>\<^isub>P` FrP FrQ `extractFrame(P \<parallel> Q) = \<langle>A\<^isub>P\<^isub>Q, \<Psi>\<^isub>P\<^isub>Q\<rangle>` have "\<langle>(A\<^isub>P@A\<^isub>Q), \<Psi>\<^isub>P \<otimes> \<Psi>\<^isub>Q\<rangle> = \<langle>A\<^isub>P\<^isub>Q, \<Psi>\<^isub>P\<^isub>Q\<rangle>"
    by auto
  with `supp \<Psi>\<^isub>P = {}` `supp \<Psi>\<^isub>Q = {}` compSupp have "\<Psi>\<^isub>P\<^isub>Q = \<Psi>\<^isub>P \<otimes> \<Psi>\<^isub>Q"
    by blast
  moreover from `\<Psi>\<^isub>P \<simeq> \<bottom>` `\<Psi>\<^isub>Q \<simeq> \<bottom>` have "\<Psi>\<^isub>P \<otimes> \<Psi>\<^isub>Q \<simeq> \<bottom>"
    by(metis Composition Identity Associativity Commutativity AssertionStatEqTrans)
  ultimately show ?case using `supp \<Psi>\<^isub>P = {}` `supp \<Psi>\<^isub>Q = {}` compSupp
    by blast
next
  case(Res x P A\<^isub>x\<^isub>P \<Psi>\<^isub>x\<^isub>P)
  from `guarded(\<lparr>\<nu>x\<rparr>P)` have "guarded P" by simp
  moreover obtain A\<^isub>P \<Psi>\<^isub>P where FrP: "extractFrame P = \<langle>A\<^isub>P, \<Psi>\<^isub>P\<rangle>" by(rule freshFrame)
  moreover note `\<And>A\<^isub>P \<Psi>\<^isub>P. \<lbrakk>guarded P; extractFrame P = \<langle>A\<^isub>P, \<Psi>\<^isub>P\<rangle>\<rbrakk> \<Longrightarrow> \<Psi>\<^isub>P \<simeq> \<bottom> \<and> (supp \<Psi>\<^isub>P = ({}::name set))`
  ultimately have "\<Psi>\<^isub>P \<simeq> \<bottom>" and "supp \<Psi>\<^isub>P = ({}::name set)" by auto
  from FrP `extractFrame(\<lparr>\<nu>x\<rparr>P) = \<langle>A\<^isub>x\<^isub>P, \<Psi>\<^isub>x\<^isub>P\<rangle>` have "\<langle>(x#A\<^isub>P), \<Psi>\<^isub>P\<rangle> = \<langle>A\<^isub>x\<^isub>P, \<Psi>\<^isub>x\<^isub>P\<rangle>" by simp
  with `supp \<Psi>\<^isub>P = {}` have "\<Psi>\<^isub>P = \<Psi>\<^isub>x\<^isub>P" by(auto simp del: frameResChain.simps)
  with `\<Psi>\<^isub>P \<simeq> \<bottom>` `supp \<Psi>\<^isub>P = {}` show ?case
    by simp
next
  case(Assert \<Psi> A\<^isub>P \<Psi>\<^isub>P)
  thus ?case by simp
next
  case(Bang P A\<^isub>P \<Psi>\<^isub>P)
  thus ?case by simp
next
  case(Trm M P)
  thus ?case by simp
next
  case(Bind x I)
  thus ?case by simp
next
  case EmptyCase
  thus ?case by simp
next
  case(Cond \<phi> P psiCase)
  thus ?case by simp
qed

end

end
