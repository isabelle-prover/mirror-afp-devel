(* 
   Title: Psi-calculi   
   Author/Maintainer: Jesper Bengtson (jebe@itu.dk), 2012
*)
theory Sim_Struct_Cong
  imports Simulation
begin

lemma partitionListLeft:
  assumes "xs@ys=xs'@y#ys'"
  and     "y mem xs"
  and     "distinct(xs@ys)"

  obtains zs where "xs = xs'@y#zs" and "ys'=zs@ys"
using assms
by(auto simp add: append_eq_append_conv2 append_eq_Cons_conv)

lemma partitionListRight: 
  assumes "xs@ys=xs'@y#ys'"
  and     "y mem ys"
  and     "distinct(xs@ys)"

  obtains zs where "xs' = xs@zs" and "ys=zs@y#ys'"
using assms
by(force simp add: append_eq_append_conv2 append_eq_Cons_conv)

context env begin

lemma resComm:
  fixes \<Psi>   :: 'b
  and   x   :: name
  and   y   :: name
  and   Rel :: "('b \<times> ('a, 'b, 'c) psi \<times> ('a, 'b, 'c) psi) set"
  and   P   :: "('a, 'b, 'c) psi"
  
  assumes "x \<sharp> \<Psi>"
  and     "y \<sharp> \<Psi>"
  and     "eqvt Rel"
  and     R1: "\<And>\<Psi>' Q. (\<Psi>', Q, Q) \<in> Rel"
  and     R2: "\<And>\<Psi>' a b Q. \<lbrakk>a \<sharp> \<Psi>'; b \<sharp> \<Psi>'\<rbrakk> \<Longrightarrow> (\<Psi>', \<lparr>\<nu>a\<rparr>(\<lparr>\<nu>b\<rparr>Q), \<lparr>\<nu>b\<rparr>(\<lparr>\<nu>a\<rparr>Q)) \<in> Rel"

  shows "\<Psi> \<rhd> \<lparr>\<nu>x\<rparr>(\<lparr>\<nu>y\<rparr>P) \<leadsto>[Rel] \<lparr>\<nu>y\<rparr>(\<lparr>\<nu>x\<rparr>P)"
proof(case_tac "x=y")
  assume "x = y"
  thus ?thesis using R1
    by(force intro: reflexive)
next
  assume "x \<noteq> y"
  note `eqvt Rel`
  moreover from `x \<sharp> \<Psi>` `y \<sharp> \<Psi>` have "[x, y] \<sharp>* \<Psi>" by(simp add: fresh_star_def)
  moreover have "[x, y] \<sharp>* \<lparr>\<nu>x\<rparr>(\<lparr>\<nu>y\<rparr>P)" by(simp add: abs_fresh)
  moreover have "[x, y] \<sharp>* \<lparr>\<nu>y\<rparr>(\<lparr>\<nu>x\<rparr>P)" by(simp add: abs_fresh)
  ultimately show ?thesis
  proof(induct rule: simIChainFresh[where C="(x, y)"])
    case(cSim \<alpha> P')
    from `bn \<alpha> \<sharp>* (x, y)` `bn \<alpha> \<sharp>* (\<lparr>\<nu>x\<rparr>(\<lparr>\<nu>y\<rparr>P))` have "x \<sharp> bn \<alpha>" and "y \<sharp> bn \<alpha>" and "bn \<alpha> \<sharp>* P" by simp+
    from `[x, y] \<sharp>* \<alpha>` have "x \<sharp> \<alpha>" and "y \<sharp> \<alpha>" by simp+
    from `[x, y] \<sharp>* P'` have "x \<sharp> P'" and "y \<sharp> P'" by simp+
    from `bn \<alpha> \<sharp>* P` `x \<sharp> \<alpha>` have "bn \<alpha> \<sharp>* \<lparr>\<nu>x\<rparr>P" by(simp add: abs_fresh)
    with `\<Psi> \<rhd> \<lparr>\<nu>y\<rparr>(\<lparr>\<nu>x\<rparr>P) \<longmapsto>\<alpha> \<prec> P'` `y \<sharp> \<Psi>` `y \<sharp> \<alpha>` `y \<sharp> P'` `bn \<alpha> \<sharp>* \<Psi>`
    show ?case using `bn \<alpha> \<sharp>* subject \<alpha>` `x \<sharp> \<alpha>` `x \<sharp> P'` `bn \<alpha> \<sharp>* \<Psi>` `bn \<alpha> \<sharp>* P` `bn \<alpha> \<sharp>* subject \<alpha>` `y \<sharp> \<alpha>`
    proof(induct rule: resCases')
      case(cOpen M yvec1 yvec2 y' N P')
      from `yvec1 \<sharp>* yvec2` `distinct yvec1` `distinct yvec2` have "distinct(yvec1@yvec2)" by auto
      from `x \<sharp> M\<lparr>\<nu>*(yvec1 @ y' # yvec2)\<rparr>\<langle>N\<rangle>` have "x \<sharp> M" and "x \<sharp> yvec1" and "x \<noteq> y'" and "x \<sharp> yvec2" and "x \<sharp> N"
        by simp+
      from `y \<sharp> M\<lparr>\<nu>*(yvec1 @ y' # yvec2)\<rparr>\<langle>N\<rangle>` have "y \<sharp> M" and "y \<sharp> yvec1" and "y \<sharp> yvec2"
        by simp+
      from `\<Psi> \<rhd> ([(y, y')] \<bullet> \<lparr>\<nu>x\<rparr>P) \<longmapsto>M\<lparr>\<nu>*(yvec1@yvec2)\<rparr>\<langle>N\<rangle> \<prec> P'` `x \<noteq> y` `x \<noteq> y'`
      have "\<Psi> \<rhd> \<lparr>\<nu>x\<rparr>([(y, y')] \<bullet> P) \<longmapsto>M\<lparr>\<nu>*(yvec1@yvec2)\<rparr>\<langle>N\<rangle> \<prec> P'" by(simp add: eqvts)
      moreover note `x \<sharp> \<Psi>`
      moreover from `x \<sharp> N` `x \<sharp> yvec1` `x \<sharp> yvec2` `x \<sharp> M` have "x \<sharp> M\<lparr>\<nu>*(yvec1@yvec2)\<rparr>\<langle>N\<rangle>" by simp
      moreover note `x \<sharp> P'`
      moreover from `yvec1 \<sharp>* \<Psi>` `yvec2 \<sharp>* \<Psi>` have "bn(M\<lparr>\<nu>*(yvec1@yvec2)\<rparr>\<langle>N\<rangle>) \<sharp>* \<Psi>" by simp
      moreover from `yvec1 \<sharp>* \<lparr>\<nu>x\<rparr>P` `yvec2 \<sharp>* \<lparr>\<nu>x\<rparr>P` `y \<sharp> yvec1` `y' \<sharp> yvec1` `y \<sharp> yvec2` `y' \<sharp> yvec2` `x \<sharp> yvec1` `x \<sharp> yvec2`
      have "bn(M\<lparr>\<nu>*(yvec1@yvec2)\<rparr>\<langle>N\<rangle>) \<sharp>* ([(y, y')] \<bullet> P)" by simp
      moreover from `yvec1 \<sharp>* M` `yvec2 \<sharp>* M` have "bn(M\<lparr>\<nu>*(yvec1 @ yvec2)\<rparr>\<langle>N\<rangle>) \<sharp>* subject(M\<lparr>\<nu>*(yvec1 @ yvec2)\<rparr>\<langle>N\<rangle>)"
        by simp
      moreover have "bn(M\<lparr>\<nu>*(yvec1 @ yvec2)\<rparr>\<langle>N\<rangle>) = yvec1@yvec2" by simp
      moreover have "subject(M\<lparr>\<nu>*(yvec1 @ yvec2)\<rparr>\<langle>N\<rangle>) = Some M" by simp
      moreover have "object(M\<lparr>\<nu>*(yvec1 @ yvec2)\<rparr>\<langle>N\<rangle>) = Some N" by simp
      ultimately show ?case 
      proof(induct rule: resCases')
        case(cOpen M' xvec1 xvec2 x' N' P')
        from `bn(M'\<lparr>\<nu>*(xvec1 @ x' # xvec2)\<rparr>\<langle>N'\<rangle>) = yvec1 @ yvec2` have "yvec1@yvec2 = xvec1@x'#xvec2" by simp
        from `subject(M'\<lparr>\<nu>*(xvec1 @ x' # xvec2)\<rparr>\<langle>N'\<rangle>) = Some M` have "M = M'" by simp
        from `object(M'\<lparr>\<nu>*(xvec1 @ x' # xvec2)\<rparr>\<langle>N'\<rangle>) = Some N` have "N = N'" by simp
        from `x \<sharp> yvec1` `x \<sharp> yvec2` `y' \<sharp> yvec1` `y' \<sharp> yvec2` `y \<sharp> yvec1` `y \<sharp> yvec2`
        have "x \<sharp> (yvec1@yvec2)" and "y \<sharp> (yvec1@yvec2)" and "y' \<sharp> (yvec1@yvec2)" by simp+
        with `yvec1@yvec2 = xvec1@x'#xvec2`
        have "x \<sharp> xvec1" and "x \<noteq> x'" and "x \<sharp> xvec2" and "y \<sharp> xvec1" and "y \<noteq> x'" and "y \<sharp> xvec2"
          and "y' \<sharp> xvec1" and "x' \<noteq> y'" and "y' \<sharp> xvec2"
          by auto

        show ?case
        proof(case_tac "x' mem yvec1")
          assume "x' mem yvec1"
        
          with `yvec1@yvec2 = xvec1@x'#xvec2` `distinct (yvec1@yvec2)`
          obtain xvec2' where Eq1: "yvec1=xvec1@x'#xvec2'"
                          and Eq: "xvec2=xvec2'@yvec2"
            by(rule_tac partitionListLeft)
          from `\<Psi> \<rhd> ([(x, x')] \<bullet> [(y, y')] \<bullet> P) \<longmapsto>M'\<lparr>\<nu>*(xvec1@xvec2)\<rparr>\<langle>N'\<rangle> \<prec> P'` `y' \<in> supp N` `y' \<sharp> \<Psi>` `y' \<sharp> M` `y' \<sharp> xvec1` `y' \<sharp> xvec2` Eq `M=M'` `N = N'`
          have "\<Psi> \<rhd> \<lparr>\<nu>y'\<rparr>([(x, x')] \<bullet> [(y, y')] \<bullet> P) \<longmapsto>M'\<lparr>\<nu>*((xvec1@xvec2')@y'#yvec2)\<rparr>\<langle>N'\<rangle> \<prec> P'" 
            by(rule_tac Open) auto
          then have "\<Psi> \<rhd> \<lparr>\<nu>x'\<rparr>(\<lparr>\<nu>y'\<rparr>([(x, x')] \<bullet> [(y, y')] \<bullet> P)) \<longmapsto>M\<lparr>\<nu>*(xvec1@x'#xvec2'@y'#yvec2)\<rparr>\<langle>N\<rangle> \<prec> P'" 
            using `x' \<in> supp N'` `x' \<sharp> \<Psi>` `x' \<sharp> M'` `x' \<sharp> xvec1` `x' \<sharp> xvec2` `x' \<noteq> y'` Eq `M=M'` `N=N'`
            by(rule_tac Open) auto
          with `x' \<noteq> y'` `x \<noteq> y'` `x' \<sharp> [(y, y')] \<bullet> P`
          have "\<Psi> \<rhd> \<lparr>\<nu>x\<rparr>(\<lparr>\<nu>y'\<rparr>([(y, y')] \<bullet> P)) \<longmapsto>M\<lparr>\<nu>*(xvec1@x'#xvec2'@y'#yvec2)\<rparr>\<langle>N\<rangle> \<prec> P'"
            by(subst alphaRes[where y=x']) (simp add: calc_atm eqvts abs_fresh)+
          with Eq1 `y' \<sharp> \<lparr>\<nu>x\<rparr>P` `x \<noteq> y'` R1 show ?case
            by(fastforce simp add: alphaRes abs_fresh)
        next
          assume "\<not>x' mem yvec1"
          hence "x' \<sharp> yvec1" by(simp add: fresh_def)
          from `\<not>x' mem yvec1` `yvec1@yvec2 = xvec1@x'#xvec2`
          have "x' mem yvec2"
            by(fastforce simp add: append_eq_append_conv2 append_eq_Cons_conv
                                  fresh_list_append fresh_list_cons)
          with `yvec1@yvec2 = xvec1@x'#xvec2` `distinct (yvec1@yvec2)`
          obtain xvec2' where Eq: "xvec1=yvec1@xvec2'"
                          and Eq1: "yvec2=xvec2'@x'#xvec2"
            by(rule_tac partitionListRight)
          from `\<Psi> \<rhd> ([(x, x')] \<bullet> [(y, y')] \<bullet> P) \<longmapsto>M'\<lparr>\<nu>*(xvec1@xvec2)\<rparr>\<langle>N'\<rangle> \<prec> P'` `y' \<in> supp N` `y' \<sharp> \<Psi>` `y' \<sharp> M` `y' \<sharp> xvec1` `y' \<sharp> xvec2` Eq `M=M'` `N = N'`
          have "\<Psi> \<rhd> \<lparr>\<nu>y'\<rparr>([(x, x')] \<bullet> [(y, y')] \<bullet> P) \<longmapsto>M'\<lparr>\<nu>*(yvec1@y'#xvec2'@xvec2)\<rparr>\<langle>N'\<rangle> \<prec> P'" 
            by(rule_tac Open) (assumption | simp)+
          then have "\<Psi> \<rhd> \<lparr>\<nu>x'\<rparr>(\<lparr>\<nu>y'\<rparr>([(x, x')] \<bullet> [(y, y')] \<bullet> P)) \<longmapsto>M\<lparr>\<nu>*((yvec1@y'#xvec2')@x'#xvec2)\<rparr>\<langle>N\<rangle> \<prec> P'" 
            using `x' \<in> supp N'` `x' \<sharp> \<Psi>` `x' \<sharp> M'` `x' \<sharp> xvec1` `x' \<sharp> xvec2` `x' \<noteq> y'` Eq `M=M'` `N=N'`
            by(rule_tac Open) auto
          with `x' \<noteq> y'` `x \<noteq> y'` `x' \<sharp> [(y, y')] \<bullet> P`
          have "\<Psi> \<rhd> \<lparr>\<nu>x\<rparr>(\<lparr>\<nu>y'\<rparr>([(y, y')] \<bullet> P)) \<longmapsto>M\<lparr>\<nu>*((yvec1@y'#xvec2')@x'#xvec2)\<rparr>\<langle>N\<rangle> \<prec> P'"
            by(subst alphaRes[where y=x']) (simp add: calc_atm eqvts abs_fresh)+
          with Eq1 `y' \<sharp> \<lparr>\<nu>x\<rparr>P` `x \<noteq> y'` R1 show ?case
            by(fastforce simp add: alphaRes abs_fresh)
        qed
      next
        case(cRes P')
        from `\<Psi> \<rhd> ([(y, y')] \<bullet> P) \<longmapsto>M\<lparr>\<nu>*(yvec1@yvec2)\<rparr>\<langle>N\<rangle> \<prec> P'` `y' \<in> supp N` `y' \<sharp> \<Psi>` `y' \<sharp> M` `y' \<sharp> yvec1` `y' \<sharp> yvec2`
        have "\<Psi> \<rhd> \<lparr>\<nu>y'\<rparr>([(y, y')] \<bullet> P) \<longmapsto>M\<lparr>\<nu>*(yvec1@y'#yvec2)\<rparr>\<langle>N\<rangle> \<prec> P'" by(rule Open)
        with `y' \<sharp> \<lparr>\<nu>x\<rparr>P` `x \<noteq> y'`have "\<Psi> \<rhd> \<lparr>\<nu>y\<rparr>P \<longmapsto>M\<lparr>\<nu>*(yvec1@y'#yvec2)\<rparr>\<langle>N\<rangle> \<prec> P'" by(simp add: alphaRes abs_fresh)
        hence "\<Psi> \<rhd> \<lparr>\<nu>x\<rparr>(\<lparr>\<nu>y\<rparr>P) \<longmapsto>M\<lparr>\<nu>*(yvec1@y'#yvec2)\<rparr>\<langle>N\<rangle> \<prec> \<lparr>\<nu>x\<rparr>P'" using `x \<sharp> \<Psi>` `x \<sharp> M` `x \<sharp> yvec1` `x \<noteq> y'` `x \<sharp> yvec2` `x \<sharp> N`
          by(rule_tac Scope) auto
        moreover have "(\<Psi>, \<lparr>\<nu>x\<rparr>P', \<lparr>\<nu>x\<rparr>P') \<in> Rel" by(rule R1)
        ultimately show ?case by blast
      qed
    next
      case(cRes P')
      from `x \<sharp> \<lparr>\<nu>y\<rparr>P'` `x \<noteq> y` have "x \<sharp> P'" by(simp add: abs_fresh)
      with `\<Psi> \<rhd> \<lparr>\<nu>x\<rparr>P \<longmapsto>\<alpha> \<prec> P'` `x \<sharp> \<Psi>` `x \<sharp> \<alpha>`
      show ?case using `bn \<alpha> \<sharp>* \<Psi>` `bn \<alpha> \<sharp>* P` `bn \<alpha> \<sharp>* subject \<alpha>` `y \<sharp> \<alpha>`
      proof(induct rule: resCases')
        case(cOpen M xvec1 xvec2 x' N P')
        from `y \<sharp> M\<lparr>\<nu>*(xvec1@x'#xvec2)\<rparr>\<langle>N\<rangle>` have "y \<noteq> x'" and "y \<sharp> M\<lparr>\<nu>*(xvec1@xvec2)\<rparr>\<langle>N\<rangle>" by simp+
        from `\<Psi> \<rhd> ([(x, x')] \<bullet> P) \<longmapsto>M\<lparr>\<nu>*(xvec1@xvec2)\<rparr>\<langle>N\<rangle> \<prec> P'` `y \<sharp> \<Psi>` `y \<sharp> M\<lparr>\<nu>*(xvec1@xvec2)\<rparr>\<langle>N\<rangle>`
        have "\<Psi> \<rhd> \<lparr>\<nu>y\<rparr>([(x, x')] \<bullet> P) \<longmapsto>M\<lparr>\<nu>*(xvec1@xvec2)\<rparr>\<langle>N\<rangle> \<prec> \<lparr>\<nu>y\<rparr>P'" 
          by(rule Scope)
        hence "\<Psi> \<rhd> \<lparr>\<nu>x'\<rparr>(\<lparr>\<nu>y\<rparr>([(x, x')] \<bullet> P)) \<longmapsto>M\<lparr>\<nu>*(xvec1@x'#xvec2)\<rparr>\<langle>N\<rangle> \<prec> \<lparr>\<nu>y\<rparr>P'" 
          using `x' \<in> supp N` `x' \<sharp> \<Psi>` `x' \<sharp> M` `x' \<sharp> xvec1` `x' \<sharp> xvec2`
          by(rule Open)
        with `y \<noteq> x'` `x \<noteq> y` `x' \<sharp> P` have "\<Psi> \<rhd> \<lparr>\<nu>x\<rparr>(\<lparr>\<nu>y\<rparr>P) \<longmapsto>M\<lparr>\<nu>*(xvec1@x'#xvec2)\<rparr>\<langle>N\<rangle> \<prec> \<lparr>\<nu>y\<rparr>P'"
          by(subst alphaRes[where y=x']) (simp add: abs_fresh eqvts calc_atm)+
        moreover have "(\<Psi>, \<lparr>\<nu>y\<rparr>P', \<lparr>\<nu>y\<rparr>P') \<in> Rel" by(rule R1)
        ultimately show ?case by blast
      next
        case(cRes P')
        from `\<Psi> \<rhd> P \<longmapsto>\<alpha> \<prec> P'` `y \<sharp> \<Psi>` `y \<sharp> \<alpha>`
        have "\<Psi> \<rhd> \<lparr>\<nu>y\<rparr>P \<longmapsto>\<alpha> \<prec> \<lparr>\<nu>y\<rparr>P'" by(rule Scope)
        hence "\<Psi> \<rhd> \<lparr>\<nu>x\<rparr>(\<lparr>\<nu>y\<rparr>P) \<longmapsto>\<alpha> \<prec> \<lparr>\<nu>x\<rparr>(\<lparr>\<nu>y\<rparr>P')" using `x \<sharp> \<Psi>` `x \<sharp> \<alpha>`
          by(rule Scope)
        moreover from `x \<sharp> \<Psi>` `y \<sharp> \<Psi>` have "(\<Psi>, \<lparr>\<nu>x\<rparr>(\<lparr>\<nu>y\<rparr>P'), \<lparr>\<nu>y\<rparr>(\<lparr>\<nu>x\<rparr>P')) \<in> Rel"
          by(rule R2)
        ultimately show ?case by blast
      qed
    qed
  qed
qed

lemma parAssocLeft:
  fixes \<Psi>   :: 'b
  and   P   :: "('a, 'b, 'c) psi"
  and   Q   :: "('a, 'b, 'c) psi"
  and   R   :: "('a, 'b, 'c) psi"
  and   Rel :: "('b \<times> ('a, 'b, 'c) psi \<times> ('a, 'b, 'c) psi) set"

  assumes "eqvt Rel"
  and     C1: "\<And>\<Psi>' S T U. (\<Psi>, (S \<parallel> T) \<parallel> U, S \<parallel> (T \<parallel> U)) \<in> Rel"
  and     C2: "\<And>xvec \<Psi>' S T U. \<lbrakk>xvec \<sharp>* \<Psi>'; xvec \<sharp>* S\<rbrakk> \<Longrightarrow> (\<Psi>', \<lparr>\<nu>*xvec\<rparr>((S \<parallel> T) \<parallel> U), S \<parallel> (\<lparr>\<nu>*xvec\<rparr>(T \<parallel> U))) \<in> Rel"
  and     C3: "\<And>xvec \<Psi>' S T U. \<lbrakk>xvec \<sharp>* \<Psi>'; xvec \<sharp>* U\<rbrakk> \<Longrightarrow> (\<Psi>', (\<lparr>\<nu>*xvec\<rparr>(S \<parallel> T)) \<parallel> U, \<lparr>\<nu>*xvec\<rparr>(S \<parallel> (T \<parallel> U))) \<in> Rel"
  and     C4: "\<And>\<Psi>' S T xvec. \<lbrakk>(\<Psi>', S, T) \<in> Rel; xvec \<sharp>* \<Psi>'\<rbrakk> \<Longrightarrow> (\<Psi>', \<lparr>\<nu>*xvec\<rparr>S, \<lparr>\<nu>*xvec\<rparr>T) \<in> Rel"

  shows "\<Psi> \<rhd> (P \<parallel> Q) \<parallel> R \<leadsto>[Rel] P \<parallel> (Q \<parallel> R)"
using `eqvt Rel`
proof(induct rule: simI[of _ _ _ _ "()"])
  case(cSim \<alpha> PQR) 
  from `bn \<alpha> \<sharp>* (P \<parallel> Q \<parallel> R)` have "bn \<alpha> \<sharp>* P" and "bn \<alpha> \<sharp>* Q" and "bn \<alpha> \<sharp>* R" by simp+
  hence "bn \<alpha> \<sharp>* (Q \<parallel> R)" by simp
  with `\<Psi> \<rhd> P \<parallel> (Q \<parallel> R) \<longmapsto>\<alpha> \<prec> PQR` `bn \<alpha> \<sharp>* \<Psi>` `bn \<alpha> \<sharp>* P`
  show ?case using `bn \<alpha> \<sharp>* subject \<alpha>`
  proof(induct rule: parCases[where C = "(\<Psi>, P, Q, R, \<alpha>)"])
    case(cPar1 P' A\<^sub>Q\<^sub>R \<Psi>\<^sub>Q\<^sub>R)
    from `A\<^sub>Q\<^sub>R \<sharp>* (\<Psi>, P, Q, R, \<alpha>)` have "A\<^sub>Q\<^sub>R \<sharp>* Q" and  "A\<^sub>Q\<^sub>R \<sharp>* R"
      by simp+
    with `extractFrame(Q \<parallel> R) = \<langle>A\<^sub>Q\<^sub>R, \<Psi>\<^sub>Q\<^sub>R\<rangle>` `distinct A\<^sub>Q\<^sub>R`
    obtain A\<^sub>Q \<Psi>\<^sub>Q A\<^sub>R \<Psi>\<^sub>R where "A\<^sub>Q\<^sub>R = A\<^sub>Q@A\<^sub>R" and "\<Psi>\<^sub>Q\<^sub>R = \<Psi>\<^sub>Q \<otimes> \<Psi>\<^sub>R" and FrQ: "extractFrame Q = \<langle>A\<^sub>Q, \<Psi>\<^sub>Q\<rangle>" and  FrR: "extractFrame R = \<langle>A\<^sub>R, \<Psi>\<^sub>R\<rangle>"
                           and "A\<^sub>Q \<sharp>* \<Psi>\<^sub>R" and "A\<^sub>R \<sharp>* \<Psi>\<^sub>Q"
      by(rule_tac mergeFrameE) (auto dest: extractFrameFreshChain)

    from `A\<^sub>Q\<^sub>R = A\<^sub>Q@A\<^sub>R` `A\<^sub>Q\<^sub>R \<sharp>* \<Psi>` `A\<^sub>Q\<^sub>R \<sharp>* P` `A\<^sub>Q\<^sub>R \<sharp>* Q` `A\<^sub>Q\<^sub>R \<sharp>* \<alpha>`
    have "A\<^sub>Q \<sharp>* \<Psi>" and "A\<^sub>R \<sharp>* \<Psi>" and "A\<^sub>Q \<sharp>* P" and "A\<^sub>R \<sharp>* P" and "A\<^sub>Q \<sharp>* Q" and "A\<^sub>R \<sharp>* Q" and "A\<^sub>Q \<sharp>* \<alpha>" and "A\<^sub>R \<sharp>* \<alpha>"
      by simp+

    from `\<Psi> \<otimes> \<Psi>\<^sub>Q\<^sub>R \<rhd> P \<longmapsto>\<alpha> \<prec> P'` `\<Psi>\<^sub>Q\<^sub>R = \<Psi>\<^sub>Q \<otimes> \<Psi>\<^sub>R` have "(\<Psi> \<otimes> \<Psi>\<^sub>R) \<otimes> \<Psi>\<^sub>Q \<rhd> P \<longmapsto>\<alpha> \<prec> P'"
      by(metis statEqTransition Associativity Commutativity Composition)
    hence "\<Psi> \<otimes> \<Psi>\<^sub>R \<rhd> P \<parallel> Q \<longmapsto>\<alpha> \<prec> (P' \<parallel> Q)" using FrQ `bn \<alpha> \<sharp>* Q` `A\<^sub>Q \<sharp>* \<Psi>` `A\<^sub>Q \<sharp>* \<Psi>\<^sub>R` `A\<^sub>Q \<sharp>* P` `A\<^sub>Q \<sharp>* \<alpha>`
      by(rule_tac Par1) auto
    hence "\<Psi> \<rhd> (P \<parallel> Q) \<parallel> R \<longmapsto>\<alpha> \<prec> ((P' \<parallel> Q) \<parallel> R)" using FrR `bn \<alpha> \<sharp>* R` `A\<^sub>R \<sharp>* \<Psi>` `A\<^sub>R \<sharp>* P` `A\<^sub>R \<sharp>* Q` `A\<^sub>R \<sharp>* \<alpha>`
      by(rule_tac Par1) auto
    moreover have "(\<Psi>, (P' \<parallel> Q) \<parallel> R, P' \<parallel> (Q \<parallel> R)) \<in> Rel" by(rule C1)
    ultimately show ?case by blast
  next
    case(cPar2 QR A\<^sub>P \<Psi>\<^sub>P)
    from `A\<^sub>P \<sharp>* (\<Psi>, P, Q, R, \<alpha>)` have "A\<^sub>P \<sharp>* Q" and "A\<^sub>P \<sharp>* R" and "A\<^sub>P \<sharp>* \<alpha>"
      by simp+
    have FrP: "extractFrame P = \<langle>A\<^sub>P, \<Psi>\<^sub>P\<rangle>" by fact
    with `bn \<alpha> \<sharp>* P` `A\<^sub>P \<sharp>* \<alpha>` have "bn \<alpha> \<sharp>* \<Psi>\<^sub>P" by(auto dest: extractFrameFreshChain)
    with `bn \<alpha> \<sharp>* \<Psi>` have "bn \<alpha> \<sharp>* (\<Psi> \<otimes> \<Psi>\<^sub>P)" by force
    with `\<Psi> \<otimes> \<Psi>\<^sub>P \<rhd> Q \<parallel> R \<longmapsto>\<alpha> \<prec> QR`
    show ?case using `bn \<alpha> \<sharp>* Q` `bn \<alpha> \<sharp>* R` `bn \<alpha> \<sharp>* subject \<alpha>` `A\<^sub>P \<sharp>* Q` `A\<^sub>P \<sharp>* R`
    proof(induct rule: parCasesSubject[where C = "(A\<^sub>P, \<Psi>\<^sub>P, P, Q, R, \<Psi>)"])
      case(cPar1 Q' A\<^sub>R \<Psi>\<^sub>R)
      from `A\<^sub>R \<sharp>* (A\<^sub>P, \<Psi>\<^sub>P, P, Q, R, \<Psi>)` have "A\<^sub>R \<sharp>* A\<^sub>P" and "A\<^sub>R \<sharp>* P" and "A\<^sub>R \<sharp>* Q" and "A\<^sub>R \<sharp>* \<Psi>\<^sub>P" and "A\<^sub>R \<sharp>* \<Psi>"
        by simp+
      from `A\<^sub>P \<sharp>* R` `extractFrame R = \<langle>A\<^sub>R, \<Psi>\<^sub>R\<rangle>` `A\<^sub>R \<sharp>* A\<^sub>P` have "A\<^sub>P \<sharp>* \<Psi>\<^sub>R"
        by(drule_tac extractFrameFreshChain) auto
      from `(\<Psi> \<otimes> \<Psi>\<^sub>P) \<otimes> \<Psi>\<^sub>R \<rhd> Q \<longmapsto>\<alpha> \<prec> Q'` have "(\<Psi> \<otimes> \<Psi>\<^sub>R) \<otimes> \<Psi>\<^sub>P \<rhd> Q \<longmapsto>\<alpha> \<prec> Q'" 
        by(metis statEqTransition Associativity Commutativity Composition)
      hence "\<Psi> \<otimes> \<Psi>\<^sub>R \<rhd> P \<parallel> Q \<longmapsto>\<alpha> \<prec> (P \<parallel> Q')"
        using FrP `bn \<alpha> \<sharp>* P` `A\<^sub>P \<sharp>* \<Psi>` `A\<^sub>P \<sharp>* \<Psi>\<^sub>R` `A\<^sub>P \<sharp>* Q` `A\<^sub>P \<sharp>* \<alpha>`
        by(rule_tac Par2) (assumption | force)+
      hence "\<Psi> \<rhd> (P \<parallel> Q) \<parallel> R \<longmapsto>\<alpha> \<prec> ((P \<parallel> Q') \<parallel> R)"
        using `extractFrame R = \<langle>A\<^sub>R, \<Psi>\<^sub>R\<rangle>` `bn \<alpha> \<sharp>* R` `A\<^sub>R \<sharp>* \<Psi>` `A\<^sub>R \<sharp>* P` `A\<^sub>R \<sharp>* Q` `A\<^sub>R \<sharp>* \<alpha>`
        by(rule_tac Par1) (assumption | simp)+
      moreover have "(\<Psi>, (P \<parallel> Q') \<parallel> R, P \<parallel> (Q' \<parallel> R)) \<in> Rel" by(rule C1)
      ultimately show ?case by blast
    next
      case(cPar2 R' A\<^sub>Q \<Psi>\<^sub>Q)
      from `A\<^sub>Q \<sharp>* (A\<^sub>P, \<Psi>\<^sub>P, P, Q, R, \<Psi>)` have "A\<^sub>Q \<sharp>* A\<^sub>P" and "A\<^sub>Q \<sharp>* R" and "A\<^sub>Q \<sharp>* \<Psi>\<^sub>P" and "A\<^sub>Q \<sharp>* \<Psi>"
        by simp+
      have FrQ: "extractFrame Q = \<langle>A\<^sub>Q, \<Psi>\<^sub>Q\<rangle>" by fact
      from `A\<^sub>P \<sharp>* Q` FrQ `A\<^sub>Q \<sharp>* A\<^sub>P` have "A\<^sub>P \<sharp>* \<Psi>\<^sub>Q"
        by(drule_tac extractFrameFreshChain) auto
      from `(\<Psi> \<otimes> \<Psi>\<^sub>P) \<otimes> \<Psi>\<^sub>Q \<rhd> R \<longmapsto>\<alpha> \<prec> R'`
      have "\<Psi> \<otimes> (\<Psi>\<^sub>P \<otimes> \<Psi>\<^sub>Q) \<rhd> R \<longmapsto>\<alpha> \<prec> R'"
        by(blast intro: statEqTransition Associativity)
      moreover from FrP FrQ `A\<^sub>Q \<sharp>* A\<^sub>P` `A\<^sub>P \<sharp>* \<Psi>\<^sub>Q`  `A\<^sub>Q \<sharp>* \<Psi>\<^sub>P` 
      have "extractFrame(P \<parallel> Q) = \<langle>(A\<^sub>P@A\<^sub>Q), \<Psi>\<^sub>P \<otimes> \<Psi>\<^sub>Q\<rangle> " by simp
      moreover from `bn \<alpha> \<sharp>* P` `bn \<alpha> \<sharp>* Q` have "bn \<alpha> \<sharp>* (P \<parallel> Q)" by simp
      moreover from `A\<^sub>P \<sharp>* \<Psi>` `A\<^sub>Q \<sharp>* \<Psi>` have "(A\<^sub>P@A\<^sub>Q) \<sharp>* \<Psi>" by simp
      moreover from `A\<^sub>P \<sharp>* R` `A\<^sub>Q \<sharp>* R` have "(A\<^sub>P@A\<^sub>Q) \<sharp>* R" by simp
      moreover from `A\<^sub>P \<sharp>* \<alpha>` `A\<^sub>Q \<sharp>* \<alpha>` have "(A\<^sub>P@A\<^sub>Q) \<sharp>* \<alpha>" by simp
      ultimately have "\<Psi> \<rhd> (P \<parallel> Q) \<parallel> R \<longmapsto>\<alpha> \<prec> ((P \<parallel> Q) \<parallel> R')"
        by(rule Par2) 
      moreover have "(\<Psi>, (P \<parallel> Q) \<parallel> R', P \<parallel> (Q \<parallel> R')) \<in> Rel" by(rule C1)
      ultimately show ?case by blast
    next
      case(cComm1 \<Psi>\<^sub>R M N Q' A\<^sub>Q \<Psi>\<^sub>Q K xvec R' A\<^sub>R) 
      from `A\<^sub>Q \<sharp>* (A\<^sub>P, \<Psi>\<^sub>P, P, Q, R, \<Psi>)`
      have "A\<^sub>Q \<sharp>* P" and "A\<^sub>Q \<sharp>* Q" and "A\<^sub>Q \<sharp>* R" and "A\<^sub>Q \<sharp>* A\<^sub>P" and "A\<^sub>Q \<sharp>* \<Psi>\<^sub>P"  and "A\<^sub>Q \<sharp>* \<Psi>" by simp+
      from `A\<^sub>R \<sharp>* (A\<^sub>P, \<Psi>\<^sub>P, P, Q, R, \<Psi>)` have "A\<^sub>R \<sharp>* P" and "A\<^sub>R \<sharp>* Q" and "A\<^sub>R \<sharp>* R" and "A\<^sub>R \<sharp>* A\<^sub>P"  and "A\<^sub>R \<sharp>* \<Psi>" by simp+
      from `xvec \<sharp>* (A\<^sub>P,  \<Psi>\<^sub>P, P, Q, R, \<Psi>)` have "xvec \<sharp>* A\<^sub>P" and "xvec \<sharp>* P" and "xvec \<sharp>* Q" and "xvec \<sharp>* \<Psi>" by simp+

      have FrQ: "extractFrame Q = \<langle>A\<^sub>Q, \<Psi>\<^sub>Q\<rangle>" by fact
      with `A\<^sub>P \<sharp>* Q` `A\<^sub>Q \<sharp>* A\<^sub>P` have "A\<^sub>P \<sharp>* \<Psi>\<^sub>Q"
        by(drule_tac extractFrameFreshChain) auto
      have FrR: "extractFrame R = \<langle>A\<^sub>R, \<Psi>\<^sub>R\<rangle>" by fact
      with `A\<^sub>P \<sharp>* R` `A\<^sub>R \<sharp>* A\<^sub>P` have "A\<^sub>P \<sharp>* \<Psi>\<^sub>R"
        by(drule_tac extractFrameFreshChain) auto
      from `(\<Psi> \<otimes> \<Psi>\<^sub>P) \<otimes> \<Psi>\<^sub>Q \<rhd> R \<longmapsto>K\<lparr>\<nu>*xvec\<rparr>\<langle>N\<rangle> \<prec> R'` `A\<^sub>P \<sharp>* R` `xvec \<sharp>* A\<^sub>P` `xvec \<sharp>* K` `distinct xvec` have "A\<^sub>P \<sharp>* N" 
        by(rule_tac outputFreshChainDerivative) auto

      from `(\<Psi> \<otimes> \<Psi>\<^sub>P) \<otimes> \<Psi>\<^sub>R \<rhd> Q \<longmapsto>M\<lparr>N\<rparr> \<prec> Q'` have "(\<Psi> \<otimes> \<Psi>\<^sub>R) \<otimes> \<Psi>\<^sub>P \<rhd> Q \<longmapsto>M\<lparr>N\<rparr> \<prec> Q'"
        by(metis statEqTransition Associativity Commutativity Composition)
      hence "\<Psi> \<otimes> \<Psi>\<^sub>R \<rhd> P \<parallel> Q \<longmapsto>M\<lparr>N\<rparr> \<prec> (P \<parallel> Q')" using FrP `A\<^sub>P \<sharp>* \<Psi>` `A\<^sub>P \<sharp>* \<Psi>\<^sub>R` `A\<^sub>P \<sharp>* Q` `A\<^sub>P \<sharp>* M` `A\<^sub>P \<sharp>* N`
        by(rule_tac Par2) auto
      moreover from FrP FrQ `A\<^sub>P \<sharp>* \<Psi>\<^sub>Q` `A\<^sub>Q \<sharp>* A\<^sub>P` `A\<^sub>Q \<sharp>* \<Psi>\<^sub>P` have "extractFrame(P \<parallel> Q) = \<langle>(A\<^sub>P@A\<^sub>Q), \<Psi>\<^sub>P \<otimes> \<Psi>\<^sub>Q\<rangle>"
        by simp
      moreover from  `(\<Psi> \<otimes> \<Psi>\<^sub>P) \<otimes> \<Psi>\<^sub>Q \<rhd> R \<longmapsto>K\<lparr>\<nu>*xvec\<rparr>\<langle>N\<rangle> \<prec> R'` have "\<Psi> \<otimes> \<Psi>\<^sub>P \<otimes> \<Psi>\<^sub>Q \<rhd> R \<longmapsto>K\<lparr>\<nu>*xvec\<rparr>\<langle>N\<rangle> \<prec> R'"
        by(metis statEqTransition Associativity)
      moreover note `extractFrame R = \<langle>A\<^sub>R, \<Psi>\<^sub>R\<rangle>`
      moreover from `(\<Psi> \<otimes> \<Psi>\<^sub>P) \<otimes> \<Psi>\<^sub>Q \<otimes> \<Psi>\<^sub>R \<turnstile> M \<leftrightarrow> K` have "\<Psi> \<otimes> (\<Psi>\<^sub>P \<otimes> \<Psi>\<^sub>Q) \<otimes> \<Psi>\<^sub>R \<turnstile> M \<leftrightarrow> K"
        by(metis statEqEnt Associativity Commutativity Composition)
      ultimately have "\<Psi> \<rhd> (P \<parallel> Q) \<parallel> R \<longmapsto>\<tau> \<prec> \<lparr>\<nu>*xvec\<rparr>((P \<parallel> Q') \<parallel> R')"
        using `A\<^sub>P \<sharp>* \<Psi>` `A\<^sub>Q \<sharp>* \<Psi>` `A\<^sub>R \<sharp>* \<Psi>` `A\<^sub>P \<sharp>* P` `A\<^sub>Q \<sharp>* P` `A\<^sub>R \<sharp>* P` `A\<^sub>P \<sharp>* Q` `A\<^sub>Q \<sharp>* Q` `A\<^sub>R \<sharp>* Q` `A\<^sub>P \<sharp>* R` `A\<^sub>Q \<sharp>* R` `A\<^sub>R \<sharp>* R`
              `A\<^sub>P \<sharp>* M` `A\<^sub>Q \<sharp>* M` `A\<^sub>R \<sharp>* K` `A\<^sub>R \<sharp>* A\<^sub>P` `A\<^sub>Q \<sharp>* A\<^sub>R` `xvec \<sharp>* P` `xvec \<sharp>* Q`
        by(rule_tac Comm1) (assumption | simp)+
      moreover from `xvec \<sharp>* \<Psi>` `xvec \<sharp>* P` have "(\<Psi>, \<lparr>\<nu>*xvec\<rparr>((P \<parallel> Q') \<parallel> R'), P \<parallel> (\<lparr>\<nu>*xvec\<rparr>(Q' \<parallel> R'))) \<in> Rel"
        by(rule C2)
      ultimately show ?case by blast
    next
      case(cComm2 \<Psi>\<^sub>R M xvec N Q' A\<^sub>Q \<Psi>\<^sub>Q K R' A\<^sub>R) 
      from `A\<^sub>Q \<sharp>* (A\<^sub>P,  \<Psi>\<^sub>P, P, Q, R, \<Psi>)`
      have "A\<^sub>Q \<sharp>* P" and "A\<^sub>Q \<sharp>* Q" and "A\<^sub>Q \<sharp>* R" and "A\<^sub>Q \<sharp>* A\<^sub>P" and "A\<^sub>Q \<sharp>* \<Psi>" and "A\<^sub>Q \<sharp>* \<Psi>\<^sub>P" by simp+
      from `A\<^sub>R \<sharp>* (A\<^sub>P,  \<Psi>\<^sub>P, P, Q, R, \<Psi>)` have "A\<^sub>R \<sharp>* P" and "A\<^sub>R \<sharp>* Q" and "A\<^sub>R \<sharp>* R" and "A\<^sub>R \<sharp>* A\<^sub>P"and "A\<^sub>R \<sharp>* \<Psi>" by simp+
      from `xvec \<sharp>* (A\<^sub>P,  \<Psi>\<^sub>P, P, Q, R, \<Psi>)` have "xvec \<sharp>* A\<^sub>P" and "xvec \<sharp>* P" and "xvec \<sharp>* Q" and "xvec \<sharp>* \<Psi>" by simp+

      have FrQ: "extractFrame Q = \<langle>A\<^sub>Q, \<Psi>\<^sub>Q\<rangle>" by fact
      with `A\<^sub>P \<sharp>* Q` `A\<^sub>Q \<sharp>* A\<^sub>P` have "A\<^sub>P \<sharp>* \<Psi>\<^sub>Q"
        by(drule_tac extractFrameFreshChain) auto
      have FrR: "extractFrame R = \<langle>A\<^sub>R, \<Psi>\<^sub>R\<rangle>" by fact
      with `A\<^sub>P \<sharp>* R` `A\<^sub>R \<sharp>* A\<^sub>P` have "A\<^sub>P \<sharp>* \<Psi>\<^sub>R"
        by(drule_tac extractFrameFreshChain) auto

      from `(\<Psi> \<otimes> \<Psi>\<^sub>P) \<otimes> \<Psi>\<^sub>R \<rhd> Q \<longmapsto>M\<lparr>\<nu>*xvec\<rparr>\<langle>N\<rangle> \<prec> Q'` `A\<^sub>P \<sharp>* Q` `xvec \<sharp>* A\<^sub>P` `xvec \<sharp>* M` `distinct xvec` have "A\<^sub>P \<sharp>* N" 
        by(rule_tac outputFreshChainDerivative) auto

      from `(\<Psi> \<otimes> \<Psi>\<^sub>P) \<otimes> \<Psi>\<^sub>R \<rhd> Q \<longmapsto>M\<lparr>\<nu>*xvec\<rparr>\<langle>N\<rangle> \<prec> Q'` have "(\<Psi> \<otimes> \<Psi>\<^sub>R) \<otimes> \<Psi>\<^sub>P \<rhd> Q \<longmapsto>M\<lparr>\<nu>*xvec\<rparr>\<langle>N\<rangle> \<prec> Q'"
        by(metis statEqTransition Associativity Commutativity Composition)
      hence "\<Psi> \<otimes> \<Psi>\<^sub>R \<rhd> P \<parallel> Q \<longmapsto>M\<lparr>\<nu>*xvec\<rparr>\<langle>N\<rangle> \<prec> (P \<parallel> Q')" using FrP `A\<^sub>P \<sharp>* \<Psi>` `A\<^sub>P \<sharp>* \<Psi>\<^sub>R` `A\<^sub>P \<sharp>* Q` `A\<^sub>P \<sharp>* M` `A\<^sub>P \<sharp>* N` `xvec \<sharp>* P` `xvec \<sharp>* A\<^sub>P`
        by(rule_tac Par2) auto
      moreover from FrP FrQ `A\<^sub>P \<sharp>* \<Psi>\<^sub>Q` `A\<^sub>Q \<sharp>* A\<^sub>P` `A\<^sub>Q \<sharp>* \<Psi>\<^sub>P` have "extractFrame(P \<parallel> Q) = \<langle>(A\<^sub>P@A\<^sub>Q), \<Psi>\<^sub>P \<otimes> \<Psi>\<^sub>Q\<rangle>"
        by simp+
      moreover from  `(\<Psi> \<otimes> \<Psi>\<^sub>P) \<otimes> \<Psi>\<^sub>Q \<rhd> R \<longmapsto>K\<lparr>N\<rparr> \<prec> R'` have "\<Psi> \<otimes> \<Psi>\<^sub>P \<otimes> \<Psi>\<^sub>Q \<rhd> R \<longmapsto>K\<lparr>N\<rparr> \<prec> R'"
        by(metis statEqTransition Associativity)
      moreover note `extractFrame R = \<langle>A\<^sub>R, \<Psi>\<^sub>R\<rangle>`
      moreover from `(\<Psi> \<otimes> \<Psi>\<^sub>P) \<otimes> \<Psi>\<^sub>Q \<otimes> \<Psi>\<^sub>R \<turnstile> M \<leftrightarrow> K` have "\<Psi> \<otimes> (\<Psi>\<^sub>P \<otimes> \<Psi>\<^sub>Q) \<otimes> \<Psi>\<^sub>R \<turnstile> M \<leftrightarrow> K"
        by(metis statEqEnt Associativity Commutativity Composition)
      ultimately have "\<Psi> \<rhd> (P \<parallel> Q) \<parallel> R \<longmapsto>\<tau> \<prec> \<lparr>\<nu>*xvec\<rparr>((P \<parallel> Q') \<parallel> R')"
        using `A\<^sub>P \<sharp>* \<Psi>` `A\<^sub>Q \<sharp>* \<Psi>` `A\<^sub>R \<sharp>* \<Psi>` `A\<^sub>P \<sharp>* P` `A\<^sub>Q \<sharp>* P` `A\<^sub>R \<sharp>* P` `A\<^sub>P \<sharp>* Q` `A\<^sub>Q \<sharp>* Q` `A\<^sub>R \<sharp>* Q` `A\<^sub>P \<sharp>* R` `A\<^sub>Q \<sharp>* R` `A\<^sub>R \<sharp>* R`
              `A\<^sub>P \<sharp>* M` `A\<^sub>Q \<sharp>* M` `A\<^sub>R \<sharp>* K` `A\<^sub>R \<sharp>* A\<^sub>P` `A\<^sub>Q \<sharp>* A\<^sub>R` `xvec \<sharp>* R`
        by(rule_tac Comm2) (assumption | simp)+
      moreover from `xvec \<sharp>* \<Psi>` `xvec \<sharp>* P` have "(\<Psi>, \<lparr>\<nu>*xvec\<rparr>((P \<parallel> Q') \<parallel> R'), P \<parallel> (\<lparr>\<nu>*xvec\<rparr>(Q' \<parallel> R'))) \<in> Rel"
        by(rule C2)
      ultimately show ?case by blast
    qed
  next
    case(cComm1 \<Psi>\<^sub>Q\<^sub>R M N P' A\<^sub>P \<Psi>\<^sub>P K xvec QR' A\<^sub>Q\<^sub>R)
    from `xvec \<sharp>* (\<Psi>, P, Q, R, \<alpha>)` have "xvec \<sharp>* Q" and "xvec \<sharp>* R" by simp+
    from `A\<^sub>Q\<^sub>R \<sharp>* (\<Psi>, P, Q, R, \<alpha>)` have "A\<^sub>Q\<^sub>R \<sharp>* Q" and "A\<^sub>Q\<^sub>R \<sharp>* R" and "A\<^sub>Q\<^sub>R \<sharp>* \<Psi>" by simp+
    from `A\<^sub>P \<sharp>* (Q \<parallel> R)` have "A\<^sub>P \<sharp>* Q" and "A\<^sub>P \<sharp>* R" by simp+
    have PTrans: "\<Psi> \<otimes> \<Psi>\<^sub>Q\<^sub>R \<rhd> P \<longmapsto>M\<lparr>N\<rparr> \<prec> P'" and FrP: "extractFrame P = \<langle>A\<^sub>P, \<Psi>\<^sub>P\<rangle>" and MeqK: "\<Psi> \<otimes> \<Psi>\<^sub>P \<otimes> \<Psi>\<^sub>Q\<^sub>R \<turnstile> M \<leftrightarrow> K" by fact+
    note `\<Psi> \<otimes> \<Psi>\<^sub>P \<rhd> Q \<parallel> R \<longmapsto>K\<lparr>\<nu>*xvec\<rparr>\<langle>N\<rangle> \<prec> QR'`  
    moreover from `xvec \<sharp>* \<Psi>` `xvec \<sharp>* \<Psi>\<^sub>P` have "xvec \<sharp>* (\<Psi> \<otimes> \<Psi>\<^sub>P)" by force
    moreover note `xvec \<sharp>* Q``xvec \<sharp>* R` `xvec \<sharp>* K`
         `extractFrame(Q \<parallel> R) = \<langle>A\<^sub>Q\<^sub>R, \<Psi>\<^sub>Q\<^sub>R\<rangle>` `distinct A\<^sub>Q\<^sub>R` 
    moreover from `A\<^sub>Q\<^sub>R \<sharp>* \<Psi>` `A\<^sub>Q\<^sub>R \<sharp>* \<Psi>\<^sub>P` have "A\<^sub>Q\<^sub>R \<sharp>* (\<Psi> \<otimes> \<Psi>\<^sub>P)" by force
    ultimately show ?case using `A\<^sub>Q\<^sub>R \<sharp>* Q` `A\<^sub>Q\<^sub>R \<sharp>* R` `A\<^sub>Q\<^sub>R \<sharp>* K`
    proof(induct rule: parCasesOutputFrame)
      case(cPar1 Q' A\<^sub>Q \<Psi>\<^sub>Q A\<^sub>R \<Psi>\<^sub>R)
      have Aeq: "A\<^sub>Q\<^sub>R = A\<^sub>Q@A\<^sub>R" and \<Psi>eq: "\<Psi>\<^sub>Q\<^sub>R = \<Psi>\<^sub>Q \<otimes> \<Psi>\<^sub>R" by fact+
      from PTrans \<Psi>eq have "(\<Psi> \<otimes> \<Psi>\<^sub>R) \<otimes> \<Psi>\<^sub>Q \<rhd> P \<longmapsto>M\<lparr>N\<rparr> \<prec> P'"
        by(metis statEqTransition Associativity Commutativity Composition)
      moreover note FrP
      moreover from `(\<Psi> \<otimes> \<Psi>\<^sub>P) \<otimes> \<Psi>\<^sub>R \<rhd> Q \<longmapsto>K\<lparr>\<nu>*xvec\<rparr>\<langle>N\<rangle> \<prec> Q'` have "(\<Psi> \<otimes> \<Psi>\<^sub>R) \<otimes> \<Psi>\<^sub>P \<rhd> Q \<longmapsto>K\<lparr>\<nu>*xvec\<rparr>\<langle>N\<rangle> \<prec> Q'"
        by(metis statEqTransition Associativity Commutativity Composition)
      moreover note `extractFrame Q = \<langle>A\<^sub>Q, \<Psi>\<^sub>Q\<rangle>`
      moreover from MeqK \<Psi>eq have "(\<Psi> \<otimes> \<Psi>\<^sub>R) \<otimes> \<Psi>\<^sub>P \<otimes> \<Psi>\<^sub>Q \<turnstile> M \<leftrightarrow> K"
        by(metis statEqEnt Associativity Commutativity Composition)
      moreover from `A\<^sub>P \<sharp>* R` `A\<^sub>P \<sharp>* A\<^sub>Q\<^sub>R` Aeq `extractFrame R = \<langle>A\<^sub>R, \<Psi>\<^sub>R\<rangle>` have "A\<^sub>P \<sharp>* A\<^sub>Q" and "A\<^sub>P \<sharp>* \<Psi>\<^sub>R"
        by(auto dest:  extractFrameFreshChain)
      moreover from `A\<^sub>Q\<^sub>R \<sharp>* P` `A\<^sub>Q\<^sub>R \<sharp>* \<Psi>` Aeq have "A\<^sub>Q \<sharp>* P" and "A\<^sub>Q \<sharp>* \<Psi>" by simp+
      ultimately have "\<Psi> \<otimes> \<Psi>\<^sub>R \<rhd> P \<parallel> Q \<longmapsto>\<tau> \<prec> \<lparr>\<nu>*xvec\<rparr>(P' \<parallel> Q')"
        using `A\<^sub>P \<sharp>* \<Psi>` `A\<^sub>P \<sharp>* P` `A\<^sub>P \<sharp>* Q` `A\<^sub>P \<sharp>* M` `A\<^sub>P \<sharp>* A\<^sub>Q` `A\<^sub>Q \<sharp>* \<Psi>` `A\<^sub>Q \<sharp>* \<Psi>\<^sub>R` `A\<^sub>Q \<sharp>* P` `A\<^sub>Q \<sharp>* Q` `A\<^sub>Q \<sharp>* K` `xvec \<sharp>* P`
        by(rule_tac Comm1) (assumption | force)+
      moreover from `A\<^sub>Q\<^sub>R \<sharp>* \<Psi>` Aeq have "A\<^sub>R \<sharp>* \<Psi>" by simp
      moreover from `A\<^sub>Q\<^sub>R \<sharp>* P` Aeq have "A\<^sub>R \<sharp>* P" by simp
      ultimately have "\<Psi> \<rhd> (P \<parallel> Q) \<parallel> R \<longmapsto>\<tau> \<prec> (\<lparr>\<nu>*xvec\<rparr>(P' \<parallel> Q')) \<parallel> R" using `extractFrame R = \<langle>A\<^sub>R, \<Psi>\<^sub>R\<rangle>` `A\<^sub>R \<sharp>* Q`
        by(rule_tac Par1) (assumption | simp)+
      moreover from `xvec \<sharp>* \<Psi>` `xvec \<sharp>* R` have "(\<Psi>, (\<lparr>\<nu>*xvec\<rparr>(P' \<parallel> Q')) \<parallel> R, \<lparr>\<nu>*xvec\<rparr>(P' \<parallel> (Q' \<parallel> R))) \<in> Rel"
        by(rule C3)
      ultimately show ?case by blast
    next
      case(cPar2 R' A\<^sub>Q \<Psi>\<^sub>Q A\<^sub>R \<Psi>\<^sub>R)
      have Aeq: "A\<^sub>Q\<^sub>R = A\<^sub>Q@A\<^sub>R" and \<Psi>eq: "\<Psi>\<^sub>Q\<^sub>R = \<Psi>\<^sub>Q \<otimes> \<Psi>\<^sub>R" by fact+
      from `A\<^sub>Q\<^sub>R \<sharp>* \<Psi>` `A\<^sub>Q\<^sub>R \<sharp>* P` `A\<^sub>Q\<^sub>R \<sharp>* \<Psi>\<^sub>P` `A\<^sub>P \<sharp>* A\<^sub>Q\<^sub>R` Aeq have "A\<^sub>R \<sharp>* \<Psi>" and "A\<^sub>R \<sharp>* \<Psi>\<^sub>P" and "A\<^sub>P \<sharp>* A\<^sub>R" and "A\<^sub>P \<sharp>* A\<^sub>Q" and "A\<^sub>R \<sharp>* P" by simp+
      from `A\<^sub>Q\<^sub>R \<sharp>* \<Psi>` Aeq have "A\<^sub>Q \<sharp>* \<Psi>" by simp
      from `A\<^sub>Q\<^sub>R \<sharp>* P` `A\<^sub>P \<sharp>* A\<^sub>Q\<^sub>R` Aeq FrP have "A\<^sub>Q \<sharp>* \<Psi>\<^sub>P" by(auto dest: extractFrameFreshChain)
      from `A\<^sub>P \<sharp>* A\<^sub>Q\<^sub>R` `extractFrame R = \<langle>A\<^sub>R, \<Psi>\<^sub>R\<rangle>` `extractFrame Q = \<langle>A\<^sub>Q, \<Psi>\<^sub>Q\<rangle>` Aeq `A\<^sub>P \<sharp>* Q` `A\<^sub>P \<sharp>* R` have "A\<^sub>P \<sharp>* \<Psi>\<^sub>Q" and  "A\<^sub>P \<sharp>* \<Psi>\<^sub>R" by(auto dest: extractFrameFreshChain)
      have RTrans: "(\<Psi> \<otimes> \<Psi>\<^sub>P) \<otimes> \<Psi>\<^sub>Q \<rhd> R \<longmapsto>K\<lparr>\<nu>*xvec\<rparr>\<langle>N\<rangle> \<prec> R'" and FrR: "extractFrame R = \<langle>A\<^sub>R, \<Psi>\<^sub>R\<rangle>" by fact+
      then obtain K' where KeqK': "((\<Psi> \<otimes> \<Psi>\<^sub>P) \<otimes> \<Psi>\<^sub>Q) \<otimes> \<Psi>\<^sub>R \<turnstile> K \<leftrightarrow> K'" and "A\<^sub>P \<sharp>* K'" and "A\<^sub>Q \<sharp>* K'"
      using `A\<^sub>P \<sharp>* R` `A\<^sub>Q \<sharp>* R` `A\<^sub>R \<sharp>* \<Psi>` `A\<^sub>R \<sharp>* \<Psi>\<^sub>P` `A\<^sub>R \<sharp>* \<Psi>\<^sub>Q` `A\<^sub>Q \<sharp>* A\<^sub>R` `A\<^sub>P \<sharp>* A\<^sub>R` `A\<^sub>R \<sharp>* R` `A\<^sub>R \<sharp>* R` `A\<^sub>R \<sharp>* K` `distinct A\<^sub>R` `xvec \<sharp>* K` `distinct xvec`
        by(rule_tac B="A\<^sub>P@A\<^sub>Q" in obtainPrefix) (assumption | force)+
      from PTrans \<Psi>eq have "(\<Psi> \<otimes> \<Psi>\<^sub>R) \<otimes> \<Psi>\<^sub>Q \<rhd> P \<longmapsto>M\<lparr>N\<rparr> \<prec> P'"
        by(metis statEqTransition Associativity Commutativity Composition)
      moreover from MeqK KeqK' \<Psi>eq have MeqK': "((\<Psi> \<otimes> \<Psi>\<^sub>R) \<otimes> \<Psi>\<^sub>Q) \<otimes> \<Psi>\<^sub>P \<turnstile> M \<leftrightarrow> K'"
        by(metis statEqEnt Associativity Commutativity Composition chanEqTrans)
      ultimately have "(\<Psi> \<otimes> \<Psi>\<^sub>R) \<otimes> \<Psi>\<^sub>Q \<rhd> P \<longmapsto>K'\<lparr>N\<rparr> \<prec> P'" using FrP `distinct A\<^sub>P` `A\<^sub>P \<sharp>* \<Psi>` `A\<^sub>P \<sharp>* P` `A\<^sub>P \<sharp>* M` `A\<^sub>P \<sharp>* K'` `A\<^sub>P \<sharp>* \<Psi>\<^sub>Q` `A\<^sub>P \<sharp>* \<Psi>\<^sub>R`
        by(rule_tac inputRenameSubject) auto
      moreover from `A\<^sub>Q\<^sub>R \<sharp>* P` `A\<^sub>Q\<^sub>R \<sharp>* N` Aeq have "A\<^sub>Q \<sharp>* P" and "A\<^sub>Q \<sharp>* N" by simp+
      ultimately have "\<Psi> \<otimes> \<Psi>\<^sub>R \<rhd> P \<parallel> Q \<longmapsto>K'\<lparr>N\<rparr> \<prec> P' \<parallel> Q" using `extractFrame Q = \<langle>A\<^sub>Q, \<Psi>\<^sub>Q\<rangle>` `A\<^sub>Q \<sharp>* \<Psi>\<^sub>R` `A\<^sub>Q \<sharp>* K'` `A\<^sub>Q \<sharp>* \<Psi>`
        by(rule_tac Par1) (assumption | force)+
      moreover from FrP `extractFrame Q = \<langle>A\<^sub>Q, \<Psi>\<^sub>Q\<rangle>` `A\<^sub>P \<sharp>* A\<^sub>Q` `A\<^sub>P \<sharp>* \<Psi>\<^sub>Q` `A\<^sub>Q \<sharp>* \<Psi>\<^sub>P`
      have "extractFrame(P \<parallel> Q) = \<langle>(A\<^sub>P@A\<^sub>Q), \<Psi>\<^sub>P \<otimes> \<Psi>\<^sub>Q\<rangle>" by simp+
      moreover from RTrans have "\<Psi> \<otimes> (\<Psi>\<^sub>P \<otimes> \<Psi>\<^sub>Q) \<rhd> R \<longmapsto>K\<lparr>\<nu>*xvec\<rparr>\<langle>N\<rangle> \<prec> R'" by(metis Associativity statEqTransition)
      moreover note FrR
      moreover from MeqK' KeqK' have "\<Psi> \<otimes> (\<Psi>\<^sub>P \<otimes> \<Psi>\<^sub>Q) \<otimes> \<Psi>\<^sub>R \<turnstile> K' \<leftrightarrow> K"
        by(metis statEqEnt Associativity Commutativity Composition chanEqTrans chanEqSym)
      ultimately have "\<Psi> \<rhd> (P \<parallel> Q) \<parallel> R \<longmapsto>\<tau> \<prec> \<lparr>\<nu>*xvec\<rparr>((P' \<parallel> Q) \<parallel> R')"
        using `A\<^sub>P \<sharp>* \<Psi>` `A\<^sub>Q \<sharp>* \<Psi>` `A\<^sub>P \<sharp>* P` `A\<^sub>Q \<sharp>* P` `A\<^sub>P \<sharp>* Q` `A\<^sub>Q \<sharp>* Q` `A\<^sub>P \<sharp>* R` `A\<^sub>Q \<sharp>* R` `A\<^sub>P \<sharp>* K'` `A\<^sub>Q \<sharp>* K'` `A\<^sub>P \<sharp>* A\<^sub>R` `A\<^sub>Q \<sharp>* A\<^sub>R`
              `A\<^sub>R \<sharp>* \<Psi>` `A\<^sub>R \<sharp>* P` `A\<^sub>R \<sharp>* Q` `A\<^sub>R \<sharp>* R` `A\<^sub>R \<sharp>* K` `xvec \<sharp>* P` `xvec \<sharp>* Q`
        by(rule_tac Comm1) (assumption | simp)+
      moreover from `xvec \<sharp>* \<Psi>` have "(\<Psi>, \<lparr>\<nu>*xvec\<rparr>((P' \<parallel> Q) \<parallel> R'), \<lparr>\<nu>*xvec\<rparr>(P' \<parallel> (Q \<parallel> R'))) \<in> Rel"
        by(metis C1 C4)
      ultimately show ?case by blast
    qed
  next
    case(cComm2 \<Psi>\<^sub>Q\<^sub>R M xvec N P' A\<^sub>P \<Psi>\<^sub>P K QR' A\<^sub>Q\<^sub>R)
    from `A\<^sub>Q\<^sub>R \<sharp>* (\<Psi>, P, Q, R, \<alpha>)` have "A\<^sub>Q\<^sub>R \<sharp>* Q" and "A\<^sub>Q\<^sub>R \<sharp>* R" and "A\<^sub>Q\<^sub>R \<sharp>* \<Psi>" by simp+
    from `A\<^sub>P \<sharp>* (Q \<parallel> R)` `xvec \<sharp>* (Q \<parallel> R)` have "A\<^sub>P \<sharp>* Q" and "A\<^sub>P \<sharp>* R" and "xvec \<sharp>* Q" and "xvec \<sharp>* R" by simp+
    have PTrans: "\<Psi> \<otimes> \<Psi>\<^sub>Q\<^sub>R \<rhd> P \<longmapsto>M\<lparr>\<nu>*xvec\<rparr>\<langle>N\<rangle> \<prec> P'" and FrP: "extractFrame P = \<langle>A\<^sub>P, \<Psi>\<^sub>P\<rangle>" and MeqK: "\<Psi> \<otimes> \<Psi>\<^sub>P \<otimes> \<Psi>\<^sub>Q\<^sub>R \<turnstile> M \<leftrightarrow> K" by fact+
    note `\<Psi> \<otimes> \<Psi>\<^sub>P \<rhd> Q \<parallel> R \<longmapsto>K\<lparr>N\<rparr> \<prec> QR'` `extractFrame(Q \<parallel> R) = \<langle>A\<^sub>Q\<^sub>R, \<Psi>\<^sub>Q\<^sub>R\<rangle>` `distinct A\<^sub>Q\<^sub>R` 
    moreover from `A\<^sub>Q\<^sub>R \<sharp>* \<Psi>` `A\<^sub>Q\<^sub>R \<sharp>* \<Psi>\<^sub>P` have "A\<^sub>Q\<^sub>R \<sharp>* (\<Psi> \<otimes> \<Psi>\<^sub>P)" by force
    ultimately show ?case using `A\<^sub>Q\<^sub>R \<sharp>* Q` `A\<^sub>Q\<^sub>R \<sharp>* R` `A\<^sub>Q\<^sub>R \<sharp>* K`
    proof(induct rule: parCasesInputFrame)
      case(cPar1 Q' A\<^sub>Q \<Psi>\<^sub>Q A\<^sub>R \<Psi>\<^sub>R)
      have Aeq: "A\<^sub>Q\<^sub>R = A\<^sub>Q@A\<^sub>R" and \<Psi>eq: "\<Psi>\<^sub>Q\<^sub>R = \<Psi>\<^sub>Q \<otimes> \<Psi>\<^sub>R" by fact+
      from PTrans \<Psi>eq have "(\<Psi> \<otimes> \<Psi>\<^sub>R) \<otimes> \<Psi>\<^sub>Q \<rhd> P \<longmapsto>M\<lparr>\<nu>*xvec\<rparr>\<langle>N\<rangle> \<prec> P'"
        by(metis statEqTransition Associativity Commutativity Composition)
      moreover note FrP
      moreover from `(\<Psi> \<otimes> \<Psi>\<^sub>P) \<otimes> \<Psi>\<^sub>R \<rhd> Q \<longmapsto>K\<lparr>N\<rparr> \<prec> Q'` have "(\<Psi> \<otimes> \<Psi>\<^sub>R) \<otimes> \<Psi>\<^sub>P \<rhd> Q \<longmapsto>K\<lparr>N\<rparr> \<prec> Q'"
        by(metis statEqTransition Associativity Commutativity Composition)
      moreover note `extractFrame Q = \<langle>A\<^sub>Q, \<Psi>\<^sub>Q\<rangle>`
      moreover from MeqK \<Psi>eq have "(\<Psi> \<otimes> \<Psi>\<^sub>R) \<otimes> \<Psi>\<^sub>P \<otimes> \<Psi>\<^sub>Q \<turnstile> M \<leftrightarrow> K"
        by(metis statEqEnt Associativity Commutativity Composition)
      moreover from `A\<^sub>P \<sharp>* Q` `A\<^sub>P \<sharp>* R` `A\<^sub>P \<sharp>* A\<^sub>Q\<^sub>R` Aeq `extractFrame Q = \<langle>A\<^sub>Q, \<Psi>\<^sub>Q\<rangle>` `extractFrame R = \<langle>A\<^sub>R, \<Psi>\<^sub>R\<rangle>`
      have "A\<^sub>P \<sharp>* A\<^sub>Q" and "A\<^sub>P \<sharp>* \<Psi>\<^sub>R" by(auto dest: extractFrameFreshChain)
      moreover from `A\<^sub>Q\<^sub>R \<sharp>* \<Psi>`  `A\<^sub>Q\<^sub>R \<sharp>* P` Aeq have "A\<^sub>Q \<sharp>* \<Psi>" and "A\<^sub>Q \<sharp>* P" by simp+
      ultimately have "\<Psi> \<otimes> \<Psi>\<^sub>R \<rhd> P \<parallel> Q \<longmapsto>\<tau> \<prec> \<lparr>\<nu>*xvec\<rparr>(P' \<parallel> Q')"
        using `A\<^sub>P \<sharp>* \<Psi>` `A\<^sub>P \<sharp>* P` `A\<^sub>P \<sharp>* Q` `A\<^sub>P \<sharp>* M` `A\<^sub>P \<sharp>* A\<^sub>Q` `A\<^sub>Q \<sharp>* \<Psi>` `A\<^sub>Q \<sharp>* \<Psi>\<^sub>R` `A\<^sub>Q \<sharp>* P` `A\<^sub>Q \<sharp>* Q` `A\<^sub>Q \<sharp>* K` `xvec \<sharp>* Q`
        by(rule_tac Comm2) (assumption | force)+
      moreover from `A\<^sub>Q\<^sub>R \<sharp>* \<Psi>` `A\<^sub>Q\<^sub>R \<sharp>* P` Aeq have "A\<^sub>R \<sharp>* \<Psi>" and "A\<^sub>R \<sharp>* P" by simp+
      ultimately have "\<Psi> \<rhd> (P \<parallel> Q) \<parallel> R \<longmapsto>\<tau> \<prec> (\<lparr>\<nu>*xvec\<rparr>(P' \<parallel> Q')) \<parallel> R" using `extractFrame R = \<langle>A\<^sub>R, \<Psi>\<^sub>R\<rangle>` `A\<^sub>R \<sharp>* Q`
        by(rule_tac Par1) (assumption | simp)+
      moreover from `xvec \<sharp>* \<Psi>` `xvec \<sharp>* R` have "(\<Psi>, (\<lparr>\<nu>*xvec\<rparr>(P' \<parallel> Q')) \<parallel> R, \<lparr>\<nu>*xvec\<rparr>(P' \<parallel> (Q' \<parallel> R))) \<in> Rel"
        by(rule C3)
      ultimately show ?case by blast
    next
      case(cPar2 R' A\<^sub>Q \<Psi>\<^sub>Q A\<^sub>R \<Psi>\<^sub>R)
      have Aeq: "A\<^sub>Q\<^sub>R = A\<^sub>Q@A\<^sub>R" and \<Psi>eq: "\<Psi>\<^sub>Q\<^sub>R = \<Psi>\<^sub>Q \<otimes> \<Psi>\<^sub>R" by fact+
      from `A\<^sub>Q\<^sub>R \<sharp>* \<Psi>` `A\<^sub>Q\<^sub>R \<sharp>* P` `A\<^sub>Q\<^sub>R \<sharp>* \<Psi>\<^sub>P` `A\<^sub>P \<sharp>* A\<^sub>Q\<^sub>R` Aeq 
      have "A\<^sub>R \<sharp>* \<Psi>" and "A\<^sub>R \<sharp>* \<Psi>\<^sub>P" and "A\<^sub>P \<sharp>* A\<^sub>R" and "A\<^sub>P \<sharp>* A\<^sub>Q" and "A\<^sub>R \<sharp>* P" and "A\<^sub>Q \<sharp>* \<Psi>" and "A\<^sub>Q \<sharp>* \<Psi>\<^sub>P" by simp+
      have RTrans: "(\<Psi> \<otimes> \<Psi>\<^sub>P) \<otimes> \<Psi>\<^sub>Q \<rhd> R \<longmapsto>K\<lparr>N\<rparr> \<prec> R'" and FrR: "extractFrame R = \<langle>A\<^sub>R, \<Psi>\<^sub>R\<rangle>" by fact+
      then obtain K' where KeqK': "((\<Psi> \<otimes> \<Psi>\<^sub>P) \<otimes> \<Psi>\<^sub>Q) \<otimes> \<Psi>\<^sub>R \<turnstile> K \<leftrightarrow> K'" and "A\<^sub>P \<sharp>* K'" and "A\<^sub>Q \<sharp>* K'"
      using `A\<^sub>P \<sharp>* R` `A\<^sub>Q \<sharp>* R` `A\<^sub>R \<sharp>* \<Psi>` `A\<^sub>R \<sharp>* \<Psi>\<^sub>P` `A\<^sub>R \<sharp>* \<Psi>\<^sub>Q` `A\<^sub>Q \<sharp>* A\<^sub>R` `A\<^sub>P \<sharp>* A\<^sub>R` `A\<^sub>R \<sharp>* R` `A\<^sub>R \<sharp>* R` `A\<^sub>R \<sharp>* K` `distinct A\<^sub>R`
        by(rule_tac B="A\<^sub>P@A\<^sub>Q" in obtainPrefix) (assumption | force)+
      from PTrans \<Psi>eq have "(\<Psi> \<otimes> \<Psi>\<^sub>R) \<otimes> \<Psi>\<^sub>Q \<rhd> P \<longmapsto>M\<lparr>\<nu>*xvec\<rparr>\<langle>N\<rangle> \<prec> P'"
        by(metis statEqTransition Associativity Commutativity Composition)
      moreover from MeqK KeqK' \<Psi>eq have MeqK': "((\<Psi> \<otimes> \<Psi>\<^sub>R) \<otimes> \<Psi>\<^sub>Q) \<otimes> \<Psi>\<^sub>P \<turnstile> M \<leftrightarrow> K'"
        by(metis statEqEnt Associativity Commutativity Composition chanEqTrans)
      moreover from `A\<^sub>P \<sharp>* R` `A\<^sub>P \<sharp>* Q` `A\<^sub>P \<sharp>* A\<^sub>Q\<^sub>R` FrR `extractFrame Q = \<langle>A\<^sub>Q, \<Psi>\<^sub>Q\<rangle>` Aeq have "A\<^sub>P \<sharp>* \<Psi>\<^sub>Q" and "A\<^sub>P \<sharp>* \<Psi>\<^sub>R"
        by(auto dest: extractFrameFreshChain)
      ultimately have "(\<Psi> \<otimes> \<Psi>\<^sub>R) \<otimes> \<Psi>\<^sub>Q \<rhd> P \<longmapsto>K'\<lparr>\<nu>*xvec\<rparr>\<langle>N\<rangle> \<prec> P'" using FrP `distinct A\<^sub>P` `A\<^sub>P \<sharp>* \<Psi>` `A\<^sub>P \<sharp>* P` `A\<^sub>P \<sharp>* M` `A\<^sub>P \<sharp>* K'`
        by(rule_tac outputRenameSubject) auto
      moreover from `A\<^sub>Q\<^sub>R \<sharp>* P` `A\<^sub>Q\<^sub>R \<sharp>* N` `A\<^sub>Q\<^sub>R \<sharp>* xvec` Aeq have "A\<^sub>Q \<sharp>* P" and "A\<^sub>Q \<sharp>* N" and "A\<^sub>Q \<sharp>* xvec" by simp+
      ultimately have "\<Psi> \<otimes> \<Psi>\<^sub>R \<rhd> P \<parallel> Q \<longmapsto>K'\<lparr>\<nu>*xvec\<rparr>\<langle>N\<rangle> \<prec> (P' \<parallel> Q)" using `extractFrame Q = \<langle>A\<^sub>Q, \<Psi>\<^sub>Q\<rangle>` `A\<^sub>Q \<sharp>* \<Psi>\<^sub>R` `A\<^sub>Q \<sharp>* K'` `xvec \<sharp>* Q` `A\<^sub>Q \<sharp>* \<Psi>`
        by(rule_tac Par1) (assumption | force)+
      moreover from FrP `extractFrame Q = \<langle>A\<^sub>Q, \<Psi>\<^sub>Q\<rangle>` `A\<^sub>P \<sharp>* A\<^sub>Q` `A\<^sub>P \<sharp>* \<Psi>\<^sub>Q` `A\<^sub>Q \<sharp>* \<Psi>\<^sub>P`
      have "extractFrame(P \<parallel> Q) = \<langle>(A\<^sub>P@A\<^sub>Q), \<Psi>\<^sub>P \<otimes> \<Psi>\<^sub>Q\<rangle>" by simp+
      moreover from RTrans have "\<Psi> \<otimes> (\<Psi>\<^sub>P \<otimes> \<Psi>\<^sub>Q) \<rhd> R \<longmapsto>K\<lparr>N\<rparr> \<prec> R'" by(metis Associativity statEqTransition)
      moreover note FrR
      moreover from MeqK' KeqK' have "\<Psi> \<otimes> (\<Psi>\<^sub>P \<otimes> \<Psi>\<^sub>Q) \<otimes> \<Psi>\<^sub>R \<turnstile> K' \<leftrightarrow> K"
        by(metis statEqEnt Associativity Commutativity Composition chanEqTrans chanEqSym)
      ultimately have "\<Psi> \<rhd> (P \<parallel> Q) \<parallel> R \<longmapsto>\<tau> \<prec> \<lparr>\<nu>*xvec\<rparr>((P' \<parallel> Q) \<parallel> R')"
        using `A\<^sub>P \<sharp>* \<Psi>` `A\<^sub>Q \<sharp>* \<Psi>` `A\<^sub>P \<sharp>* P` `A\<^sub>Q \<sharp>* P` `A\<^sub>P \<sharp>* Q` `A\<^sub>Q \<sharp>* Q` `A\<^sub>P \<sharp>* R` `A\<^sub>Q \<sharp>* R` `A\<^sub>P \<sharp>* K'` `A\<^sub>Q \<sharp>* K'` `A\<^sub>P \<sharp>* A\<^sub>R` `A\<^sub>Q \<sharp>* A\<^sub>R`
              `A\<^sub>R \<sharp>* \<Psi>` `A\<^sub>R \<sharp>* P` `A\<^sub>R \<sharp>* Q` `A\<^sub>R \<sharp>* R` `A\<^sub>R \<sharp>* K` `xvec \<sharp>* R`
        by(rule_tac Comm2) (assumption | simp)+
      moreover from `xvec \<sharp>* \<Psi>` have "(\<Psi>, \<lparr>\<nu>*xvec\<rparr>((P' \<parallel> Q) \<parallel> R'), \<lparr>\<nu>*xvec\<rparr>(P' \<parallel> (Q \<parallel> R'))) \<in> Rel"
        by(metis C1 C4)
      ultimately show ?case by blast
    qed
  qed
qed

lemma parNilLeft:
  fixes \<Psi> :: 'b
  and   P   :: "('a, 'b, 'c) psi"
  and   Rel :: "('b \<times> ('a, 'b, 'c) psi \<times> ('a, 'b, 'c) psi) set"  

  assumes "eqvt Rel"
  and     C1: "\<And>Q. (\<Psi>, Q \<parallel> \<zero>, Q) \<in> Rel"

  shows "\<Psi> \<rhd> (P \<parallel> \<zero>) \<leadsto>[Rel] P"
using `eqvt Rel`
proof(induct rule: simI[of _ _ _ _ "()"])
  case(cSim \<alpha> P')
  from `\<Psi> \<rhd> P \<longmapsto>\<alpha> \<prec> P'` have "\<Psi> \<otimes> SBottom' \<rhd> P \<longmapsto>\<alpha> \<prec> P'"
    by(metis statEqTransition Identity AssertionStatEqSym)
  hence "\<Psi> \<rhd> (P \<parallel> \<zero>) \<longmapsto>\<alpha> \<prec> (P' \<parallel> \<zero>)"
    by(rule_tac Par1) auto
  moreover have "(\<Psi>, P' \<parallel> \<zero>, P') \<in> Rel" by(rule C1)
  ultimately show ?case by blast
qed

lemma parNilRight:
  fixes \<Psi> :: 'b
  and   P   :: "('a, 'b, 'c) psi"
  and   Rel :: "('b \<times> ('a, 'b, 'c) psi \<times> ('a, 'b, 'c) psi) set"  

  assumes "eqvt Rel"
  and     C1: "\<And>Q. (\<Psi>, Q, (Q \<parallel> \<zero>)) \<in> Rel"

  shows "\<Psi> \<rhd> P \<leadsto>[Rel] (P \<parallel> \<zero>)"
using `eqvt Rel`
proof(induct rule: simI[of _ _ _ _ "()"])
  case(cSim \<alpha> P')
  note `\<Psi> \<rhd> P \<parallel> \<zero> \<longmapsto>\<alpha> \<prec> P'` `bn \<alpha> \<sharp>* \<Psi>` `bn \<alpha> \<sharp>* P`
  moreover have "bn \<alpha> \<sharp>* \<zero>" by simp
  ultimately show ?case using `bn \<alpha> \<sharp>* subject \<alpha>`
  proof(induct rule: parCases[where C="()"])
    case(cPar1 P' A\<^sub>Q \<Psi>\<^sub>Q)
    from `extractFrame(\<zero>) = \<langle>A\<^sub>Q, \<Psi>\<^sub>Q\<rangle>` have "\<Psi>\<^sub>Q = SBottom'" by auto
    with `\<Psi> \<otimes> \<Psi>\<^sub>Q \<rhd> P \<longmapsto>\<alpha> \<prec> P'` have "\<Psi> \<rhd> P \<longmapsto>\<alpha> \<prec> P'"
      by(metis statEqTransition Identity)
    moreover have "(\<Psi>, P', P' \<parallel> \<zero>) \<in> Rel" by(rule C1)
    ultimately show ?case by blast
  next
    case(cPar2 Q' A\<^sub>P \<Psi>\<^sub>P)
    from `\<Psi> \<otimes> \<Psi>\<^sub>P \<rhd> \<zero> \<longmapsto>\<alpha> \<prec> Q'` have False
      by auto
    thus ?case by simp
  next
    case(cComm1 \<Psi>\<^sub>Q M N P' A\<^sub>P \<Psi>\<^sub>P K xvec Q' A\<^sub>Q)
    from `\<Psi> \<otimes> \<Psi>\<^sub>P \<rhd> \<zero> \<longmapsto>K\<lparr>\<nu>*xvec\<rparr>\<langle>N\<rangle> \<prec> Q'` have False by auto
    thus ?case by simp
  next
    case(cComm2 \<Psi>\<^sub>Q M xvec N P' A\<^sub>P \<Psi>\<^sub>P K Q' A\<^sub>Q)
    from `\<Psi> \<otimes> \<Psi>\<^sub>P \<rhd> \<zero> \<longmapsto>K\<lparr>N\<rparr> \<prec> Q'` have False
      by auto
    thus ?case by simp
  qed
qed

lemma resNilLeft:
  fixes x   :: name
  and   \<Psi>   :: 'b
  and   Rel :: "('b \<times> ('a, 'b, 'c) psi \<times> ('a, 'b, 'c) psi) set"

  shows "\<Psi> \<rhd> \<lparr>\<nu>x\<rparr>\<zero> \<leadsto>[Rel] \<zero>"
by(auto simp add: simulation_def)

lemma resNilRight:
  fixes x   :: name
  and   \<Psi>   :: 'b
  and   Rel :: "('b \<times> ('a, 'b, 'c) psi \<times> ('a, 'b, 'c) psi) set"

  shows "\<Psi> \<rhd> \<zero> \<leadsto>[Rel] \<lparr>\<nu>x\<rparr>\<zero>"
using assms
apply(auto simp add: simulation_def)
by(cases rule: semantics.cases) (auto simp add: psi.inject alpha')

lemma inputPushResLeft:
  fixes \<Psi>   :: 'b
  and   x    :: name
  and   M    :: 'a
  and   xvec :: "name list"
  and   N    :: 'a
  and   P    :: "('a, 'b, 'c) psi"

  assumes "eqvt Rel"
  and     "x \<sharp> \<Psi>"
  and     "x \<sharp> M"
  and     "x \<sharp> xvec"
  and     "x \<sharp> N"
  and     C1: "\<And>Q. (\<Psi>, Q, Q) \<in> Rel"

  shows "\<Psi> \<rhd> \<lparr>\<nu>x\<rparr>(M\<lparr>\<lambda>*xvec N\<rparr>.P) \<leadsto>[Rel] M\<lparr>\<lambda>*xvec N\<rparr>.\<lparr>\<nu>x\<rparr>P"
proof -
  note `eqvt Rel` `x \<sharp> \<Psi>`
  moreover have "x \<sharp> \<lparr>\<nu>x\<rparr>(M\<lparr>\<lambda>*xvec N\<rparr>.P)" by(simp add: abs_fresh)
  moreover from `x \<sharp> M` `x \<sharp> N` have "x \<sharp> M\<lparr>\<lambda>*xvec N\<rparr>.\<lparr>\<nu>x\<rparr>P"
    by(auto simp add: inputChainFresh abs_fresh)
  ultimately show ?thesis
  proof(induct rule: simIFresh[of _ _ _ _ _ "()"])
    case(cSim \<alpha> P')
    from `\<Psi> \<rhd> M\<lparr>\<lambda>*xvec N\<rparr>.\<lparr>\<nu>x\<rparr>P \<longmapsto>\<alpha> \<prec> P'` `x \<sharp> \<alpha>` show ?case
    proof(induct rule: inputCases)
      case(cInput K Tvec)
      from `x \<sharp> K\<lparr>N[xvec::=Tvec]\<rparr>` have "x \<sharp> K" and "x \<sharp> N[xvec::=Tvec]" by simp+
      from `\<Psi> \<turnstile> M \<leftrightarrow> K` `distinct xvec` `set xvec \<subseteq> supp N` `length xvec = length Tvec`
      have "\<Psi> \<rhd> M\<lparr>\<lambda>*xvec N\<rparr>.P \<longmapsto>K\<lparr>(N[xvec::=Tvec])\<rparr> \<prec> P[xvec::=Tvec]"
        by(rule Input)
      hence "\<Psi> \<rhd> \<lparr>\<nu>x\<rparr>(M\<lparr>\<lambda>*xvec N\<rparr>.P) \<longmapsto>K\<lparr>(N[xvec::=Tvec])\<rparr> \<prec> \<lparr>\<nu>x\<rparr>(P[xvec::=Tvec])" using `x \<sharp> \<Psi>` `x \<sharp> K` `x \<sharp> N[xvec::=Tvec]`
        by(rule_tac Scope) auto
      moreover from `length xvec = length Tvec` `distinct xvec` `set xvec \<subseteq> supp N` `x \<sharp> N[xvec::=Tvec]` have "x \<sharp> Tvec"
        by(rule substTerm.subst3)
      with `x \<sharp> xvec` have "(\<Psi>, \<lparr>\<nu>x\<rparr>(P[xvec::=Tvec]), (\<lparr>\<nu>x\<rparr>P)[xvec::=Tvec]) \<in> Rel"
        by(force intro: C1)
      ultimately show ?case by blast
    qed
  qed
qed
 
lemma inputPushResRight:
  fixes \<Psi>   :: 'b
  and   x    :: name
  and   M    :: 'a
  and   xvec :: "name list"
  and   N    :: 'a
  and   P    :: "('a, 'b, 'c) psi"

  assumes "eqvt Rel"
  and     "x \<sharp> \<Psi>"
  and     "x \<sharp> M"
  and     "x \<sharp> xvec"
  and     "x \<sharp> N"
  and     C1: "\<And>Q. (\<Psi>, Q, Q) \<in> Rel"

  shows "\<Psi> \<rhd> M\<lparr>\<lambda>*xvec N\<rparr>.\<lparr>\<nu>x\<rparr>P \<leadsto>[Rel] \<lparr>\<nu>x\<rparr>(M\<lparr>\<lambda>*xvec N\<rparr>.P)"
proof -
  note `eqvt Rel` `x \<sharp> \<Psi>`
  moreover from `x \<sharp> M` `x \<sharp> N` have "x \<sharp> M\<lparr>\<lambda>*xvec N\<rparr>.\<lparr>\<nu>x\<rparr>P"
    by(auto simp add: inputChainFresh abs_fresh)
  moreover have "x \<sharp> \<lparr>\<nu>x\<rparr>(M\<lparr>\<lambda>*xvec N\<rparr>.P)" by(simp add: abs_fresh)
  ultimately show ?thesis
  proof(induct rule: simIFresh[of _ _ _ _ _ "()"])
    case(cSim \<alpha> P')
    note `\<Psi> \<rhd> \<lparr>\<nu>x\<rparr>(M\<lparr>\<lambda>*xvec N\<rparr>.P) \<longmapsto>\<alpha> \<prec> P'` `x \<sharp> \<Psi>` `x \<sharp> \<alpha>` `x \<sharp> P'` `bn \<alpha> \<sharp>* \<Psi>` 
    moreover from `bn \<alpha> \<sharp>* (\<lparr>\<nu>x\<rparr>(M\<lparr>\<lambda>*xvec N\<rparr>.P))` `x \<sharp> \<alpha>` have  "bn \<alpha> \<sharp>* (M\<lparr>\<lambda>*xvec N\<rparr>.P)"
      by simp
    ultimately show ?case using `bn \<alpha> \<sharp>* subject \<alpha>`
    proof(induct rule: resCases)
      case(cRes P')
      from `\<Psi> \<rhd> M\<lparr>\<lambda>*xvec N\<rparr>.P \<longmapsto>\<alpha> \<prec> P'` `x \<sharp> \<alpha>` show ?case
      proof(induct rule: inputCases)
        case(cInput K Tvec)
        from `x \<sharp> K\<lparr>N[xvec::=Tvec]\<rparr>` have "x \<sharp> K" and "x \<sharp> N[xvec::=Tvec]" by simp+
        from `\<Psi> \<turnstile> M \<leftrightarrow> K` `distinct xvec` `set xvec \<subseteq> supp N` `length xvec = length Tvec`
        have "\<Psi> \<rhd> M\<lparr>\<lambda>*xvec N\<rparr>.(\<lparr>\<nu>x\<rparr>P) \<longmapsto>K\<lparr>(N[xvec::=Tvec])\<rparr> \<prec> (\<lparr>\<nu>x\<rparr>P)[xvec::=Tvec]"
          by(rule Input)
        moreover from `length xvec = length Tvec` `distinct xvec` `set xvec \<subseteq> supp N` `x \<sharp> N[xvec::=Tvec]` have "x \<sharp> Tvec"
          by(rule substTerm.subst3)
        with `x \<sharp> xvec` have "(\<Psi>, (\<lparr>\<nu>x\<rparr>P)[xvec::=Tvec], \<lparr>\<nu>x\<rparr>(P[xvec::=Tvec])) \<in> Rel"
          by(force intro: C1)
        ultimately show ?case by blast
      qed
    next
      case cOpen
      then have False by auto
      thus ?case by simp
    qed
  qed
qed

lemma outputPushResLeft:
  fixes \<Psi>   :: 'b
  and   x    :: name
  and   M    :: 'a
  and   N    :: 'a
  and   P    :: "('a, 'b, 'c) psi"

  assumes "eqvt Rel"
  and     "x \<sharp> \<Psi>"
  and     "x \<sharp> M"
  and     "x \<sharp> N"
  and     C1: "\<And>Q. (\<Psi>, Q, Q) \<in> Rel"

  shows "\<Psi> \<rhd> \<lparr>\<nu>x\<rparr>(M\<langle>N\<rangle>.P) \<leadsto>[Rel] M\<langle>N\<rangle>.\<lparr>\<nu>x\<rparr>P"
proof -
  note `eqvt Rel` `x \<sharp> \<Psi>`
  moreover have "x \<sharp> \<lparr>\<nu>x\<rparr>(M\<langle>N\<rangle>.P)" by(simp add: abs_fresh)
  moreover from `x \<sharp> M` `x \<sharp> N` have "x \<sharp> M\<langle>N\<rangle>.\<lparr>\<nu>x\<rparr>P"
    by(auto simp add: abs_fresh)
  ultimately show ?thesis
  proof(induct rule: simIFresh[of _ _ _ _ _ "()"])
    case(cSim \<alpha> P')
    from `\<Psi> \<rhd> M\<langle>N\<rangle>.\<lparr>\<nu>x\<rparr>P \<longmapsto>\<alpha> \<prec> P'` `x \<sharp> \<alpha>`
    show ?case
    proof(induct rule: outputCases)
      case(cOutput K)
      from `\<Psi> \<turnstile> M \<leftrightarrow> K` have "\<Psi> \<rhd> M\<langle>N\<rangle>.P \<longmapsto>K\<langle>N\<rangle> \<prec> P"
        by(rule Output)
      hence "\<Psi> \<rhd> \<lparr>\<nu>x\<rparr>(M\<langle>N\<rangle>.P) \<longmapsto>K\<langle>N\<rangle> \<prec> \<lparr>\<nu>x\<rparr>P" using `x \<sharp> \<Psi>` `x \<sharp> K\<langle>N\<rangle>`
        by(rule Scope)
      moreover have "(\<Psi>, \<lparr>\<nu>x\<rparr>P, \<lparr>\<nu>x\<rparr>P) \<in> Rel" by(rule C1)
      ultimately show ?case by blast
    qed
  qed
qed
 
lemma outputPushResRight:
  fixes \<Psi>   :: 'b
  and   x    :: name
  and   M    :: 'a
  and   N    :: 'a
  and   P    :: "('a, 'b, 'c) psi"

  assumes "eqvt Rel"
  and     "x \<sharp> \<Psi>"
  and     "x \<sharp> M"
  and     "x \<sharp> N"
  and     C1: "\<And>Q. (\<Psi>, Q, Q) \<in> Rel"

  shows "\<Psi> \<rhd> M\<langle>N\<rangle>.\<lparr>\<nu>x\<rparr>P \<leadsto>[Rel] \<lparr>\<nu>x\<rparr>(M\<langle>N\<rangle>.P)"
proof -
  note `eqvt Rel` `x \<sharp> \<Psi>`
  moreover from `x \<sharp> M` `x \<sharp> N` have "x \<sharp> M\<langle>N\<rangle>.\<lparr>\<nu>x\<rparr>P"
    by(auto simp add: abs_fresh)
  moreover have "x \<sharp> \<lparr>\<nu>x\<rparr>(M\<langle>N\<rangle>.P)" by(simp add: abs_fresh)
  ultimately show ?thesis
  proof(induct rule: simIFresh[of _ _ _ _ _ "(M, N)"])
    case(cSim \<alpha> P')
    note `\<Psi> \<rhd> \<lparr>\<nu>x\<rparr>(M\<langle>N\<rangle>.P) \<longmapsto>\<alpha> \<prec> P'` `x \<sharp> \<Psi>` `x \<sharp> \<alpha>` `x \<sharp> P'` `bn \<alpha> \<sharp>* \<Psi>`
    moreover from `bn \<alpha> \<sharp>* (\<lparr>\<nu>x\<rparr>(M\<langle>N\<rangle>.P))` `x \<sharp> \<alpha>` have "bn \<alpha> \<sharp>* (M\<langle>N\<rangle>.P)" by simp
    ultimately show ?case using `bn \<alpha> \<sharp>* subject \<alpha>` `bn \<alpha> \<sharp>* (M, N)` `x \<sharp> \<alpha>`
    proof(induct rule: resCases)
      case(cOpen K xvec1 xvec2 y N' P')
      from `bn(K\<lparr>\<nu>*(xvec1@y#xvec2)\<rparr>\<langle>N'\<rangle>) \<sharp>* (M, N)` have "y \<sharp> N" by simp+
      from `\<Psi> \<rhd> M\<langle>N\<rangle>.P \<longmapsto>K\<lparr>\<nu>*(xvec1@xvec2)\<rparr>\<langle>([(x, y)] \<bullet> N')\<rangle> \<prec> ([(x, y)] \<bullet> P')`
      have "N = ([(x, y)] \<bullet> N')"
        apply -
        by(ind_cases "\<Psi> \<rhd> M\<langle>N\<rangle>.P \<longmapsto>K\<lparr>\<nu>*(xvec1@xvec2)\<rparr>\<langle>([(x, y)] \<bullet> N')\<rangle> \<prec> ([(x, y)] \<bullet> P')")
          (auto simp add: residualInject psi.inject)
      with `x \<sharp> N` `y \<sharp> N` `x \<noteq> y` have "N = N'"
        by(subst pt_bij[OF pt_name_inst, OF at_name_inst, symmetric, where pi="[(x, y)]"])
          (simp add: fresh_left calc_atm)
      with `y \<in> supp N'` `y \<sharp> N` have False by(simp add: fresh_def)
      thus ?case by simp
    next
      case(cRes P')
      from `\<Psi> \<rhd> M\<langle>N\<rangle>.P \<longmapsto>\<alpha> \<prec> P'` show ?case
      proof(induct rule: outputCases)
        case(cOutput K)
        from `\<Psi> \<turnstile> M \<leftrightarrow> K` have "\<Psi> \<rhd> M\<langle>N\<rangle>.(\<lparr>\<nu>x\<rparr>P) \<longmapsto>K\<langle>N\<rangle> \<prec> \<lparr>\<nu>x\<rparr>P"
          by(rule Output)
        moreover have "(\<Psi>, \<lparr>\<nu>x\<rparr>P, \<lparr>\<nu>x\<rparr>P) \<in> Rel" by(rule C1)
        ultimately show ?case by force
      qed
    qed
  qed
qed

lemma casePushResLeft:
  fixes \<Psi>  :: 'b
  and   x  :: name
  and   Cs :: "('c \<times> ('a, 'b, 'c) psi) list"

  assumes "eqvt Rel"
  and     "x \<sharp> \<Psi>"
  and     "x \<sharp> map fst Cs"
  and     C1: "\<And>Q. (\<Psi>, Q, Q) \<in> Rel"

  shows "\<Psi> \<rhd> \<lparr>\<nu>x\<rparr>(Cases Cs) \<leadsto>[Rel] Cases (map (\<lambda>(\<phi>, P). (\<phi>, \<lparr>\<nu>x\<rparr>P)) Cs)"
proof -
  note `eqvt Rel` `x \<sharp> \<Psi>`
  moreover have "x \<sharp> \<lparr>\<nu>x\<rparr>(Cases Cs)" by(simp add: abs_fresh)
  moreover from `x \<sharp> map fst Cs` have "x \<sharp> Cases (map (\<lambda>(\<phi>, P). (\<phi>, \<lparr>\<nu>x\<rparr>P)) Cs)"
    by(induct Cs) (auto simp add: abs_fresh)
  ultimately show ?thesis
  proof(induct rule: simIFresh[of _ _ _ _ _ Cs])
    case(cSim \<alpha> P'')
    from `\<Psi> \<rhd> Cases (map (\<lambda>(\<phi>, P). (\<phi>, \<lparr>\<nu>x\<rparr>P)) Cs) \<longmapsto>\<alpha> \<prec> P''` 
    show ?case
    proof(induct rule: caseCases)
      case(cCase \<phi> P')
      from `(\<phi>, P') mem (map (\<lambda>(\<phi>, P). (\<phi>, \<lparr>\<nu>x\<rparr>P)) Cs)` 
      obtain P where "(\<phi>, P) mem Cs" and "P' = \<lparr>\<nu>x\<rparr>P" 
        by(induct Cs) auto
      from `guarded P'` `P' = \<lparr>\<nu>x\<rparr>P` have "guarded P" by simp
      from `\<Psi> \<rhd> P' \<longmapsto>\<alpha> \<prec> P''` `P' = \<lparr>\<nu>x\<rparr>P` have "\<Psi> \<rhd> \<lparr>\<nu>x\<rparr>P \<longmapsto>\<alpha> \<prec> P''"
        by simp
      moreover note `x \<sharp> \<Psi>` `x \<sharp> \<alpha>` `x \<sharp> P''` `bn \<alpha> \<sharp>* \<Psi>` 
      moreover from `bn \<alpha> \<sharp>* Cs` `(\<phi>, P) mem Cs`
      have "bn \<alpha> \<sharp>* P" by(auto dest: memFreshChain)
      ultimately show ?case using `bn \<alpha> \<sharp>* subject \<alpha>` `x \<sharp> \<alpha>` `bn \<alpha> \<sharp>* Cs`
      proof(induct rule: resCases)
        case(cOpen M xvec1 xvec2 y N P')
        from `x \<sharp> M\<lparr>\<nu>*(xvec1@y#xvec2)\<rparr>\<langle>N\<rangle>` have "x \<sharp> xvec1" and "x \<sharp> xvec2" and "x \<sharp> M" by simp+
        from `bn(M\<lparr>\<nu>*(xvec1@y#xvec2)\<rparr>\<langle>N\<rangle>) \<sharp>* Cs` have "y \<sharp> Cs" by simp
        from `\<Psi> \<rhd> P \<longmapsto>M\<lparr>\<nu>*(xvec1@xvec2)\<rparr>\<langle>([(x, y)] \<bullet> N)\<rangle> \<prec> ([(x, y)] \<bullet> P')` `(\<phi>, P) mem Cs` `\<Psi> \<turnstile> \<phi>` `guarded P`
        have "\<Psi> \<rhd> Cases Cs \<longmapsto>M\<lparr>\<nu>*(xvec1@xvec2)\<rparr>\<langle>([(x, y)] \<bullet> N)\<rangle> \<prec> ([(x, y)] \<bullet> P')" by(rule Case)
        hence "([(x, y)] \<bullet> \<Psi>) \<rhd> ([(x, y)] \<bullet> (Cases Cs))  \<longmapsto>([(x, y)] \<bullet> (M\<lparr>\<nu>*(xvec1@xvec2)\<rparr>\<langle>([(x, y)] \<bullet> N)\<rangle> \<prec> ([(x, y)] \<bullet> P')))"
          by(rule semantics.eqvt)
        with `x \<sharp> \<Psi>` `x \<sharp> M` `y \<sharp> xvec1` `y \<sharp> xvec2` `y \<sharp> \<Psi>` `y \<sharp> M` `x \<sharp> xvec1` `x \<sharp> xvec2`
        have "\<Psi> \<rhd> ([(x, y)] \<bullet> (Cases Cs))  \<longmapsto>M\<lparr>\<nu>*(xvec1@xvec2)\<rparr>\<langle>N\<rangle> \<prec> P'" by(simp add: eqvts)
        hence "\<Psi> \<rhd> \<lparr>\<nu>y\<rparr>([(x, y)] \<bullet> (Cases Cs))  \<longmapsto>M\<lparr>\<nu>*(xvec1@y#xvec2)\<rparr>\<langle>N\<rangle> \<prec> P'" using `y \<in> supp N` `y \<sharp> \<Psi>` `y \<sharp> M` `y \<sharp> xvec1` `y \<sharp> xvec2`
          by(rule Open)
        hence "\<Psi> \<rhd> \<lparr>\<nu>x\<rparr>(Cases Cs)  \<longmapsto>M\<lparr>\<nu>*(xvec1@y#xvec2)\<rparr>\<langle>N\<rangle> \<prec> P'" using `y \<sharp> Cs`
          by(simp add: alphaRes)
        moreover have "(\<Psi>, P', P') \<in> Rel" by(rule C1)
        ultimately show ?case by blast
      next
        case(cRes P')
        from `\<Psi> \<rhd> P \<longmapsto>\<alpha> \<prec> P'` `(\<phi>, P) mem Cs` `\<Psi> \<turnstile> \<phi>` `guarded P`
        have "\<Psi> \<rhd> Cases Cs \<longmapsto>\<alpha> \<prec> P'" by(rule Case)
        hence "\<Psi> \<rhd> \<lparr>\<nu>x\<rparr>(Cases Cs) \<longmapsto>\<alpha> \<prec> \<lparr>\<nu>x\<rparr>P'" using `x \<sharp> \<Psi>` `x \<sharp> \<alpha>`
          by(rule Scope)
        moreover have "(\<Psi>, \<lparr>\<nu>x\<rparr>P', \<lparr>\<nu>x\<rparr>P') \<in> Rel" by(rule C1)
        ultimately show ?case by blast
      qed
    qed
  qed
qed
 
lemma casePushResRight:
  fixes \<Psi>  :: 'b
  and   x  :: name
  and   Cs :: "('c \<times> ('a, 'b, 'c) psi) list"

  assumes "eqvt Rel"
  and     "x \<sharp> \<Psi>"
  and     "x \<sharp> map fst Cs"
  and     C1: "\<And>Q. (\<Psi>, Q, Q) \<in> Rel"

  shows "\<Psi> \<rhd> Cases (map (\<lambda>(\<phi>, P). (\<phi>, \<lparr>\<nu>x\<rparr>P)) Cs) \<leadsto>[Rel] \<lparr>\<nu>x\<rparr>(Cases Cs)"
proof -
  note `eqvt Rel` `x \<sharp> \<Psi>`
  moreover from `x \<sharp> map fst Cs` have "x \<sharp> Cases (map (\<lambda>(\<phi>, P). (\<phi>, \<lparr>\<nu>x\<rparr>P)) Cs)"
    by(induct Cs) (auto simp add: abs_fresh)
  moreover have "x \<sharp> \<lparr>\<nu>x\<rparr>(Cases Cs)" by(simp add: abs_fresh)
  ultimately show ?thesis
  proof(induct rule: simIFresh[of _ _ _ _ _ Cs])
    case(cSim \<alpha> P'')
    note `\<Psi> \<rhd> \<lparr>\<nu>x\<rparr>(Cases Cs) \<longmapsto>\<alpha> \<prec> P''` `x \<sharp> \<Psi>` `x \<sharp> \<alpha>` `x \<sharp> P''` `bn \<alpha> \<sharp>* \<Psi>`
    moreover from `bn \<alpha> \<sharp>* \<lparr>\<nu>x\<rparr>(Cases Cs)` `x \<sharp> \<alpha>` have "bn \<alpha> \<sharp>* (Cases Cs)" by simp
    ultimately show ?case using `bn \<alpha> \<sharp>* subject \<alpha>` `x \<sharp> \<alpha>` `bn \<alpha> \<sharp>* Cs`
    proof(induct rule: resCases)
      case(cOpen M xvec1 xvec2 y N P')
      from `x \<sharp> M\<lparr>\<nu>*(xvec1@y#xvec2)\<rparr>\<langle>N\<rangle>` have "x \<sharp> xvec1" and "x \<sharp> xvec2" and "x \<sharp> M" by simp+
      from `bn(M\<lparr>\<nu>*(xvec1@y#xvec2)\<rparr>\<langle>N\<rangle>) \<sharp>* Cs` have "y \<sharp> Cs" by simp
      from `\<Psi> \<rhd> Cases Cs \<longmapsto>M\<lparr>\<nu>*(xvec1@xvec2)\<rparr>\<langle>([(x, y)] \<bullet> N)\<rangle> \<prec> ([(x, y)] \<bullet> P')`
      show ?case
      proof(induct rule: caseCases)
        case(cCase \<phi> P)
        from `\<Psi> \<rhd> P \<longmapsto>M\<lparr>\<nu>*(xvec1@xvec2)\<rparr>\<langle>([(x, y)] \<bullet> N)\<rangle> \<prec> ([(x, y)] \<bullet> P')`
        have "([(x, y)] \<bullet> \<Psi>) \<rhd> ([(x, y)] \<bullet> P)  \<longmapsto>([(x, y)] \<bullet> (M\<lparr>\<nu>*(xvec1@xvec2)\<rparr>\<langle>([(x, y)] \<bullet> N)\<rangle> \<prec> ([(x, y)] \<bullet> P')))"
          by(rule semantics.eqvt)
        with `x \<sharp> \<Psi>` `x \<sharp> M` `y \<sharp> xvec1` `y \<sharp> xvec2` `y \<sharp> \<Psi>` `y \<sharp> M` `x \<sharp> xvec1` `x \<sharp> xvec2`
        have "\<Psi> \<rhd> ([(x, y)] \<bullet> P)  \<longmapsto>M\<lparr>\<nu>*(xvec1@xvec2)\<rparr>\<langle>N\<rangle> \<prec> P'" by(simp add: eqvts)
        hence "\<Psi> \<rhd> \<lparr>\<nu>y\<rparr>([(x, y)] \<bullet> P)  \<longmapsto>M\<lparr>\<nu>*(xvec1@y#xvec2)\<rparr>\<langle>N\<rangle> \<prec> P'" using `y \<in> supp N` `y \<sharp> \<Psi>` `y \<sharp> M` `y \<sharp> xvec1` `y \<sharp> xvec2`
          by(rule Open)
        hence "\<Psi> \<rhd> \<lparr>\<nu>x\<rparr>P  \<longmapsto>M\<lparr>\<nu>*(xvec1@y#xvec2)\<rparr>\<langle>N\<rangle> \<prec> P'" using `y \<sharp> Cs` `(\<phi>, P) mem Cs`
          by(subst alphaRes, auto dest: memFresh)
        moreover from `(\<phi>, P) mem Cs` have "(\<phi>, \<lparr>\<nu>x\<rparr>P) mem (map (\<lambda>(\<phi>, P). (\<phi>, \<lparr>\<nu>x\<rparr>P)) Cs)"
          by(induct Cs) auto
        moreover note `\<Psi> \<turnstile> \<phi>`
        moreover from `guarded P` have "guarded(\<lparr>\<nu>x\<rparr>P)" by simp
        ultimately have "\<Psi> \<rhd> (Cases (map (\<lambda>(\<phi>, P). (\<phi>, \<lparr>\<nu>x\<rparr>P)) Cs)) \<longmapsto>M\<lparr>\<nu>*(xvec1@y#xvec2)\<rparr>\<langle>N\<rangle> \<prec> P'"
          by(rule Case)
        moreover have "(\<Psi>, P', P') \<in> Rel" by(rule C1)
        ultimately show ?case by blast
      qed
    next
      case(cRes P')
      from `\<Psi> \<rhd> Cases Cs \<longmapsto>\<alpha> \<prec> P'`
      show ?case
      proof(induct rule: caseCases)
        case(cCase \<phi> P)
        from `\<Psi> \<rhd> P \<longmapsto>\<alpha> \<prec> P'` `x \<sharp> \<Psi>` `x \<sharp> \<alpha>`
        have "\<Psi> \<rhd> \<lparr>\<nu>x\<rparr>P \<longmapsto>\<alpha> \<prec> \<lparr>\<nu>x\<rparr>P'" by(rule Scope)
        moreover from `(\<phi>, P) mem Cs` have "(\<phi>, \<lparr>\<nu>x\<rparr>P) mem (map (\<lambda>(\<phi>, P). (\<phi>, \<lparr>\<nu>x\<rparr>P)) Cs)"
          by(induct Cs) auto
        moreover note `\<Psi> \<turnstile> \<phi>`
        moreover from `guarded P` have "guarded(\<lparr>\<nu>x\<rparr>P)" by simp
        ultimately have "\<Psi> \<rhd> (Cases (map (\<lambda>(\<phi>, P). (\<phi>, \<lparr>\<nu>x\<rparr>P)) Cs)) \<longmapsto>\<alpha> \<prec> \<lparr>\<nu>x\<rparr>P'"
          by(rule Case)
        moreover have "(\<Psi>, \<lparr>\<nu>x\<rparr>P', \<lparr>\<nu>x\<rparr>P') \<in> Rel" by(rule C1)
        ultimately show ?case by blast
      qed
    qed
  qed
qed

lemma resInputCases[consumes 5, case_names cRes]:
  fixes \<Psi>    :: 'b
  and   x    :: name
  and   P    :: "('a, 'b, 'c) psi"
  and   M    :: 'a
  and   N    :: 'a
  and   P'   :: "('a, 'b, 'c) psi"
  and   C    :: "'d::fs_name"

  assumes Trans: "\<Psi> \<rhd> \<lparr>\<nu>x\<rparr>P \<longmapsto>M\<lparr>N\<rparr> \<prec> P'"
  and     "x \<sharp> \<Psi>"
  and     "x \<sharp> M"
  and     "x \<sharp> N"
  and     "x \<sharp> P'"
  and     rScope:  "\<And>P'. \<lbrakk>\<Psi> \<rhd> P \<longmapsto>M\<lparr>N\<rparr> \<prec> P'\<rbrakk> \<Longrightarrow> Prop (\<lparr>\<nu>x\<rparr>P')"

  shows "Prop P'"
proof -
  note Trans `x \<sharp> \<Psi>`
  moreover from `x \<sharp> M` `x \<sharp> N` have "x \<sharp> (M\<lparr>N\<rparr>)" by simp
  moreover note `x \<sharp> P'`
  moreover have "bn(M\<lparr>N\<rparr>) \<sharp>* \<Psi>" and "bn(M\<lparr>N\<rparr>) \<sharp>* P" and "bn(M\<lparr>N\<rparr>) \<sharp>* subject(M\<lparr>N\<rparr>)" and "bn(M\<lparr>N\<rparr>) = []" by simp+
  ultimately show ?thesis
    by(induct rule: resCases) (auto intro: rScope)
qed

lemma scopeExtLeft:
  fixes x   :: name
  and   P   :: "('a, 'b, 'c) psi"
  and   \<Psi>   :: 'b
  and   Q   :: "('a, 'b, 'c) psi"
  and   Rel :: "('b \<times> ('a, 'b, 'c) psi \<times> ('a, 'b, 'c) psi) set"

  assumes "x \<sharp> P"
  and     "x \<sharp> \<Psi>"
  and     "eqvt Rel"
  and     C1: "\<And>\<Psi>' R. (\<Psi>', R, R) \<in> Rel"
  and     C2: "\<And>y \<Psi>' R S zvec. \<lbrakk>y \<sharp> \<Psi>'; y \<sharp> R; zvec \<sharp>* \<Psi>'\<rbrakk> \<Longrightarrow> (\<Psi>', \<lparr>\<nu>y\<rparr>(\<lparr>\<nu>*zvec\<rparr>(R \<parallel> S)), \<lparr>\<nu>*zvec\<rparr>(R \<parallel> \<lparr>\<nu>y\<rparr>S)) \<in> Rel"
  and     C3: "\<And>\<Psi>' zvec R y. \<lbrakk>y \<sharp> \<Psi>'; zvec \<sharp>* \<Psi>'\<rbrakk> \<Longrightarrow> (\<Psi>', \<lparr>\<nu>y\<rparr>(\<lparr>\<nu>*zvec\<rparr>R), \<lparr>\<nu>*zvec\<rparr>(\<lparr>\<nu>y\<rparr>R)) \<in> Rel"

  shows "\<Psi> \<rhd> \<lparr>\<nu>x\<rparr>(P \<parallel> Q) \<leadsto>[Rel] P \<parallel> \<lparr>\<nu>x\<rparr>Q"
proof -
  note `eqvt Rel` `x \<sharp> \<Psi>`
  moreover have "x \<sharp> \<lparr>\<nu>x\<rparr>(P \<parallel> Q)" by(simp add: abs_fresh)
  moreover from `x \<sharp> P` have "x \<sharp> P \<parallel> \<lparr>\<nu>x\<rparr>Q" by(simp add: abs_fresh)
  ultimately show ?thesis
  proof(induct rule: simIFresh[of _ _ _ _ _ x])
    case(cSim \<alpha> PQ)
    from `x \<sharp> \<alpha>` `bn \<alpha> \<sharp>* (P \<parallel> \<lparr>\<nu>x\<rparr>Q)` have "bn \<alpha> \<sharp>* Q" by simp
    note `\<Psi> \<rhd> P \<parallel> \<lparr>\<nu>x\<rparr>Q \<longmapsto>\<alpha> \<prec> PQ` `bn \<alpha> \<sharp>* \<Psi>`
    moreover from `bn \<alpha> \<sharp>* (P \<parallel> \<lparr>\<nu>x\<rparr>Q)` have "bn \<alpha> \<sharp>* P" and "bn \<alpha> \<sharp>* \<lparr>\<nu>x\<rparr>Q" by simp+
    ultimately show ?case using `bn \<alpha> \<sharp>* subject \<alpha>` `x \<sharp> PQ`
    proof(induct rule: parCases[where C=x])
      case(cPar1 P' A\<^sub>Q \<Psi>\<^sub>Q)
      from `x \<sharp> P' \<parallel> \<lparr>\<nu>x\<rparr>Q` have "x \<sharp> P'" by simp
      have PTrans: "\<Psi> \<otimes> \<Psi>\<^sub>Q \<rhd> P \<longmapsto>\<alpha> \<prec> P'" by fact
      from `extractFrame(\<lparr>\<nu>x\<rparr>Q) = \<langle>A\<^sub>Q, \<Psi>\<^sub>Q\<rangle>` have FrxQ: "\<lparr>\<nu>x\<rparr>(extractFrame Q) = \<langle>A\<^sub>Q, \<Psi>\<^sub>Q\<rangle>" by simp
      then obtain y A\<^sub>Q' where A: "A\<^sub>Q = y#A\<^sub>Q'" by(case_tac A\<^sub>Q) auto
      with `A\<^sub>Q \<sharp>* \<Psi>` `A\<^sub>Q \<sharp>* P` `A\<^sub>Q \<sharp>* \<alpha>`
      have "A\<^sub>Q' \<sharp>* \<Psi>" and "A\<^sub>Q' \<sharp>* P" and "A\<^sub>Q' \<sharp>* \<alpha>"
        and "y \<sharp> \<Psi>" and "y \<sharp> P" and "y \<sharp> \<alpha>"
        by simp+
      from PTrans `y \<sharp> P` `y \<sharp> \<alpha>` `bn \<alpha> \<sharp>* subject \<alpha>` `distinct(bn \<alpha>)` have "y \<sharp> P'"
        by(auto intro: freeFreshDerivative)
      note PTrans
      moreover from A `A\<^sub>Q \<sharp>* x` FrxQ have "extractFrame([(y, x)] \<bullet> Q) = \<langle>A\<^sub>Q', \<Psi>\<^sub>Q\<rangle>" 
        by(simp add: frame.inject alpha' fresh_list_cons eqvts) 
      moreover from `bn \<alpha> \<sharp>* Q` have "([(y, x)] \<bullet> (bn \<alpha>)) \<sharp>* ([(y, x)] \<bullet> Q)"
        by(simp add: pt_fresh_star_bij[OF pt_name_inst, OF at_name_inst])
      with `x \<sharp> \<alpha>` `A\<^sub>Q \<sharp>* \<alpha>` A have "bn \<alpha> \<sharp>* ([(y, x)] \<bullet> Q)" by simp
      ultimately have "\<Psi> \<rhd> P \<parallel> ([(y, x)] \<bullet> Q) \<longmapsto>\<alpha> \<prec> (P' \<parallel> ([(y, x)] \<bullet> Q))"
        using `A\<^sub>Q' \<sharp>* \<Psi>` `A\<^sub>Q' \<sharp>* P` `A\<^sub>Q' \<sharp>* \<alpha>`
        by(rule Par1)
      hence "\<Psi> \<rhd> \<lparr>\<nu>y\<rparr>(P \<parallel> ([(y, x)] \<bullet> Q)) \<longmapsto>\<alpha> \<prec> \<lparr>\<nu>y\<rparr>(P' \<parallel> ([(y, x)] \<bullet> Q))"
        using `y \<sharp> \<Psi>` `y \<sharp> \<alpha>`
        by(rule Scope)
      hence "([(y, x)] \<bullet> \<Psi>) \<rhd> ([(y, x)] \<bullet> (\<lparr>\<nu>y\<rparr>(P \<parallel> ([(y, x)] \<bullet> Q)))) \<longmapsto>([(y, x)] \<bullet> (\<alpha> \<prec> \<lparr>\<nu>y\<rparr>(P' \<parallel> ([(y, x)] \<bullet> Q))))"
        by(rule semantics.eqvt)
      with `x \<sharp> \<Psi>` `y \<sharp> \<Psi>` `x \<sharp> P` `y \<sharp> P` `x \<sharp> \<alpha>` `y \<sharp> \<alpha>` `x \<sharp> P'` `y \<sharp> P'`
      have "\<Psi> \<rhd> \<lparr>\<nu>x\<rparr>(P \<parallel> Q) \<longmapsto>\<alpha> \<prec> \<lparr>\<nu>x\<rparr>(P' \<parallel> Q)"
        by(simp add: eqvts calc_atm)
      moreover from `x \<sharp> \<Psi>` `x \<sharp> P'` have "(\<Psi>, \<lparr>\<nu>x\<rparr>(\<lparr>\<nu>*[]\<rparr>(P' \<parallel> Q)), \<lparr>\<nu>*[]\<rparr>(P' \<parallel> \<lparr>\<nu>x\<rparr>Q)) \<in> Rel"
        by(rule_tac C2) auto
      ultimately show ?case
        by force
    next
      case(cPar2 xQ' A\<^sub>P \<Psi>\<^sub>P)
      from `A\<^sub>P \<sharp>* \<lparr>\<nu>x\<rparr>Q` `A\<^sub>P \<sharp>* x` have "A\<^sub>P \<sharp>* Q" by simp
      note `\<Psi> \<otimes> \<Psi>\<^sub>P \<rhd> \<lparr>\<nu>x\<rparr>Q \<longmapsto>\<alpha> \<prec> xQ'`
      moreover have FrP: "extractFrame P = \<langle>A\<^sub>P, \<Psi>\<^sub>P\<rangle>" by fact
      with `x \<sharp> P` `A\<^sub>P \<sharp>* x` have "x \<sharp> \<Psi>\<^sub>P" and "x \<sharp> A\<^sub>P"
        by(force dest: extractFrameFresh)+
      with `x \<sharp> \<Psi>` have "x \<sharp> \<Psi> \<otimes> \<Psi>\<^sub>P" by force
      moreover note `x \<sharp> \<alpha>`
      moreover from `x \<sharp> P \<parallel> xQ'` have "x \<sharp> xQ'" by simp
      moreover from FrP `bn \<alpha> \<sharp>* P` `A\<^sub>P \<sharp>* \<alpha>` have "bn \<alpha> \<sharp>* \<Psi>\<^sub>P"
        by(drule_tac extractFrameFreshChain) auto
      with `bn \<alpha> \<sharp>* \<Psi>` have "bn \<alpha> \<sharp>* (\<Psi> \<otimes> \<Psi>\<^sub>P)" by force
      ultimately show ?case using `bn \<alpha> \<sharp>* Q` `bn \<alpha> \<sharp>* subject \<alpha>` `x \<sharp> \<alpha>` `bn \<alpha> \<sharp>* P` `A\<^sub>P \<sharp>* \<alpha>` `bn \<alpha> \<sharp>* \<Psi>`
      proof(induct rule: resCases')
        case(cOpen M xvec1 xvec2 y N Q')
        from `x \<sharp> M\<lparr>\<nu>*(xvec1@y#xvec2)\<rparr>\<langle>N\<rangle>` have "x \<sharp> xvec1" and "x \<noteq> y" and "x \<sharp> xvec2" by simp+
        from `bn(M\<lparr>\<nu>*(xvec1@y#xvec2)\<rparr>\<langle>N\<rangle>) \<sharp>* \<Psi>` have "y \<sharp> \<Psi>" by simp
        note `\<Psi> \<otimes> \<Psi>\<^sub>P \<rhd> ([(x, y)] \<bullet> Q) \<longmapsto>M\<lparr>\<nu>*(xvec1@xvec2)\<rparr>\<langle>N\<rangle> \<prec> Q'` FrP
        moreover from `bn(M\<lparr>\<nu>*(xvec1@y#xvec2)\<rparr>\<langle>N\<rangle>) \<sharp>* P` have "(xvec1@xvec2) \<sharp>* P" and "y \<sharp> P" by simp+
        moreover from `A\<^sub>P \<sharp>* (M\<lparr>\<nu>*(xvec1@y#xvec2)\<rparr>\<langle>N\<rangle>)` have "A\<^sub>P \<sharp>* (M\<lparr>\<nu>*(xvec1@xvec2)\<rparr>\<langle>N\<rangle>)" and "y \<sharp> A\<^sub>P" by simp+
        moreover from `A\<^sub>P \<sharp>* Q` `x \<sharp> A\<^sub>P` `y \<sharp> A\<^sub>P` have "A\<^sub>P \<sharp>* ([(x, y)] \<bullet> Q)" by simp
        ultimately have "\<Psi> \<rhd> P \<parallel> ([(x, y)] \<bullet> Q) \<longmapsto>M\<lparr>\<nu>*(xvec1@xvec2)\<rparr>\<langle>N\<rangle> \<prec> (P \<parallel> Q')" 
          using `A\<^sub>P \<sharp>* \<Psi>`
          by(rule_tac Par2) (assumption | simp)+
         hence "\<Psi> \<rhd> \<lparr>\<nu>y\<rparr>(P \<parallel> ([(x, y)] \<bullet> Q)) \<longmapsto>M\<lparr>\<nu>*(xvec1@y#xvec2)\<rparr>\<langle>N\<rangle> \<prec> (P \<parallel> Q')"
           using `y \<in> supp N` `y \<sharp> \<Psi>` `y \<sharp> M` `y \<sharp> xvec1` `y \<sharp> xvec2`
           by(rule Open)
         with `x \<sharp> P` `y \<sharp> P` `y \<sharp> Q` have "\<Psi> \<rhd> \<lparr>\<nu>x\<rparr>(P \<parallel> Q) \<longmapsto>M\<lparr>\<nu>*(xvec1@y#xvec2)\<rparr>\<langle>N\<rangle> \<prec> (P \<parallel> Q')"
           by(subst alphaRes[where y=y]) (simp add: fresh_left calc_atm eqvts)+
        moreover have "(\<Psi>, P \<parallel> Q', P \<parallel> Q') \<in> Rel" by(rule C1)
        ultimately show ?case by blast
      next
        case(cRes Q')
        from `\<Psi> \<otimes> \<Psi>\<^sub>P \<rhd> Q \<longmapsto>\<alpha> \<prec> Q'` FrP `bn \<alpha> \<sharp>* P`
        have "\<Psi> \<rhd> P \<parallel> Q \<longmapsto>\<alpha> \<prec> (P \<parallel> Q')" using `A\<^sub>P \<sharp>* \<Psi>` `A\<^sub>P \<sharp>* Q` `A\<^sub>P \<sharp>* \<alpha>`
          by(rule Par2)
        hence "\<Psi> \<rhd> \<lparr>\<nu>x\<rparr>(P \<parallel> Q) \<longmapsto>\<alpha> \<prec> \<lparr>\<nu>x\<rparr>(P \<parallel> Q')" using `x \<sharp> \<Psi>` `x \<sharp> \<alpha>`
          by(rule Scope)
        moreover from `x \<sharp> \<Psi>` `x \<sharp> P` have "(\<Psi>, \<lparr>\<nu>x\<rparr>(\<lparr>\<nu>*[]\<rparr>(P \<parallel> Q')), \<lparr>\<nu>*[]\<rparr>(P \<parallel> \<lparr>\<nu>x\<rparr>Q')) \<in> Rel"
          by(rule_tac C2) auto
        ultimately show ?case
          by force
      qed
    next
      case(cComm1 \<Psi>\<^sub>Q M N P' A\<^sub>P \<Psi>\<^sub>P K xvec xQ' A\<^sub>Q)
      have QTrans: "\<Psi> \<otimes> \<Psi>\<^sub>P \<rhd> \<lparr>\<nu>x\<rparr>Q \<longmapsto>K\<lparr>\<nu>*xvec\<rparr>\<langle>N\<rangle> \<prec> xQ'" and FrQ: "extractFrame(\<lparr>\<nu>x\<rparr>Q) = \<langle>A\<^sub>Q, \<Psi>\<^sub>Q\<rangle>" by fact+
      have PTrans: "\<Psi> \<otimes> \<Psi>\<^sub>Q \<rhd> P \<longmapsto>M\<lparr>N\<rparr> \<prec> P'" and FrP: "extractFrame P = \<langle>A\<^sub>P, \<Psi>\<^sub>P\<rangle>" by fact+
      have "x \<sharp> \<lparr>\<nu>x\<rparr>Q" by(simp add: abs_fresh)
      with QTrans have "x \<sharp> N" and "x \<sharp> xQ'" using `xvec \<sharp>* x` `xvec \<sharp>* K` `distinct xvec` 
        by(force intro: outputFreshDerivative)+
      from PTrans `x \<sharp> P` `x \<sharp> N`  have "x \<sharp> P'" by(rule inputFreshDerivative)
      from `x \<sharp> \<lparr>\<nu>x\<rparr>Q` FrQ `A\<^sub>Q \<sharp>* x` have "x \<sharp> \<Psi>\<^sub>Q"
        by(drule_tac extractFrameFresh) auto
      from `x \<sharp> P` FrP `A\<^sub>P \<sharp>* x` have "x \<sharp> \<Psi>\<^sub>P"
        by(drule_tac extractFrameFresh) auto
      from `A\<^sub>P \<sharp>* \<lparr>\<nu>x\<rparr>Q` `A\<^sub>P \<sharp>* x` have "A\<^sub>P \<sharp>* Q" by simp
      from `A\<^sub>Q \<sharp>* \<lparr>\<nu>x\<rparr>Q` `A\<^sub>Q \<sharp>* x` have "A\<^sub>Q \<sharp>* Q" by simp
      from PTrans FrP `distinct A\<^sub>P` `x \<sharp> P` `A\<^sub>Q \<sharp>* P` `xvec \<sharp>* P` `A\<^sub>P \<sharp>* \<Psi>` `A\<^sub>P \<sharp>* \<Psi>\<^sub>Q` `A\<^sub>P \<sharp>* x` `A\<^sub>P \<sharp>* A\<^sub>Q` `A\<^sub>P \<sharp>* P`  `A\<^sub>P \<sharp>* M` `A\<^sub>P \<sharp>* xvec`
      obtain M' where "(\<Psi> \<otimes> \<Psi>\<^sub>Q) \<otimes> \<Psi>\<^sub>P \<turnstile> M \<leftrightarrow> M'" and "x \<sharp> M'" and "A\<^sub>Q \<sharp>* M'" and "xvec \<sharp>* M'"
        by(rule_tac B="x#xvec@A\<^sub>Q" in obtainPrefix) (assumption | force simp add: fresh_star_list_cons)+
      hence MeqM': "\<Psi> \<otimes> \<Psi>\<^sub>P \<otimes> \<Psi>\<^sub>Q \<turnstile> M \<leftrightarrow> M'" by(metis statEqEnt Associativity Commutativity Composition)
      with `\<Psi> \<otimes> \<Psi>\<^sub>P \<otimes> \<Psi>\<^sub>Q \<turnstile> M \<leftrightarrow> K` have "\<Psi> \<otimes> \<Psi>\<^sub>P \<otimes> \<Psi>\<^sub>Q \<turnstile> K \<leftrightarrow> M'"
        by(blast intro: chanEqTrans chanEqSym)
      hence "(\<Psi> \<otimes> \<Psi>\<^sub>P) \<otimes> \<Psi>\<^sub>Q \<turnstile> K \<leftrightarrow> M'" by(metis statEqEnt Associativity Commutativity Composition)
      with QTrans FrQ `distinct A\<^sub>Q` `A\<^sub>Q \<sharp>* \<Psi>` `A\<^sub>Q \<sharp>* \<Psi>\<^sub>P` `A\<^sub>Q \<sharp>* (\<lparr>\<nu>x\<rparr>Q)` `A\<^sub>Q \<sharp>* K` `A\<^sub>Q \<sharp>* M'`
      have "\<Psi> \<otimes> \<Psi>\<^sub>P \<rhd> \<lparr>\<nu>x\<rparr>Q \<longmapsto>M'\<lparr>\<nu>*xvec\<rparr>\<langle>N\<rangle> \<prec> xQ'"
        by(force intro: outputRenameSubject)
      moreover from `x \<sharp> \<Psi>` `x \<sharp> \<Psi>\<^sub>P` have "x \<sharp> \<Psi> \<otimes> \<Psi>\<^sub>P" by force
      moreover from `xvec \<sharp>* x` have "x \<sharp> xvec" by simp
      with `x \<sharp> M'` `x \<sharp> N` have "x \<sharp> M'\<lparr>\<nu>*xvec\<rparr>\<langle>N\<rangle>" by simp
      moreover note `x \<sharp> xQ'`
      moreover from `xvec \<sharp>* \<Psi>` `xvec \<sharp>* \<Psi>\<^sub>P` have "bn(M'\<lparr>\<nu>*xvec\<rparr>\<langle>N\<rangle>) \<sharp>* (\<Psi> \<otimes> \<Psi>\<^sub>P)" by force
      moreover from `xvec \<sharp>* \<lparr>\<nu>x\<rparr>Q` `x \<sharp> xvec` have "bn(M'\<lparr>\<nu>*xvec\<rparr>\<langle>N\<rangle>) \<sharp>* Q" by simp
      moreover from `xvec \<sharp>* P` have "bn(M'\<lparr>\<nu>*xvec\<rparr>\<langle>N\<rangle>) \<sharp>* P" by simp
      from `xvec \<sharp>* \<Psi>` have "bn(M'\<lparr>\<nu>*xvec\<rparr>\<langle>N\<rangle>) \<sharp>* \<Psi>" by simp
      from `A\<^sub>Q \<sharp>* xvec` `A\<^sub>Q \<sharp>* M'` `A\<^sub>Q \<sharp>* N` have "A\<^sub>Q \<sharp>* (M'\<lparr>\<nu>*xvec\<rparr>\<langle>N\<rangle>)" by simp
      have "object(M'\<lparr>\<nu>*xvec\<rparr>\<langle>N\<rangle>) = Some N" by simp
      have "bn(M'\<lparr>\<nu>*xvec\<rparr>\<langle>N\<rangle>) = xvec" by simp
      have "subject(M'\<lparr>\<nu>*xvec\<rparr>\<langle>N\<rangle>) = Some M'" by simp
      from `xvec \<sharp>* M'` have "bn(M'\<lparr>\<nu>*xvec\<rparr>\<langle>N\<rangle>) \<sharp>* subject(M'\<lparr>\<nu>*xvec\<rparr>\<langle>N\<rangle>)" by simp
      ultimately show ?case 
        using `x \<sharp> M'\<lparr>\<nu>*xvec\<rparr>\<langle>N\<rangle>` `bn(M'\<lparr>\<nu>*xvec\<rparr>\<langle>N\<rangle>) \<sharp>* P` `bn(M'\<lparr>\<nu>*xvec\<rparr>\<langle>N\<rangle>) \<sharp>* \<Psi>` `object(M'\<lparr>\<nu>*xvec\<rparr>\<langle>N\<rangle>) = Some N`
              `bn(M'\<lparr>\<nu>*xvec\<rparr>\<langle>N\<rangle>) = xvec` `subject(M'\<lparr>\<nu>*xvec\<rparr>\<langle>N\<rangle>) = Some M'` `A\<^sub>Q \<sharp>* (M'\<lparr>\<nu>*xvec\<rparr>\<langle>N\<rangle>)`
      proof(induct rule: resCases)
        case(cOpen M'' xvec1 xvec2 y N' Q')
        from `x \<sharp> M''\<lparr>\<nu>*(xvec1@y#xvec2)\<rparr>\<langle>N'\<rangle>` have "x \<sharp> xvec1" and "x \<noteq> y" and "x \<sharp> xvec2" and "x \<sharp> M''"
          by simp+
        from `bn(M''\<lparr>\<nu>*(xvec1@y#xvec2)\<rparr>\<langle>N'\<rangle>) \<sharp>* P` have "(xvec1@xvec2) \<sharp>* P" and "y \<sharp> P" by simp+
        from `A\<^sub>Q \<sharp>* (M''\<lparr>\<nu>*(xvec1@y#xvec2)\<rparr>\<langle>N'\<rangle>)` have "(xvec1@xvec2) \<sharp>* A\<^sub>Q" and "y \<sharp> A\<^sub>Q" and "A\<^sub>Q \<sharp>* M''" by simp+
        from `bn(M''\<lparr>\<nu>*(xvec1@y#xvec2)\<rparr>\<langle>N'\<rangle>) \<sharp>* \<Psi>` have "(xvec1@xvec2) \<sharp>* \<Psi>" and "y \<sharp> \<Psi>" by simp+
        from `object(M''\<lparr>\<nu>*(xvec1@y#xvec2)\<rparr>\<langle>N'\<rangle>) = Some N` have "N = N'" by simp
        from `bn(M''\<lparr>\<nu>*(xvec1@y#xvec2)\<rparr>\<langle>N'\<rangle>) = xvec` have "xvec = xvec1@y#xvec2" by simp
        from `subject(M''\<lparr>\<nu>*(xvec1@y#xvec2)\<rparr>\<langle>N'\<rangle>) = Some M'` have "M' = M''" by simp
        from `x \<sharp> P` `y \<sharp> P` `x \<noteq> y` `\<Psi> \<otimes> \<Psi>\<^sub>Q \<rhd> P \<longmapsto>M\<lparr>N\<rparr> \<prec> P'`
        have "\<Psi> \<otimes> \<Psi>\<^sub>Q \<rhd> P \<longmapsto>M\<lparr>([(y, x)] \<bullet> N)\<rparr> \<prec> ([(y, x)] \<bullet> P')"
          by(rule_tac xvec="[y]" in inputAlpha) (auto simp add: calc_atm)
        hence PTrans: "\<Psi> \<otimes> \<Psi>\<^sub>Q \<rhd> P \<longmapsto>M\<lparr>([(x, y)] \<bullet> N)\<rparr> \<prec> ([(x, y)] \<bullet> P')"
          by(simp add: name_swap)
        have QTrans: "\<Psi> \<otimes> \<Psi>\<^sub>P \<rhd> Q \<longmapsto>M''\<lparr>\<nu>*(xvec1@xvec2)\<rparr>\<langle>([(x, y)] \<bullet> N')\<rangle> \<prec> ([(x, y)] \<bullet> Q')" by fact
        with `A\<^sub>Q \<sharp>* x` `y \<sharp> A\<^sub>Q` `distinct xvec1` `distinct xvec2` `xvec1 \<sharp>* xvec2` `xvec1 \<sharp>* M''` `xvec2 \<sharp>* M''`
             `(xvec1@xvec2) \<sharp>* A\<^sub>Q`
        have "A\<^sub>Q \<sharp>* ([(x, y)] \<bullet> Q')" using `A\<^sub>Q \<sharp>* Q`
          by(rule_tac outputFreshChainDerivative(2)) (assumption | simp)+

        from `extractFrame(\<lparr>\<nu>x\<rparr>Q) = \<langle>A\<^sub>Q, \<Psi>\<^sub>Q\<rangle>` have FrxQ: "\<lparr>\<nu>x\<rparr>(extractFrame Q) = \<langle>A\<^sub>Q, \<Psi>\<^sub>Q\<rangle>" by simp
        then obtain z A\<^sub>Q' where A: "A\<^sub>Q = z#A\<^sub>Q'" by(case_tac A\<^sub>Q) auto
        with `A\<^sub>Q \<sharp>* \<Psi>` `A\<^sub>Q \<sharp>* P` `A\<^sub>Q \<sharp>* P'` `A\<^sub>Q \<sharp>* \<Psi>\<^sub>P` `A\<^sub>Q \<sharp>* Q` `(xvec1@xvec2) \<sharp>* A\<^sub>Q` `A\<^sub>Q \<sharp>* M''` `A\<^sub>Q \<sharp>* ([(x, y)] \<bullet> Q')` `y \<sharp> A\<^sub>Q` `A\<^sub>Q \<sharp>* N`
        have "A\<^sub>Q' \<sharp>* \<Psi>" and "A\<^sub>Q' \<sharp>* P" and "A\<^sub>Q' \<sharp>* \<Psi>\<^sub>P" and "A\<^sub>Q' \<sharp>* Q"
          and "z \<sharp> \<Psi>" and "z \<sharp> P" and "z \<sharp> P'" and "z \<sharp> \<Psi>\<^sub>P" and "z \<sharp> Q" and "z \<sharp> xvec1" and "z \<sharp> xvec2"
          and "z \<sharp> M''" and "z \<sharp> ([(x, y)] \<bullet> Q')" and "A\<^sub>Q' \<sharp>* M''" and "z \<noteq> y" and "z \<sharp> (xvec1@xvec2)"
          by auto
        from A `A\<^sub>P \<sharp>* A\<^sub>Q` have "A\<^sub>P \<sharp>* A\<^sub>Q'" and "z \<sharp> A\<^sub>P" by simp+
        from A `A\<^sub>Q \<sharp>* x` have "x \<noteq> z" and "x \<sharp> A\<^sub>Q'" by simp+

        from `distinct A\<^sub>Q` A have "z \<sharp> A\<^sub>Q'" 
          by(induct A\<^sub>Q') (auto simp add: fresh_list_nil fresh_list_cons)
        from PTrans `x \<sharp> P` `z \<sharp> P` `x \<noteq> z` have "\<Psi> \<otimes> \<Psi>\<^sub>Q \<rhd> P \<longmapsto>M\<lparr>([(x, z)] \<bullet> [(x, y)] \<bullet> N)\<rparr> \<prec> ([(x, z)] \<bullet> [(x, y)] \<bullet> P')"
          by(rule_tac xvec="[x]" in inputAlpha) (auto simp add: calc_atm)
        moreover note FrP 
        moreover from QTrans have "([(x, z)] \<bullet> (\<Psi> \<otimes> \<Psi>\<^sub>P)) \<rhd> ([(x, z)] \<bullet> Q) \<longmapsto>([(x, z)] \<bullet> (M''\<lparr>\<nu>*(xvec1@xvec2)\<rparr>\<langle>([(x, y)] \<bullet> N')\<rangle> \<prec> ([(x, y)] \<bullet> Q')))" 
          by(rule semantics.eqvt)
        with `x \<sharp> \<Psi>` `z \<sharp> \<Psi>` `x \<sharp> \<Psi>\<^sub>P` `z \<sharp> \<Psi>\<^sub>P` `x \<sharp> M''` `z \<sharp> M''` `x \<sharp> xvec1` `x \<sharp> xvec2` `z \<sharp> xvec1` `z \<sharp> xvec2`
        have "\<Psi> \<otimes> \<Psi>\<^sub>P \<rhd> ([(x, z)] \<bullet> Q) \<longmapsto>M''\<lparr>\<nu>*(xvec1@xvec2)\<rparr>\<langle>([(x, z)] \<bullet> [(x, y)] \<bullet> N')\<rangle> \<prec> ([(x, z)] \<bullet> [(x, y)] \<bullet> Q')" 
          by(simp add: eqvts)
        moreover from A `A\<^sub>Q \<sharp>* x` FrxQ have "extractFrame([(x, z)] \<bullet> Q) = \<langle>A\<^sub>Q', \<Psi>\<^sub>Q\<rangle>"
          by(clarsimp simp add: alpha' eqvts frame.inject fresh_list_cons name_swap)
        moreover from `A\<^sub>P \<sharp>* Q` have "([(x, z)] \<bullet> A\<^sub>P) \<sharp>* ([(x, z)] \<bullet> Q)"
          by(simp add: pt_fresh_star_bij[OF pt_name_inst, OF at_name_inst])
        with `A\<^sub>P \<sharp>* x` `z \<sharp> A\<^sub>P` have "A\<^sub>P \<sharp>* ([(x, z)] \<bullet> Q)" by simp
        moreover from `A\<^sub>Q' \<sharp>* Q` have "([(x, z)] \<bullet> A\<^sub>Q') \<sharp>* ([(x, z)] \<bullet> Q)"
          by(simp add: pt_fresh_star_bij[OF pt_name_inst, OF at_name_inst])
        with `x \<sharp> A\<^sub>Q'` `z \<sharp> A\<^sub>Q'` have "A\<^sub>Q' \<sharp>* ([(x, z)] \<bullet> Q)" by simp
        ultimately have "\<Psi> \<rhd> (P \<parallel> ([(x, z)] \<bullet> Q)) \<longmapsto>\<tau> \<prec> \<lparr>\<nu>*(xvec1@xvec2)\<rparr>(([(x, z)] \<bullet> [(x, y)] \<bullet> P') \<parallel> ([(x, z)] \<bullet> [(x, y)] \<bullet> Q'))"
          using MeqM' `M'=M''` `N=N'` `A\<^sub>P \<sharp>* \<Psi>` `A\<^sub>P \<sharp>* P`  `A\<^sub>P \<sharp>* A\<^sub>Q'` `A\<^sub>Q' \<sharp>* \<Psi>` `A\<^sub>Q' \<sharp>* P` `(xvec1@xvec2) \<sharp>* P` `A\<^sub>P \<sharp>* M` `A\<^sub>Q' \<sharp>* M''`
          by(rule_tac Comm1) (assumption | simp)+
        with`z \<sharp> \<Psi>` have "\<Psi> \<rhd> \<lparr>\<nu>z\<rparr>(P \<parallel> ([(x, z)] \<bullet> Q)) \<longmapsto>\<tau> \<prec> \<lparr>\<nu>z\<rparr>(\<lparr>\<nu>*(xvec1@xvec2)\<rparr>(([(x, z)] \<bullet> [(x, y)] \<bullet> P') \<parallel> ([(x, z)] \<bullet> [(x, y)] \<bullet> Q')))"
          by(rule_tac Scope) auto
        moreover from `x \<sharp> P` `z \<sharp> P` `z \<sharp> Q` have "\<lparr>\<nu>z\<rparr>(P \<parallel> ([(x, z)] \<bullet> Q)) = \<lparr>\<nu>x\<rparr>([(x, z)] \<bullet> (P \<parallel> ([(x, z)] \<bullet> Q)))"
          by(subst alphaRes[of x]) (auto simp add: calc_atm fresh_left name_swap)
        with `x \<sharp> P` `z \<sharp> P` have "\<lparr>\<nu>z\<rparr>(P \<parallel> ([(x, z)] \<bullet> Q)) = \<lparr>\<nu>x\<rparr>(P \<parallel> Q)"
          by(simp add: eqvts)
        moreover from `z \<noteq> y` `x \<noteq> z` `z \<sharp> P'` `z \<sharp> [(x, y)] \<bullet> Q'` have "\<lparr>\<nu>z\<rparr>(\<lparr>\<nu>*(xvec1@xvec2)\<rparr>(([(x, z)] \<bullet> [(x, y)] \<bullet> P') \<parallel> ([(x, z)] \<bullet> [(x, y)] \<bullet> Q'))) = \<lparr>\<nu>x\<rparr>([(x, z)] \<bullet> (\<lparr>\<nu>*(xvec1@xvec2)\<rparr>(([(x, z)] \<bullet> [(x, y)] \<bullet> P') \<parallel> ([(x, z)] \<bullet> [(x, y)] \<bullet> Q'))))"
          by(subst alphaRes[of x]) (auto simp add: resChainFresh fresh_left calc_atm name_swap)
        with `x \<sharp> xvec1` `x \<sharp> xvec2` `z \<sharp> xvec1` `z \<sharp> xvec2` have "\<lparr>\<nu>z\<rparr>(\<lparr>\<nu>*(xvec1@xvec2)\<rparr>(([(x, z)] \<bullet> [(x, y)] \<bullet> P') \<parallel> ([(x, z)] \<bullet> [(x, y)] \<bullet> Q'))) = \<lparr>\<nu>x\<rparr>(\<lparr>\<nu>*(xvec1@xvec2)\<rparr>(([(x, y)] \<bullet> P') \<parallel> ([(x, y)] \<bullet> Q')))"
          by(simp add: eqvts)
        moreover from `x \<sharp> P'` `x \<sharp> Q'` `x \<sharp> xvec1` `x \<sharp> xvec2` `y \<sharp> xvec1` `y \<sharp> xvec2`
          have "\<lparr>\<nu>x\<rparr>(\<lparr>\<nu>*(xvec1@xvec2)\<rparr>(([(x, y)] \<bullet> P') \<parallel> ([(x, y)] \<bullet> Q'))) =  \<lparr>\<nu>y\<rparr>(\<lparr>\<nu>*(xvec1@xvec2)\<rparr>(P' \<parallel> Q'))"
          by(subst alphaRes[of y]) (auto simp add: resChainFresh calc_atm eqvts fresh_left name_swap)
        ultimately have "\<Psi> \<rhd> \<lparr>\<nu>x\<rparr>(P \<parallel> Q) \<longmapsto>\<tau> \<prec> \<lparr>\<nu>y\<rparr>(\<lparr>\<nu>*(xvec1@xvec2)\<rparr>(P' \<parallel> Q'))"
          by simp
        moreover from `y \<sharp> \<Psi>` `(xvec1@xvec2) \<sharp>* \<Psi>` `xvec=xvec1@y#xvec2`
        have "(\<Psi>, \<lparr>\<nu>y\<rparr>(\<lparr>\<nu>*(xvec1@xvec2)\<rparr>(P' \<parallel> Q')), \<lparr>\<nu>*xvec\<rparr>(P' \<parallel> Q')) \<in> Rel"
          by(force intro: C3 simp add: resChainAppend)
        ultimately show ?case by blast
      next
        case(cRes Q')   
        have QTrans: "\<Psi> \<otimes> \<Psi>\<^sub>P \<rhd> Q \<longmapsto>M'\<lparr>\<nu>*xvec\<rparr>\<langle>N\<rangle> \<prec> Q'" by fact
        with `A\<^sub>Q \<sharp>* Q` `A\<^sub>Q \<sharp>* xvec` `xvec \<sharp>* M'` `distinct xvec` have "A\<^sub>Q \<sharp>* Q'"
          by(force dest: outputFreshChainDerivative)
        
        with `extractFrame(\<lparr>\<nu>x\<rparr>Q) = \<langle>A\<^sub>Q, \<Psi>\<^sub>Q\<rangle>` have FrxQ: "\<lparr>\<nu>x\<rparr>(extractFrame Q) = \<langle>A\<^sub>Q, \<Psi>\<^sub>Q\<rangle>" by simp
        then obtain y A\<^sub>Q' where A: "A\<^sub>Q = y#A\<^sub>Q'" by(case_tac A\<^sub>Q) auto
        with `A\<^sub>Q \<sharp>* \<Psi>` `A\<^sub>Q \<sharp>* P` `A\<^sub>Q \<sharp>* P'` `A\<^sub>Q \<sharp>* \<Psi>\<^sub>P` `A\<^sub>Q \<sharp>* Q` `A\<^sub>Q \<sharp>* xvec` `A\<^sub>Q \<sharp>* M'` `A\<^sub>Q \<sharp>* Q'`
        have "A\<^sub>Q' \<sharp>* \<Psi>" and "A\<^sub>Q' \<sharp>* P" and "A\<^sub>Q' \<sharp>* \<Psi>\<^sub>P" and "A\<^sub>Q' \<sharp>* Q" and "A\<^sub>Q \<sharp>* xvec" and "A\<^sub>Q \<sharp>* Q'"
          and "y \<sharp> \<Psi>" and "y \<sharp> P" and "y \<sharp> P'" and "y \<sharp> \<Psi>\<^sub>P" and "y \<sharp> Q" and "y \<sharp> xvec" and "y \<sharp> M'" and "y \<sharp> Q'"
          and "A\<^sub>Q' \<sharp>* M'"
          by(simp)+
        from A `A\<^sub>P \<sharp>* A\<^sub>Q` have "A\<^sub>P \<sharp>* A\<^sub>Q'" and "y \<sharp> A\<^sub>P" by(simp add: fresh_star_list_cons)+
        from A `A\<^sub>Q \<sharp>* x` have "x \<noteq> y" and "x \<sharp> A\<^sub>Q'" by(simp add: fresh_list_cons)+
        
        with A `distinct A\<^sub>Q` have "y \<sharp> A\<^sub>Q'" 
          by(induct A\<^sub>Q') (auto simp add: fresh_list_nil fresh_list_cons)

        from `x \<sharp> P` `y \<sharp> P` `x \<noteq> y` `\<Psi> \<otimes> \<Psi>\<^sub>Q \<rhd> P \<longmapsto>M\<lparr>N\<rparr> \<prec> P'`
        have "\<Psi> \<otimes> \<Psi>\<^sub>Q \<rhd> P \<longmapsto>M\<lparr>([(y, x)] \<bullet> N)\<rparr> \<prec> [(y, x)] \<bullet> P'"
          by(rule_tac xvec="[y]" in inputAlpha) (auto simp add: calc_atm)
        hence "\<Psi> \<otimes> \<Psi>\<^sub>Q \<rhd> P \<longmapsto>M\<lparr>([(x, y)] \<bullet> N)\<rparr> \<prec> [(x, y)] \<bullet> P'"
          by(simp add: name_swap)
        moreover note FrP
        moreover from  `\<Psi> \<otimes> \<Psi>\<^sub>P \<rhd> Q \<longmapsto>M'\<lparr>\<nu>*xvec\<rparr>\<langle>N\<rangle> \<prec> Q'` have "([(x, y)] \<bullet> (\<Psi> \<otimes> \<Psi>\<^sub>P)) \<rhd> ([(x, y)] \<bullet> Q) \<longmapsto>([(x, y)] \<bullet> (M'\<lparr>\<nu>*xvec\<rparr>\<langle>N\<rangle> \<prec> Q'))" 
          by(rule semantics.eqvt)
        with `x \<sharp> \<Psi>` `y \<sharp> \<Psi>` `x \<sharp> \<Psi>\<^sub>P` `y \<sharp> \<Psi>\<^sub>P` `x \<sharp> M'` `y \<sharp> M'` `x \<sharp> xvec` `y \<sharp> xvec`
        have "\<Psi> \<otimes> \<Psi>\<^sub>P \<rhd> ([(x, y)] \<bullet> Q) \<longmapsto>M'\<lparr>\<nu>*xvec\<rparr>\<langle>([(x, y)] \<bullet> N)\<rangle> \<prec> ([(x, y)] \<bullet> Q')" 
          by(simp add: eqvts)
        moreover from A `A\<^sub>Q \<sharp>* x` FrxQ have FrQ: "extractFrame([(x, y)] \<bullet> Q) = \<langle>A\<^sub>Q', \<Psi>\<^sub>Q\<rangle>"
          by(clarsimp simp add: alpha' eqvts frame.inject fresh_list_cons name_swap)
        moreover from `A\<^sub>P \<sharp>* Q` have "([(x, y)] \<bullet> A\<^sub>P) \<sharp>* ([(x, y)] \<bullet> Q)" by(simp add: pt_fresh_star_bij[OF pt_name_inst, OF at_name_inst])
        with `A\<^sub>P \<sharp>* x` `y \<sharp> A\<^sub>P` have "A\<^sub>P \<sharp>* ([(x, y)] \<bullet> Q)" by simp
        moreover from `A\<^sub>Q' \<sharp>* Q` have "([(x, y)] \<bullet> A\<^sub>Q') \<sharp>* ([(x, y)] \<bullet> Q)" by(simp add: pt_fresh_star_bij[OF pt_name_inst, OF at_name_inst])
        with `x \<sharp> A\<^sub>Q'` `y \<sharp> A\<^sub>Q'` have "A\<^sub>Q' \<sharp>* ([(x, y)] \<bullet> Q)" by simp
        ultimately have "\<Psi> \<rhd> (P \<parallel> ([(x, y)] \<bullet> Q)) \<longmapsto>\<tau> \<prec> \<lparr>\<nu>*xvec\<rparr>([(x, y)] \<bullet> P') \<parallel> ([(x, y)] \<bullet> Q')"
          using MeqM' `A\<^sub>P \<sharp>* \<Psi>` `A\<^sub>P \<sharp>* P`  `A\<^sub>P \<sharp>* A\<^sub>Q'` `A\<^sub>Q' \<sharp>* \<Psi>` `A\<^sub>Q' \<sharp>* P` `xvec \<sharp>* P` `A\<^sub>P \<sharp>* M` `A\<^sub>Q' \<sharp>* M'`
          by(rule_tac Comm1) (assumption | simp)+
        with`y \<sharp> \<Psi>` have "\<Psi> \<rhd> \<lparr>\<nu>y\<rparr>(P \<parallel> ([(x, y)] \<bullet> Q)) \<longmapsto>\<tau> \<prec> \<lparr>\<nu>y\<rparr>(\<lparr>\<nu>*xvec\<rparr>(([(x, y)] \<bullet> P') \<parallel> ([(x, y)] \<bullet> Q')))"
          by(rule_tac Scope) auto
        moreover from `x \<sharp> P` `y \<sharp> P` `y \<sharp> Q` have "\<lparr>\<nu>y\<rparr>(P \<parallel> ([(x, y)] \<bullet> Q)) = \<lparr>\<nu>x\<rparr>([(x, y)] \<bullet> (P \<parallel> ([(x, y)] \<bullet> Q)))"
          by(subst alphaRes[of x]) (auto simp add: calc_atm fresh_left name_swap)
        with `x \<sharp> P` `y \<sharp> P` have "\<lparr>\<nu>y\<rparr>(P \<parallel> ([(x, y)] \<bullet> Q)) = \<lparr>\<nu>x\<rparr>(P \<parallel> Q)"
          by(simp add: eqvts)
        moreover from `y \<sharp> P'` `y \<sharp> Q'` `x \<sharp> xvec` `y \<sharp> xvec` have "\<lparr>\<nu>y\<rparr>(\<lparr>\<nu>*xvec\<rparr>(([(x, y)] \<bullet> P') \<parallel> ([(x, y)] \<bullet> Q'))) =  \<lparr>\<nu>x\<rparr>(\<lparr>\<nu>*xvec\<rparr>(P' \<parallel> Q'))"
          by(subst alphaRes[of y]) (auto simp add: resChainFresh calc_atm eqvts fresh_left name_swap)
        ultimately have "\<Psi> \<rhd> \<lparr>\<nu>x\<rparr>(P \<parallel> Q) \<longmapsto>\<tau> \<prec> \<lparr>\<nu>x\<rparr>(\<lparr>\<nu>*xvec\<rparr>(P' \<parallel> Q'))"
          by simp
        moreover from `x \<sharp> \<Psi>` `x \<sharp> P'` `xvec \<sharp>* \<Psi>` have "(\<Psi>, \<lparr>\<nu>x\<rparr>(\<lparr>\<nu>*xvec\<rparr>(P' \<parallel> Q')), \<lparr>\<nu>*xvec\<rparr>(P' \<parallel> \<lparr>\<nu>x\<rparr>Q')) \<in> Rel"
          by(rule C2)
        ultimately show ?case by blast
      qed
    next
      case(cComm2 \<Psi>\<^sub>Q M xvec N P' A\<^sub>P \<Psi>\<^sub>P K xQ' A\<^sub>Q)
      have QTrans: "\<Psi> \<otimes> \<Psi>\<^sub>P \<rhd> \<lparr>\<nu>x\<rparr>Q \<longmapsto>K\<lparr>N\<rparr> \<prec> xQ'" and FrQ: "extractFrame(\<lparr>\<nu>x\<rparr>Q) = \<langle>A\<^sub>Q, \<Psi>\<^sub>Q\<rangle>" by fact+
      have PTrans: "\<Psi> \<otimes> \<Psi>\<^sub>Q \<rhd> P \<longmapsto>M\<lparr>\<nu>*xvec\<rparr>\<langle>N\<rangle> \<prec> P'" and FrP: "extractFrame P = \<langle>A\<^sub>P, \<Psi>\<^sub>P\<rangle>" by fact+
      from PTrans `x \<sharp> P` have "x \<sharp> N" and "x \<sharp> P'" using `xvec \<sharp>* x` `xvec \<sharp>* M` `distinct xvec` 
        by(force intro: outputFreshDerivative)+
      have "x \<sharp> \<lparr>\<nu>x\<rparr>Q" by(simp add: abs_fresh)
      with FrQ `A\<^sub>Q \<sharp>* x` have "x \<sharp> \<Psi>\<^sub>Q"
        by(drule_tac extractFrameFresh) auto
      from `x \<sharp> P` FrP `A\<^sub>P \<sharp>* x` have "x \<sharp> \<Psi>\<^sub>P"
        by(drule_tac extractFrameFresh) auto
      from `A\<^sub>P \<sharp>* \<lparr>\<nu>x\<rparr>Q` `A\<^sub>P \<sharp>* x` have "A\<^sub>P \<sharp>* Q" by simp
      from `A\<^sub>Q \<sharp>* \<lparr>\<nu>x\<rparr>Q` `A\<^sub>Q \<sharp>* x` have "A\<^sub>Q \<sharp>* Q" by simp
      from `xvec \<sharp>* x` `xvec \<sharp>* \<lparr>\<nu>x\<rparr>Q` have "xvec \<sharp>* Q" by simp

      from PTrans FrP `distinct A\<^sub>P` `x \<sharp> P` `A\<^sub>Q \<sharp>* P` `A\<^sub>P \<sharp>* \<Psi>` `A\<^sub>P \<sharp>* \<Psi>\<^sub>Q` `A\<^sub>P \<sharp>* x` `A\<^sub>P \<sharp>* A\<^sub>Q` `A\<^sub>P \<sharp>* P`  `A\<^sub>P \<sharp>* M` `xvec \<sharp>* M` `distinct xvec`
      obtain M' where "(\<Psi> \<otimes> \<Psi>\<^sub>Q) \<otimes> \<Psi>\<^sub>P \<turnstile> M \<leftrightarrow> M'" and "x \<sharp> M'" and "A\<^sub>Q \<sharp>* M'"
        by(rule_tac B="x#A\<^sub>Q" in obtainPrefix) (assumption | force simp add: fresh_star_list_cons)+
      hence MeqM': "\<Psi> \<otimes> \<Psi>\<^sub>P \<otimes> \<Psi>\<^sub>Q \<turnstile> M \<leftrightarrow> M'"
        by(metis statEqEnt Associativity Commutativity Composition)
      with `\<Psi> \<otimes> \<Psi>\<^sub>P \<otimes> \<Psi>\<^sub>Q \<turnstile> M \<leftrightarrow> K` have "\<Psi> \<otimes> \<Psi>\<^sub>P \<otimes> \<Psi>\<^sub>Q \<turnstile> K \<leftrightarrow> M'"
        by(blast intro: chanEqTrans chanEqSym)
      hence "(\<Psi> \<otimes> \<Psi>\<^sub>P) \<otimes> \<Psi>\<^sub>Q \<turnstile> K \<leftrightarrow> M'"
        by(metis statEqEnt Associativity Commutativity Composition)
      with QTrans FrQ `distinct A\<^sub>Q` `A\<^sub>Q \<sharp>* \<Psi>` `A\<^sub>Q \<sharp>* \<Psi>\<^sub>P` `A\<^sub>Q \<sharp>* (\<lparr>\<nu>x\<rparr>Q)` `A\<^sub>Q \<sharp>* K` `A\<^sub>Q \<sharp>* M'`
      have "\<Psi> \<otimes> \<Psi>\<^sub>P \<rhd> \<lparr>\<nu>x\<rparr>Q \<longmapsto>M'\<lparr>N\<rparr> \<prec> xQ'" by(force intro: inputRenameSubject)

      moreover from `x \<sharp> \<Psi>` `x \<sharp> \<Psi>\<^sub>P` have "x \<sharp> \<Psi> \<otimes> \<Psi>\<^sub>P" by force
      moreover note `x \<sharp> M'` `x \<sharp> N` 
      moreover from QTrans `x \<sharp> N` have "x \<sharp> xQ'" by(force dest: inputFreshDerivative simp add: abs_fresh)
      ultimately show ?case
      proof(induct rule: resInputCases)
        case(cRes Q')   
        have QTrans: "\<Psi> \<otimes> \<Psi>\<^sub>P \<rhd> Q \<longmapsto>M'\<lparr>N\<rparr> \<prec> Q'" by fact
        with `A\<^sub>Q \<sharp>* Q` `A\<^sub>Q \<sharp>* N` have "A\<^sub>Q \<sharp>* Q'"
          by(rule_tac inputFreshChainDerivative)

        with `extractFrame(\<lparr>\<nu>x\<rparr>Q) = \<langle>A\<^sub>Q, \<Psi>\<^sub>Q\<rangle>` have FrxQ: "\<lparr>\<nu>x\<rparr>(extractFrame Q) = \<langle>A\<^sub>Q, \<Psi>\<^sub>Q\<rangle>" by simp
        then obtain y A\<^sub>Q' where A: "A\<^sub>Q = y#A\<^sub>Q'" by(case_tac A\<^sub>Q) auto
        with `A\<^sub>Q \<sharp>* \<Psi>` `A\<^sub>Q \<sharp>* P` `A\<^sub>Q \<sharp>* P'` `A\<^sub>Q \<sharp>* \<Psi>\<^sub>P` `A\<^sub>Q \<sharp>* Q` `A\<^sub>Q \<sharp>* xvec` `A\<^sub>Q \<sharp>* M'` `A\<^sub>Q \<sharp>* Q'` `A\<^sub>Q \<sharp>* N`
        have "A\<^sub>Q' \<sharp>* \<Psi>" and "A\<^sub>Q' \<sharp>* P" and "A\<^sub>Q' \<sharp>* \<Psi>\<^sub>P" and "A\<^sub>Q' \<sharp>* Q" and "A\<^sub>Q \<sharp>* xvec" and "A\<^sub>Q \<sharp>* Q'"
          and "y \<sharp> \<Psi>" and "y \<sharp> P" and "y \<sharp> P'" and "y \<sharp> \<Psi>\<^sub>P" and "y \<sharp> Q" and "y \<sharp> xvec" and "y \<sharp> M'" and "y \<sharp> Q'" and "y \<sharp> N"
          and "A\<^sub>Q' \<sharp>* M'"
          by(simp)+
        from A `A\<^sub>P \<sharp>* A\<^sub>Q` have "A\<^sub>P \<sharp>* A\<^sub>Q'" and "y \<sharp> A\<^sub>P" by(simp add: fresh_star_list_cons)+
        from A `A\<^sub>Q \<sharp>* x` have "x \<noteq> y" and "x \<sharp> A\<^sub>Q'" by(simp add: fresh_list_cons)+
        
        with A `distinct A\<^sub>Q` have "y \<sharp> A\<^sub>Q'" 
          by(induct A\<^sub>Q') (auto simp add: fresh_list_nil fresh_list_cons)

        note PTrans FrP
        moreover from  `\<Psi> \<otimes> \<Psi>\<^sub>P \<rhd> Q \<longmapsto>M'\<lparr>N\<rparr> \<prec> Q'` have "([(x, y)] \<bullet> (\<Psi> \<otimes> \<Psi>\<^sub>P)) \<rhd> ([(x, y)] \<bullet> Q) \<longmapsto>([(x, y)] \<bullet> (M'\<lparr>N\<rparr> \<prec> Q'))" 
          by(rule semantics.eqvt)
        with `x \<sharp> \<Psi>` `y \<sharp> \<Psi>` `x \<sharp> \<Psi>\<^sub>P` `y \<sharp> \<Psi>\<^sub>P` `x \<sharp> M'` `y \<sharp> M'` `x \<sharp> N` `y \<sharp> N`
        have "\<Psi> \<otimes> \<Psi>\<^sub>P \<rhd> ([(x, y)] \<bullet> Q) \<longmapsto>M'\<lparr>N\<rparr> \<prec> ([(x, y)] \<bullet> Q')" 
          by(simp add: eqvts)
        moreover from A `A\<^sub>Q \<sharp>* x` FrxQ have FrQ: "extractFrame([(x, y)] \<bullet> Q) = \<langle>A\<^sub>Q', \<Psi>\<^sub>Q\<rangle>" and "y \<sharp> extractFrame Q"
          by(clarsimp simp add: alpha' eqvts frame.inject fresh_list_cons name_swap)+
        moreover from `A\<^sub>P \<sharp>* Q` have "([(x, y)] \<bullet> A\<^sub>P) \<sharp>* ([(x, y)] \<bullet> Q)" by(simp add: pt_fresh_star_bij[OF pt_name_inst, OF at_name_inst])
        with `A\<^sub>P \<sharp>* x` `y \<sharp> A\<^sub>P` have "A\<^sub>P \<sharp>* ([(x, y)] \<bullet> Q)" by simp
        moreover from `A\<^sub>Q' \<sharp>* Q` have "([(x, y)] \<bullet> A\<^sub>Q') \<sharp>* ([(x, y)] \<bullet> Q)" by(simp add: pt_fresh_star_bij[OF pt_name_inst, OF at_name_inst])
        with `x \<sharp> A\<^sub>Q'` `y \<sharp> A\<^sub>Q'` have "A\<^sub>Q' \<sharp>* ([(x, y)] \<bullet> Q)" by simp
        moreover from `xvec \<sharp>* Q` have "([(x, y)] \<bullet> xvec) \<sharp>* ([(x, y)] \<bullet> Q)" by(simp add: pt_fresh_star_bij[OF pt_name_inst, OF at_name_inst])
        with `xvec \<sharp>* x` `y \<sharp> xvec` have "xvec \<sharp>* ([(x, y)] \<bullet> Q)" by simp
        ultimately have "\<Psi> \<rhd> (P \<parallel> ([(x, y)] \<bullet> Q)) \<longmapsto>\<tau> \<prec> \<lparr>\<nu>*xvec\<rparr>(P' \<parallel> ([(x, y)] \<bullet> Q'))"
          using MeqM' `A\<^sub>P \<sharp>* \<Psi>` `A\<^sub>P \<sharp>* P`  `A\<^sub>P \<sharp>* A\<^sub>Q'` `A\<^sub>Q' \<sharp>* \<Psi>` `A\<^sub>Q' \<sharp>* P` `A\<^sub>P \<sharp>* M` `A\<^sub>Q' \<sharp>* M'`
          by(rule_tac Comm2) (assumption | simp)+
        with`y \<sharp> \<Psi>` have "\<Psi> \<rhd> \<lparr>\<nu>y\<rparr>(P \<parallel> ([(x, y)] \<bullet> Q)) \<longmapsto>\<tau> \<prec> \<lparr>\<nu>y\<rparr>(\<lparr>\<nu>*xvec\<rparr>(P' \<parallel> ([(x, y)] \<bullet> Q')))"
          by(rule_tac Scope) auto
        moreover from `x \<sharp> P` `y \<sharp> P` `y \<sharp> Q` have "\<lparr>\<nu>y\<rparr>(P \<parallel> ([(x, y)] \<bullet> Q)) = \<lparr>\<nu>x\<rparr>([(x, y)] \<bullet> (P \<parallel> ([(x, y)] \<bullet> Q)))"
          by(subst alphaRes[of x]) (auto simp add: calc_atm fresh_left name_swap)
        with `x \<sharp> P` `y \<sharp> P` have "\<lparr>\<nu>y\<rparr>(P \<parallel> ([(x, y)] \<bullet> Q)) = \<lparr>\<nu>x\<rparr>(P \<parallel> Q)"
          by(simp add: eqvts)
        moreover from `x \<sharp> P'` `y \<sharp> P'` `y \<sharp> Q'` `xvec \<sharp>* x` `y \<sharp> xvec` have "\<lparr>\<nu>y\<rparr>(\<lparr>\<nu>*xvec\<rparr>(P' \<parallel> ([(x, y)] \<bullet> Q'))) =  \<lparr>\<nu>x\<rparr>(\<lparr>\<nu>*xvec\<rparr>(P' \<parallel> Q'))"
          by(subst alphaRes[of y]) (auto simp add: resChainFresh calc_atm eqvts fresh_left name_swap)
        ultimately have "\<Psi> \<rhd> \<lparr>\<nu>x\<rparr>(P \<parallel> Q) \<longmapsto>\<tau> \<prec> \<lparr>\<nu>x\<rparr>(\<lparr>\<nu>*xvec\<rparr>(P' \<parallel> Q'))"
          by simp
        moreover from `x \<sharp> \<Psi>` `x \<sharp> P'` `xvec \<sharp>* \<Psi>` have "(\<Psi>, \<lparr>\<nu>x\<rparr>(\<lparr>\<nu>*xvec\<rparr>(P' \<parallel> Q')), \<lparr>\<nu>*xvec\<rparr>(P' \<parallel> \<lparr>\<nu>x\<rparr>Q')) \<in> Rel"
          by(rule C2)
        ultimately show ?case by blast
      qed
    qed
  qed
qed

lemma scopeExtRight:
  fixes x   :: name
  and   P   :: "('a, 'b, 'c) psi"
  and   \<Psi>   :: 'b
  and   Q   :: "('a, 'b, 'c) psi"
  and   Rel :: "('b \<times> ('a, 'b, 'c) psi \<times> ('a, 'b, 'c) psi) set"

  assumes "x \<sharp> P"
  and     "x \<sharp> \<Psi>"
  and     "eqvt Rel"
  and     C1: "\<And>\<Psi>' R. (\<Psi>, R, R) \<in> Rel"
  and     C2: "\<And>y \<Psi>' R S zvec. \<lbrakk>y \<sharp> \<Psi>'; y \<sharp> R; zvec \<sharp>* \<Psi>'\<rbrakk> \<Longrightarrow> (\<Psi>', \<lparr>\<nu>*zvec\<rparr>(R \<parallel> \<lparr>\<nu>y\<rparr>S), \<lparr>\<nu>y\<rparr>(\<lparr>\<nu>*zvec\<rparr>(R \<parallel> S))) \<in> Rel"

  shows "\<Psi> \<rhd> P \<parallel> \<lparr>\<nu>x\<rparr>Q \<leadsto>[Rel] \<lparr>\<nu>x\<rparr>(P \<parallel> Q)"
proof -
  note `eqvt Rel` `x \<sharp> \<Psi>`
  moreover from `x \<sharp> P` have "x \<sharp> P \<parallel> \<lparr>\<nu>x\<rparr>Q" by(simp add: abs_fresh)
  moreover from `x \<sharp> P` have "x \<sharp> \<lparr>\<nu>x\<rparr>(P \<parallel> Q)" by(simp add: abs_fresh)
  ultimately show ?thesis
  proof(induct rule: simIFresh[of _ _ _ _ _ "()"])
    case(cSim \<alpha> xPQ)
    from `bn \<alpha> \<sharp>* (P \<parallel> \<lparr>\<nu>x\<rparr>Q)` `x \<sharp> \<alpha>` have "bn \<alpha>  \<sharp>* P" and "bn \<alpha>  \<sharp>* Q" by simp+
    note `\<Psi> \<rhd> \<lparr>\<nu>x\<rparr>(P \<parallel> Q) \<longmapsto>\<alpha> \<prec> xPQ` `x \<sharp> \<Psi>` `x \<sharp> \<alpha>` `x \<sharp> xPQ` `bn \<alpha> \<sharp>* \<Psi>`
    moreover from `bn \<alpha> \<sharp>* P` `bn \<alpha> \<sharp>* Q` have "bn \<alpha> \<sharp>* (P \<parallel> Q)" by simp
    ultimately show ?case using `bn \<alpha> \<sharp>* subject \<alpha>` `x \<sharp> \<alpha>`
    proof(induct rule: resCases)
      case(cOpen M xvec1 xvec2 y N PQ)
      from `x \<sharp> M\<lparr>\<nu>*(xvec1@y#xvec2)\<rparr>\<langle>N\<rangle>` have "x \<sharp> xvec1" and "x \<noteq> y" and "x \<sharp> xvec2" and "x \<sharp> M" by simp+
      from `xvec1 \<sharp>* (P \<parallel> Q)` `xvec2 \<sharp>* (P \<parallel> Q)` `y \<sharp> (P \<parallel> Q)`
      have "(xvec1@xvec2) \<sharp>* P" and "(xvec1@xvec2) \<sharp>* Q" and "y \<sharp> P" and "y \<sharp> Q"
        by simp+
      from `\<Psi> \<rhd> P \<parallel> Q \<longmapsto> M\<lparr>\<nu>*(xvec1@xvec2)\<rparr>\<langle>([(x, y)] \<bullet> N)\<rangle> \<prec> ([(x, y)] \<bullet> PQ)`
      have "([(x, y)] \<bullet> \<Psi>) \<rhd> ([(x, y)] \<bullet> (P \<parallel> Q)) \<longmapsto> ([(x, y)] \<bullet> (M\<lparr>\<nu>*(xvec1@xvec2)\<rparr>\<langle>([(x, y)] \<bullet> N)\<rangle> \<prec> ([(x, y)] \<bullet> PQ)))"
        by(rule semantics.eqvt)
      with `x \<sharp> \<Psi>` `y \<sharp> \<Psi>` `x \<sharp> P` `y \<sharp> P` `x \<sharp> M` `y \<sharp> M` `x \<sharp> xvec1` `x \<sharp> xvec2` `y \<sharp> xvec1` `y \<sharp> xvec2`
      have "\<Psi> \<rhd> P \<parallel> ([(x, y)] \<bullet> Q) \<longmapsto> M\<lparr>\<nu>*(xvec1@xvec2)\<rparr>\<langle>N\<rangle> \<prec> PQ"
        by(simp add: eqvts)
      moreover from `xvec1 \<sharp>* \<Psi>` `xvec2 \<sharp>* \<Psi>` have "(xvec1@xvec2) \<sharp>* \<Psi>" by simp
      moreover note `(xvec1@xvec2) \<sharp>* P`
      moreover from `(xvec1@xvec2) \<sharp>* Q` have "([(x, y)] \<bullet> (xvec1@xvec2)) \<sharp>* ([(x, y)] \<bullet> Q)"
        by(simp add: pt_fresh_star_bij[OF pt_name_inst, OF at_name_inst])
      with `x \<sharp> xvec1` `x \<sharp> xvec2` `y \<sharp> xvec1` `y \<sharp> xvec2` have "(xvec1@xvec2) \<sharp>* ([(x, y)] \<bullet> Q)"
        by(auto simp add: eqvts)
      moreover from `xvec1 \<sharp>* M` `xvec2 \<sharp>* M` have "(xvec1@xvec2) \<sharp>* M" by simp
      ultimately show ?case
      proof(induct rule: parOutputCases[where C=y])
        case(cPar1 P' A\<^sub>Q \<Psi>\<^sub>Q)
        from `y \<sharp> xvec1` `y \<sharp> xvec2` have "y \<sharp> (xvec1@xvec2)" by(auto simp add: fresh_list_append)
        with `\<Psi> \<otimes> \<Psi>\<^sub>Q \<rhd> P \<longmapsto>M\<lparr>\<nu>*(xvec1@xvec2)\<rparr>\<langle>N\<rangle> \<prec> P'` `(xvec1@xvec2) \<sharp>* M` `y \<sharp> P` 
             `distinct xvec1` `distinct xvec2` `xvec1 \<sharp>* xvec2` 
        have "y \<sharp> N" by(force intro: outputFreshDerivative)
        with `y \<in> supp N` have False by(simp add: fresh_def)
        thus ?case by simp
      next
        case(cPar2 Q' A\<^sub>P \<Psi>\<^sub>P)
        have FrP: "extractFrame P = \<langle>A\<^sub>P, \<Psi>\<^sub>P\<rangle>" by fact
        with `y \<sharp> P` `A\<^sub>P \<sharp>* y` have "y \<sharp> \<Psi>\<^sub>P" 
          apply(drule_tac extractFrameFresh)
          by(simp add: frameResChainFresh) (simp add: fresh_def name_list_supp)
        from `\<Psi> \<otimes> \<Psi>\<^sub>P \<rhd> ([(x, y)] \<bullet> Q) \<longmapsto>M\<lparr>\<nu>*(xvec1@xvec2)\<rparr>\<langle>N\<rangle> \<prec> Q'` `y \<in> supp N` `y \<sharp> \<Psi>` `y \<sharp> \<Psi>\<^sub>P` `y \<sharp> M` `y \<sharp> xvec1` `y \<sharp> xvec2`
        have "\<Psi> \<otimes> \<Psi>\<^sub>P \<rhd> \<lparr>\<nu>y\<rparr>(([(x, y)] \<bullet> Q)) \<longmapsto>M\<lparr>\<nu>*(xvec1@y#xvec2)\<rparr>\<langle>N\<rangle> \<prec> Q'" by(force intro: Open) 
        with `y \<sharp> Q` have "\<Psi> \<otimes> \<Psi>\<^sub>P \<rhd> \<lparr>\<nu>x\<rparr>Q \<longmapsto>M\<lparr>\<nu>*(xvec1@y#xvec2)\<rparr>\<langle>N\<rangle> \<prec> Q'"
          by(simp add: alphaRes)
        moreover from `A\<^sub>P \<sharp>* ([(x, y)] \<bullet> Q)` have "A\<^sub>P \<sharp>* \<lparr>\<nu>y\<rparr>([(x, y)] \<bullet> Q)" by(auto simp add: fresh_star_def abs_fresh)
        with `y \<sharp> Q` have "A\<^sub>P \<sharp>* \<lparr>\<nu>x\<rparr>Q" by(simp add: alphaRes)
        ultimately have "\<Psi> \<rhd> P \<parallel> (\<lparr>\<nu>x\<rparr>Q) \<longmapsto>M\<lparr>\<nu>*(xvec1@y#xvec2)\<rparr>\<langle>N\<rangle> \<prec> (P \<parallel> Q')" 
          using FrP `(xvec1@xvec2) \<sharp>* P` `A\<^sub>P \<sharp>* \<Psi>` `A\<^sub>P \<sharp>* M` `y \<sharp> P` `A\<^sub>P \<sharp>* (xvec1@xvec2)` `A\<^sub>P \<sharp>* y` `A\<^sub>P \<sharp>* N`
          by(rule_tac Par2) auto
        moreover have "(\<Psi>, P \<parallel> Q', P \<parallel> Q') \<in> Rel" by(rule C1)
        ultimately show ?case by blast
      qed
    next
      case(cRes PQ)
      from `\<Psi> \<rhd> P \<parallel> Q \<longmapsto>\<alpha> \<prec> PQ` `bn \<alpha> \<sharp>* \<Psi>`  `bn \<alpha> \<sharp>* P` `bn \<alpha> \<sharp>* Q` `bn \<alpha> \<sharp>* subject \<alpha>`
      show ?case
      proof(induct rule: parCases[where C=x])
        case(cPar1 P' A\<^sub>Q \<Psi>\<^sub>Q)
        note `\<Psi> \<otimes> \<Psi>\<^sub>Q \<rhd> P \<longmapsto>\<alpha> \<prec> P'`
        moreover with `x \<sharp> P` `x \<sharp> \<alpha>` `bn \<alpha> \<sharp>* subject \<alpha>` `distinct(bn \<alpha>)`
        have "x \<sharp> P'" by(force dest: freeFreshDerivative)
        with `extractFrame Q = \<langle>A\<^sub>Q, \<Psi>\<^sub>Q\<rangle>` have "extractFrame(\<lparr>\<nu>x\<rparr>Q) = \<langle>(x#A\<^sub>Q), \<Psi>\<^sub>Q\<rangle>"
          by simp
        moreover from `bn \<alpha> \<sharp>* Q` have "bn \<alpha> \<sharp>* (\<lparr>\<nu>x\<rparr>Q)" by(simp add: fresh_star_def abs_fresh)
        moreover from `x \<sharp> \<Psi>` `A\<^sub>Q \<sharp>* \<Psi>` have "(x#A\<^sub>Q) \<sharp>* \<Psi>" by simp
        moreover from `x \<sharp> P` `A\<^sub>Q \<sharp>* P` have "(x#A\<^sub>Q) \<sharp>* P" by simp
        moreover from `x \<sharp> \<alpha>` `A\<^sub>Q \<sharp>* \<alpha>` have "(x#A\<^sub>Q) \<sharp>* \<alpha>" by simp
        ultimately have "\<Psi> \<rhd> P \<parallel> \<lparr>\<nu>x\<rparr>Q \<longmapsto>\<alpha> \<prec> (P' \<parallel> \<lparr>\<nu>x\<rparr>Q)"
          by(rule Par1)
        moreover from `x \<sharp> P'` `x \<sharp> \<Psi>` have "(\<Psi>, \<lparr>\<nu>*[]\<rparr>(P' \<parallel> (\<lparr>\<nu>x\<rparr>Q)), \<lparr>\<nu>x\<rparr>(\<lparr>\<nu>*[]\<rparr>(P' \<parallel> Q))) \<in> Rel"
          by(rule_tac C2) auto
        ultimately show ?case
          by force
      next
        case(cPar2 Q' A\<^sub>P \<Psi>\<^sub>P)
        have FrP: "extractFrame P = \<langle>A\<^sub>P, \<Psi>\<^sub>P\<rangle>" by fact
        with `x \<sharp> P` `A\<^sub>P \<sharp>* x` have "x \<sharp> \<Psi>\<^sub>P"
          apply(drule_tac extractFrameFresh)
          by(simp add: frameResChainFresh) (simp add: fresh_def name_list_supp)
        from `\<Psi> \<otimes> \<Psi>\<^sub>P \<rhd> Q \<longmapsto>\<alpha> \<prec> Q'` `x \<sharp> \<Psi>` `x \<sharp> \<Psi>\<^sub>P` `x \<sharp> \<alpha>`
        have "\<Psi> \<otimes> \<Psi>\<^sub>P \<rhd> \<lparr>\<nu>x\<rparr>Q \<longmapsto>\<alpha> \<prec> \<lparr>\<nu>x\<rparr>Q'"
          by(rule_tac Scope) auto
        moreover note FrP `bn \<alpha> \<sharp>* P` `A\<^sub>P \<sharp>* \<Psi>`
        moreover from `A\<^sub>P \<sharp>* Q` have "A\<^sub>P \<sharp>* \<lparr>\<nu>x\<rparr>Q" by(simp add: fresh_star_def abs_fresh)
        ultimately have "\<Psi> \<rhd> P \<parallel> \<lparr>\<nu>x\<rparr>Q \<longmapsto>\<alpha> \<prec> (P \<parallel> \<lparr>\<nu>x\<rparr>Q')" using `A\<^sub>P \<sharp>* \<alpha>`
          by(rule Par2)
        moreover from `x \<sharp> P` `x \<sharp> \<Psi>` have "(\<Psi>, \<lparr>\<nu>*[]\<rparr>(P \<parallel> (\<lparr>\<nu>x\<rparr>Q')), \<lparr>\<nu>x\<rparr>(\<lparr>\<nu>*[]\<rparr>(P \<parallel> Q'))) \<in> Rel"
          by(rule_tac C2) auto
        ultimately show ?case
          by force
      next
        case(cComm1 \<Psi>\<^sub>Q M N P' A\<^sub>P \<Psi>\<^sub>P K xvec Q' A\<^sub>Q)
        have PTrans: "\<Psi> \<otimes> \<Psi>\<^sub>Q \<rhd> P \<longmapsto>M\<lparr>N\<rparr> \<prec> P'" and FrP: "extractFrame P = \<langle>A\<^sub>P, \<Psi>\<^sub>P\<rangle>" by fact+
        have QTrans: "\<Psi> \<otimes> \<Psi>\<^sub>P \<rhd> Q \<longmapsto>K\<lparr>\<nu>*xvec\<rparr>\<langle>N\<rangle> \<prec> Q'" and FrQ: "extractFrame Q = \<langle>A\<^sub>Q, \<Psi>\<^sub>Q\<rangle>" by fact+
        from FrP `x \<sharp> P` have "x \<sharp> \<langle>A\<^sub>P, \<Psi>\<^sub>P\<rangle>" by(drule_tac extractFrameFresh) simp
        with `A\<^sub>P \<sharp>* x` have "x \<sharp> \<Psi>\<^sub>P" by(simp add: frameResChainFresh) (simp add: fresh_def name_list_supp)
        from PTrans FrP `distinct A\<^sub>P` `x \<sharp> P` `A\<^sub>P \<sharp>* \<Psi>` `A\<^sub>P \<sharp>* \<Psi>\<^sub>Q` `A\<^sub>P \<sharp>* x` `A\<^sub>P \<sharp>* P` `A\<^sub>P \<sharp>* M` `A\<^sub>Q \<sharp>* P` `A\<^sub>P \<sharp>* A\<^sub>Q`
        obtain M' where MeqM': "(\<Psi> \<otimes> \<Psi>\<^sub>Q) \<otimes> \<Psi>\<^sub>P \<turnstile> M \<leftrightarrow> M'" and "x \<sharp> M'" and "A\<^sub>Q \<sharp>* M'"
          by(rule_tac B="x#A\<^sub>Q" in obtainPrefix) (assumption | force simp add: fresh_star_list_cons)+
        
        from MeqM' have MeqM': "\<Psi> \<otimes> \<Psi>\<^sub>P \<otimes> \<Psi>\<^sub>Q \<turnstile> M \<leftrightarrow> M'"
          by(metis statEqEnt Associativity Composition Commutativity)
        with `\<Psi> \<otimes> \<Psi>\<^sub>P \<otimes> \<Psi>\<^sub>Q \<turnstile> M \<leftrightarrow> K` have "\<Psi> \<otimes> \<Psi>\<^sub>P \<otimes> \<Psi>\<^sub>Q \<turnstile> K \<leftrightarrow> M'"
          by(blast intro: chanEqTrans chanEqSym)
        hence "(\<Psi> \<otimes> \<Psi>\<^sub>P) \<otimes> \<Psi>\<^sub>Q \<turnstile> K \<leftrightarrow> M'"
          by(metis statEqEnt Associativity Composition Commutativity)
        with QTrans FrQ `distinct A\<^sub>Q` have QTrans: "\<Psi> \<otimes> \<Psi>\<^sub>P \<rhd> Q \<longmapsto>M'\<lparr>\<nu>*xvec\<rparr>\<langle>N\<rangle> \<prec> Q'" using `A\<^sub>Q \<sharp>* \<Psi>` `A\<^sub>Q \<sharp>* \<Psi>\<^sub>P` `A\<^sub>Q \<sharp>* Q` `A\<^sub>Q \<sharp>* K` `A\<^sub>Q \<sharp>* M'`
          by(rule_tac outputRenameSubject) (assumption | force)+
        show ?case
        proof(case_tac "x \<in> supp N")
          note PTrans FrP
          moreover assume "x \<in> supp N"
          hence "\<Psi> \<otimes> \<Psi>\<^sub>P \<rhd> \<lparr>\<nu>x\<rparr>Q \<longmapsto>M'\<lparr>\<nu>*([]@(x#xvec))\<rparr>\<langle>N\<rangle> \<prec> Q'" using QTrans `x \<sharp> \<Psi>` `x \<sharp> \<Psi>\<^sub>P` `x \<sharp> M'` `xvec \<sharp>* x`
            by(rule_tac Open) (assumption | force simp add: fresh_list_nil)+
          hence QTrans: "\<Psi> \<otimes> \<Psi>\<^sub>P \<rhd> \<lparr>\<nu>x\<rparr>Q \<longmapsto>M'\<lparr>\<nu>*(x#xvec)\<rparr>\<langle>N\<rangle> \<prec> Q'" by simp
          moreover from `extractFrame Q = \<langle>A\<^sub>Q, \<Psi>\<^sub>Q\<rangle>` have "extractFrame(\<lparr>\<nu>x\<rparr>Q) = \<langle>(x#A\<^sub>Q), \<Psi>\<^sub>Q\<rangle>" 
            by simp
          moreover note MeqM' `A\<^sub>P \<sharp>* \<Psi>` `A\<^sub>P \<sharp>* P`
          moreover from  `A\<^sub>P \<sharp>* Q` have "A\<^sub>P \<sharp>* (\<lparr>\<nu>x\<rparr>Q)" by(simp add: fresh_star_def abs_fresh)
          moreover from `A\<^sub>P \<sharp>* A\<^sub>Q` `A\<^sub>P \<sharp>* x` have "A\<^sub>P \<sharp>* (x#A\<^sub>Q)" 
            by(simp add: fresh_star_def fresh_list_cons) (auto simp add: fresh_def name_list_supp)
          moreover from `x \<sharp> \<Psi>` `A\<^sub>Q \<sharp>* \<Psi>` have "(x#A\<^sub>Q) \<sharp>* \<Psi>" by simp
          moreover from `x \<sharp> P` `A\<^sub>Q \<sharp>* P` have "(x#A\<^sub>Q) \<sharp>* P" by simp
          moreover from `x \<sharp> M'` `A\<^sub>Q \<sharp>* M'` have "(x#A\<^sub>Q) \<sharp>* M'" by simp
          moreover from `A\<^sub>Q \<sharp>* Q` have "(x#A\<^sub>Q) \<sharp>* (\<lparr>\<nu>x\<rparr>Q)" by(simp add: fresh_star_def abs_fresh)
          moreover from `x \<sharp> P` `xvec \<sharp>* P` have "(x#xvec) \<sharp>* P" by(simp)
          ultimately have "\<Psi> \<rhd> P \<parallel> \<lparr>\<nu>x\<rparr>Q \<longmapsto>\<tau> \<prec> \<lparr>\<nu>*(x#xvec)\<rparr>(P' \<parallel> Q')" using `A\<^sub>P \<sharp>* M`
            by(rule_tac Comm1) (assumption | simp)+
          moreover have "(\<Psi>, \<lparr>\<nu>x\<rparr>(\<lparr>\<nu>*xvec\<rparr>(P' \<parallel> Q')), \<lparr>\<nu>x\<rparr>(\<lparr>\<nu>*xvec\<rparr>(P' \<parallel> Q'))) \<in> Rel" by(rule C1)
          ultimately show ?case by force
        next
          note PTrans FrP
          moreover assume "x \<notin> supp N"
          hence "x \<sharp> N" by(simp add: fresh_def)
          with QTrans `x \<sharp> \<Psi>` `x \<sharp> \<Psi>\<^sub>P` `x \<sharp> M'` `xvec \<sharp>* x`
          have QTrans: "\<Psi> \<otimes> \<Psi>\<^sub>P \<rhd> \<lparr>\<nu>x\<rparr>Q \<longmapsto>M'\<lparr>\<nu>*xvec\<rparr>\<langle>N\<rangle> \<prec> \<lparr>\<nu>x\<rparr>Q'"
            by(rule_tac Scope) (assumption | force)+
          moreover from PTrans `x \<sharp> P` `x \<sharp> N` have "x \<sharp> P'" by(rule inputFreshDerivative)
          with `extractFrame Q = \<langle>A\<^sub>Q, \<Psi>\<^sub>Q\<rangle>` have "extractFrame(\<lparr>\<nu>x\<rparr>Q) = \<langle>(x#A\<^sub>Q), \<Psi>\<^sub>Q\<rangle>"
            by simp
          moreover note MeqM' `A\<^sub>P \<sharp>* \<Psi>` `A\<^sub>P \<sharp>* P`
          moreover from  `A\<^sub>P \<sharp>* Q` have "A\<^sub>P \<sharp>* (\<lparr>\<nu>x\<rparr>Q)" by(simp add: fresh_star_def abs_fresh)
          moreover from `A\<^sub>P \<sharp>* A\<^sub>Q` `A\<^sub>P \<sharp>* x` have "A\<^sub>P \<sharp>* (x#A\<^sub>Q)" 
            by(simp add: fresh_star_def fresh_list_cons) (auto simp add: fresh_def name_list_supp)
          moreover from `x \<sharp> \<Psi>` `A\<^sub>Q \<sharp>* \<Psi>` have "(x#A\<^sub>Q) \<sharp>* \<Psi>" by simp
          moreover from `x \<sharp> P` `A\<^sub>Q \<sharp>* P` have "(x#A\<^sub>Q) \<sharp>* P" by simp
          moreover from `x \<sharp> M'` `A\<^sub>Q \<sharp>* M'` have "(x#A\<^sub>Q) \<sharp>* M'" by simp
          moreover from `A\<^sub>Q \<sharp>* Q` have "(x#A\<^sub>Q) \<sharp>* (\<lparr>\<nu>x\<rparr>Q)" by(simp add: fresh_star_def abs_fresh)
          moreover from `x \<sharp> P` `xvec \<sharp>* P` have "(x#xvec) \<sharp>* P" by(simp)
          ultimately have "\<Psi> \<rhd> P \<parallel> \<lparr>\<nu>x\<rparr>Q \<longmapsto>\<tau> \<prec> \<lparr>\<nu>*xvec\<rparr>(P' \<parallel> \<lparr>\<nu>x\<rparr>Q')" using `A\<^sub>P \<sharp>* M`
            by(rule_tac Comm1) (assumption | simp)+
          moreover from `x \<sharp> \<Psi>` `x \<sharp> P'` `xvec \<sharp>* \<Psi>` have "(\<Psi>, \<lparr>\<nu>*xvec\<rparr>(P' \<parallel> \<lparr>\<nu>x\<rparr>Q'), \<lparr>\<nu>x\<rparr>(\<lparr>\<nu>*xvec\<rparr>(P' \<parallel> Q'))) \<in> Rel" by(rule C2)
          ultimately show ?case by blast
        qed
      next
        case(cComm2 \<Psi>\<^sub>Q M xvec N P' A\<^sub>P \<Psi>\<^sub>P K Q' A\<^sub>Q)
        have PTrans: "\<Psi> \<otimes> \<Psi>\<^sub>Q \<rhd> P \<longmapsto>M\<lparr>\<nu>*xvec\<rparr>\<langle>N\<rangle> \<prec> P'" and FrP: "extractFrame P = \<langle>A\<^sub>P, \<Psi>\<^sub>P\<rangle>" by fact+
        have QTrans: "\<Psi> \<otimes> \<Psi>\<^sub>P \<rhd> Q \<longmapsto>K\<lparr>N\<rparr> \<prec> Q'" and FrQ: "extractFrame Q = \<langle>A\<^sub>Q, \<Psi>\<^sub>Q\<rangle>" by fact+
        from FrP `x \<sharp> P` have "x \<sharp> \<langle>A\<^sub>P, \<Psi>\<^sub>P\<rangle>" by(drule_tac extractFrameFresh) simp
        with `A\<^sub>P \<sharp>* x` have "x \<sharp> \<Psi>\<^sub>P" by(simp add: frameResChainFresh) (simp add: fresh_def name_list_supp)
        from PTrans FrP `distinct A\<^sub>P` `x \<sharp> P` `A\<^sub>P \<sharp>* \<Psi>` `A\<^sub>P \<sharp>* \<Psi>\<^sub>Q` `A\<^sub>P \<sharp>* x` `A\<^sub>P \<sharp>* P` `A\<^sub>P \<sharp>* M` `A\<^sub>Q \<sharp>* P` `A\<^sub>P \<sharp>* A\<^sub>Q` `xvec \<sharp>* M` `distinct xvec`
        obtain M' where MeqM': "(\<Psi> \<otimes> \<Psi>\<^sub>Q) \<otimes> \<Psi>\<^sub>P \<turnstile> M \<leftrightarrow> M'" and "x \<sharp> M'" and "A\<^sub>Q \<sharp>* M'"
          by(rule_tac B="x#A\<^sub>Q" in obtainPrefix) (assumption | force simp add: fresh_star_list_cons)+
        
        from MeqM' have MeqM': "\<Psi> \<otimes> \<Psi>\<^sub>P \<otimes> \<Psi>\<^sub>Q \<turnstile> M \<leftrightarrow> M'"
          by(metis statEqEnt Associativity Commutativity Composition)
        with `\<Psi> \<otimes> \<Psi>\<^sub>P \<otimes> \<Psi>\<^sub>Q \<turnstile> M \<leftrightarrow> K` have "\<Psi> \<otimes> \<Psi>\<^sub>P \<otimes> \<Psi>\<^sub>Q \<turnstile> K \<leftrightarrow> M'"
          by(blast intro: chanEqTrans chanEqSym)
        hence "(\<Psi> \<otimes> \<Psi>\<^sub>P) \<otimes> \<Psi>\<^sub>Q \<turnstile> K \<leftrightarrow> M'"
          by(metis statEqEnt Associativity Commutativity Composition)
        with QTrans FrQ `distinct A\<^sub>Q` have QTrans: "\<Psi> \<otimes> \<Psi>\<^sub>P \<rhd> Q \<longmapsto>M'\<lparr>N\<rparr> \<prec> Q'" using `A\<^sub>Q \<sharp>* \<Psi>` `A\<^sub>Q \<sharp>* \<Psi>\<^sub>P` `A\<^sub>Q \<sharp>* Q` `A\<^sub>Q \<sharp>* K` `A\<^sub>Q \<sharp>* M'`
          by(rule_tac inputRenameSubject) (assumption | force)+

        from PTrans `x \<sharp> P` `xvec \<sharp>* x` `distinct xvec` `xvec \<sharp>* M`
        have "x \<sharp> N" and "x \<sharp> P'" by(force intro: outputFreshDerivative)+
        from QTrans `x \<sharp> \<Psi>`  `x \<sharp> \<Psi>\<^sub>P` `x \<sharp> M'` `x \<sharp> N` have QTrans: "\<Psi> \<otimes> \<Psi>\<^sub>P \<rhd> \<lparr>\<nu>x\<rparr>Q \<longmapsto>M'\<lparr>N\<rparr> \<prec> \<lparr>\<nu>x\<rparr>Q'"
          by(rule_tac Scope) (assumption | force)+

        note PTrans FrP QTrans
        moreover with `extractFrame Q = \<langle>A\<^sub>Q, \<Psi>\<^sub>Q\<rangle>` have "extractFrame(\<lparr>\<nu>x\<rparr>Q) = \<langle>(x#A\<^sub>Q), \<Psi>\<^sub>Q\<rangle>"
          by simp
        moreover note MeqM' `A\<^sub>P \<sharp>* \<Psi>` `A\<^sub>P \<sharp>* P`
        moreover from  `A\<^sub>P \<sharp>* Q` have "A\<^sub>P \<sharp>* (\<lparr>\<nu>x\<rparr>Q)" by(simp add: fresh_star_def abs_fresh)
        moreover from `A\<^sub>P \<sharp>* A\<^sub>Q` `A\<^sub>P \<sharp>* x` have "A\<^sub>P \<sharp>* (x#A\<^sub>Q)" 
          by(simp add: fresh_star_def fresh_list_cons) (auto simp add: fresh_def name_list_supp)
        moreover from `x \<sharp> \<Psi>` `A\<^sub>Q \<sharp>* \<Psi>` have "(x#A\<^sub>Q) \<sharp>* \<Psi>" by simp
        moreover from `x \<sharp> P` `A\<^sub>Q \<sharp>* P` have "(x#A\<^sub>Q) \<sharp>* P" by simp
        moreover from `x \<sharp> M'` `A\<^sub>Q \<sharp>* M'` have "(x#A\<^sub>Q) \<sharp>* M'" by simp
        moreover from `A\<^sub>Q \<sharp>* Q` have "(x#A\<^sub>Q) \<sharp>* (\<lparr>\<nu>x\<rparr>Q)" by(simp add: fresh_star_def abs_fresh)
        moreover from `xvec \<sharp>* Q` have "(x#xvec) \<sharp>* (\<lparr>\<nu>x\<rparr>Q)" by(simp add: abs_fresh fresh_star_def)
        ultimately have "\<Psi> \<rhd> P \<parallel> \<lparr>\<nu>x\<rparr>Q \<longmapsto>\<tau> \<prec> \<lparr>\<nu>*xvec\<rparr>(P' \<parallel> \<lparr>\<nu>x\<rparr>Q')" using `A\<^sub>P \<sharp>* M`
          by(rule_tac Comm2) (assumption | simp)+
        moreover from `x \<sharp> \<Psi>` `x \<sharp> P'` `xvec \<sharp>* \<Psi>` have "(\<Psi>, \<lparr>\<nu>*xvec\<rparr>(P' \<parallel> \<lparr>\<nu>x\<rparr>Q'), \<lparr>\<nu>x\<rparr>(\<lparr>\<nu>*xvec\<rparr>(P' \<parallel> Q'))) \<in> Rel" by(rule C2)
        ultimately show ?case by blast
      qed
    qed
  qed
qed

lemma simParComm:
  fixes \<Psi>   :: 'b
  and   P   :: "('a, 'b, 'c) psi"
  and   Q   :: "('a, 'b, 'c) psi"
  and   Rel :: "('b \<times> ('a, 'b, 'c) psi \<times> ('a, 'b, 'c) psi) set"
  
  assumes "eqvt Rel"
  and     C1: "\<And>\<Psi>' R S. (\<Psi>', R \<parallel> S, S \<parallel> R) \<in> Rel"
  and     C2: "\<And>\<Psi>' R S xvec. \<lbrakk>(\<Psi>', R, S) \<in> Rel; xvec \<sharp>* \<Psi>'\<rbrakk> \<Longrightarrow> (\<Psi>', \<lparr>\<nu>*xvec\<rparr>R, \<lparr>\<nu>*xvec\<rparr>S) \<in> Rel"

  shows "\<Psi> \<rhd> P \<parallel> Q \<leadsto>[Rel] Q \<parallel> P"
using `eqvt Rel`
proof(induct rule: simI[of _ _ _ _ "()"])
  case(cSim \<alpha> PQ)
  from `bn \<alpha> \<sharp>* (P \<parallel> Q)` have "bn \<alpha> \<sharp>* Q" and "bn \<alpha> \<sharp>* P" by simp+
  with `\<Psi> \<rhd> Q \<parallel> P \<longmapsto>\<alpha> \<prec> PQ` `bn \<alpha> \<sharp>* \<Psi>` show ?case using `bn \<alpha> \<sharp>* subject \<alpha>`
  proof(induct rule: parCases[where C="()"])
    case(cPar1 Q' A\<^sub>P \<Psi>\<^sub>P)
    from `\<Psi> \<otimes> \<Psi>\<^sub>P \<rhd> Q \<longmapsto>\<alpha>\<prec> Q'` `extractFrame P = \<langle>A\<^sub>P, \<Psi>\<^sub>P\<rangle>` `bn \<alpha> \<sharp>* P` `A\<^sub>P \<sharp>* \<Psi>` `A\<^sub>P \<sharp>* Q` `A\<^sub>P \<sharp>* \<alpha>` 
    have "\<Psi> \<rhd> P \<parallel> Q \<longmapsto>\<alpha> \<prec> (P \<parallel> Q')" by(rule Par2)
    moreover have "(\<Psi>, P \<parallel> Q', Q' \<parallel> P) \<in> Rel" by(rule C1)
    ultimately show ?case by blast
  next
    case(cPar2 P' A\<^sub>Q \<Psi>\<^sub>Q)
    from `\<Psi> \<otimes> \<Psi>\<^sub>Q \<rhd> P \<longmapsto>\<alpha> \<prec> P'` `extractFrame Q = \<langle>A\<^sub>Q, \<Psi>\<^sub>Q\<rangle>` `bn \<alpha> \<sharp>* Q` `A\<^sub>Q \<sharp>* \<Psi>` `A\<^sub>Q \<sharp>* P` `A\<^sub>Q \<sharp>* \<alpha>` 
    have "\<Psi> \<rhd> P \<parallel> Q \<longmapsto>\<alpha> \<prec> (P' \<parallel> Q)" by(rule Par1)
    moreover have "(\<Psi>, P' \<parallel> Q, Q \<parallel> P') \<in> Rel" by(rule C1)
    ultimately show ?case by blast
  next
    case(cComm1 \<Psi>\<^sub>P M N Q' A\<^sub>Q \<Psi>\<^sub>Q K xvec P' A\<^sub>P)
    note `\<Psi> \<otimes> \<Psi>\<^sub>Q \<rhd> P \<longmapsto>K\<lparr>\<nu>*xvec\<rparr>\<langle>N\<rangle> \<prec> P'` `extractFrame P = \<langle>A\<^sub>P, \<Psi>\<^sub>P\<rangle>`
         `\<Psi> \<otimes> \<Psi>\<^sub>P \<rhd> Q \<longmapsto>M\<lparr>N\<rparr> \<prec> Q'` `extractFrame Q = \<langle>A\<^sub>Q, \<Psi>\<^sub>Q\<rangle>`
    moreover from `\<Psi> \<otimes> \<Psi>\<^sub>Q \<otimes> \<Psi>\<^sub>P \<turnstile> M \<leftrightarrow> K`
    have "\<Psi> \<otimes> \<Psi>\<^sub>Q \<otimes> \<Psi>\<^sub>P \<turnstile> K \<leftrightarrow> M"
      by(rule chanEqSym)
    hence "\<Psi> \<otimes> \<Psi>\<^sub>P \<otimes> \<Psi>\<^sub>Q \<turnstile> K \<leftrightarrow> M"
      by(blast intro: statEqEnt compositionSym Commutativity)
    ultimately have "\<Psi> \<rhd> P \<parallel> Q \<longmapsto>\<tau> \<prec> \<lparr>\<nu>*xvec\<rparr>(P' \<parallel> Q')"
      using `A\<^sub>P \<sharp>* \<Psi>` `A\<^sub>P \<sharp>* P` `A\<^sub>P \<sharp>* Q` `A\<^sub>Q \<sharp>* A\<^sub>P` `A\<^sub>Q \<sharp>* \<Psi>` `A\<^sub>Q \<sharp>* P` `A\<^sub>Q \<sharp>* Q` `xvec \<sharp>* Q` `A\<^sub>P \<sharp>* K` `A\<^sub>Q \<sharp>* M`
      by(rule_tac Comm2) (assumption | simp)+
    moreover have "(\<Psi>, P' \<parallel> Q', Q' \<parallel> P') \<in> Rel" by(rule C1)
    hence "(\<Psi>, \<lparr>\<nu>*xvec\<rparr>(P' \<parallel> Q'), \<lparr>\<nu>*xvec\<rparr>(Q' \<parallel> P')) \<in> Rel" using `xvec \<sharp>* \<Psi>` by(rule C2)
    ultimately show ?case by blast
  next
    case(cComm2 \<Psi>\<^sub>P M xvec N Q' A\<^sub>Q \<Psi>\<^sub>Q K P' A\<^sub>P)
    note `\<Psi> \<otimes> \<Psi>\<^sub>Q \<rhd> P \<longmapsto>K\<lparr>N\<rparr> \<prec> P'` `extractFrame P = \<langle>A\<^sub>P, \<Psi>\<^sub>P\<rangle>`
         `\<Psi> \<otimes> \<Psi>\<^sub>P \<rhd> Q \<longmapsto>M\<lparr>\<nu>*xvec\<rparr>\<langle>N\<rangle> \<prec> Q'` `extractFrame Q = \<langle>A\<^sub>Q, \<Psi>\<^sub>Q\<rangle>`
    moreover from `\<Psi> \<otimes> \<Psi>\<^sub>Q \<otimes> \<Psi>\<^sub>P \<turnstile> M \<leftrightarrow> K`
    have "\<Psi> \<otimes> \<Psi>\<^sub>Q \<otimes> \<Psi>\<^sub>P \<turnstile> K \<leftrightarrow> M"
      by(rule chanEqSym)
    hence "\<Psi> \<otimes> \<Psi>\<^sub>P \<otimes> \<Psi>\<^sub>Q \<turnstile> K \<leftrightarrow> M"
      by(blast intro: statEqEnt compositionSym Commutativity)
    ultimately have "\<Psi> \<rhd> P \<parallel> Q \<longmapsto>\<tau> \<prec> \<lparr>\<nu>*xvec\<rparr>(P' \<parallel> Q')"
      using `A\<^sub>P \<sharp>* \<Psi>` `A\<^sub>P \<sharp>* P` `A\<^sub>P \<sharp>* Q` `A\<^sub>Q \<sharp>* A\<^sub>P` `A\<^sub>Q \<sharp>* \<Psi>` `A\<^sub>Q \<sharp>* P` `A\<^sub>Q \<sharp>* Q` `xvec \<sharp>* P` `A\<^sub>P \<sharp>* K` `A\<^sub>Q \<sharp>* M`
      by(rule_tac Comm1) (assumption | simp add: freshChainSym)+
    moreover have "(\<Psi>, P' \<parallel> Q', Q' \<parallel> P') \<in> Rel" by(rule C1)
    hence "(\<Psi>, \<lparr>\<nu>*xvec\<rparr>(P' \<parallel> Q'), \<lparr>\<nu>*xvec\<rparr>(Q' \<parallel> P')) \<in> Rel" using `xvec \<sharp>* \<Psi>` by(rule C2)
    ultimately show ?case by blast
  qed
qed

lemma bangExtLeft:
  fixes \<Psi> :: 'b
  and   P :: "('a, 'b, 'c) psi"

  assumes "guarded P"
  and     "\<And>\<Psi>' Q. (\<Psi>', Q, Q) \<in> Rel"

  shows "\<Psi> \<rhd> !P \<leadsto>[Rel] P \<parallel> !P"
using assms
by(auto simp add: simulation_def dest: Bang)

lemma bangExtRight:
  fixes \<Psi> :: 'b
  and   P :: "('a, 'b, 'c) psi"

  assumes C1: "\<And>\<Psi>' Q. (\<Psi>', Q, Q) \<in> Rel"

  shows "\<Psi> \<rhd> P \<parallel> !P \<leadsto>[Rel] !P"
proof(auto simp add: simulation_def)
  fix \<alpha> P'
  assume "\<Psi> \<rhd> !P \<longmapsto>\<alpha> \<prec> P'"
  hence "\<Psi> \<rhd> P \<parallel> !P \<longmapsto>\<alpha> \<prec> P'"
    apply -
    by(ind_cases "\<Psi> \<rhd> !P \<longmapsto>\<alpha> \<prec> P'") (auto simp add: psi.inject)
  moreover have "(\<Psi>, P', P') \<in> Rel" by(rule C1)
  ultimately show "\<exists>P''. \<Psi> \<rhd> P \<parallel> !P \<longmapsto>\<alpha> \<prec> P'' \<and> (\<Psi>, P'', P') \<in> Rel"
    by blast
qed

end

end