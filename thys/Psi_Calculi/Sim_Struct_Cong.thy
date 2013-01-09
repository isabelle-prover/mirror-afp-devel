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
    case(cPar1 P' A\<^isub>Q\<^isub>R \<Psi>\<^isub>Q\<^isub>R)
    from `A\<^isub>Q\<^isub>R \<sharp>* (\<Psi>, P, Q, R, \<alpha>)` have "A\<^isub>Q\<^isub>R \<sharp>* Q" and  "A\<^isub>Q\<^isub>R \<sharp>* R"
      by simp+
    with `extractFrame(Q \<parallel> R) = \<langle>A\<^isub>Q\<^isub>R, \<Psi>\<^isub>Q\<^isub>R\<rangle>` `distinct A\<^isub>Q\<^isub>R`
    obtain A\<^isub>Q \<Psi>\<^isub>Q A\<^isub>R \<Psi>\<^isub>R where "A\<^isub>Q\<^isub>R = A\<^isub>Q@A\<^isub>R" and "\<Psi>\<^isub>Q\<^isub>R = \<Psi>\<^isub>Q \<otimes> \<Psi>\<^isub>R" and FrQ: "extractFrame Q = \<langle>A\<^isub>Q, \<Psi>\<^isub>Q\<rangle>" and  FrR: "extractFrame R = \<langle>A\<^isub>R, \<Psi>\<^isub>R\<rangle>"
                           and "A\<^isub>Q \<sharp>* \<Psi>\<^isub>R" and "A\<^isub>R \<sharp>* \<Psi>\<^isub>Q"
      by(rule_tac mergeFrameE) (auto dest: extractFrameFreshChain)

    from `A\<^isub>Q\<^isub>R = A\<^isub>Q@A\<^isub>R` `A\<^isub>Q\<^isub>R \<sharp>* \<Psi>` `A\<^isub>Q\<^isub>R \<sharp>* P` `A\<^isub>Q\<^isub>R \<sharp>* Q` `A\<^isub>Q\<^isub>R \<sharp>* \<alpha>`
    have "A\<^isub>Q \<sharp>* \<Psi>" and "A\<^isub>R \<sharp>* \<Psi>" and "A\<^isub>Q \<sharp>* P" and "A\<^isub>R \<sharp>* P" and "A\<^isub>Q \<sharp>* Q" and "A\<^isub>R \<sharp>* Q" and "A\<^isub>Q \<sharp>* \<alpha>" and "A\<^isub>R \<sharp>* \<alpha>"
      by simp+

    from `\<Psi> \<otimes> \<Psi>\<^isub>Q\<^isub>R \<rhd> P \<longmapsto>\<alpha> \<prec> P'` `\<Psi>\<^isub>Q\<^isub>R = \<Psi>\<^isub>Q \<otimes> \<Psi>\<^isub>R` have "(\<Psi> \<otimes> \<Psi>\<^isub>R) \<otimes> \<Psi>\<^isub>Q \<rhd> P \<longmapsto>\<alpha> \<prec> P'"
      by(metis statEqTransition Associativity Commutativity Composition)
    hence "\<Psi> \<otimes> \<Psi>\<^isub>R \<rhd> P \<parallel> Q \<longmapsto>\<alpha> \<prec> (P' \<parallel> Q)" using FrQ `bn \<alpha> \<sharp>* Q` `A\<^isub>Q \<sharp>* \<Psi>` `A\<^isub>Q \<sharp>* \<Psi>\<^isub>R` `A\<^isub>Q \<sharp>* P` `A\<^isub>Q \<sharp>* \<alpha>`
      by(rule_tac Par1) auto
    hence "\<Psi> \<rhd> (P \<parallel> Q) \<parallel> R \<longmapsto>\<alpha> \<prec> ((P' \<parallel> Q) \<parallel> R)" using FrR `bn \<alpha> \<sharp>* R` `A\<^isub>R \<sharp>* \<Psi>` `A\<^isub>R \<sharp>* P` `A\<^isub>R \<sharp>* Q` `A\<^isub>R \<sharp>* \<alpha>`
      by(rule_tac Par1) auto
    moreover have "(\<Psi>, (P' \<parallel> Q) \<parallel> R, P' \<parallel> (Q \<parallel> R)) \<in> Rel" by(rule C1)
    ultimately show ?case by blast
  next
    case(cPar2 QR A\<^isub>P \<Psi>\<^isub>P)
    from `A\<^isub>P \<sharp>* (\<Psi>, P, Q, R, \<alpha>)` have "A\<^isub>P \<sharp>* Q" and "A\<^isub>P \<sharp>* R" and "A\<^isub>P \<sharp>* \<alpha>"
      by simp+
    have FrP: "extractFrame P = \<langle>A\<^isub>P, \<Psi>\<^isub>P\<rangle>" by fact
    with `bn \<alpha> \<sharp>* P` `A\<^isub>P \<sharp>* \<alpha>` have "bn \<alpha> \<sharp>* \<Psi>\<^isub>P" by(auto dest: extractFrameFreshChain)
    with `bn \<alpha> \<sharp>* \<Psi>` have "bn \<alpha> \<sharp>* (\<Psi> \<otimes> \<Psi>\<^isub>P)" by force
    with `\<Psi> \<otimes> \<Psi>\<^isub>P \<rhd> Q \<parallel> R \<longmapsto>\<alpha> \<prec> QR`
    show ?case using `bn \<alpha> \<sharp>* Q` `bn \<alpha> \<sharp>* R` `bn \<alpha> \<sharp>* subject \<alpha>` `A\<^isub>P \<sharp>* Q` `A\<^isub>P \<sharp>* R`
    proof(induct rule: parCasesSubject[where C = "(A\<^isub>P, \<Psi>\<^isub>P, P, Q, R, \<Psi>)"])
      case(cPar1 Q' A\<^isub>R \<Psi>\<^isub>R)
      from `A\<^isub>R \<sharp>* (A\<^isub>P, \<Psi>\<^isub>P, P, Q, R, \<Psi>)` have "A\<^isub>R \<sharp>* A\<^isub>P" and "A\<^isub>R \<sharp>* P" and "A\<^isub>R \<sharp>* Q" and "A\<^isub>R \<sharp>* \<Psi>\<^isub>P" and "A\<^isub>R \<sharp>* \<Psi>"
        by simp+
      from `A\<^isub>P \<sharp>* R` `extractFrame R = \<langle>A\<^isub>R, \<Psi>\<^isub>R\<rangle>` `A\<^isub>R \<sharp>* A\<^isub>P` have "A\<^isub>P \<sharp>* \<Psi>\<^isub>R"
        by(drule_tac extractFrameFreshChain) auto
      from `(\<Psi> \<otimes> \<Psi>\<^isub>P) \<otimes> \<Psi>\<^isub>R \<rhd> Q \<longmapsto>\<alpha> \<prec> Q'` have "(\<Psi> \<otimes> \<Psi>\<^isub>R) \<otimes> \<Psi>\<^isub>P \<rhd> Q \<longmapsto>\<alpha> \<prec> Q'" 
        by(metis statEqTransition Associativity Commutativity Composition)
      hence "\<Psi> \<otimes> \<Psi>\<^isub>R \<rhd> P \<parallel> Q \<longmapsto>\<alpha> \<prec> (P \<parallel> Q')"
        using FrP `bn \<alpha> \<sharp>* P` `A\<^isub>P \<sharp>* \<Psi>` `A\<^isub>P \<sharp>* \<Psi>\<^isub>R` `A\<^isub>P \<sharp>* Q` `A\<^isub>P \<sharp>* \<alpha>`
        by(rule_tac Par2) (assumption | force)+
      hence "\<Psi> \<rhd> (P \<parallel> Q) \<parallel> R \<longmapsto>\<alpha> \<prec> ((P \<parallel> Q') \<parallel> R)"
        using `extractFrame R = \<langle>A\<^isub>R, \<Psi>\<^isub>R\<rangle>` `bn \<alpha> \<sharp>* R` `A\<^isub>R \<sharp>* \<Psi>` `A\<^isub>R \<sharp>* P` `A\<^isub>R \<sharp>* Q` `A\<^isub>R \<sharp>* \<alpha>`
        by(rule_tac Par1) (assumption | simp)+
      moreover have "(\<Psi>, (P \<parallel> Q') \<parallel> R, P \<parallel> (Q' \<parallel> R)) \<in> Rel" by(rule C1)
      ultimately show ?case by blast
    next
      case(cPar2 R' A\<^isub>Q \<Psi>\<^isub>Q)
      from `A\<^isub>Q \<sharp>* (A\<^isub>P, \<Psi>\<^isub>P, P, Q, R, \<Psi>)` have "A\<^isub>Q \<sharp>* A\<^isub>P" and "A\<^isub>Q \<sharp>* R" and "A\<^isub>Q \<sharp>* \<Psi>\<^isub>P" and "A\<^isub>Q \<sharp>* \<Psi>"
        by simp+
      have FrQ: "extractFrame Q = \<langle>A\<^isub>Q, \<Psi>\<^isub>Q\<rangle>" by fact
      from `A\<^isub>P \<sharp>* Q` FrQ `A\<^isub>Q \<sharp>* A\<^isub>P` have "A\<^isub>P \<sharp>* \<Psi>\<^isub>Q"
        by(drule_tac extractFrameFreshChain) auto
      from `(\<Psi> \<otimes> \<Psi>\<^isub>P) \<otimes> \<Psi>\<^isub>Q \<rhd> R \<longmapsto>\<alpha> \<prec> R'`
      have "\<Psi> \<otimes> (\<Psi>\<^isub>P \<otimes> \<Psi>\<^isub>Q) \<rhd> R \<longmapsto>\<alpha> \<prec> R'"
        by(blast intro: statEqTransition Associativity)
      moreover from FrP FrQ `A\<^isub>Q \<sharp>* A\<^isub>P` `A\<^isub>P \<sharp>* \<Psi>\<^isub>Q`  `A\<^isub>Q \<sharp>* \<Psi>\<^isub>P` 
      have "extractFrame(P \<parallel> Q) = \<langle>(A\<^isub>P@A\<^isub>Q), \<Psi>\<^isub>P \<otimes> \<Psi>\<^isub>Q\<rangle> " by simp
      moreover from `bn \<alpha> \<sharp>* P` `bn \<alpha> \<sharp>* Q` have "bn \<alpha> \<sharp>* (P \<parallel> Q)" by simp
      moreover from `A\<^isub>P \<sharp>* \<Psi>` `A\<^isub>Q \<sharp>* \<Psi>` have "(A\<^isub>P@A\<^isub>Q) \<sharp>* \<Psi>" by simp
      moreover from `A\<^isub>P \<sharp>* R` `A\<^isub>Q \<sharp>* R` have "(A\<^isub>P@A\<^isub>Q) \<sharp>* R" by simp
      moreover from `A\<^isub>P \<sharp>* \<alpha>` `A\<^isub>Q \<sharp>* \<alpha>` have "(A\<^isub>P@A\<^isub>Q) \<sharp>* \<alpha>" by simp
      ultimately have "\<Psi> \<rhd> (P \<parallel> Q) \<parallel> R \<longmapsto>\<alpha> \<prec> ((P \<parallel> Q) \<parallel> R')"
        by(rule Par2) 
      moreover have "(\<Psi>, (P \<parallel> Q) \<parallel> R', P \<parallel> (Q \<parallel> R')) \<in> Rel" by(rule C1)
      ultimately show ?case by blast
    next
      case(cComm1 \<Psi>\<^isub>R M N Q' A\<^isub>Q \<Psi>\<^isub>Q K xvec R' A\<^isub>R) 
      from `A\<^isub>Q \<sharp>* (A\<^isub>P, \<Psi>\<^isub>P, P, Q, R, \<Psi>)`
      have "A\<^isub>Q \<sharp>* P" and "A\<^isub>Q \<sharp>* Q" and "A\<^isub>Q \<sharp>* R" and "A\<^isub>Q \<sharp>* A\<^isub>P" and "A\<^isub>Q \<sharp>* \<Psi>\<^isub>P"  and "A\<^isub>Q \<sharp>* \<Psi>" by simp+
      from `A\<^isub>R \<sharp>* (A\<^isub>P, \<Psi>\<^isub>P, P, Q, R, \<Psi>)` have "A\<^isub>R \<sharp>* P" and "A\<^isub>R \<sharp>* Q" and "A\<^isub>R \<sharp>* R" and "A\<^isub>R \<sharp>* A\<^isub>P"  and "A\<^isub>R \<sharp>* \<Psi>" by simp+
      from `xvec \<sharp>* (A\<^isub>P,  \<Psi>\<^isub>P, P, Q, R, \<Psi>)` have "xvec \<sharp>* A\<^isub>P" and "xvec \<sharp>* P" and "xvec \<sharp>* Q" and "xvec \<sharp>* \<Psi>" by simp+

      have FrQ: "extractFrame Q = \<langle>A\<^isub>Q, \<Psi>\<^isub>Q\<rangle>" by fact
      with `A\<^isub>P \<sharp>* Q` `A\<^isub>Q \<sharp>* A\<^isub>P` have "A\<^isub>P \<sharp>* \<Psi>\<^isub>Q"
        by(drule_tac extractFrameFreshChain) auto
      have FrR: "extractFrame R = \<langle>A\<^isub>R, \<Psi>\<^isub>R\<rangle>" by fact
      with `A\<^isub>P \<sharp>* R` `A\<^isub>R \<sharp>* A\<^isub>P` have "A\<^isub>P \<sharp>* \<Psi>\<^isub>R"
        by(drule_tac extractFrameFreshChain) auto
      from `(\<Psi> \<otimes> \<Psi>\<^isub>P) \<otimes> \<Psi>\<^isub>Q \<rhd> R \<longmapsto>K\<lparr>\<nu>*xvec\<rparr>\<langle>N\<rangle> \<prec> R'` `A\<^isub>P \<sharp>* R` `xvec \<sharp>* A\<^isub>P` `xvec \<sharp>* K` `distinct xvec` have "A\<^isub>P \<sharp>* N" 
        by(rule_tac outputFreshChainDerivative) auto

      from `(\<Psi> \<otimes> \<Psi>\<^isub>P) \<otimes> \<Psi>\<^isub>R \<rhd> Q \<longmapsto>M\<lparr>N\<rparr> \<prec> Q'` have "(\<Psi> \<otimes> \<Psi>\<^isub>R) \<otimes> \<Psi>\<^isub>P \<rhd> Q \<longmapsto>M\<lparr>N\<rparr> \<prec> Q'"
        by(metis statEqTransition Associativity Commutativity Composition)
      hence "\<Psi> \<otimes> \<Psi>\<^isub>R \<rhd> P \<parallel> Q \<longmapsto>M\<lparr>N\<rparr> \<prec> (P \<parallel> Q')" using FrP `A\<^isub>P \<sharp>* \<Psi>` `A\<^isub>P \<sharp>* \<Psi>\<^isub>R` `A\<^isub>P \<sharp>* Q` `A\<^isub>P \<sharp>* M` `A\<^isub>P \<sharp>* N`
        by(rule_tac Par2) auto
      moreover from FrP FrQ `A\<^isub>P \<sharp>* \<Psi>\<^isub>Q` `A\<^isub>Q \<sharp>* A\<^isub>P` `A\<^isub>Q \<sharp>* \<Psi>\<^isub>P` have "extractFrame(P \<parallel> Q) = \<langle>(A\<^isub>P@A\<^isub>Q), \<Psi>\<^isub>P \<otimes> \<Psi>\<^isub>Q\<rangle>"
        by simp
      moreover from  `(\<Psi> \<otimes> \<Psi>\<^isub>P) \<otimes> \<Psi>\<^isub>Q \<rhd> R \<longmapsto>K\<lparr>\<nu>*xvec\<rparr>\<langle>N\<rangle> \<prec> R'` have "\<Psi> \<otimes> \<Psi>\<^isub>P \<otimes> \<Psi>\<^isub>Q \<rhd> R \<longmapsto>K\<lparr>\<nu>*xvec\<rparr>\<langle>N\<rangle> \<prec> R'"
        by(metis statEqTransition Associativity)
      moreover note `extractFrame R = \<langle>A\<^isub>R, \<Psi>\<^isub>R\<rangle>`
      moreover from `(\<Psi> \<otimes> \<Psi>\<^isub>P) \<otimes> \<Psi>\<^isub>Q \<otimes> \<Psi>\<^isub>R \<turnstile> M \<leftrightarrow> K` have "\<Psi> \<otimes> (\<Psi>\<^isub>P \<otimes> \<Psi>\<^isub>Q) \<otimes> \<Psi>\<^isub>R \<turnstile> M \<leftrightarrow> K"
        by(metis statEqEnt Associativity Commutativity Composition)
      ultimately have "\<Psi> \<rhd> (P \<parallel> Q) \<parallel> R \<longmapsto>\<tau> \<prec> \<lparr>\<nu>*xvec\<rparr>((P \<parallel> Q') \<parallel> R')"
        using `A\<^isub>P \<sharp>* \<Psi>` `A\<^isub>Q \<sharp>* \<Psi>` `A\<^isub>R \<sharp>* \<Psi>` `A\<^isub>P \<sharp>* P` `A\<^isub>Q \<sharp>* P` `A\<^isub>R \<sharp>* P` `A\<^isub>P \<sharp>* Q` `A\<^isub>Q \<sharp>* Q` `A\<^isub>R \<sharp>* Q` `A\<^isub>P \<sharp>* R` `A\<^isub>Q \<sharp>* R` `A\<^isub>R \<sharp>* R`
              `A\<^isub>P \<sharp>* M` `A\<^isub>Q \<sharp>* M` `A\<^isub>R \<sharp>* K` `A\<^isub>R \<sharp>* A\<^isub>P` `A\<^isub>Q \<sharp>* A\<^isub>R` `xvec \<sharp>* P` `xvec \<sharp>* Q`
        by(rule_tac Comm1) (assumption | simp)+
      moreover from `xvec \<sharp>* \<Psi>` `xvec \<sharp>* P` have "(\<Psi>, \<lparr>\<nu>*xvec\<rparr>((P \<parallel> Q') \<parallel> R'), P \<parallel> (\<lparr>\<nu>*xvec\<rparr>(Q' \<parallel> R'))) \<in> Rel"
        by(rule C2)
      ultimately show ?case by blast
    next
      case(cComm2 \<Psi>\<^isub>R M xvec N Q' A\<^isub>Q \<Psi>\<^isub>Q K R' A\<^isub>R) 
      from `A\<^isub>Q \<sharp>* (A\<^isub>P,  \<Psi>\<^isub>P, P, Q, R, \<Psi>)`
      have "A\<^isub>Q \<sharp>* P" and "A\<^isub>Q \<sharp>* Q" and "A\<^isub>Q \<sharp>* R" and "A\<^isub>Q \<sharp>* A\<^isub>P" and "A\<^isub>Q \<sharp>* \<Psi>" and "A\<^isub>Q \<sharp>* \<Psi>\<^isub>P" by simp+
      from `A\<^isub>R \<sharp>* (A\<^isub>P,  \<Psi>\<^isub>P, P, Q, R, \<Psi>)` have "A\<^isub>R \<sharp>* P" and "A\<^isub>R \<sharp>* Q" and "A\<^isub>R \<sharp>* R" and "A\<^isub>R \<sharp>* A\<^isub>P"and "A\<^isub>R \<sharp>* \<Psi>" by simp+
      from `xvec \<sharp>* (A\<^isub>P,  \<Psi>\<^isub>P, P, Q, R, \<Psi>)` have "xvec \<sharp>* A\<^isub>P" and "xvec \<sharp>* P" and "xvec \<sharp>* Q" and "xvec \<sharp>* \<Psi>" by simp+

      have FrQ: "extractFrame Q = \<langle>A\<^isub>Q, \<Psi>\<^isub>Q\<rangle>" by fact
      with `A\<^isub>P \<sharp>* Q` `A\<^isub>Q \<sharp>* A\<^isub>P` have "A\<^isub>P \<sharp>* \<Psi>\<^isub>Q"
        by(drule_tac extractFrameFreshChain) auto
      have FrR: "extractFrame R = \<langle>A\<^isub>R, \<Psi>\<^isub>R\<rangle>" by fact
      with `A\<^isub>P \<sharp>* R` `A\<^isub>R \<sharp>* A\<^isub>P` have "A\<^isub>P \<sharp>* \<Psi>\<^isub>R"
        by(drule_tac extractFrameFreshChain) auto

      from `(\<Psi> \<otimes> \<Psi>\<^isub>P) \<otimes> \<Psi>\<^isub>R \<rhd> Q \<longmapsto>M\<lparr>\<nu>*xvec\<rparr>\<langle>N\<rangle> \<prec> Q'` `A\<^isub>P \<sharp>* Q` `xvec \<sharp>* A\<^isub>P` `xvec \<sharp>* M` `distinct xvec` have "A\<^isub>P \<sharp>* N" 
        by(rule_tac outputFreshChainDerivative) auto

      from `(\<Psi> \<otimes> \<Psi>\<^isub>P) \<otimes> \<Psi>\<^isub>R \<rhd> Q \<longmapsto>M\<lparr>\<nu>*xvec\<rparr>\<langle>N\<rangle> \<prec> Q'` have "(\<Psi> \<otimes> \<Psi>\<^isub>R) \<otimes> \<Psi>\<^isub>P \<rhd> Q \<longmapsto>M\<lparr>\<nu>*xvec\<rparr>\<langle>N\<rangle> \<prec> Q'"
        by(metis statEqTransition Associativity Commutativity Composition)
      hence "\<Psi> \<otimes> \<Psi>\<^isub>R \<rhd> P \<parallel> Q \<longmapsto>M\<lparr>\<nu>*xvec\<rparr>\<langle>N\<rangle> \<prec> (P \<parallel> Q')" using FrP `A\<^isub>P \<sharp>* \<Psi>` `A\<^isub>P \<sharp>* \<Psi>\<^isub>R` `A\<^isub>P \<sharp>* Q` `A\<^isub>P \<sharp>* M` `A\<^isub>P \<sharp>* N` `xvec \<sharp>* P` `xvec \<sharp>* A\<^isub>P`
        by(rule_tac Par2) auto
      moreover from FrP FrQ `A\<^isub>P \<sharp>* \<Psi>\<^isub>Q` `A\<^isub>Q \<sharp>* A\<^isub>P` `A\<^isub>Q \<sharp>* \<Psi>\<^isub>P` have "extractFrame(P \<parallel> Q) = \<langle>(A\<^isub>P@A\<^isub>Q), \<Psi>\<^isub>P \<otimes> \<Psi>\<^isub>Q\<rangle>"
        by simp+
      moreover from  `(\<Psi> \<otimes> \<Psi>\<^isub>P) \<otimes> \<Psi>\<^isub>Q \<rhd> R \<longmapsto>K\<lparr>N\<rparr> \<prec> R'` have "\<Psi> \<otimes> \<Psi>\<^isub>P \<otimes> \<Psi>\<^isub>Q \<rhd> R \<longmapsto>K\<lparr>N\<rparr> \<prec> R'"
        by(metis statEqTransition Associativity)
      moreover note `extractFrame R = \<langle>A\<^isub>R, \<Psi>\<^isub>R\<rangle>`
      moreover from `(\<Psi> \<otimes> \<Psi>\<^isub>P) \<otimes> \<Psi>\<^isub>Q \<otimes> \<Psi>\<^isub>R \<turnstile> M \<leftrightarrow> K` have "\<Psi> \<otimes> (\<Psi>\<^isub>P \<otimes> \<Psi>\<^isub>Q) \<otimes> \<Psi>\<^isub>R \<turnstile> M \<leftrightarrow> K"
        by(metis statEqEnt Associativity Commutativity Composition)
      ultimately have "\<Psi> \<rhd> (P \<parallel> Q) \<parallel> R \<longmapsto>\<tau> \<prec> \<lparr>\<nu>*xvec\<rparr>((P \<parallel> Q') \<parallel> R')"
        using `A\<^isub>P \<sharp>* \<Psi>` `A\<^isub>Q \<sharp>* \<Psi>` `A\<^isub>R \<sharp>* \<Psi>` `A\<^isub>P \<sharp>* P` `A\<^isub>Q \<sharp>* P` `A\<^isub>R \<sharp>* P` `A\<^isub>P \<sharp>* Q` `A\<^isub>Q \<sharp>* Q` `A\<^isub>R \<sharp>* Q` `A\<^isub>P \<sharp>* R` `A\<^isub>Q \<sharp>* R` `A\<^isub>R \<sharp>* R`
              `A\<^isub>P \<sharp>* M` `A\<^isub>Q \<sharp>* M` `A\<^isub>R \<sharp>* K` `A\<^isub>R \<sharp>* A\<^isub>P` `A\<^isub>Q \<sharp>* A\<^isub>R` `xvec \<sharp>* R`
        by(rule_tac Comm2) (assumption | simp)+
      moreover from `xvec \<sharp>* \<Psi>` `xvec \<sharp>* P` have "(\<Psi>, \<lparr>\<nu>*xvec\<rparr>((P \<parallel> Q') \<parallel> R'), P \<parallel> (\<lparr>\<nu>*xvec\<rparr>(Q' \<parallel> R'))) \<in> Rel"
        by(rule C2)
      ultimately show ?case by blast
    qed
  next
    case(cComm1 \<Psi>\<^isub>Q\<^isub>R M N P' A\<^isub>P \<Psi>\<^isub>P K xvec QR' A\<^isub>Q\<^isub>R)
    from `xvec \<sharp>* (\<Psi>, P, Q, R, \<alpha>)` have "xvec \<sharp>* Q" and "xvec \<sharp>* R" by simp+
    from `A\<^isub>Q\<^isub>R \<sharp>* (\<Psi>, P, Q, R, \<alpha>)` have "A\<^isub>Q\<^isub>R \<sharp>* Q" and "A\<^isub>Q\<^isub>R \<sharp>* R" and "A\<^isub>Q\<^isub>R \<sharp>* \<Psi>" by simp+
    from `A\<^isub>P \<sharp>* (Q \<parallel> R)` have "A\<^isub>P \<sharp>* Q" and "A\<^isub>P \<sharp>* R" by simp+
    have PTrans: "\<Psi> \<otimes> \<Psi>\<^isub>Q\<^isub>R \<rhd> P \<longmapsto>M\<lparr>N\<rparr> \<prec> P'" and FrP: "extractFrame P = \<langle>A\<^isub>P, \<Psi>\<^isub>P\<rangle>" and MeqK: "\<Psi> \<otimes> \<Psi>\<^isub>P \<otimes> \<Psi>\<^isub>Q\<^isub>R \<turnstile> M \<leftrightarrow> K" by fact+
    note `\<Psi> \<otimes> \<Psi>\<^isub>P \<rhd> Q \<parallel> R \<longmapsto>K\<lparr>\<nu>*xvec\<rparr>\<langle>N\<rangle> \<prec> QR'`  
    moreover from `xvec \<sharp>* \<Psi>` `xvec \<sharp>* \<Psi>\<^isub>P` have "xvec \<sharp>* (\<Psi> \<otimes> \<Psi>\<^isub>P)" by force
    moreover note `xvec \<sharp>* Q``xvec \<sharp>* R` `xvec \<sharp>* K`
         `extractFrame(Q \<parallel> R) = \<langle>A\<^isub>Q\<^isub>R, \<Psi>\<^isub>Q\<^isub>R\<rangle>` `distinct A\<^isub>Q\<^isub>R` 
    moreover from `A\<^isub>Q\<^isub>R \<sharp>* \<Psi>` `A\<^isub>Q\<^isub>R \<sharp>* \<Psi>\<^isub>P` have "A\<^isub>Q\<^isub>R \<sharp>* (\<Psi> \<otimes> \<Psi>\<^isub>P)" by force
    ultimately show ?case using `A\<^isub>Q\<^isub>R \<sharp>* Q` `A\<^isub>Q\<^isub>R \<sharp>* R` `A\<^isub>Q\<^isub>R \<sharp>* K`
    proof(induct rule: parCasesOutputFrame)
      case(cPar1 Q' A\<^isub>Q \<Psi>\<^isub>Q A\<^isub>R \<Psi>\<^isub>R)
      have Aeq: "A\<^isub>Q\<^isub>R = A\<^isub>Q@A\<^isub>R" and \<Psi>eq: "\<Psi>\<^isub>Q\<^isub>R = \<Psi>\<^isub>Q \<otimes> \<Psi>\<^isub>R" by fact+
      from PTrans \<Psi>eq have "(\<Psi> \<otimes> \<Psi>\<^isub>R) \<otimes> \<Psi>\<^isub>Q \<rhd> P \<longmapsto>M\<lparr>N\<rparr> \<prec> P'"
        by(metis statEqTransition Associativity Commutativity Composition)
      moreover note FrP
      moreover from `(\<Psi> \<otimes> \<Psi>\<^isub>P) \<otimes> \<Psi>\<^isub>R \<rhd> Q \<longmapsto>K\<lparr>\<nu>*xvec\<rparr>\<langle>N\<rangle> \<prec> Q'` have "(\<Psi> \<otimes> \<Psi>\<^isub>R) \<otimes> \<Psi>\<^isub>P \<rhd> Q \<longmapsto>K\<lparr>\<nu>*xvec\<rparr>\<langle>N\<rangle> \<prec> Q'"
        by(metis statEqTransition Associativity Commutativity Composition)
      moreover note `extractFrame Q = \<langle>A\<^isub>Q, \<Psi>\<^isub>Q\<rangle>`
      moreover from MeqK \<Psi>eq have "(\<Psi> \<otimes> \<Psi>\<^isub>R) \<otimes> \<Psi>\<^isub>P \<otimes> \<Psi>\<^isub>Q \<turnstile> M \<leftrightarrow> K"
        by(metis statEqEnt Associativity Commutativity Composition)
      moreover from `A\<^isub>P \<sharp>* R` `A\<^isub>P \<sharp>* A\<^isub>Q\<^isub>R` Aeq `extractFrame R = \<langle>A\<^isub>R, \<Psi>\<^isub>R\<rangle>` have "A\<^isub>P \<sharp>* A\<^isub>Q" and "A\<^isub>P \<sharp>* \<Psi>\<^isub>R"
        by(auto dest:  extractFrameFreshChain)
      moreover from `A\<^isub>Q\<^isub>R \<sharp>* P` `A\<^isub>Q\<^isub>R \<sharp>* \<Psi>` Aeq have "A\<^isub>Q \<sharp>* P" and "A\<^isub>Q \<sharp>* \<Psi>" by simp+
      ultimately have "\<Psi> \<otimes> \<Psi>\<^isub>R \<rhd> P \<parallel> Q \<longmapsto>\<tau> \<prec> \<lparr>\<nu>*xvec\<rparr>(P' \<parallel> Q')"
        using `A\<^isub>P \<sharp>* \<Psi>` `A\<^isub>P \<sharp>* P` `A\<^isub>P \<sharp>* Q` `A\<^isub>P \<sharp>* M` `A\<^isub>P \<sharp>* A\<^isub>Q` `A\<^isub>Q \<sharp>* \<Psi>` `A\<^isub>Q \<sharp>* \<Psi>\<^isub>R` `A\<^isub>Q \<sharp>* P` `A\<^isub>Q \<sharp>* Q` `A\<^isub>Q \<sharp>* K` `xvec \<sharp>* P`
        by(rule_tac Comm1) (assumption | force)+
      moreover from `A\<^isub>Q\<^isub>R \<sharp>* \<Psi>` Aeq have "A\<^isub>R \<sharp>* \<Psi>" by simp
      moreover from `A\<^isub>Q\<^isub>R \<sharp>* P` Aeq have "A\<^isub>R \<sharp>* P" by simp
      ultimately have "\<Psi> \<rhd> (P \<parallel> Q) \<parallel> R \<longmapsto>\<tau> \<prec> (\<lparr>\<nu>*xvec\<rparr>(P' \<parallel> Q')) \<parallel> R" using `extractFrame R = \<langle>A\<^isub>R, \<Psi>\<^isub>R\<rangle>` `A\<^isub>R \<sharp>* Q`
        by(rule_tac Par1) (assumption | simp)+
      moreover from `xvec \<sharp>* \<Psi>` `xvec \<sharp>* R` have "(\<Psi>, (\<lparr>\<nu>*xvec\<rparr>(P' \<parallel> Q')) \<parallel> R, \<lparr>\<nu>*xvec\<rparr>(P' \<parallel> (Q' \<parallel> R))) \<in> Rel"
        by(rule C3)
      ultimately show ?case by blast
    next
      case(cPar2 R' A\<^isub>Q \<Psi>\<^isub>Q A\<^isub>R \<Psi>\<^isub>R)
      have Aeq: "A\<^isub>Q\<^isub>R = A\<^isub>Q@A\<^isub>R" and \<Psi>eq: "\<Psi>\<^isub>Q\<^isub>R = \<Psi>\<^isub>Q \<otimes> \<Psi>\<^isub>R" by fact+
      from `A\<^isub>Q\<^isub>R \<sharp>* \<Psi>` `A\<^isub>Q\<^isub>R \<sharp>* P` `A\<^isub>Q\<^isub>R \<sharp>* \<Psi>\<^isub>P` `A\<^isub>P \<sharp>* A\<^isub>Q\<^isub>R` Aeq have "A\<^isub>R \<sharp>* \<Psi>" and "A\<^isub>R \<sharp>* \<Psi>\<^isub>P" and "A\<^isub>P \<sharp>* A\<^isub>R" and "A\<^isub>P \<sharp>* A\<^isub>Q" and "A\<^isub>R \<sharp>* P" by simp+
      from `A\<^isub>Q\<^isub>R \<sharp>* \<Psi>` Aeq have "A\<^isub>Q \<sharp>* \<Psi>" by simp
      from `A\<^isub>Q\<^isub>R \<sharp>* P` `A\<^isub>P \<sharp>* A\<^isub>Q\<^isub>R` Aeq FrP have "A\<^isub>Q \<sharp>* \<Psi>\<^isub>P" by(auto dest: extractFrameFreshChain)
      from `A\<^isub>P \<sharp>* A\<^isub>Q\<^isub>R` `extractFrame R = \<langle>A\<^isub>R, \<Psi>\<^isub>R\<rangle>` `extractFrame Q = \<langle>A\<^isub>Q, \<Psi>\<^isub>Q\<rangle>` Aeq `A\<^isub>P \<sharp>* Q` `A\<^isub>P \<sharp>* R` have "A\<^isub>P \<sharp>* \<Psi>\<^isub>Q" and  "A\<^isub>P \<sharp>* \<Psi>\<^isub>R" by(auto dest: extractFrameFreshChain)
      have RTrans: "(\<Psi> \<otimes> \<Psi>\<^isub>P) \<otimes> \<Psi>\<^isub>Q \<rhd> R \<longmapsto>K\<lparr>\<nu>*xvec\<rparr>\<langle>N\<rangle> \<prec> R'" and FrR: "extractFrame R = \<langle>A\<^isub>R, \<Psi>\<^isub>R\<rangle>" by fact+
      then obtain K' where KeqK': "((\<Psi> \<otimes> \<Psi>\<^isub>P) \<otimes> \<Psi>\<^isub>Q) \<otimes> \<Psi>\<^isub>R \<turnstile> K \<leftrightarrow> K'" and "A\<^isub>P \<sharp>* K'" and "A\<^isub>Q \<sharp>* K'"
      using `A\<^isub>P \<sharp>* R` `A\<^isub>Q \<sharp>* R` `A\<^isub>R \<sharp>* \<Psi>` `A\<^isub>R \<sharp>* \<Psi>\<^isub>P` `A\<^isub>R \<sharp>* \<Psi>\<^isub>Q` `A\<^isub>Q \<sharp>* A\<^isub>R` `A\<^isub>P \<sharp>* A\<^isub>R` `A\<^isub>R \<sharp>* R` `A\<^isub>R \<sharp>* R` `A\<^isub>R \<sharp>* K` `distinct A\<^isub>R` `xvec \<sharp>* K` `distinct xvec`
        by(rule_tac B="A\<^isub>P@A\<^isub>Q" in obtainPrefix) (assumption | force)+
      from PTrans \<Psi>eq have "(\<Psi> \<otimes> \<Psi>\<^isub>R) \<otimes> \<Psi>\<^isub>Q \<rhd> P \<longmapsto>M\<lparr>N\<rparr> \<prec> P'"
        by(metis statEqTransition Associativity Commutativity Composition)
      moreover from MeqK KeqK' \<Psi>eq have MeqK': "((\<Psi> \<otimes> \<Psi>\<^isub>R) \<otimes> \<Psi>\<^isub>Q) \<otimes> \<Psi>\<^isub>P \<turnstile> M \<leftrightarrow> K'"
        by(metis statEqEnt Associativity Commutativity Composition chanEqTrans)
      ultimately have "(\<Psi> \<otimes> \<Psi>\<^isub>R) \<otimes> \<Psi>\<^isub>Q \<rhd> P \<longmapsto>K'\<lparr>N\<rparr> \<prec> P'" using FrP `distinct A\<^isub>P` `A\<^isub>P \<sharp>* \<Psi>` `A\<^isub>P \<sharp>* P` `A\<^isub>P \<sharp>* M` `A\<^isub>P \<sharp>* K'` `A\<^isub>P \<sharp>* \<Psi>\<^isub>Q` `A\<^isub>P \<sharp>* \<Psi>\<^isub>R`
        by(rule_tac inputRenameSubject) auto
      moreover from `A\<^isub>Q\<^isub>R \<sharp>* P` `A\<^isub>Q\<^isub>R \<sharp>* N` Aeq have "A\<^isub>Q \<sharp>* P" and "A\<^isub>Q \<sharp>* N" by simp+
      ultimately have "\<Psi> \<otimes> \<Psi>\<^isub>R \<rhd> P \<parallel> Q \<longmapsto>K'\<lparr>N\<rparr> \<prec> P' \<parallel> Q" using `extractFrame Q = \<langle>A\<^isub>Q, \<Psi>\<^isub>Q\<rangle>` `A\<^isub>Q \<sharp>* \<Psi>\<^isub>R` `A\<^isub>Q \<sharp>* K'` `A\<^isub>Q \<sharp>* \<Psi>`
        by(rule_tac Par1) (assumption | force)+
      moreover from FrP `extractFrame Q = \<langle>A\<^isub>Q, \<Psi>\<^isub>Q\<rangle>` `A\<^isub>P \<sharp>* A\<^isub>Q` `A\<^isub>P \<sharp>* \<Psi>\<^isub>Q` `A\<^isub>Q \<sharp>* \<Psi>\<^isub>P`
      have "extractFrame(P \<parallel> Q) = \<langle>(A\<^isub>P@A\<^isub>Q), \<Psi>\<^isub>P \<otimes> \<Psi>\<^isub>Q\<rangle>" by simp+
      moreover from RTrans have "\<Psi> \<otimes> (\<Psi>\<^isub>P \<otimes> \<Psi>\<^isub>Q) \<rhd> R \<longmapsto>K\<lparr>\<nu>*xvec\<rparr>\<langle>N\<rangle> \<prec> R'" by(metis Associativity statEqTransition)
      moreover note FrR
      moreover from MeqK' KeqK' have "\<Psi> \<otimes> (\<Psi>\<^isub>P \<otimes> \<Psi>\<^isub>Q) \<otimes> \<Psi>\<^isub>R \<turnstile> K' \<leftrightarrow> K"
        by(metis statEqEnt Associativity Commutativity Composition chanEqTrans chanEqSym)
      ultimately have "\<Psi> \<rhd> (P \<parallel> Q) \<parallel> R \<longmapsto>\<tau> \<prec> \<lparr>\<nu>*xvec\<rparr>((P' \<parallel> Q) \<parallel> R')"
        using `A\<^isub>P \<sharp>* \<Psi>` `A\<^isub>Q \<sharp>* \<Psi>` `A\<^isub>P \<sharp>* P` `A\<^isub>Q \<sharp>* P` `A\<^isub>P \<sharp>* Q` `A\<^isub>Q \<sharp>* Q` `A\<^isub>P \<sharp>* R` `A\<^isub>Q \<sharp>* R` `A\<^isub>P \<sharp>* K'` `A\<^isub>Q \<sharp>* K'` `A\<^isub>P \<sharp>* A\<^isub>R` `A\<^isub>Q \<sharp>* A\<^isub>R`
              `A\<^isub>R \<sharp>* \<Psi>` `A\<^isub>R \<sharp>* P` `A\<^isub>R \<sharp>* Q` `A\<^isub>R \<sharp>* R` `A\<^isub>R \<sharp>* K` `xvec \<sharp>* P` `xvec \<sharp>* Q`
        by(rule_tac Comm1) (assumption | simp)+
      moreover from `xvec \<sharp>* \<Psi>` have "(\<Psi>, \<lparr>\<nu>*xvec\<rparr>((P' \<parallel> Q) \<parallel> R'), \<lparr>\<nu>*xvec\<rparr>(P' \<parallel> (Q \<parallel> R'))) \<in> Rel"
        by(metis C1 C4)
      ultimately show ?case by blast
    qed
  next
    case(cComm2 \<Psi>\<^isub>Q\<^isub>R M xvec N P' A\<^isub>P \<Psi>\<^isub>P K QR' A\<^isub>Q\<^isub>R)
    from `A\<^isub>Q\<^isub>R \<sharp>* (\<Psi>, P, Q, R, \<alpha>)` have "A\<^isub>Q\<^isub>R \<sharp>* Q" and "A\<^isub>Q\<^isub>R \<sharp>* R" and "A\<^isub>Q\<^isub>R \<sharp>* \<Psi>" by simp+
    from `A\<^isub>P \<sharp>* (Q \<parallel> R)` `xvec \<sharp>* (Q \<parallel> R)` have "A\<^isub>P \<sharp>* Q" and "A\<^isub>P \<sharp>* R" and "xvec \<sharp>* Q" and "xvec \<sharp>* R" by simp+
    have PTrans: "\<Psi> \<otimes> \<Psi>\<^isub>Q\<^isub>R \<rhd> P \<longmapsto>M\<lparr>\<nu>*xvec\<rparr>\<langle>N\<rangle> \<prec> P'" and FrP: "extractFrame P = \<langle>A\<^isub>P, \<Psi>\<^isub>P\<rangle>" and MeqK: "\<Psi> \<otimes> \<Psi>\<^isub>P \<otimes> \<Psi>\<^isub>Q\<^isub>R \<turnstile> M \<leftrightarrow> K" by fact+
    note `\<Psi> \<otimes> \<Psi>\<^isub>P \<rhd> Q \<parallel> R \<longmapsto>K\<lparr>N\<rparr> \<prec> QR'` `extractFrame(Q \<parallel> R) = \<langle>A\<^isub>Q\<^isub>R, \<Psi>\<^isub>Q\<^isub>R\<rangle>` `distinct A\<^isub>Q\<^isub>R` 
    moreover from `A\<^isub>Q\<^isub>R \<sharp>* \<Psi>` `A\<^isub>Q\<^isub>R \<sharp>* \<Psi>\<^isub>P` have "A\<^isub>Q\<^isub>R \<sharp>* (\<Psi> \<otimes> \<Psi>\<^isub>P)" by force
    ultimately show ?case using `A\<^isub>Q\<^isub>R \<sharp>* Q` `A\<^isub>Q\<^isub>R \<sharp>* R` `A\<^isub>Q\<^isub>R \<sharp>* K`
    proof(induct rule: parCasesInputFrame)
      case(cPar1 Q' A\<^isub>Q \<Psi>\<^isub>Q A\<^isub>R \<Psi>\<^isub>R)
      have Aeq: "A\<^isub>Q\<^isub>R = A\<^isub>Q@A\<^isub>R" and \<Psi>eq: "\<Psi>\<^isub>Q\<^isub>R = \<Psi>\<^isub>Q \<otimes> \<Psi>\<^isub>R" by fact+
      from PTrans \<Psi>eq have "(\<Psi> \<otimes> \<Psi>\<^isub>R) \<otimes> \<Psi>\<^isub>Q \<rhd> P \<longmapsto>M\<lparr>\<nu>*xvec\<rparr>\<langle>N\<rangle> \<prec> P'"
        by(metis statEqTransition Associativity Commutativity Composition)
      moreover note FrP
      moreover from `(\<Psi> \<otimes> \<Psi>\<^isub>P) \<otimes> \<Psi>\<^isub>R \<rhd> Q \<longmapsto>K\<lparr>N\<rparr> \<prec> Q'` have "(\<Psi> \<otimes> \<Psi>\<^isub>R) \<otimes> \<Psi>\<^isub>P \<rhd> Q \<longmapsto>K\<lparr>N\<rparr> \<prec> Q'"
        by(metis statEqTransition Associativity Commutativity Composition)
      moreover note `extractFrame Q = \<langle>A\<^isub>Q, \<Psi>\<^isub>Q\<rangle>`
      moreover from MeqK \<Psi>eq have "(\<Psi> \<otimes> \<Psi>\<^isub>R) \<otimes> \<Psi>\<^isub>P \<otimes> \<Psi>\<^isub>Q \<turnstile> M \<leftrightarrow> K"
        by(metis statEqEnt Associativity Commutativity Composition)
      moreover from `A\<^isub>P \<sharp>* Q` `A\<^isub>P \<sharp>* R` `A\<^isub>P \<sharp>* A\<^isub>Q\<^isub>R` Aeq `extractFrame Q = \<langle>A\<^isub>Q, \<Psi>\<^isub>Q\<rangle>` `extractFrame R = \<langle>A\<^isub>R, \<Psi>\<^isub>R\<rangle>`
      have "A\<^isub>P \<sharp>* A\<^isub>Q" and "A\<^isub>P \<sharp>* \<Psi>\<^isub>R" by(auto dest: extractFrameFreshChain)
      moreover from `A\<^isub>Q\<^isub>R \<sharp>* \<Psi>`  `A\<^isub>Q\<^isub>R \<sharp>* P` Aeq have "A\<^isub>Q \<sharp>* \<Psi>" and "A\<^isub>Q \<sharp>* P" by simp+
      ultimately have "\<Psi> \<otimes> \<Psi>\<^isub>R \<rhd> P \<parallel> Q \<longmapsto>\<tau> \<prec> \<lparr>\<nu>*xvec\<rparr>(P' \<parallel> Q')"
        using `A\<^isub>P \<sharp>* \<Psi>` `A\<^isub>P \<sharp>* P` `A\<^isub>P \<sharp>* Q` `A\<^isub>P \<sharp>* M` `A\<^isub>P \<sharp>* A\<^isub>Q` `A\<^isub>Q \<sharp>* \<Psi>` `A\<^isub>Q \<sharp>* \<Psi>\<^isub>R` `A\<^isub>Q \<sharp>* P` `A\<^isub>Q \<sharp>* Q` `A\<^isub>Q \<sharp>* K` `xvec \<sharp>* Q`
        by(rule_tac Comm2) (assumption | force)+
      moreover from `A\<^isub>Q\<^isub>R \<sharp>* \<Psi>` `A\<^isub>Q\<^isub>R \<sharp>* P` Aeq have "A\<^isub>R \<sharp>* \<Psi>" and "A\<^isub>R \<sharp>* P" by simp+
      ultimately have "\<Psi> \<rhd> (P \<parallel> Q) \<parallel> R \<longmapsto>\<tau> \<prec> (\<lparr>\<nu>*xvec\<rparr>(P' \<parallel> Q')) \<parallel> R" using `extractFrame R = \<langle>A\<^isub>R, \<Psi>\<^isub>R\<rangle>` `A\<^isub>R \<sharp>* Q`
        by(rule_tac Par1) (assumption | simp)+
      moreover from `xvec \<sharp>* \<Psi>` `xvec \<sharp>* R` have "(\<Psi>, (\<lparr>\<nu>*xvec\<rparr>(P' \<parallel> Q')) \<parallel> R, \<lparr>\<nu>*xvec\<rparr>(P' \<parallel> (Q' \<parallel> R))) \<in> Rel"
        by(rule C3)
      ultimately show ?case by blast
    next
      case(cPar2 R' A\<^isub>Q \<Psi>\<^isub>Q A\<^isub>R \<Psi>\<^isub>R)
      have Aeq: "A\<^isub>Q\<^isub>R = A\<^isub>Q@A\<^isub>R" and \<Psi>eq: "\<Psi>\<^isub>Q\<^isub>R = \<Psi>\<^isub>Q \<otimes> \<Psi>\<^isub>R" by fact+
      from `A\<^isub>Q\<^isub>R \<sharp>* \<Psi>` `A\<^isub>Q\<^isub>R \<sharp>* P` `A\<^isub>Q\<^isub>R \<sharp>* \<Psi>\<^isub>P` `A\<^isub>P \<sharp>* A\<^isub>Q\<^isub>R` Aeq 
      have "A\<^isub>R \<sharp>* \<Psi>" and "A\<^isub>R \<sharp>* \<Psi>\<^isub>P" and "A\<^isub>P \<sharp>* A\<^isub>R" and "A\<^isub>P \<sharp>* A\<^isub>Q" and "A\<^isub>R \<sharp>* P" and "A\<^isub>Q \<sharp>* \<Psi>" and "A\<^isub>Q \<sharp>* \<Psi>\<^isub>P" by simp+
      have RTrans: "(\<Psi> \<otimes> \<Psi>\<^isub>P) \<otimes> \<Psi>\<^isub>Q \<rhd> R \<longmapsto>K\<lparr>N\<rparr> \<prec> R'" and FrR: "extractFrame R = \<langle>A\<^isub>R, \<Psi>\<^isub>R\<rangle>" by fact+
      then obtain K' where KeqK': "((\<Psi> \<otimes> \<Psi>\<^isub>P) \<otimes> \<Psi>\<^isub>Q) \<otimes> \<Psi>\<^isub>R \<turnstile> K \<leftrightarrow> K'" and "A\<^isub>P \<sharp>* K'" and "A\<^isub>Q \<sharp>* K'"
      using `A\<^isub>P \<sharp>* R` `A\<^isub>Q \<sharp>* R` `A\<^isub>R \<sharp>* \<Psi>` `A\<^isub>R \<sharp>* \<Psi>\<^isub>P` `A\<^isub>R \<sharp>* \<Psi>\<^isub>Q` `A\<^isub>Q \<sharp>* A\<^isub>R` `A\<^isub>P \<sharp>* A\<^isub>R` `A\<^isub>R \<sharp>* R` `A\<^isub>R \<sharp>* R` `A\<^isub>R \<sharp>* K` `distinct A\<^isub>R`
        by(rule_tac B="A\<^isub>P@A\<^isub>Q" in obtainPrefix) (assumption | force)+
      from PTrans \<Psi>eq have "(\<Psi> \<otimes> \<Psi>\<^isub>R) \<otimes> \<Psi>\<^isub>Q \<rhd> P \<longmapsto>M\<lparr>\<nu>*xvec\<rparr>\<langle>N\<rangle> \<prec> P'"
        by(metis statEqTransition Associativity Commutativity Composition)
      moreover from MeqK KeqK' \<Psi>eq have MeqK': "((\<Psi> \<otimes> \<Psi>\<^isub>R) \<otimes> \<Psi>\<^isub>Q) \<otimes> \<Psi>\<^isub>P \<turnstile> M \<leftrightarrow> K'"
        by(metis statEqEnt Associativity Commutativity Composition chanEqTrans)
      moreover from `A\<^isub>P \<sharp>* R` `A\<^isub>P \<sharp>* Q` `A\<^isub>P \<sharp>* A\<^isub>Q\<^isub>R` FrR `extractFrame Q = \<langle>A\<^isub>Q, \<Psi>\<^isub>Q\<rangle>` Aeq have "A\<^isub>P \<sharp>* \<Psi>\<^isub>Q" and "A\<^isub>P \<sharp>* \<Psi>\<^isub>R"
        by(auto dest: extractFrameFreshChain)
      ultimately have "(\<Psi> \<otimes> \<Psi>\<^isub>R) \<otimes> \<Psi>\<^isub>Q \<rhd> P \<longmapsto>K'\<lparr>\<nu>*xvec\<rparr>\<langle>N\<rangle> \<prec> P'" using FrP `distinct A\<^isub>P` `A\<^isub>P \<sharp>* \<Psi>` `A\<^isub>P \<sharp>* P` `A\<^isub>P \<sharp>* M` `A\<^isub>P \<sharp>* K'`
        by(rule_tac outputRenameSubject) auto
      moreover from `A\<^isub>Q\<^isub>R \<sharp>* P` `A\<^isub>Q\<^isub>R \<sharp>* N` `A\<^isub>Q\<^isub>R \<sharp>* xvec` Aeq have "A\<^isub>Q \<sharp>* P" and "A\<^isub>Q \<sharp>* N" and "A\<^isub>Q \<sharp>* xvec" by simp+
      ultimately have "\<Psi> \<otimes> \<Psi>\<^isub>R \<rhd> P \<parallel> Q \<longmapsto>K'\<lparr>\<nu>*xvec\<rparr>\<langle>N\<rangle> \<prec> (P' \<parallel> Q)" using `extractFrame Q = \<langle>A\<^isub>Q, \<Psi>\<^isub>Q\<rangle>` `A\<^isub>Q \<sharp>* \<Psi>\<^isub>R` `A\<^isub>Q \<sharp>* K'` `xvec \<sharp>* Q` `A\<^isub>Q \<sharp>* \<Psi>`
        by(rule_tac Par1) (assumption | force)+
      moreover from FrP `extractFrame Q = \<langle>A\<^isub>Q, \<Psi>\<^isub>Q\<rangle>` `A\<^isub>P \<sharp>* A\<^isub>Q` `A\<^isub>P \<sharp>* \<Psi>\<^isub>Q` `A\<^isub>Q \<sharp>* \<Psi>\<^isub>P`
      have "extractFrame(P \<parallel> Q) = \<langle>(A\<^isub>P@A\<^isub>Q), \<Psi>\<^isub>P \<otimes> \<Psi>\<^isub>Q\<rangle>" by simp+
      moreover from RTrans have "\<Psi> \<otimes> (\<Psi>\<^isub>P \<otimes> \<Psi>\<^isub>Q) \<rhd> R \<longmapsto>K\<lparr>N\<rparr> \<prec> R'" by(metis Associativity statEqTransition)
      moreover note FrR
      moreover from MeqK' KeqK' have "\<Psi> \<otimes> (\<Psi>\<^isub>P \<otimes> \<Psi>\<^isub>Q) \<otimes> \<Psi>\<^isub>R \<turnstile> K' \<leftrightarrow> K"
        by(metis statEqEnt Associativity Commutativity Composition chanEqTrans chanEqSym)
      ultimately have "\<Psi> \<rhd> (P \<parallel> Q) \<parallel> R \<longmapsto>\<tau> \<prec> \<lparr>\<nu>*xvec\<rparr>((P' \<parallel> Q) \<parallel> R')"
        using `A\<^isub>P \<sharp>* \<Psi>` `A\<^isub>Q \<sharp>* \<Psi>` `A\<^isub>P \<sharp>* P` `A\<^isub>Q \<sharp>* P` `A\<^isub>P \<sharp>* Q` `A\<^isub>Q \<sharp>* Q` `A\<^isub>P \<sharp>* R` `A\<^isub>Q \<sharp>* R` `A\<^isub>P \<sharp>* K'` `A\<^isub>Q \<sharp>* K'` `A\<^isub>P \<sharp>* A\<^isub>R` `A\<^isub>Q \<sharp>* A\<^isub>R`
              `A\<^isub>R \<sharp>* \<Psi>` `A\<^isub>R \<sharp>* P` `A\<^isub>R \<sharp>* Q` `A\<^isub>R \<sharp>* R` `A\<^isub>R \<sharp>* K` `xvec \<sharp>* R`
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
    case(cPar1 P' A\<^isub>Q \<Psi>\<^isub>Q)
    from `extractFrame(\<zero>) = \<langle>A\<^isub>Q, \<Psi>\<^isub>Q\<rangle>` have "\<Psi>\<^isub>Q = SBottom'" by auto
    with `\<Psi> \<otimes> \<Psi>\<^isub>Q \<rhd> P \<longmapsto>\<alpha> \<prec> P'` have "\<Psi> \<rhd> P \<longmapsto>\<alpha> \<prec> P'"
      by(metis statEqTransition Identity)
    moreover have "(\<Psi>, P', P' \<parallel> \<zero>) \<in> Rel" by(rule C1)
    ultimately show ?case by blast
  next
    case(cPar2 Q' A\<^isub>P \<Psi>\<^isub>P)
    from `\<Psi> \<otimes> \<Psi>\<^isub>P \<rhd> \<zero> \<longmapsto>\<alpha> \<prec> Q'` have False
      by auto
    thus ?case by simp
  next
    case(cComm1 \<Psi>\<^isub>Q M N P' A\<^isub>P \<Psi>\<^isub>P K xvec Q' A\<^isub>Q)
    from `\<Psi> \<otimes> \<Psi>\<^isub>P \<rhd> \<zero> \<longmapsto>K\<lparr>\<nu>*xvec\<rparr>\<langle>N\<rangle> \<prec> Q'` have False by auto
    thus ?case by simp
  next
    case(cComm2 \<Psi>\<^isub>Q M xvec N P' A\<^isub>P \<Psi>\<^isub>P K Q' A\<^isub>Q)
    from `\<Psi> \<otimes> \<Psi>\<^isub>P \<rhd> \<zero> \<longmapsto>K\<lparr>N\<rparr> \<prec> Q'` have False
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
      case(cPar1 P' A\<^isub>Q \<Psi>\<^isub>Q)
      from `x \<sharp> P' \<parallel> \<lparr>\<nu>x\<rparr>Q` have "x \<sharp> P'" by simp
      have PTrans: "\<Psi> \<otimes> \<Psi>\<^isub>Q \<rhd> P \<longmapsto>\<alpha> \<prec> P'" by fact
      from `extractFrame(\<lparr>\<nu>x\<rparr>Q) = \<langle>A\<^isub>Q, \<Psi>\<^isub>Q\<rangle>` have FrxQ: "\<lparr>\<nu>x\<rparr>(extractFrame Q) = \<langle>A\<^isub>Q, \<Psi>\<^isub>Q\<rangle>" by simp
      then obtain y A\<^isub>Q' where A: "A\<^isub>Q = y#A\<^isub>Q'" by(case_tac A\<^isub>Q) auto
      with `A\<^isub>Q \<sharp>* \<Psi>` `A\<^isub>Q \<sharp>* P` `A\<^isub>Q \<sharp>* \<alpha>`
      have "A\<^isub>Q' \<sharp>* \<Psi>" and "A\<^isub>Q' \<sharp>* P" and "A\<^isub>Q' \<sharp>* \<alpha>"
        and "y \<sharp> \<Psi>" and "y \<sharp> P" and "y \<sharp> \<alpha>"
        by simp+
      from PTrans `y \<sharp> P` `y \<sharp> \<alpha>` `bn \<alpha> \<sharp>* subject \<alpha>` `distinct(bn \<alpha>)` have "y \<sharp> P'"
        by(auto intro: freeFreshDerivative)
      note PTrans
      moreover from A `A\<^isub>Q \<sharp>* x` FrxQ have "extractFrame([(y, x)] \<bullet> Q) = \<langle>A\<^isub>Q', \<Psi>\<^isub>Q\<rangle>" 
        by(simp add: frame.inject alpha' fresh_list_cons eqvts) 
      moreover from `bn \<alpha> \<sharp>* Q` have "([(y, x)] \<bullet> (bn \<alpha>)) \<sharp>* ([(y, x)] \<bullet> Q)"
        by(simp add: pt_fresh_star_bij[OF pt_name_inst, OF at_name_inst])
      with `x \<sharp> \<alpha>` `A\<^isub>Q \<sharp>* \<alpha>` A have "bn \<alpha> \<sharp>* ([(y, x)] \<bullet> Q)" by simp
      ultimately have "\<Psi> \<rhd> P \<parallel> ([(y, x)] \<bullet> Q) \<longmapsto>\<alpha> \<prec> (P' \<parallel> ([(y, x)] \<bullet> Q))"
        using `A\<^isub>Q' \<sharp>* \<Psi>` `A\<^isub>Q' \<sharp>* P` `A\<^isub>Q' \<sharp>* \<alpha>`
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
      case(cPar2 xQ' A\<^isub>P \<Psi>\<^isub>P)
      from `A\<^isub>P \<sharp>* \<lparr>\<nu>x\<rparr>Q` `A\<^isub>P \<sharp>* x` have "A\<^isub>P \<sharp>* Q" by simp
      note `\<Psi> \<otimes> \<Psi>\<^isub>P \<rhd> \<lparr>\<nu>x\<rparr>Q \<longmapsto>\<alpha> \<prec> xQ'`
      moreover have FrP: "extractFrame P = \<langle>A\<^isub>P, \<Psi>\<^isub>P\<rangle>" by fact
      with `x \<sharp> P` `A\<^isub>P \<sharp>* x` have "x \<sharp> \<Psi>\<^isub>P" and "x \<sharp> A\<^isub>P"
        by(force dest: extractFrameFresh)+
      with `x \<sharp> \<Psi>` have "x \<sharp> \<Psi> \<otimes> \<Psi>\<^isub>P" by force
      moreover note `x \<sharp> \<alpha>`
      moreover from `x \<sharp> P \<parallel> xQ'` have "x \<sharp> xQ'" by simp
      moreover from FrP `bn \<alpha> \<sharp>* P` `A\<^isub>P \<sharp>* \<alpha>` have "bn \<alpha> \<sharp>* \<Psi>\<^isub>P"
        by(drule_tac extractFrameFreshChain) auto
      with `bn \<alpha> \<sharp>* \<Psi>` have "bn \<alpha> \<sharp>* (\<Psi> \<otimes> \<Psi>\<^isub>P)" by force
      ultimately show ?case using `bn \<alpha> \<sharp>* Q` `bn \<alpha> \<sharp>* subject \<alpha>` `x \<sharp> \<alpha>` `bn \<alpha> \<sharp>* P` `A\<^isub>P \<sharp>* \<alpha>` `bn \<alpha> \<sharp>* \<Psi>`
      proof(induct rule: resCases')
        case(cOpen M xvec1 xvec2 y N Q')
        from `x \<sharp> M\<lparr>\<nu>*(xvec1@y#xvec2)\<rparr>\<langle>N\<rangle>` have "x \<sharp> xvec1" and "x \<noteq> y" and "x \<sharp> xvec2" by simp+
        from `bn(M\<lparr>\<nu>*(xvec1@y#xvec2)\<rparr>\<langle>N\<rangle>) \<sharp>* \<Psi>` have "y \<sharp> \<Psi>" by simp
        note `\<Psi> \<otimes> \<Psi>\<^isub>P \<rhd> ([(x, y)] \<bullet> Q) \<longmapsto>M\<lparr>\<nu>*(xvec1@xvec2)\<rparr>\<langle>N\<rangle> \<prec> Q'` FrP
        moreover from `bn(M\<lparr>\<nu>*(xvec1@y#xvec2)\<rparr>\<langle>N\<rangle>) \<sharp>* P` have "(xvec1@xvec2) \<sharp>* P" and "y \<sharp> P" by simp+
        moreover from `A\<^isub>P \<sharp>* (M\<lparr>\<nu>*(xvec1@y#xvec2)\<rparr>\<langle>N\<rangle>)` have "A\<^isub>P \<sharp>* (M\<lparr>\<nu>*(xvec1@xvec2)\<rparr>\<langle>N\<rangle>)" and "y \<sharp> A\<^isub>P" by simp+
        moreover from `A\<^isub>P \<sharp>* Q` `x \<sharp> A\<^isub>P` `y \<sharp> A\<^isub>P` have "A\<^isub>P \<sharp>* ([(x, y)] \<bullet> Q)" by simp
        ultimately have "\<Psi> \<rhd> P \<parallel> ([(x, y)] \<bullet> Q) \<longmapsto>M\<lparr>\<nu>*(xvec1@xvec2)\<rparr>\<langle>N\<rangle> \<prec> (P \<parallel> Q')" 
          using `A\<^isub>P \<sharp>* \<Psi>`
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
        from `\<Psi> \<otimes> \<Psi>\<^isub>P \<rhd> Q \<longmapsto>\<alpha> \<prec> Q'` FrP `bn \<alpha> \<sharp>* P`
        have "\<Psi> \<rhd> P \<parallel> Q \<longmapsto>\<alpha> \<prec> (P \<parallel> Q')" using `A\<^isub>P \<sharp>* \<Psi>` `A\<^isub>P \<sharp>* Q` `A\<^isub>P \<sharp>* \<alpha>`
          by(rule Par2)
        hence "\<Psi> \<rhd> \<lparr>\<nu>x\<rparr>(P \<parallel> Q) \<longmapsto>\<alpha> \<prec> \<lparr>\<nu>x\<rparr>(P \<parallel> Q')" using `x \<sharp> \<Psi>` `x \<sharp> \<alpha>`
          by(rule Scope)
        moreover from `x \<sharp> \<Psi>` `x \<sharp> P` have "(\<Psi>, \<lparr>\<nu>x\<rparr>(\<lparr>\<nu>*[]\<rparr>(P \<parallel> Q')), \<lparr>\<nu>*[]\<rparr>(P \<parallel> \<lparr>\<nu>x\<rparr>Q')) \<in> Rel"
          by(rule_tac C2) auto
        ultimately show ?case
          by force
      qed
    next
      case(cComm1 \<Psi>\<^isub>Q M N P' A\<^isub>P \<Psi>\<^isub>P K xvec xQ' A\<^isub>Q)
      have QTrans: "\<Psi> \<otimes> \<Psi>\<^isub>P \<rhd> \<lparr>\<nu>x\<rparr>Q \<longmapsto>K\<lparr>\<nu>*xvec\<rparr>\<langle>N\<rangle> \<prec> xQ'" and FrQ: "extractFrame(\<lparr>\<nu>x\<rparr>Q) = \<langle>A\<^isub>Q, \<Psi>\<^isub>Q\<rangle>" by fact+
      have PTrans: "\<Psi> \<otimes> \<Psi>\<^isub>Q \<rhd> P \<longmapsto>M\<lparr>N\<rparr> \<prec> P'" and FrP: "extractFrame P = \<langle>A\<^isub>P, \<Psi>\<^isub>P\<rangle>" by fact+
      have "x \<sharp> \<lparr>\<nu>x\<rparr>Q" by(simp add: abs_fresh)
      with QTrans have "x \<sharp> N" and "x \<sharp> xQ'" using `xvec \<sharp>* x` `xvec \<sharp>* K` `distinct xvec` 
        by(force intro: outputFreshDerivative)+
      from PTrans `x \<sharp> P` `x \<sharp> N`  have "x \<sharp> P'" by(rule inputFreshDerivative)
      from `x \<sharp> \<lparr>\<nu>x\<rparr>Q` FrQ `A\<^isub>Q \<sharp>* x` have "x \<sharp> \<Psi>\<^isub>Q"
        by(drule_tac extractFrameFresh) auto
      from `x \<sharp> P` FrP `A\<^isub>P \<sharp>* x` have "x \<sharp> \<Psi>\<^isub>P"
        by(drule_tac extractFrameFresh) auto
      from `A\<^isub>P \<sharp>* \<lparr>\<nu>x\<rparr>Q` `A\<^isub>P \<sharp>* x` have "A\<^isub>P \<sharp>* Q" by simp
      from `A\<^isub>Q \<sharp>* \<lparr>\<nu>x\<rparr>Q` `A\<^isub>Q \<sharp>* x` have "A\<^isub>Q \<sharp>* Q" by simp
      from PTrans FrP `distinct A\<^isub>P` `x \<sharp> P` `A\<^isub>Q \<sharp>* P` `xvec \<sharp>* P` `A\<^isub>P \<sharp>* \<Psi>` `A\<^isub>P \<sharp>* \<Psi>\<^isub>Q` `A\<^isub>P \<sharp>* x` `A\<^isub>P \<sharp>* A\<^isub>Q` `A\<^isub>P \<sharp>* P`  `A\<^isub>P \<sharp>* M` `A\<^isub>P \<sharp>* xvec`
      obtain M' where "(\<Psi> \<otimes> \<Psi>\<^isub>Q) \<otimes> \<Psi>\<^isub>P \<turnstile> M \<leftrightarrow> M'" and "x \<sharp> M'" and "A\<^isub>Q \<sharp>* M'" and "xvec \<sharp>* M'"
        by(rule_tac B="x#xvec@A\<^isub>Q" in obtainPrefix) (assumption | force simp add: fresh_star_list_cons)+
      hence MeqM': "\<Psi> \<otimes> \<Psi>\<^isub>P \<otimes> \<Psi>\<^isub>Q \<turnstile> M \<leftrightarrow> M'" by(metis statEqEnt Associativity Commutativity Composition)
      with `\<Psi> \<otimes> \<Psi>\<^isub>P \<otimes> \<Psi>\<^isub>Q \<turnstile> M \<leftrightarrow> K` have "\<Psi> \<otimes> \<Psi>\<^isub>P \<otimes> \<Psi>\<^isub>Q \<turnstile> K \<leftrightarrow> M'"
        by(blast intro: chanEqTrans chanEqSym)
      hence "(\<Psi> \<otimes> \<Psi>\<^isub>P) \<otimes> \<Psi>\<^isub>Q \<turnstile> K \<leftrightarrow> M'" by(metis statEqEnt Associativity Commutativity Composition)
      with QTrans FrQ `distinct A\<^isub>Q` `A\<^isub>Q \<sharp>* \<Psi>` `A\<^isub>Q \<sharp>* \<Psi>\<^isub>P` `A\<^isub>Q \<sharp>* (\<lparr>\<nu>x\<rparr>Q)` `A\<^isub>Q \<sharp>* K` `A\<^isub>Q \<sharp>* M'`
      have "\<Psi> \<otimes> \<Psi>\<^isub>P \<rhd> \<lparr>\<nu>x\<rparr>Q \<longmapsto>M'\<lparr>\<nu>*xvec\<rparr>\<langle>N\<rangle> \<prec> xQ'"
        by(force intro: outputRenameSubject)
      moreover from `x \<sharp> \<Psi>` `x \<sharp> \<Psi>\<^isub>P` have "x \<sharp> \<Psi> \<otimes> \<Psi>\<^isub>P" by force
      moreover from `xvec \<sharp>* x` have "x \<sharp> xvec" by simp
      with `x \<sharp> M'` `x \<sharp> N` have "x \<sharp> M'\<lparr>\<nu>*xvec\<rparr>\<langle>N\<rangle>" by simp
      moreover note `x \<sharp> xQ'`
      moreover from `xvec \<sharp>* \<Psi>` `xvec \<sharp>* \<Psi>\<^isub>P` have "bn(M'\<lparr>\<nu>*xvec\<rparr>\<langle>N\<rangle>) \<sharp>* (\<Psi> \<otimes> \<Psi>\<^isub>P)" by force
      moreover from `xvec \<sharp>* \<lparr>\<nu>x\<rparr>Q` `x \<sharp> xvec` have "bn(M'\<lparr>\<nu>*xvec\<rparr>\<langle>N\<rangle>) \<sharp>* Q" by simp
      moreover from `xvec \<sharp>* P` have "bn(M'\<lparr>\<nu>*xvec\<rparr>\<langle>N\<rangle>) \<sharp>* P" by simp
      from `xvec \<sharp>* \<Psi>` have "bn(M'\<lparr>\<nu>*xvec\<rparr>\<langle>N\<rangle>) \<sharp>* \<Psi>" by simp
      from `A\<^isub>Q \<sharp>* xvec` `A\<^isub>Q \<sharp>* M'` `A\<^isub>Q \<sharp>* N` have "A\<^isub>Q \<sharp>* (M'\<lparr>\<nu>*xvec\<rparr>\<langle>N\<rangle>)" by simp
      have "object(M'\<lparr>\<nu>*xvec\<rparr>\<langle>N\<rangle>) = Some N" by simp
      have "bn(M'\<lparr>\<nu>*xvec\<rparr>\<langle>N\<rangle>) = xvec" by simp
      have "subject(M'\<lparr>\<nu>*xvec\<rparr>\<langle>N\<rangle>) = Some M'" by simp
      from `xvec \<sharp>* M'` have "bn(M'\<lparr>\<nu>*xvec\<rparr>\<langle>N\<rangle>) \<sharp>* subject(M'\<lparr>\<nu>*xvec\<rparr>\<langle>N\<rangle>)" by simp
      ultimately show ?case 
        using `x \<sharp> M'\<lparr>\<nu>*xvec\<rparr>\<langle>N\<rangle>` `bn(M'\<lparr>\<nu>*xvec\<rparr>\<langle>N\<rangle>) \<sharp>* P` `bn(M'\<lparr>\<nu>*xvec\<rparr>\<langle>N\<rangle>) \<sharp>* \<Psi>` `object(M'\<lparr>\<nu>*xvec\<rparr>\<langle>N\<rangle>) = Some N`
              `bn(M'\<lparr>\<nu>*xvec\<rparr>\<langle>N\<rangle>) = xvec` `subject(M'\<lparr>\<nu>*xvec\<rparr>\<langle>N\<rangle>) = Some M'` `A\<^isub>Q \<sharp>* (M'\<lparr>\<nu>*xvec\<rparr>\<langle>N\<rangle>)`
      proof(induct rule: resCases)
        case(cOpen M'' xvec1 xvec2 y N' Q')
        from `x \<sharp> M''\<lparr>\<nu>*(xvec1@y#xvec2)\<rparr>\<langle>N'\<rangle>` have "x \<sharp> xvec1" and "x \<noteq> y" and "x \<sharp> xvec2" and "x \<sharp> M''"
          by simp+
        from `bn(M''\<lparr>\<nu>*(xvec1@y#xvec2)\<rparr>\<langle>N'\<rangle>) \<sharp>* P` have "(xvec1@xvec2) \<sharp>* P" and "y \<sharp> P" by simp+
        from `A\<^isub>Q \<sharp>* (M''\<lparr>\<nu>*(xvec1@y#xvec2)\<rparr>\<langle>N'\<rangle>)` have "(xvec1@xvec2) \<sharp>* A\<^isub>Q" and "y \<sharp> A\<^isub>Q" and "A\<^isub>Q \<sharp>* M''" by simp+
        from `bn(M''\<lparr>\<nu>*(xvec1@y#xvec2)\<rparr>\<langle>N'\<rangle>) \<sharp>* \<Psi>` have "(xvec1@xvec2) \<sharp>* \<Psi>" and "y \<sharp> \<Psi>" by simp+
        from `object(M''\<lparr>\<nu>*(xvec1@y#xvec2)\<rparr>\<langle>N'\<rangle>) = Some N` have "N = N'" by simp
        from `bn(M''\<lparr>\<nu>*(xvec1@y#xvec2)\<rparr>\<langle>N'\<rangle>) = xvec` have "xvec = xvec1@y#xvec2" by simp
        from `subject(M''\<lparr>\<nu>*(xvec1@y#xvec2)\<rparr>\<langle>N'\<rangle>) = Some M'` have "M' = M''" by simp
        from `x \<sharp> P` `y \<sharp> P` `x \<noteq> y` `\<Psi> \<otimes> \<Psi>\<^isub>Q \<rhd> P \<longmapsto>M\<lparr>N\<rparr> \<prec> P'`
        have "\<Psi> \<otimes> \<Psi>\<^isub>Q \<rhd> P \<longmapsto>M\<lparr>([(y, x)] \<bullet> N)\<rparr> \<prec> ([(y, x)] \<bullet> P')"
          by(rule_tac xvec="[y]" in inputAlpha) (auto simp add: calc_atm)
        hence PTrans: "\<Psi> \<otimes> \<Psi>\<^isub>Q \<rhd> P \<longmapsto>M\<lparr>([(x, y)] \<bullet> N)\<rparr> \<prec> ([(x, y)] \<bullet> P')"
          by(simp add: name_swap)
        have QTrans: "\<Psi> \<otimes> \<Psi>\<^isub>P \<rhd> Q \<longmapsto>M''\<lparr>\<nu>*(xvec1@xvec2)\<rparr>\<langle>([(x, y)] \<bullet> N')\<rangle> \<prec> ([(x, y)] \<bullet> Q')" by fact
        with `A\<^isub>Q \<sharp>* x` `y \<sharp> A\<^isub>Q` `distinct xvec1` `distinct xvec2` `xvec1 \<sharp>* xvec2` `xvec1 \<sharp>* M''` `xvec2 \<sharp>* M''`
             `(xvec1@xvec2) \<sharp>* A\<^isub>Q`
        have "A\<^isub>Q \<sharp>* ([(x, y)] \<bullet> Q')" using `A\<^isub>Q \<sharp>* Q`
          by(rule_tac outputFreshChainDerivative(2)) (assumption | simp)+

        from `extractFrame(\<lparr>\<nu>x\<rparr>Q) = \<langle>A\<^isub>Q, \<Psi>\<^isub>Q\<rangle>` have FrxQ: "\<lparr>\<nu>x\<rparr>(extractFrame Q) = \<langle>A\<^isub>Q, \<Psi>\<^isub>Q\<rangle>" by simp
        then obtain z A\<^isub>Q' where A: "A\<^isub>Q = z#A\<^isub>Q'" by(case_tac A\<^isub>Q) auto
        with `A\<^isub>Q \<sharp>* \<Psi>` `A\<^isub>Q \<sharp>* P` `A\<^isub>Q \<sharp>* P'` `A\<^isub>Q \<sharp>* \<Psi>\<^isub>P` `A\<^isub>Q \<sharp>* Q` `(xvec1@xvec2) \<sharp>* A\<^isub>Q` `A\<^isub>Q \<sharp>* M''` `A\<^isub>Q \<sharp>* ([(x, y)] \<bullet> Q')` `y \<sharp> A\<^isub>Q` `A\<^isub>Q \<sharp>* N`
        have "A\<^isub>Q' \<sharp>* \<Psi>" and "A\<^isub>Q' \<sharp>* P" and "A\<^isub>Q' \<sharp>* \<Psi>\<^isub>P" and "A\<^isub>Q' \<sharp>* Q"
          and "z \<sharp> \<Psi>" and "z \<sharp> P" and "z \<sharp> P'" and "z \<sharp> \<Psi>\<^isub>P" and "z \<sharp> Q" and "z \<sharp> xvec1" and "z \<sharp> xvec2"
          and "z \<sharp> M''" and "z \<sharp> ([(x, y)] \<bullet> Q')" and "A\<^isub>Q' \<sharp>* M''" and "z \<noteq> y" and "z \<sharp> (xvec1@xvec2)"
          by auto
        from A `A\<^isub>P \<sharp>* A\<^isub>Q` have "A\<^isub>P \<sharp>* A\<^isub>Q'" and "z \<sharp> A\<^isub>P" by simp+
        from A `A\<^isub>Q \<sharp>* x` have "x \<noteq> z" and "x \<sharp> A\<^isub>Q'" by simp+

        from `distinct A\<^isub>Q` A have "z \<sharp> A\<^isub>Q'" 
          by(induct A\<^isub>Q') (auto simp add: fresh_list_nil fresh_list_cons)
        from PTrans `x \<sharp> P` `z \<sharp> P` `x \<noteq> z` have "\<Psi> \<otimes> \<Psi>\<^isub>Q \<rhd> P \<longmapsto>M\<lparr>([(x, z)] \<bullet> [(x, y)] \<bullet> N)\<rparr> \<prec> ([(x, z)] \<bullet> [(x, y)] \<bullet> P')"
          by(rule_tac xvec="[x]" in inputAlpha) (auto simp add: calc_atm)
        moreover note FrP 
        moreover from QTrans have "([(x, z)] \<bullet> (\<Psi> \<otimes> \<Psi>\<^isub>P)) \<rhd> ([(x, z)] \<bullet> Q) \<longmapsto>([(x, z)] \<bullet> (M''\<lparr>\<nu>*(xvec1@xvec2)\<rparr>\<langle>([(x, y)] \<bullet> N')\<rangle> \<prec> ([(x, y)] \<bullet> Q')))" 
          by(rule semantics.eqvt)
        with `x \<sharp> \<Psi>` `z \<sharp> \<Psi>` `x \<sharp> \<Psi>\<^isub>P` `z \<sharp> \<Psi>\<^isub>P` `x \<sharp> M''` `z \<sharp> M''` `x \<sharp> xvec1` `x \<sharp> xvec2` `z \<sharp> xvec1` `z \<sharp> xvec2`
        have "\<Psi> \<otimes> \<Psi>\<^isub>P \<rhd> ([(x, z)] \<bullet> Q) \<longmapsto>M''\<lparr>\<nu>*(xvec1@xvec2)\<rparr>\<langle>([(x, z)] \<bullet> [(x, y)] \<bullet> N')\<rangle> \<prec> ([(x, z)] \<bullet> [(x, y)] \<bullet> Q')" 
          by(simp add: eqvts)
        moreover from A `A\<^isub>Q \<sharp>* x` FrxQ have "extractFrame([(x, z)] \<bullet> Q) = \<langle>A\<^isub>Q', \<Psi>\<^isub>Q\<rangle>"
          by(clarsimp simp add: alpha' eqvts frame.inject fresh_list_cons name_swap)
        moreover from `A\<^isub>P \<sharp>* Q` have "([(x, z)] \<bullet> A\<^isub>P) \<sharp>* ([(x, z)] \<bullet> Q)"
          by(simp add: pt_fresh_star_bij[OF pt_name_inst, OF at_name_inst])
        with `A\<^isub>P \<sharp>* x` `z \<sharp> A\<^isub>P` have "A\<^isub>P \<sharp>* ([(x, z)] \<bullet> Q)" by simp
        moreover from `A\<^isub>Q' \<sharp>* Q` have "([(x, z)] \<bullet> A\<^isub>Q') \<sharp>* ([(x, z)] \<bullet> Q)"
          by(simp add: pt_fresh_star_bij[OF pt_name_inst, OF at_name_inst])
        with `x \<sharp> A\<^isub>Q'` `z \<sharp> A\<^isub>Q'` have "A\<^isub>Q' \<sharp>* ([(x, z)] \<bullet> Q)" by simp
        ultimately have "\<Psi> \<rhd> (P \<parallel> ([(x, z)] \<bullet> Q)) \<longmapsto>\<tau> \<prec> \<lparr>\<nu>*(xvec1@xvec2)\<rparr>(([(x, z)] \<bullet> [(x, y)] \<bullet> P') \<parallel> ([(x, z)] \<bullet> [(x, y)] \<bullet> Q'))"
          using MeqM' `M'=M''` `N=N'` `A\<^isub>P \<sharp>* \<Psi>` `A\<^isub>P \<sharp>* P`  `A\<^isub>P \<sharp>* A\<^isub>Q'` `A\<^isub>Q' \<sharp>* \<Psi>` `A\<^isub>Q' \<sharp>* P` `(xvec1@xvec2) \<sharp>* P` `A\<^isub>P \<sharp>* M` `A\<^isub>Q' \<sharp>* M''`
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
        have QTrans: "\<Psi> \<otimes> \<Psi>\<^isub>P \<rhd> Q \<longmapsto>M'\<lparr>\<nu>*xvec\<rparr>\<langle>N\<rangle> \<prec> Q'" by fact
        with `A\<^isub>Q \<sharp>* Q` `A\<^isub>Q \<sharp>* xvec` `xvec \<sharp>* M'` `distinct xvec` have "A\<^isub>Q \<sharp>* Q'"
          by(force dest: outputFreshChainDerivative)
        
        with `extractFrame(\<lparr>\<nu>x\<rparr>Q) = \<langle>A\<^isub>Q, \<Psi>\<^isub>Q\<rangle>` have FrxQ: "\<lparr>\<nu>x\<rparr>(extractFrame Q) = \<langle>A\<^isub>Q, \<Psi>\<^isub>Q\<rangle>" by simp
        then obtain y A\<^isub>Q' where A: "A\<^isub>Q = y#A\<^isub>Q'" by(case_tac A\<^isub>Q) auto
        with `A\<^isub>Q \<sharp>* \<Psi>` `A\<^isub>Q \<sharp>* P` `A\<^isub>Q \<sharp>* P'` `A\<^isub>Q \<sharp>* \<Psi>\<^isub>P` `A\<^isub>Q \<sharp>* Q` `A\<^isub>Q \<sharp>* xvec` `A\<^isub>Q \<sharp>* M'` `A\<^isub>Q \<sharp>* Q'`
        have "A\<^isub>Q' \<sharp>* \<Psi>" and "A\<^isub>Q' \<sharp>* P" and "A\<^isub>Q' \<sharp>* \<Psi>\<^isub>P" and "A\<^isub>Q' \<sharp>* Q" and "A\<^isub>Q \<sharp>* xvec" and "A\<^isub>Q \<sharp>* Q'"
          and "y \<sharp> \<Psi>" and "y \<sharp> P" and "y \<sharp> P'" and "y \<sharp> \<Psi>\<^isub>P" and "y \<sharp> Q" and "y \<sharp> xvec" and "y \<sharp> M'" and "y \<sharp> Q'"
          and "A\<^isub>Q' \<sharp>* M'"
          by(simp)+
        from A `A\<^isub>P \<sharp>* A\<^isub>Q` have "A\<^isub>P \<sharp>* A\<^isub>Q'" and "y \<sharp> A\<^isub>P" by(simp add: fresh_star_list_cons)+
        from A `A\<^isub>Q \<sharp>* x` have "x \<noteq> y" and "x \<sharp> A\<^isub>Q'" by(simp add: fresh_list_cons)+
        
        with A `distinct A\<^isub>Q` have "y \<sharp> A\<^isub>Q'" 
          by(induct A\<^isub>Q') (auto simp add: fresh_list_nil fresh_list_cons)

        from `x \<sharp> P` `y \<sharp> P` `x \<noteq> y` `\<Psi> \<otimes> \<Psi>\<^isub>Q \<rhd> P \<longmapsto>M\<lparr>N\<rparr> \<prec> P'`
        have "\<Psi> \<otimes> \<Psi>\<^isub>Q \<rhd> P \<longmapsto>M\<lparr>([(y, x)] \<bullet> N)\<rparr> \<prec> [(y, x)] \<bullet> P'"
          by(rule_tac xvec="[y]" in inputAlpha) (auto simp add: calc_atm)
        hence "\<Psi> \<otimes> \<Psi>\<^isub>Q \<rhd> P \<longmapsto>M\<lparr>([(x, y)] \<bullet> N)\<rparr> \<prec> [(x, y)] \<bullet> P'"
          by(simp add: name_swap)
        moreover note FrP
        moreover from  `\<Psi> \<otimes> \<Psi>\<^isub>P \<rhd> Q \<longmapsto>M'\<lparr>\<nu>*xvec\<rparr>\<langle>N\<rangle> \<prec> Q'` have "([(x, y)] \<bullet> (\<Psi> \<otimes> \<Psi>\<^isub>P)) \<rhd> ([(x, y)] \<bullet> Q) \<longmapsto>([(x, y)] \<bullet> (M'\<lparr>\<nu>*xvec\<rparr>\<langle>N\<rangle> \<prec> Q'))" 
          by(rule semantics.eqvt)
        with `x \<sharp> \<Psi>` `y \<sharp> \<Psi>` `x \<sharp> \<Psi>\<^isub>P` `y \<sharp> \<Psi>\<^isub>P` `x \<sharp> M'` `y \<sharp> M'` `x \<sharp> xvec` `y \<sharp> xvec`
        have "\<Psi> \<otimes> \<Psi>\<^isub>P \<rhd> ([(x, y)] \<bullet> Q) \<longmapsto>M'\<lparr>\<nu>*xvec\<rparr>\<langle>([(x, y)] \<bullet> N)\<rangle> \<prec> ([(x, y)] \<bullet> Q')" 
          by(simp add: eqvts)
        moreover from A `A\<^isub>Q \<sharp>* x` FrxQ have FrQ: "extractFrame([(x, y)] \<bullet> Q) = \<langle>A\<^isub>Q', \<Psi>\<^isub>Q\<rangle>"
          by(clarsimp simp add: alpha' eqvts frame.inject fresh_list_cons name_swap)
        moreover from `A\<^isub>P \<sharp>* Q` have "([(x, y)] \<bullet> A\<^isub>P) \<sharp>* ([(x, y)] \<bullet> Q)" by(simp add: pt_fresh_star_bij[OF pt_name_inst, OF at_name_inst])
        with `A\<^isub>P \<sharp>* x` `y \<sharp> A\<^isub>P` have "A\<^isub>P \<sharp>* ([(x, y)] \<bullet> Q)" by simp
        moreover from `A\<^isub>Q' \<sharp>* Q` have "([(x, y)] \<bullet> A\<^isub>Q') \<sharp>* ([(x, y)] \<bullet> Q)" by(simp add: pt_fresh_star_bij[OF pt_name_inst, OF at_name_inst])
        with `x \<sharp> A\<^isub>Q'` `y \<sharp> A\<^isub>Q'` have "A\<^isub>Q' \<sharp>* ([(x, y)] \<bullet> Q)" by simp
        ultimately have "\<Psi> \<rhd> (P \<parallel> ([(x, y)] \<bullet> Q)) \<longmapsto>\<tau> \<prec> \<lparr>\<nu>*xvec\<rparr>([(x, y)] \<bullet> P') \<parallel> ([(x, y)] \<bullet> Q')"
          using MeqM' `A\<^isub>P \<sharp>* \<Psi>` `A\<^isub>P \<sharp>* P`  `A\<^isub>P \<sharp>* A\<^isub>Q'` `A\<^isub>Q' \<sharp>* \<Psi>` `A\<^isub>Q' \<sharp>* P` `xvec \<sharp>* P` `A\<^isub>P \<sharp>* M` `A\<^isub>Q' \<sharp>* M'`
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
      case(cComm2 \<Psi>\<^isub>Q M xvec N P' A\<^isub>P \<Psi>\<^isub>P K xQ' A\<^isub>Q)
      have QTrans: "\<Psi> \<otimes> \<Psi>\<^isub>P \<rhd> \<lparr>\<nu>x\<rparr>Q \<longmapsto>K\<lparr>N\<rparr> \<prec> xQ'" and FrQ: "extractFrame(\<lparr>\<nu>x\<rparr>Q) = \<langle>A\<^isub>Q, \<Psi>\<^isub>Q\<rangle>" by fact+
      have PTrans: "\<Psi> \<otimes> \<Psi>\<^isub>Q \<rhd> P \<longmapsto>M\<lparr>\<nu>*xvec\<rparr>\<langle>N\<rangle> \<prec> P'" and FrP: "extractFrame P = \<langle>A\<^isub>P, \<Psi>\<^isub>P\<rangle>" by fact+
      from PTrans `x \<sharp> P` have "x \<sharp> N" and "x \<sharp> P'" using `xvec \<sharp>* x` `xvec \<sharp>* M` `distinct xvec` 
        by(force intro: outputFreshDerivative)+
      have "x \<sharp> \<lparr>\<nu>x\<rparr>Q" by(simp add: abs_fresh)
      with FrQ `A\<^isub>Q \<sharp>* x` have "x \<sharp> \<Psi>\<^isub>Q"
        by(drule_tac extractFrameFresh) auto
      from `x \<sharp> P` FrP `A\<^isub>P \<sharp>* x` have "x \<sharp> \<Psi>\<^isub>P"
        by(drule_tac extractFrameFresh) auto
      from `A\<^isub>P \<sharp>* \<lparr>\<nu>x\<rparr>Q` `A\<^isub>P \<sharp>* x` have "A\<^isub>P \<sharp>* Q" by simp
      from `A\<^isub>Q \<sharp>* \<lparr>\<nu>x\<rparr>Q` `A\<^isub>Q \<sharp>* x` have "A\<^isub>Q \<sharp>* Q" by simp
      from `xvec \<sharp>* x` `xvec \<sharp>* \<lparr>\<nu>x\<rparr>Q` have "xvec \<sharp>* Q" by simp

      from PTrans FrP `distinct A\<^isub>P` `x \<sharp> P` `A\<^isub>Q \<sharp>* P` `A\<^isub>P \<sharp>* \<Psi>` `A\<^isub>P \<sharp>* \<Psi>\<^isub>Q` `A\<^isub>P \<sharp>* x` `A\<^isub>P \<sharp>* A\<^isub>Q` `A\<^isub>P \<sharp>* P`  `A\<^isub>P \<sharp>* M` `xvec \<sharp>* M` `distinct xvec`
      obtain M' where "(\<Psi> \<otimes> \<Psi>\<^isub>Q) \<otimes> \<Psi>\<^isub>P \<turnstile> M \<leftrightarrow> M'" and "x \<sharp> M'" and "A\<^isub>Q \<sharp>* M'"
        by(rule_tac B="x#A\<^isub>Q" in obtainPrefix) (assumption | force simp add: fresh_star_list_cons)+
      hence MeqM': "\<Psi> \<otimes> \<Psi>\<^isub>P \<otimes> \<Psi>\<^isub>Q \<turnstile> M \<leftrightarrow> M'"
        by(metis statEqEnt Associativity Commutativity Composition)
      with `\<Psi> \<otimes> \<Psi>\<^isub>P \<otimes> \<Psi>\<^isub>Q \<turnstile> M \<leftrightarrow> K` have "\<Psi> \<otimes> \<Psi>\<^isub>P \<otimes> \<Psi>\<^isub>Q \<turnstile> K \<leftrightarrow> M'"
        by(blast intro: chanEqTrans chanEqSym)
      hence "(\<Psi> \<otimes> \<Psi>\<^isub>P) \<otimes> \<Psi>\<^isub>Q \<turnstile> K \<leftrightarrow> M'"
        by(metis statEqEnt Associativity Commutativity Composition)
      with QTrans FrQ `distinct A\<^isub>Q` `A\<^isub>Q \<sharp>* \<Psi>` `A\<^isub>Q \<sharp>* \<Psi>\<^isub>P` `A\<^isub>Q \<sharp>* (\<lparr>\<nu>x\<rparr>Q)` `A\<^isub>Q \<sharp>* K` `A\<^isub>Q \<sharp>* M'`
      have "\<Psi> \<otimes> \<Psi>\<^isub>P \<rhd> \<lparr>\<nu>x\<rparr>Q \<longmapsto>M'\<lparr>N\<rparr> \<prec> xQ'" by(force intro: inputRenameSubject)

      moreover from `x \<sharp> \<Psi>` `x \<sharp> \<Psi>\<^isub>P` have "x \<sharp> \<Psi> \<otimes> \<Psi>\<^isub>P" by force
      moreover note `x \<sharp> M'` `x \<sharp> N` 
      moreover from QTrans `x \<sharp> N` have "x \<sharp> xQ'" by(force dest: inputFreshDerivative simp add: abs_fresh)
      ultimately show ?case
      proof(induct rule: resInputCases)
        case(cRes Q')   
        have QTrans: "\<Psi> \<otimes> \<Psi>\<^isub>P \<rhd> Q \<longmapsto>M'\<lparr>N\<rparr> \<prec> Q'" by fact
        with `A\<^isub>Q \<sharp>* Q` `A\<^isub>Q \<sharp>* N` have "A\<^isub>Q \<sharp>* Q'"
          by(rule_tac inputFreshChainDerivative)

        with `extractFrame(\<lparr>\<nu>x\<rparr>Q) = \<langle>A\<^isub>Q, \<Psi>\<^isub>Q\<rangle>` have FrxQ: "\<lparr>\<nu>x\<rparr>(extractFrame Q) = \<langle>A\<^isub>Q, \<Psi>\<^isub>Q\<rangle>" by simp
        then obtain y A\<^isub>Q' where A: "A\<^isub>Q = y#A\<^isub>Q'" by(case_tac A\<^isub>Q) auto
        with `A\<^isub>Q \<sharp>* \<Psi>` `A\<^isub>Q \<sharp>* P` `A\<^isub>Q \<sharp>* P'` `A\<^isub>Q \<sharp>* \<Psi>\<^isub>P` `A\<^isub>Q \<sharp>* Q` `A\<^isub>Q \<sharp>* xvec` `A\<^isub>Q \<sharp>* M'` `A\<^isub>Q \<sharp>* Q'` `A\<^isub>Q \<sharp>* N`
        have "A\<^isub>Q' \<sharp>* \<Psi>" and "A\<^isub>Q' \<sharp>* P" and "A\<^isub>Q' \<sharp>* \<Psi>\<^isub>P" and "A\<^isub>Q' \<sharp>* Q" and "A\<^isub>Q \<sharp>* xvec" and "A\<^isub>Q \<sharp>* Q'"
          and "y \<sharp> \<Psi>" and "y \<sharp> P" and "y \<sharp> P'" and "y \<sharp> \<Psi>\<^isub>P" and "y \<sharp> Q" and "y \<sharp> xvec" and "y \<sharp> M'" and "y \<sharp> Q'" and "y \<sharp> N"
          and "A\<^isub>Q' \<sharp>* M'"
          by(simp)+
        from A `A\<^isub>P \<sharp>* A\<^isub>Q` have "A\<^isub>P \<sharp>* A\<^isub>Q'" and "y \<sharp> A\<^isub>P" by(simp add: fresh_star_list_cons)+
        from A `A\<^isub>Q \<sharp>* x` have "x \<noteq> y" and "x \<sharp> A\<^isub>Q'" by(simp add: fresh_list_cons)+
        
        with A `distinct A\<^isub>Q` have "y \<sharp> A\<^isub>Q'" 
          by(induct A\<^isub>Q') (auto simp add: fresh_list_nil fresh_list_cons)

        note PTrans FrP
        moreover from  `\<Psi> \<otimes> \<Psi>\<^isub>P \<rhd> Q \<longmapsto>M'\<lparr>N\<rparr> \<prec> Q'` have "([(x, y)] \<bullet> (\<Psi> \<otimes> \<Psi>\<^isub>P)) \<rhd> ([(x, y)] \<bullet> Q) \<longmapsto>([(x, y)] \<bullet> (M'\<lparr>N\<rparr> \<prec> Q'))" 
          by(rule semantics.eqvt)
        with `x \<sharp> \<Psi>` `y \<sharp> \<Psi>` `x \<sharp> \<Psi>\<^isub>P` `y \<sharp> \<Psi>\<^isub>P` `x \<sharp> M'` `y \<sharp> M'` `x \<sharp> N` `y \<sharp> N`
        have "\<Psi> \<otimes> \<Psi>\<^isub>P \<rhd> ([(x, y)] \<bullet> Q) \<longmapsto>M'\<lparr>N\<rparr> \<prec> ([(x, y)] \<bullet> Q')" 
          by(simp add: eqvts)
        moreover from A `A\<^isub>Q \<sharp>* x` FrxQ have FrQ: "extractFrame([(x, y)] \<bullet> Q) = \<langle>A\<^isub>Q', \<Psi>\<^isub>Q\<rangle>" and "y \<sharp> extractFrame Q"
          by(clarsimp simp add: alpha' eqvts frame.inject fresh_list_cons name_swap)+
        moreover from `A\<^isub>P \<sharp>* Q` have "([(x, y)] \<bullet> A\<^isub>P) \<sharp>* ([(x, y)] \<bullet> Q)" by(simp add: pt_fresh_star_bij[OF pt_name_inst, OF at_name_inst])
        with `A\<^isub>P \<sharp>* x` `y \<sharp> A\<^isub>P` have "A\<^isub>P \<sharp>* ([(x, y)] \<bullet> Q)" by simp
        moreover from `A\<^isub>Q' \<sharp>* Q` have "([(x, y)] \<bullet> A\<^isub>Q') \<sharp>* ([(x, y)] \<bullet> Q)" by(simp add: pt_fresh_star_bij[OF pt_name_inst, OF at_name_inst])
        with `x \<sharp> A\<^isub>Q'` `y \<sharp> A\<^isub>Q'` have "A\<^isub>Q' \<sharp>* ([(x, y)] \<bullet> Q)" by simp
        moreover from `xvec \<sharp>* Q` have "([(x, y)] \<bullet> xvec) \<sharp>* ([(x, y)] \<bullet> Q)" by(simp add: pt_fresh_star_bij[OF pt_name_inst, OF at_name_inst])
        with `xvec \<sharp>* x` `y \<sharp> xvec` have "xvec \<sharp>* ([(x, y)] \<bullet> Q)" by simp
        ultimately have "\<Psi> \<rhd> (P \<parallel> ([(x, y)] \<bullet> Q)) \<longmapsto>\<tau> \<prec> \<lparr>\<nu>*xvec\<rparr>(P' \<parallel> ([(x, y)] \<bullet> Q'))"
          using MeqM' `A\<^isub>P \<sharp>* \<Psi>` `A\<^isub>P \<sharp>* P`  `A\<^isub>P \<sharp>* A\<^isub>Q'` `A\<^isub>Q' \<sharp>* \<Psi>` `A\<^isub>Q' \<sharp>* P` `A\<^isub>P \<sharp>* M` `A\<^isub>Q' \<sharp>* M'`
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
        case(cPar1 P' A\<^isub>Q \<Psi>\<^isub>Q)
        from `y \<sharp> xvec1` `y \<sharp> xvec2` have "y \<sharp> (xvec1@xvec2)" by(auto simp add: fresh_list_append)
        with `\<Psi> \<otimes> \<Psi>\<^isub>Q \<rhd> P \<longmapsto>M\<lparr>\<nu>*(xvec1@xvec2)\<rparr>\<langle>N\<rangle> \<prec> P'` `(xvec1@xvec2) \<sharp>* M` `y \<sharp> P` 
             `distinct xvec1` `distinct xvec2` `xvec1 \<sharp>* xvec2` 
        have "y \<sharp> N" by(force intro: outputFreshDerivative)
        with `y \<in> supp N` have False by(simp add: fresh_def)
        thus ?case by simp
      next
        case(cPar2 Q' A\<^isub>P \<Psi>\<^isub>P)
        have FrP: "extractFrame P = \<langle>A\<^isub>P, \<Psi>\<^isub>P\<rangle>" by fact
        with `y \<sharp> P` `A\<^isub>P \<sharp>* y` have "y \<sharp> \<Psi>\<^isub>P" 
          apply(drule_tac extractFrameFresh)
          by(simp add: frameResChainFresh) (simp add: fresh_def name_list_supp)
        from `\<Psi> \<otimes> \<Psi>\<^isub>P \<rhd> ([(x, y)] \<bullet> Q) \<longmapsto>M\<lparr>\<nu>*(xvec1@xvec2)\<rparr>\<langle>N\<rangle> \<prec> Q'` `y \<in> supp N` `y \<sharp> \<Psi>` `y \<sharp> \<Psi>\<^isub>P` `y \<sharp> M` `y \<sharp> xvec1` `y \<sharp> xvec2`
        have "\<Psi> \<otimes> \<Psi>\<^isub>P \<rhd> \<lparr>\<nu>y\<rparr>(([(x, y)] \<bullet> Q)) \<longmapsto>M\<lparr>\<nu>*(xvec1@y#xvec2)\<rparr>\<langle>N\<rangle> \<prec> Q'" by(force intro: Open) 
        with `y \<sharp> Q` have "\<Psi> \<otimes> \<Psi>\<^isub>P \<rhd> \<lparr>\<nu>x\<rparr>Q \<longmapsto>M\<lparr>\<nu>*(xvec1@y#xvec2)\<rparr>\<langle>N\<rangle> \<prec> Q'"
          by(simp add: alphaRes)
        moreover from `A\<^isub>P \<sharp>* ([(x, y)] \<bullet> Q)` have "A\<^isub>P \<sharp>* \<lparr>\<nu>y\<rparr>([(x, y)] \<bullet> Q)" by(auto simp add: fresh_star_def abs_fresh)
        with `y \<sharp> Q` have "A\<^isub>P \<sharp>* \<lparr>\<nu>x\<rparr>Q" by(simp add: alphaRes)
        ultimately have "\<Psi> \<rhd> P \<parallel> (\<lparr>\<nu>x\<rparr>Q) \<longmapsto>M\<lparr>\<nu>*(xvec1@y#xvec2)\<rparr>\<langle>N\<rangle> \<prec> (P \<parallel> Q')" 
          using FrP `(xvec1@xvec2) \<sharp>* P` `A\<^isub>P \<sharp>* \<Psi>` `A\<^isub>P \<sharp>* M` `y \<sharp> P` `A\<^isub>P \<sharp>* (xvec1@xvec2)` `A\<^isub>P \<sharp>* y` `A\<^isub>P \<sharp>* N`
          by(rule_tac Par2) auto
        moreover have "(\<Psi>, P \<parallel> Q', P \<parallel> Q') \<in> Rel" by(rule C1)
        ultimately show ?case by blast
      qed
    next
      case(cRes PQ)
      from `\<Psi> \<rhd> P \<parallel> Q \<longmapsto>\<alpha> \<prec> PQ` `bn \<alpha> \<sharp>* \<Psi>`  `bn \<alpha> \<sharp>* P` `bn \<alpha> \<sharp>* Q` `bn \<alpha> \<sharp>* subject \<alpha>`
      show ?case
      proof(induct rule: parCases[where C=x])
        case(cPar1 P' A\<^isub>Q \<Psi>\<^isub>Q)
        note `\<Psi> \<otimes> \<Psi>\<^isub>Q \<rhd> P \<longmapsto>\<alpha> \<prec> P'`
        moreover with `x \<sharp> P` `x \<sharp> \<alpha>` `bn \<alpha> \<sharp>* subject \<alpha>` `distinct(bn \<alpha>)`
        have "x \<sharp> P'" by(force dest: freeFreshDerivative)
        with `extractFrame Q = \<langle>A\<^isub>Q, \<Psi>\<^isub>Q\<rangle>` have "extractFrame(\<lparr>\<nu>x\<rparr>Q) = \<langle>(x#A\<^isub>Q), \<Psi>\<^isub>Q\<rangle>"
          by simp
        moreover from `bn \<alpha> \<sharp>* Q` have "bn \<alpha> \<sharp>* (\<lparr>\<nu>x\<rparr>Q)" by(simp add: fresh_star_def abs_fresh)
        moreover from `x \<sharp> \<Psi>` `A\<^isub>Q \<sharp>* \<Psi>` have "(x#A\<^isub>Q) \<sharp>* \<Psi>" by simp
        moreover from `x \<sharp> P` `A\<^isub>Q \<sharp>* P` have "(x#A\<^isub>Q) \<sharp>* P" by simp
        moreover from `x \<sharp> \<alpha>` `A\<^isub>Q \<sharp>* \<alpha>` have "(x#A\<^isub>Q) \<sharp>* \<alpha>" by simp
        ultimately have "\<Psi> \<rhd> P \<parallel> \<lparr>\<nu>x\<rparr>Q \<longmapsto>\<alpha> \<prec> (P' \<parallel> \<lparr>\<nu>x\<rparr>Q)"
          by(rule Par1)
        moreover from `x \<sharp> P'` `x \<sharp> \<Psi>` have "(\<Psi>, \<lparr>\<nu>*[]\<rparr>(P' \<parallel> (\<lparr>\<nu>x\<rparr>Q)), \<lparr>\<nu>x\<rparr>(\<lparr>\<nu>*[]\<rparr>(P' \<parallel> Q))) \<in> Rel"
          by(rule_tac C2) auto
        ultimately show ?case
          by force
      next
        case(cPar2 Q' A\<^isub>P \<Psi>\<^isub>P)
        have FrP: "extractFrame P = \<langle>A\<^isub>P, \<Psi>\<^isub>P\<rangle>" by fact
        with `x \<sharp> P` `A\<^isub>P \<sharp>* x` have "x \<sharp> \<Psi>\<^isub>P"
          apply(drule_tac extractFrameFresh)
          by(simp add: frameResChainFresh) (simp add: fresh_def name_list_supp)
        from `\<Psi> \<otimes> \<Psi>\<^isub>P \<rhd> Q \<longmapsto>\<alpha> \<prec> Q'` `x \<sharp> \<Psi>` `x \<sharp> \<Psi>\<^isub>P` `x \<sharp> \<alpha>`
        have "\<Psi> \<otimes> \<Psi>\<^isub>P \<rhd> \<lparr>\<nu>x\<rparr>Q \<longmapsto>\<alpha> \<prec> \<lparr>\<nu>x\<rparr>Q'"
          by(rule_tac Scope) auto
        moreover note FrP `bn \<alpha> \<sharp>* P` `A\<^isub>P \<sharp>* \<Psi>`
        moreover from `A\<^isub>P \<sharp>* Q` have "A\<^isub>P \<sharp>* \<lparr>\<nu>x\<rparr>Q" by(simp add: fresh_star_def abs_fresh)
        ultimately have "\<Psi> \<rhd> P \<parallel> \<lparr>\<nu>x\<rparr>Q \<longmapsto>\<alpha> \<prec> (P \<parallel> \<lparr>\<nu>x\<rparr>Q')" using `A\<^isub>P \<sharp>* \<alpha>`
          by(rule Par2)
        moreover from `x \<sharp> P` `x \<sharp> \<Psi>` have "(\<Psi>, \<lparr>\<nu>*[]\<rparr>(P \<parallel> (\<lparr>\<nu>x\<rparr>Q')), \<lparr>\<nu>x\<rparr>(\<lparr>\<nu>*[]\<rparr>(P \<parallel> Q'))) \<in> Rel"
          by(rule_tac C2) auto
        ultimately show ?case
          by force
      next
        case(cComm1 \<Psi>\<^isub>Q M N P' A\<^isub>P \<Psi>\<^isub>P K xvec Q' A\<^isub>Q)
        have PTrans: "\<Psi> \<otimes> \<Psi>\<^isub>Q \<rhd> P \<longmapsto>M\<lparr>N\<rparr> \<prec> P'" and FrP: "extractFrame P = \<langle>A\<^isub>P, \<Psi>\<^isub>P\<rangle>" by fact+
        have QTrans: "\<Psi> \<otimes> \<Psi>\<^isub>P \<rhd> Q \<longmapsto>K\<lparr>\<nu>*xvec\<rparr>\<langle>N\<rangle> \<prec> Q'" and FrQ: "extractFrame Q = \<langle>A\<^isub>Q, \<Psi>\<^isub>Q\<rangle>" by fact+
        from FrP `x \<sharp> P` have "x \<sharp> \<langle>A\<^isub>P, \<Psi>\<^isub>P\<rangle>" by(drule_tac extractFrameFresh) simp
        with `A\<^isub>P \<sharp>* x` have "x \<sharp> \<Psi>\<^isub>P" by(simp add: frameResChainFresh) (simp add: fresh_def name_list_supp)
        from PTrans FrP `distinct A\<^isub>P` `x \<sharp> P` `A\<^isub>P \<sharp>* \<Psi>` `A\<^isub>P \<sharp>* \<Psi>\<^isub>Q` `A\<^isub>P \<sharp>* x` `A\<^isub>P \<sharp>* P` `A\<^isub>P \<sharp>* M` `A\<^isub>Q \<sharp>* P` `A\<^isub>P \<sharp>* A\<^isub>Q`
        obtain M' where MeqM': "(\<Psi> \<otimes> \<Psi>\<^isub>Q) \<otimes> \<Psi>\<^isub>P \<turnstile> M \<leftrightarrow> M'" and "x \<sharp> M'" and "A\<^isub>Q \<sharp>* M'"
          by(rule_tac B="x#A\<^isub>Q" in obtainPrefix) (assumption | force simp add: fresh_star_list_cons)+
        
        from MeqM' have MeqM': "\<Psi> \<otimes> \<Psi>\<^isub>P \<otimes> \<Psi>\<^isub>Q \<turnstile> M \<leftrightarrow> M'"
          by(metis statEqEnt Associativity Composition Commutativity)
        with `\<Psi> \<otimes> \<Psi>\<^isub>P \<otimes> \<Psi>\<^isub>Q \<turnstile> M \<leftrightarrow> K` have "\<Psi> \<otimes> \<Psi>\<^isub>P \<otimes> \<Psi>\<^isub>Q \<turnstile> K \<leftrightarrow> M'"
          by(blast intro: chanEqTrans chanEqSym)
        hence "(\<Psi> \<otimes> \<Psi>\<^isub>P) \<otimes> \<Psi>\<^isub>Q \<turnstile> K \<leftrightarrow> M'"
          by(metis statEqEnt Associativity Composition Commutativity)
        with QTrans FrQ `distinct A\<^isub>Q` have QTrans: "\<Psi> \<otimes> \<Psi>\<^isub>P \<rhd> Q \<longmapsto>M'\<lparr>\<nu>*xvec\<rparr>\<langle>N\<rangle> \<prec> Q'" using `A\<^isub>Q \<sharp>* \<Psi>` `A\<^isub>Q \<sharp>* \<Psi>\<^isub>P` `A\<^isub>Q \<sharp>* Q` `A\<^isub>Q \<sharp>* K` `A\<^isub>Q \<sharp>* M'`
          by(rule_tac outputRenameSubject) (assumption | force)+
        show ?case
        proof(case_tac "x \<in> supp N")
          note PTrans FrP
          moreover assume "x \<in> supp N"
          hence "\<Psi> \<otimes> \<Psi>\<^isub>P \<rhd> \<lparr>\<nu>x\<rparr>Q \<longmapsto>M'\<lparr>\<nu>*([]@(x#xvec))\<rparr>\<langle>N\<rangle> \<prec> Q'" using QTrans `x \<sharp> \<Psi>` `x \<sharp> \<Psi>\<^isub>P` `x \<sharp> M'` `xvec \<sharp>* x`
            by(rule_tac Open) (assumption | force simp add: fresh_list_nil)+
          hence QTrans: "\<Psi> \<otimes> \<Psi>\<^isub>P \<rhd> \<lparr>\<nu>x\<rparr>Q \<longmapsto>M'\<lparr>\<nu>*(x#xvec)\<rparr>\<langle>N\<rangle> \<prec> Q'" by simp
          moreover from `extractFrame Q = \<langle>A\<^isub>Q, \<Psi>\<^isub>Q\<rangle>` have "extractFrame(\<lparr>\<nu>x\<rparr>Q) = \<langle>(x#A\<^isub>Q), \<Psi>\<^isub>Q\<rangle>" 
            by simp
          moreover note MeqM' `A\<^isub>P \<sharp>* \<Psi>` `A\<^isub>P \<sharp>* P`
          moreover from  `A\<^isub>P \<sharp>* Q` have "A\<^isub>P \<sharp>* (\<lparr>\<nu>x\<rparr>Q)" by(simp add: fresh_star_def abs_fresh)
          moreover from `A\<^isub>P \<sharp>* A\<^isub>Q` `A\<^isub>P \<sharp>* x` have "A\<^isub>P \<sharp>* (x#A\<^isub>Q)" 
            by(simp add: fresh_star_def fresh_list_cons) (auto simp add: fresh_def name_list_supp)
          moreover from `x \<sharp> \<Psi>` `A\<^isub>Q \<sharp>* \<Psi>` have "(x#A\<^isub>Q) \<sharp>* \<Psi>" by simp
          moreover from `x \<sharp> P` `A\<^isub>Q \<sharp>* P` have "(x#A\<^isub>Q) \<sharp>* P" by simp
          moreover from `x \<sharp> M'` `A\<^isub>Q \<sharp>* M'` have "(x#A\<^isub>Q) \<sharp>* M'" by simp
          moreover from `A\<^isub>Q \<sharp>* Q` have "(x#A\<^isub>Q) \<sharp>* (\<lparr>\<nu>x\<rparr>Q)" by(simp add: fresh_star_def abs_fresh)
          moreover from `x \<sharp> P` `xvec \<sharp>* P` have "(x#xvec) \<sharp>* P" by(simp)
          ultimately have "\<Psi> \<rhd> P \<parallel> \<lparr>\<nu>x\<rparr>Q \<longmapsto>\<tau> \<prec> \<lparr>\<nu>*(x#xvec)\<rparr>(P' \<parallel> Q')" using `A\<^isub>P \<sharp>* M`
            by(rule_tac Comm1) (assumption | simp)+
          moreover have "(\<Psi>, \<lparr>\<nu>x\<rparr>(\<lparr>\<nu>*xvec\<rparr>(P' \<parallel> Q')), \<lparr>\<nu>x\<rparr>(\<lparr>\<nu>*xvec\<rparr>(P' \<parallel> Q'))) \<in> Rel" by(rule C1)
          ultimately show ?case by force
        next
          note PTrans FrP
          moreover assume "x \<notin> supp N"
          hence "x \<sharp> N" by(simp add: fresh_def)
          with QTrans `x \<sharp> \<Psi>` `x \<sharp> \<Psi>\<^isub>P` `x \<sharp> M'` `xvec \<sharp>* x`
          have QTrans: "\<Psi> \<otimes> \<Psi>\<^isub>P \<rhd> \<lparr>\<nu>x\<rparr>Q \<longmapsto>M'\<lparr>\<nu>*xvec\<rparr>\<langle>N\<rangle> \<prec> \<lparr>\<nu>x\<rparr>Q'"
            by(rule_tac Scope) (assumption | force)+
          moreover from PTrans `x \<sharp> P` `x \<sharp> N` have "x \<sharp> P'" by(rule inputFreshDerivative)
          with `extractFrame Q = \<langle>A\<^isub>Q, \<Psi>\<^isub>Q\<rangle>` have "extractFrame(\<lparr>\<nu>x\<rparr>Q) = \<langle>(x#A\<^isub>Q), \<Psi>\<^isub>Q\<rangle>"
            by simp
          moreover note MeqM' `A\<^isub>P \<sharp>* \<Psi>` `A\<^isub>P \<sharp>* P`
          moreover from  `A\<^isub>P \<sharp>* Q` have "A\<^isub>P \<sharp>* (\<lparr>\<nu>x\<rparr>Q)" by(simp add: fresh_star_def abs_fresh)
          moreover from `A\<^isub>P \<sharp>* A\<^isub>Q` `A\<^isub>P \<sharp>* x` have "A\<^isub>P \<sharp>* (x#A\<^isub>Q)" 
            by(simp add: fresh_star_def fresh_list_cons) (auto simp add: fresh_def name_list_supp)
          moreover from `x \<sharp> \<Psi>` `A\<^isub>Q \<sharp>* \<Psi>` have "(x#A\<^isub>Q) \<sharp>* \<Psi>" by simp
          moreover from `x \<sharp> P` `A\<^isub>Q \<sharp>* P` have "(x#A\<^isub>Q) \<sharp>* P" by simp
          moreover from `x \<sharp> M'` `A\<^isub>Q \<sharp>* M'` have "(x#A\<^isub>Q) \<sharp>* M'" by simp
          moreover from `A\<^isub>Q \<sharp>* Q` have "(x#A\<^isub>Q) \<sharp>* (\<lparr>\<nu>x\<rparr>Q)" by(simp add: fresh_star_def abs_fresh)
          moreover from `x \<sharp> P` `xvec \<sharp>* P` have "(x#xvec) \<sharp>* P" by(simp)
          ultimately have "\<Psi> \<rhd> P \<parallel> \<lparr>\<nu>x\<rparr>Q \<longmapsto>\<tau> \<prec> \<lparr>\<nu>*xvec\<rparr>(P' \<parallel> \<lparr>\<nu>x\<rparr>Q')" using `A\<^isub>P \<sharp>* M`
            by(rule_tac Comm1) (assumption | simp)+
          moreover from `x \<sharp> \<Psi>` `x \<sharp> P'` `xvec \<sharp>* \<Psi>` have "(\<Psi>, \<lparr>\<nu>*xvec\<rparr>(P' \<parallel> \<lparr>\<nu>x\<rparr>Q'), \<lparr>\<nu>x\<rparr>(\<lparr>\<nu>*xvec\<rparr>(P' \<parallel> Q'))) \<in> Rel" by(rule C2)
          ultimately show ?case by blast
        qed
      next
        case(cComm2 \<Psi>\<^isub>Q M xvec N P' A\<^isub>P \<Psi>\<^isub>P K Q' A\<^isub>Q)
        have PTrans: "\<Psi> \<otimes> \<Psi>\<^isub>Q \<rhd> P \<longmapsto>M\<lparr>\<nu>*xvec\<rparr>\<langle>N\<rangle> \<prec> P'" and FrP: "extractFrame P = \<langle>A\<^isub>P, \<Psi>\<^isub>P\<rangle>" by fact+
        have QTrans: "\<Psi> \<otimes> \<Psi>\<^isub>P \<rhd> Q \<longmapsto>K\<lparr>N\<rparr> \<prec> Q'" and FrQ: "extractFrame Q = \<langle>A\<^isub>Q, \<Psi>\<^isub>Q\<rangle>" by fact+
        from FrP `x \<sharp> P` have "x \<sharp> \<langle>A\<^isub>P, \<Psi>\<^isub>P\<rangle>" by(drule_tac extractFrameFresh) simp
        with `A\<^isub>P \<sharp>* x` have "x \<sharp> \<Psi>\<^isub>P" by(simp add: frameResChainFresh) (simp add: fresh_def name_list_supp)
        from PTrans FrP `distinct A\<^isub>P` `x \<sharp> P` `A\<^isub>P \<sharp>* \<Psi>` `A\<^isub>P \<sharp>* \<Psi>\<^isub>Q` `A\<^isub>P \<sharp>* x` `A\<^isub>P \<sharp>* P` `A\<^isub>P \<sharp>* M` `A\<^isub>Q \<sharp>* P` `A\<^isub>P \<sharp>* A\<^isub>Q` `xvec \<sharp>* M` `distinct xvec`
        obtain M' where MeqM': "(\<Psi> \<otimes> \<Psi>\<^isub>Q) \<otimes> \<Psi>\<^isub>P \<turnstile> M \<leftrightarrow> M'" and "x \<sharp> M'" and "A\<^isub>Q \<sharp>* M'"
          by(rule_tac B="x#A\<^isub>Q" in obtainPrefix) (assumption | force simp add: fresh_star_list_cons)+
        
        from MeqM' have MeqM': "\<Psi> \<otimes> \<Psi>\<^isub>P \<otimes> \<Psi>\<^isub>Q \<turnstile> M \<leftrightarrow> M'"
          by(metis statEqEnt Associativity Commutativity Composition)
        with `\<Psi> \<otimes> \<Psi>\<^isub>P \<otimes> \<Psi>\<^isub>Q \<turnstile> M \<leftrightarrow> K` have "\<Psi> \<otimes> \<Psi>\<^isub>P \<otimes> \<Psi>\<^isub>Q \<turnstile> K \<leftrightarrow> M'"
          by(blast intro: chanEqTrans chanEqSym)
        hence "(\<Psi> \<otimes> \<Psi>\<^isub>P) \<otimes> \<Psi>\<^isub>Q \<turnstile> K \<leftrightarrow> M'"
          by(metis statEqEnt Associativity Commutativity Composition)
        with QTrans FrQ `distinct A\<^isub>Q` have QTrans: "\<Psi> \<otimes> \<Psi>\<^isub>P \<rhd> Q \<longmapsto>M'\<lparr>N\<rparr> \<prec> Q'" using `A\<^isub>Q \<sharp>* \<Psi>` `A\<^isub>Q \<sharp>* \<Psi>\<^isub>P` `A\<^isub>Q \<sharp>* Q` `A\<^isub>Q \<sharp>* K` `A\<^isub>Q \<sharp>* M'`
          by(rule_tac inputRenameSubject) (assumption | force)+

        from PTrans `x \<sharp> P` `xvec \<sharp>* x` `distinct xvec` `xvec \<sharp>* M`
        have "x \<sharp> N" and "x \<sharp> P'" by(force intro: outputFreshDerivative)+
        from QTrans `x \<sharp> \<Psi>`  `x \<sharp> \<Psi>\<^isub>P` `x \<sharp> M'` `x \<sharp> N` have QTrans: "\<Psi> \<otimes> \<Psi>\<^isub>P \<rhd> \<lparr>\<nu>x\<rparr>Q \<longmapsto>M'\<lparr>N\<rparr> \<prec> \<lparr>\<nu>x\<rparr>Q'"
          by(rule_tac Scope) (assumption | force)+

        note PTrans FrP QTrans
        moreover with `extractFrame Q = \<langle>A\<^isub>Q, \<Psi>\<^isub>Q\<rangle>` have "extractFrame(\<lparr>\<nu>x\<rparr>Q) = \<langle>(x#A\<^isub>Q), \<Psi>\<^isub>Q\<rangle>"
          by simp
        moreover note MeqM' `A\<^isub>P \<sharp>* \<Psi>` `A\<^isub>P \<sharp>* P`
        moreover from  `A\<^isub>P \<sharp>* Q` have "A\<^isub>P \<sharp>* (\<lparr>\<nu>x\<rparr>Q)" by(simp add: fresh_star_def abs_fresh)
        moreover from `A\<^isub>P \<sharp>* A\<^isub>Q` `A\<^isub>P \<sharp>* x` have "A\<^isub>P \<sharp>* (x#A\<^isub>Q)" 
          by(simp add: fresh_star_def fresh_list_cons) (auto simp add: fresh_def name_list_supp)
        moreover from `x \<sharp> \<Psi>` `A\<^isub>Q \<sharp>* \<Psi>` have "(x#A\<^isub>Q) \<sharp>* \<Psi>" by simp
        moreover from `x \<sharp> P` `A\<^isub>Q \<sharp>* P` have "(x#A\<^isub>Q) \<sharp>* P" by simp
        moreover from `x \<sharp> M'` `A\<^isub>Q \<sharp>* M'` have "(x#A\<^isub>Q) \<sharp>* M'" by simp
        moreover from `A\<^isub>Q \<sharp>* Q` have "(x#A\<^isub>Q) \<sharp>* (\<lparr>\<nu>x\<rparr>Q)" by(simp add: fresh_star_def abs_fresh)
        moreover from `xvec \<sharp>* Q` have "(x#xvec) \<sharp>* (\<lparr>\<nu>x\<rparr>Q)" by(simp add: abs_fresh fresh_star_def)
        ultimately have "\<Psi> \<rhd> P \<parallel> \<lparr>\<nu>x\<rparr>Q \<longmapsto>\<tau> \<prec> \<lparr>\<nu>*xvec\<rparr>(P' \<parallel> \<lparr>\<nu>x\<rparr>Q')" using `A\<^isub>P \<sharp>* M`
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
    case(cPar1 Q' A\<^isub>P \<Psi>\<^isub>P)
    from `\<Psi> \<otimes> \<Psi>\<^isub>P \<rhd> Q \<longmapsto>\<alpha>\<prec> Q'` `extractFrame P = \<langle>A\<^isub>P, \<Psi>\<^isub>P\<rangle>` `bn \<alpha> \<sharp>* P` `A\<^isub>P \<sharp>* \<Psi>` `A\<^isub>P \<sharp>* Q` `A\<^isub>P \<sharp>* \<alpha>` 
    have "\<Psi> \<rhd> P \<parallel> Q \<longmapsto>\<alpha> \<prec> (P \<parallel> Q')" by(rule Par2)
    moreover have "(\<Psi>, P \<parallel> Q', Q' \<parallel> P) \<in> Rel" by(rule C1)
    ultimately show ?case by blast
  next
    case(cPar2 P' A\<^isub>Q \<Psi>\<^isub>Q)
    from `\<Psi> \<otimes> \<Psi>\<^isub>Q \<rhd> P \<longmapsto>\<alpha> \<prec> P'` `extractFrame Q = \<langle>A\<^isub>Q, \<Psi>\<^isub>Q\<rangle>` `bn \<alpha> \<sharp>* Q` `A\<^isub>Q \<sharp>* \<Psi>` `A\<^isub>Q \<sharp>* P` `A\<^isub>Q \<sharp>* \<alpha>` 
    have "\<Psi> \<rhd> P \<parallel> Q \<longmapsto>\<alpha> \<prec> (P' \<parallel> Q)" by(rule Par1)
    moreover have "(\<Psi>, P' \<parallel> Q, Q \<parallel> P') \<in> Rel" by(rule C1)
    ultimately show ?case by blast
  next
    case(cComm1 \<Psi>\<^isub>P M N Q' A\<^isub>Q \<Psi>\<^isub>Q K xvec P' A\<^isub>P)
    note `\<Psi> \<otimes> \<Psi>\<^isub>Q \<rhd> P \<longmapsto>K\<lparr>\<nu>*xvec\<rparr>\<langle>N\<rangle> \<prec> P'` `extractFrame P = \<langle>A\<^isub>P, \<Psi>\<^isub>P\<rangle>`
         `\<Psi> \<otimes> \<Psi>\<^isub>P \<rhd> Q \<longmapsto>M\<lparr>N\<rparr> \<prec> Q'` `extractFrame Q = \<langle>A\<^isub>Q, \<Psi>\<^isub>Q\<rangle>`
    moreover from `\<Psi> \<otimes> \<Psi>\<^isub>Q \<otimes> \<Psi>\<^isub>P \<turnstile> M \<leftrightarrow> K`
    have "\<Psi> \<otimes> \<Psi>\<^isub>Q \<otimes> \<Psi>\<^isub>P \<turnstile> K \<leftrightarrow> M"
      by(rule chanEqSym)
    hence "\<Psi> \<otimes> \<Psi>\<^isub>P \<otimes> \<Psi>\<^isub>Q \<turnstile> K \<leftrightarrow> M"
      by(blast intro: statEqEnt compositionSym Commutativity)
    ultimately have "\<Psi> \<rhd> P \<parallel> Q \<longmapsto>\<tau> \<prec> \<lparr>\<nu>*xvec\<rparr>(P' \<parallel> Q')"
      using `A\<^isub>P \<sharp>* \<Psi>` `A\<^isub>P \<sharp>* P` `A\<^isub>P \<sharp>* Q` `A\<^isub>Q \<sharp>* A\<^isub>P` `A\<^isub>Q \<sharp>* \<Psi>` `A\<^isub>Q \<sharp>* P` `A\<^isub>Q \<sharp>* Q` `xvec \<sharp>* Q` `A\<^isub>P \<sharp>* K` `A\<^isub>Q \<sharp>* M`
      by(rule_tac Comm2) (assumption | simp)+
    moreover have "(\<Psi>, P' \<parallel> Q', Q' \<parallel> P') \<in> Rel" by(rule C1)
    hence "(\<Psi>, \<lparr>\<nu>*xvec\<rparr>(P' \<parallel> Q'), \<lparr>\<nu>*xvec\<rparr>(Q' \<parallel> P')) \<in> Rel" using `xvec \<sharp>* \<Psi>` by(rule C2)
    ultimately show ?case by blast
  next
    case(cComm2 \<Psi>\<^isub>P M xvec N Q' A\<^isub>Q \<Psi>\<^isub>Q K P' A\<^isub>P)
    note `\<Psi> \<otimes> \<Psi>\<^isub>Q \<rhd> P \<longmapsto>K\<lparr>N\<rparr> \<prec> P'` `extractFrame P = \<langle>A\<^isub>P, \<Psi>\<^isub>P\<rangle>`
         `\<Psi> \<otimes> \<Psi>\<^isub>P \<rhd> Q \<longmapsto>M\<lparr>\<nu>*xvec\<rparr>\<langle>N\<rangle> \<prec> Q'` `extractFrame Q = \<langle>A\<^isub>Q, \<Psi>\<^isub>Q\<rangle>`
    moreover from `\<Psi> \<otimes> \<Psi>\<^isub>Q \<otimes> \<Psi>\<^isub>P \<turnstile> M \<leftrightarrow> K`
    have "\<Psi> \<otimes> \<Psi>\<^isub>Q \<otimes> \<Psi>\<^isub>P \<turnstile> K \<leftrightarrow> M"
      by(rule chanEqSym)
    hence "\<Psi> \<otimes> \<Psi>\<^isub>P \<otimes> \<Psi>\<^isub>Q \<turnstile> K \<leftrightarrow> M"
      by(blast intro: statEqEnt compositionSym Commutativity)
    ultimately have "\<Psi> \<rhd> P \<parallel> Q \<longmapsto>\<tau> \<prec> \<lparr>\<nu>*xvec\<rparr>(P' \<parallel> Q')"
      using `A\<^isub>P \<sharp>* \<Psi>` `A\<^isub>P \<sharp>* P` `A\<^isub>P \<sharp>* Q` `A\<^isub>Q \<sharp>* A\<^isub>P` `A\<^isub>Q \<sharp>* \<Psi>` `A\<^isub>Q \<sharp>* P` `A\<^isub>Q \<sharp>* Q` `xvec \<sharp>* P` `A\<^isub>P \<sharp>* K` `A\<^isub>Q \<sharp>* M`
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