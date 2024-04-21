theory Sim_Struct_Cong
  imports Simulation "HOL-Library.Multiset"
begin

text \<open>This file is a (heavily modified) variant of the theory {\it Psi\_Calculi.Sim\_Struct\_Cong}
from~\cite{DBLP:journals/afp/Bengtson12}.\<close>

lemma partitionListLeft:
  assumes "xs@ys=xs'@y#ys'"
    and   "y \<in> set xs"
    and   "distinct(xs@ys)"

obtains zs where "xs = xs'@y#zs" and "ys'=zs@ys"
  using assms
  by(force simp add: append_eq_append_conv2 append_eq_Cons_conv)

lemma partitionListRight:

assumes "xs@ys=xs'@y#ys'"
  and   "y \<in> set ys"
  and   "distinct(xs@ys)"

obtains zs where "xs' = xs@zs" and "ys=zs@y#ys'"
  using assms
  by(force simp add: append_eq_append_conv2 append_eq_Cons_conv)

context env begin

lemma resOutputCases''''[consumes 8, case_names cOpen cRes]:
  fixes \<Psi>    :: 'b
    and x    :: name
    and zvec :: "name list"
    and P    :: "('a, 'b, 'c) psi"
    and \<alpha>    :: "'a action"
    and P'   :: "('a, 'b, 'c) psi"
    and C    :: "'f::fs_name"

assumes Trans: "\<Psi> \<rhd> \<lparr>\<nu>x\<rparr>P \<longmapsto>\<alpha> \<prec> P'"
  and   1: "x \<sharp> \<Psi>"
  and   2: "x \<sharp> \<alpha>"
  and   3: "x \<sharp> P'"
  and   4: "bn \<alpha> \<sharp>* \<Psi>"
  and   5: "bn \<alpha> \<sharp>* P"
  and   6: "bn \<alpha> \<sharp>* subject \<alpha>"
  and   "\<alpha> = M\<lparr>\<nu>*zvec\<rparr>\<langle>N\<rangle>"
  and   rOpen: "\<And>M xvec yvec y N P'. \<lbrakk>\<Psi> \<rhd> ([(x, y)] \<bullet> P) \<longmapsto>M\<lparr>\<nu>*(xvec@yvec)\<rparr>\<langle>N\<rangle> \<prec> P'; y \<in> supp N;
                                         x \<sharp> N; x \<sharp> P'; x \<noteq> y; y \<sharp> xvec; y \<sharp> yvec; y \<sharp> M; distinct xvec; distinct yvec;
                                         xvec \<sharp>* \<Psi>; y \<sharp> \<Psi>; yvec \<sharp>* \<Psi>; xvec \<sharp>* P; y \<sharp> P; yvec \<sharp>* P; xvec \<sharp>* M; y \<sharp> M;
                                         yvec \<sharp>* M; xvec \<sharp>* yvec\<rbrakk> \<Longrightarrow>
                                         Prop (M\<lparr>\<nu>*(xvec@y#yvec)\<rparr>\<langle>N\<rangle>) P'"
  and   rScope:  "\<And>P'. \<lbrakk>\<Psi> \<rhd> P \<longmapsto>\<alpha> \<prec> P'\<rbrakk> \<Longrightarrow> Prop \<alpha> (\<lparr>\<nu>x\<rparr>P')"

shows "Prop \<alpha> P'"
proof -
  from Trans have "distinct (bn \<alpha>)" by(auto dest: boundOutputDistinct)
  show ?thesis using Trans 1 2 3 4 5 6 \<open>\<alpha>=M\<lparr>\<nu>*zvec\<rparr>\<langle>N\<rangle>\<close> rOpen rScope
  proof(induct rule: resCases'[where C="(zvec, C)"])
    case cBrOpen
    then show ?case
      by(auto simp add: residualInject boundOutputApp)
  next
    case cRes
    then show ?case
      by(auto simp add: residualInject boundOutputApp)
  next
    case cBrClose
    then show ?case
      by(auto simp add: residualInject boundOutputApp)
  next
    case(cOpen M' xvec yvec y N' P')
    show ?case
      using \<open>\<Psi> \<rhd> [(x, y)] \<bullet> P \<longmapsto> M'\<lparr>\<nu>*(xvec @ yvec)\<rparr>\<langle>N'\<rangle> \<prec> P'\<close> \<open>y \<in> supp N'\<close> \<open>x \<sharp> N'\<close> \<open>x \<sharp> P'\<close>
        \<open>x \<noteq> y\<close> \<open>y \<sharp> xvec\<close> \<open>y \<sharp> yvec\<close> \<open>y \<sharp> M'\<close> \<open>distinct xvec\<close> \<open>distinct yvec\<close> \<open>xvec \<sharp>* \<Psi>\<close>
        \<open>y \<sharp> \<Psi>\<close> \<open>yvec \<sharp>* \<Psi>\<close> \<open>xvec \<sharp>* P\<close> \<open>y \<sharp> P\<close> \<open>yvec \<sharp>* P\<close> \<open>xvec \<sharp>* M'\<close> \<open>y \<sharp> M'\<close>
        \<open>yvec \<sharp>* M'\<close> \<open>xvec \<sharp>* yvec\<close>
      by(rule cOpen(22))
  qed
qed

lemma resOutputCases'''''[consumes 7, case_names cOpen cRes]:
  fixes \<Psi>    :: 'b
    and x    :: name
    and zvec :: "name list"
    and P    :: "('a, 'b, 'c) psi"
    and P'   :: "('a, 'b, 'c) psi"
    and C    :: "'f::fs_name"

assumes Trans: "\<Psi> \<rhd> \<lparr>\<nu>x\<rparr>P \<longmapsto>M\<lparr>\<nu>*zvec\<rparr>\<langle>N\<rangle> \<prec> P'"
  and   1: "x \<sharp> \<Psi>"
  and   "x \<sharp> M\<lparr>\<nu>*zvec\<rparr>\<langle>N\<rangle>"
  and   3: "x \<sharp> P'"
  and   "zvec \<sharp>* \<Psi>"
  and   "zvec \<sharp>* P"
  and   "zvec \<sharp>* M"
  and   rOpen: "\<And>M' xvec yvec y N' P'. \<lbrakk>\<Psi> \<rhd> ([(x, y)] \<bullet> P) \<longmapsto>M'\<lparr>\<nu>*(xvec@yvec)\<rparr>\<langle>N'\<rangle> \<prec> P'; y \<in> supp N';
                                         x \<sharp> N'; x \<sharp> P'; x \<noteq> y; y \<sharp> xvec; y \<sharp> yvec; y \<sharp> M'; distinct xvec; distinct yvec;
                                         xvec \<sharp>* \<Psi>; y \<sharp> \<Psi>; yvec \<sharp>* \<Psi>; xvec \<sharp>* P; y \<sharp> P; yvec \<sharp>* P; xvec \<sharp>* M'; y \<sharp> M';
                                         yvec \<sharp>* M'; xvec \<sharp>* yvec; M'\<lparr>\<nu>*(xvec@y#yvec)\<rparr>\<langle>N'\<rangle> = M\<lparr>\<nu>*zvec\<rparr>\<langle>N\<rangle>\<rbrakk> \<Longrightarrow>
                                         Prop P'"
  and   rScope:  "\<And>P'. \<lbrakk>\<Psi> \<rhd> P \<longmapsto>M\<lparr>\<nu>*zvec\<rparr>\<langle>N\<rangle> \<prec> P'\<rbrakk> \<Longrightarrow> Prop (\<lparr>\<nu>x\<rparr>P')"

shows "Prop P'"
proof -
  from Trans have "distinct zvec" by(auto dest: boundOutputDistinct)
  obtain al where "al=M\<lparr>\<nu>*zvec\<rparr>\<langle>N\<rangle>" by simp
  from \<open>al = M\<lparr>\<nu>*zvec\<rparr>\<langle>N\<rangle>\<close> Trans \<open>zvec \<sharp>* \<Psi>\<close> \<open>zvec \<sharp>* P\<close> \<open>zvec \<sharp>* M\<close>
  have \<alpha>Trans: "\<Psi> \<rhd> \<lparr>\<nu>x\<rparr>P \<longmapsto>al \<prec> P'" and 4: "bn al \<sharp>* \<Psi>" and 5: "bn al \<sharp>* P" and 6: "bn al \<sharp>* subject al"
    by simp+
  from \<open>x \<sharp> M\<lparr>\<nu>*zvec\<rparr>\<langle>N\<rangle>\<close> \<open>al=M\<lparr>\<nu>*zvec\<rparr>\<langle>N\<rangle>\<close> have 2: "x \<sharp> al" by simp
  show ?thesis using \<alpha>Trans 1 2 3 4 5 6 \<open>al=M\<lparr>\<nu>*zvec\<rparr>\<langle>N\<rangle>\<close> rOpen rScope
  proof(induct rule: resCases'[where C="(zvec, C)"])
    case cBrOpen
    then show ?case
      by(auto simp add: residualInject boundOutputApp)
  next
    case cBrClose
    then show ?case
      by(auto simp add: residualInject boundOutputApp)
  next
    case(cOpen M' xvec yvec y N' P')
    show ?case
      using \<open>\<Psi> \<rhd> [(x, y)] \<bullet> P \<longmapsto> M'\<lparr>\<nu>*(xvec @ yvec)\<rparr>\<langle>N'\<rangle> \<prec> P'\<close> \<open>y \<in> supp N'\<close> \<open>x \<sharp> N'\<close> \<open>x \<sharp> P'\<close>
        \<open>x \<noteq> y\<close> \<open>y \<sharp> xvec\<close> \<open>y \<sharp> yvec\<close> \<open>y \<sharp> M'\<close> \<open>distinct xvec\<close> \<open>distinct yvec\<close> \<open>xvec \<sharp>* \<Psi>\<close>
        \<open>y \<sharp> \<Psi>\<close> \<open>yvec \<sharp>* \<Psi>\<close> \<open>xvec \<sharp>* P\<close> \<open>y \<sharp> P\<close> \<open>yvec \<sharp>* P\<close> \<open>xvec \<sharp>* M'\<close> \<open>y \<sharp> M'\<close>
        \<open>yvec \<sharp>* M'\<close> \<open>xvec \<sharp>* yvec\<close> \<open>M'\<lparr>\<nu>*(xvec @ y # yvec)\<rparr>\<langle>N'\<rangle> = M\<lparr>\<nu>*zvec\<rparr>\<langle>N\<rangle>\<close>
      by(rule cOpen(22))
  next
    case (cRes P')
    from \<open>\<Psi> \<rhd> P \<longmapsto> al \<prec> P'\<close> \<open>al = M\<lparr>\<nu>*zvec\<rparr>\<langle>N\<rangle>\<close>
    show ?case
      by (simp add: cRes(4))
  qed
qed

lemma resBrOutputCases'[consumes 7, case_names cBrOpen cRes]:
  fixes \<Psi>    :: 'b
    and x    :: name
    and zvec :: "name list"
    and P    :: "('a, 'b, 'c) psi"
    and P'   :: "('a, 'b, 'c) psi"
    and C    :: "'f::fs_name"

assumes Trans: "\<Psi> \<rhd> \<lparr>\<nu>x\<rparr>P \<longmapsto>\<exclamdown>M\<lparr>\<nu>*zvec\<rparr>\<langle>N\<rangle> \<prec> P'"
  and   1: "x \<sharp> \<Psi>"
  and   "x \<sharp> \<exclamdown>M\<lparr>\<nu>*zvec\<rparr>\<langle>N\<rangle>"
  and   3: "x \<sharp> P'"
  and   "zvec \<sharp>* \<Psi>"
  and   "zvec \<sharp>* P"
  and   "zvec \<sharp>* M"
  and   rBrOpen: "\<And>M' xvec yvec y N' P'. \<lbrakk>\<Psi> \<rhd> ([(x, y)] \<bullet> P) \<longmapsto>\<exclamdown>M'\<lparr>\<nu>*(xvec@yvec)\<rparr>\<langle>N'\<rangle> \<prec> P'; y \<in> supp N';
                                         x \<sharp> N'; x \<sharp> P'; x \<noteq> y; y \<sharp> xvec; y \<sharp> yvec; y \<sharp> M'; distinct xvec; distinct yvec;
                                         xvec \<sharp>* \<Psi>; y \<sharp> \<Psi>; yvec \<sharp>* \<Psi>; xvec \<sharp>* P; y \<sharp> P; yvec \<sharp>* P; xvec \<sharp>* M'; y \<sharp> M';
                                         yvec \<sharp>* M'; xvec \<sharp>* yvec; \<exclamdown>M'\<lparr>\<nu>*(xvec@y#yvec)\<rparr>\<langle>N'\<rangle> = \<exclamdown>M\<lparr>\<nu>*zvec\<rparr>\<langle>N\<rangle>\<rbrakk> \<Longrightarrow>
                                         Prop P'"
  and   rScope:  "\<And>P'. \<lbrakk>\<Psi> \<rhd> P \<longmapsto>\<exclamdown>M\<lparr>\<nu>*zvec\<rparr>\<langle>N\<rangle> \<prec> P'\<rbrakk> \<Longrightarrow> Prop (\<lparr>\<nu>x\<rparr>P')"

shows "Prop P'"
proof -
  from Trans have "distinct zvec" by(auto dest: boundOutputDistinct)
  obtain al where "al=\<exclamdown>M\<lparr>\<nu>*zvec\<rparr>\<langle>N\<rangle>" by simp
  from \<open>al = \<exclamdown>M\<lparr>\<nu>*zvec\<rparr>\<langle>N\<rangle>\<close> Trans \<open>zvec \<sharp>* \<Psi>\<close> \<open>zvec \<sharp>* P\<close> \<open>zvec \<sharp>* M\<close>
  have \<alpha>Trans: "\<Psi> \<rhd> \<lparr>\<nu>x\<rparr>P \<longmapsto>al \<prec> P'" and 4: "bn al \<sharp>* \<Psi>" and 5: "bn al \<sharp>* P" and 6: "bn al \<sharp>* subject al"
    by simp+
  from \<open>x \<sharp> \<exclamdown>M\<lparr>\<nu>*zvec\<rparr>\<langle>N\<rangle>\<close> \<open>al=\<exclamdown>M\<lparr>\<nu>*zvec\<rparr>\<langle>N\<rangle>\<close> have 2: "x \<sharp> al" by simp
  show ?thesis using \<alpha>Trans 1 2 3 4 5 6 \<open>al=\<exclamdown>M\<lparr>\<nu>*zvec\<rparr>\<langle>N\<rangle>\<close> rBrOpen rScope
  proof(induct rule: resCases'[where C="(zvec, C)"])
    case cBrOpen
    then show ?case
      by(auto simp add: residualInject boundOutputApp)
  next
    case cBrClose
    then show ?case
      by(auto simp add: residualInject boundOutputApp)
  next
    case(cOpen M' xvec yvec y N' P')
    then show ?case
      by(auto simp add: residualInject boundOutputApp)
  next
    case (cRes P')
    from \<open>\<Psi> \<rhd> P \<longmapsto> al \<prec> P'\<close> \<open>al = \<exclamdown>M\<lparr>\<nu>*zvec\<rparr>\<langle>N\<rangle>\<close>
    show ?case
      by (simp add: cRes(4))
  qed
qed

lemma brOutputFreshSubject:
  fixes x::name
  assumes "\<Psi> \<rhd> P \<longmapsto> \<exclamdown>M\<lparr>\<nu>*xvec\<rparr>\<langle>N\<rangle> \<prec> P'"
    and   "xvec \<sharp>* M"
    and   "x \<sharp> P"
  shows "x \<sharp> M"
  using assms
proof(nominal_induct avoiding: x rule: brOutputInduct')
  case(cAlpha \<Psi> P M xvec N P' p)
  then show ?case by simp
next
  case(cBrOutput \<Psi> M K N P)
  then show ?case
    by(auto simp add: fresh_def psi.supp dest: chanOutConSupp)
next
  case(cCase \<Psi> P M xvec N P' \<phi> Cs) then show ?case
    by(induct Cs) auto
next
  case(cPar1 \<Psi> \<Psi>\<^sub>Q P M xvec N P' A\<^sub>Q Q) then show ?case
    by simp
next
  case cPar2 then show ?case by simp
next
  case cBrComm1 then show ?case by simp
next
  case cBrComm2 then show ?case by simp
next
  case cBrOpen then show ?case by(simp add: fresh_abs_fun_iff[OF pt_name_inst, OF at_name_inst, OF fin_supp])
next
  case cScope then show ?case by(simp add: fresh_abs_fun_iff[OF pt_name_inst, OF at_name_inst, OF fin_supp])
next
  case cBang then show ?case by simp
qed

lemma brInputFreshSubject:
  fixes x::name
  assumes "\<Psi> \<rhd> P \<longmapsto> \<questiondown>M\<lparr>N\<rparr> \<prec> P'"
    and   "x \<sharp> P"
  shows "x \<sharp> M"
  using assms
proof(nominal_induct avoiding: x rule: brInputInduct)
  case(cBrInput \<Psi> K M xvec N Tvec P y)
  then show ?case
    by(auto simp add: fresh_def psi.supp dest: chanInConSupp)
next
  case(cCase \<Psi> P M N P' \<phi> Cs y) then show ?case
    by(induct Cs) auto
next
  case(cPar1 \<Psi> \<Psi>\<^sub>Q P M N P' A\<^sub>Q Q y) then show ?case
    by simp
next
  case cPar2 then show ?case by simp
next
  case cBrMerge then show ?case by simp
next
  case cScope then show ?case by(simp add: fresh_abs_fun_iff[OF pt_name_inst, OF at_name_inst, OF fin_supp])
next
  case cBang then show ?case by simp
qed

lemma resComm:
  fixes \<Psi>   :: 'b
    and x   :: name
    and y   :: name
    and Rel :: "('b \<times> ('a, 'b, 'c) psi \<times> ('a, 'b, 'c) psi) set"
    and P   :: "('a, 'b, 'c) psi"

assumes "x \<sharp> \<Psi>"
  and   "y \<sharp> \<Psi>"
  and   "eqvt Rel"
  and   R1: "\<And>\<Psi>' Q. (\<Psi>', Q, Q) \<in> Rel"
  and   R2: "\<And>\<Psi>' a b Q. \<lbrakk>a \<sharp> \<Psi>'; b \<sharp> \<Psi>'\<rbrakk> \<Longrightarrow> (\<Psi>', \<lparr>\<nu>a\<rparr>(\<lparr>\<nu>b\<rparr>Q), \<lparr>\<nu>b\<rparr>(\<lparr>\<nu>a\<rparr>Q)) \<in> Rel"
  and   R3: "\<And>\<Psi>' xvec yvec Q. \<lbrakk>xvec \<sharp>* \<Psi>'; mset xvec = mset yvec\<rbrakk> \<Longrightarrow> (\<Psi>', \<lparr>\<nu>*xvec\<rparr>Q, \<lparr>\<nu>*yvec\<rparr>Q) \<in> Rel"

shows "\<Psi> \<rhd> \<lparr>\<nu>x\<rparr>(\<lparr>\<nu>y\<rparr>P) \<leadsto>[Rel] \<lparr>\<nu>y\<rparr>(\<lparr>\<nu>x\<rparr>P)"
proof(cases "x=y")
  assume "x = y"
  then show ?thesis using R1
    by(force intro: reflexive)
next
  assume "x \<noteq> y"
  note \<open>eqvt Rel\<close>
  moreover from \<open>x \<sharp> \<Psi>\<close> \<open>y \<sharp> \<Psi>\<close> have "[x, y] \<sharp>* \<Psi>" by(simp add: fresh_star_def)
  moreover have "[x, y] \<sharp>* \<lparr>\<nu>x\<rparr>(\<lparr>\<nu>y\<rparr>P)" by(simp add: abs_fresh)
  moreover have "[x, y] \<sharp>* \<lparr>\<nu>y\<rparr>(\<lparr>\<nu>x\<rparr>P)" by(simp add: abs_fresh)
  ultimately show ?thesis
  proof(induct rule: simIChainFresh[where C="(x, y)"])
    case(cSim \<alpha> P')
    from \<open>bn \<alpha> \<sharp>* (x, y)\<close> \<open>bn \<alpha> \<sharp>* (\<lparr>\<nu>x\<rparr>(\<lparr>\<nu>y\<rparr>P))\<close> have "x \<sharp> bn \<alpha>" and "y \<sharp> bn \<alpha>" and "bn \<alpha> \<sharp>* P" by simp+
    from \<open>[x, y] \<sharp>* \<alpha>\<close> have "x \<sharp> \<alpha>" and "y \<sharp> \<alpha>" by simp+
    from \<open>[x, y] \<sharp>* P'\<close> have "x \<sharp> P'" and "y \<sharp> P'" by simp+
    from \<open>bn \<alpha> \<sharp>* P\<close> \<open>x \<sharp> \<alpha>\<close> have "bn \<alpha> \<sharp>* \<lparr>\<nu>x\<rparr>P" by(simp add: abs_fresh)
    with \<open>\<Psi> \<rhd> \<lparr>\<nu>y\<rparr>(\<lparr>\<nu>x\<rparr>P) \<longmapsto>\<alpha> \<prec> P'\<close> \<open>y \<sharp> \<Psi>\<close> \<open>y \<sharp> \<alpha>\<close> \<open>y \<sharp> P'\<close> \<open>bn \<alpha> \<sharp>* \<Psi>\<close>
    show ?case using \<open>bn \<alpha> \<sharp>* subject \<alpha>\<close> \<open>x \<sharp> \<alpha>\<close> \<open>x \<sharp> P'\<close> \<open>bn \<alpha> \<sharp>* \<Psi>\<close> \<open>bn \<alpha> \<sharp>* P\<close> \<open>bn \<alpha> \<sharp>* subject \<alpha>\<close> \<open>y \<sharp> \<alpha>\<close>
    proof(induct rule: resCases'[where C=x])
      case(cOpen M yvec1 yvec2 y' N P')
      from \<open>yvec1 \<sharp>* yvec2\<close> \<open>distinct yvec1\<close> \<open>distinct yvec2\<close> have "distinct(yvec1@yvec2)" by auto
      from \<open>x \<sharp> M\<lparr>\<nu>*(yvec1 @ y' # yvec2)\<rparr>\<langle>N\<rangle>\<close> have "x \<sharp> M" and "x \<sharp> yvec1" and "x \<noteq> y'" and "x \<sharp> yvec2" and "x \<sharp> N"
        by simp+
      from \<open>y \<sharp> M\<lparr>\<nu>*(yvec1 @ y' # yvec2)\<rparr>\<langle>N\<rangle>\<close> have "y \<sharp> M" and "y \<sharp> yvec1" and "y \<sharp> yvec2"
        by simp+
      from \<open>\<Psi> \<rhd> ([(y, y')] \<bullet> \<lparr>\<nu>x\<rparr>P) \<longmapsto>M\<lparr>\<nu>*(yvec1@yvec2)\<rparr>\<langle>N\<rangle> \<prec> P'\<close> \<open>x \<noteq> y\<close> \<open>x \<noteq> y'\<close>
      have "\<Psi> \<rhd> \<lparr>\<nu>x\<rparr>([(y, y')] \<bullet> P) \<longmapsto>M\<lparr>\<nu>*(yvec1@yvec2)\<rparr>\<langle>N\<rangle> \<prec> P'" by(simp add: eqvts)
      moreover note \<open>x \<sharp> \<Psi>\<close>
      moreover from \<open>x \<sharp> N\<close> \<open>x \<sharp> yvec1\<close> \<open>x \<sharp> yvec2\<close> \<open>x \<sharp> M\<close> have "x \<sharp> M\<lparr>\<nu>*(yvec1@yvec2)\<rparr>\<langle>N\<rangle>" by simp
      moreover note \<open>x \<sharp> P'\<close>
      moreover from \<open>yvec1 \<sharp>* \<Psi>\<close> \<open>yvec2 \<sharp>* \<Psi>\<close> have "(yvec1@yvec2) \<sharp>* \<Psi>" by simp
      moreover from \<open>yvec1 \<sharp>* \<lparr>\<nu>x\<rparr>P\<close> \<open>yvec2 \<sharp>* \<lparr>\<nu>x\<rparr>P\<close> \<open>y \<sharp> yvec1\<close> \<open>y' \<sharp> yvec1\<close> \<open>y \<sharp> yvec2\<close> \<open>y' \<sharp> yvec2\<close> \<open>x \<sharp> yvec1\<close> \<open>x \<sharp> yvec2\<close>
      have "(yvec1@yvec2) \<sharp>* ([(y, y')] \<bullet> P)" by simp
      moreover from \<open>yvec1 \<sharp>* M\<close> \<open>yvec2 \<sharp>* M\<close> have "(yvec1 @ yvec2) \<sharp>* M"
        by simp
      ultimately show ?case
      proof(induct rule: resOutputCases''''')
        case(cOpen M' xvec1 xvec2 x' N' P')
        from \<open>M'\<lparr>\<nu>*(xvec1 @ x' # xvec2)\<rparr>\<langle>N'\<rangle> = M\<lparr>\<nu>*(yvec1 @ yvec2)\<rparr>\<langle>N\<rangle>\<close> have "yvec1@yvec2 = xvec1@x'#xvec2" and "M = M'" and "N = N'" by (simp add: action.inject)+
        from \<open>x \<sharp> yvec1\<close> \<open>x \<sharp> yvec2\<close> \<open>y' \<sharp> yvec1\<close> \<open>y' \<sharp> yvec2\<close> \<open>y \<sharp> yvec1\<close> \<open>y \<sharp> yvec2\<close>
        have "x \<sharp> (yvec1@yvec2)" and "y \<sharp> (yvec1@yvec2)" and "y' \<sharp> (yvec1@yvec2)" by simp+
        with \<open>yvec1@yvec2 = xvec1@x'#xvec2\<close>
        have "x \<sharp> xvec1" and "x \<noteq> x'" and "x \<sharp> xvec2" and "y \<sharp> xvec1" and "y \<noteq> x'" and "y \<sharp> xvec2"
          and "y' \<sharp> xvec1" and "x' \<noteq> y'" and "y' \<sharp> xvec2"
          by auto

        show ?case
        proof(cases "x' \<in> set yvec1")
          assume "x' \<in> set yvec1"

          with \<open>yvec1@yvec2 = xvec1@x'#xvec2\<close> \<open>distinct (yvec1@yvec2)\<close>
          obtain xvec2' where Eq1: "yvec1=xvec1@x'#xvec2'"
            and Eq: "xvec2=xvec2'@yvec2"
            by(metis partitionListLeft)
          from \<open>\<Psi> \<rhd> ([(x, x')] \<bullet> [(y, y')] \<bullet> P) \<longmapsto>M'\<lparr>\<nu>*(xvec1@xvec2)\<rparr>\<langle>N'\<rangle> \<prec> P'\<close> \<open>y' \<in> supp N\<close> \<open>y' \<sharp> \<Psi>\<close> \<open>y' \<sharp> M\<close> \<open>y' \<sharp> xvec1\<close> \<open>y' \<sharp> xvec2\<close> Eq \<open>M=M'\<close> \<open>N = N'\<close>
          have "\<Psi> \<rhd> \<lparr>\<nu>y'\<rparr>([(x, x')] \<bullet> [(y, y')] \<bullet> P) \<longmapsto>M'\<lparr>\<nu>*((xvec1@xvec2')@y'#yvec2)\<rparr>\<langle>N'\<rangle> \<prec> P'"
            by(intro Open) auto
          then have "\<Psi> \<rhd> \<lparr>\<nu>x'\<rparr>(\<lparr>\<nu>y'\<rparr>([(x, x')] \<bullet> [(y, y')] \<bullet> P)) \<longmapsto>M\<lparr>\<nu>*(xvec1@x'#xvec2'@y'#yvec2)\<rparr>\<langle>N\<rangle> \<prec> P'"
            using \<open>x' \<in> supp N'\<close> \<open>x' \<sharp> \<Psi>\<close> \<open>x' \<sharp> M'\<close> \<open>x' \<sharp> xvec1\<close> \<open>x' \<sharp> xvec2\<close> \<open>x' \<noteq> y'\<close> Eq \<open>M=M'\<close> \<open>N=N'\<close>
            by(intro Open) auto
          with \<open>x' \<noteq> y'\<close> \<open>x \<noteq> y'\<close> \<open>x' \<sharp> [(y, y')] \<bullet> P\<close>
          have "\<Psi> \<rhd> \<lparr>\<nu>x\<rparr>(\<lparr>\<nu>y'\<rparr>([(y, y')] \<bullet> P)) \<longmapsto>M\<lparr>\<nu>*(xvec1@x'#xvec2'@y'#yvec2)\<rparr>\<langle>N\<rangle> \<prec> P'"
            by(subst alphaRes[where y=x']) (simp add: calc_atm eqvts abs_fresh)+
          with Eq1 \<open>y' \<sharp> \<lparr>\<nu>x\<rparr>P\<close> \<open>x \<noteq> y'\<close> R1 show ?case
            by(auto simp add: alphaRes abs_fresh)
        next
          assume "\<not>x' \<in> set yvec1"
          then have "x' \<sharp> yvec1" by(simp add: fresh_def)
          from \<open>\<not>x' \<in> set yvec1\<close> \<open>yvec1@yvec2 = xvec1@x'#xvec2\<close>
          have "x' \<in> set yvec2"
            by(auto simp add: append_eq_append_conv2 append_eq_Cons_conv)
          with \<open>yvec1@yvec2 = xvec1@x'#xvec2\<close> \<open>distinct (yvec1@yvec2)\<close>
          obtain xvec2' where Eq: "xvec1=yvec1@xvec2'"
            and Eq1: "yvec2=xvec2'@x'#xvec2"
            by(metis partitionListRight)
          from \<open>\<Psi> \<rhd> ([(x, x')] \<bullet> [(y, y')] \<bullet> P) \<longmapsto>M'\<lparr>\<nu>*(xvec1@xvec2)\<rparr>\<langle>N'\<rangle> \<prec> P'\<close> \<open>y' \<in> supp N\<close> \<open>y' \<sharp> \<Psi>\<close> \<open>y' \<sharp> M\<close> \<open>y' \<sharp> xvec1\<close> \<open>y' \<sharp> xvec2\<close> Eq \<open>M=M'\<close> \<open>N = N'\<close>
          have "\<Psi> \<rhd> \<lparr>\<nu>y'\<rparr>([(x, x')] \<bullet> [(y, y')] \<bullet> P) \<longmapsto>M'\<lparr>\<nu>*(yvec1@y'#xvec2'@xvec2)\<rparr>\<langle>N'\<rangle> \<prec> P'"
            by(intro Open) (assumption | simp)+
          then have "\<Psi> \<rhd> \<lparr>\<nu>x'\<rparr>(\<lparr>\<nu>y'\<rparr>([(x, x')] \<bullet> [(y, y')] \<bullet> P)) \<longmapsto>M\<lparr>\<nu>*((yvec1@y'#xvec2')@x'#xvec2)\<rparr>\<langle>N\<rangle> \<prec> P'"
            using \<open>x' \<in> supp N'\<close> \<open>x' \<sharp> \<Psi>\<close> \<open>x' \<sharp> M'\<close> \<open>x' \<sharp> xvec1\<close> \<open>x' \<sharp> xvec2\<close> \<open>x' \<noteq> y'\<close> Eq \<open>M=M'\<close> \<open>N=N'\<close>
            by(intro Open) auto
          with \<open>x' \<noteq> y'\<close> \<open>x \<noteq> y'\<close> \<open>x' \<sharp> [(y, y')] \<bullet> P\<close>
          have "\<Psi> \<rhd> \<lparr>\<nu>x\<rparr>(\<lparr>\<nu>y'\<rparr>([(y, y')] \<bullet> P)) \<longmapsto>M\<lparr>\<nu>*((yvec1@y'#xvec2')@x'#xvec2)\<rparr>\<langle>N\<rangle> \<prec> P'"
            by(subst alphaRes[where y=x']) (simp add: calc_atm eqvts abs_fresh)+
          with Eq1 \<open>y' \<sharp> \<lparr>\<nu>x\<rparr>P\<close> \<open>x \<noteq> y'\<close> R1 show ?case
            by(auto simp add: alphaRes abs_fresh)
        qed
      next
        case(cRes P')
        from \<open>\<Psi> \<rhd> ([(y, y')] \<bullet> P) \<longmapsto>M\<lparr>\<nu>*(yvec1@yvec2)\<rparr>\<langle>N\<rangle> \<prec> P'\<close> \<open>y' \<in> supp N\<close> \<open>y' \<sharp> \<Psi>\<close> \<open>y' \<sharp> M\<close> \<open>y' \<sharp> yvec1\<close> \<open>y' \<sharp> yvec2\<close>
        have "\<Psi> \<rhd> \<lparr>\<nu>y'\<rparr>([(y, y')] \<bullet> P) \<longmapsto>M\<lparr>\<nu>*(yvec1@y'#yvec2)\<rparr>\<langle>N\<rangle> \<prec> P'" by(rule Open)
        with \<open>y' \<sharp> \<lparr>\<nu>x\<rparr>P\<close> \<open>x \<noteq> y'\<close>have "\<Psi> \<rhd> \<lparr>\<nu>y\<rparr>P \<longmapsto>M\<lparr>\<nu>*(yvec1@y'#yvec2)\<rparr>\<langle>N\<rangle> \<prec> P'" by(simp add: alphaRes abs_fresh)
        then have "\<Psi> \<rhd> \<lparr>\<nu>x\<rparr>(\<lparr>\<nu>y\<rparr>P) \<longmapsto>M\<lparr>\<nu>*(yvec1@y'#yvec2)\<rparr>\<langle>N\<rangle> \<prec> \<lparr>\<nu>x\<rparr>P'" using \<open>x \<sharp> \<Psi>\<close> \<open>x \<sharp> M\<close> \<open>x \<sharp> yvec1\<close> \<open>x \<noteq> y'\<close> \<open>x \<sharp> yvec2\<close> \<open>x \<sharp> N\<close>
          by(intro Scope) auto
        moreover have "(\<Psi>, \<lparr>\<nu>x\<rparr>P', \<lparr>\<nu>x\<rparr>P') \<in> Rel" by(rule R1)
        ultimately show ?case by blast
      qed
    next
      case(cBrOpen M yvec1 yvec2 y' N P')
      from \<open>yvec1 \<sharp>* yvec2\<close> \<open>distinct yvec1\<close> \<open>distinct yvec2\<close> have "distinct(yvec1@yvec2)" by auto
      from \<open>x \<sharp> \<exclamdown>M\<lparr>\<nu>*(yvec1 @ y' # yvec2)\<rparr>\<langle>N\<rangle>\<close> have "x \<sharp> M" and "x \<sharp> yvec1" and "x \<noteq> y'" and "x \<sharp> yvec2" and "x \<sharp> N"
        by simp+
      from \<open>y \<sharp> \<exclamdown>M\<lparr>\<nu>*(yvec1 @ y' # yvec2)\<rparr>\<langle>N\<rangle>\<close> have "y \<sharp> M" and "y \<sharp> yvec1" and "y \<sharp> yvec2"
        by simp+
      from \<open>\<Psi> \<rhd> ([(y, y')] \<bullet> \<lparr>\<nu>x\<rparr>P) \<longmapsto>\<exclamdown>M\<lparr>\<nu>*(yvec1@yvec2)\<rparr>\<langle>N\<rangle> \<prec> P'\<close> \<open>x \<noteq> y\<close> \<open>x \<noteq> y'\<close>
      have "\<Psi> \<rhd> \<lparr>\<nu>x\<rparr>([(y, y')] \<bullet> P) \<longmapsto>\<exclamdown>M\<lparr>\<nu>*(yvec1@yvec2)\<rparr>\<langle>N\<rangle> \<prec> P'" by(simp add: eqvts)
      moreover note \<open>x \<sharp> \<Psi>\<close>
      moreover from \<open>x \<sharp> N\<close> \<open>x \<sharp> yvec1\<close> \<open>x \<sharp> yvec2\<close> \<open>x \<sharp> M\<close> have "x \<sharp> \<exclamdown>M\<lparr>\<nu>*(yvec1@yvec2)\<rparr>\<langle>N\<rangle>" by simp
      moreover note \<open>x \<sharp> P'\<close>
      moreover from \<open>yvec1 \<sharp>* \<Psi>\<close> \<open>yvec2 \<sharp>* \<Psi>\<close> have "(yvec1@yvec2) \<sharp>* \<Psi>" by simp
      moreover from \<open>yvec1 \<sharp>* \<lparr>\<nu>x\<rparr>P\<close> \<open>yvec2 \<sharp>* \<lparr>\<nu>x\<rparr>P\<close> \<open>y \<sharp> yvec1\<close> \<open>y' \<sharp> yvec1\<close> \<open>y \<sharp> yvec2\<close> \<open>y' \<sharp> yvec2\<close> \<open>x \<sharp> yvec1\<close> \<open>x \<sharp> yvec2\<close>
      have "(yvec1@yvec2) \<sharp>* ([(y, y')] \<bullet> P)" by simp
      moreover from \<open>yvec1 \<sharp>* M\<close> \<open>yvec2 \<sharp>* M\<close> have "(yvec1 @ yvec2) \<sharp>* M"
        by simp
      ultimately show ?case
      proof(induct rule: resBrOutputCases')
        case(cBrOpen M' xvec1 xvec2 x' N' P')
        from \<open>\<exclamdown>M'\<lparr>\<nu>*(xvec1 @ x' # xvec2)\<rparr>\<langle>N'\<rangle> = \<exclamdown>M\<lparr>\<nu>*(yvec1 @ yvec2)\<rparr>\<langle>N\<rangle>\<close> have "yvec1@yvec2 = xvec1@x'#xvec2" and "M = M'" and "N = N'" by (simp add: action.inject)+
        from \<open>x \<sharp> yvec1\<close> \<open>x \<sharp> yvec2\<close> \<open>y' \<sharp> yvec1\<close> \<open>y' \<sharp> yvec2\<close> \<open>y \<sharp> yvec1\<close> \<open>y \<sharp> yvec2\<close>
        have "x \<sharp> (yvec1@yvec2)" and "y \<sharp> (yvec1@yvec2)" and "y' \<sharp> (yvec1@yvec2)" by simp+
        with \<open>yvec1@yvec2 = xvec1@x'#xvec2\<close>
        have "x \<sharp> xvec1" and "x \<noteq> x'" and "x \<sharp> xvec2" and "y \<sharp> xvec1" and "y \<noteq> x'" and "y \<sharp> xvec2"
          and "y' \<sharp> xvec1" and "x' \<noteq> y'" and "y' \<sharp> xvec2"
          by auto

        show ?case
        proof(cases "x' \<in> set yvec1")
          assume "x' \<in> set yvec1"

          with \<open>yvec1@yvec2 = xvec1@x'#xvec2\<close> \<open>distinct (yvec1@yvec2)\<close>
          obtain xvec2' where Eq1: "yvec1=xvec1@x'#xvec2'"
            and Eq: "xvec2=xvec2'@yvec2"
            by(metis partitionListLeft)
          from \<open>\<Psi> \<rhd> ([(x, x')] \<bullet> [(y, y')] \<bullet> P) \<longmapsto>\<exclamdown>M'\<lparr>\<nu>*(xvec1@xvec2)\<rparr>\<langle>N'\<rangle> \<prec> P'\<close> \<open>y' \<in> supp N\<close> \<open>y' \<sharp> \<Psi>\<close> \<open>y' \<sharp> M\<close> \<open>y' \<sharp> xvec1\<close> \<open>y' \<sharp> xvec2\<close> Eq \<open>M=M'\<close> \<open>N = N'\<close>
          have "\<Psi> \<rhd> \<lparr>\<nu>y'\<rparr>([(x, x')] \<bullet> [(y, y')] \<bullet> P) \<longmapsto>\<exclamdown>M'\<lparr>\<nu>*((xvec1@xvec2')@y'#yvec2)\<rparr>\<langle>N'\<rangle> \<prec> P'"
            by(intro BrOpen) auto
          then have "\<Psi> \<rhd> \<lparr>\<nu>x'\<rparr>(\<lparr>\<nu>y'\<rparr>([(x, x')] \<bullet> [(y, y')] \<bullet> P)) \<longmapsto>\<exclamdown>M\<lparr>\<nu>*(xvec1@x'#xvec2'@y'#yvec2)\<rparr>\<langle>N\<rangle> \<prec> P'"
            using \<open>x' \<in> supp N'\<close> \<open>x' \<sharp> \<Psi>\<close> \<open>x' \<sharp> M'\<close> \<open>x' \<sharp> xvec1\<close> \<open>x' \<sharp> xvec2\<close> \<open>x' \<noteq> y'\<close> Eq \<open>M=M'\<close> \<open>N=N'\<close>
            by(intro BrOpen) auto
          with \<open>x' \<noteq> y'\<close> \<open>x \<noteq> y'\<close> \<open>x' \<sharp> [(y, y')] \<bullet> P\<close>
          have "\<Psi> \<rhd> \<lparr>\<nu>x\<rparr>(\<lparr>\<nu>y'\<rparr>([(y, y')] \<bullet> P)) \<longmapsto>\<exclamdown>M\<lparr>\<nu>*(xvec1@x'#xvec2'@y'#yvec2)\<rparr>\<langle>N\<rangle> \<prec> P'"
            by(subst alphaRes[where y=x']) (simp add: calc_atm eqvts abs_fresh)+
          with Eq1 \<open>y' \<sharp> \<lparr>\<nu>x\<rparr>P\<close> \<open>x \<noteq> y'\<close> R1 show ?case
            by(auto simp add: alphaRes abs_fresh)
        next
          assume "\<not>x' \<in> set yvec1"
          then have "x' \<sharp> yvec1" by(simp add: fresh_def)
          from \<open>\<not>x' \<in> set yvec1\<close> \<open>yvec1@yvec2 = xvec1@x'#xvec2\<close>
          have "x' \<in> set yvec2"
            by(auto simp add: append_eq_append_conv2 append_eq_Cons_conv)
          with \<open>yvec1@yvec2 = xvec1@x'#xvec2\<close> \<open>distinct (yvec1@yvec2)\<close>
          obtain xvec2' where Eq: "xvec1=yvec1@xvec2'"
            and Eq1: "yvec2=xvec2'@x'#xvec2"
            by(metis partitionListRight)
          from \<open>\<Psi> \<rhd> ([(x, x')] \<bullet> [(y, y')] \<bullet> P) \<longmapsto>\<exclamdown>M'\<lparr>\<nu>*(xvec1@xvec2)\<rparr>\<langle>N'\<rangle> \<prec> P'\<close> \<open>y' \<in> supp N\<close> \<open>y' \<sharp> \<Psi>\<close> \<open>y' \<sharp> M\<close> \<open>y' \<sharp> xvec1\<close> \<open>y' \<sharp> xvec2\<close> Eq \<open>M=M'\<close> \<open>N = N'\<close>
          have "\<Psi> \<rhd> \<lparr>\<nu>y'\<rparr>([(x, x')] \<bullet> [(y, y')] \<bullet> P) \<longmapsto>\<exclamdown>M'\<lparr>\<nu>*(yvec1@y'#xvec2'@xvec2)\<rparr>\<langle>N'\<rangle> \<prec> P'"
            by(intro BrOpen) (assumption | simp)+
          then have "\<Psi> \<rhd> \<lparr>\<nu>x'\<rparr>(\<lparr>\<nu>y'\<rparr>([(x, x')] \<bullet> [(y, y')] \<bullet> P)) \<longmapsto>\<exclamdown>M\<lparr>\<nu>*((yvec1@y'#xvec2')@x'#xvec2)\<rparr>\<langle>N\<rangle> \<prec> P'"
            using \<open>x' \<in> supp N'\<close> \<open>x' \<sharp> \<Psi>\<close> \<open>x' \<sharp> M'\<close> \<open>x' \<sharp> xvec1\<close> \<open>x' \<sharp> xvec2\<close> \<open>x' \<noteq> y'\<close> Eq \<open>M=M'\<close> \<open>N=N'\<close>
            by(intro BrOpen) auto
          with \<open>x' \<noteq> y'\<close> \<open>x \<noteq> y'\<close> \<open>x' \<sharp> [(y, y')] \<bullet> P\<close>
          have "\<Psi> \<rhd> \<lparr>\<nu>x\<rparr>(\<lparr>\<nu>y'\<rparr>([(y, y')] \<bullet> P)) \<longmapsto>\<exclamdown>M\<lparr>\<nu>*((yvec1@y'#xvec2')@x'#xvec2)\<rparr>\<langle>N\<rangle> \<prec> P'"
            by(subst alphaRes[where y=x']) (simp add: calc_atm eqvts abs_fresh)+
          with Eq1 \<open>y' \<sharp> \<lparr>\<nu>x\<rparr>P\<close> \<open>x \<noteq> y'\<close> R1 show ?case
            by(auto simp add: alphaRes abs_fresh)
        qed
      next
        case(cRes P')
        from \<open>\<Psi> \<rhd> ([(y, y')] \<bullet> P) \<longmapsto>\<exclamdown>M\<lparr>\<nu>*(yvec1@yvec2)\<rparr>\<langle>N\<rangle> \<prec> P'\<close> \<open>y' \<in> supp N\<close> \<open>y' \<sharp> \<Psi>\<close> \<open>y' \<sharp> M\<close> \<open>y' \<sharp> yvec1\<close> \<open>y' \<sharp> yvec2\<close>
        have "\<Psi> \<rhd> \<lparr>\<nu>y'\<rparr>([(y, y')] \<bullet> P) \<longmapsto>\<exclamdown>M\<lparr>\<nu>*(yvec1@y'#yvec2)\<rparr>\<langle>N\<rangle> \<prec> P'" by(rule BrOpen)
        with \<open>y' \<sharp> \<lparr>\<nu>x\<rparr>P\<close> \<open>x \<noteq> y'\<close>have "\<Psi> \<rhd> \<lparr>\<nu>y\<rparr>P \<longmapsto>\<exclamdown>M\<lparr>\<nu>*(yvec1@y'#yvec2)\<rparr>\<langle>N\<rangle> \<prec> P'" by(simp add: alphaRes abs_fresh)
        then have "\<Psi> \<rhd> \<lparr>\<nu>x\<rparr>(\<lparr>\<nu>y\<rparr>P) \<longmapsto>\<exclamdown>M\<lparr>\<nu>*(yvec1@y'#yvec2)\<rparr>\<langle>N\<rangle> \<prec> \<lparr>\<nu>x\<rparr>P'" using \<open>x \<sharp> \<Psi>\<close> \<open>x \<sharp> M\<close> \<open>x \<sharp> yvec1\<close> \<open>x \<noteq> y'\<close> \<open>x \<sharp> yvec2\<close> \<open>x \<sharp> N\<close>
          by(intro Scope) auto
        moreover have "(\<Psi>, \<lparr>\<nu>x\<rparr>P', \<lparr>\<nu>x\<rparr>P') \<in> Rel" by(rule R1)
        ultimately show ?case by blast
      qed
    next
      case(cRes P')
      from \<open>x \<sharp> \<lparr>\<nu>y\<rparr>P'\<close> \<open>x \<noteq> y\<close> have "x \<sharp> P'" by(simp add: abs_fresh)
      with \<open>\<Psi> \<rhd> \<lparr>\<nu>x\<rparr>P \<longmapsto>\<alpha> \<prec> P'\<close> \<open>x \<sharp> \<Psi>\<close> \<open>x \<sharp> \<alpha>\<close>
      show ?case using \<open>bn \<alpha> \<sharp>* \<Psi>\<close> \<open>bn \<alpha> \<sharp>* P\<close> \<open>bn \<alpha> \<sharp>* subject \<alpha>\<close> \<open>y \<sharp> \<alpha>\<close>
      proof(induct rule: resCases'[where C="(x, y)"])
        case(cOpen M xvec1 xvec2 x' N P')
        from \<open>y \<sharp> M\<lparr>\<nu>*(xvec1@x'#xvec2)\<rparr>\<langle>N\<rangle>\<close> have "y \<noteq> x'" and "y \<sharp> M\<lparr>\<nu>*(xvec1@xvec2)\<rparr>\<langle>N\<rangle>" by simp+
        from \<open>\<Psi> \<rhd> ([(x, x')] \<bullet> P) \<longmapsto>M\<lparr>\<nu>*(xvec1@xvec2)\<rparr>\<langle>N\<rangle> \<prec> P'\<close> \<open>y \<sharp> \<Psi>\<close> \<open>y \<sharp> M\<lparr>\<nu>*(xvec1@xvec2)\<rparr>\<langle>N\<rangle>\<close>
        have "\<Psi> \<rhd> \<lparr>\<nu>y\<rparr>([(x, x')] \<bullet> P) \<longmapsto>M\<lparr>\<nu>*(xvec1@xvec2)\<rparr>\<langle>N\<rangle> \<prec> \<lparr>\<nu>y\<rparr>P'"
          by(rule Scope)
        then have "\<Psi> \<rhd> \<lparr>\<nu>x'\<rparr>(\<lparr>\<nu>y\<rparr>([(x, x')] \<bullet> P)) \<longmapsto>M\<lparr>\<nu>*(xvec1@x'#xvec2)\<rparr>\<langle>N\<rangle> \<prec> \<lparr>\<nu>y\<rparr>P'"
          using \<open>x' \<in> supp N\<close> \<open>x' \<sharp> \<Psi>\<close> \<open>x' \<sharp> M\<close> \<open>x' \<sharp> xvec1\<close> \<open>x' \<sharp> xvec2\<close>
          by(rule Open)
        with \<open>y \<noteq> x'\<close> \<open>x \<noteq> y\<close> \<open>x' \<sharp> P\<close> have "\<Psi> \<rhd> \<lparr>\<nu>x\<rparr>(\<lparr>\<nu>y\<rparr>P) \<longmapsto>M\<lparr>\<nu>*(xvec1@x'#xvec2)\<rparr>\<langle>N\<rangle> \<prec> \<lparr>\<nu>y\<rparr>P'"
          by(subst alphaRes[where y=x']) (simp add: abs_fresh eqvts calc_atm)+
        moreover have "(\<Psi>, \<lparr>\<nu>y\<rparr>P', \<lparr>\<nu>y\<rparr>P') \<in> Rel" by(rule R1)
        ultimately show ?case by blast
      next
        case(cBrOpen M xvec1 xvec2 x' N P')
        from \<open>y \<sharp> \<exclamdown>M\<lparr>\<nu>*(xvec1@x'#xvec2)\<rparr>\<langle>N\<rangle>\<close> have "y \<noteq> x'" and "y \<sharp> \<exclamdown>M\<lparr>\<nu>*(xvec1@xvec2)\<rparr>\<langle>N\<rangle>" by simp+
        from \<open>\<Psi> \<rhd> ([(x, x')] \<bullet> P) \<longmapsto>\<exclamdown>M\<lparr>\<nu>*(xvec1@xvec2)\<rparr>\<langle>N\<rangle> \<prec> P'\<close> \<open>y \<sharp> \<Psi>\<close> \<open>y \<sharp> \<exclamdown>M\<lparr>\<nu>*(xvec1@xvec2)\<rparr>\<langle>N\<rangle>\<close>
        have "\<Psi> \<rhd> \<lparr>\<nu>y\<rparr>([(x, x')] \<bullet> P) \<longmapsto>\<exclamdown>M\<lparr>\<nu>*(xvec1@xvec2)\<rparr>\<langle>N\<rangle> \<prec> \<lparr>\<nu>y\<rparr>P'"
          by(rule Scope)
        then have "\<Psi> \<rhd> \<lparr>\<nu>x'\<rparr>(\<lparr>\<nu>y\<rparr>([(x, x')] \<bullet> P)) \<longmapsto>\<exclamdown>M\<lparr>\<nu>*(xvec1@x'#xvec2)\<rparr>\<langle>N\<rangle> \<prec> \<lparr>\<nu>y\<rparr>P'"
          using \<open>x' \<in> supp N\<close> \<open>x' \<sharp> \<Psi>\<close> \<open>x' \<sharp> M\<close> \<open>x' \<sharp> xvec1\<close> \<open>x' \<sharp> xvec2\<close>
          by(rule BrOpen)
        with \<open>y \<noteq> x'\<close> \<open>x \<noteq> y\<close> \<open>x' \<sharp> P\<close> have "\<Psi> \<rhd> \<lparr>\<nu>x\<rparr>(\<lparr>\<nu>y\<rparr>P) \<longmapsto>\<exclamdown>M\<lparr>\<nu>*(xvec1@x'#xvec2)\<rparr>\<langle>N\<rangle> \<prec> \<lparr>\<nu>y\<rparr>P'"
          by(subst alphaRes[where y=x']) (simp add: abs_fresh eqvts calc_atm)+
        moreover have "(\<Psi>, \<lparr>\<nu>y\<rparr>P', \<lparr>\<nu>y\<rparr>P') \<in> Rel" by(rule R1)
        ultimately show ?case by blast
      next
        case(cRes P')
        from \<open>\<Psi> \<rhd> P \<longmapsto>\<alpha> \<prec> P'\<close> \<open>y \<sharp> \<Psi>\<close> \<open>y \<sharp> \<alpha>\<close>
        have "\<Psi> \<rhd> \<lparr>\<nu>y\<rparr>P \<longmapsto>\<alpha> \<prec> \<lparr>\<nu>y\<rparr>P'" by(rule Scope)
        then have "\<Psi> \<rhd> \<lparr>\<nu>x\<rparr>(\<lparr>\<nu>y\<rparr>P) \<longmapsto>\<alpha> \<prec> \<lparr>\<nu>x\<rparr>(\<lparr>\<nu>y\<rparr>P')" using \<open>x \<sharp> \<Psi>\<close> \<open>x \<sharp> \<alpha>\<close>
          by(rule Scope)
        moreover from \<open>x \<sharp> \<Psi>\<close> \<open>y \<sharp> \<Psi>\<close> have "(\<Psi>, \<lparr>\<nu>x\<rparr>(\<lparr>\<nu>y\<rparr>P'), \<lparr>\<nu>y\<rparr>(\<lparr>\<nu>x\<rparr>P')) \<in> Rel"
          by(rule R2)
        ultimately show ?case by blast
      next
        case(cBrClose M xvec N P')
        then show ?case
        proof(cases "y \<sharp> \<exclamdown>M\<lparr>\<nu>*xvec\<rparr>\<langle>N\<rangle>")
          case True
          with \<open>\<Psi> \<rhd> P \<longmapsto>\<exclamdown>M\<lparr>\<nu>*xvec\<rparr>\<langle>N\<rangle> \<prec> P'\<close>
          have "\<Psi> \<rhd> \<lparr>\<nu>y\<rparr>P \<longmapsto>\<exclamdown>M\<lparr>\<nu>*xvec\<rparr>\<langle>N\<rangle> \<prec> \<lparr>\<nu>y\<rparr>P'" using \<open>y \<sharp> \<Psi>\<close>
            by(intro Scope)
          then have "\<Psi> \<rhd> \<lparr>\<nu>x\<rparr>(\<lparr>\<nu>y\<rparr>P) \<longmapsto> \<tau> \<prec> (\<lparr>\<nu>x\<rparr>(\<lparr>\<nu>*xvec\<rparr>\<lparr>\<nu>y\<rparr>P'))" using \<open>x \<in> supp M\<close> \<open>x \<sharp> \<Psi>\<close>
            by(rule BrClose)
          moreover have "(\<Psi>, (\<lparr>\<nu>x\<rparr>(\<lparr>\<nu>*xvec\<rparr>\<lparr>\<nu>y\<rparr>P')), \<lparr>\<nu>y\<rparr>(\<lparr>\<nu>x\<rparr>(\<lparr>\<nu>*xvec\<rparr>P'))) \<in> Rel"
          proof -
            have "mset (x#xvec@[y]) = mset (y#x#xvec)"
              by simp
            moreover have "(x#xvec@[y]) \<sharp>* \<Psi>" using \<open>x \<sharp> \<Psi>\<close> \<open>y \<sharp> \<Psi>\<close> \<open>xvec \<sharp>* \<Psi>\<close>
              by simp
            ultimately have "(\<Psi>, \<lparr>\<nu>*(x#xvec@[y])\<rparr>P', \<lparr>\<nu>*(y#x#xvec)\<rparr>P') \<in> Rel"
              by(metis R3)
            then show ?thesis
              by(auto simp add: resChainAppend)
          qed
          ultimately show ?thesis
            by blast
        next
          case False
          then have "y \<in> supp(\<exclamdown>M\<lparr>\<nu>*xvec\<rparr>\<langle>N\<rangle>)" unfolding fresh_def by simp
          show ?thesis
          proof(cases "y \<in> supp(M)")
            case True
            with \<open>\<Psi> \<rhd> P \<longmapsto>\<exclamdown>M\<lparr>\<nu>*xvec\<rparr>\<langle>N\<rangle> \<prec> P'\<close>
            have "\<Psi> \<rhd> \<lparr>\<nu>y\<rparr>P \<longmapsto>\<tau> \<prec> \<lparr>\<nu>y\<rparr>(\<lparr>\<nu>*xvec\<rparr>P')" using \<open>y \<sharp> \<Psi>\<close>
              by(rule BrClose)
            then have "\<Psi> \<rhd> \<lparr>\<nu>x\<rparr>(\<lparr>\<nu>y\<rparr>P) \<longmapsto>\<tau> \<prec> \<lparr>\<nu>x\<rparr>(\<lparr>\<nu>y\<rparr>(\<lparr>\<nu>*xvec\<rparr>P'))" using \<open>x \<sharp> \<Psi>\<close>
              by(rule Scope) simp
            moreover have "(\<Psi>, \<lparr>\<nu>x\<rparr>(\<lparr>\<nu>y\<rparr>(\<lparr>\<nu>*xvec\<rparr>P')), \<lparr>\<nu>y\<rparr>(\<lparr>\<nu>x\<rparr>(\<lparr>\<nu>*xvec\<rparr>P'))) \<in> Rel" using \<open>x \<sharp> \<Psi>\<close> \<open>y \<sharp> \<Psi>\<close>
              by(metis R2)
            ultimately show ?thesis
              by blast
          next
            case False
            then have "y \<sharp> M" by(simp add: fresh_def)
            from \<open>xvec \<sharp>* (x, y)\<close> have "y \<sharp> xvec" by simp
            with False \<open>y \<in> supp(\<exclamdown>M\<lparr>\<nu>*xvec\<rparr>\<langle>N\<rangle>)\<close>
            have "y \<in> supp N"
              by(simp add: fresh_def action.supp)
            from \<open>\<Psi> \<rhd> P \<longmapsto>\<exclamdown>M\<lparr>\<nu>*xvec\<rparr>\<langle>N\<rangle> \<prec> P'\<close> have "\<Psi> \<rhd> P \<longmapsto>\<exclamdown>M\<lparr>\<nu>*([]@xvec)\<rparr>\<langle>N\<rangle> \<prec> P'"
              by simp
            then have "\<Psi> \<rhd> \<lparr>\<nu>y\<rparr>P \<longmapsto>\<exclamdown>M\<lparr>\<nu>*([]@y#xvec)\<rparr>\<langle>N\<rangle> \<prec> P'" using \<open>y \<in> supp N\<close> \<open>y \<sharp> \<Psi>\<close> \<open>y \<sharp> M\<close> \<open>y \<sharp> xvec\<close>
              by(intro BrOpen) (assumption|simp)+
            then have "\<Psi> \<rhd> \<lparr>\<nu>y\<rparr>P \<longmapsto>\<exclamdown>M\<lparr>\<nu>*(y#xvec)\<rparr>\<langle>N\<rangle> \<prec> P'"
              by simp
            then have "\<Psi> \<rhd> \<lparr>\<nu>x\<rparr>(\<lparr>\<nu>y\<rparr>P) \<longmapsto>\<tau> \<prec> \<lparr>\<nu>x\<rparr>(\<lparr>\<nu>y\<rparr>(\<lparr>\<nu>*xvec\<rparr>P'))" using \<open>x \<in> supp M\<close> \<open>x \<sharp> \<Psi>\<close>
              by(auto dest: BrClose)
            moreover have "(\<Psi>, \<lparr>\<nu>x\<rparr>(\<lparr>\<nu>y\<rparr>(\<lparr>\<nu>*xvec\<rparr>P')), \<lparr>\<nu>y\<rparr>(\<lparr>\<nu>x\<rparr>(\<lparr>\<nu>*xvec\<rparr>P'))) \<in> Rel" using \<open>x \<sharp> \<Psi>\<close> \<open>y \<sharp> \<Psi>\<close>
              by(rule R2)
            ultimately show ?thesis by blast
          qed
        qed
      qed
    next
      case(cBrClose M xvec N P')
      from \<open>xvec \<sharp>* x\<close> have "x \<sharp> xvec" by simp
      have "x \<sharp> \<lparr>\<nu>x\<rparr>P" by(simp add: fresh_abs_fun_iff[OF pt_name_inst, OF at_name_inst, OF fin_supp])
      have "x \<sharp> P'"
        by(rule broutputFreshDerivativeP) fact+
      have "x \<sharp> N"
        by(rule broutputFreshDerivativeN) fact+
      moreover from \<open>\<Psi> \<rhd> \<lparr>\<nu>x\<rparr>P \<longmapsto> \<exclamdown>M\<lparr>\<nu>*xvec\<rparr>\<langle>N\<rangle> \<prec> P'\<close> \<open>xvec \<sharp>* M\<close> \<open>x \<sharp> \<lparr>\<nu>x\<rparr>P\<close> have "x \<sharp> M"
        by(rule brOutputFreshSubject)
      moreover note \<open>x \<sharp> xvec\<close>
      ultimately have "x \<sharp> \<exclamdown>M\<lparr>\<nu>*xvec\<rparr>\<langle>N\<rangle>"
        by simp
      have "bn (\<exclamdown>M\<lparr>\<nu>*xvec\<rparr>\<langle>N\<rangle>) \<sharp>* \<Psi>" using \<open>xvec \<sharp>* \<Psi>\<close> by simp
      have "bn (\<exclamdown>M\<lparr>\<nu>*xvec\<rparr>\<langle>N\<rangle>) \<sharp>* P" using \<open>xvec \<sharp>* \<lparr>\<nu>x\<rparr>P\<close> \<open>x \<sharp> xvec\<close> by(simp add: fresh_abs_fun_iff[OF pt_name_inst, OF at_name_inst, OF fin_supp])
      have "bn (\<exclamdown>M\<lparr>\<nu>*xvec\<rparr>\<langle>N\<rangle>) \<sharp>* subject (\<exclamdown>M\<lparr>\<nu>*xvec\<rparr>\<langle>N\<rangle>)" using \<open>xvec \<sharp>* M\<close> by simp
      have "y \<in> supp(subject (\<exclamdown>M\<lparr>\<nu>*xvec\<rparr>\<langle>N\<rangle>))" using \<open>y \<in> supp M\<close>
        by(simp add: supp_some)
      obtain M' xvec' N' where "\<exclamdown>M\<lparr>\<nu>*xvec\<rparr>\<langle>N\<rangle> = \<exclamdown>M'\<lparr>\<nu>*xvec'\<rparr>\<langle>N'\<rangle>"
        by auto
      from \<open>\<Psi> \<rhd> \<lparr>\<nu>x\<rparr>P \<longmapsto> \<exclamdown>M\<lparr>\<nu>*xvec\<rparr>\<langle>N\<rangle> \<prec> P'\<close> \<open>x \<sharp> \<Psi>\<close> \<open>x \<sharp> \<exclamdown>M\<lparr>\<nu>*xvec\<rparr>\<langle>N\<rangle>\<close> \<open>x \<sharp> P'\<close> \<open>bn (\<exclamdown>M\<lparr>\<nu>*xvec\<rparr>\<langle>N\<rangle>) \<sharp>* \<Psi>\<close> \<open>bn (\<exclamdown>M\<lparr>\<nu>*xvec\<rparr>\<langle>N\<rangle>) \<sharp>* P\<close> \<open>bn (\<exclamdown>M\<lparr>\<nu>*xvec\<rparr>\<langle>N\<rangle>) \<sharp>* subject (\<exclamdown>M\<lparr>\<nu>*xvec\<rparr>\<langle>N\<rangle>)\<close> \<open>\<exclamdown>M\<lparr>\<nu>*xvec\<rparr>\<langle>N\<rangle> = \<exclamdown>M'\<lparr>\<nu>*xvec'\<rparr>\<langle>N'\<rangle>\<close> \<open>y \<in> supp(subject (\<exclamdown>M\<lparr>\<nu>*xvec\<rparr>\<langle>N\<rangle>))\<close>
      have "\<exists>Q'. \<Psi> \<rhd> \<lparr>\<nu>x\<rparr>(\<lparr>\<nu>y\<rparr>P) \<longmapsto> \<tau> \<prec> Q' \<and> (\<Psi>, Q', \<lparr>\<nu>y\<rparr>(\<lparr>\<nu>*(bn (\<exclamdown>M\<lparr>\<nu>*xvec\<rparr>\<langle>N\<rangle>))\<rparr>P')) \<in> Rel"
      proof(induct rule: resCases'[where C=y])
        case cOpen then show ?case by(simp add: residualInject)
      next
        case(cBrOpen M xvec yvec z N P')
        from \<open>y \<in> supp (subject (\<exclamdown>M\<lparr>\<nu>*(xvec @ z # yvec)\<rparr>\<langle>N\<rangle>))\<close> have "y \<in> supp M"
          by(simp add: supp_some)
        then have "y \<noteq> z" using \<open>z \<sharp> M\<close> by(auto simp add: fresh_def)
        from \<open>\<Psi> \<rhd> [(x, z)] \<bullet> P \<longmapsto> \<exclamdown>M\<lparr>\<nu>*(xvec @ yvec)\<rparr>\<langle>N\<rangle> \<prec> P'\<close> \<open>y \<in> supp M\<close> \<open>y \<sharp> \<Psi>\<close>
        have "\<Psi> \<rhd> \<lparr>\<nu>y\<rparr>([(x, z)] \<bullet> P) \<longmapsto> \<tau> \<prec> \<lparr>\<nu>y\<rparr>(\<lparr>\<nu>*(xvec@yvec)\<rparr>P')"
          by(rule BrClose)
        then have "\<Psi> \<rhd> \<lparr>\<nu>z\<rparr>(\<lparr>\<nu>y\<rparr>([(x, z)] \<bullet> P)) \<longmapsto> \<tau> \<prec> \<lparr>\<nu>z\<rparr>(\<lparr>\<nu>y\<rparr>(\<lparr>\<nu>*(xvec@yvec)\<rparr>P'))" using \<open>z \<sharp> \<Psi>\<close>
          by(rule Scope) simp
        then have "\<Psi> \<rhd> \<lparr>\<nu>x\<rparr>(\<lparr>\<nu>y\<rparr>P) \<longmapsto> \<tau> \<prec> \<lparr>\<nu>z\<rparr>(\<lparr>\<nu>y\<rparr>(\<lparr>\<nu>*(xvec@yvec)\<rparr>P'))" using \<open>z \<sharp> P\<close> \<open>x \<noteq> y\<close> \<open>y \<noteq> z\<close>
          apply(subst alphaRes[where x=x and y=z])
           apply(simp add: fresh_abs_fun_iff[OF pt_name_inst, OF at_name_inst, OF fin_supp])
          apply(simp add: eqvts swap_simps)
          done
        moreover have "(\<Psi>, \<lparr>\<nu>z\<rparr>(\<lparr>\<nu>y\<rparr>(\<lparr>\<nu>*(xvec @ yvec)\<rparr>P')), \<lparr>\<nu>y\<rparr>(\<lparr>\<nu>*bn (\<exclamdown>M\<lparr>\<nu>*(xvec @ z # yvec)\<rparr>\<langle>N\<rangle>)\<rparr>P')) \<in> Rel"
        proof -
          have "mset(z#y#xvec@yvec) = mset(y#xvec@z#yvec)"
            by simp
          moreover have "(z#y#xvec@yvec) \<sharp>* \<Psi>" using \<open>z \<sharp> \<Psi>\<close> \<open>y \<sharp> \<Psi>\<close> \<open>xvec \<sharp>* \<Psi>\<close> \<open>yvec \<sharp>* \<Psi>\<close>
            by simp
          ultimately have "(\<Psi>, \<lparr>\<nu>*(z#y#xvec@yvec)\<rparr>P', \<lparr>\<nu>*(y#xvec@z#yvec)\<rparr>P') \<in> Rel"
            by(metis R3)
          then show ?thesis
            by(simp add: resChainAppend)
        qed
        ultimately show ?case
          by blast
      next
        case(cRes P')
        from \<open>\<Psi> \<rhd> P \<longmapsto> \<exclamdown>M\<lparr>\<nu>*xvec\<rparr>\<langle>N\<rangle> \<prec> P'\<close> \<open>y \<in> supp M\<close> \<open>y \<sharp> \<Psi>\<close>
        have "\<Psi> \<rhd> \<lparr>\<nu>y\<rparr>P \<longmapsto> \<tau> \<prec> \<lparr>\<nu>y\<rparr>(\<lparr>\<nu>*xvec\<rparr>P')"
          by(rule BrClose)
        then have "\<Psi> \<rhd> \<lparr>\<nu>x\<rparr>(\<lparr>\<nu>y\<rparr>P) \<longmapsto> \<tau> \<prec> \<lparr>\<nu>x\<rparr>(\<lparr>\<nu>y\<rparr>(\<lparr>\<nu>*xvec\<rparr>P'))" using \<open>x \<sharp> \<Psi>\<close>
          by(rule Scope) simp
        moreover have "(\<Psi>, \<lparr>\<nu>x\<rparr>(\<lparr>\<nu>y\<rparr>(\<lparr>\<nu>*xvec\<rparr>P')), \<lparr>\<nu>y\<rparr>(\<lparr>\<nu>*bn (\<exclamdown>M\<lparr>\<nu>*xvec\<rparr>\<langle>N\<rangle>)\<rparr>\<lparr>\<nu>x\<rparr>P')) \<in> Rel"
        proof -
          have "mset(x#y#xvec) = mset(y#xvec@[x])"
            by simp
          moreover have "(x#y#xvec) \<sharp>* \<Psi>" using \<open>x \<sharp> \<Psi>\<close> \<open>y \<sharp> \<Psi>\<close> \<open>xvec \<sharp>* \<Psi>\<close>
            by simp
          ultimately have "(\<Psi>, \<lparr>\<nu>*(x#y#xvec)\<rparr>P', \<lparr>\<nu>*(y#xvec@[x])\<rparr>P') \<in> Rel"
            by(metis R3)
          then show ?thesis by(simp add: resChainAppend)
        qed
        ultimately show ?case
          by blast
      next
        case cBrClose then show ?case by simp
      qed
      then show ?case by simp
    qed
  qed
qed

lemma parAssocLeft:
  fixes \<Psi>   :: 'b
    and P   :: "('a, 'b, 'c) psi"
    and Q   :: "('a, 'b, 'c) psi"
    and R   :: "('a, 'b, 'c) psi"
    and Rel :: "('b \<times> ('a, 'b, 'c) psi \<times> ('a, 'b, 'c) psi) set"

assumes "eqvt Rel"
  and   C1: "\<And>\<Psi>' S T U. (\<Psi>, (S \<parallel> T) \<parallel> U, S \<parallel> (T \<parallel> U)) \<in> Rel"
  and   C2: "\<And>xvec \<Psi>' S T U. \<lbrakk>xvec \<sharp>* \<Psi>'; xvec \<sharp>* S\<rbrakk> \<Longrightarrow> (\<Psi>', \<lparr>\<nu>*xvec\<rparr>((S \<parallel> T) \<parallel> U), S \<parallel> (\<lparr>\<nu>*xvec\<rparr>(T \<parallel> U))) \<in> Rel"
  and   C3: "\<And>xvec \<Psi>' S T U. \<lbrakk>xvec \<sharp>* \<Psi>'; xvec \<sharp>* U\<rbrakk> \<Longrightarrow> (\<Psi>', (\<lparr>\<nu>*xvec\<rparr>(S \<parallel> T)) \<parallel> U, \<lparr>\<nu>*xvec\<rparr>(S \<parallel> (T \<parallel> U))) \<in> Rel"
  and   C4: "\<And>\<Psi>' S T xvec. \<lbrakk>(\<Psi>', S, T) \<in> Rel; xvec \<sharp>* \<Psi>'\<rbrakk> \<Longrightarrow> (\<Psi>', \<lparr>\<nu>*xvec\<rparr>S, \<lparr>\<nu>*xvec\<rparr>T) \<in> Rel"

shows "\<Psi> \<rhd> (P \<parallel> Q) \<parallel> R \<leadsto>[Rel] P \<parallel> (Q \<parallel> R)"
  using \<open>eqvt Rel\<close>
proof(induct rule: simI[of _ _ _ _ "()"])
  case(cSim \<alpha> PQR)
  from \<open>bn \<alpha> \<sharp>* (P \<parallel> Q \<parallel> R)\<close> have "bn \<alpha> \<sharp>* P" and "bn \<alpha> \<sharp>* Q" and "bn \<alpha> \<sharp>* R" by simp+
  then have "bn \<alpha> \<sharp>* (Q \<parallel> R)" by simp
  with \<open>\<Psi> \<rhd> P \<parallel> (Q \<parallel> R) \<longmapsto>\<alpha> \<prec> PQR\<close> \<open>bn \<alpha> \<sharp>* \<Psi>\<close> \<open>bn \<alpha> \<sharp>* P\<close>
  show ?case using \<open>bn \<alpha> \<sharp>* subject \<alpha>\<close>
  proof(induct rule: parCases[where C = "(\<Psi>, P, Q, R, \<alpha>)"])
    case(cPar1 P' A\<^sub>Q\<^sub>R \<Psi>\<^sub>Q\<^sub>R)
    from \<open>A\<^sub>Q\<^sub>R \<sharp>* (\<Psi>, P, Q, R, \<alpha>)\<close> have "A\<^sub>Q\<^sub>R \<sharp>* Q" and  "A\<^sub>Q\<^sub>R \<sharp>* R"
      by simp+
    with \<open>extractFrame(Q \<parallel> R) = \<langle>A\<^sub>Q\<^sub>R, \<Psi>\<^sub>Q\<^sub>R\<rangle>\<close> \<open>distinct A\<^sub>Q\<^sub>R\<close>
    obtain A\<^sub>Q \<Psi>\<^sub>Q A\<^sub>R \<Psi>\<^sub>R where "A\<^sub>Q\<^sub>R = A\<^sub>Q@A\<^sub>R" and "\<Psi>\<^sub>Q\<^sub>R = \<Psi>\<^sub>Q \<otimes> \<Psi>\<^sub>R" and FrQ: "extractFrame Q = \<langle>A\<^sub>Q, \<Psi>\<^sub>Q\<rangle>" and  FrR: "extractFrame R = \<langle>A\<^sub>R, \<Psi>\<^sub>R\<rangle>"
      and "A\<^sub>Q \<sharp>* \<Psi>\<^sub>R" and "A\<^sub>R \<sharp>* \<Psi>\<^sub>Q"
      by(auto intro: mergeFrameE dest: extractFrameFreshChain)

    from \<open>A\<^sub>Q\<^sub>R = A\<^sub>Q@A\<^sub>R\<close> \<open>A\<^sub>Q\<^sub>R \<sharp>* \<Psi>\<close> \<open>A\<^sub>Q\<^sub>R \<sharp>* P\<close> \<open>A\<^sub>Q\<^sub>R \<sharp>* Q\<close> \<open>A\<^sub>Q\<^sub>R \<sharp>* \<alpha>\<close>
    have "A\<^sub>Q \<sharp>* \<Psi>" and "A\<^sub>R \<sharp>* \<Psi>" and "A\<^sub>Q \<sharp>* P" and "A\<^sub>R \<sharp>* P" and "A\<^sub>Q \<sharp>* Q" and "A\<^sub>R \<sharp>* Q" and "A\<^sub>Q \<sharp>* \<alpha>" and "A\<^sub>R \<sharp>* \<alpha>"
      by simp+

    from \<open>\<Psi> \<otimes> \<Psi>\<^sub>Q\<^sub>R \<rhd> P \<longmapsto>\<alpha> \<prec> P'\<close> \<open>\<Psi>\<^sub>Q\<^sub>R = \<Psi>\<^sub>Q \<otimes> \<Psi>\<^sub>R\<close> have "(\<Psi> \<otimes> \<Psi>\<^sub>R) \<otimes> \<Psi>\<^sub>Q \<rhd> P \<longmapsto>\<alpha> \<prec> P'"
      by(metis statEqTransition Associativity Commutativity Composition)
    then have "\<Psi> \<otimes> \<Psi>\<^sub>R \<rhd> P \<parallel> Q \<longmapsto>\<alpha> \<prec> (P' \<parallel> Q)" using FrQ \<open>bn \<alpha> \<sharp>* Q\<close> \<open>A\<^sub>Q \<sharp>* \<Psi>\<close> \<open>A\<^sub>Q \<sharp>* \<Psi>\<^sub>R\<close> \<open>A\<^sub>Q \<sharp>* P\<close> \<open>A\<^sub>Q \<sharp>* \<alpha>\<close>
      by(intro Par1) auto
    then have "\<Psi> \<rhd> (P \<parallel> Q) \<parallel> R \<longmapsto>\<alpha> \<prec> ((P' \<parallel> Q) \<parallel> R)" using FrR \<open>bn \<alpha> \<sharp>* R\<close> \<open>A\<^sub>R \<sharp>* \<Psi>\<close> \<open>A\<^sub>R \<sharp>* P\<close> \<open>A\<^sub>R \<sharp>* Q\<close> \<open>A\<^sub>R \<sharp>* \<alpha>\<close>
      by(auto intro: Par1)
    moreover have "(\<Psi>, (P' \<parallel> Q) \<parallel> R, P' \<parallel> (Q \<parallel> R)) \<in> Rel" by(rule C1)
    ultimately show ?case by blast
  next
    case(cPar2 QR A\<^sub>P \<Psi>\<^sub>P)
    from \<open>A\<^sub>P \<sharp>* (\<Psi>, P, Q, R, \<alpha>)\<close> have "A\<^sub>P \<sharp>* Q" and "A\<^sub>P \<sharp>* R" and "A\<^sub>P \<sharp>* \<alpha>"
      by simp+
    have FrP: "extractFrame P = \<langle>A\<^sub>P, \<Psi>\<^sub>P\<rangle>" by fact
    with \<open>bn \<alpha> \<sharp>* P\<close> \<open>A\<^sub>P \<sharp>* \<alpha>\<close> have "bn \<alpha> \<sharp>* \<Psi>\<^sub>P" by(auto dest: extractFrameFreshChain)
    with \<open>bn \<alpha> \<sharp>* \<Psi>\<close> have "bn \<alpha> \<sharp>* (\<Psi> \<otimes> \<Psi>\<^sub>P)" by force
    with \<open>\<Psi> \<otimes> \<Psi>\<^sub>P \<rhd> Q \<parallel> R \<longmapsto>\<alpha> \<prec> QR\<close>
    show ?case using \<open>bn \<alpha> \<sharp>* Q\<close> \<open>bn \<alpha> \<sharp>* R\<close> \<open>bn \<alpha> \<sharp>* subject \<alpha>\<close> \<open>A\<^sub>P \<sharp>* Q\<close> \<open>A\<^sub>P \<sharp>* R\<close>
    proof(induct rule: parCasesSubject[where C = "(A\<^sub>P, \<Psi>\<^sub>P, P, Q, R, \<Psi>)"])
      case(cPar1 Q' A\<^sub>R \<Psi>\<^sub>R)
      from \<open>A\<^sub>R \<sharp>* (A\<^sub>P, \<Psi>\<^sub>P, P, Q, R, \<Psi>)\<close> have "A\<^sub>R \<sharp>* A\<^sub>P" and "A\<^sub>R \<sharp>* P" and "A\<^sub>R \<sharp>* Q" and "A\<^sub>R \<sharp>* \<Psi>\<^sub>P" and "A\<^sub>R \<sharp>* \<Psi>"
        by simp+
      from \<open>A\<^sub>P \<sharp>* R\<close> \<open>extractFrame R = \<langle>A\<^sub>R, \<Psi>\<^sub>R\<rangle>\<close> \<open>A\<^sub>R \<sharp>* A\<^sub>P\<close> have "A\<^sub>P \<sharp>* \<Psi>\<^sub>R"
        by(auto dest: extractFrameFreshChain)
      from \<open>(\<Psi> \<otimes> \<Psi>\<^sub>P) \<otimes> \<Psi>\<^sub>R \<rhd> Q \<longmapsto>\<alpha> \<prec> Q'\<close> have "(\<Psi> \<otimes> \<Psi>\<^sub>R) \<otimes> \<Psi>\<^sub>P \<rhd> Q \<longmapsto>\<alpha> \<prec> Q'"
        by(metis statEqTransition Associativity Commutativity Composition)
      then have "\<Psi> \<otimes> \<Psi>\<^sub>R \<rhd> P \<parallel> Q \<longmapsto>\<alpha> \<prec> (P \<parallel> Q')"
        using FrP \<open>bn \<alpha> \<sharp>* P\<close> \<open>A\<^sub>P \<sharp>* \<Psi>\<close> \<open>A\<^sub>P \<sharp>* \<Psi>\<^sub>R\<close> \<open>A\<^sub>P \<sharp>* Q\<close> \<open>A\<^sub>P \<sharp>* \<alpha>\<close>
        by(intro Par2) (assumption | force)+
      then have "\<Psi> \<rhd> (P \<parallel> Q) \<parallel> R \<longmapsto>\<alpha> \<prec> ((P \<parallel> Q') \<parallel> R)"
        using \<open>extractFrame R = \<langle>A\<^sub>R, \<Psi>\<^sub>R\<rangle>\<close> \<open>bn \<alpha> \<sharp>* R\<close> \<open>A\<^sub>R \<sharp>* \<Psi>\<close> \<open>A\<^sub>R \<sharp>* P\<close> \<open>A\<^sub>R \<sharp>* Q\<close> \<open>A\<^sub>R \<sharp>* \<alpha>\<close>
        by(intro Par1) (assumption | simp)+
      moreover have "(\<Psi>, (P \<parallel> Q') \<parallel> R, P \<parallel> (Q' \<parallel> R)) \<in> Rel" by(rule C1)
      ultimately show ?case by blast
    next
      case(cPar2 R' A\<^sub>Q \<Psi>\<^sub>Q)
      from \<open>A\<^sub>Q \<sharp>* (A\<^sub>P, \<Psi>\<^sub>P, P, Q, R, \<Psi>)\<close> have "A\<^sub>Q \<sharp>* A\<^sub>P" and "A\<^sub>Q \<sharp>* R" and "A\<^sub>Q \<sharp>* \<Psi>\<^sub>P" and "A\<^sub>Q \<sharp>* \<Psi>"
        by simp+
      have FrQ: "extractFrame Q = \<langle>A\<^sub>Q, \<Psi>\<^sub>Q\<rangle>" by fact
      from \<open>A\<^sub>P \<sharp>* Q\<close> FrQ \<open>A\<^sub>Q \<sharp>* A\<^sub>P\<close> have "A\<^sub>P \<sharp>* \<Psi>\<^sub>Q"
        by(auto dest: extractFrameFreshChain)
      from \<open>(\<Psi> \<otimes> \<Psi>\<^sub>P) \<otimes> \<Psi>\<^sub>Q \<rhd> R \<longmapsto>\<alpha> \<prec> R'\<close>
      have "\<Psi> \<otimes> (\<Psi>\<^sub>P \<otimes> \<Psi>\<^sub>Q) \<rhd> R \<longmapsto>\<alpha> \<prec> R'"
        by(blast intro: statEqTransition Associativity)
      moreover from FrP FrQ \<open>A\<^sub>Q \<sharp>* A\<^sub>P\<close> \<open>A\<^sub>P \<sharp>* \<Psi>\<^sub>Q\<close>  \<open>A\<^sub>Q \<sharp>* \<Psi>\<^sub>P\<close>
      have "extractFrame(P \<parallel> Q) = \<langle>(A\<^sub>P@A\<^sub>Q), \<Psi>\<^sub>P \<otimes> \<Psi>\<^sub>Q\<rangle> " by simp
      moreover from \<open>bn \<alpha> \<sharp>* P\<close> \<open>bn \<alpha> \<sharp>* Q\<close> have "bn \<alpha> \<sharp>* (P \<parallel> Q)" by simp
      moreover from \<open>A\<^sub>P \<sharp>* \<Psi>\<close> \<open>A\<^sub>Q \<sharp>* \<Psi>\<close> have "(A\<^sub>P@A\<^sub>Q) \<sharp>* \<Psi>" by simp
      moreover from \<open>A\<^sub>P \<sharp>* R\<close> \<open>A\<^sub>Q \<sharp>* R\<close> have "(A\<^sub>P@A\<^sub>Q) \<sharp>* R" by simp
      moreover from \<open>A\<^sub>P \<sharp>* \<alpha>\<close> \<open>A\<^sub>Q \<sharp>* \<alpha>\<close> have "(A\<^sub>P@A\<^sub>Q) \<sharp>* \<alpha>" by simp
      ultimately have "\<Psi> \<rhd> (P \<parallel> Q) \<parallel> R \<longmapsto>\<alpha> \<prec> ((P \<parallel> Q) \<parallel> R')"
        by(rule Par2)
      moreover have "(\<Psi>, (P \<parallel> Q) \<parallel> R', P \<parallel> (Q \<parallel> R')) \<in> Rel" by(rule C1)
      ultimately show ?case by blast
    next
      case(cComm1 \<Psi>\<^sub>R M N Q' A\<^sub>Q \<Psi>\<^sub>Q K xvec R' A\<^sub>R)
      from \<open>A\<^sub>Q \<sharp>* (A\<^sub>P, \<Psi>\<^sub>P, P, Q, R, \<Psi>)\<close>
      have "A\<^sub>Q \<sharp>* P" and "A\<^sub>Q \<sharp>* Q" and "A\<^sub>Q \<sharp>* R" and "A\<^sub>Q \<sharp>* A\<^sub>P" and "A\<^sub>Q \<sharp>* \<Psi>\<^sub>P"  and "A\<^sub>Q \<sharp>* \<Psi>" by simp+
      from \<open>A\<^sub>R \<sharp>* (A\<^sub>P, \<Psi>\<^sub>P, P, Q, R, \<Psi>)\<close> have "A\<^sub>R \<sharp>* P" and "A\<^sub>R \<sharp>* Q" and "A\<^sub>R \<sharp>* R" and "A\<^sub>R \<sharp>* A\<^sub>P"  and "A\<^sub>R \<sharp>* \<Psi>" by simp+
      from \<open>xvec \<sharp>* (A\<^sub>P,  \<Psi>\<^sub>P, P, Q, R, \<Psi>)\<close> have "xvec \<sharp>* A\<^sub>P" and "xvec \<sharp>* P" and "xvec \<sharp>* Q" and "xvec \<sharp>* \<Psi>" by simp+

      have FrQ: "extractFrame Q = \<langle>A\<^sub>Q, \<Psi>\<^sub>Q\<rangle>" by fact
      with \<open>A\<^sub>P \<sharp>* Q\<close> \<open>A\<^sub>Q \<sharp>* A\<^sub>P\<close> have "A\<^sub>P \<sharp>* \<Psi>\<^sub>Q"
        by(auto dest: extractFrameFreshChain)
      have FrR: "extractFrame R = \<langle>A\<^sub>R, \<Psi>\<^sub>R\<rangle>" by fact
      with \<open>A\<^sub>P \<sharp>* R\<close> \<open>A\<^sub>R \<sharp>* A\<^sub>P\<close> have "A\<^sub>P \<sharp>* \<Psi>\<^sub>R"
        by(auto dest: extractFrameFreshChain)
      from \<open>(\<Psi> \<otimes> \<Psi>\<^sub>P) \<otimes> \<Psi>\<^sub>Q \<rhd> R \<longmapsto>K\<lparr>\<nu>*xvec\<rparr>\<langle>N\<rangle> \<prec> R'\<close> \<open>A\<^sub>P \<sharp>* R\<close> \<open>xvec \<sharp>* A\<^sub>P\<close> \<open>xvec \<sharp>* K\<close> \<open>distinct xvec\<close> have "A\<^sub>P \<sharp>* N"
        by(auto intro: outputFreshChainDerivative)

      from \<open>(\<Psi> \<otimes> \<Psi>\<^sub>P) \<otimes> \<Psi>\<^sub>R \<rhd> Q \<longmapsto>M\<lparr>N\<rparr> \<prec> Q'\<close> have "(\<Psi> \<otimes> \<Psi>\<^sub>R) \<otimes> \<Psi>\<^sub>P \<rhd> Q \<longmapsto>M\<lparr>N\<rparr> \<prec> Q'"
        by(metis statEqTransition Associativity Commutativity Composition)
      then have "\<Psi> \<otimes> \<Psi>\<^sub>R \<rhd> P \<parallel> Q \<longmapsto>M\<lparr>N\<rparr> \<prec> (P \<parallel> Q')" using FrP \<open>A\<^sub>P \<sharp>* \<Psi>\<close> \<open>A\<^sub>P \<sharp>* \<Psi>\<^sub>R\<close> \<open>A\<^sub>P \<sharp>* Q\<close> \<open>A\<^sub>P \<sharp>* M\<close> \<open>A\<^sub>P \<sharp>* N\<close>
        by(intro Par2) auto
      moreover from FrP FrQ \<open>A\<^sub>P \<sharp>* \<Psi>\<^sub>Q\<close> \<open>A\<^sub>Q \<sharp>* A\<^sub>P\<close> \<open>A\<^sub>Q \<sharp>* \<Psi>\<^sub>P\<close> have "extractFrame(P \<parallel> Q) = \<langle>(A\<^sub>P@A\<^sub>Q), \<Psi>\<^sub>P \<otimes> \<Psi>\<^sub>Q\<rangle>"
        by simp
      moreover from  \<open>(\<Psi> \<otimes> \<Psi>\<^sub>P) \<otimes> \<Psi>\<^sub>Q \<rhd> R \<longmapsto>K\<lparr>\<nu>*xvec\<rparr>\<langle>N\<rangle> \<prec> R'\<close> have "\<Psi> \<otimes> \<Psi>\<^sub>P \<otimes> \<Psi>\<^sub>Q \<rhd> R \<longmapsto>K\<lparr>\<nu>*xvec\<rparr>\<langle>N\<rangle> \<prec> R'"
        by(metis statEqTransition Associativity)
      moreover note \<open>extractFrame R = \<langle>A\<^sub>R, \<Psi>\<^sub>R\<rangle>\<close>
      moreover from \<open>(\<Psi> \<otimes> \<Psi>\<^sub>P) \<otimes> \<Psi>\<^sub>Q \<otimes> \<Psi>\<^sub>R \<turnstile> M \<leftrightarrow> K\<close> have "\<Psi> \<otimes> (\<Psi>\<^sub>P \<otimes> \<Psi>\<^sub>Q) \<otimes> \<Psi>\<^sub>R \<turnstile> M \<leftrightarrow> K"
        by(metis statEqEnt Associativity Commutativity Composition)
      ultimately have "\<Psi> \<rhd> (P \<parallel> Q) \<parallel> R \<longmapsto>\<tau> \<prec> \<lparr>\<nu>*xvec\<rparr>((P \<parallel> Q') \<parallel> R')"
        using \<open>A\<^sub>P \<sharp>* \<Psi>\<close> \<open>A\<^sub>Q \<sharp>* \<Psi>\<close> \<open>A\<^sub>R \<sharp>* \<Psi>\<close> \<open>A\<^sub>P \<sharp>* P\<close> \<open>A\<^sub>Q \<sharp>* P\<close> \<open>A\<^sub>R \<sharp>* P\<close> \<open>A\<^sub>P \<sharp>* Q\<close> \<open>A\<^sub>Q \<sharp>* Q\<close> \<open>A\<^sub>R \<sharp>* Q\<close> \<open>A\<^sub>P \<sharp>* R\<close> \<open>A\<^sub>Q \<sharp>* R\<close> \<open>A\<^sub>R \<sharp>* R\<close>
          \<open>A\<^sub>P \<sharp>* M\<close> \<open>A\<^sub>Q \<sharp>* M\<close> \<open>A\<^sub>R \<sharp>* K\<close> \<open>A\<^sub>R \<sharp>* A\<^sub>P\<close> \<open>A\<^sub>Q \<sharp>* A\<^sub>R\<close> \<open>xvec \<sharp>* P\<close> \<open>xvec \<sharp>* Q\<close>
        by(intro Comm1) (assumption | simp)+
      moreover from \<open>xvec \<sharp>* \<Psi>\<close> \<open>xvec \<sharp>* P\<close> have "(\<Psi>, \<lparr>\<nu>*xvec\<rparr>((P \<parallel> Q') \<parallel> R'), P \<parallel> (\<lparr>\<nu>*xvec\<rparr>(Q' \<parallel> R'))) \<in> Rel"
        by(rule C2)
      ultimately show ?case by blast
    next
      case(cComm2 \<Psi>\<^sub>R M xvec N Q' A\<^sub>Q \<Psi>\<^sub>Q K R' A\<^sub>R)
      from \<open>A\<^sub>Q \<sharp>* (A\<^sub>P,  \<Psi>\<^sub>P, P, Q, R, \<Psi>)\<close>
      have "A\<^sub>Q \<sharp>* P" and "A\<^sub>Q \<sharp>* Q" and "A\<^sub>Q \<sharp>* R" and "A\<^sub>Q \<sharp>* A\<^sub>P" and "A\<^sub>Q \<sharp>* \<Psi>" and "A\<^sub>Q \<sharp>* \<Psi>\<^sub>P" by simp+
      from \<open>A\<^sub>R \<sharp>* (A\<^sub>P,  \<Psi>\<^sub>P, P, Q, R, \<Psi>)\<close> have "A\<^sub>R \<sharp>* P" and "A\<^sub>R \<sharp>* Q" and "A\<^sub>R \<sharp>* R" and "A\<^sub>R \<sharp>* A\<^sub>P"and "A\<^sub>R \<sharp>* \<Psi>" by simp+
      from \<open>xvec \<sharp>* (A\<^sub>P,  \<Psi>\<^sub>P, P, Q, R, \<Psi>)\<close> have "xvec \<sharp>* A\<^sub>P" and "xvec \<sharp>* P" and "xvec \<sharp>* Q" and "xvec \<sharp>* \<Psi>" by simp+

      have FrQ: "extractFrame Q = \<langle>A\<^sub>Q, \<Psi>\<^sub>Q\<rangle>" by fact
      with \<open>A\<^sub>P \<sharp>* Q\<close> \<open>A\<^sub>Q \<sharp>* A\<^sub>P\<close> have "A\<^sub>P \<sharp>* \<Psi>\<^sub>Q"
        by(auto dest: extractFrameFreshChain)
      have FrR: "extractFrame R = \<langle>A\<^sub>R, \<Psi>\<^sub>R\<rangle>" by fact
      with \<open>A\<^sub>P \<sharp>* R\<close> \<open>A\<^sub>R \<sharp>* A\<^sub>P\<close> have "A\<^sub>P \<sharp>* \<Psi>\<^sub>R"
        by(auto dest: extractFrameFreshChain)

      from \<open>(\<Psi> \<otimes> \<Psi>\<^sub>P) \<otimes> \<Psi>\<^sub>R \<rhd> Q \<longmapsto>M\<lparr>\<nu>*xvec\<rparr>\<langle>N\<rangle> \<prec> Q'\<close> \<open>A\<^sub>P \<sharp>* Q\<close> \<open>xvec \<sharp>* A\<^sub>P\<close> \<open>xvec \<sharp>* M\<close> \<open>distinct xvec\<close> have "A\<^sub>P \<sharp>* N"
        by(auto intro: outputFreshChainDerivative)

      from \<open>(\<Psi> \<otimes> \<Psi>\<^sub>P) \<otimes> \<Psi>\<^sub>R \<rhd> Q \<longmapsto>M\<lparr>\<nu>*xvec\<rparr>\<langle>N\<rangle> \<prec> Q'\<close> have "(\<Psi> \<otimes> \<Psi>\<^sub>R) \<otimes> \<Psi>\<^sub>P \<rhd> Q \<longmapsto>M\<lparr>\<nu>*xvec\<rparr>\<langle>N\<rangle> \<prec> Q'"
        by(metis statEqTransition Associativity Commutativity Composition)
      then have "\<Psi> \<otimes> \<Psi>\<^sub>R \<rhd> P \<parallel> Q \<longmapsto>M\<lparr>\<nu>*xvec\<rparr>\<langle>N\<rangle> \<prec> (P \<parallel> Q')" using FrP \<open>A\<^sub>P \<sharp>* \<Psi>\<close> \<open>A\<^sub>P \<sharp>* \<Psi>\<^sub>R\<close> \<open>A\<^sub>P \<sharp>* Q\<close> \<open>A\<^sub>P \<sharp>* M\<close> \<open>A\<^sub>P \<sharp>* N\<close> \<open>xvec \<sharp>* P\<close> \<open>xvec \<sharp>* A\<^sub>P\<close>
        by(intro Par2) auto
      moreover from FrP FrQ \<open>A\<^sub>P \<sharp>* \<Psi>\<^sub>Q\<close> \<open>A\<^sub>Q \<sharp>* A\<^sub>P\<close> \<open>A\<^sub>Q \<sharp>* \<Psi>\<^sub>P\<close> have "extractFrame(P \<parallel> Q) = \<langle>(A\<^sub>P@A\<^sub>Q), \<Psi>\<^sub>P \<otimes> \<Psi>\<^sub>Q\<rangle>"
        by simp+
      moreover from  \<open>(\<Psi> \<otimes> \<Psi>\<^sub>P) \<otimes> \<Psi>\<^sub>Q \<rhd> R \<longmapsto>K\<lparr>N\<rparr> \<prec> R'\<close> have "\<Psi> \<otimes> \<Psi>\<^sub>P \<otimes> \<Psi>\<^sub>Q \<rhd> R \<longmapsto>K\<lparr>N\<rparr> \<prec> R'"
        by(metis statEqTransition Associativity)
      moreover note \<open>extractFrame R = \<langle>A\<^sub>R, \<Psi>\<^sub>R\<rangle>\<close>
      moreover from \<open>(\<Psi> \<otimes> \<Psi>\<^sub>P) \<otimes> \<Psi>\<^sub>Q \<otimes> \<Psi>\<^sub>R \<turnstile> M \<leftrightarrow> K\<close> have "\<Psi> \<otimes> (\<Psi>\<^sub>P \<otimes> \<Psi>\<^sub>Q) \<otimes> \<Psi>\<^sub>R \<turnstile> M \<leftrightarrow> K"
        by(metis statEqEnt Associativity Commutativity Composition)
      ultimately have "\<Psi> \<rhd> (P \<parallel> Q) \<parallel> R \<longmapsto>\<tau> \<prec> \<lparr>\<nu>*xvec\<rparr>((P \<parallel> Q') \<parallel> R')"
        using \<open>A\<^sub>P \<sharp>* \<Psi>\<close> \<open>A\<^sub>Q \<sharp>* \<Psi>\<close> \<open>A\<^sub>R \<sharp>* \<Psi>\<close> \<open>A\<^sub>P \<sharp>* P\<close> \<open>A\<^sub>Q \<sharp>* P\<close> \<open>A\<^sub>R \<sharp>* P\<close> \<open>A\<^sub>P \<sharp>* Q\<close> \<open>A\<^sub>Q \<sharp>* Q\<close> \<open>A\<^sub>R \<sharp>* Q\<close> \<open>A\<^sub>P \<sharp>* R\<close> \<open>A\<^sub>Q \<sharp>* R\<close> \<open>A\<^sub>R \<sharp>* R\<close>
          \<open>A\<^sub>P \<sharp>* M\<close> \<open>A\<^sub>Q \<sharp>* M\<close> \<open>A\<^sub>R \<sharp>* K\<close> \<open>A\<^sub>R \<sharp>* A\<^sub>P\<close> \<open>A\<^sub>Q \<sharp>* A\<^sub>R\<close> \<open>xvec \<sharp>* R\<close>
        by(intro Comm2) (assumption | simp)+
      moreover from \<open>xvec \<sharp>* \<Psi>\<close> \<open>xvec \<sharp>* P\<close> have "(\<Psi>, \<lparr>\<nu>*xvec\<rparr>((P \<parallel> Q') \<parallel> R'), P \<parallel> (\<lparr>\<nu>*xvec\<rparr>(Q' \<parallel> R'))) \<in> Rel"
        by(rule C2)
      ultimately show ?case by blast
    next
      case(cBrMerge \<Psi>\<^sub>R M N Q' A\<^sub>Q \<Psi>\<^sub>Q R' A\<^sub>R)
      from \<open>A\<^sub>P \<sharp>* \<alpha>\<close> \<open>\<alpha> = \<questiondown>M\<lparr>N\<rparr>\<close> have "A\<^sub>P \<sharp>* M" and "A\<^sub>P \<sharp>* N" by simp+
      from \<open>A\<^sub>Q \<sharp>* (A\<^sub>P, \<Psi>\<^sub>P, P, Q, R, \<Psi>)\<close>
      have "A\<^sub>Q \<sharp>* P" and "A\<^sub>Q \<sharp>* Q" and "A\<^sub>Q \<sharp>* R" and "A\<^sub>Q \<sharp>* A\<^sub>P" and "A\<^sub>Q \<sharp>* \<Psi>\<^sub>P"  and "A\<^sub>Q \<sharp>* \<Psi>" by simp+
      from \<open>A\<^sub>R \<sharp>* (A\<^sub>P, \<Psi>\<^sub>P, P, Q, R, \<Psi>)\<close> have "A\<^sub>R \<sharp>* P" and "A\<^sub>R \<sharp>* Q" and "A\<^sub>R \<sharp>* R" and "A\<^sub>R \<sharp>* A\<^sub>P"  and "A\<^sub>R \<sharp>* \<Psi>" by simp+

      have FrQ: "extractFrame Q = \<langle>A\<^sub>Q, \<Psi>\<^sub>Q\<rangle>" by fact
      with \<open>A\<^sub>P \<sharp>* Q\<close> \<open>A\<^sub>Q \<sharp>* A\<^sub>P\<close> have "A\<^sub>P \<sharp>* \<Psi>\<^sub>Q"
        by(auto dest: extractFrameFreshChain)
      have FrR: "extractFrame R = \<langle>A\<^sub>R, \<Psi>\<^sub>R\<rangle>" by fact
      with \<open>A\<^sub>P \<sharp>* R\<close> \<open>A\<^sub>R \<sharp>* A\<^sub>P\<close> have "A\<^sub>P \<sharp>* \<Psi>\<^sub>R"
        by(auto dest: extractFrameFreshChain)

      from \<open>(\<Psi> \<otimes> \<Psi>\<^sub>P) \<otimes> \<Psi>\<^sub>R \<rhd> Q \<longmapsto>\<questiondown>M\<lparr>N\<rparr> \<prec> Q'\<close> have "(\<Psi> \<otimes> \<Psi>\<^sub>R) \<otimes> \<Psi>\<^sub>P \<rhd> Q \<longmapsto>\<questiondown>M\<lparr>N\<rparr> \<prec> Q'"
        by(metis statEqTransition Associativity Commutativity Composition)
      then have "\<Psi> \<otimes> \<Psi>\<^sub>R \<rhd> P \<parallel> Q \<longmapsto>\<questiondown>M\<lparr>N\<rparr> \<prec> (P \<parallel> Q')" using FrP \<open>A\<^sub>P \<sharp>* \<Psi>\<close> \<open>A\<^sub>P \<sharp>* \<Psi>\<^sub>R\<close> \<open>A\<^sub>P \<sharp>* Q\<close> \<open>A\<^sub>P \<sharp>* M\<close> \<open>A\<^sub>P \<sharp>* N\<close>
        by(intro Par2) auto
      moreover from FrP FrQ \<open>A\<^sub>P \<sharp>* \<Psi>\<^sub>Q\<close> \<open>A\<^sub>Q \<sharp>* A\<^sub>P\<close> \<open>A\<^sub>Q \<sharp>* \<Psi>\<^sub>P\<close> have "extractFrame(P \<parallel> Q) = \<langle>(A\<^sub>P@A\<^sub>Q), \<Psi>\<^sub>P \<otimes> \<Psi>\<^sub>Q\<rangle>"
        by simp
      moreover from  \<open>(\<Psi> \<otimes> \<Psi>\<^sub>P) \<otimes> \<Psi>\<^sub>Q \<rhd> R \<longmapsto>\<questiondown>M\<lparr>N\<rparr> \<prec> R'\<close> have "\<Psi> \<otimes> \<Psi>\<^sub>P \<otimes> \<Psi>\<^sub>Q \<rhd> R \<longmapsto>\<questiondown>M\<lparr>N\<rparr> \<prec> R'"
        by(metis statEqTransition Associativity)
      moreover note \<open>extractFrame R = \<langle>A\<^sub>R, \<Psi>\<^sub>R\<rangle>\<close>
      ultimately have "\<Psi> \<rhd> (P \<parallel> Q) \<parallel> R \<longmapsto>\<questiondown>M\<lparr>N\<rparr> \<prec> (P \<parallel> Q') \<parallel> R'"
        using \<open>A\<^sub>P \<sharp>* \<Psi>\<close> \<open>A\<^sub>Q \<sharp>* \<Psi>\<close> \<open>A\<^sub>R \<sharp>* \<Psi>\<close> \<open>A\<^sub>P \<sharp>* P\<close> \<open>A\<^sub>Q \<sharp>* P\<close> \<open>A\<^sub>R \<sharp>* P\<close> \<open>A\<^sub>P \<sharp>* Q\<close> \<open>A\<^sub>Q \<sharp>* Q\<close> \<open>A\<^sub>R \<sharp>* Q\<close> \<open>A\<^sub>P \<sharp>* R\<close> \<open>A\<^sub>Q \<sharp>* R\<close> \<open>A\<^sub>R \<sharp>* R\<close>
          \<open>A\<^sub>P \<sharp>* M\<close> \<open>A\<^sub>Q \<sharp>* M\<close> \<open>A\<^sub>R \<sharp>* M\<close> \<open>A\<^sub>R \<sharp>* A\<^sub>P\<close> \<open>A\<^sub>Q \<sharp>* A\<^sub>R\<close>
        by(auto intro: BrMerge)
      moreover have "(\<Psi>, (P \<parallel> Q') \<parallel> R', P \<parallel> (Q' \<parallel> R')) \<in> Rel"
        by(rule C1)
      ultimately show ?case by blast
    next
      case(cBrComm1 \<Psi>\<^sub>R M N Q' A\<^sub>Q \<Psi>\<^sub>Q xvec R' A\<^sub>R)
      from \<open>\<exclamdown>M\<lparr>\<nu>*xvec\<rparr>\<langle>N\<rangle> = \<alpha>\<close> have "xvec = bn \<alpha>"
        by(auto simp add: action.inject)
      from \<open>\<exclamdown>M\<lparr>\<nu>*xvec\<rparr>\<langle>N\<rangle> = \<alpha>\<close> \<open>A\<^sub>P \<sharp>* \<alpha>\<close>
      have "A\<^sub>P \<sharp>* xvec" and "A\<^sub>P \<sharp>* M" and "A\<^sub>P \<sharp>* N" by auto
      from \<open>xvec = bn \<alpha>\<close> \<open>bn \<alpha> \<sharp>* P\<close> \<open>bn \<alpha> \<sharp>* \<Psi>\<close> \<open>bn \<alpha> \<sharp>* \<Psi>\<^sub>P\<close> have "xvec \<sharp>* P" and "xvec \<sharp>* \<Psi>" and "xvec \<sharp>* \<Psi>\<^sub>P"
        by simp+
      from \<open>A\<^sub>Q \<sharp>* (A\<^sub>P, \<Psi>\<^sub>P, P, Q, R, \<Psi>)\<close>
      have "A\<^sub>Q \<sharp>* P" and "A\<^sub>Q \<sharp>* Q" and "A\<^sub>Q \<sharp>* R" and "A\<^sub>Q \<sharp>* A\<^sub>P" and "A\<^sub>Q \<sharp>* \<Psi>\<^sub>P"  and "A\<^sub>Q \<sharp>* \<Psi>" by simp+
      from \<open>A\<^sub>R \<sharp>* (A\<^sub>P, \<Psi>\<^sub>P, P, Q, R, \<Psi>)\<close> have "A\<^sub>R \<sharp>* P" and "A\<^sub>R \<sharp>* Q" and "A\<^sub>R \<sharp>* R" and "A\<^sub>R \<sharp>* A\<^sub>P"  and "A\<^sub>R \<sharp>* \<Psi>" by simp+

      have FrQ: "extractFrame Q = \<langle>A\<^sub>Q, \<Psi>\<^sub>Q\<rangle>" by fact
      with \<open>A\<^sub>P \<sharp>* Q\<close> \<open>A\<^sub>Q \<sharp>* A\<^sub>P\<close> have "A\<^sub>P \<sharp>* \<Psi>\<^sub>Q"
        by(auto dest: extractFrameFreshChain)
      have FrR: "extractFrame R = \<langle>A\<^sub>R, \<Psi>\<^sub>R\<rangle>" by fact
      with \<open>A\<^sub>P \<sharp>* R\<close> \<open>A\<^sub>R \<sharp>* A\<^sub>P\<close> have "A\<^sub>P \<sharp>* \<Psi>\<^sub>R"
        by(auto dest: extractFrameFreshChain)

      from \<open>(\<Psi> \<otimes> \<Psi>\<^sub>P) \<otimes> \<Psi>\<^sub>R \<rhd> Q \<longmapsto>\<questiondown>M\<lparr>N\<rparr> \<prec> Q'\<close> have "(\<Psi> \<otimes> \<Psi>\<^sub>R) \<otimes> \<Psi>\<^sub>P \<rhd> Q \<longmapsto>\<questiondown>M\<lparr>N\<rparr> \<prec> Q'"
        by(metis statEqTransition Associativity Commutativity Composition)
      then have "\<Psi> \<otimes> \<Psi>\<^sub>R \<rhd> P \<parallel> Q \<longmapsto>\<questiondown>M\<lparr>N\<rparr> \<prec> (P \<parallel> Q')" using FrP \<open>A\<^sub>P \<sharp>* \<Psi>\<close> \<open>A\<^sub>P \<sharp>* \<Psi>\<^sub>R\<close> \<open>A\<^sub>P \<sharp>* Q\<close> \<open>A\<^sub>P \<sharp>* M\<close> \<open>A\<^sub>P \<sharp>* N\<close>
        by(intro Par2) auto
      moreover from FrP FrQ \<open>A\<^sub>P \<sharp>* \<Psi>\<^sub>Q\<close> \<open>A\<^sub>Q \<sharp>* A\<^sub>P\<close> \<open>A\<^sub>Q \<sharp>* \<Psi>\<^sub>P\<close> have "extractFrame(P \<parallel> Q) = \<langle>(A\<^sub>P@A\<^sub>Q), \<Psi>\<^sub>P \<otimes> \<Psi>\<^sub>Q\<rangle>"
        by simp
      moreover from  \<open>(\<Psi> \<otimes> \<Psi>\<^sub>P) \<otimes> \<Psi>\<^sub>Q \<rhd> R \<longmapsto>\<exclamdown>M\<lparr>\<nu>*xvec\<rparr>\<langle>N\<rangle> \<prec> R'\<close> have "\<Psi> \<otimes> \<Psi>\<^sub>P \<otimes> \<Psi>\<^sub>Q \<rhd> R \<longmapsto>\<exclamdown>M\<lparr>\<nu>*xvec\<rparr>\<langle>N\<rangle> \<prec> R'"
        by(metis statEqTransition Associativity)
      moreover note \<open>extractFrame R = \<langle>A\<^sub>R, \<Psi>\<^sub>R\<rangle>\<close>
      ultimately have "\<Psi> \<rhd> (P \<parallel> Q) \<parallel> R \<longmapsto>\<exclamdown>M\<lparr>\<nu>*xvec\<rparr>\<langle>N\<rangle> \<prec> ((P \<parallel> Q') \<parallel> R')"
        using \<open>A\<^sub>P \<sharp>* \<Psi>\<close> \<open>A\<^sub>Q \<sharp>* \<Psi>\<close> \<open>A\<^sub>R \<sharp>* \<Psi>\<close> \<open>A\<^sub>P \<sharp>* P\<close> \<open>A\<^sub>Q \<sharp>* P\<close> \<open>A\<^sub>R \<sharp>* P\<close> \<open>A\<^sub>P \<sharp>* Q\<close> \<open>A\<^sub>Q \<sharp>* Q\<close> \<open>A\<^sub>R \<sharp>* Q\<close> \<open>A\<^sub>P \<sharp>* R\<close> \<open>A\<^sub>Q \<sharp>* R\<close> \<open>A\<^sub>R \<sharp>* R\<close>
          \<open>A\<^sub>P \<sharp>* M\<close> \<open>A\<^sub>Q \<sharp>* M\<close> \<open>A\<^sub>R \<sharp>* M\<close> \<open>A\<^sub>R \<sharp>* A\<^sub>P\<close> \<open>A\<^sub>Q \<sharp>* A\<^sub>R\<close> \<open>xvec \<sharp>* P\<close> \<open>xvec \<sharp>* Q\<close>
        by(intro BrComm1) (assumption | simp)+
      moreover have "(\<Psi>, ((P \<parallel> Q') \<parallel> R'), (P \<parallel> (Q' \<parallel> R'))) \<in> Rel"
        by(rule C1)
      ultimately show ?case by blast
    next
      case(cBrComm2 \<Psi>\<^sub>R M xvec N Q' A\<^sub>Q \<Psi>\<^sub>Q R' A\<^sub>R)
      from \<open>\<exclamdown>M\<lparr>\<nu>*xvec\<rparr>\<langle>N\<rangle> = \<alpha>\<close> have "xvec = bn \<alpha>"
        by(auto simp add: action.inject)
      from \<open>\<exclamdown>M\<lparr>\<nu>*xvec\<rparr>\<langle>N\<rangle> = \<alpha>\<close> \<open>A\<^sub>P \<sharp>* \<alpha>\<close>
      have "A\<^sub>P \<sharp>* xvec" and "A\<^sub>P \<sharp>* M" and "A\<^sub>P \<sharp>* N" by auto
      from \<open>xvec = bn \<alpha>\<close> \<open>bn \<alpha> \<sharp>* P\<close> \<open>bn \<alpha> \<sharp>* \<Psi>\<close> \<open>bn \<alpha> \<sharp>* \<Psi>\<^sub>P\<close> have "xvec \<sharp>* P" and "xvec \<sharp>* \<Psi>" and "xvec \<sharp>* \<Psi>\<^sub>P"
        by simp+
      from \<open>A\<^sub>Q \<sharp>* (A\<^sub>P,  \<Psi>\<^sub>P, P, Q, R, \<Psi>)\<close>
      have "A\<^sub>Q \<sharp>* P" and "A\<^sub>Q \<sharp>* Q" and "A\<^sub>Q \<sharp>* R" and "A\<^sub>Q \<sharp>* A\<^sub>P" and "A\<^sub>Q \<sharp>* \<Psi>" and "A\<^sub>Q \<sharp>* \<Psi>\<^sub>P" by simp+
      from \<open>A\<^sub>R \<sharp>* (A\<^sub>P,  \<Psi>\<^sub>P, P, Q, R, \<Psi>)\<close> have "A\<^sub>R \<sharp>* P" and "A\<^sub>R \<sharp>* Q" and "A\<^sub>R \<sharp>* R" and "A\<^sub>R \<sharp>* A\<^sub>P"and "A\<^sub>R \<sharp>* \<Psi>" by simp+

      have FrQ: "extractFrame Q = \<langle>A\<^sub>Q, \<Psi>\<^sub>Q\<rangle>" by fact
      with \<open>A\<^sub>P \<sharp>* Q\<close> \<open>A\<^sub>Q \<sharp>* A\<^sub>P\<close> have "A\<^sub>P \<sharp>* \<Psi>\<^sub>Q"
        by(auto dest: extractFrameFreshChain)
      have FrR: "extractFrame R = \<langle>A\<^sub>R, \<Psi>\<^sub>R\<rangle>" by fact
      with \<open>A\<^sub>P \<sharp>* R\<close> \<open>A\<^sub>R \<sharp>* A\<^sub>P\<close> have "A\<^sub>P \<sharp>* \<Psi>\<^sub>R"
        by(auto dest: extractFrameFreshChain)

      from \<open>(\<Psi> \<otimes> \<Psi>\<^sub>P) \<otimes> \<Psi>\<^sub>R \<rhd> Q \<longmapsto>\<exclamdown>M\<lparr>\<nu>*xvec\<rparr>\<langle>N\<rangle> \<prec> Q'\<close> have "(\<Psi> \<otimes> \<Psi>\<^sub>R) \<otimes> \<Psi>\<^sub>P \<rhd> Q \<longmapsto>\<exclamdown>M\<lparr>\<nu>*xvec\<rparr>\<langle>N\<rangle> \<prec> Q'"
        by(metis statEqTransition Associativity Commutativity Composition)
      then have "\<Psi> \<otimes> \<Psi>\<^sub>R \<rhd> P \<parallel> Q \<longmapsto>\<exclamdown>M\<lparr>\<nu>*xvec\<rparr>\<langle>N\<rangle> \<prec> (P \<parallel> Q')" using FrP \<open>A\<^sub>P \<sharp>* \<Psi>\<close> \<open>A\<^sub>P \<sharp>* \<Psi>\<^sub>R\<close> \<open>A\<^sub>P \<sharp>* Q\<close> \<open>A\<^sub>P \<sharp>* M\<close> \<open>A\<^sub>P \<sharp>* N\<close> \<open>xvec \<sharp>* P\<close> \<open>A\<^sub>P \<sharp>* xvec\<close>
        by(intro Par2) auto
      moreover from FrP FrQ \<open>A\<^sub>P \<sharp>* \<Psi>\<^sub>Q\<close> \<open>A\<^sub>Q \<sharp>* A\<^sub>P\<close> \<open>A\<^sub>Q \<sharp>* \<Psi>\<^sub>P\<close> have "extractFrame(P \<parallel> Q) = \<langle>(A\<^sub>P@A\<^sub>Q), \<Psi>\<^sub>P \<otimes> \<Psi>\<^sub>Q\<rangle>"
        by simp+
      moreover from  \<open>(\<Psi> \<otimes> \<Psi>\<^sub>P) \<otimes> \<Psi>\<^sub>Q \<rhd> R \<longmapsto>\<questiondown>M\<lparr>N\<rparr> \<prec> R'\<close> have "\<Psi> \<otimes> \<Psi>\<^sub>P \<otimes> \<Psi>\<^sub>Q \<rhd> R \<longmapsto>\<questiondown>M\<lparr>N\<rparr> \<prec> R'"
        by(metis statEqTransition Associativity)
      moreover note \<open>extractFrame R = \<langle>A\<^sub>R, \<Psi>\<^sub>R\<rangle>\<close>
      ultimately have "\<Psi> \<rhd> (P \<parallel> Q) \<parallel> R \<longmapsto>\<exclamdown>M\<lparr>\<nu>*xvec\<rparr>\<langle>N\<rangle> \<prec> ((P \<parallel> Q') \<parallel> R')"
        using \<open>A\<^sub>P \<sharp>* \<Psi>\<close> \<open>A\<^sub>Q \<sharp>* \<Psi>\<close> \<open>A\<^sub>R \<sharp>* \<Psi>\<close> \<open>A\<^sub>P \<sharp>* P\<close> \<open>A\<^sub>Q \<sharp>* P\<close> \<open>A\<^sub>R \<sharp>* P\<close> \<open>A\<^sub>P \<sharp>* Q\<close> \<open>A\<^sub>Q \<sharp>* Q\<close> \<open>A\<^sub>R \<sharp>* Q\<close> \<open>A\<^sub>P \<sharp>* R\<close> \<open>A\<^sub>Q \<sharp>* R\<close> \<open>A\<^sub>R \<sharp>* R\<close>
          \<open>A\<^sub>P \<sharp>* M\<close> \<open>A\<^sub>Q \<sharp>* M\<close> \<open>A\<^sub>R \<sharp>* M\<close> \<open>A\<^sub>R \<sharp>* A\<^sub>P\<close> \<open>A\<^sub>Q \<sharp>* A\<^sub>R\<close> \<open>xvec \<sharp>* R\<close>
        by(auto intro: BrComm2)
      moreover have "(\<Psi>, ((P \<parallel> Q') \<parallel> R'), (P \<parallel> (Q' \<parallel> R'))) \<in> Rel"
        by(rule C1)
      ultimately show ?case by blast
    qed
  next
    case(cComm1 \<Psi>\<^sub>Q\<^sub>R M N P' A\<^sub>P \<Psi>\<^sub>P K xvec QR' A\<^sub>Q\<^sub>R)
    from \<open>xvec \<sharp>* (\<Psi>, P, Q, R, \<alpha>)\<close> have "xvec \<sharp>* Q" and "xvec \<sharp>* R" by simp+
    from \<open>A\<^sub>Q\<^sub>R \<sharp>* (\<Psi>, P, Q, R, \<alpha>)\<close> have "A\<^sub>Q\<^sub>R \<sharp>* Q" and "A\<^sub>Q\<^sub>R \<sharp>* R" and "A\<^sub>Q\<^sub>R \<sharp>* \<Psi>" by simp+
    from \<open>A\<^sub>P \<sharp>* (Q \<parallel> R)\<close> have "A\<^sub>P \<sharp>* Q" and "A\<^sub>P \<sharp>* R" by simp+
    have PTrans: "\<Psi> \<otimes> \<Psi>\<^sub>Q\<^sub>R \<rhd> P \<longmapsto>M\<lparr>N\<rparr> \<prec> P'" and FrP: "extractFrame P = \<langle>A\<^sub>P, \<Psi>\<^sub>P\<rangle>" and MeqK: "\<Psi> \<otimes> \<Psi>\<^sub>P \<otimes> \<Psi>\<^sub>Q\<^sub>R \<turnstile> M \<leftrightarrow> K" by fact+
    note \<open>\<Psi> \<otimes> \<Psi>\<^sub>P \<rhd> Q \<parallel> R \<longmapsto>K\<lparr>\<nu>*xvec\<rparr>\<langle>N\<rangle> \<prec> QR'\<close>
    moreover from \<open>xvec \<sharp>* \<Psi>\<close> \<open>xvec \<sharp>* \<Psi>\<^sub>P\<close> have "xvec \<sharp>* (\<Psi> \<otimes> \<Psi>\<^sub>P)" by force
    moreover note \<open>xvec \<sharp>* Q\<close>\<open>xvec \<sharp>* R\<close> \<open>xvec \<sharp>* K\<close>
      \<open>extractFrame(Q \<parallel> R) = \<langle>A\<^sub>Q\<^sub>R, \<Psi>\<^sub>Q\<^sub>R\<rangle>\<close> \<open>distinct A\<^sub>Q\<^sub>R\<close>
    moreover from \<open>A\<^sub>Q\<^sub>R \<sharp>* \<Psi>\<close> \<open>A\<^sub>Q\<^sub>R \<sharp>* \<Psi>\<^sub>P\<close> have "A\<^sub>Q\<^sub>R \<sharp>* (\<Psi> \<otimes> \<Psi>\<^sub>P)" by force
    ultimately show ?case using \<open>A\<^sub>Q\<^sub>R \<sharp>* Q\<close> \<open>A\<^sub>Q\<^sub>R \<sharp>* R\<close> \<open>A\<^sub>Q\<^sub>R \<sharp>* K\<close>
    proof(induct rule: parCasesOutputFrame)
      case(cPar1 Q' A\<^sub>Q \<Psi>\<^sub>Q A\<^sub>R \<Psi>\<^sub>R)
      have Aeq: "A\<^sub>Q\<^sub>R = A\<^sub>Q@A\<^sub>R" and \<Psi>eq: "\<Psi>\<^sub>Q\<^sub>R = \<Psi>\<^sub>Q \<otimes> \<Psi>\<^sub>R" by fact+
      from PTrans \<Psi>eq have "(\<Psi> \<otimes> \<Psi>\<^sub>R) \<otimes> \<Psi>\<^sub>Q \<rhd> P \<longmapsto>M\<lparr>N\<rparr> \<prec> P'"
        by(metis statEqTransition Associativity Commutativity Composition)
      moreover note FrP
      moreover from \<open>(\<Psi> \<otimes> \<Psi>\<^sub>P) \<otimes> \<Psi>\<^sub>R \<rhd> Q \<longmapsto>K\<lparr>\<nu>*xvec\<rparr>\<langle>N\<rangle> \<prec> Q'\<close> have "(\<Psi> \<otimes> \<Psi>\<^sub>R) \<otimes> \<Psi>\<^sub>P \<rhd> Q \<longmapsto>K\<lparr>\<nu>*xvec\<rparr>\<langle>N\<rangle> \<prec> Q'"
        by(metis statEqTransition Associativity Commutativity Composition)
      moreover note \<open>extractFrame Q = \<langle>A\<^sub>Q, \<Psi>\<^sub>Q\<rangle>\<close>
      moreover from MeqK \<Psi>eq have "(\<Psi> \<otimes> \<Psi>\<^sub>R) \<otimes> \<Psi>\<^sub>P \<otimes> \<Psi>\<^sub>Q \<turnstile> M \<leftrightarrow> K"
        by(metis statEqEnt Associativity Commutativity Composition)
      moreover from \<open>A\<^sub>P \<sharp>* R\<close> \<open>A\<^sub>P \<sharp>* A\<^sub>Q\<^sub>R\<close> Aeq \<open>extractFrame R = \<langle>A\<^sub>R, \<Psi>\<^sub>R\<rangle>\<close> have "A\<^sub>P \<sharp>* A\<^sub>Q" and "A\<^sub>P \<sharp>* \<Psi>\<^sub>R"
        by(auto dest:  extractFrameFreshChain)
      moreover from \<open>A\<^sub>Q\<^sub>R \<sharp>* P\<close> \<open>A\<^sub>Q\<^sub>R \<sharp>* \<Psi>\<close> Aeq have "A\<^sub>Q \<sharp>* P" and "A\<^sub>Q \<sharp>* \<Psi>" by simp+
      ultimately have "\<Psi> \<otimes> \<Psi>\<^sub>R \<rhd> P \<parallel> Q \<longmapsto>\<tau> \<prec> \<lparr>\<nu>*xvec\<rparr>(P' \<parallel> Q')"
        using \<open>A\<^sub>P \<sharp>* \<Psi>\<close> \<open>A\<^sub>P \<sharp>* P\<close> \<open>A\<^sub>P \<sharp>* Q\<close> \<open>A\<^sub>P \<sharp>* M\<close> \<open>A\<^sub>P \<sharp>* A\<^sub>Q\<close> \<open>A\<^sub>Q \<sharp>* \<Psi>\<close> \<open>A\<^sub>Q \<sharp>* \<Psi>\<^sub>R\<close> \<open>A\<^sub>Q \<sharp>* P\<close> \<open>A\<^sub>Q \<sharp>* Q\<close> \<open>A\<^sub>Q \<sharp>* K\<close> \<open>xvec \<sharp>* P\<close>
        by(intro Comm1) (assumption | force)+
      moreover from \<open>A\<^sub>Q\<^sub>R \<sharp>* \<Psi>\<close> Aeq have "A\<^sub>R \<sharp>* \<Psi>" by simp
      moreover from \<open>A\<^sub>Q\<^sub>R \<sharp>* P\<close> Aeq have "A\<^sub>R \<sharp>* P" by simp
      ultimately have "\<Psi> \<rhd> (P \<parallel> Q) \<parallel> R \<longmapsto>\<tau> \<prec> (\<lparr>\<nu>*xvec\<rparr>(P' \<parallel> Q')) \<parallel> R" using \<open>extractFrame R = \<langle>A\<^sub>R, \<Psi>\<^sub>R\<rangle>\<close> \<open>A\<^sub>R \<sharp>* Q\<close>
        by(intro Par1) (assumption | simp)+
      moreover from \<open>xvec \<sharp>* \<Psi>\<close> \<open>xvec \<sharp>* R\<close> have "(\<Psi>, (\<lparr>\<nu>*xvec\<rparr>(P' \<parallel> Q')) \<parallel> R, \<lparr>\<nu>*xvec\<rparr>(P' \<parallel> (Q' \<parallel> R))) \<in> Rel"
        by(rule C3)
      ultimately show ?case by blast
    next
      case(cPar2 R' A\<^sub>Q \<Psi>\<^sub>Q A\<^sub>R \<Psi>\<^sub>R)
      have Aeq: "A\<^sub>Q\<^sub>R = A\<^sub>Q@A\<^sub>R" and \<Psi>eq: "\<Psi>\<^sub>Q\<^sub>R = \<Psi>\<^sub>Q \<otimes> \<Psi>\<^sub>R" by fact+
      from \<open>A\<^sub>Q\<^sub>R \<sharp>* \<Psi>\<close> \<open>A\<^sub>Q\<^sub>R \<sharp>* P\<close> \<open>A\<^sub>Q\<^sub>R \<sharp>* \<Psi>\<^sub>P\<close> \<open>A\<^sub>P \<sharp>* A\<^sub>Q\<^sub>R\<close> Aeq have "A\<^sub>R \<sharp>* \<Psi>" and "A\<^sub>R \<sharp>* \<Psi>\<^sub>P" and "A\<^sub>P \<sharp>* A\<^sub>R" and "A\<^sub>P \<sharp>* A\<^sub>Q" and "A\<^sub>R \<sharp>* P" by simp+
      from \<open>A\<^sub>Q\<^sub>R \<sharp>* \<Psi>\<close> Aeq have "A\<^sub>Q \<sharp>* \<Psi>" by simp
      from \<open>A\<^sub>Q\<^sub>R \<sharp>* P\<close> \<open>A\<^sub>P \<sharp>* A\<^sub>Q\<^sub>R\<close> Aeq FrP have "A\<^sub>Q \<sharp>* \<Psi>\<^sub>P" by(auto dest: extractFrameFreshChain)
      from \<open>A\<^sub>P \<sharp>* A\<^sub>Q\<^sub>R\<close> \<open>extractFrame R = \<langle>A\<^sub>R, \<Psi>\<^sub>R\<rangle>\<close> \<open>extractFrame Q = \<langle>A\<^sub>Q, \<Psi>\<^sub>Q\<rangle>\<close> Aeq \<open>A\<^sub>P \<sharp>* Q\<close> \<open>A\<^sub>P \<sharp>* R\<close> have "A\<^sub>P \<sharp>* \<Psi>\<^sub>Q" and  "A\<^sub>P \<sharp>* \<Psi>\<^sub>R" by(auto dest: extractFrameFreshChain)
      have RTrans: "(\<Psi> \<otimes> \<Psi>\<^sub>P) \<otimes> \<Psi>\<^sub>Q \<rhd> R \<longmapsto>K\<lparr>\<nu>*xvec\<rparr>\<langle>N\<rangle> \<prec> R'" and FrR: "extractFrame R = \<langle>A\<^sub>R, \<Psi>\<^sub>R\<rangle>" by fact+
      then have "(\<Psi> \<otimes> \<Psi>\<^sub>P) \<otimes> \<Psi>\<^sub>Q \<rhd> R \<longmapsto> ROut K (\<lparr>\<nu>*xvec\<rparr>N \<prec>' R')" by(simp add: residualInject)
      then obtain K' where KeqK': "((\<Psi> \<otimes> \<Psi>\<^sub>P) \<otimes> \<Psi>\<^sub>Q) \<otimes> \<Psi>\<^sub>R \<turnstile> K \<leftrightarrow> K'" and "A\<^sub>P \<sharp>* K'" and "A\<^sub>Q \<sharp>* K'"
        using \<open>A\<^sub>P \<sharp>* R\<close> \<open>A\<^sub>Q \<sharp>* R\<close> \<open>A\<^sub>R \<sharp>* \<Psi>\<close> \<open>A\<^sub>R \<sharp>* \<Psi>\<^sub>P\<close> \<open>A\<^sub>R \<sharp>* \<Psi>\<^sub>Q\<close> \<open>A\<^sub>Q \<sharp>* A\<^sub>R\<close> \<open>A\<^sub>P \<sharp>* A\<^sub>R\<close> \<open>A\<^sub>R \<sharp>* R\<close> \<open>A\<^sub>R \<sharp>* R\<close> \<open>A\<^sub>R \<sharp>* K\<close> \<open>distinct A\<^sub>R\<close> \<open>xvec \<sharp>* K\<close> \<open>distinct xvec\<close> FrR
        using outputObtainPrefix[where B="A\<^sub>P@A\<^sub>Q"]
        by (smt (verit, ccfv_threshold) freshChainAppend freshChainSym freshCompChain(1))
      from PTrans \<Psi>eq have "(\<Psi> \<otimes> \<Psi>\<^sub>R) \<otimes> \<Psi>\<^sub>Q \<rhd> P \<longmapsto>M\<lparr>N\<rparr> \<prec> P'"
        by(metis statEqTransition Associativity Commutativity Composition)
      moreover from MeqK KeqK' \<Psi>eq have MeqK': "((\<Psi> \<otimes> \<Psi>\<^sub>R) \<otimes> \<Psi>\<^sub>Q) \<otimes> \<Psi>\<^sub>P \<turnstile> M \<leftrightarrow> K'"
        by(metis statEqEnt Associativity Commutativity Composition chanEqTrans)
      ultimately have "(\<Psi> \<otimes> \<Psi>\<^sub>R) \<otimes> \<Psi>\<^sub>Q \<rhd> P \<longmapsto>K'\<lparr>N\<rparr> \<prec> P'" using FrP \<open>distinct A\<^sub>P\<close> \<open>A\<^sub>P \<sharp>* \<Psi>\<close> \<open>A\<^sub>P \<sharp>* P\<close> \<open>A\<^sub>P \<sharp>* M\<close> \<open>A\<^sub>P \<sharp>* K'\<close> \<open>A\<^sub>P \<sharp>* \<Psi>\<^sub>Q\<close> \<open>A\<^sub>P \<sharp>* \<Psi>\<^sub>R\<close>
        by(auto intro: inputRenameSubject)
      moreover from \<open>A\<^sub>Q\<^sub>R \<sharp>* P\<close> \<open>A\<^sub>Q\<^sub>R \<sharp>* N\<close> Aeq have "A\<^sub>Q \<sharp>* P" and "A\<^sub>Q \<sharp>* N" by simp+
      ultimately have "\<Psi> \<otimes> \<Psi>\<^sub>R \<rhd> P \<parallel> Q \<longmapsto>K'\<lparr>N\<rparr> \<prec> P' \<parallel> Q" using \<open>extractFrame Q = \<langle>A\<^sub>Q, \<Psi>\<^sub>Q\<rangle>\<close> \<open>A\<^sub>Q \<sharp>* \<Psi>\<^sub>R\<close> \<open>A\<^sub>Q \<sharp>* K'\<close> \<open>A\<^sub>Q \<sharp>* \<Psi>\<close>
        by(intro Par1) (assumption | force)+
      moreover from FrP \<open>extractFrame Q = \<langle>A\<^sub>Q, \<Psi>\<^sub>Q\<rangle>\<close> \<open>A\<^sub>P \<sharp>* A\<^sub>Q\<close> \<open>A\<^sub>P \<sharp>* \<Psi>\<^sub>Q\<close> \<open>A\<^sub>Q \<sharp>* \<Psi>\<^sub>P\<close>
      have "extractFrame(P \<parallel> Q) = \<langle>(A\<^sub>P@A\<^sub>Q), \<Psi>\<^sub>P \<otimes> \<Psi>\<^sub>Q\<rangle>" by simp+
      moreover from RTrans have "\<Psi> \<otimes> (\<Psi>\<^sub>P \<otimes> \<Psi>\<^sub>Q) \<rhd> R \<longmapsto>K\<lparr>\<nu>*xvec\<rparr>\<langle>N\<rangle> \<prec> R'" by(metis Associativity statEqTransition)
      moreover note FrR
      moreover from MeqK' KeqK' have "\<Psi> \<otimes> (\<Psi>\<^sub>P \<otimes> \<Psi>\<^sub>Q) \<otimes> \<Psi>\<^sub>R \<turnstile> K' \<leftrightarrow> K"
        by(metis statEqEnt Associativity Commutativity Composition chanEqTrans chanEqSym)
      ultimately have "\<Psi> \<rhd> (P \<parallel> Q) \<parallel> R \<longmapsto>\<tau> \<prec> \<lparr>\<nu>*xvec\<rparr>((P' \<parallel> Q) \<parallel> R')"
        using \<open>A\<^sub>P \<sharp>* \<Psi>\<close> \<open>A\<^sub>Q \<sharp>* \<Psi>\<close> \<open>A\<^sub>P \<sharp>* P\<close> \<open>A\<^sub>Q \<sharp>* P\<close> \<open>A\<^sub>P \<sharp>* Q\<close> \<open>A\<^sub>Q \<sharp>* Q\<close> \<open>A\<^sub>P \<sharp>* R\<close> \<open>A\<^sub>Q \<sharp>* R\<close> \<open>A\<^sub>P \<sharp>* K'\<close> \<open>A\<^sub>Q \<sharp>* K'\<close> \<open>A\<^sub>P \<sharp>* A\<^sub>R\<close> \<open>A\<^sub>Q \<sharp>* A\<^sub>R\<close>
          \<open>A\<^sub>R \<sharp>* \<Psi>\<close> \<open>A\<^sub>R \<sharp>* P\<close> \<open>A\<^sub>R \<sharp>* Q\<close> \<open>A\<^sub>R \<sharp>* R\<close> \<open>A\<^sub>R \<sharp>* K\<close> \<open>xvec \<sharp>* P\<close> \<open>xvec \<sharp>* Q\<close>
        by(intro Comm1) (assumption | simp)+
      moreover from \<open>xvec \<sharp>* \<Psi>\<close> have "(\<Psi>, \<lparr>\<nu>*xvec\<rparr>((P' \<parallel> Q) \<parallel> R'), \<lparr>\<nu>*xvec\<rparr>(P' \<parallel> (Q \<parallel> R'))) \<in> Rel"
        by(metis C1 C4)
      ultimately show ?case by blast
    qed
  next
    case(cComm2 \<Psi>\<^sub>Q\<^sub>R M xvec N P' A\<^sub>P \<Psi>\<^sub>P K QR' A\<^sub>Q\<^sub>R)
    from \<open>A\<^sub>Q\<^sub>R \<sharp>* (\<Psi>, P, Q, R, \<alpha>)\<close> have "A\<^sub>Q\<^sub>R \<sharp>* Q" and "A\<^sub>Q\<^sub>R \<sharp>* R" and "A\<^sub>Q\<^sub>R \<sharp>* \<Psi>" by simp+
    from \<open>A\<^sub>P \<sharp>* (Q \<parallel> R)\<close> \<open>xvec \<sharp>* (Q \<parallel> R)\<close> have "A\<^sub>P \<sharp>* Q" and "A\<^sub>P \<sharp>* R" and "xvec \<sharp>* Q" and "xvec \<sharp>* R" by simp+
    have PTrans: "\<Psi> \<otimes> \<Psi>\<^sub>Q\<^sub>R \<rhd> P \<longmapsto>M\<lparr>\<nu>*xvec\<rparr>\<langle>N\<rangle> \<prec> P'" and FrP: "extractFrame P = \<langle>A\<^sub>P, \<Psi>\<^sub>P\<rangle>" and MeqK: "\<Psi> \<otimes> \<Psi>\<^sub>P \<otimes> \<Psi>\<^sub>Q\<^sub>R \<turnstile> M \<leftrightarrow> K" by fact+
    note \<open>\<Psi> \<otimes> \<Psi>\<^sub>P \<rhd> Q \<parallel> R \<longmapsto>K\<lparr>N\<rparr> \<prec> QR'\<close> \<open>extractFrame(Q \<parallel> R) = \<langle>A\<^sub>Q\<^sub>R, \<Psi>\<^sub>Q\<^sub>R\<rangle>\<close> \<open>distinct A\<^sub>Q\<^sub>R\<close>
    moreover from \<open>A\<^sub>Q\<^sub>R \<sharp>* \<Psi>\<close> \<open>A\<^sub>Q\<^sub>R \<sharp>* \<Psi>\<^sub>P\<close> have "A\<^sub>Q\<^sub>R \<sharp>* (\<Psi> \<otimes> \<Psi>\<^sub>P)" by force
    ultimately show ?case using \<open>A\<^sub>Q\<^sub>R \<sharp>* Q\<close> \<open>A\<^sub>Q\<^sub>R \<sharp>* R\<close> \<open>A\<^sub>Q\<^sub>R \<sharp>* K\<close>
    proof(induct rule: parCasesInputFrame)
      case(cPar1 Q' A\<^sub>Q \<Psi>\<^sub>Q A\<^sub>R \<Psi>\<^sub>R)
      have Aeq: "A\<^sub>Q\<^sub>R = A\<^sub>Q@A\<^sub>R" and \<Psi>eq: "\<Psi>\<^sub>Q\<^sub>R = \<Psi>\<^sub>Q \<otimes> \<Psi>\<^sub>R" by fact+
      from PTrans \<Psi>eq have "(\<Psi> \<otimes> \<Psi>\<^sub>R) \<otimes> \<Psi>\<^sub>Q \<rhd> P \<longmapsto>M\<lparr>\<nu>*xvec\<rparr>\<langle>N\<rangle> \<prec> P'"
        by(metis statEqTransition Associativity Commutativity Composition)
      moreover note FrP
      moreover from \<open>(\<Psi> \<otimes> \<Psi>\<^sub>P) \<otimes> \<Psi>\<^sub>R \<rhd> Q \<longmapsto>K\<lparr>N\<rparr> \<prec> Q'\<close> have "(\<Psi> \<otimes> \<Psi>\<^sub>R) \<otimes> \<Psi>\<^sub>P \<rhd> Q \<longmapsto>K\<lparr>N\<rparr> \<prec> Q'"
        by(metis statEqTransition Associativity Commutativity Composition)
      moreover note \<open>extractFrame Q = \<langle>A\<^sub>Q, \<Psi>\<^sub>Q\<rangle>\<close>
      moreover from MeqK \<Psi>eq have "(\<Psi> \<otimes> \<Psi>\<^sub>R) \<otimes> \<Psi>\<^sub>P \<otimes> \<Psi>\<^sub>Q \<turnstile> M \<leftrightarrow> K"
        by(metis statEqEnt Associativity Commutativity Composition)
      moreover from \<open>A\<^sub>P \<sharp>* Q\<close> \<open>A\<^sub>P \<sharp>* R\<close> \<open>A\<^sub>P \<sharp>* A\<^sub>Q\<^sub>R\<close> Aeq \<open>extractFrame Q = \<langle>A\<^sub>Q, \<Psi>\<^sub>Q\<rangle>\<close> \<open>extractFrame R = \<langle>A\<^sub>R, \<Psi>\<^sub>R\<rangle>\<close>
      have "A\<^sub>P \<sharp>* A\<^sub>Q" and "A\<^sub>P \<sharp>* \<Psi>\<^sub>R" by(auto dest: extractFrameFreshChain)
      moreover from \<open>A\<^sub>Q\<^sub>R \<sharp>* \<Psi>\<close>  \<open>A\<^sub>Q\<^sub>R \<sharp>* P\<close> Aeq have "A\<^sub>Q \<sharp>* \<Psi>" and "A\<^sub>Q \<sharp>* P" by simp+
      ultimately have "\<Psi> \<otimes> \<Psi>\<^sub>R \<rhd> P \<parallel> Q \<longmapsto>\<tau> \<prec> \<lparr>\<nu>*xvec\<rparr>(P' \<parallel> Q')"
        using \<open>A\<^sub>P \<sharp>* \<Psi>\<close> \<open>A\<^sub>P \<sharp>* P\<close> \<open>A\<^sub>P \<sharp>* Q\<close> \<open>A\<^sub>P \<sharp>* M\<close> \<open>A\<^sub>P \<sharp>* A\<^sub>Q\<close> \<open>A\<^sub>Q \<sharp>* \<Psi>\<close> \<open>A\<^sub>Q \<sharp>* \<Psi>\<^sub>R\<close> \<open>A\<^sub>Q \<sharp>* P\<close> \<open>A\<^sub>Q \<sharp>* Q\<close> \<open>A\<^sub>Q \<sharp>* K\<close> \<open>xvec \<sharp>* Q\<close>
        by(intro Comm2) (assumption | force)+
      moreover from \<open>A\<^sub>Q\<^sub>R \<sharp>* \<Psi>\<close> \<open>A\<^sub>Q\<^sub>R \<sharp>* P\<close> Aeq have "A\<^sub>R \<sharp>* \<Psi>" and "A\<^sub>R \<sharp>* P" by simp+
      ultimately have "\<Psi> \<rhd> (P \<parallel> Q) \<parallel> R \<longmapsto>\<tau> \<prec> (\<lparr>\<nu>*xvec\<rparr>(P' \<parallel> Q')) \<parallel> R" using \<open>extractFrame R = \<langle>A\<^sub>R, \<Psi>\<^sub>R\<rangle>\<close> \<open>A\<^sub>R \<sharp>* Q\<close>
        by(intro Par1) (assumption | simp)+
      moreover from \<open>xvec \<sharp>* \<Psi>\<close> \<open>xvec \<sharp>* R\<close> have "(\<Psi>, (\<lparr>\<nu>*xvec\<rparr>(P' \<parallel> Q')) \<parallel> R, \<lparr>\<nu>*xvec\<rparr>(P' \<parallel> (Q' \<parallel> R))) \<in> Rel"
        by(rule C3)
      ultimately show ?case by blast
    next
      case(cPar2 R' A\<^sub>Q \<Psi>\<^sub>Q A\<^sub>R \<Psi>\<^sub>R)
      have Aeq: "A\<^sub>Q\<^sub>R = A\<^sub>Q@A\<^sub>R" and \<Psi>eq: "\<Psi>\<^sub>Q\<^sub>R = \<Psi>\<^sub>Q \<otimes> \<Psi>\<^sub>R" by fact+
      from \<open>A\<^sub>Q\<^sub>R \<sharp>* \<Psi>\<close> \<open>A\<^sub>Q\<^sub>R \<sharp>* P\<close> \<open>A\<^sub>Q\<^sub>R \<sharp>* \<Psi>\<^sub>P\<close> \<open>A\<^sub>P \<sharp>* A\<^sub>Q\<^sub>R\<close> Aeq
      have "A\<^sub>R \<sharp>* \<Psi>" and "A\<^sub>R \<sharp>* \<Psi>\<^sub>P" and "A\<^sub>P \<sharp>* A\<^sub>R" and "A\<^sub>P \<sharp>* A\<^sub>Q" and "A\<^sub>R \<sharp>* P" and "A\<^sub>Q \<sharp>* \<Psi>" and "A\<^sub>Q \<sharp>* \<Psi>\<^sub>P" by simp+
      have RTrans: "(\<Psi> \<otimes> \<Psi>\<^sub>P) \<otimes> \<Psi>\<^sub>Q \<rhd> R \<longmapsto>K\<lparr>N\<rparr> \<prec> R'" and FrR: "extractFrame R = \<langle>A\<^sub>R, \<Psi>\<^sub>R\<rangle>" by fact+
      then obtain K' where KeqK': "((\<Psi> \<otimes> \<Psi>\<^sub>P) \<otimes> \<Psi>\<^sub>Q) \<otimes> \<Psi>\<^sub>R \<turnstile> K \<leftrightarrow> K'" and "A\<^sub>P \<sharp>* K'" and "A\<^sub>Q \<sharp>* K'"
        using \<open>A\<^sub>P \<sharp>* R\<close> \<open>A\<^sub>Q \<sharp>* R\<close> \<open>A\<^sub>R \<sharp>* \<Psi>\<close> \<open>A\<^sub>R \<sharp>* \<Psi>\<^sub>P\<close> \<open>A\<^sub>R \<sharp>* \<Psi>\<^sub>Q\<close> \<open>A\<^sub>Q \<sharp>* A\<^sub>R\<close> \<open>A\<^sub>P \<sharp>* A\<^sub>R\<close> \<open>A\<^sub>R \<sharp>* R\<close> \<open>A\<^sub>R \<sharp>* R\<close> \<open>A\<^sub>R \<sharp>* K\<close> \<open>distinct A\<^sub>R\<close>
        using inputObtainPrefix[where B="A\<^sub>P@A\<^sub>Q"]
        by (smt (verit, ccfv_threshold) freshChainAppend freshChainSym freshCompChain(1))
      from PTrans \<Psi>eq have "(\<Psi> \<otimes> \<Psi>\<^sub>R) \<otimes> \<Psi>\<^sub>Q \<rhd> P \<longmapsto>M\<lparr>\<nu>*xvec\<rparr>\<langle>N\<rangle> \<prec> P'"
        by(metis statEqTransition Associativity Commutativity Composition)
      moreover from MeqK KeqK' \<Psi>eq have MeqK': "((\<Psi> \<otimes> \<Psi>\<^sub>R) \<otimes> \<Psi>\<^sub>Q) \<otimes> \<Psi>\<^sub>P \<turnstile> M \<leftrightarrow> K'"
        by(metis statEqEnt Associativity Commutativity Composition chanEqTrans)
      moreover from \<open>A\<^sub>P \<sharp>* R\<close> \<open>A\<^sub>P \<sharp>* Q\<close> \<open>A\<^sub>P \<sharp>* A\<^sub>Q\<^sub>R\<close> FrR \<open>extractFrame Q = \<langle>A\<^sub>Q, \<Psi>\<^sub>Q\<rangle>\<close> Aeq have "A\<^sub>P \<sharp>* \<Psi>\<^sub>Q" and "A\<^sub>P \<sharp>* \<Psi>\<^sub>R"
        by(auto dest: extractFrameFreshChain)
      ultimately have "(\<Psi> \<otimes> \<Psi>\<^sub>R) \<otimes> \<Psi>\<^sub>Q \<rhd> P \<longmapsto>K'\<lparr>\<nu>*xvec\<rparr>\<langle>N\<rangle> \<prec> P'" using FrP \<open>distinct A\<^sub>P\<close> \<open>A\<^sub>P \<sharp>* \<Psi>\<close> \<open>A\<^sub>P \<sharp>* P\<close> \<open>A\<^sub>P \<sharp>* M\<close> \<open>A\<^sub>P \<sharp>* K'\<close>
        by(auto intro: outputRenameSubject)
      moreover from \<open>A\<^sub>Q\<^sub>R \<sharp>* P\<close> \<open>A\<^sub>Q\<^sub>R \<sharp>* N\<close> \<open>A\<^sub>Q\<^sub>R \<sharp>* xvec\<close> Aeq have "A\<^sub>Q \<sharp>* P" and "A\<^sub>Q \<sharp>* N" and "A\<^sub>Q \<sharp>* xvec" by simp+
      ultimately have "\<Psi> \<otimes> \<Psi>\<^sub>R \<rhd> P \<parallel> Q \<longmapsto>K'\<lparr>\<nu>*xvec\<rparr>\<langle>N\<rangle> \<prec> (P' \<parallel> Q)" using \<open>extractFrame Q = \<langle>A\<^sub>Q, \<Psi>\<^sub>Q\<rangle>\<close> \<open>A\<^sub>Q \<sharp>* \<Psi>\<^sub>R\<close> \<open>A\<^sub>Q \<sharp>* K'\<close> \<open>xvec \<sharp>* Q\<close> \<open>A\<^sub>Q \<sharp>* \<Psi>\<close>
        by(intro Par1) (assumption | force)+
      moreover from FrP \<open>extractFrame Q = \<langle>A\<^sub>Q, \<Psi>\<^sub>Q\<rangle>\<close> \<open>A\<^sub>P \<sharp>* A\<^sub>Q\<close> \<open>A\<^sub>P \<sharp>* \<Psi>\<^sub>Q\<close> \<open>A\<^sub>Q \<sharp>* \<Psi>\<^sub>P\<close>
      have "extractFrame(P \<parallel> Q) = \<langle>(A\<^sub>P@A\<^sub>Q), \<Psi>\<^sub>P \<otimes> \<Psi>\<^sub>Q\<rangle>" by simp+
      moreover from RTrans have "\<Psi> \<otimes> (\<Psi>\<^sub>P \<otimes> \<Psi>\<^sub>Q) \<rhd> R \<longmapsto>K\<lparr>N\<rparr> \<prec> R'" by(metis Associativity statEqTransition)
      moreover note FrR
      moreover from MeqK' KeqK' have "\<Psi> \<otimes> (\<Psi>\<^sub>P \<otimes> \<Psi>\<^sub>Q) \<otimes> \<Psi>\<^sub>R \<turnstile> K' \<leftrightarrow> K"
        by(metis statEqEnt Associativity Commutativity Composition chanEqTrans chanEqSym)
      ultimately have "\<Psi> \<rhd> (P \<parallel> Q) \<parallel> R \<longmapsto>\<tau> \<prec> \<lparr>\<nu>*xvec\<rparr>((P' \<parallel> Q) \<parallel> R')"
        using \<open>A\<^sub>P \<sharp>* \<Psi>\<close> \<open>A\<^sub>Q \<sharp>* \<Psi>\<close> \<open>A\<^sub>P \<sharp>* P\<close> \<open>A\<^sub>Q \<sharp>* P\<close> \<open>A\<^sub>P \<sharp>* Q\<close> \<open>A\<^sub>Q \<sharp>* Q\<close> \<open>A\<^sub>P \<sharp>* R\<close> \<open>A\<^sub>Q \<sharp>* R\<close> \<open>A\<^sub>P \<sharp>* K'\<close> \<open>A\<^sub>Q \<sharp>* K'\<close> \<open>A\<^sub>P \<sharp>* A\<^sub>R\<close> \<open>A\<^sub>Q \<sharp>* A\<^sub>R\<close>
          \<open>A\<^sub>R \<sharp>* \<Psi>\<close> \<open>A\<^sub>R \<sharp>* P\<close> \<open>A\<^sub>R \<sharp>* Q\<close> \<open>A\<^sub>R \<sharp>* R\<close> \<open>A\<^sub>R \<sharp>* K\<close> \<open>xvec \<sharp>* R\<close>
        by(intro Comm2) (assumption | simp)+
      moreover from \<open>xvec \<sharp>* \<Psi>\<close> have "(\<Psi>, \<lparr>\<nu>*xvec\<rparr>((P' \<parallel> Q) \<parallel> R'), \<lparr>\<nu>*xvec\<rparr>(P' \<parallel> (Q \<parallel> R'))) \<in> Rel"
        by(metis C1 C4)
      ultimately show ?case by blast
    qed
  next
    case(cBrMerge \<Psi>\<^sub>Q\<^sub>R M N P' A\<^sub>P \<Psi>\<^sub>P QR' A\<^sub>Q\<^sub>R)
    from \<open>A\<^sub>Q\<^sub>R \<sharp>* (\<Psi>, P, Q, R, \<alpha>)\<close> have "A\<^sub>Q\<^sub>R \<sharp>* Q" and "A\<^sub>Q\<^sub>R \<sharp>* R" and "A\<^sub>Q\<^sub>R \<sharp>* \<Psi>" by simp+
    from \<open>A\<^sub>P \<sharp>* (Q \<parallel> R)\<close> have "A\<^sub>P \<sharp>* Q" and "A\<^sub>P \<sharp>* R" by simp+
    have PTrans: "\<Psi> \<otimes> \<Psi>\<^sub>Q\<^sub>R \<rhd> P \<longmapsto>\<questiondown>M\<lparr>N\<rparr> \<prec> P'" and FrP: "extractFrame P = \<langle>A\<^sub>P, \<Psi>\<^sub>P\<rangle>" by fact+
    note \<open>\<Psi> \<otimes> \<Psi>\<^sub>P \<rhd> Q \<parallel> R \<longmapsto>\<questiondown>M\<lparr>N\<rparr> \<prec> QR'\<close> \<open>extractFrame(Q \<parallel> R) = \<langle>A\<^sub>Q\<^sub>R, \<Psi>\<^sub>Q\<^sub>R\<rangle>\<close> \<open>distinct A\<^sub>Q\<^sub>R\<close>
    moreover from \<open>A\<^sub>Q\<^sub>R \<sharp>* \<Psi>\<close> \<open>A\<^sub>Q\<^sub>R \<sharp>* \<Psi>\<^sub>P\<close> have "A\<^sub>Q\<^sub>R \<sharp>* (\<Psi> \<otimes> \<Psi>\<^sub>P)" by force
    ultimately show ?case using \<open>A\<^sub>Q\<^sub>R \<sharp>* Q\<close> \<open>A\<^sub>Q\<^sub>R \<sharp>* R\<close> \<open>A\<^sub>Q\<^sub>R \<sharp>* M\<close> \<open>A\<^sub>Q\<^sub>R \<sharp>* N\<close> \<open>A\<^sub>Q\<^sub>R \<sharp>* P\<close> \<open>A\<^sub>Q\<^sub>R \<sharp>* M\<close> \<open>A\<^sub>Q\<^sub>R \<sharp>* \<Psi>\<close>
    proof(induct rule: parCasesBrInputFrame)
      case(cPar1 Q' A\<^sub>Q \<Psi>\<^sub>Q A\<^sub>R \<Psi>\<^sub>R)
      from \<open>A\<^sub>Q\<^sub>R \<sharp>* N\<close> \<open>A\<^sub>Q\<^sub>R = A\<^sub>Q @ A\<^sub>R\<close> have "A\<^sub>Q \<sharp>* N" and "A\<^sub>R \<sharp>* N"
        by simp+
      have Aeq: "A\<^sub>Q\<^sub>R = A\<^sub>Q@A\<^sub>R" and \<Psi>eq: "\<Psi>\<^sub>Q\<^sub>R = \<Psi>\<^sub>Q \<otimes> \<Psi>\<^sub>R" by fact+
      from PTrans \<Psi>eq have "(\<Psi> \<otimes> \<Psi>\<^sub>R) \<otimes> \<Psi>\<^sub>Q \<rhd> P \<longmapsto>\<questiondown>M\<lparr>N\<rparr> \<prec> P'"
        by(metis statEqTransition Associativity Commutativity Composition)
      moreover note FrP
      moreover from \<open>(\<Psi> \<otimes> \<Psi>\<^sub>P) \<otimes> \<Psi>\<^sub>R \<rhd> Q \<longmapsto>\<questiondown>M\<lparr>N\<rparr> \<prec> Q'\<close> have "(\<Psi> \<otimes> \<Psi>\<^sub>R) \<otimes> \<Psi>\<^sub>P \<rhd> Q \<longmapsto>\<questiondown>M\<lparr>N\<rparr> \<prec> Q'"
        by(metis statEqTransition Associativity Commutativity Composition)
      moreover note \<open>extractFrame Q = \<langle>A\<^sub>Q, \<Psi>\<^sub>Q\<rangle>\<close>
      moreover from \<open>A\<^sub>P \<sharp>* Q\<close> \<open>A\<^sub>P \<sharp>* R\<close> \<open>A\<^sub>P \<sharp>* A\<^sub>Q\<^sub>R\<close> Aeq \<open>extractFrame Q = \<langle>A\<^sub>Q, \<Psi>\<^sub>Q\<rangle>\<close> \<open>extractFrame R = \<langle>A\<^sub>R, \<Psi>\<^sub>R\<rangle>\<close>
      have "A\<^sub>P \<sharp>* A\<^sub>Q" and "A\<^sub>P \<sharp>* \<Psi>\<^sub>R" by(auto dest: extractFrameFreshChain)
      moreover from \<open>A\<^sub>Q\<^sub>R \<sharp>* \<Psi>\<close>  \<open>A\<^sub>Q\<^sub>R \<sharp>* P\<close> Aeq have "A\<^sub>Q \<sharp>* \<Psi>" and "A\<^sub>Q \<sharp>* P" by simp+
      ultimately have "\<Psi> \<otimes> \<Psi>\<^sub>R \<rhd> P \<parallel> Q \<longmapsto>\<questiondown>M\<lparr>N\<rparr> \<prec> (P' \<parallel> Q')"
        using \<open>A\<^sub>P \<sharp>* \<Psi>\<close> \<open>A\<^sub>P \<sharp>* P\<close> \<open>A\<^sub>P \<sharp>* Q\<close> \<open>A\<^sub>P \<sharp>* M\<close> \<open>A\<^sub>P \<sharp>* A\<^sub>Q\<close> \<open>A\<^sub>Q \<sharp>* \<Psi>\<close> \<open>A\<^sub>Q \<sharp>* \<Psi>\<^sub>R\<close> \<open>A\<^sub>Q \<sharp>* P\<close> \<open>A\<^sub>Q \<sharp>* Q\<close> \<open>A\<^sub>Q \<sharp>* M\<close>
        by(intro BrMerge) (assumption | force)+
      moreover from \<open>A\<^sub>Q\<^sub>R \<sharp>* \<Psi>\<close> \<open>A\<^sub>Q\<^sub>R \<sharp>* P\<close> Aeq have "A\<^sub>R \<sharp>* \<Psi>" and "A\<^sub>R \<sharp>* P" by simp+
      ultimately have "\<Psi> \<rhd> (P \<parallel> Q) \<parallel> R \<longmapsto>\<questiondown>M\<lparr>N\<rparr> \<prec> (P' \<parallel> Q') \<parallel> R" using \<open>extractFrame R = \<langle>A\<^sub>R, \<Psi>\<^sub>R\<rangle>\<close> \<open>A\<^sub>R \<sharp>* Q\<close> \<open>A\<^sub>R \<sharp>* M\<close> \<open>A\<^sub>R \<sharp>* N\<close>
        by(intro Par1) (assumption | simp)+
      moreover have "(\<Psi>, (P' \<parallel> Q') \<parallel> R, (P' \<parallel> (Q' \<parallel> R))) \<in> Rel"
        by(rule C1)
      ultimately show ?case by blast
    next
      case(cPar2 R' A\<^sub>Q \<Psi>\<^sub>Q A\<^sub>R \<Psi>\<^sub>R)
      from \<open>A\<^sub>Q\<^sub>R \<sharp>* N\<close> \<open>A\<^sub>Q\<^sub>R = A\<^sub>Q @ A\<^sub>R\<close> have "A\<^sub>Q \<sharp>* N" and "A\<^sub>R \<sharp>* N"
        by simp+
      have Aeq: "A\<^sub>Q\<^sub>R = A\<^sub>Q@A\<^sub>R" and \<Psi>eq: "\<Psi>\<^sub>Q\<^sub>R = \<Psi>\<^sub>Q \<otimes> \<Psi>\<^sub>R" by fact+
      from \<open>A\<^sub>Q\<^sub>R \<sharp>* \<Psi>\<close> \<open>A\<^sub>Q\<^sub>R \<sharp>* P\<close> \<open>A\<^sub>Q\<^sub>R \<sharp>* \<Psi>\<^sub>P\<close> \<open>A\<^sub>P \<sharp>* A\<^sub>Q\<^sub>R\<close> Aeq
      have "A\<^sub>R \<sharp>* \<Psi>" and "A\<^sub>R \<sharp>* \<Psi>\<^sub>P" and "A\<^sub>P \<sharp>* A\<^sub>R" and "A\<^sub>P \<sharp>* A\<^sub>Q" and "A\<^sub>R \<sharp>* P" and "A\<^sub>Q \<sharp>* \<Psi>" and "A\<^sub>Q \<sharp>* \<Psi>\<^sub>P" by simp+
      have RTrans: "(\<Psi> \<otimes> \<Psi>\<^sub>P) \<otimes> \<Psi>\<^sub>Q \<rhd> R \<longmapsto>\<questiondown>M\<lparr>N\<rparr> \<prec> R'" and FrR: "extractFrame R = \<langle>A\<^sub>R, \<Psi>\<^sub>R\<rangle>" by fact+
      from PTrans \<Psi>eq have "(\<Psi> \<otimes> \<Psi>\<^sub>R) \<otimes> \<Psi>\<^sub>Q \<rhd> P \<longmapsto>\<questiondown>M\<lparr>N\<rparr> \<prec> P'"
        by(metis statEqTransition Associativity Commutativity Composition)
      moreover from \<open>A\<^sub>P \<sharp>* R\<close> \<open>A\<^sub>P \<sharp>* Q\<close> \<open>A\<^sub>P \<sharp>* A\<^sub>Q\<^sub>R\<close> FrR \<open>extractFrame Q = \<langle>A\<^sub>Q, \<Psi>\<^sub>Q\<rangle>\<close> Aeq have "A\<^sub>P \<sharp>* \<Psi>\<^sub>Q" and "A\<^sub>P \<sharp>* \<Psi>\<^sub>R"
        by(auto dest: extractFrameFreshChain)
      moreover from \<open>A\<^sub>Q\<^sub>R \<sharp>* P\<close> \<open>A\<^sub>Q\<^sub>R \<sharp>* N\<close> Aeq have "A\<^sub>Q \<sharp>* P" and "A\<^sub>Q \<sharp>* N" by simp+
      ultimately have "\<Psi> \<otimes> \<Psi>\<^sub>R \<rhd> P \<parallel> Q \<longmapsto>\<questiondown>M\<lparr>N\<rparr> \<prec> (P' \<parallel> Q)" using \<open>extractFrame Q = \<langle>A\<^sub>Q, \<Psi>\<^sub>Q\<rangle>\<close> \<open>A\<^sub>Q \<sharp>* \<Psi>\<^sub>R\<close> \<open>A\<^sub>Q \<sharp>* M\<close> \<open>A\<^sub>Q \<sharp>* \<Psi>\<close>
        by(intro Par1) (assumption | force)+
      moreover from FrP \<open>extractFrame Q = \<langle>A\<^sub>Q, \<Psi>\<^sub>Q\<rangle>\<close> \<open>A\<^sub>P \<sharp>* A\<^sub>Q\<close> \<open>A\<^sub>P \<sharp>* \<Psi>\<^sub>Q\<close> \<open>A\<^sub>Q \<sharp>* \<Psi>\<^sub>P\<close>
      have "extractFrame(P \<parallel> Q) = \<langle>(A\<^sub>P@A\<^sub>Q), \<Psi>\<^sub>P \<otimes> \<Psi>\<^sub>Q\<rangle>" by simp+
      moreover from RTrans have "\<Psi> \<otimes> (\<Psi>\<^sub>P \<otimes> \<Psi>\<^sub>Q) \<rhd> R \<longmapsto>\<questiondown>M\<lparr>N\<rparr> \<prec> R'" by(metis Associativity statEqTransition)
      moreover note FrR
      ultimately have "\<Psi> \<rhd> (P \<parallel> Q) \<parallel> R \<longmapsto>\<questiondown>M\<lparr>N\<rparr> \<prec> ((P' \<parallel> Q) \<parallel> R')"
        using \<open>A\<^sub>P \<sharp>* \<Psi>\<close> \<open>A\<^sub>Q \<sharp>* \<Psi>\<close> \<open>A\<^sub>P \<sharp>* P\<close> \<open>A\<^sub>Q \<sharp>* P\<close> \<open>A\<^sub>P \<sharp>* Q\<close> \<open>A\<^sub>Q \<sharp>* Q\<close> \<open>A\<^sub>P \<sharp>* R\<close> \<open>A\<^sub>Q \<sharp>* R\<close> \<open>A\<^sub>P \<sharp>* M\<close> \<open>A\<^sub>Q \<sharp>* M\<close> \<open>A\<^sub>P \<sharp>* A\<^sub>R\<close> \<open>A\<^sub>Q \<sharp>* A\<^sub>R\<close>
          \<open>A\<^sub>R \<sharp>* \<Psi>\<close> \<open>A\<^sub>R \<sharp>* P\<close> \<open>A\<^sub>R \<sharp>* Q\<close> \<open>A\<^sub>R \<sharp>* R\<close> \<open>A\<^sub>R \<sharp>* M\<close>
        by(auto intro: BrMerge)
      moreover have "(\<Psi>, ((P' \<parallel> Q) \<parallel> R'), (P' \<parallel> (Q \<parallel> R'))) \<in> Rel"
        by(rule C1)
      ultimately show ?case by blast
    next
      case(cBrMerge \<Psi>\<^sub>R Q' A\<^sub>Q \<Psi>\<^sub>Q R' A\<^sub>R)
      have Aeq: "A\<^sub>Q\<^sub>R = A\<^sub>Q@A\<^sub>R" and \<Psi>eq: "\<Psi>\<^sub>Q\<^sub>R = \<Psi>\<^sub>Q \<otimes> \<Psi>\<^sub>R" by fact+
      from \<open>A\<^sub>Q\<^sub>R \<sharp>* N\<close> \<open>A\<^sub>Q\<^sub>R \<sharp>* M\<close> \<open>A\<^sub>Q\<^sub>R \<sharp>* P\<close> \<open>A\<^sub>Q\<^sub>R \<sharp>* \<Psi>\<close> \<open>A\<^sub>Q\<^sub>R \<sharp>* \<Psi>\<^sub>P\<close> \<open>A\<^sub>P \<sharp>* A\<^sub>Q\<^sub>R\<close> Aeq \<Psi>eq
      have "A\<^sub>Q \<sharp>* N" and "A\<^sub>R \<sharp>* N" and "A\<^sub>Q \<sharp>* M" and "A\<^sub>R \<sharp>* M"
        and "A\<^sub>Q \<sharp>* \<Psi>" and "A\<^sub>R \<sharp>* \<Psi>" and "A\<^sub>P \<sharp>* A\<^sub>Q" and "A\<^sub>P \<sharp>* A\<^sub>R"
        and "A\<^sub>Q \<sharp>* \<Psi>\<^sub>P" and "A\<^sub>R \<sharp>* \<Psi>\<^sub>P"
        and "A\<^sub>Q \<sharp>* P" and "A\<^sub>R \<sharp>* P"
        by simp+

      from \<open>extractFrame Q = \<langle>A\<^sub>Q, \<Psi>\<^sub>Q\<rangle>\<close> \<open>A\<^sub>P \<sharp>* Q\<close> \<open>A\<^sub>P \<sharp>* A\<^sub>Q\<close>
      have "A\<^sub>P \<sharp>* \<Psi>\<^sub>Q"
        by (metis extractFrameFreshChain freshFrameDest)
      from Aeq \<Psi>eq PTrans have "\<Psi> \<otimes> (\<Psi>\<^sub>Q \<otimes> \<Psi>\<^sub>R) \<rhd> P \<longmapsto> \<questiondown>M\<lparr>N\<rparr> \<prec> P'" by simp
      then have "\<Psi> \<otimes> (\<Psi>\<^sub>R \<otimes> \<Psi>\<^sub>Q) \<rhd> P \<longmapsto> \<questiondown>M\<lparr>N\<rparr> \<prec> P'"
        by (metis Commutativity \<Psi>eq compositionSym statEqTransition)
      then have "(\<Psi> \<otimes> \<Psi>\<^sub>R) \<otimes> \<Psi>\<^sub>Q \<rhd> P \<longmapsto> \<questiondown>M\<lparr>N\<rparr> \<prec> P'"
        by (metis AssertionStatEqSym Associativity statEqTransition)
      moreover note FrP
      moreover from \<open>(\<Psi> \<otimes> \<Psi>\<^sub>P) \<otimes> \<Psi>\<^sub>R \<rhd> Q \<longmapsto>\<questiondown>M\<lparr>N\<rparr> \<prec> Q'\<close> have "(\<Psi> \<otimes> \<Psi>\<^sub>R) \<otimes> \<Psi>\<^sub>P \<rhd> Q \<longmapsto>\<questiondown>M\<lparr>N\<rparr> \<prec> Q'"
        by (metis associativitySym statEqTransition)
      moreover note \<open>extractFrame Q = \<langle>A\<^sub>Q, \<Psi>\<^sub>Q\<rangle>\<close>
      moreover note \<open>A\<^sub>P \<sharp>* \<Psi>\<close> \<open>A\<^sub>Q \<sharp>* \<Psi>\<close> \<open>A\<^sub>Q \<sharp>* \<Psi>\<^sub>R\<close>
      moreover from \<open>extractFrame R = \<langle>A\<^sub>R, \<Psi>\<^sub>R\<rangle>\<close> \<open>A\<^sub>P \<sharp>* A\<^sub>R\<close> \<open>A\<^sub>P \<sharp>* R\<close> have "A\<^sub>P \<sharp>* \<Psi>\<^sub>R"
        by (metis extractFrameFreshChain freshFrameDest)
      moreover note \<open>A\<^sub>P \<sharp>* P\<close> \<open>A\<^sub>P \<sharp>* Q\<close> \<open>A\<^sub>P \<sharp>* M\<close> \<open>A\<^sub>P \<sharp>* A\<^sub>Q\<close> \<open>A\<^sub>Q \<sharp>* P\<close> \<open>A\<^sub>Q \<sharp>* Q\<close> \<open>A\<^sub>Q \<sharp>* M\<close>
      ultimately have "(\<Psi> \<otimes> \<Psi>\<^sub>R) \<rhd> (P \<parallel> Q) \<longmapsto>\<questiondown>M\<lparr>N\<rparr> \<prec> (P' \<parallel> Q')"
        by(intro BrMerge) (assumption | force)+

      from \<open>(\<Psi> \<otimes> \<Psi>\<^sub>P) \<otimes> \<Psi>\<^sub>Q \<rhd> R \<longmapsto>\<questiondown>M\<lparr>N\<rparr> \<prec> R'\<close> have "\<Psi> \<otimes> (\<Psi>\<^sub>P \<otimes> \<Psi>\<^sub>Q) \<rhd> R \<longmapsto>\<questiondown>M\<lparr>N\<rparr> \<prec> R'"
        by (metis Associativity statEqTransition)

      note \<open>(\<Psi> \<otimes> \<Psi>\<^sub>R) \<rhd> (P \<parallel> Q) \<longmapsto>\<questiondown>M\<lparr>N\<rparr> \<prec> (P' \<parallel> Q')\<close>
      moreover from FrP \<open>extractFrame Q = \<langle>A\<^sub>Q, \<Psi>\<^sub>Q\<rangle>\<close> \<open>A\<^sub>P \<sharp>* A\<^sub>Q\<close> \<open>A\<^sub>P \<sharp>* \<Psi>\<^sub>Q\<close> \<open>A\<^sub>Q \<sharp>* \<Psi>\<^sub>P\<close>
      have "extractFrame(P \<parallel> Q) = \<langle>(A\<^sub>P@A\<^sub>Q), (\<Psi>\<^sub>P \<otimes> \<Psi>\<^sub>Q)\<rangle>" by simp
      moreover note \<open>\<Psi> \<otimes> (\<Psi>\<^sub>P \<otimes> \<Psi>\<^sub>Q) \<rhd> R \<longmapsto>\<questiondown>M\<lparr>N\<rparr> \<prec> R'\<close> \<open>extractFrame R = \<langle>A\<^sub>R, \<Psi>\<^sub>R\<rangle>\<close>
      moreover note \<open>A\<^sub>P \<sharp>* \<Psi>\<close> \<open>A\<^sub>Q \<sharp>* \<Psi>\<close> \<open>A\<^sub>R \<sharp>* \<Psi>\<close> \<open>A\<^sub>P \<sharp>* P\<close> \<open>A\<^sub>Q \<sharp>* P\<close> \<open>A\<^sub>P \<sharp>* Q\<close> \<open>A\<^sub>Q \<sharp>* Q\<close>
        \<open>A\<^sub>P \<sharp>* R\<close> \<open>A\<^sub>Q \<sharp>* R\<close> \<open>A\<^sub>P \<sharp>* M\<close> \<open>A\<^sub>Q \<sharp>* M\<close> \<open>A\<^sub>P \<sharp>* A\<^sub>R\<close> \<open>A\<^sub>Q \<sharp>* A\<^sub>R\<close> \<open>A\<^sub>R \<sharp>* P\<close> \<open>A\<^sub>R \<sharp>* Q\<close> \<open>A\<^sub>R \<sharp>* R\<close> \<open>A\<^sub>R \<sharp>* M\<close>
      ultimately have "\<Psi> \<rhd> (P \<parallel> Q) \<parallel> R \<longmapsto>\<questiondown>M\<lparr>N\<rparr> \<prec> (P' \<parallel> Q') \<parallel> R'"
        by(auto intro: BrMerge)
      moreover have "(\<Psi>, (P' \<parallel> Q') \<parallel> R', (P' \<parallel> (Q' \<parallel> R'))) \<in> Rel"
        by(rule C1)
      ultimately show ?case by blast
    qed
  next
    case(cBrComm1 \<Psi>\<^sub>Q\<^sub>R M N P' A\<^sub>P \<Psi>\<^sub>P xvec QR' A\<^sub>Q\<^sub>R)
    from \<open>\<exclamdown>M\<lparr>\<nu>*xvec\<rparr>\<langle>N\<rangle> = \<alpha>\<close> \<open>bn \<alpha> \<sharp>* Q\<close> \<open>bn \<alpha> \<sharp>* R\<close> have "xvec \<sharp>* Q" and "xvec \<sharp>* R" by auto
    from \<open>A\<^sub>Q\<^sub>R \<sharp>* (\<Psi>, P, Q, R, \<alpha>)\<close> have "A\<^sub>Q\<^sub>R \<sharp>* Q" and "A\<^sub>Q\<^sub>R \<sharp>* R" and "A\<^sub>Q\<^sub>R \<sharp>* \<Psi>" by simp+
    from \<open>A\<^sub>P \<sharp>* (Q \<parallel> R)\<close> have "A\<^sub>P \<sharp>* Q" and "A\<^sub>P \<sharp>* R" by simp+
    have PTrans: "\<Psi> \<otimes> \<Psi>\<^sub>Q\<^sub>R \<rhd> P \<longmapsto>\<questiondown>M\<lparr>N\<rparr> \<prec> P'" and FrP: "extractFrame P = \<langle>A\<^sub>P, \<Psi>\<^sub>P\<rangle>" by fact+
    note \<open>\<Psi> \<otimes> \<Psi>\<^sub>P \<rhd> Q \<parallel> R \<longmapsto>\<exclamdown>M\<lparr>\<nu>*xvec\<rparr>\<langle>N\<rangle> \<prec> QR'\<close>
    moreover from \<open>xvec \<sharp>* \<Psi>\<close> \<open>xvec \<sharp>* \<Psi>\<^sub>P\<close> have "xvec \<sharp>* (\<Psi> \<otimes> \<Psi>\<^sub>P)" by force
    moreover note \<open>xvec \<sharp>* Q\<close> \<open>xvec \<sharp>* R\<close> \<open>xvec \<sharp>* M\<close>
      \<open>extractFrame(Q \<parallel> R) = \<langle>A\<^sub>Q\<^sub>R, \<Psi>\<^sub>Q\<^sub>R\<rangle>\<close> \<open>distinct A\<^sub>Q\<^sub>R\<close>
    moreover from \<open>A\<^sub>Q\<^sub>R \<sharp>* \<Psi>\<close> \<open>A\<^sub>Q\<^sub>R \<sharp>* \<Psi>\<^sub>P\<close> have "A\<^sub>Q\<^sub>R \<sharp>* (\<Psi> \<otimes> \<Psi>\<^sub>P)" by force
    ultimately show ?case using \<open>A\<^sub>Q\<^sub>R \<sharp>* Q\<close> \<open>A\<^sub>Q\<^sub>R \<sharp>* R\<close> \<open>A\<^sub>Q\<^sub>R \<sharp>* M\<close>
    proof(induct rule: parCasesBrOutputFrame)
      case(cPar1 Q' A\<^sub>Q \<Psi>\<^sub>Q A\<^sub>R \<Psi>\<^sub>R)
      from \<open>A\<^sub>Q\<^sub>R \<sharp>* N\<close> \<open>A\<^sub>Q\<^sub>R = A\<^sub>Q @ A\<^sub>R\<close> have "A\<^sub>Q \<sharp>* N" and "A\<^sub>R \<sharp>* N"
        by simp+
      from \<open>A\<^sub>Q\<^sub>R \<sharp>* xvec\<close> \<open>A\<^sub>Q\<^sub>R = (A\<^sub>Q@A\<^sub>R)\<close> have "A\<^sub>Q \<sharp>* xvec" and "A\<^sub>R \<sharp>* xvec"
        by simp+
      have Aeq: "A\<^sub>Q\<^sub>R = A\<^sub>Q@A\<^sub>R" and \<Psi>eq: "\<Psi>\<^sub>Q\<^sub>R = \<Psi>\<^sub>Q \<otimes> \<Psi>\<^sub>R" by fact+
      from PTrans \<Psi>eq have "(\<Psi> \<otimes> \<Psi>\<^sub>R) \<otimes> \<Psi>\<^sub>Q \<rhd> P \<longmapsto>\<questiondown>M\<lparr>N\<rparr> \<prec> P'"
        by(metis statEqTransition Associativity Commutativity Composition)
      moreover note FrP
      moreover from \<open>(\<Psi> \<otimes> \<Psi>\<^sub>P) \<otimes> \<Psi>\<^sub>R \<rhd> Q \<longmapsto>\<exclamdown>M\<lparr>\<nu>*xvec\<rparr>\<langle>N\<rangle> \<prec> Q'\<close> have "(\<Psi> \<otimes> \<Psi>\<^sub>R) \<otimes> \<Psi>\<^sub>P \<rhd> Q \<longmapsto>\<exclamdown>M\<lparr>\<nu>*xvec\<rparr>\<langle>N\<rangle> \<prec> Q'"
        by(metis statEqTransition Associativity Commutativity Composition)
      moreover note \<open>extractFrame Q = \<langle>A\<^sub>Q, \<Psi>\<^sub>Q\<rangle>\<close>
      moreover from \<open>A\<^sub>P \<sharp>* Q\<close> \<open>A\<^sub>P \<sharp>* R\<close> \<open>A\<^sub>P \<sharp>* A\<^sub>Q\<^sub>R\<close> Aeq \<open>extractFrame Q = \<langle>A\<^sub>Q, \<Psi>\<^sub>Q\<rangle>\<close> \<open>extractFrame R = \<langle>A\<^sub>R, \<Psi>\<^sub>R\<rangle>\<close>
      have "A\<^sub>P \<sharp>* A\<^sub>Q" and "A\<^sub>P \<sharp>* \<Psi>\<^sub>R" by(auto dest: extractFrameFreshChain)
      moreover from \<open>A\<^sub>Q\<^sub>R \<sharp>* \<Psi>\<close>  \<open>A\<^sub>Q\<^sub>R \<sharp>* P\<close> Aeq have "A\<^sub>Q \<sharp>* \<Psi>" and "A\<^sub>Q \<sharp>* P" by simp+
      ultimately have "\<Psi> \<otimes> \<Psi>\<^sub>R \<rhd> P \<parallel> Q \<longmapsto>\<exclamdown>M\<lparr>\<nu>*xvec\<rparr>\<langle>N\<rangle> \<prec> (P' \<parallel> Q')"
        using \<open>A\<^sub>P \<sharp>* \<Psi>\<close> \<open>A\<^sub>P \<sharp>* P\<close> \<open>A\<^sub>P \<sharp>* Q\<close> \<open>A\<^sub>P \<sharp>* M\<close> \<open>A\<^sub>P \<sharp>* A\<^sub>Q\<close> \<open>A\<^sub>Q \<sharp>* \<Psi>\<close> \<open>A\<^sub>Q \<sharp>* \<Psi>\<^sub>R\<close> \<open>A\<^sub>Q \<sharp>* P\<close> \<open>A\<^sub>Q \<sharp>* Q\<close> \<open>A\<^sub>Q \<sharp>* M\<close> \<open>xvec \<sharp>* P\<close>
        by(intro BrComm1) (assumption | force)+
      moreover from \<open>A\<^sub>Q\<^sub>R \<sharp>* \<Psi>\<close> \<open>A\<^sub>Q\<^sub>R \<sharp>* P\<close> Aeq have "A\<^sub>R \<sharp>* \<Psi>" and "A\<^sub>R \<sharp>* P" by simp+
      ultimately have "\<Psi> \<rhd> (P \<parallel> Q) \<parallel> R \<longmapsto>\<exclamdown>M\<lparr>\<nu>*xvec\<rparr>\<langle>N\<rangle> \<prec> (P' \<parallel> Q') \<parallel> R" using \<open>extractFrame R = \<langle>A\<^sub>R, \<Psi>\<^sub>R\<rangle>\<close> \<open>A\<^sub>R \<sharp>* Q\<close> \<open>A\<^sub>R \<sharp>* M\<close> \<open>A\<^sub>R \<sharp>* N\<close> \<open>xvec \<sharp>* R\<close> \<open>A\<^sub>R \<sharp>* xvec\<close>
        by(intro Par1) (assumption | simp)+
      moreover have "(\<Psi>, (P' \<parallel> Q') \<parallel> R, (P' \<parallel> (Q' \<parallel> R))) \<in> Rel"
        by(rule C1)
      ultimately show ?case by blast
    next
      case(cPar2 R' A\<^sub>Q \<Psi>\<^sub>Q A\<^sub>R \<Psi>\<^sub>R)
      from \<open>A\<^sub>Q\<^sub>R \<sharp>* N\<close> \<open>A\<^sub>Q\<^sub>R = A\<^sub>Q @ A\<^sub>R\<close> have "A\<^sub>Q \<sharp>* N" and "A\<^sub>R \<sharp>* N"
        by simp+
      have Aeq: "A\<^sub>Q\<^sub>R = A\<^sub>Q@A\<^sub>R" and \<Psi>eq: "\<Psi>\<^sub>Q\<^sub>R = \<Psi>\<^sub>Q \<otimes> \<Psi>\<^sub>R" by fact+
      from \<open>A\<^sub>Q\<^sub>R \<sharp>* \<Psi>\<close> \<open>A\<^sub>Q\<^sub>R \<sharp>* P\<close> \<open>A\<^sub>Q\<^sub>R \<sharp>* \<Psi>\<^sub>P\<close> \<open>A\<^sub>P \<sharp>* A\<^sub>Q\<^sub>R\<close> Aeq
      have "A\<^sub>R \<sharp>* \<Psi>" and "A\<^sub>R \<sharp>* \<Psi>\<^sub>P" and "A\<^sub>P \<sharp>* A\<^sub>R" and "A\<^sub>P \<sharp>* A\<^sub>Q" and "A\<^sub>R \<sharp>* P" and "A\<^sub>Q \<sharp>* \<Psi>" and "A\<^sub>Q \<sharp>* \<Psi>\<^sub>P" by simp+
      have RTrans: "(\<Psi> \<otimes> \<Psi>\<^sub>P) \<otimes> \<Psi>\<^sub>Q \<rhd> R \<longmapsto>\<exclamdown>M\<lparr>\<nu>*xvec\<rparr>\<langle>N\<rangle> \<prec> R'" and FrR: "extractFrame R = \<langle>A\<^sub>R, \<Psi>\<^sub>R\<rangle>" by fact+
      from PTrans \<Psi>eq have "(\<Psi> \<otimes> \<Psi>\<^sub>R) \<otimes> \<Psi>\<^sub>Q \<rhd> P \<longmapsto>\<questiondown>M\<lparr>N\<rparr> \<prec> P'"
        by(metis statEqTransition Associativity Commutativity Composition)
      moreover from \<open>A\<^sub>P \<sharp>* R\<close> \<open>A\<^sub>P \<sharp>* Q\<close> \<open>A\<^sub>P \<sharp>* A\<^sub>Q\<^sub>R\<close> FrR \<open>extractFrame Q = \<langle>A\<^sub>Q, \<Psi>\<^sub>Q\<rangle>\<close> Aeq have "A\<^sub>P \<sharp>* \<Psi>\<^sub>Q" and "A\<^sub>P \<sharp>* \<Psi>\<^sub>R"
        by(auto dest: extractFrameFreshChain)
      moreover from \<open>A\<^sub>Q\<^sub>R \<sharp>* P\<close> \<open>A\<^sub>Q\<^sub>R \<sharp>* N\<close> Aeq have "A\<^sub>Q \<sharp>* P" and "A\<^sub>Q \<sharp>* N" by simp+
      ultimately have "\<Psi> \<otimes> \<Psi>\<^sub>R \<rhd> P \<parallel> Q \<longmapsto>\<questiondown>M\<lparr>N\<rparr> \<prec> (P' \<parallel> Q)" using \<open>extractFrame Q = \<langle>A\<^sub>Q, \<Psi>\<^sub>Q\<rangle>\<close> \<open>A\<^sub>Q \<sharp>* \<Psi>\<^sub>R\<close> \<open>A\<^sub>Q \<sharp>* M\<close> \<open>A\<^sub>Q \<sharp>* \<Psi>\<close>
        by(intro Par1) (assumption | force)+
      moreover from FrP \<open>extractFrame Q = \<langle>A\<^sub>Q, \<Psi>\<^sub>Q\<rangle>\<close> \<open>A\<^sub>P \<sharp>* A\<^sub>Q\<close> \<open>A\<^sub>P \<sharp>* \<Psi>\<^sub>Q\<close> \<open>A\<^sub>Q \<sharp>* \<Psi>\<^sub>P\<close>
      have "extractFrame(P \<parallel> Q) = \<langle>(A\<^sub>P@A\<^sub>Q), \<Psi>\<^sub>P \<otimes> \<Psi>\<^sub>Q\<rangle>" by simp+
      moreover from RTrans have "\<Psi> \<otimes> (\<Psi>\<^sub>P \<otimes> \<Psi>\<^sub>Q) \<rhd> R \<longmapsto>\<exclamdown>M\<lparr>\<nu>*xvec\<rparr>\<langle>N\<rangle> \<prec> R'" by(metis Associativity statEqTransition)
      moreover note FrR
      ultimately have "\<Psi> \<rhd> (P \<parallel> Q) \<parallel> R \<longmapsto>\<exclamdown>M\<lparr>\<nu>*xvec\<rparr>\<langle>N\<rangle> \<prec> ((P' \<parallel> Q) \<parallel> R')"
        using \<open>A\<^sub>P \<sharp>* \<Psi>\<close> \<open>A\<^sub>Q \<sharp>* \<Psi>\<close> \<open>A\<^sub>P \<sharp>* P\<close> \<open>A\<^sub>Q \<sharp>* P\<close> \<open>A\<^sub>P \<sharp>* Q\<close> \<open>A\<^sub>Q \<sharp>* Q\<close> \<open>A\<^sub>P \<sharp>* R\<close> \<open>A\<^sub>Q \<sharp>* R\<close> \<open>A\<^sub>P \<sharp>* M\<close> \<open>A\<^sub>Q \<sharp>* M\<close> \<open>A\<^sub>P \<sharp>* A\<^sub>R\<close> \<open>A\<^sub>Q \<sharp>* A\<^sub>R\<close>
          \<open>A\<^sub>R \<sharp>* \<Psi>\<close> \<open>A\<^sub>R \<sharp>* P\<close> \<open>A\<^sub>R \<sharp>* Q\<close> \<open>A\<^sub>R \<sharp>* R\<close> \<open>A\<^sub>R \<sharp>* M\<close> \<open>xvec \<sharp>* P\<close> \<open>xvec \<sharp>* Q\<close>
        by(intro BrComm1) (assumption | simp)+
      moreover have "(\<Psi>, ((P' \<parallel> Q) \<parallel> R'), (P' \<parallel> (Q \<parallel> R'))) \<in> Rel"
        by(rule C1)
      ultimately show ?case by blast
    next
      case(cBrComm1 \<Psi>\<^sub>R Q' A\<^sub>Q \<Psi>\<^sub>Q R' A\<^sub>R)
      from \<open>A\<^sub>Q\<^sub>R \<sharp>* N\<close> \<open>A\<^sub>Q\<^sub>R = A\<^sub>Q @ A\<^sub>R\<close> have "A\<^sub>Q \<sharp>* N" and "A\<^sub>R \<sharp>* N"
        by simp+
      from \<open>A\<^sub>Q\<^sub>R \<sharp>* xvec\<close> \<open>A\<^sub>Q\<^sub>R = (A\<^sub>Q@A\<^sub>R)\<close> have "A\<^sub>Q \<sharp>* xvec" and "A\<^sub>R \<sharp>* xvec"
        by simp+
      have Aeq: "A\<^sub>Q\<^sub>R = A\<^sub>Q@A\<^sub>R" and \<Psi>eq: "\<Psi>\<^sub>Q\<^sub>R = \<Psi>\<^sub>Q \<otimes> \<Psi>\<^sub>R" by fact+
      from Aeq \<open>A\<^sub>Q\<^sub>R \<sharp>* P\<close> have "A\<^sub>Q \<sharp>* P" and "A\<^sub>R \<sharp>* P" by simp+
      from Aeq \<open>A\<^sub>Q\<^sub>R \<sharp>* \<Psi>\<close> have "A\<^sub>Q \<sharp>* \<Psi>" and "A\<^sub>R \<sharp>* \<Psi>" by simp+
      from Aeq \<open>A\<^sub>P \<sharp>* A\<^sub>Q\<^sub>R\<close> have "A\<^sub>P \<sharp>* A\<^sub>Q" and "A\<^sub>P \<sharp>* A\<^sub>R" by simp+
      with \<open>A\<^sub>P \<sharp>* Q\<close> \<open>extractFrame Q = \<langle>A\<^sub>Q, \<Psi>\<^sub>Q\<rangle>\<close> have "A\<^sub>P \<sharp>* \<Psi>\<^sub>Q"
        by (metis extractFrameFreshChain freshChainSym freshFrameDest)
      from PTrans \<Psi>eq have "(\<Psi> \<otimes> \<Psi>\<^sub>R) \<otimes> \<Psi>\<^sub>Q \<rhd> P \<longmapsto>\<questiondown>M\<lparr>N\<rparr> \<prec> P'"
        by(metis statEqTransition Associativity Commutativity Composition)
      moreover note FrP
      moreover from \<open>(\<Psi> \<otimes> \<Psi>\<^sub>P) \<otimes> \<Psi>\<^sub>R \<rhd> Q \<longmapsto>\<questiondown>M\<lparr>N\<rparr> \<prec> Q'\<close> have "(\<Psi> \<otimes> \<Psi>\<^sub>R) \<otimes> \<Psi>\<^sub>P \<rhd> Q \<longmapsto>\<questiondown>M\<lparr>N\<rparr> \<prec> Q'"
        by(metis statEqTransition Associativity Commutativity Composition)
      moreover note \<open>extractFrame Q = \<langle>A\<^sub>Q, \<Psi>\<^sub>Q\<rangle>\<close>
      moreover from \<open>A\<^sub>P \<sharp>* Q\<close> \<open>A\<^sub>P \<sharp>* R\<close> \<open>A\<^sub>P \<sharp>* A\<^sub>Q\<^sub>R\<close> Aeq \<open>extractFrame Q = \<langle>A\<^sub>Q, \<Psi>\<^sub>Q\<rangle>\<close> \<open>extractFrame R = \<langle>A\<^sub>R, \<Psi>\<^sub>R\<rangle>\<close>
      have "A\<^sub>P \<sharp>* A\<^sub>Q" and "A\<^sub>P \<sharp>* \<Psi>\<^sub>R" by(auto dest: extractFrameFreshChain)
      moreover from \<open>A\<^sub>Q\<^sub>R \<sharp>* \<Psi>\<close>  \<open>A\<^sub>Q\<^sub>R \<sharp>* P\<close> Aeq have "A\<^sub>Q \<sharp>* \<Psi>" and "A\<^sub>Q \<sharp>* P" by simp+
      ultimately have PQTrans: "\<Psi> \<otimes> \<Psi>\<^sub>R \<rhd> P \<parallel> Q \<longmapsto>\<questiondown>M\<lparr>N\<rparr> \<prec> (P' \<parallel> Q')"
        using \<open>A\<^sub>P \<sharp>* \<Psi>\<close> \<open>A\<^sub>P \<sharp>* P\<close> \<open>A\<^sub>P \<sharp>* Q\<close> \<open>A\<^sub>P \<sharp>* M\<close> \<open>A\<^sub>P \<sharp>* A\<^sub>Q\<close> \<open>A\<^sub>Q \<sharp>* \<Psi>\<close> \<open>A\<^sub>Q \<sharp>* \<Psi>\<^sub>R\<close> \<open>A\<^sub>Q \<sharp>* P\<close> \<open>A\<^sub>Q \<sharp>* Q\<close> \<open>A\<^sub>Q \<sharp>* M\<close>
        by(intro BrMerge) (assumption | force)+
      have RTrans: "(\<Psi> \<otimes> \<Psi>\<^sub>P) \<otimes> \<Psi>\<^sub>Q \<rhd> R \<longmapsto>\<exclamdown>M\<lparr>\<nu>*xvec\<rparr>\<langle>N\<rangle> \<prec> R'" and FrR: "extractFrame R = \<langle>A\<^sub>R, \<Psi>\<^sub>R\<rangle>" by fact+
      note PQTrans
      moreover from FrP \<open>extractFrame Q = \<langle>A\<^sub>Q, \<Psi>\<^sub>Q\<rangle>\<close> \<open>A\<^sub>P \<sharp>* A\<^sub>Q\<close> \<open>A\<^sub>P \<sharp>* \<Psi>\<^sub>Q\<close> \<open>A\<^sub>Q\<^sub>R \<sharp>* \<Psi>\<^sub>P\<close> Aeq
      have "extractFrame(P \<parallel> Q) = \<langle>(A\<^sub>P@A\<^sub>Q), \<Psi>\<^sub>P \<otimes> \<Psi>\<^sub>Q\<rangle>" by simp+
      moreover from RTrans have "\<Psi> \<otimes> (\<Psi>\<^sub>P \<otimes> \<Psi>\<^sub>Q) \<rhd> R \<longmapsto>\<exclamdown>M\<lparr>\<nu>*xvec\<rparr>\<langle>N\<rangle> \<prec> R'"
        by (metis Associativity statEqTransition)
      moreover note FrR
      moreover note \<open>A\<^sub>P \<sharp>* \<Psi>\<close> \<open>A\<^sub>Q \<sharp>* \<Psi>\<close> \<open>A\<^sub>P \<sharp>* P\<close> \<open>A\<^sub>P \<sharp>* Q\<close> \<open>A\<^sub>Q \<sharp>* P\<close> \<open>A\<^sub>Q \<sharp>* Q\<close> \<open>A\<^sub>P \<sharp>* R\<close> \<open>A\<^sub>Q \<sharp>* R\<close>
        \<open>A\<^sub>P \<sharp>* M\<close> \<open>A\<^sub>Q \<sharp>* M\<close> \<open>A\<^sub>P \<sharp>* A\<^sub>R\<close> \<open>A\<^sub>Q \<sharp>* A\<^sub>R\<close> \<open>A\<^sub>R \<sharp>* \<Psi>\<close> \<open>A\<^sub>R \<sharp>* P\<close> \<open>A\<^sub>R \<sharp>* Q\<close> \<open>A\<^sub>R \<sharp>* R\<close> \<open>A\<^sub>R \<sharp>* M\<close> \<open>xvec \<sharp>* P\<close> \<open>xvec \<sharp>* Q\<close>
      ultimately have "\<Psi> \<rhd> (P \<parallel> Q) \<parallel> R \<longmapsto>\<exclamdown>M\<lparr>\<nu>*xvec\<rparr>\<langle>N\<rangle> \<prec> (P' \<parallel> Q') \<parallel> R'"
        by(intro BrComm1) (assumption | force)+
      moreover have "(\<Psi>, (P' \<parallel> Q') \<parallel> R', (P' \<parallel> (Q' \<parallel> R'))) \<in> Rel"
        by(rule C1)
      ultimately show ?case by blast
    next
      case(cBrComm2 \<Psi>\<^sub>R Q' A\<^sub>Q \<Psi>\<^sub>Q R' A\<^sub>R)
      from \<open>A\<^sub>Q\<^sub>R \<sharp>* N\<close> \<open>A\<^sub>Q\<^sub>R = A\<^sub>Q @ A\<^sub>R\<close> have "A\<^sub>Q \<sharp>* N" and "A\<^sub>R \<sharp>* N"
        by simp+
      from \<open>A\<^sub>Q\<^sub>R \<sharp>* xvec\<close> \<open>A\<^sub>Q\<^sub>R = (A\<^sub>Q@A\<^sub>R)\<close> have "A\<^sub>Q \<sharp>* xvec" and "A\<^sub>R \<sharp>* xvec"
        by simp+
      have Aeq: "A\<^sub>Q\<^sub>R = A\<^sub>Q@A\<^sub>R" and \<Psi>eq: "\<Psi>\<^sub>Q\<^sub>R = \<Psi>\<^sub>Q \<otimes> \<Psi>\<^sub>R" by fact+
      from Aeq \<open>A\<^sub>Q\<^sub>R \<sharp>* P\<close> have "A\<^sub>Q \<sharp>* P" and "A\<^sub>R \<sharp>* P" by simp+
      from Aeq \<open>A\<^sub>Q\<^sub>R \<sharp>* \<Psi>\<close> have "A\<^sub>Q \<sharp>* \<Psi>" and "A\<^sub>R \<sharp>* \<Psi>" by simp+
      from Aeq \<open>A\<^sub>P \<sharp>* A\<^sub>Q\<^sub>R\<close> have "A\<^sub>P \<sharp>* A\<^sub>Q" and "A\<^sub>P \<sharp>* A\<^sub>R" by simp+
      with \<open>A\<^sub>P \<sharp>* Q\<close> \<open>extractFrame Q = \<langle>A\<^sub>Q, \<Psi>\<^sub>Q\<rangle>\<close> have "A\<^sub>P \<sharp>* \<Psi>\<^sub>Q"
        by (metis extractFrameFreshChain freshChainSym freshFrameDest)
      from PTrans \<Psi>eq have "(\<Psi> \<otimes> \<Psi>\<^sub>R) \<otimes> \<Psi>\<^sub>Q \<rhd> P \<longmapsto>\<questiondown>M\<lparr>N\<rparr> \<prec> P'"
        by(metis statEqTransition Associativity Commutativity Composition)
      moreover note FrP
      moreover from \<open>(\<Psi> \<otimes> \<Psi>\<^sub>P) \<otimes> \<Psi>\<^sub>R \<rhd> Q \<longmapsto>\<exclamdown>M\<lparr>\<nu>*xvec\<rparr>\<langle>N\<rangle> \<prec> Q'\<close> have "(\<Psi> \<otimes> \<Psi>\<^sub>R) \<otimes> \<Psi>\<^sub>P \<rhd> Q \<longmapsto>\<exclamdown>M\<lparr>\<nu>*xvec\<rparr>\<langle>N\<rangle> \<prec> Q'"
        by(metis statEqTransition Associativity Commutativity Composition)
      moreover note \<open>extractFrame Q = \<langle>A\<^sub>Q, \<Psi>\<^sub>Q\<rangle>\<close>
      moreover from \<open>A\<^sub>P \<sharp>* Q\<close> \<open>A\<^sub>P \<sharp>* R\<close> \<open>A\<^sub>P \<sharp>* A\<^sub>Q\<^sub>R\<close> Aeq \<open>extractFrame Q = \<langle>A\<^sub>Q, \<Psi>\<^sub>Q\<rangle>\<close> \<open>extractFrame R = \<langle>A\<^sub>R, \<Psi>\<^sub>R\<rangle>\<close>
      have "A\<^sub>P \<sharp>* A\<^sub>Q" and "A\<^sub>P \<sharp>* \<Psi>\<^sub>R" by(auto dest: extractFrameFreshChain)
      moreover from \<open>A\<^sub>Q\<^sub>R \<sharp>* \<Psi>\<close>  \<open>A\<^sub>Q\<^sub>R \<sharp>* P\<close> Aeq have "A\<^sub>Q \<sharp>* \<Psi>" and "A\<^sub>Q \<sharp>* P" by simp+
      ultimately have PQTrans: "\<Psi> \<otimes> \<Psi>\<^sub>R \<rhd> P \<parallel> Q \<longmapsto>\<exclamdown>M\<lparr>\<nu>*xvec\<rparr>\<langle>N\<rangle> \<prec> (P' \<parallel> Q')"
        using \<open>A\<^sub>P \<sharp>* \<Psi>\<close> \<open>A\<^sub>P \<sharp>* P\<close> \<open>A\<^sub>P \<sharp>* Q\<close> \<open>A\<^sub>P \<sharp>* M\<close> \<open>A\<^sub>P \<sharp>* A\<^sub>Q\<close> \<open>A\<^sub>Q \<sharp>* \<Psi>\<close> \<open>A\<^sub>Q \<sharp>* \<Psi>\<^sub>R\<close> \<open>A\<^sub>Q \<sharp>* P\<close> \<open>A\<^sub>Q \<sharp>* Q\<close> \<open>A\<^sub>Q \<sharp>* M\<close> \<open>xvec \<sharp>* P\<close>
        by(intro BrComm1) (assumption | force)+
      have RTrans: "(\<Psi> \<otimes> \<Psi>\<^sub>P) \<otimes> \<Psi>\<^sub>Q \<rhd> R \<longmapsto>\<questiondown>M\<lparr>N\<rparr> \<prec> R'" and FrR: "extractFrame R = \<langle>A\<^sub>R, \<Psi>\<^sub>R\<rangle>" by fact+
      note PQTrans
      moreover from FrP \<open>extractFrame Q = \<langle>A\<^sub>Q, \<Psi>\<^sub>Q\<rangle>\<close> \<open>A\<^sub>P \<sharp>* A\<^sub>Q\<close> \<open>A\<^sub>P \<sharp>* \<Psi>\<^sub>Q\<close> \<open>A\<^sub>Q\<^sub>R \<sharp>* \<Psi>\<^sub>P\<close> Aeq
      have "extractFrame(P \<parallel> Q) = \<langle>(A\<^sub>P@A\<^sub>Q), \<Psi>\<^sub>P \<otimes> \<Psi>\<^sub>Q\<rangle>" by simp+
      moreover from RTrans have "\<Psi> \<otimes> (\<Psi>\<^sub>P \<otimes> \<Psi>\<^sub>Q) \<rhd> R \<longmapsto>\<questiondown>M\<lparr>N\<rparr> \<prec> R'"
        by (metis Associativity statEqTransition)
      moreover note FrR
      moreover note \<open>A\<^sub>P \<sharp>* \<Psi>\<close> \<open>A\<^sub>Q \<sharp>* \<Psi>\<close> \<open>A\<^sub>P \<sharp>* P\<close> \<open>A\<^sub>P \<sharp>* Q\<close> \<open>A\<^sub>Q \<sharp>* P\<close> \<open>A\<^sub>Q \<sharp>* Q\<close> \<open>A\<^sub>P \<sharp>* R\<close> \<open>A\<^sub>Q \<sharp>* R\<close>
        \<open>A\<^sub>P \<sharp>* M\<close> \<open>A\<^sub>Q \<sharp>* M\<close> \<open>A\<^sub>P \<sharp>* A\<^sub>R\<close> \<open>A\<^sub>Q \<sharp>* A\<^sub>R\<close> \<open>A\<^sub>R \<sharp>* \<Psi>\<close> \<open>A\<^sub>R \<sharp>* P\<close> \<open>A\<^sub>R \<sharp>* Q\<close> \<open>A\<^sub>R \<sharp>* R\<close> \<open>A\<^sub>R \<sharp>* M\<close>
        \<open>xvec \<sharp>* P\<close> \<open>xvec \<sharp>* Q\<close> \<open>xvec \<sharp>* R\<close>
      ultimately have "\<Psi> \<rhd> (P \<parallel> Q) \<parallel> R \<longmapsto>\<exclamdown>M\<lparr>\<nu>*xvec\<rparr>\<langle>N\<rangle> \<prec> (P' \<parallel> Q') \<parallel> R'"
        by(auto intro: BrComm2)
      moreover have "(\<Psi>, (P' \<parallel> Q') \<parallel> R', (P' \<parallel> (Q' \<parallel> R'))) \<in> Rel"
        by(rule C1)
      ultimately show ?case by blast
    qed
  next
    case(cBrComm2 \<Psi>\<^sub>Q\<^sub>R M xvec N P' A\<^sub>P \<Psi>\<^sub>P QR' A\<^sub>Q\<^sub>R)
    from \<open>\<exclamdown>M\<lparr>\<nu>*xvec\<rparr>\<langle>N\<rangle> = \<alpha>\<close> \<open>bn \<alpha> \<sharp>* Q\<close> \<open>bn \<alpha> \<sharp>* R\<close> have "xvec \<sharp>* Q" and "xvec \<sharp>* R" by auto
    from \<open>A\<^sub>Q\<^sub>R \<sharp>* (\<Psi>, P, Q, R, \<alpha>)\<close> have "A\<^sub>Q\<^sub>R \<sharp>* Q" and "A\<^sub>Q\<^sub>R \<sharp>* R" and "A\<^sub>Q\<^sub>R \<sharp>* \<Psi>" by simp+
    from \<open>A\<^sub>P \<sharp>* (Q \<parallel> R)\<close> have "A\<^sub>P \<sharp>* Q" and "A\<^sub>P \<sharp>* R" by simp+
    have PTrans: "\<Psi> \<otimes> \<Psi>\<^sub>Q\<^sub>R \<rhd> P \<longmapsto>\<exclamdown>M\<lparr>\<nu>*xvec\<rparr>\<langle>N\<rangle> \<prec> P'" and FrP: "extractFrame P = \<langle>A\<^sub>P, \<Psi>\<^sub>P\<rangle>" by fact+
    note \<open>\<Psi> \<otimes> \<Psi>\<^sub>P \<rhd> Q \<parallel> R \<longmapsto>\<questiondown>M\<lparr>N\<rparr> \<prec> QR'\<close> \<open>extractFrame(Q \<parallel> R) = \<langle>A\<^sub>Q\<^sub>R, \<Psi>\<^sub>Q\<^sub>R\<rangle>\<close> \<open>distinct A\<^sub>Q\<^sub>R\<close>
    moreover from \<open>A\<^sub>Q\<^sub>R \<sharp>* \<Psi>\<close> \<open>A\<^sub>Q\<^sub>R \<sharp>* \<Psi>\<^sub>P\<close> have "A\<^sub>Q\<^sub>R \<sharp>* (\<Psi> \<otimes> \<Psi>\<^sub>P)" by force
    ultimately show ?case using \<open>A\<^sub>Q\<^sub>R \<sharp>* Q\<close> \<open>A\<^sub>Q\<^sub>R \<sharp>* R\<close> \<open>A\<^sub>Q\<^sub>R \<sharp>* M\<close>
    proof(induct rule: parCasesBrInputFrame)
      case(cPar1 Q' A\<^sub>Q \<Psi>\<^sub>Q A\<^sub>R \<Psi>\<^sub>R)
      from \<open>A\<^sub>Q\<^sub>R \<sharp>* N\<close> \<open>A\<^sub>Q\<^sub>R = A\<^sub>Q @ A\<^sub>R\<close> have "A\<^sub>Q \<sharp>* N" and "A\<^sub>R \<sharp>* N"
        by simp+
      from \<open>A\<^sub>Q\<^sub>R \<sharp>* xvec\<close> \<open>A\<^sub>Q\<^sub>R = (A\<^sub>Q@A\<^sub>R)\<close> have "A\<^sub>Q \<sharp>* xvec" and "A\<^sub>R \<sharp>* xvec"
        by simp+
      have Aeq: "A\<^sub>Q\<^sub>R = A\<^sub>Q@A\<^sub>R" and \<Psi>eq: "\<Psi>\<^sub>Q\<^sub>R = \<Psi>\<^sub>Q \<otimes> \<Psi>\<^sub>R" by fact+
      from PTrans \<Psi>eq have "(\<Psi> \<otimes> \<Psi>\<^sub>R) \<otimes> \<Psi>\<^sub>Q \<rhd> P \<longmapsto>\<exclamdown>M\<lparr>\<nu>*xvec\<rparr>\<langle>N\<rangle> \<prec> P'"
        by(metis statEqTransition Associativity Commutativity Composition)
      moreover note FrP
      moreover from \<open>(\<Psi> \<otimes> \<Psi>\<^sub>P) \<otimes> \<Psi>\<^sub>R \<rhd> Q \<longmapsto>\<questiondown>M\<lparr>N\<rparr> \<prec> Q'\<close> have "(\<Psi> \<otimes> \<Psi>\<^sub>R) \<otimes> \<Psi>\<^sub>P \<rhd> Q \<longmapsto>\<questiondown>M\<lparr>N\<rparr> \<prec> Q'"
        by(metis statEqTransition Associativity Commutativity Composition)
      moreover note \<open>extractFrame Q = \<langle>A\<^sub>Q, \<Psi>\<^sub>Q\<rangle>\<close>
      moreover from \<open>A\<^sub>P \<sharp>* Q\<close> \<open>A\<^sub>P \<sharp>* R\<close> \<open>A\<^sub>P \<sharp>* A\<^sub>Q\<^sub>R\<close> Aeq \<open>extractFrame Q = \<langle>A\<^sub>Q, \<Psi>\<^sub>Q\<rangle>\<close> \<open>extractFrame R = \<langle>A\<^sub>R, \<Psi>\<^sub>R\<rangle>\<close>
      have "A\<^sub>P \<sharp>* A\<^sub>Q" and "A\<^sub>P \<sharp>* \<Psi>\<^sub>R" by(auto dest: extractFrameFreshChain)
      moreover from \<open>A\<^sub>Q\<^sub>R \<sharp>* \<Psi>\<close>  \<open>A\<^sub>Q\<^sub>R \<sharp>* P\<close> Aeq have "A\<^sub>Q \<sharp>* \<Psi>" and "A\<^sub>Q \<sharp>* P" by simp+
      ultimately have "\<Psi> \<otimes> \<Psi>\<^sub>R \<rhd> P \<parallel> Q \<longmapsto>\<exclamdown>M\<lparr>\<nu>*xvec\<rparr>\<langle>N\<rangle> \<prec> (P' \<parallel> Q')"
        using \<open>A\<^sub>P \<sharp>* \<Psi>\<close> \<open>A\<^sub>P \<sharp>* P\<close> \<open>A\<^sub>P \<sharp>* Q\<close> \<open>A\<^sub>P \<sharp>* M\<close> \<open>A\<^sub>P \<sharp>* A\<^sub>Q\<close> \<open>A\<^sub>Q \<sharp>* \<Psi>\<close> \<open>A\<^sub>Q \<sharp>* \<Psi>\<^sub>R\<close> \<open>A\<^sub>Q \<sharp>* P\<close> \<open>A\<^sub>Q \<sharp>* Q\<close> \<open>A\<^sub>Q \<sharp>* M\<close> \<open>xvec \<sharp>* Q\<close>
        by(intro BrComm2) (assumption | force)+
      moreover from \<open>A\<^sub>Q\<^sub>R \<sharp>* \<Psi>\<close> \<open>A\<^sub>Q\<^sub>R \<sharp>* P\<close> Aeq have "A\<^sub>R \<sharp>* \<Psi>" and "A\<^sub>R \<sharp>* P" by simp+
      ultimately have "\<Psi> \<rhd> (P \<parallel> Q) \<parallel> R \<longmapsto>\<exclamdown>M\<lparr>\<nu>*xvec\<rparr>\<langle>N\<rangle> \<prec> (P' \<parallel> Q') \<parallel> R" using \<open>extractFrame R = \<langle>A\<^sub>R, \<Psi>\<^sub>R\<rangle>\<close> \<open>A\<^sub>R \<sharp>* Q\<close> \<open>A\<^sub>R \<sharp>* M\<close> \<open>A\<^sub>R \<sharp>* N\<close> \<open>xvec \<sharp>* R\<close> \<open>A\<^sub>R \<sharp>* xvec\<close>
        by(intro Par1) (assumption | simp)+
      moreover have "(\<Psi>, (P' \<parallel> Q') \<parallel> R, (P' \<parallel> (Q' \<parallel> R))) \<in> Rel"
        by(rule C1)
      ultimately show ?case by blast
    next
      case(cPar2 R' A\<^sub>Q \<Psi>\<^sub>Q A\<^sub>R \<Psi>\<^sub>R)
      from \<open>A\<^sub>Q\<^sub>R \<sharp>* N\<close> \<open>A\<^sub>Q\<^sub>R \<sharp>* xvec\<close> \<open>A\<^sub>Q\<^sub>R = A\<^sub>Q @ A\<^sub>R\<close> have "A\<^sub>Q \<sharp>* N" and "A\<^sub>R \<sharp>* N" and "A\<^sub>Q \<sharp>* xvec" and "A\<^sub>R \<sharp>* xvec"
        by simp+
      have Aeq: "A\<^sub>Q\<^sub>R = A\<^sub>Q@A\<^sub>R" and \<Psi>eq: "\<Psi>\<^sub>Q\<^sub>R = \<Psi>\<^sub>Q \<otimes> \<Psi>\<^sub>R" by fact+
      from \<open>A\<^sub>Q\<^sub>R \<sharp>* \<Psi>\<close> \<open>A\<^sub>Q\<^sub>R \<sharp>* P\<close> \<open>A\<^sub>Q\<^sub>R \<sharp>* \<Psi>\<^sub>P\<close> \<open>A\<^sub>P \<sharp>* A\<^sub>Q\<^sub>R\<close> Aeq
      have "A\<^sub>R \<sharp>* \<Psi>" and "A\<^sub>R \<sharp>* \<Psi>\<^sub>P" and "A\<^sub>P \<sharp>* A\<^sub>R" and "A\<^sub>P \<sharp>* A\<^sub>Q" and "A\<^sub>R \<sharp>* P" and "A\<^sub>Q \<sharp>* \<Psi>" and "A\<^sub>Q \<sharp>* \<Psi>\<^sub>P" by simp+
      have RTrans: "(\<Psi> \<otimes> \<Psi>\<^sub>P) \<otimes> \<Psi>\<^sub>Q \<rhd> R \<longmapsto>\<questiondown>M\<lparr>N\<rparr> \<prec> R'" and FrR: "extractFrame R = \<langle>A\<^sub>R, \<Psi>\<^sub>R\<rangle>" by fact+
      from PTrans \<Psi>eq have "(\<Psi> \<otimes> \<Psi>\<^sub>R) \<otimes> \<Psi>\<^sub>Q \<rhd> P \<longmapsto>\<exclamdown>M\<lparr>\<nu>*xvec\<rparr>\<langle>N\<rangle> \<prec> P'"
        by(metis statEqTransition Associativity Commutativity Composition)
      moreover from \<open>A\<^sub>P \<sharp>* R\<close> \<open>A\<^sub>P \<sharp>* Q\<close> \<open>A\<^sub>P \<sharp>* A\<^sub>Q\<^sub>R\<close> FrR \<open>extractFrame Q = \<langle>A\<^sub>Q, \<Psi>\<^sub>Q\<rangle>\<close> Aeq have "A\<^sub>P \<sharp>* \<Psi>\<^sub>Q" and "A\<^sub>P \<sharp>* \<Psi>\<^sub>R"
        by(auto dest: extractFrameFreshChain)
      moreover from \<open>A\<^sub>Q\<^sub>R \<sharp>* P\<close> \<open>A\<^sub>Q\<^sub>R \<sharp>* N\<close> Aeq have "A\<^sub>Q \<sharp>* P" and "A\<^sub>Q \<sharp>* N" by simp+
      ultimately have "\<Psi> \<otimes> \<Psi>\<^sub>R \<rhd> P \<parallel> Q \<longmapsto>\<exclamdown>M\<lparr>\<nu>*xvec\<rparr>\<langle>N\<rangle> \<prec> (P' \<parallel> Q)" using \<open>extractFrame Q = \<langle>A\<^sub>Q, \<Psi>\<^sub>Q\<rangle>\<close> \<open>A\<^sub>Q \<sharp>* \<Psi>\<^sub>R\<close>
          \<open>A\<^sub>Q \<sharp>* M\<close> \<open>A\<^sub>Q \<sharp>* \<Psi>\<close> \<open>xvec \<sharp>* Q\<close> \<open>A\<^sub>Q \<sharp>* xvec\<close>
        by(intro Par1) (assumption | force)+
      moreover from FrP \<open>extractFrame Q = \<langle>A\<^sub>Q, \<Psi>\<^sub>Q\<rangle>\<close> \<open>A\<^sub>P \<sharp>* A\<^sub>Q\<close> \<open>A\<^sub>P \<sharp>* \<Psi>\<^sub>Q\<close> \<open>A\<^sub>Q \<sharp>* \<Psi>\<^sub>P\<close>
      have "extractFrame(P \<parallel> Q) = \<langle>(A\<^sub>P@A\<^sub>Q), \<Psi>\<^sub>P \<otimes> \<Psi>\<^sub>Q\<rangle>" by simp+
      moreover from RTrans have "\<Psi> \<otimes> (\<Psi>\<^sub>P \<otimes> \<Psi>\<^sub>Q) \<rhd> R \<longmapsto>\<questiondown>M\<lparr>N\<rparr> \<prec> R'" by(metis Associativity statEqTransition)
      moreover note FrR
      ultimately have "\<Psi> \<rhd> (P \<parallel> Q) \<parallel> R \<longmapsto>\<exclamdown>M\<lparr>\<nu>*xvec\<rparr>\<langle>N\<rangle> \<prec> ((P' \<parallel> Q) \<parallel> R')"
        using \<open>A\<^sub>P \<sharp>* \<Psi>\<close> \<open>A\<^sub>Q \<sharp>* \<Psi>\<close> \<open>A\<^sub>P \<sharp>* P\<close> \<open>A\<^sub>Q \<sharp>* P\<close> \<open>A\<^sub>P \<sharp>* Q\<close> \<open>A\<^sub>Q \<sharp>* Q\<close> \<open>A\<^sub>P \<sharp>* R\<close> \<open>A\<^sub>Q \<sharp>* R\<close> \<open>A\<^sub>P \<sharp>* M\<close> \<open>A\<^sub>Q \<sharp>* M\<close> \<open>A\<^sub>P \<sharp>* A\<^sub>R\<close> \<open>A\<^sub>Q \<sharp>* A\<^sub>R\<close>
          \<open>A\<^sub>R \<sharp>* \<Psi>\<close> \<open>A\<^sub>R \<sharp>* P\<close> \<open>A\<^sub>R \<sharp>* Q\<close> \<open>A\<^sub>R \<sharp>* R\<close> \<open>A\<^sub>R \<sharp>* M\<close> \<open>xvec \<sharp>* P\<close> \<open>xvec \<sharp>* R\<close>
        by(auto intro: BrComm2)
      moreover have "(\<Psi>, ((P' \<parallel> Q) \<parallel> R'), (P' \<parallel> (Q \<parallel> R'))) \<in> Rel"
        by(rule C1)
      ultimately show ?case by blast
    next
      case(cBrMerge \<Psi>\<^sub>R Q' A\<^sub>Q \<Psi>\<^sub>Q R' A\<^sub>R)
      from \<open>A\<^sub>Q\<^sub>R \<sharp>* N\<close> \<open>A\<^sub>Q\<^sub>R = A\<^sub>Q @ A\<^sub>R\<close> have "A\<^sub>Q \<sharp>* N" and "A\<^sub>R \<sharp>* N"
        by simp+
      from \<open>A\<^sub>Q\<^sub>R \<sharp>* xvec\<close> \<open>A\<^sub>Q\<^sub>R = (A\<^sub>Q@A\<^sub>R)\<close> have "A\<^sub>Q \<sharp>* xvec" and "A\<^sub>R \<sharp>* xvec"
        by simp+
      have Aeq: "A\<^sub>Q\<^sub>R = A\<^sub>Q@A\<^sub>R" and \<Psi>eq: "\<Psi>\<^sub>Q\<^sub>R = \<Psi>\<^sub>Q \<otimes> \<Psi>\<^sub>R" by fact+
      from Aeq \<open>A\<^sub>Q\<^sub>R \<sharp>* P\<close> have "A\<^sub>Q \<sharp>* P" and "A\<^sub>R \<sharp>* P" by simp+
      from Aeq \<open>A\<^sub>Q\<^sub>R \<sharp>* M\<close> have "A\<^sub>Q \<sharp>* M" and "A\<^sub>R \<sharp>* M" by simp+
      from Aeq \<open>A\<^sub>Q\<^sub>R \<sharp>* \<Psi>\<close> have "A\<^sub>Q \<sharp>* \<Psi>" and "A\<^sub>R \<sharp>* \<Psi>" by simp+
      from Aeq \<open>A\<^sub>P \<sharp>* A\<^sub>Q\<^sub>R\<close> have "A\<^sub>P \<sharp>* A\<^sub>Q" and "A\<^sub>P \<sharp>* A\<^sub>R" by simp+
      with \<open>A\<^sub>P \<sharp>* Q\<close> \<open>extractFrame Q = \<langle>A\<^sub>Q, \<Psi>\<^sub>Q\<rangle>\<close> have "A\<^sub>P \<sharp>* \<Psi>\<^sub>Q"
        by (metis extractFrameFreshChain freshChainSym freshFrameDest)
      from PTrans \<Psi>eq have "(\<Psi> \<otimes> \<Psi>\<^sub>R) \<otimes> \<Psi>\<^sub>Q \<rhd> P \<longmapsto>\<exclamdown>M\<lparr>\<nu>*xvec\<rparr>\<langle>N\<rangle> \<prec> P'"
        by(metis statEqTransition Associativity Commutativity Composition)
      moreover note FrP
      moreover from \<open>(\<Psi> \<otimes> \<Psi>\<^sub>P) \<otimes> \<Psi>\<^sub>R \<rhd> Q \<longmapsto>\<questiondown>M\<lparr>N\<rparr> \<prec> Q'\<close> have "(\<Psi> \<otimes> \<Psi>\<^sub>R) \<otimes> \<Psi>\<^sub>P \<rhd> Q \<longmapsto>\<questiondown>M\<lparr>N\<rparr> \<prec> Q'"
        by(metis statEqTransition Associativity Commutativity Composition)
      moreover note \<open>extractFrame Q = \<langle>A\<^sub>Q, \<Psi>\<^sub>Q\<rangle>\<close>
      moreover from \<open>A\<^sub>P \<sharp>* Q\<close> \<open>A\<^sub>P \<sharp>* R\<close> \<open>A\<^sub>P \<sharp>* A\<^sub>Q\<^sub>R\<close> Aeq \<open>extractFrame Q = \<langle>A\<^sub>Q, \<Psi>\<^sub>Q\<rangle>\<close> \<open>extractFrame R = \<langle>A\<^sub>R, \<Psi>\<^sub>R\<rangle>\<close>
      have "A\<^sub>P \<sharp>* A\<^sub>Q" and "A\<^sub>P \<sharp>* \<Psi>\<^sub>R" by(auto dest: extractFrameFreshChain)
      moreover from \<open>A\<^sub>Q\<^sub>R \<sharp>* \<Psi>\<close>  \<open>A\<^sub>Q\<^sub>R \<sharp>* P\<close> Aeq have "A\<^sub>Q \<sharp>* \<Psi>" and "A\<^sub>Q \<sharp>* P" by simp+
      ultimately have PQTrans: "\<Psi> \<otimes> \<Psi>\<^sub>R \<rhd> P \<parallel> Q \<longmapsto>\<exclamdown>M\<lparr>\<nu>*xvec\<rparr>\<langle>N\<rangle> \<prec> (P' \<parallel> Q')"
        using \<open>A\<^sub>P \<sharp>* \<Psi>\<close> \<open>A\<^sub>P \<sharp>* P\<close> \<open>A\<^sub>P \<sharp>* Q\<close> \<open>A\<^sub>P \<sharp>* M\<close> \<open>A\<^sub>P \<sharp>* A\<^sub>Q\<close> \<open>A\<^sub>Q \<sharp>* \<Psi>\<close> \<open>A\<^sub>Q \<sharp>* \<Psi>\<^sub>R\<close> \<open>A\<^sub>Q \<sharp>* P\<close> \<open>A\<^sub>Q \<sharp>* Q\<close> \<open>xvec \<sharp>* Q\<close> \<open>A\<^sub>Q \<sharp>* M\<close>
        by(intro BrComm2) (assumption | force)+
      have RTrans: "(\<Psi> \<otimes> \<Psi>\<^sub>P) \<otimes> \<Psi>\<^sub>Q \<rhd> R \<longmapsto>\<questiondown>M\<lparr>N\<rparr> \<prec> R'" and FrR: "extractFrame R = \<langle>A\<^sub>R, \<Psi>\<^sub>R\<rangle>" by fact+
      note PQTrans
      moreover from FrP \<open>extractFrame Q = \<langle>A\<^sub>Q, \<Psi>\<^sub>Q\<rangle>\<close> \<open>A\<^sub>P \<sharp>* A\<^sub>Q\<close> \<open>A\<^sub>P \<sharp>* \<Psi>\<^sub>Q\<close> \<open>A\<^sub>Q\<^sub>R \<sharp>* \<Psi>\<^sub>P\<close> Aeq
      have "extractFrame(P \<parallel> Q) = \<langle>(A\<^sub>P@A\<^sub>Q), \<Psi>\<^sub>P \<otimes> \<Psi>\<^sub>Q\<rangle>" by simp+
      moreover from RTrans have "\<Psi> \<otimes> (\<Psi>\<^sub>P \<otimes> \<Psi>\<^sub>Q) \<rhd> R \<longmapsto>\<questiondown>M\<lparr>N\<rparr> \<prec> R'"
        by (metis Associativity statEqTransition)
      moreover note FrR
      moreover note \<open>A\<^sub>P \<sharp>* \<Psi>\<close> \<open>A\<^sub>Q \<sharp>* \<Psi>\<close> \<open>A\<^sub>P \<sharp>* P\<close> \<open>A\<^sub>P \<sharp>* Q\<close> \<open>A\<^sub>Q \<sharp>* P\<close> \<open>A\<^sub>Q \<sharp>* Q\<close> \<open>A\<^sub>P \<sharp>* R\<close> \<open>A\<^sub>Q \<sharp>* R\<close>
        \<open>A\<^sub>P \<sharp>* M\<close> \<open>A\<^sub>Q \<sharp>* M\<close> \<open>A\<^sub>P \<sharp>* A\<^sub>R\<close> \<open>A\<^sub>Q \<sharp>* A\<^sub>R\<close> \<open>A\<^sub>R \<sharp>* \<Psi>\<close> \<open>A\<^sub>R \<sharp>* P\<close> \<open>A\<^sub>R \<sharp>* Q\<close> \<open>A\<^sub>R \<sharp>* R\<close> \<open>A\<^sub>R \<sharp>* M\<close> \<open>xvec \<sharp>* P\<close> \<open>xvec \<sharp>* R\<close>
      ultimately have "\<Psi> \<rhd> (P \<parallel> Q) \<parallel> R \<longmapsto>\<exclamdown>M\<lparr>\<nu>*xvec\<rparr>\<langle>N\<rangle> \<prec> (P' \<parallel> Q') \<parallel> R'"
        by(auto intro: BrComm2)
      moreover have "(\<Psi>, (P' \<parallel> Q') \<parallel> R', (P' \<parallel> (Q' \<parallel> R'))) \<in> Rel"
        by(rule C1)
      ultimately show ?case by blast
    qed
  qed
qed

lemma parNilLeft:
  fixes \<Psi> :: 'b
    and P   :: "('a, 'b, 'c) psi"
    and Rel :: "('b \<times> ('a, 'b, 'c) psi \<times> ('a, 'b, 'c) psi) set"

assumes "eqvt Rel"
  and   C1: "\<And>Q. (\<Psi>, Q \<parallel> \<zero>, Q) \<in> Rel"

shows "\<Psi> \<rhd> (P \<parallel> \<zero>) \<leadsto>[Rel] P"
  using \<open>eqvt Rel\<close>
proof(induct rule: simI[of _ _ _ _ "()"])
  case(cSim \<alpha> P')
  from \<open>\<Psi> \<rhd> P \<longmapsto>\<alpha> \<prec> P'\<close> have "\<Psi> \<otimes> SBottom' \<rhd> P \<longmapsto>\<alpha> \<prec> P'"
    by(metis statEqTransition Identity AssertionStatEqSym)
  then have "\<Psi> \<rhd> (P \<parallel> \<zero>) \<longmapsto>\<alpha> \<prec> (P' \<parallel> \<zero>)"
    by(rule Par1) auto
  moreover have "(\<Psi>, P' \<parallel> \<zero>, P') \<in> Rel" by(rule C1)
  ultimately show ?case by blast
qed

lemma parNilRight:
  fixes \<Psi> :: 'b
    and P   :: "('a, 'b, 'c) psi"
    and Rel :: "('b \<times> ('a, 'b, 'c) psi \<times> ('a, 'b, 'c) psi) set"

assumes "eqvt Rel"
  and   C1: "\<And>Q. (\<Psi>, Q, (Q \<parallel> \<zero>)) \<in> Rel"

shows "\<Psi> \<rhd> P \<leadsto>[Rel] (P \<parallel> \<zero>)"
  using \<open>eqvt Rel\<close>
proof(induct rule: simI[of _ _ _ _ "()"])
  case(cSim \<alpha> P')
  note \<open>\<Psi> \<rhd> P \<parallel> \<zero> \<longmapsto>\<alpha> \<prec> P'\<close> \<open>bn \<alpha> \<sharp>* \<Psi>\<close> \<open>bn \<alpha> \<sharp>* P\<close>
  moreover have "bn \<alpha> \<sharp>* \<zero>" by simp
  ultimately show ?case using \<open>bn \<alpha> \<sharp>* subject \<alpha>\<close>
  proof(induct rule: parCases[where C="()"])
    case(cPar1 P' A\<^sub>Q \<Psi>\<^sub>Q)
    from \<open>extractFrame(\<zero>) = \<langle>A\<^sub>Q, \<Psi>\<^sub>Q\<rangle>\<close> have "\<Psi>\<^sub>Q = SBottom'" by auto
    with \<open>\<Psi> \<otimes> \<Psi>\<^sub>Q \<rhd> P \<longmapsto>\<alpha> \<prec> P'\<close> have "\<Psi> \<rhd> P \<longmapsto>\<alpha> \<prec> P'"
      by(metis statEqTransition Identity)
    moreover have "(\<Psi>, P', P' \<parallel> \<zero>) \<in> Rel" by(rule C1)
    ultimately show ?case by blast
  next
    case(cPar2 Q' A\<^sub>P \<Psi>\<^sub>P)
    from \<open>\<Psi> \<otimes> \<Psi>\<^sub>P \<rhd> \<zero> \<longmapsto>\<alpha> \<prec> Q'\<close> have False
      by auto
    then show ?case by simp
  next
    case(cComm1 \<Psi>\<^sub>Q M N P' A\<^sub>P \<Psi>\<^sub>P K xvec Q' A\<^sub>Q)
    from \<open>\<Psi> \<otimes> \<Psi>\<^sub>P \<rhd> \<zero> \<longmapsto>K\<lparr>\<nu>*xvec\<rparr>\<langle>N\<rangle> \<prec> Q'\<close> have False by auto
    then show ?case by simp
  next
    case(cComm2 \<Psi>\<^sub>Q M xvec N P' A\<^sub>P \<Psi>\<^sub>P K Q' A\<^sub>Q)
    from \<open>\<Psi> \<otimes> \<Psi>\<^sub>P \<rhd> \<zero> \<longmapsto>K\<lparr>N\<rparr> \<prec> Q'\<close> have False
      by auto
    then show ?case by simp
  next
    case(cBrMerge \<Psi>\<^sub>Q M N P' A\<^sub>P \<Psi>\<^sub>P Q' A\<^sub>Q)
    from \<open>\<Psi> \<otimes> \<Psi>\<^sub>P \<rhd> \<zero> \<longmapsto> \<questiondown>M\<lparr>N\<rparr> \<prec> Q'\<close> have False
      by auto
    then show ?case by simp
  next
    case(cBrComm1 \<Psi>\<^sub>Q M N P' A\<^sub>P \<Psi>\<^sub>P xvec Q' A\<^sub>Q)
    from \<open>\<Psi> \<otimes> \<Psi>\<^sub>P \<rhd> \<zero> \<longmapsto> \<exclamdown>M\<lparr>\<nu>*xvec\<rparr>\<langle>N\<rangle> \<prec> Q'\<close> have False
      by auto
    then show ?case by simp
  next
    case(cBrComm2 \<Psi>\<^sub>Q M xvec N P' A\<^sub>P \<Psi>\<^sub>P Q' A\<^sub>Q)
    from \<open>\<Psi> \<otimes> \<Psi>\<^sub>P \<rhd> \<zero> \<longmapsto> \<questiondown>M\<lparr>N\<rparr> \<prec> Q'\<close> have False
      by auto
    then show ?case by simp
  qed
qed

lemma resNilLeft:
  fixes x   :: name
    and \<Psi>   :: 'b
    and Rel :: "('b \<times> ('a, 'b, 'c) psi \<times> ('a, 'b, 'c) psi) set"

shows "\<Psi> \<rhd> \<lparr>\<nu>x\<rparr>\<zero> \<leadsto>[Rel] \<zero>"
  by(auto simp add: simulation_def)

lemma resNilRight:
  fixes x   :: name
    and \<Psi>   :: 'b
    and Rel :: "('b \<times> ('a, 'b, 'c) psi \<times> ('a, 'b, 'c) psi) set"

shows "\<Psi> \<rhd> \<zero> \<leadsto>[Rel] \<lparr>\<nu>x\<rparr>\<zero>"
  apply(clarsimp simp add: simulation_def)
  by(cases rule: semantics.cases) (auto simp add: psi.inject alpha')

lemma inputPushResLeft:
  fixes \<Psi>   :: 'b
    and x    :: name
    and M    :: 'a
    and xvec :: "name list"
    and N    :: 'a
    and P    :: "('a, 'b, 'c) psi"

assumes "eqvt Rel"
  and   "x \<sharp> \<Psi>"
  and   "x \<sharp> M"
  and   "x \<sharp> xvec"
  and   "x \<sharp> N"
  and   C1: "\<And>Q. (\<Psi>, Q, Q) \<in> Rel"

shows "\<Psi> \<rhd> \<lparr>\<nu>x\<rparr>(M\<lparr>\<lambda>*xvec N\<rparr>.P) \<leadsto>[Rel] M\<lparr>\<lambda>*xvec N\<rparr>.\<lparr>\<nu>x\<rparr>P"
proof -
  note \<open>eqvt Rel\<close> \<open>x \<sharp> \<Psi>\<close>
  moreover have "x \<sharp> \<lparr>\<nu>x\<rparr>(M\<lparr>\<lambda>*xvec N\<rparr>.P)" by(simp add: abs_fresh)
  moreover from \<open>x \<sharp> M\<close> \<open>x \<sharp> N\<close> have "x \<sharp> M\<lparr>\<lambda>*xvec N\<rparr>.\<lparr>\<nu>x\<rparr>P"
    by(auto simp add: inputChainFresh abs_fresh)
  ultimately show ?thesis
  proof(induct rule: simIFresh[of _ _ _ _ _ "()"])
    case(cSim \<alpha> P')
    from \<open>\<Psi> \<rhd> M\<lparr>\<lambda>*xvec N\<rparr>.\<lparr>\<nu>x\<rparr>P \<longmapsto>\<alpha> \<prec> P'\<close> \<open>x \<sharp> \<alpha>\<close> show ?case
    proof(induct rule: inputCases)
      case(cInput K Tvec)
      from \<open>x \<sharp> K\<lparr>N[xvec::=Tvec]\<rparr>\<close> have "x \<sharp> K" and "x \<sharp> N[xvec::=Tvec]" by simp+
      from \<open>\<Psi> \<turnstile> M \<leftrightarrow> K\<close> \<open>distinct xvec\<close> \<open>set xvec \<subseteq> supp N\<close> \<open>length xvec = length Tvec\<close>
      have "\<Psi> \<rhd> M\<lparr>\<lambda>*xvec N\<rparr>.P \<longmapsto>K\<lparr>(N[xvec::=Tvec])\<rparr> \<prec> P[xvec::=Tvec]"
        by(rule Input)
      then have "\<Psi> \<rhd> \<lparr>\<nu>x\<rparr>(M\<lparr>\<lambda>*xvec N\<rparr>.P) \<longmapsto>K\<lparr>(N[xvec::=Tvec])\<rparr> \<prec> \<lparr>\<nu>x\<rparr>(P[xvec::=Tvec])" using \<open>x \<sharp> \<Psi>\<close> \<open>x \<sharp> K\<close> \<open>x \<sharp> N[xvec::=Tvec]\<close>
        by(intro Scope) auto
      moreover from \<open>length xvec = length Tvec\<close> \<open>distinct xvec\<close> \<open>set xvec \<subseteq> supp N\<close> \<open>x \<sharp> N[xvec::=Tvec]\<close> have "x \<sharp> Tvec"
        by(rule substTerm.subst3)
      with \<open>x \<sharp> xvec\<close> have "(\<Psi>, \<lparr>\<nu>x\<rparr>(P[xvec::=Tvec]), (\<lparr>\<nu>x\<rparr>P)[xvec::=Tvec]) \<in> Rel"
        by(force intro: C1)
      ultimately show ?case by blast
    next
      case(cBrInput K Tvec)
      from \<open>x \<sharp> \<questiondown>K\<lparr>N[xvec::=Tvec]\<rparr>\<close> have "x \<sharp> K" and "x \<sharp> N[xvec::=Tvec]" by simp+
      from \<open>\<Psi> \<turnstile> K \<succeq> M\<close> \<open>distinct xvec\<close> \<open>set xvec \<subseteq> supp N\<close> \<open>length xvec = length Tvec\<close>
      have "\<Psi> \<rhd> M\<lparr>\<lambda>*xvec N\<rparr>.P \<longmapsto>\<questiondown>K\<lparr>(N[xvec::=Tvec])\<rparr> \<prec> P[xvec::=Tvec]"
        by(rule BrInput)
      then have "\<Psi> \<rhd> \<lparr>\<nu>x\<rparr>(M\<lparr>\<lambda>*xvec N\<rparr>.P) \<longmapsto>\<questiondown>K\<lparr>(N[xvec::=Tvec])\<rparr> \<prec> \<lparr>\<nu>x\<rparr>(P[xvec::=Tvec])" using \<open>x \<sharp> \<Psi>\<close> \<open>x \<sharp> K\<close> \<open>x \<sharp> N[xvec::=Tvec]\<close>
        by(intro Scope) auto
      moreover from \<open>length xvec = length Tvec\<close> \<open>distinct xvec\<close> \<open>set xvec \<subseteq> supp N\<close> \<open>x \<sharp> N[xvec::=Tvec]\<close> have "x \<sharp> Tvec"
        by(rule substTerm.subst3)
      with \<open>x \<sharp> xvec\<close> have "(\<Psi>, \<lparr>\<nu>x\<rparr>(P[xvec::=Tvec]), (\<lparr>\<nu>x\<rparr>P)[xvec::=Tvec]) \<in> Rel"
        by(force intro: C1)
      ultimately show ?case by blast
    qed
  qed
qed

lemma inputPushResRight:
  fixes \<Psi>   :: 'b
    and x    :: name
    and M    :: 'a
    and xvec :: "name list"
    and N    :: 'a
    and P    :: "('a, 'b, 'c) psi"

assumes "eqvt Rel"
  and   "x \<sharp> \<Psi>"
  and   "x \<sharp> M"
  and   "x \<sharp> xvec"
  and   "x \<sharp> N"
  and   C1: "\<And>Q. (\<Psi>, Q, Q) \<in> Rel"

shows "\<Psi> \<rhd> M\<lparr>\<lambda>*xvec N\<rparr>.\<lparr>\<nu>x\<rparr>P \<leadsto>[Rel] \<lparr>\<nu>x\<rparr>(M\<lparr>\<lambda>*xvec N\<rparr>.P)"
proof -
  note \<open>eqvt Rel\<close> \<open>x \<sharp> \<Psi>\<close>
  moreover from \<open>x \<sharp> M\<close> \<open>x \<sharp> N\<close> have "x \<sharp> M\<lparr>\<lambda>*xvec N\<rparr>.\<lparr>\<nu>x\<rparr>P"
    by(auto simp add: inputChainFresh abs_fresh)
  moreover have "x \<sharp> \<lparr>\<nu>x\<rparr>(M\<lparr>\<lambda>*xvec N\<rparr>.P)" by(simp add: abs_fresh)
  ultimately show ?thesis
  proof(induct rule: simIFresh[of _ _ _ _ _ "()"])
    case(cSim \<alpha> P')
    note \<open>\<Psi> \<rhd> \<lparr>\<nu>x\<rparr>(M\<lparr>\<lambda>*xvec N\<rparr>.P) \<longmapsto>\<alpha> \<prec> P'\<close> \<open>x \<sharp> \<Psi>\<close> \<open>x \<sharp> \<alpha>\<close> \<open>x \<sharp> P'\<close> \<open>bn \<alpha> \<sharp>* \<Psi>\<close>
    moreover from \<open>bn \<alpha> \<sharp>* (\<lparr>\<nu>x\<rparr>(M\<lparr>\<lambda>*xvec N\<rparr>.P))\<close> \<open>x \<sharp> \<alpha>\<close> have  "bn \<alpha> \<sharp>* (M\<lparr>\<lambda>*xvec N\<rparr>.P)"
      by simp
    ultimately show ?case using \<open>bn \<alpha> \<sharp>* subject \<alpha>\<close>
    proof(induct rule: resCases[where C="()"])
      case(cRes P')
      from \<open>\<Psi> \<rhd> M\<lparr>\<lambda>*xvec N\<rparr>.P \<longmapsto>\<alpha> \<prec> P'\<close> \<open>x \<sharp> \<alpha>\<close> show ?case
      proof(induct rule: inputCases)
        case(cInput K Tvec)
        from \<open>x \<sharp> K\<lparr>N[xvec::=Tvec]\<rparr>\<close> have "x \<sharp> K" and "x \<sharp> N[xvec::=Tvec]" by simp+
        from \<open>\<Psi> \<turnstile> M \<leftrightarrow> K\<close> \<open>distinct xvec\<close> \<open>set xvec \<subseteq> supp N\<close> \<open>length xvec = length Tvec\<close>
        have "\<Psi> \<rhd> M\<lparr>\<lambda>*xvec N\<rparr>.(\<lparr>\<nu>x\<rparr>P) \<longmapsto>K\<lparr>(N[xvec::=Tvec])\<rparr> \<prec> (\<lparr>\<nu>x\<rparr>P)[xvec::=Tvec]"
          by(rule Input)
        moreover from \<open>length xvec = length Tvec\<close> \<open>distinct xvec\<close> \<open>set xvec \<subseteq> supp N\<close> \<open>x \<sharp> N[xvec::=Tvec]\<close> have "x \<sharp> Tvec"
          by(rule substTerm.subst3)
        with \<open>x \<sharp> xvec\<close> have "(\<Psi>, (\<lparr>\<nu>x\<rparr>P)[xvec::=Tvec], \<lparr>\<nu>x\<rparr>(P[xvec::=Tvec])) \<in> Rel"
          by(force intro: C1)
        ultimately show ?case by blast
      next
        case(cBrInput K Tvec)
        from \<open>x \<sharp> \<questiondown>K\<lparr>N[xvec::=Tvec]\<rparr>\<close> have "x \<sharp> K" and "x \<sharp> N[xvec::=Tvec]" by simp+
        from \<open>\<Psi> \<turnstile> K \<succeq> M\<close> \<open>distinct xvec\<close> \<open>set xvec \<subseteq> supp N\<close> \<open>length xvec = length Tvec\<close>
        have "\<Psi> \<rhd> M\<lparr>\<lambda>*xvec N\<rparr>.(\<lparr>\<nu>x\<rparr>P) \<longmapsto>\<questiondown>K\<lparr>(N[xvec::=Tvec])\<rparr> \<prec> (\<lparr>\<nu>x\<rparr>P)[xvec::=Tvec]"
          by(rule BrInput)
        moreover from \<open>length xvec = length Tvec\<close> \<open>distinct xvec\<close> \<open>set xvec \<subseteq> supp N\<close> \<open>x \<sharp> N[xvec::=Tvec]\<close> have "x \<sharp> Tvec"
          by(rule substTerm.subst3)
        with \<open>x \<sharp> xvec\<close> have "(\<Psi>, (\<lparr>\<nu>x\<rparr>P)[xvec::=Tvec], \<lparr>\<nu>x\<rparr>(P[xvec::=Tvec])) \<in> Rel"
          by(force intro: C1)
        ultimately show ?case by blast
      qed
    next
      case cOpen
      then have False by auto
      then show ?case by simp
    next
      case cBrOpen
      then have False by auto
      then show ?case by simp
    next
      case (cBrClose M xvec N P')
      then have False by auto
      then show ?case by simp
    qed
  qed
qed

lemma outputPushResLeft:
  fixes \<Psi>   :: 'b
    and x    :: name
    and M    :: 'a
    and N    :: 'a
    and P    :: "('a, 'b, 'c) psi"

assumes "eqvt Rel"
  and   "x \<sharp> \<Psi>"
  and   "x \<sharp> M"
  and   "x \<sharp> N"
  and   C1: "\<And>Q. (\<Psi>, Q, Q) \<in> Rel"

shows "\<Psi> \<rhd> \<lparr>\<nu>x\<rparr>(M\<langle>N\<rangle>.P) \<leadsto>[Rel] M\<langle>N\<rangle>.\<lparr>\<nu>x\<rparr>P"
proof -
  note \<open>eqvt Rel\<close> \<open>x \<sharp> \<Psi>\<close>
  moreover have "x \<sharp> \<lparr>\<nu>x\<rparr>(M\<langle>N\<rangle>.P)" by(simp add: abs_fresh)
  moreover from \<open>x \<sharp> M\<close> \<open>x \<sharp> N\<close> have "x \<sharp> M\<langle>N\<rangle>.\<lparr>\<nu>x\<rparr>P"
    by(auto simp add: abs_fresh)
  ultimately show ?thesis
  proof(induct rule: simIFresh[of _ _ _ _ _ "()"])
    case(cSim \<alpha> P')
    from \<open>\<Psi> \<rhd> M\<langle>N\<rangle>.\<lparr>\<nu>x\<rparr>P \<longmapsto>\<alpha> \<prec> P'\<close> \<open>x \<sharp> \<alpha>\<close>
    show ?case
    proof(induct rule: outputCases)
      case(cOutput K)
      from \<open>\<Psi> \<turnstile> M \<leftrightarrow> K\<close> have "\<Psi> \<rhd> M\<langle>N\<rangle>.P \<longmapsto>K\<langle>N\<rangle> \<prec> P"
        by(rule Output)
      then have "\<Psi> \<rhd> \<lparr>\<nu>x\<rparr>(M\<langle>N\<rangle>.P) \<longmapsto>K\<langle>N\<rangle> \<prec> \<lparr>\<nu>x\<rparr>P" using \<open>x \<sharp> \<Psi>\<close> \<open>x \<sharp> K\<langle>N\<rangle>\<close>
        by(rule Scope)
      moreover have "(\<Psi>, \<lparr>\<nu>x\<rparr>P, \<lparr>\<nu>x\<rparr>P) \<in> Rel" by(rule C1)
      ultimately show ?case by blast
    next
      case(cBrOutput K)
      from \<open>\<Psi> \<turnstile> M \<preceq> K\<close> have "\<Psi> \<rhd> M\<langle>N\<rangle>.P \<longmapsto>\<exclamdown>K\<langle>N\<rangle> \<prec> P"
        by(rule BrOutput)
      then have "\<Psi> \<rhd> \<lparr>\<nu>x\<rparr>(M\<langle>N\<rangle>.P) \<longmapsto>\<exclamdown>K\<langle>N\<rangle> \<prec> \<lparr>\<nu>x\<rparr>P" using \<open>x \<sharp> \<Psi>\<close> \<open>x \<sharp> \<exclamdown>K\<langle>N\<rangle>\<close>
        by(rule Scope)
      moreover have "(\<Psi>, \<lparr>\<nu>x\<rparr>P, \<lparr>\<nu>x\<rparr>P) \<in> Rel" by(rule C1)
      ultimately show ?case by blast
    qed
  qed
qed

lemma broutputNoBind:
  fixes \<Psi> :: 'b
    and M  :: 'a
    and N  :: 'a
    and P  :: "('a, 'b, 'c) psi"
    and \<alpha>  :: "'a action"
    and P' :: "('a, 'b, 'c) psi"

assumes "\<Psi> \<rhd> M\<langle>N\<rangle>.P \<longmapsto>(\<exclamdown>K\<lparr>\<nu>*xvec\<rparr>\<langle>N'\<rangle>) \<prec> P'"
shows "xvec = []"
proof -
  from assms have "bn(\<exclamdown>K\<lparr>\<nu>*xvec\<rparr>\<langle>N'\<rangle>) = []"
    by(induct rule: outputCases) auto
  then show ?thesis by simp
qed

lemma broutputObjectEq:
  fixes \<Psi> :: 'b
    and M  :: 'a
    and N  :: 'a
    and P  :: "('a, 'b, 'c) psi"
    and \<alpha>  :: "'a action"
    and P' :: "('a, 'b, 'c) psi"

assumes "\<Psi> \<rhd> M\<langle>N\<rangle>.P \<longmapsto>(\<exclamdown>K\<lparr>\<nu>*xvec\<rparr>\<langle>N'\<rangle>) \<prec> P'"
shows "N = N'"
proof -
  from assms have "object(\<exclamdown>K\<lparr>\<nu>*xvec\<rparr>\<langle>N'\<rangle>) = Some N"
    by(induct rule: outputCases) auto
  then show ?thesis
    by simp
qed

lemma brOutputOutputCases[consumes 1, case_names cBrOutput]:
  fixes \<Psi> :: 'b
    and M  :: 'a
    and N  :: 'a
    and P  :: "('a, 'b, 'c) psi"
    and \<alpha>  :: "'a action"
    and P' :: "('a, 'b, 'c) psi"

assumes Trans: "\<Psi> \<rhd> M\<langle>N\<rangle>.P \<longmapsto>(\<exclamdown>K\<lparr>\<nu>*xvec\<rparr>\<langle>N'\<rangle>) \<prec> P'"
  and   rBrOutput: "\<And>K. \<Psi> \<turnstile> M \<preceq> K \<Longrightarrow> Prop (\<exclamdown>K\<langle>N\<rangle>) P"

shows "Prop (\<exclamdown>K\<lparr>\<nu>*xvec\<rparr>\<langle>N'\<rangle>) P'"
proof -
  have "xvec = []" using Trans by(rule broutputNoBind)
  then obtain K' N'' where eq: "(\<exclamdown>K\<lparr>\<nu>*xvec\<rparr>\<langle>N'\<rangle>)= \<exclamdown>K'\<langle>N''\<rangle>"
    by blast
  have "N = N'" using Trans by(rule broutputObjectEq)
  from Trans \<open>(\<exclamdown>K\<lparr>\<nu>*xvec\<rparr>\<langle>N'\<rangle>)= \<exclamdown>K'\<langle>N''\<rangle>\<close>
  show ?thesis unfolding \<open>N = N'\<close>[symmetric]
  proof(induct rule: outputCases)
    case (cOutput K) then show ?case by simp
  next
    case (cBrOutput K) then show ?case
      by(intro rBrOutput)
  qed
qed

lemma outputPushResRight:
  fixes \<Psi>   :: 'b
    and x    :: name
    and M    :: 'a
    and N    :: 'a
    and P    :: "('a, 'b, 'c) psi"

assumes "eqvt Rel"
  and   "x \<sharp> \<Psi>"
  and   "x \<sharp> M"
  and   "x \<sharp> N"
  and   C1: "\<And>Q. (\<Psi>, Q, Q) \<in> Rel"

shows "\<Psi> \<rhd> M\<langle>N\<rangle>.\<lparr>\<nu>x\<rparr>P \<leadsto>[Rel] \<lparr>\<nu>x\<rparr>(M\<langle>N\<rangle>.P)"
proof -
  note \<open>eqvt Rel\<close> \<open>x \<sharp> \<Psi>\<close>
  moreover from \<open>x \<sharp> M\<close> \<open>x \<sharp> N\<close> have "x \<sharp> M\<langle>N\<rangle>.\<lparr>\<nu>x\<rparr>P"
    by(auto simp add: abs_fresh)
  moreover have "x \<sharp> \<lparr>\<nu>x\<rparr>(M\<langle>N\<rangle>.P)" by(simp add: abs_fresh)
  ultimately show ?thesis
  proof(induct rule: simIFresh[of _ _ _ _ _ "(M, N)"])
    case(cSim \<alpha> P')
    note \<open>\<Psi> \<rhd> \<lparr>\<nu>x\<rparr>(M\<langle>N\<rangle>.P) \<longmapsto>\<alpha> \<prec> P'\<close> \<open>x \<sharp> \<Psi>\<close> \<open>x \<sharp> \<alpha>\<close> \<open>x \<sharp> P'\<close> \<open>bn \<alpha> \<sharp>* \<Psi>\<close>
    moreover from \<open>bn \<alpha> \<sharp>* (\<lparr>\<nu>x\<rparr>(M\<langle>N\<rangle>.P))\<close> \<open>x \<sharp> \<alpha>\<close> have "bn \<alpha> \<sharp>* (M\<langle>N\<rangle>.P)" by simp
    ultimately show ?case using \<open>bn \<alpha> \<sharp>* subject \<alpha>\<close> \<open>bn \<alpha> \<sharp>* (M, N)\<close> \<open>x \<sharp> \<alpha>\<close> \<open>x \<sharp> M\<close> \<open>x \<sharp> N\<close>
    proof(induct rule: resCases[where C="()"])
      case(cOpen K xvec1 xvec2 y N' P')
      from \<open>bn(K\<lparr>\<nu>*(xvec1@y#xvec2)\<rparr>\<langle>N'\<rangle>) \<sharp>* (M, N)\<close> have "y \<sharp> N" by simp+
      from \<open>\<Psi> \<rhd> M\<langle>N\<rangle>.P \<longmapsto>K\<lparr>\<nu>*(xvec1@xvec2)\<rparr>\<langle>([(x, y)] \<bullet> N')\<rangle> \<prec> ([(x, y)] \<bullet> P')\<close>
      have "N = ([(x, y)] \<bullet> N')"
        apply -
        by(ind_cases "\<Psi> \<rhd> M\<langle>N\<rangle>.P \<longmapsto>K\<lparr>\<nu>*(xvec1@xvec2)\<rparr>\<langle>([(x, y)] \<bullet> N')\<rangle> \<prec> ([(x, y)] \<bullet> P')")
          (auto simp add: residualInject psi.inject)
      with \<open>x \<sharp> N\<close> \<open>y \<sharp> N\<close> \<open>x \<noteq> y\<close> have "N = N'"
        by(subst pt_bij[OF pt_name_inst, OF at_name_inst, symmetric, where pi="[(x, y)]"])
          (simp add: fresh_left calc_atm)
      with \<open>y \<in> supp N'\<close> \<open>y \<sharp> N\<close> have False by(simp add: fresh_def)
      then show ?case by simp
    next
      case(cBrOpen K xvec1 xvec2 y N' P')
      from \<open>bn(\<exclamdown>K\<lparr>\<nu>*(xvec1@y#xvec2)\<rparr>\<langle>N'\<rangle>) \<sharp>* (M, N)\<close> have "y \<sharp> N" by simp+
      from \<open>\<Psi> \<rhd> M\<langle>N\<rangle>.P \<longmapsto>\<exclamdown>K\<lparr>\<nu>*(xvec1@xvec2)\<rparr>\<langle>([(x, y)] \<bullet> N')\<rangle> \<prec> ([(x, y)] \<bullet> P')\<close>
      have "N = ([(x, y)] \<bullet> N')"
        apply -
        by(ind_cases "\<Psi> \<rhd> M\<langle>N\<rangle>.P \<longmapsto>\<exclamdown>K\<lparr>\<nu>*(xvec1@xvec2)\<rparr>\<langle>([(x, y)] \<bullet> N')\<rangle> \<prec> ([(x, y)] \<bullet> P')")
          (auto simp add: residualInject psi.inject)
      with \<open>x \<sharp> N\<close> \<open>y \<sharp> N\<close> \<open>x \<noteq> y\<close> have "N = N'"
        by(subst pt_bij[OF pt_name_inst, OF at_name_inst, symmetric, where pi="[(x, y)]"])
          (simp add: fresh_left calc_atm)
      with \<open>y \<in> supp N'\<close> \<open>y \<sharp> N\<close> have False by(simp add: fresh_def)
      then show ?case by simp
    next
      case(cRes P')
      from \<open>\<Psi> \<rhd> M\<langle>N\<rangle>.P \<longmapsto>\<alpha> \<prec> P'\<close> show ?case
      proof(induct rule: outputCases)
        case(cOutput K)
        from \<open>\<Psi> \<turnstile> M \<leftrightarrow> K\<close> have "\<Psi> \<rhd> M\<langle>N\<rangle>.(\<lparr>\<nu>x\<rparr>P) \<longmapsto>K\<langle>N\<rangle> \<prec> \<lparr>\<nu>x\<rparr>P"
          by(rule Output)
        moreover have "(\<Psi>, \<lparr>\<nu>x\<rparr>P, \<lparr>\<nu>x\<rparr>P) \<in> Rel" by(rule C1)
        ultimately show ?case by force
      next
        case(cBrOutput K)
        from \<open>\<Psi> \<turnstile> M \<preceq> K\<close> have "\<Psi> \<rhd> M\<langle>N\<rangle>.(\<lparr>\<nu>x\<rparr>P) \<longmapsto>\<exclamdown>K\<langle>N\<rangle> \<prec> \<lparr>\<nu>x\<rparr>P"
          by(rule BrOutput)
        moreover have "(\<Psi>, \<lparr>\<nu>x\<rparr>P, \<lparr>\<nu>x\<rparr>P) \<in> Rel" by(rule C1)
        ultimately show ?case by force
      qed
    next
      case(cBrClose K xvec N' P')
      from \<open>\<Psi> \<rhd> M\<langle>N\<rangle>.P \<longmapsto> \<exclamdown>K\<lparr>\<nu>*xvec\<rparr>\<langle>N'\<rangle> \<prec> P'\<close>
      have "\<Psi> \<turnstile> M \<preceq> the(subject(\<exclamdown>K\<lparr>\<nu>*xvec\<rparr>\<langle>N'\<rangle>))"
        by(rule brOutputOutputCases) simp
      then have "\<Psi> \<turnstile> M \<preceq> K" by simp
      then have "supp K \<subseteq> (supp M:: name set)" by(rule chanOutConSupp)
      then have False using \<open>x \<in> supp K\<close> \<open>x \<sharp> M\<close> unfolding fresh_def
        by blast
      then show ?case by(rule FalseE)
    qed
  qed
qed

lemma casePushResLeft:
  fixes \<Psi>  :: 'b
    and x  :: name
    and Cs :: "('c \<times> ('a, 'b, 'c) psi) list"

assumes "eqvt Rel"
  and   "x \<sharp> \<Psi>"
  and   "x \<sharp> map fst Cs"
  and   C1: "\<And>Q. (\<Psi>, Q, Q) \<in> Rel"

shows "\<Psi> \<rhd> \<lparr>\<nu>x\<rparr>(Cases Cs) \<leadsto>[Rel] Cases (map (\<lambda>(\<phi>, P). (\<phi>, \<lparr>\<nu>x\<rparr>P)) Cs)"
proof -
  note \<open>eqvt Rel\<close> \<open>x \<sharp> \<Psi>\<close>
  moreover have "x \<sharp> \<lparr>\<nu>x\<rparr>(Cases Cs)" by(simp add: abs_fresh)
  moreover from \<open>x \<sharp> map fst Cs\<close> have "x \<sharp> Cases (map (\<lambda>(\<phi>, P). (\<phi>, \<lparr>\<nu>x\<rparr>P)) Cs)"
    by(induct Cs) (auto simp add: abs_fresh)
  ultimately show ?thesis
  proof(induct rule: simIFresh[of _ _ _ _ _ Cs])
    case(cSim \<alpha> P'')
    from \<open>\<Psi> \<rhd> Cases (map (\<lambda>(\<phi>, P). (\<phi>, \<lparr>\<nu>x\<rparr>P)) Cs) \<longmapsto>\<alpha> \<prec> P''\<close>
    show ?case
    proof(induct rule: caseCases)
      case(cCase \<phi> P')
      from \<open>(\<phi>, P') \<in> set (map (\<lambda>(\<phi>, P). (\<phi>, \<lparr>\<nu>x\<rparr>P)) Cs)\<close>
      obtain P where "(\<phi>, P) \<in> set Cs" and "P' = \<lparr>\<nu>x\<rparr>P"
        by(induct Cs) auto
      from \<open>guarded P'\<close> \<open>P' = \<lparr>\<nu>x\<rparr>P\<close> have "guarded P" by simp
      from \<open>\<Psi> \<rhd> P' \<longmapsto>\<alpha> \<prec> P''\<close> \<open>P' = \<lparr>\<nu>x\<rparr>P\<close> have "\<Psi> \<rhd> \<lparr>\<nu>x\<rparr>P \<longmapsto>\<alpha> \<prec> P''"
        by simp
      moreover note \<open>x \<sharp> \<Psi>\<close> \<open>x \<sharp> \<alpha>\<close> \<open>x \<sharp> P''\<close> \<open>bn \<alpha> \<sharp>* \<Psi>\<close>
      moreover from \<open>bn \<alpha> \<sharp>* Cs\<close> \<open>(\<phi>, P) \<in> set Cs\<close>
      have "bn \<alpha> \<sharp>* P" by(auto dest: memFreshChain)
      ultimately show ?case using \<open>bn \<alpha> \<sharp>* subject \<alpha>\<close> \<open>x \<sharp> \<alpha>\<close> \<open>bn \<alpha> \<sharp>* Cs\<close>
      proof(induct rule: resCases[where C="()"])
        case(cOpen M xvec1 xvec2 y N P')
        from \<open>x \<sharp> M\<lparr>\<nu>*(xvec1@y#xvec2)\<rparr>\<langle>N\<rangle>\<close> have "x \<sharp> xvec1" and "x \<sharp> xvec2" and "x \<sharp> M" by simp+
        from \<open>bn(M\<lparr>\<nu>*(xvec1@y#xvec2)\<rparr>\<langle>N\<rangle>) \<sharp>* Cs\<close> have "y \<sharp> Cs" by simp
        from \<open>\<Psi> \<rhd> P \<longmapsto>M\<lparr>\<nu>*(xvec1@xvec2)\<rparr>\<langle>([(x, y)] \<bullet> N)\<rangle> \<prec> ([(x, y)] \<bullet> P')\<close> \<open>(\<phi>, P) \<in> set Cs\<close> \<open>\<Psi> \<turnstile> \<phi>\<close> \<open>guarded P\<close>
        have "\<Psi> \<rhd> Cases Cs \<longmapsto>M\<lparr>\<nu>*(xvec1@xvec2)\<rparr>\<langle>([(x, y)] \<bullet> N)\<rangle> \<prec> ([(x, y)] \<bullet> P')" by(rule Case)
        then have "([(x, y)] \<bullet> \<Psi>) \<rhd> ([(x, y)] \<bullet> (Cases Cs))  \<longmapsto>([(x, y)] \<bullet> (M\<lparr>\<nu>*(xvec1@xvec2)\<rparr>\<langle>([(x, y)] \<bullet> N)\<rangle> \<prec> ([(x, y)] \<bullet> P')))"
          by(rule semantics.eqvt)
        with \<open>x \<sharp> \<Psi>\<close> \<open>x \<sharp> M\<close> \<open>y \<sharp> xvec1\<close> \<open>y \<sharp> xvec2\<close> \<open>y \<sharp> \<Psi>\<close> \<open>y \<sharp> M\<close> \<open>x \<sharp> xvec1\<close> \<open>x \<sharp> xvec2\<close>
        have "\<Psi> \<rhd> ([(x, y)] \<bullet> (Cases Cs))  \<longmapsto>M\<lparr>\<nu>*(xvec1@xvec2)\<rparr>\<langle>N\<rangle> \<prec> P'" by(simp add: eqvts)
        then have "\<Psi> \<rhd> \<lparr>\<nu>y\<rparr>([(x, y)] \<bullet> (Cases Cs))  \<longmapsto>M\<lparr>\<nu>*(xvec1@y#xvec2)\<rparr>\<langle>N\<rangle> \<prec> P'" using \<open>y \<in> supp N\<close> \<open>y \<sharp> \<Psi>\<close> \<open>y \<sharp> M\<close> \<open>y \<sharp> xvec1\<close> \<open>y \<sharp> xvec2\<close>
          by(rule Open)
        then have "\<Psi> \<rhd> \<lparr>\<nu>x\<rparr>(Cases Cs)  \<longmapsto>M\<lparr>\<nu>*(xvec1@y#xvec2)\<rparr>\<langle>N\<rangle> \<prec> P'" using \<open>y \<sharp> Cs\<close>
          by(simp add: alphaRes)
        moreover have "(\<Psi>, P', P') \<in> Rel" by(rule C1)
        ultimately show ?case by blast
      next
        case(cBrOpen M xvec1 xvec2 y N P')
        from \<open>x \<sharp> \<exclamdown>M\<lparr>\<nu>*(xvec1@y#xvec2)\<rparr>\<langle>N\<rangle>\<close> have "x \<sharp> xvec1" and "x \<sharp> xvec2" and "x \<sharp> M" by simp+
        from \<open>bn(\<exclamdown>M\<lparr>\<nu>*(xvec1@y#xvec2)\<rparr>\<langle>N\<rangle>) \<sharp>* Cs\<close> have "y \<sharp> Cs" by simp
        from \<open>\<Psi> \<rhd> P \<longmapsto>\<exclamdown>M\<lparr>\<nu>*(xvec1@xvec2)\<rparr>\<langle>([(x, y)] \<bullet> N)\<rangle> \<prec> ([(x, y)] \<bullet> P')\<close> \<open>(\<phi>, P) \<in> set Cs\<close> \<open>\<Psi> \<turnstile> \<phi>\<close> \<open>guarded P\<close>
        have "\<Psi> \<rhd> Cases Cs \<longmapsto>\<exclamdown>M\<lparr>\<nu>*(xvec1@xvec2)\<rparr>\<langle>([(x, y)] \<bullet> N)\<rangle> \<prec> ([(x, y)] \<bullet> P')" by(rule Case)
        then have "([(x, y)] \<bullet> \<Psi>) \<rhd> ([(x, y)] \<bullet> (Cases Cs))  \<longmapsto>([(x, y)] \<bullet> (\<exclamdown>M\<lparr>\<nu>*(xvec1@xvec2)\<rparr>\<langle>([(x, y)] \<bullet> N)\<rangle> \<prec> ([(x, y)] \<bullet> P')))"
          by(rule semantics.eqvt)
        with \<open>x \<sharp> \<Psi>\<close> \<open>x \<sharp> M\<close> \<open>y \<sharp> xvec1\<close> \<open>y \<sharp> xvec2\<close> \<open>y \<sharp> \<Psi>\<close> \<open>y \<sharp> M\<close> \<open>x \<sharp> xvec1\<close> \<open>x \<sharp> xvec2\<close>
        have "\<Psi> \<rhd> ([(x, y)] \<bullet> (Cases Cs))  \<longmapsto>\<exclamdown>M\<lparr>\<nu>*(xvec1@xvec2)\<rparr>\<langle>N\<rangle> \<prec> P'" by(simp add: eqvts)
        then have "\<Psi> \<rhd> \<lparr>\<nu>y\<rparr>([(x, y)] \<bullet> (Cases Cs))  \<longmapsto>\<exclamdown>M\<lparr>\<nu>*(xvec1@y#xvec2)\<rparr>\<langle>N\<rangle> \<prec> P'" using \<open>y \<in> supp N\<close> \<open>y \<sharp> \<Psi>\<close> \<open>y \<sharp> M\<close> \<open>y \<sharp> xvec1\<close> \<open>y \<sharp> xvec2\<close>
          by(rule BrOpen)
        then have "\<Psi> \<rhd> \<lparr>\<nu>x\<rparr>(Cases Cs)  \<longmapsto>\<exclamdown>M\<lparr>\<nu>*(xvec1@y#xvec2)\<rparr>\<langle>N\<rangle> \<prec> P'" using \<open>y \<sharp> Cs\<close>
          by(simp add: alphaRes)
        moreover have "(\<Psi>, P', P') \<in> Rel" by(rule C1)
        ultimately show ?case by blast
      next
        case(cRes P')
        from \<open>\<Psi> \<rhd> P \<longmapsto>\<alpha> \<prec> P'\<close> \<open>(\<phi>, P) \<in> set Cs\<close> \<open>\<Psi> \<turnstile> \<phi>\<close> \<open>guarded P\<close>
        have "\<Psi> \<rhd> Cases Cs \<longmapsto>\<alpha> \<prec> P'" by(rule Case)
        then have "\<Psi> \<rhd> \<lparr>\<nu>x\<rparr>(Cases Cs) \<longmapsto>\<alpha> \<prec> \<lparr>\<nu>x\<rparr>P'" using \<open>x \<sharp> \<Psi>\<close> \<open>x \<sharp> \<alpha>\<close>
          by(rule Scope)
        moreover have "(\<Psi>, \<lparr>\<nu>x\<rparr>P', \<lparr>\<nu>x\<rparr>P') \<in> Rel" by(rule C1)
        ultimately show ?case by blast
      next
        case(cBrClose M xvec N P')
        from \<open>\<Psi> \<rhd> P \<longmapsto> \<exclamdown>M\<lparr>\<nu>*xvec\<rparr>\<langle>N\<rangle> \<prec> P'\<close> \<open>x \<in> supp M\<close> \<open>x \<sharp> \<Psi>\<close>
        have "\<Psi> \<rhd> \<lparr>\<nu>x\<rparr>P \<longmapsto> \<tau> \<prec> \<lparr>\<nu>x\<rparr>(\<lparr>\<nu>*xvec\<rparr>P')"
          by(rule BrClose)
        from \<open>\<Psi> \<rhd> P \<longmapsto> \<exclamdown>M\<lparr>\<nu>*xvec\<rparr>\<langle>N\<rangle> \<prec> P'\<close> \<open>(\<phi>, P) \<in> set Cs\<close> \<open>\<Psi> \<turnstile> \<phi>\<close> \<open>guarded P\<close>
        have "\<Psi> \<rhd> Cases Cs \<longmapsto> \<exclamdown>M\<lparr>\<nu>*xvec\<rparr>\<langle>N\<rangle> \<prec> P'"
          by(rule Case)
        then have "\<Psi> \<rhd> \<lparr>\<nu>x\<rparr>(Cases Cs) \<longmapsto> \<tau> \<prec> \<lparr>\<nu>x\<rparr>(\<lparr>\<nu>*xvec\<rparr>P')" using \<open>x \<in> supp M\<close> \<open>x \<sharp> \<Psi>\<close>
          by(rule BrClose)
        moreover have "(\<Psi>,\<lparr>\<nu>x\<rparr>(\<lparr>\<nu>*xvec\<rparr>P'),\<lparr>\<nu>x\<rparr>(\<lparr>\<nu>*xvec\<rparr>P')) \<in> Rel" by fact
        ultimately show ?case by blast
      qed
    qed
  qed
qed

lemma casePushResRight:
  fixes \<Psi>  :: 'b
    and x  :: name
    and Cs :: "('c \<times> ('a, 'b, 'c) psi) list"

assumes "eqvt Rel"
  and   "x \<sharp> \<Psi>"
  and   "x \<sharp> map fst Cs"
  and   C1: "\<And>Q. (\<Psi>, Q, Q) \<in> Rel"

shows "\<Psi> \<rhd> Cases (map (\<lambda>(\<phi>, P). (\<phi>, \<lparr>\<nu>x\<rparr>P)) Cs) \<leadsto>[Rel] \<lparr>\<nu>x\<rparr>(Cases Cs)"
proof -
  note \<open>eqvt Rel\<close> \<open>x \<sharp> \<Psi>\<close>
  moreover from \<open>x \<sharp> map fst Cs\<close> have "x \<sharp> Cases (map (\<lambda>(\<phi>, P). (\<phi>, \<lparr>\<nu>x\<rparr>P)) Cs)"
    by(induct Cs) (auto simp add: abs_fresh)
  moreover have "x \<sharp> \<lparr>\<nu>x\<rparr>(Cases Cs)" by(simp add: abs_fresh)
  ultimately show ?thesis
  proof(induct rule: simIFresh[of _ _ _ _ _ Cs])
    case(cSim \<alpha> P'')
    note \<open>\<Psi> \<rhd> \<lparr>\<nu>x\<rparr>(Cases Cs) \<longmapsto>\<alpha> \<prec> P''\<close> \<open>x \<sharp> \<Psi>\<close> \<open>x \<sharp> \<alpha>\<close> \<open>x \<sharp> P''\<close> \<open>bn \<alpha> \<sharp>* \<Psi>\<close>
    moreover from \<open>bn \<alpha> \<sharp>* \<lparr>\<nu>x\<rparr>(Cases Cs)\<close> \<open>x \<sharp> \<alpha>\<close> have "bn \<alpha> \<sharp>* (Cases Cs)" by simp
    ultimately show ?case using \<open>bn \<alpha> \<sharp>* subject \<alpha>\<close> \<open>x \<sharp> \<alpha>\<close> \<open>bn \<alpha> \<sharp>* Cs\<close>
    proof(induct rule: resCases[where C="()"])
      case(cOpen M xvec1 xvec2 y N P')
      from \<open>x \<sharp> M\<lparr>\<nu>*(xvec1@y#xvec2)\<rparr>\<langle>N\<rangle>\<close> have "x \<sharp> xvec1" and "x \<sharp> xvec2" and "x \<sharp> M" by simp+
      from \<open>bn(M\<lparr>\<nu>*(xvec1@y#xvec2)\<rparr>\<langle>N\<rangle>) \<sharp>* Cs\<close> have "y \<sharp> Cs" by simp
      from \<open>\<Psi> \<rhd> Cases Cs \<longmapsto>M\<lparr>\<nu>*(xvec1@xvec2)\<rparr>\<langle>([(x, y)] \<bullet> N)\<rangle> \<prec> ([(x, y)] \<bullet> P')\<close>
      show ?case
      proof(induct rule: caseCases)
        case(cCase \<phi> P)
        from \<open>\<Psi> \<rhd> P \<longmapsto>M\<lparr>\<nu>*(xvec1@xvec2)\<rparr>\<langle>([(x, y)] \<bullet> N)\<rangle> \<prec> ([(x, y)] \<bullet> P')\<close>
        have "([(x, y)] \<bullet> \<Psi>) \<rhd> ([(x, y)] \<bullet> P)  \<longmapsto>([(x, y)] \<bullet> (M\<lparr>\<nu>*(xvec1@xvec2)\<rparr>\<langle>([(x, y)] \<bullet> N)\<rangle> \<prec> ([(x, y)] \<bullet> P')))"
          by(rule semantics.eqvt)
        with \<open>x \<sharp> \<Psi>\<close> \<open>x \<sharp> M\<close> \<open>y \<sharp> xvec1\<close> \<open>y \<sharp> xvec2\<close> \<open>y \<sharp> \<Psi>\<close> \<open>y \<sharp> M\<close> \<open>x \<sharp> xvec1\<close> \<open>x \<sharp> xvec2\<close>
        have "\<Psi> \<rhd> ([(x, y)] \<bullet> P)  \<longmapsto>M\<lparr>\<nu>*(xvec1@xvec2)\<rparr>\<langle>N\<rangle> \<prec> P'" by(simp add: eqvts)
        then have "\<Psi> \<rhd> \<lparr>\<nu>y\<rparr>([(x, y)] \<bullet> P)  \<longmapsto>M\<lparr>\<nu>*(xvec1@y#xvec2)\<rparr>\<langle>N\<rangle> \<prec> P'" using \<open>y \<in> supp N\<close> \<open>y \<sharp> \<Psi>\<close> \<open>y \<sharp> M\<close> \<open>y \<sharp> xvec1\<close> \<open>y \<sharp> xvec2\<close>
          by(rule Open)
        then have "\<Psi> \<rhd> \<lparr>\<nu>x\<rparr>P  \<longmapsto>M\<lparr>\<nu>*(xvec1@y#xvec2)\<rparr>\<langle>N\<rangle> \<prec> P'" using \<open>y \<sharp> Cs\<close> \<open>(\<phi>, P) \<in> set Cs\<close>
          by(subst alphaRes, auto dest: memFresh)
        moreover from \<open>(\<phi>, P) \<in> set Cs\<close> have "(\<phi>, \<lparr>\<nu>x\<rparr>P) \<in> set (map (\<lambda>(\<phi>, P). (\<phi>, \<lparr>\<nu>x\<rparr>P)) Cs)"
          by(induct Cs) auto
        moreover note \<open>\<Psi> \<turnstile> \<phi>\<close>
        moreover from \<open>guarded P\<close> have "guarded(\<lparr>\<nu>x\<rparr>P)" by simp
        ultimately have "\<Psi> \<rhd> (Cases (map (\<lambda>(\<phi>, P). (\<phi>, \<lparr>\<nu>x\<rparr>P)) Cs)) \<longmapsto>M\<lparr>\<nu>*(xvec1@y#xvec2)\<rparr>\<langle>N\<rangle> \<prec> P'"
          by(rule Case)
        moreover have "(\<Psi>, P', P') \<in> Rel" by(rule C1)
        ultimately show ?case by blast
      qed
    next
      case(cBrOpen M xvec1 xvec2 y N P')
      from \<open>x \<sharp> \<exclamdown>M\<lparr>\<nu>*(xvec1@y#xvec2)\<rparr>\<langle>N\<rangle>\<close> have "x \<sharp> xvec1" and "x \<sharp> xvec2" and "x \<sharp> M" by simp+
      from \<open>bn(\<exclamdown>M\<lparr>\<nu>*(xvec1@y#xvec2)\<rparr>\<langle>N\<rangle>) \<sharp>* Cs\<close> have "y \<sharp> Cs" by simp
      from \<open>\<Psi> \<rhd> Cases Cs \<longmapsto>\<exclamdown>M\<lparr>\<nu>*(xvec1@xvec2)\<rparr>\<langle>([(x, y)] \<bullet> N)\<rangle> \<prec> ([(x, y)] \<bullet> P')\<close>
      show ?case
      proof(induct rule: caseCases)
        case(cCase \<phi> P)
        from \<open>\<Psi> \<rhd> P \<longmapsto>\<exclamdown>M\<lparr>\<nu>*(xvec1@xvec2)\<rparr>\<langle>([(x, y)] \<bullet> N)\<rangle> \<prec> ([(x, y)] \<bullet> P')\<close>
        have "([(x, y)] \<bullet> \<Psi>) \<rhd> ([(x, y)] \<bullet> P) \<longmapsto>([(x, y)] \<bullet> (\<exclamdown>M\<lparr>\<nu>*(xvec1@xvec2)\<rparr>\<langle>([(x, y)] \<bullet> N)\<rangle> \<prec> ([(x, y)] \<bullet> P')))"
          by(rule semantics.eqvt)
        with \<open>x \<sharp> \<Psi>\<close> \<open>x \<sharp> M\<close> \<open>y \<sharp> xvec1\<close> \<open>y \<sharp> xvec2\<close> \<open>y \<sharp> \<Psi>\<close> \<open>y \<sharp> M\<close> \<open>x \<sharp> xvec1\<close> \<open>x \<sharp> xvec2\<close>
        have "\<Psi> \<rhd> ([(x, y)] \<bullet> P)  \<longmapsto>\<exclamdown>M\<lparr>\<nu>*(xvec1@xvec2)\<rparr>\<langle>N\<rangle> \<prec> P'" by(simp add: eqvts)
        then have "\<Psi> \<rhd> \<lparr>\<nu>y\<rparr>([(x, y)] \<bullet> P)  \<longmapsto>\<exclamdown>M\<lparr>\<nu>*(xvec1@y#xvec2)\<rparr>\<langle>N\<rangle> \<prec> P'" using \<open>y \<in> supp N\<close> \<open>y \<sharp> \<Psi>\<close> \<open>y \<sharp> M\<close> \<open>y \<sharp> xvec1\<close> \<open>y \<sharp> xvec2\<close>
          by(rule BrOpen)
        then have "\<Psi> \<rhd> \<lparr>\<nu>x\<rparr>P \<longmapsto>\<exclamdown>M\<lparr>\<nu>*(xvec1@y#xvec2)\<rparr>\<langle>N\<rangle> \<prec> P'" using \<open>y \<sharp> Cs\<close> \<open>(\<phi>, P) \<in> set Cs\<close>
          by(subst alphaRes, auto dest: memFresh)
        moreover from \<open>(\<phi>, P) \<in> set Cs\<close> have "(\<phi>, \<lparr>\<nu>x\<rparr>P) \<in> set (map (\<lambda>(\<phi>, P). (\<phi>, \<lparr>\<nu>x\<rparr>P)) Cs)"
          by(induct Cs) auto
        moreover note \<open>\<Psi> \<turnstile> \<phi>\<close>
        moreover from \<open>guarded P\<close> have "guarded(\<lparr>\<nu>x\<rparr>P)" by simp
        ultimately have "\<Psi> \<rhd> (Cases (map (\<lambda>(\<phi>, P). (\<phi>, \<lparr>\<nu>x\<rparr>P)) Cs)) \<longmapsto>\<exclamdown>M\<lparr>\<nu>*(xvec1@y#xvec2)\<rparr>\<langle>N\<rangle> \<prec> P'"
          by(rule Case)
        moreover have "(\<Psi>, P', P') \<in> Rel" by(rule C1)
        ultimately show ?case by blast
      qed
    next
      case(cRes P')
      from \<open>\<Psi> \<rhd> Cases Cs \<longmapsto>\<alpha> \<prec> P'\<close>
      show ?case
      proof(induct rule: caseCases)
        case(cCase \<phi> P)
        from \<open>\<Psi> \<rhd> P \<longmapsto>\<alpha> \<prec> P'\<close> \<open>x \<sharp> \<Psi>\<close> \<open>x \<sharp> \<alpha>\<close>
        have "\<Psi> \<rhd> \<lparr>\<nu>x\<rparr>P \<longmapsto>\<alpha> \<prec> \<lparr>\<nu>x\<rparr>P'" by(rule Scope)
        moreover from \<open>(\<phi>, P) \<in> set Cs\<close> have "(\<phi>, \<lparr>\<nu>x\<rparr>P) \<in> set (map (\<lambda>(\<phi>, P). (\<phi>, \<lparr>\<nu>x\<rparr>P)) Cs)"
          by(induct Cs) auto
        moreover note \<open>\<Psi> \<turnstile> \<phi>\<close>
        moreover from \<open>guarded P\<close> have "guarded(\<lparr>\<nu>x\<rparr>P)" by simp
        ultimately have "\<Psi> \<rhd> (Cases (map (\<lambda>(\<phi>, P). (\<phi>, \<lparr>\<nu>x\<rparr>P)) Cs)) \<longmapsto>\<alpha> \<prec> \<lparr>\<nu>x\<rparr>P'"
          by(rule Case)
        moreover have "(\<Psi>, \<lparr>\<nu>x\<rparr>P', \<lparr>\<nu>x\<rparr>P') \<in> Rel" by(rule C1)
        ultimately show ?case by blast
      qed
    next
      case(cBrClose M xvec N P')
      then show ?case
      proof(induct rule: caseCases)
        case(cCase \<phi> P)
        from \<open>\<Psi> \<rhd> P \<longmapsto>\<exclamdown>M\<lparr>\<nu>*xvec\<rparr>\<langle>N\<rangle> \<prec> P'\<close> \<open>x \<sharp> \<Psi>\<close> \<open>x \<in> supp M\<close>
        have "\<Psi> \<rhd> \<lparr>\<nu>x\<rparr>P \<longmapsto> \<tau> \<prec> \<lparr>\<nu>x\<rparr>(\<lparr>\<nu>*xvec\<rparr>P')"
          by(intro BrClose)
        moreover from \<open>(\<phi>, P) \<in> set Cs\<close> have "(\<phi>, \<lparr>\<nu>x\<rparr>P) \<in> set (map (\<lambda>(\<phi>, P). (\<phi>, \<lparr>\<nu>x\<rparr>P)) Cs)"
          by(induct Cs) auto
        moreover from \<open>guarded P\<close> have "guarded(\<lparr>\<nu>x\<rparr>P)" by simp
        moreover note \<open>\<Psi> \<turnstile> \<phi>\<close>
        ultimately have "\<Psi> \<rhd> Cases map (\<lambda>(\<phi>, P). (\<phi>, \<lparr>\<nu>x\<rparr>P)) Cs \<longmapsto> \<tau> \<prec> \<lparr>\<nu>x\<rparr>(\<lparr>\<nu>*xvec\<rparr>P')"
          by(intro Case)
        moreover have "(\<Psi>,\<lparr>\<nu>x\<rparr>(\<lparr>\<nu>*xvec\<rparr>P'),\<lparr>\<nu>x\<rparr>(\<lparr>\<nu>*xvec\<rparr>P')) \<in> Rel"
          by fact
        ultimately show ?case
          by blast
      qed
    qed
  qed
qed

lemma resInputCases[consumes 5, case_names cRes]:
  fixes \<Psi>    :: 'b
    and x    :: name
    and P    :: "('a, 'b, 'c) psi"
    and M    :: 'a
    and N    :: 'a
    and P'   :: "('a, 'b, 'c) psi"
    and C    :: "'d::fs_name"

assumes Trans: "\<Psi> \<rhd> \<lparr>\<nu>x\<rparr>P \<longmapsto>M\<lparr>N\<rparr> \<prec> P'"
  and   "x \<sharp> \<Psi>"
  and   "x \<sharp> M"
  and   "x \<sharp> N"
  and   "x \<sharp> P'"
  and   rScope:  "\<And>P'. \<lbrakk>\<Psi> \<rhd> P \<longmapsto>M\<lparr>N\<rparr> \<prec> P'\<rbrakk> \<Longrightarrow> Prop (\<lparr>\<nu>x\<rparr>P')"

shows "Prop P'"
proof -
  note Trans \<open>x \<sharp> \<Psi>\<close>
  moreover from \<open>x \<sharp> M\<close> \<open>x \<sharp> N\<close> have "x \<sharp> M\<lparr>N\<rparr>" by simp
  moreover note \<open>x \<sharp> P'\<close>
  ultimately show ?thesis using assms
    by(induct rule: resInputCases') simp
qed

lemma resBrInputCases[consumes 5, case_names cRes]:
  fixes \<Psi>    :: 'b
    and x    :: name
    and P    :: "('a, 'b, 'c) psi"
    and M    :: 'a
    and N    :: 'a
    and P'   :: "('a, 'b, 'c) psi"
    and C    :: "'d::fs_name"

assumes Trans: "\<Psi> \<rhd> \<lparr>\<nu>x\<rparr>P \<longmapsto>\<questiondown>M\<lparr>N\<rparr> \<prec> P'"
  and   "x \<sharp> \<Psi>"
  and   "x \<sharp> M"
  and   "x \<sharp> N"
  and   "x \<sharp> P'"
  and   rScope:  "\<And>P'. \<lbrakk>\<Psi> \<rhd> P \<longmapsto>\<questiondown>M\<lparr>N\<rparr> \<prec> P'\<rbrakk> \<Longrightarrow> Prop (\<lparr>\<nu>x\<rparr>P')"

shows "Prop P'"
proof -
  note Trans \<open>x \<sharp> \<Psi>\<close>
  moreover from \<open>x \<sharp> M\<close> \<open>x \<sharp> N\<close> have "x \<sharp> \<questiondown>M\<lparr>N\<rparr>" by simp
  moreover note \<open>x \<sharp> P'\<close>
  ultimately show ?thesis using assms
    by(induct rule: resBrInputCases') simp
qed

lemma swap_supp:
  fixes x   :: name
    and y   :: name
    and N   :: 'a

assumes "y \<in> supp N"

shows "x \<in> supp ([(x, y)] \<bullet> N)"
  using assms
  by (metis fresh_bij fresh_def swap_simps(2))

lemma swap_supp':
  fixes x   :: name
    and y   :: name
    and N   :: 'a

assumes "x \<in> supp N"

shows "y \<in> supp ([(x, y)] \<bullet> N)"
  using assms
  by (metis fresh_bij fresh_def swap_simps(1))

lemma brOutputFreshSubjectChain:
  fixes \<Psi>   :: 'b
    and Q   :: "('a, 'b, 'c) psi"
    and M   :: 'a
    and xvec :: "name list"
    and N   :: 'a
    and Q'  :: "('a, 'b, 'c) psi"
    and yvec :: "name list"

assumes "\<Psi> \<rhd> Q \<longmapsto> \<exclamdown>M\<lparr>\<nu>*xvec\<rparr>\<langle>N\<rangle> \<prec> Q'"
  and "xvec \<sharp>* M"
  and "yvec \<sharp>* Q"

shows "yvec \<sharp>* M"
  using assms
proof(induct yvec)
  case Nil
  then show ?case by simp
next
  case(Cons a yvec)
  then have "yvec \<sharp>* M" by simp
  from \<open>(a # yvec) \<sharp>* Q\<close> have "a \<sharp> Q" by simp
  from \<open>xvec \<sharp>* M\<close> \<open>a \<sharp> Q\<close> \<open>\<Psi> \<rhd> Q \<longmapsto> \<exclamdown>M\<lparr>\<nu>*xvec\<rparr>\<langle>N\<rangle> \<prec> Q'\<close>
  have "a \<sharp> M"
    by(simp add: brOutputFreshSubject)
  with \<open>yvec \<sharp>* M\<close> show ?case
    by simp
qed

lemma scopeExtLeft:
  fixes x   :: name
    and P   :: "('a, 'b, 'c) psi"
    and \<Psi>   :: 'b
    and Q   :: "('a, 'b, 'c) psi"
    and Rel :: "('b \<times> ('a, 'b, 'c) psi \<times> ('a, 'b, 'c) psi) set"

assumes "x \<sharp> P"
  and   "x \<sharp> \<Psi>"
  and   "eqvt Rel"
  and   C1: "\<And>\<Psi>' R. (\<Psi>', R, R) \<in> Rel"
  and   C2: "\<And>y \<Psi>' R S zvec. \<lbrakk>y \<sharp> \<Psi>'; y \<sharp> R; zvec \<sharp>* \<Psi>'\<rbrakk> \<Longrightarrow> (\<Psi>', \<lparr>\<nu>y\<rparr>(\<lparr>\<nu>*zvec\<rparr>(R \<parallel> S)), \<lparr>\<nu>*zvec\<rparr>(R \<parallel> \<lparr>\<nu>y\<rparr>S)) \<in> Rel"
  and   C3: "\<And>\<Psi>' zvec R y. \<lbrakk>y \<sharp> \<Psi>'; zvec \<sharp>* \<Psi>'\<rbrakk> \<Longrightarrow> (\<Psi>', \<lparr>\<nu>y\<rparr>(\<lparr>\<nu>*zvec\<rparr>R), \<lparr>\<nu>*zvec\<rparr>(\<lparr>\<nu>y\<rparr>R)) \<in> Rel"
  \<comment> \<open>Addition for Broadcast\<close>
  and   C4: "\<And>\<Psi>' R S zvec. \<lbrakk>zvec \<sharp>* R; zvec \<sharp>* \<Psi>'\<rbrakk> \<Longrightarrow> (\<Psi>', (\<lparr>\<nu>*zvec\<rparr>(R \<parallel> S)), (R \<parallel> (\<lparr>\<nu>*zvec\<rparr>S))) \<in> Rel"

shows "\<Psi> \<rhd> \<lparr>\<nu>x\<rparr>(P \<parallel> Q) \<leadsto>[Rel] P \<parallel> \<lparr>\<nu>x\<rparr>Q"
proof -
  note \<open>eqvt Rel\<close> \<open>x \<sharp> \<Psi>\<close>
  moreover have "x \<sharp> \<lparr>\<nu>x\<rparr>(P \<parallel> Q)" by(simp add: abs_fresh)
  moreover from \<open>x \<sharp> P\<close> have "x \<sharp> P \<parallel> \<lparr>\<nu>x\<rparr>Q" by(simp add: abs_fresh)
  ultimately show ?thesis
  proof(induct rule: simIFresh[of _ _ _ _ _ x])
    case(cSim \<alpha> PQ)
    from \<open>x \<sharp> \<alpha>\<close> \<open>bn \<alpha> \<sharp>* (P \<parallel> \<lparr>\<nu>x\<rparr>Q)\<close> have "bn \<alpha> \<sharp>* Q" by simp
    note \<open>\<Psi> \<rhd> P \<parallel> \<lparr>\<nu>x\<rparr>Q \<longmapsto>\<alpha> \<prec> PQ\<close> \<open>bn \<alpha> \<sharp>* \<Psi>\<close>
    moreover from \<open>bn \<alpha> \<sharp>* (P \<parallel> \<lparr>\<nu>x\<rparr>Q)\<close> have "bn \<alpha> \<sharp>* P" and "bn \<alpha> \<sharp>* \<lparr>\<nu>x\<rparr>Q" by simp+
    ultimately show ?case using \<open>bn \<alpha> \<sharp>* subject \<alpha>\<close> \<open>x \<sharp> PQ\<close>
    proof(induct rule: parCases[where C=x])
      case(cPar1 P' A\<^sub>Q \<Psi>\<^sub>Q)
      from \<open>x \<sharp> P' \<parallel> \<lparr>\<nu>x\<rparr>Q\<close> have "x \<sharp> P'" by simp
      have PTrans: "\<Psi> \<otimes> \<Psi>\<^sub>Q \<rhd> P \<longmapsto>\<alpha> \<prec> P'" by fact
      from \<open>extractFrame(\<lparr>\<nu>x\<rparr>Q) = \<langle>A\<^sub>Q, \<Psi>\<^sub>Q\<rangle>\<close> have FrxQ: "\<lparr>\<nu>x\<rparr>(extractFrame Q) = \<langle>A\<^sub>Q, \<Psi>\<^sub>Q\<rangle>" by simp
      then obtain y A\<^sub>Q' where A: "A\<^sub>Q = y#A\<^sub>Q'" by(cases A\<^sub>Q) auto
      with \<open>A\<^sub>Q \<sharp>* \<Psi>\<close> \<open>A\<^sub>Q \<sharp>* P\<close> \<open>A\<^sub>Q \<sharp>* \<alpha>\<close>
      have "A\<^sub>Q' \<sharp>* \<Psi>" and "A\<^sub>Q' \<sharp>* P" and "A\<^sub>Q' \<sharp>* \<alpha>"
        and "y \<sharp> \<Psi>" and "y \<sharp> P" and "y \<sharp> \<alpha>"
        by simp+
      from PTrans \<open>y \<sharp> P\<close> \<open>y \<sharp> \<alpha>\<close> \<open>bn \<alpha> \<sharp>* subject \<alpha>\<close> \<open>distinct(bn \<alpha>)\<close> have "y \<sharp> P'"
        by(auto intro: freeFreshDerivative)
      note PTrans
      moreover from A \<open>A\<^sub>Q \<sharp>* x\<close> FrxQ have "extractFrame([(y, x)] \<bullet> Q) = \<langle>A\<^sub>Q', \<Psi>\<^sub>Q\<rangle>"
        by(simp add: frame.inject alpha' fresh_list_cons eqvts)
      moreover from \<open>bn \<alpha> \<sharp>* Q\<close> have "([(y, x)] \<bullet> (bn \<alpha>)) \<sharp>* ([(y, x)] \<bullet> Q)"
        by(simp add: pt_fresh_star_bij[OF pt_name_inst, OF at_name_inst])
      with \<open>x \<sharp> \<alpha>\<close> \<open>A\<^sub>Q \<sharp>* \<alpha>\<close> A have "bn \<alpha> \<sharp>* ([(y, x)] \<bullet> Q)" by simp
      ultimately have "\<Psi> \<rhd> P \<parallel> ([(y, x)] \<bullet> Q) \<longmapsto>\<alpha> \<prec> (P' \<parallel> ([(y, x)] \<bullet> Q))"
        using \<open>A\<^sub>Q' \<sharp>* \<Psi>\<close> \<open>A\<^sub>Q' \<sharp>* P\<close> \<open>A\<^sub>Q' \<sharp>* \<alpha>\<close>
        by(rule Par1)
      then have "\<Psi> \<rhd> \<lparr>\<nu>y\<rparr>(P \<parallel> ([(y, x)] \<bullet> Q)) \<longmapsto>\<alpha> \<prec> \<lparr>\<nu>y\<rparr>(P' \<parallel> ([(y, x)] \<bullet> Q))"
        using \<open>y \<sharp> \<Psi>\<close> \<open>y \<sharp> \<alpha>\<close>
        by(rule Scope)
      then have "([(y, x)] \<bullet> \<Psi>) \<rhd> ([(y, x)] \<bullet> (\<lparr>\<nu>y\<rparr>(P \<parallel> ([(y, x)] \<bullet> Q)))) \<longmapsto>([(y, x)] \<bullet> (\<alpha> \<prec> \<lparr>\<nu>y\<rparr>(P' \<parallel> ([(y, x)] \<bullet> Q))))"
        by(rule semantics.eqvt)
      with \<open>x \<sharp> \<Psi>\<close> \<open>y \<sharp> \<Psi>\<close> \<open>x \<sharp> P\<close> \<open>y \<sharp> P\<close> \<open>x \<sharp> \<alpha>\<close> \<open>y \<sharp> \<alpha>\<close> \<open>x \<sharp> P'\<close> \<open>y \<sharp> P'\<close>
      have "\<Psi> \<rhd> \<lparr>\<nu>x\<rparr>(P \<parallel> Q) \<longmapsto>\<alpha> \<prec> \<lparr>\<nu>x\<rparr>(P' \<parallel> Q)"
        by(simp add: eqvts calc_atm)
      moreover from \<open>x \<sharp> \<Psi>\<close> \<open>x \<sharp> P'\<close> have "(\<Psi>, \<lparr>\<nu>x\<rparr>(\<lparr>\<nu>*[]\<rparr>(P' \<parallel> Q)), \<lparr>\<nu>*[]\<rparr>(P' \<parallel> \<lparr>\<nu>x\<rparr>Q)) \<in> Rel"
        by(rule C2) auto
      ultimately show ?case
        by force
    next
      case(cPar2 xQ' A\<^sub>P \<Psi>\<^sub>P)
      from \<open>A\<^sub>P \<sharp>* \<lparr>\<nu>x\<rparr>Q\<close> \<open>A\<^sub>P \<sharp>* x\<close> have "A\<^sub>P \<sharp>* Q" by simp
      note \<open>\<Psi> \<otimes> \<Psi>\<^sub>P \<rhd> \<lparr>\<nu>x\<rparr>Q \<longmapsto>\<alpha> \<prec> xQ'\<close>
      moreover have FrP: "extractFrame P = \<langle>A\<^sub>P, \<Psi>\<^sub>P\<rangle>" by fact
      with \<open>x \<sharp> P\<close> \<open>A\<^sub>P \<sharp>* x\<close> have "x \<sharp> \<Psi>\<^sub>P" and "x \<sharp> A\<^sub>P"
        by(force dest: extractFrameFresh)+
      with \<open>x \<sharp> \<Psi>\<close> have "x \<sharp> \<Psi> \<otimes> \<Psi>\<^sub>P" by force
      moreover note \<open>x \<sharp> \<alpha>\<close>
      moreover from \<open>x \<sharp> P \<parallel> xQ'\<close> have "x \<sharp> xQ'" by simp
      moreover from FrP \<open>bn \<alpha> \<sharp>* P\<close> \<open>A\<^sub>P \<sharp>* \<alpha>\<close> have "bn \<alpha> \<sharp>* \<Psi>\<^sub>P"
        by(auto dest: extractFrameFreshChain)
      with \<open>bn \<alpha> \<sharp>* \<Psi>\<close> have "bn \<alpha> \<sharp>* (\<Psi> \<otimes> \<Psi>\<^sub>P)" by force
      ultimately show ?case using \<open>bn \<alpha> \<sharp>* Q\<close> \<open>bn \<alpha> \<sharp>* subject \<alpha>\<close> \<open>x \<sharp> \<alpha>\<close> \<open>bn \<alpha> \<sharp>* P\<close> \<open>A\<^sub>P \<sharp>* \<alpha>\<close> \<open>bn \<alpha> \<sharp>* \<Psi>\<close> \<open>x \<sharp> P\<close>
      proof(induct rule: resCases'[where C="(P, A\<^sub>P, \<Psi>)"])
        case(cOpen M xvec1 xvec2 y N Q')
        from \<open>x \<sharp> M\<lparr>\<nu>*(xvec1@y#xvec2)\<rparr>\<langle>N\<rangle>\<close> have "x \<sharp> xvec1" and "x \<noteq> y" and "x \<sharp> xvec2" by simp+
        from \<open>bn(M\<lparr>\<nu>*(xvec1@y#xvec2)\<rparr>\<langle>N\<rangle>) \<sharp>* \<Psi>\<close> have "y \<sharp> \<Psi>" by simp
        note \<open>\<Psi> \<otimes> \<Psi>\<^sub>P \<rhd> ([(x, y)] \<bullet> Q) \<longmapsto>M\<lparr>\<nu>*(xvec1@xvec2)\<rparr>\<langle>N\<rangle> \<prec> Q'\<close> FrP
        moreover from \<open>bn(M\<lparr>\<nu>*(xvec1@y#xvec2)\<rparr>\<langle>N\<rangle>) \<sharp>* P\<close> have "(xvec1@xvec2) \<sharp>* P" and "y \<sharp> P" by simp+
        moreover from \<open>A\<^sub>P \<sharp>* (M\<lparr>\<nu>*(xvec1@y#xvec2)\<rparr>\<langle>N\<rangle>)\<close> have "A\<^sub>P \<sharp>* (M\<lparr>\<nu>*(xvec1@xvec2)\<rparr>\<langle>N\<rangle>)" and "y \<sharp> A\<^sub>P" by simp+
        moreover from \<open>A\<^sub>P \<sharp>* Q\<close> \<open>x \<sharp> A\<^sub>P\<close> \<open>y \<sharp> A\<^sub>P\<close> have "A\<^sub>P \<sharp>* ([(x, y)] \<bullet> Q)" by simp
        ultimately have "\<Psi> \<rhd> P \<parallel> ([(x, y)] \<bullet> Q) \<longmapsto>M\<lparr>\<nu>*(xvec1@xvec2)\<rparr>\<langle>N\<rangle> \<prec> (P \<parallel> Q')"
          using \<open>A\<^sub>P \<sharp>* \<Psi>\<close>
          by(intro Par2) (assumption | simp)+
        then have "\<Psi> \<rhd> \<lparr>\<nu>y\<rparr>(P \<parallel> ([(x, y)] \<bullet> Q)) \<longmapsto>M\<lparr>\<nu>*(xvec1@y#xvec2)\<rparr>\<langle>N\<rangle> \<prec> (P \<parallel> Q')"
          using \<open>y \<in> supp N\<close> \<open>y \<sharp> \<Psi>\<close> \<open>y \<sharp> M\<close> \<open>y \<sharp> xvec1\<close> \<open>y \<sharp> xvec2\<close>
          by(rule Open)
        with \<open>x \<sharp> P\<close> \<open>y \<sharp> P\<close> \<open>y \<sharp> Q\<close> have "\<Psi> \<rhd> \<lparr>\<nu>x\<rparr>(P \<parallel> Q) \<longmapsto>M\<lparr>\<nu>*(xvec1@y#xvec2)\<rparr>\<langle>N\<rangle> \<prec> (P \<parallel> Q')"
          by(subst alphaRes[where y=y]) (simp add: fresh_left calc_atm eqvts)+
        moreover have "(\<Psi>, P \<parallel> Q', P \<parallel> Q') \<in> Rel" by(rule C1)
        ultimately show ?case by blast
      next
        case(cBrOpen M xvec1 xvec2 y N Q')
        from \<open>x \<sharp> \<exclamdown>M\<lparr>\<nu>*(xvec1@y#xvec2)\<rparr>\<langle>N\<rangle>\<close> have "x \<sharp> xvec1" and "x \<noteq> y" and "x \<sharp> xvec2" by simp+
        from \<open>bn(\<exclamdown>M\<lparr>\<nu>*(xvec1@y#xvec2)\<rparr>\<langle>N\<rangle>) \<sharp>* \<Psi>\<close> have "y \<sharp> \<Psi>" by simp
        note \<open>\<Psi> \<otimes> \<Psi>\<^sub>P \<rhd> ([(x, y)] \<bullet> Q) \<longmapsto>\<exclamdown>M\<lparr>\<nu>*(xvec1@xvec2)\<rparr>\<langle>N\<rangle> \<prec> Q'\<close> FrP
        moreover from \<open>bn(\<exclamdown>M\<lparr>\<nu>*(xvec1@y#xvec2)\<rparr>\<langle>N\<rangle>) \<sharp>* P\<close> have "(xvec1@xvec2) \<sharp>* P" and "y \<sharp> P" by simp+
        moreover from \<open>A\<^sub>P \<sharp>* (\<exclamdown>M\<lparr>\<nu>*(xvec1@y#xvec2)\<rparr>\<langle>N\<rangle>)\<close> have "A\<^sub>P \<sharp>* (\<exclamdown>M\<lparr>\<nu>*(xvec1@xvec2)\<rparr>\<langle>N\<rangle>)" and "y \<sharp> A\<^sub>P" by simp+
        moreover from \<open>A\<^sub>P \<sharp>* Q\<close> \<open>x \<sharp> A\<^sub>P\<close> \<open>y \<sharp> A\<^sub>P\<close> have "A\<^sub>P \<sharp>* ([(x, y)] \<bullet> Q)" by simp
        ultimately have "\<Psi> \<rhd> P \<parallel> ([(x, y)] \<bullet> Q) \<longmapsto>\<exclamdown>M\<lparr>\<nu>*(xvec1@xvec2)\<rparr>\<langle>N\<rangle> \<prec> (P \<parallel> Q')"
          using \<open>A\<^sub>P \<sharp>* \<Psi>\<close>
          by(intro Par2) (assumption | simp)+
        then have "\<Psi> \<rhd> \<lparr>\<nu>y\<rparr>(P \<parallel> ([(x, y)] \<bullet> Q)) \<longmapsto>\<exclamdown>M\<lparr>\<nu>*(xvec1@y#xvec2)\<rparr>\<langle>N\<rangle> \<prec> (P \<parallel> Q')"
          using \<open>y \<in> supp N\<close> \<open>y \<sharp> \<Psi>\<close> \<open>y \<sharp> M\<close> \<open>y \<sharp> xvec1\<close> \<open>y \<sharp> xvec2\<close>
          by(rule BrOpen)
        with \<open>x \<sharp> P\<close> \<open>y \<sharp> P\<close> \<open>y \<sharp> Q\<close> have "\<Psi> \<rhd> \<lparr>\<nu>x\<rparr>(P \<parallel> Q) \<longmapsto>\<exclamdown>M\<lparr>\<nu>*(xvec1@y#xvec2)\<rparr>\<langle>N\<rangle> \<prec> (P \<parallel> Q')"
          by(subst alphaRes[where y=y]) (simp add: fresh_left calc_atm eqvts)+
        moreover have "(\<Psi>, P \<parallel> Q', P \<parallel> Q') \<in> Rel" by(rule C1)
        ultimately show ?case by blast
      next
        case(cRes Q')
        from \<open>\<Psi> \<otimes> \<Psi>\<^sub>P \<rhd> Q \<longmapsto>\<alpha> \<prec> Q'\<close> FrP \<open>bn \<alpha> \<sharp>* P\<close>
        have "\<Psi> \<rhd> P \<parallel> Q \<longmapsto>\<alpha> \<prec> (P \<parallel> Q')" using \<open>A\<^sub>P \<sharp>* \<Psi>\<close> \<open>A\<^sub>P \<sharp>* Q\<close> \<open>A\<^sub>P \<sharp>* \<alpha>\<close>
          by(rule Par2)
        then have "\<Psi> \<rhd> \<lparr>\<nu>x\<rparr>(P \<parallel> Q) \<longmapsto>\<alpha> \<prec> \<lparr>\<nu>x\<rparr>(P \<parallel> Q')" using \<open>x \<sharp> \<Psi>\<close> \<open>x \<sharp> \<alpha>\<close>
          by(rule Scope)
        moreover from \<open>x \<sharp> \<Psi>\<close> \<open>x \<sharp> P\<close> have "(\<Psi>, \<lparr>\<nu>x\<rparr>(\<lparr>\<nu>*[]\<rparr>(P \<parallel> Q')), \<lparr>\<nu>*[]\<rparr>(P \<parallel> \<lparr>\<nu>x\<rparr>Q')) \<in> Rel"
          by(rule C2) auto
        ultimately show ?case
          by force
      next
        case(cBrClose M xvec N Q')
        from \<open>xvec \<sharp>* (P, A\<^sub>P, \<Psi>)\<close>
        have "xvec \<sharp>* P" and "A\<^sub>P \<sharp>* xvec" and "xvec \<sharp>* \<Psi>"
          by simp+
        from \<open>\<Psi> \<otimes> \<Psi>\<^sub>P \<rhd> Q \<longmapsto> \<exclamdown>M\<lparr>\<nu>*xvec\<rparr>\<langle>N\<rangle> \<prec> Q'\<close> \<open>A\<^sub>P \<sharp>* Q\<close>
          \<open>xvec \<sharp>* M\<close>
        have "A\<^sub>P \<sharp>* M"
          by(simp add: brOutputFreshSubjectChain)

        from \<open>\<Psi> \<otimes> \<Psi>\<^sub>P \<rhd> Q \<longmapsto> \<exclamdown>M\<lparr>\<nu>*xvec\<rparr>\<langle>N\<rangle> \<prec> Q'\<close> \<open>xvec \<sharp>* M\<close> \<open>distinct xvec\<close> \<open>A\<^sub>P \<sharp>* Q\<close> \<open>A\<^sub>P \<sharp>* xvec\<close>
        have "A\<^sub>P \<sharp>* N" and "A\<^sub>P \<sharp>* Q'" by(simp add: broutputFreshChainDerivative)+
        from \<open>A\<^sub>P \<sharp>* M\<close> \<open>A\<^sub>P \<sharp>* xvec\<close> \<open>A\<^sub>P \<sharp>* N\<close> have "A\<^sub>P \<sharp>* (\<exclamdown>M\<lparr>\<nu>*xvec\<rparr>\<langle>N\<rangle>)"
          by simp

        from \<open>\<Psi> \<otimes> \<Psi>\<^sub>P \<rhd> Q \<longmapsto> \<exclamdown>M\<lparr>\<nu>*xvec\<rparr>\<langle>N\<rangle> \<prec> Q'\<close> \<open>extractFrame P = \<langle>A\<^sub>P, \<Psi>\<^sub>P\<rangle>\<close> \<open>xvec \<sharp>* P\<close> \<open>A\<^sub>P \<sharp>* \<Psi>\<close> \<open>A\<^sub>P \<sharp>* Q\<close> \<open>A\<^sub>P \<sharp>* (\<exclamdown>M\<lparr>\<nu>*xvec\<rparr>\<langle>N\<rangle>)\<close>
        have "\<Psi> \<rhd> P \<parallel> Q \<longmapsto> \<exclamdown>M\<lparr>\<nu>*xvec\<rparr>\<langle>N\<rangle> \<prec> P \<parallel> Q'"
          by(simp add: Par2)

        from \<open>x \<sharp> \<Psi>\<close> \<open>x \<sharp> P\<close> \<open>xvec \<sharp>* P\<close> \<open>xvec \<sharp>* \<Psi>\<close>
        have "(x#xvec) \<sharp>* P" and "(x#xvec) \<sharp>* \<Psi>" by simp+
        then have "(\<Psi>, (\<lparr>\<nu>*(x#xvec)\<rparr>(P \<parallel> Q')), P \<parallel> (\<lparr>\<nu>*(x#xvec)\<rparr>Q')) \<in> Rel"
          by(rule C4)
        then have "(\<Psi>, \<lparr>\<nu>x\<rparr>(\<lparr>\<nu>*xvec\<rparr>(P \<parallel> Q')), P \<parallel> \<lparr>\<nu>x\<rparr>(\<lparr>\<nu>*xvec\<rparr>Q')) \<in> Rel"
          by simp

        moreover from \<open>\<Psi> \<rhd> P \<parallel> Q \<longmapsto> \<exclamdown>M\<lparr>\<nu>*xvec\<rparr>\<langle>N\<rangle> \<prec> P \<parallel> Q'\<close> \<open>x \<in> supp M\<close> \<open>x \<sharp> \<Psi>\<close>
        have "\<Psi> \<rhd> \<lparr>\<nu>x\<rparr>(P \<parallel> Q) \<longmapsto> \<tau> \<prec> \<lparr>\<nu>x\<rparr>(\<lparr>\<nu>*xvec\<rparr>(P \<parallel> Q'))"
          by(rule BrClose)

        ultimately show ?case
          by force
      qed
    next
      case(cComm1 \<Psi>\<^sub>Q M N P' A\<^sub>P \<Psi>\<^sub>P K xvec xQ' A\<^sub>Q)
      have QTrans: "\<Psi> \<otimes> \<Psi>\<^sub>P \<rhd> \<lparr>\<nu>x\<rparr>Q \<longmapsto>K\<lparr>\<nu>*xvec\<rparr>\<langle>N\<rangle> \<prec> xQ'" and FrQ: "extractFrame(\<lparr>\<nu>x\<rparr>Q) = \<langle>A\<^sub>Q, \<Psi>\<^sub>Q\<rangle>" by fact+
      have PTrans: "\<Psi> \<otimes> \<Psi>\<^sub>Q \<rhd> P \<longmapsto>M\<lparr>N\<rparr> \<prec> P'" and FrP: "extractFrame P = \<langle>A\<^sub>P, \<Psi>\<^sub>P\<rangle>" by fact+
      have "x \<sharp> \<lparr>\<nu>x\<rparr>Q" by(simp add: abs_fresh)
      with QTrans have "x \<sharp> N" and "x \<sharp> xQ'" using \<open>xvec \<sharp>* x\<close> \<open>xvec \<sharp>* K\<close> \<open>distinct xvec\<close>
        by(force intro: outputFreshDerivative)+
      from PTrans \<open>x \<sharp> P\<close> \<open>x \<sharp> N\<close>  have "x \<sharp> P'" by(rule inputFreshDerivative)
      from \<open>x \<sharp> \<lparr>\<nu>x\<rparr>Q\<close> FrQ \<open>A\<^sub>Q \<sharp>* x\<close> have "x \<sharp> \<Psi>\<^sub>Q"
        by(drule_tac extractFrameFresh) auto
      from \<open>x \<sharp> P\<close> FrP \<open>A\<^sub>P \<sharp>* x\<close> have "x \<sharp> \<Psi>\<^sub>P"
        by(drule_tac extractFrameFresh) auto
      from \<open>A\<^sub>P \<sharp>* \<lparr>\<nu>x\<rparr>Q\<close> \<open>A\<^sub>P \<sharp>* x\<close> have "A\<^sub>P \<sharp>* Q" by simp
      from \<open>A\<^sub>Q \<sharp>* \<lparr>\<nu>x\<rparr>Q\<close> \<open>A\<^sub>Q \<sharp>* x\<close> have "A\<^sub>Q \<sharp>* Q" by simp
      from PTrans FrP \<open>distinct A\<^sub>P\<close> \<open>x \<sharp> P\<close> \<open>A\<^sub>Q \<sharp>* P\<close> \<open>xvec \<sharp>* P\<close> \<open>A\<^sub>P \<sharp>* \<Psi>\<close> \<open>A\<^sub>P \<sharp>* \<Psi>\<^sub>Q\<close> \<open>A\<^sub>P \<sharp>* x\<close> \<open>A\<^sub>P \<sharp>* A\<^sub>Q\<close> \<open>A\<^sub>P \<sharp>* P\<close>  \<open>A\<^sub>P \<sharp>* M\<close> \<open>A\<^sub>P \<sharp>* xvec\<close>
      obtain M' where "(\<Psi> \<otimes> \<Psi>\<^sub>Q) \<otimes> \<Psi>\<^sub>P \<turnstile> M \<leftrightarrow> M'" and "x \<sharp> M'" and "A\<^sub>Q \<sharp>* M'" and "xvec \<sharp>* M'"
        by(elim inputObtainPrefix[where B="x#xvec@A\<^sub>Q"]) (assumption | force simp add: fresh_star_list_cons)+
      then have MeqM': "\<Psi> \<otimes> \<Psi>\<^sub>P \<otimes> \<Psi>\<^sub>Q \<turnstile> M \<leftrightarrow> M'" by(metis statEqEnt Associativity Commutativity Composition)
      with \<open>\<Psi> \<otimes> \<Psi>\<^sub>P \<otimes> \<Psi>\<^sub>Q \<turnstile> M \<leftrightarrow> K\<close> have "\<Psi> \<otimes> \<Psi>\<^sub>P \<otimes> \<Psi>\<^sub>Q \<turnstile> K \<leftrightarrow> M'"
        by(blast intro: chanEqTrans chanEqSym)
      then have "(\<Psi> \<otimes> \<Psi>\<^sub>P) \<otimes> \<Psi>\<^sub>Q \<turnstile> K \<leftrightarrow> M'" by(metis statEqEnt Associativity Commutativity Composition)
      with QTrans FrQ \<open>distinct A\<^sub>Q\<close> \<open>A\<^sub>Q \<sharp>* \<Psi>\<close> \<open>A\<^sub>Q \<sharp>* \<Psi>\<^sub>P\<close> \<open>A\<^sub>Q \<sharp>* (\<lparr>\<nu>x\<rparr>Q)\<close> \<open>A\<^sub>Q \<sharp>* K\<close> \<open>A\<^sub>Q \<sharp>* M'\<close>
      have "\<Psi> \<otimes> \<Psi>\<^sub>P \<rhd> \<lparr>\<nu>x\<rparr>Q \<longmapsto>M'\<lparr>\<nu>*xvec\<rparr>\<langle>N\<rangle> \<prec> xQ'"
        by(force intro: outputRenameSubject)
      moreover from \<open>x \<sharp> \<Psi>\<close> \<open>x \<sharp> \<Psi>\<^sub>P\<close> have "x \<sharp> \<Psi> \<otimes> \<Psi>\<^sub>P" by force
      moreover from \<open>xvec \<sharp>* x\<close> have "x \<sharp> xvec" by simp
      with \<open>x \<sharp> M'\<close> \<open>x \<sharp> N\<close> have "x \<sharp> M'\<lparr>\<nu>*xvec\<rparr>\<langle>N\<rangle>" by simp
      moreover note \<open>x \<sharp> xQ'\<close>

      moreover from \<open>xvec \<sharp>* \<Psi>\<close> \<open>xvec \<sharp>* \<Psi>\<^sub>P\<close> have "xvec \<sharp>* (\<Psi> \<otimes> \<Psi>\<^sub>P)" by force
      moreover from \<open>xvec \<sharp>* \<lparr>\<nu>x\<rparr>Q\<close> \<open>x \<sharp> xvec\<close> have "xvec \<sharp>* Q" by simp
      moreover note \<open>xvec \<sharp>* M'\<close>

      moreover from \<open>xvec \<sharp>* \<Psi>\<close> \<open>xvec \<sharp>* \<Psi>\<^sub>P\<close> have "bn(M'\<lparr>\<nu>*xvec\<rparr>\<langle>N\<rangle>) \<sharp>* (\<Psi> \<otimes> \<Psi>\<^sub>P)" by force
      moreover from \<open>xvec \<sharp>* \<lparr>\<nu>x\<rparr>Q\<close> \<open>x \<sharp> xvec\<close> have "bn(M'\<lparr>\<nu>*xvec\<rparr>\<langle>N\<rangle>) \<sharp>* Q" by simp
      moreover from \<open>xvec \<sharp>* P\<close> have "bn(M'\<lparr>\<nu>*xvec\<rparr>\<langle>N\<rangle>) \<sharp>* P" by simp
      from \<open>xvec \<sharp>* \<Psi>\<close> have "bn(M'\<lparr>\<nu>*xvec\<rparr>\<langle>N\<rangle>) \<sharp>* \<Psi>" by simp
      from \<open>A\<^sub>Q \<sharp>* xvec\<close> \<open>A\<^sub>Q \<sharp>* M'\<close> \<open>A\<^sub>Q \<sharp>* N\<close> have "A\<^sub>Q \<sharp>* (M'\<lparr>\<nu>*xvec\<rparr>\<langle>N\<rangle>)" by simp
      have "object(M'\<lparr>\<nu>*xvec\<rparr>\<langle>N\<rangle>) = Some N" by simp
      have "bn(M'\<lparr>\<nu>*xvec\<rparr>\<langle>N\<rangle>) = xvec" by simp
      have "subject(M'\<lparr>\<nu>*xvec\<rparr>\<langle>N\<rangle>) = Some M'" by simp
      from \<open>xvec \<sharp>* M'\<close> have "bn(M'\<lparr>\<nu>*xvec\<rparr>\<langle>N\<rangle>) \<sharp>* subject(M'\<lparr>\<nu>*xvec\<rparr>\<langle>N\<rangle>)" by simp
      ultimately show ?case
        using \<open>x \<sharp> M'\<lparr>\<nu>*xvec\<rparr>\<langle>N\<rangle>\<close> \<open>bn(M'\<lparr>\<nu>*xvec\<rparr>\<langle>N\<rangle>) \<sharp>* P\<close> \<open>bn(M'\<lparr>\<nu>*xvec\<rparr>\<langle>N\<rangle>) \<sharp>* \<Psi>\<close> \<open>object(M'\<lparr>\<nu>*xvec\<rparr>\<langle>N\<rangle>) = Some N\<close>
          \<open>bn(M'\<lparr>\<nu>*xvec\<rparr>\<langle>N\<rangle>) = xvec\<close> \<open>subject(M'\<lparr>\<nu>*xvec\<rparr>\<langle>N\<rangle>) = Some M'\<close> \<open>A\<^sub>Q \<sharp>* (M'\<lparr>\<nu>*xvec\<rparr>\<langle>N\<rangle>)\<close>
      proof(induct rule: resOutputCases''''')
      	case(cOpen M'' xvec1 xvec2 y N' Q')
        then have Eq: "M'\<lparr>\<nu>*xvec\<rparr>\<langle>N\<rangle> = M''\<lparr>\<nu>*(xvec1 @ y # xvec2)\<rparr>\<langle>N'\<rangle>" by simp
        from \<open>x \<sharp> M'\<lparr>\<nu>*xvec\<rparr>\<langle>N\<rangle>\<close> Eq have "x \<sharp> xvec1" and "x \<noteq> y" and "x \<sharp> xvec2" and "x \<sharp> M''"
          by simp+
        from \<open>bn(M'\<lparr>\<nu>*xvec\<rparr>\<langle>N\<rangle>) \<sharp>* P\<close> Eq have "(xvec1@xvec2) \<sharp>* P" and "y \<sharp> P" by simp+
        from \<open>A\<^sub>Q \<sharp>* (M'\<lparr>\<nu>*xvec\<rparr>\<langle>N\<rangle>)\<close> Eq have "(xvec1@xvec2) \<sharp>* A\<^sub>Q" and "y \<sharp> A\<^sub>Q" and "A\<^sub>Q \<sharp>* M''" by simp+
        from \<open>bn(M'\<lparr>\<nu>*xvec\<rparr>\<langle>N\<rangle>) \<sharp>* \<Psi>\<close> Eq have "(xvec1@xvec2) \<sharp>* \<Psi>" and "y \<sharp> \<Psi>" by simp+
        from Eq have "N = N'" and "xvec = xvec1@y#xvec2" and "M' = M''" by(simp add: action.inject)+
        from \<open>x \<sharp> P\<close> \<open>y \<sharp> P\<close> \<open>x \<noteq> y\<close> \<open>\<Psi> \<otimes> \<Psi>\<^sub>Q \<rhd> P \<longmapsto>M\<lparr>N\<rparr> \<prec> P'\<close>
        have "\<Psi> \<otimes> \<Psi>\<^sub>Q \<rhd> P \<longmapsto>M\<lparr>([(y, x)] \<bullet> N)\<rparr> \<prec> ([(y, x)] \<bullet> P')"
          by(elim inputAlpha[where xvec="[y]"]) (auto simp add: calc_atm)
        then have PTrans: "\<Psi> \<otimes> \<Psi>\<^sub>Q \<rhd> P \<longmapsto>M\<lparr>([(x, y)] \<bullet> N)\<rparr> \<prec> ([(x, y)] \<bullet> P')"
          by(simp add: name_swap)

        from \<open>\<Psi> \<otimes> \<Psi>\<^sub>P \<rhd> [(x, y)] \<bullet> Q \<longmapsto> M''\<lparr>\<nu>*(xvec1 @ xvec2)\<rparr>\<langle>N'\<rangle> \<prec> Q'\<close>
        have "[(x, y)] \<bullet> (\<Psi> \<otimes> \<Psi>\<^sub>P \<rhd> [(x, y)] \<bullet> Q \<longmapsto> M''\<lparr>\<nu>*(xvec1 @ xvec2)\<rparr>\<langle>N'\<rangle> \<prec> Q')"
          by simp
        then have "[(x, y)] \<bullet> (\<Psi> \<otimes> \<Psi>\<^sub>P) \<rhd> ([(x, y)] \<bullet> ([(x, y)] \<bullet> Q)) \<longmapsto> ([(x, y)] \<bullet> M'')\<lparr>\<nu>*([(x, y)] \<bullet> (xvec1 @ xvec2))\<rparr>\<langle>([(x, y)] \<bullet> N')\<rangle> \<prec> [(x, y)] \<bullet> Q'"
          by(simp add: eqvts)
        with \<open>x \<sharp> (\<Psi> \<otimes> \<Psi>\<^sub>P)\<close> \<open>y \<sharp> (\<Psi> \<otimes> \<Psi>\<^sub>P)\<close> \<open>x \<sharp> xvec1\<close> \<open>y \<sharp> xvec1\<close> \<open>x \<sharp> xvec2\<close> \<open>y \<sharp> xvec2\<close> \<open>x \<sharp> M''\<close> \<open>y \<sharp> M''\<close>
        have QTrans: "\<Psi> \<otimes> \<Psi>\<^sub>P \<rhd> Q \<longmapsto> M''\<lparr>\<nu>*(xvec1 @ xvec2)\<rparr>\<langle>([(x, y)] \<bullet> N')\<rangle> \<prec> [(x, y)] \<bullet> Q'"
          by simp
        with \<open>A\<^sub>Q \<sharp>* x\<close> \<open>y \<sharp> A\<^sub>Q\<close> \<open>distinct xvec1\<close> \<open>distinct xvec2\<close> \<open>xvec1 \<sharp>* xvec2\<close> \<open>xvec1 \<sharp>* M''\<close> \<open>xvec2 \<sharp>* M''\<close>
          \<open>(xvec1@xvec2) \<sharp>* A\<^sub>Q\<close>
        have "A\<^sub>Q \<sharp>* ([(x, y)] \<bullet> Q')" using \<open>A\<^sub>Q \<sharp>* Q\<close>
          by(elim outputFreshChainDerivative(2)) (assumption | simp)+

        from \<open>extractFrame(\<lparr>\<nu>x\<rparr>Q) = \<langle>A\<^sub>Q, \<Psi>\<^sub>Q\<rangle>\<close> have FrxQ: "\<lparr>\<nu>x\<rparr>(extractFrame Q) = \<langle>A\<^sub>Q, \<Psi>\<^sub>Q\<rangle>" by simp
        then obtain z A\<^sub>Q' where A: "A\<^sub>Q = z#A\<^sub>Q'" by(cases A\<^sub>Q) auto
        with \<open>A\<^sub>Q \<sharp>* \<Psi>\<close> \<open>A\<^sub>Q \<sharp>* P\<close> \<open>A\<^sub>Q \<sharp>* P'\<close> \<open>A\<^sub>Q \<sharp>* \<Psi>\<^sub>P\<close> \<open>A\<^sub>Q \<sharp>* Q\<close> \<open>(xvec1@xvec2) \<sharp>* A\<^sub>Q\<close> \<open>A\<^sub>Q \<sharp>* M''\<close> \<open>A\<^sub>Q \<sharp>* ([(x, y)] \<bullet> Q')\<close> \<open>y \<sharp> A\<^sub>Q\<close> \<open>A\<^sub>Q \<sharp>* N\<close>
        have "A\<^sub>Q' \<sharp>* \<Psi>" and "A\<^sub>Q' \<sharp>* P" and "A\<^sub>Q' \<sharp>* \<Psi>\<^sub>P" and "A\<^sub>Q' \<sharp>* Q"
          and "z \<sharp> \<Psi>" and "z \<sharp> P" and "z \<sharp> P'" and "z \<sharp> \<Psi>\<^sub>P" and "z \<sharp> Q" and "z \<sharp> xvec1" and "z \<sharp> xvec2"
          and "z \<sharp> M''" and "z \<sharp> ([(x, y)] \<bullet> Q')" and "A\<^sub>Q' \<sharp>* M''" and "z \<noteq> y" and "z \<sharp> (xvec1@xvec2)"
          by auto
        from A \<open>A\<^sub>P \<sharp>* A\<^sub>Q\<close> have "A\<^sub>P \<sharp>* A\<^sub>Q'" and "z \<sharp> A\<^sub>P" by simp+
        from A \<open>A\<^sub>Q \<sharp>* x\<close> have "x \<noteq> z" and "x \<sharp> A\<^sub>Q'" by simp+

        from \<open>distinct A\<^sub>Q\<close> A have "z \<sharp> A\<^sub>Q'"
          by(induct A\<^sub>Q') (auto simp add: fresh_list_nil fresh_list_cons)
        from PTrans \<open>x \<sharp> P\<close> \<open>z \<sharp> P\<close> \<open>x \<noteq> z\<close> have "\<Psi> \<otimes> \<Psi>\<^sub>Q \<rhd> P \<longmapsto>M\<lparr>([(x, z)] \<bullet> [(x, y)] \<bullet> N)\<rparr> \<prec> ([(x, z)] \<bullet> [(x, y)] \<bullet> P')"
          by(elim inputAlpha[where xvec="[x]"]) (auto simp add: calc_atm)
        moreover note FrP
        moreover from QTrans have "([(x, z)] \<bullet> (\<Psi> \<otimes> \<Psi>\<^sub>P)) \<rhd> ([(x, z)] \<bullet> Q) \<longmapsto>([(x, z)] \<bullet> (M''\<lparr>\<nu>*(xvec1@xvec2)\<rparr>\<langle>([(x, y)] \<bullet> N')\<rangle> \<prec> ([(x, y)] \<bullet> Q')))"
          by(rule semantics.eqvt)
        with \<open>x \<sharp> \<Psi>\<close> \<open>z \<sharp> \<Psi>\<close> \<open>x \<sharp> \<Psi>\<^sub>P\<close> \<open>z \<sharp> \<Psi>\<^sub>P\<close> \<open>x \<sharp> M''\<close> \<open>z \<sharp> M''\<close> \<open>x \<sharp> xvec1\<close> \<open>x \<sharp> xvec2\<close> \<open>z \<sharp> xvec1\<close> \<open>z \<sharp> xvec2\<close>
        have "\<Psi> \<otimes> \<Psi>\<^sub>P \<rhd> ([(x, z)] \<bullet> Q) \<longmapsto>M''\<lparr>\<nu>*(xvec1@xvec2)\<rparr>\<langle>([(x, z)] \<bullet> [(x, y)] \<bullet> N')\<rangle> \<prec> ([(x, z)] \<bullet> [(x, y)] \<bullet> Q')"
          by(simp add: eqvts)
        moreover from A \<open>A\<^sub>Q \<sharp>* x\<close> FrxQ have "extractFrame([(x, z)] \<bullet> Q) = \<langle>A\<^sub>Q', \<Psi>\<^sub>Q\<rangle>"
          by(clarsimp simp add: alpha' eqvts frame.inject fresh_list_cons name_swap)
        moreover from \<open>A\<^sub>P \<sharp>* Q\<close> have "([(x, z)] \<bullet> A\<^sub>P) \<sharp>* ([(x, z)] \<bullet> Q)"
          by(simp add: pt_fresh_star_bij[OF pt_name_inst, OF at_name_inst])
        with \<open>A\<^sub>P \<sharp>* x\<close> \<open>z \<sharp> A\<^sub>P\<close> have "A\<^sub>P \<sharp>* ([(x, z)] \<bullet> Q)" by simp
        moreover from \<open>A\<^sub>Q' \<sharp>* Q\<close> have "([(x, z)] \<bullet> A\<^sub>Q') \<sharp>* ([(x, z)] \<bullet> Q)"
          by(simp add: pt_fresh_star_bij[OF pt_name_inst, OF at_name_inst])
        with \<open>x \<sharp> A\<^sub>Q'\<close> \<open>z \<sharp> A\<^sub>Q'\<close> have "A\<^sub>Q' \<sharp>* ([(x, z)] \<bullet> Q)" by simp
        ultimately have "\<Psi> \<rhd> (P \<parallel> ([(x, z)] \<bullet> Q)) \<longmapsto>\<tau> \<prec> \<lparr>\<nu>*(xvec1@xvec2)\<rparr>(([(x, z)] \<bullet> [(x, y)] \<bullet> P') \<parallel> ([(x, z)] \<bullet> [(x, y)] \<bullet> Q'))"
          using MeqM' \<open>M'=M''\<close> \<open>N=N'\<close> \<open>A\<^sub>P \<sharp>* \<Psi>\<close> \<open>A\<^sub>P \<sharp>* P\<close>  \<open>A\<^sub>P \<sharp>* A\<^sub>Q'\<close> \<open>A\<^sub>Q' \<sharp>* \<Psi>\<close> \<open>A\<^sub>Q' \<sharp>* P\<close> \<open>(xvec1@xvec2) \<sharp>* P\<close> \<open>A\<^sub>P \<sharp>* M\<close> \<open>A\<^sub>Q' \<sharp>* M''\<close>
          by(intro Comm1) (assumption | simp)+
        with\<open>z \<sharp> \<Psi>\<close> have "\<Psi> \<rhd> \<lparr>\<nu>z\<rparr>(P \<parallel> ([(x, z)] \<bullet> Q)) \<longmapsto>\<tau> \<prec> \<lparr>\<nu>z\<rparr>(\<lparr>\<nu>*(xvec1@xvec2)\<rparr>(([(x, z)] \<bullet> [(x, y)] \<bullet> P') \<parallel> ([(x, z)] \<bullet> [(x, y)] \<bullet> Q')))"
          by(intro Scope) auto
        moreover from \<open>x \<sharp> P\<close> \<open>z \<sharp> P\<close> \<open>z \<sharp> Q\<close> have "\<lparr>\<nu>z\<rparr>(P \<parallel> ([(x, z)] \<bullet> Q)) = \<lparr>\<nu>x\<rparr>([(x, z)] \<bullet> (P \<parallel> ([(x, z)] \<bullet> Q)))"
          by(subst alphaRes[of x]) (auto simp add: calc_atm fresh_left name_swap)
        with \<open>x \<sharp> P\<close> \<open>z \<sharp> P\<close> have "\<lparr>\<nu>z\<rparr>(P \<parallel> ([(x, z)] \<bullet> Q)) = \<lparr>\<nu>x\<rparr>(P \<parallel> Q)"
          by(simp add: eqvts)
        moreover from \<open>z \<noteq> y\<close> \<open>x \<noteq> z\<close> \<open>z \<sharp> P'\<close> \<open>z \<sharp> [(x, y)] \<bullet> Q'\<close> have "\<lparr>\<nu>z\<rparr>(\<lparr>\<nu>*(xvec1@xvec2)\<rparr>(([(x, z)] \<bullet> [(x, y)] \<bullet> P') \<parallel> ([(x, z)] \<bullet> [(x, y)] \<bullet> Q'))) = \<lparr>\<nu>x\<rparr>([(x, z)] \<bullet> (\<lparr>\<nu>*(xvec1@xvec2)\<rparr>(([(x, z)] \<bullet> [(x, y)] \<bullet> P') \<parallel> ([(x, z)] \<bullet> [(x, y)] \<bullet> Q'))))"
          by(subst alphaRes[of x]) (auto simp add: resChainFresh fresh_left calc_atm name_swap)
        with \<open>x \<sharp> xvec1\<close> \<open>x \<sharp> xvec2\<close> \<open>z \<sharp> xvec1\<close> \<open>z \<sharp> xvec2\<close> have "\<lparr>\<nu>z\<rparr>(\<lparr>\<nu>*(xvec1@xvec2)\<rparr>(([(x, z)] \<bullet> [(x, y)] \<bullet> P') \<parallel> ([(x, z)] \<bullet> [(x, y)] \<bullet> Q'))) = \<lparr>\<nu>x\<rparr>(\<lparr>\<nu>*(xvec1@xvec2)\<rparr>(([(x, y)] \<bullet> P') \<parallel> ([(x, y)] \<bullet> Q')))"
          by(simp add: eqvts)
        moreover from \<open>x \<sharp> P'\<close> \<open>x \<sharp> Q'\<close> \<open>x \<sharp> xvec1\<close> \<open>x \<sharp> xvec2\<close> \<open>y \<sharp> xvec1\<close> \<open>y \<sharp> xvec2\<close>
        have "\<lparr>\<nu>x\<rparr>(\<lparr>\<nu>*(xvec1@xvec2)\<rparr>(([(x, y)] \<bullet> P') \<parallel> ([(x, y)] \<bullet> Q'))) =  \<lparr>\<nu>y\<rparr>(\<lparr>\<nu>*(xvec1@xvec2)\<rparr>(P' \<parallel> Q'))"
          by(subst alphaRes[of y]) (auto simp add: resChainFresh calc_atm eqvts fresh_left name_swap)
        ultimately have "\<Psi> \<rhd> \<lparr>\<nu>x\<rparr>(P \<parallel> Q) \<longmapsto>\<tau> \<prec> \<lparr>\<nu>y\<rparr>(\<lparr>\<nu>*(xvec1@xvec2)\<rparr>(P' \<parallel> Q'))"
          by simp
        moreover from \<open>y \<sharp> \<Psi>\<close> \<open>(xvec1@xvec2) \<sharp>* \<Psi>\<close> \<open>xvec=xvec1@y#xvec2\<close>
        have "(\<Psi>, \<lparr>\<nu>y\<rparr>(\<lparr>\<nu>*(xvec1@xvec2)\<rparr>(P' \<parallel> Q')), \<lparr>\<nu>*xvec\<rparr>(P' \<parallel> Q')) \<in> Rel"
          by(force intro: C3 simp add: resChainAppend)
        ultimately show ?case by blast
      next
        case(cRes Q')
        have QTrans: "\<Psi> \<otimes> \<Psi>\<^sub>P \<rhd> Q \<longmapsto>M'\<lparr>\<nu>*xvec\<rparr>\<langle>N\<rangle> \<prec> Q'" by fact
        with \<open>A\<^sub>Q \<sharp>* Q\<close> \<open>A\<^sub>Q \<sharp>* xvec\<close> \<open>xvec \<sharp>* M'\<close> \<open>distinct xvec\<close> have "A\<^sub>Q \<sharp>* Q'"
          by(force dest: outputFreshChainDerivative)

        with \<open>extractFrame(\<lparr>\<nu>x\<rparr>Q) = \<langle>A\<^sub>Q, \<Psi>\<^sub>Q\<rangle>\<close> have FrxQ: "\<lparr>\<nu>x\<rparr>(extractFrame Q) = \<langle>A\<^sub>Q, \<Psi>\<^sub>Q\<rangle>" by simp
        then obtain y A\<^sub>Q' where A: "A\<^sub>Q = y#A\<^sub>Q'" by(cases A\<^sub>Q) auto
        with \<open>A\<^sub>Q \<sharp>* \<Psi>\<close> \<open>A\<^sub>Q \<sharp>* P\<close> \<open>A\<^sub>Q \<sharp>* P'\<close> \<open>A\<^sub>Q \<sharp>* \<Psi>\<^sub>P\<close> \<open>A\<^sub>Q \<sharp>* Q\<close> \<open>A\<^sub>Q \<sharp>* xvec\<close> \<open>A\<^sub>Q \<sharp>* M'\<close> \<open>A\<^sub>Q \<sharp>* Q'\<close>
        have "A\<^sub>Q' \<sharp>* \<Psi>" and "A\<^sub>Q' \<sharp>* P" and "A\<^sub>Q' \<sharp>* \<Psi>\<^sub>P" and "A\<^sub>Q' \<sharp>* Q" and "A\<^sub>Q \<sharp>* xvec" and "A\<^sub>Q \<sharp>* Q'"
          and "y \<sharp> \<Psi>" and "y \<sharp> P" and "y \<sharp> P'" and "y \<sharp> \<Psi>\<^sub>P" and "y \<sharp> Q" and "y \<sharp> xvec" and "y \<sharp> M'" and "y \<sharp> Q'"
          and "A\<^sub>Q' \<sharp>* M'"
          by(simp)+
        from A \<open>A\<^sub>P \<sharp>* A\<^sub>Q\<close> have "A\<^sub>P \<sharp>* A\<^sub>Q'" and "y \<sharp> A\<^sub>P" by(simp add: fresh_star_list_cons)+
        from A \<open>A\<^sub>Q \<sharp>* x\<close> have "x \<noteq> y" and "x \<sharp> A\<^sub>Q'" by(simp add: fresh_list_cons)+

        with A \<open>distinct A\<^sub>Q\<close> have "y \<sharp> A\<^sub>Q'"
          by(induct A\<^sub>Q') (auto simp add: fresh_list_nil fresh_list_cons)

        from \<open>x \<sharp> P\<close> \<open>y \<sharp> P\<close> \<open>x \<noteq> y\<close> \<open>\<Psi> \<otimes> \<Psi>\<^sub>Q \<rhd> P \<longmapsto>M\<lparr>N\<rparr> \<prec> P'\<close>
        have "\<Psi> \<otimes> \<Psi>\<^sub>Q \<rhd> P \<longmapsto>M\<lparr>([(y, x)] \<bullet> N)\<rparr> \<prec> [(y, x)] \<bullet> P'"
          by(intro inputAlpha[where xvec="[y]"]) (auto simp add: calc_atm)
        then have "\<Psi> \<otimes> \<Psi>\<^sub>Q \<rhd> P \<longmapsto>M\<lparr>([(x, y)] \<bullet> N)\<rparr> \<prec> [(x, y)] \<bullet> P'"
          by(simp add: name_swap)
        moreover note FrP
        moreover from  \<open>\<Psi> \<otimes> \<Psi>\<^sub>P \<rhd> Q \<longmapsto>M'\<lparr>\<nu>*xvec\<rparr>\<langle>N\<rangle> \<prec> Q'\<close> have "([(x, y)] \<bullet> (\<Psi> \<otimes> \<Psi>\<^sub>P)) \<rhd> ([(x, y)] \<bullet> Q) \<longmapsto>([(x, y)] \<bullet> (M'\<lparr>\<nu>*xvec\<rparr>\<langle>N\<rangle> \<prec> Q'))"
          by(rule semantics.eqvt)
        with \<open>x \<sharp> \<Psi>\<close> \<open>y \<sharp> \<Psi>\<close> \<open>x \<sharp> \<Psi>\<^sub>P\<close> \<open>y \<sharp> \<Psi>\<^sub>P\<close> \<open>x \<sharp> M'\<close> \<open>y \<sharp> M'\<close> \<open>x \<sharp> xvec\<close> \<open>y \<sharp> xvec\<close>
        have "\<Psi> \<otimes> \<Psi>\<^sub>P \<rhd> ([(x, y)] \<bullet> Q) \<longmapsto>M'\<lparr>\<nu>*xvec\<rparr>\<langle>([(x, y)] \<bullet> N)\<rangle> \<prec> ([(x, y)] \<bullet> Q')"
          by(simp add: eqvts)
        moreover from A \<open>A\<^sub>Q \<sharp>* x\<close> FrxQ have FrQ: "extractFrame([(x, y)] \<bullet> Q) = \<langle>A\<^sub>Q', \<Psi>\<^sub>Q\<rangle>"
          by(clarsimp simp add: alpha' eqvts frame.inject fresh_list_cons name_swap)
        moreover from \<open>A\<^sub>P \<sharp>* Q\<close> have "([(x, y)] \<bullet> A\<^sub>P) \<sharp>* ([(x, y)] \<bullet> Q)" by(simp add: pt_fresh_star_bij[OF pt_name_inst, OF at_name_inst])
        with \<open>A\<^sub>P \<sharp>* x\<close> \<open>y \<sharp> A\<^sub>P\<close> have "A\<^sub>P \<sharp>* ([(x, y)] \<bullet> Q)" by simp
        moreover from \<open>A\<^sub>Q' \<sharp>* Q\<close> have "([(x, y)] \<bullet> A\<^sub>Q') \<sharp>* ([(x, y)] \<bullet> Q)" by(simp add: pt_fresh_star_bij[OF pt_name_inst, OF at_name_inst])
        with \<open>x \<sharp> A\<^sub>Q'\<close> \<open>y \<sharp> A\<^sub>Q'\<close> have "A\<^sub>Q' \<sharp>* ([(x, y)] \<bullet> Q)" by simp
        ultimately have "\<Psi> \<rhd> (P \<parallel> ([(x, y)] \<bullet> Q)) \<longmapsto>\<tau> \<prec> \<lparr>\<nu>*xvec\<rparr>([(x, y)] \<bullet> P') \<parallel> ([(x, y)] \<bullet> Q')"
          using MeqM' \<open>A\<^sub>P \<sharp>* \<Psi>\<close> \<open>A\<^sub>P \<sharp>* P\<close>  \<open>A\<^sub>P \<sharp>* A\<^sub>Q'\<close> \<open>A\<^sub>Q' \<sharp>* \<Psi>\<close> \<open>A\<^sub>Q' \<sharp>* P\<close> \<open>xvec \<sharp>* P\<close> \<open>A\<^sub>P \<sharp>* M\<close> \<open>A\<^sub>Q' \<sharp>* M'\<close>
          by(intro Comm1) (assumption | simp)+
        with\<open>y \<sharp> \<Psi>\<close> have "\<Psi> \<rhd> \<lparr>\<nu>y\<rparr>(P \<parallel> ([(x, y)] \<bullet> Q)) \<longmapsto>\<tau> \<prec> \<lparr>\<nu>y\<rparr>(\<lparr>\<nu>*xvec\<rparr>(([(x, y)] \<bullet> P') \<parallel> ([(x, y)] \<bullet> Q')))"
          by(intro Scope) auto
        moreover from \<open>x \<sharp> P\<close> \<open>y \<sharp> P\<close> \<open>y \<sharp> Q\<close> have "\<lparr>\<nu>y\<rparr>(P \<parallel> ([(x, y)] \<bullet> Q)) = \<lparr>\<nu>x\<rparr>([(x, y)] \<bullet> (P \<parallel> ([(x, y)] \<bullet> Q)))"
          by(subst alphaRes[of x]) (auto simp add: calc_atm fresh_left name_swap)
        with \<open>x \<sharp> P\<close> \<open>y \<sharp> P\<close> have "\<lparr>\<nu>y\<rparr>(P \<parallel> ([(x, y)] \<bullet> Q)) = \<lparr>\<nu>x\<rparr>(P \<parallel> Q)"
          by(simp add: eqvts)
        moreover from \<open>y \<sharp> P'\<close> \<open>y \<sharp> Q'\<close> \<open>x \<sharp> xvec\<close> \<open>y \<sharp> xvec\<close> have "\<lparr>\<nu>y\<rparr>(\<lparr>\<nu>*xvec\<rparr>(([(x, y)] \<bullet> P') \<parallel> ([(x, y)] \<bullet> Q'))) =  \<lparr>\<nu>x\<rparr>(\<lparr>\<nu>*xvec\<rparr>(P' \<parallel> Q'))"
          by(subst alphaRes[of y]) (auto simp add: resChainFresh calc_atm eqvts fresh_left name_swap)
        ultimately have "\<Psi> \<rhd> \<lparr>\<nu>x\<rparr>(P \<parallel> Q) \<longmapsto>\<tau> \<prec> \<lparr>\<nu>x\<rparr>(\<lparr>\<nu>*xvec\<rparr>(P' \<parallel> Q'))"
          by simp
        moreover from \<open>x \<sharp> \<Psi>\<close> \<open>x \<sharp> P'\<close> \<open>xvec \<sharp>* \<Psi>\<close> have "(\<Psi>, \<lparr>\<nu>x\<rparr>(\<lparr>\<nu>*xvec\<rparr>(P' \<parallel> Q')), \<lparr>\<nu>*xvec\<rparr>(P' \<parallel> \<lparr>\<nu>x\<rparr>Q')) \<in> Rel"
          by(rule C2)
        ultimately show ?case by blast
      qed
    next
      case(cComm2 \<Psi>\<^sub>Q M xvec N P' A\<^sub>P \<Psi>\<^sub>P K xQ' A\<^sub>Q)
      have QTrans: "\<Psi> \<otimes> \<Psi>\<^sub>P \<rhd> \<lparr>\<nu>x\<rparr>Q \<longmapsto>K\<lparr>N\<rparr> \<prec> xQ'" and FrQ: "extractFrame(\<lparr>\<nu>x\<rparr>Q) = \<langle>A\<^sub>Q, \<Psi>\<^sub>Q\<rangle>" by fact+
      have PTrans: "\<Psi> \<otimes> \<Psi>\<^sub>Q \<rhd> P \<longmapsto>M\<lparr>\<nu>*xvec\<rparr>\<langle>N\<rangle> \<prec> P'" and FrP: "extractFrame P = \<langle>A\<^sub>P, \<Psi>\<^sub>P\<rangle>" by fact+
      from PTrans \<open>x \<sharp> P\<close> have "x \<sharp> N" and "x \<sharp> P'" using \<open>xvec \<sharp>* x\<close> \<open>xvec \<sharp>* M\<close> \<open>distinct xvec\<close>
        by(force intro: outputFreshDerivative)+
      have "x \<sharp> \<lparr>\<nu>x\<rparr>Q" by(simp add: abs_fresh)
      with FrQ \<open>A\<^sub>Q \<sharp>* x\<close> have "x \<sharp> \<Psi>\<^sub>Q"
        by(drule_tac extractFrameFresh) auto
      from \<open>x \<sharp> P\<close> FrP \<open>A\<^sub>P \<sharp>* x\<close> have "x \<sharp> \<Psi>\<^sub>P"
        by(drule_tac extractFrameFresh) auto
      from \<open>A\<^sub>P \<sharp>* \<lparr>\<nu>x\<rparr>Q\<close> \<open>A\<^sub>P \<sharp>* x\<close> have "A\<^sub>P \<sharp>* Q" by simp
      from \<open>A\<^sub>Q \<sharp>* \<lparr>\<nu>x\<rparr>Q\<close> \<open>A\<^sub>Q \<sharp>* x\<close> have "A\<^sub>Q \<sharp>* Q" by simp
      from \<open>xvec \<sharp>* x\<close> \<open>xvec \<sharp>* \<lparr>\<nu>x\<rparr>Q\<close> have "xvec \<sharp>* Q" by simp

      from \<open>\<Psi> \<otimes> \<Psi>\<^sub>Q \<rhd> P \<longmapsto> M\<lparr>\<nu>*xvec\<rparr>\<langle>N\<rangle> \<prec> P'\<close> have PResTrans: "\<Psi> \<otimes> \<Psi>\<^sub>Q \<rhd> P \<longmapsto> ROut M (\<lparr>\<nu>*xvec\<rparr>N \<prec>' P')"
        by(simp add: residualInject)

      from PResTrans FrP \<open>distinct A\<^sub>P\<close> \<open>x \<sharp> P\<close> \<open>A\<^sub>Q \<sharp>* P\<close> \<open>A\<^sub>P \<sharp>* \<Psi>\<close> \<open>A\<^sub>P \<sharp>* \<Psi>\<^sub>Q\<close> \<open>A\<^sub>P \<sharp>* x\<close> \<open>A\<^sub>P \<sharp>* A\<^sub>Q\<close> \<open>A\<^sub>P \<sharp>* P\<close>  \<open>A\<^sub>P \<sharp>* M\<close> \<open>xvec \<sharp>* M\<close> \<open>distinct xvec\<close>
      obtain M' where "(\<Psi> \<otimes> \<Psi>\<^sub>Q) \<otimes> \<Psi>\<^sub>P \<turnstile> M \<leftrightarrow> M'" and "x \<sharp> M'" and "A\<^sub>Q \<sharp>* M'"
        by(elim outputObtainPrefix[where B="x#A\<^sub>Q"]) (assumption | force simp add: fresh_star_list_cons)+
      then have MeqM': "\<Psi> \<otimes> \<Psi>\<^sub>P \<otimes> \<Psi>\<^sub>Q \<turnstile> M \<leftrightarrow> M'"
        by(metis statEqEnt Associativity Commutativity Composition)
      with \<open>\<Psi> \<otimes> \<Psi>\<^sub>P \<otimes> \<Psi>\<^sub>Q \<turnstile> M \<leftrightarrow> K\<close> have "\<Psi> \<otimes> \<Psi>\<^sub>P \<otimes> \<Psi>\<^sub>Q \<turnstile> K \<leftrightarrow> M'"
        by(blast intro: chanEqTrans chanEqSym)
      then have "(\<Psi> \<otimes> \<Psi>\<^sub>P) \<otimes> \<Psi>\<^sub>Q \<turnstile> K \<leftrightarrow> M'"
        by(metis statEqEnt Associativity Commutativity Composition)
      with QTrans FrQ \<open>distinct A\<^sub>Q\<close> \<open>A\<^sub>Q \<sharp>* \<Psi>\<close> \<open>A\<^sub>Q \<sharp>* \<Psi>\<^sub>P\<close> \<open>A\<^sub>Q \<sharp>* (\<lparr>\<nu>x\<rparr>Q)\<close> \<open>A\<^sub>Q \<sharp>* K\<close> \<open>A\<^sub>Q \<sharp>* M'\<close>
      have "\<Psi> \<otimes> \<Psi>\<^sub>P \<rhd> \<lparr>\<nu>x\<rparr>Q \<longmapsto>M'\<lparr>N\<rparr> \<prec> xQ'" by(force intro: inputRenameSubject)

      moreover from \<open>x \<sharp> \<Psi>\<close> \<open>x \<sharp> \<Psi>\<^sub>P\<close> have "x \<sharp> \<Psi> \<otimes> \<Psi>\<^sub>P" by force
      moreover note \<open>x \<sharp> M'\<close> \<open>x \<sharp> N\<close>
      moreover from QTrans \<open>x \<sharp> N\<close> have "x \<sharp> xQ'" by(force dest: inputFreshDerivative simp add: abs_fresh)
      ultimately show ?case
      proof(induct rule: resInputCases)
        case(cRes Q')
        have QTrans: "\<Psi> \<otimes> \<Psi>\<^sub>P \<rhd> Q \<longmapsto>M'\<lparr>N\<rparr> \<prec> Q'" by fact
        with \<open>A\<^sub>Q \<sharp>* Q\<close> \<open>A\<^sub>Q \<sharp>* N\<close> have "A\<^sub>Q \<sharp>* Q'"
          by(elim inputFreshChainDerivative)

        with \<open>extractFrame(\<lparr>\<nu>x\<rparr>Q) = \<langle>A\<^sub>Q, \<Psi>\<^sub>Q\<rangle>\<close> have FrxQ: "\<lparr>\<nu>x\<rparr>(extractFrame Q) = \<langle>A\<^sub>Q, \<Psi>\<^sub>Q\<rangle>" by simp
        then obtain y A\<^sub>Q' where A: "A\<^sub>Q = y#A\<^sub>Q'" by(cases A\<^sub>Q) auto
        with \<open>A\<^sub>Q \<sharp>* \<Psi>\<close> \<open>A\<^sub>Q \<sharp>* P\<close> \<open>A\<^sub>Q \<sharp>* P'\<close> \<open>A\<^sub>Q \<sharp>* \<Psi>\<^sub>P\<close> \<open>A\<^sub>Q \<sharp>* Q\<close> \<open>A\<^sub>Q \<sharp>* xvec\<close> \<open>A\<^sub>Q \<sharp>* M'\<close> \<open>A\<^sub>Q \<sharp>* Q'\<close> \<open>A\<^sub>Q \<sharp>* N\<close>
        have "A\<^sub>Q' \<sharp>* \<Psi>" and "A\<^sub>Q' \<sharp>* P" and "A\<^sub>Q' \<sharp>* \<Psi>\<^sub>P" and "A\<^sub>Q' \<sharp>* Q" and "A\<^sub>Q \<sharp>* xvec" and "A\<^sub>Q \<sharp>* Q'"
          and "y \<sharp> \<Psi>" and "y \<sharp> P" and "y \<sharp> P'" and "y \<sharp> \<Psi>\<^sub>P" and "y \<sharp> Q" and "y \<sharp> xvec" and "y \<sharp> M'" and "y \<sharp> Q'" and "y \<sharp> N"
          and "A\<^sub>Q' \<sharp>* M'"
          by(simp)+
        from A \<open>A\<^sub>P \<sharp>* A\<^sub>Q\<close> have "A\<^sub>P \<sharp>* A\<^sub>Q'" and "y \<sharp> A\<^sub>P" by(simp add: fresh_star_list_cons)+
        from A \<open>A\<^sub>Q \<sharp>* x\<close> have "x \<noteq> y" and "x \<sharp> A\<^sub>Q'" by(simp add: fresh_list_cons)+

        with A \<open>distinct A\<^sub>Q\<close> have "y \<sharp> A\<^sub>Q'"
          by(induct A\<^sub>Q') (auto simp add: fresh_list_nil fresh_list_cons)

        note PTrans FrP
        moreover from  \<open>\<Psi> \<otimes> \<Psi>\<^sub>P \<rhd> Q \<longmapsto>M'\<lparr>N\<rparr> \<prec> Q'\<close> have "([(x, y)] \<bullet> (\<Psi> \<otimes> \<Psi>\<^sub>P)) \<rhd> ([(x, y)] \<bullet> Q) \<longmapsto>([(x, y)] \<bullet> (M'\<lparr>N\<rparr> \<prec> Q'))"
          by(rule semantics.eqvt)
        with \<open>x \<sharp> \<Psi>\<close> \<open>y \<sharp> \<Psi>\<close> \<open>x \<sharp> \<Psi>\<^sub>P\<close> \<open>y \<sharp> \<Psi>\<^sub>P\<close> \<open>x \<sharp> M'\<close> \<open>y \<sharp> M'\<close> \<open>x \<sharp> N\<close> \<open>y \<sharp> N\<close>
        have "\<Psi> \<otimes> \<Psi>\<^sub>P \<rhd> ([(x, y)] \<bullet> Q) \<longmapsto>M'\<lparr>N\<rparr> \<prec> ([(x, y)] \<bullet> Q')"
          by(simp add: eqvts)
        moreover from A \<open>A\<^sub>Q \<sharp>* x\<close> FrxQ have FrQ: "extractFrame([(x, y)] \<bullet> Q) = \<langle>A\<^sub>Q', \<Psi>\<^sub>Q\<rangle>" and "y \<sharp> extractFrame Q"
          by(clarsimp simp add: alpha' eqvts frame.inject fresh_list_cons name_swap)+
        moreover from \<open>A\<^sub>P \<sharp>* Q\<close> have "([(x, y)] \<bullet> A\<^sub>P) \<sharp>* ([(x, y)] \<bullet> Q)" by(simp add: pt_fresh_star_bij[OF pt_name_inst, OF at_name_inst])
        with \<open>A\<^sub>P \<sharp>* x\<close> \<open>y \<sharp> A\<^sub>P\<close> have "A\<^sub>P \<sharp>* ([(x, y)] \<bullet> Q)" by simp
        moreover from \<open>A\<^sub>Q' \<sharp>* Q\<close> have "([(x, y)] \<bullet> A\<^sub>Q') \<sharp>* ([(x, y)] \<bullet> Q)" by(simp add: pt_fresh_star_bij[OF pt_name_inst, OF at_name_inst])
        with \<open>x \<sharp> A\<^sub>Q'\<close> \<open>y \<sharp> A\<^sub>Q'\<close> have "A\<^sub>Q' \<sharp>* ([(x, y)] \<bullet> Q)" by simp
        moreover from \<open>xvec \<sharp>* Q\<close> have "([(x, y)] \<bullet> xvec) \<sharp>* ([(x, y)] \<bullet> Q)" by(simp add: pt_fresh_star_bij[OF pt_name_inst, OF at_name_inst])
        with \<open>xvec \<sharp>* x\<close> \<open>y \<sharp> xvec\<close> have "xvec \<sharp>* ([(x, y)] \<bullet> Q)" by simp
        ultimately have "\<Psi> \<rhd> (P \<parallel> ([(x, y)] \<bullet> Q)) \<longmapsto>\<tau> \<prec> \<lparr>\<nu>*xvec\<rparr>(P' \<parallel> ([(x, y)] \<bullet> Q'))"
          using MeqM' \<open>A\<^sub>P \<sharp>* \<Psi>\<close> \<open>A\<^sub>P \<sharp>* P\<close>  \<open>A\<^sub>P \<sharp>* A\<^sub>Q'\<close> \<open>A\<^sub>Q' \<sharp>* \<Psi>\<close> \<open>A\<^sub>Q' \<sharp>* P\<close> \<open>A\<^sub>P \<sharp>* M\<close> \<open>A\<^sub>Q' \<sharp>* M'\<close>
          by(intro Comm2) (assumption | simp)+
        with\<open>y \<sharp> \<Psi>\<close> have "\<Psi> \<rhd> \<lparr>\<nu>y\<rparr>(P \<parallel> ([(x, y)] \<bullet> Q)) \<longmapsto>\<tau> \<prec> \<lparr>\<nu>y\<rparr>(\<lparr>\<nu>*xvec\<rparr>(P' \<parallel> ([(x, y)] \<bullet> Q')))"
          by(intro Scope) auto
        moreover from \<open>x \<sharp> P\<close> \<open>y \<sharp> P\<close> \<open>y \<sharp> Q\<close> have "\<lparr>\<nu>y\<rparr>(P \<parallel> ([(x, y)] \<bullet> Q)) = \<lparr>\<nu>x\<rparr>([(x, y)] \<bullet> (P \<parallel> ([(x, y)] \<bullet> Q)))"
          by(subst alphaRes[of x]) (auto simp add: calc_atm fresh_left name_swap)
        with \<open>x \<sharp> P\<close> \<open>y \<sharp> P\<close> have "\<lparr>\<nu>y\<rparr>(P \<parallel> ([(x, y)] \<bullet> Q)) = \<lparr>\<nu>x\<rparr>(P \<parallel> Q)"
          by(simp add: eqvts)
        moreover from \<open>x \<sharp> P'\<close> \<open>y \<sharp> P'\<close> \<open>y \<sharp> Q'\<close> \<open>xvec \<sharp>* x\<close> \<open>y \<sharp> xvec\<close> have "\<lparr>\<nu>y\<rparr>(\<lparr>\<nu>*xvec\<rparr>(P' \<parallel> ([(x, y)] \<bullet> Q'))) =  \<lparr>\<nu>x\<rparr>(\<lparr>\<nu>*xvec\<rparr>(P' \<parallel> Q'))"
          by(subst alphaRes[of y]) (auto simp add: resChainFresh calc_atm eqvts fresh_left name_swap)
        ultimately have "\<Psi> \<rhd> \<lparr>\<nu>x\<rparr>(P \<parallel> Q) \<longmapsto>\<tau> \<prec> \<lparr>\<nu>x\<rparr>(\<lparr>\<nu>*xvec\<rparr>(P' \<parallel> Q'))"
          by simp
        moreover from \<open>x \<sharp> \<Psi>\<close> \<open>x \<sharp> P'\<close> \<open>xvec \<sharp>* \<Psi>\<close> have "(\<Psi>, \<lparr>\<nu>x\<rparr>(\<lparr>\<nu>*xvec\<rparr>(P' \<parallel> Q')), \<lparr>\<nu>*xvec\<rparr>(P' \<parallel> \<lparr>\<nu>x\<rparr>Q')) \<in> Rel"
          by(rule C2)
        ultimately show ?case by blast
      qed
    next
      case(cBrMerge \<Psi>\<^sub>Q M N P' A\<^sub>P \<Psi>\<^sub>P xQ' A\<^sub>Q)
      have QTrans: "\<Psi> \<otimes> \<Psi>\<^sub>P \<rhd> \<lparr>\<nu>x\<rparr>Q \<longmapsto>\<questiondown>M\<lparr>N\<rparr> \<prec> xQ'" and FrQ: "extractFrame(\<lparr>\<nu>x\<rparr>Q) = \<langle>A\<^sub>Q, \<Psi>\<^sub>Q\<rangle>" by fact+
      have PTrans: "\<Psi> \<otimes> \<Psi>\<^sub>Q \<rhd> P \<longmapsto>\<questiondown>M\<lparr>N\<rparr> \<prec> P'" and FrP: "extractFrame P = \<langle>A\<^sub>P, \<Psi>\<^sub>P\<rangle>" by fact+
      from \<open>x \<sharp> \<alpha>\<close> \<open>\<alpha> = \<questiondown>M\<lparr>N\<rparr>\<close> have "x \<sharp> M" and "x \<sharp> N" by simp+
      from \<open>x \<sharp> P' \<parallel> xQ'\<close> have "x \<sharp> xQ'" by simp
      from FrP \<open>A\<^sub>P \<sharp>* x\<close> \<open>x \<sharp> P\<close> have "x \<sharp> \<Psi>\<^sub>P"
        by(drule_tac extractFrameFresh) auto
      from PTrans \<open>x \<sharp> P\<close> \<open>x \<sharp> N\<close> have "x \<sharp> P'"
        by(rule brinputFreshDerivative)
      have "x \<sharp> \<lparr>\<nu>x\<rparr>Q" by(simp add: abs_fresh)
      with FrQ \<open>A\<^sub>Q \<sharp>* x\<close> have "x \<sharp> \<Psi>\<^sub>Q"
        by(drule_tac extractFrameFresh) auto
      from \<open>A\<^sub>P \<sharp>* \<lparr>\<nu>x\<rparr>Q\<close> \<open>A\<^sub>P \<sharp>* x\<close> have "A\<^sub>P \<sharp>* Q" by simp
      from \<open>A\<^sub>Q \<sharp>* \<lparr>\<nu>x\<rparr>Q\<close> \<open>A\<^sub>Q \<sharp>* x\<close> have "A\<^sub>Q \<sharp>* Q" by simp
      from \<open>x \<sharp> \<Psi>\<close> \<open>x \<sharp> \<Psi>\<^sub>P\<close>
      have "x \<sharp> (\<Psi> \<otimes> \<Psi>\<^sub>P)" by force
      from \<open>\<Psi> \<otimes> \<Psi>\<^sub>P \<rhd> \<lparr>\<nu>x\<rparr>Q \<longmapsto> \<questiondown>M\<lparr>N\<rparr> \<prec> xQ'\<close> \<open>x \<sharp> (\<Psi> \<otimes> \<Psi>\<^sub>P)\<close> \<open>x \<sharp> M\<close> \<open>x \<sharp> N\<close> \<open>x \<sharp> xQ'\<close>
      show ?case
      proof(induct rule: resBrInputCases)
        case(cRes Q')
        have QTrans: "\<Psi> \<otimes> \<Psi>\<^sub>P \<rhd> Q \<longmapsto>\<questiondown>M\<lparr>N\<rparr> \<prec> Q'" by fact
        with \<open>A\<^sub>Q \<sharp>* Q\<close> \<open>A\<^sub>Q \<sharp>* N\<close> have "A\<^sub>Q \<sharp>* Q'"
          by(elim brinputFreshChainDerivative)

        with \<open>extractFrame(\<lparr>\<nu>x\<rparr>Q) = \<langle>A\<^sub>Q, \<Psi>\<^sub>Q\<rangle>\<close> have FrxQ: "\<lparr>\<nu>x\<rparr>(extractFrame Q) = \<langle>A\<^sub>Q, \<Psi>\<^sub>Q\<rangle>" by simp
        then obtain y A\<^sub>Q' where A: "A\<^sub>Q = y#A\<^sub>Q'" by(cases A\<^sub>Q) auto
        with \<open>A\<^sub>Q \<sharp>* \<Psi>\<close> \<open>A\<^sub>Q \<sharp>* P\<close> \<open>A\<^sub>Q \<sharp>* P'\<close> \<open>A\<^sub>Q \<sharp>* \<Psi>\<^sub>P\<close> \<open>A\<^sub>Q \<sharp>* Q\<close> \<open>A\<^sub>Q \<sharp>* M\<close> \<open>A\<^sub>Q \<sharp>* Q'\<close> \<open>A\<^sub>Q \<sharp>* N\<close>
        have "A\<^sub>Q' \<sharp>* \<Psi>" and "A\<^sub>Q' \<sharp>* P" and "A\<^sub>Q' \<sharp>* \<Psi>\<^sub>P" and "A\<^sub>Q' \<sharp>* Q" and "A\<^sub>Q \<sharp>* Q'"
          and "y \<sharp> \<Psi>" and "y \<sharp> P" and "y \<sharp> P'" and "y \<sharp> \<Psi>\<^sub>P" and "y \<sharp> Q" and "y \<sharp> M" and "y \<sharp> Q'" and "y \<sharp> N"
          and "A\<^sub>Q' \<sharp>* M"
          by(simp)+
        from A \<open>A\<^sub>P \<sharp>* A\<^sub>Q\<close> have "A\<^sub>P \<sharp>* A\<^sub>Q'" and "y \<sharp> A\<^sub>P" by(simp add: fresh_star_list_cons)+
        from A \<open>A\<^sub>Q \<sharp>* x\<close> have "x \<noteq> y" and "x \<sharp> A\<^sub>Q'" by(simp add: fresh_list_cons)+

        with A \<open>distinct A\<^sub>Q\<close> have "y \<sharp> A\<^sub>Q'"
          by(induct A\<^sub>Q') (auto simp add: fresh_list_nil fresh_list_cons)

        note PTrans FrP
        moreover from  \<open>\<Psi> \<otimes> \<Psi>\<^sub>P \<rhd> Q \<longmapsto>\<questiondown>M\<lparr>N\<rparr> \<prec> Q'\<close> have "([(x, y)] \<bullet> (\<Psi> \<otimes> \<Psi>\<^sub>P)) \<rhd> ([(x, y)] \<bullet> Q) \<longmapsto>([(x, y)] \<bullet> (\<questiondown>M\<lparr>N\<rparr> \<prec> Q'))"
          by(rule semantics.eqvt)
        with \<open>x \<sharp> \<Psi>\<close> \<open>y \<sharp> \<Psi>\<close> \<open>x \<sharp> \<Psi>\<^sub>P\<close> \<open>y \<sharp> \<Psi>\<^sub>P\<close> \<open>x \<sharp> M\<close> \<open>y \<sharp> M\<close> \<open>x \<sharp> N\<close> \<open>y \<sharp> N\<close>
        have "\<Psi> \<otimes> \<Psi>\<^sub>P \<rhd> ([(x, y)] \<bullet> Q) \<longmapsto>\<questiondown>M\<lparr>N\<rparr> \<prec> ([(x, y)] \<bullet> Q')"
          by(simp add: eqvts)
        moreover from A \<open>A\<^sub>Q \<sharp>* x\<close> FrxQ have FrQ: "extractFrame([(x, y)] \<bullet> Q) = \<langle>A\<^sub>Q', \<Psi>\<^sub>Q\<rangle>" and "y \<sharp> extractFrame Q"
          by(clarsimp simp add: alpha' eqvts frame.inject fresh_list_cons name_swap)+
        moreover from \<open>A\<^sub>P \<sharp>* Q\<close> have "([(x, y)] \<bullet> A\<^sub>P) \<sharp>* ([(x, y)] \<bullet> Q)" by(simp add: pt_fresh_star_bij[OF pt_name_inst, OF at_name_inst])
        with \<open>A\<^sub>P \<sharp>* x\<close> \<open>y \<sharp> A\<^sub>P\<close> have "A\<^sub>P \<sharp>* ([(x, y)] \<bullet> Q)" by simp
        moreover from \<open>A\<^sub>Q' \<sharp>* Q\<close> have "([(x, y)] \<bullet> A\<^sub>Q') \<sharp>* ([(x, y)] \<bullet> Q)" by(simp add: pt_fresh_star_bij[OF pt_name_inst, OF at_name_inst])
        with \<open>x \<sharp> A\<^sub>Q'\<close> \<open>y \<sharp> A\<^sub>Q'\<close> have "A\<^sub>Q' \<sharp>* ([(x, y)] \<bullet> Q)" by simp
        ultimately have "\<Psi> \<rhd> (P \<parallel> ([(x, y)] \<bullet> Q)) \<longmapsto>\<questiondown>M\<lparr>N\<rparr> \<prec> (P' \<parallel> ([(x, y)] \<bullet> Q'))"
          using \<open>A\<^sub>P \<sharp>* \<Psi>\<close> \<open>A\<^sub>P \<sharp>* P\<close>  \<open>A\<^sub>P \<sharp>* A\<^sub>Q'\<close> \<open>A\<^sub>Q' \<sharp>* \<Psi>\<close> \<open>A\<^sub>Q' \<sharp>* P\<close> \<open>A\<^sub>P \<sharp>* M\<close> \<open>A\<^sub>Q' \<sharp>* M\<close>
          by(intro BrMerge)
        with\<open>y \<sharp> \<Psi>\<close> \<open>y \<sharp> M\<close> \<open>y \<sharp> N\<close> have "\<Psi> \<rhd> \<lparr>\<nu>y\<rparr>(P \<parallel> ([(x, y)] \<bullet> Q)) \<longmapsto>\<questiondown>M\<lparr>N\<rparr> \<prec> \<lparr>\<nu>y\<rparr>(P' \<parallel> ([(x, y)] \<bullet> Q'))"
          by(intro Scope) auto
        moreover from \<open>x \<sharp> P\<close> \<open>y \<sharp> P\<close> \<open>y \<sharp> Q\<close> have "\<lparr>\<nu>y\<rparr>(P \<parallel> ([(x, y)] \<bullet> Q)) = \<lparr>\<nu>x\<rparr>([(x, y)] \<bullet> (P \<parallel> ([(x, y)] \<bullet> Q)))"
          by(subst alphaRes[of x]) (auto simp add: calc_atm fresh_left name_swap)
        moreover with \<open>x \<sharp> P\<close> \<open>y \<sharp> P\<close> have "\<lparr>\<nu>y\<rparr>(P \<parallel> ([(x, y)] \<bullet> Q)) = \<lparr>\<nu>x\<rparr>(P \<parallel> Q)"
          by(simp add: eqvts)
        moreover from \<open>x \<sharp> P'\<close> \<open>y \<sharp> P'\<close> \<open>y \<sharp> Q'\<close> have "\<lparr>\<nu>y\<rparr>(P' \<parallel> ([(x, y)] \<bullet> Q')) =  \<lparr>\<nu>x\<rparr>(P' \<parallel> Q')"
          by(subst alphaRes[of y]) (auto simp add: resChainFresh calc_atm eqvts fresh_left name_swap)
        ultimately have finTrans: "\<Psi> \<rhd> \<lparr>\<nu>x\<rparr>(P \<parallel> Q) \<longmapsto>\<questiondown>M\<lparr>N\<rparr> \<prec> \<lparr>\<nu>x\<rparr>(P' \<parallel> Q')"
          by simp
        from \<open>x \<sharp> \<Psi>\<close> \<open>x \<sharp> P'\<close> have "[x] \<sharp>* P'" and "[x] \<sharp>* \<Psi>" by simp+
        then have "(\<Psi>, \<lparr>\<nu>*[x]\<rparr>(P' \<parallel> Q'), (P' \<parallel> (\<lparr>\<nu>*[x]\<rparr>Q'))) \<in> Rel"
          by(rule C4)
        then have "(\<Psi>, \<lparr>\<nu>x\<rparr>(P' \<parallel> Q'), (P' \<parallel> \<lparr>\<nu>x\<rparr>Q')) \<in> Rel"
          by simp
        with finTrans show ?case by blast
      qed
    next
      case(cBrComm1 \<Psi>\<^sub>Q M N P' A\<^sub>P \<Psi>\<^sub>P xvec xQ' A\<^sub>Q)
      have QTrans: "\<Psi> \<otimes> \<Psi>\<^sub>P \<rhd> \<lparr>\<nu>x\<rparr>Q \<longmapsto>\<exclamdown>M\<lparr>\<nu>*xvec\<rparr>\<langle>N\<rangle> \<prec> xQ'" and FrQ: "extractFrame(\<lparr>\<nu>x\<rparr>Q) = \<langle>A\<^sub>Q, \<Psi>\<^sub>Q\<rangle>" by fact+
      have PTrans: "\<Psi> \<otimes> \<Psi>\<^sub>Q \<rhd> P \<longmapsto>\<questiondown>M\<lparr>N\<rparr> \<prec> P'" and FrP: "extractFrame P = \<langle>A\<^sub>P, \<Psi>\<^sub>P\<rangle>" by fact+
      from \<open>bn \<alpha> \<sharp>* x\<close> \<open>\<exclamdown>M\<lparr>\<nu>*xvec\<rparr>\<langle>N\<rangle> = \<alpha>\<close> have "x \<sharp> xvec" by force
      have "x \<sharp> \<lparr>\<nu>x\<rparr>Q" by(simp add: abs_fresh)
      with QTrans have "x \<sharp> N" and "x \<sharp> xQ'" using \<open>x \<sharp> xvec\<close> \<open>xvec \<sharp>* M\<close> \<open>distinct xvec\<close>
        by(force intro: broutputFreshDerivative)+
      from PTrans \<open>x \<sharp> P\<close> \<open>x \<sharp> N\<close>  have "x \<sharp> P'" by(rule brinputFreshDerivative)
      from \<open>x \<sharp> \<lparr>\<nu>x\<rparr>Q\<close> FrQ \<open>A\<^sub>Q \<sharp>* x\<close> have "x \<sharp> \<Psi>\<^sub>Q"
        by(drule_tac extractFrameFresh) auto
      from \<open>x \<sharp> P\<close> FrP \<open>A\<^sub>P \<sharp>* x\<close> have "x \<sharp> \<Psi>\<^sub>P"
        by(drule_tac extractFrameFresh) auto
      from \<open>A\<^sub>P \<sharp>* \<lparr>\<nu>x\<rparr>Q\<close> \<open>A\<^sub>P \<sharp>* x\<close> have "A\<^sub>P \<sharp>* Q" by simp
      from \<open>A\<^sub>Q \<sharp>* \<lparr>\<nu>x\<rparr>Q\<close> \<open>A\<^sub>Q \<sharp>* x\<close> have "A\<^sub>Q \<sharp>* Q" by simp
      note QTrans
      moreover from \<open>x \<sharp> \<Psi>\<close> \<open>x \<sharp> \<Psi>\<^sub>P\<close> have "x \<sharp> \<Psi> \<otimes> \<Psi>\<^sub>P" by force
      moreover from \<open>x \<sharp> xvec\<close> have "xvec \<sharp>* x" by simp
      from \<open>x \<sharp> \<alpha>\<close> \<open>\<exclamdown>M\<lparr>\<nu>*xvec\<rparr>\<langle>N\<rangle> = \<alpha>\<close> have "x \<sharp> \<exclamdown>M\<lparr>\<nu>*xvec\<rparr>\<langle>N\<rangle>" by simp
      moreover note \<open>x \<sharp> xQ'\<close>

      moreover from \<open>xvec \<sharp>* \<Psi>\<close> \<open>xvec \<sharp>* \<Psi>\<^sub>P\<close> have "xvec \<sharp>* (\<Psi> \<otimes> \<Psi>\<^sub>P)" by force
      moreover from \<open>xvec \<sharp>* \<lparr>\<nu>x\<rparr>Q\<close> \<open>x \<sharp> xvec\<close> have "xvec \<sharp>* Q" by simp
      moreover note \<open>xvec \<sharp>* M\<close>

      moreover from \<open>xvec \<sharp>* \<Psi>\<close> \<open>xvec \<sharp>* \<Psi>\<^sub>P\<close> have "bn(\<exclamdown>M\<lparr>\<nu>*xvec\<rparr>\<langle>N\<rangle>) \<sharp>* (\<Psi> \<otimes> \<Psi>\<^sub>P)" by force
      moreover from \<open>xvec \<sharp>* \<lparr>\<nu>x\<rparr>Q\<close> \<open>x \<sharp> xvec\<close> have "bn(\<exclamdown>M\<lparr>\<nu>*xvec\<rparr>\<langle>N\<rangle>) \<sharp>* Q" by simp
      moreover from \<open>xvec \<sharp>* P\<close> have "bn(\<exclamdown>M\<lparr>\<nu>*xvec\<rparr>\<langle>N\<rangle>) \<sharp>* P" by simp
      from \<open>xvec \<sharp>* \<Psi>\<close> have "bn(\<exclamdown>M\<lparr>\<nu>*xvec\<rparr>\<langle>N\<rangle>) \<sharp>* \<Psi>" by simp
      from \<open>A\<^sub>Q \<sharp>* xvec\<close> \<open>A\<^sub>Q \<sharp>* M\<close> \<open>A\<^sub>Q \<sharp>* N\<close> have "A\<^sub>Q \<sharp>* (\<exclamdown>M\<lparr>\<nu>*xvec\<rparr>\<langle>N\<rangle>)" by simp
      have "object(\<exclamdown>M\<lparr>\<nu>*xvec\<rparr>\<langle>N\<rangle>) = Some N" by simp
      have "bn(\<exclamdown>M\<lparr>\<nu>*xvec\<rparr>\<langle>N\<rangle>) = xvec" by simp
      have "subject(\<exclamdown>M\<lparr>\<nu>*xvec\<rparr>\<langle>N\<rangle>) = Some M" by simp
      from \<open>xvec \<sharp>* M\<close> have "bn(\<exclamdown>M\<lparr>\<nu>*xvec\<rparr>\<langle>N\<rangle>) \<sharp>* subject(\<exclamdown>M\<lparr>\<nu>*xvec\<rparr>\<langle>N\<rangle>)" by simp
      ultimately show ?case
        using \<open>x \<sharp> \<exclamdown>M\<lparr>\<nu>*xvec\<rparr>\<langle>N\<rangle>\<close> \<open>bn(\<exclamdown>M\<lparr>\<nu>*xvec\<rparr>\<langle>N\<rangle>) \<sharp>* P\<close> \<open>bn(\<exclamdown>M\<lparr>\<nu>*xvec\<rparr>\<langle>N\<rangle>) \<sharp>* \<Psi>\<close> \<open>object(\<exclamdown>M\<lparr>\<nu>*xvec\<rparr>\<langle>N\<rangle>) = Some N\<close>
          \<open>bn(\<exclamdown>M\<lparr>\<nu>*xvec\<rparr>\<langle>N\<rangle>) = xvec\<close> \<open>subject(\<exclamdown>M\<lparr>\<nu>*xvec\<rparr>\<langle>N\<rangle>) = Some M\<close> \<open>A\<^sub>Q \<sharp>* (\<exclamdown>M\<lparr>\<nu>*xvec\<rparr>\<langle>N\<rangle>)\<close>
      proof(induct rule: resBrOutputCases')
      	case(cBrOpen M'' xvec1 xvec2 y N' Q')
        then have Eq: "\<exclamdown>M\<lparr>\<nu>*xvec\<rparr>\<langle>N\<rangle> = \<exclamdown>M''\<lparr>\<nu>*(xvec1 @ y # xvec2)\<rparr>\<langle>N'\<rangle>" by simp
        from \<open>x \<sharp> \<exclamdown>M\<lparr>\<nu>*xvec\<rparr>\<langle>N\<rangle>\<close> Eq have "x \<sharp> xvec1" and "x \<noteq> y" and "x \<sharp> xvec2" and "x \<sharp> M''"
          by simp+
        from \<open>bn(\<exclamdown>M\<lparr>\<nu>*xvec\<rparr>\<langle>N\<rangle>) \<sharp>* P\<close> Eq have "(xvec1@xvec2) \<sharp>* P" and "y \<sharp> P" by simp+
        from \<open>A\<^sub>Q \<sharp>* (\<exclamdown>M\<lparr>\<nu>*xvec\<rparr>\<langle>N\<rangle>)\<close> Eq have "(xvec1@xvec2) \<sharp>* A\<^sub>Q" and "y \<sharp> A\<^sub>Q" and "A\<^sub>Q \<sharp>* M''" by simp+
        from \<open>bn(\<exclamdown>M\<lparr>\<nu>*xvec\<rparr>\<langle>N\<rangle>) \<sharp>* \<Psi>\<close> Eq have "(xvec1@xvec2) \<sharp>* \<Psi>" and "y \<sharp> \<Psi>" by simp+
        from Eq have "N = N'" and "xvec = xvec1@y#xvec2" and "M = M''" by(simp add: action.inject)+
        from \<open>x \<sharp> P\<close> \<open>y \<sharp> P\<close> \<open>x \<noteq> y\<close> \<open>\<Psi> \<otimes> \<Psi>\<^sub>Q \<rhd> P \<longmapsto>\<questiondown>M\<lparr>N\<rparr> \<prec> P'\<close>
        have "\<Psi> \<otimes> \<Psi>\<^sub>Q \<rhd> P \<longmapsto>\<questiondown>M\<lparr>([(y, x)] \<bullet> N)\<rparr> \<prec> ([(y, x)] \<bullet> P')"
          by(intro brinputAlpha[where xvec="[y]"]) (auto simp add: calc_atm)
        then have PTrans: "\<Psi> \<otimes> \<Psi>\<^sub>Q \<rhd> P \<longmapsto>\<questiondown>M\<lparr>([(x, y)] \<bullet> N)\<rparr> \<prec> ([(x, y)] \<bullet> P')"
          by(simp add: name_swap)

        from \<open>\<Psi> \<otimes> \<Psi>\<^sub>P \<rhd> [(x, y)] \<bullet> Q \<longmapsto> \<exclamdown>M''\<lparr>\<nu>*(xvec1 @ xvec2)\<rparr>\<langle>N'\<rangle> \<prec> Q'\<close>
        have "[(x, y)] \<bullet> (\<Psi> \<otimes> \<Psi>\<^sub>P \<rhd> [(x, y)] \<bullet> Q \<longmapsto> \<exclamdown>M''\<lparr>\<nu>*(xvec1 @ xvec2)\<rparr>\<langle>N'\<rangle> \<prec> Q')"
          by simp
        then have "[(x, y)] \<bullet> (\<Psi> \<otimes> \<Psi>\<^sub>P) \<rhd> ([(x, y)] \<bullet> ([(x, y)] \<bullet> Q)) \<longmapsto> \<exclamdown>([(x, y)] \<bullet> M'')\<lparr>\<nu>*([(x, y)] \<bullet> (xvec1 @ xvec2))\<rparr>\<langle>([(x, y)] \<bullet> N')\<rangle> \<prec> [(x, y)] \<bullet> Q'"
          by(simp add: eqvts)
        with \<open>x \<sharp> (\<Psi> \<otimes> \<Psi>\<^sub>P)\<close> \<open>y \<sharp> (\<Psi> \<otimes> \<Psi>\<^sub>P)\<close> \<open>x \<sharp> xvec1\<close> \<open>y \<sharp> xvec1\<close> \<open>x \<sharp> xvec2\<close> \<open>y \<sharp> xvec2\<close> \<open>x \<sharp> M''\<close> \<open>y \<sharp> M''\<close>
        have QTrans: "\<Psi> \<otimes> \<Psi>\<^sub>P \<rhd> Q \<longmapsto> \<exclamdown>M''\<lparr>\<nu>*(xvec1 @ xvec2)\<rparr>\<langle>([(x, y)] \<bullet> N')\<rangle> \<prec> [(x, y)] \<bullet> Q'"
          by simp
        with \<open>A\<^sub>Q \<sharp>* x\<close> \<open>y \<sharp> A\<^sub>Q\<close> \<open>distinct xvec1\<close> \<open>distinct xvec2\<close> \<open>xvec1 \<sharp>* xvec2\<close> \<open>xvec1 \<sharp>* M''\<close> \<open>xvec2 \<sharp>* M''\<close>
          \<open>(xvec1@xvec2) \<sharp>* A\<^sub>Q\<close>
        have "A\<^sub>Q \<sharp>* ([(x, y)] \<bullet> Q')" using \<open>A\<^sub>Q \<sharp>* Q\<close>
          by(elim broutputFreshChainDerivative(2)) (assumption | simp)+

        from \<open>extractFrame(\<lparr>\<nu>x\<rparr>Q) = \<langle>A\<^sub>Q, \<Psi>\<^sub>Q\<rangle>\<close> have FrxQ: "\<lparr>\<nu>x\<rparr>(extractFrame Q) = \<langle>A\<^sub>Q, \<Psi>\<^sub>Q\<rangle>" by simp
        then obtain z A\<^sub>Q' where A: "A\<^sub>Q = z#A\<^sub>Q'" by(cases A\<^sub>Q) auto
        with \<open>A\<^sub>Q \<sharp>* \<Psi>\<close> \<open>A\<^sub>Q \<sharp>* P\<close> \<open>A\<^sub>Q \<sharp>* P'\<close> \<open>A\<^sub>Q \<sharp>* \<Psi>\<^sub>P\<close> \<open>A\<^sub>Q \<sharp>* Q\<close> \<open>(xvec1@xvec2) \<sharp>* A\<^sub>Q\<close> \<open>A\<^sub>Q \<sharp>* M''\<close> \<open>A\<^sub>Q \<sharp>* ([(x, y)] \<bullet> Q')\<close> \<open>y \<sharp> A\<^sub>Q\<close> \<open>A\<^sub>Q \<sharp>* N\<close>
        have "A\<^sub>Q' \<sharp>* \<Psi>" and "A\<^sub>Q' \<sharp>* P" and "A\<^sub>Q' \<sharp>* \<Psi>\<^sub>P" and "A\<^sub>Q' \<sharp>* Q"
          and "z \<sharp> \<Psi>" and "z \<sharp> P" and "z \<sharp> P'" and "z \<sharp> \<Psi>\<^sub>P" and "z \<sharp> Q" and "z \<sharp> xvec1" and "z \<sharp> xvec2"
          and "z \<sharp> M''" and "z \<sharp> ([(x, y)] \<bullet> Q')" and "A\<^sub>Q' \<sharp>* M''" and "z \<noteq> y" and "z \<sharp> (xvec1@xvec2)"
          by auto
        from A \<open>A\<^sub>P \<sharp>* A\<^sub>Q\<close> have "A\<^sub>P \<sharp>* A\<^sub>Q'" and "z \<sharp> A\<^sub>P" by simp+
        from A \<open>A\<^sub>Q \<sharp>* x\<close> have "x \<noteq> z" and "x \<sharp> A\<^sub>Q'" by simp+

        from \<open>A\<^sub>Q \<sharp>* (\<exclamdown>M\<lparr>\<nu>*xvec\<rparr>\<langle>N\<rangle>)\<close> A have "z \<sharp> M" and "z \<sharp> xvec" and "z \<sharp> N" by simp+

        from \<open>y \<in> supp N'\<close> \<open>N = N'\<close> have "y \<in> supp N" by simp
        then have "x \<in> supp ([(x, y)] \<bullet> N)"
          by (rule swap_supp)
        then have zsupp: "z \<in> supp ([(x, z)] \<bullet> [(x, y)] \<bullet> N)"
          by (rule swap_supp')

        from \<open>distinct A\<^sub>Q\<close> A have "z \<sharp> A\<^sub>Q'"
          by(induct A\<^sub>Q') (auto simp add: fresh_list_nil fresh_list_cons)
        from PTrans \<open>x \<sharp> P\<close> \<open>z \<sharp> P\<close> \<open>x \<noteq> z\<close> have "\<Psi> \<otimes> \<Psi>\<^sub>Q \<rhd> P \<longmapsto>\<questiondown>M\<lparr>([(x, z)] \<bullet> [(x, y)] \<bullet> N)\<rparr> \<prec> ([(x, z)] \<bullet> [(x, y)] \<bullet> P')"
          by(elim brinputAlpha[where xvec="[x]"]) (auto simp add: calc_atm)
        moreover note FrP
        moreover from QTrans have "([(x, z)] \<bullet> (\<Psi> \<otimes> \<Psi>\<^sub>P)) \<rhd> ([(x, z)] \<bullet> Q) \<longmapsto>([(x, z)] \<bullet> (\<exclamdown>M''\<lparr>\<nu>*(xvec1@xvec2)\<rparr>\<langle>([(x, y)] \<bullet> N')\<rangle> \<prec> ([(x, y)] \<bullet> Q')))"
          by(rule semantics.eqvt)
        with \<open>x \<sharp> \<Psi>\<close> \<open>z \<sharp> \<Psi>\<close> \<open>x \<sharp> \<Psi>\<^sub>P\<close> \<open>z \<sharp> \<Psi>\<^sub>P\<close> \<open>x \<sharp> M''\<close> \<open>z \<sharp> M''\<close> \<open>x \<sharp> xvec1\<close> \<open>x \<sharp> xvec2\<close> \<open>z \<sharp> xvec1\<close> \<open>z \<sharp> xvec2\<close>
        have "\<Psi> \<otimes> \<Psi>\<^sub>P \<rhd> ([(x, z)] \<bullet> Q) \<longmapsto>\<exclamdown>M''\<lparr>\<nu>*(xvec1@xvec2)\<rparr>\<langle>([(x, z)] \<bullet> [(x, y)] \<bullet> N')\<rangle> \<prec> ([(x, z)] \<bullet> [(x, y)] \<bullet> Q')"
          by(simp add: eqvts)
        moreover from A \<open>A\<^sub>Q \<sharp>* x\<close> FrxQ have "extractFrame([(x, z)] \<bullet> Q) = \<langle>A\<^sub>Q', \<Psi>\<^sub>Q\<rangle>"
          by(clarsimp simp add: alpha' eqvts frame.inject fresh_list_cons name_swap)
        moreover from \<open>A\<^sub>P \<sharp>* Q\<close> have "([(x, z)] \<bullet> A\<^sub>P) \<sharp>* ([(x, z)] \<bullet> Q)"
          by(simp add: pt_fresh_star_bij[OF pt_name_inst, OF at_name_inst])
        with \<open>A\<^sub>P \<sharp>* x\<close> \<open>z \<sharp> A\<^sub>P\<close> have "A\<^sub>P \<sharp>* ([(x, z)] \<bullet> Q)" by simp
        moreover from \<open>A\<^sub>Q' \<sharp>* Q\<close> have "([(x, z)] \<bullet> A\<^sub>Q') \<sharp>* ([(x, z)] \<bullet> Q)"
          by(simp add: pt_fresh_star_bij[OF pt_name_inst, OF at_name_inst])
        with \<open>x \<sharp> A\<^sub>Q'\<close> \<open>z \<sharp> A\<^sub>Q'\<close> have "A\<^sub>Q' \<sharp>* ([(x, z)] \<bullet> Q)" by simp
        ultimately have "\<Psi> \<rhd> (P \<parallel> ([(x, z)] \<bullet> Q)) \<longmapsto>\<exclamdown>M\<lparr>\<nu>*(xvec1@xvec2)\<rparr>\<langle>([(x, z)] \<bullet> [(x, y)] \<bullet> N)\<rangle> \<prec> (([(x, z)] \<bullet> [(x, y)] \<bullet> P') \<parallel> ([(x, z)] \<bullet> [(x, y)] \<bullet> Q'))"
          using \<open>M=M''\<close> \<open>N=N'\<close> \<open>A\<^sub>P \<sharp>* \<Psi>\<close> \<open>A\<^sub>P \<sharp>* P\<close>  \<open>A\<^sub>P \<sharp>* A\<^sub>Q'\<close> \<open>A\<^sub>Q' \<sharp>* \<Psi>\<close> \<open>A\<^sub>Q' \<sharp>* P\<close> \<open>(xvec1@xvec2) \<sharp>* P\<close> \<open>A\<^sub>P \<sharp>* M\<close> \<open>A\<^sub>Q' \<sharp>* M''\<close>
          by(intro BrComm1) (assumption | simp)+
        then have permTrans: "\<Psi> \<rhd> \<lparr>\<nu>z\<rparr>(P \<parallel> ([(x, z)] \<bullet> Q)) \<longmapsto>\<exclamdown>M\<lparr>\<nu>*(xvec1@z#xvec2)\<rparr>\<langle>([(x, z)] \<bullet> [(x, y)] \<bullet> N)\<rangle> \<prec> (([(x, z)] \<bullet> [(x, y)] \<bullet> P') \<parallel> ([(x, z)] \<bullet> [(x, y)] \<bullet> Q'))"
          using zsupp \<open>z \<sharp> \<Psi>\<close> \<open>z \<sharp> M\<close> \<open>z \<sharp> xvec1\<close> \<open>z \<sharp> xvec2\<close>
          by(rule BrOpen)

        from \<open>x \<sharp> P\<close> \<open>z \<sharp> P\<close> \<open>z \<sharp> Q\<close> have "\<lparr>\<nu>z\<rparr>(P \<parallel> ([(x, z)] \<bullet> Q)) = \<lparr>\<nu>x\<rparr>([(x, z)] \<bullet> (P \<parallel> ([(x, z)] \<bullet> Q)))"
          by(subst alphaRes[of x]) (auto simp add: calc_atm fresh_left name_swap)
        with \<open>x \<sharp> P\<close> \<open>z \<sharp> P\<close> have "\<lparr>\<nu>z\<rparr>(P \<parallel> ([(x, z)] \<bullet> Q)) = \<lparr>\<nu>x\<rparr>(P \<parallel> Q)"
          by(simp add: eqvts)
        with permTrans have permTrans2: "\<Psi> \<rhd> \<lparr>\<nu>x\<rparr>(P \<parallel> Q) \<longmapsto>\<exclamdown>M\<lparr>\<nu>*(xvec1@z#xvec2)\<rparr>\<langle>([(x, z)] \<bullet> [(x, y)] \<bullet> N)\<rangle> \<prec> (([(x, z)] \<bullet> [(x, y)] \<bullet> P') \<parallel> ([(x, z)] \<bullet> [(x, y)] \<bullet> Q'))"
          by simp
        then have "\<Psi> \<rhd> \<lparr>\<nu>x\<rparr>(P \<parallel> Q) \<longmapsto> RBrOut M (\<lparr>\<nu>*(xvec1@z#xvec2)\<rparr>([(x, z)] \<bullet> [(x, y)] \<bullet> N) \<prec>' (([(x, z)] \<bullet> [(x, y)] \<bullet> P') \<parallel> ([(x, z)] \<bullet> [(x, y)] \<bullet> Q')))"
          by(simp add: residualInject)
        then have permTrans3: "\<Psi> \<rhd> \<lparr>\<nu>x\<rparr>(P \<parallel> Q) \<longmapsto> RBrOut M (\<lparr>\<nu>*(xvec1@z#xvec2)\<rparr> (([(x, z)] \<bullet> [(x, y)] \<bullet> N) \<prec>' ([(x, z)] \<bullet> [(x, y)] \<bullet> (P' \<parallel> Q'))))"
          by simp
        from \<open>z \<sharp> N\<close> \<open>x \<noteq> z\<close> \<open>z \<noteq> y\<close>
        have "z \<sharp> ([(x, y)] \<bullet> N)"
          by (metis calc_atm(2) calc_atm(3) fresh_right name_prm_name.simps(2) name_prm_name_def singleton_rev_conv swap_name_def)
        from \<open>z \<sharp> P'\<close> \<open>x \<noteq> z\<close> \<open>z \<noteq> y\<close>
        have "z \<sharp> ([(x, y)] \<bullet> P')"
          by (metis calc_atm(2) calc_atm(3) fresh_right name_prm_name.simps(2) name_prm_name_def singleton_rev_conv swap_name_def)
        from \<open>z \<sharp> ([(x, y)] \<bullet> N)\<close> have "x \<sharp> ([(x, z)] \<bullet> [(x, y)] \<bullet> N)"
          by (metis calc_atm(2) calc_atm(3) fresh_right name_prm_name.simps(2) name_prm_name_def singleton_rev_conv swap_name_def)
        from \<open>z \<sharp> ([(x, y)] \<bullet> P')\<close> have "x \<sharp> ([(x, z)] \<bullet> [(x, y)] \<bullet> P')"
          by (metis calc_atm(2) calc_atm(3) fresh_right name_prm_name.simps(2) name_prm_name_def singleton_rev_conv swap_name_def)
        moreover from \<open>z \<sharp> [(x, y)] \<bullet> Q'\<close>
        have "x \<sharp> ([(x, z)] \<bullet> [(x, y)] \<bullet> Q')"
          by (metis calc_atm(2) calc_atm(3) fresh_right name_prm_name.simps(2) name_prm_name_def singleton_rev_conv swap_name_def)
        ultimately have "x \<sharp> ([(x, z)] \<bullet> [(x, y)] \<bullet> (P' \<parallel> Q'))"
          by simp
        have "z \<in> set ((xvec1@z#xvec2))"
          by simp
        from \<open>x \<sharp> ([(x, z)] \<bullet> [(x, y)] \<bullet> N)\<close> \<open>x \<sharp> ([(x, z)] \<bullet> [(x, y)] \<bullet> (P' \<parallel> Q'))\<close> \<open>z \<in> set ((xvec1@z#xvec2))\<close>
        have eq1: "(\<lparr>\<nu>*(xvec1@z#xvec2)\<rparr> (([(x, z)] \<bullet> [(x, y)] \<bullet> N) \<prec>' ([(x, z)] \<bullet> [(x, y)] \<bullet> (P' \<parallel> Q')))) = (\<lparr>\<nu>*([(z, x)] \<bullet> (xvec1@z#xvec2))\<rparr> (([(z, x)] \<bullet> [(x, z)] \<bullet> [(x, y)] \<bullet> N) \<prec>' ([(z, x)] \<bullet> [(x, z)] \<bullet> [(x, y)] \<bullet> (P' \<parallel> Q'))))"
          by(rule boundOutputChainSwap)
        have eq2: "(\<lparr>\<nu>*([(z, x)] \<bullet> (xvec1@z#xvec2))\<rparr> (([(z, x)] \<bullet> [(x, z)] \<bullet> [(x, y)] \<bullet> N) \<prec>' ([(z, x)] \<bullet> [(x, z)] \<bullet> [(x, y)] \<bullet> (P' \<parallel> Q')))) = (\<lparr>\<nu>*([(z, x)] \<bullet> (xvec1@z#xvec2))\<rparr> (([(x, y)] \<bullet> N) \<prec>' ([(x, y)] \<bullet> (P' \<parallel> Q'))))"
          by auto (metis perm_swap(2))+
        from \<open>x \<sharp> xvec1\<close> \<open>x \<sharp> xvec2\<close> \<open>z \<sharp> xvec1\<close> \<open>z \<sharp> xvec2\<close>
        have "([(z, x)] \<bullet> (xvec1@z#xvec2)) = (xvec1@x#xvec2)"
          by(simp add: eqvts swap_simps)
        then have eq3: "(\<lparr>\<nu>*([(z, x)] \<bullet> (xvec1@z#xvec2))\<rparr> (([(x, y)] \<bullet> N) \<prec>' ([(x, y)] \<bullet> (P' \<parallel> Q')))) = (\<lparr>\<nu>*(xvec1@x#xvec2)\<rparr> (([(x, y)] \<bullet> N) \<prec>' ([(x, y)] \<bullet> (P' \<parallel> Q'))))"
          by simp

        from permTrans3 eq1 eq2 eq3 have noXZTrans: "\<Psi> \<rhd> \<lparr>\<nu>x\<rparr>(P \<parallel> Q) \<longmapsto> RBrOut M (\<lparr>\<nu>*(xvec1@x#xvec2)\<rparr> (([(x, y)] \<bullet> N) \<prec>' ([(x, y)] \<bullet> (P' \<parallel> Q'))))"
          by simp

        from \<open>x \<sharp> N\<close>
        have "y \<sharp> ([(x, y)] \<bullet> N)"
          by (metis calc_atm(2) fresh_right name_prm_name.simps(2) name_prm_name_def singleton_rev_conv swap_name_def swap_simps(2))
        moreover from \<open>x \<sharp> P'\<close> \<open>x \<sharp> Q'\<close>
        have "y \<sharp> ([(x, y)] \<bullet> (P' \<parallel> Q'))"
          by (metis fresh_left psi.fresh(5) singleton_rev_conv swap_simps(2))
        moreover have "x \<in> set (xvec1@x#xvec2)"
          by simp
        ultimately have eq1: "\<lparr>\<nu>*(xvec1@x#xvec2)\<rparr>([(x, y)] \<bullet> N) \<prec>' ([(x, y)] \<bullet> (P' \<parallel> Q')) = \<lparr>\<nu>*([(x, y)] \<bullet> (xvec1@x#xvec2))\<rparr>([(x, y)] \<bullet> [(x, y)] \<bullet> N) \<prec>' ([(x, y)] \<bullet> [(x, y)] \<bullet> (P' \<parallel> Q'))"
          by(rule boundOutputChainSwap)
        have eq2: "\<lparr>\<nu>*([(x, y)] \<bullet> (xvec1@x#xvec2))\<rparr>([(x, y)] \<bullet> [(x, y)] \<bullet> N) \<prec>' ([(x, y)] \<bullet> [(x, y)] \<bullet> (P' \<parallel> Q')) = \<lparr>\<nu>*([(x, y)] \<bullet> (xvec1@x#xvec2))\<rparr>N \<prec>' (P' \<parallel> Q')"
          by simp
        from \<open>x \<sharp> xvec1\<close> \<open>x \<sharp> xvec2\<close> \<open>y \<sharp> xvec1\<close> \<open>y \<sharp> xvec2\<close>
        have eq3: "([(x, y)] \<bullet> (xvec1@x#xvec2)) = (xvec1@y#xvec2)"
          by(simp add: eqvts swap_simps)

        from eq1 eq2 eq3 noXZTrans have "\<Psi> \<rhd> \<lparr>\<nu>x\<rparr>(P \<parallel> Q) \<longmapsto> RBrOut M (\<lparr>\<nu>*(xvec1@y#xvec2)\<rparr>N \<prec>' (P' \<parallel> Q'))"
          by simp
        then have "\<Psi> \<rhd> \<lparr>\<nu>x\<rparr>(P \<parallel> Q) \<longmapsto>\<exclamdown>M\<lparr>\<nu>*(xvec1@y#xvec2)\<rparr>\<langle>N\<rangle> \<prec> (P' \<parallel> Q')"
          by(simp add: residualInject)

        with \<open>xvec = xvec1@y#xvec2\<close>
        have "\<Psi> \<rhd> \<lparr>\<nu>x\<rparr>(P \<parallel> Q) \<longmapsto>\<exclamdown>M\<lparr>\<nu>*xvec\<rparr>\<langle>N\<rangle> \<prec> (P' \<parallel> Q')"
          by simp
        moreover have "(\<Psi>, P' \<parallel> Q', P' \<parallel> Q') \<in> Rel"
          by(rule C1)

        ultimately show ?case
          by force
      next
        case(cRes Q')
        from \<open>x \<sharp> \<exclamdown>M\<lparr>\<nu>*xvec\<rparr>\<langle>N\<rangle>\<close>
        have "x \<sharp> M" and "x \<sharp> xvec" and "x \<sharp> N"
          by simp+
        have QTrans: "\<Psi> \<otimes> \<Psi>\<^sub>P \<rhd> Q \<longmapsto>\<exclamdown>M\<lparr>\<nu>*xvec\<rparr>\<langle>N\<rangle> \<prec> Q'" by fact
        with \<open>A\<^sub>Q \<sharp>* Q\<close> \<open>A\<^sub>Q \<sharp>* xvec\<close> \<open>xvec \<sharp>* M\<close> \<open>distinct xvec\<close> have "A\<^sub>Q \<sharp>* Q'"
          by(force dest: broutputFreshChainDerivative)

        with \<open>extractFrame(\<lparr>\<nu>x\<rparr>Q) = \<langle>A\<^sub>Q, \<Psi>\<^sub>Q\<rangle>\<close> have FrxQ: "\<lparr>\<nu>x\<rparr>(extractFrame Q) = \<langle>A\<^sub>Q, \<Psi>\<^sub>Q\<rangle>" by simp
        then obtain y A\<^sub>Q' where A: "A\<^sub>Q = y#A\<^sub>Q'" by(cases A\<^sub>Q) auto
        with \<open>A\<^sub>Q \<sharp>* \<Psi>\<close> \<open>A\<^sub>Q \<sharp>* P\<close> \<open>A\<^sub>Q \<sharp>* P'\<close> \<open>A\<^sub>Q \<sharp>* \<Psi>\<^sub>P\<close> \<open>A\<^sub>Q \<sharp>* Q\<close> \<open>A\<^sub>Q \<sharp>* xvec\<close> \<open>A\<^sub>Q \<sharp>* M\<close> \<open>A\<^sub>Q \<sharp>* Q'\<close> \<open>A\<^sub>Q \<sharp>* N\<close>
        have "A\<^sub>Q' \<sharp>* \<Psi>" and "A\<^sub>Q' \<sharp>* P" and "A\<^sub>Q' \<sharp>* \<Psi>\<^sub>P" and "A\<^sub>Q' \<sharp>* Q" and "A\<^sub>Q \<sharp>* xvec" and "A\<^sub>Q \<sharp>* Q'"
          and "y \<sharp> \<Psi>" and "y \<sharp> P" and "y \<sharp> P'" and "y \<sharp> \<Psi>\<^sub>P" and "y \<sharp> Q" and "y \<sharp> xvec" and "y \<sharp> M" and "y \<sharp> Q'"
          and "A\<^sub>Q' \<sharp>* M" and "y \<sharp> N"
          by(simp)+
        from A \<open>A\<^sub>P \<sharp>* A\<^sub>Q\<close> have "A\<^sub>P \<sharp>* A\<^sub>Q'" and "y \<sharp> A\<^sub>P" by(simp add: fresh_star_list_cons)+
        from A \<open>A\<^sub>Q \<sharp>* x\<close> have "x \<noteq> y" and "x \<sharp> A\<^sub>Q'" by(simp add: fresh_list_cons)+

        with A \<open>distinct A\<^sub>Q\<close> have "y \<sharp> A\<^sub>Q'"
          by(induct A\<^sub>Q') (auto simp add: fresh_list_nil fresh_list_cons)

        from \<open>x \<sharp> N\<close> have "y \<sharp> [(x, y)] \<bullet> N"
          by (metis calc_atm(2) fresh_right name_prm_name.simps(2) name_prm_name_def singleton_rev_conv swap_name_def swap_simps(2))

        from \<open>x \<sharp> P\<close> \<open>y \<sharp> P\<close> \<open>x \<noteq> y\<close> \<open>\<Psi> \<otimes> \<Psi>\<^sub>Q \<rhd> P \<longmapsto>\<questiondown>M\<lparr>N\<rparr> \<prec> P'\<close>
        have "\<Psi> \<otimes> \<Psi>\<^sub>Q \<rhd> P \<longmapsto>\<questiondown>M\<lparr>([(y, x)] \<bullet> N)\<rparr> \<prec> [(y, x)] \<bullet> P'"
          by(elim brinputAlpha[where xvec="[y]"]) (auto simp add: calc_atm)
        then have "\<Psi> \<otimes> \<Psi>\<^sub>Q \<rhd> P \<longmapsto>\<questiondown>M\<lparr>([(x, y)] \<bullet> N)\<rparr> \<prec> [(x, y)] \<bullet> P'"
          by(simp add: name_swap)
        moreover note FrP
        moreover from  \<open>\<Psi> \<otimes> \<Psi>\<^sub>P \<rhd> Q \<longmapsto>\<exclamdown>M\<lparr>\<nu>*xvec\<rparr>\<langle>N\<rangle> \<prec> Q'\<close> have "([(x, y)] \<bullet> (\<Psi> \<otimes> \<Psi>\<^sub>P)) \<rhd> ([(x, y)] \<bullet> Q) \<longmapsto>([(x, y)] \<bullet> (\<exclamdown>M\<lparr>\<nu>*xvec\<rparr>\<langle>N\<rangle> \<prec> Q'))"
          by(rule semantics.eqvt)
        with \<open>x \<sharp> \<Psi>\<close> \<open>y \<sharp> \<Psi>\<close> \<open>x \<sharp> \<Psi>\<^sub>P\<close> \<open>y \<sharp> \<Psi>\<^sub>P\<close> \<open>x \<sharp> M\<close> \<open>y \<sharp> M\<close> \<open>x \<sharp> xvec\<close> \<open>y \<sharp> xvec\<close>
        have "\<Psi> \<otimes> \<Psi>\<^sub>P \<rhd> ([(x, y)] \<bullet> Q) \<longmapsto>\<exclamdown>M\<lparr>\<nu>*xvec\<rparr>\<langle>([(x, y)] \<bullet> N)\<rangle> \<prec> ([(x, y)] \<bullet> Q')"
          by(simp add: eqvts)
        moreover from A \<open>A\<^sub>Q \<sharp>* x\<close> FrxQ have FrQ: "extractFrame([(x, y)] \<bullet> Q) = \<langle>A\<^sub>Q', \<Psi>\<^sub>Q\<rangle>"
          by(clarsimp simp add: alpha' eqvts frame.inject fresh_list_cons name_swap)
        moreover from \<open>A\<^sub>P \<sharp>* Q\<close> have "([(x, y)] \<bullet> A\<^sub>P) \<sharp>* ([(x, y)] \<bullet> Q)" by(simp add: pt_fresh_star_bij[OF pt_name_inst, OF at_name_inst])
        with \<open>A\<^sub>P \<sharp>* x\<close> \<open>y \<sharp> A\<^sub>P\<close> have "A\<^sub>P \<sharp>* ([(x, y)] \<bullet> Q)" by simp
        moreover from \<open>A\<^sub>Q' \<sharp>* Q\<close> have "([(x, y)] \<bullet> A\<^sub>Q') \<sharp>* ([(x, y)] \<bullet> Q)" by(simp add: pt_fresh_star_bij[OF pt_name_inst, OF at_name_inst])
        with \<open>x \<sharp> A\<^sub>Q'\<close> \<open>y \<sharp> A\<^sub>Q'\<close> have "A\<^sub>Q' \<sharp>* ([(x, y)] \<bullet> Q)" by simp
        ultimately have "\<Psi> \<rhd> (P \<parallel> ([(x, y)] \<bullet> Q)) \<longmapsto>\<exclamdown>M\<lparr>\<nu>*xvec\<rparr>\<langle>([(x, y)] \<bullet> N)\<rangle> \<prec> ([(x, y)] \<bullet> P') \<parallel> ([(x, y)] \<bullet> Q')"
          using \<open>A\<^sub>P \<sharp>* \<Psi>\<close> \<open>A\<^sub>P \<sharp>* P\<close>  \<open>A\<^sub>P \<sharp>* A\<^sub>Q'\<close> \<open>A\<^sub>Q' \<sharp>* \<Psi>\<close> \<open>A\<^sub>Q' \<sharp>* P\<close> \<open>xvec \<sharp>* P\<close> \<open>A\<^sub>P \<sharp>* M\<close> \<open>A\<^sub>Q' \<sharp>* M\<close>
          by(intro BrComm1) (assumption | simp)+
        with\<open>y \<sharp> \<Psi>\<close> \<open>y \<sharp> M\<close> \<open>y \<sharp> xvec\<close> \<open>y \<sharp> [(x, y)] \<bullet> N\<close> have "\<Psi> \<rhd> \<lparr>\<nu>y\<rparr>(P \<parallel> ([(x, y)] \<bullet> Q)) \<longmapsto>\<exclamdown>M\<lparr>\<nu>*xvec\<rparr>\<langle>([(x, y)] \<bullet> N)\<rangle> \<prec> \<lparr>\<nu>y\<rparr>(([(x, y)] \<bullet> P') \<parallel> ([(x, y)] \<bullet> Q'))"
          by(intro Scope) auto
        moreover from \<open>x \<sharp> P\<close> \<open>y \<sharp> P\<close> \<open>y \<sharp> Q\<close> have "\<lparr>\<nu>y\<rparr>(P \<parallel> ([(x, y)] \<bullet> Q)) = \<lparr>\<nu>x\<rparr>([(x, y)] \<bullet> (P \<parallel> ([(x, y)] \<bullet> Q)))"
          by(subst alphaRes[of x]) (auto simp add: calc_atm fresh_left name_swap)
        with \<open>x \<sharp> P\<close> \<open>y \<sharp> P\<close> have "\<lparr>\<nu>y\<rparr>(P \<parallel> ([(x, y)] \<bullet> Q)) = \<lparr>\<nu>x\<rparr>(P \<parallel> Q)"
          by(simp add: eqvts)
        moreover from \<open>y \<sharp> P'\<close> \<open>y \<sharp> Q'\<close> \<open>x \<sharp> xvec\<close> \<open>y \<sharp> xvec\<close> have "\<lparr>\<nu>y\<rparr>(([(x, y)] \<bullet> P') \<parallel> ([(x, y)] \<bullet> Q')) =  \<lparr>\<nu>x\<rparr>(P' \<parallel> Q')"
          by(subst alphaRes[of y]) (auto simp add: resChainFresh calc_atm eqvts fresh_left name_swap)
        ultimately have "\<Psi> \<rhd> \<lparr>\<nu>x\<rparr>(P \<parallel> Q) \<longmapsto>\<exclamdown>M\<lparr>\<nu>*xvec\<rparr>\<langle>([(x, y)] \<bullet> N)\<rangle> \<prec> \<lparr>\<nu>x\<rparr>(P' \<parallel> Q')"
          by simp
        with \<open>x \<sharp> N\<close> \<open>y \<sharp> N\<close>
        have Trans: "\<Psi> \<rhd> \<lparr>\<nu>x\<rparr>(P \<parallel> Q) \<longmapsto>\<exclamdown>M\<lparr>\<nu>*xvec\<rparr>\<langle>N\<rangle> \<prec> \<lparr>\<nu>x\<rparr>(P' \<parallel> Q')"
          by simp
        from \<open>x \<sharp> P'\<close> \<open>x \<sharp> \<Psi>\<close>
        have "(\<Psi>, \<lparr>\<nu>*[x]\<rparr>(P' \<parallel> Q'), (P' \<parallel> (\<lparr>\<nu>*[x]\<rparr>Q'))) \<in> Rel"
          by(intro C4) simp+
        then have Relation: "(\<Psi>, \<lparr>\<nu>x\<rparr>(P' \<parallel> Q'), (P' \<parallel> (\<lparr>\<nu>x\<rparr>Q'))) \<in> Rel"
          by simp
        from Trans Relation show ?case
          by blast
      qed
    next
      case(cBrComm2 \<Psi>\<^sub>Q M xvec N P' A\<^sub>P \<Psi>\<^sub>P xQ' A\<^sub>Q)
      from \<open>x \<sharp> \<alpha>\<close> \<open>\<exclamdown>M\<lparr>\<nu>*xvec\<rparr>\<langle>N\<rangle> = \<alpha>\<close>
      have "x \<sharp> M" "x \<sharp> xvec" "x \<sharp> N"
        by force+
      have QTrans: "\<Psi> \<otimes> \<Psi>\<^sub>P \<rhd> \<lparr>\<nu>x\<rparr>Q \<longmapsto>\<questiondown>M\<lparr>N\<rparr> \<prec> xQ'" and FrQ: "extractFrame(\<lparr>\<nu>x\<rparr>Q) = \<langle>A\<^sub>Q, \<Psi>\<^sub>Q\<rangle>" by fact+
      have PTrans: "\<Psi> \<otimes> \<Psi>\<^sub>Q \<rhd> P \<longmapsto>\<exclamdown>M\<lparr>\<nu>*xvec\<rparr>\<langle>N\<rangle> \<prec> P'" and FrP: "extractFrame P = \<langle>A\<^sub>P, \<Psi>\<^sub>P\<rangle>" by fact+
      from PTrans \<open>x \<sharp> P\<close> have "x \<sharp> N" and "x \<sharp> P'" using \<open>x \<sharp> xvec\<close> \<open>xvec \<sharp>* M\<close> \<open>distinct xvec\<close>
        by(force intro: broutputFreshDerivative)+
      have "x \<sharp> \<lparr>\<nu>x\<rparr>Q" by(simp add: abs_fresh)
      with FrQ \<open>A\<^sub>Q \<sharp>* x\<close> have "x \<sharp> \<Psi>\<^sub>Q"
        by(drule_tac extractFrameFresh) auto
      from \<open>x \<sharp> P\<close> FrP \<open>A\<^sub>P \<sharp>* x\<close> have "x \<sharp> \<Psi>\<^sub>P"
        by(drule_tac extractFrameFresh) auto
      from \<open>A\<^sub>P \<sharp>* \<lparr>\<nu>x\<rparr>Q\<close> \<open>A\<^sub>P \<sharp>* x\<close> have "A\<^sub>P \<sharp>* Q" by simp
      from \<open>A\<^sub>Q \<sharp>* \<lparr>\<nu>x\<rparr>Q\<close> \<open>A\<^sub>Q \<sharp>* x\<close> have "A\<^sub>Q \<sharp>* Q" by simp
      from \<open>x \<sharp> xvec\<close> \<open>xvec \<sharp>* \<lparr>\<nu>x\<rparr>Q\<close> have "xvec \<sharp>* Q" by simp

      from \<open>\<Psi> \<otimes> \<Psi>\<^sub>Q \<rhd> P \<longmapsto> \<exclamdown>M\<lparr>\<nu>*xvec\<rparr>\<langle>N\<rangle> \<prec> P'\<close> have PResTrans: "\<Psi> \<otimes> \<Psi>\<^sub>Q \<rhd> P \<longmapsto> RBrOut M (\<lparr>\<nu>*xvec\<rparr>N \<prec>' P')"
        by(simp add: residualInject)

      note QTrans
      moreover from \<open>x \<sharp> \<Psi>\<close> \<open>x \<sharp> \<Psi>\<^sub>P\<close> have "x \<sharp> \<Psi> \<otimes> \<Psi>\<^sub>P" by force
      moreover note \<open>x \<sharp> M\<close> \<open>x \<sharp> N\<close>
      moreover from QTrans \<open>x \<sharp> N\<close> have "x \<sharp> xQ'" by(force dest: brinputFreshDerivative simp add: abs_fresh)
      ultimately show ?case
      proof(induct rule: resBrInputCases)
        case(cRes Q')
        have QTrans: "\<Psi> \<otimes> \<Psi>\<^sub>P \<rhd> Q \<longmapsto>\<questiondown>M\<lparr>N\<rparr> \<prec> Q'" by fact
        with \<open>A\<^sub>Q \<sharp>* Q\<close> \<open>A\<^sub>Q \<sharp>* N\<close> have "A\<^sub>Q \<sharp>* Q'"
          by(elim brinputFreshChainDerivative)

        with \<open>extractFrame(\<lparr>\<nu>x\<rparr>Q) = \<langle>A\<^sub>Q, \<Psi>\<^sub>Q\<rangle>\<close> have FrxQ: "\<lparr>\<nu>x\<rparr>(extractFrame Q) = \<langle>A\<^sub>Q, \<Psi>\<^sub>Q\<rangle>" by simp
        then obtain y A\<^sub>Q' where A: "A\<^sub>Q = y#A\<^sub>Q'" by(cases A\<^sub>Q) auto
        with \<open>A\<^sub>Q \<sharp>* \<Psi>\<close> \<open>A\<^sub>Q \<sharp>* P\<close> \<open>A\<^sub>Q \<sharp>* P'\<close> \<open>A\<^sub>Q \<sharp>* \<Psi>\<^sub>P\<close> \<open>A\<^sub>Q \<sharp>* Q\<close> \<open>A\<^sub>Q \<sharp>* xvec\<close> \<open>A\<^sub>Q \<sharp>* M\<close> \<open>A\<^sub>Q \<sharp>* Q'\<close> \<open>A\<^sub>Q \<sharp>* N\<close>
        have "A\<^sub>Q' \<sharp>* \<Psi>" and "A\<^sub>Q' \<sharp>* P" and "A\<^sub>Q' \<sharp>* \<Psi>\<^sub>P" and "A\<^sub>Q' \<sharp>* Q" and "A\<^sub>Q \<sharp>* xvec" and "A\<^sub>Q \<sharp>* Q'"
          and "y \<sharp> \<Psi>" and "y \<sharp> P" and "y \<sharp> P'" and "y \<sharp> \<Psi>\<^sub>P" and "y \<sharp> Q" and "y \<sharp> xvec" and "y \<sharp> M" and "y \<sharp> Q'" and "y \<sharp> N"
          and "A\<^sub>Q' \<sharp>* M"
          by(simp)+
        from A \<open>A\<^sub>P \<sharp>* A\<^sub>Q\<close> have "A\<^sub>P \<sharp>* A\<^sub>Q'" and "y \<sharp> A\<^sub>P" by(simp add: fresh_star_list_cons)+
        from A \<open>A\<^sub>Q \<sharp>* x\<close> have "x \<noteq> y" and "x \<sharp> A\<^sub>Q'" by(simp add: fresh_list_cons)+

        with A \<open>distinct A\<^sub>Q\<close> have "y \<sharp> A\<^sub>Q'"
          by(induct A\<^sub>Q') (auto simp add: fresh_list_nil fresh_list_cons)

        note PTrans FrP
        moreover from  \<open>\<Psi> \<otimes> \<Psi>\<^sub>P \<rhd> Q \<longmapsto>\<questiondown>M\<lparr>N\<rparr> \<prec> Q'\<close> have "([(x, y)] \<bullet> (\<Psi> \<otimes> \<Psi>\<^sub>P)) \<rhd> ([(x, y)] \<bullet> Q) \<longmapsto>([(x, y)] \<bullet> (\<questiondown>M\<lparr>N\<rparr> \<prec> Q'))"
          by(rule semantics.eqvt)
        with \<open>x \<sharp> \<Psi>\<close> \<open>y \<sharp> \<Psi>\<close> \<open>x \<sharp> \<Psi>\<^sub>P\<close> \<open>y \<sharp> \<Psi>\<^sub>P\<close> \<open>x \<sharp> M\<close> \<open>y \<sharp> M\<close> \<open>x \<sharp> N\<close> \<open>y \<sharp> N\<close>
        have "\<Psi> \<otimes> \<Psi>\<^sub>P \<rhd> ([(x, y)] \<bullet> Q) \<longmapsto>\<questiondown>M\<lparr>N\<rparr> \<prec> ([(x, y)] \<bullet> Q')"
          by(simp add: eqvts)
        moreover from A \<open>A\<^sub>Q \<sharp>* x\<close> FrxQ have FrQ: "extractFrame([(x, y)] \<bullet> Q) = \<langle>A\<^sub>Q', \<Psi>\<^sub>Q\<rangle>" and "y \<sharp> extractFrame Q"
          by(clarsimp simp add: alpha' eqvts frame.inject fresh_list_cons name_swap)+
        moreover from \<open>A\<^sub>P \<sharp>* Q\<close> have "([(x, y)] \<bullet> A\<^sub>P) \<sharp>* ([(x, y)] \<bullet> Q)" by(simp add: pt_fresh_star_bij[OF pt_name_inst, OF at_name_inst])
        with \<open>A\<^sub>P \<sharp>* x\<close> \<open>y \<sharp> A\<^sub>P\<close> have "A\<^sub>P \<sharp>* ([(x, y)] \<bullet> Q)" by simp
        moreover from \<open>A\<^sub>Q' \<sharp>* Q\<close> have "([(x, y)] \<bullet> A\<^sub>Q') \<sharp>* ([(x, y)] \<bullet> Q)" by(simp add: pt_fresh_star_bij[OF pt_name_inst, OF at_name_inst])
        with \<open>x \<sharp> A\<^sub>Q'\<close> \<open>y \<sharp> A\<^sub>Q'\<close> have "A\<^sub>Q' \<sharp>* ([(x, y)] \<bullet> Q)" by simp
        moreover from \<open>xvec \<sharp>* Q\<close> have "([(x, y)] \<bullet> xvec) \<sharp>* ([(x, y)] \<bullet> Q)" by(simp add: pt_fresh_star_bij[OF pt_name_inst, OF at_name_inst])
        with \<open>x \<sharp> xvec\<close> \<open>y \<sharp> xvec\<close> have "xvec \<sharp>* ([(x, y)] \<bullet> Q)" by simp
        ultimately have "\<Psi> \<rhd> (P \<parallel> ([(x, y)] \<bullet> Q)) \<longmapsto>\<exclamdown>M\<lparr>\<nu>*xvec\<rparr>\<langle>N\<rangle> \<prec> (P' \<parallel> ([(x, y)] \<bullet> Q'))"
          using \<open>A\<^sub>P \<sharp>* \<Psi>\<close> \<open>A\<^sub>P \<sharp>* P\<close>  \<open>A\<^sub>P \<sharp>* A\<^sub>Q'\<close> \<open>A\<^sub>Q' \<sharp>* \<Psi>\<close> \<open>A\<^sub>Q' \<sharp>* P\<close> \<open>A\<^sub>P \<sharp>* M\<close> \<open>A\<^sub>Q' \<sharp>* M\<close>
          by(intro BrComm2) (assumption | simp)+
        with \<open>y \<sharp> \<Psi>\<close> \<open>y \<sharp> M\<close> \<open>y \<sharp> xvec\<close> \<open>y \<sharp> N\<close> have "\<Psi> \<rhd> \<lparr>\<nu>y\<rparr>(P \<parallel> ([(x, y)] \<bullet> Q)) \<longmapsto>\<exclamdown>M\<lparr>\<nu>*xvec\<rparr>\<langle>N\<rangle> \<prec> \<lparr>\<nu>y\<rparr>(P' \<parallel> ([(x, y)] \<bullet> Q'))"
          by(intro Scope) auto
        moreover from \<open>x \<sharp> P\<close> \<open>y \<sharp> P\<close> \<open>y \<sharp> Q\<close> have "\<lparr>\<nu>y\<rparr>(P \<parallel> ([(x, y)] \<bullet> Q)) = \<lparr>\<nu>x\<rparr>([(x, y)] \<bullet> (P \<parallel> ([(x, y)] \<bullet> Q)))"
          by(subst alphaRes[of x]) (auto simp add: calc_atm fresh_left name_swap)
        with \<open>x \<sharp> P\<close> \<open>y \<sharp> P\<close> have "\<lparr>\<nu>y\<rparr>(P \<parallel> ([(x, y)] \<bullet> Q)) = \<lparr>\<nu>x\<rparr>(P \<parallel> Q)"
          by(simp add: eqvts)
        moreover from \<open>x \<sharp> P'\<close> \<open>y \<sharp> P'\<close> \<open>y \<sharp> Q'\<close> \<open>x \<sharp> xvec\<close> \<open>y \<sharp> xvec\<close> have "\<lparr>\<nu>y\<rparr>(P' \<parallel> ([(x, y)] \<bullet> Q')) =  \<lparr>\<nu>x\<rparr>(P' \<parallel> Q')"
          by(subst alphaRes[of y]) (auto simp add: resChainFresh calc_atm eqvts fresh_left name_swap)
        ultimately have "\<Psi> \<rhd> \<lparr>\<nu>x\<rparr>(P \<parallel> Q) \<longmapsto>\<exclamdown>M\<lparr>\<nu>*xvec\<rparr>\<langle>N\<rangle> \<prec> \<lparr>\<nu>x\<rparr>(P' \<parallel> Q')"
          by simp
        moreover from \<open>x \<sharp> \<Psi>\<close> \<open>x \<sharp> P'\<close> have "(\<Psi>, \<lparr>\<nu>*[x]\<rparr>(P' \<parallel> Q'), (P' \<parallel> (\<lparr>\<nu>*[x]\<rparr>Q'))) \<in> Rel"
          by(intro C4) simp+
        moreover then have "(\<Psi>, \<lparr>\<nu>x\<rparr>(P' \<parallel> Q'), (P' \<parallel> (\<lparr>\<nu>x\<rparr>Q'))) \<in> Rel"
          by simp
        ultimately show ?case by blast
      qed
    qed
  qed
qed

lemma scopeExtRight:
  fixes x   :: name
    and P   :: "('a, 'b, 'c) psi"
    and \<Psi>   :: 'b
    and Q   :: "('a, 'b, 'c) psi"
    and Rel :: "('b \<times> ('a, 'b, 'c) psi \<times> ('a, 'b, 'c) psi) set"

assumes "x \<sharp> P"
  and   "x \<sharp> \<Psi>"
  and   "eqvt Rel"
  and   C1: "\<And>\<Psi>' R. (\<Psi>, R, R) \<in> Rel"
  and   C2: "\<And>y \<Psi>' R S zvec. \<lbrakk>y \<sharp> \<Psi>'; y \<sharp> R; zvec \<sharp>* \<Psi>'\<rbrakk> \<Longrightarrow> (\<Psi>', \<lparr>\<nu>*zvec\<rparr>(R \<parallel> \<lparr>\<nu>y\<rparr>S), \<lparr>\<nu>y\<rparr>(\<lparr>\<nu>*zvec\<rparr>(R \<parallel> S))) \<in> Rel"
  \<comment> \<open>Addition for Broadcast\<close>
  and   C3: "\<And>\<Psi>' R S zvec. \<lbrakk>zvec \<sharp>* R; zvec \<sharp>* \<Psi>'\<rbrakk> \<Longrightarrow> (\<Psi>', (R \<parallel> (\<lparr>\<nu>*zvec\<rparr>S)), (\<lparr>\<nu>*zvec\<rparr>(R \<parallel> S))) \<in> Rel"

shows "\<Psi> \<rhd> P \<parallel> \<lparr>\<nu>x\<rparr>Q \<leadsto>[Rel] \<lparr>\<nu>x\<rparr>(P \<parallel> Q)"
proof -
  note \<open>eqvt Rel\<close> \<open>x \<sharp> \<Psi>\<close>
  moreover from \<open>x \<sharp> P\<close> have "x \<sharp> P \<parallel> \<lparr>\<nu>x\<rparr>Q" by(simp add: abs_fresh)
  moreover from \<open>x \<sharp> P\<close> have "x \<sharp> \<lparr>\<nu>x\<rparr>(P \<parallel> Q)" by(simp add: abs_fresh)
  ultimately show ?thesis
  proof(induct rule: simIFresh[of _ _ _ _ _ "()"])
    case(cSim \<alpha> xPQ)
    from \<open>bn \<alpha> \<sharp>* (P \<parallel> \<lparr>\<nu>x\<rparr>Q)\<close> \<open>x \<sharp> \<alpha>\<close> have "bn \<alpha>  \<sharp>* P" and "bn \<alpha>  \<sharp>* Q" by simp+
    note \<open>\<Psi> \<rhd> \<lparr>\<nu>x\<rparr>(P \<parallel> Q) \<longmapsto>\<alpha> \<prec> xPQ\<close> \<open>x \<sharp> \<Psi>\<close> \<open>x \<sharp> \<alpha>\<close> \<open>x \<sharp> xPQ\<close> \<open>bn \<alpha> \<sharp>* \<Psi>\<close>
    moreover from \<open>bn \<alpha> \<sharp>* P\<close> \<open>bn \<alpha> \<sharp>* Q\<close> have "bn \<alpha> \<sharp>* (P \<parallel> Q)" by simp
    ultimately show ?case using \<open>bn \<alpha> \<sharp>* subject \<alpha>\<close> \<open>x \<sharp> \<alpha>\<close>
    proof(induct rule: resCases[where C="()"])
      case(cOpen M xvec1 xvec2 y N PQ)
      from \<open>x \<sharp> M\<lparr>\<nu>*(xvec1@y#xvec2)\<rparr>\<langle>N\<rangle>\<close> have "x \<sharp> xvec1" and "x \<noteq> y" and "x \<sharp> xvec2" and "x \<sharp> M" by simp+
      from \<open>xvec1 \<sharp>* (P \<parallel> Q)\<close> \<open>xvec2 \<sharp>* (P \<parallel> Q)\<close> \<open>y \<sharp> (P \<parallel> Q)\<close>
      have "(xvec1@xvec2) \<sharp>* P" and "(xvec1@xvec2) \<sharp>* Q" and "y \<sharp> P" and "y \<sharp> Q"
        by simp+
      from \<open>\<Psi> \<rhd> P \<parallel> Q \<longmapsto> M\<lparr>\<nu>*(xvec1@xvec2)\<rparr>\<langle>([(x, y)] \<bullet> N)\<rangle> \<prec> ([(x, y)] \<bullet> PQ)\<close>
      have "([(x, y)] \<bullet> \<Psi>) \<rhd> ([(x, y)] \<bullet> (P \<parallel> Q)) \<longmapsto> ([(x, y)] \<bullet> (M\<lparr>\<nu>*(xvec1@xvec2)\<rparr>\<langle>([(x, y)] \<bullet> N)\<rangle> \<prec> ([(x, y)] \<bullet> PQ)))"
        by(rule semantics.eqvt)
      with \<open>x \<sharp> \<Psi>\<close> \<open>y \<sharp> \<Psi>\<close> \<open>x \<sharp> P\<close> \<open>y \<sharp> P\<close> \<open>x \<sharp> M\<close> \<open>y \<sharp> M\<close> \<open>x \<sharp> xvec1\<close> \<open>x \<sharp> xvec2\<close> \<open>y \<sharp> xvec1\<close> \<open>y \<sharp> xvec2\<close>
      have "\<Psi> \<rhd> P \<parallel> ([(x, y)] \<bullet> Q) \<longmapsto> M\<lparr>\<nu>*(xvec1@xvec2)\<rparr>\<langle>N\<rangle> \<prec> PQ"
        by(simp add: eqvts)
      moreover from \<open>xvec1 \<sharp>* \<Psi>\<close> \<open>xvec2 \<sharp>* \<Psi>\<close> have "(xvec1@xvec2) \<sharp>* \<Psi>" by simp
      moreover note \<open>(xvec1@xvec2) \<sharp>* P\<close>
      moreover from \<open>(xvec1@xvec2) \<sharp>* Q\<close> have "([(x, y)] \<bullet> (xvec1@xvec2)) \<sharp>* ([(x, y)] \<bullet> Q)"
        by(simp add: pt_fresh_star_bij[OF pt_name_inst, OF at_name_inst])
      with \<open>x \<sharp> xvec1\<close> \<open>x \<sharp> xvec2\<close> \<open>y \<sharp> xvec1\<close> \<open>y \<sharp> xvec2\<close> have "(xvec1@xvec2) \<sharp>* ([(x, y)] \<bullet> Q)"
        by(auto simp add: eqvts)
      moreover from \<open>xvec1 \<sharp>* M\<close> \<open>xvec2 \<sharp>* M\<close> have "(xvec1@xvec2) \<sharp>* M" by simp
      ultimately show ?case
      proof(induct rule: parOutputCases[where C=y])
        case(cPar1 P' A\<^sub>Q \<Psi>\<^sub>Q)
        from \<open>y \<sharp> xvec1\<close> \<open>y \<sharp> xvec2\<close> have "y \<sharp> (xvec1@xvec2)" by(auto simp add: fresh_list_append)
        with \<open>\<Psi> \<otimes> \<Psi>\<^sub>Q \<rhd> P \<longmapsto>M\<lparr>\<nu>*(xvec1@xvec2)\<rparr>\<langle>N\<rangle> \<prec> P'\<close> \<open>(xvec1@xvec2) \<sharp>* M\<close> \<open>y \<sharp> P\<close>
          \<open>distinct xvec1\<close> \<open>distinct xvec2\<close> \<open>xvec1 \<sharp>* xvec2\<close>
        have "y \<sharp> N" by(force intro: outputFreshDerivative)
        with \<open>y \<in> supp N\<close> have False by(simp add: fresh_def)
        then show ?case by simp
      next
        case(cPar2 Q' A\<^sub>P \<Psi>\<^sub>P)
        have FrP: "extractFrame P = \<langle>A\<^sub>P, \<Psi>\<^sub>P\<rangle>" by fact
        with \<open>y \<sharp> P\<close> \<open>A\<^sub>P \<sharp>* y\<close> have "y \<sharp> \<Psi>\<^sub>P"
          apply(drule_tac extractFrameFresh)
          by(simp add: frameResChainFresh) (simp add: fresh_def name_list_supp)
        from \<open>\<Psi> \<otimes> \<Psi>\<^sub>P \<rhd> ([(x, y)] \<bullet> Q) \<longmapsto>M\<lparr>\<nu>*(xvec1@xvec2)\<rparr>\<langle>N\<rangle> \<prec> Q'\<close> \<open>y \<in> supp N\<close> \<open>y \<sharp> \<Psi>\<close> \<open>y \<sharp> \<Psi>\<^sub>P\<close> \<open>y \<sharp> M\<close> \<open>y \<sharp> xvec1\<close> \<open>y \<sharp> xvec2\<close>
        have "\<Psi> \<otimes> \<Psi>\<^sub>P \<rhd> \<lparr>\<nu>y\<rparr>(([(x, y)] \<bullet> Q)) \<longmapsto>M\<lparr>\<nu>*(xvec1@y#xvec2)\<rparr>\<langle>N\<rangle> \<prec> Q'" by(force intro: Open)
        with \<open>y \<sharp> Q\<close> have "\<Psi> \<otimes> \<Psi>\<^sub>P \<rhd> \<lparr>\<nu>x\<rparr>Q \<longmapsto>M\<lparr>\<nu>*(xvec1@y#xvec2)\<rparr>\<langle>N\<rangle> \<prec> Q'"
          by(simp add: alphaRes)
        moreover from \<open>A\<^sub>P \<sharp>* ([(x, y)] \<bullet> Q)\<close> have "A\<^sub>P \<sharp>* \<lparr>\<nu>y\<rparr>([(x, y)] \<bullet> Q)" by(auto simp add: fresh_star_def abs_fresh)
        with \<open>y \<sharp> Q\<close> have "A\<^sub>P \<sharp>* \<lparr>\<nu>x\<rparr>Q" by(simp add: alphaRes)
        ultimately have "\<Psi> \<rhd> P \<parallel> (\<lparr>\<nu>x\<rparr>Q) \<longmapsto>M\<lparr>\<nu>*(xvec1@y#xvec2)\<rparr>\<langle>N\<rangle> \<prec> (P \<parallel> Q')"
          using FrP \<open>(xvec1@xvec2) \<sharp>* P\<close> \<open>A\<^sub>P \<sharp>* \<Psi>\<close> \<open>A\<^sub>P \<sharp>* M\<close> \<open>y \<sharp> P\<close> \<open>A\<^sub>P \<sharp>* (xvec1@xvec2)\<close> \<open>A\<^sub>P \<sharp>* y\<close> \<open>A\<^sub>P \<sharp>* N\<close>
          by(intro Par2) auto
        moreover have "(\<Psi>, P \<parallel> Q', P \<parallel> Q') \<in> Rel" by(rule C1)
        ultimately show ?case by blast
      qed
    next
      case(cBrOpen M xvec1 xvec2 y N PQ)
      from \<open>x \<sharp> \<exclamdown>M\<lparr>\<nu>*(xvec1@y#xvec2)\<rparr>\<langle>N\<rangle>\<close> have "x \<sharp> xvec1" and "x \<noteq> y" and "x \<sharp> xvec2" and "x \<sharp> M" by simp+
      from \<open>xvec1 \<sharp>* (P \<parallel> Q)\<close> \<open>xvec2 \<sharp>* (P \<parallel> Q)\<close> \<open>y \<sharp> (P \<parallel> Q)\<close>
      have "(xvec1@xvec2) \<sharp>* P" and "(xvec1@xvec2) \<sharp>* Q" and "y \<sharp> P" and "y \<sharp> Q"
        by simp+
      from \<open>\<Psi> \<rhd> P \<parallel> Q \<longmapsto> \<exclamdown>M\<lparr>\<nu>*(xvec1@xvec2)\<rparr>\<langle>([(x, y)] \<bullet> N)\<rangle> \<prec> ([(x, y)] \<bullet> PQ)\<close>
      have "([(x, y)] \<bullet> \<Psi>) \<rhd> ([(x, y)] \<bullet> (P \<parallel> Q)) \<longmapsto> ([(x, y)] \<bullet> (\<exclamdown>M\<lparr>\<nu>*(xvec1@xvec2)\<rparr>\<langle>([(x, y)] \<bullet> N)\<rangle> \<prec> ([(x, y)] \<bullet> PQ)))"
        by(rule semantics.eqvt)
      with \<open>x \<sharp> \<Psi>\<close> \<open>y \<sharp> \<Psi>\<close> \<open>x \<sharp> P\<close> \<open>y \<sharp> P\<close> \<open>x \<sharp> M\<close> \<open>y \<sharp> M\<close> \<open>x \<sharp> xvec1\<close> \<open>x \<sharp> xvec2\<close> \<open>y \<sharp> xvec1\<close> \<open>y \<sharp> xvec2\<close>
      have "\<Psi> \<rhd> P \<parallel> ([(x, y)] \<bullet> Q) \<longmapsto> \<exclamdown>M\<lparr>\<nu>*(xvec1@xvec2)\<rparr>\<langle>N\<rangle> \<prec> PQ"
        by(simp add: eqvts)
      moreover from \<open>xvec1 \<sharp>* \<Psi>\<close> \<open>xvec2 \<sharp>* \<Psi>\<close> have "(xvec1@xvec2) \<sharp>* \<Psi>" by simp
      moreover note \<open>(xvec1@xvec2) \<sharp>* P\<close>
      moreover from \<open>(xvec1@xvec2) \<sharp>* Q\<close> have "([(x, y)] \<bullet> (xvec1@xvec2)) \<sharp>* ([(x, y)] \<bullet> Q)"
        by(simp add: pt_fresh_star_bij[OF pt_name_inst, OF at_name_inst])
      with \<open>x \<sharp> xvec1\<close> \<open>x \<sharp> xvec2\<close> \<open>y \<sharp> xvec1\<close> \<open>y \<sharp> xvec2\<close> have "(xvec1@xvec2) \<sharp>* ([(x, y)] \<bullet> Q)"
        by(auto simp add: eqvts)
      moreover from \<open>xvec1 \<sharp>* M\<close> \<open>xvec2 \<sharp>* M\<close> have "(xvec1@xvec2) \<sharp>* M" by simp
      ultimately show ?case
      proof(induct rule: parBrOutputCases[where C=y])
        case(cPar1 P' A\<^sub>Q \<Psi>\<^sub>Q)
        from \<open>y \<sharp> xvec1\<close> \<open>y \<sharp> xvec2\<close> have "y \<sharp> (xvec1@xvec2)" by(auto simp add: fresh_list_append)
        with \<open>\<Psi> \<otimes> \<Psi>\<^sub>Q \<rhd> P \<longmapsto>\<exclamdown>M\<lparr>\<nu>*(xvec1@xvec2)\<rparr>\<langle>N\<rangle> \<prec> P'\<close> \<open>(xvec1@xvec2) \<sharp>* M\<close> \<open>y \<sharp> P\<close>
          \<open>distinct xvec1\<close> \<open>distinct xvec2\<close> \<open>xvec1 \<sharp>* xvec2\<close>
        have "y \<sharp> N" by(force intro: broutputFreshDerivative)
        with \<open>y \<in> supp N\<close> have False by(simp add: fresh_def)
        then show ?case by simp
      next
        case(cPar2 Q' A\<^sub>P \<Psi>\<^sub>P)
        have FrP: "extractFrame P = \<langle>A\<^sub>P, \<Psi>\<^sub>P\<rangle>" by fact
        with \<open>y \<sharp> P\<close> \<open>A\<^sub>P \<sharp>* y\<close> have "y \<sharp> \<Psi>\<^sub>P"
          apply(drule_tac extractFrameFresh)
          by(simp add: frameResChainFresh) (simp add: fresh_def name_list_supp)
        from \<open>\<Psi> \<otimes> \<Psi>\<^sub>P \<rhd> ([(x, y)] \<bullet> Q) \<longmapsto>\<exclamdown>M\<lparr>\<nu>*(xvec1@xvec2)\<rparr>\<langle>N\<rangle> \<prec> Q'\<close> \<open>y \<in> supp N\<close> \<open>y \<sharp> \<Psi>\<close> \<open>y \<sharp> \<Psi>\<^sub>P\<close> \<open>y \<sharp> M\<close> \<open>y \<sharp> xvec1\<close> \<open>y \<sharp> xvec2\<close>
        have "\<Psi> \<otimes> \<Psi>\<^sub>P \<rhd> \<lparr>\<nu>y\<rparr>(([(x, y)] \<bullet> Q)) \<longmapsto>\<exclamdown>M\<lparr>\<nu>*(xvec1@y#xvec2)\<rparr>\<langle>N\<rangle> \<prec> Q'" by(force intro: BrOpen)
        with \<open>y \<sharp> Q\<close> have "\<Psi> \<otimes> \<Psi>\<^sub>P \<rhd> \<lparr>\<nu>x\<rparr>Q \<longmapsto>\<exclamdown>M\<lparr>\<nu>*(xvec1@y#xvec2)\<rparr>\<langle>N\<rangle> \<prec> Q'"
          by(simp add: alphaRes)
        moreover from \<open>A\<^sub>P \<sharp>* ([(x, y)] \<bullet> Q)\<close> have "A\<^sub>P \<sharp>* \<lparr>\<nu>y\<rparr>([(x, y)] \<bullet> Q)" by(auto simp add: fresh_star_def abs_fresh)
        with \<open>y \<sharp> Q\<close> have "A\<^sub>P \<sharp>* \<lparr>\<nu>x\<rparr>Q" by(simp add: alphaRes)
        ultimately have "\<Psi> \<rhd> P \<parallel> (\<lparr>\<nu>x\<rparr>Q) \<longmapsto>\<exclamdown>M\<lparr>\<nu>*(xvec1@y#xvec2)\<rparr>\<langle>N\<rangle> \<prec> (P \<parallel> Q')"
          using FrP \<open>(xvec1@xvec2) \<sharp>* P\<close> \<open>A\<^sub>P \<sharp>* \<Psi>\<close> \<open>A\<^sub>P \<sharp>* M\<close> \<open>y \<sharp> P\<close> \<open>A\<^sub>P \<sharp>* (xvec1@xvec2)\<close> \<open>A\<^sub>P \<sharp>* y\<close> \<open>A\<^sub>P \<sharp>* N\<close>
          by(intro Par2) auto
        moreover have "(\<Psi>, P \<parallel> Q', P \<parallel> Q') \<in> Rel" by(rule C1)
        ultimately show ?case by blast
      next
        case(cBrComm1 \<Psi>\<^sub>Q P' A\<^sub>P \<Psi>\<^sub>P Q' A\<^sub>Q)
        have FrP: "extractFrame P = \<langle>A\<^sub>P, \<Psi>\<^sub>P\<rangle>" by fact
        with \<open>y \<sharp> P\<close> \<open>A\<^sub>P \<sharp>* y\<close> have "y \<sharp> \<Psi>\<^sub>P"
          apply(drule_tac extractFrameFresh)
          by(simp add: frameResChainFresh) (simp add: fresh_def name_list_supp)

        from \<open>extractFrame ([(x, y)] \<bullet> Q) = \<langle>A\<^sub>Q, \<Psi>\<^sub>Q\<rangle>\<close>
        have "extractFrame (\<lparr>\<nu>y\<rparr>([(x, y)] \<bullet> Q)) = \<langle>(y#A\<^sub>Q), \<Psi>\<^sub>Q\<rangle>"
          by simp
        with \<open>y \<sharp> Q\<close>
        have FrQ: "extractFrame (\<lparr>\<nu>x\<rparr>Q) = \<langle>(y#A\<^sub>Q), \<Psi>\<^sub>Q\<rangle>"
          by(simp add: alphaRes)
        from \<open>\<Psi> \<otimes> \<Psi>\<^sub>P \<rhd> [(x, y)] \<bullet> Q \<longmapsto> \<exclamdown>M\<lparr>\<nu>*(xvec1 @ xvec2)\<rparr>\<langle>N\<rangle> \<prec> Q'\<close> \<open>y \<in> supp N\<close> \<open>y \<sharp> \<Psi>\<close> \<open>y \<sharp> \<Psi>\<^sub>P\<close> \<open>y \<sharp> M\<close> \<open>y \<sharp> xvec1\<close> \<open>y \<sharp> xvec2\<close>
        have "\<Psi> \<otimes> \<Psi>\<^sub>P \<rhd> \<lparr>\<nu>y\<rparr>([(x, y)] \<bullet> Q) \<longmapsto> \<exclamdown>M\<lparr>\<nu>*(xvec1@y#xvec2)\<rparr>\<langle>N\<rangle> \<prec> Q'"
          by(force intro: BrOpen)
        with \<open>y \<sharp> Q\<close> have QTrans: "\<Psi> \<otimes> \<Psi>\<^sub>P \<rhd> \<lparr>\<nu>x\<rparr>Q \<longmapsto>\<exclamdown>M\<lparr>\<nu>*(xvec1@y#xvec2)\<rparr>\<langle>N\<rangle> \<prec> Q'"
          by(simp add: alphaRes)
        from \<open>A\<^sub>P \<sharp>* ([(x, y)] \<bullet> Q)\<close> have "A\<^sub>P \<sharp>* \<lparr>\<nu>y\<rparr>([(x, y)] \<bullet> Q)" by(auto simp add: fresh_star_def abs_fresh)
        with \<open>y \<sharp> Q\<close> have "A\<^sub>P \<sharp>* \<lparr>\<nu>x\<rparr>Q" by(simp add: alphaRes)
        from \<open>A\<^sub>Q \<sharp>* ([(x, y)] \<bullet> Q)\<close> have "A\<^sub>Q \<sharp>* \<lparr>\<nu>y\<rparr>([(x, y)] \<bullet> Q)" by(auto simp add: fresh_star_def abs_fresh)
        with \<open>y \<sharp> Q\<close> have "A\<^sub>Q \<sharp>* \<lparr>\<nu>x\<rparr>Q" by(simp add: alphaRes)
        moreover from \<open>y \<sharp> Q\<close> have "y \<sharp> \<lparr>\<nu>x\<rparr>Q"
          by (metis resChain.base resChain.step resChainFresh)
        ultimately have "(y # A\<^sub>Q) \<sharp>* (\<lparr>\<nu>x\<rparr>Q)" by simp
        from \<open>\<Psi> \<otimes> \<Psi>\<^sub>Q \<rhd> P \<longmapsto> \<questiondown>M\<lparr>N\<rparr> \<prec> P'\<close> FrP QTrans FrQ
          \<open>A\<^sub>P \<sharp>* \<Psi>\<close> \<open>A\<^sub>P \<sharp>* P\<close> \<open>A\<^sub>P \<sharp>* \<lparr>\<nu>x\<rparr>Q\<close> \<open>A\<^sub>P \<sharp>* M\<close> \<open>A\<^sub>P \<sharp>* y\<close> \<open>A\<^sub>P \<sharp>* A\<^sub>Q\<close>
          \<open>y \<sharp> \<Psi>\<close> \<open>A\<^sub>Q \<sharp>* \<Psi>\<close> \<open>y \<sharp> P\<close> \<open>A\<^sub>Q \<sharp>* P\<close> \<open>(y#A\<^sub>Q) \<sharp>* \<lparr>\<nu>x\<rparr>Q\<close>
          \<open>y \<sharp> M\<close> \<open>A\<^sub>Q \<sharp>* M\<close> \<open>y \<sharp> P\<close> \<open>(xvec1@xvec2) \<sharp>* P\<close>
        have "\<Psi> \<rhd> P \<parallel> (\<lparr>\<nu>x\<rparr>Q) \<longmapsto>\<exclamdown>M\<lparr>\<nu>*(xvec1@y#xvec2)\<rparr>\<langle>N\<rangle> \<prec> (P' \<parallel> Q')"
          by(intro BrComm1) (assumption | simp)+
        moreover have "(\<Psi>, P' \<parallel> Q', P' \<parallel> Q') \<in> Rel" by(rule C1)
        ultimately show ?case by blast
      next
        case(cBrComm2 \<Psi>\<^sub>Q P' A\<^sub>P \<Psi>\<^sub>P Q' A\<^sub>Q)
        from \<open>y \<sharp> xvec1\<close> \<open>y \<sharp> xvec2\<close> have "y \<sharp> (xvec1@xvec2)" by(auto simp add: fresh_list_append)
        with \<open>\<Psi> \<otimes> \<Psi>\<^sub>Q \<rhd> P \<longmapsto>\<exclamdown>M\<lparr>\<nu>*(xvec1@xvec2)\<rparr>\<langle>N\<rangle> \<prec> P'\<close> \<open>(xvec1@xvec2) \<sharp>* M\<close> \<open>y \<sharp> P\<close>
          \<open>distinct xvec1\<close> \<open>distinct xvec2\<close> \<open>xvec1 \<sharp>* xvec2\<close>
        have "y \<sharp> N" by(force intro: broutputFreshDerivative)
        with \<open>y \<in> supp N\<close> have False by(simp add: fresh_def)
        then show ?case by simp
      qed
    next
      case(cRes PQ)
      from \<open>\<Psi> \<rhd> P \<parallel> Q \<longmapsto>\<alpha> \<prec> PQ\<close> \<open>bn \<alpha> \<sharp>* \<Psi>\<close>  \<open>bn \<alpha> \<sharp>* P\<close> \<open>bn \<alpha> \<sharp>* Q\<close> \<open>bn \<alpha> \<sharp>* subject \<alpha>\<close>
      show ?case
      proof(induct rule: parCases[where C=x])
        case(cPar1 P' A\<^sub>Q \<Psi>\<^sub>Q)
        note \<open>\<Psi> \<otimes> \<Psi>\<^sub>Q \<rhd> P \<longmapsto>\<alpha> \<prec> P'\<close>
        moreover with \<open>x \<sharp> P\<close> \<open>x \<sharp> \<alpha>\<close> \<open>bn \<alpha> \<sharp>* subject \<alpha>\<close> \<open>distinct(bn \<alpha>)\<close>
        have "x \<sharp> P'" by(force dest: freeFreshDerivative)
        with \<open>extractFrame Q = \<langle>A\<^sub>Q, \<Psi>\<^sub>Q\<rangle>\<close> have "extractFrame(\<lparr>\<nu>x\<rparr>Q) = \<langle>(x#A\<^sub>Q), \<Psi>\<^sub>Q\<rangle>"
          by simp
        moreover from \<open>bn \<alpha> \<sharp>* Q\<close> have "bn \<alpha> \<sharp>* (\<lparr>\<nu>x\<rparr>Q)" by(simp add: fresh_star_def abs_fresh)
        moreover from \<open>x \<sharp> \<Psi>\<close> \<open>A\<^sub>Q \<sharp>* \<Psi>\<close> have "(x#A\<^sub>Q) \<sharp>* \<Psi>" by simp
        moreover from \<open>x \<sharp> P\<close> \<open>A\<^sub>Q \<sharp>* P\<close> have "(x#A\<^sub>Q) \<sharp>* P" by simp
        moreover from \<open>x \<sharp> \<alpha>\<close> \<open>A\<^sub>Q \<sharp>* \<alpha>\<close> have "(x#A\<^sub>Q) \<sharp>* \<alpha>" by simp
        ultimately have "\<Psi> \<rhd> P \<parallel> \<lparr>\<nu>x\<rparr>Q \<longmapsto>\<alpha> \<prec> (P' \<parallel> \<lparr>\<nu>x\<rparr>Q)"
          by(rule Par1)
        moreover from \<open>x \<sharp> P'\<close> \<open>x \<sharp> \<Psi>\<close> have "(\<Psi>, \<lparr>\<nu>*[]\<rparr>(P' \<parallel> (\<lparr>\<nu>x\<rparr>Q)), \<lparr>\<nu>x\<rparr>(\<lparr>\<nu>*[]\<rparr>(P' \<parallel> Q))) \<in> Rel"
          by(intro C2) auto
        ultimately show ?case
          by force
      next
        case(cPar2 Q' A\<^sub>P \<Psi>\<^sub>P)
        have FrP: "extractFrame P = \<langle>A\<^sub>P, \<Psi>\<^sub>P\<rangle>" by fact
        with \<open>x \<sharp> P\<close> \<open>A\<^sub>P \<sharp>* x\<close> have "x \<sharp> \<Psi>\<^sub>P"
          apply(drule_tac extractFrameFresh)
          by(simp add: frameResChainFresh) (simp add: fresh_def name_list_supp)
        from \<open>\<Psi> \<otimes> \<Psi>\<^sub>P \<rhd> Q \<longmapsto>\<alpha> \<prec> Q'\<close> \<open>x \<sharp> \<Psi>\<close> \<open>x \<sharp> \<Psi>\<^sub>P\<close> \<open>x \<sharp> \<alpha>\<close>
        have "\<Psi> \<otimes> \<Psi>\<^sub>P \<rhd> \<lparr>\<nu>x\<rparr>Q \<longmapsto>\<alpha> \<prec> \<lparr>\<nu>x\<rparr>Q'"
          by(intro Scope) auto
        moreover note FrP \<open>bn \<alpha> \<sharp>* P\<close> \<open>A\<^sub>P \<sharp>* \<Psi>\<close>
        moreover from \<open>A\<^sub>P \<sharp>* Q\<close> have "A\<^sub>P \<sharp>* \<lparr>\<nu>x\<rparr>Q" by(simp add: fresh_star_def abs_fresh)
        ultimately have "\<Psi> \<rhd> P \<parallel> \<lparr>\<nu>x\<rparr>Q \<longmapsto>\<alpha> \<prec> (P \<parallel> \<lparr>\<nu>x\<rparr>Q')" using \<open>A\<^sub>P \<sharp>* \<alpha>\<close>
          by(rule Par2)
        moreover from \<open>x \<sharp> P\<close> \<open>x \<sharp> \<Psi>\<close> have "(\<Psi>, \<lparr>\<nu>*[]\<rparr>(P \<parallel> (\<lparr>\<nu>x\<rparr>Q')), \<lparr>\<nu>x\<rparr>(\<lparr>\<nu>*[]\<rparr>(P \<parallel> Q'))) \<in> Rel"
          by(intro C2) auto
        ultimately show ?case
          by force
      next
        case(cComm1 \<Psi>\<^sub>Q M N P' A\<^sub>P \<Psi>\<^sub>P K xvec Q' A\<^sub>Q)
        have PTrans: "\<Psi> \<otimes> \<Psi>\<^sub>Q \<rhd> P \<longmapsto>M\<lparr>N\<rparr> \<prec> P'" and FrP: "extractFrame P = \<langle>A\<^sub>P, \<Psi>\<^sub>P\<rangle>" by fact+
        have QTrans: "\<Psi> \<otimes> \<Psi>\<^sub>P \<rhd> Q \<longmapsto>K\<lparr>\<nu>*xvec\<rparr>\<langle>N\<rangle> \<prec> Q'" and FrQ: "extractFrame Q = \<langle>A\<^sub>Q, \<Psi>\<^sub>Q\<rangle>" by fact+
        from FrP \<open>x \<sharp> P\<close> have "x \<sharp> \<langle>A\<^sub>P, \<Psi>\<^sub>P\<rangle>"
          by(auto dest: extractFrameFresh)
        with \<open>A\<^sub>P \<sharp>* x\<close> have "x \<sharp> \<Psi>\<^sub>P" by(simp add: frameResChainFresh) (simp add: fresh_def name_list_supp)
        from PTrans FrP \<open>distinct A\<^sub>P\<close> \<open>x \<sharp> P\<close> \<open>A\<^sub>P \<sharp>* \<Psi>\<close> \<open>A\<^sub>P \<sharp>* \<Psi>\<^sub>Q\<close> \<open>A\<^sub>P \<sharp>* x\<close> \<open>A\<^sub>P \<sharp>* P\<close> \<open>A\<^sub>P \<sharp>* M\<close> \<open>A\<^sub>Q \<sharp>* P\<close> \<open>A\<^sub>P \<sharp>* A\<^sub>Q\<close>
        obtain M' where MeqM': "(\<Psi> \<otimes> \<Psi>\<^sub>Q) \<otimes> \<Psi>\<^sub>P \<turnstile> M \<leftrightarrow> M'" and "x \<sharp> M'" and "A\<^sub>Q \<sharp>* M'"
          by(elim inputObtainPrefix[where B="x#A\<^sub>Q"]) (assumption | force simp add: fresh_star_list_cons)+
        from MeqM' have MeqM': "\<Psi> \<otimes> \<Psi>\<^sub>P \<otimes> \<Psi>\<^sub>Q \<turnstile> M \<leftrightarrow> M'"
          by(metis statEqEnt Associativity Composition Commutativity)
        with \<open>\<Psi> \<otimes> \<Psi>\<^sub>P \<otimes> \<Psi>\<^sub>Q \<turnstile> M \<leftrightarrow> K\<close> have "\<Psi> \<otimes> \<Psi>\<^sub>P \<otimes> \<Psi>\<^sub>Q \<turnstile> K \<leftrightarrow> M'"
          by(blast intro: chanEqTrans chanEqSym)
        then have "(\<Psi> \<otimes> \<Psi>\<^sub>P) \<otimes> \<Psi>\<^sub>Q \<turnstile> K \<leftrightarrow> M'"
          by(metis statEqEnt Associativity Composition Commutativity)
        with QTrans FrQ \<open>distinct A\<^sub>Q\<close> have QTrans: "\<Psi> \<otimes> \<Psi>\<^sub>P \<rhd> Q \<longmapsto>M'\<lparr>\<nu>*xvec\<rparr>\<langle>N\<rangle> \<prec> Q'" using \<open>A\<^sub>Q \<sharp>* \<Psi>\<close> \<open>A\<^sub>Q \<sharp>* \<Psi>\<^sub>P\<close> \<open>A\<^sub>Q \<sharp>* Q\<close> \<open>A\<^sub>Q \<sharp>* K\<close> \<open>A\<^sub>Q \<sharp>* M'\<close>
          by(elim outputRenameSubject) (assumption | force)+
        show ?case
        proof(cases "x \<in> supp N")
          note PTrans FrP
          moreover assume "x \<in> supp N"
          then have "\<Psi> \<otimes> \<Psi>\<^sub>P \<rhd> \<lparr>\<nu>x\<rparr>Q \<longmapsto>M'\<lparr>\<nu>*([]@(x#xvec))\<rparr>\<langle>N\<rangle> \<prec> Q'" using QTrans \<open>x \<sharp> \<Psi>\<close> \<open>x \<sharp> \<Psi>\<^sub>P\<close> \<open>x \<sharp> M'\<close> \<open>xvec \<sharp>* x\<close>
            by(intro Open) (assumption | force simp add: fresh_list_nil)+
          then have QTrans: "\<Psi> \<otimes> \<Psi>\<^sub>P \<rhd> \<lparr>\<nu>x\<rparr>Q \<longmapsto>M'\<lparr>\<nu>*(x#xvec)\<rparr>\<langle>N\<rangle> \<prec> Q'" by simp
          moreover from \<open>extractFrame Q = \<langle>A\<^sub>Q, \<Psi>\<^sub>Q\<rangle>\<close> have "extractFrame(\<lparr>\<nu>x\<rparr>Q) = \<langle>(x#A\<^sub>Q), \<Psi>\<^sub>Q\<rangle>"
            by simp
          moreover note MeqM' \<open>A\<^sub>P \<sharp>* \<Psi>\<close> \<open>A\<^sub>P \<sharp>* P\<close>
          moreover from  \<open>A\<^sub>P \<sharp>* Q\<close> have "A\<^sub>P \<sharp>* (\<lparr>\<nu>x\<rparr>Q)" by(simp add: fresh_star_def abs_fresh)
          moreover from \<open>A\<^sub>P \<sharp>* A\<^sub>Q\<close> \<open>A\<^sub>P \<sharp>* x\<close> have "A\<^sub>P \<sharp>* (x#A\<^sub>Q)"
            by(simp add: fresh_star_def fresh_list_cons) (auto simp add: fresh_def name_list_supp)
          moreover from \<open>x \<sharp> \<Psi>\<close> \<open>A\<^sub>Q \<sharp>* \<Psi>\<close> have "(x#A\<^sub>Q) \<sharp>* \<Psi>" by simp
          moreover from \<open>x \<sharp> P\<close> \<open>A\<^sub>Q \<sharp>* P\<close> have "(x#A\<^sub>Q) \<sharp>* P" by simp
          moreover from \<open>x \<sharp> M'\<close> \<open>A\<^sub>Q \<sharp>* M'\<close> have "(x#A\<^sub>Q) \<sharp>* M'" by simp
          moreover from \<open>A\<^sub>Q \<sharp>* Q\<close> have "(x#A\<^sub>Q) \<sharp>* (\<lparr>\<nu>x\<rparr>Q)" by(simp add: fresh_star_def abs_fresh)
          moreover from \<open>x \<sharp> P\<close> \<open>xvec \<sharp>* P\<close> have "(x#xvec) \<sharp>* P" by(simp)
          ultimately have "\<Psi> \<rhd> P \<parallel> \<lparr>\<nu>x\<rparr>Q \<longmapsto>\<tau> \<prec> \<lparr>\<nu>*(x#xvec)\<rparr>(P' \<parallel> Q')" using \<open>A\<^sub>P \<sharp>* M\<close>
            by(intro Comm1) (assumption | simp)+
          moreover have "(\<Psi>, \<lparr>\<nu>x\<rparr>(\<lparr>\<nu>*xvec\<rparr>(P' \<parallel> Q')), \<lparr>\<nu>x\<rparr>(\<lparr>\<nu>*xvec\<rparr>(P' \<parallel> Q'))) \<in> Rel" by(rule C1)
          ultimately show ?case by force
        next
          note PTrans FrP
          moreover assume "x \<notin> supp N"
          then have "x \<sharp> N" by(simp add: fresh_def)
          with QTrans \<open>x \<sharp> \<Psi>\<close> \<open>x \<sharp> \<Psi>\<^sub>P\<close> \<open>x \<sharp> M'\<close> \<open>xvec \<sharp>* x\<close>
          have QTrans: "\<Psi> \<otimes> \<Psi>\<^sub>P \<rhd> \<lparr>\<nu>x\<rparr>Q \<longmapsto>M'\<lparr>\<nu>*xvec\<rparr>\<langle>N\<rangle> \<prec> \<lparr>\<nu>x\<rparr>Q'"
            by(intro Scope) (assumption | force)+
          moreover from PTrans \<open>x \<sharp> P\<close> \<open>x \<sharp> N\<close> have "x \<sharp> P'" by(rule inputFreshDerivative)
          with \<open>extractFrame Q = \<langle>A\<^sub>Q, \<Psi>\<^sub>Q\<rangle>\<close> have "extractFrame(\<lparr>\<nu>x\<rparr>Q) = \<langle>(x#A\<^sub>Q), \<Psi>\<^sub>Q\<rangle>"
            by simp
          moreover note MeqM' \<open>A\<^sub>P \<sharp>* \<Psi>\<close> \<open>A\<^sub>P \<sharp>* P\<close>
          moreover from  \<open>A\<^sub>P \<sharp>* Q\<close> have "A\<^sub>P \<sharp>* (\<lparr>\<nu>x\<rparr>Q)" by(simp add: fresh_star_def abs_fresh)
          moreover from \<open>A\<^sub>P \<sharp>* A\<^sub>Q\<close> \<open>A\<^sub>P \<sharp>* x\<close> have "A\<^sub>P \<sharp>* (x#A\<^sub>Q)"
            by(simp add: fresh_star_def fresh_list_cons) (auto simp add: fresh_def name_list_supp)
          moreover from \<open>x \<sharp> \<Psi>\<close> \<open>A\<^sub>Q \<sharp>* \<Psi>\<close> have "(x#A\<^sub>Q) \<sharp>* \<Psi>" by simp
          moreover from \<open>x \<sharp> P\<close> \<open>A\<^sub>Q \<sharp>* P\<close> have "(x#A\<^sub>Q) \<sharp>* P" by simp
          moreover from \<open>x \<sharp> M'\<close> \<open>A\<^sub>Q \<sharp>* M'\<close> have "(x#A\<^sub>Q) \<sharp>* M'" by simp
          moreover from \<open>A\<^sub>Q \<sharp>* Q\<close> have "(x#A\<^sub>Q) \<sharp>* (\<lparr>\<nu>x\<rparr>Q)" by(simp add: fresh_star_def abs_fresh)
          moreover from \<open>x \<sharp> P\<close> \<open>xvec \<sharp>* P\<close> have "(x#xvec) \<sharp>* P" by(simp)
          ultimately have "\<Psi> \<rhd> P \<parallel> \<lparr>\<nu>x\<rparr>Q \<longmapsto>\<tau> \<prec> \<lparr>\<nu>*xvec\<rparr>(P' \<parallel> \<lparr>\<nu>x\<rparr>Q')" using \<open>A\<^sub>P \<sharp>* M\<close>
            by(intro Comm1) (assumption | simp)+
          moreover from \<open>x \<sharp> \<Psi>\<close> \<open>x \<sharp> P'\<close> \<open>xvec \<sharp>* \<Psi>\<close> have "(\<Psi>, \<lparr>\<nu>*xvec\<rparr>(P' \<parallel> \<lparr>\<nu>x\<rparr>Q'), \<lparr>\<nu>x\<rparr>(\<lparr>\<nu>*xvec\<rparr>(P' \<parallel> Q'))) \<in> Rel" by(rule C2)
          ultimately show ?case by blast
        qed
      next
        case(cComm2 \<Psi>\<^sub>Q M xvec N P' A\<^sub>P \<Psi>\<^sub>P K Q' A\<^sub>Q)
        have PTrans: "\<Psi> \<otimes> \<Psi>\<^sub>Q \<rhd> P \<longmapsto>M\<lparr>\<nu>*xvec\<rparr>\<langle>N\<rangle> \<prec> P'" and FrP: "extractFrame P = \<langle>A\<^sub>P, \<Psi>\<^sub>P\<rangle>" by fact+
        have QTrans: "\<Psi> \<otimes> \<Psi>\<^sub>P \<rhd> Q \<longmapsto>K\<lparr>N\<rparr> \<prec> Q'" and FrQ: "extractFrame Q = \<langle>A\<^sub>Q, \<Psi>\<^sub>Q\<rangle>" by fact+
        from FrP \<open>x \<sharp> P\<close> have "x \<sharp> \<langle>A\<^sub>P, \<Psi>\<^sub>P\<rangle>"
          by(auto dest: extractFrameFresh)
        with \<open>A\<^sub>P \<sharp>* x\<close> have "x \<sharp> \<Psi>\<^sub>P" by(simp add: frameResChainFresh) (simp add: fresh_def name_list_supp)
        from PTrans
        have "\<Psi> \<otimes> \<Psi>\<^sub>Q \<rhd> P \<longmapsto> ROut M (\<lparr>\<nu>*xvec\<rparr>N \<prec>' P')"
          by(simp add: residualInject)
        with FrP \<open>distinct A\<^sub>P\<close> \<open>x \<sharp> P\<close> \<open>A\<^sub>P \<sharp>* \<Psi>\<close> \<open>A\<^sub>P \<sharp>* \<Psi>\<^sub>Q\<close> \<open>A\<^sub>P \<sharp>* x\<close> \<open>A\<^sub>P \<sharp>* P\<close> \<open>A\<^sub>P \<sharp>* M\<close> \<open>A\<^sub>Q \<sharp>* P\<close> \<open>A\<^sub>P \<sharp>* A\<^sub>Q\<close> \<open>xvec \<sharp>* M\<close> \<open>distinct xvec\<close>
        obtain M' where MeqM': "(\<Psi> \<otimes> \<Psi>\<^sub>Q) \<otimes> \<Psi>\<^sub>P \<turnstile> M \<leftrightarrow> M'" and "x \<sharp> M'" and "A\<^sub>Q \<sharp>* M'"
          by(elim outputObtainPrefix[where B="x#A\<^sub>Q"]) (assumption | force simp add: fresh_star_list_cons)+
        from MeqM' have MeqM': "\<Psi> \<otimes> \<Psi>\<^sub>P \<otimes> \<Psi>\<^sub>Q \<turnstile> M \<leftrightarrow> M'"
          by(metis statEqEnt Associativity Commutativity Composition)
        with \<open>\<Psi> \<otimes> \<Psi>\<^sub>P \<otimes> \<Psi>\<^sub>Q \<turnstile> M \<leftrightarrow> K\<close> have "\<Psi> \<otimes> \<Psi>\<^sub>P \<otimes> \<Psi>\<^sub>Q \<turnstile> K \<leftrightarrow> M'"
          by(blast intro: chanEqTrans chanEqSym)
        then have "(\<Psi> \<otimes> \<Psi>\<^sub>P) \<otimes> \<Psi>\<^sub>Q \<turnstile> K \<leftrightarrow> M'"
          by(metis statEqEnt Associativity Commutativity Composition)
        with QTrans FrQ \<open>distinct A\<^sub>Q\<close> have QTrans: "\<Psi> \<otimes> \<Psi>\<^sub>P \<rhd> Q \<longmapsto>M'\<lparr>N\<rparr> \<prec> Q'" using \<open>A\<^sub>Q \<sharp>* \<Psi>\<close> \<open>A\<^sub>Q \<sharp>* \<Psi>\<^sub>P\<close> \<open>A\<^sub>Q \<sharp>* Q\<close> \<open>A\<^sub>Q \<sharp>* K\<close> \<open>A\<^sub>Q \<sharp>* M'\<close>
          by(auto intro: inputRenameSubject)

        from PTrans \<open>x \<sharp> P\<close> \<open>xvec \<sharp>* x\<close> \<open>distinct xvec\<close> \<open>xvec \<sharp>* M\<close>
        have "x \<sharp> N" and "x \<sharp> P'" by(force intro: outputFreshDerivative)+
        from QTrans \<open>x \<sharp> \<Psi>\<close>  \<open>x \<sharp> \<Psi>\<^sub>P\<close> \<open>x \<sharp> M'\<close> \<open>x \<sharp> N\<close> have QTrans: "\<Psi> \<otimes> \<Psi>\<^sub>P \<rhd> \<lparr>\<nu>x\<rparr>Q \<longmapsto>M'\<lparr>N\<rparr> \<prec> \<lparr>\<nu>x\<rparr>Q'"
          by(intro Scope) (assumption | force)+

        note PTrans FrP QTrans
        moreover with \<open>extractFrame Q = \<langle>A\<^sub>Q, \<Psi>\<^sub>Q\<rangle>\<close> have "extractFrame(\<lparr>\<nu>x\<rparr>Q) = \<langle>(x#A\<^sub>Q), \<Psi>\<^sub>Q\<rangle>"
          by simp
        moreover note MeqM' \<open>A\<^sub>P \<sharp>* \<Psi>\<close> \<open>A\<^sub>P \<sharp>* P\<close>
        moreover from  \<open>A\<^sub>P \<sharp>* Q\<close> have "A\<^sub>P \<sharp>* (\<lparr>\<nu>x\<rparr>Q)" by(simp add: fresh_star_def abs_fresh)
        moreover from \<open>A\<^sub>P \<sharp>* A\<^sub>Q\<close> \<open>A\<^sub>P \<sharp>* x\<close> have "A\<^sub>P \<sharp>* (x#A\<^sub>Q)"
          by(simp add: fresh_star_def fresh_list_cons) (auto simp add: fresh_def name_list_supp)
        moreover from \<open>x \<sharp> \<Psi>\<close> \<open>A\<^sub>Q \<sharp>* \<Psi>\<close> have "(x#A\<^sub>Q) \<sharp>* \<Psi>" by simp
        moreover from \<open>x \<sharp> P\<close> \<open>A\<^sub>Q \<sharp>* P\<close> have "(x#A\<^sub>Q) \<sharp>* P" by simp
        moreover from \<open>x \<sharp> M'\<close> \<open>A\<^sub>Q \<sharp>* M'\<close> have "(x#A\<^sub>Q) \<sharp>* M'" by simp
        moreover from \<open>A\<^sub>Q \<sharp>* Q\<close> have "(x#A\<^sub>Q) \<sharp>* (\<lparr>\<nu>x\<rparr>Q)" by(simp add: fresh_star_def abs_fresh)
        moreover from \<open>xvec \<sharp>* Q\<close> have "(x#xvec) \<sharp>* (\<lparr>\<nu>x\<rparr>Q)" by(simp add: abs_fresh fresh_star_def)
        ultimately have "\<Psi> \<rhd> P \<parallel> \<lparr>\<nu>x\<rparr>Q \<longmapsto>\<tau> \<prec> \<lparr>\<nu>*xvec\<rparr>(P' \<parallel> \<lparr>\<nu>x\<rparr>Q')" using \<open>A\<^sub>P \<sharp>* M\<close>
          by(intro Comm2) (assumption | simp)+
        moreover from \<open>x \<sharp> \<Psi>\<close> \<open>x \<sharp> P'\<close> \<open>xvec \<sharp>* \<Psi>\<close> have "(\<Psi>, \<lparr>\<nu>*xvec\<rparr>(P' \<parallel> \<lparr>\<nu>x\<rparr>Q'), \<lparr>\<nu>x\<rparr>(\<lparr>\<nu>*xvec\<rparr>(P' \<parallel> Q'))) \<in> Rel" by(rule C2)
        ultimately show ?case by blast
      next
        case(cBrMerge \<Psi>\<^sub>Q M N P' A\<^sub>P \<Psi>\<^sub>P Q' A\<^sub>Q)
        have PTrans: "\<Psi> \<otimes> \<Psi>\<^sub>Q \<rhd> P \<longmapsto>\<questiondown>M\<lparr>N\<rparr> \<prec> P'" and FrP: "extractFrame P = \<langle>A\<^sub>P, \<Psi>\<^sub>P\<rangle>" by fact+
        have QTrans: "\<Psi> \<otimes> \<Psi>\<^sub>P \<rhd> Q \<longmapsto>\<questiondown>M\<lparr>N\<rparr> \<prec> Q'" and FrQ: "extractFrame Q = \<langle>A\<^sub>Q, \<Psi>\<^sub>Q\<rangle>" by fact+
        from FrP \<open>x \<sharp> P\<close> have "x \<sharp> \<langle>A\<^sub>P, \<Psi>\<^sub>P\<rangle>"
          by(auto dest: extractFrameFresh)
        with \<open>A\<^sub>P \<sharp>* x\<close> have "x \<sharp> \<Psi>\<^sub>P"
          by(simp add: frameResChainFresh) (simp add: fresh_def name_list_supp)
        from \<open>x \<sharp> \<alpha>\<close> \<open>\<alpha> = \<questiondown>M\<lparr>N\<rparr>\<close> have "x \<sharp> M" and "x \<sharp> N" by simp+
        from PTrans \<open>x \<sharp> P\<close> \<open>x \<sharp> N\<close>
        have "x \<sharp> P'"
          by(rule brinputFreshDerivative)
        from QTrans \<open>x \<sharp> \<Psi>\<close>  \<open>x \<sharp> \<Psi>\<^sub>P\<close> \<open>x \<sharp> M\<close> \<open>x \<sharp> N\<close> have QTrans: "\<Psi> \<otimes> \<Psi>\<^sub>P \<rhd> \<lparr>\<nu>x\<rparr>Q \<longmapsto>\<questiondown>M\<lparr>N\<rparr> \<prec> \<lparr>\<nu>x\<rparr>Q'"
          by(intro Scope) (assumption | force)+

        note PTrans FrP QTrans
        moreover with \<open>extractFrame Q = \<langle>A\<^sub>Q, \<Psi>\<^sub>Q\<rangle>\<close> have "extractFrame(\<lparr>\<nu>x\<rparr>Q) = \<langle>(x#A\<^sub>Q), \<Psi>\<^sub>Q\<rangle>"
          by simp
        moreover note \<open>A\<^sub>P \<sharp>* \<Psi>\<close> \<open>A\<^sub>P \<sharp>* P\<close>
        moreover from  \<open>A\<^sub>P \<sharp>* Q\<close> have "A\<^sub>P \<sharp>* (\<lparr>\<nu>x\<rparr>Q)" by(simp add: fresh_star_def abs_fresh)
        moreover from \<open>A\<^sub>P \<sharp>* A\<^sub>Q\<close> \<open>A\<^sub>P \<sharp>* x\<close> have "A\<^sub>P \<sharp>* (x#A\<^sub>Q)"
          by(simp add: fresh_star_def fresh_list_cons) (auto simp add: fresh_def name_list_supp)
        moreover from \<open>x \<sharp> \<Psi>\<close> \<open>A\<^sub>Q \<sharp>* \<Psi>\<close> have "(x#A\<^sub>Q) \<sharp>* \<Psi>" by simp
        moreover from \<open>x \<sharp> P\<close> \<open>A\<^sub>Q \<sharp>* P\<close> have "(x#A\<^sub>Q) \<sharp>* P" by simp
        moreover from \<open>x \<sharp> M\<close> \<open>A\<^sub>Q \<sharp>* M\<close> have "(x#A\<^sub>Q) \<sharp>* M" by simp
        moreover from \<open>A\<^sub>Q \<sharp>* Q\<close> have "(x#A\<^sub>Q) \<sharp>* (\<lparr>\<nu>x\<rparr>Q)" by(simp add: fresh_star_def abs_fresh)
        ultimately have Trans: "\<Psi> \<rhd> P \<parallel> \<lparr>\<nu>x\<rparr>Q \<longmapsto>\<questiondown>M\<lparr>N\<rparr> \<prec> (P' \<parallel> \<lparr>\<nu>x\<rparr>Q')" using \<open>A\<^sub>P \<sharp>* M\<close>
          by(intro BrMerge) (assumption | simp)+
        from \<open>x \<sharp> \<Psi>\<close> \<open>x \<sharp> P'\<close> have "(\<Psi>, (P' \<parallel> (\<lparr>\<nu>*[x]\<rparr>Q')), \<lparr>\<nu>*[x]\<rparr>(P' \<parallel> Q')) \<in> Rel"
          by(intro C3) simp+
        then have Relation: "(\<Psi>, (P' \<parallel> (\<lparr>\<nu>x\<rparr>Q')), \<lparr>\<nu>x\<rparr>(P' \<parallel> Q')) \<in> Rel" by simp
        with Trans Relation show ?case by blast
      next
        case(cBrComm1 \<Psi>\<^sub>Q M N P' A\<^sub>P \<Psi>\<^sub>P xvec Q' A\<^sub>Q)
        from \<open>x \<sharp> \<alpha>\<close> \<open>\<exclamdown>M\<lparr>\<nu>*xvec\<rparr>\<langle>N\<rangle> = \<alpha>\<close> have "x \<sharp> M" and "x \<sharp> xvec" and "x \<sharp> N" by force+
        have PTrans: "\<Psi> \<otimes> \<Psi>\<^sub>Q \<rhd> P \<longmapsto>\<questiondown>M\<lparr>N\<rparr> \<prec> P'" and FrP: "extractFrame P = \<langle>A\<^sub>P, \<Psi>\<^sub>P\<rangle>" by fact+
        have QTrans: "\<Psi> \<otimes> \<Psi>\<^sub>P \<rhd> Q \<longmapsto>\<exclamdown>M\<lparr>\<nu>*xvec\<rparr>\<langle>N\<rangle> \<prec> Q'" and FrQ: "extractFrame Q = \<langle>A\<^sub>Q, \<Psi>\<^sub>Q\<rangle>" by fact+
        from FrP \<open>x \<sharp> P\<close> have "x \<sharp> \<langle>A\<^sub>P, \<Psi>\<^sub>P\<rangle>"
          by(auto dest: extractFrameFresh)
        with \<open>A\<^sub>P \<sharp>* x\<close> have "x \<sharp> \<Psi>\<^sub>P"
          by(simp add: frameResChainFresh) (simp add: fresh_def name_list_supp)
        show ?case
        proof(cases "x \<in> supp N")
          note PTrans FrP
          moreover assume "x \<in> supp N"
          with \<open>x \<sharp> N\<close> have False
            by(simp add: fresh_def)
          then show ?case
            by simp
        next
          note PTrans FrP
          moreover assume "x \<notin> supp N"
          from QTrans \<open>x \<sharp> \<Psi>\<close> \<open>x \<sharp> \<Psi>\<^sub>P\<close> \<open>x \<sharp> M\<close> \<open>x \<sharp> N\<close> \<open>x \<sharp> xvec\<close>
          have QTrans: "\<Psi> \<otimes> \<Psi>\<^sub>P \<rhd> \<lparr>\<nu>x\<rparr>Q \<longmapsto>\<exclamdown>M\<lparr>\<nu>*xvec\<rparr>\<langle>N\<rangle> \<prec> \<lparr>\<nu>x\<rparr>Q'"
            by(intro Scope) (assumption | force)+
          moreover from PTrans \<open>x \<sharp> P\<close> \<open>x \<sharp> N\<close> have "x \<sharp> P'" by(rule brinputFreshDerivative)
          with \<open>extractFrame Q = \<langle>A\<^sub>Q, \<Psi>\<^sub>Q\<rangle>\<close> have "extractFrame(\<lparr>\<nu>x\<rparr>Q) = \<langle>(x#A\<^sub>Q), \<Psi>\<^sub>Q\<rangle>"
            by simp
          moreover note \<open>A\<^sub>P \<sharp>* \<Psi>\<close> \<open>A\<^sub>P \<sharp>* P\<close>
          moreover from  \<open>A\<^sub>P \<sharp>* Q\<close> have "A\<^sub>P \<sharp>* (\<lparr>\<nu>x\<rparr>Q)" by(simp add: fresh_star_def abs_fresh)
          moreover from \<open>A\<^sub>P \<sharp>* A\<^sub>Q\<close> \<open>A\<^sub>P \<sharp>* x\<close> have "A\<^sub>P \<sharp>* (x#A\<^sub>Q)"
            by(simp add: fresh_star_def fresh_list_cons) (auto simp add: fresh_def name_list_supp)
          moreover from \<open>x \<sharp> \<Psi>\<close> \<open>A\<^sub>Q \<sharp>* \<Psi>\<close> have "(x#A\<^sub>Q) \<sharp>* \<Psi>" by simp
          moreover from \<open>x \<sharp> P\<close> \<open>A\<^sub>Q \<sharp>* P\<close> have "(x#A\<^sub>Q) \<sharp>* P" by simp
          moreover from \<open>x \<sharp> M\<close> \<open>A\<^sub>Q \<sharp>* M\<close> have "(x#A\<^sub>Q) \<sharp>* M" by simp
          moreover from \<open>A\<^sub>Q \<sharp>* Q\<close> have "(x#A\<^sub>Q) \<sharp>* (\<lparr>\<nu>x\<rparr>Q)" by(simp add: fresh_star_def abs_fresh)
          moreover from \<open>x \<sharp> P\<close> \<open>xvec \<sharp>* P\<close> have "(x#xvec) \<sharp>* P" by(simp)
          ultimately have Trans: "\<Psi> \<rhd> P \<parallel> \<lparr>\<nu>x\<rparr>Q \<longmapsto>\<exclamdown>M\<lparr>\<nu>*xvec\<rparr>\<langle>N\<rangle> \<prec> (P' \<parallel> \<lparr>\<nu>x\<rparr>Q')" using \<open>A\<^sub>P \<sharp>* M\<close>
            by(intro BrComm1) (assumption | simp)+
          from \<open>x \<sharp> \<Psi>\<close> \<open>x \<sharp> P'\<close> have "(\<Psi>, (P' \<parallel> (\<lparr>\<nu>*[x]\<rparr>Q')), \<lparr>\<nu>*[x]\<rparr>(P' \<parallel> Q')) \<in> Rel"
            by(intro C3) simp+
          then have Relation: "(\<Psi>, (P' \<parallel> (\<lparr>\<nu>x\<rparr>Q')), \<lparr>\<nu>x\<rparr>(P' \<parallel> Q')) \<in> Rel" by simp
          from Trans Relation show ?case by blast
        qed
      next
        case(cBrComm2 \<Psi>\<^sub>Q M xvec N P' A\<^sub>P \<Psi>\<^sub>P Q' A\<^sub>Q)
        from \<open>x \<sharp> \<alpha>\<close> \<open>\<exclamdown>M\<lparr>\<nu>*xvec\<rparr>\<langle>N\<rangle> = \<alpha>\<close> have "x \<sharp> M" and "x \<sharp> xvec" and "x \<sharp> N" by force+
        have PTrans: "\<Psi> \<otimes> \<Psi>\<^sub>Q \<rhd> P \<longmapsto>\<exclamdown>M\<lparr>\<nu>*xvec\<rparr>\<langle>N\<rangle> \<prec> P'" and FrP: "extractFrame P = \<langle>A\<^sub>P, \<Psi>\<^sub>P\<rangle>" by fact+
        have QTrans: "\<Psi> \<otimes> \<Psi>\<^sub>P \<rhd> Q \<longmapsto>\<questiondown>M\<lparr>N\<rparr> \<prec> Q'" and FrQ: "extractFrame Q = \<langle>A\<^sub>Q, \<Psi>\<^sub>Q\<rangle>" by fact+
        from FrP \<open>x \<sharp> P\<close> have "x \<sharp> \<langle>A\<^sub>P, \<Psi>\<^sub>P\<rangle>"
          by(auto dest: extractFrameFresh)
        with \<open>A\<^sub>P \<sharp>* x\<close> have "x \<sharp> \<Psi>\<^sub>P"
          by(simp add: frameResChainFresh) (simp add: fresh_def name_list_supp)
        from PTrans \<open>x \<sharp> P\<close> \<open>x \<sharp> xvec\<close> \<open>distinct xvec\<close> \<open>xvec \<sharp>* M\<close>
        have "x \<sharp> N" and "x \<sharp> P'" by(force intro: broutputFreshDerivative)+
        from QTrans \<open>x \<sharp> \<Psi>\<close>  \<open>x \<sharp> \<Psi>\<^sub>P\<close> \<open>x \<sharp> M\<close> \<open>x \<sharp> N\<close> have QTrans: "\<Psi> \<otimes> \<Psi>\<^sub>P \<rhd> \<lparr>\<nu>x\<rparr>Q \<longmapsto>\<questiondown>M\<lparr>N\<rparr> \<prec> \<lparr>\<nu>x\<rparr>Q'"
          by(intro Scope) (assumption | force)+

        note PTrans FrP QTrans
        moreover with \<open>extractFrame Q = \<langle>A\<^sub>Q, \<Psi>\<^sub>Q\<rangle>\<close> have "extractFrame(\<lparr>\<nu>x\<rparr>Q) = \<langle>(x#A\<^sub>Q), \<Psi>\<^sub>Q\<rangle>"
          by simp
        moreover note \<open>A\<^sub>P \<sharp>* \<Psi>\<close> \<open>A\<^sub>P \<sharp>* P\<close>
        moreover from  \<open>A\<^sub>P \<sharp>* Q\<close> have "A\<^sub>P \<sharp>* (\<lparr>\<nu>x\<rparr>Q)" by(simp add: fresh_star_def abs_fresh)
        moreover from \<open>A\<^sub>P \<sharp>* A\<^sub>Q\<close> \<open>A\<^sub>P \<sharp>* x\<close> have "A\<^sub>P \<sharp>* (x#A\<^sub>Q)"
          by(simp add: fresh_star_def fresh_list_cons) (auto simp add: fresh_def name_list_supp)
        moreover from \<open>x \<sharp> \<Psi>\<close> \<open>A\<^sub>Q \<sharp>* \<Psi>\<close> have "(x#A\<^sub>Q) \<sharp>* \<Psi>" by simp
        moreover from \<open>x \<sharp> P\<close> \<open>A\<^sub>Q \<sharp>* P\<close> have "(x#A\<^sub>Q) \<sharp>* P" by simp
        moreover from \<open>x \<sharp> M\<close> \<open>A\<^sub>Q \<sharp>* M\<close> have "(x#A\<^sub>Q) \<sharp>* M" by simp
        moreover from \<open>A\<^sub>Q \<sharp>* Q\<close> have "(x#A\<^sub>Q) \<sharp>* (\<lparr>\<nu>x\<rparr>Q)" by(simp add: fresh_star_def abs_fresh)
        moreover from \<open>xvec \<sharp>* Q\<close> have "(x#xvec) \<sharp>* (\<lparr>\<nu>x\<rparr>Q)" by(simp add: abs_fresh fresh_star_def)
        ultimately have Trans: "\<Psi> \<rhd> P \<parallel> \<lparr>\<nu>x\<rparr>Q \<longmapsto>\<exclamdown>M\<lparr>\<nu>*xvec\<rparr>\<langle>N\<rangle> \<prec> (P' \<parallel> \<lparr>\<nu>x\<rparr>Q')" using \<open>A\<^sub>P \<sharp>* M\<close>
          by(intro BrComm2) (assumption | simp)+
        from \<open>x \<sharp> \<Psi>\<close> \<open>x \<sharp> P'\<close> have "(\<Psi>, (P' \<parallel> (\<lparr>\<nu>*[x]\<rparr>Q')), \<lparr>\<nu>*[x]\<rparr>(P' \<parallel> Q')) \<in> Rel"
          by(intro C3) simp+
        then have Relation: "(\<Psi>, (P' \<parallel> \<lparr>\<nu>x\<rparr>Q'), \<lparr>\<nu>x\<rparr>(P' \<parallel> Q')) \<in> Rel" by simp
        from Trans Relation show ?case by blast
      qed
    next
      case(cBrClose M xvec N PQ)
      from \<open>xvec \<sharp>* (P \<parallel> Q)\<close> have "xvec \<sharp>* P" and "xvec \<sharp>* Q" by simp+
      note \<open>\<Psi> \<rhd> P \<parallel> Q \<longmapsto> \<exclamdown>M\<lparr>\<nu>*xvec\<rparr>\<langle>N\<rangle> \<prec> PQ\<close> \<open>xvec \<sharp>* \<Psi>\<close> \<open>xvec \<sharp>* P\<close> \<open>xvec \<sharp>* Q\<close> \<open>xvec \<sharp>* M\<close>
      then show ?case
      proof(induct rule: parBrOutputCases[where C=x])
        case(cPar1 P' A\<^sub>Q \<Psi>\<^sub>Q)
        from \<open>\<Psi> \<otimes> \<Psi>\<^sub>Q \<rhd> P \<longmapsto> \<exclamdown>M\<lparr>\<nu>*xvec\<rparr>\<langle>N\<rangle> \<prec> P'\<close> \<open>xvec \<sharp>* M\<close> \<open>x \<sharp> P\<close>
        have "x \<sharp> M"
          by(rule brOutputFreshSubject)
        with \<open>x \<in> supp M\<close> have False
          by(simp add: fresh_def)
        then show ?case
          by simp
      next
        case(cPar2 Q' A\<^sub>P \<Psi>\<^sub>P)
        from \<open>A\<^sub>P \<sharp>* x\<close> have "x \<sharp> A\<^sub>P" by simp
        with \<open>x \<sharp> P\<close> \<open>extractFrame P = \<langle>A\<^sub>P, \<Psi>\<^sub>P\<rangle>\<close>
        have "x \<sharp> \<Psi>\<^sub>P"
          apply(drule_tac extractFrameFresh)
          by(simp add: frameResChainFresh) (simp add: fresh_def name_list_supp)
        from \<open>x \<sharp> \<Psi>\<close> \<open>x \<sharp> \<Psi>\<^sub>P\<close> have "x \<sharp> (\<Psi> \<otimes> \<Psi>\<^sub>P)" by force
        from \<open>\<Psi> \<otimes> \<Psi>\<^sub>P \<rhd> Q \<longmapsto> \<exclamdown>M\<lparr>\<nu>*xvec\<rparr>\<langle>N\<rangle> \<prec> Q'\<close> \<open>x \<in> supp M\<close> \<open>x \<sharp> (\<Psi> \<otimes> \<Psi>\<^sub>P)\<close>
        have QTrans: "\<Psi> \<otimes> \<Psi>\<^sub>P \<rhd> \<lparr>\<nu>x\<rparr>Q \<longmapsto> \<tau> \<prec> \<lparr>\<nu>x\<rparr>(\<lparr>\<nu>*xvec\<rparr>Q')"
          by(rule BrClose)
        with \<open>extractFrame P = \<langle>A\<^sub>P, \<Psi>\<^sub>P\<rangle>\<close> \<open>A\<^sub>P \<sharp>* \<Psi>\<close> \<open>x \<sharp> A\<^sub>P\<close> \<open>A\<^sub>P \<sharp>* Q\<close>
        have Trans: "\<Psi> \<rhd> (P \<parallel> \<lparr>\<nu>x\<rparr>Q) \<longmapsto> \<tau> \<prec> (P \<parallel> \<lparr>\<nu>x\<rparr>(\<lparr>\<nu>*xvec\<rparr>Q'))"
          by(intro Par2) (assumption | simp)+
        from \<open>x \<sharp> P\<close> \<open>xvec \<sharp>* P\<close> have "(x#xvec) \<sharp>* P" by simp
        moreover from \<open>x \<sharp> \<Psi>\<close> \<open>xvec \<sharp>* \<Psi>\<close> have "(x#xvec) \<sharp>* \<Psi>" by simp
        ultimately have "(\<Psi>, (P \<parallel> (\<lparr>\<nu>*(x#xvec)\<rparr>Q')), (\<lparr>\<nu>*(x#xvec)\<rparr>P \<parallel> Q')) \<in> Rel"
          by(rule C3)
        then have Relation: "(\<Psi>, (P \<parallel> \<lparr>\<nu>x\<rparr>(\<lparr>\<nu>*xvec\<rparr>Q')), \<lparr>\<nu>x\<rparr>(\<lparr>\<nu>*xvec\<rparr>P \<parallel> Q')) \<in> Rel"
          by simp
        from Trans Relation
        show ?case
          by blast
      next
        case(cBrComm1 \<Psi>\<^sub>Q P' A\<^sub>P \<Psi>\<^sub>P Q' A\<^sub>Q)
        from \<open>\<Psi> \<otimes> \<Psi>\<^sub>Q \<rhd> P \<longmapsto> \<questiondown>M\<lparr>N\<rparr> \<prec> P'\<close> \<open>x \<sharp> P\<close>
        have "x \<sharp> M"
          by(rule brInputFreshSubject)
        with \<open>x \<in> supp M\<close> have False
          by(simp add: fresh_def)
        then show ?case
          by simp
      next
        case(cBrComm2 \<Psi>\<^sub>Q P' A\<^sub>P \<Psi>\<^sub>P Q' A\<^sub>Q)
        from \<open>\<Psi> \<otimes> \<Psi>\<^sub>Q \<rhd> P \<longmapsto> \<exclamdown>M\<lparr>\<nu>*xvec\<rparr>\<langle>N\<rangle> \<prec> P'\<close> \<open>xvec \<sharp>* M\<close> \<open>x \<sharp> P\<close>
        have "x \<sharp> M"
          by(rule brOutputFreshSubject)
        with \<open>x \<in> supp M\<close> have False
          by(simp add: fresh_def)
        then show ?case
          by simp
      qed
    qed
  qed
qed

lemma simParComm:
  fixes \<Psi>   :: 'b
    and P   :: "('a, 'b, 'c) psi"
    and Q   :: "('a, 'b, 'c) psi"
    and Rel :: "('b \<times> ('a, 'b, 'c) psi \<times> ('a, 'b, 'c) psi) set"

assumes "eqvt Rel"
  and   C1: "\<And>\<Psi>' R S. (\<Psi>', R \<parallel> S, S \<parallel> R) \<in> Rel"
  and   C2: "\<And>\<Psi>' R S xvec. \<lbrakk>(\<Psi>', R, S) \<in> Rel; xvec \<sharp>* \<Psi>'\<rbrakk> \<Longrightarrow> (\<Psi>', \<lparr>\<nu>*xvec\<rparr>R, \<lparr>\<nu>*xvec\<rparr>S) \<in> Rel"

shows "\<Psi> \<rhd> P \<parallel> Q \<leadsto>[Rel] Q \<parallel> P"
  using \<open>eqvt Rel\<close>
proof(induct rule: simI[of _ _ _ _ "()"])
  case(cSim \<alpha> PQ)
  from \<open>bn \<alpha> \<sharp>* (P \<parallel> Q)\<close> have "bn \<alpha> \<sharp>* Q" and "bn \<alpha> \<sharp>* P" by simp+
  with \<open>\<Psi> \<rhd> Q \<parallel> P \<longmapsto>\<alpha> \<prec> PQ\<close> \<open>bn \<alpha> \<sharp>* \<Psi>\<close> show ?case using \<open>bn \<alpha> \<sharp>* subject \<alpha>\<close>
  proof(induct rule: parCases[where C="()"])
    case(cPar1 Q' A\<^sub>P \<Psi>\<^sub>P)
    from \<open>\<Psi> \<otimes> \<Psi>\<^sub>P \<rhd> Q \<longmapsto>\<alpha>\<prec> Q'\<close> \<open>extractFrame P = \<langle>A\<^sub>P, \<Psi>\<^sub>P\<rangle>\<close> \<open>bn \<alpha> \<sharp>* P\<close> \<open>A\<^sub>P \<sharp>* \<Psi>\<close> \<open>A\<^sub>P \<sharp>* Q\<close> \<open>A\<^sub>P \<sharp>* \<alpha>\<close>
    have "\<Psi> \<rhd> P \<parallel> Q \<longmapsto>\<alpha> \<prec> (P \<parallel> Q')" by(rule Par2)
    moreover have "(\<Psi>, P \<parallel> Q', Q' \<parallel> P) \<in> Rel" by(rule C1)
    ultimately show ?case by blast
  next
    case(cPar2 P' A\<^sub>Q \<Psi>\<^sub>Q)
    from \<open>\<Psi> \<otimes> \<Psi>\<^sub>Q \<rhd> P \<longmapsto>\<alpha> \<prec> P'\<close> \<open>extractFrame Q = \<langle>A\<^sub>Q, \<Psi>\<^sub>Q\<rangle>\<close> \<open>bn \<alpha> \<sharp>* Q\<close> \<open>A\<^sub>Q \<sharp>* \<Psi>\<close> \<open>A\<^sub>Q \<sharp>* P\<close> \<open>A\<^sub>Q \<sharp>* \<alpha>\<close>
    have "\<Psi> \<rhd> P \<parallel> Q \<longmapsto>\<alpha> \<prec> (P' \<parallel> Q)" by(rule Par1)
    moreover have "(\<Psi>, P' \<parallel> Q, Q \<parallel> P') \<in> Rel" by(rule C1)
    ultimately show ?case by blast
  next
    case(cComm1 \<Psi>\<^sub>P M N Q' A\<^sub>Q \<Psi>\<^sub>Q K xvec P' A\<^sub>P)
    note \<open>\<Psi> \<otimes> \<Psi>\<^sub>Q \<rhd> P \<longmapsto>K\<lparr>\<nu>*xvec\<rparr>\<langle>N\<rangle> \<prec> P'\<close> \<open>extractFrame P = \<langle>A\<^sub>P, \<Psi>\<^sub>P\<rangle>\<close>
      \<open>\<Psi> \<otimes> \<Psi>\<^sub>P \<rhd> Q \<longmapsto>M\<lparr>N\<rparr> \<prec> Q'\<close> \<open>extractFrame Q = \<langle>A\<^sub>Q, \<Psi>\<^sub>Q\<rangle>\<close>
    moreover from \<open>\<Psi> \<otimes> \<Psi>\<^sub>Q \<otimes> \<Psi>\<^sub>P \<turnstile> M \<leftrightarrow> K\<close>
    have "\<Psi> \<otimes> \<Psi>\<^sub>Q \<otimes> \<Psi>\<^sub>P \<turnstile> K \<leftrightarrow> M"
      by(rule chanEqSym)
    then have "\<Psi> \<otimes> \<Psi>\<^sub>P \<otimes> \<Psi>\<^sub>Q \<turnstile> K \<leftrightarrow> M"
      by(blast intro: statEqEnt compositionSym Commutativity)
    ultimately have "\<Psi> \<rhd> P \<parallel> Q \<longmapsto>\<tau> \<prec> \<lparr>\<nu>*xvec\<rparr>(P' \<parallel> Q')"
      using \<open>A\<^sub>P \<sharp>* \<Psi>\<close> \<open>A\<^sub>P \<sharp>* P\<close> \<open>A\<^sub>P \<sharp>* Q\<close> \<open>A\<^sub>Q \<sharp>* A\<^sub>P\<close> \<open>A\<^sub>Q \<sharp>* \<Psi>\<close> \<open>A\<^sub>Q \<sharp>* P\<close> \<open>A\<^sub>Q \<sharp>* Q\<close> \<open>xvec \<sharp>* Q\<close> \<open>A\<^sub>P \<sharp>* K\<close> \<open>A\<^sub>Q \<sharp>* M\<close>
      by(intro Comm2) (assumption | simp)+
    moreover have "(\<Psi>, P' \<parallel> Q', Q' \<parallel> P') \<in> Rel" by(rule C1)
    then have "(\<Psi>, \<lparr>\<nu>*xvec\<rparr>(P' \<parallel> Q'), \<lparr>\<nu>*xvec\<rparr>(Q' \<parallel> P')) \<in> Rel" using \<open>xvec \<sharp>* \<Psi>\<close> by(rule C2)
    ultimately show ?case by blast
  next
    case(cComm2 \<Psi>\<^sub>P M xvec N Q' A\<^sub>Q \<Psi>\<^sub>Q K P' A\<^sub>P)
    note \<open>\<Psi> \<otimes> \<Psi>\<^sub>Q \<rhd> P \<longmapsto>K\<lparr>N\<rparr> \<prec> P'\<close> \<open>extractFrame P = \<langle>A\<^sub>P, \<Psi>\<^sub>P\<rangle>\<close>
      \<open>\<Psi> \<otimes> \<Psi>\<^sub>P \<rhd> Q \<longmapsto>M\<lparr>\<nu>*xvec\<rparr>\<langle>N\<rangle> \<prec> Q'\<close> \<open>extractFrame Q = \<langle>A\<^sub>Q, \<Psi>\<^sub>Q\<rangle>\<close>
    moreover from \<open>\<Psi> \<otimes> \<Psi>\<^sub>Q \<otimes> \<Psi>\<^sub>P \<turnstile> M \<leftrightarrow> K\<close>
    have "\<Psi> \<otimes> \<Psi>\<^sub>Q \<otimes> \<Psi>\<^sub>P \<turnstile> K \<leftrightarrow> M"
      by(rule chanEqSym)
    then have "\<Psi> \<otimes> \<Psi>\<^sub>P \<otimes> \<Psi>\<^sub>Q \<turnstile> K \<leftrightarrow> M"
      by(blast intro: statEqEnt compositionSym Commutativity)
    ultimately have "\<Psi> \<rhd> P \<parallel> Q \<longmapsto>\<tau> \<prec> \<lparr>\<nu>*xvec\<rparr>(P' \<parallel> Q')"
      using \<open>A\<^sub>P \<sharp>* \<Psi>\<close> \<open>A\<^sub>P \<sharp>* P\<close> \<open>A\<^sub>P \<sharp>* Q\<close> \<open>A\<^sub>Q \<sharp>* A\<^sub>P\<close> \<open>A\<^sub>Q \<sharp>* \<Psi>\<close> \<open>A\<^sub>Q \<sharp>* P\<close> \<open>A\<^sub>Q \<sharp>* Q\<close> \<open>xvec \<sharp>* P\<close> \<open>A\<^sub>P \<sharp>* K\<close> \<open>A\<^sub>Q \<sharp>* M\<close>
      by(intro Comm1) (assumption | simp add: freshChainSym)+
    moreover have "(\<Psi>, P' \<parallel> Q', Q' \<parallel> P') \<in> Rel" by(rule C1)
    then have "(\<Psi>, \<lparr>\<nu>*xvec\<rparr>(P' \<parallel> Q'), \<lparr>\<nu>*xvec\<rparr>(Q' \<parallel> P')) \<in> Rel" using \<open>xvec \<sharp>* \<Psi>\<close> by(rule C2)
    ultimately show ?case by blast
  next
    case(cBrMerge \<Psi>\<^sub>P M N Q' A\<^sub>Q \<Psi>\<^sub>Q P' A\<^sub>P)
    then have "\<Psi> \<rhd> P \<parallel> Q \<longmapsto> \<questiondown>M\<lparr>N\<rparr> \<prec> P' \<parallel> Q'"
      by(intro BrMerge) (assumption|simp)+
    then show ?case by(blast intro: C1)
  next
    case(cBrComm1 \<Psi>\<^sub>P M N Q' A\<^sub>Q \<Psi>\<^sub>Q xvec P' A\<^sub>P)
    then have "\<Psi> \<rhd> P \<parallel> Q \<longmapsto> \<exclamdown>M\<lparr>\<nu>*xvec\<rparr>\<langle>N\<rangle> \<prec> P' \<parallel> Q'"
      by(intro BrComm2) (assumption|simp)+
    then show ?case by(blast intro: C1)
  next
    case(cBrComm2 \<Psi>\<^sub>P M xvec N Q' A\<^sub>Q \<Psi>\<^sub>Q P' A\<^sub>P)
    then have "\<Psi> \<rhd> P \<parallel> Q \<longmapsto> \<exclamdown>M\<lparr>\<nu>*xvec\<rparr>\<langle>N\<rangle> \<prec> P' \<parallel> Q'"
      by(intro BrComm1) (assumption|simp)+
    then show ?case by(blast intro: C1)
  qed
qed

lemma bangExtLeft:
  fixes \<Psi> :: 'b
    and P :: "('a, 'b, 'c) psi"

assumes "guarded P"
  and   "\<And>\<Psi>' Q. (\<Psi>', Q, Q) \<in> Rel"

shows "\<Psi> \<rhd> !P \<leadsto>[Rel] P \<parallel> !P"
  using assms
  by(auto simp add: simulation_def dest: Bang)

lemma bangExtRight:
  fixes \<Psi> :: 'b
    and P :: "('a, 'b, 'c) psi"

assumes C1: "\<And>\<Psi>' Q. (\<Psi>', Q, Q) \<in> Rel"

shows "\<Psi> \<rhd> P \<parallel> !P \<leadsto>[Rel] !P"
proof -
  {
    fix \<alpha> P'
    assume "\<Psi> \<rhd> !P \<longmapsto>\<alpha> \<prec> P'"
    then have "\<Psi> \<rhd> P \<parallel> !P \<longmapsto>\<alpha> \<prec> P'"
      apply -
      by(ind_cases "\<Psi> \<rhd> !P \<longmapsto>\<alpha> \<prec> P'") (auto simp add: psi.inject)
    moreover have "(\<Psi>, P', P') \<in> Rel" by(rule C1)
    ultimately have "\<exists>P''. \<Psi> \<rhd> P \<parallel> !P \<longmapsto>\<alpha> \<prec> P'' \<and> (\<Psi>, P'', P') \<in> Rel"
      by blast
  }
  then show ?thesis
    by(auto simp add: simulation_def)
qed

end

end
