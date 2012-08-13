(* 
   Title: Psi-calculi   
   Author/Maintainer: Jesper Bengtson (jebe@itu.dk), 2012
*)
theory Weak_Bisimulation
  imports Weak_Simulation Weak_Stat_Imp Bisim_Struct_Cong
begin

context env begin

lemma monoCoinduct: "\<And>x y xa xb xc P Q \<Psi>.
                      x \<le> y \<Longrightarrow>
                      (\<Psi> \<rhd> Q \<leadsto><{(xc, xb, xa). x xc xb xa}> P) \<longrightarrow>
                     (\<Psi> \<rhd> Q \<leadsto><{(xb, xa, xc). y xb xa xc}> P)"
apply auto
apply(rule weakSimMonotonic)
by(auto dest: le_funE)

lemma monoCoinduct2: "\<And>x y xa xb xc P Q \<Psi>.
                      x \<le> y \<Longrightarrow>
                      (\<Psi> \<rhd> Q \<lessapprox><{(xc, xb, xa). x xc xb xa}> P) \<longrightarrow>
                     (\<Psi> \<rhd> Q \<lessapprox><{(xb, xa, xc). y xb xa xc}> P)"
apply auto
apply(rule weakStatImpMonotonic)
by(auto dest: le_funE)

coinductive_set weakBisim :: "('b \<times> ('a, 'b, 'c) psi \<times> ('a, 'b, 'c) psi) set" 
where
  step: "\<lbrakk>\<Psi> \<rhd> P \<lessapprox><weakBisim> Q; \<Psi> \<rhd> P \<leadsto><weakBisim> Q;
          \<forall>\<Psi>'. (\<Psi> \<otimes> \<Psi>',  P, Q) \<in> weakBisim; (\<Psi>, Q, P) \<in> weakBisim\<rbrakk> \<Longrightarrow> (\<Psi>, P, Q) \<in> weakBisim"
monos monoCoinduct monoCoinduct2

abbreviation
  weakBisimJudge ("_ \<rhd> _ \<approx> _" [70, 70, 70] 65) where "\<Psi> \<rhd> P \<approx> Q \<equiv> (\<Psi>, P, Q) \<in> weakBisim"
abbreviation
  weakBisimNilJudge ("_ \<approx> _" [70, 70] 65) where "P \<approx> Q \<equiv> \<one> \<rhd> P \<approx> Q"

lemma weakBisimCoinductAux[consumes 1]:
  fixes F :: 'b
  and   P :: "('a, 'b, 'c) psi"
  and   Q :: "('a, 'b, 'c) psi"
  and   X :: "('b \<times> ('a, 'b, 'c) psi \<times> ('a, 'b, 'c) psi) set"

  assumes "(\<Psi>, P, Q) \<in> X"
  and     "\<And>\<Psi> P Q. (\<Psi>, P, Q) \<in> X \<Longrightarrow> (\<Psi> \<rhd> P \<lessapprox><(X \<union> weakBisim)> Q) \<and>
                                      (\<Psi> \<rhd> P \<leadsto><(X \<union> weakBisim)> Q) \<and>
                                      (\<forall>\<Psi>'. (\<Psi> \<otimes> \<Psi>', P, Q) \<in> X \<or> (\<Psi> \<otimes> \<Psi>', P, Q) \<in> weakBisim) \<and>
                                      ((\<Psi>, Q, P) \<in> X \<or> (\<Psi>, Q, P) \<in> weakBisim)"

  shows "(\<Psi>, P, Q) \<in> weakBisim"
proof -
  have "X \<union> weakBisim = {(\<Psi>, P, Q). (\<Psi>, P, Q) \<in> X \<or> (\<Psi>, P, Q) \<in> weakBisim}" by auto
  with assms show ?thesis
    by coinduct (simp add: rtrancl_def)
qed

lemma weakBisimCoinduct[consumes 1, case_names cStatImp cSim cExt cSym]:
  fixes F :: 'b
  and   P :: "('a, 'b, 'c) psi"
  and   Q :: "('a, 'b, 'c) psi"
  and   X :: "('b \<times> ('a, 'b, 'c) psi \<times> ('a, 'b, 'c) psi) set"

  assumes "(\<Psi>, P, Q) \<in> X"
  and     "\<And>\<Psi>' R S. (\<Psi>', R, S) \<in> X \<Longrightarrow> \<Psi>' \<rhd> R \<lessapprox><(X \<union> weakBisim)> S"
  and     "\<And>\<Psi>' R S. (\<Psi>', R, S) \<in> X \<Longrightarrow> \<Psi>' \<rhd> R \<leadsto><(X \<union> weakBisim)> S"
  and     "\<And>\<Psi>' R S \<Psi>''. (\<Psi>', R, S) \<in> X \<Longrightarrow> (\<Psi>' \<otimes> \<Psi>'', R, S) \<in> X \<or> \<Psi>' \<otimes> \<Psi>'' \<rhd> R \<approx> S"
  and     "\<And>\<Psi>' R S. (\<Psi>', R, S) \<in> X \<Longrightarrow> (\<Psi>', S, R) \<in> X \<or> \<Psi>' \<rhd> S \<approx> R"

  shows "\<Psi> \<rhd> P \<approx> Q"
proof -
  have "X \<union> weakBisim = {(\<Psi>, P, Q). (\<Psi>, P, Q) \<in> X \<or> (\<Psi>, P, Q) \<in> weakBisim}" by auto
  with assms show ?thesis
    by coinduct (simp add: rtrancl_def)
qed

lemma weakBisimWeakCoinductAux[consumes 1]:
  fixes \<Psi> :: 'b
  and   P :: "('a, 'b, 'c) psi"
  and   Q :: "('a, 'b, 'c) psi"
  and   X :: "('b \<times> ('a, 'b, 'c) psi \<times> ('a, 'b, 'c) psi) set"

  assumes "(\<Psi>, P, Q) \<in> X"
  and     "\<And>\<Psi> P Q. (\<Psi>, P, Q) \<in> X \<Longrightarrow> \<Psi> \<rhd> P \<lessapprox><X> Q \<and> \<Psi> \<rhd> P \<leadsto><X> Q \<and>
                                      (\<forall>\<Psi>'. (\<Psi> \<otimes> \<Psi>', P, Q) \<in> X) \<and> (\<Psi>, Q, P) \<in> X" 

  shows "\<Psi> \<rhd> P \<approx> Q"
using assms
by(coinduct rule: weakBisimCoinductAux) (blast intro: weakSimMonotonic weakStatImpMonotonic)

lemma weakBisimWeakCoinduct[consumes 1, case_names cStatImp cSim cExt cSym]:
  fixes F :: 'b
  and   P :: "('a, 'b, 'c) psi"
  and   Q :: "('a, 'b, 'c) psi"
  and   X :: "('b \<times> ('a, 'b, 'c) psi \<times> ('a, 'b, 'c) psi) set"

  assumes "(\<Psi>, P, Q) \<in> X"
  and     "\<And>\<Psi> P Q. (\<Psi>, P, Q) \<in> X \<Longrightarrow> \<Psi> \<rhd> P \<lessapprox><X> Q"
  and     "\<And>\<Psi> P Q. (\<Psi>, P, Q) \<in> X \<Longrightarrow> \<Psi> \<rhd> P \<leadsto><X> Q"
  and     "\<And>\<Psi> P Q \<Psi>'. (\<Psi>, P, Q) \<in> X \<Longrightarrow> (\<Psi> \<otimes> \<Psi>', P, Q) \<in> X"
  and     "\<And>\<Psi> P Q. (\<Psi>, P, Q) \<in> X \<Longrightarrow> (\<Psi>, Q, P) \<in> X"

  shows "(\<Psi>, P, Q) \<in> weakBisim"
proof -
  have "X \<union> weakBisim = {(\<Psi>, P, Q). (\<Psi>, P, Q) \<in> X \<or> (\<Psi>, P, Q) \<in> weakBisim}" by auto
  with assms show ?thesis
    by(coinduct rule: weakBisimWeakCoinductAux) blast
qed

lemma weakBisimE:
  fixes P  :: "('a, 'b, 'c) psi"
  and   Q  :: "('a, 'b, 'c) psi"
  and   \<Psi>  :: 'b
  and   \<Psi>' :: 'b

  assumes "\<Psi> \<rhd> P \<approx> Q"

  shows "\<Psi> \<rhd> P \<lessapprox><weakBisim> Q"
  and   "\<Psi> \<rhd> P \<leadsto><weakBisim> Q"
  and   "\<Psi> \<otimes> \<Psi>' \<rhd>  P \<approx> Q"
  and   "\<Psi> \<rhd> Q \<approx> P"
using assms
by(auto intro: weakBisim.cases simp add: rtrancl_def)

lemma weakBisimI:
  fixes P :: "('a, 'b, 'c) psi"
  and   Q :: "('a, 'b, 'c) psi"
  and   \<Psi> :: 'b

  assumes "\<Psi> \<rhd> P \<lessapprox><weakBisim> Q"
  and     "\<Psi> \<rhd> P \<leadsto><weakBisim> Q"
  and     "\<forall>\<Psi>'. \<Psi> \<otimes> \<Psi>' \<rhd> P \<approx> Q"
  and     "\<Psi> \<rhd> Q \<approx> P"

  shows "\<Psi> \<rhd> P \<approx> Q"
using assms
by(rule_tac weakBisim.step) (auto simp add: rtrancl_def)

lemma weakBisimReflexive:
  fixes \<Psi> :: 'b
  and   P :: "('a, 'b, 'c) psi"


  shows "\<Psi> \<rhd> P \<approx> P"
proof -
  let ?X = "{(\<Psi>, P, P) | \<Psi> P. True}"
  have "(\<Psi>, P, P) \<in> ?X" by simp
  thus ?thesis
    by(coinduct rule: weakBisimWeakCoinduct, auto intro: weakSimReflexive weakStatImpReflexive)
qed

lemma weakBisimClosed:
  fixes \<Psi> :: 'b
  and   P :: "('a, 'b, 'c) psi"
  and   Q :: "('a, 'b, 'c) psi"
  and   p :: "name prm"
  
  assumes "\<Psi> \<rhd> P \<approx> Q"

  shows "(p \<bullet> \<Psi>) \<rhd>  (p \<bullet> P) \<approx> (p \<bullet> Q)"
proof -
  let ?X = "{(p \<bullet> \<Psi>, p \<bullet> P, p \<bullet> Q) | (p::name prm) \<Psi>  P Q. \<Psi> \<rhd> P \<approx> Q}"
  have "eqvt ?X"
    apply(auto simp add: eqvt_def)
    apply(rule_tac x="pa@p" in exI)
    by(auto simp add: pt2[OF pt_name_inst])
  from `\<Psi> \<rhd> P \<approx> Q` have "(p \<bullet> \<Psi>, p \<bullet> P, p \<bullet> Q) \<in> ?X" by blast
  thus ?thesis
  proof(coinduct rule: weakBisimWeakCoinduct)
    case(cStatImp \<Psi> P Q)
    {
      fix \<Psi> P Q p
      assume "\<Psi> \<rhd> P \<approx> (Q::('a, 'b, 'c) psi)"
      hence "\<Psi> \<rhd> P \<lessapprox><weakBisim> Q" by(rule weakBisimE)
      hence "\<Psi> \<rhd> P \<lessapprox><?X> Q"
        apply(rule_tac A=weakBisim in weakStatImpMonotonic, auto)
        by(rule_tac x="[]::name prm" in exI) auto
      with `eqvt ?X` have "((p::name prm) \<bullet> \<Psi>) \<rhd> (p \<bullet> P) \<lessapprox><?X> (p \<bullet> Q)"
        by(rule weakStatImpClosed)
    }
    with `(\<Psi>, P, Q) \<in> ?X` show ?case by blast
  next
    case(cSim \<Psi> P Q)
    {
      fix p :: "name prm"
      fix \<Psi> P Q
      assume "\<Psi> \<rhd> P \<leadsto><weakBisim> Q"
      hence "\<Psi> \<rhd> P \<leadsto><?X> Q"
        apply(rule_tac A=weakBisim in weakSimMonotonic, auto)
        by(rule_tac x="[]::name prm" in exI) auto
      with `eqvt ?X` have "((p::name prm) \<bullet> \<Psi>) \<rhd> (p \<bullet> P) \<leadsto><?X> (p \<bullet> Q)"
        by(rule_tac weakSimClosed)
    }
    with `(\<Psi>, P, Q) \<in> ?X` show ?case
      by(blast dest: weakBisimE)
  next
    case(cExt \<Psi> P Q \<Psi>')
    {
      fix p :: "name prm"
      fix \<Psi> P Q \<Psi>'
      assume "\<forall>\<Psi>'. (\<Psi> \<otimes> \<Psi>', P, Q) \<in> weakBisim"
      hence "((p \<bullet> \<Psi>) \<otimes> \<Psi>', p \<bullet> P, p \<bullet> Q) \<in> ?X"
        apply(auto, rule_tac x=p in exI)
        apply(rule_tac x="\<Psi> \<otimes> (rev p \<bullet> \<Psi>')" in exI)
        by(auto simp add: eqvts)
    }
    with `(\<Psi>, P, Q) \<in> ?X` show ?case
      by(blast dest: weakBisimE)
  next
    case(cSym \<Psi> P Q)
    thus ?case
      by(blast dest: weakBisimE)
  qed
qed

lemma weakBisimEqvt[simp]:
  shows "eqvt weakBisim"
using assms
by(auto simp add: eqvt_def weakBisimClosed)

lemma statEqWeakBisim:
  fixes \<Psi>  :: 'b
  and   P  :: "('a, 'b, 'c) psi"
  and   Q  :: "('a, 'b, 'c) psi"
  and   \<Psi>' :: 'b
  
  assumes "\<Psi> \<rhd> P \<approx> Q"
  and     "\<Psi> \<simeq> \<Psi>'"

  shows "\<Psi>' \<rhd> P \<approx> Q"
proof -
  let ?X = "{(\<Psi>', P, Q) | \<Psi> P Q \<Psi>'. \<Psi> \<rhd> P \<approx> Q \<and> \<Psi> \<simeq> \<Psi>'}"
  from `\<Psi> \<rhd> P \<approx> Q` `\<Psi> \<simeq> \<Psi>'` have "(\<Psi>', P, Q) \<in> ?X" by auto
  thus ?thesis
  proof(coinduct rule: weakBisimCoinduct)
    case(cStatImp \<Psi>' P Q)
    from `(\<Psi>', P, Q) \<in> ?X` obtain \<Psi> where "\<Psi> \<rhd> P \<approx> Q" and "\<Psi> \<simeq> \<Psi>'"
      by auto
    from `\<Psi> \<rhd> P \<approx> Q` have "\<Psi> \<rhd> P \<lessapprox><weakBisim> Q" by(rule weakBisimE)
    moreover note `\<Psi> \<simeq> \<Psi>'`
    moreover have "\<And>\<Psi> P Q \<Psi>'. \<lbrakk>\<Psi> \<rhd> P \<approx> Q; \<Psi> \<simeq> \<Psi>'\<rbrakk> \<Longrightarrow> (\<Psi>', P, Q) \<in> ?X \<union> weakBisim"
      by auto
    ultimately show ?case by(rule weakStatImpStatEq)
  next
    case(cSim \<Psi>' P Q)
    from `(\<Psi>', P, Q) \<in> ?X` obtain \<Psi> where "\<Psi> \<rhd> P \<approx> Q" and "\<Psi> \<simeq> \<Psi>'"
      by auto
    from `\<Psi> \<rhd> P \<approx> Q` have "\<Psi> \<rhd> P \<leadsto><weakBisim> Q" by(blast dest: weakBisimE)
    moreover have "eqvt ?X"
      by(auto simp add: eqvt_def) (metis weakBisimClosed AssertionStatEqClosed)
    hence "eqvt(?X \<union> weakBisim)" by auto
    moreover note `\<Psi> \<simeq> \<Psi>'`
    moreover have "\<And>\<Psi> P Q \<Psi>'. \<lbrakk>\<Psi> \<rhd> P \<approx> Q; \<Psi> \<simeq> \<Psi>'\<rbrakk> \<Longrightarrow> (\<Psi>', P, Q) \<in> ?X \<union> weakBisim"
      by auto
    ultimately show ?case by(rule weakSimStatEq)
  next
    case(cExt \<Psi>' P Q \<Psi>'')
    from `(\<Psi>', P, Q) \<in> ?X` obtain \<Psi> where "\<Psi> \<rhd> P \<approx> Q" and "\<Psi> \<simeq> \<Psi>'"
      by auto
    from `\<Psi> \<rhd> P \<approx> Q` have "\<Psi> \<otimes> \<Psi>'' \<rhd> P \<approx> Q" by(rule weakBisimE)
    moreover from `\<Psi> \<simeq> \<Psi>'` have "\<Psi> \<otimes> \<Psi>'' \<simeq> \<Psi>' \<otimes> \<Psi>''" by(rule Composition)
    ultimately show ?case by blast
  next
    case(cSym \<Psi>' P Q)
    from `(\<Psi>', P, Q) \<in> ?X` obtain \<Psi> where "\<Psi> \<rhd> P \<approx> Q" and "\<Psi> \<simeq> \<Psi>'"
      by auto
    from `\<Psi> \<rhd> P \<approx> Q` have "\<Psi> \<rhd> Q \<approx> P" by(rule weakBisimE)
    thus ?case using `\<Psi> \<simeq> \<Psi>'` by auto
  qed
qed

lemma weakBisimTransitive:
  fixes \<Psi> :: 'b
  and   P :: "('a, 'b, 'c) psi"
  and   Q :: "('a, 'b, 'c) psi"
  and   R :: "('a, 'b, 'c) psi"

  assumes PQ: "\<Psi> \<rhd> P \<approx> Q"
  and     QR: "\<Psi> \<rhd> Q \<approx> R"

  shows "\<Psi> \<rhd> P \<approx> R"
proof -
  let ?X = "{(\<Psi>, P, R) | \<Psi> P R. \<exists>Q. \<Psi> \<rhd> P \<approx> Q \<and> \<Psi> \<rhd> Q \<approx> R}" 
  from PQ QR have "(\<Psi>, P, R) \<in> ?X" by auto
  thus ?thesis
  proof(coinduct rule: weakBisimCoinduct)
    case(cStatImp \<Psi> P R)
    from `(\<Psi>, P, R) \<in> ?X` obtain Q where "\<Psi> \<rhd> P \<approx> Q" and  "\<Psi> \<rhd> Q \<approx> R" by blast
    from `\<Psi> \<rhd> P \<approx> Q` have "\<Psi> \<rhd> P \<lessapprox><weakBisim> Q" by(rule weakBisimE)
    moreover note `\<Psi> \<rhd> Q \<approx> R`
    moreover have "?X \<subseteq> ?X \<union> weakBisim" by auto
    moreover note weakBisimE(1)
    moreover from weakBisimE(2) have "\<And>\<Psi> P Q P'. \<lbrakk>\<Psi> \<rhd> P \<approx> Q; \<Psi> \<rhd> P \<Longrightarrow>\<^sup>^\<^sub>\<tau> P'\<rbrakk> \<Longrightarrow> \<exists>Q'. \<Psi> \<rhd> Q \<Longrightarrow>\<^sup>^\<^sub>\<tau> Q' \<and> \<Psi> \<rhd> P' \<approx> Q'"
      by(metis weakBisimE(4) weakSimTauChain)
    ultimately show ?case by(rule weakStatImpTransitive)
  next
    case(cSim \<Psi> P R)
    {
      fix \<Psi> P Q R
      assume "\<Psi> \<rhd> P \<approx> Q" and "\<Psi> \<rhd> Q \<leadsto><weakBisim> R"
      moreover have "eqvt ?X"
        by(force simp add: eqvt_def dest: weakBisimClosed)
      with weakBisimEqvt have "eqvt (?X \<union> weakBisim)" by blast
      moreover have "?X \<subseteq> ?X \<union> weakBisim" by auto
      moreover note weakBisimE(2)
      ultimately have "\<Psi> \<rhd> P \<leadsto><(?X \<union> weakBisim)> R"
        by(rule_tac weakSimTransitive) auto
    }
    with `(\<Psi>, P, R) \<in> ?X` show ?case
      by(blast dest: weakBisimE)
  next
    case(cExt \<Psi> P R \<Psi>')
    thus ?case by(blast dest: weakBisimE)
  next
    case(cSym \<Psi> P R)
    thus ?case by(blast dest: weakBisimE)
  qed
qed

lemma strongBisimWeakBisim:
  fixes \<Psi> :: 'b
  and   P :: "('a, 'b, 'c) psi"
  and   Q :: "('a, 'b, 'c) psi"

  assumes "\<Psi> \<rhd> P \<sim> Q"

  shows "\<Psi> \<rhd> P \<approx> Q"
proof -
  from `\<Psi> \<rhd> P \<sim> Q`
  show ?thesis
  proof(coinduct rule: weakBisimWeakCoinduct)
    case(cStatImp \<Psi> P Q)
    from `\<Psi> \<rhd> P \<sim> Q` have "insertAssertion(extractFrame P) \<Psi> \<hookrightarrow>\<^sub>F insertAssertion(extractFrame Q) \<Psi>"
      by(metis bisimE FrameStatEq_def)
    moreover from `\<Psi> \<rhd> P \<sim> Q` have "\<And>\<Psi>'. \<Psi> \<otimes> \<Psi>' \<rhd> P \<sim> Q" by(rule bisimE)
    ultimately show ?case by(rule statImpWeakStatImp)
  next
    case(cSim \<Psi> P Q)
    note `\<Psi> \<rhd> P \<sim> Q`
    moreover have "\<And>\<Psi> P Q. \<Psi> \<rhd> P \<sim> Q \<Longrightarrow> insertAssertion(extractFrame Q) \<Psi> \<hookrightarrow>\<^sub>F insertAssertion(extractFrame P) \<Psi>"
      by(drule_tac bisimE) (simp add: FrameStatEq_def)
    ultimately show ?case using bisimE(2) bisimE(3)
      by(rule strongSimWeakSim)
  next
    case(cExt \<Psi> P Q \<Psi>')
    from `\<Psi> \<rhd> P \<sim> Q` show ?case
      by(rule bisimE)
  next
    case(cSym \<Psi> P Q)
    from `\<Psi> \<rhd> P \<sim> Q` show ?case
      by(rule bisimE)
  qed
qed

lemma structCongWeakBisim:
  fixes \<Psi> :: 'b
  and   P :: "('a, 'b, 'c) psi"
  and   Q :: "('a, 'b, 'c) psi"

  assumes "P \<equiv>\<^sub>s Q"

  shows "P \<approx> Q"
using assms
by(metis structCongBisim strongBisimWeakBisim)

lemma simTauChain:
  fixes \<Psi> :: 'b
  and   P  :: "('a, 'b, 'c) psi"
  and   Q  :: "('a, 'b, 'c) psi"
  and   Q' :: "('a, 'b, 'c) psi"

  assumes "(\<Psi>, P, Q) \<in> Rel"
  and     "\<Psi> \<rhd> Q \<Longrightarrow>\<^sup>^\<^sub>\<tau> Q'"
  and     Sim: "\<And>\<Psi> P Q. (\<Psi>, P, Q) \<in> Rel \<Longrightarrow> \<Psi> \<rhd> P \<leadsto>[Rel] Q"
  
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
    from `(\<Psi>, P', Q') \<in> Rel` have "\<Psi> \<rhd> P' \<leadsto>[Rel] Q'" by(rule Sim)
    then obtain P'' where P'Chain: "\<Psi> \<rhd> P' \<longmapsto>\<tau> \<prec> P''" and "(\<Psi>, P'', Q'') \<in> Rel"
      using `\<Psi> \<rhd> Q' \<longmapsto>\<tau> \<prec> Q''` by(drule_tac simE) auto
    from PChain P'Chain have "\<Psi> \<rhd> P \<Longrightarrow>\<^sup>^\<^sub>\<tau> P''" by(auto dest: tauActTauChain)
    thus ?case using `(\<Psi>, P'', Q'') \<in> Rel` by(rule TauStep)
  qed
qed

lemma quietBisimNil:
  fixes \<Psi> :: 'b
  and   P :: "('a, 'b, 'c) psi"

  assumes "quiet P"

  shows "\<Psi> \<rhd> P \<approx> \<zero>"
proof -
  let ?X = "{(\<Psi>, \<zero>, P) | \<Psi> P. quiet P} \<union> {(\<Psi>, P, \<zero>) | \<Psi> P. quiet P}"

  from `quiet P` have "(\<Psi>, P, \<zero>) \<in> ?X" by auto
  thus ?thesis
  proof(coinduct rule: weakBisimWeakCoinduct)
    case(cStatImp \<Psi> P Q)
    thus ?case
      apply(simp add: weakStatImp_def)
      apply(rule allI)
      apply(rule_tac x=Q in exI)
      apply auto
      apply(drule_tac \<Psi>=\<Psi> in quietFrame)
      apply(rule_tac G="\<langle>\<epsilon>, \<Psi>\<rangle>" in FrameStatImpTrans)
      using Identity
      apply(simp add: AssertionStatEq_def)
      apply(simp add: FrameStatEq_def)
      apply(drule_tac \<Psi>=\<Psi> in quietFrame)
      apply(rule_tac G="\<langle>\<epsilon>, \<Psi>\<rangle>" in FrameStatImpTrans)
      apply auto
      defer
      using Identity
      apply(simp add: AssertionStatEq_def)
      apply(simp add: FrameStatEq_def)
      done
  next
    case(cSim \<Psi> P Q)
    moreover have "eqvt ?X" by(auto simp add: eqvt_def intro: quietEqvt)
    ultimately show ?case
      apply auto
      apply(rule quietSim)
      apply auto
      apply(auto simp add: weakSimulation_def)
      done
  next
    case(cExt \<Psi> P Q \<Psi>')
    thus ?case by blast
  next
    case(cSym \<Psi> P Q)
    thus ?case by blast
  qed
qed

lemma weakTransitiveWeakCoinduct[case_names cStatImp cSim cExt cSym, case_conclusion bisim step, consumes 2]:
  fixes \<Psi> :: 'b
  and   P :: "('a, 'b, 'c) psi"
  and   Q :: "('a, 'b, 'c) psi"
  and   X :: "('b \<times> ('a, 'b, 'c) psi \<times> ('a, 'b, 'c) psi) set"

  assumes p: "(\<Psi>, P, Q) \<in> X"
  and Eqvt: "eqvt X"
  and rStatImp: "\<And>\<Psi> P Q. (\<Psi>, P, Q) \<in> X \<Longrightarrow> \<Psi> \<rhd> P \<lessapprox><X> Q"
  and rSim: "\<And>\<Psi> P Q. (\<Psi>, P, Q) \<in> X \<Longrightarrow> \<Psi> \<rhd> P \<leadsto><({(\<Psi>, P, Q) | \<Psi> P Q. \<exists>P' Q'. \<Psi> \<rhd> P \<sim> P' \<and>
                                                                        (\<Psi>, P', Q') \<in> X \<and>
                                                                        \<Psi> \<rhd> Q' \<sim> Q})> Q"
  and rExt: "\<And>\<Psi> P Q \<Psi>'. (\<Psi>, P, Q) \<in> X \<Longrightarrow> (\<Psi> \<otimes> \<Psi>', P, Q) \<in> X"
  and rSym: "\<And>\<Psi> P Q. (\<Psi>, P, Q) \<in> X \<Longrightarrow> (\<Psi>, Q, P) \<in> X"

  shows "\<Psi> \<rhd> P \<approx> Q"
proof -
  let ?X = "{(\<Psi>, P, Q) | \<Psi> P Q. \<exists>P' Q'. \<Psi> \<rhd> P \<sim> P' \<and> (\<Psi>, P', Q') \<in> X \<and> \<Psi> \<rhd> Q' \<sim> Q}"
  from p have "(\<Psi>, P, Q) \<in> ?X"
    by(blast intro: bisimReflexive)
  thus ?thesis
  proof(coinduct rule: weakBisimWeakCoinduct)
    case(cStatImp \<Psi> P Q)
    {
      fix \<Psi>'
      from `(\<Psi> , P, Q) \<in> ?X` obtain P' Q' where "\<Psi> \<rhd> P \<sim> P'" and "(\<Psi>, P', Q') \<in> X" and "\<Psi> \<rhd> Q' \<sim> Q" by auto
      from `(\<Psi>, P', Q') \<in> X` obtain Q'' Q''' where Q'Chain: "\<Psi> \<rhd> Q' \<Longrightarrow>\<^sup>^\<^sub>\<tau> Q''"
                                               and PImpQ: "insertAssertion (extractFrame P') \<Psi> \<hookrightarrow>\<^sub>F insertAssertion (extractFrame Q'') \<Psi>"
                                               and Q''Chain: "\<Psi> \<otimes> \<Psi>' \<rhd> Q'' \<Longrightarrow>\<^sup>^\<^sub>\<tau> Q'''" and "(\<Psi> \<otimes> \<Psi>', P', Q''') \<in> X"
        apply(drule_tac rStatImp) by(auto simp add: weakStatImp_def) blast
      from `\<Psi> \<rhd> Q' \<sim> Q` have "\<Psi> \<rhd> Q \<sim> Q'" by(rule bisimE)
      then obtain Q'''' where "\<Psi> \<rhd> Q \<Longrightarrow>\<^sup>^\<^sub>\<tau> Q''''" and "\<Psi> \<rhd> Q'''' \<sim> Q''" using  `\<Psi> \<rhd> Q' \<Longrightarrow>\<^sup>^\<^sub>\<tau> Q''` bisimE(2)
        by(rule simTauChain)
      note `\<Psi> \<rhd> Q \<Longrightarrow>\<^sup>^\<^sub>\<tau> Q''''`
      moreover have "insertAssertion (extractFrame P) \<Psi> \<hookrightarrow>\<^sub>F insertAssertion (extractFrame Q'''') \<Psi>"
      proof -
        from `\<Psi> \<rhd> P \<sim> P'` have "insertAssertion (extractFrame P) \<Psi> \<hookrightarrow>\<^sub>F insertAssertion (extractFrame P') \<Psi>"
          by(drule_tac bisimE) (simp add: FrameStatEq_def)
        moreover from `\<Psi> \<rhd> Q'''' \<sim> Q''` have "insertAssertion (extractFrame Q'') \<Psi> \<hookrightarrow>\<^sub>F insertAssertion (extractFrame Q'''') \<Psi>"
          by(drule_tac bisimE) (simp add: FrameStatEq_def)
        ultimately show ?thesis using PImpQ by(blast intro: FrameStatImpTrans)
      qed
      moreover from `\<Psi> \<rhd> Q'''' \<sim> Q''` have "\<Psi> \<otimes> \<Psi>' \<rhd> Q'''' \<sim> Q''" by(metis bisimE)
      then obtain Q''''' where Q''''Chain: "\<Psi> \<otimes> \<Psi>' \<rhd> Q'''' \<Longrightarrow>\<^sup>^\<^sub>\<tau> Q'''''" and "\<Psi> \<otimes> \<Psi>' \<rhd> Q''''' \<sim> Q'''" using Q''Chain bisimE(2)
        by(rule simTauChain)
      moreover from `\<Psi> \<rhd> P \<sim> P'` `(\<Psi> \<otimes> \<Psi>' , P', Q''') \<in> X` `\<Psi> \<otimes> \<Psi>' \<rhd> Q''''' \<sim> Q'''` have "(\<Psi> \<otimes> \<Psi>', P, Q''''') \<in> ?X" by(auto dest: bisimE)
      ultimately have "\<exists>Q' Q''. \<Psi> \<rhd> Q \<Longrightarrow>\<^sup>^\<^sub>\<tau> Q'' \<and> insertAssertion (extractFrame P) \<Psi> \<hookrightarrow>\<^sub>F insertAssertion (extractFrame Q'') \<Psi> \<and> \<Psi> \<otimes> \<Psi>' \<rhd> Q'' \<Longrightarrow>\<^sup>^\<^sub>\<tau> Q' \<and> (\<Psi> \<otimes> \<Psi>', P, Q') \<in> ?X" by blast
    }
    with `(\<Psi>, P, Q) \<in> ?X` show ?case by(simp add: weakStatImp_def) blast
  next
    case(cSim \<Psi> P Q)
    from `(\<Psi>, P, Q) \<in> ?X` obtain P' Q' where "\<Psi> \<rhd> P \<sim> P'" and "(\<Psi>, P', Q') \<in> X" and "\<Psi> \<rhd> Q' \<sim> Q" by auto
    from `(\<Psi>, P', Q') \<in> X` have "\<Psi> \<rhd> P' \<leadsto><?X> Q'" 
      by(rule rSim)
    moreover from `\<Psi> \<rhd> Q' \<sim> Q` have "\<Psi> \<rhd> Q' \<leadsto>[bisim] Q" by(rule bisimE)
    moreover from `eqvt X` have "eqvt ?X"
      apply(auto simp add: eqvt_def)
      apply(drule_tac p=p in bisimClosed)
      apply(drule_tac p=p in bisimClosed)
      apply(rule_tac x="p \<bullet> P'" in exI, simp)
      by(rule_tac x="p \<bullet> Q'" in exI, auto)
    moreover from `\<Psi> \<rhd> Q' \<sim> Q` have "insertAssertion (extractFrame Q) \<Psi> \<hookrightarrow>\<^sub>F insertAssertion (extractFrame Q') \<Psi>"
      by(drule_tac bisimE) (simp add: FrameStatEq_def)
    moreover have "{(\<Psi>, P, R) | \<Psi> P R. \<exists>Q. (\<Psi>, P, Q) \<in> ?X \<and> \<Psi> \<rhd> Q \<sim> R} \<subseteq> ?X"
      by(blast intro: bisimTransitive)
    moreover note bisimE(3)
    ultimately have "\<Psi> \<rhd> P' \<leadsto><?X> Q" by(rule strongAppend) 
    moreover have "{(\<Psi>, P, R) | \<Psi> P R. \<exists>Q. \<Psi> \<rhd> P \<sim> Q \<and> (\<Psi>, Q, R) \<in> ?X} \<subseteq> ?X"
      by(blast intro: bisimTransitive)
    moreover {
      fix \<Psi> P Q

      assume "\<Psi> \<rhd> P \<sim> Q"
      moreover have "\<And>\<Psi> P Q. \<Psi> \<rhd> P \<sim> Q \<Longrightarrow> insertAssertion (extractFrame Q) \<Psi> \<hookrightarrow>\<^sub>F insertAssertion (extractFrame P) \<Psi>"
        by(drule_tac bisimE) (simp add: FrameStatEq_def)
      ultimately have "\<Psi> \<rhd> P \<leadsto><bisim> Q" using bisimE(2) bisimE(3)
        by(rule strongSimWeakSim)
    }
    ultimately show ?case using `\<Psi> \<rhd> P \<sim> P'` `eqvt ?X`
      by(rule_tac weakSimTransitive)
  next
    case(cExt \<Psi> P Q \<Psi>')
    thus ?case by(blast dest: bisimE intro: rExt)
  next
    case(cSym \<Psi> P Q)
    thus ?case by(blast dest: bisimE intro: rSym)
  qed
qed

lemma weakTransitiveCoinduct[case_names cStatImp cSim cExt cSym, case_conclusion bisim step, consumes 2]:
  fixes \<Psi> :: 'b
  and   P :: "('a, 'b, 'c) psi"
  and   Q :: "('a, 'b, 'c) psi"
  and   X :: "('b \<times> ('a, 'b, 'c) psi \<times> ('a, 'b, 'c) psi) set"

  assumes p: "(\<Psi>, P, Q) \<in> X"
  and Eqvt: "eqvt X"
  and rStatImp: "\<And>\<Psi> P Q. (\<Psi>, P, Q) \<in> X \<Longrightarrow> \<Psi> \<rhd> P \<lessapprox><(X \<union> weakBisim)> Q"
  and rSim: "\<And>\<Psi> P Q. (\<Psi>, P, Q) \<in> X \<Longrightarrow> \<Psi> \<rhd> P \<leadsto><({(\<Psi>, P, Q) | \<Psi> P Q. \<exists>P' Q'. \<Psi> \<rhd> P \<sim> P' \<and>
                                                                        (\<Psi>, P', Q') \<in> (X \<union> weakBisim) \<and>
                                                                        \<Psi> \<rhd> Q' \<sim> Q})> Q"
  and rExt: "\<And>\<Psi> P Q \<Psi>'. (\<Psi>, P, Q) \<in> X \<Longrightarrow> (\<Psi> \<otimes> \<Psi>', P, Q) \<in> X \<union> weakBisim"
  and rSym: "\<And>\<Psi> P Q. (\<Psi>, P, Q) \<in> X \<Longrightarrow> (\<Psi>, Q, P) \<in> X \<union> weakBisim"

  shows "\<Psi> \<rhd> P \<approx> Q"
proof -
  from p have "(\<Psi>, P, Q) \<in> X \<union> weakBisim" by auto
  moreover from `eqvt X` have "eqvt(X \<union> weakBisim)" by auto
  ultimately show ?thesis
  proof(coinduct rule: weakTransitiveWeakCoinduct)
    case(cStatImp \<Psi> P Q)
    thus ?case by(blast dest: rStatImp weakBisimE(1) weakStatImpMonotonic)
  next
    case(cSim \<Psi> P Q)
    thus ?case by(fastforce intro: rSim weakBisimE(2) weakSimMonotonic bisimReflexive)
  next
    case(cExt \<Psi> P Q \<Psi>')
    thus ?case by(blast dest: weakBisimE rExt) 
  next
    case(cSym \<Psi> P Q)
    thus ?case by(blast dest: weakBisimE rSym)
  qed
qed

lemma weakTransitiveCoinduct2[case_names cStatImp cSim cExt cSym, case_conclusion bisim step, consumes 2]:
  fixes \<Psi> :: 'b
  and   P :: "('a, 'b, 'c) psi"
  and   Q :: "('a, 'b, 'c) psi"
  and   X :: "('b \<times> ('a, 'b, 'c) psi \<times> ('a, 'b, 'c) psi) set"

  assumes p: "(\<Psi>, P, Q) \<in> X"
  and Eqvt: "eqvt X"
  and rStatImp: "\<And>\<Psi> P Q. (\<Psi>, P, Q) \<in> X \<Longrightarrow> \<Psi> \<rhd> P \<lessapprox><X> Q"
  and rSim: "\<And>\<Psi> P Q. (\<Psi>, P, Q) \<in> X \<Longrightarrow> \<Psi> \<rhd> P \<leadsto><({(\<Psi>, P, Q) | \<Psi> P Q. \<exists>P' Q'. \<Psi> \<rhd> P \<approx> P' \<and> (\<Psi>, P', Q') \<in> X \<and> \<Psi> \<rhd> Q' \<sim> Q})> Q"
  and rExt: "\<And>\<Psi> P Q \<Psi>'. (\<Psi>, P, Q) \<in> X \<Longrightarrow> (\<Psi> \<otimes> \<Psi>', P, Q) \<in> X"
  and rSym: "\<And>\<Psi> P Q. (\<Psi>, P, Q) \<in> X \<Longrightarrow> (\<Psi>, Q, P) \<in> X"

  shows "\<Psi> \<rhd> P \<approx> Q"
proof -
  let ?X = "{(\<Psi>, P, Q) | \<Psi> P Q. \<exists>P' Q'. \<Psi> \<rhd> P \<approx> P' \<and> (\<Psi>, P', Q') \<in> X \<and> \<Psi> \<rhd> Q' \<sim> Q}"
  let ?Y = "{(\<Psi>, P, Q) | \<Psi> P Q. \<exists>P' Q'. \<Psi> \<rhd> P \<approx> P' \<and> (\<Psi>, P', Q') \<in> X \<and> \<Psi> \<rhd> Q' \<approx> Q}"

  from `eqvt X` have "eqvt ?X"
    apply(auto simp add: eqvt_def)
    apply(drule_tac p=p in bisimClosed)
    apply(drule_tac p=p in weakBisimClosed)
    apply(rule_tac x="p \<bullet> P'" in exI, simp)
    by(rule_tac x="p \<bullet> Q'" in exI, auto)
  from `eqvt X` have "eqvt ?Y"
    apply(auto simp add: eqvt_def)
    apply(drule_tac p=p in weakBisimClosed)
    apply(drule_tac p=p in weakBisimClosed)
    apply(rule_tac x="p \<bullet> P'" in exI, simp)
    by(rule_tac x="p \<bullet> Q'" in exI, auto)

  {
    fix \<Psi> P Q
    assume "(\<Psi>, P, Q) \<in> ?X"
    then obtain P' Q' where "\<Psi> \<rhd> P \<approx> P'" and "(\<Psi>, P', Q') \<in> X" and "\<Psi> \<rhd> Q' \<sim> Q"
      by auto
    note `\<Psi> \<rhd> P \<approx> P'`
    moreover from `(\<Psi>, P', Q') \<in> X` have "\<Psi> \<rhd> P' \<leadsto><?X> Q'" by(rule rSim)
    moreover note `eqvt ?X`
    moreover have "{(\<Psi>, P, R) | \<Psi> P R. \<exists>Q. \<Psi> \<rhd> P \<approx> Q \<and> (\<Psi>, Q, R) \<in> ?X} \<subseteq> ?X"
      by(blast intro: weakBisimTransitive)
    ultimately have "\<Psi> \<rhd> P \<leadsto><?X> Q'" using weakBisimE(2) by(rule weakSimTransitive)
    moreover from `\<Psi> \<rhd> Q' \<sim> Q` have "\<Psi> \<rhd> Q' \<leadsto>[bisim] Q" by(rule bisimE)
    moreover note `eqvt ?X`
    moreover from `\<Psi> \<rhd> Q' \<sim> Q` have "insertAssertion (extractFrame Q) \<Psi> \<hookrightarrow>\<^sub>F insertAssertion (extractFrame Q') \<Psi>"
      by(drule_tac bisimE) (simp add: FrameStatEq_def)
    moreover have "{(\<Psi>, P, R) | \<Psi> P R. \<exists>Q. (\<Psi>, P, Q) \<in> ?X \<and> \<Psi> \<rhd> Q \<sim> R} \<subseteq> ?X"
      by(blast dest: bisimTransitive)
    moreover note bisimE(3)
    ultimately have "\<Psi> \<rhd> P \<leadsto><?X> Q" by(rule_tac strongAppend) 
  }
  note Goal = this

  from p have "(\<Psi>, P, Q) \<in> ?Y" by(blast intro: weakBisimReflexive bisimReflexive rSym)
  thus ?thesis
  proof(coinduct rule: weakBisimWeakCoinduct)
  next
    case(cStatImp \<Psi> P Q)
    {
      fix \<Psi>'

      from `(\<Psi>, P, Q) \<in> ?Y` obtain R S where "\<Psi> \<rhd> P \<approx> R" and "(\<Psi>, R, S) \<in> X" and "\<Psi> \<rhd> S \<approx> Q" by auto
      from `\<Psi> \<rhd> P \<approx> R` obtain R'' R' 
        where RChain: "\<Psi> \<rhd> R \<Longrightarrow>\<^sup>^\<^sub>\<tau> R''" 
          and PImpR'': "insertAssertion (extractFrame P) \<Psi> \<hookrightarrow>\<^sub>F insertAssertion (extractFrame R'') \<Psi>"
          and R''Chain: "\<Psi> \<otimes> \<Psi>' \<rhd> R'' \<Longrightarrow>\<^sup>^\<^sub>\<tau> R'" 
          and "\<Psi> \<otimes> \<Psi>' \<rhd> P \<approx> R'"
        apply(drule_tac weakBisimE) by(simp add: weakStatImp_def) blast

      from `(\<Psi>, R, S) \<in> X` have "(\<Psi>, S, R) \<in> ?X" by(blast intro: weakBisimReflexive bisimReflexive rSym)
      with RChain obtain S'' where SChain: "\<Psi> \<rhd> S \<Longrightarrow>\<^sup>^\<^sub>\<tau> S''" and "(\<Psi>, S'', R'') \<in> ?X" using Goal
        by(rule weakSimTauChain)

      from `(\<Psi>, S'', R'') \<in> ?X` obtain T U where "\<Psi> \<rhd> S'' \<approx> T" and "(\<Psi>, T, U) \<in> X" and "\<Psi> \<rhd> U \<sim> R''"
        by auto
      from `\<Psi> \<rhd> U \<sim> R''` have R''ImpU: "insertAssertion (extractFrame R'') \<Psi> \<hookrightarrow>\<^sub>F insertAssertion (extractFrame U) \<Psi>"
        by(drule_tac bisimE) (simp add: FrameStatEq_def)
      
      from `(\<Psi>, T, U) \<in> X` weakStatImp_def
      obtain T'' T' where TChain: "\<Psi> \<rhd> T \<Longrightarrow>\<^sup>^\<^sub>\<tau> T''"
                      and UImpT'': "insertAssertion (extractFrame U) \<Psi> \<hookrightarrow>\<^sub>F insertAssertion (extractFrame T'') \<Psi>"
                      and T''Chain: "\<Psi> \<otimes> \<Psi>' \<rhd> T'' \<Longrightarrow>\<^sup>^\<^sub>\<tau> T'" 
                      and "(\<Psi> \<otimes> \<Psi>', U, T') \<in> X"
        by(blast dest: rStatImp rSym)

      from TChain `\<Psi> \<rhd> S'' \<approx> T` weakBisimE(2) obtain S''' where S''Chain: "\<Psi> \<rhd> S'' \<Longrightarrow>\<^sup>^\<^sub>\<tau> S'''" and "\<Psi> \<rhd> S''' \<approx> T''"
        by(rule weakSimTauChain)

      from `\<Psi> \<rhd> S''' \<approx> T''` weakStatImp_def
      obtain S''''' S'''' where S'''Chain: "\<Psi> \<rhd> S''' \<Longrightarrow>\<^sup>^\<^sub>\<tau> S'''''"
                            and T''ImpS''''': "insertAssertion (extractFrame T'') \<Psi> \<hookrightarrow>\<^sub>F insertAssertion (extractFrame S''''') \<Psi>"
                            and S'''''Chain: "\<Psi> \<otimes> \<Psi>' \<rhd> S''''' \<Longrightarrow>\<^sup>^\<^sub>\<tau> S''''" 
                            and "\<Psi> \<otimes> \<Psi>' \<rhd> T'' \<approx> S''''"
        by(metis weakBisimE)
      
      from SChain S''Chain S'''Chain have "\<Psi> \<rhd> S \<Longrightarrow>\<^sup>^\<^sub>\<tau> S'''''" by auto
      moreover from `\<Psi> \<rhd> S \<approx> Q` have "\<Psi> \<rhd> Q \<approx> S" by(rule weakBisimE)
      ultimately obtain Q''' where QChain: "\<Psi> \<rhd> Q \<Longrightarrow>\<^sup>^\<^sub>\<tau> Q'''" and "\<Psi> \<rhd> Q''' \<approx> S'''''" using weakBisimE(2)
        by(rule weakSimTauChain)
      from `\<Psi> \<rhd> Q''' \<approx> S'''''` have "\<Psi> \<rhd> S''''' \<approx> Q'''" by(rule weakBisimE)
      then obtain Q'' Q' where Q'''Chain: "\<Psi> \<rhd> Q''' \<Longrightarrow>\<^sup>^\<^sub>\<tau> Q''"
                           and S'''''ImpQ'': "insertAssertion (extractFrame S''''') \<Psi> \<hookrightarrow>\<^sub>F insertAssertion (extractFrame Q'') \<Psi>"
                           and Q''Chain: "\<Psi> \<otimes> \<Psi>' \<rhd> Q'' \<Longrightarrow>\<^sup>^\<^sub>\<tau> Q'" 
                           and "\<Psi> \<otimes> \<Psi>' \<rhd> S''''' \<approx> Q'" using weakStatImp_def
        by(metis weakBisimE)

      from QChain Q'''Chain have "\<Psi> \<rhd> Q \<Longrightarrow>\<^sup>^\<^sub>\<tau> Q''" by auto
      moreover from PImpR'' R''ImpU UImpT'' T''ImpS''''' S'''''ImpQ''
      have "insertAssertion (extractFrame P) \<Psi> \<hookrightarrow>\<^sub>F insertAssertion (extractFrame Q'') \<Psi>"
        by(blast dest: FrameStatImpTrans)

      moreover from `\<Psi> \<rhd> U \<sim> R''` have "\<Psi> \<otimes> \<Psi>' \<rhd> U \<approx> R''" by(metis weakBisimE strongBisimWeakBisim)
      with R''Chain obtain U' where UChain: "\<Psi> \<otimes> \<Psi>' \<rhd> U \<Longrightarrow>\<^sup>^\<^sub>\<tau> U'" and "\<Psi> \<otimes> \<Psi>' \<rhd> U' \<approx> R'" using weakBisimE(2)
        by(rule weakSimTauChain)
      from `\<Psi> \<otimes> \<Psi>' \<rhd> U' \<approx> R'` have "\<Psi> \<otimes> \<Psi>' \<rhd> R' \<approx> U'" by(rule weakBisimE)
      from `(\<Psi> \<otimes> \<Psi>', U, T') \<in> X` have "(\<Psi> \<otimes> \<Psi>', T', U) \<in> ?X" by(blast intro: rSym weakBisimReflexive bisimReflexive)
      with UChain obtain T''' where T'Chain: "\<Psi> \<otimes> \<Psi>' \<rhd> T' \<Longrightarrow>\<^sup>^\<^sub>\<tau> T'''" and "(\<Psi> \<otimes> \<Psi>', T''', U') \<in> ?X" using Goal
        by(rule weakSimTauChain)
      from `(\<Psi> \<otimes> \<Psi>', T''', U') \<in> ?X` have "(\<Psi> \<otimes> \<Psi>', U', T''') \<in> ?Y" 
        by(blast dest: weakBisimE rSym strongBisimWeakBisim)
      from T''Chain T'Chain have "\<Psi> \<otimes> \<Psi>' \<rhd> T'' \<Longrightarrow>\<^sup>^\<^sub>\<tau> T'''" by auto
      then obtain S'''''' where S''''Chain: "\<Psi> \<otimes> \<Psi>' \<rhd> S'''' \<Longrightarrow>\<^sup>^\<^sub>\<tau> S''''''" and "\<Psi> \<otimes> \<Psi>' \<rhd> T''' \<approx> S''''''" 
        using  `\<Psi> \<otimes> \<Psi>' \<rhd> T'' \<approx> S''''` weakBisimE(2)
        apply(drule_tac weakBisimE(4))
        by(rule weakSimTauChain) (auto dest: weakBisimE(4))
      from S'''''Chain S''''Chain have "\<Psi> \<otimes> \<Psi>' \<rhd> S''''' \<Longrightarrow>\<^sup>^\<^sub>\<tau> S''''''" by auto

      with `\<Psi> \<otimes> \<Psi>' \<rhd> S''''' \<approx> Q'`
      obtain Q'''' where Q'Chain: "\<Psi> \<otimes> \<Psi>' \<rhd> Q' \<Longrightarrow>\<^sup>^\<^sub>\<tau> Q''''" and "\<Psi> \<otimes> \<Psi>' \<rhd> S'''''' \<approx> Q''''" using weakBisimE(2)
        apply(drule_tac weakBisimE(4))
        by(rule weakSimTauChain) (auto dest: weakBisimE(4))

      from Q''Chain Q'Chain have "\<Psi> \<otimes> \<Psi>' \<rhd> Q'' \<Longrightarrow>\<^sup>^\<^sub>\<tau> Q''''" by auto
      moreover from `\<Psi> \<otimes> \<Psi>' \<rhd> P \<approx> R'` `\<Psi> \<otimes> \<Psi>' \<rhd> R' \<approx> U'` `(\<Psi> \<otimes> \<Psi>', U', T''') \<in> ?Y` `\<Psi> \<otimes> \<Psi>' \<rhd> T''' \<approx> S''''''`
                    `\<Psi> \<otimes> \<Psi>' \<rhd> S'''''' \<approx> Q''''`
      have "(\<Psi> \<otimes> \<Psi>', P, Q'''') \<in> ?Y"
        by auto (blast dest: weakBisimTransitive)
      ultimately have "\<exists>Q'' Q'. \<Psi> \<rhd> Q \<Longrightarrow>\<^sup>^\<^sub>\<tau> Q'' \<and> insertAssertion (extractFrame P) \<Psi> \<hookrightarrow>\<^sub>F insertAssertion (extractFrame Q'') \<Psi> \<and> \<Psi> \<otimes> \<Psi>' \<rhd> Q'' \<Longrightarrow>\<^sup>^\<^sub>\<tau> Q' \<and> (\<Psi> \<otimes> \<Psi>', P, Q') \<in> ?Y"
        by blast
    }
    thus ?case by(simp add: weakStatImp_def)
  next
    case(cSim \<Psi> P Q)
    moreover {
      fix \<Psi> P P' Q' Q
      assume "\<Psi> \<rhd> P \<approx> P'" and "(\<Psi>, P', Q') \<in> X" and "\<Psi> \<rhd> Q' \<approx> Q"
      from `(\<Psi>, P', Q') \<in> X` have "(\<Psi>, P', Q') \<in> ?X"
        by(blast intro: weakBisimReflexive bisimReflexive)
      moreover from `\<Psi> \<rhd> Q' \<approx> Q` have "\<Psi> \<rhd> Q' \<leadsto><weakBisim> Q" by(rule weakBisimE)
      moreover note `eqvt ?Y`
      moreover have "{(\<Psi>, P, R) | \<Psi> P R. \<exists>Q. (\<Psi>, P, Q) \<in> ?X \<and> \<Psi> \<rhd> Q \<approx> R} \<subseteq> ?Y"
        by(blast dest: weakBisimTransitive strongBisimWeakBisim)
      ultimately have "\<Psi> \<rhd> P' \<leadsto><?Y> Q" using Goal
        by(rule weakSimTransitive)
      note `\<Psi> \<rhd> P \<approx> P'` this `eqvt ?Y`
      moreover have "{(\<Psi>, P, R) | \<Psi> P R. \<exists>Q. \<Psi> \<rhd> P \<approx> Q \<and> (\<Psi>, Q, R) \<in> ?Y} \<subseteq> ?Y"
        by(blast dest: weakBisimTransitive)
      ultimately have "\<Psi> \<rhd> P \<leadsto><?Y> Q" using weakBisimE(2)
        by(rule weakSimTransitive)
    }      
    ultimately show ?case by auto
  next
    case(cExt \<Psi> P Q \<Psi>')
    thus ?case by(blast dest: bisimE weakBisimE intro: rExt)
  next
    case(cSym \<Psi> P Q) 
    thus ?case by(blast dest: bisimE(4) weakBisimE(4) rSym)
  qed
qed

end

end