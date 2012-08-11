(* 
   Title: Psi-calculi   
   Author/Maintainer: Jesper Bengtson (jebe@itu.dk), 2012
*)
theory Sum
  imports Semantics Close_Subst
begin

context env
begin

abbreviation sumAssertJudge ("_ \<oplus>\<^sub>_ _" [150, 50, 50] 150) 
  where "(P::('a, 'b, 'c) psi) \<oplus>\<^sub>\<phi> Q \<equiv> Cases [(\<phi>, P), (\<phi>, Q)]"

lemma SumAssert1:
  fixes \<Psi> :: 'b
  and   P :: "('a, 'b, 'c) psi"
  and   Q :: "('a, 'b, 'c) psi"

  assumes "\<Psi> \<rhd> P \<longmapsto> Rs"
  and     "\<Psi> \<turnstile> \<phi>"
  and     "guarded P"

  shows "\<Psi> \<rhd> P \<oplus>\<^sub>\<phi> Q \<longmapsto> Rs"
proof -
  note `\<Psi> \<rhd> P \<longmapsto> Rs`
  moreover have "(\<phi>, P) mem [(\<phi>, P), (\<phi>, Q)]" by simp
  ultimately show ?thesis using `\<Psi> \<turnstile> \<phi>` `guarded P`
    by(rule Case)
qed

lemma SumAssert2:
  fixes \<Psi> :: 'b
  and   P :: "('a, 'b, 'c) psi"
  and   Q :: "('a, 'b, 'c) psi"

  assumes "\<Psi> \<rhd> Q \<longmapsto> Rs"
  and     "\<Psi> \<turnstile> \<phi>"
  and     "guarded Q"

  shows "\<Psi> \<rhd> P \<oplus>\<^sub>\<phi> Q \<longmapsto> Rs"
proof -
  note `\<Psi> \<rhd> Q \<longmapsto> Rs`
  moreover have "(\<phi>, Q) mem [(\<phi>, P), (\<phi>, Q)]" by simp
  ultimately show ?thesis using `\<Psi> \<turnstile> \<phi>` `guarded Q`
    by(rule Case)
qed

lemma sumAssertCases[consumes 2, case_names cSum1 cSum2]:
  fixes \<Psi> :: 'b
  and   P :: "('a, 'b, 'c) psi"
  and   Q :: "('a, 'b, 'c) psi"
  and   \<phi> :: 'c

  assumes "\<Psi> \<rhd> P \<oplus>\<^sub>\<phi> Q \<longmapsto> Rs"
  and     "\<Psi> \<turnstile> \<phi>"
  and     rSum1: "\<lbrakk>\<Psi> \<rhd> P \<longmapsto> Rs; guarded P\<rbrakk> \<Longrightarrow> Prop"
  and     rSum2: "\<lbrakk>\<Psi> \<rhd> Q \<longmapsto> Rs; guarded Q\<rbrakk> \<Longrightarrow> Prop"

  shows Prop
proof -
  from `\<Psi> \<rhd> P \<oplus>\<^sub>\<phi> Q \<longmapsto> Rs` show ?thesis
  proof(induct rule: caseCases)
    case(cCase \<phi>' P')
    from `(\<phi>', P') mem [(\<phi>, P), (\<phi>, Q)]`
    have "\<phi> = \<phi>'" and D: "P = P' \<or> Q = P'" by auto
    from D show ?thesis
    proof(rule disjE)
      assume "P = P'"
      with `\<Psi> \<rhd> P' \<longmapsto> Rs` `guarded P'` show ?case by(rule_tac rSum1) auto
    next
      assume "Q = P'"
      with `\<Psi> \<rhd> P' \<longmapsto> Rs` `guarded P'` show ?case by(rule_tac rSum2) auto
    qed
  qed
qed

lemma sumElim[dest]:
  fixes \<Psi> :: 'b
  and   P :: "('a, 'b, 'c) psi"
  and   Q :: "('a, 'b, 'c) psi"
  and   \<phi> :: 'c

  assumes "\<Psi> \<rhd> P \<oplus>\<^sub>\<phi> Q \<longmapsto> Rs"
  and     "\<not>(\<Psi> \<turnstile> \<phi>)"

  shows False
using assms
by(induct rule: caseCases) auto

end

locale sum = env +
  fixes T :: 'c

  assumes Top: "\<Psi> \<turnstile> T"
  and     TopEqvt[eqvt]: "((p::name prm) \<bullet> T) = T"
  and     TopSubst[simp]: "substCond T xvec Tvec = T"
begin

abbreviation topJudge ("\<top>" 150) where "\<top> \<equiv> T"
abbreviation sumJudge (infixr "\<oplus>" 80) where "P \<oplus> Q \<equiv> P \<oplus>\<^sub>\<top> Q"

lemma topSeqSubst[simp]:
  shows "(substCond.seqSubst T \<sigma>) = T"
by(induct \<sigma>) auto

lemma suppTop:
  shows "((supp(\<top>))::name set) = {}"
by(auto simp add: supp_def eqvts)

lemma freshTop[simp]:
  fixes x    :: name
  and   xvec :: "name list"
  and   Xs   :: "name set"

  shows "x \<sharp> \<top>" and "xvec \<sharp>* \<top>" and "Xs \<sharp>* \<top>"
by(auto simp add: fresh_def fresh_star_def suppTop)

lemma sumSubst[simp]:
  fixes P    :: "('a, 'b, 'c) psi"
  and   Q    :: "('a, 'b, 'c) psi"
  and   xvec :: "name list"
  and   Tvec :: "'a list"

  assumes "length xvec = length Tvec"
  and     "distinct xvec"

  shows "(P \<oplus> Q)[xvec::=Tvec] = (P[xvec::=Tvec] \<oplus> Q[xvec::=Tvec])"
by auto

lemma sumSeqSubst[simp]:
  fixes P :: "('a, 'b, 'c) psi"
  and   Q :: "('a, 'b, 'c) psi"
  and   \<sigma> :: "(name list \<times> 'a list) list"

  assumes "wellFormedSubst \<sigma>"

  shows "(P \<oplus> Q)[<\<sigma>>] = ((P[<\<sigma>>]) \<oplus> (Q[<\<sigma>>]))"
using assms
by(induct \<sigma> arbitrary: P Q) auto

lemma Sum1:
  fixes \<Psi> :: 'b
  and   P :: "('a, 'b, 'c) psi"
  and   Q :: "('a, 'b, 'c) psi"

  assumes "\<Psi> \<rhd> P \<longmapsto> Rs"
  and     "guarded P"

  shows "\<Psi> \<rhd> P \<oplus> Q \<longmapsto> Rs"
proof -
  have "\<Psi> \<turnstile> \<top>" by(rule Top)
  with `\<Psi> \<rhd> P \<longmapsto> Rs` show ?thesis using `guarded P`
    by(rule SumAssert1)
qed

lemma Sum2:
  fixes \<Psi> :: 'b
  and   P :: "('a, 'b, 'c) psi"
  and   Q :: "('a, 'b, 'c) psi"

  assumes "\<Psi> \<rhd> Q \<longmapsto> Rs"
  and     "guarded Q"

  shows "\<Psi> \<rhd> P \<oplus> Q \<longmapsto> Rs"
proof -
  have "\<Psi> \<turnstile> \<top>" by(rule Top)
  with `\<Psi> \<rhd> Q \<longmapsto> Rs` show ?thesis using `guarded Q`
    by(rule SumAssert2)
qed

lemma sumCases[consumes 1, case_names cSum1 cSum2]:
  fixes \<Psi> :: 'b
  and   P :: "('a, 'b, 'c) psi"
  and   Q :: "('a, 'b, 'c) psi"

  assumes "\<Psi> \<rhd> P \<oplus> Q \<longmapsto> Rs"
  and     rSum1: "\<lbrakk>\<Psi> \<rhd> P \<longmapsto> Rs; guarded P\<rbrakk> \<Longrightarrow> Prop"
  and     rSum2: "\<lbrakk>\<Psi> \<rhd> Q \<longmapsto> Rs; guarded Q\<rbrakk> \<Longrightarrow> Prop"

  shows Prop
proof -
  have "\<Psi> \<turnstile> \<top>" by(rule Top)
  with `\<Psi> \<rhd> P \<oplus> Q \<longmapsto> Rs` show ?thesis
  proof(induct rule: sumAssertCases)
    case cSum1
    thus ?case by (rule rSum1)
  next
    case cSum2
    thus ?case by(rule rSum2)
  qed
qed

end

end

