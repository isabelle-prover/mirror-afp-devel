theory Bisim_Subst
  imports Bisim_Struct_Cong "Psi_Calculi.Close_Subst"
begin

text \<open>This file is a (heavily modified) variant of the theory {\it Psi\_Calculi.Bisim\_Subst}
from~\cite{DBLP:journals/afp/Bengtson12}.\<close>

context env begin

abbreviation
  bisimSubstJudge (\<open>_ \<rhd> _ \<sim>\<^sub>s _\<close> [70, 70, 70] 65) where "\<Psi> \<rhd> P \<sim>\<^sub>s Q \<equiv> (\<Psi>, P, Q) \<in> closeSubst bisim"
abbreviation
  bisimSubstNilJudge (\<open>_ \<sim>\<^sub>s _\<close> [70, 70] 65) where "P \<sim>\<^sub>s Q \<equiv> SBottom' \<rhd> P \<sim>\<^sub>s Q"

lemmas bisimSubstClosed[eqvt] = closeSubstClosed[OF bisimEqvt]
lemmas bisimSubstEqvt[simp] = closeSubstEqvt[OF bisimEqvt]

lemma bisimSubstOutputPres:
  fixes \<Psi> :: 'b
    and P :: "('a, 'b, 'c) psi"
    and Q :: "('a, 'b, 'c) psi"
    and M :: 'a
    and N :: 'a

assumes "\<Psi> \<rhd> P \<sim>\<^sub>s Q"

shows "\<Psi> \<rhd> M\<langle>N\<rangle>.P \<sim>\<^sub>s M\<langle>N\<rangle>.Q"
  using assms closeSubstI closeSubstE bisimOutputPres by force


lemma seqSubstInputChain[simp]:
  fixes xvec :: "name list"
    and N    :: "'a"
    and P    :: "('a, 'b, 'c) psi"
    and \<sigma>    :: "(name list \<times> 'a list) list"

assumes "xvec \<sharp>* \<sigma>"

shows "seqSubs' (inputChain xvec N P) \<sigma> = inputChain xvec (substTerm.seqSubst N \<sigma>) (seqSubs P \<sigma>)"
  using assms
  by(induct xvec) auto

lemma bisimSubstInputPres:
  fixes \<Psi>    :: 'b
    and P    :: "('a, 'b, 'c) psi"
    and Q    :: "('a, 'b, 'c) psi"
    and M    :: 'a
    and xvec :: "name list"
    and N    :: 'a

assumes "\<Psi> \<rhd> P \<sim>\<^sub>s Q"
  and   "xvec \<sharp>* \<Psi>"
  and   "distinct xvec"

shows "\<Psi> \<rhd> M\<lparr>\<lambda>*xvec N\<rparr>.P \<sim>\<^sub>s M\<lparr>\<lambda>*xvec N\<rparr>.Q"
proof(rule closeSubstI)
  fix \<sigma>
  assume "wellFormedSubst(\<sigma>::(name list \<times> 'a list) list)"
  obtain p where "(p \<bullet> xvec) \<sharp>* \<sigma>"
    and "(p \<bullet> xvec) \<sharp>* P" and "(p \<bullet> xvec) \<sharp>* Q" and "(p \<bullet> xvec) \<sharp>* \<Psi>" and "(p \<bullet> xvec) \<sharp>* N"
    and S: "set p \<subseteq> set xvec \<times> set (p \<bullet> xvec)"
    by(rule name_list_avoiding[where c="(\<sigma>, P, Q, \<Psi>, N)"]) auto

  from \<open>\<Psi> \<rhd> P \<sim>\<^sub>s Q\<close> have "(p \<bullet> \<Psi>) \<rhd> (p \<bullet> P) \<sim>\<^sub>s (p \<bullet> Q)"
    by(rule bisimSubstClosed)
  with \<open>xvec \<sharp>* \<Psi>\<close> \<open>(p \<bullet> xvec) \<sharp>* \<Psi>\<close> S have "\<Psi> \<rhd> (p \<bullet> P) \<sim>\<^sub>s (p \<bullet> Q)"
    by simp

  {
    fix Tvec :: "'a list"
    from \<open>\<Psi> \<rhd> (p \<bullet> P) \<sim>\<^sub>s (p \<bullet> Q)\<close> \<open>wellFormedSubst \<sigma>\<close> have "\<Psi> \<rhd> (p \<bullet> P)[<\<sigma>>] \<sim>\<^sub>s (p \<bullet> Q)[<\<sigma>>]"
      by(rule closeSubstUnfold)
    moreover assume "length xvec = length Tvec" and "distinct xvec"
    ultimately have "\<Psi> \<rhd> ((p \<bullet> P)[<\<sigma>>])[(p \<bullet> xvec)::=Tvec] \<sim> ((p \<bullet> Q)[<\<sigma>>])[(p \<bullet> xvec)::=Tvec]"
      apply -
      by(drule closeSubstE[where \<sigma>="[((p \<bullet> xvec), Tvec)]"]) auto
  }

  with \<open>(p \<bullet> xvec) \<sharp>* \<sigma>\<close> \<open>distinct xvec\<close>
  have "\<Psi> \<rhd> (M\<lparr>\<lambda>*(p \<bullet> xvec) (p \<bullet> N)\<rparr>.(p \<bullet> P))[<\<sigma>>] \<sim> (M\<lparr>\<lambda>*(p \<bullet> xvec) (p \<bullet> N)\<rparr>.(p \<bullet> Q))[<\<sigma>>]"
    by(force intro: bisimInputPres)
  moreover from \<open>(p \<bullet> xvec) \<sharp>* N\<close> \<open>(p \<bullet> xvec) \<sharp>* P\<close> S have "M\<lparr>\<lambda>*(p \<bullet> xvec) (p \<bullet> N)\<rparr>.(p \<bullet> P) = M\<lparr>\<lambda>*xvec N\<rparr>.P"
    apply(simp add: psi.inject) by(rule inputChainAlpha[symmetric]) auto
  moreover from \<open>(p \<bullet> xvec) \<sharp>* N\<close> \<open>(p \<bullet> xvec) \<sharp>* Q\<close> S have "M\<lparr>\<lambda>*(p \<bullet> xvec) (p \<bullet> N)\<rparr>.(p \<bullet> Q) = M\<lparr>\<lambda>*xvec N\<rparr>.Q"
    apply(simp add: psi.inject) by(rule inputChainAlpha[symmetric]) auto
  ultimately show "\<Psi> \<rhd> (M\<lparr>\<lambda>*xvec N\<rparr>.P)[<\<sigma>>] \<sim> (M\<lparr>\<lambda>*xvec N\<rparr>.Q)[<\<sigma>>]"
    by force
qed

lemma bisimSubstCasePresAux:
  fixes \<Psi>   :: 'b
    and CsP :: "('c \<times> ('a, 'b, 'c) psi) list"
    and CsQ :: "('c \<times> ('a, 'b, 'c) psi) list"

assumes C1: "\<And>\<phi> P. (\<phi>, P) \<in> set CsP \<Longrightarrow> \<exists>Q. (\<phi>, Q) \<in> set CsQ \<and> guarded Q \<and> \<Psi> \<rhd> P \<sim>\<^sub>s Q"
  and   C2: "\<And>\<phi> Q. (\<phi>, Q) \<in> set CsQ \<Longrightarrow> \<exists>P. (\<phi>, P) \<in> set CsP \<and> guarded P \<and> \<Psi> \<rhd> P \<sim>\<^sub>s Q"

shows "\<Psi> \<rhd> Cases CsP \<sim>\<^sub>s Cases CsQ"
proof -
  {
    fix \<sigma> :: "(name list \<times> 'a list) list"

    assume "wellFormedSubst \<sigma>"

    have "\<Psi> \<rhd> Cases(caseListSeqSubst CsP \<sigma>) \<sim> Cases(caseListSeqSubst CsQ \<sigma>)"
    proof(rule bisimCasePres)
      fix \<phi> P
      assume "(\<phi>, P) \<in> set (caseListSeqSubst CsP \<sigma>)"
      then obtain \<phi>' P' where "(\<phi>', P') \<in> set CsP" and "\<phi> = substCond.seqSubst \<phi>' \<sigma>" and PeqP': "P = (P'[<\<sigma>>])"
        by(induct CsP) force+
      from \<open>(\<phi>', P') \<in> set CsP\<close> obtain Q' where "(\<phi>', Q') \<in> set CsQ" and "guarded Q'" and "\<Psi> \<rhd> P' \<sim>\<^sub>s Q'" by(blast dest: C1)
      from \<open>(\<phi>', Q') \<in> set CsQ\<close> \<open>\<phi> = substCond.seqSubst \<phi>' \<sigma>\<close> obtain Q where "(\<phi>, Q) \<in> set (caseListSeqSubst CsQ \<sigma>)" and "Q = Q'[<\<sigma>>]"
        by(induct CsQ) auto
      with PeqP' \<open>guarded Q'\<close> \<open>\<Psi> \<rhd> P' \<sim>\<^sub>s Q'\<close> \<open>wellFormedSubst \<sigma>\<close> show "\<exists>Q. (\<phi>, Q) \<in> set (caseListSeqSubst CsQ \<sigma>) \<and> guarded Q \<and> \<Psi> \<rhd> P \<sim> Q"
        by(blast dest: closeSubstE guardedSeqSubst)
    next
      fix \<phi> Q
      assume "(\<phi>, Q) \<in> set (caseListSeqSubst CsQ \<sigma>)"
      then obtain \<phi>' Q' where "(\<phi>', Q') \<in> set CsQ" and "\<phi> = substCond.seqSubst \<phi>' \<sigma>" and QeqQ': "Q = Q'[<\<sigma>>]"
        by(induct CsQ) force+
      from \<open>(\<phi>', Q') \<in> set CsQ\<close> obtain P' where "(\<phi>', P') \<in> set CsP" and "guarded P'" and "\<Psi> \<rhd> P' \<sim>\<^sub>s Q'" by(blast dest: C2)
      from \<open>(\<phi>', P') \<in> set CsP\<close> \<open>\<phi> = substCond.seqSubst \<phi>' \<sigma>\<close> obtain P where "(\<phi>, P) \<in> set (caseListSeqSubst CsP \<sigma>)" and "P = P'[<\<sigma>>]"
        by(induct CsP) auto
      with QeqQ' \<open>guarded P'\<close> \<open>\<Psi> \<rhd> P' \<sim>\<^sub>s Q'\<close> \<open>wellFormedSubst \<sigma>\<close>  show "\<exists>P. (\<phi>, P) \<in> set (caseListSeqSubst CsP \<sigma>) \<and> guarded P \<and> \<Psi> \<rhd> P \<sim> Q"
        by(blast dest: closeSubstE guardedSeqSubst)
    qed
  }
  then show ?thesis
    by(intro closeSubstI) auto
qed

lemma bisimSubstReflexive:
  fixes \<Psi> :: 'b
    and P :: "('a, 'b, 'c) psi"

shows "\<Psi> \<rhd> P \<sim>\<^sub>s P"
  by(auto intro: closeSubstI bisimReflexive)

lemma bisimSubstTransitive:
  fixes \<Psi> :: 'b
    and P :: "('a, 'b, 'c) psi"
    and Q :: "('a, 'b, 'c) psi"
    and R :: "('a, 'b, 'c) psi"

assumes "\<Psi> \<rhd> P \<sim>\<^sub>s Q"
  and   "\<Psi> \<rhd> Q \<sim>\<^sub>s R"

shows "\<Psi> \<rhd> P \<sim>\<^sub>s R"
  using assms
  by(auto intro: closeSubstI closeSubstE bisimTransitive)

lemma bisimSubstSymmetric:
  fixes \<Psi> :: 'b
    and P :: "('a, 'b, 'c) psi"
    and Q :: "('a, 'b, 'c) psi"

assumes "\<Psi> \<rhd> P \<sim>\<^sub>s Q"

shows "\<Psi> \<rhd> Q \<sim>\<^sub>s P"
  using assms
  by(auto intro: closeSubstI closeSubstE bisimE)

lemma bisimSubstCasePres:
  fixes \<Psi>   :: 'b
    and CsP :: "('c \<times> ('a, 'b, 'c) psi) list"
    and CsQ :: "('c \<times> ('a, 'b, 'c) psi) list"

assumes "length CsP = length CsQ"
  and   C: "\<And>(i::nat) \<phi> P \<phi>' Q. \<lbrakk>i <= length CsP; (\<phi>, P) = nth CsP i; (\<phi>', Q) = nth CsQ i\<rbrakk> \<Longrightarrow> \<phi> = \<phi>' \<and> \<Psi> \<rhd> P \<sim>\<^sub>s Q \<and> guarded P \<and> guarded Q"

shows "\<Psi> \<rhd> Cases CsP \<sim>\<^sub>s Cases CsQ"
proof -
  {
    fix \<phi>
      and P

    assume "(\<phi>, P) \<in> set CsP"

    with \<open>length CsP = length CsQ\<close> have "\<exists>Q. (\<phi>, Q) \<in> set CsQ \<and> guarded Q \<and> \<Psi> \<rhd> P \<sim>\<^sub>s Q" using C
    proof(induct n=="length CsP" arbitrary: CsP CsQ rule: nat.induct)
      case zero then show ?case by simp
    next
      case(Suc n) then show ?case
      proof(cases CsP)
        case Nil then show ?thesis using \<open>Suc n = length CsP\<close> by simp
      next
        case(Cons P'\<phi> CsP')
        note CsPdef = this
        then show ?thesis
        proof(cases CsQ)
          case Nil then show ?thesis using CsPdef \<open>length CsP = length CsQ\<close>
            by simp
        next
          case(Cons Q'\<phi> CsQ')
          obtain Q' \<phi>' where Q'phi: "Q'\<phi>=(\<phi>',Q')"
            by(induct Q'\<phi>) auto
          show ?thesis
          proof(cases "P'\<phi> = (\<phi>,P)")
            case True
            have "0 <= length CsP" unfolding CsPdef
              by simp
            moreover from True have "(\<phi>, P) = nth CsP 0" using \<open>(\<phi>, P) \<in> set CsP\<close> unfolding CsPdef
              by simp
            moreover have "(\<phi>', Q') = nth CsQ 0" unfolding Cons Q'phi by simp
            ultimately have "\<phi> = \<phi>' \<and> \<Psi> \<rhd> P \<sim>\<^sub>s Q' \<and> guarded P \<and> guarded Q'"
              by(rule Suc)
            then show ?thesis unfolding Cons Q'phi
              by(intro exI[where x=Q']) auto
          next
            case False
            have "n = length CsP'" using \<open>Suc n = length CsP\<close> unfolding CsPdef
              by simp
            moreover have "length CsP' = length CsQ'" using \<open>length CsP = length CsQ\<close> unfolding CsPdef Cons by simp
            moreover from \<open>(\<phi>,P) \<in> set CsP\<close> False have "(\<phi>, P) \<in> set CsP'" unfolding CsPdef by simp
            moreover
            {
              fix   i::nat
                and \<phi>::'c
                and \<phi>'::'c
                and P::"('a,'b,'c) psi"
                and Q::"('a,'b,'c) psi"
              assume "i \<le> length CsP'"
                and  "(\<phi>, P) = CsP' ! i"
                and  "(\<phi>', Q) = CsQ' ! i"
              then have "(i+1) \<le> length CsP"
                and "(\<phi>, P) = CsP ! (i+1)"
                and "(\<phi>', Q) = CsQ ! (i+1)"
                unfolding CsPdef Cons
                by simp+
              then have "\<phi> = \<phi>' \<and> \<Psi> \<rhd> P \<sim>\<^sub>s Q \<and> guarded P \<and> guarded Q"
                by(rule Suc)
            }
            note this
            ultimately have "\<exists>Q. (\<phi>, Q) \<in> set CsQ' \<and> guarded Q \<and> \<Psi> \<rhd> P \<sim>\<^sub>s Q"
              by(rule Suc)
            then show ?thesis unfolding Cons by auto
          qed
        qed
      qed
    qed
  }
  note this
  moreover
  {
    fix \<phi>
      and Q

    assume "(\<phi>, Q) \<in> set CsQ"

    with \<open>length CsP = length CsQ\<close> have "\<exists>P. (\<phi>, P) \<in> set CsP \<and> guarded P \<and> \<Psi> \<rhd> P \<sim>\<^sub>s Q" using C
    proof(induct n=="length CsQ" arbitrary: CsP CsQ rule: nat.induct)
      case zero then show ?case by simp
    next
      case(Suc n) then show ?case
      proof(cases CsQ)
        case Nil then show ?thesis using \<open>Suc n = length CsQ\<close> by simp
      next
        case(Cons Q'\<phi> CsQ')
        note CsPdef = this
        then show ?thesis
        proof(cases CsP)
          case Nil then show ?thesis using CsPdef \<open>length CsP = length CsQ\<close>
            by simp
        next
          case(Cons P'\<phi> CsP')
          obtain P' \<phi>' where P'phi: "P'\<phi>=(\<phi>',P')"
            by(induct P'\<phi>) auto
          show ?thesis
          proof(cases "Q'\<phi> = (\<phi>,Q)")
            case True
            have "0 <= length CsP" unfolding CsPdef
              by simp
            moreover have "(\<phi>', P') = nth CsP 0" unfolding Cons P'phi by simp
            moreover from True have "(\<phi>, Q) = nth CsQ 0" using \<open>(\<phi>, Q) \<in> set CsQ\<close> unfolding CsPdef
              by simp
            ultimately have "\<phi>' = \<phi> \<and> \<Psi> \<rhd> P' \<sim>\<^sub>s Q \<and> guarded P' \<and> guarded Q"
              by(rule Suc)
            then show ?thesis unfolding Cons P'phi
              by(intro exI[where x=P']) auto
          next
            case False
            have "n = length CsQ'" using \<open>Suc n = length CsQ\<close> unfolding CsPdef
              by simp
            moreover have "length CsP' = length CsQ'" using \<open>length CsP = length CsQ\<close> unfolding CsPdef Cons by simp
            moreover from \<open>(\<phi>,Q) \<in> set CsQ\<close> False have "(\<phi>, Q) \<in> set CsQ'" unfolding CsPdef by simp
            moreover
            {
              fix   i::nat
                and \<phi>::'c
                and \<phi>'::'c
                and P::"('a,'b,'c) psi"
                and Q::"('a,'b,'c) psi"
              assume "i \<le> length CsP'"
                and  "(\<phi>, P) = CsP' ! i"
                and  "(\<phi>', Q) = CsQ' ! i"
              then have "(i+1) \<le> length CsP"
                and "(\<phi>, P) = CsP ! (i+1)"
                and "(\<phi>', Q) = CsQ ! (i+1)"
                unfolding CsPdef Cons
                by simp+
              then have "\<phi> = \<phi>' \<and> \<Psi> \<rhd> P \<sim>\<^sub>s Q \<and> guarded P \<and> guarded Q"
                by(rule Suc)
            }
            note this
            ultimately have "\<exists>P. (\<phi>, P) \<in> set CsP' \<and> guarded P \<and> \<Psi> \<rhd> P \<sim>\<^sub>s Q"
              by(rule Suc)
            then show ?thesis unfolding Cons by auto
          qed
        qed
      qed
    qed
  }
  ultimately show ?thesis
    by(rule bisimSubstCasePresAux)
qed

lemma bisimSubstParPres:
  fixes \<Psi> :: 'b
    and P :: "('a, 'b, 'c) psi"
    and Q :: "('a, 'b, 'c) psi"
    and R :: "('a, 'b, 'c) psi"

assumes "\<Psi> \<rhd> P \<sim>\<^sub>s Q"

shows "\<Psi> \<rhd> P \<parallel> R \<sim>\<^sub>s Q \<parallel> R"
  using assms closeSubstI closeSubstE bisimParPres by force

lemma bisimSubstResPres:
  fixes \<Psi> :: 'b
    and P :: "('a, 'b, 'c) psi"
    and Q :: "('a, 'b, 'c) psi"
    and x :: name

assumes "\<Psi> \<rhd> P \<sim>\<^sub>s Q"
  and   "x \<sharp> \<Psi>"

shows "\<Psi> \<rhd> \<lparr>\<nu>x\<rparr>P \<sim>\<^sub>s \<lparr>\<nu>x\<rparr>Q"
proof(rule closeSubstI)
  fix \<sigma> :: "(name list \<times> 'a list) list"

  assume "wellFormedSubst \<sigma>"
  obtain y::name where "y \<sharp> \<Psi>" and "y \<sharp> P" and "y \<sharp> Q" and "y \<sharp> \<sigma>"
    by(generate_fresh "name") (auto simp add: fresh_prod)

  from \<open>\<Psi> \<rhd> P \<sim>\<^sub>s Q\<close> have "([(x, y)] \<bullet> \<Psi>) \<rhd> ([(x, y)] \<bullet> P) \<sim>\<^sub>s ([(x, y)] \<bullet> Q)"
    by(rule bisimSubstClosed)
  with \<open>x \<sharp> \<Psi>\<close> \<open>y \<sharp> \<Psi>\<close> have "\<Psi> \<rhd> ([(x, y)] \<bullet> P) \<sim>\<^sub>s ([(x, y)] \<bullet> Q)"
    by simp
  then have "\<Psi> \<rhd> ([(x, y)] \<bullet> P)[<\<sigma>>] \<sim> ([(x, y)] \<bullet> Q)[<\<sigma>>]" using \<open>wellFormedSubst \<sigma>\<close>
    by(rule closeSubstE)
  then have "\<Psi> \<rhd> \<lparr>\<nu>y\<rparr>(([(x, y)] \<bullet> P)[<\<sigma>>]) \<sim> \<lparr>\<nu>y\<rparr>(([(x, y)] \<bullet> Q)[<\<sigma>>])" using \<open>y \<sharp> \<Psi>\<close>
    by(rule bisimResPres)
  with \<open>y \<sharp> P\<close> \<open>y \<sharp> Q\<close> \<open>y \<sharp> \<sigma>\<close>
  show "\<Psi> \<rhd> (\<lparr>\<nu>x\<rparr>P)[<\<sigma>>] \<sim> (\<lparr>\<nu>x\<rparr>Q)[<\<sigma>>]"
    by(simp add: alphaRes)
qed

lemma bisimSubstBangPres:
  fixes \<Psi> :: 'b
    and P :: "('a, 'b, 'c) psi"
    and Q :: "('a, 'b, 'c) psi"

assumes "\<Psi> \<rhd> P \<sim>\<^sub>s Q"
  and   "guarded P"
  and   "guarded Q"

shows "\<Psi> \<rhd> !P \<sim>\<^sub>s !Q"
  using assms closeSubstI closeSubstE bisimBangPres guardedSeqSubst by force

lemma substNil[simp]:
  fixes xvec :: "name list"
    and Tvec :: "'a list"

assumes "wellFormedSubst \<sigma>"
  and   "distinct xvec"

shows "(\<zero>[<\<sigma>>]) = \<zero>"
  using assms
  by simp

lemma bisimSubstParNil:
  fixes \<Psi> :: 'b
    and P :: "('a, 'b, 'c) psi"

shows "\<Psi> \<rhd> P \<parallel> \<zero> \<sim>\<^sub>s P"
  by(auto intro!: closeSubstI bisimParNil)

lemma bisimSubstParComm:
  fixes \<Psi> :: 'b
    and P :: "('a, 'b, 'c) psi"
    and Q :: "('a, 'b, 'c) psi"

shows "\<Psi> \<rhd> P \<parallel> Q \<sim>\<^sub>s Q \<parallel> P"
  by(auto intro!: closeSubstI bisimParComm)

lemma bisimSubstParAssoc:
  fixes \<Psi> :: 'b
    and P :: "('a, 'b, 'c) psi"
    and Q :: "('a, 'b, 'c) psi"
    and R :: "('a, 'b, 'c) psi"

shows "\<Psi> \<rhd> (P \<parallel> Q) \<parallel> R \<sim>\<^sub>s P \<parallel> (Q \<parallel> R)"
  by(auto intro!: closeSubstI bisimParAssoc)

lemma bisimSubstResNil:
  fixes \<Psi> :: 'b
    and x :: name

shows "\<Psi> \<rhd> \<lparr>\<nu>x\<rparr>\<zero> \<sim>\<^sub>s \<zero>"
proof(rule closeSubstI)
  fix \<sigma>:: "(name list \<times> 'a list) list"

  assume "wellFormedSubst \<sigma>"
  obtain y::name where "y \<sharp> \<Psi>" and "y \<sharp> \<sigma>"
    by(generate_fresh "name") (auto simp add: fresh_prod)
  have "\<Psi> \<rhd> \<lparr>\<nu>y\<rparr>\<zero> \<sim> \<zero>" by(rule bisimResNil)
  with \<open>y \<sharp> \<sigma>\<close> \<open>wellFormedSubst \<sigma>\<close>  show "\<Psi> \<rhd> (\<lparr>\<nu>x\<rparr>\<zero>)[<\<sigma>>] \<sim> \<zero>[<\<sigma>>]"
    by(subst alphaRes[of y]) auto
qed

lemma seqSubst2:
  fixes x :: name
    and P :: "('a, 'b, 'c) psi"

assumes "wellFormedSubst \<sigma>"
  and   "x \<sharp> \<sigma>"
  and   "x \<sharp> P"

shows "x \<sharp> P[<\<sigma>>]"
  using assms
  by(induct \<sigma> arbitrary: P, auto) (blast dest: subst2)

notation substTerm.seqSubst (\<open>_[<_>]\<close> [100, 100] 100)

lemma bisimSubstScopeExt:
  fixes \<Psi> :: 'b
    and x :: name
    and P :: "('a, 'b, 'c) psi"
    and Q :: "('a, 'b, 'c) psi"

assumes "x \<sharp> P"

shows "\<Psi> \<rhd> \<lparr>\<nu>x\<rparr>(P \<parallel> Q) \<sim>\<^sub>s P \<parallel> \<lparr>\<nu>x\<rparr>Q"
proof(rule closeSubstI)
  fix \<sigma>:: "(name list \<times> 'a list) list"

  assume "wellFormedSubst \<sigma>"
  obtain y::name where "y \<sharp> \<Psi>" and "y \<sharp> \<sigma>" and "y \<sharp> P" and "y \<sharp> Q"
    by(generate_fresh "name") (auto simp add: fresh_prod)
  moreover from \<open>wellFormedSubst \<sigma>\<close>  \<open>y \<sharp> \<sigma>\<close> \<open>y \<sharp> P\<close> have "y \<sharp> P[<\<sigma>>]"
    by(rule seqSubst2)
  then have "\<Psi> \<rhd> \<lparr>\<nu>y\<rparr>((P[<\<sigma>>]) \<parallel> (([(x, y)] \<bullet> Q)[<\<sigma>>])) \<sim> (P[<\<sigma>>]) \<parallel> \<lparr>\<nu>y\<rparr>(([(x, y)] \<bullet> Q)[<\<sigma>>])"
    by(rule bisimScopeExt)
  with \<open>x \<sharp> P\<close> \<open>y \<sharp> P\<close> \<open>y \<sharp> Q\<close> \<open>y \<sharp> \<sigma>\<close> show "\<Psi> \<rhd> (\<lparr>\<nu>x\<rparr>(P \<parallel> Q))[<\<sigma>>] \<sim> (P \<parallel> \<lparr>\<nu>x\<rparr>Q)[<\<sigma>>]"
    apply(subst alphaRes[of y], simp)
    apply(subst alphaRes[of y Q], simp)
    by(simp add: eqvts)
qed

lemma bisimSubstCasePushRes:
  fixes x  :: name
    and \<Psi>  :: 'b
    and Cs :: "('c \<times> ('a, 'b, 'c) psi) list"

assumes "x \<sharp> map fst Cs"

shows "\<Psi> \<rhd> \<lparr>\<nu>x\<rparr>(Cases Cs) \<sim>\<^sub>s Cases map (\<lambda>(\<phi>, P). (\<phi>, \<lparr>\<nu>x\<rparr>P)) Cs"
proof(rule closeSubstI)
  fix \<sigma>:: "(name list \<times> 'a list) list"

  assume "wellFormedSubst \<sigma>"
  obtain y::name where "y \<sharp> \<Psi>" and "y \<sharp> \<sigma>" and "y \<sharp> Cs"
    by(generate_fresh "name") (auto simp add: fresh_prod)

  {
    fix x    :: name
      and Cs   :: "('c \<times> ('a, 'b, 'c) psi) list"
      and \<sigma>    :: "(name list \<times> 'a list) list"

    assume "x \<sharp> \<sigma>"

    then have "(Cases map (\<lambda>(\<phi>, P). (\<phi>, \<lparr>\<nu>x\<rparr>P)) Cs)[<\<sigma>>] = Cases map (\<lambda>(\<phi>, P). (\<phi>, \<lparr>\<nu>x\<rparr>P)) (caseListSeqSubst Cs \<sigma>)"
      by(induct Cs) auto
  }
  note C1 = this

  {
    fix x    :: name
      and y    :: name
      and Cs   :: "('c \<times> ('a, 'b, 'c) psi) list"

    assume "x \<sharp> map fst Cs"
      and  "y \<sharp> map fst Cs"
      and  "y \<sharp> Cs"

    then have "(Cases map (\<lambda>(\<phi>, P). (\<phi>, \<lparr>\<nu>x\<rparr>P)) Cs) = Cases map (\<lambda>(\<phi>, P). (\<phi>, \<lparr>\<nu>y\<rparr>P)) ([(x, y)] \<bullet> Cs)"
      by(induct Cs) (auto simp add: fresh_list_cons alphaRes)
  }
  note C2 = this

  from \<open>y \<sharp> Cs\<close> have "y \<sharp> map fst Cs" by(induct Cs) (auto simp add: fresh_list_cons fresh_list_nil)
  from \<open>y \<sharp> Cs\<close> \<open>y \<sharp> \<sigma>\<close> \<open>x \<sharp> map fst Cs\<close> \<open>wellFormedSubst \<sigma>\<close>  have "y \<sharp> map fst (caseListSeqSubst ([(x, y)] \<bullet> Cs) \<sigma>)"
    by(induct Cs) (auto intro: substCond.seqSubst2 simp add: fresh_list_cons fresh_list_nil fresh_prod)
  then have "\<Psi> \<rhd> \<lparr>\<nu>y\<rparr>(Cases(caseListSeqSubst ([(x, y)] \<bullet> Cs) \<sigma>)) \<sim> Cases map (\<lambda>(\<phi>, P). (\<phi>, \<lparr>\<nu>y\<rparr>P)) (caseListSeqSubst ([(x, y)] \<bullet> Cs) \<sigma>)"
    by(rule bisimCasePushRes)

  with \<open>y \<sharp> Cs\<close> \<open>x \<sharp> map fst Cs\<close> \<open>y \<sharp> map fst Cs\<close> \<open>y \<sharp> \<sigma>\<close> \<open>wellFormedSubst \<sigma>\<close>
  show "\<Psi> \<rhd> (\<lparr>\<nu>x\<rparr>(Cases Cs))[<\<sigma>>] \<sim> (Cases map (\<lambda>(\<phi>, P). (\<phi>, \<lparr>\<nu>x\<rparr>P)) Cs)[<\<sigma>>]"
    apply(subst C2[of x Cs y])
       apply assumption+
    apply(subst C1)
     apply assumption+
    apply(subst alphaRes[of y], simp)
    by(simp add: eqvts)
qed

lemma bisimSubstOutputPushRes:
  fixes x :: name
    and \<Psi> :: 'b
    and M :: 'a
    and N :: 'a
    and P :: "('a, 'b, 'c) psi"

assumes "x \<sharp> M"
  and   "x \<sharp> N"

shows "\<Psi> \<rhd> \<lparr>\<nu>x\<rparr>(M\<langle>N\<rangle>.P) \<sim>\<^sub>s M\<langle>N\<rangle>.\<lparr>\<nu>x\<rparr>P"
proof(rule closeSubstI)
  fix \<sigma>:: "(name list \<times> 'a list) list"

  assume "wellFormedSubst \<sigma>"
  obtain y::name where "y \<sharp> \<Psi>" and "y \<sharp> \<sigma>" and "y \<sharp> P" and "y \<sharp> M" and "y \<sharp> N"
    by(generate_fresh "name") (auto simp add: fresh_prod)
  from \<open>wellFormedSubst \<sigma>\<close>  \<open>y \<sharp> M\<close> \<open>y \<sharp> \<sigma>\<close> have "y \<sharp> M[<\<sigma>>]" by auto
  moreover from \<open>wellFormedSubst \<sigma>\<close>  \<open>y \<sharp> N\<close> \<open>y \<sharp> \<sigma>\<close> have "y \<sharp> N[<\<sigma>>]" by auto
  ultimately have "\<Psi> \<rhd> \<lparr>\<nu>y\<rparr>((M[<\<sigma>>])\<langle>(N[<\<sigma>>])\<rangle>.(([(x, y)] \<bullet> P)[<\<sigma>>])) \<sim> (M[<\<sigma>>])\<langle>(N[<\<sigma>>])\<rangle>.(\<lparr>\<nu>y\<rparr>(([(x, y)] \<bullet> P)[<\<sigma>>]))"
    by(rule bisimOutputPushRes)
  with \<open>y \<sharp> M\<close> \<open>y \<sharp> N\<close> \<open>y \<sharp> P\<close> \<open>x \<sharp> M\<close> \<open>x \<sharp> N\<close> \<open>y \<sharp> \<sigma>\<close> \<open>wellFormedSubst \<sigma>\<close>
  show "\<Psi> \<rhd> (\<lparr>\<nu>x\<rparr>(M\<langle>N\<rangle>.P))[<\<sigma>>] \<sim> (M\<langle>N\<rangle>.\<lparr>\<nu>x\<rparr>P)[<\<sigma>>]"
    apply(subst alphaRes[of y], simp)
    apply(subst alphaRes[of y P], simp)
    by(simp add: eqvts)
qed

lemma bisimSubstInputPushRes:
  fixes x    :: name
    and \<Psi>    :: 'b
    and M    :: 'a
    and xvec :: "name list"
    and N    :: 'a

assumes "x \<sharp> M"
  and   "x \<sharp> xvec"
  and   "x \<sharp> N"

shows "\<Psi> \<rhd> \<lparr>\<nu>x\<rparr>(M\<lparr>\<lambda>*xvec N\<rparr>.P) \<sim>\<^sub>s M\<lparr>\<lambda>*xvec N\<rparr>.\<lparr>\<nu>x\<rparr>P"
proof(rule closeSubstI)
  fix \<sigma>:: "(name list \<times> 'a list) list"

  assume "wellFormedSubst \<sigma>"
  obtain y::name where "y \<sharp> \<Psi>" and "y \<sharp> \<sigma>" and "y \<sharp> P" and "y \<sharp> M" and "y \<sharp> xvec" and "y \<sharp> N"
    by(generate_fresh "name") (auto simp add: fresh_prod)
  obtain p::"name prm" where "(p \<bullet> xvec) \<sharp>* N" and  "(p \<bullet> xvec) \<sharp>* P" and "x \<sharp> (p \<bullet> xvec)" and "y \<sharp> (p \<bullet> xvec)" and "(p \<bullet> xvec) \<sharp>* \<sigma>"
    and S: "set p \<subseteq> set xvec \<times> set(p \<bullet> xvec)"
    by(rule name_list_avoiding[where c="(N, P, x, y, \<sigma>)"]) auto

  from \<open>wellFormedSubst \<sigma>\<close> \<open>y \<sharp> M\<close> \<open>y \<sharp> \<sigma> \<close> have "y \<sharp> M[<\<sigma>>]" by auto
  moreover note \<open>y \<sharp> (p \<bullet> xvec)\<close>
  moreover from \<open>y \<sharp> N\<close> have "(p \<bullet> y) \<sharp> (p \<bullet> N)" by(simp add: pt_fresh_bij[OF pt_name_inst, OF at_name_inst])
  with \<open>y \<sharp> xvec\<close> \<open>y \<sharp> (p \<bullet> xvec)\<close> S have "y \<sharp> p \<bullet> N" by simp
  with \<open>wellFormedSubst \<sigma>\<close> have "y \<sharp> (p \<bullet> N)[<\<sigma>>]" using \<open>y \<sharp> \<sigma>\<close> by auto
  ultimately have "\<Psi> \<rhd> \<lparr>\<nu>y\<rparr>((M[<\<sigma>>])\<lparr>\<lambda>*(p \<bullet> xvec) ((p \<bullet> N)[<\<sigma>>])\<rparr>.(([(x, y)] \<bullet> (p \<bullet> P))[<\<sigma>>])) \<sim> (M[<\<sigma>>])\<lparr>\<lambda>*(p \<bullet> xvec) ((p \<bullet> N)[<\<sigma>>])\<rparr>.(\<lparr>\<nu>y\<rparr>(([(x, y)] \<bullet> p \<bullet> P)[<\<sigma>>]))"
    by(rule bisimInputPushRes)
  with \<open>y \<sharp> M\<close> \<open>y \<sharp> N\<close> \<open>y \<sharp> P\<close> \<open>x \<sharp> M\<close> \<open>x \<sharp> N\<close> \<open>y \<sharp> xvec\<close> \<open>x \<sharp> xvec\<close> \<open>(p \<bullet> xvec) \<sharp>* N\<close> \<open>(p \<bullet> xvec) \<sharp>* P\<close>
    \<open>x \<sharp> (p \<bullet> xvec)\<close> \<open>y \<sharp> (p \<bullet> xvec)\<close> \<open>y \<sharp> \<sigma>\<close> \<open>(p \<bullet> xvec) \<sharp>* \<sigma>\<close> S \<open>wellFormedSubst \<sigma>\<close>
  show "\<Psi> \<rhd> (\<lparr>\<nu>x\<rparr>(M\<lparr>\<lambda>*xvec N\<rparr>.P))[<\<sigma>>] \<sim> (M\<lparr>\<lambda>*xvec N\<rparr>.\<lparr>\<nu>x\<rparr>P)[<\<sigma>>]"
    apply(subst inputChainAlpha')
       apply assumption+
    apply(subst inputChainAlpha'[of p xvec])
       apply(simp add: abs_fresh_star)
      apply assumption+
    apply(simp add: eqvts)
    apply(subst alphaRes[of y], simp)
     apply(simp add: inputChainFresh)
     apply(simp add: freshChainSimps)
    apply(subst alphaRes[of y "(p \<bullet> P)"])
     apply(simp add: freshChainSimps)
    by(simp add: freshChainSimps eqvts)
qed

lemma bisimSubstResComm:
  fixes x :: name
    and y :: name

shows "\<Psi> \<rhd> \<lparr>\<nu>x\<rparr>(\<lparr>\<nu>y\<rparr>P) \<sim>\<^sub>s \<lparr>\<nu>y\<rparr>(\<lparr>\<nu>x\<rparr>P)"
proof(cases "x = y")
  assume "x = y"
  then show ?thesis by(force intro: bisimSubstReflexive)
next
  assume "x \<noteq> y"
  show ?thesis
  proof(rule closeSubstI)
    fix \<sigma>:: "(name list \<times> 'a list) list"
    assume "wellFormedSubst \<sigma>"


    obtain x'::name where "x' \<sharp>  \<Psi>" and "x' \<sharp> \<sigma>" and "x' \<sharp> P" and "x \<noteq> x'" and "y \<noteq> x'"
      by(generate_fresh "name") (auto simp add: fresh_prod)
    obtain y'::name where "y' \<sharp>  \<Psi>" and "y' \<sharp> \<sigma>" and "y' \<sharp> P" and "x \<noteq> y'" and "y \<noteq> y'" and "x' \<noteq> y'"
      by(generate_fresh "name") (auto simp add: fresh_prod)

    have "\<Psi> \<rhd> \<lparr>\<nu>x'\<rparr>(\<lparr>\<nu>y'\<rparr>(([(x, x')] \<bullet> [(y, y')] \<bullet> P)[<\<sigma>>])) \<sim> \<lparr>\<nu>y'\<rparr>(\<lparr>\<nu>x'\<rparr>(([(x, x')] \<bullet> [(y, y')] \<bullet> P)[<\<sigma>>]))"
      by(rule bisimResComm)
    moreover from \<open>x' \<sharp> P\<close> \<open>y' \<sharp> P\<close> \<open>x \<noteq> y'\<close> \<open>x' \<noteq> y'\<close> have "\<lparr>\<nu>x\<rparr>(\<lparr>\<nu>y\<rparr>P) = \<lparr>\<nu>x'\<rparr>(\<lparr>\<nu>y'\<rparr>(([(x, x')] \<bullet> [(y, y')] \<bullet> P)))"
      apply(subst alphaRes[of y' P], simp)
      by(subst alphaRes[of x']) (auto simp add: abs_fresh fresh_left calc_atm eqvts)
    moreover from \<open>x' \<sharp> P\<close> \<open>y' \<sharp> P\<close> \<open>y \<noteq> x'\<close> \<open>x \<noteq> y'\<close> \<open>x' \<noteq> y'\<close> \<open>x \<noteq> x'\<close> \<open>x \<noteq> y\<close> have "\<lparr>\<nu>y\<rparr>(\<lparr>\<nu>x\<rparr>P) = \<lparr>\<nu>y'\<rparr>(\<lparr>\<nu>x'\<rparr>(([(x, x')] \<bullet> [(y, y')] \<bullet> P)))"
      apply(subst alphaRes[of x' P], simp)
      apply(subst alphaRes[of y'], simp add: abs_fresh fresh_left calc_atm)
      apply(simp add: eqvts calc_atm)
      by(subst perm_compose) (simp add: calc_atm)

    ultimately show "\<Psi> \<rhd> (\<lparr>\<nu>x\<rparr>(\<lparr>\<nu>y\<rparr>P))[<\<sigma>>] \<sim> (\<lparr>\<nu>y\<rparr>(\<lparr>\<nu>x\<rparr>P))[<\<sigma>>]"
      using \<open>wellFormedSubst \<sigma>\<close>  \<open>x' \<sharp> \<sigma>\<close> \<open>y' \<sharp> \<sigma>\<close>
      by simp
  qed
qed

lemma bisimSubstExtBang:
  fixes \<Psi> :: 'b
    and P :: "('a, 'b, 'c) psi"

assumes "guarded P"

shows "\<Psi> \<rhd> !P \<sim>\<^sub>s P \<parallel> !P"
  using assms closeSubstI bangExt guardedSeqSubst by force

lemma structCongBisimSubst:
  fixes P :: "('a, 'b, 'c) psi"
    and Q :: "('a, 'b, 'c) psi"

assumes "P \<equiv>\<^sub>s Q"

shows "P \<sim>\<^sub>s Q"
  using assms
  by(induct rule: structCong.induct)
    (auto intro: bisimSubstReflexive bisimSubstSymmetric bisimSubstTransitive bisimSubstParComm bisimSubstParAssoc bisimSubstParNil bisimSubstResNil bisimSubstResComm bisimSubstScopeExt bisimSubstCasePushRes bisimSubstInputPushRes bisimSubstOutputPushRes bisimSubstExtBang)

end

end
