(* The value setup for paper confidentiality *)
theory Decision_Value_Setup2
imports Decision_Value_Setup
begin

section\<open>Preliminaries\<close>

(* two papers equal everywhere but w.r.t. the tail of the decision: *)
fun eqExcD2 :: "paper \<Rightarrow> paper \<Rightarrow> bool" where
"eqExcD2 (Paper title abstract ct reviews dis decs )
         (Paper title1 abstract1 ct1 reviews1 dis1 decs1) =
 (title = title1 \<and> abstract = abstract1 \<and> ct = ct1 \<and> reviews = reviews1 \<and> dis = dis1 \<and>
 hd decs = hd decs1)"

lemma eqExcD2:
"eqExcD2 pap pap1 =
 (titlePaper pap = titlePaper pap1 \<and> abstractPaper pap = abstractPaper pap1 \<and>
  contentPaper pap = contentPaper pap1 \<and>
  reviewsPaper pap = reviewsPaper pap1 \<and> disPaper pap = disPaper pap1 \<and>
  hd (decsPaper pap) = hd (decsPaper pap1)
 )"
by(cases pap, cases pap1, auto)

lemma eqExcD2_eq[simp,intro!]: "eqExcD2 pap pap"
by(cases pap) auto

lemma eqExcD2_sym:
assumes "eqExcD2 pap pap1"
shows "eqExcD2 pap1 pap"
apply(cases pap, cases pap1)
using assms by auto

lemma eqExcD2_trans:
assumes "eqExcD2 pap pap1" and "eqExcD2 pap1 pap2"
shows "eqExcD2 pap pap2"
apply(cases pap, cases pap1, cases pap2)
using assms by auto

(* Auxiliary notion:  *)
definition eeqExcPID2 where
"eeqExcPID2 paps paps1 \<equiv>
 \<forall> pid. if pid = PID then eqExcD2 (paps pid) (paps1 pid) else paps pid = paps1 pid"

lemma eeqExcPID2_eeq[simp,intro!]: "eeqExcPID2 s s"
unfolding eeqExcPID2_def by auto

lemma eeqExcPID2_sym:
assumes "eeqExcPID2 s s1" shows "eeqExcPID2 s1 s"
using assms eqExcD2_sym unfolding eeqExcPID2_def by auto

lemma eeqExcPID2_trans:
assumes "eeqExcPID2 s s1" and "eeqExcPID2 s1 s2" shows "eeqExcPID2 s s2"
using assms eqExcD2_trans unfolding eeqExcPID2_def by simp blast

lemma eeqExcPID2_imp:
"eeqExcPID2 paps paps1 \<Longrightarrow> eqExcD2 (paps PID) (paps1 PID)"
"\<lbrakk>eeqExcPID2 paps paps1; pid \<noteq> PID\<rbrakk> \<Longrightarrow> paps pid = paps1 pid"
unfolding eeqExcPID2_def by auto

lemma eeqExcPID2_cong:
assumes "eeqExcPID2 paps paps1"
and "pid = PID \<Longrightarrow> eqExcD2 uu uu1"
and "pid \<noteq> PID \<Longrightarrow> uu = uu1"
shows "eeqExcPID2 (paps (pid := uu)) (paps1(pid := uu1))"
using assms unfolding eeqExcPID2_def by auto

lemma eeqExcPID2_RDD:
"eeqExcPID2 paps paps1 \<Longrightarrow>
 titlePaper (paps PID) = titlePaper (paps1 PID) \<and>
 abstractPaper (paps PID) = abstractPaper (paps1 PID) \<and>
 contentPaper (paps PID) = contentPaper (paps1 PID) \<and>
 reviewsPaper (paps PID) = reviewsPaper (paps1 PID) \<and>
 disPaper (paps PID) = disPaper (paps1 PID) \<and>
 hd (decsPaper (paps PID)) = hd (decsPaper (paps PID))"
using eeqExcPID2_def unfolding eqExcD2 by auto

(* The notion of two states being equal everywhere but on the tail of the decision of
   the paper associated to a given PID *)
definition eqExcPID2 :: "state \<Rightarrow> state \<Rightarrow> bool" where
"eqExcPID2 s s1 \<equiv>
 confIDs s = confIDs s1 \<and> conf s = conf s1 \<and>
 userIDs s = userIDs s1 \<and> pass s = pass s1 \<and> user s = user s1 \<and> roles s = roles s1 \<and>
 paperIDs s = paperIDs s1
 \<and>
 eeqExcPID2 (paper s) (paper s1)
 \<and>
 pref s = pref s1 \<and>
 voronkov s = voronkov s1 \<and>
 news s = news s1 \<and> phase s = phase s1"

lemma eqExcPID2_eq[simp,intro!]: "eqExcPID2 s s"
unfolding eqExcPID2_def by auto

lemma eqExcPID2_sym:
assumes "eqExcPID2 s s1" shows "eqExcPID2 s1 s"
using assms eeqExcPID2_sym unfolding eqExcPID2_def by auto

lemma eqExcPID2_trans:
assumes "eqExcPID2 s s1" and "eqExcPID2 s1 s2" shows "eqExcPID2 s s2"
using assms eeqExcPID2_trans unfolding eqExcPID2_def by auto

(* Implications from eqExcPID2, including w.r.t. auxiliary operations: *)
lemma eqExcPID2_imp:
"eqExcPID2 s s1 \<Longrightarrow>
 confIDs s = confIDs s1 \<and> conf s = conf s1 \<and>
 userIDs s = userIDs s1 \<and> pass s = pass s1 \<and> user s = user s1 \<and> roles s = roles s1 \<and>
 paperIDs s = paperIDs s1
 \<and>
 eeqExcPID2 (paper s) (paper s1)
 \<and>
 pref s = pref s1 \<and>
 voronkov s = voronkov s1 \<and>
 news s = news s1 \<and> phase s = phase s1 \<and>

 getAllPaperIDs s = getAllPaperIDs s1 \<and>
 isRev s cid uid pid = isRev s1 cid uid pid \<and>
 getReviewIndex s cid uid pid = getReviewIndex s1 cid uid pid \<and>
 getRevRole s cid uid pid = getRevRole s1 cid uid pid"
unfolding eqExcPID2_def getAllPaperIDs_def
unfolding isRev_def getReviewIndex_def getRevRole_def by auto

lemma eqExcPID2_imp1:
"eqExcPID2 s s1 \<Longrightarrow> eqExcD2 (paper s pid) (paper s1 pid)"
"eqExcPID2 s s1 \<Longrightarrow> pid \<noteq> PID \<or> PID \<noteq> pid \<Longrightarrow>
    paper s pid = paper s1 pid \<and>
    getNthReview s pid n = getNthReview s1 pid n"
unfolding eqExcPID2_def getNthReview_def eeqExcPID2_def
apply auto
by (metis eqExcD2_eq)

lemma eqExcPID2_imp2:
assumes "eqExcPID2 s s1" and "pid \<noteq> PID \<or> PID \<noteq> pid"
shows "getReviewersReviews s cid pid = getReviewersReviews s1 cid pid"
proof-
  have
  "(\<lambda>uID. if isRev s cid uID pid then [(uID, getNthReview s pid (getReviewIndex s cid uID pid))] else []) =
   (\<lambda>uID. if isRev s1 cid uID pid then [(uID, getNthReview s1 pid (getReviewIndex s1 cid uID pid))] else [])"
  apply(rule ext)
  using assms by (auto simp: eqExcPID2_imp eqExcPID2_imp1)
  thus ?thesis unfolding getReviewersReviews_def using assms by (simp add: eqExcPID2_imp)
qed

lemma eqExcPID2_RDD:
"eqExcPID2 s s1 \<Longrightarrow>
 titlePaper (paper s PID) = titlePaper (paper s1 PID) \<and>
 abstractPaper (paper s PID) = abstractPaper (paper s1 PID) \<and>
 contentPaper (paper s PID) = contentPaper (paper s1 PID) \<and>
 reviewsPaper (paper s PID) = reviewsPaper (paper s1 PID) \<and>
 disPaper (paper s PID) = disPaper (paper s1 PID)"
using eqExcPID2_imp eeqExcPID2_RDD by auto

lemma eqExcPID2_cong[simp, intro]:
"\<And> uu1 uu2. eqExcPID2 s s1 \<Longrightarrow> uu1 = uu2 \<Longrightarrow> eqExcPID2 (s \<lparr>confIDs := uu1\<rparr>) (s1 \<lparr>confIDs := uu2\<rparr>)"
"\<And> uu1 uu2. eqExcPID2 s s1 \<Longrightarrow> uu1 = uu2 \<Longrightarrow> eqExcPID2 (s \<lparr>conf := uu1\<rparr>) (s1 \<lparr>conf := uu2\<rparr>)"

"\<And> uu1 uu2. eqExcPID2 s s1 \<Longrightarrow> uu1 = uu2 \<Longrightarrow> eqExcPID2 (s \<lparr>userIDs := uu1\<rparr>) (s1 \<lparr>userIDs := uu2\<rparr>)"
"\<And> uu1 uu2. eqExcPID2 s s1 \<Longrightarrow> uu1 = uu2 \<Longrightarrow> eqExcPID2 (s \<lparr>pass := uu1\<rparr>) (s1 \<lparr>pass := uu2\<rparr>)"
"\<And> uu1 uu2. eqExcPID2 s s1 \<Longrightarrow> uu1 = uu2 \<Longrightarrow> eqExcPID2 (s \<lparr>user := uu1\<rparr>) (s1 \<lparr>user := uu2\<rparr>)"
"\<And> uu1 uu2. eqExcPID2 s s1 \<Longrightarrow> uu1 = uu2 \<Longrightarrow> eqExcPID2 (s \<lparr>roles := uu1\<rparr>) (s1 \<lparr>roles := uu2\<rparr>)"

"\<And> uu1 uu2. eqExcPID2 s s1 \<Longrightarrow> uu1 = uu2 \<Longrightarrow> eqExcPID2 (s \<lparr>paperIDs := uu1\<rparr>) (s1 \<lparr>paperIDs := uu2\<rparr>)"
"\<And> uu1 uu2. eqExcPID2 s s1 \<Longrightarrow> eeqExcPID2 uu1 uu2 \<Longrightarrow> eqExcPID2 (s \<lparr>paper := uu1\<rparr>) (s1 \<lparr>paper := uu2\<rparr>)"

"\<And> uu1 uu2. eqExcPID2 s s1 \<Longrightarrow> uu1 = uu2 \<Longrightarrow> eqExcPID2 (s \<lparr>pref := uu1\<rparr>) (s1 \<lparr>pref := uu2\<rparr>)"
"\<And> uu1 uu2. eqExcPID2 s s1 \<Longrightarrow> uu1 = uu2 \<Longrightarrow> eqExcPID2 (s \<lparr>voronkov := uu1\<rparr>) (s1 \<lparr>voronkov := uu2\<rparr>)"
"\<And> uu1 uu2. eqExcPID2 s s1 \<Longrightarrow> uu1 = uu2 \<Longrightarrow> eqExcPID2 (s \<lparr>news := uu1\<rparr>) (s1 \<lparr>news := uu2\<rparr>)"
"\<And> uu1 uu2. eqExcPID2 s s1 \<Longrightarrow> uu1 = uu2 \<Longrightarrow> eqExcPID2 (s \<lparr>phase := uu1\<rparr>) (s1 \<lparr>phase := uu2\<rparr>)"
unfolding eqExcPID2_def by auto

lemma eqExcPID2_Paper:
assumes s's1': "eqExcPID2 s s1"
and "paper s pid = Paper title abstract content reviews dis decs"
and "paper s1 pid = Paper title1 abstract1 content1 reviews1 dis1 decs1"
shows "title = title1 \<and> abstract = abstract1 \<and> content = content1 \<and> reviews = reviews1 \<and>
    dis = dis1"
using assms unfolding eqExcPID2_def apply (auto simp: eqExcD2 eeqExcPID2_def)
  by (metis titlePaper.simps abstractPaper.simps contentPaper.simps reviewsPaper.simps
disPaper.simps)+


section\<open>Value Setup\<close>

(* These hold for eeqExcPID, but not for eeqExcPID2:
lemma UUact_uuDec_step_eqExcPID2:
assumes a: "a = UUact (uuDec cid uid p PID dec)"
and "step s a = (ou,s')"
shows "eqExcPID2 s s'"
using assms unfolding eqExcPID2_def eeqExcPID2_def by (auto simp: uu_defs)

lemma \<phi>_step_eqExcPID2:
assumes \<phi>: "\<phi> (Trans s a ou s')"
and s: "step s a = (ou,s')"
shows "eqExcPID2 s s'"
using \<phi> UUact_uuDec_step_eqExcPID2[OF _ s] unfolding \<phi>_def2 by blast
*)

(* major *) lemma eqExcPID2_step:
assumes s's1': "eqExcPID2 s s1"
and step: "step s a = (ou,s')"
and step1: "step s1 a = (ou1,s1')"
shows "eqExcPID2 s' s1'"
proof -
  note eqs = eqExcPID2_imp[OF s's1']
  note eqs' = eqExcPID2_imp1[OF s's1']

  note simps[simp] = c_defs u_defs uu_defs r_defs l_defs Paper_dest_conv eqExcPID2_def eeqExcPID2_def eqExcD2

  show ?thesis
    using s's1' step step1 eqs eqs'
    apply(cases a, simp_all only:)
      subgoal for x1 apply(cases x1)
        apply auto[] apply auto[] apply auto[] apply auto[]
        apply auto[] apply auto[] apply auto[] apply auto[] .
      subgoal for x2 apply(cases x2)
        apply auto[] apply auto[] apply auto[] apply auto[]
        apply auto[] apply auto[] apply auto[] .
      subgoal for x3 apply(cases x3)
        apply auto[] apply auto[] apply auto[] apply auto[] .
      apply auto
  done
qed

lemma eqExcPID2_step_\<phi>_imp:
assumes s's1': "eqExcPID2 s s1"
and step: "step s a = (ou,s')" and step1: "step s1 a = (ou1,s1')"
and \<phi>: "\<phi> (Trans s a ou s')"
shows "\<phi> (Trans s1 a ou1 s1')"
using assms unfolding \<phi>_def2 by (auto simp add: uu_defs eqExcPID2_imp)

lemma eqExcPID2_step_\<phi>:
assumes s's1': "eqExcPID2 s s1"
and step: "step s a = (ou,s')" and step1: "step s1 a = (ou1,s1')"
shows "\<phi> (Trans s a ou s') = \<phi> (Trans s1 a ou1 s1')"
by (metis eqExcPID2_step_\<phi>_imp eqExcPID2_sym assms)


end