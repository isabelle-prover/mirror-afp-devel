theory Discussion_Value_Setup
imports Discussion_Intro
begin

text \<open>The ID of the paper under scrutiny:\<close>

consts PID :: paperID

subsection \<open>Preliminaries\<close>

declare updates_commute_paper[simp]

(* two papers equal everywhere except w.r.t. discussion: *)
fun eqExcD :: "paper \<Rightarrow> paper \<Rightarrow> bool" where
"eqExcD (Paper title abstract ct reviews dis decs)
        (Paper title1 abstract1 ct1 reviews1 dis1 decs1) =
 (title = title1 \<and> abstract = abstract1 \<and> ct = ct1 \<and> reviews = reviews1 \<and> decs = decs1)"

lemma eqExcD:
"eqExcD pap pap1 =
 (titlePaper pap = titlePaper pap1 \<and> abstractPaper pap = abstractPaper pap1 \<and>
  contentPaper pap = contentPaper pap1 \<and>
  reviewsPaper pap = reviewsPaper pap1 \<and> decsPaper pap = decsPaper pap1)"
by(cases pap, cases pap1, auto)

lemma eqExcD_eq[simp,intro!]: "eqExcD pap pap"
by(cases pap) auto

lemma eqExcD_sym:
assumes "eqExcD pap pap1"
shows "eqExcD pap1 pap"
apply(cases pap, cases pap1)
using assms by auto

lemma eqExcD_trans:
assumes "eqExcD pap pap1" and "eqExcD pap1 pap2"
shows "eqExcD pap pap2"
apply(cases pap, cases pap1, cases pap2)
using assms by auto

(* Auxiliary notion:  *)
definition eeqExcPID where
"eeqExcPID paps paps1 \<equiv>
 \<forall> pid. if pid = PID then eqExcD (paps pid) (paps1 pid) else paps pid = paps1 pid"

lemma eeqExcPID_eeq[simp,intro!]: "eeqExcPID s s"
unfolding eeqExcPID_def by auto

lemma eeqExcPID_sym:
assumes "eeqExcPID s s1" shows "eeqExcPID s1 s"
using assms eqExcD_sym unfolding eeqExcPID_def by auto

lemma eeqExcPID_trans:
assumes "eeqExcPID s s1" and "eeqExcPID s1 s2" shows "eeqExcPID s s2"
using assms eqExcD_trans unfolding eeqExcPID_def by simp blast

lemma eeqExcPID_imp:
"eeqExcPID paps paps1 \<Longrightarrow> eqExcD (paps PID) (paps1 PID)"
"\<lbrakk>eeqExcPID paps paps1; pid \<noteq> PID\<rbrakk> \<Longrightarrow> paps pid = paps1 pid"
unfolding eeqExcPID_def by auto

lemma eeqExcPID_cong:
assumes "eeqExcPID paps paps1"
and "pid = PID \<Longrightarrow> eqExcD uu uu1"
and "pid \<noteq> PID \<Longrightarrow> uu = uu1"
shows "eeqExcPID (paps (pid := uu)) (paps1(pid := uu1))"
using assms unfolding eeqExcPID_def by auto

lemma eeqExcPID_RDD:
"eeqExcPID paps paps1 \<Longrightarrow>
 titlePaper (paps PID) = titlePaper (paps1 PID) \<and>
 abstractPaper (paps PID) = abstractPaper (paps1 PID) \<and>
 contentPaper (paps PID) = contentPaper (paps1 PID) \<and>
 reviewsPaper (paps PID) = reviewsPaper (paps1 PID) \<and>
 decsPaper (paps PID) = decsPaper (paps1 PID)"
using eeqExcPID_def unfolding eqExcD by auto

(* The notion of two states being equal everywhere but on the discussion of
   the paper associated to a given PID *)
definition eqExcPID :: "state \<Rightarrow> state \<Rightarrow> bool" where
"eqExcPID s s1 \<equiv>
 confIDs s = confIDs s1 \<and> conf s = conf s1 \<and>
 userIDs s = userIDs s1 \<and> pass s = pass s1 \<and> user s = user s1 \<and> roles s = roles s1 \<and>
 paperIDs s = paperIDs s1
 \<and>
 eeqExcPID (paper s) (paper s1)
 \<and>
 pref s = pref s1 \<and>
 voronkov s = voronkov s1 \<and>
 news s = news s1 \<and> phase s = phase s1"

lemma eqExcPID_eq[simp,intro!]: "eqExcPID s s"
unfolding eqExcPID_def by auto

lemma eqExcPID_sym:
assumes "eqExcPID s s1" shows "eqExcPID s1 s"
using assms eeqExcPID_sym unfolding eqExcPID_def by auto

lemma eqExcPID_trans:
assumes "eqExcPID s s1" and "eqExcPID s1 s2" shows "eqExcPID s s2"
using assms eeqExcPID_trans unfolding eqExcPID_def by auto

(* Implications from eqExcPID, including w.r.t. auxiliary operations: *)
lemma eqExcPID_imp:
"eqExcPID s s1 \<Longrightarrow>
 confIDs s = confIDs s1 \<and> conf s = conf s1 \<and>
 userIDs s = userIDs s1 \<and> pass s = pass s1 \<and> user s = user s1 \<and> roles s = roles s1 \<and>
 paperIDs s = paperIDs s1
 \<and>
 eeqExcPID (paper s) (paper s1)
 \<and>
 pref s = pref s1 \<and>
 voronkov s = voronkov s1 \<and>
 news s = news s1 \<and> phase s = phase s1 \<and>

 getAllPaperIDs s = getAllPaperIDs s1 \<and>
 isRev s cid uid pid = isRev s1 cid uid pid \<and>
 getReviewIndex s cid uid pid = getReviewIndex s1 cid uid pid \<and>
 getRevRole s cid uid pid = getRevRole s1 cid uid pid"
unfolding eqExcPID_def getAllPaperIDs_def
unfolding isRev_def getReviewIndex_def getRevRole_def by auto

lemma eqExcPID_imp1:
"eqExcPID s s1 \<Longrightarrow> eqExcD (paper s pid) (paper s1 pid)"
"eqExcPID s s1 \<Longrightarrow> pid \<noteq> PID \<or> PID \<noteq> pid \<Longrightarrow>
    paper s pid = paper s1 pid \<and>
    getNthReview s pid n = getNthReview s1 pid n"
unfolding eqExcPID_def getNthReview_def eeqExcPID_def
apply auto
by (metis eqExcD_eq)

lemma eqExcPID_imp2:
assumes "eqExcPID s s1" and "pid \<noteq> PID \<or> PID \<noteq> pid"
shows "getReviewersReviews s cid pid = getReviewersReviews s1 cid pid"
proof-
  have
  "(\<lambda>uID. if isRev s cid uID pid then [(uID, getNthReview s pid (getReviewIndex s cid uID pid))] else []) =
   (\<lambda>uID. if isRev s1 cid uID pid then [(uID, getNthReview s1 pid (getReviewIndex s1 cid uID pid))] else [])"
  apply(rule ext)
  using assms by (auto simp: eqExcPID_imp eqExcPID_imp1)
  thus ?thesis unfolding getReviewersReviews_def using assms by (simp add: eqExcPID_imp)
qed

lemma eqExcPID_RDD:
"eqExcPID s s1 \<Longrightarrow>
 titlePaper (paper s PID) = titlePaper (paper s1 PID) \<and>
 abstractPaper (paper s PID) = abstractPaper (paper s1 PID) \<and>
 contentPaper (paper s PID) = contentPaper (paper s1 PID) \<and>
 reviewsPaper (paper s PID) = reviewsPaper (paper s1 PID) \<and>
 decsPaper (paper s PID) = decsPaper (paper s1 PID)"
using eqExcPID_imp eeqExcPID_RDD by auto

lemma eqExcPID_cong[simp, intro]:
"\<And> uu1 uu2. eqExcPID s s1 \<Longrightarrow> uu1 = uu2 \<Longrightarrow> eqExcPID (s \<lparr>confIDs := uu1\<rparr>) (s1 \<lparr>confIDs := uu2\<rparr>)"
"\<And> uu1 uu2. eqExcPID s s1 \<Longrightarrow> uu1 = uu2 \<Longrightarrow> eqExcPID (s \<lparr>conf := uu1\<rparr>) (s1 \<lparr>conf := uu2\<rparr>)"

"\<And> uu1 uu2. eqExcPID s s1 \<Longrightarrow> uu1 = uu2 \<Longrightarrow> eqExcPID (s \<lparr>userIDs := uu1\<rparr>) (s1 \<lparr>userIDs := uu2\<rparr>)"
"\<And> uu1 uu2. eqExcPID s s1 \<Longrightarrow> uu1 = uu2 \<Longrightarrow> eqExcPID (s \<lparr>pass := uu1\<rparr>) (s1 \<lparr>pass := uu2\<rparr>)"
"\<And> uu1 uu2. eqExcPID s s1 \<Longrightarrow> uu1 = uu2 \<Longrightarrow> eqExcPID (s \<lparr>user := uu1\<rparr>) (s1 \<lparr>user := uu2\<rparr>)"
"\<And> uu1 uu2. eqExcPID s s1 \<Longrightarrow> uu1 = uu2 \<Longrightarrow> eqExcPID (s \<lparr>roles := uu1\<rparr>) (s1 \<lparr>roles := uu2\<rparr>)"

"\<And> uu1 uu2. eqExcPID s s1 \<Longrightarrow> uu1 = uu2 \<Longrightarrow> eqExcPID (s \<lparr>paperIDs := uu1\<rparr>) (s1 \<lparr>paperIDs := uu2\<rparr>)"
"\<And> uu1 uu2. eqExcPID s s1 \<Longrightarrow> eeqExcPID uu1 uu2 \<Longrightarrow> eqExcPID (s \<lparr>paper := uu1\<rparr>) (s1 \<lparr>paper := uu2\<rparr>)"

"\<And> uu1 uu2. eqExcPID s s1 \<Longrightarrow> uu1 = uu2 \<Longrightarrow> eqExcPID (s \<lparr>pref := uu1\<rparr>) (s1 \<lparr>pref := uu2\<rparr>)"
"\<And> uu1 uu2. eqExcPID s s1 \<Longrightarrow> uu1 = uu2 \<Longrightarrow> eqExcPID (s \<lparr>voronkov := uu1\<rparr>) (s1 \<lparr>voronkov := uu2\<rparr>)"
"\<And> uu1 uu2. eqExcPID s s1 \<Longrightarrow> uu1 = uu2 \<Longrightarrow> eqExcPID (s \<lparr>news := uu1\<rparr>) (s1 \<lparr>news := uu2\<rparr>)"
"\<And> uu1 uu2. eqExcPID s s1 \<Longrightarrow> uu1 = uu2 \<Longrightarrow> eqExcPID (s \<lparr>phase := uu1\<rparr>) (s1 \<lparr>phase := uu2\<rparr>)"
unfolding eqExcPID_def by auto

lemma eqExcPID_Paper:
assumes s's1': "eqExcPID s s1"
and "paper s pid = Paper title abstract content reviews dis decs"
and "paper s1 pid = Paper title1 abstract1 content1 reviews1 dis1 decs1"
shows "title = title1 \<and> abstract = abstract1 \<and> content = content1 \<and> reviews = reviews1 \<and> decs = decs1 "
using assms unfolding eqExcPID_def apply (auto simp: eqExcD eeqExcPID_def)
by (metis titlePaper.simps abstractPaper.simps contentPaper.simps reviewsPaper.simps decsPaper.simps
         )+


subsection \<open>Value Setup\<close>

type_synonym "value" = string

fun \<phi> :: "(state,act,out) trans \<Rightarrow> bool" where
"\<phi> (Trans _ (UUact (uuDis cid uid p pid com)) ou _) = (pid = PID \<and> ou = outOK)"
|
"\<phi> _ = False"

lemma \<phi>_def2:
"\<phi> (Trans s a ou s') = (\<exists> cid uid p com. a = UUact (uuDis cid uid p PID com) \<and> ou = outOK)"
proof (cases a)
  case (UUact x3)
  then show ?thesis by (cases x3; auto)
qed auto

fun f :: "(state,act,out) trans \<Rightarrow> value" where
"f (Trans _ (UUact (uuDis cid uid p pid com)) _ _) = com"

lemma UUact_uuDis_step_eqExcPID:
assumes a: "a = UUact (uuDis cid uid p PID com)"
and "step s a = (ou,s')"
shows "eqExcPID s s'"
using assms unfolding eqExcPID_def eeqExcPID_def by (auto simp: uu_defs)

lemma \<phi>_step_eqExcPID:
assumes \<phi>: "\<phi> (Trans s a ou s')"
and s: "step s a = (ou,s')"
shows "eqExcPID s s'"
using \<phi> UUact_uuDis_step_eqExcPID[OF _ s] unfolding \<phi>_def2 by blast

(* major *) lemma eqExcPID_step:
assumes s's1': "eqExcPID s s1"
and step: "step s a = (ou,s')"
and step1: "step s1 a = (ou1,s1')"
shows "eqExcPID s' s1'"
proof -
  note eqs = eqExcPID_imp[OF s's1']
  note eqs' = eqExcPID_imp1[OF s's1']
  note simps[simp] = c_defs u_defs uu_defs r_defs l_defs Paper_dest_conv eqExcPID_def eeqExcPID_def eqExcD
  note * = step step1 eqs eqs'

  then show ?thesis
  proof (cases a)
    case (Cact x1)
    then show ?thesis using * by (cases x1; auto)
  next
    case (Uact x2)
    then show ?thesis using * by (cases x2; auto)
  next
    case (UUact x3)
    then show ?thesis using * by (cases x3; auto)
  qed auto
qed

lemma eqExcPID_step_\<phi>_imp:
assumes s's1': "eqExcPID s s1"
and step: "step s a = (ou,s')" and step1: "step s1 a = (ou1,s1')"
and \<phi>: "\<phi> (Trans s a ou s')"
shows "\<phi> (Trans s1 a ou1 s1')"
using assms unfolding \<phi>_def2 by (auto simp add: uu_defs eqExcPID_imp)

lemma eqExcPID_step_\<phi>:
assumes s's1': "eqExcPID s s1"
and step: "step s a = (ou,s')" and step1: "step s1 a = (ou1,s1')"
shows "\<phi> (Trans s a ou s') = \<phi> (Trans s1 a ou1 s1')"
by (metis eqExcPID_step_\<phi>_imp eqExcPID_sym assms)


end
