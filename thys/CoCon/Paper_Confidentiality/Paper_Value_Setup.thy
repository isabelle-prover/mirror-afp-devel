(* The value setup for paper confidentiality *)
theory Paper_Value_Setup
imports Paper_Intro
begin

(* The observed values: *)
consts PID :: paperID

subsection\<open>Preliminaries\<close>

declare updates_commute_paper[simp]

(* two papers equal everywhere but w.r.t. their content: *)
fun eqButC :: "paper \<Rightarrow> paper \<Rightarrow> bool" where
"eqButC (Paper name info ct reviews dis decs )
        (Paper name1 info1 ct1 reviews1 dis1 decs1) =
 (name = name1 \<and> info = info1 \<and> reviews = reviews1 \<and> dis = dis1 \<and> decs = decs1)"

lemma eqButC:
"eqButC pap pap1 =
 (titlePaper pap = titlePaper pap1 \<and> abstractPaper pap = abstractPaper pap1 \<and>
  reviewsPaper pap = reviewsPaper pap1 \<and> disPaper pap = disPaper pap1 \<and> decsPaper pap = decsPaper pap1)"
by(cases pap, cases pap1, auto)

lemma eqButC_eq[simp,intro!]: "eqButC pap pap"
by(cases pap) auto

lemma eqButC_sym:
assumes "eqButC pap pap1"
shows "eqButC pap1 pap"
apply(cases pap, cases pap1)
using assms by auto

lemma eqButC_trans:
assumes "eqButC pap pap1" and "eqButC pap1 pap2"
shows "eqButC pap pap2"
apply(cases pap, cases pap1, cases pap2)
using assms by auto

(* Auxiliary notion: two functions are equal everywhere but on the NIC (content) of
   the value corresponding to PID *)
definition eeqButPID where
"eeqButPID paps paps1 \<equiv>
 \<forall> pid. if pid = PID then eqButC (paps pid) (paps1 pid) else paps pid = paps1 pid"

lemma eeqButPID_eeq[simp,intro!]: "eeqButPID s s"
unfolding eeqButPID_def by auto

lemma eeqButPID_sym:
assumes "eeqButPID s s1" shows "eeqButPID s1 s"
using assms eqButC_sym unfolding eeqButPID_def by auto

lemma eeqButPID_trans:
assumes "eeqButPID s s1" and "eeqButPID s1 s2" shows "eeqButPID s s2"
using assms eqButC_trans unfolding eeqButPID_def by simp blast

lemma eeqButPID_imp:
"eeqButPID paps paps1 \<Longrightarrow> eqButC (paps PID) (paps1 PID)"
"\<lbrakk>eeqButPID paps paps1; pid \<noteq> PID\<rbrakk> \<Longrightarrow> paps pid = paps1 pid"
unfolding eeqButPID_def by auto

lemma eeqButPID_cong:
assumes "eeqButPID paps paps1"
and "pid = PID \<Longrightarrow> eqButC uu uu1"
and "pid \<noteq> PID \<Longrightarrow> uu = uu1"
shows "eeqButPID (paps (pid := uu)) (paps1(pid := uu1))"
using assms unfolding eeqButPID_def by auto

lemma eeqButPID_RDD:
"eeqButPID paps paps1 \<Longrightarrow>
 titlePaper (paps PID) = titlePaper (paps1 PID) \<and>
 abstractPaper (paps PID) = abstractPaper (paps1 PID) \<and>
 reviewsPaper (paps PID) = reviewsPaper (paps1 PID) \<and>
 disPaper (paps PID) = disPaper (paps1 PID) \<and>
 decsPaper (paps PID) = decsPaper (paps1 PID)"
using eeqButPID_def unfolding eqButC by auto

(* The notion of two states being equal everywhere but on the content of
   the paper associated to a given PID *)
definition eqButPID :: "state \<Rightarrow> state \<Rightarrow> bool" where
"eqButPID s s1 \<equiv>
 confIDs s = confIDs s1 \<and> conf s = conf s1 \<and>
 userIDs s = userIDs s1 \<and> pass s = pass s1 \<and> user s = user s1 \<and> roles s = roles s1 \<and>
 paperIDs s = paperIDs s1
 \<and>
 eeqButPID (paper s) (paper s1)
 \<and>
 pref s = pref s1 \<and>
 voronkov s = voronkov s1 \<and>
 news s = news s1 \<and> phase s = phase s1"

lemma eqButPID_eq[simp,intro!]: "eqButPID s s"
unfolding eqButPID_def by auto

lemma eqButPID_sym:
assumes "eqButPID s s1" shows "eqButPID s1 s"
using assms eeqButPID_sym unfolding eqButPID_def by auto

lemma eqButPID_trans:
assumes "eqButPID s s1" and "eqButPID s1 s2" shows "eqButPID s s2"
using assms eeqButPID_trans unfolding eqButPID_def by auto

(* Implications from eqButPID, including w.r.t. auxiliary operations: *)
lemma eqButPID_imp:
"eqButPID s s1 \<Longrightarrow>
 confIDs s = confIDs s1 \<and> conf s = conf s1 \<and>
 userIDs s = userIDs s1 \<and> pass s = pass s1 \<and> user s = user s1 \<and> roles s = roles s1 \<and>
 paperIDs s = paperIDs s1
 \<and>
 eeqButPID (paper s) (paper s1)
 \<and>
 pref s = pref s1 \<and>
 voronkov s = voronkov s1 \<and>
 news s = news s1 \<and> phase s = phase s1 \<and>

 getAllPaperIDs s = getAllPaperIDs s1 \<and>
 isRev s cid uid pid = isRev s1 cid uid pid \<and>
 getReviewIndex s cid uid pid = getReviewIndex s1 cid uid pid \<and>
 getRevRole s cid uid pid = getRevRole s1 cid uid pid "
unfolding eqButPID_def getAllPaperIDs_def
unfolding isRev_def getReviewIndex_def getRevRole_def by auto

lemma eqButPID_imp1:
"eqButPID s s1 \<Longrightarrow> eqButC (paper s pid) (paper s1 pid)"
"eqButPID s s1 \<Longrightarrow> pid \<noteq> PID \<or> PID \<noteq> pid \<Longrightarrow>
    paper s pid = paper s1 pid \<and>
    getNthReview s pid n = getNthReview s1 pid n"
unfolding eqButPID_def getNthReview_def eeqButPID_def
apply auto
by (metis eqButC_eq)

lemma eqButPID_imp2:
assumes "eqButPID s s1" and "pid \<noteq> PID \<or> PID \<noteq> pid"
shows "getReviewersReviews s cid pid = getReviewersReviews s1 cid pid"
proof-
  have
  "(\<lambda>uID. if isRev s cid uID pid then [(uID, getNthReview s pid (getReviewIndex s cid uID pid))] else []) =
   (\<lambda>uID. if isRev s1 cid uID pid then [(uID, getNthReview s1 pid (getReviewIndex s1 cid uID pid))] else [])"
  apply(rule ext)
  using assms by (auto simp: eqButPID_imp eqButPID_imp1)
  thus ?thesis unfolding getReviewersReviews_def using assms by (simp add: eqButPID_imp)
qed

lemma eqButPID_RDD:
"eqButPID s s1 \<Longrightarrow>
 titlePaper (paper s PID) = titlePaper (paper s1 PID) \<and>
 abstractPaper (paper s PID) = abstractPaper (paper s1 PID) \<and>
 reviewsPaper (paper s PID) = reviewsPaper (paper s1 PID) \<and>
 disPaper (paper s PID) = disPaper (paper s1 PID) \<and>
 decsPaper (paper s PID) = decsPaper (paper s1 PID)"
using eqButPID_imp eeqButPID_RDD by auto

lemma eqButPID_cong[simp, intro]:
"\<And> uu1 uu2. eqButPID s s1 \<Longrightarrow> uu1 = uu2 \<Longrightarrow> eqButPID (s \<lparr>confIDs := uu1\<rparr>) (s1 \<lparr>confIDs := uu2\<rparr>)"
"\<And> uu1 uu2. eqButPID s s1 \<Longrightarrow> uu1 = uu2 \<Longrightarrow> eqButPID (s \<lparr>conf := uu1\<rparr>) (s1 \<lparr>conf := uu2\<rparr>)"

"\<And> uu1 uu2. eqButPID s s1 \<Longrightarrow> uu1 = uu2 \<Longrightarrow> eqButPID (s \<lparr>userIDs := uu1\<rparr>) (s1 \<lparr>userIDs := uu2\<rparr>)"
"\<And> uu1 uu2. eqButPID s s1 \<Longrightarrow> uu1 = uu2 \<Longrightarrow> eqButPID (s \<lparr>pass := uu1\<rparr>) (s1 \<lparr>pass := uu2\<rparr>)"
"\<And> uu1 uu2. eqButPID s s1 \<Longrightarrow> uu1 = uu2 \<Longrightarrow> eqButPID (s \<lparr>user := uu1\<rparr>) (s1 \<lparr>user := uu2\<rparr>)"
"\<And> uu1 uu2. eqButPID s s1 \<Longrightarrow> uu1 = uu2 \<Longrightarrow> eqButPID (s \<lparr>roles := uu1\<rparr>) (s1 \<lparr>roles := uu2\<rparr>)"

"\<And> uu1 uu2. eqButPID s s1 \<Longrightarrow> uu1 = uu2 \<Longrightarrow> eqButPID (s \<lparr>paperIDs := uu1\<rparr>) (s1 \<lparr>paperIDs := uu2\<rparr>)"
"\<And> uu1 uu2. eqButPID s s1 \<Longrightarrow> eeqButPID uu1 uu2 \<Longrightarrow> eqButPID (s \<lparr>paper := uu1\<rparr>) (s1 \<lparr>paper := uu2\<rparr>)"

"\<And> uu1 uu2. eqButPID s s1 \<Longrightarrow> uu1 = uu2 \<Longrightarrow> eqButPID (s \<lparr>pref := uu1\<rparr>) (s1 \<lparr>pref := uu2\<rparr>)"
"\<And> uu1 uu2. eqButPID s s1 \<Longrightarrow> uu1 = uu2 \<Longrightarrow> eqButPID (s \<lparr>voronkov := uu1\<rparr>) (s1 \<lparr>voronkov := uu2\<rparr>)"
"\<And> uu1 uu2. eqButPID s s1 \<Longrightarrow> uu1 = uu2 \<Longrightarrow> eqButPID (s \<lparr>news := uu1\<rparr>) (s1 \<lparr>news := uu2\<rparr>)"
"\<And> uu1 uu2. eqButPID s s1 \<Longrightarrow> uu1 = uu2 \<Longrightarrow> eqButPID (s \<lparr>phase := uu1\<rparr>) (s1 \<lparr>phase := uu2\<rparr>)"

unfolding eqButPID_def by auto

lemma eqButPID_Paper:
assumes s's1': "eqButPID s s1"
and "paper s pid = Paper title abstract pc reviews dis decs"
and "paper s1 pid = Paper title1 abstract1 pc1 reviews1 dis1 decs1"
shows "title = title1 \<and> abstract = abstract1 \<and> reviews = reviews1 \<and> dis = dis1 \<and> decs = decs1"
using assms unfolding eqButPID_def apply (auto simp: eqButC eeqButPID_def)
by (metis titlePaper.simps abstractPaper.simps reviewsPaper.simps disPaper.simps decsPaper.simps)+

definition "NOSIMP a \<equiv> a"
lemma [cong]: "NOSIMP a = NOSIMP a" by simp

lemma eqButPID_paper:
  assumes "eqButPID s s1"
  shows "paper s = (paper s1)(PID :=
    Paper (titlePaper (paper s1 PID))
      (abstractPaper (paper s1 PID))
      (contentPaper (NOSIMP (paper s PID)))
      (reviewsPaper (paper s1 PID))
      (disPaper (paper s1 PID))
      (decsPaper (paper s1 PID))
    )"
  apply (rule sym)
  using assms unfolding NOSIMP_def eqButPID_def eeqButPID_def
  apply (intro ext)
  apply simp
  apply (cases "paper s1 PID", simp_all)
  apply (cases "paper s PID", simp_all)
  done

(* lemmas eqButPID_simps = eqButPID_simps1 eqButPID_simps2 eqButPID_paper *)
lemmas eqButPID_simps = eqButPID_imp eqButPID_paper


subsection\<open>Value Setup\<close>

type_synonym "value" = pcontent

fun \<phi> :: "(state,act,out) trans \<Rightarrow> bool" where
"\<phi> (Trans _ (Uact (uPaperC cid uid p pid ct)) ou _) = (pid = PID \<and> ou = outOK)"
|
"\<phi> _ = False"

lemma \<phi>_def2:
"\<phi> (Trans s a ou s') = (\<exists>cid uid p ct. a = Uact (uPaperC cid uid p PID ct) \<and> ou = outOK)"
proof (cases a)
  case (Uact x2)
  then show ?thesis by (cases x2; auto)
qed auto

fun f :: "(state,act,out) trans \<Rightarrow> value" where
"f (Trans _ (Uact (uPaperC cid uid p pid ct)) _ _) = ct"

lemma Uact_uPaperC_step_eqButPID:
assumes a: "a = Uact (uPaperC cid uid p PID ct)"
and "step s a = (ou,s')"
shows "eqButPID s s'"
using assms unfolding eqButPID_def eeqButPID_def by (auto simp: u_defs)

lemma \<phi>_step_eqButPID:
assumes \<phi>: "\<phi> (Trans s a ou s')"
and s: "step s a = (ou,s')"
shows "eqButPID s s'"
using \<phi> Uact_uPaperC_step_eqButPID[OF _ s] unfolding \<phi>_def2 by blast

(* major *) lemma eqButPID_step:
assumes s's1': "eqButPID s s1"
and step: "step s a = (ou,s')"
and step1: "step s1 a = (ou1,s1')"
shows "eqButPID s' s1'"
proof -
  note eqs = eqButPID_imp[OF s's1']
  note eqs' = eqButPID_imp1[OF s's1']

  note simps[simp] = c_defs u_defs uu_defs r_defs l_defs Paper_dest_conv eqButPID_def eeqButPID_def eqButC
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

lemma eqButPID_step_\<phi>_imp:
assumes s's1': "eqButPID s s1"
and step: "step s a = (ou,s')" and step1: "step s1 a = (ou1,s1')"
and \<phi>: "\<phi> (Trans s a ou s')"
shows "\<phi> (Trans s1 a ou1 s1')"
using assms unfolding \<phi>_def2 by (auto simp add: u_defs eqButPID_imp)

lemma eqButPID_step_\<phi>:
assumes s's1': "eqButPID s s1"
and step: "step s a = (ou,s')" and step1: "step s1 a = (ou1,s1')"
shows "\<phi> (Trans s a ou s') = \<phi> (Trans s1 a ou1 s1')"
by (metis eqButPID_step_\<phi>_imp eqButPID_sym assms)


end
