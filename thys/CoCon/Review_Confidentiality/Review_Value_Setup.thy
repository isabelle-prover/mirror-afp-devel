(* The value setup for reviewer confidentiality *)
theory Review_Value_Setup
imports Review_Intro
begin

consts PID :: paperID  consts N :: nat

text \<open>\<^term>\<open>(PID,N)\<close> identifies uniquely the review under scrutiny\<close>

subsection \<open>Preliminaries\<close>

declare updates_commute_paper[simp]

text \<open>Auxiliary definitions:\<close>

definition eqExcNth where
"eqExcNth xs ys n \<equiv>
 length xs = length ys \<and> (\<forall> i < length xs. i \<noteq> n \<longrightarrow> xs!i = ys!i)"

lemma eqExcNth_eq[simp,intro!]: "eqExcNth xs xs n"
unfolding eqExcNth_def by auto

lemma eqExcNth_sym:
assumes "eqExcNth xs xs1 n"
shows "eqExcNth xs1 xs n"
using assms unfolding eqExcNth_def by auto

lemma eqExcNth_trans:
assumes "eqExcNth xs xs1 n" and "eqExcNth xs1 xs2 n"
shows "eqExcNth xs xs2 n"
using assms unfolding eqExcNth_def by auto

fun eqExcD :: "paper \<Rightarrow> paper \<Rightarrow> bool" where
"eqExcD (Paper name info ct reviews dis decs)
        (Paper name1 info1 ct1 reviews1 dis1 decs1) =
 (name = name1 \<and> info = info1 \<and> ct = ct1 \<and> dis = dis1 \<and> decs = decs1 \<and>
  eqExcNth reviews reviews1 N)"

lemma eqExcD:
"eqExcD pap pap1 =
 (titlePaper pap = titlePaper pap1 \<and> abstractPaper pap = abstractPaper pap1 \<and>
  contentPaper pap = contentPaper pap1 \<and>
  disPaper pap = disPaper pap1 \<and> decsPaper pap = decsPaper pap1 \<and>
  eqExcNth (reviewsPaper pap) (reviewsPaper pap1) N)"
by(cases pap, cases pap1, auto)

lemma eqExcD_eq[simp,intro!]: "eqExcD pap pap"
unfolding eqExcD using eqExcNth_eq by auto


lemma eqExcD_sym:
assumes "eqExcD pap pap1"
shows "eqExcD pap1 pap"
using assms unfolding eqExcD using eqExcNth_sym by auto

lemma eqExcD_trans:
assumes "eqExcD pap pap1" and "eqExcD pap1 pap2"
shows "eqExcD pap pap2"
using assms unfolding eqExcD using eqExcNth_trans by auto

definition eeqExcPID_N where
"eeqExcPID_N paps paps1 \<equiv>
 \<forall> pid. if pid = PID then eqExcD (paps pid) (paps1 pid) else paps pid = paps1 pid"

lemma eeqExcPID_N_eeq[simp,intro!]: "eeqExcPID_N s s"
unfolding eeqExcPID_N_def by auto

lemma eeqExcPID_N_sym:
assumes "eeqExcPID_N s s1" shows "eeqExcPID_N s1 s"
using assms eqExcD_sym unfolding eeqExcPID_N_def by auto

lemma eeqExcPID_N_trans:
assumes "eeqExcPID_N s s1" and "eeqExcPID_N s1 s2" shows "eeqExcPID_N s s2"
using assms eqExcD_trans unfolding eeqExcPID_N_def by simp blast

lemma eeqExcPID_N_imp:
"eeqExcPID_N paps paps1 \<Longrightarrow> eqExcD (paps PID) (paps1 PID)"
"\<lbrakk>eeqExcPID_N paps paps1; pid \<noteq> PID\<rbrakk> \<Longrightarrow> paps pid = paps1 pid"
unfolding eeqExcPID_N_def by auto

lemma eeqExcPID_N_cong:
assumes "eeqExcPID_N paps paps1"
and "pid = PID \<Longrightarrow> eqExcD uu uu1"
and "pid \<noteq> PID \<Longrightarrow> uu = uu1"
shows "eeqExcPID_N (paps (pid := uu)) (paps1(pid := uu1))"
using assms unfolding eeqExcPID_N_def by auto

lemma eeqExcPID_N_RDD:
"eeqExcPID_N paps paps1 \<Longrightarrow>
 titlePaper (paps PID) = titlePaper (paps1 PID) \<and>
 abstractPaper (paps PID) = abstractPaper (paps1 PID) \<and>
 contentPaper (paps PID) = contentPaper (paps1 PID) \<and>
 disPaper (paps PID) = disPaper (paps1 PID) \<and>
 decsPaper (paps PID) = decsPaper (paps1 PID)"
using eeqExcPID_N_def unfolding eqExcD by auto

text \<open>The notion of two states being equal everywhere except on the the review \<^term>\<open>(N,PID)\<close>:\<close>

definition eqExcPID_N :: "state \<Rightarrow> state \<Rightarrow> bool" where
"eqExcPID_N s s1 \<equiv>
 confIDs s = confIDs s1 \<and> conf s = conf s1 \<and>
 userIDs s = userIDs s1 \<and> pass s = pass s1 \<and> user s = user s1 \<and> roles s = roles s1 \<and>
 paperIDs s = paperIDs s1
 \<and>
 eeqExcPID_N (paper s) (paper s1)
 \<and>
 pref s = pref s1 \<and>
 voronkov s = voronkov s1 \<and>
 news s = news s1 \<and> phase s = phase s1"

lemma eqExcPID_N_eq[simp,intro!]: "eqExcPID_N s s"
unfolding eqExcPID_N_def by auto

lemma eqExcPID_N_sym:
assumes "eqExcPID_N s s1" shows "eqExcPID_N s1 s"
using assms eeqExcPID_N_sym unfolding eqExcPID_N_def by auto

lemma eqExcPID_N_trans:
assumes "eqExcPID_N s s1" and "eqExcPID_N s1 s2" shows "eqExcPID_N s s2"
using assms eeqExcPID_N_trans unfolding eqExcPID_N_def by auto

text \<open>Implications from \<^term>\<open>eqExcPID_N\<close>, including w.r.t. auxiliary operations:\<close>

lemma eqExcPID_N_imp:
"eqExcPID_N s s1 \<Longrightarrow>
 confIDs s = confIDs s1 \<and> conf s = conf s1 \<and>
 userIDs s = userIDs s1 \<and> pass s = pass s1 \<and> user s = user s1 \<and> roles s = roles s1 \<and>
 paperIDs s = paperIDs s1
 \<and>
 eeqExcPID_N (paper s) (paper s1)
 \<and>
 pref s = pref s1 \<and>
 voronkov s = voronkov s1 \<and>
 news s = news s1 \<and> phase s = phase s1 \<and>

 getAllPaperIDs s = getAllPaperIDs s1 \<and>
 isRev s cid uid pid = isRev s1 cid uid pid \<and>
 getReviewIndex s cid uid pid = getReviewIndex s1 cid uid pid \<and>
 getRevRole s cid uid pid = getRevRole s1 cid uid pid \<and>
 length (reviewsPaper (paper s pid)) = length (reviewsPaper (paper s1 pid))"
unfolding eqExcPID_N_def getAllPaperIDs_def
unfolding isRev_def getReviewIndex_def getRevRole_def apply auto
unfolding eeqExcPID_N_def eqExcD eqExcNth_def by (cases "pid = PID") auto

lemma eqExcPID_N_imp1:
"eqExcPID_N s s1 \<Longrightarrow> eqExcD (paper s pid) (paper s1 pid)"
"eqExcPID_N s s1 \<Longrightarrow> pid \<noteq> PID \<or> PID \<noteq> pid \<Longrightarrow>
    paper s pid = paper s1 pid \<and>
    getNthReview s pid n = getNthReview s1 pid n"
unfolding eqExcPID_N_def eeqExcPID_N_def getNthReview_def
apply auto by (metis eqExcD_eq)

lemma eqExcPID_N_imp2:
assumes "eqExcPID_N s s1" and "pid \<noteq> PID \<or> PID \<noteq> pid"
shows "getReviewersReviews s cid pid = getReviewersReviews s1 cid pid"
proof-
  have
  "(\<lambda>uID. if isRev s cid uID pid then [(uID, getNthReview s pid (getReviewIndex s cid uID pid))] else []) =
   (\<lambda>uID. if isRev s1 cid uID pid then [(uID, getNthReview s1 pid (getReviewIndex s1 cid uID pid))] else [])"
  apply(rule ext)
  using assms by (auto simp: eqExcPID_N_imp eqExcPID_N_imp1)
  thus ?thesis unfolding getReviewersReviews_def using assms by (simp add: eqExcPID_N_imp)
qed

lemma eqExcPID_N_imp3:
"eqExcPID_N s s1 \<Longrightarrow> pid \<noteq> PID \<or> PID \<noteq> pid \<or> (n < length (reviewsPaper (paper s PID)) \<and> n \<noteq> N)
 \<Longrightarrow>
 getNthReview s pid n = getNthReview s1 pid n"
  unfolding eqExcPID_N_def
  apply auto
   apply (metis eeqExcPID_N_imp(2) getNthReview_def)
  unfolding eeqExcPID_N_def apply simp unfolding eqExcD eqExcNth_def
  by (metis getNthReview_def)


lemma eqExcPID_N_imp3':
assumes s: "reach s"
and "eqExcPID_N s s1" and "pid \<noteq> PID \<or> (isRevNth s cid uid pid n \<and> n \<noteq> N)"
shows "getNthReview s pid n = getNthReview s1 pid n"
proof-
  have "isRevNth s cid uid pid n \<Longrightarrow> pid \<noteq> PID \<or> n < length (reviewsPaper (paper s PID))"
  using s by (metis isRevNth_less_length)
  thus ?thesis using eqExcPID_N_imp3 assms by auto
qed

lemma eqExcPID_N_RDD:
"eqExcPID_N s s1 \<Longrightarrow>
 titlePaper (paper s PID) = titlePaper (paper s1 PID) \<and>
 abstractPaper (paper s PID) = abstractPaper (paper s1 PID) \<and>
 contentPaper (paper s PID) = contentPaper (paper s1 PID) \<and>
 disPaper (paper s PID) = disPaper (paper s1 PID) \<and>
 decsPaper (paper s PID) = decsPaper (paper s1 PID)"
using eqExcPID_N_imp eeqExcPID_N_RDD by auto

lemma eqExcPID_N_cong[simp, intro]:
"\<And> uu1 uu2. eqExcPID_N s s1 \<Longrightarrow> uu1 = uu2 \<Longrightarrow> eqExcPID_N (s \<lparr>confIDs := uu1\<rparr>) (s1 \<lparr>confIDs := uu2\<rparr>)"
"\<And> uu1 uu2. eqExcPID_N s s1 \<Longrightarrow> uu1 = uu2 \<Longrightarrow> eqExcPID_N (s \<lparr>conf := uu1\<rparr>) (s1 \<lparr>conf := uu2\<rparr>)"

"\<And> uu1 uu2. eqExcPID_N s s1 \<Longrightarrow> uu1 = uu2 \<Longrightarrow> eqExcPID_N (s \<lparr>userIDs := uu1\<rparr>) (s1 \<lparr>userIDs := uu2\<rparr>)"
"\<And> uu1 uu2. eqExcPID_N s s1 \<Longrightarrow> uu1 = uu2 \<Longrightarrow> eqExcPID_N (s \<lparr>pass := uu1\<rparr>) (s1 \<lparr>pass := uu2\<rparr>)"
"\<And> uu1 uu2. eqExcPID_N s s1 \<Longrightarrow> uu1 = uu2 \<Longrightarrow> eqExcPID_N (s \<lparr>user := uu1\<rparr>) (s1 \<lparr>user := uu2\<rparr>)"
"\<And> uu1 uu2. eqExcPID_N s s1 \<Longrightarrow> uu1 = uu2 \<Longrightarrow> eqExcPID_N (s \<lparr>roles := uu1\<rparr>) (s1 \<lparr>roles := uu2\<rparr>)"

"\<And> uu1 uu2. eqExcPID_N s s1 \<Longrightarrow> uu1 = uu2 \<Longrightarrow> eqExcPID_N (s \<lparr>paperIDs := uu1\<rparr>) (s1 \<lparr>paperIDs := uu2\<rparr>)"
"\<And> uu1 uu2. eqExcPID_N s s1 \<Longrightarrow> eeqExcPID_N uu1 uu2 \<Longrightarrow> eqExcPID_N (s \<lparr>paper := uu1\<rparr>) (s1 \<lparr>paper := uu2\<rparr>)"

"\<And> uu1 uu2. eqExcPID_N s s1 \<Longrightarrow> uu1 = uu2 \<Longrightarrow> eqExcPID_N (s \<lparr>pref := uu1\<rparr>) (s1 \<lparr>pref := uu2\<rparr>)"
"\<And> uu1 uu2. eqExcPID_N s s1 \<Longrightarrow> uu1 = uu2 \<Longrightarrow> eqExcPID_N (s \<lparr>voronkov := uu1\<rparr>) (s1 \<lparr>voronkov := uu2\<rparr>)"
"\<And> uu1 uu2. eqExcPID_N s s1 \<Longrightarrow> uu1 = uu2 \<Longrightarrow> eqExcPID_N (s \<lparr>news := uu1\<rparr>) (s1 \<lparr>news := uu2\<rparr>)"
"\<And> uu1 uu2. eqExcPID_N s s1 \<Longrightarrow> uu1 = uu2 \<Longrightarrow> eqExcPID_N (s \<lparr>phase := uu1\<rparr>) (s1 \<lparr>phase := uu2\<rparr>)"

unfolding eqExcPID_N_def by auto

lemma eqExcPID_N_Paper:
assumes s's1': "eqExcPID_N s s1"
and "paper s pid = Paper title abstract content reviews dis decs"
and "paper s1 pid = Paper title1 abstract1 content1 reviews1 dis1 decs1"
shows "title = title1 \<and> abstract = abstract1 \<and> content = content1 \<and> dis = dis1 \<and> decs = decs1"
using assms unfolding eqExcPID_N_def apply (auto simp: eqExcD eeqExcPID_N_def)
by (metis titlePaper.simps abstractPaper.simps contentPaper.simps disPaper.simps decsPaper.simps)+

text \<open>Auxiliary definitions for a slightly weaker equivalence relation defined below:\<close>

definition eqExcNth2 where
"eqExcNth2 rl rl1 n \<equiv>
 length rl = length rl1 \<and>
 (\<forall> i < length rl. i \<noteq> n \<longrightarrow> rl!i = rl1!i) \<and>
 hd (rl!n) = hd (rl1!n)"

lemma eqExcNth2_eq[simp,intro!]: "eqExcNth2 rl rl n"
unfolding eqExcNth2_def by auto

lemma eqExcNth2_sym:
assumes "eqExcNth2 rl rl1 n"
shows "eqExcNth2 rl1 rl n"
using assms unfolding eqExcNth2_def by auto

lemma eqExcNth2_trans:
assumes "eqExcNth2 rl rl1 n" and "eqExcNth2 rl1 rl2 n"
shows "eqExcNth2 rl rl2 n"
using assms unfolding eqExcNth2_def by auto

fun eqExcD2 :: "paper \<Rightarrow> paper \<Rightarrow> bool" where
"eqExcD2 (Paper title abstract ct reviews dis decs)
         (Paper title1 abstract1 ct1 reviews1 dis1 decs1) =
 (title = title1 \<and> abstract = abstract1 \<and> ct = ct1 \<and> dis = dis1 \<and> decs = decs1 \<and>
  eqExcNth2 reviews reviews1 N)"

lemma eqExcD2:
"eqExcD2 pap pap1 =
 (titlePaper pap = titlePaper pap1 \<and> abstractPaper pap = abstractPaper pap1 \<and>
  contentPaper pap = contentPaper pap1 \<and>
  disPaper pap = disPaper pap1 \<and> decsPaper pap = decsPaper pap1 \<and>
  eqExcNth2 (reviewsPaper pap) (reviewsPaper pap1) N)"
by(cases pap, cases pap1, auto)

lemma eqExcD2_eq[simp,intro!]: "eqExcD2 pap pap"
unfolding eqExcD2 using eqExcNth2_eq by auto

lemma eqExcD2_sym:
assumes "eqExcD2 pap pap1"
shows "eqExcD2 pap1 pap"
using assms unfolding eqExcD2 using eqExcNth2_sym by auto

lemma eqExcD2_trans:
assumes "eqExcD2 pap pap1" and "eqExcD2 pap1 pap2"
shows "eqExcD2 pap pap2"
using assms unfolding eqExcD2 using eqExcNth2_trans by auto

definition eeqExcPID_N2 where
"eeqExcPID_N2 paps paps1 \<equiv>
 \<forall> pid. if pid = PID then eqExcD2 (paps pid) (paps1 pid) else paps pid = paps1 pid"

lemma eeqExcPID_N2_eeq[simp,intro!]: "eeqExcPID_N2 s s"
unfolding eeqExcPID_N2_def by auto

lemma eeqExcPID_N2_sym:
assumes "eeqExcPID_N2 s s1" shows "eeqExcPID_N2 s1 s"
using assms eqExcD2_sym unfolding eeqExcPID_N2_def by auto

lemma eeqExcPID_N2_trans:
assumes "eeqExcPID_N2 s s1" and "eeqExcPID_N2 s1 s2" shows "eeqExcPID_N2 s s2"
using assms eqExcD2_trans unfolding eeqExcPID_N2_def by simp blast

lemma eeqExcPID_N2_imp:
"eeqExcPID_N2 paps paps1 \<Longrightarrow> eqExcD2 (paps PID) (paps1 PID)"
"\<lbrakk>eeqExcPID_N2 paps paps1; pid \<noteq> PID\<rbrakk> \<Longrightarrow> paps pid = paps1 pid"
unfolding eeqExcPID_N2_def by auto

lemma eeqExcPID_N2_cong:
assumes "eeqExcPID_N2 paps paps1"
and "pid = PID \<Longrightarrow> eqExcD2 uu uu1"
and "pid \<noteq> PID \<Longrightarrow> uu = uu1"
shows "eeqExcPID_N2 (paps (pid := uu)) (paps1(pid := uu1))"
using assms unfolding eeqExcPID_N2_def by auto

lemma eeqExcPID_N2_RDD:
"eeqExcPID_N2 paps paps1 \<Longrightarrow>
 titlePaper (paps PID) = titlePaper (paps1 PID) \<and>
 abstractPaper (paps PID) = abstractPaper (paps1 PID) \<and>
 contentPaper (paps PID) = contentPaper (paps1 PID) \<and>
 disPaper (paps PID) = disPaper (paps1 PID) \<and>
 decsPaper (paps PID) = decsPaper (paps1 PID)"
using eeqExcPID_N2_def unfolding eqExcD2 by auto

text \<open>A weaker state equivalence that allows differences in old versions of the score and comments
of the review \<^term>\<open>(N, PID)\<close>.  It is used for the confidentiality property that does not cover
PC members in the discussion phase, when they will learn about scores and comments.\<close>

definition eqExcPID_N2 :: "state \<Rightarrow> state \<Rightarrow> bool" where
"eqExcPID_N2 s s1 \<equiv>
 confIDs s = confIDs s1 \<and> conf s = conf s1 \<and>
 userIDs s = userIDs s1 \<and> pass s = pass s1 \<and> user s = user s1 \<and> roles s = roles s1 \<and>
 paperIDs s = paperIDs s1
 \<and>
 eeqExcPID_N2 (paper s) (paper s1)
 \<and>
 pref s = pref s1 \<and>
 voronkov s = voronkov s1 \<and>
 news s = news s1 \<and> phase s = phase s1"

lemma eqExcPID_N2_eq[simp,intro!]: "eqExcPID_N2 s s"
unfolding eqExcPID_N2_def by auto

lemma eqExcPID_N2_sym:
assumes "eqExcPID_N2 s s1" shows "eqExcPID_N2 s1 s"
using assms eeqExcPID_N2_sym unfolding eqExcPID_N2_def by auto

lemma eqExcPID_N2_trans:
assumes "eqExcPID_N2 s s1" and "eqExcPID_N2 s1 s2" shows "eqExcPID_N2 s s2"
using assms eeqExcPID_N2_trans unfolding eqExcPID_N2_def by auto

text \<open>Implications from \<^term>\<open>eqExcPID_N2\<close>, including w.r.t. auxiliary operations:\<close>

lemma eqExcPID_N2_imp:
"eqExcPID_N2 s s1 \<Longrightarrow>
 confIDs s = confIDs s1 \<and> conf s = conf s1 \<and>
 userIDs s = userIDs s1 \<and> pass s = pass s1 \<and> user s = user s1 \<and> roles s = roles s1 \<and>
 paperIDs s = paperIDs s1
 \<and>
 eeqExcPID_N2 (paper s) (paper s1)
 \<and>
 pref s = pref s1 \<and>
 voronkov s = voronkov s1 \<and>
 news s = news s1 \<and> phase s = phase s1 \<and>

 getAllPaperIDs s = getAllPaperIDs s1 \<and>
 isRev s cid uid pid = isRev s1 cid uid pid \<and>
 getReviewIndex s cid uid pid = getReviewIndex s1 cid uid pid \<and>
 getRevRole s cid uid pid = getRevRole s1 cid uid pid \<and>
 length (reviewsPaper (paper s pid)) = length (reviewsPaper (paper s1 pid))"
unfolding eqExcPID_N2_def getAllPaperIDs_def
unfolding isRev_def getReviewIndex_def getRevRole_def apply auto
unfolding eeqExcPID_N2_def eqExcD2 eqExcNth2_def by simp metis

lemma eqExcPID_N2_imp1:
"eqExcPID_N2 s s1 \<Longrightarrow> eqExcD2 (paper s pid) (paper s1 pid)"
"eqExcPID_N2 s s1 \<Longrightarrow> pid \<noteq> PID \<or> PID \<noteq> pid \<Longrightarrow>
    paper s pid = paper s1 pid \<and>
    getNthReview s pid n = getNthReview s1 pid n"
unfolding eqExcPID_N2_def getNthReview_def eeqExcPID_N2_def
apply auto
by (metis eqExcD2_eq)

lemma eqExcPID_N2_imp2:
assumes "eqExcPID_N2 s s1" and "pid \<noteq> PID \<or> PID \<noteq> pid"
shows "getReviewersReviews s cid pid = getReviewersReviews s1 cid pid"
proof-
  have
  "(\<lambda>uID. if isRev s cid uID pid then [(uID, getNthReview s pid (getReviewIndex s cid uID pid))] else []) =
   (\<lambda>uID. if isRev s1 cid uID pid then [(uID, getNthReview s1 pid (getReviewIndex s1 cid uID pid))] else [])"
  apply(rule ext)
  using assms by (auto simp: eqExcPID_N2_imp eqExcPID_N2_imp1)
  thus ?thesis unfolding getReviewersReviews_def using assms by (simp add: eqExcPID_N2_imp)
qed

lemma eqExcPID_N2_eqExcPID_N:
"eqExcPID_N2 s s1 \<Longrightarrow> eqExcPID_N s s1"
unfolding eqExcPID_N_def eqExcPID_N2_def eeqExcPID_N_def eeqExcPID_N2_def eqExcD2 eqExcD
by (auto simp: eqExcNth_def eqExcNth2_def)

lemma eqExcPID_N2_imp3:
"eqExcPID_N2 s s1 \<Longrightarrow> pid \<noteq> PID \<or> PID \<noteq> pid \<or> (n < length (reviewsPaper (paper s PID)) \<and> n \<noteq> N)
 \<Longrightarrow>
 getNthReview s pid n = getNthReview s1 pid n"
by (metis eqExcPID_N2_eqExcPID_N eqExcPID_N_imp3)

lemma eqExcPID_N2_imp3':
assumes s: "reach s"
and "eqExcPID_N2 s s1" and "pid \<noteq> PID \<or> (isRevNth s cid uid pid n \<and> n \<noteq> N)"
shows "getNthReview s pid n = getNthReview s1 pid n"
by (metis assms eqExcPID_N2_eqExcPID_N eqExcPID_N_imp3')

lemma eqExcPID_N2_imp33:
assumes "eqExcPID_N2 s s1"
shows "hd (getNthReview s pid N) = hd (getNthReview s1 pid N)"
proof(cases "pid = PID")
  case False thus ?thesis using eqExcPID_N2_imp3[OF assms] by auto
next
  case True thus ?thesis apply simp
  using assms unfolding eqExcPID_N2_def eeqExcPID_N2_def eqExcD2 eqExcNth2_def getNthReview_def by auto
qed


lemma eqExcPID_N2_RDD:
"eqExcPID_N2 s s1 \<Longrightarrow>
 titlePaper (paper s PID) = titlePaper (paper s1 PID) \<and>
 abstractPaper (paper s PID) = abstractPaper (paper s1 PID) \<and>
 contentPaper (paper s PID) = contentPaper (paper s1 PID) \<and>
 disPaper (paper s PID) = disPaper (paper s1 PID) \<and>
 decsPaper (paper s PID) = decsPaper (paper s1 PID)"
using eqExcPID_N2_imp eeqExcPID_N2_RDD by auto

lemma eqExcPID_N2_cong[simp, intro]:
"\<And> uu1 uu2. eqExcPID_N2 s s1 \<Longrightarrow> uu1 = uu2 \<Longrightarrow> eqExcPID_N2 (s \<lparr>confIDs := uu1\<rparr>) (s1 \<lparr>confIDs := uu2\<rparr>)"
"\<And> uu1 uu2. eqExcPID_N2 s s1 \<Longrightarrow> uu1 = uu2 \<Longrightarrow> eqExcPID_N2 (s \<lparr>conf := uu1\<rparr>) (s1 \<lparr>conf := uu2\<rparr>)"

"\<And> uu1 uu2. eqExcPID_N2 s s1 \<Longrightarrow> uu1 = uu2 \<Longrightarrow> eqExcPID_N2 (s \<lparr>userIDs := uu1\<rparr>) (s1 \<lparr>userIDs := uu2\<rparr>)"
"\<And> uu1 uu2. eqExcPID_N2 s s1 \<Longrightarrow> uu1 = uu2 \<Longrightarrow> eqExcPID_N2 (s \<lparr>pass := uu1\<rparr>) (s1 \<lparr>pass := uu2\<rparr>)"
"\<And> uu1 uu2. eqExcPID_N2 s s1 \<Longrightarrow> uu1 = uu2 \<Longrightarrow> eqExcPID_N2 (s \<lparr>user := uu1\<rparr>) (s1 \<lparr>user := uu2\<rparr>)"
"\<And> uu1 uu2. eqExcPID_N2 s s1 \<Longrightarrow> uu1 = uu2 \<Longrightarrow> eqExcPID_N2 (s \<lparr>roles := uu1\<rparr>) (s1 \<lparr>roles := uu2\<rparr>)"

"\<And> uu1 uu2. eqExcPID_N2 s s1 \<Longrightarrow> uu1 = uu2 \<Longrightarrow> eqExcPID_N2 (s \<lparr>paperIDs := uu1\<rparr>) (s1 \<lparr>paperIDs := uu2\<rparr>)"
"\<And> uu1 uu2. eqExcPID_N2 s s1 \<Longrightarrow> eeqExcPID_N2 uu1 uu2 \<Longrightarrow> eqExcPID_N2 (s \<lparr>paper := uu1\<rparr>) (s1 \<lparr>paper := uu2\<rparr>)"

"\<And> uu1 uu2. eqExcPID_N2 s s1 \<Longrightarrow> uu1 = uu2 \<Longrightarrow> eqExcPID_N2 (s \<lparr>pref := uu1\<rparr>) (s1 \<lparr>pref := uu2\<rparr>)"
"\<And> uu1 uu2. eqExcPID_N2 s s1 \<Longrightarrow> uu1 = uu2 \<Longrightarrow> eqExcPID_N2 (s \<lparr>voronkov := uu1\<rparr>) (s1 \<lparr>voronkov := uu2\<rparr>)"
"\<And> uu1 uu2. eqExcPID_N2 s s1 \<Longrightarrow> uu1 = uu2 \<Longrightarrow> eqExcPID_N2 (s \<lparr>news := uu1\<rparr>) (s1 \<lparr>news := uu2\<rparr>)"
"\<And> uu1 uu2. eqExcPID_N2 s s1 \<Longrightarrow> uu1 = uu2 \<Longrightarrow> eqExcPID_N2 (s \<lparr>phase := uu1\<rparr>) (s1 \<lparr>phase := uu2\<rparr>)"

unfolding eqExcPID_N2_def by auto

lemma eqExcPID_N2_Paper:
assumes s's1': "eqExcPID_N2 s s1"
and "paper s pid = Paper title abstract content reviews dis decs"
and "paper s1 pid = Paper title1 abstract1 content1 reviews1 dis1 decs1"
shows "title = title1 \<and> abstract = abstract1 \<and> content = content1 \<and> dis = dis1 \<and> decs = decs1"
using assms unfolding eqExcPID_N2_def apply (auto simp: eqExcD2 eeqExcPID_N2_def)
by (metis titlePaper.simps abstractPaper.simps contentPaper.simps disPaper.simps decsPaper.simps)+


(* major *) lemma eqExcPID_N2_step:
assumes ss1: "eqExcPID_N2 s s1"
and step: "step s a = (ou,s')"
and step1: "step s1 a = (ou1,s1')"
and s: "reach s" and r: "isRevNth s cid uid PID N" (* new *)
shows "eqExcPID_N2 s' s1'"
proof -
  note eqs = eqExcPID_N2_imp[OF ss1]
  note eqs' = eqExcPID_N2_imp1[OF ss1]
  have r: "N < length (reviewsPaper (paper s PID))" using s r by (metis isRevNth_less_length)
  have r1: "N < length (reviewsPaper (paper s1 PID))"
  using r eqs unfolding eeqExcPID_N2_def eqExcD2 eqExcNth2_def by simp

  note simps[simp] = c_defs u_defs uu_defs r_defs l_defs Paper_dest_conv eqExcPID_N2_def eeqExcPID_N2_def eqExcD2 eqExcNth2_def
  note * = step step1 eqs eqs' r r1

  then show ?thesis
  proof (cases a)
    case (Cact x1)
    with * show ?thesis
    proof (cases x1)
      case (cReview x81 x82 x83 x84 x85)
      with Cact * show ?thesis
        by (clarsimp; metis (no_types, lifting) less_SucE nth_append_length right_cons_left)
    qed auto
  next
    case (Uact x2)
    with * show ?thesis
    proof (cases x2)
      case (uReview x71 x72 x73 x74 x75 x76)
      with Uact * show ?thesis
        by (clarsimp; metis (no_types, lifting) nth_list_update nth_list_update_neq)
    qed auto
  next
    case (UUact x3)
    with * show ?thesis
    proof (cases x3)
      case (uuReview x31 x32 x33 x34 x35 x36)
      with UUact * show ?thesis
        by (clarsimp; smt list.sel(1) nth_list_update nth_list_update_neq)
    qed auto
  qed auto
qed


subsection \<open>Value Setup\<close>

fun \<phi> :: "(state,act,out) trans \<Rightarrow> bool" where
"\<phi> (Trans _ (Uact (uReview cid uid p pid n rc)) ou _) =
 (pid = PID \<and> n = N \<and> ou = outOK)"
|
"\<phi> (Trans _ (UUact (uuReview cid uid p pid n rc)) ou _) =
 (pid = PID \<and> n = N \<and> ou = outOK)"
|
"\<phi> _ = False"

lemma \<phi>_def2:
"\<phi> (Trans s a ou s') =
 (ou = outOK \<and>
 (\<exists> cid uid p rc.
     a = Uact (uReview cid uid p PID N rc)
     \<or>
    a = UUact (uuReview cid uid p PID N rc)
 ))"
  apply(cases a)
  subgoal by simp
  subgoal for x2 apply (cases x2, auto) .
  subgoal for x3  apply(cases x3, auto) .
  by simp_all

lemma uReview_uuReview_step_eqExcPID_N:
assumes a:
"a = Uact (uReview cid uid p PID N rc) \<or>
 a = UUact (uuReview cid uid p PID N rc)"
and "step s a = (ou,s')"
shows "eqExcPID_N s s'"
using assms unfolding eqExcPID_N_def eeqExcPID_N_def by (auto simp: u_defs uu_defs eqExcNth_def)

lemma \<phi>_step_eqExcPID_N:
assumes \<phi>: "\<phi> (Trans s a ou s')"
and s: "step s a = (ou,s')"
shows "eqExcPID_N s s'"
using \<phi> uReview_uuReview_step_eqExcPID_N[OF _ s] unfolding \<phi>_def2 by blast

(* major *) lemma eqExcPID_N_step:
assumes s's1': "eqExcPID_N s s1"
and step: "step s a = (ou,s')"
and step1: "step s1 a = (ou1,s1')"
shows "eqExcPID_N s' s1'"
proof -
  note eqs = eqExcPID_N_imp[OF s's1']
  note eqs' = eqExcPID_N_imp1[OF s's1']

  note simps[simp] = c_defs u_defs uu_defs r_defs l_defs Paper_dest_conv eqExcPID_N_def eeqExcPID_N_def eqExcD eqExcNth_def
  note * = step step1 eqs eqs'

  then show ?thesis
  proof (cases a)
    case (Cact x1)
    with * show ?thesis
    proof (cases x1)
      case (cReview x81 x82 x83 x84 x85)
      with Cact * show ?thesis
        by (clarsimp; metis (no_types, lifting) less_SucE nth_append_length right_cons_left)
    qed auto
  next
    case (Uact x2)
    with * show ?thesis
    proof (cases x2)
      case (uReview x71 x72 x73 x74 x75 x76)
      with Uact * show ?thesis
        by (clarsimp; metis (no_types, lifting) nth_list_update nth_list_update_neq)
    qed auto
  next
    case (UUact x3)
    with * show ?thesis
    proof (cases x3)
      case (uuReview x31 x32 x33 x34 x35 x36)
      with UUact * show ?thesis
        by (clarsimp; metis (no_types, lifting) nth_list_update nth_list_update_neq)
    qed auto
  qed auto
qed

lemma eqExcPID_N_step_\<phi>_imp:
assumes ss1: "eqExcPID_N s s1"
and step: "step s a = (ou,s')" and step1: "step s1 a = (ou1,s1')"
and \<phi>: "\<phi> (Trans s a ou s')"
shows "\<phi> (Trans s1 a ou1 s1')"
using assms unfolding \<phi>_def2 by (auto simp add: u_defs uu_defs eqExcPID_N_imp)

lemma eqExcPID_N_step_\<phi>:
assumes s's1': "eqExcPID_N s s1"
and step: "step s a = (ou,s')" and step1: "step s1 a = (ou1,s1')"
shows "\<phi> (Trans s a ou s') = \<phi> (Trans s1 a ou1 s1')"
by (metis eqExcPID_N_step_\<phi>_imp eqExcPID_N_sym assms)

lemma eqExcPID_N2_step_\<phi>_imp:
assumes ss1: "eqExcPID_N2 s s1"
and step: "step s a = (ou,s')" and step1: "step s1 a = (ou1,s1')"
and r: "N < length (reviewsPaper (paper s PID))" (* new *)
and \<phi>: "\<phi> (Trans s a ou s')"
shows "\<phi> (Trans s1 a ou1 s1')"
using assms unfolding \<phi>_def2 by (auto simp add: u_defs uu_defs eqExcPID_N2_imp)

(* More complex, roundabout proof than for other types of documents: *)
lemma eqExcPID_N2_step_\<phi>:
assumes s: "reach s" and s1: "reach s1"
and ss1: "eqExcPID_N2 s s1"
and step: "step s a = (ou,s')" and step1: "step s1 a = (ou1,s1')"
shows "\<phi> (Trans s a ou s') = \<phi> (Trans s1 a ou1 s1')"
proof(cases "\<exists> cid uid. isRevNth s cid uid PID N")
  case False
  hence "\<not> \<phi> (Trans s a ou s')" unfolding \<phi>_def2 using step
  by (auto simp add: u_defs uu_defs) (metis isRev_imp_isRevNth_getReviewIndex)+
  moreover have "\<not> \<phi> (Trans s1 a ou1 s1')" using step1 False unfolding \<phi>_def2
  by (auto simp add: u_defs uu_defs) (metis eqExcPID_N2_def isRev_imp_isRevNth_getReviewIndex ss1)+
  ultimately show ?thesis by auto
next
  case True note r = True
  note eqs = eqExcPID_N2_imp[OF ss1]
  have r: "N < length (reviewsPaper (paper s PID))"
  using isRevNth_less_length[OF s] r by auto
  have r1: "N < length (reviewsPaper (paper s1 PID))"
  using eqs r unfolding eeqExcPID_N2_def eqExcD2 eqExcNth2_def by simp
  thus ?thesis by (metis eqExcPID_N2_step_\<phi>_imp eqExcPID_N2_sym assms r)
qed

end
