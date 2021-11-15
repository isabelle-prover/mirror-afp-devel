(* The value setup for reviewer confidentiality *)
theory Reviewer_Assignment_Value_Setup
  imports Reviewer_Assignment_Intro
begin


subsection \<open>Preliminaries\<close>

declare updates_commute_paper[simp]

consts PID :: paperID

(* Equality of two role lists everywhere except on their PID reviewer roles *)
definition eqExcRLR :: "role list \<Rightarrow> role list \<Rightarrow> bool" where
"eqExcRLR rl rl1 \<equiv> [r \<leftarrow> rl . \<not> isRevRoleFor PID r] = [r \<leftarrow> rl1 . \<not> isRevRoleFor PID r]"

lemma eqExcRLR_set:
assumes 1: "eqExcRLR rl rl1" and 2: "\<not> isRevRoleFor PID r"
shows "r \<in>\<in> rl \<longleftrightarrow> r \<in>\<in> rl1"
proof-
  have "set ([r\<leftarrow>rl . \<not> isRevRoleFor PID r]) = set ([r\<leftarrow>rl1 . \<not> isRevRoleFor PID r])"
  using 1 unfolding eqExcRLR_def by auto
  thus ?thesis using 2 unfolding set_filter by auto
qed

lemmas eqExcRLR = eqExcRLR_def

lemma eqExcRLR_eq[simp,intro!]: "eqExcRLR rl rl"
unfolding eqExcRLR by auto

lemma eqExcRLR_sym:
assumes "eqExcRLR rl rl1"
shows "eqExcRLR rl1 rl"
using assms unfolding eqExcRLR by auto

lemma eqExcRLR_trans:
assumes "eqExcRLR rl rl1" and "eqExcRLR rl1 rl2"
shows "eqExcRLR rl rl2"
using assms unfolding eqExcRLR by auto

lemma eqExcRLR_imp:
assumes s: "reach s" and pid: "pid \<noteq> PID" and
1: "eqExcRLR (roles s cid uid) (roles s1 cid uid)"
shows
"isRevNth s cid uid pid = isRevNth s1 cid uid pid \<and>
 isRev s cid uid pid = isRev s1 cid uid pid \<and>
 getRevRole s cid uid pid = getRevRole s1 cid uid pid \<and>
 getReviewIndex s cid uid pid = getReviewIndex s1 cid uid pid" (is "?A \<and> ?B \<and> ?C \<and> ?D")
proof(intro conjI)
  show A: ?A
    apply(rule ext)
    using 1 by (metis eqExcRLR_set isRevRoleFor.simps(1) pid)
  show B: ?B using A unfolding isRev_def2 by auto
  show C: ?C
    apply(cases "isRev s cid uid pid")
    subgoal by (metis A B getRevRole_Some_Rev_isRevNth isRevNth_equals isRev_getRevRole2 s)
    by (metis B Bex_set_list_ex find_None_iff getRevRole_def isRev_def)
  show D: ?D unfolding getReviewIndex_def using C by auto
qed

lemma eqExcRLR_imp2:
assumes "eqExcRLR (roles s cid uid) (roles s1 cid uid)"
shows
"isPC s cid uid = isPC s1 cid uid \<and>
 isChair s cid uid = isChair s1 cid uid \<and>
 isAut s cid uid = isAut s1 cid uid"
by (metis (opaque_lifting, no_types) assms eqExcRLR_set isRevRoleFor.simps)

(* fixme: move where belong *)
lemma filter_eq_imp:
assumes "\<And> x. P x \<Longrightarrow> Q x"
and "filter Q xs = filter Q ys"
shows "filter P xs = filter P ys"
using assms filter_filter
proof-
  have "filter P xs = filter P (filter Q xs)"
  unfolding filter_filter using assms by metis
  also have "... = filter P (filter Q ys)" using assms by simp
  also have "... = filter P ys" unfolding filter_filter using assms by metis
  finally show ?thesis .
qed

lemma arg_cong3: "a = a1 \<Longrightarrow> b = b1 \<Longrightarrow> c = c1 \<Longrightarrow> h a b c = h a1 b1 c1"
by auto

lemmas map_concat_cong1 = arg_cong[where f = concat, OF arg_cong2[where f = map, OF _ refl]]
lemmas If_cong1 = arg_cong3[where h = If, OF _ refl refl]

lemma diff_cong1: "a = a1 \<Longrightarrow> (a \<noteq> b) = (a1 \<noteq> b)" by auto

lemma isRev_pref_notConflict:
assumes "reach s" and "isRev s cid uid pid"
shows "pref s uid pid \<noteq> Conflict"
by (metis assms pref_Conflict_isRev)

lemma isRev_pref_notConflict_isPC:
assumes "reach s" and "isRev s cid uid pid"
shows "pref s uid pid \<noteq> Conflict \<and> isPC s cid uid"
by (metis assms(1) assms(2) isRev_isPC isRev_pref_notConflict)

lemma eqExcRLR_imp_isRevRole_imp:
assumes "eqExcRLR rl rl1"
shows "[r\<leftarrow> rl. \<not> isRevRole r] = [r\<leftarrow> rl1 . \<not> isRevRole r]"
using assms filter_eq_imp unfolding eqExcRLR_def
by (metis isRevRole.simps(1) isRevRoleFor.elims(2))

lemma notIsPC_eqExLRL_roles_eq:
assumes s: "reach s" and s1: "reach s1" and PID: "PID \<in>\<in> paperIDs s cid"
and pc: "\<not> isPC s cid uid"
and eq: "eqExcRLR (roles s cid uid) (roles (s1::state) cid uid)"
shows "roles s cid uid = roles s1 cid uid"
proof-
  have "\<not> isPC s1 cid uid" using pc eqExcRLR_imp2[OF eq] by auto
  hence "\<not> isRev s cid uid PID \<and> \<not> isRev s1 cid uid PID" using pc s s1 PID
  by (metis isRev_pref_notConflict_isPC)
  thus ?thesis using eq unfolding eqExcRLR_def
  by (metis Bex_set_list_ex filter_id_conv isRev_def)
qed

lemma foo1: "P a \<Longrightarrow> [r\<leftarrow>List.insert a l . P r] = (if a\<in>set l then filter P l else a#filter P l)"
  by (metis filter.simps(2) in_set_insert not_in_set_insert)

lemma foo2: "\<lbrakk>eqExcRLR rl rl'; \<not> isRevRoleFor PID x\<rbrakk> \<Longrightarrow> eqExcRLR (List.insert x rl) (List.insert x rl')"
  unfolding eqExcRLR_def
  apply (auto simp: foo1) []
  apply (metis eqExcRLR_def eqExcRLR_set isRevRoleFor.simps)+
  done

lemma foo3:
  assumes "eqExcRLR rl rl'" "isRevRoleFor PID x"
  shows "eqExcRLR (List.insert x rl) (rl')"
  and "eqExcRLR (rl) (List.insert x rl')"
  using assms
  unfolding eqExcRLR_def
  by (auto simp: List.insert_def)


text \<open>The notion of two states being equal everywhere except on the reviewer roles for PID:\<close>

definition eqExcPID :: "state \<Rightarrow> state \<Rightarrow> bool" where
"eqExcPID s s1 \<equiv>
 confIDs s = confIDs s1 \<and> conf s = conf s1 \<and>
 userIDs s = userIDs s1 \<and> pass s = pass s1 \<and> user s = user s1
 \<and>
 (\<forall> cid uid. eqExcRLR (roles s cid uid) (roles s1 cid uid))
 \<and>
 paperIDs s = paperIDs s1
 \<and>
 paper s = paper s1
 \<and>
 pref s = pref s1 \<and>
 voronkov s = voronkov s1 \<and>
 news s = news s1 \<and> phase s = phase s1"

lemma eqExcPID_eq[simp,intro!]: "eqExcPID s s"
unfolding eqExcPID_def by auto

lemma eqExcPID_sym:
assumes "eqExcPID s s1" shows "eqExcPID s1 s"
using assms eqExcRLR_sym unfolding eqExcPID_def by auto

lemma eqExcPID_trans:
assumes "eqExcPID s s1" and "eqExcPID s1 s2" shows "eqExcPID s s2"
using assms eqExcRLR_trans unfolding eqExcPID_def by metis

(* Implications from eqExcPID, including w.r.t. auxiliary operations: *)
lemma eqExcPID_imp:
"eqExcPID s s1 \<Longrightarrow>
 confIDs s = confIDs s1 \<and> conf s = conf s1 \<and>
 userIDs s = userIDs s1 \<and> pass s = pass s1 \<and> user s = user s1
 \<and>
 eqExcRLR (roles s cid uid) (roles s1 cid uid)
 \<and>
 paperIDs s = paperIDs s1
 \<and>
 paper s = paper s1
 \<and>
 pref s = pref s1 \<and>
 voronkov s = voronkov s1 \<and>
 news s = news s1 \<and> phase s = phase s1 \<and>
 getAllPaperIDs s = getAllPaperIDs s1"
unfolding eqExcPID_def eqExcRLR_def getAllPaperIDs_def by auto

(* does not work well with simp: *)
lemma eqExcPID_imp':
assumes s: "reach s" and ss1: "eqExcPID s s1" and pid: "pid \<noteq> PID \<or> PID \<noteq> pid"
shows
"isRev s cid uid pid = isRev s1 cid uid pid \<and>
 getRevRole s cid uid pid = getRevRole s1 cid uid pid \<and>
 getReviewIndex s cid uid pid = getReviewIndex s1 cid uid pid"
proof-
  have 1: "eqExcRLR (roles s cid uid) (roles s1 cid uid)"
  using eqExcPID_imp[OF ss1] by auto
  show ?thesis proof (intro conjI)
    show 3: "isRev s cid uid pid = isRev s1 cid uid pid"
    by (metis "1" eqExcRLR_imp pid s)
    show 4: "getRevRole s cid uid pid = getRevRole s1 cid uid pid"
    by (metis "1" eqExcRLR_imp pid s)
    show "getReviewIndex s cid uid pid = getReviewIndex s1 cid uid pid"
    unfolding getReviewIndex_def using 4 by auto
  qed
qed

lemma eqExcPID_imp1:
"eqExcPID s s1 \<Longrightarrow> pid \<noteq> PID \<or> PID \<noteq> pid \<Longrightarrow>
    getNthReview s pid n = getNthReview s1 pid n"
unfolding eqExcPID_def getNthReview_def
by auto

lemma eqExcPID_imp2:
assumes "reach s" and "eqExcPID s s1" and "pid \<noteq> PID \<or> PID \<noteq> pid"
shows "getReviewersReviews s cid pid = getReviewersReviews s1 cid pid"
proof-
  have
  "(\<lambda>uID. if isRev s cid uID pid then [(uID, getNthReview s pid (getReviewIndex s cid uID pid))] else []) =
   (\<lambda>uID. if isRev s1 cid uID pid then [(uID, getNthReview s1 pid (getReviewIndex s1 cid uID pid))] else [])"
  apply(rule ext)
  using assms using assms by (auto simp add: eqExcPID_imp' eqExcPID_imp1)
  thus ?thesis unfolding getReviewersReviews_def using assms by (simp add: eqExcPID_imp)
qed

lemma eqExcPID_imp3:
"reach s \<Longrightarrow> eqExcPID s s1 \<Longrightarrow> pid \<noteq> PID \<or> PID \<noteq> pid
 \<Longrightarrow>
 getNthReview s pid = getNthReview s1 pid"
unfolding eqExcPID_def apply auto
apply (rule ext) by (metis getNthReview_def)

lemma eqExcPID_cong[simp, intro]:
"\<And> uu1 uu2. eqExcPID s s1 \<Longrightarrow> uu1 = uu2 \<Longrightarrow> eqExcPID (s \<lparr>confIDs := uu1\<rparr>) (s1 \<lparr>confIDs := uu2\<rparr>)"
"\<And> uu1 uu2. eqExcPID s s1 \<Longrightarrow> uu1 = uu2 \<Longrightarrow> eqExcPID (s \<lparr>conf := uu1\<rparr>) (s1 \<lparr>conf := uu2\<rparr>)"

"\<And> uu1 uu2. eqExcPID s s1 \<Longrightarrow> uu1 = uu2 \<Longrightarrow> eqExcPID (s \<lparr>userIDs := uu1\<rparr>) (s1 \<lparr>userIDs := uu2\<rparr>)"
"\<And> uu1 uu2. eqExcPID s s1 \<Longrightarrow> uu1 = uu2 \<Longrightarrow> eqExcPID (s \<lparr>pass := uu1\<rparr>) (s1 \<lparr>pass := uu2\<rparr>)"
"\<And> uu1 uu2. eqExcPID s s1 \<Longrightarrow> uu1 = uu2 \<Longrightarrow> eqExcPID (s \<lparr>user := uu1\<rparr>) (s1 \<lparr>user := uu2\<rparr>)"
"\<And> uu1 uu2. eqExcPID s s1 \<Longrightarrow> uu1 = uu2 \<Longrightarrow> eqExcPID (s \<lparr>roles := uu1\<rparr>) (s1 \<lparr>roles := uu2\<rparr>)"

"\<And> uu1 uu2. eqExcPID s s1 \<Longrightarrow> uu1 = uu2 \<Longrightarrow> eqExcPID (s \<lparr>paperIDs := uu1\<rparr>) (s1 \<lparr>paperIDs := uu2\<rparr>)"
"\<And> uu1 uu2. eqExcPID s s1 \<Longrightarrow> uu1 = uu2 \<Longrightarrow> eqExcPID (s \<lparr>paper := uu1\<rparr>) (s1 \<lparr>paper := uu2\<rparr>)"

"\<And> uu1 uu2. eqExcPID s s1 \<Longrightarrow> uu1 = uu2 \<Longrightarrow> eqExcPID (s \<lparr>pref := uu1\<rparr>) (s1 \<lparr>pref := uu2\<rparr>)"
"\<And> uu1 uu2. eqExcPID s s1 \<Longrightarrow> uu1 = uu2 \<Longrightarrow> eqExcPID (s \<lparr>voronkov := uu1\<rparr>) (s1 \<lparr>voronkov := uu2\<rparr>)"
"\<And> uu1 uu2. eqExcPID s s1 \<Longrightarrow> uu1 = uu2 \<Longrightarrow> eqExcPID (s \<lparr>news := uu1\<rparr>) (s1 \<lparr>news := uu2\<rparr>)"
"\<And> uu1 uu2. eqExcPID s s1 \<Longrightarrow> uu1 = uu2 \<Longrightarrow> eqExcPID (s \<lparr>phase := uu1\<rparr>) (s1 \<lparr>phase := uu2\<rparr>)"

unfolding eqExcPID_def by auto

text \<open>A slightly weaker state equivalence that allows differences in the reviews of paper \<^term>\<open>PID\<close>.
It is used for the confidentiality property that doesn't cover the authors of that paper in the
notification phase (when the authors will learn the contents of the reviews).\<close>

(* Equality of two papers everywhere except on their reviews *)
fun eqExcR :: "paper \<Rightarrow> paper \<Rightarrow> bool" where
"eqExcR (Paper name info ct reviews dis decs)
        (Paper name1 info1 ct1 reviews1 dis1 decs1) =
 (name = name1 \<and> info = info1 \<and> ct = ct1 \<and> dis = dis1 \<and> decs = decs1)"

lemma eqExcR:
"eqExcR pap pap1 =
 (titlePaper pap = titlePaper pap1 \<and> abstractPaper pap = abstractPaper pap1 \<and>
  contentPaper pap = contentPaper pap1 \<and>
  disPaper pap = disPaper pap1 \<and> decsPaper pap = decsPaper pap1)"
by(cases pap, cases pap1, auto)

lemma eqExcR_eq[simp,intro!]: "eqExcR pap pap"
unfolding eqExcR by auto

lemma eqExcR_sym:
assumes "eqExcR pap pap1"
shows "eqExcR pap1 pap"
using assms unfolding eqExcR by auto

lemma eqExcR_trans:
assumes "eqExcR pap pap1" and "eqExcR pap1 pap2"
shows "eqExcR pap pap2"
using assms unfolding eqExcR by auto

(* Auxiliary notion:  *)
definition eeqExcPID where
"eeqExcPID paps paps1 \<equiv>
 \<forall> pid. if pid = PID then eqExcR (paps pid) (paps1 pid) else paps pid = paps1 pid"

lemma eeqExcPID_eeq[simp,intro!]: "eeqExcPID s s"
unfolding eeqExcPID_def by auto

lemma eeqExcPID_sym:
assumes "eeqExcPID s s1" shows "eeqExcPID s1 s"
using assms eqExcR_sym unfolding eeqExcPID_def by auto

lemma eeqExcPID_trans:
assumes "eeqExcPID s s1" and "eeqExcPID s1 s2" shows "eeqExcPID s s2"
using assms eqExcR_trans unfolding eeqExcPID_def by simp blast

lemma eeqExcPID_imp:
"eeqExcPID paps paps1 \<Longrightarrow> eqExcR (paps PID) (paps1 PID)"
"\<lbrakk>eeqExcPID paps paps1; pid \<noteq> PID\<rbrakk> \<Longrightarrow> paps pid = paps1 pid"
unfolding eeqExcPID_def by auto

lemma eeqExcPID_cong:
assumes "eeqExcPID paps paps1"
and "pid = PID \<Longrightarrow> eqExcR uu uu1"
and "pid \<noteq> PID \<Longrightarrow> uu = uu1"
shows "eeqExcPID (paps (pid := uu)) (paps1(pid := uu1))"
using assms unfolding eeqExcPID_def by auto

lemma eeqExcPID_RDD:
"eeqExcPID paps paps1 \<Longrightarrow>
 titlePaper (paps PID) = titlePaper (paps1 PID) \<and>
 abstractPaper (paps PID) = abstractPaper (paps1 PID) \<and>
 contentPaper (paps PID) = contentPaper (paps1 PID) \<and>
 disPaper (paps PID) = disPaper (paps1 PID) \<and>
 decsPaper (paps PID) = decsPaper (paps1 PID)"
using eeqExcPID_def unfolding eqExcR by auto

(* The notion of two states being equal everywhere except on the the reviews of PID
   and on the reviewer roles for PID *)
definition eqExcPID2 :: "state \<Rightarrow> state \<Rightarrow> bool" where
"eqExcPID2 s s1 \<equiv>
 confIDs s = confIDs s1 \<and> conf s = conf s1 \<and>
 userIDs s = userIDs s1 \<and> pass s = pass s1 \<and> user s = user s1
 \<and>
 (\<forall> cid uid. eqExcRLR (roles s cid uid) (roles s1 cid uid))
 \<and>
 paperIDs s = paperIDs s1
 \<and>
 eeqExcPID (paper s) (paper s1)
 \<and>
 pref s = pref s1 \<and>
 voronkov s = voronkov s1 \<and>
 news s = news s1 \<and> phase s = phase s1"

lemma eqExcPID2_eq[simp,intro!]: "eqExcPID2 s s"
unfolding eqExcPID2_def by auto

lemma eqExcPID2_sym:
assumes "eqExcPID2 s s1" shows "eqExcPID2 s1 s"
using assms eeqExcPID_sym eqExcRLR_sym unfolding eqExcPID2_def by auto

lemma eqExcPID2_trans:
assumes "eqExcPID2 s s1" and "eqExcPID2 s1 s2" shows "eqExcPID2 s s2"
using assms eeqExcPID_trans eqExcRLR_trans unfolding eqExcPID2_def by metis

(* Implications from eqExcPID2, including w.r.t. auxiliary operations: *)
lemma eqExcPID2_imp:
"eqExcPID2 s s1 \<Longrightarrow>
 confIDs s = confIDs s1 \<and> conf s = conf s1 \<and>
 userIDs s = userIDs s1 \<and> pass s = pass s1 \<and> user s = user s1
 \<and>
 eqExcRLR (roles s cid uid) (roles s1 cid uid)
 \<and>
 paperIDs s = paperIDs s1
 \<and>
 eeqExcPID (paper s) (paper s1)
 \<and>
 pref s = pref s1 \<and>
 voronkov s = voronkov s1 \<and>
 news s = news s1 \<and> phase s = phase s1 \<and>

 getAllPaperIDs s = getAllPaperIDs s1"
unfolding eqExcPID2_def eqExcRLR_def getAllPaperIDs_def by auto


lemma eeqExcPID_imp2:
assumes pid: "pid \<noteq> PID" and
1: "eeqExcPID (paper s) (paper s1)"
shows
"reviewsPaper (paper s pid) = reviewsPaper (paper s1 pid)"
by (metis "1" eeqExcPID_imp(2) pid)

(* does not work well with simp: *)
lemma eqExcPID2_imp':
assumes s: "reach s" and ss1: "eqExcPID2 s s1" and pid: "pid \<noteq> PID \<or> PID \<noteq> pid"
shows
"isRev s cid uid pid = isRev s1 cid uid pid \<and>
 getRevRole s cid uid pid = getRevRole s1 cid uid pid \<and>
 getReviewIndex s cid uid pid = getReviewIndex s1 cid uid pid \<and>
 reviewsPaper (paper s pid) = reviewsPaper (paper s1 pid)"
proof-
  have 1: "eqExcRLR (roles s cid uid) (roles s1 cid uid)"
  and 2: "eeqExcPID (paper s) (paper s1)"
  using eqExcPID2_imp[OF ss1] by auto
  show ?thesis proof (intro conjI)
    show 3: "isRev s cid uid pid = isRev s1 cid uid pid"
    by (metis "1" eqExcRLR_imp pid s)
    show 4: "getRevRole s cid uid pid = getRevRole s1 cid uid pid"
    by (metis "1" eqExcRLR_imp pid s)
    show "getReviewIndex s cid uid pid = getReviewIndex s1 cid uid pid"
    unfolding getReviewIndex_def using 4 by auto
    show "reviewsPaper (paper s pid) = reviewsPaper (paper s1 pid)"
    using pid 2 unfolding eeqExcPID_def by auto
  qed
qed

lemma eqExcPID2_imp1:
"eqExcPID2 s s1 \<Longrightarrow> eqExcR (paper s pid) (paper s1 pid)"
"eqExcPID2 s s1 \<Longrightarrow> pid \<noteq> PID \<or> PID \<noteq> pid \<Longrightarrow>
    paper s pid = paper s1 pid \<and>
    getNthReview s pid n = getNthReview s1 pid n"
unfolding eqExcPID2_def eeqExcPID_def getNthReview_def
apply auto by (metis eqExcR_eq)

lemma eqExcPID2_imp2:
assumes "reach s" and "eqExcPID2 s s1" and "pid \<noteq> PID \<or> PID \<noteq> pid"
shows "getReviewersReviews s cid pid = getReviewersReviews s1 cid pid"
proof-
  have
  "(\<lambda>uID. if isRev s cid uID pid then [(uID, getNthReview s pid (getReviewIndex s cid uID pid))] else []) =
   (\<lambda>uID. if isRev s1 cid uID pid then [(uID, getNthReview s1 pid (getReviewIndex s1 cid uID pid))] else [])"
  apply(rule ext)
  using assms using assms by (auto simp add: eqExcPID2_imp' eqExcPID2_imp1)
  thus ?thesis unfolding getReviewersReviews_def using assms by (simp add: eqExcPID2_imp)
qed

lemma eqExcPID2_imp3:
"reach s \<Longrightarrow> eqExcPID2 s s1 \<Longrightarrow> pid \<noteq> PID \<or> PID \<noteq> pid
 \<Longrightarrow>
 getNthReview s pid = getNthReview s1 pid"
unfolding eqExcPID2_def apply auto
apply (rule ext) by (metis eeqExcPID_imp getNthReview_def)

lemma eqExcPID2_RDD:
"eqExcPID2 s s1 \<Longrightarrow>
 titlePaper (paper s PID) = titlePaper (paper s1 PID) \<and>
 abstractPaper (paper s PID) = abstractPaper (paper s1 PID) \<and>
 contentPaper (paper s PID) = contentPaper (paper s1 PID) \<and>
 disPaper (paper s PID) = disPaper (paper s1 PID) \<and>
 decsPaper (paper s PID) = decsPaper (paper s1 PID)"
using eqExcPID2_imp eeqExcPID_RDD by auto

lemma eqExcPID2_cong[simp, intro]:
"\<And> uu1 uu2. eqExcPID2 s s1 \<Longrightarrow> uu1 = uu2 \<Longrightarrow> eqExcPID2 (s \<lparr>confIDs := uu1\<rparr>) (s1 \<lparr>confIDs := uu2\<rparr>)"
"\<And> uu1 uu2. eqExcPID2 s s1 \<Longrightarrow> uu1 = uu2 \<Longrightarrow> eqExcPID2 (s \<lparr>conf := uu1\<rparr>) (s1 \<lparr>conf := uu2\<rparr>)"

"\<And> uu1 uu2. eqExcPID2 s s1 \<Longrightarrow> uu1 = uu2 \<Longrightarrow> eqExcPID2 (s \<lparr>userIDs := uu1\<rparr>) (s1 \<lparr>userIDs := uu2\<rparr>)"
"\<And> uu1 uu2. eqExcPID2 s s1 \<Longrightarrow> uu1 = uu2 \<Longrightarrow> eqExcPID2 (s \<lparr>pass := uu1\<rparr>) (s1 \<lparr>pass := uu2\<rparr>)"
"\<And> uu1 uu2. eqExcPID2 s s1 \<Longrightarrow> uu1 = uu2 \<Longrightarrow> eqExcPID2 (s \<lparr>user := uu1\<rparr>) (s1 \<lparr>user := uu2\<rparr>)"
"\<And> uu1 uu2. eqExcPID2 s s1 \<Longrightarrow> uu1 = uu2 \<Longrightarrow> eqExcPID2 (s \<lparr>roles := uu1\<rparr>) (s1 \<lparr>roles := uu2\<rparr>)"

"\<And> uu1 uu2. eqExcPID2 s s1 \<Longrightarrow> uu1 = uu2 \<Longrightarrow> eqExcPID2 (s \<lparr>paperIDs := uu1\<rparr>) (s1 \<lparr>paperIDs := uu2\<rparr>)"
"\<And> uu1 uu2. eqExcPID2 s s1 \<Longrightarrow> eeqExcPID uu1 uu2 \<Longrightarrow> eqExcPID2 (s \<lparr>paper := uu1\<rparr>) (s1 \<lparr>paper := uu2\<rparr>)"

"\<And> uu1 uu2. eqExcPID2 s s1 \<Longrightarrow> uu1 = uu2 \<Longrightarrow> eqExcPID2 (s \<lparr>pref := uu1\<rparr>) (s1 \<lparr>pref := uu2\<rparr>)"
"\<And> uu1 uu2. eqExcPID2 s s1 \<Longrightarrow> uu1 = uu2 \<Longrightarrow> eqExcPID2 (s \<lparr>voronkov := uu1\<rparr>) (s1 \<lparr>voronkov := uu2\<rparr>)"
"\<And> uu1 uu2. eqExcPID2 s s1 \<Longrightarrow> uu1 = uu2 \<Longrightarrow> eqExcPID2 (s \<lparr>news := uu1\<rparr>) (s1 \<lparr>news := uu2\<rparr>)"
"\<And> uu1 uu2. eqExcPID2 s s1 \<Longrightarrow> uu1 = uu2 \<Longrightarrow> eqExcPID2 (s \<lparr>phase := uu1\<rparr>) (s1 \<lparr>phase := uu2\<rparr>)"

unfolding eqExcPID2_def by auto

lemma eqExcPID2_Paper:
assumes s's1': "eqExcPID2 s s1"
and "paper s pid = Paper title abstract content reviews dis decs"
and "paper s1 pid = Paper title1 abstract1 content1 reviews1 dis1 decs1"
shows "title = title1 \<and> abstract = abstract1 \<and> content = content1 \<and> dis = dis1 \<and> decs = decs1"
using assms unfolding eqExcPID2_def apply (auto simp: eqExcR eeqExcPID_def)
by (metis titlePaper.simps abstractPaper.simps contentPaper.simps disPaper.simps decsPaper.simps)+


lemma cReview_step_eqExcPID2:
assumes a:
"a = Cact (cReview cid uid p PID uid')"
and "step s a = (ou,s')"
shows "eqExcPID2 s s'"
using assms unfolding eqExcPID2_def eeqExcPID_def eqExcRLR_def
apply (auto simp: c_defs)
unfolding List.insert_def by (smt filter.simps(2) isRevRoleFor.simps(1))


subsection \<open>Value Setup\<close>

type_synonym "value" = "userID \<times> userID set"

fun \<phi> :: "(state,act,out) trans \<Rightarrow> bool" where
"\<phi> (Trans _ (Cact (cReview cid uid p pid uid')) ou _) =
 (pid = PID \<and> ou = outOK)"
|
"\<phi> _ = False"

fun f :: "(state,act,out) trans \<Rightarrow> value" where
"f (Trans s (Cact (cReview cid uid p pid uid')) _ s') =
 (uid', {uid'. isPC s cid uid' \<and> pref s uid' PID \<noteq> Conflict})"

lemma \<phi>_def2:
"\<phi> (Trans s a ou s') =
 (ou = outOK \<and>
 (\<exists> cid uid p uid'. a = Cact (cReview cid uid p PID uid')))"
apply(cases a, simp_all) subgoal for x1 by (cases x1, auto) .


fun \<chi> :: "act \<Rightarrow> bool" where
"\<chi> (Uact (uReview cid uid p pid n rc)) = (pid = PID)"
|
"\<chi> (UUact (uuReview cid uid p pid n rc)) = (pid = PID)"
|
"\<chi> _ = False"

lemma \<chi>_def2:
"\<chi> a =
 (\<exists> cid uid p n rc. a = Uact (uReview cid uid p PID n rc) \<or>
                    a = UUact (uuReview cid uid p PID n rc))"
apply(cases a, simp_all)
  subgoal for x2 apply (cases x2, auto) .
  subgoal for x3 by (cases x3, auto) .

lemma eqExcPID_step_\<phi>_imp:
assumes s: "reach s" and ss1: "eqExcPID s s1"
(* new compared to the other properties: *)
and PID: "PID \<in>\<in> paperIDs s cid" and ph: "phase s cid > revPH"
(* end new *)
and step: "step s a = (ou,s')" and step1: "step s1 a = (ou1,s1')"
and \<phi>: "\<not> \<phi> (Trans s a ou s')"
shows "\<not> \<phi> (Trans s1 a ou1 s1')"
using assms unfolding \<phi>_def2 apply (auto simp add: c_defs eqExcPID_imp)
unfolding eqExcPID_def
apply(metis eqExcRLR_imp[OF s] eqExcRLR_imp2)
apply(metis eqExcRLR_imp[OF s] eqExcRLR_imp2)
using eqExcRLR_imp[OF s] PID by (metis less_not_refl paperIDs_equals)

lemma eqExcPID_step_\<phi>:
assumes "reach s" and "reach s1" and ss1: "eqExcPID s s1"
(* new compared to the other properties: *)
and PID: "PID \<in>\<in> paperIDs s cid" and ph: "phase s cid > revPH"
(* end new *)
and step: "step s a = (ou,s')" and step1: "step s1 a = (ou1,s1')"
shows "\<phi> (Trans s a ou s') = \<phi> (Trans s1 a ou1 s1')"
proof-
  have "PID \<in>\<in> paperIDs s1 cid \<and> phase s1 cid > revPH"
  using eqExcPID_imp[OF ss1] PID ph by auto
  thus ?thesis by (metis eqExcPID_step_\<phi>_imp eqExcPID_sym assms)
qed

(* new lemma compared to the other properties: *)
lemma non_eqExcPID_step_\<phi>_imp:
assumes s: "reach s" and ss1: "eqExcPID s s1"
and PID: "PID \<in>\<in> paperIDs s cid" and ou: "ou \<noteq> outErr"
and step: "step s a = (ou,s')" and step1: "step s1 a = (ou1,s1')"
and \<phi>: "\<not> \<phi> (Trans s a ou s')"
shows "\<not> \<phi> (Trans s1 a ou1 s1')"
using assms unfolding \<phi>_def2 by (auto simp add: c_defs eqExcPID_imp)

(* major *) lemma eqExcPID_step:
assumes s: "reach s" and s1: "reach s1"
and ss1: "eqExcPID s s1"
and step: "step s a = (ou,s')"
and step1: "step s1 a = (ou1,s1')"
and PID: "PID \<in>\<in> paperIDs s cid"
and ou_ph: "ou \<noteq> outErr \<or> phase s cid > revPH"
and \<phi>: "\<not> \<phi> (Trans s a ou s')" and \<chi>: "\<not> \<chi> a"
shows "eqExcPID s' s1'"
proof -
  have s': "reach s'" by (metis reach_PairI s step)
  note eqs = eqExcPID_imp[OF ss1]
  note eqs' = eqExcPID_imp1[OF ss1]

  note eqss = eqExcPID_imp'[OF s ss1]

  note simps[simp] = c_defs u_defs uu_defs r_defs l_defs Paper_dest_conv eqExcPID_def
  note simps2[simp] = eqExcRLR_imp2[where s=s and ?s1.0 = s1'] eqExcRLR_imp2[where s=s' and ?s1.0 = s1]
       eqExcRLR_set[of "(roles s cid uid)" "(roles s1' cid uid)" for uid cid]
       eqExcRLR_set[of "(roles s' cid uid)" "(roles s1 cid uid)" for uid cid]
       foo2 foo3 eqExcRLR_imp[OF s, where ?s1.0=s1'] eqExcRLR_imp[OF s', where ?s1.0=s1]

  note * = step step1 eqs eqs' \<phi> \<chi> PID ou_ph

  then show ?thesis
  proof (cases a)
    case (Cact x1)
    with * show ?thesis
    proof (cases x1)
      case (cReview x81 x82 x83 x84 x85)
      with Cact * show ?thesis
        by clarsimp (metis less_irrefl_nat paperIDs_equals s1 simps2(9))
    qed auto
  next
    case (Uact x2)
    with * show ?thesis
    proof (cases x2)
      case (uReview x71 x72 x73 x74 x75 x76)
      with Uact * show ?thesis
        by (clarsimp simp del: simps2) auto
    qed auto
  next
    case (UUact x3)
    with * show ?thesis
    proof (cases x3)
      case (uuReview x31 x32 x33 x34 x35 x36)
      with UUact * show ?thesis
        by (clarsimp simp del: simps2) auto
    qed auto
  qed auto
qed


lemma \<phi>_step_eqExcPID2:
assumes \<phi>: "\<phi> (Trans s a ou s')"
and s: "step s a = (ou,s')"
shows "eqExcPID2 s s'"
using \<phi> cReview_step_eqExcPID2[OF _ s] unfolding \<phi>_def2 by blast

(* major *) lemma eqExcPID2_step:
assumes s: "reach s"
and ss1: "eqExcPID2 s s1"
and step: "step s a = (ou,s')"
and step1: "step s1 a = (ou1,s1')"
and PID: "PID \<in>\<in> paperIDs s cid" and ph: "phase s cid \<ge> revPH"
and \<phi>: "\<not> \<phi> (Trans s a ou s')"
shows "eqExcPID2 s' s1'"
proof -
  have s': "reach s'" by (metis reach_PairI s step)
  note eqs = eqExcPID2_imp[OF ss1]
  (* note eqss = eqExcPID2_imp'[OF s ss1] *)
  note eqs' = eqExcPID2_imp1[OF ss1]

  note eqss = eqExcPID2_imp'[OF s ss1]

  note simps[simp] = c_defs u_defs uu_defs r_defs l_defs
          Paper_dest_conv
          eqExcPID2_def eeqExcPID_def
          eqExcR
  note simps2[simp] = eqExcRLR_imp2[where s=s and ?s1.0 = s1'] eqExcRLR_imp2[where s=s' and ?s1.0 = s1]
      eqExcRLR_set[of "(roles s cid uid)" "(roles s1' cid uid)" for cid uid]
      eqExcRLR_set[of "(roles s' cid uid)" "(roles s1 cid uid)" for cid uid]
      foo2 foo3 eqExcRLR_imp[OF s, where ?s1.0=s1'] eqExcRLR_imp[OF s', where ?s1.0=s1]
  note * = step step1 eqs eqs' ph PID \<phi>

  then show ?thesis
  proof (cases a)
    case (Cact x1)
    with * show ?thesis
    proof (cases x1)
      case (cReview x81 x82 x83 x84 x85)
      with Cact * show ?thesis
        by clarsimp (metis simps2(9))
    qed auto
  next
    case (Uact x2)
    with * show ?thesis
    proof (cases x2)
      case (uReview x71 x72 x73 x74 x75 x76)
      with Uact * show ?thesis
        by (clarsimp simp del: simps2) auto
    qed auto
  next
    case (UUact x3)
    with * show ?thesis
    proof (cases x3)
      case (uuReview x31 x32 x33 x34 x35 x36)
      with UUact * show ?thesis
        by (clarsimp simp del: simps2) auto
    qed auto
  next
    case (Lact x5)
    with * show ?thesis by (cases x5; auto)
  qed auto
qed

lemma eqExcPID2_step_\<phi>_imp:
assumes s: "reach s" and ss1: "eqExcPID2 s s1"
(* new compared to the other properties: *)
and PID: "PID \<in>\<in> paperIDs s cid" and ph: "phase s cid > revPH"
(* end new *)
and step: "step s a = (ou,s')" and step1: "step s1 a = (ou1,s1')"
and \<phi>: "\<not> \<phi> (Trans s a ou s')"
shows "\<not> \<phi> (Trans s1 a ou1 s1')"
using assms unfolding \<phi>_def2 apply (auto simp add: c_defs eqExcPID2_imp)
unfolding eqExcPID2_def
apply(metis eqExcRLR_imp[OF s] eqExcRLR_imp2)
apply(metis eqExcRLR_imp[OF s] eqExcRLR_imp2)
using eqExcRLR_imp[OF s] PID by (metis less_not_refl paperIDs_equals)

lemma eqExcPID2_step_\<phi>:
assumes "reach s" and "reach s1" and ss1: "eqExcPID2 s s1"
(* new compared to the other properties: *)
and PID: "PID \<in>\<in> paperIDs s cid" and ph: "phase s cid > revPH"
(* end new *)
and step: "step s a = (ou,s')" and step1: "step s1 a = (ou1,s1')"
shows "\<phi> (Trans s a ou s') = \<phi> (Trans s1 a ou1 s1')"
proof-
  have "PID \<in>\<in> paperIDs s1 cid \<and> phase s1 cid > revPH"
  using eqExcPID2_imp[OF ss1] PID ph by auto
  thus ?thesis by (metis eqExcPID2_step_\<phi>_imp eqExcPID2_sym assms)
qed

(* new lemma compared to the other properties: *)
lemma non_eqExcPID2_step_\<phi>_imp:
assumes s: "reach s" and ss1: "eqExcPID2 s s1"
and PID: "PID \<in>\<in> paperIDs s cid" and ou: "ou \<noteq> outErr"
and step: "step s a = (ou,s')" and step1: "step s1 a = (ou1,s1')"
and \<phi>: "\<not> \<phi> (Trans s a ou s')"
shows "\<not> \<phi> (Trans s1 a ou1 s1')"
using assms unfolding \<phi>_def2 by (auto simp add: c_defs eqExcPID2_imp)




end
