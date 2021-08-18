theory Friend_Traceback
imports Traceback_Intro
begin


subsection \<open>Tracing Back Friendship Status\<close>

text \<open>We prove the following traceback property:
If, at some point \<open>t\<close> on a system trace, the users \<open>UID\<close> and \<open>UID'\<close> are friends,
then one of the following holds:
\begin{itemize}
\item Either \<open>UID\<close> had issued a friend request to \<open>UID'\<close>, eventually followed by an approval
(i.e., a successful \<open>UID\<close>-friend creation action) by \<open>UID'\<close> such that between
that approval and \<open>t\<close> there was no successful \<open>UID'\<close>-unfriending (i.e., friend deletion)
by \<open>UID\<close> or \<open>UID\<close>-unfriending by \<open>UID'\<close>
\item Or vice versa (with \<open>UID\<close> and \<open>UID'\<close> swapped)
\end{itemize}

This property is captured by the predicate \<open>proper\<close>, which decomposes any valid system trace tr
starting in the initial state
for which the target state \<open>tgtOf (last tr)\<close> has \<open>UID\<close> and \<open>UID'\<close> as friends,
as follows: tr is the concatenation of \<open>tr1\<close>, \<open>trn\<close>, \<open>tr2\<close>, \<open>trnn\<close> and \<open>tr3\<close> where
\begin{itemize}
\item \<open>trn\<close> represents the time of the relevant friend request
\item \<open>trnn\<close> represents the time of the approval of this request
\item \<open>tr3\<close> contains no unfriending between the two users
\end{itemize}

The main theorem states that \<open>proper tr\<close>
holds for any trace \<open>tr\<close> that leads to \<open>UID\<close> and \<open>UID'\<close> being friends.
\<close>

consts UID :: userID
consts UID' :: userID

text \<open>\<open>SFRC\<close> means ``is a successful friend request creation''\<close>

fun SFRC :: "userID \<Rightarrow> userID \<Rightarrow> (state,act,out) trans \<Rightarrow> bool" where
"SFRC uidd uidd' (Trans s (Cact (cFriendReq uid p uid' _)) ou s') = (ou = outOK \<and> (uid,uid') = (uidd,uidd'))"
|
"SFRC uidd uidd' _ = False"

text \<open>\<open>SFC\<close> means ``is a successful friend creation'' \<close>

fun SFC :: "userID \<Rightarrow> userID \<Rightarrow> (state,act,out) trans \<Rightarrow> bool" where
"SFC uidd uidd' (Trans s (Cact (cFriend uid p uid')) ou s') = (ou = outOK \<and> (uid,uid') = (uidd,uidd'))"
|
"SFC uidd uidd' _ = False"

text \<open>\<open>SFD\<close> means ``is a successful friend deletion'' \<close>

fun SFD :: "userID \<Rightarrow> userID \<Rightarrow> (state,act,out) trans \<Rightarrow> bool" where
"SFD uidd uidd' (Trans s (Dact (dFriend uid p uid')) ou s') = (ou = outOK \<and> (uid,uid') = (uidd,uidd'))"
|
"SFD uidd uidd' _ = False"

definition proper1 :: "(state,act,out) trans trace \<Rightarrow> bool" where
"proper1 tr \<equiv>
 \<exists> trr trnn tr3. tr = trr @ trnn # tr3 \<and>
                 (SFC UID UID' trnn \<or> SFC UID' UID trnn) \<and>
                 never (SFD UID UID') tr3 \<and> never (SFD UID' UID) tr3"

lemma SFC_validTrans:
assumes "validTrans trn"
and "\<not> UID' \<in>\<in> friendIDs (srcOf trn) UID"
and "UID' \<in>\<in> friendIDs (tgtOf trn) UID"
shows "SFC UID UID' trn \<or> SFC UID' UID trn"
proof(cases trn)
  case (Trans s a ou s')
  then show ?thesis
    using assms
    by (cases a) (auto elim: step_elims simp: all_defs)
qed

lemma SFD_validTrans:
assumes "validTrans trn"
and "UID' \<in>\<in> friendIDs (tgtOf trn) UID"
shows "\<not> SFD UID UID' trn \<and> \<not> SFD UID' UID trn"
proof(cases trn)
  case (Trans s a ou s')
  then show ?thesis
    using assms
    by (cases a) (auto elim: step_elims simp: all_defs)
qed

lemma SFC_SFD:
assumes "SFC uid1 uid2 trn" shows "\<not> SFD uid3 uid4 trn"
proof(cases trn)
  case (Trans s a ou s') note trn = Trans
  show ?thesis using assms unfolding trn
  by (cases "a") auto
qed

lemma proper1_valid:
assumes "valid tr"
and "\<not> UID' \<in>\<in> friendIDs (srcOf (hd tr)) UID"
and "UID' \<in>\<in> friendIDs (tgtOf (last tr)) UID"
shows "proper1 tr"
using assms unfolding valid_valid2 proof induct
  case (Singl trn)
  then show ?case unfolding proper1_def using SFC_validTrans
  by (intro exI[of _ "[]"] exI[of _ trn]) auto
next
  case (Rcons tr trn)
  show ?case
  proof(cases "UID' \<in>\<in> friendIDs (srcOf trn) UID")
    case False
    hence "SFC UID UID' trn \<or> SFC UID' UID trn"
    using Rcons SFC_validTrans by auto
    thus ?thesis unfolding proper1_def
    apply - apply (rule exI[of _ tr]) by (intro exI[of _ trn] exI[of _ "[]"]) auto
  next
    case True
    hence "proper1 tr" using Rcons by auto
    then obtain trr trnn tr3 where
    tr: "tr = trr @ trnn # tr3" and
    SFC: "SFC UID UID' trnn \<or> SFC UID' UID trnn" and
    n: "never (SFD UID UID') tr3 \<and> never (SFD UID' UID) tr3"
    unfolding proper1_def by auto
    have "UID' \<in>\<in> friendIDs (tgtOf trn) UID" using Rcons.prems(2) by auto
    hence SFD: "\<not> SFD UID UID' trn \<and> \<not> SFD UID' UID trn"
    using SFD_validTrans \<open>validTrans trn\<close> by auto
    show ?thesis using SFC n SFD unfolding proper1_def tr
    apply - apply (rule exI[of _ trr])
    by (intro exI[of _ trnn] exI[of _ "tr3 ## trn"]) simp
  qed
qed

lemma istate_friendIDs:
"\<not> UID' \<in>\<in> friendIDs (istate) UID"
unfolding istate_def by simp

lemma proper1_valid_istate:
assumes "valid tr" and "srcOf (hd tr) = istate"
and "UID' \<in>\<in> friendIDs (tgtOf (last tr)) UID"
shows "proper1 tr"
using assms istate_friendIDs proper1_valid by auto

(*  *)

definition proper2 :: "userID \<Rightarrow> userID \<Rightarrow> (state,act,out) trans trace \<Rightarrow> bool" where
"proper2 uid uid' tr \<equiv>
 \<exists> tr1 trnn tr2. tr = tr1 @ trnn # tr2 \<and> SFRC uid uid' trnn"

lemma SFRC_validTrans:
assumes "validTrans trn"
and "\<not> uid \<in>\<in> pendingFReqs (srcOf trn) uid'"
and "uid \<in>\<in> pendingFReqs (tgtOf trn) uid'"
shows "SFRC uid uid' trn"
proof(cases trn)
  case (Trans s a ou s')
  then show ?thesis
    using assms
    by (cases "a") (auto elim: step_elims simp: all_defs)
qed

lemma proper2_valid:
assumes "valid tr"
and "\<not> uid \<in>\<in> pendingFReqs (srcOf (hd tr)) uid'"
and "uid \<in>\<in> pendingFReqs (tgtOf (last tr)) uid'"
shows "proper2 uid uid' tr"
using assms unfolding valid_valid2 proof induct
  case (Singl trn)
  thus ?case unfolding proper2_def using SFRC_validTrans
  by (intro exI[of _ "[]"] exI[of _ trn]) auto
next
  case (Rcons tr trn)
  show ?case
  proof(cases "uid \<in>\<in> pendingFReqs (srcOf trn) uid'")
    case False
    hence "SFRC uid uid' trn"
    using Rcons SFRC_validTrans by auto
    thus ?thesis unfolding proper2_def
    apply - apply (rule exI[of _ tr]) by (intro exI[of _ trn] exI[of _ "[]"]) auto
  next
    case True
    hence "proper2 uid uid' tr" using Rcons by auto
    then obtain trr trnn tr3 where
    tr: "tr = trr @ trnn # tr3" and SFRC: "SFRC uid uid' trnn"
    unfolding proper2_def by auto
    have "uid \<in>\<in> pendingFReqs (tgtOf trn) uid'" using Rcons.prems(2) by auto
    show ?thesis using SFRC unfolding proper2_def tr
    apply - apply (rule exI[of _ trr])
    by (intro exI[of _ trnn] exI[of _ "tr3 ## trn"]) simp
  qed
qed

lemma istate_pendingFReqs:
"\<not> uid \<in>\<in> pendingFReqs (istate) uid'"
unfolding istate_def by simp

lemma proper2_valid_istate:
assumes "valid tr" and "srcOf (hd tr) = istate"
and "uid \<in>\<in> pendingFReqs (tgtOf (last tr)) uid'"
shows "proper2 uid uid' tr"
using assms istate_pendingFReqs proper2_valid by auto

(*  *)

lemma SFC_pendingFReqs:
assumes "validTrans trn"
and "SFC uid' uid trn"
shows "uid \<in>\<in> pendingFReqs (srcOf trn) uid'"
proof(cases trn)
  case (Trans s a ou s')
  then show ?thesis
    using assms
    by (cases "a") (auto elim: step_elims simp: all_defs)
qed


definition proper :: "(state,act,out) trans trace \<Rightarrow> bool" where
"proper tr \<equiv>
 \<exists> tr1 trn tr2 trnn tr3. tr = tr1 @ trn # tr2 @ trnn # tr3 \<and>
                 (SFRC UID' UID trn \<and> SFC UID UID' trnn \<or>
                  SFRC UID UID' trn \<and> SFC UID' UID trnn) \<and>
                 never (SFD UID UID') tr3 \<and> never (SFD UID' UID) tr3"

theorem friend_accountability:
assumes v: "valid tr" and i: "srcOf (hd tr) = istate"
and UID: "UID' \<in>\<in> friendIDs (tgtOf (last tr)) UID"
shows "proper tr"
proof-
  have "proper1 tr" using proper1_valid_istate[OF assms] .
  then obtain trr trnn tr3 where
  tr: "tr = trr @ trnn # tr3" and
  SFC: "SFC UID UID' trnn \<or> SFC UID' UID trnn" (is "?A \<or> ?B") and
  n: "never (SFD UID UID') tr3 \<and> never (SFD UID' UID) tr3"
  unfolding proper1_def by auto
  have trnn: "validTrans trnn" and trr: "valid trr" using tr
  apply (metis valid_Cons_iff append_self_conv2 assms(1) list.distinct(1) valid_append)
  by (metis SFC SFC_pendingFReqs append_self_conv2 i istate_pendingFReqs list.distinct(1) list.sel(1) tr v valid_Cons_iff valid_append)
  show ?thesis using SFC proof
    assume SFC: ?A
    have 0: "UID' \<in>\<in> pendingFReqs (srcOf trnn) UID"
    using SFC_pendingFReqs[OF trnn SFC] .
    hence "srcOf trnn \<noteq> istate" unfolding istate_def by auto
    hence 2: "trr \<noteq> []" using i unfolding tr by auto
    hence i: "srcOf (hd trr) = istate" using i unfolding tr by auto
    have "srcOf trnn = tgtOf (last trr)" using tr v valid_append 2 by auto
    hence 1: "UID' \<in>\<in> pendingFReqs (tgtOf (last trr)) UID" using 0 by simp
    have "proper2 UID' UID trr" using proper2_valid_istate[OF trr i 1] .
    then obtain tr1 trn tr2 where
    trr: "trr = tr1 @ trn # tr2" and SFRC: "SFRC UID' UID trn"
    unfolding proper2_def by auto
    show ?thesis unfolding proper_def
    apply(rule exI[of _ tr1], rule exI[of _ trn], rule exI[of _ tr2],
          rule exI[of _ trnn], rule exI[of _ tr3])
    unfolding tr trr using SFRC SFC n by simp
  next
    assume SFC: ?B
    have 0: "UID \<in>\<in> pendingFReqs (srcOf trnn) UID'"
    using SFC_pendingFReqs[OF trnn SFC] .
    hence "srcOf trnn \<noteq> istate" unfolding istate_def by auto
    hence 2: "trr \<noteq> []" using i unfolding tr by auto
    hence i: "srcOf (hd trr) = istate" using i unfolding tr by auto
    have "srcOf trnn = tgtOf (last trr)" using tr v valid_append 2 by auto
    hence 1: "UID \<in>\<in> pendingFReqs (tgtOf (last trr)) UID'" using 0 by simp
    have "proper2 UID UID' trr" using proper2_valid_istate[OF trr i 1] .
    then obtain tr1 trn tr2 where
    trr: "trr = tr1 @ trn # tr2" and SFRC: "SFRC UID UID' trn"
    unfolding proper2_def by auto
    show ?thesis unfolding proper_def
    apply(rule exI[of _ tr1], rule exI[of _ trn], rule exI[of _ tr2],
          rule exI[of _ trnn], rule exI[of _ tr3])
    unfolding tr trr using SFRC SFC n by simp
  qed
qed



end
