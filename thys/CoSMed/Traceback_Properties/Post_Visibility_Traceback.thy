theory Post_Visibility_Traceback
  imports Traceback_Intro
begin

consts PID :: postID
consts VIS :: vis

subsection \<open>Tracing Back Post Visibility Status\<close>

text \<open>We prove the following traceback property:
If, at some point \<open>t\<close> on a system trace, the visibility of a post \<open>PID\<close>
has a value \<open>VIS\<close>, then one of the following holds:
\begin{itemize}
\item Either \<open>VIS\<close> is \<open>FriendV\<close> (i.e., friends-only) which is the default at post creation
\item Or the post's owner had issued a successful ``update visibility'' action setting the visibility to \<open>VIS\<close>,
and no other successful update actions to \<open>PID\<close>'s visibility occur
between the time of that action and \<open>t\<close>.
\end{itemize}

This will be captured in the predicate \<open>proper\<close>, and the main theorem states that \<open>proper tr\<close>
holds for any trace \<open>tr\<close> that leads to post \<open>PID\<close> acquiring visibility \<open>VIS\<close>.
\<close>


text \<open>\<open>SNC uidd trn\<close> means
``The transaction \<open>trn\<close> is a successful post creation by user \<open>uidd\<close>'' \<close>

fun SNC :: "userID \<Rightarrow> (state,act,out) trans \<Rightarrow> bool" where
"SNC uidd (Trans s (Cact (cPost uid p pid tit)) ou s') = (ou = outOK \<and> (uid,pid) = (uidd,PID))"
|
"SNC uidd _ = False"


text \<open>\<open>SNVU uidd vvs trn\<close> means
"The transaction \<open>trn\<close> is a successful post visibility update for \<open>PID\<close>, by user \<open>uidd\<close>, to value \<open>vvs\<close>'' \<close>

fun SNVU :: "userID \<Rightarrow> vis \<Rightarrow> (state,act,out) trans \<Rightarrow> bool" where
"SNVU uidd vvs (Trans s (Uact (uVisPost uid p pid vs)) ou s') =
   (ou = outOK \<and> (uid,pid) = (uidd,PID) \<and> vs = vvs)"
|
"SNVU uidd vvis _ = False"

definition proper :: "(state,act,out) trans trace \<Rightarrow> bool" where
"proper tr \<equiv>
 VIS = FriendV
 \<or>
 (\<exists> uid tr1 trn tr2 trnn tr3.
    tr = tr1 @ trn # tr2 @ trnn # tr3 \<and>
    SNC uid trn \<and> SNVU uid VIS trnn \<and> (\<forall> vis. never (SNVU uid vis) tr3))"

(*  *)

definition proper1 :: "(state,act,out) trans trace \<Rightarrow> bool" where
"proper1 tr \<equiv>
 \<exists> tr2 trnn tr3.
    tr = tr2 @ trnn # tr3 \<and>
    SNVU (owner (srcOf trnn) PID) VIS trnn"

lemma not_never_ex:
assumes "\<not> never P xs"
shows "\<exists> xs1 x xs2. xs = xs1 @ x # xs2 \<and> P x \<and> never P xs2"
using assms proof(induct xs rule: rev_induct)
  case (Nil)
  thus ?case unfolding list_all_iff empty_iff by auto
next
  case (snoc y ys)
  show ?case
  proof(cases "P y")
    case True thus ?thesis using snoc
    apply(intro exI[of _ ys]) apply(intro exI[of _ y] exI[of _ "[]"]) by auto
  next
    case False then obtain xs1 x xs2 where "ys = xs1 @ x # xs2 \<and> P x \<and> never P xs2"
    using snoc by auto
    thus ?thesis using snoc False
    apply(intro exI[of _ xs1]) apply(intro exI[of _ x] exI[of _ "xs2 ## y"]) by auto
  qed
qed

lemma SNVU_postIDs:
assumes "validTrans trn" and "SNVU uid vs trn"
shows "PID \<in>\<in> postIDs (srcOf trn)"
proof(cases trn)
  case (Trans s a ou s')
  then show ?thesis
    using assms
    by (cases "a") (auto simp: all_defs elim: step_elims)
qed

lemma SNVU_visib:
assumes "validTrans trn" and "SNVU uid vs trn"
shows "vis (tgtOf trn) PID = vs"
proof(cases trn)
  case (Trans s a ou s')
  then show ?thesis
    using assms
    by (cases "a") (auto simp: all_defs elim: step_elims)
qed

lemma owner_validTrans:
assumes "validTrans trn" and "PID \<in>\<in> postIDs (srcOf trn)"
shows "owner (srcOf trn) PID = owner (tgtOf trn) PID"
proof(cases trn)
  case (Trans s a ou s')
  then show ?thesis
    using assms
    by (cases "a") (auto simp: all_defs elim: step_elims)
qed

lemma owner_valid:
assumes "valid tr" and "PID \<in>\<in> postIDs (srcOf (hd tr))"
shows "owner (srcOf (hd tr)) PID = owner (tgtOf (last tr)) PID"
using assms using owner_validTrans IDs_mono validTrans by induct auto

lemma SNVU_vis_validTrans:
assumes "validTrans trn" and "PID \<in>\<in> postIDs (srcOf trn)"
and "\<forall> vs. \<not> SNVU (owner (srcOf trn) PID) vs trn"
shows "vis (srcOf trn) PID = vis (tgtOf trn) PID"
proof(cases trn)
  case (Trans s a ou s')
  then show ?thesis
    using assms
    by (cases "a") (auto simp: all_defs elim: step_elims)
qed

lemma SNVU_vis_valid:
assumes "valid tr" and "PID \<in>\<in> postIDs (srcOf (hd tr))"
and "\<forall> vis. never (SNVU (owner (srcOf (hd tr)) PID) vis) tr"
shows "vis (srcOf (hd tr)) PID = vis (tgtOf (last tr)) PID"
using assms proof induct
  case (Singl)
  thus ?case using SNVU_vis_validTrans by auto
next
  case (Cons trn tr)
  have n: "PID \<in>\<in> postIDs (srcOf (hd tr))"
  using Cons by (simp add: IDs_mono(2) validTrans)
  have v: "\<forall> vis. never (SNVU (owner (srcOf (hd tr)) PID) vis) tr"
  using Cons by (simp add: owner_validTrans)
  have "vis (srcOf trn) PID = vis (srcOf (hd tr)) PID"
  using Cons SNVU_vis_validTrans by auto
  also have "... = vis (tgtOf (last tr)) PID"
  using n v Cons(4) by auto
  finally show ?case using Cons by auto
qed

lemma proper1_never:
assumes vtr: "valid tr" and PID: "PID \<in>\<in> postIDs (srcOf (hd tr))"
and tr: "proper1 tr" and v: "vis (tgtOf (last tr)) PID = VIS"
shows "\<exists> tr2 trnn tr3.
    tr = tr2 @ trnn # tr3 \<and>
    SNVU (owner (srcOf trnn) PID) VIS trnn \<and> (\<forall> vis. never (SNVU (owner (srcOf trnn) PID) vis) tr3)"
proof-
  obtain tr2 trnn tr3 where
  tr: "tr = tr2 @ trnn # tr3" and SNVU: "SNVU (owner (srcOf trnn) PID) VIS trnn"
  using tr unfolding proper1_def by auto
  define uid where "uid \<equiv> owner (srcOf trnn) PID"
  show ?thesis
  proof(cases "never (\<lambda> trn. \<exists> vis. SNVU uid vis trn) tr3")
    case True thus ?thesis using tr SNVU unfolding uid_def list_all_iff by blast
  next
    case False
    from not_never_ex[OF this] obtain tr3a tr3n tr3b vs where tr3: "tr3 = tr3a @ tr3n # tr3b"
    and SNVUtr3n: "SNVU uid vs tr3n" and n: "\<forall> vs. never (SNVU uid vs) tr3b"
    unfolding list_all_iff by blast
    have trnn: "validTrans trnn" and
    tr3n: "validTrans tr3n" and vtr3: "valid tr3" using tr unfolding tr tr3
    by (metis Nil_is_append_conv append_self_conv2 list.distinct(1) tr tr3 valid_ConsE valid_append vtr)+
    hence PID_trnn: "PID \<in>\<in> postIDs (srcOf trnn)" and
    PID_tr3n: "PID \<in>\<in> postIDs (srcOf tr3n)" using SNVU_postIDs SNVU SNVUtr3n by auto
    have vvv: "valid (trnn # tr3a @ [tr3n])"
    using vtr unfolding tr tr3
    by (smt Nil_is_append_conv append_self_conv2 hd_append2 list.distinct(1) list.sel(1)
        valid_Cons_iff valid_append)
    hence PID_tr3n': "PID \<in>\<in> postIDs (tgtOf tr3n)" using tr3n SNVUtr3n
    by (simp add: IDs_mono(2) PID_tr3n validTrans)
    from owner_valid[OF vvv] PID_trnn
    have 000: "owner (tgtOf tr3n) PID = uid" unfolding uid_def by simp
    hence 0: "owner (srcOf tr3n) PID = uid" using PID_tr3n owner_validTrans tr3n by blast
    have 00: "vs = vis (tgtOf tr3n) PID" using SNVUtr3n tr3n SNVU_visib by auto
    have vis: "vs = VIS"
    proof(cases "tr3b = []")
      case True
      thus ?thesis using v 00 unfolding tr tr3 by simp
    next
      case False
      hence tgt: "tgtOf tr3n = srcOf (hd tr3b)" and tr3b: "valid tr3b" using vtr3 unfolding tr3
      apply (metis valid_append list.distinct(2) self_append_conv2 valid_ConsE)
      by (metis False append_self_conv2 list.distinct(1) tr3 valid_Cons_iff valid_append vtr3)
      show ?thesis unfolding 00 tgt
        using v False PID_tr3n'
        using SNVU_vis_valid[OF tr3b _ n[unfolded 000[symmetric] tgt]]
      unfolding tr tr3 tgt by simp
    qed
    show ?thesis apply(intro exI[of _ "tr2 @ trnn # tr3a"])
    apply(intro exI[of _ tr3n] exI[of _ tr3b])
    using SNVUtr3n n unfolding tr tr3 0 vis by simp
  qed
qed


(* *)

lemma SNVU_validTrans:
assumes "validTrans trn"
and "PID \<in>\<in> postIDs (srcOf trn)"
and "vis (srcOf trn) PID \<noteq> VIS"
and "vis (tgtOf trn) PID = VIS"
shows "SNVU (owner (srcOf trn) PID) VIS trn"
proof(cases trn)
  case (Trans s a ou s')
  then show ?thesis
    using assms
    by (cases "a") (auto simp: all_defs elim: step_elims)
qed

lemma valid_mono_postID:
assumes "valid tr"
and "PID \<in>\<in> postIDs (srcOf (hd tr))"
shows "PID \<in>\<in> postIDs (tgtOf (last tr))"
using assms proof induct
  case (Singl trn)
  then show ?case using IDs_mono(2) by (cases trn) auto
next
  case (Cons trn tr)
  then show ?case using IDs_mono(2) by (cases trn) auto
qed

lemma proper1_valid:
assumes V: "VIS \<noteq> FriendV"
and a: "valid tr"
"PID \<in>\<in> postIDs (srcOf (hd tr))"
"vis (srcOf (hd tr)) PID \<noteq> VIS"
"vis (tgtOf (last tr)) PID = VIS"
shows "proper1 tr"
using a unfolding valid_valid2 proof induct
  case (Singl trn)
  then show ?case unfolding proper1_def using SNVU_validTrans
  by (intro exI[of _ "owner (srcOf trn) PID"] exI[of _ "[]"] exI[of _ trn]) auto
next
  case (Rcons tr trn)
  hence "PID \<in>\<in> postIDs (srcOf (hd tr))" using Rcons by simp
  from valid_mono_postID[OF \<open>valid2 tr\<close>[unfolded valid2_valid] this]
  have "PID \<in>\<in> postIDs (tgtOf (last tr))" by simp
  hence 0: "PID \<in>\<in> postIDs (srcOf trn)" using Rcons by simp
  show ?case
  proof(cases "vis (srcOf trn) PID = VIS")
    case False
    hence "SNVU (owner (srcOf trn) PID) VIS trn"
    apply (intro SNVU_validTrans) using 0 Rcons by auto
    thus ?thesis unfolding proper1_def
    by (intro exI[of _ tr] exI[of _ trn] exI[of _ "[]"]) auto
  next
    case True
    hence "proper1 tr" using Rcons by auto
    then obtain trr trnn tr3 where
    tr: "tr = trr @ trnn # tr3" and SNVU: "SNVU (owner (srcOf trnn) PID) VIS trnn"
    unfolding proper1_def using V by auto
    have "vis (tgtOf trn) PID = VIS" using Rcons.prems by auto
    thus ?thesis
    using SNVU V unfolding proper1_def tr
    by(intro exI[of _ trr] exI[of _ trnn] exI[of _ "tr3 ## trn"]) auto
  qed
qed

lemma istate_postIDs:
"\<not> PID \<in>\<in> postIDs istate"
unfolding istate_def by simp


(* *)

definition proper2 :: "(state,act,out) trans trace \<Rightarrow> bool" where
"proper2 tr \<equiv>
 \<exists> uid tr1 trn tr2.
    tr = tr1 @ trn # tr2 \<and> SNC uid trn"

lemma SNC_validTrans:
assumes "VIS \<noteq> FriendV" and "validTrans trn"
and "\<not> PID \<in>\<in> postIDs (srcOf trn)"
and "PID \<in>\<in> postIDs (tgtOf trn)"
shows "\<exists> uid. SNC uid trn"
proof(cases trn)
  case (Trans s a ou s')
  then show ?thesis
    using assms
    by (cases "a") (auto simp: all_defs elim: step_elims)
qed

lemma proper2_valid:
assumes V: "VIS \<noteq> FriendV"
and a: "valid tr"
"\<not> PID \<in>\<in> postIDs (srcOf (hd tr))"
"PID \<in>\<in> postIDs (tgtOf (last tr))"
shows "proper2 tr"
using a unfolding valid_valid2 proof induct
  case (Singl trn)
  then obtain uid where "SNC uid trn" using SNC_validTrans V by auto
  thus ?case unfolding proper2_def using SNC_validTrans
  by (intro exI[of _ uid] exI[of _ "[]"]  exI[of _ trn]) auto
next
  case (Rcons tr trn)
  show ?case
  proof(cases "PID \<in>\<in> postIDs (srcOf trn)")
    case False
    then obtain uid where "SNC uid trn"
    using Rcons SNC_validTrans V by auto
    thus ?thesis unfolding proper2_def
    apply - apply (intro exI[of _ uid] exI[of _ tr]) by (intro exI[of _ trn] exI[of _ "[]"]) auto
  next
    case True
    hence "proper2 tr" using Rcons by auto
    then obtain uid tr1 trnn tr2 where
    tr: "tr = tr1 @ trnn # tr2" and SFRC: "SNC uid trnn"
    unfolding proper2_def by auto
    have "PID \<in>\<in> postIDs (tgtOf trn)" using V Rcons.prems by auto
    show ?thesis using SFRC unfolding proper2_def tr
    apply - apply (intro exI[of _ uid] exI[of _ tr1])
    by (intro exI[of _ trnn] exI[of _ "tr2 ## trn"]) simp
  qed
qed

lemma proper2_valid_istate:
assumes V: "VIS \<noteq> FriendV"
and a: "valid tr"
"srcOf (hd tr) = istate"
"PID \<in>\<in> postIDs (tgtOf (last tr))"
shows "proper2 tr"
using proper2_valid assms istate_postIDs by auto

(* *)

lemma SNC_visPost:
assumes "VIS \<noteq> FriendV"
and "validTrans trn" "SNC uid trn" and "reach (srcOf trn)"
shows "vis (tgtOf trn) PID \<noteq> VIS"
proof(cases trn)
  case (Trans s a ou s')
  then show ?thesis
    using assms
    apply (cases "a") apply (auto simp: all_defs elim: step_elims)
    subgoal for x2 apply(cases x2)
      using reach_not_postIDs_vis_FriendV
      by (auto simp: all_defs elim: step_elims) .
qed

lemma SNC_postIDs:
assumes "validTrans trn" and "SNC uid trn"
shows "PID \<in>\<in> postIDs (tgtOf trn)"
proof(cases trn)
  case (Trans s a ou s')
  then show ?thesis
    using assms
    by (cases "a") (auto simp: all_defs elim: step_elims)
qed

lemma SNC_owner:
assumes "validTrans trn" and "SNC uid trn"
shows "uid = owner (tgtOf trn) PID"
proof(cases trn)
  case (Trans s a ou s')
  then show ?thesis
    using assms
    by (cases "a") (auto simp: all_defs elim: step_elims)
qed

theorem post_accountability:
assumes v: "valid tr" and i: "srcOf (hd tr) = istate"
and PIDin: "PID \<in>\<in> postIDs (tgtOf (last tr))"
and PID: "vis (tgtOf (last tr)) PID = VIS"
shows "proper tr"
proof(cases "VIS = FriendV")
  case True thus ?thesis unfolding proper_def by auto
next
  case False
  have "proper2 tr" using proper2_valid_istate[OF False v i PIDin] .
  then obtain uid tr1 trn trr where
  tr: "tr = tr1 @ trn # trr" and SNC: "SNC uid trn" unfolding proper2_def by auto
  hence trn: "validTrans trn" and r: "reach (srcOf trn)" using v unfolding tr
    apply (metis list.distinct(2) self_append_conv2 valid_ConsE valid_append)
    by (metis (mono_tags, lifting) append_Cons hd_append i list.sel(1) reach.simps tr v valid_append valid_init_reach)
  hence N: "PID \<in>\<in> postIDs (tgtOf trn)" "vis (tgtOf trn) PID \<noteq> VIS"
  using SNC_postIDs SNC_visPost False SNC by auto
  hence trrNE: "trr \<noteq> []" and 1: "last tr = last trr" using PID unfolding tr by auto
  hence trr_v: "valid trr" using v unfolding tr
  by (metis valid_Cons_iff append_self_conv2 list.distinct(1) valid_append)
  have 0: "tgtOf trn = srcOf (hd trr)" using v trrNE unfolding tr
  by (metis valid_append list.distinct(2) self_append_conv2 valid_ConsE)
  have "proper1 trr" using proper1_valid[OF False trr_v N[unfolded 0] PID[unfolded 1]] .
  from proper1_never[OF trr_v N(1)[unfolded 0] this PID[unfolded 1]] obtain tr2 trnn tr3 where
  trr: "trr = tr2 @ trnn # tr3" and SNVU: "SNVU (owner (srcOf trnn) PID) VIS trnn"
  and vis: "\<forall> vis. never (SNVU (owner (srcOf trnn) PID) vis) tr3" by auto
  have 00: "srcOf (hd (tr2 @ [trnn])) = tgtOf trn" using v unfolding tr trr
  by (metis "0" append_self_conv2 hd_append2 list.sel(1) trr)
  have trnn: "validTrans trnn" using trr_v unfolding trr
  by (metis valid_Cons_iff append_self_conv2 list.distinct(1) valid_append)
  have vv: "valid (tr2 @ [trnn])"
  using v unfolding tr trr
  by (smt Nil_is_append_conv append_self_conv2 hd_append2 list.distinct(1) list.sel(1)
        valid_Cons_iff valid_append)
  have "uid = owner (tgtOf trn) PID" using SNC trn SNC_owner by auto
  also have "... = owner (tgtOf trnn) PID"
  using owner_valid[OF vv] N(1) unfolding 00 by simp
  also have "... = owner (srcOf trnn) PID"
  using SNVU trnn SNVU_postIDs owner_validTrans by auto
  finally have uid: "uid = owner (srcOf trnn) PID" .
  show ?thesis unfolding proper_def
  apply(rule disjI2)
  apply(intro exI[of _ uid] exI[of _ tr1])
  apply(rule exI[of _ trn], rule exI[of _ tr2])
  apply(intro exI[of _ trnn] exI[of _ tr3])
  using SNC SNVU vis unfolding tr trr uid by auto
qed


end
