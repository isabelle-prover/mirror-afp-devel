(* The value setup for post confidentiality *)
theory Post_Value_Setup
imports Post_Intro
begin

text \<open>The ID of the confidential post:\<close>

consts PID :: postID

subsection\<open>Preliminaries\<close>

(*
(* two posts equal everywhere but w.r.t. their content: *)
fun eqButT :: "post \<Rightarrow> post \<Rightarrow> bool" where
"eqButT ntc ntc1 =
 (titlePost ntc = titlePost ntc1 \<and>
  imgPost ntc = imgPost ntc1 \<and>
  visPost ntc = visPost ntc1)"

lemma eqButT_eq[simp,intro!]: "eqButT pap pap"
by(cases pap) auto

lemma eqButT_sym:
assumes "eqButT pap pap1"
shows "eqButT pap1 pap"
apply(cases pap, cases pap1)
using assms by auto

lemma eqButT_trans:
assumes "eqButT pap pap1" and "eqButT pap1 pap2"
shows "eqButT pap pap2"
apply(cases pap, cases pap1, cases pap2)
using assms by auto
*)

(* Auxiliary notion: two functions are equal everywhere but on PID *)
definition eeqButPID where
"eeqButPID ntcs ntcs1 \<equiv>
 \<forall> pid. pid \<noteq> PID \<longrightarrow>  ntcs pid = ntcs1 pid"

(* \<forall> pid. if pid = PID then eqButT (ntcs PID) (ntcs1 PID) else ntcs pid = ntcs1 pid *)

lemmas eeqButPID_intro = eeqButPID_def[THEN meta_eq_to_obj_eq, THEN iffD2]

lemma eeqButPID_eeq[simp,intro!]: "eeqButPID ntcs ntcs"
unfolding eeqButPID_def by auto

lemma eeqButPID_sym:
assumes "eeqButPID ntcs ntcs1" shows "eeqButPID ntcs1 ntcs"
using assms unfolding eeqButPID_def by auto

lemma eeqButPID_trans:
assumes "eeqButPID ntcs ntcs1" and "eeqButPID ntcs1 ntcs2" shows "eeqButPID ntcs ntcs2"
using assms unfolding eeqButPID_def by (auto split: if_splits)

lemma eeqButPID_cong:
assumes "eeqButPID ntcs ntcs1"
and "PID = PID \<Longrightarrow> eqButT uu uu1"
and "pid \<noteq> PID \<Longrightarrow> uu = uu1"
shows "eeqButPID (ntcs (pid := uu)) (ntcs1(pid := uu1))"
using assms unfolding eeqButPID_def by (auto split: if_splits)

(* lemma eeqButPID_eqButT:
"eeqButPID ntcs ntcs1 \<Longrightarrow> eqButT (ntcs PID) (ntcs1 PID)"
unfolding eeqButPID_def by (auto split: if_splits)
*)

lemma eeqButPID_not_PID:
"\<lbrakk>eeqButPID ntcs ntcs1; pid \<noteq> PID\<rbrakk> \<Longrightarrow> ntcs pid = ntcs1 pid"
unfolding eeqButPID_def by (auto split: if_splits)

(*
lemma eeqButPID_postSelectors:
"eeqButPID ntcs ntcs1 \<Longrightarrow>
 visPost (ntcs pid) = visPost (ntcs1 pid)"
  unfolding eeqButPID_def sledgehammer  by (metis eqButT.simps)
*)

lemma eeqButPID_toEq:
assumes "eeqButPID ntcs ntcs1"
shows "ntcs (PID := pst) = ntcs1 (PID := pst)"
using eeqButPID_not_PID[OF assms] by auto

lemma eeqButPID_update_post:
assumes "eeqButPID ntcs ntcs1"
shows "eeqButPID (ntcs (pid := ntc)) (ntcs1 (pid := ntc))"
using eeqButPID_not_PID[OF assms]
using assms unfolding eeqButPID_def by auto

(* The notion of two states being equal everywhere but on the content of
   the post associated to a given PID: *)
definition eqButPID :: "state \<Rightarrow> state \<Rightarrow> bool" where
"eqButPID s s1 \<equiv>
 admin s = admin s1 \<and>

 pendingUReqs s = pendingUReqs s1 \<and> userReq s = userReq s1 \<and>
 userIDs s = userIDs s1 \<and> user s = user s1 \<and> pass s = pass s1 \<and>

 pendingFReqs s = pendingFReqs s1 \<and> friendReq s = friendReq s1 \<and> friendIDs s = friendIDs s1 \<and>

 postIDs s = postIDs s1 \<and> admin s = admin s1 \<and>
 eeqButPID (post s) (post s1) \<and>
 owner s = owner s1 \<and>
 vis s = vis s1"

lemmas eqButPID_intro = eqButPID_def[THEN meta_eq_to_obj_eq, THEN iffD2]

lemma eqButPID_refl[simp,intro!]: "eqButPID s s"
unfolding eqButPID_def by auto

lemma eqButPID_sym:
assumes "eqButPID s s1" shows "eqButPID s1 s"
using assms eeqButPID_sym unfolding eqButPID_def by auto

lemma eqButPID_trans:
assumes "eqButPID s s1" and "eqButPID s1 s2" shows "eqButPID s s2"
using assms eeqButPID_trans unfolding eqButPID_def
by simp blast

(* Implications from eqButPID, including w.r.t. auxiliary operations: *)
lemma eqButPID_stateSelectors:
"eqButPID s s1 \<Longrightarrow>
 admin s = admin s1 \<and>

 pendingUReqs s = pendingUReqs s1 \<and> userReq s = userReq s1 \<and>
 userIDs s = userIDs s1 \<and> user s = user s1 \<and> pass s = pass s1 \<and>

 pendingFReqs s = pendingFReqs s1 \<and> friendReq s = friendReq s1 \<and> friendIDs s = friendIDs s1 \<and>

 postIDs s = postIDs s1 \<and> admin s = admin s1 \<and>
 eeqButPID (post s) (post s1) \<and>
 owner s = owner s1 \<and>
 vis s = vis s1 \<and>

 IDsOK s = IDsOK s1"
unfolding eqButPID_def IDsOK_def[abs_def] by auto

(* lemma eqButPID_eqButT:
"eqButPID s s1 \<Longrightarrow> eqButT (post s PID) (post s1 PID)"
unfolding eqButPID_def using eeqButPID_eqButT by auto *)

lemma eqButPID_not_PID:
"eqButPID s s1 \<Longrightarrow> pid \<noteq> PID \<Longrightarrow> post s pid = post s1 pid"
unfolding eqButPID_def using eeqButPID_not_PID by auto

lemma eqButPID_actions:
assumes "eqButPID s s1"
shows "listPosts s uid p = listPosts s1 uid p"
using eqButPID_stateSelectors[OF assms]
by (auto simp: l_defs intro!: arg_cong2[of _ _ _ _ cmap])

lemma eqButPID_setPost:
assumes "eqButPID s s1"
shows "(post s)(PID := pst) = (post s1)(PID := pst)"
using assms unfolding eqButPID_def using eeqButPID_toEq by auto

lemma eqButPID_update_post:
assumes "eqButPID s s1"
shows "eeqButPID ((post s) (pid := ntc)) ((post s1) (pid := ntc))"
using assms unfolding eqButPID_def using eeqButPID_update_post by auto

lemma eqButPID_cong[simp, intro]:
"\<And> uu1 uu2. eqButPID s s1 \<Longrightarrow> uu1 = uu2 \<Longrightarrow> eqButPID (s \<lparr>admin := uu1\<rparr>) (s1 \<lparr>admin := uu2\<rparr>)"

"\<And> uu1 uu2. eqButPID s s1 \<Longrightarrow> uu1 = uu2 \<Longrightarrow> eqButPID (s \<lparr>pendingUReqs := uu1\<rparr>) (s1 \<lparr>pendingUReqs := uu2\<rparr>)"
"\<And> uu1 uu2. eqButPID s s1 \<Longrightarrow> uu1 = uu2 \<Longrightarrow> eqButPID (s \<lparr>userReq := uu1\<rparr>) (s1 \<lparr>userReq := uu2\<rparr>)"
"\<And> uu1 uu2. eqButPID s s1 \<Longrightarrow> uu1 = uu2 \<Longrightarrow> eqButPID (s \<lparr>userIDs := uu1\<rparr>) (s1 \<lparr>userIDs := uu2\<rparr>)"
"\<And> uu1 uu2. eqButPID s s1 \<Longrightarrow> uu1 = uu2 \<Longrightarrow> eqButPID (s \<lparr>user := uu1\<rparr>) (s1 \<lparr>user := uu2\<rparr>)"
"\<And> uu1 uu2. eqButPID s s1 \<Longrightarrow> uu1 = uu2 \<Longrightarrow> eqButPID (s \<lparr>pass := uu1\<rparr>) (s1 \<lparr>pass := uu2\<rparr>)"

"\<And> uu1 uu2. eqButPID s s1 \<Longrightarrow> uu1 = uu2 \<Longrightarrow> eqButPID (s \<lparr>postIDs := uu1\<rparr>) (s1 \<lparr>postIDs := uu2\<rparr>)"
"\<And> uu1 uu2. eqButPID s s1 \<Longrightarrow> uu1 = uu2 \<Longrightarrow> eqButPID (s \<lparr>owner := uu1\<rparr>) (s1 \<lparr>owner := uu2\<rparr>)"
"\<And> uu1 uu2. eqButPID s s1 \<Longrightarrow> eeqButPID uu1 uu2 \<Longrightarrow> eqButPID (s \<lparr>post := uu1\<rparr>) (s1 \<lparr>post := uu2\<rparr>)"
"\<And> uu1 uu2. eqButPID s s1 \<Longrightarrow> uu1 = uu2 \<Longrightarrow> eqButPID (s \<lparr>vis := uu1\<rparr>) (s1 \<lparr>vis := uu2\<rparr>)"

"\<And> uu1 uu2. eqButPID s s1 \<Longrightarrow> uu1 = uu2 \<Longrightarrow> eqButPID (s \<lparr>pendingFReqs := uu1\<rparr>) (s1 \<lparr>pendingFReqs := uu2\<rparr>)"
"\<And> uu1 uu2. eqButPID s s1 \<Longrightarrow> uu1 = uu2 \<Longrightarrow> eqButPID (s \<lparr>friendReq := uu1\<rparr>) (s1 \<lparr>friendReq := uu2\<rparr>)"
"\<And> uu1 uu2. eqButPID s s1 \<Longrightarrow> uu1 = uu2 \<Longrightarrow> eqButPID (s \<lparr>friendIDs := uu1\<rparr>) (s1 \<lparr>friendIDs := uu2\<rparr>)"

unfolding eqButPID_def by auto


subsection\<open>Value Setup\<close>

datatype "value" =
  TVal post \<comment> \<open>updated content of the confidential post\<close>
| OVal bool \<comment> \<open>updated dynamic declassification trigger condition\<close>

text \<open>Openness of the access window to the confidential information in a given state,
i.e.~the dynamic declassification trigger condition:\<close>

definition openToUIDs where
"openToUIDs s \<equiv>
 \<exists> uid \<in> UIDs.
   uid \<in>\<in> userIDs s \<and>
   (uid = owner s PID \<or> uid \<in>\<in> friendIDs s (owner s PID) \<or>
    vis s PID = PublicV)"


definition "open" where "open s \<equiv> PID \<in>\<in> postIDs s \<and> openToUIDs s"

lemmas open_defs = openToUIDs_def open_def

lemma eqButPID_openToUIDs:
assumes "eqButPID s s1"
shows "openToUIDs s \<longleftrightarrow> openToUIDs s1"
using eqButPID_stateSelectors[OF assms]
unfolding openToUIDs_def by auto

lemma eqButPID_open:
assumes "eqButPID s s1"
shows "open s \<longleftrightarrow> open s1"
using assms eqButPID_openToUIDs eqButPID_stateSelectors
unfolding open_def by auto

lemma not_open_eqButPID:
assumes 1: "\<not> open s" and 2: "eqButPID s s1"
shows "\<not> open s1"
using 1 unfolding eqButPID_open[OF 2] .

fun \<phi> :: "(state,act,out) trans \<Rightarrow> bool" where
"\<phi> (Trans _ (Uact (uPost uid p pid pst)) ou _) = (pid = PID \<and> ou = outOK)"
|
"\<phi> (Trans s _ _ s') = (open s \<noteq> open s')"

lemma \<phi>_def2:
  assumes "step s a = (ou,s')"
  shows
    "\<phi> (Trans s a ou s') \<longleftrightarrow>
     (\<exists>uid p pst. a = Uact (uPost uid p PID pst) \<and> ou = outOK) \<or>
      open s \<noteq> open s'"
proof (cases a)
  case (Uact ua)
  then show ?thesis
    using assms
    by (cases ua, auto simp: u_defs open_defs)
qed auto

fun f :: "(state,act,out) trans \<Rightarrow> value" where
"f (Trans s (Uact (uPost uid p pid pst)) _ s') =
 (if pid = PID then TVal pst else OVal (open s'))"
|
"f (Trans s _ _ s') = OVal (open s')"

lemma Uact_uPost_step_eqButPID:
assumes a: "a = Uact (uPost uid p PID pst)"
and "step s a = (ou,s')"
shows "eqButPID s s'"
using assms unfolding eqButPID_def eeqButPID_def
by (auto simp: u_defs split: if_splits)


(* Key lemma: *)
lemma eqButPID_step:
assumes ss1: "eqButPID s s1"
and step: "step s a = (ou,s')"
and step1: "step s1 a = (ou1,s1')"
shows "eqButPID s' s1'"
proof -
  note [simp] = all_defs
                eeqButPID_def
  note [intro!] = eqButPID_intro
  note * =
    step step1 ss1
    eqButPID_stateSelectors[OF ss1]
    eqButPID_setPost[OF ss1] eqButPID_update_post[OF ss1]
  then show ?thesis
  proof (cases a)
    case (Sact x1)
    then show ?thesis using * by (cases x1) auto
  next
    case (Cact x2)
    then show ?thesis using * by (cases x2) auto
  next
    case (Dact x3)
    then show ?thesis using * by (cases x3) auto
  next
    case (Uact x4)
    show ?thesis
    proof (cases x4)
      case (uUser x11 x12 x13 x14 x15)
      then show ?thesis using Uact * by auto
    next
      case (uPost x31 x32 x33 x34)
      then show ?thesis using Uact * by (cases "x33 = PID") auto
    next
      case (uVisPost x51 x52 x53 x54)
      then show ?thesis using Uact * by (cases "x53 = PID") auto
    qed
  qed auto
qed

lemma eqButPID_step_\<phi>_imp:
assumes ss1: "eqButPID s s1"
and step: "step s a = (ou,s')" and step1: "step s1 a = (ou1,s1')"
and \<phi>: "\<phi> (Trans s a ou s')"
shows "\<phi> (Trans s1 a ou1 s1')"
proof-
  have s's1': "eqButPID s' s1'"
  using eqButPID_step local.step ss1 step1 by blast
  show ?thesis using step step1 \<phi> eqButPID_open[OF ss1] eqButPID_open[OF s's1']
  using eqButPID_stateSelectors[OF ss1]
  unfolding \<phi>_def2[OF step] \<phi>_def2[OF step1]
  by (auto simp: u_defs)
qed

(* Key lemma: *)
lemma eqButPID_step_\<phi>:
assumes s's1': "eqButPID s s1"
and step: "step s a = (ou,s')" and step1: "step s1 a = (ou1,s1')"
shows "\<phi> (Trans s a ou s') = \<phi> (Trans s1 a ou1 s1')"
by (metis eqButPID_step_\<phi>_imp eqButPID_sym assms)


end
