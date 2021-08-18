theory Post_Unwinding_Helper_RECEIVER
  imports Post_Observation_Setup_RECEIVER
begin

subsubsection \<open>Unwinding helper definitions and lemmas\<close>

locale Receiver_State_Equivalence_Up_To_PID = Fixed_PID + Fixed_AID
begin

(* Auxiliary notion: two functions are equal everywhere but on the content of
   the value corresponding to PID *)
definition eeqButPID where
"eeqButPID psts psts1 \<equiv>
 \<forall> aid pid. if aid = AID \<and> pid = PID then True
                                     else psts aid pid = psts1 aid pid"

lemmas eeqButPID_intro = eeqButPID_def[THEN meta_eq_to_obj_eq, THEN iffD2]

lemma eeqButPID_eeq[simp,intro!]: "eeqButPID psts psts"
unfolding eeqButPID_def by auto

lemma eeqButPID_sym:
assumes "eeqButPID psts psts1" shows "eeqButPID psts1 psts"
using assms unfolding eeqButPID_def by auto

lemma eeqButPID_trans:
assumes "eeqButPID psts psts1" and "eeqButPID psts1 psts2" shows "eeqButPID psts psts2"
using assms unfolding eeqButPID_def by (auto split: if_splits)

lemma eeqButPID_cong:
assumes "eeqButPID psts psts1"
and "aid = AID \<Longrightarrow> pid = PID \<Longrightarrow> eqButT uu uu1"
and "aid \<noteq> AID \<or> pid \<noteq> PID \<Longrightarrow> uu = uu1"
shows "eeqButPID (fun_upd2 psts aid pid uu) (fun_upd2 psts1 aid pid uu1)"
using assms unfolding eeqButPID_def fun_upd2_def by (auto split: if_splits)

(*
lemma eeqButPID_eqButT:
"eeqButPID psts psts1 \<Longrightarrow> eqButT (psts AID PID) (psts1 AID PID)"
unfolding eeqButPID_def by (auto split: if_splits)
*)

lemma eeqButPID_not_PID:
"\<lbrakk>eeqButPID psts psts1; aid \<noteq> AID \<or> pid \<noteq> PID\<rbrakk> \<Longrightarrow> psts aid pid = psts1 aid pid"
unfolding eeqButPID_def by (auto split: if_splits)

lemma eeqButPID_toEq:
assumes "eeqButPID psts psts1"
shows "fun_upd2 psts AID PID pst =
       fun_upd2 psts1 AID PID pst"
using eeqButPID_not_PID[OF assms]
unfolding fun_upd2_def by (auto split: if_splits intro!: ext)

lemma eeqButPID_update_post:
assumes "eeqButPID psts psts1"
shows "eeqButPID (fun_upd2 psts aid pid pst) (fun_upd2 psts1 aid pid pst)"
using eeqButPID_not_PID[OF assms]
unfolding fun_upd2_def
using assms unfolding eeqButPID_def by auto


(* lists two pairs (apiID, boolean flag) are equal save for the boolean flag: *)
fun eqButF :: "(apiID \<times> bool) list \<Rightarrow> (apiID \<times> bool) list \<Rightarrow> bool" where
"eqButF aID_bl aID_bl1 = (map fst aID_bl = map fst aID_bl1)"

lemma eqButF_eq[simp,intro!]: "eqButF aID_bl aID_bl"
by auto

lemma eqButF_sym:
assumes "eqButF aID_bl aID_bl1"
shows "eqButF aID_bl1 aID_bl"
using assms by auto

lemma eqButF_trans:
assumes "eqButF aID_bl aID_bl1" and "eqButF aID_bl1 aID_bl2"
shows "eqButF aID_bl aID_bl2"
using assms by auto

lemma eqButF_insert2:
"eqButF aID_bl aID_bl1 \<Longrightarrow>
 eqButF (insert2 aID b aID_bl) (insert2 aID b aID_bl1)"
unfolding insert2_def
by simp (smt comp_apply fst_conv map_eq_conv split_def)


(* The notion of two states being equal everywhere but on the content of
   the post associated to a given PID and the update status of the PID shareWith info: *)
definition eqButPID :: "state \<Rightarrow> state \<Rightarrow> bool" where
"eqButPID s s1 \<equiv>
 admin s = admin s1 \<and>

 pendingUReqs s = pendingUReqs s1 \<and> userReq s = userReq s1 \<and>
 userIDs s = userIDs s1 \<and> user s = user s1 \<and> pass s = pass s1 \<and>

 pendingFReqs s = pendingFReqs s1 \<and> friendReq s = friendReq s1 \<and> friendIDs s = friendIDs s1 \<and>
 sentOuterFriendIDs s = sentOuterFriendIDs s1 \<and> recvOuterFriendIDs s = recvOuterFriendIDs s1 \<and>

 postIDs s = postIDs s1 \<and> admin s = admin s1 \<and>
 post s = post s1 \<and>
 owner s = owner s1 \<and>
 vis s = vis s1 \<and>

 pendingSApiReqs s = pendingSApiReqs s1 \<and> sApiReq s = sApiReq s1 \<and>
 serverApiIDs s = serverApiIDs s1 \<and> serverPass s = serverPass s1 \<and>
 outerPostIDs s = outerPostIDs s1 \<and>
 eeqButPID (outerPost s) (outerPost s1) \<and>
 outerOwner s = outerOwner s1 \<and>
 outerVis s = outerVis s1 \<and>

 pendingCApiReqs s = pendingCApiReqs s1 \<and> cApiReq s = cApiReq s1 \<and>
 clientApiIDs s = clientApiIDs s1 \<and> clientPass s = clientPass s1 \<and>
 sharedWith s = sharedWith s1"

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
 sentOuterFriendIDs s = sentOuterFriendIDs s1 \<and> recvOuterFriendIDs s = recvOuterFriendIDs s1 \<and>

 postIDs s = postIDs s1 \<and> admin s = admin s1 \<and>
 post s = post s1 \<and>
 owner s = owner s1 \<and>
 vis s = vis s1 \<and>

 pendingSApiReqs s = pendingSApiReqs s1 \<and> sApiReq s = sApiReq s1 \<and>
 serverApiIDs s = serverApiIDs s1 \<and> serverPass s = serverPass s1 \<and>
 outerPostIDs s = outerPostIDs s1 \<and>
 eeqButPID (outerPost s) (outerPost s1) \<and>
 outerOwner s = outerOwner s1 \<and>
 outerVis s = outerVis s1 \<and>

 pendingCApiReqs s = pendingCApiReqs s1 \<and> cApiReq s = cApiReq s1 \<and>
 clientApiIDs s = clientApiIDs s1 \<and> clientPass s = clientPass s1 \<and>
 sharedWith s = sharedWith s1 \<and>

 IDsOK s = IDsOK s1"
unfolding eqButPID_def IDsOK_def[abs_def] by auto

lemma eqButPID_not_PID:
"eqButPID s s1 \<Longrightarrow> aid \<noteq> AID \<or> pid \<noteq> PID \<Longrightarrow> outerPost s aid pid = outerPost s1 aid pid"
unfolding eqButPID_def using eeqButPID_not_PID by auto

lemma eqButPID_actions:
assumes "eqButPID s s1"
shows "listInnerPosts s uid p = listInnerPosts s1 uid p"
and "listOuterPosts s uid p = listOuterPosts s1 uid p"
using eqButPID_stateSelectors[OF assms] (* eqButPID_postSelectors[OF assms] *)
by (auto simp: l_defs intro!: arg_cong2[of _ _ _ _ cmap])

lemma eqButPID_update:
assumes "eqButPID s s1"
shows "fun_upd2 (outerPost s) AID PID pst = fun_upd2 (outerPost s1) AID PID pst"
using assms unfolding eqButPID_def using eeqButPID_toEq by (metis fun_upd2_absorb)

lemma eqButPID_update_post:
assumes "eqButPID s s1"
shows "eeqButPID (fun_upd2 (outerPost s) aid pid pst) (fun_upd2 (outerPost s1) aid pid pst)"
using assms unfolding eqButPID_def using eeqButPID_update_post by auto

lemma eqButPID_cong[simp, intro]:
"\<And> uu1 uu2. eqButPID s s1 \<Longrightarrow> uu1 = uu2 \<Longrightarrow> eqButPID (s \<lparr>admin := uu1\<rparr>) (s1 \<lparr>admin := uu2\<rparr>)"

"\<And> uu1 uu2. eqButPID s s1 \<Longrightarrow> uu1 = uu2 \<Longrightarrow> eqButPID (s \<lparr>pendingUReqs := uu1\<rparr>) (s1 \<lparr>pendingUReqs := uu2\<rparr>)"
"\<And> uu1 uu2. eqButPID s s1 \<Longrightarrow> uu1 = uu2 \<Longrightarrow> eqButPID (s \<lparr>userReq := uu1\<rparr>) (s1 \<lparr>userReq := uu2\<rparr>)"
"\<And> uu1 uu2. eqButPID s s1 \<Longrightarrow> uu1 = uu2 \<Longrightarrow> eqButPID (s \<lparr>userIDs := uu1\<rparr>) (s1 \<lparr>userIDs := uu2\<rparr>)"
"\<And> uu1 uu2. eqButPID s s1 \<Longrightarrow> uu1 = uu2 \<Longrightarrow> eqButPID (s \<lparr>user := uu1\<rparr>) (s1 \<lparr>user := uu2\<rparr>)"
"\<And> uu1 uu2. eqButPID s s1 \<Longrightarrow> uu1 = uu2 \<Longrightarrow> eqButPID (s \<lparr>pass := uu1\<rparr>) (s1 \<lparr>pass := uu2\<rparr>)"

"\<And> uu1 uu2. eqButPID s s1 \<Longrightarrow> uu1 = uu2 \<Longrightarrow> eqButPID (s \<lparr>postIDs := uu1\<rparr>) (s1 \<lparr>postIDs := uu2\<rparr>)"
"\<And> uu1 uu2. eqButPID s s1 \<Longrightarrow> uu1 = uu2 \<Longrightarrow> eqButPID (s \<lparr>post := uu1\<rparr>) (s1 \<lparr>post := uu2\<rparr>)"
"\<And> uu1 uu2. eqButPID s s1 \<Longrightarrow> uu1 = uu2 \<Longrightarrow> eqButPID (s \<lparr>owner := uu1\<rparr>) (s1 \<lparr>owner := uu2\<rparr>)"
"\<And> uu1 uu2. eqButPID s s1 \<Longrightarrow> uu1 = uu2 \<Longrightarrow> eqButPID (s \<lparr>vis := uu1\<rparr>) (s1 \<lparr>vis := uu2\<rparr>)"

"\<And> uu1 uu2. eqButPID s s1 \<Longrightarrow> uu1 = uu2 \<Longrightarrow> eqButPID (s \<lparr>pendingFReqs := uu1\<rparr>) (s1 \<lparr>pendingFReqs := uu2\<rparr>)"
"\<And> uu1 uu2. eqButPID s s1 \<Longrightarrow> uu1 = uu2 \<Longrightarrow> eqButPID (s \<lparr>friendReq := uu1\<rparr>) (s1 \<lparr>friendReq := uu2\<rparr>)"
"\<And> uu1 uu2. eqButPID s s1 \<Longrightarrow> uu1 = uu2 \<Longrightarrow> eqButPID (s \<lparr>friendIDs := uu1\<rparr>) (s1 \<lparr>friendIDs := uu2\<rparr>)"
"\<And> uu1 uu2. eqButPID s s1 \<Longrightarrow> uu1 = uu2 \<Longrightarrow> eqButPID (s \<lparr>sentOuterFriendIDs := uu1\<rparr>) (s1 \<lparr>sentOuterFriendIDs := uu2\<rparr>)"
"\<And> uu1 uu2. eqButPID s s1 \<Longrightarrow> uu1 = uu2 \<Longrightarrow> eqButPID (s \<lparr>recvOuterFriendIDs := uu1\<rparr>) (s1 \<lparr>recvOuterFriendIDs := uu2\<rparr>)"

"\<And> uu1 uu2. eqButPID s s1 \<Longrightarrow> uu1 = uu2 \<Longrightarrow> eqButPID (s \<lparr>pendingSApiReqs := uu1\<rparr>) (s1 \<lparr>pendingSApiReqs := uu2\<rparr>)"
"\<And> uu1 uu2. eqButPID s s1 \<Longrightarrow> uu1 = uu2 \<Longrightarrow> eqButPID (s \<lparr>sApiReq := uu1\<rparr>) (s1 \<lparr>sApiReq := uu2\<rparr>)"
"\<And> uu1 uu2. eqButPID s s1 \<Longrightarrow> uu1 = uu2 \<Longrightarrow> eqButPID (s \<lparr>serverApiIDs := uu1\<rparr>) (s1 \<lparr>serverApiIDs := uu2\<rparr>)"
"\<And> uu1 uu2. eqButPID s s1 \<Longrightarrow> uu1 = uu2 \<Longrightarrow> eqButPID (s \<lparr>serverPass := uu1\<rparr>) (s1 \<lparr>serverPass := uu2\<rparr>)"
"\<And> uu1 uu2. eqButPID s s1 \<Longrightarrow> uu1 = uu2 \<Longrightarrow> eqButPID (s \<lparr>outerPostIDs := uu1\<rparr>) (s1 \<lparr>outerPostIDs := uu2\<rparr>)"

"\<And> uu1 uu2. eqButPID s s1 \<Longrightarrow> eeqButPID uu1 uu2 \<Longrightarrow> eqButPID (s \<lparr>outerPost := uu1\<rparr>) (s1 \<lparr>outerPost := uu2\<rparr>)"
"\<And> uu1 uu2. eqButPID s s1 \<Longrightarrow> uu1 = uu2 \<Longrightarrow> eqButPID (s \<lparr>outerVis := uu1\<rparr>) (s1 \<lparr>outerVis := uu2\<rparr>)"

"\<And> uu1 uu2. eqButPID s s1 \<Longrightarrow> uu1 = uu2 \<Longrightarrow> eqButPID (s \<lparr>outerOwner := uu1\<rparr>) (s1 \<lparr>outerOwner := uu2\<rparr>)"

"\<And> uu1 uu2. eqButPID s s1 \<Longrightarrow> uu1 = uu2 \<Longrightarrow> eqButPID (s \<lparr>pendingCApiReqs := uu1\<rparr>) (s1 \<lparr>pendingCApiReqs := uu2\<rparr>)"
"\<And> uu1 uu2. eqButPID s s1 \<Longrightarrow> uu1 = uu2 \<Longrightarrow> eqButPID (s \<lparr>cApiReq := uu1\<rparr>) (s1 \<lparr>cApiReq := uu2\<rparr>)"
"\<And> uu1 uu2. eqButPID s s1 \<Longrightarrow> uu1 = uu2 \<Longrightarrow> eqButPID (s \<lparr>clientApiIDs := uu1\<rparr>) (s1 \<lparr>clientApiIDs := uu2\<rparr>)"
"\<And> uu1 uu2. eqButPID s s1 \<Longrightarrow> uu1 = uu2 \<Longrightarrow> eqButPID (s \<lparr>clientPass := uu1\<rparr>) (s1 \<lparr>clientPass := uu2\<rparr>)"

"\<And> uu1 uu2. eqButPID s s1 \<Longrightarrow> uu1 = uu2 \<Longrightarrow> eqButPID (s \<lparr>sharedWith := uu1\<rparr>) (s1 \<lparr>sharedWith:= uu2\<rparr>)"
unfolding eqButPID_def by auto


(* major *) lemma comReceivePost_step_eqButPID:
assumes a: "a = COMact (comReceivePost AID sp PID pst uid vs)"
and a1: "a1 = COMact (comReceivePost AID sp PID pst1 uid vs)"
and "step s a = (ou,s')" and "step s1 a1 = (ou1,s1')"
and "eqButPID s s1"
shows "eqButPID s' s1'"
using assms unfolding eqButPID_def eeqButPID_def
unfolding a a1 by (fastforce simp: com_defs fun_upd2_def)

(* major *) lemma eqButPID_step:
assumes ss1: "eqButPID s s1"
and step: "step s a = (ou,s')"
and step1: "step s1 a = (ou1,s1')"
shows "eqButPID s' s1'"
proof -
  note [simp] = all_defs
  note * = step step1 ss1 eqButPID_stateSelectors[OF ss1] eqButPID_update_post[OF ss1]

  then show ?thesis
  proof (cases a)
    case (Sact x1)
    with * show ?thesis by (cases x1) auto
  next
    case (Cact x2)
    with * show ?thesis by (cases x2) auto
  next
    case (Dact x3)
    with * show ?thesis by (cases x3) auto
  next
    case (Uact x4)
    with * show ?thesis by (cases x4) auto
  next
    case (COMact x7)
    with * show ?thesis by (cases x7) auto
  qed auto
qed

end

end
