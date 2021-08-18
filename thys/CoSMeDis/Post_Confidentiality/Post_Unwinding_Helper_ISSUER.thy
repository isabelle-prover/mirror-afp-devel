theory Post_Unwinding_Helper_ISSUER
  imports Post_Observation_Setup_ISSUER
begin

locale Issuer_State_Equivalence_Up_To_PID = Fixed_PID
begin

subsubsection \<open>Unwinding helper lemmas and definitions\<close>

(* Auxiliary notion: two functions are equal everywhere but on the NIC (content) of
   the value corresponding to PID *)
definition eeqButPID where
"eeqButPID psts psts1 \<equiv>
 \<forall> pid. if pid = PID then True else psts pid = psts1 pid"

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
and "pid = PID \<Longrightarrow> eqButT uu uu1"
and "pid \<noteq> PID \<Longrightarrow> uu = uu1"
shows "eeqButPID (psts (pid := uu)) (psts1(pid := uu1))"
using assms unfolding eeqButPID_def by (auto split: if_splits)

(*
lemma eeqButPID_eqButT:
"eeqButPID psts psts1 \<Longrightarrow> eqButT (psts PID) (psts1 PID)"
unfolding eeqButPID_def by (auto split: if_splits)
*)

lemma eeqButPID_not_PID:
"\<lbrakk>eeqButPID psts psts1; pid \<noteq> PID\<rbrakk> \<Longrightarrow> psts pid = psts1 pid"
unfolding eeqButPID_def by (auto split: if_splits)

(*
lemma eeqButPID_postSelectors:
"eeqButPID psts psts1 \<Longrightarrow>
 titlePost (psts pid) = titlePost (psts1 pid) \<and>
 imgPost (psts pid) = imgPost (psts1 pid) \<and>
 visPost (psts pid) = visPost (psts1 pid)"
unfolding eeqButPID_def by (metis eqButT.simps)
*)

lemma eeqButPID_toEq:
assumes "eeqButPID psts psts1"
shows "psts (PID := pid) =
       psts1 (PID := pid)"
using eeqButPID_not_PID[OF assms] by auto

lemma eeqButPID_update_post:
assumes "eeqButPID psts psts1"
shows "eeqButPID (psts (pid := pst)) (psts1 (pid := pst))"
using eeqButPID_not_PID[OF assms]
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
by simp (smt map_eq_conv o_apply o_id prod.collapse prod.sel(1) split_conv)


(* Auxiliary notion: two functions are equal everywhere but on the second component of NIC of
   the value corresponding to PID, which is a list of pairs *)
definition eeqButPID_F where
"eeqButPID_F sw sw1 \<equiv>
 \<forall> pid. if pid = PID then eqButF (sw PID) (sw1 PID) else sw pid = sw1 pid"

lemmas eeqButPID_F_intro = eeqButPID_F_def[THEN meta_eq_to_obj_eq, THEN iffD2]

lemma eeqButPID_F_eeq[simp,intro!]: "eeqButPID_F sw sw"
unfolding eeqButPID_F_def by auto

lemma eeqButPID_F_sym:
assumes "eeqButPID_F sw sw1" shows "eeqButPID_F sw1 sw"
using assms eqButF_sym unfolding eeqButPID_F_def
by presburger

lemma eeqButPID_F_trans:
assumes "eeqButPID_F sw sw1" and "eeqButPID_F sw1 sw2" shows "eeqButPID_F sw sw2"
using assms unfolding eeqButPID_F_def by (auto split: if_splits)

lemma eeqButPID_F_cong:
assumes "eeqButPID_F sw sw1"
and "PID = PID \<Longrightarrow> eqButF uu uu1"
and "pid \<noteq> PID \<Longrightarrow> uu = uu1"
shows "eeqButPID_F (sw (pid := uu)) (sw1(pid := uu1))"
using assms unfolding eeqButPID_F_def by (auto split: if_splits)

lemma eeqButPID_F_eqButF:
"eeqButPID_F sw sw1 \<Longrightarrow> eqButF (sw PID) (sw1 PID)"
unfolding eeqButPID_F_def by (auto split: if_splits)

lemma eeqButPID_F_not_PID:
"\<lbrakk>eeqButPID_F sw sw1; pid \<noteq> PID\<rbrakk> \<Longrightarrow> sw pid = sw1 pid"
unfolding eeqButPID_F_def by (auto split: if_splits)

lemma eeqButPID_F_postSelectors:
"eeqButPID_F sw sw1 \<Longrightarrow> map fst (sw pid) = map fst (sw1 pid)"
unfolding eeqButPID_F_def by (metis eqButF.simps)

lemma eeqButPID_F_insert2:
"eeqButPID_F sw sw1 \<Longrightarrow>
 eqButF (insert2 aID b (sw PID)) (insert2 aID b (sw1 PID))"
unfolding eeqButPID_F_def using eqButF_insert2 by metis

lemma eeqButPID_F_toEq:
assumes "eeqButPID_F sw sw1"
shows "sw (PID := map (\<lambda> (aID,_). (aID,b)) (sw PID)) =
       sw1 (PID := map (\<lambda> (aID,_). (aID,b)) (sw1 PID))"
using length_map eeqButPID_F_eqButF[OF assms] eeqButPID_F_not_PID[OF assms]
apply(auto simp: o_def split_def map_replicate_const intro!: map_prod_cong ext)
by (metis length_map)

lemma eeqButPID_F_updateShared:
assumes "eeqButPID_F sw sw1"
shows "eeqButPID_F (sw (pid := aID_b)) (sw1 (pid := aID_b))"
using eeqButPID_F_eqButF[OF assms] eeqButPID_F_not_PID[OF assms]
using assms unfolding eeqButPID_F_def by auto


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
 eeqButPID (post s) (post s1) \<and>
 owner s = owner s1 \<and>
 vis s = vis s1 \<and>

 pendingSApiReqs s = pendingSApiReqs s1 \<and> sApiReq s = sApiReq s1 \<and>
 serverApiIDs s = serverApiIDs s1 \<and> serverPass s = serverPass s1 \<and>
 outerPostIDs s = outerPostIDs s1 \<and> outerPost s = outerPost s1 \<and>
 outerOwner s = outerOwner s1 \<and>
 outerVis s = outerVis s1 \<and>

 pendingCApiReqs s = pendingCApiReqs s1 \<and> cApiReq s = cApiReq s1 \<and>
 clientApiIDs s = clientApiIDs s1 \<and> clientPass s = clientPass s1 \<and>
 eeqButPID_F (sharedWith s) (sharedWith s1)"

lemmas eqButPID_intro = eqButPID_def[THEN meta_eq_to_obj_eq, THEN iffD2]

lemma eqButPID_refl[simp,intro!]: "eqButPID s s"
unfolding eqButPID_def by auto

lemma eqButPID_sym:
assumes "eqButPID s s1" shows "eqButPID s1 s"
using assms eeqButPID_sym eeqButPID_F_sym unfolding eqButPID_def by auto

lemma eqButPID_trans:
assumes "eqButPID s s1" and "eqButPID s1 s2" shows "eqButPID s s2"
using assms eeqButPID_trans eeqButPID_F_trans unfolding eqButPID_def
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
 eeqButPID (post s) (post s1) \<and>
 owner s = owner s1 \<and>
 vis s = vis s1 \<and>

 pendingSApiReqs s = pendingSApiReqs s1 \<and> sApiReq s = sApiReq s1 \<and>
 serverApiIDs s = serverApiIDs s1 \<and> serverPass s = serverPass s1 \<and>
 outerPostIDs s = outerPostIDs s1 \<and> outerPost s = outerPost s1 \<and>
 outerOwner s = outerOwner s1 \<and>
 outerVis s = outerVis s1 \<and>

 pendingCApiReqs s = pendingCApiReqs s1 \<and> cApiReq s = cApiReq s1 \<and>
 clientApiIDs s = clientApiIDs s1 \<and> clientPass s = clientPass s1 \<and>
 eeqButPID_F (sharedWith s) (sharedWith s1) \<and>

 IDsOK s = IDsOK s1"
unfolding eqButPID_def IDsOK_def[abs_def] by auto

(* lemma eqButPID_eqButT:
"eqButPID s s1 \<Longrightarrow> eqButT (post s PID) (post s1 PID)"
unfolding eqButPID_def using eeqButPID_eqButT by auto *)

lemma eqButPID_not_PID:
"eqButPID s s1 \<Longrightarrow> pid \<noteq> PID \<Longrightarrow> post s pid = post s1 pid"
unfolding eqButPID_def using eeqButPID_not_PID by auto

lemma eqButPID_eqButF:
"eqButPID s s1 \<Longrightarrow> eqButF (sharedWith s PID) (sharedWith s1 PID)"
unfolding eqButPID_def using eeqButPID_F_eqButF by auto

lemma eqButPID_not_PID_sharedWith:
"eqButPID s s1 \<Longrightarrow> pid \<noteq> PID \<Longrightarrow> sharedWith s pid = sharedWith s1 pid"
unfolding eqButPID_def using eeqButPID_F_not_PID by auto

(* lemma eqButPID_imp0:
assumes "eqButPID s s1" and 1: "pid \<noteq> PID"
shows "post s pid = post s1 pid"
proof-
  have "eeqButPID (post s) (post s1)"
  using assms using eqButPID_imp by simp
  from eeqButPID_imp(2)[OF this] 1 show ?thesis by auto
qed *)

(*
lemma eqButPID_postSelectors:
assumes "eqButPID s s1"
shows "titlePost (post s pid) = titlePost (post s1 pid) \<and>
       imgPost (post s pid) = imgPost (post s1 pid) \<and>
       visPost (post s pid) = visPost (post s1 pid)"
using assms unfolding eqButPID_def using eeqButPID_postSelectors by auto
*)

lemma eqButPID_insert2:
"eqButPID s s1 \<Longrightarrow>
 eqButF (insert2 aID b (sharedWith s PID)) (insert2 aID b (sharedWith s1 PID))"
unfolding eqButPID_def using eeqButPID_F_insert2 by metis

lemma eqButPID_actions:
assumes "eqButPID s s1"
shows "listInnerPosts s uid p = listInnerPosts s1 uid p"
using eqButPID_stateSelectors[OF assms] (* eqButPID_postSelectors[OF assms *)
by (auto simp: l_defs intro!: arg_cong2[of _ _ _ _ cmap])

(*
lemma eqButPID_setTextPost:
assumes "eqButPID s s1"
shows "setTextPost (post s PID) pst =
       setTextPost (post s1 PID) pst"
using assms unfolding eqButPID_def using eeqButPID_toEq
by (meson fun_upd_eqD)
*)

lemma eqButPID_update:
assumes "eqButPID s s1"
shows "(post s)(PID := txt) = (post s1)(PID := txt)"
using assms unfolding eqButPID_def using eeqButPID_toEq by auto

lemma eqButPID_update_post:
assumes "eqButPID s s1"
shows "eeqButPID ((post s) (pid := pst)) ((post s1) (pid := pst))"
using assms unfolding eqButPID_def using eeqButPID_update_post by auto

lemma eqButPID_setShared:
assumes "eqButPID s s1"
shows "(sharedWith s) (PID := map (\<lambda> (aID,_). (aID,b)) (sharedWith s PID)) =
       (sharedWith s1) (PID := map (\<lambda> (aID,_). (aID,b)) (sharedWith s1 PID))"
using assms unfolding eqButPID_def using eeqButPID_F_toEq by auto

lemma eqButPID_updateShared:
assumes "eqButPID s s1"
shows "eeqButPID_F ((sharedWith s) (pid := aID_b)) ((sharedWith s1) (pid := aID_b))"
using assms unfolding eqButPID_def using eeqButPID_F_updateShared by auto


lemma eqButPID_cong[simp]:
"\<And> uu1 uu2. eqButPID s s1 \<Longrightarrow> uu1 = uu2 \<Longrightarrow> eqButPID (s \<lparr>admin := uu1\<rparr>) (s1 \<lparr>admin := uu2\<rparr>)"

"\<And> uu1 uu2. eqButPID s s1 \<Longrightarrow> uu1 = uu2 \<Longrightarrow> eqButPID (s \<lparr>pendingUReqs := uu1\<rparr>) (s1 \<lparr>pendingUReqs := uu2\<rparr>)"
"\<And> uu1 uu2. eqButPID s s1 \<Longrightarrow> uu1 = uu2 \<Longrightarrow> eqButPID (s \<lparr>userReq := uu1\<rparr>) (s1 \<lparr>userReq := uu2\<rparr>)"
"\<And> uu1 uu2. eqButPID s s1 \<Longrightarrow> uu1 = uu2 \<Longrightarrow> eqButPID (s \<lparr>userIDs := uu1\<rparr>) (s1 \<lparr>userIDs := uu2\<rparr>)"
"\<And> uu1 uu2. eqButPID s s1 \<Longrightarrow> uu1 = uu2 \<Longrightarrow> eqButPID (s \<lparr>user := uu1\<rparr>) (s1 \<lparr>user := uu2\<rparr>)"
"\<And> uu1 uu2. eqButPID s s1 \<Longrightarrow> uu1 = uu2 \<Longrightarrow> eqButPID (s \<lparr>pass := uu1\<rparr>) (s1 \<lparr>pass := uu2\<rparr>)"

"\<And> uu1 uu2. eqButPID s s1 \<Longrightarrow> uu1 = uu2 \<Longrightarrow> eqButPID (s \<lparr>postIDs := uu1\<rparr>) (s1 \<lparr>postIDs := uu2\<rparr>)"
"\<And> uu1 uu2. eqButPID s s1 \<Longrightarrow> eeqButPID uu1 uu2 \<Longrightarrow> eqButPID (s \<lparr>post := uu1\<rparr>) (s1 \<lparr>post := uu2\<rparr>)"
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
"\<And> uu1 uu2. eqButPID s s1 \<Longrightarrow> uu1 = uu2 \<Longrightarrow> eqButPID (s \<lparr>outerPost := uu1\<rparr>) (s1 \<lparr>outerPost := uu2\<rparr>)"
"\<And> uu1 uu2. eqButPID s s1 \<Longrightarrow> uu1 = uu2 \<Longrightarrow> eqButPID (s \<lparr>outerOwner := uu1\<rparr>) (s1 \<lparr>outerOwner := uu2\<rparr>)"
"\<And> uu1 uu2. eqButPID s s1 \<Longrightarrow> uu1 = uu2 \<Longrightarrow> eqButPID (s \<lparr>outerVis := uu1\<rparr>) (s1 \<lparr>outerVis := uu2\<rparr>)"

"\<And> uu1 uu2. eqButPID s s1 \<Longrightarrow> uu1 = uu2 \<Longrightarrow> eqButPID (s \<lparr>pendingCApiReqs := uu1\<rparr>) (s1 \<lparr>pendingCApiReqs := uu2\<rparr>)"
"\<And> uu1 uu2. eqButPID s s1 \<Longrightarrow> uu1 = uu2 \<Longrightarrow> eqButPID (s \<lparr>cApiReq := uu1\<rparr>) (s1 \<lparr>cApiReq := uu2\<rparr>)"
"\<And> uu1 uu2. eqButPID s s1 \<Longrightarrow> uu1 = uu2 \<Longrightarrow> eqButPID (s \<lparr>clientApiIDs := uu1\<rparr>) (s1 \<lparr>clientApiIDs := uu2\<rparr>)"
"\<And> uu1 uu2. eqButPID s s1 \<Longrightarrow> uu1 = uu2 \<Longrightarrow> eqButPID (s \<lparr>clientPass := uu1\<rparr>) (s1 \<lparr>clientPass := uu2\<rparr>)"

"\<And> uu1 uu2. eqButPID s s1 \<Longrightarrow> eeqButPID_F uu1 uu2 \<Longrightarrow> eqButPID (s \<lparr>sharedWith := uu1\<rparr>) (s1 \<lparr>sharedWith:= uu2\<rparr>)"
unfolding eqButPID_def by auto


(* major *) lemma eqButPID_step:
assumes ss1: "eqButPID s s1"
and step: "step s a = (ou,s')"
and step1: "step s1 a = (ou1,s1')"
shows "eqButPID s' s1'"
proof -
  note [simp] = all_defs eeqButPID_F_def
  note [intro!] = eqButPID_cong
  note * = step step1 ss1 eqButPID_stateSelectors[OF ss1]
           eqButPID_update[OF ss1] eqButPID_update_post[OF ss1]
           eqButPID_setShared[OF ss1] eqButPID_updateShared[OF ss1]
           eqButPID_insert2[OF ss1]
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
    with * show ?thesis
    proof (cases x4)
      case (uPost x21 x22 x23 x24)
      with Uact * show ?thesis by (cases "x23 = PID") auto
    next
      case (uVisPost x31 x32 x33 x34)
      with Uact * show ?thesis by (cases "x33 = PID") auto
    qed auto
  next
    case (COMact x7)
    with * show ?thesis
    proof (cases x7)
      case (comSendPost x61 x62 x63 x64)
      with COMact * show ?thesis by (cases "x64 = PID") auto
    qed auto
  qed auto
qed

end

end
