(* The state equivalence used for the unwinding proofs for the friendship confidentiality
   properties *)
theory Outer_Friend_Receiver_State_Indistinguishability
  imports Outer_Friend_Receiver_Observation_Setup
begin

subsubsection \<open>Unwinding helper definitions and lemmas\<close>

context OuterFriendReceiver
begin

(* The notion of two (apiID \<times> userID) lists being equal except for an occurrence of (AID, UID): *)
fun eqButUIDl :: "(apiID \<times> userID) list \<Rightarrow> (apiID \<times> userID) list \<Rightarrow> bool" where
"eqButUIDl auidl auidl1 = (remove1 (AID,UID) auidl = remove1 (AID,UID) auidl1)"

lemma eqButUIDl_eq[simp,intro!]: "eqButUIDl auidl auidl"
by auto

lemma eqButUIDl_sym:
assumes "eqButUIDl auidl auidl1"
shows "eqButUIDl auidl1 auidl"
using assms by auto

lemma eqButUIDl_trans:
assumes "eqButUIDl auidl auidl1" and "eqButUIDl auidl1 auidl2"
shows "eqButUIDl auidl auidl2"
using assms by auto

lemma eqButUIDl_remove1_cong:
assumes "eqButUIDl auidl auidl1"
shows "eqButUIDl (remove1 auid auidl) (remove1 auid auidl1)"
using assms by (auto simp: remove1_commute)


lemma eqButUIDl_snoc_cong:
assumes "eqButUIDl auidl auidl1"
and "auid' \<in>\<in> auidl \<longleftrightarrow> auid' \<in>\<in> auidl1"
shows "eqButUIDl (auidl ## auid') (auidl1 ## auid')"
using assms by (auto simp: remove1_append remove1_idem)


(* The notion of two functions each taking a userID being equal for observers,
   and eqButUIDs for others. *)
definition eqButUIDf where
"eqButUIDf frds frds1 \<equiv>
  (\<forall>uid. if uid \<in> UIDs AID' then frds uid = frds1 uid else eqButUIDl (frds uid) (frds1 uid))"

lemmas eqButUIDf_intro = eqButUIDf_def[THEN meta_eq_to_obj_eq, THEN iffD2]

lemma eqButUIDf_eeq[simp,intro!]: "eqButUIDf frds frds"
unfolding eqButUIDf_def by auto

lemma eqButUIDf_sym:
assumes "eqButUIDf frds frds1" shows "eqButUIDf frds1 frds"
using assms unfolding eqButUIDf_def
by auto

lemma eqButUIDf_trans:
assumes "eqButUIDf frds frds1" and "eqButUIDf frds1 frds2"
shows "eqButUIDf frds frds2"
using assms unfolding eqButUIDf_def by fastforce

lemma eqButUIDf_cong:
assumes "eqButUIDf frds frds1"
and "uid \<in> UIDs AID' \<Longrightarrow> uu = uu1"
and "uid \<notin> UIDs AID' \<Longrightarrow> eqButUIDl uu uu1"
shows "eqButUIDf (frds (uid := uu)) (frds1(uid := uu1))"
using assms unfolding eqButUIDf_def by auto
(*
lemma eqButUIDf_eqButUIDl:
assumes "eqButUIDf frds frds1"
shows "eqButUIDl UID2 (frds UID1) (frds1 UID1)"
  and "eqButUIDl UID1 (frds UID2) (frds1 UID2)"
using assms unfolding eqButUIDf_def by (auto split: if_splits)
*)
lemma eqButUIDf_UIDs:
"\<lbrakk>eqButUIDf frds frds1; uid \<in> UIDs AID'\<rbrakk> \<Longrightarrow> frds uid = frds1 uid"
unfolding eqButUIDf_def by (auto split: if_splits)
(*
lemma eqButUIDf_not_UID':
assumes eq1: "eqButUIDf frds frds1"
and uid: "(uid,uid') \<notin> {(UID1,UID2), (UID2,UID1)}"
shows "uid \<in>\<in> frds uid' \<longleftrightarrow> uid \<in>\<in> frds1 uid'"
proof -
  from uid have "(uid' = UID1 \<and> uid \<noteq> UID2)
               \<or> (uid' = UID2 \<and> uid \<noteq> UID1)
               \<or> (uid' \<notin> {UID1,UID2})" (is "?u1 \<or> ?u2 \<or> ?n12")
    by auto
  then show ?thesis proof (elim disjE)
    assume "?u1"
    moreover then have "uid \<in>\<in> remove1 UID2 (frds uid') \<longleftrightarrow> uid \<in>\<in> remove1 UID2 (frds1 uid')"
      using eq1 unfolding eqButUIDf_def by auto
    ultimately show ?thesis by auto
  next
    assume "?u2"
    moreover then have "uid \<in>\<in> remove1 UID1 (frds uid') \<longleftrightarrow> uid \<in>\<in> remove1 UID1 (frds1 uid')"
      using eq1 unfolding eqButUIDf_def by auto
    ultimately show ?thesis by auto
  next
    assume "?n12"
    then show ?thesis using eq1 unfolding eqButUIDf_def by auto
  qed
qed

(* The notion of two functions each taking two userID arguments being
  equal everywhere but on the values (UID1,UID2) and (UID2,UID1): *)
definition eqButUID12 where
"eqButUID12 freq freq1 \<equiv>
 \<forall> uid uid'. if (uid,uid') \<in> {(UID1,UID2), (UID2,UID1)} then True else freq uid uid' = freq1 uid uid'"

lemmas eqButUID12_intro = eqButUID12_def[THEN meta_eq_to_obj_eq, THEN iffD2]

lemma eqButUID12_eeq[simp,intro!]: "eqButUID12 freq freq"
unfolding eqButUID12_def by auto

lemma eqButUID12_sym:
assumes "eqButUID12 freq freq1" shows "eqButUID12 freq1 freq"
using assms unfolding eqButUID12_def
by presburger

lemma eqButUID12_trans:
assumes "eqButUID12 freq freq1" and "eqButUID12 freq1 freq2"
shows "eqButUID12 freq freq2"
using assms unfolding eqButUID12_def by (auto split: if_splits)

lemma eqButUID12_cong:
assumes "eqButUID12 freq freq1"
(*and "uid = UID1 \<Longrightarrow> eqButUID2 uu uu1"*)
and "\<not> (uid,uid') \<in> {(UID1,UID2), (UID2,UID1)} \<Longrightarrow> uu = uu1"
shows "eqButUID12 (fun_upd2 freq uid uid' uu) (fun_upd2 freq1 uid uid' uu1)"
using assms unfolding eqButUID12_def fun_upd2_def by (auto split: if_splits)

lemma eqButUID12_not_UID:
"\<lbrakk>eqButUID12 freq freq1; \<not> (uid,uid') \<in> {(UID1,UID2), (UID2,UID1)}\<rbrakk> \<Longrightarrow> freq uid uid' = freq1 uid uid'"
unfolding eqButUID12_def by (auto split: if_splits)
*)

(* The notion of two states being equal everywhere but on the friendship requests or status of users UID1 and UID2: *)
definition eqButUID :: "state \<Rightarrow> state \<Rightarrow> bool" where
"eqButUID s s1 \<equiv>
 admin s = admin s1 \<and>

 pendingUReqs s = pendingUReqs s1 \<and> userReq s = userReq s1 \<and>
 userIDs s = userIDs s1 \<and> user s = user s1 \<and> pass s = pass s1 \<and>

 pendingFReqs s = pendingFReqs s1 \<and>
 friendReq s = friendReq s1 \<and>
 friendIDs s = friendIDs s1 \<and>

 postIDs s = postIDs s1 \<and> admin s = admin s1 \<and>
 post s = post s1 \<and> vis s = vis s1 \<and>
 owner s = owner s1 \<and>

 pendingSApiReqs s = pendingSApiReqs s1 \<and> sApiReq s = sApiReq s1 \<and>
 serverApiIDs s = serverApiIDs s1 \<and> serverPass s = serverPass s1 \<and>
 outerPostIDs s = outerPostIDs s1 \<and> outerPost s = outerPost s1 \<and> outerVis s = outerVis s1 \<and>
 outerOwner s = outerOwner s1 \<and>
 sentOuterFriendIDs s = sentOuterFriendIDs s1 \<and>
 eqButUIDf (recvOuterFriendIDs s) (recvOuterFriendIDs s1) \<and>

 pendingCApiReqs s = pendingCApiReqs s1 \<and> cApiReq s = cApiReq s1 \<and>
 clientApiIDs s = clientApiIDs s1 \<and> clientPass s = clientPass s1 \<and>
 sharedWith s = sharedWith s1"

lemmas eqButUID_intro = eqButUID_def[THEN meta_eq_to_obj_eq, THEN iffD2]

lemma eqButUID_refl[simp,intro!]: "eqButUID s s"
unfolding eqButUID_def by auto

lemma eqButUID_sym[sym]:
assumes "eqButUID s s1" shows "eqButUID s1 s"
using assms eqButUIDf_sym unfolding eqButUID_def by auto

lemma eqButUID_trans[trans]:
assumes "eqButUID s s1" and "eqButUID s1 s2" shows "eqButUID s s2"
using assms eqButUIDf_trans unfolding eqButUID_def by metis

(* Implications from eqButUID, including w.r.t. auxiliary operations: *)
lemma eqButUID_stateSelectors:
assumes "eqButUID s s1"
shows "admin s = admin s1"
"pendingUReqs s = pendingUReqs s1" "userReq s = userReq s1"
"userIDs s = userIDs s1" "user s = user s1" "pass s = pass s1"
"pendingFReqs s = pendingFReqs s1"
"friendReq s = friendReq s1"
"friendIDs s = friendIDs s1"

"postIDs s = postIDs s1"
"post s = post s1" "vis s = vis s1"
"owner s = owner s1"

"pendingSApiReqs s = pendingSApiReqs s1" "sApiReq s = sApiReq s1"
"serverApiIDs s = serverApiIDs s1" "serverPass s = serverPass s1"
"outerPostIDs s = outerPostIDs s1" "outerPost s = outerPost s1" "outerVis s = outerVis s1"
"outerOwner s = outerOwner s1"
"sentOuterFriendIDs s = sentOuterFriendIDs s1"
"eqButUIDf (recvOuterFriendIDs s) (recvOuterFriendIDs s1)"

"pendingCApiReqs s = pendingCApiReqs s1" "cApiReq s = cApiReq s1"
"clientApiIDs s = clientApiIDs s1" "clientPass s = clientPass s1"
"sharedWith s = sharedWith s1"

"IDsOK s = IDsOK s1"
using assms unfolding eqButUID_def IDsOK_def[abs_def] by auto

lemma eqButUID_UIDs:
"eqButUID s s1 \<Longrightarrow> uid \<in> UIDs AID' \<Longrightarrow> recvOuterFriendIDs s uid = recvOuterFriendIDs s1 uid"
unfolding eqButUID_def eqButUIDf_def by auto

lemma eqButUID_recvOuterFriends_UIDs:
assumes "eqButUID s s1"
and "uid \<noteq> UID \<or> aid \<noteq> AID"
shows "(aid, uid) \<in>\<in> recvOuterFriendIDs s uid' \<longleftrightarrow> (aid, uid) \<in>\<in> recvOuterFriendIDs s1 uid'"
using assms unfolding eqButUID_def eqButUIDf_def
proof -
  have "(aid, uid) \<in>\<in> remove1 (AID,UID) (recvOuterFriendIDs s uid')
    \<longleftrightarrow> (aid, uid) \<in>\<in> remove1 (AID,UID) (recvOuterFriendIDs s1 uid')"
    using assms unfolding eqButUID_def eqButUIDf_def by (cases "uid' \<in> UIDs AID'") auto
  then show ?thesis using assms by auto
qed

lemma eqButUID_remove1_UID_recvOuterFriends:
assumes "eqButUID s s1"
shows "remove1 (AID,UID) (recvOuterFriendIDs s uid) = remove1 (AID,UID) (recvOuterFriendIDs s1 uid)"
using assms unfolding eqButUID_def eqButUIDf_def by (cases "uid \<in> UIDs AID'") auto


lemma eqButUID_cong:
"\<And> uu1 uu2. eqButUID s s1 \<Longrightarrow> uu1 = uu2 \<Longrightarrow> eqButUID (s \<lparr>admin := uu1\<rparr>) (s1 \<lparr>admin := uu2\<rparr>)"

"\<And> uu1 uu2. eqButUID s s1 \<Longrightarrow> uu1 = uu2 \<Longrightarrow> eqButUID (s \<lparr>pendingUReqs := uu1\<rparr>) (s1 \<lparr>pendingUReqs := uu2\<rparr>)"
"\<And> uu1 uu2. eqButUID s s1 \<Longrightarrow> uu1 = uu2 \<Longrightarrow> eqButUID (s \<lparr>userReq := uu1\<rparr>) (s1 \<lparr>userReq := uu2\<rparr>)"
"\<And> uu1 uu2. eqButUID s s1 \<Longrightarrow> uu1 = uu2 \<Longrightarrow> eqButUID (s \<lparr>userIDs := uu1\<rparr>) (s1 \<lparr>userIDs := uu2\<rparr>)"
"\<And> uu1 uu2. eqButUID s s1 \<Longrightarrow> uu1 = uu2 \<Longrightarrow> eqButUID (s \<lparr>user := uu1\<rparr>) (s1 \<lparr>user := uu2\<rparr>)"
"\<And> uu1 uu2. eqButUID s s1 \<Longrightarrow> uu1 = uu2 \<Longrightarrow> eqButUID (s \<lparr>pass := uu1\<rparr>) (s1 \<lparr>pass := uu2\<rparr>)"

"\<And> uu1 uu2. eqButUID s s1 \<Longrightarrow> uu1 = uu2 \<Longrightarrow> eqButUID (s \<lparr>postIDs := uu1\<rparr>) (s1 \<lparr>postIDs := uu2\<rparr>)"
"\<And> uu1 uu2. eqButUID s s1 \<Longrightarrow> uu1 = uu2 \<Longrightarrow> eqButUID (s \<lparr>owner := uu1\<rparr>) (s1 \<lparr>owner := uu2\<rparr>)"
"\<And> uu1 uu2. eqButUID s s1 \<Longrightarrow> uu1 = uu2 \<Longrightarrow> eqButUID (s \<lparr>post := uu1\<rparr>) (s1 \<lparr>post := uu2\<rparr>)"
"\<And> uu1 uu2. eqButUID s s1 \<Longrightarrow> uu1 = uu2 \<Longrightarrow> eqButUID (s \<lparr>vis := uu1\<rparr>) (s1 \<lparr>vis := uu2\<rparr>)"

"\<And> uu1 uu2. eqButUID s s1 \<Longrightarrow> uu1 = uu2 \<Longrightarrow> eqButUID (s \<lparr>pendingFReqs := uu1\<rparr>) (s1 \<lparr>pendingFReqs := uu2\<rparr>)"
"\<And> uu1 uu2. eqButUID s s1 \<Longrightarrow> uu1 = uu2 \<Longrightarrow> eqButUID (s \<lparr>friendReq := uu1\<rparr>) (s1 \<lparr>friendReq := uu2\<rparr>)"
"\<And> uu1 uu2. eqButUID s s1 \<Longrightarrow> uu1 = uu2 \<Longrightarrow> eqButUID (s \<lparr>friendIDs := uu1\<rparr>) (s1 \<lparr>friendIDs := uu2\<rparr>)"

"\<And> uu1 uu2. eqButUID s s1 \<Longrightarrow> uu1 = uu2 \<Longrightarrow> eqButUID (s \<lparr>pendingSApiReqs := uu1\<rparr>) (s1 \<lparr>pendingSApiReqs := uu2\<rparr>)"
"\<And> uu1 uu2. eqButUID s s1 \<Longrightarrow> uu1 = uu2 \<Longrightarrow> eqButUID (s \<lparr>sApiReq := uu1\<rparr>) (s1 \<lparr>sApiReq := uu2\<rparr>)"
"\<And> uu1 uu2. eqButUID s s1 \<Longrightarrow> uu1 = uu2 \<Longrightarrow> eqButUID (s \<lparr>serverApiIDs := uu1\<rparr>) (s1 \<lparr>serverApiIDs := uu2\<rparr>)"
"\<And> uu1 uu2. eqButUID s s1 \<Longrightarrow> uu1 = uu2 \<Longrightarrow> eqButUID (s \<lparr>serverPass := uu1\<rparr>) (s1 \<lparr>serverPass := uu2\<rparr>)"
"\<And> uu1 uu2. eqButUID s s1 \<Longrightarrow> uu1 = uu2 \<Longrightarrow> eqButUID (s \<lparr>outerPostIDs := uu1\<rparr>) (s1 \<lparr>outerPostIDs := uu2\<rparr>)"
"\<And> uu1 uu2. eqButUID s s1 \<Longrightarrow> uu1 = uu2 \<Longrightarrow> eqButUID (s \<lparr>outerPost := uu1\<rparr>) (s1 \<lparr>outerPost := uu2\<rparr>)"
"\<And> uu1 uu2. eqButUID s s1 \<Longrightarrow> uu1 = uu2 \<Longrightarrow> eqButUID (s \<lparr>outerVis := uu1\<rparr>) (s1 \<lparr>outerVis := uu2\<rparr>)"
"\<And> uu1 uu2. eqButUID s s1 \<Longrightarrow> uu1 = uu2 \<Longrightarrow> eqButUID (s \<lparr>outerOwner := uu1\<rparr>) (s1 \<lparr>outerOwner := uu2\<rparr>)"
"\<And> uu1 uu2. eqButUID s s1 \<Longrightarrow> uu1 = uu2 \<Longrightarrow> eqButUID (s \<lparr>sentOuterFriendIDs := uu1\<rparr>) (s1 \<lparr>sentOuterFriendIDs := uu2\<rparr>)"
"\<And> uu1 uu2. eqButUID s s1 \<Longrightarrow> eqButUIDf uu1 uu2 \<Longrightarrow> eqButUID (s \<lparr>recvOuterFriendIDs := uu1\<rparr>) (s1 \<lparr>recvOuterFriendIDs := uu2\<rparr>)"

"\<And> uu1 uu2. eqButUID s s1 \<Longrightarrow> uu1 = uu2 \<Longrightarrow> eqButUID (s \<lparr>pendingCApiReqs := uu1\<rparr>) (s1 \<lparr>pendingCApiReqs := uu2\<rparr>)"
"\<And> uu1 uu2. eqButUID s s1 \<Longrightarrow> uu1 = uu2 \<Longrightarrow> eqButUID (s \<lparr>cApiReq := uu1\<rparr>) (s1 \<lparr>cApiReq := uu2\<rparr>)"
"\<And> uu1 uu2. eqButUID s s1 \<Longrightarrow> uu1 = uu2 \<Longrightarrow> eqButUID (s \<lparr>clientApiIDs := uu1\<rparr>) (s1 \<lparr>clientApiIDs := uu2\<rparr>)"
"\<And> uu1 uu2. eqButUID s s1 \<Longrightarrow> uu1 = uu2 \<Longrightarrow> eqButUID (s \<lparr>clientPass := uu1\<rparr>) (s1 \<lparr>clientPass := uu2\<rparr>)"
"\<And> uu1 uu2. eqButUID s s1 \<Longrightarrow> uu1 = uu2 \<Longrightarrow> eqButUID (s \<lparr>sharedWith := uu1\<rparr>) (s1 \<lparr>sharedWith:= uu2\<rparr>)"
unfolding eqButUID_def by auto

end

end
