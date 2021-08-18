(* The state equivalence used for the unwinding proofs for the friendship confidentiality
   properties *)
theory Outer_Friend_Issuer_State_Indistinguishability
  imports Outer_Friend_Issuer_Observation_Setup
begin

subsubsection \<open>Unwinding helper definitions and lemmas\<close>

context OuterFriendIssuer
begin

fun filterUIDs :: "(apiID \<times> userID) list \<Rightarrow> (apiID \<times> userID) list" where
"filterUIDs auidl = filter (\<lambda>auid. (snd auid) \<in> UIDs (fst auid)) auidl"

fun removeUIDs :: "(apiID \<times> userID) list \<Rightarrow> (apiID \<times> userID) list" where
"removeUIDs auidl = filter (\<lambda>auid. (snd auid) \<notin> UIDs (fst auid)) auidl"

(* The notion of two (apiID \<times> userID) lists being equal on observers: *)
fun eqButUIDs :: "(apiID \<times> userID) list \<Rightarrow> (apiID \<times> userID) list \<Rightarrow> bool" where
"eqButUIDs uidl uidl1 = (filterUIDs uidl = filterUIDs uidl1)"

lemma eqButUIDs_eq[simp,intro!]: "eqButUIDs uidl uidl"
by auto

lemma eqButUIDs_sym:
assumes "eqButUIDs uidl uidl1"
shows "eqButUIDs uidl1 uidl"
using assms by auto

lemma eqButUIDs_trans:
assumes "eqButUIDs uidl uidl1" and "eqButUIDs uidl1 uidl2"
shows "eqButUIDs uidl uidl2"
using assms by auto

lemma eqButUIDs_remove1_cong:
assumes "eqButUIDs uidl uidl1"
shows "eqButUIDs (remove1 auid uidl) (remove1 auid uidl1)"
using assms by (auto simp: filter_remove1)

lemma eqButUIDs_snoc_cong:
assumes "eqButUIDs uidl uidl1"
(*and "uid' \<in>\<in> uidl \<longleftrightarrow> uid' \<in>\<in> uidl1"*)
shows "eqButUIDs (uidl ## auid') (uidl1 ## auid')"
using assms by auto


(* The notion of two functions each taking a userID being equal everywhere but on UID,
   where they are eqButUIDs. *)
definition eqButUIDf where
"eqButUIDf frds frds1 \<equiv>
  eqButUIDs (frds UID) (frds1 UID)
\<and> (\<forall>uid. uid \<noteq> UID \<longrightarrow> frds uid = frds1 uid)"

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
using assms unfolding eqButUIDf_def by auto

lemma eqButUIDf_cong:
assumes "eqButUIDf frds frds1"
and "uid \<noteq> UID \<Longrightarrow> uu = uu1"
and "uid = UID \<Longrightarrow> eqButUIDs uu uu1"
shows "eqButUIDf (frds (uid := uu)) (frds1(uid := uu1))"
using assms unfolding eqButUIDf_def by auto

lemma eqButUIDf_not_UID:
"\<lbrakk>eqButUIDf frds frds1; uid \<noteq> UID\<rbrakk> \<Longrightarrow> frds uid = frds1 uid"
unfolding eqButUIDf_def by (auto split: if_splits)

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
 eqButUIDf (sentOuterFriendIDs s) (sentOuterFriendIDs s1) \<and>
 recvOuterFriendIDs s = recvOuterFriendIDs s1 \<and>

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
"eqButUIDf (sentOuterFriendIDs s) (sentOuterFriendIDs s1)"
"recvOuterFriendIDs s = recvOuterFriendIDs s1"

"pendingCApiReqs s = pendingCApiReqs s1" "cApiReq s = cApiReq s1"
"clientApiIDs s = clientApiIDs s1" "clientPass s = clientPass s1"
"sharedWith s = sharedWith s1"

"IDsOK s = IDsOK s1"
using assms unfolding eqButUID_def IDsOK_def[abs_def] by auto

lemmas eqButUID_eqButUIDf = eqButUID_stateSelectors(22)

lemma eqButUID_eqButUIDs:
"eqButUID s s1 \<Longrightarrow> eqButUIDs (sentOuterFriendIDs s UID) (sentOuterFriendIDs s1 UID)"
unfolding eqButUID_def eqButUIDf_def by auto

lemma eqButUID_not_UID:
"eqButUID s s1 \<Longrightarrow> uid \<noteq> UID \<Longrightarrow> sentOuterFriendIDs s uid = sentOuterFriendIDs s1 uid"
unfolding eqButUID_def eqButUIDf_def by auto

lemma eqButUID_sentOuterFriends_UIDs:
assumes "eqButUID s s1"
and "uid' \<in> UIDs aid"
shows "(aid, uid') \<in>\<in> sentOuterFriendIDs s UID \<longleftrightarrow> (aid, uid') \<in>\<in> sentOuterFriendIDs s1 UID"
proof -
  have "(aid, uid') \<in>\<in> filterUIDs (sentOuterFriendIDs s UID)
    \<longleftrightarrow> (aid, uid') \<in>\<in> filterUIDs (sentOuterFriendIDs s1 UID)"
    using assms unfolding eqButUID_def eqButUIDf_def by auto
  then show ?thesis using assms by auto
qed

lemma eqButUID_sentOuterFriendIDs_cong:
assumes "eqButUID s s1"
and "uid' \<notin> UIDs aid"
shows "eqButUID (s\<lparr>sentOuterFriendIDs := (sentOuterFriendIDs s)(UID := sentOuterFriendIDs s UID ## (aid, uid'))\<rparr>) s1"
and "eqButUID s (s1\<lparr>sentOuterFriendIDs := (sentOuterFriendIDs s1)(UID := sentOuterFriendIDs s1 UID ## (aid, uid'))\<rparr>)"
and "eqButUID s (s1\<lparr>sentOuterFriendIDs := (sentOuterFriendIDs s1)(UID := remove1 (aid, uid') (sentOuterFriendIDs s1 UID))\<rparr>)"
and "eqButUID (s\<lparr>sentOuterFriendIDs := (sentOuterFriendIDs s)(UID := remove1 (aid, uid') (sentOuterFriendIDs s UID))\<rparr>) s1"
using assms unfolding eqButUID_def eqButUIDf_def by (auto simp: filter_remove1)

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
"\<And> uu1 uu2. eqButUID s s1 \<Longrightarrow> eqButUIDf uu1 uu2 \<Longrightarrow> eqButUID (s \<lparr>sentOuterFriendIDs := uu1\<rparr>) (s1 \<lparr>sentOuterFriendIDs := uu2\<rparr>)"
"\<And> uu1 uu2. eqButUID s s1 \<Longrightarrow> uu1 = uu2 \<Longrightarrow> eqButUID (s \<lparr>recvOuterFriendIDs := uu1\<rparr>) (s1 \<lparr>recvOuterFriendIDs := uu2\<rparr>)"

"\<And> uu1 uu2. eqButUID s s1 \<Longrightarrow> uu1 = uu2 \<Longrightarrow> eqButUID (s \<lparr>pendingCApiReqs := uu1\<rparr>) (s1 \<lparr>pendingCApiReqs := uu2\<rparr>)"
"\<And> uu1 uu2. eqButUID s s1 \<Longrightarrow> uu1 = uu2 \<Longrightarrow> eqButUID (s \<lparr>cApiReq := uu1\<rparr>) (s1 \<lparr>cApiReq := uu2\<rparr>)"
"\<And> uu1 uu2. eqButUID s s1 \<Longrightarrow> uu1 = uu2 \<Longrightarrow> eqButUID (s \<lparr>clientApiIDs := uu1\<rparr>) (s1 \<lparr>clientApiIDs := uu2\<rparr>)"
"\<And> uu1 uu2. eqButUID s s1 \<Longrightarrow> uu1 = uu2 \<Longrightarrow> eqButUID (s \<lparr>clientPass := uu1\<rparr>) (s1 \<lparr>clientPass := uu2\<rparr>)"
"\<And> uu1 uu2. eqButUID s s1 \<Longrightarrow> uu1 = uu2 \<Longrightarrow> eqButUID (s \<lparr>sharedWith := uu1\<rparr>) (s1 \<lparr>sharedWith:= uu2\<rparr>)"
unfolding eqButUID_def by auto


lemma distinct_remove1_idem: "distinct xs \<Longrightarrow> remove1 y (remove1 y xs) = remove1 y xs"
by (induction xs) (auto simp add: remove1_idem)

(* major *) lemma eqButUID_step:
assumes ss1: "eqButUID s s1"
and step: "step s a = (ou,s')"
and step1: "step s1 a = (ou1,s1')"
and rs: "reach s"
and rs1: "reach s1"
shows "eqButUID s' s1'"
proof -
  note simps = eqButUID_stateSelectors s_defs c_defs d_defs u_defs r_defs l_defs com_defs
               eqButUID_sentOuterFriends_UIDs eqButUID_not_UID
  from assms show ?thesis proof (cases a)
    case (Sact sa) with assms show ?thesis by (cases sa) (auto simp add: simps intro!: eqButUID_cong)
  next
    case (Cact ca) with assms show ?thesis by (cases ca) (auto simp add: simps intro!: eqButUID_cong)
  next
    case (Uact ua) with assms show ?thesis by (cases ua) (auto simp add: simps intro!: eqButUID_cong)
  next
    case (Ract ra) with assms show ?thesis by (cases ra) (auto simp add: simps intro!: eqButUID_cong)
  next
    case (Lact la) with assms show ?thesis by (cases la) (auto simp add: simps intro!: eqButUID_cong)
  next
    case (COMact ca)
      with assms show ?thesis proof (cases ca)
        case (comSendCreateOFriend uid p aid uid')
          then show ?thesis
            using COMact assms eqButUID_eqButUIDf[OF ss1] eqButUID_eqButUIDs[OF ss1]
            by (cases "uid = UID"; cases "uid' \<in> UIDs aid")
               (auto simp: simps intro!: eqButUID_cong eqButUIDf_cong intro: eqButUID_sentOuterFriendIDs_cong)
      next
        case (comSendDeleteOFriend uid p aid uid')
          then show ?thesis
            using COMact assms eqButUID_eqButUIDf[OF ss1] eqButUID_eqButUIDs[OF ss1]
            by (cases "uid = UID"; cases "uid' \<in> UIDs aid")
               (auto simp: simps filter_remove1 intro!: eqButUID_cong eqButUIDf_cong intro: eqButUID_sentOuterFriendIDs_cong)
      qed (auto simp: simps intro!: eqButUID_cong)
  next
    case (Dact da) with assms show ?thesis by (cases da) (auto simp add: simps intro!: eqButUID_cong)
  qed
qed

end

end
