(* The state equivalence used for the unwinding proofs for the friendship confidentiality
   properties *)
theory Friend_State_Indistinguishability
  imports "Friend_Observation_Setup"
begin

subsection \<open>Unwinding helper definitions and lemmas\<close>

(* The secret: One will be interested in the friendship information of two arbitary,
   but fixed users UID1 and UID2 *)
locale Friend = FriendObservationSetup +
fixes
  UID1 :: userID
and
  UID2 :: userID
assumes
  UID1_UID2_UIDs: "{UID1,UID2} \<inter> UIDs = {}"
and
  UID1_UID2: "UID1 \<noteq> UID2"
begin

(* The notion of two userID lists being equal save for at most one occurrence of uid: *)
fun eqButUIDl :: "userID \<Rightarrow> userID list \<Rightarrow> userID list \<Rightarrow> bool" where
"eqButUIDl uid uidl uidl1 = (remove1 uid uidl = remove1 uid uidl1)"

lemma eqButUIDl_eq[simp,intro!]: "eqButUIDl uid uidl uidl"
by auto

lemma eqButUIDl_sym:
assumes "eqButUIDl uid uidl uidl1"
shows "eqButUIDl uid uidl1 uidl"
using assms by auto

lemma eqButUIDl_trans:
assumes "eqButUIDl uid uidl uidl1" and "eqButUIDl uid uidl1 uidl2"
shows "eqButUIDl uid uidl uidl2"
using assms by auto

lemma eqButUIDl_remove1_cong:
assumes "eqButUIDl uid uidl uidl1"
shows "eqButUIDl uid (remove1 uid' uidl) (remove1 uid' uidl1)"
proof -
  have "remove1 uid (remove1 uid' uidl) = remove1 uid' (remove1 uid uidl)" by (simp add: remove1_commute)
  also have "\<dots> = remove1 uid' (remove1 uid uidl1)" using assms by simp
  also have "\<dots> = remove1 uid (remove1 uid' uidl1)" by (simp add: remove1_commute)
  finally show ?thesis by simp
qed

lemma eqButUIDl_snoc_cong:
assumes "eqButUIDl uid uidl uidl1"
and "uid' \<in>\<in> uidl \<longleftrightarrow> uid' \<in>\<in> uidl1"
shows "eqButUIDl uid (uidl ## uid') (uidl1 ## uid')"
using assms by (auto simp add: remove1_append remove1_idem)

(* The notion of two functions each taking a userID and returning a list of user IDs
  being equal everywhere but on UID1 and UID2, where their return results are allowed
  to be eqButUIDl : *)
definition eqButUIDf where
"eqButUIDf frds frds1 \<equiv>
  eqButUIDl UID2 (frds UID1) (frds1 UID1)
\<and> eqButUIDl UID1 (frds UID2) (frds1 UID2)
\<and> (\<forall>uid. uid \<noteq> UID1 \<and> uid \<noteq> UID2 \<longrightarrow> frds uid = frds1 uid)"

lemmas eqButUIDf_intro = eqButUIDf_def[THEN meta_eq_to_obj_eq, THEN iffD2]

lemma eqButUIDf_eeq[simp,intro!]: "eqButUIDf frds frds"
unfolding eqButUIDf_def by auto

lemma eqButUIDf_sym:
assumes "eqButUIDf frds frds1" shows "eqButUIDf frds1 frds"
using assms eqButUIDl_sym unfolding eqButUIDf_def
by presburger

lemma eqButUIDf_trans:
assumes "eqButUIDf frds frds1" and "eqButUIDf frds1 frds2"
shows "eqButUIDf frds frds2"
using assms eqButUIDl_trans unfolding eqButUIDf_def by (auto split: if_splits)

lemma eqButUIDf_cong:
assumes "eqButUIDf frds frds1"
and "uid = UID1 \<Longrightarrow> eqButUIDl UID2 uu uu1"
and "uid = UID2 \<Longrightarrow> eqButUIDl UID1 uu uu1"
and "uid \<noteq> UID1 \<Longrightarrow> uid \<noteq> UID2 \<Longrightarrow> uu = uu1"
shows "eqButUIDf (frds (uid := uu)) (frds1(uid := uu1))"
using assms unfolding eqButUIDf_def by (auto split: if_splits)

lemma eqButUIDf_eqButUIDl:
assumes "eqButUIDf frds frds1"
shows "eqButUIDl UID2 (frds UID1) (frds1 UID1)"
  and "eqButUIDl UID1 (frds UID2) (frds1 UID2)"
using assms unfolding eqButUIDf_def by (auto split: if_splits)

lemma eqButUIDf_not_UID:
"\<lbrakk>eqButUIDf frds frds1; uid \<noteq> UID1; uid \<noteq> UID2\<rbrakk> \<Longrightarrow> frds uid = frds1 uid"
unfolding eqButUIDf_def by (auto split: if_splits)

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


(* The notion of two states being equal everywhere but on the friendship requests or status of users UID1 and UID2: *)
definition eqButUID :: "state \<Rightarrow> state \<Rightarrow> bool" where
"eqButUID s s1 \<equiv>
 admin s = admin s1 \<and>

 pendingUReqs s = pendingUReqs s1 \<and> userReq s = userReq s1 \<and>
 userIDs s = userIDs s1 \<and> user s = user s1 \<and> pass s = pass s1 \<and>

 eqButUIDf (pendingFReqs s) (pendingFReqs s1) \<and>
 eqButUID12 (friendReq s) (friendReq s1) \<and>
 eqButUIDf (friendIDs s) (friendIDs s1) \<and>

 postIDs s = postIDs s1 \<and> admin s = admin s1 \<and>
 post s = post s1 \<and> vis s = vis s1 \<and>
 owner s = owner s1 \<and>

 pendingSApiReqs s = pendingSApiReqs s1 \<and> sApiReq s = sApiReq s1 \<and>
 serverApiIDs s = serverApiIDs s1 \<and> serverPass s = serverPass s1 \<and>
 outerPostIDs s = outerPostIDs s1 \<and> outerPost s = outerPost s1 \<and> outerVis s = outerVis s1 \<and>
 outerOwner s = outerOwner s1 \<and>
 sentOuterFriendIDs s = sentOuterFriendIDs s1 \<and>
 recvOuterFriendIDs s = recvOuterFriendIDs s1 \<and>

 pendingCApiReqs s = pendingCApiReqs s1 \<and> cApiReq s = cApiReq s1 \<and>
 clientApiIDs s = clientApiIDs s1 \<and> clientPass s = clientPass s1 \<and>
 sharedWith s = sharedWith s1"

lemmas eqButUID_intro = eqButUID_def[THEN meta_eq_to_obj_eq, THEN iffD2]

lemma eqButUID_refl[simp,intro!]: "eqButUID s s"
unfolding eqButUID_def by auto

lemma eqButUID_sym[sym]:
assumes "eqButUID s s1" shows "eqButUID s1 s"
using assms eqButUIDf_sym eqButUID12_sym unfolding eqButUID_def by auto

lemma eqButUID_trans[trans]:
assumes "eqButUID s s1" and "eqButUID s1 s2" shows "eqButUID s s2"
using assms eqButUIDf_trans eqButUID12_trans unfolding eqButUID_def by metis

(* Implications from eqButUID, including w.r.t. auxiliary operations: *)
lemma eqButUID_stateSelectors:
assumes "eqButUID s s1"
shows "admin s = admin s1"
"pendingUReqs s = pendingUReqs s1" "userReq s = userReq s1"
"userIDs s = userIDs s1" "user s = user s1" "pass s = pass s1"
"eqButUIDf (pendingFReqs s) (pendingFReqs s1)"
"eqButUID12 (friendReq s) (friendReq s1)"
"eqButUIDf (friendIDs s) (friendIDs s1)"

"postIDs s = postIDs s1"
"post s = post s1" "vis s = vis s1"
"owner s = owner s1"

"pendingSApiReqs s = pendingSApiReqs s1" "sApiReq s = sApiReq s1"
"serverApiIDs s = serverApiIDs s1" "serverPass s = serverPass s1"
"outerPostIDs s = outerPostIDs s1" "outerPost s = outerPost s1" "outerVis s = outerVis s1"
"outerOwner s = outerOwner s1"
"sentOuterFriendIDs s = sentOuterFriendIDs s1"
"recvOuterFriendIDs s = recvOuterFriendIDs s1"

"pendingCApiReqs s = pendingCApiReqs s1" "cApiReq s = cApiReq s1"
"clientApiIDs s = clientApiIDs s1" "clientPass s = clientPass s1"
"sharedWith s = sharedWith s1"

"IDsOK s = IDsOK s1"
using assms unfolding eqButUID_def IDsOK_def[abs_def] by auto

lemma eqButUID_eqButUID2:
"eqButUID s s1 \<Longrightarrow> eqButUIDl UID2 (friendIDs s UID1) (friendIDs s1 UID1)"
unfolding eqButUID_def using eqButUIDf_eqButUIDl
by (smt eqButUIDf_eqButUIDl eqButUIDl.simps)

lemma eqButUID_not_UID:
"eqButUID s s1 \<Longrightarrow> uid \<noteq> UID \<Longrightarrow> post s uid = post s1 uid"
unfolding eqButUID_def by auto


lemma eqButUID_cong[simp, intro]:
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

"\<And> uu1 uu2. eqButUID s s1 \<Longrightarrow> eqButUIDf uu1 uu2 \<Longrightarrow> eqButUID (s \<lparr>pendingFReqs := uu1\<rparr>) (s1 \<lparr>pendingFReqs := uu2\<rparr>)"
"\<And> uu1 uu2. eqButUID s s1 \<Longrightarrow> eqButUID12 uu1 uu2 \<Longrightarrow> eqButUID (s \<lparr>friendReq := uu1\<rparr>) (s1 \<lparr>friendReq := uu2\<rparr>)"
"\<And> uu1 uu2. eqButUID s s1 \<Longrightarrow> eqButUIDf uu1 uu2 \<Longrightarrow> eqButUID (s \<lparr>friendIDs := uu1\<rparr>) (s1 \<lparr>friendIDs := uu2\<rparr>)"

"\<And> uu1 uu2. eqButUID s s1 \<Longrightarrow> uu1 = uu2 \<Longrightarrow> eqButUID (s \<lparr>pendingSApiReqs := uu1\<rparr>) (s1 \<lparr>pendingSApiReqs := uu2\<rparr>)"
"\<And> uu1 uu2. eqButUID s s1 \<Longrightarrow> uu1 = uu2 \<Longrightarrow> eqButUID (s \<lparr>sApiReq := uu1\<rparr>) (s1 \<lparr>sApiReq := uu2\<rparr>)"
"\<And> uu1 uu2. eqButUID s s1 \<Longrightarrow> uu1 = uu2 \<Longrightarrow> eqButUID (s \<lparr>serverApiIDs := uu1\<rparr>) (s1 \<lparr>serverApiIDs := uu2\<rparr>)"
"\<And> uu1 uu2. eqButUID s s1 \<Longrightarrow> uu1 = uu2 \<Longrightarrow> eqButUID (s \<lparr>serverPass := uu1\<rparr>) (s1 \<lparr>serverPass := uu2\<rparr>)"
"\<And> uu1 uu2. eqButUID s s1 \<Longrightarrow> uu1 = uu2 \<Longrightarrow> eqButUID (s \<lparr>outerPostIDs := uu1\<rparr>) (s1 \<lparr>outerPostIDs := uu2\<rparr>)"
"\<And> uu1 uu2. eqButUID s s1 \<Longrightarrow> uu1 = uu2 \<Longrightarrow> eqButUID (s \<lparr>outerPost := uu1\<rparr>) (s1 \<lparr>outerPost := uu2\<rparr>)"
"\<And> uu1 uu2. eqButUID s s1 \<Longrightarrow> uu1 = uu2 \<Longrightarrow> eqButUID (s \<lparr>outerVis := uu1\<rparr>) (s1 \<lparr>outerVis := uu2\<rparr>)"
"\<And> uu1 uu2. eqButUID s s1 \<Longrightarrow> uu1 = uu2 \<Longrightarrow> eqButUID (s \<lparr>outerOwner := uu1\<rparr>) (s1 \<lparr>outerOwner := uu2\<rparr>)"
"\<And> uu1 uu2. eqButUID s s1 \<Longrightarrow> uu1 = uu2 \<Longrightarrow> eqButUID (s \<lparr>sentOuterFriendIDs := uu1\<rparr>) (s1 \<lparr>sentOuterFriendIDs := uu2\<rparr>)"
"\<And> uu1 uu2. eqButUID s s1 \<Longrightarrow> uu1 = uu2 \<Longrightarrow> eqButUID (s \<lparr>recvOuterFriendIDs := uu1\<rparr>) (s1 \<lparr>recvOuterFriendIDs := uu2\<rparr>)"

"\<And> uu1 uu2. eqButUID s s1 \<Longrightarrow> uu1 = uu2 \<Longrightarrow> eqButUID (s \<lparr>pendingCApiReqs := uu1\<rparr>) (s1 \<lparr>pendingCApiReqs := uu2\<rparr>)"
"\<And> uu1 uu2. eqButUID s s1 \<Longrightarrow> uu1 = uu2 \<Longrightarrow> eqButUID (s \<lparr>cApiReq := uu1\<rparr>) (s1 \<lparr>cApiReq := uu2\<rparr>)"
"\<And> uu1 uu2. eqButUID s s1 \<Longrightarrow> uu1 = uu2 \<Longrightarrow> eqButUID (s \<lparr>clientApiIDs := uu1\<rparr>) (s1 \<lparr>clientApiIDs := uu2\<rparr>)"
"\<And> uu1 uu2. eqButUID s s1 \<Longrightarrow> uu1 = uu2 \<Longrightarrow> eqButUID (s \<lparr>clientPass := uu1\<rparr>) (s1 \<lparr>clientPass := uu2\<rparr>)"
"\<And> uu1 uu2. eqButUID s s1 \<Longrightarrow> uu1 = uu2 \<Longrightarrow> eqButUID (s \<lparr>sharedWith := uu1\<rparr>) (s1 \<lparr>sharedWith:= uu2\<rparr>)"
unfolding eqButUID_def by auto

definition "friends12" :: "state \<Rightarrow> bool"
where "friends12 s \<equiv> UID1 \<in>\<in> friendIDs s UID2 \<and> UID2 \<in>\<in> friendIDs s UID1"

lemma step_friendIDs:
assumes "step s a = (ou, s')"
and "a \<noteq> Cact (cFriend uid (pass s uid) uid') \<and> a \<noteq> Cact (cFriend uid' (pass s uid') uid) \<and>
     a \<noteq> Dact (dFriend uid (pass s uid) uid') \<and> a \<noteq> Dact (dFriend uid' (pass s uid') uid)"
shows "uid \<in>\<in> friendIDs s' uid' \<longleftrightarrow> uid \<in>\<in> friendIDs s uid'" (is ?uid)
  and "uid' \<in>\<in> friendIDs s' uid \<longleftrightarrow> uid' \<in>\<in> friendIDs s uid" (is ?uid')
proof -
  from assms have "?uid \<and> ?uid'"
  proof (cases a)
    case (Sact sa) then show ?thesis using assms by (cases sa) (auto simp: s_defs) next
    case (Uact ua) then show ?thesis using assms by (cases ua) (auto simp: u_defs) next
    case (COMact ca) then show ?thesis using assms by (cases ca) (auto simp: com_defs) next
    case (Cact ca) then show ?thesis using assms by (cases ca) (auto simp: c_defs) next
    case (Dact da) then show ?thesis using assms by (cases da) (auto simp: d_defs)
  qed auto
  then show ?uid and ?uid' by auto
qed

lemma step_friends12:
assumes "step s a = (ou, s')"
and "a \<noteq> Cact (cFriend UID1 (pass s UID1) UID2) \<and> a \<noteq> Cact (cFriend UID2 (pass s UID2) UID1) \<and>
     a \<noteq> Dact (dFriend UID1 (pass s UID1) UID2) \<and> a \<noteq> Dact (dFriend UID2 (pass s UID2) UID1)"
shows "friends12 s' \<longleftrightarrow> friends12 s"
using step_friendIDs[OF assms] unfolding friends12_def by auto

lemma step_pendingFReqs:
assumes step: "step s a = (ou, s')"
and "\<forall>req. a \<noteq> Cact (cFriend uid (pass s uid) uid') \<and> a \<noteq> Cact (cFriend uid' (pass s uid') uid) \<and>
           a \<noteq> Dact (dFriend uid (pass s uid) uid') \<and> a \<noteq> Dact (dFriend uid' (pass s uid') uid) \<and>
           a \<noteq> Cact (cFriendReq uid (pass s uid) uid' req) \<and>
           a \<noteq> Cact (cFriendReq uid' (pass s uid') uid req)"
shows "uid \<in>\<in> pendingFReqs s' uid' \<longleftrightarrow> uid \<in>\<in> pendingFReqs s uid'" (is ?uid)
  and "uid' \<in>\<in> pendingFReqs s' uid \<longleftrightarrow> uid' \<in>\<in> pendingFReqs s uid" (is ?uid')
proof -
  from assms have "?uid \<and> ?uid'"
  proof (cases a)
    case (Sact sa) then show ?thesis using assms by (cases sa) (auto simp: s_defs) next
    case (Uact ua) then show ?thesis using assms by (cases ua) (auto simp: u_defs) next
    case (COMact ca) then show ?thesis using assms by (cases ca) (auto simp: com_defs) next
    case (Cact ca) then show ?thesis using assms proof (cases ca)
      case (cFriend uid1 p uid1')
        then have "((uid1 = uid \<longrightarrow> uid1' \<noteq> uid') \<and> (uid1 = uid' \<longrightarrow> uid1' \<noteq> uid)) \<or> ou = outErr"
          using Cact assms by (auto simp: c_defs)
        then show ?thesis using step Cact cFriend by (auto simp: c_defs)
    qed (auto simp: c_defs) next
    case (Dact da) then show ?thesis using assms by (cases da) (auto simp: d_defs)
  qed auto
  then show ?uid and ?uid' by auto
qed

lemma eqButUID_friends12_set_friendIDs_eq:
assumes ss1: "eqButUID s s1"
and f12: "friends12 s = friends12 s1"
and rs: "reach s" and rs1: "reach s1"
shows "set (friendIDs s uid) = set (friendIDs s1 uid)"
proof -
  have dfIDs: "distinct (friendIDs s uid)" "distinct (friendIDs s1 uid)"
    using reach_distinct_friends_reqs[OF rs] reach_distinct_friends_reqs[OF rs1] by auto
  from f12 have uid12: "UID1 \<in>\<in> friendIDs s UID2 \<longleftrightarrow> UID1 \<in>\<in> friendIDs s1 UID2"
                       "UID2 \<in>\<in> friendIDs s UID1 \<longleftrightarrow> UID2 \<in>\<in> friendIDs s1 UID1"
    using reach_friendIDs_symmetric[OF rs] reach_friendIDs_symmetric[OF rs1]
    unfolding friends12_def by auto
  from ss1 have fIDs: "eqButUIDf (friendIDs s) (friendIDs s1)" unfolding eqButUID_def by simp
  show "set (friendIDs s uid) = set (friendIDs s1 uid)"
  proof (intro equalityI subsetI)
    fix uid'
    assume "uid' \<in>\<in> friendIDs s uid"
    then show "uid' \<in>\<in> friendIDs s1 uid"
      using fIDs dfIDs uid12 eqButUIDf_not_UID' unfolding eqButUIDf_def
      by (metis (no_types, lifting) insert_iff prod.inject singletonD)
  next
    fix uid'
    assume "uid' \<in>\<in> friendIDs s1 uid"
    then show "uid' \<in>\<in> friendIDs s uid"
      using fIDs dfIDs uid12 eqButUIDf_not_UID' unfolding eqButUIDf_def
      by (metis (no_types, lifting) insert_iff prod.inject singletonD)
  qed
qed


lemma distinct_remove1_idem: "distinct xs \<Longrightarrow> remove1 y (remove1 y xs) = remove1 y xs"
by (induction xs) (auto simp add: remove1_idem)

lemma Cact_cFriend_step_eqButUID:
assumes step: "step s (Cact (cFriend uid p uid')) = (ou,s')"
and s: "reach s"
and uids: "(uid = UID1 \<and> uid' = UID2) \<or> (uid = UID2 \<and> uid' = UID1)" (is "?u12 \<or> ?u21")
shows "eqButUID s s'"
using assms proof (cases)
  assume ou: "ou = outOK"
  then have "uid' \<in>\<in> pendingFReqs s uid" using step by (auto simp add: c_defs)
  then have fIDs: "uid' \<notin> set (friendIDs s uid)" "uid \<notin> set (friendIDs s uid')"
        and fRs: "distinct (pendingFReqs s uid)" "distinct (pendingFReqs s uid')"
    using reach_distinct_friends_reqs[OF s] by auto
  have "eqButUIDf (friendIDs s) (friendIDs (createFriend s uid p uid'))"
    using fIDs uids UID1_UID2 unfolding eqButUIDf_def
    by (cases "?u12") (auto simp add: c_defs remove1_idem remove1_append)
  moreover have "eqButUIDf (pendingFReqs s) (pendingFReqs (createFriend s uid p uid'))"
    using fRs uids UID1_UID2 unfolding eqButUIDf_def
    by (cases "?u12") (auto simp add: c_defs distinct_remove1_idem)
  moreover have "eqButUID12 (friendReq s) (friendReq (createFriend s uid p uid'))"
    using uids unfolding eqButUID12_def
    by (auto simp add: c_defs fun_upd2_eq_but_a_b)
  ultimately show "eqButUID s s'" using step ou unfolding eqButUID_def by (auto simp add: c_defs)
qed (auto)

lemma Cact_cFriendReq_step_eqButUID:
assumes step: "step s (Cact (cFriendReq uid p uid' req)) = (ou,s')"
and uids: "(uid = UID1 \<and> uid' = UID2) \<or> (uid = UID2 \<and> uid' = UID1)" (is "?u12 \<or> ?u21")
shows "eqButUID s s'"
using assms proof (cases)
  assume ou: "ou = outOK"
  then have "uid \<notin> set (pendingFReqs s uid')" "uid \<notin> set (friendIDs s uid')"
    using step by (auto simp add: c_defs)
  then have "eqButUIDf (pendingFReqs s) (pendingFReqs (createFriendReq s uid p uid' req))"
    using uids UID1_UID2 unfolding eqButUIDf_def
    by (cases "?u12") (auto simp add: c_defs remove1_idem remove1_append)
  moreover have "eqButUID12 (friendReq s) (friendReq (createFriendReq s uid p uid' req))"
    using uids unfolding eqButUID12_def
    by (auto simp add: c_defs fun_upd2_eq_but_a_b)
  ultimately show "eqButUID s s'" using step ou unfolding eqButUID_def by (auto simp add: c_defs)
qed (auto)


lemma Dact_dFriend_step_eqButUID:
assumes step: "step s (Dact (dFriend uid p uid')) = (ou,s')"
and s: "reach s"
and uids: "(uid = UID1 \<and> uid' = UID2) \<or> (uid = UID2 \<and> uid' = UID1)" (is "?u12 \<or> ?u21")
shows "eqButUID s s'"
using assms proof (cases)
  assume ou: "ou = outOK"
  then have "uid' \<in>\<in> friendIDs s uid" using step by (auto simp add: d_defs)
  then have fRs: "distinct (friendIDs s uid)" "distinct (friendIDs s uid')"
    using reach_distinct_friends_reqs[OF s] by auto
  have "eqButUIDf (friendIDs s) (friendIDs (deleteFriend s uid p uid'))"
    using fRs uids UID1_UID2 unfolding eqButUIDf_def
    by (cases "?u12") (auto simp add: d_defs remove1_idem distinct_remove1_removeAll)
  then show "eqButUID s s'" using step ou unfolding eqButUID_def by (auto simp add: d_defs)
qed (auto)


(* major *) lemma eqButUID_step:
assumes ss1: "eqButUID s s1"
and step: "step s a = (ou,s')"
and step1: "step s1 a = (ou1,s1')"
and rs: "reach s"
and rs1: "reach s1"
shows "eqButUID s' s1'"
proof -
  note simps = eqButUID_stateSelectors s_defs c_defs u_defs r_defs l_defs com_defs
  from assms show ?thesis proof (cases a)
    case (Sact sa) with assms show ?thesis by (cases sa) (auto simp add: simps)
  next
    case (Cact ca) note a = this
      with assms show ?thesis proof (cases ca)
        case (cFriendReq uid p uid' req) note ca = this
          then show ?thesis
          proof (cases "(uid = UID1 \<and> uid' = UID2) \<or> (uid = UID2 \<and> uid' = UID1)")
            case True
              then have "eqButUID s s'" and "eqButUID s1 s1'"
                using step step1 unfolding a ca
                by (auto intro: Cact_cFriendReq_step_eqButUID)
              with ss1 show "eqButUID s' s1'" by (auto intro: eqButUID_sym eqButUID_trans)
          next
            case False
              have fRs: "eqButUIDf (pendingFReqs s) (pendingFReqs s1)"
               and fIDs: "eqButUIDf (friendIDs s) (friendIDs s1)" using ss1 by (auto simp: simps)
              then have uid_uid': "uid \<in>\<in> pendingFReqs s uid' \<longleftrightarrow> uid \<in>\<in> pendingFReqs s1 uid'"
                                  "uid \<in>\<in> friendIDs s uid' \<longleftrightarrow> uid \<in>\<in> friendIDs s1 uid'"
                using False by (auto intro!: eqButUIDf_not_UID')
              have "eqButUIDf ((pendingFReqs s)(uid' := pendingFReqs s uid' ## uid))
                              ((pendingFReqs s1)(uid' := pendingFReqs s1 uid' ## uid))"
                using fRs False
                by (intro eqButUIDf_cong) (auto simp add: remove1_append remove1_idem eqButUIDf_def)
              moreover have "eqButUID12 (fun_upd2 (friendReq s) uid uid' req)
                                        (fun_upd2 (friendReq s1) uid uid' req)"
                using ss1 by (intro eqButUID12_cong) (auto simp: simps)
              moreover have "e_createFriendReq s uid p uid' req
                         \<longleftrightarrow> e_createFriendReq s1 uid p uid' req"
                using uid_uid' ss1 by (auto simp: simps)
              ultimately show ?thesis using assms unfolding a ca by (auto simp: simps)
          qed
      next
        case (cFriend uid p uid') note ca = this
          then show ?thesis
          proof (cases "(uid = UID1 \<and> uid' = UID2) \<or> (uid = UID2 \<and> uid' = UID1)")
            case True
              then have "eqButUID s s'" and "eqButUID s1 s1'"
                using step step1 rs rs1 unfolding a ca
                by (auto intro!: Cact_cFriend_step_eqButUID)+
              with ss1 show "eqButUID s' s1'" by (auto intro: eqButUID_sym eqButUID_trans)
          next
            case False
              have fRs: "eqButUIDf (pendingFReqs s) (pendingFReqs s1)"
                    (is "eqButUIDf (?pfr s) (?pfr s1)")
               and fIDs: "eqButUIDf (friendIDs s) (friendIDs s1)" using ss1 by (auto simp: simps)
              then have uid_uid': "uid \<in>\<in> pendingFReqs s uid' \<longleftrightarrow> uid \<in>\<in> pendingFReqs s1 uid'"
                                  "uid' \<in>\<in> pendingFReqs s uid \<longleftrightarrow> uid' \<in>\<in> pendingFReqs s1 uid"
                                  "uid \<in>\<in> friendIDs s uid' \<longleftrightarrow> uid \<in>\<in> friendIDs s1 uid'"
                                  "uid' \<in>\<in> friendIDs s uid \<longleftrightarrow> uid' \<in>\<in> friendIDs s1 uid"
                using False by (auto intro!: eqButUIDf_not_UID')
              have "eqButUIDl UID1 (remove1 uid' (?pfr s UID2)) (remove1 uid' (?pfr s1 UID2))"
               and "eqButUIDl UID2 (remove1 uid' (?pfr s UID1)) (remove1 uid' (?pfr s1 UID1))"
               and "eqButUIDl UID1 (remove1 uid (?pfr s UID2)) (remove1 uid (?pfr s1 UID2))"
               and "eqButUIDl UID2 (remove1 uid (?pfr s UID1)) (remove1 uid (?pfr s1 UID1))"
               using fRs unfolding eqButUIDf_def
               by (auto intro!: eqButUIDl_remove1_cong simp del: eqButUIDl.simps)
              then have 1: "eqButUIDf ((?pfr s)(uid := remove1 uid' (?pfr s uid),
                                                uid' := remove1 uid (?pfr s uid')))
                                     ((?pfr s1)(uid := remove1 uid' (?pfr s1 uid),
                                                uid' := remove1 uid (?pfr s1 uid')))"
                using fRs False
                by (intro eqButUIDf_cong) (auto simp add: eqButUIDf_def)
              have "uid = UID1 \<Longrightarrow> eqButUIDl UID2 (friendIDs s UID1 ## uid') (friendIDs s1 UID1 ## uid')"
               and "uid = UID2 \<Longrightarrow> eqButUIDl UID1 (friendIDs s UID2 ## uid') (friendIDs s1 UID2 ## uid')"
               and "uid' = UID1 \<Longrightarrow> eqButUIDl UID2 (friendIDs s UID1 ## uid) (friendIDs s1 UID1 ## uid)"
               and "uid' = UID2 \<Longrightarrow> eqButUIDl UID1 (friendIDs s UID2 ## uid) (friendIDs s1 UID2 ## uid)"
                using fIDs uid_uid' by - (intro eqButUIDl_snoc_cong; simp add: eqButUIDf_def)+
              then have 2: "eqButUIDf ((friendIDs s)(uid := friendIDs s uid ## uid',
                                                      uid' := friendIDs s uid' ## uid))
                                       ((friendIDs s1)(uid := friendIDs s1 uid ## uid',
                                                       uid' := friendIDs s1 uid' ## uid))"
                using fIDs by (intro eqButUIDf_cong) (auto simp add: eqButUIDf_def)
              have 3: "eqButUID12 (fun_upd2 (fun_upd2 (friendReq s) uid' uid emptyRequestInfo)
                                                                    uid uid' emptyRequestInfo)
                                  (fun_upd2 (fun_upd2 (friendReq s1) uid' uid emptyRequestInfo)
                                                                     uid uid' emptyRequestInfo)"
                using ss1 by (intro eqButUID12_cong) (auto simp: simps)
              have "e_createFriend s uid p uid'
                \<longleftrightarrow> e_createFriend s1 uid p uid'"
                using uid_uid' ss1 by (auto simp: simps)
              with 1 2 3 show ?thesis using assms unfolding a ca by (auto simp: simps)
          qed
      qed (auto simp: simps)
  next
    case (Uact ua) with assms show ?thesis by (cases ua) (auto simp add: simps)
  next
    case (Ract ra) with assms show ?thesis by (cases ra) (auto simp add: simps)
  next
    case (Lact la) with assms show ?thesis by (cases la) (auto simp add: simps)
  next
    case (COMact ca) with assms show ?thesis by (cases ca) (auto simp add: simps)
  next
    case (Dact da) note a = this
      with assms show ?thesis proof (cases da)
        case (dFriend uid p uid') note ca = this
          then show ?thesis
          proof (cases "(uid = UID1 \<and> uid' = UID2) \<or> (uid = UID2 \<and> uid' = UID1)")
            case True
              then have "eqButUID s s'" and "eqButUID s1 s1'"
                using step step1 rs rs1 unfolding a ca
                by (auto intro!: Dact_dFriend_step_eqButUID)+
              with ss1 show "eqButUID s' s1'" by (auto intro: eqButUID_sym eqButUID_trans)
          next
            case False
              have fIDs: "eqButUIDf (friendIDs s) (friendIDs s1)" using ss1 by (auto simp: simps)
              then have uid_uid': "uid \<in>\<in> friendIDs s uid' \<longleftrightarrow> uid \<in>\<in> friendIDs s1 uid'"
                                  "uid' \<in>\<in> friendIDs s uid \<longleftrightarrow> uid' \<in>\<in> friendIDs s1 uid"
                using False by (auto intro!: eqButUIDf_not_UID')
              have dfIDs: "distinct (friendIDs s uid)" "distinct (friendIDs s uid')"
                          "distinct (friendIDs s1 uid)" "distinct (friendIDs s1 uid')"
                using reach_distinct_friends_reqs[OF rs] reach_distinct_friends_reqs[OF rs1] by auto
              have "uid = UID1 \<Longrightarrow> eqButUIDl UID2 (remove1 uid' (friendIDs s UID1)) (remove1 uid' (friendIDs s1 UID1))"
               and "uid = UID2 \<Longrightarrow> eqButUIDl UID1 (remove1 uid' (friendIDs s UID2)) (remove1 uid' (friendIDs s1 UID2))"
               and "uid' = UID1 \<Longrightarrow> eqButUIDl UID2 (remove1 uid (friendIDs s UID1)) (remove1 uid (friendIDs s1 UID1))"
               and "uid' = UID2 \<Longrightarrow> eqButUIDl UID1 (remove1 uid (friendIDs s UID2)) (remove1 uid (friendIDs s1 UID2))"
                using fIDs uid_uid' by - (intro eqButUIDl_remove1_cong; simp add: eqButUIDf_def)+
              then have 1: "eqButUIDf ((friendIDs s)(uid := remove1 uid' (friendIDs s uid),
                                                      uid' := remove1 uid (friendIDs s uid')))
                                       ((friendIDs s1)(uid := remove1 uid' (friendIDs s1 uid),
                                                       uid' := remove1 uid (friendIDs s1 uid')))"
                using fIDs by (intro eqButUIDf_cong) (auto simp add: eqButUIDf_def)
              have "e_deleteFriend s uid p uid'
                \<longleftrightarrow> e_deleteFriend s1 uid p uid'"
                using uid_uid' ss1 by (auto simp: simps d_defs)
              with 1 show ?thesis using assms dfIDs unfolding a ca
                by (auto simp: simps d_defs distinct_remove1_removeAll)
          qed
      qed
  qed
qed

lemma eqButUID_step_friendIDs_eq:
assumes ss1: "eqButUID s s1"
and rs: "reach s" and rs1: "reach s1"
and step: "step s a = (ou,s')" and step1: "step s1 a = (ou1,s1')"
and a: "a \<noteq> Cact (cFriend UID1 (pass s UID1) UID2) \<and> a \<noteq> Cact (cFriend UID2 (pass s UID2) UID1) \<and>
        a \<noteq> Dact (dFriend UID1 (pass s UID1) UID2) \<and> a \<noteq> Dact (dFriend UID2 (pass s UID2) UID1)"
and "friendIDs s = friendIDs s1"
shows "friendIDs s' = friendIDs s1'"
using assms proof (cases a)
  case (Sact sa) then show ?thesis using assms by (cases sa) (auto simp: s_defs) next
  case (Uact ua) then show ?thesis using assms by (cases ua) (auto simp: u_defs) next
  case (COMact ca) then show ?thesis using assms by (cases ca) (auto simp: com_defs) next
  case (Dact da) then show ?thesis using assms proof (cases da)
    case (dFriend uid p uid')
      with Dact assms show ?thesis
        by (cases "(uid,uid') \<in> {(UID1,UID2), (UID2,UID1)}")
           (auto simp: d_defs eqButUID_stateSelectors eqButUIDf_not_UID')
    qed
next
  case (Cact ca) then show ?thesis using assms proof (cases ca)
    case (cFriend uid p uid')
      { assume "p = pass s uid"
        then have "uid' \<in>\<in> pendingFReqs s uid \<longleftrightarrow> uid' \<in>\<in> pendingFReqs s1 uid"
          using Cact cFriend ss1 a by (intro eqButUIDf_not_UID') (auto simp: eqButUID_stateSelectors)
      }
      with Cact cFriend assms show ?thesis
        by (auto simp: c_defs eqButUID_stateSelectors)
    qed (auto simp: c_defs)
qed auto

lemma createFriend_sym: "createFriend s uid p uid' = createFriend s uid' p' uid"
unfolding c_defs by (cases "uid = uid'") (auto simp: fun_upd2_comm fun_upd_twist)

lemma deleteFriend_sym: "deleteFriend s uid p uid' = deleteFriend s uid' p' uid"
unfolding d_defs by (cases "uid = uid'") (auto simp: fun_upd_twist)

lemma createFriendReq_createFriend_absorb:
assumes "e_createFriendReq s uid' p uid req"
shows "createFriend (createFriendReq s uid' p1 uid req) uid p2 uid' = createFriend s uid p3 uid'"
using assms unfolding c_defs by (auto simp: remove1_idem remove1_append fun_upd2_absorb)

lemma eqButUID_deleteFriend12_friendIDs_eq:
assumes ss1: "eqButUID s s1"
and rs: "reach s" and rs1: "reach s1"
shows "friendIDs (deleteFriend s UID1 p UID2) = friendIDs (deleteFriend s1 UID1 p' UID2)"
proof -
  have "distinct (friendIDs s UID1)" "distinct (friendIDs s UID2)"
       "distinct (friendIDs s1 UID1)" "distinct (friendIDs s1 UID2)"
    using rs rs1 by (auto intro: reach_distinct_friends_reqs)
  then show ?thesis
    using ss1 unfolding eqButUID_def eqButUIDf_def unfolding d_defs
    by (auto simp: distinct_remove1_removeAll)
qed

lemma eqButUID_createFriend12_friendIDs_eq:
assumes ss1: "eqButUID s s1"
and rs: "reach s" and rs1: "reach s1"
and f12: "\<not>friends12 s" "\<not>friends12 s1"
shows "friendIDs (createFriend s UID1 p UID2) = friendIDs (createFriend s1 UID1 p' UID2)"
proof -
  have f12': "UID1 \<notin> set (friendIDs s UID2)" "UID2 \<notin> set (friendIDs s UID1)"
             "UID1 \<notin> set (friendIDs s1 UID2)" "UID2 \<notin> set (friendIDs s1 UID1)"
    using f12 rs rs1 reach_friendIDs_symmetric unfolding friends12_def by auto
  have "friendIDs s = friendIDs s1"
  proof (intro ext)
    fix uid
    show "friendIDs s uid = friendIDs s1 uid"
      using ss1 f12' unfolding eqButUID_def eqButUIDf_def
      by (cases "uid = UID1 \<or> uid = UID2") (auto simp: remove1_idem)
  qed
  then show ?thesis by (auto simp: c_defs)
qed

end

end
