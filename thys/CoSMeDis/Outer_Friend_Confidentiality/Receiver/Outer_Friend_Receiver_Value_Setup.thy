(* The value setup for outer friendship status confidentiality *)
theory Outer_Friend_Receiver_Value_Setup
  imports Outer_Friend_Receiver_State_Indistinguishability
begin

subsubsection \<open>Value Setup\<close>

context OuterFriendReceiver
begin

fun \<phi> :: "(state,act,out) trans \<Rightarrow> bool" where
"\<phi> (Trans s (COMact (comReceiveCreateOFriend aID cp uID uID')) ou s') =
  (aID = AID \<and> uID = UID \<and> uID' \<notin> UIDs AID' \<and> ou = outOK)"
|
"\<phi> (Trans s (COMact (comReceiveDeleteOFriend aID cp uID uID')) ou s') =
  (aID = AID \<and> uID = UID \<and> uID' \<notin> UIDs AID' \<and> ou = outOK)"
|
"\<phi> _ = False"

fun f :: "(state,act,out) trans \<Rightarrow> value" where
"f (Trans s (COMact (comReceiveCreateOFriend aID cp uID uID')) ou s') = FrVal AID' uID' True"
|
"f (Trans s (COMact (comReceiveDeleteOFriend aID cp uID uID')) ou s') = FrVal AID' uID' False"
|
"f _ = undefined"



lemma recvOFriend_eqButUID:
assumes "step s a = (ou, s')"
and "reach s"
and "a = COMact (comReceiveCreateOFriend AID cp UID uID') \<or> a = COMact (comReceiveDeleteOFriend AID cp UID uID')"
and "uID' \<notin> UIDs AID'"
shows "eqButUID s s'"
using assms reach_distinct_friends_reqs(4) unfolding eqButUID_def eqButUIDf_def
by (auto simp: com_defs remove1_idem remove1_append)


(* major *) lemma eqButUID_step:
assumes ss1: "eqButUID s s1"
and step: "step s a = (ou,s')"
and step1: "step s1 a = (ou1,s1')"
and rs: "reach s"
and rs1: "reach s1"
shows "eqButUID s' s1'"
proof -
  note facts = eqButUID_recvOuterFriends_UIDs[OF ss1] eqButUID_UIDs[OF ss1]
               eqButUID_remove1_UID_recvOuterFriends[OF ss1]
  note simps = eqButUID_stateSelectors s_defs c_defs d_defs u_defs r_defs l_defs com_defs
  note congs = eqButUID_cong eqButUIDf_cong eqButUIDl_snoc_cong eqButUIDl_remove1_cong
  from assms show ?thesis proof (cases a)
    case (Sact sa) with assms show ?thesis by (cases sa) (auto simp: simps congs)
  next
    case (Cact ca) with assms show ?thesis by (cases ca) (auto simp: simps congs)
  next
    case (Uact ua) with assms show ?thesis by (cases ua) (auto simp: simps congs)
  next
    case (Ract ra) with assms show ?thesis by (cases ra) (auto simp: simps congs)
  next
    case (Lact la) with assms show ?thesis by (cases la) (auto simp: simps congs)
  next
    case (COMact ca)
      with assms show ?thesis proof (cases "\<phi> (Trans s a ou s') \<or> \<phi> (Trans s1 a ou1 s1')")
        case True
          then have "eqButUID s s'" and "eqButUID s1 s1'"
            using COMact rs rs1 recvOFriend_eqButUID[OF step] recvOFriend_eqButUID[OF step1]
            by (cases ca; auto)+
          then show "eqButUID s' s1'" using ss1 by (auto intro: eqButUID_sym eqButUID_trans)
      next
        case False
          then show ?thesis using assms facts COMact by (cases ca) (auto simp: simps intro!: congs)
      qed
  next
    case (Dact da) with assms show ?thesis by (cases da) (auto simp: simps congs)
  qed
qed



(* major *) lemma eqButUID_step_\<gamma>_out:
assumes ss1: "eqButUID s s1"
and step: "step s a = (ou,s')" and step1: "step s1 a = (ou1,s1')"
and \<phi>: "\<phi> (Trans s1 a ou1 s1') \<longleftrightarrow> \<phi> (Trans s a ou s')"
and \<gamma>: "\<gamma> (Trans s a ou s')"
shows "ou = ou1"
proof -
  obtain uid com_act where uid_a: "(userOfA a = Some uid \<and> uid \<in> UIDs AID')
                                 \<or> (a = COMact com_act \<and> ou \<noteq> outErr)"
    using \<gamma> UID_UIDs by fastforce
  note simps = eqButUID_stateSelectors eqButUID_UIDs[OF ss1] r_defs s_defs c_defs com_defs l_defs u_defs d_defs
  note facts = ss1 step step1 uid_a
  show ?thesis
  proof (cases a)
    case (Ract ra) then show ?thesis using facts by (cases ra) (auto simp add: simps)
  next
    case (Sact sa) then show ?thesis using facts by (cases sa) (auto simp add: simps)
  next
    case (Cact ca) then show ?thesis using facts by (cases ca) (auto simp add: simps)
  next
    case (COMact ca)
      then show ?thesis using facts proof (cases ca)
        case (comReceiveCreateOFriend aid sp uid uid')
          with facts \<phi> show ?thesis using COMact eqButUID_recvOuterFriends_UIDs[OF ss1]
            by (auto simp: simps)
      next
        case (comReceiveDeleteOFriend aid sp uid uid')
          with facts \<phi> show ?thesis using COMact eqButUID_recvOuterFriends_UIDs[OF ss1]
            by (auto simp: simps)
      qed (auto simp: simps)
  next
    case (Lact la)
      then show ?thesis using facts proof (cases la)
        case (lInnerPosts uid p)
          then have o: "\<And>nid. owner s nid = owner s1 nid"
                and n: "\<And>nid. post s nid = post s1 nid"
                and nids: "postIDs s = postIDs s1"
                and vis: "vis s = vis s1"
                and fu: "\<And>uid'. friendIDs s uid' = friendIDs s1 uid'"
                and e: "e_listInnerPosts s uid p \<longleftrightarrow> e_listInnerPosts s1 uid p"
            using ss1 unfolding eqButUID_def l_defs by auto
          have "listInnerPosts s uid p = listInnerPosts s1 uid p"
            unfolding listInnerPosts_def o n nids vis fu ..
          with e show ?thesis using Lact lInnerPosts step step1 by auto
      qed (auto simp add: simps)
  next
    case (Uact ua) then show ?thesis using facts by (cases ua) (auto simp add: simps)
  next
    case (Dact da) then show ?thesis using facts by (cases da) (auto simp add: simps)
  qed
qed


lemma eqButUID_step_\<gamma>:
assumes ss1: "eqButUID s s1"
and step: "step s a = (ou,s')" and step1: "step s1 a = (ou1,s1')"
and \<phi>: "\<phi> (Trans s1 a ou1 s1') \<longleftrightarrow> \<phi> (Trans s a ou s')"
shows "\<gamma> (Trans s a ou s') = \<gamma> (Trans s1 a ou1 s1')"
using assms eqButUID_step_\<gamma>_out[OF assms] eqButUID_step_\<gamma>_out[OF _ step1 step]
by (auto intro: eqButUID_sym)


end

end
