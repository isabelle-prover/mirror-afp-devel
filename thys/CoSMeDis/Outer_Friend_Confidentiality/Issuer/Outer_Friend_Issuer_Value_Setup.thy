(* The value setup for outer friendship status confidentiality *)
theory Outer_Friend_Issuer_Value_Setup
  imports Outer_Friend_Issuer_Openness
begin

subsubsection \<open>Value setup\<close>

context OuterFriendIssuer
begin

fun \<phi> :: "(state,act,out) trans \<Rightarrow> bool" where
"\<phi> (Trans s (COMact (comSendCreateOFriend uID p aID uID')) ou s') =
  (uID = UID \<and> uID' \<notin> UIDs aID \<and> ou \<noteq> outErr)"
|
"\<phi> (Trans s (COMact (comSendDeleteOFriend uID p aID uID')) ou s') =
  (uID = UID \<and> uID' \<notin> UIDs aID \<and> ou \<noteq> outErr)"
|
"\<phi> (Trans s _ _ s') = (open s \<noteq> open s')"

fun f :: "(state,act,out) trans \<Rightarrow> value" where
"f (Trans s (COMact (comSendCreateOFriend uID p aID uID')) ou s') = FrVal aID uID' True"
|
"f (Trans s (COMact (comSendDeleteOFriend uID p aID uID')) ou s') = FrVal aID uID' False"
|
"f (Trans s _ _ s') = OVal (open s')"


lemma \<phi>E:
assumes \<phi>: "\<phi> (Trans s a ou s')" (is "\<phi> ?trn")
and step: "step s a = (ou, s')"
and rs: "reach s"
obtains
  (Friend) p aID uID' where "a = COMact (comSendCreateOFriend UID p aID uID')" "ou \<noteq> outErr"
                            "f ?trn = FrVal aID uID' True" "uID' \<notin> UIDs aID"
| (Unfriend) p aID uID' where "a = COMact (comSendDeleteOFriend UID p aID uID')" "ou \<noteq> outErr"
                              "f ?trn = FrVal aID uID' False" "uID' \<notin> UIDs aID"
| (OpenF) uid p uid' where "a = Cact (cFriend uid p uid')" "ou = outOK" "p = pass s uid"
                           "uid \<in> UIDs AID \<and> uid' = UID \<or> uid = UID \<and> uid' \<in> UIDs AID"
                           "open s'" "\<not>open s"
                           "f ?trn = OVal True"
| (CloseF) uid p uid' where "a = Dact (dFriend uid p uid')" "ou = outOK" "p = pass s uid"
                            "uid \<in> UIDs AID \<and> uid' = UID \<or> uid = UID \<and> uid' \<in> UIDs AID"
                            "open s" "\<not>open s'"
                            "f ?trn = OVal False"
proof cases
  assume "open s = open s'"
  with \<phi> show thesis by (elim \<phi>.elims) (auto intro: Friend Unfriend)
next
  assume "open s \<noteq> open s'"
  then show thesis proof (elim open_step_cases[OF _ step], goal_cases)
    case 1 then show ?case by (intro OpenF) auto next
    case 2 then show ?case by (intro CloseF) auto
  qed
qed


(* major *) lemma eqButUID_step_\<gamma>_out:
assumes ss1: "eqButUID s s1"
and step: "step s a = (ou,s')" and step1: "step s1 a = (ou1,s1')"
(*and sT: "reachNT s" and s1: "reachNT s1"*)
and \<gamma>: "\<gamma> (Trans s a ou s')"
and os1: "\<not>open s1"
and \<phi>: "\<phi> (Trans s1 a ou1 s1') \<longleftrightarrow> \<phi> (Trans s a ou s')"
shows "ou = ou1"
proof -
  obtain uid sa com_act where uid_a: "(userOfA a = Some uid \<and> uid \<in> UIDs AID \<and> uid \<noteq> UID)
                                      \<or> a = COMact com_act \<or> a = Sact sa"
    using \<gamma> UID_UIDs by fastforce
  note simps = eqButUID_not_UID eqButUID_stateSelectors r_defs s_defs c_defs com_defs l_defs u_defs d_defs
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
        case (comSendCreateOFriend uID p aID uID')
          with facts \<phi> show ?thesis using COMact eqButUID_sentOuterFriends_UIDs[OF ss1]
            by (cases "uID = UID") (auto simp: simps)
      next
        case (comSendDeleteOFriend uID p aID uID')
          with facts \<phi> show ?thesis using COMact eqButUID_sentOuterFriends_UIDs[OF ss1]
            by (cases "uID = UID") (auto simp: simps)
      qed (auto simp: simps)
  next
    case (Lact la)
      then show ?thesis using facts proof (cases la)
        case (lSentOuterFriends uID p uID')
          with Lact facts os1 show ?thesis by (cases "uID' = UID") (auto simp: simps open_def)
      next
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



lemma step_open_\<phi>:
assumes "step s a = (ou, s')"
and "open s \<noteq> open s'"
shows "\<phi> (Trans s a ou s')"
using assms by (elim open_step_cases) (auto simp: open_def)

lemma step_sendOFriend_eqButUID:
assumes "step s a = (ou, s')"
and "reach s"
and "uID' \<notin> UIDs aID"
and "a = COMact (comSendCreateOFriend UID (pass s UID) aID uID') \<or>
     a = COMact (comSendDeleteOFriend UID (pass s UID) aID uID')"
shows "eqButUID s s'"
using assms proof cases
  assume "\<phi> (Trans s a ou s')"
  then show "eqButUID s s'" using assms proof (cases rule: \<phi>E)
    case (Friend p aid uid')
      then show ?thesis
        using assms eqButUID_sentOuterFriendIDs_cong[of s s]
        by (auto split: prod.splits simp: com_defs)
  next
    case (Unfriend p aid uid')
      then show ?thesis
        using assms eqButUID_sentOuterFriendIDs_cong[of s s]
        by (auto split: prod.splits simp: com_defs)
  qed auto
qed (auto split: prod.splits)

lemma eqButUID_step_\<phi>_imp:
assumes ss1: "eqButUID s s1"
and rs: "reach s" and rs1: "reach s1"
and step: "step s a = (ou,s')" and step1: "step s1 a = (ou1,s1')"
and a: "\<forall>aID uID'. uID' \<notin> UIDs aID \<longrightarrow>
                   a \<noteq> COMact (comSendCreateOFriend UID (pass s UID) aID uID') \<and>
                   a \<noteq> COMact (comSendDeleteOFriend UID (pass s UID) aID uID')"
and \<phi>: "\<phi> (Trans s a ou s')"
shows "\<phi> (Trans s1 a ou1 s1')"
proof -
  have "eqButUID s' s1'" using eqButUID_step[OF ss1 step step1 rs rs1] .
  then have "open s = open s1" and "open s' = open s1'"
    using ss1 by (auto simp: eqButUID_open_eq)
  with \<phi> step step1 show "\<phi> (Trans s1 a ou1 s1')"
    using rs ss1 a by (elim \<phi>E) (auto simp: com_defs)
qed

lemma eqButUID_step_\<phi>:
assumes ss1: "eqButUID s s1"
and rs: "reach s" and rs1: "reach s1"
and step: "step s a = (ou,s')" and step1: "step s1 a = (ou1,s1')"
and a: "\<forall>aID uID'. uID' \<notin> UIDs aID \<longrightarrow>
                   a \<noteq> COMact (comSendCreateOFriend UID (pass s UID) aID uID') \<and>
                   a \<noteq> COMact (comSendDeleteOFriend UID (pass s UID) aID uID')"
shows "\<phi> (Trans s a ou s') = \<phi> (Trans s1 a ou1 s1')"
proof
  assume "\<phi> (Trans s a ou s')"
  with assms show "\<phi> (Trans s1 a ou1 s1')" by (rule eqButUID_step_\<phi>_imp)
next
  assume "\<phi> (Trans s1 a ou1 s1')"
  moreover have "eqButUID s1 s" using ss1 by (rule eqButUID_sym)
  moreover have "\<forall>aID uID'. uID' \<notin> UIDs aID \<longrightarrow>
                   a \<noteq> COMact (comSendCreateOFriend UID (pass s1 UID) aID uID') \<and>
                   a \<noteq> COMact (comSendDeleteOFriend UID (pass s1 UID) aID uID')"
    using a ss1 by (auto simp: eqButUID_stateSelectors)
  ultimately show "\<phi> (Trans s a ou s')" using rs rs1 step step1
    by (intro eqButUID_step_\<phi>_imp[of s1 s])
qed

lemma eqButUID_step_\<gamma>:
assumes ss1: "eqButUID s s1"
and rs: "reach s" and rs1: "reach s1"
and step: "step s a = (ou,s')" and step1: "step s1 a = (ou1,s1')"
and a: "\<forall>aID uID'. uID' \<notin> UIDs aID \<longrightarrow>
                   a \<noteq> COMact (comSendCreateOFriend UID (pass s UID) aID uID') \<and>
                   a \<noteq> COMact (comSendDeleteOFriend UID (pass s UID) aID uID')"
shows "\<gamma> (Trans s a ou s') = \<gamma> (Trans s1 a ou1 s1')"
proof -
  { fix ca
    assume a: "a = COMact ca"
    then have "ou = ou1" using assms proof (cases ca)
      case (comSendCreateOFriend uid p aid uid')
        with assms a show ?thesis
          by (cases "uid = UID"; cases "uid' \<in> UIDs aid")
             (auto simp: com_defs eqButUID_def eqButUID_sentOuterFriends_UIDs eqButUID_not_UID)
    next
      case (comSendDeleteOFriend uid p aid uid')
        with assms a show ?thesis
          by (cases "uid = UID"; cases "uid' \<in> UIDs aid")
             (auto simp: com_defs eqButUID_def eqButUID_sentOuterFriends_UIDs eqButUID_not_UID)
    qed (auto simp: com_defs eqButUID_def)
  }
  with assms show ?thesis by auto
qed


end

end
