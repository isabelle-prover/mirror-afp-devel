section \<open>Safety properties \<close>

text \<open>Here we prove some safety properties (state invariants) for a CoSMeDis
node that are needed in the proof of BD Security properties.
\<close>

theory Safety_Properties
  imports
    Automation_Setup
begin

declare Let_def[simp]
declare if_splits[split]
declare IDsOK_def[simp]

lemmas eff_defs = s_defs c_defs d_defs u_defs
lemmas obs_defs = r_defs l_defs
lemmas effc_defs = eff_defs com_defs
lemmas all_defs = effc_defs obs_defs

declare sstep_Cons[simp]

lemma Lact_Ract_noStateChange[simp]:
assumes "a \<in> Lact ` UNIV \<union> Ract ` UNIV"
shows "snd (step s a) = s"
using assms by (cases a) auto

lemma Lact_Ract_noStateChange_set:
assumes "set al \<subseteq> Lact ` UNIV \<union> Ract ` UNIV"
shows "snd (sstep s al) = s"
using assms by (induct al) (auto split: prod.splits)

lemma reach_postIDs_persist:
"pID \<in>\<in> postIDs s \<Longrightarrow> step s a = (ou,s') \<Longrightarrow> pID \<in>\<in> postIDs s'"
apply (cases a)
  subgoal for x1 apply(cases x1, auto simp: effc_defs) .
  subgoal for x2 apply(cases x2, auto simp: effc_defs) .
  subgoal for x3 apply(cases x3, auto simp: effc_defs) .
  subgoal for x4 apply(cases x4, auto simp: effc_defs) .
  subgoal by auto
  subgoal by auto
  subgoal for x7 apply(cases x7, auto simp: effc_defs) .
done

lemma userOfA_not_userIDs_outErr:
"\<exists> uid. userOfA a = Some uid \<and> \<not> uid \<in>\<in> userIDs s \<Longrightarrow>
 \<forall> aID uID p name. a \<noteq> Sact (sSys uID p) \<Longrightarrow>
 \<forall> uID name. a \<noteq> Cact (cNUReq uID name) \<Longrightarrow>
 fst (step s a) = outErr"
apply (cases a)
  subgoal for x1 apply(cases x1, auto simp: all_defs) .
  subgoal for x2 apply(cases x2, auto simp: all_defs) .
  subgoal for x3 apply(cases x3, auto simp: all_defs) .
  subgoal for x4 apply(cases x4, auto simp: all_defs) .
  subgoal for x5 apply(cases x5, auto simp: all_defs) .
  subgoal for x6 apply(cases x6, auto simp: all_defs) .
  subgoal for x7 apply(cases x7, auto simp: all_defs) .
done

lemma reach_vis: "reach s \<Longrightarrow> vis s pID \<in> {FriendV, PublicV}"
proof (induction rule: reach_step_induct)
  case (Step s a) then show ?case proof (cases a)
     case (Sact sAct) with Step show ?thesis
     apply (cases sAct) by (auto simp add: s_defs)
  next
    case (Cact cAct) with Step show ?thesis
    apply (cases cAct) by (auto simp add: c_defs)
  next
    case (Dact dAct) with Step show ?thesis
    apply (cases dAct) by (auto simp add: d_defs)
  next
    case (Uact uAct) with Step show ?thesis
    apply (cases uAct) by (auto simp add: u_defs)
  next
    case (COMact comAct) with Step show ?thesis apply (cases comAct)
    by (auto simp add: com_defs)
  qed auto
qed (auto simp add: istate_def)

lemma reach_not_postIDs_emptyPost:
"reach s \<Longrightarrow> PID \<notin> set (postIDs s) \<Longrightarrow> post s PID = emptyPost"
proof (induction rule: reach_step_induct)
  case (Step s a) then show ?case proof (cases a)
     case (Sact sAct) with Step show ?thesis
     apply (cases sAct) by (auto simp add: s_defs)
  next
    case (Cact cAct) with Step show ?thesis
    apply (cases cAct) by (auto simp add: c_defs)
  next
    case (Dact dAct) with Step show ?thesis
    apply (cases dAct) by (auto simp add: d_defs)
  next
    case (Uact uAct) with Step show ?thesis
    apply (cases uAct) by (auto simp add: u_defs)
  next
    case (COMact comAct) with Step show ?thesis apply (cases comAct)
    by (auto simp add: com_defs)
  qed auto
qed (auto simp add: istate_def)

lemma reach_not_postIDs_friendV:
"reach s \<Longrightarrow> PID \<notin> set (postIDs s) \<Longrightarrow> vis s PID = FriendV"
proof (induction rule: reach_step_induct)
  case (Step s a) then show ?case proof (cases a)
     case (Sact sAct) with Step show ?thesis
     apply (cases sAct) by (auto simp add: s_defs)
  next
    case (Cact cAct) with Step show ?thesis
    apply (cases cAct) by (auto simp add: c_defs)
  next
    case (Dact dAct) with Step show ?thesis
    apply (cases dAct) by (auto simp add: d_defs)
  next
    case (Uact uAct) with Step show ?thesis
    apply (cases uAct) by (auto simp add: u_defs)
  next
    case (COMact comAct) with Step show ?thesis apply (cases comAct)
    by (auto simp add: com_defs)
  qed auto
qed (auto simp add: istate_def)


(* Would only work if we new that the same property holds
for what is being received:
lemma reach_outerVis: "reach s \<Longrightarrow> outerVis s aID pID \<in> {FriendV, PublicV}"
proof (induction rule: reach_step_induct)
  case (Step s a) then show ?case proof (cases a)
     case (Sact sAct) with Step show ?thesis
     apply (cases sAct) by (auto simp add: s_defs)
  next
    case (Cact cAct) with Step show ?thesis
    apply (cases cAct) by (auto simp add: c_defs)
  next
    case (Dact dAct) with Step show ?thesis
    apply (cases dAct) by (auto simp add: d_defs)
  next
    case (Uact uAct) with Step show ?thesis
    apply (cases uAct) by (auto simp add: u_defs)
  next
    case (COMact comAct) with Step show ?thesis apply (cases comAct)
    apply (auto simp add: com_defs fun_upd2_def)
  qed auto
qed (auto simp add: istate_def)
*)

lemma reach_owner_userIDs: "reach s \<Longrightarrow> pID \<in>\<in> postIDs s \<Longrightarrow> owner s pID \<in>\<in> userIDs s"
proof (induction rule: reach_step_induct)
  case (Step s a) then show ?case proof (cases a)
     case (Sact sAct) with Step show ?thesis
     apply (cases sAct) by (auto simp add: s_defs)
  next
    case (Cact cAct) with Step show ?thesis
    apply (cases cAct) by (auto simp add: c_defs)
  next
    case (Dact dAct) with Step show ?thesis
    apply (cases dAct) by (auto simp add: d_defs)
  next
    case (Uact uAct) with Step show ?thesis
    apply (cases uAct) by (auto simp add: u_defs)
  next
    case (COMact comAct) with Step show ?thesis apply (cases comAct)
    by (auto simp add: com_defs)
  qed auto
qed (auto simp add: istate_def)

lemma reach_admin_userIDs: "reach s \<Longrightarrow> uID \<in>\<in> userIDs s \<Longrightarrow> admin s \<in>\<in> userIDs s"
proof (induction rule: reach_step_induct)
  case (Step s a) then show ?case proof (cases a)
     case (Sact sAct) with Step show ?thesis
     apply (cases sAct) by (auto simp add: s_defs)
  next
    case (Cact cAct) with Step show ?thesis
    apply (cases cAct) by (auto simp add: c_defs)
  next
    case (Dact dAct) with Step show ?thesis
    apply (cases dAct) by (auto simp add: d_defs)
  next
    case (Uact uAct) with Step show ?thesis
    apply (cases uAct) by (auto simp add: u_defs)
  next
    case (COMact comAct) with Step show ?thesis apply (cases comAct)
    by (auto simp add: com_defs)
  qed auto
qed (auto simp add: istate_def)

lemma reach_pendingUReqs_distinct: "reach s \<Longrightarrow> distinct (pendingUReqs s)"
proof (induction rule: reach_step_induct)
  case (Step s a) then show ?case proof (cases a)
    case (Sact sAct) with Step show ?thesis by (cases sAct) (auto simp add: s_defs) next
    case (Cact cAct) with Step show ?thesis by (cases cAct) (auto simp add: c_defs) next
    case (Dact dAct) with Step show ?thesis by (cases dAct) (auto simp add: d_defs) next
    case (Uact uAct) with Step show ?thesis by (cases uAct) (auto simp add: u_defs) next
    case (COMact comAct) with Step show ?thesis by (cases comAct) (auto simp add: com_defs)
  qed auto
qed (auto simp: istate_def)

lemma reach_pendingUReqs:
"reach s \<Longrightarrow> uid \<in>\<in> pendingUReqs s \<Longrightarrow> uid \<notin> set (userIDs s) \<and> admin s \<in>\<in> userIDs s"
proof (induction rule: reach_step_induct)
  case (Step s a) then show ?case proof (cases a)
    case (Sact sAct) with Step show ?thesis by (cases sAct) (auto simp add: s_defs) next
    case (Cact cAct)
      with Step reach_pendingUReqs_distinct show ?thesis
        by (cases cAct) (auto simp add: c_defs) next
    case (Dact dAct) with Step show ?thesis by (cases dAct) (auto simp add: d_defs) next
    case (Uact uAct) with Step show ?thesis by (cases uAct) (auto simp add: u_defs) next
    case (COMact comAct) with Step show ?thesis by (cases comAct) (auto simp add: com_defs)
  qed auto
qed (auto simp: istate_def)

lemma reach_friendIDs_symmetric:
"reach s \<Longrightarrow> uID1 \<in>\<in> friendIDs s uID2 \<longleftrightarrow> uID2 \<in>\<in> friendIDs s uID1"
proof (induction rule: reach_step_induct)
  case (Step s a) then show ?case proof (cases a)
    case (Sact sAct) with Step show ?thesis by (cases sAct) (auto simp add: s_defs) next
    case (Cact cAct) with Step show ?thesis by (cases cAct) (auto simp add: c_defs ) next
    case (Dact dAct) with Step show ?thesis by (cases dAct) (auto simp add: d_defs ) next
    case (Uact uAct) with Step show ?thesis by (cases uAct) (auto simp add: u_defs) next
    case (COMact comAct) with Step show ?thesis by (cases comAct) (auto simp add: com_defs)
  qed auto
qed (auto simp add: istate_def)

(* No longer holds:
lemma friendIDs_mono:
assumes "step s a = (ou, s')"
and "uid \<in>\<in> friendIDs s uid'"
shows "uid \<in>\<in> friendIDs s' uid'"
using assms proof (cases a)
  case (Sact sAct) with assms show ?thesis by (cases sAct) (auto simp add: s_defs) next
  case (Cact cAct) with assms show ?thesis by (cases cAct) (auto simp add: c_defs ) next
  case (Dact dAct) with assms show ?thesis by (cases dAct) (auto simp add: d_defs ) next
  case (Uact uAct) with assms show ?thesis by (cases uAct) (auto simp add: u_defs) next
  case (COMact comAct) with assms show ?thesis by (cases comAct) (auto simp add: com_defs)
qed auto
*)

lemma reach_distinct_friends_reqs:
assumes "reach s"
shows "distinct (friendIDs s uid)" and "distinct (pendingFReqs s uid)"
  and "distinct (sentOuterFriendIDs s uid)" and "distinct (recvOuterFriendIDs s uid)"
  and "uid' \<in>\<in> pendingFReqs s uid \<Longrightarrow> uid' \<notin> set (friendIDs s uid)"
  and "uid' \<in>\<in> pendingFReqs s uid \<Longrightarrow> uid \<notin> set (friendIDs s uid')"
using assms proof (induction arbitrary: uid uid' rule: reach_step_induct)
  case Istate
    fix uid uid'
    show "distinct (friendIDs istate uid)" and "distinct (pendingFReqs istate uid)"
     and "distinct (sentOuterFriendIDs istate uid)" and "distinct (recvOuterFriendIDs istate uid)"
     and "uid' \<in>\<in> pendingFReqs istate uid \<Longrightarrow> uid' \<notin> set (friendIDs istate uid)"
     and "uid' \<in>\<in> pendingFReqs istate uid \<Longrightarrow> uid \<notin> set (friendIDs istate uid')"
      unfolding istate_def by auto
next
  case (Step s a)
    have s': "reach (snd (step s a))" using reach_step[OF Step(1)] .
    { fix uid uid'
      have "distinct (friendIDs (snd (step s a)) uid) \<and> distinct (pendingFReqs (snd (step s a)) uid)
          \<and> distinct (sentOuterFriendIDs (snd (step s a)) uid)
          \<and> distinct (recvOuterFriendIDs (snd (step s a)) uid)
          \<and> (uid' \<in>\<in> pendingFReqs (snd (step s a)) uid \<longrightarrow> uid' \<notin> set (friendIDs (snd (step s a)) uid))"
      proof (cases a)
        case (Sact sa) with Step show ?thesis by (cases sa) (auto simp add: s_defs) next
        case (Cact ca) with Step show ?thesis by (cases ca) (auto simp add: c_defs) next
        case (Dact da) with Step show ?thesis by (cases da) (auto simp add: d_defs distinct_removeAll) next
        case (Uact ua) with Step show ?thesis by (cases ua) (auto simp add: u_defs) next
        case (Ract ra) with Step show ?thesis by auto next
        case (Lact ra) with Step show ?thesis by auto next
        case (COMact ca) with Step show ?thesis by (cases ca) (auto simp add: com_defs) next
      qed
    } note goal = this
    fix uid uid'
    from goal show "distinct (friendIDs (snd (step s a)) uid)"
               and "distinct (pendingFReqs (snd (step s a)) uid)"
               and "distinct (sentOuterFriendIDs (snd (step s a)) uid)"
               and "distinct (recvOuterFriendIDs (snd (step s a)) uid)"
 by auto
    assume "uid' \<in>\<in> pendingFReqs (snd (step s a)) uid"
    with goal show "uid' \<notin> set (friendIDs (snd (step s a)) uid)" by auto
    then show "uid \<notin> set (friendIDs (snd (step s a)) uid')"
      using reach_friendIDs_symmetric[OF s'] by simp
qed

lemma remove1_in_set: "x \<in>\<in> remove1 y xs \<Longrightarrow> x \<in>\<in> xs"
by (induction xs) auto

lemma reach_IDs_used_IDsOK[rule_format]:
assumes "reach s"
shows "uid \<in>\<in> pendingFReqs s uid' \<longrightarrow> IDsOK s [uid, uid'] [] [] []" (is ?p)
and "uid \<in>\<in> friendIDs s uid' \<longrightarrow> IDsOK s [uid, uid'] [] [] []" (is ?f)
using assms proof -
  from assms have "uid \<in>\<in> pendingFReqs s uid' \<or> uid \<in>\<in> friendIDs s uid'
               \<longrightarrow> IDsOK s [uid, uid'] [] [] []"
  proof (induction rule: reach_step_induct)
    case Istate then show ?case by (auto simp add: istate_def)
  next
    case (Step s a) then show ?case proof (cases a)
      case (Sact sa) with Step show ?thesis by (cases sa) (auto simp: s_defs) next
      case (Cact ca) with Step show ?thesis by (cases ca) (auto simp: c_defs intro: remove1_in_set) next
      case (Dact da) with Step show ?thesis by (cases da) (auto simp: d_defs) next
      case (Uact ua) with Step show ?thesis by (cases ua) (auto simp: u_defs) next
      case (COMact ca) with Step show ?thesis by (cases ca) (auto simp: com_defs)
    qed auto
  qed
  then show ?p and ?f by auto
qed

lemma reach_AID_used_valid:
assumes "reach s"
and "aid \<in>\<in> serverApiIDs s \<or> aid \<in>\<in> clientApiIDs s \<or> aid \<in>\<in> pendingSApiReqs s \<or> aid \<in>\<in> pendingCApiReqs s"
shows "admin s \<in>\<in> userIDs s"
using assms proof (induction rule: reach_step_induct)
  case Istate then show ?case by (auto simp: istate_def)
next
  case (Step s a) then show ?case proof (cases a)
    case (Sact sa) with Step show ?thesis by (cases sa) (auto simp: s_defs) next
    case (Cact ca) with Step show ?thesis by (cases ca) (auto simp: c_defs) next
    case (Dact da) with Step show ?thesis by (cases da) (auto simp: d_defs) next
    case (Uact ua) with Step show ?thesis by (cases ua) (auto simp: u_defs) next
    case (COMact ca) with Step show ?thesis by (cases ca) (auto simp: com_defs intro: remove1_in_set)
  qed auto
qed

lemma IDs_mono[rule_format]:
assumes "step s a = (ou, s')"
shows "uid \<in>\<in> userIDs s \<longrightarrow> uid \<in>\<in> userIDs s'" (is "?u")
and "nid \<in>\<in> postIDs s \<longrightarrow> nid \<in>\<in> postIDs s'" (is "?n")
and "aid \<in>\<in> clientApiIDs s \<longrightarrow> aid \<in>\<in> clientApiIDs s'" (is "?c")
and "sid \<in>\<in> serverApiIDs s \<longrightarrow> sid \<in>\<in> serverApiIDs s'" (is "?s")
and "nid \<in>\<in> outerPostIDs s aid \<longrightarrow> nid \<in>\<in> outerPostIDs s' aid" (is "?o")
proof -
  from assms have "?u \<and> ?n \<and> ?c \<and> ?s \<and> ?o" proof (cases a)
    case (Sact sa) with assms show ?thesis by (cases sa) (auto simp add: s_defs) next
    case (Cact ca) with assms show ?thesis by (cases ca) (auto simp add: c_defs) next
    case (Dact da) with assms show ?thesis by (cases da) (auto simp add: d_defs) next
    case (Uact ua) with assms show ?thesis by (cases ua) (auto simp add: u_defs) next
    case (COMact ca) with assms show ?thesis by (cases ca) (auto simp add: com_defs)
  qed (auto)
  then show "?u" "?n" "?c" "?s" "?o" by auto
qed

lemma IDsOK_mono:
assumes "step s a = (ou, s')"
and "IDsOK s uIDs pIDs saID_pIDs_s caIDs"
shows "IDsOK s' uIDs pIDs saID_pIDs_s caIDs"
using IDs_mono[OF assms(1)] assms(2)
by (auto simp add: list_all_iff)


lemma step_outerFriendIDs_idem:
assumes "step s a = (ou, s')"
and "\<forall>uID p aID uID'. a \<noteq> COMact (comSendCreateOFriend uID p aID uID') \<and>
                      a \<noteq> COMact (comReceiveCreateOFriend aID p uID uID') \<and>
                      a \<noteq> COMact (comSendDeleteOFriend uID p aID uID') \<and>
                      a \<noteq> COMact (comReceiveDeleteOFriend aID p uID uID')"
shows "sentOuterFriendIDs s' = sentOuterFriendIDs s" (is ?sent)
  and "recvOuterFriendIDs s' = recvOuterFriendIDs s" (is ?recv)
proof -
  have "?sent \<and> ?recv" using assms proof (cases a)
    case (Sact sa) with assms show ?thesis by (cases sa) (auto simp add: s_defs) next
    case (Cact ca) with assms show ?thesis by (cases ca) (auto simp add: c_defs) next
    case (Dact da) with assms show ?thesis by (cases da) (auto simp add: d_defs) next
    case (Uact ua) with assms show ?thesis by (cases ua) (auto simp add: u_defs) next
    case (COMact ca) with assms show ?thesis by (cases ca) (auto simp add: com_defs)
  qed auto
  then show "?sent" and "?recv" by auto
qed

lemma istate_sSys:
assumes "step istate a = (ou, s')"
obtains uid p where "a = Sact (sSys uid p)"
      | "s' = istate"
using assms proof (cases a)
  case (Sact sa) with assms show ?thesis by (cases sa) (auto intro: that) next
  case (Cact ca) with assms that(2) show ?thesis by (cases ca) (auto simp add: c_defs istate_def) next
  case (Dact da) with assms that(2) show ?thesis by (cases da) (auto simp add: d_defs istate_def) next
  case (Uact ua) with assms that(2) show ?thesis by (cases ua) (auto simp add: u_defs istate_def) next
  case (COMact ca) with assms that(2) show ?thesis by (cases ca) (auto simp add: com_defs istate_def) next
  case (Ract ra) with assms that(2) show ?thesis by (cases ra) (auto simp add: r_defs istate_def) next
  case (Lact la) with assms that(2) show ?thesis by (cases la) (auto simp add: l_defs istate_def)
qed


end
