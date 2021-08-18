(* The ``openness'' of the access window for the friendship confidentiality properties *)
theory Friend_Openness
  imports "Friend_State_Indistinguishability"
begin

subsection \<open>Dynamic declassification trigger\<close>

context Friend
begin

text \<open>The dynamic declassification trigger condition holds, i.e.~the access window to the
confidential information is open, as long as the two users have not been created yet (so there cannot
be friendship between them) or while one of them is a local friend of an observer.\<close>

definition openByA :: "state \<Rightarrow> bool"
where "openByA s \<equiv> \<not> UID1 \<in>\<in> userIDs s \<or> \<not> UID2 \<in>\<in> userIDs s"

definition openByF :: "state \<Rightarrow> bool"
where "openByF s \<equiv> \<exists>uid \<in> UIDs. uid \<in>\<in> friendIDs s UID1 \<or> uid \<in>\<in> friendIDs s UID2"

definition "open" :: "state \<Rightarrow> bool"
where "open s \<equiv> openByA s \<or> openByF s"

lemmas open_defs = open_def openByA_def openByF_def


lemma step_openByA_cases:
assumes "step s a = (ou, s')"
and "openByA s \<noteq> openByA s'"
obtains (CloseA) uid p uid' p' where "a = Cact (cUser uid p uid' p')"
                                     "uid' = UID1 \<or> uid' = UID2" "ou = outOK" "p = pass s uid"
                                     "openByA s" "\<not>openByA s'"
using assms proof (cases a)
  case (Dact da) then show ?thesis using assms by (cases da) (auto simp: d_defs openByA_def) next
  case (Uact ua) then show ?thesis using assms by (cases ua) (auto simp: u_defs openByA_def) next
  case (COMact ca) then show ?thesis using assms by (cases ca) (auto simp: com_defs openByA_def) next
  case (Sact sa)
    then show ?thesis using assms UID1_UID2 by (cases sa) (auto simp: s_defs openByA_def) next
  case (Cact ca)
    then show ?thesis using assms UID1_UID2 proof (cases ca)
      case (cUser uid p uid' p')
        then show ?thesis using Cact assms by (intro that) (auto simp: c_defs openByA_def)
    qed (auto simp: c_defs openByA_def)
qed auto

lemma step_openByF_cases:
assumes "step s a = (ou, s')"
and "openByF s \<noteq> openByF s'"
obtains
  (OpenF) uid p uid' where "a = Cact (cFriend uid p uid')" "ou = outOK" "p = pass s uid"
                           "uid \<in> UIDs \<and> uid' \<in> {UID1,UID2} \<or> uid \<in> {UID1,UID2} \<and> uid' \<in> UIDs"
                           "openByF s'" "\<not>openByF s"
| (CloseF) uid p uid' where "a = Dact (dFriend uid p uid')" "ou = outOK" "p = pass s uid"
                            "uid \<in> UIDs \<and> uid' \<in> {UID1,UID2} \<or> uid \<in> {UID1,UID2} \<and> uid' \<in> UIDs"
                            "openByF s" "\<not>openByF s'"
using assms proof (cases a)
  case (Uact ua) then show ?thesis using assms by (cases ua) (auto simp: u_defs openByF_def) next
  case (COMact ca) then show ?thesis using assms by (cases ca) (auto simp: com_defs openByF_def) next
  case (Sact sa)
    then show ?thesis using assms UID1_UID2 by (cases sa) (auto simp: s_defs openByF_def)
next
  case (Cact ca)
    then show ?thesis using assms UID1_UID2 proof (cases ca)
      case (cFriend uid p uid')
        then show ?thesis using Cact assms by (intro OpenF) (auto simp: c_defs openByF_def)
    qed (auto simp: c_defs openByF_def)
next
  case (Dact da)
    then show ?thesis using assms proof (cases da)
      case (dFriend uid p uid')
        then show ?thesis using Dact assms by (intro CloseF) (auto simp: d_defs openByF_def)
    qed
qed auto


lemma step_open_cases:
assumes step: "step s a = (ou, s')"
and op: "open s \<noteq> open s'"
obtains
  (CloseA) uid p uid' p' where "a = Cact (cUser uid p uid' p')"
                               "uid' = UID1 \<or> uid' = UID2" "ou = outOK" "p = pass s uid"
                               "openByA s" "\<not>openByA s'" "\<not>openByF s" "\<not>openByF s'"
| (OpenF) uid p uid' where "a = Cact (cFriend uid p uid')" "ou = outOK" "p = pass s uid"
                           "uid \<in> UIDs \<and> uid' \<in> {UID1,UID2} \<or> uid \<in> {UID1,UID2} \<and> uid' \<in> UIDs"
                           "openByF s'" "\<not>openByF s" "\<not>openByA s" "\<not>openByA s'"
| (CloseF) uid p uid' where "a = Dact (dFriend uid p uid')" "ou = outOK" "p = pass s uid"
                            "uid \<in> UIDs \<and> uid' \<in> {UID1,UID2} \<or> uid \<in> {UID1,UID2} \<and> uid' \<in> UIDs"
                            "openByF s" "\<not>openByF s'" "\<not>openByA s" "\<not>openByA s'"
proof -
  from op have "openByF s \<noteq> openByF s' \<or> openByA s \<noteq> openByA s'"
    unfolding open_def by auto
  then show thesis proof
    assume "openByF s \<noteq> openByF s'"
    with step show thesis proof (cases rule: step_openByF_cases)
      case (OpenF uid p uid')
        then have "openByA s = openByA s'" using step
          by (cases "openByA s \<noteq> openByA s'", elim step_openByA_cases) auto
        then have "\<not>openByA s \<and> \<not>openByA s'" using op unfolding open_def by auto
        with OpenF show thesis by (intro that(2)) auto
    next
      case (CloseF uid p uid')
        then have "openByA s = openByA s'" using step
          by (cases "openByA s \<noteq> openByA s'", elim step_openByA_cases) auto
        then have "\<not>openByA s \<and> \<not>openByA s'" using op unfolding open_def by auto
        with CloseF show thesis by (intro that(3)) auto
    qed
  next
    assume "openByA s \<noteq> openByA s'"
    with step show thesis proof (cases rule: step_openByA_cases)
      case (CloseA uid p uid' p')
        then have "openByF s = openByF s'" using step
          by (cases "openByF s \<noteq> openByF s'", elim step_openByF_cases) auto
        then have "\<not>openByF s \<and> \<not>openByF s'" using op unfolding open_def by auto
        with CloseA show thesis by (intro that(1)) auto
    qed
  qed
qed


lemma eqButUID_openByA_eq:
assumes "eqButUID s s1"
shows "openByA s = openByA s1"
using assms unfolding openByA_def eqButUID_def by auto

lemma eqButUID_openByF_eq:
assumes ss1: "eqButUID s s1"
shows "openByF s = openByF s1"
proof -
  from ss1 have fIDs: "eqButUIDf (friendIDs s) (friendIDs s1)" unfolding eqButUID_def by auto
  have "\<forall>uid \<in> UIDs. uid \<in>\<in> friendIDs s UID1 \<longleftrightarrow> uid \<in>\<in> friendIDs s1 UID1"
    using UID1_UID2_UIDs UID1_UID2 by (intro ballI eqButUIDf_not_UID'[OF fIDs]; auto)
  moreover have "\<forall>uid \<in> UIDs. uid \<in>\<in> friendIDs s UID2 \<longleftrightarrow> uid \<in>\<in> friendIDs s1 UID2"
    using UID1_UID2_UIDs UID1_UID2 by (intro ballI eqButUIDf_not_UID'[OF fIDs]; auto)
  ultimately show "openByF s = openByF s1" unfolding openByF_def by auto
qed

lemma eqButUID_open_eq: "eqButUID s s1 \<Longrightarrow> open s = open s1"
using eqButUID_openByA_eq eqButUID_openByF_eq unfolding open_def by blast


(* major *) lemma eqButUID_step_\<gamma>_out:
assumes ss1: "eqButUID s s1"
and step: "step s a = (ou,s')" and step1: "step s1 a = (ou1,s1')"
(*and sT: "reachNT s" and s1: "reachNT s1"*)
and \<gamma>: "\<gamma> (Trans s a ou s')"
and os: "open s \<longrightarrow> friendIDs s = friendIDs s1"
shows "ou = ou1"
proof -
  obtain uid sa com_act where uid_a: "(userOfA a = Some uid \<and> uid \<in> UIDs \<and> uid \<noteq> UID1 \<and> uid \<noteq> UID2)
                                  \<or> a = COMact com_act \<or> a = Sact sa"
    using \<gamma> UID1_UID2_UIDs by fastforce
  { fix uid
    assume "uid \<in>\<in> friendIDs s UID1 \<or> uid \<in>\<in> friendIDs s UID2" and "uid \<in> UIDs"
    with os have "friendIDs s = friendIDs s1" unfolding open_def openByF_def by auto
  } note fIDs = this
  { fix uid uid'
    assume uid: "uid \<noteq> UID1" "uid \<noteq> UID2"
    have "friendIDs s uid = friendIDs s1 uid" (is ?f_eq)
     and "pendingFReqs s uid = pendingFReqs s1 uid" (is ?pFR_eq)
     and "uid \<in>\<in> friendIDs s uid' \<longleftrightarrow> uid \<in>\<in> friendIDs s1 uid'" (is ?f_iff)
     and "uid \<in>\<in> pendingFReqs s uid' \<longleftrightarrow> uid \<in>\<in> pendingFReqs s1 uid'" (is ?pFR_iff)
     and "friendReq s uid uid' = friendReq s1 uid uid'" (is ?FR_eq)
     and "friendReq s uid' uid = friendReq s1 uid' uid" (is ?FR_eq')
    proof -
      show ?f_eq ?pFR_eq using uid ss1 UID1_UID2_UIDs unfolding eqButUID_def
        by (auto intro!: eqButUIDf_not_UID)
      show ?f_iff ?pFR_iff using uid ss1 UID1_UID2_UIDs unfolding eqButUID_def
        by (auto intro!: eqButUIDf_not_UID')
      from uid have "\<not> (uid,uid') \<in> {(UID1,UID2), (UID2,UID1)}" by auto
      then show ?FR_eq ?FR_eq' using ss1 UID1_UID2_UIDs unfolding eqButUID_def
        by (auto intro!: eqButUID12_not_UID)
    qed
  } note simps = this eqButUID_stateSelectors r_defs s_defs c_defs com_defs l_defs u_defs d_defs
  note facts = ss1 step step1 uid_a
  show ?thesis
  proof (cases a)
    case (Ract ra) then show ?thesis using facts by (cases ra) (auto simp add: simps)
  next
    case (Sact sa) then show ?thesis using facts by (cases sa) (auto simp add: simps)
  next
    case (Cact ca) then show ?thesis using facts by (cases ca) (auto simp add: simps)
  next
    case (COMact ca) then show ?thesis using facts by (cases ca) (auto simp add: simps)
  next
    case (Lact la)
      then show ?thesis using facts proof (cases la)
        case (lFriends uid p uid')
          with \<gamma> have uid: "uid \<in> UIDs" using Lact by auto
          then have uid_uid': "uid \<in>\<in> friendIDs s uid' \<longleftrightarrow> uid \<in>\<in> friendIDs s1 uid'"
            using ss1 UID1_UID2_UIDs unfolding eqButUID_def by (intro eqButUIDf_not_UID') auto
          show ?thesis
          proof (cases "(uid' = UID1 \<or> uid' = UID2) \<and> uid \<in>\<in> friendIDs s uid'")
            case True
              with uid have "friendIDs s = friendIDs s1" by (intro fIDs) auto
              then show ?thesis using lFriends facts Lact by (auto simp: simps)
          next
            case False
              then show ?thesis using lFriends facts Lact simps(1) uid_uid' by (auto simp: simps)
          qed
      next
        case (lInnerPosts uid p)
          then have o: "\<And>nid. owner s nid = owner s1 nid"
                and n: "\<And>nid. post s nid = post s1 nid"
                and nids: "postIDs s = postIDs s1"
                and vis: "vis s = vis s1"
                and fu: "\<And>uid'. uid \<in>\<in> friendIDs s uid' \<longleftrightarrow> uid \<in>\<in> friendIDs s1 uid'"
                and e: "e_listInnerPosts s uid p \<longleftrightarrow> e_listInnerPosts s1 uid p"
            using ss1 uid_a Lact unfolding eqButUID_def l_defs by (auto simp add: simps(3))
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

end

end
