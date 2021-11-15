section \<open>Safety properties\<close>

theory Safety_Properties
imports Automation_Setup "Bounded_Deducibility_Security.Compositional_Reasoning"
begin

interpretation IO_Automaton where
istate = istate and step = step
done

declare if_splits[split]
declare IDsOK_def[simp]

lemmas eff_defs = s_defs c_defs d_defs u_defs
lemmas obs_defs = r_defs l_defs
lemmas all_defs = eff_defs obs_defs
lemmas step_elims = step.elims sStep.elims cStep.elims dStep.elims uStep.elims

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
  by (cases a) (auto elim: step_elims simp: eff_defs)

lemma reach_visPost: "reach s \<Longrightarrow> vis s pID \<in> {FriendV, PublicV}"
proof (induction rule: reach_step_induct)
  case (Step s a)
  then show ?case proof (cases a)
    case (Sact sAct)
    with Step show ?thesis
      by (cases sAct) (auto simp add: s_defs)
  next
    case (Cact cAct)
    with Step show ?thesis
      by (cases cAct) (auto simp add: c_defs)
  next
    case (Dact dAct)
    with Step show ?thesis
      by (cases dAct) (auto simp add: d_defs)
  next
    case (Uact uAct)
    with Step show ?thesis
      by (cases uAct) (auto simp add: u_defs)
  qed auto
qed (auto simp add: istate_def)

lemma reach_owner_userIDs: "reach s \<Longrightarrow> pID \<in>\<in> postIDs s \<Longrightarrow> owner s pID \<in>\<in> userIDs s"
proof (induction rule: reach_step_induct)
  case (Step s a)
  then show ?case proof (cases a)
    case (Sact sAct)
    with Step show ?thesis
      by (cases sAct) (auto simp add: s_defs)
  next
    case (Cact cAct)
    with Step show ?thesis
      by (cases cAct) (auto simp add: c_defs)
  next
    case (Dact dAct)
    with Step show ?thesis
      by (cases dAct) (auto simp add: d_defs)
  next
    case (Uact uAct)
    with Step show ?thesis
      by (cases uAct) (auto simp add: u_defs)
  qed auto
qed (auto simp add: istate_def)

lemma reach_friendIDs_symmetric:
"reach s \<Longrightarrow> uID1 \<in>\<in> friendIDs s uID2 \<longleftrightarrow> uID2 \<in>\<in> friendIDs s uID1"
proof (induction rule: reach_step_induct)
  case (Step s a) then show ?case proof (cases a)
    case (Sact sAct) with Step show ?thesis by (cases sAct) (auto simp add: s_defs) next
    case (Cact cAct) with Step show ?thesis by (cases cAct) (auto simp add: c_defs ) next
    case (Dact dAct) with Step show ?thesis by (cases dAct) (auto simp add: d_defs ) next
    case (Uact uAct) with Step show ?thesis by (cases uAct) (auto simp add: u_defs)
  qed auto
qed (auto simp add: istate_def)

lemma reach_not_postIDs_vis_FriendV:
assumes  "reach s" "\<not> pid \<in>\<in> postIDs s"
shows "vis s pid = FriendV"
using assms proof (induction rule: reach_step_induct)
  case (Step s a) then show ?case proof (cases a)
    case (Sact sAct) with Step show ?thesis by (cases sAct) (auto simp add: s_defs) next
    case (Cact cAct) with Step show ?thesis by (cases cAct) (auto simp add: c_defs ) next
    case (Dact dAct) with Step show ?thesis by (cases dAct) (auto simp add: d_defs ) next
    case (Uact uAct) with Step show ?thesis by (cases uAct) (auto simp add: u_defs)
  qed auto
qed (auto simp add: istate_def)

lemma reach_distinct_friends_reqs:
assumes "reach s"
shows "distinct (friendIDs s uid)" and "distinct (pendingFReqs s uid)"
  and "uid' \<in>\<in> pendingFReqs s uid \<Longrightarrow> uid' \<notin> set (friendIDs s uid)"
  and "uid' \<in>\<in> pendingFReqs s uid \<Longrightarrow> uid \<notin> set (friendIDs s uid')"
using assms proof (induction arbitrary: uid uid' rule: reach_step_induct)
  case Istate
    fix uid uid'
    show "distinct (friendIDs istate uid)" and "distinct (pendingFReqs istate uid)"
     and "uid' \<in>\<in> pendingFReqs istate uid \<Longrightarrow> uid' \<notin> set (friendIDs istate uid)"
     and "uid' \<in>\<in> pendingFReqs istate uid \<Longrightarrow> uid \<notin> set (friendIDs istate uid')"
      unfolding istate_def by auto
next
  case (Step s a)
    have s': "reach (snd (step s a))" using reach_step[OF Step(1)] .
    { fix uid uid'
      have "distinct (friendIDs (snd (step s a)) uid) \<and> distinct (pendingFReqs (snd (step s a)) uid)
          \<and> (uid' \<in>\<in> pendingFReqs (snd (step s a)) uid \<longrightarrow> uid' \<notin> set (friendIDs (snd (step s a)) uid))"
      proof (cases a)
        case (Sact sa) with Step show ?thesis by (cases sa) (auto simp add: s_defs) next
        case (Cact ca) with Step show ?thesis by (cases ca) (auto simp add: c_defs) next
        case (Dact da) with Step show ?thesis by (cases da) (auto simp add: d_defs distinct_removeAll) next
        case (Uact ua) with Step show ?thesis by (cases ua) (auto simp add: u_defs) next
        case (Ract ra) with Step show ?thesis by auto next
        case (Lact ra) with Step show ?thesis by auto
      qed
    } note goal = this
    fix uid uid'
    from goal show "distinct (friendIDs (snd (step s a)) uid)"
               and "distinct (pendingFReqs (snd (step s a)) uid)" by auto
    assume "uid' \<in>\<in> pendingFReqs (snd (step s a)) uid"
    with goal show "uid' \<notin> set (friendIDs (snd (step s a)) uid)" by auto
    then show "uid \<notin> set (friendIDs (snd (step s a)) uid')"
      using reach_friendIDs_symmetric[OF s'] by simp
qed

lemma remove1_in_set: "x \<in>\<in> remove1 y xs \<Longrightarrow> x \<in>\<in> xs"
by (induction xs) auto

lemma reach_IDs_used_IDsOK[rule_format]:
assumes "reach s"
shows "uid \<in>\<in> pendingFReqs s uid' \<longrightarrow> IDsOK s [uid, uid'] []" (is ?p)
and "uid \<in>\<in> friendIDs s uid' \<longrightarrow> IDsOK s [uid, uid'] []" (is ?f)
using assms proof -
  from assms have "uid \<in>\<in> pendingFReqs s uid' \<or> uid \<in>\<in> friendIDs s uid'
               \<longrightarrow> IDsOK s [uid, uid'] []"
  proof (induction rule: reach_step_induct)
    case Istate then show ?case by (auto simp add: istate_def)
  next
    case (Step s a) then show ?case proof (cases a)
      case (Sact sa) with Step show ?thesis by (cases sa) (auto simp: s_defs) next
      case (Cact ca) with Step show ?thesis by (cases ca) (auto simp: c_defs intro: remove1_in_set) next
      case (Dact da) with Step show ?thesis by (cases da) (auto simp: d_defs) next
      case (Uact ua) with Step show ?thesis by (cases ua) (auto simp: u_defs)
    qed auto
  qed
  then show ?p and ?f by auto
qed

lemma IDs_mono[rule_format]:
assumes "step s a = (ou, s')"
shows "uid \<in>\<in> userIDs s \<longrightarrow> uid \<in>\<in> userIDs s'" (is "?u")
and "pid \<in>\<in> postIDs s \<longrightarrow> pid \<in>\<in> postIDs s'" (is "?n")
proof -
  from assms have "?u \<and> ?n" proof (cases a)
    case (Sact sa) with assms show ?thesis by (cases sa) (auto simp add: s_defs) next
    case (Cact ca) with assms show ?thesis by (cases ca) (auto simp add: c_defs) next
    case (Dact da) with assms show ?thesis by (cases da) (auto simp add: d_defs) next
    case (Uact ua) with assms show ?thesis by (cases ua) (auto simp add: u_defs)
  qed (auto)
  then show "?u" "?n" by auto
qed

lemma IDsOK_mono:
assumes "step s a = (ou, s')"
and "IDsOK s uIDs pIDs"
shows "IDsOK s' uIDs pIDs"
using IDs_mono[OF assms(1)] assms(2)
  by (auto simp add: list_all_iff)






end
