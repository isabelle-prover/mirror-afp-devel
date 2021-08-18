theory Outer_Friend_Network
imports
  "../API_Network"
  "Issuer/Outer_Friend_Issuer"
  "Receiver/Outer_Friend_Receiver"
  "BD_Security_Compositional.Composing_Security_Network"
begin

subsection \<open>Confidentiality for the N-ary composition\<close>

locale OuterFriendNetwork = OuterFriend + Network +
assumes AID_AIDs: "AID \<in> AIDs"
begin

sublocale Issuer: OuterFriendIssuer UIDs AID UID using UID_UIDs by unfold_locales

abbreviation \<phi> :: "apiID \<Rightarrow> (state, act, out) trans \<Rightarrow> bool"
where "\<phi> aid trn \<equiv> (if aid = AID then Issuer.\<phi> trn else OuterFriendReceiver.\<phi> UIDs AID UID aid trn)"

abbreviation f :: "apiID \<Rightarrow> (state, act, out) trans \<Rightarrow> value"
where "f aid trn \<equiv> (if aid = AID then Issuer.f trn else OuterFriendReceiver.f aid trn)"

abbreviation \<gamma> :: "apiID \<Rightarrow> (state, act, out) trans \<Rightarrow> bool"
where "\<gamma> aid trn \<equiv> (if aid = AID then Issuer.\<gamma> trn else OuterFriendReceiver.\<gamma> UIDs aid trn)"

abbreviation g :: "apiID \<Rightarrow> (state, act, out) trans \<Rightarrow> obs"
where "g aid trn \<equiv> (if aid = AID then Issuer.g trn else OuterFriendReceiver.g UIDs AID UID aid trn)"

abbreviation T :: "apiID \<Rightarrow> (state, act, out) trans \<Rightarrow> bool"
where "T aid trn \<equiv> False"

abbreviation B :: "apiID \<Rightarrow> value list \<Rightarrow> value list \<Rightarrow> bool"
where "B aid vl vl1 \<equiv> (if aid = AID then Issuer.B vl vl1 else OuterFriendReceiver.B UIDs AID UID aid vl vl1)"

fun comOfV where
  "comOfV aid (FrVal aid' uid' st) = (if aid \<noteq> AID then Recv else (if aid' \<noteq> aid then Send else Internal))"
| "comOfV aid (OVal ov) = Internal"

fun tgtNodeOfV where
  "tgtNodeOfV aid (FrVal aid' uid' st) = (if aid = AID then aid' else AID)"
| "tgtNodeOfV aid (OVal ov) = AID"

abbreviation "syncV aid1 v1 aid2 v2 \<equiv> (v1 = v2)"

sublocale Net: BD_Security_TS_Network_getTgtV
where istate = "\<lambda>_. istate" and validTrans = validTrans and srcOf = "\<lambda>_. srcOf" and tgtOf = "\<lambda>_. tgtOf"
  and nodes = AIDs and comOf = comOf and tgtNodeOf = tgtNodeOf
  and sync = sync and \<phi> = \<phi> and f = f and \<gamma> = \<gamma> and g = g and T = T and B = B
  and comOfV = comOfV and tgtNodeOfV = tgtNodeOfV and syncV = syncV
  and comOfO = comOfO and tgtNodeOfO = tgtNodeOfO and syncO = syncO (*and cmpO = cmpO*)
  and source = AID and getTgtV = id
proof (unfold_locales, goal_cases)
  case (1 aid trn)
    interpret Receiver: OuterFriendReceiver UIDs AID UID aid by unfold_locales
    from 1 show ?case by (cases trn) (auto elim!: Issuer.\<phi>E Receiver.\<phi>.elims split: prod.splits)
next
  case (2 aid trn)
    interpret Receiver: OuterFriendReceiver UIDs AID UID aid by unfold_locales
    from 2 show ?case by (cases trn) (auto elim!: Issuer.\<phi>E Receiver.\<phi>.elims)
next
  case (3 aid trn)
    interpret Receiver: OuterFriendReceiver UIDs AID UID aid by unfold_locales
    from 3 show ?case by (cases "(aid,trn)" rule: tgtNodeOf.cases) (auto)
next
  case (4 aid trn)
    interpret Receiver: OuterFriendReceiver UIDs AID UID aid by unfold_locales
    from 4 show ?case by (cases "(aid,trn)" rule: tgtNodeOf.cases) auto
next
  case (5 aid1 trn1 aid2 trn2)
    interpret Receiver1: OuterFriendReceiver UIDs AID UID aid1 by unfold_locales
    interpret Receiver2: OuterFriendReceiver UIDs AID UID aid2 by unfold_locales
    from 5 show ?case by (elim sync_cases) (auto simp: com_defs)
next
  case (6 aid1 trn1 aid2 trn2)
    interpret Receiver1: OuterFriendReceiver UIDs AID UID aid1 by unfold_locales
    interpret Receiver2: OuterFriendReceiver UIDs AID UID aid2 by unfold_locales
    from 6 show ?case by (elim sync_cases) (auto)
next
  case (7 aid1 trn1 aid2 trn2)
    interpret Receiver1: OuterFriendReceiver UIDs AID UID aid1 by unfold_locales
    interpret Receiver2: OuterFriendReceiver UIDs AID UID aid2 by unfold_locales
    from 7 show ?case
      using Issuer.COMact_open[of "srcOf trn1" "actOf trn1" "outOf trn1" "tgtOf trn1"]
      using Issuer.COMact_open[of "srcOf trn2" "actOf trn2" "outOf trn2" "tgtOf trn2"]
      by (elim sync_cases) auto
next
  case (8 aid1 trn1 aid2 trn2)
    interpret Receiver1: OuterFriendReceiver UIDs AID UID aid1 by unfold_locales
    interpret Receiver2: OuterFriendReceiver UIDs AID UID aid2 by unfold_locales
    assume "comOf aid1 trn1 = Send" "comOf aid2 trn2 = Recv" "syncO aid1 (g aid1 trn1) aid2 (g aid2 trn2)"
           "\<phi> aid1 trn1 \<Longrightarrow> \<phi> aid2 trn2 \<Longrightarrow> f aid1 trn1 = f aid2 trn2"
           "validTrans aid1 trn1" "validTrans aid2 trn2"
    then show ?case using emptyUserID_not_UIDs
      by (elim syncO_cases; cases trn1; cases trn2)
         (auto simp: Issuer.g_simps Receiver1.g_simps Receiver2.g_simps simp: com_defs)
next
  case (9 aid trn)
    interpret Receiver: OuterFriendReceiver UIDs AID UID aid by unfold_locales
    from 9 show ?case by (cases "(aid,trn)" rule: tgtNodeOf.cases) (auto)
next
  case (10 aid trn)
    interpret Receiver: OuterFriendReceiver UIDs AID UID aid by unfold_locales
    from 10 show ?case using AID_AIDs by (auto elim!: Receiver.\<phi>.elims)
next
  case (11 vSrc nid vn) then show ?case by (cases vSrc) auto
next
  case (12 vSrc nid vn) then show ?case by (cases vSrc) auto
qed

context
fixes AID' :: apiID
assumes AID': "AID' \<in> AIDs - {AID}"
begin

interpretation Receiver: OuterFriendReceiver UIDs AID UID AID' by unfold_locales

lemma Issuer_BC_Receiver_BC:
assumes "Issuer.BC vl vl1"
shows "Receiver.BC (Net.projectSrcV AID' vl) (Net.projectSrcV AID' vl1)"
using assms by (induction rule: Issuer.BC.induct) auto

lemma Collect_setminus: "Collect P - A = {u. u \<notin> A \<and> P u}"
by auto

lemma Issuer_vVS_Receiver_vVS:
assumes "Issuer.validValSeq vl auidl"
shows "Receiver.validValSeq (Net.projectSrcV AID' vl) {uid. (AID',uid) \<in>\<in> auidl}"
using assms AID'
proof (induction vl auidl rule: Issuer.validValSeq.induct)
  case (2 aid uid vl auidl)
  then show ?case by (auto simp: insert_Collect Collect_setminus, linarith, smt Collect_cong)
next
  case (3 aid uid vl auidl)
  then show ?case by (auto simp: insert_Collect Collect_setminus; smt Collect_cong)
qed auto

lemma Issuer_B_Receiver_B:
assumes "Issuer.B vl vl1"
shows "Receiver.B (Net.projectSrcV AID' vl) (Net.projectSrcV AID' vl1)"
using assms Issuer_BC_Receiver_BC Issuer_vVS_Receiver_vVS[of _ "[]"]
unfolding Issuer.B_def Issuer.BO_def Receiver.B_def Receiver.friendsOfUID_def
by (auto simp: istate_def intro!: Receiver.BC_append Receiver.BC_id, blast dest: Issuer.validValSeq_prefix)

end


sublocale BD_Security_TS_Network_Preserve_Source_Security_getTgtV
where istate = "\<lambda>_. istate" and validTrans = validTrans and srcOf = "\<lambda>_. srcOf" and tgtOf = "\<lambda>_. tgtOf"
  and nodes = AIDs and comOf = comOf and tgtNodeOf = tgtNodeOf
  and sync = sync and \<phi> = \<phi> and f = f and \<gamma> = \<gamma> and g = g and T = T and B = B
  and comOfV = comOfV and tgtNodeOfV = tgtNodeOfV and syncV = syncV
  and comOfO = comOfO and tgtNodeOfO = tgtNodeOfO and syncO = syncO (*and cmpO = cmpO*)
  and source = AID and getTgtV = id
using AID_AIDs Issuer_B_Receiver_B Issuer.secure
by unfold_locales auto

theorem secure: "secure"
proof (intro preserve_source_secure ballI)
  fix aid
  interpret Receiver: OuterFriendReceiver UIDs AID UID aid by unfold_locales
  assume "aid \<in> AIDs - {AID}"
  then show "Net.lsecure aid" using Receiver.secure by auto
qed

end

end
