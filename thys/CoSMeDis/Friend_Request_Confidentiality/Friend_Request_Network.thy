theory Friend_Request_Network
  imports
    "../API_Network"
    "Friend_Request"
    "BD_Security_Compositional.Composing_Security_Network"
begin

subsection \<open>Confidentiality for the N-ary composition\<close>

locale FriendRequestNetwork = Network + FriendNetworkObservationSetup +
fixes
  AID :: apiID
and
  UID1 :: userID
and
  UID2 :: userID
assumes
  UID1_UID2_UIDs: "{UID1,UID2} \<inter> (UIDs AID) = {}"
and
  UID1_UID2: "UID1 \<noteq> UID2"
and
  AID_AIDs: "AID \<in> AIDs"
begin

sublocale Issuer: Friend "UIDs AID" UID1 UID2 using UID1_UID2_UIDs UID1_UID2 by unfold_locales

abbreviation \<phi> :: "apiID \<Rightarrow> (state, act, out) trans \<Rightarrow> bool"
where "\<phi> aid trn \<equiv> (Issuer.\<phi> trn \<and> aid = AID)"

abbreviation f :: "apiID \<Rightarrow> (state, act, out) trans \<Rightarrow> Friend.value"
where "f aid trn \<equiv> Friend.f UID1 UID2 trn"

abbreviation T :: "apiID \<Rightarrow> (state, act, out) trans \<Rightarrow> bool"
where "T aid trn \<equiv> False"

abbreviation B :: "apiID \<Rightarrow> Friend.value list \<Rightarrow> Friend.value list \<Rightarrow> bool"
where "B aid vl vl1 \<equiv> (if aid = AID then Issuer.B vl vl1 else (vl = [] \<and> vl1 = []))"

abbreviation "comOfV aid vl \<equiv> Internal"
abbreviation "tgtNodeOfV aid vl \<equiv> undefined"
abbreviation "syncV aid1 vl1 aid2 vl2 \<equiv> False"

lemma [simp]: "validTrans aid trn \<Longrightarrow> lreach aid (srcOf trn) \<Longrightarrow> \<phi> aid trn \<Longrightarrow> comOf aid trn = Internal"
by (cases trn) (auto elim: Issuer.\<phi>E)

sublocale Net: BD_Security_TS_Network_getTgtV
where istate = "\<lambda>_. istate" and validTrans = validTrans and srcOf = "\<lambda>_. srcOf" and tgtOf = "\<lambda>_. tgtOf"
  and nodes = AIDs and comOf = comOf (*and srcNodeOf = srcNodeOf*) and tgtNodeOf = tgtNodeOf
  and sync = sync and \<phi> = \<phi> and f = f and \<gamma> = \<gamma> and g = g and T = T and B = B
  and comOfV = comOfV and tgtNodeOfV = tgtNodeOfV and syncV = syncV
  and comOfO = comOfO and tgtNodeOfO = tgtNodeOfO and syncO = syncO (*and cmpO = cmpO*)
  and source = AID and getTgtV = id
proof (unfold_locales, goal_cases)
  case (1 aid trn) then show ?case by auto next
  case (2 aid trn) then show ?case by auto next
  case (3 aid trn) then show ?case by (cases trn) auto next
  case (4 aid trn) then show ?case by (cases "(aid,trn)" rule: tgtNodeOf.cases) auto next
  case (5 aid1 trn1 aid2 trn2) then show ?case by auto next
  case (6 aid1 trn1 aid2 trn2) then show ?case by (cases trn1; cases trn2; auto) next
  case (7 aid1 trn1 aid2 trn2) then show ?case by auto next
  case (8 aid1 trn1 aid2 trn2) then show ?case by (cases trn1; cases trn2; auto) next
  case (9 aid trn) then show ?case by (cases "(aid,trn)" rule: tgtNodeOf.cases) (auto simp: FriendObservationSetup.\<gamma>.simps) next
  case (10 aid trn) then show ?case by auto
qed auto

sublocale BD_Security_TS_Network_Preserve_Source_Security_getTgtV
where istate = "\<lambda>_. istate" and validTrans = validTrans and srcOf = "\<lambda>_. srcOf" and tgtOf = "\<lambda>_. tgtOf"
  and nodes = AIDs and comOf = comOf and tgtNodeOf = tgtNodeOf
  and sync = sync and \<phi> = \<phi> and f = f and \<gamma> = \<gamma> and g = g and T = T and B = B
  and comOfV = comOfV and tgtNodeOfV = tgtNodeOfV and syncV = syncV
  and comOfO = comOfO and tgtNodeOfO = tgtNodeOfO and syncO = syncO (*and cmpO = cmpO*)
  and source = AID and getTgtV = id
using AID_AIDs Issuer.secure
by unfold_locales auto

theorem secure: "secure"
proof (intro preserve_source_secure ballI)
  fix aid
  assume "aid \<in> AIDs - {AID}"
  then show "Net.lsecure aid" by (intro Abstract_BD_Security.B_id_secure) (auto simp: B_id_def)
qed

end

end
