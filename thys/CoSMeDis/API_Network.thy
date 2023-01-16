section \<open>The CoSMeDis network of communicating nodes \<close>

text \<open>This is the specification of an entire CoSMeDis network
of communicating  nodes, as described
in Section IV.B of \<^cite>\<open>"cosmedis-SandP2017"\<close>
NB: What that paper refers to as "nodes" are referred in this formalization
as "APIs".
\<close>

theory API_Network
imports
  "BD_Security_Compositional.Composing_Security_Network"
  System_Specification
begin

locale Network =
fixes AIDs :: "apiID set"
assumes finite_AIDs: "finite AIDs"
begin

fun comOfO :: "apiID \<Rightarrow> (act \<times> out) \<Rightarrow> com" where
  "comOfO aid (COMact (comSendServerReq uid password aID req), ou) =
    (if aid \<noteq> aID \<and> ou \<noteq> outErr then Send else Internal)"
| "comOfO aid (COMact (comConnectClient uID p aID sp), ou) =
    (if aid \<noteq> aID \<and> ou \<noteq> outErr then Send else Internal)"
| "comOfO aid (COMact (comSendPost uID p aID nID), ou) =
    (if aid \<noteq> aID \<and> ou \<noteq> outErr then Send else Internal)"
| "comOfO aid (COMact (comSendCreateOFriend uID p aID uID'), ou) =
    (if aid \<noteq> aID \<and> ou \<noteq> outErr then Send else Internal)"
| "comOfO aid (COMact (comSendDeleteOFriend uID p aID uID'), ou) =
    (if aid \<noteq> aID \<and> ou \<noteq> outErr then Send else Internal)"
| "comOfO aid (COMact (comReceiveClientReq aID req), ou) =
    (if aid \<noteq> aID \<and> ou \<noteq> outErr then Recv else Internal)"
| "comOfO aid (COMact (comConnectServer aID sp), ou) =
    (if aid \<noteq> aID \<and> ou \<noteq> outErr then Recv else Internal)"
| "comOfO aid (COMact (comReceivePost aID sp nID ntc uid v), ou) =
    (if aid \<noteq> aID \<and> ou \<noteq> outErr then Recv else Internal)"
| "comOfO aid (COMact (comReceiveCreateOFriend aID sp uid uid'), ou) =
    (if aid \<noteq> aID \<and> ou \<noteq> outErr then Recv else Internal)"
| "comOfO aid (COMact (comReceiveDeleteOFriend aID sp uid uid'), ou) =
    (if aid \<noteq> aID \<and> ou \<noteq> outErr then Recv else Internal)"
| "comOfO _ _ = Internal"

fun comOf :: "apiID \<Rightarrow> (state, act, out) trans \<Rightarrow> com" where
  "comOf aid (Trans _ a ou _) = comOfO aid (a, ou)"

fun syncO :: "apiID \<Rightarrow> (act \<times> out) \<Rightarrow> apiID \<Rightarrow> (act \<times> out) \<Rightarrow> bool" where
  "syncO aid1 (COMact (comSendServerReq uid p aid req), ou1) aid2 (a2, ou2) =
     (\<exists>req2. a2 = (COMact (comReceiveClientReq aid1 req2)) \<and> ou1 = O_sendServerReq (aid2,req2) \<and> ou2 = outOK)"
| "syncO aid1 (COMact (comConnectClient uid p aid sp), ou1) aid2 (a2, ou2) =
     (\<exists>sp2. a2 = (COMact (comConnectServer aid1 sp2)) \<and> ou1 = O_connectClient (aid2,sp2) \<and> ou2 = outOK)"
| "syncO aid1 (COMact (comSendPost uid p aid nid), ou1) aid2 (a2, ou2) =
     (\<exists>sp2 nid2 ntc2 uid2 v. a2 = (COMact (comReceivePost aid1 sp2 nid2 ntc2 uid2 v)) \<and> ou1 = O_sendPost (aid2, sp2, nid2, ntc2, uid2, v) \<and> ou2 = outOK)"
| "syncO aid1 (COMact (comSendCreateOFriend uid p aid uid'), ou1) aid2 (a2, ou2) =
     (\<exists>sp2 uid2 uid2'. a2 = (COMact (comReceiveCreateOFriend aid1 sp2 uid2 uid2')) \<and> ou1 = O_sendCreateOFriend (aid2, sp2, uid2, uid2') \<and> ou2 = outOK)"
| "syncO aid1 (COMact (comSendDeleteOFriend uid p aid uid'), ou1) aid2 (a2, ou2) =
     (\<exists>sp2 uid2 uid2'. a2 = (COMact (comReceiveDeleteOFriend aid1 sp2 uid2 uid2')) \<and> ou1 = O_sendDeleteOFriend (aid2, sp2, uid2, uid2') \<and> ou2 = outOK)"
| "syncO _ _ _ _ = False"

fun cmpO :: "apiID \<Rightarrow> (act \<times> out) \<Rightarrow> apiID \<Rightarrow> (act \<times> out) \<Rightarrow> (apiID \<times> act \<times> out \<times> apiID \<times> act \<times> out)" where
  "cmpO aid1 obs1 aid2 obs2 = (aid1, fst obs1, snd obs1, aid2, fst obs2, snd obs2)"

fun sync :: "apiID \<Rightarrow> (state, act, out) trans \<Rightarrow> apiID \<Rightarrow> (state, act, out) trans \<Rightarrow> bool" where
  "sync aid1 (Trans s1 a1 ou1 s1') aid2 (Trans s2 a2 ou2 s2') = syncO aid1 (a1, ou1) aid2 (a2, ou2)"


lemma syncO_cases:
assumes "syncO aid1 obs1 aid2 obs2"
obtains
  (Req) uid p aid req1 req2
  where "obs1 = (COMact (comSendServerReq uid p aid req1), O_sendServerReq (aid2,req2))"
    and "obs2 = (COMact (comReceiveClientReq aid1 req2), outOK)"
| (Connect) uid p aid sp sp2
  where "obs1 = (COMact (comConnectClient uid p aid sp), O_connectClient (aid2,sp2))"
    and "obs2 = (COMact (comConnectServer aid1 sp2), outOK)"
| (Notice) uid p aid nid sp2 nid2 ntc2 own2 v
  where "obs1 = (COMact (comSendPost uid p aid nid), O_sendPost (aid2, sp2, nid2, ntc2, own2, v))"
    and "obs2 = (COMact (comReceivePost aid1 sp2 nid2 ntc2 own2 v), outOK)"
| (CFriend) uid p aid uid' sp2 uid2 uid2'
  where "obs1 = (COMact (comSendCreateOFriend uid p aid uid'), O_sendCreateOFriend (aid2, sp2, uid2, uid2'))"
    and "obs2 = (COMact (comReceiveCreateOFriend aid1 sp2 uid2 uid2'), outOK)"
| (DFriend) uid p aid uid' sp2 uid2 uid2'
  where "obs1 = (COMact (comSendDeleteOFriend uid p aid uid'), O_sendDeleteOFriend (aid2, sp2, uid2, uid2'))"
    and "obs2 = (COMact (comReceiveDeleteOFriend aid1 sp2 uid2 uid2'), outOK)"
using assms by (cases "(aid1,obs1,aid2,obs2)" rule: syncO.cases) auto

lemma sync_cases:
assumes "sync aid1 trn1 aid2 trn2"
and "validTrans trn1"
obtains
  (Req) uid p aid req s1 s1' s2 s2'
  where "trn1 = Trans s1 (COMact (comSendServerReq uid p aid req)) (O_sendServerReq (aid2,req)) s1'"
    and "trn2 = Trans s2 (COMact (comReceiveClientReq aid1 req)) outOK s2'"
| (Connect) uid p aid sp s1 s1' s2 s2'
  where "trn1 = Trans s1 (COMact (comConnectClient uid p aid sp)) (O_connectClient (aid2,sp)) s1'"
    and "trn2 = Trans s2 (COMact (comConnectServer aid1 sp)) outOK s2'"
| (Notice) uid p aid nid sp2 nid2 ntc2 own2 v s1 s1' s2 s2'
  where "trn1 = Trans s1 (COMact (comSendPost uid p aid nid)) (O_sendPost (aid2, sp2, nid2, ntc2, own2, v)) s1'"
    and "trn2 = Trans s2 (COMact (comReceivePost aid1 sp2 nid2 ntc2 own2 v)) outOK s2'"
| (CFriend) uid p uid' sp s1 s1' s2 s2'
  where "trn1 = Trans s1 (COMact (comSendCreateOFriend uid p aid2 uid')) (O_sendCreateOFriend (aid2, sp, uid, uid')) s1'"
    and "trn2 = Trans s2 (COMact (comReceiveCreateOFriend aid1 sp uid uid')) outOK s2'"
| (DFriend) uid p aid uid' sp s1 s1' s2 s2'
  where "trn1 = Trans s1 (COMact (comSendDeleteOFriend uid p aid2 uid')) (O_sendDeleteOFriend (aid2, sp, uid, uid')) s1'"
    and "trn2 = Trans s2 (COMact (comReceiveDeleteOFriend aid1 sp uid uid')) outOK s2'"
  using assms
  by (cases trn1; cases trn2) (auto elim!: syncO_cases simp: com_defs split: if_splits)

fun tgtNodeOfO :: "apiID \<Rightarrow> (act \<times> out) \<Rightarrow> apiID" where
  "tgtNodeOfO _ (COMact (comSendServerReq uID p aID reqInfo), ou) = aID"
| "tgtNodeOfO _ (COMact (comReceiveClientReq aID reqInfo), ou) = aID"
| "tgtNodeOfO _ (COMact (comConnectClient uID p aID sp), ou) = aID"
| "tgtNodeOfO _ (COMact (comConnectServer aID sp), ou) = aID"
| "tgtNodeOfO _ (COMact (comSendPost uID p aID nID), ou) = aID"
| "tgtNodeOfO _ (COMact (comReceivePost aID sp nID title text v), ou) = aID"
| "tgtNodeOfO _ (COMact (comSendCreateOFriend uID p aID uID'), ou) = aID"
| "tgtNodeOfO _ (COMact (comReceiveCreateOFriend aID sp uid uid'), ou) = aID"
| "tgtNodeOfO _ (COMact (comSendDeleteOFriend uID p aID uID'), ou) = aID"
| "tgtNodeOfO _ (COMact (comReceiveDeleteOFriend aID sp uid uid'), ou) = aID"
| "tgtNodeOfO _ _ = undefined"

fun tgtNodeOf :: "apiID \<Rightarrow> (state, act, out) trans \<Rightarrow> apiID" where
  "tgtNodeOf _ (Trans s (COMact (comSendServerReq uID p aID reqInfo)) ou s') = aID"
| "tgtNodeOf _ (Trans s (COMact (comReceiveClientReq aID reqInfo)) ou s') = aID"
| "tgtNodeOf _ (Trans s (COMact (comConnectClient uID p aID sp)) ou s') = aID"
| "tgtNodeOf _ (Trans s (COMact (comConnectServer aID sp)) ou s') = aID"
| "tgtNodeOf _ (Trans s (COMact (comSendPost uID p aID nID)) ou s') = aID"
| "tgtNodeOf _ (Trans s (COMact (comReceivePost aID sp nID title text v)) ou s') = aID"
| "tgtNodeOf _ (Trans s (COMact (comSendCreateOFriend uID p aID uID')) ou s') = aID"
| "tgtNodeOf _ (Trans s (COMact (comReceiveCreateOFriend aID sp uid uid')) ou s') = aID"
| "tgtNodeOf _ (Trans s (COMact (comSendDeleteOFriend uID p aID uID')) ou s') = aID"
| "tgtNodeOf _ (Trans s (COMact (comReceiveDeleteOFriend aID sp uid uid')) ou s') = aID"
| "tgtNodeOf _ _ = undefined"

abbreviation validTrans :: "apiID \<Rightarrow> (state, act, out) trans \<Rightarrow> bool" where
  "validTrans aid \<equiv> System_Specification.validTrans"

sublocale TS_Network
where istate = "\<lambda>_. istate" and validTrans = validTrans and srcOf = "\<lambda>_. srcOf" and tgtOf = "\<lambda>_. tgtOf"
  and nodes = AIDs and comOf = comOf and tgtNodeOf = tgtNodeOf
  and sync = sync
proof (unfold_locales, goal_cases)
  case (1) show ?case using finite_AIDs . next
  case (2 aid trn)
    from 2 show ?case
      by (cases "(aid, trn)" rule: tgtNodeOf.cases) auto
qed

end

end
