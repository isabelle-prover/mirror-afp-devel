theory Outer_Friend_Issuer_Observation_Setup
  imports "../Outer_Friend"
begin

subsection \<open>Issuer node\<close>

subsubsection \<open>Observation setup\<close>

text \<open>We now consider the network node \<open>AID\<close>, at which the user \<open>UID\<close> is registered, whose remote
   friends are to be kept confidential. \<close>
locale OuterFriendIssuer = OuterFriend
begin

fun \<gamma> :: "(state,act,out) trans \<Rightarrow> bool" where
"\<gamma> (Trans _ a ou _) \<longleftrightarrow> (\<exists> uid. userOfA a = Some uid \<and> uid \<in> UIDs AID) \<or>
                        (\<exists>ca. a = COMact ca \<and> ou \<noteq> outErr)"

text \<open>Purging communicating actions: password information is removed, the user IDs of friends
   added or deleted by \<open>UID\<close> are removed, and the information whether \<open>UID\<close> added or deleted
   a friend is removed \<close>

fun comPurge :: "comActt \<Rightarrow> comActt" where
 "comPurge (comSendServerReq uID p aID reqInfo) = comSendServerReq uID emptyPass aID reqInfo"
|"comPurge (comReceiveClientReq aID reqInfo) = comReceiveClientReq aID reqInfo"
|"comPurge (comConnectClient uID p aID sp) = comConnectClient uID emptyPass aID sp"
|"comPurge (comConnectServer aID sp) = comConnectServer aID sp"
|"comPurge (comReceivePost aID sp nID nt uID v) = comReceivePost aID sp nID nt uID v"
|"comPurge (comSendPost uID p aID nID) = comSendPost uID emptyPass aID nID"
|"comPurge (comSendCreateOFriend uID p aID uID') =
    (if uID = UID \<and> uID' \<notin> UIDs aID
     then comSendCreateOFriend uID emptyPass aID emptyUserID
     else comSendCreateOFriend uID emptyPass aID uID')"
|"comPurge (comReceiveCreateOFriend aID cp uID uID') = comReceiveCreateOFriend aID cp uID uID'"
|"comPurge (comSendDeleteOFriend uID p aID uID') =
    (if uID = UID \<and> uID' \<notin> UIDs aID
     then comSendCreateOFriend uID emptyPass aID emptyUserID
     else comSendDeleteOFriend uID emptyPass aID uID')"
|"comPurge (comReceiveDeleteOFriend aID cp uID uID') = comReceiveDeleteOFriend aID cp uID uID'"

lemma comPurge_simps:
  "comPurge ca = comSendServerReq uID p aID reqInfo \<longleftrightarrow> (\<exists>p'. ca = comSendServerReq uID p' aID reqInfo \<and> p = emptyPass)"
  "comPurge ca = comReceiveClientReq aID reqInfo \<longleftrightarrow> ca = comReceiveClientReq aID reqInfo"
  "comPurge ca = comConnectClient uID p aID sp \<longleftrightarrow> (\<exists>p'. ca = comConnectClient uID p' aID sp \<and> p = emptyPass)"
  "comPurge ca = comConnectServer aID sp \<longleftrightarrow> ca = comConnectServer aID sp"
  "comPurge ca = comReceivePost aID sp nID nt uID v \<longleftrightarrow> ca = comReceivePost aID sp nID nt uID v"
  "comPurge ca = comSendPost uID p aID nID \<longleftrightarrow> (\<exists>p'. ca = comSendPost uID p' aID nID \<and> p = emptyPass)"
  "comPurge ca = comSendCreateOFriend uID p aID uID'
\<longleftrightarrow> (\<exists>p' uid''. (ca = comSendCreateOFriend uID p' aID uid'' \<or> ca = comSendDeleteOFriend uID p' aID uid'') \<and> uID = UID \<and> uid'' \<notin> UIDs aID \<and> uID' = emptyUserID \<and> p = emptyPass)
    \<or> (\<exists>p'. ca = comSendCreateOFriend uID p' aID uID' \<and> \<not>(uID = UID \<and> uID' \<notin> UIDs aID) \<and> p = emptyPass)"
  "comPurge ca = comReceiveCreateOFriend aID cp uID uID' \<longleftrightarrow> ca = comReceiveCreateOFriend aID cp uID uID'"
  "comPurge ca = comSendDeleteOFriend uID p aID uID' \<longleftrightarrow> (\<exists>p'. ca = comSendDeleteOFriend uID p' aID uID' \<and> \<not>(uID = UID \<and> uID' \<notin> UIDs aID) \<and> p = emptyPass)"
  "comPurge ca = comReceiveDeleteOFriend aID cp uID uID' \<longleftrightarrow> ca = comReceiveDeleteOFriend aID cp uID uID'"
by (cases ca; auto)+

text \<open>Purging outputs: the user IDs of friends added or deleted
   by \<open>UID\<close> are removed from outer friend creation and deletion outputs.\<close>
fun outPurge :: "out \<Rightarrow> out" where
 "outPurge (O_sendCreateOFriend (aID, sp, uID, uID')) =
  (if uID = UID \<and> uID' \<notin> UIDs aID
   then O_sendCreateOFriend (aID, sp, uID, emptyUserID)
   else O_sendCreateOFriend (aID, sp, uID, uID'))"
|"outPurge (O_sendDeleteOFriend (aID, sp, uID, uID')) =
  (if uID = UID \<and> uID' \<notin> UIDs aID
   then O_sendCreateOFriend (aID, sp, uID, emptyUserID)
   else O_sendDeleteOFriend (aID, sp, uID, uID'))"
|"outPurge ou = ou"

lemma outPurge_simps[simp]:
  "outPurge ou = outErr \<longleftrightarrow> ou = outErr"
  "outPurge ou = outOK \<longleftrightarrow> ou = outOK"
  "outPurge ou = O_sendServerReq ossr \<longleftrightarrow> ou = O_sendServerReq ossr"
  "outPurge ou = O_connectClient occ \<longleftrightarrow> ou = O_connectClient occ"
  "outPurge ou = O_sendPost osn \<longleftrightarrow> ou = O_sendPost osn"
  "outPurge ou = O_sendCreateOFriend (aID, sp, uID, uID')
 \<longleftrightarrow> (\<exists>uid''. (ou = O_sendCreateOFriend (aID, sp, uID, uid'') \<or> ou = O_sendDeleteOFriend (aID, sp, uID, uid'')) \<and> uID = UID \<and> uid'' \<notin> UIDs aID \<and> uID' = emptyUserID)
     \<or> (ou = O_sendCreateOFriend (aID, sp, uID, uID') \<and> \<not>(uID = UID \<and> uID' \<notin> UIDs aID))"
  "outPurge ou = O_sendDeleteOFriend (aID, sp, uID, uID')
 \<longleftrightarrow> (ou = O_sendDeleteOFriend (aID, sp, uID, uID') \<and> \<not>(uID = UID \<and> uID' \<notin> UIDs aID))"
by (cases ou; cases "uID = UID"; auto)+

fun g :: "(state,act,out)trans \<Rightarrow> obs" where
 "g (Trans _ (COMact ca) ou _) = (COMact (comPurge ca), outPurge ou)"
|"g (Trans _ a ou _) = (a,ou)"

lemma g_simps:
  "g (Trans s a ou s') = (COMact (comSendServerReq uID p aID reqInfo), O_sendServerReq ossr)
\<longleftrightarrow> (\<exists>p'. a = COMact (comSendServerReq uID p' aID reqInfo) \<and> p = emptyPass \<and> ou = O_sendServerReq ossr)"
  "g (Trans s a ou s') = (COMact (comReceiveClientReq aID reqInfo), outOK)
\<longleftrightarrow> a = COMact (comReceiveClientReq aID reqInfo) \<and> ou = outOK"
  "g (Trans s a ou s') = (COMact (comConnectClient uID p aID sp), O_connectClient occ)
\<longleftrightarrow> (\<exists>p'. a = COMact (comConnectClient uID p' aID sp) \<and> p = emptyPass \<and> ou = O_connectClient occ)"
  "g (Trans s a ou s') = (COMact (comConnectServer aID sp), outOK)
\<longleftrightarrow> a = COMact (comConnectServer aID sp) \<and> ou = outOK"
  "g (Trans s a ou s') = (COMact (comReceivePost aID sp nID nt uID v), outOK)
\<longleftrightarrow> a = COMact (comReceivePost aID sp nID nt uID v) \<and> ou = outOK"
  "g (Trans s a ou s') = (COMact (comSendPost uID p aID nID), O_sendPost osn)
\<longleftrightarrow> (\<exists>p'. a = COMact (comSendPost uID p' aID nID) \<and> p = emptyPass \<and> ou = O_sendPost osn)"
  "g (Trans s a ou s') = (COMact (comSendCreateOFriend uID p aID uID'), O_sendCreateOFriend (aid, sp, uid, uid'))
\<longleftrightarrow> ((\<exists>p' uid''. (a = COMact (comSendCreateOFriend uID p' aID uid'') \<or> a = COMact (comSendDeleteOFriend uID p' aID uid'')) \<and> uID = UID \<and> uid'' \<notin> UIDs aID \<and> uID' = emptyUserID \<and> p = emptyPass)
    \<or> (\<exists>p'. a = COMact (comSendCreateOFriend uID p' aID uID') \<and> \<not>(uID = UID \<and> uID' \<notin> UIDs aID) \<and> p = emptyPass))
    \<and> ((\<exists>uid''. (ou = O_sendCreateOFriend (aid, sp, uid, uid'') \<or> ou = O_sendDeleteOFriend (aid, sp, uid, uid'')) \<and> uid = UID \<and> uid'' \<notin> UIDs aid \<and> uid' = emptyUserID)
     \<or> (ou = O_sendCreateOFriend (aid, sp, uid, uid') \<and> \<not>(uid = UID \<and> uid' \<notin> UIDs aid)))"
  "g (Trans s a ou s') = (COMact (comReceiveCreateOFriend aID cp uID uID'), outOK)
\<longleftrightarrow> a = COMact (comReceiveCreateOFriend aID cp uID uID') \<and> ou = outOK"
  "g (Trans s a ou s') = (COMact (comSendDeleteOFriend uID p aID uID'), O_sendDeleteOFriend (aid, sp, uid, uid'))
\<longleftrightarrow> (\<exists>p'. a = COMact (comSendDeleteOFriend uID p' aID uID') \<and> \<not>(uID = UID \<and> uID' \<notin> UIDs aID) \<and> p = emptyPass)
    \<and> (ou = O_sendDeleteOFriend (aid, sp, uid, uid') \<and> \<not>(uid = UID \<and> uid' \<notin> UIDs aid))"
  "g (Trans s a ou s') = (COMact (comReceiveDeleteOFriend aID cp uID uID'), outOK)
\<longleftrightarrow> a = COMact (comReceiveDeleteOFriend aID cp uID uID') \<and> ou = outOK"
  by (cases a; auto simp: comPurge_simps)+

end


end
