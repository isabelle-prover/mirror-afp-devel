theory Outer_Friend_Receiver_Observation_Setup
  imports "../Outer_Friend"
begin

subsection \<open>Receiver nodes\<close>

subsubsection \<open>Observation setup\<close>

(* We now consider one arbitrary, but fixed network node receiving secrets *)
locale OuterFriendReceiver = OuterFriend +
fixes AID' :: apiID \<comment> \<open>The ID of this (arbitrary, but fixed) receiver node\<close>
begin

(*  *)
fun \<gamma> :: "(state,act,out) trans \<Rightarrow> bool" where
"\<gamma> (Trans _ a ou _) \<longleftrightarrow> (\<exists> uid. userOfA a = Some uid \<and> uid \<in> UIDs AID') \<or>
                        (\<exists>ca. a = COMact ca \<and> ou \<noteq> outErr)"

(* Note: the passwords don't really have to be purged (since identity theft is not
considered in the first place); however, purging passwords looks more sane. *)

(* Purging the password in starting actions: *)
fun sPurge :: "sActt \<Rightarrow> sActt" where
"sPurge (sSys uid pwd) = sSys uid emptyPass"

(* Purging communicating actions: password information is removed, the user IDs of friends
   added or deleted by UID are removed, and the information whether UID added or deleted
   a friend is removed *)
fun comPurge :: "comActt \<Rightarrow> comActt" where
 "comPurge (comSendServerReq uID p aID reqInfo) = comSendServerReq uID emptyPass aID reqInfo"
|"comPurge (comReceiveClientReq aID reqInfo) = comReceiveClientReq aID reqInfo"
|"comPurge (comConnectClient uID p aID sp) = comConnectClient uID emptyPass aID sp"
|"comPurge (comConnectServer aID sp) = comConnectServer aID sp"
|"comPurge (comReceivePost aID sp nID nt uID v) = comReceivePost aID sp nID nt uID v"
|"comPurge (comSendPost uID p aID nID) = comSendPost uID emptyPass aID nID"
|"comPurge (comSendCreateOFriend uID p aID uID') = comSendCreateOFriend uID emptyPass aID uID'"
    (*(if aID = AID \<and> uID = UID \<and> uID' \<notin> UIDs AID'
     then comSendCreateOFriend uID emptyPass aID emptyUserID
     else comSendCreateOFriend uID emptyPass aID uID')"*)
|"comPurge (comReceiveCreateOFriend aID cp uID uID') =
    (if aID = AID \<and> uID = UID \<and> uID' \<notin> UIDs AID'
     then comReceiveCreateOFriend aID cp uID emptyUserID
     else comReceiveCreateOFriend aID cp uID uID')"
|"comPurge (comSendDeleteOFriend uID p aID uID') = comSendDeleteOFriend uID emptyPass aID uID'"
    (*(if aID = AID \<and> uID = UID \<and> uID' \<notin> UIDs AID'
     then comSendCreateOFriend uID emptyPass aID emptyUserID
     else comSendDeleteOFriend uID emptyPass aID uID')"*)
|"comPurge (comReceiveDeleteOFriend aID cp uID uID') =
    (if aID = AID \<and> uID = UID \<and> uID' \<notin> UIDs AID'
     then comReceiveCreateOFriend aID cp uID emptyUserID
     else comReceiveDeleteOFriend aID cp uID uID')"

lemma comPurge_simps:
  "comPurge ca = comSendServerReq uID p aID reqInfo \<longleftrightarrow> (\<exists>p'. ca = comSendServerReq uID p' aID reqInfo \<and> p = emptyPass)"
  "comPurge ca = comReceiveClientReq aID reqInfo \<longleftrightarrow> ca = comReceiveClientReq aID reqInfo"
  "comPurge ca = comConnectClient uID p aID sp \<longleftrightarrow> (\<exists>p'. ca = comConnectClient uID p' aID sp \<and> p = emptyPass)"
  "comPurge ca = comConnectServer aID sp \<longleftrightarrow> ca = comConnectServer aID sp"
  "comPurge ca = comReceivePost aID sp nID nt uID v \<longleftrightarrow> ca = comReceivePost aID sp nID nt uID v"
  "comPurge ca = comSendPost uID p aID nID \<longleftrightarrow> (\<exists>p'. ca = comSendPost uID p' aID nID \<and> p = emptyPass)"
  "comPurge ca = comSendCreateOFriend uID p aID uID' \<longleftrightarrow> (\<exists>p'. ca = comSendCreateOFriend uID p' aID uID' \<and> p = emptyPass)"
  "comPurge ca = comReceiveCreateOFriend aID cp uID uID'
\<longleftrightarrow> (\<exists>uid''. (ca = comReceiveCreateOFriend aID cp uID uid'' \<or> ca = comReceiveDeleteOFriend aID cp uID uid'') \<and> aID = AID \<and> uID = UID \<and> uid'' \<notin> UIDs AID' \<and> uID' = emptyUserID)
    \<or> (ca = comReceiveCreateOFriend aID cp uID uID' \<and> \<not>(aID = AID \<and> uID = UID \<and> uID' \<notin> UIDs AID'))"
  "comPurge ca = comSendDeleteOFriend uID p aID uID' \<longleftrightarrow> (\<exists>p'. ca = comSendDeleteOFriend uID p' aID uID' \<and> p = emptyPass)"
  "comPurge ca = comReceiveDeleteOFriend aID cp uID uID' \<longleftrightarrow> ca = comReceiveDeleteOFriend aID cp uID uID' \<and> \<not>(aID = AID \<and> uID = UID \<and> uID' \<notin> UIDs AID')"
by (cases ca; auto)+

(* Purging outputs: password information is removed, and the user IDs of friends added or deleted
   by UID are removed from the only kind of output that may contain such info: outAIDPUIDUID   *)
(*n outPurge :: "out \<Rightarrow> out" where
 "outPurge (outAIDPUIDUID (aID, sp, uID, uID')) =
  (if aID = AID \<and> uID = UID \<and> uID' \<notin> UIDs AID'
   then outAIDPUIDUID (aID, sp, uID, emptyUserID)
   else outAIDPUIDUID (aID, sp, uID, uID'))"
|"outPurge ou = ou"

lemma outPurge_outErr[simp]: "outPurge ou = outErr \<longleftrightarrow> ou = outErr"
by (cases ou) auto*)

fun g :: "(state,act,out)trans \<Rightarrow> obs" where
 "g (Trans _ (Sact sa) ou _) = (Sact (sPurge sa), ou)"
|"g (Trans _ (COMact ca) ou _) = (COMact (comPurge ca), ou)"
|"g (Trans _ a ou _) = (a,ou)"

lemma g_simps:
  "g (Trans s a ou s') = (COMact (comSendServerReq uID p aID reqInfo), ou')
\<longleftrightarrow> (\<exists>p'. a = COMact (comSendServerReq uID p' aID reqInfo) \<and> p = emptyPass \<and> ou = ou')"
  "g (Trans s a ou s') = (COMact (comReceiveClientReq aID reqInfo), ou')
\<longleftrightarrow> a = COMact (comReceiveClientReq aID reqInfo) \<and> ou = ou'"
  "g (Trans s a ou s') = (COMact (comConnectClient uID p aID sp), ou')
\<longleftrightarrow> (\<exists>p'. a = COMact (comConnectClient uID p' aID sp) \<and> p = emptyPass \<and> ou = ou')"
  "g (Trans s a ou s') = (COMact (comConnectServer aID sp), ou')
\<longleftrightarrow> a = COMact (comConnectServer aID sp) \<and> ou = ou'"
  "g (Trans s a ou s') = (COMact (comReceivePost aID sp nID nt uID v), ou')
\<longleftrightarrow> a = COMact (comReceivePost aID sp nID nt uID v) \<and> ou = ou'"
  "g (Trans s a ou s') = (COMact (comSendPost uID p aID nID), ou')
\<longleftrightarrow> (\<exists>p'. a = COMact (comSendPost uID p' aID nID) \<and> p = emptyPass \<and> ou = ou')"
  "g (Trans s a ou s') = (COMact (comSendCreateOFriend uID p aID uID'), ou')
\<longleftrightarrow> (\<exists>p'. a = COMact (comSendCreateOFriend uID p' aID uID') \<and> p = emptyPass \<and> ou = ou')"
  "g (Trans s a ou s') = (COMact (comReceiveCreateOFriend aID cp uID uID'), ou')
\<longleftrightarrow> (((\<exists>uid''. (a = COMact (comReceiveCreateOFriend aID cp uID uid'') \<or> a = COMact (comReceiveDeleteOFriend aID cp uID uid'')) \<and> aID = AID \<and> uID = UID \<and> uid'' \<notin> UIDs AID' \<and> uID' = emptyUserID)
    \<or> (a = COMact (comReceiveCreateOFriend aID cp uID uID') \<and> \<not>(aID = AID \<and> uID = UID \<and> uID' \<notin> UIDs AID')))
    \<and> ou = ou')"
  "g (Trans s a ou s') = (COMact (comSendDeleteOFriend uID p aID uID'), ou')
\<longleftrightarrow> (\<exists>p'. a = COMact (comSendDeleteOFriend uID p' aID uID') \<and> p = emptyPass \<and> ou = ou')"
  "g (Trans s a ou s') = (COMact (comReceiveDeleteOFriend aID cp uID uID'), ou')
\<longleftrightarrow> a = COMact (comReceiveDeleteOFriend aID cp uID uID') \<and> \<not>(aID = AID \<and> uID = UID \<and> uID' \<notin> UIDs AID') \<and> ou = ou'"
by (cases a; auto simp: comPurge_simps)+

end

(*
locale FriendNetworkObservationSetup =
fixes UIDs :: "apiID \<Rightarrow> userID set"
and UID :: "userID"
begin

(*  *)
abbreviation \<gamma> :: "apiID \<Rightarrow> (state,act,out) trans \<Rightarrow> bool" where
"\<gamma> aid trn \<equiv> FriendObservationSetup.\<gamma> (UIDs aid) trn"

abbreviation g :: "apiID \<Rightarrow> (state,act,out)trans \<Rightarrow> obs" where
"g aid trn \<equiv> FriendObservationSetup.g UID trn"

end
*)

end
