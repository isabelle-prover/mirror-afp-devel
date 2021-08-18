(* Strengthened observation setup, customized for post confidentiality *)
theory Independent_Post_Observation_Setup_RECEIVER
  imports
    "../../Safety_Properties"
    "../Post_Observation_Setup_RECEIVER"
begin

subsubsection \<open>Receiver observation setup\<close>

locale Strong_ObservationSetup_RECEIVER = Fixed_UIDs + Fixed_PID + Fixed_AID
begin

(*  *)
fun \<gamma> :: "(state,act,out) trans \<Rightarrow> bool" where
"\<gamma> (Trans _ a _ _) \<longleftrightarrow>
   (\<exists> uid. userOfA a = Some uid \<and> uid \<in> UIDs)
   \<or>
   \<comment> \<open>Communication actions are considered to be observable in order to make the security
       properties compositional\<close>
   (\<exists>ca. a = COMact ca)
   \<or>
   \<comment> \<open>The following actions are added to strengthen the observers in order to show that all
      posts \<^emph>\<open>other than \<open>PID\<close> of \<open>AID\<close>\<close> are completely independent of that post;  the
      confidentiality of the latter is protected even if the observers can see all updates to
      other posts (and actions contributing to the declassification triggers of those posts).\<close>
   (\<exists>uid p pid pst. a = Uact (uPost uid p pid pst))
   \<or>
   (\<exists>uid p. a = Sact (sSys uid p))
   \<or>
   (\<exists>uid p uid' p'. a = Cact (cUser uid p uid' p'))
   \<or>
   (\<exists>uid p pid. a = Cact (cPost uid p pid))
   \<or>
   (\<exists>uid p uid'. a = Cact (cFriend uid p uid'))
   \<or>
   (\<exists>uid p uid'. a = Dact (dFriend uid p uid'))
   \<or>
   (\<exists>uid p pid v. a = Uact (uVisPost uid p pid v))"

(* Note: the passwords don't really have to be purged (since identity theft is not
considered in the first place); however, purging passwords looks more sane. *)

(* Purging the password in starting actions: *)
fun sPurge :: "sActt \<Rightarrow> sActt" where
"sPurge (sSys uid pwd) = sSys uid emptyPass"

(* Purging communicating actions: user-password information is removed, and post content for PID
  is removed from the only kind of action that may contain such info: comReceivePost.
  Note: server-password info is not purged --todo: discuss this.  *)
fun comPurge :: "comActt \<Rightarrow> comActt" where
 "comPurge (comSendServerReq uID p aID reqInfo) = comSendServerReq uID emptyPass aID reqInfo"
|"comPurge (comConnectClient uID p aID sp) = comConnectClient uID emptyPass aID sp"
(* *)
|"comPurge (comReceivePost aID sp pID pst uID vs) =
  (let pst' = (if aID = AID \<and> pID = PID then emptyPost else pst)
   in comReceivePost aID sp pID pst' uID vs)"
(* *)
|"comPurge (comSendPost uID p aID pID) = comSendPost uID emptyPass aID pID"
|"comPurge (comSendCreateOFriend uID p aID uID') = comSendCreateOFriend uID emptyPass aID uID'"
|"comPurge (comSendDeleteOFriend uID p aID uID') = comSendDeleteOFriend uID emptyPass aID uID'"
|"comPurge ca = ca"

(* Note: No output purge here -- only for the issuer. *)

fun g :: "(state,act,out)trans \<Rightarrow> obs" where
 "g (Trans _ (Sact sa) ou _) = (Sact (sPurge sa), ou)"
|"g (Trans _ (COMact ca) ou _) = (COMact (comPurge ca), ou)"
|"g (Trans _ a ou _) = (a,ou)"

lemma comPurge_simps:
  "comPurge ca = comSendServerReq uID p aID reqInfo \<longleftrightarrow> (\<exists>p'. ca = comSendServerReq uID p' aID reqInfo \<and> p = emptyPass)"
  "comPurge ca = comReceiveClientReq aID reqInfo \<longleftrightarrow> ca = comReceiveClientReq aID reqInfo"
  "comPurge ca = comConnectClient uID p aID sp \<longleftrightarrow> (\<exists>p'. ca = comConnectClient uID p' aID sp \<and> p = emptyPass)"
  "comPurge ca = comConnectServer aID sp \<longleftrightarrow> ca = comConnectServer aID sp"
  "comPurge ca = comReceivePost aID sp pID pst' uID v \<longleftrightarrow> (\<exists>pst. ca = comReceivePost aID sp pID pst uID v \<and> pst' = (if pID = PID \<and> aID = AID then emptyPost else pst))"
  "comPurge ca = comSendPost uID p aID pID \<longleftrightarrow> (\<exists>p'. ca = comSendPost uID p' aID pID \<and> p = emptyPass)"
  "comPurge ca = comSendCreateOFriend uID p aID uID' \<longleftrightarrow> (\<exists>p'. ca = comSendCreateOFriend uID p' aID uID' \<and> p = emptyPass)"
  "comPurge ca = comReceiveCreateOFriend aID cp uID uID' \<longleftrightarrow> ca = comReceiveCreateOFriend aID cp uID uID'"
  "comPurge ca = comSendDeleteOFriend uID p aID uID' \<longleftrightarrow> (\<exists>p'. ca = comSendDeleteOFriend uID p' aID uID' \<and> p = emptyPass)"
  "comPurge ca = comReceiveDeleteOFriend aID cp uID uID' \<longleftrightarrow> ca = comReceiveDeleteOFriend aID cp uID uID'"
by (cases ca; auto)+

lemma g_simps:
  "g (Trans s a ou s') = (COMact (comSendServerReq uID p aID reqInfo), ou')
\<longleftrightarrow> (\<exists>p'. a = COMact (comSendServerReq uID p' aID reqInfo) \<and> p = emptyPass \<and> ou = ou')"
  "g (Trans s a ou s') = (COMact (comReceiveClientReq aID reqInfo), ou')
\<longleftrightarrow> a = COMact (comReceiveClientReq aID reqInfo) \<and> ou = ou'"
  "g (Trans s a ou s') = (COMact (comConnectClient uID p aID sp), ou')
\<longleftrightarrow> (\<exists>p'. a = COMact (comConnectClient uID p' aID sp) \<and> p = emptyPass \<and> ou = ou')"
  "g (Trans s a ou s') = (COMact (comConnectServer aID sp), ou')
\<longleftrightarrow> a = COMact (comConnectServer aID sp) \<and> ou = ou'"
  "g (Trans s a ou s') = (COMact (comReceivePost aID sp pID pst' uID v), ou')
\<longleftrightarrow> (\<exists>pst. a = COMact (comReceivePost aID sp pID pst uID v) \<and> pst' = (if pID = PID \<and> aID = AID then emptyPost else pst) \<and> ou = ou')"
   "g (Trans s a ou s') = (COMact (comSendPost uID p aID nID), O_sendPost (aid, sp, pid, pst, own, v))
\<longleftrightarrow> (\<exists>p'. a = COMact (comSendPost uID p' aID nID) \<and> p = emptyPass \<and> ou = O_sendPost (aid, sp, pid, pst, own, v))"
  "g (Trans s a ou s') = (COMact (comSendCreateOFriend uID p aID uID'), ou')
\<longleftrightarrow> (\<exists>p'. a = (COMact (comSendCreateOFriend uID p' aID uID')) \<and> p = emptyPass \<and> ou = ou')"
  "g (Trans s a ou s') = (COMact (comReceiveCreateOFriend aID cp uID uID'), ou')
\<longleftrightarrow> a = COMact (comReceiveCreateOFriend aID cp uID uID') \<and> ou = ou'"
  "g (Trans s a ou s') = (COMact (comSendDeleteOFriend uID p aID uID'), ou')
\<longleftrightarrow> (\<exists>p'. a = COMact (comSendDeleteOFriend uID p' aID uID') \<and> p = emptyPass \<and> ou = ou')"
  "g (Trans s a ou s') = (COMact (comReceiveDeleteOFriend aID cp uID uID'), ou')
\<longleftrightarrow> a = COMact (comReceiveDeleteOFriend aID cp uID uID') \<and> ou = ou'"
by (cases a; auto simp: comPurge_simps ObservationSetup_RECEIVER.comPurge.simps)+

end

end
