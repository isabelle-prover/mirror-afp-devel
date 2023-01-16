theory Post_Observation_Setup_RECEIVER
  imports "../Safety_Properties"
begin

subsection \<open>Confidentiality for a secret receiver node\<close>

text \<open>We verify that a group of users of a given node \<open>j\<close>
can learn nothing about the updates to the content of a post
\<open>PID\<close> located at a different node \<open>i\<close> beyond the
existence of an update unless \<open>PID\<close> is being shared between
the two nodes and one of the users is the admin at node \<open>j\<close> or becomes
a remote friend of \<open>PID\<close>'s owner, or \<open>PID\<close> is marked as public.
This is formulated as a BD Security
property and is proved by unwinding.

See \<^cite>\<open>"cosmedis-SandP2017"\<close> for more details.
\<close>

subsubsection\<open>Observation setup\<close>

(* *)
type_synonym obs = "act * out"

(* The observers are an arbitrary, but fixed set of users *)
locale Fixed_UIDs = fixes UIDs :: "userID set"
(* The secret is PID received from AID:  *)
locale Fixed_PID = fixes PID :: "postID"
locale Fixed_AID = fixes AID :: "apiID"

locale ObservationSetup_RECEIVER = Fixed_UIDs + Fixed_PID + Fixed_AID
begin

(*  *)
fun \<gamma> :: "(state,act,out) trans \<Rightarrow> bool" where
"\<gamma> (Trans _ a _ _) \<longleftrightarrow>
   (\<exists> uid. userOfA a = Some uid \<and> uid \<in> UIDs)
   \<or>
   (\<exists>ca. a = COMact ca)
   \<or>
   (\<exists>uid p. a = Sact (sSys uid p))"

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
