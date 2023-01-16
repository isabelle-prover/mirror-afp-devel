(* Strengthened observation setup, customized for post confidentiality *)
theory Post_Observation_Setup_ISSUER
  imports Post_Intro
begin

subsection \<open>Confidentiality for a secret issuer node\<close>


text \<open>\label{sec:post-issuer}
We verify that a group of users of a given node \<open>i\<close>
can learn nothing about the updates to the content of a post
\<open>PID\<close> located at that node beyond the existence of an update
unless one of them is the admin or the owner of \<open>PID\<close>,
or becomes friends with the owner,
or \<open>PID\<close> is marked as public. This is formulated as a BD Security
property and is proved by unwinding.

See \<^cite>\<open>"cosmedis-SandP2017"\<close> for more details.
\<close>

subsubsection \<open>Observation setup\<close>

(* *)
type_synonym obs = "act * out"

(* The observers are an arbitrary, but fixed set of users *)
locale Fixed_UIDs = fixes UIDs :: "userID set"
(* The secret is PID: *)
locale Fixed_PID = fixes PID :: "postID"

locale ObservationSetup_ISSUER = Fixed_UIDs + Fixed_PID
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

(* Purging communicating actions: user-password information is removed.
  Note: comReceivePost is not affected by the purging, in that post content
  is not removed; this only happens on the receiving end.
  (Also, nothing to purge in comSendPost either -- the output will be purged here, since
   only the output contains an actual post.)


  Note: server-password info is not purged --todo: discuss this.  *)
fun comPurge :: "comActt \<Rightarrow> comActt" where
 "comPurge (comSendServerReq uID p aID reqInfo) = comSendServerReq uID emptyPass aID reqInfo"
|"comPurge (comConnectClient uID p aID sp) = comConnectClient uID emptyPass aID sp"
|"comPurge (comConnectServer aID sp) = comConnectServer aID sp"
|"comPurge (comSendPost uID p aID pID) = comSendPost uID emptyPass aID pID"
|"comPurge (comSendCreateOFriend uID p aID uID') = comSendCreateOFriend uID emptyPass aID uID'"
|"comPurge (comSendDeleteOFriend uID p aID uID') = comSendDeleteOFriend uID emptyPass aID uID'"
|"comPurge ca = ca"

(* Purging outputs: post content for PID
  is removed from the post sending outputs
  (Again, server-password info is not purged.)   *)
fun outPurge :: "out \<Rightarrow> out" where
 "outPurge (O_sendPost (aID, sp, pID, pst, uID, vs)) =
  (let pst' = (if pID = PID then emptyPost else pst)
   in O_sendPost (aID, sp, pID, pst', uID, vs))"
|"outPurge ou = ou"

fun g :: "(state,act,out)trans \<Rightarrow> obs" where
 "g (Trans _ (Sact sa) ou _) = (Sact (sPurge sa), outPurge ou)"
|"g (Trans _ (COMact ca) ou _) = (COMact (comPurge ca), outPurge ou)"
|"g (Trans _ a ou _) = (a,ou)"

lemma comPurge_simps:
  "comPurge ca = comSendServerReq uID p aID reqInfo \<longleftrightarrow> (\<exists>p'. ca = comSendServerReq uID p' aID reqInfo \<and> p = emptyPass)"
  "comPurge ca = comReceiveClientReq aID reqInfo \<longleftrightarrow> ca = comReceiveClientReq aID reqInfo"
  "comPurge ca = comConnectClient uID p aID sp \<longleftrightarrow> (\<exists>p'. ca = comConnectClient uID p' aID sp \<and> p = emptyPass)"
  "comPurge ca = comConnectServer aID sp \<longleftrightarrow> ca = comConnectServer aID sp"
  "comPurge ca = comReceivePost aID sp nID nt uID v \<longleftrightarrow> ca = comReceivePost aID sp nID nt uID v"
  "comPurge ca = comSendPost uID p aID nID \<longleftrightarrow> (\<exists>p'. ca = comSendPost uID p' aID nID \<and> p = emptyPass)"
  "comPurge ca = comSendCreateOFriend uID p aID uID' \<longleftrightarrow> (\<exists>p'. ca = comSendCreateOFriend uID p' aID uID' \<and> p = emptyPass)"
  "comPurge ca = comReceiveCreateOFriend aID cp uID uID' \<longleftrightarrow> ca = comReceiveCreateOFriend aID cp uID uID'"
  "comPurge ca = comSendDeleteOFriend uID p aID uID' \<longleftrightarrow> (\<exists>p'. ca = comSendDeleteOFriend uID p' aID uID' \<and> p = emptyPass)"
  "comPurge ca = comReceiveDeleteOFriend aID cp uID uID' \<longleftrightarrow> ca = comReceiveDeleteOFriend aID cp uID uID'"
by (cases ca; auto)+

lemma outPurge_simps[simp]:
  "outPurge ou = outErr \<longleftrightarrow> ou = outErr"
  "outPurge ou = outOK \<longleftrightarrow> ou = outOK"
  "outPurge ou = O_sendServerReq ossr \<longleftrightarrow> ou = O_sendServerReq ossr"
  "outPurge ou = O_connectClient occ \<longleftrightarrow> ou = O_connectClient occ"
  "outPurge ou = O_sendPost (aid, sp, pid, pst', uid, vs) \<longleftrightarrow> (\<exists>pst.
     ou = O_sendPost (aid, sp, pid, pst, uid, vs) \<and>
     pst' = (if pid = PID then emptyPost else pst))"
  "outPurge ou = O_sendCreateOFriend oscf \<longleftrightarrow> ou = O_sendCreateOFriend oscf"
  "outPurge ou = O_sendDeleteOFriend osdf \<longleftrightarrow> ou = O_sendDeleteOFriend osdf"
by (cases ou; auto simp: ObservationSetup_ISSUER.outPurge.simps)+


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
  "g (Trans s a ou s') = (COMact (comSendPost uID p aID nID), O_sendPost (aid, sp, pid, pst', uid, vs))
\<longleftrightarrow> (\<exists>pst p'. a = COMact (comSendPost uID p' aID nID) \<and> p = emptyPass \<and> ou = O_sendPost (aid, sp, pid, pst, uid, vs) \<and> pst' = (if pid = PID then emptyPost else pst))"
  "g (Trans s a ou s') = (COMact (comSendCreateOFriend uID p aID uID'), O_sendCreateOFriend (aid, sp, uid, uid'))
\<longleftrightarrow> (\<exists>p'. a = (COMact (comSendCreateOFriend uID p' aID uID')) \<and> p = emptyPass \<and> ou = O_sendCreateOFriend (aid, sp, uid, uid'))"
  "g (Trans s a ou s') = (COMact (comReceiveCreateOFriend aID cp uID uID'), outOK)
\<longleftrightarrow> a = COMact (comReceiveCreateOFriend aID cp uID uID') \<and> ou = outOK"
  "g (Trans s a ou s') = (COMact (comSendDeleteOFriend uID p aID uID'), O_sendDeleteOFriend (aid, sp, uid, uid'))
\<longleftrightarrow> (\<exists>p'. a = COMact (comSendDeleteOFriend uID p' aID uID') \<and> p = emptyPass \<and> ou = O_sendDeleteOFriend (aid, sp, uid, uid'))"
  "g (Trans s a ou s') = (COMact (comReceiveDeleteOFriend aID cp uID uID'), outOK)
\<longleftrightarrow> a = COMact (comReceiveDeleteOFriend aID cp uID uID') \<and> ou = outOK"
by (cases a; auto simp: comPurge_simps)+

end

end
