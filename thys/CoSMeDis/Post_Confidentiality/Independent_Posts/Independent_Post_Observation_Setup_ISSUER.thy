(* Strengthened observation setup, customized for post confidentiality *)
theory Independent_Post_Observation_Setup_ISSUER
  imports
    "../../Safety_Properties"
    "../Post_Observation_Setup_ISSUER"
begin

subsection \<open>Variation with multiple independent secret posts\<close>

text \<open>This section formalizes the lifting of the confidentiality of one
given (arbitrary but fixed) post to the confidentiality of two posts of
arbitrary nodes of the network, as described in \<^cite>\<open>\<open>Appendix E\<close> in "cosmedis-SandP2017"\<close>.
\<close>

subsubsection\<open>Issuer observation setup\<close>

locale Strong_ObservationSetup_ISSUER = Fixed_UIDs + Fixed_PID
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
      posts \<^emph>\<open>other than \<open>PID\<close>\<close> are completely independent of \<open>PID\<close>;  the confidentiality of \<open>PID\<close>
      is protected even if the observers can see all updates to other posts (and actions
      contributing to the declassification triggers of those posts).\<close>
   (\<exists>uid p pid pst. a = Uact (uPost uid p pid pst) \<and> pid \<noteq> PID)
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

(* Purging communicating actions: user-password information is removed.
  Note: comReceivePost is not affected by the purging, in that post text
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

(* Purging outputs: post text information for PID
  is removed from the only kind of output that may contain such info: outAIDPPIDNUID.
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
by (cases ou; auto simp: Strong_ObservationSetup_ISSUER.outPurge.simps)+


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
