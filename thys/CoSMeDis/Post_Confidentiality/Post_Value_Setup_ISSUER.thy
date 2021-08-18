(* The value setup for post confidentiality *)
theory Post_Value_Setup_ISSUER
  imports
    "../Safety_Properties"
    "Post_Observation_Setup_ISSUER"
    "Post_Unwinding_Helper_ISSUER"
begin

locale Post_ISSUER = ObservationSetup_ISSUER
begin

subsubsection \<open>Value setup\<close>


datatype "value" =
  isPVal: PVal post \<comment> \<open>updating the post content locally\<close>
| isPValS: PValS (PValS_tgtAPI: apiID) post \<comment> \<open>sending the post to another node\<close>

lemma filter_isPValS_Nil: "filter isPValS vl = [] \<longleftrightarrow> list_all isPVal vl"
proof(induct vl)
  case (Cons v vl)
  thus ?case by (cases v) auto
qed auto

fun \<phi> :: "(state,act,out) trans \<Rightarrow> bool" where
"\<phi> (Trans _ (Uact (uPost uid p pid pst)) ou _) = (pid = PID \<and> ou = outOK)"
|
"\<phi> (Trans _ (COMact (comSendPost uid p aid pid)) ou _) = (pid = PID \<and> ou \<noteq> outErr)"
(* Added during strengthening: saying \<noteq> outErr is simpler than actually describing the output, which essentially
   takes some parameters from the post and some values from the state. *)
|
"\<phi> (Trans s _ _ s') = False"

lemma \<phi>_def2:
shows
"\<phi> (Trans s a ou s') \<longleftrightarrow>
 (\<exists>uid p pst. a = Uact (uPost uid p PID pst) \<and> ou = outOK) \<or>
 (\<exists>uid p aid. a = COMact (comSendPost uid p aid PID) \<and> ou \<noteq> outErr)"
by (cases "Trans s a ou s'" rule: \<phi>.cases) auto

lemma uPost_out:
assumes 1: "step s a = (ou,s')" and a: "a = Uact (uPost uid p PID pst)" and 2: "ou = outOK"
shows "uid = owner s PID \<and> p = pass s uid"
using 1 2 unfolding a by (auto simp: u_defs)

lemma comSendPost_out:
assumes 1: "step s a = (ou,s')" and a: "a = COMact (comSendPost uid p aid PID)" and 2: "ou \<noteq> outErr"
shows "ou = O_sendPost (aid, clientPass s aid, PID, post s PID, owner s PID, vis s PID)
       \<and> uid = admin s \<and> p = pass s (admin s)"
using 1 2 unfolding a by (auto simp: com_defs)

lemma \<phi>_def3:
assumes "step s a = (ou,s')"
shows
"\<phi> (Trans s a ou s') \<longleftrightarrow>
 (\<exists>pst. a = Uact (uPost (owner s PID) (pass s (owner s PID)) PID pst) \<and> ou = outOK) \<or>
 (\<exists>aid. a = COMact (comSendPost (admin s) (pass s (admin s)) aid PID) \<and>
        ou = O_sendPost (aid, clientPass s aid, PID, post s PID, owner s PID, vis s PID))"
unfolding \<phi>_def2(* [OF assms] *)
using comSendPost_out[OF assms] uPost_out[OF assms]
by blast

lemma \<phi>_cases:
assumes "\<phi> (Trans s a ou s')"
and "step s a = (ou, s')"
and "reach s"
obtains
  (UpdateT) uid p pID pst where "a = Uact (uPost uid p PID pst)" "ou = outOK" "p = pass s uid"
                                  "uid = owner s PID"
| (Send) uid p aid where "a = COMact (comSendPost uid p aid PID)" "ou \<noteq> outErr" "p = pass s uid"
                                  "uid = admin s"
proof -
  from assms(1) obtain uid p pst aid where "(a = Uact (uPost uid p PID pst) \<and> ou = outOK) \<or>
                                          (a = COMact (comSendPost uid p aid PID) \<and> ou \<noteq> outErr)"
    unfolding \<phi>_def2(* [OF assms(2)] *) by auto
  then show thesis proof(elim disjE)
    assume "a = Uact (uPost uid p PID pst) \<and> ou = outOK"
    with assms(2) show thesis by (intro UpdateT) (auto simp: u_defs)
  next
    assume "a = COMact (comSendPost uid p aid PID) \<and> ou \<noteq> outErr"
    with assms(2) show thesis by (intro Send) (auto simp: com_defs)
  qed
qed


fun f :: "(state,act,out) trans \<Rightarrow> value" where
"f (Trans s (Uact (uPost uid p pid pst)) _ s') =
 (if pid = PID then PVal pst else undefined)"
|
"f (Trans s (COMact (comSendPost uid p aid pid)) (O_sendPost (_, _, _, pst, _, _)) s') =
 (if pid = PID then PValS aid pst else undefined)"
|
"f (Trans s _ _ s') = undefined"

sublocale Issuer_State_Equivalence_Up_To_PID .

lemma Uact_uPaperC_step_eqButPID:
assumes a: "a = Uact (uPost uid p PID pst)"
and "step s a = (ou,s')"
shows "eqButPID s s'"
using assms unfolding eqButPID_def eeqButPID_def eeqButPID_F_def
by (auto simp: u_defs split: if_splits)


lemma eqButPID_step_\<phi>_imp:
assumes ss1: "eqButPID s s1"
and step: "step s a = (ou,s')" and step1: "step s1 a = (ou1,s1')"
and \<phi>: "\<phi> (Trans s a ou s')"
shows "\<phi> (Trans s1 a ou1 s1')"
proof-
  have s's1': "eqButPID s' s1'"
  using eqButPID_step local.step ss1 step1 by blast
  show ?thesis using step step1 \<phi>
  using eqButPID_stateSelectors[OF ss1]
  unfolding \<phi>_def2(* [OF step] \<phi>_def2[OF step1]  *)
  by (auto simp: u_defs com_defs)
qed

lemma eqButPID_step_\<phi>:
assumes s's1': "eqButPID s s1"
and step: "step s a = (ou,s')" and step1: "step s1 a = (ou1,s1')"
shows "\<phi> (Trans s a ou s') = \<phi> (Trans s1 a ou1 s1')"
by (metis eqButPID_step_\<phi>_imp eqButPID_sym assms)


end

end
