(* The value setup for paper confidentiality *)
theory Post_Value_Setup_RECEIVER
  imports
    "../Safety_Properties"
    "Post_Observation_Setup_RECEIVER"
    "Post_Unwinding_Helper_RECEIVER"
begin

subsubsection \<open>Value setup\<close>

locale Post_RECEIVER = ObservationSetup_RECEIVER
begin

datatype "value" = PValR post \<comment> \<open>post content received from the issuer node\<close>


fun \<phi> :: "(state,act,out) trans \<Rightarrow> bool" where
"\<phi> (Trans _ (COMact (comReceivePost aid sp pid pst uid vs)) ou _) =
(aid = AID \<and> pid = PID \<and> ou = outOK)"
|
"\<phi> (Trans s _ _ s') = False"

lemma \<phi>_def2:
"\<phi> (Trans s a ou s') \<longleftrightarrow>
 (\<exists>uid p pst vs. a = COMact (comReceivePost AID p PID pst uid vs) \<and> ou = outOK)"
by (cases "Trans s a ou s'" rule: \<phi>.cases) auto

lemma comReceivePost_out:
assumes 1: "step s a = (ou,s')" and a: "a = COMact (comReceivePost AID p PID pst uid vs)" and 2: "ou = outOK"
shows "p = serverPass s AID"
using 1 2 unfolding a by (auto simp: com_defs)

lemma \<phi>_def3:
assumes "step s a = (ou,s')"
shows
"\<phi> (Trans s a ou s') \<longleftrightarrow>
 (\<exists>uid pst vs. a = COMact (comReceivePost AID (serverPass s AID) PID pst uid vs) \<and> ou = outOK)"
unfolding \<phi>_def2
using comReceivePost_out[OF assms]
by blast

lemma \<phi>_cases:
assumes "\<phi> (Trans s a ou s')"
and "step s a = (ou, s')"
and "reach s"
obtains
  (Recv) uid sp aID pID pst vs where "a = COMact (comReceivePost aID sp pID pst uid vs)" "ou = outOK"
                                 "sp = serverPass s AID"
                                  "aID = AID" "pID = PID"
proof -
  from assms(1) obtain sp pst uid vs where "a = COMact (comReceivePost AID sp PID pst uid vs) \<and> ou = outOK"
    unfolding \<phi>_def2 by auto
  then show thesis proof -
    assume "a = COMact (comReceivePost AID sp PID pst uid vs) \<and> ou = outOK"
    with assms(2) show thesis by (intro Recv) (auto simp: com_defs)
  qed
qed


fun f :: "(state,act,out) trans \<Rightarrow> value" where
"f (Trans s (COMact (comReceivePost aid sp pid pst uid vs)) _ s') =
 (if aid = AID \<and> pid = PID then PValR pst else undefined)"
|
"f (Trans s _ _ s') = undefined"


sublocale Receiver_State_Equivalence_Up_To_PID .

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
  unfolding \<phi>_def2
  by (auto simp: u_defs com_defs)
qed

lemma eqButPID_step_\<phi>:
assumes s's1': "eqButPID s s1"
and step: "step s a = (ou,s')" and step1: "step s1 a = (ou1,s1')"
shows "\<phi> (Trans s a ou s') = \<phi> (Trans s1 a ou1 s1')"
by (metis eqButPID_step_\<phi>_imp eqButPID_sym assms)


end

end
