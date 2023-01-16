(* The value setup for post confidentiality *)
theory DYNAMIC_Post_Value_Setup_ISSUER
  imports
    "../Safety_Properties"
    "Post_Observation_Setup_ISSUER"
    "Post_Unwinding_Helper_ISSUER"
begin

subsection \<open>Variation with dynamic declassification trigger\<close>

text \<open>This section formalizes the ``dynamic'' variation of one
post confidentiality properties, as described in \<^cite>\<open>\<open>Appendix C\<close> in "cosmedis-SandP2017"\<close>.
\<close>

locale Post = ObservationSetup_ISSUER
begin

subsubsection\<open>Issuer value setup\<close>

datatype "value" =
  isPVal: PVal post \<comment> \<open>updating the post content locally\<close>
| isPValS: PValS (tgtAPI: apiID) post \<comment> \<open>sending the post to another node\<close>
| isOVal: OVal bool \<comment> \<open>change in the dynamic declassification trigger condition\<close>

text \<open>The dynamic declassification trigger condition holds, i.e.~the access window to the
confidential information is open, when the post is public or one of the observers is the
administrator, the post's owner, or a friend of the post's owner.\<close>

definition "open" where
"open s \<equiv>
 \<exists> uid \<in> UIDs.
   uid \<in>\<in> userIDs s \<and> PID \<in>\<in> postIDs s \<and>
   (uid = admin s \<or> uid = owner s PID \<or> uid \<in>\<in> friendIDs s (owner s PID) \<or>
    vis s PID = PublicV)"

sublocale Issuer_State_Equivalence_Up_To_PID .

lemma eqButPID_open:
assumes "eqButPID s s1"
shows "open s \<longleftrightarrow> open s1"
using eqButPID_stateSelectors[OF assms] (* eqButPID_postSelectors[OF assms] *)
unfolding open_def by auto

lemma not_open_eqButPID:
assumes 1: "\<not> open s" and 2: "eqButPID s s1"
shows "\<not> open s1"
using 1 unfolding eqButPID_open[OF 2] .

lemma step_isCOMact_open:
assumes "step s a = (ou, s')"
and "isCOMact a"
shows "open s' = open s"
using assms proof (cases a)
  case (COMact ca) then show ?thesis using assms by (cases ca) (auto simp: open_def com_defs)
qed auto

lemma validTrans_isCOMact_open:
assumes "validTrans trn"
and "isCOMact (actOf trn)"
shows "open (tgtOf trn) = open (srcOf trn)"
using assms step_isCOMact_open by (cases trn) auto



lemma list_all_isOVal_filter_isPValS:
"list_all isOVal vl \<Longrightarrow> filter (Not o isPValS) vl = vl"
by (induct vl) auto

lemma list_all_Not_isOVal_OVal_True:
assumes "list_all (Not \<circ> isOVal) ul"
and "ul @ vll = OVal True # vll'"
shows "ul = []"
using assms by (cases ul) auto

lemma list_all_filter_isOVal_isPVal_isPValS:
assumes "list_all (Not \<circ> isOVal) ul"
and "filter isPValS ul = []" and "filter isPVal ul = []"
shows "ul = []"
using assms value.exhaust_disc by (induct ul) auto

lemma filter_list_all_isPValS_isOVal:
assumes "list_all (Not \<circ> isOVal) ul" and "filter isPVal ul = []"
shows "list_all isPValS ul"
using assms value.exhaust_disc by (induct ul) auto

lemma filter_list_all_isPVal_isOVal:
assumes "list_all (Not \<circ> isOVal) ul" and "filter isPValS ul = []"
shows "list_all isPVal ul"
using assms value.exhaust_disc by (induct ul) auto

lemma list_all_isPValS_Not_isOVal_filter:
assumes "list_all isPValS ul" shows "list_all (Not \<circ> isOVal) ul \<and> filter isPVal ul = []"
using assms value.exhaust_disc by (induct ul) auto

lemma filter_isTValS_Nil:
"filter isPValS vl = [] \<longleftrightarrow>
 list_all (\<lambda> v. isPVal v \<or> isOVal v) vl"
proof(induct vl)
  case (Cons v vl)
  thus ?case by (cases v) auto
qed auto

(*   ******  *)
fun \<phi> :: "(state,act,out) trans \<Rightarrow> bool" where
"\<phi> (Trans _ (Uact (uPost uid p pid pst)) ou _) = (pid = PID \<and> ou = outOK)"
|
"\<phi> (Trans _ (COMact (comSendPost uid p aid pid)) ou _) = (pid = PID \<and> ou \<noteq> outErr)"
(* Added during strengthening: saying \<noteq> outErr is simpler than actually describing the output, which essentially
   takes some parameters from the post and some values from the state. *)
|
"\<phi> (Trans s _ _ s') = (open s \<noteq> open s')"

lemma \<phi>_def2:
assumes "step s a = (ou,s')"
shows
"\<phi> (Trans s a ou s') \<longleftrightarrow>
 (\<exists>uid p pst. a = Uact (uPost uid p PID pst) \<and> ou = outOK) \<or>
 (\<exists>uid p aid. a = COMact (comSendPost uid p aid PID) \<and> ou \<noteq> outErr) \<or>
  open s \<noteq> open s'"
using assms by (cases "Trans s a ou s'" rule: \<phi>.cases) (auto simp: all_defs open_def)

lemma uTextPost_out:
assumes 1: "step s a = (ou,s')" and a: "a = Uact (uPost uid p PID pst)" and 2: "ou = outOK"
shows "uid = owner s PID \<and> p = pass s uid"
using 1 2 unfolding a by (auto simp: u_defs)

lemma comSendPost_out:
assumes 1: "step s a = (ou,s')" and a: "a = COMact (comSendPost uid p aid PID)"
  and 2: "ou \<noteq> outErr"
shows "ou = O_sendPost (aid, clientPass s aid, PID, post s PID, owner s PID, vis s PID)
       \<and> uid = admin s \<and> p = pass s (admin s)"
using 1 2 unfolding a by (auto simp: com_defs)

lemma step_open_isCOMact:
assumes "step s a = (ou,s')"
and "open s \<noteq> open s'"
shows "\<not> isCOMact a \<and> \<not> (\<exists> ua. isuPost ua \<and> a = Uact ua)"
  using assms unfolding open_def
  apply(cases a)
  subgoal by (auto simp: all_defs)
  subgoal by (auto simp: all_defs)
  subgoal by (auto simp: all_defs)
  subgoal for x4 by (cases x4) (auto simp: all_defs)
  subgoal by (auto simp: all_defs)
  subgoal by (auto simp: all_defs)
  subgoal for x7 by (cases x7) (auto simp: all_defs)
  done

lemma \<phi>_def3:
assumes "step s a = (ou,s')"
shows
"\<phi> (Trans s a ou s') \<longleftrightarrow>
 (\<exists>pst. a = Uact (uPost (owner s PID) (pass s (owner s PID)) PID pst) \<and> ou = outOK)
 \<or>
 (\<exists>aid. a = COMact (comSendPost (admin s) (pass s (admin s)) aid PID) \<and>
        ou = O_sendPost (aid, clientPass s aid, PID, post s PID, owner s PID, vis s PID))
 \<or>
 open s \<noteq> open s' \<and> \<not> isCOMact a \<and> \<not> (\<exists> ua. isuPost ua \<and> a = Uact ua)"
unfolding \<phi>_def2[OF assms]
using comSendPost_out[OF assms] uTextPost_out[OF assms]
step_open_isCOMact[OF assms]
by blast

fun f :: "(state,act,out) trans \<Rightarrow> value" where
"f (Trans s (Uact (uPost uid p pid pst)) _ s') =
 (if pid = PID then PVal pst else OVal (open s'))"  (* else undefined  *)
|
"f (Trans s (COMact (comSendPost uid p aid pid)) (O_sendPost (_, _, _, pst, _)) s') =
 (if pid = PID then PValS aid pst else OVal (open s'))" (* else undefined  *)
|
"f (Trans s _ _ s') = OVal (open s')"

lemma f_open_OVal:
assumes "step s a = (ou,s')"
and "open s \<noteq> open s' \<and> \<not> isCOMact a \<and> \<not> (\<exists> ua. isuPost ua \<and> a = Uact ua)"
shows "f (Trans s a ou s') = OVal (open s')"
using assms by (cases "Trans s a ou s'" rule: f.cases) auto

lemma f_eq_PVal:
assumes "step s a = (ou,s')" and "\<phi> (Trans s a ou s')"
and "f (Trans s a ou s') = PVal pst"
shows "a = Uact (uPost (owner s PID) (pass s (owner s PID)) PID pst)"
using assms by (cases "Trans s a ou s'" rule: f.cases) (auto simp: u_defs com_defs)

lemma f_eq_PValS:
assumes "step s a = (ou,s')" and "\<phi> (Trans s a ou s')"
and "f (Trans s a ou s') = PValS aid pst"
shows "a = COMact (comSendPost (admin s) (pass s (admin s)) aid PID)"
using assms by (cases "Trans s a ou s'" rule: f.cases) (auto simp: com_defs)

lemma f_eq_OVal:
assumes "step s a = (ou,s')" and "\<phi> (Trans s a ou s')"
and "f (Trans s a ou s') = OVal b"
shows "open s' \<noteq> open s"
using assms by (auto simp: \<phi>_def2 com_defs)

lemma uPost_comSendPost_open_eq:
assumes step: "step s a = (ou, s')"
and a: "a = Uact (uPost uid p pid pst) \<or> a = COMact (comSendPost uid p aid pid)"
shows "open s' = open s"
using assms a unfolding open_def
by (cases a) (auto simp: u_defs com_defs)

lemma step_open_\<phi>_f_PVal_\<gamma>:
assumes s: "reach s"
and step: "step s a = (ou, s')"
and PID: "PID \<in> set (postIDs s)"
and op: "\<not> open s" and fi: "\<phi> (Trans s a ou s')" and f: "f (Trans s a ou s') = PVal pst"
shows "\<not> \<gamma> (Trans s a ou s')"
proof-
  have a: "a = Uact (uPost (owner s PID) (pass s (owner s PID)) PID pst)"
  using f_eq_PVal[OF step fi f] .
  have ou: "ou = outOK" using fi op unfolding a \<phi>_def2[OF step] by auto
  have "owner s PID \<in>\<in> userIDs s" using s by (simp add: PID reach_owner_userIDs)
  hence "owner s PID \<notin> UIDs" using op PID unfolding open_def by auto
  thus ?thesis unfolding a by simp
qed

lemma Uact_uPaperC_step_eqButPID:
assumes a: "a = Uact (uPost uid p PID pst)"
and "step s a = (ou,s')"
shows "eqButPID s s'"
using assms unfolding eqButPID_def eeqButPID_def eeqButPID_F_def
by (auto simp: all_defs split: if_splits)

lemma eqButPID_step_\<phi>_imp:
assumes ss1: "eqButPID s s1"
and step: "step s a = (ou,s')" and step1: "step s1 a = (ou1,s1')"
and \<phi>: "\<phi> (Trans s a ou s')"
shows "\<phi> (Trans s1 a ou1 s1')"
proof-
  have s's1': "eqButPID s' s1'"
  using eqButPID_step local.step ss1 step1 by blast
  show ?thesis using step step1 \<phi> eqButPID_open[OF ss1] eqButPID_open[OF s's1']
  using eqButPID_stateSelectors[OF ss1]
  unfolding \<phi>_def2[OF step] \<phi>_def2[OF step1]
  by (auto simp: all_defs)
qed

lemma eqButPID_step_\<phi>:
assumes s's1': "eqButPID s s1"
and step: "step s a = (ou,s')" and step1: "step s1 a = (ou1,s1')"
shows "\<phi> (Trans s a ou s') = \<phi> (Trans s1 a ou1 s1')"
by (metis eqButPID_step_\<phi>_imp eqButPID_sym assms)


end



end
