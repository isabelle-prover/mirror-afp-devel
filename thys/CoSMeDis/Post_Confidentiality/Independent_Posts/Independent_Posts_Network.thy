theory Independent_Posts_Network
  imports
    "Independent_DYNAMIC_Post_Network"
    "BD_Security_Compositional.Independent_Secrets"
begin

subsubsection \<open>Composition of confidentiality guarantees for different posts\<close>

text \<open>We combine \<^emph>\<open>two\<close> confidentiality guarantees for two different posts in arbitrary nodes of
the network.

For this purpose, we have strengthened the observation power of the security property for
individual posts to make all transitions that update \<^emph>\<open>other\<close> posts observable, as well as all
transitions that contribute to the state of the trigger (see the observation setup
theories).  This guarantees that the confidentiality of one post is independent of actions
affecting other posts, which will allow us to combine security guarantees for different posts.

We now prove a few helper lemmas establishing that now the observable transitions indeed
fully determine the state of the trigger.\<close>

fun obsEffect :: "state \<Rightarrow> obs \<Rightarrow> state" where
  "obsEffect s (Uact (uPost uid p pid pst), ou) = updatePost s uid p pid pst"
| "obsEffect s (Uact (uVisPost uid p pid v), ou) = updateVisPost s uid p pid v"
| "obsEffect s (Sact (sSys uid p), ou) = startSys s uid p"
| "obsEffect s (Cact (cUser uid p uid' p'), ou) = createUser s uid p uid' p'"
| "obsEffect s (Cact (cPost uid p pid), ou) = createPost s uid p pid"
| "obsEffect s (Cact (cFriend uid p uid'), ou) = createFriend s uid p uid'"
| "obsEffect s (Dact (dFriend uid p uid'), ou) = deleteFriend s uid p uid'"
| "obsEffect s (COMact (comSendPost uid p aid pid), ou) = snd (sendPost s uid p aid pid)"
| "obsEffect s (COMact (comReceivePost aid p pid pst uid v), ou) = receivePost s aid p pid pst uid v"
| "obsEffect s (COMact (comReceiveCreateOFriend aid p uid uid'), ou) = receiveCreateOFriend s aid p uid uid'"
| "obsEffect s (COMact (comReceiveDeleteOFriend aid p uid uid'), ou) = receiveDeleteOFriend s aid p uid uid'"
| "obsEffect s _ = s"

fun obsStep :: "state \<Rightarrow> obs \<Rightarrow> state" where
  "obsStep s (a,ou) = (if ou \<noteq> outErr then obsEffect s (a,ou) else s)"

fun obsSteps :: "state \<Rightarrow> obs list \<Rightarrow> state" where
  "obsSteps s obsl = foldl obsStep s obsl"

definition triggerEq :: "state \<Rightarrow> state \<Rightarrow> bool" where
  "triggerEq s s' \<longleftrightarrow> userIDs s = userIDs s' \<and> postIDs s = postIDs s' \<and> admin s = admin s' \<and>
                      owner s = owner s' \<and> friendIDs s = friendIDs s' \<and> vis s = vis s' \<and>
                      outerPostIDs s = outerPostIDs s' \<and> outerOwner s = outerOwner s' \<and>
                      recvOuterFriendIDs s = recvOuterFriendIDs s' \<and> outerVis s = outerVis s'"

lemma triggerEq_refl[simp]: "triggerEq s s"
and triggerEq_sym: "triggerEq s s' \<Longrightarrow> triggerEq s' s"
and triggerEq_trans: "triggerEq s s' \<Longrightarrow> triggerEq s' s'' \<Longrightarrow> triggerEq s s''"
unfolding triggerEq_def by auto

no_notation relcomp (infixr "O" 75)

context Post
begin

lemma [simp]: "outOK = outPurge ou \<longleftrightarrow> ou = outOK" by (cases ou) auto
lemma [simp]: "sPurge sa = sSys (sUserOfA sa) emptyPass" by (cases sa) auto
lemma sStep_unfold: "sStep s sa = (if userIDs s = []
                                   then (case sa of sSys uid p \<Rightarrow> (outOK, startSys s uid p))
                                   else (outErr, s))"
by (cases sa) (auto simp: s_defs)

lemma triggerEq_open:
assumes "triggerEq s s'"
shows "open s \<longleftrightarrow> open s'"
using assms unfolding triggerEq_def open_def by auto

lemma triggerEq_not_\<gamma>:
assumes "validTrans (Trans s a ou s')" and "\<not>\<gamma> (Trans s a ou s')"
shows "triggerEq s s'"
proof (cases a)
  case (Sact sa) then show ?thesis using assms by (cases sa) (auto simp: triggerEq_def s_defs) next
  case (Cact ca) then show ?thesis using assms by (cases ca) (auto simp: triggerEq_def c_defs) next
  case (Dact da) then show ?thesis using assms by (cases da) (auto simp: triggerEq_def d_defs) next
  case (Uact ua) then show ?thesis using assms by (cases ua) (auto simp: triggerEq_def u_defs) next
  case (Ract ra) then show ?thesis using assms by (auto simp: triggerEq_def) next
  case (Lact ra) then show ?thesis using assms by (auto simp: triggerEq_def) next
  case (COMact ca) then show ?thesis using assms by (cases ca) (auto simp: triggerEq_def com_defs)
qed

lemma triggerEq_obsStep:
assumes "validTrans (Trans s a ou s')" and "\<gamma> (Trans s a ou s')" and "triggerEq s s1"
shows "triggerEq s' (obsStep s1 (g (Trans s a ou s')))"
proof (cases a)
  case (Sact sa) then show ?thesis using assms by (cases sa) (auto simp: triggerEq_def s_defs) next
  case (Cact ca) then show ?thesis using assms by (cases ca) (auto simp: triggerEq_def c_defs) next
  case (Dact da) then show ?thesis using assms by (cases da) (auto simp: triggerEq_def d_defs) next
  case (Uact ua) then show ?thesis using assms by (cases ua) (auto simp: triggerEq_def u_defs) next
  case (Ract ra) then show ?thesis using assms by (auto simp: triggerEq_def) next
  case (Lact ra) then show ?thesis using assms by (auto simp: triggerEq_def) next
  case (COMact ca) then show ?thesis using assms by (cases ca) (auto simp: triggerEq_def com_defs)
qed

lemma triggerEq_obsSteps:
assumes "validFrom s tr" and "triggerEq s s'"
shows "triggerEq (tgtOfTrFrom s tr) (obsSteps s' (O tr))"
using assms proof (induction tr arbitrary: s s')
  case (Nil s s')
  then show ?case by auto
next
  case (Cons trn tr s s')
  then obtain a ou s'' where trn: "trn = Trans s a ou s''" and step: "step s a = (ou, s'')"
    by (cases trn) (auto simp: validFrom_Cons)
  show ?case proof cases
    assume \<gamma>: "\<gamma> trn"
    then have "triggerEq s'' (obsStep s' (g trn))" unfolding trn using step Cons(3) by (auto intro: triggerEq_obsStep)
    with Cons.IH[OF _ this] Cons(2) \<gamma> trn show ?thesis by (auto simp: validFrom_Cons)
  next
    assume n\<gamma>: "\<not> \<gamma> trn"
    then have "triggerEq s s''" using Cons(2) unfolding trn by (intro triggerEq_not_\<gamma>) (auto simp: validFrom_Cons)
    with Cons(3) have "triggerEq s'' s'" by (auto intro: triggerEq_sym triggerEq_trans)
    with Cons.IH[OF _ this] Cons(2) n\<gamma> trn show ?thesis by (auto simp: validFrom_Cons)
  qed
qed

end

context Post_RECEIVER
begin

lemma sPurge_simp[simp]: "sPurge sa = sSys (sUserOfA sa) emptyPass" by (cases sa) auto

definition "T_state s' \<equiv>
(\<exists> uid \<in> UIDs.
   uid \<in>\<in> userIDs s' \<and> PID \<in>\<in> outerPostIDs s' AID \<and>
   (uid = admin s' \<or>
    (AID,outerOwner s' AID PID) \<in>\<in> recvOuterFriendIDs s' uid \<or>
    outerVis s' AID PID = PublicV))"

lemma T_T_state: "T trn \<longleftrightarrow> T_state (tgtOf trn)"
by (cases trn) (auto simp: T_state_def)

lemma triggerEq_T:
assumes "triggerEq s s'"
shows "T_state s \<longleftrightarrow> T_state s'"
using assms unfolding triggerEq_def T_state_def by auto

lemma never_T_not_T_state:
assumes "validFrom s tr" and "never T tr" and "\<not>T_state s"
shows "\<not>T_state (tgtOfTrFrom s tr)"
using assms by (induction tr arbitrary: s rule: rev_induct) (auto simp: T_T_state)

lemma triggerEq_not_\<gamma>:
assumes "validTrans (Trans s a ou s')" and "\<not>\<gamma> (Trans s a ou s')"
shows "triggerEq s s'"
proof (cases a)
  case (Sact sa) then show ?thesis using assms by (cases sa) (auto simp: triggerEq_def s_defs) next
  case (Cact ca) then show ?thesis using assms by (cases ca) (auto simp: triggerEq_def c_defs) next
  case (Dact da) then show ?thesis using assms by (cases da) (auto simp: triggerEq_def d_defs) next
  case (Uact ua) then show ?thesis using assms by (cases ua) (auto simp: triggerEq_def u_defs) next
  case (Ract ra) then show ?thesis using assms by (auto simp: triggerEq_def) next
  case (Lact ra) then show ?thesis using assms by (auto simp: triggerEq_def) next
  case (COMact ca) then show ?thesis using assms by (cases ca) (auto simp: triggerEq_def com_defs)
qed

lemma triggerEq_obsStep:
assumes "validTrans (Trans s a ou s')" and "\<gamma> (Trans s a ou s')" and "triggerEq s s1"
shows "triggerEq s' (obsStep s1 (g (Trans s a ou s')))"
proof (cases a)
  case (Sact sa) then show ?thesis using assms by (cases sa) (auto simp: triggerEq_def s_defs) next
  case (Cact ca) then show ?thesis using assms by (cases ca) (auto simp: triggerEq_def c_defs) next
  case (Dact da) then show ?thesis using assms by (cases da) (auto simp: triggerEq_def d_defs) next
  case (Uact ua) then show ?thesis using assms by (cases ua) (auto simp: triggerEq_def u_defs) next
  case (Ract ra) then show ?thesis using assms by (auto simp: triggerEq_def) next
  case (Lact ra) then show ?thesis using assms by (auto simp: triggerEq_def) next
  case (COMact ca) then show ?thesis using assms by (cases ca) (auto simp: triggerEq_def com_defs)
qed


lemma triggerEq_obsSteps:
assumes "validFrom s tr" and "triggerEq s s'"
shows "triggerEq (tgtOfTrFrom s tr) (obsSteps s' (O tr))"
using assms proof (induction tr arbitrary: s s')
  case (Nil s s')
  then show ?case by auto
next
  case (Cons trn tr s s')
  then obtain a ou s'' where trn: "trn = Trans s a ou s''" and step: "step s a = (ou, s'')"
    by (cases trn) (auto simp: validFrom_Cons)
  show ?case proof cases
    assume \<gamma>: "\<gamma> trn"
    then have "triggerEq s'' (obsStep s' (g trn))" unfolding trn using step Cons(3) by (auto intro: triggerEq_obsStep)
    with Cons.IH[OF _ this] Cons(2) \<gamma> trn show ?thesis by (auto simp: validFrom_Cons)
  next
    assume n\<gamma>: "\<not> \<gamma> trn"
    then have "triggerEq s s''" using Cons(2) unfolding trn by (intro triggerEq_not_\<gamma>) (auto simp: validFrom_Cons)
    with Cons(3) have "triggerEq s'' s'" by (auto intro: triggerEq_sym triggerEq_trans)
    with Cons.IH[OF _ this] Cons(2) n\<gamma> trn show ?thesis by (auto simp: validFrom_Cons)
  qed
qed

end

context Post_Network
begin

fun nObsStep :: "(apiID \<Rightarrow> state) \<Rightarrow> (apiID, act \<times> out) nobs \<Rightarrow> (apiID \<Rightarrow> state)" where
  "nObsStep s (LObs aid obs) = s(aid := obsStep (s aid) obs)"
| "nObsStep s (CObs aid1 obs1 aid2 obs2) = s(aid1 := obsStep (s aid1) obs1, aid2 := obsStep (s aid2) obs2)"

fun nObsSteps :: "(apiID \<Rightarrow> state) \<Rightarrow> (apiID, act \<times> out) nobs list \<Rightarrow> (apiID \<Rightarrow> state)" where
  "nObsSteps s obsl = foldl nObsStep s obsl"

definition nTriggerEq :: "(apiID \<Rightarrow> state) \<Rightarrow> (apiID \<Rightarrow> state) \<Rightarrow> bool" where
  "nTriggerEq s s' \<longleftrightarrow> (\<forall>aid. triggerEq (s aid) (s' aid))"

lemma nTriggerEq_refl[simp]: "nTriggerEq s s"
and nTriggerEq_sym: "nTriggerEq s s' \<Longrightarrow> nTriggerEq s' s"
and nTriggerEq_trans: "nTriggerEq s s' \<Longrightarrow> nTriggerEq s' s'' \<Longrightarrow> nTriggerEq s s''"
unfolding nTriggerEq_def by (auto intro: triggerEq_sym triggerEq_trans)

lemma nTriggerEq_open:
assumes "nTriggerEq s s'"
shows "\<forall>aid. Iss.open (s aid) \<longleftrightarrow> Iss.open (s' aid)"
using assms unfolding nTriggerEq_def by (auto intro!: Iss.triggerEq_open)

lemma nTriggerEq_not_\<gamma>:
assumes "nValidTrans trn" and "\<not>Net.n\<gamma> trn"
shows "nTriggerEq (nSrcOf trn) (nTgtOf trn)"
proof (cases trn)
  case (LTrans s aid1 trn1)
  with assms show ?thesis using Iss.triggerEq_not_\<gamma> Post_RECEIVER.triggerEq_not_\<gamma>
    by (cases trn1) (auto simp: nTriggerEq_def)
next
  case (CTrans s aid1 trn1 aid2 trn2)
  with assms show ?thesis
    by (auto elim: sync_cases simp: Strong_ObservationSetup_RECEIVER.\<gamma>.simps Strong_ObservationSetup_ISSUER.\<gamma>.simps)
qed

lemma nTriggerEq_obsStep:
assumes "nValidTrans trn" and "Net.n\<gamma> trn" and "nTriggerEq (nSrcOf trn) s1"
shows "nTriggerEq (nTgtOf trn) (nObsStep s1 (Net.ng trn))"
unfolding nTriggerEq_def proof
  fix aid
  show "triggerEq (nTgtOf trn aid) (nObsStep s1 (Net.ng trn) aid)"
  proof (cases trn)
    case (LTrans s aid1 trn1)
    with assms show ?thesis unfolding nTriggerEq_def
      by (cases trn1) (auto intro: Iss.triggerEq_obsStep Post_RECEIVER.triggerEq_obsStep)
  next
    case (CTrans s aid1 trn1 aid2 trn2)
    then have "sync aid1 trn1 aid2 trn2" using assms by auto
    moreover obtain a1 ou1 s1' a2 ou2 s2'
    where "trn1 = Trans (s aid1) a1 ou1 s1'" and "trn2 = Trans (s aid2) a2 ou2 s2'"
      using CTrans assms by (cases trn1, cases trn2) auto
    ultimately show ?thesis using CTrans assms unfolding nTriggerEq_def
      using Iss.triggerEq_obsStep[of "s aid1" a1 ou1 s1' "s1 aid1"]
      using Iss.triggerEq_obsStep[of "s aid2" a2 ou2 s2' "s1 aid2"]
      using Post_RECEIVER.triggerEq_obsStep[of "s aid1" a1 ou1 s1' "UIDs aid1" "s1 aid1"]
      using Post_RECEIVER.triggerEq_obsStep[of "s aid2" a2 ou2 s2' "UIDs aid2" "s1 aid2"]
      by (elim sync_cases) (auto simp: Strong_ObservationSetup_RECEIVER.\<gamma>.simps)
  qed
qed

lemma triggerEq_obsSteps:
assumes "validFrom s tr" and "nTriggerEq s s'"
shows "nTriggerEq (nTgtOfTrFrom s tr) (nObsSteps s' (O tr))"
using assms proof (induction tr arbitrary: s s')
  case (Nil s s')
  then show ?case by auto
next
  case (Cons trn tr s s')
  have tr: "local.validFrom (nTgtOf trn) tr" "nTgtOfTrFrom s (trn # tr) = nTgtOfTrFrom (nTgtOf trn) tr"
    using Cons(2) by auto
  show ?case proof cases
    assume \<gamma>: "Net.n\<gamma> trn"
    then have O: "nObsSteps s' (O (trn # tr)) = nObsSteps (nObsStep s' (Net.ng trn)) (O tr)" by auto
    have "nTriggerEq (nTgtOf trn) (nObsStep s' (Net.ng trn))" using Cons(2,3) \<gamma>
      by (intro nTriggerEq_obsStep) auto
    from Cons.IH[OF tr(1) this] show ?thesis unfolding O tr(2) .
  next
    assume n\<gamma>: "\<not> Net.n\<gamma> trn"
    then have O: "O (trn # tr) = O tr" by auto
    have "nTriggerEq (nSrcOf trn) (nTgtOf trn)" using n\<gamma> Cons(2) by (intro nTriggerEq_not_\<gamma>) auto
    with Cons(3) have "nTriggerEq (nTgtOf trn) s'" using Cons(2) by (auto intro: nTriggerEq_sym nTriggerEq_trans)
    from Cons.IH[OF tr(1) this] show ?thesis unfolding O tr(2) .
  qed
qed

lemma O_eq_nTriggerEq:
assumes O: "O tr = O tr'" and tr: "validFrom s (tr ## trn)" and tr': "validFrom s' (tr' ## trn')"
and \<gamma>: "Net.n\<gamma> trn" and \<gamma>': "Net.n\<gamma> trn'" and g: "Net.ng trn = Net.ng trn'"
and s_s': "nTriggerEq s s'"
shows "nTriggerEq (nSrcOf trn) (nSrcOf trn')" and "nTriggerEq (nTgtOf trn) (nTgtOf trn')"
proof -
  have *: "nTriggerEq (nTgtOfTrFrom s tr) (nObsSteps s' (O tr))" using tr s_s'
    by (intro triggerEq_obsSteps) auto
  have **: "nTriggerEq (nTgtOfTrFrom s' tr') (nObsSteps s' (O tr'))" using tr'
    by (intro triggerEq_obsSteps) auto
  from nTriggerEq_trans[OF *[unfolded O] **[THEN nTriggerEq_sym]]
  show src: "nTriggerEq (nSrcOf trn) (nSrcOf trn')" using tr tr'
    by (auto simp: nTgtOfTrFrom_nTgtOf_last)
  have "nTriggerEq (nTgtOf trn) (nObsStep (nSrcOf trn') (Net.ng trn))" using tr \<gamma> src
    by (intro nTriggerEq_obsStep) auto
  moreover have "nTriggerEq (nTgtOf trn') (nObsStep (nSrcOf trn') (Net.ng trn'))" using tr' \<gamma>'
    by (intro nTriggerEq_obsStep) auto
  ultimately show "nTriggerEq (nTgtOf trn) (nTgtOf trn')" unfolding g
    by (auto intro: nTriggerEq_sym nTriggerEq_trans)
qed

end


text \<open>We are now ready to combine two confidentiality properties for different posts in different
nodes.\<close>

locale Posts_Network =
  Post1: Post_Network AIDs UIDs AID1 PID1
+ Post2: Post_Network AIDs UIDs AID2 PID2
for AIDs :: "apiID set"
and UIDs :: "apiID \<Rightarrow> userID set"
and AID1 :: "apiID" and AID2 :: "apiID"
and PID1 :: "postID" and PID2 :: "postID"
+
assumes AID1_neq_AID2: "AID1 \<noteq> AID2"
begin

text \<open>The combined observations consist of the local actions of observing users and their outputs,
as usual. We do not consider communication actions here for simplicity, because this would require
us to combine the \<^emph>\<open>purgings\<close> of observations of the two properties. This is straightforward, but
tedious.\<close>

fun n\<gamma> :: "(apiID, state, (state, act, out) trans) ntrans \<Rightarrow> bool" where
  "n\<gamma> (LTrans s aid (Trans _ a _ _)) = (\<exists> uid. userOfA a = Some uid \<and> uid \<in> UIDs aid \<and> (\<not>isCOMact a))"
| "n\<gamma> (CTrans s aid1 trn1 aid2 trn2) = False"

fun g :: "(state,act,out) trans \<Rightarrow> obs" where
  "g (Trans _ (Sact sa) ou _) = (Sact (Post1.Iss.sPurge sa), ou)"
| "g (Trans _ a ou _) = (a,ou)"

fun ng :: "(apiID, state, (state, act, out) trans) ntrans \<Rightarrow> (apiID, act \<times> out) nobs" where
  "ng (LTrans s aid trn) = LObs aid (g trn)"
| "ng (CTrans s aid1 trn1 aid2 trn2) = undefined"

abbreviation "validSystemTrace \<equiv> Post1.validFrom (\<lambda>_. istate)"

text \<open>We now instantiate the generic technique for combining security properties with
independent secret sources.\<close>

sublocale BD_Security_TS_Two_Secrets "\<lambda>_. istate" Post1.nValidTrans Post1.nSrcOf Post1.nTgtOf
  Post1.Net.n\<phi> Post1.nf' Post1.Net.n\<gamma> Post1.Net.ng Post1.Net.nT "Post1.B AID1"
  Post2.Net.n\<phi> Post2.nf' Post2.Net.n\<gamma> Post2.Net.ng Post2.Net.nT "Post2.B AID2"
  n\<gamma> ng
proof
  fix tr trn
  assume "n\<gamma> trn"
  then show "Post1.Net.n\<gamma> trn \<and> Post2.Net.n\<gamma> trn"
    by (cases trn rule: n\<gamma>.cases) (auto simp: Strong_ObservationSetup_RECEIVER.\<gamma>.simps)
next
  fix tr tr' trn trn'
  assume tr: "validSystemTrace (tr ## trn)" and tr': "validSystemTrace (tr' ## trn')"
     and \<gamma>: "Post1.Net.n\<gamma> trn" and \<gamma>': "Post1.Net.n\<gamma> trn'" and g: "Post1.Net.ng trn = Post1.Net.ng trn'"
  from tr tr' have trn: "Post1.nValidTrans trn" "Post1.nValidTrans trn'" by auto
  show "n\<gamma> trn = n\<gamma> trn'" proof (cases trn)
    case (LTrans s aid1 trn1)
    then obtain s' trn1' where trn': "trn' = LTrans s' aid1 trn1'" using g by (cases trn') auto
    then show ?thesis using LTrans g
      by (cases trn1 rule: Strong_ObservationSetup_ISSUER.g.cases;
          cases trn1' rule: Strong_ObservationSetup_ISSUER.g.cases)
         (auto simp: Strong_ObservationSetup_RECEIVER.g.simps Post_RECEIVER.sPurge_simp)
  next
    case (CTrans s aid1 trn1 aid2 trn2)
    then show ?thesis using g by (cases trn') auto
  qed
next
  fix tr tr' trn trn'
  assume O: "Post1.O tr = Post1.O tr'" and \<gamma>: "Post1.Net.n\<gamma> trn" "Post1.Net.n\<gamma> trn'"
     and tr: "validSystemTrace (tr ## trn)" and tr': "validSystemTrace (tr' ## trn')"
     and g: "Post1.Net.ng trn = Post1.Net.ng trn'" and \<gamma>: "n\<gamma> trn" and \<gamma>': "n\<gamma> trn'"
  then have trn: "Post1.nValidTrans trn" and trn': "Post1.nValidTrans trn'" by auto
  show "ng trn = ng trn'" proof (cases trn)
    case (LTrans s aid1 trn1)
    then obtain s' trn1' where "trn' = LTrans s' aid1 trn1'" using g by (cases trn') auto
    then show ?thesis using LTrans \<gamma> \<gamma>' g trn trn'
      by (cases "(aid1,trn1)" rule: Post1.tgtNodeOf.cases;
          cases "(aid1,trn1')" rule: Post1.tgtNodeOf.cases)
         (auto simp: Strong_ObservationSetup_RECEIVER.g.simps Post_RECEIVER.sPurge_simp
               simp: Post1.Iss.sStep_unfold split: sActt.splits)
  next
    case (CTrans s aid1 trn1 aid2 trn2)
    with \<gamma> show ?thesis by auto
  qed
next
  fix tr tr' trn trn'
  assume tr: "validSystemTrace (tr ## trn)" and tr': "validSystemTrace (tr' ## trn')"
     and \<gamma>: "Post2.Net.n\<gamma> trn" and \<gamma>': "Post2.Net.n\<gamma> trn'" and g: "Post2.Net.ng trn = Post2.Net.ng trn'"
  from tr tr' have trn: "Post1.nValidTrans trn" "Post1.nValidTrans trn'" by auto
  show "n\<gamma> trn = n\<gamma> trn'" proof (cases trn)
    case (LTrans s aid1 trn1)
    then obtain s' trn1' where trn': "trn' = LTrans s' aid1 trn1'" using g by (cases trn') auto
    then show ?thesis using LTrans g
      by (cases trn1 rule: Strong_ObservationSetup_ISSUER.g.cases;
          cases trn1' rule: Strong_ObservationSetup_ISSUER.g.cases)
         (auto simp: Strong_ObservationSetup_RECEIVER.g.simps Post_RECEIVER.sPurge_simp)
  next
    case (CTrans s aid1 trn1 aid2 trn2)
    then show ?thesis using g by (cases trn') auto
  qed
next
  fix tr tr' trn trn'
  assume O: "Post2.O tr = Post2.O tr'" and \<gamma>: "Post2.Net.n\<gamma> trn" "Post2.Net.n\<gamma> trn'"
     and tr: "validSystemTrace (tr ## trn)" and tr': "validSystemTrace (tr' ## trn')"
     and g: "Post2.Net.ng trn = Post2.Net.ng trn'" and \<gamma>: "n\<gamma> trn" and \<gamma>': "n\<gamma> trn'"
  then have trn: "Post1.nValidTrans trn" and trn': "Post1.nValidTrans trn'" by auto
  show "ng trn = ng trn'" proof (cases trn)
    case (LTrans s aid1 trn1)
    then obtain s' trn1' where "trn' = LTrans s' aid1 trn1'" using g by (cases trn') auto
    then show ?thesis using LTrans \<gamma> \<gamma>' g trn trn'
      by (cases "(aid1,trn1)" rule: Post1.tgtNodeOf.cases;
          cases "(aid1,trn1')" rule: Post1.tgtNodeOf.cases)
         (auto simp: Strong_ObservationSetup_RECEIVER.g.simps Post_RECEIVER.sPurge_simp
               simp: Post1.Iss.sStep_unfold split: sActt.splits)
  next
    case (CTrans s aid1 trn1 aid2 trn2)
    with \<gamma> show ?thesis by auto
  qed
next
  fix tr trn
  assume "validSystemTrace (tr ## trn)" and n\<phi>: "Post2.Net.n\<phi> trn"
  then have trn: "Post1.nValidTrans trn" by auto
  show "Post1.Net.n\<gamma> trn" proof (cases trn)
    case (LTrans s aid1 trn1)
    then obtain a ou s1' where trn1: "trn1 = Trans (s aid1) a ou s1'" using trn by (cases trn1) auto
    then show ?thesis using n\<phi> trn LTrans AID1_neq_AID2
      using Post2.Iss.triggerEq_not_\<gamma>[THEN Post2.Iss.triggerEq_open]
      by (cases "Post2.Iss.\<gamma> trn1") (auto simp: Post2.\<phi>_defs Strong_ObservationSetup_RECEIVER.\<gamma>.simps)
  next
    case (CTrans s aid1 trn1 aid2 trn2)
    with trn have "Post1.sync aid1 trn1 aid2 trn2" by auto
    then show ?thesis using trn CTrans
      by (elim Post1.sync_cases) (auto simp: Strong_ObservationSetup_RECEIVER.\<gamma>.simps)
  qed
next
  fix tr tr' trn trn'
  assume O: "Post1.O tr = Post1.O tr'" and \<gamma>: "Post1.Net.n\<gamma> trn" "Post1.Net.n\<gamma> trn'"
     and tr: "validSystemTrace (tr ## trn)" and tr': "validSystemTrace (tr' ## trn')"
     and g: "Post1.Net.ng trn = Post1.Net.ng trn'"
  have op: "\<forall>aid. Post2.Iss.open (Post1.nSrcOf trn aid) \<longleftrightarrow> Post2.Iss.open (Post1.nSrcOf trn' aid)"
    using O \<gamma> tr tr' g by (intro Post2.nTriggerEq_open Post1.O_eq_nTriggerEq) auto
  have op': "\<forall>aid. Post2.Iss.open (Post1.nTgtOf trn aid) \<longleftrightarrow> Post2.Iss.open (Post1.nTgtOf trn' aid)"
    using O \<gamma> tr tr' g by (intro Post2.nTriggerEq_open Post1.O_eq_nTriggerEq) auto
  have trn: "Post1.nValidTrans trn" and trn': "Post1.nValidTrans trn'" using tr tr' by auto
  show "Post2.Net.n\<phi> trn = Post2.Net.n\<phi> trn'"
  proof (cases trn)
    case (LTrans s aid1 trn1)
    then obtain s' trn1' where s': "trn' = LTrans s' aid1 trn1'" using g by (cases trn') auto
    moreover then have "srcOf trn1 = s aid1" "srcOf trn1' = s' aid1"
                       "tgtOf trn1 = Post1.nTgtOf trn aid1" "tgtOf trn1' = Post1.nTgtOf trn' aid1"
      using LTrans trn trn' by auto
    ultimately show ?thesis using LTrans op op' g AID1_neq_AID2
      by (cases trn1 rule: Post.\<phi>.cases; cases trn1' rule: Post.\<phi>.cases)
         (auto simp: Strong_ObservationSetup_RECEIVER.g.simps Strong_ObservationSetup_RECEIVER.comPurge.simps
                     Post.\<phi>.simps Post_RECEIVER.\<phi>.simps)
  next
    case (CTrans s aid1 trn1 aid2 trn2)
    then obtain s' trn1' trn2' where CTrans': "trn' = CTrans s' aid1 trn1' aid2 trn2'"
      using g by (cases trn') auto
    have "Post1.sync aid1 trn1 aid2 trn2" "Post1.sync aid1 trn1' aid2 trn2'"
      using CTrans CTrans' trn trn' by auto
    then show ?thesis using CTrans CTrans' trn trn' op op' g
      by (elim Post1.sync_cases)
         (auto simp: Post_RECEIVER.\<phi>.simps Strong_ObservationSetup_RECEIVER.g.simps
                     Strong_ObservationSetup_RECEIVER.comPurge.simps)
  qed
next
  fix tr tr' trn trn'
  assume O: "Post1.O tr = Post1.O tr'" and \<gamma>: "Post1.Net.n\<gamma> trn" "Post1.Net.n\<gamma> trn'"
     and tr: "validSystemTrace (tr ## trn)" and tr': "validSystemTrace (tr' ## trn')"
     and g: "Post1.Net.ng trn = Post1.Net.ng trn'"
     and \<phi>: "Post2.Net.n\<phi> trn" and \<phi>': "Post2.Net.n\<phi> trn'"
  have op: "\<forall>aid. Post2.Iss.open (Post1.nSrcOf trn aid) \<longleftrightarrow> Post2.Iss.open (Post1.nSrcOf trn' aid)"
    using O \<gamma> tr tr' g by (intro Post2.nTriggerEq_open Post1.O_eq_nTriggerEq) auto
  have op': "\<forall>aid. Post2.Iss.open (Post1.nTgtOf trn aid) \<longleftrightarrow> Post2.Iss.open (Post1.nTgtOf trn' aid)"
    using O \<gamma> tr tr' g by (intro Post2.nTriggerEq_open Post1.O_eq_nTriggerEq) auto
  have trn: "Post1.nValidTrans trn" and trn': "Post1.nValidTrans trn'" using tr tr' by auto
  show "Post2.nf' trn = Post2.nf' trn'"
  proof (cases trn)
    case (LTrans s aid1 trn1)
    then obtain s' trn1' where s': "trn' = LTrans s' aid1 trn1'" using g by (cases trn') auto
    moreover then have "srcOf trn1 = s aid1" "srcOf trn1' = s' aid1"
                       "tgtOf trn1 = Post1.nTgtOf trn aid1" "tgtOf trn1' = Post1.nTgtOf trn' aid1"
      using LTrans trn trn' by auto
    ultimately show ?thesis using LTrans \<phi> \<phi>' op' g AID1_neq_AID2
      by (cases trn1 rule: Post.\<phi>.cases; cases trn1' rule: Post.f.cases)
         (auto simp: Strong_ObservationSetup_RECEIVER.g.simps Strong_ObservationSetup_RECEIVER.comPurge.simps
                     Post.\<phi>.simps Post_RECEIVER.\<phi>.simps)
  next
    case (CTrans s aid1 trn1 aid2 trn2)
    then obtain s' trn1' trn2' where CTrans': "trn' = CTrans s' aid1 trn1' aid2 trn2'"
      using g by (cases trn') auto
    then have trn1: "validTrans trn1" and trn1': "validTrans trn1'" using trn trn' CTrans by auto
    have states: "tgtOf trn1 = Post1.nTgtOf trn aid1" "tgtOf trn2 = Post1.nTgtOf trn aid2"
                 "tgtOf trn1' = Post1.nTgtOf trn' aid1" "tgtOf trn2' = Post1.nTgtOf trn' aid2"
      using trn trn' CTrans CTrans' by auto
    have "Post1.sync aid1 trn1 aid2 trn2" "Post1.sync aid1 trn1' aid2 trn2'"
      using CTrans CTrans' trn trn' by auto
    then show ?thesis using CTrans CTrans' op' g states AID1_neq_AID2
      by (elim Post1.sync_cases[OF _ trn1] Post1.sync_cases[OF _ trn1'])
         (auto simp: Post_RECEIVER.\<phi>.simps Strong_ObservationSetup_RECEIVER.g.simps
                     Strong_ObservationSetup_RECEIVER.comPurge.simps)
  qed
next
  fix tr trn
  assume "validSystemTrace (tr ## trn)" and n\<phi>: "Post1.Net.n\<phi> trn"
  then have trn: "Post1.nValidTrans trn" by auto
  show "Post2.Net.n\<gamma> trn" proof (cases trn)
    case (LTrans s aid1 trn1)
    then obtain a ou s1' where trn1: "trn1 = Trans (s aid1) a ou s1'" using trn by (cases trn1) auto
    then show ?thesis using n\<phi> trn LTrans AID1_neq_AID2
      using Post1.Iss.triggerEq_not_\<gamma>[THEN Post1.Iss.triggerEq_open]
      by (cases "Post1.Iss.\<gamma> trn1") (auto simp: Post1.\<phi>_defs Strong_ObservationSetup_RECEIVER.\<gamma>.simps)
  next
    case (CTrans s aid1 trn1 aid2 trn2)
    with trn have "Post1.sync aid1 trn1 aid2 trn2" by auto
    then show ?thesis
      using trn CTrans
      by (elim Post1.sync_cases) (auto simp: Strong_ObservationSetup_RECEIVER.\<gamma>.simps)
  qed
next
  fix tr tr' trn trn'
  assume O: "Post2.O tr = Post2.O tr'" and \<gamma>: "Post2.Net.n\<gamma> trn" "Post2.Net.n\<gamma> trn'"
     and tr: "validSystemTrace (tr ## trn)" and tr': "validSystemTrace (tr' ## trn')"
     and g: "Post2.Net.ng trn = Post2.Net.ng trn'"
  have op: "\<forall>aid. Post1.Iss.open (Post1.nSrcOf trn aid) \<longleftrightarrow> Post1.Iss.open (Post1.nSrcOf trn' aid)"
    using O \<gamma> tr tr' g by (intro Post1.nTriggerEq_open Post2.O_eq_nTriggerEq) auto
  have op': "\<forall>aid. Post1.Iss.open (Post1.nTgtOf trn aid) \<longleftrightarrow> Post1.Iss.open (Post1.nTgtOf trn' aid)"
    using O \<gamma> tr tr' g by (intro Post1.nTriggerEq_open Post2.O_eq_nTriggerEq) auto
  have trn: "Post1.nValidTrans trn" and trn': "Post1.nValidTrans trn'" using tr tr' by auto
  show "Post1.Net.n\<phi> trn = Post1.Net.n\<phi> trn'"
  proof (cases trn)
    case (LTrans s aid1 trn1)
    then obtain s' trn1' where s': "trn' = LTrans s' aid1 trn1'" using g by (cases trn') auto
    moreover then have "srcOf trn1 = s aid1" "srcOf trn1' = s' aid1"
                       "tgtOf trn1 = Post1.nTgtOf trn aid1" "tgtOf trn1' = Post1.nTgtOf trn' aid1"
      using LTrans trn trn' by auto
    ultimately show ?thesis using LTrans op op' g AID1_neq_AID2
      by (cases trn1 rule: Post.\<phi>.cases; cases trn1' rule: Post.\<phi>.cases)
         (auto simp: Strong_ObservationSetup_RECEIVER.g.simps Strong_ObservationSetup_RECEIVER.comPurge.simps
                     Post.\<phi>.simps Post_RECEIVER.\<phi>.simps)
  next
    case (CTrans s aid1 trn1 aid2 trn2)
    then obtain s' trn1' trn2' where CTrans': "trn' = CTrans s' aid1 trn1' aid2 trn2'"
      using g by (cases trn') auto
    have "Post1.sync aid1 trn1 aid2 trn2" "Post1.sync aid1 trn1' aid2 trn2'"
      using CTrans CTrans' trn trn' by auto
    then show ?thesis using CTrans CTrans' trn trn' op op' g
      by (elim Post1.sync_cases)
         (auto simp: Post_RECEIVER.\<phi>.simps Strong_ObservationSetup_RECEIVER.g.simps
                     Strong_ObservationSetup_RECEIVER.comPurge.simps)
  qed
next
  fix tr tr' trn trn'
  assume O: "Post2.O tr = Post2.O tr'" and \<gamma>: "Post2.Net.n\<gamma> trn" "Post2.Net.n\<gamma> trn'"
     and tr: "validSystemTrace (tr ## trn)" and tr': "validSystemTrace (tr' ## trn')"
     and g: "Post2.Net.ng trn = Post2.Net.ng trn'"
     and \<phi>: "Post1.Net.n\<phi> trn" and \<phi>': "Post1.Net.n\<phi> trn'"
  have op: "\<forall>aid. Post1.Iss.open (Post1.nSrcOf trn aid) \<longleftrightarrow> Post1.Iss.open (Post1.nSrcOf trn' aid)"
    using O \<gamma> tr tr' g by (intro Post1.nTriggerEq_open Post2.O_eq_nTriggerEq) auto
  have op': "\<forall>aid. Post1.Iss.open (Post1.nTgtOf trn aid) \<longleftrightarrow> Post1.Iss.open (Post1.nTgtOf trn' aid)"
    using O \<gamma> tr tr' g by (intro Post1.nTriggerEq_open Post2.O_eq_nTriggerEq) auto
  have trn: "Post1.nValidTrans trn" and trn': "Post1.nValidTrans trn'" using tr tr' by auto
  show "Post1.nf' trn = Post1.nf' trn'"
  proof (cases trn)
    case (LTrans s aid1 trn1)
    then obtain s' trn1' where s': "trn' = LTrans s' aid1 trn1'" using g by (cases trn') auto
    moreover then have "srcOf trn1 = s aid1" "srcOf trn1' = s' aid1"
                       "tgtOf trn1 = Post1.nTgtOf trn aid1" "tgtOf trn1' = Post1.nTgtOf trn' aid1"
      using LTrans trn trn' by auto
    ultimately show ?thesis using LTrans \<phi> \<phi>' op' g AID1_neq_AID2
      by (cases trn1 rule: Post.\<phi>.cases; cases trn1' rule: Post.f.cases)
         (auto simp: Strong_ObservationSetup_RECEIVER.g.simps Strong_ObservationSetup_RECEIVER.comPurge.simps
                     Post.\<phi>.simps Post_RECEIVER.\<phi>.simps)
  next
    case (CTrans s aid1 trn1 aid2 trn2)
    then obtain s' trn1' trn2' where CTrans': "trn' = CTrans s' aid1 trn1' aid2 trn2'"
      using g by (cases trn') auto
    then have trn1: "validTrans trn1" and trn1': "validTrans trn1'" using trn trn' CTrans by auto
    have states: "tgtOf trn1 = Post1.nTgtOf trn aid1" "tgtOf trn2 = Post1.nTgtOf trn aid2"
                 "tgtOf trn1' = Post1.nTgtOf trn' aid1" "tgtOf trn2' = Post1.nTgtOf trn' aid2"
      using trn trn' CTrans CTrans' by auto
    have "Post1.sync aid1 trn1 aid2 trn2" "Post1.sync aid1 trn1' aid2 trn2'"
      using CTrans CTrans' trn trn' by auto
    then show ?thesis using CTrans CTrans' op' g states AID1_neq_AID2
      by (elim Post1.sync_cases[OF _ trn1] Post1.sync_cases[OF _ trn1'])
         (auto simp: Post_RECEIVER.\<phi>.simps Strong_ObservationSetup_RECEIVER.g.simps
                     Strong_ObservationSetup_RECEIVER.comPurge.simps)
  qed
next
  fix tr trn
  assume nT_trn: "Post2.Net.nT trn" and tr: "validSystemTrace (tr ## trn)"
     and nT_tr: "never Post2.Net.nT tr"
  show "Post1.Net.n\<gamma> trn" proof (cases trn)
    case (CTrans s aid1 trn1 aid2 trn2)
    then have "Post1.sync aid1 trn1 aid2 trn2" using tr by auto
    then show ?thesis using tr CTrans
      by (elim Post1.sync_cases) (auto simp: Strong_ObservationSetup_RECEIVER.\<gamma>.simps)
  next
    case (LTrans s aid1 trn1)
    then obtain a ou s1' where trn1: "trn1 = Trans (s aid1) a ou s1'" using tr by (cases trn1) auto
    interpret R: Post_RECEIVER "UIDs aid1" PID2 AID2 .
    interpret R': Post_RECEIVER "UIDs aid1" PID1 AID1 .
    from nT_trn have aid1: "aid1 \<noteq> AID2" and Ttgt: "R.T_state s1'"
      using LTrans R.T_T_state trn1 by auto
    have decomp_tr: "Post1.Iss.validFrom istate (Post1.decomp (tr ## trn) aid1)"
      using LTrans tr Post1.validFrom_lValidFrom[of "\<lambda>_. istate"] by auto
    then have s_aid1: "s aid1 = tgtOfTrFrom istate (Post1.decomp tr aid1)"
      using LTrans trn1 unfolding Post1.decomp_append
      by (auto simp: Post1.Iss.validFrom_Cons Post1.Iss.validFrom_append)
    have "\<not>R.T_state (s aid1)" unfolding s_aid1 proof (intro R.never_T_not_T_state)
      show "Post1.Iss.validFrom istate (Post1.decomp tr aid1)" using decomp_tr
        unfolding Post1.decomp_append by (auto simp: Post1.Iss.validFrom_append)
      show "never R.T (Post1.decomp tr aid1)" using aid1 Post2.Net.nTT_TT[OF nT_tr, of aid1] by auto
      show "\<not> R.T_state istate" unfolding istate_def R.T_state_def by auto
    qed
    then have s_s1': "\<not>triggerEq (s aid1) s1'" using Ttgt by (auto simp: triggerEq_def R.T_state_def)
    show ?thesis proof (cases "aid1 = AID1")
      case True
      then show ?thesis using s_s1' Post1.Iss.triggerEq_not_\<gamma> tr unfolding trn1 LTrans
        by (cases "Post1.Iss.\<gamma> (Trans (s aid1) a ou s1')") auto
    next
      case False
      then show ?thesis using s_s1' R'.triggerEq_not_\<gamma> tr unfolding trn1 LTrans
        by (cases "R'.\<gamma> (Trans (s aid1) a ou s1')") auto
    qed
  qed
next
  fix tr tr' trn trn'
  assume O: "Post1.O tr = Post1.O tr'" and \<gamma>: "Post1.Net.n\<gamma> trn" "Post1.Net.n\<gamma> trn'"
     and tr: "validSystemTrace (tr ## trn)" and tr': "validSystemTrace (tr' ## trn')"
     and g: "Post1.Net.ng trn = Post1.Net.ng trn'"
  have op': "Post1.nTriggerEq (Post1.nTgtOf trn) (Post1.nTgtOf trn')"
    using O \<gamma> tr tr' g by (intro Post1.O_eq_nTriggerEq) auto
  have trn: "Post1.nValidTrans trn" and trn': "Post1.nValidTrans trn'" using tr tr' by auto
  show "Post2.Net.nT trn = Post2.Net.nT trn'" proof (cases trn)
    case (LTrans s aid1 trn1)
    moreover then obtain s' trn1' where LTrans': "trn' = LTrans s' aid1 trn1'"
      using g by (cases trn') auto
    ultimately have t: "triggerEq (tgtOf trn1) (tgtOf trn1')" using op' unfolding Post1.nTriggerEq_def
      by auto
    interpret R: Post_RECEIVER "UIDs aid1" PID2 AID2 .
    from t have "R.T_state (tgtOf trn1) \<longleftrightarrow> R.T_state (tgtOf trn1')" by (intro R.triggerEq_T)
    then show ?thesis using LTrans LTrans' by (auto simp: R.T_T_state)
  next
    case (CTrans s aid1 trn1 aid2 trn2)
    moreover then obtain s' trn1' trn2' where CTrans': "trn' = CTrans s' aid1 trn1' aid2 trn2'"
      using g by (cases trn') auto
    moreover then have "aid1 \<noteq> aid2" using trn' by auto
    ultimately have t: "triggerEq (tgtOf trn1) (tgtOf trn1')" "triggerEq (tgtOf trn2) (tgtOf trn2')"
      using op' unfolding Post1.nTriggerEq_def by auto
    interpret R1: Post_RECEIVER "UIDs aid1" PID2 AID2 .
    interpret R2: Post_RECEIVER "UIDs aid2" PID2 AID2 .
    from t have "R1.T_state (tgtOf trn1) \<longleftrightarrow> R1.T_state (tgtOf trn1')"
                "R2.T_state (tgtOf trn2) \<longleftrightarrow> R2.T_state (tgtOf trn2')"
      by (auto intro!: R1.triggerEq_T R2.triggerEq_T)
    then show ?thesis using CTrans CTrans' by (auto simp: R1.T_T_state R2.T_T_state)
  qed
qed

theorem two_posts_secure:
  "secure"
  using Post1.secure Post2.secure
  by (rule two_secure)

end

end
