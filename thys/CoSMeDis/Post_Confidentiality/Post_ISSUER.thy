theory Post_ISSUER
  imports
    "Bounded_Deducibility_Security.Compositional_Reasoning"
    "Post_Observation_Setup_ISSUER"
    "Post_Value_Setup_ISSUER"
begin

subsubsection \<open>Issuer declassification bound\<close>

text \<open>We verify that a group of users of some node \<open>i\<close>,
allowed to take normal actions to the system and observe their outputs
\emph{and additionally allowed to observe communication},
can learn nothing about the updates to a post located at node \<open>i\<close>
and the sends of that post to other nodes beyond

(1) the presence of the sends (i.e., the number of the sending actions)

(2) the public knowledge that what is being sent is always the last version (modeled as
the correlation predicate)

unless:
\begin{itemize}
\item either a user in the group is the post's owner or the administrator
\item or a user in the group becomes a friend of the owner
\item or the group has at least one registered user and the post is being marked as "public"
\end{itemize}

See \<^cite>\<open>"cosmedis-SandP2017"\<close> for more details.
\<close>

context Post_ISSUER
begin

fun T :: "(state,act,out) trans \<Rightarrow> bool" where
"T (Trans s a ou s') \<longleftrightarrow>
 (\<exists> uid \<in> UIDs.
   uid \<in>\<in> userIDs s' \<and> PID \<in>\<in> postIDs s' \<and>
   (uid = admin s' \<or>
    uid = owner s' PID \<or>
    uid \<in>\<in> friendIDs s' (owner s' PID) \<or>
    vis s' PID = PublicV))"

(* Correlation is defined to mean: always send what was last uploaded, or emptyPost
if nothing had been uploaded. This needs the auxiliary notion of "correlated from" *)
fun corrFrom :: "post \<Rightarrow> value list \<Rightarrow> bool" where
 "corrFrom pst [] = True"
|"corrFrom pst (PVal pstt # vl) = corrFrom pstt vl"
|"corrFrom pst (PValS aid pstt # vl) = (pst = pstt \<and> corrFrom pst vl)"

abbreviation corr :: "value list \<Rightarrow> bool" where "corr \<equiv> corrFrom emptyPost"

(* Beyond correlation (which is public knowledge), one can only learn
the absence of any secret produced (if that is the case), the number of
times the notice has been sent, and to which nodes they have been sent:
(since network traffic is assumed to be observable) *)
definition B :: "value list \<Rightarrow> value list \<Rightarrow> bool" where
"B vl vl1 \<equiv>
 corr vl1 \<and>
 (vl = [] \<longrightarrow> vl1 = []) \<and>
 map PValS_tgtAPI (filter isPValS vl) = map PValS_tgtAPI (filter isPValS vl1)"


sublocale BD_Security_IO where
istate = istate and step = step and
\<phi> = \<phi> and f = f and \<gamma> = \<gamma> and g = g and T = T and B = B
done

subsubsection \<open>Unwinding proof\<close>

lemma reach_PublicV_imples_FriendV[simp]:
assumes "reach s"
and "vis s pID \<noteq> PublicV"
shows "vis s pID = FriendV"
using assms reach_vis by auto

lemma reachNT_state:
assumes "reachNT s"
shows "\<not> (\<exists> uid \<in> UIDs.
   uid \<in>\<in> userIDs s \<and> PID \<in>\<in> postIDs s \<and>
   (uid = admin s \<or> uid = owner s PID \<or> uid \<in>\<in> friendIDs s (owner s PID) \<or>
    vis s PID = PublicV))"
using assms proof induct
  case (Step trn) thus ?case
  by (cases trn) auto
qed (simp add: istate_def)

(* major *) lemma T_\<phi>_\<gamma>:
assumes 1: "reachNT s" and 2: "step s a = (ou,s')"
and 3: "\<phi> (Trans s a ou s')" and
(* note that now we have some overlap between \<phi> and \<gamma>, even for reachNT: *)
4: "\<forall> ca. a \<noteq> COMact ca"
shows "\<not> \<gamma> (Trans s a ou s')"
using reachNT_state[OF 1] 2 3 4 using \<phi>_def2(* [OF 2] *)
by (auto simp add: u_defs com_defs)

(* major *) lemma eqButPID_step_\<gamma>_out:
assumes ss1: "eqButPID s s1"
and step: "step s a = (ou,s')" and step1: "step s1 a = (ou1,s1')"
and sT: "reachNT s" and T: "\<not> T (Trans s a ou s')"
and s1: "reach s1"
and \<gamma>: "\<gamma> (Trans s a ou s')"
shows "(\<exists> uid p aid pid. a = COMact (comSendPost uid p aid pid) \<and> outPurge ou = outPurge ou1) \<or> ou = ou1"
proof-
  have s'T: "reachNT s'" using step sT T using reachNT_PairI by blast
  note op = reachNT_state[OF s'T]
  note [simp] = all_defs
  note s = reachNT_reach[OF sT]
  note willUse =
    step step1 \<gamma>
    op
    reach_vis[OF s]
    eqButPID_stateSelectors[OF ss1] (* eqButPID_postSelectors[OF ss1] *)
    eqButPID_actions[OF ss1]
    eqButPID_update[OF ss1] (* eqButPID_setTextPost[OF ss1] *) eqButPID_not_PID[OF ss1]
    (* added to cope with extra leak towards the admin, when moving from API to CAPI: *)
    (* eqButPID_eqButT[OF ss1] *) eqButPID_eqButF[OF ss1]
    eqButPID_setShared[OF ss1] eqButPID_updateShared[OF ss1]
    eeqButPID_F_not_PID eqButPID_not_PID_sharedWith
    eqButPID_insert2[OF ss1]
  show ?thesis
  proof (cases a)
    case (Sact x1)
    with willUse show ?thesis by (cases x1) auto
  next
    case (Cact x2)
    with willUse show ?thesis by (cases x2) auto
  next
    case (Dact x3)
    with willUse show ?thesis by (cases x3) auto
  next
    case (Uact x4)
    with willUse show ?thesis by (cases x4) auto
  next
    case (Ract x5)
    with willUse show ?thesis
    proof (cases x5)
      case (rPost uid p pid)
      with Ract willUse show ?thesis by (cases "pid = PID") auto
    qed auto
  next
    case (Lact x6)
    with willUse show ?thesis
    proof (cases x6)
      case (lClientsPost uid p pid)
      with Lact willUse show ?thesis by (cases "pid = PID") auto
    qed auto
  next
    case (COMact x7)
    with willUse show ?thesis by (cases x7) auto
  qed
qed

(* major *) lemma eqButPID_step_eq:
assumes ss1: "eqButPID s s1"
and a: "a = Uact (uPost uid p PID pst)" "ou = outOK"
and step: "step s a = (ou, s')" and step1: "step s1 a = (ou', s1')"
shows "s' = s1'"
using ss1 step step1
using eqButPID_stateSelectors[OF ss1]
eqButPID_update[OF ss1] (* eqButPID_setTextPost[OF ss1] *) eqButPID_setShared[OF ss1]
unfolding a by (auto simp: u_defs)

definition \<Delta>0 :: "state \<Rightarrow> value list \<Rightarrow> state \<Rightarrow> value list \<Rightarrow> bool" where
"\<Delta>0 s vl s1 vl1 \<equiv>
 \<not> PID \<in>\<in> postIDs s \<and> post s PID = emptyPost \<and>
 s = s1 \<and>
 corrFrom (post s1 PID) vl1 \<and>
 (vl = [] \<longrightarrow> vl1 = []) \<and>
 map PValS_tgtAPI (filter isPValS vl) = map PValS_tgtAPI (filter isPValS vl1)"

definition \<Delta>1 :: "state \<Rightarrow> value list \<Rightarrow> state \<Rightarrow> value list \<Rightarrow> bool" where
"\<Delta>1 s vl s1 vl1 \<equiv>
 PID \<in>\<in> postIDs s \<and>
 eqButPID s s1 \<and>
 corrFrom (post s1 PID) vl1 \<and>
 (vl = [] \<longrightarrow> vl1 = []) \<and>
 map PValS_tgtAPI (filter isPValS vl) = map PValS_tgtAPI (filter isPValS vl1)"

definition \<Delta>2 :: "state \<Rightarrow> value list \<Rightarrow> state \<Rightarrow> value list \<Rightarrow> bool" where
"\<Delta>2 s vl s1 vl1 \<equiv>
 PID \<in>\<in> postIDs s \<and>
 eqButPID s s1 \<and>
 vl = [] \<and> list_all isPVal vl1"

lemma istate_\<Delta>0:
assumes B: "B vl vl1"
shows "\<Delta>0 istate vl istate vl1"
using assms unfolding \<Delta>0_def B_def istate_def by auto

lemma unwind_cont_\<Delta>0: "unwind_cont \<Delta>0 {\<Delta>0,\<Delta>1}"
proof(rule, simp)
  let ?\<Delta> = "\<lambda>s vl s1 vl1. \<Delta>0 s vl s1 vl1 \<or> \<Delta>1 s vl s1 vl1"
  fix s s1 :: state and vl vl1 :: "value list"
  assume rsT: "reachNT s" and rs1: "reach s1" and "\<Delta>0 s vl s1 vl1"
  hence rs: "reach s" and ss1: "s1 = s" and pPID: "post s PID = emptyPost"
  and ch: "corrFrom (post s1 PID) vl1"
  and l: "map PValS_tgtAPI (filter isPValS vl) = map PValS_tgtAPI (filter isPValS vl1)"
  and PID: "\<not> PID \<in>\<in> postIDs s" and vlvl1: "vl = [] \<Longrightarrow> vl1 = []"
  using reachNT_reach unfolding \<Delta>0_def by auto
  show "iaction ?\<Delta> s vl s1 vl1 \<or>
        ((vl = [] \<longrightarrow> vl1 = []) \<and> reaction ?\<Delta> s vl s1 vl1)" (is "?iact \<or> (_ \<and> ?react)")
  proof-
    have ?react proof
      fix a :: act and ou :: out and s' :: state and vl'
      let ?trn = "Trans s a ou s'"  let ?trn1 = "Trans s1 a ou s'"
      assume step: "step s a = (ou, s')" and T: "\<not> T ?trn" and c: "consume ?trn vl vl'"
      show "match ?\<Delta> s s1 vl1 a ou s' vl' \<or> ignore ?\<Delta> s s1 vl1 a ou s' vl'" (is "?match \<or> ?ignore")
      proof-
        have \<phi>: "\<not> \<phi> ?trn" using PID step unfolding \<phi>_def2(* [OF step] *) by (auto simp: u_defs com_defs)
        hence vl': "vl' = vl" using c \<phi> unfolding consume_def by simp
        have pPID': "post s' PID = emptyPost"
          using pPID PID step
          apply(cases a)
          subgoal for x1 apply(cases x1, auto simp: all_defs) .
          subgoal for x2 apply(cases x2, auto simp: all_defs) .
          subgoal for x3 apply(cases x3, auto simp: all_defs) .
          subgoal for x4 apply(cases x4, auto simp: all_defs) .
          subgoal by auto
          subgoal by auto
          subgoal for x7 apply(cases x7, auto simp: all_defs) .
          done
        have ?match proof(cases "\<exists> uid p. a = Cact (cPost uid p PID) \<and> ou = outOK")
          case True
          then obtain uid p where a: "a = Cact (cPost uid p PID)" and ou: "ou = outOK" by auto
          have PID': "PID \<in>\<in> postIDs s'"
          using step PID unfolding a ou by (auto simp: c_defs)
          note uid = reachNT_state[OF rsT]
          show ?thesis proof
            show "validTrans ?trn1" unfolding ss1 using step by simp
          next
            show "consume ?trn1 vl1 vl1" using \<phi> unfolding consume_def ss1 by auto
          next
            show "\<gamma> ?trn = \<gamma> ?trn1" unfolding ss1 by simp
          next
            assume "\<gamma> ?trn" thus "g ?trn = g ?trn1" unfolding ss1 by simp
          next
            have "\<Delta>1 s' vl' s' vl1" using l PID' c ch vlvl1 pPID' pPID
             unfolding ss1 \<Delta>1_def vl' by auto
            thus "?\<Delta> s' vl' s' vl1" by simp
          qed
        next
          case False note a = False
          have PID': "\<not> PID \<in>\<in> postIDs s'"
            using step PID a
            apply(cases a)
            subgoal for x1 apply(cases x1) apply(fastforce simp: s_defs)+ .
            subgoal for x2 apply(cases x2) apply(fastforce simp: c_defs)+ .
            subgoal for x3 apply(cases x3) apply(fastforce simp: d_defs)+ .
            subgoal for x4 apply(cases x4) apply(fastforce simp: u_defs)+ .
            subgoal by auto
            subgoal by auto
            subgoal for x7 apply(cases x7) apply(fastforce simp: com_defs)+ .
            done
          show ?thesis proof
            show "validTrans ?trn1" unfolding ss1 using step by simp
          next
            show "consume ?trn1 vl1 vl1" using \<phi> unfolding consume_def ss1 by auto
          next
            show "\<gamma> ?trn = \<gamma> ?trn1" unfolding ss1 by simp
          next
            assume "\<gamma> ?trn" thus "g ?trn = g ?trn1" unfolding ss1 by simp
          next
            have "\<Delta>0 s' vl' s' vl1" using a PID' pPID pPID' ch vlvl1 l unfolding \<Delta>0_def vl' ss1 by simp
            thus "?\<Delta> s' vl' s' vl1" by simp
          qed
        qed
        thus ?thesis by simp
      qed
    qed
  thus ?thesis using vlvl1 by simp
  qed
qed

lemma unwind_cont_\<Delta>1: "unwind_cont \<Delta>1 {\<Delta>1,\<Delta>2}"
proof(rule, simp)
  let ?\<Delta> = "\<lambda>s vl s1 vl1. \<Delta>1 s vl s1 vl1 \<or> \<Delta>2 s vl s1 vl1"
  fix s s1 :: state and vl vl1 :: "value list"
  assume rsT: "reachNT s" and rs1: "reach s1" and "\<Delta>1 s vl s1 vl1"
  hence vlvl1: "vl = [] \<longrightarrow> vl1 = []" and ch1: "corrFrom (post s1 PID) vl1"
  and rs: "reach s" and ss1: "eqButPID s s1" and PID: "PID \<in>\<in> postIDs s"
  and l: "map PValS_tgtAPI (filter isPValS vl) = map PValS_tgtAPI (filter isPValS vl1)"
  using reachNT_reach unfolding \<Delta>1_def by auto
  have PID1: "PID \<in>\<in> postIDs s1" using eqButPID_stateSelectors[OF ss1] PID by auto
  have own: "owner s PID \<in> set (userIDs s)" using reach_owner_userIDs[OF rs PID] .
  hence own1: "owner s1 PID \<in> set (userIDs s1)" using eqButPID_stateSelectors[OF ss1] by auto
  show "iaction ?\<Delta> s vl s1 vl1 \<or>
        ((vl = [] \<longrightarrow> vl1 = []) \<and> reaction ?\<Delta> s vl s1 vl1)" (is "?iact \<or> (_ \<and> ?react)")
  proof(cases vl1)
    case (Cons v1 vll1) note vl1 = Cons
    obtain v vll where vl: "vl = v # vll" using vl1 vlvl1 by (cases vl) auto
    show ?thesis
    proof(cases v1)
      case (PVal pst1) note v1 = PVal
      let ?uid1 = "owner s1 PID" let ?p1 = "pass s1 ?uid1"
      have uid1: "?uid1 \<in>\<in> userIDs s1" using reach_owner_userIDs[OF rs1 PID1] .
      define a1 where "a1 \<equiv> Uact (uPost ?uid1 ?p1 PID pst1)"
      obtain s1' ou1 where step1: "step s1 a1 = (ou1,s1')" by force
      hence ou1: "ou1 = outOK" using PID1 uid1 unfolding a1_def by (auto simp: u_defs)
      let ?trn1 = "Trans s1 a1 ou1 s1'"
      have \<phi>1: "\<phi> ?trn1" unfolding a1_def PID1 ou1 by simp
      have 2[simp]: "post s1' PID = pst1"
      using step1 unfolding a1_def ou1 by (auto simp: u_defs)
      have "?uid1 = owner s PID" using eqButPID_stateSelectors[OF ss1] by simp
      hence uid1: "?uid1 \<notin> UIDs" using reachNT_state own rsT PID by auto
      have "eqButPID s1 s1'" using step1 a1_def Uact_uPaperC_step_eqButPID by auto
      hence ss1': "eqButPID s s1'" using ss1 using eqButPID_trans by blast
      have "?iact" proof
        show "step s1 a1 = (ou1, s1')" "\<phi> ?trn1" by fact+
        show "consume (Trans s1 a1 ou1 s1') vl1 vll1"
        using \<phi>1 unfolding consume_def vl1 a1_def v1 by simp
        show "\<not> \<gamma> ?trn1" using uid1 unfolding a1_def by auto
        show "?\<Delta> s vl s1' vll1"
        proof(cases vll1)
          case Nil
          have "\<Delta>1 s vl s1' vll1" using PID ss1' l unfolding \<Delta>1_def B_def vl1 v1 Nil by auto
          thus ?thesis by simp
        next
          case (Cons w1 vlll1) note vll1 = Cons
          have "\<Delta>1 s vl s1' vll1" using PID ss1' l ch1
          unfolding \<Delta>1_def B_def vl1 v1 vl by auto
          thus ?thesis by simp
        qed
      qed
      thus ?thesis by simp
    next
      case (PValS aid1 pst1) note v1 = PValS
      have pst1: "pst1 = post s1 PID" using ch1 unfolding vl1 v1 by simp
      show ?thesis
      proof(cases v)
        case (PVal "pst") note v = PVal
        hence vll: "vll \<noteq> []" using vlvl1 l unfolding vl vl1 v v1 by auto
        have ?react proof
          fix a :: act and ou :: out and s' :: state and vl'
          let ?trn = "Trans s a ou s'"
          assume step: "step s a = (ou, s')" and T: "\<not> T ?trn" and c: "consume ?trn vl vl'"
          have vl': "vl' = vl \<or> vl' = vll" using c unfolding vl consume_def by (cases "\<phi> ?trn") auto
          hence vl'NE: "vl' \<noteq> []" using vll vl by auto
          have fvl': "filter isPValS vl' = filter isPValS vll" using vl' unfolding vl v by auto
          obtain ou1 s1' where step1: "step s1 a = (ou1, s1')" by fastforce
          let ?trn1 = "Trans s1 a ou1 s1'"
          have s's1': "eqButPID s' s1'" using eqButPID_step ss1 step step1 by blast
          have \<gamma>\<gamma>1: "\<gamma> ?trn \<longleftrightarrow> \<gamma> ?trn1" by simp
          have PID': "PID \<in>\<in> postIDs s'" using step rs PID using reach_postIDs_persist by blast
          have 2[simp]: "\<not> \<phi> ?trn1 \<Longrightarrow> post s1' PID = post s1 PID"
            using step1 PID1 unfolding \<phi>_def2(* [OF step1] *)
            apply(cases a, auto)
            subgoal for x1 apply(cases x1, auto simp: all_defs) .
            subgoal for x2 apply(cases x2, auto simp: all_defs) .
            subgoal for x3 apply(cases x3, auto simp: all_defs) .
            subgoal for x4 apply(cases x4, auto simp: all_defs) .
            subgoal for x4 apply(cases x4, auto simp: all_defs) .
            subgoal for x7 apply(cases x7, auto simp: all_defs) .
            subgoal for x7 apply(cases x7, auto simp: all_defs) .
            done
          show "match ?\<Delta> s s1 vl1 a ou s' vl' \<or> ignore ?\<Delta> s s1 vl1 a ou s' vl'" (is "?match \<or> ?ignore")
          proof(cases "\<gamma> ?trn")
            case True note \<gamma> = True
            have ou: "(\<exists> uid p aid pid. a = COMact (comSendPost uid p aid pid) \<and> outPurge ou = outPurge ou1) \<or>
                                        ou = ou1"
            using eqButPID_step_\<gamma>_out[OF ss1 step step1 rsT T rs1 \<gamma>] .
            {assume \<phi>: "\<phi> ?trn"
             hence "f ?trn = v" using c unfolding consume_def vl by simp
             hence "\<forall>ca. a \<noteq> COMact ca" using \<phi> unfolding \<phi>_def3[OF step] v by auto
             hence False using T_\<phi>_\<gamma>[OF rsT step \<phi>] \<gamma> by auto
            }
            hence \<phi>: "\<not> \<phi> ?trn" by auto
            have vl': "vl' = vl" using \<phi> c unfolding consume_def by simp
            have \<phi>1: "\<not> \<phi> ?trn1" using step step1 ss1 \<phi> eqButPID_step_\<phi> by blast
            have ?match proof
              show "validTrans ?trn1" using step1 by auto
              show "consume ?trn1 vl1 vl1" using \<phi>1 unfolding consume_def by simp
              show "\<gamma> ?trn \<longleftrightarrow> \<gamma> ?trn1" by fact
            next
              show "g ?trn = g ?trn1" using ou by (cases a) auto
              have "\<Delta>1 s' vl' s1' vl1"
              using PID' s's1' vlvl1 l ch1 \<phi>1 unfolding \<Delta>1_def vl' by auto
              thus "?\<Delta> s' vl' s1' vl1" by simp
            qed
            thus ?thesis by simp
          next
            case False note \<gamma> = False
            show ?thesis
            proof(cases "\<phi> ?trn")
              case True note \<phi> = True
              hence "f ?trn = v" using c unfolding consume_def vl by simp
              hence "\<forall>ca. a \<noteq> COMact ca" using \<phi> unfolding \<phi>_def3[OF step] v by auto
              then obtain uid p "pstt" where a: "a = Uact (uPost uid p PID pstt)"
              using \<phi> unfolding \<phi>_def2(* [OF step] *) by auto
              hence ss': "eqButPID s s'" using step Uact_uPaperC_step_eqButPID by auto
              hence s's1: "eqButPID s' s1" using ss1 eqButPID_sym eqButPID_trans by blast
              have ?ignore proof
                show "\<not> \<gamma> ?trn" by fact
                have "\<Delta>1 s' vl' s1 vl1"
                using PID' s's1' ch1 l vl'NE s's1 unfolding \<Delta>1_def fvl' vl v by auto
                thus "?\<Delta> s' vl' s1 vl1" by simp
              qed
              thus ?thesis by simp
            next
              case False note \<phi> = False
              have vl': "vl' = vl" using \<phi> c unfolding consume_def by simp
              have \<phi>1: "\<not> \<phi> ?trn1" using step step1 ss1 \<phi> eqButPID_step_\<phi> by blast
              have ?match proof
                show "validTrans ?trn1" using step1 by auto
                show "consume ?trn1 vl1 vl1" using \<phi>1 unfolding consume_def by simp
                show "\<gamma> ?trn \<longleftrightarrow> \<gamma> ?trn1" by fact
              next
                assume "\<gamma> ?trn" thus "g ?trn = g ?trn1" using \<gamma> by simp
              next
                have "\<Delta>1 s' vl' s1' vl1"
                using PID' s's1' vlvl1 l ch1 \<phi>1 unfolding \<Delta>1_def vl' by auto
                thus "?\<Delta> s' vl' s1' vl1" by simp
              qed
              thus ?thesis by simp
            qed
          qed
        qed
        thus ?thesis using vlvl1 by simp
      next
        case (PValS aid "pst") note v = PValS
        have ?react proof
          fix a :: act and ou :: out and s' :: state and vl'
          let ?trn = "Trans s a ou s'"
          assume step: "step s a = (ou, s')" and T: "\<not> T ?trn" and c: "consume ?trn vl vl'"
          have vl': "vl' = vl \<or> vl' = vll" using c unfolding vl consume_def by (cases "\<phi> ?trn") auto
          obtain ou1 s1' where step1: "step s1 a = (ou1, s1')" by fastforce
          let ?trn1 = "Trans s1 a ou1 s1'"
          have s's1': "eqButPID s' s1'" using eqButPID_step ss1 step step1 by blast
          have \<gamma>\<gamma>1: "\<gamma> ?trn \<longleftrightarrow> \<gamma> ?trn1" by simp
          have PID': "PID \<in>\<in> postIDs s'" using step rs PID using reach_postIDs_persist by blast
          show "match ?\<Delta> s s1 vl1 a ou s' vl' \<or> ignore ?\<Delta> s s1 vl1 a ou s' vl'" (is "?match \<or> ?ignore")
          proof-
            have ?match proof(cases "\<phi> ?trn")
              case True note \<phi> = True
              have \<phi>1: "\<phi> ?trn1" using step step1 ss1 \<phi> eqButPID_step_\<phi> by blast
              let ?ad = "admin s"  let ?p = "pass s ?ad" let ?pst = "post s PID"
              let ?uid = "owner s PID" let ?vs = "vis s PID"
              obtain vl': "vl' = vll"
              and ou: "ou = O_sendPost (aid, clientPass s aid, PID, pst, ?uid, ?vs)"
              and a: "a = COMact (comSendPost ?ad ?p aid PID)" and "pst": "pst = ?pst"
              using \<phi> c unfolding \<phi>_def3[OF step] consume_def vl v by auto
              let ?pst1 = "post s1 PID"
              have "clientPass s aid = clientPass s1 aid" and "?uid = owner s1 PID"
              and "?vs = vis s1 PID"
              using eqButPID_stateSelectors[OF ss1] by auto
              hence ou1: "ou1 = O_sendPost (aid, clientPass s aid, PID, ?pst1, ?uid, ?vs)"
              using step1 \<phi>1 unfolding \<phi>_def3[OF step1] vl1 v1 a
              by (auto simp: com_defs)
              have 2[simp]: "post s1' PID = pst1"
              using step1 unfolding a ou1 pst1 by (auto simp: com_defs)
              have ch_vll1: "corrFrom pst1 vll1" using ch1 unfolding pst1[symmetric] vl1 v1 by auto
              show ?thesis proof
                show "validTrans ?trn1" using step1 by auto
                show "consume (Trans s1 a ou1 s1') vl1 vll1"
                using l \<phi>1 pst1 unfolding consume_def vl vl1 v v1 a ou1 by simp
                show "\<gamma> ?trn \<longleftrightarrow> \<gamma> ?trn1" by fact
              next
                show "g ?trn = g ?trn1" unfolding a ou ou1 by (simp add: ss1)
                show "?\<Delta> s' vl' s1' vll1"
                proof(cases "vll = []")
                  case False
                  hence "\<Delta>1 s' vl' s1' vll1" using PID' s's1' vlvl1 l ch1 ch_vll1
                  unfolding \<Delta>1_def vl' vl vl1 v v1 by auto
                  thus ?thesis by simp
                next
                  case True
                  hence "list_all isPVal vll1" using l unfolding vl vl1 v v1 by (simp add: filter_isPValS_Nil)
                  hence "\<Delta>2 s' vl' s1' vll1" using True PID' s's1' vlvl1 l ch1 ch_vll1
                  unfolding \<Delta>2_def vl' vl vl1 v v1 by simp
                  thus ?thesis by simp
                qed
              qed
            next
              case False note \<phi> = False
              have vl': "vl' = vl" using \<phi> c unfolding consume_def by simp
              have \<phi>1: "\<not> \<phi> ?trn1" using step step1 ss1 \<phi> eqButPID_step_\<phi> by blast
              have ?match proof
                show "validTrans ?trn1" using step1 by auto
                show "consume ?trn1 vl1 vl1" using \<phi>1 unfolding consume_def by simp
                show "\<gamma> ?trn \<longleftrightarrow> \<gamma> ?trn1" by fact
              next
                assume "\<gamma> ?trn" note \<gamma> = this
                have ou: "(\<exists> uid p aid pid. a = COMact (comSendPost uid p aid pid) \<and> outPurge ou = outPurge ou1) \<or>
                                        ou = ou1"
                using eqButPID_step_\<gamma>_out[OF ss1 step step1 rsT T rs1 \<gamma>] .
                thus "g ?trn = g ?trn1" by (cases a) auto
              next
                have 2[simp]: "post s1' PID  = post s1 PID"
                  using step1 PID1 \<phi>1 unfolding \<phi>_def2(* [OF step1] *)
                  apply(cases a)
                  subgoal for x1 apply(cases x1, auto simp: all_defs) .
                  subgoal for x2 apply(cases x2, auto simp: all_defs) .
                  subgoal for x3 apply(cases x3, auto simp: all_defs) .
                  subgoal for x4 apply(cases x4, auto simp: all_defs) .
                  subgoal by auto
                  subgoal by auto
                  subgoal for x7 apply(cases x7, auto simp: all_defs) .
                  done
                have "\<Delta>1 s' vl' s1' vl1" using PID' s's1' vlvl1 l ch1
                unfolding \<Delta>1_def vl' vl vl1 v v1 by auto
                thus "?\<Delta> s' vl' s1' vl1" by simp
              qed
              thus ?thesis by simp
            qed
            thus ?thesis by simp
          qed
        qed
        thus ?thesis using vlvl1 by simp
      qed
    qed
  next
    case Nil note vl1 = Nil
    have ?react proof
      fix a :: act and ou :: out and s' :: state and vl'
      let ?trn = "Trans s a ou s'"
      assume step: "step s a = (ou, s')" and T: "\<not> T ?trn" and c: "consume ?trn vl vl'"
      obtain ou1 s1' where step1: "step s1 a = (ou1, s1')" by fastforce
      let ?trn1 = "Trans s1 a ou1 s1'"
      have s's1': "eqButPID s' s1'" using eqButPID_step ss1 step step1 by blast
      have \<gamma>\<gamma>1: "\<gamma> ?trn \<longleftrightarrow> \<gamma> ?trn1" by simp
      have PID': "PID \<in>\<in> postIDs s'" using step rs PID using reach_postIDs_persist by blast
      show "match ?\<Delta> s s1 vl1 a ou s' vl' \<or> ignore ?\<Delta> s s1 vl1 a ou s' vl'" (is "?match \<or> ?ignore")
      proof(cases "\<phi> ?trn")
        case True note \<phi> = True
        then obtain v vll where vl: "vl = v # vll"
        and f: "f ?trn = v" using c unfolding consume_def by (cases vl) auto
        obtain "pst" where v: "v = PVal pst" using l unfolding vl1 vl by (cases v) auto
        have fvll: "filter isPValS vll = []"using l unfolding vl1 vl by auto
        have vl': "vl' = vll" using c \<phi> unfolding vl consume_def by auto
        hence 0: "\<forall>ca. a \<noteq> COMact ca" using \<phi> v f unfolding \<phi>_def3[OF step] by auto
        then obtain uid p "pstt" where a: "a = Uact (uPost uid p PID pstt)"
        using \<phi> unfolding \<phi>_def2(* [OF step] *) by auto
        hence ss': "eqButPID s s'" using step Uact_uPaperC_step_eqButPID by auto
        hence s's1: "eqButPID s' s1" using ss1 eqButPID_sym eqButPID_trans by blast
        have ?ignore proof
          show "\<not> \<gamma> ?trn" using T_\<phi>_\<gamma>[OF rsT step \<phi> 0] .
          have "\<Delta>1 s' vl' s1 vl1"
          using PID' s's1' ch1 l s's1 vl1 fvll  unfolding \<Delta>1_def vl v vl' by auto
          thus "?\<Delta> s' vl' s1 vl1" by simp
        qed
        thus ?thesis by simp
      next
        case False note \<phi> = False
        have vl': "vl' = vl" using \<phi> c unfolding consume_def by simp
        have \<phi>1: "\<not> \<phi> ?trn1" using step step1 ss1 \<phi> eqButPID_step_\<phi> by blast
        have ?match proof
          show "validTrans ?trn1" using step1 by auto
          show "consume ?trn1 vl1 vl1" using \<phi>1 unfolding consume_def by simp
          show "\<gamma> ?trn \<longleftrightarrow> \<gamma> ?trn1" by fact
        next
          assume "\<gamma> ?trn" note \<gamma> = this
          have ou: "(\<exists> uid p aid pid. a = COMact (comSendPost uid p aid pid) \<and> outPurge ou = outPurge ou1) \<or>
                                        ou = ou1"
          using eqButPID_step_\<gamma>_out[OF ss1 step step1 rsT T rs1 \<gamma>] .
          thus "g ?trn = g ?trn1" by (cases a) auto
        next
          have 2[simp]: "post s1' PID  = post s1 PID"
            using step1 PID1 \<phi>1 unfolding \<phi>_def2(* [OF step1] *)
            apply(cases a)
            subgoal for x1 apply(cases x1, auto simp: all_defs) .
            subgoal for x2 apply(cases x2, auto simp: all_defs) .
            subgoal for x3 apply(cases x3, auto simp: all_defs) .
            subgoal for x4 apply(cases x4, auto simp: all_defs) .
            subgoal by auto
            subgoal by auto
            subgoal for x7 apply(cases x7, auto simp: all_defs) .
            done
          have "\<Delta>1 s' vl' s1' vl1" using PID' s's1' vlvl1 l ch1
          unfolding \<Delta>1_def vl' vl1 by auto
          thus "?\<Delta> s' vl' s1' vl1" by simp
        qed
        thus ?thesis by simp
      qed
    qed
    thus ?thesis using vl1 by simp
  qed
qed

lemma unwind_cont_\<Delta>2: "unwind_cont \<Delta>2 {\<Delta>2}"
proof(rule, simp)
  let ?\<Delta> = "\<lambda>s vl s1 vl1. \<Delta>2 s vl s1 vl1"
  fix s s1 :: state and vl vl1 :: "value list"
  assume rsT: "reachNT s" and rs1: "reach s1" and "\<Delta>2 s vl s1 vl1"
  hence PID: "PID \<in>\<in> postIDs s" and ss1: "eqButPID s s1" and vl: "vl = []" and lvl1: "list_all isPVal vl1"
  and rs: "reach s" using reachNT_reach unfolding \<Delta>2_def by auto
  have PID1: "PID \<in>\<in> postIDs s1" using eqButPID_stateSelectors[OF ss1] PID by auto
  have own: "owner s PID \<in> set (userIDs s)" using reach_owner_userIDs[OF rs PID] .
  hence own1: "owner s1 PID \<in> set (userIDs s1)" using eqButPID_stateSelectors[OF ss1] by auto
  show "iaction ?\<Delta> s vl s1 vl1 \<or>
        ((vl = [] \<longrightarrow> vl1 = []) \<and> reaction ?\<Delta> s vl s1 vl1)" (is "?iact \<or> (_ \<and> ?react)")
  proof(cases vl1)
    case (Cons v1 vll1) note vl1 = Cons
    obtain pst1 where v1: "v1 = PVal pst1" and lvll1: "list_all isPVal vll1"
      using lvl1 unfolding vl1 by (cases v1) auto
    define uid where "uid \<equiv> owner s PID"  define p where "p \<equiv> pass s uid"
    define a1 where "a1 \<equiv> Uact (uPost uid p PID pst1)"
    have uid1: "uid = owner s1 PID" and p1: "p = pass s1 uid" unfolding uid_def p_def
    using eqButPID_stateSelectors[OF ss1] by auto
    obtain ou1 s1' where step1: "step s1 a1 = (ou1, s1')" by(cases "step s1 a1") auto
    have ou1: "ou1 = outOK" using step1 PID1 own1 unfolding a1_def uid1 p1 by (auto simp: u_defs)
    have uid: "uid \<notin> UIDs" unfolding uid_def using rsT reachNT_state own PID by blast
    let ?trn1 = "Trans s1 a1 ou1 s1'"
    have ?iact proof
      show "step s1 a1 = (ou1, s1')" using step1 .
    next
      show \<phi>1: "\<phi> ?trn1" unfolding \<phi>_def2(* [OF step1] *) a1_def ou1 by simp
      show "consume ?trn1 vl1 vll1"
      using \<phi>1 unfolding vl1 consume_def a1_def v1 by simp
      show "\<not> \<gamma> ?trn1" using uid unfolding a1_def by simp
    next
      have "eqButPID s1 s1'" using Uact_uPaperC_step_eqButPID[OF _ step1] a1_def by auto
      hence ss1': "eqButPID s s1'" using eqButPID_trans ss1 by blast
      show "\<Delta>2 s vl s1' vll1"
      using PID ss1' lvll1 unfolding \<Delta>2_def vl by auto
    qed
    thus ?thesis by simp
  next
    case Nil note vl1 = Nil
    have ?react proof
      fix a :: act and ou :: out and s' :: state and vl'
      let ?trn = "Trans s a ou s'"
      assume step: "step s a = (ou, s')" and T: "\<not> T ?trn" and c: "consume ?trn vl vl'"
      obtain ou1 s1' where step1: "step s1 a = (ou1, s1')" by fastforce
      let ?trn1 = "Trans s1 a ou1 s1'"
      have s's1': "eqButPID s' s1'" using eqButPID_step ss1 step step1 by blast
      have \<gamma>\<gamma>1: "\<gamma> ?trn \<longleftrightarrow> \<gamma> ?trn1" by simp
      have PID': "PID \<in>\<in> postIDs s'" using step rs PID using reach_postIDs_persist by blast
      have \<phi>: "\<not> \<phi> ?trn" and vl': "vl' = vl" using c unfolding vl consume_def by auto
      hence \<phi>1: "\<not> \<phi> ?trn1" using eqButPID_step_\<phi> step ss1 step1 by auto
      show "match ?\<Delta> s s1 vl1 a ou s' vl' \<or> ignore ?\<Delta> s s1 vl1 a ou s' vl'" (is "?match \<or> ?ignore")
      proof-
        have ?match proof
          show "validTrans ?trn1" using step1 by auto
          show "consume ?trn1 vl1 vl1" using \<phi>1 unfolding consume_def by simp
          show "\<gamma> ?trn \<longleftrightarrow> \<gamma> ?trn1" by fact
        next
          assume "\<gamma> ?trn" note \<gamma> = this
          have ou: "(\<exists> uid p aid pid. a = COMact (comSendPost uid p aid pid) \<and> outPurge ou = outPurge ou1) \<or>
                                        ou = ou1"
          using eqButPID_step_\<gamma>_out[OF ss1 step step1 rsT T rs1 \<gamma>] .
          thus "g ?trn = g ?trn1" by (cases a) auto
        next
          have 2[simp]: "textPost (post s1' PID)  = textPost (post s1 PID)"
            using step1 PID1 \<phi>1 unfolding \<phi>_def2(* [OF step1] *)
            apply(cases a)
            subgoal for x1 apply(cases x1, auto simp: all_defs) .
            subgoal for x2 apply(cases x2, auto simp: all_defs) .
            subgoal for x3 apply(cases x3, auto simp: all_defs) .
            subgoal for x4 apply(cases x4, auto simp: all_defs) .
            subgoal by auto
            subgoal by auto
            subgoal for x7 apply(cases x7, auto simp: all_defs) .
            done
          show "\<Delta>2 s' vl' s1' vl1" using PID' s's1' vl
          unfolding \<Delta>2_def vl1 vl' by auto
        qed
        thus ?thesis by simp
      qed
    qed
  thus ?thesis using vl1 by simp
  qed
qed

definition Gr where
"Gr =
 {
 (\<Delta>0, {\<Delta>0,\<Delta>1}),
 (\<Delta>1, {\<Delta>1,\<Delta>2}),
 (\<Delta>2, {\<Delta>2})
 }"


theorem Post_secure: secure
apply (rule unwind_decomp_secure_graph[of Gr \<Delta>0])
unfolding Gr_def
apply (simp, smt insert_subset order_refl)
using istate_\<Delta>0 unwind_cont_\<Delta>0 unwind_cont_\<Delta>1 unwind_cont_\<Delta>2
unfolding Gr_def by auto



end (* context Post_ISSUER *)

end
