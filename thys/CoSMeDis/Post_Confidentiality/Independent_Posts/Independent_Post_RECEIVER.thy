theory Independent_Post_RECEIVER
  imports
    "Independent_Post_Observation_Setup_RECEIVER"
    "Independent_Post_Value_Setup_RECEIVER"
    "Bounded_Deducibility_Security.Compositional_Reasoning"
begin

subsubsection \<open>Receiver declassification bound\<close>

context Post_RECEIVER
begin


fun T :: "(state,act,out) trans \<Rightarrow> bool" where
"T (Trans s a ou s') \<longleftrightarrow>
 (\<exists> uid \<in> UIDs.
   uid \<in>\<in> userIDs s' \<and> PID \<in>\<in> outerPostIDs s' AID \<and>
   (uid = admin s' \<or>
    (AID,outerOwner s' AID PID) \<in>\<in> recvOuterFriendIDs s' uid \<or>
    outerVis s' AID PID = PublicV))"

definition B :: "value list \<Rightarrow> value list \<Rightarrow> bool" where
"B vl vl1 \<equiv> length vl = length vl1"

sublocale BD_Security_IO where
istate = istate and step = step and
\<phi> = \<phi> and f = f and \<gamma> = \<gamma> and g = g and T = T and B = B
done

subsubsection \<open>Receiver unwinding proof\<close>

lemma reach_PublicV_imples_FriendV[simp]:
assumes "reach s"
and "vis s pID \<noteq> PublicV"
shows "vis s pID = FriendV"
using assms reach_vis by auto

lemma reachNT_state:
assumes "reachNT s"
shows
"\<not> (\<exists> uid \<in> UIDs.
   uid \<in>\<in> userIDs s \<and> PID \<in>\<in> outerPostIDs s AID \<and>
   (uid = admin s \<or>
    (AID,outerOwner s AID PID) \<in>\<in> recvOuterFriendIDs s uid \<or>
     outerVis s AID PID = PublicV))"
using assms proof induct
  case (Step trn) thus ?case
  by (cases trn) auto
qed (simp add: istate_def)


(* major *) lemma eqButPID_step_\<gamma>_out:
assumes ss1: "eqButPID s s1"
and step: "step s a = (ou,s')" and step1: "step s1 a = (ou1,s1')"
and sT: "reachNT s" and T: "\<not> T (Trans s a ou s')"
and s1: "reach s1"
and \<gamma>: "\<gamma> (Trans s a ou s')"
shows "ou = ou1"
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
      case (rOPost uid p aid pid)
      with Ract willUse show ?thesis by (cases "aid = AID \<and> pid = PID") auto
    qed auto
  next
    case (Lact x6)
    with willUse show ?thesis by (cases x6) auto
  next
    case (COMact x7)
    with willUse show ?thesis by (cases x7) auto
  qed
qed


definition \<Delta>0 :: "state \<Rightarrow> value list \<Rightarrow> state \<Rightarrow> value list \<Rightarrow> bool" where
"\<Delta>0 s vl s1 vl1 \<equiv>
 \<not> AID \<in>\<in> serverApiIDs s \<and>
 s = s1 \<and>
 length vl = length vl1"

definition \<Delta>1 :: "state \<Rightarrow> value list \<Rightarrow> state \<Rightarrow> value list \<Rightarrow> bool" where
"\<Delta>1 s vl s1 vl1 \<equiv>
 AID \<in>\<in> serverApiIDs s \<and>
 eqButPID s s1 \<and>
 length vl = length vl1"

lemma istate_\<Delta>0:
assumes B: "B vl vl1"
shows "\<Delta>0 istate vl istate vl1"
using assms unfolding \<Delta>0_def B_def istate_def by auto

lemma unwind_cont_\<Delta>0: "unwind_cont \<Delta>0 {\<Delta>0,\<Delta>1}"
proof(rule, simp)
  let ?\<Delta> = "\<lambda>s vl s1 vl1. \<Delta>0 s vl s1 vl1 \<or> \<Delta>1 s vl s1 vl1"
  fix s s1 :: state and vl vl1 :: "value list"
  assume rsT: "reachNT s" and rs1: "reach s1" and "\<Delta>0 s vl s1 vl1"
  hence rs: "reach s" and ss1: "s1 = s" and l: "length vl = length vl1"
  and AID: "\<not> AID \<in>\<in> serverApiIDs s"
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
        have \<phi>: "\<not> \<phi> ?trn" using AID step unfolding \<phi>_def2(* [OF step] *) by (auto simp: u_defs com_defs)
        hence vl': "vl' = vl" using c \<phi> unfolding consume_def by simp
        have ?match proof(cases "\<exists> p. a = COMact (comConnectServer AID p) \<and> ou = outOK")
          case True
          then obtain p where a: "a = COMact (comConnectServer AID p)" and ou: "ou = outOK" by auto
          have AID': "AID \<in>\<in> serverApiIDs s'"
          using step AID unfolding a ou by (auto simp: com_defs)
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
            have "\<Delta>1 s' vl' s' vl1" using l AID' c unfolding ss1 \<Delta>1_def vl' by auto
            thus "?\<Delta> s' vl' s' vl1" by simp
          qed
        next
          case False note a = False
          have AID': "\<not> AID \<in>\<in> serverApiIDs s'"
            using step AID a
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
            have "\<Delta>0 s' vl' s' vl1" using a AID' l unfolding \<Delta>0_def vl' ss1 by simp
            thus "?\<Delta> s' vl' s' vl1" by simp
          qed
        qed
        thus ?thesis by simp
      qed
    qed
  thus ?thesis using l by auto
  qed
qed

lemma unwind_cont_\<Delta>1: "unwind_cont \<Delta>1 {\<Delta>1}"
proof(rule, simp)
  let ?\<Delta> = "\<lambda>s vl s1 vl1. \<Delta>1 s vl s1 vl1"
  fix s s1 :: state and vl vl1 :: "value list"
  assume rsT: "reachNT s" and rs1: "reach s1" and "\<Delta>1 s vl s1 vl1"
  hence rs: "reach s" and ss1: "eqButPID s s1"
  and l: "length vl = length vl1" and AID: "AID \<in>\<in> serverApiIDs s"
  using reachNT_reach unfolding \<Delta>1_def by auto
  have AID1: "AID \<in>\<in> serverApiIDs s1" using eqButPID_stateSelectors[OF ss1] AID by auto

  show "iaction ?\<Delta> s vl s1 vl1 \<or>
        ((vl = [] \<longrightarrow> vl1 = []) \<and> reaction ?\<Delta> s vl s1 vl1)" (is "?iact \<or> (_ \<and> ?react)")
  proof-
    have ?react proof
      fix a :: act and ou :: out and s' :: state and vl'
      let ?trn = "Trans s a ou s'"
      assume step: "step s a = (ou, s')" and T: "\<not> T ?trn" and c: "consume ?trn vl vl'"
      show "match ?\<Delta> s s1 vl1 a ou s' vl' \<or> ignore ?\<Delta> s s1 vl1 a ou s' vl'" (is "?match \<or> ?ignore")
      proof-
        have ?match proof(cases "\<exists> p pst uid vs. a = COMact (comReceivePost AID p PID pst uid vs) \<and> ou = outOK")
          case True
          then obtain p pst uid vs where
          a: "a = COMact (comReceivePost AID p PID pst uid vs)" and ou: "ou = outOK" by auto
          have p: "p = serverPass s AID" using comReceivePost_out[OF step a ou] .
          have p1: "p = serverPass s1 AID" using p ss1 eqButPID_stateSelectors by auto
          have \<phi>: "\<phi> ?trn" using a ou step \<phi>_def2 by auto
          obtain v where vl: "vl = v # vl'" and f: "f ?trn = v"
          using c \<phi> unfolding consume_def by (cases vl) auto
          have AID': "AID \<in>\<in> serverApiIDs s'" using step AID unfolding a ou by (auto simp: com_defs)
          note uid = reachNT_state[OF rsT]
          obtain v1 vl1' where vl1: "vl1 = v1 # vl1'" using l unfolding vl by (cases vl1) auto
          obtain pst1 where v1: "v1 = PValR pst1" by (cases v1) auto
          define a1 where a1: "a1 \<equiv> COMact (comReceivePost AID p PID pst1 uid vs)"
          obtain s1' where step1: "step s1 a1 = (outOK, s1')" using AID1 unfolding a1 p1 by (simp add: com_defs)
          have s's1': "eqButPID s' s1'" using comReceivePost_step_eqButPID[OF a _ step step1 ss1] a1 by simp
          let ?trn1 = "Trans s1 a1 outOK s1'"
          have \<phi>1: "\<phi> ?trn1" unfolding \<phi>_def2(* [OF step1] *) unfolding a1 by auto
          have f1: "f ?trn1 = v1" unfolding a1 v1 by simp
          show ?thesis proof
            show "validTrans ?trn1" using step1 by simp
          next
            show "consume ?trn1 vl1 vl1'" using \<phi>1 f1 unfolding consume_def ss1 vl1 by simp
          next
            show "\<gamma> ?trn = \<gamma> ?trn1" unfolding a a1 by simp
          next
            assume "\<gamma> ?trn" thus "g ?trn = g ?trn1" unfolding a a1 ou by simp
          next
            show "\<Delta>1 s' vl' s1' vl1'" using l AID' c s's1' unfolding \<Delta>1_def vl vl1 by simp
          qed
        next
          case False note a = False
          obtain s1' ou1 where step1: "step s1 a = (ou1, s1')" by fastforce
          let ?trn1 = "Trans s1 a ou1 s1'"
          have \<phi>: "\<not> \<phi> ?trn" using a step \<phi>_def2 by auto
          have \<phi>1: "\<not> \<phi> ?trn1" using \<phi> ss1 step step1 eqButPID_step_\<phi> by blast
          have s's1': "eqButPID s' s1'" using ss1 step step1 eqButPID_step by blast
          have ouou1: "\<gamma> ?trn \<Longrightarrow> ou = ou1" using eqButPID_step_\<gamma>_out ss1 step step1 T rs1 rsT by blast
          have AID': "AID \<in>\<in> serverApiIDs s'" using AID step rs using IDs_mono by auto
          have vl': "vl' = vl" using c \<phi> unfolding consume_def by simp
          show ?thesis proof
            show "validTrans ?trn1" using step1 by simp
          next
            show "consume ?trn1 vl1 vl1" using \<phi>1 unfolding consume_def ss1 by auto
          next
            show 1: "\<gamma> ?trn = \<gamma> ?trn1" unfolding ss1 by simp
          next
            assume "\<gamma> ?trn" hence "ou = ou1" using ouou1 by auto
            thus "g ?trn = g ?trn1" using ouou1 by (cases a) auto
          next
            show "\<Delta>1 s' vl' s1' vl1" using a l s's1' AID' unfolding \<Delta>1_def vl' by simp
          qed
        qed
        thus ?thesis by simp
      qed
    qed
  thus ?thesis using l by auto
  qed
qed

definition Gr where
"Gr =
 {
 (\<Delta>0, {\<Delta>0,\<Delta>1}),
 (\<Delta>1, {\<Delta>1})
 }"


theorem Post_secure: secure
apply (rule unwind_decomp_secure_graph[of Gr \<Delta>0])
unfolding Gr_def
apply (simp, smt insert_subset order_refl)
using istate_\<Delta>0 unwind_cont_\<Delta>0 unwind_cont_\<Delta>1
unfolding Gr_def by auto


end (* context Post_RECEIVER *)

end
