theory Independent_DYNAMIC_Post_ISSUER
  imports
    "Independent_Post_Observation_Setup_ISSUER"
    "Independent_DYNAMIC_Post_Value_Setup_ISSUER"
    "Bounded_Deducibility_Security.Compositional_Reasoning"
begin


subsubsection \<open>Issuer declassification bound\<close>

(* We verify that a group of users,
   allowed to take normal actions to the system and observe their outputs
   *and additionally allowed to observe communication*,
   learn nothing about the updates to a post and the sends of that post to other APIs
   beyond:
(1) the updates that occur during the times when:
     -- either a user in the group is the post's owner
     -- or a user in the group is a friend of the owner
     -- or the group has at least one registered user and the post is marked "public"
(2) the presence of the sends (i.e., the number of the sending actions)
(3) and the public knowledge that what is being sent is always the last version (modeled as
the correlation predicate)
*)

context Post
begin

fun T :: "(state,act,out) trans \<Rightarrow> bool" where "T _ = False"

text \<open>We again use the dynamic declassification bound for the issuer node
(Section~\ref{sec:dynamic-post-issuer}).\<close>

inductive BC :: "value list \<Rightarrow> value list \<Rightarrow> bool"
and BO :: "value list \<Rightarrow> value list \<Rightarrow> bool"
where
 BC_PVal[simp,intro!]:
  "list_all (Not o isOVal) ul \<Longrightarrow> list_all (Not o isOVal) ul1 \<Longrightarrow>
   map tgtAPI (filter isPValS ul) = map tgtAPI (filter isPValS ul1) \<Longrightarrow>
   (ul = [] \<longrightarrow> ul1 = [])
   \<Longrightarrow> BC ul ul1"
|BC_BO[intro]:
  "BO vl vl1 \<Longrightarrow>
   list_all (Not o isOVal) ul \<Longrightarrow> list_all (Not o isOVal) ul1 \<Longrightarrow>
   map tgtAPI (filter isPValS ul) = map tgtAPI (filter isPValS ul1) \<Longrightarrow>
   (ul = [] \<longleftrightarrow> ul1 = []) \<Longrightarrow>
   (ul \<noteq> [] \<Longrightarrow> isPVal (last ul) \<and> last ul = last ul1) \<Longrightarrow>
   list_all isPValS sul
   \<Longrightarrow>
   BC (ul  @ sul @ OVal True # vl)
      (ul1 @ sul @ OVal True # vl1)"
(*  *)
|BO_PVal[simp,intro!]:
  "list_all (Not o isOVal) ul \<Longrightarrow> BO ul ul"
|BO_BC[intro]:
  "BC vl vl1 \<Longrightarrow>
   list_all (Not o isOVal) ul
   \<Longrightarrow>
   BO (ul @ OVal False # vl) (ul @ OVal False # vl1)"

lemma list_all_filter_Not_isOVal:
assumes "list_all (Not \<circ> isOVal) ul"
and "filter isPValS ul = []" and "filter isPVal ul = []"
shows "ul = []"
using assms value.exhaust_disc by (induct ul) auto

lemma BC_not_Nil: "BC vl vl1 \<Longrightarrow> vl = [] \<Longrightarrow> vl1 = []"
by(auto elim: BC.cases)

lemma BC_OVal_True:
assumes "BC (OVal True # vl') vl1"
shows "\<exists> vl1'. BO vl' vl1' \<and> vl1 = OVal True # vl1'"
proof-
  define vl where vl: "vl \<equiv> OVal True # vl'"
  have "BC vl vl1" using assms unfolding vl by auto
  thus ?thesis proof cases
    case (BC_BO vll vll1 ul ul1 sul)
    hence ul: "ul = []" unfolding vl apply simp
    by (metis (no_types) Post.value.disc(9) append_eq_Cons_conv
         list.map(2) list.pred_inject(2) list_all_map)
    have sul: "sul = []" using BC_BO unfolding vl ul apply simp
    by (metis Post.value.disc(6) append_eq_Cons_conv list.pred_inject(2))
    show ?thesis
    apply - apply(rule exI[of _ "vll1"])
    using BC_BO using list_all_filter_Not_isOVal[of ul1]
    unfolding ul sul vl by auto
  qed(unfold vl, auto)
qed

(* Correlation is defined to mean: always send what was last uploaded, or emptyPost
if nothing had been uploaded. This needs the auxiliary notion of "coherence from" *)
fun corrFrom :: "post \<Rightarrow> value list \<Rightarrow> bool" where
 "corrFrom pst [] = True"
|"corrFrom pst (PVal pstt # vl) = corrFrom pstt vl"
|"corrFrom pst (PValS aid pstt # vl) = (pst = pstt \<and> corrFrom pst vl)"
|"corrFrom pst (OVal b # vl) = (corrFrom pst vl)"


abbreviation corr :: "value list \<Rightarrow> bool" where "corr \<equiv> corrFrom emptyPost"

definition B where
"B vl vl1 \<equiv> BC vl vl1 \<and> corr vl1"

(* lemma vl_Nil_filter_not:
assumes "filter (%v. isPVal v \<or> isOVal v) Vl = [] \<and> filter (Not o isPVal) Vl = []"
shows "Vl = []"
using assms by (induct Vl) auto *)

lemma B_not_Nil:
assumes B: "B vl vl1" and vl: "vl = []"
shows "vl1 = []"
using B Post.BC_not_Nil Post.B_def vl by blast


sublocale BD_Security_IO where
istate = istate and step = step and
\<phi> = \<phi> and f = f and \<gamma> = \<gamma> and g = g and T = T and B = B
done

subsubsection \<open>Issuer unwinding proof\<close>

lemma reach_PublicV_imples_FriendV[simp]:
assumes "reach s"
and "vis s pid \<noteq> PublicV"
shows "vis s pid = FriendV"
using assms reach_vis by auto


(* major *) lemma eqButPID_step_\<gamma>_out:
assumes ss1: "eqButPID s s1"
and step: "step s a = (ou,s')" and step1: "step s1 a = (ou1,s1')"
and op: "\<not> open s"
and sT: "reachNT s" and s1: "reach s1"
and \<gamma>: "\<gamma> (Trans s a ou s')"
shows "(\<exists> uid p aid pid. a = COMact (comSendPost uid p aid pid) \<and> outPurge ou = outPurge ou1) \<or>
       ou = ou1"
proof-
  note [simp] = all_defs
                open_def
  note s = reachNT_reach[OF sT]
  note willUse =
  step step1 \<gamma>
  not_open_eqButPID[OF op ss1]
  reach_vis[OF s]
  eqButPID_stateSelectors[OF ss1] (* eqButPID_postSelectors[OF ss1]  *)
  eqButPID_actions[OF ss1]
  eqButPID_update[OF ss1] (* eqButPID_setTextPost[OF ss1] *) eqButPID_not_PID[OF ss1]
(* added to cope with extra leak towards the admin, when moving from CoSMed to CoSMeDis: *)
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
 \<not> PID \<in>\<in> postIDs s \<and>
 s = s1 \<and> BC vl vl1 \<and>
 corr vl1"

definition \<Delta>1 :: "state \<Rightarrow> value list \<Rightarrow> state \<Rightarrow> value list \<Rightarrow> bool" where
"\<Delta>1 s vl s1 vl1 \<equiv>
 PID \<in>\<in> postIDs s \<and>
 list_all (Not o isOVal) vl \<and> list_all (Not o isOVal) vl1 \<and>
 map tgtAPI (filter isPValS vl) = map tgtAPI (filter isPValS vl1) \<and>
 (vl = [] \<longrightarrow> vl1 = []) \<and>
 eqButPID s s1 \<and> \<not> open s \<and>
 corrFrom (post s1 PID) vl1"

definition \<Delta>11 :: "state \<Rightarrow> value list \<Rightarrow> state \<Rightarrow> value list \<Rightarrow> bool" where
"\<Delta>11 s vl s1 vl1 \<equiv>
 PID \<in>\<in> postIDs s \<and>
 vl = [] \<and> list_all isPVal vl1 \<and>
 eqButPID s s1 \<and> \<not> open s \<and>
 corrFrom (post s1 PID) vl1"

definition \<Delta>2 :: "state \<Rightarrow> value list \<Rightarrow> state \<Rightarrow> value list \<Rightarrow> bool" where
"\<Delta>2 s vl s1 vl1 \<equiv>
 PID \<in>\<in> postIDs s \<and>
 list_all (Not o isOVal) vl \<and>
 vl = vl1 \<and>
 s = s1 \<and> open s \<and>
 corrFrom (post s1 PID) vl1"

definition \<Delta>31 :: "state \<Rightarrow> value list \<Rightarrow> state \<Rightarrow> value list \<Rightarrow> bool" where
"\<Delta>31 s vl s1 vl1 \<equiv>
 PID \<in>\<in> postIDs s \<and>
 (\<exists> ul ul1 sul vll vll1.
    BO vll vll1 \<and>
    list_all (Not o isOVal) ul \<and> list_all (Not o isOVal) ul1 \<and>
    map tgtAPI (filter isPValS ul) = map tgtAPI (filter isPValS ul1) \<and>
    ul \<noteq> [] \<and> ul1 \<noteq> [] \<and>
    isPVal (last ul) \<and> last ul = last ul1 \<and>
    list_all isPValS sul \<and>
    vl = ul @ sul @ OVal True # vll \<and> vl1 = ul1 @ sul @ OVal True # vll1) \<and>
 eqButPID s s1 \<and> \<not> open s \<and>
 corrFrom (post s1 PID) vl1"

definition \<Delta>32 :: "state \<Rightarrow> value list \<Rightarrow> state \<Rightarrow> value list \<Rightarrow> bool" where
"\<Delta>32 s vl s1 vl1 \<equiv>
 PID \<in>\<in> postIDs s \<and>
 (\<exists> sul vll vll1.
    BO vll vll1 \<and>
    list_all isPValS sul \<and>
    vl = sul @ OVal True # vll \<and> vl1 = sul @ OVal True # vll1) \<and>
 s = s1 \<and> \<not> open s \<and>
 corrFrom (post s1 PID) vl1"

definition \<Delta>4 :: "state \<Rightarrow> value list \<Rightarrow> state \<Rightarrow> value list \<Rightarrow> bool" where
"\<Delta>4 s vl s1 vl1 \<equiv>
 PID \<in>\<in> postIDs s \<and>
 (\<exists> ul vll vll1.
    BC vll vll1 \<and>
    list_all (Not o isOVal) ul \<and>
    vl = ul @ OVal False # vll \<and> vl1 = ul @ OVal False # vll1) \<and>
 s = s1 \<and> open s \<and>
 corrFrom (post s1 PID) vl1"

lemma istate_\<Delta>0:
assumes B: "B vl vl1"
shows "\<Delta>0 istate vl istate vl1"
using assms unfolding \<Delta>0_def istate_def B_def by auto
(* by (auto simp: list_all_isOVal_filter_isPValS)
(auto intro!: exI[of _ "[]"]) *)

lemma list_all_filter[simp]:
assumes "list_all PP xs"
shows "filter PP xs = xs"
using assms by (induct xs) auto

lemma unwind_cont_\<Delta>0: "unwind_cont \<Delta>0 {\<Delta>0,\<Delta>1,\<Delta>2,\<Delta>31,\<Delta>32,\<Delta>4}"
proof(rule, simp)
  let ?\<Delta> = "\<lambda>s vl s1 vl1. \<Delta>0 s vl s1 vl1 \<or>
                           \<Delta>1 s vl s1 vl1 \<or> \<Delta>2 s vl s1 vl1 \<or>
                           \<Delta>31 s vl s1 vl1 \<or> \<Delta>32 s vl s1 vl1 \<or> \<Delta>4 s vl s1 vl1"
  fix s s1 :: state and vl vl1 :: "value list"
  assume rsT: "reachNT s" and rs1: "reach s1" and "\<Delta>0 s vl s1 vl1"
  hence rs: "reach s" and ss1: "s1 = s" and BC: "BC vl vl1" and PID: "\<not> PID \<in>\<in> postIDs s"
  and cor1: "corr vl1" using reachNT_reach unfolding \<Delta>0_def by auto
  have vis: "vis s PID = FriendV" using reach_not_postIDs_friendV[OF rs PID] .
  have pPID: "post s1 PID = emptyPost" by (simp add: PID reach_not_postIDs_emptyPost rs ss1)
  have vlvl1: "vl = [] \<Longrightarrow> vl1 = []" using BC_not_Nil BC by auto
  have op: "\<not> open s" using PID unfolding open_def by auto
  show "iaction ?\<Delta> s vl s1 vl1 \<or>
        ((vl = [] \<longrightarrow> vl1 = []) \<and> reaction ?\<Delta> s vl s1 vl1)" (is "?iact \<or> (_ \<and> ?react)")
  proof-
    have ?react proof
      fix a :: act and ou :: out and s' :: state and vl'
      let ?trn = "Trans s a ou s'"  let ?trn1 = "Trans s1 a ou s'"
      assume step: "step s a = (ou, s')" and T: "\<not> T ?trn" and c: "consume ?trn vl vl'"
      hence pPID': "post s' PID = emptyPost" using step pPID ss1 PID
        apply (cases a)
        subgoal for x1 apply(cases x1) apply(fastforce simp: s_defs)+ .
        subgoal for x2 apply(cases x2) apply(fastforce simp: c_defs)+ .
        subgoal for x3 apply(cases x3) apply(fastforce simp: d_defs)+ .
        subgoal for x4 apply(cases x4) apply(fastforce simp: u_defs)+ .
        subgoal by auto
        subgoal by auto
        subgoal for x7 apply(cases x7) apply(fastforce simp: com_defs)+ .
        done
      show "match ?\<Delta> s s1 vl1 a ou s' vl' \<or> ignore ?\<Delta> s s1 vl1 a ou s' vl'" (is "?match \<or> ?ignore")
      proof-
        have ?match
        proof(cases "\<exists> uid p. a = Cact (cPost uid p PID) \<and> ou = outOK")
          case True
          then obtain uid p where a: "a = Cact (cPost uid p PID)" and ou: "ou = outOK" by auto
          have PID': "PID \<in>\<in> postIDs s'"
          using step PID unfolding a ou by (auto simp: c_defs)
          show ?thesis proof(cases
             "\<exists> uid' \<in> UIDs. uid' \<in>\<in> userIDs s \<and>
                             (uid' = admin s \<or> uid' = uid \<or> uid' \<in>\<in> friendIDs s uid)")
            case True note uid = True
            have op': "open s'" using uid using step PID' unfolding a ou by (auto simp: c_defs open_def)
            have \<phi>: "\<phi> ?trn" using op op' unfolding \<phi>_def2[OF step] by simp
            then obtain v where vl: "vl = v # vl'" and f: "f ?trn = v"
            using c unfolding consume_def \<phi>_def2 by(cases vl) auto
            have v: "v = OVal True" using f op op' unfolding a by simp
            then obtain ul1 vl1' where BO': "BO vl' vl1'" and vl1: "vl1 = ul1 @ OVal True # vl1'"
            and ul1: "list_all (Not \<circ> isOVal) ul1"
            using BC_OVal_True[OF BC[unfolded vl v]] by auto
            have ul1: "ul1 = []"
              using BC BC_OVal_True list_all_Not_isOVal_OVal_True ul1 v vl vl1 by blast
            hence vl1: "vl1 = OVal True # vl1'" using vl1 by simp
            show ?thesis proof
              show "validTrans ?trn1" unfolding ss1 using step by simp
            next
              show "consume ?trn1 vl1 vl1'" using \<phi> f unfolding vl1 v consume_def ss1 by simp
            next
              show "\<gamma> ?trn = \<gamma> ?trn1" unfolding ss1 by simp
            next
              assume "\<gamma> ?trn" thus "g ?trn = g ?trn1" unfolding ss1 by simp
            next
              show "?\<Delta> s' vl' s' vl1'" using BO' proof(cases rule: BO.cases)
                case (BO_PVal)
                hence "\<Delta>2 s' vl' s' vl1'" using PID' op' cor1 unfolding \<Delta>2_def vl1 pPID' by auto
                thus ?thesis by simp
              next
                case (BO_BC vll vll1 textl)
                hence "\<Delta>4 s' vl' s' vl1'" using PID' op' cor1 unfolding \<Delta>4_def vl1 pPID' by auto
                thus ?thesis by simp
              qed
            qed
          next
            case False note uid = False
            have op': "\<not> open s'" using step op uid vis unfolding open_def a by (auto simp: c_defs)
            have \<phi>: "\<not> \<phi> ?trn" using op op' a unfolding \<phi>_def2[OF step] by auto
            hence vl': "vl' = vl" using c unfolding consume_def by simp
            show ?thesis proof
              show "validTrans ?trn1" unfolding ss1 using step by simp
            next
              show "consume ?trn1 vl1 vl1" using \<phi> unfolding consume_def ss1 by auto
            next
              show "\<gamma> ?trn = \<gamma> ?trn1" unfolding ss1 by simp
            next
              assume "\<gamma> ?trn" thus "g ?trn = g ?trn1" unfolding ss1 by simp
            next
              show "?\<Delta> s' vl' s' vl1" using BC proof(cases rule: BC.cases)
                case (BC_PVal)
                hence "\<Delta>1 s' vl' s' vl1" using PID' op' cor1 unfolding \<Delta>1_def vl' pPID' by auto
                thus ?thesis by simp
              next
                case (BC_BO vll vll1 ul ul1 sul)
                show ?thesis
                proof(cases "ul \<noteq> [] \<and> ul1 \<noteq> []")
                  case True
                  hence "\<Delta>31 s' vl' s' vl1" using BC_BO PID' op' cor1
                  unfolding \<Delta>31_def vl' pPID' apply auto
                  apply (rule exI[of _ "ul"]) apply (rule exI[of _ "ul1"])
                  apply (rule exI[of _ "sul"])
                  apply (rule exI[of _ "vll"]) apply (rule exI[of _ "vll1"])
                  by auto
                  thus ?thesis by simp
                next
                  case False
                  hence 0: "ul = [] \<and> ul1 = []" using BC_BO by simp
                  hence 1: "list_all isPValS ul \<and> list_all isPValS ul1"
                  using \<open>list_all (Not \<circ> isOVal) ul\<close> \<open>list_all (Not \<circ> isOVal) ul1\<close>
                  using filter_list_all_isPValS_isOVal by auto
                  (* have "map tgtAPI ul = map tgtAPI ul1" using 1BC_BO by auto *)
                  have "\<Delta>32 s' vl' s' vl1" using BC_BO PID' op' cor1 0 1
                  unfolding \<Delta>32_def vl' pPID' apply simp
                  apply(rule exI[of _ "sul"])
                  apply(rule exI[of _ vll]) apply(rule exI[of _ vll1])
                  by auto
                  thus ?thesis by simp
                qed
              qed
            qed
          qed
        next
          case False note a = False
          have op': "\<not> open s'"
            using a step PID op unfolding open_def
            apply(cases a)
            subgoal for x1 apply(cases x1) apply(fastforce simp: s_defs)+ .
            subgoal for x2 apply(cases x2) apply(fastforce simp: c_defs)+ .
            subgoal for x3 apply(cases x3) apply(fastforce simp: d_defs)+ .
            subgoal for x4 apply(cases x4) apply(fastforce simp: u_defs)+ .
            subgoal by auto
            subgoal by auto
            subgoal for x7 apply(cases x7) apply(fastforce simp: com_defs)+ .
            done
          have \<phi>: "\<not> \<phi> ?trn" using PID step op op' unfolding \<phi>_def2[OF step]
          by (auto simp: u_defs com_defs)
          hence vl': "vl' = vl" using c unfolding consume_def by simp
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
            have "\<Delta>0 s' vl' s' vl1" using a BC PID' cor1 unfolding \<Delta>0_def vl' by simp
            thus "?\<Delta> s' vl' s' vl1" by simp
          qed
        qed
        thus ?thesis by simp
      qed
    qed
  thus ?thesis using vlvl1 by simp
  qed
qed

lemma unwind_cont_\<Delta>1: "unwind_cont \<Delta>1 {\<Delta>1,\<Delta>11}"
proof(rule, simp)
  let ?\<Delta> = "\<lambda>s vl s1 vl1. \<Delta>1 s vl s1 vl1 \<or> \<Delta>11 s vl s1 vl1"
  fix s s1 :: state and vl vl1 :: "value list"
  assume rsT: "reachNT s" and rs1: "reach s1" and "\<Delta>1 s vl s1 vl1"
  then obtain
  lvl: "list_all (Not \<circ> isOVal) vl" and lvl1: "list_all (Not \<circ> isOVal) vl1"
  and map: "map tgtAPI (filter isPValS vl) = map tgtAPI (filter isPValS vl1)"
  and rs: "reach s" and ss1: "eqButPID s s1" and op: "\<not> open s" and PID: "PID \<in>\<in> postIDs s"
  and vlvl1: "vl = [] \<Longrightarrow> vl1 = []" and cor1: "corrFrom (post s1 PID) vl1"
  using reachNT_reach unfolding \<Delta>1_def by auto
  have PID1: "PID \<in>\<in> postIDs s1" using eqButPID_stateSelectors[OF ss1] PID by auto
  have own: "owner s PID \<in> set (userIDs s)" using reach_owner_userIDs[OF rs PID] .
  hence own1: "owner s1 PID \<in> set (userIDs s1)" using eqButPID_stateSelectors[OF ss1] by auto
  have adm: "admin s \<in> set (userIDs s)" using reach_admin_userIDs[OF rs own] .
  hence adm1: "admin s1 \<in> set (userIDs s1)" using eqButPID_stateSelectors[OF ss1] by auto
  have op1: "\<not> open s1" using op ss1 eqButPID_open by auto
  show "iaction ?\<Delta> s vl s1 vl1 \<or>
        ((vl = [] \<longrightarrow> vl1 = []) \<and> reaction ?\<Delta> s vl s1 vl1)" (is "?iact \<or> (_ \<and> ?react)")
  proof(cases vl1)
    case (Cons v1 vll1) note vl1 = Cons
    show ?thesis proof(cases v1)
      case (PVal pst1) note v1 = PVal
      define uid where uid: "uid \<equiv> owner s PID"  define p where p: "p \<equiv> pass s uid"
      define a1 where a1: "a1 \<equiv> Uact (uPost uid p PID pst1)"
      have uid1: "uid = owner s1 PID" and p1: "p = pass s1 uid" unfolding uid p
      using eqButPID_stateSelectors[OF ss1] by auto
      obtain ou1 s1' where step1: "step s1 a1 = (ou1, s1')" by(cases "step s1 a1") auto
      have ou1: "ou1 = outOK" using step1 PID1 own1 unfolding a1 uid1 p1 by (auto simp: u_defs)
      have op1': "\<not> open s1'" using step1 op1 unfolding a1 ou1 open_def by (auto simp: u_defs)
      have uid: "uid \<notin> UIDs" unfolding uid using op PID own unfolding open_def by auto
      have pPID1': "post s1' PID = pst1" using step1 unfolding a1 ou1 by (auto simp: u_defs)
      let ?trn1 = "Trans s1 a1 ou1 s1'"
      have ?iact proof
        show "step s1 a1 = (ou1, s1')" using step1 .
      next
        show \<phi>: "\<phi> ?trn1" unfolding \<phi>_def2[OF step1] a1 ou1 by simp
        show "consume ?trn1 vl1 vll1"
        using \<phi> unfolding vl1 consume_def v1 a1 by auto
      next
        show "\<not> \<gamma> ?trn1" using uid unfolding a1 by auto
      next
        have "eqButPID s1 s1'" using Uact_uPaperC_step_eqButPID[OF _ step1] a1 by auto
        hence ss1': "eqButPID s s1'" using eqButPID_trans ss1 by blast
        show "?\<Delta> s vl s1' vll1" using PID op ss1' lvl lvl1 map vlvl1 cor1
        unfolding \<Delta>1_def vl1 v1 pPID1' by auto
      qed
      thus ?thesis by simp
    next
      case (PValS aid1 pst1) note v1 = PValS
      have pPID1: "post s1 PID = pst1" using cor1 unfolding vl1 v1 by auto
      then obtain v vll where vl: "vl = v # vll"
      using map unfolding vl1 v1 by (cases vl) auto
      have ?react proof
        fix a :: act and ou :: out and s' :: state and vl'
        let ?trn = "Trans s a ou s'"
        assume step: "step s a = (ou, s')" and c: "consume ?trn vl vl'"
        have PID': "PID \<in>\<in> postIDs s'" using reach_postIDs_persist[OF PID step] .
        obtain ou1 s1' where step1: "step s1 a = (ou1, s1')" by(cases "step s1 a") auto
        let ?trn1 = "Trans s1 a ou1 s1'"
        show "match ?\<Delta> s s1 vl1 a ou s' vl' \<or> ignore ?\<Delta> s s1 vl1 a ou s' vl'"
            (is "?match \<or> ?ignore")
        proof(cases "\<phi> ?trn")
          case True note \<phi> = True
          then obtain f: "f ?trn = v" and vl': "vl' = vll"
          using c unfolding vl consume_def \<phi>_def2 by auto
          show ?thesis
          proof(cases v)
            case (PVal pst) note v = PVal
            have vll: "vll \<noteq> []" using map unfolding vl1 v1 vl v by auto
            define uid where uid: "uid \<equiv> owner s PID"  define p where p: "p \<equiv> pass s uid"
            have a: "a = Uact (uPost uid p PID pst)"
            using f_eq_PVal[OF step \<phi> f[unfolded v]] unfolding uid p .
            have "eqButPID s s'" using Uact_uPaperC_step_eqButPID[OF a step] by auto
            hence s's1: "eqButPID s' s1" using eqButPID_sym eqButPID_trans ss1 by blast
            have op': "\<not> open s'" using uPost_comSendPost_open_eq[OF step] a op by auto
            have ?ignore proof
              show \<gamma>: "\<not> \<gamma> ?trn" using step_open_\<phi>_f_PVal_\<gamma>[OF rs step PID op \<phi> f[unfolded v]] .
              show "?\<Delta> s' vl' s1 vl1"
              using lvl1 lvl PID' map s's1 op' vll cor1 unfolding \<Delta>1_def vl1 vl vl' v
              by auto
            qed
            thus ?thesis by simp
          next
            case (PValS aid pst) note v = PValS
            define uid where uid: "uid \<equiv> admin s" define p where p: "p \<equiv> pass s uid"
            have a: "a = COMact (comSendPost (admin s) p aid PID)"
            using f_eq_PValS[OF step \<phi> f[unfolded v]] unfolding uid p .
            have op': "\<not> open s'" using uPost_comSendPost_open_eq[OF step] a op by auto
            have aid1: "aid1 = aid" using map unfolding vl1 v1 vl v by simp
            have uid1: "uid = admin s1" and p1: "p = pass s1 uid" unfolding uid p
            using eqButPID_stateSelectors[OF ss1] by auto
            obtain ou1 s1' where step1: "step s1 a = (ou1, s1')" by(cases "step s1 a") auto
            have pPID1': "post s1' PID = pst1" using pPID1 step1 unfolding a
            by (auto simp: com_defs)
            have uid: "uid \<notin> UIDs" unfolding uid using op PID adm unfolding open_def by auto
            have op1': "\<not> open s1'" using step1 op1 unfolding a open_def
            by (auto simp: u_defs com_defs)
            let ?trn1 = "Trans s1 a ou1 s1'"
            have \<phi>1: "\<phi> ?trn1" using eqButPID_step_\<phi>_imp[OF ss1 step step1 \<phi>] .
            have ou1: "ou1 =
                O_sendPost (aid, clientPass s1 aid, PID, post s1 PID, owner s1 PID, vis s1 PID)"
              using \<phi>1 step1 adm1 PID1 unfolding a by (cases ou1, auto simp: com_defs)
            have f1: "f ?trn1 = v1" using \<phi>1 unfolding \<phi>_def2[OF step1] v1 a ou1 aid1 pPID1 by auto
            have s's1': "eqButPID s' s1'" using eqButPID_step[OF ss1 step step1] .
            have ?match proof
              show "validTrans ?trn1" using step1 by simp
            next
              show "consume ?trn1 vl1 vll1" using \<phi>1 unfolding consume_def vl1 f1 by simp
            next
              show "\<gamma> ?trn = \<gamma> ?trn1" unfolding ss1 by simp
            next
              assume "\<gamma> ?trn" note \<gamma> = this
              have ou: "(\<exists> uid p aid pid.
                       a = COMact (comSendPost uid p aid pid) \<and> outPurge ou = outPurge ou1) \<or>
                                        ou = ou1"
              using eqButPID_step_\<gamma>_out[OF ss1 step step1 op rsT rs1 \<gamma>] .
              thus "g ?trn = g ?trn1" by (cases a) auto
            next
              show "?\<Delta> s' vl' s1' vll1"
              proof(cases "vll = []")
                case True note vll = True
                hence "filter isPValS vll1 = []" using map lvl lvl1 unfolding vl vl1 v v1 by simp
                hence lvl1: "list_all isPVal vll1"
                using filter_list_all_isPVal_isOVal lvl1 unfolding vl1 v1 by auto
                hence "\<Delta>11 s' vl' s1' vll1" using s's1' op1' op' PID' lvl lvl1 map cor1 pPID1 pPID1'
                unfolding \<Delta>11_def vl vl' vl1 v v1 vll by auto
                thus ?thesis by auto
              next
                case False note vll = False
                hence "\<Delta>1 s' vl' s1' vll1" using s's1' op1' op' PID' lvl lvl1 map cor1 pPID1 pPID1'
                unfolding \<Delta>1_def vl vl' vl1 v v1 by auto
                thus ?thesis by auto
              qed
            qed
          thus ?thesis using vl by simp
        qed(insert lvl vl, auto)
      next
        case False note \<phi> = False
        hence vl': "vl' = vl" using c unfolding consume_def by auto
        obtain ou1 s1' where step1: "step s1 a = (ou1, s1')" by(cases "step s1 a") auto
        have s's1': "eqButPID s' s1'" using eqButPID_step[OF ss1 step step1] .
        let ?trn1 = "Trans s1 a ou1 s1'"
        have \<phi>1: "\<not> \<phi> ?trn1" using \<phi> ss1 by (simp add: eqButPID_step_\<phi> step step1)
        have pPID1': "post s1' PID = pst1"
          using PID1 pPID1 step1 \<phi>1 (* unfolding \<phi>_def2[OF step1] *)
          apply(cases a)
          subgoal for x1 apply(cases x1) apply(fastforce simp: s_defs)+ .
          subgoal for x2 apply(cases x2) apply(fastforce simp: c_defs)+ .
          subgoal for x3 apply(cases x3) apply(fastforce simp: d_defs)+ .
          subgoal for x4 apply(cases x4) apply(fastforce simp: u_defs)+ .
          subgoal by auto
          subgoal by auto
          subgoal for x7 apply(cases x7) apply(fastforce simp: com_defs)+ .
          done
        have op': "\<not> open s'"
          using PID step \<phi> op
          unfolding \<phi>_def2[OF step1]
          apply(cases a)
          subgoal for x1 apply(cases x1) apply(fastforce simp: s_defs)+ .
          subgoal by auto
          subgoal by auto
          subgoal for x4 using \<phi>_def2 \<phi> step by blast
          subgoal by auto
          subgoal by auto
          subgoal using \<phi>_def2 \<phi> step by blast
          done
        have ?match proof
          show "validTrans ?trn1" using step1 by simp
        next
          show "consume ?trn1 vl1 vl1" using \<phi>1 unfolding consume_def by simp
        next
          show "\<gamma> ?trn = \<gamma> ?trn1" unfolding ss1 by simp
        next
          assume "\<gamma> ?trn" note \<gamma> = this
          have ou: "(\<exists> uid p aid pid.
                   a = COMact (comSendPost uid p aid pid) \<and> outPurge ou = outPurge ou1) \<or>
                   ou = ou1"
          using eqButPID_step_\<gamma>_out[OF ss1 step step1 op rsT rs1 \<gamma>] .
          thus "g ?trn = g ?trn1" by (cases a) auto
        next
          have "\<Delta>1 s' vl' s1' vl1" using s's1' PID' pPID1 pPID1' lvl lvl1 map cor1 op'
          unfolding \<Delta>1_def vl vl' by auto
          thus "?\<Delta> s' vl' s1' vl1" by simp
        qed
        thus ?thesis by simp
      qed
    qed
    thus ?thesis using vlvl1 by simp
  qed(insert lvl1 vl1, auto)
next
  case Nil note vl1 = Nil
  have ?react proof
    fix a :: act and ou :: out and s' :: state and vl'
    let ?trn = "Trans s a ou s'"
      assume step: "step s a = (ou, s')" and T: "\<not> T ?trn" and c: "consume ?trn vl vl'"
      have PID': "PID \<in>\<in> postIDs s'" using reach_postIDs_persist[OF PID step] .
      obtain ou1 s1' where step1: "step s1 a = (ou1, s1')" by(cases "step s1 a") auto
      let ?trn1 = "Trans s1 a ou1 s1'"
      show "match ?\<Delta> s s1 vl1 a ou s' vl' \<or> ignore ?\<Delta> s s1 vl1 a ou s' vl'" (is "?match \<or> ?ignore")
      proof(cases "\<exists> uid p pstt. a = Uact (uPost uid p PID pstt) \<and> ou = outOK")
        case True then obtain uid p pstt where
        a: "a = Uact (uPost uid p PID pstt)" and ou: "ou = outOK" by auto
        hence \<phi>: "\<phi> ?trn" unfolding \<phi>_def2[OF step] by auto
        then obtain v where vl: "vl = v # vl'" and f: "f ?trn = v"
        using c unfolding consume_def \<phi>_def2 by (cases vl) auto
        obtain pst where v: "v = PVal pst" using map lvl unfolding vl vl1 by (cases v) auto
        have pstt: "pstt = pst" using f unfolding a v by auto
        have uid: "uid \<notin> UIDs" using step op PID unfolding a ou open_def by (auto simp: u_defs)
        have "eqButPID s s'" using Uact_uPaperC_step_eqButPID[OF a step] by auto
        hence s's1: "eqButPID s' s1" using eqButPID_sym eqButPID_trans ss1 by blast
        have op': "\<not> open s'" using step PID' op unfolding a ou open_def by (auto simp: u_defs)
        have ?ignore proof
          show "\<not> \<gamma> ?trn" unfolding a using uid by auto
        next
          show "?\<Delta> s' vl' s1 vl1" using PID' s's1 op' lvl map
          unfolding \<Delta>1_def vl1 vl by auto
        qed
        thus ?thesis by simp
      next
        case False note a = False
        {assume \<phi>: "\<phi> ?trn"
         then obtain v vl' where vl: "vl = v # vl'" and f: "f ?trn = v"
         using c unfolding consume_def by (cases vl) auto
         obtain pst where v: "v = PVal pst" using map lvl unfolding vl vl1 by (cases v) auto
         have False using f f_eq_PVal[OF step \<phi>, of pst] a \<phi> v by auto
        }
        hence \<phi>: "\<not> \<phi> ?trn" by auto
        have \<phi>1: "\<not> \<phi> ?trn1" by (metis \<phi> eqButPID_step_\<phi> step ss1 step1)
        have op': "\<not> open s'" using a op \<phi> unfolding \<phi>_def2[OF step] by auto
        have vl': "vl' = vl" using c \<phi> unfolding consume_def by auto
        have s's1': "eqButPID s' s1'" using eqButPID_step[OF ss1 step step1] .
        have op1': "\<not> open s1'" using op' eqButPID_open[OF s's1'] by simp
        have "\<And> uid p pst. e_updatePost s1 uid p PID pst \<longleftrightarrow> e_updatePost s uid p PID pst"
        using eqButPID_stateSelectors[OF ss1] unfolding u_defs by auto
        hence ou1: "\<And> uid p pst. a = Uact (uPost uid p PID pst) \<Longrightarrow> ou1 = ou"
        using step step1 by auto
        have ?match proof
          show "validTrans ?trn1" using step1 by simp
        next
          show "consume ?trn1 vl1 vl1" using \<phi>1 unfolding consume_def by simp
        next
          show "\<gamma> ?trn = \<gamma> ?trn1" unfolding ss1 by simp
        next
          assume "\<gamma> ?trn" note \<gamma> = this
          have ou: "(\<exists> uid p aid pid.
                       a = COMact (comSendPost uid p aid pid) \<and> outPurge ou = outPurge ou1) \<or>
                                        ou = ou1"
          using eqButPID_step_\<gamma>_out[OF ss1 step step1 op rsT rs1 \<gamma>] .
          thus "g ?trn = g ?trn1" by (cases a) auto
        next
          show "?\<Delta> s' vl' s1' vl1" using s's1' op' PID' lvl map
          unfolding \<Delta>1_def vl' vl1 by auto
        qed
      thus ?thesis by simp
      qed
    qed
    thus ?thesis using vlvl1 by simp
  qed
qed

lemma unwind_cont_\<Delta>11: "unwind_cont \<Delta>11 {\<Delta>11}"
proof(rule, simp)
  let ?\<Delta> = "\<lambda>s vl s1 vl1. \<Delta>11 s vl s1 vl1"
  fix s s1 :: state and vl vl1 :: "value list"
  assume rsT: "reachNT s" and rs1: "reach s1" and "\<Delta>11 s vl s1 vl1"
  hence  vl: "vl = []" and lvl1: "list_all isPVal vl1"
  and rs: "reach s" and ss1: "eqButPID s s1" and op: "\<not> open s" and PID: "PID \<in>\<in> postIDs s"
  and cor1: "corrFrom (post s1 PID) vl1"
  using reachNT_reach unfolding \<Delta>11_def by auto
  have PID1: "PID \<in>\<in> postIDs s1" using eqButPID_stateSelectors[OF ss1] PID by auto
  have own: "owner s PID \<in> set (userIDs s)" using reach_owner_userIDs[OF rs PID] .
  hence own1: "owner s1 PID \<in> set (userIDs s1)" using eqButPID_stateSelectors[OF ss1] by auto
  have adm: "admin s \<in> set (userIDs s)" using reach_admin_userIDs[OF rs own] .
  hence adm1: "admin s1 \<in> set (userIDs s1)" using eqButPID_stateSelectors[OF ss1] by auto
  have op1: "\<not> open s1" using op ss1 eqButPID_open by auto
  show "iaction ?\<Delta> s vl s1 vl1 \<or>
        ((vl = [] \<longrightarrow> vl1 = []) \<and> reaction ?\<Delta> s vl s1 vl1)" (is "?iact \<or> (_ \<and> ?react)")
  proof(cases vl1)
    case (Cons v1 vll1) note vl1 = Cons
    then obtain pst1 where v1: "v1 = PVal pst1" using lvl1 unfolding vl1 by (cases v1) auto
    define uid where uid: "uid \<equiv> owner s PID"  define p where p: "p \<equiv> pass s uid"
    define a1 where a1: "a1 \<equiv> Uact (uPost uid p PID pst1)"
    have uid1: "uid = owner s1 PID" and p1: "p = pass s1 uid" unfolding uid p
    using eqButPID_stateSelectors[OF ss1] by auto
    obtain ou1 s1' where step1: "step s1 a1 = (ou1, s1')" by(cases "step s1 a1") auto
    have ou1: "ou1 = outOK" using step1 PID1 own1 unfolding a1 uid1 p1 by (auto simp: u_defs)
    have op1': "\<not> open s1'" using step1 op1 unfolding a1 ou1 open_def by (auto simp: u_defs)
    have uid: "uid \<notin> UIDs" unfolding uid using op PID own unfolding open_def by auto
    have pPID1': "post s1' PID = pst1" using step1 unfolding a1 ou1 by (auto simp: u_defs)
    let ?trn1 = "Trans s1 a1 ou1 s1'"
    have ?iact proof
      show "step s1 a1 = (ou1, s1')" using step1 .
    next
      show \<phi>: "\<phi> ?trn1" unfolding \<phi>_def2[OF step1] a1 ou1 by simp
      show "consume ?trn1 vl1 vll1"
      using \<phi> unfolding vl1 consume_def v1 a1 by auto
    next
      show "\<not> \<gamma> ?trn1" using uid unfolding a1 by auto
    next
      have "eqButPID s1 s1'" using Uact_uPaperC_step_eqButPID[OF _ step1] a1 by auto
      hence ss1': "eqButPID s s1'" using eqButPID_trans ss1 by blast
      show "?\<Delta> s vl s1' vll1"
      using PID op ss1' lvl1 cor1 unfolding \<Delta>11_def vl1 v1 vl pPID1' by auto
    qed
    thus ?thesis by simp
  next
    case Nil note vl1 = Nil
    have ?react proof
      fix a :: act and ou :: out and s' :: state and vl'
      let ?trn = "Trans s a ou s'"
      assume step: "step s a = (ou, s')" and c: "consume ?trn vl vl'"
      have PID': "PID \<in>\<in> postIDs s'" using reach_postIDs_persist[OF PID step] .
      obtain ou1 s1' where step1: "step s1 a = (ou1, s1')" by(cases "step s1 a") auto
      let ?trn1 = "Trans s1 a ou1 s1'"
      have \<phi>: "\<not> \<phi> ?trn" using c unfolding consume_def vl by auto
      show "match ?\<Delta> s s1 vl1 a ou s' vl' \<or> ignore ?\<Delta> s s1 vl1 a ou s' vl'"
          (is "?match \<or> ?ignore")
      proof-
        have vl': "vl' = vl" using c unfolding vl consume_def by auto
        obtain ou1 s1' where step1: "step s1 a = (ou1, s1')" by(cases "step s1 a") auto
        have s's1': "eqButPID s' s1'" using eqButPID_step[OF ss1 step step1] .
        let ?trn1 = "Trans s1 a ou1 s1'"
        have \<phi>1: "\<not> \<phi> ?trn1" using \<phi> ss1 by (simp add: eqButPID_step_\<phi> step step1)
        have pPID1': "post s1' PID = post s1 PID" using PID1 step1 \<phi>1
        apply(cases a)
          subgoal for x1 apply(cases x1) apply(fastforce simp: s_defs)+ .
          subgoal for x2 apply(cases x2) apply(fastforce simp: c_defs)+ .
          subgoal for x3 apply(cases x3) apply(fastforce simp: d_defs)+ .
          subgoal for x4 apply(cases x4) apply(fastforce simp: u_defs)+ .
          subgoal by auto
          subgoal by auto
          subgoal for x7 apply(cases x7) apply(fastforce simp: com_defs)+ .
        done
        have op': "\<not> open s'"
          using PID step \<phi> op unfolding \<phi>_def2[OF step]
          by auto
        have ?match proof
          show "validTrans ?trn1" using step1 by simp
        next
          show "consume ?trn1 vl1 vl1" using \<phi>1 unfolding consume_def by simp
        next
          show "\<gamma> ?trn = \<gamma> ?trn1" unfolding ss1 by simp
        next
          assume "\<gamma> ?trn" note \<gamma> = this
          have ou: "(\<exists> uid p aid pid.
                   a = COMact (comSendPost uid p aid pid) \<and> outPurge ou = outPurge ou1) \<or>
                   ou = ou1"
          using eqButPID_step_\<gamma>_out[OF ss1 step step1 op rsT rs1 \<gamma>] .
          thus "g ?trn = g ?trn1" by (cases a) auto
        next
          have "?\<Delta> s' vl' s1' vl1" using s's1' PID' pPID1' lvl1 cor1 op'
          unfolding \<Delta>11_def vl vl' by auto
          thus "?\<Delta> s' vl' s1' vl1" by simp
        qed
        thus ?thesis by simp
      qed
    qed
    thus ?thesis using vl1 by simp
  qed
qed

lemma unwind_cont_\<Delta>31: "unwind_cont \<Delta>31 {\<Delta>31,\<Delta>32}"
proof(rule, simp)
  let ?\<Delta> = "\<lambda>s vl s1 vl1. \<Delta>31 s vl s1 vl1 \<or> \<Delta>32 s vl s1 vl1"
  fix s s1 :: state and vl vl1 :: "value list"
  assume rsT: "reachNT s" and rs1: "reach s1" and "\<Delta>31 s vl s1 vl1"
  then obtain ul ul1 sul vll vll1 where
  lul: "list_all (Not \<circ> isOVal) ul" and lul1: "list_all (Not \<circ> isOVal) ul1"
  and map: "map tgtAPI (filter isPValS ul) = map tgtAPI (filter isPValS ul1)"
  and rs: "reach s" and ss1: "eqButPID s s1" and op: "\<not> open s" and PID: "PID \<in>\<in> postIDs s"
  and cor1: "corrFrom (post s1 PID) vl1"
  and ful: "ul \<noteq> []" and ful1: "ul1 \<noteq> []"
  and lastul: "isPVal (last ul)" and ulul1: "last ul = last ul1"
  and lsul: "list_all isPValS sul"
  and vl: "vl = ul @ sul @ OVal True # vll"
  and vl1: "vl1 = ul1 @ sul @ OVal True # vll1"
  and BO: "BO vll vll1"
  using reachNT_reach unfolding \<Delta>31_def by auto
  have ulNE: "ul \<noteq> []" and ul1NE: "ul1 \<noteq> []" using ful ful1 by auto
  have PID1: "PID \<in>\<in> postIDs s1" using eqButPID_stateSelectors[OF ss1] PID by auto
  have own: "owner s PID \<in> set (userIDs s)" using reach_owner_userIDs[OF rs PID] .
  hence own1: "owner s1 PID \<in> set (userIDs s1)" using eqButPID_stateSelectors[OF ss1] by auto
  have adm: "admin s \<in> set (userIDs s)" using reach_admin_userIDs[OF rs own] .
  hence adm1: "admin s1 \<in> set (userIDs s1)" using eqButPID_stateSelectors[OF ss1] by auto
  have op1: "\<not> open s1" using op ss1 eqButPID_open by auto
  obtain v1 ull1 where ul1: "ul1 = v1 # ull1" using ful1 by (cases ul1) auto
  show "iaction ?\<Delta> s vl s1 vl1 \<or>
        ((vl = [] \<longrightarrow> vl1 = []) \<and> reaction ?\<Delta> s vl s1 vl1)" (is "?iact \<or> (_ \<and> ?react)")
  proof(cases v1)
    case (PVal pst1) note v1 = PVal
    show ?thesis proof(cases "list_ex isPVal ull1")
      case True note lull1 = True
      hence full1: "filter isPVal ull1 \<noteq> []" by (induct ull1) auto
      hence ull1NE: "ull1 \<noteq> []" by auto
      define uid where uid: "uid \<equiv> owner s PID"  define p where p: "p \<equiv> pass s uid"
      define a1 where a1: "a1 \<equiv> Uact (uPost uid p PID pst1)"
      have uid1: "uid = owner s1 PID" and p1: "p = pass s1 uid" unfolding uid p
      using eqButPID_stateSelectors[OF ss1] by auto
      obtain ou1 s1' where step1: "step s1 a1 = (ou1, s1')" by(cases "step s1 a1") auto
      have ou1: "ou1 = outOK" using step1 PID1 own1 unfolding a1 uid1 p1 by (auto simp: u_defs)
      have op1': "\<not> open s1'" using step1 op1 unfolding a1 ou1 open_def by (auto simp: u_defs)
      have uid: "uid \<notin> UIDs" unfolding uid using op PID own unfolding open_def by auto
      have pPID1': "post s1' PID = pst1" using step1 unfolding a1 ou1 by (auto simp: u_defs)
      let ?trn1 = "Trans s1 a1 ou1 s1'"
      let ?vl1' = "ull1 @ sul @ OVal True # vll1"
      have ?iact proof
        show "step s1 a1 = (ou1, s1')" using step1 .
      next
        show \<phi>: "\<phi> ?trn1" unfolding \<phi>_def2[OF step1] a1 ou1 by simp
        show "consume ?trn1 vl1 ?vl1'"
        using \<phi> unfolding vl1 ul1 consume_def v1 a1 by simp
      next
        show "\<not> \<gamma> ?trn1" using uid unfolding a1 by auto
      next
        have "eqButPID s1 s1'" using Uact_uPaperC_step_eqButPID[OF _ step1] a1 by auto
        hence ss1': "eqButPID s s1'" using eqButPID_trans ss1 by blast
        have "\<Delta>31 s vl s1' ?vl1'"
        using PID op ss1' lul lul1 map ulul1 cor1 BO ull1NE ful ful1 full1 lastul ulul1 lsul
        unfolding \<Delta>31_def vl vl1 ul1 v1 pPID1' apply auto
        apply(rule exI[of _ "ul"]) apply(rule exI[of _ "ull1"]) apply(rule exI[of _ sul])
        apply(rule exI[of _ "vll"]) apply(rule exI[of _ "vll1"]) by auto
        thus "?\<Delta> s vl s1' ?vl1'" by auto
      qed
      thus ?thesis by simp
    next
      case False note lull1 = False
      hence ull1: "ull1 = []" using lastul unfolding ulul1 ul1 v1 by simp(meson Bex_set last_in_set)
      hence ul1: "ul1 = [PVal pst1]" unfolding ul1 v1 by simp
      obtain ulll where ul_ulll: "ul = ulll ## PVal pst1" using lastul ulul1 ulNE unfolding ul1 ull1 v1
      by (cases ul rule: rev_cases) auto
      hence ulNE: "ul \<noteq> []" by simp
      (* then obtain v ul' where ul: "ul = v # ul'" by (cases ul) auto *)
      have "filter isPValS ulll = []" using map unfolding ul_ulll ul1 v1 ull1 by simp
      hence lull: "list_all isPVal ulll" using lul filter_list_all_isPVal_isOVal
      unfolding ul_ulll by auto
      have ?react  proof
        fix a :: act and ou :: out and s' :: state and vl'
        let ?trn = "Trans s a ou s'"
        assume step: "step s a = (ou, s')" and c: "consume ?trn vl vl'"
        have PID': "PID \<in>\<in> postIDs s'" using reach_postIDs_persist[OF PID step] .
        obtain ul' where cc: "consume ?trn ul ul'" and
        vl': "vl' = ul' @ sul @ OVal True # vll" using c ulNE unfolding consume_def vl
        by (cases "\<phi> ?trn") auto
        obtain ou1 s1' where step1: "step s1 a = (ou1, s1')" by(cases "step s1 a") auto
        let ?trn1 = "Trans s1 a ou1 s1'"
        show "match ?\<Delta> s s1 vl1 a ou s' vl' \<or> ignore ?\<Delta> s s1 vl1 a ou s' vl'"
             (is "?match \<or> ?ignore")
        proof(cases ulll)
          case Nil
          hence ul: "ul = [PVal pst1]" unfolding ul_ulll by simp
          have ?match proof(cases "\<phi> ?trn")
            case True note \<phi> = True
            then obtain f: "f ?trn = PVal pst1" and ul': "ul' = []"
            using cc unfolding ul consume_def \<phi>_def2 by auto
            define uid where uid: "uid \<equiv> owner s PID"  define p where p: "p \<equiv> pass s uid"
            have a: "a = Uact (uPost uid p PID pst1)"
            using f_eq_PVal[OF step \<phi> f] unfolding uid p .
            have uid1: "uid = owner s1 PID" and p1: "p = pass s1 uid" unfolding uid p
            using eqButPID_stateSelectors[OF ss1] by auto
            obtain ou1 s1' where step1: "step s1 a = (ou1, s1')" by(cases "step s1 a") auto
            let ?trn1 = "Trans s1 a ou1 s1'"
            have \<phi>1: "\<phi> ?trn1" using eqButPID_step_\<phi>_imp[OF ss1 step step1 \<phi>] .
            have ou1: "ou1 = outOK"
            using \<phi>1 step1 PID1 unfolding a by (cases ou1, auto simp: com_defs)
            have pPID': "post s' PID = pst1" using step \<phi> unfolding a by (auto simp: u_defs)
            have pPID1': "post s1' PID = pst1" using step1 \<phi>1 unfolding a by (auto simp: u_defs)
            have uid: "uid \<notin> UIDs" unfolding uid using op PID own unfolding open_def by auto
            have op1': "\<not> open s1'" using step1 op1 unfolding a open_def
            by (auto simp: u_defs com_defs)
            have f1: "f ?trn1 = PVal pst1" using \<phi>1 unfolding \<phi>_def2[OF step1] v1 a ou1 by auto
            have s's1': "eqButPID s' s1'" using eqButPID_step[OF ss1 step step1] .
            have op': "\<not> open s'" using uPost_comSendPost_open_eq[OF step] a op by auto
            have ou: "ou = outOK" using \<phi> op op' unfolding \<phi>_def2[OF step] a by auto
            let ?vl' = "sul @ OVal True # vll"
            let ?vl1' = "sul @ OVal True # vll1"
            show ?thesis proof
              show "validTrans ?trn1" using step1 by simp
            next
              show "consume ?trn1 vl1 ?vl1'"
              using \<phi>1 unfolding consume_def ul1 f1 vl1 by simp
            next
              show "\<gamma> ?trn = \<gamma> ?trn1" unfolding ss1 by simp
            next
              assume "\<gamma> ?trn" note \<gamma> = this
              thus "g ?trn = g ?trn1" using ou ou1 by (cases a) auto
            next
              have s': "s' = s1'" using eqButPID_step_eq[OF ss1 a ou step step1] .
              have corr1: "corrFrom (post s1' PID) ?vl1'"
              using cor1 unfolding vl1 ul1 v1 pPID1' by auto
              have "\<Delta>32 s' vl' s1' ?vl1'"
              using PID' op1 op' s's1' lul lul1 map ulul1 cor1 BO ful ful1 lastul ulul1 lsul corr1
              unfolding \<Delta>32_def vl vl1 v1 vl' ul' ul ul1 s' apply simp
              apply(rule exI[of _ sul])
              apply(rule exI[of _ "vll"]) apply(rule exI[of _ "vll1"]) by auto
              thus "?\<Delta> s' vl' s1' ?vl1'" by simp
            qed
          next
            case False note \<phi> = False
            hence ul': "ul' = ul" using cc unfolding consume_def by auto
            obtain ou1 s1' where step1: "step s1 a = (ou1, s1')" by(cases "step s1 a") auto
            have s's1': "eqButPID s' s1'" using eqButPID_step[OF ss1 step step1] .
            let ?trn1 = "Trans s1 a ou1 s1'"
            have \<phi>1: "\<not> \<phi> ?trn1" using \<phi> ss1 by (simp add: eqButPID_step_\<phi> step step1)
            have pPID1': "post s1' PID = post s1 PID" using PID1 step1 \<phi>1
            apply(cases a)
              subgoal for x1 apply(cases x1) apply(fastforce simp: s_defs)+ .
              subgoal for x2 apply(cases x2) apply(fastforce simp: c_defs)+ .
              subgoal for x3 apply(cases x3) apply(fastforce simp: d_defs)+ .
              subgoal for x4 apply(cases x4) apply(fastforce simp: u_defs)+ .
              subgoal by auto
              subgoal by auto
              subgoal for x7 apply(cases x7) apply(fastforce simp: com_defs)+ .
            done
            have op': "\<not> open s'"
            using PID step \<phi> op unfolding \<phi>_def2[OF step] by auto
            have ?match proof
              show "validTrans ?trn1" using step1 by simp
            next
              show "consume ?trn1 vl1 vl1" using \<phi>1 unfolding consume_def by simp
            next
              show "\<gamma> ?trn = \<gamma> ?trn1" unfolding ss1 by simp
            next
              assume "\<gamma> ?trn" note \<gamma> = this
              have ou: "(\<exists> uid p aid pid.
                 a = COMact (comSendPost uid p aid pid) \<and> outPurge ou = outPurge ou1) \<or>
                 ou = ou1"
              using eqButPID_step_\<gamma>_out[OF ss1 step step1 op rsT rs1 \<gamma>] .
              thus "g ?trn = g ?trn1" by (cases a) auto
            next
              have "\<Delta>31 s' vl' s1' vl1"
              using PID' pPID1' op' s's1' lul lul1 map ulul1 cor1
              BO ful ful1 lastul ulul1 lsul cor1
              unfolding \<Delta>31_def vl vl1 v1 vl' ul' apply simp
              apply(rule exI[of _ "ul"]) apply(rule exI[of _ "ul1"]) apply(rule exI[of _ sul])
              apply(rule exI[of _ "vll"]) apply(rule exI[of _ "vll1"]) by auto
              thus "?\<Delta> s' vl' s1' vl1" by simp
            qed
            thus ?thesis by simp
          qed
          thus ?thesis by simp
        next
          case (Cons v ullll) note ulll = Cons
          then obtain pst where v: "v = PVal pst" using lull ul_ulll ulll lul by (cases v) auto
          define ull where ull: "ull \<equiv> ullll ## PVal pst1"
          have ul: "ul = v # ull" unfolding ul_ulll ull ulll by simp
          show ?thesis proof(cases "\<phi> ?trn")
            case True note \<phi> = True
            then obtain f: "f ?trn = v" and ul': "ul' = ull"
            using cc unfolding ul consume_def \<phi>_def2 by auto
            define uid where uid: "uid \<equiv> owner s PID"  define p where p: "p \<equiv> pass s uid"
            have a: "a = Uact (uPost uid p PID pst)"
            using f_eq_PVal[OF step \<phi> f[unfolded v]] unfolding uid p .
            have "eqButPID s s'" using Uact_uPaperC_step_eqButPID[OF a step] by auto
            hence s's1: "eqButPID s' s1" using eqButPID_sym eqButPID_trans ss1 by blast
            have op': "\<not> open s'" using uPost_comSendPost_open_eq[OF step] a op by auto
            have ?ignore proof
              show \<gamma>: "\<not> \<gamma> ?trn" using step_open_\<phi>_f_PVal_\<gamma>[OF rs step PID op \<phi> f[unfolded v]] .
              have "\<Delta>31 s' vl' s1 vl1"
              using PID' op' s's1 lul lul1 map ulul1 cor1 BO ful ful1 lastul ulul1 lsul ull
              unfolding \<Delta>31_def vl vl1 v1 vl' ul' ul v apply simp
              apply(rule exI[of _ "ull"]) apply(rule exI[of _ "ul1"]) apply(rule exI[of _ sul])
              apply(rule exI[of _ "vll"]) apply(rule exI[of _ "vll1"]) by auto
              thus "?\<Delta> s' vl' s1 vl1" by auto
            qed
            thus ?thesis by simp
          next
            case False note \<phi> = False
            hence ul': "ul' = ul" using cc unfolding consume_def by auto
            obtain ou1 s1' where step1: "step s1 a = (ou1, s1')" by(cases "step s1 a") auto
            have s's1': "eqButPID s' s1'" using eqButPID_step[OF ss1 step step1] .
            let ?trn1 = "Trans s1 a ou1 s1'"
            have \<phi>1: "\<not> \<phi> ?trn1" using \<phi> ss1 by (simp add: eqButPID_step_\<phi> step step1)
            have pPID1': "post s1' PID = post s1 PID" using PID1 step1 \<phi>1
            apply(cases a)
              subgoal for x1 apply(cases x1) apply(fastforce simp: s_defs)+ .
              subgoal for x2 apply(cases x2) apply(fastforce simp: c_defs)+ .
              subgoal for x3 apply(cases x3) apply(fastforce simp: d_defs)+ .
              subgoal for x4 apply(cases x4) apply(fastforce simp: u_defs)+ .
              subgoal by auto
              subgoal by auto
              subgoal for x7 apply(cases x7) apply(fastforce simp: com_defs)+ .
            done
            have op': "\<not> open s'"
            using PID step \<phi> op unfolding \<phi>_def2[OF step] by auto
            have ?match proof
              show "validTrans ?trn1" using step1 by simp
            next
              show "consume ?trn1 vl1 vl1" using \<phi>1 unfolding consume_def by simp
            next
              show "\<gamma> ?trn = \<gamma> ?trn1" unfolding ss1 by simp
            next
              assume "\<gamma> ?trn" note \<gamma> = this
              have ou: "(\<exists> uid p aid pid.
                 a = COMact (comSendPost uid p aid pid) \<and> outPurge ou = outPurge ou1) \<or>
                 ou = ou1"
              using eqButPID_step_\<gamma>_out[OF ss1 step step1 op rsT rs1 \<gamma>] .
              thus "g ?trn = g ?trn1" by (cases a) auto
            next
              have "\<Delta>31 s' vl' s1' vl1"
              using PID' pPID1' op' s's1' lul lul1 map ulul1 cor1
              BO ful ful1 lastul ulul1 lsul cor1
              unfolding \<Delta>31_def vl vl1 v1 vl' ul' apply simp
              apply(rule exI[of _ "ul"]) apply(rule exI[of _ "ul1"]) apply(rule exI[of _ sul])
              apply(rule exI[of _ "vll"]) apply(rule exI[of _ "vll1"]) by auto
              thus "?\<Delta> s' vl' s1' vl1" by simp
            qed
          thus ?thesis by simp
          qed
        qed
      qed
      thus ?thesis using vl by simp
    qed
  next
    case (PValS aid1 pst1) note v1 = PValS
    have pPID1: "post s1 PID = pst1" using cor1 unfolding vl1 ul1 v1 by auto
    then obtain v ull where ul: "ul = v # ull"
    using map unfolding ul1 v1 by (cases ul) auto
    let ?vl1' = "ull1 @ sul @ OVal True # vll1"
    have ?react proof
      fix a :: act and ou :: out and s' :: state and vl'
      let ?trn = "Trans s a ou s'"
      assume step: "step s a = (ou, s')" and c: "consume ?trn vl vl'"
      have PID': "PID \<in>\<in> postIDs s'" using reach_postIDs_persist[OF PID step] .
      obtain ul' where cc: "consume ?trn ul ul'" and
      vl': "vl' = ul' @ sul @ OVal True # vll" using c ul unfolding consume_def vl
      by (cases "\<phi> ?trn") auto
      obtain ou1 s1' where step1: "step s1 a = (ou1, s1')" by(cases "step s1 a") auto
      let ?trn1 = "Trans s1 a ou1 s1'"
      show "match ?\<Delta> s s1 vl1 a ou s' vl' \<or> ignore ?\<Delta> s s1 vl1 a ou s' vl'"
          (is "?match \<or> ?ignore")
      proof(cases "\<phi> ?trn")
        case True note \<phi> = True
        then obtain f: "f ?trn = v" and ul': "ul' = ull"
        using cc unfolding ul consume_def \<phi>_def2 by auto
        show ?thesis
        proof(cases v)
          case (PVal pst) note v = PVal
          have full: "ull \<noteq> []" using map unfolding ul1 v1 ul v by auto
          define uid where uid: "uid \<equiv> owner s PID"  define p where p: "p \<equiv> pass s uid"
          have a: "a = Uact (uPost uid p PID pst)"
          using f_eq_PVal[OF step \<phi> f[unfolded v]] unfolding uid p .
          have "eqButPID s s'" using Uact_uPaperC_step_eqButPID[OF a step] by auto
          hence s's1: "eqButPID s' s1" using eqButPID_sym eqButPID_trans ss1 by blast
          have op': "\<not> open s'" using uPost_comSendPost_open_eq[OF step] a op by auto
          (* have "list_ex isPVal ull1" using lastul not_list_ex_filter
          using ful1 not_list_ex_filter ul1 v1 unfolding ulul1 by auto
          hence lull: "list_ex isPVal ull" using lastul ulul1 ull unfolding ul ul1 v v1
          by (metis filter_empty_conv last_ConsR last_in_set not_list_ex_filter)
          hence full: "filter isPVal ull \<noteq> []" by (induct ull) auto *)
          have ?ignore proof
            show \<gamma>: "\<not> \<gamma> ?trn" using step_open_\<phi>_f_PVal_\<gamma>[OF rs step PID op \<phi> f[unfolded v]] .
            have "\<Delta>31 s' vl' s1 vl1"
            using PID' op' s's1 lul lul1 map ulul1 cor1 BO ful ful1 lastul ulul1 lsul full
            unfolding \<Delta>31_def vl vl1 v1 vl' ul' ul v apply simp
            apply(rule exI[of _ "ull"]) apply(rule exI[of _ "ul1"]) apply(rule exI[of _ sul])
            apply(rule exI[of _ "vll"]) apply(rule exI[of _ "vll1"]) by auto
            thus "?\<Delta> s' vl' s1 vl1" by auto
          qed
          thus ?thesis by simp
        next
          case (PValS aid pst) note v = PValS
          define uid where uid: "uid \<equiv> admin s" define p where p: "p \<equiv> pass s uid"
          have a: "a = COMact (comSendPost (admin s) p aid PID)"
          using f_eq_PValS[OF step \<phi> f[unfolded v]] unfolding uid p .
          have op': "\<not> open s'" using uPost_comSendPost_open_eq[OF step] a op by auto
          have aid1: "aid1 = aid" using map unfolding ul1 v1 ul v by simp
          have uid1: "uid = admin s1" and p1: "p = pass s1 uid" unfolding uid p
          using eqButPID_stateSelectors[OF ss1] by auto
          obtain ou1 s1' where step1: "step s1 a = (ou1, s1')" by(cases "step s1 a") auto
          have pPID1': "post s1' PID = pst1" using pPID1 step1 unfolding a
          by (auto simp: com_defs)
          have uid: "uid \<notin> UIDs" unfolding uid using op PID adm unfolding open_def by auto
          have op1': "\<not> open s1'" using step1 op1 unfolding a open_def
          by (auto simp: u_defs com_defs)
          let ?trn1 = "Trans s1 a ou1 s1'"
          have \<phi>1: "\<phi> ?trn1" using eqButPID_step_\<phi>_imp[OF ss1 step step1 \<phi>] .
          have ou1: "ou1 =
            O_sendPost (aid, clientPass s1 aid, PID, post s1 PID, owner s1 PID, vis s1 PID)"
          using \<phi>1 step1 adm1 PID1 unfolding a by (cases ou1, auto simp: com_defs)
          have f1: "f ?trn1 = v1" using \<phi>1 unfolding \<phi>_def2[OF step1] v1 a ou1 aid1 pPID1 by auto
          have s's1': "eqButPID s' s1'" using eqButPID_step[OF ss1 step step1] .
          have ?match proof
            show "validTrans ?trn1" using step1 by simp
          next
            show "consume ?trn1 vl1 ?vl1'" using \<phi>1 unfolding consume_def ul1 f1 vl1 by simp
          next
            show "\<gamma> ?trn = \<gamma> ?trn1" unfolding ss1 by simp
          next
            assume "\<gamma> ?trn" note \<gamma> = this
            have ou: "(\<exists> uid p aid pid.
               a = COMact (comSendPost uid p aid pid) \<and> outPurge ou = outPurge ou1) \<or>
               ou = ou1"
            using eqButPID_step_\<gamma>_out[OF ss1 step step1 op rsT rs1 \<gamma>] .
            thus "g ?trn = g ?trn1" by (cases a) auto
          next
            have corr1: "corrFrom (post s1' PID) ?vl1'"
            using cor1 unfolding vl1 ul1 v1 pPID1' by auto
            have ullull1: "ull1 \<noteq> [] \<longrightarrow> ull \<noteq> []" using ul ul1 lastul ulul1 unfolding v v1
            by fastforce
            have "\<Delta>31 s' vl' s1' ?vl1'"
            using PID' op' s's1' lul lul1 map ulul1 cor1 BO ful ful1 lastul ulul1 lsul corr1 ullull1
            unfolding \<Delta>31_def vl vl1 v1 vl' ul' ul ul1 v apply auto
            apply(rule exI[of _ "ull"]) apply(rule exI[of _ "ull1"]) apply(rule exI[of _ sul])
            apply(rule exI[of _ "vll"]) apply(rule exI[of _ "vll1"]) by auto
            thus "?\<Delta> s' vl' s1' ?vl1'" by simp
          qed
          thus ?thesis using ul by simp
        next
        qed(insert lul ul, auto)
      next
        case False note \<phi> = False
        hence ul': "ul' = ul" using cc unfolding consume_def by auto
        obtain ou1 s1' where step1: "step s1 a = (ou1, s1')" by(cases "step s1 a") auto
        have s's1': "eqButPID s' s1'" using eqButPID_step[OF ss1 step step1] .
        let ?trn1 = "Trans s1 a ou1 s1'"
        have \<phi>1: "\<not> \<phi> ?trn1" using \<phi> ss1 by (simp add: eqButPID_step_\<phi> step step1)
        have pPID1': "post s1' PID = pst1" using PID1 pPID1 step1 \<phi>1
        apply(cases a)
          subgoal for x1 apply(cases x1) apply(fastforce simp: s_defs)+ .
          subgoal for x2 apply(cases x2) apply(fastforce simp: c_defs)+ .
          subgoal for x3 apply(cases x3) apply(fastforce simp: d_defs)+ .
          subgoal for x4 apply(cases x4) apply(fastforce simp: u_defs)+ .
          subgoal by auto
          subgoal by auto
          subgoal for x7 apply(cases x7) apply(fastforce simp: com_defs)+ .
        done
        have op': "\<not> open s'"
        using PID step \<phi> op unfolding \<phi>_def2[OF step] by auto
        have ?match proof
          show "validTrans ?trn1" using step1 by simp
        next
          show "consume ?trn1 vl1 vl1" using \<phi>1 unfolding consume_def by simp
        next
          show "\<gamma> ?trn = \<gamma> ?trn1" unfolding ss1 by simp
        next
          assume "\<gamma> ?trn" note \<gamma> = this
          have ou: "(\<exists> uid p aid pid.
                 a = COMact (comSendPost uid p aid pid) \<and> outPurge ou = outPurge ou1) \<or>
                 ou = ou1"
          using eqButPID_step_\<gamma>_out[OF ss1 step step1 op rsT rs1 \<gamma>] .
          thus "g ?trn = g ?trn1" by (cases a) auto
        next
          have "\<Delta>31 s' vl' s1' vl1"
          using PID' pPID1 pPID1' op' s's1' lul lul1 map ulul1 cor1
            BO ful ful1 lastul ulul1 lsul cor1
          unfolding \<Delta>31_def vl vl1 v1 vl' ul' apply simp
          apply(rule exI[of _ "ul"]) apply(rule exI[of _ "ul1"]) apply(rule exI[of _ sul])
          apply(rule exI[of _ "vll"]) apply(rule exI[of _ "vll1"]) by auto
          thus "?\<Delta> s' vl' s1' vl1" by simp
        qed
        thus ?thesis by simp
      qed
    qed
    thus ?thesis using vl by simp
  qed(insert lul1 ul1, auto)
qed

lemma unwind_cont_\<Delta>32: "unwind_cont \<Delta>32 {\<Delta>2,\<Delta>32,\<Delta>4}"
proof(rule, simp)
  let ?\<Delta> = "\<lambda>s vl s1 vl1. \<Delta>2 s vl s1 vl1 \<or> \<Delta>32 s vl s1 vl1 \<or> \<Delta>4 s vl s1 vl1"
  fix s s1 :: state and vl vl1 :: "value list"
  assume rsT: "reachNT s" and rs1: "reach s1" and "\<Delta>32 s vl s1 vl1"
  then obtain ul vll vll1 where
  lul: "list_all isPValS ul"
  and rs: "reach s" and ss1: "s1 = s" and op: "\<not> open s" and PID: "PID \<in>\<in> postIDs s"
  and cor1: "corrFrom (post s1 PID) vl1"
  and vl: "vl = ul @ OVal True # vll"
  and vl1: "vl1 = ul @ OVal True # vll1"
  and BO: "BO vll vll1"
  using reachNT_reach unfolding \<Delta>32_def by blast
  have own: "owner s PID \<in> set (userIDs s)" using reach_owner_userIDs[OF rs PID] .
  have adm: "admin s \<in> set (userIDs s)" using reach_admin_userIDs[OF rs own] .
  show "iaction ?\<Delta> s vl s1 vl1 \<or>
        ((vl = [] \<longrightarrow> vl1 = []) \<and> reaction ?\<Delta> s vl s1 vl1)" (is "?iact \<or> (_ \<and> ?react)")
  proof-
    have ?react proof
      fix a :: act and ou :: out and s' :: state and vl'
      let ?trn = "Trans s a ou s'" let ?trn1 = "Trans s1 a ou s'"
      assume step: "step s a = (ou, s')" and c: "consume ?trn vl vl'"
      have PID': "PID \<in>\<in> postIDs s'" using reach_postIDs_persist[OF PID step] .
      show "match ?\<Delta> s s1 vl1 a ou s' vl' \<or> ignore ?\<Delta> s s1 vl1 a ou s' vl'"
          (is "?match \<or> ?ignore")
      proof-
        have ?match proof(cases "ul = []")
          case False note ul = False
          then obtain ul' where cc: "consume ?trn ul ul'"
          and vl': "vl' = ul' @ OVal True # vll" using vl c unfolding consume_def
          by (cases "\<phi> ?trn") auto
          let ?vl1' = "ul' @ OVal True # vll1"
          show ?thesis proof
            show "validTrans ?trn1" using step unfolding ss1 by simp
          next
            show "consume ?trn1 vl1 ?vl1'" using cc ul unfolding vl1 consume_def ss1
            by (cases "\<phi> ?trn") auto
          next
            show "\<gamma> ?trn = \<gamma> ?trn1" unfolding ss1 by simp
          next
            assume "\<gamma> ?trn" note \<gamma> = this
            thus "g ?trn = g ?trn1" unfolding ss1 by simp
          next
            have "\<Delta>32 s' vl' s' ?vl1'"
            proof(cases "\<phi> ?trn")
              case True note \<phi> = True
              then obtain v where f: "f ?trn = v" and  ul: "ul = v # ul'"
              using cc unfolding consume_def by (cases ul) auto
              define uid where uid: "uid \<equiv> admin s" define p where p: "p \<equiv> pass s uid"
              obtain aid pst where v: "v = PValS aid pst" using lul unfolding ul by (cases v) auto
              have a: "a = COMact (comSendPost (admin s) p aid PID)"
              using f_eq_PValS[OF step \<phi> f[unfolded v]] unfolding uid p .
              have op': "\<not> open s'" using uPost_comSendPost_open_eq[OF step] a op by auto
              have pPID': "post s' PID = post s PID"
              using step unfolding a by (auto simp: com_defs)
              show ?thesis using PID' pPID' op' cor1 BO lul
              unfolding \<Delta>32_def vl1 ul ss1 v vl' by auto
            next
              case False note \<phi> = False
              hence ul: "ul = ul'" using cc unfolding consume_def by (cases ul) auto
              have pPID': "post s' PID = post s PID"
              using step \<phi> PID op
              apply(cases a)
                subgoal for x1 apply(cases x1) apply(fastforce simp: s_defs)+ .
                subgoal for x2 apply(cases x2) apply(fastforce simp: c_defs)+ .
                subgoal for x3 apply(cases x3) apply(fastforce simp: d_defs)+ .
                subgoal for x4 apply(cases x4) apply(auto simp: u_defs) .
                subgoal by auto
                subgoal by auto
                subgoal for x7 apply(cases x7) apply(fastforce simp: com_defs)+ .
              done
              have op': "\<not> open s'"
              using PID step \<phi> op unfolding \<phi>_def2[OF step] by auto
              show ?thesis using PID' pPID' op' cor1 BO lul
              unfolding \<Delta>32_def vl1 ul ss1 vl' by auto
            qed
            thus "?\<Delta> s' vl' s' ?vl1'" by simp
          qed
        next
          case True note ul = True
          show ?thesis proof(cases "\<phi> ?trn")
            case True note \<phi> = True
            hence f: "f ?trn = OVal True" and vl': "vl' = vll"
            using vl c unfolding consume_def ul by auto
            have op': "open s'" using f_eq_OVal[OF step \<phi> f] op by simp
            show ?thesis proof
              show "validTrans ?trn1" using step unfolding ss1 by simp
            next
              show "consume ?trn1 vl1 vll1" using ul \<phi> c
              unfolding vl1 vl' vl ss1 consume_def by auto
            next
              show "\<gamma> ?trn = \<gamma> ?trn1" unfolding ss1 by simp
            next
              assume "\<gamma> ?trn" note \<gamma> = this
              thus "g ?trn = g ?trn1" unfolding ss1 by simp
            next
              have pPID': "post s' PID = post s PID"
              using step \<phi> PID op op' f
              apply(cases a)
                subgoal for x1 apply(cases x1) apply(fastforce simp: s_defs)+ .
                subgoal for x2 apply(cases x2) apply(fastforce simp: c_defs)+ .
                subgoal for x3 apply(cases x3) apply(fastforce simp: d_defs)+ .
                subgoal for x4 apply(cases x4) apply(auto simp: u_defs) .
                subgoal by auto
                subgoal by auto
                subgoal for x7 apply(cases x7) apply(fastforce simp: com_defs)+ .
              done
              show "?\<Delta> s' vl' s' vll1" using BO proof cases
                case BO_PVal
                hence "\<Delta>2 s' vl' s' vll1" using PID' pPID' op' cor1 BO lul
                unfolding \<Delta>2_def vl1 ul ss1 vl' by auto
                thus ?thesis by simp
              next
                case BO_BC
                hence "\<Delta>4 s' vl' s' vll1" using PID' pPID' op' cor1 BO lul
                unfolding \<Delta>4_def vl1 ul ss1 vl' by auto
                thus ?thesis by simp
              qed
            qed
          next
            case False note \<phi> = False
            hence vl': "vl' = vl" using c unfolding consume_def by auto
            have pPID': "post s' PID = post s PID"
            using step \<phi> PID op
            apply(cases a)
                subgoal for x1 apply(cases x1) apply(fastforce simp: s_defs)+ .
                subgoal for x2 apply(cases x2) apply(fastforce simp: c_defs)+ .
                subgoal for x3 apply(cases x3) apply(fastforce simp: d_defs)+ .
                subgoal for x4 apply(cases x4) apply(auto simp: u_defs) .
                subgoal by auto
                subgoal by auto
                subgoal for x7 apply(cases x7) apply(fastforce simp: com_defs)+ .
            done
            have op': "\<not> open s'"
            using PID step \<phi> op unfolding \<phi>_def2[OF step] by (cases a) auto
            show ?thesis proof
              show "validTrans ?trn1" using step unfolding ss1 by simp
            next
              show "consume ?trn1 vl1 vl1" using ul \<phi> unfolding vl1 consume_def ss1 by simp
            next
              show "\<gamma> ?trn = \<gamma> ?trn1" unfolding ss1 by simp
            next
              assume "\<gamma> ?trn" note \<gamma> = this
              thus "g ?trn = g ?trn1" unfolding ss1 by simp
            next
              have "\<Delta>32 s' vl' s' vl1" using PID' pPID' op' cor1 BO lul
              unfolding \<Delta>32_def vl vl1 ul ss1 vl' apply simp
              apply(rule exI[of _ "[]"])
              apply(rule exI[of _ vll]) apply(rule exI[of _ vll1]) by auto
              thus "?\<Delta> s' vl' s' vl1" by simp
            qed
          qed
        qed
        thus ?thesis by simp
      qed
    qed
  thus ?thesis using vl by simp
  qed
qed

lemma unwind_cont_\<Delta>2: "unwind_cont \<Delta>2 {\<Delta>2}"
proof(rule, simp)
  let ?\<Delta> = "\<lambda>s vl s1 vl1. \<Delta>2 s vl s1 vl1"
  fix s s1 :: state and vl vl1 :: "value list"
  assume rsT: "reachNT s" and rs1: "reach s1" and "\<Delta>2 s vl s1 vl1"
  hence vlvl1: "vl = vl1"
  and rs: "reach s" and ss1: "s1 = s" and op: "open s" and PID: "PID \<in>\<in> postIDs s"
  and cor1: "corrFrom (post s1 PID) vl1" and lvl: "list_all (Not \<circ> isOVal) vl"
  using reachNT_reach unfolding \<Delta>2_def by auto
  have own: "owner s PID \<in> set (userIDs s)" using reach_owner_userIDs[OF rs PID] .
  have adm: "admin s \<in> set (userIDs s)" using reach_admin_userIDs[OF rs own] .
  show "iaction ?\<Delta> s vl s1 vl1 \<or>
        ((vl = [] \<longrightarrow> vl1 = []) \<and> reaction ?\<Delta> s vl s1 vl1)" (is "?iact \<or> (_ \<and> ?react)")
  proof-
    have ?react proof
      fix a :: act and ou :: out and s' :: state and vl'
      let ?trn = "Trans s a ou s'"  let ?trn1 = "Trans s1 a ou s'"
      assume step: "step s a = (ou, s')" and c: "consume ?trn vl vl'"
      have PID': "PID \<in>\<in> postIDs s'" using reach_postIDs_persist[OF PID step] .
      show "match ?\<Delta> s s1 vl1 a ou s' vl' \<or> ignore ?\<Delta> s s1 vl1 a ou s' vl'" (is "?match \<or> ?ignore")
      proof-
        have ?match proof(cases "\<phi> ?trn")
          case True note \<phi> = True
          then obtain v where vl: "vl = v # vl'" and f: "f ?trn = v"
          using c unfolding consume_def \<phi>_def2 by(cases vl) auto
          show ?thesis proof(cases v)
            case (PVal pst) note v = PVal
            have a: "a = Uact (uPost (owner s PID) (pass s (owner s PID)) PID pst)"
            using f_eq_PVal[OF step \<phi> f[unfolded v]] .
            have ou: "ou = outOK" using step own PID unfolding a by (auto simp: u_defs)
            have op': "open s'" using step op PID PID' \<phi>
            unfolding open_def a by (auto simp: u_defs)
            have pPID': "post s' PID = pst"
            using step \<phi> PID op f op' unfolding a by(auto simp: u_defs)
            show ?thesis proof
              show "validTrans ?trn1" unfolding ss1 using step by simp
            next
              show "consume ?trn1 vl1 vl'" using \<phi> vlvl1 unfolding ss1 consume_def vl f by auto
            next
              show "\<gamma> ?trn = \<gamma> ?trn1" unfolding ss1 by simp
            next
              assume "\<gamma> ?trn" thus "g ?trn = g ?trn1" unfolding ss1 by simp
            next
              show "?\<Delta> s' vl' s' vl'" using cor1 PID' pPID' op' lvl vlvl1 ss1
              unfolding \<Delta>2_def vl v by auto
            qed
          next
            case (PValS aid pid) note v = PValS
            have a: "a = COMact (comSendPost (admin s) (pass s (admin s)) aid PID)"
            using f_eq_PValS[OF step \<phi> f[unfolded v]] .
            have op': "open s'" using step op PID PID' \<phi>
            unfolding open_def a by (auto simp: com_defs)
            have ou: "ou \<noteq> outErr" using \<phi> op op' unfolding \<phi>_def2[OF step] unfolding a by auto
            have pPID': "post s' PID = post s PID"
            using step \<phi> PID op f op' unfolding a by(auto simp: com_defs)
            show ?thesis proof
              show "validTrans ?trn1" unfolding ss1 using step by simp
            next
              show "consume ?trn1 vl1 vl'" using \<phi> vlvl1 unfolding ss1 consume_def vl f by auto
            next
              show "\<gamma> ?trn = \<gamma> ?trn1" unfolding ss1 by simp
            next
              assume "\<gamma> ?trn" thus "g ?trn = g ?trn1" unfolding ss1 by simp
            next
              show "?\<Delta> s' vl' s' vl'" using cor1 PID' pPID' op' lvl vlvl1 ss1
              unfolding \<Delta>2_def vl v by auto
            qed
          qed(insert vl lvl, auto)
        next
          case False note \<phi> = False
          hence vl': "vl' = vl" using c unfolding consume_def by auto
          have pPID': "post s' PID = post s PID"
            using step \<phi> PID op
            apply(cases a)
                subgoal for x1 apply(cases x1) apply(fastforce simp: s_defs)+ .
                subgoal for x2 apply(cases x2) apply(fastforce simp: c_defs)+ .
                subgoal for x3 apply(cases x3) apply(fastforce simp: d_defs)+ .
                subgoal for x4 apply(cases x4) apply(auto simp: u_defs) .
                subgoal by auto
                subgoal by auto
                subgoal for x7 apply(cases x7) apply(fastforce simp: com_defs)+ .
            done
          have op': "open s'"
            using PID step \<phi> op unfolding \<phi>_def2[OF step] by (cases a) auto
          show ?thesis proof
            show "validTrans ?trn1" unfolding ss1 using step by simp
          next
            show "consume ?trn1 vl1 vl" using \<phi> vlvl1 unfolding ss1 consume_def vl' by simp
          next
            show "\<gamma> ?trn = \<gamma> ?trn1" unfolding ss1 by simp
          next
            assume "\<gamma> ?trn" thus "g ?trn = g ?trn1" unfolding ss1 by simp
          next
            show "?\<Delta> s' vl' s' vl" using cor1 PID' op' lvl vlvl1 pPID'
            unfolding \<Delta>2_def vl' ss1 by auto
          qed
        qed
      thus ?thesis by simp
      qed
    qed
  thus ?thesis using vlvl1 by simp
  qed
qed

lemma unwind_cont_\<Delta>4: "unwind_cont \<Delta>4 {\<Delta>1,\<Delta>31,\<Delta>32,\<Delta>4}"
proof(rule, simp)
  let ?\<Delta> = "\<lambda>s vl s1 vl1. \<Delta>1 s vl s1 vl1 \<or> \<Delta>31 s vl s1 vl1 \<or> \<Delta>32 s vl s1 vl1 \<or> \<Delta>4 s vl s1 vl1"
  fix s s1 :: state and vl vl1 :: "value list"
  assume rsT: "reachNT s" and rs1: "reach s1" and "\<Delta>4 s vl s1 vl1"
  then obtain ul vll vll1 where vl: "vl = ul @ OVal False # vll" and vl1: "vl1 = ul @ OVal False # vll1"
  and rs: "reach s" and ss1: "s1 = s" and op: "open s" and PID: "PID \<in>\<in> postIDs s"
  and cor1: "corrFrom (post s1 PID) vl1" and lul: "list_all (Not \<circ> isOVal) ul"
  and BC: "BC vll vll1"
  using reachNT_reach unfolding \<Delta>4_def by blast
  have own: "owner s PID \<in> set (userIDs s)" using reach_owner_userIDs[OF rs PID] .
  have adm: "admin s \<in> set (userIDs s)" using reach_admin_userIDs[OF rs own] .
  show "iaction ?\<Delta> s vl s1 vl1 \<or>
        ((vl = [] \<longrightarrow> vl1 = []) \<and> reaction ?\<Delta> s vl s1 vl1)" (is "?iact \<or> (_ \<and> ?react)")
  proof-
    have ?react proof
      fix a :: act and ou :: out and s' :: state and vl'
      let ?trn = "Trans s a ou s'"  let ?trn1 = "Trans s1 a ou s'"
      assume step: "step s a = (ou, s')" and c: "consume ?trn vl vl'"
      have PID': "PID \<in>\<in> postIDs s'" using reach_postIDs_persist[OF PID step] .
      show "match ?\<Delta> s s1 vl1 a ou s' vl' \<or> ignore ?\<Delta> s s1 vl1 a ou s' vl'" (is "?match \<or> ?ignore")
      proof-
        have ?match proof(cases "\<phi> ?trn")
          case True note \<phi> = True
          then obtain v where vl_vl': "vl = v # vl'" and f: "f ?trn = v"
          using c unfolding consume_def \<phi>_def2 by(cases vl) auto
          show ?thesis proof(cases "ul = []")
            case False note ul = False
            then obtain ul' where ul: "ul = v # ul'" and vl': "vl' = ul' @ OVal False # vll"
            using c \<phi> f unfolding consume_def vl by (cases ul) auto
            let ?vl1' = "ul' @ OVal False # vll1"
            show ?thesis proof(cases v)
              case (PVal pst) note v = PVal
              have a: "a = Uact (uPost (owner s PID) (pass s (owner s PID)) PID pst)"
              using f_eq_PVal[OF step \<phi> f[unfolded v]] .
              have ou: "ou = outOK" using step own PID unfolding a by (auto simp: u_defs)
              have op': "open s'" using step op PID PID' \<phi>
              unfolding open_def a by (auto simp: u_defs)
              have pPID': "post s' PID = pst"
              using step \<phi> PID op f op' unfolding a by(auto simp: u_defs)
              show ?thesis proof
                show "validTrans ?trn1" unfolding ss1 using step by simp
              next
                show "consume ?trn1 vl1 ?vl1'" using \<phi>
                unfolding ss1 consume_def vl f ul vl1 vl' by simp
              next
                show "\<gamma> ?trn = \<gamma> ?trn1" unfolding ss1 by simp
              next
                assume "\<gamma> ?trn" thus "g ?trn = g ?trn1" unfolding ss1 by simp
              next
                have "\<Delta>4 s' vl' s' ?vl1'" using cor1 PID' pPID' op' vl1 ss1 lul BC
                unfolding \<Delta>4_def vl v ul vl' apply simp
                apply(rule exI[of _ ul'])
                apply(rule exI[of _ vll]) apply(rule exI[of _ vll1])
                by auto
                thus "?\<Delta> s' vl' s' ?vl1'" by simp
              qed
            next
              case (PValS aid pid) note v = PValS
              have a: "a = COMact (comSendPost (admin s) (pass s (admin s)) aid PID)"
              using f_eq_PValS[OF step \<phi> f[unfolded v]] .
              have op': "open s'" using step op PID PID' \<phi>
              unfolding open_def a by (auto simp: com_defs)
              have ou: "ou \<noteq> outErr" using \<phi> op op' unfolding \<phi>_def2[OF step] unfolding a by auto
              have pPID': "post s' PID = post s PID"
              using step \<phi> PID op f op' unfolding a by(auto simp: com_defs)
              show ?thesis proof
                show "validTrans ?trn1" unfolding ss1 using step by simp
              next
                show "consume ?trn1 vl1 ?vl1'" using \<phi>
                unfolding ss1 consume_def vl f ul vl1 vl' by simp
              next
                show "\<gamma> ?trn = \<gamma> ?trn1" unfolding ss1 by simp
              next
                assume "\<gamma> ?trn" thus "g ?trn = g ?trn1" unfolding ss1 by simp
              next
                have "\<Delta>4 s' vl' s' ?vl1'" using cor1 PID' pPID' op' vl1 ss1 lul BC
                unfolding \<Delta>4_def vl v ul vl' by auto
                thus "?\<Delta> s' vl' s' ?vl1'" by simp
              qed
            qed(insert vl lul ul, auto)
          next
            case True note ul = True
            hence f: "f ?trn = OVal False" and vl': "vl' = vll"
            using vl c f \<phi> unfolding consume_def ul by auto
            have op': "\<not> open s'" using f_eq_OVal[OF step \<phi> f] op by simp
            show ?thesis proof
              show "validTrans ?trn1" using step unfolding ss1 by simp
            next
              show "consume ?trn1 vl1 vll1" using ul \<phi> c
              unfolding vl1 vl' vl ss1 consume_def by auto
            next
              show "\<gamma> ?trn = \<gamma> ?trn1" unfolding ss1 by simp
            next
              assume "\<gamma> ?trn" note \<gamma> = this
              thus "g ?trn = g ?trn1" unfolding ss1 by simp
            next
              have pPID': "post s' PID = post s PID"
              using step \<phi> PID op op' f
              apply(cases a)
                subgoal for x1 apply(cases x1) apply(fastforce simp: s_defs)+ .
                subgoal for x2 apply(cases x2) apply(fastforce simp: c_defs)+ .
                subgoal for x3 apply(cases x3) apply(fastforce simp: d_defs)+ .
                subgoal for x4 apply(cases x4) apply(auto simp: u_defs) .
                subgoal by auto
                subgoal by auto
                subgoal for x7 apply(cases x7) apply(fastforce simp: com_defs)+ .
              done
              show "?\<Delta> s' vl' s' vll1" using BC proof cases
                case BC_PVal
                hence "\<Delta>1 s' vl' s' vll1" using PID' pPID' op' cor1 BC lul
                unfolding \<Delta>1_def vl1 ul ss1 vl' by auto
                thus ?thesis by simp
              next
                case (BC_BO Vll Vll1 Ul Ul1 Sul)
                show ?thesis proof(cases "Ul \<noteq> [] \<and> Ul1 \<noteq> []")
                  case True
                  hence "\<Delta>31 s' vl' s' vll1" using PID' pPID' op' cor1 BC BC_BO lul
                  unfolding \<Delta>31_def vl1 ul ss1 vl' apply simp
                  apply(rule exI[of _ Ul]) apply(rule exI[of _ Ul1])
                  apply(rule exI[of _ Sul])
                  apply(rule exI[of _ Vll]) apply(rule exI[of _ Vll1])
                  by auto
                  thus ?thesis by simp
                next
                  case False
                  hence 0: "Ul = []" "Ul1 = []" using BC_BO by auto
                  hence "\<Delta>32 s' vl' s' vll1" using PID' pPID' op' cor1 BC BC_BO lul
                  unfolding \<Delta>32_def vl1 ul ss1 vl' apply simp
                  apply(rule exI[of _ Sul])
                  apply(rule exI[of _ Vll]) apply(rule exI[of _ Vll1])
                  by auto
                  thus ?thesis by simp
                qed
              qed
            qed
          qed
        next
          case False note \<phi> = False
          hence vl': "vl' = vl" using c unfolding consume_def by auto
          have pPID': "post s' PID = post s PID"
            using step \<phi> PID op
            apply(cases a)
                subgoal for x1 apply(cases x1) apply(fastforce simp: s_defs)+ .
                subgoal for x2 apply(cases x2) apply(fastforce simp: c_defs)+ .
                subgoal for x3 apply(cases x3) apply(fastforce simp: d_defs)+ .
                subgoal for x4 apply(cases x4) apply(auto simp: u_defs) .
                subgoal by auto
                subgoal by auto
                subgoal for x7 apply(cases x7) apply(fastforce simp: com_defs)+ .
            done
          have op': "open s'"
            using PID step \<phi> op unfolding \<phi>_def2[OF step] by (cases a) auto
          show ?thesis proof
            show "validTrans ?trn1" unfolding ss1 using step by simp
          next
            show "consume ?trn1 vl1 vl1" using \<phi> unfolding ss1 consume_def vl' vl vl1 by simp
          next
            show "\<gamma> ?trn = \<gamma> ?trn1" unfolding ss1 by simp
          next
            assume "\<gamma> ?trn" thus "g ?trn = g ?trn1" unfolding ss1 by simp
          next
            have "\<Delta>4 s' vl' s' vl1" using cor1 PID' pPID' op' vl1 ss1 lul BC
            unfolding \<Delta>4_def vl vl' by auto
            thus "?\<Delta> s' vl' s' vl1" by simp
          qed
        qed
      thus ?thesis by simp
      qed
    qed
  thus ?thesis using vl by simp
  qed
qed

definition Gr where
"Gr =
 {
 (\<Delta>0, {\<Delta>0,\<Delta>1,\<Delta>2,\<Delta>31,\<Delta>32,\<Delta>4}),
 (\<Delta>1, {\<Delta>1,\<Delta>11}),
 (\<Delta>11, {\<Delta>11}),
 (\<Delta>2, {\<Delta>2}),
 (\<Delta>31, {\<Delta>31,\<Delta>32}),
 (\<Delta>32, {\<Delta>2,\<Delta>32,\<Delta>4}),
 (\<Delta>4, {\<Delta>1,\<Delta>31,\<Delta>32,\<Delta>4})
 }"


theorem secure: secure
apply (rule unwind_decomp_secure_graph[of Gr \<Delta>0])
unfolding Gr_def
apply (simp, smt insert_subset order_refl)
using
istate_\<Delta>0 unwind_cont_\<Delta>0 unwind_cont_\<Delta>1 unwind_cont_\<Delta>11
unwind_cont_\<Delta>31 unwind_cont_\<Delta>32 unwind_cont_\<Delta>2 unwind_cont_\<Delta>4
unfolding Gr_def by auto




end

end
