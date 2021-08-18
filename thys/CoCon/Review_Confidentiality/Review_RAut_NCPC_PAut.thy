theory Review_RAut_NCPC_PAut
imports "../Observation_Setup" Review_Value_Setup "Bounded_Deducibility_Security.Compositional_Reasoning"
begin

subsection \<open>Confidentiality from users who are not the review's author, a PC member, or an author of the paper\<close>

text \<open>We verify the following property:

\ \\
A group of users UIDs learn nothing
about the various updates to the N'th review of a paper PID
(save for the inexistence of any updates) unless/until
\begin{itemize}
\item a user in UIDs is the review's author, or
\item a user in UIDs becomes a PC member in the paper's conference
having no conflict with that paper and the
conference moves to the discussion phase, or
\item a user in UIDs become a PC member in the paper's conference
or an author of the paper and the conference moves to the notification phase
\end{itemize}
\<close>

type_synonym "value" = rcontent

fun f :: "(state,act,out) trans \<Rightarrow> value" where
"f (Trans _ (Uact (uReview cid uid p pid n rc)) _ _) = rc"
|
"f (Trans _ (UUact (uuReview cid uid p pid n rc)) _ _) = rc"

fun T :: "(state,act,out) trans \<Rightarrow> bool" where
"T (Trans _ _ ou s') =
 (\<exists> uid \<in> UIDs.
    isREVNth s' uid PID N
    \<or>
    (\<exists> cid. PID \<in>\<in> paperIDs s' cid \<and> isPC s' cid uid \<and> pref s' uid PID \<noteq> Conflict \<and> phase s' cid \<ge> disPH)
    \<or>
    (\<exists> cid. PID \<in>\<in> paperIDs s' cid \<and> isPC s' cid uid \<and> phase s' cid \<ge> notifPH)
    \<or>
    isAUT s' uid PID \<and> (\<exists> cid. PID \<in>\<in> paperIDs s' cid \<and> phase s' cid \<ge> notifPH)
 )"

declare T.simps [simp del]

definition B :: "value list \<Rightarrow> value list \<Rightarrow> bool" where
"B vl vl1 \<equiv> vl \<noteq> []"

interpretation BD_Security_IO where
istate = istate and step = step and
\<phi> = \<phi> and f = f and \<gamma> = \<gamma> and g = g and T = T and B = B
done

lemma reachNT_non_isPC_isChair:
assumes "reachNT s" and "uid \<in> UIDs"
shows
"\<not> isRevNth s cid uid PID N \<and>
 (PID \<in>\<in> paperIDs s cid \<and> isPC s cid uid \<longrightarrow>
    (pref s uid PID = Conflict \<or> phase s cid < disPH) \<and> phase s cid < notifPH) \<and>
 (PID \<in>\<in> paperIDs s cid \<and> isChair s cid uid \<longrightarrow>
    (pref s uid PID = Conflict \<or> phase s cid < disPH) \<and> phase s cid < notifPH) \<and>
 (isAut s cid uid PID \<longrightarrow> phase s cid < notifPH)"
using assms apply induct
apply (auto simp: istate_def)[]
apply(intro conjI)
  subgoal for trn apply(cases trn, simp add: T.simps reachNT_reach isAUT_def isREVNth_def)[] .
  subgoal for trn apply(cases trn, simp add: T.simps reachNT_reach isAUT_def isREVNth_def)[]
    apply (metis not_less) .
  subgoal for trn apply(cases trn, simp add: T.simps reachNT_reach isAUT_def isREVNth_def)[]
    apply (metis isChair_isPC not_less reachNT_reach reach_PairI) .
  subgoal for trn apply(cases trn, simp add: T.simps reachNT_reach isAUT_def isREVNth_def)[]
    apply (metis isAut_paperIDs not_less reachNT_reach reach_PairI) .
done

lemma T_\<phi>_\<gamma>:
assumes 1: "reachNT s" and 2: "step s a = (ou,s')" "\<phi> (Trans s a ou s')"
shows "\<not> \<gamma> (Trans s a ou s')"
using reachNT_non_isPC_isChair[OF 1] 2 unfolding T.simps \<phi>_def2
apply (auto simp: u_defs uu_defs isRev_imp_isRevNth_getReviewIndex)
by (metis isRev_imp_isRevNth_getReviewIndex)+

(* major *) lemma eqExcPID_N_step_out:
assumes s's1': "eqExcPID_N s s1"
and step: "step s a = (ou,s')" and step1: "step s1 a = (ou1,s1')"
and sT: "reachNT s" and s1: "reach s1"
and PID: "PID \<in>\<in> paperIDs s cid"
and UIDs: "userOfA a \<in> UIDs"
shows "ou = ou1"
proof-
  note s = reachNT_reach[OF sT]
  note Inv = reachNT_non_isPC_isChair[OF sT UIDs]
  note eqs = eqExcPID_N_imp[OF s's1']
  note eqs' = eqExcPID_N_imp1[OF s's1']
  note eqss = eqExcPID_N_imp2[OF s's1'] eqExcPID_N_imp3'[OF s s's1']

  note simps[simp] = c_defs u_defs uu_defs r_defs l_defs Paper_dest_conv eqExcPID_N_def eeqExcPID_N_def eqExcD
  note * = step step1 eqs eqs' eqss s s1 UIDs PID paperIDs_equals[OF s] Inv

  show ?thesis
  proof (cases a)
    case (Cact x1)
    with * show ?thesis by (cases x1; auto)
  next
    case (Uact x2)
    with * show ?thesis by (cases x2; auto)
  next
    case (UUact x3)
    with * show ?thesis by (cases x3; auto)
  next
    case (Ract x4)
    with * show ?thesis
    proof (cases x4)
      case (rMyReview x81 x82 x83 x84)
      with Ract * show ?thesis
        by clarsimp (metis getRevRole_Some_Rev_isRevNth)
    next
      case (rReviews x91 x92 x93 x94)
      with Ract * show ?thesis
        by clarsimp (metis not_less)
    next
      case (rFinalReviews x121 x122 x123 x124)
      with Ract * show ?thesis
        by clarsimp (metis not_less)
    qed auto
  next
    case (Lact x5)
    with * show ?thesis by (cases x5; auto; presburger)
  qed
qed

definition \<Delta>1 :: "state \<Rightarrow> value list \<Rightarrow> state \<Rightarrow> value list \<Rightarrow> bool" where
"\<Delta>1 s vl s1 vl1 \<equiv>
 (\<forall> cid. PID \<in>\<in> paperIDs s cid \<longrightarrow> phase s cid < revPH) \<and> s = s1 \<and> B vl vl1"

definition \<Delta>2 :: "state \<Rightarrow> value list \<Rightarrow> state \<Rightarrow> value list \<Rightarrow> bool" where
"\<Delta>2 s vl s1 vl1 \<equiv>
 \<exists> cid.
   PID \<in>\<in> paperIDs s cid \<and> phase s cid = revPH \<and>
   \<not> (\<exists> uid. isREVNth s uid PID N) \<and>
   s = s1 \<and> B vl vl1"

(* Note: In the similar property from discussion confidentiality we have only 3 non-exit phases
instead of 4, not having a phase like \<Delta>2: this is because there the agent affecting the documents (chairs),
must have been assigned in a previous phase; here reviewers are assigned in the same phase
in which they can edit.   *)

definition \<Delta>3 :: "state \<Rightarrow> value list \<Rightarrow> state \<Rightarrow> value list \<Rightarrow> bool" where
"\<Delta>3 s vl s1 vl1 \<equiv>
 \<exists> cid uid. PID \<in>\<in> paperIDs s cid \<and> phase s cid = revPH \<and> isREVNth s uid PID N \<and> eqExcPID_N s s1"

definition \<Delta>4 :: "state \<Rightarrow> value list \<Rightarrow> state \<Rightarrow> value list \<Rightarrow> bool" where
"\<Delta>4 s vl s1 vl1 \<equiv>
 \<exists> cid. PID \<in>\<in> paperIDs s cid \<and> phase s cid > revPH \<and> eqExcPID_N s s1 \<and> vl1 = []"

definition \<Delta>e :: "state \<Rightarrow> value list \<Rightarrow> state \<Rightarrow> value list \<Rightarrow> bool" where
"\<Delta>e s vl s1 vl1 \<equiv>
 vl \<noteq> [] \<and>
 (\<exists> cid. PID \<in>\<in> paperIDs s cid \<and> phase s cid > revPH \<and> \<not> (\<exists> uid. isREVNth s uid PID N))"

lemma istate_\<Delta>1:
assumes B: "B vl vl1"
shows "\<Delta>1 istate vl istate vl1"
using B unfolding \<Delta>1_def B_def istate_def by auto

lemma unwind_cont_\<Delta>1: "unwind_cont \<Delta>1 {\<Delta>1,\<Delta>2,\<Delta>e}"
proof(rule, simp)
  let ?\<Delta> = "\<lambda>s vl s1 vl1. \<Delta>1 s vl s1 vl1 \<or> \<Delta>2 s vl s1 vl1 \<or> \<Delta>e s vl s1 vl1"
  fix s s1 :: state and vl vl1 :: "value list"
  assume rsT: "reachNT s" and rs1: "reach s1" and "\<Delta>1 s vl s1 vl1"
  hence rs: "reach s" and ss1: "s1 = s" and vl: "vl \<noteq> []"
  and PID_ph: "\<And> cid. PID \<in>\<in> paperIDs s cid \<Longrightarrow> phase s cid < revPH"
  using reachNT_reach unfolding \<Delta>1_def B_def by auto
  show "iaction ?\<Delta> s vl s1 vl1 \<or>
        ((vl = [] \<longrightarrow> vl1 = []) \<and> reaction ?\<Delta> s vl s1 vl1)" (is "?iact \<or> (_ \<and> ?react)")
  proof-
    have ?react proof
      fix a :: act and ou :: out and s' :: state and vl'
      let ?trn = "Trans s a ou s'"  let ?trn1 = "Trans s1 a ou s'"
      assume step: "step s a = (ou, s')" and T: "\<not> T ?trn" and c: "consume ?trn vl vl'"
      have \<phi>: "\<not> \<phi> ?trn"
        apply(cases a)
        subgoal by simp
        subgoal for x2 apply(cases x2) using step PID_ph by (fastforce simp: u_defs)+
        subgoal for x3 apply(cases x3) using step PID_ph by (fastforce simp: uu_defs)+
        by simp_all
      hence vl': "vl' = vl" using c unfolding consume_def by auto
      show "match ?\<Delta> s s1 vl1 a ou s' vl' \<or> ignore ?\<Delta> s s1 vl1 a ou s' vl'" (is "?match \<or> ?ignore")
      proof-
        have ?match proof
          show "validTrans ?trn1" unfolding ss1 using step by simp
        next
          show "consume ?trn1 vl1 vl1" unfolding consume_def ss1 using \<phi> by auto
        next
          show "\<gamma> ?trn = \<gamma> ?trn1" unfolding ss1 by simp
        next
          assume "\<gamma> ?trn" thus "g ?trn = g ?trn1" unfolding ss1 by simp
        next
          show "?\<Delta> s' vl' s' vl1"
          proof(cases "\<exists> cid. PID \<in>\<in> paperIDs s cid")
            case False note PID = False
            have PID_ph': "\<And> cid. PID \<in>\<in> paperIDs s' cid \<Longrightarrow> phase s' cid < revPH" using PID step rs
            apply(cases a)
              subgoal for _ x1 apply(cases x1) apply(fastforce simp: c_defs)+ .
              subgoal for _ x2 apply(cases x2) apply(fastforce simp: u_defs)+ .
              subgoal for _ x3 apply(cases x3) apply(fastforce simp: uu_defs)+ .
              by auto
            hence "\<Delta>1 s' vl' s' vl1" unfolding \<Delta>1_def B_def vl' using PID_ph' vl by auto
            thus ?thesis by auto
          next
            case True
            then obtain CID where PID: "PID \<in>\<in> paperIDs s CID" by auto
            hence ph: "phase s CID < revPH" using PID_ph by auto
            have PID': "PID \<in>\<in> paperIDs s' CID" by (metis PID paperIDs_mono step)
            show ?thesis
            proof(cases "phase s' CID < revPH")
              case True note ph' = True
              hence "\<Delta>1 s' vl' s' vl1" unfolding \<Delta>1_def B_def vl' using vl ph' PID' apply auto
              by (metis reach_PairI paperIDs_equals rs step)
              thus ?thesis by auto
            next
              case False note ph' = False
              have "\<not> (\<exists> uid. isRevNth s CID uid PID N)" using rs ph isRevNth_geq_revPH by fastforce
              hence ph_isRev': "phase s' CID = revPH \<and> \<not> (\<exists> uid. isRevNth s' CID uid PID N)"
              using ph' ph PID step rs
              apply(cases a)
                subgoal for x1 apply(cases x1) apply(fastforce simp: c_defs)+ .
                subgoal for x2 apply(cases x2) apply(fastforce simp: u_defs)+ .
                subgoal for x3 apply(cases x3) apply(fastforce simp: uu_defs)+ .
              by auto
              hence "\<not> (\<exists> uid. isREVNth s' uid PID N)"
              by (metis PID' isREVNth_imp_isRevNth reach_PairI rs1 ss1 step)
              hence "\<Delta>2 s' vl' s' vl1"
              unfolding \<Delta>2_def B_def isREVNth_def vl' using vl ph' PID' ph_isRev' by auto
              thus ?thesis by auto
            qed
          qed
        qed
        thus ?thesis by simp
      qed
    qed
    thus ?thesis using vl by auto
  qed
qed

lemma unwind_cont_\<Delta>2: "unwind_cont \<Delta>2 {\<Delta>2,\<Delta>3,\<Delta>e}"
proof(rule, simp)
  let ?\<Delta> = "\<lambda>s vl s1 vl1. \<Delta>2 s vl s1 vl1 \<or> \<Delta>3 s vl s1 vl1 \<or> \<Delta>e s vl s1 vl1"
  fix s s1 :: state and vl vl1 :: "value list"
  assume rsT: "reachNT s" and rs1: "reach s1" and "\<Delta>2 s vl s1 vl1"
  then obtain CID where rs: "reach s" and ph: "phase s CID = revPH" (is "?ph = _")
  and PID: "PID \<in>\<in> paperIDs s CID" and ss1: "s1 = s"
  and vl: "vl \<noteq> []" and uid: "\<not> (\<exists> uid. isREVNth s uid PID N)"
  using reachNT_reach unfolding \<Delta>2_def B_def by auto
  hence uid: "\<not> (\<exists> uid. isRevNth s CID uid PID N)" by (metis isREVNth_def)
  show "iaction ?\<Delta> s vl s1 vl1 \<or>
        ((vl = [] \<longrightarrow> vl1 = []) \<and> reaction ?\<Delta> s vl s1 vl1)" (is "?iact \<or> (_ \<and> ?react)")
  proof-
    have ?react proof
      fix a :: act and ou :: out and s' :: state and vl'
      let ?trn = "Trans s a ou s'"  let ?trn1 = "Trans s1 a ou s'"
      let ?ph' = "phase s' CID"
      assume step: "step s a = (ou, s')" and T: "\<not> T ?trn" and c: "consume ?trn vl vl'"
      have \<phi>: "\<not> \<phi> ?trn"
        apply(cases a)
        subgoal by simp
        subgoal for x2 apply(cases x2)
          using step ph uid apply (auto simp: u_defs isRev_def3)
          by (metis PID paperIDs_equals rs)
        subgoal for x3 apply(cases x3)
          using step ph apply (auto simp: uu_defs)
          by (metis PID n_not_Suc_n paperIDs_equals rs)
        by simp_all
      hence vl': "vl' = vl" using c unfolding consume_def by auto
      have PID': "PID \<in>\<in> paperIDs s' CID" by (metis paperIDs_mono step PID)
      show "match ?\<Delta> s s1 vl1 a ou s' vl' \<or> ignore ?\<Delta> s s1 vl1 a ou s' vl'" (is "?match \<or> ?ignore")
      proof-
        have ?match proof
          show "validTrans ?trn1" unfolding ss1 using step by simp
        next
          show "consume ?trn1 vl1 vl1" unfolding consume_def ss1 using \<phi> by auto
        next
          show "\<gamma> ?trn = \<gamma> ?trn1" unfolding ss1 by simp
        next
          assume "\<gamma> ?trn" thus "g ?trn = g ?trn1" unfolding ss1 by simp
        next
          show "?\<Delta> s' vl' s' vl1"
          proof(cases "?ph' = revPH")
            case True note ph' = True
            show ?thesis
            proof(cases "\<exists> uid. isRevNth s' CID uid PID N")
              case False
              hence "\<not> (\<exists> uid. isREVNth s' uid PID N)"
              by (metis reach_PairI PID' isREVNth_imp_isRevNth rs1 ss1 step)
              hence "\<Delta>2 s' vl' s' vl1" unfolding \<Delta>2_def B_def vl' using vl ph' PID' by auto
              thus ?thesis by auto
            next
              case True  hence "\<exists> uid. isREVNth s' uid PID N" by (metis isREVNth_def)
              hence "\<Delta>3 s' vl' s' vl1" unfolding \<Delta>3_def vl' using vl ph' PID' by auto
              thus ?thesis by auto
            qed
          next
            case False hence 1: "?ph' > revPH \<and> \<not> (\<exists> uid. isRevNth s' CID uid PID N)"
              using PID ph uid step rs
              apply(cases a)
              subgoal for x1 apply(cases x1) apply(fastforce simp: c_defs)+ .
              subgoal for x2 apply(cases x2) apply(fastforce simp: u_defs)+ .
              subgoal for x3 apply(cases x3) apply(fastforce simp: uu_defs)+ .
              by auto
            hence "\<not> (\<exists> uid. isREVNth s' uid PID N)"
            by (metis reach_PairI PID' isREVNth_imp_isRevNth rs1 ss1 step)
            hence "\<Delta>e s' vl' s' vl1" unfolding \<Delta>e_def vl' using vl PID' 1 by auto
            thus ?thesis by auto
          qed
        qed
        thus ?thesis by simp
      qed
    qed
    thus ?thesis using vl by simp
  qed
qed

lemma unwind_cont_\<Delta>3: "unwind_cont \<Delta>3 {\<Delta>3,\<Delta>4,\<Delta>e}"
proof(rule, simp)
  let ?\<Delta> = "\<lambda>s vl s1 vl1. \<Delta>3 s vl s1 vl1 \<or> \<Delta>4 s vl s1 vl1 \<or> \<Delta>e s vl s1 vl1"
  fix s s1 :: state and vl vl1 :: "value list"
  assume rsT: "reachNT s" and rs1: "reach s1" and "\<Delta>3 s vl s1 vl1"
  then obtain CID uid where uuid: "isREVNth s uid PID N"
  and rs: "reach s" and ph: "phase s CID = revPH" (is "?ph = _") and ss1: "eqExcPID_N s s1"
  and PID: "PID \<in>\<in> paperIDs s CID" using reachNT_reach unfolding \<Delta>3_def by blast
  hence uid: "isRevNth s CID uid PID N" by (metis isREVNth_imp_isRevNth)
  hence uid_notin: "uid \<notin> UIDs" using reachNT_non_isPC_isChair[OF rsT] by auto
  show "iaction ?\<Delta> s vl s1 vl1 \<or>
        ((vl = [] \<longrightarrow> vl1 = []) \<and> reaction ?\<Delta> s vl s1 vl1)" (is "?iact \<or> (_ \<and> ?react)")
  proof(cases vl1)
    case (Cons v1 vl1') note vl1 = Cons
    have uid1: "isRevNth s CID uid PID N" using ss1 uid unfolding eqExcPID_N_def by auto
    define a1 where "a1 \<equiv> Uact (uReview CID uid (pass s uid) PID N v1)"
    obtain s1' ou1 where step1: "step s1 a1 = (ou1,s1')" by (metis prod.exhaust)
    let ?trn1 = "Trans s1 a1 ou1 s1'"
    have s1s1': "eqExcPID_N s1 s1'" using a1_def step1 uReview_uuReview_step_eqExcPID_N by blast
    have ss1': "eqExcPID_N s s1'" using eqExcPID_N_trans[OF ss1 s1s1'] .
    hence many_s1': "PID \<in>\<in> paperIDs s1' CID" "isRevNth s1' CID uid PID N"
    "phase s1' CID = revPH" "pass s1' uid = pass s uid"
    using uid PID ph unfolding eqExcPID_N_def by auto
    hence more_s1': "uid \<in>\<in> userIDs s1'" "CID \<in>\<in> confIDs s1'"
    by (metis paperIDs_confIDs reach_PairI roles_userIDs rs1 step1 many_s1'(1))+
    have f: "f ?trn1 = v1" unfolding a1_def by simp
    have rs1': "reach s1'" using rs1 step1 by (auto intro: reach_PairI)
    have ou1: "ou1 = outOK"
    using step1 uid1 ph unfolding a1_def apply ( simp add: u_defs uu_defs many_s1' more_s1' isRev_def2)
    by (metis isRevNth_getReviewIndex many_s1' rs1)
    have ?iact proof
      show "step s1 a1 = (ou1,s1')" by fact
    next
      show \<phi>: "\<phi> ?trn1" using ou1 unfolding a1_def by simp
      thus "consume ?trn1 vl1 vl1'" using f unfolding consume_def vl1 by simp
    next
      show "\<not> \<gamma> ?trn1" by (simp add: a1_def uid_notin)
    next
      have "\<Delta>3 s vl s1' vl1'" unfolding \<Delta>3_def using ph PID ss1' uuid by auto
      thus "?\<Delta> s vl s1' vl1'" by simp
    qed
    thus ?thesis by auto
  next
    case Nil note vl1 = Nil
    have ?react proof
      fix a :: act and ou :: out and s' :: state and vl'
      let ?trn = "Trans s a ou s'"
      let ?ph' = "phase s' CID"
      assume step: "step s a = (ou, s')" and T: "\<not> T ?trn" and c: "consume ?trn vl vl'"
      have PID': "PID \<in>\<in> paperIDs s' CID" using PID rs by (metis paperIDs_mono step)
      have uid': "isRevNth s' CID uid PID N"
      using uid step rs ph PID isRevNth_persistent by auto
      have uuid': "isREVNth s' uid PID N" by (metis isREVNth_def uid')
      show "match ?\<Delta> s s1 vl1 a ou s' vl' \<or> ignore ?\<Delta> s s1 vl1 a ou s' vl'" (is "?match \<or> ?ignore")
      proof(cases "\<phi> ?trn")
        case False note \<phi> = False
        have vl: "vl' = vl" using c \<phi> unfolding consume_def by (cases vl) auto
        obtain ou1 and s1' where step1: "step s1 a = (ou1,s1')" by (metis prod.exhaust)
        let ?trn1 = "Trans s1 a ou1 s1'"
        have s's1': "eqExcPID_N s' s1'" using eqExcPID_N_step[OF ss1 step step1] .
        have \<phi>1: "\<not> \<phi> ?trn1" using \<phi> unfolding eqExcPID_N_step_\<phi>[OF ss1 step step1] .
        have ?match proof
          show "validTrans ?trn1" using step1 by simp
        next
          show "consume ?trn1 vl1 vl1" unfolding consume_def using \<phi>1 by auto
        next
          show "\<gamma> ?trn = \<gamma> ?trn1" unfolding ss1 by simp
        next
          assume "\<gamma> ?trn" thus "g ?trn = g ?trn1"
          using eqExcPID_N_step_out[OF ss1 step step1 rsT rs1 PID] by simp
        next
          show "?\<Delta> s' vl' s1' vl1"
          proof(cases "?ph' = revPH")
            case True
            hence "\<Delta>3 s' vl' s1' vl1" using PID' s's1' uuid' unfolding \<Delta>3_def by auto
            thus ?thesis by auto
          next
            case False hence "?ph' > revPH"
            using ph rs step by (metis le_less phase_increases2 prod.sel(2))
            hence "\<Delta>4 s' vl' s1' vl1" using s's1' PID' unfolding \<Delta>4_def vl1 by auto
            thus ?thesis by auto
          qed
        qed
        thus ?thesis by simp
      next
        case True note \<phi> = True
        have s's: "eqExcPID_N s' s" using eqExcPID_N_sym[OF \<phi>_step_eqExcPID_N[OF \<phi> step]] .
        have s's1: "eqExcPID_N s' s1" using eqExcPID_N_trans[OF s's ss1] .
        have ?ignore proof
          show "\<not> \<gamma> ?trn" using T_\<phi>_\<gamma> \<phi> rsT step by auto
        next
          show "?\<Delta> s' vl' s1 vl1"
          proof(cases "?ph' = revPH")
            case True
            hence "\<Delta>3 s' vl' s1 vl1" using s's1 PID' uuid' unfolding \<Delta>3_def by auto
            thus ?thesis by auto
          next
            case False hence "?ph' > revPH"
            using ph rs step using eqExcPID_N_def s's by auto
            hence "\<Delta>4 s' vl' s1 vl1" using s's1 PID' unfolding \<Delta>4_def vl1 by auto
            thus ?thesis by auto
          qed
        qed
        thus ?thesis by auto
      qed
    qed
    thus ?thesis using vl1 by auto
  qed
qed

lemma unwind_cont_\<Delta>4: "unwind_cont \<Delta>4 {\<Delta>4,\<Delta>e}"
proof(rule, simp)
  let ?\<Delta> = "\<lambda>s vl s1 vl1. \<Delta>4 s vl s1 vl1 \<or> \<Delta>e s vl s1 vl1"
  fix s s1 :: state and vl vl1 :: "value list"
  assume rsT: "reachNT s" and rs1: "reach s1" and "\<Delta>4 s vl s1 vl1"
  then obtain CID where rs: "reach s" and ph: "phase s CID > revPH" (is "?ph > _")
  and PID: "PID \<in>\<in> paperIDs s CID" and ss1: "eqExcPID_N s s1" and vl1: "vl1 = []"
  using reachNT_reach unfolding \<Delta>4_def by auto
  show "iaction ?\<Delta> s vl s1 vl1 \<or>
        ((vl = [] \<longrightarrow> vl1 = []) \<and> reaction ?\<Delta> s vl s1 vl1)" (is "?iact \<or> (_ \<and> ?react)")
  proof-
    have "?react"
    proof
      fix a :: act and ou :: out and s' :: state and vl'
      let ?trn = "Trans s a ou s'"
      let ?ph' = "phase s' CID"
      assume step: "step s a = (ou, s')" and T: "\<not> T ?trn" and c: "consume ?trn vl vl'"
      have PID': "PID \<in>\<in> paperIDs s' CID" using PID rs by (metis paperIDs_mono step)
      have ph': "phase s' CID > revPH" using ph rs by (meson less_le_trans local.step phase_increases)
      show "match ?\<Delta> s s1 vl1 a ou s' vl' \<or> ignore ?\<Delta> s s1 vl1 a ou s' vl'" (is "?match \<or> ?ignore")
      proof(cases "\<phi> ?trn")
        case False note \<phi> = False
        have vl: "vl' = vl" using c \<phi> unfolding consume_def by (cases vl) auto
        obtain ou1 and s1' where step1: "step s1 a = (ou1,s1')" by (metis prod.exhaust)
        let ?trn1 = "Trans s1 a ou1 s1'"
        have s's1': "eqExcPID_N s' s1'" using eqExcPID_N_step[OF ss1 step step1] .
        have \<phi>1: "\<not> \<phi> ?trn1" using \<phi> unfolding eqExcPID_N_step_\<phi>[OF ss1 step step1] .
        have ?match proof
          show "validTrans ?trn1" using step1 by simp
        next
          show "consume ?trn1 vl1 vl1" unfolding consume_def using \<phi>1 by auto
        next
          show "\<gamma> ?trn = \<gamma> ?trn1" unfolding ss1 by simp
        next
          assume "\<gamma> ?trn" thus "g ?trn = g ?trn1"
          using eqExcPID_N_step_out[OF ss1 step step1 rsT rs1 PID] by simp
        next
          have "\<Delta>4 s' vl' s1' vl1" using ph' PID' s's1' unfolding \<Delta>4_def vl1 by auto
          thus "?\<Delta> s' vl' s1' vl1" by simp
        qed
        thus ?thesis by simp
      next
        case True note \<phi> = True
        have s's: "eqExcPID_N s' s" using eqExcPID_N_sym[OF \<phi>_step_eqExcPID_N[OF \<phi> step]] .
        have s's1: "eqExcPID_N s' s1" using eqExcPID_N_trans[OF s's ss1] .
        have ?ignore proof
          show "\<not> \<gamma> ?trn" using T_\<phi>_\<gamma> \<phi> rsT step by auto
        next
          have "\<Delta>4 s' vl' s1 vl1" using s's1 PID' ph' vl1 unfolding \<Delta>4_def by auto
          thus "?\<Delta> s' vl' s1 vl1" by auto
        qed
        thus ?thesis by simp
      qed
    qed
    thus ?thesis using vl1 by simp
  qed
qed

(* Exit arguments: *)
definition K1exit where
"K1exit cid s \<equiv> PID \<in>\<in> paperIDs s cid \<and> phase s cid > revPH \<and> \<not> (\<exists> uid. isRevNth s cid uid PID N)"

lemma invarNT_K1exit: "invarNT (K1exit cid)"
unfolding invarNT_def apply (safe dest!: reachNT_reach)
  subgoal for _ a apply(cases a)
    subgoal for x1 apply(cases x1) apply (fastforce simp add: c_defs K1exit_def geq_noPH_confIDs)+ .
    subgoal for x2 apply(cases x2) apply (fastforce simp add: u_defs K1exit_def paperIDs_equals)+ .
    subgoal for x3 apply(cases x3) apply (fastforce simp add: uu_defs K1exit_def)+ .
    by auto
  done

lemma noVal_K1exit: "noVal (K1exit cid) v"
apply(rule no\<phi>_noVal)
unfolding no\<phi>_def apply safe
  subgoal for _ a apply(cases a)
    subgoal by (fastforce simp add: c_defs K1exit_def)
    subgoal for x2 apply(cases x2) apply (auto simp add: u_defs K1exit_def)
      apply (metis less_not_refl paperIDs_equals reachNT_reach) .
    subgoal for x3 apply(cases x3) apply (auto simp add: uu_defs K1exit_def)
      apply (metis isRev_def3 paperIDs_equals reachNT_reach) .
    by auto
  done

lemma unwind_exit_\<Delta>e: "unwind_exit \<Delta>e"
proof
  fix s s1 :: state and vl vl1 :: "value list"
  assume rsT: "reachNT s" and rs1: "reach s1" and \<Delta>e: "\<Delta>e s vl s1 vl1"
  hence vl: "vl \<noteq> []" using reachNT_reach unfolding \<Delta>e_def by auto
  then obtain CID where "K1exit CID s" using \<Delta>e unfolding K1exit_def \<Delta>e_def isREVNth_def by auto
  thus "vl \<noteq> [] \<and> exit s (hd vl)" apply(simp add: vl)
  by (metis rsT exitI2 invarNT_K1exit noVal_K1exit)
qed

theorem secure: secure
apply(rule unwind_decomp4_secure[of \<Delta>1 \<Delta>2 \<Delta>e \<Delta>3 \<Delta>4])
using
istate_\<Delta>1
unwind_cont_\<Delta>1 unwind_cont_\<Delta>2 unwind_cont_\<Delta>3 unwind_cont_\<Delta>4
unwind_exit_\<Delta>e
by auto

end
