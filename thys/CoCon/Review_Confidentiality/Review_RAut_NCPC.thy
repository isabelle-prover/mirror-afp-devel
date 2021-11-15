theory Review_RAut_NCPC
imports "../Observation_Setup" Review_Value_Setup "Bounded_Deducibility_Security.Compositional_Reasoning"
begin

subsection \<open>Confidentiality protection from users who are not the review's author or a PC member\<close>

text \<open>We verify the following property:

\ \\
A group of users UIDs learn nothing
about the various updates of the N'th review of a paper PID
except for the last edited version before notification
unless/until one of the following holds:
\begin{itemize}
\item a user in UIDs is the review's author, or
\item a user in UIDs becomes a PC member in the paper's conference
having no conflict with that paper, and the conference moves to the discussion phase.
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
 )"

declare T.simps [simp del]

definition B :: "value list \<Rightarrow> value list \<Rightarrow> bool" where
"B vl vl1 \<equiv> vl \<noteq> [] \<and> vl1 \<noteq> [] \<and> last vl = last vl1"

interpretation BD_Security_IO where
istate = istate and step = step and
\<phi> = \<phi> and f = f and \<gamma> = \<gamma> and g = g and T = T and B = B
done

lemma reachNT_non_isRevNth_isPC_isChair:
assumes "reachNT s" and "uid \<in> UIDs"
shows
"\<not> isRevNth s cid uid PID N \<and>
 (PID \<in>\<in> paperIDs s cid \<and> isPC s cid uid \<longrightarrow> pref s uid PID = Conflict \<or> phase s cid < disPH) \<and>
 (PID \<in>\<in> paperIDs s cid \<and> isChair s cid uid \<longrightarrow> pref s uid PID = Conflict \<or> phase s cid < disPH)"
  using assms
  apply induct
   apply (auto simp: istate_def)[]
  apply(intro conjI)
  subgoal for trn apply(cases trn, auto simp: T.simps reachNT_reach isREVNth_def)[] .
  subgoal by (metis T.elims(3) not_le_imp_less tgtOf_simps)
  by (metis T.elims(3) isChair_isPC not_le_imp_less reach.Step reachNT_reach tgtOf_simps)

(* important: *) lemma T_\<phi>_\<gamma>:
assumes 1: "reachNT s" and 2: "step s a = (ou,s')" "\<phi> (Trans s a ou s')"
shows "\<not> \<gamma> (Trans s a ou s')"
using reachNT_non_isRevNth_isPC_isChair[OF 1] 2 unfolding T.simps \<phi>_def2
apply (auto simp add: u_defs uu_defs) by (metis isRev_imp_isRevNth_getReviewIndex)+

(* major *) lemma eqExcPID_N_step_out:
assumes s's1': "eqExcPID_N s s1"
and step: "step s a = (ou,s')" and step1: "step s1 a = (ou1,s1')"
and sP: "reachNT s" and s1: "reach s1"
and PID: "PID \<in>\<in> paperIDs s cid"
and ph: "phase s cid = revPH \<or> phase s cid = disPH"
and UIDs: "userOfA a \<in> UIDs"
shows "ou = ou1"
proof-
  note Inv = reachNT_non_isRevNth_isPC_isChair[OF sP UIDs]
  note eqs = eqExcPID_N_imp[OF s's1']
  note eqs' = eqExcPID_N_imp1[OF s's1']
  note eqss = eqExcPID_N_imp2[OF s's1']
  note s = reachNT_reach[OF sP]

  note simps[simp] = c_defs u_defs uu_defs r_defs l_defs Paper_dest_conv eqExcPID_N_def eeqExcPID_N_def eqExcD
  note * = step step1 eqs eqs' s s1 PID UIDs ph paperIDs_equals[OF s] Inv

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
        by clarsimp (metis eqExcPID_N_imp3' getRevRole_Some_Rev_isRevNth s's1')
    next
      case (rReviews x91 x92 x93 x94)
      with Ract * show ?thesis
        by clarsimp (metis eqss not_less)
    next
      case (rFinalReviews x121 x122 x123 x124)
      with Ract * show ?thesis
        by clarsimp (metis Suc_leD Suc_n_not_le_n)
    qed auto
  next
    case (Lact x5)
    with * show ?thesis by (cases x5; auto; presburger)
  qed
qed

(* major *) lemma eqExcPID_N2_step_out:
assumes ss1: "eqExcPID_N2 s s1"
and step: "step s a = (ou,s')" and step1: "step s1 a = (ou1,s1')"
and sP: "reachNT s" and s1: "reach s1"
and r: "isRevNth s cid uid PID N"
and ph: "phase s cid \<ge> revPH"
and UIDs: "userOfA a \<in> UIDs"
and decs_exit: "(reviewsPaper (paper s PID))!N \<noteq> [] \<and> (reviewsPaper (paper s1 PID))!N \<noteq> []"
shows "ou = ou1"
proof-
  note s = reachNT_reach[OF sP]
  note Inv = reachNT_non_isRevNth_isPC_isChair[OF sP UIDs]
  note eqs = eqExcPID_N2_imp[OF ss1]
  note eqs' = eqExcPID_N2_imp1[OF ss1]
  note eqss = eqExcPID_N2_imp2[OF ss1] eqExcPID_N2_imp3'[OF s ss1] eqExcPID_N2_imp33[OF ss1]

  have PID: "PID \<in>\<in> paperIDs s cid" using r by (metis isRevNth_paperIDs s)
  have PID1: "PID \<in>\<in> paperIDs s1 cid" using PID ss1 unfolding eqExcPID_N2_def by auto
  have r1: "isRevNth s1 cid uid PID N" by (metis eqs r)
  hence decs_exit': "(reviewsPaper (paper s' PID))!N \<noteq> [] \<and>
                     (reviewsPaper (paper s1' PID))!N \<noteq> []"
  using nonempty_reviews_persist s s1 PID PID1 r r1 decs_exit step step1 by metis+

  note simps[simp] = c_defs u_defs uu_defs r_defs l_defs Paper_dest_conv eqExcPID_N2_def eeqExcPID_N2_def eqExcD2

  have "eqExcD2 (paper s PID) (paper s1 PID)"
  using eqExcPID_N2_imp[OF ss1] eeqExcPID_N2_imp by blast
  hence 1: "hd (reviewsPaper (paper s PID) ! N) =
            hd (reviewsPaper (paper s1 PID) ! N)"
  unfolding eqExcD2 eqExcNth2_def by auto

  { fix cid uid p pid assume a: "a = Ract (rFinalReviews cid uid p pid)"
    have ?thesis using step step1 eqExcPID_N2_imp[OF ss1]
      unfolding a
      apply clarsimp
      apply(intro nth_equalityI)
      subgoal by simp
      subgoal for i apply (cases "i \<noteq> N")
        subgoal by simp (smt eqExcPID_N2_imp3 getNthReview_def ss1)
        by (auto split: list.splits)
      subgoal for i ia
        apply (cases "pid = PID")
        subgoal
          apply(cases "reviewsPaper (paper s' PID) ! i")
          subgoal apply simp
            by (smt decs_exit eqExcPID_N2_imp3 getNthReview_def list.simps(4) nth_Cons_0 ss1)
          subgoal apply(cases "reviewsPaper (paper s1' PID) ! i ")
            subgoal apply simp
              by (metis (no_types, lifting) decs_exit eqExcD2 eqExcNth2_def neq_Nil_conv)
            subgoal apply simp
              by (metis (no_types, lifting) eqExcD2 eqExcNth2_def list.sel(1)) . .
        subgoal by simp . .
  } note this[simp]

  note * = step step1 eqs eqs' s s1 PID PID1 r r1 UIDs ph paperIDs_equals[OF s] Inv

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
        by clarsimp (metis eqss(2) getRevRole_Some_Rev_isRevNth)
    next
      case (rReviews x91 x92 x93 x94)
      with Ract * show ?thesis
        by clarsimp (metis eqss(1) not_less)
    qed auto
  next
    case (Lact x5)
    with * show ?thesis by (cases x5; auto; presburger)
  qed
qed

lemma eqExcPID_N_step_eqExcPID_N2:
assumes rs: "reach s"
and a: "a = Uact (uReview cid uid p PID N rc) \<or>
        a = UUact (uuReview cid uid p PID N rc)" (is "?L \<or> ?R")
and ss1: "eqExcPID_N s s1"
and step: "step s a = (outOK,s')" and step1: "step s1 a = (outOK,s1')"
shows "eqExcPID_N2 s' s1'"
using a proof
  assume a: ?L
  have "isRevNth s cid uid PID N" using step unfolding a apply(simp add: u_defs uu_defs)
  by (metis isRev_imp_isRevNth_getReviewIndex)
  hence N: "N < length (reviewsPaper (paper s PID))"
  using rs by (metis isRevNth_less_length)
  hence N1: "N < length (reviewsPaper (paper s1 PID))"
  using ss1 unfolding eqExcPID_N_def eeqExcPID_N_def eqExcD eqExcNth_def by auto
  have "eqExcPID_N s' s1'" using assms by (metis eqExcPID_N_step)
  moreover have "hd (reviewsPaper (paper s' PID) ! N) = hd (reviewsPaper (paper s1' PID) ! N)"
  using step step1 N N1 unfolding a by(auto simp add: u_defs uu_defs)
  ultimately show ?thesis
  unfolding eqExcPID_N_def eqExcPID_N2_def eeqExcPID_N_def eeqExcPID_N2_def eqExcD2 eqExcD
  eqExcNth_def eqExcNth2_def by auto
next
  assume a: ?R
  have "isRevNth s cid uid PID N" using step unfolding a apply(simp add: u_defs uu_defs)
  by (metis isRev_imp_isRevNth_getReviewIndex)
  hence N: "N < length (reviewsPaper (paper s PID))"
  using rs by (metis isRevNth_less_length)
  hence N1: "N < length (reviewsPaper (paper s1 PID))"
  using ss1 unfolding eqExcPID_N_def eeqExcPID_N_def eqExcD eqExcNth_def by auto
  have "eqExcPID_N s' s1'" using assms by (metis eqExcPID_N_step)
  moreover have "hd (reviewsPaper (paper s' PID) ! N) = hd (reviewsPaper (paper s1' PID) ! N)"
  using step step1 N N1 unfolding a by(auto simp add: u_defs uu_defs)
  ultimately show ?thesis
  unfolding eqExcPID_N_def eqExcPID_N2_def eeqExcPID_N_def eeqExcPID_N2_def eqExcD2 eqExcD
  eqExcNth_def eqExcNth2_def by auto
qed

(* major *) lemma eqExcPID_N_step_\<phi>_eqExcPID_N2:
assumes rs: "reach s"
and ss1: "eqExcPID_N s s1"
and step: "step s a = (ou,s')" and step1: "step s1 a = (ou1,s1')"
and \<phi>: "\<phi> (Trans s a ou s')"
shows "eqExcPID_N2 s' s1'"
proof-
  obtain cid uid p rc where
  a: "a = Uact (uReview cid uid p PID N rc) \<or>
      a = UUact (uuReview cid uid p PID N rc)" (is "?L \<or> ?R")
  and ou: "ou = outOK"
  using \<phi> unfolding \<phi>_def2 by blast
  have \<phi>1: "\<phi> (Trans s1 a ou1 s1')" using \<phi> ss1 by (metis eqExcPID_N_step_\<phi>_imp step step1)
  hence ou1: "ou1 = outOK" using \<phi> unfolding \<phi>_def2 by auto
  show ?thesis using eqExcPID_N_step_eqExcPID_N2[OF rs a ss1 step[unfolded ou] step1[unfolded ou1]] .
qed

definition \<Delta>1 :: "state \<Rightarrow> value list \<Rightarrow> state \<Rightarrow> value list \<Rightarrow> bool" where
"\<Delta>1 s vl s1 vl1 \<equiv>
 (\<forall> cid. PID \<in>\<in> paperIDs s cid \<longrightarrow> phase s cid < revPH)  \<and>
 s = s1 \<and> B vl vl1"

definition \<Delta>2 :: "state \<Rightarrow> value list \<Rightarrow> state \<Rightarrow> value list \<Rightarrow> bool" where
"\<Delta>2 s vl s1 vl1 \<equiv>
 \<exists> cid.
    PID \<in>\<in> paperIDs s cid \<and> phase s cid = revPH \<and> \<not> (\<exists> uid. isREVNth s uid PID N) \<and>
    s = s1 \<and> B vl vl1"

definition \<Delta>3 :: "state \<Rightarrow> value list \<Rightarrow> state \<Rightarrow> value list \<Rightarrow> bool" where
"\<Delta>3 s vl s1 vl1 \<equiv>
 \<exists> cid uid.
    PID \<in>\<in> paperIDs s cid \<and> phase s cid \<in> {revPH, disPH} \<and> isREVNth s uid PID N \<and>
    eqExcPID_N s s1 \<and> B vl vl1"

definition \<Delta>4 :: "state \<Rightarrow> value list \<Rightarrow> state \<Rightarrow> value list \<Rightarrow> bool" where
"\<Delta>4 s vl s1 vl1 \<equiv>
 \<exists> cid uid.
    PID \<in>\<in> paperIDs s cid \<and> phase s cid \<ge> revPH \<and> isREVNth s uid PID N \<and>
    (reviewsPaper (paper s PID))!N \<noteq> [] \<and> (reviewsPaper (paper s1 PID))!N \<noteq> [] \<and>
    eqExcPID_N2 s s1 \<and> vl = [] \<and> vl1 = []"

definition \<Delta>e :: "state \<Rightarrow> value list \<Rightarrow> state \<Rightarrow> value list \<Rightarrow> bool" where
"\<Delta>e s vl s1 vl1 \<equiv>
 vl \<noteq> [] \<and>
 (
  (\<exists> cid. PID \<in>\<in> paperIDs s cid \<and> phase s cid > revPH \<and> \<not> (\<exists> uid. isREVNth s uid PID N))
  \<or>
  (\<exists> cid. PID \<in>\<in> paperIDs s cid \<and> phase s cid > disPH)
 )"

lemma istate_\<Delta>1:
assumes B: "B vl vl1"
shows "\<Delta>1 istate vl istate vl1"
using B unfolding \<Delta>1_def B_def istate_def by auto

lemma unwind_cont_\<Delta>1: "unwind_cont \<Delta>1 {\<Delta>1,\<Delta>2,\<Delta>e}"
proof(rule, simp)
  let ?\<Delta> = "\<lambda>s vl s1 vl1. \<Delta>1 s vl s1 vl1 \<or> \<Delta>2 s vl s1 vl1 \<or> \<Delta>e s vl s1 vl1"
  fix s s1 :: state and vl vl1 :: "value list"
  assume rsP: "reachNT s" and rs1: "reach s1" and "\<Delta>1 s vl s1 vl1"
  hence rs: "reach s" and ss1: "s1 = s"
  and vl: "vl \<noteq> []" and vl1: "vl1 \<noteq> []" and vl_vl1: "last vl1 = last vl"
  and PID_ph: "\<And> cid. PID \<in>\<in> paperIDs s cid \<Longrightarrow> phase s cid < revPH"
  using reachNT_reach unfolding \<Delta>1_def B_def by auto
  note vlvl1 = vl vl1 vl_vl1
  show "iaction ?\<Delta> s vl s1 vl1 \<or>
        ((vl = [] \<longrightarrow> vl1 = []) \<and> reaction ?\<Delta> s vl s1 vl1)" (is "?iact \<or> (_ \<and> ?react)")
  proof-
    have ?react proof
      fix a :: act and ou :: out and s' and vl'
      let ?trn = "Trans s a ou s'"  let ?trn1 = "Trans s1 a ou s'"
      assume step: "step s a = (ou, s')" and P: "\<not> T ?trn" and c: "consume ?trn vl vl'"
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
            subgoal apply(cases a)
              subgoal for x1 apply(cases x1) apply(fastforce simp: c_defs)+ .
              subgoal for x2 apply(cases x2) apply(fastforce simp: u_defs)+ .
              subgoal for x3 apply(cases x3) apply(fastforce simp: uu_defs)+ .
              by auto
            done
            hence "\<Delta>1 s' vl' s' vl1" unfolding \<Delta>1_def B_def B_def vl' using PID_ph' vlvl1 by auto
            thus ?thesis by auto
          next
            case True
            then obtain CID where PID: "PID \<in>\<in> paperIDs s CID" by auto
            hence ph: "phase s CID < revPH" using PID_ph by auto
            have PID': "PID \<in>\<in> paperIDs s' CID" by (metis PID paperIDs_mono step)
            show ?thesis
            proof(cases "phase s' CID < revPH")
              case True note ph' = True
              hence "\<Delta>1 s' vl' s' vl1" unfolding \<Delta>1_def B_def B_def vl' using vlvl1 ph' PID' apply auto
              by (metis reach_PairI paperIDs_equals rs step)
              thus ?thesis by auto
            next
              case False note ph' = False
              have "\<not> (\<exists> uid. isRevNth s CID uid PID N)" using rs ph isRevNth_geq_revPH by fastforce
              hence ph_isRev': "phase s' CID = revPH \<and> \<not> (\<exists> uid. isRevNth s' CID uid PID N)"
              using ph' ph PID step rs
              subgoal apply(cases a)
                subgoal for x1 apply(cases x1) apply(fastforce simp: c_defs)+ .
                subgoal for x2 apply(cases x2) apply(fastforce simp: u_defs)+ .
                subgoal for x3 apply(cases x3) apply(fastforce simp: uu_defs)+ .
                by auto
              done
              hence "\<not> (\<exists> uid. isREVNth s' uid PID N)"
              by (metis PID' isREVNth_imp_isRevNth reach_PairI rs step)
              hence "\<Delta>2 s' vl' s' vl1" unfolding \<Delta>2_def B_def vl' using vlvl1 ph' PID' ph_isRev' by auto
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
  assume rsP: "reachNT s" and rs1: "reach s1" and "\<Delta>2 s vl s1 vl1"
  then obtain CID where rs: "reach s" and ph: "phase s CID = revPH" (is "?ph = _") and ss1: "s1 = s"
  and uuid: "\<not> (\<exists> uid. isREVNth s uid PID N)"
  and vl: "vl \<noteq> []" and vl1: "vl1 \<noteq> []" and vl_vl1: "last vl1 = last vl"
  and PID: "PID \<in>\<in> paperIDs s CID" using reachNT_reach unfolding \<Delta>2_def B_def by auto
  hence uid: "\<not> (\<exists> uid. isRevNth s CID uid PID N)" by (metis isREVNth_def)
  note vlvl1 = vl vl1 vl_vl1
  show "iaction ?\<Delta> s vl s1 vl1 \<or>
        ((vl = [] \<longrightarrow> vl1 = []) \<and> reaction ?\<Delta> s vl s1 vl1)" (is "?iact \<or> (_ \<and> ?react)")
  proof-
    have ?react proof
      fix a :: act and ou :: out and s' :: state and vl'
      let ?trn = "Trans s a ou s'"  let ?trn1 = "Trans s1 a ou s'"
      let ?ph' = "phase s' CID"
      assume step: "step s a = (ou, s')" and P: "\<not> T ?trn" and c: "consume ?trn vl vl'"
      have \<phi>: "\<not> \<phi> ?trn"
        apply(cases a)
        subgoal by simp
        subgoal for x2 apply(cases x2)
          using step ph apply (auto simp: u_defs)
          by (metis PID isRev_imp_isRevNth_getReviewIndex paperIDs_equals rs uid)
        subgoal for x3 apply(cases x3)
          using step ph apply (auto simp: uu_defs)
          using PID paperIDs_equals rs by force
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
            case False
            hence 1: "?ph' > revPH \<and> \<not> (\<exists> uid. isRevNth s' CID uid PID N)"
            using uid PID ph step rs
            subgoal apply(cases a)
              subgoal for x1 apply(cases x1) apply(fastforce simp: c_defs)+ .
              subgoal for x2 apply(cases x2) apply(fastforce simp: u_defs)+ .
              subgoal for x3 apply(cases x3) apply(fastforce simp: uu_defs)+ .
              by auto
            done
            hence "\<not> (\<exists> uid. isREVNth s' uid PID N)"
            by (metis PID' isREVNth_imp_isRevNth reach_PairI rs step)
            hence "\<Delta>e s' vl' s' vl1" unfolding \<Delta>e_def vl' using PID' vl 1 by auto
            thus ?thesis by simp
          next
            case True note ph' = True
            show ?thesis proof(cases "\<exists> uid. isREVNth s' uid PID N")
              case False
              hence "\<Delta>2 s' vl' s' vl1" using PID' vlvl1 ph' unfolding \<Delta>2_def B_def vl' by auto
              thus ?thesis by simp
            next
              case True
              hence "\<Delta>3 s' vl' s' vl1" using PID' vlvl1 ph' unfolding \<Delta>3_def B_def vl' by auto
              thus ?thesis by simp
            qed
          qed
        qed
        thus ?thesis by simp
      qed
    qed
    thus ?thesis using vl by auto
  qed
qed

lemma unwind_cont_\<Delta>3: "unwind_cont \<Delta>3 {\<Delta>3,\<Delta>4,\<Delta>e}"
proof(rule, simp)
  let ?\<Delta> = "\<lambda>s vl s1 vl1. \<Delta>3 s vl s1 vl1 \<or> \<Delta>4 s vl s1 vl1 \<or> \<Delta>e s vl s1 vl1"
  fix s s1 :: state and vl vl1 :: "value list"
  assume rsT: "reachNT s" and rs1: "reach s1" and "\<Delta>3 s vl s1 vl1"
  then obtain CID uid where uuid: "isREVNth s uid PID N"
  and PID: "PID \<in>\<in> paperIDs s CID"
  and rs: "reach s" and ph: "phase s CID = revPH \<or> phase s CID = disPH" (is "?ph = _ \<or> _")
  and ss1: "eqExcPID_N s s1" and vl: "vl \<noteq> []" and vl1: "vl1 \<noteq> []" and vl_vl1: "last vl = last vl1"
  using reachNT_reach unfolding \<Delta>3_def B_def by auto
  hence uid: "isRevNth s CID uid PID N" by (metis isREVNth_imp_isRevNth)
  note vlvl1 = vl vl1 vl_vl1
  from vl vl1 obtain v vl' v1 vl1' where vl: "vl = v # vl'" and vl1: "vl1 = v1 # vl1'" by (metis list.exhaust)
  have uid_notin: "uid \<notin> UIDs" using uid by (metis reachNT_non_isRevNth_isPC_isChair rsT)
  show "iaction ?\<Delta> s vl s1 vl1 \<or>
        ((vl = [] \<longrightarrow> vl1 = []) \<and> reaction ?\<Delta> s vl s1 vl1)" (is "?iact \<or> (_ \<and> ?react)")
  proof(cases "vl1' = []")
    case False note vl1' = False
    hence vl_vl1': "last vl = last vl1'" using vl_vl1 unfolding vl1 by simp
    have uid1: "isRevNth s CID uid PID N" using ss1 uid unfolding eqExcPID_N_def by auto
    define a1 where "a1 \<equiv>
     if ?ph = revPH
      then Uact (uReview CID uid (pass s uid) PID N v1)
      else UUact (uuReview CID uid (pass s uid) PID N v1)"
    (is "_ \<equiv> if ?ph = revPH then ?A else ?B")
    hence a1: "a1 \<in> {?A,?B}" by auto
    obtain s1' ou1 where step1: "step s1 a1 = (ou1,s1')" by (metis prod.exhaust)
    let ?trn1 = "Trans s1 a1 ou1 s1'"
    have s1s1': "eqExcPID_N s1 s1'" using step1 by (metis a1_def uReview_uuReview_step_eqExcPID_N)
    have ss1': "eqExcPID_N s s1'" using eqExcPID_N_trans[OF ss1 s1s1'] .
    hence many_s1': "PID \<in>\<in> paperIDs s1' CID" "isRevNth s1' CID uid PID N"
    "pass s1' uid = pass s uid" "phase s1' CID = phase s CID"
    using uid PID ph unfolding eqExcPID_N_def by simp_all
    hence more_s1': "uid \<in>\<in> userIDs s1'" "CID \<in>\<in> confIDs s1'"
    by (metis paperIDs_confIDs reach_PairI roles_userIDs rs1 step1 many_s1'(1))+
    have f: "f ?trn1 = v1" unfolding a1_def by simp
    have rs1': "reach s1'" using rs1 step1 by (auto intro: reach_PairI)
    have ou1: "ou1 = outOK"
    using step1 uid1 ph unfolding a1_def apply (simp_all add: u_defs uu_defs many_s1' more_s1')
    by (metis isRevNth_getReviewIndex isRev_def3 many_s1' rs1')+
    have ?iact proof
      show "step s1 a1 = (ou1,s1')" by fact
    next
      show \<phi>: "\<phi> ?trn1" using ou1 unfolding a1_def by simp
      thus "consume ?trn1 vl1 vl1'" using f unfolding consume_def vl1 by simp
    next
      show "\<not> \<gamma> ?trn1" by (simp add: a1_def uid_notin)
    next
      have "\<Delta>3 s vl s1' vl1'" unfolding \<Delta>3_def B_def using ph PID ss1' uuid vl_vl1' vl1' vl by auto
      thus "?\<Delta> s vl s1' vl1'" by simp
    qed
    thus ?thesis by auto
  next
    case True hence vl1: "vl1 = [v1]" unfolding vl1 by simp
    have ?react proof
      fix a :: act and ou :: out and s' :: state and vll'
      let ?trn = "Trans s a ou s'"
      let ?ph' = "phase s' CID"
      assume step: "step s a = (ou, s')" and T: "\<not> T ?trn" and c: "consume ?trn vl vll'"
      have PID': "PID \<in>\<in> paperIDs s' CID" using PID rs by (metis paperIDs_mono step)
      have uid': "isRevNth s' CID uid PID N" using uid step rs ph PID isRevNth_persistent by auto
      hence uuid': "isREVNth s' uid PID N" by (metis isREVNth_def)
      show "match ?\<Delta> s s1 vl1 a ou s' vll' \<or> ignore ?\<Delta> s s1 vl1 a ou s' vll'" (is "?match \<or> ?ignore")
      proof(cases "\<phi> ?trn")
        case False note \<phi> = False
        have vll': "vll' = vl" using c \<phi> unfolding consume_def by (cases vl) auto
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
          using eqExcPID_N_step_out[OF ss1 step step1 rsT rs1 PID ph] by simp
        next
          show "?\<Delta> s' vll' s1' vl1"
          proof(cases "?ph' = revPH \<or> ?ph' = disPH")
            case True
            hence "\<Delta>3 s' vll' s1' vl1" using PID' s's1' uuid' vlvl1 unfolding \<Delta>3_def B_def vll' by auto
            thus ?thesis by auto
          next
            case False hence ph': "?ph' > disPH" using ph rs step
            by (metis le_less less_antisym not_less phase_increases2 prod.sel(2))
            hence "\<Delta>e s' vll' s1' vl1" unfolding \<Delta>e_def vll' using PID' vlvl1 by auto
            thus ?thesis by auto
          qed
        qed
        thus ?thesis by simp
      next
        case True note \<phi> = True
        hence vll': "vll' = vl'" using c unfolding vl consume_def by simp
        obtain cid uid p rc where a:
        "a = Uact (uReview cid uid p PID N rc) \<or>
         a = UUact (uuReview cid uid p PID N rc)" (is "a = ?A \<or> a = ?B")
        and ou: "ou = outOK" and v: "v = rc"
        using \<phi> c unfolding vl consume_def \<phi>_def2 vll' by fastforce
        hence cid: "cid = CID" using step apply(auto simp: u_defs uu_defs)
        (* crucial use of safety: *) by (metis PID paperIDs_equals rs)+
        have a: "(?ph = revPH \<longrightarrow> a = ?A) \<and> (?ph = disPH \<longrightarrow> a = ?B)"
        using step ou a by (cases "a = ?A", auto simp: u_defs uu_defs cid)
        have \<gamma>: "\<not> \<gamma> ?trn" using step T rsT by (metis T_\<phi>_\<gamma> True)
        hence f: "f ?trn = v" using c \<phi> unfolding consume_def vl by auto
        have s's: "eqExcPID_N s' s" using eqExcPID_N_sym[OF \<phi>_step_eqExcPID_N[OF \<phi> step]] .
        have s's1: "eqExcPID_N s' s1" using eqExcPID_N_trans[OF s's ss1] .
        have ph': "phase s' CID = ?ph" using s's ph unfolding eqExcPID_N_def by auto
        show ?thesis
        proof(cases "vl' = []")
          case False note vl' = False
          hence vl'_vl1: "last vl' = last vl1" using vl_vl1 unfolding vl by auto
          have ?ignore proof
            show "\<not> \<gamma> ?trn" by fact
          next
            show "?\<Delta> s' vll' s1 vl1"
            proof(cases "?ph' = revPH \<or> ?ph' = disPH")
              case True
              hence "\<Delta>3 s' vll' s1 vl1" using s's1 PID' uuid' vl' vl1 vl_vl1 unfolding \<Delta>3_def B_def vl vll' by auto
              thus ?thesis by auto
            next
              case False hence "?ph' > disPH" using ph rs step by (simp add: ph')
              hence "\<Delta>e s' vll' s1 vl1" unfolding \<Delta>e_def vll' using PID' vlvl1 vl' by auto
              thus ?thesis by auto
            qed
          qed
          thus ?thesis by auto
        next
          case True note vl' = True hence vl: "vl = [v]" unfolding vl by simp
(* the transition to \<Delta>4: \<phi> holds and both vl and vl1 are singletons: *)
          hence v1v: "v1 = v" using vl_vl1 unfolding vl1 by simp
          obtain s1' ou1 where step1: "step s1 a = (ou1,s1')" by (metis prod.exhaust)
          let ?trn1 = "Trans s1 a ou1 s1'"
          have \<phi>1: "\<phi> ?trn1" using eqExcPID_N_step_\<phi>_imp[OF ss1 step step1 \<phi>] .
          hence ou1: "ou1 = outOK" unfolding \<phi>_def2 by auto
          have uid'_uid1': "isRevNth s' CID uid PID N \<and> isRevNth s1' CID uid PID N"
          using step step1 ou ou1 ph a apply(auto simp: u_defs uu_defs)
          by (metis cid isRev_imp_isRevNth_getReviewIndex)+
          hence N: "N < length (reviewsPaper (paper s' PID)) \<and> N < length (reviewsPaper (paper s1' PID))"
          by (metis isRevNth_less_length reach_PairI rs rs1 step step1)
          hence l: "reviewsPaper (paper s' PID) ! N \<noteq> [] \<and> reviewsPaper (paper s1' PID) ! N \<noteq> []"
          using step step1 ph a ou ou1 by (auto simp add: u_defs uu_defs)
          have ?match proof
          show "validTrans ?trn1" using step1 by simp
        next
          show "consume ?trn1 vl1 []" unfolding consume_def using \<phi>1 a ph
          by (auto simp add: a v vl1 v1v)
        next
          show "\<gamma> ?trn = \<gamma> ?trn1" unfolding ss1 by simp
        next
          assume "\<gamma> ?trn" thus "g ?trn = g ?trn1"
          using eqExcPID_N_step_out[OF ss1 step step1 rsT rs1 PID ph] by simp
        next
          have "\<Delta>4 s' vll' s1' []" unfolding vll' vl' \<Delta>4_def
          using ph' ph uuid' l eqExcPID_N_step_\<phi>_eqExcPID_N2[OF rs ss1 step step1 \<phi>] PID' by auto
          thus "?\<Delta> s' vll' s1' []" by simp
        qed
        thus ?thesis by simp
        qed
      qed
    qed
    thus ?thesis using vl by auto
  qed
qed

lemma unwind_cont_\<Delta>4: "unwind_cont \<Delta>4 {\<Delta>4,\<Delta>e}"
proof(rule, simp)
  let ?\<Delta> = "\<lambda>s vl s1 vl1. \<Delta>4 s vl s1 vl1 \<or> \<Delta>e s vl s1 vl1"
  fix s s1 :: state and vl vl1 :: "value list"
  assume rsT: "reachNT s" and rs1: "reach s1" and "\<Delta>4 s vl s1 vl1"
  then obtain CID uid where uuid: "isREVNth s uid PID N"
  and rs: "reach s" and ph: "phase s CID \<ge> revPH" (is "?ph \<ge> _")
  and PID: "PID \<in>\<in> paperIDs s CID"
  and decs: "(reviewsPaper (paper s PID))!N \<noteq> [] \<and> (reviewsPaper (paper s1 PID))!N \<noteq> []"
  and ss1: "eqExcPID_N2 s s1" and vl: "vl = []" and vl1: "vl1 = []"
  using reachNT_reach unfolding \<Delta>4_def by auto
  hence uid: "isRevNth s CID uid PID N" by (metis isREVNth_imp_isRevNth)
  show "iaction ?\<Delta> s vl s1 vl1 \<or>
        ((vl = [] \<longrightarrow> vl1 = []) \<and> reaction ?\<Delta> s vl s1 vl1)" (is "?iact \<or> (_ \<and> ?react)")
  proof-
    have "?react"
    proof
      fix a :: act and ou :: out and s' :: state and vl'
      let ?trn = "Trans s a ou s'"
      let ?ph' = "phase s' CID"
      assume step: "step s a = (ou, s')" and T: "\<not> T ?trn" and c: "consume ?trn vl vl'"
      have ph': "phase s' CID \<ge> revPH" using ph rs isRevNth_geq_revPH isRevNth_persistent local.step reach_PairI uid by blast
      have PID': "PID \<in>\<in> paperIDs s' CID" by (metis PID paperIDs_mono step)
      have uid': "isRevNth s' CID uid PID N" using isRevNth_persistent by (metis isRevNth_persistent rs step uid)
      hence uuid': "isREVNth s' uid PID N" by (metis isREVNth_def)
      show "match ?\<Delta> s s1 vl1 a ou s' vl' \<or> ignore ?\<Delta> s s1 vl1 a ou s' vl'" (is "?match \<or> ?ignore")
      proof-
        have \<phi>: "\<not> \<phi> ?trn" and vl': "vl' = []" using c unfolding consume_def vl by auto
        obtain ou1 and s1' where step1: "step s1 a = (ou1,s1')" by (metis prod.exhaust)
        let ?trn1 = "Trans s1 a ou1 s1'"
        have s's1': "eqExcPID_N2 s' s1'" using eqExcPID_N2_step[OF ss1 step step1 rs uid] .
        have \<phi>1: "\<not> \<phi> ?trn1" using \<phi> unfolding eqExcPID_N2_step_\<phi>[OF rs rs1 ss1 step step1] .
        have uid1: "isRevNth s1 CID uid PID N" using uid eqExcPID_N2_imp[OF ss1] by auto
        have decs': "(reviewsPaper (paper s' PID))!N \<noteq> []" "(reviewsPaper (paper s1' PID))!N \<noteq> []"
        using nonempty_reviews_persist rs rs1 step step1 uid uid1 decs by blast+
        have ?match proof
          show "validTrans ?trn1" using step1 by simp
        next
          show "consume ?trn1 vl1 vl1" unfolding consume_def using \<phi>1 by auto
        next
          show "\<gamma> ?trn = \<gamma> ?trn1" unfolding ss1 by simp
        next
          assume "\<gamma> ?trn" thus "g ?trn = g ?trn1"
          using eqExcPID_N2_step_out[OF ss1 step step1 rsT rs1 uid ph _ decs] by simp
        next
          have "\<Delta>4 s' vl' s1' vl1" using ph' uuid' s's1' PID' unfolding \<Delta>4_def vl1 vl' by (auto simp: decs')
          thus "?\<Delta> s' vl' s1' vl1" by simp
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

definition K2exit where
"K2exit cid s \<equiv> PID \<in>\<in> paperIDs s cid \<and> phase s cid > disPH"

lemma invarNT_K2exit: "invarNT (K2exit cid)"
unfolding invarNT_def apply (safe dest!: reachNT_reach)
  subgoal for _ a apply(cases a)
    subgoal for x1 apply(cases x1) apply (fastforce simp add: c_defs K2exit_def geq_noPH_confIDs)+ .
    subgoal for x2 apply(cases x2) apply (fastforce simp add: u_defs K2exit_def paperIDs_equals)+ .
    subgoal for x3 apply(cases x3) apply (fastforce simp add: uu_defs K2exit_def)+ .
    by auto
  done

lemma noVal_K2exit: "noVal (K2exit cid) v"
  apply(rule no\<phi>_noVal)
  unfolding no\<phi>_def apply safe
  subgoal for _ a apply(cases a)
    subgoal by (fastforce simp add: c_defs K2exit_def)
    subgoal for x2 apply(cases x2) apply (auto simp add: u_defs K2exit_def)
      using paperIDs_equals reachNT_reach apply fastforce .
    subgoal for x3 apply(cases x3) apply (auto simp add: uu_defs K2exit_def)
      using paperIDs_equals reachNT_reach apply fastforce .
    by auto
done

lemma unwind_exit_\<Delta>e: "unwind_exit \<Delta>e"
proof
  fix s s1 :: state and vl vl1 :: "value list"
  assume rsT: "reachNT s" and rs1: "reach s1" and \<Delta>e: "\<Delta>e s vl s1 vl1"
  hence vl: "vl \<noteq> []" using reachNT_reach unfolding \<Delta>e_def by auto
  then obtain CID where "K1exit CID s \<or> K2exit CID s" using \<Delta>e
  unfolding K1exit_def K2exit_def \<Delta>e_def isREVNth_def by auto
  thus "vl \<noteq> [] \<and> exit s (hd vl)" apply(simp add: vl)
  by (metis rsT exitI2 invarNT_K1exit noVal_K1exit invarNT_K2exit noVal_K2exit)
qed

theorem secure: secure
apply(rule unwind_decomp4_secure[of \<Delta>1 \<Delta>2 \<Delta>e \<Delta>3 \<Delta>4])
using
istate_\<Delta>1
unwind_cont_\<Delta>1 unwind_cont_\<Delta>2 unwind_cont_\<Delta>2 unwind_cont_\<Delta>3 unwind_cont_\<Delta>4
unwind_exit_\<Delta>e
by auto


end
