theory Review_RAut
imports "../Observation_Setup" Review_Value_Setup "Bounded_Deducibility_Security.Compositional_Reasoning"
begin

subsection \<open>Confidentiality protection from users who are not the review's author\<close>


text \<open>We verify the following property:

\ \\
A group UIDs of users learn nothing
about the various updates of the N'th review of a paper PID
except for the last edited version before discussion and all the later versions
unless a user in UIDs is that review's author.

\ \\
\<close>

type_synonym "value" = "phase * rcontent"

fun f :: "(state,act,out) trans \<Rightarrow> value" where
"f (Trans s (Uact (uReview cid uid p pid n rc)) _ _) = (phase s cid, rc)"
|
"f (Trans s (UUact (uuReview cid uid p pid n rc)) _ _) = (phase s cid, rc)"

fun T :: "(state,act,out) trans \<Rightarrow> bool" where
"T (Trans _ _ ou s') =
 (\<exists> uid \<in> UIDs. isREVNth s' uid PID N)"

declare T.simps [simp del]

definition B :: "value list \<Rightarrow> value list \<Rightarrow> bool" where
"B vl vl1 \<equiv>
 \<exists> ul ul1 wl.
   vl = (map (Pair revPH) ul) @ (map (Pair disPH) wl) \<and>
   vl1 = (map (Pair revPH) ul1) @ (map (Pair disPH) wl) \<and>
   ul \<noteq> [] \<and> ul1 \<noteq> [] \<and> last ul = last ul1"

interpretation BD_Security_IO where
istate = istate and step = step and
\<phi> = \<phi> and f = f and \<gamma> = \<gamma> and g = g and T = T and B = B
done

lemma reachNT_non_isRevNth:
assumes "reachNT s" and "uid \<in> UIDs"
shows "\<not> isRevNth s cid uid PID N"
  using assms
  apply induct
   apply (auto simp: istate_def)[]
  subgoal for trn apply(cases trn, auto simp: T.simps reachNT_reach isREVNth_def) .
  done


(* important: *) lemma P_\<phi>_\<gamma>:
assumes 1: "reachNT s" and 2: "step s a = (ou,s')" "\<phi> (Trans s a ou s')"
shows "\<not> \<gamma> (Trans s a ou s')"
using reachNT_non_isRevNth[OF 1] 2 unfolding T.simps \<phi>_def2
apply (auto simp add: u_defs uu_defs) by (metis isRev_imp_isRevNth_getReviewIndex)+

(* major *) lemma eqExcPID_N_step_out:
assumes s's1': "eqExcPID_N s s1"
and step: "step s a = (ou,s')" and step1: "step s1 a = (ou1,s1')"
and sT: "reachNT s" and s1: "reach s1"
and PID: "PID \<in>\<in> paperIDs s cid"
and ph: "phase s cid = revPH"
and UIDs: "userOfA a \<in> UIDs"
shows "ou = ou1"
proof-
  note Inv = reachNT_non_isRevNth[OF sT UIDs]
  note eqs = eqExcPID_N_imp[OF s's1']
  note eqs' = eqExcPID_N_imp1[OF s's1']
  note s = reachNT_reach[OF sT]

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
        by clarsimp (metis Suc_n_not_le_n eqExcPID_N_imp2 s's1')
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

lemma eeqExcPID_N_imp_eq:
assumes "eeqExcPID_N paps paps1"
and "reviewsPaper (paps PID) ! N = reviewsPaper (paps1 PID) ! N"
shows "paps = paps1"
proof(rule ext)
  fix pid
  show "paps pid = paps1 pid"
  using assms unfolding eeqExcPID_N_def eqExcD eqExcNth_def
  apply(cases "paps PID", cases "paps1 PID", cases "pid = PID")
  by simp_all (metis nth_equalityI)
qed

lemma eqExcPID_N_imp_eq:
assumes e: "eqExcPID_N s s1"
and "reviewsPaper (paper s PID) ! N = reviewsPaper (paper s1 PID) ! N"
shows "s = s1"
proof-
  have "paper s = paper s1" using assms eeqExcPID_N_imp_eq
  unfolding eqExcPID_N_def by metis
  thus ?thesis
  using e unfolding eqExcPID_N_def by (intro state.equality) auto
qed


(* major *) lemma eqExcPID_N_step_eq:
assumes s: "reach s" and ss1: "eqExcPID_N s s1"
and a: "a = Uact (uReview cid uid p PID N rc)"
and step: "step s a = (outOK, s')" and step1: "step s1 a = (ou', s1')"
shows "s' = s1'"
proof(cases "\<exists> cid uid. isRevNth s cid uid PID N")
  case False
  hence False
  using step unfolding a
  by (auto simp add: u_defs uu_defs) (metis isRev_imp_isRevNth_getReviewIndex)+
  thus ?thesis by auto
next
  case True note r = True
  note eqs = eqExcPID_N_imp[OF ss1]
  note eqsT = eqExcPID_N_Paper[OF ss1]
  have r: "N < length (reviewsPaper (paper s PID))"
  using isRevNth_less_length[OF s] r by auto
  have r1: "N < length (reviewsPaper (paper s1 PID))"
  using eqs r unfolding eeqExcPID_N_def eqExcD eqExcNth_def by simp
  have s's1': "eqExcPID_N s' s1'" using assms by (metis eqExcPID_N_step)

  have "e_updateReview s cid uid p PID N rc"
  using step a by auto
  hence "e_updateReview s1 cid uid p PID N rc"
  using eqExcPID_N_imp[OF ss1] u_defs by auto
  hence ou': "ou' = outOK" using step1 a by auto

  let ?p = "paper s PID" let ?p1 = "paper s1 PID"

  have 1: "eqExcD ?p ?p1"
  using ss1 eqExcPID_N_imp unfolding eeqExcPID_N_def by auto

  have 2: "reviewsPaper (paper s' PID) ! N = reviewsPaper (paper s1' PID) ! N"
  using step step1[unfolded ou'] r r1 unfolding a
  by (cases ?p, cases ?p1) (auto simp : u_defs)

  from 1 2 show ?thesis using eqExcPID_N_imp_eq s's1' by blast
qed

definition \<Delta>1 :: "state \<Rightarrow> value list \<Rightarrow> state \<Rightarrow> value list \<Rightarrow> bool" where
"\<Delta>1 s vl s1 vl1 \<equiv>
 (\<forall> cid. PID \<in>\<in> paperIDs s cid \<longrightarrow> phase s cid < revPH) \<and>
 s = s1 \<and> B vl vl1"

definition \<Delta>2 :: "state \<Rightarrow> value list \<Rightarrow> state \<Rightarrow> value list \<Rightarrow> bool" where
"\<Delta>2 s vl s1 vl1 \<equiv>
 \<exists> cid.
    PID \<in>\<in> paperIDs s cid \<and> phase s cid = revPH \<and> \<not> (\<exists> uid. isREVNth s uid PID N) \<and>
    s = s1 \<and> B vl vl1"

definition \<Delta>3 :: "state \<Rightarrow> value list \<Rightarrow> state \<Rightarrow> value list \<Rightarrow> bool" where
"\<Delta>3 s vl s1 vl1 \<equiv>
 \<exists> cid uid.
    PID \<in>\<in> paperIDs s cid \<and> phase s cid = revPH \<and> isREVNth s uid PID N \<and>
    eqExcPID_N s s1 \<and> B vl vl1"

definition \<Delta>4 :: "state \<Rightarrow> value list \<Rightarrow> state \<Rightarrow> value list \<Rightarrow> bool" where
"\<Delta>4 s vl s1 vl1 \<equiv>
 \<exists> cid uid.
    PID \<in>\<in> paperIDs s cid \<and> phase s cid \<ge> revPH \<and> isREVNth s uid PID N \<and>
    s = s1 \<and> (\<exists> wl. vl = map (Pair disPH) wl \<and> vl1 = map (Pair disPH) wl)"

definition \<Delta>e :: "state \<Rightarrow> value list \<Rightarrow> state \<Rightarrow> value list \<Rightarrow> bool" where
"\<Delta>e s vl s1 vl1 \<equiv>
 vl \<noteq> [] \<and>
 (
  (\<exists> cid. PID \<in>\<in> paperIDs s cid \<and> phase s cid > revPH \<and> \<not> (\<exists> uid. isREVNth s uid PID N))
  \<or>
  (\<exists> cid. PID \<in>\<in> paperIDs s cid \<and> phase s cid > revPH \<and> fst (hd vl) = revPH)
 )"

lemma istate_\<Delta>1:
assumes B: "B vl vl1"
shows "\<Delta>1 istate vl istate vl1"
using B unfolding \<Delta>1_def B_def istate_def by auto

lemma unwind_cont_\<Delta>1: "unwind_cont \<Delta>1 {\<Delta>1,\<Delta>2,\<Delta>e}"
proof(rule, simp)
  let ?\<Delta> = "\<lambda>s vl s1 vl1. \<Delta>1 s vl s1 vl1 \<or> \<Delta>2 s vl s1 vl1 \<or> \<Delta>e s vl s1 vl1"
  fix s s1 :: state and vl vl1 :: "value list"
  assume rsT: "reachNT s" and rs1: "reach s1" and "\<Delta>1 s vl s1 vl1"
  hence rs: "reach s" and ss1: "s1 = s" and B: "B vl vl1"
  and vl: "vl \<noteq> []" and vl1: "vl1 \<noteq> []" and PID_ph: "\<And> cid. PID \<in>\<in> paperIDs s cid \<longrightarrow> phase s cid < revPH"
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
            hence "\<Delta>1 s' vl' s' vl1" unfolding \<Delta>1_def vl' using B PID_ph' vl by auto
            thus ?thesis by auto
          next
            case True
            then obtain CID where PID: "PID \<in>\<in> paperIDs s CID" by auto
            hence ph: "phase s CID < revPH" using PID_ph by auto
            have PID': "PID \<in>\<in> paperIDs s' CID" by (metis PID paperIDs_mono step)
            show ?thesis
            proof(cases "phase s' CID < revPH")
              case True note ph' = True
              hence "\<Delta>1 s' vl' s' vl1" unfolding \<Delta>1_def vl' using B vl ph' PID' apply auto
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
              by (metis PID' isREVNth_imp_isRevNth reach_PairI rs step)
              hence "\<Delta>2 s' vl' s' vl1" unfolding \<Delta>2_def vl' using B vl ph' PID' ph_isRev' by auto
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
  then obtain CID where uuid: "\<not> (\<exists> uid. isREVNth s uid PID N)" and PID: "PID \<in>\<in> paperIDs s CID"
  and rs: "reach s" and ph: "phase s CID = revPH" (is "?ph = _") and ss1: "s1 = s"
  and B: "B vl vl1"
  and vl: "vl \<noteq> []" and vl1: "vl1 \<noteq> []"
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
            case True note ph' = True
            show ?thesis proof(cases "\<exists> uid. isRevNth s' CID uid PID N")
              case False
              hence "\<not> (\<exists> uid. isREVNth s' uid PID N)"
              by (metis PID' isREVNth_def isRevNth_paperIDs paperIDs_equals reach_PairI rs1 ss1 step)
              hence "\<Delta>2 s' vl' s' vl1" unfolding \<Delta>2_def vl' using B ph' PID' unfolding B_def by auto
              thus ?thesis by auto
            next
              case True hence "\<exists> uid. isREVNth s' uid PID N" by (metis isREVNth_def)
              hence "\<Delta>3 s' vl' s' vl1" unfolding \<Delta>3_def vl' using B ph' PID' unfolding B_def by auto
              thus ?thesis by auto
            qed
          next
            case False
            hence ph': "?ph' > revPH" by (metis le_less step ph phase_increases)
            hence "\<not> (\<exists> uid. isRevNth s' CID uid PID N)" using PID uid ph step rs
            apply(cases a)
              subgoal for x1 apply(cases x1) apply(fastforce simp: c_defs)+ .
              subgoal for x2 apply(cases x2) apply(fastforce simp: u_defs)+ .
              subgoal for x3 apply(cases x3) apply(fastforce simp: uu_defs)+ .
              by auto
            hence "\<not> (\<exists> uid. isREVNth s' uid PID N)"
            by (metis IO_Automaton.reach_PairI PID' isREVNth_imp_isRevNth rs1 ss1 step)
            hence "\<Delta>e s' vl' s' vl1" using ph' vl PID' unfolding \<Delta>e_def vl' by auto
            thus ?thesis by auto
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
  then obtain CID uid ul ul1 wl where uuid: "isREVNth s uid PID N"
  and rs: "reach s" and ph: "phase s CID = revPH" (is "?ph = _")  and ss1: "eqExcPID_N s s1"
  and PID: "PID \<in>\<in> paperIDs s CID" and B: "B vl vl1"
  and vlvl1: "vl \<noteq> []" "vl1 \<noteq> []"
  and vl_wl: "vl = (map (Pair revPH) ul) @ (map (Pair disPH) wl)"
  and vl1_wl: "vl1 = (map (Pair revPH) ul1) @ (map (Pair disPH) wl)"
  and ulul1: "ul \<noteq> [] \<and> ul1 \<noteq> [] \<and> last ul = last ul1"
  using reachNT_reach unfolding \<Delta>3_def B_def by blast
  hence uid: "isRevNth s CID uid PID N" by (metis isREVNth_imp_isRevNth)
  have ph1: "phase s1 CID = revPH" using ss1 ph eqExcPID_N_imp by auto
  from ulul1 obtain u ul' u1 ul1' where ul: "ul = u # ul'" and ul1: "ul1 = u1 # ul1'" by (metis list.exhaust)
  obtain vl' vl1' where
  vl:  "vl = (revPH, u) # vl'"    and vl'_wl: "vl' = (map (Pair revPH) ul') @ (map (Pair disPH) wl)" and
  vl1: "vl1 = (revPH, u1) # vl1'" and vl1'_wl: "vl1' = (map (Pair revPH) ul1') @ (map (Pair disPH) wl)"
  unfolding vl_wl ul vl1_wl ul1 by auto
  have uid_notin: "uid \<notin> UIDs" using uid by (metis reachNT_non_isRevNth rsT)
  show "iaction ?\<Delta> s vl s1 vl1 \<or>
        ((vl = [] \<longrightarrow> vl1 = []) \<and> reaction ?\<Delta> s vl s1 vl1)" (is "?iact \<or> (_ \<and> ?react)")
  proof(cases "ul1' = []")
    case False note ul1' = False
    hence ul_ul1': "last ul = last ul1'" using ulul1 unfolding ul1 by simp
    have uid1: "isRevNth s1 CID uid PID N" using ss1 uid unfolding eqExcPID_N_def by auto
    define a1 where "a1 \<equiv> Uact (uReview CID uid (pass s uid) PID N u1)"
    obtain s1' ou1 where step1: "step s1 a1 = (ou1,s1')" by (metis prod.exhaust)
    let ?trn1 = "Trans s1 a1 ou1 s1'"
    have s1s1': "eqExcPID_N s1 s1'" using a1_def step1 by (metis uReview_uuReview_step_eqExcPID_N)
    have ss1': "eqExcPID_N s s1'" using eqExcPID_N_trans[OF ss1 s1s1'] .
    hence many_s1': "PID \<in>\<in> paperIDs s1' CID" "isRevNth s1' CID uid PID N"
    "phase s1' CID = revPH" "pass s1' uid = pass s uid"
    using uid PID ph unfolding eqExcPID_N_def by auto
    hence more_s1': "uid \<in>\<in> userIDs s1'" "CID \<in>\<in> confIDs s1'"
    by (metis paperIDs_confIDs reach_PairI roles_userIDs rs1 step1 many_s1'(1))+
    have f: "f ?trn1 = (revPH,u1)" unfolding a1_def using ph1 by simp
    have rs1': "reach s1'" using rs1 step1 by (auto intro: reach_PairI)
    have ou1: "ou1 = outOK"
    using step1 uid1 ph unfolding a1_def apply (auto simp add: u_defs many_s1' more_s1')
    by (metis isRevNth_getReviewIndex isRev_def3 many_s1'(2) rs1')+
    have ?iact proof
      show "step s1 a1 = (ou1,s1')" by fact
    next
      show \<phi>: "\<phi> ?trn1" using ou1 unfolding a1_def by simp
      thus "consume ?trn1 vl1 vl1'" using f unfolding consume_def vl1 ul1 by simp
    next
      show "\<not> \<gamma> ?trn1" by (simp add: a1_def uid_notin)
    next
      have "\<Delta>3 s vl s1' vl1'" unfolding \<Delta>3_def B_def
      using ph PID ss1' uuid ul1' vl_wl vl1'_wl ulul1 ul_ul1' by fastforce
      thus "?\<Delta> s vl s1' vl1'" by simp
    qed
    thus ?thesis by auto
  next
    case True hence ul1: "ul1 = [u1]" unfolding ul1 by simp
    have ?react proof
      fix a :: act and ou :: out and s' :: state and vll'
      let ?trn = "Trans s a ou s'"
      let ?ph' = "phase s' CID"
      assume step: "step s a = (ou, s')" and T: "\<not> T ?trn" and c: "consume ?trn vl vll'"
      have PID': "PID \<in>\<in> paperIDs s' CID" using PID rs by (metis paperIDs_mono step)
      have uid': "isRevNth s' CID uid PID N" by (metis isRevNth_persistent rs step uid)
      hence uuid': "isREVNth s' uid PID N" by (metis isREVNth_def)
      show "match ?\<Delta> s s1 vl1 a ou s' vll' \<or> ignore ?\<Delta> s s1 vl1 a ou s' vll'" (is "?match \<or> ?ignore")
      proof(cases "\<phi> ?trn")
        case False note \<phi> = False
        have vll': "vll' = vl" using c \<phi> unfolding consume_def by auto
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
          proof(cases "?ph' = revPH")
            case True
            hence "\<Delta>3 s' vll' s1' vl1"
            unfolding \<Delta>3_def B_def vll' using ph PID s's1' PID' uuid' vl_wl vl1_wl ulul1 by fastforce
            thus ?thesis by auto
          next
            case False hence "?ph' > revPH" using ph rs step by (metis le_less phase_increases2 snd_conv)
            hence "\<Delta>e s' vll' s1' vl1" using vlvl1 PID' unfolding \<Delta>e_def vll' vl_wl ul by auto
            thus ?thesis by auto
          qed
        qed
        thus ?thesis by simp
      next
        case True note \<phi> = True
        hence vll': "vll' = vl'" using c unfolding vl consume_def by simp
        obtain cid uid' p rc
        where "a = Uact (uReview cid uid' p PID N rc) \<or>
               a = UUact (uuReview cid uid' p PID N rc)" and ou: "ou = outOK"
        using \<phi> c ph step ph unfolding vl consume_def \<phi>_def2 vll' by force
        hence a: "a = Uact (uReview cid uid' p PID N rc)"
        using step ph unfolding ou apply (auto simp: uu_defs) using PID paperIDs_equals rs by force
        have cid: "cid = CID"
          using step unfolding a
          apply(simp add: u_defs uu_defs)
           apply (metis PID e_updateReview_def isRev_paperIDs paperIDs_equals rs)
          by (metis ou out.distinct(1))
        hence \<gamma>: "\<not> \<gamma> ?trn" using step T rsT by (metis P_\<phi>_\<gamma> True)
        hence f: "f ?trn = (revPH,u)" using c \<phi> ph unfolding consume_def vl by simp
        have u: "u = rc" using f unfolding a by (auto simp: u_defs)
        have s's: "eqExcPID_N s' s" using eqExcPID_N_sym[OF \<phi>_step_eqExcPID_N[OF \<phi> step]] .
        have s's1: "eqExcPID_N s' s1" using eqExcPID_N_trans[OF s's ss1] .
        have ph': "phase s' CID = revPH" using s's ph unfolding eqExcPID_N_def by auto
        show ?thesis
        proof(cases "ul' = []")
          case False note ul' = False
          hence ul'ul1: "last ul' = last ul1" using ulul1 unfolding ul by auto
          have ?ignore proof
            show "\<not> \<gamma> ?trn" by fact
          next
            show "?\<Delta> s' vll' s1 vl1"
            proof(cases "?ph' = revPH")
              case True
              hence "\<Delta>3 s' vll' s1 vl1"
                unfolding \<Delta>3_def B_def using ph PID s's1 PID'
                apply - apply(rule exI[of _ CID]) apply(rule exI[of _ uid])
                apply safe
                subgoal using uuid' by simp
                subgoal
                  apply(rule exI[of _ ul']) apply(rule exI[of _ ul1]) apply(rule exI[of _ wl])
                  unfolding vll' using vl'_wl vl1_wl ul'ul1 ul' ulul1 by auto
                done
              thus ?thesis by auto
            next
              case False hence "?ph' > revPH" using rs step ph' by blast
              hence "\<Delta>e s' vll' s1 vl1" unfolding \<Delta>e_def vll' vl'_wl using ul' PID' by (cases ul') auto
              thus ?thesis by auto
            qed
          qed
          thus ?thesis by auto
        next
          case True note ul' = True hence ul: "ul = [u]" unfolding ul by simp
(* the transition to \<Delta>4: \<phi> holds and both ul and ul1 (the parts of vl and vl1 that
cover the reviewing phase) are singletons: *)
          hence u1u: "u1 = u" using ulul1 unfolding ul1 by simp
          obtain s1' ou1 where step1: "step s1 a = (ou1,s1')" by (metis prod.exhaust)
          let ?trn1 = "Trans s1 a ou1 s1'"
          have \<phi>1: "\<phi> ?trn1" using eqExcPID_N_step_\<phi>_imp[OF ss1 step step1 \<phi>] .
          hence ou1: "ou1 = outOK" unfolding \<phi>_def2 by auto
          have "PID \<in>\<in> paperIDs s1 CID" "\<exists> uid. isRevNth s1 CID uid PID N"
          using eqExcPID_N_imp[OF ss1] PID uid by auto
          hence many_s1': "revPH \<le> phase s1' CID" "PID \<in>\<in> paperIDs s1' CID"
          "\<exists>uid. isRevNth s1' CID uid PID N"
          by (metis ph1 phase_increases step1 paperIDs_mono a
                    eqExcPID_N_step_eq ou rs ss1 step step1 uid')+
          hence uuid1': "\<exists>uid. isREVNth s1' uid PID N" by (metis isREVNth_def)
          have ?match proof
          show "validTrans ?trn1" using step1 by simp
        next
          show "consume ?trn1 vl1 (map (Pair disPH) wl)"
          using \<phi>1 ph1 unfolding consume_def by (simp add: a ul1 vl1_wl ul1 u1u u ph1 cid)
        next
          show "\<gamma> ?trn = \<gamma> ?trn1" unfolding ss1 by simp
        next
          assume "\<gamma> ?trn" thus "g ?trn = g ?trn1"
          using eqExcPID_N_step_out[OF ss1 step step1 rsT rs1 PID ph] by simp
        next
          note s's1' = eqExcPID_N_step_eq[OF rs ss1 a step[unfolded ou] step1]
          have "\<Delta>4 s' vll' s1' (map (Pair disPH) wl)"
          unfolding \<Delta>4_def B_def using ph PID s's1' many_s1' uuid1'
          unfolding vll' vl'_wl ul' by auto
          thus "?\<Delta> s' vll' s1' (map (Pair disPH) wl)" by simp
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
  then obtain uid CID  wl where uuid: "isREVNth s uid PID N"
  and rs: "reach s" and ph: "phase s CID \<ge> revPH" (is "?ph \<ge> revPH") and ss1: "s1 = s"
  and PID: "PID \<in>\<in> paperIDs s CID" and vl: "vl = map (Pair disPH) wl"
  and vl1: "vl1 = map (Pair disPH) wl"
  using reachNT_reach unfolding \<Delta>4_def by blast
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
      have uid': "isRevNth s' CID uid PID N" by (metis isRevNth_persistent rs step uid)
      hence uuid': "isREVNth s' uid PID N" by (metis isREVNth_def)
      have PID': "PID \<in>\<in> paperIDs s' CID" using PID rs by (metis paperIDs_mono step)
      have ph': "phase s' CID \<ge> revPH" using rs isRevNth_geq_revPH local.step reach_PairI uid' by blast
      let ?trn1 = "Trans s1 a ou s'"
      show "match ?\<Delta> s s1 vl1 a ou s' vl' \<or> ignore ?\<Delta> s s1 vl1 a ou s' vl'" (is "?match \<or> ?ignore")
      proof(cases "\<phi> ?trn")
        case True note \<phi> = True
        hence \<phi>1: "\<phi> ?trn1" unfolding ss1 by simp
        obtain w wl' where wl: "wl = w # wl'" and vl: "vl = (disPH,w) # map (Pair disPH) wl'"
        and vl1: "vl1 = (disPH,w) # map (Pair disPH) wl'" and vl': "vl' = map (Pair disPH) wl'"
        using \<phi> \<phi>1 c unfolding vl vl1 consume_def by (cases wl) auto
        have f: "f ?trn = (disPH, w)" "f ?trn1 = (disPH, w)"
        using \<phi> \<phi>1 c unfolding consume_def vl vl1 ss1 by auto
        have ?match proof
          show "validTrans ?trn1" using step unfolding ss1 by simp
        next
          show "consume ?trn1 vl1 vl'" unfolding consume_def vl1 vl' using \<phi>1 f by auto
        next
          show "\<gamma> ?trn = \<gamma> ?trn1" unfolding ss1 by simp
        next
          assume "\<gamma> ?trn" thus "g ?trn = g ?trn1" by simp
        next
          have "\<Delta>4 s' vl' s' vl'"
          using ph' PID' uuid' unfolding \<Delta>4_def vl' by auto
          thus "?\<Delta> s' vl' s' vl'" by simp
        qed
        thus ?thesis by simp
      next
        case False note \<phi> = False
        hence \<phi>1: "\<not> \<phi> ?trn1" unfolding ss1 by simp
        hence vl': "vl' = vl" using \<phi> c unfolding vl consume_def by auto
        have ?match proof
          show "validTrans ?trn1" using step unfolding ss1 by simp
        next
          show "consume ?trn1 vl1 vl" unfolding consume_def vl1 vl using \<phi>1 by auto
        next
          show "\<gamma> ?trn = \<gamma> ?trn1" unfolding ss1 by simp
        next
          assume "\<gamma> ?trn" thus "g ?trn = g ?trn1" by simp
        next
          have "\<Delta>4 s' vl' s' vl"
          using ph' PID' uuid' unfolding \<Delta>4_def vl' vl by auto
          thus "?\<Delta> s' vl' s' vl" by simp
        qed
        thus ?thesis by simp
      qed
    qed
    thus ?thesis using vl vl1 by simp
  qed
qed

(* Exit arguments: *)
definition K2exit where
"K2exit cid s \<equiv>
 PID \<in>\<in> paperIDs s cid \<and> phase s cid > revPH \<and> \<not> (\<exists> uid. isRevNth s cid uid PID N)"

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
     apply (metis less_not_refl paperIDs_equals reachNT_reach) .
    subgoal for x3 apply(cases x3) apply (auto simp add: uu_defs K2exit_def)
      apply (metis isRev_def3 paperIDs_equals reachNT_reach) .
    by auto
  done

definition K3exit where
"K3exit cid s \<equiv> PID \<in>\<in> paperIDs s cid \<and> phase s cid > revPH"

lemma invarNT_K3exit: "invarNT (K3exit cid)"
unfolding invarNT_def apply (safe dest!: reachNT_reach)
  subgoal for _ a apply(cases a)
    subgoal for x1 apply(cases x1) apply (fastforce simp add: c_defs K3exit_def geq_noPH_confIDs)+ .
    subgoal for x2 apply(cases x2) apply (fastforce simp add: u_defs K3exit_def paperIDs_equals)+ .
    subgoal for x3 apply(cases x3) apply (fastforce simp add: uu_defs K3exit_def)+ .
    by auto
  done

(* The most interesting exit condition so far, not reducible to the "no\<phi>" condition *)
lemma noVal_K3exit: "noVal (K3exit cid) (revPH,u)"
unfolding noVal_def apply safe
  subgoal for _ a apply(cases a)
    subgoal by (fastforce simp add: c_defs K3exit_def)
    subgoal for x2 apply(cases x2) apply (auto simp add: u_defs K3exit_def)
     apply (metis less_not_refl paperIDs_equals reachNT_reach) .
    subgoal for x3 apply(cases x3) apply (auto simp add: uu_defs K3exit_def) .
    by auto
  done

lemma unwind_exit_\<Delta>e: "unwind_exit \<Delta>e"
proof
  fix s s1 :: state and vl vl1 :: "value list"
  assume rsT: "reachNT s" and rs1: "reach s1" and \<Delta>e: "\<Delta>e s vl s1 vl1"
  hence rs:  "reach s" and vl: "vl \<noteq> []" using reachNT_reach unfolding \<Delta>e_def by auto
  then obtain CID where K: "K2exit CID s \<or> K3exit CID s" and PID: "PID \<in>\<in> paperIDs s CID"
  using \<Delta>e unfolding K2exit_def K3exit_def \<Delta>e_def by auto
  show "vl \<noteq> [] \<and> exit s (hd vl)" proof(simp add: vl, cases "K2exit CID s")
    case True
    thus "exit s (hd vl)"
    by (metis rsT exitI2 invarNT_K2exit noVal_K2exit)
  next
    case False
    then obtain u where h: "hd vl = (revPH,u)" and K3: "K3exit CID s"
    using \<Delta>e K PID rs unfolding \<Delta>e_def K2exit_def K3exit_def
    by (cases vl) (auto simp: isREVNth_def)
    show "exit s (hd vl)" unfolding h using K3
    by (metis rsT exitI2 invarNT_K3exit noVal_K3exit)
  qed
qed

theorem secure: secure
apply(rule unwind_decomp4_secure[of \<Delta>1 \<Delta>2 \<Delta>e \<Delta>3 \<Delta>4])
using
istate_\<Delta>1
unwind_cont_\<Delta>1 unwind_cont_\<Delta>2 unwind_cont_\<Delta>2 unwind_cont_\<Delta>3 unwind_cont_\<Delta>4
unwind_exit_\<Delta>e
by auto


end
