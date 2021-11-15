theory Discussion_NCPC
imports "../Observation_Setup" Discussion_Value_Setup "Bounded_Deducibility_Security.Compositional_Reasoning"
begin

subsection \<open>Confidentiality protection from non-PC-members\<close>

text \<open>We verify the following property:

\ \\
A group of users UIDs learn
nothing about the various updates of a paper's discussion
(i.e., about the comments being posted on a paper by the PC members)
(save for the non-existence of any edit)
unless/until a user in UIDs becomes a PC member in the paper's conference having no conflict with that paper
and the conference moves to the discussion phase.

\ \\
\<close>

fun T :: "(state,act,out) trans \<Rightarrow> bool" where
"T (Trans _ _ ou s') =
 (\<exists> uid \<in> UIDs. \<exists> cid.
    PID \<in>\<in> paperIDs s' cid \<and> isPC s' cid uid \<and> pref s' uid PID \<noteq> Conflict \<and> phase s' cid \<ge> disPH
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
"(PID \<in>\<in> paperIDs s cid \<and> isPC s cid uid \<and> phase s cid \<ge> disPH \<longrightarrow> pref s uid PID = Conflict) \<and>
 (PID \<in>\<in> paperIDs s cid \<and> isChair s cid uid \<and> phase s cid \<ge> disPH \<longrightarrow> pref s uid PID = Conflict)"
  using assms
  apply induct
   apply (auto simp: istate_def)[]
  apply(intro conjI)
  subgoal for trn apply(cases trn, auto simp: T.simps reachNT_reach)[] .
  by (metis T.elims(3) isChair_isPC reachNT_reach reach.Step tgtOf_simps)


lemma T_\<phi>_\<gamma>:
assumes 1: "reachNT s" and 2: "step s a = (ou,s')" "\<phi> (Trans s a ou s')"
shows "\<not> \<gamma> (Trans s a ou s')"
using reachNT_non_isPC_isChair[OF 1] 2 unfolding \<phi>_def2
by (fastforce simp add: uu_defs)

(* major *) lemma eqExcPID_step_out:
assumes s's1': "eqExcPID s s1"
and step: "step s a = (ou,s')" and step1: "step s1 a = (ou1,s1')"
and sT: "reachNT s" and s1: "reach s1"
and PID: "PID \<in>\<in> paperIDs s cid"
and UIDs: "userOfA a \<in> UIDs"
shows "ou = ou1"
proof-
  note Inv = reachNT_non_isPC_isChair[OF sT UIDs]
  note eqs = eqExcPID_imp[OF s's1']
  note eqs' = eqExcPID_imp1[OF s's1']
  note s = reachNT_reach[OF sT]

  note simps[simp] = c_defs u_defs uu_defs r_defs l_defs Paper_dest_conv eqExcPID_def eeqExcPID_def eqExcD
  note * = step step1 eqs eqs' s s1 PID UIDs paperIDs_equals[OF s] Inv

  show ?thesis
  proof (cases a)
    case (Cact x1)
    then show ?thesis using * by (cases x1) auto
  next
    case (Uact x2)
    then show ?thesis using * by (cases x2) auto
  next
    case (UUact x3)
    then show ?thesis using * by (cases x3) auto
  next
    case (Ract x4)
    show ?thesis
    proof (cases x4)
      case (rMyReview x81 x82 x83 x84)
      then show ?thesis using * Ract by (auto simp add: getNthReview_def)
    next
      case (rReviews x91 x92 x93 x94)
      then show ?thesis using * Ract by (clarsimp; metis eqExcPID_imp2 s's1')
    next
      case (rDis x111 x112 x113 x114)
      then show ?thesis using * Ract by (clarsimp; metis discussion.inject)
    qed (use * Ract in auto)
  next
    case (Lact x5)
    then show ?thesis using * by (cases x5; auto; presburger)
  qed
qed

definition \<Delta>1 :: "state \<Rightarrow> value list \<Rightarrow> state \<Rightarrow> value list \<Rightarrow> bool" where
"\<Delta>1 s vl s1 vl1 \<equiv>
 (\<forall> cid. PID \<in>\<in> paperIDs s cid \<longrightarrow> phase s cid < disPH) \<and> s = s1 \<and> B vl vl1"

(* main difference from the Paper_Confidentiality/Aut_PC: need to assume
that there are means to produce vl1 via iaction when disPH has been reached;
if not, this yields and exit *)
definition \<Delta>2 :: "state \<Rightarrow> value list \<Rightarrow> state \<Rightarrow> value list \<Rightarrow> bool" where
"\<Delta>2 s vl s1 vl1 \<equiv>
 \<exists> cid uid.
    PID \<in>\<in> paperIDs s cid \<and> phase s cid = disPH \<and>
    isPC s cid uid \<and> pref s uid PID \<noteq> Conflict
    \<and> eqExcPID s s1"

definition \<Delta>3 :: "state \<Rightarrow> value list \<Rightarrow> state \<Rightarrow> value list \<Rightarrow> bool" where
"\<Delta>3 s vl s1 vl1 \<equiv>
 \<exists> cid. PID \<in>\<in> paperIDs s cid \<and> phase s cid > disPH \<and> eqExcPID s s1 \<and> vl1 = []"

definition \<Delta>e :: "state \<Rightarrow> value list \<Rightarrow> state \<Rightarrow> value list \<Rightarrow> bool" where
"\<Delta>e s vl s1 vl1 \<equiv>
 vl \<noteq> [] \<and>
 (\<exists> cid. PID \<in>\<in> paperIDs s cid \<and> phase s cid \<ge> disPH \<and>
         \<not> (\<exists> uid. isPC s cid uid \<and> pref s uid PID \<noteq> Conflict)
 )"

lemma init_\<Delta>1:
assumes B: "B vl vl1"
shows "\<Delta>1 istate vl istate vl1"
using B unfolding \<Delta>1_def B_def istate_def by auto

lemma unwind_cont_\<Delta>1: "unwind_cont \<Delta>1 {\<Delta>1,\<Delta>2,\<Delta>e}"
proof(rule, simp)
  let ?\<Delta> = "\<lambda>s vl s1 vl1. \<Delta>1 s vl s1 vl1 \<or> \<Delta>2 s vl s1 vl1 \<or> \<Delta>e s vl s1 vl1"
  fix s s1 :: state and vl vl1 :: "value list"
  assume rsT: "reachNT s" and rs1: "reach s1" and "\<Delta>1 s vl s1 vl1"
  hence rs: "reach s" and ss1: "s1 = s" and vl: "vl \<noteq> []"
  and PID_ph: "\<And> cid. PID \<in>\<in> paperIDs s cid \<Longrightarrow> phase s cid < disPH"
  using reachNT_reach unfolding \<Delta>1_def B_def by auto
  show "iaction ?\<Delta> s vl s1 vl1 \<or>
        ((vl = [] \<longrightarrow> vl1 = []) \<and> reaction ?\<Delta> s vl s1 vl1)" (is "?iact \<or> (_ \<and> ?react)")
  proof-
    have ?react proof
      fix a :: act and ou :: out and s' :: state and vl'
      let ?trn = "Trans s a ou s'"  let ?trn1 = "Trans s1 a ou s'"
      assume step: "step s a = (ou, s')" and T: "\<not> T ?trn" and c: "consume ?trn vl vl'"
      have \<phi>: "\<not> \<phi> ?trn"
      proof (cases a)
        case (UUact x3)
        then show ?thesis
          using step PID_ph
          by (cases x3; fastforce simp: uu_defs)
      qed auto
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
            have ph_PID': "\<And> cid. PID \<in>\<in> paperIDs s' cid \<Longrightarrow> phase s' cid < disPH" using PID step rs
            subgoal apply(cases a)
              subgoal for x1 apply(cases x1) apply(fastforce simp: c_defs)+ .
              subgoal for x2 apply(cases x2) apply(fastforce simp: u_defs)+ .
              subgoal for x3 apply(cases x3) apply(fastforce simp: uu_defs)+ .
              by auto
            done
            hence "\<Delta>1 s' vl' s' vl1" unfolding \<Delta>1_def B_def vl' using ph_PID' vl by auto
            thus ?thesis by auto
          next
            case True then obtain CID where PID: "PID \<in>\<in> paperIDs s CID" by auto
            hence ph: "phase s CID < disPH" (is "?ph < _") using PID_ph by auto
            show ?thesis
            proof(cases "phase s' CID < disPH")
              case True note ph' = True
              show ?thesis proof(cases "PID \<in>\<in> paperIDs s' CID")
                case False
                hence "\<Delta>1 s' vl' s' vl1" unfolding \<Delta>1_def B_def vl' using vl ph' apply auto
                by (metis PID paperIDs_mono step)(* safety crucially used *)
                thus ?thesis by auto
              next
                case True
                hence "\<Delta>1 s' vl' s' vl1" unfolding \<Delta>1_def B_def vl' using vl ph' apply auto
                by (metis reach_PairI paperIDs_equals rs step) (* safety crucially used *)
                thus ?thesis by auto
              qed
            next
              case False
              hence ph': "phase s' CID = disPH \<and> PID \<in>\<in> paperIDs s' CID"
              using PID ph step rs
              subgoal apply(cases a)
                subgoal for x1 apply(cases x1) apply(fastforce simp: c_defs)+ .
                subgoal for x2 apply(cases x2) apply(fastforce simp: u_defs)+ .
                subgoal for x3 apply(cases x3) apply(fastforce simp: uu_defs)+ .
              by auto
            done
              show ?thesis
              proof(cases "\<exists>uid. isPC s' CID uid \<and> pref s' uid PID \<noteq> Conflict")
                case True
                hence "\<Delta>2 s' vl' s' vl1" unfolding \<Delta>2_def vl' using vl ph' by auto
                thus ?thesis by auto
              next
                case False
                hence "\<Delta>e s' vl' s' vl1" unfolding \<Delta>e_def vl' using vl ph' by auto
                thus ?thesis by auto
              qed
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
  then obtain CID uid where uid: "isPC s CID uid" "pref s uid PID \<noteq> Conflict"
  and rs: "reach s" and ph: "phase s CID = disPH" (is "?ph = _")
  and PID: "PID \<in>\<in> paperIDs s CID" and ss1: "eqExcPID s s1"
  using reachNT_reach unfolding \<Delta>2_def by auto
  hence uid_notin: "uid \<notin> UIDs" using ph reachNT_non_isPC_isChair[OF rsT] by force
  show "iaction ?\<Delta> s vl s1 vl1 \<or>
        ((vl = [] \<longrightarrow> vl1 = []) \<and> reaction ?\<Delta> s vl s1 vl1)" (is "?iact \<or> (_ \<and> ?react)")
  proof(cases vl1)
    case (Cons v1 vl1') note vl1 = Cons
    have uid1: "isPC s1 CID uid" "pref s1 uid PID \<noteq> Conflict"
    using ss1 uid unfolding eqExcPID_def by auto
    define a1 where "a1 \<equiv> UUact (uuDis CID uid (pass s uid) PID v1)"
    obtain s1' ou1 where step1: "step s1 a1 = (ou1,s1')" by (metis prod.exhaust)
    let ?trn1 = "Trans s1 a1 ou1 s1'"
    have s1s1': "eqExcPID s1 s1'" using a1_def step1 UUact_uuDis_step_eqExcPID by auto
    have ss1': "eqExcPID s s1'" using eqExcPID_trans[OF ss1 s1s1'] .
    hence many_s1': "PID \<in>\<in> paperIDs s1' CID" "isPC s1' CID uid"
    "pref s1' uid PID \<noteq> Conflict" "phase s1' CID = disPH"
    "pass s1' uid = pass s uid"
    using uid PID ph unfolding eqExcPID_def by auto
    hence more_s1': "uid \<in>\<in> userIDs s1'" "CID \<in>\<in> confIDs s1'"
    by (metis paperIDs_confIDs reach_PairI roles_userIDs rs1 step1 many_s1'(1))+
    have f: "f ?trn1 = v1" unfolding a1_def by simp
    have rs1': "reach s1'" using rs1 step1 by (auto intro: reach_PairI)
    have ou1: "ou1 = outOK"
    using step1 uid1 ph unfolding a1_def by (auto simp add: uu_defs many_s1' more_s1')
    have ?iact proof
      show "step s1 a1 = (ou1,s1')" by fact
    next
      show \<phi>: "\<phi> ?trn1" using ou1 unfolding a1_def by simp
      thus "consume ?trn1 vl1 vl1'" using f unfolding consume_def vl1 by simp
    next
      show "\<not> \<gamma> ?trn1" by (simp add: a1_def uid_notin)
    next
      have "\<Delta>2 s vl s1' vl1'" unfolding \<Delta>2_def using ph PID ss1' uid by auto
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
      have uid': "isPC s' CID uid \<and> pref s' uid PID \<noteq> Conflict"
      using uid step rs ph PID pref_Conflict_disPH isPC_persistent by auto
      show "match ?\<Delta> s s1 vl1 a ou s' vl' \<or> ignore ?\<Delta> s s1 vl1 a ou s' vl'" (is "?match \<or> ?ignore")
      proof(cases "\<phi> ?trn")
        case False note \<phi> = False
        have vl: "vl' = vl" using c \<phi> unfolding consume_def by (cases vl) auto
        obtain ou1 and s1' where step1: "step s1 a = (ou1,s1')" by (metis prod.exhaust)
        let ?trn1 = "Trans s1 a ou1 s1'"
        have s's1': "eqExcPID s' s1'" using eqExcPID_step[OF ss1 step step1] .
        have \<phi>1: "\<not> \<phi> ?trn1" using \<phi> unfolding eqExcPID_step_\<phi>[OF ss1 step step1] .
        have ?match proof
          show "validTrans ?trn1" using step1 by simp
        next
          show "consume ?trn1 vl1 vl1" unfolding consume_def using \<phi>1 by auto
        next
          show "\<gamma> ?trn = \<gamma> ?trn1" unfolding ss1 by simp
        next
          assume "\<gamma> ?trn" thus "g ?trn = g ?trn1"
          using eqExcPID_step_out[OF ss1 step step1 rsT rs1 PID] by simp
        next
          show "?\<Delta> s' vl' s1' vl1"
          proof(cases "?ph' = disPH")
            case True
            hence "\<Delta>2 s' vl' s1' vl1" using PID' s's1' uid' unfolding \<Delta>2_def by auto
            thus ?thesis by auto
          next
            case False hence "?ph' > disPH"
            using ph rs step by (metis le_less phase_increases)
            hence "\<Delta>3 s' vl' s1' vl1" using s's1' PID' unfolding \<Delta>3_def vl1 by auto
            thus ?thesis by auto
          qed
        qed
        thus ?thesis by simp
      next
        case True note \<phi> = True
        have s's: "eqExcPID s' s" using eqExcPID_sym[OF \<phi>_step_eqExcPID[OF \<phi> step]] .
        have s's1: "eqExcPID s' s1" using eqExcPID_trans[OF s's ss1] .
        have ?ignore proof
          show "\<not> \<gamma> ?trn" using T_\<phi>_\<gamma> \<phi> rsT step by auto
        next
          show "?\<Delta> s' vl' s1 vl1"
          proof(cases "?ph' = disPH")
            case True
            hence "\<Delta>2 s' vl' s1 vl1" using s's1 PID' uid' unfolding \<Delta>2_def by auto
            thus ?thesis by auto
          next
            case False hence "?ph' > disPH"
            using ph rs step by (metis le_less phase_increases)
            hence "\<Delta>3 s' vl' s1 vl1" using s's1 PID' unfolding \<Delta>3_def vl1 by auto
            thus ?thesis by auto
          qed
        qed
        thus ?thesis by auto
      qed
    qed
    thus ?thesis using vl1 by auto
  qed
qed

lemma unwind_cont_\<Delta>3: "unwind_cont \<Delta>3 {\<Delta>3,\<Delta>e}"
proof(rule, simp)
  let ?\<Delta> = "\<lambda>s vl s1 vl1. \<Delta>3 s vl s1 vl1 \<or> \<Delta>e s vl s1 vl1"
  fix s s1 :: state and vl vl1 :: "value list"
  assume rsT: "reachNT s" and rs1: "reach s1" and "\<Delta>3 s vl s1 vl1"
  then obtain CID where rs: "reach s" and ph: "phase s CID > disPH" (is "?ph < _")
  and PID: "PID \<in>\<in> paperIDs s CID"
  and ss1: "eqExcPID s s1" and vl1: "vl1 = []"
  using reachNT_reach unfolding \<Delta>3_def by auto
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
      have ph': "phase s' CID > disPH" using ph rs by (meson less_le_trans local.step phase_increases)
      show "match ?\<Delta> s s1 vl1 a ou s' vl' \<or> ignore ?\<Delta> s s1 vl1 a ou s' vl'" (is "?match \<or> ?ignore")
      proof-
        have \<phi>: "\<not> \<phi> ?trn" using ph step unfolding \<phi>_def2 apply (auto simp: uu_defs)
        using PID less_not_refl2 paperIDs_equals rs by blast (* safety crucialy used *)
        have vl: "vl' = vl" using c \<phi> unfolding consume_def by (cases vl) auto
        obtain ou1 and s1' where step1: "step s1 a = (ou1,s1')" by (metis prod.exhaust)
        let ?trn1 = "Trans s1 a ou1 s1'"
        have s's1': "eqExcPID s' s1'" using eqExcPID_step[OF ss1 step step1] .
        have \<phi>1: "\<not> \<phi> ?trn1" using \<phi> unfolding eqExcPID_step_\<phi>[OF ss1 step step1] .
        have ?match proof
          show "validTrans ?trn1" using step1 by simp
        next
          show "consume ?trn1 vl1 vl1" unfolding consume_def using \<phi>1 by auto
        next
          show "\<gamma> ?trn = \<gamma> ?trn1" unfolding ss1 by simp
        next
          assume "\<gamma> ?trn" thus "g ?trn = g ?trn1"
          using eqExcPID_step_out[OF ss1 step step1 rsT rs1 PID] by simp
        next
          have "\<Delta>3 s' vl' s1' vl1" using ph' PID' s's1' unfolding \<Delta>3_def vl1 by auto
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
"K1exit cid s \<equiv>
 (PID \<in>\<in> paperIDs s cid \<and> phase s cid \<ge> disPH \<and>
  \<not> (\<exists> uid. isPC s cid uid \<and> pref s uid PID \<noteq> Conflict))"

lemma invarNT_K1exit: "invarNT (K1exit cid)"
unfolding invarNT_def apply (safe dest!: reachNT_reach)
  subgoal for _ a apply(cases a)
    subgoal for x1 apply(cases x1) apply (fastforce simp add: c_defs K1exit_def geq_noPH_confIDs)+ .
    subgoal for x2
      apply(cases x2)
            apply (fastforce simp add: u_defs K1exit_def paperIDs_equals)
           apply (fastforce simp add: u_defs K1exit_def paperIDs_equals)
          apply (fastforce simp add: u_defs K1exit_def paperIDs_equals)
         apply (fastforce simp add: u_defs K1exit_def paperIDs_equals)
        apply (fastforce simp add: u_defs K1exit_def paperIDs_equals)
        subgoal for x61 apply(cases "x61 = cid")
           apply (fastforce simp add: u_defs K1exit_def paperIDs_equals)+ .
        apply (fastforce simp add: u_defs K1exit_def paperIDs_equals) .
    subgoal for x3 apply(cases x3) apply (fastforce simp add: uu_defs K1exit_def)+ .
    by auto
  done

lemma noVal_K1exit: "noVal (K1exit cid) v"
apply(rule no\<phi>_noVal)
unfolding no\<phi>_def apply safe
  subgoal for _ a apply(cases a)
        apply (fastforce simp add: c_defs K1exit_def)
       apply (fastforce simp add: c_defs K1exit_def)
    subgoal for x3
      apply(cases x3) apply (auto simp add: uu_defs K1exit_def)
      apply (metis paperIDs_equals reachNT_reach) (* crucial use of safety *) .
    by auto
  done

lemma unwind_exit_\<Delta>e: "unwind_exit \<Delta>e"
proof
  fix s s1 :: state and vl vl1 :: "value list"
  assume rsT: "reachNT s" and rs1: "reach s1" and \<Delta>e: "\<Delta>e s vl s1 vl1"
  hence vl: "vl \<noteq> []" using reachNT_reach unfolding \<Delta>e_def by auto
  then obtain CID where "K1exit CID s" using \<Delta>e unfolding K1exit_def \<Delta>e_def by auto
  thus "vl \<noteq> [] \<and> exit s (hd vl)" apply(simp add: vl)
  by (metis rsT exitI2 invarNT_K1exit noVal_K1exit)
qed

theorem secure: secure
apply(rule unwind_decomp3_secure[of \<Delta>1 \<Delta>2 \<Delta>e \<Delta>3])
using
init_\<Delta>1
unwind_cont_\<Delta>1 unwind_cont_\<Delta>2 unwind_cont_\<Delta>3
unwind_exit_\<Delta>e
by auto

end
