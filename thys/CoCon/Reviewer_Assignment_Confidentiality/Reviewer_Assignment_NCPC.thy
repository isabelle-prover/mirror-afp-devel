theory Reviewer_Assignment_NCPC
imports "../Observation_Setup" Reviewer_Assignment_Value_Setup "Bounded_Deducibility_Security.Compositional_Reasoning"
begin

subsection \<open>Confidentiality protection from non-PC-members\<close>

text \<open>We verify the following property:

\ \\
A group of users UIDs learn
nothing about the reviewers assigned to a paper PID
except for their number and the fact that they are PC members having no conflict
with that paper
unless/until the user becomes a PC member in the paper's conference
having no conflict with that paper and the conference moves to the reviewing phase.

\ \\
\<close>


fun T :: "(state,act,out) trans \<Rightarrow> bool" where
"T (Trans _ _ ou s') =
 (\<exists> uid \<in> UIDs. \<exists> cid.
    PID \<in>\<in> paperIDs s' cid \<and> isPC s' cid uid \<and> pref s' uid PID \<noteq> Conflict \<and> phase s' cid \<ge> revPH)"

term isAUT

declare T.simps [simp del]

(*
The explanation of what this bound says is similar to that of
the bound in Reviewer_Assignment_NCPC_Aut, just that the value vl'
is additionally assumed to have the same length as vl (i.e.,
using the notations from that explanation, m = n).
*)

definition B :: "value list \<Rightarrow> value list \<Rightarrow> bool" where
"B vl vl1 \<equiv>
 vl \<noteq> [] \<and>
 length vl = length vl1 \<and>
 distinct (map fst vl1) \<and> fst ` (set vl1) \<subseteq> snd (hd vl) \<and> snd ` (set vl1) = {snd (hd vl)}"

interpretation BD_Security_IO where
istate = istate and step = step and
\<phi> = \<phi> and f = f and \<gamma> = \<gamma> and g = g and T = T and B = B
done

lemma reachNT_non_isPC_isChair:
assumes "reachNT s" and "uid \<in> UIDs"
shows
"(PID \<in>\<in> paperIDs s cid \<and> isPC s cid uid \<longrightarrow>
    pref s uid PID = Conflict \<or> phase s cid < revPH) \<and>
 (PID \<in>\<in> paperIDs s cid \<and> isChair s cid uid \<longrightarrow>
    pref s uid PID = Conflict \<or> phase s cid < revPH)"
  using assms
  apply induct
  subgoal by (auto simp: istate_def)
  subgoal apply(intro conjI)
     apply (metis T.simps not_le_imp_less trans.collapse)
    by (metis T.simps isChair_isPC not_le_imp_less reachNT.Step reachNT_reach trans.collapse)
  done

lemma T_\<phi>_\<gamma>:
assumes 1: "reachNT s" and 2: "step s a = (ou,s')" "\<phi> (Trans s a ou s')"
shows "\<not> \<gamma> (Trans s a ou s')"
using reachNT_non_isPC_isChair[OF 1] 2 unfolding T.simps \<phi>_def2
by (fastforce simp: c_defs isRev_imp_isRevNth_getReviewIndex)

lemma T_\<phi>_\<gamma>_stronger:
assumes s: "reach s" and 0: "PID \<in>\<in> paperIDs s cid"
and 2: "step s a = (ou,s')" "\<phi> (Trans s a ou s')"
and 1: "\<forall> uid \<in> UIDs. isChair s cid uid \<longrightarrow> pref s uid PID = Conflict \<or> phase s cid < revPH"
shows "\<not> \<gamma> (Trans s a ou s')"
proof-
  have "\<not> (\<exists> uid \<in> UIDs. \<exists> cid. PID \<in>\<in> paperIDs s cid \<and>
  isChair s cid uid \<and> pref s uid PID \<noteq> Conflict \<and> phase s cid \<ge> revPH)"
  using 0 1 s by (metis not_le paperIDs_equals)
  thus ?thesis using assms unfolding T.simps \<phi>_def2 by (force simp add: c_defs)
qed

lemma T_\<phi>_\<gamma>_1:
assumes s: "reachNT s" and s1: "reach s1" and PID: "PID \<in>\<in> paperIDs s cid"
and ss1: "eqExcPID s s1"
and step1: "step s1 a = (ou1,s1')" and \<phi>1: "\<phi> (Trans s1 a ou1 s1')"
and \<phi>: "\<not> \<phi> (Trans s a ou s')"
shows "\<not> \<gamma> (Trans s1 a ou1 s1')"
proof-
  have "\<forall> uid \<in> UIDs. isChair s cid uid \<longrightarrow> pref s uid PID = Conflict \<or> phase s cid < revPH"
  using reachNT_non_isPC_isChair[OF s] PID by auto
  hence 1: "\<forall> uid \<in> UIDs. isChair s1 cid uid \<longrightarrow> pref s1 uid PID = Conflict \<or> phase s1 cid < revPH"
  using ss1 unfolding eqExcPID_def using eqExcRLR_imp2 by fastforce
  have PID1: "PID \<in>\<in> paperIDs s1 cid" using PID ss1 eqExcPID_imp by auto
  show ?thesis apply(rule T_\<phi>_\<gamma>_stronger[OF s1 PID1 step1 \<phi>1]) using 1 by auto
qed

lemma notIsPCorConflict_eqExcPID_roles_eq:
assumes s: "reach s" and s1: "reach s1" and PID: "PID \<in>\<in> paperIDs s cid"
and pc: "\<not> isPC s cid uid \<or> pref s uid PID = Conflict"
and eeq: "eqExcPID s s1"
shows "roles s cid uid = roles s1 cid uid"
proof-
  have eq: "eqExcRLR (roles s cid uid) (roles s1 cid uid)"
  using eeq unfolding eqExcPID_def by auto
  have "\<not> isPC s1 cid uid \<or> pref s1 uid PID = Conflict"
  using pc eqExcPID_imp[OF eeq] eqExcRLR_imp2[OF eq] by auto
  hence "\<not> isRev s cid uid PID \<and> \<not> isRev s1 cid uid PID" using pc s s1 PID
  by (metis isRev_pref_notConflict_isPC)
  thus ?thesis using eq unfolding eqExcRLR_def
  by (metis Bex_set_list_ex filter_id_conv isRev_def)
qed

lemma notInPaperIDs_eqExcPID_roles_eq:
assumes s: "reach s" and s1: "reach s1" and PID: "\<not> PID \<in>\<in> paperIDs s cid"
and eq: "eqExcPID s s1"
shows "roles s cid uid = roles s1 cid uid"
proof-
  have "\<not> PID \<in>\<in> paperIDs s1 cid" using PID eq unfolding eqExcPID_def by auto
  hence "\<not> isRev s cid uid PID \<and> \<not> isRev s1 cid uid PID" using s s1 PID by (metis isRev_paperIDs)
  thus ?thesis using eq unfolding eqExcPID_def eqExcRLR_def
  by (metis Bex_set_list_ex filter_True isRev_def)
qed

(* major *) lemma eqExcPID_step_out:
assumes ss1: "eqExcPID s s1"
and step: "step s a = (ou,s')" and step1: "step s1 a = (ou1,s1')"
and sT: "reachNT s" and s1: "reach s1"
and PID: "PID \<in>\<in> paperIDs s cid" and ph: "phase s cid \<ge> revPH"
and \<phi>: "\<not> \<phi> (Trans s a ou s')" and \<phi>1: "\<not> \<phi> (Trans s1 a ou1 s1')"  and \<chi>: "\<not> \<chi> a"
and UIDs: "userOfA a \<in> UIDs"
shows "ou = ou1"
proof-
  note s = reachNT_reach[OF sT]
  have s': "reach s'" and s1': "reach s1'" by (metis reach_PairI s s1 step step1)+
  have s's1': "eqExcPID s' s1'"
  using \<chi> \<phi> \<phi>1 eqExcPID_step eqExcPID_sym s s1 ss1 step step1 step_outErr_eq
  by (metis PID isAut_paperIDs notInPaperIDs_eqExcPID_roles_eq paperID_ex_userID1 paperID_ex_userID_def)
  have s1's': "eqExcPID s1' s'" by (metis eqExcPID_sym s's1')
  have s': "reach s'" by (metis reach_PairI s step)
  have ph1: "phase s1 cid \<ge> revPH" using ph ss1 unfolding eqExcPID_def by auto
  have ph': "phase s' cid \<ge> revPH" and ph1': "phase s1' cid \<ge> revPH"
  using ph ph1 by (metis dual_order.trans phase_increases step step1)+
  note Inv = reachNT_non_isPC_isChair[OF sT UIDs]
  note eqs = eqExcPID_imp[OF ss1]
  note eqs' = eqExcPID_imp1[OF ss1]

  note simps[simp] = c_defs u_defs uu_defs r_defs l_defs Paper_dest_conv eqExcPID_def
  note simps2[simp] = eqExcRLR_imp[of s _ _ _ s1, OF s] eqExcRLR_imp[of s' _ _ _ s1']
                eqExcRLR_imp[of s _ _ _ s1'] eqExcRLR_imp[of s' _ _ _ s1]
      eqExcRLR_imp2[of s _ _ s1] eqExcRLR_imp2[of s' _ _ s1']
                eqExcRLR_imp2[of s _ _ s1'] eqExcRLR_imp2[of s' _ _ s1]
      eqExcRLR_set[of "(roles s cid uid)" "(roles s1 cid uid)" for cid uid]
      eqExcRLR_set[of "(roles s cid uid)" "(roles s1' cid uid)" for cid uid]
      eqExcRLR_set[of "(roles s' cid uid)" "(roles s1 cid uid)" for cid uid]
      eqExcRLR_set[of "(roles s' cid uid)" "(roles s1' cid uid)" for cid uid]
      foo2 foo3
      eqExcRLR_imp_isRevRole_imp

  {fix cid uid p pid assume "a = Ract (rMyReview cid uid p pid)"
   hence ?thesis
   using step step1 eqs eqs' s s1 UIDs PID \<phi> \<phi>1 \<chi> paperIDs_equals[OF s] Inv
   apply (auto simp add: isRev_getRevRole getRevRole_Some)[]
   apply (metis eqExcPID_imp' isRev_isPC not_less option.inject pref_Conflict_isRev role.distinct role.inject s1's'
                isRev_isPC not_less pref_Conflict_isRev simps2(1) simps2(8) isRev_getRevRole getRevRole_Some)+
   done
  } note this[simp]

  have ?thesis
    using step step1 eqs eqs' s s1 UIDs PID \<phi> \<phi>1 \<chi>
    paperIDs_equals[OF s] Inv
    apply(cases a, simp_all only:)
      subgoal for x1 apply(cases x1)
        apply auto[] apply auto[] apply auto[] apply auto[]
        apply auto[] apply auto[] apply auto[] apply auto[] .
      subgoal for x2 apply(cases x2)
        apply auto[] apply auto[] apply auto[] apply auto[]
        apply auto[] apply auto[] apply auto[] .
      subgoal for x3 apply(cases x3)
        apply auto[] apply auto[] apply auto[] apply auto[] .
      subgoal for x4 apply(cases x4)
        apply auto[] apply auto[] apply auto[] apply auto[]
        apply auto[] apply auto[] apply auto[] apply auto[]
        apply clarsimp apply (metis eqExcPID_imp2 not_less ph' s's1')
        apply auto[] apply auto[] apply auto[] apply auto[]
        apply auto[] .
     subgoal for x5 apply(cases x5)
        apply auto[] apply auto[] apply auto[]
        apply clarsimp apply (metis (opaque_lifting) empty_iff list.set(1) notInPaperIDs_eqExcPID_roles_eq notIsPCorConflict_eqExcPID_roles_eq s's1' s1's')
        apply auto[] apply auto[] apply auto[] apply auto[]
        apply auto[] apply auto[]
        apply clarsimp apply (metis Suc_leI filter_cong isRev_pref_notConflict_isPC not_less_eq_eq simps2(2))
        apply clarsimp apply (metis not_less simps2(1)) .
     done

  note * = step step1 eqs eqs' s s1 UIDs PID \<phi> \<phi>1 \<chi> paperIDs_equals[OF s] Inv

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
      case (rReviews x91 x92 x93 x94)
      with Ract * show ?thesis
        by clarsimp (metis eqExcPID_imp2 not_less ph' s's1')
    qed auto
  next
    case (Lact x5)
    with * show ?thesis
    proof (cases x5)
      case (lMyConfs x41 x42)
      with Lact * show ?thesis
        by clarsimp (metis (opaque_lifting) empty_iff list.set(1) notInPaperIDs_eqExcPID_roles_eq notIsPCorConflict_eqExcPID_roles_eq s's1' s1's')
    next
      case (lMyAssignedPapers x111 x112 x113)
      with Lact * show ?thesis
        by clarsimp (metis Suc_leI filter_cong isRev_pref_notConflict_isPC not_less_eq_eq simps2(2))
    next
      case (lAssignedReviewers x121 x122 x123 x124)
      with Lact * show ?thesis
        by clarsimp (metis not_less simps2(1))
    qed auto
  qed
qed

lemma eqExcPID_step_\<phi>_eqExcPID_out:
assumes s: "reach s" and s1: "reach s1"
and a: "a = Cact (cReview cid uid p PID uid')"
and a1: "a1 = Cact (cReview cid uid p PID uid1')"
and ss1: "eqExcPID s s1" and step: "step s a = (outOK,s')"
and pc: "isPC s cid uid1' \<and> pref s uid1' PID \<noteq> Conflict"
and rv1: "\<not> isRev s1 cid uid1' PID" and step1: "step s1 a1 = (ou1,s1')"
shows "eqExcPID s' s1' \<and> ou1 = outOK"
proof-
  have s': "reach s'" and s1': "reach s1'" by (metis reach_PairI s s1 step step1)+
  have c: "isChair s cid uid \<and> pref s uid PID \<noteq> Conflict \<and>
   phase s cid = revPH \<and> pass s uid = p \<and>
   PID \<in>\<in> paperIDs s cid \<and> cid \<in>\<in> confIDs s"
  using step unfolding a by (auto simp: c_defs)
  hence c1: "isChair s1 cid uid \<and> pref s1 uid PID \<noteq> Conflict \<and>
    phase s1 cid = revPH \<and> pass s1 uid = p \<and>
   PID \<in>\<in> paperIDs s1 cid \<and> cid \<in>\<in> confIDs s1"
  and pc1: "isPC s1 cid uid1' \<and> pref s1 uid1' PID \<noteq> Conflict"
  using pc ss1 unfolding eqExcPID_def using eqExcRLR_imp2 by metis+

  note simps[simp] = c_defs u_defs uu_defs r_defs l_defs Paper_dest_conv eqExcPID_def
  note simps2[simp] = eqExcRLR_imp[of s _ _ _ s1, OF s] eqExcRLR_imp[of s' _ _ _ s1']
                eqExcRLR_imp[of s _ _ _ s1'] eqExcRLR_imp[of s' _ _ _ s1]
      eqExcRLR_imp2[of s _ _ s1] eqExcRLR_imp2[of s' _ _ s1']
                eqExcRLR_imp2[of s _ _ s1'] eqExcRLR_imp2[of s' _ _ s1]
      eqExcRLR_set[of "(roles s cid uid)" "(roles s1 cid uid)" for cid uid]
      eqExcRLR_set[of "(roles s cid uid)" "(roles s1' cid uid)" for cid uid]
      eqExcRLR_set[of "(roles s' cid uid)" "(roles s1 cid uid)" for cid uid]
      eqExcRLR_set[of "(roles s' cid uid)" "(roles s1' cid uid)" for cid uid]
      foo2 foo3
      eqExcRLR_imp_isRevRole_imp

  show ?thesis
  using pc1 c1 ss1 step step1 c c1 pc rv1 unfolding eqExcPID_def a a1
  using roles_userIDs s1' by force
qed

lemma eqExcPID_ex_isNthReview:
assumes s: "reach s" and s1: "reach s1" and e: "eqExcPID s s1"
and i: "isRevNth s cid uid PID n"
shows "\<exists> uid1. isRevNth s1 cid uid1 PID n"
proof-
  have PID: "PID \<in>\<in> paperIDs s cid" by (metis i isRevNth_paperIDs s)
  have "n < length (reviewsPaper (paper s PID))" using s i by (metis isRevNth_less_length)
  hence "PID \<in>\<in> paperIDs s1 cid \<and> n < length (reviewsPaper (paper s1 PID))"
  using e PID unfolding eqExcPID_def by auto
  thus ?thesis using s1 by (metis reviews_compact)
qed

lemma eqExcPID_step_\<chi>1:
assumes s: "reach s" and s1: "reach s1"
and a: "a = Uact (uReview cid uid p PID n rc)"
and ss1: "eqExcPID s s1" and step: "step s a = (outOK,s')"
shows
"\<exists> s1' uid1 p.
   isRevNth s1 cid uid1 PID n \<and>
   step s1 (Uact (uReview cid uid1 p PID n rc)) = (outOK,s1') \<and>
   eqExcPID s' s1'"
proof-
  have s': "reach s'" by (metis reach_PairI s step)
  have c: "isRevNth s cid uid PID n \<and> phase s cid = revPH \<and> PID \<in>\<in> paperIDs s cid \<and> cid \<in>\<in> confIDs s"
  using step unfolding a apply (auto simp: u_defs) by (metis isRev_imp_isRevNth_getReviewIndex)
  obtain uid1 where rv1: "isRevNth s1 cid uid1 PID n" using s s1 ss1 by (metis c eqExcPID_ex_isNthReview)
  let ?p = "pass s1 uid1"
  define a1 where a1: "a1 \<equiv> Uact (uReview cid uid1 (pass s1 uid1) PID n rc)"
  obtain ou1 s1' where step1: "step s1 a1 = (ou1,s1')" by (metis surj_pair)
  have s1': "reach s1'" by (metis reach_PairI s1 step1)
  have c1: "phase s1 cid = revPH \<and> PID \<in>\<in> paperIDs s1 cid \<and> cid \<in>\<in> confIDs s1"
  using ss1 c unfolding eqExcPID_def using eqExcRLR_imp2 by auto
  show ?thesis
  apply(intro exI[of _ s1'] exI[of _ uid1] exI[of _ ?p])
  using rv1 c1 ss1 step step1 c c1 rv1 unfolding eqExcPID_def a a1
  using isRevNth_getReviewIndex isRev_def2 roles_userIDs s1'
  by ((auto
          simp: u_defs
          simp: Paper_dest_conv
          simp: eqExcPID_def
      ))
qed

lemma eqExcPID_step_\<chi>2:
assumes s: "reach s" and s1: "reach s1"
and a: "a = UUact (uuReview cid uid p PID n rc)"
and ss1: "eqExcPID s s1" and step: "step s a = (outOK,s')"
shows
"\<exists> s1' uid1 p.
   isRevNth s1 cid uid1 PID n \<and>
   step s1 (UUact (uuReview cid uid1 p PID n rc)) = (outOK,s1') \<and>
   eqExcPID s' s1'"
proof-
  have s': "reach s'" by (metis reach_PairI s step)
  have c: "isRevNth s cid uid PID n \<and> phase s cid = disPH \<and> PID \<in>\<in> paperIDs s cid \<and> cid \<in>\<in> confIDs s"
  using step unfolding a apply (auto simp: uu_defs) by (metis isRev_imp_isRevNth_getReviewIndex)
  obtain uid1 where rv1: "isRevNth s1 cid uid1 PID n" using s s1 ss1 by (metis c eqExcPID_ex_isNthReview)
  let ?p = "pass s1 uid1"
  define a1 where  a1: "a1 \<equiv> UUact (uuReview cid uid1 (pass s1 uid1) PID n rc)"
  obtain ou1 s1' where step1: "step s1 a1 = (ou1,s1')" by (metis surj_pair)
  have s1': "reach s1'" by (metis reach_PairI s1 step1)
  have c1: "phase s1 cid = disPH \<and> PID \<in>\<in> paperIDs s1 cid \<and> cid \<in>\<in> confIDs s1"
  using ss1 c unfolding eqExcPID_def using eqExcRLR_imp2 by auto
  show ?thesis
  apply(intro exI[of _ s1'] exI[of _ uid1] exI[of _ ?p])
  using rv1 c1 ss1 step step1 c c1 rv1 unfolding eqExcPID_def a a1
  using isRevNth_getReviewIndex isRev_def2 roles_userIDs s1'
  by ((force
          simp: uu_defs
          simp: Paper_dest_conv
          simp: eqExcPID_def
      ))
qed


definition \<Delta>1 :: "state \<Rightarrow> value list \<Rightarrow> state \<Rightarrow> value list \<Rightarrow> bool" where
"\<Delta>1 s vl s1 vl1 \<equiv>
 (\<forall> cid. PID \<in>\<in> paperIDs s cid \<longrightarrow> phase s cid < revPH) \<and> s = s1
 \<and> B vl vl1"

definition \<Delta>2 :: "state \<Rightarrow> value list \<Rightarrow> state \<Rightarrow> value list \<Rightarrow> bool" where
"\<Delta>2 s vl s1 vl1 \<equiv>
 \<exists> cid uid.
   PID \<in>\<in> paperIDs s cid \<and> phase s cid = revPH \<and>
   isChair s cid uid \<and> pref s uid PID \<noteq> Conflict \<and>
   eqExcPID s s1 \<and>
   length vl = length vl1 \<and>
   distinct (map fst vl1) \<and>
   fst ` (set vl1) \<subseteq> {uid'. isPC s cid uid' \<and> pref s uid' PID \<noteq> Conflict} \<and>
   fst ` (set vl1) \<inter> {uid'. isRev s1 cid uid' PID} = {} \<and>
   snd ` (set vl1) \<subseteq> {{uid'. isPC s cid uid' \<and> pref s uid' PID \<noteq> Conflict}}"

definition \<Delta>3 :: "state \<Rightarrow> value list \<Rightarrow> state \<Rightarrow> value list \<Rightarrow> bool" where
"\<Delta>3 s vl s1 vl1 \<equiv>
 \<exists> cid. PID \<in>\<in> paperIDs s cid \<and> phase s cid > revPH \<and> eqExcPID s s1 \<and> vl1 = []"

definition \<Delta>e :: "state \<Rightarrow> value list \<Rightarrow> state \<Rightarrow> value list \<Rightarrow> bool" where
"\<Delta>e s vl s1 vl1 \<equiv>
 vl \<noteq> [] \<and>
 (
  (\<exists> cid. PID \<in>\<in> paperIDs s cid \<and> phase s cid \<ge> revPH \<and>
          \<not> (\<exists> uid. isChair s cid uid \<and> pref s uid PID \<noteq> Conflict))
  \<or>
  (\<exists> cid. PID \<in>\<in> paperIDs s cid \<and> phase s cid \<ge> revPH \<and>
          snd (hd vl) \<noteq> {uid'. isPC s cid uid' \<and> pref s uid' PID \<noteq> Conflict})
  \<or>
  (\<exists> cid. PID \<in>\<in> paperIDs s cid \<and> phase s cid > revPH)
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
  and l: "length vl = length vl1"
  and c_d: "distinct (map fst vl1) \<and> fst ` (set vl1) \<subseteq> snd (hd vl) \<and> snd ` (set vl1) = {snd (hd vl)}"
  and vl: "vl \<noteq> []"
  and PID_ph: "\<And> cid. PID \<in>\<in> paperIDs s cid \<Longrightarrow> phase s cid < revPH"
  using reachNT_reach unfolding \<Delta>1_def B_def by auto
  have rv: "\<And> cid. \<not> (\<exists> uid'. isRev s cid uid' PID)" using rs PID_ph
  by (metis isRev_geq_revPH isRev_paperIDs less_Suc_eq_le not_less_eq_eq)
  show "iaction ?\<Delta> s vl s1 vl1 \<or>
        ((vl = [] \<longrightarrow> vl1 = []) \<and> reaction ?\<Delta> s vl s1 vl1)" (is "?iact \<or> (_ \<and> ?react)")
  proof-
    have ?react proof
      fix a :: act and ou :: out and s' :: state and vl'
      let ?trn = "Trans s a ou s'"  let ?trn1 = "Trans s1 a ou s'"
      assume step: "step s a = (ou, s')" and T: "\<not> T ?trn" and c: "consume ?trn vl vl'"
      have \<phi>: "\<not> \<phi> ?trn"
        apply(cases a)
        subgoal for x1 apply(cases x1) using step PID_ph by (fastforce simp: c_defs)+
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
            hence "\<Delta>1 s' vl' s' vl1" unfolding \<Delta>1_def B_def vl' using PID_ph' c_d vl l by auto
            thus ?thesis by auto
          next
            case True
            then obtain CID where PID: "PID \<in>\<in> paperIDs s CID" by auto
            hence ph: "phase s CID < revPH" using PID_ph by auto
            have PID': "PID \<in>\<in> paperIDs s' CID" by (metis PID paperIDs_mono step)
            show ?thesis
            proof(cases "phase s' CID < revPH")
              case True note ph' = True
              hence "\<Delta>1 s' vl' s' vl1" unfolding \<Delta>1_def B_def vl' using vl c_d ph' PID' l apply auto
              by (metis reach_PairI paperIDs_equals rs step)
              thus ?thesis by auto
            next
              case False
              hence ph_rv': "phase s' CID = revPH \<and> \<not> (\<exists> uid'. isRev s' CID uid' PID)"
              using ph PID step rs rv
              apply(cases a)
                subgoal for x1 apply(cases x1) apply(fastforce simp: c_defs)+ .
                subgoal for x2 apply(cases x2) apply(fastforce simp: u_defs isRev_def2)+ .
                subgoal for x3 apply(cases x3) apply(fastforce simp: uu_defs)+ .
                by auto
              show ?thesis
              proof(cases "(\<exists> uid. isChair s' CID uid \<and> pref s' uid PID \<noteq> Conflict) \<and>
                           snd (hd vl) = {uid'. isPC s' CID uid' \<and> pref s' uid' PID \<noteq> Conflict}")
                case True
                hence "\<Delta>2 s' vl' s' vl1"
                unfolding \<Delta>2_def B_def vl' using c_d ph_rv' PID' l by auto
                thus ?thesis by auto
              next
                case False
                hence "\<Delta>e s' vl' s' vl1"
                unfolding \<Delta>e_def vl' using vl c_d ph_rv' PID' l by auto
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

lemma not_\<phi>_isRev_isPC_persists:
assumes "reach s"
"PID \<in>\<in> paperIDs s cid" and "\<not> \<phi> (Trans s a ou s')"
and "step s a = (ou,s')"
shows "isRev s' cid uid PID  = isRev s cid uid PID \<and> isPC s' cid uid = isPC s cid uid"
  using assms apply(cases a)
  subgoal for x1 apply(cases x1) apply(auto simp: c_defs isRev_def2 roles_confIDs paperIDs_confIDs)
    apply (metis Suc_n_not_le_n paperIDs_geq_subPH)+ .
  subgoal for x2 apply(cases x2,auto simp: u_defs isRev_def2) .
  subgoal for x3 apply(cases x3,auto simp: uu_defs isRev_def2) .
  by auto

lemma \<gamma>_not\<chi>_eqButPID_outErr:
assumes sT: "reachNT s" and s1: "reach s1"
and UIDs: "userOfA a \<in> UIDs" and step: "step s a = (outErr,s')" (* and \<chi>: "\<not> \<chi> a" *)
and ss1: "eqExcPID s s1" and PID: "PID \<in>\<in> paperIDs s CID"
shows "step s1 a = (outErr,s1)"
proof-
  have s: "reach s" by (metis reachNT_reach sT)
  have step: "step s a = (outErr,s)" using step by (metis step_outErr_eq)
  note Inv = reachNT_non_isPC_isChair[OF sT UIDs]
  note eqs = eqExcPID_imp[OF ss1]
  note eqs' = eqExcPID_imp1[OF ss1]
  have PID1: "PID \<in>\<in> paperIDs s1 CID" using ss1 PID unfolding eqExcPID_def by auto

  note simps[simp] = c_defs u_defs uu_defs r_defs l_defs Paper_dest_conv eqExcPID_def
  note simps2[simp] = eqExcRLR_imp[of s _ _ _ s1, OF s]
      eqExcRLR_imp2[of s _ _ s1]
      eqExcRLR_set[of "(roles s cid uid)" "(roles s1 cid uid)" for cid uid]
      foo2 foo3
      eqExcRLR_imp_isRevRole_imp

  note * = step eqs eqs' s s1 UIDs (* \<chi> *) PID PID1 paperIDs_equals[OF s] Inv

  show ?thesis
  proof (cases a)
    case (Cact x1)
    with * show ?thesis
      by (cases x1; auto; metis less_irrefl_nat simps2(1))
  next
    case (Uact x2)
    with * show ?thesis
      by (cases x2; auto; metis isRev_pref_notConflict_isPC less_irrefl_nat simps2(1))
  next
    case (UUact x3)
    with * show ?thesis
      by (cases x3; auto; metis eqs isRev_isPC less_Suc_eq less_irrefl_nat pref_Conflict_isRev simps2(1))
  next
    case (Ract x4)
    with * show ?thesis
      by (cases x4; auto; metis isRev_isPC not_less pref_Conflict_isRev s1 simps2(1))
  next
    case (Lact x5)
    with * show ?thesis
      by (cases x5; auto)
  qed
qed

lemma exists_failedAct:
"\<exists> a. step s a = (outErr,s) \<and> userOfA a = uid"
proof-
  obtain p where p: "pass s uid = Password p"
    by (cases "pass s uid")
  let ?a = "Cact (cConf undefined uid (Password (fresh {p} p)) undefined undefined)"
  show ?thesis apply(rule exI[of _ ?a]) using p fresh_notIn[of "{p}" p] by(auto simp: c_defs)
qed

lemma unwind_cont_\<Delta>2: "unwind_cont \<Delta>2 {\<Delta>2,\<Delta>3,\<Delta>e}"
proof(rule, simp)
  let ?\<Delta> = "\<lambda>s vl s1 vl1. \<Delta>2 s vl s1 vl1 \<or> \<Delta>3 s vl s1 vl1 \<or> \<Delta>e s vl s1 vl1"
  fix s s1 :: state and vl vl1 :: "value list"
  assume rsT: "reachNT s" and rs1: "reach s1" and "\<Delta>2 s vl s1 vl1"
  then obtain CID uidc where uidc: "isChair s CID uidc \<and> pref s uidc PID \<noteq> Conflict"
  and rs: "reach s" and ph: "phase s CID = revPH" (is "?ph = _") and ss1: "eqExcPID s s1"
  and PID: "PID \<in>\<in> paperIDs s CID"
  and dis: "distinct (map fst vl1)"
  and l: "length vl = length vl1"
  and fst_isPC: "fst ` (set vl1) \<subseteq> {uid'. isPC s CID uid' \<and> pref s uid' PID \<noteq> Conflict}"
  and fst_isRev: "fst ` (set vl1) \<inter> {uid'. isRev s1 CID uid' PID} = {}"
  and snd_isPC: "snd ` (set vl1) \<subseteq> {{uid'. isPC s CID uid' \<and> pref s uid' PID \<noteq> Conflict}}"
  using reachNT_reach unfolding \<Delta>2_def by auto
  hence uidc_notin: "uidc \<notin> UIDs" using less_not_refl3 reachNT_non_isPC_isChair rsT by fastforce
  note vl1_all = dis fst_isPC fst_isRev snd_isPC
  have PID1: "PID \<in>\<in> paperIDs s1 CID" using PID ss1 unfolding eqExcPID_def by auto
  show "iaction ?\<Delta> s vl s1 vl1 \<or>
        ((vl = [] \<longrightarrow> vl1 = []) \<and> reaction ?\<Delta> s vl s1 vl1)" (is "?iact \<or> (_ \<and> ?react)")
  proof-
    have ?react proof
      fix a :: act and ou :: out and s' :: state and vl'
      let ?trn = "Trans s a ou s'"
      let ?ph' = "phase s' CID"
      assume step: "step s a = (ou, s')" and T: "\<not> T ?trn" and c: "consume ?trn vl vl'"
      have PID': "PID \<in>\<in> paperIDs s' CID" using PID rs by (metis paperIDs_mono step)
      have uidc': "isChair s' CID uidc \<and> pref s' uidc PID \<noteq> Conflict"
      using uidc step rs ph PID isChair_persistent revPH_pref_persists[OF rs PID ] by auto
      show "match ?\<Delta> s s1 vl1 a ou s' vl' \<or> ignore ?\<Delta> s s1 vl1 a ou s' vl'" (is "?match \<or> ?ignore")
      proof(cases "\<phi> ?trn")
        case False note \<phi> = False
        have vl': "vl' = vl" using c \<phi> unfolding consume_def by (cases vl) auto
        obtain ou1 and s1' where step1: "step s1 a = (ou1,s1')" by (metis prod.exhaust)
        let ?trn1 = "Trans s1 a ou1 s1'"
        show ?thesis
        proof(cases "ou = outErr")
          case True note ou = True
          have s': "s' = s" by (metis ou step step_outErr_eq)
          show ?thesis
          proof (cases "userOfA a \<in> UIDs")
            case True note uidUIDs = True
            hence ou1: "ou1 = outErr" using \<gamma>_not\<chi>_eqButPID_outErr
            by (metis PID Pair_inject ou rs1 rsT ss1 step step1)
            hence s1': "s1' = s1" by (metis step1 step_outErr_eq)
            have \<phi>1: "\<not> \<phi> ?trn1" unfolding \<phi>_def2 ou1 by auto
            have ?match proof
              show "validTrans ?trn1" using step1 by simp
            next
              show "consume ?trn1 vl1 vl1" unfolding consume_def using \<phi>1 by auto
            next
              show "\<gamma> ?trn = \<gamma> ?trn1" by simp
            next
              assume "\<gamma> ?trn" thus "g ?trn = g ?trn1" unfolding ou ou1 by simp
            next
              show "?\<Delta> s' vl' s1' vl1" unfolding s' s1' vl' by (metis \<open>\<Delta>2 s vl s1 vl1\<close>)
            qed
            thus ?thesis by simp
          next
            case False note uidUIDs = False
            obtain a1 where ua1: "userOfA a1 = userOfA a" and step1: "step s1 a1 = (outErr,s1)"
            by (metis exists_failedAct ou)
            let ?trn1 = "Trans s1 a1 outErr s1"
            have ?match proof
              show "validTrans ?trn1" using step1 by simp
            next
              show "consume ?trn1 vl1 vl1" unfolding consume_def \<phi>_def2 ou by auto
            next
              show "\<gamma> ?trn = \<gamma> ?trn1" by (simp add: ua1)
            next
              assume "\<gamma> ?trn" thus "g ?trn = g ?trn1" using uidUIDs unfolding ou by simp
            next
              show "?\<Delta> s' vl' s1 vl1" unfolding s' vl' by (metis \<open>\<Delta>2 s vl s1 vl1\<close>)
            qed
            thus ?thesis by simp
          qed
        next
          case False note ou = False
          show ?thesis
          proof(cases "\<chi> a")
            case False note \<chi> = False
            have s's1': "eqExcPID s' s1'" using eqExcPID_step rs rs1 ss1 step step1 PID \<phi> \<chi> ou by blast
            have \<phi>1: "\<not> \<phi> ?trn1" using \<phi> using non_eqExcPID_step_\<phi>_imp rs rs1 ss1 PID step step1 ou by auto
            have out: "userOfA a \<in> UIDs \<longrightarrow> ou1 = ou"
            using eqExcPID_step_out[OF ss1 step step1 rsT rs1 PID _ \<phi> \<phi>1 \<chi>] ph by auto
            have ?match proof
              show "validTrans ?trn1" using step1 by simp
            next
              show "consume ?trn1 vl1 vl1" unfolding consume_def using \<phi>1 by auto
            next
              show "\<gamma> ?trn = \<gamma> ?trn1" unfolding ss1 by simp
            next
              assume "\<gamma> ?trn" thus "g ?trn = g ?trn1" using out by simp
            next
              show "?\<Delta> s' vl' s1' vl1"
              proof(cases "phase s' CID = revPH")
                case True
                hence "\<Delta>2 s' vl' s1' vl1" using uidc' PID' s's1' vl1_all l unfolding \<Delta>2_def vl'
                apply(intro exI[of _ CID] exI[of _ uidc]) apply simp apply(intro conjI)
                using isPC_persistent[OF _ step] revPH_pref_persists[OF rs PID _ step] ph
                not_\<phi>_isRev_isPC_persists[OF rs1 PID1 \<phi>1 step1]
                revPH_pref_persists[OF rs PID _ step] not_\<phi>_isRev_isPC_persists[OF rs PID \<phi> step] ph
                by auto
                thus "?\<Delta> s' vl' s1' vl1" by simp
              next
                case False
                hence ph': "phase s' CID > revPH" using rs step ph by (metis antisym_conv2 phase_increases)
                show ?thesis
                proof(cases "vl = []")
                  case True hence "vl1 = []" using l by simp
                  hence "\<Delta>3 s' vl' s1' vl1" using uidc' PID' s's1' ph' unfolding \<Delta>3_def vl' by auto
                  thus ?thesis by simp
                next
                  case False
                  hence "\<Delta>e s' vl' s1' vl1" using PID' ph' unfolding \<Delta>e_def vl' by auto
                  thus ?thesis by simp
                qed
              qed
            qed
            thus ?thesis by simp
          next
            case True
            thus ?thesis unfolding \<chi>_def2 proof(elim exE disjE)
              fix cid uid p n rc assume a: "a = Uact (uReview cid uid p PID n rc)"
              hence ou: "ou = outOK" using step ou unfolding a by (auto simp: u_defs)
              obtain s1' uid1 p where
              uid1: "isRevNth s1 cid uid1 PID n"
              and step1: "step s1 (Uact (uReview cid uid1 p PID n rc)) = (outOK,s1')" (is "step _ ?a1 = _")
              and s's1': "eqExcPID s' s1'" using eqExcPID_step_\<chi>1 rs rs1 a ss1 step ou by metis
              let ?trn1 = "Trans s1 ?a1 outOK s1'"
              have \<phi>1: "\<not> \<phi> ?trn1" by simp
              have "isPC s cid uid \<and> pref s uid PID \<noteq> Conflict"
              using step unfolding a ou apply(auto simp: u_defs)
              by (metis isRev_pref_notConflict_isPC rs)+
              hence uidUIDs: "\<not> uid \<in> UIDs" using ph reachNT_non_isPC_isChair[OF rsT] apply auto
              by (metis PID PID1 isRevNth_paperIDs less_irrefl_nat paperIDs_equals rs1 uid1)
              have "isPC s1 cid uid1 \<and> pref s1 uid1 PID \<noteq> Conflict" using step1  apply(auto simp: u_defs)
              by (metis isRev_pref_notConflict_isPC rs1)+
              hence "isPC s cid uid1 \<and> pref s uid1 PID \<noteq> Conflict" using ss1 unfolding eqExcPID_def
              using eqExcRLR_imp2 by fastforce
              hence uid1UIDs: "\<not> uid1 \<in> UIDs" using ph reachNT_non_isPC_isChair[OF rsT] apply auto
              by (metis (no_types, opaque_lifting) eqExcPID_def isRevNth_geq_revPH isRevNth_paperIDs not_le rs1 ss1 uid1)
              have ph': "phase s' CID = revPH" using ph step unfolding a by (auto simp: u_defs)
              have ?match proof
                show "validTrans ?trn1" using step1 by simp
              next
                show "consume ?trn1 vl1 vl1" unfolding consume_def using \<phi>1 by auto
              next
                show "\<gamma> ?trn = \<gamma> ?trn1" using uidUIDs uid1UIDs unfolding a by simp
              next
                assume "\<gamma> ?trn" thus "g ?trn = g ?trn1" using uidUIDs unfolding a by simp
              next
                have "\<Delta>2 s' vl' s1' vl1" using ph' PID' s's1' unfolding \<Delta>2_def vl'
                apply(intro exI[of _ CID] exI[of _ uidc]) using l vl1_all
                using isPC_persistent[OF _ step] revPH_pref_persists[OF rs PID _ step] ph
                not_\<phi>_isRev_isPC_persists[OF rs1 PID1 \<phi>1 step1]
                revPH_pref_persists[OF rs PID _ step] not_\<phi>_isRev_isPC_persists[OF rs PID \<phi> step] ph uidc'
                by auto
                thus "?\<Delta> s' vl' s1' vl1" by simp
              qed
              thus ?thesis by simp
            next
              fix cid uid p n rc assume a: "a = UUact (uuReview cid uid p PID n rc)"
              hence ou: "ou = outOK" using step ou unfolding a by (auto simp: uu_defs)
              obtain s1' uid1 p where
              uid1: "isRevNth s1 cid uid1 PID n"
              and step1: "step s1 (UUact (uuReview cid uid1 p PID n rc)) = (outOK,s1')" (is "step _ ?a1 = _")
              and s's1': "eqExcPID s' s1'" using eqExcPID_step_\<chi>2 rs rs1 a ss1 step ou by metis
              let ?trn1 = "Trans s1 ?a1 outOK s1'"
              have \<phi>1: "\<not> \<phi> ?trn1" by simp
              have "isPC s cid uid \<and> pref s uid PID \<noteq> Conflict"
              using step unfolding a ou apply(auto simp: uu_defs)
              by (metis isRev_pref_notConflict_isPC rs)+
              hence uidUIDs: "\<not> uid \<in> UIDs" using ph reachNT_non_isPC_isChair[OF rsT] apply auto
              by (metis (no_types, opaque_lifting) eqExcPID_def isRevNth_geq_revPH isRevNth_paperIDs not_le rs1 ss1 uid1)
              have "isPC s1 cid uid1 \<and> pref s1 uid1 PID \<noteq> Conflict" using step1  apply(auto simp: uu_defs)
              by (metis isRev_pref_notConflict_isPC rs1)+
              hence "isPC s cid uid1 \<and> pref s uid1 PID \<noteq> Conflict" using ss1 unfolding eqExcPID_def
              using eqExcRLR_imp2 by fastforce
              hence uid1UIDs: "\<not> uid1 \<in> UIDs" using ph reachNT_non_isPC_isChair[OF rsT] apply auto
              by (metis (no_types, opaque_lifting) eqExcPID_def isRevNth_geq_revPH isRevNth_paperIDs not_le rs1 ss1 uid1)
              have ph': "phase s' CID = revPH" using ph step unfolding a by (auto simp: uu_defs)
              have ?match proof
                show "validTrans ?trn1" using step1 by simp
              next
                show "consume ?trn1 vl1 vl1" unfolding consume_def using \<phi>1 by auto
              next
                show "\<gamma> ?trn = \<gamma> ?trn1" using uidUIDs uid1UIDs unfolding a by simp
              next
                assume "\<gamma> ?trn" thus "g ?trn = g ?trn1" using uidUIDs unfolding a by simp
              next
                have "\<Delta>2 s' vl' s1' vl1" using ph' PID' s's1' unfolding \<Delta>2_def vl'
                apply(intro exI[of _ CID] exI[of _ uidc]) using l vl1_all
                using isPC_persistent[OF _ step] revPH_pref_persists[OF rs PID _ step] ph
                not_\<phi>_isRev_isPC_persists[OF rs1 PID1 \<phi>1 step1]
                revPH_pref_persists[OF rs PID _ step] not_\<phi>_isRev_isPC_persists[OF rs PID \<phi> step] ph uidc'
                by auto
                thus "?\<Delta> s' vl' s1' vl1" by simp
              qed
              thus ?thesis by simp
            qed
          qed
        qed
      next
        case True note \<phi> = True
        then obtain cid uid p uid' where  a: "a = Cact (cReview cid uid p PID uid')"
        (* have ua: "userOfA a \<notin> UIDs" by (metis \<phi> T_\<phi>_\<gamma> \<gamma>.simps rsT step) *)
        and ou: "ou = outOK" unfolding \<phi>_def2 by auto
        have cid: "cid = CID" using step unfolding a ou apply(auto simp: c_defs)
        by (metis PID paperIDs_equals rs)
        obtain v vll' where "vl = v # vll'" using \<phi> c unfolding consume_def by (cases vl) auto
        hence vl: "vl = v # vl'" by (metis \<phi> c consume_def list.sel(2-3))
        obtain v1 vl1' where vl1: "vl1 = v1 # vl1'" using l vl by (cases vl1) auto
        obtain uid1' where v1: "v1 = (uid1', {uid1'. isPC s CID uid1' \<and> pref s uid1' PID \<noteq> Conflict})"
        using snd_isPC unfolding vl1 by(cases v1) auto
        hence uid1': "isPC s CID uid1' \<and> pref s uid1' PID \<noteq> Conflict" and uid1'1: "\<not> isRev s1 CID uid1' PID"
        using fst_isPC fst_isRev unfolding vl1 by auto
        have uid: "isChair s CID uid \<and> pref s uid PID \<noteq> Conflict"
        using step unfolding a ou cid by (auto simp: c_defs)
        have uid1: "isChair s1 CID uid \<and> pref s1 uid PID \<noteq> Conflict"
        using ss1 uid unfolding eqExcPID_def using eqExcRLR_imp2 by metis
        have uuid1': "isPC s1 CID uid1' \<and> pref s1 uid1' PID \<noteq> Conflict"
        using uid1' ss1 unfolding eqExcPID_def apply auto by (metis eqExcRLR_imp2)
        obtain a1 where a1: "a1 = Cact (cReview CID uid p PID uid1')" by blast
        obtain s1' ou1 where step1: "step s1 a1 = (ou1,s1')" by (metis prod.exhaust)
        have ph1: "phase s1 CID = revPH" using ss1 ph unfolding eqExcPID_def by auto
        let ?trn1 = "Trans s1 a1 ou1 s1'"
        have s's1': "eqExcPID s' s1'" and ou1: "ou1 = outOK"
        using eqExcPID_step_\<phi>_eqExcPID_out[OF rs rs1 a[unfolded cid]
                                              a1 ss1 step[unfolded ou] uid1' uid1'1 step1] by auto
        hence many_s1': "PID \<in>\<in> paperIDs s1' CID" "isChair s1' CID uid \<and> pref s1' uid PID \<noteq> Conflict"
        "phase s1' CID = revPH" "pass s1' uid = pass s1 uid"
        "isPC s1' CID uid1' \<and> pref s1' uid1' PID \<noteq> Conflict"
          subgoal by (metis PID1 paperIDs_mono step1)
          subgoal by (metis (no_types, lifting) PID1 Suc_leI eqExcPID_def isChair_persistent lessI ph revPH_pref_persists rs1 ss1 step1 uid1)
          subgoal using step1 ph1 unfolding a1 by (fastforce simp: c_defs)
          subgoal using step1 ph1 unfolding a1 by (fastforce simp: c_defs)
          subgoal by (metis (no_types, lifting) PID1 Suc_leI eqExcPID_def isPC_persistent lessI ph revPH_pref_persists rs1 ss1 step1 uuid1')
          done
        hence more_s1': "uid \<in>\<in> userIDs s1'" "CID \<in>\<in> confIDs s1'"
        by (metis paperIDs_confIDs reach_PairI roles_userIDs rs1 step1 many_s1'(1))+
        have \<phi>1: "\<phi> ?trn1" unfolding a1 ou1 \<phi>_def2 by auto
        have f1: "f ?trn1 = v1" unfolding a1 v1 apply simp
        using ss1 unfolding eqExcPID_def using eqExcRLR_imp2
        by (metis eqExcRLR_set isRevRoleFor.simps(3))
        have rs1': "reach s1'" using rs1 step1 by (auto intro: reach_PairI)
        have ph': "phase s' CID = revPH" using step ph unfolding a by(auto simp: c_defs)
        have ?match proof
          show "validTrans ?trn1" using step1 by simp
          next
            show "consume ?trn1 vl1 vl1'" unfolding consume_def vl1 using \<phi>1 f1 by auto
          next
            show "\<gamma> ?trn = \<gamma> ?trn1" unfolding a a1 by simp
          next
            assume "\<gamma> ?trn" thus "g ?trn = g ?trn1" by (metis \<phi> T_\<phi>_\<gamma> \<gamma>.simps rsT step)
          next
            have 0: "{uid'. isPC s' CID uid' \<and> pref s' uid' PID \<noteq> Conflict} =
                     {uid'. isPC s CID uid' \<and> pref s uid' PID \<noteq> Conflict}"
            using step rs ph unfolding a ou by (auto simp: c_defs)
            have 1: "{uid'. isRev s1' CID uid' PID} \<subseteq> {uid'. isRev s1 CID uid' PID} \<union> {uid1'}"
            using step1 unfolding a1 ou1 by (auto simp: c_defs isRev_def2)
            have 2: "fst ` set vl1' \<subseteq> fst ` set vl1 - {uid1'}" using dis
            unfolding vl1 apply simp unfolding image_set unfolding v1 by simp
            have 3: "fst ` set vl1' \<inter> {uid'. isRev s1' CID uid' PID} = {}"
            using 1 2 vl1_all(3) by blast
            have "\<Delta>2 s' vl' s1' vl1'" unfolding \<Delta>2_def
            apply(intro exI[of _ CID] exI[of _ uidc]) using l vl1_all unfolding vl1 vl apply simp
            using PID' ph' uidc' s's1' apply simp
            unfolding 0 using 3 by simp
            thus "?\<Delta> s' vl' s1' vl1'" by simp
        qed
        thus ?thesis by simp
      qed
    qed
    thus ?thesis using l by (metis length_0_conv)
  qed
qed

lemma unwind_cont_\<Delta>3: "unwind_cont \<Delta>3 {\<Delta>3,\<Delta>e}"
proof(rule, simp)
  let ?\<Delta> = "\<lambda>s vl s1 vl1. \<Delta>3 s vl s1 vl1 \<or> \<Delta>e s vl s1 vl1"
  fix s s1 :: state and vl vl1 :: "value list"
  assume rsT: "reachNT s" and rs1: "reach s1" and "\<Delta>3 s vl s1 vl1"
  then obtain CID where rs: "reach s" and ph: "phase s CID > revPH" (is "?ph > _")
  and PID: "PID \<in>\<in> paperIDs s CID" and ss1: "eqExcPID s s1"
  and vl1: "vl1 = []"
  using reachNT_reach unfolding \<Delta>3_def by auto
  have PID1: "PID \<in>\<in> paperIDs s1 CID"
  by (metis PID eqExcPID_sym isAut_paperIDs notInPaperIDs_eqExcPID_roles_eq paperID_ex_userID rs rs1 ss1)
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
      have ph': "phase s' CID > revPH" using ph rs
      by (meson less_le_trans local.step phase_increases)
      have \<phi>: "\<not> \<phi> ?trn" using step ph unfolding \<phi>_def2 apply(auto simp: c_defs)
      using PID paperIDs_equals rs by force
      have vl': "vl' = vl" using c \<phi> unfolding consume_def by (cases vl) auto
      show "match ?\<Delta> s s1 vl1 a ou s' vl' \<or> ignore ?\<Delta> s s1 vl1 a ou s' vl'" (is "?match \<or> ?ignore")
      proof(cases "\<chi> a")
        case True
        thus ?thesis unfolding \<chi>_def2 proof(elim exE disjE)
          fix cid uid p n rc assume a: "a = Uact (uReview cid uid p PID n rc)"
          show ?thesis
          proof(cases "ou = outErr")
             case True note ou = True
             hence s's: "s' = s" by (metis step step_outErr_eq)
             show ?thesis proof(cases "uid \<in> UIDs")
               case True note uidUIDs = True
               obtain ou1 and s1' where step1: "step s1 a = (ou1,s1')" by (metis prod.exhaust)
               let ?trn1 = "Trans s1 a ou1 s1'"
               have "isPC s CID uid \<longrightarrow> pref s uid PID = Conflict"
               using reachNT_non_isPC_isChair[OF rsT uidUIDs] ph PID by force
               hence 1: "isPC s1 CID uid \<longrightarrow> pref s1 uid PID = Conflict" using ss1 unfolding eqExcPID_def
               using eqExcRLR_imp2 by fastforce
               have ou1: "ou1 = outErr" using step1 uidUIDs unfolding a apply(auto simp: u_defs)
               apply(cases "cid = CID", auto)
               apply (metis 1 isRev_isPC isRev_pref_notConflict rs1)
               by (metis rs1 PID1 paperIDs_equals)
               have s1's1: "s1' = s1" by (metis ou ou1 step step1 step_outErr_eq)
               have \<phi>1: "\<not> \<phi> ?trn1" using \<phi> unfolding eqExcPID_step_\<phi>[OF rs rs1 ss1 PID ph step step1] .
               have ?match proof
                 show "validTrans ?trn1" using step1 by simp
               next
                 show "consume ?trn1 vl1 vl1" unfolding consume_def using \<phi>1 by auto
               next
                 show "\<gamma> ?trn = \<gamma> ?trn1" unfolding ss1 by simp
               next
                 assume "\<gamma> ?trn" thus "g ?trn = g ?trn1" unfolding ou ou1 by simp
               next
                 have "\<Delta>3 s' vl' s1' vl1" using ph' PID' ss1 unfolding \<Delta>3_def s's s1's1 vl1 by auto
                 thus "?\<Delta> s' vl' s1' vl1" by simp
               qed
               thus ?thesis by simp
             next
               case False note uidUIDs = False
               have ?ignore proof
                 show "\<not> \<gamma> ?trn" using uidUIDs unfolding a by auto
               next
                 have "\<Delta>3 s' vl' s1 vl1" using ph' PID' ss1 unfolding \<Delta>3_def s's vl1 by auto
                 thus "?\<Delta> s' vl' s1 vl1" by simp
               qed
               thus ?thesis by simp
             qed
          next
             case False hence ou: "ou = outOK" using step unfolding a by (auto simp: u_defs)
             obtain s1' uid1 p where
             uid1: "isRevNth s1 cid uid1 PID n"
             and step1: "step s1 (Uact (uReview cid uid1 p PID n rc)) = (outOK,s1')" (is "step _ ?a1 = _")
             and s's1': "eqExcPID s' s1'" using eqExcPID_step_\<chi>1 rs rs1 a ss1 step ou by metis
             let ?trn1 = "Trans s1 ?a1 outOK s1'"
             have \<phi>1: "\<not> \<phi> ?trn1" by simp
             have "isPC s cid uid \<and> pref s uid PID \<noteq> Conflict" using step unfolding a ou apply(auto simp: u_defs)
             by (metis isRev_pref_notConflict_isPC rs)+
             hence uidUIDs: "\<not> uid \<in> UIDs" using ph reachNT_non_isPC_isChair[OF rsT] apply auto
             by (metis (no_types, opaque_lifting) eqExcPID_def isRevNth_geq_revPH isRevNth_paperIDs not_le rs1 ss1 uid1)
             have "isPC s1 cid uid1 \<and> pref s1 uid1 PID \<noteq> Conflict" using step1  apply(auto simp: u_defs)
             by (metis isRev_pref_notConflict_isPC rs1)+
             hence "isPC s cid uid1 \<and> pref s uid1 PID \<noteq> Conflict" using ss1 unfolding eqExcPID_def
             using eqExcRLR_imp2 by fastforce
             hence uid1UIDs: "\<not> uid1 \<in> UIDs" using ph reachNT_non_isPC_isChair[OF rsT] apply auto
             by (metis (no_types, opaque_lifting) eqExcPID_def isRevNth_geq_revPH isRevNth_paperIDs not_le rs1 ss1 uid1)
             have ?match proof
               show "validTrans ?trn1" using step1 by simp
             next
               show "consume ?trn1 vl1 vl1" unfolding consume_def using \<phi>1 by auto
             next
               show "\<gamma> ?trn = \<gamma> ?trn1" using uidUIDs uid1UIDs unfolding a by simp
             next
               assume "\<gamma> ?trn" thus "g ?trn = g ?trn1" using uidUIDs unfolding a by simp
             next
               have "\<Delta>3 s' vl' s1' vl1" using ph' PID' s's1' unfolding \<Delta>3_def vl1 by auto
               thus "?\<Delta> s' vl' s1' vl1" by simp
             qed
             thus ?thesis by simp
          qed
        next
          fix cid uid p n rc assume a: "a = UUact (uuReview cid uid p PID n rc)"
           show ?thesis
          proof(cases "ou = outErr")
             case True note ou = True
             hence s's: "s' = s" by (metis step step_outErr_eq)
             show ?thesis proof(cases "uid \<in> UIDs")
               case True note uidUIDs = True
               obtain ou1 and s1' where step1: "step s1 a = (ou1,s1')" by (metis prod.exhaust)
               let ?trn1 = "Trans s1 a ou1 s1'"
               have "isPC s CID uid \<longrightarrow> pref s uid PID = Conflict"
               using reachNT_non_isPC_isChair[OF rsT uidUIDs] ph PID by force
               hence 1: "isPC s1 CID uid \<longrightarrow> pref s1 uid PID = Conflict" using ss1 unfolding eqExcPID_def
               using eqExcRLR_imp2 by fastforce
               have ou1: "ou1 = outErr" using step1 uidUIDs unfolding a apply(auto simp: uu_defs)
               apply(cases "cid = CID", auto)
               apply (metis 1 isRev_isPC isRev_pref_notConflict rs1)
               by (metis rs1 PID1 paperIDs_equals)
               have s1's1: "s1' = s1" by (metis ou ou1 step step1 step_outErr_eq)
               have \<phi>1: "\<not> \<phi> ?trn1" using \<phi> unfolding eqExcPID_step_\<phi>[OF rs rs1 ss1 PID ph step step1] .
               have ?match proof
                 show "validTrans ?trn1" using step1 by simp
               next
                 show "consume ?trn1 vl1 vl1" unfolding consume_def using \<phi>1 by auto
               next
                 show "\<gamma> ?trn = \<gamma> ?trn1" unfolding ss1 by simp
               next
                 assume "\<gamma> ?trn" thus "g ?trn = g ?trn1" unfolding ou ou1 by simp
               next
                 have "\<Delta>3 s' vl' s1' vl1" using ph' PID' ss1 unfolding \<Delta>3_def s's s1's1 vl1 by auto
                 thus "?\<Delta> s' vl' s1' vl1" by simp
               qed
               thus ?thesis by simp
             next
               case False note uidUIDs = False
               have ?ignore proof
                 show "\<not> \<gamma> ?trn" using uidUIDs unfolding a by auto
               next
                 have "\<Delta>3 s' vl' s1 vl1" using ph' PID' ss1 unfolding \<Delta>3_def s's vl1 by auto
                 thus "?\<Delta> s' vl' s1 vl1" by simp
               qed
               thus ?thesis by simp
             qed
          next
             case False hence ou: "ou = outOK" using step unfolding a by (auto simp: u_defs)
             obtain s1' uid1 p where
             uid1: "isRevNth s1 cid uid1 PID n"
             and step1: "step s1 (UUact (uuReview cid uid1 p PID n rc)) = (outOK,s1')" (is "step _ ?a1 = _")
             and s's1': "eqExcPID s' s1'" using eqExcPID_step_\<chi>2 rs rs1 a ss1 step ou by metis
             let ?trn1 = "Trans s1 ?a1 outOK s1'"
             have \<phi>1: "\<not> \<phi> ?trn1" by simp
             have "isPC s cid uid \<and> pref s uid PID \<noteq> Conflict" using step unfolding a ou apply(auto simp: uu_defs)
             by (metis isRev_pref_notConflict_isPC rs)+
             hence uidUIDs: "\<not> uid \<in> UIDs" using ph reachNT_non_isPC_isChair[OF rsT] apply auto
             by (metis (no_types, opaque_lifting) eqExcPID_def isRevNth_geq_revPH isRevNth_paperIDs not_le rs1 ss1 uid1)
             have "isPC s1 cid uid1 \<and> pref s1 uid1 PID \<noteq> Conflict" using step1  apply(auto simp: uu_defs)
             by (metis isRev_pref_notConflict_isPC rs1)+
             hence "isPC s cid uid1 \<and> pref s uid1 PID \<noteq> Conflict" using ss1 unfolding eqExcPID_def
             using eqExcRLR_imp2 by fastforce
             hence uid1UIDs: "\<not> uid1 \<in> UIDs" using ph reachNT_non_isPC_isChair[OF rsT] apply auto
             by (metis (no_types, opaque_lifting) eqExcPID_def isRevNth_geq_revPH isRevNth_paperIDs not_le rs1 ss1 uid1)
             have ?match proof
               show "validTrans ?trn1" using step1 by simp
             next
               show "consume ?trn1 vl1 vl1" unfolding consume_def using \<phi>1 by auto
             next
               show "\<gamma> ?trn = \<gamma> ?trn1" using uidUIDs uid1UIDs unfolding a by simp
             next
               assume "\<gamma> ?trn" thus "g ?trn = g ?trn1" using uidUIDs unfolding a by simp
             next
               have "\<Delta>3 s' vl' s1' vl1" using ph' PID' s's1' unfolding \<Delta>3_def vl1 by auto
               thus "?\<Delta> s' vl' s1' vl1" by simp
             qed
             thus ?thesis by simp
          qed
        qed
      next
        case False note \<chi> = False
        obtain ou1 and s1' where step1: "step s1 a = (ou1,s1')" by (metis prod.exhaust)
        let ?trn1 = "Trans s1 a ou1 s1'"
        have \<phi>1: "\<not> \<phi> ?trn1" using \<phi> unfolding eqExcPID_step_\<phi>[OF rs rs1 ss1 PID ph step step1] .
        have out: "userOfA a \<in> UIDs \<longrightarrow> ou1 = ou"
        using eqExcPID_step_out[OF ss1 step step1 rsT rs1 PID _ \<phi> \<phi>1 \<chi>] ph by auto
        have s's1': "eqExcPID s' s1'" using eqExcPID_step rs rs1 ss1 step step1 PID ph \<phi> \<chi> by blast
        have ?match proof
          show "validTrans ?trn1" using step1 by simp
        next
          show "consume ?trn1 vl1 vl1" unfolding consume_def using \<phi>1 by auto
        next
          show "\<gamma> ?trn = \<gamma> ?trn1" unfolding ss1 by simp
        next
          assume "\<gamma> ?trn" thus "g ?trn = g ?trn1" using out by simp
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
"K1exit cid s \<equiv> PID \<in>\<in> paperIDs s cid \<and> phase s cid \<ge> revPH \<and>
                \<not> (\<exists> uid. isChair s cid uid \<and> pref s uid PID \<noteq> Conflict)"

lemma invarNT_K1exit: "invarNT (K1exit cid)"
unfolding invarNT_def apply (safe dest!: reachNT_reach)
  subgoal for _ a apply(cases a)
    subgoal for x1 apply(cases x1) apply (fastforce simp add: c_defs K1exit_def geq_noPH_confIDs)+ .
    subgoal for x2 apply(cases x2) apply (auto simp add: u_defs K1exit_def paperIDs_equals)
      apply (metis less_eq_Suc_le less_not_refl paperIDs_equals) .
    subgoal for x3 apply(cases x3) apply (auto simp add: uu_defs K1exit_def) .
    by auto
  done

lemma noVal_K1exit: "noVal (K1exit cid) v"
  apply(rule no\<phi>_noVal)
  unfolding no\<phi>_def apply safe
  subgoal for _ a apply(cases a)
    subgoal for x1 apply(cases x1)
      apply (auto simp add: c_defs K1exit_def)
      by (metis paperIDs_equals reachNT_reach)
    by auto
  done

definition K2exit where
"K2exit cid s v \<equiv>
 PID \<in>\<in> paperIDs s cid \<and> phase s cid \<ge> revPH \<and>
 snd v \<noteq> {uid'. isPC s cid uid' \<and> pref s uid' PID \<noteq> Conflict}"

lemma revPH_isPC_constant:
assumes s: "reach s"
and "step s a = (ou,s')"
and "pid \<in>\<in> paperIDs s cid" and "phase s cid \<ge> revPH"
shows "isPC s' cid uid' = isPC s cid uid'"
using assms apply(cases a)
  subgoal for x1 apply(cases x1) apply (auto simp add: c_defs)
    apply (metis paperIDs_confIDs) .
  subgoal for x2 apply(cases x2) apply (auto simp add: u_defs) .
  subgoal for x3 apply(cases x3) apply (auto simp add: uu_defs) .
  by auto

lemma revPH_pref_constant:
assumes s: "reach s"
and "step s a = (ou,s')"
and "pid \<in>\<in> paperIDs s cid" and "phase s cid \<ge> revPH"
shows "pref s' uid pid = pref s uid pid"
using assms apply(cases a)
  subgoal for x1 apply(cases x1) apply (auto simp add: c_defs)
    apply (metis paperIDs_getAllPaperIDs)
    apply (metis Suc_n_not_le_n le_SucI paperIDs_equals)
    apply (metis Suc_n_not_le_n le_SucI paperIDs_equals) .
  subgoal for x2 apply(cases x2) apply (auto simp add: u_defs)
    apply (metis Suc_n_not_le_n paperIDs_equals) .
  subgoal for x3 apply(cases x3) apply (auto simp add: uu_defs) .
  by auto

lemma invarNT_K2exit: "invarNT (\<lambda> s. K2exit cid s v)"
unfolding invarNT_def apply (safe dest!: reachNT_reach)
unfolding K2exit_def
by (smt Collect_cong le_trans paperIDs_mono phase_increases revPH_isPC_constant revPH_pref_constant)


(* An even more interesting invariant than the one in Review_Confidentiality/RAut:
it requires the binary version noVal2  *)
lemma noVal_K2exit: "noVal2 (K2exit cid) v"
unfolding noVal2_def apply safe
  subgoal for _ a apply(cases a)
    subgoal for x1 apply(cases x1)
             apply (auto simp add: c_defs K2exit_def)
       apply (metis paperIDs_equals reachNT_reach)+ .
    by auto
  done

definition K3exit where
"K3exit cid s \<equiv> PID \<in>\<in> paperIDs s cid \<and> phase s cid > revPH"

lemma invarNT_K3exit: "invarNT (K3exit cid)"
unfolding invarNT_def apply (safe dest!: reachNT_reach)
  subgoal for _ a apply(cases a)
    subgoal for x1 apply(cases x1) apply (auto simp add: c_defs K3exit_def) .
    subgoal for x2 apply(cases x2) apply (auto simp add: u_defs K3exit_def) .
    subgoal for x3 apply(cases x3) apply (auto simp add: uu_defs K3exit_def) .
    by auto
  done

lemma noVal_K3exit: "noVal (K3exit cid) v"
apply(rule no\<phi>_noVal)
unfolding no\<phi>_def apply safe
  subgoal for _ a apply(cases a)
    subgoal for x1 apply(cases x1)
             apply (auto simp add: c_defs K3exit_def)
      using reachNT_reach paperIDs_equals by fastforce
    by auto
  done

lemma unwind_exit_\<Delta>e: "unwind_exit \<Delta>e"
proof
  fix s s1 :: state and vl vl1 :: "value list"
  assume rsT: "reachNT s" and rs1: "reach s1" and \<Delta>e: "\<Delta>e s vl s1 vl1"
  hence vl: "vl \<noteq> []" using reachNT_reach unfolding \<Delta>e_def by auto
  then obtain CID where "K1exit CID s \<or> K2exit CID s (hd vl) \<or> K3exit CID s"
  using \<Delta>e unfolding K1exit_def K2exit_def K3exit_def \<Delta>e_def by auto
  thus "vl \<noteq> [] \<and> exit s (hd vl)" apply(simp add: vl)
  by (metis exitI2 exitI2_noVal2 invarNT_K1exit invarNT_K2exit invarNT_K3exit
            noVal_K1exit noVal_K2exit noVal_K3exit rsT)
qed

theorem secure: secure
apply(rule unwind_decomp3_secure[of \<Delta>1 \<Delta>2 \<Delta>e \<Delta>3])
using
istate_\<Delta>1
unwind_cont_\<Delta>1 unwind_cont_\<Delta>2 unwind_cont_\<Delta>3
unwind_exit_\<Delta>e
by auto

end
