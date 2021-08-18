theory Reviewer_Assignment_NCPC_Aut
imports "../Observation_Setup" Reviewer_Assignment_Value_Setup "Bounded_Deducibility_Security.Compositional_Reasoning"
begin

subsection \<open>Confidentiality protection from users who are not PC members
or authors of the paper\<close>

text \<open>We verify the following property:

\ \\
A group of users UIDs learn
nothing about the reviewers assigned to a paper PID
except for the fact that they are PC members having no conflict with that paper
unless/until one of the following occurs:
\begin{itemize}
\item the user becomes a PC member in the paper's conference having no conflict
     with that paper and the conference moves to the reviewing phase,
or
\item the user becomes an author of the paper
   and the conference moves to the notification phase.
\end{itemize}
\<close>

fun T :: "(state,act,out) trans \<Rightarrow> bool" where
"T (Trans _ _ ou s') =
 (\<exists> uid \<in> UIDs.
    (\<exists> cid. PID \<in>\<in> paperIDs s' cid \<and> isPC s' cid uid \<and> pref s' uid PID \<noteq> Conflict \<and> phase s' cid \<ge> revPH)
    \<or>
    (\<exists> cid. PID \<in>\<in> paperIDs s' cid \<and> isAut s' cid uid PID \<and> phase s' cid \<ge> notifPH)
 )"


declare T.simps [simp del]

(*
The bound says that a sequence of values vl,
i.e., a sequence of pairs [(uid_1,Uids_1),...,(uid_n,Uids_n)]
representing the users uid_i appointed as reviewers and the set
of PC members Uids_i not having conflict with paper ID at the time,
cannot be distinguished from a sequence of values
vl' = [(uid'_1,Uids'_1),...,(uid'_m,Uids'_m)] provided that
-- uid'_1,...,uid'_m are all distinct
-- Uids'_1 are all equal, and they are all equal to U
-- uid'_1 is in U

where U = Uids_1. Note actually that, because in the Reviewing phase
conflicts can no longer be changed, we actually have
U = Uids_1 = ... = Uids_n, which explains the above bound.

Thus, the second component of values (which turns out be constant)
is only collected in order to be able to express the following piece of information:
"the appointed reviewers are PC members having no conflict with paper".
*)

definition B :: "value list \<Rightarrow> value list \<Rightarrow> bool" where
"B vl vl1 \<equiv>
 vl \<noteq> [] \<and>
 distinct (map fst vl1) \<and> fst ` (set vl1) \<subseteq> snd (hd vl) \<and> snd ` (set vl1) = {snd (hd vl)}"

interpretation BD_Security_IO where
istate = istate and step = step and
\<phi> = \<phi> and f = f and \<gamma> = \<gamma> and g = g and T = T and B = B
done

lemma reachNT_non_isPC_isChair:
assumes "reachNT s" and "uid \<in> UIDs"
shows
"(PID \<in>\<in> paperIDs s cid \<and> isPC s cid uid \<longrightarrow> pref s uid PID = Conflict \<or> phase s cid < revPH)
 \<and>
 (PID \<in>\<in> paperIDs s cid \<and> isChair s cid uid \<longrightarrow> pref s uid PID = Conflict \<or> phase s cid < revPH)
 \<and>
 (PID \<in>\<in> paperIDs s cid \<and> isAut s cid uid PID \<longrightarrow>
    phase s cid < notifPH)"
  using assms
  apply induct
  subgoal by (auto simp: istate_def)
  subgoal apply(intro conjI)
    subgoal by (metis (no_types, lifting) T.simps not_le_imp_less trans.collapse)
    subgoal by (metis (mono_tags, lifting) reachNT_reach T.simps isChair_isPC not_le_imp_less reach.Step trans.collapse)
    subgoal by (metis T.simps not_le_imp_less trans.collapse) .
  done

lemma T_\<phi>_\<gamma>:
assumes 1: "reachNT s" and 2: "step s a = (ou,s')" "\<phi> (Trans s a ou s')"
shows "\<not> \<gamma> (Trans s a ou s')"
using reachNT_non_isPC_isChair[OF 1] 2 unfolding T.simps \<phi>_def2
by (fastforce simp: c_defs isRev_imp_isRevNth_getReviewIndex)

lemma T_\<phi>_\<gamma>_stronger:
assumes s: "reach s" and 0: "PID \<in>\<in> paperIDs s cid"
and 2: "step s a = (ou,s')" "\<phi> (Trans s a ou s')"
and 1:  "\<forall> uid \<in> UIDs. isChair s cid uid \<longrightarrow> pref s uid PID = Conflict \<or> phase s cid < revPH"
shows "\<not> \<gamma> (Trans s a ou s')"
proof-
  have "\<not> (\<exists> uid \<in> UIDs. \<exists> cid. PID \<in>\<in> paperIDs s cid \<and>
  isChair s cid uid \<and> pref s uid PID \<noteq> Conflict \<and> phase s cid \<ge> revPH)"
  using 0 1 s by (metis not_le paperIDs_equals)
  thus ?thesis using assms unfolding T.simps \<phi>_def2 by (force simp add: c_defs)
qed

lemma T_\<phi>_\<gamma>_1:
assumes s: "reachNT s" and s1: "reach s1" and PID: "PID \<in>\<in> paperIDs s cid"
and ss1: "eqExcPID2 s s1"
and step1: "step s1 a = (ou1,s1')" and \<phi>1: "\<phi> (Trans s1 a ou1 s1')"
and \<phi>: "\<not> \<phi> (Trans s a ou s')"
shows "\<not> \<gamma> (Trans s1 a ou1 s1')"
proof-
  have "\<forall> uid \<in> UIDs. isChair s cid uid \<longrightarrow> pref s uid PID = Conflict \<or> phase s cid < revPH"
  using reachNT_non_isPC_isChair[OF s] PID by auto
  hence 1: "\<forall> uid \<in> UIDs. isChair s1 cid uid \<longrightarrow> pref s1 uid PID = Conflict \<or> phase s1 cid < revPH"
  using ss1 unfolding eqExcPID2_def using eqExcRLR_imp2 by fastforce
  have PID1: "PID \<in>\<in> paperIDs s1 cid" using PID ss1 eqExcPID2_imp by auto
  show ?thesis apply(rule T_\<phi>_\<gamma>_stronger[OF s1 PID1 step1 \<phi>1]) using 1 by auto
qed

lemma notInPaperIDs_eqExLRL_roles_eq:
assumes s: "reach s" and s1: "reach s1" and PID: "\<not> PID \<in>\<in> paperIDs s cid"
and eq: "eqExcPID2 s s1"
shows "roles s cid uid = roles s1 cid uid"
proof-
  have "\<not> PID \<in>\<in> paperIDs s1 cid" using PID eq unfolding eqExcPID2_def by auto
  hence "\<not> isRev s cid uid PID \<and> \<not> isRev s1 cid uid PID" using s s1 PID by (metis isRev_paperIDs)
  thus ?thesis using eq unfolding eqExcPID2_def eqExcRLR_def
  by (metis Bex_set_list_ex filter_True isRev_def)
qed


(* major *) lemma eqExcPID2_step_out:
assumes ss1: "eqExcPID2 s s1"
and step: "step s a = (ou,s')" and step1: "step s1 a = (ou1,s1')"
and sT: "reachNT s" and s1: "reach s1"
and PID: "PID \<in>\<in> paperIDs s cid" and ph: "phase s cid \<ge> revPH"
and \<phi>: "\<not> \<phi> (Trans s a ou s')" and \<phi>1: "\<not> \<phi> (Trans s1 a ou1 s1')"
and UIDs: "userOfA a \<in> UIDs"
shows "ou = ou1"
proof-
  note s = reachNT_reach[OF sT]
  have s': "reach s'" and s1': "reach s1'" by (metis reach_PairI s s1 step step1)+
  have s's1': "eqExcPID2 s' s1'" by (metis PID \<phi> eqExcPID2_step ph s ss1 step step1)
  note Inv = reachNT_non_isPC_isChair[OF sT UIDs]
  note eqs = eqExcPID2_imp[OF ss1]
  note eqs' = eqExcPID2_imp1[OF ss1]

  note simps[simp] = c_defs u_defs uu_defs r_defs l_defs Paper_dest_conv eqExcPID2_def
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
   using step step1 eqs eqs' s s1 UIDs PID \<phi> \<phi>1 ph
    paperIDs_equals[OF s] Inv
   apply (auto simp add: isRev_getRevRole getRevRole_Some)[]
   apply (metis eqExcPID2_imp' isRev_isPC not_less option.inject pref_Conflict_isRev role.distinct role.inject ss1
                isRev_isPC not_less pref_Conflict_isRev simps2(1) simps2(8) isRev_getRevRole getRevRole_Some)+
   done
  } note this[simp]

  {fix cid uid p pid assume "a = Ract (rFinalDec cid uid p pid)"
   hence ?thesis
   apply(cases "pid = PID")
   using step step1 eqs eqs' s s1 UIDs PID \<phi> \<phi>1 ph
   paperIDs_equals[OF s] Inv using eeqExcPID_RDD by fastforce+
  } note this[simp]

  show ?thesis
    using step step1 eqs eqs' s s1 UIDs PID \<phi> \<phi>1 ph
    paperIDs_equals[OF s] Inv
    apply(cases a)
      subgoal for x1 by (cases x1; auto)
      subgoal for x2 apply(cases x2)
        subgoal by auto
        subgoal by auto
        subgoal by auto
        subgoal by auto
        subgoal by auto
        subgoal by auto
        subgoal apply clarsimp
          subgoal by (metis eqExcPID2_imp' isRev_pref_notConflict_isPC nat_neq_iff simps2(7) ss1)
          subgoal by (metis isRev_pref_notConflict_isPC nat_neq_iff simps2(1)) . .
      subgoal for x3 apply(cases x3)
        subgoal by auto
        subgoal by auto
        subgoal apply clarsimp
          subgoal by (metis isRev_pref_notConflict_isPC le_antisym less_imp_le_nat n_not_Suc_n simps2(1) simps2(5))
          subgoal by (metis isRev_pref_notConflict_isPC le_antisym less_imp_le_nat n_not_Suc_n simps2(1)) .
        subgoal by auto .
      subgoal for x4 apply(cases x4)
        subgoal by auto
        subgoal by auto
        subgoal by auto
        subgoal by auto
        subgoal by clarsimp (metis eqExcPID2_RDD ss1)
        subgoal apply clarsimp
          subgoal by (metis eqExcPID2_RDD ss1)
          subgoal by auto .
        subgoal by auto
        subgoal by auto
        subgoal by clarsimp (metis eqExcPID2_imp2 less_imp_le_nat not_less_eq_eq ss1)
        subgoal by clarsimp (metis less_imp_le_nat not_less_eq_eq)
        subgoal by clarsimp (metis discussion.inject less_imp_le_nat not_less_eq_eq)
        subgoal by clarsimp (metis (mono_tags, lifting) Suc_le_lessD not_less_eq)
        subgoal by auto
        subgoal by clarsimp linarith .
      subgoal for x5 apply(cases x5)
        subgoal by auto
        subgoal by auto
        subgoal by auto
        subgoal by clarsimp (metis (no_types, opaque_lifting) empty_iff list.set(1)
                           notInPaperIDs_eqExLRL_roles_eq notIsPC_eqExLRL_roles_eq simps2(5) ss1)
        subgoal by auto
        subgoal by auto
        subgoal by auto
        subgoal by auto
        subgoal by auto
        subgoal by auto
        subgoal by clarsimp (smt Suc_le_lessD eqExcRLR_imp filter_cong isRev_pref_notConflict_isPC not_less_eq)
        subgoal by clarsimp (metis Suc_le_lessD eqExcPID2_imp' not_less_eq ss1) .
    done
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
   eqExcPID2 s s1 \<and>
   distinct (map fst vl1) \<and>
   fst ` (set vl1) \<subseteq> {uid'. isPC s cid uid' \<and> pref s uid' PID \<noteq> Conflict} \<and>
   fst ` (set vl1) \<inter> {uid'. isRev s1 cid uid' PID} = {} \<and>
   snd ` (set vl1) \<subseteq> {{uid'. isPC s cid uid' \<and> pref s uid' PID \<noteq> Conflict}}"

definition \<Delta>3 :: "state \<Rightarrow> value list \<Rightarrow> state \<Rightarrow> value list \<Rightarrow> bool" where
"\<Delta>3 s vl s1 vl1 \<equiv>
 \<exists> cid. PID \<in>\<in> paperIDs s cid \<and> phase s cid > revPH \<and> eqExcPID2 s s1 \<and> vl1 = []"

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
            hence "\<Delta>1 s' vl' s' vl1" unfolding \<Delta>1_def B_def vl' using PID_ph' c_d vl by auto
            thus ?thesis by auto
          next
            case True
            then obtain CID where PID: "PID \<in>\<in> paperIDs s CID" by auto
            hence ph: "phase s CID < revPH" using PID_ph by auto
            have PID': "PID \<in>\<in> paperIDs s' CID" by (metis PID paperIDs_mono step)
            show ?thesis
            proof(cases "phase s' CID < revPH")
              case True note ph' = True
              hence "\<Delta>1 s' vl' s' vl1" unfolding \<Delta>1_def B_def vl' using vl c_d ph' PID' apply auto
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
                unfolding \<Delta>2_def B_def vl' using c_d ph_rv' PID' by auto
                thus ?thesis by auto
              next
                case False
                hence "\<Delta>e s' vl' s' vl1"
                unfolding \<Delta>e_def vl' using vl c_d ph_rv' PID' by auto
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
  then obtain CID uid where uid: "isChair s CID uid \<and> pref s uid PID \<noteq> Conflict"
  and rs: "reach s" and ph: "phase s CID = revPH" (is "?ph = _") and ss1: "eqExcPID2 s s1"
  and PID: "PID \<in>\<in> paperIDs s CID"
  and dis: "distinct (map fst vl1)"
  and fst_isPC: "fst ` (set vl1) \<subseteq> {uid'. isPC s CID uid' \<and> pref s uid' PID \<noteq> Conflict}"
  and fst_isRev: "fst ` (set vl1) \<inter> {uid'. isRev s1 CID uid' PID} = {}"
  and snd_isPC: "snd ` (set vl1) \<subseteq> {{uid'. isPC s CID uid' \<and> pref s uid' PID \<noteq> Conflict}}"
  using reachNT_reach unfolding \<Delta>2_def by auto
  hence uid_notin: "uid \<notin> UIDs"
    using reachNT_non_isPC_isChair rsT by fastforce
  note vl1_all = dis fst_isPC fst_isRev snd_isPC
  show "iaction ?\<Delta> s vl s1 vl1 \<or>
        ((vl = [] \<longrightarrow> vl1 = []) \<and> reaction ?\<Delta> s vl s1 vl1)" (is "?iact \<or> (_ \<and> ?react)")
  proof(cases vl1)
    case (Cons v1 vl1') note vl1 = Cons
    obtain uid' where v1: "v1 = (uid', {uid'. isPC s CID uid' \<and> pref s uid' PID \<noteq> Conflict})"
    using snd_isPC unfolding vl1 by(cases v1) auto
    hence uid': "isPC s CID uid' \<and> pref s uid' PID \<noteq> Conflict"
    and uid'1: "\<not> isRev s1 CID uid' PID"
    using fst_isPC fst_isRev unfolding vl1 by auto
    have uid1: "isChair s1 CID uid \<and> pref s1 uid PID \<noteq> Conflict"
    using ss1 uid unfolding eqExcPID2_def using eqExcRLR_imp2 by metis
    define a1 where "a1 \<equiv> Cact (cReview CID uid (pass s uid) PID uid')"
    obtain s1' ou1 where step1: "step s1 a1 = (ou1,s1')" by (metis prod.exhaust)
    let ?trn1 = "Trans s1 a1 ou1 s1'"
    have s1s1': "eqExcPID2 s1 s1'" using a1_def step1 cReview_step_eqExcPID2 by blast
    have ss1': "eqExcPID2 s s1'" using eqExcPID2_trans[OF ss1 s1s1'] .
    hence many_s1': "PID \<in>\<in> paperIDs s1' CID" "isChair s1' CID uid \<and> pref s1' uid PID \<noteq> Conflict"
    "phase s1' CID = revPH" "pass s1' uid = pass s uid"
    "isPC s1' CID uid' \<and> pref s1' uid' PID \<noteq> Conflict"
    using uid' uid PID ph unfolding eqExcPID2_def using eqExcRLR_imp2 apply auto by metis+
    hence more_s1': "uid \<in>\<in> userIDs s1'" "CID \<in>\<in> confIDs s1'"
    by (metis paperIDs_confIDs reach_PairI roles_userIDs rs1 step1 many_s1'(1))+
    have ou1: "ou1 = outOK" using step1 unfolding a1_def apply ( simp add: c_defs)
    using more_s1' many_s1' uid'1 by (metis roles_userIDs rs1)
    have f: "f ?trn1 = v1" unfolding a1_def v1 apply simp
    using ss1 unfolding eqExcPID2_def using eqExcRLR_imp2
    by (metis eqExcRLR_set isRevRoleFor.simps(3))
    have rs1': "reach s1'" using rs1 step1 by (auto intro: reach_PairI)
    have ?iact proof
      show "step s1 a1 = (ou1,s1')" by fact
    next
      show \<phi>: "\<phi> ?trn1" using ou1 unfolding a1_def by simp
      thus "consume ?trn1 vl1 vl1'" using f unfolding consume_def vl1 by simp
    next
      show "\<not> \<gamma> ?trn1" by (simp add: a1_def uid_notin)
    next
      have "{uid'. isRev s1' CID uid' PID} \<subseteq> insert uid' {uid'. isRev s1 CID uid' PID}"
      using step1 unfolding a1_def ou1 by (auto simp add: c_defs isRev_def2 )
      hence "fst ` set vl1' \<inter> {uid'. isRev s1' CID uid' PID} = {}"
      using fst_isRev dis unfolding vl1 v1 by auto
      hence "\<Delta>2 s vl s1' vl1'" unfolding \<Delta>2_def
      using PID ph ss1' uid using vl1_all unfolding vl1 by auto
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
      have uid': "isChair s' CID uid \<and> pref s' uid PID \<noteq> Conflict"
      using uid step rs ph PID isChair_persistent revPH_pref_persists[OF rs PID ] by auto
      have all_vl1':
      "fst ` (set vl1) \<subseteq> {uid'. isPC s' CID uid' \<and> pref s' uid' PID \<noteq> Conflict}"
      and "snd ` (set vl1) \<subseteq> {{uid'. isPC s' CID uid' \<and> pref s' uid' PID \<noteq> Conflict}}"
      using vl1_all
      apply (metis (full_types) empty_subsetI image_empty set_empty vl1)
      by (metis (lifting, no_types) empty_set image_is_empty subset_insertI vl1)
      show "match ?\<Delta> s s1 vl1 a ou s' vl' \<or> ignore ?\<Delta> s s1 vl1 a ou s' vl'" (is "?match \<or> ?ignore")
      proof(cases "\<phi> ?trn")
        case False note \<phi> = False
        have vl: "vl' = vl" using c \<phi> unfolding consume_def by (cases vl) auto
        obtain ou1 and s1' where step1: "step s1 a = (ou1,s1')" by (metis prod.exhaust)
        let ?trn1 = "Trans s1 a ou1 s1'"
        have s's1': "eqExcPID2 s' s1'" using eqExcPID2_step[OF rs ss1 step step1 PID] ph \<phi> by auto
        show ?thesis
        proof(cases "ou = outErr \<and> \<not> \<gamma> ?trn")
          case True note ou = True[THEN conjunct1] and \<gamma> = True[THEN conjunct2]
          have s': "s' = s" using step ou by (metis step_outErr_eq)
          have ?ignore proof
            show "\<not> \<gamma> ?trn" by fact
          next
            show "?\<Delta> s' vl' s1 vl1"
            proof(cases "?ph' = revPH")
              case True
              hence "\<Delta>2 s' vl' s1 vl1" using ss1 PID' uid' vl1_all unfolding \<Delta>2_def vl1 s' by auto
              thus ?thesis by auto
            next
              case False hence ph': "?ph' > revPH" using ph rs step s' by blast
              show ?thesis
              proof(cases vl')
                case Nil
                hence "\<Delta>3 s' vl' s1 vl1" using ss1 PID' ph' unfolding \<Delta>3_def vl1 s' by auto
                thus ?thesis by auto
              next
                case Cons
                hence "\<Delta>e s' vl' s1 vl1" using PID' ph' unfolding \<Delta>e_def by auto
                thus ?thesis by auto
              qed
            qed
          qed
          thus ?thesis by auto
        next
          case False note ou_\<gamma> = False
          have \<phi>1: "\<not> \<phi> ?trn1"
          using non_eqExcPID2_step_\<phi>_imp[OF rs ss1 PID _ step step1 \<phi>]
                T_\<phi>_\<gamma>_1[OF rsT rs1 PID ss1 step1 _ \<phi>] ou_\<gamma> by auto
          have ?match
          proof
            show "validTrans ?trn1" using step1 by simp
          next
            show "consume ?trn1 vl1 vl1" unfolding consume_def using \<phi>1 by auto
          next
            show "\<gamma> ?trn = \<gamma> ?trn1" unfolding ss1 by simp
          next
            assume "\<gamma> ?trn" thus "g ?trn = g ?trn1"
            using eqExcPID2_step_out[OF ss1 step step1 rsT rs1 PID _ \<phi> \<phi>1] ph by simp
          next
            show "?\<Delta> s' vl' s1' vl1"
            proof(cases "?ph' = revPH")
              case True note ph' = True
              hence "\<Delta>2 s' vl' s1' vl1" using PID' s's1' uid' ph' vl1_all unfolding \<Delta>2_def vl1 by auto
              thus ?thesis by auto
            next
              case False hence ph': "?ph' > revPH" using ph rs step by (metis antisym_conv2 phase_increases)
              show ?thesis
              proof(cases vl')
                case Nil
                hence "\<Delta>3 s' vl' s1' vl1" using s's1' PID' ph' unfolding \<Delta>3_def vl1 by auto
                thus ?thesis by auto
              next
                case Cons
                hence "\<Delta>e s' vl' s1' vl1" using PID' ph' unfolding \<Delta>e_def by auto
                thus ?thesis by auto
              qed
            qed
          qed
          thus ?thesis by simp
        qed
      next
        case True note \<phi> = True
        have s's: "eqExcPID2 s' s" using eqExcPID2_sym using \<phi>_step_eqExcPID2[OF \<phi> step]  .
        have s's1: "eqExcPID2 s' s1" using eqExcPID2_trans[OF s's ss1] .
        have ?ignore proof
          show "\<not> \<gamma> ?trn" using T_\<phi>_\<gamma> \<phi> rsT step by auto
        next
          show "?\<Delta> s' vl' s1 vl1"
          proof(cases "?ph' = revPH")
            case True
            hence "\<Delta>2 s' vl' s1 vl1" using s's1 PID' uid' vl1_all unfolding \<Delta>2_def vl1 by auto
            thus ?thesis by auto
          next
            case False hence ph': "?ph' > revPH" using ph rs step by (metis antisym_conv2 phase_increases)
            show ?thesis
            proof(cases vl')
                case Nil
                hence "\<Delta>3 s' vl' s1 vl1" using s's1 PID' ph' unfolding \<Delta>3_def vl1 by auto
                thus ?thesis by auto
              next
                case Cons
                hence "\<Delta>e s' vl' s1 vl1" using PID' ph' unfolding \<Delta>e_def by auto
                thus ?thesis by auto
              qed
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
  then obtain CID where rs: "reach s" and ph: "phase s CID > revPH" (is "?ph > _")
  and PID: "PID \<in>\<in> paperIDs s CID" and ss1: "eqExcPID2 s s1"
  and vl1: "vl1 = []"
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
      have ph': "phase s' CID > revPH" using ph rs by (meson less_le_trans local.step phase_increases)
      show "match ?\<Delta> s s1 vl1 a ou s' vl' \<or> ignore ?\<Delta> s s1 vl1 a ou s' vl'" (is "?match \<or> ?ignore")
      proof(cases "\<phi> ?trn")
        case False note \<phi> = False
        have vl': "vl' = vl" using c \<phi> unfolding consume_def by (cases vl) auto
        obtain ou1 and s1' where step1: "step s1 a = (ou1,s1')" by (metis prod.exhaust)
        let ?trn1 = "Trans s1 a ou1 s1'"
        have s's1': "eqExcPID2 s' s1'" using eqExcPID2_step[OF rs ss1 step step1 PID] ph \<phi> by auto
        have \<phi>1: "\<not> \<phi> ?trn1" using \<phi> unfolding eqExcPID2_step_\<phi>[OF rs rs1 ss1 PID ph step step1] .
        have ?match proof
          show "validTrans ?trn1" using step1 by simp
        next
          show "consume ?trn1 vl1 vl1" unfolding consume_def using \<phi>1 by auto
        next
          show "\<gamma> ?trn = \<gamma> ?trn1" unfolding ss1 by simp
        next
          assume "\<gamma> ?trn" thus "g ?trn = g ?trn1"
          using eqExcPID2_step_out[OF ss1 step step1 rsT rs1 PID _ \<phi> \<phi>1] ph by simp
        next
          have "\<Delta>3 s' vl' s1' vl1" using ph' PID' s's1' unfolding \<Delta>3_def vl1 by auto
          thus "?\<Delta> s' vl' s1' vl1" by simp
        qed
        thus ?thesis by simp
      next
        case True note \<phi> = True
        have s's: "eqExcPID2 s' s" using eqExcPID2_sym[OF \<phi>_step_eqExcPID2[OF \<phi> step]] .
        have s's1: "eqExcPID2 s' s1" using eqExcPID2_trans[OF s's ss1] .
        have ?ignore proof
          show "\<not> \<gamma> ?trn" using T_\<phi>_\<gamma> \<phi> rsT step by auto
        next
          have "\<Delta>3 s' vl' s1 vl1" using s's1 PID' ph' vl1 unfolding \<Delta>3_def by auto
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
"K1exit cid s \<equiv> PID \<in>\<in> paperIDs s cid \<and> phase s cid \<ge> revPH \<and>
                \<not> (\<exists> uid. isChair s cid uid \<and> pref s uid PID \<noteq> Conflict)"

lemma invarNT_K1exit: "invarNT (K1exit cid)"
  unfolding invarNT_def
  apply (safe dest!: reachNT_reach)
  subgoal for _ a apply(cases a)
    subgoal for x1 apply(cases x1) apply (fastforce simp add: c_defs K1exit_def geq_noPH_confIDs)+ .
    subgoal for x2 apply(cases x2) apply (auto simp add: u_defs K1exit_def paperIDs_equals)
      apply (metis less_eq_Suc_le less_not_refl paperIDs_equals) .
    subgoal for x3 apply(cases x3) apply (auto simp add: uu_defs K1exit_def) .
    by auto
  done

lemma noVal_K1exit: "noVal (K1exit cid) v"
  apply(rule no\<phi>_noVal)
  unfolding no\<phi>_def
  apply safe
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
  using assms
  apply(cases a)
  subgoal for x1 apply(cases x1)
           apply (auto simp add: c_defs)
    by (metis paperIDs_confIDs)
  subgoal for x2 apply(cases x2) apply (auto simp add: u_defs) .
  subgoal for x3 apply(cases x3) apply (auto simp add: uu_defs) .
  by auto

lemma revPH_pref_constant:
assumes s: "reach s"
and "step s a = (ou,s')"
and "pid \<in>\<in> paperIDs s cid" and "phase s cid \<ge> revPH"
shows "pref s' uid pid = pref s uid pid"
  using assms
  apply(cases a)
  subgoal for x1 apply(cases x1)
           apply (auto simp add: c_defs)
      apply (metis paperIDs_getAllPaperIDs)
     apply (metis Suc_n_not_le_n le_SucI paperIDs_equals)
    apply (metis Suc_n_not_le_n le_SucI paperIDs_equals) .
  subgoal for x2 apply(cases x2)
          apply (auto simp add: u_defs)
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
  unfolding noVal2_def
  apply safe
  subgoal for _ a apply(cases a)
    subgoal for x1 apply(cases x1)
             apply (auto simp add: c_defs K2exit_def)
      by (metis paperIDs_equals reachNT_reach)+
    by auto
  done

definition K3exit where
"K3exit cid s \<equiv> PID \<in>\<in> paperIDs s cid \<and> phase s cid > revPH"

lemma invarNT_K3exit: "invarNT (K3exit cid)"
  unfolding invarNT_def
  apply (safe dest!: reachNT_reach)
  subgoal for _ a apply(cases a)
    subgoal for x1 apply(cases x1) apply (auto simp add: c_defs K3exit_def) .
    subgoal for x2 apply(cases x2) apply (auto simp add: u_defs K3exit_def) .
    subgoal for x3 apply(cases x3) apply (auto simp add: uu_defs K3exit_def) .
    by auto
  done

lemma noVal_K3exit: "noVal (K3exit cid) v"
  apply(rule no\<phi>_noVal)
  unfolding no\<phi>_def
  apply safe
  subgoal for _ a apply(cases a)
    subgoal for x1 apply(cases x1)
             apply (auto simp add: c_defs K3exit_def)
      using paperIDs_equals reachNT_reach by fastforce
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
