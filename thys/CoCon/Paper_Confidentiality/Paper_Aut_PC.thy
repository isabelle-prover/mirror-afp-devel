theory Paper_Aut_PC
imports "../Observation_Setup" Paper_Value_Setup "Bounded_Deducibility_Security.Compositional_Reasoning"
begin

subsection \<open>Confidentiality protection from users who are not the
paper's authors or PC members\<close>

text \<open>We verify the following property:

\ \\
A group of users UIDs
learns nothing about the various uploads of a paper PID
(save for the non-existence of any upload)
unless/until one of the following occurs:
\begin{itemize}
\item a user in UIDs becomes the paper's author or
\item a user in UIDs becomes a PC member in the paper's conference
and the conference moves to the bidding phase.
\end{itemize}
\<close>

fun T :: "(state,act,out) trans \<Rightarrow> bool" where
"T (Trans _ _ ou s') =
 (\<exists> uid \<in> UIDs.
    isAUT s' uid PID \<or>
    (\<exists> cid. PID \<in>\<in> paperIDs s' cid \<and> isPC s' cid uid \<and> phase s' cid \<ge> bidPH)
 )"

declare T.simps [simp del]

definition B :: "value list \<Rightarrow> value list \<Rightarrow> bool" where
"B vl vl1 \<equiv> vl \<noteq> []"

interpretation BD_Security_IO where
istate = istate and step = step and
\<phi> = \<phi> and f = f and \<gamma> = \<gamma> and g = g and T = T and B = B
done

lemma reachNT_non_isAut_isPC_isChair:
assumes "reachNT s" and "uid \<in> UIDs"
shows
"\<not> isAut s cid uid PID \<and>
 (isPC s cid uid \<longrightarrow> \<not> PID \<in>\<in> paperIDs s cid \<or> phase s cid \<le> subPH) \<and>
 (isChair s cid uid \<longrightarrow> \<not> PID \<in>\<in> paperIDs s cid \<or> phase s cid \<le> subPH)"
  using assms
  apply (cases rule: reachNT_state_cases)
   apply (auto simp: istate_def)[]
  apply clarsimp
    (* safety property used: isChair_isPC *)
  by (simp add: T.simps assms(1) isAUT_def isChair_isPC not_less_eq_eq reachNT_reach)


lemma P_\<phi>_\<gamma>:
assumes 1: "reachNT s" and 2: "step s a = (ou,s')" "\<phi> (Trans s a ou s')"
shows "\<not> \<gamma> (Trans s a ou s')"
using reachNT_non_isAut_isPC_isChair[OF 1] 2 unfolding T.simps \<phi>_def2
by (auto simp add: u_defs)

(* Note: the following alternative formulation is not always guaranteed to hold,
due to the trigger T speaking about s', not s:
lemma P_\<phi>_\<gamma>:
assumes 1: "\<not> T (Trans s a ou s')" and 2: "step s a = (ou,s')" "\<phi> (Trans s a ou s')"
shows "\<not> \<gamma> (Trans s a ou s')"
using 1 2 unfolding T.simps \<phi>_def2
by (auto simp add: u_defs)
*)

text \<open>major\<close> lemma eqButPID_step_out:
assumes s's1': "eqButPID s s1"
and step: "step s a = (ou,s')" and step1: "step s1 a = (ou1,s1')"
and sT: "reachNT s" and s1: "reach s1"
and PID: "PID \<in>\<in> paperIDs s cid"
and UIDs: "userOfA a \<in> UIDs"
shows "ou = ou1"
proof-
  note Inv = reachNT_non_isAut_isPC_isChair[OF sT UIDs]
  note eqs = eqButPID_imp[OF s's1']
  note eqs' = eqButPID_imp1[OF s's1']
  note s = reachNT_reach[OF sT]

  note simps[simp] = c_defs u_defs uu_defs r_defs l_defs Paper_dest_conv eqButPID_def eeqButPID_def eqButC
  note * = step step1 eqs eqs' s s1 PID UIDs paperIDs_equals[OF s] Inv

  show ?thesis
  proof (cases a)
    case (Cact x1)
    then show ?thesis using * by (cases x1; auto)
  next
    case (Uact x2)
    then show ?thesis using * by (cases x2; auto)
  next
    case (UUact x3)
    then show ?thesis using * by (cases x3; auto)
  next
    case (Ract x4)
    with * show ?thesis
    proof (cases x4)
      case (rPaperC x61 x62 x63 x64)
      then show ?thesis using * Ract by (clarsimp; metis not_less_eq_eq)
    next
      case (rMyReview x81 x82 x83 x84)
      then show ?thesis using * Ract by (auto simp: getNthReview_def)
    next
      case (rReviews x91 x92 x93 x94)
      then show ?thesis using * Ract by (clarsimp; metis Suc_leD eqButPID_imp2 not_less_eq_eq s's1')
    qed auto
  next
    case (Lact x5)
    then show ?thesis using * by (cases x5; auto)
  qed
qed

definition \<Delta>1 :: "state \<Rightarrow> value list \<Rightarrow> state \<Rightarrow> value list \<Rightarrow> bool" where
"\<Delta>1 s vl s1 vl1 \<equiv> \<not> (\<exists>cid. PID \<in>\<in> paperIDs s cid) \<and> s = s1 \<and> B vl vl1"

definition \<Delta>2 :: "state \<Rightarrow> value list \<Rightarrow> state \<Rightarrow> value list \<Rightarrow> bool" where
"\<Delta>2 s vl s1 vl1 \<equiv>
 \<exists>cid. PID \<in>\<in> paperIDs s cid \<and> phase s cid = subPH \<and> eqButPID s s1"

definition \<Delta>3 :: "state \<Rightarrow> value list \<Rightarrow> state \<Rightarrow> value list \<Rightarrow> bool" where
"\<Delta>3 s vl s1 vl1 \<equiv>
 \<exists>cid. PID \<in>\<in> paperIDs s cid \<and> eqButPID s s1 \<and> phase s cid > subPH \<and> vl=[] \<and> vl1=[]"

definition \<Delta>e :: "state \<Rightarrow> value list \<Rightarrow> state \<Rightarrow> value list \<Rightarrow> bool" where
"\<Delta>e s vl s1 vl1 \<equiv>
 \<exists>cid. PID \<in>\<in> paperIDs s cid \<and> phase s cid > subPH \<and> vl \<noteq> []"

lemma istate_\<Delta>1:
assumes B: "B vl vl1"
shows "\<Delta>1 istate vl istate vl1"
using B unfolding \<Delta>1_def B_def istate_def by auto

lemma unwind_cont_\<Delta>1: "unwind_cont \<Delta>1 {\<Delta>1,\<Delta>2,\<Delta>e}"
proof(rule, goal_cases)
  case (1 s vl s1 vl1)
  (*fix s s1 :: state and vl vl1 :: "value list"*)
  assume rsT: "reachNT s" and rs1: "reach s1" and "\<Delta>1 s vl s1 vl1"
  hence rs: "reach s" and ss1: "s1 = s" and vl: "vl \<noteq> []"
    and pid: "\<forall>cid. PID \<notin> set (paperIDs s cid)"
  using reachNT_reach unfolding \<Delta>1_def B_def by auto
  show ?case (is "?iact \<or> (_ \<and> ?react)")
  proof-
    have ?react proof (rule, goal_cases)
      case (1 a ou s' vl')
      let ?trn = "Trans s a ou s'"  let ?trn1 = "Trans s1 a ou s'"
      assume step: "step s a = (ou, s')"
        and T: "\<not> T ?trn" and c: "consume ?trn vl vl'"
      have \<phi>: "\<not> \<phi> ?trn"
        apply(cases a)
        subgoal by simp
        subgoal for x2 apply(cases x2) using step pid by(auto simp: u_defs)
        by simp_all
      hence vl': "vl' = vl" using c unfolding consume_def by auto
      show ?case (is "?match \<or> ?ignore")
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
          show "disjAll {\<Delta>1, \<Delta>2, \<Delta>e} s' vl' s' vl1"
          proof (cases "\<exists>cid. PID \<in>\<in> paperIDs s' cid")
            case False hence "\<Delta>1 s' vl' s' vl1"
              by (simp add: \<Delta>1_def B_def vl vl')
            thus ?thesis by simp
          next
            case True
            hence "\<Delta>2 s' vl' s' vl1"
              using step pid
              apply (simp add: \<Delta>2_def vl' vl)
              apply (erule exE)
              subgoal for cid apply (rule exI[of _ cid])
                apply (cases a)
                  subgoal for x1 apply (cases x1, auto simp: c_defs) [] .
                  subgoal for x2 apply (cases x2, auto simp: u_defs) [] .
                  subgoal for x3 apply (cases x3, auto simp: uu_defs) [] .
                  by simp_all
              done
            thus ?thesis by simp
          qed
        qed
        thus ?thesis by simp
      qed
    qed
    thus ?thesis using vl by simp
  qed
qed

lemma unwind_cont_\<Delta>2: "unwind_cont \<Delta>2 {\<Delta>2,\<Delta>3,\<Delta>e}"
proof(rule,goal_cases)
  case (1 s vl s1 vl1)
  assume rsT: "reachNT s" and rs1: "reach s1" and "\<Delta>2 s vl s1 vl1"
  then obtain cid where rs: "reach s"
    and pid: "PID \<in>\<in> paperIDs s cid" and ss1: "eqButPID s s1"
    and ph: "phase s cid = subPH"
    using reachNT_reach unfolding \<Delta>2_def by auto

  have cid: "cid \<in>\<in> confIDs s"
    by (metis paperIDs_confIDs pid rs)

  from pid ph cid have
    pid1: "PID \<in>\<in> paperIDs s1 cid"
    and ph1: "phase s1 cid = subPH"
    and cid1: "cid \<in>\<in> confIDs s1"
    by (auto simp add: eqButPID_imp[OF ss1])


  show ?case (is "?iact \<or> (_ \<and> ?react)")
  proof (cases vl1)
    case (Cons v vl1') note this[simp]
    obtain uid1 where aut1: "isAut s1 cid uid1 PID"
      thm paperID_ex_userID
      using paperID_ex_userID[OF rs1 pid1] by auto
    have uid1: "uid1 \<in>\<in> userIDs s1"
      by (metis roles_userIDs rs1 aut1)

    from aut1 have "isAut s cid uid1 PID"
      using ss1 aut1 by (simp add: eqButPID_imp[OF ss1])
    with reachNT_non_isAut_isPC_isChair[OF rsT] uid1 have uid1_ne: "uid1\<notin>UIDs"
      by auto

    let ?a1 = "(Uact (uPaperC cid uid1 (pass s1 uid1) PID v))"
    obtain s1' where step: "step s1 ?a1 = (outOK,s1')" and s1's1: "eqButPID s1' s1"
      by (cases "paper s1 PID")
         (auto simp add: u_defs cid1 uid1 pid1 ph1 aut1 eqButPID_def eeqButPID_def)

    have "?iact"
    proof
      show "step s1 ?a1 = (outOK,s1')" using step .
      show "\<phi> (Trans s1 ?a1 outOK s1')" by simp
      show "consume (Trans s1 ?a1 outOK s1') vl1 vl1'" by (simp add: consume_def)
      show "\<not>\<gamma> (Trans s1 ?a1 outOK s1')" by (simp add: uid1_ne)
      have "\<Delta>2 s vl s1' vl1'" unfolding \<Delta>2_def
        apply (rule exI[where x=cid])
        using ph pid
        apply clarsimp
        by (metis s1's1 eqButPID_sym eqButPID_trans ss1)
      thus "disjAll {\<Delta>2, \<Delta>3, \<Delta>e} s vl s1' vl1'" by simp
    qed
    thus ?thesis by simp
  next
    case Nil note this[simp]
    have "?react"
    proof (rule, goal_cases)
      case (1 a ou s' vl')
      assume STEP: "step s a = (ou, s')" and "\<not> T (Trans s a ou s')"
        and CONSUME: "consume (Trans s a ou s') vl vl'"

      have ph': "phase s' cid \<ge> subPH"
        by (smt STEP ph phase_increases)

      have pid': "PID \<in>\<in> paperIDs s' cid" using pid STEP
        by (metis paperIDs_mono)

      {
        fix s1 vl1
        assume "phase s' cid \<noteq> subPH" "vl'\<noteq>[]"
        hence "\<Delta>e s' vl' s1 vl1"
          unfolding \<Delta>e_def
          apply -
          apply(rule exI[of _ cid])
          using STEP CONSUME ph
          apply (cases a)
          subgoal for x1 apply (cases x1) apply(auto simp: c_defs) .
          subgoal for x2 apply (cases x2) apply(auto simp: u_defs consume_def pid) .
          subgoal for x3 apply (cases x3) apply(auto simp: uu_defs) .
          by simp_all
      } note \<Delta>e=this

      obtain s1' ou' where
        STEP': "step s1 a = (ou',s1')" and s's1': "eqButPID s' s1'"
        using eqButPID_step[OF ss1 STEP]
        by fastforce

      from eqButPID_step_\<phi>[OF ss1 STEP STEP']
      have \<phi>_eq: "\<phi> (Trans s1 a ou' s1') = \<phi> (Trans s a ou s')" by simp

      show ?case (is "?match \<or> ?ignore")
      proof (cases "\<phi> (Trans s a ou s')")
        case True note \<phi>=this

        then obtain cid' uid p where
          a[simp]: "a=Uact (uPaperC cid' uid p PID (hd vl))" "ou=outOK"
          using CONSUME
          by (cases "(Trans s a ou s')" rule: f.cases) (auto simp add: consume_def)

        from STEP pid have [simp]: "cid'=cid"
          by (simp add: u_defs paperIDs_equals[OF rs])

        from \<phi>_step_eqButPID[OF \<phi> STEP] have ss': "eqButPID s s'" .

        have n\<gamma>: "\<not>\<gamma> (Trans s a ou s')"
          using P_\<phi>_\<gamma>[OF rsT STEP] by simp

        have ph': "phase s' cid = subPH"
          using STEP by (auto simp add: u_defs)

        have ?ignore
        proof
          show "\<not> \<gamma> (Trans s a ou s')" by (rule n\<gamma>)
          have "\<Delta>2 s' vl' s1 vl1"
            unfolding \<Delta>2_def
            using ph' pid' eqButPID_trans[OF eqButPID_sym[OF ss'] ss1]
            by auto
          thus "disjAll {\<Delta>2, \<Delta>3, \<Delta>e} s' vl' s1 vl1" by simp
        qed
        thus ?thesis by simp
      next
        case False note \<phi>=this
        with CONSUME have [simp]: "vl'=vl" by (simp add: consume_def)

        have ?match proof
          show "validTrans (Trans s1 a ou' s1')" using STEP' by simp
          show "consume (Trans s1 a ou' s1') vl1 vl1" using \<phi>
            by (simp add: consume_def \<phi>_eq)
          show "\<gamma> (Trans s a ou s') = \<gamma> (Trans s1 a ou' s1')" by simp
          show "\<gamma> (Trans s a ou s') \<Longrightarrow> g (Trans s a ou s') = g (Trans s1 a ou' s1')"
            using eqButPID_step_out[OF ss1 STEP STEP' rsT rs1 pid]
            by simp
          show "disjAll {\<Delta>2, \<Delta>3, \<Delta>e} s' vl' s1' vl1"
          proof (cases "phase s' cid = subPH")
            case True
            hence "\<Delta>2 s' vl' s1' vl1"
              unfolding \<Delta>2_def
              using eqButPID_step[OF ss1 STEP STEP']
              using ph' pid' by auto
            thus ?thesis by simp
          next
            case False with ph' have ph': "subPH < phase s' cid" by simp
            show ?thesis proof (cases "vl'=[]")
              case False
              hence "\<Delta>e s' vl' s1' vl1" using \<Delta>e ph' by simp
              thus ?thesis by simp
            next
              case True
              hence "\<Delta>3 s' vl' s1' vl1"
                unfolding \<Delta>3_def
                apply(intro exI[of _ cid])
                using ph' pid' eqButPID_step[OF ss1 STEP STEP']
                by simp
              thus ?thesis by simp
            qed
          qed
        qed
        thus ?thesis by simp
      qed
    qed
    thus ?thesis by simp
  qed
qed

lemma unwind_cont_\<Delta>3: "unwind_cont \<Delta>3 {\<Delta>3,\<Delta>e}"
proof (rule, goal_cases)
  case (1 s vl s1 vl1)
  assume rsT: "reachNT s" and rs1: "reach s1" and \<Delta>: "\<Delta>3 s vl s1 vl1"
  thm \<Delta>3_def
  then obtain cid where ss1: "eqButPID s s1" and [simp]: "vl=[]" "vl1=[]"
    and pid: "PID \<in>\<in> paperIDs s cid" and ph: "subPH < phase s cid"
    unfolding \<Delta>3_def by auto

  from rsT have rs: "reach s"
    by (metis reachNT_reach)

  from pid ph have
    pid1: "PID \<in>\<in> paperIDs s1 cid"
    and ph1: "subPH < phase s1 cid"
    using ss1
    by (auto simp add: eqButPID_imp)


  thus ?case (is "_ \<or> (_ \<and> ?react)")
  proof -
    have "?react"
    proof (rule, goal_cases)
      case (1 a ou s' vl')
      assume STEP: "step s a = (ou, s')" and NT: "\<not> T (Trans s a ou s')" (is "\<not>T ?trn")
        and CONSUME: "consume (Trans s a ou s') vl vl'"

      show ?case (is "?match \<or> _")
      proof -

        have ph': "subPH < phase s' cid"
         using STEP ph phase_increases by (meson le_trans not_less)

        have [simp]: "vl'=[]" using CONSUME by (auto simp add: consume_def)

        obtain ou1 and s1' where STEP1: "step s1 a = (ou1,s1')"
          by (metis prod.exhaust)
        let ?trn1 = "Trans s1 a ou1 s1'"
        have s's1': "eqButPID s' s1'" using eqButPID_step[OF ss1 STEP STEP1] .

        from s's1' ph' have ph1': "subPH < phase s1' cid"
          by (simp add: eqButPID_imp)

        have \<phi>: "\<not> \<phi> ?trn1"
          using STEP1 ph1' unfolding \<phi>_def2 by (auto simp: u_defs paperIDs_equals[OF rs1 pid1])

        have ?match proof
          show "validTrans ?trn1" using STEP1 by simp
        next
          show "consume ?trn1 vl1 vl1" unfolding consume_def using \<phi> by auto
        next
          show "\<gamma> ?trn = \<gamma> ?trn1" unfolding ss1 by simp
        next
          assume "\<gamma> ?trn" thus "g ?trn = g ?trn1"
          using eqButPID_step_out[OF ss1 STEP STEP1 rsT rs1 pid] by simp
        next
          have "\<Delta>3 s' vl' s1' vl1" using ph' s's1' paperIDs_mono[OF STEP pid]
            unfolding \<Delta>3_def by auto
          thus "disjAll {\<Delta>3, \<Delta>e} s' vl' s1' vl1" by simp
        qed
        thus ?thesis by simp
      qed
    qed
    thus ?case by simp
  qed
qed


definition K1exit where
"K1exit s \<equiv> \<exists>cid. phase s cid > subPH \<and> PID \<in>\<in> paperIDs s cid"

lemma invarNT_K1exit: "invarNT K1exit"
  unfolding invarNT_def apply (safe dest!: reachNT_reach)
  subgoal for _ a apply(cases a)
    subgoal for x1 apply (cases x1, auto simp: c_defs K1exit_def) .
    subgoal for x2 apply (cases x2)
      apply(auto simp: u_defs K1exit_def paperIDs_equals)
      apply (metis less_nat_zero_code)
      apply (metis Suc_lessD) .
    subgoal for x3 apply (cases x3, auto simp: uu_defs K1exit_def) .
    by simp_all
  done

lemma noVal_K1exit: "noVal K1exit v"
  apply(rule no\<phi>_noVal)
  unfolding no\<phi>_def apply safe
  subgoal for _ a apply(cases a)
    subgoal by simp
    subgoal for x2
      apply(cases x2, auto simp add: u_defs K1exit_def) []
      apply (metis reachNT_reach less_not_refl paperIDs_equals) .
    by simp_all
  done

lemma unwind_exit_\<Delta>e: "unwind_exit \<Delta>e"
proof
  fix s s1 :: state and vl vl1 :: "value list"
  assume rsT: "reachNT s" and rs1: "reach s1" and \<Delta>e: "\<Delta>e s vl s1 vl1"
  hence vl: "vl \<noteq> []" using reachNT_reach unfolding \<Delta>e_def by auto
  hence "K1exit s" using \<Delta>e unfolding K1exit_def \<Delta>e_def by auto
  thus "vl \<noteq> [] \<and> exit s (hd vl)" apply(simp add: vl)
  by (metis rsT exitI2 invarNT_K1exit noVal_K1exit)
qed

theorem secure: secure
  apply(rule unwind_decomp3_secure[of \<Delta>1 \<Delta>2 \<Delta>e \<Delta>3])
  using
    istate_\<Delta>1
    unwind_cont_\<Delta>1 unwind_cont_\<Delta>2 unwind_cont_\<Delta>3
    unwind_exit_\<Delta>e
  by auto

end
