theory Paper_Aut
imports "../Observation_Setup" Paper_Value_Setup "Bounded_Deducibility_Security.Compositional_Reasoning"
begin

subsection \<open>Confidentiality protection from non-authors\<close>

text \<open>We verify the following property:

\ \\
A group of users UIDs
learns nothing about the various uploads of a paper PID
except for the last (most recent) upload
unless/until a user in UIDs becomes an author of the paper.

\ \\
\<close>

fun T :: "(state,act,out) trans \<Rightarrow> bool" where
"T (Trans _ _ ou s') = (\<exists> uid \<in> UIDs. isAUT s' uid PID)"

declare T.simps [simp del]

definition B :: "value list \<Rightarrow> value list \<Rightarrow> bool" where
"B vl vl1 \<equiv> vl \<noteq> [] \<and> vl1 \<noteq> [] \<and> last vl = last vl1"

interpretation BD_Security_IO where
istate = istate and step = step and
\<phi> = \<phi> and f = f and \<gamma> = \<gamma> and g = g and T = T and B = B
done

lemma reachNT_non_isAut:
assumes "reachNT s" and "uid \<in> UIDs"
shows "\<not> isAut s cid uid PID"
  using assms
  apply induct
   apply (auto simp: istate_def)[]
  subgoal for trn apply(cases trn, auto simp: T.simps reachNT_reach isChair_isPC isAUT_def) .
  done


lemma T_\<phi>_\<gamma>:
assumes 1: "reachNT s" and 2: "step s a = (ou,s')" "\<phi> (Trans s a ou s')"
shows "\<not> \<gamma> (Trans s a ou s')"
using reachNT_non_isAut[OF 1] 2 unfolding T.simps \<phi>_def2
by (auto simp add: u_defs)

(* major *) lemma eqButPID_step_out:
assumes ss1: "eqButPID s s1"
and step: "step s a = (ou,s')" and step1: "step s1 a = (ou1,s1')"
and sT: "reachNT s" and s1: "reach s1"
and PID: "PID \<in>\<in> paperIDs s cid"
and ph: "phase s cid = subPH"
and UIDs: "userOfA a \<in> UIDs"
shows "ou = ou1"
proof-
  note Inv = reachNT_non_isAut[OF sT UIDs]
  note eqs = eqButPID_imp[OF ss1]
  note eqs' = eqButPID_imp1[OF ss1]
  note s = reachNT_reach[OF sT]
  have PID': "PID \<in>\<in> paperIDs s1 cid" and ph': "phase s cid = subPH"
  using PID ph ss1 unfolding eqButPID_def by auto

  note simps[simp] = c_defs u_defs uu_defs r_defs l_defs Paper_dest_conv eqButPID_def eeqButPID_def eqButC
  note * = step step1 eqs eqs' s s1 PID ph PID' ph' UIDs paperIDs_equals[OF s] Inv

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
      then show ?thesis using * Ract by (clarsimp; metis Suc_n_not_le_n)
    next
      case (rMyReview x81 x82 x83 x84)
      then show ?thesis using * Ract by (auto simp: getNthReview_def)
    next
      case (rReviews x91 x92 x93 x94)
      then show ?thesis using * Ract by (clarsimp; metis Suc_leD eqButPID_imp2 not_less_eq_eq ss1)
    qed auto
  next
    case (Lact x5)
    then show ?thesis using * by (cases x5; auto)
  qed
qed

text \<open>major\<close> lemma eqButPID_step_eq:
assumes ss1: "eqButPID s s1"
and [simp]: "a=Uact (uPaperC cid uid p PID ct)" "ou=outOK"
and step: "step s a = (ou, s')" and step1: "step s1 a = (ou', s1')"
shows "s' = s1'"
  using ss1 step step1
  apply (simp add: u_defs eqButPID_paper )
  subgoal by (cases s; cases s1; auto simp add: eqButPID_def eeqButPID_def)
  subgoal by (use ss1 step step1 in \<open>auto simp add: eqButPID_def eeqButPID_def\<close>)
  done

definition \<Delta>1 :: "state \<Rightarrow> value list \<Rightarrow> state \<Rightarrow> value list \<Rightarrow> bool" where
"\<Delta>1 s vl s1 vl1 \<equiv>
 \<not> (\<exists> cid. PID \<in>\<in> paperIDs s cid) \<and> s = s1 \<and> B vl vl1"

definition \<Delta>2 :: "state \<Rightarrow> value list \<Rightarrow> state \<Rightarrow> value list \<Rightarrow> bool" where
"\<Delta>2 s vl s1 vl1 \<equiv>
 (\<exists> cid. PID \<in>\<in> paperIDs s cid \<and> phase s cid = subPH) \<and>
 eqButPID s s1 \<and> B vl vl1"


definition \<Delta>3 :: "state \<Rightarrow> value list \<Rightarrow> state \<Rightarrow> value list \<Rightarrow> bool" where
"\<Delta>3 s vl s1 vl1 \<equiv>
 (\<exists> cid. PID \<in>\<in> paperIDs s cid) \<and> s = s1 \<and> vl = [] \<and> vl1 = []"


definition \<Delta>e :: "state \<Rightarrow> value list \<Rightarrow> state \<Rightarrow> value list \<Rightarrow> bool" where
"\<Delta>e s vl s1 vl1 \<equiv>
 (\<exists> cid. PID \<in>\<in> paperIDs s cid \<and> phase s cid > subPH) \<and> vl \<noteq> []"

lemma istate_\<Delta>1:
assumes B: "B vl vl1"
shows "\<Delta>1 istate vl istate vl1"
using assms unfolding \<Delta>1_def B_def istate_def by auto

lemma unwind_cont_\<Delta>1: "unwind_cont \<Delta>1 {\<Delta>1,\<Delta>2,\<Delta>e}"
proof(rule)
  let ?\<Delta> = "disjAll {\<Delta>1, \<Delta>2, \<Delta>e}"
  fix s s1 :: state and vl vl1 :: "value list"
  assume rsT: "reachNT s" and rs1: "reach s1" and "\<Delta>1 s vl s1 vl1"
  hence rs: "reach s" and cid: "\<forall>cid. \<not> PID \<in>\<in> paperIDs s cid"
    and ss1: "s1 = s" and vl: "vl \<noteq> []" and vl1: "vl1 \<noteq> []" and vlvl1: "last vl = last vl1"
  using reachNT_reach unfolding \<Delta>1_def B_def by auto
  show "iaction ?\<Delta> s vl s1 vl1 \<or>
        ((vl \<noteq> [] \<or> vl1 = []) \<and> reaction ?\<Delta> s vl s1 vl1)" (is "?iact \<or> (_ \<and> ?react)")
  proof -
    have "?react"
    proof (rule, goal_cases)
      case (1 a ou s' vl')
      assume STET: "step s a = (ou, s')" and "\<not> T (Trans s a ou s')"
        and CONSUME: "consume (Trans s a ou s') vl vl'"

      have not_phi: "\<not>\<phi> (Trans s a ou s')"
        using STET cid
        by (auto simp: \<phi>_def2 u_defs)
      with CONSUME have vlvl': "vl'=vl"
        by (simp add: consume_def)

      have "match (disjAll {\<Delta>1, \<Delta>2, \<Delta>e}) s s1 vl1 a ou s' vl'"
      proof
        show "validTrans (Trans s1 a ou s')" using STET by (simp add: ss1)
        show "consume (Trans s1 a ou s') vl1 vl1"
          by (simp add: consume_def ss1 not_phi)

        show "\<gamma> (Trans s a ou s') = \<gamma> (Trans s1 a ou s')" by simp
        show "g (Trans s a ou s') = g (Trans s1 a ou s')" by simp
        show "disjAll {\<Delta>1, \<Delta>2, \<Delta>e} s' vl' s' vl1"
        proof (cases "\<exists>cid. PID \<in>\<in> paperIDs s' cid")
          case False hence "\<Delta>1 s' vl' s' vl1"
            by (simp add: \<Delta>1_def B_def vlvl' vl vl1 vlvl1)
          thus ?thesis by simp
        next
          case True hence "\<Delta>2 s' vl' s' vl1"
            apply (simp add: \<Delta>2_def B_def vlvl' vl vl1 vlvl1)
            apply (erule exE)
            subgoal for cid apply(rule exI[of _ cid])
              apply simp
              apply (use STET cid in \<open>cases a\<close>)
              subgoal for x1 apply(cases x1) apply(auto simp: c_defs) .
              subgoal for x2 apply(cases x2) apply(auto simp: u_defs) .
              subgoal for x3 apply(cases x3) apply(auto simp: uu_defs) .
              subgoal by simp
              subgoal by simp
              done
            done
          thus ?thesis by simp
        qed
      qed
      thus ?case by simp
    qed
    thus ?thesis using vl vl1 by auto
  qed
qed

lemma unwind_cont_\<Delta>2: "unwind_cont \<Delta>2 {\<Delta>2,\<Delta>3,\<Delta>e}"
proof (rule, goal_cases)
  case (1 s vl s1 vl1)
  assume rsT: "reachNT s" and rs1: "reach s1" and "\<Delta>2 s vl s1 vl1"
  then obtain cid where
    rs: "reach s" and pid: "PID \<in>\<in> paperIDs s cid" and ph: "phase s cid = subPH"
    and ss1: "eqButPID s s1"
  and vl: "vl \<noteq> []" and vl1: "vl1 \<noteq> []" and vlvl1: "last vl = last vl1"
  using reachNT_reach unfolding \<Delta>2_def B_def by auto

  have cid: "cid \<in>\<in> confIDs s"
    by (metis paperIDs_confIDs pid rs)

  from pid ph cid have
    pid1: "PID \<in>\<in> paperIDs s1 cid"
    and ph1: "phase s1 cid = subPH"
    and cid1: "cid \<in>\<in> confIDs s1"
    by (auto simp add: eqButPID_imp[OF ss1])

  show ?case (is "?iact \<or> (_ \<and> ?react)")
  proof (cases "length vl1>1")
    case True then obtain v vl1' where [simp]: "vl1 = v#vl1'" "vl1'\<noteq>[]" by (cases vl1) auto

    obtain uid1 where aut1: "isAut s1 cid uid1 PID"
      thm paperID_ex_userID
      using paperID_ex_userID[OF rs1 pid1] by auto
    have uid1: "uid1 \<in>\<in> userIDs s1"
      by (metis roles_userIDs rs1 aut1)

    from aut1 have "isAut s cid uid1 PID"
      using ss1 aut1 by (simp add: eqButPID_imp[OF ss1])
    with reachNT_non_isAut[OF rsT] uid1 have uid1_ne: "uid1\<notin>UIDs"
      by auto

    let ?a1 = "(Uact (uPaperC cid uid1 (pass s1 uid1) PID v))"
    obtain s1' where step: "step s1 ?a1 = (outOK,s1')" and s1's1: "eqButPID s1' s1"
      apply (simp add: u_defs cid1 uid1 pid1 ph1 aut1)
      apply (cases "paper s1 PID")
      apply (auto simp: eqButPID_def eeqButPID_def)
      done

    have "?iact"
    proof
      show "step s1 ?a1 = (outOK,s1')" using step .
      show "\<phi> (Trans s1 ?a1 outOK s1')" by simp
      show "consume (Trans s1 ?a1 outOK s1') vl1 vl1'" by (simp add: consume_def)
      show "\<not>\<gamma> (Trans s1 ?a1 outOK s1')" by (simp add: uid1_ne)
      have "\<Delta>2 s vl s1' vl1'" unfolding \<Delta>2_def B_def
        using vl vlvl1 ph pid
        apply simp_all
        by (metis s1's1 eqButPID_sym eqButPID_trans ss1)
      thus "disjAll {\<Delta>2, \<Delta>3, \<Delta>e} s vl s1' vl1'" by simp
    qed
    thus ?thesis by simp
  next
    case False then obtain v1 where [simp]: "vl1=[v1]" using vl1 by (cases vl1) auto

    have "?react"
    proof (rule, goal_cases)
      case (1 a ou s' vl')
      assume STET: "step s a = (ou, s')" and "\<not> T (Trans s a ou s')"
        and CONSUME: "consume (Trans s a ou s') vl vl'"

      have ph': "phase s' cid \<ge> subPH"
        by (smt STET ph phase_increases)

      have pid': "PID \<in>\<in> paperIDs s' cid" using pid STET
        by (metis paperIDs_mono)

      {
        fix s1 vl1
        assume "phase s' cid \<noteq> subPH"
        hence "\<Delta>e s' vl' s1 vl1"
          unfolding \<Delta>e_def
          using STET CONSUME vl ph
          apply (cases a)
            subgoal for x1 apply(cases x1) apply(auto simp: c_defs) .
            subgoal for x2 apply(cases x2) apply(auto simp: u_defs consume_def pid) apply metis .
            subgoal for x3 apply(cases x3) apply(auto simp: uu_defs) .
            by simp_all
      } note \<Delta>e=this

      obtain s1' ou' where STET': "step s1 a = (ou',s1')" and s's1': "eqButPID s' s1'"
        using eqButPID_step[OF ss1 STET]
        by fastforce

      from eqButPID_step_\<phi>[OF ss1 STET STET']
      have \<phi>_eq: "\<phi> (Trans s1 a ou' s1') = \<phi> (Trans s a ou s')" by simp

      show ?case (is "?match \<or> ?ignore")
      proof (cases "\<phi> (Trans s a ou s')")
        case True note \<phi>=this

        then obtain cid' uid p where
          a[simp]: "a=Uact (uPaperC cid' uid p PID (hd vl))" "ou=outOK" using CONSUME
          by (cases "(Trans s a ou s')" rule: f.cases) (auto simp add: consume_def vl)

        from STET pid have [simp]: "cid'=cid"
          by (simp add: u_defs paperIDs_equals[OF rs])

        from \<phi>_step_eqButPID[OF \<phi> STET] have ss': "eqButPID s s'" .

        have n\<gamma>: "\<not>\<gamma> (Trans s a ou s')"
          using T_\<phi>_\<gamma>[OF rsT STET] by simp

        have ph': "phase s' cid = subPH"
          using STET by (auto simp add: u_defs)

        show ?thesis proof (cases "length vl = 1")
          case True hence [simp]: "vl=[v1]" using vlvl1 by (cases vl) simp_all
          from CONSUME have [simp]: "vl'=[]" by (simp add: consume_def \<phi>)

          from STET STET' have [simp]: "s1'=s'"
          using eqButPID_step_eq ss1 a by blast

          have ?match proof
            show "validTrans (Trans s1 a ou' s1')" using STET' by simp
            show "consume (Trans s1 a ou' s1') vl1 []"
              using \<phi> \<phi>_eq CONSUME
              by (simp add: consume_def)
            show "\<gamma> (Trans s a ou s') = \<gamma> (Trans s1 a ou' s1')" by simp
            show "\<gamma> (Trans s a ou s') \<Longrightarrow> g (Trans s a ou s') = g (Trans s1 a ou' s1')"
              using n\<gamma> by simp
            have "\<Delta>3 s' vl' s1' []"
              unfolding \<Delta>3_def
              using ph' pid'
              by force
            thus "disjAll {\<Delta>2, \<Delta>3, \<Delta>e} s' vl' s1' []" by simp
          qed
          thus ?thesis by simp
        next
          case False then obtain v where [simp]: "vl=v#vl'" "vl'\<noteq>[]"
            using CONSUME vl by (cases vl) (simp_all add: consume_def)
          have ?ignore
          proof
            show "\<not> \<gamma> (Trans s a ou s')" by (rule n\<gamma>)
            have "\<Delta>2 s' vl' s1 vl1"
              unfolding \<Delta>2_def B_def
              using vlvl1 ph' pid' eqButPID_trans[OF eqButPID_sym[OF ss'] ss1]
              by auto
            thus "disjAll {\<Delta>2, \<Delta>3, \<Delta>e} s' vl' s1 vl1" by simp
          qed
          thus ?thesis by simp
        qed
      next
        case False note \<phi>=this
        with CONSUME have [simp]: "vl'=vl" by (simp add: consume_def)

        have ?match proof
          show "validTrans (Trans s1 a ou' s1')" using STET' by simp
          show "consume (Trans s1 a ou' s1') vl1 vl1" using \<phi>
            by (simp add: consume_def \<phi>_eq)
          show "\<gamma> (Trans s a ou s') = \<gamma> (Trans s1 a ou' s1')" by simp
          show "\<gamma> (Trans s a ou s') \<Longrightarrow> g (Trans s a ou s') = g (Trans s1 a ou' s1')"
            using eqButPID_step_out[OF ss1 STET STET' rsT rs1 pid ph]
            by simp
          show "disjAll {\<Delta>2, \<Delta>3, \<Delta>e} s' vl' s1' vl1"
          proof (cases "phase s' cid = subPH")
            case True
            hence "\<Delta>2 s' vl' s1' vl1"
              unfolding \<Delta>2_def B_def
              using eqButPID_step[OF ss1 STET STET']
              using ph' pid' vl vl1 vlvl1 by auto
            thus ?thesis by simp
          next
            case False
            hence "\<Delta>e s' vl' s1' vl1" using \<Delta>e by simp
            thus ?thesis by simp
          qed
        qed
        thus ?thesis by simp
      qed
    qed
    thus ?thesis using vl vl1 by simp
  qed
qed

lemma unwind_cont_\<Delta>3: "unwind_cont \<Delta>3 {\<Delta>3,\<Delta>e}"
proof (rule, goal_cases)
  case (1 s vl s1 vl1)
  assume rsT: "reachNT s" and rs1: "reach s1" and \<Delta>: "\<Delta>3 s vl s1 vl1"
  thm \<Delta>3_def
  then obtain cid where [simp]: "s1=s" "vl=[]" "vl1=[]"
    and pid: "PID \<in>\<in> paperIDs s cid"
    unfolding \<Delta>3_def by auto

  thus ?case (is "_ \<or> (_ \<and> ?react)")
  proof -
    have "?react"
    proof (rule, goal_cases)
      case (1 a ou s' vl')
      assume STET: "step s a = (ou, s')" and NT: "\<not> T (Trans s a ou s')"
        and CONSUME: "consume (Trans s a ou s') vl vl'"
      have \<Delta>3: "\<Delta>3 s' vl' s' vl'" and [simp]: "vl'=[]"
        using CONSUME paperIDs_mono[OF STET pid]
        unfolding \<Delta>3_def
        by (auto simp add: consume_def)
      thus ?case (is "?match \<or> ?ignore")
      proof -
        have ?match
          apply (rule matchI[of s1 a ou s' vl1 vl1])
          using STET CONSUME \<Delta>3 by simp_all
        thus ?thesis by simp
      qed
    qed
    thus ?thesis by simp
  qed
qed

definition K1exit where
"K1exit s \<equiv> \<exists>cid. phase s cid > subPH \<and> PID \<in>\<in> paperIDs s cid"

lemma invarNT_K1exit: "invarNT K1exit"
  unfolding invarNT_def
  apply (safe dest!: reachNT_reach)
  subgoal for _ a apply(cases a)
    subgoal for x1 apply(cases x1) apply (auto simp: c_defs K1exit_def) .
    subgoal for x2 apply(cases x2) apply (auto simp: u_defs K1exit_def paperIDs_equals,force+) .
    subgoal for x3 apply(cases x3) apply (auto simp: uu_defs K1exit_def) .
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
