theory Post
imports "../Observation_Setup" Post_Value_Setup
begin

subsection \<open>Declassification bound\<close>


fun T :: "(state,act,out) trans \<Rightarrow> bool" where "T _ = False"

text \<open>\label{sec:post-bound}
The bound may dynamically change from closed (\<open>B\<close>) to open (\<open>BO\<close>) access to the
confidential information (or vice versa) when the openness predicate changes value.
The bound essentially relates arbitrary value sequences in the closed phase (i.e.~observers
learn nothing about the updates during that phase) and identical value sequences in the open phase
(i.e.~observers may learn everything about the updates during that phase);
when transitioning from a closed to an open access window (\<open>B_BO\<close> below),
the last update in the closed phase, i.e.~the current version of the post,
is also declassified in addition to subsequent updates.
This formalizes the ``while-or-last-before'' scheme in the informal description of the
confidentiality property.
Moreover, the empty value sequence is treated specially in order to capture harmless cases
where the observers may deduce that no secret updates have occurred,
e.g.~if the system has not been initialized yet.
See \<^cite>\<open>\<open>Section 3.4\<close> in "cosmed-jar2018"\<close> for a detailed discussion of the bound.\<close>

inductive B :: "value list \<Rightarrow> value list \<Rightarrow> bool"
and BO :: "value list \<Rightarrow> value list \<Rightarrow> bool"
where
 B_TVal[simp,intro!]:
  "(pstl = [] \<longrightarrow> pstl1 = []) \<Longrightarrow> B (map TVal pstl) (map TVal pstl1)"
|B_BO[intro]:
  "BO vl vl1 \<Longrightarrow> (pstl = [] \<longleftrightarrow> pstl1 = []) \<Longrightarrow> (pstl \<noteq> [] \<Longrightarrow> last pstl = last pstl1) \<Longrightarrow>
   B (map TVal pstl  @ OVal True # vl)
     (map TVal pstl1 @ OVal True # vl1)"
(*  *)
|BO_TVal[simp,intro!]:
  "BO (map TVal pstl) (map TVal pstl)"
|BO_B[intro]:
  "B vl vl1 \<Longrightarrow>
   BO (map TVal pstl @ OVal False # vl) (map TVal pstl @ OVal False # vl1)"

lemma B_not_Nil: "B vl vl1 \<Longrightarrow> vl = [] \<Longrightarrow> vl1 = []"
by(auto elim: B.cases)

lemma B_OVal_True:
assumes "B (OVal True # vl') vl1"
shows "\<exists> vl1'. BO vl' vl1' \<and> vl1 = OVal True # vl1'"
using assms apply(auto elim!: B.cases)
by (metis append_self_conv2 hd_append list.map_disc_iff list.map_sel(1) list.sel(1)
       list.sel(3) value.distinct(1))+

no_notation relcomp (infixr "O" 75)

interpretation BD_Security_IO where
istate = istate and step = step and
\<phi> = \<phi> and f = f and \<gamma> = \<gamma> and g = g and T = T and B = B
done


subsection \<open>Unwinding proof\<close>

(* Key lemma: *)
lemma eqButPID_step_\<gamma>_out:
assumes ss1: "eqButPID s s1"
and step: "step s a = (ou,s')" and step1: "step s1 a = (ou1,s1')"
and op: "\<not> open s"
and sT: "reachNT s" and s1: "reach s1"
and \<gamma>: "\<gamma> (Trans s a ou s')"
shows "ou = ou1"
proof-
  note [simp] = all_defs
                open_defs
  note s = reachNT_reach[OF sT]
  note willUse =
  step step1 \<gamma>
  not_open_eqButPID[OF op ss1]
  reach_visPost[OF s]
  eqButPID_stateSelectors[OF ss1]
  eqButPID_actions[OF ss1]
  eqButPID_not_PID[OF ss1]
  {fix uid p pid assume "a = Ract (rPost uid p pid)"
   hence ?thesis using willUse
   by (cases "pid = PID") fastforce+
  } note intCase1 = this
  show ?thesis
  proof (cases a)
    case (Sact x1)
    then show ?thesis using intCase1 willUse by (cases x1) auto
  next
    case (Cact x2)
    then show ?thesis using intCase1 willUse by (cases x2) auto
  next
    case (Dact x3)
    then show ?thesis using intCase1 willUse by (cases x3) auto
  next
    case (Uact x4)
    then show ?thesis using intCase1 willUse by (cases x4) auto
  next
    case (Ract x5)
    then show ?thesis using intCase1 willUse by (cases x5) auto
  next
    case (Lact x6)
    then show ?thesis using intCase1 willUse by (cases x6) auto
  qed
qed

(* Key lemma: *)
lemma eqButPID_step_eq:
assumes ss1: "eqButPID s s1"
and a: "a = Uact (uPost uid p PID pst)" "ou = outOK"
and step: "step s a = (ou, s')" and step1: "step s1 a = (ou', s1')"
shows "s' = s1'"
using ss1 step step1
using eqButPID_stateSelectors[OF ss1] eqButPID_setPost[OF ss1]
unfolding a by (auto simp: u_defs)

definition \<Delta>0 :: "state \<Rightarrow> value list \<Rightarrow> state \<Rightarrow> value list \<Rightarrow> bool" where
"\<Delta>0 s vl s1 vl1 \<equiv>
 \<not> PID \<in>\<in> postIDs s \<and>
 s = s1 \<and> B vl vl1"

definition \<Delta>1 :: "state \<Rightarrow> value list \<Rightarrow> state \<Rightarrow> value list \<Rightarrow> bool" where
"\<Delta>1 s vl s1 vl1 \<equiv>
 PID \<in>\<in> postIDs s \<and>
 (\<exists> pstl pstl1. (pstl = [] \<longrightarrow> pstl1 = []) \<and> vl = map TVal pstl \<and> vl1 = map TVal pstl1) \<and>
 eqButPID s s1 \<and> \<not> open s"

definition \<Delta>2 :: "state \<Rightarrow> value list \<Rightarrow> state \<Rightarrow> value list \<Rightarrow> bool" where
"\<Delta>2 s vl s1 vl1 \<equiv>
 PID \<in>\<in> postIDs s \<and>
 (\<exists> pstl. vl = map TVal pstl \<and> vl1 = map TVal pstl) \<and>
 s = s1 \<and> open s"

definition \<Delta>31 :: "state \<Rightarrow> value list \<Rightarrow> state \<Rightarrow> value list \<Rightarrow> bool" where
"\<Delta>31 s vl s1 vl1 \<equiv>
 PID \<in>\<in> postIDs s \<and>
 (\<exists> pstl pstl1 vll vll1.
    BO vll vll1 \<and> pstl \<noteq> [] \<and> pstl1 \<noteq> [] \<and> last pstl = last pstl1 \<and>
    vl = map TVal pstl @ OVal True # vll \<and> vl1 = map TVal pstl1 @ OVal True # vll1) \<and>
 eqButPID s s1 \<and> \<not> open s"

definition \<Delta>32 :: "state \<Rightarrow> value list \<Rightarrow> state \<Rightarrow> value list \<Rightarrow> bool" where
"\<Delta>32 s vl s1 vl1 \<equiv>
 PID \<in>\<in> postIDs s \<and>
 (\<exists> vll vll1.
    BO vll vll1 \<and>
    vl = OVal True # vll \<and> vl1 = OVal True # vll1) \<and>
 s = s1 \<and> \<not> open s"

definition \<Delta>4 :: "state \<Rightarrow> value list \<Rightarrow> state \<Rightarrow> value list \<Rightarrow> bool" where
"\<Delta>4 s vl s1 vl1 \<equiv>
 PID \<in>\<in> postIDs s \<and>
 (\<exists> pstl vll vll1.
    B vll vll1 \<and>
    vl = map TVal pstl @ OVal False # vll \<and> vl1 = map TVal pstl @ OVal False # vll1) \<and>
 s = s1 \<and> open s"

lemma istate_\<Delta>0:
assumes B: "B vl vl1"
shows "\<Delta>0 istate vl istate vl1"
using assms unfolding \<Delta>0_def istate_def by auto

lemma unwind_cont_\<Delta>0: "unwind_cont \<Delta>0 {\<Delta>0,\<Delta>1,\<Delta>2,\<Delta>31,\<Delta>32,\<Delta>4}"
proof(rule, simp)
  let ?\<Delta> = "\<lambda>s vl s1 vl1. \<Delta>0 s vl s1 vl1 \<or>
                           \<Delta>1 s vl s1 vl1 \<or> \<Delta>2 s vl s1 vl1 \<or>
                           \<Delta>31 s vl s1 vl1 \<or> \<Delta>32 s vl s1 vl1 \<or> \<Delta>4 s vl s1 vl1"
  fix s s1 :: state and vl vl1 :: "value list"
  assume rsT: "reachNT s" and rs1: "reach s1" and "\<Delta>0 s vl s1 vl1"
  hence rs: "reach s" and ss1: "s1 = s" and B: "B vl vl1" and PID: "\<not> PID \<in>\<in> postIDs s"
  using reachNT_reach unfolding \<Delta>0_def by auto
  have vlvl1: "vl = [] \<Longrightarrow> vl1 = []" using B_not_Nil B by auto
  have op: "\<not> open s" using PID unfolding open_defs by auto
  show "iaction ?\<Delta> s vl s1 vl1 \<or>
        ((vl = [] \<longrightarrow> vl1 = []) \<and> reaction ?\<Delta> s vl s1 vl1)" (is "?iact \<or> (_ \<and> ?react)")
  proof-
    have ?react proof
      fix a :: act and ou :: out and s' :: state and vl'
      let ?trn = "Trans s a ou s'"  let ?trn1 = "Trans s1 a ou s'"
      assume step: "step s a = (ou, s')" and T: "\<not> T ?trn" and c: "consume ?trn vl vl'"
      show "match ?\<Delta> s s1 vl1 a ou s' vl' \<or> ignore ?\<Delta> s s1 vl1 a ou s' vl'" (is "?match \<or> ?ignore")
      proof-
        have ?match proof(cases "\<exists> uid p text. a = Cact (cPost uid p PID text) \<and> ou = outOK")
          case True
          then obtain uid p "text" where a: "a = Cact (cPost uid p PID text)" and ou: "ou = outOK" by auto
          have PID': "PID \<in>\<in> postIDs s'"
          using step PID unfolding a ou by (auto simp: c_defs)
          show ?thesis proof(cases "uid \<in> UIDs \<or> (\<exists> uid' \<in> UIDs. uid' \<in>\<in> userIDs s \<and> (uid' \<in>\<in> friendIDs s uid))")
            case True note uid = True
            have op': "open s'" using uid using step PID' unfolding a ou by (auto simp: c_defs open_defs)
            have \<phi>: "\<phi> ?trn" using op op' unfolding \<phi>_def2[OF step] by simp
            then obtain v where vl: "vl = v # vl'" and f: "f ?trn = v"
            using c unfolding consume_def \<phi>_def2 by(cases vl) auto
            have v: "v = OVal True" using f op op' unfolding a by simp
            then obtain vl1' where BO': "BO vl' vl1'" and vl1: "vl1 = OVal True # vl1'"
            using B_OVal_True B unfolding vl v by auto
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
                case (BO_TVal pstl)
                hence "\<Delta>2 s' vl' s' vl1'" using PID' op' unfolding \<Delta>2_def by auto
                thus ?thesis by simp
              next
                case (BO_B vll vll1 pstl)
                hence "\<Delta>4 s' vl' s' vl1'" using PID' op' unfolding \<Delta>4_def by auto
                thus ?thesis by simp
              qed
            qed
          next
            case False note uid = False
            have op': "\<not> open s'" using step op uid unfolding open_defs a
              by (auto simp add: c_defs reach_not_postIDs_vis_FriendV rs)
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
              show "?\<Delta> s' vl' s' vl1" using B proof(cases rule: B.cases)
                case (B_TVal pstl)
                hence "\<Delta>1 s' vl' s' vl1" using PID' op' unfolding \<Delta>1_def vl' by auto
                thus ?thesis by simp
              next
                case (B_BO vll vll1 pstl pstl1)
                show ?thesis
                proof(cases "pstl \<noteq> [] \<and> pstl1 \<noteq> []")
                  case True
                  hence "\<Delta>31 s' vl' s' vl1" using B_BO PID' op' unfolding \<Delta>31_def vl' by auto
                  thus ?thesis by simp
                next
                  case False
                  hence "\<Delta>32 s' vl' s' vl1" using B_BO PID' op' unfolding \<Delta>32_def vl' by auto
                  thus ?thesis by simp
                qed
              qed
            qed
          qed
        next
          case False note a = False
          have op': "\<not> open s'"
            using a step PID op unfolding open_defs
            by (cases a) (auto elim: step_elims simp: all_defs)
          have \<phi>: "\<not> \<phi> ?trn" using PID step op op' unfolding \<phi>_def2[OF step] by (auto simp: u_defs)
          hence vl': "vl' = vl" using c unfolding consume_def by simp
          have PID': "\<not> PID \<in>\<in> postIDs s'"
            using step PID a
            by (cases a) (auto elim: step_elims simp: all_defs)
          show ?thesis proof
            show "validTrans ?trn1" unfolding ss1 using step by simp
          next
            show "consume ?trn1 vl1 vl1" using \<phi> unfolding consume_def ss1 by auto
          next
            show "\<gamma> ?trn = \<gamma> ?trn1" unfolding ss1 by simp
          next
            assume "\<gamma> ?trn" thus "g ?trn = g ?trn1" unfolding ss1 by simp
          next
            have "\<Delta>0 s' vl' s' vl1" using a B PID' unfolding \<Delta>0_def vl' by simp
            thus "?\<Delta> s' vl' s' vl1" by simp
          qed
        qed
        thus ?thesis by simp
      qed
    qed
  thus ?thesis using vlvl1 by simp
  qed
qed

lemma unwind_cont_\<Delta>1: "unwind_cont \<Delta>1 {\<Delta>1}"
proof(rule, simp)
  let ?\<Delta> = "\<lambda>s vl s1 vl1. \<Delta>1 s vl s1 vl1"
  fix s s1 :: state and vl vl1 :: "value list"
  assume rsT: "reachNT s" and rs1: "reach s1" and "\<Delta>1 s vl s1 vl1"
  then obtain pstl pstl1 where
  t: "pstl = [] \<longrightarrow> pstl1 = []"
  and vl: "vl = map TVal pstl" and vl1: "vl1 = map TVal pstl1"
  and rs: "reach s" and ss1: "eqButPID s s1" and op: "\<not> open s" and PID: "PID \<in>\<in> postIDs s"
  using reachNT_reach unfolding \<Delta>1_def by auto
  have vlvl1: "vl = [] \<Longrightarrow> vl1 = []" using t unfolding vl vl1 by auto
  have PID1: "PID \<in>\<in> postIDs s1" using eqButPID_stateSelectors[OF ss1] PID by auto
  have own: "owner s PID \<in> set (userIDs s)" using reach_owner_userIDs[OF rs PID] .
  hence own1: "owner s1 PID \<in> set (userIDs s1)" using eqButPID_stateSelectors[OF ss1] by auto
  have op1: "\<not> open s1" using op ss1 eqButPID_open by auto
  show "iaction ?\<Delta> s vl s1 vl1 \<or>
        ((vl = [] \<longrightarrow> vl1 = []) \<and> reaction ?\<Delta> s vl s1 vl1)" (is "?iact \<or> (_ \<and> ?react)")
  proof(cases pstl1)
    case (Cons text1 pstll1) note pstl1 = Cons
    define uid where uid: "uid \<equiv> owner s PID"  define p where p: "p \<equiv> pass s uid"
    define a1 where a1: "a1 \<equiv> Uact (uPost uid p PID text1)"
    have uid1: "uid = owner s1 PID" and p1: "p = pass s1 uid" unfolding uid p
    using eqButPID_stateSelectors[OF ss1] by auto
    obtain ou1 s1' where step1: "step s1 a1 = (ou1, s1')" by(cases "step s1 a1") auto
    have ou1: "ou1 = outOK" using step1 PID1 own1 unfolding a1 uid1 p1 by (auto simp: u_defs)
    have op1': "\<not> open s1'" using step1 op1 unfolding a1 ou1 open_defs by (auto simp: u_defs)
    have uid: "uid \<notin> UIDs" unfolding uid using op PID own unfolding open_defs by auto
    let ?trn1 = "Trans s1 a1 ou1 s1'"
    have ?iact proof
      show "step s1 a1 = (ou1, s1')" using step1 .
    next
      show \<phi>: "\<phi> ?trn1" unfolding \<phi>_def2[OF step1] a1 ou1 by simp
      show "consume ?trn1 vl1 (map TVal pstll1)"
      using \<phi> unfolding vl1 consume_def pstl1 a1 by auto
    next
      show "\<not> \<gamma> ?trn1" using uid unfolding a1 by auto
    next
      have "eqButPID s1 s1'" using Uact_uPost_step_eqButPID[OF _ step1] a1 by auto
      hence ss1': "eqButPID s s1'" using eqButPID_trans ss1 by blast
      show "?\<Delta> s vl s1' (map TVal pstll1)" using PID op t ss1' unfolding \<Delta>1_def vl pstl1 by auto
    qed
    thus ?thesis by simp
  next
    case Nil note pstl1 = Nil
    have ?react proof
      fix a :: act and ou :: out and s' :: state and vl'
      let ?trn = "Trans s a ou s'"
      assume step: "step s a = (ou, s')" and T: "\<not> T ?trn" and c: "consume ?trn vl vl'"
      have PID': "PID \<in>\<in> postIDs s'" using reach_postIDs_persist[OF PID step] .
      obtain ou1 s1' where step1: "step s1 a = (ou1, s1')" by(cases "step s1 a") auto
      let ?trn1 = "Trans s1 a ou1 s1'"
      show "match ?\<Delta> s s1 vl1 a ou s' vl' \<or> ignore ?\<Delta> s s1 vl1 a ou s' vl'" (is "?match \<or> ?ignore")
      proof(cases "\<exists> uid p textt. a = Uact (uPost uid p PID textt) \<and> ou = outOK")
        case True then obtain uid p textt where
        a: "a = Uact (uPost uid p PID textt)" and ou: "ou = outOK" by auto
        hence \<phi>: "\<phi> ?trn" unfolding \<phi>_def2[OF step] by auto
        then obtain "text" pstl' where pstl: "pstl = text # pstl'" and f: "f ?trn = TVal text"
        and vl': "vl' = map TVal pstl'"
        using c unfolding consume_def \<phi>_def2 vl by (cases pstl) auto
        have textt: "textt = text" using f unfolding a by auto
        have uid: "uid \<notin> UIDs" using step op PID unfolding a ou open_defs by (auto simp: u_defs)
        have "eqButPID s s'" using Uact_uPost_step_eqButPID[OF a step] by auto
        hence s's1: "eqButPID s' s1" using eqButPID_sym eqButPID_trans ss1 by blast
        have op': "\<not> open s'" using step PID' op unfolding a ou open_defs by (auto simp: u_defs)
        have ?ignore proof
          show "\<not> \<gamma> ?trn" unfolding a using uid by auto
        next
          show "?\<Delta> s' vl' s1 vl1" using PID' s's1 op' unfolding \<Delta>1_def vl' vl1 pstl1 by auto
        qed
        thus ?thesis by simp
      next
        case False note a = False
        {assume \<phi>: "\<phi> ?trn"
         then obtain "text" pstl' where pstl: "pstl = text # pstl'" and f: "f ?trn = TVal text"
         and vl': "vl' = map TVal pstl'" using c unfolding consume_def vl by (cases pstl) auto
         have False using f a \<phi> by (cases ?trn rule: \<phi>.cases) auto
        }
        hence \<phi>: "\<not> \<phi> ?trn" by auto
        have op': "\<not> open s'" using a op \<phi> unfolding \<phi>_def2[OF step] by auto
        have vl': "vl' = vl" using c \<phi> unfolding consume_def by auto
        have s's1': "eqButPID s' s1'" using eqButPID_step[OF ss1 step step1] .
        have op1': "\<not> open s1'" using op' eqButPID_open[OF s's1'] by simp
        have "\<And> uid p text. e_updatePost s1 uid p PID text \<longleftrightarrow> e_updatePost s uid p PID text"
        using eqButPID_stateSelectors[OF ss1] unfolding u_defs by auto
        hence ou1: "\<And> uid p text. a = Uact (uPost uid p PID text) \<Longrightarrow> ou1 = ou"
        using step step1 by auto
        hence \<phi>1: "\<not> \<phi> ?trn1" using a op1 op1' unfolding \<phi>_def2[OF step1] by auto
        have ?match proof
          show "validTrans ?trn1" using step1 by simp
        next
          show "consume ?trn1 vl1 vl1" using \<phi>1 unfolding consume_def by simp
        next
          show "\<gamma> ?trn = \<gamma> ?trn1" unfolding ss1 by simp
        next
          assume "\<gamma> ?trn"
          hence "ou1 = ou" using eqButPID_step_\<gamma>_out[OF ss1 step step1 op rsT rs1] by simp
          thus "g ?trn = g ?trn1" by simp
        next
          show "?\<Delta> s' vl' s1' vl1" using s's1' op' PID' unfolding \<Delta>1_def vl' vl vl1 pstl1 by auto
        qed
      thus ?thesis by simp
      qed
    qed
    thus ?thesis using vlvl1 by simp
  qed
qed

lemma unwind_cont_\<Delta>2: "unwind_cont \<Delta>2 {\<Delta>2}"
proof(rule, simp)
  let ?\<Delta> = "\<lambda>s vl s1 vl1. \<Delta>2 s vl s1 vl1"
  fix s s1 :: state and vl vl1 :: "value list"
  assume rsT: "reachNT s" and rs1: "reach s1" and "\<Delta>2 s vl s1 vl1"
  then obtain pstl where
  vl: "vl = map TVal pstl" and vl1: "vl1 = map TVal pstl"
  and rs: "reach s" and ss1: "s1 = s" and op: "open s" and PID: "PID \<in>\<in> postIDs s"
  using reachNT_reach unfolding \<Delta>2_def by fastforce
  have vlvl1: "vl = [] \<Longrightarrow> vl1 = []" unfolding vl vl1 by auto
  have own: "owner s PID \<in> set (userIDs s)" using reach_owner_userIDs[OF rs PID] .
  show "iaction ?\<Delta> s vl s1 vl1 \<or>
        ((vl = [] \<longrightarrow> vl1 = []) \<and> reaction ?\<Delta> s vl s1 vl1)" (is "?iact \<or> (_ \<and> ?react)")
  proof-
    have ?react proof
      fix a :: act and ou :: out and s' :: state and vl'
      let ?trn = "Trans s a ou s'"  let ?trn1 = "Trans s1 a ou s'"
      assume step: "step s a = (ou, s')" and T: "\<not> T ?trn" and c: "consume ?trn vl vl'"
      have PID': "PID \<in>\<in> postIDs s'" using reach_postIDs_persist[OF PID step] .
      {assume op': "\<not> open s'"
       hence \<phi>: "\<phi> ?trn" using op unfolding \<phi>_def2[OF step] by simp
       then obtain "text" pstl' where pstl: "pstl = text # pstl'" and f: "f ?trn = TVal text" and vl': "vl' = map TVal pstl'"
       using c unfolding consume_def \<phi>_def2 vl by(cases pstl) auto
       obtain uid p where a: "a = Uact (uPost uid p PID text)" and ou: "ou = outOK"
         using f \<phi> by (cases ?trn rule: \<phi>.cases) auto
       have False using step op op' PID PID' unfolding a ou open_defs by (auto simp: u_defs)
      }
      hence op': "open s'" by auto
      show "match ?\<Delta> s s1 vl1 a ou s' vl' \<or> ignore ?\<Delta> s s1 vl1 a ou s' vl'" (is "?match \<or> ?ignore")
      proof-
        have ?match proof(cases "\<phi> ?trn")
          case True note \<phi> = True
          then obtain "text" pstl' where pstl: "pstl = text # pstl'" and f: "f ?trn = TVal text" and vl': "vl' = map TVal pstl'"
          using c unfolding consume_def \<phi>_def2 vl by(cases pstl) auto
          obtain uid p textt where a: "a = Uact (uPost uid p PID textt)" and ou: "ou = outOK"
          using \<phi> op op' unfolding \<phi>_def2[OF step] by auto
          have textt: "textt = text" using f unfolding a by simp
          show ?thesis proof
            show "validTrans ?trn1" unfolding ss1 using step by simp
          next
            show "consume ?trn1 vl1 vl'" using \<phi> unfolding ss1 consume_def vl1 vl vl' pstl f by auto
          next
            show "\<gamma> ?trn = \<gamma> ?trn1" unfolding ss1 by simp
          next
            assume "\<gamma> ?trn" thus "g ?trn = g ?trn1" unfolding ss1 by simp
          next
            show "?\<Delta> s' vl' s' vl'" using PID' op' unfolding \<Delta>2_def vl1 vl' vl by auto
          qed
        next
          case False note \<phi> = False
          hence vl': "vl' = vl" using c unfolding consume_def by auto
          show ?thesis proof
            show "validTrans ?trn1" unfolding ss1 using step by simp
          next
            show "consume ?trn1 vl1 vl" using \<phi> unfolding ss1 consume_def vl1 vl vl' by auto
          next
            show "\<gamma> ?trn = \<gamma> ?trn1" unfolding ss1 by simp
          next
            assume "\<gamma> ?trn" thus "g ?trn = g ?trn1" unfolding ss1 by simp
          next
            show "?\<Delta> s' vl' s' vl" using PID' op' unfolding \<Delta>2_def vl1 vl' vl by auto
          qed
        qed
      thus ?thesis by simp
      qed
    qed
  thus ?thesis using vlvl1 by simp
  qed
qed

lemma unwind_cont_\<Delta>31: "unwind_cont \<Delta>31 {\<Delta>31,\<Delta>32}"
proof(rule, simp)
  let ?\<Delta> = "\<lambda>s vl s1 vl1. \<Delta>31 s vl s1 vl1 \<or> \<Delta>32 s vl s1 vl1"
  fix s s1 :: state and vl vl1 :: "value list"
  assume rsT: "reachNT s" and rs1: "reach s1" and "\<Delta>31 s vl s1 vl1"
  then obtain pstl pstl1 vll vll1 where BO: "BO vll vll1" and
  t: "pstl \<noteq> []" "pstl1 \<noteq> []" "last pstl = last pstl1"
  and vl: "vl = map TVal pstl @ OVal True # vll"
  and vl1: "vl1 = map TVal pstl1 @ OVal True # vll1"
  and rs: "reach s" and ss1: "eqButPID s s1" and op: "\<not> open s" and PID: "PID \<in>\<in> postIDs s"
  using reachNT_reach unfolding \<Delta>31_def by auto
  have vlvl1: "vl = [] \<Longrightarrow> vl1 = []" using t unfolding vl vl1 by auto
  have PID1: "PID \<in>\<in> postIDs s1" using eqButPID_stateSelectors[OF ss1] PID by auto
  have own: "owner s PID \<in> set (userIDs s)" using reach_owner_userIDs[OF rs PID] .
  hence own1: "owner s1 PID \<in> set (userIDs s1)" using eqButPID_stateSelectors[OF ss1] by auto
  have op1: "\<not> open s1" using op ss1 eqButPID_open by auto
  show "iaction ?\<Delta> s vl s1 vl1 \<or>
        ((vl = [] \<longrightarrow> vl1 = []) \<and> reaction ?\<Delta> s vl s1 vl1)" (is "?iact \<or> (_ \<and> ?react)")
  proof(cases "length pstl1 \<ge> 2" )
    case True then obtain text1 pstll1 where pstl1: "pstl1 = text1 # pstll1"
    and pstll1: "pstll1 \<noteq> []" by (cases pstl1) fastforce+
    define uid where uid: "uid \<equiv> owner s PID"  define p where p: "p \<equiv> pass s uid"
    define a1 where a1: "a1 \<equiv> Uact (uPost uid p PID text1)"
    have uid1: "uid = owner s1 PID" and p1: "p = pass s1 uid" unfolding uid p
    using eqButPID_stateSelectors[OF ss1] by auto
    obtain ou1 s1' where step1: "step s1 a1 = (ou1, s1')" by(cases "step s1 a1") auto
    have ou1: "ou1 = outOK" using step1 PID1 own1 unfolding a1 uid1 p1 by (auto simp: u_defs)
    have op1': "\<not> open s1'" using step1 op1 unfolding a1 ou1 open_defs by (auto simp: u_defs)
    have uid: "uid \<notin> UIDs" unfolding uid using op PID own unfolding open_defs by auto
    let ?trn1 = "Trans s1 a1 ou1 s1'"
    have ?iact proof
      show "step s1 a1 = (ou1, s1')" using step1 .
    next
      show \<phi>: "\<phi> ?trn1" unfolding \<phi>_def2[OF step1] a1 ou1 by simp
      show "consume ?trn1 vl1 (map TVal pstll1 @ OVal True # vll1)"
      using \<phi> unfolding vl1 consume_def pstl1 a1 by auto
    next
      show "\<not> \<gamma> ?trn1" using uid unfolding a1 by auto
    next
      have "eqButPID s1 s1'" using Uact_uPost_step_eqButPID[OF _ step1] a1 by auto
      hence ss1': "eqButPID s s1'" using eqButPID_trans ss1 by blast
      have "\<Delta>31 s vl s1' (map TVal pstll1 @ OVal True # vll1)"
      using BO PID op t ss1' pstll1 unfolding \<Delta>31_def vl pstl1 by auto
      thus "?\<Delta> s vl s1' (map TVal pstll1 @ OVal True # vll1)" by simp
    qed
    thus ?thesis by simp
  next
    case False then obtain text1 where pstl1: "pstl1 = [text1]" using t
    by (cases pstl1) (auto simp: Suc_leI)
    have ?react proof
      fix a :: act and ou :: out and s' :: state and vl'
      let ?trn = "Trans s a ou s'"
      assume step: "step s a = (ou, s')" and T: "\<not> T ?trn" and c: "consume ?trn vl vl'"
      obtain ou1 s1' where step1: "step s1 a = (ou1, s1')" by(cases "step s1 a") auto
      let ?trn1 = "Trans s1 a ou1 s1'"
      show "match ?\<Delta> s s1 vl1 a ou s' vl' \<or> ignore ?\<Delta> s s1 vl1 a ou s' vl'" (is "?match \<or> ?ignore")
      proof(cases "\<exists> uid p textt. a = Uact (uPost uid p PID textt) \<and> ou = outOK")
        case True then obtain uid p textt where
        a: "a = Uact (uPost uid p PID textt)" and ou: "ou = outOK" by auto
        hence \<phi>: "\<phi> ?trn" unfolding \<phi>_def2[OF step] by auto
        then obtain "text" pstl' where pstl: "pstl = text # pstl'" and f: "f ?trn = TVal text"
        and vl': "vl' = map TVal pstl' @ OVal True # vll"
        using c t unfolding consume_def \<phi>_def2 vl by (cases pstl) auto
        have textt: "textt = text" using f unfolding a by auto
        have uid: "uid \<notin> UIDs" using step op PID unfolding a ou open_defs by (auto simp: u_defs)
        have "eqButPID s s'" using Uact_uPost_step_eqButPID[OF a step] by auto
        hence s's1: "eqButPID s' s1" using eqButPID_sym eqButPID_trans ss1 by blast
        have s's1': "s' = s1'" using step step1 ss1 eqButPID_step_eq unfolding a ou by blast
        have "e_updatePost s' uid p PID textt" using step unfolding a ou by(auto simp: u_defs)
        hence \<phi>1: "\<phi> ?trn1" using step1 unfolding a \<phi>_def2[OF step1] s's1' by auto
        hence f1: "f ?trn1 = TVal text" unfolding a textt by simp
        show ?thesis proof(cases "pstl' = []")
          case True note pstl' = True
          hence pstl: "pstl = [text]" unfolding pstl by auto
          hence text1: "text1 = text" using pstl pstl1 t by auto
          have PID': "PID \<in>\<in> postIDs s'" using reach_postIDs_persist[OF PID step] .
          have op': "\<not> open s'" using step PID' op unfolding a ou open_defs by (auto simp: u_defs)
          have ou1: "ou1 = outOK" using \<phi>1 op1 op' unfolding \<phi>_def2[OF step1] s's1' by auto
          have ?match proof
            show "validTrans ?trn1" using step1 by simp
          next
            show "consume ?trn1 vl1 (OVal True # vll1)"
            using \<phi>1 f1 unfolding consume_def vl1 pstl1 pstl text1 by simp
          next
            show "\<gamma> ?trn = \<gamma> ?trn1" unfolding ss1 by simp
          next
            assume "\<gamma> ?trn"
            show "g ?trn = g ?trn1" using ou ou1 by simp
          next
            have "\<Delta>32 s' vl' s1' (OVal True # vll1)"
            using s's1' BO PID' op' unfolding \<Delta>32_def vl' pstl' by auto
            thus "?\<Delta> s' vl' s1' (OVal True # vll1)" by simp
          qed
          thus ?thesis by simp
        next
          case False note pstl'NE = False
          have lpstl': "last pstl' = text1" using t pstl'NE unfolding pstl pstl1 by simp
          have ?ignore proof
            show "\<not> \<gamma> ?trn" unfolding a using uid by auto
          next
            have PID': "PID \<in>\<in> postIDs s'" using reach_postIDs_persist[OF PID step] .
            have op': "\<not> open s'" using step PID' op unfolding a ou open_defs by (auto simp: u_defs)
            have ou1: "ou1 = outOK" using \<phi>1 op1 op' unfolding \<phi>_def2[OF step1] s's1' by auto
            have "\<Delta>31 s' vl' s1 vl1"
            using PID' s's1 op' BO pstl'NE lpstl' unfolding \<Delta>31_def vl' vl1 pstl1 by force
            thus "?\<Delta> s' vl' s1 vl1" by simp
          qed
          thus ?thesis by simp
        qed
      next
        case False note a = False
        {assume \<phi>: "\<phi> ?trn"
         then obtain "text" pstl' where pstl: "pstl = text # pstl'" and f: "f ?trn = TVal text"
         and vl': "vl' = map TVal pstl' @ OVal True # vll"
         using c t unfolding consume_def vl by (cases pstl) auto
         have False using f a \<phi> by (cases ?trn rule: \<phi>.cases) auto
        }
        hence \<phi>: "\<not> \<phi> ?trn" by auto
        have op': "\<not> open s'" using a op \<phi> unfolding \<phi>_def2[OF step] by auto
        have vl': "vl' = vl" using c \<phi> unfolding consume_def by auto
        have s's1': "eqButPID s' s1'" using eqButPID_step[OF ss1 step step1] .
        have op1': "\<not> open s1'" using op' eqButPID_open[OF s's1'] by simp
        have "\<And> uid p text. e_updatePost s1 uid p PID text \<longleftrightarrow> e_updatePost s uid p PID text"
        using eqButPID_stateSelectors[OF ss1] unfolding u_defs by auto
        hence ou1: "\<And> uid p text. a = Uact (uPost uid p PID text) \<Longrightarrow> ou1 = ou"
        using step step1 by auto
        hence \<phi>1: "\<not> \<phi> ?trn1" using a op1 op1' unfolding \<phi>_def2[OF step1] by auto
        have ?match proof
          show "validTrans ?trn1" using step1 by simp
        next
          show "consume ?trn1 vl1 vl1" using \<phi>1 unfolding consume_def by simp
        next
          show "\<gamma> ?trn = \<gamma> ?trn1" unfolding ss1 by simp
        next
          assume "\<gamma> ?trn"
          hence "ou1 = ou" using eqButPID_step_\<gamma>_out[OF ss1 step step1 op rsT rs1] by simp
          thus "g ?trn = g ?trn1" by simp
        next
          have PID': "PID \<in>\<in> postIDs s'" using reach_postIDs_persist[OF PID step] .
          have "\<Delta>31 s' vl' s1' vl1" using s's1' op' PID' BO t
          unfolding \<Delta>31_def vl' vl vl1 pstl1 by fastforce
          thus "?\<Delta> s' vl' s1' vl1" by simp
        qed
      thus ?thesis by simp
      qed
    qed
    thus ?thesis using vlvl1 by simp
  qed
qed

lemma unwind_cont_\<Delta>32: "unwind_cont \<Delta>32 {\<Delta>2,\<Delta>32,\<Delta>4}"
proof(rule, simp)
  let ?\<Delta> = "\<lambda>s vl s1 vl1. \<Delta>2 s vl s1 vl1 \<or> \<Delta>32 s vl s1 vl1 \<or> \<Delta>4 s vl s1 vl1"
  fix s s1 :: state and vl vl1 :: "value list"
  assume rsT: "reachNT s" and rs1: "reach s1" and "\<Delta>32 s vl s1 vl1"
  then obtain vll vll1 where BO: "BO vll vll1"
  and vl: "vl = OVal True # vll"
  and vl1: "vl1 = OVal True # vll1"
  and rs: "reach s" and ss1: "s1 = s" and op: "\<not> open s" and PID: "PID \<in>\<in> postIDs s"
  using reachNT_reach unfolding \<Delta>32_def by fastforce
  have vlvl1: "vl = [] \<Longrightarrow> vl1 = []" unfolding vl vl1 by auto
  show "iaction ?\<Delta> s vl s1 vl1 \<or>
        ((vl = [] \<longrightarrow> vl1 = []) \<and> reaction ?\<Delta> s vl s1 vl1)" (is "?iact \<or> (_ \<and> ?react)")
  proof-
    have ?react proof
      fix a :: act and ou :: out and s' :: state and vl'
      let ?trn = "Trans s a ou s'"
      assume step: "step s a = (ou, s')" and T: "\<not> T ?trn" and c: "consume ?trn vl vl'"
      have PID': "PID \<in>\<in> postIDs s'" using reach_postIDs_persist[OF PID step] .
      let ?trn1 = "Trans s1 a ou s'"
      show "match ?\<Delta> s s1 vl1 a ou s' vl' \<or> ignore ?\<Delta> s s1 vl1 a ou s' vl'" (is "?match \<or> ?ignore")
      proof
        show ?match proof(cases "\<phi> ?trn")
          case True note \<phi> = True
          hence f: "f ?trn = OVal True" and vl': "vl' = vll" using c unfolding consume_def vl by auto
          have op': "open s'" using op \<phi> f unfolding \<phi>_def2[OF step] by auto
          show ?thesis proof
            show "validTrans ?trn1" using step unfolding ss1 by simp
          next
            show "consume ?trn1 vl1 vll1" using \<phi> f unfolding consume_def vl1 ss1 by simp
          next
            show "\<gamma> ?trn = \<gamma> ?trn1" unfolding ss1 by simp
          next
            assume "\<gamma> ?trn"
            thus "g ?trn = g ?trn1" by simp
          next
            show "?\<Delta> s' vl' s' vll1" using BO proof(cases rule: BO.cases)
              case (BO_TVal pstll)
              hence "\<Delta>2 s' vl' s' vll1" using PID' op' unfolding \<Delta>2_def vl' by auto
              thus ?thesis by simp
            next
              case (BO_B vlll pstll)
              hence "\<Delta>4 s' vl' s' vll1" using PID' op' unfolding \<Delta>4_def vl' by auto
              thus ?thesis by simp
            qed
          qed
        next
          case False note \<phi> = False
          hence vl': "vl' = vl" using c unfolding consume_def vl by auto
          have op': "\<not> open s'" using op \<phi> unfolding \<phi>_def2[OF step] by auto
          show ?thesis proof
            show "validTrans ?trn1" using step unfolding ss1 by simp
          next
            show "consume ?trn1 vl1 vl1" using \<phi> unfolding consume_def vl1 ss1 by simp
          next
            show "\<gamma> ?trn = \<gamma> ?trn1" unfolding ss1 by simp
          next
            assume "\<gamma> ?trn"
            thus "g ?trn = g ?trn1" by simp
          next
            have "\<Delta>32 s' vl' s' vl1" using BO PID' op' unfolding \<Delta>32_def vl' vl vl1 by simp
            thus "?\<Delta> s' vl' s' vl1" by simp
          qed
        qed
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
  then obtain pstl vll vll1 where B: "B vll vll1"
  and vl: "vl = map TVal pstl @ OVal False # vll" and vl1: "vl1 = map TVal pstl @ OVal False # vll1"
  and rs: "reach s" and ss1: "s1 = s" and op: "open s" and PID: "PID \<in>\<in> postIDs s"
  using reachNT_reach unfolding \<Delta>4_def by fastforce
  have vlvl1: "vl = [] \<Longrightarrow> vl1 = []" unfolding vl vl1 by auto
  have own: "owner s PID \<in> set (userIDs s)" using reach_owner_userIDs[OF rs PID] .
  show "iaction ?\<Delta> s vl s1 vl1 \<or>
        ((vl = [] \<longrightarrow> vl1 = []) \<and> reaction ?\<Delta> s vl s1 vl1)" (is "?iact \<or> (_ \<and> ?react)")
  proof-
    have ?react proof
      fix a :: act and ou :: out and s' :: state and vl'
      let ?trn = "Trans s a ou s'"  let ?trn1 = "Trans s1 a ou s'"
      assume step: "step s a = (ou, s')" and T: "\<not> T ?trn" and c: "consume ?trn vl vl'"
      have PID': "PID \<in>\<in> postIDs s'" using reach_postIDs_persist[OF PID step] .
      show "match ?\<Delta> s s1 vl1 a ou s' vl' \<or> ignore ?\<Delta> s s1 vl1 a ou s' vl'" (is "?match \<or> ?ignore")
      proof-
        have ?match proof(cases pstl)
          case (Cons "text" pstl') note pstl = Cons
          {assume op': "\<not> open s'"
           hence \<phi>: "\<phi> ?trn" using op unfolding \<phi>_def2[OF step] by simp
           hence f: "f ?trn = TVal text"
           and vl': "vl' = map TVal pstl' @ OVal False # vll"
           using c unfolding consume_def vl pstl by auto
           obtain uid p where a: "a = Uact (uPost uid p PID text)" and ou: "ou = outOK"
             using f \<phi> by (cases ?trn rule: \<phi>.cases) auto
           have False using step op op' PID PID' unfolding a ou open_defs by (auto simp: u_defs)
          }
          hence op': "open s'" by auto
          show ?thesis proof(cases "\<phi> ?trn")
            case True note \<phi> = True
            hence f: "f ?trn = TVal text" and vl': "vl' = map TVal pstl' @ OVal False # vll"
            using c unfolding consume_def  vl pstl by auto
            obtain uid p textt where a: "a = Uact (uPost uid p PID textt)" and ou: "ou = outOK"
            using \<phi> op op' unfolding \<phi>_def2[OF step] by auto
            have textt: "textt = text" using f unfolding a by simp
            show ?thesis proof
              show "validTrans ?trn1" unfolding ss1 using step by simp
            next
              show "consume ?trn1 vl1 (map TVal pstl' @ OVal False # vll1)"
              using \<phi> unfolding ss1 consume_def vl1 vl vl' pstl f by auto
            next
              show "\<gamma> ?trn = \<gamma> ?trn1" unfolding ss1 by simp
            next
              assume "\<gamma> ?trn" thus "g ?trn = g ?trn1" unfolding ss1 by simp
            next
              have "\<Delta>4 s' vl' s' (map TVal pstl' @ OVal False # vll1)"
              using B PID' op' unfolding \<Delta>4_def vl1 vl' vl by auto
              thus "?\<Delta> s' vl' s' (map TVal pstl' @ OVal False # vll1)" by simp
            qed
          next
            case False note \<phi> = False
            hence vl': "vl' = vl" using c unfolding consume_def by auto
            show ?thesis proof
              show "validTrans ?trn1" unfolding ss1 using step by simp
            next
              show "consume ?trn1 vl1 vl1" using \<phi> unfolding ss1 consume_def vl1 vl vl' by auto
            next
              show "\<gamma> ?trn = \<gamma> ?trn1" unfolding ss1 by simp
            next
              assume "\<gamma> ?trn" thus "g ?trn = g ?trn1" unfolding ss1 by simp
            next
              have "\<Delta>4 s' vl' s' vl1"
              using B PID' op' unfolding \<Delta>4_def vl1 vl' vl by auto
              thus "?\<Delta> s' vl' s' vl1" by simp
            qed
          qed
        next
          case Nil note pstl = Nil
          show ?thesis proof(cases "\<phi> ?trn")
            case True note \<phi> = True
            hence f: "f ?trn = OVal False" and vl': "vl' = vll"
            using c unfolding consume_def vl pstl by auto
            hence op': "\<not> open s'" using op step \<phi> unfolding \<phi>_def2[OF step] by auto
            show ?thesis proof
              show "validTrans ?trn1" unfolding ss1 using step by simp
            next
              show "consume ?trn1 vl1 vll1"
              using \<phi> unfolding ss1 consume_def vl1 vl vl' pstl f by auto
            next
              show "\<gamma> ?trn = \<gamma> ?trn1" unfolding ss1 by simp
            next
              assume "\<gamma> ?trn" thus "g ?trn = g ?trn1" unfolding ss1 by simp
            next
              show "?\<Delta> s' vl' s' vll1" using B proof(cases rule: B.cases)
                case (B_TVal pstlll pstlll1)
                hence "\<Delta>1 s' vl' s' vll1"
                using B PID' op' unfolding \<Delta>1_def vl1 vl' vl by auto
                thus ?thesis by simp
              next
                case (B_BO vlll vlll1 pstlll pstlll1)
                show ?thesis proof(cases "pstlll \<noteq> [] \<and> pstlll1 \<noteq> []")
                  case True
                  hence "\<Delta>31 s' vl' s' vll1"
                  using B_BO B PID' op' unfolding \<Delta>31_def vl1 vl' vl by auto
                  thus ?thesis by simp
                next
                  case False
                  hence "\<Delta>32 s' vl' s' vll1"
                  using B_BO B PID' op' unfolding \<Delta>32_def vl1 vl' vl by auto
                  thus ?thesis by simp
                qed
              qed
            qed
          next
            case False note \<phi> = False
            hence vl': "vl' = vl" using c unfolding consume_def by auto
            have op': "open s'" using \<phi> op unfolding \<phi>_def2[OF step] by auto
            show ?thesis proof
              show "validTrans ?trn1" unfolding ss1 using step by simp
            next
              show "consume ?trn1 vl1 vl1" using \<phi> unfolding ss1 consume_def vl1 vl vl' by auto
            next
              show "\<gamma> ?trn = \<gamma> ?trn1" unfolding ss1 by simp
            next
              assume "\<gamma> ?trn" thus "g ?trn = g ?trn1" unfolding ss1 by simp
            next
              have "\<Delta>4 s' vl' s' vl1"
              using B PID' op' unfolding \<Delta>4_def vl1 vl' vl by auto
              thus "?\<Delta> s' vl' s' vl1" by simp
            qed
          qed
        qed
      thus ?thesis by simp
      qed
    qed
  thus ?thesis using vlvl1 by simp
  qed
qed

definition Gr where
"Gr =
 {
 (\<Delta>0, {\<Delta>0,\<Delta>1,\<Delta>2,\<Delta>31,\<Delta>32,\<Delta>4}),
 (\<Delta>1, {\<Delta>1}),
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
istate_\<Delta>0 unwind_cont_\<Delta>0 unwind_cont_\<Delta>1
unwind_cont_\<Delta>31 unwind_cont_\<Delta>32 unwind_cont_\<Delta>2 unwind_cont_\<Delta>4
unfolding Gr_def by auto




end
