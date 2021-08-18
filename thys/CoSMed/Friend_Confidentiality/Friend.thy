theory Friend
imports "../Observation_Setup" Friend_Value_Setup
begin


subsection \<open>Declassification bound\<close>

fun T :: "(state,act,out) trans \<Rightarrow> bool"
where "T (Trans _ _ _ _) = False"

text \<open>The bound follows the same ``while-or-last-before'' scheme as the bound for post
confidentiality (Section~\ref{sec:post-bound}), alternating between open (\<open>BO\<close>) and
closed (\<open>BC\<close>) phases.

The access window is initially open, because the two users are known not to exist when the system
is initialized, so there cannot be friendship between them.

The bound also incorporates the static knowledge that the friendship status alternates between
\<open>False\<close> and \<open>True\<close>.\<close>

fun alternatingFriends :: "value list \<Rightarrow> bool \<Rightarrow> bool" where
  "alternatingFriends [] _ = True"
| "alternatingFriends (FrVal st # vl) st' \<longleftrightarrow> st' = (\<not>st) \<and> alternatingFriends vl st"
| "alternatingFriends (OVal _ # vl) st = alternatingFriends vl st"

inductive BO :: "value list \<Rightarrow> value list \<Rightarrow> bool"
and BC :: "value list \<Rightarrow> value list \<Rightarrow> bool"
where
 BO_FrVal[simp,intro!]:
  "BO (map FrVal fs) (map FrVal fs)"
|BO_BC[intro]:
  "BC vl vl1 \<Longrightarrow>
   BO (map FrVal fs @ OVal False # vl) (map FrVal fs @ OVal False # vl1)"
(*  *)
|BC_FrVal[simp,intro!]:
  "BC (map FrVal fs) (map FrVal fs1)"
|BC_BO[intro]:
  "BO vl vl1 \<Longrightarrow> (fs = [] \<longleftrightarrow> fs1 = []) \<Longrightarrow> (fs \<noteq> [] \<Longrightarrow> last fs = last fs1) \<Longrightarrow>
   BC (map FrVal fs  @ OVal True # vl)
      (map FrVal fs1 @ OVal True # vl1)"

definition "B vl vl1 \<equiv> BO vl vl1 \<and> alternatingFriends vl1 False"


lemma BO_Nil_Nil: "BO vl vl1 \<Longrightarrow> vl = [] \<Longrightarrow> vl1 = []"
by (cases rule: BO.cases) auto

no_notation relcomp (infixr "O" 75)

interpretation BD_Security_IO where
istate = istate and step = step and
\<phi> = \<phi> and f = f and \<gamma> = \<gamma> and g = g and T = T and B = B
done

subsection \<open>Unwinding proof\<close>

(* Key lemma: *)
lemma eqButUID_step_\<gamma>_out:
assumes ss1: "eqButUID s s1"
and step: "step s a = (ou,s')" and step1: "step s1 a = (ou1,s1')"
and \<gamma>: "\<gamma> (Trans s a ou s')"
and os: "open s \<longrightarrow> friendIDs s = friendIDs s1"
shows "ou = ou1"
proof -
  from \<gamma> obtain uid where uid: "userOfA a = Some uid \<and> uid \<in> UIDs \<and> uid \<noteq> UID1 \<and> uid \<noteq> UID2
                              \<or> userOfA a = None"
    using UID1_UID2_UIDs  by (cases "userOfA a") auto
  { fix uid
    assume "uid \<in>\<in> friendIDs s UID1 \<or> uid \<in>\<in> friendIDs s UID2" and "uid \<in> UIDs"
    with os have "friendIDs s = friendIDs s1" unfolding open_def openByF_def by auto
  } note fIDs = this
  { fix uid uid'
    assume uid: "uid \<noteq> UID1" "uid \<noteq> UID2"
    have "friendIDs s uid = friendIDs s1 uid" (is ?f_eq)
     and "pendingFReqs s uid = pendingFReqs s1 uid" (is ?pFR_eq)
     and "uid \<in>\<in> friendIDs s uid' \<longleftrightarrow> uid \<in>\<in> friendIDs s1 uid'" (is ?f_iff)
     and "uid \<in>\<in> pendingFReqs s uid' \<longleftrightarrow> uid \<in>\<in> pendingFReqs s1 uid'" (is ?pFR_iff)
     and "friendReq s uid uid' = friendReq s1 uid uid'" (is ?FR_eq)
     and "friendReq s uid' uid = friendReq s1 uid' uid" (is ?FR_eq')
    proof -
      show ?f_eq ?pFR_eq using uid ss1 UID1_UID2_UIDs unfolding eqButUID_def
        by (auto intro!: eqButUIDf_not_UID)
      show ?f_iff ?pFR_iff using uid ss1 UID1_UID2_UIDs unfolding eqButUID_def
        by (auto intro!: eqButUIDf_not_UID')
      from uid have "\<not> (uid,uid') \<in> {(UID1,UID2), (UID2,UID1)}" by auto
      then show ?FR_eq ?FR_eq' using ss1 UID1_UID2_UIDs unfolding eqButUID_def
        by (auto intro!: eqButUID12_not_UID)
    qed
  } note simps = this eqButUID_def r_defs s_defs c_defs l_defs u_defs d_defs
  note facts = ss1 step step1 uid
  show ?thesis
  proof (cases a)
    case (Ract ra) then show ?thesis using facts by (cases ra) (auto simp add: simps)
  next
    case (Sact sa) then show ?thesis using facts by (cases sa) (auto simp add: simps)
  next
    case (Cact ca) then show ?thesis using facts by (cases ca) (auto simp add: simps)
  next
    case (Lact la)
      then show ?thesis using facts proof (cases la)
        case (lFriends uid p uid')
          with \<gamma> have uid: "uid \<in> UIDs" using Lact by auto
          then have uid_uid': "uid \<in>\<in> friendIDs s uid' \<longleftrightarrow> uid \<in>\<in> friendIDs s1 uid'"
            using ss1 UID1_UID2_UIDs unfolding eqButUID_def by (intro eqButUIDf_not_UID') auto
          show ?thesis
          proof (cases "(uid' = UID1 \<or> uid' = UID2) \<and> uid \<in>\<in> friendIDs s uid'")
            case True
              with uid have "friendIDs s = friendIDs s1" by (intro fIDs) auto
              then show ?thesis using lFriends facts Lact by (auto simp: simps)
          next
            case False
              then show ?thesis using lFriends facts Lact simps(1) uid_uid' by (auto simp: simps)
          qed
      next
        case (lPosts uid p)
          then have o: "\<And>PID. owner s PID = owner s1 PID"
                and n: "\<And>PID. post s PID = post s1 PID"
                and PIDs: "postIDs s = postIDs s1"
                and viss: "vis s = vis s1"
                and fu: "\<And>uid'. uid \<in>\<in> friendIDs s uid' \<longleftrightarrow> uid \<in>\<in> friendIDs s1 uid'"
                and e: "e_listPosts s uid p \<longleftrightarrow> e_listPosts s1 uid p"
            using ss1 uid Lact unfolding eqButUID_def l_defs by (auto simp add: simps(3))
          have "listPosts s uid p = listPosts s1 uid p"
            unfolding listPosts_def o n PIDs fu viss ..
          with e show ?thesis using Lact lPosts step step1 by auto
      qed (auto simp add: simps)
  next
    case (Uact ua) then show ?thesis using facts by (cases ua) (auto simp add: simps)
  next
    case (Dact da) then show ?thesis using facts by (cases da) (auto simp add: simps)
  qed
qed


(* helper *) lemma toggle_friends12_True:
assumes rs: "reach s"
    and IDs: "IDsOK s [UID1, UID2] []"
    and nf12: "\<not>friends12 s"
obtains al oul
where "sstep s al = (oul, createFriend s UID1 (pass s UID1) UID2)"
  and "al \<noteq> []" and "eqButUID s (createFriend s UID1 (pass s UID1) UID2)"
  and "friends12 (createFriend s UID1 (pass s UID1) UID2)"
  and "O (traceOf s al) = []" and "V (traceOf s al) = [FrVal True]"
proof cases
  assume "UID1 \<in>\<in> pendingFReqs s UID2 \<or> UID2 \<in>\<in> pendingFReqs s UID1"
  then show thesis proof
    assume pFR: "UID1 \<in>\<in> pendingFReqs s UID2"
    let ?a = "Cact (cFriend UID2 (pass s UID2) UID1)"
    let ?s' = "createFriend s UID1 (pass s UID1) UID2"
    let ?trn = "Trans s ?a outOK ?s'"
    have step: "step s ?a = (outOK, ?s')" using IDs pFR UID1_UID2
      unfolding createFriend_sym[of "s" "UID1" "pass s UID1" "UID2" "pass s UID2"]
      by (auto simp add: c_defs)
    moreover then have "\<phi> ?trn" and "f ?trn = FrVal True" and "friends12 ?s'"
      by (auto simp: c_defs friends12_def)
    moreover have "\<not>\<gamma> ?trn" using UID1_UID2_UIDs by auto
    ultimately show thesis using nf12 rs
      by (intro that[of "[?a]" "[outOK]"]) (auto intro: Cact_cFriend_step_eqButUID)
  next
    assume pFR: "UID2 \<in>\<in> pendingFReqs s UID1"
    let ?a = "Cact (cFriend UID1 (pass s UID1) UID2)"
    let ?s' = "createFriend s UID1 (pass s UID1) UID2"
    let ?trn = "Trans s ?a outOK ?s'"
    have step: "step s ?a = (outOK, ?s')" using IDs pFR UID1_UID2 by (auto simp add: c_defs)
    moreover then have "\<phi> ?trn" and "f ?trn = FrVal True" and "friends12 ?s'"
      by (auto simp: c_defs friends12_def)
    moreover have "\<not>\<gamma> ?trn" using UID1_UID2_UIDs by auto
    ultimately show thesis using nf12 rs
      by (intro that[of "[?a]" "[outOK]"]) (auto intro: Cact_cFriend_step_eqButUID)
  qed
next
  assume pFR: "\<not>(UID1 \<in>\<in> pendingFReqs s UID2 \<or> UID2 \<in>\<in> pendingFReqs s UID1)"
  let ?a1 = "Cact (cFriendReq UID2 (pass s UID2) UID1 emptyReq)"
  let ?s1 = "createFriendReq s UID2 (pass s UID2) UID1 emptyReq"
  let ?trn1 = "Trans s ?a1 outOK ?s1"
  let ?a2 = "Cact (cFriend UID1 (pass ?s1 UID1) UID2)"
  let ?s2 = "createFriend ?s1 UID1 (pass ?s1 UID1) UID2"
  let ?trn2 = "Trans ?s1 ?a2 outOK ?s2"
  have eFR: "e_createFriendReq s UID2 (pass s UID2) UID1 emptyReq" using IDs pFR nf12
    using reach_friendIDs_symmetric[OF rs]
    by (auto simp add: c_defs friends12_def)
  then have step1: "step s ?a1 = (outOK, ?s1)" by auto
  moreover then have "\<not>\<phi> ?trn1" and "\<not>\<gamma> ?trn1" using UID1_UID2_UIDs by auto
  moreover have "eqButUID s ?s1" by (intro Cact_cFriendReq_step_eqButUID[OF step1]) auto
  moreover have rs1: "reach ?s1" using step1 by (intro reach_PairI[OF rs])
  moreover have step2: "step ?s1 ?a2 = (outOK, ?s2)" using IDs by (auto simp: c_defs)
  moreover then have "\<phi> ?trn2" and "f ?trn2 = FrVal True" and "friends12 ?s2"
    by (auto simp: c_defs friends12_def)
  moreover have "\<not>\<gamma> ?trn2" using UID1_UID2_UIDs by auto
  moreover have "eqButUID ?s1 ?s2" by (intro Cact_cFriend_step_eqButUID[OF step2 rs1]) auto
  moreover have "?s2 = createFriend s UID1 (pass s UID1) UID2"
    using eFR by (intro createFriendReq_createFriend_absorb)
  ultimately show thesis using nf12 rs
    by (intro that[of "[?a1, ?a2]" "[outOK, outOK]"]) (auto intro: eqButUID_trans)
qed

(* helper *) lemma toggle_friends12_False:
assumes rs: "reach s"
    and IDs: "IDsOK s [UID1, UID2] []"
    and f12: "friends12 s"
obtains al oul
where "sstep s al = (oul, deleteFriend s UID1 (pass s UID1) UID2)"
  and "al \<noteq> []" and "eqButUID s (deleteFriend s UID1 (pass s UID1) UID2)"
  and "\<not>friends12 (deleteFriend s UID1 (pass s UID1) UID2)"
  and "O (traceOf s al) = []" and "V (traceOf s al) = [FrVal False]"
proof -
  let ?a = "Dact (dFriend UID1 (pass s UID1) UID2)"
  let ?s' = "deleteFriend s UID1 (pass s UID1) UID2"
  let ?trn = "Trans s ?a outOK ?s'"
  have step: "step s ?a = (outOK, ?s')" using IDs f12 UID1_UID2
    by (auto simp add: d_defs friends12_def)
  moreover then have "\<phi> ?trn" and "f ?trn = FrVal False" and "\<not>friends12 ?s'"
    using reach_friendIDs_symmetric[OF rs] by (auto simp: d_defs friends12_def)
  moreover have "\<not>\<gamma> ?trn" using UID1_UID2_UIDs by auto
  ultimately show thesis using f12 rs
    by (intro that[of "[?a]" "[outOK]"]) (auto intro: Dact_dFriend_step_eqButUID)
qed


definition \<Delta>0 :: "state \<Rightarrow> value list \<Rightarrow> state \<Rightarrow> value list \<Rightarrow> bool" where
"\<Delta>0 s vl s1 vl1 \<equiv>
 eqButUID s s1 \<and> friendIDs s = friendIDs s1 \<and> open s \<and>
 BO vl vl1 \<and> alternatingFriends vl1 (friends12 s1)"

definition \<Delta>1 :: "state \<Rightarrow> value list \<Rightarrow> state \<Rightarrow> value list \<Rightarrow> bool" where
"\<Delta>1 s vl s1 vl1 \<equiv> (\<exists>fs fs1.
 eqButUID s s1 \<and> \<not>open s \<and>
 alternatingFriends vl1 (friends12 s1) \<and>
 vl = map FrVal fs \<and> vl1 = map FrVal fs1)"

definition \<Delta>2 :: "state \<Rightarrow> value list \<Rightarrow> state \<Rightarrow> value list \<Rightarrow> bool" where
"\<Delta>2 s vl s1 vl1 \<equiv> (\<exists>fs fs1 vlr vlr1.
 eqButUID s s1 \<and> \<not>open s \<and> BO vlr vlr1 \<and>
 alternatingFriends vl1 (friends12 s1) \<and>
 (fs = [] \<longleftrightarrow> fs1 = []) \<and>
 (fs \<noteq> [] \<longrightarrow> last fs = last fs1) \<and>
 (fs = [] \<longrightarrow> friendIDs s = friendIDs s1) \<and>
 vl =  map FrVal fs  @ OVal True # vlr \<and>
 vl1 = map FrVal fs1 @ OVal True # vlr1)"

lemma \<Delta>2_I:
assumes "eqButUID s s1" "\<not>open s" "BO vlr vlr1" "alternatingFriends vl1 (friends12 s1)"
        "fs = [] \<longleftrightarrow> fs1 = []" "fs \<noteq> [] \<longrightarrow> last fs = last fs1"
        "fs = [] \<longrightarrow> friendIDs s = friendIDs s1"
        "vl =  map FrVal fs  @ OVal True # vlr"
        "vl1 = map FrVal fs1 @ OVal True # vlr1"
shows "\<Delta>2 s vl s1 vl1"
using assms unfolding \<Delta>2_def by blast


lemma istate_\<Delta>0:
assumes B: "B vl vl1"
shows "\<Delta>0 istate vl istate vl1"
using assms unfolding \<Delta>0_def istate_def B_def open_def openByA_def openByF_def friends12_def
by auto

lemma unwind_cont_\<Delta>0: "unwind_cont \<Delta>0 {\<Delta>0,\<Delta>1,\<Delta>2}"
proof(rule, simp)
  let ?\<Delta> = "\<lambda>s vl s1 vl1. \<Delta>0 s vl s1 vl1 \<or>
                           \<Delta>1 s vl s1 vl1 \<or>
                           \<Delta>2 s vl s1 vl1"
  fix s s1 :: state and vl vl1 :: "value list"
  assume rsT: "reachNT s" and rs1: "reach s1" and \<Delta>0: "\<Delta>0 s vl s1 vl1"
  then have rs: "reach s" and ss1: "eqButUID s s1" and fIDs: "friendIDs s = friendIDs s1"
        and os: "open s" and BO: "BO vl vl1" and aF1: "alternatingFriends vl1 (friends12 s1)"
    using reachNT_reach unfolding \<Delta>0_def by auto
  show "iaction ?\<Delta> s vl s1 vl1 \<or>
        ((vl = [] \<longrightarrow> vl1 = []) \<and> reaction ?\<Delta> s vl s1 vl1)" (is "?iact \<or> (_ \<and> ?react)")
  proof-
    have ?react proof
      fix a :: act and ou :: out and s' :: state and vl'
      let ?trn = "Trans s a ou s'"
      assume step: "step s a = (ou, s')" and T: "\<not> T ?trn" and c: "consume ?trn vl vl'"
      show "match ?\<Delta> s s1 vl1 a ou s' vl' \<or> ignore ?\<Delta> s s1 vl1 a ou s' vl'" (is "?match \<or> ?ignore")
      proof cases
        assume \<phi>: "\<phi> ?trn"
        then have vl: "vl = f ?trn # vl'" using c by (auto simp: consume_def)
        from BO have ?match proof (cases "f ?trn")
          case (FrVal fv)
            with BO vl obtain vl1' where vl1': "vl1 = f ?trn # vl1'" and BO': "BO vl' vl1'"
            proof (cases rule: BO.cases)
              case (BO_BC vl'' vl1'' fs)
                moreover with vl FrVal obtain fs' where "fs = fv # fs'" by (cases fs) auto
                ultimately show ?thesis using FrVal BO_BC vl
                  by (intro that[of "map FrVal fs' @ OVal False # vl1''"]) auto
            qed auto
            from fIDs have f12: "friends12 s = friends12 s1" unfolding friends12_def by auto
            show ?match using \<phi> step rs FrVal proof (cases rule: \<phi>E)
              case (Friend uid p uid')
                then have IDs1: "IDsOK s1 [UID1, UID2] []"
                  using ss1 unfolding eqButUID_def by auto
                let ?s1' = "createFriend s1 UID1 (pass s1 UID1) UID2"
                have s': "s' = createFriend s UID1 p UID2"
                  using Friend step by (auto simp: createFriend_sym)
                have ss': "eqButUID s s'" using rs step Friend
                  by (auto intro: Cact_cFriend_step_eqButUID)
                moreover then have os': "open s'" using os eqButUID_open_eq by auto
                moreover obtain al oul where al: "sstep s1 al = (oul, ?s1')" "al \<noteq> []"
                                         and tr1: "O (traceOf s1 al) = []"
                                                  "V (traceOf s1 al) = [FrVal True]"
                                         and f12s1': "friends12 ?s1'"
                                         and s1s1': "eqButUID s1 ?s1'"
                  using rs1 IDs1 Friend unfolding f12 by (auto elim: toggle_friends12_True)
                moreover have "friendIDs s' = friendIDs ?s1'"
                  using Friend(6) f12 unfolding s'
                  by (intro eqButUID_createFriend12_friendIDs_eq[OF ss1 rs rs1]) auto
                ultimately have "\<Delta>0 s' vl' ?s1' vl1'"
                  using ss1 BO' aF1 unfolding \<Delta>0_def vl1' Friend(3)
                  by (auto intro: eqButUID_trans eqButUID_sym)
                moreover have "\<not>\<gamma> ?trn" using Friend UID1_UID2_UIDs by auto
                ultimately show ?match using tr1 vl1' Friend
                  by (intro matchI_ms[OF al]) (auto simp: consumeList_def)
            next
              case (Unfriend uid p uid')
                then have IDs1: "IDsOK s1 [UID1, UID2] []"
                  using ss1 unfolding eqButUID_def by auto
                let ?s1' = "deleteFriend s1 UID1 (pass s1 UID1) UID2"
                have s': "s' = deleteFriend s UID1 p UID2"
                  using Unfriend step by (auto simp: deleteFriend_sym)
                have ss': "eqButUID s s'" using rs step Unfriend
                  by (auto intro: Dact_dFriend_step_eqButUID)
                moreover then have os': "open s'" using os eqButUID_open_eq by auto
                moreover obtain al oul where al: "sstep s1 al = (oul, ?s1')" "al \<noteq> []"
                                         and tr1: "O (traceOf s1 al) = []"
                                                  "V (traceOf s1 al) = [FrVal False]"
                                         and f12s1': "\<not>friends12 ?s1'"
                                         and s1s1': "eqButUID s1 ?s1'"
                  using rs1 IDs1 Unfriend unfolding f12 by (auto elim: toggle_friends12_False)
                moreover have "friendIDs s' = friendIDs ?s1'"
                  using fIDs unfolding s' by (auto simp: d_defs)
                ultimately have "\<Delta>0 s' vl' ?s1' vl1'"
                  using ss1 BO' aF1 unfolding \<Delta>0_def vl1' Unfriend(3)
                  by (auto intro: eqButUID_trans eqButUID_sym)
                moreover have "\<not>\<gamma> ?trn" using Unfriend UID1_UID2_UIDs by auto
                ultimately show ?match using tr1 vl1' Unfriend
                  by (intro matchI_ms[OF al]) (auto simp: consumeList_def)
            qed auto
        next
          case (OVal ov)
            with BO vl obtain vl1' where vl1': "vl1 = OVal False # vl1'"
                                      and vl': "vl = OVal False # vl'"
                                      and BC: "BC vl' vl1'"
            proof (cases rule: BO.cases)
              case (BO_BC vl'' vl1'' fs)
                moreover then have "fs = []" using vl unfolding OVal by (cases fs) auto
                ultimately show thesis using vl by (intro that[of vl1'']) auto
            qed auto
            then have "f ?trn = OVal False" using vl by auto
            with \<phi> step rs show ?match proof (cases rule: \<phi>E)
              case (CloseF uid p uid')
                let ?s1' = "deleteFriend s1 uid p uid'"
                let ?trn1 = "Trans s1 a outOK ?s1'"
                have s': "s' = deleteFriend s uid p uid'" using CloseF step by auto
                have step1: "step s1 a = (outOK, ?s1')"
                  using CloseF step ss1 fIDs unfolding eqButUID_def by (auto simp: d_defs)
                have s's1': "eqButUID s' ?s1'" using eqButUID_step[OF ss1 step step1 rs rs1] .
                moreover have os': "\<not>open s'" using CloseF os unfolding open_def by auto
                moreover have fIDs': "friendIDs s' = friendIDs ?s1'"
                  using fIDs unfolding s' by (auto simp: d_defs)
                moreover have f12s1: "friends12 s1 = friends12 ?s1'"
                  using CloseF(2) UID1_UID2_UIDs unfolding friends12_def d_defs by auto
                from BC have "\<Delta>1 s' vl' ?s1' vl1' \<or> \<Delta>2 s' vl' ?s1' vl1'"
                proof (cases rule: BC.cases)
                  case (BC_FrVal fs fs1)
                    then show ?thesis using aF1 os' fIDs' f12s1 s's1' unfolding \<Delta>1_def vl1' by auto
                next
                  case (BC_BO vlr vlr1 fs fs1)
                    then have "\<Delta>2 s' vl' ?s1' vl1'" using s's1' os' aF1 f12s1 fIDs' unfolding vl1'
                      by (intro \<Delta>2_I[of _ _ _ _ _ fs fs1]) auto
                    then show ?thesis ..
                qed
                moreover have "open s1" "\<not>open ?s1'"
                  using ss1 os s's1' os' by (auto simp: eqButUID_open_eq)
                moreover then have "\<phi> ?trn1" unfolding CloseF by auto
                ultimately show ?match using step1 vl1' CloseF UID1_UID2 UID1_UID2_UIDs
                  by (intro matchI[of s1 a outOK ?s1' vl1 vl1']) (auto simp: consume_def)
            next
              case (CloseA uid p uid' p')
                let ?s1' = "createUser s1 uid p uid' p'"
                let ?trn1 = "Trans s1 a outOK ?s1'"
                have s': "s' = createUser s uid p uid' p'" using CloseA step by auto
                have step1: "step s1 a = (outOK, ?s1')"
                  using CloseA step ss1 unfolding eqButUID_def by (auto simp: c_defs)
                have s's1': "eqButUID s' ?s1'" using eqButUID_step[OF ss1 step step1 rs rs1] .
                moreover have os': "\<not>open s'" using CloseA os unfolding open_def by auto
                moreover have fIDs': "friendIDs s' = friendIDs ?s1'"
                  using fIDs unfolding s' by (auto simp: c_defs)
                moreover have f12s1: "friends12 s1 = friends12 ?s1'"
                  unfolding friends12_def by (auto simp: c_defs)
                from BC have "\<Delta>1 s' vl' ?s1' vl1' \<or> \<Delta>2 s' vl' ?s1' vl1'"
                proof (cases rule: BC.cases)
                  case (BC_FrVal fs fs1)
                    then show ?thesis using aF1 os' fIDs' f12s1 s's1' unfolding \<Delta>1_def vl1' by auto
                next
                  case (BC_BO vlr vlr1 fs fs1)
                    then have "\<Delta>2 s' vl' ?s1' vl1'" using s's1' os' aF1 f12s1 fIDs' unfolding vl1'
                      by (intro \<Delta>2_I[of _ _ _ _ _ fs fs1]) auto
                    then show ?thesis ..
                qed
                moreover have "open s1" "\<not>open ?s1'"
                  using ss1 os s's1' os' by (auto simp: eqButUID_open_eq)
                moreover then have "\<phi> ?trn1" unfolding CloseA by auto
                ultimately show ?match using step1 vl1' CloseA UID1_UID2 UID1_UID2_UIDs
                  by (intro matchI[of s1 a outOK ?s1' vl1 vl1']) (auto simp: consume_def)
            qed auto
        qed
        then show "?match \<or> ?ignore" ..
      next
        assume n\<phi>: "\<not>\<phi> ?trn"
        then have os': "open s = open s'" and f12s': "friends12 s = friends12 s'"
          using step_open_\<phi>[OF step] step_friends12_\<phi>[OF step] by auto
        have vl': "vl' = vl" using n\<phi> c by (auto simp: consume_def)
        show ?thesis proof (cases "a \<noteq> Cact (cFriend UID1 (pass s UID1) UID2) \<and>
                                   a \<noteq> Cact (cFriend UID2 (pass s UID2) UID1) \<and>
                                   a \<noteq> Dact (dFriend UID1 (pass s UID1) UID2) \<and>
                                   a \<noteq> Dact (dFriend UID2 (pass s UID2) UID1)")
          case True
            obtain ou1 s1' where step1: "step s1 a = (ou1, s1')" by (cases "step s1 a") auto
            let ?trn1 = "Trans s1 a ou1 s1'"
            have fIDs': "friendIDs s' = friendIDs s1'"
              using eqButUID_step_friendIDs_eq[OF ss1 rs rs1 step step1 True fIDs] .
            from True n\<phi> have n\<phi>': "\<not>\<phi> ?trn1" using eqButUID_step_\<phi>[OF ss1 rs rs1 step step1] by auto
            then have f12s1': "friends12 s1 = friends12 s1'"
              using step_friends12_\<phi>[OF step1] by auto
            have "eqButUID s' s1'" using eqButUID_step[OF ss1 step step1 rs rs1] .
            then have "\<Delta>0 s' vl' s1' vl1" using os fIDs' aF1 BO
              unfolding \<Delta>0_def os' f12s1' vl' by auto
            then have ?match
              using step1 n\<phi>' fIDs eqButUID_step_\<gamma>_out[OF ss1 step step1]
              by (intro matchI[of s1 a ou1 s1' vl1 vl1]) (auto simp: consume_def)
            then show "?match \<or> ?ignore" ..
        next
          case False
            with n\<phi> have "ou \<noteq> outOK" by auto
            then have "s' = s" using step False by auto
            then have ?ignore using \<Delta>0 False UID1_UID2_UIDs unfolding vl' by (intro ignoreI) auto
            then show "?match \<or> ?ignore" ..
        qed
      qed
    qed
    then show ?thesis using BO BO_Nil_Nil by auto
  qed
qed

lemma unwind_cont_\<Delta>1: "unwind_cont \<Delta>1 {\<Delta>1, \<Delta>0}"
proof(rule, simp)
  let ?\<Delta> = "\<lambda>s vl s1 vl1. \<Delta>1 s vl s1 vl1 \<or> \<Delta>0 s vl s1 vl1"
  fix s s1 :: state and vl vl1 :: "value list"
  assume rsT: "reachNT s" and rs1: "reach s1" and 1: "\<Delta>1 s vl s1 vl1"
  from rsT have rs: "reach s" by (intro reachNT_reach)
  from 1 obtain fs fs1
  where ss1: "eqButUID s s1" and os: "\<not>open s"
    and aF1: "alternatingFriends vl1 (friends12 s1)"
    and vl: "vl = map FrVal fs" and vl1: "vl1 = map FrVal fs1"
    unfolding \<Delta>1_def by auto
  from os have IDs: "IDsOK s [UID1, UID2] []" unfolding open_defs by auto
  then have IDs1: "IDsOK s1 [UID1, UID2] []" using ss1 unfolding eqButUID_def by auto
  show "iaction ?\<Delta> s vl s1 vl1 \<or>
        ((vl = [] \<longrightarrow> vl1 = []) \<and> reaction ?\<Delta> s vl s1 vl1)" (is "?iact \<or> (_ \<and> ?react)")
  proof cases
    assume fs1: "fs1 = []"
    have ?react proof
      fix a :: act and ou :: out and s' :: state and vl'
      let ?trn = "Trans s a ou s'"
      assume step: "step s a = (ou, s')" and T: "\<not> T ?trn" and c: "consume ?trn vl vl'"
      show "match ?\<Delta> s s1 vl1 a ou s' vl' \<or> ignore ?\<Delta> s s1 vl1 a ou s' vl'" (is "?match \<or> ?ignore")
      proof cases
        assume \<phi>: "\<phi> ?trn"
        with vl c obtain fv fs' where vl': "vl' = map FrVal fs'" and fv: "f ?trn = FrVal fv"
          by (cases fs) (auto simp: consume_def)
        from \<phi> step rs fv have ss': "eqButUID s s'"
          by (elim \<phi>E) (auto intro: Cact_cFriend_step_eqButUID Dact_dFriend_step_eqButUID)
        then have "\<not>open s'" using os by (auto simp: eqButUID_open_eq)
        moreover have "eqButUID s' s1" using ss1 ss' by (auto intro: eqButUID_sym eqButUID_trans)
        ultimately have "\<Delta>1 s' vl' s1 vl1" using aF1 unfolding \<Delta>1_def vl' vl1 by auto
        moreover have "\<not>\<gamma> ?trn" using \<phi> step rs fv UID1_UID2_UIDs by (elim \<phi>E) auto
        ultimately have ?ignore by (intro ignoreI) auto
        then show "?match \<or> ?ignore" ..
      next
        assume n\<phi>: "\<not>\<phi> ?trn"
        then have os': "open s = open s'" and f12s': "friends12 s = friends12 s'"
          using step_open_\<phi>[OF step] step_friends12_\<phi>[OF step] by auto
        have vl': "vl' = vl" using n\<phi> c by (auto simp: consume_def)
        show ?thesis proof (cases "a \<noteq> Cact (cFriend UID1 (pass s UID1) UID2) \<and>
                                   a \<noteq> Cact (cFriend UID2 (pass s UID2) UID1) \<and>
                                   a \<noteq> Dact (dFriend UID1 (pass s UID1) UID2) \<and>
                                   a \<noteq> Dact (dFriend UID2 (pass s UID2) UID1)")
          case True
            obtain ou1 s1' where step1: "step s1 a = (ou1, s1')" by (cases "step s1 a") auto
            let ?trn1 = "Trans s1 a ou1 s1'"
            from True n\<phi> have n\<phi>': "\<not>\<phi> ?trn1" using eqButUID_step_\<phi>[OF ss1 rs rs1 step step1] by auto
            then have f12s1': "friends12 s1 = friends12 s1'"
              using step_friends12_\<phi>[OF step1] by auto
            have "eqButUID s' s1'" using eqButUID_step[OF ss1 step step1 rs rs1] .
            then have "\<Delta>1 s' vl' s1' vl1" using os aF1 vl vl1
              unfolding \<Delta>1_def os' vl' f12s1' by auto
            then have ?match
              using step1 n\<phi>' os eqButUID_step_\<gamma>_out[OF ss1 step step1]
              by (intro matchI[of s1 a ou1 s1' vl1 vl1]) (auto simp: consume_def)
            then show "?match \<or> ?ignore" ..
        next
          case False
            with n\<phi> have "ou \<noteq> outOK" by auto
            then have "s' = s" using step False by auto
            then have ?ignore using 1 False UID1_UID2_UIDs unfolding vl' by (intro ignoreI) auto
            then show "?match \<or> ?ignore" ..
        qed
      qed
    qed
    then show ?thesis using fs1 unfolding vl1 by auto
  next
    assume "fs1 \<noteq> []"
    then obtain fs1' where fs1: "fs1 = (\<not>friends12 s1) # fs1'"
                       and aF1': "alternatingFriends (map FrVal fs1') (\<not>friends12 s1)"
      using aF1 unfolding vl1 by (cases fs1) auto
    obtain al oul s1' where "sstep s1 al = (oul, s1')" "al \<noteq> []" "eqButUID s1 s1'"
                            "friends12 s1' = (\<not>friends12 s1)"
                            "O (traceOf s1 al) = []" "V (traceOf s1 al) = [FrVal (\<not>friends12 s1)]"
      using rs1 IDs1
      by (cases "friends12 s1") (auto intro: toggle_friends12_True toggle_friends12_False)
    moreover then have "\<Delta>1 s vl s1' (map FrVal fs1')"
      using os aF1' vl ss1 unfolding \<Delta>1_def by (auto intro: eqButUID_sym eqButUID_trans)
    ultimately have ?iact using vl1 unfolding fs1
      by (intro iactionI_ms[of s1 al oul s1'])
         (auto simp: consumeList_def O_Nil_never list_ex_iff_length_V)
    then show ?thesis ..
  qed
qed

lemma unwind_cont_\<Delta>2: "unwind_cont \<Delta>2 {\<Delta>2,\<Delta>0}"
proof(rule, simp)
  let ?\<Delta> = "\<lambda>s vl s1 vl1. \<Delta>2 s vl s1 vl1 \<or> \<Delta>0 s vl s1 vl1"
  fix s s1 :: state and vl vl1 :: "value list"
  assume rsT: "reachNT s" and rs1: "reach s1" and 2: "\<Delta>2 s vl s1 vl1"
  from rsT have rs: "reach s" by (intro reachNT_reach)
  obtain fs fs1 vlr vlr1
  where ss1: "eqButUID s s1" and os: "\<not>open s" and BO: "BO vlr vlr1"
    and aF1: "alternatingFriends vl1 (friends12 s1)"
    and vl:  "vl =  map FrVal fs  @ OVal True # vlr"
    and vl1: "vl1 = map FrVal fs1 @ OVal True # vlr1"
    and fs_fs1: "fs = [] \<longleftrightarrow> fs1 = []"
    and last_fs: "fs \<noteq> [] \<longrightarrow> last fs = last fs1"
    and fs_fIDs: "fs = [] \<longrightarrow> friendIDs s = friendIDs s1"
    using 2 unfolding \<Delta>2_def by auto
  from os have IDs: "IDsOK s [UID1, UID2] []" unfolding open_defs by auto
  then have IDs1: "IDsOK s1 [UID1, UID2] []" using ss1 unfolding eqButUID_def by auto
  show "iaction ?\<Delta> s vl s1 vl1 \<or>
        ((vl = [] \<longrightarrow> vl1 = []) \<and> reaction ?\<Delta> s vl s1 vl1)" (is "?iact \<or> (_ \<and> ?react)")
  proof cases
    assume "length fs1 > 1"
    then obtain fs1'
    where fs1: "fs1 = (\<not>friends12 s1) # fs1'" and fs1': "fs1' \<noteq> []"
      and last_fs': "last fs1 = last fs1'"
      and aF1': "alternatingFriends (map FrVal fs1' @ OVal True # vlr1) (\<not>friends12 s1)"
      using vl1 aF1 by (cases fs1) auto
    obtain al oul s1' where "sstep s1 al = (oul, s1')" "al \<noteq> []" "eqButUID s1 s1'"
                            "friends12 s1' = (\<not>friends12 s1)"
                            "O (traceOf s1 al) = []" "V (traceOf s1 al) = [FrVal (\<not>friends12 s1)]"
      using rs1 IDs1
      by (cases "friends12 s1") (auto intro: toggle_friends12_True toggle_friends12_False)
    moreover then have "\<Delta>2 s vl s1' (map FrVal fs1' @ OVal True # vlr1)"
      using os aF1' vl ss1 fs1' last_fs' fs_fs1 last_fs BO unfolding fs1
      by (intro \<Delta>2_I[of _ _ vlr vlr1 _ fs fs1'])
         (auto intro: eqButUID_sym eqButUID_trans)
    ultimately have ?iact using vl1 unfolding fs1
      by (intro iactionI_ms[of s1 al oul s1'])
         (auto simp: consumeList_def O_Nil_never list_ex_iff_length_V)
    then show ?thesis ..
  next
    assume len1_leq_1: "\<not> length fs1 > 1"
    have ?react proof
      fix a :: act and ou :: out and s' :: state and vl'
      let ?trn = "Trans s a ou s'"  let ?trn1 = "Trans s1 a ou s'"
      assume step: "step s a = (ou, s')" and T: "\<not> T ?trn" and c: "consume ?trn vl vl'"
      show "match ?\<Delta> s s1 vl1 a ou s' vl' \<or> ignore ?\<Delta> s s1 vl1 a ou s' vl'" (is "?match \<or> ?ignore")
      proof cases
        assume \<phi>: "\<phi> ?trn"
        show ?thesis proof cases
          assume "length fs > 1"
          then obtain fv fs'
          where fs1: "fs = fv # fs'" and fs1': "fs' \<noteq> []"
            and last_fs': "last fs = last fs'"
            using vl by (cases fs) auto
          with \<phi> c have fv: "f ?trn = FrVal fv" and vl': "vl' = map FrVal fs' @ OVal True # vlr"
            unfolding vl consume_def by auto
          from \<phi> step rs fv have ss': "eqButUID s s'"
            by (elim \<phi>E) (auto intro: Cact_cFriend_step_eqButUID Dact_dFriend_step_eqButUID)
          then have "\<not>open s'" using os by (auto simp: eqButUID_open_eq)
          moreover have "eqButUID s' s1" using ss1 ss' by (auto intro: eqButUID_sym eqButUID_trans)
          ultimately have "\<Delta>2 s' vl' s1 vl1"
            using aF1 vl' fs1' fs_fs1 last_fs BO unfolding fs1 vl1
            by (intro \<Delta>2_I[of _ _ vlr vlr1 _ fs' fs1])
               (auto intro: eqButUID_sym eqButUID_trans)
          moreover have "\<not>\<gamma> ?trn" using \<phi> step rs fv UID1_UID2_UIDs by (elim \<phi>E) auto
          ultimately have ?ignore by (intro ignoreI) auto
          then show "?match \<or> ?ignore" ..
        next
          assume len_leq_1: "\<not> length fs > 1"
          show ?thesis proof cases
            assume fs: "fs = []"
            then have fs1: "fs1 = []" and fIDs: "friendIDs s = friendIDs s1"
              using fs_fs1 fs_fIDs by auto
            from fs \<phi> c have ov: "f ?trn = OVal True" and vl': "vl' = vlr"
              unfolding vl consume_def by auto
            with \<phi> step rs have ?match proof (cases rule: \<phi>E)
              case (OpenF uid p uid')
                let ?s1' = "createFriend s1 uid p uid'"
                let ?trn1 = "Trans s1 a outOK ?s1'"
                have s': "s' = createFriend s uid p uid'" using OpenF step by auto
                have "eqButUIDf (pendingFReqs s) (pendingFReqs s1)"
                  using ss1 unfolding eqButUID_def by auto
                then have "uid' \<in>\<in> pendingFReqs s uid \<longleftrightarrow> uid' \<in>\<in> pendingFReqs s1 uid"
                  using OpenF by (intro eqButUIDf_not_UID') auto
                then have step1: "step s1 a = (outOK, ?s1')"
                  using OpenF step ss1 fIDs unfolding eqButUID_def by (auto simp: c_defs)
                have s's1': "eqButUID s' ?s1'" using eqButUID_step[OF ss1 step step1 rs rs1] .
                moreover have os': "open s'" using OpenF unfolding open_def by auto
                moreover have fIDs': "friendIDs s' = friendIDs ?s1'"
                  using fIDs unfolding s' by (auto simp: c_defs)
                moreover have f12s1: "friends12 s1 = friends12 ?s1'"
                  using OpenF(2) UID1_UID2_UIDs unfolding friends12_def c_defs by auto
                ultimately have "\<Delta>0 s' vl' ?s1' vlr1"
                  using BO aF1 unfolding \<Delta>0_def vl' vl1 fs1 by auto
                moreover have "\<not>open s1" "open ?s1'"
                  using ss1 os s's1' os' by (auto simp: eqButUID_open_eq)
                moreover then have "\<phi> ?trn1" unfolding OpenF by auto
                ultimately show ?match using step1 vl1 fs1 OpenF UID1_UID2 UID1_UID2_UIDs
                  by (intro matchI[of s1 a outOK ?s1' vl1 vlr1]) (auto simp: consume_def)
            qed auto
            then show ?thesis ..
          next
            assume "fs \<noteq> []"
            then obtain fv where fs: "fs = [fv]" using len_leq_1 by (cases fs) auto
            then have fs1: "fs1 = [fv]" using len1_leq_1 fs_fs1 last_fs by (cases fs1) auto
            with aF1 have f12s1: "friends12 s1 = (\<not>fv)" unfolding vl1 by auto
            have fv: "f ?trn = FrVal fv" and vl': "vl' = OVal True # vlr"
              using c \<phi> unfolding vl fs by (auto simp: consume_def)
            with \<phi> step rs have ?match proof (cases rule: \<phi>E)
              case (Friend uid p uid')
                then have IDs1: "IDsOK s1 [UID1, UID2] []"
                  using ss1 unfolding eqButUID_def by auto
                have fv: "fv = True" using fv Friend by auto
                let ?s1' = "createFriend s1 UID1 (pass s1 UID1) UID2"
                have s': "s' = createFriend s UID1 p UID2"
                  using Friend step by (auto simp: createFriend_sym)
                have ss': "eqButUID s s'" using rs step Friend
                  by (auto intro: Cact_cFriend_step_eqButUID)
                moreover then have os': "\<not>open s'" using os eqButUID_open_eq by auto
                moreover obtain al oul where al: "sstep s1 al = (oul, ?s1')" "al \<noteq> []"
                                         and tr1: "O (traceOf s1 al) = []"
                                                  "V (traceOf s1 al) = [FrVal True]"
                                         and f12s1': "friends12 ?s1'"
                                         and s1s1': "eqButUID s1 ?s1'"
                  using rs1 IDs1 Friend f12s1 unfolding fv by (auto elim: toggle_friends12_True)
                moreover have "friendIDs s' = friendIDs ?s1'"
                  using Friend(6) f12s1 unfolding s' fv
                  by (intro eqButUID_createFriend12_friendIDs_eq[OF ss1 rs rs1]) auto
                ultimately have "\<Delta>2 s' vl' ?s1' (OVal True # vlr1)"
                  using BO ss1 aF1 unfolding vl' vl1 fs1 f12s1 fv
                  by (intro \<Delta>2_I[of _ _ _ _ _ "[]" "[]"])
                     (auto intro: eqButUID_trans eqButUID_sym)
                moreover have "\<not>\<gamma> ?trn" using Friend UID1_UID2_UIDs by auto
                ultimately show ?match using tr1 vl1 Friend unfolding fs1 fv
                  by (intro matchI_ms[OF al]) (auto simp: consumeList_def)
            next
              case (Unfriend uid p uid')
                then have IDs1: "IDsOK s1 [UID1, UID2] []"
                  using ss1 unfolding eqButUID_def by auto
                have fv: "fv = False" using fv Unfriend by auto
                let ?s1' = "deleteFriend s1 UID1 (pass s1 UID1) UID2"
                have s': "s' = deleteFriend s UID1 p UID2"
                  using Unfriend step by (auto simp: deleteFriend_sym)
                have ss': "eqButUID s s'" using rs step Unfriend
                  by (auto intro: Dact_dFriend_step_eqButUID)
                moreover then have os': "\<not>open s'" using os eqButUID_open_eq by auto
                moreover obtain al oul where al: "sstep s1 al = (oul, ?s1')" "al \<noteq> []"
                                         and tr1: "O (traceOf s1 al) = []"
                                                  "V (traceOf s1 al) = [FrVal False]"
                                         and f12s1': "\<not>friends12 ?s1'"
                                         and s1s1': "eqButUID s1 ?s1'"
                  using rs1 IDs1 Unfriend f12s1 unfolding fv by (auto elim: toggle_friends12_False)
                moreover have "friendIDs s' = friendIDs ?s1'"
                  using Unfriend(6) f12s1 unfolding s' fv
                  by (intro eqButUID_deleteFriend12_friendIDs_eq[OF ss1 rs rs1])
                ultimately have "\<Delta>2 s' vl' ?s1' (OVal True # vlr1)"
                  using BO ss1 aF1 unfolding vl' vl1 fs1 f12s1 fv
                  by (intro \<Delta>2_I[of _ _ _ _ _ "[]" "[]"])
                     (auto intro: eqButUID_trans eqButUID_sym)
                moreover have "\<not>\<gamma> ?trn" using Unfriend UID1_UID2_UIDs by auto
                ultimately show ?match using tr1 vl1 Unfriend unfolding fs1 fv
                  by (intro matchI_ms[OF al]) (auto simp: consumeList_def)
            qed auto
            then show ?thesis ..
          qed
        qed
      next
        assume n\<phi>: "\<not>\<phi> ?trn"
        then have os': "open s = open s'" and f12s': "friends12 s = friends12 s'"
          using step_open_\<phi>[OF step] step_friends12_\<phi>[OF step] by auto
        have vl': "vl' = vl" using n\<phi> c by (auto simp: consume_def)
        show ?thesis proof (cases "a \<noteq> Cact (cFriend UID1 (pass s UID1) UID2) \<and>
                                   a \<noteq> Cact (cFriend UID2 (pass s UID2) UID1) \<and>
                                   a \<noteq> Dact (dFriend UID1 (pass s UID1) UID2) \<and>
                                   a \<noteq> Dact (dFriend UID2 (pass s UID2) UID1)")
          case True
            obtain ou1 s1' where step1: "step s1 a = (ou1, s1')" by (cases "step s1 a") auto
            let ?trn1 = "Trans s1 a ou1 s1'"
            from True n\<phi> have n\<phi>': "\<not>\<phi> ?trn1" using eqButUID_step_\<phi>[OF ss1 rs rs1 step step1] by auto
            then have f12s1': "friends12 s1 = friends12 s1'"
              using step_friends12_\<phi>[OF step1] by auto
            have "eqButUID s' s1'" using eqButUID_step[OF ss1 step step1 rs rs1] .
            moreover have "friendIDs s = friendIDs s1 \<longrightarrow> friendIDs s' = friendIDs s1'"
              using eqButUID_step_friendIDs_eq[OF ss1 rs rs1 step step1 True] ..
            ultimately have "\<Delta>2 s' vl' s1' vl1"
              using os' os aF1 BO fs_fs1 last_fs fs_fIDs unfolding f12s1' vl' vl vl1
              by (intro \<Delta>2_I) auto
            then have ?match
              using step1 n\<phi>' os eqButUID_step_\<gamma>_out[OF ss1 step step1]
              by (intro matchI[of s1 a ou1 s1' vl1 vl1]) (auto simp: consume_def)
            then show "?match \<or> ?ignore" ..
        next
          case False
            with n\<phi> have "ou \<noteq> outOK" by auto
            then have "s' = s" using step False by auto
            then have ?ignore using 2 False UID1_UID2_UIDs unfolding vl' by (intro ignoreI) auto
            then show "?match \<or> ?ignore" ..
        qed
      qed
    qed
    then show ?thesis unfolding vl by auto
  qed
qed


definition Gr where
"Gr =
 {
 (\<Delta>0, {\<Delta>0,\<Delta>1,\<Delta>2}),
 (\<Delta>1, {\<Delta>1,\<Delta>0}),
 (\<Delta>2, {\<Delta>2,\<Delta>0})
 }"


theorem secure: secure
apply (rule unwind_decomp_secure_graph[of Gr \<Delta>0])
unfolding Gr_def
apply (simp, smt insert_subset order_refl)
using
istate_\<Delta>0 unwind_cont_\<Delta>0 unwind_cont_\<Delta>1 unwind_cont_\<Delta>2
unfolding Gr_def by (auto intro: unwind_cont_mono)


end
