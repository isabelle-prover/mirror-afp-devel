theory Friend_Request
imports "../Observation_Setup" Friend_Request_Value_Setup
begin

subsection \<open>Declassification bound\<close>


fun T :: "(state,act,out) trans \<Rightarrow> bool"
where "T (Trans _ _ _ _) = False"

text \<open>Friendship updates form an alternating sequence of friending and unfriending,
and every successful friend creation is preceded by one or two friendship requests.\<close>

fun validValSeq :: "value list \<Rightarrow> bool \<Rightarrow> bool \<Rightarrow> bool \<Rightarrow> bool" where
  "validValSeq [] _ _ _ = True"
| "validValSeq (FRVal U1 req # vl) st r1 r2 \<longleftrightarrow> (\<not>st) \<and> (\<not>r1) \<and> validValSeq vl st True r2"
| "validValSeq (FRVal U2 req # vl) st r1 r2 \<longleftrightarrow> (\<not>st) \<and> (\<not>r2) \<and> validValSeq vl st r1 True"
| "validValSeq (FVal True # vl) st r1 r2 \<longleftrightarrow> (\<not>st) \<and> (r1 \<or> r2) \<and> validValSeq vl True False False"
| "validValSeq (FVal False # vl) st r1 r2 \<longleftrightarrow> st \<and> (\<not>r1) \<and> (\<not>r2) \<and> validValSeq vl False False False"
| "validValSeq (OVal True # vl) st r1 r2 \<longleftrightarrow> validValSeq vl st r1 r2"
| "validValSeq (OVal False # vl) st r1 r2 \<longleftrightarrow> validValSeq vl st r1 r2"

abbreviation validValSeqFrom :: "value list \<Rightarrow> state \<Rightarrow> bool"
where "validValSeqFrom vl s
 \<equiv> validValSeq vl (friends12 s) (UID1 \<in>\<in> pendingFReqs s UID2) (UID2 \<in>\<in> pendingFReqs s UID1)"

text \<open>With respect to the friendship status updates, we use the same
``while-or-last-before'' bound as for friendship status confidentiality.\<close>

inductive BO :: "value list \<Rightarrow> value list \<Rightarrow> bool"
and BC :: "value list \<Rightarrow> value list \<Rightarrow> bool"
where
 BO_FVal[simp,intro!]:
  "BO (map FVal fs) (map FVal fs)"
|BO_BC[intro]:
  "BC vl vl1 \<Longrightarrow>
   BO (map FVal fs @ OVal False # vl) (map FVal fs @ OVal False # vl1)"
(*  *)
|BC_FVal[simp,intro!]:
  "BC (map FVal fs) (map FVal fs1)"
|BC_BO[intro]:
  "BO vl vl1 \<Longrightarrow> (fs = [] \<longleftrightarrow> fs1 = []) \<Longrightarrow> (fs \<noteq> [] \<Longrightarrow> last fs = last fs1) \<Longrightarrow>
   BC (map FVal fs  @ OVal True # vl)
      (map FVal fs1 @ OVal True # vl1)"

text \<open>Taking into account friendship requests, two value sequences \<open>vl\<close> and \<open>vl1\<close> are in the bound if
  \<^item> \<open>vl1\<close> (with friendship requests) forms a valid value sequence,
  \<^item> \<open>vl\<close> and \<open>vl1\<close> are in \<open>BO\<close> (without friendship requests),
  \<^item> \<open>vl1\<close> is empty if \<open>vl\<close> is empty, and
  \<^item> \<open>vl1\<close> begins with \<^term>\<open>OVal False\<close> if \<open>vl\<close> begins with \<^term>\<open>OVal False\<close>.

The last two points are due to the fact that \<^term>\<open>UID1\<close> and \<^term>\<open>UID1\<close> might not exist yet
if \<open>vl\<close> is empty (or before \<^term>\<open>OVal False\<close>), in which case the observer can deduce that no
friendship request has happened yet.\<close>

definition "B vl vl1 \<equiv> BO (filter (Not o isFRVal) vl) (filter (Not o isFRVal) vl1) \<and>
                       validValSeqFrom vl1 istate \<and>
                       (vl = [] \<longrightarrow> vl1 = []) \<and>
                       (vl \<noteq> [] \<and> hd vl = OVal False \<longrightarrow> vl1 \<noteq> [] \<and> hd vl1 = OVal False)"


lemma BO_Nil_iff: "BO vl vl1 \<Longrightarrow> vl = [] \<longleftrightarrow> vl1 = []"
by (cases rule: BO.cases) auto

no_notation relcomp (infixr "O" 75)

interpretation BD_Security_IO where
istate = istate and step = step and
\<phi> = \<phi> and f = f and \<gamma> = \<gamma> and g = g and T = T and B = B
done

(* sanity check *) lemma validFrom_validValSeq:
assumes "validFrom s tr"
and "reach s"
shows "validValSeqFrom (V tr) s"
using assms proof (induction tr arbitrary: s)
  case (Cons trn tr s)
    then obtain a ou s' where trn: "trn = Trans s a ou s'"
                          and step: "step s a = (ou, s')"
                          and tr: "validFrom s' tr"
                          and s': "reach s'"
      by (cases trn) (auto iff: validFrom_Cons intro: reach_PairI)
    then have vVS_tr: "validValSeqFrom (V tr) s'" by (intro Cons.IH)
    show ?case proof cases
      assume \<phi>: "\<phi> (Trans s a ou s')"
      then have V: "V (Trans s a ou s' # tr) = f (Trans s a ou s') # V tr" by auto
      from \<phi> vVS_tr Cons.prems step show ?thesis unfolding trn V by (elim \<phi>E) auto
    next
      assume "\<not>\<phi> (Trans s a ou s')"
      then have "V (Trans s a ou s' # tr) = V tr" and "friends12 s' = friends12 s"
            and "UID1 \<in>\<in> pendingFReqs s' UID2 \<longleftrightarrow> UID1 \<in>\<in> pendingFReqs s UID2"
            and "UID2 \<in>\<in> pendingFReqs s' UID1 \<longleftrightarrow> UID2 \<in>\<in> pendingFReqs s UID1"
        using step_friends12_\<phi>[OF step] step_pendingFReqs_\<phi>[OF step] by auto
      with vVS_tr show ?thesis unfolding trn by auto
    qed
qed auto

lemma "validFrom istate tr \<Longrightarrow> validValSeqFrom (V tr) istate"
using validFrom_validValSeq[of istate] reach.Istate unfolding istate_def friends12_def
by auto


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
    using UID1_UID2_UIDs by (cases "userOfA a") auto
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
    case (Ract ra) then show ?thesis using facts
      apply (cases ra) by (auto simp add: simps)
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
          then have o: "\<And>pid. owner s pid = owner s1 pid"
                and n: "\<And>pid. post s pid = post s1 pid"
                and pids: "postIDs s = postIDs s1"
                and viss: "vis s = vis s1"
                and fu: "\<And>uid'. uid \<in>\<in> friendIDs s uid' \<longleftrightarrow> uid \<in>\<in> friendIDs s1 uid'"
                and e: "e_listPosts s uid p \<longleftrightarrow> e_listPosts s1 uid p"
            using ss1 uid Lact unfolding eqButUID_def l_defs by (auto simp add: simps(3))
          have "listPosts s uid p = listPosts s1 uid p"
            unfolding listPosts_def o n pids fu viss ..
          with e show ?thesis using Lact lPosts step step1 by auto
      qed (auto simp add: simps)
  next
    case (Uact ua) then show ?thesis using facts by (cases ua) (auto simp add: simps)
  next
    case (Dact da) then show ?thesis using facts by (cases da) (auto simp add: simps)
  qed
qed


(* helper *) lemma produce_FRVal:
assumes rs: "reach s"
and IDs: "IDsOK s [UID1, UID2] []"
and vVS: "validValSeqFrom (FRVal u req # vl) s"
obtains a uid uid' s'
where "step s a = (outOK, s')"
  and "a = Cact (cFriendReq uid (pass s uid) uid' req)"
  and "uid = UID1 \<and> uid' = UID2 \<or> uid = UID2 \<and> uid' = UID1"
  and "\<phi> (Trans s a outOK s')"
  and "f (Trans s a outOK s') = FRVal u req"
  and "validValSeqFrom vl s'"
proof (cases u)
  case U1
    then have "step s (Cact (cFriendReq UID1 (pass s UID1) UID2 req)) =
                 (outOK, createFriendReq s UID1 (pass s UID1) UID2 req)"
          and "\<not>friends12 (createFriendReq s UID1 (pass s UID1) UID2 req)"
      using IDs vVS reach_friendIDs_symmetric[OF rs] by (auto simp: c_defs friends12_def)
    then show thesis using U1 vVS UID1_UID2 by (intro that[of _ _ UID1 UID2]) (auto simp: c_defs)
next
  case U2
    then have "step s (Cact (cFriendReq UID2 (pass s UID2) UID1 req)) =
                 (outOK, createFriendReq s UID2 (pass s UID2) UID1 req)"
          and "\<not>friends12 (createFriendReq s UID2 (pass s UID2) UID1 req)"
      using IDs vVS reach_friendIDs_symmetric[OF rs] by (auto simp: c_defs friends12_def)
    then show thesis using U2 vVS UID1_UID2 by (intro that[of _ _ UID2 UID1]) (auto simp: c_defs)
qed

(* helper *) lemma toggle_friends12_True:
assumes rs: "reach s"
    and IDs: "IDsOK s [UID1, UID2] []"
    and nf12: "\<not>friends12 s"
    and vVS: "validValSeqFrom (FVal True # vl) s"
obtains a uid uid' s'
where "step s a = (outOK, s')"
  and "a = Cact (cFriend uid (pass s uid) uid')"
  and "s' = createFriend s UID1 (pass s UID1) UID2"
  and "uid = UID1 \<and> uid' = UID2 \<or> uid = UID2 \<and> uid' = UID1"
  and "friends12 s'"
  and "eqButUID s s'"
  and "\<phi> (Trans s a outOK s')"
  and "f (Trans s a outOK s') = FVal True"
  and "\<not>\<gamma> (Trans s a outOK s')"
  and "validValSeqFrom vl s'"
proof -
  from vVS have "UID1 \<in>\<in> pendingFReqs s UID2 \<or> UID2 \<in>\<in> pendingFReqs s UID1" by auto
  then show thesis proof
    assume pFR: "UID1 \<in>\<in> pendingFReqs s UID2"
    let ?a = "Cact (cFriend UID2 (pass s UID2) UID1)"
    let ?s' = "createFriend s UID1 (pass s UID1) UID2"
    let ?trn = "Trans s ?a outOK ?s'"
    have step: "step s ?a = (outOK, ?s')" using IDs pFR UID1_UID2
      unfolding createFriend_sym[of "s" "UID1" "pass s UID1" "UID2" "pass s UID2"]
      by (auto simp add: c_defs)
    moreover then have "\<phi> ?trn" and "f ?trn = FVal True" and "friends12 ?s'"
                   and "UID1 \<notin> set (pendingFReqs ?s' UID2)"
                   and "UID2 \<notin> set (pendingFReqs ?s' UID1)"
      using reach_distinct_friends_reqs[OF rs] by (auto simp: c_defs friends12_def)
    moreover have "\<not>\<gamma> ?trn" using UID1_UID2_UIDs by auto
    ultimately show thesis using nf12 rs vVS
      by (intro that[of "?a" "?s'" UID2 UID1]) (auto intro: Cact_cFriend_step_eqButUID)
  next
    assume pFR: "UID2 \<in>\<in> pendingFReqs s UID1"
    let ?a = "Cact (cFriend UID1 (pass s UID1) UID2)"
    let ?s' = "createFriend s UID1 (pass s UID1) UID2"
    let ?trn = "Trans s ?a outOK ?s'"
    have step: "step s ?a = (outOK, ?s')" using IDs pFR UID1_UID2 by (auto simp add: c_defs)
    moreover then have "\<phi> ?trn" and "f ?trn = FVal True" and "friends12 ?s'"
                   and "UID1 \<notin> set (pendingFReqs ?s' UID2)"
                   and "UID2 \<notin> set (pendingFReqs ?s' UID1)"
      using reach_distinct_friends_reqs[OF rs] by (auto simp: c_defs friends12_def)
    moreover have "\<not>\<gamma> ?trn" using UID1_UID2_UIDs by auto
    ultimately show thesis using nf12 rs vVS
      by (intro that[of "?a" "?s'" UID1 UID2]) (auto intro: Cact_cFriend_step_eqButUID)
  qed
qed

(* helper *) lemma toggle_friends12_False:
assumes rs: "reach s"
    and IDs: "IDsOK s [UID1, UID2] []"
    and f12: "friends12 s"
    and vVS: "validValSeqFrom (FVal False # vl) s"
obtains a s'
where "step s a = (outOK, s')"
  and "a = Dact (dFriend UID1 (pass s UID1) UID2)"
  and "s' = deleteFriend s UID1 (pass s UID1) UID2"
  and "\<not>friends12 s'"
  and "eqButUID s s'"
  and "\<phi> (Trans s a outOK s')"
  and "f (Trans s a outOK s') = FVal False"
  and "\<not>\<gamma> (Trans s a outOK s')"
  and "validValSeqFrom vl s'"
proof -
  let ?a = "Dact (dFriend UID1 (pass s UID1) UID2)"
  let ?s' = "deleteFriend s UID1 (pass s UID1) UID2"
  let ?trn = "Trans s ?a outOK ?s'"
  from vVS have step: "step s ?a = (outOK, ?s')"
        and "UID1 \<notin> set (pendingFReqs ?s' UID2)" "UID2 \<notin> set (pendingFReqs ?s' UID1)"
    using IDs f12 UID1_UID2 by (auto simp add: d_defs friends12_def)
  moreover then have "\<phi> ?trn" and "f ?trn = FVal False" and "\<not>friends12 ?s'"
    by (auto simp: d_defs friends12_def)
  moreover have "\<not>\<gamma> ?trn" using UID1_UID2_UIDs by auto
  ultimately show thesis using f12 rs vVS
    by (intro that[of ?a ?s']) (auto intro: Dact_dFriend_step_eqButUID)
qed

lemma toggle_friends12:
assumes rs: "reach s"
    and IDs: "IDsOK s [UID1, UID2] []"
    and f12: "friends12 s \<noteq> fv"
    and vVS: "validValSeqFrom (FVal fv # vl) s"
obtains a s'
where "step s a = (outOK, s')"
  and "friends12 s' = fv"
  and "eqButUID s s'"
  and "\<phi> (Trans s a outOK s')"
  and "f (Trans s a outOK s') = FVal fv"
  and "\<not>\<gamma> (Trans s a outOK s')"
  and "validValSeqFrom vl s'"
proof (cases "friends12 s")
  case True
    moreover then have "UID1 \<notin> set (pendingFReqs s UID2)" "UID2 \<notin> set (pendingFReqs s UID1)"
                   and "fv = False"
                   and vVS: "validValSeqFrom (FVal False # vl) s"
      using vVS f12 unfolding friends12_def by auto
    moreover then have "UID1 \<notin> set (pendingFReqs (deleteFriend s UID1 (pass s UID1) UID2) UID2)"
                       "UID2 \<notin> set (pendingFReqs (deleteFriend s UID1 (pass s UID1) UID2) UID1)"
      by (auto simp: d_defs)
    ultimately show thesis using assms
      by (elim toggle_friends12_False, blast, blast, blast) (elim that, blast+)
next
  case False
    moreover then have "fv = True"
                   and vVS: "validValSeqFrom (FVal True # vl) s"
      using vVS f12 by auto
    moreover have "UID1 \<notin> set (pendingFReqs (createFriend s UID1 (pass s UID1) UID2) UID2)"
                  "UID2 \<notin> set (pendingFReqs (createFriend s UID1 (pass s UID1) UID2) UID1)"
      using reach_distinct_friends_reqs[OF rs] by (auto simp: c_defs)
    ultimately show thesis using assms
      by (elim toggle_friends12_True, blast, blast, blast) (elim that, blast+)
qed


(* helper *) lemma BO_cases:
assumes "BO vl vl1"
obtains (Nil) "vl = []" and "vl1 = []"
      | (FVal) fv vl' vl1' where "vl = FVal fv # vl'" and "vl1 = FVal fv # vl1'" and "BO vl' vl1'"
      | (OVal) vl' vl1' where "vl = OVal False # vl'" and "vl1 = OVal False # vl1'" and "BC vl' vl1'"
using assms proof (cases rule: BO.cases)
  case (BO_FVal fs) then show thesis by (cases fs) (auto intro: Nil FVal) next
  case (BO_BC vl'' vl1'' fs) then show thesis by (cases fs) (auto intro: FVal OVal)
qed

(* helper *) lemma BC_cases:
assumes "BC vl vl1"
obtains (Nil) "vl = []" and "vl1 = []"
      | (FVal) fv fs where "vl = FVal fv # map FVal fs" and "vl1 = []"
      | (FVal1) fv fs fs1 where "vl = map FVal fs" and "vl1 = FVal fv # map FVal fs1"
      | (BO_FVal) fv fv' fs vl' vl1' where "vl = FVal fv # map FVal fs @ FVal fv' # OVal True # vl'"
                                       and "vl1 = FVal fv' # OVal True # vl1'" and "BO vl' vl1'"
      | (BO_FVal1) fv fv' fs fs1 vl' vl1' where "vl = map FVal fs @ FVal fv' # OVal True # vl'"
                                       and "vl1 = FVal fv # map FVal fs1 @ FVal fv' # OVal True # vl1'"
                                       and "BO vl' vl1'"
      | (FVal_BO) fv vl' vl1' where "vl = FVal fv # OVal True # vl'"
                                and "vl1 = FVal fv # OVal True # vl1'" and "BO vl' vl1'"
      | (OVal) vl' vl1' where "vl = OVal True # vl'" and "vl1 = OVal True # vl1'" and "BO vl' vl1'"
using assms proof (cases rule: BC.cases)
  case (BC_FVal fs fs1)
    then show ?thesis proof (induction fs1)
      case Nil then show ?case by (induction fs) (auto intro: that(1,2)) next
      case (Cons fv fs1') then show ?case by (intro that(3)) auto
    qed
next
  case (BC_BO vl' vl1' fs fs1)
    then show ?thesis proof (cases fs1 rule: rev_cases)
      case Nil then show ?thesis using BC_BO by (intro that(7)) auto next
      case (snoc fs1' fv')
        moreover then obtain fs' where "fs = fs' ## fv'" using BC_BO
          by (induction fs rule: rev_induct) auto
        ultimately show ?thesis using BC_BO proof (induction fs1')
          case Nil
            then show ?thesis proof (induction fs')
              case Nil then show ?thesis by (intro that(6)) auto next
              case (Cons fv'' fs'') then show ?thesis by (intro that(4)) auto
            qed
        next
          case (Cons fv'' fs1'') then show ?thesis by (intro that(5)) auto
        qed
    qed
qed


definition \<Delta>0 :: "state \<Rightarrow> value list \<Rightarrow> state \<Rightarrow> value list \<Rightarrow> bool" where
"\<Delta>0 s vl s1 vl1 \<equiv>
 s = s1 \<and> B vl vl1 \<and> open s \<and> (\<not>IDsOK s [UID1, UID2] [])"

definition \<Delta>1 :: "state \<Rightarrow> value list \<Rightarrow> state \<Rightarrow> value list \<Rightarrow> bool" where
"\<Delta>1 s vl s1 vl1 \<equiv>
 eqButUID s s1 \<and> friendIDs s = friendIDs s1 \<and> open s \<and>
 BO (filter (Not o isFRVal) vl) (filter (Not o isFRVal) vl1) \<and>
 validValSeqFrom vl1 s1 \<and>
 IDsOK s1 [UID1, UID2] []"

definition \<Delta>2 :: "state \<Rightarrow> value list \<Rightarrow> state \<Rightarrow> value list \<Rightarrow> bool" where
"\<Delta>2 s vl s1 vl1 \<equiv> (\<exists>fs fs1.
 eqButUID s s1 \<and> \<not>open s \<and>
 validValSeqFrom vl1 s1 \<and>
 filter (Not o isFRVal) vl  = map FVal fs  \<and>
 filter (Not o isFRVal) vl1 = map FVal fs1)"

definition \<Delta>3 :: "state \<Rightarrow> value list \<Rightarrow> state \<Rightarrow> value list \<Rightarrow> bool" where
"\<Delta>3 s vl s1 vl1 \<equiv> (\<exists>fs fs1 vlr vlr1.
 eqButUID s s1 \<and> \<not>open s \<and> BO vlr vlr1 \<and>
 validValSeqFrom vl1 s1 \<and>
 (fs = [] \<longleftrightarrow> fs1 = []) \<and>
 (fs \<noteq> [] \<longrightarrow> last fs = last fs1) \<and>
 (fs = [] \<longrightarrow> friendIDs s = friendIDs s1) \<and>
 filter (Not o isFRVal) vl  = map FVal fs  @ OVal True # vlr \<and>
 filter (Not o isFRVal) vl1 = map FVal fs1 @ OVal True # vlr1)"


lemma \<Delta>2_I:
assumes "eqButUID s s1" "\<not>open s"
        "validValSeqFrom vl1 s1"
        "filter (Not o isFRVal) vl  = map FVal fs"
        "filter (Not o isFRVal) vl1 = map FVal fs1"
shows "\<Delta>2 s vl s1 vl1"
using assms unfolding \<Delta>2_def by blast

lemma \<Delta>3_I:
assumes "eqButUID s s1" "\<not>open s" "BO vlr vlr1"
        "validValSeqFrom vl1 s1"
        "fs = [] \<longleftrightarrow> fs1 = []" "fs \<noteq> [] \<longrightarrow> last fs = last fs1"
        "fs = [] \<longrightarrow> friendIDs s = friendIDs s1"
        "filter (Not o isFRVal) vl  = map FVal fs  @ OVal True # vlr"
        "filter (Not o isFRVal) vl1 = map FVal fs1 @ OVal True # vlr1"
shows "\<Delta>3 s vl s1 vl1"
using assms unfolding \<Delta>3_def by blast


lemma istate_\<Delta>0:
assumes B: "B vl vl1"
shows "\<Delta>0 istate vl istate vl1"
using assms unfolding \<Delta>0_def istate_def B_def open_def openByA_def openByF_def friends12_def
by auto

lemma unwind_cont_\<Delta>0: "unwind_cont \<Delta>0 {\<Delta>0,\<Delta>1,\<Delta>2,\<Delta>3}"
proof(rule, simp)
  let ?\<Delta> = "\<lambda>s vl s1 vl1. \<Delta>0 s vl s1 vl1 \<or>
                           \<Delta>1 s vl s1 vl1 \<or>
                           \<Delta>2 s vl s1 vl1 \<or>
                           \<Delta>3 s vl s1 vl1"
  fix s s1 :: state and vl vl1 :: "value list"
  assume rsT: "reachNT s" and rs1: "reach s1" and \<Delta>0: "\<Delta>0 s vl s1 vl1"
  then have rs: "reach s" and ss1: "s1 = s" and B: "B vl vl1" and os: "open s"
        and IDs: "\<not>IDsOK s [UID1, UID2] []"
    using reachNT_reach unfolding \<Delta>0_def by auto
  from IDs have "UID1 \<notin> set (pendingFReqs s UID2)" and "\<not>friends12 s"
            and "UID2 \<notin> set (pendingFReqs s UID1)"
    using reach_IDs_used_IDsOK[OF rs] unfolding friends12_def by auto
  with B have BO: "BO (filter (Not \<circ> isFRVal) vl) (filter (Not \<circ> isFRVal) vl1)"
          and vl_vl1: "vl = [] \<longrightarrow> vl1 = []"
          and vl_OVal: "vl \<noteq> [] \<and> hd vl = OVal False \<longrightarrow> vl1 \<noteq> [] \<and> hd vl1 = OVal False"
          and vVS: "validValSeqFrom vl1 s"
    unfolding B_def by (auto simp: istate_def friends12_def)
  show "iaction ?\<Delta> s vl s1 vl1 \<or>
        ((vl = [] \<longrightarrow> vl1 = []) \<and> reaction ?\<Delta> s vl s1 vl1)" (is "?iact \<or> (_ \<and> ?react)")
  proof -
    have ?react proof
      fix a :: act and ou :: out and s' :: state and vl'
      let ?trn = "Trans s a ou s'"
      assume step: "step s a = (ou, s')" and T: "\<not> T ?trn" and c: "consume ?trn vl vl'"
      show "match ?\<Delta> s s1 vl1 a ou s' vl' \<or> ignore ?\<Delta> s s1 vl1 a ou s' vl'" (is "?match \<or> ?ignore")
      proof cases
        assume \<phi>: "\<phi> ?trn"
        then obtain uid p uid' p' where a: "a = Cact (cUser uid p uid' p')"
                                     "\<not>openByA s'" "\<not>openByF s'"
                                     "ou = outOK" "f ?trn = OVal False"
                                     "friends12 s' = friends12 s"
                                     "UID1 \<in>\<in> pendingFReqs s' UID2 \<longleftrightarrow> UID1 \<in>\<in> pendingFReqs s UID2"
                                     "UID2 \<in>\<in> pendingFReqs s' UID1 \<longleftrightarrow> UID2 \<in>\<in> pendingFReqs s UID1"
          using step rs IDs by (elim \<phi>E) (auto simp: openByA_def)
        with c \<phi> have vl: "vl = OVal False # vl'" unfolding consume_def by auto
        with vl_OVal obtain vl1' where vl1: "vl1 = OVal False # vl1'" by (cases vl1) auto
        from BO vl vl1 have BC': "BC (filter (Not \<circ> isFRVal) vl') (filter (Not \<circ> isFRVal) vl1')"
          by (cases rule: BO_cases) auto
        then have "\<Delta>2 s' vl' s' vl1' \<or> \<Delta>3 s' vl' s' vl1'" using vVS a unfolding vl1
        proof (cases rule: BC.cases)
          case BC_FVal
            then show ?thesis using vVS a unfolding vl1
              by (intro disjI1 \<Delta>2_I) (auto simp: open_def)
        next
          case BC_BO
            then show ?thesis using vVS a unfolding vl1
              by (intro disjI2 \<Delta>3_I) (auto simp: open_def)
        qed
        then have ?match using step a \<phi> unfolding ss1 vl1
          by (intro matchI[of s a ou s']) (auto simp: consume_def)
        then show ?thesis ..
      next
        assume n\<phi>: "\<not>\<phi> ?trn"
        then have s': "open s'" "friends12 s' = friends12 s"
                      "UID1 \<in>\<in> pendingFReqs s' UID2 \<longleftrightarrow> UID1 \<in>\<in> pendingFReqs s UID2"
                      "UID2 \<in>\<in> pendingFReqs s' UID1 \<longleftrightarrow> UID2 \<in>\<in> pendingFReqs s UID1"
          using os step_open_\<phi>[OF step] step_friends12_\<phi>[OF step] step_pendingFReqs_\<phi>[OF step]
          by auto
        moreover have "vl' = vl" using n\<phi> c by (auto simp: consume_def)
        ultimately have "\<Delta>0 s' vl' s' vl1 \<or> \<Delta>1 s' vl' s' vl1"
          using vVS B BO unfolding \<Delta>0_def \<Delta>1_def
          by (cases "IDsOK s' [UID1, UID2] []") auto
        then have ?match using step c n\<phi> unfolding ss1
          by (intro matchI[of s a ou s']) (auto simp: consume_def)
        then show ?thesis ..
      qed
    qed
    then show ?thesis using vl_vl1 by auto
  qed
qed

lemma unwind_cont_\<Delta>1: "unwind_cont \<Delta>1 {\<Delta>1,\<Delta>2,\<Delta>3}"
proof(rule, simp)
  let ?\<Delta> = "\<lambda>s vl s1 vl1. \<Delta>1 s vl s1 vl1 \<or>
                           \<Delta>2 s vl s1 vl1 \<or>
                           \<Delta>3 s vl s1 vl1"
  fix s s1 :: state and vl vl1 :: "value list"
  assume rsT: "reachNT s" and rs1: "reach s1" and \<Delta>1: "\<Delta>1 s vl s1 vl1"
  then have rs: "reach s" and ss1: "eqButUID s s1" and fIDs: "friendIDs s = friendIDs s1"
        and os: "open s" and BO: "BO (filter (Not o isFRVal) vl) (filter (Not o isFRVal) vl1)"
        and vVS1: "validValSeq vl1 (friends12 s1)
                                   (UID1 \<in>\<in> pendingFReqs s1 UID2)
                                   (UID2 \<in>\<in> pendingFReqs s1 UID1)" (is "?vVS vl1 s1")
        and IDs1: "IDsOK s1 [UID1, UID2] []"
    using reachNT_reach unfolding \<Delta>1_def by auto
  show "iaction ?\<Delta> s vl s1 vl1 \<or>
        ((vl = [] \<longrightarrow> vl1 = []) \<and> reaction ?\<Delta> s vl s1 vl1)" (is "?iact \<or> (_ \<and> ?react)")
  proof cases
    assume "\<exists>u req vl1'. vl1 = FRVal u req # vl1'"
    then obtain u req vl1' where vl1: "vl1 = FRVal u req # vl1'" by auto
    obtain a uid uid' s1' where step1: "step s1 a = (outOK, s1')" and "\<phi> (Trans s1 a outOK s1')"
                            and a: "a = Cact (cFriendReq uid (pass s1 uid) uid' req)"
                            and uid: "uid = UID1 \<and> uid' = UID2 \<or> uid = UID2 \<and> uid' = UID1"
                            and "f (Trans s1 a outOK s1') = FRVal u req" and "?vVS vl1' s1'"
      using rs1 IDs1 vVS1 UID1_UID2_UIDs unfolding vl1 by (blast intro: produce_FRVal)
    moreover then have "\<not>\<gamma> (Trans s1 a outOK s1')" using UID1_UID2_UIDs by auto
    moreover have "eqButUID s1 s1'" using step1 a uid by (auto intro: Cact_cFriendReq_step_eqButUID)
    moreover have "friendIDs s1' = friendIDs s1" and "IDsOK s1' [UID1, UID2] []"
      using step1 a uid by (auto simp: c_defs)
    ultimately have "?iact" using ss1 fIDs os BO unfolding vl1
      by (intro iactionI[of s1 a "outOK" s1']) (auto simp: consume_def \<Delta>1_def intro: eqButUID_trans)
    then show ?thesis ..
  next
    assume nFRVal1: "\<not> (\<exists>u req vl1'. vl1 = FRVal u req # vl1')"
    have ?react proof
      fix a :: act and ou :: out and s' :: state and vl'
      let ?trn = "Trans s a ou s'"
      assume step: "step s a = (ou, s')" and T: "\<not> T ?trn" and c: "consume ?trn vl vl'"
      show "match ?\<Delta> s s1 vl1 a ou s' vl' \<or> ignore ?\<Delta> s s1 vl1 a ou s' vl'" (is "?match \<or> ?ignore")
      proof cases
        assume \<phi>: "\<phi> ?trn"
        then have vl: "vl = f ?trn # vl'" using c by (auto simp: consume_def)
        from BO show ?thesis proof (cases "f ?trn")
          case (FVal fv)
            with BO obtain vl1' where vl1: "vl1 = f ?trn # vl1'"
              using BO_Nil_iff[OF BO] FVal vl nFRVal1
              by (cases rule: BO_cases; cases vl1; cases "hd vl1") auto
            with BO have BO': "BO (filter (Not o isFRVal) vl') (filter (Not o isFRVal) vl1')"
              using FVal vl by (cases rule: BO_cases) auto
            from fIDs have f12: "friends12 s = friends12 s1" unfolding friends12_def by auto
            have ?match using \<phi> step rs FVal proof (cases rule: \<phi>E)
              case (Friend uid p uid')
                then have IDs1: "IDsOK s1 [UID1, UID2] []"
                  using ss1 unfolding eqButUID_def by auto
                let ?s1' = "createFriend s1 UID1 (pass s1 UID1) UID2"
                have s': "s' = createFriend s UID1 p UID2"
                  using Friend step by (auto simp: createFriend_sym)
                have ss': "eqButUID s s'" using rs step Friend
                  by (auto intro: Cact_cFriend_step_eqButUID)
                moreover then have os': "open s'" using os eqButUID_open_eq by auto
                moreover obtain a1 uid1 uid1' p1
                where "step s1 a1 = (outOK, ?s1')" "friends12 ?s1'"
                      "a1 = Cact (cFriend uid1 p1 uid1')"
                      "uid1 = UID1 \<and> uid1' = UID2 \<or> uid1 = UID2 \<and> uid1' = UID1"
                      "\<phi> (Trans s1 a1 outOK ?s1')"
                      "f (Trans s1 a1 outOK ?s1') = FVal True"
                      "eqButUID s1 ?s1'" "?vVS vl1' ?s1'"
                  using rs1 IDs1 Friend vVS1 unfolding vl1 f12 Friend(3)
                  by (elim toggle_friends12_True) blast+
                moreover then have "IDsOK ?s1' [UID1, UID2] []" by (auto simp: c_defs)
                moreover have "friendIDs s' = friendIDs ?s1'"
                  using Friend(6) f12 unfolding s'
                  by (intro eqButUID_createFriend12_friendIDs_eq[OF ss1 rs rs1]) auto
                ultimately show ?match using ss1 BO' Friend UID1_UID2_UIDs unfolding vl1 \<Delta>1_def
                  by (intro matchI[of s1 a1 "outOK" ?s1'])
                     (auto simp: consume_def intro: eqButUID_trans eqButUID_sym)
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
                moreover obtain a1 uid1 uid1' p1
                where "step s1 a1 = (outOK, ?s1')" "\<not>friends12 ?s1'"
                      "a1 = Dact (dFriend uid1 p1 uid1')"
                      "uid1 = UID1 \<and> uid1' = UID2 \<or> uid1 = UID2 \<and> uid1' = UID1"
                      "\<phi> (Trans s1 a1 outOK ?s1')"
                      "f (Trans s1 a1 outOK ?s1') = FVal False"
                      "eqButUID s1 ?s1'" "?vVS vl1' ?s1'"
                  using rs1 IDs1 Unfriend vVS1 unfolding vl1 f12 Unfriend(3)
                  by (elim toggle_friends12_False) blast+
                moreover have "friendIDs s' = friendIDs ?s1'" "IDsOK ?s1' [UID1, UID2] []"
                  using fIDs IDs1 unfolding s' by (auto simp: d_defs)
                ultimately show ?match using ss1 BO' Unfriend UID1_UID2_UIDs unfolding vl1 \<Delta>1_def
                  by (intro matchI[of s1 a1 "outOK" ?s1'])
                     (auto simp: consume_def intro: eqButUID_trans eqButUID_sym)
            qed auto
            then show ?thesis ..
        next
          case (OVal ov)
            with BO obtain vl1' where vl1': "vl1 = OVal False # vl1'"
              using BO_Nil_iff[OF BO] OVal vl nFRVal1
              by (cases rule: BO_cases; cases vl1; cases "hd vl1") auto
            with BO have BC': "BC (filter (Not o isFRVal) vl') (filter (Not o isFRVal) vl1')"
              using OVal vl by (cases rule: BO_cases) auto
            from BO vl OVal have "f ?trn = OVal False" by (cases rule: BO_cases) auto
            with \<phi> step rs have ?match proof (cases rule: \<phi>E)
              case (CloseF uid p uid')
                let ?s1' = "deleteFriend s1 uid p uid'"
                let ?trn1 = "Trans s1 a outOK ?s1'"
                have s': "s' = deleteFriend s uid p uid'" using CloseF step by auto
                have step1: "step s1 a = (outOK, ?s1')"
                 and pFR1': "pendingFReqs ?s1' = pendingFReqs s1"
                  using CloseF step ss1 fIDs unfolding eqButUID_def by (auto simp: d_defs)
                have s's1': "eqButUID s' ?s1'" using eqButUID_step[OF ss1 step step1 rs rs1] .
                moreover have os': "\<not>open s'" using CloseF os unfolding open_def by auto
                moreover have fIDs': "friendIDs s' = friendIDs ?s1'"
                  using fIDs unfolding s' by (auto simp: d_defs)
                moreover have f12s1: "friends12 s1 = friends12 ?s1'"
                  using CloseF(2) UID1_UID2_UIDs unfolding friends12_def d_defs by auto
                from BC' have "\<Delta>2 s' vl' ?s1' vl1' \<or> \<Delta>3 s' vl' ?s1' vl1'"
                proof (cases rule: BC.cases)
                  case (BC_FVal fs fs1)
                    then show ?thesis using vVS1 os' fIDs' f12s1 s's1' pFR1'
                      unfolding \<Delta>2_def vl1' by auto
                next
                  case (BC_BO vlr vlr1 fs fs1)
                    then have "\<Delta>3 s' vl' ?s1' vl1'" using s's1' os' vVS1 f12s1 fIDs' pFR1'
                      unfolding vl1' by (intro \<Delta>3_I[of _ _ _ _ _ fs fs1]) auto
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
                 and pFR1': "pendingFReqs ?s1' = pendingFReqs s1"
                  using CloseA step ss1 unfolding eqButUID_def by (auto simp: c_defs)
                have s's1': "eqButUID s' ?s1'" using eqButUID_step[OF ss1 step step1 rs rs1] .
                moreover have os': "\<not>open s'" using CloseA os unfolding open_def by auto
                moreover have fIDs': "friendIDs s' = friendIDs ?s1'"
                  using fIDs unfolding s' by (auto simp: c_defs)
                moreover have f12s1: "friends12 s1 = friends12 ?s1'"
                  unfolding friends12_def by (auto simp: c_defs)
                from BC' have "\<Delta>2 s' vl' ?s1' vl1' \<or> \<Delta>3 s' vl' ?s1' vl1'"
                proof (cases rule: BC.cases)
                  case (BC_FVal fs fs1)
                    then show ?thesis using vVS1 os' fIDs' f12s1 s's1' pFR1'
                      unfolding \<Delta>2_def vl1' by auto
                next
                  case (BC_BO vlr vlr1 fs fs1)
                    then have "\<Delta>3 s' vl' ?s1' vl1'" using s's1' os' vVS1 f12s1 fIDs' pFR1'
                      unfolding vl1' by (intro \<Delta>3_I[of _ _ _ _ _ fs fs1]) auto
                    then show ?thesis ..
                qed
                moreover have "open s1" "\<not>open ?s1'"
                  using ss1 os s's1' os' by (auto simp: eqButUID_open_eq)
                moreover then have "\<phi> ?trn1" unfolding CloseA by auto
                ultimately show ?match using step1 vl1' CloseA UID1_UID2 UID1_UID2_UIDs
                  by (intro matchI[of s1 a outOK ?s1' vl1 vl1']) (auto simp: consume_def)
            qed auto
            then show ?thesis ..
        next
          case (FRVal u req)
            obtain p
            where a: "(a = Cact (cFriendReq UID1 p UID2 req) \<and> UID1 \<in>\<in> pendingFReqs s' UID2 \<and>
                       UID1 \<notin> set (pendingFReqs s UID2) \<and>
                       (UID2 \<in>\<in> pendingFReqs s' UID1 \<longleftrightarrow> UID2 \<in>\<in> pendingFReqs s UID1)) \<or>
                      (a = Cact (cFriendReq UID2 p UID1 req) \<and> UID2 \<in>\<in> pendingFReqs s' UID1 \<and>
                       UID2 \<notin> set (pendingFReqs s UID1) \<and>
                       (UID1 \<in>\<in> pendingFReqs s' UID2 \<longleftrightarrow> UID1 \<in>\<in> pendingFReqs s UID2))"
                     "ou = outOK" "\<not>friends12 s" "\<not>friends12 s'" "open s' = open s"
              using \<phi> step rs FRVal by (cases rule: \<phi>E) fastforce+
            then have fIDs': "friendIDs s' = friendIDs s" using step by (auto simp: c_defs)
            have "eqButUID s s'" using a step
              by (auto intro: Cact_cFriendReq_step_eqButUID)
            then have "\<Delta>1 s' vl' s1 vl1"
              unfolding \<Delta>1_def using ss1 fIDs' fIDs os a(5) vVS1 IDs1 BO vl FRVal
              by (auto intro: eqButUID_trans eqButUID_sym)
            moreover from \<phi> step rs a have "\<not>\<gamma> (Trans s a ou s')"
              using UID1_UID2_UIDs by auto
            ultimately have ?ignore by (intro ignoreI) auto
            then show ?thesis ..
        qed
      next
        assume n\<phi>: "\<not>\<phi> ?trn"
        then have os': "open s = open s'" and f12s': "friends12 s = friends12 s'"
          using step_open_\<phi>[OF step] step_friends12_\<phi>[OF step] by auto
        have vl': "vl' = vl" using n\<phi> c by (auto simp: consume_def)
        show ?thesis proof (cases "\<forall>req. a \<noteq> Cact (cFriend UID1 (pass s UID1) UID2) \<and>
                                         a \<noteq> Cact (cFriend UID2 (pass s UID2) UID1) \<and>
                                         a \<noteq> Cact (cFriendReq UID2 (pass s UID2) UID1 req) \<and>
                                         a \<noteq> Cact (cFriendReq UID1 (pass s UID1) UID2 req) \<and>
                                         a \<noteq> Dact (dFriend UID1 (pass s UID1) UID2) \<and>
                                         a \<noteq> Dact (dFriend UID2 (pass s UID2) UID1)")
          case True
            obtain ou1 s1' where step1: "step s1 a = (ou1, s1')" by (cases "step s1 a") auto
            let ?trn1 = "Trans s1 a ou1 s1'"
            have fIDs': "friendIDs s' = friendIDs s1'" using True
              by (intro eqButUID_step_friendIDs_eq[OF ss1 rs rs1 step step1 _ fIDs]) auto
            from True n\<phi> have n\<phi>': "\<not>\<phi> ?trn1" using eqButUID_step_\<phi>[OF ss1 rs rs1 step step1] by auto
            then have f12s1': "friends12 s1 = friends12 s1'"
                  and pFRs': "UID1 \<in>\<in> pendingFReqs s1 UID2 \<longleftrightarrow> UID1 \<in>\<in> pendingFReqs s1' UID2"
                             "UID2 \<in>\<in> pendingFReqs s1 UID1 \<longleftrightarrow> UID2 \<in>\<in> pendingFReqs s1' UID1"
              using step_friends12_\<phi>[OF step1] step_pendingFReqs_\<phi>[OF step1]
              by auto
            have "eqButUID s' s1'" using eqButUID_step[OF ss1 step step1 rs rs1] .
            then have "\<Delta>1 s' vl' s1' vl1" using os fIDs' vVS1 BO IDsOK_mono[OF step1 IDs1]
              unfolding \<Delta>1_def os' f12s1' pFRs' vl' by auto
            then have ?match
              using step1 n\<phi>' fIDs eqButUID_step_\<gamma>_out[OF ss1 step step1]
              by (intro matchI[of s1 a ou1 s1' vl1 vl1]) (auto simp: consume_def)
            then show "?match \<or> ?ignore" ..
        next
          case False
            with n\<phi> have "ou \<noteq> outOK" by auto
            then have "s' = s" using step False by auto
            then have ?ignore using \<Delta>1 False UID1_UID2_UIDs unfolding vl' by (intro ignoreI) auto
            then show "?match \<or> ?ignore" ..
        qed
      qed
    qed
    moreover have "vl = [] \<longrightarrow> vl1 = []" proof
      assume "vl = []"
      with BO have "filter (Not \<circ> isFRVal) vl1 = []" using BO_Nil_iff[OF BO] by auto
      with nFRVal1 show "vl1 = []" by (cases vl1; cases "hd vl1") auto
    qed
    ultimately show ?thesis by auto
  qed
qed

lemma unwind_cont_\<Delta>2: "unwind_cont \<Delta>2 {\<Delta>2, \<Delta>1}"
proof(rule, simp)
  let ?\<Delta> = "\<lambda>s vl s1 vl1. \<Delta>2 s vl s1 vl1 \<or> \<Delta>1 s vl s1 vl1"
  fix s s1 :: state and vl vl1 :: "value list"
  assume rsT: "reachNT s" and rs1: "reach s1" and 2: "\<Delta>2 s vl s1 vl1"
  from rsT have rs: "reach s" by (intro reachNT_reach)
  from 2 obtain fs fs1
  where ss1: "eqButUID s s1" and os: "\<not>open s"
    and vVS1: "validValSeqFrom vl1 s1"
    and fs:  "filter (Not o isFRVal) vl =  map FVal fs"
    and fs1: "filter (Not o isFRVal) vl1 = map FVal fs1"
    unfolding \<Delta>2_def by auto
  from os have IDs: "IDsOK s [UID1, UID2] []" unfolding open_defs by auto
  then have IDs1: "IDsOK s1 [UID1, UID2] []" using ss1 unfolding eqButUID_def by auto
  show "iaction ?\<Delta> s vl s1 vl1 \<or>
        ((vl = [] \<longrightarrow> vl1 = []) \<and> reaction ?\<Delta> s vl s1 vl1)" (is "?iact \<or> (_ \<and> ?react)")
  proof cases
    assume vl1: "vl1 = []"
    have ?react proof
      fix a :: act and ou :: out and s' :: state and vl'
      let ?trn = "Trans s a ou s'"
      assume step: "step s a = (ou, s')" and T: "\<not> T ?trn" and c: "consume ?trn vl vl'"
      show "match ?\<Delta> s s1 vl1 a ou s' vl' \<or> ignore ?\<Delta> s s1 vl1 a ou s' vl'" (is "?match \<or> ?ignore")
      proof cases
        assume \<phi>: "\<phi> ?trn"
        with c have vl: "vl = f ?trn # vl'" by (auto simp: consume_def)
        with fs have ?ignore proof (cases "f ?trn")
          case (FRVal u req)
            obtain p
            where a: "(a = Cact (cFriendReq UID1 p UID2 req) \<and> UID1 \<in>\<in> pendingFReqs s' UID2 \<and>
                       UID1 \<notin> set (pendingFReqs s UID2) \<and>
                       (UID2 \<in>\<in> pendingFReqs s' UID1 \<longleftrightarrow> UID2 \<in>\<in> pendingFReqs s UID1)) \<or>
                      (a = Cact (cFriendReq UID2 p UID1 req) \<and> UID2 \<in>\<in> pendingFReqs s' UID1 \<and>
                       UID2 \<notin> set (pendingFReqs s UID1) \<and>
                       (UID1 \<in>\<in> pendingFReqs s' UID2 \<longleftrightarrow> UID1 \<in>\<in> pendingFReqs s UID2))"
                     "ou = outOK" "\<not>friends12 s" "\<not>friends12 s'" "open s' = open s"
              using \<phi> step rs FRVal by (cases rule: \<phi>E) fastforce+
            then have fIDs': "friendIDs s' = friendIDs s" using step by (auto simp: c_defs)
            have "eqButUID s s'" using a step
              by (auto intro: Cact_cFriendReq_step_eqButUID)
            then have "\<Delta>2 s' vl' s1 vl1"
              unfolding \<Delta>2_def using ss1 os a(5) vVS1 vl fs fs1
              by (auto intro: eqButUID_trans eqButUID_sym)
            moreover from \<phi> step rs a have "\<not>\<gamma> (Trans s a ou s')"
              using UID1_UID2_UIDs by auto
            ultimately show ?ignore by (intro ignoreI) auto
        next
          case (FVal fv)
            with fs vl obtain fs' where fs': "fs = fv # fs'" by (cases fs) auto
            from \<phi> step rs FVal have ss': "eqButUID s s'"
              by (elim \<phi>E) (auto intro: Cact_cFriend_step_eqButUID Dact_dFriend_step_eqButUID)
            then have "\<not>open s'" using os by (auto simp: eqButUID_open_eq)
            moreover have "eqButUID s' s1" using ss1 ss' by (auto intro: eqButUID_sym eqButUID_trans)
            ultimately have "\<Delta>2 s' vl' s1 vl1"
              using vVS1 fs' fs unfolding \<Delta>2_def vl vl1 FVal by auto
            moreover have "\<not>\<gamma> ?trn" using \<phi> step rs FVal UID1_UID2_UIDs by (elim \<phi>E) auto
            ultimately show ?ignore by (intro ignoreI) auto
        qed auto
        then show ?thesis ..
      next
        assume n\<phi>: "\<not>\<phi> ?trn"
        then have os': "open s = open s'" and f12s': "friends12 s = friends12 s'"
          using step_open_\<phi>[OF step] step_friends12_\<phi>[OF step] by auto
        have vl': "vl' = vl" using n\<phi> c by (auto simp: consume_def)
        show ?thesis proof (cases "\<forall>req. a \<noteq> Cact (cFriend UID1 (pass s UID1) UID2) \<and>
                                         a \<noteq> Cact (cFriend UID2 (pass s UID2) UID1) \<and>
                                         a \<noteq> Cact (cFriendReq UID2 (pass s UID2) UID1 req) \<and>
                                         a \<noteq> Cact (cFriendReq UID1 (pass s UID1) UID2 req) \<and>
                                         a \<noteq> Dact (dFriend UID1 (pass s UID1) UID2) \<and>
                                         a \<noteq> Dact (dFriend UID2 (pass s UID2) UID1)")
          case True
            obtain ou1 s1' where step1: "step s1 a = (ou1, s1')" by (cases "step s1 a") auto
            let ?trn1 = "Trans s1 a ou1 s1'"
            from True n\<phi> have n\<phi>': "\<not>\<phi> ?trn1"
              using eqButUID_step_\<phi>[OF ss1 rs rs1 step step1] by auto
            then have f12s1': "friends12 s1 = friends12 s1'"
                  and pFRs': "UID1 \<in>\<in> pendingFReqs s1 UID2 \<longleftrightarrow> UID1 \<in>\<in> pendingFReqs s1' UID2"
                             "UID2 \<in>\<in> pendingFReqs s1 UID1 \<longleftrightarrow> UID2 \<in>\<in> pendingFReqs s1' UID1"
              using step_friends12_\<phi>[OF step1] step_pendingFReqs_\<phi>[OF step1]
              by auto
            have "eqButUID s' s1'" using eqButUID_step[OF ss1 step step1 rs rs1] .
            then have "\<Delta>2 s' vl' s1' vl1" using os vVS1 fs fs1
              unfolding \<Delta>2_def os' f12s1' pFRs' vl' by auto
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
    then show ?thesis using vl1 by auto
  next
    assume "vl1 \<noteq> []"
    then obtain v vl1' where vl1: "vl1 = v # vl1'" by (cases vl1) auto
    with fs1 have ?iact proof (cases v)
      case (FRVal u req)
        obtain a uid uid' s1' where step1: "step s1 a = (outOK, s1')" and "\<phi> (Trans s1 a outOK s1')"
                                and a: "a = Cact (cFriendReq uid (pass s1 uid) uid' req)"
                                and uid: "uid = UID1 \<and> uid' = UID2 \<or> uid = UID2 \<and> uid' = UID1"
                                and "f (Trans s1 a outOK s1') = FRVal u req"
                                and vVS1': "validValSeqFrom vl1' s1'"
          using rs1 IDs1 vVS1 UID1_UID2_UIDs unfolding vl1 FRVal by (blast intro: produce_FRVal)
        moreover then have "\<not>\<gamma> (Trans s1 a outOK s1')" using UID1_UID2_UIDs by auto
        moreover have "eqButUID s1 s1'" using step1 a uid
          by (auto intro: Cact_cFriendReq_step_eqButUID)
        moreover then have "\<Delta>2 s vl s1' vl1'" using ss1 os vVS1' fs fs1 unfolding vl1 FRVal
          by (intro \<Delta>2_I[of s s1' vl1' vl fs fs1]) (auto intro: eqButUID_trans)
        ultimately show "?iact" using ss1 os unfolding vl1 FRVal
          by (intro iactionI[of s1 a "outOK" s1']) (auto simp: consume_def intro: eqButUID_trans)
    next
      case (FVal fv)
        then obtain fs1' where fs1': "fs1 = fv # fs1'"
          using vl1 fs1 by (cases fs1) auto
        from FVal vVS1 vl1 have f12: "friends12 s1 \<noteq> fv"
                            and vVS1: "validValSeqFrom (FVal fv # vl1') s1" by auto
        then show ?iact using rs1 IDs1 vl1 FVal ss1 os fs fs1 fs1' vl1 FVal
          by (elim toggle_friends12[of s1 fv vl1'], blast, blast, blast)
             (intro iactionI[of s1 _ _ _ vl1 vl1'],
              auto simp: consume_def intro: \<Delta>2_I[of s _ vl1' vl fs fs1'] eqButUID_trans)
    qed auto
    then show ?thesis ..
  qed
qed


lemma unwind_cont_\<Delta>3: "unwind_cont \<Delta>3 {\<Delta>3,\<Delta>1}"
proof(rule, simp)
  let ?\<Delta> = "\<lambda>s vl s1 vl1. \<Delta>3 s vl s1 vl1 \<or> \<Delta>1 s vl s1 vl1"
  fix s s1 :: state and vl vl1 :: "value list"
  assume rsT: "reachNT s" and rs1: "reach s1" and 3: "\<Delta>3 s vl s1 vl1"
  from rsT have rs: "reach s" by (intro reachNT_reach)
  obtain fs fs1 vlr vlr1
  where ss1: "eqButUID s s1" and os: "\<not>open s" and BO: "BO vlr vlr1"
    and vVS1: "validValSeqFrom vl1 s1"
    and fs:  "filter (Not o isFRVal) vl =  map FVal fs  @ OVal True # vlr"
    and fs1: "filter (Not o isFRVal) vl1 = map FVal fs1 @ OVal True # vlr1"
    and fs_fs1: "fs = [] \<longleftrightarrow> fs1 = []"
    and last_fs: "fs \<noteq> [] \<longrightarrow> last fs = last fs1"
    and fs_fIDs: "fs = [] \<longrightarrow> friendIDs s = friendIDs s1"
    using 3 unfolding \<Delta>3_def by auto
  have BC: "BC (map FVal fs @ OVal True # vlr) (map FVal fs1 @ OVal True # vlr1)"
    using fs fs1 fs_fs1 last_fs BO by auto
  from os have IDs: "IDsOK s [UID1, UID2] []" unfolding open_defs by auto
  then have IDs1: "IDsOK s1 [UID1, UID2] []" using ss1 unfolding eqButUID_def by auto
  show "iaction ?\<Delta> s vl s1 vl1 \<or>
        ((vl = [] \<longrightarrow> vl1 = []) \<and> reaction ?\<Delta> s vl s1 vl1)" (is "?iact \<or> (_ \<and> ?react)")
  proof cases
    assume "\<exists>u req vl1'. vl1 = FRVal u req # vl1'"
    then obtain u req vl1' where vl1: "vl1 = FRVal u req # vl1'" by auto
    obtain a uid uid' s1' where step1: "step s1 a = (outOK, s1')" and \<phi>: "\<phi> (Trans s1 a outOK s1')"
                            and a: "a = Cact (cFriendReq uid (pass s1 uid) uid' req)"
                            and uid: "uid = UID1 \<and> uid' = UID2 \<or> uid = UID2 \<and> uid' = UID1"
                            and f: "f (Trans s1 a outOK s1') = FRVal u req"
                            and "validValSeqFrom vl1' s1'"
      using rs1 IDs1 vVS1 UID1_UID2_UIDs unfolding vl1 by (blast intro: produce_FRVal)
    moreover have "eqButUID s1 s1'" using step1 a uid by (auto intro: Cact_cFriendReq_step_eqButUID)
    moreover have "friendIDs s1' = friendIDs s1" and "IDsOK s1' [UID1, UID2] []"
      using step1 a uid by (auto simp: c_defs)
    ultimately have "\<Delta>3 s vl s1' vl1'" using ss1 os BO fs_fs1 last_fs fs_fIDs fs fs1 unfolding vl1
      by (intro \<Delta>3_I[of _ _ vlr vlr1 vl1' fs fs1 vl])
         (auto simp: consume_def intro: eqButUID_trans)
    moreover have "\<not>\<gamma> (Trans s1 a outOK s1')" using a uid UID1_UID2_UIDs by auto
    ultimately have "?iact" using step1 \<phi> f unfolding vl1
      by (intro iactionI[of s1 a "outOK" s1']) (auto simp: consume_def)
    then show ?thesis ..
  next
    assume nFRVal1: "\<not>(\<exists>u req vl1'. vl1 = FRVal u req # vl1')"
    from BC show ?thesis proof (cases rule: BC_cases)
      case (BO_FVal fv fv' fs' vl'' vl1'')
        then have fs': "filter (Not o isFRVal) vl = map FVal (fv # fs' ## fv') @ OVal True # vl''"
              and fs1': "filter (Not o isFRVal) vl1 = FVal fv' # OVal True # vl1''"
          using fs fs1 by auto
        have ?react proof
          fix a :: act and ou :: out and s' :: state and vl'
          let ?trn = "Trans s a ou s'"  let ?trn1 = "Trans s1 a ou s'"
          assume step: "step s a = (ou, s')" and T: "\<not> T ?trn" and c: "consume ?trn vl vl'"
          show "match ?\<Delta> s s1 vl1 a ou s' vl' \<or> ignore ?\<Delta> s s1 vl1 a ou s' vl'" (is "?match \<or> ?ignore")
          proof cases
            assume \<phi>: "\<phi> ?trn"
            with c have vl: "vl = f ?trn # vl'" by (auto simp: consume_def)
            with fs' have ?ignore proof (cases "f ?trn")
              case (FRVal u req)
                obtain p
                where a: "(a = Cact (cFriendReq UID1 p UID2 req) \<and> UID1 \<in>\<in> pendingFReqs s' UID2 \<and>
                           UID1 \<notin> set (pendingFReqs s UID2) \<and>
                           (UID2 \<in>\<in> pendingFReqs s' UID1 \<longleftrightarrow> UID2 \<in>\<in> pendingFReqs s UID1)) \<or>
                          (a = Cact (cFriendReq UID2 p UID1 req) \<and> UID2 \<in>\<in> pendingFReqs s' UID1 \<and>
                           UID2 \<notin> set (pendingFReqs s UID1) \<and>
                           (UID1 \<in>\<in> pendingFReqs s' UID2 \<longleftrightarrow> UID1 \<in>\<in> pendingFReqs s UID2))"
                         "ou = outOK" "\<not>friends12 s" "\<not>friends12 s'" "open s' = open s"
                  using \<phi> step rs FRVal by (cases rule: \<phi>E) fastforce+
                then have fIDs': "friendIDs s' = friendIDs s" using step by (auto simp: c_defs)
                have "eqButUID s s'" using a step
                  by (auto intro: Cact_cFriendReq_step_eqButUID)
                then have "\<Delta>3 s' vl' s1 vl1"
                  using ss1 a os BO vVS1 fs_fs1 last_fs fs_fIDs fs fs1 fIDs' vl FRVal
                  by (intro \<Delta>3_I[of s' s1 vlr vlr1 vl1 fs fs1 vl'])
                     (auto intro: eqButUID_trans eqButUID_sym)
                moreover from a have "\<not>\<gamma> (Trans s a ou s')"
                  using UID1_UID2_UIDs by auto
                ultimately show ?ignore by (intro ignoreI) auto
            next
              case (FVal fv'')
                with vl fs' have FVal: "f ?trn = FVal fv"
                             and vl': "filter (Not \<circ> isFRVal) vl' = map FVal (fs' ## fv') @ OVal True # vl''"
                  by auto
                from \<phi> step rs FVal have ss': "eqButUID s s'"
                  by (elim \<phi>E) (auto intro: Cact_cFriend_step_eqButUID Dact_dFriend_step_eqButUID)
                then have "\<not>open s'" using os by (auto simp: eqButUID_open_eq)
                moreover have "eqButUID s' s1" using ss1 ss' by (auto intro: eqButUID_sym eqButUID_trans)
                ultimately have "\<Delta>3 s' vl' s1 vl1" using BO_FVal(3) vVS1 vl' fs1'
                  by (intro \<Delta>3_I[of s' s1 vl'' vl1'' vl1 "fs' ## fv'" "[fv']" vl']) auto
                moreover have "\<not>\<gamma> ?trn" using \<phi> step rs FVal UID1_UID2_UIDs by (elim \<phi>E) auto
                ultimately show ?ignore by (intro ignoreI) auto
            qed auto
            then show ?thesis ..
          next
            assume n\<phi>: "\<not>\<phi> ?trn"
            then have os': "open s = open s'" and f12s': "friends12 s = friends12 s'"
              using step_open_\<phi>[OF step] step_friends12_\<phi>[OF step] by auto
            have vl': "vl' = vl" using n\<phi> c by (auto simp: consume_def)
            show ?thesis proof (cases "\<forall>req. a \<noteq> Cact (cFriend UID1 (pass s UID1) UID2) \<and>
                                             a \<noteq> Cact (cFriend UID2 (pass s UID2) UID1) \<and>
                                             a \<noteq> Cact (cFriendReq UID2 (pass s UID2) UID1 req) \<and>
                                             a \<noteq> Cact (cFriendReq UID1 (pass s UID1) UID2 req) \<and>
                                             a \<noteq> Dact (dFriend UID1 (pass s UID1) UID2) \<and>
                                             a \<noteq> Dact (dFriend UID2 (pass s UID2) UID1)")
              case True
                obtain ou1 s1' where step1: "step s1 a = (ou1, s1')" by (cases "step s1 a") auto
                let ?trn1 = "Trans s1 a ou1 s1'"
                from True n\<phi> have n\<phi>': "\<not>\<phi> ?trn1"
                  using eqButUID_step_\<phi>[OF ss1 rs rs1 step step1] by auto
                then have f12s1': "friends12 s1 = friends12 s1'"
                      and pFRs': "UID1 \<in>\<in> pendingFReqs s1 UID2 \<longleftrightarrow> UID1 \<in>\<in> pendingFReqs s1' UID2"
                                 "UID2 \<in>\<in> pendingFReqs s1 UID1 \<longleftrightarrow> UID2 \<in>\<in> pendingFReqs s1' UID1"
                  using step_friends12_\<phi>[OF step1] step_pendingFReqs_\<phi>[OF step1]
                  by auto
                have "eqButUID s' s1'" using eqButUID_step[OF ss1 step step1 rs rs1] .
                thm \<Delta>3_I[of s' s1' vl'' vl1'' vl1 "fv # fs' ## fv'" "[fv']" vl']
                then have "\<Delta>3 s' vl' s1' vl1" using os vVS1 fs' fs1' BO_FVal
                  unfolding os' f12s1' pFRs' vl'
                  by (intro \<Delta>3_I[of s' s1' vl'' vl1'' vl1 "fv # fs' ## fv'" "[fv']" vl]) auto
                then have ?match
                  using step1 n\<phi>' os eqButUID_step_\<gamma>_out[OF ss1 step step1]
                  by (intro matchI[of s1 a ou1 s1' vl1 vl1]) (auto simp: consume_def)
                then show "?match \<or> ?ignore" ..
            next
              case False
                with n\<phi> have "ou \<noteq> outOK" by auto
                then have "s' = s" using step False by auto
                then have ?ignore using 3 False UID1_UID2_UIDs unfolding vl' by (intro ignoreI) auto
                then show "?match \<or> ?ignore" ..
            qed
          qed
        qed
        then show ?thesis using fs' by auto
    next
      case (BO_FVal1 fv fv' fs' fs1' vl'' vl1'')
        then have fs': "filter (Not o isFRVal) vl = map FVal (fs' ## fv') @ OVal True # vl''"
              and fs1': "filter (Not o isFRVal) vl1 = map FVal (fv # fs1' ## fv') @ OVal True # vl1''"
          using fs fs1 by auto
        with nFRVal1 obtain vl1'
        where vl1: "vl1 = FVal fv # vl1'"
          and vl1': "filter (Not o isFRVal) vl1' = map FVal (fs1' ## fv') @ OVal True # vl1''"
          by (cases vl1; cases "hd vl1") auto
        with vVS1 have f12: "friends12 s1 \<noteq> fv"
                   and vVS1: "validValSeqFrom (FVal fv # vl1') s1" by auto
        then have ?iact using rs1 IDs1 vl1 ss1 os BO_FVal1(3) fs' vl1'
          by (elim toggle_friends12[of s1 fv vl1'], blast, blast, blast)
             (intro iactionI[of s1 _ _ _ vl1 vl1'],
              auto simp: consume_def
                   intro: \<Delta>3_I[of s _ vl'' vl1'' vl1' "fs' ## fv'" "fs1' ## fv'" vl]
                          eqButUID_trans)
        then show ?thesis ..
    next
      case (FVal_BO fv vl'' vl1'')
        then have fs': "filter (Not o isFRVal) vl = FVal fv # OVal True # vl''"
              and fs1': "filter (Not o isFRVal) vl1 = FVal fv # OVal True # vl1''"
          using fs fs1 by auto
        have ?react proof
          fix a :: act and ou :: out and s' :: state and vl'
          let ?trn = "Trans s a ou s'"  let ?trn1 = "Trans s1 a ou s'"
          assume step: "step s a = (ou, s')" and T: "\<not> T ?trn" and c: "consume ?trn vl vl'"
          show "match ?\<Delta> s s1 vl1 a ou s' vl' \<or> ignore ?\<Delta> s s1 vl1 a ou s' vl'" (is "?match \<or> ?ignore")
          proof cases
            assume \<phi>: "\<phi> ?trn"
            with c have vl: "vl = f ?trn # vl'" by (auto simp: consume_def)
            with fs' show ?thesis proof (cases "f ?trn")
              case (FRVal u req)
                obtain p
                where a: "(a = Cact (cFriendReq UID1 p UID2 req) \<and> UID1 \<in>\<in> pendingFReqs s' UID2 \<and>
                           UID1 \<notin> set (pendingFReqs s UID2) \<and>
                           (UID2 \<in>\<in> pendingFReqs s' UID1 \<longleftrightarrow> UID2 \<in>\<in> pendingFReqs s UID1)) \<or>
                          (a = Cact (cFriendReq UID2 p UID1 req) \<and> UID2 \<in>\<in> pendingFReqs s' UID1 \<and>
                           UID2 \<notin> set (pendingFReqs s UID1) \<and>
                           (UID1 \<in>\<in> pendingFReqs s' UID2 \<longleftrightarrow> UID1 \<in>\<in> pendingFReqs s UID2))"
                         "ou = outOK" "\<not>friends12 s" "\<not>friends12 s'" "open s' = open s"
                  using \<phi> step rs FRVal by (cases rule: \<phi>E) fastforce+
                then have fIDs': "friendIDs s' = friendIDs s" using step by (auto simp: c_defs)
                have "eqButUID s s'" using a step
                  by (auto intro: Cact_cFriendReq_step_eqButUID)
                then have "\<Delta>3 s' vl' s1 vl1"
                  using ss1 a os BO vVS1 fs_fs1 last_fs fs_fIDs fs fs1 fIDs' vl FRVal
                  by (intro \<Delta>3_I[of s' s1 vlr vlr1 vl1 fs fs1 vl'])
                     (auto intro: eqButUID_trans eqButUID_sym)
                moreover from a have "\<not>\<gamma> (Trans s a ou s')"
                  using UID1_UID2_UIDs by auto
                ultimately have ?ignore by (intro ignoreI) auto
                then show ?thesis ..
            next
              case (FVal fv'')
                with vl fs' have FVal: "f ?trn = FVal fv"
                             and vl': "filter (Not \<circ> isFRVal) vl' = OVal True # vl''"
                  by auto
                from fs1' nFRVal1 obtain vl1'
                where vl1: "vl1 = FVal fv # vl1'"
                  and vl1': "filter (Not \<circ> isFRVal) vl1' = OVal True # vl1''"
                  by (cases vl1; cases "hd vl1") auto
                have ?match using \<phi> step rs FVal proof (cases rule: \<phi>E)
                  case (Friend uid p uid')
                    then have IDs1: "IDsOK s1 [UID1, UID2] []"
                          and f12s1: "\<not>friends12 s1"
                          and fv: "fv = True"
                      using ss1 vVS1 FVal unfolding eqButUID_def vl1 by auto
                    let ?s1' = "createFriend s1 UID1 (pass s1 UID1) UID2"
                    have s': "s' = createFriend s UID1 p UID2"
                      using Friend step by (auto simp: createFriend_sym)
                    have ss': "eqButUID s s'" using rs step Friend
                      by (auto intro: Cact_cFriend_step_eqButUID)
                    moreover then have os': "\<not>open s'" using os eqButUID_open_eq by auto
                    moreover obtain a1 uid1 uid1' p1
                    where "step s1 a1 = (outOK, ?s1')" "friends12 ?s1'"
                          "a1 = Cact (cFriend uid1 p1 uid1')"
                          "uid1 = UID1 \<and> uid1' = UID2 \<or> uid1 = UID2 \<and> uid1' = UID1"
                          "\<phi> (Trans s1 a1 outOK ?s1')"
                          "f (Trans s1 a1 outOK ?s1') = FVal True"
                          "eqButUID s1 ?s1'" "validValSeqFrom vl1' ?s1'"
                      using rs1 IDs1 Friend vVS1 f12s1 unfolding vl1 FVal
                      by (elim toggle_friends12_True; blast)
                    moreover then have "IDsOK ?s1' [UID1, UID2] []" by (auto simp: c_defs)
                    moreover have "friendIDs s' = friendIDs ?s1'"
                      using Friend(6) f12s1 unfolding s'
                      by (intro eqButUID_createFriend12_friendIDs_eq[OF ss1 rs rs1]) auto
                    ultimately show ?match
                      using ss1 FVal_BO Friend UID1_UID2_UIDs vl' vl1' unfolding vl1 fv
                      by (intro matchI[of s1 a1 "outOK" ?s1'])
                         (auto simp: consume_def intro: eqButUID_trans eqButUID_sym
                               intro!: \<Delta>3_I[of s' ?s1' vl'' vl1'' vl1' "[]" "[]" vl'])
                next
                  case (Unfriend uid p uid')
                    then have IDs1: "IDsOK s1 [UID1, UID2] []"
                          and f12s1: "friends12 s1"
                          and fv: "fv = False"
                      using ss1 vVS1 FVal unfolding eqButUID_def vl1 by auto
                    let ?s1' = "deleteFriend s1 UID1 (pass s1 UID1) UID2"
                    have s': "s' = deleteFriend s UID1 p UID2"
                      using Unfriend step by (auto simp: deleteFriend_sym)
                    have ss': "eqButUID s s'" using rs step Unfriend
                      by (auto intro: Dact_dFriend_step_eqButUID)
                    moreover then have os': "\<not>open s'" using os eqButUID_open_eq by auto
                    moreover obtain a1 uid1 uid1' p1
                    where "step s1 a1 = (outOK, ?s1')" "\<not>friends12 ?s1'"
                          "a1 = Dact (dFriend uid1 p1 uid1')"
                          "uid1 = UID1 \<and> uid1' = UID2 \<or> uid1 = UID2 \<and> uid1' = UID1"
                          "\<phi> (Trans s1 a1 outOK ?s1')"
                          "f (Trans s1 a1 outOK ?s1') = FVal False"
                          "eqButUID s1 ?s1'" "validValSeqFrom vl1' ?s1'"
                      using rs1 IDs1 Unfriend vVS1 f12s1 unfolding vl1 FVal
                      by (elim toggle_friends12_False; blast)
                    moreover then have "IDsOK ?s1' [UID1, UID2] []" by (auto simp: d_defs)
                    moreover have "friendIDs s' = friendIDs ?s1'"
                      using Unfriend(6) f12s1 unfolding s'
                      by (intro eqButUID_deleteFriend12_friendIDs_eq[OF ss1 rs rs1])
                    ultimately show ?match
                      using ss1 FVal_BO Unfriend UID1_UID2_UIDs vl' vl1' unfolding vl1 fv
                      by (intro matchI[of s1 a1 "outOK" ?s1'])
                         (auto simp: consume_def intro: eqButUID_trans eqButUID_sym
                               intro!: \<Delta>3_I[of s' ?s1' vl'' vl1'' vl1' "[]" "[]" vl'])
                qed auto
                then show ?thesis ..
            qed auto
          next
            assume n\<phi>: "\<not>\<phi> ?trn"
            then have os': "open s = open s'" and f12s': "friends12 s = friends12 s'"
              using step_open_\<phi>[OF step] step_friends12_\<phi>[OF step] by auto
            have vl': "vl' = vl" using n\<phi> c by (auto simp: consume_def)
            show ?thesis proof (cases "\<forall>req. a \<noteq> Cact (cFriend UID1 (pass s UID1) UID2) \<and>
                                             a \<noteq> Cact (cFriend UID2 (pass s UID2) UID1) \<and>
                                             a \<noteq> Cact (cFriendReq UID2 (pass s UID2) UID1 req) \<and>
                                             a \<noteq> Cact (cFriendReq UID1 (pass s UID1) UID2 req) \<and>
                                             a \<noteq> Dact (dFriend UID1 (pass s UID1) UID2) \<and>
                                             a \<noteq> Dact (dFriend UID2 (pass s UID2) UID1)")
              case True
                obtain ou1 s1' where step1: "step s1 a = (ou1, s1')" by (cases "step s1 a") auto
                let ?trn1 = "Trans s1 a ou1 s1'"
                from True n\<phi> have n\<phi>': "\<not>\<phi> ?trn1"
                  using eqButUID_step_\<phi>[OF ss1 rs rs1 step step1] by auto
                then have f12s1': "friends12 s1 = friends12 s1'"
                      and pFRs': "UID1 \<in>\<in> pendingFReqs s1 UID2 \<longleftrightarrow> UID1 \<in>\<in> pendingFReqs s1' UID2"
                                 "UID2 \<in>\<in> pendingFReqs s1 UID1 \<longleftrightarrow> UID2 \<in>\<in> pendingFReqs s1' UID1"
                  using step_friends12_\<phi>[OF step1] step_pendingFReqs_\<phi>[OF step1]
                  by auto
                have "eqButUID s' s1'" using eqButUID_step[OF ss1 step step1 rs rs1] .
                thm \<Delta>3_I[of s' s1' vl'' vl1'' vl1 "[fv]" "[fv]" vl']
                then have "\<Delta>3 s' vl' s1' vl1" using os vVS1 fs' fs1' FVal_BO
                  unfolding os' f12s1' pFRs' vl'
                  by (intro \<Delta>3_I[of s' s1' vl'' vl1'' vl1 "[fv]" "[fv]" vl]) auto
                then have ?match
                  using step1 n\<phi>' os eqButUID_step_\<gamma>_out[OF ss1 step step1]
                  by (intro matchI[of s1 a ou1 s1' vl1 vl1]) (auto simp: consume_def)
                then show "?match \<or> ?ignore" ..
            next
              case False
                with n\<phi> have "ou \<noteq> outOK" by auto
                then have "s' = s" using step False by auto
                then have ?ignore using 3 False UID1_UID2_UIDs unfolding vl' by (intro ignoreI) auto
                then show "?match \<or> ?ignore" ..
            qed
          qed
        qed
        then show ?thesis using fs' by auto
    next
      case (OVal vl'' vl1'')
        then have fs': "filter (Not o isFRVal) vl = OVal True # vl''"
              and fs1': "filter (Not o isFRVal) vl1 = OVal True # vl1''"
              and BO'': "BO vl'' vl1''"
          using fs fs1 by auto
        from fs fs' have fs: "fs = []" by (cases fs) auto
        with fs_fIDs have fIDs: "friendIDs s = friendIDs s1" by auto
        have ?react proof
          fix a :: act and ou :: out and s' :: state and vl'
          let ?trn = "Trans s a ou s'"  let ?trn1 = "Trans s1 a ou s'"
          assume step: "step s a = (ou, s')" and T: "\<not> T ?trn" and c: "consume ?trn vl vl'"
          show "match ?\<Delta> s s1 vl1 a ou s' vl' \<or> ignore ?\<Delta> s s1 vl1 a ou s' vl'" (is "?match \<or> ?ignore")
          proof cases
            assume \<phi>: "\<phi> ?trn"
            with c have vl: "vl = f ?trn # vl'" by (auto simp: consume_def)
            with fs' show ?thesis proof (cases "f ?trn")
              case (FRVal u req)
                obtain p
                where a: "(a = Cact (cFriendReq UID1 p UID2 req) \<and> UID1 \<in>\<in> pendingFReqs s' UID2 \<and>
                           UID1 \<notin> set (pendingFReqs s UID2) \<and>
                           (UID2 \<in>\<in> pendingFReqs s' UID1 \<longleftrightarrow> UID2 \<in>\<in> pendingFReqs s UID1)) \<or>
                          (a = Cact (cFriendReq UID2 p UID1 req) \<and> UID2 \<in>\<in> pendingFReqs s' UID1 \<and>
                           UID2 \<notin> set (pendingFReqs s UID1) \<and>
                           (UID1 \<in>\<in> pendingFReqs s' UID2 \<longleftrightarrow> UID1 \<in>\<in> pendingFReqs s UID2))"
                         "ou = outOK" "\<not>friends12 s" "\<not>friends12 s'" "open s' = open s"
                  using \<phi> step rs FRVal by (cases rule: \<phi>E) fastforce+
                then have fIDs': "friendIDs s' = friendIDs s" using step by (auto simp: c_defs)
                have "eqButUID s s'" using a step
                  by (auto intro: Cact_cFriendReq_step_eqButUID)
                then have "\<Delta>3 s' vl' s1 vl1"
                  using ss1 a os OVal(3) vVS1 fs' fs1' fs fs_fs1 fIDs' fIDs unfolding vl FRVal
                  by (intro \<Delta>3_I[of s' s1 vl'' vl1'' vl1 fs fs1 vl'])
                     (auto intro: eqButUID_trans eqButUID_sym)
                moreover from \<phi> step rs a have "\<not>\<gamma> (Trans s a ou s')"
                  using UID1_UID2_UIDs by auto
                ultimately have ?ignore by (intro ignoreI) auto
                then show ?thesis ..
            next
              case (OVal ov')
                with vl fs' have OVal: "f ?trn = OVal True"
                             and vl': "filter (Not \<circ> isFRVal) vl' = vl''"
                  by auto
                from fs1' nFRVal1 obtain vl1'
                where vl1: "vl1 = OVal True # vl1'"
                  and vl1': "filter (Not \<circ> isFRVal) vl1' = vl1''"
                  by (cases vl1; cases "hd vl1") auto
                have ?match using \<phi> step rs OVal proof (cases rule: \<phi>E)
                  case (OpenF uid p uid')
                    let ?s1' = "createFriend s1 uid p uid'"
                    have s': "s' = createFriend s uid p uid'"
                      using OpenF step by auto
                    from OpenF(2) have uids: "uid \<noteq> UID1 \<and> uid \<noteq> UID2 \<and> uid' = UID1 \<or>
                                        uid \<noteq> UID1 \<and> uid \<noteq> UID2 \<and> uid' = UID2 \<or>
                                        uid' \<noteq> UID1 \<and> uid' \<noteq> UID2 \<and> uid = UID1 \<or>
                                        uid' \<noteq> UID1 \<and> uid' \<noteq> UID2 \<and> uid = UID2"
                      using UID1_UID2_UIDs by auto
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
                                  "UID1 \<in>\<in> pendingFReqs s1 UID2 \<longleftrightarrow> UID1 \<in>\<in> pendingFReqs ?s1' UID2"
                                  "UID2 \<in>\<in> pendingFReqs s1 UID1 \<longleftrightarrow> UID2 \<in>\<in> pendingFReqs ?s1' UID1"
                      using uids unfolding friends12_def c_defs by auto
                    moreover then have "validValSeqFrom vl1' ?s1'" using vVS1 unfolding vl1 by auto
                    ultimately have "\<Delta>1 s' vl' ?s1' vl1'"
                      using BO'' IDsOK_mono[OF step1 IDs1] unfolding \<Delta>1_def vl' vl1' by auto
                    moreover have "\<phi> ?trn \<longleftrightarrow> \<phi> (Trans s1 a outOK ?s1')"
                      using OpenF(1) uids by (intro eqButUID_step_\<phi>[OF ss1 rs rs1 step step1]) auto
                    ultimately show ?match using step1 \<phi> OpenF(1,3,4) unfolding vl1
                      by (intro matchI[of s1 a outOK ?s1' _ vl1']) (auto simp: consume_def)
                qed auto
                then show ?thesis ..
            qed auto
        next
          assume n\<phi>: "\<not>\<phi> ?trn"
            then have os': "open s = open s'" and f12s': "friends12 s = friends12 s'"
              using step_open_\<phi>[OF step] step_friends12_\<phi>[OF step] by auto
            have vl': "vl' = vl" using n\<phi> c by (auto simp: consume_def)
            show ?thesis proof (cases "\<forall>req. a \<noteq> Cact (cFriend UID1 (pass s UID1) UID2) \<and>
                                             a \<noteq> Cact (cFriend UID2 (pass s UID2) UID1) \<and>
                                             a \<noteq> Cact (cFriendReq UID2 (pass s UID2) UID1 req) \<and>
                                             a \<noteq> Cact (cFriendReq UID1 (pass s UID1) UID2 req) \<and>
                                             a \<noteq> Dact (dFriend UID1 (pass s UID1) UID2) \<and>
                                             a \<noteq> Dact (dFriend UID2 (pass s UID2) UID1)")
              case True
                obtain ou1 s1' where step1: "step s1 a = (ou1, s1')" by (cases "step s1 a") auto
                let ?trn1 = "Trans s1 a ou1 s1'"
                from True n\<phi> have n\<phi>': "\<not>\<phi> ?trn1"
                  using eqButUID_step_\<phi>[OF ss1 rs rs1 step step1] by auto
                then have f12s1': "friends12 s1 = friends12 s1'"
                      and pFRs': "UID1 \<in>\<in> pendingFReqs s1 UID2 \<longleftrightarrow> UID1 \<in>\<in> pendingFReqs s1' UID2"
                                 "UID2 \<in>\<in> pendingFReqs s1 UID1 \<longleftrightarrow> UID2 \<in>\<in> pendingFReqs s1' UID1"
                  using step_friends12_\<phi>[OF step1] step_pendingFReqs_\<phi>[OF step1]
                  by auto
                have "eqButUID s' s1'" using eqButUID_step[OF ss1 step step1 rs rs1] .
                moreover have "friendIDs s' = friendIDs s1'"
                  using eqButUID_step_friendIDs_eq[OF ss1 rs rs1 step step1 _ fIDs] True
                  by auto
                ultimately have "\<Delta>3 s' vl' s1' vl1" using os vVS1 fs' fs1' OVal
                  unfolding os' f12s1' pFRs' vl'
                  by (intro \<Delta>3_I[of s' s1' vl'' vl1'' vl1 "[]" "[]" vl]) auto
                then have ?match
                  using step1 n\<phi>' os eqButUID_step_\<gamma>_out[OF ss1 step step1]
                  by (intro matchI[of s1 a ou1 s1' vl1 vl1]) (auto simp: consume_def)
                then show "?match \<or> ?ignore" ..
            next
              case False
                with n\<phi> have "ou \<noteq> outOK" by auto
                then have "s' = s" using step False by auto
                then have ?ignore using 3 False UID1_UID2_UIDs unfolding vl' by (intro ignoreI) auto
                then show "?match \<or> ?ignore" ..
            qed
          qed
        qed
        then show ?thesis using fs' by auto
    next
      case (FVal1 fv fs' fs1')
        from this(1) have "False" proof (induction fs' arbitrary: fs)
          case (Cons fv'' fs'')
            then obtain fs''' where "map FVal (fv'' # fs''') @ OVal True # vlr = map FVal (fv'' # fs'')"
              by (cases fs) auto
            with Cons.IH[of fs'''] show "False" by auto
        qed auto
        then show ?thesis ..
    next
      case (FVal) then show ?thesis by (induction fs) auto next
      case (Nil) then show ?thesis by auto
    qed
  qed
qed



definition Gr where
"Gr =
 {
 (\<Delta>0, {\<Delta>0,\<Delta>1,\<Delta>2,\<Delta>3}),
 (\<Delta>1, {\<Delta>1,\<Delta>2,\<Delta>3}),
 (\<Delta>2, {\<Delta>2,\<Delta>1}),
 (\<Delta>3, {\<Delta>3,\<Delta>1})
 }"


theorem secure: secure
apply (rule unwind_decomp_secure_graph[of Gr \<Delta>0])
unfolding Gr_def
apply (simp, smt insert_subset order_refl)
using
istate_\<Delta>0 unwind_cont_\<Delta>0 unwind_cont_\<Delta>1 unwind_cont_\<Delta>2 unwind_cont_\<Delta>3
unfolding Gr_def by (auto intro: unwind_cont_mono)

end
