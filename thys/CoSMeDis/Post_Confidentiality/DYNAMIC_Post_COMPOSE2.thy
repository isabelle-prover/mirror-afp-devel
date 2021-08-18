theory DYNAMIC_Post_COMPOSE2
  imports
    DYNAMIC_Post_ISSUER
    Post_RECEIVER
    "BD_Security_Compositional.Composing_Security"
begin

subsubsection \<open>Confidentiality for the (binary) issuer-receiver composition\<close>

type_synonym ttrans = "(state, act, out) trans"
type_synonym value1 = Post.value  type_synonym value2 = Post_RECEIVER.value
type_synonym obs1 = Post_Observation_Setup_ISSUER.obs
type_synonym obs2 = Post_Observation_Setup_RECEIVER.obs

(* irrelevant for the security conditions: *)
datatype cval = PValC post
type_synonym cobs = "obs1 \<times> obs2"

locale Post_COMPOSE2 =
  Iss: Post UIDs PID +
  Rcv: Post_RECEIVER UIDs2 PID AID1
for UIDs :: "userID set" and UIDs2 :: "userID set" and
   AID1 :: "apiID" and PID :: "postID"
+ fixes AID2 :: "apiID"
begin

abbreviation "\<phi>1 \<equiv> Iss.\<phi>"  abbreviation "f1 \<equiv> Iss.f" abbreviation "\<gamma>1 \<equiv> Iss.\<gamma>"  abbreviation "g1 \<equiv> Iss.g"
  abbreviation "T1 \<equiv> Iss.T"  abbreviation "B1 \<equiv> Iss.B"
abbreviation "\<phi>2 \<equiv> Rcv.\<phi>"  abbreviation "f2 \<equiv> Rcv.f" abbreviation "\<gamma>2 \<equiv> Rcv.\<gamma>"  abbreviation "g2 \<equiv> Rcv.g"
  abbreviation "T2 \<equiv> Rcv.T"  abbreviation "B2 \<equiv> Rcv.B"

(* Recall that we assume that the system prevents communication if error occurs: *)
fun isCom1 :: "ttrans \<Rightarrow> bool" where
 "isCom1 (Trans s (COMact ca1) ou1 s') = (ou1 \<noteq> outErr)"
|"isCom1 _ = False"

fun isCom2 :: "ttrans \<Rightarrow> bool" where
 "isCom2 (Trans s (COMact ca2) ou2 s') = (ou2 \<noteq> outErr)"
|"isCom2 _ = False"

fun isComV1 :: "value1 \<Rightarrow> bool" where
 "isComV1 (Iss.PValS aid1 pst1) = True"
|"isComV1 _ = False"

fun isComV2 :: "value2 \<Rightarrow> bool" where
 "isComV2 (Rcv.PValR pst2) = True"
(* |"isComV2 _ = False" *)

fun syncV :: "value1 \<Rightarrow> value2 \<Rightarrow> bool" where
 "syncV (Iss.PValS aud1 pst1) (Rcv.PValR pst2) = (pst1 = pst2)"
|"syncV _ _ = False"

(* irrelevant for the security conditions: *)
fun cmpV :: "value1 \<Rightarrow> value2 \<Rightarrow> cval"  where
 "cmpV (Iss.PValS aid1 pst1) (Rcv.PValR pst2) = PValC pst1"
|"cmpV _ _ = undefined"

fun isComO1 :: "obs1 \<Rightarrow> bool" where
 "isComO1 (COMact ca1, ou1) = (ou1 \<noteq> outErr)"
|"isComO1 _ = False"

fun isComO2 :: "obs2 \<Rightarrow> bool" where
 "isComO2 (COMact ca2, ou2) = (ou2 \<noteq> outErr)"
|"isComO2 _ = False"

fun comSyncOA :: "out \<Rightarrow> comActt \<Rightarrow> bool" where
 "comSyncOA (O_sendServerReq (aid2, reqInfo1)) (comReceiveClientReq aid1 reqInfo2) =
   (aid1 = AID1 \<and> aid2 = AID2 \<and> reqInfo1 = reqInfo2)"
|"comSyncOA (O_connectClient (aid2, sp1)) (comConnectServer aid1 sp2) =
   (aid1 = AID1 \<and> aid2 = AID2 \<and> sp1 = sp2)"
|"comSyncOA (O_sendPost (aid2, sp1, pid1, pst1, uid1, vs1)) (comReceivePost aid1 sp2 pid2 pst2 uid2 vs2) =
   (aid1 = AID1 \<and> aid2 = AID2 \<and> (pid1, pst1, uid1, vs1) = (pid2, pst2, uid2, vs2))"
|"comSyncOA (O_sendCreateOFriend (aid2, sp1, uid1, uid1')) (comReceiveCreateOFriend aid1 sp2 uid2 uid2') =
   (aid1 = AID1 \<and> aid2 = AID2 \<and> (uid1, uid1') = (uid2, uid2'))"
|"comSyncOA (O_sendDeleteOFriend (aid2, sp1, uid1, uid1')) (comReceiveDeleteOFriend aid1 sp2 uid2 uid2') =
   (aid1 = AID1 \<and> aid2 = AID2 \<and> (uid1, uid1') = (uid2, uid2'))"
|"comSyncOA _ _ = False"

fun syncO :: "obs1 \<Rightarrow> obs2 \<Rightarrow> bool" where
 "syncO (COMact ca1, ou1) (COMact ca2, ou2) =
  (ou1 \<noteq> outErr \<and> ou2 \<noteq> outErr \<and>
   (comSyncOA ou1 ca2 \<or> comSyncOA ou2 ca1)
  )"
|"syncO _ _ = False"

fun sync :: "ttrans \<Rightarrow> ttrans \<Rightarrow> bool" where
"sync (Trans s1 a1 ou1 s1') (Trans s2 a2 ou2 s2') = syncO (a1, ou1) (a2, ou2)"

(* irrelevant for the security conditions: *)
definition cmpO :: "obs1 \<Rightarrow> obs2 \<Rightarrow> cobs"  where
"cmpO o1 o2 \<equiv> (o1,o2)"


(*  *)



lemma isCom1_isComV1:
assumes v: "validTrans trn1" and r: "reach (srcOf trn1)" and \<phi>1: "\<phi>1 trn1"
shows "isCom1 trn1 \<longleftrightarrow> isComV1 (f1 trn1)"
proof (cases trn1)
  case (Trans s1 a1 o1 s1')
  hence step: "step s1 a1 = (o1, s1')" using v by simp
  show ?thesis using \<phi>1[unfolded Trans] unfolding Iss.\<phi>_def3[OF step]
  proof (elim exE disjE conjE)
    assume "Iss.open s1 \<noteq> Iss.open s1'"
    and a1: "\<not> isCOMact a1" "\<not> (\<exists> ua. isuPost ua \<and> a1 = Uact ua)"
    hence "Iss.f (Trans s1 a1 o1 s1') = Iss.OVal (Iss.open s1')" using Iss.f_open_OVal[OF step] by auto
    thus ?thesis unfolding Trans using a1 by (cases a1) auto
  qed(unfold Trans, auto)
qed

lemma isCom1_isComO1:
assumes "validTrans trn1" and "reach (srcOf trn1)" and "\<gamma>1 trn1"
shows "isCom1 trn1 \<longleftrightarrow> isComO1 (g1 trn1)"
using assms apply(cases trn1)
subgoal for _ x2 apply(cases x2) by auto .

lemma isCom2_isComV2:
assumes "validTrans trn2" and "reach (srcOf trn2)" and "\<phi>2 trn2"
shows "isCom2 trn2 \<longleftrightarrow> isComV2 (f2 trn2)"
using assms apply(cases trn2) by (auto simp: Rcv.\<phi>_def2 split: prod.splits)

lemma isCom2_isComO2:
assumes "validTrans trn2" and "reach (srcOf trn2)" and "\<gamma>2 trn2"
shows "isCom2 trn2 \<longleftrightarrow> isComO2 (g2 trn2)"
using assms apply(cases trn2)
subgoal for _ x2 apply(cases x2) by auto .

lemma sync_syncV:
assumes v1: "validTrans trn1" and "reach (srcOf trn1)"
and v2: "validTrans trn2" and "reach (srcOf trn2)"
and c1: "isCom1 trn1" and c2: "isCom2 trn2" and \<phi>1: "\<phi>1 trn1" and \<phi>2: "\<phi>2 trn2"
and snc: "sync trn1 trn2"
shows "syncV (f1 trn1) (f2 trn2)"
proof (cases trn1)
  case (Trans s1 a1 o1 s1') note trn1 = Trans
  show ?thesis proof(cases trn2)
    case (Trans s2 a2 o2 s2') note trn2 = Trans
    have step1: "step s1 a1 = (o1, s1')" and step2: "step s2 a2 = (o2, s2')"
    using v1 v2 trn1 trn2 by auto
    obtain uid2 pst2 vs2
    where a2: "a2 = COMact
        (comReceivePost AID1 (serverPass s2 AID1) PID pst2 uid2 vs2)"
    and o2: "o2 = outOK" using \<phi>2[unfolded trn2]
    unfolding Rcv.\<phi>_def3[OF step2] by auto
    hence f2: "Rcv.f trn2 = Rcv.PValR pst2" unfolding trn2 by simp
    show ?thesis using \<phi>1[unfolded trn1]
    unfolding Iss.\<phi>_def3[OF step1]
    proof (elim exE disjE conjE)
      assume "Iss.open s1 \<noteq> Iss.open s1'"
      and a1: "\<not> isCOMact a1" "\<not> (\<exists> ua. isuPost ua \<and> a1 = Uact ua)"
      hence f1: "Iss.f (Trans s1 a1 o1 s1') = Iss.OVal (Iss.open s1')"
      using Iss.f_open_OVal step1 step2 by auto
      thus ?thesis using a1 c1 c2 unfolding trn1 trn2 a2 o2 f2
      by (cases a1, auto)
    qed(insert snc c1 c2, unfold trn1 trn2 a2, auto)
  qed
qed

lemma sync_syncO:
assumes "validTrans trn1" and "reach (srcOf trn1)"
and "validTrans trn2" and "reach (srcOf trn2)"
and "isCom1 trn1" and "isCom2 trn2" and "\<gamma>1 trn1" and "\<gamma>2 trn2"
and "sync trn1 trn2"
shows "syncO (g1 trn1) (g2 trn2)"
proof(cases trn1)
  case (Trans s1 a1 ou1 s1') note trn1 = Trans
  show ?thesis proof(cases trn2)
    case (Trans s2 a2 ou2 s2') note trn2 = Trans
    show ?thesis
    proof(cases a1)
      case (COMact ca1) note a1 = COMact
      show ?thesis
      proof(cases a2)
        case (COMact ca2) note a2 = COMact
        show ?thesis
        using assms unfolding trn1 trn2 a1 a2
        apply(cases ca1) by (cases ca2, auto split: prod.splits)+
      qed(insert assms, unfold trn1 trn2, auto)
    qed(insert assms, unfold trn1 trn2, auto)
  qed
qed

lemma sync_\<phi>1_\<phi>2:
assumes v1: "validTrans trn1" and r1: "reach (srcOf trn1)"
and v2: "validTrans trn2" and s2: "reach (srcOf trn2)"
and c1: "isCom1 trn1" and c2: "isCom2 trn2"
and sn: "sync trn1 trn2"
shows "\<phi>1 trn1 \<longleftrightarrow> \<phi>2 trn2" (is "?A \<longleftrightarrow> ?B")
proof(cases trn1)
  case (Trans s1 a1 ou1 s1') note trn1 = Trans
  hence step1: "step s1 a1 = (ou1,s1')" using v1 by auto
  show ?thesis proof(cases trn2)
    case (Trans s2 a2 ou2 s2') note trn2 = Trans
    hence step2: "step s2 a2 = (ou2,s2')" using v2 by auto
    show ?thesis
    proof(cases a1)
      case (COMact ca1) note a1 = COMact
      show ?thesis
      proof(cases a2)
        case (COMact ca2) note a2 = COMact

        have "?A \<longleftrightarrow> (\<exists>aid1. ca1 =
             (comSendPost (admin s1) (pass s1 (admin s1)) aid1
               PID) \<and>
            ou1 =
            O_sendPost
             (aid1, clientPass s1 aid1, PID, post s1 PID,
              owner s1 PID, vis s1 PID))"
        using c1 unfolding trn1 Iss.\<phi>_def3[OF step1] unfolding a1 by auto
        also have "\<dots> \<longleftrightarrow> (\<exists>uid2 pst2 vs2.
        ca2 = comReceivePost AID1 (serverPass s2 AID1) PID pst2 uid2 vs2 \<and> ou2 = outOK)"
        using sn step1 step2 unfolding trn1 trn2 a1 a2
        apply(cases ca1) by (cases ca2, auto simp: all_defs)+
        also have "\<dots> \<longleftrightarrow> ?B"
        using c2 unfolding trn2 Rcv.\<phi>_def3[OF step2] unfolding a2 by auto
        finally show ?thesis .
      qed(insert assms, unfold trn1 trn2, auto)
    qed(insert assms, unfold trn1 trn2, auto)
  qed
qed

lemma textPost_textPost_cong[intro]:
assumes "textPost pst1 = textPost pst2"
and "setTextPost pst1 emptyText = setTextPost pst2 emptyText"
shows "pst1 = pst2"
using assms by (cases pst1, cases pst2) auto

lemma sync_\<phi>_\<gamma>:
assumes "validTrans trn1" and "reach (srcOf trn1)"
and "validTrans trn2" and "reach (srcOf trn2)"
and "isCom1 trn1" and "isCom2 trn2"
and "\<gamma>1 trn1" and "\<gamma>2 trn2"
and so: "syncO (g1 trn1) (g2 trn2)"
and "\<phi>1 trn1 \<Longrightarrow> \<phi>2 trn2 \<Longrightarrow> syncV (f1 trn1) (f2 trn2)"
shows "sync trn1 trn2"
proof(cases trn1, cases trn2)
  fix s1 a1 ou1 s1' s2 a2 ou2 s2'
  assume trn1: "trn1 = Trans s1 a1 ou1 s1'"
  and trn2: "trn2 = Trans s2 a2 ou2 s2'"
  hence step1: "step s1 a1 = (ou1,s1')" and step2: "step s2 a2 = (ou2,s2')" using assms by auto
  show ?thesis
  proof(cases a1)
    case (COMact ca1) note a1 = COMact
    show ?thesis
    proof(cases a2)
      case (COMact ca2) note a2 = COMact
      show ?thesis
      proof(cases ca1)   term comReceivePost
        case (comSendPost uid1 p1 aid1 pid) note ca1 = comSendPost
        then obtain pst where p1: "p1 = pass s1 (admin s1)" and
        aid1: "aid1 = AID2" and ou2: "ou2 = outOK" and ou1: "ou1 \<noteq> outErr" and
        ca2: "ca2 = comReceivePost AID1 (serverPass s2 AID1) pid pst (owner s1 pid) (vis s1 pid)"
        using so step1 step2 unfolding trn1 trn2 a1 a2 ca1
        by (cases ca2, auto simp: all_defs)
        have ou1: "ou1 = O_sendPost (AID2,clientPass s1 AID2,pid, post s1 pid, owner s1 pid, vis s1 pid)"
        using step1 ou1 unfolding a1 ca1 aid1 by (auto simp: all_defs)
        show ?thesis proof(cases "pid = PID")
          case False thus ?thesis using so step1 step2 unfolding trn1 trn2 a1 a2 ca1 ca2
          by (auto simp: all_defs)
        next
          case True  note pid = True
          hence "\<phi>1 trn1 \<and> \<phi>2 trn2" using ou1 ou2 unfolding trn1 trn2 a1 a2 ca1 ca2 by auto
          hence "syncV (f1 trn1) (f2 trn2)" using assms by simp
          hence pst: "pst = post s1 PID" using pid unfolding trn1 trn2 a1 a2 ca1 ca2 aid1 ou1 by auto
          show ?thesis unfolding trn1 trn2 a1 a2 ca1 ca2 ou1 ou2 pst pid by auto
        qed
      qed(insert so step1 step2, unfold trn1 trn2 a1 a2, (cases ca2, auto simp: all_defs)+)
    qed(insert assms, unfold trn1 trn2, auto)
  qed(insert assms, unfold trn1 trn2, auto)
qed

lemma isCom1_\<gamma>1:
assumes "validTrans trn1" and "reach (srcOf trn1)" and "isCom1 trn1"
shows "\<gamma>1 trn1"
proof(cases trn1)
  case (Trans s1 a1 ou1 s1')
  thus ?thesis using assms by (cases a1) auto
qed

lemma isCom2_\<gamma>2:
assumes "validTrans trn2" and "reach (srcOf trn2)" and "isCom2 trn2"
shows "\<gamma>2 trn2"
proof(cases trn2)
  case (Trans s2 a2 ou2 s2')
  thus ?thesis using assms by (cases a2) auto
qed

lemma isCom2_V2:
assumes "validTrans trn2" and "reach (srcOf trn2)" and "\<phi>2 trn2"
shows "isCom2 trn2"
proof(cases trn2)
  case (Trans s2 a2 ou2 s2') note trn2 = Trans
  show ?thesis
  proof(cases a2)
    case (COMact ca2)
    thus ?thesis using assms trn2 by (cases ca2) auto
  qed(insert assms trn2, auto)
qed

end (* context Post_COMPOSE2 *)


sublocale Post_COMPOSE2 < BD_Security_TS_Comp where
  istate1 = istate and validTrans1 = validTrans and srcOf1 = srcOf and tgtOf1 = tgtOf
    and \<phi>1 = \<phi>1 and f1 = f1 and \<gamma>1 = \<gamma>1 and g1 = g1 and T1 = T1 and B1 = B1
  and
  istate2 = istate and validTrans2 = validTrans and srcOf2 = srcOf and tgtOf2 = tgtOf
    and \<phi>2 = \<phi>2 and f2 = f2 and \<gamma>2 = \<gamma>2 and g2 = g2 and T2 = T2 and B2 = B2
  and isCom1 = isCom1 and isCom2 = isCom2 and sync = sync
  and isComV1 = isComV1 and isComV2 = isComV2 and syncV = syncV
  and isComO1 = isComO1 and isComO2 = isComO2 and syncO = syncO
apply standard
using isCom1_isComV1 isCom1_isComO1 isCom2_isComV2 isCom2_isComO2
  sync_syncV sync_syncO
apply auto
apply (meson sync_\<phi>1_\<phi>2, meson sync_\<phi>1_\<phi>2)
using sync_\<phi>_\<gamma> apply auto
using isCom1_\<gamma>1 isCom2_\<gamma>2 isCom2_V2 apply auto
by (meson isCom2_V2)


context Post_COMPOSE2
begin


theorem secure: "secure"
  using secure1_secure2_secure[OF Iss.secure Rcv.Post_secure] .


end (* context Post_COMPOSE2 *)

end
