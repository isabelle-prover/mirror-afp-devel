theory Outer_Friend_Receiver
  imports
    "Outer_Friend_Receiver_Value_Setup"
    "Bounded_Deducibility_Security.Compositional_Reasoning"
begin

subsubsection \<open>Declassification bound\<close>

(* We verify the following:
   Given an arbitrary but fixed user UID at node AID (who is not an observer) and a set of
   observers at each network node, the observers may learn about the *occurrence* of remote
   friendship actions of UID (because network traffic is assumed to be observable), but they
   learn nothing about the *content* of those actions (who was added or deleted as a friend)
   beyond public knowledge (friendship addition and deletion occur alternatingly),
   except if the action adds or deletes one of the observers themselves as friend.
*)

context OuterFriendReceiver
begin

fun T :: "(state,act,out) trans \<Rightarrow> bool"
where "T trn = False"

text \<open>For each user \<open>uid\<close> at this receiver node \<open>AID'\<close>, the remote friendship updates with
the fixed user \<open>UID\<close> at the issuer node \<open>AID\<close> form an alternating sequence of friending and unfriending.

Note that actions involving remote users who are observers do not produce secret values;
instead, those actions are observable, and the property we verify does not protect their
confidentiality.

Moreover, there is no declassification trigger on the receiver side, so \<^term>\<open>OVal\<close> values
are never produced by receiver nodes, only by the issuer node.\<close>

definition friendsOfUID :: "state \<Rightarrow> userID set" where
  "friendsOfUID s = {uid. (AID,UID) \<in>\<in> recvOuterFriendIDs s uid \<and> uid \<notin> UIDs AID'}"

fun validValSeq :: "value list \<Rightarrow> userID set \<Rightarrow> bool" where
  "validValSeq [] _ = True"
| "validValSeq (FrVal aid uid True # vl) uids \<longleftrightarrow> uid \<notin> uids \<and> aid = AID' \<and> uid \<notin> UIDs AID' \<and> validValSeq vl (insert uid uids)"
| "validValSeq (FrVal aid uid False # vl) uids \<longleftrightarrow> uid \<in> uids \<and> aid = AID' \<and> uid \<notin> UIDs AID' \<and> validValSeq vl (uids - {uid})"
| "validValSeq (OVal ov # vl) uids \<longleftrightarrow> False"

abbreviation "validValSeqFrom vl s \<equiv> validValSeq vl (friendsOfUID s)"

text \<open>Observers may learn about the occurrence of
remote friendship actions (by observing network traffic), but not their content;
remote friendship actions at a receiver node \<open>AID'\<close> can be replaced by different actions
involving different users of that node (who are not observers)
without affecting the observations.\<close>

inductive BC :: "value list \<Rightarrow> value list \<Rightarrow> bool"
where
  BC_Nil[simp,intro]: "BC [] []"
| BC_FrVal[intro]:
    "BC vl vl1 \<Longrightarrow> uid' \<notin> UIDs AID' \<Longrightarrow> BC (FrVal aid uid st # vl) (FrVal AID' uid' st' # vl1)"

definition "B vl vl1 \<equiv> BC vl vl1 \<and> validValSeqFrom vl1 istate"


lemma BC_Nil_Nil: "BC vl vl1 \<Longrightarrow> vl1 = [] \<longleftrightarrow> vl = []"
by (induction rule: BC.induct) auto

lemma BC_id: "validValSeq vl uids \<Longrightarrow> BC vl vl"
by (induction rule: validValSeq.induct) auto

lemma BC_append: "BC vl vl1 \<Longrightarrow> BC vl' vl1' \<Longrightarrow> BC (vl @ vl') (vl1 @ vl1')"
by (induction rule: BC.induct) auto


sublocale BD_Security_IO where
istate = istate and step = step and
\<phi> = \<phi> and f = f and \<gamma> = \<gamma> and g = g and T = T and B = B
done


subsubsection \<open>Unwinding proof\<close>

definition \<Delta>0 :: "state \<Rightarrow> value list \<Rightarrow> state \<Rightarrow> value list \<Rightarrow> bool" where
"\<Delta>0 s vl s1 vl1 \<equiv> BC vl vl1 \<and> eqButUID s s1 \<and> validValSeqFrom vl1 s1"

lemma istate_\<Delta>0:
assumes B: "B vl vl1"
shows "\<Delta>0 istate vl istate vl1"
using assms unfolding \<Delta>0_def B_def
by auto

lemma friendsOfUID_cong:
assumes "recvOuterFriendIDs s = recvOuterFriendIDs s'"
shows "friendsOfUID s = friendsOfUID s'"
using assms unfolding friendsOfUID_def by auto

lemma friendsOfUID_step_not_UID:
assumes "uid \<noteq> UID \<or> aid \<noteq> AID \<or> uid' \<in> UIDs AID'"
shows "friendsOfUID (receiveCreateOFriend s aid sp uid uid') = friendsOfUID s"
and "friendsOfUID (receiveDeleteOFriend s aid sp uid uid') = friendsOfUID s"
using assms unfolding friendsOfUID_def by (auto simp: com_defs)

lemma friendsOfUID_step_Create_UID:
assumes "uid' \<notin> UIDs AID'"
shows "friendsOfUID (receiveCreateOFriend s AID sp UID uid') = insert uid' (friendsOfUID s)"
using assms unfolding friendsOfUID_def by (auto simp: com_defs)

lemma friendsOfUID_step_Delete_UID:
assumes "e_receiveDeleteOFriend s AID sp UID uid'"
and rs: "reach s"
shows "friendsOfUID (receiveDeleteOFriend s AID sp UID uid') = friendsOfUID s - {uid'}"
using assms reach_distinct_friends_reqs(4) unfolding friendsOfUID_def by (auto simp: com_defs)

lemma step_validValSeqFrom:
assumes step: "step s a = (ou, s')"
and rs: "reach s"
and c: "consume (Trans s a ou s') vl vl'" (is "consume ?trn vl vl'")
and vVS: "validValSeqFrom vl s"
shows "validValSeqFrom vl' s'"
proof cases
  assume "\<phi> ?trn"
  moreover then obtain v where "vl = v # vl'" using c by (cases vl, auto simp: consume_def)
  ultimately show ?thesis using assms
    by (elim \<phi>.elims) (auto simp: consume_def friendsOfUID_step_Create_UID friendsOfUID_step_Delete_UID)
next
  assume n\<phi>: "\<not>\<phi> ?trn"
  then have vl': "vl' = vl" using c by (auto simp: consume_def)
  then show ?thesis using vVS step proof (cases a)
    case (Sact sa) then show ?thesis using assms vl' by (cases sa) (auto simp: s_defs cong: friendsOfUID_cong) next
    case (Cact ca) then show ?thesis using assms vl' by (cases ca) (auto simp: c_defs cong: friendsOfUID_cong) next
    case (Dact da) then show ?thesis using assms vl' by (cases da) (auto simp: d_defs cong: friendsOfUID_cong) next
    case (Uact ua) then show ?thesis using assms vl' by (cases ua) (auto simp: u_defs cong: friendsOfUID_cong) next
    case (COMact ca)
      then show ?thesis using assms vl' n\<phi> proof (cases ca)
        case (comReceiveCreateOFriend aid sp uid uid')
          then show ?thesis using COMact assms n\<phi> by (auto simp: friendsOfUID_step_not_UID consume_def)
      next
        case (comReceiveDeleteOFriend aid sp uid uid')
          then show ?thesis using COMact assms n\<phi> by (auto simp: friendsOfUID_step_not_UID consume_def)
      qed (auto simp: com_defs cong: friendsOfUID_cong)
  qed auto
qed



lemma unwind_cont_\<Delta>0: "unwind_cont \<Delta>0 {\<Delta>0}"
proof(rule, simp)
  fix s s1 :: state and vl vl1 :: "value list"
  assume rsT: "reachNT s" and rs1: "reach s1" and \<Delta>0: "\<Delta>0 s vl s1 vl1"
  then have rs: "reach s" and ss1: "eqButUID s s1" and BC: "BC vl vl1"
        and vVS1: "validValSeqFrom vl1 s1"
    using reachNT_reach unfolding \<Delta>0_def by auto
  show "iaction \<Delta>0 s vl s1 vl1 \<or>
        ((vl = [] \<longrightarrow> vl1 = []) \<and> reaction \<Delta>0 s vl s1 vl1)" (is "?iact \<or> (_ \<and> ?react)")
  proof-
    have ?react proof
      fix a :: act and ou :: out and s' :: state and vl'
      let ?trn = "Trans s a ou s'"
      assume step: "step s a = (ou, s')" and T: "\<not> T ?trn" and c: "consume ?trn vl vl'"
      show "match \<Delta>0 s s1 vl1 a ou s' vl' \<or> ignore \<Delta>0 s s1 vl1 a ou s' vl'" (is "?match \<or> ?ignore")
      proof cases
        assume \<phi>: "\<phi> ?trn"
        with BC c have "?match" proof (cases rule: BC.cases)
          case (BC_FrVal vl'' vl1'' uid' aid uid st st')
            then show ?thesis proof (cases st')
              case True
                let ?a1 = "COMact (comReceiveCreateOFriend AID (serverPass s AID) UID uid')"
                let ?ou1 = "outOK"
                let ?s1' = "receiveCreateOFriend s1 AID (serverPass s AID) UID uid'"
                let ?trn1 = "Trans s1 ?a1 ?ou1 ?s1'"
                have c1: "consume ?trn1 vl1 vl1''" and "vl' = vl''" and "f ?trn = FrVal AID' uid st"
                  using \<phi> c BC_FrVal True by (auto elim: \<phi>.elims simp: consume_def)
                moreover then have a: "a = COMact (comReceiveCreateOFriend AID (serverPass s AID) UID uid)
                                     \<or> a = COMact (comReceiveDeleteOFriend AID (serverPass s AID) UID uid)"
                               and ou: "ou = outOK"
                               and IDs: "IDsOK s [] [] [(AID,[])] []"
                               and uid: "uid \<notin> UIDs AID'"
                  using \<phi> step rs by (auto elim!: \<phi>.elims split: prod.splits simp: com_defs)
                moreover have step1: "step s1 ?a1 = (?ou1, ?s1')"
                  using IDs vVS1 BC_FrVal True ss1 by (auto simp: com_defs eqButUID_def friendsOfUID_def)
                moreover then have "validValSeqFrom vl1'' ?s1'"
                  using vVS1 rs1 c1 by (intro step_validValSeqFrom[OF step1]) auto
                moreover have "eqButUID s' ?s1'"
                  using ss1 recvOFriend_eqButUID[OF step rs a uid]
                  using recvOFriend_eqButUID[OF step1 rs1, of "serverPass s AID" uid'] BC_FrVal(4)
                  by (auto intro: eqButUID_sym eqButUID_trans)
                moreover have "\<gamma> ?trn = \<gamma> ?trn1" and "g ?trn = g ?trn1"
                  using BC_FrVal a ou uid by (auto simp: com_defs)
                ultimately show "?match"
                  using BC_FrVal by (intro matchI[of s1 ?a1 ?ou1 ?s1' vl1 vl1'']) (auto simp: \<Delta>0_def)
            next
              case False
                let ?a1 = "COMact (comReceiveDeleteOFriend AID (serverPass s AID) UID uid')"
                let ?ou1 = "outOK"
                let ?s1' = "receiveDeleteOFriend s1 AID (serverPass s AID) UID uid'"
                let ?trn1 = "Trans s1 ?a1 ?ou1 ?s1'"
                have c1: "consume ?trn1 vl1 vl1''" and "vl' = vl''" and "f ?trn = FrVal AID' uid st"
                  using \<phi> c BC_FrVal False by (auto elim: \<phi>.elims simp: consume_def)
                moreover then have a: "a = COMact (comReceiveCreateOFriend AID (serverPass s AID) UID uid)
                                     \<or> a = COMact (comReceiveDeleteOFriend AID (serverPass s AID) UID uid)"
                               and ou: "ou = outOK"
                               and IDs: "IDsOK s [] [] [(AID,[])] []"
                               and uid: "uid \<notin> UIDs AID'"
                  using \<phi> step rs by (auto elim!: \<phi>.elims split: prod.splits simp: com_defs)
                moreover have step1: "step s1 ?a1 = (?ou1, ?s1')"
                  using IDs vVS1 BC_FrVal False ss1 by (auto simp: com_defs eqButUID_def friendsOfUID_def)
                moreover then have "validValSeqFrom vl1'' ?s1'"
                  using vVS1 rs1 c1 by (intro step_validValSeqFrom[OF step1]) auto
                moreover have "eqButUID s' ?s1'"
                  using ss1 recvOFriend_eqButUID[OF step rs a uid]
                  using recvOFriend_eqButUID[OF step1 rs1, of "serverPass s AID" uid'] BC_FrVal(4)
                  by (auto intro: eqButUID_sym eqButUID_trans)
                moreover have "\<gamma> ?trn = \<gamma> ?trn1" and "g ?trn = g ?trn1"
                  using BC_FrVal a ou uid by (auto simp: com_defs)
                ultimately show "?match"
                  using BC_FrVal by (intro matchI[of s1 ?a1 ?ou1 ?s1' vl1 vl1'']) (auto simp: \<Delta>0_def)
            qed
        qed (auto simp: consume_def)
        then show "?match \<or> ?ignore" ..
      next
        assume n\<phi>: "\<not>\<phi> ?trn"
        then have vl': "vl' = vl" using c by (auto simp: consume_def)
        obtain ou1 s1' where step1: "step s1 a = (ou1, s1')" by (cases "step s1 a")
        let ?trn1 = "Trans s1 a ou1 s1'"
        show "?match \<or> ?ignore"
        proof (cases "\<forall>uID'. uID' \<notin> UIDs AID' \<longrightarrow>
                             a \<noteq> COMact (comReceiveCreateOFriend AID (serverPass s1 AID) UID uID') \<and>
                             a \<noteq> COMact (comReceiveDeleteOFriend AID (serverPass s1 AID) UID uID')")
          case True
            then have n\<phi>1: "\<not>\<phi> ?trn1" using step1 by (auto elim!: \<phi>.elims simp: com_defs)
            have "?match" using step1 unfolding vl' proof (intro matchI[of s1 a ou1 s1' vl1 vl1])
              show c1: "consume ?trn1 vl1 vl1" using n\<phi>1 by (auto simp: consume_def)
              show "\<Delta>0 s' vl s1' vl1" using BC unfolding \<Delta>0_def proof (intro conjI)
                show "eqButUID s' s1'" using eqButUID_step[OF ss1 step step1 rs rs1] .
                show "validValSeqFrom vl1 s1'"
                  using c1 rs1 vVS1 by (intro step_validValSeqFrom[OF step1]) auto
              qed auto
              show "\<gamma> ?trn = \<gamma> ?trn1" using ss1 rs rs1 step step1 True n\<phi> n\<phi>1
                by (intro eqButUID_step_\<gamma>) auto
            next
              assume "\<gamma> ?trn"
              then have "ou = ou1" using n\<phi> n\<phi>1 by (intro eqButUID_step_\<gamma>_out[OF ss1 step step1]) auto
              then show "g ?trn = g ?trn1" by (cases a) auto
            qed auto
            then show "?match \<or> ?ignore" ..
        next
          case False
            with n\<phi> have "?ignore"
              using UID_UIDs BC step ss1 vVS1 unfolding vl'
              by (intro ignoreI) (auto simp: \<Delta>0_def split: prod.splits)
            then show "?match \<or> ?ignore" ..
        qed
      qed
    qed
    with BC show ?thesis by (cases rule: BC.cases) auto
  qed
qed



definition Gr where
"Gr =
 {
 (\<Delta>0, {\<Delta>0})
 }"


theorem secure: secure
apply (rule unwind_decomp_secure_graph[of Gr \<Delta>0])
unfolding Gr_def
(* apply (simp, smt insert_subset order_refl) *)
using
istate_\<Delta>0 unwind_cont_\<Delta>0
unfolding Gr_def by (auto intro: unwind_cont_mono)


end

end
