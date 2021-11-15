theory Outer_Friend_Issuer
  imports
    "Outer_Friend_Issuer_Value_Setup"
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

context OuterFriendIssuer
begin

fun T :: "(state,act,out) trans \<Rightarrow> bool"
where "T trn = False"

text \<open>For each user \<open>uid\<close> at a node \<open>aid\<close>, the remote friendship updates with
the fixed user \<open>UID\<close> at node \<open>AID\<close> form an alternating sequence of friending and unfriending.

Note that actions involving remote users who are observers do not produce secret values;
instead, those actions are observable, and the property we verify does not protect their
confidentiality.\<close>

fun validValSeq :: "value list \<Rightarrow> (apiID \<times> userID) list \<Rightarrow> bool" where
  "validValSeq [] _ = True"
| "validValSeq (FrVal aid uid True # vl) auidl \<longleftrightarrow> (aid, uid) \<notin> set auidl \<and> uid \<notin> UIDs aid \<and> validValSeq vl (auidl ## (aid, uid))"
| "validValSeq (FrVal aid uid False # vl) auidl \<longleftrightarrow> (aid, uid) \<in>\<in> auidl \<and> uid \<notin> UIDs aid \<and> validValSeq vl (removeAll (aid, uid) auidl)"
| "validValSeq (OVal _ # vl) auidl = validValSeq vl auidl"

abbreviation validValSeqFrom :: "value list \<Rightarrow> state \<Rightarrow> bool" where
  "validValSeqFrom vl s \<equiv> validValSeq vl (removeUIDs (sentOuterFriendIDs s UID))"

text \<open>When the access window is closed, observers may learn about the occurrence of
remote friendship actions (by observing network traffic), but not their content;
the actions can be replaced by different actions involving different users (who are not observers)
without affecting the observations.\<close>

inductive BC :: "value list \<Rightarrow> value list \<Rightarrow> bool"
where
  BC_Nil[simp,intro]: "BC [] []"
| BC_FrVal[intro]:
    "BC vl vl1 \<Longrightarrow> uid' \<notin> UIDs aid \<Longrightarrow> BC (FrVal aid uid st # vl) (FrVal aid uid' st' # vl1)"

text \<open>When the access window is open, i.e.~the user \<open>UID\<close> is a local friend of an observer,
all information about the remote friends of \<open>UID\<close> is declassified;
when the access window closes again, the contents of future updates are kept confidential.\<close>

definition "BO vl vl1 \<equiv>
 (vl1 = vl) \<or>
 (\<exists>vl0 vl' vl1'. vl = vl0 @ OVal False # vl' \<and> vl1 = vl0 @ OVal False # vl1' \<and> BC vl' vl1')"

definition "B vl vl1 \<equiv> (BC vl vl1 \<or> BO vl vl1) \<and> validValSeqFrom vl1 istate"


lemma B_Nil_Nil: "B vl vl1 \<Longrightarrow> vl1 = [] \<longleftrightarrow> vl = []"
unfolding B_def BO_def by (auto elim: BC.cases)

sublocale BD_Security_IO where
istate = istate and step = step and
\<phi> = \<phi> and f = f and \<gamma> = \<gamma> and g = g and T = T and B = B
done


subsubsection \<open>Unwinding proof\<close>

definition \<Delta>0 :: "state \<Rightarrow> value list \<Rightarrow> state \<Rightarrow> value list \<Rightarrow> bool" where
"\<Delta>0 s vl s1 vl1 \<equiv>
 s1 = istate \<and> s = istate \<and> B vl vl1"


definition \<Delta>1 :: "state \<Rightarrow> value list \<Rightarrow> state \<Rightarrow> value list \<Rightarrow> bool" where
"\<Delta>1 s vl s1 vl1 \<equiv>
 BO vl vl1 \<and>
 s1 = s \<and>
 validValSeqFrom vl1 s1"


definition \<Delta>2 :: "state \<Rightarrow> value list \<Rightarrow> state \<Rightarrow> value list \<Rightarrow> bool" where
"\<Delta>2 s vl s1 vl1 \<equiv>
 BC vl vl1 \<and>
 eqButUID s s1 \<and> \<not>open s1 \<and>
 validValSeqFrom vl1 s1"


lemma validValSeq_prefix: "validValSeq (vl @ vl') auidl \<Longrightarrow> validValSeq vl auidl"
by (induction vl arbitrary: auidl) (auto elim: validValSeq.elims)

lemma filter_removeAll: "filter P (removeAll x xs) = removeAll x (filter P xs)"
unfolding removeAll_filter_not_eq by (auto intro: filter_cong)

lemma step_validValSeqFrom:
assumes step: "step s a = (ou, s')"
and rs: "reach s"
and c: "consume (Trans s a ou s') vl vl'" (is "consume ?trn vl vl'")
and vVS: "validValSeqFrom vl s"
shows "validValSeqFrom vl' s'"
proof cases
  assume "\<phi> ?trn"
  moreover then obtain v where "vl = v # vl'" using c by (cases vl, auto simp: consume_def)
  moreover have "distinct (sentOuterFriendIDs s UID)" using rs by (intro reach_distinct_friends_reqs)
  ultimately show ?thesis using assms
    by (elim \<phi>E)
       (auto simp: com_defs c_defs d_defs consume_def distinct_remove1_removeAll filter_removeAll)
next
  assume n\<phi>: "\<not>\<phi> ?trn"
  then have vl': "vl' = vl" using c by (auto simp: consume_def)
  then show ?thesis using vVS step proof (cases a)
    case (Sact sa) then show ?thesis using assms vl' by (cases sa) (auto simp: s_defs) next
    case (Cact ca) then show ?thesis using assms vl' by (cases ca) (auto simp: c_defs) next
    case (Dact da) then show ?thesis using assms vl' by (cases da) (auto simp: d_defs) next
    case (Uact ua) then show ?thesis using assms vl' by (cases ua) (auto simp: u_defs) next
    case (COMact ca) then show ?thesis using assms vl' n\<phi> by (cases ca) (auto simp: com_defs filter_remove1)
  qed auto
qed

lemma istate_\<Delta>0:
assumes B: "B vl vl1"
shows "\<Delta>0 istate vl istate vl1"
using assms unfolding \<Delta>0_def
by auto

lemma unwind_cont_\<Delta>0: "unwind_cont \<Delta>0 {\<Delta>1,\<Delta>2}"
proof(rule, simp)
  let ?\<Delta> = "\<lambda>s vl s1 vl1. \<Delta>1 s vl s1 vl1 \<or>
                           \<Delta>2 s vl s1 vl1"
  fix s s1 :: state and vl vl1 :: "value list"
  assume rsT: "reachNT s" and rs1: "reach s1" and \<Delta>0: "\<Delta>0 s vl s1 vl1"
  then have rs: "reach s" and s: "s = istate" and s1: "s1 = istate" and B: "B vl vl1"
    using reachNT_reach unfolding \<Delta>0_def by auto
  show "iaction ?\<Delta> s vl s1 vl1 \<or>
        ((vl = [] \<longrightarrow> vl1 = []) \<and> reaction ?\<Delta> s vl s1 vl1)" (is "?iact \<or> (_ \<and> ?react)")
  proof-
    have ?react proof
      fix a :: act and ou :: out and s' :: state and vl'
      let ?trn = "Trans s a ou s'"
      assume step: "step s a = (ou, s')" and T: "\<not> T ?trn" and c: "consume ?trn vl vl'"
      show "match ?\<Delta> s s1 vl1 a ou s' vl' \<or> ignore ?\<Delta> s s1 vl1 a ou s' vl'" (is "?match \<or> ?ignore")
      proof (intro disjI1)
        obtain uid p where a: "a = Sact (sSys uid p) \<or> s' = s"
          using step unfolding s by (elim istate_sSys) auto
        have "\<not>open s'" using step a s by (auto simp: istate_def s_defs open_def)
        moreover then have "\<not>\<phi> ?trn" using step rs a by (auto elim!: \<phi>E simp: s istate_def com_defs)
        moreover have "sentOuterFriendIDs s' UID = sentOuterFriendIDs s UID"
          using s a step by (auto simp: s_defs)
        ultimately show "?match" using s s1 step B c unfolding \<Delta>1_def \<Delta>2_def B_def
          by (intro matchI[of s1 a ou s' vl1 vl1]) (auto simp: consume_def)
      qed
    qed
    with B_Nil_Nil[OF B] show ?thesis by auto
  qed
qed


lemma unwind_cont_\<Delta>1: "unwind_cont \<Delta>1 {\<Delta>1,\<Delta>2}"
proof(rule, simp)
  let ?\<Delta> = "\<lambda>s vl s1 vl1. \<Delta>1 s vl s1 vl1 \<or>
                           \<Delta>2 s vl s1 vl1"
  fix s s1 :: state and vl vl1 :: "value list"
  assume rsT: "reachNT s" and rs1: "reach s1" and \<Delta>0: "\<Delta>1 s vl s1 vl1"
  then have rs: "reach s" and s: "s1 = s" and BO: "BO vl vl1"
        and vVS1: "validValSeqFrom vl1 s1"
    using reachNT_reach unfolding \<Delta>1_def by auto
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
        consider (Eq) "vl1 = vl"
          | (BC) vl0 vl'' vl1'' where "vl = vl0 @ OVal False # vl''"
                                and "vl1 = vl0 @ OVal False # vl1''"
                                and "BC vl'' vl1''"
          using BO
          by (auto simp: BO_def)
        then have "?match"
        proof cases
          case Eq
          then show ?thesis
            using step s c vVS1 step_validValSeqFrom[OF step rs c]
            by (intro matchI[of s1 a ou s' vl1 vl']) (auto simp: \<Delta>1_def BO_def)
        next
          case BC
          show "?match" proof (cases vl0)
            case Nil
              then have "consume ?trn vl1 vl1''" and "vl' = vl''" and f: "f ?trn = OVal False"
                using \<phi> c BC by (auto simp: consume_def)
              moreover then have "validValSeqFrom vl1'' s'"
                using s rs vVS1 by (intro step_validValSeqFrom[OF step]) auto
              moreover have "\<not>open s'" using \<phi> step rs f by (auto elim: \<phi>E)
              ultimately show ?thesis
                using step s BC by (intro matchI[of s1 a ou s' vl1 vl1'']) (auto simp: \<Delta>2_def)
          next
            case (Cons v vl0')
              then have "consume ?trn vl1 (vl0' @ OVal False # vl1'')" and "vl' = vl0' @ OVal False # vl''"
                using \<phi> c BC by (auto simp: consume_def)
              moreover then have "validValSeqFrom (vl0' @ OVal False # vl1'') s'"
                using s rs vVS1 by (intro step_validValSeqFrom[OF step]) auto
              ultimately show ?thesis
                using step s BC
                by (intro matchI[of s1 a ou s' vl1 "(vl0' @ OVal False # vl1'')"]) (auto simp: \<Delta>1_def BO_def)
          qed
        qed
        then show "?match \<or> ?ignore" ..
      next
        assume n\<phi>: "\<not>\<phi> ?trn"
        then have "consume ?trn vl1 vl1" and "vl' = vl" using c by (auto simp: consume_def)
        moreover then have "validValSeqFrom vl1 s'"
          using s rs vVS1 by (intro step_validValSeqFrom[OF step]) auto
        ultimately have "?match"
          using step s BO by (intro matchI[of s1 a ou s' vl1 vl1]) (auto simp: \<Delta>1_def)
        then show "?match \<or> ?ignore" ..
      qed
    qed
    with BO show ?thesis by (auto simp: BO_def)
  qed
qed

lemma unwind_cont_\<Delta>2: "unwind_cont \<Delta>2 {\<Delta>2}"
proof(rule, simp)
  fix s s1 :: state and vl vl1 :: "value list"
  assume rsT: "reachNT s" and rs1: "reach s1" and \<Delta>2: "\<Delta>2 s vl s1 vl1"
  then have rs: "reach s" and ss1: "eqButUID s s1" and BC: "BC vl vl1"
        and os: "\<not>open s1" and vVS1: "validValSeqFrom vl1 s1"
    using reachNT_reach unfolding \<Delta>2_def by auto
  show "iaction \<Delta>2 s vl s1 vl1 \<or>
        ((vl = [] \<longrightarrow> vl1 = []) \<and> reaction \<Delta>2 s vl s1 vl1)" (is "?iact \<or> (_ \<and> ?react)")
  proof-
    have ?react proof
      fix a :: act and ou :: out and s' :: state and vl'
      let ?trn = "Trans s a ou s'"
      assume step: "step s a = (ou, s')" and T: "\<not> T ?trn" and c: "consume ?trn vl vl'"
      show "match \<Delta>2 s s1 vl1 a ou s' vl' \<or> ignore \<Delta>2 s s1 vl1 a ou s' vl'" (is "?match \<or> ?ignore")
      proof cases
        assume \<phi>: "\<phi> ?trn"
        with BC c have "?match" proof (cases rule: BC.cases)
          case (BC_FrVal vl'' vl1'' uid' aid uid st st')
            then show ?thesis proof (cases st')
              case True
                let ?a1 = "COMact (comSendCreateOFriend UID (pass s1 UID) aid uid')"
                let ?ou1 = "O_sendCreateOFriend (aid, clientPass s aid, UID, uid')"
                let ?s1' = "snd (sendCreateOFriend s1 UID (pass s1 UID) aid uid')"
                let ?trn1 = "Trans s1 ?a1 ?ou1 ?s1'"
                have c1: "consume ?trn1 vl1 vl1''" and "vl' = vl''" and "f ?trn = FrVal aid uid st"
                  using \<phi> c BC_FrVal True by (auto simp: consume_def)
                moreover then have a: "(a = COMact (comSendCreateOFriend UID (pass s UID) aid uid)
                                        \<and> ou = O_sendCreateOFriend (aid, clientPass s aid, UID, uid))
                                     \<or> (a = COMact (comSendDeleteOFriend UID (pass s UID) aid uid)
                                        \<and> ou = O_sendDeleteOFriend (aid, clientPass s aid, UID, uid))"
                               and IDs: "IDsOK s [UID] [] [] [aid]"
                               and uid: "uid \<notin> UIDs aid"
                  using \<phi> step rs by (auto elim!: \<phi>E split: prod.splits simp: com_defs)
                moreover have step1: "step s1 ?a1 = (?ou1, ?s1')"
                  using IDs vVS1 BC_FrVal True ss1 by (auto simp: com_defs eqButUID_def)
                moreover then have "validValSeqFrom vl1'' ?s1'"
                  using vVS1 rs1 c1 by (intro step_validValSeqFrom[OF step1]) auto
                moreover have "\<not>open ?s1'" using os by (auto simp: open_def com_defs)
                moreover have "eqButUID s' ?s1'"
                  using ss1 step a uid BC_FrVal(4) eqButUID_eqButUIDf[OF ss1] eqButUID_eqButUIDs[OF ss1]
                  by (auto split: prod.splits simp: com_defs filter_remove1 intro!: eqButUID_cong eqButUIDf_cong)
                moreover have "\<gamma> ?trn = \<gamma> ?trn1" and "g ?trn = g ?trn1"
                  using BC_FrVal a uid by (auto simp: com_defs)
                ultimately show "?match"
                  using BC_FrVal by (intro matchI[of s1 ?a1 ?ou1 ?s1' vl1 vl1'']) (auto simp: \<Delta>2_def)
            next
              case False
                let ?a1 = "COMact (comSendDeleteOFriend UID (pass s1 UID) aid uid')"
                let ?ou1 = "O_sendDeleteOFriend (aid, clientPass s aid, UID, uid')"
                let ?s1' = "snd (sendDeleteOFriend s1 UID (pass s1 UID) aid uid')"
                let ?trn1 = "Trans s1 ?a1 ?ou1 ?s1'"
                have c1: "consume ?trn1 vl1 vl1''" and "vl' = vl''" and "f ?trn = FrVal aid uid st"
                  using \<phi> c BC_FrVal False by (auto simp: consume_def)
                moreover then have a: "(a = COMact (comSendCreateOFriend UID (pass s UID) aid uid)
                                        \<and> ou = O_sendCreateOFriend (aid, clientPass s aid, UID, uid))
                                     \<or> (a = COMact (comSendDeleteOFriend UID (pass s UID) aid uid)
                                        \<and> ou = O_sendDeleteOFriend (aid, clientPass s aid, UID, uid))"
                               and IDs: "IDsOK s [UID] [] [] [aid]"
                               and uid: "uid \<notin> UIDs aid"
                  using \<phi> step rs by (auto elim!: \<phi>E split: prod.splits simp: com_defs)
                moreover have step1: "step s1 ?a1 = (?ou1, ?s1')"
                  using IDs vVS1 BC_FrVal False ss1 by (auto simp: com_defs eqButUID_def)
                moreover then have "validValSeqFrom vl1'' ?s1'"
                  using vVS1 rs1 c1 by (intro step_validValSeqFrom[OF step1]) auto
                moreover have "\<not>open ?s1'" using os by (auto simp: open_def com_defs)
                moreover have "eqButUID s' ?s1'"
                  using ss1 step a uid BC_FrVal(4) eqButUID_eqButUIDf[OF ss1] eqButUID_eqButUIDs[OF ss1]
                  by (auto split: prod.splits simp: com_defs filter_remove1 intro!: eqButUID_cong eqButUIDf_cong)
                moreover have "\<gamma> ?trn = \<gamma> ?trn1" and "g ?trn = g ?trn1"
                  using BC_FrVal a uid by (auto simp: com_defs)
                ultimately show "?match"
                  using BC_FrVal by (intro matchI[of s1 ?a1 ?ou1 ?s1' vl1 vl1'']) (auto simp: \<Delta>2_def)
            qed
        qed (auto simp: consume_def)
        then show "?match \<or> ?ignore" ..
      next
        assume n\<phi>: "\<not>\<phi> ?trn"
        then have vl': "vl' = vl" using c by (auto simp: consume_def)
        obtain ou1 s1' where step1: "step s1 a = (ou1, s1')" by (cases "step s1 a")
        let ?trn1 = "Trans s1 a ou1 s1'"
        show "?match \<or> ?ignore"
        proof (cases "\<forall>aID uID'. uID' \<notin> UIDs aID \<longrightarrow>
                                 a \<noteq> COMact (comSendCreateOFriend UID (pass s UID) aID uID') \<and>
                                 a \<noteq> COMact (comSendDeleteOFriend UID (pass s UID) aID uID')")
          case True
            then have n\<phi>1: "\<not>\<phi> ?trn1"
              using n\<phi> ss1 rs rs1 step step1 by (auto simp: eqButUID_step_\<phi>)
            have "?match" using step1 unfolding vl' proof (intro matchI[of s1 a ou1 s1' vl1 vl1])
              show c1: "consume ?trn1 vl1 vl1" using n\<phi>1 by (auto simp: consume_def)
              show "\<Delta>2 s' vl s1' vl1" using BC unfolding \<Delta>2_def proof (intro conjI)
                show "eqButUID s' s1'" using eqButUID_step[OF ss1 step step1 rs rs1] .
                show "\<not>open s1'" proof
                  assume "open s1'"
                  with os have "open s1 \<noteq> open s1'" by auto
                  then show "False" using step1 n\<phi>1 by (elim open_step_cases[of s1 s1']) auto
                qed
                show "validValSeqFrom vl1 s1'"
                  using c1 rs1 vVS1 by (intro step_validValSeqFrom[OF step1]) auto
              qed auto
              show "\<gamma> ?trn = \<gamma> ?trn1" using ss1 rs rs1 step step1 True by (intro eqButUID_step_\<gamma>) auto
            next
              assume "\<gamma> ?trn"
              then have "ou = ou1" using os n\<phi> n\<phi>1 by (intro eqButUID_step_\<gamma>_out[OF ss1 step step1]) auto
              then show "g ?trn = g ?trn1" by (cases a) auto
            qed auto
            then show "?match \<or> ?ignore" ..
        next
          case False
            with n\<phi> have "?ignore"
              using UID_UIDs BC step ss1 os vVS1 unfolding vl'
              by (intro ignoreI) (auto simp: \<Delta>2_def split: prod.splits)
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
 (\<Delta>0, {\<Delta>1,\<Delta>2}),
 (\<Delta>1, {\<Delta>1,\<Delta>2}),
 (\<Delta>2, {\<Delta>2})
 }"


theorem secure: secure
apply (rule unwind_decomp_secure_graph[of Gr \<Delta>0])
unfolding Gr_def
apply (simp, smt insert_subset order_refl)
using
istate_\<Delta>0 unwind_cont_\<Delta>0 unwind_cont_\<Delta>1 unwind_cont_\<Delta>2
unfolding Gr_def by (auto intro: unwind_cont_mono)

end

end
