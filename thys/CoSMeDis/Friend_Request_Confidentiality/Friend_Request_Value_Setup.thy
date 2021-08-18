(* The value setup for friendship request confidentiality *)
theory Friend_Request_Value_Setup
  imports Friend_Request_Intro
begin

subsection \<open>Value setup\<close>

context Friend
begin

datatype "fUser" = U1 | U2
datatype "value" =
  isFRVal: FRVal fUser requestInfo \<comment> \<open>friendship requests from \<open>UID1\<close> to \<open>UID2\<close> (or vice versa)\<close>
| isFVal: FVal bool \<comment> \<open>updated friendship status between \<open>UID1\<close> and \<open>UID2\<close>\<close>
| isOVal: OVal bool \<comment> \<open>updated dynamic declassification trigger condition\<close>

fun \<phi> :: "(state,act,out) trans \<Rightarrow> bool" where
"\<phi> (Trans s (Cact (cFriendReq uid p uid' req)) ou s') =
  ((uid,uid') \<in> {(UID1,UID2), (UID2,UID1)} \<and> ou = outOK)"
|
"\<phi> (Trans s (Cact (cFriend uid p uid')) ou s') =
  ((uid,uid') \<in> {(UID1,UID2), (UID2,UID1)} \<and> ou = outOK \<or>
   open s \<noteq> open s')"
|
"\<phi> (Trans s (Dact (dFriend uid p uid')) ou s') =
  ((uid,uid') \<in> {(UID1,UID2), (UID2,UID1)} \<and> ou = outOK \<or>
   open s \<noteq> open s')"
|
"\<phi> (Trans s (Cact (cUser uid p uid' p')) ou s') =
  (open s \<noteq> open s')"
|
"\<phi> _ = False"

fun f :: "(state,act,out) trans \<Rightarrow> value" where
"f (Trans s (Cact (cFriendReq uid p uid' req)) ou s') =
    (if uid = UID1 \<and> uid' = UID2 then FRVal U1 req
else if uid = UID2 \<and> uid' = UID1 then FRVal U2 req
                                 else OVal True)"
|
"f (Trans s (Cact (cFriend uid p uid')) ou s') =
  (if (uid,uid') \<in> {(UID1,UID2), (UID2,UID1)} then FVal True
                                              else OVal True)"
|
"f (Trans s (Dact (dFriend uid p uid')) ou s') =
  (if (uid,uid') \<in> {(UID1,UID2), (UID2,UID1)} then FVal False
                                              else OVal False)"
|
"f (Trans s (Cact (cUser uid p uid' p')) ou s') = OVal False"
|
"f _ = undefined"

lemma \<phi>E:
assumes \<phi>: "\<phi> (Trans s a ou s')" (is "\<phi> ?trn")
and step: "step s a = (ou, s')"
and rs: "reach s"
obtains (FReq1) u p req where "a = Cact (cFriendReq UID1 p UID2 req)" "ou = outOK"
                              "f ?trn = FRVal u req" "u = U1" "IDsOK s [UID1, UID2] [] [] []"
                              "\<not>friends12 s" "\<not>friends12 s'" "open s' = open s"
                              "UID1 \<in>\<in> pendingFReqs s' UID2" "UID1 \<notin> set (pendingFReqs s UID2)"
                              "UID2 \<in>\<in> pendingFReqs s' UID1 \<longleftrightarrow> UID2 \<in>\<in> pendingFReqs s UID1"
      | (FReq2) u p req where "a = Cact (cFriendReq UID2 p UID1 req)" "ou = outOK"
                              "f ?trn = FRVal u req" "u = U2" "IDsOK s [UID1, UID2] [] [] []"
                              "\<not>friends12 s" "\<not>friends12 s'" "open s' = open s"
                              "UID2 \<in>\<in> pendingFReqs s' UID1" "UID2 \<notin> set (pendingFReqs s UID1)"
                              "UID1 \<in>\<in> pendingFReqs s' UID2 \<longleftrightarrow> UID1 \<in>\<in> pendingFReqs s UID2"
      | (Friend) uid p uid' where "a = Cact (cFriend uid p uid')" "ou = outOK" "f ?trn = FVal True"
                                  "uid = UID1 \<and> uid' = UID2 \<or> uid = UID2 \<and> uid' = UID1"
                                  "IDsOK s [UID1, UID2] [] [] []"
                                  "\<not>friends12 s" "friends12 s'" "uid' \<in>\<in> pendingFReqs s uid"
                                  "UID1 \<notin> set (pendingFReqs s' UID2)"
                                  "UID2 \<notin> set (pendingFReqs s' UID1)"
      | (Unfriend) uid p uid' where "a = Dact (dFriend uid p uid')" "ou = outOK" "f ?trn = FVal False"
                                    "uid = UID1 \<and> uid' = UID2 \<or> uid = UID2 \<and> uid' = UID1"
                                    "IDsOK s [UID1, UID2] [] [] []"
                                    "friends12 s" "\<not>friends12 s'"
                                    "UID1 \<notin> set (pendingFReqs s' UID2)"
                                    "UID1 \<notin> set (pendingFReqs s UID2)"
                                    "UID2 \<notin> set (pendingFReqs s' UID1)"
                                    "UID2 \<notin> set (pendingFReqs s UID1)"
      | (OpenF) uid p uid' where "a = Cact (cFriend uid p uid')"
                                 "(uid \<in> UIDs \<and> uid' \<in> {UID1,UID2}) \<or> (uid' \<in> UIDs \<and> uid \<in> {UID1,UID2})"
                                 "ou = outOK" "f ?trn = OVal True" "\<not>openByF s" "openByF s'"
                                 "\<not>openByA s" "\<not>openByA s'"
                                 "friends12 s' = friends12 s"
                                 "UID1 \<in>\<in> pendingFReqs s' UID2 \<longleftrightarrow> UID1 \<in>\<in> pendingFReqs s UID2"
                                 "UID2 \<in>\<in> pendingFReqs s' UID1 \<longleftrightarrow> UID2 \<in>\<in> pendingFReqs s UID1"
      | (CloseF) uid p uid' where "a = Dact (dFriend uid p uid')"
                                  "(uid \<in> UIDs \<and> uid' \<in> {UID1,UID2}) \<or> (uid' \<in> UIDs \<and> uid \<in> {UID1,UID2})"
                                  "ou = outOK" "f ?trn = OVal False" "openByF s" "\<not>openByF s'"
                                  "\<not>openByA s" "\<not>openByA s'"
                                  "friends12 s' = friends12 s"
                                  "UID1 \<in>\<in> pendingFReqs s' UID2 \<longleftrightarrow> UID1 \<in>\<in> pendingFReqs s UID2"
                                  "UID2 \<in>\<in> pendingFReqs s' UID1 \<longleftrightarrow> UID2 \<in>\<in> pendingFReqs s UID1"
      | (CloseA) uid p uid' p' where "a = Cact (cUser uid p uid' p')"
                                     "uid' \<in> {UID1,UID2}" "openByA s" "\<not>openByA s'"
                                     "\<not>openByF s" "\<not>openByF s'"
                                     "ou = outOK" "f ?trn = OVal False"
                                     "friends12 s' = friends12 s"
                                     "UID1 \<in>\<in> pendingFReqs s' UID2 \<longleftrightarrow> UID1 \<in>\<in> pendingFReqs s UID2"
                                     "UID2 \<in>\<in> pendingFReqs s' UID1 \<longleftrightarrow> UID2 \<in>\<in> pendingFReqs s UID1"
using \<phi> proof (elim \<phi>.elims disjE conjE)
  fix s1 uid p uid' req ou1 s1'
  assume "(uid,uid') \<in> {(UID1,UID2), (UID2,UID1)}" and ou: "ou1 = outOK"
     and "?trn = Trans s1 (Cact (cFriendReq uid p uid' req)) ou1 s1'"
  then have trn: "a = Cact (cFriendReq uid p uid' req)" "s = s1" "s' = s1'" "ou = ou1"
        and uids: "uid = UID1 \<and> uid' = UID2 \<or> uid = UID2 \<and> uid' = UID1" using UID1_UID2 by auto
  from uids show thesis proof
    assume "uid = UID1 \<and> uid' = UID2"
    then show thesis using ou uids trn step UID1_UID2_UIDs UID1_UID2 reach_distinct_friends_reqs[OF rs]
      by (intro FReq1[of p req]) (auto simp add: c_defs friends12_def open_defs)
  next
    assume "uid = UID2 \<and> uid' = UID1"
    then show thesis using ou uids trn step UID1_UID2_UIDs UID1_UID2 reach_distinct_friends_reqs[OF rs]
      by (intro FReq2[of p req]) (auto simp add: c_defs friends12_def open_defs)
  qed
next
  fix s1 uid p uid' ou1 s1'
  assume "(uid,uid') \<in> {(UID1,UID2), (UID2,UID1)}" and ou: "ou1 = outOK"
     and "?trn = Trans s1 (Cact (cFriend uid p uid')) ou1 s1'"
  then have trn: "a = Cact (cFriend uid p uid')" "s = s1" "s' = s1'" "ou = ou1"
        and uids: "uid = UID1 \<and> uid' = UID2 \<or> uid = UID2 \<and> uid' = UID1" using UID1_UID2 by auto
  then show thesis using ou uids trn step UID1_UID2_UIDs UID1_UID2 reach_distinct_friends_reqs[OF rs]
    by (intro Friend[of uid p uid']) (auto simp add: c_defs friends12_def)
next
  fix s1 uid p uid' ou1 s1'
  assume op: "open s1 \<noteq> open s1'"
     and "?trn = Trans s1 (Cact (cFriend uid p uid')) ou1 s1'"
  then have trn: "open s \<noteq> open s'" "a = Cact (cFriend uid p uid')" "s = s1" "s' = s1'" "ou = ou1"
    by auto
  with step have uids: "(uid \<in> UIDs \<and> uid' \<in> {UID1, UID2} \<or> uid \<in> {UID1, UID2} \<and> uid' \<in> UIDs) \<and>
                        ou = outOK \<and> p = pass s uid \<and>
                        \<not>openByF s \<and> openByF s' \<and> \<not>openByA s \<and> \<not>openByA s'"
    by (cases rule: step_open_cases) auto
  moreover have "friends12 s' \<longleftrightarrow> friends12 s"
    using step_friendIDs[OF step, of UID1 UID2] trn uids UID1_UID2 UID1_UID2_UIDs
    by (auto simp add: friends12_def)
  moreover have "(UID1 \<in>\<in> pendingFReqs s' UID2 \<longleftrightarrow> UID1 \<in>\<in> pendingFReqs s UID2) \<and>
                 (UID2 \<in>\<in> pendingFReqs s' UID1 \<longleftrightarrow> UID2 \<in>\<in> pendingFReqs s UID1)"
    using step_pendingFReqs[OF step, of UID1 UID2] trn uids UID1_UID2 UID1_UID2_UIDs
    by auto
  ultimately show thesis using trn(2) step UID1_UID2_UIDs UID1_UID2 by (intro OpenF) auto
next
  fix s1 uid p uid' ou1 s1'
  assume "(uid,uid') \<in> {(UID1,UID2), (UID2,UID1)}" and ou: "ou1 = outOK"
     and "?trn = Trans s1 (Dact (dFriend uid p uid')) ou1 s1'"
  then have trn: "a = Dact (dFriend uid p uid')" "s = s1" "s' = s1'" "ou = ou1"
        and uids: "uid = UID1 \<and> uid' = UID2 \<or> uid = UID2 \<and> uid' = UID1" using UID1_UID2 by auto
  then show thesis using step ou reach_friendIDs_symmetric[OF rs] reach_distinct_friends_reqs[OF rs]
    by (intro Unfriend; auto simp: d_defs friends12_def) blast+
next
  fix s1 uid p uid' ou1 s1'
  assume op: "open s1 \<noteq> open s1'"
     and "?trn = Trans s1 (Dact (dFriend uid p uid')) ou1 s1'"
  then have trn: "open s \<noteq> open s'" "a = Dact (dFriend uid p uid')" "s = s1" "s' = s1'" "ou = ou1"
    by auto
  with step have uids: "(uid \<in> UIDs \<and> uid' \<in> {UID1, UID2} \<or> uid \<in> {UID1, UID2} \<and> uid' \<in> UIDs) \<and>
                   ou = outOK \<and> openByF s \<and> \<not>openByF s' \<and> \<not>openByA s \<and> \<not>openByA s'"
    by (cases rule: step_open_cases) auto
  moreover have "friends12 s' \<longleftrightarrow> friends12 s"
    using step_friendIDs[OF step, of UID1 UID2] trn uids UID1_UID2 UID1_UID2_UIDs
    by (auto simp add: friends12_def)
  moreover have "(UID1 \<in>\<in> pendingFReqs s' UID2 \<longleftrightarrow> UID1 \<in>\<in> pendingFReqs s UID2) \<and>
                 (UID2 \<in>\<in> pendingFReqs s' UID1 \<longleftrightarrow> UID2 \<in>\<in> pendingFReqs s UID1)"
    using step_pendingFReqs[OF step, of UID1 UID2] trn uids UID1_UID2 UID1_UID2_UIDs
    by auto
  ultimately show thesis using trn(1,2) step UID1_UID2 UID1_UID2_UIDs
    by (intro CloseF) auto
next
  fix s1 uid p uid' p' ou1 s1'
  assume op: "open s1 \<noteq> open s1'"
     and "?trn = Trans s1 (Cact (cUser uid p uid' p')) ou1 s1'"
  then have trn: "open s \<noteq> open s'" "a = Cact (cUser uid p uid' p')" "s = s1" "s' = s1'" "ou = ou1"
    by auto
  with step have uids: "(uid' = UID2 \<or> uid' = UID1) \<and> ou = outOK \<and>
                       \<not>openByF s1 \<and> \<not>openByF s1' \<and> openByA s1 \<and> \<not>openByA s1'"
    by (cases rule: step_open_cases) auto
  moreover have "friends12 s1' \<longleftrightarrow> friends12 s1"
    using step_friendIDs[OF step, of UID1 UID2] trn uids UID1_UID2 UID1_UID2_UIDs
    by (auto simp add: friends12_def)
  moreover have "(UID1 \<in>\<in> pendingFReqs s' UID2 \<longleftrightarrow> UID1 \<in>\<in> pendingFReqs s UID2) \<and>
                 (UID2 \<in>\<in> pendingFReqs s' UID1 \<longleftrightarrow> UID2 \<in>\<in> pendingFReqs s UID1)"
    using step_pendingFReqs[OF step, of UID1 UID2] trn uids UID1_UID2 UID1_UID2_UIDs
    by auto
  ultimately show thesis using trn step UID1_UID2_UIDs UID1_UID2 by (intro CloseA) auto
qed

lemma step_open_\<phi>:
assumes "step s a = (ou, s')"
and "open s \<noteq> open s'"
shows "\<phi> (Trans s a ou s')"
using assms by (cases rule: step_open_cases) (auto simp: open_def)

lemma step_friends12_\<phi>:
assumes "step s a = (ou, s')"
and "friends12 s \<noteq> friends12 s'"
shows "\<phi> (Trans s a ou s')"
proof -
  have "a = Cact (cFriend UID1 (pass s UID1) UID2) \<or> a = Cact (cFriend UID2 (pass s UID2) UID1) \<or>
        a = Dact (dFriend UID1 (pass s UID1) UID2) \<or> a = Dact (dFriend UID2 (pass s UID2) UID1)"
   using assms step_friends12 by auto
  moreover then have "ou = outOK" using assms by auto
  ultimately show "\<phi> (Trans s a ou s')" by auto
qed

lemma step_pendingFReqs_\<phi>:
assumes "step s a = (ou, s')"
and "(UID1 \<in>\<in> pendingFReqs s UID2) \<noteq> (UID1 \<in>\<in> pendingFReqs s' UID2)
   \<or> (UID2 \<in>\<in> pendingFReqs s UID1) \<noteq> (UID2 \<in>\<in> pendingFReqs s' UID1)"
shows "\<phi> (Trans s a ou s')"
proof -
  have "\<exists>req. a = Cact (cFriend UID1 (pass s UID1) UID2) \<or>
              a = Cact (cFriend UID2 (pass s UID2) UID1) \<or>
              a = Dact (dFriend UID1 (pass s UID1) UID2) \<or>
              a = Dact (dFriend UID2 (pass s UID2) UID1) \<or>
              a = Cact (cFriendReq UID1 (pass s UID1) UID2 req) \<or>
              a = Cact (cFriendReq UID2 (pass s UID2) UID1 req)"
    by (rule ccontr, insert assms step_pendingFReqs) auto
  moreover then have "ou = outOK" using assms by auto
  ultimately show "\<phi> (Trans s a ou s')" by auto
qed

lemma eqButUID_step_\<phi>_imp:
assumes ss1: "eqButUID s s1"
and rs: "reach s" and rs1: "reach s1"
and step: "step s a = (ou,s')" and step1: "step s1 a = (ou1,s1')"
and a: "\<forall>req. a \<noteq> Cact (cFriend UID1 (pass s UID1) UID2) \<and>
              a \<noteq> Cact (cFriend UID2 (pass s UID2) UID1) \<and>
              a \<noteq> Cact (cFriendReq UID1 (pass s UID1) UID2 req) \<and>
              a \<noteq> Cact (cFriendReq UID2 (pass s UID2) UID1 req) \<and>
              a \<noteq> Dact (dFriend UID1 (pass s UID1) UID2) \<and>
              a \<noteq> Dact (dFriend UID2 (pass s UID2) UID1)"
and \<phi>: "\<phi> (Trans s a ou s')"
shows "\<phi> (Trans s1 a ou1 s1')"
proof -
  have "eqButUID s' s1'" using eqButUID_step[OF ss1 step step1 rs rs1] .
  then have "open s = open s1" and "open s' = open s1'"
        and "openByA s = openByA s1" and "openByA s' = openByA s1'"
        and "openByF s = openByF s1" and "openByF s' = openByF s1'"
    using ss1 by (auto simp: eqButUID_open_eq eqButUID_openByA_eq eqButUID_openByF_eq)
  with \<phi> a step step1 show "\<phi> (Trans s1 a ou1 s1')" using UID1_UID2_UIDs
    by (elim \<phi>.elims) (auto simp: c_defs d_defs)
qed

lemma eqButUID_step_\<phi>:
assumes ss1: "eqButUID s s1"
and rs: "reach s" and rs1: "reach s1"
and step: "step s a = (ou,s')" and step1: "step s1 a = (ou1,s1')"
and a: "\<forall>req. a \<noteq> Cact (cFriend UID1 (pass s UID1) UID2) \<and>
              a \<noteq> Cact (cFriend UID2 (pass s UID2) UID1) \<and>
              a \<noteq> Cact (cFriendReq UID1 (pass s UID1) UID2 req) \<and>
              a \<noteq> Cact (cFriendReq UID2 (pass s UID2) UID1 req) \<and>
              a \<noteq> Dact (dFriend UID1 (pass s UID1) UID2) \<and>
              a \<noteq> Dact (dFriend UID2 (pass s UID2) UID1)"
shows "\<phi> (Trans s a ou s') = \<phi> (Trans s1 a ou1 s1')"
proof
  assume "\<phi> (Trans s a ou s')"
  with assms show "\<phi> (Trans s1 a ou1 s1')" by (rule eqButUID_step_\<phi>_imp)
next
  assume "\<phi> (Trans s1 a ou1 s1')"
  moreover have "eqButUID s1 s" using ss1 by (rule eqButUID_sym)
  moreover have "\<forall>req. a \<noteq> Cact (cFriend UID1 (pass s1 UID1) UID2) \<and>
                       a \<noteq> Cact (cFriend UID2 (pass s1 UID2) UID1) \<and>
                       a \<noteq> Cact (cFriendReq UID1 (pass s1 UID1) UID2 req) \<and>
                       a \<noteq> Cact (cFriendReq UID2 (pass s1 UID2) UID1 req) \<and>
                       a \<noteq> Dact (dFriend UID1 (pass s1 UID1) UID2) \<and>
                       a \<noteq> Dact (dFriend UID2 (pass s1 UID2) UID1)"
    using a ss1 unfolding eqButUID_def by auto
  ultimately show "\<phi> (Trans s a ou s')" using rs rs1 step step1
    by (intro eqButUID_step_\<phi>_imp[of s1 s])
qed

end

end
