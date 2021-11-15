(* The value setup for friendship status confidentiality *)
theory Friend_Value_Setup
  imports "Friend_Openness"
begin

subsection \<open>Value Setup\<close>

context Friend
begin

datatype "value" =
  FrVal bool \<comment> \<open>updated friendship status between \<open>UID1\<close> and \<open>UID2\<close>\<close>
| OVal bool \<comment> \<open>updated dynamic declassification trigger condition\<close>

fun \<phi> :: "(state,act,out) trans \<Rightarrow> bool" where
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
"f (Trans s (Cact (cFriend uid p uid')) ou s') =
  (if (uid,uid') \<in> {(UID1,UID2), (UID2,UID1)} then FrVal True
                                              else OVal True)"
|
"f (Trans s (Dact (dFriend uid p uid')) ou s') =
  (if (uid,uid') \<in> {(UID1,UID2), (UID2,UID1)} then FrVal False
                                              else OVal False)"
|
"f (Trans s (Cact (cUser uid p uid' p')) ou s') = OVal False"
|
"f _ = undefined"


lemma \<phi>E:
assumes \<phi>: "\<phi> (Trans s a ou s')" (is "\<phi> ?trn")
and step: "step s a = (ou, s')"
and rs: "reach s"
obtains (Friend) uid p uid' where "a = Cact (cFriend uid p uid')" "ou = outOK" "f ?trn = FrVal True"
                                  "uid = UID1 \<and> uid' = UID2 \<or> uid = UID2 \<and> uid' = UID1"
                                  "IDsOK s [UID1, UID2] [] [] []"
                                  "\<not>friends12 s" "friends12 s'"
      | (Unfriend) uid p uid' where "a = Dact (dFriend uid p uid')" "ou = outOK" "f ?trn = FrVal False"
                                    "uid = UID1 \<and> uid' = UID2 \<or> uid = UID2 \<and> uid' = UID1"
                                    "IDsOK s [UID1, UID2] [] [] []"
                                    "friends12 s" "\<not>friends12 s'"
      | (OpenF) uid p uid' where "a = Cact (cFriend uid p uid')"
                                 "(uid \<in> UIDs \<and> uid' \<in> {UID1,UID2}) \<or> (uid' \<in> UIDs \<and> uid \<in> {UID1,UID2})"
                                 "ou = outOK" "f ?trn = OVal True" "\<not>openByF s" "openByF s'"
                                 "\<not>openByA s" "\<not>openByA s'"
      | (CloseF) uid p uid' where "a = Dact (dFriend uid p uid')"
                                  "(uid \<in> UIDs \<and> uid' \<in> {UID1,UID2}) \<or> (uid' \<in> UIDs \<and> uid \<in> {UID1,UID2})"
                                  "ou = outOK" "f ?trn = OVal False" "openByF s" "\<not>openByF s'"
                                  "\<not>openByA s" "\<not>openByA s'"
      | (CloseA) uid p uid' p' where "a = Cact (cUser uid p uid' p')"
                                     "uid' \<in> {UID1,UID2}" "openByA s" "\<not>openByA s'"
                                     "\<not>openByF s" "\<not>openByF s'"
                                     "ou = outOK" "f ?trn = OVal False"
using \<phi> proof (elim \<phi>.elims disjE conjE)
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
  then have trn: "open s \<noteq> open s'" "s = s1" "s' = s1'" "ou = ou1"
        and a: "a = Cact (cFriend uid p uid')"
    by auto
  with step have uids: "(uid \<in> UIDs \<and> uid' \<in> {UID1, UID2} \<or> uid \<in> {UID1, UID2} \<and> uid' \<in> UIDs) \<and>
                        ou = outOK \<and> \<not>openByF s \<and> openByF s' \<and> \<not>openByA s \<and> \<not>openByA s'"
    by (cases rule: step_open_cases) auto
  then show thesis using a UID1_UID2_UIDs by (intro OpenF) auto
next
  fix s1 uid p uid' ou1 s1'
  assume "(uid,uid') \<in> {(UID1,UID2), (UID2,UID1)}" and ou: "ou1 = outOK"
     and "?trn = Trans s1 (Dact (dFriend uid p uid')) ou1 s1'"
  then have trn: "a = Dact (dFriend uid p uid')" "s = s1" "s' = s1'" "ou = ou1"
        and uids: "uid = UID1 \<and> uid' = UID2 \<or> uid = UID2 \<and> uid' = UID1" using UID1_UID2 by auto
  then show thesis using step ou reach_friendIDs_symmetric[OF rs]
    by (intro Unfriend) (auto simp: d_defs friends12_def)
next
  fix s1 uid p uid' ou1 s1'
  assume op: "open s1 \<noteq> open s1'"
     and "?trn = Trans s1 (Dact (dFriend uid p uid')) ou1 s1'"
  then have trn: "open s \<noteq> open s'" "s = s1" "s' = s1'" "ou = ou1"
        and a: "a = Dact (dFriend uid p uid')"
    by auto
  with step have uids: "(uid \<in> UIDs \<and> uid' \<in> {UID1, UID2} \<or> uid \<in> {UID1, UID2} \<and> uid' \<in> UIDs) \<and>
                        ou = outOK \<and> openByF s \<and> (\<not>openByF s') \<and> (\<not>openByA s) \<and> (\<not>openByA s')"
    by (cases rule: step_open_cases) auto
  then show thesis using a UID1_UID2_UIDs by (intro CloseF) auto
next
  fix s1 uid p uid' p' ou1 s1'
  assume op: "open s1 \<noteq> open s1'"
     and "?trn = Trans s1 (Cact (cUser uid p uid' p')) ou1 s1'"
  then have trn: "open s \<noteq> open s'" "s = s1" "s' = s1'" "ou = ou1"
        and a: "a = Cact (cUser uid p uid' p')"
    by auto
  with step have uids: "(uid' = UID2 \<or> uid' = UID1) \<and> ou = outOK \<and>
                        (\<not>openByF s) \<and> (\<not>openByF s') \<and> openByA s \<and> (\<not>openByA s')"
    by (cases rule: step_open_cases) auto
  then show thesis using a UID1_UID2_UIDs by (intro CloseA) auto
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
   using assms step_friends12 by (cases "ou = outOK") auto
  moreover then have "ou = outOK" using assms by auto
  ultimately show "\<phi> (Trans s a ou s')" by auto
qed

lemma eqButUID_step_\<phi>_imp:
assumes ss1: "eqButUID s s1"
and rs: "reach s" and rs1: "reach s1"
and step: "step s a = (ou,s')" and step1: "step s1 a = (ou1,s1')"
and a: "a \<noteq> Cact (cFriend UID1 (pass s UID1) UID2) \<and> a \<noteq> Cact (cFriend UID2 (pass s UID2) UID1) \<and>
        a \<noteq> Dact (dFriend UID1 (pass s UID1) UID2) \<and> a \<noteq> Dact (dFriend UID2 (pass s UID2) UID1)"
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
and a: "a \<noteq> Cact (cFriend UID1 (pass s UID1) UID2) \<and> a \<noteq> Cact (cFriend UID2 (pass s UID2) UID1) \<and>
        a \<noteq> Dact (dFriend UID1 (pass s UID1) UID2) \<and> a \<noteq> Dact (dFriend UID2 (pass s UID2) UID1)"
shows "\<phi> (Trans s a ou s') = \<phi> (Trans s1 a ou1 s1')"
proof
  assume "\<phi> (Trans s a ou s')"
  with assms show "\<phi> (Trans s1 a ou1 s1')" by (rule eqButUID_step_\<phi>_imp)
next
  assume "\<phi> (Trans s1 a ou1 s1')"
  moreover have "eqButUID s1 s" using ss1 by (rule eqButUID_sym)
  moreover have "a \<noteq> Cact (cFriend UID1 (pass s1 UID1) UID2) \<and>
                 a \<noteq> Cact (cFriend UID2 (pass s1 UID2) UID1) \<and>
                 a \<noteq> Dact (dFriend UID1 (pass s1 UID1) UID2) \<and>
                 a \<noteq> Dact (dFriend UID2 (pass s1 UID2) UID1)"
    using a ss1 by (auto simp: eqButUID_stateSelectors)
  ultimately show "\<phi> (Trans s a ou s')" using rs rs1 step step1
    by (intro eqButUID_step_\<phi>_imp[of s1 s])
qed

end

end
