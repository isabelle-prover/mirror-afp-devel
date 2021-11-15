(* The value setup for friend confidentiality *)
theory Friend_Value_Setup
imports Friend_Intro
begin

text \<open>The confidential information is the friendship status between two arbitrary but fixed users:\<close>

consts UID1 :: userID
consts UID2 :: userID

axiomatization where
UID1_UID2_UIDs: "{UID1,UID2} \<inter> UIDs = {}"
and
UID1_UID2: "UID1 \<noteq> UID2"

subsection \<open>Preliminaries\<close>

(* The notion of two userID lists being equal save for at most one occurrence of uid: *)
fun eqButUIDl :: "userID \<Rightarrow> userID list \<Rightarrow> userID list \<Rightarrow> bool" where
"eqButUIDl uid uidl uidl1 = (remove1 uid uidl = remove1 uid uidl1)"

lemma eqButUIDl_eq[simp,intro!]: "eqButUIDl uid uidl uidl"
by auto

lemma eqButUIDl_sym:
assumes "eqButUIDl uid uidl uidl1"
shows "eqButUIDl uid uidl1 uidl"
using assms by auto

lemma eqButUIDl_trans:
assumes "eqButUIDl uid uidl uidl1" and "eqButUIDl uid uidl1 uidl2"
shows "eqButUIDl uid uidl uidl2"
using assms by auto

lemma eqButUIDl_remove1_cong:
assumes "eqButUIDl uid uidl uidl1"
shows "eqButUIDl uid (remove1 uid' uidl) (remove1 uid' uidl1)"
proof -
  have "remove1 uid (remove1 uid' uidl) = remove1 uid' (remove1 uid uidl)" by (simp add: remove1_commute)
  also have "\<dots> = remove1 uid' (remove1 uid uidl1)" using assms by simp
  also have "\<dots> = remove1 uid (remove1 uid' uidl1)" by (simp add: remove1_commute)
  finally show ?thesis by simp
qed

lemma eqButUIDl_snoc_cong:
assumes "eqButUIDl uid uidl uidl1"
and "uid' \<in>\<in> uidl \<longleftrightarrow> uid' \<in>\<in> uidl1"
shows "eqButUIDl uid (uidl ## uid') (uidl1 ## uid')"
using assms by (auto simp add: remove1_append remove1_idem)

(* The notion of two functions each taking a userID and returning a list of user IDs
  being equal everywhere but on UID1 and UID2, where their return results are allowed
  to be eqButUIDl : *)
definition eqButUIDf where
"eqButUIDf frds frds1 \<equiv>
  eqButUIDl UID2 (frds UID1) (frds1 UID1)
\<and> eqButUIDl UID1 (frds UID2) (frds1 UID2)
\<and> (\<forall>uid. uid \<noteq> UID1 \<and> uid \<noteq> UID2 \<longrightarrow> frds uid = frds1 uid)"

lemmas eqButUIDf_intro = eqButUIDf_def[THEN meta_eq_to_obj_eq, THEN iffD2]

lemma eqButUIDf_eeq[simp,intro!]: "eqButUIDf frds frds"
unfolding eqButUIDf_def by auto

lemma eqButUIDf_sym:
assumes "eqButUIDf frds frds1" shows "eqButUIDf frds1 frds"
using assms eqButUIDl_sym unfolding eqButUIDf_def
by presburger

lemma eqButUIDf_trans:
assumes "eqButUIDf frds frds1" and "eqButUIDf frds1 frds2"
shows "eqButUIDf frds frds2"
using assms eqButUIDl_trans unfolding eqButUIDf_def by (auto split: if_splits)

lemma eqButUIDf_cong:
assumes "eqButUIDf frds frds1"
and "uid = UID1 \<Longrightarrow> eqButUIDl UID2 uu uu1"
and "uid = UID2 \<Longrightarrow> eqButUIDl UID1 uu uu1"
and "uid \<noteq> UID1 \<Longrightarrow> uid \<noteq> UID2 \<Longrightarrow> uu = uu1"
shows "eqButUIDf (frds (uid := uu)) (frds1(uid := uu1))"
using assms unfolding eqButUIDf_def by (auto split: if_splits)

lemma eqButUIDf_eqButUIDl:
assumes "eqButUIDf frds frds1"
shows "eqButUIDl UID2 (frds UID1) (frds1 UID1)"
  and "eqButUIDl UID1 (frds UID2) (frds1 UID2)"
using assms unfolding eqButUIDf_def by (auto split: if_splits)

lemma eqButUIDf_not_UID:
"\<lbrakk>eqButUIDf frds frds1; uid \<noteq> UID1; uid \<noteq> UID2\<rbrakk> \<Longrightarrow> frds uid = frds1 uid"
unfolding eqButUIDf_def by (auto split: if_splits)

lemma eqButUIDf_not_UID':
assumes eq1: "eqButUIDf frds frds1"
and uid: "(uid,uid') \<notin> {(UID1,UID2), (UID2,UID1)}"
shows "uid \<in>\<in> frds uid' \<longleftrightarrow> uid \<in>\<in> frds1 uid'"
proof -
  from uid have "(uid' = UID1 \<and> uid \<noteq> UID2)
               \<or> (uid' = UID2 \<and> uid \<noteq> UID1)
               \<or> (uid' \<notin> {UID1,UID2})" (is "?u1 \<or> ?u2 \<or> ?n12")
    by auto
  then show ?thesis proof (elim disjE)
    assume "?u1"
    moreover then have "uid \<in>\<in> remove1 UID2 (frds uid') \<longleftrightarrow> uid \<in>\<in> remove1 UID2 (frds1 uid')"
      using eq1 unfolding eqButUIDf_def by auto
    ultimately show ?thesis by auto
  next
    assume "?u2"
    moreover then have "uid \<in>\<in> remove1 UID1 (frds uid') \<longleftrightarrow> uid \<in>\<in> remove1 UID1 (frds1 uid')"
      using eq1 unfolding eqButUIDf_def by auto
    ultimately show ?thesis by auto
  next
    assume "?n12"
    then show ?thesis using eq1 unfolding eqButUIDf_def by auto
  qed
qed

(* The notion of two functions each taking two userID arguments being
  equal everywhere but on the values (UID1,UID2) and (UID2,UID1): *)
definition eqButUID12 where
"eqButUID12 freq freq1 \<equiv>
 \<forall> uid uid'. if (uid,uid') \<in> {(UID1,UID2), (UID2,UID1)} then True else freq uid uid' = freq1 uid uid'"

lemmas eqButUID12_intro = eqButUID12_def[THEN meta_eq_to_obj_eq, THEN iffD2]

lemma eqButUID12_eeq[simp,intro!]: "eqButUID12 freq freq"
unfolding eqButUID12_def by auto

lemma eqButUID12_sym:
assumes "eqButUID12 freq freq1" shows "eqButUID12 freq1 freq"
using assms unfolding eqButUID12_def
by presburger

lemma eqButUID12_trans:
assumes "eqButUID12 freq freq1" and "eqButUID12 freq1 freq2"
shows "eqButUID12 freq freq2"
using assms unfolding eqButUID12_def by (auto split: if_splits)

lemma eqButUID12_cong:
assumes "eqButUID12 freq freq1"
(*and "uid = UID1 \<Longrightarrow> eqButUID2 uu uu1"*)
and "\<not> (uid,uid') \<in> {(UID1,UID2), (UID2,UID1)} \<Longrightarrow> uu = uu1"
shows "eqButUID12 (fun_upd2 freq uid uid' uu) (fun_upd2 freq1 uid uid' uu1)"
using assms unfolding eqButUID12_def fun_upd2_def by (auto split: if_splits)

lemma eqButUID12_not_UID:
"\<lbrakk>eqButUID12 freq freq1; \<not> (uid,uid') \<in> {(UID1,UID2), (UID2,UID1)}\<rbrakk> \<Longrightarrow> freq uid uid' = freq1 uid uid'"
unfolding eqButUID12_def by (auto split: if_splits)


(* The notion of two states being equal everywhere but on the friendship requests or status of users UID1 and UID2: *)
definition eqButUID :: "state \<Rightarrow> state \<Rightarrow> bool" where
"eqButUID s s1 \<equiv>
 admin s = admin s1 \<and>

 pendingUReqs s = pendingUReqs s1 \<and> userReq s = userReq s1 \<and>
 userIDs s = userIDs s1 \<and> user s = user s1 \<and> pass s = pass s1 \<and>

 eqButUIDf (pendingFReqs s) (pendingFReqs s1) \<and>
 eqButUID12 (friendReq s) (friendReq s1) \<and>
 eqButUIDf (friendIDs s) (friendIDs s1) \<and>

 postIDs s = postIDs s1 \<and> admin s = admin s1 \<and>
 post s = post s1 \<and>
 owner s = owner s1 \<and>
 vis s = vis s1"

lemmas eqButUID_intro = eqButUID_def[THEN meta_eq_to_obj_eq, THEN iffD2]

lemma eqButUID_refl[simp,intro!]: "eqButUID s s"
unfolding eqButUID_def by auto

lemma eqButUID_sym[sym]:
assumes "eqButUID s s1" shows "eqButUID s1 s"
using assms eqButUIDf_sym eqButUID12_sym unfolding eqButUID_def by auto

lemma eqButUID_trans[trans]:
assumes "eqButUID s s1" and "eqButUID s1 s2" shows "eqButUID s s2"
using assms eqButUIDf_trans eqButUID12_trans unfolding eqButUID_def by metis

(* Implications from eqButUID, including w.r.t. auxiliary operations: *)
lemma eqButUID_stateSelectors:
"eqButUID s s1 \<Longrightarrow>
 admin s = admin s1 \<and>

 pendingUReqs s = pendingUReqs s1 \<and> userReq s = userReq s1 \<and>
 userIDs s = userIDs s1 \<and> user s = user s1 \<and> pass s = pass s1 \<and>

 eqButUIDf (pendingFReqs s) (pendingFReqs s1) \<and>
 eqButUID12 (friendReq s) (friendReq s1) \<and>
 eqButUIDf (friendIDs s) (friendIDs s1) \<and>

 postIDs s = postIDs s1 \<and> admin s = admin s1 \<and>
 post s = post s1 \<and>
 owner s = owner s1 \<and>
 vis s = vis s1 \<and>

 IDsOK s = IDsOK s1"
unfolding eqButUID_def IDsOK_def[abs_def] by auto

lemma eqButUID_eqButUID2:
"eqButUID s s1 \<Longrightarrow> eqButUIDl UID2 (friendIDs s UID1) (friendIDs s1 UID1)"
unfolding eqButUID_def using eqButUIDf_eqButUIDl
by (smt eqButUIDf_eqButUIDl eqButUIDl.simps)

lemma eqButUID_not_UID:
"eqButUID s s1 \<Longrightarrow> uid \<noteq> UID \<Longrightarrow> post s uid = post s1 uid"
unfolding eqButUID_def by auto


lemma eqButUID_cong[simp, intro]:
"\<And> uu1 uu2. eqButUID s s1 \<Longrightarrow> uu1 = uu2 \<Longrightarrow> eqButUID (s \<lparr>admin := uu1\<rparr>) (s1 \<lparr>admin := uu2\<rparr>)"

"\<And> uu1 uu2. eqButUID s s1 \<Longrightarrow> uu1 = uu2 \<Longrightarrow> eqButUID (s \<lparr>pendingUReqs := uu1\<rparr>) (s1 \<lparr>pendingUReqs := uu2\<rparr>)"
"\<And> uu1 uu2. eqButUID s s1 \<Longrightarrow> uu1 = uu2 \<Longrightarrow> eqButUID (s \<lparr>userReq := uu1\<rparr>) (s1 \<lparr>userReq := uu2\<rparr>)"
"\<And> uu1 uu2. eqButUID s s1 \<Longrightarrow> uu1 = uu2 \<Longrightarrow> eqButUID (s \<lparr>userIDs := uu1\<rparr>) (s1 \<lparr>userIDs := uu2\<rparr>)"
"\<And> uu1 uu2. eqButUID s s1 \<Longrightarrow> uu1 = uu2 \<Longrightarrow> eqButUID (s \<lparr>user := uu1\<rparr>) (s1 \<lparr>user := uu2\<rparr>)"
"\<And> uu1 uu2. eqButUID s s1 \<Longrightarrow> uu1 = uu2 \<Longrightarrow> eqButUID (s \<lparr>pass := uu1\<rparr>) (s1 \<lparr>pass := uu2\<rparr>)"

"\<And> uu1 uu2. eqButUID s s1 \<Longrightarrow> uu1 = uu2 \<Longrightarrow> eqButUID (s \<lparr>postIDs := uu1\<rparr>) (s1 \<lparr>postIDs := uu2\<rparr>)"
"\<And> uu1 uu2. eqButUID s s1 \<Longrightarrow> uu1 = uu2 \<Longrightarrow> eqButUID (s \<lparr>owner := uu1\<rparr>) (s1 \<lparr>owner := uu2\<rparr>)"
"\<And> uu1 uu2. eqButUID s s1 \<Longrightarrow> uu1 = uu2 \<Longrightarrow> eqButUID (s \<lparr>post := uu1\<rparr>) (s1 \<lparr>post := uu2\<rparr>)"
"\<And> uu1 uu2. eqButUID s s1 \<Longrightarrow> uu1 = uu2 \<Longrightarrow> eqButUID (s \<lparr>vis := uu1\<rparr>) (s1 \<lparr>vis := uu2\<rparr>)"

"\<And> uu1 uu2. eqButUID s s1 \<Longrightarrow> eqButUIDf uu1 uu2 \<Longrightarrow> eqButUID (s \<lparr>pendingFReqs := uu1\<rparr>) (s1 \<lparr>pendingFReqs := uu2\<rparr>)"
"\<And> uu1 uu2. eqButUID s s1 \<Longrightarrow> eqButUID12 uu1 uu2 \<Longrightarrow> eqButUID (s \<lparr>friendReq := uu1\<rparr>) (s1 \<lparr>friendReq := uu2\<rparr>)"
"\<And> uu1 uu2. eqButUID s s1 \<Longrightarrow> eqButUIDf uu1 uu2 \<Longrightarrow> eqButUID (s \<lparr>friendIDs := uu1\<rparr>) (s1 \<lparr>friendIDs := uu2\<rparr>)"

unfolding eqButUID_def by auto

subsection\<open>Value Setup\<close>

datatype "value" =
  FrVal bool \<comment> \<open>updated friendship status between \<open>UID1\<close> and \<open>UID2\<close>\<close>
| OVal bool \<comment> \<open>updated dynamic declassification trigger condition\<close>

text \<open>The dynamic declassification trigger condition holds, i.e.~the access window to the
confidential information is open, as long as the two users have not been created yet (so there
cannot be friendship between them) or one of them is friends with an observer.\<close>

definition openByA :: "state \<Rightarrow> bool" \<comment> \<open>Openness by absence\<close>
where "openByA s \<equiv> \<not> UID1 \<in>\<in> userIDs s \<or> \<not> UID2 \<in>\<in> userIDs s"

definition openByF :: "state \<Rightarrow> bool" \<comment> \<open>Openness by friendship\<close>
where "openByF s \<equiv> \<exists>uid \<in> UIDs. uid \<in>\<in> friendIDs s UID1 \<or> uid \<in>\<in> friendIDs s UID2"

definition "open" :: "state \<Rightarrow> bool"
where "open s \<equiv> openByA s \<or> openByF s"

lemmas open_defs = open_def openByA_def openByF_def

definition "friends12" :: "state \<Rightarrow> bool"
where "friends12 s \<equiv> UID1 \<in>\<in> friendIDs s UID2 \<and> UID2 \<in>\<in> friendIDs s UID1"

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
                                  "IDsOK s [UID1, UID2] []"
                                  "\<not>friends12 s" "friends12 s'"
      | (Unfriend) uid p uid' where "a = Dact (dFriend uid p uid')" "ou = outOK" "f ?trn = FrVal False"
                                    "uid = UID1 \<and> uid' = UID2 \<or> uid = UID2 \<and> uid' = UID1"
                                    "IDsOK s [UID1, UID2] []"
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
  then have trn: "a = Cact (cFriend uid p uid')" "s = s1" "s' = s1'" "ou = ou1" by auto
  then have uids: "uid \<in> UIDs \<and> uid' \<in> {UID1, UID2} \<or> uid \<in> {UID1, UID2} \<and> uid' \<in> UIDs" "ou = outOK"
                  "\<not>openByF s1" "openByF s1'" "\<not>openByA s1" "\<not>openByA s1'"
    using op step by (auto simp add: c_defs open_def openByA_def openByF_def)
  then show thesis using op trn step UID1_UID2_UIDs UID1_UID2 by (intro OpenF) auto
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
  then have trn: "a = Dact (dFriend uid p uid')" "s = s1" "s' = s1'" "ou = ou1" by auto
  then have uids: "uid \<in> UIDs \<and> uid' \<in> {UID1, UID2} \<or> uid \<in> {UID1, UID2} \<and> uid' \<in> UIDs" "ou = outOK"
                  "openByF s1" "\<not>openByF s1'" "\<not>openByA s1" "\<not>openByA s1'"
    using op step by (auto simp add: d_defs open_def openByA_def openByF_def)
  then show thesis using op trn step UID1_UID2_UIDs UID1_UID2 by (auto intro: CloseF)
next
  fix s1 uid p uid' p' ou1 s1'
  assume op: "open s1 \<noteq> open s1'"
     and "?trn = Trans s1 (Cact (cUser uid p uid' p')) ou1 s1'"
  then have trn: "a = Cact (cUser uid p uid' p')" "s = s1" "s' = s1'" "ou = ou1" by auto
  then have uids: "uid' = UID2 \<or> uid' = UID1" "ou = outOK"
                  "\<not>openByF s1" "\<not>openByF s1'" "openByA s1" "\<not>openByA s1'"
    using op step by (auto simp add: c_defs open_def openByF_def openByA_def)
  then show thesis using trn step UID1_UID2_UIDs UID1_UID2 by (intro CloseA) auto
qed

lemma step_open_\<phi>:
assumes "step s a = (ou, s')"
and "open s \<noteq> open s'"
shows "\<phi> (Trans s a ou s')"
using assms proof (cases a)
  case (Sact sa) then show ?thesis using assms UID1_UID2 by (cases sa) (auto simp: s_defs open_defs) next
  case (Cact ca) then show ?thesis using assms by (cases ca) (auto simp: c_defs open_defs) next
  case (Dact da) then show ?thesis using assms by (cases da) (auto simp: d_defs open_defs) next
  case (Uact ua) then show ?thesis using assms by (cases ua) (auto simp: u_defs open_defs)
qed auto

lemma step_friends12_\<phi>:
assumes "step s a = (ou, s')"
and "friends12 s \<noteq> friends12 s'"
shows "\<phi> (Trans s a ou s')"
using assms proof (cases a)
  case (Sact sa) then show ?thesis using assms by (cases sa) (auto simp: s_defs friends12_def) next
  case (Cact ca) then show ?thesis using assms by (cases ca) (auto simp: c_defs friends12_def) next
  case (Dact da) then show ?thesis using assms by (cases da) (auto simp: d_defs friends12_def) next
  case (Uact ua) then show ?thesis using assms by (cases ua) (auto simp: u_defs friends12_def)
qed auto

lemma eqButUID_friends12_set_friendIDs_eq:
assumes ss1: "eqButUID s s1"
and f12: "friends12 s = friends12 s1"
and rs: "reach s" and rs1: "reach s1"
shows "set (friendIDs s uid) = set (friendIDs s1 uid)"
proof -
  have dfIDs: "distinct (friendIDs s uid)" "distinct (friendIDs s1 uid)"
    using reach_distinct_friends_reqs[OF rs] reach_distinct_friends_reqs[OF rs1] by auto
  from f12 have uid12: "UID1 \<in>\<in> friendIDs s UID2 \<longleftrightarrow> UID1 \<in>\<in> friendIDs s1 UID2"
                       "UID2 \<in>\<in> friendIDs s UID1 \<longleftrightarrow> UID2 \<in>\<in> friendIDs s1 UID1"
    using reach_friendIDs_symmetric[OF rs] reach_friendIDs_symmetric[OF rs1]
    unfolding friends12_def by auto
  from ss1 have fIDs: "eqButUIDf (friendIDs s) (friendIDs s1)" unfolding eqButUID_def by simp
  show "set (friendIDs s uid) = set (friendIDs s1 uid)"
  proof (intro equalityI subsetI)
    fix uid'
    assume "uid' \<in>\<in> friendIDs s uid"
    then show "uid' \<in>\<in> friendIDs s1 uid"
      using fIDs dfIDs uid12 eqButUIDf_not_UID' unfolding eqButUIDf_def
      by (metis (no_types, lifting) insert_iff prod.inject singletonD)
  next
    fix uid'
    assume "uid' \<in>\<in> friendIDs s1 uid"
    then show "uid' \<in>\<in> friendIDs s uid"
      using fIDs dfIDs uid12 eqButUIDf_not_UID' unfolding eqButUIDf_def
      by (metis (no_types, lifting) insert_iff prod.inject singletonD)
  qed
qed


lemma distinct_remove1_idem: "distinct xs \<Longrightarrow> remove1 y (remove1 y xs) = remove1 y xs"
by (induction xs) (auto simp add: remove1_idem)

lemma Cact_cFriend_step_eqButUID:
assumes step: "step s (Cact (cFriend uid p uid')) = (ou,s')"
and s: "reach s"
and uids: "(uid = UID1 \<and> uid' = UID2) \<or> (uid = UID2 \<and> uid' = UID1)" (is "?u12 \<or> ?u21")
shows "eqButUID s s'"
using assms proof (cases)
  assume ou: "ou = outOK"
  then have "uid' \<in>\<in> pendingFReqs s uid" using step by (auto simp add: c_defs)
  then have fIDs: "uid' \<notin> set (friendIDs s uid)" "uid \<notin> set (friendIDs s uid')"
        and fRs: "distinct (pendingFReqs s uid)" "distinct (pendingFReqs s uid')"
    using reach_distinct_friends_reqs[OF s] by auto
  have "eqButUIDf (friendIDs s) (friendIDs (createFriend s uid p uid'))"
    using fIDs uids UID1_UID2 unfolding eqButUIDf_def
    by (cases "?u12") (auto simp add: c_defs remove1_idem remove1_append)
  moreover have "eqButUIDf (pendingFReqs s) (pendingFReqs (createFriend s uid p uid'))"
    using fRs uids UID1_UID2 unfolding eqButUIDf_def
    by (cases "?u12") (auto simp add: c_defs distinct_remove1_idem)
  moreover have "eqButUID12 (friendReq s) (friendReq (createFriend s uid p uid'))"
    using uids unfolding eqButUID12_def
    by (auto simp add: c_defs fun_upd2_eq_but_a_b)
  ultimately show "eqButUID s s'" using step ou unfolding eqButUID_def by (auto simp add: c_defs)
qed (auto)

lemma Cact_cFriendReq_step_eqButUID:
assumes step: "step s (Cact (cFriendReq uid p uid' req)) = (ou,s')"
and uids: "(uid = UID1 \<and> uid' = UID2) \<or> (uid = UID2 \<and> uid' = UID1)" (is "?u12 \<or> ?u21")
shows "eqButUID s s'"
using assms proof (cases)
  assume ou: "ou = outOK"
  then have "uid \<notin> set (pendingFReqs s uid')" "uid \<notin> set (friendIDs s uid')"
    using step by (auto simp add: c_defs)
  then have "eqButUIDf (pendingFReqs s) (pendingFReqs (createFriendReq s uid p uid' req))"
    using uids UID1_UID2 unfolding eqButUIDf_def
    by (cases "?u12") (auto simp add: c_defs remove1_idem remove1_append)
  moreover have "eqButUID12 (friendReq s) (friendReq (createFriendReq s uid p uid' req))"
    using uids unfolding eqButUID12_def
    by (auto simp add: c_defs fun_upd2_eq_but_a_b)
  ultimately show "eqButUID s s'" using step ou unfolding eqButUID_def by (auto simp add: c_defs)
qed (auto)


lemma Dact_dFriend_step_eqButUID:
assumes step: "step s (Dact (dFriend uid p uid')) = (ou,s')"
and s: "reach s"
and uids: "(uid = UID1 \<and> uid' = UID2) \<or> (uid = UID2 \<and> uid' = UID1)" (is "?u12 \<or> ?u21")
shows "eqButUID s s'"
using assms proof (cases)
  assume ou: "ou = outOK"
  then have "uid' \<in>\<in> friendIDs s uid" using step by (auto simp add: d_defs)
  then have fRs: "distinct (friendIDs s uid)" "distinct (friendIDs s uid')"
    using reach_distinct_friends_reqs[OF s] by auto
  have "eqButUIDf (friendIDs s) (friendIDs (deleteFriend s uid p uid'))"
    using fRs uids UID1_UID2 unfolding eqButUIDf_def
    by (cases "?u12") (auto simp add: d_defs remove1_idem distinct_remove1_removeAll)
  then show "eqButUID s s'" using step ou unfolding eqButUID_def by (auto simp add: d_defs)
qed (auto)


(* Key lemma: *)
lemma eqButUID_step:
assumes ss1: "eqButUID s s1"
and step: "step s a = (ou,s')"
and step1: "step s1 a = (ou1,s1')"
and rs: "reach s"
and rs1: "reach s1"
shows "eqButUID s' s1'"
proof -
  note simps = eqButUID_def s_defs c_defs u_defs r_defs l_defs
  from assms show ?thesis proof (cases a)
    case (Sact sa) with assms show ?thesis by (cases sa) (auto simp add: simps)
  next
    case (Cact ca) note a = this
      with assms show ?thesis proof (cases ca)
        case (cFriendReq uid p uid' req) note ca = this
          then show ?thesis
          proof (cases "(uid = UID1 \<and> uid' = UID2) \<or> (uid = UID2 \<and> uid' = UID1)")
            case True
              then have "eqButUID s s'" and "eqButUID s1 s1'"
                using step step1 unfolding a ca
                by (auto intro: Cact_cFriendReq_step_eqButUID)
              with ss1 show "eqButUID s' s1'" by (auto intro: eqButUID_sym eqButUID_trans)
          next
            case False
              have fRs: "eqButUIDf (pendingFReqs s) (pendingFReqs s1)"
               and fIDs: "eqButUIDf (friendIDs s) (friendIDs s1)" using ss1 by (auto simp: simps)
              then have uid_uid': "uid \<in>\<in> pendingFReqs s uid' \<longleftrightarrow> uid \<in>\<in> pendingFReqs s1 uid'"
                                  "uid \<in>\<in> friendIDs s uid' \<longleftrightarrow> uid \<in>\<in> friendIDs s1 uid'"
                using False by (auto intro!: eqButUIDf_not_UID')
              have "eqButUIDf ((pendingFReqs s)(uid' := pendingFReqs s uid' ## uid))
                              ((pendingFReqs s1)(uid' := pendingFReqs s1 uid' ## uid))"
                using fRs False
                by (intro eqButUIDf_cong) (auto simp add: remove1_append remove1_idem eqButUIDf_def)
              moreover have "eqButUID12 (fun_upd2 (friendReq s) uid uid' req)
                                        (fun_upd2 (friendReq s1) uid uid' req)"
                using ss1 by (intro eqButUID12_cong) (auto simp: simps)
              moreover have "e_createFriendReq s uid p uid' req
                         \<longleftrightarrow> e_createFriendReq s1 uid p uid' req"
                using uid_uid' ss1 by (auto simp: simps)
              ultimately show ?thesis using assms unfolding a ca by (auto simp: simps)
          qed
      next
        case (cFriend uid p uid') note ca = this
          then show ?thesis
          proof (cases "(uid = UID1 \<and> uid' = UID2) \<or> (uid = UID2 \<and> uid' = UID1)")
            case True
              then have "eqButUID s s'" and "eqButUID s1 s1'"
                using step step1 rs rs1 unfolding a ca
                by (auto intro!: Cact_cFriend_step_eqButUID)+
              with ss1 show "eqButUID s' s1'" by (auto intro: eqButUID_sym eqButUID_trans)
          next
            case False
              have fRs: "eqButUIDf (pendingFReqs s) (pendingFReqs s1)"
                    (is "eqButUIDf (?pfr s) (?pfr s1)")
               and fIDs: "eqButUIDf (friendIDs s) (friendIDs s1)" using ss1 by (auto simp: simps)
              then have uid_uid': "uid \<in>\<in> pendingFReqs s uid' \<longleftrightarrow> uid \<in>\<in> pendingFReqs s1 uid'"
                                  "uid' \<in>\<in> pendingFReqs s uid \<longleftrightarrow> uid' \<in>\<in> pendingFReqs s1 uid"
                                  "uid \<in>\<in> friendIDs s uid' \<longleftrightarrow> uid \<in>\<in> friendIDs s1 uid'"
                                  "uid' \<in>\<in> friendIDs s uid \<longleftrightarrow> uid' \<in>\<in> friendIDs s1 uid"
                using False by (auto intro!: eqButUIDf_not_UID')
              have "eqButUIDl UID1 (remove1 uid' (?pfr s UID2)) (remove1 uid' (?pfr s1 UID2))"
               and "eqButUIDl UID2 (remove1 uid' (?pfr s UID1)) (remove1 uid' (?pfr s1 UID1))"
               and "eqButUIDl UID1 (remove1 uid (?pfr s UID2)) (remove1 uid (?pfr s1 UID2))"
               and "eqButUIDl UID2 (remove1 uid (?pfr s UID1)) (remove1 uid (?pfr s1 UID1))"
               using fRs unfolding eqButUIDf_def
               by (auto intro!: eqButUIDl_remove1_cong simp del: eqButUIDl.simps)
              then have 1: "eqButUIDf ((?pfr s)(uid := remove1 uid' (?pfr s uid),
                                                uid' := remove1 uid (?pfr s uid')))
                                     ((?pfr s1)(uid := remove1 uid' (?pfr s1 uid),
                                                uid' := remove1 uid (?pfr s1 uid')))"
                using fRs False
                by (intro eqButUIDf_cong) (auto simp add: eqButUIDf_def)
              have "uid = UID1 \<Longrightarrow> eqButUIDl UID2 (friendIDs s UID1 ## uid') (friendIDs s1 UID1 ## uid')"
               and "uid = UID2 \<Longrightarrow> eqButUIDl UID1 (friendIDs s UID2 ## uid') (friendIDs s1 UID2 ## uid')"
               and "uid' = UID1 \<Longrightarrow> eqButUIDl UID2 (friendIDs s UID1 ## uid) (friendIDs s1 UID1 ## uid)"
               and "uid' = UID2 \<Longrightarrow> eqButUIDl UID1 (friendIDs s UID2 ## uid) (friendIDs s1 UID2 ## uid)"
                using fIDs uid_uid' by - (intro eqButUIDl_snoc_cong; simp add: eqButUIDf_def)+
              then have 2: "eqButUIDf ((friendIDs s)(uid := friendIDs s uid ## uid',
                                                      uid' := friendIDs s uid' ## uid))
                                       ((friendIDs s1)(uid := friendIDs s1 uid ## uid',
                                                       uid' := friendIDs s1 uid' ## uid))"
                using fIDs by (intro eqButUIDf_cong) (auto simp add: eqButUIDf_def)
              have 3: "eqButUID12 (fun_upd2 (fun_upd2 (friendReq s) uid' uid emptyReq)
                                                                    uid uid' emptyReq)
                                  (fun_upd2 (fun_upd2 (friendReq s1) uid' uid emptyReq)
                                                                     uid uid' emptyReq)"
                using ss1 by (intro eqButUID12_cong) (auto simp: simps)
              have "e_createFriend s uid p uid'
                \<longleftrightarrow> e_createFriend s1 uid p uid'"
                using uid_uid' ss1 by (auto simp: simps)
              with 1 2 3 show ?thesis using assms unfolding a ca by (auto simp: simps)
          qed
      qed (auto simp: simps)
  next
    case (Uact ua) with assms show ?thesis by (cases ua) (auto simp add: simps)
  next
    case (Ract ra) with assms show ?thesis by (cases ra) (auto simp add: simps)
  next
    case (Lact la) with assms show ?thesis by (cases la) (auto simp add: simps)
  next
    case (Dact da) note a = this
      with assms show ?thesis proof (cases da)
        case (dFriend uid p uid') note ca = this
          then show ?thesis
          proof (cases "(uid = UID1 \<and> uid' = UID2) \<or> (uid = UID2 \<and> uid' = UID1)")
            case True
              then have "eqButUID s s'" and "eqButUID s1 s1'"
                using step step1 rs rs1 unfolding a ca
                by (auto intro!: Dact_dFriend_step_eqButUID)+
              with ss1 show "eqButUID s' s1'" by (auto intro: eqButUID_sym eqButUID_trans)
          next
            case False
              have fIDs: "eqButUIDf (friendIDs s) (friendIDs s1)" using ss1 by (auto simp: simps)
              then have uid_uid': "uid \<in>\<in> friendIDs s uid' \<longleftrightarrow> uid \<in>\<in> friendIDs s1 uid'"
                                  "uid' \<in>\<in> friendIDs s uid \<longleftrightarrow> uid' \<in>\<in> friendIDs s1 uid"
                using False by (auto intro!: eqButUIDf_not_UID')
              have dfIDs: "distinct (friendIDs s uid)" "distinct (friendIDs s uid')"
                          "distinct (friendIDs s1 uid)" "distinct (friendIDs s1 uid')"
                using reach_distinct_friends_reqs[OF rs] reach_distinct_friends_reqs[OF rs1] by auto
              have "uid = UID1 \<Longrightarrow> eqButUIDl UID2 (remove1 uid' (friendIDs s UID1)) (remove1 uid' (friendIDs s1 UID1))"
               and "uid = UID2 \<Longrightarrow> eqButUIDl UID1 (remove1 uid' (friendIDs s UID2)) (remove1 uid' (friendIDs s1 UID2))"
               and "uid' = UID1 \<Longrightarrow> eqButUIDl UID2 (remove1 uid (friendIDs s UID1)) (remove1 uid (friendIDs s1 UID1))"
               and "uid' = UID2 \<Longrightarrow> eqButUIDl UID1 (remove1 uid (friendIDs s UID2)) (remove1 uid (friendIDs s1 UID2))"
                using fIDs uid_uid' by - (intro eqButUIDl_remove1_cong; simp add: eqButUIDf_def)+
              then have 1: "eqButUIDf ((friendIDs s)(uid := remove1 uid' (friendIDs s uid),
                                                      uid' := remove1 uid (friendIDs s uid')))
                                       ((friendIDs s1)(uid := remove1 uid' (friendIDs s1 uid),
                                                       uid' := remove1 uid (friendIDs s1 uid')))"
                using fIDs by (intro eqButUIDf_cong) (auto simp add: eqButUIDf_def)
              have "e_deleteFriend s uid p uid'
                \<longleftrightarrow> e_deleteFriend s1 uid p uid'"
                using uid_uid' ss1 by (auto simp: simps d_defs)
              with 1 show ?thesis using assms dfIDs unfolding a ca
                by (auto simp: simps d_defs distinct_remove1_removeAll)
          qed
      qed
  qed
qed

lemma eqButUID_openByA_eq:
assumes "eqButUID s s1"
shows "openByA s = openByA s1"
using assms unfolding openByA_def eqButUID_def by auto

lemma eqButUID_openByF_eq:
assumes ss1: "eqButUID s s1"
shows "openByF s = openByF s1"
proof -
  from ss1 have fIDs: "eqButUIDf (friendIDs s) (friendIDs s1)" unfolding eqButUID_def by auto
  have "\<forall>uid \<in> UIDs. uid \<in>\<in> friendIDs s UID1 \<longleftrightarrow> uid \<in>\<in> friendIDs s1 UID1"
    using UID1_UID2_UIDs UID1_UID2 by (intro ballI eqButUIDf_not_UID'[OF fIDs]; auto)
  moreover have "\<forall>uid \<in> UIDs. uid \<in>\<in> friendIDs s UID2 \<longleftrightarrow> uid \<in>\<in> friendIDs s1 UID2"
    using UID1_UID2_UIDs UID1_UID2 by (intro ballI eqButUIDf_not_UID'[OF fIDs]; auto)
  ultimately show "openByF s = openByF s1" unfolding openByF_def by auto
qed

lemma eqButUID_open_eq: "eqButUID s s1 \<Longrightarrow> open s = open s1"
using eqButUID_openByA_eq eqButUID_openByF_eq unfolding open_def by blast

lemma eqButUID_step_friendIDs_eq:
assumes ss1: "eqButUID s s1"
and rs: "reach s" and rs1: "reach s1"
and step: "step s a = (ou,s')" and step1: "step s1 a = (ou1,s1')"
and a: "a \<noteq> Cact (cFriend UID1 (pass s UID1) UID2) \<and> a \<noteq> Cact (cFriend UID2 (pass s UID2) UID1) \<and>
        a \<noteq> Dact (dFriend UID1 (pass s UID1) UID2) \<and> a \<noteq> Dact (dFriend UID2 (pass s UID2) UID1)"
and "friendIDs s = friendIDs s1"
shows "friendIDs s' = friendIDs s1'"
using assms proof (cases a)
  case (Sact sa) then show ?thesis using assms by (cases sa) (auto simp: s_defs) next
  case (Uact ua) then show ?thesis using assms by (cases ua) (auto simp: u_defs) next
  case (Dact da) then show ?thesis using assms proof (cases da)
    case (dFriend uid p uid')
      with Dact assms show ?thesis
        by (cases "(uid,uid') \<in> {(UID1,UID2), (UID2,UID1)}")
           (auto simp: d_defs eqButUID_def eqButUIDf_not_UID')
    qed
next
  case (Cact ca) then show ?thesis using assms proof (cases ca)
    case (cFriend uid p uid')
      with Cact assms show ?thesis
        by (cases "(uid,uid') \<in> {(UID1,UID2), (UID2,UID1)}")
           (auto simp: c_defs eqButUID_def eqButUIDf_not_UID')
    qed (auto simp: c_defs)
qed auto

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

(* Key lemma: *)
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
    using a ss1 unfolding eqButUID_def by auto
  ultimately show "\<phi> (Trans s a ou s')" using rs rs1 step step1
    by (intro eqButUID_step_\<phi>_imp[of s1 s])
qed

lemma createFriend_sym: "createFriend s uid p uid' = createFriend s uid' p' uid"
unfolding c_defs by (cases "uid = uid'") (auto simp: fun_upd2_comm fun_upd_twist)

lemma deleteFriend_sym: "deleteFriend s uid p uid' = deleteFriend s uid' p' uid"
unfolding d_defs by (cases "uid = uid'") (auto simp: fun_upd_twist)

lemma createFriendReq_createFriend_absorb:
assumes "e_createFriendReq s uid' p uid req"
shows "createFriend (createFriendReq s uid' p1 uid req) uid p2 uid' = createFriend s uid p3 uid'"
using assms unfolding c_defs by (auto simp: remove1_idem remove1_append fun_upd2_absorb)

lemma eqButUID_deleteFriend12_friendIDs_eq:
assumes ss1: "eqButUID s s1"
and rs: "reach s" and rs1: "reach s1"
shows "friendIDs (deleteFriend s UID1 p UID2) = friendIDs (deleteFriend s1 UID1 p' UID2)"
proof -
  have "distinct (friendIDs s UID1)" "distinct (friendIDs s UID2)"
       "distinct (friendIDs s1 UID1)" "distinct (friendIDs s1 UID2)"
    using rs rs1 by (auto intro: reach_distinct_friends_reqs)
  then show ?thesis
    using ss1 unfolding eqButUID_def eqButUIDf_def unfolding d_defs
    by (auto simp: distinct_remove1_removeAll)
qed

lemma eqButUID_createFriend12_friendIDs_eq:
assumes ss1: "eqButUID s s1"
and rs: "reach s" and rs1: "reach s1"
and f12: "\<not>friends12 s" "\<not>friends12 s1"
shows "friendIDs (createFriend s UID1 p UID2) = friendIDs (createFriend s1 UID1 p' UID2)"
proof -
  have f12': "UID1 \<notin> set (friendIDs s UID2)" "UID2 \<notin> set (friendIDs s UID1)"
             "UID1 \<notin> set (friendIDs s1 UID2)" "UID2 \<notin> set (friendIDs s1 UID1)"
    using f12 rs rs1 reach_friendIDs_symmetric unfolding friends12_def by auto
  have "friendIDs s = friendIDs s1"
  proof (intro ext)
    fix uid
    show "friendIDs s uid = friendIDs s1 uid"
      using ss1 f12' unfolding eqButUID_def eqButUIDf_def
      by (cases "uid = UID1 \<or> uid = UID2") (auto simp: remove1_idem)
  qed
  then show ?thesis by (auto simp: c_defs)
qed

end
