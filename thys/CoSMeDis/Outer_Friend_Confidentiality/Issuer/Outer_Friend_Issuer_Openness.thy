theory Outer_Friend_Issuer_Openness
  imports Outer_Friend_Issuer_State_Indistinguishability
begin

subsubsection \<open>Dynamic declassification trigger\<close>

context OuterFriendIssuer
begin

text \<open>The dynamic declassification trigger condition holds, i.e.~the access window to the
confidential information is open, while an observer is a local friend of the user \<open>UID\<close>.\<close>

definition "open" :: "state \<Rightarrow> bool"
where "open s \<equiv> \<exists>uid \<in> UIDs AID. uid \<in>\<in> friendIDs s UID"

lemma open_step_cases:
assumes "open s \<noteq> open s'"
and "step s a = (ou, s')"
obtains
  (OpenF) uid p uid' where "a = Cact (cFriend uid p uid')" "ou = outOK" "p = pass s uid"
                           "uid \<in> UIDs AID \<and> uid' = UID \<or> uid = UID \<and> uid' \<in> UIDs AID"
                           "open s'" "\<not>open s"
| (CloseF) uid p uid' where "a = Dact (dFriend uid p uid')" "ou = outOK" "p = pass s uid"
                            "uid \<in> UIDs AID \<and> uid' = UID \<or> uid = UID \<and> uid' \<in> UIDs AID"
                            "open s" "\<not>open s'"
using assms proof (cases a)
  case (Uact ua) then show ?thesis using assms by (cases ua) (auto simp: u_defs open_def) next
  case (COMact ca) then show ?thesis using assms by (cases ca) (auto simp: com_defs open_def) next
  case (Sact sa)
    then show ?thesis using assms by (cases sa) (auto simp: s_defs open_def)
next
  case (Cact ca)
    then show ?thesis using assms proof (cases ca)
      case (cFriend uid p uid')
        then show ?thesis using Cact assms by (intro OpenF) (auto simp: c_defs open_def)
    qed (auto simp: c_defs open_def)
next
  case (Dact da)
    then show ?thesis using assms proof (cases da)
      case (dFriend uid p uid')
        then show ?thesis using Dact assms by (intro CloseF) (auto simp: d_defs open_def)
    qed
qed auto

lemma COMact_open:
assumes "step s a = (ou, s')"
and "a = COMact ca"
shows "open s = open s'"
by (rule ccontr, insert assms, elim open_step_cases, auto)

lemma eqButUID_open_eq: "eqButUID s s1 \<Longrightarrow> open s = open s1"
using open_def eqButUID_def by auto

end

end
