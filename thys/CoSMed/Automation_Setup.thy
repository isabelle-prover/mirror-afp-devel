theory Automation_Setup
imports System_Specification
begin

lemma add_prop:
  assumes "PROP (T)"
  shows "A ==> PROP (T)"
  using assms .


lemmas exhaust_elim =
   sActt.exhaust[of x, THEN add_prop[where A="a=Sact x"], rotated -1]
   cActt.exhaust[of x, THEN add_prop[where A="a=Cact x"], rotated -1]
   uActt.exhaust[of x, THEN add_prop[where A="a=Uact x"], rotated -1]
   rActt.exhaust[of x, THEN add_prop[where A="a=Ract x"], rotated -1]
   lActt.exhaust[of x, THEN add_prop[where A="a=Lact x"], rotated -1]
  for x a


lemma state_cong:
fixes s::state
assumes
"pendingUReqs s = pendingUReqs s1 \<and> userReq s = userReq s1 \<and> userIDs s = userIDs s1 \<and>
 postIDs s = postIDs s1 \<and> admin s = admin s1 \<and>
 user s = user s1 \<and> pass s = pass s1 \<and> pendingFReqs s = pendingFReqs s1 \<and> friendReq s = friendReq s1 \<and> friendIDs s = friendIDs s1 \<and>
 post s = post s1 \<and>
 owner s = owner s1 \<and>
 vis s = vis s1"
shows "s = s1"
using assms by (cases s, cases s1) auto


end