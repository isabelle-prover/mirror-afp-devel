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
   comActt.exhaust[of x, THEN add_prop[where A="a=COMact x"], rotated -1]
  for x a


lemma state_cong:
fixes s::state
assumes
"pendingUReqs s = pendingUReqs s1 \<and> userReq s = userReq s1 \<and> userIDs s = userIDs s1 \<and>
 postIDs s = postIDs s1 \<and> admin s = admin s1 \<and>
 user s = user s1 \<and> pass s = pass s1 \<and> pendingFReqs s = pendingFReqs s1 \<and> friendReq s = friendReq s1 \<and> friendIDs s = friendIDs s1 \<and>
 sentOuterFriendIDs s = sentOuterFriendIDs s1 \<and>
 recvOuterFriendIDs s = recvOuterFriendIDs s1 \<and>
 post s = post s1 \<and>
 owner s = owner s1 \<and> vis s = vis s1 \<and>
 pendingSApiReqs s = pendingSApiReqs s1 \<and> sApiReq s = sApiReq s1 \<and> serverApiIDs s = serverApiIDs s1 \<and> serverPass s = serverPass s1 \<and>
 outerPostIDs s = outerPostIDs s1 \<and> outerPost s = outerPost s1 \<and>
 outerOwner s = outerOwner s1 \<and> outerVis s = outerVis s1 \<and>
 pendingCApiReqs s = pendingCApiReqs s1 \<and> cApiReq s = cApiReq s1 \<and> clientApiIDs s = clientApiIDs s1 \<and> clientPass s = clientPass s1 \<and>
 sharedWith s = sharedWith s1"
shows "s = s1"
using assms apply (cases s, cases s1) by auto

(*
lemma Paper_dest_conv:
  "(p =
        Paper title abstract content reviews dis decs fcontent) \<longleftrightarrow>
  title = titlePaper p \<and>
  abstract = abstractPaper p \<and>
  content = contentPaper p \<and>
  reviews = reviewsPaper p \<and>
  dis = disPaper p \<and>
  decs = decsPaper p \<and>
  fcontent = fcontentPaper p
  "
  by (cases p) auto
*)

end
