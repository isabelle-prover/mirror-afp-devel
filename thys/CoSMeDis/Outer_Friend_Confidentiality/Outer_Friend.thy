theory Outer_Friend
  imports Outer_Friend_Intro
begin


type_synonym obs = "act * out"

text \<open>The observers \<open>UIDs j\<close> are an arbitrary, but fixed sets of users at each node \<open>j\<close> of the
network, and the secret is the friendship information of user \<open>UID\<close> at node \<open>AID\<close>.\<close>

locale OuterFriend =
fixes UIDs :: "apiID \<Rightarrow> userID set"
and AID :: "apiID"
and UID :: "userID"
assumes UID_UIDs: "UID \<notin> UIDs AID"
and emptyUserID_not_UIDs: "\<And>aid. emptyUserID \<notin> UIDs aid"

datatype "value" =
  isFrVal: FrVal apiID userID bool \<comment> \<open>updates to the friendship status of UID\<close>
| isOVal: OVal bool \<comment> \<open>a change in the ``openness" status of the UID friendship info\<close>

end
