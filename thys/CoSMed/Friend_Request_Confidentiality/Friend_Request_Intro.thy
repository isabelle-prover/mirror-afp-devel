theory Friend_Request_Intro
  imports "../Safety_Properties" "../Observation_Setup"
begin

section \<open>Friendship request confidentiality\<close>

text \<open>We prove the following property:

\ \\
Given a group of users \<open>UIDs\<close> and given two users \<open>UID1\<close> and \<open>UID2\<close> not in that group,

that group cannot learn anything about the friendship requests issued between
\<open>UID1\<close> and \<open>UID2\<close>

beyond what everybody knows, namely that
  \<^item> there is no friendship between \<open>UID1\<close> and \<open>UID2\<close> before those users have been created, and
  \<^item> friendship status updates form an alternating sequence of friending and unfriending,
    every successful friend creation is preceded by at least one and at most two requests,

and beyond those requests performed while or last before a user in \<open>UIDs\<close> is friends with
\<open>UID1\<close> or \<open>UID2\<close>.\<close>

end
