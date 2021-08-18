theory Friend_Intro
  imports "../Safety_Properties" "../Observation_Setup"
begin

section \<open>Friendship status confidentiality\<close>

text \<open>We prove the following property:

\ \\
Given a group of users \<open>UIDs\<close> and given two users \<open>UID1\<close> and \<open>UID2\<close> not in that group,

that group cannot learn anything about the changes in the status
of friendship between \<open>UID1\<close> and \<open>UID2\<close>

beyond what everybody knows, namely that
  \<^item> there is no friendship between \<open>UID1\<close> and \<open>UID2\<close> before those users have been created, and
  \<^item> the updates form an alternating sequence of friending and unfriending,

and beyond those updates performed while or last before a user in \<open>UIDs\<close> is friends with
\<open>UID1\<close> or \<open>UID2\<close>.\<close>


end