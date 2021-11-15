theory Friend_Request_Intro
  imports
    "../Friend_Confidentiality/Friend_Openness"
    "../Friend_Confidentiality/Friend_State_Indistinguishability"
begin

section \<open>Friendship request confidentiality\<close>

text \<open>
We verify the following property:

\ \\
Given a coalition consisting of groups of users \<open>UIDs j\<close> from multiple nodes \<open>j\<close>
and given two users \<open>UID1\<close> and \<open>UID2\<close> at some node \<open>i\<close> who are not in these groups,

the coalition cannot learn anything about the the friendship requests issued between
\<open>UID1\<close> and \<open>UID2\<close>

beyond what everybody knows, namely that
  \<^item> every successful friend creation is preceded by at least one and at most two requests, and
  \<^item> friendship status updates form an alternating sequence of friending and unfriending,

and beyond the existence of requests issued while or last before
a user in the group \<open>UIDs i\<close> is a local friend of \<open>UID1\<close> or \<open>UID2\<close>.

\ \\
The approach here is similar to that for friendship status confidentiality
(explained in the introduction of Section~\ref{sec:friend}).
Like in the case of friendship status, here secret information is not communicated
between different nodes (so again we don't need to distinguish between an issuer node
and the other, receiver nodes).
\<close>

end
