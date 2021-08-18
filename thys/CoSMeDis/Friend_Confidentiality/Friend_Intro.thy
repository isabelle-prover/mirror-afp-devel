theory Friend_Intro
  imports "../Safety_Properties"
begin

section \<open>Friendship status confidentiality\<close>

text \<open>\label{sec:friend}
We verify the following property:

\ \\
Given a coalition consisting of groups of users \<open>UIDs j\<close> from multiple nodes \<open>j\<close>
and given two users \<open>UID1\<close> and \<open>UID2\<close> at some node \<open>i\<close> who are not in these groups,

the coalition cannot learn anything about the changes in the status
of friendship between \<open>UID1\<close> and \<open>UID2\<close>

beyond what everybody knows, namely that
  \<^item> there is no friendship between them before those users have been created, and
  \<^item> the updates form an alternating sequence of friending and unfriending,

and beyond those updates performed while or last before
a user in the group \<open>UIDs i\<close> is friends with \<open>UID1\<close> or \<open>UID2\<close>.

\ \\
The approach to proving this is similar to that for post confidentiality (explained
in the introduction of the post confidentiality section~\ref{sec:post}), but conceptually simpler
since here secret information is not communicated between different nodes (so we
don't need to distinguish between an issuer node and the other, receiver nodes).

Moreover, here we do not consider static versions of the bounds, but go directly for
the dynamic ones. Also, we prove directly the BD security for a network of \<open>n\<close> nodes,
omitting the case of two nodes.

Note that, unlike for post confidentiality, here remote friendship plays
no role in the statement of the property. This is because, in CoSMeDis, the listing
of a user's friends is only available to local (same-node) friends of that user,
and not to the remote (outer) friends.
\<close>

end
