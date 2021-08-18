theory Outer_Friend_Intro
  imports "../Safety_Properties"
begin

section \<open>Remote (outer) friendship status confidentiality\<close>

text \<open>
We verify the following property, which is specific to CosMeDis,
in that it does not have a CoSMed counterpart:
Given a coalition consisting of groups of users \<open>UIDs j\<close> from multiple nodes \<open>j\<close>
and a user \<open>UID\<close> at some node \<open>i\<close> not in these groups,

the coalition may learn about the \<^emph>\<open>occurrence\<close> of remote friendship actions of \<open>UID\<close>
(because network traffic is assumed to be observable),

but they learn nothing about the \<^emph>\<open>content\<close> (who was added or deleted as a friend)
of remote friendship actions between \<open>UID\<close> and remote users who are not in the coalition

beyond what everybody knows, namely that, with respect to each other user \<open>uid'\<close>,
those actions form an alternating sequence of friending and unfriending,

unless a user in \<open>UIDs i\<close> becomes a local friend of \<open>UID\<close>.

\ \\
Similarly to the other properties, this property is proved using the
system compositionality and transport theorems for BD security.

Note that, unlike inner friendship, outer friendship is not necessarily symmetric.
It is always established from a user of a server to a user of a client, the former giving
the latter unilateral access to his friend-only posts. These unilateral friendship permissions
are stored on the client.

When proving the single-node BD security properties, the bound refers to
outer friendship-status changes issued by the user \<open>UID\<close>
concerning friending or unfriending some user \<open>UID'\<close> located at a node \<open>j\<close>
different from \<open>i\<close>. Such changes occur as communicating actions between
the ``secret issuer'' node \<open>i\<close> and the ``secret receiver'' nodes \<open>j\<close>.
\<close>

end
