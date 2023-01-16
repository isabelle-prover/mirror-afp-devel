theory Post_Intro
  imports "../Safety_Properties"
begin

section \<open>Post confidentiality\<close>

text \<open>\label{sec:post}
We verify the following BD Security property of the CoSMeDis network:

\ \\
Given a coalition consisting of groups of users \<open>UIDs j\<close> from multiple nodes \<open>j\<close>
and given a post \<open>PID\<close> at node \<open>i\<close>,

the coalition cannot learn anything about the updates to this post

beyond those updates performed while or last before one of the following holds:

(1) Some user in \<open>UIDs i\<close> is the admin at node \<open>i\<close>,
is the owner of \<open>PID\<close> or is friends with the owner of \<open>PID\<close>

(2) \<open>PID\<close> is marked as public

unless some user in \<open>UIDs j\<close> for a node \<open>j\<close> different than \<open>i\<close> is admin of node \<open>j\<close>
or is remote friend with the owner of \<open>PID\<close>.\footnote{So \<open>UIDs\<close> is a function from node
identifiers (called API IDs in this formalization) to sets of user IDs.
We will write \<open>AID\<close> instead of \<open>i\<close> (which will be fixed in our locales)
and \<open>aid\<close> instead of \<open>j\<close>.}

\ \\
As explained in \<^cite>\<open>"cosmedis-SandP2017"\<close>, in order to prove this property
for the CoSMeDis network, we compose BD security properties of
individual CoSMeDis nodes. When formulating the individual node properties, we will
distinguish between the \emph{secret issuer} node \<open>i\<close> and the (potential)
\emph{secret receiver} nodes: all nodes different from \<open>i\<close>. Consequently, we will
have two BD security properties -- for issuers and for receivers -- proved in their
corresponding subsections. Then we prove BD Security for the (binary) composition of an
issuer and a receiver node, and finally we prove BD Security for the n-ary composition
(of an entire CoSMeDis network of nodes).

Described above is the property in a form that employs a dynamic trigger
(i.e., an inductive bound that incorporates an iterated trigger) for the secret issuer
node.
However, the first subsections of this section cover the static version of this (multi-node)
property, corresponding to a static BD security property for the secret issuer.
The dynamic version is covered after that, in a dedicated subsection.

Finally, we lift the above BD security property, which refers to a single secret source,
i.e., a post at some node, to simultaneous BD Security for two independent secret sources,
i.e., two different posts at two (possibly different) nodes. For this, we use the
BD Security system compositionality and transport theorems formalized in the AFP entry
\<^cite>\<open>"BDSecuritycomp-AFP"\<close>.
More details about this approach can be found in \<^cite>\<open>"cosmedis-SandP2017"\<close>;
in particular, Appendix A from that paper discusses the transport theorem.
\<close>

end
