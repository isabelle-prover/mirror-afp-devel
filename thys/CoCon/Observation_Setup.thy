theory Observation_Setup
imports Safety_Properties
begin

section \<open>Observation setup for confidentiality properties\<close>


text \<open>The observation infrastructure, consisting of
a discriminator $\gamma$ and a selector $g$,
is the same for all our confidentiality properties.
Namely, we fix a group UIDs of users, and consider
the actions and outputs of these users.
\<close>

consts UIDs :: "userID set" (* the observers *)

type_synonym obs = "act * out"

fun \<gamma> :: "(state,act,out) trans \<Rightarrow> bool" where
"\<gamma> (Trans _ a _ _) = (userOfA a \<in> UIDs)"

fun g :: "(state,act,out)trans \<Rightarrow> obs" where
"g (Trans _ a ou _) = (a,ou)"


end
