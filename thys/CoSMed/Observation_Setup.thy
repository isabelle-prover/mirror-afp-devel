(* The observation functions, the same for all our confidentiality properties *)
theory Observation_Setup
imports Safety_Properties
begin

section\<open>The observation setup\<close>

text \<open>The observers are a arbitrary but fixed set of users:\<close>

consts UIDs :: "userID set"

type_synonym obs = "act * out"

text \<open>The observations are all their actions:\<close>

fun \<gamma> :: "(state,act,out) trans \<Rightarrow> bool" where
"\<gamma> (Trans _ a _ _) =
 (userOfA a \<in> Some ` UIDs)"

fun g :: "(state,act,out)trans \<Rightarrow> obs" where
"g (Trans _ a ou _) = (a,ou)"


end
