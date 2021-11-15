theory Friend_Observation_Setup
  imports Friend_Intro
begin

subsection \<open>Observation setup\<close>

(* *)
type_synonym obs = "act * out"

locale FriendObservationSetup =
  fixes UIDs :: "userID set" \<comment> \<open>local group of observers at a given node\<close>
begin

(*  *)
fun \<gamma> :: "(state,act,out) trans \<Rightarrow> bool" where
"\<gamma> (Trans _ a _ _) = (\<exists> uid. userOfA a = Some uid \<and> uid \<in> UIDs \<or> (\<exists>ca. a = COMact ca))"

fun g :: "(state,act,out)trans \<Rightarrow> obs" where
"g (Trans _ a ou _) = (a,ou)"

end

locale FriendNetworkObservationSetup =
  fixes UIDs :: "apiID \<Rightarrow> userID set" \<comment> \<open>groups of observers at different nodes\<close>
begin

(*  *)
abbreviation \<gamma> :: "apiID \<Rightarrow> (state,act,out) trans \<Rightarrow> bool" where
"\<gamma> aid trn \<equiv> FriendObservationSetup.\<gamma> (UIDs aid) trn"

abbreviation g :: "apiID \<Rightarrow> (state,act,out)trans \<Rightarrow> obs" where
"g aid trn \<equiv> FriendObservationSetup.g trn"

end

end
