(*<*)
theory NU_Atoms 
imports NU_Terms
begin
(*>*)

section \<open>Facts about Atoms Occurring in Swappings\<close>

fun atms :: "(string \<times> string) list \<Rightarrow> string set" where
"atms [] = {}" | 
"atms (x#xs) = ((atms xs) \<union>  {fst(x),snd(x)})"

lemma atms_append[simp]: 
  shows "atms (xs@ys) = atms xs \<union> atms ys"
  by (induct xs) auto

lemma atms_rev[simp]: 
  shows "atms (rev pi) = atms pi"
  by (induct pi) auto

lemma a_not_in_atms: 
  assumes "a \<notin> atms pi"
  shows "a = swapas pi a"
  using assms by (induct pi) auto

lemma swapas_pi_ineq_a: 
  assumes  "swapas pi a \<noteq> a"
  shows "a \<in> atms pi"
  using a_not_in_atms assms by force

lemma a_ineq_swapas_pi: 
  assumes "a \<noteq> swapas pi a"
  shows "a \<in> atms pi"
  using a_not_in_atms assms by blast

lemma swapas_pi_in_atms: 
  assumes "a \<in> atms pi" 
  shows"swapas pi a \<in> atms pi"
  using assms by (metis a_not_in_atms swapas_rev_pi_a)

(*<*)
end
(*>*)