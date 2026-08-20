(*<*)
theory NU_Swap
  imports Main
begin
(*>*)

section \<open>Swappings of Pairs of Atoms\<close>

fun swapa :: "(string \<times> string) \<Rightarrow> string \<Rightarrow> string"
  where
  "swapa (b,c) a = (if b = a then c else (if c = a then b else a))"

fun swapas:: "(string \<times> string) list \<Rightarrow> string \<Rightarrow> string"
  where
  "swapas []     a = a"
| "swapas (x#pi) a = swapa x (swapas pi a)"

lemma swapas_aa[simp]: 
  shows "swapas [(a,a)] b = b"
  by simp

lemma swapas_ab_ba:
  shows "swapas [(a,b)] = swapas [(b,a)]"
  by auto

lemma swapas_append: 
  shows "swapas (pi1@pi2) a = swapas pi1 (swapas pi2 a)"
  by (induct pi1) auto
 
lemma swapas_inv [simp]: 
  shows "swapas (rev pi) (swapas pi a) = a"
  by (induct_tac pi) (auto simp add: swapas_append)

lemma swapas_rev_pi_a: 
  assumes "swapas pi a = b"
  shows "swapas (rev pi) b = a"
using assms by auto

lemma swapas_rev_swapas_id [simp]: 
  shows "swapas pi (swapas (rev pi) a) = a"
  by (metis swapas_rev_pi_a)

lemma swapas_rev_pi_b: 
  assumes "swapas (rev pi) a = b"
  shows "swapas pi b = a"
using assms by auto

lemma swapas_comm: 
  shows "(swapas (pi@[(a,b)]) c) = (swapas ([(swapas pi a,swapas pi b)]@pi) c)"
  by (metis swapa.simps swapas.simps(1,2) swapas_append swapas_rev_pi_a)

(*<*)
end
(*>*)