(*<*)
theory NU_Disagreement 
imports NU_Atoms
begin
(*>*)

section \<open>Disagreement Sets\<close>

definition  ds :: "(string \<times> string) list \<Rightarrow> (string \<times> string) list \<Rightarrow> string set" where
  ds_def: "ds xs ys  \<equiv>  { a . a \<in> (atms xs \<union> atms ys) \<and> (swapas xs a \<noteq> swapas ys a) }"

lemma ds_elem: 
  assumes "swapas pi a\<noteq>a"
  shows "a\<in>ds [] pi"
  using assms ds_def swapas_pi_ineq_a by simp

corollary ds_elem_cp: 
  assumes "a \<notin> ds [] pi"
  shows "swapas pi a = a"
  using assms ds_elem by blast

lemma elem_ds: 
  assumes "a\<in>ds [] pi"
  shows "a\<noteq>swapas pi a"
  using assms ds_def by simp

lemma ds_sym: 
  shows "ds pi1 pi2 = ds pi2 pi1"
  using ds_def by auto

lemma ds_trans: 
  assumes "c \<in> ds pi1 pi3"
  shows "c \<in> ds pi1 pi2 \<or> c \<in> ds pi2 pi3"
using assms ds_def a_not_in_atms swapas_pi_ineq_a by auto

lemma ds_cancel_pi_left:
  assumes "c\<in> ds (pi1@pi) (pi2@pi)"
  shows "swapas pi c \<in> ds pi1 pi2"
  using assms ds_def swapas_append a_ineq_swapas_pi a_not_in_atms
  by (metis (mono_tags, lifting) Un_iff mem_Collect_eq)

lemma ds_cancel_pi_right: 
  assumes "swapas pi c \<in> ds pi1 pi2"
  shows "c \<in> ds (pi1@pi) (pi2@pi)"
  using assms 
  unfolding ds_def
  using a_not_in_atms swapas_append by auto

lemma ds_equality: 
  shows "(ds [] pi)-{a,swapas pi a} = (ds [] ((a,swapas pi a)#pi))-{swapas pi a}"
  using ds_def by auto

lemma ds_7: 
  assumes "b \<noteq> swapas pi b" "a \<in> ds [] ((b,swapas pi b)#pi)"
  shows "a\<in>ds [] pi"
  using assms ds_def swapas_pi_in_atms a_ineq_swapas_pi swapas_rev_pi_a 
    ds_elem elem_ds swapa.simps swapas.simps(2)
  by metis

lemma ds_cancel_pi_front: 
  shows "ds (pi@pi1) (pi@pi2) = ds pi1 pi2"
  unfolding ds_def
  by (metis (lifting) Un_iff a_not_in_atms swapas_append swapas_inv)

lemma ds_rev_pi_pi: 
  shows "ds ((rev pi1)@pi1) pi2 = ds [] pi2"
  unfolding ds_def
  using a_not_in_atms swapas_append by auto 

lemma ds_rev: 
  shows "ds [] ((rev pi1)@pi2) = ds pi1 pi2"
  using ds_cancel_pi_front ds_rev_pi_pi by blast

lemma ds_acabbc: 
  assumes "a\<noteq>b" "b\<noteq>c" "c\<noteq>a"
  shows "ds [(a, b), (b, c)] [(a, c)] = {a, b}"
  using assms ds_def by auto

lemma ds_baab: 
  assumes "a\<noteq>b"
  shows "ds [(b,a)] [(a, b)] = {}"
  using assms ds_def by auto

lemma ds_baab_id: 
  assumes "a\<noteq>b"
  shows "ds ([(b,a)]@[(a, b)]) [] = {}"
  using assms ds_def ds_rev ds_baab by simp

lemma ds_abab: 
  shows "ds [] [(a, b), (a, b)] = {}"
  using ds_def by auto

lemma ds_comm:
  shows "ds (pi @ [(a,b)]) ([(swapas pi a, swapas pi b)] @ pi) = {}"
  using swapas_comm ds_def by simp

lemma ds_rev_pi_id:
  shows "ds (rev pi @ pi) [] = {}"
  using ds_rev_pi_pi[of pi \<open>[]\<close>] elem_ds
    ds_sym[of \<open>(rev pi @ pi)\<close> \<open>[]\<close>] by fastforce

lemma ds_pi_rev_id:
  shows "ds (pi @ rev pi) [] = {}"
  using ds_rev_pi_id[of \<open>rev pi\<close>] rev_rev_ident[of pi]
  by simp

lemma ds_swapas_eq:
  assumes "ds pi1 pi2 = {}"
  shows "swapas pi1 a = swapas pi2 a"
  using assms
  by (metis ds_elem_cp ds_pi_rev_id ds_rev ds_sym emptyE swapas_append) 

text \<open>Disagreement sets as lists.\<close> 

fun flatten :: "(string \<times> string)list \<Rightarrow> string list" where
"flatten []     = []" |
"flatten (x#xs) = (fst x)#(snd x)#(flatten xs)"

definition ds_list :: "(string \<times> string)list \<Rightarrow> (string \<times> string)list \<Rightarrow> string list" where
  ds_list_def: "ds_list pi1 pi2 \<equiv> remdups ([x. x <- (flatten (pi1@pi2)), x\<in>ds pi1 pi2])"

lemma set_flatten_eq_atms: 
  shows "set (flatten pi) = atms pi"
  by (induct pi) auto

lemma ds_list_equ_ds: 
  "set (ds_list pi1 pi2) = ds pi1 pi2"
  using ds_list_def ds_def set_flatten_eq_atms by auto


(*<*)
end
(*>*)