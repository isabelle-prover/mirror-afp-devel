theory Partially_Filled_Array_Iter
imports
  Partially_Filled_Array
  "Separation_Logic_Imperative_HOL.Imp_List_Spec"
begin


subsubsection \<open>Iterator\<close>

type_synonym 'a pfa_it = "'a pfarray \<times> nat"
definition "pfa_is_it c ls lsi ls2
  \<equiv> (\<lambda>(lsi',i). is_pfa c ls lsi * \<up>(ls2 = drop i ls \<and> i \<le> length ls \<and> lsi' = lsi))"

definition pfa_it_init :: "'a pfarray \<Rightarrow> ('a pfa_it) Heap" 
  where "pfa_it_init l = return (l,0)"

fun pfa_it_next where 
  "pfa_it_next (p,i) = do {
    x \<leftarrow> pfa_get p i;
    return (x, (p,Suc i))
  }"

definition pfa_it_has_next :: "('a::heap) pfa_it \<Rightarrow> bool Heap" where
  "pfa_it_has_next it \<equiv> do {
    l \<leftarrow> pfa_length (fst it);
    return (snd it \<noteq> l)
}"

lemma pfa_iterate_impl: 
  "imp_list_iterate (is_pfa k) (pfa_is_it k) pfa_it_init pfa_it_has_next pfa_it_next"
  apply unfold_locales
  unfolding pfa_it_init_def pfa_is_it_def[abs_def] 
proof(goal_cases)
  case 1
  then show ?case
    by (simp add: is_pfa_prec)
next
  case (2 l p)
  then show ?case
    by sep_auto
next
  case (3 l' l p it)
  then show ?case
  apply (case_tac it, simp)
  apply (case_tac l', simp)
  apply sep_auto
    subgoal by (metis drop_all list.simps(3) not_le_imp_less)
  apply (sep_auto)
    apply (metis drop_eq_ConsD list.sel(3))
    subgoal by (meson Suc_leI \<open>\<And>list ba b aa a. \<lbrakk>it = ((a, b), ba); l' = drop ba l; aa # list = drop ba l; ba \<le> length l; p = (a, b)\<rbrakk> \<Longrightarrow> ba < length l\<close>)
    subgoal by (metis list.sel(1) nth_via_drop)
    subgoal using ent_refl_true by presburger
    done
next
  case (4 l p l' it)
  then show ?case
  unfolding pfa_it_has_next_def
  apply (case_tac it, simp)
  by (sep_auto)
next
  case (5 l p l' it)
  then show ?case
  apply (case_tac it, simp)
    by sep_auto
qed

interpretation pfa_iter: 
  imp_list_iterate "is_pfa k" "pfa_is_it k" pfa_it_init pfa_it_has_next pfa_it_next
  by (rule pfa_iterate_impl)


end