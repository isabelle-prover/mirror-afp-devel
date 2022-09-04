theory Imp_List_Sum
imports "Separation_Logic_Imperative_HOL.Imp_List_Spec"
begin

text "A general sum operation can be defined for list iterators
over elements of a monoid"

locale imp_list_iterate_sum = imp_list_iterate is_list is_it
  for is_list :: "('a ::{monoid_add}) list \<Rightarrow> 'b \<Rightarrow> assn"
  and is_it :: "'a list \<Rightarrow> 'b \<Rightarrow> 'a list \<Rightarrow> 'it \<Rightarrow> assn"
begin
subsubsection \<open>List-Sum\<close>

partial_function (heap) it_sum' :: "'it \<Rightarrow> 'a \<Rightarrow> 'a Heap"
  where [code]:
  "it_sum' it s = do {
    b \<leftarrow> it_has_next it;
    if b then do {
      (x,it') \<leftarrow> it_next it;
      it_sum' it' (s+x)
    } else return s
  }"

lemma it_sum'_rule[sep_heap_rules]: 
  "<is_it l p l' it> 
    it_sum' it s 
  <\<lambda>r. is_list l p * \<up>(r = s + sum_list l')>\<^sub>t"
proof (induct l' arbitrary: it s)
  case Nil thus ?case
    apply (subst it_sum'.simps)
    apply (sep_auto intro: quit_iteration ent_true_drop(1))
    done
next
  case (Cons x l')
  show ?case
    apply (subst it_sum'.simps)
    apply (sep_auto heap: Cons.hyps simp add: add.assoc)
    done
qed

definition "it_sum p \<equiv> do { 
  it \<leftarrow> it_init p;
  it_sum' it 0}"

lemma it_sum_rule[sep_heap_rules]: 
  "<is_list l p> it_sum p <\<lambda>r. is_list l p * \<up>(r=sum_list l)>\<^sub>t"
  unfolding it_sum_def
  by sep_auto

end

end