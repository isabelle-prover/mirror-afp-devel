section \<open>Auxiliary Algorithm for Testing Whether "set xs" is a Singleton Set\<close>
theory Singleton_List
  imports Main
begin

definition "singleton x = [x]" 

fun is_singleton_list :: "'a list \<Rightarrow> bool" where
  "is_singleton_list [x] = True" 
| "is_singleton_list (x # y # xs) = (x = y \<and> is_singleton_list (x # xs))"
| "is_singleton_list _ = False"


lemma is_singleton_list: "is_singleton_list xs \<longleftrightarrow> set (singleton (hd xs)) = set xs"
  by (induct xs rule: is_singleton_list.induct, auto simp: singleton_def)

lemma is_singleton_list2: "is_singleton_list xs \<longleftrightarrow> (\<exists> x. set xs = {x})"  
  by (induct xs rule: is_singleton_list.induct, auto)

end
