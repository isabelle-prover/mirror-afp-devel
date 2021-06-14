theory Env_list
  imports Env "HOL-Library.Library"
begin


subsection \<open>Generic lemmas\<close>

lemma map_of_filter:
  "x \<noteq> y \<Longrightarrow> map_of (filter (\<lambda>z. fst z \<noteq> y) zs) x = map_of zs x"
  by (induction zs) auto


subsection \<open>List-based implementation of environment\<close>

context
begin

qualified type_synonym ('key, 'val) t = "('key \<times> 'val) list"

qualified definition empty :: "('key, 'val) t" where
  "empty \<equiv> []"

qualified definition get :: "('key, 'val) t \<Rightarrow> 'key \<Rightarrow> 'val option" where
  "get \<equiv> map_of"

qualified definition add :: "('key, 'val) t \<Rightarrow> 'key \<Rightarrow> 'val \<Rightarrow> ('key, 'val) t" where
  "add e k v \<equiv> AList.update k v e"

term filter

qualified fun to_list :: "('key, 'val) t \<Rightarrow> ('key \<times> 'val) list" where
  "to_list [] = []" |
  "to_list (x # xs) = x # to_list (filter (\<lambda>(k, v). k \<noteq> fst x) xs)"

lemma get_empty: "get empty x = None"
  unfolding get_def empty_def
  by simp

lemma get_add_eq: "get (add e x v) x = Some v"
  unfolding get_def add_def
  by (simp add: update_Some_unfold)

lemma get_add_neq: "x \<noteq> y \<Longrightarrow> get (add e x v) y = get e y"
  unfolding get_def add_def
  by (simp add: update_conv')

lemma to_list_correct: "map_of (to_list e) = get e"
  unfolding get_def
proof (induction e rule: to_list.induct)
  case 1
  then show ?case by simp
next
  case (2 x xs)
  show ?case
  proof (rule ext)
    fix k'
    show "map_of (to_list (x # xs)) k' = map_of (x # xs) k'"
      using "2.IH" map_of_filter
      by (auto simp add: case_prod_beta')
  qed
qed

lemma set_to_list: "set (to_list e) \<subseteq> set e"
  by (induction e rule: to_list.induct) auto

lemma to_list_distinct: "distinct (map fst (to_list e))"
proof (induction e rule: to_list.induct)
  case 1
  then show ?case by simp
next
  case (2 x xs)
  then show ?case
    using set_to_list
    by fastforce
qed

end


global_interpretation env_list:
  env Env_list.empty Env_list.get Env_list.add Env_list.to_list
  defines
    singleton = env_list.singleton and
    add_list = env_list.add_list and
    from_list = env_list.from_list
  apply (unfold_locales)
  by (simp_all add: get_empty get_add_eq get_add_neq to_list_correct to_list_distinct)


export_code Env_list.empty Env_list.get Env_list.add Env_list.to_list singleton add_list from_list
  in SML module_name Env

end