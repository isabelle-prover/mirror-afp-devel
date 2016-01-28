(*  
    Author:      René Thiemann 
                 Akihisa Yamada
    License:     BSD
*)
subsection \<open>Missing List\<close>

text \<open>The provides some standard algorithms and lemmas on lists.\<close>
theory Missing_List
imports 
  "../Matrix/Utility"
begin

fun concat_lists :: "'a list list \<Rightarrow> 'a list list" where
  "concat_lists [] = [[]]"
| "concat_lists (as # xs) = concat (map (\<lambda>vec. map (\<lambda>a. a # vec) as) (concat_lists xs))"

lemma concat_lists_listset: "set (concat_lists xs) = listset (map set xs)" 
  by (induct xs, auto simp: set_Cons_def)

lemma listsum_concat: 
  shows "listsum (concat ls) = listsum (map listsum ls)"
  proof (induct ls, auto) qed


(* TODO: move to src/HOL/List *)
lemma listset: "listset xs = { ys. length ys = length xs \<and> (\<forall> i < length xs. ys ! i \<in> xs ! i)}"
proof (induct xs)
  case (Cons x xs)
  let ?n = "length xs" 
  from Cons 
  have "?case = (set_Cons x {ys. length ys = ?n \<and> (\<forall>i < ?n. ys ! i \<in> xs ! i)} =
    {ys. length ys = Suc ?n \<and> ys ! 0 \<in> x \<and> (\<forall>i < ?n. ys ! Suc i \<in> xs ! i)})" 
    (is "_ = (?L = ?R)")
    by (auto simp: all_Suc_conv)
  also have "?L = ?R"
    by (auto simp: set_Cons_def, case_tac xa, auto)
  finally show ?case by simp
qed auto

lemma set_concat_lists[simp]: "set (concat_lists xs) = {as. length as = length xs \<and> (\<forall>i<length xs. as ! i \<in> set (xs ! i))}"
  unfolding concat_lists_listset listset by simp

declare concat_lists.simps[simp del]

fun find_map_filter :: "('a \<Rightarrow> 'b) \<Rightarrow> ('b \<Rightarrow> bool) \<Rightarrow> 'a list \<Rightarrow> 'b option" where
  "find_map_filter f p [] = None"
| "find_map_filter f p (a # as) = (let b = f a in if p b then Some b else find_map_filter f p as)"

lemma find_map_filter_Some: "find_map_filter f p as = Some b \<Longrightarrow> p b \<and> b \<in> f ` set as"
  by (induct f p as rule: find_map_filter.induct, auto simp: Let_def split: if_splits)

lemma find_map_filter_None: "find_map_filter f p as = None \<Longrightarrow> \<forall> b \<in> f ` set as. \<not> p b"
  by (induct f p as rule: find_map_filter.induct, auto simp: Let_def split: if_splits)

lemma remdups_adj_sorted_distinct[simp]: "sorted xs \<Longrightarrow> distinct (remdups_adj xs)"
proof (induct xs rule: sorted.induct)
  case (Cons xs x) note oCons = this
  show ?case 
  proof (cases xs)
    case (Cons y ys)
    with oCons have "x \<le> y" by auto
    show ?thesis
    proof (cases "x = y")
      case True
      with oCons Cons show ?thesis by auto
    next
      case False
      with `x \<le> y` have "x < y" by auto      
      with oCons Cons have id: "remdups_adj (x # xs) = x # remdups_adj xs" by auto
      {
        assume "x \<in> set xs" 
        with `sorted xs` have "y \<le> x" unfolding Cons by (cases, auto)
        with `x < y` have False by auto
      }
      thus ?thesis using oCons(3) unfolding id by auto
    qed
  qed simp
qed simp

end