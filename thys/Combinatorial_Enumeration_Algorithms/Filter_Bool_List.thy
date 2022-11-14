theory Filter_Bool_List
  imports
  "HOL.List"
begin

text "A simple algorithm to filter a list by a boolean list. A different approach would be to filter
by a set of indices, but this approach is faster, because lookups are slow in ML."

fun filter_bool_list :: "bool list \<Rightarrow> 'a list \<Rightarrow> 'a list" where
  "filter_bool_list [] _ = []"
| "filter_bool_list _ [] = []"
| "filter_bool_list (b#bs) (x#xs) =
    (if b then x#(filter_bool_list bs xs) else (filter_bool_list bs xs))"

text"The following could be an alternative definition, but the version above provides a nice computational induction rule."
lemma "filter_bool_list bs xs = map snd (filter fst (zip bs xs))"
  by(induct bs xs rule: filter_bool_list.induct) auto

lemma filter_bool_list_in:
  "n < length xs \<Longrightarrow> n < length bs \<Longrightarrow> bs!n \<Longrightarrow> xs!n \<in> set (filter_bool_list bs xs)"
proof (induct bs xs arbitrary: n rule: filter_bool_list.induct)
  case (3 b bs x xs)
  then show ?case by(cases n) auto
qed auto

lemma filter_bool_list_not_elem: "x \<notin> set xs \<Longrightarrow> x \<notin> set (filter_bool_list bs xs)"
  by(induct bs xs rule: filter_bool_list.induct) auto

lemma filter_bool_list_elem: "x \<in> set (filter_bool_list bs xs) \<Longrightarrow> x \<in> set xs"
  using filter_bool_list_not_elem by fast

lemma filter_bool_list_not_in:
  "distinct xs \<Longrightarrow> n < length xs\<Longrightarrow> n < length bs \<Longrightarrow> bs!n = False
    \<Longrightarrow> xs!n \<notin> set (filter_bool_list bs xs)"
proof (induct bs xs arbitrary: n rule: filter_bool_list.induct)
  case (3 b bs x xs)
  then show ?case proof(induct n)
    case 0
    then show ?case using filter_bool_list_not_elem
      by force
  qed auto
qed auto

lemma filter_bool_list_elem_nth:  "ys \<in> set (filter_bool_list bs xs)
  \<Longrightarrow> \<exists>n. ys = xs ! n \<and> bs ! n \<and> n < length bs \<and> n < length xs"
proof(induct bs xs arbitrary: ys rule: filter_bool_list.induct)
  case (1 xs)
  then show ?case by simp
next
  case (2 b bs)
  then show ?case by simp
next
  case (3 b bs y ys)
  then show ?case 
    by(cases b) (force)+
qed 

text"May be a useful conversion, since the algorithm could also be implemented with a list of indices."
lemma filter_bool_list_set_nth:
  "set (filter_bool_list bs xs) = {xs ! n |n. bs ! n \<and> n < length bs \<and> n < length xs}"
  by (auto simp: filter_bool_list_in filter_bool_list_elem_nth)

lemma filter_bool_list_exist_length: "A \<subseteq> set xs
  \<Longrightarrow> \<exists>bs. length bs = length xs \<and> A = set (filter_bool_list bs xs)"
proof(induct xs arbitrary: A)
  case Nil
  then show ?case
    by auto
next
  case (Cons x xs)
  from Cons have "A - {x} \<subseteq> set xs"
    by auto
  from this Cons have 1: "\<exists>bs. length bs = length xs \<and> A - {x} = set (filter_bool_list bs xs)"
    by simp

  then have "\<exists>bs. length bs = length (x # xs) \<and> A = set (filter_bool_list bs (x # xs))"
    by (metis Diff_empty Diff_insert0 insert_Diff_single insert_absorb list.simps(15) list.size(4) filter_bool_list.simps(3))
  
  then show ?case .
qed

lemma filter_bool_list_card:
  "\<lbrakk>distinct xs; length xs = length bs\<rbrakk> \<Longrightarrow> card (set (filter_bool_list bs xs)) = count_list bs True" 
  by(induct bs xs rule: filter_bool_list.induct) (auto simp: filter_bool_list_not_elem)

lemma filter_bool_list_exist_length_card_True: "\<lbrakk>distinct xs; A \<subseteq> set xs; n = card A\<rbrakk>
   \<Longrightarrow> \<exists>bs. length bs = length xs \<and> count_list bs True = card A \<and> A = set (filter_bool_list bs xs)"
  by (metis filter_bool_list_card filter_bool_list_exist_length)

lemma filter_bool_list_distinct: "distinct xs \<Longrightarrow> distinct (filter_bool_list bs xs)"
  by(induct bs xs rule: filter_bool_list.induct) (auto simp: filter_bool_list_not_elem) 

lemma filter_bool_list_inj_aux:
  assumes "length bs1 = length xs"
  and "length xs = length bs2"
  and "distinct xs"
shows "filter_bool_list bs1 xs = filter_bool_list bs2 xs \<Longrightarrow> bs1 = bs2"
using assms proof(induct rule: list_induct3)
  case Nil
  then show ?case by simp
next
  case (Cons b1 bs1 x xs b2 bs2)
  then show ?case
    by(cases b1; cases b2, auto) (metis list.set_intros(1) filter_bool_list_not_elem)+
qed

lemma filter_bool_list_inj:
  "distinct xs \<Longrightarrow> inj_on (\<lambda>bs. filter_bool_list bs xs) {bs. length bs = length xs}"
  unfolding inj_on_def using filter_bool_list_inj_aux by fastforce

end
