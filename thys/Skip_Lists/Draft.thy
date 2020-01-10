theory Draft
imports Skip_List
begin



locale abstract_sl' =
  fixes
    val :: "'a \<Rightarrow> 'b" and
    down :: "'a \<Rightarrow> 'a option" and
    right :: "'a \<Rightarrow> 'a option" and
    V :: "'a set"

locale abstract_sl = abstract_sl' +
  assumes f: "finite V"
begin


function acyclic where
  "acyclic visited a = (let visited' = visited \<union> {a} in (if visited' \<subseteq> V \<and> a \<notin> visited then
     (case down a of Some d \<Rightarrow> acyclic (visited \<union> {a}) d | None \<Rightarrow> True) else False))"
  by auto
termination
  by (relation "Wellfounded.measure (\<lambda>(visited, v). card V - card visited)")
    (use f in \<open>auto simp add: finite_subset intro!: psubset_card_mono diff_less_mono2\<close>)




locale abstract_sl = abstract_sl' +
  fixes wf_sl
  assumes ""


datatype ('a::linorder) slttt = SL 'a "nat option" "nat option"


term "map_of [(0, SL 1 (Some 1) (Some 3)), (1, SL 1 None (Some 2)), (2, SL 8 None (Some 4))]"

function lookup :: "'a::linorder \<Rightarrow> 'a list list \<Rightarrow> bool" where
  "lookup x [] = False" |
  "lookup x ((y#ys)#ls) = (if x = y then True else
                              (if y < x then lookup x (ys#(map (dropWhile (\<lambda>z. z \<le> y)) ls)) else
                               lookup x ls))" |
  "lookup x ([] # ls) = lookup x ls"
  by pat_completeness auto
termination
proof (relation "(\<lambda>(a,xs). length (concat xs)) <*mlex*> (\<lambda>(a,xs). length xs) <*mlex*> {}",
       goal_cases)
  case 1
  then show ?case by(intro wf_mlex wf_empty)
next
  case (2 a y ys ls)
  have "length (concat (map (dropWhile (\<lambda>z. z \<le> y)) ls)) \<le> (length (concat ls))"
    by (auto simp add: length_concat  length_dropWhile_le intro!: sum_list_mono)
  then show ?case by (intro mlex_less) auto
next
  case (3 x y ys ls)
  then show ?case by (intro mlex_less) auto
next
  case (4 x ls)
  then show ?case by (rule mlex_leq) (auto intro!: mlex_less)
qed

definition sl where "sl ls = (list_all distinct ls \<and> list_all sorted ls \<and> sorted_wrt subseq ls)"


lemma subseq_dropWhile: "subseq xs ys \<Longrightarrow> subseq (dropWhile P xs) ys"
  by (induction xs ys rule: list_emb.induct) (auto)

lemma subseq_dropWhile': "subseq xs ys \<Longrightarrow> subseq (dropWhile P xs) (dropWhile P ys)"
  by (induction xs ys rule: list_emb.induct) (use subseq_dropWhile in auto)

lemma sl_map_dropWhile: "sl ls \<Longrightarrow> sl (map (dropWhile P) ls)"
  by (induction ls) (use subseq_dropWhile' in \<open>auto simp add: sorted_dropWhile sl_def\<close>)

definition set_sl where "set_sl ls = \<Union> (set ` set ls)"

lemma set_sl_Cons:
  "set xs \<subseteq> set xs' \<Longrightarrow> set_sl ls \<subseteq> set_sl ls' \<Longrightarrow> set_sl (xs # ls) \<subseteq> set_sl (xs' # ls')"
  unfolding set_sl_def by (auto)

lemma subseq_subset: "subseq xs ys \<Longrightarrow> set xs \<subseteq> set ys"
  by (induction xs ys rule: list_emb.induct) (auto)

lemma subseq_sorted: "subseq xs ys \<Longrightarrow> sorted ys \<Longrightarrow> sorted xs"
  by (induction xs ys rule: list_emb.induct) (use subseq_subset in auto)

lemma subseq_distinct: "subseq xs ys \<Longrightarrow> distinct ys \<Longrightarrow> distinct xs"
   by (induction xs ys rule: list_emb.induct) (use subseq_subset in auto)

lemma set_dropWhile: "set (dropWhile P ls) \<subseteq> set ls"
  by (induction ls) auto

lemma "lookup x ls \<Longrightarrow> x \<in> set_sl ls"
  using set_dropWhile
  by (induction x ls rule: lookup.induct) (fastforce split: if_splits simp add: set_sl_def)+

lemma "subseq xs ys \<Longrightarrow> distinct ys \<Longrightarrow> distinct xs"
   by (induction xs ys rule: list_emb.induct) (use subseq_subset in auto)

lemma subseq_dropWhile_leq:
  assumes "sorted ys" "distinct ys" "subseq xs ys" "xs = x'#xs'"
  shows "subseq xs' (dropWhile (\<lambda>z. z \<le> x') ys)"
using assms proof (induction ys arbitrary: xs x' xs')
  case Nil
  then show ?case by simp
next
  case (Cons y ys xs x' xs')
  have ?case if "x' = y" "xs' \<noteq> []"
    using that Cons by (cases ys) (auto)
  moreover have ?case if "x' < y"
  proof -
    have "subseq xs' (y # ys)"
      using Cons subseq_Cons' by metis
    then show ?thesis
      using that Cons by (auto)
  qed
  ultimately show ?case using Cons by (cases "x' = y") (auto)
qed

lemma sorted_dropWhile_filter: "sorted ls \<Longrightarrow> dropWhile (\<lambda>x. x \<le> y) ls = filter (\<lambda>x. x > y) ls"
  by (induction ls) (auto simp add: less_le_trans)

lemma sl_dropWhile_filter: "sl ls \<Longrightarrow> map (dropWhile (\<lambda>x. x \<le> y)) ls = map (filter (\<lambda>x. x > y)) ls"
  by (auto simp add: sl_def list_all_iff intro!:  map_cong sorted_dropWhile_filter)

lemma "sl ls \<Longrightarrow> x \<in> set_sl ls \<Longrightarrow> lookup x ls"
(* TODO: clean up *)
proof (induction x ls rule: lookup.induct)
  case (1 x)
  then show ?case by  (fastforce split: if_splits simp add: set_sl_def)
next
  case (2 x y ys ls)
  consider (a) "x = y" | (b) "y < x" | (c) "x < y"
    by fastforce
  then show ?case
  proof (cases)
    case b
    have "sl (ys # map (dropWhile (\<lambda>z. z \<le> y)) ls)"
    proof (cases ls)
      case Nil
      then show ?thesis using 2 by (auto simp add: sl_def)
    next
      case (Cons l' ls')
      have I:"sl (map (dropWhile (\<lambda>z. z \<le> y)) ls)"
        using 2  by (auto intro!: sl_map_dropWhile) (simp add: sl_def)
      have "subseq ys (dropWhile (\<lambda>z. z \<le> y) l')"
        using 2 Cons by (auto simp add: sl_def intro!: subseq_dropWhile_leq)
      then show ?thesis
        using Cons I by (auto simp add: sl_def list_all_iff subseq_sorted subseq_distinct)
    qed
    moreover have "set_sl (ys # map (dropWhile (\<lambda>z. z \<le> y)) ls) = set_sl (ys # map (filter (\<lambda>z. y < z)) ls)"
      using 2  by (subst sl_dropWhile_filter) (auto simp add: sl_def)
    ultimately show ?thesis
      using b 2 by (auto simp add: set_sl_def intro!: 2)
  next
    case c
    then have "x \<in> set_sl ls"
      using 2 subseq_subset by (cases ls) (auto simp add: set_sl_def sl_def)
    then have "lookup x ls"
      using c 2 by (auto simp add: set_sl_def sl_def intro!: 2)
    then show ?thesis
      using c 2 by (auto)
  qed (auto)
next
  case (3 x ls)
  then show ?case by (fastforce split: if_splits simp add: set_sl_def sl_def)
qed

fun sl_insert' where
  "sl_insert' x (Suc n) (l#ls) = insort x l # sl_insert' x n ls" |
  "sl_insert' x 0 (l#ls) = insort x l # ls" |
  "sl_insert' x (Suc n) [] = [x] # sl_insert' x n []" |
  "sl_insert' x 0 [] = [[x]]"

definition sl_insert where
  "sl_insert x n ls = (if lookup x ls then ls else rev (sl_insert' x n (rev ls)))"

lemma sl_rev:
  "sl (rev ls) = (list_all distinct ls \<and> list_all sorted ls \<and> sorted_wrt (\<lambda>x y. subseq y x) ls)"
  by (auto simp add: sl_def sorted_wrt_rev)

lemma subseq_sorted_wrt: "sorted_wrt P xs \<Longrightarrow> subseq ys xs \<Longrightarrow> sorted_wrt P ys"
proof (induction ys)
  case (Cons y ys)
  then have "P y y'" if "y' \<in> set ys" for y'
    using that subseq_subset by (induction xs) (auto split: if_splits)
  then show ?case
    using Cons by (auto simp add: subseq_Cons')
qed (auto)

lemma sl_subseq_sl: "sl ls \<Longrightarrow> subseq ls' ls \<Longrightarrow> sl ls'"
  using subseq_subset subseq_sorted_wrt by (fastforce simp add: sl_def list_all_iff)

lemma subseq_rev: "subseq xs ys \<Longrightarrow> subseq (rev xs) (rev ys)"
  by (induction xs ys rule: list_emb.induct) (auto)

lemma subseq_insort_key: "subseq xs (insort_key P x xs)"
  by (induction xs) (auto)

lemma 1111: assumes "l \<in> set (sl_insert' x n ls)"
  shows "(\<exists>l' \<in> set ls. l = insort x l') \<or> l = [x] \<or> l \<in> set ls"
  using assms by (induction x n ls rule: sl_insert'.induct) (auto)

lemma 28: "subseq xs ys \<Longrightarrow> sorted ys \<Longrightarrow> subseq (insort x xs) (insort x ys)"
proof (induction xs ys rule: list_emb.induct)
  case (list_emb_Cons xs ys y)
  then have "\<forall>x\<in>set xs. y \<le> x"
    using subseq_subset by (auto)
  then have "insort x xs = x # xs" if "x \<le> y"
    using that by (subst insort_is_Cons) (auto simp add: insort_is_Cons)
  then show ?case
    using list_emb_Cons by (auto)
qed (auto simp add: set_insort_key subseq_singleton_left)



lemma
  assumes "sl ls"
  shows "sl (sl_insert x n ls)"
proof -
  let ?sws = "sorted_wrt (\<lambda>x y. subseq y x)"
  let ?sort = "(\<lambda>ls. list_all sorted ls \<and> sorted_wrt (\<lambda>x y. subseq y x) ls)"
  have "?sort (sl_insert' x n xs)" if "?sort xs" for xs
    using that proof (induction x n xs rule: sl_insert'.induct)
    case (1 x n y ys)
    have "subseq l' (insort x y)" if "l' \<in> set (sl_insert' x n ys) " for l'
        using 1 that apply - apply(drule 1111[of l']) apply(auto)
          defer
          apply(subst subseq_singleton_left)
          apply (simp add: set_insort_key)
         apply(subgoal_tac "subseq l' y")
        using subseq_insort_key[of y]
        using subseq_order.order_trans apply blast
        using 1 apply(blast)
        apply(rule 28)
        by (auto)
    then show ?case
      using 1 sorted_insort by (auto)
  next
    case (2 x l ls)
    then have "subseq l' l" if "l' \<in> set ls" for l'
      using that by (auto)
    moreover have "subseq l (insort x l)"
      by (simp add: subseq_insort_key)
    ultimately have "subseq l' (insort x l)" if "l' \<in> set ls" for l'
      using that by fastforce
    then show ?case
      using 2 sorted_insort by (auto)
  next
    case (3 x n)
    then show ?case
      by (cases n) (auto)
  qed (auto)
  then show ?thesis
    using assms sorry
qed

notepad
begin
  have 1: "a + b \<le> c" (is "?x + ?y \<le> ?z") for a b c::nat
    sorry
  let ?y = 1

end
