(*  Author:      Christian Sternagel
    Maintainer:  Christian Sternagel
*)

theory Efficient_Sort
imports "~~/src/HOL/Library/Multiset"
begin

text {*
A high-level overview of this formalization as well as some experimental data is
to be found in \cite{Sternagel2012}.
*}

section {* Chaining Lists by Predicates *}

text {*
Make sure that some binary predicate @{text P} is satisfied between
every two consecutive elements of a list. We call such a list a
\emph{chain} in the following.
*}
inductive
  linked :: "('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> 'a list \<Rightarrow> bool"
  for P::"'a \<Rightarrow> 'a \<Rightarrow> bool"
where
  Nil[iff]: "linked P []"
| singleton[iff]: "linked P [x]"
| many: "P x y \<Longrightarrow> linked P (y#ys) \<Longrightarrow> linked P (x#y#ys)"

declare eqTrueI[OF Nil, code] eqTrueI[OF singleton, code]

lemma linked_many_eq[simp, code]:
  "linked P (x#y#zs) \<longleftrightarrow> P x y \<and> linked P (y#zs)"
  by (blast intro: linked.many elim: linked.cases)

text {* Take the longest prefix of a list that forms a chain. *}
fun take_chain :: "'a \<Rightarrow> ('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> 'a list \<Rightarrow> 'a list" where
  "take_chain a P [] = []"
| "take_chain a P (x#xs) = (if P a x
    then x # take_chain x P xs
    else [])"

text {* Drop the longest prefix of a list that forms a chain. *}
fun drop_chain :: "'a \<Rightarrow> ('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> 'a list \<Rightarrow> 'a list" where
  "drop_chain a P [] = []"
| "drop_chain a P (x#xs) = (if P a x
    then drop_chain x P xs
    else x#xs)"

lemma take_chain_drop_chain_id[simp]:
  "take_chain a P xs @ drop_chain a P xs = xs"
  by (induct xs arbitrary: a) simp_all

lemma linked_take_chain:
  "linked P (x # take_chain x P xs)"
  by (induct xs arbitrary: x) simp_all

lemma linked_rev_take_chain_append:
  "linked P (x#ys) \<Longrightarrow> linked P (rev (take_chain x (\<lambda>x y. P y x) xs) @ x#ys)"
  by (induct xs arbitrary: x ys) simp_all

lemma linked_rev_take_chain:
  "linked P (rev (take_chain x (\<lambda>x y. P y x) xs) @ [x])"
  using linked_rev_take_chain_append[of P x "[]" xs] by simp

lemma linked_append:
  "linked P (xs@ys) \<longleftrightarrow> linked P xs \<and> linked P ys
    \<and> (if xs \<noteq> [] \<and> ys \<noteq> [] then P (last xs) (hd ys) else True)"
    (is "?lhs = ?rhs")
proof
  assume "?lhs" thus "?rhs"
  proof (induct xs)
    case (Cons x xs) thus ?case by (cases xs, simp_all) (cases ys, auto)
  qed simp
next
  assume "?rhs" thus "?lhs"
  proof (induct xs)
    case (Cons x xs) thus ?case by (cases ys, auto) (cases xs, auto)
  qed simp
qed

lemma length_drop_chain[termination_simp]:
  "length (drop_chain b P xs) \<le> length xs" (is "?P b xs")
proof (induct xs arbitrary: b rule: length_induct)
  fix xs::"'a list" and b
  assume IH: "\<forall>ys. length ys < length xs \<longrightarrow> (\<forall>x. ?P x ys)"
  show "?P b xs"
  proof (cases xs)
    case (Cons y ys) with IH[rule_format, of ys y] show ?thesis by simp
  qed simp
qed

lemma take_chain_map[simp]:
  "take_chain (f x) P (map f xs) = map f (take_chain x (\<lambda>x y. P (f x) (f y)) xs)"
  by (induct xs arbitrary: x) simp_all


subsection {* Sorted is a Special Case of Linked *}

lemma (in linorder) linked_le_sorted_conv[simp]:
  "linked (op \<le>) xs = sorted xs"
proof
  assume "sorted xs" thus "linked (op \<le>) xs"
  proof (induct xs rule: sorted.induct)
    case (Cons xs x) thus ?case by (cases xs) simp_all
  qed simp
qed (induct xs rule: linked.induct, simp_all)

lemma (in linorder) linked_less_imp_sorted:
  "linked (op <) xs \<Longrightarrow> sorted xs"
  by (induct xs rule: linked.induct) simp_all

abbreviation (in linorder) (input) lt :: "('b \<Rightarrow> 'a) \<Rightarrow> 'b \<Rightarrow> 'b \<Rightarrow> bool" where
  "lt key x y \<equiv> key x < key y"

abbreviation (in linorder) (input) le :: "('b \<Rightarrow> 'a) \<Rightarrow> 'b \<Rightarrow> 'b \<Rightarrow> bool" where
  "le key x y \<equiv> key x \<le> key y"

abbreviation (in linorder) (input) gt :: "('b \<Rightarrow> 'a) \<Rightarrow> 'b \<Rightarrow> 'b \<Rightarrow> bool" where
  "gt key x y \<equiv> key x > key y"

abbreviation (in linorder) (input) ge :: "('b \<Rightarrow> 'a) \<Rightarrow> 'b \<Rightarrow> 'b \<Rightarrow> bool" where
  "ge key x y \<equiv> key x \<ge> key y"

lemma (in linorder) sorted_take_chain_le[simp]:
  "sorted (key x # map key (take_chain x (le key) xs))"
  using linked_take_chain[of "op \<le>", of "key x" "map key xs"] by simp

lemma (in linorder) sorted_rev_take_chain_gt_append:
  assumes "linked (op <) (key x # map key ys)"
  shows "sorted (map key (rev (take_chain x (gt key) xs)) @ key x # map key ys)"
  using linked_less_imp_sorted[OF linked_rev_take_chain_append[OF assms, of "map key xs"]]
    by (simp add: rev_map)

lemma mset_take_chain_drop_chain[simp]:
  "mset (take_chain x P xs) + mset (drop_chain x P xs) = mset xs"
  by (induct xs arbitrary: x) (simp_all add: ac_simps)

lemma mset_drop_chain_take_chain[simp]:
  "mset (drop_chain x P xs) + mset (take_chain x P xs) = mset xs"
  by (induct xs arbitrary: x) (simp_all add: ac_simps)


section {* GHC Version of Mergesort *}

text {*
In the following we show that the mergesort implementation
used in GHC (see @{url "http://haskell.org/ghc/docs/7.0-latest/html/libraries/base-4.3.1.0/src/Data-List.html#sort"})
is a correct and stable sorting algorithm. Furthermore, experimental
data suggests that generated code for this implementation is much more
efficient than for the implementation provided by @{theory Multiset}.
*}
context linorder
begin

text {*
Split a list into chunks of ascending and descending parts, where
descending parts are reversed. Hence, the result is a list of
sorted lists.
*}
fun sequences :: "('b \<Rightarrow> 'a) \<Rightarrow> 'b list \<Rightarrow> 'b list list"
  and asc :: "('b \<Rightarrow> 'a) \<Rightarrow> 'b \<Rightarrow> ('b list \<Rightarrow> 'b list) \<Rightarrow> 'b list \<Rightarrow> 'b list list"
  and desc :: "('b \<Rightarrow> 'a) \<Rightarrow> 'b \<Rightarrow> 'b list \<Rightarrow> 'b list \<Rightarrow> 'b list list"
where
  "sequences key (a#b#xs) =
    (if key a > key b then desc key b [a] xs else asc key b (op # a) xs)"
| "sequences key xs = [xs]"
| "asc key a f (b#bs) = (if \<not> key a > key b
    then asc key b (f \<circ> op # a) bs
    else f [a] # sequences key (b#bs))"
| "asc key a f bs = f [a] # sequences key bs"
| "desc key a as (b#bs) = (if key a > key b
    then desc key b (a#as) bs
    else (a#as) # sequences key (b#bs))"
| "desc key a as bs = (a#as) # sequences key bs"

fun merge :: "('b \<Rightarrow> 'a) \<Rightarrow> 'b list \<Rightarrow> 'b list \<Rightarrow> 'b list" where
  "merge key (a#as) (b#bs) = (if key a > key b
    then b # merge key (a#as) bs
    else a # merge key as (b#bs))"
| "merge key [] bs = bs"
| "merge key as [] = as"

fun merge_pairs :: "('b \<Rightarrow> 'a) \<Rightarrow> 'b list list \<Rightarrow> 'b list list" where
  "merge_pairs key (a#b#xs) = merge key a b # merge_pairs key xs"
| "merge_pairs key xs = xs"

lemma merge_Nil2[simp]: "merge key as [] = as" by (cases as) simp_all

lemma length_merge[simp]:
  "length (merge key xs ys) = length xs + length ys"
  by (induct xs ys rule: merge.induct) simp_all

lemma merge_pairs_length[termination_simp]:
  "length (merge_pairs key xs) \<le> length xs"
  by (induct xs rule: merge_pairs.induct) simp_all

fun merge_all :: "('b \<Rightarrow> 'a) \<Rightarrow> 'b list list \<Rightarrow> 'b list" where
  "merge_all key [] = []"
| "merge_all key [x] = x"
| "merge_all key xs = merge_all key (merge_pairs key xs)"

lemma mset_merge[simp]:
  "mset (merge key xs ys) = mset xs + mset ys"
  by (induct xs ys rule: merge.induct) (simp_all add: ac_simps)

lemma set_merge[simp]:
  "set (merge key xs ys) = set xs \<union> set ys"
  unfolding set_mset_mset[symmetric] by simp

lemma mset_concat_merge_pairs[simp]:
  "mset (concat (merge_pairs key xs)) = mset (concat xs)"
  by (induct xs rule: merge_pairs.induct) (auto simp: ac_simps)

lemma set_concat_merge_pairs[simp]:
  "set (concat (merge_pairs key xs)) = set (concat xs)"
  unfolding set_mset_mset[symmetric] by simp

lemma mset_merge_all[simp]:
  "mset (merge_all key xs) = mset (concat xs)"
  by (induct xs rule: merge_all.induct) (simp_all add: ac_simps)

lemma set_merge_all[simp]:
  "set (merge_all key xs) = set (concat xs)"
  unfolding set_mset_mset[symmetric] by simp

lemma sorted_merge[simp]:
  assumes "sorted (map key xs)" and "sorted (map key ys)"
  shows "sorted (map key (merge key xs ys))"
  using assms by (induct xs ys rule: merge.induct) (auto simp: sorted_Cons)

lemma sorted_merge_pairs[simp]:
  assumes "\<forall>x\<in>set xs. sorted (map key x)"
  shows "\<forall>x\<in>set (merge_pairs key xs). sorted (map key x)"
  using assms by (induct xs rule: merge_pairs.induct) simp_all

lemma sorted_merge_all:
  assumes "\<forall>x\<in>set xs. sorted (map key x)"
  shows "sorted (map key (merge_all key xs))"
  using assms by (induct xs rule: merge_all.induct) simp_all

lemma desc_take_chain_drop_chain_conv[simp]:
  "desc key a bs xs
    = (rev (take_chain a (gt key) xs) @ a # bs) # sequences key (drop_chain a (gt key) xs)"
proof (induct xs arbitrary: a bs)
  case (Cons x xs) thus ?case by (cases "key a < key x") simp_all
qed simp

lemma asc_take_chain_drop_chain_conv_append:
  assumes "\<And>xs ys. f (xs@ys) = f xs @ ys"
  shows "asc key a (f \<circ> op @ as) xs
    = (f as @ a # take_chain a (le key) xs) # sequences key (drop_chain a (le key) xs)"
using assms
proof (induct xs arbitrary: as a)
  case (Cons x xs)
  show ?case
  proof (cases "le key a x")
    case False with Cons show ?thesis by auto
  next
    case True
    with Cons(1)[of "x" "as@[a]"] and Cons(2)
      show ?thesis by (simp add: o_def)
  qed
qed simp

lemma asc_take_chain_drop_chain_conv[simp]:
  "asc key b (op # a) xs
    = (a # b # take_chain b (le key) xs) # sequences key (drop_chain b (le key) xs)"
proof -
  let ?f = "op # a"
  have "\<And>xs ys. (op # a) (xs@ys) = (op # a) xs @ ys" by simp
  from asc_take_chain_drop_chain_conv_append[of ?f key b "[]" xs, OF this]
    show ?thesis by (simp add: o_def)
qed

lemma sequences_induct[case_names Nil singleton many]:
  assumes "\<And>key. P key []" and "\<And>key x. P key [x]"
    and "\<And>key a b xs.
    (le key a b \<Longrightarrow> P key (drop_chain b (le key) xs))
    \<Longrightarrow> (\<not> le key a b \<Longrightarrow> P key (drop_chain b (gt key) xs))
    \<Longrightarrow> P key (a#b#xs)"
  shows "P key xs"
  using assms by (induction_schema) (pat_completeness, lexicographic_order)

lemma sorted_sequences:
  "\<forall>x\<in>set (sequences key xs). sorted (map key x)"
proof (induct key xs rule: sequences_induct)
  case (many key a b xs)
  thus ?case using sorted_rev_take_chain_gt_append[of key b "[a]" xs]
    by (cases "le key a b") auto
qed simp_all

lemma mset_sequences[simp]:
  "mset (concat (sequences key xs)) = mset xs"
  by (induct key xs rule: sequences_induct) (simp_all add: ac_simps)

lemma filter_by_key_drop_chain_gt[simp]:
  assumes "key b \<le> key a"
  shows "[y\<leftarrow>drop_chain b (gt key) xs. key a = key y] = [y\<leftarrow>xs. key a = key y]"
  using assms by (induct xs arbitrary: b) auto

lemma filter_by_key_take_chain_gt[simp]:
  assumes "key b \<le> key a"
  shows "[y\<leftarrow>take_chain b (gt key) xs. key a = key y] = []"
  using assms by (induct xs arbitrary: b) auto

lemma filter_take_chain_drop_chain[simp]:
  "filter P (take_chain x Q xs) @ filter P (drop_chain x Q xs) = filter P xs"
  by (simp add: filter_append[symmetric])

lemma filter_by_key_rev_take_chain_gt_conv[simp]:
  "[y\<leftarrow>rev (take_chain b (gt key) xs). key x = key y]
    = [y\<leftarrow>take_chain b (gt key) xs. key x = key y]"
  by (induct xs arbitrary: b) auto

lemma filter_by_key_sequences[simp]:
  "[y\<leftarrow>concat (sequences key xs). key x = key y]
    = [y\<leftarrow>xs. key x = key y]" (is ?P)
  by (induct key xs rule: sequences_induct) auto

lemma merge_simp[simp]:
  assumes "sorted (map key xs)"
  shows "merge key xs (y#ys)
    = takeWhile (ge key y) xs @ y # merge key (dropWhile (ge key y) xs) ys"
  using assms by (induct xs arbitrary: y ys) (auto simp: sorted_Cons)

lemma sorted_map_dropWhile[simp]:
  assumes "sorted (map key xs)"
  shows "sorted (map key (dropWhile (ge key y) xs))"
  using sorted_dropWhile[OF assms] by (simp add: dropWhile_map o_def)

lemma sorted_merge_induct[consumes 1, case_names Nil IH]:
  assumes "sorted (map key xs)"
    and "\<And>xs. P xs []"
    and "\<And>xs y ys. sorted (map key xs) \<Longrightarrow> P (dropWhile (ge key y) xs) ys
      \<Longrightarrow> P xs (y#ys)"
  shows "P xs ys"
  using assms(2-) assms(1)
  by (induction_schema) (case_tac ys, simp_all, lexicographic_order)
 
lemma filter_by_key_dropWhile[simp]:
  assumes "sorted (map key xs)"
  shows "[y\<leftarrow>dropWhile (\<lambda>x. key x \<le> key z) xs. key z = key y] = []"
    (is "[y\<leftarrow>dropWhile ?P xs. key z = key y] = []")
using assms
proof (induct xs rule: rev_induct)
  case Nil thus ?case by simp
next
  case (snoc x xs)
  hence IH: "[y\<leftarrow>dropWhile ?P xs. key z = key y] = []"
    by (auto simp: sorted_append)
  show ?case
  proof (cases "\<forall>z\<in>set xs. ?P z")
    case True
    show ?thesis
      using dropWhile_append2[of xs ?P "[x]"] and True by simp
  next
    case False
    then obtain a where a: "a \<in> set xs" "\<not> ?P a" by auto
    show ?thesis
      unfolding dropWhile_append1[of a xs ?P, OF a]
      using snoc and False by (auto simp: IH sorted_append)
  qed
qed

lemma filter_by_key_takeWhile[simp]:
  assumes "sorted (map key xs)"
  shows "[y\<leftarrow>takeWhile (\<lambda>x. key x \<le> key z) xs. key z = key y]
    = [y\<leftarrow>xs. key z = key y]"
    (is "[y\<leftarrow>takeWhile ?P xs. key z = key y] = _")
using assms
proof (induct xs rule: rev_induct)
  case Nil thus ?case by simp
next
  case (snoc x xs)
  hence IH: "[y\<leftarrow>takeWhile ?P xs. key z = key y] = [y\<leftarrow>xs. key z = key y]"
    by (auto simp: sorted_append)
  show ?case
  proof (cases "\<forall>z\<in>set xs. ?P z")
    case True
    show ?thesis
      using takeWhile_append2[of xs ?P "[x]"] and True by simp
  next
    case False
    then obtain a where a: "a \<in> set xs" "\<not> ?P a" by auto
    show ?thesis
      unfolding takeWhile_append1[of a xs ?P, OF a]
      using snoc and False by (auto simp: IH sorted_append)
  qed
qed
 
lemma filter_takeWhile_dropWhile_id[simp]:
  "filter P (takeWhile Q xs) @ filter P (dropWhile Q xs) = filter P xs"
  by (simp add: filter_append[symmetric])

lemma filter_by_key_merge_is_append[simp]:
  assumes "sorted (map key xs)"
  shows "[y\<leftarrow>merge key xs ys. key x = key y]
    = [y\<leftarrow>xs. key x = key y] @ [y\<leftarrow>ys. key x = key y]"
  using assms by (induct xs ys rule: sorted_merge_induct) auto

lemma filter_by_key_merge_pairs[simp]:
  assumes "\<forall>xs\<in>set xss. sorted (map key xs)"
  shows "[y\<leftarrow>concat (merge_pairs key xss). key x = key y]
    = [y\<leftarrow>concat xss. key x = key y]"
  using assms by (induct xss rule: merge_pairs.induct) simp_all

lemma filter_by_key_merge_all[simp]:
  assumes "\<forall>xs\<in>set xss. sorted (map key xs)"
  shows "[y\<leftarrow>merge_all key xss. key x = key y]
    = [y\<leftarrow>concat xss. key x = key y]"
  using assms by (induct xss rule: merge_all.induct) simp_all

lemma filter_by_key_merge_all_sequences[simp]:
  "[x\<leftarrow>merge_all key (sequences key xs) . key y = key x]
    = [x\<leftarrow>xs . key y = key x]"
  using sorted_sequences[of key xs] by simp

lemma sort_key_merge_all_sequences:
  "sort_key key = merge_all key \<circ> sequences key"
  by (intro ext properties_for_sort_key)
     (simp_all add: sorted_merge_all[OF sorted_sequences])

text {*
Replace existing code equations for @{const sort_key} by
@{term "merge_all key \<circ> sequences key"}.
*}
declare sort_key_merge_all_sequences[code]

end
end
