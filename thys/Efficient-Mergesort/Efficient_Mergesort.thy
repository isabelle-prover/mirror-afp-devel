(*  Author:      Christian Sternagel <c.sternagel@gmail.com>
    Maintainer:  Christian Sternagel <c.sternagel@gmail.com>
*)
theory Efficient_Mergesort
  imports "HOL-Library.Multiset"
begin


section \<open>GHC Version of Mergesort\<close>

text \<open>
  In the following we show that the mergesort implementation
  used in GHC (see \<^url>\<open>http://hackage.haskell.org/package/base-4.11.1.0/docs/src/Data.OldList.html#sort\<close>)
  is a correct and stable sorting algorithm. Furthermore, experimental
  data suggests that generated code for this implementation is much more
  efficient than for the implementation provided by \<^theory>\<open>HOL-Library.Multiset\<close>.
\<close>
context linorder
begin


subsection \<open>Definition of Natural Mergesort\<close>

text \<open>
  Split a list into chunks of ascending and descending parts, where
  descending parts are reversed on the fly.
  Thus, the result is a list of sorted lists.
\<close>
fun sequences :: "('b \<Rightarrow> 'a) \<Rightarrow> 'b list \<Rightarrow> 'b list list"
  and asc :: "('b \<Rightarrow> 'a) \<Rightarrow> 'b \<Rightarrow> ('b list \<Rightarrow> 'b list) \<Rightarrow> 'b list \<Rightarrow> 'b list list"
  and desc :: "('b \<Rightarrow> 'a) \<Rightarrow> 'b \<Rightarrow> 'b list \<Rightarrow> 'b list \<Rightarrow> 'b list list"
  where
    "sequences key (a # b # xs) =
      (if key a > key b then desc key b [a] xs else asc key b ((#) a) xs)"
  | "sequences key [x] = [[x]]"
  | "sequences key [] = []"
  | "asc key a f (b # bs) =
      (if \<not> key a > key b then asc key b (f \<circ> (#) a) bs
      else f [a] # sequences key (b # bs))"
  | "asc key a f [] = [f [a]]"
  | "desc key a as (b # bs) =
      (if key a > key b then desc key b (a # as) bs
      else (a # as) # sequences key (b # bs))"
  | "desc key a as [] = [a # as]"

fun merge :: "('b \<Rightarrow> 'a) \<Rightarrow> 'b list \<Rightarrow> 'b list \<Rightarrow> 'b list"
  where
    "merge key (a#as) (b#bs) =
      (if key a > key b then b # merge key (a#as) bs
      else a # merge key as (b#bs))"
  | "merge key [] bs = bs"
  | "merge key as [] = as"

fun merge_pairs :: "('b \<Rightarrow> 'a) \<Rightarrow> 'b list list \<Rightarrow> 'b list list"
  where
    "merge_pairs key (a#b#xs) = merge key a b # merge_pairs key xs"
  | "merge_pairs key xs = xs"

lemma length_merge [simp]:
  "length (merge key xs ys) = length xs + length ys"
  by (induct xs ys rule: merge.induct) simp_all

lemma length_merge_pairs [termination_simp]:
  "length (merge_pairs key xs) \<le> length xs"
  by (induct key xs rule: merge_pairs.induct) simp_all

fun merge_all :: "('b \<Rightarrow> 'a) \<Rightarrow> 'b list list \<Rightarrow> 'b list"
  where
    "merge_all key [] = []"
  | "merge_all key [x] = x"
  | "merge_all key xs = merge_all key (merge_pairs key xs)"

fun msort_key :: "('b \<Rightarrow> 'a) \<Rightarrow> 'b list \<Rightarrow> 'b list"
  where
    "msort_key key xs = merge_all key (sequences key xs)"


subsection \<open>Functional Correctness\<close>

lemma mset_merge [simp]:
  "mset (merge key xs ys) = mset xs + mset ys"
  by (induct xs ys rule: merge.induct) (simp_all add: ac_simps)

lemma set_merge [simp]:
  "set (merge key xs ys) = set xs \<union> set ys"
  by (simp flip: set_mset_mset)

lemma mset_concat_merge_pairs [simp]:
  "mset (concat (merge_pairs key xs)) = mset (concat xs)"
  by (induct key xs rule: merge_pairs.induct) (auto simp: ac_simps)

lemma set_concat_merge_pairs [simp]:
  "set (concat (merge_pairs key xs)) = set (concat xs)"
  by (simp flip: set_mset_mset)

lemma mset_merge_all [simp]:
  "mset (merge_all key xs) = mset (concat xs)"
  by (induct key xs rule: merge_all.induct) (simp_all add: ac_simps)

lemma set_merge_all [simp]:
  "set (merge_all key xs) = set (concat xs)"
  by (simp flip: set_mset_mset)

definition "ascP f = (\<forall>xs ys. f (xs @ ys) = f xs @ ys)"

lemma ascP_Cons [simp]: "ascP ((#) x)" by (simp add: ascP_def)

lemma ascP_comp_Cons [simp]: "ascP f \<Longrightarrow> ascP (f \<circ> (#) x)"
  by (auto simp: ascP_def simp flip: append_Cons)

lemma ascP_comp_Cons': "ascP f \<Longrightarrow> ascP (\<lambda>xs. f [] @ x # xs)"
  by (auto simp: ascP_def)

lemma ascP_f_singleton:
  assumes "ascP f"
  shows "f [x] = f [] @ [x]"
  using assms [unfolded ascP_def, THEN spec, THEN spec, of "[]" "[x]"] by simp

lemma ascP_f_Cons:
  assumes "ascP f"
  shows "f (x # xs) = f [] @ x # xs"
  using assms [unfolded ascP_def, THEN spec, THEN spec, of "[]" "x # xs"] by simp

lemma mset_sequences [simp]:
  "mset (concat (sequences key xs)) = mset xs"
  "ascP f \<Longrightarrow> mset (concat (asc key x f ys)) = {#x#} + mset (f []) + mset ys"
  "mset (concat (desc key x xs ys)) = {#x#} + mset xs + mset ys"
  by (induct key xs and key x f ys and key x xs ys rule: sequences_asc_desc.induct)
    (auto simp: ascP_f_singleton)

lemma mset_msort_key:
  "mset (msort_key key xs) = mset xs"
  by (auto)

lemma sorted_merge [simp]:
  assumes "sorted (map key xs)" and "sorted (map key ys)"
  shows "sorted (map key (merge key xs ys))"
  using assms by (induct key xs ys rule: merge.induct) (auto)

lemma sorted_merge_pairs [simp]:
  assumes "\<forall>x\<in>set xs. sorted (map key x)"
  shows "\<forall>x\<in>set (merge_pairs key xs). sorted (map key x)"
  using assms by (induct key xs rule: merge_pairs.induct) simp_all

lemma sorted_merge_all:
  assumes "\<forall>x\<in>set xs. sorted (map key x)"
  shows "sorted (map key (merge_all key xs))"
  using assms by (induct key xs rule: merge_all.induct) simp_all

lemma
  shows sorted_sequences: "\<forall>x \<in> set (sequences key xs). sorted (map key x)"
    and sorted_asc: "ascP f \<Longrightarrow> sorted (map key (f [])) \<Longrightarrow> \<forall>x\<in>set (f []). key x \<le> key a \<Longrightarrow> \<forall>x\<in>set (asc key a f ys). sorted (map key x)"
    and sorted_desc: "sorted (map key xs) \<Longrightarrow> \<forall>x\<in>set xs. key a \<le> key x \<Longrightarrow> \<forall>x\<in>set (desc key a xs ys). sorted (map key x)"
  by (induct key xs and key a f ys and key a xs ys rule: sequences_asc_desc.induct)
    (auto simp: ascP_f_singleton sorted_append not_less dest: order_trans, fastforce)

lemma sorted_msort_key:
  "sorted (map key (msort_key key xs))"
  by (unfold msort_key.simps) (intro sorted_merge_all sorted_sequences)


subsection \<open>Stability\<close>

lemma
  shows filter_by_key_sequences [simp]:
    "[y\<leftarrow>concat (sequences key xs). key y = k] = [y\<leftarrow>xs. key y = k]"
    and filter_by_key_asc:
    "ascP f \<Longrightarrow> [y\<leftarrow>concat (asc key a f ys). key y = k] = [y\<leftarrow>f [a] @ ys. key y = k]"
    and filter_by_key_desc:
    "sorted (map key xs) \<Longrightarrow> \<forall>x\<in>set xs. key a \<le> key x \<Longrightarrow> [y\<leftarrow>concat (desc key a xs ys). key y = k] = [y\<leftarrow>a # xs @ ys. key y = k]"
proof (induct key xs and key a f ys and key a xs ys rule: sequences_asc_desc.induct)
  case (4 key a f b bs)
  then show ?case
    by (auto simp: o_def ascP_f_Cons [where f = f] ascP_comp_Cons')
next
  case (6 key a as b bs)
  then show ?case
  proof (cases "key b < key a")
    case True
    with 6 have "[y\<leftarrow>concat (desc key b (a # as) bs). key y = k] =
      [y\<leftarrow>b # (a # as) @ bs. key y = k]"
      by  (auto) (insert dual_order.order_iff_strict dual_order.trans, blast+)
    moreover
    from 6 have "\<forall>x\<in>set (desc key a as (b # bs)). sorted (map key x)" by (intro sorted_desc)
    ultimately show ?thesis
      using True and 6 by (auto simp: Cons_eq_append_conv intro!: filter_False)
  qed auto
qed auto
 
lemma filter_by_key_merge_is_append [simp]:
  assumes "sorted (map key xs)"
  shows "[y\<leftarrow>merge key xs ys. key y = k] = [y\<leftarrow>xs. key y = k] @ [y\<leftarrow>ys. key y = k]"
  using assms
  by (induct key xs ys rule: merge.induct)
    (auto simp: Cons_eq_append_conv leD intro!: filter_False)

lemma filter_by_key_merge_pairs [simp]:
  assumes "\<forall>xs\<in>set xss. sorted (map key xs)"
  shows "[y\<leftarrow>concat (merge_pairs key xss). key y = k] = [y\<leftarrow>concat xss. key y = k]"
  using assms by (induct key xss rule: merge_pairs.induct) simp_all

lemma filter_by_key_merge_all [simp]:
  assumes "\<forall>xs\<in>set xss. sorted (map key xs)"
  shows "[y\<leftarrow>merge_all key xss. key y = k] = [y\<leftarrow>concat xss. key y = k]"
  using assms by (induct key xss rule: merge_all.induct) simp_all

lemma filter_by_key_merge_all_sequences [simp]:
  "[x\<leftarrow>merge_all key (sequences key xs) . key x = k] = [x\<leftarrow>xs . key x = k]"
  using sorted_sequences [of key xs] by simp

lemma msort_key_stable:
  "[x\<leftarrow>msort_key key xs. key x = k] = [x\<leftarrow>xs. key x = k]"
  by auto

lemma sort_key_msort_key_conv:
  "sort_key key = msort_key key"
  using msort_key_stable [of key "key x" for key x, of key]
  by (intro ext properties_for_sort_key mset_msort_key sorted_msort_key)
    (metis (mono_tags, lifting) filter_cong)

text \<open>
  Replace existing code equations for \<^const>\<open>sort_key\<close> by \<^term>\<open>msort_key key\<close>.
\<close>
declare sort_key_by_quicksort_code [code del]
declare sort_key_msort_key_conv [code]

end

end
