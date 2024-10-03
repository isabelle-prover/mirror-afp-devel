theory List_Slice
  imports Main
begin

section \<open>List Slices\<close>

fun list_slice :: 
  "'a list \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> 'a list"
where
  "list_slice xs i j = drop i (take j xs)"

lemma length_list_slice[simp add]:
  "length (list_slice xs i j) = (min j (length xs)) - i"
  by simp

lemma list_slice_cons:
  fixes i j :: nat
  assumes "i \<le> j"
  assumes "i > 0"
  shows "list_slice (x # xs) i j = list_slice xs (i - 1) (j - 1)"
  using assms gr0_implies_Suc[OF order.strict_trans2]
  by (fastforce dest: gr0_implies_Suc)

lemma list_slice_append:
  fixes i j k :: nat
  assumes "i \<le> j"
  assumes "j \<le> k"
  shows "list_slice xs i k = list_slice xs i j @ list_slice xs j k"
using assms
proof (induct xs arbitrary: i j k)
  case (Cons a xs i j k)
  note IH = this
  show ?case
  proof (cases "i > 0")
    assume "\<not> i > 0"
    hence "i = 0"
      by simp
    then show ?case
      unfolding list_slice.simps
      by (metis IH(3) append_take_drop_id drop0 min_def take_take)
  next
    assume "i > 0"
    with list_slice_cons[of i k a xs]
    have "list_slice (a # xs) i k = list_slice xs (i - 1) (k - 1)"
      using IH(2) IH(3) dual_order.trans by blast
    moreover
    from list_slice_cons[of i j a xs]
    have "list_slice (a # xs) i j = list_slice xs (i - 1) (j - 1)"
      using IH(2) \<open>i > 0\<close> by blast
    moreover
    from list_slice_cons[of j k a xs]
    have "list_slice (a # xs) j k = list_slice xs (j - 1) (k - 1)"
      using IH(2) IH(3) \<open>0 < i\<close> by blast
    moreover
    from IH(1)[of "i-1" "j-1" "k-1"]
    have "list_slice xs (i - 1) (k - 1) =
          list_slice xs (i - 1) (j - 1) @ list_slice xs (j - 1) (k - 1)"
      using IH(2) IH(3) diff_le_mono by blast
    ultimately show ?case
      by presburger
  qed
qed simp

lemma list_slice_0_length:
  fixes xs :: "'a list" 
  fixes n  :: nat
  assumes "length xs \<le> n"
  shows "list_slice xs 0 n = xs"
  using assms by simp

lemma list_slice_n_n[simp add]:
  fixes xs :: "'a list" 
  fixes n  :: nat
  shows "list_slice xs n n = []"
  by simp

lemma list_slice_nth:
  fixes i s e :: nat
  fixes xs :: "'a list" 
  assumes "i < length xs"
  assumes "s \<le> i"
  assumes "i < e"
  shows "(list_slice xs s e) ! (i - s) = xs ! i"
  using assms by simp

lemma list_slice_start_gre_length:
  fixes xs :: "'a list" 
  fixes s :: nat
  assumes "length xs \<le> s"
  shows "list_slice xs s e = []"
  using assms by simp

lemma list_slice_end_gre_length:
  fixes xs :: "'a list" 
  fixes e :: nat
  assumes "length xs \<le> e"
  shows "list_slice xs s e = list_slice xs s (length xs)"
  using assms by simp

lemma fold_list_slice:
  fixes i j :: nat
  fixes B :: "nat list"
  assumes "i \<le> j"
  and "j < length B"
  and "sorted B"
  fixes T zs :: "'a list" 
  shows
   "fold (\<lambda>x xs. xs @ list_slice T (B ! x) (B ! Suc x)) [i..<j] zs
    = zs @ (list_slice T (B ! i) (B ! j))"
  using assms
proof (induct j arbitrary: i)
  case 0
  then show ?case
    by (simp del: list_slice.simps)
next
  case (Suc j i)
  note IH = this
  show ?case
  proof (cases "i \<le> j")
    assume i_leq_j: "i \<le> j"

    have "fold (\<lambda>x xs. xs @ list_slice T (B ! x) (B ! Suc x)) [i..<Suc j] zs =
          fold (\<lambda>x xs. xs @ list_slice T (B ! x) (B ! Suc x)) [i..<j] zs @
            list_slice T (B ! j) (B ! Suc j)"
      using \<open>i \<le> j\<close> by force
    moreover
    from IH(1)[OF \<open>i \<le> j\<close> _ IH(4)]
    have "fold (\<lambda>x xs. xs @ list_slice T (B ! x) (B ! Suc x)) [i..<j] zs =
          zs @ list_slice T (B ! i) (B ! j)"
      using Suc.prems(2) Suc_lessD by blast
    moreover
    have "list_slice T (B ! i) (B ! Suc j) = list_slice T (B ! i) (B ! j) @
          list_slice T (B ! j) (B ! Suc j)"
      by (meson Suc.prems(2,3) Suc_lessD i_leq_j list_slice_append 
                sorted_iff_nth_Suc sorted_nth_mono)
    ultimately show ?case
      by (metis append.assoc)
  next
    assume "\<not> i \<le> j"
    then show ?case
      using Suc.prems(1) le_SucE by fastforce
  qed
qed

lemma nth_list_slice:
  fixes i s e :: nat
  fixes xs :: "'a list" 
  assumes "i < length (list_slice xs s e)"
  shows "(list_slice xs s e) ! i = xs ! (s + i)"
  using assms less_diff_conv by auto

lemma list_slice_nth_eq_iff_index_eq:
  fixes i s e j :: nat
  fixes xs :: "'a list" 
  assumes "distinct (list_slice xs s e)"
  assumes "e \<le> length xs"
  assumes "s \<le> i" and "i < e" 
  and     "s \<le> j" and "j < e"
  shows   "(xs ! i = xs ! j) \<longleftrightarrow> (i = j)"
  using assms
  by (fastforce 
      dest: nth_eq_iff_index_eq[where i = "i - s" and j = "j - s"])

lemma distinct_list_slice:
  fixes i j :: nat
  fixes xs :: "'a list" 
  assumes "distinct xs"
  shows   "distinct (list_slice xs i j)"
  using assms by simp

lemma list_slice_nth_mem:
  fixes e :: nat
  fixes xs :: "'a list" 
  fixes s i :: nat
  assumes "s \<le> i" and "i < e"
  assumes "e \<le> length xs"
  shows "xs ! i \<in> set (list_slice xs s e)"
  by (metis (no_types, opaque_lifting) assms nat_le_iff_add 
            add_diff_cancel_left' diff_less_mono nth_mem
            length_list_slice min_def nth_list_slice)

lemma nth_mem_list_slice:
  fixes x :: 'a
  fixes xs :: "'a list" 
  fixes s e :: nat
  assumes "x \<in> set (list_slice xs s e)"
  shows "\<exists>i < length xs. 
            s \<le> i \<and> 
            i < e \<and> 
            xs ! i = x"
proof -
  from in_set_conv_nth[THEN iffD1, OF \<open>_ \<in> _\<close>]
  obtain i where
    "i < length (list_slice xs s e)"
    "(list_slice xs s e) ! i = x"
    by auto
  with nth_list_slice[of i xs s e]
  have "xs ! (s + i) = x"
    by auto
  moreover
  have "s \<le> s + i"
    by linarith
  moreover
  have "s + i < length xs"
    using \<open>i < length (list_slice xs s e)\<close> by auto
  moreover
  have "s + i < e"
    using \<open>i < length (list_slice xs s e)\<close> by auto
  ultimately show ?thesis 
    by blast
qed

lemma list_slice_subset:
  fixes i j :: nat
  fixes xs :: "'a list" 
  shows "set (list_slice xs i j) \<subseteq> set xs"
  using set_drop_subset set_take_subset by force

lemma list_slice_Suc:
  fixes i j :: nat
  fixes xs :: "'a list" 
  assumes "i < length xs"
  assumes "i < j"
  shows "list_slice xs i j = xs ! i # list_slice xs (Suc i) j"
  by (metis assms Cons_nth_drop_Suc Suc_diff_Suc 
            list_slice.simps take_Suc_Cons drop_take)

lemma list_slice_update_unchanged_1:
  fixes xs :: "'a list" 
  fixes i j k :: nat
  assumes "i < j"
  shows "list_slice (xs[i := x]) j k = list_slice xs j k"
  by (simp add: assms drop_take)

lemma list_slice_update_unchanged_2:
  fixes i j k :: nat
  fixes xs :: "'a list" 
  assumes " k \<le> i"
  shows   "list_slice (xs[i := x]) j k = list_slice xs j k"
  by (metis assms list_slice.simps take_update_cancel)

lemma list_slice_update_changed:
  assumes "i < length xs"
  assumes  "j \<le> i" 
  assumes  "i < k"
  shows "list_slice (xs[i := x]) j k = (list_slice xs j k)[i - j := x]"
  using assms
  by (fastforce 
         intro: list_eq_iff_nth_eq[THEN iffD2]
         simp:  nth_list_slice  nth_list_update)

lemma list_slice_map_nth_upt:
  assumes "j < length xs"
  shows "list_slice xs i j = map (nth xs) [i..<j]"
  using assms 
  by (fastforce intro: list_eq_iff_nth_eq[THEN iffD2])


lemma map_list_slice:
  "map f (list_slice xs i j) = list_slice (map f xs) i j"
  by (simp add: drop_map take_map)

section \<open>Sorted List Slice\<close>

lemma (in linorder) sorted_list_slice:
  assumes "sorted xs"
  shows "sorted (list_slice xs i j)"
  by (simp add: assms sorted_wrt_drop sorted_wrt_take)

lemma (in linorder) sorted_map_list_slice:
  assumes "sorted (map f xs)" 
  shows "sorted (map f (list_slice xs i j))"
  by (metis assms drop_map list_slice.simps local.sorted_list_slice take_map)

lemma (in linorder) sorted_map_filter_list_slice:
  assumes "sorted (map f (filter P xs))"
  shows "sorted (map f (filter P (list_slice xs i j)))"
proof -
  have "i \<le> j \<or> j < i"
    using linorder_class.le_less_linear by blast
  moreover
  have "j < i \<Longrightarrow> ?thesis"
  proof -
    assume "j < i"
    hence "list_slice xs i j = []"
      by (simp add: drop_take)
    then show ?thesis
      by simp
  qed
  moreover
  have "i \<le> j \<Longrightarrow> ?thesis"
  proof -
    let ?as = "list_slice xs 0 i" and
        ?bs = "list_slice xs i j" and
        ?cs = "list_slice xs j (length xs)"
    assume "i \<le> j"
    hence "xs = ?as @ ?bs @ ?cs"
      by (metis le0 linorder_class.linear list_slice_0_length list_slice_append
                list_slice_start_gre_length)
    hence "filter P xs = filter P ?as @ filter P ?bs @ filter P ?cs"
      by (metis filter_append)
    hence "map f (filter P xs)
            = (map f (filter P ?as)) @ (map f (filter P ?bs)) @ (map f (filter P ?cs))"
      by simp
    with \<open>sorted (map f (filter P xs))\<close>
    show ?thesis
      by (simp add: local.sorted_append)
  qed
  ultimately show ?thesis
    by blast
qed

lemma (in linorder) list_slice_sorted_nth_mono:
  assumes "sorted (list_slice xs s e)"
  and     "s \<le> i"
  and     "i \<le> j"
  and     "j < e"
  and     "j < length xs"
shows "xs ! i \<le> xs ! j"
proof -
  have "\<exists>i'. i = s + i'"
    using assms(2) nat_le_iff_add by blast
  then obtain i' where
    "i = s + i'"
    by blast

  have "\<exists>j'. j = s + j'"
    using assms(2) assms(3) nat_le_iff_add by auto
  then obtain j' where
    "j = s + j'"
    by blast

  have "i' \<le> j'"
    using \<open>i = s + i'\<close> \<open>j = s + j'\<close> assms(3) by auto

  have "j' < length (list_slice xs s e)"
    using \<open>j = s + j'\<close> assms(4) assms(5) by auto
  with sorted_nth_mono[OF assms(1) `i' \<le> j'`]
  have "list_slice xs s e ! i' \<le> list_slice xs s e ! j'" .
  moreover
  have "xs ! i = list_slice xs s e ! i'"
    using \<open>i = s + i'\<close> assms(3-5) by force
  moreover
  have "xs ! j = list_slice xs s e ! j'"
    using \<open>j = s + j'\<close> \<open>j' < length (list_slice xs s e)\<close> nth_list_slice by force
  ultimately show ?thesis
    by simp
qed
end
