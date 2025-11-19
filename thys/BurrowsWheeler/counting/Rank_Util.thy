theory Rank_Util
  imports "HOL-Library.Multiset"
          Count_Util
          "SuffixArray.Prefix"
begin

section "Rank Definition"

text \<open>Count how many occurrences of an element are in a certain index in the list\<close>

text \<open>Definition 3.7 from \<^cite>\<open>"Cheung_CPP_2025"\<close>: Rank\<close>
definition rank :: "'a list \<Rightarrow> 'a \<Rightarrow> nat \<Rightarrow> nat"
  where
"rank s x i \<equiv> count_list (take i s) x"

section "Rank Properties"

subsection "List Properties"

lemma rank_cons_same:
  "rank (x # xs) x (Suc i) = Suc (rank xs x i)"
  by (simp add: rank_def)

lemma rank_cons_diff:
  "a \<noteq> x \<Longrightarrow> rank (a # xs) x (Suc i) = rank xs x i"
  by (simp add: rank_def)

subsection "Counting Properties"

lemma rank_length:
  "rank xs x (length xs) = count_list xs x"
  by (simp add: rank_def)

lemma rank_gre_length:
  "length xs \<le> n \<Longrightarrow> rank xs x n = count_list xs x"
  by (simp add: rank_def)

lemma rank_not_in:
  "x \<notin> set xs \<Longrightarrow> rank xs x i = 0"
  by (metis gr_zeroI in_count rank_def set_take_subset subset_code(1))

lemma rank_0:
  "rank xs x 0 = 0"
  by (simp add: rank_def)

text \<open>Theorem 3.11 from \<^cite>\<open>"Cheung_CPP_2025"\<close>: Rank Equivalence\<close>
lemma rank_card_spec:
  "rank xs x i = card {j. j < length xs \<and> j < i \<and> xs ! j = x}"
proof -
  have "rank xs x i = count_list (take i xs) x"
    by (meson rank_def)
  moreover
  have "count_list (take i xs) x = card {j. j < length (take i xs) \<and> (take i xs) ! j = x}"
    by (metis count_list_card)
  moreover
  have "{j. j < length (take i xs) \<and> (take i xs) ! j = x} = 
        {j. j < length xs \<and> j < i \<and> xs ! j = x}"
    by fastforce
  ultimately show ?thesis
    by simp
qed


lemma le_rank_plus_card:
  "i \<le> j \<Longrightarrow>
   rank xs x j = rank xs x i + card {k. k < length xs \<and> i \<le> k \<and> k < j \<and> xs ! k = x}"
proof -
  assume "i \<le> j"

  let ?X = "{k. k < length xs \<and> k < j \<and> xs ! k = x}"
  have "rank xs x j = card ?X"
    by (simp add: rank_card_spec)
  moreover
  let ?Y = "{k. k < length xs \<and> k < i \<and> xs ! k = x}"
  have "rank xs x i = card ?Y"
    by (simp add: rank_card_spec)
  moreover
  let ?Z = "{k. k < length xs \<and> i \<le> k \<and> k < j \<and> xs ! k = x}"
  have "?Y \<union> ?Z = ?X"
  proof safe
    fix k
    assume "k < i"
    then show "k < j"
      using \<open>i \<le> j\<close> order_less_le_trans by blast
  next
    fix k
    assume "\<not> i \<le> k"
    then show "k < i"
      using linorder_le_less_linear by blast
  qed
  moreover
  have "?Y \<inter> ?Z = {}"
    by force
  hence "card (?Y \<union> ?Z) = card ?Y + card ?Z"
    by (simp add: card_Un_disjoint)
  ultimately show ?thesis
    by presburger
qed

subsection "Bound Properties"

lemma rank_lower_bound:
  assumes "k < rank xs x i"
  shows "k < i"
proof -
  from rank_card_spec[of xs x i]
  have "rank xs x i = card {j. j < length xs \<and> j < i \<and> xs ! j = x}" .
  hence "k < card {j. j < length xs \<and> j < i \<and> xs ! j = x}"
    using assms by presburger
  moreover
  {
    have "i \<le> length xs \<or> length xs < i"
      using linorder_not_less by blast
    moreover
    have "i \<le> length xs \<Longrightarrow> {j. j < length xs \<and> j < i \<and> xs ! j = x} \<subseteq> {0..<i}"
      using atLeast0LessThan by blast
    hence "i \<le> length xs \<Longrightarrow> card {j. j < length xs \<and> j < i \<and> xs ! j = x} \<le> i"
      using subset_eq_atLeast0_lessThan_card by presburger
    moreover
    have "length xs < i \<Longrightarrow> {j. j < length xs \<and> j < i \<and> xs ! j = x} \<subseteq> {0..<length xs}"
      using atLeast0LessThan by blast
    hence "length xs < i \<Longrightarrow> card {j. j < length xs \<and> j < i \<and> xs ! j = x} \<le> length xs"
      using subset_eq_atLeast0_lessThan_card by presburger
    hence "length xs < i \<Longrightarrow> card {j. j < length xs \<and> j < i \<and> xs ! j = x} \<le> i"
      by linarith
    ultimately have "card {j. j < length xs \<and> j < i \<and> xs ! j = x} \<le> i"
      by blast
  }
  ultimately show ?thesis
    using dual_order.strict_trans1 by blast
qed

corollary rank_Suc_ex:
  assumes "k < rank xs x i"
  shows "\<exists>l. i = Suc l"
  by (metis Nat.lessE assms rank_lower_bound)

lemma rank_upper_bound:
  "\<lbrakk>i < length xs; xs ! i = x\<rbrakk> \<Longrightarrow> rank xs x i < count_list xs x"
proof (induct xs arbitrary: i)
  case Nil
  then show ?case
    by (simp add: rank_def)
next
  case (Cons a xs i)
  then show ?case
  proof (cases i)
    case 0
    then show ?thesis
      by (metis Cons.prems(2) count_in list.set_intros(1) nth_Cons_0 rank_0)
  next
    case (Suc n)
    then show ?thesis
      by (metis Cons.hyps Cons.prems Suc_less_eq length_Cons nth_Cons_Suc rank_cons_diff 
                rank_cons_same rank_length)
  qed
qed

lemma rank_idx_mono:
  "i \<le> j \<Longrightarrow> rank xs x i \<le> rank xs x j"
proof (cases "i = j")
  assume "i = j"
  then show ?thesis
    by simp
next
  assume "i \<le> j" "i \<noteq> j"
  hence "i < j"
    using antisym_conv2 by blast
  hence "prefix xs j = prefix xs i @ list_slice xs i j"
    by (metis \<open>i \<le> j\<close> append_take_drop_id list_slice.elims min.absorb1 take_take)
  hence "rank xs x j = rank xs x i + count_list (list_slice xs i j) x"
    by (metis count_list_append rank_def)
  then show ?thesis
    by fastforce
qed

lemma rank_less:
  "\<lbrakk>i < length xs; i < j; xs ! i = x\<rbrakk> \<Longrightarrow> rank xs x i < rank xs x j"
proof -
  let ?X = "{k. k < length xs \<and> i \<le> k \<and> k < j \<and> xs ! k = x}"
  assume "i < length xs" "i < j" "xs ! i = x"
  with le_rank_plus_card[of i j xs x]
  have "rank xs x j = rank xs x i + card ?X"
    using nless_le by blast
  moreover
  have "i \<in> ?X"
    using \<open>i < j\<close> \<open>i < length xs\<close> \<open>xs ! i = x\<close> by blast
  hence "card ?X > 0"
    using card_gt_0_iff by fastforce
  ultimately show ?thesis
    by linarith
qed

lemma rank_upper_bound_gen:
  "rank xs x i \<le> count_list xs x"
  by (metis nat_le_linear rank_gre_length rank_idx_mono)


subsection "Sorted Properties"

lemma sorted_card_rank_idx:
  assumes "sorted xs"
  and     "i < length xs"
shows "i = card {j. j < length xs \<and> xs ! j < xs ! i} + rank xs (xs ! i) i"
proof -

  let ?A = "{j. j < length xs \<and> xs ! j < xs ! i}"
  let ?B = "{j. j < length xs \<and> xs ! j = xs ! i}"


  have "?B \<noteq> {}"
    using assms(2) by blast

  have "Min ?B \<in> ?B"
    by (metis (no_types, lifting) Min_in \<open>?B \<noteq> {}\<close> finite_nat_set_iff_bounded mem_Collect_eq)
  hence "Min ?B < length xs" "xs ! (Min ?B) = xs ! i"
    by simp_all

  have "Min ?B \<le> i"
    by (simp add: assms(2))

  have P: "\<forall>k < Min ?B. xs ! k < xs ! i"
  proof (intro allI impI)
    fix k
    assume "k < Min ?B"
    with sorted_nth_mono[OF assms(1) _ \<open>Min ?B < length xs\<close>]
    have "xs ! k \<le> xs ! (Min ?B)"
      using le_eq_less_or_eq by presburger
    
    show "xs ! k < xs ! i"
    proof (rule ccontr)
      assume "\<not> xs ! k < xs ! i"
      with \<open>xs ! k \<le> xs ! (Min ?B)\<close> \<open>xs ! (Min ?B) = xs ! i\<close>
      have "xs ! k = xs ! i"
        by order
      with \<open>k < Min ?B\<close> \<open>Min ?B < length xs\<close>
      have "k \<in> ?B"
        by auto
      then show False
        by (metis (mono_tags, lifting) Min_gr_iff \<open>k < Min ?B\<close> \<open>?B \<noteq> {}\<close> finite_nat_set_iff_bounded 
                                       less_irrefl_nat mem_Collect_eq)
    qed
  qed

  have "?A = {0..<Min ?B}"
  proof (intro equalityI subsetI)
    fix x
    assume "x \<in> ?A"
    hence "x < length xs" "xs ! x < xs ! i"
      by blast+
    hence "xs ! x < xs ! Min ?B"
      using \<open>xs ! Min ?B = xs ! i\<close> by simp
    hence "x < Min ?B"
      using assms(1) \<open>x < length xs\<close> \<open>Min ?B < length xs\<close>
      by (meson dual_order.strict_iff_not not_le_imp_less sorted_nth_mono)
    then show "x \<in> {0..<Min ?B}"
      using atLeastLessThan_iff by blast
  next
    fix x 
    assume "x \<in> {0..<Min ?B}"
    with P \<open>Min ?B < length xs\<close>
    show "x \<in> ?A"
      by auto
  qed
  moreover
  {
    let ?C = "{j. j < length xs \<and> j < i \<and> xs ! j = xs ! i}"
    from rank_card_spec[of xs "xs ! i" i]
    have "rank xs (xs ! i) i = card ?C" .
    moreover
    have "?C = {Min ?B..<i}" 
    proof (intro equalityI subsetI)
      fix x
      assume "x \<in> ?C"
      hence "x < length xs" "x < i" "xs ! x = xs ! i"
        by blast+
      hence "Min ?B \<le> x"
        by simp
      with \<open>x < i\<close>
      show "x \<in> {Min ?B..<i}"
        using atLeastLessThan_iff by blast
    next
      fix x
      assume "x \<in> {Min ?B..<i}"
      hence "Min ?B \<le> x" "x < i"
        using atLeastLessThan_iff by blast+
      moreover
      have "xs ! x = xs ! i"
      proof -
        have "xs ! x \<le> xs ! i"
          using assms(1,2) \<open>x < i\<close> 
          by (simp add: sorted_wrt_nth_less)
        moreover
        have "xs ! Min ?B \<le> xs ! x"
          using assms(1,2) \<open>Min ?B \<le> x\<close> \<open>x < i\<close>
          by (meson order.strict_trans sorted_iff_nth_mono)
        ultimately show ?thesis
          using \<open>xs ! Min ?B = xs ! i\<close> by order
      qed
      ultimately show "x \<in> ?C"
        using assms(2) by fastforce
    qed
    ultimately have "rank xs (xs ! i) i = card {Min ?B..<i}"
      by presburger
  }
  ultimately show ?thesis
    by (simp add: \<open>Min ?B \<le> i\<close>)
qed

lemma sorted_rank:
  assumes "sorted xs"
  and     "i < length xs"
  and     "xs ! i = a"
shows "rank xs a i = i - card {k. k < length xs \<and> xs ! k < a}"
  using assms(1) assms(2) assms(3) sorted_card_rank_idx by fastforce

lemma sorted_rank_less:
  assumes "sorted xs"
  and     "i < length xs"
  and     "xs ! i < a"
shows "rank xs a i = 0"
proof -
  have "rank xs a i = card {k. k < length xs \<and> k < i \<and> xs ! k = a}"
    by (simp add: rank_card_spec)
  moreover
  have "{k. k < length xs \<and> k < i \<and> xs ! k = a} = {}"
    using assms sorted_wrt_nth_less by fastforce
  ultimately show ?thesis
    by fastforce
qed

lemma sorted_rank_greater:
  assumes "sorted xs"
  and     "i < length xs"
  and     "xs ! i > a"
shows "rank xs a i = count_list xs a"
proof -
  let ?A = "{k. k < length xs \<and> k < i \<and> xs ! k = a}"
  have "rank xs a i = card ?A"
    by (simp add: rank_card_spec)
  moreover
  let ?B = "{k. k < length xs \<and> k \<ge> i \<and> xs ! k = a}"
  let ?C = "{k. k < length xs \<and> xs ! k = a}"
  {
    have "?A \<union> ?B = ?C"
    proof safe
      fix x
      assume "\<not> i \<le> x"
      then show "x < i"
        using linorder_le_less_linear by blast
    qed
    moreover
    have "?B = {}"
    proof -
      have "\<forall>k < length xs. k \<ge> i \<longrightarrow> xs ! k > a"
        by (meson assms(1) assms(3) dual_order.strict_trans1 sorted_nth_mono)
      then show ?thesis
        by blast
    qed
    ultimately have "?A = ?C"
      by blast
  }
  ultimately show ?thesis
    by (simp add: count_list_card)
qed

end