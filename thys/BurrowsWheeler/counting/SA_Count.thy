theory SA_Count
  imports Rank_Select
          "../util/SA_Util"
begin

section "Counting Properties on Suffix Arays"

context Suffix_Array_General begin

subsection "Counting Properties"

lemma sa_card_index:
  assumes "i < length s"
  shows "i = card {j. j < length s \<and> suffix s (sa s ! j) < suffix s (sa s ! i)}"
        (is "i = card ?A")
proof -
  let ?P = "\<lambda>j. j < length s \<and> suffix s (sa s ! j) < suffix s (sa s ! i)"
  have P: "\<forall>j < i. ?P j"
  proof (safe)
    fix j
    assume "j < i"
    with assms
    show "j < length s"
      by simp
  next
    fix j
    assume "j < i"
    with sorted_wrt_nth_less[OF sa_g_sorted[of s] `j < i`] assms
    show "suffix s (sa s ! j) < suffix s (sa s ! i)"
      using assms sa_length by auto
  qed

  have "?A = {j. j < i}"
  proof (safe)
    fix x
    assume "x < i"
    then show "x < length s"
      using assms by simp
  next
    fix x
    assume "x < i"
    then show "suffix s (sa s ! x) < suffix s (sa s ! i)"
      using P by auto
  next
    fix x
    assume Q: "x < length s" "suffix s (sa s ! x) < suffix s (sa s ! i)"
    hence "x \<noteq> i"
      by blast
    with sorted_nth_less_mono[OF strict_sorted_imp_sorted[OF sa_g_sorted],
                                 simplified length_map sa_length,
                              OF Q(1) assms]
         Q assms
    show "x < i"
      by (simp add: sa_length)
  qed
  then show ?thesis
    using card_Collect_less_nat by presburger
qed

corollary sa_card_s_index:
  assumes "i < length s"
  shows "i = card {j. j < length s \<and> suffix s j < suffix s (sa s ! i)}"
        (is "i = card ?A")
proof -
  let ?i = "sa s ! i"
  let ?v = "s ! ?i"
  let ?B = "{j. j < length s \<and> suffix s (sa s ! j) < suffix s ?i}"

  from sa_card_index[OF assms]
  have "i = card ?B" .
  moreover
  have "bij_betw (\<lambda>x. sa s ! x) ?B ?A"
  proof (intro bij_betwI'; safe)
    fix x y
    assume "x < length s" "y < length s" "sa s ! x = sa s ! y"
    then show "x = y"
      by (simp add: nth_eq_iff_index_eq sa_distinct sa_length)
  next
    fix x
    assume "x < length s"
    then show "sa s ! x < length s"
      using sa_nth_ex by fastforce
  next
    fix x
    assume "x < length s" "suffix s x < suffix s ?i"
    then show "\<exists>y \<in> ?B. x = sa s ! y"
      using ex_sa_nth by blast
  qed
  hence "card ?B = card ?A"
    using bij_betw_same_card by blast
  ultimately show ?thesis
    by simp
qed

lemma sa_card_s_idx:
  assumes "i < length s"
  shows "i = card {j. j < length s \<and> s ! j < s ! (sa s ! i)} +
             card {j. j < length s \<and> s ! j = s ! (sa s ! i) \<and> suffix s j < suffix s (sa s ! i)}"
proof -
  let ?i = "sa s ! i"
  let ?v = "s ! ?i"
  let ?A = "{j. j < length s \<and> s ! j < ?v}"
  let ?B = "{j. j < length s \<and> s ! j = ?v \<and> suffix s j < suffix s ?i}"
  let ?C = "{j. j < length s \<and> suffix s j < suffix s ?i}"

  from sa_card_s_index[OF assms]
  have "i = card ?C"
    by simp
  moreover
  have "?A \<inter> ?B = {}"
    by fastforce
  moreover
  have "?C = ?A \<union> ?B"
  proof (safe)
    fix x
    assume "x < length s" "suffix s x < suffix s ?i" "\<not>s ! x < s ! ?i"
    then show "s ! x = s ! ?i"
      by (metis Cons_less_Cons sa_nth_ex assms suffix_cons_Suc)
  next
    fix x
    assume "x < length s" "s ! x < s ! ?i"
    then show "suffix s x < suffix s ?i"
      by (metis Cons_less_Cons sa_nth_ex assms suffix_cons_Suc)
  qed
  ultimately show ?thesis
    by (simp add: card_Un_disjoint)
qed

lemma sa_card_index_lower_bound:
  assumes "i < length s"
  shows "card {j. j < length s \<and> s ! (sa s ! j) < s ! (sa s ! i)} \<le> i"
  (is "card ?A \<le> i")
proof -
  let ?B = "{j. j < length s \<and> suffix s (sa s ! j) < suffix s (sa s ! i)}"
  have "?A \<subseteq> ?B"
  proof safe
    fix x
    assume "x < length s" "s ! (sa s ! x) < s ! (sa s ! i)"
    then show "suffix s (sa s ! x) < suffix s (sa s ! i)"
      by (metis Cons_less_Cons Cons_nth_drop_Suc assms sa_nth_ex)
  qed
  hence "card ?A \<le> card ?B"
    by (simp add: card_mono)
  then show ?thesis
    using sa_card_index[OF assms] by simp
qed

lemma sa_card_rank_idx:
  assumes "i < length s"
  shows "i = card {j. j < length s \<and> s ! (sa s ! j) < s ! (sa s ! i)}
              + rank (sort s) (s ! (sa s ! i)) i"
proof -
  from sorted_card_rank_idx[of "sort s" i]
  have "i = card {j. j < length (sort s) \<and> sort s ! j < sort s ! i} + rank (sort s) (sort s ! i) i"
    using assms by fastforce
  moreover
  have "sort s ! i = s ! (sa s ! i)"
    using assms sort_sa_nth by auto
  moreover
  have "length (sort s) = length s"
    by simp
  ultimately show ?thesis
    using sort_sa_nth[of _s]
    by (metis (no_types, lifting) Collect_cong)
qed

corollary sa_card_rank_s_idx:
  assumes "i < length s"
  shows "i = card {j. j < length s \<and> s ! j < s ! (sa s ! i)}
              + rank (sort s) (s ! (sa s ! i)) i"
proof -
  let ?A = "{j. j < length s \<and> s ! j < s ! (sa s ! i)}"
  and ?B = "{j. j < length s \<and> s ! (sa s ! j) < s ! (sa s ! i)}"
  from sa_card_rank_idx[OF assms]
  have "i = card {j. j < length s \<and> s ! (sa s ! j) < s ! (sa s ! i)} +
            rank (sort s) (s ! (sa s ! i)) i" .
  moreover
  have "bij_betw (\<lambda>x. sa s ! x)
          {j. j < length s \<and> s ! (sa s ! j) < s ! (sa s ! i)}
          {j. j < length s \<and> s ! j < s ! (sa s ! i)}"
  proof (rule bij_betwI'; safe)
    fix x y
    assume "x < length s" "y < length s" "sa s ! x = sa s ! y"
    then show "x = y"
      by (simp add: nth_eq_iff_index_eq sa_distinct sa_length)
  next
    fix x
    assume "x < length s"
    then show "sa s ! x < length s"
      using sa_nth_ex by auto
  next
    fix x
    assume "x < length s" "s ! x < s ! (sa s ! i)"
    then show "\<exists>xa \<in> {j. j < length s \<and> s ! (sa s ! j) < s ! (sa s ! i)}.  x = sa s ! xa"
      using ex_sa_nth by blast
  qed
  hence "card ?B = card ?A"
    using bij_betw_same_card by blast
  ultimately show ?thesis
    by simp
qed

lemma sa_rank_nth:
  assumes "i < length s"
  shows "rank (sort s) (s ! (sa s ! i)) i =
          card {j. j < length s \<and> s ! j = s ! (sa s ! i) \<and>
                   suffix s j < suffix s (sa s ! i)}"
proof -
  let ?i = "sa s ! i"
  let ?v = "s ! ?i"
  let ?A = "{j. j < length s \<and> s ! j < ?v}"
  let ?B = "{j. j < length s \<and> s ! j = ?v \<and> suffix s j < suffix s ?i}"

  from sa_card_rank_s_idx[OF assms]
  have "i = card ?A + rank (sort s) ?v i" .
  moreover
  from sa_card_s_idx[OF assms]
  have "i = card ?A + card ?B" .
  ultimately show ?thesis
    by linarith
qed

lemma sa_suffix_nth:
  assumes "card {k. k < length s \<and> s ! k < c } + i < length s"
  and     "i < count_list s c"
shows "\<exists>as. suffix s (sa s ! (card {k. k < length s \<and> s ! k < c} + i)) = c # as"
proof -
  let ?A = "{k. k < length s \<and> s ! k < c}"
  let ?i = "card ?A"
  let ?A' = "{k. k < length (sort s) \<and> (sort s) ! k < c}"

  have "\<exists>as. suffix s (sa s ! (?i + i)) = (s ! (sa s ! (?i + i))) # as"
    using assms sa_nth_ex suffix_cons_ex by blast
  moreover
  have "s ! (sa s ! (?i + i)) = sort s ! (?i + i)"
    using assms(1) sort_sa_nth by presburger
  moreover
  {
    have "i < count_list (sort s) c"
      by (metis assms(2) count_list_perm sort_perm)
    moreover
    have "card ?A = card ?A'"
    proof -
      have "\<exists>f. bij_betw f {n. n < length s \<and> s ! n < c} {n. n < length (sort s) \<and> sort s ! n < c}"
        using bij_betw_sort_idx_ex by blast
      then show ?thesis
        using bij_betw_same_card by blast
    qed
    ultimately have "sort s ! (?i + i) = c"
      using sorted_nth_gen[of "sort s" c i] assms(1) by auto
  }
  ultimately show ?thesis
    by force
qed

subsection "Ordering Properties"

lemma sa_suffix_order_le:
  assumes "card {k. k < length s \<and> s ! k < c } < length s"
  shows "[c] \<le> suffix s (sa s ! (card {k. k < length s \<and> s ! k < c}))"
proof -
  let ?A = "{k. k < length s \<and> s ! k < c}"
  let ?A' = "{k. k < length (sort s) \<and> (sort s) ! k < c}"
  let ?i = "card ?A"
  let ?i' = "card ?A'"

  have "\<exists>as. suffix s (sa s ! ?i) = (s ! (sa s ! ?i)) # as"
    using assms sa_nth_ex suffix_cons_ex by blast
  then obtain as where
    "suffix s (sa s ! ?i) = (s ! (sa s ! ?i)) # as"
    by blast
  moreover
  from sort_sa_nth[of ?i s]
  have "sort s ! ?i = s ! (sa s ! ?i)"
    using assms by blast
  moreover
  have "?i = ?i'"
  proof -
    have "\<exists>f. bij_betw f {n. n < length s \<and> s ! n < c} {n. n < length (sort s) \<and> sort s ! n < c}"
      using bij_betw_sort_idx_ex by blast
    then show ?thesis
      using bij_betw_same_card by blast
  qed
  hence "c \<le> sort s ! ?i"
    using sorted_nth_le[of "sort s" c] assms by auto
  ultimately show ?thesis
    by fastforce
qed

lemma sa_suffix_order_le_gen:
  assumes "card {k. k < length s \<and> s ! k < c } + i < length s"
  shows "[c] \<le> suffix s (sa s ! (card {k. k < length s \<and> s ! k < c} + i))"
proof (cases i)
  case 0
  then show ?thesis
    using assms sa_suffix_order_le by auto
next
  let ?x = "card {k. k < length s \<and> s ! k < c }"
  case (Suc m)
  with sorted_wrt_mapD[OF sa_g_sorted, of ?x "?x + i" s]
  have "suffix s (sa s ! ?x) < suffix s (sa s ! (?x + i))"
    using assms sa_length by auto
  moreover
  have "[c] \<le> suffix s (sa s ! ?x)"
    using add_lessD1 assms sa_suffix_order_le by blast
  ultimately show ?thesis
    by order
qed

lemma sa_suffix_nth_less:
  assumes "i < card {k. k < length s \<and> s ! k < c}"
  shows "\<forall>as. suffix s (sa s ! i) < c # as"
proof -
  have "i < length s"
    using assms card_less_idx_upper dual_order.strict_trans1 by blast
  hence "\<exists>as. suffix s (sa s ! i) = s ! (sa s ! i) # as"
    using sa_nth_ex suffix_cons_Suc by blast
  moreover
  have "i < card {k. k < length (sort s) \<and> (sort s) ! k < c}"
    using bij_betw_sort_idx_ex[of "sort s" s c] assms bij_betw_same_card by force
  with sorted_nth_less_gen[of "sort s" i c]
  have "s ! (sa s ! i) < c"
    using sorted_nth_less_gen[of "sort s" i c] \<open>i < length s\<close> sort_sa_nth by force
  ultimately show ?thesis
    by fastforce
qed

lemma sa_suffix_nth_gr:
  assumes "card {k. k < length s \<and> s ! k < c} + i < length s"
  and     "count_list s c \<le> i"
shows "\<forall>as. c # as < suffix s (sa s ! (card {k. k < length s \<and> s ! k < c} + i))"
proof -
  let ?x = "card {k. k < length s \<and> s ! k < c}"
  let ?i = "?x + i"
  let ?y = "card {k. k < length (sort s) \<and> sort s ! k < c}"
  have "\<exists>as. suffix s (sa s ! ?i) = s ! (sa s ! ?i) # as"
    using assms(1) sa_nth_ex suffix_cons_Suc by blast
  moreover
  {
    have "?y = ?x"
      using bij_betw_sort_idx_ex[of "sort s" s c] bij_betw_same_card by force
    moreover
    have "?y + i < length (sort s)"
      using assms(1) calculation(1) by auto
    moreover
    have "count_list (sort s) c \<le> i"
      by (metis assms(2) count_list_perm mset_sort)
    ultimately have "s ! (sa s ! ?i) > c"
      using sorted_nth_gr_gen[of "sort s" c i] sort_sa_nth by fastforce
  }
  ultimately show ?thesis
    by fastforce
qed

end (* of context *)

end