theory SA_Util
  imports "SuffixArray.Suffix_Array_Properties"
          "SuffixArray.Simple_SACA_Verification"
          "../counting/Rank_Select"
begin

section "Suffix Array Properties"

subsection "Bijections"

lemma bij_betw_empty:
  "bij_betw f {} {}"
  using bij_betwI' by fastforce

lemma bij_betw_sort_idx_ex:
  assumes "xs = sort ys"
  shows "\<exists>f. bij_betw f {j. j < length ys \<and> ys ! j < x} {j. j < length xs \<and> xs ! j < x}"
proof -

  let ?A = "{j. j < length ys \<and> ys ! j < x}"
  let ?B = "{j. j < length xs \<and> xs ! j < x}"

  have "mset ys = mset xs"
    by (simp add: assms)
  with permutation_Ex_bij[of ys xs]
  obtain f where
    "bij_betw f {..<length ys} {..<length xs}"
    "(\<forall>i<length ys. ys ! i = xs ! f i)"
    by blast
  moreover
  have "?A \<subseteq> {..<length ys}"
    by blast
  moreover
  have "f ` ?A = ?B"
  proof safe
    fix a
    assume "a < length ys" "ys ! a < x"
    then show "f a < length xs"
      by (meson bij_betw_apply calculation(1) lessThan_iff)
  next
    fix a
    assume "a < length ys" "ys ! a < x"
    then show "xs ! f a < x"
      by (simp add: calculation(2))
  next
    fix a
    assume A: "a < length xs" "xs ! a < x"
    from bij_betw_iff_bijections[THEN iffD1, OF calculation(1)]
    obtain g where
      "\<forall>x\<in>{..<length ys}. f x \<in> {..<length xs} \<and> g (f x) = x"
      "\<forall>y\<in>{..<length xs}. g y \<in> {..<length ys} \<and> f (g y) = y"
      by blast
    then show "a \<in> f ` ?A"
      by (metis (no_types, lifting) A calculation(2) imageI lessThan_iff mem_Collect_eq)
  qed
  ultimately show ?thesis
    using bij_betw_subset
    by blast
qed

subsection "Suffix Properties"

lemma suffix_hd_set_eq:
  "{k. k < length s \<and> s ! k = c } = {k. k < length s \<and> (\<exists>xs. suffix s k = c # xs)}"
  using suffix_cons_ex by fastforce

lemma suffix_hd_set_less:
  "{k. k < length s \<and> s ! k < c } = {k. k < length s \<and> suffix s k < [c]}"
  using suffix_cons_ex by fastforce

lemma select_nth_suffix_start1:
  assumes "i < card {k. k < length s \<and> (\<exists>as. suffix s k = a # as)}"
  and     "xs = sort s"
shows "select xs a i = card {k. k < length s \<and> suffix s k < [a]} + i"
proof -
  let ?A = "{k. k < length s \<and> (\<exists>as. suffix s k = a # as)}"
  let ?A' = "{k. k < length s \<and> s ! k = a}"

  have "?A = ?A'"
    using suffix_cons_Suc by fastforce
  with assms(1)
  have "i < count_list s a"
    by (simp add: count_list_card)
  hence "i < count_list xs a"
    by (metis assms(2) count_list_perm mset_sort)
  moreover
  let ?B = "{k. k < length s \<and> suffix s k < [a]}"
  let ?B' = "{k. k < length s \<and> s ! k < a}"
  let ?B'' = "{k. k < length xs \<and> xs ! k < a}"
  {
    have "?B = ?B'"
      using suffix_cons_ex by fastforce
    moreover
    have "card ?B' = card ?B''"
      using bij_betw_sort_idx_ex[OF assms(2), of a] bij_betw_same_card
      by blast
    ultimately have "card ?B = card ?B''"
      by presburger
  }
  ultimately show ?thesis
    using sorted_select assms(2) by force
qed

lemma select_nth_suffix_start2:
  assumes "card {k. k < length s \<and> (\<exists>as. suffix s k = a # as)} \<le> i"
  and     "xs = sort s"
shows "select xs a i = length xs"
proof (rule select_out_of_range[of s])
  show "mset s = mset xs"
    by (simp add: assms(2))
next
  let ?A = "{k. k < length s \<and> (\<exists>as. suffix s k = a # as)}"
  let ?A' = "{k. k < length s \<and> s ! k = a}"
  have "?A = ?A'"
    using suffix_cons_Suc by fastforce
  with assms(1)
  show "count_list s a \<le> i"
    by (simp add: count_list_card)
qed

context Suffix_Array_General begin

subsection "General Properties"

lemma sa_subset_upt:
  "set (sa s) \<subseteq> {0..< length s}"
  by (simp add: sa_set_upt)

lemma sa_suffix_sorted:
  "sorted (map (suffix s) (sa s))"
  using sa_g_sorted strict_sorted_imp_sorted by blast

subsection "Nth Properties"

lemma sa_nth_suc_le:
  assumes "j < length s"
  and     "i < j"
  and     "s ! (sa s ! i) = s ! (sa s ! j)"
  and     "Suc (sa s ! i) < length s"
  and     "Suc (sa s ! j) < length s"
shows "s ! Suc (sa s ! i) \<le> s ! (Suc (sa s ! j))"
proof -
  from sorted_wrt_nth_less[OF sa_g_sorted[of s] assms(2)] assms(1,2)
  have "suffix s (sa s ! i) < suffix s (sa s ! j)"
    using sa_length by auto
  with assms(3-)
  have "suffix s (Suc (sa s ! i)) < suffix s (Suc (sa s ! j))"
    by (metis Cons_less_Cons Cons_nth_drop_Suc Suc_lessD order_less_imp_not_less)
  then show ?thesis
    by (metis Cons_less_Cons assms(4,5) dual_order.asym suffix_cons_Suc verit_comp_simplify1(3))
qed

lemma sa_nth_suc_le_ex:
  assumes "j < length s"
  and     "i < j"
  and     "s ! (sa s ! i) = s ! (sa s ! j)"
  and     "Suc (sa s ! i) < length s"
  and     "Suc (sa s ! j) < length s"
shows "\<exists>k l. k < l \<and> sa s ! k = Suc (sa s ! i) \<and> sa s ! l = Suc (sa s ! j)"
proof -
  from sorted_wrt_nth_less[OF sa_g_sorted[of s] assms(2)] assms(1,2)
  have "suffix s (sa s ! i) < suffix s (sa s ! j)"
    using sa_length by auto
  with assms(3-)
  have "suffix s (Suc (sa s ! i)) < suffix s (Suc (sa s ! j))"
    by (metis Cons_less_Cons Cons_nth_drop_Suc Suc_lessD order_less_imp_not_less)
  moreover
  from ex_sa_nth[OF assms(4)]
  obtain k where
    "k < length s"
    "sa s ! k = Suc (sa s ! i)"
    by blast
  moreover
  from ex_sa_nth[OF assms(5)]
  obtain l where
    "l < length s"
    "sa s ! l = Suc (sa s ! j)"
    by blast
  ultimately have "k < l"
    using sorted_nth_less_mono[OF strict_sorted_imp_sorted[OF sa_g_sorted[of s]]]
    by (metis length_map not_less_iff_gr_or_eq nth_map sa_length)
  with `sa s ! k = _` `sa s ! l = _`
  show ?thesis
    by blast
qed

lemma sorted_map_nths_sa:
  "sorted (map (nth s) (sa s))"
proof (intro sorted_wrt_mapI)
  fix i j
  assume "i < j" "j < length (sa s)"
  hence "suffix s (sa s ! i) < suffix s (sa s ! j)"
    using sa_g_sorted sorted_wrt_mapD by blast
  moreover
  have "suffix s (sa s ! i) = s ! (sa s ! i) # suffix s (Suc (sa s ! i))"
    by (metis \<open>i < j\<close> \<open>j < length (sa s)\<close> order.strict_trans sa_length sa_nth_ex suffix_cons_Suc)
  moreover
  have "suffix s (sa s ! j) = s ! (sa s ! j) # suffix s (Suc (sa s ! j))"
    by (metis \<open>j < length (sa s)\<close> sa_length sa_nth_ex suffix_cons_Suc)
  ultimately show "s ! (sa s ! i) \<le> s ! (sa s ! j)"
    by fastforce
qed

lemma perm_map_nths_sa:
  "s <~~> map (nth s) (sa s)"
  by (metis map_nth mset_map sa_g_permutation)

lemma sort_eq_map_nths_sa:
  "sort s = map (nth s) (sa s)"
  by (metis perm_map_nths_sa properties_for_sort sorted_map_nths_sa)

lemma sort_sa_nth:
  "i < length s \<Longrightarrow> sort s ! i = s ! (sa s ! i)"
  by (simp add: sa_length sort_eq_map_nths_sa)

lemma inj_on_nth_sa_upt:
  assumes "j \<le> length s" "l \<le> length s"
shows "inj_on (nth (sa s)) ({i..<j} \<union> {k..<l})"
proof
  fix x y
  assume "x \<in> {i..<j} \<union> {k..<l}" "y \<in> {i..<j} \<union> {k..<l}" "sa s ! x = sa s ! y"

  have "x < length s"
    using \<open>x \<in> {i..<j} \<union> {k..<l}\<close> assms(1) assms(2) by auto
  moreover
  have "y < length s"
    using \<open>y \<in> {i..<j} \<union> {k..<l}\<close> assms(1) assms(2) by auto
  ultimately show "x = y"
    by (metis \<open>sa s ! x = sa s ! y\<close> nth_eq_iff_index_eq sa_distinct sa_length)
qed

lemma nth_sa_upt_set:
  "nth (sa s) ` {0..<length s} = {0..<length s}"
proof safe
  fix x
  assume "x \<in> {0..<length s}"
  then show "sa s ! x \<in> {0..<length s}"
    using sa_nth_ex by force
next
  fix x
  assume "x \<in> {0..<length s}"
  then show "x \<in> (!) (sa s) ` {0..<length s}"
    by (metis ex_sa_nth image_iff in_set_conv_nth sa_length sa_set_upt)
qed

subsection "Valid List Properties"

lemma valid_list_sa_hd:
  assumes "valid_list s"
  shows "\<exists>n. length s = Suc n \<and> sa s ! 0 = n"
proof -
  from valid_list_ex_def[THEN iffD1, OF assms]
  obtain xs where
    "s = xs @ [bot]"
    by blast
  hence "valid_list (xs @ [bot])"
    using assms by simp
  with valid_list_bot_min[of xs sa, OF _ sa_g_permutation sa_g_sorted]
  obtain ys where
    "sa (xs @ [bot]) = length xs # ys"
    by blast
  with `s = xs @ [bot]`
  show ?thesis
    by simp
qed

lemma valid_list_not_last:
  assumes "valid_list s"
  and     "i < length s"
  and     "j < length s"
  and     "i \<noteq> j"
  and     "s ! i = s ! j"
shows "i < length s - 1 \<and> j < length s - 1"
  by (metis One_nat_def Suc_pred assms hd_drop_conv_nth last_suffix_index less_Suc_eq
            valid_list_length)

end (* of context *)

lemma Suffix_Array_General_ex:
  "\<exists>sa. Suffix_Array_General sa"
  using simple_saca.Suffix_Array_General_axioms by auto

end