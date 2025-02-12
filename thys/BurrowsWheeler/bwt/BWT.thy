theory BWT
  imports "../../util/SA_Util"
        
begin

section "Burrows-Wheeler Transform"

text \<open>Based on \<^cite>\<open>"Burrows_Tech_1994"\<close>\<close>

text \<open>Definition 3.3 from \<^cite>\<open>"Cheung_CPP_2025"\<close>: Canonical BWT\<close>
definition bwt_canon :: "('a  :: {linorder, order_bot}) list \<Rightarrow> 'a list"
  where
"bwt_canon s = map last (sort (map (\<lambda>x. rotate x s) [0..<length s]))"

context Suffix_Array_General begin

text \<open>Definition 3.4 from \<^cite>\<open>"Cheung_CPP_2025"\<close>: Suffix Array Version of the BWT\<close>
definition bwt_sa :: "('a  :: {linorder, order_bot}) list \<Rightarrow> 'a list"
  where
"bwt_sa s = map (\<lambda>i. s ! ((i + length s - Suc 0) mod (length s))) (sa s)"

end (* of context *)

section "BWT Verification"

subsection "List Rotations"

lemma rotate_suffix_prefix:
  assumes "i < length xs"
  shows "rotate i xs = suffix xs i @ prefix xs i"
  by (simp add: assms rotate_drop_take)

lemma rotate_last:
  assumes "i < length xs"
  shows "last (rotate i xs) = xs ! ((i + length xs - Suc 0) mod (length xs))"
  by (metis Nat.add_diff_assoc One_nat_def Suc_leI assms diff_less last_conv_nth
            length_greater_0_conv length_rotate list.size(3) not_less_zero nth_rotate zero_less_one)

lemma (in Suffix_Array_General) map_last_rotations:
  "map last (map (\<lambda>i. rotate i s) (sa s)) = bwt_sa s"
proof -
  have "\<forall>x\<in>set (sa s). last (rotate x s) = s ! ((x + length s - Suc 0) mod length s)"
    by (meson atLeastLessThan_iff rotate_last sa_subset_upt subset_code(1))
  then show ?thesis
    unfolding bwt_sa_def by simp
qed

lemma distinct_rotations:
  assumes "valid_list s"
  and     "i < length s"
  and     "j < length s"
  and     "i \<noteq> j"
shows "rotate i s \<noteq> rotate j s"
proof -
  from rotate_suffix_prefix[OF assms(2)]
       rotate_suffix_prefix[OF assms(3)]
       suffix_has_no_prefix_suffix[OF assms, simplified]
       suffix_has_no_prefix_suffix[OF assms(1,3,2) assms(4)[symmetric], simplified]
  show ?thesis
    by (metis append_eq_append_conv2)
qed

subsection "Ordering"

lemma list_less_suffix_app_prefix_1:
  assumes "valid_list xs"
  and     "i < length xs"
  and     "j < length xs"
  and     "suffix xs i < suffix xs j"
shows "suffix xs i @ prefix xs i < suffix xs j @ prefix xs j"
proof -
  from suffix_less_ex[OF assms]
  obtain b c as bs cs where
    "suffix xs i = as @ b # bs"
    "suffix xs j = as @ c # cs"
    "b < c"
    by blast
  hence "suffix xs i @ prefix xs i = as @ b # bs @ prefix xs i"
        "suffix xs j @ prefix xs j = as @ c # cs @ prefix xs j"
    by simp_all
  with `b < c`
  show ?thesis
    by (metis list_less_ex)
qed

lemma list_less_suffix_app_prefix_2:
  assumes "valid_list xs"
  and     "i < length xs"
  and     "j < length xs"
  and     "suffix xs i @ prefix xs i < suffix xs j @ prefix xs j"
shows "suffix xs i < suffix xs j"
  by (metis assms list_less_suffix_app_prefix_1 not_less_iff_gr_or_eq suffixes_neq)

corollary list_less_suffix_app_prefix:
  assumes "valid_list xs"
  and     "i < length xs"
  and     "j < length xs"
shows "suffix xs i < suffix xs j \<longleftrightarrow>
       suffix xs i @ prefix xs i < suffix xs j @ prefix xs j"
  using assms list_less_suffix_app_prefix_1 list_less_suffix_app_prefix_2 by blast

text \<open>Theorem 3.5 from \<^cite>\<open>"Cheung_CPP_2025"\<close>: Same Suffix and Rotation Order\<close>
lemma list_less_suffix_rotate:
  assumes "valid_list xs"
  and     "i < length xs"
  and     "j < length xs"
shows "suffix xs i < suffix xs j \<longleftrightarrow> rotate i xs < rotate j xs"
  by (simp add: assms list_less_suffix_app_prefix rotate_suffix_prefix)

lemma (in Suffix_Array_General) sorted_rotations:
  assumes "valid_list s"
  shows "strict_sorted (map (\<lambda>i. rotate i s) (sa s))"
proof (intro sorted_wrt_mapI)
  fix i j
  assume "i < j" "j < length (sa s)"
  with sorted_wrt_nth_less[OF sa_g_sorted `i < j`, simplified, OF `j < _`]
  have "suffix s (sa s ! i) < suffix s (sa s ! j)"
    by force
  with list_less_suffix_rotate[THEN iffD1, OF assms, of "sa s ! i" "sa s ! j"]
  show "rotate (sa s ! i) s < rotate (sa s ! j) s"
    by (metis \<open>i < j\<close> \<open>j < length (sa s)\<close> dual_order.strict_trans sa_length sa_nth_ex)
qed

subsection "BWT Equivalence"

text \<open>Theorem 3.6 from \<^cite>\<open>"Cheung_CPP_2025"\<close>: BWT and Suffix Array Correspondence
      Canoncial BWT and BWT via Suffix Array Correspondence\<close>
theorem (in Suffix_Array_General) bwt_canon_eq_bwt_sa:
  assumes "valid_list s"
  shows "bwt_canon s = bwt_sa s"
proof -
  let ?xs = "map (\<lambda>x. rotate x s) [0..<length s]"

  have "distinct ?xs"
    by (intro distinct_conv_nth[THEN iffD2] allI impI; simp add: distinct_rotations[OF assms])
  hence "strict_sorted (sort ?xs)"
    using distinct_sort sorted_sort strict_sorted_iff by blast
  hence "sort ?xs = map (\<lambda>i. rotate i s) (sa s)"
    using sorted_rotations[OF assms]
    by (simp add: strict_sorted_equal sa_set_upt)
  with map_last_rotations[of s]
  have "map last (sort ?xs) = bwt_sa s"
    by presburger
  then show ?thesis
    by (metis bwt_canon_def)
qed

end