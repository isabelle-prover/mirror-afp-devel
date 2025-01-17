theory BWT_SA_Corres
  imports BWT
          "../../counting/SA_Count"
          "../../util/Rotated_Substring"
begin

section "BWT and Suffix Array Correspondence"

context Suffix_Array_General begin

text \<open>Definition 3.12 from \<^cite>\<open>"Cheung_CPP_2025"\<close>: BWT Permutation\<close>
definition bwt_perm :: "('a  :: {linorder, order_bot}) list \<Rightarrow> nat list"
  where
"bwt_perm s = map (\<lambda>i. (i + length s - Suc 0) mod (length s)) (sa s)"

subsection "BWT Using Suffix Arrays"

lemma map_bwt_indexes:
  fixes s :: "('a :: {linorder, order_bot}) list"
  shows "bwt_sa s = map (\<lambda>i. s ! i) (bwt_perm s)"
  by (simp add: bwt_perm_def bwt_sa_def)

lemma map_bwt_indexes_perm:
  fixes s :: "('a :: {linorder, order_bot}) list"
  shows "bwt_perm s <~~> [0..<length s]"
proof (intro distinct_set_imp_perm)
  show "distinct [0..<length s]"
    by simp
next
  show "set (bwt_perm s) = set [0..<length s]"
    unfolding bwt_perm_def
  proof safe
    fix x
    assume "x \<in> set (map (\<lambda>i. (i + length s - Suc 0) mod length s) (sa s))"
    hence "x < length s"
      by (metis (no_types, lifting) ex_map_conv length_map length_pos_if_in_set mod_less_divisor
                                    sa_length)
    then show "x \<in> set [0..<length s]"
      by simp
  next
    fix x
    assume "x \<in> set [0..<length s]"
    hence "x \<in> {0..<length s}"
      using atLeastLessThan_upt by blast

    have "x \<in> (\<lambda>i. (i + length s - Suc 0) mod length s) ` {0..<length s}"
    proof (cases "Suc x < length s")
      assume "Suc x < length s"
      hence "(\<lambda>i. (i + length s - Suc 0) mod length s) (Suc x) = x"
        by simp
      then show ?thesis
        using \<open>Suc x < length s\<close> by force
    next
      assume "\<not> Suc x < length s"
      with \<open>x \<in> {0..<length s}\<close>
      have "Suc x = length s"
        by simp
      hence "(\<lambda>i. (i + length s - Suc 0) mod length s) 0 = x"
        using diff_Suc_1' lessI mod_less by presburger
      then show ?thesis
        by (metis (mono_tags, lifting) \<open>Suc x = length s\<close> atLeastLessThan_iff imageI zero_le
                                       zero_less_Suc)
    qed
    then show "x \<in> set (map (\<lambda>i. (i + length s - Suc 0) mod length s) (sa s))"
      by (simp add: sa_set_upt)
  qed
next
  show "distinct (bwt_perm s)"
  proof (intro distinct_conv_nth[THEN iffD2] allI impI)
    fix i j
    assume A: "i < length (bwt_perm s)" "j < length (bwt_perm s)" "i \<noteq> j"

    have "bwt_perm s ! i = (sa s ! i + length s - Suc 0) mod (length s)"
      using A(1) bwt_perm_def by force
    moreover
    have "bwt_perm s ! j = (sa s ! j + length s - Suc 0) mod (length s)"
      using A(2) bwt_perm_def by force
    moreover
    have "sa s ! i \<noteq> sa s ! j"
      by (metis A bwt_perm_def length_map nth_eq_iff_index_eq sa_distinct)

    have "(sa s ! i + length s - Suc 0) mod (length s) \<noteq> 
          (sa s ! j + length s - Suc 0) mod (length s)"
    proof (cases "sa s ! i")
      case 0
      hence "(sa s ! i + length s - Suc 0) mod (length s) = length s - Suc 0"
        by (metis diff_Suc_less gen_length_def length_code length_greater_0_conv list.size(3) 
                  mod_by_0 mod_less)
      moreover
      have "\<exists>m. sa s ! j = Suc m"
        using "0" \<open>sa s ! i \<noteq> sa s ! j\<close> not0_implies_Suc by force
      then obtain m where
        "sa s ! j = Suc m"
        by blast
      hence "(sa s ! j + length s - Suc 0) mod (length s) = m"
        using A(2) bwt_perm_def sa_length sa_nth_ex by force
      moreover
      have "Suc m \<le> length s - Suc 0"
        by (metis "0" A(1) A(2) Suc_pred \<open>sa s ! j = Suc m\<close> bwt_perm_def length_map less_Suc_eq_le 
                  sa_length sa_nth_ex)
      hence "m < length s - Suc 0"
        using Suc_le_eq by blast
      ultimately show ?thesis
        by (metis not_less_iff_gr_or_eq)
    next
      case (Suc n)
      assume "sa s ! i = Suc n"
      hence B: "(sa s ! i + length s - Suc 0) mod (length s) = n"
        using A(1) bwt_perm_def sa_length sa_nth_ex by force
      show ?thesis
      proof (cases "sa s ! j")
        case 0
        hence "(sa s ! j + length s - Suc 0) mod (length s) = length s - Suc 0"
          by (metis add_eq_if diff_Suc_less length_greater_0_conv list.size(3) mod_by_0 mod_less)
        moreover
        have "Suc n \<le> length s - Suc 0"
          by (metis "0" A(1,2) Suc Suc_pred bwt_perm_def length_map less_Suc_eq_le sa_length
                    sa_nth_ex)
        hence "n < length s - Suc 0"
          using Suc_le_eq by blast
        ultimately show ?thesis
          by (simp add: B)
      next
        case (Suc m)
        hence "(sa s ! j + length s - Suc 0) mod (length s) = m"
          using A(2) add_Suc bwt_perm_def sa_length sa_nth_ex by force
        moreover
        have "m \<noteq> n"
          using Suc \<open>sa s ! i = Suc n\<close> \<open>sa s ! i \<noteq> sa s ! j\<close> by auto
        ultimately show ?thesis
          using B by presburger
      qed
    qed
    ultimately show "bwt_perm s ! i \<noteq> bwt_perm s ! j"
      by presburger
  qed
qed

lemma bwt_sa_perm:
  fixes s :: "('a :: {linorder, order_bot}) list"
  shows "bwt_sa s <~~> s"
  by (metis map_bwt_indexes_perm  map_bwt_indexes map_nth mset_map)

lemma bwt_sa_nth:
  fixes s :: "('a :: {linorder, order_bot}) list"
  fixes i :: nat
  assumes "i < length s"
  shows "bwt_sa s ! i = s ! (((sa s ! i) + length s - 1) mod (length s))"
  using assms sa_length bwt_sa_def by force

lemma bwt_perm_nth:
  fixes s :: "('a :: {linorder, order_bot}) list"
  fixes i :: nat
  assumes "i < length s"
  shows "bwt_perm s ! i = ((sa s ! i) + length s - 1) mod (length s)"
  using assms sa_length bwt_perm_def by force

lemma bwt_perm_s_nth:
  fixes s :: "('a :: {linorder, order_bot}) list"
  fixes i :: nat
  assumes "i < length s"
  shows "bwt_sa s ! i = s ! (bwt_perm s ! i)"
  using assms bwt_perm_nth bwt_sa_nth by presburger

lemma bwt_sa_length:
  fixes s :: "('a :: {linorder, order_bot}) list"
  shows "length (bwt_sa s) = length s"
  using sa_length bwt_sa_def by force

lemma bwt_perm_length:
  fixes s :: "('a :: {linorder, order_bot}) list"
  shows "length (bwt_perm s) = length s"
  using sa_length bwt_perm_def by force

lemma ex_bwt_perm_nth:
  fixes s :: "('a :: {linorder, order_bot}) list"
  fixes k :: nat
  assumes "k < length s "
  shows "\<exists>i < length s. bwt_perm s ! i = k"
  using assms ex_perm_nth map_bwt_indexes_perm by blast

lemma valid_list_sa_index_helper:
  fixes s :: "('a :: {linorder, order_bot}) list"
  fixes i j :: nat
  assumes "valid_list s"
  and     "i < length s"
  and     "j < length s"
  and     "i \<noteq> j"
  and     "s ! (bwt_perm s ! i) = s ! (bwt_perm s ! j)"
 
shows "sa s ! i \<noteq> 0"
proof (rule ccontr)
  assume "\<not> sa s ! i \<noteq> 0"
  hence "sa s ! i = 0"
    by clarsimp

  from valid_list_length_ex[OF assms(1)]
  obtain n where
    "length s = Suc n"
    by blast

  let ?i = "(sa s ! i + length s - 1) mod length s"
  and ?j = "(sa s ! j + length s - 1) mod length s"

  from bwt_perm_nth[OF assms(2)]
  have "bwt_perm s ! i = ?i" .
  moreover
  from bwt_perm_nth[OF assms(3)]
  have "bwt_perm s ! j = ?j" .
  moreover
  have "?i = n"
    by (simp add: \<open>length s = Suc n\<close> \<open>sa s ! i = 0\<close>)
  hence "s ! ?i = bot"
    by (metis One_nat_def \<open>length s = Suc n\<close> assms(1) diff_Suc_Suc diff_zero last_conv_nth
              list.size(3) nat.distinct(1) valid_list_def)
  moreover
  have "\<exists>k. sa s ! j = Suc k"
    by (metis \<open>length s = Suc n\<close> \<open>sa s ! i = 0\<close> assms(2-4) less_Suc_eq_0_disj nth_eq_iff_index_eq
              sa_distinct sa_length sa_nth_ex)
  then obtain k where
    "sa s ! j = Suc k"
    by blast
  hence "?j = k \<and> k < n"
    by (metis \<open>length s = Suc n\<close> add_Suc_right add_Suc_shift add_diff_cancel_left' assms(3)
              dual_order.strict_trans lessI mod_add_self2 mod_less not_less_eq plus_1_eq_Suc
              sa_nth_ex)
  hence "s ! ?j \<noteq> bot"
    by (metis \<open>length s = Suc n\<close> assms(1) diff_Suc_1 valid_list_def)
  ultimately show False
    by (metis assms(5))
qed

text \<open>Theorem 3.13 from \<^cite>\<open>"Cheung_CPP_2025"\<close>: Suffix Relative Order Preservation
      Relative order of the suffixes is maintained by the BWT permutation\<close>
lemma bwt_relative_order:
  fixes s :: "('a :: {linorder, order_bot}) list"
  fixes i j :: nat
  assumes "valid_list s"
  and     "i < j"
  and     "j < length s"
  and     "s ! (bwt_perm s ! i) = s ! (bwt_perm s ! j)"
shows "suffix s (bwt_perm s ! i) < suffix s (bwt_perm s ! j)"
proof -
  from valid_list_length_ex[OF assms(1)]
  obtain n where
    "length s = Suc n"
    by blast

  let ?i = "(sa s ! i + length s - 1) mod length s"
  and ?j = "(sa s ! j + length s - 1) mod length s"

  from bwt_perm_nth[of i s] assms(2-3)
  have "bwt_perm s ! i = ?i"
    using dual_order.strict_trans by blast
  moreover
  from bwt_perm_nth[OF assms(3)]
  have "bwt_perm s ! j = ?j" .
  moreover
  from sorted_wrt_nth_less[OF sa_g_sorted assms(2)] assms(2,3)
  have "suffix s (sa s ! i) < suffix s (sa s ! j)"
    using sa_length by force
  moreover
  have "\<exists>k. sa s ! i = Suc k"
    using valid_list_sa_index_helper[OF assms(1) _ assms(3) _ assms(4)] assms(2,3)
          dual_order.strict_trans not0_implies_Suc by blast
  then obtain k where
    "sa s ! i = Suc k"
    by blast
  moreover
  from calculation(4)
  have "?i = k"
    by (metis Suc_lessD add.assoc assms(2,3) diff_Suc_1 dual_order.strict_trans mod_add_self2
              mod_less plus_1_eq_Suc sa_nth_ex)
  moreover
  have "\<exists>l. sa s ! j = Suc l"
  using valid_list_sa_index_helper[OF assms(1) assms(3) _ _ assms(4)[symmetric]] assms(2,3)
          dual_order.strict_trans not0_implies_Suc by blast
  then obtain l where
    "sa s ! j = Suc l"
    by blast
  moreover
  from calculation(6)
  have "?j = l"
    using assms(3) sa_nth_ex by force
  ultimately show ?thesis
    by (metis Cons_less_Cons Cons_nth_drop_Suc assms(1,4) mod_less_divisor valid_list_length)
qed

lemma bwt_sa_card_s_idx:
  fixes s :: "('a :: {linorder, order_bot}) list"
  fixes i :: nat
  assumes "valid_list s"
  and     "i < length s"
  shows "i = card {j. j < length s \<and> j < i \<and> bwt_sa s ! j \<noteq> bwt_sa s ! i} +
             card {j. j < length s \<and> s ! j = bwt_sa s ! i \<and>
                      suffix s j < suffix s (bwt_perm s ! i)}"
proof -
  let ?bwt = "bwt_sa s"
  let ?idx = "bwt_perm s"
  let ?i = "?idx ! i"
  let ?v = "?bwt ! i"
  let ?A = "{j. j < length s \<and> j < i \<and> ?bwt ! j \<noteq> ?v}"
  let ?B = "{j. j < length s \<and> s ! j = ?v \<and> suffix s j < suffix s ?i}"
  let ?C = "{j. j < length s \<and> j < i \<and> ?bwt ! j = ?v}"

  have P: "\<And>x. \<lbrakk>x < i; \<not>x < length s\<rbrakk> \<Longrightarrow> False"
    using assms(2) dual_order.strict_trans by blast

  have "?A \<inter> ?C = {}"
    by blast
  moreover
  have "?A \<union> ?C = {0..<i}"
    by (safe; clarsimp dest!: P)
  ultimately have "i = card ?A + card ?C"
    by (metis (no_types, lifting) List.finite_set atLeastLessThan_upt card_Un_disjnt card_upt
                                  disjnt_def finite_Un)
  moreover
  have "bij_betw (\<lambda>x. ?idx ! x) ?C ?B"
  proof (intro bij_betwI'; safe)
    fix x y
    assume "x < length s" "y < length s" "?idx ! x = ?idx ! y"
    with perm_distinct_iff[OF map_bwt_indexes_perm, of s]
    show "x = y"
      by (simp add: bwt_perm_length nth_eq_iff_index_eq)
  next
    fix x
    assume "x < length s"
    with map_bwt_indexes_perm[of s]
    show "?idx ! x < length s"
      using perm_nth_ex by blast
  next
    fix x
    assume "x < length s" "bwt_sa s ! x = ?v"
    then show "s ! (?idx ! x) = ?v"
      using bwt_perm_s_nth by auto
  next
    fix x
    assume "x < length s" "x < i" "bwt_sa s ! x = ?v"
    then show "suffix s (?idx ! x) < suffix s ?i"
      using bwt_relative_order[OF assms(1) _ assms(2), of x] assms(2) bwt_perm_s_nth by fastforce
  next
    fix x
    assume Q: "x < length s" "s ! x = ?v" "suffix s x < suffix s ?i"

    from perm_nth[OF map_bwt_indexes_perm[of s, symmetric],
                  simplified length_map sa_length length_upt]
    have "\<exists>y < length s. x = ?idx ! y"
      using Q(1) bwt_perm_length by auto
    then obtain y where
      "y < length s"
      "x = ?idx ! y"
      by blast
    moreover
    from Q(2) calculation
    have "?bwt ! y = ?v"
      by (simp add: bwt_perm_s_nth)
    moreover
    have "y < i"
    proof (rule ccontr)
      assume "\<not> y < i"
      hence "i \<le> y"
        by simp
      moreover
      from Q(3) `x = ?idx ! y`
      have "i = y \<Longrightarrow> False"
        by blast
      moreover
      have "i < y \<Longrightarrow> False"
      proof -
        assume "i < y"
        from bwt_relative_order[OF assms(1) `i < y` `y < _`]
             Q(2) `x = ?idx ! y`
        have "suffix s ?i < suffix s (?idx ! y)"
          by (simp add: bwt_perm_s_nth assms(2))
        with Q(3) `x = ?idx ! y`
        show False
          using order.asym by blast
      qed
      ultimately show False
        using nat_less_le by blast
    qed
    ultimately show "\<exists>y \<in> ?C. x = bwt_perm s ! y"
      by blast
  qed
  hence "card ?C = card ?B"
    using bij_betw_same_card by blast
  ultimately
  show ?thesis
    by presburger
qed

lemma bwt_perm_to_sa_idx:
  assumes "valid_list s"
  and     "i < length s"
shows "\<exists>k < length s. sa s ! k = bwt_perm s ! i \<and>
           k = card {j. j < length s \<and> s ! j < bwt_sa s ! i} +
               card {j. j < length s \<and> s ! j = bwt_sa s ! i \<and>
                        suffix s j < suffix s (bwt_perm s ! i)}"
proof -
  let ?bwt = "bwt_sa s"
  let ?v = "?bwt ! i"
  let ?i = "bwt_perm s ! i"
  let ?A = "{j. j < length s \<and> s ! j < ?v}"
  let ?B = "{j. j < length s \<and> s ! j = ?v \<and> suffix s j < suffix s ?i}"

  have "\<exists>k < length s. sa s ! k = ?i"
    by (metis assms bwt_perm_nth ex_sa_nth mod_less_divisor valid_list_length)
  then obtain k where
    "k < length s"
    "sa s ! k = ?i"
    by blast
  moreover
  have "s ! (sa s ! k) = ?v"
    using assms(2) bwt_perm_s_nth calculation(2) by presburger
  with sa_card_s_idx[OF calculation(1)]
  have "k = card ?A + card ?B"
    by (metis calculation(2))
  ultimately show ?thesis
    by blast
qed

corollary bwt_perm_eq:
  fixes s :: "('a :: {linorder, order_bot}) list"
  fixes i :: nat
  assumes "valid_list s"
  and     "i < length s"
shows "bwt_perm s ! i =
        sa s ! (card {j. j < length s \<and> s ! j < bwt_sa s ! i} +
                card {j. j < length s \<and> s ! j = bwt_sa s ! i \<and>
                         suffix s j < suffix s (bwt_perm s ! i)})"
  using assms bwt_perm_to_sa_idx by presburger

subsection "BWT Rank Properties"

lemma bwt_perm_rank_nth:
  fixes s :: "('a :: {linorder, order_bot}) list"
  fixes i :: nat
  assumes "valid_list s"
  and     "i < length s"
shows "rank (bwt_sa s) (bwt_sa s ! i) i =
        card {j. j < length s \<and> s ! j = bwt_sa s ! i \<and>
                 suffix s j < suffix s (bwt_perm s ! i)}"
proof -
  let ?bwt = "bwt_sa s"
  let ?idx = "bwt_perm s"
  let ?i = "?idx ! i"
  let ?v = "?bwt ! i"
  let ?A = "{j. j < length s \<and> s ! j = ?v \<and> suffix s j < suffix s ?i}"
  let ?B = "{j. j < length ?bwt \<and> j < i \<and> ?bwt ! j = ?v}"
  let ?C = "{j. j < length s \<and> j < i \<and> ?bwt ! j = ?v}"

  from valid_list_length_ex[OF assms(1)]
  obtain n where
    "length s = Suc n"
    by blast

  from rank_card_spec[of ?bwt ?v i]
  have "rank ?bwt ?v i = card ?B" .
  moreover
  have "?B = ?C"
    by (simp add: bwt_sa_length sa_length)
  moreover
  have "bij_betw (\<lambda>x. ?idx ! x) ?C ?A"
  proof (rule bij_betwI'; safe)
    fix x y
    assume "x < length s" "y < length s" "?idx ! x = ?idx ! y"
    then show "x = y"
      by (metis map_bwt_indexes_perm  bwt_perm_length nth_eq_iff_index_eq
                perm_distinct_set_of_upt_iff)
  next
    fix x
    assume "x < length s"
    then show "?idx ! x < length s"
      using map_bwt_indexes_perm perm_nth_ex by blast
  next
    fix x
    assume "x < length s" "x < i" "?bwt ! x = ?v"
    then show "s ! (?idx ! x) = ?v"
      using bwt_perm_s_nth by auto
  next
    fix x
    assume "x < length s" "x < i" "?bwt ! x = ?v"
    then show "suffix s (?idx ! x) < suffix s ?i"
      by (simp add: assms(1,2) bwt_relative_order bwt_perm_s_nth)
  next
    fix x
    assume "x < length s" "s ! x = ?v" "suffix s x < suffix s ?i"

    from perm_nth[OF map_bwt_indexes_perm[of s, symmetric],
                  simplified length_map sa_length length_upt, of x]
    have "\<exists>y < length s. x = ?idx ! y"
      using \<open>x < length s\<close> bwt_perm_length by auto
    then obtain y where
      "y < length s"
      "x = ?idx ! y"
      by blast
    moreover
    from calculation `s ! x = ?v`
    have "?bwt ! y = ?v"
      using bwt_perm_s_nth by presburger
    moreover
    have "y < i"
    proof (rule ccontr)
      assume "\<not> y < i"
      hence "i \<le> y"
        by simp
      moreover
      from `suffix s x < suffix s ?i` `x = ?idx ! y`
      have "y = i \<Longrightarrow> False"
        by blast
      moreover
      have "i < y \<Longrightarrow> False"
      proof -
        assume "i < y"
        with bwt_relative_order[OF assms(1) `i < y` `y < _`] `x = ?idx ! y` `s ! x = bwt_sa s ! i`
        have "suffix s ?i < suffix s x"
          using assms(2) bwt_perm_s_nth by presburger
        with `suffix s x < suffix s ?i`
        show False
          using less_not_sym by blast
      qed
      ultimately show False
        by linarith
    qed
    ultimately show "\<exists>y \<in> ?C. x = bwt_perm s ! y"
      by blast
  qed
  hence "card ?C = card ?A"
    using bij_betw_same_card by blast
  ultimately show ?thesis
    by presburger
qed

lemma bwt_sa_card_rank_s_idx:
  fixes s :: "('a :: {linorder, order_bot}) list"
  fixes i :: nat
  assumes "valid_list s"
  and     "i < length s"
shows "i = card {j. j < length s \<and> j < i \<and> bwt_sa s ! j \<noteq> bwt_sa s ! i} +
           rank (bwt_sa s) (bwt_sa s ! i) i"
  using assms bwt_sa_card_s_idx bwt_perm_rank_nth by presburger

subsection "Suffix Array and BWT Rank"

lemma sa_bwt_perm_same_rank:
  fixes s :: "('a :: {linorder, order_bot}) list"
  fixes i j :: nat
  assumes "valid_list s"
  and     "i < length s"
  and     "j < length s"
  and     "sa s ! i = bwt_perm s ! j"
shows "rank (sort s) (s ! (sa s ! i)) i = rank (bwt_sa s) (bwt_sa s ! j) j"
proof -
  let ?i = "sa s ! i"
  let ?v = "s ! ?i"
  let ?A = "{j. j < length s \<and> s ! j = ?v \<and> suffix s j < suffix s ?i}"

  have "bwt_sa s ! j = ?v"
    using bwt_perm_s_nth[OF assms(3)] assms(4) by presburger

  from sa_rank_nth[OF assms(2)]
  have "rank (sort s) ?v i = card ?A" .
  moreover
  from bwt_perm_rank_nth[OF assms(1,3), simplified assms(4)[symmetric]]  `bwt_sa s ! j = ?v`
  have "rank (bwt_sa s) (bwt_sa s ! j) j = card ?A"
    by simp
  ultimately show ?thesis
    by simp
qed

text \<open>Theorem 3.17 from \<^cite>\<open>Cheung_CPP_2025\<close>: Same Rank
      Rank for each symbol is the same in the BWT and suffix array\<close>
lemma rank_same_sa_bwt_perm:
  fixes s :: "('a :: {linorder, order_bot}) list"
  fixes i j :: nat
  fixes v :: 'a
  assumes "valid_list s"
  and     "i < length s"
  and     "j < length s"
  and     "s ! (sa s ! i) = v"
  and     "bwt_sa s ! j = v"
  and     "rank (sort s) v i = rank (bwt_sa s) v j"
shows "sa s ! i = bwt_perm s ! j"
proof -
  let ?A = "{j. j < length s \<and> s ! j < v}"
  from sa_card_rank_s_idx[OF assms(2), simplified assms(4)]
  have "i = card ?A + rank (sort s) v i" .
  moreover
  from bwt_perm_rank_nth[OF assms(1,3), simplified assms(5)]
       bwt_perm_eq[OF assms(1,3), simplified assms(5)]
  have "bwt_perm s ! j = sa s ! (card ?A + rank (bwt_sa s) v j)"
    by presburger
  with assms(6)
  have "bwt_perm s ! j = sa s ! (card ?A + rank (sort s) v i)"
    by simp
  ultimately show ?thesis
    by simp
qed

lemma rank_bwt_card_suffix:
  fixes s :: "('a :: {linorder, order_bot}) list"
  fixes i :: nat
  fixes a :: 'a
  assumes "i < length s"
  shows "rank (bwt_sa s) a i =
         card {k. k < length s \<and> k < i \<and> bwt_sa s ! k = a \<and>
                  a # suffix s (sa s ! k) < a # suffix s (sa s ! i)}"
proof -
  let ?X = "{j. j < length (bwt_sa s) \<and> j < i \<and> bwt_sa s ! j = a}"
  let ?Y = "{k. k < length s \<and> k < i \<and> bwt_sa s ! k = a \<and>
                a # suffix s (sa s ! k) < a # suffix s (sa s ! i)}"

  from rank_card_spec[of "bwt_sa s" a i]
  have "rank (bwt_sa s) a i = card ?X" .
  moreover
  have "?Y \<subseteq> ?X"
    using bwt_sa_length by auto
  moreover
  have "?X \<subseteq> ?Y"
  proof safe
    fix x
    assume "x < length (bwt_sa s)"
    then show "x < length s"
      by (simp add: bwt_sa_length)
  next
    fix x
    assume "x < length (bwt_sa s)" "x < i" "a = bwt_sa s ! x"
    with sorted_wrt_mapD[OF sa_g_sorted, of x i s]
    show "bwt_sa s ! x # suffix s (sa s ! x) < bwt_sa s ! x # suffix s (sa s ! i)"
      by (simp add: assms sa_length)
  qed
  ultimately show ?thesis
    by force
qed

lemma sa_to_bwt_perm_idx:
  fixes s :: "('a :: {linorder, order_bot}) list"
  fixes i :: nat
  assumes "valid_list s"
  and     "i < length s"
shows "sa s ! i =
        bwt_perm s ! (select (bwt_sa s) (s ! (sa s ! i)) (rank (sort s) (s ! (sa s ! i)) i))"
proof -
  let ?a = "s ! (sa s ! i)"
  let ?r1 = "rank (sort s) ?a i"
  let ?i = "select (bwt_sa s) ?a ?r1"
  let ?r2 = "rank (bwt_sa s) ?a ?i"

  have "?r1 < count_list (sort s) ?a"
    by (simp add: assms(2) rank_upper_bound sort_sa_nth)
  hence "?r1< count_list (bwt_sa s) ?a"
    by (metis bwt_sa_perm count_list_perm mset_sort)
  hence "?i < length (bwt_sa s)"
    by (metis rank_length select_upper_bound)
  hence "?r1 = ?r2 \<and> bwt_sa s ! ?i = ?a"
    by (metis rank_select select_nth_alt)
  with rank_same_sa_bwt_perm[OF assms, of ?i ?a]
  show ?thesis
    using \<open>?i < length (bwt_sa s)\<close> bwt_sa_length by fastforce
qed

lemma suffix_bwt_perm_sa:
  fixes s :: "('a :: {linorder, order_bot}) list"
  fixes i :: nat
  assumes "valid_list s"
  and     "i < length s"
  and     "bwt_sa s ! i \<noteq> bot"
shows "suffix s (bwt_perm s ! i) = bwt_sa s ! i # suffix s (sa s ! i)"
proof -
  from bwt_sa_nth[OF assms(2)]
  have "bwt_sa s ! i = s ! ((sa s ! i + length s - 1) mod length s)" .
  moreover
  have "sa s ! i \<noteq> 0"
    by (metis add_diff_cancel_left' assms(1,3) calculation diff_less diff_zero last_conv_nth 
              length_greater_0_conv less_one mod_less valid_list_def)
  ultimately have "bwt_sa s ! i = s ! (sa s ! i - 1)"
    by (metis Nat.add_diff_assoc2 One_nat_def Suc_lessD Suc_pred assms(2) bot_nat_0.not_eq_extremum 
              less_Suc_eq_le linorder_not_less mod_add_self2 mod_if sa_nth_ex)
  hence "bwt_sa s ! i # suffix s (sa s ! i) = suffix s (sa s ! i - 1)"
    by (metis Suc_lessD \<open>sa s ! i \<noteq> 0\<close> add_diff_inverse_nat assms(2) less_one plus_1_eq_Suc 
              sa_nth_ex suffix_cons_Suc)
  moreover
  have "bwt_perm s ! i = sa s ! i - 1"
    by (metis Nat.add_diff_assoc2 One_nat_def Suc_leI Suc_lessD Suc_pred \<open>sa s ! i \<noteq> 0\<close> assms(2) 
              bwt_perm_nth mod_add_self2 mod_less not_gr_zero sa_nth_ex)
  ultimately show ?thesis
    by presburger
qed

end (* of context *)

end
