theory EGZ_Prime
  imports
    EGZ_Basics
begin

section \<open>The prime case\<close>

text \<open>
  The prime-modulus argument works entirely on residues modulo a prime
  @{term p}. After reducing an integer multiset modulo @{term p}, there are two
  possibilities: either some residue occurs at least @{term p} times, yielding an
  immediate zero-sum block, or every residue occurs fewer than @{term p} times.
  In the latter case we sort the remaining residues, pair the lower and upper
  halves, and use the subset-sum coverage theorem from the basics theory on the
  resulting list of nonzero gaps.
\<close>

subsection \<open>Compatibility of reduction modulo @{term p}\<close>

lemma sum_mset_mod_image:
  "sum_mset (image_mset (\<lambda>x::int. x mod m) M) mod m = sum_mset M mod m"
proof (induction M)
  case empty
  then show ?case
    by simp
next
  case (add x M)
  let ?s = "sum_mset (image_mset (\<lambda>x. x mod m) M)"
  have s_decomp: "?s = ?s div m * m + (?s mod m)"
    by (rule div_mult_mod_eq [symmetric])
  have "(x mod m + ?s) mod m = (x mod m + (?s div m * m + (?s mod m))) mod m"
    using s_decomp by simp
  also have "\<dots> = (x + sum_mset M) mod m"
    using add.IH by (metis mod_add_left_eq mod_add_right_eq s_decomp) 
  finally show ?case
    by simp
qed

subsection \<open>Sorted pairings and nonzero gaps\<close>

lemma sorted_nth_gap:
  assumes prime_p: "prime p"
  assumes sorted_ys: "sorted ys"
  assumes len: "length ys = 2 * (p - 1)"
  assumes count_bound: "\<forall>r. count (mset ys) r < p"
  assumes i_lt: "i < p - 1"
  shows "ys ! i < ys ! (i + (p - 1))"
proof (rule ccontr)
  have p_pos: "0 < p"
    using prime_gt_0_nat[OF prime_p] .
  have idx_lt: "i + (p - 1) < length ys"
    using i_lt len by simp
  have le_gap: "ys ! i \<le> ys ! (i + (p - 1))"
    by (rule sorted_nth_mono[OF sorted_ys]) (use i_lt idx_lt in simp_all)
  assume "\<not> ys ! i < ys ! (i + (p - 1))"
  then have ge_gap: "ys ! (i + (p - 1)) \<le> ys ! i"
    by simp
  then have eq_gap: "ys ! i = ys ! (i + (p - 1))"
    using le_gap by auto
  have mid_eq: "ys ! k = ys ! i" if k_range: "k \<in> {i..i + (p - 1)}" for k
  proof -
    have i_le_k: "i \<le> k" and k_le: "k \<le> i + (p - 1)"
      using k_range by auto
    have k_lt: "k < length ys"
      using k_le idx_lt by linarith
    have le_left: "ys ! i \<le> ys ! k"
      by (rule sorted_nth_mono[OF sorted_ys i_le_k k_lt])
    have le_right: "ys ! k \<le> ys ! (i + (p - 1))"
      by (rule sorted_nth_mono[OF sorted_ys k_le idx_lt])
    have "ys ! k \<le> ys ! i"
      using le_right eq_gap by simp
    with le_left show ?thesis
      by simp
  qed
  have interval_subset: "{i..i + (p - 1)} \<subseteq> {k. k < length ys \<and> ys ! k = ys ! i}"
  proof
    fix k
    assume k_in: "k \<in> {i..i + (p - 1)}"
    then have "k < length ys"
      using idx_lt by auto
    moreover have "ys ! k = ys ! i"
      by (rule mid_eq[OF k_in])
    ultimately show "k \<in> {k. k < length ys \<and> ys ! k = ys ! i}"
      by simp
  qed
  have p_le_card: "p \<le> card {k. k < length ys \<and> ys ! k = ys ! i}"
  proof -
    have finite_hits: "finite {k. k < length ys \<and> ys ! k = ys ! i}"
      by simp
    have "p = card {i..i + (p - 1)}"
      using p_pos by simp
    also have "\<dots> \<le> card {k. k < length ys \<and> ys ! k = ys ! i}"
      by (rule card_mono[OF finite_hits interval_subset])
    finally show ?thesis .
  qed
  have hits_eq: "{k. k < length ys \<and> ys ! k = ys ! i} = {k. k < length ys \<and> ys ! i = ys ! k}"
    by auto
  have count_eq: "count (mset ys) (ys ! i) = card {k. k < length ys \<and> ys ! k = ys ! i}"
    by (simp add: count_mset count_list_eq_length_filter length_filter_conv_card hits_eq)
  have "p \<le> count (mset ys) (ys ! i)"
    using p_le_card count_eq by simp
  then show False
    using count_bound by (simp add: dual_order.strict_iff_not) 
qed

lemma pair_differences_nonzero:
  assumes prime_p: "prime p"
  assumes sorted_ys: "sorted ys"
  assumes len: "length ys = 2 * (p - 1)"
  assumes ys_res: "set ys \<subseteq> residues p"
  assumes count_bound: "\<forall>r. count (mset ys) r < p"
  shows "\<forall>d\<in>set (map2 (\<lambda>a b. b - a) (take (p - 1) ys) (drop (p - 1) ys)). d mod int p \<noteq> 0"
proof
  fix d
  assume d_in: "d \<in> set (map2 (\<lambda>a b. b - a) (take (p - 1) ys) (drop (p - 1) ys))"
  have p_pos: "0 < p"
    using prime_gt_0_nat[OF prime_p] .
  have len_take: "length (take (p - 1) ys) = p - 1"
    using len p_pos by simp
  have len_drop: "length (drop (p - 1) ys) = p - 1"
    using len by simp
  from d_in obtain i where i_lt: "i < length (map2 (\<lambda>a b. b - a) (take (p - 1) ys) (drop (p - 1) ys))"
    and d_eq: "(map2 (\<lambda>a b. b - a) (take (p - 1) ys) (drop (p - 1) ys)) ! i = d"
    by (auto simp: in_set_conv_nth)
  have i_gap: "i < p - 1"
    using i_lt len_take len_drop by simp
  have idx_lt: "i + (p - 1) < length ys"
    using i_gap len by simp
  have low_eq: "take (p - 1) ys ! i = ys ! i"
    using i_gap by simp
  have high_eq: "drop (p - 1) ys ! i = ys ! (i + (p - 1))"
    using idx_lt by (simp add: nth_drop add.commute)
  have d_formula: "d = ys ! (i + (p - 1)) - ys ! i"
  proof -
    have "d = drop (p - 1) ys ! i - take (p - 1) ys ! i"
      using d_eq i_gap len_take len_drop by (simp add: nth_zip)
    also have "\<dots> = ys ! (i + (p - 1)) - ys ! i"
      by (simp only: high_eq low_eq)
    finally show ?thesis .
  qed
  have gap_lt: "ys ! i < ys ! (i + (p - 1))"
    by (rule sorted_nth_gap[OF prime_p sorted_ys len count_bound i_gap])
  have low_in: "ys ! i \<in> residues p"
    using ys_res i_gap len by (auto dest: nth_mem)
  have high_in: "ys ! (i + (p - 1)) \<in> residues p"
    using ys_res idx_lt by (auto dest: nth_mem)
  from low_in have low_bounds: "0 \<le> ys ! i" "ys ! i < int p"
    by (auto simp: residues_def)
  have idx_norm: "i + (p - 1) = i + p - 1"
    using p_pos by arith
  have high_lt_p: "ys ! (i + (p - 1)) < int p"
    by (metis atLeastLessThan_iff high_in residues_def)
  have "0 < d"
    using d_formula gap_lt by linarith
  moreover have "d < int p"
    using d_formula high_lt_p low_bounds by linarith
  ultimately show "d mod int p \<noteq> 0"
    by simp
qed

subsection \<open>Choosing one element from each pair\<close>

lemma paired_choice_length:
  assumes len_ys: "length ys = 2 * n"
  assumes I_sub: "I \<subseteq> {..<n}"
  shows "length (nths (take n ys) ({..<n} - I) @ nths (drop n ys) I) = n"
proof -
  have len_take: "length (take n ys) = n"
    using len_ys by simp
  have len_drop: "length (drop n ys) = n"
    using len_ys by simp
  have comp_sub: "{..<n} - I \<subseteq> {..<length (take n ys)}"
    using I_sub len_take by auto
  have I_sub_drop: "I \<subseteq> {..<length (drop n ys)}"
    using I_sub len_drop by simp
  have n_le_len: "n \<le> length ys"
    using len_ys by simp
  have len_low: "length (nths (take n ys) ({..<n} - I)) = card ({..<n} - I)"
  proof -
    have len_low_raw: "length (nths (take n ys) ({..<n} - I)) =
        card {i. i < length ys \<and> i < n \<and> i \<in> {..<n} - I}"
      by (simp add: length_nths)
    have hits_eq: "{i. i < length ys \<and> i < n \<and> i \<in> {..<n} - I} = {..<n} - I"
      using n_le_len by auto
    have card_eq: "card {i. i < length ys \<and> i < n \<and> i \<in> {..<n} - I} = card ({..<n} - I)"
      by (rule arg_cong[where f = card, OF hits_eq])
    from len_low_raw card_eq show ?thesis
      by simp
  qed
  have len_high: "length (nths (drop n ys) I) = card I"
  proof -
    have len_high_raw: "length (nths (drop n ys) I) = card {i. i < length ys - n \<and> i \<in> I}"
      by (simp add: length_nths)
    have high_hits_eq: "{i. i < length ys - n \<and> i \<in> I} = I"
      using I_sub_drop len_drop by auto
    from len_high_raw show ?thesis
      by (simp add: high_hits_eq)
  qed
  have card_low: "card ({..<n} - I) = n - card I"
    by (metis I_sub card_Diff_subset card_lessThan finite_lessThan finite_subset)
  show ?thesis
  proof -
    have finite_I: "finite I"
      using I_sub by (rule finite_subset) auto
    have card_I_le: "card I \<le> n"
      by (metis I_sub card_lessThan card_mono finite_lessThan)
    have card_total: "card ({..<n} - I) + card I = n"
      by (simp add: card_I_le card_low)
    have "length (nths (take n ys) ({..<n} - I) @ nths (drop n ys) I) =
        length (nths (take n ys) ({..<n} - I)) + length (nths (drop n ys) I)"
      by simp
    also have "\<dots> = n"
      using len_low len_high card_total by simp
    finally show ?thesis .
  qed
qed

lemma paired_choice_subset:
  "mset (nths (take n ys) ({..<n} - I) @ nths (drop n ys) I) \<subseteq># mset ys"
  by (metis append_take_drop_id mset_nths_subseteq subset_mset.add_mono union_code)

lemma paired_choice_sum:
  assumes len_ys: "length ys = 2 * n"
  assumes I_sub: "I \<subseteq> {..<n}"
  shows "sum_list (nths (take n ys) ({..<n} - I) @ nths (drop n ys) I) =
      sum_list (take n ys) + list_index_sum (map2 (\<lambda>a b. b - a) (take n ys) (drop n ys)) I"
proof -
  have len_take: "length (take n ys) = n" and len_drop: "length (drop n ys) = n"
    using len_ys by auto
  have I_sub_take: "I \<subseteq> {..<length (take n ys)}" and I_sub_drop: "I \<subseteq> {..<length (drop n ys)}"
    using I_sub len_drop len_ys by auto
  have "list_index_sum (take n ys) ({..<n} - I) + list_index_sum (take n ys) I = sum_list (take n ys)"
    by (metis I_sub len_take list_index_sum_partition)
  then have "sum_list (nths (take n ys) ({..<n} - I) @ nths (drop n ys) I) =
      sum_list (take n ys) - list_index_sum (take n ys) I + list_index_sum (drop n ys) I"
    using I_sub_drop I_sub len_ys sum_list_nths_eq_list_index_sum by force
  also have "\<dots> =
      sum_list (take n ys) + (list_index_sum (drop n ys) I - list_index_sum (take n ys) I)"
    by (simp add: algebra_simps)
  also have "\<dots> =
      sum_list (take n ys) + list_index_sum (map2 (\<lambda>a b. b - a) (take n ys) (drop n ys)) I"
    using I_sub_take len_ys len_drop by (simp add: list_index_sum_map2_diff)
  finally show ?thesis .
qed

subsection \<open>The residue-valued prime theorem\<close>

text \<open>
  In the nontrivial branch we remove one distinguished residue @{term z}, sort
  the remaining residues, split them into lower and upper halves, and consider
  the pairwise differences. Those differences are nonzero modulo @{term p}, so
  the subset-sum coverage theorem from the basics theory can realize the
  correction term needed to turn the lower half into a @{term p}-element
  zero-sum submultiset.
\<close>

lemma prime_residue_zero_sum_submultiset:
  assumes prime_p: "prime p"
  assumes size_R: "size R = 2 * p - 1"
  assumes R_sub: "set_mset R \<subseteq> residues p"
  shows "\<exists>N. N \<subseteq># R \<and> size N = p \<and> sum_mset N mod int p = 0"
proof -
  have p_pos: "0 < p"
    using prime_gt_0_nat[OF prime_p] .
  show ?thesis
  proof (cases "\<exists>r. p \<le> count R r")
    case True
    then obtain r where r_count: "p \<le> count R r"
      by auto
    let ?N = "replicate_mset p r"
    have "?N \<subseteq># R"
      using r_count by (simp add: count_le_replicate_mset_subset_eq)
    moreover have "size ?N = p"
      by simp
    moreover have "sum_mset ?N mod int p = 0"
      by simp
    ultimately show ?thesis
      by (intro exI[of _ ?N]) simp
  next
    case False
    let ?xs = "sorted_list_of_multiset R"
    have len_xs: "length ?xs = 2 * p - 1"
      by (metis mset_sorted_list_of_multiset size_R size_mset)
    have xs_nonempty: "?xs \<noteq> []"
    proof
      assume "?xs = []"
      with len_xs p_pos show False
        by simp
    qed
    have xs_sorted: "sorted ?xs"
      by simp
    have xs_res: "set ?xs \<subseteq> residues p"
      using R_sub by simp
    from xs_nonempty obtain z ys where xs_eq: "?xs = z # ys"
      by (cases ?xs) auto
    have len_ys: "length ys = 2 * (p - 1)"
    proof -
      have "Suc (length ys) = 2 * p - 1"
        using len_xs xs_eq by simp
      then have "length ys = 2 * p - 2"
        by simp
      also have "\<dots> = 2 * (p - 1)"
        using p_pos by arith
      finally show ?thesis .
    qed
    have ys_sorted: "sorted ys"
      using xs_sorted xs_eq by simp
    have ys_res: "set ys \<subseteq> residues p"
      using xs_res xs_eq by auto
    have R_decomp: "R = {#z#} + mset ys"
    proof -
      have "mset (sorted_list_of_multiset R) = mset (z # ys)"
        using xs_eq by simp
      then have "R = mset (z # ys)"
        by simp
      then show ?thesis
        by simp
    qed
    have count_bound_ys: "\<forall>r. count (mset ys) r < p"
    proof
      fix r
      have "count (mset ys) r \<le> count R r"
        using R_decomp by simp
      also have "\<dots> < p"
        using False leI by auto
      finally show "count (mset ys) r < p" .
    qed
    let ?us = "take (p - 1) ys"
    let ?vs = "drop (p - 1) ys"
    let ?ds = "map2 (\<lambda>a b. b - a) ?us ?vs"
    have len_ds: "length ?ds = p - 1"
      using len_ys by simp
    have ds_nonzero: "\<forall>d\<in>set ?ds. d mod int p \<noteq> 0"
      using pair_differences_nonzero[OF prime_p ys_sorted len_ys ys_res count_bound_ys]
      by simp
    let ?t = "(- z - sum_list ?us) mod int p"
    have t_in_res: "?t \<in> residues p"
      using p_pos by (simp add: residues_def)
    have ds_full: "mod_subset_sums p ?ds = residues p"
      by (rule mod_subset_sums_eq_residues[OF prime_p len_ds ds_nonzero])
    have t_in: "?t \<in> mod_subset_sums p ?ds"
      using t_in_res ds_full by simp
    then obtain I where I_sub: "I \<subseteq> {..<length ?ds}"
      and I_eq: "?t = list_index_sum ?ds I mod int p"
      using mod_subset_sums_iff_list_index_sum by blast
    have I_sub': "I \<subseteq> {..<(p - 1)}"
      using I_sub len_ds by simp
    let ?sel = "nths ?us ({..<(p - 1)} - I) @ nths ?vs I"
    have sel_sub: "mset ?sel \<subseteq># mset ys"
      by (rule paired_choice_subset)
    have sel_len: "length ?sel = p - 1"
      by (rule paired_choice_length[OF len_ys I_sub'])
    have sel_sum: "sum_list ?sel = sum_list ?us + list_index_sum ?ds I"
      by (rule paired_choice_sum[OF len_ys I_sub'])
    have N_sub: "mset (z # ?sel) \<subseteq># R"
    proof -
      have "mset (z # ?sel) = {#z#} + mset ?sel"
        by simp
      also have "\<dots> \<subseteq># {#z#} + mset ys"
        by (rule subset_mset.add_mono[OF subset_mset.order_refl sel_sub])
      also have "\<dots> = R"
        by (rule R_decomp[symmetric])
      finally show ?thesis .
    qed
    have N_size: "size (mset (z # ?sel)) = p"
      using sel_len p_pos by simp
    have N_sum: "sum_mset (mset (z # ?sel)) mod int p = 0"
    proof -
      have sum_z_sel: "sum_mset (mset (z # ?sel)) = z + sum_list ?sel"
      proof -
        have "sum_mset (mset (z # ?sel)) = z + sum_mset (mset ?sel)"
          by simp
        also have "\<dots> = z + sum_list ?sel"
          by (metis sum_mset_sum_list)
        finally show ?thesis .
        qed
      have step0: "sum_mset (mset (z # ?sel)) mod int p = (z + sum_list ?sel) mod int p"
        using sum_z_sel by simp
      have step1: "z + sum_list ?sel = z + sum_list ?us + list_index_sum ?ds I"
        using sel_sum by simp
      have "sum_mset (mset (z # ?sel)) mod int p = (z + sum_list ?us + list_index_sum ?ds I) mod int p"
        using step0 step1 by (simp add: algebra_simps)
      also have "\<dots> = (z + sum_list ?us + (list_index_sum ?ds I mod int p)) mod int p"
        by (simp add: mod_simps)
      also have "\<dots> = (z + sum_list ?us + ((- z - sum_list ?us) mod int p)) mod int p"
        using I_eq by simp
      also have "\<dots> = 0"
        by (simp add: mod_add_right_eq)
      finally show ?thesis .
    qed
    show ?thesis
      using N_sub N_size N_sum by (intro exI[of _ "mset (z # ?sel)"]) simp
  qed
qed

subsection \<open>Lifting the prime theorem back to integers\<close>

theorem prime_egz:
  assumes prime_p: "prime p"
  assumes size_M: "size M = 2 * p - 1"
  shows "\<exists>N. N \<subseteq># M \<and> size N = p \<and> sum_mset N mod int p = 0"
proof -
  have p_pos: "0 < p"
    using prime_gt_0_nat[OF prime_p] .
  let ?R = "image_mset (\<lambda>x::int. x mod int p) M"
  have size_R: "size ?R = 2 * p - 1"
    using size_M by simp
  have R_sub: "set_mset ?R \<subseteq> residues p"
    using p_pos by (auto simp: residues_def)
  have "\<exists>Nres. Nres \<subseteq># ?R \<and> size Nres = p \<and> sum_mset Nres mod int p = 0"
    by (rule prime_residue_zero_sum_submultiset[OF prime_p size_R R_sub])
  then obtain Nres where Nres_sub: "Nres \<subseteq># ?R"
    and Nres_size: "size Nres = p"
    and Nres_sum: "sum_mset Nres mod int p = 0"
    by auto
  obtain C where R_split: "?R = Nres + C"
    using Nres_sub by (auto simp: subset_mset.le_iff_add)
  from image_mset_eq_plusD[OF R_split]
  obtain N C' where M_split: "M = N + C'"
    and N_image: "Nres = image_mset (\<lambda>x::int. x mod int p) N"
    and C_image: "C = image_mset (\<lambda>x::int. x mod int p) C'"
    by blast
  have N_sub: "N \<subseteq># M"
    using M_split by (auto simp: subset_mset.le_iff_add)
  have N_size: "size N = p"
    using Nres_size N_image by simp
  have N_sum: "sum_mset N mod int p = 0"
    using Nres_sum N_image sum_mset_mod_image[of "int p" N] by simp
  show ?thesis
    using N_sub N_size N_sum by (intro exI[of _ N]) simp
qed

end

