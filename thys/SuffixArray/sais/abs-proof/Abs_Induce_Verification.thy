theory Abs_Induce_Verification
  imports 
    Abs_Induce_L_Verification 
    Abs_Induce_S_Verification 
    Abs_Bucket_Insert_Verification
begin

section "Bucket Initialisation Properties"

lemma l_bucket_init_map_bucket_start:
  "l_bucket_init \<alpha> T (map (bucket_start \<alpha> T) [0..<Suc (\<alpha> (Max (set T)))])"
  unfolding l_bucket_init_def
  by (metis add.left_neutral diff_zero le_imp_less_Suc length_map length_upt lessI nth_map_upt)

lemma lms_bucket_init_map_bucket_end:
  "lms_bucket_init \<alpha> T (map (bucket_end \<alpha> T) [0..<Suc (\<alpha> (Max (set T)))])"
  unfolding lms_bucket_init_def
  by (metis add.left_neutral diff_zero le_imp_less_Suc length_map length_upt lessI nth_map_upt)

lemma s_bucket_init_map_bucket_end:
  "s_bucket_init \<alpha> T ((map (bucket_end \<alpha> T) [0..<Suc (\<alpha> (Max (set T)))])[0 := 0])"
  unfolding s_bucket_init_def
  by (metis (no_types, lifting) length_greater_0_conv length_list_update list.size(3)
                                nth_list_update lms_bucket_init_def lms_bucket_init_map_bucket_end)

abbreviation "bucket_starts \<alpha> T \<equiv> map (bucket_start \<alpha> T) [0..<Suc (\<alpha> (Max (set T)))]"

abbreviation "bucket_ends \<alpha> T \<equiv> map (bucket_end \<alpha> T) [0..<Suc (\<alpha> (Max (set T)))]"

section "Bucket Insert Precondition"

lemma lms_pre_established:
  assumes "set LMS = {i. abs_is_lms T i}"
  and     "distinct LMS"
  and     "strict_mono \<alpha>"
shows "lms_pre \<alpha> T (bucket_ends \<alpha> T) (replicate (length T) (length T)) (rev LMS)"
      (is "lms_pre \<alpha> T ?B ?SA (rev LMS)")
proof -
  from lms_bucket_init_map_bucket_end[of \<alpha> T]
  have "lms_bucket_init \<alpha> T ?B" .
  then show "lms_pre \<alpha> T ?B ?SA0 (rev LMS)"
    by (clarsimp simp: lms_pre_def `lms_bucket_init \<alpha> T ?B` assms
                 simp del: upt_Suc)
qed

section "Induce L Precondition"

lemma l_perm_pre_established:
  assumes "valid_list T"
  and     "strict_mono \<alpha>"
  and     "lms_pre \<alpha> T B SA (rev LMS)"
shows "l_perm_pre \<alpha> T (bucket_starts \<alpha> T) (abs_bucket_insert \<alpha> T B SA (rev LMS))"
      (is "l_perm_pre \<alpha> T ?B ?SA")
  unfolding l_perm_pre_def
proof safe
  show "lms_init \<alpha> T ?SA"
    by (metis assms(3) abs_bucket_insert_vals lms_init_def lms_vals_postD)
next
  show "l_init \<alpha> T ?SA"
    unfolding l_init_def
  proof (intro allI impI; elim conjE)
    fix b i
    assume "b \<le> \<alpha> (Max (set T))" "i < length ?SA" "bucket_start \<alpha> T b \<le> i"
           "i < l_bucket_end \<alpha> T b"
    hence "i < lms_bucket_start \<alpha> T b"
      using l_bucket_end_le_lms_bucket_start less_le_trans by blast
    with lms_unknowns_postD[OF abs_bucket_insert_unknowns[OF assms(3)] `b \<le> _`
          `bucket_start _ _ _ \<le> _`]
    show "?SA ! i = length T" .
  qed
next
  show "s_init \<alpha> T ?SA"
    unfolding s_init_def
  proof (intro allI impI; elim conjE)
    fix b i
    assume "b \<le> \<alpha> (Max (set T))" "i < length ?SA" "l_bucket_end \<alpha> T b \<le> i"
           "i < lms_bucket_start \<alpha> T b"
    hence "bucket_start \<alpha> T b \<le> i"
      by (simp add: l_bucket_end_def)
    with lms_unknowns_postD[OF abs_bucket_insert_unknowns[OF assms(3)] `b \<le> _` _
          `i < lms_bucket_start _ _ _`]
    show "?SA ! i = length T" .
  qed
next
  from l_bucket_init_map_bucket_start[of \<alpha> T]
  show "l_bucket_init \<alpha> T ?B" .
next
  show "length ?SA = length T"
    by (metis assms(3) abs_bucket_insert_length lms_pre_elims(2))
qed (force simp: valid_list_not_nil[OF assms(1)] assms(2))+

section "Induce S Precondition"

lemma s_perm_pre_established:
  assumes "valid_list T"
  and     "strict_mono \<alpha>"
  and     "\<alpha> bot = 0"
  and     "Suc 0 < length T"
  and     "lms_pre \<alpha> T B0 SA0 (rev LMS)"
  and     "SA1 = abs_bucket_insert \<alpha> T B0 SA0 (rev LMS)"
  and     "l_perm_pre \<alpha> T B1 SA1"
shows "s_perm_pre \<alpha> T ((bucket_ends \<alpha> T)[0 := 0]) (abs_induce_l \<alpha> T B1 SA1) (length T)"
      (is "s_perm_pre \<alpha> T ?B ?SA ?n")
  unfolding s_perm_pre_def
proof (intro conjI)
  from s_bucket_init_map_bucket_end[of \<alpha> T]
  show "s_bucket_init \<alpha> T ?B" .
next
  from valid_list_length_ex[OF assms(1)]
  obtain n where
    "length T = Suc n"
    by blast
  hence "\<exists>m. length T = Suc (Suc m)"
    using assms(4) old.nat.exhaust by auto
  then obtain m where
    "length T = Suc (Suc m)"
    by blast

  from abs_bucket_insert_bot_first[OF assms(5,1) `length T = Suc (Suc m)` assms(3)]
  have "SA1 ! 0 = n"
    using \<open>length T = Suc (Suc m)\<close> \<open>length T = Suc n\<close> assms(6) by auto

  have "0 \<le> \<alpha> (Max (set T))"
    by simp
  moreover
  have "s_bucket_start \<alpha> T 0 \<le> 0"
    by (simp add: assms(1-3) valid_list_s_bucket_start_0)
  moreover
  have "0 < bucket_end \<alpha> T 0"
    by (simp add: assms(1-3) valid_list_bucket_end_0)
  ultimately have "?SA ! 0 = SA1 ! 0"
    using abs_induce_l_unchanged[OF `l_perm_pre _ _ _ _`, of 0 0]
    by blast
  with `SA1 ! 0 = n`
  have "?SA ! 0 = n"
    by simp
  with `length T = Suc n`
  show "s_type_init T ?SA"
    using s_type_init_def by blast
next
  show "length ?SA = length T"
    by (metis abs_induce_l_length assms(7) l_perm_pre_elims(7))
next
  from abs_induce_l_distinct_l_bucket[OF assms(7)]
       abs_induce_l_list_slice_l_bucket[OF assms(7)]
  show "l_types_init \<alpha> T ?SA"
    by (simp add: l_types_init_def)
qed(force simp: assms)+

section "Permutation"

lemma abs_sa_induce_permutation:
  assumes "set LMS = {i. abs_is_lms T i}"
  and     "distinct LMS"
  and     "valid_list T"
  and     "strict_mono \<alpha>"
  and     "\<alpha> bot = 0"
  and     "Suc 0 < length T"
shows "abs_sa_induce \<alpha> T LMS <~~> [0..< length T]"
proof -
  let ?B0 = "map (bucket_end \<alpha> T) [0..<Suc (\<alpha> (Max (set T)))]" and
      ?B1 = "map (bucket_start \<alpha> T) [0..<Suc (\<alpha> (Max (set T)))]" and
      ?SA0 = "replicate (length T) (length T)"

  let ?B2 = "?B0[0 := 0]"
  let ?SA1 = "abs_bucket_insert \<alpha> T ?B0 ?SA0 (rev LMS)"
  let ?SA2 = "abs_induce_l \<alpha> T ?B1 ?SA1"
  let ?SA3 = "abs_induce_s \<alpha> T (?B0[0 := 0]) ?SA2"

  from lms_pre_established[OF assms(1,2,4)]
  have "lms_pre \<alpha> T ?B0 ?SA0 (rev LMS)" .

  have "l_perm_pre \<alpha> T ?B1 ?SA1"
    using \<open>lms_pre \<alpha> T ?B0 ?SA0 (rev LMS)\<close> assms(3,4) l_perm_pre_established by blast

  have "s_perm_pre \<alpha> T ?B2 ?SA2 (length T)"
    using \<open>l_perm_pre \<alpha> T ?B1 ?SA1\<close> \<open>lms_pre \<alpha> T ?B0 ?SA0 (rev LMS)\<close> assms(3-6)
          s_perm_pre_established by blast
  with abs_induce_s_perm[of \<alpha> T "?B0[0 := 0]" ?SA2]
  have "?SA3 <~~> [0..< length T]"
    by blast
  then show ?thesis
    by (metis abs_sa_induce_def)
qed

(*
subsection "Permutation Properties"

lemma abs_sa_induce_distinct:
  assumes "set LMS = {i. abs_is_lms T i}"
  and     "distinct LMS"
  and     "valid_list T"
  and     "strict_mono \<alpha>"
  and     "\<alpha> bot = 0"
  and     "Suc 0 < length T"
shows "distinct (abs_sa_induce \<alpha> T LMS)"
  using abs_sa_induce_permutation[OF assms] perm_distinct_set_of_upt_iff by blast

lemma abs_sa_induce_length:
shows "length (abs_sa_induce \<alpha> T LMS) = length T"
proof -
  let ?B0 = "map (bucket_end \<alpha> T) [0..<Suc (\<alpha> (Max (set T)))]" and
      ?B1 = "map (bucket_start \<alpha> T) [0..<Suc (\<alpha> (Max (set T)))]" and
      ?SA0 = "replicate (length T) (length T)"

  let ?SA1 = "abs_bucket_insert \<alpha> T ?B0 ?SA0 (rev LMS)"
  let ?SA2 = "abs_induce_l \<alpha> T ?B1 ?SA1"

  have "length ?SA0 = length T"
    by simp
  hence "length ?SA1 = length T"
    by (simp add: abs_bucket_insert_length)
  hence "length ?SA2 = length T"
    by (simp add: abs_induce_l_length)
  then show ?thesis
    unfolding abs_sa_induce_def
    by (metis abs_induce_s_length)
qed

lemma abs_sa_induce_nth_le_length:
  assumes "set LMS = {i. abs_is_lms T i}"
  and     "distinct LMS"
  and     "valid_list T"
  and     "strict_mono \<alpha>"
  and     "\<alpha> bot = 0"
  and     "Suc 0 < length T"
  and     "i < length T"
shows "(abs_sa_induce \<alpha> T LMS) ! i < length T"
  using abs_sa_induce_permutation[OF assms(1-6)] perm_distinct_set_of_upt_iff
  by (metis assms(7) atLeastLessThan_iff nth_mem abs_sa_induce_length)

lemma set_sa_induce_eq_upt_length_T:
  "\<lbrakk>set LMS = {i. abs_is_lms T i}; distinct LMS; valid_list T; strict_mono \<alpha>; \<alpha> bot = 0;
    Suc 0 < length T\<rbrakk> \<Longrightarrow>
    set (abs_sa_induce \<alpha> T LMS) = {0..<length T}"
  by (metis (no_types, lifting) perm_set_eq abs_sa_induce_permutation set_upt)

lemma set_sa_induce_el_less_length:
  "\<lbrakk>set LMS = {i. abs_is_lms T i}; distinct LMS; valid_list T; strict_mono \<alpha>; \<alpha> bot = 0;
    Suc 0 < length T\<rbrakk> \<Longrightarrow>
    \<forall>x \<in> set (abs_sa_induce \<alpha> T LMS). x < length T"
  by (simp add: set_sa_induce_eq_upt_length_T)

lemma abs_sa_induce_distinct_suffixes:
  assumes "set LMS = {i. abs_is_lms T i}"
  and     "distinct LMS"
  and     "valid_list T"
  and     "strict_mono \<alpha>"
  and     "\<alpha> bot = 0"
  and     "Suc 0 < length T"
shows "distinct (map (suffix T) (abs_sa_induce \<alpha> T LMS))"
  by (simp add: distinct_suffixes assms abs_sa_induce_distinct set_sa_induce_eq_upt_length_T)
*)

section "Sorting"

 \<comment>\<open> Used in SAIS algorithm to induce the suffix ordering based on LMS \<close>
lemma abs_sa_induce_suffix_sorted:
  assumes "set LMS = {i. abs_is_lms T i}"
  and     "distinct LMS"
  and     "valid_list T"
  and     "strict_mono \<alpha>"
  and     "\<alpha> bot = 0"
  and     "Suc 0 < length T"
  and     "ordlistns.sorted (map (suffix T) LMS)"
shows "ordlistns.sorted (map (suffix T) (abs_sa_induce \<alpha> T LMS))"
proof -
  let ?B0 = "map (bucket_end \<alpha> T) [0..<Suc (\<alpha> (Max (set T)))]" and
      ?B1 = "map (bucket_start \<alpha> T) [0..<Suc (\<alpha> (Max (set T)))]" and
      ?SA0 = "replicate (length T) (length T)"

  let ?B2 = "?B0[0 := 0]"
  let ?SA1 = "abs_bucket_insert \<alpha> T ?B0 ?SA0 (rev LMS)"
  let ?SA2 = "abs_induce_l \<alpha> T ?B1 ?SA1"
  let ?SA3 = "abs_induce_s \<alpha> T (?B0[0 := 0]) ?SA2"

  from lms_pre_established[OF assms(1,2,4)]
  have "lms_pre \<alpha> T ?B0 ?SA0 (rev LMS)" .

  have P0:
    "\<forall>b \<le> \<alpha> (Max (set T)).
      ordlistns.sorted (map (suffix T)
        (list_slice ?SA1 (lms_bucket_start \<alpha> T b) (bucket_end \<alpha> T b)))"
  proof(intro allI impI)
    fix b
    assume "b \<le> \<alpha> (Max (set T))"
    from lms_suffix_sorted_bucket[OF `lms_pre _ _ _ _ _` _ `b \<le> _`] assms(7)
    show "ordlistns.sorted (map (suffix T)
            (list_slice ?SA1 (lms_bucket_start \<alpha> T b) (bucket_end \<alpha> T b)))"
      by simp
  qed

  have "l_perm_pre \<alpha> T ?B1 ?SA1"
    using \<open>lms_pre \<alpha> T ?B0 ?SA0 (rev LMS)\<close> assms(3,4) l_perm_pre_established by blast
  moreover
  have "l_suffix_sorted_pre \<alpha> T ?SA1"
    using P0 l_suffix_sorted_pre_def by blast
  ultimately have P1:
    "\<forall>b \<le> \<alpha> (Max (set T)).
      ordlistns.sorted (map (suffix T) (list_slice ?SA2 (bucket_start \<alpha> T b) (l_bucket_end \<alpha> T b)))"
    using abs_induce_l_suffix_sorted_l_bucket by blast

  have "s_perm_pre \<alpha> T ?B2 ?SA2 (length T)"
    using \<open>l_perm_pre \<alpha> T ?B1 ?SA1\<close> \<open>lms_pre \<alpha> T ?B0 ?SA0 (rev LMS)\<close> assms(3-6)
          s_perm_pre_established by blast
  moreover
  have "s_sorted_pre \<alpha> T ?SA2"
    using P1 s_sorted_pre_def by blast
  ultimately show ?thesis
    by (metis abs_induce_s_sorted abs_sa_induce_def)
qed

 \<comment>\<open> Used in SAIS algorithm to induce the prefix ordering based on LMS \<close>

theorem abs_sa_induce_prefix_sorted:
  assumes "set LMS = {i. abs_is_lms T i}"
  and     "distinct LMS"
  and     "valid_list T"
  and     "strict_mono \<alpha>"
  and     "\<alpha> bot = 0"
  and     "Suc 0 < length T"
shows "ordlistns.sorted (map (lms_slice T) (abs_sa_induce \<alpha> T LMS))"
proof -
  let ?B0 = "map (bucket_end \<alpha> T) [0..<Suc (\<alpha> (Max (set T)))]" and
      ?B1 = "map (bucket_start \<alpha> T) [0..<Suc (\<alpha> (Max (set T)))]" and
      ?SA0 = "replicate (length T) (length T)"

  let ?B2 = "?B0[0 := 0]"
  let ?SA1 = "abs_bucket_insert \<alpha> T ?B0 ?SA0 (rev LMS)"
  let ?SA2 = "abs_induce_l \<alpha> T ?B1 ?SA1"
  let ?SA3 = "abs_induce_s \<alpha> T (?B0[0 := 0]) ?SA2"

  from lms_pre_established[OF assms(1,2,4)]
  have "lms_pre \<alpha> T ?B0 ?SA0 (rev LMS)" .

  have P0:
    "\<forall>b \<le> \<alpha> (Max (set T)).
      ordlistns.sorted (map (lms_prefix T)
        (list_slice ?SA1 (lms_bucket_start \<alpha> T b) (bucket_end \<alpha> T b)))"
  proof(intro allI impI)
    fix b
    assume "b \<le> \<alpha> (Max (set T))"
    from lms_prefix_sorted_bucket[OF `lms_pre _ _ _ _ _` `b \<le> _`]
    show "ordlistns.sorted (map (lms_prefix T)
            (list_slice ?SA1 (lms_bucket_start \<alpha> T b) (bucket_end \<alpha> T b)))"
      by simp
  qed

  have "l_perm_pre \<alpha> T ?B1 ?SA1"
    using \<open>lms_pre \<alpha> T ?B0 ?SA0 (rev LMS)\<close> assms(3,4) l_perm_pre_established by blast
  moreover
  have "l_prefix_sorted_pre \<alpha> T ?SA1"
    using P0 l_prefix_sorted_pre_def by blast
  ultimately have P1:
    "\<forall>b \<le> \<alpha> (Max (set T)).
      ordlistns.sorted (map (lms_prefix T)
        (list_slice ?SA2 (bucket_start \<alpha> T b) (l_bucket_end \<alpha> T b)))"
    using abs_induce_l_prefix_sorted_l_bucket by blast

  have P2:
    "\<forall>b \<le> \<alpha> (Max (set T)).
      ordlistns.sorted (map (lms_slice T)
        (list_slice ?SA2 (bucket_start \<alpha> T b) (l_bucket_end \<alpha> T b)))"
  proof (intro allI impI sorted_wrt_mapI)
    fix b i j

    let ?xs = "list_slice ?SA2 (bucket_start \<alpha> T b) (l_bucket_end \<alpha> T b)" and
        ?R1 = "(\<lambda>x y. list_less_eq_ns (lms_prefix T x) (lms_prefix T y))" and
        ?R2 = "(\<lambda>x y. list_less_eq_ns (lms_slice T x) (lms_slice T y))"

    assume "b \<le> \<alpha> (Max (set T))" "i < j" "j < length ?xs"
    with P1
    have "ordlistns.sorted (map (lms_prefix T) ?xs)"
      by blast
    with sorted_wrt_mapD[OF _ \<open>i < j\<close> \<open>j < length ?xs\<close>]
    have "list_less_eq_ns (lms_prefix T (?xs ! i)) (lms_prefix T (?xs ! j))"
      by blast
    moreover
    from abs_induce_l_list_slice_l_bucket[OF `l_perm_pre _ _ _ _` `b \<le> _`]
    have "?xs ! i \<in> l_bucket \<alpha> T b"
      using Suc_lessD \<open>i < j\<close> \<open>j < length ?xs\<close> less_trans_Suc nth_mem by blast
    hence "suffix_type T (?xs ! i) = L_type"
      using l_bucket_def bucket_def by blast
    hence "lms_prefix T (?xs ! i) = lms_slice T (?xs ! i)"
      by (metis SL_types.distinct(1) abs_is_lms_def not_lms_imp_next_eq_lms_prefix)
    moreover
    from abs_induce_l_list_slice_l_bucket[OF `l_perm_pre _ _ _ _` `b \<le> _`]
    have "?xs ! j \<in> l_bucket \<alpha> T b"
      using \<open>j < length ?xs\<close> less_trans_Suc nth_mem by blast
    hence "suffix_type T (?xs ! j) = L_type"
      using l_bucket_def bucket_def by blast
    hence "lms_prefix T (?xs ! j) = lms_slice T (?xs ! j)"
      by (metis SL_types.distinct(1) abs_is_lms_def not_lms_imp_next_eq_lms_prefix)
    ultimately show "list_less_eq_ns (lms_slice T (?xs ! i)) (lms_slice T (?xs ! j))"
      by order
  qed

  have "s_perm_pre \<alpha> T ?B2 ?SA2 (length T)"
    using \<open>l_perm_pre \<alpha> T ?B1 ?SA1\<close> \<open>lms_pre \<alpha> T ?B0 ?SA0 (rev LMS)\<close> assms(3-6)
          s_perm_pre_established by blast
  moreover
  have "s_prefix_sorted_pre \<alpha> T ?SA2"
    using P2 s_prefix_sorted_pre_def by blast
  ultimately show ?thesis
    by (metis abs_induce_s_prefix_sorted abs_sa_induce_def)
qed

(*
subsection "Sorting Properties"

lemma abs_sa_induce_suffix_lms_sublist_first_item:
  assumes "set LMS = {i. abs_is_lms T i}"
  and     "distinct LMS"
  and     "valid_list T"
  and     "length T = Suc n"
  and     "strict_mono \<alpha>"
  and     "\<alpha> bot = 0"
  and     "Suc 0 < length T"
shows "abs_sa_induce \<alpha> T LMS ! 0 = n"
proof -

  note H = set_sa_induce_eq_upt_length_T[OF assms(1-3,5-)]

  from abs_sa_induce_prefix_sorted[where \<alpha> = \<alpha>, OF assms(1-3,5-7)]
  have A: "ordlistns.sorted (map (lms_slice T) (abs_sa_induce \<alpha> T LMS))"
    by assumption

  from assms(4) H
  have B: "n \<in> set (abs_sa_induce \<alpha> T LMS)"
    by simp

  have C: "\<forall>i < n. list_less_ns (lms_slice T n) (lms_slice T i)"
  proof (intro allI impI)
    fix i
    assume "i < n"
    from ordlistns.Min_eq_iff[THEN iffD1, OF _ _ Min_valid_lms_slice[OF assms(3-4)]]
    have "(\<forall>a\<in>{lms_slice T i |i. i < length T}. list_less_eq_ns (lms_slice T n) a)"
      using assms(4) by auto
    with `i < n` assms(4)
    have "list_less_eq_ns (lms_slice T n) (lms_slice T i)"
      by (metis (mono_tags, lifting) less_SucI mem_Collect_eq)
    with unique_valid_lms_slice[OF assms(3-4)] `i < n`
    show "list_less_ns (lms_slice T n) (lms_slice T i)"
      by (simp add: ordlistns.dual_order.not_eq_order_implies_strict)
  qed

  from A
  have "\<forall>i < length (abs_sa_induce \<alpha> T LMS).
          list_less_eq_ns (lms_slice T ((abs_sa_induce \<alpha> T LMS) ! 0))
            (lms_slice T ((abs_sa_induce \<alpha> T LMS) ! i))"
    using ordlistns.sorted_nth_mono by fastforce

  from ordlistns.sorted_find_Min[OF A, of "(\<lambda>_. True)", simplified]
  have D: "lms_slice T ((abs_sa_induce \<alpha> T LMS) ! 0) =
            ordlistns.Min (lms_slice T ` set (abs_sa_induce \<alpha> T LMS))"
    by (metis B find_Some_iff length_pos_if_in_set less_Suc0 list.size(3) not_less_eq nth_map)

  have "lms_slice T ` set (abs_sa_induce \<alpha> T LMS) = {lms_slice T i |i. i < length T}"
  proof (intro equalityI subsetI)
    fix x
    assume A0: "x \<in> lms_slice T ` set (abs_sa_induce \<alpha> T LMS)"
    from image_iff[THEN iffD1, OF A0]
    obtain i where
      "i \<in> set (abs_sa_induce \<alpha> T LMS)"
      "x = lms_slice T i"
      by blast
    with set_sa_induce_el_less_length[OF assms(1-3,5-)]
    show "x \<in> {lms_slice T i |i. i < length T}"
      by blast
  next
    fix x
    assume A0: "x \<in> {lms_slice T i |i. i < length T}"
    show  "x \<in> lms_slice T ` set (abs_sa_induce \<alpha> T LMS)"
      using H A0 atLeastLessThan_iff by blast
  qed
  with Min_valid_lms_slice[OF assms(3-4)] unique_valid_lms_slice[OF assms(3-4)]
       assms H B C D
  show ?thesis
    by (metis (no_types, lifting) atLeastLessThan_iff length_pos_if_in_set less_SucE nth_mem)
qed
*)
end