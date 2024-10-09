theory Suffix_Util
  imports 
    "../util/List_Slice"
    Suffix
    Valid_List
    Valid_List_Util

begin

section \<open>Valid Lists and Suffixes\<close>

lemma valid_suffix:
  "\<lbrakk>valid_list s; i < length s\<rbrakk> \<Longrightarrow> valid_list (suffix s i)"
  by (clarsimp simp: valid_list_ex_def)

lemma last_suffix_index:
  assumes "valid_list s"
  and     "i < length s"
  shows "hd (suffix s i) = bot \<longleftrightarrow> i = length s - 1"
proof -
  from iffD1[OF valid_list_ex_def `valid_list s`]
  obtain xs where
    "s = xs @ [bot]"
    "\<forall>i < length xs. xs ! i \<noteq> bot"
    by blast
  show ?thesis
  proof
    from \<open>s = xs @ [bot]\<close> \<open>\<forall>i < length xs. xs ! i \<noteq> bot\<close>
    show "i = length s - 1 \<Longrightarrow> hd (suffix s i) = bot"
      by simp
  next
    from \<open>s = xs @ [bot]\<close> \<open>\<forall>i < length xs. xs ! i \<noteq> bot\<close> \<open>i < length s\<close>
    show "hd (suffix s i) = bot \<Longrightarrow> i = length s - 1"
      by (clarsimp simp: hd_append hd_drop_conv_nth split: if_splits)
  qed
qed

section \<open>Prefixes and Suffixes\<close>

lemma suffix_has_no_prefix_suffix:
  assumes valid_list: "valid_list s"
  and     i_less_len_s:  "i < length s"
  and     j_less_len_s:  "j < length s"
  and     i_neq_j:       "i \<noteq> j"
  shows "\<not> (\<exists>s'. suffix s i = (suffix s j) @ s')"
proof
  assume "\<exists>s'. suffix s i = suffix s j @ s'"
  then obtain s' where
    pref: "suffix s i = suffix s j @ s'"
    by blast
  with i_neq_j i_less_len_s j_less_len_s
  have "i < j"
    by (metis diff_less_mono2 length_append length_drop less_Suc_eq not_add_less1
          not_less_eq)
  with pref i_less_len_s j_less_len_s
    have s_not_nil: "s' \<noteq> []"
    by (metis append_Nil2 diff_less_mono2 length_drop less_irrefl_nat)

  from valid_list i_less_len_s valid_suffix
  have valid_suf_i: "valid_list (suffix s i)"
    by force

  from valid_list j_less_len_s valid_suffix
  have "valid_list (suffix s j)"
    by force
  with pref valid_list_ex_def
  have "\<exists>xs. suffix s i = xs @ [bot] @ s'"
    using append_assoc by auto
  then obtain xs where
    suf_i: "suffix s i = xs @ [bot] @ s'"
    by blast

  from valid_suf_i valid_list_ex_def
  have "\<exists>ys. suffix s i = ys @ [bot] \<and> (\<forall>k < length ys. ys ! k \<noteq> bot)"
    by blast
  then obtain ys where
                  "suffix s i = ys @ [bot]" and
    all_ys_not_0: "\<forall>k < length ys. ys ! k \<noteq> bot"
    by blast
  with suf_i
  have suf_i_eq: "xs @ [bot] @ s' = ys @ [bot]"
    by force
  with s_not_nil
  have "length xs < length ys"
    by (metis (no_types, lifting) append_assoc append_eq_append_conv 
              length_append length_append_singleton less_trans_Suc 
              linorder_neqE_nat not_add_less1 self_append_conv)
  with suf_i_eq all_ys_not_0
  show "False"
    by (metis append_Cons butlast_snoc nth_append_length nth_butlast)
qed


section \<open>Suffix Comparisons\<close>

subsection \<open>Lexicographical Ordering\<close>

lemma suffix_less_ex:
  fixes s :: "('a :: {linorder, order_bot}) list"
  assumes "valid_list s"
  and     "i < length s"
  and     "j < length s"
  and     "suffix s i < suffix s j"
  shows "\<exists>b c as bs cs. suffix s i = as @ b # bs \<and> 
                      suffix s j = as @ c # cs \<and> b < c"
proof -
  have "valid_list (suffix s i)"
    using assms(1) assms(2) valid_suffix by blast
  moreover
  have "valid_list (suffix s j)"
    using assms(1) assms(3) valid_suffix by blast
  moreover
  have "suffix s i \<noteq> suffix s j"
    using assms(4) nless_le by blast
  ultimately have
    "\<exists>b c as bs cs. suffix s i = as @ b # bs \<and> suffix s j = as @ c # cs \<and> b \<noteq> c"
    using valid_list_neqE by blast
  then obtain b c as bs cs where
    "suffix s i = as @ b # bs" "suffix s j = as @ c # cs" "b \<noteq> c"
    by blast
  hence "b < c"
    by (metis assms(4) linorder_less_linear list_less_ex order_less_imp_not_less)
  then show ?thesis
    using \<open>suffix s i = as @ b # bs\<close> \<open>suffix s j = as @ c # cs\<close> by blast
qed

lemma suffix_less_nth:
  assumes "valid_list s"
  and     "i < length s"
  and     "j < length s"
  and     "suffix s i < suffix s j"
  shows
  "\<exists>n. n < length (suffix s i) \<and>
       n < length (suffix s j) \<and>
       (\<forall>k < n. (suffix s i) ! k = (suffix s j) ! k) \<and>
                (suffix s i) ! n < (suffix s j) ! n"
proof -
  from suffix_less_ex[OF assms]
  obtain b c as bs cs where
    suf_i:    "suffix s i = as @ b # bs" and
    suf_j:    "suffix s j = as @ c # cs" and
    b_less_c: "b < c"
    by blast
  hence "length as < length (suffix s i)" and
        "length as < length (suffix s j)" and
        "(suffix s i) ! length as = b"    and
        "(suffix s j) ! length as = c"
    by fastforce+
  with b_less_c suf_i suf_j
  show ?thesis
    by (metis nth_append)
qed

lemma suffix_less_butlast:
 assumes "valid_list s"
  and    "i < length s"
  and    "j < length s"
  and    "suffix s i < suffix s j"
  shows "butlast (suffix s i) < butlast (suffix s j)"
  by (metis append_butlast_last_id assms suffix_neq_nil valid_list_def valid_list_list_less_imp
            valid_suffix)

subsection \<open>Non-standard List Ordering\<close>

lemma suffix_less_ns_ex:
  assumes "valid_list s"
  and     "i < length s"
  and     "j < length s"
  and     "list_less_ns (suffix s i) (suffix s j)"
  shows "\<exists>b c as bs cs. 
          suffix s i = as @ b # bs \<and> 
          suffix s j = as @ c # cs \<and> b < c"
  by (meson assms suffix_less_ex valid_suffix
      valid_list_list_less_equiv_list_less_ns)


lemma suffix_less_ns_nth:
  assumes "valid_list s"
  and     "i < length s"
  and     "j < length s"
  and     "list_less_ns (suffix s i) (suffix s j)"
  shows
  "\<exists>n. n < length (suffix s i) \<and>
       n < length (suffix s j) \<and>
       (\<forall>k < n. (suffix s i) ! k = (suffix s j) ! k) \<and>
       (suffix s i) ! n < (suffix s j) ! n"
  by (meson assms suffix_less_nth valid_list_list_less_equiv_list_less_ns valid_suffix)

section \<open>List Slice\<close>

declare list_slice.simps[simp del]

lemma list_slice_to_suffix:
  "list_slice T i j = take (j - i) (suffix T i)"
  by (simp add: list_slice.simps drop_take)

lemma suffix_eq_list_slice:
  "suffix T i = list_slice T i (length T)"
  by (simp add: list_slice.simps)

lemma list_slice_suffix:
  "list_slice T i j = list_slice (suffix T i) 0 (j - i)"
  by (metis drop0 drop_take list_slice.simps)
lemma suffix_to_list_slice_app:
  "i \<le> j \<Longrightarrow> suffix T i = (list_slice T i j) @ (list_slice T j (length T))"
  apply (cases "j \<le> length T")
   apply (subst list_slice_append[symmetric]; simp?)
   apply (clarsimp simp: list_slice.simps)
  apply (clarsimp simp: not_le)
  apply (subst list_slice_end_gre_length, arith)
  apply (simp add: list_slice_start_gre_length list_slice.simps)
  done

section \<open>Sorting\<close>

lemma ordlist_strict_mono_strict_sorted_1:
  assumes "strict_mono \<alpha>"
  and     "strict_sorted (map (suffix (map \<alpha> s)) xs)"
  shows "strict_sorted (map (suffix s) xs)"
proof (intro sorted_wrt_mapI)
  fix i j
  assume "i < j" "j < length xs"
  with sorted_wrt_nth_less[OF assms(2)]
  have "suffix (map \<alpha> s) (xs ! i) < suffix (map \<alpha> s) (xs ! j)"
    by auto
  then show "suffix s (xs ! i) < suffix s (xs ! j)"
    by (metis assms(1) strict_mono_map_list_less suffix_map)
qed

lemma ordlist_strict_mono_on_strict_sorted_1:
  assumes "strict_mono_on A \<alpha>"
  and     "set s \<subseteq> A"
  and     "strict_sorted (map (suffix (map \<alpha> s)) xs)"
  shows "strict_sorted (map (suffix s) xs)"
proof (intro sorted_wrt_mapI)
  fix i j
  assume "i < j" "j < length xs"
  with sorted_wrt_nth_less[OF assms(3)]
  have "suffix (map \<alpha> s) (xs ! i) < suffix (map \<alpha> s) (xs ! j)"
    by auto
  hence "map \<alpha> (suffix s (xs ! i)) < map \<alpha> (suffix s (xs ! j))"
    by (metis suffix_map)
  then show "suffix s (xs ! i) < suffix s (xs ! j)"
    by (meson assms(1,2) dual_order.trans set_suffix_subset 
              strict_mono_on_map_list_less)
qed

lemma ordlist_strict_mono_strict_sorted_2:
  assumes "strict_mono \<alpha>"
  and     "strict_sorted (map (suffix s) xs)"
  shows "strict_sorted (map (suffix (map \<alpha> s)) xs)"
proof (intro sorted_wrt_mapI)
  fix i j
  assume "i < j" "j < length xs"
  with sorted_wrt_nth_less[OF assms(2)]
  have "suffix s (xs ! i) < suffix s (xs ! j)"
    by auto
  then show "suffix (map \<alpha> s) (xs ! i) < suffix (map \<alpha> s) (xs ! j)"
    by (metis assms(1) strict_mono_list_less_map suffix_map)
qed

lemma ordlist_strict_mono_on_strict_sorted_2:
  assumes "strict_mono_on A \<alpha>"
  and     "set s \<subseteq> A"
  and     "strict_sorted (map (suffix s) xs)"
  shows "strict_sorted (map (suffix (map \<alpha> s)) xs)"
proof (intro sorted_wrt_mapI)
  fix i j
  assume "i < j" "j < length xs"
  with sorted_wrt_nth_less[OF assms(3)]
  have "suffix s (xs ! i) < suffix s (xs ! j)"
    by auto
  moreover
  have "set (suffix s (xs ! i)) \<subseteq> A"
    by (meson assms(2) dual_order.trans set_suffix_subset)
  moreover
  have "set (suffix s (xs ! j)) \<subseteq> A"
    by (meson assms(2) dual_order.trans set_suffix_subset)
  ultimately show "suffix (map \<alpha> s) (xs ! i) < suffix (map \<alpha> s) (xs ! j)"
    using strict_mono_on_list_less_map[OF assms(1)]
    by (metis suffix_map)
qed

lemma valid_list_ordlist_ordlistns_strict_sorted_eq:
  assumes "valid_list T"
  and     "set xs \<subseteq> {0..<length T}"
  shows "ordlistns.strict_sorted (map (suffix T) xs) \<longleftrightarrow> 
         strict_sorted (map (suffix T) xs)"
using assms
proof (safe) 
  assume A: "valid_list T" and
         B: "set xs \<subseteq> {0..<length T}" and
         C: "sorted_wrt list_less_ns (map (suffix T) xs)"
  show "sorted_wrt (<) (map (suffix T) xs)"
  proof (intro sorted_wrt_mapI)
    fix i j
    assume "i < j" "j < length xs"
    with sorted_wrt_nth_less[OF C \<open>i < j\<close>]
    have R1: "list_less_ns (suffix T (xs ! i)) (suffix T (xs ! j))"
      by auto

    from B \<open>i < j\<close> \<open>j < length xs\<close>
    have "xs ! i < length T"
      by (meson atLeastLessThan_iff less_trans nth_mem subsetD)
    with valid_suffix[OF A]
    have R2: "valid_list (suffix T (xs ! i))"
      by simp

    from B \<open>j < length xs\<close>
    have "xs ! j < length T"
      by (meson atLeastLessThan_iff less_trans nth_mem subsetD)
    with valid_suffix[OF A]
    have R3: "valid_list (suffix T (xs ! j))"
      by simp

    from R1 valid_list_list_less_equiv_list_less_ns[OF R2 R3]
    show "suffix T (xs ! i) < suffix T (xs ! j)"
      by simp
  qed
next
  assume A: "valid_list T" and
         B: "set xs \<subseteq> {0..<length T}" and
         C: "sorted_wrt (<) (map (suffix T) xs)"
  show "sorted_wrt list_less_ns (map (suffix T) xs)"
  proof (intro sorted_wrt_mapI)
    fix i j
    assume "i < j" "j < length xs"
    with sorted_wrt_nth_less[OF C \<open>i < j\<close>]
    have R1: "suffix T (xs ! i) < suffix T (xs ! j)"
      by auto

    from B \<open>i < j\<close> \<open>j < length xs\<close>
    have "xs ! i < length T"
      by (meson atLeastLessThan_iff less_trans nth_mem subsetD)
    with valid_suffix[OF A]
    have R2: "valid_list (suffix T (xs ! i))"
      by simp

    from B \<open>j < length xs\<close>
    have "xs ! j < length T"
      by (meson atLeastLessThan_iff less_trans nth_mem subsetD)
    with valid_suffix[OF A]
    have R3: "valid_list (suffix T (xs ! j))"
      by simp

    from R1 valid_list_list_less_equiv_list_less_ns[OF R2 R3]
    show "list_less_ns (suffix T (xs ! i)) (suffix T (xs ! j))"
      by simp
  qed
qed

lemma Min_valid_suffix:
  assumes "valid_list T"
  and     "length T = Suc n"
shows "ordlistns.Min {suffix T i |i. i < length T} = suffix T n"
proof -
  from assms
  have "suffix T n = [bot]"
    by (metis add_diff_cancel_left' butlast_snoc length_butlast lessI list_slice_n_n
          nth_append_length plus_1_eq_Suc suffix_cons_Suc suffix_eq_list_slice valid_list_ex_def)

  have "\<forall>i < n. (suffix T i) ! 0 \<noteq> bot"
    by (metis add_diff_cancel_left' assms last_suffix_index less_SucI list.sel(1) nat_neq_iff
          nth_Cons_0 plus_1_eq_Suc suffix_cons_Suc)
  hence A: "\<forall>i < n. bot < (suffix T i) ! 0"
    using bot.not_eq_extremum by blast

  have B: "\<forall>i < length T. length (suffix T i) > 0"
    by auto

  show ?thesis
  proof (intro ordlistns.Min_eqI conjI)
    show "finite {suffix T i |i. i < length T}"
      by simp
  next
    fix ys
    assume "ys \<in> {suffix T i |i. i < length T}"
    hence "\<exists>i < length T. ys = suffix T i"
      by blast
    then obtain i where
      "i < length T"
      "ys = suffix T i"
      by blast

    with \<open>ys = suffix T i\<close>
    have R1: "i = n \<Longrightarrow> list_less_eq_ns (suffix T n) ys"
      by simp

    from \<open>i < length T\<close> assms(2)
    have R2_1: "i \<noteq> n \<Longrightarrow> i < n"
      by linarith

    from A \<open>suffix T n = [bot]\<close> \<open>i < length T\<close> \<open>ys = suffix T i\<close>
    have R2_2: "i < n \<Longrightarrow> list_less_eq_ns (suffix T n) ys"
      by (metis list_less_ns_cons_diff nth_Cons_0 ordlistns.less_imp_le suffix_cons_ex)

    from R1 R2_2[OF R2_1]
    show "list_less_eq_ns (suffix T n) ys"
      by blast
  next
    show "suffix T n \<in> {suffix T i |i. i < length T}"
      using assms(2) by auto
  qed
qed

end