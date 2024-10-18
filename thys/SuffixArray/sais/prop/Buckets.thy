theory Buckets
  imports 
    "../../util/Continuous_Interval" 
    List_Type
begin
section \<open>Buckets\<close>

subsection \<open>Entire Bucket\<close>

definition bucket :: "('a :: {linorder,order_bot} \<Rightarrow> nat) \<Rightarrow> 'a list \<Rightarrow> nat \<Rightarrow> nat set"
  where
"bucket \<alpha> T b \<equiv> {k |k. k < length T \<and> \<alpha> (T ! k) = b}"

definition bucket_size :: "('a :: {linorder,order_bot} \<Rightarrow> nat) \<Rightarrow> 'a list \<Rightarrow> nat \<Rightarrow> nat"
  where
"bucket_size \<alpha> T b \<equiv> card (bucket \<alpha> T b)"

definition bucket_upt :: "('a :: {linorder,order_bot} \<Rightarrow> nat) \<Rightarrow> 'a list \<Rightarrow> nat \<Rightarrow> nat set"
  where
"bucket_upt \<alpha> T b = {k |k. k < length T \<and> \<alpha> (T ! k) < b}"

definition bucket_start :: "('a :: {linorder,order_bot} \<Rightarrow> nat) \<Rightarrow> 'a list \<Rightarrow> nat \<Rightarrow> nat"
  where
"bucket_start \<alpha> T b \<equiv> card (bucket_upt \<alpha> T b)"

definition bucket_end :: "('a :: {linorder,order_bot} \<Rightarrow> nat) \<Rightarrow> 'a list \<Rightarrow> nat \<Rightarrow> nat"
  where
"bucket_end \<alpha> T b \<equiv> card (bucket_upt \<alpha> T (Suc b))"

lemma bucket_upt_subset:
  "bucket_upt \<alpha> T b \<subseteq> {0..<length T}"
  by (rule subsetI, simp add: bucket_upt_def)

lemma bucket_upt_subset_Suc:
  "bucket_upt \<alpha> T b \<subseteq> bucket_upt \<alpha> T (Suc b)"
  by (rule subsetI, simp add: bucket_upt_def)

lemma bucket_upt_un_bucket:
  "bucket_upt \<alpha> T b \<union> bucket \<alpha> T b = bucket_upt \<alpha> T (Suc b)"
  apply (clarsimp simp: bucket_upt_def bucket_def)
  apply (intro equalityI subsetI; clarsimp)
  apply (erule disjE; clarsimp)
  done

lemma bucket_0:
  assumes "valid_list T" "\<alpha> bot = 0" "strict_mono \<alpha>" "length T = Suc k"
  shows "bucket \<alpha> T 0 = {k}"
proof safe
  fix x
  assume "x \<in> bucket \<alpha> T 0"
  then show "x = k"
    by (metis (mono_tags, lifting) assms bucket_def diff_Suc_1 le_neq_trans le_simps(2)
                                   mem_Collect_eq strict_mono_eq valid_list_def)
next
  show "k \<in> bucket \<alpha> T 0"
    by (metis (mono_tags, lifting) assms(1,2,4) bucket_def diff_Suc_1 last_conv_nth lessI
                                   list.size(3) mem_Collect_eq order_less_irrefl valid_list_def)
qed

lemma finite_bucket:
  "finite (bucket \<alpha> T x)"
  by (clarsimp simp: bucket_def)

lemma finite_bucket_upt:
  "finite (bucket_upt \<alpha> T b)"
  by (meson bucket_upt_subset subset_eq_atLeast0_lessThan_finite)

lemma bucket_start_Suc:
  "bucket_start \<alpha> T (Suc b) = bucket_start \<alpha> T b + bucket_size \<alpha> T b"
  apply (clarsimp simp: bucket_start_def bucket_size_def)
  apply (subst card_Un_disjoint[symmetric])
     apply (meson bucket_upt_subset subset_eq_atLeast0_lessThan_finite)
    apply (simp add: finite_bucket)
   apply (rule disjointI')
  apply (metis (mono_tags, lifting) bucket_def bucket_upt_def less_irrefl_nat mem_Collect_eq)
  apply (simp add: bucket_upt_un_bucket)
  done

lemma bucket_start_le:
  "b \<le> b' \<Longrightarrow> bucket_start \<alpha> T b \<le> bucket_start \<alpha> T b'"
  apply (clarsimp simp: bucket_start_def)
  by (meson bucket_upt_subset bucket_upt_subset_Suc card_mono lift_Suc_mono_le
        subset_eq_atLeast0_lessThan_finite)

lemma bucket_start_Suc_eq_bucket_end:
  "bucket_start \<alpha> T (Suc b) = bucket_end \<alpha> T b"
  by (simp add: bucket_end_def bucket_start_def)

lemma bucket_end_le_length:
  "bucket_end \<alpha> T b \<le> length T"
  apply (clarsimp simp: bucket_end_def)
  apply (insert card_mono[OF _  bucket_upt_subset[of \<alpha> T "Suc b"]])
  apply (erule meta_impE, simp)
  apply (erule order.trans)
  apply simp
  done

lemma bucket_start_le_end:
  "bucket_start \<alpha> T b \<le> bucket_end \<alpha> T b"
  by (metis Suc_n_not_le_n bucket_start_Suc_eq_bucket_end bucket_start_le nat_le_linear)

lemma le_bucket_start_le_end:
  "b \<le> b' \<Longrightarrow> bucket_start \<alpha> T b \<le> bucket_end \<alpha> T b'"
  using bucket_start_le bucket_start_le_end le_trans by blast

lemma bucket_end_le:
  "b \<le> b' \<Longrightarrow> bucket_end \<alpha> T b \<le> bucket_end \<alpha> T b'"
  by (metis bucket_start_Suc_eq_bucket_end bucket_start_le_end lift_Suc_mono_le)

lemma less_bucket_end_le_start:
  "b < b' \<Longrightarrow> bucket_end \<alpha> T b \<le> bucket_start \<alpha> T b'"
  by (metis Suc_leI bucket_start_Suc_eq_bucket_end bucket_start_le)

lemma bucket_end_def':
  "bucket_end \<alpha> T b = bucket_start \<alpha> T b + bucket_size \<alpha> T b"
  by (metis bucket_start_Suc bucket_start_Suc_eq_bucket_end)

lemma valid_list_bucket_start_0:
  "\<lbrakk>valid_list T; strict_mono \<alpha>; \<alpha> bot = 0\<rbrakk> \<Longrightarrow>
   bucket_start \<alpha> T 0 = 0"
  by (clarsimp simp: bucket_start_def bucket_upt_def)

lemma bucket_upt_0:
  "bucket_upt \<alpha> T 0 = {}"
  by (clarsimp simp: bucket_upt_def)

lemma bucket_start_0:
  "bucket_start \<alpha> T 0 = 0"
  by (clarsimp simp: bucket_start_def bucket_upt_def)

lemma valid_list_bucket_upt_Suc_0:
  "\<lbrakk>valid_list T; strict_mono \<alpha>; \<alpha> bot = 0; length T = Suc n\<rbrakk> \<Longrightarrow>
   bucket_upt \<alpha> T (Suc 0) = {n}"
  apply (clarsimp simp: bucket_upt_def)
  apply (intro equalityI subsetI)
   apply (clarsimp simp: valid_list_def)
   apply (metis less_antisym strict_mono_eq)
  apply (clarsimp simp: valid_list_ex_def)
  done

lemma valid_list_bucket_end_0:
  "\<lbrakk>valid_list T; strict_mono \<alpha>; \<alpha> bot = 0\<rbrakk> \<Longrightarrow>
   bucket_end \<alpha> T 0 = 1"
  apply (clarsimp simp: bucket_end_def)
  apply (frule valid_list_length_ex)
  apply clarsimp
  apply (frule (3) valid_list_bucket_upt_Suc_0)
  apply simp
  done

lemma nth_Max:
  "T \<noteq> [] \<Longrightarrow> \<exists>i < length T. T ! i = Max (set T)"
  by (metis List.finite_set Max_in in_set_conv_nth set_empty)

lemma bucket_upt_Suc_Max:
  "strict_mono \<alpha> \<Longrightarrow> bucket_upt \<alpha> T (Suc (\<alpha> (Max (set T)))) = {0..<length T}"
  apply (intro equalityI subsetI)
   apply (erule bucket_upt_subset[THEN subsetD])
  by (clarsimp simp: bucket_upt_def less_Suc_eq_le strict_mono_less_eq)

lemma bucket_end_Max:
  "strict_mono \<alpha> \<Longrightarrow> bucket_end \<alpha> T (\<alpha> (Max (set T))) = length T"
  apply (clarsimp simp: bucket_end_def)
  apply (drule bucket_upt_Suc_Max[where T = T])
  apply clarsimp
  done

lemma bucket_end_eq_length:
  "\<lbrakk>strict_mono \<alpha>; b \<le> \<alpha> (Max (set T)); T \<noteq> []; bucket_end \<alpha> T b = length T\<rbrakk> \<Longrightarrow>
   b = \<alpha> (Max (set T))"
proof -
  assume "strict_mono \<alpha>" "b \<le> \<alpha> (Max (set T))" "bucket_end \<alpha> T b = length T" "T \<noteq> []"
  show "b = \<alpha> (Max (set T))"
  proof (rule ccontr)
    assume "b \<noteq> \<alpha> (Max (set T))"
    with \<open>b \<le> _\<close>
    have "b < \<alpha> (Max (set T))"
      by simp
    hence "\<exists>b'. b' = \<alpha> (Max (set T))"
      by blast
    then obtain b' where
      "b' = \<alpha> (Max (set T))"
      by blast
    with \<open>b < _\<close>
    have "b < b'"
      by blast
    hence "bucket_end \<alpha> T b \<le> bucket_start \<alpha> T b'"
      by (simp add: less_bucket_end_le_start)
    moreover
    from nth_Max[OF \<open>T \<noteq> []\<close>]
    obtain i where
      "i < length T"
      "T ! i = Max (set T)"
      by blast
    with \<open>b' = \<alpha> (Max (set T))\<close> \<open>strict_mono \<alpha>\<close>
    have "i \<in> bucket \<alpha> T b'"
      by (simp add: bucket_def)
    hence "bucket_start \<alpha> T b' < bucket_end \<alpha> T b'"
      by (metis add_diff_cancel_left' bucket_end_def' bucket_size_def bucket_start_le_end
            card_gt_0_iff diff_is_0_eq' empty_iff finite_bucket nat_less_le)
    moreover
    have "bucket_end \<alpha> T b' \<le> length T"
      using bucket_end_le_length by blast
    ultimately
    show False
      using \<open>bucket_end \<alpha> T b = length T\<close>
      by linarith
  qed
qed

subsection \<open>L-types\<close>

definition l_bucket :: "('a :: {linorder,order_bot} \<Rightarrow> nat) \<Rightarrow> 'a list \<Rightarrow> nat \<Rightarrow> nat set"
  where
"l_bucket \<alpha> T b = {k |k. k \<in> bucket \<alpha> T b \<and> suffix_type T k = L_type}"

definition l_bucket_size :: "('a :: {linorder,order_bot} \<Rightarrow> nat) \<Rightarrow> 'a list \<Rightarrow> nat \<Rightarrow> nat"
  where
"l_bucket_size \<alpha> T b \<equiv> card (l_bucket \<alpha> T b)"

definition l_bucket_end :: "('a :: {linorder,order_bot} \<Rightarrow> nat) \<Rightarrow> 'a list \<Rightarrow> nat \<Rightarrow> nat"
  where
"l_bucket_end \<alpha> T b = bucket_start \<alpha> T b + l_bucket_size \<alpha> T b"

lemma l_bucket_subset_bucket:
  "l_bucket \<alpha> T b \<subseteq> bucket \<alpha> T b"
  by (rule subsetI, simp add: l_bucket_def)

lemma bucket_upt_int_l_bucket:
  "strict_mono \<alpha> \<Longrightarrow> bucket_upt \<alpha> T b \<inter> l_bucket \<alpha> T b = {}"
  apply (rule disjoint_subset2[where B = "bucket \<alpha> T b"])
   apply (simp add: l_bucket_def)
  apply (simp add: bucket_def bucket_upt_def)
  apply (rule disjointI')
  apply clarsimp
  done

lemma subset_l_bucket:
  "\<lbrakk>\<forall>k < length ls. ls ! k < length T \<and> suffix_type T (ls ! k) = L_type \<and> \<alpha> (T ! (ls ! k)) = x;
    distinct ls\<rbrakk> \<Longrightarrow>
   set ls \<subseteq> l_bucket \<alpha> T x"
  apply (rule subsetI)
  apply (clarsimp simp: l_bucket_def bucket_def in_set_conv_nth)
  done

lemma finite_l_bucket:
  "finite (l_bucket \<alpha> T x)"
  apply (clarsimp simp: finite_bucket l_bucket_def)
  done

lemma l_bucket_list_eq:
  "\<lbrakk>\<forall>k < length ls. ls ! k < length T \<and> suffix_type T (ls ! k) = L_type \<and> \<alpha> (T ! (ls ! k)) = x;
    distinct ls; length ls = l_bucket_size \<alpha> T x\<rbrakk> \<Longrightarrow>
   set ls = l_bucket \<alpha> T x"
  apply (frule (1) subset_l_bucket)
  apply (frule distinct_card)
  apply (insert finite_l_bucket[of \<alpha> T x])
  by (simp add: card_subset_eq l_bucket_size_def)

lemma l_bucket_le_bucket_size:
  "l_bucket_size \<alpha> T b \<le> bucket_size \<alpha> T b"
  apply (clarsimp simp: l_bucket_size_def bucket_size_def)
  apply (rule card_mono[OF finite_bucket l_bucket_subset_bucket])
  done

lemma l_bucket_not_empty:
  "\<lbrakk>i < length T; suffix_type T i = L_type\<rbrakk> \<Longrightarrow> 0 < l_bucket_size \<alpha> T (\<alpha> (T ! i))"
  apply (clarsimp simp: l_bucket_size_def)
  apply (subst card_gt_0_iff)
  apply (intro conjI finite_l_bucket)
  apply (clarsimp simp: l_bucket_def bucket_def)
  apply blast
  done

lemma l_bucket_end_le_bucket_end:
  "l_bucket_end \<alpha> T b \<le> bucket_end \<alpha> T b"
  apply (clarsimp simp: l_bucket_end_def)
  apply (rule order.trans[where b = "bucket_start \<alpha> T b + bucket_size \<alpha> T b"])
   apply (simp add: l_bucket_le_bucket_size)
  by (metis bucket_start_Suc bucket_start_Suc_eq_bucket_end le_refl)

lemma l_bucket_Max:
  assumes "valid_list T"
  and     "Suc 0 < length T"
  and     "strict_mono \<alpha>"
  shows "l_bucket \<alpha> T (\<alpha> (Max (set T))) = bucket \<alpha> T (\<alpha> (Max (set T)))"
proof (intro subsetI equalityI)
  let ?b = "\<alpha> (Max (set T))"
  fix x
  assume "x \<in> l_bucket \<alpha> T ?b"
  then show "x \<in> bucket \<alpha> T ?b"
    using l_bucket_subset_bucket by blast
next
  let ?b = "\<alpha> (Max (set T))"
  fix x
  assume "x \<in> bucket \<alpha> T ?b"
  hence "x < length T" "\<alpha> (T ! x) = ?b"
    using bucket_def by blast+
  with suffix_max_hd_is_l_type[OF assms(1) _ assms(2)]
  have "suffix_type T x = L_type"
    by (metis Cons_nth_drop_Suc assms(3) list.sel(1) strict_mono_eq)
  then show "x \<in> l_bucket \<alpha> T ?b"
    using \<open>x \<in> bucket \<alpha> T (\<alpha> (Max (set T)))\<close> l_bucket_def by blast
qed

subsection \<open>LMS-types\<close>

definition lms_bucket :: "('a :: {linorder,order_bot} \<Rightarrow> nat) \<Rightarrow> 'a list \<Rightarrow> nat \<Rightarrow> nat set"
  where
"lms_bucket \<alpha> T b = {k |k. k \<in> bucket \<alpha> T b \<and> abs_is_lms T k}"

definition lms_bucket_size :: "('a :: {linorder,order_bot} \<Rightarrow> nat) \<Rightarrow> 'a list \<Rightarrow> nat \<Rightarrow> nat"
  where
"lms_bucket_size \<alpha> T b \<equiv> card (lms_bucket \<alpha> T b)"

lemma lms_bucket_subset_bucket:
  "lms_bucket \<alpha> T b \<subseteq> bucket \<alpha> T b"
  by (simp add: lms_bucket_def)

lemma finite_lms_bucket:
  "finite (lms_bucket \<alpha> T b)"
  by (clarsimp simp: lms_bucket_def finite_bucket)

lemma disjoint_l_lms_bucket:
 "l_bucket \<alpha> T b \<inter> lms_bucket \<alpha> T b = {}"
  apply (rule disjointI')
  by (clarsimp simp: l_bucket_def lms_bucket_def abs_is_lms_def)

subsection \<open>S-types\<close>

definition s_bucket :: "('a :: {linorder,order_bot} \<Rightarrow> nat) \<Rightarrow> 'a list \<Rightarrow> nat \<Rightarrow> nat set"
  where
"s_bucket \<alpha> T b = {k |k. k \<in> bucket \<alpha> T b \<and> suffix_type T k = S_type}"

definition s_bucket_size :: "('a :: {linorder,order_bot} \<Rightarrow> nat) \<Rightarrow> 'a list \<Rightarrow> nat \<Rightarrow> nat"
  where
"s_bucket_size \<alpha> T b \<equiv> card (s_bucket \<alpha> T b)"

definition s_bucket_start :: "('a :: {linorder,order_bot} \<Rightarrow> nat) \<Rightarrow> 'a list \<Rightarrow> nat \<Rightarrow> nat"
  where
"s_bucket_start \<alpha> T b \<equiv> bucket_start \<alpha> T b + l_bucket_size \<alpha> T b"

lemma finite_s_bucket:
 "finite (s_bucket \<alpha> T b)"
  by (clarsimp simp: s_bucket_def finite_bucket)

lemma disjoint_l_s_bucket:
 "l_bucket \<alpha> T b \<inter> s_bucket \<alpha> T b = {}"
  apply (rule disjointI')
  by (clarsimp simp: l_bucket_def s_bucket_def)

lemma lms_subset_s_bucket:
  "lms_bucket \<alpha> T b \<subseteq> s_bucket \<alpha> T b"
  by (clarsimp simp: s_bucket_def lms_bucket_def abs_is_lms_def)

lemma l_un_s_bucket:
  "bucket \<alpha> T b = l_bucket \<alpha> T b \<union> s_bucket \<alpha> T b"
  apply (rule equalityI; clarsimp simp: l_bucket_def s_bucket_def)
  by (meson suffix_type_def)

lemma s_bucket_Max:
  assumes "valid_list T"
  and     "length T > Suc 0"
  and     "strict_mono \<alpha>"
shows "s_bucket \<alpha> T (\<alpha> (Max (set T))) = {}"
proof -
  let ?b = "\<alpha> (Max (set T))"
  from l_bucket_Max[OF assms]
  have "l_bucket \<alpha> T ?b = bucket \<alpha> T ?b" .
  moreover
  from l_un_s_bucket
  have "bucket \<alpha> T ?b = l_bucket \<alpha> T ?b \<union> s_bucket \<alpha> T ?b" .
  hence "s_bucket \<alpha> T ?b \<subseteq> bucket \<alpha> T ?b"
    by blast
  moreover
  from disjoint_l_s_bucket
  have "l_bucket \<alpha> T ?b \<inter> s_bucket \<alpha> T ?b = {}" .
  ultimately
  show ?thesis
    by blast
qed

lemma s_bucket_0:
  assumes "valid_list T"
  and     "strict_mono \<alpha>"
  and     "\<alpha> bot = 0"
  and     "length T = Suc n"
shows "s_bucket \<alpha> T 0 = {n}"
proof -
  have "suffix_type T n = S_type"
    using assms(4) suffix_type_last by blast
  moreover
  have "T ! n = bot"
    by (metis assms(1) assms(4) diff_Suc_1 last_conv_nth length_greater_0_conv valid_list_def)
  hence "\<alpha> (T ! n) = 0"
    by (simp add: assms(3))
  ultimately have "n \<in> s_bucket \<alpha> T 0"
    by (simp add: assms(4) bucket_def s_bucket_def)
  hence "{n} \<subseteq> s_bucket \<alpha> T 0"
    by blast
  moreover
  have "s_bucket \<alpha> T 0 \<subseteq> {n}"
    unfolding s_bucket_def
  proof safe
    fix k
    assume "k \<in> bucket \<alpha> T 0" "suffix_type T k = S_type"
    hence "k \<le> n"
      by (simp add: assms(4) bucket_def)
    have "\<alpha> (T ! k) = 0"
      using \<open>k \<in> bucket \<alpha> T 0\<close> bucket_def by blast
    hence "T ! k = bot"
      by (metis assms(2) assms(3) strict_mono_eq)
    show "k = n"
    proof (rule ccontr)
      assume "k \<noteq> n"
      hence "k < n"
        by (simp add: \<open>k \<le> n\<close> le_neq_implies_less)
      then show False
        using \<open>k \<in> bucket \<alpha> T 0\<close> \<open>k \<noteq> n\<close> assms bucket_0 by blast
    qed
  qed
  ultimately show ?thesis
    by blast
qed

lemma s_bucket_successor:
  "\<lbrakk>valid_list T; strict_mono \<alpha>; \<alpha> bot = 0; b \<noteq> 0; x \<in> s_bucket \<alpha> T b\<rbrakk> \<Longrightarrow>
    Suc x \<in> s_bucket \<alpha> T b \<or> (\<exists>b'. b < b' \<and> Suc x \<in> bucket \<alpha> T b')"
proof -
  assume "valid_list T" "strict_mono \<alpha>" "\<alpha> bot = 0" "b \<noteq> 0" "x \<in> s_bucket \<alpha> T b"
  hence "suffix_type T x = S_type"
    by (simp add: s_bucket_def)

  from valid_list_length_ex[OF \<open>valid_list _\<close>]
  obtain n where
    "length T = Suc n"
    by blast
  moreover
  from \<open>x \<in> s_bucket \<alpha> T b\<close>
  have "x < length T" "\<alpha> (T ! x) = b"
    by (simp add: s_bucket_def bucket_def)+
  ultimately have "Suc x < length T"
    by (metis Suc_lessI \<open>\<alpha> bot = 0\<close> \<open>b \<noteq> 0\<close> \<open>valid_list T\<close> diff_Suc_1 last_conv_nth list.size(3)
          valid_list_def)

  have "T ! x \<le> T ! Suc x"
    by (simp add: \<open>Suc x < length T\<close> \<open>suffix_type T x = S_type\<close> s_type_letter_le_Suc)
  hence "T ! x < T ! Suc x \<or> T ! x = T ! Suc x"
    using le_neq_trans by blast
  moreover
  have "T ! x < T ! Suc x \<Longrightarrow> ?thesis"
  proof -
    assume "T ! x < T ! Suc x"
    hence "\<alpha> (T ! x) < \<alpha> (T ! Suc x)"
      by (simp add: \<open>strict_mono \<alpha>\<close> strict_mono_less)
    hence "b < \<alpha> (T ! Suc x)"
      by (simp add: \<open>\<alpha> (T ! x) = b\<close>)
    with \<open>Suc x < length T\<close>
    have "Suc x \<in> bucket \<alpha> T (\<alpha> (T ! Suc x))"
      by (simp add: bucket_def)
    with \<open>b < \<alpha> (T ! Suc x)\<close>
    show ?thesis
      by blast
  qed
  moreover
  have "T ! x = T ! Suc x \<Longrightarrow> ?thesis"
  proof -
    assume "T ! x = T ! Suc x"
    hence "\<alpha> (T ! Suc x) = b"
      using \<open>\<alpha> (T ! x) = b\<close> by auto
    moreover
    from \<open>Suc x < length T\<close> \<open>T ! x = T ! Suc x\<close> \<open>suffix_type T x = S_type\<close>
    have "suffix_type T (Suc x) = S_type"
      using suffix_type_neq by force
    ultimately show ?thesis
      by (simp add: \<open>Suc x < length T\<close> bucket_def s_bucket_def)
  qed
  ultimately show ?thesis
    by blast
qed

lemma subset_s_bucket_successor:
  "\<lbrakk>valid_list T; strict_mono \<alpha>; \<alpha> bot = 0; b \<noteq> 0; A \<subseteq> s_bucket \<alpha> T b; A \<noteq> {}\<rbrakk> \<Longrightarrow>
    \<exists>x \<in> A. Suc x \<in> s_bucket \<alpha> T b - A \<or> (\<exists>b'. b < b' \<and> Suc x \<in> bucket \<alpha> T b')"
proof -
  assume "valid_list T" "strict_mono \<alpha>" "\<alpha> bot = 0" "b \<noteq> 0" "A \<subseteq> s_bucket \<alpha> T b" "A \<noteq> {}"

  have "finite A"
    using \<open>A \<subseteq> s_bucket \<alpha> T b\<close> finite_s_bucket finite_subset by blast

  let ?B = "s_bucket \<alpha> T b - A"

  have "\<exists>x \<in> A. Suc x \<notin> A"
  proof (rule ccontr)
    assume "\<not> (\<exists>x\<in>A. Suc x \<notin> A)"
    hence "\<forall>x\<in>A. Suc x \<in> A"
      by clarsimp
    hence "\<not> finite A"
      using Max.coboundedI Max_in Suc_n_not_le_n \<open>A \<noteq> {}\<close> by blast
    with \<open>finite A\<close>
    show False
      by blast
  qed
  then obtain x where
    "x \<in> A"
    "Suc x \<notin> A"
    by blast
  with s_bucket_successor[OF \<open>valid_list _\<close> \<open>strict_mono _\<close> \<open>\<alpha> _ = _\<close> \<open>b \<noteq> _\<close>, of x]
       \<open>A \<subseteq> s_bucket \<alpha> T b\<close>
  have "Suc x \<in> s_bucket \<alpha> T b \<or> (\<exists>b'. b < b' \<and> Suc x \<in> bucket \<alpha> T b')"
    by blast
  moreover
  have "Suc x \<in> s_bucket \<alpha> T b \<Longrightarrow> ?thesis"
  proof -
    assume "Suc x \<in> s_bucket \<alpha> T b"
    with \<open>Suc x \<notin> A\<close>
    show ?thesis
      using \<open>x \<in> A\<close> by blast
  qed
  moreover
  have "(\<exists>b'. b < b' \<and> Suc x \<in> bucket \<alpha> T b') \<Longrightarrow> ?thesis"
    using \<open>x \<in> A\<close> by blast
  ultimately show ?thesis
    by blast
qed

lemma valid_list_s_bucket_start_0:
  "\<lbrakk>valid_list T; strict_mono \<alpha>; \<alpha> bot = 0\<rbrakk> \<Longrightarrow>
   s_bucket_start \<alpha> T 0 = 0"
  apply (clarsimp simp: s_bucket_start_def bucket_start_0)
  apply (frule valid_list_length_ex)
  apply clarsimp
  apply (frule (3) bucket_0)
  apply (frule suffix_type_last)
  apply (clarsimp simp: l_bucket_size_def l_bucket_def)
  done

definition pure_s_bucket :: "('a :: {linorder,order_bot} \<Rightarrow> nat) \<Rightarrow> 'a list \<Rightarrow> nat \<Rightarrow> nat set"
  where
"pure_s_bucket \<alpha> T b = {k |k. k \<in> s_bucket \<alpha> T b \<and> k \<notin> lms_bucket \<alpha> T b}"

definition pure_s_bucket_size :: "('a :: {linorder,order_bot} \<Rightarrow> nat) \<Rightarrow> 'a list \<Rightarrow> nat \<Rightarrow> nat"
  where
"pure_s_bucket_size \<alpha> T b \<equiv> card (pure_s_bucket \<alpha> T b)"

lemma finite_pure_s_bucket:
 "finite (pure_s_bucket \<alpha> T b)"
  by (clarsimp simp: pure_s_bucket_def finite_s_bucket)

lemma pure_s_subset_s_bucket:
  "pure_s_bucket \<alpha> T b \<subseteq> s_bucket \<alpha> T b"
  by (clarsimp simp: s_bucket_def pure_s_bucket_def)

lemma disjoint_lms_pure_s_bucket:
 "lms_bucket \<alpha> T b \<inter> pure_s_bucket \<alpha> T b = {}"
  apply (rule disjointI')
  by (clarsimp simp: lms_bucket_def pure_s_bucket_def)

lemma disjoint_pure_s_lms_bucket:
  "pure_s_bucket \<alpha> T b \<inter> lms_bucket \<alpha> T b = {}"
  apply (subst Int_commute)
  by (rule disjoint_lms_pure_s_bucket)

lemma s_eq_pure_s_un_lms_bucket:
  "s_bucket \<alpha> T b = pure_s_bucket \<alpha> T b \<union> lms_bucket \<alpha> T b"
  apply (intro equalityI; clarsimp simp: pure_s_subset_s_bucket lms_subset_s_bucket)
  apply (clarsimp simp: s_bucket_def lms_bucket_def pure_s_bucket_def)
  done

lemma l_pl_pure_s_pl_lms_size:
  "bucket_size \<alpha> T b = l_bucket_size \<alpha> T b + pure_s_bucket_size \<alpha> T b + lms_bucket_size \<alpha> T b"
  apply (clarsimp simp: bucket_size_def l_bucket_size_def pure_s_bucket_size_def
                        lms_bucket_size_def)
  apply (subst add.assoc)
  apply (subst card_Un_disjoint[symmetric,
          OF finite_pure_s_bucket finite_lms_bucket disjoint_pure_s_lms_bucket])
  apply (subst s_eq_pure_s_un_lms_bucket[symmetric])
  apply (subst card_Un_disjoint[symmetric,
          OF finite_l_bucket finite_s_bucket disjoint_l_s_bucket])
  apply (clarsimp simp: l_un_s_bucket)
  done

lemma s_bucket_start_eq_l_bucket_end:
  "s_bucket_start \<alpha> T b = l_bucket_end \<alpha> T b"
  by (simp add: l_bucket_end_def s_bucket_start_def)

lemma s_eq_pure_pl_lms_size:
  "s_bucket_size \<alpha> T b = pure_s_bucket_size \<alpha> T b + lms_bucket_size \<alpha> T b"
  by (simp add: card_Un_disjoint disjoint_pure_s_lms_bucket finite_lms_bucket finite_pure_s_bucket
        lms_bucket_size_def pure_s_bucket_size_def s_bucket_size_def s_eq_pure_s_un_lms_bucket)

lemma bucket_end_eq_s_start_pl_size:
  "bucket_end \<alpha> T b = s_bucket_start \<alpha> T b + s_bucket_size \<alpha> T b"
  by (simp add: bucket_end_def' l_bucket_end_def l_pl_pure_s_pl_lms_size
        s_bucket_start_eq_l_bucket_end s_eq_pure_pl_lms_size)

lemma bucket_start_le_s_bucket_start:
  "bucket_start \<alpha> T b \<le> s_bucket_start \<alpha> T b"
  by (simp add: s_bucket_start_def)

lemma bucket_0_size1:
  assumes "valid_list T"
  and     "strict_mono \<alpha>"
  and     "\<alpha> bot = 0"
shows "bucket_size \<alpha> T 0 = Suc 0 \<and> l_bucket_size \<alpha> T 0 = 0"
proof -
  from valid_list_length_ex[OF assms(1)]
  obtain n where
    "length T = Suc n"
    by blast
  with bucket_0[OF assms(1,3,2)]
  have "bucket \<alpha> T 0 = {n}"
    by blast
  hence "bucket_size \<alpha> T 0 = Suc 0"
    by (simp add: bucket_size_def)
  moreover
  have "suffix_type T n = S_type"
    by (simp add: \<open>length T = Suc n\<close> suffix_type_last)
  hence "n \<notin> l_bucket \<alpha> T 0"
    by (simp add: l_bucket_def)
  hence "l_bucket_size \<alpha> T 0 = 0"
  proof -
    have "l_bucket \<alpha> T 0 \<subseteq> {n}"
      by (metis \<open>bucket \<alpha> T 0 = {n}\<close> l_bucket_subset_bucket)
    hence "\<forall>n. n \<notin> l_bucket \<alpha> T 0"
      using \<open>n \<notin> l_bucket \<alpha> T 0\<close> by blast
    then show ?thesis
      by (simp add: l_bucket_size_def)
  qed
  ultimately
  show ?thesis
    by blast
qed

lemma bucket_0_size2:
  assumes "valid_list T"
  and     "strict_mono \<alpha>"
  and     "\<alpha> bot = 0"
  and     "length T = Suc (Suc n)"
shows "bucket_size \<alpha> T 0 = Suc 0 \<and> l_bucket_size \<alpha> T 0 = 0 \<and> lms_bucket_size \<alpha> T 0 = Suc 0 \<and>
       pure_s_bucket_size \<alpha> T 0 = 0"
proof -
  from bucket_0[OF assms(1,3,2,4)]
  have "bucket \<alpha> T 0 = {Suc n}" .

  have "abs_is_lms T (Suc n)"
    using assms(1,4) abs_is_lms_last by blast
  hence "lms_bucket \<alpha> T 0 = {Suc n}"
    using lms_bucket_subset_bucket[of \<alpha> T 0] \<open>bucket \<alpha> T 0 = {Suc n}\<close>
    by (simp add: lms_bucket_def subset_antisym)
  hence "lms_bucket_size \<alpha> T 0 = Suc 0"
    by (simp add: lms_bucket_size_def)
  moreover
  from \<open>bucket \<alpha> T 0 = {Suc n}\<close> \<open>lms_bucket \<alpha> T 0 = {Suc n}\<close>
  have "pure_s_bucket \<alpha> T 0 = {}"
    by (metis disjoint_insert(1) disjoint_l_lms_bucket disjoint_lms_pure_s_bucket
          l_bucket_subset_bucket l_un_s_bucket pure_s_subset_s_bucket singletonI
          subset_singletonD sup_bot.left_neutral)
  hence "pure_s_bucket_size \<alpha> T 0 = 0"
    by (simp add: pure_s_bucket_size_def)
  moreover
  from bucket_0_size1[OF assms(1-3)]
  have "bucket_size \<alpha> T 0 = Suc 0 \<and> l_bucket_size \<alpha> T 0 = 0" .
  ultimately
  show ?thesis
    by blast
qed

definition lms_bucket_start :: "('a :: {linorder,order_bot} \<Rightarrow> nat) \<Rightarrow> 'a list \<Rightarrow> nat \<Rightarrow> nat"
  where
"lms_bucket_start \<alpha> T b = bucket_start \<alpha> T b + l_bucket_size \<alpha> T b + pure_s_bucket_size \<alpha> T b"

lemma l_bucket_end_le_lms_bucket_start:
  "l_bucket_end \<alpha> T b \<le> lms_bucket_start \<alpha> T b"
  by (simp add: l_bucket_end_def lms_bucket_start_def)

lemma lms_bucket_start_le_bucket_end:
  "lms_bucket_start \<alpha> T b \<le> bucket_end \<alpha> T b"
  by (simp add: bucket_end_def' lms_bucket_start_def l_pl_pure_s_pl_lms_size)

lemma lms_bucket_pl_size_eq_end:
  "lms_bucket_start \<alpha> T b + lms_bucket_size \<alpha> T b = bucket_end \<alpha> T b"
  by (simp add: bucket_end_def' l_pl_pure_s_pl_lms_size lms_bucket_start_def)

section \<open>Continuous Buckets\<close>

lemma continuous_buckets:
  "continuous_list (map (\<lambda>b. (bucket_start \<alpha> T b, bucket_end \<alpha> T b)) [i..<j])"
  by (clarsimp simp: continuous_list_def bucket_start_Suc_eq_bucket_end)

lemma index_in_bucket_interval_gen:
  "\<lbrakk>i < length T; strict_mono \<alpha>\<rbrakk> \<Longrightarrow>
    \<exists>b \<le> \<alpha> (Max (set T)). bucket_start \<alpha> T b \<le> i \<and> i < bucket_end \<alpha> T b"
  apply (insert continuous_buckets[of \<alpha> T 0 "Suc (\<alpha> (Max (set T)))"])
  apply (drule continuous_list_interval_2[where n = "\<alpha> (Max (set T))" and i = i])
     apply clarsimp
    apply (subst nth_map)
     apply clarsimp
    apply (clarsimp split: prod.split simp: upt_rec bucket_start_0)
    apply (subst nth_map)
    apply clarsimp
   apply (clarsimp split: prod.split simp: nth_append bucket_end_Max)
  apply clarsimp
  apply (clarsimp simp: nth_append split: if_splits prod.splits)
  apply (meson dual_order.order_iff_strict)
  by blast

lemma index_in_bucket_interval:
  "\<lbrakk>i < length T; valid_list T; \<alpha> bot = 0; strict_mono \<alpha>\<rbrakk> \<Longrightarrow>
    \<exists>b \<le> \<alpha> (Max (set T)). bucket_start \<alpha> T b \<le> i \<and> i < bucket_end \<alpha> T b"
  using index_in_bucket_interval_gen by blast

section \<open>Bucket Initialisation\<close>

definition lms_bucket_init :: "('a :: {linorder,order_bot} \<Rightarrow> nat) \<Rightarrow> 'a list \<Rightarrow> nat list \<Rightarrow> bool"
  where
"lms_bucket_init \<alpha> T B =
  (\<alpha> (Max (set T)) < length B \<and>
   (\<forall>b \<le> \<alpha> (Max (set T)). B ! b = bucket_end \<alpha> T b))"

lemma lms_bucket_init_length:
  "lms_bucket_init \<alpha> T B \<Longrightarrow> \<alpha> (Max (set T)) < length B"
  using lms_bucket_init_def by blast

lemma lms_bucket_initD:
  "\<lbrakk>lms_bucket_init \<alpha> T B; b \<le> \<alpha> (Max (set T))\<rbrakk> \<Longrightarrow> B ! b = bucket_end \<alpha> T b"
  using lms_bucket_init_def by blast

definition l_bucket_init :: "('a :: {linorder,order_bot} \<Rightarrow> nat) \<Rightarrow> 'a list \<Rightarrow> nat list \<Rightarrow> bool"
  where
"l_bucket_init \<alpha> T B =
  (\<alpha> (Max (set T)) < length B \<and>
   (\<forall>b \<le> \<alpha> (Max (set T)). B ! b = bucket_start \<alpha> T b))"

lemma l_bucket_init_length:
  "l_bucket_init \<alpha> T B \<Longrightarrow> \<alpha> (Max (set T)) < length B"
  using l_bucket_init_def by blast

lemma l_bucket_initD:
  "\<lbrakk>l_bucket_init \<alpha> T B; b \<le> \<alpha> (Max (set T))\<rbrakk> \<Longrightarrow> B ! b = bucket_start \<alpha> T b"
  using l_bucket_init_def by blast

definition s_bucket_init
  where
"s_bucket_init \<alpha> T B =
  (\<alpha> (Max (set T)) < length B \<and>
   (\<forall>b\<le>\<alpha> (Max (set T)).
    (b > 0 \<longrightarrow> B ! b = bucket_end \<alpha> T b) \<and>
    (b = 0 \<longrightarrow> B ! b = 0)
   )
  )"

lemma s_bucket_init_length:
  "s_bucket_init \<alpha> T B \<Longrightarrow> \<alpha> (Max (set T)) < length B"
  using s_bucket_init_def by blast

lemma s_bucket_initD:
  "\<lbrakk>s_bucket_init \<alpha> T B; b \<le> \<alpha> (Max (set T)); b > 0\<rbrakk> \<Longrightarrow> B ! b = bucket_end \<alpha> T b"
  "\<lbrakk>s_bucket_init \<alpha> T B; b \<le> \<alpha> (Max (set T)); b = 0\<rbrakk> \<Longrightarrow> B ! b = 0"
  using s_bucket_init_def by auto

section \<open>Bucket Range\<close>

definition in_s_current_bucket
  where
"in_s_current_bucket \<alpha> T B b i \<equiv> (b \<le> \<alpha> (Max (set T)) \<and> B ! b \<le> i \<and> i < bucket_end \<alpha> T b)"

lemma in_s_current_bucketD:
  "in_s_current_bucket \<alpha> T B b i \<Longrightarrow> b \<le> \<alpha> (Max (set T))"
  "in_s_current_bucket \<alpha> T B b i \<Longrightarrow> B ! b \<le> i"
  "in_s_current_bucket \<alpha> T B b i \<Longrightarrow> i < bucket_end \<alpha> T b"
  by (simp_all add: in_s_current_bucket_def)

definition in_s_current_buckets
  where
"in_s_current_buckets \<alpha> T B i \<equiv> (\<exists>b. in_s_current_bucket \<alpha> T B b i)"

lemma in_s_current_bucket_list_slice:
  assumes "length SA = length T"
  and     "in_s_current_bucket \<alpha> T B b i"
  and     "SA ! i = x"
shows "x \<in> set (list_slice SA (B ! b) (bucket_end \<alpha> T b))"
  by (metis assms bucket_end_le_length in_s_current_bucket_def list_slice_nth_mem)

definition in_l_bucket
  where
"in_l_bucket \<alpha> T b i \<equiv> (b \<le> \<alpha> (Max (set T)) \<and> bucket_start \<alpha> T b \<le> i \<and> i < l_bucket_end \<alpha> T b)"

end