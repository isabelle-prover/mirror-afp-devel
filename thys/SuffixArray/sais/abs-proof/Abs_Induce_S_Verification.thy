theory Abs_Induce_S_Verification
  imports "../abs-def/Abs_SAIS"
begin

section "Abstract Induce S Simple Properties"

lemma abs_induce_s_step_ex:
  "\<exists>B' SA' i'. abs_induce_s_step a b = (B', SA', i')"
  by (meson prod_cases3)

lemma abs_induce_s_step_B_length:
  "abs_induce_s_step (B, SA, i) (\<alpha>, T) = (B', SA', i') \<Longrightarrow> length B' = length B"
  by (clarsimp split: prod.splits if_splits nat.splits SL_types.splits simp: Let_def)

lemma abs_induce_s_step_SA_length:
  "abs_induce_s_step (B, SA, i) (\<alpha>, T) = (B', SA', i') \<Longrightarrow> length SA' = length SA"
  by (clarsimp split: prod.splits if_splits nat.splits SL_types.splits simp: Let_def)

lemma abs_induce_s_step_Suc:
  "abs_induce_s_step (B, SA, Suc i) (\<alpha>, T) = (B', SA', i') \<Longrightarrow> i' = i"
  by (clarsimp split: prod.splits if_splits nat.splits SL_types.splits simp: Let_def)

lemma abs_induce_s_step_0:
  "abs_induce_s_step (B, SA, 0) (\<alpha>, T) = (B, SA, 0)"
  by (clarsimp split: prod.splits if_splits nat.splits SL_types.splits simp: Let_def)

corollary abs_induce_s_step_0_alt:
  assumes "abs_induce_s_step (B, SA, i) (\<alpha>, T) = (B', SA', i')"
  and     "i = 0"
shows "B = B' \<and> SA = SA' \<and> i' = 0"
  using assms(1) assms(2) by auto

lemma repeat_abs_induce_s_step_index:
  "\<exists>B' SA'. repeat n abs_induce_s_step (B, SA, m) (\<alpha>, T) = (B', SA', m - n) \<and>
            length SA' = length SA \<and> length B' = length B"
proof(induct n arbitrary: m)
  case 0
  then show ?case by (clarsimp simp: repeat_0)
next
  case (Suc n)
  note IH = this

  from IH[of m]
  obtain B' SA' where
    "repeat n abs_induce_s_step (B, SA, m) (\<alpha>, T) = (B', SA', m - n)"
    "length SA' = length SA"
    "length B' = length B"
    by blast
  with repeat_step[of n abs_induce_s_step "(B, SA, m)" "(\<alpha>, T)"]
  have "repeat (Suc n) abs_induce_s_step (B, SA, m) (\<alpha>, T) = abs_induce_s_step (B', SA', m - n) (\<alpha>, T)"
    by simp
  moreover
  have "\<exists>B'' SA''. abs_induce_s_step (B', SA', m - n) (\<alpha>, T) = (B'', SA'', m - Suc n) \<and>
                   length SA'' = length SA' \<and> length B'' = length B'"
  proof (cases "n < m")
    assume "n < m"
    hence "\<exists>k. m - n = Suc k"
      by presburger
    then obtain k where
      "m - n = Suc k"
      by blast

    from abs_induce_s_step_ex[of "(B',SA', m - n)" "(\<alpha>, T)"]
    obtain B'' SA'' i' where
      P: "abs_induce_s_step (B', SA', m - n) (\<alpha>, T) = (B'', SA'', i')"
      by blast
    with `m - n = Suc k` abs_induce_s_step_Suc[of B' SA' k \<alpha> T B'' SA'' i']
    have "i' = m - Suc n"
      by auto
    with `abs_induce_s_step (B', SA', m - n) (\<alpha>, T) = (B'', SA'', i')`
          abs_induce_s_step_SA_length[OF P]
          abs_induce_s_step_B_length[OF P]
    show ?thesis
      by simp
  next
    assume "\<not>n < m"
    hence "m \<le> n"
      by simp
    hence "m - n = 0"
      by simp
    with abs_induce_s_step_0[of B' SA' \<alpha> T]
    show ?thesis
      by simp
  qed
  ultimately show ?case
    by (simp add: `length SA' = length SA` `length B' = length B`)
qed

lemma abs_induce_s_base_index:
  "\<exists>B' SA'. abs_induce_s_base \<alpha> T B SA = (B', SA', 0)"
  unfolding abs_induce_s_base_def
  by (metis cancel_comm_monoid_add_class.diff_cancel repeat_abs_induce_s_step_index)

lemma abs_induce_s_length:
  "length (abs_induce_s \<alpha> T B SA) = length SA"
  unfolding abs_induce_s_def abs_induce_s_base_def
  apply (rule repeat_maintain_inv; simp add: Let_def)
  apply (clarsimp split: prod.splits simp del: abs_induce_s_step.simps)
  apply (drule abs_induce_s_step_SA_length; simp)
  done

section "Preconditions"

definition l_types_init
  where
"l_types_init \<alpha> T SA \<equiv>
  (\<forall>b \<le> \<alpha> (Max (set T)).
    set (list_slice SA (bucket_start \<alpha> T b) (l_bucket_end \<alpha> T b)) = l_bucket \<alpha> T b \<and>
    distinct (list_slice SA (bucket_start \<alpha> T b) (l_bucket_end \<alpha> T b))
  )"

lemma l_types_initD:
  "\<lbrakk>l_types_init \<alpha> T SA; b \<le> \<alpha> (Max (set T))\<rbrakk> \<Longrightarrow>
   set (list_slice SA (bucket_start \<alpha> T b) (l_bucket_end \<alpha> T b)) = l_bucket \<alpha> T b"
  "\<lbrakk>l_types_init \<alpha> T SA; b \<le> \<alpha> (Max (set T))\<rbrakk> \<Longrightarrow>
   distinct (list_slice SA (bucket_start \<alpha> T b) (l_bucket_end \<alpha> T b))"
  using l_types_init_def by blast+

lemma l_types_init_nth:
  assumes "length SA = length T"
  and     "l_types_init \<alpha> T SA"
  and     "b \<le> \<alpha> (Max (set T))"
  and     "bucket_start \<alpha> T b \<le> i"
  and     "i < l_bucket_end \<alpha> T b"
shows "SA ! i \<in> l_bucket \<alpha> T b"
proof -
  have "l_bucket_end \<alpha> T b \<le> length SA"
    by (metis assms(1) bucket_end_le_length dual_order.order_iff_strict l_bucket_end_le_bucket_end
              less_le_trans)
  with l_types_initD(1)[OF assms(2,3)] list_slice_nth_mem[OF assms(4,5)]
  show ?thesis
    by blast
qed

definition s_type_init
  where
"s_type_init T SA \<equiv> (\<exists>n. length T = Suc n \<and> SA ! 0 = n)"

definition s_perm_pre
  where
"s_perm_pre \<alpha> T B SA n \<equiv>
  s_bucket_init \<alpha> T B \<and>
  s_type_init T SA \<and>
  strict_mono \<alpha> \<and>
  \<alpha> (Max (set T)) < length B \<and>
  length SA = length T \<and>
  l_types_init \<alpha> T SA \<and>
  valid_list T \<and>
  \<alpha> bot = 0 \<and>
  Suc 0 < length T \<and>
  length T \<le> n"

definition s_sorted_pre
  where
"s_sorted_pre \<alpha> T SA \<equiv>
  (\<forall>b \<le> \<alpha> (Max (set T)).
    ordlistns.sorted (map (suffix T) (list_slice SA (bucket_start \<alpha> T b) (l_bucket_end \<alpha> T b)))
  )"

lemma s_sorted_preD:
  "\<lbrakk>s_sorted_pre \<alpha> T SA; b \<le> \<alpha> (Max (set T))\<rbrakk> \<Longrightarrow>
   ordlistns.sorted (map (suffix T) (list_slice SA (bucket_start \<alpha> T b) (l_bucket_end \<alpha> T b)))"
  using s_sorted_pre_def by blast

definition s_prefix_sorted_pre
  where
"s_prefix_sorted_pre \<alpha> T SA \<equiv>
  (\<forall>b \<le> \<alpha> (Max (set T)).
    ordlistns.sorted (map (lms_slice T) (list_slice SA (bucket_start \<alpha> T b) (l_bucket_end \<alpha> T b)))
  )"

lemma s_prefix_sorted_preD:
  "\<lbrakk>s_prefix_sorted_pre \<alpha> T SA; b \<le> \<alpha> (Max (set T))\<rbrakk> \<Longrightarrow>
   ordlistns.sorted (map (lms_slice T) (list_slice SA (bucket_start \<alpha> T b) (l_bucket_end \<alpha> T b)))"
  using s_prefix_sorted_pre_def by blast

section "Invariants"

subsection "Definitions"

subsubsection "Distinctness"

definition s_distinct_inv
  where
"s_distinct_inv \<alpha> T B SA \<equiv>
  (\<forall>b \<le> \<alpha> (Max (set T)). distinct (list_slice SA (B ! b) (bucket_end \<alpha> T b)))"

lemma s_distinct_invD:
  "\<lbrakk>s_distinct_inv \<alpha> T B SA; b \<le> \<alpha> (Max (set T))\<rbrakk> \<Longrightarrow>
   distinct (list_slice SA (B ! b) (bucket_end \<alpha> T b))"
  using s_distinct_inv_def by blast

subsubsection "S Bucket Ptr"

definition s_bucket_ptr_inv ::
  "('a :: {linorder, order_bot} \<Rightarrow> nat) \<Rightarrow> 'a list \<Rightarrow> nat list \<Rightarrow> bool"
  where
"s_bucket_ptr_inv \<alpha> T B \<equiv>
  (\<forall>b \<le> \<alpha> (Max (set T)).
    s_bucket_start \<alpha> T b \<le> B ! b \<and>
    B ! b \<le> bucket_end \<alpha> T b \<and>
    (b = 0 \<longrightarrow> B ! b = 0))"

lemma s_bucket_ptr_lower_bound:
  assumes "s_bucket_ptr_inv \<alpha> T B"
  and     "b \<le> \<alpha> (Max (set T))"
shows "s_bucket_start \<alpha> T b \<le> B ! b"
  using assms(1) assms(2) s_bucket_ptr_inv_def by blast

lemma s_bucket_ptr_upper_bound:
  assumes "s_bucket_ptr_inv \<alpha> T B"
  and     "b \<le> \<alpha> (Max (set T))"
shows "B ! b \<le> bucket_end \<alpha> T b"
  by (metis assms s_bucket_ptr_inv_def)

lemma s_bucket_ptr_0:
  assumes "s_bucket_ptr_inv \<alpha> T B"
  and     "b = 0"
shows "B ! b = 0"
  using assms s_bucket_ptr_inv_def by auto

subsubsection "Locations"

definition s_locations_inv ::
  "('a :: {linorder, order_bot} \<Rightarrow> nat) \<Rightarrow> 'a list \<Rightarrow> nat list \<Rightarrow> nat list \<Rightarrow> bool"
  where
"s_locations_inv \<alpha> T B SA \<equiv>
  (\<forall>b \<le> \<alpha> (Max (set T)).
    (\<forall>i. B ! b \<le> i \<and> i < bucket_end \<alpha> T b \<longrightarrow> SA ! i \<in> s_bucket \<alpha> T b))"

lemma s_locations_invD:
  "\<lbrakk>s_locations_inv \<alpha> T B SA; b \<le> \<alpha> (Max (set T)); B ! b \<le> i; i < bucket_end \<alpha> T b\<rbrakk> \<Longrightarrow>
   SA ! i \<in> s_bucket \<alpha> T b"
  using s_locations_inv_def by blast

lemma s_locations_inv_in_list_slice:
  assumes "s_locations_inv \<alpha> T B SA"
  and     "b \<le> \<alpha> (Max (set T))"
  and     "x \<in> set (list_slice SA (B ! b) (bucket_end \<alpha> T b))"
shows "x \<in> s_bucket \<alpha> T b"
proof -
  from in_set_conv_nth[THEN iffD1, OF assms(3)]
  obtain i where
    "i < length (list_slice SA (B ! b) (bucket_end \<alpha> T b))"
    "list_slice SA (B ! b) (bucket_end \<alpha> T b) ! i = x"
    by blast
  with nth_list_slice
  have "SA ! (B ! b + i) = x"
    by fastforce
  moreover
  have "B ! b + i < bucket_end \<alpha> T b"
    using \<open>i < length (list_slice SA (B ! b) (bucket_end \<alpha> T b))\<close> by auto
  ultimately
  show ?thesis
    using assms(1,2) le_add1 s_locations_invD by blast
qed

lemma s_locations_inv_subset_s_bucket:
  assumes "s_locations_inv \<alpha> T B SA"
  and     "b \<le> \<alpha> (Max (set T))"
shows "set (list_slice SA (B ! b) (bucket_end \<alpha> T b)) \<subseteq> s_bucket \<alpha> T b"
  using assms s_locations_inv_in_list_slice by blast

subsubsection "Unchanged"

definition s_unchanged_inv ::
  "('a :: {linorder, order_bot} \<Rightarrow> nat) \<Rightarrow> 'a list \<Rightarrow> nat list \<Rightarrow> nat list \<Rightarrow> nat list \<Rightarrow> bool"
  where
"s_unchanged_inv \<alpha> T B SA SA' \<equiv>
  (\<forall>b \<le> \<alpha> (Max (set T)). (\<forall>i. bucket_start \<alpha> T b \<le> i \<and> i < B ! b \<longrightarrow>  SA' ! i = SA ! i))"

lemma s_unchanged_invD:
  "\<lbrakk>s_unchanged_inv \<alpha> T B SA SA'; b \<le> \<alpha> (Max (set T)); bucket_start \<alpha> T b \<le> i; i < B ! b\<rbrakk> \<Longrightarrow>
   SA' ! i = SA ! i"
  using s_unchanged_inv_def by blast

subsubsection "Seen"

definition s_seen_inv ::
  "('a :: {linorder, order_bot} \<Rightarrow> nat) \<Rightarrow> 'a list \<Rightarrow> nat list \<Rightarrow> nat list \<Rightarrow> nat \<Rightarrow> bool"
  where
"s_seen_inv \<alpha> T B SA n \<equiv>
  \<forall>i < length SA. n \<le> i \<longrightarrow>
    (suffix_type T (SA ! i) = S_type \<longrightarrow> in_s_current_bucket \<alpha> T B (\<alpha> (T ! (SA ! i))) i) \<and>
    (suffix_type T (SA ! i) = L_type \<longrightarrow> in_l_bucket \<alpha> T (\<alpha> (T ! (SA ! i))) i) \<and>
    SA ! i < length T"

lemma s_seen_invD:
  "\<lbrakk>s_seen_inv \<alpha> T B SA n; i < length SA; n \<le> i\<rbrakk> \<Longrightarrow> SA ! i < length T"
  "\<lbrakk>s_seen_inv \<alpha> T B SA n; i < length SA; n \<le> i; suffix_type T (SA ! i) = L_type\<rbrakk> \<Longrightarrow>
   in_l_bucket \<alpha> T (\<alpha> (T ! (SA ! i))) i"
  "\<lbrakk>s_seen_inv \<alpha> T B SA n; i < length SA; n \<le> i; suffix_type T (SA ! i) = S_type\<rbrakk> \<Longrightarrow>
   in_s_current_bucket \<alpha> T B (\<alpha> (T ! (SA ! i))) i"
  unfolding s_seen_inv_def by blast+

subsubsection "Predecessor"

definition s_pred_inv ::
  "(('a :: {linorder, order_bot}) \<Rightarrow> nat) \<Rightarrow> 'a list \<Rightarrow> nat list \<Rightarrow> nat list \<Rightarrow> nat \<Rightarrow> bool"
  where
"s_pred_inv \<alpha> T B SA n =
  (\<forall>b i. in_s_current_bucket \<alpha> T B b i \<and> b \<noteq> 0 \<longrightarrow>
    (\<exists>j < length SA. SA ! j = Suc (SA ! i) \<and> i < j \<and> n < j)
  )"

lemma s_pred_invD:
  "\<lbrakk>s_pred_inv \<alpha> T B SA k; in_s_current_bucket \<alpha> T B b i; b \<noteq> 0\<rbrakk> \<Longrightarrow>
   \<exists>j < length SA. SA ! j = Suc (SA ! i) \<and> i < j \<and> k < j"
  using s_pred_inv_def by blast

subsubsection "Successor"

definition s_suc_inv ::
  "('a :: {linorder, order_bot} \<Rightarrow> nat) \<Rightarrow> 'a list \<Rightarrow> nat list \<Rightarrow> nat list \<Rightarrow> nat \<Rightarrow> bool"
  where
"s_suc_inv \<alpha> T B SA n \<equiv>
  \<forall>i < length SA. n < i \<longrightarrow>
    (\<forall>j. SA ! i = Suc j \<and> suffix_type T j = S_type \<longrightarrow>
      (\<exists>k. in_s_current_bucket \<alpha> T B (\<alpha> (T ! j)) k \<and> SA ! k = j \<and> k < i))"

lemma s_suc_invD:
  "\<lbrakk>s_suc_inv \<alpha> T B SA n; i < length SA; n < i; SA ! i = Suc j; suffix_type T j = S_type\<rbrakk> \<Longrightarrow>
   \<exists>k. in_s_current_bucket \<alpha> T B (\<alpha> (T ! j)) k \<and> SA ! k = j \<and> k < i"
  using s_suc_inv_def by blast

subsubsection "Combined Permutation Invariant"

definition s_perm_inv ::
  "('a :: {linorder, order_bot} \<Rightarrow> nat) \<Rightarrow> 'a list \<Rightarrow> nat list \<Rightarrow> nat list \<Rightarrow> nat list \<Rightarrow> nat \<Rightarrow> bool"
  where
"s_perm_inv \<alpha> T B SA SA' n \<equiv>
  s_distinct_inv \<alpha> T B SA' \<and>
  s_bucket_ptr_inv \<alpha> T B \<and>
  s_locations_inv \<alpha> T B SA' \<and>
  s_unchanged_inv \<alpha> T B SA SA' \<and>
  s_seen_inv \<alpha> T B SA' n \<and>
  s_pred_inv \<alpha> T B SA' n \<and>
  s_suc_inv \<alpha> T B SA' n \<and>
  strict_mono \<alpha> \<and>
  \<alpha> (Max (set T)) < length B \<and>
  length SA = length T \<and>
  length SA' = length T \<and>
  l_types_init \<alpha> T SA \<and>
  valid_list T \<and>
  \<alpha> bot = 0 \<and>
  Suc 0 < length T"

lemma s_perm_inv_elims:
  "s_perm_inv \<alpha> T B SA SA' n \<Longrightarrow> s_distinct_inv \<alpha> T B SA'"
  "s_perm_inv \<alpha> T B SA SA' n \<Longrightarrow> s_bucket_ptr_inv \<alpha> T B"
  "s_perm_inv \<alpha> T B SA SA' n \<Longrightarrow> s_locations_inv \<alpha> T B SA'"
  "s_perm_inv \<alpha> T B SA SA' n \<Longrightarrow> s_unchanged_inv \<alpha> T B SA SA'"
  "s_perm_inv \<alpha> T B SA SA' n \<Longrightarrow> s_seen_inv \<alpha> T B SA' n"
  "s_perm_inv \<alpha> T B SA SA' n \<Longrightarrow> s_pred_inv \<alpha> T B SA' n"
  "s_perm_inv \<alpha> T B SA SA' n \<Longrightarrow> s_suc_inv \<alpha> T B SA' n"
  "s_perm_inv \<alpha> T B SA SA' n \<Longrightarrow> strict_mono \<alpha>"
  "s_perm_inv \<alpha> T B SA SA' n \<Longrightarrow> \<alpha> (Max (set T)) < length B"
  "s_perm_inv \<alpha> T B SA SA' n \<Longrightarrow> length SA = length T"
  "s_perm_inv \<alpha> T B SA SA' n \<Longrightarrow> length SA' = length T"
  "s_perm_inv \<alpha> T B SA SA' n \<Longrightarrow> l_types_init \<alpha> T SA"
  "s_perm_inv \<alpha> T B SA SA' n \<Longrightarrow> valid_list T"
  "s_perm_inv \<alpha> T B SA SA' n \<Longrightarrow> \<alpha> bot = 0"
  "s_perm_inv \<alpha> T B SA SA' n \<Longrightarrow> Suc 0 < length T"
  by (simp_all add: s_perm_inv_def)

fun s_perm_inv_alt ::
  "('a :: {linorder, order_bot} \<Rightarrow> nat) \<Rightarrow> 'a list \<Rightarrow> nat list \<Rightarrow> nat list \<times> nat list \<times> nat \<Rightarrow> bool"
  where
"s_perm_inv_alt \<alpha> T SA (B, SA', n) = s_perm_inv \<alpha> T B SA SA' n"

subsubsection "Sorted"

definition s_sorted_inv
  where
"s_sorted_inv \<alpha> T B SA \<equiv>
  (\<forall>b \<le> \<alpha> (Max (set T)).
    ordlistns.sorted (map (suffix T) (list_slice SA (B ! b) (bucket_end \<alpha> T b)))
  )"

lemma s_sorted_invD:
  "\<lbrakk>s_sorted_inv \<alpha> T B SA; b \<le> \<alpha> (Max (set T))\<rbrakk> \<Longrightarrow>
   ordlistns.sorted (map (suffix T) (list_slice SA (B ! b) (bucket_end \<alpha> T b)))"
  using s_sorted_inv_def by blast

fun s_sorted_inv_alt ::
  "('a :: {linorder, order_bot} \<Rightarrow> nat) \<Rightarrow> 'a list \<Rightarrow> nat list \<Rightarrow> nat list \<times> nat list \<times> nat \<Rightarrow> bool"
  where
"s_sorted_inv_alt \<alpha> T SA (B, SA', n) =
  (s_perm_inv \<alpha> T B SA SA' n \<and> s_sorted_pre \<alpha> T SA \<and> s_sorted_inv \<alpha> T B SA')"

definition s_prefix_sorted_inv
  where
"s_prefix_sorted_inv \<alpha> T B SA \<equiv>
  (\<forall>b \<le> \<alpha> (Max (set T)).
    ordlistns.sorted (map (lms_slice T) (list_slice SA (B ! b) (bucket_end \<alpha> T b)))
  )"

lemma s_prefix_sorted_invD:
  "\<lbrakk>s_prefix_sorted_inv \<alpha> T B SA; b \<le> \<alpha> (Max (set T))\<rbrakk> \<Longrightarrow>
   ordlistns.sorted (map (lms_slice T) (list_slice SA (B ! b) (bucket_end \<alpha> T b)))"
  using s_prefix_sorted_inv_def by blast

fun s_prefix_sorted_inv_alt ::
  "('a :: {linorder, order_bot} \<Rightarrow> nat) \<Rightarrow> 'a list \<Rightarrow> nat list \<Rightarrow> nat list \<times> nat list \<times> nat \<Rightarrow> bool"
  where
"s_prefix_sorted_inv_alt \<alpha> T SA (B, SA', n) =
  (s_perm_inv \<alpha> T B SA SA' n \<and> s_prefix_sorted_pre \<alpha> T SA \<and> s_prefix_sorted_inv \<alpha> T B SA')"

subsection "Helpers"

lemma s_current_bucket_pairwise_distinct:
  assumes "s_distinct_inv \<alpha> T B SA"
  and     "s_locations_inv \<alpha> T B SA"
  and     "b \<le> \<alpha> (Max (set T))"
  and     "b' \<le> \<alpha> (Max (set T))"
  and     "b \<noteq> b'"
shows "distinct (list_slice SA (B ! b) (bucket_end \<alpha> T b) @ list_slice SA (B ! b') (bucket_end \<alpha> T b'))"
proof (intro distinct_append[THEN iffD2] conjI disjointI')
  from s_distinct_invD[OF assms(1,3)]
  show "distinct (list_slice SA (B ! b) (bucket_end \<alpha> T b))" .
next
  from s_distinct_invD[OF assms(1,4)]
  show "distinct (list_slice SA (B ! b') (bucket_end \<alpha> T b'))" .
next
  fix x y
  assume A: "x \<in> set (list_slice SA (B ! b) (bucket_end \<alpha> T b))"
            "y \<in> set (list_slice SA (B ! b') (bucket_end \<alpha> T b'))"

  from s_locations_inv_in_list_slice[OF assms(2,3) A(1)]
  have "x \<in> s_bucket \<alpha> T b" .
  moreover
  from s_locations_inv_in_list_slice[OF assms(2,4) A(2)]
  have "y \<in> s_bucket \<alpha> T b'" .
  ultimately
  show "x \<noteq> y"
    using assms(5)
    by (metis (mono_tags, lifting) bucket_def s_bucket_def mem_Collect_eq)
qed

lemma s_unchanged_list_slice:
  assumes "s_unchanged_inv \<alpha> T B SA0 SA"
  and     "length SA0 = length T"
  and     "length SA = length T"
  and     "b \<le> \<alpha> (Max (set T))"
  and     "bucket_start \<alpha> T b \<le> i"
  and     "j \<le> B ! b"
shows "list_slice SA i j = list_slice SA0 i j"
proof (intro list_eq_iff_nth_eq[THEN iffD2] conjI allI impI)
  show "length (list_slice SA i j) = length (list_slice SA0 i j)"
    by (simp add: assms)
next
  fix k
  assume "k < length (list_slice SA i j)"
  hence "k < length (list_slice SA0 i j)"
    by (simp add: assms)

  from nth_list_slice[OF `k < length (list_slice SA i j)`]
  have "list_slice SA i j ! k = SA ! (i + k)" .
  moreover
  from nth_list_slice[OF `k < length (list_slice SA0 i j)`]
  have "list_slice SA0 i j ! k = SA0 ! (i + k)" .
  moreover
  {
    have "bucket_start \<alpha> T b \<le> i + k"
      by (simp add: assms(5) trans_le_add1)
    moreover
    have "i + k < j"
      using \<open>k < length (list_slice SA i j)\<close> by auto
    hence "i + k < B ! b"
      using assms(6) order.strict_trans2 by blast
    ultimately
    have "SA ! (i + k) = SA0 ! (i + k)"
      using s_unchanged_invD[OF assms(1,4)]
      by blast
  }
  ultimately show "list_slice SA i j ! k = list_slice SA0 i j ! k"
    by simp
qed

lemma l_types_init_maintained:
  assumes "s_bucket_ptr_inv \<alpha> T B"
  and     "s_unchanged_inv \<alpha> T B SA0 SA"
  and     "length SA0 = length T"
  and     "length SA = length T"
  and     "l_types_init \<alpha> T SA0"
shows "l_types_init \<alpha> T SA"
  unfolding l_types_init_def
proof(intro allI impI)
  fix b
  let ?xs = "list_slice SA (bucket_start \<alpha> T b) (l_bucket_end \<alpha> T b)"
  let ?ys = "list_slice SA0 (bucket_start \<alpha> T b) (l_bucket_end \<alpha> T b)"
  assume "b \<le> \<alpha> (Max (set T))"
  with s_bucket_ptr_lower_bound[OF assms(1), of b]
  have "l_bucket_end \<alpha> T b \<le> B ! b"
    by (simp add: s_bucket_start_eq_l_bucket_end)
  with s_unchanged_list_slice[OF assms(2-4) `b \<le> \<alpha> (Max (set T))`,
        of "bucket_start \<alpha> T b" "l_bucket_end \<alpha> T b"]
  have "?xs = ?ys"
    by blast
  with assms(5)[simplified l_types_init_def, THEN spec, THEN mp, OF `b \<le> \<alpha> (Max (set T))`]
  show "set ?xs = l_bucket \<alpha> T b \<and> distinct ?xs"
    by simp
qed

lemma s_sorted_pre_maintained:
  assumes "s_bucket_ptr_inv \<alpha> T B"
  and     "s_unchanged_inv \<alpha> T B SA0 SA"
  and     "length SA0 = length T"
  and     "length SA = length T"
  and     "s_sorted_pre \<alpha> T SA0"
shows "s_sorted_pre \<alpha> T SA"
  unfolding s_sorted_pre_def
proof(intro allI impI)
  fix b
  let ?xs = "list_slice SA (bucket_start \<alpha> T b) (l_bucket_end \<alpha> T b)"
  let ?ys = "list_slice SA0 (bucket_start \<alpha> T b) (l_bucket_end \<alpha> T b)"
  assume "b \<le> \<alpha> (Max (set T))"
  with s_bucket_ptr_lower_bound[OF assms(1), of b]
  have "l_bucket_end \<alpha> T b \<le> B ! b"
    by (simp add: s_bucket_start_eq_l_bucket_end)
  with s_unchanged_list_slice[OF assms(2-4) `b \<le> \<alpha> (Max (set T))`,
        of "bucket_start \<alpha> T b" "l_bucket_end \<alpha> T b"]
  have "?xs = ?ys"
    by blast
  then show "ordlistns.sorted (map (suffix T) ?xs)"
    using \<open>b \<le> \<alpha> (Max (set T))\<close> assms(5) s_sorted_pre_def by auto
qed

lemma s_prefix_sorted_pre_maintained:
  assumes "s_bucket_ptr_inv \<alpha> T B"
  and     "s_unchanged_inv \<alpha> T B SA0 SA"
  and     "length SA0 = length T"
  and     "length SA = length T"
  and     "s_prefix_sorted_pre \<alpha> T SA0"
shows "s_prefix_sorted_pre \<alpha> T SA"
  unfolding s_prefix_sorted_pre_def
proof(intro allI impI)
  fix b
  let ?xs = "list_slice SA (bucket_start \<alpha> T b) (l_bucket_end \<alpha> T b)"
  let ?ys = "list_slice SA0 (bucket_start \<alpha> T b) (l_bucket_end \<alpha> T b)"
  assume "b \<le> \<alpha> (Max (set T))"
  with s_bucket_ptr_lower_bound[OF assms(1), of b]
  have "l_bucket_end \<alpha> T b \<le> B ! b"
    by (simp add: s_bucket_start_eq_l_bucket_end)
  with s_unchanged_list_slice[OF assms(2-4) `b \<le> \<alpha> (Max (set T))`,
        of "bucket_start \<alpha> T b" "l_bucket_end \<alpha> T b"]
  have "?xs = ?ys"
    by blast
  then show "ordlistns.sorted (map (lms_slice T) ?xs)"
    using \<open>b \<le> \<alpha> (Max (set T))\<close> assms(5) s_prefix_sorted_pre_def by auto
qed

lemma s_next_item_not_seen:
  assumes "s_distinct_inv \<alpha> T B SA"
  and     "s_bucket_ptr_inv \<alpha> T B"
  and     "s_locations_inv \<alpha> T B SA"
  and     "s_unchanged_inv \<alpha> T B SA0 SA"
  and     "s_seen_inv \<alpha> T B SA i"
  and     "s_pred_inv \<alpha> T B SA i"
  and     "strict_mono \<alpha>"
  and     "length SA0 = length T"
  and     "length SA = length T"
  and     "l_types_init \<alpha> T SA0"
  and     "valid_list T"
  and     "\<alpha> bot = 0"
  and     "i = Suc n"
  and     "Suc n < length SA"
  and     "SA ! Suc n = Suc j"
  and     "suffix_type T j = S_type"
  and     "b = \<alpha> (T ! j)"
shows "j \<notin> set (list_slice SA (B ! b) (bucket_end \<alpha> T b))"
proof
  let ?xs = "list_slice SA (B ! b) (bucket_end \<alpha> T b)"
  let ?b = "\<alpha> (T ! (Suc j))"
  assume "j \<in> set ?xs"

  from s_seen_invD(1)[OF assms(5,14)] assms(13,15)
  have "Suc j < length T"
    by simp
  hence "?b \<le> \<alpha> (Max (set T))"
    using assms(7)
    by (simp add: strict_mono_leD)

  have "bucket_end \<alpha> T ?b \<le> length SA"
    by (simp add: assms(9) bucket_end_le_length)
  hence "l_bucket_end \<alpha> T ?b \<le> length SA"
    by (metis dual_order.trans l_bucket_end_le_bucket_end)

  have "j < length T"
    by (simp add: assms(16) suffix_type_s_bound)

  from valid_list_length_ex[OF assms(11)]
  obtain n' where
    "length T = Suc n'"
    by blast
  with `Suc j < length T`
  have "j < n'"
    by linarith
  hence "T ! j \<noteq> bot"
    by (metis \<open>length T = Suc n'\<close> assms(11) diff_Suc_1 valid_list_def)
  hence "b \<noteq> 0"
    using assms(7,12,17) strict_mono_eq by fastforce

  with in_set_conv_nth[THEN iffD1, OF `j \<in> set ?xs`]
  obtain a where
    "a < length ?xs"
    "?xs ! a = j"
    by blast
  hence "SA ! (B ! b + a) = j"
    using nth_list_slice by fastforce

  from assms(9)
  have "bucket_end \<alpha> T b \<le> length SA"
    by (simp add: bucket_end_le_length)
  with `a < length ?xs`
  have "B ! b + a < bucket_end \<alpha> T b"
    by auto
  with assms(7,17) `j < length T`
  have "in_s_current_bucket \<alpha> T B b (B ! b + a)"
    unfolding in_s_current_bucket_def
    by (simp add: strict_mono_less_eq)
  with s_pred_invD[OF assms(6) _ `b \<noteq> 0`, of "B ! b + a"] `SA ! (B ! b + a) = j`
  obtain m where
    "m < length SA"
    "SA ! m = Suc j"
    "B ! b + a < m"
    "i < m"
    by blast
  hence "i \<noteq> m"
    by blast

  have "suffix_type T (Suc j) = L_type \<Longrightarrow> False"
  proof -
    assume "suffix_type T (Suc j) = L_type"
    with s_seen_invD(2)[OF assms(5) `m < length SA`] `i < m` `SA ! m = Suc j`
    have "in_l_bucket \<alpha> T ?b m"
      by simp
    hence "bucket_start \<alpha> T ?b \<le> m" "m < l_bucket_end \<alpha> T ?b"
      using in_l_bucket_def by blast+
    moreover
    from `suffix_type T (Suc j) = L_type` assms(13,15)
         s_seen_invD(2)[OF assms(5) `Suc n < length SA`]
    have "in_l_bucket \<alpha> T ?b i"
      by simp
    hence "bucket_start \<alpha> T ?b \<le> i" "i < l_bucket_end \<alpha> T ?b"
      using in_l_bucket_def by blast+
    ultimately
    show "False"
      using list_slice_nth_eq_iff_index_eq[
              OF l_types_initD(2)[OF l_types_init_maintained[OF assms(2,4,8-10)] `?b \<le> \<alpha> _`]
                `l_bucket_end \<alpha> T ?b \<le> length SA`,
              of i m]
            `i \<noteq> m` assms(13,15) `SA ! m = Suc j`
      by simp
  qed
  moreover
  have "suffix_type T (Suc j) = S_type \<Longrightarrow> False"
  proof -
    assume "suffix_type T (Suc j) = S_type"
    with s_seen_invD(3)[OF assms(5) `m < length SA`] `i < m` `SA ! m = Suc j`
    have "in_s_current_bucket \<alpha> T B ?b m"
      by simp
    hence "B ! ?b \<le> m" "m < bucket_end \<alpha> T ?b"
      using in_s_current_bucket_def by blast+
    moreover
    from `suffix_type T (Suc j) = S_type` assms(13,15)
         s_seen_invD(3)[OF assms(5) `Suc n < length SA`]
    have "in_s_current_bucket \<alpha> T B ?b i"
      by simp
    hence "B ! ?b \<le> i" "i < bucket_end \<alpha> T ?b"
      using in_s_current_bucket_def by blast+
    ultimately
    show False
      using list_slice_nth_eq_iff_index_eq[
              OF s_distinct_invD[OF assms(1) `?b \<le> \<alpha> _`] `bucket_end \<alpha> T ?b \<le> length SA`,
              of i m]
            `i \<noteq> m` assms(13,15) `SA ! m = Suc j`
      by simp
  qed
  ultimately
  show False
    using SL_types.exhaust by blast
qed

lemma s_bucket_ptr_strict_lower_bound:
  assumes "s_distinct_inv \<alpha> T B SA"
  and     "s_bucket_ptr_inv \<alpha> T B"
  and     "s_locations_inv \<alpha> T B SA"
  and     "s_unchanged_inv \<alpha> T B SA0 SA"
  and     "s_seen_inv \<alpha> T B SA i"
  and     "s_pred_inv \<alpha> T B SA i"
  and     "strict_mono \<alpha>"
  and     "length SA0 = length T"
  and     "length SA = length T"
  and     "l_types_init \<alpha> T SA0"
  and     "valid_list T"
  and     "\<alpha> bot = 0"
  and     "i = Suc n"
  and     "Suc n < length SA"
  and     "SA ! Suc n = Suc j"
  and     "suffix_type T j = S_type"
  and     "b = \<alpha> (T ! j)"
shows "s_bucket_start \<alpha> T b < B ! b"
proof -
  have "j < length T"
    by (simp add: assms(16) suffix_type_s_bound)
  hence "b \<le> \<alpha> (Max (set T))"
    by (simp add: assms(7,17) strict_mono_leD)

  let ?xs = "list_slice SA (B ! b) (bucket_end \<alpha> T b)"

  have "bucket_end \<alpha> T b \<le> length SA"
    by (simp add: assms(9) bucket_end_le_length)
  hence "length ?xs = bucket_end \<alpha> T b - B ! b"
    by auto

  from s_next_item_not_seen[OF assms(1-17)]
  have "j \<notin> set ?xs" .
  moreover
  have "j \<in> s_bucket \<alpha> T b"
    by (simp add: assms(16,17) bucket_def s_bucket_def suffix_type_s_bound)
  ultimately
  have "set ?xs \<subset> s_bucket \<alpha> T b"
    using s_locations_inv_subset_s_bucket[OF assms(3) `b \<le> _`]
    by blast
  hence "card (set ?xs) < s_bucket_size \<alpha> T b"
    using psubset_card_mono[OF finite_s_bucket, simplified s_bucket_size_def[symmetric]]
    by blast
  moreover
  from s_distinct_invD[OF assms(1) `b \<le> _`]
  have "distinct ?xs" .
  ultimately
  have "length ?xs < s_bucket_size \<alpha> T b"
    by (simp add: distinct_card)
  with `length ?xs = _`
  have "bucket_end \<alpha> T b - B ! b < s_bucket_size \<alpha> T b"
    by simp
  hence "bucket_end \<alpha> T b < B ! b + s_bucket_size \<alpha> T b"
    by linarith
  hence
    "s_bucket_start \<alpha> T b + bucket_end \<alpha> T b < B ! b + s_bucket_start \<alpha> T b + s_bucket_size \<alpha> T b"
    by simp
  then show "s_bucket_start \<alpha> T b < B ! b"
    by (simp add: bucket_end_eq_s_start_pl_size)
qed

lemma outside_another_bucket:
  assumes "b \<noteq> b'"
  and     "bucket_start \<alpha> T b \<le> i"
  and     "i < bucket_end \<alpha> T b"
shows "\<not>(bucket_start \<alpha> T b' \<le> i \<and> i < bucket_end \<alpha> T b')"
  by (meson assms dual_order.antisym less_bucket_end_le_start not_le order.strict_trans1)

lemma s_B_val:
  assumes "s_distinct_inv \<alpha> T B SA"
  and     "s_bucket_ptr_inv \<alpha> T B"
  and     "s_locations_inv \<alpha> T B SA"
  and     "s_unchanged_inv \<alpha> T B SA0 SA"
  and     "s_seen_inv \<alpha> T B SA i"
  and     "s_pred_inv \<alpha> T B SA i"
  and     "strict_mono \<alpha>"
  and     "length SA0 = length T"
  and     "length SA = length T"
  and     "l_types_init \<alpha> T SA0"
  and     "valid_list T"
  and     "length T > Suc 0"
  and     "b \<le> \<alpha> (Max (set T))"
  and     "i < B ! b"
shows "B ! b = s_bucket_start \<alpha> T b"
proof (rule ccontr; drule neq_iff[THEN iffD1]; elim disjE)
  assume "B ! b < s_bucket_start \<alpha> T b"
  with s_bucket_ptr_lower_bound[OF assms(2,13)]
  show False
    by linarith
next
  let ?k = "B ! b - Suc 0"
  assume "s_bucket_start \<alpha> T b < B ! b"
  hence "s_bucket_start \<alpha> T b \<le> ?k"
    by linarith
  hence "bucket_start \<alpha> T b \<le> ?k"
    using bucket_start_le_s_bucket_start le_trans by blast

  have "?k < B ! b"
    using `s_bucket_start \<alpha> T b < B ! b` by auto

  from assms(14)
  have "i \<le> ?k"
    by linarith

  from s_bucket_ptr_upper_bound[OF assms(2,13)]
  have "B ! b \<le> bucket_end \<alpha> T b" .
  hence "?k < bucket_end \<alpha> T b"
    using \<open>s_bucket_start \<alpha> T b < B ! b\<close> by linarith

  have "bucket_end \<alpha> T b \<le> length SA"
    by (simp add: assms(9) bucket_end_le_length)
  moreover
  have "bucket_end \<alpha> T b = length SA \<Longrightarrow> False"
  proof -
    assume "bucket_end \<alpha> T b = length SA"
    with `s_bucket_start \<alpha> T b < B ! b` `B ! b \<le> bucket_end \<alpha> T b` assms(7,9,13)
    have "b = \<alpha> (Max (set T))"
      using bucket_end_eq_length by fastforce
    hence "s_bucket \<alpha> T b = {}"
      by (simp add: assms(7,11,12) s_bucket_Max)
    hence "s_bucket_size \<alpha> T b = 0"
      by (simp add: s_bucket_size_def)
    hence "s_bucket_start \<alpha> T b = bucket_end \<alpha> T b"
      by (simp add: bucket_end_eq_s_start_pl_size)
    with `B ! b \<le> bucket_end \<alpha> T b` `s_bucket_start \<alpha> T b < B ! b`
    show False
      by simp
  qed
  moreover
  have "bucket_end \<alpha> T b < length SA \<Longrightarrow> False"
  proof -
    assume "bucket_end \<alpha> T b < length SA"
    hence "B ! b < length SA"
      using `B ! b \<le> bucket_end \<alpha> T b`
      by linarith
    hence "?k < length SA"
      using less_imp_diff_less by blast
    with s_seen_invD[OF assms(5) _  `i \<le> ?k`]
    have "SA ! ?k < length T"
      by blast

    let ?b = "\<alpha> (T ! (SA ! ?k))"

    from `SA ! ?k < length T` assms(7)
    have "?b \<le> \<alpha> (Max (set T))"
      using Max_greD strict_mono_leD by blast
    with s_bucket_ptr_lower_bound[OF assms(2)]
    have "s_bucket_start \<alpha> T ?b \<le> B ! ?b"
      by blast
    hence "bucket_start \<alpha> T ?b \<le> B ! ?b"
      using bucket_start_le_s_bucket_start le_trans by blast

    have "suffix_type T (SA ! ?k) = L_type \<Longrightarrow> False"
    proof -
      assume "suffix_type T (SA ! ?k) = L_type"
      with s_seen_invD(2)[OF assms(5) `?k < length SA` `i \<le> ?k`]
      have "in_l_bucket \<alpha> T ?b ?k"
        by blast
      hence "bucket_start \<alpha> T ?b \<le> ?k" "?k < l_bucket_end \<alpha> T ?b"
        using in_l_bucket_def by blast+
      hence "?k < bucket_end \<alpha> T ?b"
        using l_bucket_end_le_bucket_end less_le_trans by blast

      from `?k < l_bucket_end _ _ _` `s_bucket_start _ _ _ \<le> ?k`
      have "b = ?b \<Longrightarrow> False"
        by (simp add: s_bucket_start_eq_l_bucket_end)
      moreover
      from outside_another_bucket[OF _ `bucket_start _ _ b \<le> ?k` `?k < bucket_end _ _ b`]
           `bucket_start _ _ ?b \<le> ?k` `?k < bucket_end _ _ ?b`
      have "b \<noteq> ?b \<Longrightarrow> False"
        by blast
      ultimately show False
        by blast
    qed
    moreover
    have "suffix_type T (SA ! ?k) = S_type \<Longrightarrow> False"
    proof -
      assume "suffix_type T (SA ! ?k) = S_type"
      with s_seen_invD(3)[OF assms(5) `?k < length SA` `i \<le> ?k`]
      have "in_s_current_bucket \<alpha> T B ?b ?k "
        by blast
      hence "B ! ?b \<le> ?k" "?k < bucket_end \<alpha> T ?b"
        using in_s_current_bucket_def by blast+
      hence "bucket_start \<alpha> T ?b \<le> ?k"
        using `bucket_start \<alpha> T ?b \<le> B ! ?b` by linarith

      from `B ! ?b \<le> ?k` `?k < B ! b`
      have "b = ?b \<Longrightarrow> False"
        by simp
      moreover
      from outside_another_bucket[OF _ `bucket_start _ _ b \<le> ?k` `?k < bucket_end _ _ b`]
           `bucket_start \<alpha> T ?b \<le> ?k` `?k < bucket_end \<alpha> T ?b`
      have "b \<noteq> ?b \<Longrightarrow> False"
        by blast
      ultimately show False
        by blast
    qed
    ultimately show False
      using SL_types.exhaust by blast
  qed
  ultimately show False
    by linarith
qed

lemma s_bucket_eq_list_slice:
  assumes "s_distinct_inv \<alpha> T B SA"
  and     "s_locations_inv \<alpha> T B SA"
  and     "length SA = length T"
  and     "b \<le> \<alpha> (Max (set T))"
  and     "B ! b = s_bucket_start \<alpha> T b"
shows "set (list_slice SA (s_bucket_start \<alpha> T b) (bucket_end \<alpha> T b)) = s_bucket \<alpha> T b"
      (is "set ?xs = s_bucket \<alpha> T b")
  using card_subset_eq[
          OF finite_s_bucket s_locations_inv_subset_s_bucket[OF assms(2,4), simplified assms(5)]]
        distinct_card[OF s_distinct_invD[OF assms(1,4), simplified assms(5)]]
        bucket_end_eq_s_start_pl_size[of \<alpha> T b]
        s_bucket_size_def[of \<alpha> T b]
  by (metis assms(3) bucket_end_le_length diff_add_inverse length_list_slice min_def)

lemma bucket_eq_list_slice:
  assumes "s_distinct_inv \<alpha> T B SA"
  and     "s_bucket_ptr_inv \<alpha> T B"
  and     "s_locations_inv \<alpha> T B SA"
  and     "s_unchanged_inv \<alpha> T B SA0 SA"
  and     "length SA0 = length T"
  and     "length SA = length T"
  and     "l_types_init \<alpha> T SA0"
  and     "b \<le> \<alpha> (Max (set T))"
  and     "B ! b = s_bucket_start \<alpha> T b"
shows "set (list_slice SA (bucket_start \<alpha> T b) (bucket_end \<alpha> T b)) = bucket \<alpha> T b"
      (is "set ?xs = bucket \<alpha> T b")
proof -
  let ?ys = "list_slice SA (bucket_start \<alpha> T b) (l_bucket_end \<alpha> T b)"
  and ?zs = "list_slice SA (s_bucket_start \<alpha> T b) (bucket_end \<alpha> T b)"

  have "?xs = ?ys @ ?zs"
    by (metis list_slice_append bucket_start_le_s_bucket_start l_bucket_end_le_bucket_end
          s_bucket_start_eq_l_bucket_end)
  hence "set ?xs = set ?ys \<union> set ?zs"
    by simp
  with l_types_initD(1)[OF l_types_init_maintained[OF assms(2,4-7)] assms(8)]
       s_bucket_eq_list_slice[OF assms(1,3,6,8,9)]
  have "set ?xs = l_bucket \<alpha> T b \<union> s_bucket \<alpha> T b"
    by simp
  then show ?thesis
    using l_un_s_bucket by blast
qed

lemma s_index_lower_bound:
  assumes "s_bucket_ptr_inv \<alpha> T B"
  and     "s_seen_inv \<alpha> T B SA n"
  and     "i < length SA"
  and     "n \<le> i"
shows "bucket_start \<alpha> T (\<alpha> (T ! (SA ! i))) \<le> i"
      (is "bucket_start \<alpha> T ?b \<le> i")
proof -

  have "?b \<le> \<alpha> (Max (set T))"
    by (meson SL_types.exhaust assms(2-) in_l_bucket_def in_s_current_bucketD(1) s_seen_invD(2,3))

  have "suffix_type T (SA ! i) = S_type \<or> suffix_type T (SA ! i) = L_type"
    using SL_types.exhaust by blast
  moreover
  have "suffix_type T (SA ! i) = S_type \<Longrightarrow> ?thesis"
  proof -
    assume "suffix_type T (SA ! i) = S_type"
    with s_seen_invD(3)[OF assms(2-)] s_bucket_ptr_lower_bound[OF assms(1)]
    show ?thesis
      by (meson \<open>?b \<le> \<alpha> (Max (set T))\<close> bucket_start_le_s_bucket_start dual_order.trans
            in_s_current_bucketD(2))
  qed
  moreover
  have "suffix_type T (SA ! i) = L_type \<Longrightarrow> ?thesis"
  proof -
    assume "suffix_type T (SA ! i) = L_type"
    with s_seen_invD(2)[OF assms(2-)]
    show ?thesis
      using in_l_bucket_def by blast
  qed
  ultimately show ?thesis
    by blast
qed

lemma s_index_upper_bound:
  assumes "s_bucket_ptr_inv \<alpha> T B"
  and     "s_seen_inv \<alpha> T B SA n"
  and     "i < length SA"
  and     "n \<le> i"
shows "i < bucket_end \<alpha> T (\<alpha> (T ! (SA ! i)))"
      (is "i < bucket_end \<alpha> T ?b")
proof -

  have "?b \<le> \<alpha> (Max (set T))"
    by (meson SL_types.exhaust assms(2-) in_l_bucket_def in_s_current_bucketD(1) s_seen_invD(2,3))

  have "suffix_type T (SA ! i) = S_type \<or> suffix_type T (SA ! i) = L_type"
    using SL_types.exhaust by blast
  moreover
  have "suffix_type T (SA ! i) = S_type \<Longrightarrow> ?thesis"
  proof -
    assume "suffix_type T (SA ! i) = S_type"
    with s_seen_invD(3)[OF assms(2-)] s_bucket_ptr_upper_bound[OF assms(1)]
    show ?thesis
      by (simp add: in_s_current_bucket_def)
  qed
  moreover
  have "suffix_type T (SA ! i) = L_type \<Longrightarrow> ?thesis"
  proof -
    assume "suffix_type T (SA ! i) = L_type"
    with s_seen_invD(2)[OF assms(2-)]
    show ?thesis
      using in_l_bucket_def l_bucket_end_le_bucket_end less_le_trans by blast
  qed
  ultimately show ?thesis
    by blast
qed

subsection "Establishment and Maintenance Steps"

subsubsection "Distinctness"

lemma s_distinct_inv_established:
  assumes "s_bucket_init \<alpha> T B"
  and     "valid_list T"
  and     "strict_mono \<alpha>"
  and     "\<alpha> bot = 0"
  shows "s_distinct_inv \<alpha> T B SA"
  unfolding s_distinct_inv_def
proof (intro allI impI)
  fix b
  let ?goal = "distinct (list_slice SA (B ! b) (bucket_end \<alpha> T b))"
  assume "b \<le> \<alpha> (Max (set T))"

  have "b > 0 \<Longrightarrow> ?goal"
  proof -
    assume "b > 0"
    with s_bucket_initD(1)[OF assms(1) `b \<le> _`]
    have "B ! b = bucket_end \<alpha> T b"
      by blast
    then show ?goal
      using list_slice_n_n 
      by (metis distinct.simps(1))
  qed
  moreover
  have "b = 0 \<Longrightarrow> ?goal"
  proof -
    assume "b = 0"
    with s_bucket_initD(2)[OF assms(1) `b \<le> _`]
    have "B ! b = 0" .
    moreover
    from `b = 0` assms(2-4)
    have "bucket_end \<alpha> T b = Suc 0"
      by (simp add: valid_list_bucket_end_0)
    ultimately show ?thesis
      by (simp add: distinct_conv_nth)
  qed
  ultimately show ?goal
    by blast
qed

lemma s_distinct_inv_maintained_step:
  assumes "s_distinct_inv \<alpha> T B SA"
  and     "s_bucket_ptr_inv \<alpha> T B"
  and     "s_locations_inv \<alpha> T B SA"
  and     "s_unchanged_inv \<alpha> T B SA0 SA"
  and     "s_seen_inv \<alpha> T B SA i"
  and     "s_pred_inv \<alpha> T B SA i"
  and     "strict_mono \<alpha>"
  and     "\<alpha> (Max (set T)) < length B"
  and     "length SA0 = length T"
  and     "length SA = length T"
  and     "l_types_init \<alpha> T SA0"
  and     "valid_list T"
  and     "\<alpha> bot = 0"
  and     "i = Suc n"
  and     "Suc n < length SA"
  and     "SA ! Suc n = Suc j"
  and     "suffix_type T j = S_type"
  and     "b = \<alpha> (T ! j)"
  and     "k = B ! b - Suc 0"
shows "s_distinct_inv \<alpha> T (B[b := k]) (SA[k := j])"
  unfolding s_distinct_inv_def
proof (intro allI impI)
  fix b'

  let ?goal = "distinct (list_slice (SA[k := j]) (B[b := k] ! b') (bucket_end \<alpha> T b'))"

  assume "b' \<le> \<alpha> (Max (set T))"

  from s_next_item_not_seen[OF assms(1-7,9-18)]
  have "j \<notin> set (list_slice SA (B ! b) (bucket_end \<alpha> T b))".

  from s_bucket_ptr_strict_lower_bound[OF assms(1-7,9-18)]
  have "s_bucket_start \<alpha> T b < B ! b" .
  hence "s_bucket_start \<alpha> T b \<le> k" "k < B ! b"
    using assms(19) by linarith+
  hence "bucket_start \<alpha> T b \<le> k"
    using bucket_start_le_s_bucket_start le_trans by blast

  from assms(17)
  have "j < length T"
    by (simp add: suffix_type_s_bound)
  hence "b \<le> \<alpha> (Max (set T))"
    by (simp add: assms(7,18) strict_mono_less_eq)
  with s_bucket_ptr_upper_bound[OF assms(2)] `k < B ! b`
  have "k < bucket_end \<alpha> T b"
    using less_le_trans by auto
  hence "k < length SA"
    using assms(10) bucket_end_le_length less_le_trans by fastforce

  have "b = b' \<Longrightarrow> ?goal"
  proof -
    assume "b = b'"
    hence "B[b := k] ! b' = k"
      using \<open>b \<le> \<alpha> (Max (set T))\<close> assms(8) by auto
    from s_distinct_invD[OF assms(1) `b \<le> _`]
    have "distinct (list_slice SA (B ! b) (bucket_end \<alpha> T b))" .
    moreover
    from \<open>B[b := k] ! b' = k\<close> \<open>b = b'\<close> \<open>k < B ! b\<close> \<open>k < bucket_end \<alpha> T b\<close> \<open>k < length SA\<close> assms(19)
    have "list_slice (SA[k := j]) (B[b := k] ! b') (bucket_end \<alpha> T b')
          = j # list_slice SA (B ! b) (bucket_end \<alpha> T b)"
      by (metis Suc_pred diff_is_0_eq' dual_order.order_iff_strict gr0I length_list_update
            list_slice_Suc list_slice_update_unchanged_1 nth_list_update_eq)
    ultimately show ?thesis
      using `j \<notin> set (list_slice SA (B ! b) (bucket_end \<alpha> T b))`
      by simp
  qed
  moreover
  have "b \<noteq> b' \<Longrightarrow> ?goal"
  proof -
    assume "b \<noteq> b'"
    hence "B[b := k] ! b' = B ! b'"
      by simp

    from outside_another_bucket[OF `b \<noteq> b'` `bucket_start _ _ _ \<le> k` `k < bucket_end _ _ _`]
    have "k < bucket_start \<alpha> T b' \<or> bucket_end \<alpha> T b' \<le> k"
      using leI by auto
    moreover
    have "k < bucket_start \<alpha> T b' \<Longrightarrow>
          list_slice (SA[k := j]) (B[b := k] ! b') (bucket_end \<alpha> T b')
            = list_slice SA (B ! b') (bucket_end \<alpha> T b')"
    proof -
      assume "k < bucket_start \<alpha> T b'"
      hence "k < B ! b'"
        by (meson \<open>b' \<le> \<alpha> (Max (set T))\<close> assms(2) bucket_start_le_s_bucket_start less_le_trans
              s_bucket_ptr_inv_def)
      with list_slice_update_unchanged_1 `B[b := k] ! b' = B ! b'`
      show ?thesis
        by simp
    qed
    moreover
    from `B[b := k] ! b' = B ! b'`
    have "bucket_end \<alpha> T b' \<le> k \<Longrightarrow>
          list_slice (SA[k := j]) (B[b := k] ! b') (bucket_end \<alpha> T b')
            = list_slice SA (B ! b') (bucket_end \<alpha> T b')"
      by (simp add: list_slice_update_unchanged_2)
    moreover
    from s_distinct_invD[OF assms(1) `b' \<le> _`]
    have "distinct (list_slice SA (B ! b') (bucket_end \<alpha> T b'))" .
    ultimately show ?goal
      by auto
  qed
  ultimately
  show ?goal
    by blast
qed

corollary s_distinct_inv_maintained_perm_step:
  assumes "s_perm_inv \<alpha> T B SA0 SA i"
  and     "i = Suc n"
  and     "Suc n < length SA"
  and     "SA ! Suc n = Suc j"
  and     "suffix_type T j = S_type"
  and     "b = \<alpha> (T ! j)"
  and     "k = B ! b - Suc 0"
shows "s_distinct_inv \<alpha> T (B[b := k]) (SA[k := j])"
  using s_distinct_inv_maintained_step[OF s_perm_inv_elims(1-6,8-14)[OF assms(1)] assms(2-)]
  by blast

subsubsection "Bucket Pointer"

lemma s_bucket_ptr_inv_established:
  assumes "s_bucket_init \<alpha> T B"
  and     "valid_list T"
  and     "strict_mono \<alpha>"
  and     "\<alpha> bot = 0"
  shows "s_bucket_ptr_inv \<alpha> T B"
  unfolding s_bucket_ptr_inv_def
proof(intro allI impI)
  fix b
  let ?goal = "s_bucket_start \<alpha> T b \<le> B ! b \<and> B ! b \<le> bucket_end \<alpha> T b \<and> (b = 0 \<longrightarrow> B ! b = 0)"
  assume "b \<le> \<alpha> (Max (set T))"

  have "b > 0 \<Longrightarrow> ?goal"
  proof -
    assume "b > 0"
    with s_bucket_initD(1)[OF assms(1) `b \<le> _`]
    have "B ! b = bucket_end \<alpha> T b" .
    then show ?thesis
      by (metis \<open>0 < b\<close> l_bucket_end_le_bucket_end less_numeral_extra(3) order_refl
            s_bucket_start_eq_l_bucket_end)
  qed
  moreover
  have "b = 0 \<Longrightarrow> ?goal"
  proof -
    assume "b = 0"
    with s_bucket_initD(2)[OF assms(1) `b \<le> _`]
    have "B ! b = 0" .
    with `b = 0`
         valid_list_bucket_end_0[OF assms(2-)]
         valid_list_s_bucket_start_0[OF assms(2-)]
    show ?thesis
      by auto
  qed
  ultimately show "?goal"
    by auto
qed

lemma s_bucket_ptr_inv_maintained_step:
  assumes "s_distinct_inv \<alpha> T B SA"
  and     "s_bucket_ptr_inv \<alpha> T B"
  and     "s_locations_inv \<alpha> T B SA"
  and     "s_unchanged_inv \<alpha> T B SA0 SA"
  and     "s_seen_inv \<alpha> T B SA i"
  and     "s_pred_inv \<alpha> T B SA i"
  and     "strict_mono \<alpha>"
  and     "\<alpha> (Max (set T)) < length B"
  and     "length SA0 = length T"
  and     "length SA = length T"
  and     "l_types_init \<alpha> T SA0"
  and     "valid_list T"
  and     "\<alpha> bot = 0"
  and     "i = Suc n"
  and     "Suc n < length SA"
  and     "SA ! Suc n = Suc j"
  and     "suffix_type T j = S_type"
  and     "b = \<alpha> (T ! j)"
  and     "k = B ! b - Suc 0"
shows "s_bucket_ptr_inv \<alpha> T (B[b := k])"
  unfolding s_bucket_ptr_inv_def
proof(intro allI impI)
  fix b'
  assume "b' \<le> \<alpha> (Max (set T))"

  let ?goal = "s_bucket_start \<alpha> T b' \<le> B[b := k] ! b' \<and>  B[b := k] ! b' \<le> bucket_end \<alpha> T b' \<and>
               (b' = 0 \<longrightarrow> B[b := k] ! b' = 0)"

  from valid_list_length_ex[OF assms(12)]
  obtain m where
    "length T = Suc m"
    by blast
  moreover
  have "j < length T"
    by (simp add: assms(17) suffix_type_s_bound)
  moreover
  from s_seen_invD(1)[OF assms(5,15)] assms(14,16)
  have "Suc j < length T"
    by simp
  ultimately have "j < m"
    by linarith
  hence "b \<noteq> 0"
    by (metis  \<open>length T = Suc m\<close> assms(7,12,13,18) diff_Suc_1 strict_mono_eq valid_list_def)

  have "b \<noteq> b' \<Longrightarrow> ?goal"
  proof -
    assume "b \<noteq> b'"
    hence "B[b := k] ! b' = B ! b'"
      by simp
    with s_bucket_ptr_lower_bound[OF assms(2) `b' \<le> \<alpha> (Max (set T))`]
         s_bucket_ptr_upper_bound[OF assms(2) `b' \<le> \<alpha> (Max (set T))`]
         s_bucket_ptr_0[OF assms(2)]
    show ?thesis
      by auto
  qed
  moreover
  have "b = b' \<Longrightarrow> ?goal"
  proof -
    assume "b = b'"
    from s_bucket_ptr_strict_lower_bound[OF assms(1-7,9-13,14-18)]
    have "s_bucket_start \<alpha> T b < B ! b".
    hence "s_bucket_start \<alpha> T b \<le> k"
      using assms(19) by linarith
    moreover
    from \<open>b = b'\<close> \<open>b' \<le> \<alpha> (Max (set T))\<close> assms(2,19)
    have "k \<le> bucket_end \<alpha> T b"
      using le_diff_conv s_bucket_ptr_inv_def trans_le_add1 by blast
    moreover
    have "B[b := k] ! b' = k"
      using \<open>b = b'\<close> \<open>b' \<le> \<alpha> (Max (set T))\<close> assms(8) by auto
    ultimately show ?thesis
      using \<open>b = b'\<close> \<open>b \<noteq> 0\<close> by auto
  qed
  ultimately show ?goal
    by linarith
qed

corollary s_bucket_ptr_inv_maintained_perm_step:
  assumes "s_perm_inv \<alpha> T B SA0 SA i"
  and     "i = Suc n"
  and     "Suc n < length SA"
  and     "SA ! Suc n = Suc j"
  and     "suffix_type T j = S_type"
  and     "b = \<alpha> (T ! j)"
  and     "k = B ! b - Suc 0"
shows "s_bucket_ptr_inv \<alpha> T (B[b := k])"
  using s_bucket_ptr_inv_maintained_step[OF s_perm_inv_elims(1-6,8-14)[OF assms(1)] assms(2-)]
  by blast

subsubsection "Locations"

lemma s_locations_inv_established:
  assumes "s_bucket_init \<alpha> T B"
  and     "s_type_init T SA"
  and     "valid_list T"
  and     "strict_mono \<alpha>"
  and     "\<alpha> bot = 0"
  shows "s_locations_inv \<alpha> T B SA"
  unfolding s_locations_inv_def
proof(safe)
  fix b i
  assume "b \<le> \<alpha> (Max (set T))" "B ! b \<le> i" "i < bucket_end \<alpha> T b"
  hence "b > 0 \<Longrightarrow> SA ! i \<in> s_bucket \<alpha> T b"
    by (metis assms(1) not_le s_bucket_init_def)
  moreover
  have "b = 0 \<Longrightarrow> SA ! i \<in> s_bucket \<alpha> T b"
  proof -
    assume "b = 0"
    have "0 \<le> i"
      by blast
    moreover
    have "bucket_end \<alpha> T 0 = 1"
      using assms(3-5) valid_list_bucket_end_0 by blast
    with `i < bucket_end \<alpha> T b` `b = 0`
    have "i < 1"
      by simp
    ultimately have "i = 0"
      by blast
    moreover
    from s_type_init_def[of T SA] assms(2)
    obtain n where
      "length T = Suc n"
      "SA ! 0 = n"
      by blast
    with suffix_type_last[of T n]
    have "suffix_type T n = S_type"
      by blast
    moreover
    have "T ! n = bot"
      by (metis \<open>length T = Suc n\<close> assms(3) diff_Suc_1 last_conv_nth less_numeral_extra(3)
            list.size(3) valid_list_def)
    hence "\<alpha> (T ! n) = 0"
      by (simp add: assms(5))
    ultimately show ?thesis
      by (simp add: \<open>SA ! 0 = n\<close>\<open>b = 0\<close> \<open>length T = Suc n\<close> bucket_def s_bucket_def)
  qed
  ultimately show "SA ! i \<in> s_bucket \<alpha> T b"
    by linarith
qed

lemma s_locations_inv_maintained_step:
  assumes "s_distinct_inv \<alpha> T B SA"
  and     "s_bucket_ptr_inv \<alpha> T B"
  and     "s_locations_inv \<alpha> T B SA"
  and     "s_unchanged_inv \<alpha> T B SA0 SA"
  and     "s_seen_inv \<alpha> T B SA i"
  and     "s_pred_inv \<alpha> T B SA i"
  and     "strict_mono \<alpha>"
  and     "\<alpha> (Max (set T)) < length B"
  and     "length SA0 = length T"
  and     "length SA = length T"
  and     "l_types_init \<alpha> T SA0"
  and     "valid_list T"
  and     "\<alpha> bot = 0"
  and     "i = Suc n"
  and     "Suc n < length SA"
  and     "SA ! Suc n = Suc j"
  and     "suffix_type T j = S_type"
  and     "b = \<alpha> (T ! j)"
  and     "k = B ! b - Suc 0"
shows "s_locations_inv \<alpha> T (B[b := k]) (SA[k := j])"
  unfolding s_locations_inv_def
proof(safe)
  fix b' i'
  assume "b' \<le> \<alpha> (Max (set T))" "B[b := k] ! b' \<le> i'" "i' < bucket_end \<alpha> T b'"

  from s_bucket_ptr_strict_lower_bound[OF assms(1-7,9-18)]
  have "s_bucket_start \<alpha> T b < B ! b".
  hence "s_bucket_start \<alpha> T b \<le> k"
    using assms(19) by linarith

  from `s_bucket_start \<alpha> T b < B ! b`
  have "k < B ! b"
    using assms(19) by linarith

  have "j < length T"
    by (simp add: assms(17) suffix_type_s_bound)
  hence "b \<le> \<alpha> (Max (set T))"
    by (simp add: assms(18) assms(7) strict_mono_less_eq)
  with s_bucket_ptr_upper_bound[OF assms(2)]
  have "B ! b \<le> bucket_end \<alpha> T b"
    by blast

  have "b \<noteq> b' \<Longrightarrow> SA[k := j] ! i' \<in> s_bucket \<alpha> T b'"
  proof -
    assume "b \<noteq> b'"
    hence "B[b := k] ! b' = B ! b'"
      by simp
    with `B[b := k] ! b' \<le> i'`
    have "B ! b' \<le> i'"
      by simp
    with s_locations_invD[OF assms(3) `b' \<le> \<alpha> (Max (set T))` _ `i' < bucket_end \<alpha> T b'`]
    have "SA ! i' \<in> s_bucket \<alpha> T b'"
      by linarith
    moreover
    from s_bucket_ptr_lower_bound[OF assms(2) `b' \<le> \<alpha> (Max (set T))`] `B ! b' \<le> i'`
    have "bucket_start \<alpha> T b' \<le> i'"
      by (meson bucket_start_le_s_bucket_start dual_order.trans)
    with outside_another_bucket[OF `b \<noteq> b'`[symmetric] _ `i' < _`]
         \<open>B ! b \<le> bucket_end \<alpha> T b\<close> \<open>k < B ! b\<close> \<open>s_bucket_start \<alpha> T b \<le> k\<close>
    have "k \<noteq> i'"
      using bucket_start_le_s_bucket_start le_trans less_le_trans by blast
    hence "SA[k := j] ! i' = SA ! i'"
      by simp
    ultimately show ?thesis
      by simp
  qed
  moreover
  have "b = b' \<Longrightarrow> SA[k := j] ! i' \<in> s_bucket \<alpha> T b'"
  proof -
    assume "b = b'"
    hence "k \<le> i'"
      using \<open>B[b := k] ! b' \<le> i'\<close> \<open>b' \<le> \<alpha> (Max (set T))\<close> assms(8) by auto
    hence "k = i' \<or> k < i'"
      by linarith
    moreover
    have "k = i' \<Longrightarrow> ?thesis"
    proof -
      assume "k = i'"
      hence "SA[k := j] ! i' = j"
        by (metis \<open>i' < bucket_end \<alpha> T b'\<close> assms(10) bucket_end_le_length dual_order.strict_trans1
              nth_list_update)
      with assms(17,18) `b = b'` `j < length T`
      show ?thesis
        by (simp add: bucket_def s_bucket_def)
    qed
    moreover
    have "k < i' \<Longrightarrow> ?thesis"
    proof -
      assume "k < i'"
      hence "B ! b \<le> i'"
        using assms(19) by linarith
      with s_locations_invD[OF assms(3) `b' \<le> _` _ `i' < bucket_end _ _ _`] `b = b'`
      have "SA ! i' \<in> s_bucket \<alpha> T b'"
        by blast
      moreover
      have "SA[k := j] ! i' = SA ! i'"
        using \<open>k < i'\<close> by auto
      ultimately show ?thesis
        by simp
    qed
    ultimately show ?thesis
      by linarith
  qed
  ultimately show "SA[k := j] ! i' \<in> s_bucket \<alpha> T b'"
    by blast
qed

corollary s_locations_inv_maintained_perm_step:
  assumes "s_perm_inv \<alpha> T B SA0 SA i"
  and     "i = Suc n"
  and     "Suc n < length SA"
  and     "SA ! Suc n = Suc j"
  and     "suffix_type T j = S_type"
  and     "b = \<alpha> (T ! j)"
  and     "k = B ! b - Suc 0"
shows "s_locations_inv \<alpha> T (B[b := k]) (SA[k := j])"
  using s_locations_inv_maintained_step[OF s_perm_inv_elims(1-6,8-14)[OF assms(1)] assms(2-)]
  by blast

subsubsection "Unchanged"

lemma s_unchanged_inv_established:
  shows "s_unchanged_inv \<alpha> T B SA SA"
  by (simp add: s_unchanged_inv_def)

lemma s_unchanged_inv_maintained_step:
  assumes "s_distinct_inv \<alpha> T B SA"
  and     "s_bucket_ptr_inv \<alpha> T B"
  and     "s_locations_inv \<alpha> T B SA"
  and     "s_unchanged_inv \<alpha> T B SA0 SA"
  and     "s_seen_inv \<alpha> T B SA i"
  and     "s_pred_inv \<alpha> T B SA i"
  and     "strict_mono \<alpha>"
  and     "\<alpha> (Max (set T)) < length B"
  and     "length SA0 = length T"
  and     "length SA = length T"
  and     "l_types_init \<alpha> T SA0"
  and     "valid_list T"
  and     "\<alpha> bot = 0"
  and     "i = Suc n"
  and     "Suc n < length SA"
  and     "SA ! Suc n = Suc j"
  and     "suffix_type T j = S_type"
  and     "b = \<alpha> (T ! j)"
  and     "k = B ! b - Suc 0"
shows "s_unchanged_inv \<alpha> T (B[b := k]) SA0 (SA[k := j])"
  unfolding s_unchanged_inv_def
proof(safe)
  fix b' i'
  assume "b' \<le> \<alpha> (Max (set T))" "bucket_start \<alpha> T b' \<le> i'" "i' < B[b := k] ! b'"

  from s_bucket_ptr_strict_lower_bound[OF assms(1-7,9-18)]
  have "s_bucket_start \<alpha> T b < B ! b".
  hence "s_bucket_start \<alpha> T b \<le> k"
    using assms(19) by linarith
  hence "bucket_start \<alpha> T b \<le> k"
    using bucket_start_le_s_bucket_start le_trans by blast

  from `s_bucket_start \<alpha> T b < B ! b`
  have "k < B ! b"
    using assms(19) by linarith

  have "j < length T"
    by (simp add: assms(17) suffix_type_s_bound)
  hence "b \<le> \<alpha> (Max (set T))"
    by (simp add: assms(7,18) strict_mono_less_eq)
  with s_bucket_ptr_upper_bound[OF assms(2)]
  have "B ! b \<le> bucket_end \<alpha> T b"
    by blast
  with `k < B ! b`
  have "k < bucket_end \<alpha> T b"
    by linarith

  have "b = b' \<Longrightarrow> SA[k := j] ! i' = SA0 ! i'"
  proof -
    assume "b = b'"
    hence "B[b := k] ! b' = k"
      using \<open>b' \<le> \<alpha> (Max (set T))\<close> assms(8) by auto
    with `i' < B[b := k] ! b'`
    have "i' < k"
      by linarith
    hence "SA[k := j] ! i' = SA ! i'"
      by simp
    moreover
    from `i' < k` `k < B ! b` `b = b'`
    have "i' < B ! b'"
      by simp
    with s_unchanged_invD[OF assms(4) `b' \<le> _` `bucket_start _ _ _ \<le> i'`]
    have "SA ! i' = SA0 ! i'"
      by simp
    ultimately show ?thesis
      by simp
  qed
  moreover
  have "b \<noteq> b' \<Longrightarrow> SA[k := j] ! i' = SA0 ! i'"
  proof -
    assume "b \<noteq> b'"
    with `i' < B[b := k] ! b'`
    have "i' < B ! b'"
      by simp
    with s_unchanged_invD[OF assms(4) `b' \<le> _` `bucket_start _ _ b' \<le> _`]
    have "SA ! i' = SA0 ! i'"
      by blast
    moreover
    from s_bucket_ptr_upper_bound[OF assms(2) `b' \<le> _`] `i' < B ! b'`
    have "i' < bucket_end \<alpha> T b'"
      by linarith
    with outside_another_bucket[OF `b \<noteq> b'` `bucket_start _ _ _ \<le> k` `k < bucket_end _ _ _`]
         `bucket_start _ _ b' \<le> i'`
    have "k \<noteq> i'"
      by blast
    hence "SA[k := j] ! i' = SA ! i'"
      by simp
    ultimately show ?thesis
      by simp
  qed
  ultimately show "SA[k := j] ! i' = SA0 ! i'"
    by blast
qed

corollary s_unchanged_inv_maintained_perm_step:
  assumes "s_perm_inv \<alpha> T B SA0 SA i"
  and     "i = Suc n"
  and     "Suc n < length SA"
  and     "SA ! Suc n = Suc j"
  and     "suffix_type T j = S_type"
  and     "b = \<alpha> (T ! j)"
  and     "k = B ! b - Suc 0"
shows "s_unchanged_inv \<alpha> T (B[b := k]) SA0 (SA[k := j])"
  using s_unchanged_inv_maintained_step[OF s_perm_inv_elims(1-6,8-14)[OF assms(1)] assms(2-)]
  by blast

subsubsection "Seen"

lemma s_seen_inv_established:
  assumes "length SA = length T"
  and     "length T \<le> n"
shows "s_seen_inv \<alpha> T B SA n"
  unfolding s_seen_inv_def
  using assms by auto

lemma s_seen_inv_maintained_step_c1:
  assumes "s_bucket_ptr_inv \<alpha> T B"
  and     "s_unchanged_inv \<alpha> T B SA0 SA"
  and     "s_seen_inv \<alpha> T B SA i"
  and     "strict_mono \<alpha>"
  and     "length SA0 = length T"
  and     "length SA = length T"
  and     "l_types_init \<alpha> T SA0"
  and     "valid_list T"
  and     "Suc 0 < length T"
  and     "i = Suc n"
  and     "length SA \<le> Suc n"
  shows "s_seen_inv \<alpha> T B SA n"
  unfolding s_seen_inv_def
proof (intro allI impI)
  fix j
  assume "j < length SA" "n \<le> j"
  hence "n < length SA"
    by simp
  with assms(10,11)
  have "length SA = Suc n"
    by linarith

  let ?b = "\<alpha> (T ! (SA ! j))"
  let ?g1 = "(suffix_type T (SA ! j) = S_type \<longrightarrow> in_s_current_bucket \<alpha> T B ?b j)"
  and ?g2 = "(suffix_type T (SA ! j) = L_type \<longrightarrow> in_l_bucket \<alpha> T ?b j)"
  and ?g3 = "SA ! j < length T"

  from `n \<le> j`
  have "n = j \<or> Suc n \<le> j"
    using dual_order.antisym not_less_eq_eq by auto
  moreover
  have "n = j \<Longrightarrow> ?g1 \<and> ?g2 \<and> ?g3"
  proof -
    let ?b_max = "\<alpha> (Max (set T))"
    assume "n = j"
    hence "j < bucket_end \<alpha> T ?b_max"
      using \<open>j < length SA\<close> assms(4,6) bucket_end_Max by fastforce
    hence "j < l_bucket_end \<alpha> T ?b_max"
      using l_bucket_Max[OF assms(8,9,4)]
      by (simp add: bucket_end_def' bucket_size_def l_bucket_end_def l_bucket_size_def)
    moreover
    from \<open>n = j\<close> \<open>j < length SA\<close> \<open>length SA = Suc n\<close> assms(4,6,10)
    have "bucket_start \<alpha> T ?b_max \<le> j"
      by (metis Suc_leI antisym bucket_end_eq_length bucket_end_le_length gr_implies_not0
                index_in_bucket_interval_gen length_0_conv)
    moreover
    have "?b_max \<le> \<alpha> (Max (set T))"
      by simp
    ultimately have "SA ! j \<in> l_bucket \<alpha> T ?b_max"
      using l_types_init_nth[OF assms(6) l_types_init_maintained[OF assms(1,2,5-7)] ]
      by blast
    hence "?b_max = \<alpha> (T ! (SA ! j))"
      by (simp add: bucket_def l_bucket_def)
    moreover
    from `SA ! j \<in> l_bucket \<alpha> T ?b_max`
    have ?g3
      by (simp add: bucket_def l_bucket_def)
    moreover
    from `SA ! j \<in> l_bucket \<alpha> T ?b_max`
    have "suffix_type T (SA ! j) = L_type"
      by (simp add: bucket_def l_bucket_def)
    moreover
    have "in_l_bucket \<alpha> T (\<alpha> (T ! (SA ! j))) j"
      using \<open>bucket_start _ _ _  \<le> j\<close> \<open>j < l_bucket_end _ _ _\<close> calculation(1) in_l_bucket_def
      by fastforce
    hence "?g2"
      using calculation(3) by blast
    moreover
    from calculation(3)
    have "?g1"
      by simp
    ultimately show ?thesis
      by simp
  qed
  moreover
  have "Suc n \<le> j \<Longrightarrow> ?g1 \<and> ?g2 \<and> ?g3"
  proof -
    assume "Suc n \<le> j"
    with s_seen_invD[OF assms(3) `j < length SA`] assms(10)
    show ?thesis
      by blast
  qed
  ultimately show "?g1 \<and> ?g2 \<and> ?g3"
    by blast
qed

corollary s_seen_inv_maintained_perm_step_c1:
  assumes "s_perm_inv \<alpha> T B SA0 SA i"
  and     "i = Suc n"
  and     "length SA \<le> Suc n"
  shows "s_seen_inv \<alpha> T B SA n"
  using s_seen_inv_maintained_step_c1[OF s_perm_inv_elims(2,4,5,8,10-13,15)[OF assms(1)] assms(2-)]
  by blast

lemma s_seen_inv_maintained_step_c1_alt:
  assumes "s_bucket_ptr_inv \<alpha> T B"
  and     "s_unchanged_inv \<alpha> T B SA0 SA"
  and     "s_seen_inv \<alpha> T B SA i"
  and     "strict_mono \<alpha>"
  and     "length SA0 = length T"
  and     "length SA = length T"
  and     "l_types_init \<alpha> T SA0"
  and     "valid_list T"
  and     "Suc 0 < length T"
  and     "i = Suc n"
  and     "length T \<le> SA ! Suc n"
  shows "s_seen_inv \<alpha> T B SA n"
proof (cases "length SA \<le> Suc n")
  assume "length SA \<le> Suc n"
  then show ?thesis
    using assms(1-10) s_seen_inv_maintained_step_c1 by blast
next
  assume "\<not> length SA \<le> Suc n"
  hence "Suc n < length SA"
    by simp
  show ?thesis
    unfolding s_seen_inv_def
  proof (intro allI impI)
    fix j
    assume "j < length SA" "n \<le> j"
    hence "n < length SA"
      by simp

    let ?b = "\<alpha> (T ! (SA ! j))"
    let ?g1 = "(suffix_type T (SA ! j) = S_type \<longrightarrow> in_s_current_bucket \<alpha> T B ?b j)"
    and ?g2 = "(suffix_type T (SA ! j) = L_type \<longrightarrow> in_l_bucket \<alpha> T ?b j)"
    and ?g3 = "SA ! j < length T"
  
   from `n \<le> j`
    have "n = j \<or> Suc n \<le> j"
      using dual_order.antisym not_less_eq_eq by auto
    moreover
    have "n = j \<Longrightarrow> ?g1 \<and> ?g2 \<and> ?g3"
      by (metis Suc_le_mono \<open>Suc n < length SA\<close> \<open>n \<le> j\<close> assms(3,10,11) linorder_not_le
                s_seen_invD(1))
    moreover
    have "Suc n \<le> j \<Longrightarrow> ?g1 \<and> ?g2 \<and> ?g3"
    proof -
      assume "Suc n \<le> j"
      with s_seen_invD[OF assms(3) `j < length SA`] assms(10)
      show ?thesis
        by blast
    qed
    ultimately show "?g1 \<and> ?g2 \<and> ?g3"
      by blast
  qed
qed

corollary s_seen_inv_maintained_perm_step_c1_alt:
  assumes "s_perm_inv \<alpha> T B SA0 SA i"
  and     "i = Suc n"
  and     "length T \<le> SA ! Suc n"
  shows "s_seen_inv \<alpha> T B SA n"
  using s_seen_inv_maintained_step_c1_alt[OF s_perm_inv_elims(2,4,5,8,10-13,15)[OF assms(1)] assms(2-)]
  by blast

lemma s_seen_inv_maintained_step_c2:
  assumes "s_distinct_inv \<alpha> T B SA"
  and     "s_bucket_ptr_inv \<alpha> T B"
  and     "s_locations_inv \<alpha> T B SA"
  and     "s_unchanged_inv \<alpha> T B SA0 SA"
  and     "s_seen_inv \<alpha> T B SA i"
  and     "s_pred_inv \<alpha> T B SA i"
  and     "s_suc_inv \<alpha> T B SA i"
  and     "strict_mono \<alpha>"
  and     "\<alpha> (Max (set T)) < length B"
  and     "length SA0 = length T"
  and     "length SA = length T"
  and     "l_types_init \<alpha> T SA0"
  and     "valid_list T"
  and     "\<alpha> bot = 0"
  and     "Suc 0 < length T"
  and     "i = Suc n"
  and     "Suc n < length SA"
  and     "SA ! Suc n = 0"
  shows "s_seen_inv \<alpha> T B SA n"
 unfolding s_seen_inv_def
proof (intro allI impI)
  fix j
  assume "j < length SA" "n \<le> j"
  hence "n < length SA"
    by simp
  hence "n < length T"
    by (simp add: assms(11))


  let ?b = "\<alpha> (T ! (SA ! j))"
  let ?g1 = "(suffix_type T (SA ! j) = S_type \<longrightarrow> in_s_current_bucket \<alpha> T B ?b j)"
  and ?g2 = "(suffix_type T (SA ! j) = L_type \<longrightarrow> in_l_bucket \<alpha> T ?b j)"
  and ?g3 = "SA ! j < length T"

 from `n \<le> j`
  have "n = j \<or> Suc n \<le> j"
    by linarith
  moreover
  have "n = j \<Longrightarrow> ?g1 \<and> ?g2 \<and> ?g3"
  proof -
    assume "n = j"
    with index_in_bucket_interval_gen[OF `n < length T` assms(8)]
    obtain b where
      "b \<le> \<alpha> (Max (set T))"
      "bucket_start \<alpha> T b \<le> j"
      "j < bucket_end \<alpha> T b"
      by blast

    have "j < l_bucket_end \<alpha> T b \<or> s_bucket_start \<alpha> T b \<le> j"
      by (metis not_le s_bucket_start_eq_l_bucket_end)
    moreover
    have "j < l_bucket_end \<alpha> T b \<Longrightarrow> ?thesis"
    proof -
      assume "j < l_bucket_end \<alpha> T b"
      with l_types_init_nth[OF assms(11) l_types_init_maintained[OF assms(2,4,10-12)] `b \<le> _`
            `bucket_start _ _ _ \<le> j`]
      have "SA ! j \<in> l_bucket \<alpha> T b" .
      hence "suffix_type T (SA ! j) = L_type" "SA ! j < length T"
        by (simp add: l_bucket_def bucket_def)+
      moreover
      have ?g1
        by(simp add: calculation(1) SL_types.exhaust)
      moreover
      from `SA ! j \<in> l_bucket \<alpha> T b`
      have "b = \<alpha> (T ! (SA ! j))"
        by (metis (mono_tags, lifting)  bucket_def l_bucket_def mem_Collect_eq)
      with `bucket_start \<alpha> T b \<le> j` `j < l_bucket_end \<alpha> T b` `b \<le> _`
      have "in_l_bucket \<alpha> T (\<alpha> (T ! (SA ! j))) j"
        using in_l_bucket_def by blast
      ultimately show ?thesis
        by blast
    qed
    moreover
    have "s_bucket_start \<alpha> T b \<le> j \<Longrightarrow> ?thesis"
    proof -
      assume "s_bucket_start \<alpha> T b \<le> j"
      hence "s_bucket_start \<alpha> T b < i"
        by (simp add: \<open>n = j\<close> assms(16))

      have "B ! b \<le> i"
      proof(rule ccontr)
        assume "\<not>B ! b \<le> i"
        hence "i < B ! b"
          by simp
        with s_B_val[OF assms(1-6,8,10-13,15) `b \<le> \<alpha> _`]
        have "B ! b = s_bucket_start \<alpha> T b" .
        with `s_bucket_start \<alpha> T b < i` `i < B ! b`
        show False
          by linarith
      qed
      hence "B ! b < i \<or> B ! b = i"
        using dual_order.order_iff_strict by blast
      moreover
      have "B ! b < i \<Longrightarrow> ?thesis"
      proof -
        assume "B ! b < i"
        hence "B ! b \<le> j"
          by (simp add: \<open>n = j\<close> assms(16))
        with s_locations_invD[OF assms(3) `b \<le> _` _ `j < bucket_end _ _ _`]
        have "SA ! j \<in> s_bucket \<alpha> T b" .
        hence "SA ! j < length T" "suffix_type T (SA ! j) = S_type"
          by (simp add: s_bucket_def bucket_def)+
        moreover
        from calculation(2)
        have ?g2
          by simp
        moreover
        from `SA ! j \<in> s_bucket \<alpha> T b`
        have "\<alpha> (T ! (SA ! j)) = b"
          by (simp add: s_bucket_def bucket_def)
        with `B ! b \<le> j` `j < bucket_end \<alpha> T b` `b \<le> _`
        have "in_s_current_bucket \<alpha> T B (\<alpha> (T ! (SA ! j))) j"
          by (simp add: in_s_current_bucket_def)
        ultimately show ?thesis
          by blast
      qed
      moreover
      have "B ! b = i \<Longrightarrow> ?thesis"
      proof -
        assume "B ! b = i"
        hence "s_bucket_start \<alpha> T b < B ! b"
          using \<open>s_bucket_start \<alpha> T b < i\<close> by blast

        have "b \<noteq> 0"
          using \<open>B ! b = i\<close> assms(2,16) less_Suc_eq_0_disj s_bucket_ptr_0 by fastforce

        let ?xs = "list_slice SA (B ! b) (bucket_end \<alpha> T b)"
        let ?B = "set ?xs"
        let ?A = "s_bucket \<alpha> T b - ?B"

       from s_locations_inv_subset_s_bucket[OF assms(3) `b \<le> _`]
        have "?B \<subseteq> s_bucket \<alpha> T b" .
        hence "?A \<subseteq> s_bucket \<alpha> T b"
          by blast

        have "card (s_bucket \<alpha> T b) = bucket_end \<alpha> T b - s_bucket_start \<alpha> T b"
          by (simp add: bucket_end_eq_s_start_pl_size s_bucket_size_def)

        from s_distinct_invD[OF assms(1) `b \<le> _`]
        have "card ?B = bucket_end \<alpha> T b - B ! b"
          by (metis assms(11) bucket_end_le_length distinct_card length_list_slice min.absorb_iff1)
        hence "card ?B < card (s_bucket \<alpha> T b)"
          using \<open>card (s_bucket \<alpha> T b) = bucket_end \<alpha> T b - s_bucket_start \<alpha> T b\<close>
                \<open>j < bucket_end \<alpha> T b\<close> \<open>s_bucket_start \<alpha> T b < B ! b\<close> \<open>s_bucket_start \<alpha> T b \<le> j\<close>
          by linarith
        with card_psubset[OF finite_s_bucket `?B \<subseteq> s_bucket \<alpha> T b`]
        have "?B \<subset> s_bucket \<alpha> T b" .
        hence "?A \<noteq> {}"
          by blast
        with subset_s_bucket_successor[OF assms(13,8,14) `b \<noteq> _` `?A \<subseteq> _`]
        obtain x where
          "x \<in> ?A"
          "Suc x \<in> ?B \<or> (\<exists>b'. b < b' \<and> Suc x \<in> bucket \<alpha> T b')"
          by blast
        hence "suffix_type T x = S_type" "\<alpha> (T ! x) = b" "x < length T"
          by (simp add: s_bucket_def bucket_def)+

        from `x \<in> ?A`
        have "x \<notin> ?B"
          by blast

        have "Suc x \<in> ?B \<Longrightarrow> ?thesis"
        proof -
          assume "Suc x \<in> ?B"
          from nth_mem_list_slice[OF `Suc x \<in> ?B`]
          obtain i' where
            "i' < length SA"
            "B ! b \<le> i'"
            "i' < bucket_end \<alpha> T b"
            "SA ! i' = Suc x"
            by blast

          have "i \<noteq> i'"
          proof (rule ccontr)
            assume "\<not> i \<noteq> i'"
            hence "i = i'"
              by auto
            with assms(16,18) `SA ! i' = Suc x`
            show False
              by simp
          qed
          with `B ! b = i` `B ! b \<le> i'`
          have "i < i'"
            by simp
          with s_suc_invD[OF assms(7) `i' < length SA` _ `SA ! i' = Suc x` `suffix_type T x = _`,
                simplified `\<alpha> (T ! x) = b`]
          obtain k where
            "in_s_current_bucket \<alpha> T B b k"
            "SA ! k = x"
            "k < i'"
            by blast
          hence "x \<in> ?B"
            by (meson assms(11) in_s_current_bucket_list_slice)
          with `x \<notin> ?B`
          have False
            by blast
          then show ?thesis
            by blast
        qed
        moreover
        have "\<exists>b'. b < b' \<and> Suc x \<in> bucket \<alpha> T b' \<Longrightarrow> ?thesis"
        proof -
          assume "\<exists>b'. b < b' \<and> Suc x \<in> bucket \<alpha> T b'"
          then obtain b' where
            "b < b'"
            "Suc x \<in> bucket \<alpha> T b'"
            by blast
          hence "bucket_end \<alpha> T b \<le> bucket_start \<alpha> T b'"
            by (simp add: less_bucket_end_le_start)
          with s_bucket_ptr_upper_bound[OF assms(2) `b \<le> _ `] `B ! b = i`
          have "i \<le> bucket_start \<alpha> T b'"
            by linarith

          from \<open>Suc x \<in> bucket \<alpha> T b'\<close>
          have "b' \<le> \<alpha> (Max (set T))"
            by (metis (mono_tags, lifting) Max_greD assms(8) bucket_def mem_Collect_eq
                  strict_mono_less_eq)
          with `i \<le> bucket_start \<alpha> T b'` s_bucket_ptr_lower_bound[OF assms(2), of b']
          have "i \<le> B ! b'"
            by (metis nat_le_iff_add s_bucket_start_def trans_le_add1)
          hence "i = B ! b' \<or> i < B ! b'"
            using antisym_conv1 by blast
          hence "B ! b' = s_bucket_start \<alpha> T b'"
          proof
            assume "i = B ! b'"
            with `i \<le> bucket_start \<alpha> T b'` s_bucket_ptr_lower_bound[OF assms(2) `b' \<le> _`]
            show ?thesis
              by (simp add: s_bucket_start_def)
          next
            assume "i < B ! b'"
            with s_B_val[OF assms(1-6,8,10-13,15) `b' \<le> _`]
            show ?thesis .
          qed

          from `Suc x \<in> bucket \<alpha> T b'`
          have "Suc x \<in> l_bucket \<alpha> T b' \<or> Suc x \<in> s_bucket \<alpha> T b'"
            by (simp add: l_un_s_bucket)
          moreover
          have "Suc x \<in> l_bucket \<alpha> T b' \<Longrightarrow> ?thesis"
          proof -
            assume "Suc x \<in> l_bucket \<alpha> T b'"
            with l_types_initD(1)[OF l_types_init_maintained[OF assms(2,4,10-12)] `b' \<le> _`]
            have "Suc x \<in> set (list_slice SA (bucket_start \<alpha> T b') (l_bucket_end \<alpha> T b'))"
              by simp
            with nth_mem_list_slice[of "Suc x" SA "bucket_start \<alpha> T b'" "l_bucket_end \<alpha> T b'"]
            obtain i' where
              "i' < length SA"
              "bucket_start \<alpha> T b' \<le> i'"
              "i' < l_bucket_end \<alpha> T b'"
              "SA ! i' = Suc x"
              by blast

            have "i \<noteq> i'"
            proof (rule ccontr)
              assume "\<not> i \<noteq> i'"
              hence "i = i'"
                by auto
              with `SA ! i' = Suc x` assms(16,18)
              show False
                by simp
            qed
            hence "i < i'"
              using \<open>bucket_start \<alpha> T b' \<le> i'\<close> \<open>i \<le> bucket_start \<alpha> T b'\<close> by auto
            with s_suc_invD[OF assms(7) `i' < length _` _ `SA ! i' = _` `suffix_type T x = _`,
                  simplified `\<alpha> (T ! x) = b`]
            obtain k where
              "in_s_current_bucket \<alpha> T B b k"
              "SA ! k = x"
              "k < i'"
              by blast
            hence "x \<in> ?B"
              by (meson assms(11) in_s_current_bucket_list_slice)
            with `x \<notin> ?B`
            have False
              by blast
            then show ?thesis
              by blast
          qed
          moreover
          have "Suc x \<in> s_bucket \<alpha> T b' \<Longrightarrow> ?thesis"
          proof -
            assume "Suc x \<in> s_bucket \<alpha> T b'"

          let ?ys = "list_slice SA (s_bucket_start \<alpha> T b') (bucket_end \<alpha> T b')"

            from distinct_card[OF s_distinct_invD[OF assms(1) `b' \<le> _`],
                  simplified `B ! b' = s_bucket_start _ _ _`]
            have "card (set ?ys) = card (s_bucket \<alpha> T b')"
              by (metis add_diff_cancel_left' assms(11) bucket_end_eq_s_start_pl_size
                    bucket_end_le_length length_list_slice min_def s_bucket_size_def)
            with card_subset_eq[
                  OF finite_s_bucket s_locations_inv_subset_s_bucket[OF assms(3) `b' \<le> _`],
                  simplified `B ! b' = s_bucket_start \<alpha> T b'`]
            have "set ?ys = s_bucket \<alpha> T b'"
              by blast
            with `Suc x \<in> s_bucket \<alpha> T b'`
            have "Suc x \<in> set ?ys"
              by simp
            with nth_mem_list_slice[of "Suc x"]
            obtain i' where
              "i' < length SA"
              "s_bucket_start \<alpha> T b' \<le> i'"
              "i' < bucket_end \<alpha> T b'"
              "SA ! i' = Suc x"
              by blast

            from `SA ! i' = Suc x` assms(16,18)
            have "i \<noteq> i'"
              using nat.discI by blast
            hence "i < i'"
              using \<open>B ! b' = s_bucket_start \<alpha> T b'\<close> \<open>i \<le> B ! b'\<close> \<open>s_bucket_start \<alpha> T b' \<le> i'\<close>
              by linarith
            with s_suc_invD[OF assms(7) `i' < length _` _ `SA ! i' = _` `suffix_type T x = _`,
                  simplified `\<alpha> (T ! x) = b`]
            obtain k where
              "in_s_current_bucket \<alpha> T B b k"
              "SA ! k = x"
              "k < i'"
              by blast
            hence "x \<in> ?B"
              by (meson assms(11) in_s_current_bucket_list_slice)
            with `x \<notin> ?B`
            have False
              by blast
            then show ?thesis
              by blast
          qed
          ultimately show ?thesis
            by blast
        qed
        ultimately show ?thesis
          using `Suc x \<in> ?B \<or> (\<exists>b'. b < b' \<and> Suc x \<in> bucket \<alpha> T b')` by blast
      qed
      ultimately show ?thesis
        by blast
    qed
    ultimately show ?thesis
      by blast
  qed
  moreover
  have "Suc n \<le> j \<Longrightarrow> ?g1 \<and> ?g2 \<and> ?g3"
  proof -
    assume "Suc n \<le> j"
    with s_seen_invD[OF assms(5) `j < length SA`] assms(16)
    show ?thesis
      by blast
  qed
  ultimately show "?g1 \<and> ?g2 \<and> ?g3"
    by blast
qed

corollary s_seen_inv_maintained_perm_step_c2:
  assumes "s_perm_inv \<alpha> T B SA0 SA i"
  and     "i = Suc n"
  and     "Suc n < length SA"
  and     "SA ! Suc n = 0"
shows "s_seen_inv \<alpha> T B SA n"
  using s_seen_inv_maintained_step_c2[OF s_perm_inv_elims[OF assms(1)] assms(2-)]
  by blast

lemma s_seen_inv_maintained_step_c3:
  assumes "s_distinct_inv \<alpha> T B SA"
  and     "s_bucket_ptr_inv \<alpha> T B"
  and     "s_locations_inv \<alpha> T B SA"
  and     "s_unchanged_inv \<alpha> T B SA0 SA"
  and     "s_seen_inv \<alpha> T B SA i"
  and     "s_pred_inv \<alpha> T B SA i"
  and     "s_suc_inv \<alpha> T B SA i"
  and     "strict_mono \<alpha>"
  and     "\<alpha> (Max (set T)) < length B"
  and     "length SA0 = length T"
  and     "length SA = length T"
  and     "l_types_init \<alpha> T SA0"
  and     "valid_list T"
  and     "\<alpha> bot = 0"
  and     "Suc 0 < length T"
  and     "i = Suc n"
  and     "Suc n < length SA"
  and     "SA ! Suc n = Suc j"
  and     "suffix_type T j = L_type"
shows "s_seen_inv \<alpha> T B SA n"
 unfolding s_seen_inv_def
proof (intro allI impI)
  fix k
  assume "k < length SA" "n \<le> k"
  hence "n < length SA"
    by simp
  hence "n < length T"
    by (simp add: assms(11))

  let ?b = "\<alpha> (T ! (SA ! k))"
  let ?g1 = "(suffix_type T (SA ! k) = S_type \<longrightarrow> in_s_current_bucket \<alpha> T B ?b k)"
  and ?g2 = "(suffix_type T (SA ! k) = L_type \<longrightarrow> in_l_bucket \<alpha> T ?b k)"
  and ?g3 = "SA ! k < length T"

 from `n \<le> k`
  have "n = k \<or> Suc n \<le> k"
    by linarith
  moreover
  have "n = k \<Longrightarrow> ?g1 \<and> ?g2 \<and> ?g3"
  proof -
    assume "n = k"
    with index_in_bucket_interval_gen[OF `n < length T` assms(8)]
    obtain b where
      "b \<le> \<alpha> (Max (set T))"
      "bucket_start \<alpha> T b \<le> k"
      "k < bucket_end \<alpha> T b"
      by blast

    have "k < l_bucket_end \<alpha> T b \<or> s_bucket_start \<alpha> T b \<le> k"
      by (metis not_le s_bucket_start_eq_l_bucket_end)
    moreover
    have "k < l_bucket_end \<alpha> T b \<Longrightarrow> ?thesis"
    proof -
      assume "k < l_bucket_end \<alpha> T b"
      with l_types_init_nth[OF assms(11) l_types_init_maintained[OF assms(2,4,10-12)]
            `b \<le> _` `bucket_start _ _ _ \<le> _`]
      have "SA ! k \<in> l_bucket \<alpha> T b" .
      hence "SA ! k < length T" "suffix_type T (SA ! k) = L_type"
        by (simp add: l_bucket_def bucket_def)+
      moreover
      from calculation(2)
      have ?g1
        by simp
      moreover
      from `SA ! k \<in> l_bucket \<alpha> T b`
      have "b = (\<alpha> (T ! (SA ! k)))"
        by (simp add: l_bucket_def bucket_def)
      with `b \<le> _` `bucket_start _ _ _ \<le> _` `k < l_bucket_end _ _ _`
      have "in_l_bucket \<alpha> T (\<alpha> (T ! (SA ! k))) k"
        using in_l_bucket_def by blast
      ultimately show ?thesis
        by blast
    qed
    moreover
    have "s_bucket_start \<alpha> T b \<le> k \<Longrightarrow> ?thesis"
    proof -
      assume "s_bucket_start \<alpha> T b \<le> k"
      hence "s_bucket_start \<alpha> T b < i"
        by (simp add: \<open>n = k\<close> assms(16))

      have "B ! b \<le> i"
      proof(rule ccontr)
        assume "\<not>B ! b \<le> i"
        hence "i < B ! b"
          by simp
        with s_B_val[OF assms(1-6,8,10-13,15) `b \<le> \<alpha> _`]
        have "B ! b = s_bucket_start \<alpha> T b" .
        with `s_bucket_start \<alpha> T b < i` `i < B ! b`
        show False
          by linarith
      qed
      hence "i = B ! b \<or> B ! b < i"
        by linarith
      moreover
      have "B ! b < i \<Longrightarrow> ?thesis"
      proof -
        assume "B ! b < i"
        hence "B ! b \<le> k"
          by (simp add: \<open>n = k\<close> assms(16))
        with s_locations_invD[OF assms(3) `b \<le> _` _ `k < bucket_end _ _ _`]
        have "SA ! k \<in> s_bucket \<alpha> T b" .
        hence "SA ! k < length T" "suffix_type T (SA ! k) = S_type"
          by (simp add: s_bucket_def bucket_def)+
        moreover
        from calculation(2)
        have ?g2
          by simp
        moreover
        from `SA ! k \<in> s_bucket \<alpha> T b`
        have "\<alpha> (T ! (SA ! k)) = b"
          by (simp add: s_bucket_def bucket_def)
        with `B ! b \<le> k` `k < bucket_end \<alpha> T b` `b \<le> _`
        have "in_s_current_bucket \<alpha> T B (\<alpha> (T ! (SA ! k))) k"
          by (simp add: in_s_current_bucket_def)
        ultimately show ?thesis
          by blast
      qed
      moreover
      have "i = B ! b \<Longrightarrow> ?thesis"
      proof -
        assume "i = B ! b"
        hence "k < B ! b"
          using \<open>n = k\<close> assms(16) by linarith

        have "s_bucket_start \<alpha> T b < B ! b"
          using \<open>i = B ! b\<close> \<open>s_bucket_start \<alpha> T b < i\<close> by blast

        have "b \<noteq> 0"
          by (metis \<open>k < B ! b\<close> assms(2) not_less_zero s_bucket_ptr_0)

        let ?xs = "list_slice SA (B ! b) (bucket_end \<alpha> T b)"
        let ?B = "set ?xs"
        let ?A = "s_bucket \<alpha> T b - ?B"

        from s_locations_inv_subset_s_bucket[OF assms(3) `b \<le> _`]
        have "?B \<subseteq> s_bucket \<alpha> T b" .
        hence "?A \<subseteq> s_bucket \<alpha> T b"
          by blast

        have "card (s_bucket \<alpha> T b) = bucket_end \<alpha> T b - s_bucket_start \<alpha> T b"
          by (simp add: bucket_end_eq_s_start_pl_size s_bucket_size_def)

        from s_distinct_invD[OF assms(1) `b \<le> _`]
        have "card ?B = bucket_end \<alpha> T b - B ! b"
          by (metis assms(11) bucket_end_le_length distinct_card length_list_slice min.absorb_iff1)
        hence "card ?B < card (s_bucket \<alpha> T b)"
          using \<open>card (s_bucket \<alpha> T b) = bucket_end \<alpha> T b - s_bucket_start \<alpha> T b\<close>
                \<open>k < bucket_end \<alpha> T b\<close> \<open>s_bucket_start \<alpha> T b < B ! b\<close> \<open>s_bucket_start \<alpha> T b \<le> k\<close>
          by linarith
        with card_psubset[OF finite_s_bucket `?B \<subseteq> s_bucket \<alpha> T b`]
        have "?B \<subset> s_bucket \<alpha> T b" .
        hence "?A \<noteq> {}"
          by blast
        with subset_s_bucket_successor[OF assms(13,8,14) `b \<noteq> 0` `?A \<subseteq> s_bucket \<alpha> T b`]
        obtain x where
          "x \<in> ?A"
          "Suc x \<in> s_bucket \<alpha> T b - ?A \<or> (\<exists>b'. b < b' \<and> Suc x \<in> bucket \<alpha> T b')"
          by blast
        hence "Suc x \<in> ?B \<or> (\<exists>b'. b < b' \<and> Suc x \<in> bucket \<alpha> T b')"
          by blast

        from `x \<in> ?A` `?A \<subseteq> s_bucket \<alpha> T b`
        have "suffix_type T x = S_type" "\<alpha> (T ! x) = b"
          by (simp add: s_bucket_def bucket_def)+

        have "x \<notin> ?B"
          using \<open>x \<in> ?A\<close> by blast

        from `Suc x \<in> ?B \<or> (\<exists>b'. b < b' \<and> Suc x \<in> bucket \<alpha> T b')`
        have False
        proof
          assume "Suc x \<in> ?B"
          from nth_mem_list_slice[OF `Suc x \<in> ?B`]
          obtain i' where
            "i' < length SA"
            "B ! b \<le> i'"
            "i' < bucket_end \<alpha> T b"
            "SA ! i' = Suc x"
            by blast

          have "i \<noteq> i'"
          proof (rule ccontr)
            assume "\<not> i \<noteq> i'"
            hence "i = i'"
              by auto
            hence "j = x"
              using \<open>SA ! i' = Suc x\<close> assms(16,18) by auto
            with assms(19) `suffix_type T x = _`
            show False
              by simp
          qed
          with `B ! b \<le> i'` `i = B ! b`
          have "i < i'"
            using nat_less_le by blast
          with s_suc_invD[OF assms(7) `i' < length SA ` _ `SA ! i' = _` `suffix_type T x = _`]
               `\<alpha> (T ! x) = b`
          obtain k where
            "in_s_current_bucket \<alpha> T B b k"
            "SA ! k = x"
            "k < i'"
            by blast
          hence "x \<in> ?B"
            by (meson assms(11) in_s_current_bucket_list_slice)
          with `x \<notin> ?B`
          show False
            by blast
        next
          assume "\<exists>b'. b < b' \<and> Suc x \<in> bucket \<alpha> T b'"
          then obtain b' where
            "b < b'"
            "Suc x \<in> bucket \<alpha> T b'"
            by blast
          hence "b' \<le> \<alpha> (Max (set T))"
            by (metis (mono_tags, lifting) Max_greD assms(8) bucket_def mem_Collect_eq
                  strict_mono_less_eq)

          have "suffix_type T (Suc x) = S_type \<or> suffix_type T (Suc x) = L_type"
            by (simp add: suffix_type_def)
          hence "Suc x \<in> l_bucket \<alpha> T b' \<or> Suc x \<in> s_bucket \<alpha> T b'"
            using \<open>Suc x \<in> bucket \<alpha> T b'\<close> l_bucket_def s_bucket_def by fastforce
          moreover
          have "Suc x \<in> l_bucket \<alpha> T b' \<Longrightarrow> False"
          proof -
            assume "Suc x \<in> l_bucket \<alpha> T b'"
            with l_types_initD(1)[OF l_types_init_maintained[OF assms(2,4,10-12)] `b' \<le> _`]
            have "Suc x \<in> set (list_slice SA (bucket_start \<alpha> T b') (l_bucket_end \<alpha> T b'))"
              by blast
            with nth_mem_list_slice[of "Suc x"]
            obtain i' where
              "i' < length SA"
              "bucket_start \<alpha> T b' \<le> i'"
              "i' < l_bucket_end \<alpha> T b'"
              "SA ! i' = Suc x"
              by blast

            have "i \<noteq> i'"
            proof (rule ccontr)
              assume "\<not> i \<noteq> i'"
              hence "i = i'"
                by auto
              hence "j = x"
                using \<open>SA ! i' = Suc x\<close> assms(16,18) by auto
              with assms(19) `suffix_type T x = _`
              show False
                by simp
            qed
            moreover
            from `b < b'`
            have "bucket_end \<alpha> T b \<le> bucket_start \<alpha> T b'"
              by (simp add: less_bucket_end_le_start)
            hence "B ! b \<le> i'"
              using s_bucket_ptr_upper_bound[OF assms(2) `b \<le> \<alpha> (Max (set T))`]
                    `bucket_start \<alpha> T b' \<le> i'`
              by linarith
            ultimately have "i < i'"
              using \<open>i = B ! b\<close> nat_less_le by blast
            with s_suc_invD[OF assms(7) `i' < length SA ` _ `SA ! i' = _` `suffix_type T x = _`]
                 `\<alpha> (T ! x) = b`
            obtain k where
              "in_s_current_bucket \<alpha> T B b k"
              "SA ! k = x"
              "k < i'"
              by blast
            hence "x \<in> ?B"
              by (meson assms(11) in_s_current_bucket_list_slice)
            with `x \<notin> ?B`
            show False
              by blast
          qed
          moreover
          have "Suc x \<in> s_bucket \<alpha> T b' \<Longrightarrow> False"
          proof -
            assume "Suc x \<in> s_bucket \<alpha> T b'"

            have "i \<le> bucket_end \<alpha> T b"
              by (simp add: Suc_le_eq \<open>k < bucket_end \<alpha> T b\<close> \<open>n = k\<close> assms(16))
            hence "i \<le> bucket_start \<alpha> T b'"
              using \<open>b < b'\<close> less_bucket_end_le_start order.trans by blast
            hence "i \<le> B ! b'"
              using s_bucket_ptr_lower_bound[OF assms(2) `b' \<le> _`]
              by (metis l_bucket_end_def le_trans nat_le_iff_add s_bucket_start_eq_l_bucket_end)
            hence "i < B ! b' \<or> i = B ! b'"
              using nat_less_le by blast
            hence "B ! b' = s_bucket_start \<alpha> T b'"
            proof
              assume "i < B ! b'"
              with s_B_val[OF assms(1-6,8,10-13,15) `b' \<le> _`]
              show "B ! b' = s_bucket_start \<alpha> T b'"
                by blast
            next
              assume "i = B ! b'"
              with s_bucket_ptr_lower_bound[OF assms(2) `b' \<le> _`]
                   `i \<le> bucket_start \<alpha> T b'`
              show "B ! b' = s_bucket_start \<alpha> T b'"
                by (simp add: s_bucket_start_def)
            qed

            let ?ys = "list_slice SA (s_bucket_start \<alpha> T b') (bucket_end \<alpha> T b')"

            from distinct_card[OF s_distinct_invD[OF assms(1) `b' \<le> _`],
                  simplified `B ! b' = s_bucket_start _ _ _`]
            have "card (set ?ys) = card (s_bucket \<alpha> T b')"
              by (metis add_diff_cancel_left' assms(11) bucket_end_eq_s_start_pl_size
                    bucket_end_le_length length_list_slice min_def s_bucket_size_def)
            with card_subset_eq[
                  OF finite_s_bucket s_locations_inv_subset_s_bucket[OF assms(3) `b' \<le> _`],
                  simplified `B ! b' = s_bucket_start \<alpha> T b'`]
            have "set ?ys = s_bucket \<alpha> T b'"
              by blast
            with `Suc x \<in> s_bucket \<alpha> T b'`
            have "Suc x \<in> set ?ys"
              by simp
            with nth_mem_list_slice[of "Suc x"]
            obtain i' where
              "i' < length SA"
              "s_bucket_start \<alpha> T b' \<le> i'"
              "i' < bucket_end \<alpha> T b'"
              "SA ! i' = Suc x"
              by blast

            have "i \<noteq> i'"
            proof (rule ccontr)
              assume "\<not> i \<noteq> i'"
              hence "i = i'"
                by auto
              hence "j = x"
                using \<open>SA ! i' = Suc x\<close> assms(16,18) by auto
              with assms(19) `suffix_type T x = _`
              show False
                by simp
            qed
            moreover
            have "i \<le> i'"
              using \<open>B ! b' = s_bucket_start \<alpha> T b'\<close> \<open>i \<le> B ! b'\<close> \<open>s_bucket_start \<alpha> T b' \<le> i'\<close>
              by linarith
            ultimately have "i < i'"
              using dual_order.order_iff_strict by blast
            with s_suc_invD[OF assms(7) `i' < length SA ` _ `SA ! i' = _` `suffix_type T x = _`]
                 `\<alpha> (T ! x) = b`
            obtain k where
              "in_s_current_bucket \<alpha> T B b k"
              "SA ! k = x"
              "k < i'"
              by blast
            hence "x \<in> ?B"
              by (meson assms(11) in_s_current_bucket_list_slice)
            with `x \<notin> ?B`
            show False
              by blast
          qed
          ultimately show False
            by blast
        qed
        then show ?thesis
          by blast
      qed
      ultimately show ?thesis
        by blast
    qed
    ultimately show ?thesis
      by blast
  qed
  moreover
  have "Suc n \<le> k \<Longrightarrow> ?g1 \<and> ?g2 \<and> ?g3"
  proof -
    assume "Suc n \<le> k"
    with s_seen_invD[OF assms(5) `k < length SA`] assms(16)
    show ?thesis
      by blast
  qed
  ultimately show "?g1 \<and> ?g2 \<and> ?g3"
    by blast
qed

corollary s_seen_inv_maintained_perm_step_c3:
  assumes "s_perm_inv \<alpha> T B SA0 SA i"
  and     "i = Suc n"
  and     "Suc n < length SA"
  and     "SA ! Suc n = Suc j"
  and     "suffix_type T j = L_type"
shows "s_seen_inv \<alpha> T B SA n"
  using s_seen_inv_maintained_step_c3[OF s_perm_inv_elims[OF assms(1)] assms(2-)]
  by blast

lemma s_seen_inv_maintained_step_c4:
  assumes "s_distinct_inv \<alpha> T B SA"
  and     "s_bucket_ptr_inv \<alpha> T B"
  and     "s_locations_inv \<alpha> T B SA"
  and     "s_unchanged_inv \<alpha> T B SA0 SA"
  and     "s_seen_inv \<alpha> T B SA i"
  and     "s_pred_inv \<alpha> T B SA i"
  and     "s_suc_inv \<alpha> T B SA i"
  and     "strict_mono \<alpha>"
  and     "\<alpha> (Max (set T)) < length B"
  and     "length SA0 = length T"
  and     "length SA = length T"
  and     "l_types_init \<alpha> T SA0"
  and     "valid_list T"
  and     "\<alpha> bot = 0"
  and     "Suc 0 < length T"
  and     "i = Suc n"
  and     "Suc n < length SA"
  and     "SA ! Suc n = Suc j"
  and     "suffix_type T j = S_type"
  and     "b = \<alpha> (T ! j)"
  and     "k = B ! b - Suc 0"
shows "s_seen_inv \<alpha> T (B[b := k]) (SA[k := j]) n"
  unfolding s_seen_inv_def
proof(intro allI impI)
  fix i'
  assume "i' < length (SA[k := j])" "n \<le> i'"

  let ?g1 = "(suffix_type T (SA[k := j] ! i') = S_type \<longrightarrow>
              in_s_current_bucket \<alpha> T (B[b := k]) (\<alpha> (T ! (SA[k := j] ! i'))) i')" and
      ?g2 = "(suffix_type T (SA[k := j] ! i') = L_type \<longrightarrow>
              in_l_bucket \<alpha> T (\<alpha> (T ! (SA[k := j] ! i'))) i')" and
      ?g3 = "SA[k := j] ! i' < length T"

  from s_bucket_ptr_strict_lower_bound[OF assms(1-6,8,10-14,16-20)]
  have "s_bucket_start \<alpha> T b < B ! b".
  hence "s_bucket_start \<alpha> T b \<le> k"
    using assms(21) by linarith
  hence "bucket_start \<alpha> T b \<le> k"
    using bucket_start_le_s_bucket_start le_trans by blast

  from `s_bucket_start \<alpha> T b < B ! b`
  have "k < B ! b"
    using assms(21) by linarith

  have "j < length T"
    by (simp add: assms(19) suffix_type_s_bound)
  hence "b \<le> \<alpha> (Max (set T))"
    by (simp add: assms(8,20) strict_mono_less_eq)
  with s_bucket_ptr_upper_bound[OF assms(2)]
  have "B ! b \<le> bucket_end \<alpha> T b"
    by blast
  with `k < B ! b`
  have "k < bucket_end \<alpha> T b"
    by linarith

  have "B ! b \<le> i"
  proof(rule ccontr)
    assume "\<not>B ! b \<le> i"
    hence "i < B ! b"
      by simp
    with s_B_val[OF assms(1-6,8,10-13,15) `b \<le> \<alpha> _`]
    have "B ! b = s_bucket_start \<alpha> T b" .
    with `s_bucket_start \<alpha> T b < B ! b`
    show False
      by linarith
  qed
  hence "k < i"
    using \<open>k < B ! b\<close> less_le_trans by blast

  have "k = i' \<Longrightarrow> n = i'"
    using \<open>k < i\<close> \<open>n \<le> i'\<close> assms(16) le_less_Suc_eq by blast

  have "k \<le> i'"
    using \<open>k < i\<close> \<open>n \<le> i'\<close> assms(16) by linarith

  have "i' < length T"
    using \<open>i' < length (SA[k := j])\<close> assms(11) by auto
  with index_in_bucket_interval_gen[OF _ assms(8), of i' T]
  obtain b' where
    "b' \<le> \<alpha> (Max (set T))"
    "bucket_start \<alpha> T b' \<le> i'"
    "i' < bucket_end \<alpha> T b'"
    by blast
  hence "n < bucket_end \<alpha> T b'"
    using \<open>n \<le> i'\<close> dual_order.strict_trans2 by blast
  hence "i \<le> bucket_end \<alpha> T b'"
    using assms(16) by linarith

  have "b \<le> b'"
  proof (rule ccontr)
    assume "\<not>b \<le> b'"
    hence "b' < b"
      by linarith
    hence "bucket_end \<alpha> T b' \<le> bucket_start \<alpha> T b"
      by (simp add: less_bucket_end_le_start)
    with `i \<le> bucket_end \<alpha> T b'` `bucket_start \<alpha> T b \<le> k` `k < B ! b`
    have "i < B ! b"
      by linarith
    with `B ! b \<le> i`
    show False
      by linarith
  qed

  have "in_s_current_bucket \<alpha> T (B[b := k]) b k"
    unfolding in_s_current_bucket_def
    using \<open>b \<le> \<alpha> (Max (set T))\<close> \<open>k < bucket_end \<alpha> T b\<close> assms(9) by auto

  have "b < b' \<Longrightarrow> ?g1 \<and> ?g2 \<and> ?g3"
  proof -
    assume "b < b'"
    hence "bucket_end \<alpha> T b \<le> bucket_start \<alpha> T b'"
      by (simp add: less_bucket_end_le_start)
    with `k < bucket_end _ _ b` `bucket_start _ _ b' \<le> i'`
    have "k < i'"
      by linarith
    hence "SA[k := j] ! i' = SA ! i'"
      by simp

    from `b < b'`
    have "B[b := k] ! b' = B ! b'"
      by simp

    have "i' < l_bucket_end \<alpha> T b' \<or> B ! b' \<le> i' \<or> (s_bucket_start \<alpha> T b' \<le> i' \<and> i' < B ! b')"
      by (metis not_le s_bucket_start_eq_l_bucket_end)
    moreover
    have "B ! b' \<le> i' \<Longrightarrow> ?thesis"
    proof -
      assume "B ! b' \<le> i'"
      with s_locations_invD[OF assms(3) `b' \<le> _` _ `i' < bucket_end _ _ _`]
      have "SA ! i' \<in> s_bucket \<alpha> T b'" .
      hence "suffix_type T (SA ! i') = S_type" "\<alpha> (T ! (SA ! i')) = b'" "SA ! i' < length T"
        by (simp add: s_bucket_def bucket_def)+
      moreover
      from `B[b := k] ! b' = B ! b'` `b' \<le> \<alpha> _` `B ! b' \<le> i'` `i' < bucket_end \<alpha> T b'`
      have "in_s_current_bucket \<alpha> T (B[b := k]) b' i'"
        by (simp add: in_s_current_bucket_def)
      ultimately show ?thesis
        by (simp add: `SA[k := j] ! i' = SA ! i'`)
    qed
    moreover
    have "i' < l_bucket_end \<alpha> T b' \<Longrightarrow> ?thesis"
    proof -
      assume "i' < l_bucket_end \<alpha> T b'"
      hence "in_l_bucket \<alpha> T b' i'"
        by (simp add: `bucket_start \<alpha> T b' \<le> i'` `b' \<le> \<alpha> _` in_l_bucket_def)
      moreover
      from l_types_init_nth[OF assms(11) l_types_init_maintained[OF assms(2,4,10-12)]
            `b' \<le> \<alpha> _` `bucket_start _ _ _ \<le> i'` `i' < l_bucket_end _ _ _`]
      have "SA ! i' \<in> l_bucket \<alpha> T b'" .
      hence "SA ! i' < length T" "\<alpha> (T ! (SA ! i')) = b'" "suffix_type T (SA ! i') = L_type"
        by (simp add: l_bucket_def bucket_def)+
      ultimately show ?thesis
        using `SA[k := j] ! i' = SA ! i'`
        by simp
    qed
    moreover
    have "\<lbrakk>s_bucket_start \<alpha> T b' \<le> i'; i' < B ! b'\<rbrakk> \<Longrightarrow> ?thesis"
    proof -
      assume "s_bucket_start \<alpha> T b' \<le> i'" "i' < B ! b'"
      have "B ! b' = i"
      proof (rule ccontr)
        assume "B ! b' \<noteq> i"
        hence "i < B ! b' \<or> B ! b' < i"
          by linarith
        moreover
        have "B ! b' < i \<Longrightarrow> False"
          using `i' < B ! b'` \<open>n \<le> i'\<close> assms(16) by linarith
        moreover
        have "i < B ! b' \<Longrightarrow> False"
        proof -
          assume "i < B ! b'"
          with s_B_val[OF assms(1-6,8,10-13,15) `b' \<le> \<alpha> _`]
          have "B ! b' = s_bucket_start \<alpha> T b'" .
          with `s_bucket_start \<alpha> T b' \<le> i'` `i' < B ! b'`
          show False
            by linarith
        qed
        ultimately show False
          by linarith
      qed

      have "s_bucket_start \<alpha> T b' < B ! b'"
        using \<open>i' < B ! b'\<close> \<open>s_bucket_start \<alpha> T b' \<le> i'\<close> by linarith
      hence "s_bucket_start \<alpha> T b' < bucket_end \<alpha> T b'"
        using \<open>B ! b' = i\<close> \<open>i \<le> bucket_end \<alpha> T b'\<close> order.strict_trans2 by blast
      hence "s_bucket \<alpha> T b' \<noteq> {}"
        by (metis add.commute bucket_end_eq_s_start_pl_size distinct_card distinct_conv_nth
              empty_set less_irrefl_nat less_nat_zero_code list.size(3) plus_nat.add_0
              s_bucket_size_def)

      have "bucket_end \<alpha> T b' \<le> length SA"
        by (simp add: assms(11) bucket_end_le_length)

      let ?xs = "list_slice SA (B ! b') (bucket_end \<alpha> T b')"

      have "set ?xs \<subset> s_bucket \<alpha> T b'"
      proof
        from s_locations_inv_subset_s_bucket[OF assms(3) `b' \<le> _`]
        show "set ?xs \<subseteq> s_bucket \<alpha> T b'" .
      next
        from `s_bucket_start \<alpha> T b' < B ! b'` `s_bucket_start \<alpha> T b' < bucket_end \<alpha> T b'`
        have "bucket_end \<alpha> T b' - B ! b' < bucket_end \<alpha> T b' - s_bucket_start \<alpha> T b'"
          using diff_less_mono2 by blast
        hence "length ?xs < s_bucket_size \<alpha> T b'"
          by (metis \<open>bucket_end \<alpha> T b' \<le> length SA\<close> add_diff_cancel_left'
                bucket_end_eq_s_start_pl_size length_list_slice min_def)
        hence "card (set ?xs) \<noteq> card (s_bucket \<alpha> T b')"
          by (metis card_length not_le s_bucket_size_def)
        then show "set ?xs \<noteq> s_bucket \<alpha> T b'"
          by auto
      qed

      have P0: "\<forall>i0 < length T. \<alpha> (T ! i0) = b' \<longrightarrow> T ! i0 \<noteq> bot"
        using \<open>b < b'\<close> assms(8,20) strict_mono_less by fastforce
      hence P1: "\<forall>i0 < length T. \<alpha> (T ! i0) = b' \<longrightarrow> Suc i0 < length T"
        by (metis Suc_leI assms(13) diff_Suc_1 last_conv_nth le_imp_less_or_eq length_greater_0_conv
              valid_list_def)

      let ?S = "s_bucket \<alpha> T b' - set ?xs"

      from `set ?xs \<subset> s_bucket \<alpha> T b'`
      have "?S \<noteq> {}"
        by blast
      have "?S \<subseteq> s_bucket \<alpha> T b'"
        by blast
      hence P2: "\<forall>x \<in> ?S. \<alpha> (T ! x) = b' \<and> suffix_type T x = S_type \<and> x < length T"
        by (simp add: bucket_def s_bucket_def)

      have P3: "\<forall>x \<in> ?S. Suc x < length T \<and> \<alpha> (T ! Suc x) \<ge> b'"
      proof
        fix x
        assume "x \<in> ?S"
        with P2
        have "\<alpha> (T ! x) = b'" "suffix_type T x = S_type" "x < length T"
          by blast+
        with P1
        have "Suc x < length T"
          by blast
        moreover
        from `suffix_type T x = S_type` `x < length T`
        have "T ! x \<le> T ! Suc x"
          using calculation nth_gr_imp_l_type by fastforce
        hence "\<alpha> (T ! Suc x) \<ge> b'"
          using \<open>\<alpha> (T ! x) = b'\<close> assms(8) strict_mono_leD by blast
        ultimately show "Suc x < length T \<and> \<alpha> (T ! Suc x) \<ge> b'"
          by blast
      qed

      have "finite ?S"
        by (simp add: finite_s_bucket)

      have "\<exists>x \<in> ?S. \<alpha> (T ! Suc x) > b' \<or> Suc x \<in> set ?xs"
      proof (rule ccontr)
        assume "\<not> (\<exists>x \<in> ?S. b' < \<alpha> (T ! Suc x) \<or> Suc x \<in> set ?xs)"
        hence "\<forall>x \<in> ?S. \<alpha> (T ! Suc x) \<le> b' \<and> Suc x \<notin> set ?xs"
          using not_le_imp_less by blast
        with P3
        have P4: "\<forall>x \<in> ?S. \<alpha> (T ! Suc x) = b' \<and> Suc x \<notin> set ?xs"
          using dual_order.antisym by blast
        hence P5: "\<forall>x \<in> ?S. suffix_type T (Suc x) = S_type"
          by (metis P2 P3 assms(8) strict_mono_eq suffix_type_neq)
        hence P6: "\<forall>x \<in> ?S. Suc x \<in> ?S"
          by (metis (mono_tags, lifting) Diff_iff P3 P4 bucket_def mem_Collect_eq s_bucket_def)
        with `?S \<noteq> {}` `finite ?S`
        show False
          using Suc_le_lessD infinite_growing by blast
      qed
      then obtain x where
        "x \<in> ?S"
        "\<alpha> (T ! Suc x) > b' \<or> Suc x \<in> set ?xs"
        by blast
      with P3
      have "Suc x < length T"
        by blast

      from `x \<in> ?S`
      have "suffix_type T x = S_type" "\<alpha> (T ! x) = b'" "x < length T"
        using P2 by blast+

      have P4: "\<forall>b0 \<le> \<alpha> (Max (set T)). b' < b0 \<longrightarrow> B ! b0 = s_bucket_start \<alpha> T b0"
      proof(safe)
        fix b0
        assume "b0 \<le> \<alpha> (Max (set T))" "b' < b0"
        hence "bucket_end \<alpha> T b' \<le> bucket_start \<alpha> T b0"
          by (simp add: less_bucket_end_le_start)
        with s_bucket_ptr_upper_bound[OF assms(2) `b' \<le> _ `]
             s_bucket_ptr_lower_bound[OF assms(2) `b0 \<le> _ `]
        have "B ! b' \<le> B ! b0"
          by (meson bucket_start_le_s_bucket_start le_trans)
        hence "B ! b' = B ! b0 \<or> B ! b' < B ! b0"
          by linarith
        moreover
        have "B ! b' = B ! b0 \<Longrightarrow> B ! b0 = s_bucket_start \<alpha> T b0"
          by (metis \<open>B ! b' = i\<close> \<open>bucket_end \<alpha> T b' \<le> bucket_start \<alpha> T b0\<close> le_trans
              \<open>i \<le> bucket_end \<alpha> T b'\<close> \<open>s_bucket_start \<alpha> T b0 \<le> B ! b0\<close>  dual_order.antisym
                bucket_start_le_s_bucket_start)
        moreover
        have "B ! b' < B ! b0 \<Longrightarrow> i < B ! b0"
          by (simp add: \<open>B ! b' = i\<close>)
        with s_B_val[OF assms(1-6,8,10-13,15) `b0 \<le> _`]
        have "B ! b' < B ! b0 \<Longrightarrow> B ! b0 = s_bucket_start \<alpha> T b0"
          by blast
        ultimately show "B ! b0 = s_bucket_start \<alpha> T b0"
          by blast
      qed

      from `\<alpha> (T ! Suc x) > b' \<or> Suc x \<in> set ?xs`
      show ?thesis
      proof
        let ?b = "\<alpha> (T ! Suc x)"
        let ?ys = "list_slice SA (bucket_start \<alpha> T ?b) (l_bucket_end \<alpha> T ?b)"
        and ?zs = "list_slice SA (s_bucket_start \<alpha> T ?b) (bucket_end \<alpha> T ?b)"

        assume "b' < ?b"
        with P4 `Suc x < length T`
        have "B ! ?b = s_bucket_start \<alpha> T ?b"
          by (simp add: assms(8) strict_mono_less_eq)

        from `Suc x < length T`
        have "?b \<le> \<alpha> (Max (set T))"
          by (simp add: assms(8) strict_mono_leD)

        have "bucket_end \<alpha> T b' \<le> bucket_start \<alpha> T ?b"
          using \<open>b' < \<alpha> (T ! Suc x)\<close> less_bucket_end_le_start by blast
        hence "i \<le> bucket_start \<alpha> T ?b"
          using \<open>i \<le> bucket_end \<alpha> T b'\<close> order.trans by blast

        have "set ?zs = s_bucket \<alpha> T ?b"
        proof (rule card_subset_eq[OF finite_s_bucket])
          show "set ?zs \<subseteq> s_bucket \<alpha> T ?b"
            by (metis Max_greD \<open>B ! ?b = s_bucket_start \<alpha> T ?b\<close> \<open>Suc x < length T\<close> assms(3,8)
                  s_locations_inv_subset_s_bucket strict_mono_leD)
        next
          from distinct_card[OF s_distinct_invD[OF assms(1) `?b \<le> _`]]
               `B ! ?b = s_bucket_start \<alpha> T ?b`
          have "card (set ?zs) = length ?zs"
            by simp
          moreover
          have "length ?zs = bucket_end \<alpha> T ?b - s_bucket_start \<alpha> T ?b"
            by (metis assms(11) bucket_end_le_length length_list_slice min_def)
          moreover
          have "s_bucket_size \<alpha> T ?b = bucket_end \<alpha> T ?b - s_bucket_start \<alpha> T ?b"
            by (simp add: bucket_end_eq_s_start_pl_size)
          hence "card (s_bucket \<alpha> T ?b) = bucket_end \<alpha> T ?b - s_bucket_start \<alpha> T ?b"
            by (simp add: s_bucket_size_def)
          ultimately show "card (set ?zs) = card (s_bucket \<alpha> T ?b)"
            by simp
        qed

        have "suffix_type T (Suc x) = L_type \<Longrightarrow> ?thesis"
        proof -
          assume "suffix_type T (Suc x) = L_type"
          with l_types_initD(1)[OF l_types_init_maintained[OF assms(2,4,10-12)] `?b \<le> _`]
          have "Suc x \<in> set ?ys"
            by (simp add: \<open>Suc x < length T\<close> bucket_def l_bucket_def)

          from nth_mem_list_slice[OF `Suc x \<in> set ?ys`]
          obtain i0 where
            "i0 < length SA"
            "bucket_start \<alpha> T ?b \<le> i0"
            "i0 < l_bucket_end \<alpha> T ?b"
            "SA ! i0 = Suc x"
            by blast
          hence "i \<le> i0"
            using \<open>i \<le> bucket_start \<alpha> T ?b\<close> dual_order.trans by blast
          hence "i = i0 \<or> i < i0"
            by linarith
          then show ?thesis
          proof
            assume "i = i0"
            hence "x = j"
              using \<open>SA ! i0 = Suc x\<close> assms(16,18) by auto
            then show ?thesis
              using \<open>\<alpha> (T ! x) = b'\<close> \<open>b < b'\<close> assms(20) by blast
          next
            assume "i < i0"
            with s_suc_invD[OF assms(7) `i0 < length _` _ `SA ! i0 = _` `suffix_type T x = S_type`]
                 `\<alpha> (T ! x) = b'`
            obtain i1 where
              "in_s_current_bucket \<alpha> T B b' i1"
              "SA ! i1 = x"
              "i1 < i0"
              by auto
            with in_s_current_bucket_list_slice[OF assms(11)]
            have "x \<in> set ?xs"
              by blast
            then show ?thesis
              using \<open>x \<in> ?S\<close> by blast
          qed
        qed
        moreover
        have "suffix_type T (Suc x) = S_type \<Longrightarrow> ?thesis"
        proof -
          assume "suffix_type T (Suc x) = S_type"
          with `set ?zs = s_bucket \<alpha> T ?b` `Suc x < length T`
          have "Suc x \<in> set ?zs"
            by (simp add: s_bucket_def bucket_def)

          from nth_mem_list_slice[OF `Suc x \<in> set ?zs`]
          obtain i0 where
            "i0 < length SA"
            "s_bucket_start \<alpha> T ?b \<le> i0"
            "i0 < bucket_end \<alpha> T ?b"
            "SA ! i0 = Suc x"
            by blast
          hence "i \<le> i0"
            by (meson \<open>i \<le> bucket_start \<alpha> T ?b\<close> bucket_start_le_s_bucket_start dual_order.trans)
          hence "i = i0 \<or> i < i0"
            by linarith
          then show ?thesis
          proof
            assume "i = i0"
            hence "x = j"
              using \<open>SA ! i0 = Suc x\<close> assms(16,18) by auto
            then show ?thesis
              using \<open>\<alpha> (T ! x) = b'\<close> \<open>b < b'\<close> assms(20) by blast
          next
            assume "i < i0"
            with s_suc_invD[OF assms(7) `i0 < length _` _ `SA ! i0 = _` `suffix_type T x = S_type`]
                 `\<alpha> (T ! x) = b'`
            obtain i1 where
              "in_s_current_bucket \<alpha> T B b' i1"
              "SA ! i1 = x"
              "i1 < i0"
              by auto
            with in_s_current_bucket_list_slice[OF assms(11)]
            have "x \<in> set ?xs"
              by blast
            then show ?thesis
              using \<open>x \<in> ?S\<close> by blast
          qed
        qed
        ultimately show ?thesis
          using SL_types.exhaust by blast
      next
        assume "Suc x \<in> set ?xs"

        from nth_mem_list_slice[OF `Suc x \<in> set ?xs`]
        obtain i0 where
          "i0 < length SA"
          "B ! b' \<le> i0"
          "i0 < bucket_end \<alpha> T b'"
          "SA ! i0 = Suc x"
          by blast
        with `B ! b' = i`
        have "i \<le> i0"
          by blast
        hence "i = i0 \<or> i < i0"
          by linarith
        then show ?thesis
        proof
          assume "i = i0"
          hence "x = j"
            using \<open>SA ! i0 = Suc x\<close> assms(16,18) by auto
          then show ?thesis
            using \<open>\<alpha> (T ! x) = b'\<close> \<open>b < b'\<close>  assms(20) by blast
        next
          assume "i < i0"
          with s_suc_invD[OF assms(7) `i0 < length _` _ `SA ! i0 = _` `suffix_type T x = _`]
               `\<alpha> (T ! x) = b'`
          obtain i1 where
            "in_s_current_bucket \<alpha> T B b' i1"
            "SA ! i1 = x"
            "i1 < i0"
            by blast
          with in_s_current_bucket_list_slice[OF assms(11)]
          have "x \<in> set ?xs"
            by blast
          then show ?thesis
            using \<open>x \<in> ?S\<close> by blast
        qed
      qed
    qed
    ultimately show ?thesis
      by linarith
  qed
  moreover
  have "b = b' \<Longrightarrow> ?g1 \<and> ?g2 \<and> ?g3"
  proof -
    assume "b = b'"
    have "k = i' \<Longrightarrow> ?thesis"
    proof -
      assume "k = i'"
      hence "SA[k := j] ! i' = j"
        using \<open>i' < length (SA[k := j])\<close> by auto
      with `suffix_type T j = S_type` `j < length T` `in_s_current_bucket \<alpha> T (B[b := k]) b k`
           assms(20) `k = i'`
      show ?thesis
        by simp
    qed
    moreover
    have "k < i' \<Longrightarrow> ?thesis"
    proof -
      assume "k < i'"
      hence "B ! b \<le> i'"
        using assms(21) by linarith
      with s_locations_invD[OF assms(3) `b' \<le> \<alpha> _` _ `i' < bucket_end _ _ _`] `b = b'`
      have "SA ! i' \<in> s_bucket \<alpha> T b'"
        by blast
      hence "suffix_type T (SA ! i') = S_type" "\<alpha> (T ! (SA ! i')) = b'"
        by (simp add: s_bucket_def bucket_def)+
      moreover
      have "SA[k := j] ! i' = SA ! i'"
        using `k < i'` by simp
      moreover
      have "in_s_current_bucket \<alpha> T (B[b := k]) b' i'"
        by (metis (no_types, lifting) \<open>b = b'\<close> \<open>b' \<le> \<alpha> (Max (set T))\<close> \<open>i' < bucket_end \<alpha> T b'\<close>
              \<open>k \<le> i'\<close> assms(9) dual_order.strict_trans2 in_s_current_bucket_def nth_list_update_eq)
      ultimately show ?thesis
        by (simp add: suffix_type_s_bound)
    qed
    ultimately show ?thesis
      using `k \<le> i'` dual_order.order_iff_strict by blast
  qed
  ultimately show "?g1 \<and> ?g2 \<and> ?g3"
    using \<open>b \<le> b'\<close> dual_order.order_iff_strict by blast
qed

corollary s_seen_inv_maintained_perm_step_c4:
  assumes "s_perm_inv \<alpha> T B SA0 SA i"
  and     "i = Suc n"
  and     "Suc n < length SA"
  and     "SA ! Suc n = Suc j"
  and     "suffix_type T j = S_type"
  and     "b = \<alpha> (T ! j)"
  and     "k = B ! b - Suc 0"
shows "s_seen_inv \<alpha> T (B[b := k]) (SA[k := j]) n"
  using s_seen_inv_maintained_step_c4[OF s_perm_inv_elims[OF assms(1)] assms(2-)]
  by blast

lemmas s_seen_inv_maintained_perm_step =
  s_seen_inv_maintained_perm_step_c1
  s_seen_inv_maintained_perm_step_c2
  s_seen_inv_maintained_perm_step_c3
  s_seen_inv_maintained_perm_step_c4

subsubsection "Predecessor"

lemma s_pred_inv_established:
  assumes "s_bucket_init \<alpha> T B"
shows "s_pred_inv \<alpha> T B SA n"
  unfolding s_pred_inv_def
proof (safe)
  fix b i
  assume A: "in_s_current_bucket \<alpha> T B b i" "0 < b"

  let ?goal = "\<exists>j<length SA. SA ! j = Suc (SA ! i) \<and> i < j \<and> n < j"

  have "b = 0 \<or> 0 < b"
    by blast
  moreover
  from A(2)
  have "b = 0 \<Longrightarrow> ?goal"
    by blast
  moreover
  have "0 < b \<Longrightarrow> ?goal"
  proof -
    assume "0 < b"
    with s_bucket_initD(1)[OF assms(1) in_s_current_bucketD(1)[OF A(1)]]
    have "B ! b = bucket_end \<alpha> T b" .
    with in_s_current_bucketD(2,3)[OF A(1)]
    show ?goal
      by linarith
  qed
  ultimately show ?goal
    by blast
qed

lemma s_pred_inv_maintained_step_alt:
  assumes "s_pred_inv \<alpha> T B SA i"
  and     "i = Suc n"
shows "s_pred_inv \<alpha> T B SA n"
  unfolding s_pred_inv_def
proof (intro allI impI; elim conjE)
  fix b i'
  assume "in_s_current_bucket \<alpha> T B b i'" "b \<noteq> 0"
  with s_pred_invD[OF assms(1), of b i'] assms(2)
  show  "\<exists>j<length SA. SA ! j = Suc (SA ! i') \<and> i' < j \<and> n < j"
    using Suc_lessD by blast
qed

corollary s_pred_inv_maintained_perm_step_alt:
  assumes "s_perm_inv \<alpha> T B SA0 SA i"
  and     "i = Suc n"
shows "s_pred_inv \<alpha> T B SA n"
  using s_pred_inv_maintained_step_alt[OF s_perm_inv_elims(6), OF assms]
  by blast

lemma s_pred_inv_maintained_step:
  assumes "s_distinct_inv \<alpha> T B SA"
  and     "s_bucket_ptr_inv \<alpha> T B"
  and     "s_locations_inv \<alpha> T B SA"
  and     "s_unchanged_inv \<alpha> T B SA0 SA"
  and     "s_seen_inv \<alpha> T B SA i"
  and     "s_pred_inv \<alpha> T B SA i"
  and     "s_suc_inv \<alpha> T B SA i"
  and     "strict_mono \<alpha>"
  and     "\<alpha> (Max (set T)) < length B"
  and     "length SA0 = length T"
  and     "length SA = length T"
  and     "l_types_init \<alpha> T SA0"
  and     "valid_list T"
  and     "\<alpha> bot = 0"
  and     "Suc 0 < length T"
  and     "i = Suc n"
  and     "Suc n < length SA"
  and     "SA ! Suc n = Suc j"
  and     "suffix_type T j = S_type"
  and     "b = \<alpha> (T ! j)"
  and     "k = B ! b - Suc 0"
shows "s_pred_inv \<alpha> T (B[b := k]) (SA[k := j]) n"
  unfolding s_pred_inv_def
proof(safe)
  fix b' i'
  assume "in_s_current_bucket \<alpha> T (B[b := k]) b' i'" "0 < b'"
  hence "b' \<noteq> 0"
    by linarith

  let ?goal = "\<exists>j'<length (SA[k := j]). SA[k := j] ! j' = Suc (SA[k := j] ! i') \<and> i' < j' \<and> n < j'"

  from s_bucket_ptr_strict_lower_bound[OF assms(1-6,8,10-14,16-20)]
  have "s_bucket_start \<alpha> T b < B ! b".
  hence "s_bucket_start \<alpha> T b \<le> k"
    using assms(21) by linarith
  hence "bucket_start \<alpha> T b \<le> k"
    using bucket_start_le_s_bucket_start le_trans by blast

  from `s_bucket_start \<alpha> T b < B ! b`
  have "k < B ! b"
    using assms(21) by linarith

  have "j < length T"
    by (simp add: assms(19) suffix_type_s_bound)
  hence "b \<le> \<alpha> (Max (set T))"
    by (simp add: assms(8,20) strict_mono_less_eq)
  with s_bucket_ptr_upper_bound[OF assms(2)]
  have "B ! b \<le> bucket_end \<alpha> T b"
    by blast
  with `k < B ! b`
  have "k < bucket_end \<alpha> T b"
    by linarith

  have "B ! b \<le> i"
  proof(rule ccontr)
    assume "\<not>B ! b \<le> i"
    hence "i < B ! b"
      by simp
    with s_B_val[OF assms(1-6,8,10-13,15) `b \<le> \<alpha> (Max (set T))`] `s_bucket_start \<alpha> T b < B ! b`
    show False
      by simp
  qed
  with `k < B ! b`
  have "k < i"
    by linarith

  have "b \<noteq> b' \<Longrightarrow> ?goal"
  proof -
    assume "b \<noteq> b'"
    hence "B[b := k] ! b' = B ! b'"
      by simp
    with `in_s_current_bucket \<alpha> T (B[b := k]) b' i'`
    have "in_s_current_bucket \<alpha> T B b' i'"
      by (simp add: in_s_current_bucket_def)
    with s_pred_invD[OF assms(6) _ `b' \<noteq> 0`]
    obtain j' where
      "j' < length SA"
      "SA ! j' = Suc (SA ! i')"
      "i' < j'"
      "i < j'"
      by blast
    moreover
    from `in_s_current_bucket \<alpha> T B b' i'`
    have "B ! b' \<le> i'" "i' < bucket_end \<alpha> T b'"
      by (simp_all add: in_s_current_bucket_def)
    with s_bucket_ptr_lower_bound[OF assms(2)]
         in_s_current_bucketD(1)[OF `in_s_current_bucket _ _ B _ _`]
    have "bucket_start \<alpha> T b' \<le> i'"
      by (meson bucket_start_le_s_bucket_start le_trans)
    with outside_another_bucket[OF `b \<noteq> b'` `bucket_start _ _ _ \<le> k` `k < bucket_end _ _ _`]
         `i' < bucket_end \<alpha> T b'`
    have "k \<noteq> i'"
      by blast
    hence "SA[k := j] ! i' = SA ! i'"
      by simp
    moreover
    from `i < j'` assms(16)
    have "n < j'"
      using Suc_lessD by blast
    moreover
    have "SA[k := j] ! j' = SA ! j'"
      using \<open>k < i\<close> calculation(4) by auto
    ultimately show ?thesis
      by auto
  qed
  moreover
  have "b = b' \<Longrightarrow> ?goal"
  proof -
    assume "b = b'"
    hence "B[b := k] ! b' = k"
      using \<open>b \<le> \<alpha> (Max (set T))\<close> assms(9) by auto

    have "k = i' \<Longrightarrow> ?goal"
    proof -
      assume "k = i'"
      hence "SA[k := j] ! i' = j"
        using \<open>k < i\<close> assms(16,17) by auto
      moreover
      have "SA[k := j] ! i = SA ! i"
        using \<open>k < i\<close> by auto
      ultimately show ?goal
        using assms(16-18) `k = i'` `k < i`
        by auto
    qed
    moreover
    have "k \<noteq> i' \<Longrightarrow> ?goal"
    proof -
      assume "k \<noteq> i'"
      with `in_s_current_bucket \<alpha> T (B[b := k]) b' i'` `B[b := k] ! b' = k`
      have "k < i'"
        by (simp add: in_s_current_bucket_def)
      hence "B ! b' \<le> i'"
        using assms(21) `b = b'` `k < B ! b` by simp
      hence "in_s_current_bucket \<alpha> T B b' i'"
        using \<open>in_s_current_bucket \<alpha> T (B[b := k]) b' i'\<close> in_s_current_bucket_def by blast
      with s_pred_invD[OF assms(6) _ `b' \<noteq> 0`]
      obtain j' where
        "j' < length SA"
        "SA ! j' = Suc (SA ! i')"
        "i' < j'"
        "i < j'"
        by blast
      moreover
      have "SA[k := j] ! i' = SA ! i'"
        using `k \<noteq> i'` by simp
      moreover
      have "SA[k := j] ! j' = SA ! j'"
        using `k < i'` `i' < j'`
        by auto
      ultimately show ?goal
        using assms(16) by auto
    qed
    ultimately show ?goal
      by blast
  qed
  ultimately show ?goal
    by blast
qed

corollary s_pred_inv_maintained_perm_step:
  assumes "s_perm_inv \<alpha> T B SA0 SA i"
  and     "i = Suc n"
  and     "Suc n < length SA"
  and     "SA ! Suc n = Suc j"
  and     "suffix_type T j = S_type"
  and     "b = \<alpha> (T ! j)"
  and     "k = B ! b - Suc 0"
shows "s_pred_inv \<alpha> T (B[b := k]) (SA[k := j]) n"
  using s_pred_inv_maintained_step[OF s_perm_inv_elims[OF assms(1)] assms(2-)]
  by blast

subsubsection "Successor"

lemma s_suc_inv_established:
  assumes "length SA = length T"
  and     "length T \<le> n"
shows "s_suc_inv \<alpha> T B SA n"
  unfolding s_suc_inv_def
  using assms(1) assms(2) by linarith

lemma s_suc_inv_maintained_step_c1:
  assumes "length SA \<le> Suc n"
shows "s_suc_inv \<alpha> T B SA n"
  unfolding s_suc_inv_def
proof (intro allI impI; elim conjE)
  fix i' j
  assume "i' < length SA" "n < i'" "SA ! i' = Suc j" "suffix_type T j = S_type"
  with assms
  have False
    using less_trans_Suc not_less by blast
  then show "\<exists>k. in_s_current_bucket \<alpha> T B (\<alpha> (T ! j)) k \<and> SA ! k = j \<and> k < i'"
    by blast
qed

corollary s_suc_inv_maintained_perm_step_c1:
  assumes "s_perm_inv \<alpha> T B SA0 SA i"
  and     "i = Suc n"
  and     "length SA \<le> Suc n"
shows "s_suc_inv \<alpha> T B SA n"
  by (simp add: assms(3) s_suc_inv_maintained_step_c1)

lemma s_suc_inv_maintained_step_c1_alt:
  assumes "s_suc_inv \<alpha> T B SA i"
  and     "s_bucket_ptr_inv \<alpha> T B"
  and     "s_locations_inv \<alpha> T B SA"
  and     "strict_mono \<alpha>"
  and     "\<alpha> (Max (set T)) < length B"
  and     "valid_list T"
  and     "\<alpha> bot = 0"
  and     "i = Suc n"
  and     "length T \<le> SA ! Suc n"
  shows "s_suc_inv \<alpha> T B SA n"
proof (cases "length SA \<le> Suc n")
  case True
  then show ?thesis
    by (simp add: s_suc_inv_maintained_step_c1)
next
  case False
  hence "Suc n < length SA"
    by simp
  show ?thesis
    unfolding s_suc_inv_def
  proof (intro allI impI; elim conjE)
    fix i' j
    let ?goal = "\<exists>k. in_s_current_bucket \<alpha> T B (\<alpha> (T ! j)) k \<and> SA ! k = j \<and> k < i'"
    assume "i' < length SA" "n < i'" "SA ! i' = Suc j" "suffix_type T j = S_type"
    hence "i' = Suc n \<or> Suc n < i'"
      using Suc_lessI by blast
    moreover
    from s_suc_invD[OF assms(1) \<open>i' < length SA\<close> _ \<open>SA ! i' = Suc j\<close> \<open>suffix_type T j = S_type\<close>]
    have "Suc n < i' \<Longrightarrow> ?goal"
      using \<open>i = Suc n\<close> by blast
    moreover
    have "i' = Suc n \<Longrightarrow> ?goal"
    proof -
      assume "i' = Suc n"
      have "j < length T \<or> length T \<le> j"
        using linorder_not_le by blast
      moreover
      have "length T \<le> j \<Longrightarrow> ?goal"
        by (meson \<open>suffix_type T j = S_type\<close> linorder_not_le suffix_type_s_bound)
      moreover
      have "j < length T \<Longrightarrow> ?goal"
      proof -
        assume "j < length T"
        hence "length T = Suc j"
          using \<open>SA ! i' = Suc j\<close> \<open>i' = Suc n\<close> \<open>length T \<le> SA ! Suc n\<close> by force
        hence "T ! j = bot"
          by (metis \<open>valid_list T\<close> diff_Suc_1 last_conv_nth length_greater_0_conv valid_list_def)
        hence "\<alpha> (T ! j) = 0"
          using \<open>\<alpha> bot = 0\<close> by presburger
        hence "in_s_current_bucket \<alpha> T B (\<alpha> (T ! j)) 0"
          unfolding in_s_current_bucket_def
          using One_nat_def assms(2,4,6,7) lessI s_bucket_ptr_0 valid_list_bucket_end_0
          by fastforce
        moreover
        {
          have "0 < bucket_end \<alpha> T 0"
            using \<open>\<alpha> (T ! j) = 0\<close> calculation in_s_current_bucket_def by fastforce
          with s_bucket_ptr_0[OF assms(2), of 0, simplified]
               s_locations_invD[OF assms(3), of 0 0, simplified]
          have "SA ! 0 \<in> s_bucket \<alpha> T 0"
            by simp
          moreover
          have "s_bucket \<alpha> T 0 = {j}"
            by (simp add: \<open>length T = Suc j\<close> assms(4) assms(6) assms(7) s_bucket_0)
          ultimately have "SA ! 0 = j"
            by blast
        }
        ultimately show ?goal
          using \<open>i' = Suc n\<close> by blast
      qed
      ultimately show ?goal
        by blast
    qed
    ultimately show ?goal
      by blast
  qed
qed

corollary s_suc_inv_maintained_perm_step_c1_alt:
  assumes "s_perm_inv \<alpha> T B SA0 SA i"
  and     "i = Suc n"
  and     "length T \<le> SA ! Suc n"
shows "s_suc_inv \<alpha> T B SA n"
  using assms s_perm_inv_def s_suc_inv_maintained_step_c1_alt by blast

lemma s_suc_inv_maintained_step_c2:
  assumes "s_suc_inv \<alpha> T B SA i"
  and     "i = Suc n"
  and     "Suc n < length SA"
  and     "SA ! Suc n = 0"
shows "s_suc_inv \<alpha> T B SA n"
  unfolding s_suc_inv_def
proof (intro allI impI; elim conjE)
  fix i' j
  assume "i' < length SA" "n < i'" "SA ! i' = Suc j" "suffix_type T j = S_type"

  let ?goal = "\<exists>k. in_s_current_bucket \<alpha> T B (\<alpha> (T ! j)) k \<and> SA ! k = j \<and> k < i'"

  from `n < i'` `i = Suc n`
  have "i = i' \<or> i < i'"
    by linarith
  moreover
  from assms(2,4) `SA ! i' = Suc j`
  have "i = i' \<Longrightarrow> ?goal"
    by simp
  moreover
  from s_suc_invD[OF assms(1) `i' < _` _ `SA ! i' = _` `suffix_type T j = _`] assms(2)
  have "i < i' \<Longrightarrow> ?goal"
    by blast
  ultimately show ?goal
    by blast
qed

corollary s_suc_inv_maintained_perm_step_c2:
  assumes "s_perm_inv \<alpha> T B SA0 SA i"
  and     "i = Suc n"
  and     "Suc n < length SA"
  and     "SA ! Suc n = 0"
shows "s_suc_inv \<alpha> T B SA n"
  using assms s_perm_inv_elims(7) s_suc_inv_maintained_step_c2 by blast

lemma s_suc_inv_maintained_step_c3:
  assumes "s_suc_inv \<alpha> T B SA i"
  and     "i = Suc n"
  and     "Suc n < length SA"
  and     "SA ! Suc n = Suc j"
  and     "suffix_type T j = L_type"
shows "s_suc_inv \<alpha> T B SA n"
  unfolding s_suc_inv_def
proof (intro allI impI; elim conjE)
  fix i' j'
  assume "i' < length SA" "n < i'" "SA ! i' = Suc j'" "suffix_type T j' = S_type"

  let ?goal = "\<exists>k. in_s_current_bucket \<alpha> T B (\<alpha> (T ! j')) k \<and> SA ! k = j' \<and> k < i'"

  from `n < i'` assms(2)
  have "i = i' \<or> i < i'"
    using Suc_lessI by blast
  moreover
  from assms(2,4,5) `SA ! i' = _` `suffix_type T j' = _`
  have "i = i' \<Longrightarrow> ?goal"
    by simp
  moreover
  from s_suc_invD[OF assms(1) `i' < _` _ `SA ! i' = _` `suffix_type T j' = _`]
  have "i < i' \<Longrightarrow> ?goal"
    by blast
  ultimately show ?goal
    by blast
qed

corollary s_suc_inv_maintained_perm_step_c3:
  assumes "s_perm_inv \<alpha> T B SA0 SA i"
  and     "i = Suc n"
  and     "Suc n < length SA"
  and     "SA ! Suc n = Suc j"
  and     "suffix_type T j = L_type"
shows "s_suc_inv \<alpha> T B SA n"
  using assms s_perm_inv_elims(7) s_suc_inv_maintained_step_c3 by blast

lemma s_suc_inv_maintained_step_c4:
  assumes "s_distinct_inv \<alpha> T B SA"
  and     "s_bucket_ptr_inv \<alpha> T B"
  and     "s_locations_inv \<alpha> T B SA"
  and     "s_unchanged_inv \<alpha> T B SA0 SA"
  and     "s_seen_inv \<alpha> T B SA i"
  and     "s_pred_inv \<alpha> T B SA i"
  and     "s_suc_inv \<alpha> T B SA i"
  and     "strict_mono \<alpha>"
  and     "\<alpha> (Max (set T)) < length B"
  and     "length SA0 = length T"
  and     "length SA = length T"
  and     "l_types_init \<alpha> T SA0"
  and     "valid_list T"
  and     "\<alpha> bot = 0"
  and     "Suc 0 < length T"
  and     "i = Suc n"
  and     "Suc n < length SA"
  and     "SA ! Suc n = Suc j"
  and     "suffix_type T j = S_type"
  and     "b = \<alpha> (T ! j)"
  and     "k = B ! b - Suc 0"
shows "s_suc_inv \<alpha> T (B[b := k]) (SA[k := j]) n"
  unfolding s_suc_inv_def
proof(safe)
  fix i' j'
  assume "i' < length (SA[k := j])" "n < i'" "SA[k := j] ! i' = Suc j'" "suffix_type T j' = S_type"
  hence "i' < length SA"
    by simp

  let ?b = "\<alpha> (T ! j')"
  and ?B = "B[b := k]"
  and ?SA = "SA[k := j]"

  let ?goal = "\<exists>k'. in_s_current_bucket \<alpha> T ?B ?b k' \<and> ?SA ! k' = j' \<and> k' < i'"

  from `suffix_type T j' = _`
  have "j' < length T"
    by (simp add: suffix_type_s_bound)
  hence "?b \<le> \<alpha> (Max (set T))"
    using `strict_mono _`
    by (simp add: strict_mono_less_eq)

  from s_bucket_ptr_strict_lower_bound[OF assms(1-6,8,10-14,16-20)]
  have "s_bucket_start \<alpha> T b < B ! b".
  hence "s_bucket_start \<alpha> T b \<le> k"
    using assms(21) by linarith
  hence "bucket_start \<alpha> T b \<le> k"
    using bucket_start_le_s_bucket_start le_trans by blast

  from `s_bucket_start \<alpha> T b < B ! b`
  have "k < B ! b"
    using assms(21) by linarith

  have "j < length T"
    by (simp add: assms(19) suffix_type_s_bound)
  hence "b \<le> \<alpha> (Max (set T))"
    by (simp add: assms(8,20) strict_mono_less_eq)
  with s_bucket_ptr_upper_bound[OF assms(2)]
  have "B ! b \<le> bucket_end \<alpha> T b"
    by blast
  with `k < B ! b`
  have "k < bucket_end \<alpha> T b"
    by linarith

  have "B ! b \<le> i"
  proof(rule ccontr)
    assume "\<not>B ! b \<le> i"
    hence "i < B ! b"
      by simp
    with s_B_val[OF assms(1-6,8,10-13,15) `b \<le> \<alpha> (Max (set T))`] `s_bucket_start \<alpha> T b < B ! b`
    show False
      by simp
  qed
  with `k < B ! b`
  have "k < i"
    by linarith
  hence "k \<le> n"
    by (simp add: assms(16))
  with `n < i'`
  have "k < i'"
    using dual_order.strict_trans2 by blast
  hence "SA[k := j] ! i' = SA ! i'"
    by simp
  with `SA[k := j] ! i' = Suc j'`
  have "SA ! i' = Suc j'"
    by simp

  have "i \<le> i'"
    by (simp add: Suc_leI \<open>n < i'\<close> assms(16))
  hence "i = i' \<or> i < i'"
    by (simp add: nat_less_le)
  moreover
  have "i = i' \<Longrightarrow> ?goal"
  proof -
    assume "i = i'"
    hence "j = j'"
      using \<open>SA ! i' = Suc j'\<close> assms(16,18) by auto
    hence "SA[k := j] ! k = j'"
      using \<open>k \<le> n\<close> assms(17) by auto
    moreover
    have "?b = b"
      using \<open>j = j'\<close> assms(20) by blast
    hence "in_s_current_bucket \<alpha> T ?B ?b k = in_s_current_bucket \<alpha> T ?B b k"
      by simp
    moreover
    from `\<alpha> (T ! j') \<le> \<alpha> (Max (set T))`
         `?b = b`[symmetric]
    have "in_s_current_bucket \<alpha> T ?B b k"
      unfolding in_s_current_bucket_def
      using \<open>k < bucket_end \<alpha> T b\<close> assms(9) by auto
    ultimately show ?goal
      using `k < i'` by blast
  qed
  moreover
  have "i < i' \<Longrightarrow> ?goal"
  proof -
    assume "i < i'"
    with s_suc_invD[OF assms(7) `i' < length SA` _ `SA ! i' = Suc j'` `suffix_type T j' = _`]
    obtain k' where
      "in_s_current_bucket \<alpha> T B ?b k'"
      "SA ! k' = j'"
      "k' < i'"
      by blast
    moreover
    from in_s_current_bucketD[OF `in_s_current_bucket \<alpha> T B ?b k'`]
    have "in_s_current_bucket \<alpha> T ?B ?b k'"
      unfolding in_s_current_bucket_def
    proof (safe)
      show "?B ! ?b \<le> k'"
        by (metis \<open>B ! ?b \<le> k'\<close> \<open>k < B ! b\<close> dual_order.trans list_update_beyond nat_le_linear
              not_less nth_list_update_eq nth_list_update_neq)
    qed
    moreover
    from in_s_current_bucketD(2)[OF `in_s_current_bucket \<alpha> T B ?b k'`]
    have "B ! ?b \<le> k'" .
    hence "s_bucket_start \<alpha> T ?b \<le> k'"
      by (meson \<open>?b \<le> \<alpha> (Max (set T))\<close> assms(2) le_less_trans not_le s_bucket_ptr_inv_def)
    hence "bucket_start \<alpha> T ?b \<le> k'"
      using bucket_start_le_s_bucket_start dual_order.trans by blast

    have "b = ?b \<or> b \<noteq> ?b"
      by blast
    hence "k \<noteq> k'"
    proof
      assume "b = ?b"
      with `B ! ?b \<le> k'` `k < B ! b`
      show ?thesis
        by simp
    next
      assume "b \<noteq> ?b"
      with outside_another_bucket[OF _  `bucket_start _ _ _ \<le> k` `k < bucket_end _ _ _`]
           `bucket_start \<alpha> T ?b \<le> k'` in_s_current_bucketD(3)[OF `in_s_current_bucket \<alpha> T B ?b k'`]
      show ?thesis
        by blast
    qed
    hence "SA[k := j] ! k' = SA ! k'"
      by simp
    ultimately show ?goal
      by blast
  qed
  ultimately show ?goal
    by blast
qed

corollary s_suc_inv_maintained_perm_step_c4:
  assumes "s_perm_inv \<alpha> T B SA0 SA i"
  and     "i = Suc n"
  and     "Suc n < length SA"
  and     "SA ! Suc n = Suc j"
  and     "suffix_type T j = S_type"
  and     "b = \<alpha> (T ! j)"
  and     "k = B ! b - Suc 0"
shows "s_suc_inv \<alpha> T (B[b := k]) (SA[k := j]) n"
  using s_suc_inv_maintained_step_c4[OF s_perm_inv_elims[OF assms(1)] assms(2-)]
  by blast

lemmas s_suc_inv_maintained_perm_step =
  s_suc_inv_maintained_step_c1
  s_suc_inv_maintained_perm_step_c2
  s_suc_inv_maintained_perm_step_c3
  s_suc_inv_maintained_perm_step_c4

subsubsection "Combined Permutation Invariant"

lemma s_perm_inv_established:
  assumes "s_bucket_init \<alpha> T B"
  and     "s_type_init T SA"
  and     "strict_mono \<alpha>"
  and     "\<alpha> (Max (set T)) < length B"
  and     "length SA = length T"
  and     "l_types_init \<alpha> T SA"
  and     "valid_list T"
  and     "\<alpha> bot = 0"
  and     "Suc 0 < length T"
  and     "length T \<le> n"
shows "s_perm_inv \<alpha> T B SA SA n"
  unfolding s_perm_inv_def
  by (simp add: assms s_distinct_inv_established s_bucket_ptr_inv_established
                s_locations_inv_established s_unchanged_inv_established s_seen_inv_established
                s_pred_inv_established s_suc_inv_established)

lemma s_perm_inv_maintained_step_c1:
  assumes "s_perm_inv \<alpha> T B SA0 SA i"
  and     "i = Suc n"
  and     "length SA \<le> Suc n"
shows "s_perm_inv \<alpha> T B SA0 SA n"
  unfolding s_perm_inv_def
  by (clarsimp simp: s_perm_inv_elims[OF assms(1)]
                     s_seen_inv_maintained_perm_step_c1[OF assms]
                     s_pred_inv_maintained_perm_step_alt[OF assms(1,2)]
                     s_suc_inv_maintained_step_c1[OF assms(3)])

lemma s_perm_inv_maintained_step_c1_alt:
  assumes "s_perm_inv \<alpha> T B SA0 SA i"
  and     "i = Suc n"
  and     "length T \<le> SA ! Suc n"
shows "s_perm_inv \<alpha> T B SA0 SA n"
proof (cases "length T \<le> Suc n")
  case True
  then show ?thesis
    by (metis assms(1) assms(2) s_perm_inv_elims(11) s_perm_inv_maintained_step_c1)
next
  case False
  hence "Suc n < length T"
    by simp
  then show ?thesis
    unfolding s_perm_inv_def
    by (metis assms s_perm_inv_def s_pred_inv_maintained_step_alt
              s_seen_inv_maintained_perm_step_c1_alt s_suc_inv_maintained_perm_step_c1_alt)
qed

lemma s_perm_inv_maintained_step_c2:
  assumes "s_perm_inv \<alpha> T B SA0 SA i"
  and     "i = Suc n"
  and     "Suc n < length SA"
  and     "SA ! Suc n = 0"
shows "s_perm_inv \<alpha> T B SA0 SA n"
  unfolding s_perm_inv_def
  by (clarsimp simp: s_perm_inv_elims[OF assms(1)]
                     s_seen_inv_maintained_perm_step_c2[OF assms]
                     s_pred_inv_maintained_perm_step_alt[OF assms(1,2)]
                     s_suc_inv_maintained_perm_step_c2[OF assms])

lemma s_perm_inv_maintained_step_c3:
  assumes "s_perm_inv \<alpha> T B SA0 SA i"
  and     "i = Suc n"
  and     "Suc n < length SA"
  and     "SA ! Suc n = Suc j"
  and     "suffix_type T j = L_type"
shows "s_perm_inv \<alpha> T B SA0 SA n"
  unfolding s_perm_inv_def
  by (clarsimp simp: s_perm_inv_elims[OF assms(1)]
                     s_seen_inv_maintained_perm_step_c3[OF assms]
                     s_pred_inv_maintained_perm_step_alt[OF assms(1,2)]
                     s_suc_inv_maintained_perm_step_c3[OF assms])

lemma s_perm_inv_maintained_step_c4:
  assumes "s_perm_inv \<alpha> T B SA0 SA i"
  and     "i = Suc n"
  and     "Suc n < length SA"
  and     "SA ! Suc n = Suc j"
  and     "suffix_type T j = S_type"
  and     "b = \<alpha> (T ! j)"
  and     "k = B ! b - Suc 0"
shows "s_perm_inv \<alpha> T (B[b := k]) SA0 (SA[k := j]) n"
  unfolding s_perm_inv_def
  by (clarsimp simp: s_perm_inv_elims[OF assms(1)]
                     s_distinct_inv_maintained_perm_step[OF assms]
                     s_bucket_ptr_inv_maintained_perm_step[OF assms]
                     s_locations_inv_maintained_perm_step[OF assms]
                     s_unchanged_inv_maintained_perm_step[OF assms]
                     s_seen_inv_maintained_perm_step_c4[OF assms]
                     s_pred_inv_maintained_perm_step[OF assms]
                     s_suc_inv_maintained_perm_step_c4[OF assms])

theorem abs_induce_s_perm_step:
  assumes "s_perm_inv \<alpha> T B SA0 SA i"
  and     "abs_induce_s_step (B, SA, i) (\<alpha>, T) = (B', SA', i')"
shows "s_perm_inv \<alpha> T B' SA0 SA' i'"
proof (cases i)
  case 0
  then show ?thesis
    using assms by force
next
  case (Suc n)
  assume "i = Suc n"
  have "T \<noteq> []"
    using s_perm_inv_elims(15)[OF assms(1)] by fastforce
  show ?thesis
  proof (cases "Suc n < length SA \<and> SA ! Suc n < length T")
    assume "Suc n < length SA \<and> SA ! Suc n < length T"
    hence "Suc n < length SA" "SA ! Suc n < length T"
      by blast+
    show ?thesis
    proof (cases "SA ! Suc n")
      case 0
      then show ?thesis
        using s_perm_inv_maintained_step_c2[OF assms(1) \<open>i = Suc n\<close> \<open>Suc n < length SA\<close> "0"] assms
        by (clarsimp simp: \<open>i = Suc n\<close> \<open>Suc n < length SA\<close> "0" \<open>T \<noteq> []\<close>)
    next
      case (Suc j)
      assume "SA ! Suc n = Suc j"
      hence "Suc j < length T"
        using \<open>SA ! Suc n < length T\<close> by auto
      show ?thesis
      proof (cases "suffix_type T j")
        case S_type
        then show ?thesis
          using assms \<open>i = Suc n\<close> \<open>Suc n < length SA\<close> \<open>SA ! Suc n = Suc j\<close>
                s_perm_inv_maintained_step_c4[OF assms(1), of n j "\<alpha> (T ! j)" "B ! \<alpha> (T ! j) - Suc 0"]
          by (clarsimp simp: Let_def \<open>Suc j < length T\<close>)
      next
        case L_type
        then show ?thesis
          using assms \<open>i = Suc n\<close> \<open>Suc n < length SA\<close> \<open>SA ! Suc n = Suc j\<close>
                s_perm_inv_maintained_step_c3[OF assms(1)]
          by (clarsimp simp: Let_def \<open>Suc j < length T\<close>)
      qed
    qed
  next
    assume "\<not>(Suc n < length SA \<and> SA ! Suc n < length T)" 
    hence "\<not> Suc n < length SA \<or> \<not> SA ! Suc n < length T"
      by blast
    then show ?thesis
    proof
      assume "\<not> Suc n < length SA"
      then show ?thesis
        using assms \<open>i = Suc n\<close> s_perm_inv_maintained_step_c1[OF assms(1)] by force
    next
      assume "\<not> SA ! Suc n < length T"
      hence "length T \<le> SA ! Suc n"
        by simp
      then show ?thesis
        using assms \<open>i = Suc n\<close> s_perm_inv_maintained_step_c1_alt[OF assms(1)] by simp
    qed
  qed
qed

corollary abs_induce_s_perm_step_alt:
 "\<And>a. s_perm_inv_alt \<alpha> T SA0 a \<Longrightarrow> s_perm_inv_alt \<alpha> T SA0 (abs_induce_s_step a (\<alpha>, T))"
  by (metis abs_induce_s_perm_step s_perm_inv_alt.elims(2) s_perm_inv_alt.elims(3))

theorem abs_induce_s_perm_alt_maintained:
  assumes "s_perm_inv_alt \<alpha> T SA0 (B, SA, length T)"
  shows "s_perm_inv_alt \<alpha> T SA0 (abs_induce_s_base \<alpha> T B SA)"
  unfolding abs_induce_s_base_def
  using repeat_maintain_inv[of "s_perm_inv_alt \<alpha> T SA0" abs_induce_s_step "(\<alpha>, T)", OF _ assms(1)]
        abs_induce_s_perm_step_alt
  by blast

corollary abs_induce_s_perm_maintained:
  assumes "abs_induce_s_base \<alpha> T B SA = (B', SA', n)"
  and     "s_perm_inv \<alpha> T B SA0 SA (length T)"
shows "s_perm_inv \<alpha> T B' SA0 SA' n"
  using assms abs_induce_s_perm_alt_maintained by force


lemma s_perm_inv_0_B_val:
  assumes "s_perm_inv \<alpha> T B SA SA' 0"
  and     "b \<le> \<alpha> (Max (set T))"
shows "B ! b = s_bucket_start \<alpha> T b"
proof -
  from s_bucket_ptr_lower_bound[OF s_perm_inv_elims(2)[OF assms(1)] assms(2)]
  have "s_bucket_start \<alpha> T b \<le> B ! b" .

  have "s_bucket_start \<alpha> T b \<ge> 0"
    by blast
  hence "s_bucket_start \<alpha> T b = 0 \<or> 0 < s_bucket_start \<alpha> T b"
    by blast
  with `s_bucket_start \<alpha> T b \<le> B ! b`
  have "B ! b = s_bucket_start \<alpha> T b \<or> 0 < B ! b"
    by linarith
  then show ?thesis
  proof
    assume "B ! b = s_bucket_start \<alpha> T b"
    then show ?thesis .
  next
    assume "0 < B ! b"
    with s_B_val[OF s_perm_inv_elims(1-6,8,10-13,15)[OF assms(1)] assms(2)]
    show ?thesis .
  qed
qed

lemma s_perm_inv_0_list_slice_bucket:
  assumes "s_perm_inv \<alpha> T B SA SA' 0"
  and     "b \<le> \<alpha> (Max (set T))"
shows "set (list_slice SA' (bucket_start \<alpha> T b) (bucket_end \<alpha> T b)) = bucket \<alpha> T b"
  by (meson assms bucket_eq_list_slice s_perm_inv_0_B_val s_perm_inv_elims(1-4,10-12))

lemma s_perm_inv_0_distinct_list_slice:
  assumes "s_perm_inv \<alpha> T B SA SA' 0"
  and     "b \<le> \<alpha> (Max (set T))"
shows "distinct (list_slice SA' (bucket_start \<alpha> T b) (bucket_end \<alpha> T b))"
      (is "distinct ?xs")
proof -
  let ?ys = "list_slice SA' (bucket_start \<alpha> T b) (l_bucket_end \<alpha> T b)"
  and ?zs = "list_slice SA' (s_bucket_start \<alpha> T b) (bucket_end \<alpha> T b)"

  have "?xs = ?ys @ ?zs"
    by (metis list_slice_append bucket_start_le_s_bucket_start l_bucket_end_le_bucket_end
          s_bucket_start_eq_l_bucket_end)

  from l_types_initD(1)[OF l_types_init_maintained[OF s_perm_inv_elims(2,4,10-12)[OF assms(1)]]
        assms(2)]
  have "set ?ys = l_bucket \<alpha> T b" .
  moreover
  from s_bucket_eq_list_slice[OF s_perm_inv_elims(1,3,11)[OF assms(1)] assms(2)
        s_perm_inv_0_B_val[OF assms]]
  have "set ?zs = s_bucket \<alpha> T b" .
  ultimately have "set ?ys \<inter> set ?zs = {}"
    using disjoint_l_s_bucket by blast
  with s_distinct_invD[OF s_perm_inv_elims(1), OF assms, simplified s_perm_inv_0_B_val[OF assms]]
       l_types_initD(2)[OF l_types_init_maintained[OF s_perm_inv_elims(2,4,10-12)[OF assms(1)]]
         assms(2)]
       `?xs = ?ys @ ?zs`
  show ?thesis
    by auto
qed

lemma abs_induce_s_base_distinct:
  assumes "abs_induce_s_base \<alpha> T B SA = (B', SA', n)"
  and     "s_perm_inv \<alpha> T B' SA SA' n"
shows "distinct SA'"
proof(intro distinct_conv_nth[THEN iffD2] allI impI)
  fix i j
  assume "i < length SA'" "j < length SA'" "i \<noteq> j"
  hence "i < length T" "j < length T"
    using assms(2) s_perm_inv_elims(11) by fastforce+

  from abs_induce_s_base_index[of \<alpha> T B SA] assms(1)
  have "n = 0"
    by simp

  from index_in_bucket_interval_gen[OF `i < length T` s_perm_inv_elims(8)[OF assms(2)]]
  obtain b0 where
    "b0 \<le> \<alpha> (Max (set T))"
    "bucket_start \<alpha> T b0 \<le> i"
    "i < bucket_end \<alpha> T b0"
    by blast

  have "bucket_end \<alpha> T b0 \<le> length SA'"
    using assms(2) bucket_end_le_length s_perm_inv_elims(11) by fastforce

  let ?xs = "list_slice SA' (bucket_start \<alpha> T b0) (bucket_end \<alpha> T b0)"

  from index_in_bucket_interval_gen[OF `j < length T` s_perm_inv_elims(8)[OF assms(2)]]
  obtain b1 where
    "b1 \<le> \<alpha> (Max (set T))"
    "bucket_start \<alpha> T b1 \<le> j"
    "j < bucket_end \<alpha> T b1"
    by blast

  have "bucket_end \<alpha> T b1 \<le> length SA'"
    using assms(2) bucket_end_le_length s_perm_inv_elims(11) by fastforce

  have "b0 \<noteq> b1 \<Longrightarrow> SA' ! i \<noteq> SA' ! j"
  proof -
    assume "b0 \<noteq> b1"
    hence "bucket \<alpha> T b0 \<inter> bucket \<alpha> T b1 = {}"
      by (metis (mono_tags, lifting) Int_emptyI bucket_def mem_Collect_eq)
    moreover
    from s_perm_inv_0_list_slice_bucket[OF assms(2)[simplified `n = 0`] `b0 \<le> _`]
         list_slice_nth_mem[OF `bucket_start \<alpha> T b0 \<le> i` `i < bucket_end \<alpha> T b0`
           `bucket_end \<alpha> T b0 \<le> _`]
    have "SA' ! i \<in> bucket \<alpha> T b0"
      by blast
    moreover
    from s_perm_inv_0_list_slice_bucket[OF assms(2)[simplified `n = 0`] `b1 \<le> _`]
         list_slice_nth_mem[OF `bucket_start \<alpha> T b1 \<le> j` `j < bucket_end \<alpha> T b1`
           `bucket_end \<alpha> T b1 \<le> _`]
    have "SA' ! j \<in> bucket \<alpha> T b1"
      by blast
    ultimately show ?thesis
      by auto
  qed
  moreover
  have "b0 = b1 \<Longrightarrow> SA' ! i \<noteq> SA' ! j"
  proof -
    assume "b0 = b1"
    with `bucket_start \<alpha> T b1 \<le> j` `j < bucket_end \<alpha> T b1`
    have "bucket_start \<alpha> T b0 \<le> j" "j < bucket_end \<alpha> T b0"
      by simp_all
    with list_slice_nth_eq_iff_index_eq[
          OF s_perm_inv_0_distinct_list_slice[OF assms(2)[simplified`n = 0`] `b0 \<le> _`]
            `bucket_end _ _ b0 \<le> _` `bucket_start \<alpha> T b0 \<le> i` `i < bucket_end \<alpha> T b0`, of j]
         `i \<noteq> j`
    show ?thesis
      by blast
  qed
  ultimately show "SA' ! i \<noteq> SA' ! j"
    by blast
qed

lemma abs_induce_s_base_subset_upt:
  assumes "abs_induce_s_base \<alpha> T B SA = (B', SA', n)"
  and     "s_perm_inv \<alpha> T B' SA SA' n"
shows "set SA' \<subseteq> {0..<length T}"
proof
  fix x
  assume "x \<in> set SA'"
  from in_set_conv_nth[THEN iffD1, OF `x \<in> set SA'`]
  obtain i where
    "i < length SA'"
    "SA' ! i = x"
    by blast
  hence "i < length T"
    using assms(2) s_perm_inv_elims(11) by fastforce
  with index_in_bucket_interval_gen[OF _ s_perm_inv_elims(8)[OF assms(2)]]
  obtain b where
    "b \<le> \<alpha> (Max (set T))"
    "bucket_start \<alpha> T b \<le> i"
    "i < bucket_end \<alpha> T b"
    by blast

  from abs_induce_s_base_index[of \<alpha> T B SA] assms(1)
  have "n = 0"
    by simp

  have "bucket_end \<alpha> T b \<le> length SA'"
    using assms(2) bucket_end_le_length s_perm_inv_elims(11) by fastforce
  with s_perm_inv_0_list_slice_bucket[OF assms(2)[simplified `n = 0`] `b \<le> _`]
       `SA' ! i = x` `bucket_start \<alpha> T b \<le> i` `i < bucket_end \<alpha> T b`
  have "x \<in> bucket \<alpha> T b"
    using list_slice_nth_mem by blast
  hence "x < length T"
    using bucket_def by blast
  then show "x \<in> {0..< length T}"
    by simp
qed

corollary abs_induce_s_base_eq_upt:
  assumes "abs_induce_s_base \<alpha> T B SA = (B', SA', n)"
  and     "s_perm_inv \<alpha> T B' SA SA' n"
shows "set SA' = {0..<length T}"
  by (rule card_subset_eq[OF finite_atLeastLessThan abs_induce_s_base_subset_upt[OF assms]];
      clarsimp simp: distinct_card[OF abs_induce_s_base_distinct[OF assms]]
                     s_perm_inv_elims(11)[OF assms(2)])

theorem abs_induce_s_base_perm:
  assumes "abs_induce_s_base \<alpha> T B SA = (B', SA', n)"
  and     "s_perm_inv \<alpha> T B' SA SA' n"
shows "SA' <~~> [0..< length T]"
  by (rule perm_distinct_set_of_upt_iff[THEN iffD2];
      clarsimp simp: abs_induce_s_base_distinct[OF assms] abs_induce_s_base_eq_upt[OF assms])

subsubsection "Sorted"

lemma s_sorted_established:
  assumes "s_bucket_init \<alpha> T B"
  and     "strict_mono \<alpha>"
  and     "valid_list T"
  and     "\<alpha> bot = 0"
  and     "b \<le> \<alpha> (Max (set T))"
shows "sorted_wrt R (list_slice SA (B ! b) (bucket_end \<alpha> T b))"
      (is "sorted_wrt R ?xs")
proof -
  have "b = 0 \<or> 0 < b"
    by blast
  moreover
  have "0 < b \<Longrightarrow> ?thesis"
  proof -
    assume "0 < b"
    hence "B ! b = bucket_end \<alpha> T b"
      by (simp add: \<open>b \<le> \<alpha> (Max (set T))\<close> assms(1) s_bucket_initD)
    then show ?thesis 
      by simp
  qed
  moreover
  have "b = 0 \<Longrightarrow> ?thesis"
  proof -
    assume "b = 0"
    hence "bucket_end \<alpha> T b = Suc 0"
      by (simp add: assms(2-4) valid_list_bucket_end_0)
    moreover
    from `b = 0`
    have "B ! b = 0"
      using assms(1) s_bucket_initD(2) by auto
    ultimately show ?thesis
      by (simp add: sorted_wrt01)
  qed
  ultimately show ?thesis
    by blast
qed

lemma s_sorted_inv_established:
  assumes "s_bucket_init \<alpha> T B"
  and     "strict_mono \<alpha>"
  and     "valid_list T"
  and     "\<alpha> bot = 0"
shows "s_sorted_inv \<alpha> T B SA"
  unfolding s_sorted_inv_def
  using assms ordlistns.sorted_map s_sorted_established by blast

lemma s_prefix_sorted_inv_established:
  assumes "s_bucket_init \<alpha> T B"
  and     "strict_mono \<alpha>"
  and     "valid_list T"
  and     "\<alpha> bot = 0"
shows "s_prefix_sorted_inv \<alpha> T B SA"
  unfolding s_prefix_sorted_inv_def
  using assms ordlistns.sorted_map s_sorted_established by blast

lemma s_sorted_maintained_unchanged_step:
  assumes "s_perm_inv \<alpha> T B SA0 SA i"
  and     "i = Suc n"
  and     "Suc n < length SA"
  and     "SA ! Suc n = Suc j"
  and     "suffix_type T j = S_type"
  and     "b = \<alpha> (T ! j)"
  and     "k = B ! b - Suc 0"
  and     "b' \<le> \<alpha> (Max (set T))"
  and     "sorted_wrt R (list_slice SA (B ! b') (bucket_end \<alpha> T b'))"
  and     "b \<noteq> b'"
shows "sorted_wrt R (list_slice (SA[k := j]) ((B[b := k]) ! b') (bucket_end \<alpha> T b'))"
proof -
  let ?xs = "list_slice (SA[k := j]) (B[b := k] ! b') (bucket_end \<alpha> T b')"

  have "bucket_end \<alpha> T b \<le> length T"
    using bucket_end_le_length by blast
  moreover
  have "B ! b \<le> bucket_end \<alpha> T b"
    using assms(1,5,6) s_bucket_ptr_upper_bound s_perm_inv_elims(2,8) strict_mono_less_eq
          suffix_type_s_bound by fastforce
  ultimately have "k < length T"
    using assms(1,7) s_perm_inv_elims(15) by fastforce
  hence "k < length SA"
    by (metis assms(1) s_perm_inv_def)

  from s_bucket_ptr_strict_lower_bound[OF s_perm_inv_elims(1-6,8,10-14)[OF assms(1)] assms(2-6)]
  have "s_bucket_start \<alpha> T b < B ! b" .
  hence "k < B ! b"
    using assms(7) diff_less gr_implies_not_zero by blast

  have "s_bucket_start \<alpha> T b \<le> k"
    using assms s_bucket_ptr_strict_lower_bound s_perm_inv_def by fastforce
  hence "bucket_start \<alpha> T b \<le> k"
    using bucket_start_le_s_bucket_start le_trans by blast

  from `b \<noteq> b'`
  have "B[b := k] ! b' = B ! b'"
    by simp

  have "k < B ! b' \<or> bucket_end \<alpha> T b' \<le> k"
  proof -
    from `b \<noteq> b'`
    have "b < b' \<or> b' < b"
      using nat_neq_iff by blast
    moreover
    have "b < b' \<Longrightarrow> k < B ! b'"
    proof -
      assume "b < b'"
      hence "bucket_end \<alpha> T b \<le> bucket_start \<alpha> T b'"
        by (simp add: less_bucket_end_le_start)
      hence "k < bucket_start \<alpha> T b'"
        using \<open>B ! b \<le> bucket_end \<alpha> T b\<close> \<open>k < B ! b\<close> by linarith
      with s_bucket_ptr_lower_bound[OF s_perm_inv_elims(2)[OF assms(1)] `b' \<le> _`]
      show ?thesis
        by (meson bucket_start_le_s_bucket_start order.strict_trans2)
    qed
    moreover
    have "b' < b \<Longrightarrow> bucket_end \<alpha> T b' \<le> k"
    proof -
      assume "b' < b"
      hence "bucket_end \<alpha> T b' \<le> bucket_start \<alpha> T b"
        by (simp add: less_bucket_end_le_start)
      then show ?thesis
        using \<open>bucket_start \<alpha> T b \<le> k\<close> by linarith
    qed
    ultimately show ?thesis
      by blast
  qed
  with list_slice_update_unchanged_1
       list_slice_update_unchanged_2
  have "?xs = list_slice SA (B ! b') (bucket_end \<alpha> T b')"
    using \<open>B[b := k] ! b' = B ! b'\<close> by auto
  then show ?thesis
    using assms(9) by auto
qed

lemma s_sorted_inv_maintained_step:
  assumes "s_perm_inv \<alpha> T B SA0 SA i"
  and     "s_sorted_pre \<alpha> T SA0"
  and     "s_sorted_inv \<alpha> T B SA"
  and     "i = Suc n"
  and     "Suc n < length SA"
  and     "SA ! Suc n = Suc j"
  and     "suffix_type T j = S_type"
  and     "b = \<alpha> (T ! j)"
  and     "k = B ! b - Suc 0"
shows "s_sorted_inv \<alpha> T (B[b := k]) (SA[k := j])"
  unfolding s_sorted_inv_def
proof (safe)
  fix b'
  assume "b' \<le> \<alpha> (Max (set T))"
  let ?xs = "list_slice (SA[k := j]) (B[b := k] ! b') (bucket_end \<alpha> T b')"

  have "bucket_end \<alpha> T b \<le> length T"
    using bucket_end_le_length by blast

  moreover
  have "B ! b \<le> bucket_end \<alpha> T b"
    using assms(1,7,8) s_bucket_ptr_upper_bound suffix_type_s_bound
          s_perm_inv_elims(2,8) strict_mono_less_eq
    by fastforce

  ultimately have "k < length T"
    using assms(1,9) s_perm_inv_elims(15) by fastforce
  hence "k < length SA"
    by (metis assms(1) s_perm_inv_def)

  from s_bucket_ptr_strict_lower_bound
          [OF s_perm_inv_elims(1-6,8,10-14)
          [OF assms(1)] assms(4-8)]
  have "s_bucket_start \<alpha> T b < B ! b" .
  hence "k < B ! b"
    using assms(9) diff_less gr_implies_not_zero by blast

  have "s_bucket_start \<alpha> T b \<le> k"
    using assms s_bucket_ptr_strict_lower_bound s_perm_inv_def 
    by fastforce
  hence "bucket_start \<alpha> T b \<le> k"
    using bucket_start_le_s_bucket_start le_trans 
    by blast
  hence "b \<le> \<alpha> (Max (set T))"
    by (metis \<open>k < length SA\<close> assms(1) bucket_end_Max dual_order.trans
              less_bucket_end_le_start s_perm_inv_elims(8,11) leD leI)

  have "b = b' \<or> b \<noteq> b'"
    by blast
  moreover
  have "b = b' \<Longrightarrow> ordlistns.sorted (map (suffix T) ?xs)"
  proof -
    assume "b = b'"
    hence "B[b := k] ! b' = k"
      by (meson \<open>b' \<le> \<alpha> (Max (set T))\<close> assms(1) le_less_trans nth_list_update_eq
            s_perm_inv_elims(9))

    have "SA[k := j] ! k = j"
      by (simp add: \<open>k < length SA\<close>)

    from list_slice_update_unchanged_1
         `k < B ! b` 
         `SA[k := j] ! k = j` 
         `B[b := k] ! b' = k` 
         `B ! b \<le> bucket_end \<alpha> T b`
         `b = b'` `k < length SA`
    have "?xs = j # list_slice SA (B ! b) (bucket_end \<alpha> T b)"
      by (metis Suc_pred  assms(9) length_list_update not_le  
                less_nat_zero_code list_slice_Suc less_le_trans)
    moreover
    have "ordlistns.sorted 
            (map (suffix T) (j # list_slice SA (B ! b) (bucket_end \<alpha> T b)))"
    proof -
      let ?ys = "list_slice SA (B ! b) (bucket_end \<alpha> T b)"

      have A: "map (suffix T) (j # ?ys) = (suffix T j) # map (suffix T) ?ys"
        by simp

      from s_sorted_invD[OF assms(3) `b \<le> _`]
      have B: "ordlistns.sorted (map (suffix T) ?ys)" .

      have "?ys = [] \<or> ?ys \<noteq> []"
        by blast
      hence "map (suffix T) ?ys = [] \<or> map (suffix T) ?ys \<noteq> []"
        by simp
      moreover
      have "map (suffix T) ?ys = [] \<Longrightarrow> ?thesis"
        using ordlistns.sorted_cons_nil by fastforce
      moreover
      have "map (suffix T) ?ys \<noteq> [] \<Longrightarrow>
             ordlistns.sorted ((suffix T j) # map (suffix T) ?ys)"
      proof (rule ordlistns.sorted_consI[OF _ B])
        assume "map (suffix T) (list_slice SA (B ! b) (bucket_end \<alpha> T b)) \<noteq> []"
        then 
        show "map (suffix T) (list_slice SA (B ! b) (bucket_end \<alpha> T b)) \<noteq> []"
          by simp
      next
        assume "map (suffix T) ?ys \<noteq> []"
        hence "map (suffix T) ?ys ! 0 = suffix T (?ys ! 0)"
          by (metis length_greater_0_conv list.simps(8) nth_map)
        moreover
        have "list_less_eq_ns (suffix T j) (suffix T (?ys ! 0))"
        proof -
          have "?ys ! 0 \<in> s_bucket \<alpha> T b"
            by (metis assms(1) length_greater_0_conv s_perm_inv_elims(3)
                      length_map nth_mem s_locations_inv_in_list_slice
                      \<open>b = b'\<close> 
                      \<open>b' \<le> \<alpha> (Max (set T))\<close>
                      \<open>map (suffix T) ?ys \<noteq> []\<close> )
          hence "\<alpha> (T ! (?ys ! 0)) = b" "suffix_type T (?ys ! 0) = S_type"
            by (simp add: s_bucket_def bucket_def)+
          hence "T ! j = T ! (?ys ! 0)"
            using assms(1,8) s_perm_inv_elims(8) strict_mono_eq by fastforce

          have "?ys ! 0 = SA ! (B ! b)"
            using \<open>map (suffix T) ?ys \<noteq> []\<close> nth_list_slice by fastforce

          have "b \<noteq> 0"
            by (metis \<open>s_bucket_start \<alpha> T b < B ! b\<close> assms(1)
                      gr_implies_not_zero s_bucket_ptr_0 s_perm_inv_elims(2))

          have "in_s_current_bucket \<alpha> T B b (B ! b)"
            using \<open>b = b'\<close> \<open>b' \<le> \<alpha> (Max (set T))\<close> \<open>map (suffix T) ?ys \<noteq> []\<close>  
            by (metis \<open>B ! b \<le> bucket_end \<alpha> T b\<close> in_s_current_bucket_def
                      le_eq_less_or_eq list.map_disc_iff list_slice_n_n)
            with s_pred_invD
                  [OF s_perm_inv_elims(6)[OF assms(1)] _ `b \<noteq> 0`, 
                   of "B ! b"]
          obtain i' where i'_assms:
            "i' < length SA"
            "SA ! i' = Suc (SA ! (B ! b))"
            "B ! b < i'"
            "i < i'"
            by blast

          let ?b0 = "\<alpha> (T ! (Suc j))"
          and ?b1 = "\<alpha> (T ! (Suc (SA ! (B ! b))))"

          have i_less: "i < length SA"
            by (simp add: assms(4-5))

          have "?b0 \<le> \<alpha> (Max (set T))"
            by (metis Max_greD Suc_leI assms(1,4-6) strict_mono_leD
                      s_perm_inv_elims(5,8) s_seen_invD(1) lessI)

          have "?b1 \<le> \<alpha> (Max (set T))"
            by (metis Max_greD i'_assms(1,2,4) assms(1)
                  less_imp_le_nat s_perm_inv_elims(5,8) 
                  s_seen_invD(1) strict_mono_leD)

          have S0: "suffix T j = T ! j # suffix T (Suc j)"
            using assms(7) suffix_cons_Suc suffix_type_s_bound 
            by blast

          have S1: "suffix T (?ys ! 0) = 
                      T ! (?ys ! 0) # suffix T (Suc (SA ! (B ! b)))"
            using \<open>?ys ! 0 = SA ! (B ! b)\<close> 
                  \<open>suffix_type T (?ys ! 0) = S_type\<close> suffix_cons_Suc
                  suffix_type_s_bound by auto

          have "?b0 \<le> ?b1"
          proof(rule ccontr)
            assume "\<not>?b0 \<le> ?b1"
            hence "?b1 < ?b0"
              by simp
            hence "bucket_end \<alpha> T ?b1 \<le> bucket_start \<alpha> T ?b0"
              by (simp add: less_bucket_end_le_start)
            with s_index_upper_bound[OF s_perm_inv_elims(2,5)[OF assms(1)] i'_assms(1)]
                 s_index_lower_bound[OF s_perm_inv_elims(2,5)[OF assms(1)] i_less,
                                     simplified]
                 order.strict_implies_order[OF i'_assms(4)]
            show False
              using i'_assms(2) assms(4,6) by auto
          qed
          hence "?b0 = ?b1 \<or> ?b0 < ?b1"
            by linarith
          moreover
          have "?b0 < ?b1 \<Longrightarrow> 
                list_less_eq_ns 
                  (suffix T (Suc j)) 
                  (suffix T (Suc (SA ! (B ! b))))"
          proof -
            assume "?b0 < ?b1"
            hence "T ! (Suc j) < T ! (Suc (SA ! (B ! b)))"
              using assms(1) s_perm_inv_elims(8) strict_mono_less by blast
            then show ?thesis
              by (metis i'_assms(1,2,4) assms(1,4-6) s_perm_inv_def
                        leD  s_seen_invD(1) list_less_eq_ns_linear
                        suffix_cons_Suc list_less_eq_ns_cons)
          qed
          moreover
          have "?b0 = ?b1 \<Longrightarrow> 
                  list_less_eq_ns 
                    (suffix T (Suc j)) 
                    (suffix T (Suc (SA ! (B ! b))))"
          proof -
            assume "?b0 = ?b1"
            with s_index_upper_bound
                   [OF s_perm_inv_elims(2,5)[OF assms(1)]
                 `i' < _`] i'_assms(4)
            have "i' < bucket_end \<alpha> T ?b0"
              by (simp add: \<open>SA ! i' = Suc (SA ! (B ! b))\<close>)

            have "suffix_type T (SA ! i) = S_type \<or> 
                  suffix_type T (SA ! i) = L_type"
              using SL_types.exhaust by blast
            moreover
            have "suffix_type T (SA ! i) = S_type \<Longrightarrow> ?thesis"
            proof -
              assume "suffix_type T (SA ! i) = S_type"
              with s_seen_invD(3)
                    [OF s_perm_inv_elims(5)[OF assms(1)] i_less, 
                     simplified]
              have "in_s_current_bucket \<alpha> T B ?b0 i"
                by (simp add: assms(4) assms(6))
              hence "B ! ?b0 \<le> i"
                using in_s_current_bucket_def by blast
              hence "\<exists>m. B ! ?b0 + m = i"
                using less_eqE by blast
              then obtain m0 where m0_assm:
                "B ! ?b0 + m0 = i"
                by blast

              from `B ! ?b0 \<le> i` i'_assms(4) 
              have "\<exists>m. B ! ?b0 + m = i'"
                by presburger
              then obtain m1 where m1_assm:
                "B ! ?b0 + m1 = i'"
                by blast
              hence "B ! ?b0 + m0 \<le> B ! ?b0 + m1"
                by (simp add: m0_assm i'_assms(4) dual_order.order_iff_strict)
              hence "m0 \<le> m1"
                using add_le_imp_le_left by blast

              have "(list_slice SA (B ! ?b0) (bucket_end \<alpha> T ?b0)) ! m0 = 
                    Suc j"
                using m0_assm i_less
                      \<open>in_s_current_bucket \<alpha> T B ?b0 i\<close> assms(4,6) 
                      in_s_current_bucketD(3) 
                by (metis \<open>B ! \<alpha> (T ! Suc j) \<le> i\<close> diff_add_inverse list_slice_nth)
              moreover
              have "(list_slice  SA (B ! ?b0) (bucket_end \<alpha> T ?b0)) ! m1 = 
                    Suc (SA ! (B ! b))"
                using m1_assm i'_assms
                       \<open>i' < bucket_end \<alpha> T ?b0\<close>
                by (metis diff_add_inverse le_add1 list_slice_nth)
              moreover
              have "length (list_slice SA (B ! ?b0) (bucket_end \<alpha> T ?b0)) = 
                    (bucket_end \<alpha> T ?b0) - B ! ?b0"
                by (metis assms(1) bucket_end_le_length length_list_slice min_def s_perm_inv_def)
              with `B ! ?b0 + m1 = i'` 
                    `i' < bucket_end \<alpha> T ?b0`
              have "m1 < length (list_slice SA (B ! ?b0) (bucket_end \<alpha> T ?b0))"
                by linarith
              ultimately
              show ?thesis
                using ordlistns.sorted_nth_mono
                        [OF s_sorted_invD[OF assms(3) `?b0 \<le> \<alpha> (Max _)`]
                            `m0 \<le> m1`]
                      \<open>m0 \<le> m1\<close> 
                by auto
            qed
            moreover
            have "suffix_type T (SA ! i) = L_type \<Longrightarrow> ?thesis"
            proof -
              assume "suffix_type T (SA ! i) = L_type"
              with s_seen_invD(2)
                    [OF s_perm_inv_elims(5)[OF assms(1)] i_less, 
                     simplified]
              have "in_l_bucket \<alpha> T ?b0 i"
                by (simp add: assms(4) assms(6))
              hence "bucket_start \<alpha> T ?b0 \<le> i"
                by (simp add: in_l_bucket_def)
              hence "\<exists>m. bucket_start \<alpha> T ?b0 + m = i"
                using less_eqE by blast
              then obtain m0 where start_plus_m0_eq:
                "bucket_start \<alpha> T ?b0 + m0 = i"
                by blast

              have "suffix_type T (SA ! i') = L_type \<or> 
                    suffix_type T (SA ! i') = S_type"
                using SL_types.exhaust by blast
              moreover
              have "suffix_type T (SA ! i') = S_type \<Longrightarrow> ?thesis"
              proof -
                assume "suffix_type T (SA ! i') = S_type"

                have "SA ! i < length T"
                  by (meson \<open>i < length SA\<close> assms(1) order_refl s_perm_inv_elims(5) s_seen_invD(1))

                have "SA ! i' < length T"
                  by (simp add: \<open>suffix_type T (SA ! i') = S_type\<close> suffix_type_s_bound)

                from `?b0 = ?b1`
                have "T ! (Suc j) = T ! Suc (SA ! (B ! b))"
                  using assms(1) s_perm_inv_def strict_mono_eq by blast
                hence "hd (suffix T (SA ! i')) = hd (suffix T (SA ! i))"
                  by (metis assms(4,6) list.sel(1) suffix_cons_Suc
                        \<open>SA ! i < length T\<close> \<open>SA ! i' < length T\<close> 
                        \<open>SA ! i' = Suc (SA ! (B ! b))\<close>)
                with l_less_than_s_type
                      [OF s_perm_inv_elims(13)[OF assms(1)] 
                          `SA ! i' < length T`
                          `SA ! i < length T` _ 
                          `suffix_type T (SA ! i') = _`
                          `suffix_type T (SA ! i) = _`]
                have "list_less_ns (suffix T (SA ! i)) (suffix T (SA ! i'))".
                then show ?thesis
                  by (simp add: \<open>SA ! i' = Suc (SA ! (B ! b))\<close> assms(4,6))
              qed
              moreover
              have "suffix_type T (SA ! i') = L_type \<Longrightarrow> ?thesis"
              proof -
                assume "suffix_type T (SA ! i') = L_type"
                with s_seen_invD(2)
                      [OF s_perm_inv_elims(5)[OF assms(1)] 
                          `i' < length SA`,
                       simplified 
                         `?b0 = ?b1`[symmetric]
                         `SA ! i' = Suc (SA ! (B ! b))`]
                         `SA ! i' = Suc (SA ! (B ! b))`
                have "in_l_bucket \<alpha> T ?b0 i'"
                  by (simp add: \<open>i < i'\<close> dual_order.order_iff_strict)
                hence i'_le_end: "i' < l_bucket_end \<alpha> T ?b0"
                  by (simp add: in_l_bucket_def)
                hence "\<exists>m. bucket_start \<alpha> T ?b0 + m = i'"
                  by (metis \<open>in_l_bucket \<alpha> T ?b0 i'\<close> in_l_bucket_def less_eqE)
                then obtain m1 where start_plus_m1_eq:
                  "bucket_start \<alpha> T ?b0 + m1 = i'"
                  by blast

                let ?zs = 
                    "list_slice SA 
                      (bucket_start \<alpha> T ?b0) 
                      (l_bucket_end \<alpha> T ?b0)"

                have "?zs ! m0 = Suc j" 
                  by (metis \<open>bucket_start \<alpha> T (\<alpha> (T ! Suc j)) \<le> i\<close> 
                            assms(4,6)  i'_assms(4) i'_le_end 
                            diff_add_inverse dual_order.order_iff_strict
                            i_less list_slice_nth order.strict_trans1 
                            start_plus_m0_eq)
                moreover
                have "?zs ! m1 = Suc (SA ! (B ! b))"
                  using list_slice_nth dual_order.order_iff_strict i'_assms(4)
                        le_trans [OF \<open>bucket_start \<alpha> T (\<alpha> (T ! Suc j)) \<le> i\<close>]
                        \<open>SA ! i' = Suc (SA ! (B ! b))\<close> 
                        \<open>bucket_start \<alpha> T ?b0 + m1 = i'\<close>
                        \<open>i' < l_bucket_end \<alpha> T ?b0\<close> 
                        \<open>i' < length SA\<close> 
                  by (metis diff_add_inverse)             
                moreover
                have "m0 \<le> m1"
                  using start_plus_m0_eq start_plus_m1_eq i'_assms(4)
                  by linarith
                moreover
                have "length ?zs = l_bucket_end \<alpha> T ?b0 - bucket_start \<alpha> T ?b0"
                  by (metis \<open>?b0 \<le> \<alpha> (Max (set T))\<close> assms(1)
                            add_diff_cancel_left' distinct_card
                            l_bucket_end_def l_bucket_size_def 
                            l_types_init_def s_perm_inv_def
                            l_types_init_maintained)
                hence "m1 < length ?zs"
                  using start_plus_m1_eq i'_le_end by linarith
                moreover
                from s_sorted_pre_maintained
                      [OF s_perm_inv_elims(2,4,10,11)[OF assms(1)] 
                          assms(2)]
                have "s_sorted_pre \<alpha> T SA" .
                ultimately show ?thesis
                  using ordlistns.sorted_nth_mono
                        [OF s_sorted_preD
                            [of \<alpha> T SA,
                             OF _ `?b0 \<le> \<alpha> (Max _)`], 
                        of m0 m1]
                  by (simp add: \<open>m1 < length ?zs\<close> le_less_trans
                                \<open>s_sorted_pre \<alpha> T SA\<close>)
              qed
              ultimately show ?thesis
                by blast
            qed
            ultimately show ?thesis
              by blast
          qed
          ultimately 
          have "list_less_eq_ns 
                  (suffix T (Suc j)) 
                  (suffix T (Suc (SA ! (B ! b))))"
            by blast
          with S0 S1 `T ! j = T ! (?ys ! 0)`
          show ?thesis
            by (simp add: list_less_eq_ns_cons)
        qed
        ultimately 
        show "list_less_eq_ns (suffix T j) (map (suffix T) ?ys ! 0)"
          by simp
      qed
      ultimately show ?thesis
        using A by fastforce
    qed
    ultimately show ?thesis
      by simp
  qed
  moreover
  have "b \<noteq> b' \<Longrightarrow> ordlistns.sorted (map (suffix T) ?xs)"
  proof -
    assume "b \<noteq> b'"
    with s_sorted_maintained_unchanged_step[OF assms(1,4-) `b' \<le> _`]
         s_sorted_invD[OF assms(3) `b' \<le> _`]
    show ?thesis
      using ordlistns.sorted_map by blast
  qed
  ultimately show "ordlistns.sorted (map (suffix T) ?xs)"
    by blast
qed

lemma s_prefix_sorted_inv_maintained_step:
  assumes "s_perm_inv \<alpha> T B SA0 SA i"
  and     "s_prefix_sorted_pre \<alpha> T SA0"
  and     "s_prefix_sorted_inv \<alpha> T B SA"
  and     "i = Suc n"
  and     "Suc n < length SA"
  and     "SA ! Suc n = Suc j"
  and     "suffix_type T j = S_type"
  and     "b = \<alpha> (T ! j)"
  and     "k = B ! b - Suc 0"
shows "s_prefix_sorted_inv \<alpha> T (B[b := k]) (SA[k := j])"
  unfolding s_prefix_sorted_inv_def
proof (safe)
  fix b'
  assume "b' \<le> \<alpha> (Max (set T))"
  let ?xs = "list_slice (SA[k := j]) (B[b := k] ! b') (bucket_end \<alpha> T b')"

  have "bucket_end \<alpha> T b \<le> length T"
    using bucket_end_le_length by blast
  moreover
  have "B ! b \<le> bucket_end \<alpha> T b"
    using assms(1,7,8) s_bucket_ptr_upper_bound s_perm_inv_elims(2,8) strict_mono_less_eq
          suffix_type_s_bound by fastforce

  ultimately have "k < length T"
    using assms(1,9) s_perm_inv_elims(15) by fastforce
  hence "k < length SA"
    by (metis assms(1) s_perm_inv_def)

  from s_bucket_ptr_strict_lower_bound
        [OF s_perm_inv_elims(1-6,8,10-14)[OF assms(1)] assms(4-8)]
  have "s_bucket_start \<alpha> T b < B ! b" .
  hence "k < B ! b"
    using assms(9) diff_less gr_implies_not_zero by blast

  have "s_bucket_start \<alpha> T b \<le> k"
    using assms s_bucket_ptr_strict_lower_bound s_perm_inv_def by fastforce
  hence "bucket_start \<alpha> T b \<le> k"
    using bucket_start_le_s_bucket_start le_trans by blast
  hence "b \<le> \<alpha> (Max (set T))"
    by (metis \<open>k < length SA\<close> assms(1) bucket_end_Max dual_order.trans 
              leD leI  s_perm_inv_elims(8,11) less_bucket_end_le_start)

  have "b = b' \<or> b \<noteq> b'"
    by blast
  moreover
  have "b = b' \<Longrightarrow> ordlistns.sorted (map (lms_slice T) ?xs)"
  proof -
    assume "b = b'"
    hence "B[b := k] ! b' = k"
      by (meson \<open>b' \<le> \<alpha> (Max (set T))\<close> assms(1) le_less_trans 
                nth_list_update_eq s_perm_inv_elims(9))

    have "SA[k := j] ! k = j"
      by (simp add: \<open>k < length SA\<close>)

    from list_slice_update_unchanged_1[OF `k < B ! b`]
         `k < B ! b` `SA[k := j] ! k = j` `B[b := k] ! b' = k` 
         `B ! b \<le> bucket_end \<alpha> T b`
         `b = b'` `k < length SA`
    have "?xs = j # list_slice SA (B ! b) (bucket_end \<alpha> T b)"
      by (metis Suc_pred assms(9) length_list_update not_le
                less_nat_zero_code list_slice_Suc less_le_trans)
    moreover
    have "ordlistns.sorted 
              (map (lms_slice T)
                   (j # list_slice SA (B ! b) 
                   (bucket_end \<alpha> T b)))"
    proof -
      let ?ys = "list_slice SA (B ! b) (bucket_end \<alpha> T b)"

      have A: "map (lms_slice T) (j # ?ys) = (lms_slice T j) # map (lms_slice T) ?ys"
        by simp

      from s_prefix_sorted_invD[OF assms(3) `b \<le> _`]
      have B: "ordlistns.sorted (map (lms_slice T) ?ys)" .

      have "?ys = [] \<or> ?ys \<noteq> []"
        by blast
      hence "map (lms_slice T) ?ys = [] \<or> map (lms_slice T) ?ys \<noteq> []"
        by simp
      moreover
      have "map (lms_slice T) ?ys = [] \<Longrightarrow> ?thesis"
        using ordlistns.sorted_cons_nil by fastforce
      moreover
      have "map (lms_slice T) ?ys \<noteq> [] \<Longrightarrow>
            ordlistns.sorted ((lms_slice T j) # map (lms_slice T) ?ys)"
      proof (rule ordlistns.sorted_consI[OF _ B])
        assume "map (lms_slice T) ?ys \<noteq> []"
        hence "map (lms_slice T) ?ys ! 0 = lms_slice T (?ys ! 0)"
          by (metis length_greater_0_conv list.simps(8) nth_map)
        moreover
        have "list_less_eq_ns (lms_slice T j) (lms_slice T (?ys ! 0))"
        proof -
          have "?ys ! 0 \<in> s_bucket \<alpha> T b"
            by (metis \<open>b = b'\<close> \<open>b' \<le> \<alpha> (Max (set T))\<close> \<open>map (lms_slice T) ?ys \<noteq> []\<close> assms(1)
                      length_greater_0_conv length_map nth_mem s_locations_inv_in_list_slice
                      s_perm_inv_elims(3))
          hence "\<alpha> (T ! (?ys ! 0)) = b" "suffix_type T (?ys ! 0) = S_type"
            by (simp add: s_bucket_def bucket_def)+
          hence "T ! j = T ! (?ys ! 0)"
            using assms(1,8) s_perm_inv_elims(8) strict_mono_eq by fastforce

          have "?ys ! 0 = SA ! (B ! b)"
            using \<open>map (lms_slice T) ?ys \<noteq> []\<close> nth_list_slice by fastforce

          have "b \<noteq> 0"
            by (metis \<open>s_bucket_start \<alpha> T b < B ! b\<close> assms(1)
                  gr_implies_not_zero s_bucket_ptr_0 s_perm_inv_elims(2))

          have "in_s_current_bucket \<alpha> T B b (B ! b)"
            using \<open>b = b'\<close> \<open>b' \<le> \<alpha> (Max (set T))\<close> 
                  \<open>map (lms_slice T) ?ys \<noteq> []\<close>
                  in_s_current_bucket_def 
            by (metis \<open>B ! b \<le> bucket_end \<alpha> T b\<close> 
                      dual_order.order_iff_strict list.map_disc_iff 
                      list_slice_n_n)
            with s_pred_invD
                    [OF s_perm_inv_elims(6)[OF assms(1)] _ `b \<noteq> 0`, 
                     of "B ! b"]
          obtain i' where
            "i' < length SA"
            "SA ! i' = Suc (SA ! (B ! b))"
            "B ! b < i'"
            "i < i'"
            by blast

          let ?b0 = "\<alpha> (T ! (Suc j))"
          and ?b1 = "\<alpha> (T ! (Suc (SA ! (B ! b))))"

          have "i < length SA"
            by (simp add: assms(4-5))

          have "?b0 \<le> \<alpha> (Max (set T))"
            by (metis Max_greD Suc_leI assms(1,4-6) lessI s_perm_inv_elims(5,8) s_seen_invD(1)
                  strict_mono_leD)

          have "?b1 \<le> \<alpha> (Max (set T))"
            by (metis Max_greD \<open>SA ! i' = Suc (SA ! (B ! b))\<close> \<open>i < i'\<close> \<open>i' < length SA\<close> assms(1)
                  less_imp_le_nat s_perm_inv_elims(5) s_perm_inv_elims(8) s_seen_invD(1)
                  strict_mono_leD)

          have S0: "lms_slice T j = T ! j # lms_slice T (Suc j)"
            using assms(7) lms_slice_cons suffix_type_s_bound by blast

          have S1:
            "lms_slice T (?ys ! 0) = T ! (?ys ! 0) # lms_slice T (Suc (SA ! (B ! b)))"
            using \<open>?ys ! 0 = SA ! (B ! b)\<close> \<open>suffix_type T (?ys ! 0) = S_type\<close> lms_slice_cons
                  suffix_type_s_bound by auto

          have "?b0 \<le> ?b1"
          proof(rule ccontr)
            assume "\<not>?b0 \<le> ?b1"
            hence "?b1 < ?b0"
              by simp
            hence "bucket_end \<alpha> T ?b1 \<le> bucket_start \<alpha> T ?b0"
              by (simp add: less_bucket_end_le_start)
            with s_index_upper_bound[OF s_perm_inv_elims(2,5)[OF assms(1)] `i' < length SA`]
                 s_index_lower_bound[OF s_perm_inv_elims(2,5)[OF assms(1)] `i < length SA`,
                   simplified]
                 order.strict_implies_order[OF `i < i'`]
            show False
              using \<open>SA ! i' = Suc (SA ! (B ! b))\<close> assms(4,6) by auto
          qed
          hence "?b0 = ?b1 \<or> ?b0 < ?b1"
            by linarith
          moreover
          have
            "?b0 < ?b1 \<Longrightarrow>
             list_less_eq_ns (lms_slice T (Suc j)) (lms_slice T (Suc (SA ! (B ! b))))"
          proof -
            assume "?b0 < ?b1"
            hence "T ! (Suc j) < T ! (Suc (SA ! (B ! b)))"
              using assms(1) s_perm_inv_elims(8) strict_mono_less by blast
            moreover
            have "Suc j < length T"
              using \<open>i < length SA\<close> assms(1,4,6) s_perm_inv_elims(5) s_seen_invD(1) by fastforce
            hence "\<exists>as. lms_slice T (Suc j) = T ! (Suc j) # as"
              by (metis dual_order.strict_trans abs_find_next_lms_lower_bound_1 lessI list_slice_Suc
                        lms_slice_def)
            then obtain as where
              "lms_slice T (Suc j) = T ! (Suc j) # as"
              by blast
            moreover
            have "Suc (SA ! (B ! b)) < length T"
              using \<open>SA ! i' = Suc (SA ! (B ! b))\<close> \<open>i < i'\<close> \<open>i' < length SA\<close> assms(1)
                    s_perm_inv_elims(5) s_seen_invD(1) by fastforce
            hence "\<exists>bs. lms_slice T (Suc (SA ! (B ! b))) = T ! (Suc (SA ! (B ! b))) # bs"
              by (metis abs_find_next_lms_lower_bound_1 less_Suc_eq 
                        list_slice_Suc lms_slice_def)
            then obtain bs where
              "lms_slice T (Suc (SA ! (B ! b))) = T ! (Suc (SA ! (B ! b))) # bs"
              by blast
            ultimately show ?thesis
              using list_less_eq_ns_cons by fastforce
          qed
          moreover
          have
            "?b0 = ?b1 \<Longrightarrow>
             list_less_eq_ns (lms_slice T (Suc j)) (lms_slice T (Suc (SA ! (B ! b))))"
          proof -
            assume "?b0 = ?b1"
            with s_index_upper_bound[OF s_perm_inv_elims(2,5)[OF assms(1)] `i' < _`] `i < i'`
            have "i' < bucket_end \<alpha> T ?b0"
              by (simp add: \<open>SA ! i' = Suc (SA ! (B ! b))\<close>)

            have "suffix_type T (SA ! i) = S_type \<or> suffix_type T (SA ! i) = L_type"
              using SL_types.exhaust by blast
            moreover
            have "suffix_type T (SA ! i) = S_type \<Longrightarrow> ?thesis"
            proof -
              assume "suffix_type T (SA ! i) = S_type"
              with s_seen_invD(3)[OF s_perm_inv_elims(5)[OF assms(1)] `i < length SA`, simplified]
              have "in_s_current_bucket \<alpha> T B ?b0 i"
                by (simp add: assms(4) assms(6))
              hence "B ! ?b0 \<le> i"
                using in_s_current_bucket_def by blast
              hence "\<exists>m. B ! ?b0 + m = i"
                using less_eqE by blast
              then obtain m0 where
                "B ! ?b0 + m0 = i"
                by blast

              from `B ! ?b0 \<le> i` `i < i'`
              have "\<exists>m. B ! ?b0 + m = i'"
                by presburger
              then obtain m1 where
                "B ! ?b0 + m1 = i'"
                by blast
              hence "B ! ?b0 + m0 \<le> B ! ?b0 + m1"
                by (simp add: \<open>B ! \<alpha> (T ! Suc j) + m0 = i\<close> 
                    \<open>i < i'\<close> dual_order.order_iff_strict)
              hence "m0 \<le> m1"
                using add_le_imp_le_left by blast

              have "(list_slice SA (B ! ?b0) (bucket_end \<alpha> T ?b0)) ! m0 = Suc j"
                using \<open>B ! \<alpha> (T ! Suc j) + m0 = i\<close> \<open>i < length SA\<close>
                      \<open>in_s_current_bucket \<alpha> T B ?b0 i\<close> assms(4,6) 
                      in_s_current_bucketD(3)
                by (metis \<open>B ! \<alpha> (T ! Suc j) \<le> i\<close> diff_add_inverse list_slice_nth)
              moreover
              have "(list_slice SA (B ! ?b0) (bucket_end \<alpha> T ?b0)) ! m1 = Suc (SA ! (B ! b))"
                using \<open>B ! ?b0 + m1 = i'\<close> \<open>SA ! i' = Suc (SA ! (B ! b))\<close> \<open>i' < bucket_end \<alpha> T ?b0\<close>
                      \<open>i' < length SA\<close> 
                by (metis diff_add_inverse le_add1 list_slice_nth)
              moreover
              have "length (list_slice SA (B ! ?b0) (bucket_end \<alpha> T ?b0))
                    = (bucket_end \<alpha> T ?b0) - B ! ?b0"
                by (metis assms(1) bucket_end_le_length length_list_slice min_def s_perm_inv_def)
              with `B ! ?b0 + m1 = i'` `i' < bucket_end \<alpha> T ?b0`
              have "m1 < length (list_slice SA (B ! ?b0) (bucket_end \<alpha> T ?b0))"
                by linarith
              ultimately
              show ?thesis
                using ordlistns.sorted_nth_mono[OF
                        s_prefix_sorted_invD[OF assms(3) `?b0 \<le> \<alpha> (Max _)`] `m0 \<le> m1`]
                      \<open>m0 \<le> m1\<close> by auto
            qed
            moreover
            have "suffix_type T (SA ! i) = L_type \<Longrightarrow> ?thesis"
            proof -
              assume "suffix_type T (SA ! i) = L_type"
              with s_seen_invD(2)[OF s_perm_inv_elims(5)[OF assms(1)] `i < length SA`, simplified]
              have "in_l_bucket \<alpha> T ?b0 i"
                by (simp add: assms(4) assms(6))
              hence "bucket_start \<alpha> T ?b0 \<le> i"
                by (simp add: in_l_bucket_def)
              hence "\<exists>m. bucket_start \<alpha> T ?b0 + m = i"
                using less_eqE by blast
              then obtain m0 where
                "bucket_start \<alpha> T ?b0 + m0 = i"
                by blast

              have "suffix_type T (SA ! i') = L_type \<or> suffix_type T (SA ! i') = S_type"
                using SL_types.exhaust by blast
              moreover
              have "suffix_type T (SA ! i') = S_type \<Longrightarrow> ?thesis"
              proof -
                assume "suffix_type T (SA ! i') = S_type"

                have "SA ! i < length T"
                  by (meson \<open>i < length SA\<close> assms(1) order_refl s_perm_inv_elims(5) s_seen_invD(1))

                have "SA ! i' < length T"
                  by (simp add: \<open>suffix_type T (SA ! i') = S_type\<close> suffix_type_s_bound)

                from `?b0 = ?b1`
                have "T ! (Suc j) = T ! Suc (SA ! (B ! b))"
                  using assms(1) s_perm_inv_def strict_mono_eq by blast
                hence "hd (suffix T (SA ! i')) = hd (suffix T (SA ! i))"
                  by (metis \<open>SA ! i < length T\<close> \<open>SA ! i' < length T\<close> \<open>SA ! i' = Suc (SA ! (B ! b))\<close>
                            assms(4) assms(6) list.sel(1) suffix_cons_Suc)
                hence "list_less_ns (lms_slice T (SA ! i)) (lms_slice T (SA ! i'))"
                  using \<open>SA ! i < length T\<close> \<open>SA ! i' < length T\<close> \<open>SA ! i' = Suc (SA ! (B ! b))\<close>
                        \<open>T ! Suc j = T ! Suc (SA ! (B ! b))\<close> \<open>suffix_type T (SA ! i') = S_type\<close>
                        \<open>suffix_type T (SA ! i) = L_type\<close> assms(1,4,6) s_perm_inv_elims(13)
                        lms_slice_l_less_than_s_type by fastforce
                then show ?thesis
                  by (simp add: \<open>SA ! i' = Suc (SA ! (B ! b))\<close> assms(4,6))
              qed
              moreover
              have "suffix_type T (SA ! i') = L_type \<Longrightarrow> ?thesis"
              proof -
                assume "suffix_type T (SA ! i') = L_type"
                with s_seen_invD(2)[OF s_perm_inv_elims(5)[OF assms(1)] `i' < length SA`,
                      simplified `?b0 = ?b1`[symmetric] `SA ! i' = Suc (SA ! (B ! b))`]
                     `SA ! i' = Suc (SA ! (B ! b))`
                have "in_l_bucket \<alpha> T ?b0 i'"
                  by (simp add: \<open>i < i'\<close> dual_order.order_iff_strict)
                hence "i' < l_bucket_end \<alpha> T ?b0"
                  by (simp add: in_l_bucket_def)
                hence "\<exists>m. bucket_start \<alpha> T ?b0 + m = i'"
                  by (metis \<open>in_l_bucket \<alpha> T ?b0 i'\<close> in_l_bucket_def less_eqE)
                then obtain m1 where
                  "bucket_start \<alpha> T ?b0 + m1 = i'"
                  by blast

                let ?zs = "list_slice SA (bucket_start \<alpha> T ?b0) (l_bucket_end \<alpha> T ?b0)"

                have "?zs ! m0 = Suc j"
                  using \<open>bucket_start \<alpha> T ?b0 + m0 = i\<close> \<open>i < i'\<close> \<open>i < length SA\<close>
                        \<open>i' < l_bucket_end \<alpha> T ?b0\<close> assms(4,6)
                  by (metis \<open>bucket_start \<alpha> T (\<alpha> (T ! Suc j)) \<le> i\<close> 
                            diff_add_inverse dual_order.order_iff_strict 
                            list_slice_nth order.strict_trans1)
                moreover
                have "?zs ! m1 = Suc (SA ! (B ! b))"
                  using \<open>SA ! i' = Suc (SA ! (B ! b))\<close> \<open>bucket_start \<alpha> T ?b0 + m1 = i'\<close>
                        \<open>i' < l_bucket_end \<alpha> T ?b0\<close> \<open>i' < length SA\<close> 
                  by (metis \<open>in_l_bucket \<alpha> T (\<alpha> (T ! Suc j)) i'\<close> 
                            diff_add_inverse in_l_bucket_def list_slice_nth)
                moreover
                have "m0 \<le> m1"
                  using \<open>bucket_start \<alpha> T ?b0 + m0 = i\<close> \<open>bucket_start \<alpha> T ?b0 + m1 = i'\<close> \<open>i < i'\<close>
                  by linarith
                moreover
                have "length ?zs = l_bucket_end \<alpha> T ?b0 - bucket_start \<alpha> T ?b0"
                  by (metis \<open>?b0 \<le> \<alpha> (Max (set T))\<close> add_diff_cancel_left' assms(1) distinct_card
                        l_bucket_end_def l_bucket_size_def l_types_init_def l_types_init_maintained
                        s_perm_inv_def)
                hence "m1 < length ?zs"
                  using \<open>bucket_start \<alpha> T ?b0 + m1 = i'\<close> \<open>i' < l_bucket_end \<alpha> T ?b0\<close> by linarith
                moreover
                from s_prefix_sorted_pre_maintained[OF s_perm_inv_elims(2,4,10,11)[OF assms(1)]
                      assms(2)]
                have "s_prefix_sorted_pre \<alpha> T SA" .
                ultimately show ?thesis
                  using ordlistns.sorted_nth_mono[OF s_prefix_sorted_preD[of \<alpha> T SA,
                          OF _ `?b0 \<le> \<alpha> (Max _)`], of m0 m1]
                  by (simp add: \<open>m1 < length ?zs\<close> \<open>s_prefix_sorted_pre \<alpha> T SA\<close> le_less_trans)
              qed
              ultimately show ?thesis
                by blast
            qed
            ultimately show ?thesis
              by blast
          qed
          ultimately have
            "list_less_eq_ns (lms_slice T (Suc j)) (lms_slice T (Suc (SA ! (B ! b))))"
            by blast
          with S0 S1 `T ! j = T ! (?ys ! 0)`
          show ?thesis
            by (simp add: list_less_eq_ns_cons)
        qed
        ultimately show "list_less_eq_ns (lms_slice T j) (map (lms_slice T) ?ys ! 0)"
          by simp
      qed 
      ultimately show ?thesis
        using A by fastforce
    qed
    ultimately show ?thesis
      by simp
  qed
  moreover
  have "b \<noteq> b' \<Longrightarrow> ordlistns.sorted (map (lms_slice T) ?xs)"
  proof -
    assume "b \<noteq> b'"
    with s_sorted_maintained_unchanged_step[OF assms(1,4-) `b' \<le> _`]
         s_prefix_sorted_invD[OF assms(3) `b' \<le> _`]
    show ?thesis
      using ordlistns.sorted_map by blast
  qed
  ultimately show "ordlistns.sorted (map (lms_slice T) ?xs)"
    by blast
qed

theorem abs_induce_s_sorted_step:
  assumes "s_perm_inv \<alpha> T B SA0 SA i"
  and     "s_sorted_pre \<alpha> T SA0"
  and     "s_sorted_inv \<alpha> T B SA"
  and     "abs_induce_s_step (B, SA, i) (\<alpha>, T) = (B', SA', i')"
shows " s_sorted_inv \<alpha> T B' SA'"
proof (rule abs_induce_s_step.elims[OF assms(4)];
       clarsimp simp: assms(3,4) Let_def not_less
                split: if_splits SL_types.splits nat.splits[where ?nat = i] nat.splits)
  assume "B = B'" "SA' = SA"
  with assms(3)
  show "s_sorted_inv \<alpha> T B' SA"
    by simp
next
  assume "B = B'" "SA' = SA"
  with assms(3)
  show "s_sorted_inv \<alpha> T B' SA"
    by simp
next
  assume "B = B'" "SA' = SA"
  with assms(3)
  show "s_sorted_inv \<alpha> T B' SA"
    by simp
next
  assume "B = B'" "SA' = SA"
  with assms(3)
  show "s_sorted_inv \<alpha> T B' SA"
    by simp
next
  fix j

  let ?b = "\<alpha> (T ! j)"
  let ?k = "B ! ?b - Suc 0"

  assume A: "i = Suc i'" "Suc i' < length SA" "SA ! Suc i' = Suc j" "suffix_type T j = S_type"
            "B' = B[?b := ?k]" "SA' = SA[?k := j]"

  from s_sorted_inv_maintained_step[OF assms(1-3) A(1-4), of ?b ?k, simplified]
  show "s_sorted_inv \<alpha> T (B[?b := ?k]) (SA[?k := j])" .
qed

corollary abs_induce_s_sorted_step_alt:
 "\<And>a. s_sorted_inv_alt \<alpha> T SA0 a \<Longrightarrow> s_sorted_inv_alt \<alpha> T SA0 (abs_induce_s_step a (\<alpha>, T))"
proof -
  fix a
  assume "s_sorted_inv_alt \<alpha> T SA0 a"

  have "\<exists>B SA i. a = (B, SA, i)"
    by (meson prod_cases3)
  then obtain B SA i where
    "a = (B, SA, i)"
    by blast
  with `s_sorted_inv_alt \<alpha> T SA0 a`
  have P: "s_perm_inv \<alpha> T B SA0 SA i" "s_sorted_pre \<alpha> T SA0" "s_sorted_inv \<alpha> T B SA"
    by simp_all

  from abs_induce_s_step_ex[of "(B, SA, i)" "(\<alpha>, T)"]
  obtain B' SA' i' where
    Q: "abs_induce_s_step (B, SA, i) (\<alpha>, T) = (B', SA', i')"
    by blast

  from abs_induce_s_sorted_step[OF P Q] abs_induce_s_perm_step[OF P(1) Q] `s_sorted_pre _ _ _`
  show "s_sorted_inv_alt \<alpha> T SA0 (abs_induce_s_step a (\<alpha>, T))"
    using Q \<open>a = (B, SA, i)\<close> by auto
qed

theorem abs_induce_s_sorted_alt_maintained:
  assumes "s_sorted_inv_alt \<alpha> T SA0 (B, SA, length T)"
  shows "s_sorted_inv_alt \<alpha> T SA0 (abs_induce_s_base \<alpha> T B SA)"
  unfolding abs_induce_s_base_def
  using repeat_maintain_inv
          [of "s_sorted_inv_alt \<alpha> T SA0" abs_induce_s_step "(\<alpha>, T)", OF _ assms(1)]
              abs_induce_s_sorted_step_alt
  by blast

corollary abs_induce_s_sorted_maintained:
  assumes "abs_induce_s_base \<alpha> T B SA = (B', SA', n)"
  and     "s_perm_inv \<alpha> T B SA0 SA (length T)"
  and     "s_sorted_pre \<alpha> T SA0"
  and     "s_sorted_inv \<alpha> T B SA"
shows "s_sorted_inv \<alpha> T B' SA'"
  using assms abs_induce_s_sorted_alt_maintained by force

theorem abs_induce_s_prefix_sorted_step:
  assumes "s_perm_inv \<alpha> T B SA0 SA i"
  and     "s_prefix_sorted_pre \<alpha> T SA0"
  and     "s_prefix_sorted_inv \<alpha> T B SA"
  and     "abs_induce_s_step (B, SA, i) (\<alpha>, T) = (B', SA', i')"
shows "s_prefix_sorted_inv \<alpha> T B' SA'"
proof (rule abs_induce_s_step.elims[OF assms(4)];
       clarsimp simp: assms(3,4) Let_def not_less
                split: if_splits SL_types.splits nat.splits[where ?nat = i] nat.splits)
  assume "B = B'"
  with assms(3)
  show "s_prefix_sorted_inv \<alpha> T B' SA"
    by simp
next
  assume "B = B'"
  with assms(3)
  show "s_prefix_sorted_inv \<alpha> T B' SA"
    by simp
next
  assume "B = B'"
  with assms(3)
  show "s_prefix_sorted_inv \<alpha> T B' SA"
    by simp
next
  assume "B = B'"
  with assms(3)
  show "s_prefix_sorted_inv \<alpha> T B' SA"
    by simp
next
  fix j

  let ?b = "\<alpha> (T ! j)"
  let ?k = "B ! ?b - Suc 0"

  assume A: "i = Suc i'" "Suc i' < length SA" "SA ! Suc i' = Suc j" "suffix_type T j = S_type"
            "B' = B[?b := ?k]" "SA' = SA[?k := j]"

  from s_prefix_sorted_inv_maintained_step[OF assms(1-3) A(1-4), of ?b ?k, simplified]
  show "s_prefix_sorted_inv \<alpha> T (B[?b := ?k]) (SA[?k := j])" .
qed

corollary abs_induce_s_prefix_sorted_step_alt:
 "\<And>a. s_prefix_sorted_inv_alt \<alpha> T SA0 a \<Longrightarrow>
      s_prefix_sorted_inv_alt \<alpha> T SA0 (abs_induce_s_step a (\<alpha>, T))"
proof -
  fix a
  assume "s_prefix_sorted_inv_alt \<alpha> T SA0 a"

  have "\<exists>B SA i. a = (B, SA, i)"
    by (meson prod_cases3)
  then obtain B SA i where
    "a = (B, SA, i)"
    by blast
  with `s_prefix_sorted_inv_alt \<alpha> T SA0 a`
  have P: "s_perm_inv \<alpha> T B SA0 SA i" "s_prefix_sorted_pre \<alpha> T SA0" "s_prefix_sorted_inv \<alpha> T B SA"
    by simp_all

  from abs_induce_s_step_ex[of "(B, SA, i)" "(\<alpha>, T)"]
  obtain B' SA' i' where
    Q: "abs_induce_s_step (B, SA, i) (\<alpha>, T) = (B', SA', i')"
    by blast

  from abs_induce_s_prefix_sorted_step[OF P Q] abs_induce_s_perm_step[OF P(1) Q] `s_prefix_sorted_pre _ _ _`
  show "s_prefix_sorted_inv_alt \<alpha> T SA0 (abs_induce_s_step a (\<alpha>, T))"
    using Q \<open>a = (B, SA, i)\<close> by auto
qed

theorem abs_induce_s_prefix_sorted_alt_maintained:
  assumes "s_prefix_sorted_inv_alt \<alpha> T SA0 (B, SA, length T)"
  shows "s_prefix_sorted_inv_alt \<alpha> T SA0 (abs_induce_s_base \<alpha> T B SA)"
  unfolding abs_induce_s_base_def
  using repeat_maintain_inv[of "s_prefix_sorted_inv_alt \<alpha> T SA0" abs_induce_s_step "(\<alpha>, T)",
          OF _ assms(1)]
        abs_induce_s_prefix_sorted_step_alt
  by blast

corollary abs_induce_s_prefix_sorted_maintained:
  assumes "abs_induce_s_base \<alpha> T B SA = (B', SA', n)"
  and     "s_perm_inv \<alpha> T B SA0 SA (length T)"
  and     "s_prefix_sorted_pre \<alpha> T SA0"
  and     "s_prefix_sorted_inv \<alpha> T B SA"
shows "s_prefix_sorted_inv \<alpha> T B' SA'"
  using assms abs_induce_s_prefix_sorted_alt_maintained by force

theorem s_sorted_bucket:
  assumes "s_perm_inv \<alpha> T B SA0 SA 0"
  and     "s_sorted_pre \<alpha> T SA0"
  and     "s_sorted_inv \<alpha> T B SA"
  and     "b \<le> \<alpha> (Max (set T))"
shows "ordlistns.sorted (map (suffix T) (list_slice SA (bucket_start \<alpha> T b) (bucket_end \<alpha> T b)))"
      (is "ordlistns.sorted (map (suffix T) ?xs)")
proof -
  let ?ys = "list_slice SA (bucket_start \<alpha> T b) (l_bucket_end \<alpha> T b)"
  and ?zs = "list_slice SA (s_bucket_start \<alpha> T b) (bucket_end \<alpha> T b)"

  from s_perm_inv_0_B_val[OF assms(1,4)]
  have "B ! b = s_bucket_start \<alpha> T b" .

  from s_sorted_pre_maintained[OF s_perm_inv_elims(2,4,10,11)[OF assms(1)] assms(2)]
  have "s_sorted_pre \<alpha> T SA" .

  have "?xs = ?ys @ ?zs"
    by (metis bucket_start_le_s_bucket_start l_bucket_end_le_bucket_end list_slice_append
          s_bucket_start_eq_l_bucket_end)
  hence "map (suffix T) ?xs = map (suffix T) ?ys @ map (suffix T) ?zs"
    by simp
  moreover
  from s_sorted_preD[OF `s_sorted_pre _ _ SA` `b \<le> _`]
  have "ordlistns.sorted (map (suffix T) ?ys)" .
  moreover
  from s_sorted_invD[OF assms(3,4), simplified `_ = s_bucket_start \<alpha> _ _`]
  have "ordlistns.sorted (map (suffix T) ?zs)" .
  moreover
  have "\<forall>y \<in> set (map (suffix T) ?ys). \<forall>z \<in> set (map (suffix T) ?zs). list_less_eq_ns y z"
  proof(safe)
    fix y z
    assume "y \<in> set (map (suffix T) ?ys)" "z \<in> set (map (suffix T) ?zs)"
    with in_set_mapD[of y "suffix T" ?ys]
         in_set_mapD[of z "suffix T" ?zs]
    obtain i j where
      "y = suffix T i" "i \<in> set ?ys" 
      "z = suffix T j" "j \<in> set ?zs"
      by blast

    from l_types_initD(1)[OF l_types_init_maintained[OF s_perm_inv_elims(2,4,10-12)[OF assms(1)]]
          `b \<le> _`]
         `i \<in> set ?ys`
    have "i \<in> l_bucket \<alpha> T b"
      by blast
    hence "suffix_type T i = L_type" "\<alpha> (T ! i) = b" "i < length T"
      by (simp add: l_bucket_def bucket_def)+
    moreover
    from s_bucket_eq_list_slice[OF s_perm_inv_elims(1,3,11)[OF assms(1)] `b \<le> _`
          `B ! b = s_bucket_start \<alpha> _ _`]
         `j \<in> set ?zs`
    have "j \<in> s_bucket \<alpha> T b"
      by blast
    hence "suffix_type T j = S_type" "\<alpha> (T ! j) = b" "j < length T"
      by (simp add: s_bucket_def bucket_def)+
    moreover
    have "T ! i = T ! j"
      using calculation(2,5) s_perm_inv_elims(8)[OF assms(1)] strict_mono_eq by fastforce
    ultimately have "list_less_eq_ns (suffix T i) (suffix T j)"
      using l_less_than_s_type_suffix[of j T i] by simp
    then show "list_less_eq_ns y z"
      using \<open>y = suffix T i\<close> \<open>z = suffix T j\<close> by blast
  qed
  ultimately show ?thesis
    by (simp add: ordlistns.sorted_append)
qed

theorem abs_induce_s_base_sorted:
  assumes "abs_induce_s_base \<alpha> T B SA = (B', SA', n)"
  and     "s_perm_inv \<alpha> T B SA0 SA (length T)"
  and     "s_sorted_pre \<alpha> T SA0"
  and     "s_sorted_inv \<alpha> T B SA"
shows "ordlistns.sorted (map (suffix T) SA')"
proof (intro sorted_wrt_mapI)
  fix i j
  assume "i < j" "j < length SA'"
  hence "i < length T" "j < length T"
    by (metis (no_types, lifting) abs_induce_s_perm_maintained 
              assms(1,2) order.strict_trans s_perm_inv_elims(11))+

  let ?goal = "list_less_eq_ns (suffix T (SA' ! i)) (suffix T (SA' ! j))"

  from index_in_bucket_interval_gen[OF `i < length _` s_perm_inv_elims(8)[OF assms(2)]]
  obtain b0 where
    "b0 \<le> \<alpha> (Max (set T))"
    "bucket_start \<alpha> T b0 \<le> i"
    "i < bucket_end \<alpha> T b0"
    by blast

  from index_in_bucket_interval_gen[OF `j < length T` s_perm_inv_elims(8)[OF assms(2)]]
  obtain b1 where
    "b1 \<le> \<alpha> (Max (set T))"
    "bucket_start \<alpha> T b1 \<le> j"
    "j < bucket_end \<alpha> T b1"
    by blast

  from abs_induce_s_perm_maintained[OF assms(1,2)]
  have "s_perm_inv \<alpha> T B' SA0 SA' n" .
  moreover
  have "n = 0"
    by (metis Pair_inject assms(1) abs_induce_s_base_index)
  ultimately have "s_perm_inv \<alpha> T B' SA0 SA' 0"
    by simp

  let ?xs = "list_slice SA' (bucket_start \<alpha> T b0) (bucket_end \<alpha> T b0)"
  and ?ys = "list_slice SA' (bucket_start \<alpha> T b1) (bucket_end \<alpha> T b1)"

  have "b0 \<le> b1"
  proof (rule ccontr)
    assume "\<not> b0 \<le> b1"
    hence "b1 < b0"
      by (simp add: not_le)
    hence "bucket_end \<alpha> T b1 \<le> bucket_start \<alpha> T b0"
      by (simp add: less_bucket_end_le_start)
    with `j < bucket_end \<alpha> T b1` `bucket_start \<alpha> T b0 \<le> i` `i < j`
    show False
      by linarith
  qed
  hence "b0 = b1 \<or> b0 < b1"
    by (simp add: nat_less_le)
  moreover
  have "b0 < b1 \<Longrightarrow> ?goal"
  proof -
    assume "b0 < b1"
    moreover
    from s_perm_inv_0_list_slice_bucket[OF `s_perm_inv _ _ _ _ _ 0` `b0 \<le> \<alpha> _`]
    have "set ?xs = bucket \<alpha> T b0" .
    hence "SA' ! i \<in> bucket \<alpha> T b0"
      by (metis \<open>bucket_start \<alpha> T b0 \<le> i\<close> \<open>i < bucket_end \<alpha> T b0\<close> \<open>s_perm_inv \<alpha> T B' SA0 SA' 0\<close>
            bucket_end_le_length list_slice_nth_mem s_perm_inv_elims(11))
    hence "\<alpha> (T ! (SA' ! i)) = b0" "SA' ! i < length T"
      by (simp add: bucket_def)+
    moreover
    from s_perm_inv_0_list_slice_bucket[OF `s_perm_inv _ _ _ _ _ 0` `b1 \<le> \<alpha> _`]
    have "set ?ys = bucket \<alpha> T b1" .
    hence "SA' ! j \<in> bucket \<alpha> T b1"
      by (metis \<open>bucket_start \<alpha> T b1 \<le> j\<close> \<open>j < bucket_end \<alpha> T b1\<close> \<open>s_perm_inv \<alpha> T B' SA0 SA' 0\<close>
            bucket_end_le_length list_slice_nth_mem s_perm_inv_elims(11))
    hence "\<alpha> (T ! (SA' ! j)) = b1" "SA' ! j < length T"
      by (simp add: bucket_def)+
    ultimately have "T ! (SA' ! i) < T ! (SA' ! j)"
      using assms(2) s_perm_inv_elims(8) strict_mono_less by blast
    then show ?thesis
      by (metis \<open>SA' ! i < length T\<close> \<open>SA' ! j < length T\<close> less_imp_le list_less_eq_ns_cons neq_iff
            suffix_cons_Suc)
  qed
  moreover
  have "b0 = b1 \<Longrightarrow> ?goal"
  proof -
    assume "b0 = b1"
    with `j < bucket_end \<alpha> T b1`
    have "j < bucket_end \<alpha> T b0"
      by simp

    have "\<exists>i'. i = bucket_start \<alpha> T b0 + i'"
      using \<open>bucket_start \<alpha> T b0 \<le> i\<close> nat_le_iff_add by blast
    then obtain i' where
      "i = bucket_start \<alpha> T b0 + i'"
      by blast

    have "\<exists>j'. j = bucket_start \<alpha> T b0 + j'"
      by (simp add: \<open>b0 = b1\<close> \<open>bucket_start \<alpha> T b1 \<le> j\<close> le_Suc_ex)
    then obtain j' where
      "j = bucket_start \<alpha> T b0 + j'"
      by blast
    with `i < j` `i = bucket_start \<alpha> T b0 + i'`
    have "i' \<le> j'"
      by linarith

    have "j' < length ?xs"
      by (metis \<open>b0 = b1\<close> \<open>j < bucket_end \<alpha> T b1\<close> \<open>j = bucket_start \<alpha> T b0 + j'\<close>
                \<open>s_perm_inv \<alpha> T B' SA0 SA' n\<close> add.commute bucket_end_le_length length_list_slice
                less_diff_conv min_def s_perm_inv_elims(11))
    with ordlistns.sorted_nth_mono[OF s_sorted_bucket[OF `s_perm_inv _ _ _ _ _ 0` assms(3)
          abs_induce_s_sorted_maintained[OF assms] `b0 \<le> \<alpha> _`] `i' \<le> j'`]
    have "list_less_eq_ns (suffix T (?xs ! i')) (suffix T (?xs ! j'))"
      using \<open>i' \<le> j'\<close> nth_map by auto
    moreover
    have "SA' ! i = ?xs ! i'"
      using \<open>i < bucket_end \<alpha> T b0\<close> \<open>i < length T\<close> \<open>i = bucket_start \<alpha> T b0 + i'\<close>
            \<open>s_perm_inv \<alpha> T B' SA0 SA' n\<close> s_perm_inv_elims(11) 
      by (metis \<open>bucket_start \<alpha> T b0 \<le> i\<close> diff_add_inverse list_slice_nth)
     moreover
    have "SA' ! j = ?xs ! j'"
      using \<open>j < bucket_end \<alpha> T b0\<close> \<open>j < length SA'\<close> 
            \<open>j = bucket_start \<alpha> T b0 + j'\<close> 
      by (simp add: nth_list_slice)
    ultimately show ?goal
      by simp
  qed
  ultimately show ?goal
    by blast
qed

theorem s_prefix_sorted_bucket:
  assumes "s_perm_inv \<alpha> T B SA0 SA 0"
  and     "s_prefix_sorted_pre \<alpha> T SA0"
  and     "s_prefix_sorted_inv \<alpha> T B SA"
  and     "b \<le> \<alpha> (Max (set T))"
shows "ordlistns.sorted (map (lms_slice T) (list_slice SA (bucket_start \<alpha> T b) (bucket_end \<alpha> T b)))"
      (is "ordlistns.sorted (map (lms_slice T) ?xs)")
proof -
  let ?ys = "list_slice SA (bucket_start \<alpha> T b) (l_bucket_end \<alpha> T b)"
  and ?zs = "list_slice SA (s_bucket_start \<alpha> T b) (bucket_end \<alpha> T b)"

  from s_perm_inv_0_B_val[OF assms(1,4)]
  have "B ! b = s_bucket_start \<alpha> T b" .

  from s_prefix_sorted_pre_maintained[OF s_perm_inv_elims(2,4,10,11)[OF assms(1)] assms(2)]
  have "s_prefix_sorted_pre \<alpha> T SA" .

  have "?xs = ?ys @ ?zs"
    by (metis bucket_start_le_s_bucket_start l_bucket_end_le_bucket_end list_slice_append
          s_bucket_start_eq_l_bucket_end)
  hence "map (lms_slice T) ?xs = map (lms_slice T) ?ys @ map (lms_slice T) ?zs"
    by simp
  moreover
  from s_prefix_sorted_preD[OF `s_prefix_sorted_pre _ _ SA` `b \<le> _`]
  have "ordlistns.sorted (map (lms_slice T) ?ys)" .
  moreover
  from s_prefix_sorted_invD[OF assms(3,4), simplified `_ = s_bucket_start \<alpha> _ _`]
  have "ordlistns.sorted (map (lms_slice T) ?zs)" .
  moreover
  have "\<forall>y \<in> set (map (lms_slice T) ?ys). \<forall>z \<in> set (map (lms_slice T) ?zs).
          list_less_eq_ns y z"
  proof safe
    fix y z
    assume "y \<in> set (map (lms_slice T) ?ys)"
           "z \<in> set (map (lms_slice T) ?zs)"
    with in_set_mapD[of y "lms_slice T" ?ys]
         in_set_mapD[of z "lms_slice T" ?zs]
    obtain i j where
      "y = lms_slice T i" 
      "i \<in> set ?ys"
      "z = lms_slice T j"
      "j \<in> set ?zs"
      by blast

    from l_types_initD(1)[OF l_types_init_maintained[OF s_perm_inv_elims(2,4,10-12)[OF assms(1)]]
          `b \<le> _`]
         `i \<in> set ?ys`
    have "i \<in> l_bucket \<alpha> T b"
      by blast
    hence "suffix_type T i = L_type" "\<alpha> (T ! i) = b" "i < length T"
      by (simp add: l_bucket_def bucket_def)+
    moreover
    from s_bucket_eq_list_slice[OF s_perm_inv_elims(1,3,11)[OF assms(1)] `b \<le> _`
          `B ! b = s_bucket_start \<alpha> _ _`]
         `j \<in> set ?zs`
    have "j \<in> s_bucket \<alpha> T b"
      by blast
    hence "suffix_type T j = S_type" "\<alpha> (T ! j) = b" "j < length T"
      by (simp add: s_bucket_def bucket_def)+
    moreover
    have "T ! i = T ! j"
      using assms(1) calculation(2,5) s_perm_inv_elims(8) strict_mono_eq by fastforce
    ultimately have "list_less_eq_ns (lms_slice T i) (lms_slice T j)"
      using lms_slice_l_less_than_s_type[of i T j] by simp
    then show "list_less_eq_ns y z"
      by (simp add: \<open>y = lms_slice T i\<close> \<open>z = lms_slice T j\<close>)
  qed
  ultimately show ?thesis
    by (simp add: ordlistns.sorted_append)
qed

theorem abs_induce_s_base_prefix_sorted:
  assumes "abs_induce_s_base \<alpha> T B SA = (B', SA', n)"
  and     "s_perm_inv \<alpha> T B SA0 SA (length T)"
  and     "s_prefix_sorted_pre \<alpha> T SA0"
  and     "s_prefix_sorted_inv \<alpha> T B SA"
shows "ordlistns.sorted (map (lms_slice T) SA')"
proof (intro sorted_wrt_mapI)
  fix i j
  assume "i < j" "j < length SA'"
  hence "i < length T" "j < length T"
    by (metis (no_types, lifting) abs_induce_s_perm_maintained 
              assms(1,2) order.strict_trans s_perm_inv_elims(11))+

  let ?goal = "list_less_eq_ns (lms_slice T (SA' ! i)) (lms_slice T (SA' ! j))"

  from index_in_bucket_interval_gen[OF `i < length _` s_perm_inv_elims(8)[OF assms(2)]]
  obtain b0 where
    "b0 \<le> \<alpha> (Max (set T))"
    "bucket_start \<alpha> T b0 \<le> i"
    "i < bucket_end \<alpha> T b0"
    by blast

  from index_in_bucket_interval_gen[OF `j < length T` s_perm_inv_elims(8)[OF assms(2)]]
  obtain b1 where
    "b1 \<le> \<alpha> (Max (set T))"
    "bucket_start \<alpha> T b1 \<le> j"
    "j < bucket_end \<alpha> T b1"
    by blast

  from abs_induce_s_perm_maintained[OF assms(1,2)]
  have "s_perm_inv \<alpha> T B' SA0 SA' n" .
  moreover
  have "n = 0"
    by (metis Pair_inject assms(1) abs_induce_s_base_index)
  ultimately have "s_perm_inv \<alpha> T B' SA0 SA' 0"
    by simp

  let ?xs = "list_slice SA' (bucket_start \<alpha> T b0) (bucket_end \<alpha> T b0)"
  and ?ys = "list_slice SA' (bucket_start \<alpha> T b1) (bucket_end \<alpha> T b1)"

  have "b0 \<le> b1"
  proof (rule ccontr)
    assume "\<not>b0 \<le> b1"
    hence "b1 < b0"
      by (simp add: not_le)
    hence "bucket_end \<alpha> T b1 \<le> bucket_start \<alpha> T b0"
      by (simp add: less_bucket_end_le_start)
    with `j < bucket_end \<alpha> T b1` `bucket_start \<alpha> T b0 \<le> i` `i < j`
    show False
      by linarith
  qed
  hence "b0 = b1 \<or> b0 < b1"
    by (simp add: nat_less_le)
  moreover
  have "b0 < b1 \<Longrightarrow> ?goal"
  proof -
    assume "b0 < b1"
    moreover
    from s_perm_inv_0_list_slice_bucket[OF `s_perm_inv _ _ _ _ _ 0` `b0 \<le> \<alpha> _`]
    have "set ?xs = bucket \<alpha> T b0" .
    hence "SA' ! i \<in> bucket \<alpha> T b0"
      by (metis \<open>bucket_start \<alpha> T b0 \<le> i\<close> \<open>i < bucket_end \<alpha> T b0\<close> \<open>s_perm_inv \<alpha> T B' SA0 SA' 0\<close>
            bucket_end_le_length list_slice_nth_mem s_perm_inv_elims(11))
    hence "\<alpha> (T ! (SA' ! i)) = b0" "SA' ! i < length T"
      by (simp add: bucket_def)+
    moreover
    from s_perm_inv_0_list_slice_bucket[OF `s_perm_inv _ _ _ _ _ 0` `b1 \<le> \<alpha> _`]
    have "set ?ys = bucket \<alpha> T b1" .
    hence "SA' ! j \<in> bucket \<alpha> T b1"
      by (metis \<open>bucket_start \<alpha> T b1 \<le> j\<close> \<open>j < bucket_end \<alpha> T b1\<close> \<open>s_perm_inv \<alpha> T B' SA0 SA' 0\<close>
            bucket_end_le_length list_slice_nth_mem s_perm_inv_elims(11))
    hence "\<alpha> (T ! (SA' ! j)) = b1" "SA' ! j < length T"
      by (simp add: bucket_def)+
    ultimately have "T ! (SA' ! i) < T ! (SA' ! j)"
      using assms(2) s_perm_inv_elims(8) strict_mono_less by blast
    then show ?thesis
      by (metis \<open>SA' ! i < length T\<close> \<open>SA' ! j < length T\<close> abs_find_next_lms_lower_bound_1 
            less_SucI less_imp_le list_less_eq_ns_cons list_slice_Suc neq_iff lms_slice_def)
  qed
  moreover
  have "b0 = b1 \<Longrightarrow> ?goal"
  proof -
    assume "b0 = b1"
    with `j < bucket_end \<alpha> T b1`
    have "j < bucket_end \<alpha> T b0"
      by simp

    have "\<exists>i'. i = bucket_start \<alpha> T b0 + i'"
      using \<open>bucket_start \<alpha> T b0 \<le> i\<close> nat_le_iff_add by blast
    then obtain i' where
      "i = bucket_start \<alpha> T b0 + i'"
      by blast

    have "\<exists>j'. j = bucket_start \<alpha> T b0 + j'"
      by (simp add: \<open>b0 = b1\<close> \<open>bucket_start \<alpha> T b1 \<le> j\<close> le_Suc_ex)
    then obtain j' where
      "j = bucket_start \<alpha> T b0 + j'"
      by blast
    with `i < j` `i = bucket_start \<alpha> T b0 + i'`
    have "i' \<le> j'"
      by linarith

    have "j' < length ?xs"
      by (metis \<open>b0 = b1\<close> 
            \<open>j < bucket_end \<alpha> T b1\<close> 
            \<open>j = bucket_start \<alpha> T b0 + j'\<close>
            \<open>s_perm_inv \<alpha> T B' SA0 SA' n\<close> 
            add.commute bucket_end_le_length length_list_slice
            less_diff_conv min_def s_perm_inv_elims(11))
    with ordlistns.sorted_nth_mono
           [OF s_prefix_sorted_bucket
                 [OF `s_perm_inv _ _ _ _ _ 0` assms(3)
                     abs_induce_s_prefix_sorted_maintained
                        [OF assms] `b0 \<le> \<alpha> _`] `i' \<le> j'`]
    have "list_less_eq_ns (lms_slice T (?xs ! i')) (lms_slice T (?xs ! j'))"
      using \<open>i' \<le> j'\<close> nth_map by auto
    moreover
    have "SA' ! i = ?xs ! i'"
      using \<open>i < bucket_end \<alpha> T b0\<close> 
            \<open>i < length T\<close> 
            \<open>i = bucket_start \<alpha> T b0 + i'\<close>
            \<open>s_perm_inv \<alpha> T B' SA0 SA' n\<close>  
            \<open>j' < length (list_slice SA' 
                     (bucket_start \<alpha> T b0) 
                     (bucket_end \<alpha> T b0))\<close> 
      by (metis \<open>i' \<le> j'\<close> nth_list_slice order.strict_trans1)
    moreover
    have "SA' ! j = ?xs ! j'"
      using \<open>j < bucket_end \<alpha> T b0\<close> \<open>j < length SA'\<close> 
            \<open>j = bucket_start \<alpha> T b0 + j'\<close> 
      by (simp add: nth_list_slice)
    ultimately show ?goal
      by simp
  qed
  ultimately show ?goal
    by blast
qed

section "Induce S Correctness Theorems"

theorem abs_induce_s_perm:
  assumes "s_perm_pre \<alpha> T B SA (length T)"
  shows "abs_induce_s \<alpha> T B SA <~~> [0..< length T]"
proof -
  from s_perm_inv_established assms[simplified s_perm_pre_def]
  have "s_perm_inv \<alpha> T B SA SA (length T)"
    by blast
  moreover
  from abs_induce_s_base_index[of \<alpha> T B SA]
  obtain B' SA' where
    "abs_induce_s_base \<alpha> T B SA = (B', SA', 0)"
    by blast
  ultimately have "s_perm_inv \<alpha> T B' SA SA' 0"
    using abs_induce_s_perm_maintained[of \<alpha> T B SA B' SA' 0 SA]
    by blast
  hence "SA' <~~> [0..< length T]"
    using abs_induce_s_base_perm[OF `abs_induce_s_base \<alpha> T B SA = (B', SA', 0)`]
    by blast
  with `abs_induce_s_base \<alpha> T B SA = (B', SA', 0)`
  show ?thesis
    by (simp add: abs_induce_s_def)
qed


 \<comment>\<open> Used in SAIS algorithm as part of inducing the suffix ordering based on LMS \<close>
theorem abs_induce_s_sorted:
  assumes "s_perm_pre \<alpha> T B SA (length T)"
  and     "s_sorted_pre \<alpha> T SA"
shows "ordlistns.sorted (map (suffix T) (abs_induce_s \<alpha> T B SA))"
proof -
  from s_perm_inv_established assms(1)[simplified s_perm_pre_def]
  have "s_perm_inv \<alpha> T B SA SA (length T)"
    by blast
  moreover
  from abs_induce_s_base_index[of \<alpha> T B SA]
  obtain B' SA' where
    "abs_induce_s_base \<alpha> T B SA = (B', SA', 0)"
    by blast
  moreover
  from s_sorted_inv_established assms(1)[simplified s_perm_pre_def]
  have "s_sorted_inv \<alpha> T B SA"
    by blast
  ultimately have "ordlistns.sorted (map (suffix T) SA')"
    using abs_induce_s_base_sorted[OF _ _ assms(2), of B SA B' SA' 0]
    by blast
  then show ?thesis
    by (simp add: \<open>abs_induce_s_base \<alpha> T B SA = (B', SA', 0)\<close> abs_induce_s_def)
qed

 \<comment>\<open> Used in SAIS algorithm as part of inducing the prefix ordering based on LMS \<close>
theorem abs_induce_s_prefix_sorted:
  assumes "s_perm_pre \<alpha> T B SA (length T)"
  and     "s_prefix_sorted_pre \<alpha> T SA"
shows "ordlistns.sorted (map (lms_slice T) (abs_induce_s \<alpha> T B SA))"
proof -

  from s_perm_inv_established assms(1)[simplified s_perm_pre_def]
  have "s_perm_inv \<alpha> T B SA SA (length T)"
    by blast
  moreover
  from abs_induce_s_base_index[of \<alpha> T B SA]
  obtain B' SA' where
    "abs_induce_s_base \<alpha> T B SA = (B', SA', 0)"
    by blast
  moreover
  from s_prefix_sorted_inv_established assms(1)[simplified s_perm_pre_def]
  have "s_prefix_sorted_inv \<alpha> T B SA"
    by blast
  ultimately have "ordlistns.sorted (map (lms_slice T) SA')"
    using abs_induce_s_base_prefix_sorted[OF _ _ assms(2), of B SA B' SA' 0]
    by blast
  then show ?thesis
    by (simp add: \<open>abs_induce_s_base \<alpha> T B SA = (B', SA', 0)\<close> abs_induce_s_def)
qed

end