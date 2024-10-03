theory Abs_Bucket_Insert_Verification
  imports 
    "../abs-def/Abs_SAIS"
    "../../util/List_Util"
    "../../util/List_Slice"
   

begin

section \<open>Bucket Insert with Ghost State\<close>

fun bucket_insert_abs' ::
  "(('a :: {linorder, order_bot}) \<Rightarrow> nat) \<Rightarrow>
   'a list \<Rightarrow>
   nat list \<Rightarrow>
   nat list \<Rightarrow>
   nat list \<Rightarrow>
   nat list \<Rightarrow>
   nat list \<times> nat list \<times> nat list"
where
  "bucket_insert_abs' \<alpha> T B SA gs [] = (SA, B, gs)" |
  "bucket_insert_abs' \<alpha> T B SA gs (x # xs) =
    (let b = \<alpha> (T ! x);
         k = B ! b - Suc 0;
         SA' = SA[k := x];
         B' = B[b := k];
         gs' = gs @ [x]
     in bucket_insert_abs' \<alpha> T B' SA' gs' xs)"

section \<open>Simple Properties\<close>

lemma abs_bucket_insert_length:
  "length (abs_bucket_insert \<alpha> T B SA xs) = length SA"
  by (induct xs arbitrary: B SA; simp add: Let_def)

lemma abs_bucket_insert_equiv:
  "abs_bucket_insert \<alpha> T B SA xs = fst (bucket_insert_abs' \<alpha> T B SA gs xs)"
  by (induct xs arbitrary: B SA gs; simp add: Let_def)

section \<open>Invariants\<close>

subsection \<open>Defintions and Simple Helper Lemmas\<close>

subsubsection \<open>Distinctness\<close>

definition lms_distinct_inv :: 
  "('a :: {linorder, order_bot}) list \<Rightarrow> nat list \<Rightarrow> nat list \<Rightarrow> bool"
where
  "lms_distinct_inv T SA LMS = 
     distinct ((filter (\<lambda>x. x < length T) SA) @ LMS)"

lemma lms_inv_distinct_inv_helper:
  assumes "lms_distinct_inv T SA LMS"
  shows   "distinct (filter (\<lambda>x. x < length T) SA) \<and> 
           distinct LMS \<and>
           set (filter (\<lambda>x. x < length T) SA) \<inter> set LMS = {}"
  using assms distinct_append lms_distinct_inv_def by blast

subsubsection \<open>LMS Bucket Ptr\<close>

definition cur_lms_types ::
  "('a :: {linorder, order_bot} \<Rightarrow> nat) \<Rightarrow> 'a list \<Rightarrow> nat list \<Rightarrow> nat \<Rightarrow> nat set"
where
  "cur_lms_types \<alpha> T SA b = 
      {i|i. i \<in> set SA \<and> 
      i \<in> lms_bucket \<alpha> T b }"

lemma cur_lms_subset_SA:
  "cur_lms_types \<alpha> T SA b \<subseteq> set SA"
  using cur_lms_types_def by blast

lemma cur_lms_subset_lms_bucket:
  "cur_lms_types \<alpha> T SA b \<subseteq> lms_bucket \<alpha> T b"
  using cur_lms_types_def by blast

definition num_lms_types ::
  "('a :: {linorder, order_bot} \<Rightarrow> nat) \<Rightarrow> 'a list \<Rightarrow> nat list \<Rightarrow> nat \<Rightarrow> nat"
where
  "num_lms_types \<alpha> T SA b = 
    card (cur_lms_types \<alpha> T SA b)"

lemma num_lms_types_upper_bound:
  "num_lms_types \<alpha> T SA b \<le> lms_bucket_size \<alpha> T b"
  by (metis not_le cur_lms_subset_lms_bucket num_lms_types_def
            finite_lms_bucket lms_bucket_size_def card_mono)

definition lms_bucket_ptr_inv ::
  "('a :: {linorder, order_bot} \<Rightarrow> nat) \<Rightarrow> 
   'a list \<Rightarrow> nat list \<Rightarrow> nat list \<Rightarrow> bool"
where
  "lms_bucket_ptr_inv \<alpha> T B SA \<equiv>
     (\<forall>b \<le> \<alpha> (Max (set T)). 
        B ! b + num_lms_types \<alpha> T SA b = bucket_end \<alpha> T b)"

lemma lms_bucket_ptr_invD:
  assumes "lms_bucket_ptr_inv \<alpha> T B SA"
  and     "b \<le> \<alpha> (Max (set T))"
  shows "B ! b + num_lms_types \<alpha> T SA b = bucket_end \<alpha> T b"
  using assms lms_bucket_ptr_inv_def by blast

lemma lms_bucket_ptr_lower_bound:
  assumes "lms_bucket_ptr_inv \<alpha> T B SA"
  and     "b \<le> \<alpha> (Max (set T))"
  shows "lms_bucket_start \<alpha> T b \<le> B ! b"
proof -
  from lms_bucket_ptr_invD[OF assms]
  have "B ! b + num_lms_types \<alpha> T SA b = bucket_end \<alpha> T b" .
  then show ?thesis
    by (metis add.commute add_le_cancel_left lms_bucket_pl_size_eq_end num_lms_types_upper_bound)
qed

lemma lms_bucket_ptr_upper_bound:
  assumes "lms_bucket_ptr_inv \<alpha> T B SA"
  and     "b \<le> \<alpha> (Max (set T))"
  shows   "B ! b \<le> bucket_end \<alpha> T b"
  by (metis assms le_iff_add lms_bucket_ptr_inv_def)

subsubsection \<open>Unknowns\<close>

definition lms_unknowns_inv ::
  "('a :: {linorder, order_bot} \<Rightarrow> nat) \<Rightarrow> 
   'a list \<Rightarrow> nat list \<Rightarrow> nat list \<Rightarrow> bool"
where
  "lms_unknowns_inv \<alpha> T B SA \<equiv>
      (\<forall>b \<le> \<alpha> (Max (set T)). 
        (\<forall>i. lms_bucket_start \<alpha> T b \<le> i \<and> 
             i < B ! b \<longrightarrow>  SA ! i = length T))"

lemma lms_unknowns_invD:
  assumes "lms_unknowns_inv \<alpha> T B SA"
  and     "b \<le> \<alpha> (Max (set T))"
  and     "lms_bucket_start \<alpha> T b \<le> i"
  and     "i < B ! b"
  shows "SA ! i = length T"
  using assms lms_unknowns_inv_def by blast

subsubsection \<open>Locations\<close>

definition lms_locations_inv ::
  "('a :: {linorder, order_bot} \<Rightarrow> nat) \<Rightarrow> 
   'a list \<Rightarrow> nat list \<Rightarrow> nat list \<Rightarrow> bool"
where
  "lms_locations_inv \<alpha> T B SA \<equiv>
      (\<forall>b \<le> \<alpha> (Max (set T)).
        (\<forall>i. B ! b \<le> i \<and> 
            i < bucket_end \<alpha> T b \<longrightarrow> SA ! i \<in> lms_bucket \<alpha> T b))"

lemma lms_locations_invD:
  assumes "lms_locations_inv \<alpha> T B SA"
  and     "b \<le> \<alpha> (Max (set T))"
  and     "B ! b \<le> i" 
  and     "i < bucket_end \<alpha> T b" 
  shows "SA ! i \<in> lms_bucket \<alpha> T b"
  using assms lms_locations_inv_def by blast

subsubsection \<open>Unchanged\<close>

definition lms_unchanged_inv ::
  "('a :: {linorder, order_bot} \<Rightarrow> nat) \<Rightarrow> 
   'a list \<Rightarrow> nat list \<Rightarrow> nat list \<Rightarrow> nat list \<Rightarrow> bool"
where
  "lms_unchanged_inv \<alpha> T B SA SA' \<equiv>
    (\<forall>b \<le> \<alpha> (Max (set T)). 
       (\<forall>i. bucket_start \<alpha> T b \<le> i \<and> 
            i < B ! b \<longrightarrow>  SA' ! i = SA ! i))"

lemma lms_unchanged_invD:
  assumes "lms_unchanged_inv \<alpha> T B SA SA'"
  and     " b \<le> \<alpha> (Max (set T))" 
  and     "bucket_start \<alpha> T b \<le> i"
  and     "i < B ! b"
  shows "SA' ! i = SA ! i"
  using assms lms_unchanged_inv_def by blast

subsubsection \<open>Inserted\<close>

definition lms_inserted_inv :: 
  "nat list \<Rightarrow> nat list \<Rightarrow> nat list \<Rightarrow> nat list \<Rightarrow> bool"
where
  "lms_inserted_inv LMS SA LMSa LMSb \<equiv> 
      LMS = LMSa @ LMSb \<and> 
      set LMSa \<subseteq> set SA"

lemma lms_inserted_invD:
   "\<And>LMS SA LMSa LMSb. lms_inserted_inv LMS SA LMSa LMSb \<Longrightarrow> LMS = LMSa @ LMSb"
   "\<And>LMS SA LMSa LMSb. lms_inserted_inv LMS SA LMSa LMSb \<Longrightarrow> set LMSa \<subseteq> set SA"
  unfolding lms_inserted_inv_def by blast+

subsubsection \<open>Sorted\<close>

definition lms_sorted_inv :: "('a :: {linorder, order_bot}) list \<Rightarrow> nat list \<Rightarrow> nat list \<Rightarrow> bool"
where
"lms_sorted_inv T LMS SA \<equiv>
  (\<forall>j < length SA.
    \<forall>i < j.
      SA ! i \<in> set LMS \<and> SA ! j \<in> set LMS \<longrightarrow>
        (T ! (SA ! i) \<noteq> T ! (SA ! j) \<longrightarrow> T ! (SA ! i) < T ! (SA ! j)) \<and>
        (T ! (SA ! i) = T ! (SA ! j) \<longrightarrow>
          (\<exists>j' < length LMS. \<exists>i' < j'. LMS ! i' = SA ! j \<and> LMS ! j' = SA ! i))
  )"

lemma lms_sorted_invD:
  "\<lbrakk>lms_sorted_inv T LMS SA; j < length SA; i < j; SA ! i \<in> set LMS; SA ! j \<in> set LMS\<rbrakk> \<Longrightarrow>
   (T ! (SA ! i) \<noteq> T ! (SA ! j) \<longrightarrow> T ! (SA ! i) < T ! (SA ! j)) \<and>
   (T ! (SA ! i) = T ! (SA ! j) \<longrightarrow>
    (\<exists>j' < length LMS. \<exists>i' < j'. LMS ! i' = SA ! j \<and> LMS ! j' = SA ! i))"
  using lms_sorted_inv_def by blast

lemma lms_sorted_invD1:
  "\<lbrakk>lms_sorted_inv T LMS SA; j < length SA; i < j; 
  SA ! i \<in> set LMS; SA ! j \<in> set LMS;
    T ! (SA ! i) \<noteq> T ! (SA ! j)\<rbrakk> \<Longrightarrow>
   T ! (SA ! i) < T ! (SA ! j)"
  using lms_sorted_inv_def by blast

lemma lms_sorted_invD2:
  "\<lbrakk>lms_sorted_inv T LMS SA; j < length SA; i < j; SA ! i \<in> set LMS; SA ! j \<in> set LMS;
    T ! (SA ! i) = T ! (SA ! j)\<rbrakk> \<Longrightarrow>
   \<exists>j' < length LMS. \<exists>i' < j'. LMS ! i' = SA ! j \<and> LMS ! j' = SA ! i"
  using lms_sorted_inv_def by blast

subsection \<open>Combined Invariant\<close>

definition lms_inv ::
  "('a :: {linorder, order_bot} \<Rightarrow> nat) \<Rightarrow>
   'a list \<Rightarrow>
    nat list \<Rightarrow>
    nat list \<Rightarrow>
    nat list \<Rightarrow>
    nat list \<Rightarrow>
    nat list \<Rightarrow>
    nat list \<Rightarrow>
    bool"
where
"lms_inv \<alpha> T B LMS LMSa LMSb SA0 SA \<equiv>
  lms_distinct_inv T SA LMSb \<and>
  lms_bucket_ptr_inv \<alpha> T B SA \<and>
  lms_unknowns_inv \<alpha> T B SA \<and>
  lms_locations_inv \<alpha> T B SA \<and>
  lms_unchanged_inv \<alpha> T B SA0 SA \<and>
  lms_inserted_inv LMS SA LMSa LMSb \<and>
  lms_sorted_inv T LMS SA \<and>
  strict_mono \<alpha> \<and>
  \<alpha> (Max (set T)) < length B \<and>
  set LMS \<subseteq> {i. abs_is_lms T i} \<and>
  length SA0 = length T \<and>
  length SA = length T \<and>
  (\<forall>i < length T. SA0 ! i = length T)"

lemma lms_invD:
  "lms_inv \<alpha> T B LMS LMSa LMSb SA0 SA \<Longrightarrow> lms_distinct_inv T SA LMSb"
  "lms_inv \<alpha> T B LMS LMSa LMSb SA0 SA \<Longrightarrow> lms_bucket_ptr_inv \<alpha> T B SA"
  "lms_inv \<alpha> T B LMS LMSa LMSb SA0 SA \<Longrightarrow> lms_unknowns_inv \<alpha> T B SA"
  "lms_inv \<alpha> T B LMS LMSa LMSb SA0 SA \<Longrightarrow> lms_locations_inv \<alpha> T B SA"
  "lms_inv \<alpha> T B LMS LMSa LMSb SA0 SA \<Longrightarrow> lms_unchanged_inv \<alpha> T B SA0 SA"
  "lms_inv \<alpha> T B LMS LMSa LMSb SA0 SA \<Longrightarrow> lms_inserted_inv LMS SA LMSa LMSb"
  "lms_inv \<alpha> T B LMS LMSa LMSb SA0 SA \<Longrightarrow> lms_sorted_inv T LMS SA"
  "lms_inv \<alpha> T B LMS LMSa LMSb SA0 SA \<Longrightarrow> strict_mono \<alpha>"
  "lms_inv \<alpha> T B LMS LMSa LMSb SA0 SA \<Longrightarrow> \<alpha> (Max (set T)) < length B"
  "lms_inv \<alpha> T B LMS LMSa LMSb SA0 SA \<Longrightarrow> set LMS \<subseteq> {i. abs_is_lms T i}"
  "lms_inv \<alpha> T B LMS LMSa LMSb SA0 SA \<Longrightarrow> length SA0 = length T"
  "lms_inv \<alpha> T B LMS LMSa LMSb SA0 SA \<Longrightarrow> length SA = length T"
  "lms_inv \<alpha> T B LMS LMSa LMSb SA0 SA \<Longrightarrow> \<forall>i < length T. SA0 ! i = length T"
  unfolding lms_inv_def by blast+

lemma lms_inv_lms_helper:
  "lms_inv \<alpha> T B LMS LMSa LMSb SA0 SA \<Longrightarrow> \<forall>x \<in> set LMS. abs_is_lms T x"
  "lms_inv \<alpha> T B LMS LMSa LMSb SA0 SA \<Longrightarrow> \<forall>x \<in> set LMSa. abs_is_lms T x"
  "lms_inv \<alpha> T B LMS LMSa LMSb SA0 SA \<Longrightarrow> \<forall>x \<in> set LMSb. abs_is_lms T x"
  using lms_invD(10) lms_inserted_invD(1)[OF lms_invD(6)] by fastforce+

subsection \<open>Helpers\<close>

lemma lms_distinct_bucket_ptr_lower_bound:
  assumes "b = \<alpha> (T ! x)"
  and     "lms_distinct_inv T SA (x # LMS)"
  and     "lms_bucket_ptr_inv \<alpha> T B SA"
  and     "strict_mono \<alpha>"
  and     "\<forall>i \<in> set (x # LMS). abs_is_lms T i"
shows "lms_bucket_start \<alpha> T b < B ! b"
proof (rule ccontr)
  assume "\<not> lms_bucket_start \<alpha> T b < B ! b"
  hence "B ! b \<le> lms_bucket_start \<alpha> T b"
    by simp
  moreover
  from lms_bucket_ptr_invD[OF assms(3), of b] assms(1,4,5)
  have "B ! b + num_lms_types \<alpha> T SA b = bucket_end \<alpha> T b"
    by (simp add: abs_is_lms_imp_less_length strict_mono_leD)
  ultimately
  have "lms_bucket_start \<alpha> T b + num_lms_types \<alpha> T SA b \<ge> bucket_end \<alpha> T b"
    by linarith
  with lms_bucket_pl_size_eq_end
  have "num_lms_types \<alpha> T SA b \<ge> lms_bucket_size \<alpha> T b"
    by (metis add_le_cancel_left)
  with card_seteq[OF finite_lms_bucket cur_lms_subset_lms_bucket]
  have "cur_lms_types \<alpha> T SA b = lms_bucket \<alpha> T b"
    by (simp add: lms_bucket_size_def num_lms_types_def)
  with cur_lms_subset_SA
  have "lms_bucket \<alpha> T b \<subseteq> set SA"
    by blast
  moreover
  from assms(1,5)
  have "x \<in> lms_bucket \<alpha> T b"
    by (simp add: bucket_def abs_is_lms_imp_less_length lms_bucket_def)
  ultimately
  have "x \<in> set SA"
    by blast
  moreover
  from assms(2,5)
  have "x \<notin> set SA"
    by (simp add: abs_is_lms_imp_less_length lms_distinct_inv_def)
  ultimately
  show False
    by blast
qed

lemma lms_next_insert_at_unknown:
  assumes "b = \<alpha> (T ! x)"
  and     "k = (B ! b) - Suc 0"
  and     "lms_distinct_inv T SA (x # LMS)"
  and     "lms_bucket_ptr_inv \<alpha> T B SA"
  and     "lms_unknowns_inv \<alpha> T B SA"
  and     "strict_mono \<alpha>"
  and     "length SA = length T"
  and     "\<forall>i \<in> set (x # LMS). abs_is_lms T i"
shows "k < length SA \<and> SA ! k = length T"
proof -

  from lms_distinct_bucket_ptr_lower_bound[OF assms(1,3-4,6,8)]
  have "lms_bucket_start \<alpha> T b < B ! b"
    by assumption
   with assms(2)
  have "lms_bucket_start \<alpha> T b \<le> k" "k < B ! b"
    by linarith+
  with lms_unknowns_invD[OF assms(5), of b k] assms(1,6,8)
  have "SA ! k = length T"
    by (simp add: abs_is_lms_imp_less_length strict_mono_less_eq)
  moreover
  from `k < B ! b` lms_bucket_ptr_invD[OF assms(4), of b] assms(1,6,8)
  have "k < bucket_end \<alpha> T b"
    by (simp add: assms(7) abs_is_lms_imp_less_length strict_mono_less_eq)
  with assms(7)
  have  "k < length SA"
    by (metis bucket_end_le_length dual_order.strict_trans1)
  ultimately
  show ?thesis
    by blast
qed

lemma lms_distinct_slice:
  assumes "lms_distinct_inv T SA LMS"
  and     "lms_bucket_ptr_inv \<alpha> T B SA"
  and     "lms_locations_inv \<alpha> T B SA"
  and     "length SA = length T"
  and     "b \<le> \<alpha> (Max (set T ))"
shows "distinct (list_slice SA (B ! b) (bucket_end \<alpha> T b))"
proof -
  from assms(4)
  have "bucket_end \<alpha> T b \<le> length SA"
    by (simp add: bucket_end_le_length)

  from lms_bucket_ptr_upper_bound[OF assms(2,5)]
  have "B ! b \<le> bucket_end \<alpha> T b" .

  from lms_locations_invD[OF assms(3,5)]
  have "\<forall>i. B ! b \<le> i \<and> i < bucket_end \<alpha> T b \<longrightarrow> SA ! i \<in> lms_bucket \<alpha> T b"
    by blast
  hence "\<forall>i. B ! b \<le> i \<and> i < bucket_end \<alpha> T b \<longrightarrow> SA ! i < length T"
    by (simp add: abs_is_lms_imp_less_length lms_bucket_def)

  have "\<forall>x \<in> set (list_slice SA (B ! b) (bucket_end \<alpha> T b)). x < length T"
  proof
    fix x
    assume A: "x \<in> set (list_slice SA (B ! b) (bucket_end \<alpha> T b))"
    from in_set_conv_nth[THEN iffD1, OF A]
    obtain i where
      "i < length (list_slice SA (B ! b) (bucket_end \<alpha> T b))"
      "(list_slice SA (B ! b) (bucket_end \<alpha> T b)) ! i = x"
      by blast
    with nth_list_slice
    have "(list_slice SA (B ! b) (bucket_end \<alpha> T b)) ! i = SA ! (B ! b + i)"
      by blast
    moreover
    from `i < length (list_slice SA (B ! b) (bucket_end \<alpha> T b))`
    have "B ! b + i < bucket_end \<alpha> T b"
      by (simp add: \<open>bucket_end \<alpha> T b \<le> length SA\<close> 
                    length_list_slice)
    with `\<forall>i. B ! b \<le> i \<and> i < bucket_end \<alpha> T b \<longrightarrow> SA ! i < length T`
    have "SA ! (B ! b + i) < length T"
      by simp
    ultimately
    show "x < length T"
      using `(list_slice SA (B ! b) (bucket_end \<alpha> T b)) ! i = x` by simp
  qed

  from lms_inv_distinct_inv_helper[OF assms(1)]
  have "distinct (filter (\<lambda>x. x < length T) SA)" "distinct LMS"
       "set (filter (\<lambda>x. x < length T) SA) \<inter> set LMS = {}"
    by blast+

  have "SA = list_slice SA 0 (length SA)"
    by (simp add: list_slice_0_length)
  hence "SA = list_slice SA 0 (B ! b) @ list_slice SA (B ! b) (length SA)"
    using append_take_drop_id 
    by (simp add: list_slice.simps)
  moreover
  from list_slice_append[OF `B ! b \<le> bucket_end \<alpha> T b` `bucket_end \<alpha> T b \<le> length SA`, of SA]
  have "list_slice SA (B ! b) (length SA)
          = list_slice SA (B ! b) (bucket_end \<alpha> T b) @ list_slice SA (bucket_end \<alpha> T b) (length SA)"
    by assumption
  ultimately
  have "SA = list_slice SA 0 (B ! b) @ list_slice SA (B ! b) (bucket_end \<alpha> T b) @
             list_slice SA (bucket_end \<alpha> T b) (length SA)"
    by metis
  with `distinct (filter (\<lambda>x. x < length T) SA)`
  have "distinct (filter (\<lambda>x. x < length T) (list_slice SA (B ! b) (bucket_end \<alpha> T b)))"
    by (metis distinct_append filter_append)
  with `\<forall>x \<in> set (list_slice SA (B ! b) (bucket_end \<alpha> T b)). x < length T`
  show "distinct (list_slice SA (B ! b) (bucket_end \<alpha> T b))"
    by simp
qed

lemma lms_slice_subset_lms_bucket:
  assumes "lms_locations_inv \<alpha> T B SA"
  and     "length SA = length T"
  and     "b \<le> \<alpha> (Max (set T ))"
shows "set (list_slice SA (B ! b) (bucket_end \<alpha> T b)) \<subseteq> lms_bucket \<alpha> T b"
proof
  fix x
  assume A: "x \<in> set (list_slice SA (B ! b) (bucket_end \<alpha> T b))"
  from in_set_conv_nth[THEN iffD1, OF A]
  obtain i where
    "i < length (list_slice SA (B ! b) (bucket_end \<alpha> T b))"
    "(list_slice SA (B ! b) (bucket_end \<alpha> T b)) ! i = x"
    by blast
  with nth_list_slice
  have "(list_slice SA (B ! b) (bucket_end \<alpha> T b)) ! i = SA ! (B ! b + i)"
    by blast
  moreover
  from `i < length (list_slice SA (B ! b) (bucket_end \<alpha> T b))`
  have "B ! b + i < bucket_end \<alpha> T b"
    by (simp add: assms(2) bucket_end_le_length length_list_slice)
  moreover
  have "B ! b \<le> B ! b + i"
    by simp
  ultimately
  show "x \<in> lms_bucket \<alpha> T b"
    using \<open>list_slice SA (B ! b) (bucket_end \<alpha> T b) ! i = x\<close> assms(1,3) lms_locations_invD
    by fastforce
qed

lemma lms_val_location:
  assumes "lms_locations_inv \<alpha> T B SA"
  and     "lms_unchanged_inv \<alpha> T B SA0 SA"
  and     "strict_mono \<alpha>"
  and     "length SA = length T"
  and     "\<forall>i < length T. SA0 ! i = length T"
  and     "i < length SA"
  and     "SA ! i < length T"
shows "\<exists>b \<le> \<alpha> (Max (set T)). B ! b \<le> i \<and> i < bucket_end \<alpha> T b"
proof -
  from assms
  have "i < length T"
    by simp
  with index_in_bucket_interval_gen[OF _ assms(3)]
  obtain b where
    "b \<le> \<alpha> (Max (set T))"
    "bucket_start \<alpha> T b \<le> i"
    "i < bucket_end \<alpha> T b"
    by blast
  moreover
  have "B ! b \<le> i"
  proof (rule ccontr)
    assume "\<not>B ! b \<le> i"
    hence "i < B ! b"
      by simp
    with lms_unchanged_invD[OF assms(2) `b \<le> \<alpha> (Max (set T))` `bucket_start \<alpha> T b \<le> i`]
    have "SA ! i = SA0 ! i"
      by blast
    with assms(5) `i < length T`
    have "SA ! i = length T"
      by auto
    with assms(7)
    show False
      by auto
  qed
  ultimately
  show ?thesis
    by auto
qed

lemma lms_val_imp_abs_is_lms:
  assumes "lms_locations_inv \<alpha> T B SA"
  and     "lms_unchanged_inv \<alpha> T B SA0 SA"
  and     "strict_mono \<alpha>"
  and     "length SA = length T"
  and     "\<forall>i < length T. SA0 ! i = length T"
  and     "i < length SA"
  and     "SA ! i < length T"
shows "abs_is_lms T (SA ! i)"
proof -
  from lms_val_location[OF assms(1-7)]
  obtain b where
    "b \<le> \<alpha> (Max (set T))"
    "B ! b \<le> i"
    "i < bucket_end \<alpha> T b"
    by blast
  with lms_locations_invD[OF assms(1)]
  have "SA ! i \<in> lms_bucket \<alpha> T b"
    by blast
  then show "abs_is_lms T (SA ! i)"
    using lms_bucket_def by blast
qed

lemma lms_lms_prefix_sorted:
  assumes "lms_bucket_ptr_inv \<alpha> T B SA"
  and     "lms_locations_inv \<alpha> T B SA"
  and     "lms_unchanged_inv \<alpha> T B SA0 SA"
  and     "strict_mono \<alpha>"
  and     "length SA = length T"
  and     "\<forall>i < length T. SA0 ! i = length T"
  and     "set LMS = {i. abs_is_lms T i}"
shows "ordlistns.sorted (map (lms_prefix T) (filter (\<lambda>x. x < length T) SA))"
proof (intro sorted_wrt_mapI)
  fix i j
  let ?fs = "filter (\<lambda>x. x < length T) SA"
  let ?goal = "list_less_eq_ns (lms_prefix T (?fs ! i)) (lms_prefix T (?fs ! j))"
  assume "i < j" "j < length ?fs"

  from filter_nth_relative_2[OF `j < length ?fs` `i < j`]
  obtain i' j' where
    "j' < length SA"
    "i' < j'"
    "?fs ! j = SA ! j'"
    "?fs ! i = SA ! i'"
    by blast
  hence "i' < length SA"
    by linarith

  have "SA ! i' < length T"
    by (metis \<open>?fs ! i = SA ! i'\<close> \<open>i < j\<close> \<open>j < length ?fs\<close> filter_set member_filter
              nth_mem order.strict_trans)
  with lms_val_location[OF assms(2-6) `i' < length SA`]
  obtain b where
    "b \<le> \<alpha> (Max (set T))"
    "B ! b \<le> i'"
    "i' < bucket_end \<alpha> T b"
    by blast
  with lms_locations_invD[OF assms(2)]
  have "SA ! i' \<in> lms_bucket \<alpha> T b"
    by blast
  hence "\<alpha> (T ! (SA ! i')) = b" "abs_is_lms T (SA ! i')"
    by (simp add: bucket_def lms_bucket_def)+

  from lms_lms_prefix[OF `abs_is_lms T (SA ! i')`] `?fs ! i = SA ! i'`
  have S1: "lms_prefix T (?fs ! i) = [T ! (SA ! i')]"
    by simp

  have "SA ! j' < length T"
    using \<open>?fs ! j = SA ! j'\<close> \<open>j < length ?fs\<close> nth_mem by fastforce
  with lms_val_location[OF assms(2-6) `j' < length SA`]
  obtain b' where
    "b' \<le> \<alpha> (Max (set T))"
    "B ! b' \<le> j'"
    "j' < bucket_end \<alpha> T b'"
    by blast
  with lms_locations_invD[OF assms(2)]
  have "SA ! j' \<in> lms_bucket \<alpha> T b'"
    by blast
  hence "\<alpha> (T ! (SA ! j')) = b'" "abs_is_lms T (SA ! j')"
    by (simp add: bucket_def lms_bucket_def)+

  from lms_lms_prefix[OF `abs_is_lms T (SA ! j')`] `?fs ! j = SA ! j'`
  have S2: "lms_prefix T (?fs ! j) = [T ! (SA ! j')]"
    by simp

  have "b \<le> b'"
  proof (rule ccontr)
    assume "\<not>b \<le> b'"
    hence "b' < b"
      by simp
    hence "bucket_end \<alpha> T b' \<le> bucket_start \<alpha> T b"
      by (simp add: less_bucket_end_le_start)
    hence "bucket_end \<alpha> T b' \<le> lms_bucket_start \<alpha> T b"
      by (metis l_bucket_end_def l_bucket_end_le_lms_bucket_start le_add1 le_trans)
    with lms_bucket_ptr_lower_bound[OF assms(1) `b \<le> \<alpha> (Max (set T))`]
    have "bucket_end \<alpha> T b' \<le> B ! b"
      by linarith
    with `j' < bucket_end \<alpha> T b'` `B ! b \<le> i'` `i' < j'`
    show False
      by linarith
  qed
  moreover
  have "b < b' \<Longrightarrow> ?goal"
  proof -
    assume "b < b'"
    with `\<alpha> (T ! (SA ! i')) = b` `\<alpha> (T ! (SA ! j')) = b'` assms(4)
    have "T ! (SA ! i') < T ! (SA ! j')"
      using strict_mono_less by blast
    with S1 S2
    show ?goal
      by (simp add: list_less_eq_ns_cons)
  qed
  moreover
  have "b = b' \<Longrightarrow> ?goal"
  proof -
    assume "b = b'"
    with `\<alpha> (T ! (SA ! i')) = b` `\<alpha> (T ! (SA ! j')) = b'` assms(4)
    have "T ! (SA ! i') = T ! (SA ! j')"
      by (meson strict_mono_eq)
    with S1 S2
    show ?goal
      by simp
  qed
  ultimately
  show ?goal
    using less_le by blast
qed

lemma lms_suffix_sorted:
  assumes "lms_bucket_ptr_inv \<alpha> T B SA"
  and     "lms_locations_inv \<alpha> T B SA"
  and     "lms_unchanged_inv \<alpha> T B SA0 SA"
  and     "lms_sorted_inv T LMS SA"
  and     "strict_mono \<alpha>"
  and     "length SA = length T"
  and     "\<forall>i < length T. SA0 ! i = length T"
  and     "set LMS = {i. abs_is_lms T i}"
  and     "ordlistns.sorted (map (suffix T) (rev LMS))"
shows "ordlistns.sorted (map (suffix T) (filter (\<lambda>x. x < length T) SA))"
proof (intro sorted_wrt_mapI)
  fix i j
  let ?fs = "filter (\<lambda>x. x < length T) SA"
  let ?goal = "list_less_eq_ns (suffix T (?fs ! i)) (suffix T (?fs ! j))"
  assume "i < j" "j < length ?fs"

  from filter_nth_relative_2[OF `j < length ?fs` `i < j`]
  obtain i' j' where
    "j' < length SA"
    "i' < j'"
    "?fs ! j = SA ! j'"
    "?fs ! i = SA ! i'"
    by blast
  hence "i' < length SA"
    by linarith

  have "SA ! i' < length T"
    by (metis \<open>?fs ! i = SA ! i'\<close> \<open>i < j\<close> \<open>j < length ?fs\<close> filter_set member_filter
              nth_mem order.strict_trans)
  with lms_val_location[OF assms(2,3,5-7) `i' < length SA`]
  obtain b where
    "b \<le> \<alpha> (Max (set T))"
    "B ! b \<le> i'"
    "i' < bucket_end \<alpha> T b"
    by blast
  with lms_locations_invD[OF assms(2)]
  have "SA ! i' \<in> lms_bucket \<alpha> T b"
    by blast
  hence "\<alpha> (T ! (SA ! i')) = b" "abs_is_lms T (SA ! i')"
    by (simp add: bucket_def lms_bucket_def)+
  hence "SA ! i' \<in> set LMS"
    using assms(8)
    by blast

  have "SA ! j' < length T"
    using \<open>?fs ! j = SA ! j'\<close> \<open>j < length ?fs\<close> nth_mem by fastforce
  with lms_val_location[OF assms(2,3,5-7) `j' < length SA`]
  obtain b' where
    "b' \<le> \<alpha> (Max (set T))"
    "B ! b' \<le> j'"
    "j' < bucket_end \<alpha> T b'"
    by blast
  with lms_locations_invD[OF assms(2)]
  have "SA ! j' \<in> lms_bucket \<alpha> T b'"
    by blast
  hence "\<alpha> (T ! (SA ! j')) = b'" "abs_is_lms T (SA ! j')"
    by (simp add: bucket_def lms_bucket_def)+
  hence "SA ! j' \<in> set LMS"
    using assms(8)
    by blast

  have "b \<le> b'"
  proof (rule ccontr)
    assume "\<not>b \<le> b'"
    hence "b' < b"
      by simp
    hence "bucket_end \<alpha> T b' \<le> bucket_start \<alpha> T b"
      by (simp add: less_bucket_end_le_start)
    hence "bucket_end \<alpha> T b' \<le> lms_bucket_start \<alpha> T b"
      by (metis l_bucket_end_def l_bucket_end_le_lms_bucket_start le_add1 le_trans)
    with lms_bucket_ptr_lower_bound[OF assms(1) `b \<le> \<alpha> (Max (set T))`]
    have "bucket_end \<alpha> T b' \<le> B ! b"
      by linarith
    with `j' < bucket_end \<alpha> T b'` `B ! b \<le> i'` `i' < j'`
    show False
      by linarith
  qed
  moreover
  have "b < b' \<Longrightarrow> ?goal"
  proof -
    assume "b < b'"
    with `\<alpha> (T ! (SA ! i')) = b` `\<alpha> (T ! (SA ! j')) = b'` assms(5)
    have "T ! (SA ! i') < T ! (SA ! j')"
      using strict_mono_less by blast
    with `?fs ! i = SA ! i'` `?fs ! j = SA ! j'` `SA ! i' < length T` `SA ! j' < length T`
    show ?goal
      by (metis list_less_ns_cons_diff ordlistns.less_imp_le suffix_cons_ex)
  qed
  moreover
  have "b = b' \<Longrightarrow> ?goal"
  proof -
    assume "b = b'"
    with `\<alpha> (T ! (SA ! i')) = b` `\<alpha> (T ! (SA ! j')) = b'` assms(5)
    have "T ! (SA ! i') = T ! (SA ! j')"
      by (meson strict_mono_eq)
    with lms_sorted_invD2[OF assms(4) `j' < length SA` `i' < j'` `SA ! i' \<in> set LMS`
                             `SA ! j' \<in> set LMS`]
    obtain m n where
      "n < length LMS"
      "m < n"
      "LMS ! m = SA ! j'"
      "LMS ! n = SA ! i'"
      by blast
    hence "rev LMS ! (length LMS - Suc m) = SA ! j'" "rev LMS ! (length LMS - Suc n) = SA ! i'"
      by (metis length_rev order.strict_trans rev_nth rev_rev_ident)+
    moreover
    from  `m < n` `n < length LMS`
    have "length LMS - Suc n \<le> length LMS - Suc m"
      by linarith
    moreover
    have "length LMS - Suc m < length (rev LMS)"
      using \<open>n < length LMS\<close> by auto
    ultimately
    have "list_less_eq_ns (suffix T (SA ! i')) (suffix T (SA ! j'))"
      using ordlistns.sorted_nth_mono[OF assms(9)]
      by fastforce
    with `?fs ! i = SA ! i'` `?fs ! j = SA ! j'`
    show ?goal
      by simp
  qed
  ultimately
  show ?goal
    using less_le by blast
qed

lemma next_index_outside:
  assumes "b = \<alpha> (T ! x)"
  and     "k = B ! b - Suc 0"
  and     "lms_distinct_inv T SA (x # LMS)"
  and     "lms_bucket_ptr_inv \<alpha> T B SA"
  and     "strict_mono \<alpha>"
  and     "\<forall>a \<in> set (x # LMS). abs_is_lms T a"
  and     "b' \<le> \<alpha> (Max (set T))"
  and     "b \<noteq> b'"
shows "k < bucket_start \<alpha> T b' \<or> bucket_end \<alpha> T b' \<le> k"
proof -

  from lms_distinct_bucket_ptr_lower_bound[OF assms(1,3-6)]
  have "lms_bucket_start \<alpha> T b < B ! b" .
  hence "k < B ! b"
    using assms(2) by linarith

  from `lms_bucket_start \<alpha> T b < B ! b`
  have "lms_bucket_start \<alpha> T b \<le> k"
    using assms(2) by linarith

  have "x < length T"
    by (simp add: assms(6) abs_is_lms_imp_less_length)
  hence "b \<le> \<alpha> (Max (set T))"
    by (simp add: assms(1,5) strict_mono_leD)

  from assms(8)
  have "b < b' \<or> b' < b"
    by linarith
  moreover
  have "b < b' \<Longrightarrow> k < bucket_start \<alpha> T b'"
  proof -
    assume "b < b'"
    hence "bucket_end \<alpha> T b \<le> bucket_start \<alpha> T b'"
      by (simp add: less_bucket_end_le_start)
    with lms_bucket_ptr_upper_bound[OF assms(4) `b \<le> \<alpha> (Max (set T))`]
    have "B ! b \<le> bucket_start \<alpha> T b'"
      by linarith
    with `k < B ! b`
    show ?thesis
      by linarith
  qed
  moreover
  have "b' < b \<Longrightarrow> bucket_end \<alpha> T b' \<le> k"
  proof -
    assume "b' < b"
    hence "bucket_end \<alpha> T b' \<le> bucket_start \<alpha> T b"
      by (simp add: less_bucket_end_le_start)
    hence "bucket_end \<alpha> T b' \<le> lms_bucket_start \<alpha> T b"
      by (metis l_bucket_end_def l_bucket_end_le_lms_bucket_start le_add1 le_trans)
    with `lms_bucket_start \<alpha> T b \<le> k`
    show ?thesis
      using le_trans by blast
  qed
  ultimately show ?thesis
    by blast
qed

subsection \<open>Establishment and Maintenance Steps\<close>

subsubsection \<open>Distinctness\<close>

lemma lms_distinct_inv_established:
  assumes "distinct LMS"
  and     "\<forall>i < length SA. SA ! i = length T"
shows "lms_distinct_inv T SA LMS"
proof -
  from assms(2)
  have "filter (\<lambda>x. x < length T) SA = []"
    by (metis filter_False in_set_conv_nth nat_neq_iff)
  then show ?thesis
  unfolding lms_distinct_inv_def
  using distinct_append assms(1)
  by simp
qed

lemma lms_distinct_inv_maintained_step:
  assumes "lms_distinct_inv T SA (x # LMS)"
shows "lms_distinct_inv T (SA[k := x]) LMS"
  unfolding lms_distinct_inv_def
proof(intro distinct_conv_nth[THEN iffD2] allI impI)
  let ?xs = "filter (\<lambda>x. x < length T) SA" and
      ?ys = "filter (\<lambda>x. x < length T) (SA[k := x])"
  fix i j
  assume "i \<noteq> j" "i < length (filter (\<lambda>x. x < length T) (SA[k := x]) @ LMS)"
         "j < length (filter (\<lambda>x. x < length T) (SA[k := x]) @ LMS)"
  hence "i < length ?ys + length LMS"  "j < length ?ys + length LMS"
    by simp_all

  let ?goal = "(?ys @ LMS) ! i \<noteq> (?ys @ LMS) ! j"

  from assms(1) distinct_append
  have "distinct LMS" "distinct ?xs" "x \<notin> set ?xs" "x \<notin> set LMS" "set ?xs \<inter> set LMS = {}"
    by (simp add: lms_distinct_inv_def)+

  from `distinct LMS` `i < length ?ys + length LMS` `j < length ?ys + length LMS` `i \<noteq> j`
  have R1: "\<lbrakk>length ?ys \<le> i; length ?ys \<le> j\<rbrakk> \<Longrightarrow> ?goal"
    by (metis le_Suc_ex nat_add_left_cancel_less nth_append_length_plus nth_eq_iff_index_eq)

  have "set ?ys \<subseteq> {x} \<union> set ?xs"
    by (meson filter_nth_update_subset)

  have R2:
    "\<And>i j. \<lbrakk>i < length ?ys; length ?ys \<le> j; j < length ?ys + length LMS\<rbrakk> \<Longrightarrow>
            (?ys @ LMS) ! i \<noteq> (?ys @ LMS) ! j"
  proof -
    fix i j
    assume "i < length ?ys" "length ?ys \<le> j" "j < length ?ys + length LMS"
    hence "?ys ! i \<in> {x} \<union> set ?xs"
      using `set ?ys \<subseteq> {x} \<union> set ?xs` nth_mem by blast
    hence "(?ys @ LMS) ! i \<in> {x} \<union> set ?xs"
      by (simp add: \<open>i < length ?ys\<close> nth_append)
    moreover
    from `length ?ys \<le> j` `j < length ?ys + length LMS`
    have "(?ys @ LMS) ! j \<in> set LMS"
      by (metis add.commute in_set_conv_nth leD less_diff_conv2 nth_append)
    moreover
    from `set ?xs \<inter> set LMS = {}` `x \<notin> set LMS`
    have "({x} \<union> set ?xs) \<inter> set LMS = {}"
      by blast
    ultimately
    show "(?ys @ LMS) ! i \<noteq> (?ys @ LMS) ! j"
      by (metis disjoint_iff_not_equal)
  qed

  have R3: "\<lbrakk>i < length ?ys; j < length ?ys\<rbrakk> \<Longrightarrow> ?goal"
  proof -
    assume "i < length ?ys" "j < length ?ys"
    with filter_nth_relative_neq_2[OF _ _ `i \<noteq> j`]
    obtain i' j' where
      "i' < length (SA[k := x])"
      "j' < length (SA[k := x])"
      "(SA[k := x]) ! i' = ?ys ! i"
      "(SA[k := x]) ! j' = ?ys ! j"
      "i' \<noteq> j'"
      by blast

    have "?ys ! i < length T"
      using \<open>i < length ?ys\<close> nth_mem by fastforce
    hence "(SA[k := x]) ! i' < length T"
      using `(SA[k := x]) ! i' = ?ys ! i` by simp

    have "?ys ! j < length T"
      using \<open>j < length ?ys\<close> nth_mem by fastforce
    hence "(SA[k := x]) ! j' < length T"
      using `(SA[k := x]) ! j' = ?ys ! j` by simp

    have R4:
      "\<And>i j. \<lbrakk>i \<noteq> k; j = k; i < length (SA[k := x]); j < length (SA[k := x]);
              (SA[k := x]) ! i < length T\<rbrakk> \<Longrightarrow>
              (SA[k := x]) ! i \<noteq> (SA[k := x]) ! j"
    proof -
      fix i j
      assume "i \<noteq> k" "j = k" "i < length (SA[k := x])" "j < length (SA[k := x])"
             "(SA[k := x]) ! i < length T"

      from `j = k` `j < length (SA[k := x])`
      have "(SA[k := x]) ! j = x"
        by simp
      moreover
      from `i \<noteq> k` `i < length (SA[k := x])`
      have "(SA[k := x]) ! i = SA ! i"
        by simp
      with `(SA[k := x]) ! i < length T`
      have "SA ! i < length T"
        by simp
      with filter_nth_1[of i SA "\<lambda>x. x < length T"] `i < length (SA[k := x])`
      obtain i' where
        "i' < length ?xs"
        "?xs ! i' = SA ! i"
        by auto
      with `(SA[k := x]) ! i = SA ! i`
      have "(SA[k := x]) ! i \<in> set ?xs"
        using nth_mem by fastforce
      ultimately
      show "(SA[k := x]) ! i \<noteq> (SA[k := x]) ! j"
        using `x \<notin> set ?xs` by auto
    qed

    have "\<lbrakk>i' \<noteq> k; j' \<noteq> k\<rbrakk> \<Longrightarrow> (SA[k := x]) ! i' \<noteq> (SA[k := x]) ! j'"
    proof -
      assume "i' \<noteq> k" "j' \<noteq> k"
      with `(SA[k := x]) ! i' = ?ys ! i` `(SA[k := x]) ! j' = ?ys ! j`
      have "?ys ! i = SA ! i'" "?ys ! j = SA ! j'"
        by auto
      with `?ys ! i < length T` `?ys ! j < length T` `i' < length (SA[k := x])`
           `j' < length (SA[k := x])`
           filter_nth_relative_neq_1[of i' SA "\<lambda>x. x < length T" j', OF _ _ _ _ `i' \<noteq> j'`]
      obtain i'' j'' where
        "i'' < length ?xs"
        "j'' < length ?xs"
        "?xs ! i'' = SA ! i'"
        "?xs ! j'' = SA ! j'"
        "i'' \<noteq> j''"
        by auto
      with `distinct ?xs`
      have "SA ! i' \<noteq> SA ! j'"
        by (metis distinct_Ex1 in_set_conv_nth)
      then show ?thesis
        using \<open>SA[k := x] ! i' = ?ys ! i\<close> \<open>?ys ! i = SA ! i'\<close> \<open>j' \<noteq> k\<close> by auto
    qed
    moreover
    from `i' \<noteq> j'`
    have "\<lbrakk>i' = k; j' = k\<rbrakk> \<Longrightarrow> False"
      by blast
    ultimately
    have "(SA[k := x]) ! i' \<noteq> (SA[k := x]) ! j'"
      using R4[of i' j', OF _ _ `i' < length (SA[k := x])` `j' < length (SA[k := x])`
                `(SA[k := x]) ! i' < length T`]
            R4[of j' i', OF _ _ `j' < length (SA[k := x])` `i' < length (SA[k := x])`
                `(SA[k := x]) ! j' < length T`]
      by metis
    with `(SA[k := x]) ! i' = ?ys ! i` `i < length ?ys`
         `(SA[k := x]) ! j' = ?ys ! j` `j < length ?ys`
    show ?goal
      by (simp add: nth_append)
  qed

  from R1 R2[of i j, OF _ _ `j < length ?ys + length LMS`]
       R2[of j i, OF _ _ `i < length ?ys + length LMS`] R3
  show ?goal
    by presburger
qed

lemma lms_distinct_inv_maintained:
  assumes "lms_distinct_inv T SA LMS"
  shows "lms_distinct_inv T (abs_bucket_insert \<alpha> T B SA LMS) []"
  using assms
proof (induct rule: abs_bucket_insert.induct[of _ \<alpha> T B SA LMS])
  case (1 \<alpha> T uu SA)
  then show ?case
    by simp
next
  case (2 \<alpha> T B SA x xs)
  note IH = this
  let ?b = "\<alpha> (T ! x)"
  let ?k = "B ! ?b - Suc 0"
  from IH(1)[OF  _ _ _ _ lms_distinct_inv_maintained_step[OF IH(2), of ?k], of ?b ?k "B[?b := ?k]"]
  show ?case
    by (metis (full_types) One_nat_def abs_bucket_insert.simps(2))
qed

lemma abs_bucket_insert_lms_distinct_inv:
  assumes "distinct LMS"
  and     "\<forall>i < length SA. SA ! i = length T"
shows "lms_distinct_inv T (abs_bucket_insert \<alpha> T B SA LMS) []"
  using assms lms_distinct_inv_maintained lms_distinct_inv_established
  by blast

subsubsection \<open>Bucket Ptr\<close>

lemma lms_bucket_ptr_inv_established:
  assumes "lms_bucket_init \<alpha> T B"
  and     "\<forall>i < length SA. SA ! i = length T"
shows "lms_bucket_ptr_inv \<alpha> T B SA"
  unfolding lms_bucket_ptr_inv_def
proof (intro allI impI)
  fix b
  assume "b \<le> \<alpha> (Max (set T))"
  with lms_bucket_initD[OF assms(1)]
  have "B ! b = bucket_end \<alpha> T b"
    by simp
  moreover
  from assms(2)
  have "\<forall>i \<in> set SA. \<not>abs_is_lms T i"
    by (metis in_set_conv_nth abs_is_lms_imp_less_length less_not_refl2)
  hence "cur_lms_types \<alpha> T SA b = {}"
    by (simp add: cur_lms_types_def lms_bucket_def)
  hence "num_lms_types \<alpha> T SA b = 0"
    by (simp add: num_lms_types_def)
  ultimately
  show "B ! b + num_lms_types \<alpha> T SA b = bucket_end \<alpha> T b"
    by simp
qed

lemma lms_bucket_ptr_inv_maintained_step:
  assumes "b = \<alpha> (T ! x)"
  and     "k = B ! b - Suc 0"
  and     "lms_distinct_inv T SA (x # LMS)"
  and     "lms_bucket_ptr_inv \<alpha> T B SA"
  and     "lms_unknowns_inv \<alpha> T B SA"
  and     "strict_mono \<alpha>"
  and     "\<alpha> (Max (set T)) < length B"
  and     "length SA = length T"
  and     "\<forall>a \<in> set (x # LMS). abs_is_lms T a"
shows "lms_bucket_ptr_inv \<alpha> T (B[b := k]) (SA[k := x])"
  unfolding lms_bucket_ptr_inv_def
proof (intro allI impI)
  fix b'
  assume "b' \<le> \<alpha> (Max (set T))"

  let ?goal = "B[b := k] ! b' + num_lms_types \<alpha> T (SA[k := x]) b' = bucket_end \<alpha> T b'"

  from assms(1,9)
  have "x \<in> lms_bucket \<alpha> T b"
    by (simp add: bucket_def abs_is_lms_imp_less_length lms_bucket_def)

  from lms_next_insert_at_unknown[OF assms(1-6,8,9)]
  have "k < length SA" "SA ! k = length T"
    by blast+

  have "b' \<noteq> b \<Longrightarrow> ?goal"
  proof -
    assume "b' \<noteq> b"
    with `x \<in> lms_bucket \<alpha> T b`
    have "x \<notin> lms_bucket \<alpha> T b'"
      by (simp add: bucket_def lms_bucket_def)
    with cur_lms_subset_lms_bucket
    have "x \<notin> cur_lms_types \<alpha> T SA b'"
      by blast

    have "cur_lms_types \<alpha> T (SA[k := x]) b' = cur_lms_types \<alpha> T SA b'"
      unfolding cur_lms_types_def
    proof (intro equalityI subsetI)
      fix y
      assume "y \<in> {i |i. i \<in> set (SA[k := x]) \<and> i \<in> lms_bucket \<alpha> T b'}"
      hence "y \<in> set (SA[k := x])" "y \<in> lms_bucket \<alpha> T b'"
        by simp_all
      with `x \<notin> lms_bucket \<alpha> T b'`
      have "y \<in> set SA"
        by (metis in_set_conv_nth length_list_update nth_list_update_eq nth_list_update_neq)
      then show "y \<in> {i |i. i \<in> set SA \<and> i \<in> lms_bucket \<alpha> T b'}"
        by (simp add: \<open>y \<in> lms_bucket \<alpha> T b'\<close>)
    next
      fix y
      assume "y \<in> {i |i. i \<in> set SA \<and> i \<in> lms_bucket \<alpha> T b'}"
      hence "y \<in> set SA" "y \<in> lms_bucket \<alpha> T b'"
        by simp_all
      with `x \<notin> lms_bucket \<alpha> T b'` `SA ! k = length T`
      have "y \<in> set (SA[k := x])"
        using in_set_list_update abs_is_lms_imp_less_length lms_bucket_def by fastforce
      then show "y \<in> {i |i. i \<in> set (SA[k := x]) \<and> i \<in> lms_bucket \<alpha> T b'}"
        using \<open>y \<in> lms_bucket \<alpha> T b'\<close> by blast
    qed
    hence "num_lms_types \<alpha> T (SA[k := x]) b' = num_lms_types \<alpha> T SA b'"
      by (simp add: num_lms_types_def)
    with lms_bucket_ptr_invD[OF assms(4) `b' \<le> \<alpha> (Max (set T))`] `b' \<noteq> b`
    show ?thesis
      by simp
  qed
  moreover
  have "b' = b \<Longrightarrow> ?goal"
  proof -
    assume "b' = b"
    with `b' \<le> \<alpha> (Max (set T))`
    have "b \<le> \<alpha> (Max (set T))"
      by simp

    from assms(3,9)
    have "x \<notin> set SA"
      by (simp add: abs_is_lms_imp_less_length lms_distinct_inv_def)

    from `k < length SA`
    have "x \<in> set (SA[k := x])"
      by (simp add: set_update_memI)

    have "b < length B"
      using \<open>b \<le> \<alpha> (Max (set T))\<close> assms(7) dual_order.strict_trans2 by blast
    hence "B[b := k] ! b = k"
      by simp

    have "finite (cur_lms_types \<alpha> T SA b)"
      by (meson List.finite_set cur_lms_subset_SA finite_subset)
    moreover
    from `x \<notin> set SA`
    have "cur_lms_types \<alpha> T SA b - {x} = cur_lms_types \<alpha> T SA b"
      using cur_lms_subset_SA by fastforce
    moreover
    have "insert x (cur_lms_types \<alpha> T SA b) = cur_lms_types \<alpha> T (SA[k := x]) b"
      unfolding cur_lms_types_def
    proof (intro equalityI subsetI)
      fix y
      assume "y \<in> insert x {i |i. i \<in> set SA \<and> i \<in> lms_bucket \<alpha> T b}"
      hence "y = x \<or> y \<in> set SA \<and> y \<in> lms_bucket \<alpha> T b"
        by blast
      with \<open>SA ! k = length T\<close> \<open>x \<in> lms_bucket \<alpha> T b\<close> \<open>x \<in> set (SA[k := x])\<close>
      have "y \<in> set (SA[k := x]) \<and> y \<in> lms_bucket \<alpha> T b"
        by (metis (no_types, lifting) in_set_list_update abs_is_lms_imp_less_length less_irrefl_nat
                                      lms_bucket_def mem_Collect_eq)
      then show "y \<in> {i |i. i \<in> set (SA[k := x]) \<and> i \<in> lms_bucket \<alpha> T b}"
        by blast
    next
      fix y
      assume "y \<in> {i |i. i \<in> set (SA[k := x]) \<and> i \<in> lms_bucket \<alpha> T b}"
      hence "y \<in> set (SA[k := x])" "y \<in> lms_bucket \<alpha> T b"
        by simp_all
      moreover
      have "y \<in> set SA \<Longrightarrow> y \<in> insert x {i |i. i \<in> set SA \<and> i \<in> lms_bucket \<alpha> T b}"
        using calculation(2) by blast
      moreover
      from \<open>k < length SA \<and> SA ! k = length T\<close>
      have "y \<notin> set SA \<Longrightarrow> y \<in> insert x {i |i. i \<in> set SA \<and> i \<in> lms_bucket \<alpha> T b}"
        by (metis (no_types, lifting) calculation(1) in_set_conv_nth insert_iff length_list_update
                                      nth_list_update)
      ultimately show "y \<in> insert x {i |i. i \<in> set SA \<and> i \<in> lms_bucket \<alpha> T b}"
        by blast
    qed
    ultimately
    have "num_lms_types \<alpha> T (SA[k := x]) b = Suc (num_lms_types \<alpha> T SA b)"
      by (metis num_lms_types_def card.insert_remove)
    with `b' = b` `B[b := k] ! b = k` assms(2)
    have "B[b := k] ! b' + num_lms_types \<alpha> T (SA[k := x]) b'
            = B ! b - Suc 0 + Suc (num_lms_types \<alpha> T SA b)"
      by simp
    hence "B[b := k] ! b' + num_lms_types \<alpha> T (SA[k := x]) b' = B ! b + num_lms_types \<alpha> T SA b"
      using add_Suc_shift assms less_nat_zero_code lms_distinct_bucket_ptr_lower_bound
            neq0_conv
      by fastforce
    with `b' = b`
    have "B[b := k] ! b' + num_lms_types \<alpha> T (SA[k := x]) b' = B ! b' + num_lms_types \<alpha> T SA b'"
      by simp
    with lms_bucket_ptr_invD[OF assms(4) `b' \<le> \<alpha> (Max (set T))`]
    show ?thesis
      by simp
  qed
  ultimately
  show ?goal
    by blast
qed

subsubsection \<open>Unknowns\<close>

lemma lms_unknowns_inv_established:
  assumes "lms_bucket_init \<alpha> T B"
  and     "\<forall>i < length SA. SA ! i = length T"
  and     "length SA = length T"
shows "lms_unknowns_inv \<alpha> T B SA"
  unfolding lms_unknowns_inv_def
proof (intro allI impI; elim conjE)
  fix b i
  assume "b \<le> \<alpha> (Max (set T))" "lms_bucket_start \<alpha> T b \<le> i" "i < B ! b"
  with lms_bucket_initD[OF assms(1)]
  have "B ! b = bucket_end \<alpha> T b"
    by simp
  with `i < B ! b`
  have "i < length T"
    by (simp add: bucket_end_le_length less_le_trans)
  with assms(3)
  have "i < length SA"
    by simp
  with assms(2)
  show "SA ! i = length T"
    by simp
qed

lemma lms_unknowns_inv_maintained_step:
  assumes "b = \<alpha> (T ! x)"
  and     "k = B ! b - Suc 0"
  and     "lms_distinct_inv T SA (x # LMS)"
  and     "lms_bucket_ptr_inv \<alpha> T B SA"
  and     "lms_unknowns_inv \<alpha> T B SA"
  and     "strict_mono \<alpha>"
  and     "\<alpha> (Max (set T)) < length B"
  and     "\<forall>a \<in> set (x # LMS). abs_is_lms T a"
shows "lms_unknowns_inv \<alpha> T (B[b := k]) (SA[k := x])"
  unfolding lms_unknowns_inv_def
proof (intro allI impI; elim conjE)
  fix b' i
  assume "b' \<le> \<alpha> (Max (set T))" "lms_bucket_start \<alpha> T b' \<le> i" "i < B[b := k] ! b'"

  let ?goal = "SA[k := x] ! i = length T"

  have "b' \<noteq> b \<Longrightarrow> ?goal"
  proof -
    assume "b' \<noteq> b"
    with `i < B[b := k] ! b'`
    have "i < B ! b'"
      by simp
    with lms_unknowns_invD[OF assms(5) `b' \<le> \<alpha> (Max (set T))` `lms_bucket_start \<alpha> T b' \<le> i`]
    have "SA ! i = length T"
      by simp

    from `b' \<noteq> b`
    have "b' < b \<or> b < b'"
      by auto
    then show ?thesis
    proof
      assume "b' < b"
      from lms_distinct_bucket_ptr_lower_bound[OF assms(1,3,4,6,8)]
      have "lms_bucket_start \<alpha> T b < B ! b" .
      hence "bucket_start \<alpha> T b < B ! b"
        by (metis dual_order.strict_trans2 l_bucket_end_def l_bucket_end_le_lms_bucket_start le_add1)
      moreover
      from lms_bucket_ptr_upper_bound[OF assms(4) `b' \<le> \<alpha> (Max (set T))`]
      have "B ! b' \<le> bucket_end \<alpha> T b'" .
      ultimately
      have "B ! b' < B ! b"
        by (meson \<open>b' < b\<close> dual_order.strict_trans2 less_bucket_end_le_start)
      hence "i \<noteq> k"
        using assms(2,3) `i < B ! b'`
        by linarith
      with `SA ! i = length T`
      show ?thesis
        by auto
    next
      assume "b < b'"
      from `lms_bucket_start \<alpha> T b' \<le> i`
      have "bucket_start \<alpha> T b' \<le> i"
        by (metis l_bucket_end_def l_bucket_end_le_lms_bucket_start le_add1 le_trans)
      moreover
      from lms_bucket_ptr_upper_bound[OF assms(4), of b] assms(7)
      have "B ! b \<le> bucket_end \<alpha> T b"
        using \<open>b < b'\<close> \<open>b' \<le> \<alpha> (Max (set T))\<close> by linarith
      hence "k < bucket_end \<alpha> T b"
        using assms lms_distinct_bucket_ptr_lower_bound by fastforce
      ultimately
      have "i \<noteq> k"
        by (meson \<open>b < b'\<close> leD le_trans less_bucket_end_le_start)
      with `SA ! i = length T`
      show ?thesis
        by auto
    qed
  qed
  moreover
  have "b' = b \<Longrightarrow> ?goal"
  proof -
    assume "b' = b"
    with `b' \<le> \<alpha> (Max (set T))` `lms_bucket_start \<alpha> T b' \<le> i` `i < B[b := k] ! b'`
    have "b \<le> \<alpha> (Max (set T))" "lms_bucket_start \<alpha> T b \<le> i" "i < B[b := k] ! b"
      by simp_all
    hence "i < B ! b - Suc 0"
      using assms by auto
    with lms_unknowns_invD[OF assms(5) `b \<le> \<alpha> (Max (set T))` `lms_bucket_start \<alpha> T b \<le> i`]
    have "SA ! i = length T"
      by linarith
    with `i < B ! b - Suc 0` assms(2)
    show ?thesis
      by simp
  qed
  ultimately
  show ?goal
    by blast
qed

subsubsection \<open>Locations\<close>

lemma lms_locations_inv_established:
  assumes "lms_bucket_init \<alpha> T B"
shows "lms_locations_inv \<alpha> T B SA"
  unfolding lms_locations_inv_def
proof (intro allI impI; elim conjE)
  fix b i
  assume "b \<le> \<alpha> (Max (set T))" "B ! b \<le> i" "i < bucket_end \<alpha> T b"
  with lms_bucket_initD[OF assms(1), of b]
  have False
    by linarith
  then show "SA ! i \<in> lms_bucket \<alpha> T b"
    by blast
qed

lemma lms_locations_inv_maintained_step:
  assumes "b = \<alpha> (T ! x)"
  and     "k = (B ! b) - Suc 0"
  and     "lms_distinct_inv T SA (x # LMS)"
  and     "lms_bucket_ptr_inv \<alpha> T B SA"
  and     "lms_locations_inv \<alpha> T B SA"
  and     "strict_mono \<alpha>"
  and     "\<alpha> (Max (set T)) < length B"
  and     "length SA = length T"
  and     "\<forall>a \<in> set (x # LMS). abs_is_lms T a"
shows "lms_locations_inv \<alpha> T (B[b := k]) (SA[k := x])"
  unfolding lms_locations_inv_def
proof (intro allI impI; elim conjE)
  fix b' i
  assume "b' \<le> \<alpha> (Max (set T))" "B[b := k] ! b' \<le> i" "i < bucket_end \<alpha> T b'"

  let ?goal = "SA[k := x] ! i \<in> lms_bucket \<alpha> T b'"

  have "lms_bucket_start \<alpha> T b < B ! b"
    using assms lms_distinct_bucket_ptr_lower_bound by blast

  have "b' \<noteq> b \<Longrightarrow> ?goal"
  proof -
    assume "b' \<noteq> b"
    with `B[b := k] ! b' \<le> i`
    have "B ! b' \<le> i"
      by simp

    from `b' \<noteq> b`
    have "b' < b \<or> b < b'"
      by auto
    then show ?thesis
    proof
      assume "b' < b"
      from `lms_bucket_start \<alpha> T b < B ! b`
      have "bucket_start \<alpha> T b < B ! b"
        by (metis dual_order.strict_trans2 l_bucket_end_def l_bucket_end_le_lms_bucket_start
                  le_add1)
      with `i < bucket_end \<alpha> T b'` `b' < b`
      have "i \<noteq> k"
        using assms(2,3)
        by (metis Suc_lessI Suc_pred dual_order.strict_trans1 less_bucket_end_le_start
                  less_nat_zero_code not_less_iff_gr_or_eq)
      hence "SA[k := x] ! i = SA ! i"
        by auto
      with lms_locations_invD[OF assms(5) `b' \<le> \<alpha> (Max (set T))` `B ! b' \<le> i`
                                 `i < bucket_end \<alpha> T b'`]
      show ?thesis
        by simp
    next
      assume "b < b'"
      from lms_bucket_ptr_lower_bound[OF assms(4) `b' \<le> \<alpha> (Max (set T))`]
      have "lms_bucket_start \<alpha> T b' \<le> B ! b'" .
      hence "bucket_start \<alpha> T b' \<le> B ! b'"
        by (metis l_bucket_end_def l_bucket_end_le_lms_bucket_start le_add1 le_trans)
      hence "bucket_start \<alpha> T b' \<le> i"
        using `B ! b' \<le> i` le_trans by blast
      moreover
      from lms_bucket_ptr_upper_bound[OF assms(4), of b] assms(7)
      have "B ! b \<le> bucket_end \<alpha> T b"
        using \<open>b < b'\<close> \<open>b' \<le> \<alpha> (Max (set T))\<close> by linarith
      with `lms_bucket_start \<alpha> T b < B ! b`
      have "k < bucket_end \<alpha> T b"
        using assms(2) by linarith
      ultimately
      have "i \<noteq> k"
        by (meson \<open>b < b'\<close> leD le_less_trans less_bucket_end_le_start)
      hence "SA[k := x] ! i = SA ! i"
        by simp
      with lms_locations_invD[OF assms(5)`b' \<le> \<alpha> (Max (set T))` `B ! b' \<le> i`
                                 `i < bucket_end \<alpha> T b'`]
      show ?thesis
        by simp
    qed
  qed
  moreover
  have "b' = b \<Longrightarrow> ?goal"
  proof -
    assume "b' = b"
    with `b' \<le> \<alpha> (Max (set T))` `B[b := k] ! b' \<le> i` `i < bucket_end \<alpha> T b'`
    have "b \<le> \<alpha> (Max (set T))" "B[b := k] ! b \<le> i" "i < bucket_end \<alpha> T b"
      by simp_all
    hence "k \<le> i"
      by (simp add: assms(7) order.strict_trans1)
    hence "k = i \<or> B ! b \<le> i"
      using assms(2) by linarith
    then show ?thesis
    proof
      assume "k = i"
      hence "SA[k := x] ! i = x"
        using \<open>i < bucket_end \<alpha> T b\<close> assms(8) bucket_end_le_length order.strict_trans2 by fastforce
      moreover
      from assms(1,9)
      have "x \<in> lms_bucket \<alpha> T b"
        by (simp add: bucket_def abs_is_lms_imp_less_length lms_bucket_def)
      ultimately
      show ?thesis
        using `b' = b` by simp
    next
      assume "B ! b \<le> i"
      with lms_locations_invD[OF assms(5) `b \<le> \<alpha> (Max (set T))` _ `i < bucket_end \<alpha> T b`]
      have "SA ! i \<in> lms_bucket \<alpha> T b"
        by blast
      moreover
      from `B ! b \<le> i` assms(2) `lms_bucket_start \<alpha> T b < B ! b`
      have "SA[k := x] ! i = SA ! i"
        by auto
      ultimately
      show ?thesis
        using `b' = b` by simp
    qed
  qed
  ultimately
  show ?goal
    by blast
qed
subsubsection \<open>Unchanged\<close>

lemma lms_unchanged_inv_established:
  "lms_unchanged_inv \<alpha> T B SA SA"
  unfolding lms_unchanged_inv_def
  by blast

lemma lms_unchanged_inv_maintained_step:
  assumes "b = \<alpha> (T ! x)"
  and     "k = (B ! b) - Suc 0"
  and     "lms_distinct_inv T SA (x # LMS)"
  and     "lms_bucket_ptr_inv \<alpha> T B SA"
  and     "lms_unchanged_inv \<alpha> T B SA0 SA"
  and     "strict_mono \<alpha>"
  and     "\<alpha> (Max (set T)) < length B"
  and     "length SA = length T"
  and     "\<forall>a \<in> set (x # LMS). abs_is_lms T a"
shows "lms_unchanged_inv \<alpha> T (B[b := k]) SA0 (SA[k := x])"
  unfolding lms_unchanged_inv_def
proof (intro allI impI; elim conjE)
  fix b' i
  assume "b' \<le> \<alpha> (Max (set T))" "bucket_start \<alpha> T b' \<le> i" "i < B[b := k] ! b'"

  let ?goal = "SA[k := x] ! i = SA0 ! i"

  have "lms_bucket_start \<alpha> T b < B ! b"
    using assms lms_distinct_bucket_ptr_lower_bound by blast

  have "b' \<noteq> b \<Longrightarrow> ?goal"
  proof -
    assume "b' \<noteq> b"
    with `i < B[b := k] ! b'`
    have "i < B ! b'"
      by simp

    from `b' \<noteq> b`
    have "b' < b \<or> b < b'"
      by linarith
    then show ?thesis
    proof
      assume "b' < b"
      from `lms_bucket_start \<alpha> T b < B ! b`
      have "bucket_start \<alpha> T b < B ! b"
        by (simp add: lms_bucket_start_def)
      with assms(2)
      have "bucket_start \<alpha> T b \<le> k"
        by linarith
      moreover
      from lms_bucket_ptr_upper_bound[OF assms(4) `b' \<le> \<alpha> (Max (set T))`]
      have "B ! b' \<le> bucket_end \<alpha> T b'" .
      with `i < B ! b'`
      have "i < bucket_end \<alpha> T b'"
        using less_le_trans by blast
      ultimately
      have "i \<noteq> k"
        using `b' < b`
        by (meson dual_order.strict_trans2 less_bucket_end_le_start order.strict_implies_not_eq)
      hence "SA[k := x] ! i = SA ! i"
        by simp
      with lms_unchanged_invD[OF assms(5) `b' \<le> \<alpha> (Max (set T))` `bucket_start \<alpha> T b' \<le> i`
                                 `i < B ! b'`]
      show ?thesis
        by simp
    next
      assume "b < b'"
      from `lms_bucket_start \<alpha> T b < B ! b` assms(2)
      have "k < B ! b"
        by linarith
      with lms_bucket_ptr_upper_bound[OF assms(4), of b] `b' \<le> \<alpha> (Max (set T))` `b < b'` assms(7)
      have "k < bucket_end \<alpha> T b"
        by linarith
      with `bucket_start \<alpha> T b' \<le> i` `b < b'`
      have "i \<noteq> k"
        by (meson dual_order.strict_trans1 leD less_bucket_end_le_start)
      hence "SA[k := x] ! i = SA ! i"
        by simp
      with lms_unchanged_invD[OF assms(5) `b' \<le> \<alpha> (Max (set T))` `bucket_start \<alpha> T b' \<le> i`
                                 `i < B ! b'`]
      show ?thesis
        by simp
    qed
  qed
  moreover
  have "b' = b \<Longrightarrow> ?goal"
  proof -
    assume "b' = b"
    with `b' \<le> \<alpha> (Max (set T))` `bucket_start \<alpha> T b' \<le> i` `i < B[b := k] ! b'`
    have "b \<le> \<alpha> (Max (set T))" "bucket_start \<alpha> T b \<le> i" "i < B[b := k] ! b"
      by simp_all
    hence "i < k"
      using assms(7) by auto
    hence "i < B ! b"
      using assms(2) by linarith
    with lms_unchanged_invD[OF assms(5) `b \<le> \<alpha> (Max (set T))` `bucket_start \<alpha> T b \<le> i`]
    have "SA ! i = SA0 ! i"
      by simp
    with `i < k`
    show ?thesis
      by auto
  qed
  ultimately
  show ?goal
    by blast
qed


subsubsection \<open>Inserted\<close>

lemma lms_inserted_inv_established:
  shows "lms_inserted_inv LMS SA [] LMS"
  unfolding lms_inserted_inv_def
  by simp

lemma lms_inserted_inv_maintained_step:
  assumes "b = \<alpha> (T ! x)"
  and     "k = (B ! b) - Suc 0"
  and     "lms_distinct_inv T SA (x # LMSb)"
  and     "lms_bucket_ptr_inv \<alpha> T B SA"
  and     "lms_unknowns_inv \<alpha> T B SA"
  and     "lms_inserted_inv LMS SA LMSa (x # LMSb)"
  and     "strict_mono \<alpha>"
  and     "length SA = length T"
  and     "\<forall>a \<in> set LMS. abs_is_lms T a"
shows "lms_inserted_inv LMS (SA[k := x]) (LMSa @ [x]) LMSb"
proof -

  from lms_inserted_invD(1)[OF assms(6)] assms(9)
  have "\<forall>a \<in> set (x # LMSb). abs_is_lms T a"
    by auto
  with lms_next_insert_at_unknown[OF assms(1-5,7,8)]
  have "k < length SA" "SA ! k = length T"
    by blast+

  from lms_inserted_invD(1)[OF assms(6)] assms(9)
  have "\<forall>a \<in> set LMSa. abs_is_lms T a"
    by auto
  hence "\<forall>a \<in> set LMSa. a < length T"
    using abs_is_lms_imp_less_length by blast

  have "set LMSa \<subseteq> set (SA[k := x])"
  proof (intro subsetI)
    fix y
    assume "y \<in> set LMSa"
    with `\<forall>a \<in> set LMSa. a < length T`
    have "y < length T"
      by blast
    with `SA ! k = length T`
    have "SA ! k \<noteq> y"
      by simp
    moreover
    from lms_inserted_invD(2)[OF assms(6)] `y \<in> set LMSa`
    have "y \<in> set SA"
      by blast
    ultimately
    show "y \<in> set (SA[k := x])"
      using in_set_list_update by fast
  qed
  moreover
  from `k < length SA`
  have "x \<in> set (SA[k := x])"
    by (simp add: set_update_memI)
  ultimately
  have "set (LMSa @ [x]) \<subseteq> set (SA[k := x])"
    by simp
  with lms_inserted_invD(1)[OF assms(6)]
  show ?thesis
    by (simp add: lms_inserted_inv_def)
qed

subsubsection \<open>Sorted\<close>

lemma lms_sorted_inv_established:
  assumes "\<forall>i < length SA. SA ! i = length T"
  and     "\<forall>a \<in> set LMS. abs_is_lms T a"
shows "lms_sorted_inv T LMS SA"
  unfolding lms_sorted_inv_def
proof (intro allI impI; elim conjE)
  fix i j
  assume A: "j < length SA" "i < j"  "SA ! i \<in> set LMS" "SA ! j \<in> set LMS"
  from A(1) assms(1)
  have "SA ! j = length T"
    by blast
  moreover
  from A(4) assms(2)
  have "SA ! j < length T"
    using abs_is_lms_imp_less_length by blast
  ultimately
  have False
    by auto
  then show
    "(T ! (SA ! i) \<noteq> T ! (SA ! j) \<longrightarrow> T ! (SA ! i) < T ! (SA ! j)) \<and>
     (T ! (SA ! i) = T ! (SA ! j) \<longrightarrow>
      (\<exists>j'<length LMS. \<exists>i'<j'. LMS ! i' = SA ! j \<and> LMS ! j' = SA ! i))"
    by blast
qed

lemma lms_sorted_inv_maintained_step:
  assumes "b = \<alpha> (T ! x)"
  and     "k = (B ! b) - Suc 0"
  and     "lms_distinct_inv T SA (x # LMSb)"
  and     "lms_bucket_ptr_inv \<alpha> T B SA"
  and     "lms_unknowns_inv \<alpha> T B SA"
  and     "lms_locations_inv \<alpha> T B SA"
  and     "lms_unchanged_inv \<alpha> T B SA0 SA"
  and     "lms_inserted_inv LMS SA LMSa (x # LMSb)"
  and     "lms_sorted_inv T LMS SA"
  and     "strict_mono \<alpha>"
  and     "length SA = length T"
  and     "\<forall>i < length T. SA0 ! i = length T"
  and     "\<forall>a \<in> set LMS. abs_is_lms T a"
shows "lms_sorted_inv T LMS (SA[k := x])"
  unfolding lms_sorted_inv_def
proof (intro allI impI; elim conjE)
  fix i j
  assume A: "j < length (SA[k := x])" "i < j" "SA[k := x] ! i \<in> set LMS"
            "SA[k := x] ! j \<in> set LMS"
  let ?goal1 = "T ! (SA[k := x] ! i) \<noteq> T ! (SA[k := x] ! j) \<longrightarrow>
                  T ! (SA[k := x] ! i) < T ! (SA[k := x] ! j)"
  and ?goal2 = "T ! (SA[k := x] ! i) = T ! (SA[k := x] ! j) \<longrightarrow>
                  (\<exists>j'<length LMS. \<exists>i'<j'.
                    LMS ! i' = SA[k := x] ! j \<and> LMS! j' = SA[k := x] ! i)"

  let ?goal = "?goal1 \<and> ?goal2"

  from assms(13) lms_inserted_invD[OF assms(8)]
  have "\<forall>a\<in>set (x # LMSb). abs_is_lms T a"
    by auto
  with lms_next_insert_at_unknown[OF assms(1-5,10,11)]
  have "k < length SA" "SA ! k = length T"
    by blast+

  from lms_distinct_bucket_ptr_lower_bound[OF assms(1,3,4,10) `\<forall>a\<in>set (x # LMSb). abs_is_lms T a`]
  have "lms_bucket_start \<alpha> T b < B ! b" .

  from assms(1,10) `\<forall>a\<in>set (x # LMSb). abs_is_lms T a`
  have "b \<le> \<alpha> (Max (set T))"
    by (simp add: abs_is_lms_imp_less_length strict_mono_less_eq)

  have "\<lbrakk>k \<noteq> i; k \<noteq> j\<rbrakk> \<Longrightarrow> ?goal"
  proof -
    assume "k \<noteq> i" "k \<noteq> j"
    with A
    have "j < length SA" "SA ! i \<in> set LMS" "SA ! j \<in> set LMS"
      by simp_all
    with lms_sorted_invD[OF assms(9) _ `i < j`] `k \<noteq> i` `k \<noteq> j`
    show ?goal
      by simp
  qed
  moreover
  have "\<lbrakk>k = i; k \<noteq> j\<rbrakk> \<Longrightarrow> ?goal"
  proof -
    assume "k = i" "k \<noteq> j"
    with A(1,4)
    have "j < length SA" "SA ! j \<in> set LMS" "SA[k := x] ! j = SA ! j"
      by simp_all

    from `k = i` assms(2)
    have "i = B ! b - Suc 0"
      by simp

    from `SA ! j \<in> set LMS` assms(13)
    have "SA ! j < length T"
      using abs_is_lms_imp_less_length by blast

    from index_in_bucket_interval_gen[of j T, OF _ assms(10)] assms(11) `j < length SA`
    obtain b' where
      "b' \<le> \<alpha> (Max (set T))"
      "bucket_start \<alpha> T b' \<le> j"
      "j < bucket_end \<alpha> T b'"
      by auto

    have "B ! b' \<le> j"
    proof (rule ccontr)
      assume "\<not> B ! b' \<le> j"
      hence "j < B ! b'"
        by simp
      with lms_unchanged_invD[OF assms(7) `b' \<le> \<alpha> (Max (set T))` `bucket_start \<alpha> T b' \<le> j`]
           assms(11,12) `j < length SA`
      have "SA ! j = length T"
        by auto
      with `SA ! j < length T`
      show False
        by auto
    qed
    with lms_locations_invD[OF assms(6) `b' \<le> \<alpha> (Max (set T))` _ `j < bucket_end \<alpha> T b'`]
    have "SA ! j \<in> lms_bucket \<alpha> T b'"
      by blast
    hence "\<alpha> (T ! (SA ! j)) = b'"
      by (simp add: bucket_def lms_bucket_def)

    from `lms_bucket_start \<alpha> T b < B ! b` `i = B ! b - Suc 0`
    have "lms_bucket_start \<alpha> T b \<le> i"
      by linarith
    hence "bucket_start \<alpha> T b \<le> i"
      by (metis l_bucket_end_def l_bucket_end_le_lms_bucket_start le_add1 le_trans)

    have "b \<le> b'"
    proof (rule ccontr)
      assume "\<not> b \<le> b'"
      hence "b' < b"
        by simp
      hence "bucket_end \<alpha> T b' \<le> bucket_start \<alpha> T b"
        by (simp add: less_bucket_end_le_start)
      with `j < bucket_end \<alpha> T b'`
      have "j < bucket_start \<alpha> T b"
        by linarith
      with `bucket_start \<alpha> T b \<le> i`
      have "j < i"
        by linarith
      with `i < j`
      show False
        by linarith
    qed

    from assms(3)[simplified lms_distinct_inv_def distinct_append] `SA ! j < length T`
         `j < length SA`
    have "SA ! j \<notin> set (x # LMSb)"
      by (metis IntI empty_iff filter_set member_filter nth_mem)
    with lms_inserted_invD[OF assms(8)] `SA ! j \<in> set LMS`
    have "SA ! j \<in> set LMSa"
      by auto
    hence "\<exists>j' < length LMSa. LMSa ! j' = SA ! j"
      by (simp add: in_set_conv_nth)
    then obtain j' where
      "j' < length LMSa"
      "LMSa ! j' = SA ! j"
      by blast
    with lms_inserted_invD(1)[OF assms(8)] `SA[k := x] ! j = SA ! j`
    have "LMS ! j' = SA[k := x] ! j"
      by (simp add: nth_append)

    from `\<alpha> (T ! (SA ! j)) = b'` `SA[k := x] ! j = SA ! j`
    have "\<alpha> (T ! (SA[k := x] ! j)) = b'"
      by simp

    from lms_inserted_invD(1)[OF assms(8)]
    have "length LMSa < length LMS"
      by simp

    from assms(3)[simplified lms_distinct_inv_def distinct_append] lms_inserted_invD[OF assms(8)]
    have "x \<notin> set LMSa"
      using \<open>\<forall>a\<in>set (x # LMSb). abs_is_lms T a\<close> abs_is_lms_imp_less_length by fastforce
    with lms_inserted_invD(1)[OF assms(8)]
    have "LMS ! length LMSa = x"
      by simp
    hence "LMS ! length LMSa = SA[k := x] ! i"
      using \<open>k < length SA\<close> \<open>k = i\<close> by auto

    from `k = i` assms(1) `k < length SA`
    have "\<alpha> (T ! (SA[k := x] ! i)) = b"
      by auto

    have "b = b' \<Longrightarrow> ?goal2"
    proof
      from `LMS ! j' = SA[k := x] ! j` `LMS ! length LMSa = SA[k := x] ! i` `j' < length LMSa`
           `length LMSa < length LMS`
      show "\<exists>j'<length LMS. \<exists>i'<j'. LMS ! i' = SA[k := x] ! j \<and> LMS ! j' = SA[k := x] ! i"
        by blast
    qed
    moreover
    from `\<alpha> (T ! (SA[k := x] ! j)) = b'` `\<alpha> (T ! (SA[k := x] ! i)) = b` assms(10)
    have "b = b' \<Longrightarrow> T ! (SA[k := x] ! i) = T ! (SA[k := x] ! j)"
      using strict_mono_eq by auto
    moreover
    have "b < b' \<Longrightarrow> ?goal1"
    proof
      assume "b < b'"
      with `\<alpha> (T ! (SA[k := x] ! i)) = b` `\<alpha> (T ! (SA[k := x] ! j)) = b'` assms(10)
      show "T ! (SA[k := x] ! i) < T ! (SA[k := x] ! j)"
        using strict_mono_less by blast
    qed
    moreover
    from `\<alpha> (T ! (SA[k := x] ! j)) = b'` `\<alpha> (T ! (SA[k := x] ! i)) = b` assms(10)
    have "b < b' \<Longrightarrow> T ! (SA[k := x] ! i) \<noteq> T ! (SA[k := x] ! j)"
      by auto
    moreover
    from `b \<le> b'`
    have "b = b' \<or> b < b'"
      by linarith
    ultimately
    show ?goal
      by blast
  qed
  moreover
  have "\<lbrakk>k \<noteq> i; k = j\<rbrakk> \<Longrightarrow> ?goal"
  proof -
    assume "k \<noteq> i" "k = j"
    with `SA[k := x] ! i \<in> set LMS`
    have "SA[k := x] ! i = SA ! i" "SA ! i \<in> set LMS"
      by simp_all

    from `k = j` assms(2)
    have "j = B ! b - Suc 0"
      by simp

    from `j < length (SA[k := x])` `i < j` assms(11)
    have "i < length T"
      by simp
    with index_in_bucket_interval_gen[of i T, OF _ assms(10)]
    obtain b' where
      "b' \<le> \<alpha> (Max (set T))"
      "bucket_start \<alpha> T b' \<le> i"
      "i < bucket_end \<alpha> T b'"
      by auto

    from `SA ! i \<in> set LMS` assms(13)
    have "SA ! i < length T"
      using abs_is_lms_imp_less_length by blast

    have "B ! b' \<le> i"
    proof (rule ccontr)
      assume "\<not>B ! b' \<le> i"
      hence "i < B ! b'"
        by (simp add: not_le)
      with lms_unchanged_invD[OF assms(7) `b' \<le> \<alpha> (Max (set T))` `bucket_start \<alpha> T b' \<le> i`]
           assms(12) `i < length T`
      have "SA ! i = length T"
        by simp
      with `SA ! i < length T`
      show False
        by linarith
    qed
    with lms_locations_invD[OF assms(6) `b' \<le> \<alpha> (Max (set T))` _ `i < bucket_end \<alpha> T b'`]
    have "SA ! i \<in> lms_bucket \<alpha> T b'"
      by blast
    hence "\<alpha> (T ! (SA ! i)) = b'"
      by (simp add: bucket_def lms_bucket_def)
    with `SA[k := x] ! i = SA ! i`
    have "\<alpha> (T ! (SA[k := x] ! i)) = b'"
      by simp

    from `i < j` `j = B ! b - Suc 0` `lms_bucket_start \<alpha> T b < B ! b`
    have "i < B ! b"
      using diff_le_self dual_order.strict_trans1 by blast

    have "i < bucket_start \<alpha> T b"
    proof (rule ccontr)
      assume "\<not>i < bucket_start \<alpha> T b"
      hence "bucket_start \<alpha> T b \<le> i"
        by (simp add: not_le)
      with lms_unchanged_invD[OF assms(7) `b \<le> \<alpha> (Max (set T))` _ `i < B ! b`]
           assms(12) `i < length T`
      have "SA ! i = length T"
        by auto
      with `SA ! i < length T`
      show False
        by linarith
    qed
    with `bucket_start \<alpha> T b' \<le> i`
    have "bucket_start \<alpha> T b' < bucket_start \<alpha> T b"
      by linarith
    hence "b' < b"
      by (meson bucket_start_le leD leI)

    from assms(1) `k = j` `k < length SA`
    have "\<alpha> (T ! (SA[k := x] ! j)) = b"
      by simp
    with `\<alpha> (T ! (SA[k := x] ! i)) = b'` `b' < b` assms(10)
    have "T ! (SA[k := x] ! i) < T ! (SA[k := x] ! j)"
      using strict_mono_less by blast
    then show ?goal
      by auto
  qed
  moreover
  from `i < j`
  have "\<lbrakk>k = i; k = j\<rbrakk> \<Longrightarrow> ?goal"
    by blast
  ultimately
  show ?goal
    by blast
qed

subsection \<open>Combined Establishment and Maintenance\<close>

lemma lms_inv_established:
  assumes "\<forall>i < length SA. SA ! i = length T"
  and     "\<forall>x \<in> set LMS. abs_is_lms T x"
  and     "distinct LMS"
  and     "lms_bucket_init \<alpha> T B"
  and     "length SA = length T"
  and     "strict_mono \<alpha>"
shows "lms_inv \<alpha> T B LMS [] LMS SA SA"
  unfolding lms_inv_def
  using lms_distinct_inv_established[OF assms(3,1)]
        lms_bucket_ptr_inv_established[OF assms(4,1)]
        lms_unknowns_inv_established[OF assms(4,1,5)]
        lms_locations_inv_established[OF assms(4)]
        lms_unchanged_inv_established
        lms_inserted_inv_established
        lms_sorted_inv_established[OF assms(1,2)]
        lms_bucket_init_length[OF assms(4)]
        assms
  by auto

lemma lms_inv_maintained_step:
  assumes "lms_inv \<alpha> T B LMS LMSa (x # LMSb) SA0 SA"
  and     "b = \<alpha> (T ! x)"
  and     "k = (B ! b) - Suc 0"
shows "lms_inv \<alpha> T (B[b := k]) LMS (LMSa @ [x]) LMSb SA0 (SA[k := x])"
  unfolding lms_inv_def
  using lms_distinct_inv_maintained_step[OF lms_invD(1)[OF assms(1)]]
        lms_bucket_ptr_inv_maintained_step[OF assms(2-3)
                                              lms_invD(1-3,8,9,12)[OF assms(1)]
                                              lms_inv_lms_helper(3)[OF assms(1)]]
        lms_unknowns_inv_maintained_step[OF assms(2-3)
                                            lms_invD(1-3,8,9)[OF assms(1)]
                                            lms_inv_lms_helper(3)[OF assms(1)]]
        lms_locations_inv_maintained_step[OF assms(2-3)
                                             lms_invD(1-2,4,8,9,12)[OF assms(1)]
                                             lms_inv_lms_helper(3)[OF assms(1)]]
        lms_unchanged_inv_maintained_step[OF assms(2-3)
                                             lms_invD(1-2,5,8,9,12)[OF assms(1)]
                                             lms_inv_lms_helper(3)[OF assms(1)]]
        lms_inserted_inv_maintained_step[OF assms(2-3)
                                           lms_invD(1-3,6,8,12)[OF assms(1)]
                                           lms_inv_lms_helper(1)[OF assms(1)]]
        lms_sorted_inv_maintained_step[OF assms(2-3)
                                         lms_invD(1-8,12,13)[OF assms(1)]
                                         lms_inv_lms_helper(1)[OF assms(1)]]
  by (metis assms(1) length_list_update lms_inv_def)

lemma lms_inv_maintained:
  assumes " bucket_insert_abs' \<alpha> T B SA gs xs = (SA', B', gs')"
  and     "lms_inv \<alpha> T B LMS gs xs SA0 SA"
shows "lms_inv \<alpha> T B' LMS gs' [] SA0 SA'"
  using assms
proof (induct arbitrary: SA' B' gs' LMS SA0
              rule: bucket_insert_abs'.induct[of _ \<alpha> T B SA gs xs])
  case (1 \<alpha> T B SA gs)
  note BC = this
  from BC(1)[simplified]
  have "B' = B" "SA' = SA" "gs' = gs"
    by auto
  with BC(2)
  show ?case
    by simp
next
  case (2 \<alpha> T B SA gs x xs)
  note IH = this
  let ?b = "\<alpha> (T ! x)"
  let ?k = "B ! ?b - Suc 0"
  from lms_inv_maintained_step[OF IH(3), of ?b ?k]
  have R1: "lms_inv \<alpha> T (B[?b := ?k]) LMS (gs @ [x]) xs SA0 (SA[?k := x])"
    by simp

  from IH(2)[simplified, simplified Let_def]
  have R2: " bucket_insert_abs' \<alpha> T (B[?b := ?k]) (SA[?k := x]) (gs @ [x]) xs = (SA', B', gs')" .

  from IH(1)[of ?b ?k "SA[?k := x]" "B[?b := ?k]" "gs @ [x]" SA' B' gs' LMS SA0,
             simplified,
             OF R2 R1]
  show ?case .
qed

lemma lms_inv_holds:
  assumes "\<forall>i < length SA. SA ! i = length T"
  and     "\<forall>x \<in> set LMS. abs_is_lms T x"
  and     "distinct LMS"
  and     "lms_bucket_init \<alpha> T B"
  and     "length SA = length T"
  and     "strict_mono \<alpha>"
  and     "bucket_insert_abs' \<alpha> T B SA [] LMS = (SA', B', gs')"
shows "lms_inv \<alpha> T B' LMS gs' [] SA SA'"
  using lms_inv_maintained[OF assms(7) lms_inv_established[OF assms(1-6)]] .

section \<open>Exhaustiveness\<close>

definition lms_type_exhaustive :: "('a :: {linorder, order_bot}) list \<Rightarrow> nat list \<Rightarrow> bool"
where
"lms_type_exhaustive T SA = (\<forall>i < length T. abs_is_lms T i \<longrightarrow> i \<in> set SA)"

lemma lms_type_exhaustiveD:
  "\<lbrakk>lms_type_exhaustive T SA; i < length T; abs_is_lms T i\<rbrakk> \<Longrightarrow> i \<in> set SA"
  using lms_type_exhaustive_def by blast

lemma lms_all_inserted_imp_exhaustive:
  assumes "lms_inserted_inv LMS SA LMS []"
  and     "set LMS = {i. abs_is_lms T i}"
shows "lms_type_exhaustive T SA"
  unfolding lms_type_exhaustive_def
proof (intro allI impI)
  fix i
  assume "i < length T" "abs_is_lms T i"
  with assms(2)
  have "i \<in> set LMS"
    by blast
  with lms_inserted_invD(2)[OF assms(1)]
  show "i \<in> set SA"
    by blast
qed

lemma lms_type_exhaustive_imp_lms_bucket_subset:
  assumes "lms_type_exhaustive T SA"
  and     "b \<le> \<alpha> (Max (set T))"
shows "lms_bucket \<alpha> T b \<subseteq> set SA"
proof (intro subsetI)
  fix x
  assume "x \<in> lms_bucket \<alpha> T b"
  hence "x < length T"
    by (simp add: abs_is_lms_imp_less_length lms_bucket_def)

  from `x \<in> lms_bucket \<alpha> T b`
  have "abs_is_lms T x"
    by (simp add: lms_bucket_def)

  from lms_type_exhaustiveD[OF assms(1) `x < length T` `abs_is_lms T x`]
  show "x \<in> set SA" .
qed


lemma lms_B_val:
  assumes "\<forall>i < length SA. SA ! i = length T"
  and     "distinct LMS"
  and     "lms_bucket_init \<alpha> T B"
  and     "length SA = length T"
  and     "strict_mono \<alpha>"
  and     "set LMS = {i. abs_is_lms T i}"
  and     "bucket_insert_abs' \<alpha> T B SA [] LMS = (SA', B', gs')"
  and     "b \<le> \<alpha> (Max (set T))"
shows "B' ! b = lms_bucket_start \<alpha> T b"
proof -
  from assms(6)
  have "\<forall>x \<in> set LMS. abs_is_lms T x"
    by blast
  with lms_inv_holds[OF assms(1) _ assms(2-5,7)]
  have "lms_inv \<alpha> T B' LMS gs' [] SA SA'" .
  hence "lms_inserted_inv LMS SA' gs' []"
    using lms_inv_def by blast
  hence "gs' = LMS"
    by (simp add: lms_inserted_inv_def)
  with `lms_inserted_inv LMS SA' gs' []` lms_all_inserted_imp_exhaustive[OF _ assms(6), of SA']
  have "lms_type_exhaustive T SA'"
    by simp
  with lms_type_exhaustive_imp_lms_bucket_subset assms(8)
  have "lms_bucket \<alpha> T b \<subseteq> set SA'"
    by blast
  with cur_lms_subset_lms_bucket
  have "cur_lms_types \<alpha> T SA' b = lms_bucket \<alpha> T b"
    by (simp add: cur_lms_types_def equalityI subset_eq)
  hence "num_lms_types \<alpha> T SA' b = card (lms_bucket \<alpha> T b)"
    by (simp add: num_lms_types_def)
  moreover
  from `lms_inv \<alpha> T B' LMS gs' [] SA SA'`
  have "lms_bucket_ptr_inv \<alpha> T B' SA'"
    using lms_inv_def by blast
  with lms_bucket_ptr_invD assms(8)
  have "B' ! b + num_lms_types \<alpha> T SA' b = bucket_end \<alpha> T b"
    by blast
  ultimately
  have "B' ! b + card (lms_bucket \<alpha> T b) = bucket_end \<alpha> T b"
    by simp
  then show "B' ! b = lms_bucket_start \<alpha> T b"
    by (metis add_implies_diff lms_bucket_pl_size_eq_end lms_bucket_size_def)
qed

section \<open>Postconditions\<close>

definition lms_vals_post ::  "('a :: {linorder, order_bot} \<Rightarrow> nat) \<Rightarrow> 'a list \<Rightarrow> nat list  \<Rightarrow> bool"
where
"lms_vals_post \<alpha> T SA =
  (\<forall>b \<le> \<alpha> (Max (set T)).
    lms_bucket \<alpha> T b = set (list_slice SA (lms_bucket_start \<alpha> T b) (bucket_end \<alpha> T b))
  )"

lemma lms_vals_postD:
  "\<lbrakk>lms_vals_post \<alpha> T SA; b \<le> \<alpha> (Max (set T))\<rbrakk> \<Longrightarrow>
   lms_bucket \<alpha> T b = set (list_slice SA (lms_bucket_start \<alpha> T b) (bucket_end \<alpha> T b))"
  using lms_vals_post_def by blast

definition 
  lms_pre :: "('a :: {linorder, order_bot} \<Rightarrow> nat) \<Rightarrow> 'a list \<Rightarrow> nat list \<Rightarrow> nat list \<Rightarrow> nat list \<Rightarrow> bool"
where
  "lms_pre \<alpha> T B SA LMS \<equiv>
    (\<forall>i < length SA. SA ! i = length T) \<and>
    length SA = length T \<and>
    lms_bucket_init \<alpha> T B \<and>
    strict_mono \<alpha> \<and>
    distinct LMS \<and>
    set LMS = {i. abs_is_lms T i}"

lemma lms_pre_elims:
  "lms_pre \<alpha> T B SA LMS \<Longrightarrow> \<forall>i < length SA. SA ! i = length T"
  "lms_pre \<alpha> T B SA LMS \<Longrightarrow> length SA  = length T"
  "lms_pre \<alpha> T B SA LMS \<Longrightarrow> lms_bucket_init \<alpha> T B"
  "lms_pre \<alpha> T B SA LMS \<Longrightarrow> strict_mono \<alpha>"
  "lms_pre \<alpha> T B SA LMS \<Longrightarrow> distinct LMS"
  "lms_pre \<alpha> T B SA LMS \<Longrightarrow> set LMS = {i. abs_is_lms T i}"
  using lms_pre_def by blast+

lemma lms_vals_post_holds:
  assumes "\<forall>i < length SA. SA ! i = length T"
  and     "distinct LMS"
  and     "lms_bucket_init \<alpha> T B"
  and     "length SA = length T"
  and     "strict_mono \<alpha>"
  and     "set LMS = {i. abs_is_lms T i}"
  and     "bucket_insert_abs' \<alpha> T B SA [] LMS = (SA', B', gs')"
shows "lms_vals_post \<alpha> T SA'"
  unfolding lms_vals_post_def
proof(intro allI impI)
  fix b
  assume "b \<le> \<alpha> (Max (set T))"

  from assms(6)
  have "\<forall>x \<in> set LMS. abs_is_lms T x"
    by blast
  with lms_inv_holds[OF assms(1) _ assms(2-5,7)]
  have R0:"lms_inv \<alpha> T B' LMS gs' [] SA SA'" .

  from lms_B_val[OF assms(1-7) `b \<le> \<alpha> (Max (set T))`]
  have R1: "B' ! b = lms_bucket_start \<alpha> T b" .

  have "bucket_end \<alpha> T b \<le> length SA'"
    by (metis R0 bucket_end_le_length lms_inv_def)

  have "finite (lms_bucket \<alpha> T b)"
    by (simp add: finite_lms_bucket)
  moreover
  from lms_slice_subset_lms_bucket[OF lms_invD(4,12)[OF R0] `b \<le> \<alpha> (Max (set T))`]
  have "set (list_slice SA' (B' ! b) (bucket_end \<alpha> T b)) \<subseteq> lms_bucket \<alpha> T b" .
  with R1
  have "set (list_slice SA' (lms_bucket_start \<alpha> T b) (bucket_end \<alpha> T b)) \<subseteq> lms_bucket \<alpha> T b"
    by simp
  moreover
  from lms_distinct_slice[OF lms_invD(1,2,4,12)[OF R0] `b \<le> \<alpha> (Max (set T))`]
  have "distinct (list_slice SA' (B' ! b) (bucket_end \<alpha> T b))" .
  with R1
  have "distinct (list_slice SA' (lms_bucket_start \<alpha> T b) (bucket_end \<alpha> T b))"
    by simp
  with distinct_card
  have "card (set (list_slice SA' (lms_bucket_start \<alpha> T b) (bucket_end \<alpha> T b)))
        = length (list_slice SA' (lms_bucket_start \<alpha> T b) (bucket_end \<alpha> T b))"
    by blast
  with `bucket_end \<alpha> T b \<le> length SA'`
  have "card (set (list_slice SA' (lms_bucket_start \<alpha> T b) (bucket_end \<alpha> T b)))
        = lms_bucket_size \<alpha> T b"
    by (metis add_diff_cancel_left' length_list_slice lms_bucket_pl_size_eq_end min.absorb_iff1)
  hence "card (set (list_slice SA' (lms_bucket_start \<alpha> T b) (bucket_end \<alpha> T b)))
         = card (lms_bucket \<alpha> T b)"
    by (simp add: lms_bucket_size_def)
  ultimately
  show "lms_bucket \<alpha> T b = set (list_slice SA' (lms_bucket_start \<alpha> T b) (bucket_end \<alpha> T b))"
    using card_subset_eq by blast
qed

corollary abs_bucket_insert_vals:
  assumes "lms_pre \<alpha> T B SA LMS"
  shows "lms_vals_post \<alpha> T (abs_bucket_insert \<alpha> T B SA LMS)"
proof -
  have "\<exists>SA' B' gs. bucket_insert_abs' \<alpha> T B SA [] LMS = (SA', B', gs)"
    by (meson prod_cases3)
  then obtain SA' B' gs where
    A: "bucket_insert_abs' \<alpha> T B SA [] LMS = (SA', B', gs)"
    by blast
  hence "abs_bucket_insert \<alpha> T B SA LMS = SA'"
    by (metis abs_bucket_insert_equiv fst_conv)
  with lms_vals_post_holds[OF lms_pre_elims(1,5,3,2,4,6)[OF assms] A]
  show ?thesis
    by simp
qed

definition lms_unknowns_post
where
  "lms_unknowns_post \<alpha> T SA =
  (\<forall>b \<le> \<alpha> (Max (set T)).
    (\<forall>i. bucket_start \<alpha> T b \<le> i \<and> i < lms_bucket_start \<alpha> T b \<longrightarrow> SA ! i = length T)
  )"

lemma lms_unknowns_postD:
  "\<lbrakk>lms_unknowns_post \<alpha> T SA; b \<le> \<alpha> (Max (set T)); bucket_start \<alpha> T b \<le> i;
    i < lms_bucket_start \<alpha> T b\<rbrakk> \<Longrightarrow>
   SA ! i = length T"
  using lms_unknowns_post_def by blast

lemma lms_unknowns_post_holds:
  assumes "\<forall>i < length SA. SA ! i = length T"
  and     "distinct LMS"
  and     "lms_bucket_init \<alpha> T B"
  and     "length SA = length T"
  and     "strict_mono \<alpha>"
  and     "set LMS = {i. abs_is_lms T i}"
  and     "bucket_insert_abs' \<alpha> T B SA [] LMS = (SA', B', gs')"
shows "lms_unknowns_post \<alpha> T SA'"
  unfolding lms_unknowns_post_def
proof(intro allI impI; elim conjE)
  fix b i
  assume "b \<le> \<alpha> (Max (set T))" "bucket_start \<alpha> T b \<le> i" "i < lms_bucket_start \<alpha> T b"

  from assms(6)
  have "\<forall>x \<in> set LMS. abs_is_lms T x"
    by blast
  with lms_inv_holds[OF assms(1) _ assms(2-5,7)]
  have R0:"lms_inv \<alpha> T B' LMS gs' [] SA SA'" .

  from `i < lms_bucket_start \<alpha> T b`
  have "i < length SA"
    by (metis assms(4) bucket_end_le_length dual_order.strict_trans1 lms_bucket_start_le_bucket_end)
  moreover
  from lms_B_val[OF assms(1-7) `b \<le> \<alpha> (Max (set T))`]
  have "B' ! b = lms_bucket_start \<alpha> T b" .
  with `i < lms_bucket_start \<alpha> T b`
  have "i < B' ! b"
    by simp
  with lms_unchanged_invD[OF lms_invD(5)[OF R0] `b \<le> \<alpha> (Max (set T))` `bucket_start \<alpha> T b \<le> i`]
  have "SA' ! i = SA ! i"
    by blast
  ultimately
  show "SA' ! i = length T"
    using assms(1) by auto
qed

corollary abs_bucket_insert_unknowns:
  assumes "lms_pre \<alpha> T B SA LMS"
  shows "lms_unknowns_post \<alpha> T (abs_bucket_insert \<alpha> T B SA LMS)"
proof -
  have "\<exists>SA' B' gs. bucket_insert_abs' \<alpha> T B SA [] LMS = (SA', B', gs)"
    by (meson prod_cases3)
  then obtain SA' B' gs where
    A: "bucket_insert_abs' \<alpha> T B SA [] LMS = (SA', B', gs)"
    by blast
  hence "abs_bucket_insert \<alpha> T B SA LMS = SA'"
    by (metis abs_bucket_insert_equiv fst_conv)
  with lms_unknowns_post_holds[OF lms_pre_elims(1,5,3,2,4,6)[OF assms] A]
  show ?thesis
    by simp
qed

corollary abs_bucket_insert_values:
  assumes "lms_pre \<alpha> T B SA LMS"
  shows "\<forall>b \<le> \<alpha> (Max (set T)).
           (\<forall>i. bucket_start \<alpha> T b \<le> i \<and> i < lms_bucket_start \<alpha> T b \<longrightarrow> (abs_bucket_insert \<alpha> T B SA LMS) ! i = length T) \<and>
           lms_bucket \<alpha> T b = set (list_slice (abs_bucket_insert \<alpha> T B SA LMS) (lms_bucket_start \<alpha> T b) (bucket_end \<alpha> T b))"
  by (meson assms abs_bucket_insert_unknowns abs_bucket_insert_vals lms_unknowns_postD lms_vals_postD)

lemma lms_lms_prefix_sorted_holds:
  assumes "\<forall>i < length SA. SA ! i = length T"
  and     "distinct LMS"
  and     "lms_bucket_init \<alpha> T B"
  and     "length SA = length T"
  and     "strict_mono \<alpha>"
  and     "set LMS = {i. abs_is_lms T i}"
  and     "bucket_insert_abs' \<alpha> T B SA [] LMS = (SA', B', gs')"
shows "ordlistns.sorted (map (lms_prefix T) (filter (\<lambda>x. x < length T) SA'))"
proof -
  from assms(6)
  have "\<forall>x \<in> set LMS. abs_is_lms T x"
    by blast
  with lms_inv_holds[OF assms(1) _ assms(2-5,7)]
  have R0:"lms_inv \<alpha> T B' LMS gs' [] SA SA'" .

  from lms_lms_prefix_sorted[OF lms_invD(2,4,5,8,12,13)[OF R0] assms(6)]
  show ?thesis .
qed

lemma lms_suffix_sorted_holds:
  assumes "\<forall>i < length SA. SA ! i = length T"
  and     "distinct LMS"
  and     "lms_bucket_init \<alpha> T B"
  and     "length SA = length T"
  and     "strict_mono \<alpha>"
  and     "set LMS = {i. abs_is_lms T i}"
  and     "bucket_insert_abs' \<alpha> T B SA [] LMS = (SA', B', gs')"
  and     "ordlistns.sorted (map (suffix T) (rev LMS))"
shows "ordlistns.sorted (map (suffix T) (filter (\<lambda>x. x < length T) SA'))"
proof -
  from assms(6)
  have "\<forall>x \<in> set LMS. abs_is_lms T x"
    by blast
  with lms_inv_holds[OF assms(1) _ assms(2-5,7)]
  have R0:"lms_inv \<alpha> T B' LMS gs' [] SA SA'" .

  from lms_suffix_sorted[OF lms_invD(2,4,5,7,8,12,13)[OF R0] assms(6) assms(8)]
  show ?thesis .
qed

lemma lms_bot_is_first:
  assumes "\<forall>i < length SA. SA ! i = length T"
  and     "distinct LMS"
  and     "lms_bucket_init \<alpha> T B"
  and     "length SA = length T"
  and     "strict_mono \<alpha>"
  and     "set LMS = {i. abs_is_lms T i}"
  and     "bucket_insert_abs' \<alpha> T B SA [] LMS = (SA', B', gs')"
  and     "valid_list T"
  and     "length T = Suc (Suc n)"
  and     "\<alpha> bot = 0"
shows "SA' ! 0 = Suc n"
proof -
  have "abs_is_lms T (Suc n)"
    by (simp add: assms(8,9) abs_is_lms_last)
  moreover
  have "\<alpha> (T ! (Suc n)) = 0"
    by (metis assms(8-10) diff_Suc_1 last_conv_nth length_greater_0_conv valid_list_def)
  ultimately
  have "Suc n \<in> lms_bucket \<alpha> T 0"
    by (simp add: assms(5,8-10) bucket_0 lms_bucket_def)

  have "lms_bucket_size \<alpha> T 0 = Suc 0" "l_bucket_size \<alpha> T 0 = 0" "pure_s_bucket_size \<alpha> T 0 = 0"
    using assms(5,8-10) bucket_0_size2 by blast+
  hence "lms_bucket \<alpha> T 0 = {Suc n}"
    by (metis One_nat_def add.commute assms(5,8-10) atLeastLessThan_singleton bucket_0
              lms_bucket_size_def lms_bucket_subset_bucket plus_1_eq_Suc subset_card_intvl_is_intvl)

  from assms(6)
  have "\<forall>x \<in> set LMS. abs_is_lms T x"
    by blast
  with lms_inv_holds[OF assms(1) _ assms(2-5,7)]
  have R0:"lms_inv \<alpha> T B' LMS gs' [] SA SA'" .


  from \<open>l_bucket_size \<alpha> T 0 = 0\<close> \<open>pure_s_bucket_size \<alpha> T 0 = 0\<close>
  have "lms_bucket_start \<alpha> T 0 = 0"
    by (simp add: bucket_start_0 lms_bucket_start_def)
  moreover
  from lms_B_val[OF assms(1-7), of 0]
  have "B' ! 0 = lms_bucket_start \<alpha> T 0"
    by simp
  moreover
  have "0 < bucket_end \<alpha> T 0 "
    by (simp add: assms(5,8,10) valid_list_bucket_end_0)
  ultimately
  show ?thesis
    using lms_locations_invD[OF lms_invD(4)[OF R0], of 0 0] `lms_bucket \<alpha> T 0 = {Suc n}`
    by auto
qed

corollary abs_bucket_insert_bot_first:
  assumes "lms_pre \<alpha> T B SA LMS"
  and     "valid_list T"
  and     "length T = Suc (Suc n)"
  and     "\<alpha> bot = 0"
shows "(abs_bucket_insert \<alpha> T B SA LMS) ! 0 = Suc n"
proof -
  have "\<exists>SA' B' gs. bucket_insert_abs' \<alpha> T B SA [] LMS = (SA', B', gs)"
    by (meson prod_cases3)
  then obtain SA' B' gs where
    A: "bucket_insert_abs' \<alpha> T B SA [] LMS = (SA', B', gs)"
    by blast
  hence "abs_bucket_insert \<alpha> T B SA LMS = SA'"
    by (metis abs_bucket_insert_equiv fst_conv)
  with lms_bot_is_first[OF lms_pre_elims(1,5,3,2,4,6)[OF assms(1)] A assms(2-)]
  show ?thesis
    by simp
qed

 \<comment>\<open> Used in SAIS algorithm as part of inducing the prefix ordering based on LMS \<close>
theorem lms_prefix_sorted_bucket:
  assumes "lms_pre \<alpha> T B SA LMS"
  and     "b \<le> \<alpha> (Max (set T))"
shows "ordlistns.sorted (map (lms_prefix T)
        (list_slice (abs_bucket_insert \<alpha> T B SA LMS) (lms_bucket_start \<alpha> T b) (bucket_end \<alpha> T b)))"
      (is "ordlistns.sorted (map ?f ?SA)")
proof -
  have "\<exists>SA' B' gs. bucket_insert_abs' \<alpha> T B SA [] LMS = (SA', B', gs)"
    by (meson prod_cases3)
  then obtain SA' B' gs where
    A: "bucket_insert_abs' \<alpha> T B SA [] LMS = (SA', B', gs)"
    by blast
  hence "abs_bucket_insert \<alpha> T B SA LMS = SA'"
    by (metis abs_bucket_insert_equiv fst_conv)

  from lms_vals_postD[OF abs_bucket_insert_vals[OF assms(1)] assms(2)]
  have P: "\<forall>x \<in> set ?SA . x < length T"
    using abs_is_lms_imp_less_length lms_bucket_def by blast

  from lms_lms_prefix_sorted_holds[OF lms_pre_elims(1,5,3,2,4,6)[OF assms(1)] A]
  have "ordlistns.sorted (map (lms_prefix T) (filter (\<lambda>x. x < length T) SA'))" .
  hence "ordlistns.sorted (map (lms_prefix T) (filter (\<lambda>x. x < length T) ?SA))"
    using \<open>abs_bucket_insert \<alpha> T B SA LMS = SA'\<close> ordlistns.sorted_map_filter_list_slice 
    by blast
  then show ?thesis
    by (simp add: P)
qed

 \<comment>\<open> Used in SAIS algorithm as part of inducing the suffix ordering based on LMS \<close>
theorem lms_suffix_sorted_bucket:
  assumes "lms_pre \<alpha> T B SA LMS"
  and     "ordlistns.sorted (map (suffix T) (rev LMS))"
  and     "b \<le> \<alpha> (Max (set T))"
shows "ordlistns.sorted (map (suffix T)
        (list_slice (abs_bucket_insert \<alpha> T B SA LMS) (lms_bucket_start \<alpha> T b) (bucket_end \<alpha> T b)))"
      (is "ordlistns.sorted (map ?f ?SA)")
proof -
  have "\<exists>SA' B' gs. bucket_insert_abs' \<alpha> T B SA [] LMS = (SA', B', gs)"
    by (meson prod_cases3)
  then obtain SA' B' gs where
    A: "bucket_insert_abs' \<alpha> T B SA [] LMS = (SA', B', gs)"
    by blast
  hence "abs_bucket_insert \<alpha> T B SA LMS = SA'"
    by (metis abs_bucket_insert_equiv fst_conv)

  from lms_vals_postD[OF abs_bucket_insert_vals[OF assms(1)] assms(3)]
  have P: "\<forall>x \<in> set ?SA . x < length T"
    using abs_is_lms_imp_less_length lms_bucket_def by blast

  from lms_suffix_sorted_holds[OF lms_pre_elims(1,5,3,2,4,6)[OF assms(1)] A assms(2)]
  have "ordlistns.sorted (map (suffix T) (filter (\<lambda>x. x < length T) SA'))" .
  hence "ordlistns.sorted (map (suffix T) (filter (\<lambda>x. x < length T) ?SA))"
    using \<open>abs_bucket_insert \<alpha> T B SA LMS = SA'\<close> ordlistns.sorted_map_filter_list_slice by blast
  then show ?thesis
    by (simp add: P)
qed

end