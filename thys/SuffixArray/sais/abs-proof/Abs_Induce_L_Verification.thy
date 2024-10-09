theory Abs_Induce_L_Verification
  imports "../abs-def/Abs_SAIS"
begin

section "Abstract Induce L-types Simple Properties"

lemma abs_induce_l_step_ex:
  "\<exists>B' SA' i'. abs_induce_l_step a b = (B', SA', i')"
  by (cases a; cases b; clarsimp split: prod.splits nat.splits SL_types.splits simp: Let_def)

lemma abs_induce_l_step_B_length:
  "abs_induce_l_step (B, SA, i) (\<alpha>, T) = (B', SA', i') \<Longrightarrow> length B' = length B"
  by (clarsimp split: prod.splits nat.splits SL_types.splits if_splits simp: Let_def)

lemma abs_induce_l_step_SA_length:
  "abs_induce_l_step (B, SA, i) (\<alpha>, T) = (B', SA', i') \<Longrightarrow> length SA' = length SA"
  by (clarsimp split: prod.splits nat.splits SL_types.splits if_splits simp: Let_def)

lemma abs_induce_l_step_Suc:
  "\<exists>B' SA'. abs_induce_l_step (B, SA, i) (\<alpha>, T) = (B', SA', Suc i)"
  by (clarsimp simp: Let_def split: prod.splits nat.splits SL_types.splits)

lemma abs_induce_l_step_B_val_1:
  "\<lbrakk>length SA \<le> i; abs_induce_l_step (B, SA, i) (\<alpha>, T) = (B', SA', i')\<rbrakk> \<Longrightarrow>
    B' = B"
  "\<lbrakk>i < length SA; length T \<le> SA ! i; abs_induce_l_step (B, SA, i) (\<alpha>, T) = (B', SA', i')\<rbrakk> \<Longrightarrow>
    B' = B"
  "\<lbrakk>i < length SA; SA ! i < length T; SA ! i = 0;
    abs_induce_l_step (B, SA, i) (\<alpha>, T) = (B', SA', i')\<rbrakk> \<Longrightarrow>
    B' = B"
  "\<lbrakk>i < length SA; SA ! i < length T; SA ! i = Suc j; suffix_type T j = S_type;
    abs_induce_l_step (B, SA, i) (\<alpha>, T) = (B', SA', i')\<rbrakk> \<Longrightarrow>
    B' = B"
  by (clarsimp simp: Let_def split: prod.splits nat.splits SL_types.splits if_splits)+

lemma abs_induce_l_step_B_val_2:
 "\<lbrakk>strict_mono \<alpha>;
   \<alpha> (Max (set T)) < length B;
   i < length SA;
   SA ! i < length T;
   SA ! i = Suc j;
   suffix_type T j = L_type;
   abs_induce_l_step (B, SA, i) (\<alpha>, T) = (B', SA', i')\<rbrakk> \<Longrightarrow>
   B' = B[\<alpha> (T ! j) := Suc (B ! \<alpha> (T ! j))]"
  by (clarsimp simp: Let_def split: prod.splits nat.splits SL_types.splits if_splits)

lemma repeat_abs_induce_l_step_index:
  "\<exists>B' SA'. repeat n abs_induce_l_step (B, SA, m) (\<alpha>, T) = (B', SA', n + m)"
proof (induct n)
  case 0
  then show ?case
    by (simp add: repeat_0)
next
  case (Suc n)
  from this
  obtain B' SA' where
    A: "repeat n abs_induce_l_step (B, SA, m) (\<alpha>, T) = (B', SA', n + m)"
    by blast

  from repeat_step[of n abs_induce_l_step "(B, SA, m)" "(\<alpha>, T)"]
  have B: "repeat (Suc n) abs_induce_l_step (B, SA, m) (\<alpha>, T) =
            abs_induce_l_step (repeat n abs_induce_l_step (B, SA, m) (\<alpha>, T)) (\<alpha>, T)"
    by assumption

  from abs_induce_l_step_Suc[of B' SA' "n + m" \<alpha> T]
  obtain B'' SA'' where
    "abs_induce_l_step (B', SA', n + m) (\<alpha>, T) = (B'', SA'', Suc (n + m))"
    by blast
  with A B
  show ?case
    by simp
qed

lemma abs_induce_l_step_lengths:
  "abs_induce_l_step (B, SA, i) (\<alpha>, T) = (B', SA', i') \<Longrightarrow>
   length B' = length B \<and> length SA' = length SA"
  by (clarsimp split: if_splits nat.splits SL_types.splits simp: Let_def)

lemma repeat_abs_induce_l_step_lengths:
  "repeat n abs_induce_l_step (B, SA, i) (\<alpha>, T) = (B', SA', i') \<Longrightarrow>
   length B' = length B \<and> length SA' = length SA"
proof -
  let ?P = "\<lambda>(a, b, c). length a = length B \<and> length b = length SA"

  from abs_induce_l_step_lengths
  have A: "\<And>a. ?P a \<Longrightarrow> ?P (abs_induce_l_step a (\<alpha>, T))"
    by (clarsimp simp: Let_def split: prod.splits if_splits nat.splits SL_types.splits)

  assume "repeat n abs_induce_l_step (B, SA, i) (\<alpha>, T) = (B', SA', i')"

  with repeat_maintain_inv[of ?P abs_induce_l_step "(\<alpha>, T)" "(B, SA, i)" n,
                           OF A]
  show ?thesis
    by auto
qed

lemma abs_induce_l_index:
  "\<exists>B' SA'. abs_induce_l_base \<alpha> T B SA = (B', SA', length T)"
  by (metis add.right_neutral abs_induce_l_base_def repeat_abs_induce_l_step_index)

lemma abs_induce_l_length:
  "length (abs_induce_l \<alpha> T B SA) = length SA"
  unfolding abs_induce_l_def abs_induce_l_base_def
  by (rule repeat_maintain_inv)
     (fastforce 
          simp del: abs_induce_l_step.simps 
          split: prod.splits
          dest: abs_induce_l_step_SA_length)+

  

section "Precondition Definitions"

definition lms_init :: "('a :: {linorder,order_bot} \<Rightarrow> nat) \<Rightarrow> 'a list \<Rightarrow> nat list \<Rightarrow> bool"
  where
"lms_init \<alpha> T SA =
  (\<forall>b \<le> \<alpha> (Max (set T)).
    lms_bucket \<alpha> T b = 
    set (list_slice SA (lms_bucket_start \<alpha> T b) (bucket_end \<alpha> T b))
  )"

lemma lms_init_D:
  "\<lbrakk>lms_init \<alpha> T SA; b \<le> \<alpha> (Max (set T))\<rbrakk> \<Longrightarrow>
    lms_bucket \<alpha> T b = set (list_slice SA (lms_bucket_start \<alpha> T b) (bucket_end \<alpha> T b))"
  using lms_init_def by blast

lemma lms_init_nth:
  "\<lbrakk>lms_init \<alpha> T SA;
    b \<le> \<alpha> (Max (set T));
    lms_bucket_start \<alpha> T b \<le> i;
    i < bucket_end \<alpha> T b;
    length SA = length T\<rbrakk> \<Longrightarrow>
    abs_is_lms T (SA ! i) \<and> \<alpha> (T ! (SA ! i)) = b"
  by (fastforce 
           dest: lms_init_D list_slice_nth_mem[where xs = SA]
           simp: bucket_end_le_length lms_bucket_def bucket_def)

lemma lms_init_imp_distinct_bucket:
  "\<lbrakk>lms_init \<alpha> T SA;
    b \<le> \<alpha> (Max (set T));
    length SA = length T\<rbrakk> \<Longrightarrow>
    distinct (list_slice SA (lms_bucket_start \<alpha> T b) (bucket_end \<alpha> T b))"
  by (metis bucket_end_def' min.absorb1 diff_diff_add bucket_end_le_length
            l_pl_pure_s_pl_lms_size lms_bucket_start_def length_list_slice
            diff_add_inverse lms_init_D  lms_bucket_size_def card_distinct)


lemma lms_init_imp_all_lms_in_SA:
  assumes "lms_init \<alpha> T SA"
  and     "strict_mono \<alpha>"
  shows "{k |k. abs_is_lms T k} \<subseteq> set SA"
proof
  fix x
  assume "x \<in> {k |k. abs_is_lms T k}"
  hence "x < length T"
    using abs_is_lms_gre_length le_less_linear by blast

  from `x \<in> {k |k. abs_is_lms T k}`
  have "abs_is_lms T x"
    by blast
  with `x < length T`
  have "x \<in> lms_bucket \<alpha> T (\<alpha> (T ! x))"
    unfolding lms_bucket_def bucket_def
    by blast

  from `strict_mono \<alpha>` `x < length T`
  have "\<alpha> (T ! x) \<le> \<alpha> (Max (set T))"
    by (simp add: strict_mono_leD)

  from lms_init_D[OF `lms_init \<alpha> T SA` `\<alpha> (T ! x) \<le> \<alpha> (Max (set T))`]
       `x \<in> lms_bucket \<alpha> T (\<alpha> (T ! x))`
  show "x \<in> set SA"
    using list_slice_subset by force
qed

definition s_init :: "('a :: {linorder,order_bot} \<Rightarrow> nat) \<Rightarrow> 'a list \<Rightarrow> nat list \<Rightarrow> bool"
  where
"s_init \<alpha> T SA =
  (\<forall>b \<le> \<alpha> (Max (set T)).
    \<forall>i < length SA. l_bucket_end \<alpha> T b \<le> i \<and> i < lms_bucket_start \<alpha> T b \<longrightarrow> SA ! i = length T
  )"

lemma s_init_D:
  "\<lbrakk>s_init \<alpha> T SA;
    b \<le> \<alpha> (Max (set T));
    i < length SA;
    l_bucket_end \<alpha> T b \<le> i;
    i < lms_bucket_start \<alpha> T b\<rbrakk> \<Longrightarrow>
    SA ! i = length T"
  using s_init_def by blast

definition l_init :: "('a :: {linorder,order_bot} \<Rightarrow> nat) \<Rightarrow> 'a list \<Rightarrow> nat list \<Rightarrow> bool"
  where
"l_init \<alpha> T SA =
  (\<forall>b \<le> \<alpha> (Max (set T)).
    \<forall>i < length SA. bucket_start \<alpha> T b \<le> i \<and> i < l_bucket_end \<alpha> T b \<longrightarrow> SA ! i = length T
  )"

lemma l_init_D:
  "\<lbrakk>l_init \<alpha> T SA;
    b \<le> \<alpha> (Max (set T));
    i < length SA;
    bucket_start \<alpha> T b \<le> i;
    i < l_bucket_end \<alpha> T b\<rbrakk> \<Longrightarrow>
    SA ! i = length T"
  using l_init_def by blast

lemma init_imp_lms_range:
  assumes "lms_init \<alpha> T SA"
  and     "l_init \<alpha> T SA"
  and     "s_init \<alpha> T SA"
  and     "length SA = length T"
  and     "strict_mono \<alpha>"
  and     "i < length SA"
  and     "SA ! i = j"
  and     "j < length T"
  shows "lms_bucket_start \<alpha> T (\<alpha> (T ! j)) \<le> i \<and> i < bucket_end \<alpha> T (\<alpha> (T ! j))"
proof -
  from `i < length SA` `length SA = length T`
  have "i < length T"
    by simp

  from index_in_bucket_interval_gen[OF `i < length T` `strict_mono \<alpha>`]
  obtain b where
    "b \<le> \<alpha> (Max (set T))"
    "bucket_start \<alpha> T b \<le> i"
    "i < bucket_end \<alpha> T b"
    by blast

  have "i < l_bucket_end \<alpha> T b \<longrightarrow> False"
  proof
    assume "i < l_bucket_end \<alpha> T b"
    with l_init_D[OF `l_init \<alpha> T SA` `b \<le> \<alpha> (Max (set T))` `i < length SA`]
         `bucket_start \<alpha> T b \<le> i`
         `SA ! i = j`
         `j < length T`
    show False
      by simp
  qed

  have "l_bucket_end \<alpha> T b \<le> i \<and> i < lms_bucket_start \<alpha> T b \<longrightarrow> False"
  proof(intro impI; elim conjE)
    assume "l_bucket_end \<alpha> T b \<le> i" "i < lms_bucket_start \<alpha> T b"
    with s_init_D[OF `s_init \<alpha> T SA` `b \<le> \<alpha> (Max (set T))` `i < length SA`]
         `SA ! i = j`
         `j < length T`
    show "False"
      by simp
  qed
  with `i < l_bucket_end \<alpha> T b \<longrightarrow> False`
       `b \<le> \<alpha> (Max (set T))`
       `i < bucket_end \<alpha> T b`
       `lms_init \<alpha> T SA`
       `length SA = length T`
       `SA ! i = j`
  show ?thesis
    by (metis lms_init_nth not_less)
qed

lemma init_imp_only_lms_types:
  assumes "lms_init \<alpha> T SA"
  and     "l_init \<alpha> T SA"
  and     "s_init \<alpha> T SA"
  and     "length SA = length T"
  and     "strict_mono \<alpha>"
  shows "\<forall>i < length SA. SA ! i < length T \<longrightarrow> abs_is_lms T (SA ! i)"
proof (intro allI impI)
  fix i
  assume "i < length SA" "SA ! i < length T"
  with init_imp_lms_range[OF `lms_init \<alpha> T SA`
                             `l_init \<alpha> T SA`
                             `s_init \<alpha> T SA`
                             `length SA = length T`
                             `strict_mono \<alpha>`
                             `i < length SA`]
  have "lms_bucket_start \<alpha> T (\<alpha> (T ! (SA ! i))) \<le> i \<and> i < bucket_end \<alpha> T (\<alpha> (T ! (SA ! i)))"
    by simp
  with `SA ! i < length T` `lms_init \<alpha> T SA` `length SA = length T` `strict_mono \<alpha>`
  show "abs_is_lms T (SA ! i)"
    by (meson Max_greD lms_init_nth strict_mono_less_eq)
qed

lemma init_imp_only_s_types:
  assumes "lms_init \<alpha> T SA"
  and     "l_init \<alpha> T SA"
  and     "s_init \<alpha> T SA"
  and     "length SA = length T"
  and     "strict_mono \<alpha>"
shows "\<forall>i < length SA. SA ! i < length T \<longrightarrow> suffix_type T (SA ! i) = S_type"
  using assms init_imp_only_lms_types abs_is_lms_def by blast

definition lms_sorted_init ::
  "('a :: {linorder, order_bot} \<Rightarrow> nat) \<Rightarrow>
   ('a list \<Rightarrow> nat \<Rightarrow> 'a list) \<Rightarrow>
   'a list \<Rightarrow>
   nat list \<Rightarrow>
   bool"
  where
"lms_sorted_init \<alpha> f T SA =
  (\<forall>b \<le> \<alpha> (Max (set T)).
    ordlistns.sorted (map (f T) (list_slice SA (lms_bucket_start \<alpha> T b) (bucket_end \<alpha> T b)))
  )"

lemma lms_sorted_init_D:
  "\<lbrakk>lms_sorted_init \<alpha> f T SA; b \<le> \<alpha> (Max (set T))\<rbrakk> \<Longrightarrow>
    ordlistns.sorted (map (f T) (list_slice SA (lms_bucket_start \<alpha> T b) (bucket_end \<alpha> T b)))"
  using lms_sorted_init_def by blast

definition l_suffix_sorted_pre ::
  "('a :: {linorder, order_bot} \<Rightarrow> nat) \<Rightarrow> 'a list \<Rightarrow> nat list \<Rightarrow> bool"
  where
"l_suffix_sorted_pre \<alpha> T SA =
  (\<forall>b \<le> \<alpha> (Max (set T)).
    ordlistns.sorted (map (suffix T) (list_slice SA (lms_bucket_start \<alpha> T b) (bucket_end \<alpha> T b)))
  )"

lemma l_suffix_sorted_preD:
  "\<lbrakk>l_suffix_sorted_pre \<alpha> T SA; b \<le> \<alpha> (Max (set T))\<rbrakk> \<Longrightarrow>
    ordlistns.sorted (map (suffix T) (list_slice SA (lms_bucket_start \<alpha> T b) (bucket_end \<alpha> T b)))"
  using l_suffix_sorted_pre_def by blast

definition l_prefix_sorted_pre ::
  "('a :: {linorder, order_bot} \<Rightarrow> nat) \<Rightarrow> 'a list \<Rightarrow> nat list \<Rightarrow> bool"
  where
"l_prefix_sorted_pre \<alpha> T SA =
  (\<forall>b \<le> \<alpha> (Max (set T)).
    ordlistns.sorted (map (lms_prefix T) (list_slice SA (lms_bucket_start \<alpha> T b) (bucket_end \<alpha> T b)))
  )"

lemma l_prefix_sorted_preD:
  "\<lbrakk>l_prefix_sorted_pre \<alpha> T SA; b \<le> \<alpha> (Max (set T))\<rbrakk> \<Longrightarrow>
    ordlistns.sorted (map (lms_prefix T) (list_slice SA (lms_bucket_start \<alpha> T b) (bucket_end \<alpha> T b)))"
  using l_prefix_sorted_pre_def by blast

definition l_perm_pre ::
  "('a :: {linorder, order_bot} \<Rightarrow> nat) \<Rightarrow>
   'a list \<Rightarrow>
   nat list \<Rightarrow>
   nat list \<Rightarrow>
   bool"
  where
"l_perm_pre \<alpha> T B SA =
  (lms_init \<alpha> T SA \<and>
   l_init \<alpha> T SA \<and>
   s_init \<alpha> T SA \<and>
   l_bucket_init \<alpha> T B \<and>
   T \<noteq> [] \<and>
   strict_mono \<alpha> \<and>
   length SA = length T \<and>
   \<alpha> (Max (set T)) < length B)"

lemma l_perm_pre_elims:
  "l_perm_pre \<alpha> T B SA \<Longrightarrow> lms_init \<alpha> T SA"
  "l_perm_pre \<alpha> T B SA \<Longrightarrow> l_init \<alpha> T SA"
  "l_perm_pre \<alpha> T B SA \<Longrightarrow> s_init \<alpha> T SA"
  "l_perm_pre \<alpha> T B SA \<Longrightarrow> l_bucket_init \<alpha> T B"
  "l_perm_pre \<alpha> T B SA \<Longrightarrow> T \<noteq> []"
  "l_perm_pre \<alpha> T B SA \<Longrightarrow> strict_mono \<alpha>"
  "l_perm_pre \<alpha> T B SA \<Longrightarrow> length SA = length T"
  "l_perm_pre \<alpha> T B SA \<Longrightarrow> \<alpha> (Max (set T)) < length B"
  unfolding l_perm_pre_def by blast+

section "Invariant Definitions"

text "This section contains all the various invariants that we need for the @{const abs_induce_l}
      subroutine."

subsection "Distinctness"

definition l_distinct_inv :: "('a :: {linorder, order_bot}) list \<Rightarrow> nat list \<Rightarrow> bool"
  where
"l_distinct_inv T SA = distinct (filter (\<lambda>x. x < length T) SA)"

lemma l_distinct_inv_D:
  assumes "l_distinct_inv T SA"
  and     "i < length SA"
  and     "j < length SA"
  and     "i \<noteq> j"
  and     "SA ! i < length T"
  and     "SA ! j < length T"
  shows "SA ! i \<noteq> SA ! j"
proof -
  from filter_nth_relative_neq_1[where P = "\<lambda>x. x < length T",
                                 OF `i < length SA`
                                    `SA ! i < length T`
                                    `j < length SA`
                                    `SA ! j < length T`
                                    `i \<noteq> j`]
  obtain i' j' where
    "i' < length (filter (\<lambda>x. x < length T) SA)"
    "j' < length (filter (\<lambda>x. x < length T) SA)"
    "filter (\<lambda>x. x < length T) SA ! i' = SA ! i"
    "filter (\<lambda>x. x < length T) SA ! j' = SA ! j"
    "i' \<noteq> j'"
    by blast

  from distinct_conv_nth[THEN iffD1,
                         OF l_distinct_inv_def[THEN iffD1],
                         OF `l_distinct_inv T SA`]
       `filter (\<lambda>x. x < length T) SA ! i' = SA ! i`
       `filter (\<lambda>x. x < length T) SA ! j' = SA ! j`
       `i' < length (filter (\<lambda>x. x < length T) SA)`
       `i' \<noteq> j'`
       `j' < length (filter (\<lambda>x. x < length T) SA)`
  show ?thesis
    by fastforce
qed

subsection "Predecessor"

definition l_pred_inv :: "('a :: {linorder, order_bot}) list \<Rightarrow> nat list \<Rightarrow> nat \<Rightarrow> bool"
  where
"l_pred_inv T SA k =
  (\<forall>i < length SA. SA ! i < length T \<and> suffix_type T (SA ! i) = L_type \<longrightarrow>
    (\<exists>j < length SA. SA ! j = Suc (SA ! i) \<and> j < i \<and> j < k))"

lemma l_pred_inv_D:
  "\<lbrakk>l_pred_inv T SA k; i < length SA; SA ! i < length T; suffix_type T (SA ! i) = L_type\<rbrakk> \<Longrightarrow>
    \<exists>j < length SA. SA ! j = Suc (SA ! i) \<and> SA ! j < length T \<and> j < i \<and> j < k"
  by (metis SL_types.simps(2) Suc_lessI l_pred_inv_def suffix_type_last)

subsection "L Bucket Ptr"


text "We prove that the pointer for each bucket is related to the number of L-types currently in
      SA.
      That is, if we subtract the original pointer with the current, we should have the number of
      L-types currently in SA for each symbol."

definition cur_l_types ::
  "('a :: {linorder, order_bot} \<Rightarrow> nat) \<Rightarrow> 'a list \<Rightarrow> nat list \<Rightarrow> nat \<Rightarrow> nat set"
  where
"cur_l_types \<alpha> T SA b = {i|i. i \<in> set SA \<and> i \<in> l_bucket \<alpha> T b }"

definition num_l_types ::
  "('a :: {linorder, order_bot} \<Rightarrow> nat) \<Rightarrow> 'a list \<Rightarrow> nat list \<Rightarrow> nat \<Rightarrow> nat"
  where
"num_l_types \<alpha> T SA b = card (cur_l_types \<alpha> T SA b)"

definition l_bucket_ptr_inv ::
  "('a :: {linorder, order_bot} \<Rightarrow> nat) \<Rightarrow> 'a list \<Rightarrow> nat list \<Rightarrow> nat list \<Rightarrow> bool"
  where
"l_bucket_ptr_inv \<alpha> T B SA \<equiv>
  (\<forall>b \<le> \<alpha> (Max (set T)). B ! b = bucket_start \<alpha> T b + num_l_types \<alpha> T SA b)"

lemma l_bucket_ptr_inv_D:
  "\<lbrakk>l_bucket_ptr_inv \<alpha> T B SA; b \<le> \<alpha> (Max (set T))\<rbrakk> \<Longrightarrow>
    B ! b = bucket_start \<alpha> T b + num_l_types \<alpha> T SA b"
  using l_bucket_ptr_inv_def by blast

subsection "Unknowns"

definition l_unknowns_inv ::
  "('a :: {linorder, order_bot} \<Rightarrow> nat) \<Rightarrow> 'a list \<Rightarrow> nat list \<Rightarrow> nat list \<Rightarrow> bool"
  where
"l_unknowns_inv \<alpha> T B SA \<equiv>
  (\<forall>a \<le> \<alpha> (Max (set T)). \<forall>k. B ! a \<le> k \<and> k < l_bucket_end \<alpha> T a \<longrightarrow> SA ! k = length T)"

lemma l_unknowns_inv_D:
  "\<lbrakk>l_unknowns_inv \<alpha> T B SA; b \<le> \<alpha> (Max (set T)); B ! b \<le> k; k < l_bucket_end \<alpha> T b\<rbrakk> \<Longrightarrow>
    SA ! k = length T"
  using l_unknowns_inv_def by blast

subsection "Indexes"

definition l_index_inv ::
  "('a :: {linorder, order_bot} \<Rightarrow> nat) \<Rightarrow> 'a list \<Rightarrow> nat list \<Rightarrow> nat list \<Rightarrow> bool"
  where
"l_index_inv \<alpha> T B SA \<equiv>
  (\<forall>i < length SA.
    (\<forall>j. SA ! i = Suc j \<and> Suc j < length T \<and> suffix_type T j = L_type \<longrightarrow>
      i < B ! (\<alpha> (T ! j))
    )
  )"

lemma l_index_inv_D:
  "\<lbrakk>l_index_inv \<alpha> T B SA; i < length SA; SA ! i = Suc j; Suc j < length T; suffix_type T j = L_type\<rbrakk> \<Longrightarrow>
    i < B ! (\<alpha> (T ! j))"
  using l_index_inv_def by blast

subsection "Unchanged"

definition l_unchanged_inv ::
  "('a :: {linorder,order_bot} \<Rightarrow> nat) \<Rightarrow> 'a list \<Rightarrow> nat list \<Rightarrow> nat list \<Rightarrow> bool"
  where
"l_unchanged_inv \<alpha> T SA SA'=
  ((length SA' = length SA) \<and>
  (\<forall>b \<le> \<alpha> (Max (set T)).
    (\<forall>i < length SA. l_bucket_end \<alpha> T b \<le> i \<and> i < bucket_end \<alpha> T b \<longrightarrow> SA ! i = SA' ! i)
  ))"

lemma l_unchanged_inv_trans:
  "\<lbrakk>l_unchanged_inv \<alpha> T SA0 SA1; l_unchanged_inv \<alpha> T SA1 SA2\<rbrakk> \<Longrightarrow>
    l_unchanged_inv \<alpha> T SA0 SA2"
  by (simp add: l_unchanged_inv_def)

lemma l_unchanged_inv_D:
  "\<lbrakk>l_unchanged_inv \<alpha> T SA SA'; length SA' = length SA; b \<le> \<alpha> (Max (set T));
    i < length SA; l_bucket_end \<alpha> T b \<le> i; i < bucket_end \<alpha> T b\<rbrakk> \<Longrightarrow>
    SA ! i = SA' ! i"
  using l_unchanged_inv_def by blast

subsection "L Locations"

definition l_locations_inv ::
  "('a :: {linorder,order_bot} \<Rightarrow> nat) \<Rightarrow> 'a list \<Rightarrow> nat list \<Rightarrow> nat list \<Rightarrow> bool"
  where
"l_locations_inv \<alpha> T B SA =
  (\<forall>b \<le> \<alpha> (Max (set T)).
    (\<forall>i < length SA. bucket_start \<alpha> T b \<le> i \<and> i < B ! b \<longrightarrow>
      SA ! i < length T \<and> suffix_type T (SA ! i) = L_type \<and> \<alpha> (T ! (SA ! i)) = b
    )
  )"

lemma l_locations_inv_D:
  "\<lbrakk>l_locations_inv \<alpha> T B SA;
    b \<le> \<alpha> (Max (set T));
    i < length SA;
    bucket_start \<alpha> T b \<le> i;
    i < B ! b\<rbrakk> \<Longrightarrow>
    SA ! i < length T \<and> suffix_type T (SA ! i) = L_type \<and> \<alpha> (T ! (SA ! i)) = b"
  using l_locations_inv_def by blast

lemma l_locations_list_slice:
  assumes "l_locations_inv \<alpha> T B SA"
  and     "b \<le> \<alpha> (Max (set T))"
shows "set (list_slice SA (bucket_start \<alpha> T b) (B ! b)) \<subseteq> l_bucket \<alpha> T b"
      (is "set ?xs \<subseteq> l_bucket \<alpha> T b")
proof
  fix x
  assume "x \<in> set ?xs"

  from nth_mem_list_slice[OF `x \<in> set ?xs`]
  obtain i where
    "i < length SA"
    "bucket_start \<alpha> T b \<le> i"
    "i < B ! b"
    "SA ! i = x"
    by blast
  with l_locations_inv_D[OF assms, of i]
  have "x < length T" "suffix_type T x = L_type" "\<alpha> (T ! x) = b"
    by blast+
  then show "x \<in> l_bucket \<alpha> T b"
    by (simp add: bucket_def l_bucket_def)
qed

subsection "Seen"

text "In this section, we prove that the seen invariant is maintained.
      In English, this invariant states for all L-type suffixes,
      excluding the one that starts at position 0,
      in the suffix array (SA) and that are less than the current index,
      their left neighbour is also in SA."

definition l_seen_inv :: "('a :: {linorder, order_bot}) list \<Rightarrow> nat list \<Rightarrow> nat \<Rightarrow> bool"
  where
"l_seen_inv T SA n \<equiv> \<forall>i < n. i < length SA \<and> SA ! i < length T \<longrightarrow>
                       (\<forall>j. SA ! i = Suc j \<and> suffix_type T j = L_type \<longrightarrow>
                         (\<exists>k < length SA. SA ! k = j))"

lemma l_seen_inv_nth_ex:
  "\<lbrakk>l_seen_inv T SA n; i < n; i < length SA; SA ! i < length T; SA ! i = Suc j;
    suffix_type T j = L_type\<rbrakk> \<Longrightarrow>
   \<exists>k < length SA. SA ! k = j"
  using l_seen_inv_def by blast

subsection "Sortedness"

definition abs_induce_l_sorted ::
  "(('a :: {linorder,order_bot}) list \<Rightarrow> nat \<Rightarrow> 'a list) \<Rightarrow> 'a list \<Rightarrow> nat list \<Rightarrow> bool"
  where
"abs_induce_l_sorted f T SA = ordlistns.sorted (map (f T) (filter (\<lambda>x. x < length T) SA))"

lemma abs_induce_l_sorted_nth:
  assumes "abs_induce_l_sorted f T SA"
  and     "i < j"
  and     "j < length SA"
  and     "SA ! i < length T"
  and     "SA ! j < length T"
  shows "list_less_eq_ns (f T (SA ! i)) (f T (SA ! j))"
proof -
  let ?SA = "filter (\<lambda>x. x < length T) SA" and
      ?le = "(\<lambda>x y. list_less_eq_ns (f T x) (f T y))"
  from filter_nth_relative_1[where P = "(\<lambda>x. x < length T)",
                             OF `j < length SA`
                                `SA ! j < length T`
                                `i < j`
                                `SA ! i < length T`]
  obtain i' j' where
    "j' < length ?SA"
    "i' < j'"
    "?SA ! j' = SA ! j"
    "?SA ! i' = SA ! i"
    by blast

  from ordlistns.sorted_map
       `abs_induce_l_sorted f T SA`
  have "sorted_wrt ?le ?SA"
    unfolding abs_induce_l_sorted_def
    by blast

  from sorted_wrt_nth_less[OF `sorted_wrt ?le ?SA`
                              `i' < j'`
                              `j' < length ?SA`]
  have "list_less_eq_ns (f T (?SA ! i')) (f T (?SA ! j'))"
    by assumption
  with `?SA ! i' = SA ! i` `?SA ! j' = SA ! j`
  show ?thesis
    by simp
qed

definition l_suffix_sorted_inv ::
  "(('a :: {linorder,order_bot}) \<Rightarrow> nat) \<Rightarrow> 'a list \<Rightarrow> nat list \<Rightarrow> nat list \<Rightarrow> bool"
  where
"l_suffix_sorted_inv \<alpha> T B SA =
  (\<forall>b \<le> \<alpha> (Max (set T)).
    ordlistns.sorted (map (suffix T) (list_slice SA (bucket_start \<alpha> T b) (B ! b))))"

lemma l_suffix_sorted_invD:
  "\<lbrakk>l_suffix_sorted_inv \<alpha> T B SA; b \<le> \<alpha> (Max (set T))\<rbrakk> \<Longrightarrow>
    ordlistns.sorted (map (suffix T) (list_slice SA (bucket_start \<alpha> T b) (B ! b)))"
  using l_suffix_sorted_inv_def by blast

definition l_prefix_sorted_inv ::
  "(('a :: {linorder,order_bot}) \<Rightarrow> nat) \<Rightarrow> 'a list \<Rightarrow> nat list \<Rightarrow> nat list \<Rightarrow> bool"
  where
"l_prefix_sorted_inv \<alpha> T B SA =
  (\<forall>b \<le> \<alpha> (Max (set T)).
    ordlistns.sorted (map (lms_prefix T) (list_slice SA (bucket_start \<alpha> T b) (B ! b))))"

lemma l_prefix_sorted_invD:
  "\<lbrakk>l_prefix_sorted_inv \<alpha> T B SA; b \<le> \<alpha> (Max (set T))\<rbrakk> \<Longrightarrow>
    ordlistns.sorted (map (lms_prefix T) (list_slice SA (bucket_start \<alpha> T b) (B ! b)))"
  using l_prefix_sorted_inv_def by blast

subsection "Permutation"

definition l_perm_inv ::
  "('a :: {linorder, order_bot} \<Rightarrow> nat) \<Rightarrow>
   'a list \<Rightarrow>
   nat list \<Rightarrow>
   nat list \<Rightarrow>
   nat list \<Rightarrow>
   nat \<Rightarrow>
   bool"
  where
"l_perm_inv \<alpha> T B SA SA' i \<equiv>
  \<alpha> (Max (set T)) < length B \<and>
  length SA = length T \<and>
  length SA' = length SA \<and>
  l_distinct_inv T SA' \<and>
  l_unknowns_inv \<alpha> T B SA' \<and>
  l_bucket_ptr_inv \<alpha> T B SA' \<and>
  l_index_inv \<alpha> T B SA' \<and>
  l_unchanged_inv \<alpha> T SA SA' \<and>
  l_locations_inv \<alpha> T B SA' \<and>
  l_pred_inv T SA' i \<and>
  l_seen_inv T SA' i \<and>
  strict_mono \<alpha> \<and>
  T \<noteq> [] \<and>
  lms_init \<alpha> T SA \<and>
  s_init \<alpha> T SA"

lemma l_perm_inv_elims:
  "l_perm_inv \<alpha> T B SA SA' i \<Longrightarrow> \<alpha> (Max (set T)) < length B"
  "l_perm_inv \<alpha> T B SA SA' i \<Longrightarrow> length SA = length T"
  "l_perm_inv \<alpha> T B SA SA' i \<Longrightarrow> length SA' = length SA"
  "l_perm_inv \<alpha> T B SA SA' i \<Longrightarrow> l_distinct_inv T SA'"
  "l_perm_inv \<alpha> T B SA SA' i \<Longrightarrow> l_unknowns_inv \<alpha> T B SA'"
  "l_perm_inv \<alpha> T B SA SA' i \<Longrightarrow> l_bucket_ptr_inv \<alpha> T B SA'"
  "l_perm_inv \<alpha> T B SA SA' i \<Longrightarrow> l_index_inv \<alpha> T B SA'"
  "l_perm_inv \<alpha> T B SA SA' i \<Longrightarrow> l_unchanged_inv \<alpha> T SA SA'"
  "l_perm_inv \<alpha> T B SA SA' i \<Longrightarrow> l_locations_inv \<alpha> T B SA'"
  "l_perm_inv \<alpha> T B SA SA' i \<Longrightarrow> l_pred_inv T SA' i"
  "l_perm_inv \<alpha> T B SA SA' i \<Longrightarrow> l_seen_inv T SA' i"
  "l_perm_inv \<alpha> T B SA SA' i \<Longrightarrow> strict_mono \<alpha>"
  "l_perm_inv \<alpha> T B SA SA' i \<Longrightarrow> T \<noteq> []"
  "l_perm_inv \<alpha> T B SA SA' i \<Longrightarrow> lms_init \<alpha> T SA"
  "l_perm_inv \<alpha> T B SA SA' i \<Longrightarrow> s_init \<alpha> T SA"
  by (simp add: l_perm_inv_def)+

section "Invariant Helpers"

subsection "Distinctness of New Insert"

text "We prove that the next item to be inserted cannot already be in the suffix array."
lemma l_distinct_pred_inv_helper:
  assumes "i < length SA"
  and     "SA ! i = Suc j"
  and     "Suc j < length T"
  and     "suffix_type T j = L_type"
  and     "l_distinct_inv T SA"
  and     "l_pred_inv T SA i"
  shows "j \<notin> set SA"
proof
  assume "j \<in> set SA"
  then obtain l where
    "l < length SA"
    "SA ! l = j"
    by (meson in_set_conv_nth)

  from l_pred_inv_D[OF `l_pred_inv T SA i` `l < length SA`]
       `SA ! l = j`
       `SA ! i = Suc j`
       `Suc j < length T`
       `suffix_type T j = L_type`
  obtain i' where
    "i' < length SA"
    "SA ! i' = Suc j"
    "i' < l"
    "i' < i"
    by auto

  from `SA ! i = Suc j` `SA ! i' = Suc j`
  have "SA ! i = SA ! i'"
    by simp

  from `SA ! i' = Suc j` `Suc j < length T`
  have "SA ! i' < length T"
    by simp

  from `i' < i`
  have "i \<noteq> i'"
    by simp

  from `SA ! i = Suc j` `Suc j < length T`
  have "SA ! i < length T"
    by simp

  from l_distinct_inv_D[OF `l_distinct_inv T SA`
                         `i < length SA`
                         `i' < length SA`
                         `i \<noteq> i'`
                         `SA ! i < length T`
                         `SA ! i' < length T`]
       `SA ! i = SA ! i'`
  show False
    by simp
qed

lemma l_distinct_slice:
  assumes "l_distinct_inv T SA"
  and     "l_locations_inv \<alpha> T B SA"
  and     "length SA = length T"
  and     "b \<le> \<alpha> (Max (set T))"
shows "distinct (list_slice SA (bucket_start \<alpha> T b) (B ! b))"
      (is "distinct ?xs")
proof (intro distinct_conv_nth[THEN iffD2] allI impI)
  fix i j
  assume "i < length ?xs" "j < length ?xs" "i \<noteq> j"

  let ?i = "bucket_start \<alpha> T b + i"
  and ?j = "bucket_start \<alpha> T b + j"

  have "SA ! ?i = ?xs ! i"
    using \<open>i < length ?xs\<close> nth_list_slice by force

  have "SA ! ?j = ?xs ! j"
    using \<open>j < length ?xs\<close> nth_list_slice by force

  from `i \<noteq> j`
  have "?i \<noteq> ?j"
    by auto
  moreover
  from `i < length ?xs`
  have "?i < length SA" "?i < B ! b" 
    by auto
  with l_locations_inv_D[OF assms(2,4), of ?i]
  have "SA ! ?i < length T"
    using le_add1 by blast
  moreover
  from `j < length ?xs`
  have "?j < length SA" "?j < B ! b"
    by auto
  with l_locations_inv_D[OF assms(2,4), of ?j]
  have "SA ! ?j < length T"
    using le_add1 by blast
  ultimately have "SA ! ?i \<noteq> SA ! ?j"
    using l_distinct_inv_D[OF assms(1) `?i < length SA` `?j < length SA`]
    by blast
  with `SA ! ?i = ?xs ! i` `SA ! ?j = ?xs ! j`
  show "?xs ! i \<noteq> ?xs ! j"
    by simp
qed

subsection "Bucket Ranges"

lemma num_l_types_le_l_bucket_size:
  "num_l_types \<alpha> T SA b \<le> l_bucket_size \<alpha> T b"
  by (metis (no_types, lifting) card_mono cur_l_types_def finite_l_bucket l_bucket_size_def
                                mem_Collect_eq num_l_types_def subsetI)

lemma num_l_types_less_l_bucket_size:
  "\<lbrakk>j \<notin> set SA; suffix_type T j = L_type; \<alpha> (T ! j) = b; j < length T\<rbrakk> \<Longrightarrow>
   num_l_types \<alpha> T SA b < l_bucket_size \<alpha> T b"
  apply (clarsimp simp: num_l_types_def cur_l_types_def l_bucket_size_def)
  apply (rule psubset_card_mono)
   apply (simp add: finite_l_bucket)
  apply (rule psubsetI)
   apply (rule subsetI)
   apply blast
  apply clarsimp
  apply (drule equalityD2)
  apply (drule subsetD[where c = j])
   apply (simp add: bucket_def l_bucket_def)
  apply blast
  done

lemma l_bucket_ptr_inv_imp_le_l_bucket_end:
  "\<lbrakk>l_bucket_ptr_inv \<alpha> T B SA; b \<le> \<alpha> (Max (set T))\<rbrakk> \<Longrightarrow>
    B ! b \<le> l_bucket_end \<alpha> T b"
  apply (drule (1) l_bucket_ptr_inv_D)
  by (simp add: l_bucket_end_def num_l_types_le_l_bucket_size)

lemma l_bucket_ptr_inv_imp_less_l_bucket_end:
  "\<lbrakk>l_bucket_ptr_inv \<alpha> T B SA; j < length T; suffix_type T j = L_type; j \<notin> set SA; strict_mono \<alpha>\<rbrakk> \<Longrightarrow>
    B ! (\<alpha> (T ! j)) < l_bucket_end \<alpha> T (\<alpha> (T ! j))"
  apply (frule num_l_types_less_l_bucket_size[where \<alpha> = \<alpha> and b = "\<alpha> (T ! j)"]; assumption?)
   apply simp
  apply (drule l_bucket_ptr_inv_D[where b = "\<alpha> (T ! j)"])
   apply (simp add: strict_mono_leD)
  by (simp add: l_bucket_end_def)

lemma bucket_size_imp_less_length:
  "\<lbrakk>l_bucket_ptr_inv \<alpha> T B SA; j < length T; suffix_type T j = L_type; j \<notin> set SA; strict_mono \<alpha>\<rbrakk> \<Longrightarrow>
    B ! (\<alpha> (T ! j)) < length T"
  apply (drule (4) l_bucket_ptr_inv_imp_less_l_bucket_end)
  apply (erule order.strict_trans2)
  apply (rule order.trans[OF l_bucket_end_le_bucket_end bucket_end_le_length])
  done

lemma l_bucket_ptr_inv_imp_ge_bucket_start:
  "\<lbrakk>l_bucket_ptr_inv \<alpha> T B SA; b \<le> \<alpha> (Max (set T))\<rbrakk> \<Longrightarrow>
    bucket_start \<alpha> T b \<le> B ! b"
  by (simp add: l_bucket_ptr_inv_D)

lemma l_bucket_ptr_inv_le_bucket_pointers:
  "\<lbrakk>l_bucket_ptr_inv \<alpha> T B SA; a < b; b \<le> \<alpha> (Max (set T))\<rbrakk> \<Longrightarrow>
    B ! a \<le> B ! b"
  apply (frule l_bucket_ptr_inv_imp_le_l_bucket_end[where b = a])
   apply arith
  apply (frule l_bucket_ptr_inv_D[where b = b])
   apply assumption
  apply simp
  apply (erule order.trans)
  apply (rule order.trans[where b = "bucket_start \<alpha> T b"])
   apply (erule order.trans[OF l_bucket_end_le_bucket_end less_bucket_end_le_start])
  apply simp
  done

subsection "No Overwrite"

text "We prove that the next location is set as unknown."
lemma l_unknowns_l_bucket_ptr_inv_helper:
  "\<lbrakk>l_unknowns_inv \<alpha> T B SA;
    l_bucket_ptr_inv \<alpha> T B SA;
    j < length T;
    suffix_type T j = L_type;
    j \<notin> set SA;
    strict_mono \<alpha>;
    k = \<alpha> (T ! j);
    l = B ! k\<rbrakk> \<Longrightarrow>
    SA ! l = length T"
  apply (drule (4) l_bucket_ptr_inv_imp_less_l_bucket_end)
  apply (drule l_unknowns_inv_D[where b = k and k = l]; simp add: strict_mono_leD)
  done


lemma unchanged_slice:
  assumes "l_unchanged_inv \<alpha> T SA0 SA"
  and     "length SA = length SA0"
  and     "length SA = length T"
  and     "b \<le> \<alpha> (Max (set T))"
  and     "l_bucket_end \<alpha> T b \<le> i"
  and     "j \<le> bucket_end \<alpha> T b"
shows "list_slice SA0 i j = list_slice SA i j"
proof (intro list_eq_iff_nth_eq[THEN iffD2] allI impI conjI)
  from `length SA = length SA0`
       length_list_slice
  show "length (list_slice SA0 i j) = length (list_slice SA i j)"
    by simp
next
  fix k
  assume "k < length (list_slice SA0 i j)"
  with `l_bucket_end \<alpha> T b \<le> i`
  have "l_bucket_end \<alpha> T b \<le> i + k"
    by simp

  from `length SA = length T`
  have "bucket_end \<alpha> T b \<le> length SA"
    by (simp add: bucket_end_le_length)
  with `j \<le> bucket_end \<alpha> T b`
  have "j \<le> length SA"
    by simp
  with `length SA = length SA0`
  have "length (list_slice SA0 i j) = j - i"
    by simp
  with `k < length (list_slice SA0 i j)`
  have "i < j"
    by linarith

  from `j \<le> length SA`
       `k < length (list_slice SA0 i j)`
       `length (list_slice SA0 i j) = j - i`
       `length SA = length SA0`
  have "i + k < length SA0"
    by linarith

  from `j \<le> bucket_end \<alpha> T b`
       `k < length (list_slice SA0 i j)`
       `length (list_slice SA0 i j) = j - i`
  have "i + k < bucket_end \<alpha> T b"
    by linarith

  from l_unchanged_inv_D[OF `l_unchanged_inv \<alpha> T SA0 SA`
                                `length SA = length SA0`
                                `b \<le> \<alpha> (Max (set T))`
                                `i + k < length SA0`
                                `l_bucket_end \<alpha> T b \<le> i + k`
                                `i + k < bucket_end \<alpha> T b`]
       `k < length (list_slice SA0 i j)`
       `length SA = length SA0`
  show "list_slice SA0 i j ! k = list_slice SA i j ! k"
    by (metis length_list_slice nth_list_slice)
qed

lemma lms_init_unchanged:
  assumes "l_unchanged_inv \<alpha> T SA0 SA"
  and     "length SA = length SA0"
  and     "length SA = length T"
  and     "lms_init \<alpha> T SA0"
  shows "lms_init \<alpha> T SA"
  unfolding lms_init_def
proof (intro allI impI)
  fix b
  assume "b \<le> \<alpha> (Max (set T))"

  have "l_bucket_end \<alpha> T b \<le> lms_bucket_start \<alpha> T b"
    by (simp add: l_bucket_end_le_lms_bucket_start)

  from unchanged_slice[OF `l_unchanged_inv \<alpha> T SA0 SA`
                          `length SA = length SA0`
                          `length SA = length T`
                          `b \<le> \<alpha> (Max (set T))`
                          `l_bucket_end \<alpha> T b \<le> lms_bucket_start \<alpha> T b`
                          order.refl]
       lms_init_D[OF `lms_init \<alpha> T SA0` `b \<le> \<alpha> (Max (set T))`]
  show "lms_bucket \<alpha> T b = set (list_slice SA (lms_bucket_start \<alpha> T b) (bucket_end \<alpha> T b))"
    by simp
qed

lemma s_init_unchanged:
  assumes "l_unchanged_inv \<alpha> T SA0 SA"
  and     "length SA = length SA0"
  and     "length SA = length T"
  and     "s_init \<alpha> T SA0"
  shows "s_init \<alpha> T SA"
  unfolding s_init_def
proof (intro allI impI; elim conjE)
  fix b i
  assume "b \<le> \<alpha> (Max (set T))"
         "i < length SA"
         "l_bucket_end \<alpha> T b \<le> i"
         "i < lms_bucket_start \<alpha> T b"

  have "lms_bucket_start \<alpha> T b \<le> bucket_end \<alpha> T b"
    by (simp add: bucket_end_def' l_pl_pure_s_pl_lms_size lms_bucket_start_def)
  with `i < lms_bucket_start \<alpha> T b`
  have "i < bucket_end \<alpha> T b"
    by simp

  from `i < length SA` `length SA = length SA0`
  have "i < length SA0"
    by simp

  from l_unchanged_inv_D[OF `l_unchanged_inv \<alpha> T SA0 SA`
                                `length SA = length SA0`
                                `b \<le> \<alpha> (Max (set T))`
                                `i < length SA0`
                                `l_bucket_end \<alpha> T b \<le> i`
                                `i < bucket_end \<alpha> T b`]
  have "SA0 ! i = SA ! i"
    by assumption

  from s_init_D[OF `s_init \<alpha> T SA0`
                   `b \<le> \<alpha> (Max (set T))`
                   `i < length SA0`
                   `l_bucket_end \<alpha> T b \<le> i`
                   `i < lms_bucket_start \<alpha> T b`]
  have "SA0 ! i = length T"
    by simp
  with `SA0 ! i = SA ! i`
  show "SA ! i = length T"
    by simp
qed

lemma l_suffix_sorted_pre_maintained:
  assumes "l_unchanged_inv \<alpha> T SA0 SA"
  and     "length SA = length SA0"
  and     "length SA = length T"
  and     "l_suffix_sorted_pre \<alpha> T SA0"
shows "l_suffix_sorted_pre \<alpha> T SA"
  unfolding l_suffix_sorted_pre_def
proof (safe)
  fix b
  assume "b \<le> \<alpha> (Max (set T))"
  let ?xs = "list_slice SA0 (lms_bucket_start \<alpha> T b) (bucket_end \<alpha> T b)" and
      ?ys = "list_slice SA (lms_bucket_start \<alpha> T b) (bucket_end \<alpha> T b)"

  have "l_bucket_end \<alpha> T b \<le> lms_bucket_start \<alpha> T b"
    using l_bucket_end_le_lms_bucket_start by auto
  with unchanged_slice[OF assms(1-3) `b \<le> _`]
  have "?xs = ?ys"
    by blast
  then show "ordlistns.sorted (map (suffix T) ?ys)"
    by (metis \<open>b \<le> \<alpha> (Max (set T))\<close> assms(4) l_suffix_sorted_pre_def)
qed

lemma l_prefix_sorted_pre_maintained:
  assumes "l_unchanged_inv \<alpha> T SA0 SA"
  and     "length SA = length SA0"
  and     "length SA = length T"
  and     "l_prefix_sorted_pre \<alpha> T SA0"
shows "l_prefix_sorted_pre \<alpha> T SA"
  unfolding l_prefix_sorted_pre_def
proof (safe)
  fix b
  assume "b \<le> \<alpha> (Max (set T))"
  let ?xs = "list_slice SA0 (lms_bucket_start \<alpha> T b) (bucket_end \<alpha> T b)" and
      ?ys = "list_slice SA (lms_bucket_start \<alpha> T b) (bucket_end \<alpha> T b)"

  have "l_bucket_end \<alpha> T b \<le> lms_bucket_start \<alpha> T b"
    using l_bucket_end_le_lms_bucket_start by auto
  with unchanged_slice[OF assms(1-3) `b \<le> _`]
  have "?xs = ?ys"
    by blast
  then show "ordlistns.sorted (map (lms_prefix T) ?ys)"
    by (metis \<open>b \<le> \<alpha> (Max (set T))\<close> assms(4) l_prefix_sorted_pre_def)
qed

lemma unknown_range_values:
  assumes "l_unchanged_inv \<alpha> T SA0 SA"
  and     "l_unknowns_inv \<alpha> T B SA"
  and     "length SA = length SA0"
  and     "length SA = length T"
  and     "lms_init \<alpha> T SA0"
  and     "s_init \<alpha> T SA0"
  and     "b \<le> \<alpha> (Max (set T))"
  and     "B ! b \<le> i"
  and     "i < lms_bucket_start \<alpha> T b"
shows "SA ! i = length T"
proof -
  have "i < length T"
    by (meson assms(9) bucket_end_le_length leD le_less_linear le_less_trans lms_bucket_start_le_bucket_end)
  hence "i < length SA"
    by (simp add: assms(4))

  have "i < l_bucket_end \<alpha> T b \<or> l_bucket_end \<alpha> T b \<le> i"
    using not_less by blast
  moreover
  have "i < l_bucket_end \<alpha> T b \<Longrightarrow> ?thesis"
  proof -
    assume "i < l_bucket_end \<alpha> T b"
    with l_unknowns_inv_D[OF assms(2,7,8)]
    show ?thesis .
  qed
  moreover
  have "l_bucket_end \<alpha> T b \<le> i \<Longrightarrow> ?thesis"
  proof -
    assume "l_bucket_end \<alpha> T b \<le> i"
    with s_init_D[OF s_init_unchanged[OF assms(1,3-4,6)] assms(7) `i < length SA` _ assms(9)]
    show ?thesis .
  qed
  ultimately show ?thesis
    by blast
qed

subsection "Bucket Values"

lemma same_bucket_same_hd:
  assumes "l_unchanged_inv \<alpha> T SA0 SA"
  and     "l_locations_inv \<alpha> T B SA"
  and     "l_bucket_ptr_inv \<alpha> T B SA"
  and     "l_unknowns_inv \<alpha> T B SA"
  and     "length SA = length T"
  and     "length SA = length SA0"
  and     "lms_init \<alpha> T SA0"
  and     "s_init \<alpha> T SA0"
  and     "b \<le> \<alpha> (Max (set T))"
  and     "i < length SA"
  and     "SA ! i < length T"
  and     "bucket_start \<alpha> T b \<le> i"
  and     "i < bucket_end \<alpha> T b"
  shows "\<alpha> (T ! (SA ! i)) = b"
proof -
  have "i < B ! b \<or> B ! b \<le> i"
    by linarith
  then show ?thesis
  proof
    assume "i < B ! b"
    from l_locations_inv_D[OF `l_locations_inv \<alpha> T B SA`
                          `b \<le> \<alpha> (Max (set T))`
                          `i < length SA`
                          `bucket_start \<alpha> T b \<le> i`
                          `i < B ! b`]
    show ?thesis
      by blast
  next
    assume "B ! b \<le> i"

    from `i < length SA` `length SA = length SA0`
    have "i < length SA0"
      by simp

    have "lms_bucket_start \<alpha> T b \<le> i"
    proof -
      have "i < l_bucket_end \<alpha> T b \<longrightarrow> SA ! i = length T"
      proof
        assume "i < l_bucket_end \<alpha> T b"
        from l_unknowns_inv_D[OF `l_unknowns_inv \<alpha> T B SA`
                                 `b \<le> \<alpha> (Max (set T))`
                                 `B ! b \<le> i`
                                 `i < l_bucket_end \<alpha> T b`]
        show "SA ! i = length T"
          by assumption
      qed

      have "l_bucket_end \<alpha> T b \<le> i \<and> i < lms_bucket_start \<alpha> T b \<longrightarrow> SA ! i = length T"
      proof (intro impI; elim conjE)
        assume "i < lms_bucket_start \<alpha> T b"
               "l_bucket_end \<alpha> T b \<le> i"

        from `s_init \<alpha> T SA0`
             `l_bucket_end \<alpha> T b \<le> i`
             `i < lms_bucket_start \<alpha> T b`
             `b \<le> \<alpha> (Max (set T))`
             `i < length SA0`
        have "SA0 ! i = length T"
          by (metis s_init_def)
        with l_unchanged_inv_D[OF `l_unchanged_inv \<alpha> T SA0 SA`
                                      `length SA = length SA0`
                                      `b \<le> \<alpha> (Max (set T))`
                                      `i < length SA0`
                                      `l_bucket_end \<alpha> T b \<le> i`
                                      `i < bucket_end \<alpha> T b`]
        show "SA ! i = length T"
          by simp
      qed

      from `i < l_bucket_end \<alpha> T b \<longrightarrow> SA ! i = length T`
           `l_bucket_end \<alpha> T b \<le> i \<and> i < lms_bucket_start \<alpha> T b \<longrightarrow> SA ! i = length T`
           `SA ! i < length T`
      show "lms_bucket_start \<alpha> T b \<le> i"
        by auto
    qed
    hence "l_bucket_end \<alpha> T b \<le> i"
      using l_bucket_end_le_lms_bucket_start le_trans by blast

    from `length SA = length T`
    have "bucket_end \<alpha> T b \<le> length SA"
      by (simp add: bucket_end_le_length)
    with `lms_init \<alpha> T SA0`
         `lms_bucket_start \<alpha> T b \<le> i`
         `i < bucket_end \<alpha> T b`
         `b \<le> \<alpha> (Max (set T))`
         `length SA = length SA0`
    have "SA0 ! i \<in> lms_bucket \<alpha> T b"
      by (metis list_slice_nth_mem lms_init_def)
    with l_unchanged_inv_D[OF `l_unchanged_inv \<alpha> T SA0 SA`
                                  `length SA = length SA0`
                                  `b \<le> \<alpha> (Max (set T))`
                                  `i < length SA0`
                                  `l_bucket_end \<alpha> T b \<le> i`
                                  `i < bucket_end \<alpha> T b`]
    have "SA ! i \<in> lms_bucket \<alpha> T b"
      by simp
    then show ?thesis
      by (simp add: bucket_def lms_bucket_def)
  qed
qed

lemma same_hd_same_bucket:
  assumes "l_unchanged_inv \<alpha> T SA0 SA"
  and     "l_locations_inv \<alpha> T B SA"
  and     "l_bucket_ptr_inv \<alpha> T B SA"
  and     "l_unknowns_inv \<alpha> T B SA"
  and     "strict_mono \<alpha>"
  and     "length SA = length T"
  and     "length SA = length SA0"
  and     "lms_init \<alpha> T SA0"
  and     "s_init \<alpha> T SA0"
  and     "i < length SA"
  and     "SA ! i < length T"
  and     "b = \<alpha> (T ! (SA ! i))"
  shows "bucket_start \<alpha> T b \<le> i \<and> i < bucket_end \<alpha> T b"
proof -
  from `length SA = length T` `i < length SA`
  have "i < length T"
    by simp
  from index_in_bucket_interval_gen[OF `i < length T`  `strict_mono \<alpha>`]
  obtain b' where
    "b' \<le> \<alpha> (Max (set T))"
    "bucket_start \<alpha> T b' \<le> i"
    "i < bucket_end \<alpha> T b'"
    by blast

  from same_bucket_same_hd[OF `l_unchanged_inv \<alpha> T SA0 SA`
                              `l_locations_inv \<alpha> T B SA`
                              `l_bucket_ptr_inv \<alpha> T B SA`
                              `l_unknowns_inv \<alpha> T B SA`
                              `length SA = length T`
                              `length SA = length SA0`
                              `lms_init \<alpha> T SA0`
                              `s_init \<alpha> T SA0`
                              `b' \<le> \<alpha> (Max (set T))`
                              `i < length SA`
                              `SA ! i < length T`
                              `bucket_start \<alpha> T b' \<le> i`
                              `i < bucket_end \<alpha> T b'`]
       `b = \<alpha> (T ! (SA ! i))`
       `bucket_start \<alpha> T b' \<le> i`
       `i < bucket_end \<alpha> T b'`
  show ?thesis
    by blast
qed


lemma less_bucket_less_hd:
  assumes "l_unchanged_inv \<alpha> T SA0 SA"
  and     "l_locations_inv \<alpha> T B SA"
  and     "l_bucket_ptr_inv \<alpha> T B SA"
  and     "l_unknowns_inv \<alpha> T B SA"
  and     "strict_mono \<alpha>"
  and     "length SA = length T"
  and     "length SA = length SA0"
  and     "lms_init \<alpha> T SA0"
  and     "s_init \<alpha> T SA0"
  and     "i < length SA"
  and     "SA ! i < length T"
  and     "i < bucket_start \<alpha> T b"
  shows "\<alpha> (T ! (SA ! i)) < b"
proof -
  from same_hd_same_bucket[OF `l_unchanged_inv \<alpha> T SA0 SA`
                              `l_locations_inv \<alpha> T B SA`
                              `l_bucket_ptr_inv \<alpha> T B SA`
                              `l_unknowns_inv \<alpha> T B SA`
                              `strict_mono \<alpha>`
                              `length SA = length T`
                              `length SA = length SA0`
                              `lms_init \<alpha> T SA0`
                              `s_init \<alpha> T SA0`
                              `i < length SA`
                              `SA ! i < length T`,
                            of "\<alpha> (T ! (SA ! i))"]
  have "bucket_start \<alpha> T (\<alpha> (T ! (SA ! i))) \<le> i \<and> i < bucket_end \<alpha> T (\<alpha> (T ! (SA ! i)))"
    by simp
  then show ?thesis
    by (meson `i < bucket_start \<alpha> T b` bucket_start_le leD le_less_linear le_trans)
qed

lemma gr_bucket_gr_hd:
  assumes "l_unchanged_inv \<alpha> T SA0 SA"
  and     "l_locations_inv \<alpha> T B SA"
  and     "l_bucket_ptr_inv \<alpha> T B SA"
  and     "l_unknowns_inv \<alpha> T B SA"
  and     "strict_mono \<alpha>"
  and     "length SA = length T"
  and     "length SA = length SA0"
  and     "lms_init \<alpha> T SA0"
  and     "s_init \<alpha> T SA0"
  and     "i < length SA"
  and     "SA ! i < length T"
  and     "bucket_end \<alpha> T b \<le> i"
  shows "b < \<alpha> (T ! (SA ! i))"
proof -
  from same_hd_same_bucket[OF `l_unchanged_inv \<alpha> T SA0 SA`
                              `l_locations_inv \<alpha> T B SA`
                              `l_bucket_ptr_inv \<alpha> T B SA`
                              `l_unknowns_inv \<alpha> T B SA`
                              `strict_mono \<alpha>`
                              `length SA = length T`
                              `length SA = length SA0`
                              `lms_init \<alpha> T SA0`
                              `s_init \<alpha> T SA0`
                              `i < length SA`
                              `SA ! i < length T`,
                            of "\<alpha> (T ! (SA ! i))"]
  have "bucket_start \<alpha> T (\<alpha> (T ! (SA ! i))) \<le> i \<and> i < bucket_end \<alpha> T (\<alpha> (T ! (SA ! i)))"
    by simp
  then show ?thesis
    by (meson `bucket_end \<alpha> T b \<le> i` bucket_end_le leD le_less_linear less_le_trans)
qed

subsection "Seen"
text "We have two helper lemmas in the case of updating the suffix array SA,
      and in the case when the current index is incremented.
      The two lemmas are used in conjunction in the case that the SA is updated and
      the current index is incremented."

lemma l_seen_inv_upd:
  assumes "l_seen_inv T SA n" "n \<le> k" "SA ! k = length T"
  shows "l_seen_inv T (SA[k := x]) n"
  unfolding l_seen_inv_def
proof safe
  fix i j
  assume A: "i < n" "i < length (SA[k := x])" "SA[k := x] ! i < length T" "SA[k := x] ! i = Suc j"
             "suffix_type T j = L_type"
  hence "i \<noteq> k"
    using assms(2) leD by blast
  hence B: "i < length SA" "SA ! i < length T" "SA ! i = Suc j"
    using A by auto
  with l_seen_inv_nth_ex[OF assms(1) A(1) B A(5)]
  have "\<exists>k'<length SA. SA ! k' = j"
    by blast
  then obtain k' where
    "k' < length SA" "SA ! k' = j"
    by blast
  then show "\<exists>k'<length (SA[k := x]). SA[k := x] ! k' = j"
    by (metis B(2,3) Suc_lessD assms(3) length_list_update less_irrefl_nat nth_list_update_neq)
qed

lemma l_seen_inv_Suc:
  assumes "l_seen_inv T SA n" "SA ! n = Suc j" "k < length SA" "SA ! k = j"
  shows "l_seen_inv T SA (Suc n)"
  unfolding l_seen_inv_def
proof safe
  fix i j'
  assume A: "i < Suc n" "i < length SA" "SA ! i < length T" "SA ! i = Suc j'"
            "suffix_type T j' = L_type"
  have "i < n \<or> \<not> i < n"
    by blast
  then show "\<exists>k<length SA. SA ! k = j'"
  proof
    assume "i < n"
    with l_seen_inv_nth_ex[OF assms(1) _ A(2-)]
    show "\<exists>k<length SA. SA ! k = j'"
      by blast
  next
    assume "\<not> i < n"
    then show "\<exists>k<length SA. SA ! k = j'"
      using A(1) A(4) assms(2-) not_less_less_Suc_eq by force
  qed
qed

section "Distinctness"

lemma distinct_app3:
  "distinct (xs @ ys @ zs) \<longleftrightarrow>
     distinct xs \<and> distinct ys \<and> distinct zs \<and>
     set xs \<inter> set ys = {} \<and> set xs \<inter> set zs = {} \<and> set ys \<inter> set zs = {}"
  by auto

subsection "Establishment"

lemma abs_is_lms_imp_in_lms_bucket:
  "abs_is_lms T i \<Longrightarrow> i \<in> lms_bucket \<alpha> T (\<alpha> (T ! i))"
  apply (clarsimp simp: lms_bucket_def bucket_def)
  by (simp add: abs_is_lms_def suffix_type_s_bound)

lemma l_distinct_inv_established:
  assumes "lms_init \<alpha> T SA"
  and     "l_init \<alpha> T SA"
  and     "s_init \<alpha> T SA"
  and     "length SA = length T"
  and     "strict_mono \<alpha>"
  and     "l_bucket_init \<alpha> T B"
  shows "l_distinct_inv T SA"
  unfolding l_distinct_inv_def
proof (intro  distinct_conv_nth[THEN iffD2] allI impI)
  let ?P = "(\<lambda>x. x < length T)"
  let ?SA = "filter (\<lambda>x. x < length T) SA"

  fix i j
  assume "i < length ?SA" "j < length ?SA" "i \<noteq> j"

  from `i < length ?SA`
  have "?SA ! i < length T"
    using mem_Collect_eq nth_mem by fastforce

  from `j < length ?SA`
  have "?SA ! j < length T"
    using mem_Collect_eq nth_mem by fastforce

  from filter_nth_relative_neq_2[OF `i < length ?SA` `j < length ?SA` `i \<noteq> j`]
  obtain i' j' where
    "i' < length SA"
    "j' < length SA"
    "SA ! i' = ?SA ! i"
    "SA ! j' = ?SA ! j"
    "i' \<noteq> j'"
    by blast

  from `?SA ! i < length T` `SA ! i' = ?SA ! i`
  have "SA ! i' < length T"
    by simp

  from `?SA ! j < length T` `SA ! j' = ?SA ! j`
  have "SA ! j' < length T"
    by simp

  from init_imp_lms_range assms `i' < length SA` `SA ! i' < length T`
  have "lms_bucket_start \<alpha> T (\<alpha> (T ! (SA ! i'))) \<le> i'" "i' < bucket_end \<alpha> T (\<alpha> (T ! (SA ! i')))"
    by blast+

  from init_imp_lms_range assms `j' < length SA` `SA ! j' < length T`
  have "lms_bucket_start \<alpha> T (\<alpha> (T ! (SA ! j'))) \<le> j'" "j' < bucket_end \<alpha> T (\<alpha> (T ! (SA ! j')))"
    by blast+

  have "\<alpha> (T ! (SA ! i')) = \<alpha> (T ! (SA ! j')) \<or> \<alpha> (T ! (SA ! i')) \<noteq> \<alpha> (T ! (SA ! j'))"
    by simp
  then show "?SA ! i \<noteq> ?SA ! j"
  proof
    assume "\<alpha> (T ! (SA ! i')) = \<alpha> (T ! (SA ! j'))"
    with `lms_bucket_start \<alpha> T (\<alpha> (T ! (SA ! i'))) \<le> i'`
    have "lms_bucket_start \<alpha> T (\<alpha> (T ! (SA ! j'))) \<le> i'"
      by simp

    from `\<alpha> (T ! (SA ! i')) = \<alpha> (T ! (SA ! j'))`
         `i' < bucket_end \<alpha> T (\<alpha> (T ! (SA ! i')))`
    have "i' < bucket_end \<alpha> T (\<alpha> (T ! (SA ! j')))"
      by simp

    with list_slice_nth_eq_iff_index_eq[OF lms_init_imp_distinct_bucket,
                                        OF `lms_init \<alpha> T SA`
                                           _
                                           `length SA = length T`
                                           _
                                           `lms_bucket_start \<alpha> T (\<alpha> (T ! (SA ! j'))) \<le> i'`
                                           _
                                           `lms_bucket_start \<alpha> T (\<alpha> (T ! (SA ! j'))) \<le> j'`
                                           `j' < bucket_end \<alpha> T (\<alpha> (T ! (SA ! j')))`]
         `i' \<noteq> j'`
         `length SA = length T`
         `SA ! j' < length T`
         `strict_mono \<alpha>`
    have "SA ! i' \<noteq> SA ! j'"
      by (simp add: bucket_end_le_length strict_mono_less_eq)
    with `SA ! i' = ?SA ! i` `SA ! j' = ?SA ! j`
    show ?thesis
      by simp
  next
    assume "\<alpha> (T ! (SA ! i')) \<noteq> \<alpha> (T ! (SA ! j'))"
    with `SA ! i' = ?SA ! i` `SA ! j' = ?SA ! j`
    show ?thesis
      by auto
  qed
qed

corollary l_distinct_inv_perm_established:
  assumes "l_perm_pre \<alpha> T B SA"
  shows "l_distinct_inv T SA"
  using assms l_distinct_inv_established l_perm_pre_def by blast

subsection "Maintenance"

lemma l_distinct_inv_maintained:
  assumes "i < length SA"
  and     "SA ! i = Suc j"
  and     "Suc j < length T"
  and     "suffix_type T j = L_type"
  and     "l_distinct_inv T SA"
  and     "l_pred_inv T SA i"
  shows "l_distinct_inv T (SA[l := j])"
proof -
  let ?P = "(\<lambda>x. x < length T)"

  from `Suc j < length T`
  have "j < length T"
    by simp

  \<comment>\<open> We case on whether the update occurs on an index within bounds \<close>
  have "l < length SA \<or> l \<ge> length SA"
    by arith
  then show ?thesis
  proof
    assume "l < length SA"

    from l_distinct_pred_inv_helper[OF `i < length SA`
                                       `SA ! i = Suc j`
                                       `Suc j < length T`
                                       `suffix_type T j = L_type`
                                       `l_distinct_inv T SA`
                                       `l_pred_inv T SA i`]
    have "j \<notin> set SA"
      by assumption

    let ?xs = "filter ?P (take l SA)" and
        ?ys = "filter ?P (drop (Suc l) SA)"
    \<comment>\<open> We have that @{term "j \<notin> set SA"} and show that if we now add @{term j} to
        @{term SA}, it will maintain distinctness.
        This is straightforward but does require some massaging,
        i.e. casing on whether @{term "SA ! l < length T"} or not,
        due to the use of @{term filter} in the @{thm l_distinct_inv_def} definition. \<close>

    from `j < length T` `l < length SA`
    have f_SA': "filter ?P (SA[l := j]) = ?xs @ [j] @ ?ys"
      by (simp add: filter_update_nth_success)

    from `j \<notin> set SA`
    have "set ?xs \<inter> set [j] = {}"
      using in_set_takeD by fastforce

    from `j \<notin> set SA`
    have "set [j] \<inter> set ?ys = {}"
      using in_set_dropD by force

    have "SA ! l < length T \<or> SA ! l \<ge> length T"
      by arith
    then show ?thesis
    proof
      assume "SA ! l < length T"
      with `l < length SA`
      have f_SA: "filter ?P SA = ?xs @ [SA ! l] @ ?ys"
        by (meson filter_take_nth_drop_success)

      from f_SA `l_distinct_inv T SA` distinct_app3[of ?xs "[SA ! l]" ?ys]
      have "distinct ?xs"
           "distinct ?ys"
           "set ?xs \<inter> set ?ys = {}"
        unfolding l_distinct_inv_def
        by auto

      with `set ?xs \<inter> set [j] = {}`
           `set [j] \<inter> set ?ys = {}`
           f_SA'
      show ?thesis
        unfolding l_distinct_inv_def
        by auto
    next
      assume "SA ! l \<ge> length T"
      with `l < length SA`
      have f_SA: "filter ?P SA = ?xs @ ?ys"
        by (simp add: filter_take_nth_drop_fail)

      from f_SA `l_distinct_inv T SA` distinct_append[of ?xs ?ys]
      have "distinct ?xs"
           "distinct ?ys"
           "set ?xs \<inter> set ?ys = {}"
        unfolding l_distinct_inv_def
        by auto
      with `set ?xs \<inter> set [j] = {}`
           `set [j] \<inter> set ?ys = {}`
           f_SA'
      show ?thesis
        unfolding l_distinct_inv_def
        by auto
    qed
  next
    \<comment>\<open> We now handle the case @{term "l \<ge> length SA"}, which is straightforward.
       In the actual @{const abs_induce_l} subroutine, @{term l} will always be less than
       @{term "length SA"}, but for this proof, we make no such assumption,
       nor do we need to prove it. \<close>
    assume "l \<ge> length SA"
    hence "SA[l := j] = SA"
      by simp
    with `l_distinct_inv T SA`
    show ?thesis
      by simp
  qed
qed

corollary l_distinct_inv_perm_maintained:
  assumes "l_perm_inv \<alpha> T B SA0 SA i"
  and     "i < length SA"
  and     "SA ! i = Suc j"
  and     "Suc j < length T"
  and     "suffix_type T j = L_type"
shows "l_distinct_inv T (SA[l := j])"
  by (meson assms l_distinct_inv_maintained l_perm_inv_elims(4,10))

section "Unknowns"

subsection "Establishment"

lemma l_unknowns_inv_established:
  assumes "l_init \<alpha> T SA"
          "l_bucket_init \<alpha> T B"
          "length SA = length T"
  shows "l_unknowns_inv \<alpha> T B SA"
  unfolding l_unknowns_inv_def
proof (intro allI impI; elim conjE)
  fix a k
  assume "a \<le> \<alpha> (Max (set T))"
         "B ! a \<le> k"
         "k < l_bucket_end \<alpha> T a"

  from `B ! a \<le> k` l_bucket_initD[OF `l_bucket_init \<alpha> T B` `a \<le> \<alpha> (Max (set T))`]
  have "bucket_start \<alpha> T a \<le> k"
    by simp

  from `length SA = length T` `k < l_bucket_end \<alpha> T a`
  have "k < length SA"
    by (metis bucket_end_le_length l_bucket_end_le_bucket_end less_le_trans)

  from l_init_D[OF `l_init \<alpha> T SA`
                   `a \<le> \<alpha> (Max (set T))`
                   `k < length SA`
                   `bucket_start \<alpha> T a \<le> k`
                   `k < l_bucket_end \<alpha> T a`]
  show "SA ! k = length T"
    by assumption
qed

corollary l_unknowns_inv_perm_established:
  assumes "l_perm_pre \<alpha> T B SA"
  shows "l_unknowns_inv \<alpha> T B SA"
  using assms l_perm_pre_elims(2,4,7) l_unknowns_inv_established by blast

subsection "Maintenance"

lemma l_unknowns_inv_maintained:
  assumes "l_unknowns_inv \<alpha> T B SA"
  and     "length B > \<alpha> (Max (set T))"
  and     "i < length SA"
  and     "SA ! i = Suc j"
  and     "Suc j < length T"
  and     "suffix_type T j = L_type"
  and     "k = \<alpha> (T ! j)"
  and     "l = B ! k"
  and     "strict_mono \<alpha>"
  and     "l_distinct_inv T SA"
  and     "l_pred_inv T SA i"
  and     "l_bucket_ptr_inv \<alpha> T B SA"
  shows "l_unknowns_inv \<alpha> T (B[k := Suc (B ! k)]) (SA[l := j])"
  unfolding l_unknowns_inv_def
proof (intro allI impI; elim conjE)
  fix a k'
  assume "a \<le> \<alpha> (Max (set T))"
         "B[k := Suc (B ! k)] ! a \<le> k'"
         "k' < l_bucket_end \<alpha> T a"

  from l_distinct_pred_inv_helper[OF `i < length SA`
                                     `SA ! i = Suc j`
                                     `Suc j < length T`
                                     `suffix_type T j = L_type`
                                     `l_distinct_inv T SA`
                                     `l_pred_inv T SA i`]
  have "j \<notin> set SA"
    by assumption

  from `Suc j < length T`
  have "j < length T"
    by simp

  from l_unknowns_l_bucket_ptr_inv_helper[OF `l_unknowns_inv \<alpha> T B SA`
                                        `l_bucket_ptr_inv \<alpha> T B SA`
                                        `j < length T`
                                        `suffix_type T j = L_type`
                                        `j \<notin> set SA`
                                        `strict_mono \<alpha>`
                                        `k = \<alpha> (T ! j)`
                                        `l = B ! k`]
  have "SA ! l = length T"
    by assumption

  from `strict_mono \<alpha>` `k = \<alpha> (T ! j)` `j < length T`
  have "k \<le> \<alpha> (Max (set T))"
    by (simp add: strict_mono_leD)

  from l_unknowns_inv_D[OF `l_unknowns_inv \<alpha> T B SA`
                           `a \<le> \<alpha> (Max (set T))`
                           _
                           `k' < l_bucket_end \<alpha> T a`]
       `B[k := Suc (B ! k)] ! a \<le> k'`
       `a \<le> \<alpha> (Max (set T))`
       `\<alpha> (Max (set T)) < length B`
  have "SA ! k' = length T"
    by (metis Suc_le_mono le_SucI le_less_trans nth_list_update nth_list_update_neq)

  from `j < length T` `strict_mono \<alpha>` `l_bucket_ptr_inv \<alpha> T B SA` `k = \<alpha> (T ! j)` `l = B ! k`
  have "bucket_start \<alpha> T k \<le> l"
    using Max_greD l_bucket_ptr_inv_imp_ge_bucket_start strict_mono_less_eq by blast

  from `j < length T`
       `j \<notin> set SA`
       `strict_mono \<alpha>`
       `l_bucket_ptr_inv \<alpha> T B SA`
       `suffix_type T j = L_type`
       `k = \<alpha> (T ! j)`
       `l = B ! k`
  have "l < l_bucket_end \<alpha> T k"
    using  l_bucket_ptr_inv_imp_less_l_bucket_end by blast

  have "a = k \<or> a \<noteq> k"
    by simp
  then show "SA[l := j] ! k' = length T "
  proof
    assume "a = k"
    hence "k' \<noteq> l"
      using `B[k := Suc (B ! k)] ! a \<le> k'` `a \<le> \<alpha> (Max (set T))` `\<alpha> (Max (set T)) < length B`
            `l = B ! k` by auto
    then show ?thesis
      using `SA ! k' = length T` by auto
  next
    assume "a \<noteq> k"
    hence "a < k \<or> a > k"
      by arith
    then show ?thesis
    proof
      assume "a < k"

      from less_bucket_end_le_start[OF `a < k`]
      have "bucket_end \<alpha> T a \<le> bucket_start \<alpha> T k"
        by blast
      with `bucket_start \<alpha> T k \<le> l`
      have "bucket_end \<alpha> T a \<le> l"
        by simp
      with l_bucket_end_le_bucket_end
      have "l_bucket_end \<alpha> T a \<le> l"
        using le_trans by blast
      with `k' < l_bucket_end \<alpha> T a`
      have "k' < l"
        using less_le_trans by blast
      then show ?thesis
        using \<open>SA ! k' = length T\<close> by auto
    next
      assume "a > k"

      from `B[k := Suc (B ! k)] ! a \<le> k'`
           `a \<le> \<alpha> (Max (set T))`
           `a \<noteq> k`
           `l_bucket_ptr_inv \<alpha> T B SA`
           l_bucket_ptr_inv_imp_ge_bucket_start
      have "bucket_start \<alpha> T a \<le> k'"
        by force

      from less_bucket_end_le_start[OF `k < a`]
      have "bucket_end \<alpha> T k \<le> bucket_start \<alpha> T a"
        by blast
      with `bucket_start \<alpha> T a \<le> k'`
      have "bucket_end \<alpha> T k \<le> k'"
        by simp
      with l_bucket_end_le_bucket_end
      have "l_bucket_end \<alpha> T k \<le> k'"
        using le_trans by blast
      with `l < l_bucket_end \<alpha> T k`
      have "l < k'"
        using less_le_trans by blast
      then show ?thesis
        using \<open>SA ! k' = length T\<close> by auto
    qed
  qed
qed

corollary l_unknowns_inv_perm_maintained:
  assumes "l_perm_inv \<alpha> T B SA0 SA i"
  and     "i < length SA"
  and     "SA ! i = Suc j"
  and     "Suc j < length T"
  and     "suffix_type T j = L_type"
  and     "k = \<alpha> (T ! j)"
  and     "l = B ! k"
shows "l_unknowns_inv \<alpha> T (B[k := Suc (B ! k)]) (SA[l := j])"
  by (metis assms l_perm_inv_elims(1,4-6,10,12) l_unknowns_inv_maintained)

section "Number of L-types"

subsection "Establishment"

text "We first prove that this invariant is established from the precondition,
      i.e., that initially, there are only LMS-types, which are just a special type of S-types,
      and that the initial pointer is the start of the bucket."

lemma l_bucket_ptr_inv_established:
  assumes "lms_init \<alpha> T SA"
  and     "l_init \<alpha> T SA"
  and     "s_init \<alpha> T SA"
  and     "length SA = length T"
  and     "strict_mono \<alpha>"
  and     "l_bucket_init \<alpha> T B"
  shows "l_bucket_ptr_inv \<alpha> T B SA"
proof -
  have "\<forall>b \<le> \<alpha> (Max (set T)). cur_l_types \<alpha> T SA b = {}"
    unfolding cur_l_types_def
  proof (intro allI impI equalityI subsetI)
    fix b x
    assume "x \<in> {i |i. i \<in> set SA \<and> i \<in> l_bucket \<alpha> T b}"
    hence "x \<in> set SA" "x \<in> l_bucket \<alpha> T b"
      by blast+

    have "x < length T \<or> x \<ge> length T"
      using not_less by blast
    then show "x \<in> {}"
    proof
      assume "x < length T"
      with `x \<in> set SA` init_imp_only_s_types assms
      have "suffix_type T x = S_type"
        by (metis in_set_conv_nth)
      hence "x \<notin> l_bucket \<alpha> T b"
        by (simp add: l_bucket_def)
      with `x \<in> l_bucket \<alpha> T b`
      show ?thesis
        by blast
    next
      assume  "length T \<le> x"
      hence "x \<notin> l_bucket \<alpha> T b"
        by (simp add: bucket_def l_bucket_def)
      with `x \<in> l_bucket \<alpha> T b`
      show ?thesis
        by blast
    qed
  next
    fix b :: nat
    fix x :: nat
    assume "x \<in> {}"
    then show "x \<in> {i |i. i \<in> set SA \<and> i \<in> l_bucket \<alpha> T b}"
      by blast
  qed
  hence "\<forall>b \<le> \<alpha> (Max (set T)). num_l_types \<alpha> T SA b = 0"
    by (simp add: num_l_types_def)
  with `l_bucket_init \<alpha> T B`
  show ?thesis
    by (simp add: l_bucket_ptr_inv_def l_bucket_init_def)
qed

corollary l_bucket_ptr_inv_perm_established:
  assumes "l_perm_pre \<alpha> T B SA"
  shows "l_bucket_ptr_inv \<alpha> T B SA"
  using assms l_bucket_ptr_inv_established l_perm_pre_def by blast

subsection "Maintenance"

text "We now prove that the invariant is maintained."

lemma set_update_mem_neqI:
  "\<lbrakk>x \<in> set xs; xs ! i \<noteq> x\<rbrakk> \<Longrightarrow> x \<in> set (xs[i := y])"
  by (metis in_set_conv_nth length_list_update nth_list_update_neq)

lemma cur_l_types_update_1:
  "\<lbrakk>SA ! l = length T; l < length SA; j \<notin> set SA; suffix_type T j = L_type; j < length T;
    \<alpha> (T ! j) = b\<rbrakk> \<Longrightarrow>
    cur_l_types \<alpha> T (SA[l := j]) b = insert j (cur_l_types \<alpha> T SA b)"
  apply (intro equalityI subsetI)
   apply (metis (no_types, lifting) cur_l_types_def in_set_conv_nth insertCI length_list_update
                                    mem_Collect_eq nth_list_update nth_list_update_neq)
  by (metis (mono_tags, lifting) bucket_def cur_l_types_def insert_iff l_bucket_def
                                 less_irrefl_nat mem_Collect_eq set_update_memI set_update_mem_neqI)

lemma cur_l_types_update_2:
  assumes "SA ! l = length T" "\<alpha> (T ! j) \<noteq> b"
  shows "cur_l_types \<alpha> T (SA[l := j]) b = cur_l_types \<alpha> T SA b"
proof (cases "l < length SA")
  assume "l < length SA"
  show ?thesis
  proof safe
    fix x
    assume "x \<in> cur_l_types \<alpha> T (SA[l := j]) b"
    show "x \<in> cur_l_types \<alpha> T SA b"
    proof (cases "x = j")
      assume "x = j"
      then show ?thesis
        using \<open>x \<in> cur_l_types \<alpha> T (SA[l := j]) b\<close> assms(2) bucket_def cur_l_types_def l_bucket_def
        by fastforce
    next
      assume "x \<noteq> j"
      then show ?thesis
        by (metis (no_types, lifting) \<open>x \<in> cur_l_types \<alpha> T (SA[l := j]) b\<close> cur_l_types_def
                                      in_set_conv_nth length_list_update mem_Collect_eq
                                      nth_list_update nth_list_update_neq)
    qed
  next
    fix x
    assume "x \<in> cur_l_types \<alpha> T SA b"
    then show "x \<in> cur_l_types \<alpha> T (SA[l := j]) b"
      by (simp add: assms(1) bucket_def cur_l_types_def l_bucket_def set_update_mem_neqI)
  qed
next
  assume "\<not> l < length SA"
  then show ?thesis
    by simp
qed

lemma num_l_types_update_1:
  "\<lbrakk>SA ! l = length T; l < length SA; j \<notin> set SA; suffix_type T j = L_type; j < length T;
    \<alpha> (T ! j) = b\<rbrakk> \<Longrightarrow>
    num_l_types \<alpha> T (SA[l := j]) b = Suc (num_l_types \<alpha> T SA b)"
  apply (clarsimp simp: num_l_types_def)
  apply (subst cur_l_types_update_1; simp?)
  apply (subst card_insert_disjoint)
    apply (metis (no_types, lifting) List.finite_set cur_l_types_def finite_nat_set_iff_bounded
                                     mem_Collect_eq)
   apply (simp add: cur_l_types_def)
  apply simp
  done

lemma num_l_types_update_2:
  "\<lbrakk>SA ! l = length T; \<alpha> (T ! j) \<noteq> b\<rbrakk> \<Longrightarrow>
    num_l_types \<alpha> T (SA[l := j]) b = num_l_types \<alpha> T SA b"
  apply (cases "l < length SA"; clarsimp?)
  apply (clarsimp simp: num_l_types_def)
  apply (intro arg_cong[where f = card])
  by (erule (1) cur_l_types_update_2)

lemma l_bucket_ptr_inv_maintained:
  assumes "l_bucket_ptr_inv \<alpha> T B SA"
  and     "length SA = length T"
  and     "length B > \<alpha> (Max (set T))"
  and     "i < length SA"
  and     "SA ! i = Suc j"
  and     "Suc j < length T"
  and     "suffix_type T j = L_type"
  and     "k = \<alpha> (T ! j)"
  and     "l = B ! k"
  and     "strict_mono \<alpha>"
  and     "l_distinct_inv T SA"
  and     "l_pred_inv T SA i"
  and     "l_unknowns_inv \<alpha> T B SA"
  shows "l_bucket_ptr_inv \<alpha> T (B[k := Suc (B ! k)]) (SA[l := j])"
  unfolding l_bucket_ptr_inv_def
proof safe
  fix b
  assume "b \<le> \<alpha> (Max (set T))"

  from l_distinct_pred_inv_helper[OF `i < length SA`
                                     `SA ! i = Suc j`
                                     `Suc j < length T`
                                     `suffix_type T j = L_type`
                                     `l_distinct_inv T SA`
                                     `l_pred_inv T SA i`]
  have "j \<notin> set SA"
    by assumption

  from `Suc j < length T`
  have "j < length T"
    by arith

  from l_unknowns_l_bucket_ptr_inv_helper[OF `l_unknowns_inv \<alpha> T B SA`
                                            `l_bucket_ptr_inv \<alpha> T B SA`
                                            `j < length T`
                                            `suffix_type T j = L_type`
                                            `j \<notin> set SA`
                                            `strict_mono \<alpha>`
                                            `k = \<alpha> (T ! j)`
                                            `l = B ! k`]
  have "SA ! l = length T"
    by assumption

  let ?G = "B[k := Suc (B ! k)] ! b = bucket_start \<alpha> T b + num_l_types \<alpha> T (SA[l := j]) b"
  have "b = k \<or> b \<noteq> k"
    by blast
  then show ?G
  proof
    assume "b = k"
    hence "B[k := Suc (B ! k)] ! b = Suc (B ! k)"
      using \<open>b \<le> \<alpha> (Max (set T))\<close> `length B > \<alpha> (Max (set T))` by auto

    from num_l_types_less_l_bucket_size[OF `j \<notin> set SA` `suffix_type T j = L_type`]
         `Suc j < length T`
         `b = k`
         `k = \<alpha> (T ! j)`
    have "num_l_types \<alpha> T SA b < l_bucket_size \<alpha> T b"
      by simp

    from `l_bucket_ptr_inv \<alpha> T B SA` \<open>b \<le> \<alpha> (Max (set T))\<close>
    have "B ! b = bucket_start \<alpha> T b + num_l_types \<alpha> T SA b"
      by (metis l_bucket_ptr_inv_def)
    with `num_l_types \<alpha> T SA b < l_bucket_size \<alpha> T b`
          bucket_end_le_length l_bucket_le_bucket_size bucket_end_def'
    have "B ! b < length T"
      by (metis add_less_cancel_left less_le_trans)
    with `k = \<alpha> (T ! j)` `b = k` `l = B ! k` `length SA = length T`
    have "l < length SA"
      by simp

    from `SA ! l = length T`
         `b = k`
         `b \<le> \<alpha> (Max (set T))`
         `j \<notin> set SA`
         `l < length SA`
         `k = \<alpha> (T ! j)`
         num_l_types_update_1
         `suffix_type T j = L_type`
         `Suc j < length T`
         Suc_lessD
    have "num_l_types \<alpha> T (SA[l := j]) b = Suc (num_l_types \<alpha> T SA b)"
      by blast
    from `B[k := Suc (B ! k)] ! b = Suc (B ! k)`
         `b = k`
         `b \<le> \<alpha> (Max (set T))`
         `num_l_types \<alpha> T (SA[l := j]) b = Suc (num_l_types \<alpha> T SA b)`
         `l_bucket_ptr_inv \<alpha> T B SA`
         l_bucket_ptr_inv_def
    show ?thesis
      by fastforce
  next
    assume "b \<noteq> k"
    hence "B[k := Suc (B ! k)] ! b = B ! b"
      by auto

    from num_l_types_update_2[OF `SA ! l = length T`]
         `b \<le> \<alpha> (Max (set T))`
         `b \<noteq> k`
         `k = \<alpha> (T ! j)`
    have "num_l_types \<alpha> T (SA[l := j]) b = num_l_types \<alpha> T SA b"
      by simp

    from `B[k := Suc (B ! k)] ! b = B ! b`
         `b \<le> \<alpha> (Max (set T))`
         `num_l_types \<alpha> T (SA[l := j]) b = num_l_types \<alpha> T SA b`
         `l_bucket_ptr_inv \<alpha> T B SA`
         l_bucket_ptr_inv_def
    show ?thesis
      by fastforce
  qed
qed

corollary l_bucket_ptr_inv_perm_maintained:
  assumes "l_perm_inv \<alpha> T B SA0 SA i"
  and     "i < length SA"
  and     "SA ! i = Suc j"
  and     "Suc j < length T"
  and     "suffix_type T j = L_type"
  and     "k = \<alpha> (T ! j)"
  and     "l = B ! k"
shows "l_bucket_ptr_inv \<alpha> T (B[k := Suc (B ! k)]) (SA[l := j])"
  by (metis assms l_bucket_ptr_inv_maintained l_perm_inv_elims(1,2,3-6,10,12))

section "L Locations"

subsection "Establishment"

lemma l_locations_inv_established:
  assumes "l_bucket_init \<alpha> T B"
  shows "l_locations_inv \<alpha> T B SA"
  using assms l_bucket_initD l_locations_inv_def by fastforce

corollary l_locations_inv_perm_established:
  assumes "l_perm_pre \<alpha> T B SA"
  shows "l_locations_inv \<alpha> T B SA"
  using assms l_locations_inv_established l_perm_pre_elims(4) by blast

subsection "Maintenance"

lemma l_locations_inv_maintained:
  assumes "l_locations_inv \<alpha> T B SA"
  and     "length B > \<alpha> (Max (set T))"
  and     "i < length SA"
  and     "SA ! i = Suc j"
  and     "Suc j < length T"
  and     "suffix_type T j = L_type"
  and     "k = \<alpha> (T ! j)"
  and     "l = B ! k"
  and     "strict_mono \<alpha>"
  and     "l_distinct_inv T SA"
  and     "l_pred_inv T SA i"
  and     "l_bucket_ptr_inv \<alpha> T B SA"
  shows "l_locations_inv \<alpha> T (B[k := Suc (B ! k)]) (SA[l := j])"
  unfolding l_locations_inv_def
proof (intro allI impI; elim conjE)
  fix b i'
  assume "b \<le> \<alpha> (Max (set T))"
         "i' < length (SA[l := j])"
         "bucket_start \<alpha> T b \<le> i'"
         "i' < B[k := Suc (B ! k)] ! b"
  hence "i' < length SA"
    by simp

  have "b = k \<or> b \<noteq> k"
    by blast
  then
  show "SA[l := j] ! i' < length T \<and> suffix_type T (SA[l := j] ! i') = L_type \<and>
       \<alpha> (T ! (SA[l := j] ! i')) = b"
  proof
    assume "b = k"
    with `bucket_start \<alpha> T b \<le> i'`
    have "bucket_start \<alpha> T k \<le> i'"
      by simp

    from `b = k` `i' < B[k := Suc (B ! k)] ! b`
    have "i' < Suc (B ! k)"
      using \<open>b \<le> \<alpha> (Max (set T))\<close> `length B > \<alpha> (Max (set T))` by auto
    hence "i' < B ! k \<or> i' = B ! k"
      by (simp add: less_Suc_eq)
    then show ?thesis
    proof
      assume "i' < B ! k"
      with `l = B ! k` `b = k` `b \<le> \<alpha> (Max (set T))` `bucket_start \<alpha> T k \<le> i'` `i' < length SA`
      show ?thesis
        using `l_locations_inv \<alpha> T B SA` l_locations_inv_def by fastforce
    next
      assume "i' = B ! k"
      with `l = B ! k`
      have "i' = l"
        by simp

      from `i' < length SA` `i' = l`
      have "SA[l := j] ! i' = j"
        by simp
      with  `suffix_type T j = L_type` `Suc j < length T` `i' < length SA` `b = k` `k = \<alpha> (T ! j)`
      show ?thesis
        by auto
    qed
  next
    assume "b \<noteq> k"
    hence "B[k := Suc (B ! k)] ! b = B ! b"
      by simp

    from l_bucket_ptr_inv_imp_le_l_bucket_end[OF `l_bucket_ptr_inv \<alpha> T B SA`
                                                 `b \<le> \<alpha> (Max (set T))`]
    have "B ! b \<le> l_bucket_end \<alpha> T b"
      by simp

    from `Suc j < length T`
    have "j < length T"
      by simp

    from l_distinct_pred_inv_helper[OF `i < length SA`
                                       `SA ! i = Suc j`
                                       `Suc j < length T`
                                       `suffix_type T j = L_type`
                                       `l_distinct_inv T SA`
                                       `l_pred_inv T SA i`]
    have "j \<notin> set SA"
      by assumption

    from l_bucket_ptr_inv_imp_less_l_bucket_end[OF `l_bucket_ptr_inv \<alpha> T B SA`
                                                  `j < length T`
                                                  `suffix_type T j = L_type`
                                                  `j \<notin> set SA`
                                                  `strict_mono \<alpha>`]
         `k = \<alpha> (T ! j)`
         `l = B ! k`
    have "l < l_bucket_end \<alpha> T k"
      by simp

    from `k = \<alpha> (T ! j)` `j < length T` `strict_mono \<alpha>`
    have "k \<le> \<alpha> (Max (set T))"
      by (simp add: strict_mono_less_eq)

    from l_bucket_ptr_inv_imp_ge_bucket_start[OF `l_bucket_ptr_inv \<alpha> T B SA`
                                                 `k \<le> \<alpha> (Max (set T))`]
         `l = B ! k`
    have "bucket_start \<alpha> T k \<le> l"
      by simp

    from `B[k := Suc (B ! k)] ! b = B ! b`
         `i' < B[k := Suc (B ! k)] ! b`
         l_bucket_ptr_inv_imp_le_l_bucket_end[OF `l_bucket_ptr_inv \<alpha> T B SA`
                                                 `b \<le> \<alpha> (Max (set T))`]
         l_bucket_end_le_bucket_end
    have "i' < bucket_end \<alpha> T b"
      by (metis less_le_trans)

    from `b \<noteq> k`
    have "b < k \<or> k < b"
      by linarith
    hence "i' \<noteq> l"
    proof
      assume "b < k"
      hence "bucket_end \<alpha> T b \<le> bucket_start \<alpha> T k"
        by (simp add: less_bucket_end_le_start)
        with `i' < bucket_end \<alpha> T b` `bucket_start \<alpha> T k \<le> l`
        have "i' < l"
          by linarith
        then show ?thesis
          by simp
      next
        assume "k < b"
        hence "bucket_end \<alpha> T k \<le> bucket_start \<alpha> T b"
          by (simp add: less_bucket_end_le_start)
        hence "l_bucket_end \<alpha> T k \<le> bucket_start \<alpha> T b"
          using l_bucket_end_le_bucket_end le_trans by blast
        with `bucket_start \<alpha> T b \<le> i'` `l < l_bucket_end \<alpha> T k`
        have "l < i'"
          by simp
        then show ?thesis
          by simp
      qed
      with `B[k := Suc (B ! k)] ! b = B ! b`
           `b \<le> \<alpha> (Max (set T))`
           `bucket_start \<alpha> T b \<le> i'`
           `i' < B[k := Suc (B ! k)] ! b`
           `i' < length SA`
           `l_locations_inv \<alpha> T B SA`
      show ?thesis
      using  l_locations_inv_D by fastforce
  qed
qed

corollary l_locations_inv_perm_maintained:
  assumes "l_perm_inv \<alpha> T B SA0 SA i"
  and     "i < length SA"
  and     "SA ! i = Suc j"
  and     "Suc j < length T"
  and     "suffix_type T j = L_type"
  and     "k = \<alpha> (T ! j)"
  and     "l = B ! k"
shows "l_locations_inv \<alpha> T (B[k := Suc (B ! k)]) (SA[l := j])"
  by (metis assms l_locations_inv_maintained l_perm_inv_elims(1,4,6,9,10,12))

section "Unchanged"

subsection "Establishment"

lemma l_unchanged_inv_established:
  "l_unchanged_inv \<alpha> T SA SA"
  using l_unchanged_inv_def by blast

subsection "Maintenance"

lemma l_unchanged_inv_maintained:
  assumes "l_unchanged_inv \<alpha> T SA0 SA"
  and     "length B > \<alpha> (Max (set T))"
  and     "i < length SA"
  and     "SA ! i = Suc j"
  and     "Suc j < length T"
  and     "suffix_type T j = L_type"
  and     "k = \<alpha> (T ! j)"
  and     "l = B ! k"
  and     "strict_mono \<alpha>"
  and     "l_distinct_inv T SA"
  and     "l_pred_inv T SA i"
  and     "l_bucket_ptr_inv \<alpha> T B SA"
  shows "l_unchanged_inv \<alpha> T SA0 (SA[l := j])"
proof -
  have "l_unchanged_inv \<alpha> T SA (SA[l := j])"
    unfolding l_unchanged_inv_def
  proof safe
    show "length (SA[l := j]) = length SA"
      by simp
  next
    fix b i'
    assume "b \<le> \<alpha> (Max (set T))"
           "i' < length SA"
           "l_bucket_end \<alpha> T b \<le> i'"
           "i' < bucket_end \<alpha> T b"

    from `strict_mono \<alpha>`
         `l_bucket_ptr_inv \<alpha> T B SA`
         `Suc j < length T`
         `k = \<alpha> (T ! j)`
         `l = B ! k`
    have "bucket_start \<alpha> T k \<le> l"
      by (metis Max_greD Suc_lessD l_bucket_ptr_inv_imp_ge_bucket_start strict_mono_leD)

    from `l_distinct_inv T SA`
         `l_pred_inv T SA i`
         `i < length SA`
         `SA ! i = Suc j`
         `Suc j < length T`
         `suffix_type T j = L_type`
    have "j \<notin> set SA"
      using l_distinct_pred_inv_helper by blast

    from `j \<notin> set SA`
         `strict_mono \<alpha>`
         `l_bucket_ptr_inv \<alpha> T B SA`
         `Suc j < length T`
         `suffix_type T j = L_type`
         `k = \<alpha> (T ! j)`
         `l = B ! k`
    have "l < l_bucket_end \<alpha> T k"
      using Suc_lessD l_bucket_ptr_inv_imp_less_l_bucket_end by blast

    have "b = k \<or> b \<noteq> k"
      by blast
    then show "SA ! i' = SA[l := j] ! i'"
    proof
      assume "b = k"
      then show ?thesis
        using \<open>l < l_bucket_end \<alpha> T k\<close> \<open>l_bucket_end \<alpha> T b \<le> i'\<close> by auto
    next
      assume "b \<noteq> k"
      hence "b < k \<or> k < b"
        using less_linear by blast
      then show ?thesis
      proof
        assume "b < k"
        hence "bucket_end \<alpha> T b \<le> bucket_start \<alpha> T k"
          by (simp add: less_bucket_end_le_start)
        with `i' < bucket_end \<alpha> T b` `bucket_start \<alpha> T k \<le> l`
        have "i' < l"
          by linarith
        then show ?thesis
          by simp
      next
        assume "k < b"
        hence "bucket_end \<alpha> T k \<le> bucket_start \<alpha> T b"
          by (simp add: less_bucket_end_le_start)
        hence "l_bucket_end \<alpha> T k \<le> bucket_start \<alpha> T b"
          using l_bucket_end_le_bucket_end le_trans by blast
        hence "l_bucket_end \<alpha> T k \<le> l_bucket_end \<alpha> T b"
          by (simp add: l_bucket_end_def)
        with `l < l_bucket_end \<alpha> T k` `l_bucket_end \<alpha> T b \<le> i'`
        have "l < i'"
          by linarith
        then show ?thesis
          by simp
      qed
    qed
  qed
  with `l_unchanged_inv \<alpha> T SA0 SA`
  show ?thesis
    using l_unchanged_inv_trans by blast
qed

corollary l_unchanged_inv_perm_maintained:
  assumes "l_perm_inv \<alpha> T B SA0 SA i"
  and     "i < length SA"
  and     "SA ! i = Suc j"
  and     "Suc j < length T"
  and     "suffix_type T j = L_type"
  and     "k = \<alpha> (T ! j)"
  and     "l = B ! k"
shows "l_unchanged_inv \<alpha> T SA0 (SA[l := j])"
  by (metis assms l_perm_inv_elims(1,4,6,8,10,12) l_unchanged_inv_maintained)

section "Invariant about the Current Index"

subsection "Establishment"

text "The first invariant is that current index is always less than the index
      where the update will occur."
lemma l_index_inv_established:
  assumes "lms_init \<alpha> T SA"
  and     "l_init \<alpha> T SA"
  and     "s_init \<alpha> T SA"
  and     "length SA = length T"
  and     "strict_mono \<alpha>"
  and     "l_bucket_init \<alpha> T B"
  shows "l_index_inv \<alpha> T B SA"
  unfolding l_index_inv_def
proof (intro allI impI; elim conjE)
  fix i j
  assume "i < length SA" "SA ! i = Suc j" "Suc j < length T" "suffix_type T j = L_type"
  with init_imp_only_s_types[OF `lms_init \<alpha> T SA`
                                `l_init \<alpha> T SA`
                                `s_init \<alpha> T SA`
                                `length SA = length T`
                                `strict_mono \<alpha>`,
                             THEN spec, of i]
  have "suffix_type T (Suc j) = S_type"
    by simp
  with `suffix_type T j = L_type` `Suc j < length T`
  have "T ! j \<noteq> T ! Suc j"
    by (simp add: suffix_type_neq)
  with `suffix_type T j = L_type` `Suc j < length T`
  have "T ! Suc j < T ! j"
    using nth_less_imp_s_type by fastforce
  from same_hd_same_bucket[OF l_unchanged_inv_established
                              l_locations_inv_established[OF `l_bucket_init \<alpha> T B`]
                              l_bucket_ptr_inv_established[OF `lms_init \<alpha> T SA`
                                                             `l_init \<alpha> T SA`
                                                             `s_init \<alpha> T SA`
                                                             `length SA = length T`
                                                             `strict_mono \<alpha>`]
                              l_unknowns_inv_established
                              _ _  _ _ _
                              `i < length SA`]
        assms
        `SA ! i = Suc j`
        `Suc j < length T`
  have "bucket_start \<alpha> T (\<alpha> (T ! Suc j)) \<le> i"  "i < bucket_end \<alpha> T (\<alpha> (T ! Suc j))"
    by simp+
  with `T ! Suc j < T ! j` `strict_mono \<alpha>`
  have "i < bucket_start \<alpha> T (\<alpha> (T ! j))"
    by (meson less_bucket_end_le_start less_le_trans strict_mono_less)

  from `l_bucket_init \<alpha> T B` \<open>Suc j < length T\<close> `strict_mono \<alpha>`
  have "B ! \<alpha> (T ! j) = bucket_start \<alpha> T (\<alpha> (T ! j))"
    by (simp add: Suc_lessD l_bucket_initD strict_mono_leD)
  with `i < bucket_start \<alpha> T (\<alpha> (T ! j))`
  show "i < B ! \<alpha> (T ! j)"
    by simp
qed

corollary l_index_inv_perm_established:
  assumes "l_perm_pre \<alpha> T B SA"
  shows "l_index_inv \<alpha> T B SA"
  using assms l_index_inv_established l_perm_pre_def by blast

subsection "Maintenance"

lemma l_index_inv_maintained:
  assumes "l_index_inv \<alpha> T B SA"
  and     "length B > \<alpha> (Max (set T))"
  and     "i < length SA"
  and     "SA ! i = Suc j"
  and     "Suc j < length T"
  and     "suffix_type T j = L_type"
  and     "k = \<alpha> (T ! j)"
  and     "l = B ! k"
  and     "strict_mono \<alpha>"
  and     "l_distinct_inv T SA"
  and     "l_pred_inv T SA i"
  and     "l_bucket_ptr_inv \<alpha> T B SA"
  and     "l_unknowns_inv \<alpha> T B SA"
  shows "l_index_inv \<alpha> T (B[k := Suc (B ! k)]) (SA[l := j])"
  unfolding l_index_inv_def
proof(intro impI allI; elim conjE)
  fix l' j'
  assume "l' < length (SA[l := j])"
         "SA[l := j] ! l' = Suc j'"
         "Suc j' < length T"
         "suffix_type T j' = L_type"

  from `l' < length (SA[l := j])`
  have "l' < length SA"
    by simp

  have "l' = l \<or> l' \<noteq> l"
    by simp
  then show "l' < B[k := Suc (B ! k)] ! \<alpha> (T ! j')"
  proof
    assume "l' = l"
    with `SA[l := j] ! l' = Suc j'` `l' < length SA`
    have "j = Suc j'"
      by simp
    with `suffix_type T j' = L_type` `Suc j' < length T`
    have "T ! j \<le> T ! j'"
      by (simp add: Suc_lessD l_type_letter_gre_Suc)
    with `strict_mono \<alpha>`
    have "\<alpha> (T ! j) \<le> \<alpha> (T ! j')"
      using strict_mono_less_eq by blast
    hence "\<alpha> (T ! j) = \<alpha> (T ! j') \<or> \<alpha> (T ! j) < \<alpha> (T ! j')"
      using le_imp_less_or_eq by blast
    then show ?thesis
    proof
      assume "\<alpha> (T ! j) = \<alpha> (T ! j')"
      with `k = \<alpha> (T ! j)`
           `Suc j' < length T`
           `j = Suc j'`
           `strict_mono \<alpha>`
           `length B > \<alpha> (Max (set T))`
      have "B[k := Suc (B ! k)] ! \<alpha> (T ! j') = Suc (B ! k)"
        by (metis Max_greD less_le_trans not_less nth_list_update_eq strict_mono_less)
      with `l = B ! k` `l' = l`
      show ?thesis
        by simp
    next
      assume "\<alpha> (T ! j) < \<alpha> (T ! j')"

      from `\<alpha> (T ! j) < \<alpha> (T ! j')` `k = \<alpha> (T ! j)`
      have "B[k := Suc (B ! k)] ! \<alpha> (T ! j') = B ! \<alpha> (T ! j')"
        by simp

      from l_distinct_pred_inv_helper[OF `i < length SA`
                                         `SA ! i = Suc j`
                                         `Suc j < length T`
                                         `suffix_type T j = L_type`
                                         `l_distinct_inv T SA`
                                         `l_pred_inv T SA i`]
      have "j \<notin> set SA"
        by assumption

      from Suc_lessD[OF `Suc j < length T`]
      have "j < length T"
        by assumption

      from l_bucket_ptr_inv_imp_less_l_bucket_end[OF `l_bucket_ptr_inv \<alpha> T B SA`
                                                    `j < length T`
                                                    `suffix_type T j = L_type`
                                                    `j \<notin> set SA`
                                                    `strict_mono \<alpha>`]
      have "B ! \<alpha> (T ! j) < l_bucket_end \<alpha> T (\<alpha> (T ! j))"
        by assumption
      with `l' = l` `k = \<alpha> (T ! j)` `l = B ! k`
      have "l' < l_bucket_end \<alpha> T (\<alpha> (T ! j))"
        by simp
      hence "l' < bucket_end \<alpha> T (\<alpha> (T ! j))"
        using l_bucket_end_le_bucket_end less_le_trans by blast
      with less_bucket_end_le_start[OF `\<alpha> (T ! j) < \<alpha> (T ! j')`]
      have "l' < bucket_start \<alpha> T (\<alpha> (T ! j'))"
        using less_le_trans by blast
      with l_bucket_ptr_inv_imp_ge_bucket_start[OF `l_bucket_ptr_inv \<alpha> T B SA`]
           \<open>Suc j' < length T\<close>
           `strict_mono \<alpha>`
      have "l' < B ! \<alpha> (T ! j')"
        by (meson Max_greD Suc_lessD less_le_trans strict_mono_less_eq)
      with `B[k := Suc (B ! k)] ! \<alpha> (T ! j') = B ! \<alpha> (T ! j')`
      show ?thesis
        by simp
    qed
  next
    assume "l' \<noteq> l"
    with `SA[l := j] ! l' = Suc j'`
    have "SA ! l' = Suc j'"
      by auto

    from l_index_inv_D[OF `l_index_inv \<alpha> T B SA`
                        `l' < length SA`
                        `SA ! l' = Suc j'`
                        `Suc j' < length T`
                        `suffix_type T j' = L_type`]

    show ?thesis
      by (metis Suc_leI Suc_le_lessD Suc_lessD list_update_beyond not_less nth_list_update_eq
                nth_list_update_neq)
  qed
qed

corollary l_index_inv_perm_maintained:
  assumes "l_perm_inv \<alpha> T B SA0 SA i"
  and     "i < length SA"
  and     "SA ! i = Suc j"
  and     "Suc j < length T"
  and     "suffix_type T j = L_type"
  and     "k = \<alpha> (T ! j)"
  and     "l = B ! k"
shows "l_index_inv \<alpha> T (B[k := Suc (B ! k)]) (SA[l := j])"
  using assms l_index_inv_maintained l_perm_inv_def by blast

section "Predecessor Invariant"

subsection "Establishment"

text "The proof for the establishment is simple because initially, SA contains no L-types."

lemma l_pred_inv_established:
  assumes "lms_init \<alpha> T SA"
  and     "l_init \<alpha> T SA"
  and     "s_init \<alpha> T SA"
  and     "length SA = length T"
  and     "strict_mono \<alpha>"
  shows "l_pred_inv T SA 0"
  using assms init_imp_only_s_types l_pred_inv_def by fastforce

corollary l_pred_inv_perm_established:
  assumes "l_perm_pre \<alpha> T B SA"
  shows "l_pred_inv T SA 0"
  using assms l_perm_pre_def l_pred_inv_established by blast

subsection "Maintenance"

text "In this section, we prove that the predecessor invariant @{thm l_pred_inv_def}is maintained.
      In English, this invariant states that for all L-type suffixes in the suffix array (SA),
      their right neighbour is in SA and occurs before them."

text "We now prove that the invariant is maintained for each branch of the @{const abs_induce_l_step}"

lemma l_pred_inv_maintained_no_update:
  assumes "l_pred_inv T SA i"
  shows "l_pred_inv T SA (Suc i)"
  using assms
  unfolding l_pred_inv_def
  using less_Suc_eq by auto

lemma l_pred_inv_maintained:
  assumes "l_pred_inv T SA i"
  and     "i < length SA"
  and     "SA ! i = Suc j"
  and     "Suc j < length T"
  and     "suffix_type T j = L_type"
  and     "k = \<alpha> (T ! j)"
  and     "l = B ! k"
  and     "strict_mono \<alpha>"
  and     "l_distinct_inv T SA"
  and     "l_bucket_ptr_inv \<alpha> T B SA"
  and     "l_unknowns_inv \<alpha> T B SA"
  and     "l_index_inv \<alpha> T B SA"
  shows "l_pred_inv T (SA[l := j]) (Suc i)"
proof -

  from l_distinct_pred_inv_helper[OF `i < length SA`
                                     `SA ! i = Suc j`
                                     `Suc j < length T`
                                     `suffix_type T j = L_type`
                                     `l_distinct_inv T SA`
                                     `l_pred_inv T SA i`]
  have "j \<notin> set SA"
    by assumption

  from `Suc j < length T`
  have "j < length T"
    by simp

  from l_unknowns_l_bucket_ptr_inv_helper[OF `l_unknowns_inv \<alpha> T B SA`
                                            `l_bucket_ptr_inv \<alpha> T B SA`
                                            `j < length T`
                                            `suffix_type T j = L_type`
                                            `j \<notin> set SA`
                                            `strict_mono \<alpha>`
                                            `k = \<alpha> (T ! j)`
                                            `l = B !  k`]
  have "SA ! l = length T"
    by assumption

  from l_index_inv_D[OF `l_index_inv \<alpha> T B SA`
                      `i < length SA`
                      `SA ! i = Suc j`
                      `Suc j < length T`
                      `suffix_type T j = L_type`]
       `k = \<alpha> (T ! j)`
       `l = B ! k`
  have "l > i"
    by simp

  show ?thesis
    unfolding l_pred_inv_def
  proof (intro impI allI; elim conjE)
    fix i'
    assume "i' < length (SA[l := j])"
           "SA[l := j] ! i' < length T"
           "suffix_type T (SA[l := j] ! i') = L_type"
    have "i' = l \<or> i' \<noteq> l"
      by blast
    then show
      "\<exists>ja<length (SA[l := j]). SA[l := j] ! ja = Suc (SA[l := j] ! i') \<and> ja < i' \<and> ja < Suc i"
    proof
      assume "i' = l"
      with `i' < length (SA[l := j])`
      have "SA[l := j] ! i' = j"
        by simp

      from `l > i` `SA ! i = Suc j`
      have "SA[l := j] ! i = Suc j"
        by simp
      with `l > i` `i' = l` `SA[l := j] ! i' = j` `i < length SA`
      show ?thesis
        by auto
    next
      assume "i' \<noteq> l"
      with `i' < length (SA[l := j])`
      have  "i' < length SA"
        by simp

      from `i' \<noteq> l` `SA[l := j] ! i' < length T`
      have "SA ! i' < length T"
        by simp

      from `i' \<noteq> l` `suffix_type T (SA[l := j] ! i') = L_type`
      have "suffix_type T (SA ! i') = L_type"
        by simp

      from `i' < length SA` `SA ! i' < length T` `suffix_type T (SA ! i') = L_type`
           `l_pred_inv T SA i`[simplified l_pred_inv_def, THEN spec, of i']
      obtain j' where
        "j' < length SA"
        "SA ! j' = Suc (SA ! i')"
        "j' < i'"
        "j' < i"
        by blast

      with `SA ! l = length T` `i' \<noteq> l` `suffix_type T (SA ! i') = L_type` `i < l`
      show ?thesis
        by auto
    qed
  qed
qed

corollary l_pred_inv_perm_maintained:
  assumes "l_perm_inv \<alpha> T B SA0 SA i"
  and     "i < length SA"
  and     "SA ! i = Suc j"
  and     "Suc j < length T"
  and     "suffix_type T j = L_type"
  and     "k = \<alpha> (T ! j)"
  and     "l = B ! k"
shows "l_pred_inv T (SA[l := j]) (Suc i)"
  by (metis assms l_perm_inv_elims(4-7,10,12) l_pred_inv_maintained)

section "Seen Invariant"

subsection "Establishment"

text "We first show that the invariant is initially true, i.e. @{term \<open>l_seen_inv T SA 0\<close>}."

lemma l_seen_inv_established:
  "l_seen_inv T SA 0"
  by (simp add: l_seen_inv_def)

subsection "Maintenance"

text "We now show that the invariant is maintained after each call of @{term abs_induce_l_step}."

lemma l_seen_inv_maintained_no_update:
  "\<lbrakk>l_seen_inv T SA i; length T \<le> SA ! i\<rbrakk> \<Longrightarrow> l_seen_inv T SA (Suc i)"
  "\<lbrakk>l_seen_inv T SA i; length SA \<le> i\<rbrakk> \<Longrightarrow> l_seen_inv T SA (Suc i)"
  "\<lbrakk>l_seen_inv T SA i; SA ! i < length T; SA ! i = 0\<rbrakk> \<Longrightarrow> l_seen_inv T SA (Suc i)"
  "\<lbrakk>l_seen_inv T SA i; SA ! i < length T; SA ! i = Suc j; suffix_type T j = S_type\<rbrakk> \<Longrightarrow>
   l_seen_inv T SA (Suc i)"
  unfolding l_seen_inv_def
  using less_Suc_eq by auto

lemma l_seen_inv_maintained:
  assumes "l_seen_inv T SA i"
  and     "i < length SA"
  and     "SA ! i = Suc j"
  and     "Suc j < length T"
  and     "suffix_type T j = L_type"
  and     "k = \<alpha> (T ! j)"
  and     "l = B ! k"
  and     "length SA = length T"
  and     "strict_mono \<alpha>"
  and     "l_distinct_inv T SA"
  and     "l_pred_inv T SA i"
  and     "l_unknowns_inv \<alpha> T B SA"
  and     "l_bucket_ptr_inv \<alpha> T B SA"
  and     "l_index_inv \<alpha> T B SA"
  shows "l_seen_inv T (SA[l := j]) (Suc i)"
proof -
  from l_distinct_pred_inv_helper[OF `i < length SA`
                                     `SA ! i = Suc j`
                                     `Suc j < length T`
                                     `suffix_type T j = L_type`
                                     `l_distinct_inv T SA`
                                     `l_pred_inv T SA i`]
  have "j \<notin> set SA"
    by assumption

  from `Suc j < length T`
  have "j < length T"
    by simp

  from bucket_size_imp_less_length[OF `l_bucket_ptr_inv \<alpha> T B SA`
                                      `j < length T`
                                      `suffix_type T j = L_type`
                                      `j \<notin> set SA`
                                      `strict_mono \<alpha>`]
       `k = \<alpha> (T ! j)`
       `l = B ! k`
  have "l < length T"
    by simp

  from l_index_inv_D[OF `l_index_inv \<alpha> T B SA`
                      `i < length SA`
                      `SA ! i = Suc j`
                      `Suc j < length T`
                      `suffix_type T j = L_type`]
       `k = \<alpha> (T ! j)`
       `l = B ! k`
  have "l > i"
    by simp

  from l_unknowns_l_bucket_ptr_inv_helper[OF `l_unknowns_inv \<alpha> T B SA`
                                            `l_bucket_ptr_inv \<alpha> T B SA`
                                            `j < length T`
                                            `suffix_type T j = L_type`
                                            `j \<notin> set SA`
                                            `strict_mono \<alpha>`
                                            `k = \<alpha> (T ! j)`
                                            `l = B !  k`]
  have "SA ! l = length T"
    by assumption

  with `SA ! i = Suc j` `Suc j < length T` `i < l`
  have "(SA[l := j]) ! i < length T"
    by auto

  with `SA ! i = Suc j` `i < l`
  have "(SA[l := j]) ! i = Suc j"
    by auto

  from l_seen_inv_upd[OF `l_seen_inv T SA i`]
       `l > i`
       `SA ! l = length T`
       `l < length T`
       `length SA = length T`
  have "l_seen_inv T (SA[l := j]) i"
    by auto
  with l_seen_inv_Suc[OF _ `(SA[l := j]) ! i = Suc j`]
       `l < length T`
       `length SA = length T`
  show ?thesis
    by (metis length_list_update nth_list_update_eq)
qed

corollary l_seen_inv_perm_maintained:
  assumes "l_perm_inv \<alpha> T B SA0 SA i"
  and     "i < length SA"
  and     "SA ! i = Suc j"
  and     "Suc j < length T"
  and     "suffix_type T j = L_type"
  and     "k = \<alpha> (T ! j)"
  and     "l = B ! k"
shows "l_seen_inv T (SA[l := j]) (Suc i)"
  by (metis assms l_perm_inv_elims(2,3-7,10-12) l_seen_inv_maintained)

section "Permutation"

subsection "Establishment"

lemma l_perm_inv_established:
  assumes "l_perm_pre \<alpha> T B SA"
  shows "l_perm_inv \<alpha> T B SA SA 0"
  unfolding l_perm_inv_def
  by (simp add: l_perm_pre_elims[OF assms] l_distinct_inv_perm_established[OF assms]
                l_unknowns_inv_perm_established[OF assms] l_bucket_ptr_inv_perm_established[OF assms]
                l_index_inv_perm_established[OF assms] l_unchanged_inv_established
                l_locations_inv_perm_established[OF assms] l_pred_inv_perm_established[OF assms]
                l_seen_inv_established)

subsection "Maintenance"

lemma l_perm_inv_maintained:
  assumes "l_perm_inv \<alpha> T B SA0 SA i"
  and     "i < length SA"
  and     "SA ! i = Suc j"
  and     "Suc j < length T"
  and     "suffix_type T j = L_type"
  and     "k = \<alpha> (T ! j)"
  and     "l = B ! k"
shows "l_perm_inv \<alpha> T (B[k := Suc (B ! k)]) SA0 (SA[l := j]) (Suc i)"
  unfolding l_perm_inv_def
  by (simp add: l_perm_inv_elims[OF assms(1)] l_distinct_inv_perm_maintained[OF assms(1-5)]
                l_unknowns_inv_perm_maintained[OF assms] l_bucket_ptr_inv_perm_maintained[OF assms]
                l_index_inv_perm_maintained[OF assms] l_unchanged_inv_perm_maintained[OF assms]
                l_locations_inv_perm_maintained[OF assms] l_pred_inv_perm_maintained[OF assms]
                l_seen_inv_perm_maintained[OF assms])

lemma l_perm_inv_maintained_no_upd_1:
  assumes "l_perm_inv \<alpha> T B SA0 SA i"
  and     "length SA \<le> i"
shows "l_perm_inv \<alpha> T B SA0 SA (Suc i)"
  unfolding l_perm_inv_def
  by (simp add: l_perm_inv_elims[OF assms(1)] l_pred_inv_maintained_no_update
                l_seen_inv_maintained_no_update(2)[OF l_perm_inv_elims(11)[OF assms(1)] assms(2)])

lemma l_perm_inv_maintained_no_upd_2:
  assumes "l_perm_inv \<alpha> T B SA0 SA i"
  and     "length T \<le> SA ! i "
shows "l_perm_inv \<alpha> T B SA0 SA (Suc i)"
  unfolding l_perm_inv_def
  by (simp add: l_perm_inv_elims[OF assms(1)] l_pred_inv_maintained_no_update
                l_seen_inv_maintained_no_update(1)[OF l_perm_inv_elims(11)[OF assms(1)] assms(2)])

lemma l_perm_inv_maintained_no_upd_3:
  assumes "l_perm_inv \<alpha> T B SA0 SA i"
  and     "SA ! i < length T"
  and     "SA ! i = 0"
shows "l_perm_inv \<alpha> T B SA0 SA (Suc i)"
  unfolding l_perm_inv_def
  by (simp add: l_perm_inv_elims[OF assms(1)] l_pred_inv_maintained_no_update
                l_seen_inv_maintained_no_update(3)[OF l_perm_inv_elims(11)[OF assms(1)] assms(2-)])

lemma l_perm_inv_maintained_no_upd_4:
  assumes "l_perm_inv \<alpha> T B SA0 SA i"
  and     "SA ! i < length T"
  and     "SA ! i = Suc j"
  and     "suffix_type T j = S_type"
shows "l_perm_inv \<alpha> T B SA0 SA (Suc i)"
  unfolding l_perm_inv_def
  by (simp add: l_perm_inv_elims[OF assms(1)] l_pred_inv_maintained_no_update
                l_seen_inv_maintained_no_update(4)[OF l_perm_inv_elims(11)[OF assms(1)] assms(2-)])

lemmas l_perm_inv_maintained_no_update =
  l_perm_inv_maintained_no_upd_1 l_perm_inv_maintained_no_upd_2 l_perm_inv_maintained_no_upd_3
  l_perm_inv_maintained_no_upd_4


lemma abs_induce_l_perm_step:
  assumes "l_perm_inv \<alpha> T B SA0 SA i"
  and     "abs_induce_l_step (B, SA, i) (\<alpha>, T) = (B', SA', i')"
shows "l_perm_inv \<alpha> T B' SA0 SA' i'"
proof (cases "i < length SA \<and> SA ! i < length T")
  assume A: "i < length SA \<and> SA ! i < length T"
  show ?thesis
  proof (cases "SA ! i")
    case 0
    then show ?thesis
      using A l_perm_inv_maintained_no_update(3)[OF assms(1)] assms(2)
      by force
  next
    case (Suc j)
    assume B: "SA ! i = Suc j"
    show ?thesis
    proof (cases "suffix_type T j")
      case S_type
      then show ?thesis
        using A B l_perm_inv_maintained_no_update(4)[OF assms(1)] assms(2)
        by force
    next
      case L_type
      then show ?thesis
        using A B l_perm_inv_maintained[OF assms(1)] assms(2)
        by (clarsimp simp: Let_def)
    qed
  qed
next
  assume A: "\<not>(i < length SA \<and> SA ! i < length T)"
  show ?thesis
    using l_perm_inv_maintained_no_update(1,2)[OF assms(1)] A assms(2)
    by force
qed

lemma abs_induce_l_base_perm_inv_maintained:
  assumes "l_perm_inv \<alpha> T B SA0 SA 0"
  and     "abs_induce_l_base \<alpha> T B SA = (B', SA', i)"
shows "l_perm_inv \<alpha> T B' SA0 SA' i"
proof -
  let ?P = "\<lambda>(B, SA, i). l_perm_inv \<alpha> T B SA0 SA i"

  from assms(2)
  have "repeat (length T) abs_induce_l_step (B, SA, 0) (\<alpha>, T) = (B', SA', i)"
    by (simp add: abs_induce_l_base_def)
  moreover
  have "\<And>a. ?P a \<Longrightarrow> ?P (abs_induce_l_step a (\<alpha>, T))"
    using abs_induce_l_perm_step by blast
  ultimately show ?thesis
    using repeat_maintain_inv[of ?P abs_induce_l_step "(\<alpha>, T)" "(B, SA, 0)" "length T"]
    using assms(1) by auto
qed

section "Sorted"

lemma l_suffix_sorted_inv_established:
  assumes "l_bucket_init \<alpha> T B"
  shows "l_suffix_sorted_inv \<alpha> T B SA"
  unfolding l_suffix_sorted_inv_def
proof(intro allI impI)
  fix b
  assume "b \<le> \<alpha> (Max (set T))"
  with l_bucket_initD[OF assms, of b]
  have "B ! b = bucket_start \<alpha> T b" .
  then 
  show "ordlistns.sorted 
          (map (suffix T) 
          (list_slice SA (bucket_start \<alpha> T b) (B ! b)))"
    by simp
qed

lemma l_prefix_sorted_inv_established:
  assumes "l_bucket_init \<alpha> T B"
  shows "l_prefix_sorted_inv \<alpha> T B SA"
  unfolding l_prefix_sorted_inv_def
proof(intro allI impI)
  fix b
  assume "b \<le> \<alpha> (Max (set T))"
  with l_bucket_initD[OF assms, of b]
  have "B ! b = bucket_start \<alpha> T b" .
  then show "ordlistns.sorted (map (lms_prefix T) (list_slice SA (bucket_start \<alpha> T b) (B ! b)))"
    by simp
qed

lemma l_sorted_inv_maintained_step:
  assumes "l_perm_inv \<alpha> T B SA0 SA i"
  and     "i < length SA"
  and     "SA ! i = Suc j"
  and     "Suc j < length T"
  and     "suffix_type T j = L_type"
  and     "k = \<alpha> (T ! j)"
  and     "l = B ! k"
  and     "b \<le> \<alpha> (Max (set T))"
  and     "b \<noteq> k"
  and     "ordlistns.sorted (map f (list_slice SA (bucket_start \<alpha> T b) (B ! b)))"
shows "ordlistns.sorted (map f (list_slice (SA[l := j]) (bucket_start \<alpha> T b) (B[k := Suc l] ! b)))"
proof -
  let ?xs = "list_slice (SA[l := j]) (bucket_start \<alpha> T b) (B[k := Suc l] ! b)" and
      ?ys = "list_slice SA (bucket_start \<alpha> T b) (B ! b)"

  have "i < length T"
    by (metis assms(1,2) l_perm_inv_def)
  hence "k \<le> \<alpha> (Max (set T))"
    using assms(1,4,6) l_perm_inv_def strict_mono_less_eq by fastforce

  from `Suc j < length T`
  have "j < length T"
    by simp

  from l_distinct_pred_inv_helper[OF `i < length SA`
                                     `SA ! i = Suc j`
                                     `Suc j < length T`
                                     `suffix_type T j = L_type`
                                     l_perm_inv_elims(4,10)[OF assms(1)]]
  have "j \<notin> set SA"
    by assumption

  from l_bucket_ptr_inv_imp_less_l_bucket_end[OF l_perm_inv_elims(6)[OF assms(1)]
                                                 `j < length T`
                                                 `suffix_type T j = L_type`
                                                 `j \<notin> set SA`
                                                 l_perm_inv_elims(12)[OF assms(1)]]
       `k = \<alpha> (T ! j)`
       `l = B ! k`
  have "l < l_bucket_end \<alpha> T k"
    by simp
  hence "l < length SA"
    by (metis assms(1) bucket_end_le_length dual_order.strict_trans1 l_bucket_end_le_bucket_end l_perm_inv_def)

  have "B[k := Suc l] ! b = B ! b"
    using assms(9) by auto

  have "l < bucket_start \<alpha> T b \<or> B ! b \<le> l"
  proof -
    have "b < k \<or> k < b"
      using \<open>b \<noteq> k\<close> less_linear by blast
    moreover
    have "b < k \<Longrightarrow> ?thesis"
    proof -
      assume "b < k"
      hence "bucket_end \<alpha> T b \<le> bucket_start \<alpha> T k"
        by (simp add: less_bucket_end_le_start)
      hence "l_bucket_end \<alpha> T b \<le> bucket_start \<alpha> T k"
        using l_bucket_end_le_bucket_end le_trans by blast
      with l_bucket_ptr_inv_imp_le_l_bucket_end[OF l_perm_inv_elims(6)[OF assms(1)] `b \<le> _`]
      have "B ! b \<le> bucket_start \<alpha> T k"
        by linarith
      with l_bucket_ptr_inv_imp_ge_bucket_start[OF l_perm_inv_elims(6)[OF assms(1)] `k \<le> _`]
      show ?thesis
        using assms(7) le_trans by blast
    qed
    moreover
    have "k < b \<Longrightarrow> ?thesis"
    proof -
      assume "k < b"
      hence "bucket_end \<alpha> T k \<le> bucket_start \<alpha> T b"
        by (simp add: less_bucket_end_le_start)
      hence "l_bucket_end \<alpha> T k \<le> bucket_start \<alpha> T b"
        using l_bucket_end_le_bucket_end le_trans by blast
      with `l < l_bucket_end \<alpha> T k`
      show ?thesis
        using less_le_trans by blast
    qed
    ultimately show ?thesis
      by blast
  qed
  with `B[k := Suc l] ! b = B ! b`
       list_slice_update_unchanged_1
       list_slice_update_unchanged_2
  have "?xs = ?ys"
    by auto
  then show ?thesis
    using assms(10) by auto
qed

lemma l_suffix_sorted_inv_maintained_step:
  assumes "l_perm_inv \<alpha> T B SA0 SA i"
  and     "l_suffix_sorted_pre \<alpha> T SA0"
  and     "l_suffix_sorted_inv \<alpha> T B SA"
  and     "i < length SA"
  and     "SA ! i = Suc j"
  and     "Suc j < length T"
  and     "suffix_type T j = L_type"
  and     "k = \<alpha> (T ! j)"
  and     "l = B ! k"
shows "l_suffix_sorted_inv \<alpha> T (B[k := Suc l]) (SA[l := j])"
  unfolding l_suffix_sorted_inv_def
proof (safe)
  fix b
  assume "b \<le> \<alpha> (Max (set T))"
  let ?xs = "list_slice (SA[l := j]) (bucket_start \<alpha> T b) (B[k := Suc l] ! b)" and
      ?ys = "list_slice SA (bucket_start \<alpha> T b) (B ! b)"

  have "i < length T"
    by (metis assms(1,4) l_perm_inv_def)
  hence "k \<le> \<alpha> (Max (set T))"
    using assms(1,6,8) l_perm_inv_def strict_mono_less_eq by fastforce

   from `Suc j < length T`
    have "j < length T"
      by simp

    from l_distinct_pred_inv_helper[OF `i < length SA`
                                       `SA ! i = Suc j`
                                       `Suc j < length T`
                                       `suffix_type T j = L_type`
                                       l_perm_inv_elims(4,10)[OF assms(1)]]
    have "j \<notin> set SA"
      by assumption

    from l_bucket_ptr_inv_imp_less_l_bucket_end[OF l_perm_inv_elims(6)[OF assms(1)]
                                                  `j < length T`
                                                  `suffix_type T j = L_type`
                                                  `j \<notin> set SA`
                                                  l_perm_inv_elims(12)[OF assms(1)]]
         `k = \<alpha> (T ! j)`
         `l = B ! k`
    have "l < l_bucket_end \<alpha> T k"
      by simp
    hence "l < length SA"
      by (metis assms(1) bucket_end_le_length dual_order.strict_trans1 l_bucket_end_le_bucket_end l_perm_inv_def)

  have "b = k \<or> b \<noteq> k"
    by simp
  moreover
  have "b \<noteq> k \<Longrightarrow> ordlistns.sorted (map (suffix T) ?xs)"
    using \<open>b \<le> \<alpha> (Max (set T))\<close> assms l_sorted_inv_maintained_step l_suffix_sorted_inv_def by blast
  moreover
  have "b = k \<Longrightarrow> ordlistns.sorted (map (suffix T) ?xs)"
  proof -
    assume "b = k"
    hence "B[k := Suc l] ! b = Suc l"
      using \<open>b \<le> \<alpha> (Max (set T))\<close> assms(1) l_perm_inv_elims(1) by fastforce

    have "SA[l := j] ! l = j"
      by (simp add: \<open>l < length SA\<close>)

    from list_slice_update_unchanged_2[of "B ! b" j _ "bucket_start \<alpha> T b"]
    have "list_slice (SA[l := j]) (bucket_start \<alpha> T b) (B ! b) = ?ys"
      using \<open>b = k\<close> assms(9) 
      by (simp add: list_slice_update_unchanged_2)
    hence "?xs = ?ys @ list_slice (SA[l := j]) (B ! b) (B[k := Suc l] ! k)"
      by (metis Suc_n_not_le_n \<open>B[k := Suc l] ! b = Suc l\<close> \<open>b = k\<close> \<open>k \<le> \<alpha> (Max (set T))\<close> assms(1,9)
                l_bucket_ptr_inv_imp_ge_bucket_start l_perm_inv_elims(6) linear list_slice_append)
    moreover
    have "list_slice (SA[l := j]) (B ! b) (B[k := Suc l] ! k) = [j]"
      by (metis \<open>B[k := Suc l] ! b = Suc l\<close> \<open>SA[l := j] ! l = j\<close> 
                \<open>b = k\<close> \<open>l < length SA\<close> assms(9)
                length_list_update lessI list_slice_Suc list_slice_n_n)
    ultimately have "?xs = ?ys @ [j]"
      by simp
    hence "map (suffix T) ?xs = (map (suffix T) ?ys) @ [suffix T j]"
      by simp
    moreover
    have "ordlistns.sorted ((map (suffix T) ?ys) @ [suffix T j])"
    proof -
      from l_suffix_sorted_invD[OF assms(3) `b \<le> _`]
      have "ordlistns.sorted (map (suffix T) ?ys)" .
      moreover
      have "ordlistns.sorted [suffix T j]"
        by simp
      moreover
      have "\<forall>x \<in> set (map (suffix T) ?ys). 
            \<forall>y \<in> set [suffix T j]. 
                  list_less_eq_ns x y"
      proof(safe)
        fix x y
        assume 
          "x \<in> set (map (suffix T) ?ys)" 
          "y \<in> set [suffix T j]"
        hence "y = suffix T j"
          by simp

        have A: "length ?ys = B ! b - bucket_start \<alpha> T b"
          using \<open>b = k\<close> \<open>l < length SA\<close> assms(9) min_def by auto

        from in_set_conv_nth[THEN iffD1, OF `x \<in> set (map (suffix T) ?ys)`]
        have "\<exists>i'. x = suffix T (SA ! i') \<and> 
                   bucket_start \<alpha> T b \<le> i' \<and> i' < B ! b"
          by (metis A add.commute le_add1 length_map 
                    less_diff_conv nth_list_slice nth_map)
        then obtain j' where j'_assms:
          "x = suffix T (SA ! j')"
          "bucket_start \<alpha> T b \<le> j'"
          "j' < B ! b"
          by blast
        hence j'_less: "j' < length SA"
          using \<open>b = k\<close> \<open>l < length SA\<close> assms(9) dual_order.strict_trans 
          by blast
        with l_locations_inv_D
              [OF l_perm_inv_elims(9)[OF assms(1)] `b \<le> _` _ j'_assms(2,3)]
        have "SA ! j' < length T" 
             "suffix_type T (SA ! j') = L_type" 
             "\<alpha> (T ! (SA ! j')) = b"
          by blast+
        with l_pred_inv_D[OF l_perm_inv_elims(10)[OF assms(1)] j'_less]
        have "\<exists>j<length SA. 
                SA ! j = Suc (SA ! j') \<and> 
                SA ! j < length T \<and> 
                j < j' \<and>
                j < i"
          by blast
        then obtain i' where i'_assms:
          "i' < length SA"
          "SA ! i' = Suc (SA ! j')"
          "SA ! i' < length T"
          "i' < j'"
          "i' < i"
          by blast

        have "\<alpha> (T ! j) = b"
          using \<open>b = k\<close> assms(8) by blast
        with `\<alpha> (T ! (SA ! j')) = b`
        have "T ! (SA ! j') = T ! j"
          by (metis (no_types, lifting) assms(1) l_perm_inv_elims(12) 
                    less_le not_le strict_mono_less_eq)
        moreover
        have "x = T ! (SA ! j') # suffix T (SA ! i')"
          using \<open>SA ! i' = Suc (SA ! j')\<close> 
                \<open>SA ! j' < length T\<close> 
                \<open>x = suffix T (SA ! j')\<close>
                suffix_cons_Suc 
          by auto
        moreover
        have "y = T ! j # suffix T (SA ! i)"
          using \<open>j < length T\<close> \<open>y = suffix T j\<close> 
                suffix_cons_Suc 
                `SA ! i = Suc j` 
          by auto
        ultimately 
        have "list_less_eq_ns x y = 
              list_less_eq_ns (suffix T (SA ! i')) (suffix T (SA ! i))"
          using list_less_eq_ns_cons
                  [of "T ! (SA ! j')" 
                      "suffix T (SA ! i')" 
                      "T ! j" 
                      "suffix T (SA ! i)"]
          by simp
        moreover
        have "list_less_eq_ns (suffix T (SA ! i')) (suffix T (SA ! i))"
        proof -
          have "i' < length T"
            using \<open>i < length T\<close> \<open>i' < i\<close> order.strict_trans by blast
          with index_in_bucket_interval_gen
                  [of i' T \<alpha>, 
                   OF _ l_perm_inv_elims(12)[OF assms(1)]]
          obtain b0 where b0_assms:
            "b0 \<le> \<alpha> (Max (set T))"
            "bucket_start \<alpha> T b0 \<le> i'"
            "i' < bucket_end \<alpha> T b0"
            by blast
          with same_bucket_same_hd
                 [OF l_perm_inv_elims(8,9,6,5)[OF assms(1)], 
                  of b0 i']
               l_perm_inv_elims(2,3,14,15)[OF assms(1)]
          have "\<alpha> (T ! (SA ! i')) = b0"
            using \<open>SA ! i' < length T\<close> \<open>i' < length SA\<close> by auto

          from index_in_bucket_interval_gen[OF `i < length T` l_perm_inv_elims(12)[OF assms(1)]]
          obtain b1 where b1_assms:
            "b1 \<le> \<alpha> (Max (set T))"
            "bucket_start \<alpha> T b1 \<le> i"
            "i < bucket_end \<alpha> T b1"
            by blast
          with same_bucket_same_hd
                [OF l_perm_inv_elims(8,9,6,5)[OF assms(1)], 
                 of b1 i]
               l_perm_inv_elims(2,3,14,15)[OF assms(1)]
          have "\<alpha> (T ! (SA ! i)) = b1"
            using assms(4-6) by auto

          have "b0 \<le> b1"
          proof (rule ccontr)
            assume "\<not> b0 \<le> b1"
            hence "b1 < b0"
              by auto
            hence "bucket_end \<alpha> T b1 \<le> bucket_start \<alpha> T b0"
              by (simp add: less_bucket_end_le_start)
            with `i < bucket_end \<alpha> T b1` `bucket_start \<alpha> T b0 \<le> i'` `i' < i`
            show False
              by linarith
          qed
          hence "b0 < b1 \<or> b0 = b1"
            by linarith
          moreover
          have "b0 < b1 \<Longrightarrow> ?thesis"
          proof -
            assume "b0 < b1"
            with `\<alpha> (T ! (SA ! i')) = b0`
                 `\<alpha> (T ! (SA ! i)) = b1`
            have "T ! (SA ! i') < T ! (SA ! i)"
              using assms(1) l_perm_inv_elims(12) strict_mono_less by blast
            moreover
            have "\<exists>as. suffix T (SA ! i') = T ! (SA ! i') # as"
              using \<open>SA ! i' < length T\<close> suffix_cons_Suc by blast
            then obtain as where as_assm:
              "suffix T (SA ! i') = T ! (SA ! i') # as"
              by blast
            moreover
            have "\<exists>bs. suffix T (SA ! i) = T ! (SA ! i) # bs"
              by (metis Cons_nth_drop_Suc assms(5,6))
            then obtain bs where bs_assm:
              "suffix T (SA ! i) = T ! (SA ! i) # bs"
              by blast
            ultimately show ?thesis
              by (simp add: less_le list_less_eq_ns_cons)
          qed
          moreover
          have "b0 = b1 \<Longrightarrow> ?thesis"
          proof -
            assume "b0 = b1"
            hence "\<alpha> (T ! (SA ! i')) = \<alpha> (T ! (SA ! i))"
              by (simp add: \<open>\<alpha> (T ! (SA ! i')) = b0\<close> \<open>\<alpha> (T ! (SA ! i)) = b1\<close>)
            hence "T ! (SA ! i') = T ! (SA ! i)"
              by (metis (no_types, opaque_lifting) assms(1) strict_mono_less
                        l_perm_inv_elims(12) not_less_iff_gr_or_eq )

            have "i < bucket_end \<alpha> T b0"
              by (simp add: \<open>b0 = b1\<close> \<open>i < bucket_end \<alpha> T b1\<close>)

            from unknown_range_values[OF l_perm_inv_elims(8,5)[OF assms(1)] _ _
                                         l_perm_inv_elims(14,15)[OF assms(1)] 
                                         `b0 \<le> \<alpha> _`]
                 l_perm_inv_elims(2,3)[OF assms(1)]
            have "i < B ! b0 \<or> lms_bucket_start \<alpha> T b0 \<le> i"
              using assms(5) assms(6) not_le by force

            from unknown_range_values[OF l_perm_inv_elims(8,5)[OF assms(1)] _ _
                                         l_perm_inv_elims(14,15)[OF assms(1)] 
                                         `b0 \<le> \<alpha> _`]
                 l_perm_inv_elims(2,3)[OF assms(1)]
                 `SA ! i' < length T`
            have "i' < B ! b0 \<or> 
                  lms_bucket_start \<alpha> T b0 \<le> i'"
              using not_le by force
            moreover
            have "i' < B ! b0 \<Longrightarrow> ?thesis"
            proof -
              assume "i' < B ! b0"
              have "i < B ! b0 \<Longrightarrow> ?thesis"
              proof -
                assume i_b0_assm: "i < B ! b0"
                let ?xs = "list_slice SA (bucket_start \<alpha> T b0) (B ! b0)"

                have "i' \<le> i"
                  by (simp add: \<open>i' < i\<close> less_imp_le_nat)
                from l_suffix_sorted_invD[OF assms(3) `b0 \<le> \<alpha> _`]
                have "ordlistns.sorted (map (suffix T) ?xs)" .
                with ordlistns.list_slice_sorted_nth_mono
                        [OF _ b0_assms(2) `i' \<le> i` i_b0_assm,
                         of "map (suffix T) SA"]
                show ?thesis
                  by (metis i'_assms(1) assms(4) length_map 
                            map_list_slice nth_map)
              qed
              moreover
              have "lms_bucket_start \<alpha> T b0 \<le> i \<Longrightarrow> ?thesis"
              proof -
                assume "lms_bucket_start \<alpha> T b0 \<le> i"
                with lms_init_D
                        [OF lms_init_unchanged
                              [OF l_perm_inv_elims(8)[OF assms(1)]],
                         OF _ _ l_perm_inv_elims(14)[OF assms(1)]
                           `b0 \<le> \<alpha> _`]
                     l_perm_inv_elims(2,3)[OF assms(1)]
                     `i < bucket_end \<alpha> T b0`
                have "SA ! i \<in> lms_bucket \<alpha> T b0"
                  by (metis bucket_end_le_length list_slice_nth_mem)
                hence "suffix_type T (SA ! i) = S_type"
                  by (metis \<open>b0 \<le> \<alpha> (Max (set T))\<close> 
                            \<open>i < bucket_end \<alpha> T b0\<close> 
                            \<open>length SA = length SA0\<close>
                            \<open>length SA0 = length T\<close> 
                            \<open>lms_bucket_start \<alpha> T b0 \<le> i\<close>
                            \<open>lms_init \<alpha> T SA0\<close> 
                            assms(1) abs_is_lms_def l_perm_inv_elims(8) 
                            lms_init_nth lms_init_unchanged)
                moreover
                from l_locations_inv_D
                        [OF l_perm_inv_elims(9)[OF assms(1)] 
                            `b0 \<le> \<alpha> _`
                            i'_assms(1) 
                            b0_assms(2)
                            `i' < B ! b0`]
                have "suffix_type T (SA ! i') = L_type" "SA ! i' < length T"
                  by blast+
                ultimately show ?thesis
                  using l_less_than_s_type_suffix[of "SA ! i" T "SA ! i'"]
                  by (simp add: ordlistns.less_imp_le  `\<alpha> (T ! (SA ! i')) = b0`
                                \<open>T ! (SA ! i') = T ! (SA ! i)\<close> assms(5,6))
              qed
              ultimately 
              show ?thesis
                using \<open>i < B ! b0 \<or> lms_bucket_start \<alpha> T b0 \<le> i\<close> 
                by blast
            qed
            moreover
            have "lms_bucket_start \<alpha> T b0 \<le> i' \<Longrightarrow> ?thesis"
            proof -
              assume "lms_bucket_start \<alpha> T b0 \<le> i'"

              let ?xs = 
                "list_slice SA (lms_bucket_start \<alpha> T b0) (bucket_end \<alpha> T b0)"

              from l_suffix_sorted_pre_maintained
                    [OF l_perm_inv_elims(8)[OF assms(1)]]
                   l_perm_inv_elims(2,3)[OF assms(1)]
                   l_suffix_sorted_preD[of \<alpha> T SA b0, OF _ `b0 \<le> \<alpha> _`]
              have "ordlistns.sorted (map (suffix T) ?xs)"
                by (simp add: assms(2))
              with ordlistns.list_slice_sorted_nth_mono
                      [of "map (suffix T) SA" 
                          "lms_bucket_start \<alpha> T b0"
                          "bucket_end \<alpha> T b0" i' i]
                   \<open>i < bucket_end \<alpha> T b0\<close> 
                   \<open>i' < i\<close> 
                   i'_assms(1) 
                   \<open>lms_bucket_start \<alpha> T b0 \<le> i'\<close>
              show ?thesis
                by (metis assms(4) length_map map_list_slice 
                          not_less not_less_iff_gr_or_eq nth_map)
            qed
            ultimately show ?thesis
              by blast
          qed
          ultimately show ?thesis
            by blast
        qed
        ultimately show "list_less_eq_ns x y"
          by simp
      qed
      ultimately show ?thesis
        using ordlistns.sorted_append[of "map (suffix T) ?ys" "[suffix T j]"]
        by blast
    qed
    ultimately show ?thesis
      by simp
  qed
  ultimately show "ordlistns.sorted (map (suffix T) ?xs)"
    by blast
qed

lemma l_prefix_sorted_inv_maintained_step:
  assumes "l_perm_inv \<alpha> T B SA0 SA i"
  and     "l_prefix_sorted_pre \<alpha> T SA0"
  and     "l_prefix_sorted_inv \<alpha> T B SA"
  and     "i < length SA"
  and     "SA ! i = Suc j"
  and     "Suc j < length T"
  and     "suffix_type T j = L_type"
  and     "k = \<alpha> (T ! j)"
  and     "l = B ! k"
shows "l_prefix_sorted_inv \<alpha> T (B[k := Suc l]) (SA[l := j])"
  unfolding l_prefix_sorted_inv_def
proof (safe)
  fix b
  assume "b \<le> \<alpha> (Max (set T))"
  let ?xs = "list_slice (SA[l := j]) (bucket_start \<alpha> T b) (B[k := Suc l] ! b)" 
  and ?ys = "list_slice SA (bucket_start \<alpha> T b) (B ! b)"

  have "i < length T"
    by (metis assms(1,4) l_perm_inv_def)
  hence "k \<le> \<alpha> (Max (set T))"
    using assms(1,6,8) l_perm_inv_def strict_mono_less_eq by fastforce

   from `Suc j < length T`
    have "j < length T"
      by simp

    from l_distinct_pred_inv_helper
           [OF `i < length SA`
               `SA ! i = Suc j`
               `Suc j < length T`
               `suffix_type T j = L_type`
               l_perm_inv_elims(4,10)[OF assms(1)]]
    have "j \<notin> set SA"
      by assumption

    from l_bucket_ptr_inv_imp_less_l_bucket_end
           [OF l_perm_inv_elims(6)[OF assms(1)]
               `j < length T`
               `suffix_type T j = L_type`
               `j \<notin> set SA`
               l_perm_inv_elims(12)[OF assms(1)]]
         `k = \<alpha> (T ! j)`
         `l = B ! k`
    have "l < l_bucket_end \<alpha> T k"
      by simp
    hence "l < length SA"
      by (metis bucket_end_le_length dual_order.strict_trans1 
                assms(1) l_bucket_end_le_bucket_end l_perm_inv_def)

  have "b = k \<or> b \<noteq> k"
    by simp
  moreover
  have "b \<noteq> k \<Longrightarrow> 
        ordlistns.sorted (map (lms_prefix T) ?xs)"
    using \<open>b \<le> \<alpha> (Max (set T))\<close> 
          assms l_sorted_inv_maintained_step l_prefix_sorted_inv_def 
    by blast
  moreover
  have "b = k \<Longrightarrow> 
        ordlistns.sorted (map (lms_prefix T) ?xs)"
  proof -
    assume "b = k"
    hence "B[k := Suc l] ! b = Suc l"
      using \<open>b \<le> \<alpha> (Max (set T))\<close> assms(1) l_perm_inv_elims(1) 
      by fastforce

    have "SA[l := j] ! l = j"
      by (simp add: \<open>l < length SA\<close>)

    from list_slice_update_unchanged_2
    have "list_slice (SA[l := j]) (bucket_start \<alpha> T b) (B ! b) = ?ys"
      using \<open>b = k\<close> assms(9)
      by fast 
    hence "?xs = ?ys @ list_slice (SA[l := j]) (B ! b) (B[k := Suc l] ! k)"
      by (metis \<open>B[k := Suc l] ! b = Suc l\<close> \<open>b = k\<close> 
                \<open>k \<le> \<alpha> (Max (set T))\<close> 
                assms(1,9) Suc_n_not_le_n list_slice_append linear
                l_bucket_ptr_inv_imp_ge_bucket_start l_perm_inv_elims(6))
    moreover
    have "list_slice (SA[l := j]) (B ! b) (B[k := Suc l] ! k) = [j]"
      by (metis \<open>B[k := Suc l] ! b = Suc l\<close> 
                \<open>SA[l := j] ! l = j\<close> 
                \<open>b = k\<close> 
                \<open>l < length SA\<close> 
                assms(9) length_list_update lessI list_slice_Suc list_slice_n_n)
    ultimately 
    have "?xs = ?ys @ [j]"
      by simp
    hence "map (lms_prefix T) ?xs = (map (lms_prefix T) ?ys) @ [lms_prefix T j]"
      by simp
    moreover
    have "ordlistns.sorted ((map (lms_prefix T) ?ys) @ [lms_prefix T j])"
    proof -
      from l_prefix_sorted_invD[OF assms(3) `b \<le> _`]
      have "ordlistns.sorted (map (lms_prefix T) ?ys)" .
      moreover
      have "ordlistns.sorted [lms_prefix T j]"
        by simp
      moreover
      have "\<forall>x \<in> set (map (lms_prefix T) ?ys). \<forall>y \<in> set [lms_prefix T j].
              list_less_eq_ns x y"
      proof(safe)
        fix x y
        assume "x \<in> set (map (lms_prefix T) ?ys)" "y \<in> set [lms_prefix T j]"
        hence "y = lms_prefix T j"
          by simp

        have A: "length ?ys = B ! b - bucket_start \<alpha> T b"
          using \<open>b = k\<close> \<open>l < length SA\<close> assms(9) min_def by auto

        from in_set_conv_nth[THEN iffD1, OF `x \<in> set (map (lms_prefix T) ?ys)`]
        have "\<exists>i'. x = lms_prefix T (SA ! i') \<and> 
                   bucket_start \<alpha> T b \<le> i' \<and> 
                   i' < B ! b"
          by (metis A add.commute le_add1 length_map less_diff_conv 
                    nth_list_slice nth_map)
        then obtain j' where j'_assms:
          "x = lms_prefix T (SA ! j')"
          "bucket_start \<alpha> T b \<le> j'"
          "j' < B ! b"
          by blast
        hence "j' < length SA"
          using \<open>b = k\<close> \<open>l < length SA\<close> 
                assms(9) dual_order.strict_trans by blast
        with l_locations_inv_D
                [OF l_perm_inv_elims(9)[OF assms(1)] 
                    `b \<le> _` _ 
                    j'_assms(2,3)]
        have "SA ! j' < length T" 
             "suffix_type T (SA ! j') = L_type" 
             "\<alpha> (T ! (SA ! j')) = b"
          by blast+
        with l_pred_inv_D[OF l_perm_inv_elims(10)[OF assms(1)] `j' < length SA`]
        have "\<exists>j<length SA. SA ! j = Suc (SA ! j') \<and> SA ! j < length T \<and> j < j' \<and> j < i"
          by blast
        then obtain i' where
          "i' < length SA"
          "SA ! i' = Suc (SA ! j')"
          "SA ! i' < length T"
          "i' < j'"
          "i' < i"
          by blast

        have "\<alpha> (T ! j) = b"
          using \<open>b = k\<close> assms(8) by blast
        with `\<alpha> (T ! (SA ! j')) = b`
        have "T ! (SA ! j') = T ! j"
          by (metis (no_types, lifting) assms(1) l_perm_inv_elims(12) less_le not_le strict_mono_less_eq)
        moreover
        have "x = T ! (SA ! j') # lms_prefix T (SA ! i')"
          by (simp add: \<open>SA ! i' = Suc (SA ! j')\<close> \<open>SA ! j' < length T\<close>
                        \<open>suffix_type T (SA ! j') = L_type\<close> \<open>x = lms_prefix T (SA ! j')\<close>
                        l_type_lms_prefix_cons)
        moreover
        have "y = T ! j # lms_prefix T (SA ! i)"
          by (simp add: \<open>j < length T\<close> \<open>y = lms_prefix T j\<close> assms(5,7)
                        l_type_lms_prefix_cons)
        ultimately have
          "list_less_eq_ns x y =
            list_less_eq_ns (lms_prefix T (SA ! i')) (lms_prefix T (SA ! i))"
          using list_less_eq_ns_cons[of "T ! (SA ! j')" "lms_prefix T (SA ! i')" "T ! j"
                                        "lms_prefix T (SA ! i)"]
          by simp
        moreover
        have "list_less_eq_ns (lms_prefix T (SA ! i')) (lms_prefix T (SA ! i))"
        proof -
          have "i' < length T"
            using \<open>i < length T\<close> \<open>i' < i\<close> order.strict_trans by blast
          with index_in_bucket_interval_gen[of i' T \<alpha>, OF _ l_perm_inv_elims(12)[OF assms(1)]]
          obtain b0 where
            "b0 \<le> \<alpha> (Max (set T))"
            "bucket_start \<alpha> T b0 \<le> i'"
            "i' < bucket_end \<alpha> T b0"
            by blast
          with same_bucket_same_hd[OF l_perm_inv_elims(8,9,6,5)[OF assms(1)], of b0 i']
               l_perm_inv_elims(2,3,14,15)[OF assms(1)]
          have "\<alpha> (T ! (SA ! i')) = b0"
            using \<open>SA ! i' < length T\<close> \<open>i' < length SA\<close> by auto

          from index_in_bucket_interval_gen[OF `i < length T` l_perm_inv_elims(12)[OF assms(1)]]
          obtain b1 where
            "b1 \<le> \<alpha> (Max (set T))"
            "bucket_start \<alpha> T b1 \<le> i"
            "i < bucket_end \<alpha> T b1"
            by blast
          with same_bucket_same_hd[OF l_perm_inv_elims(8,9,6,5)[OF assms(1)], of b1 i]
               l_perm_inv_elims(2,3,14,15)[OF assms(1)]
          have "\<alpha> (T ! (SA ! i)) = b1"
            using assms(4-6) by auto

          have "b0 \<le> b1"
          proof (rule ccontr)
            assume "\<not>b0 \<le> b1"
            hence "b1 < b0"
              by auto
            hence "bucket_end \<alpha> T b1 \<le> bucket_start \<alpha> T b0"
              by (simp add: less_bucket_end_le_start)
            with `i < bucket_end \<alpha> T b1` `bucket_start \<alpha> T b0 \<le> i'` `i' < i`
            show False
              by linarith
          qed
          hence "b0 < b1 \<or> b0 = b1"
            by linarith
          moreover
          have "b0 < b1 \<Longrightarrow> ?thesis"
          proof -
            assume "b0 < b1"
            with `\<alpha> (T ! (SA ! i')) = b0` `\<alpha> (T ! (SA ! i)) = b1`
            have "T ! (SA ! i') < T ! (SA ! i)"
              using assms(1) l_perm_inv_elims(12) strict_mono_less by blast
            moreover
            have "\<exists>as. lms_prefix T (SA ! i') = T ! (SA ! i') # as"
              by (metis \<open>SA ! i' < length T\<close> lms_slice_hd 
                        lms_lms_prefix not_lms_imp_next_eq_lms_prefix)
            then obtain as where
              "lms_prefix T (SA ! i') = T ! (SA ! i') # as"
              by blast
            moreover
            have "\<exists>bs. lms_prefix T (SA ! i) = T ! (SA ! i) # bs"
              by (metis (full_types) SL_types.exhaust assms(5-7) abs_is_lms_def
                                     l_type_lms_prefix_cons lms_lms_prefix)
            then obtain bs where
              "lms_prefix T (SA ! i) = T ! (SA ! i) # bs"
              by blast
            ultimately show ?thesis
              by (simp add: less_le list_less_eq_ns_cons)
          qed
          moreover
          have "b0 = b1 \<Longrightarrow> ?thesis"
          proof -
            assume "b0 = b1"
            hence "\<alpha> (T ! (SA ! i')) = \<alpha> (T ! (SA ! i))"
              by (simp add: \<open>\<alpha> (T ! (SA ! i')) = b0\<close> \<open>\<alpha> (T ! (SA ! i)) = b1\<close>)
            hence "T ! (SA ! i') = T ! (SA ! i)"
              by (metis (no_types, opaque_lifting) assms(1) strict_mono_less
                        l_perm_inv_elims(12) not_less_iff_gr_or_eq)

            have "i < bucket_end \<alpha> T b0"
              by (simp add: \<open>b0 = b1\<close> \<open>i < bucket_end \<alpha> T b1\<close>)

            from unknown_range_values
                    [OF l_perm_inv_elims(8,5)[OF assms(1)] _ _
                        l_perm_inv_elims(14,15)[OF assms(1)] `b0 \<le> \<alpha> _`]
                 l_perm_inv_elims(2,3)[OF assms(1)]
            have "i < B ! b0 \<or> lms_bucket_start \<alpha> T b0 \<le> i"
              using assms(5) assms(6) not_le by force

            from unknown_range_values
                    [OF l_perm_inv_elims(8,5)[OF assms(1)] _ _
                        l_perm_inv_elims(14,15)[OF assms(1)] `b0 \<le> \<alpha> _`]
                 l_perm_inv_elims(2,3)[OF assms(1)]
                 `SA ! i' < length T`
            have "i' < B ! b0 \<or> lms_bucket_start \<alpha> T b0 \<le> i'"
              using not_le by force
            moreover
            have "i' < B ! b0 \<Longrightarrow> ?thesis"
            proof -
              assume "i' < B ! b0"
              have "i < B ! b0 \<Longrightarrow> ?thesis"
              proof -
                assume "i < B ! b0"
                let ?xs = "list_slice SA (bucket_start \<alpha> T b0) (B ! b0)"

                have "i' \<le> i"
                  by (simp add: \<open>i' < i\<close> less_imp_le_nat)
                from l_prefix_sorted_invD[OF assms(3) `b0 \<le> \<alpha> _`]
                have "ordlistns.sorted (map (lms_prefix T) ?xs)" .
                with ordlistns.list_slice_sorted_nth_mono
                            [OF _ `bucket_start \<alpha> T b0 \<le> i'` `i' \<le> i`
                                `i < B ! b0`,
                             of "map (lms_prefix T) SA"]
                show ?thesis
                  by (metis \<open>i' < length SA\<close> assms(4) length_map map_list_slice nth_map)
              qed
              moreover
              have "lms_bucket_start \<alpha> T b0 \<le> i \<Longrightarrow> ?thesis"
              proof -
                assume "lms_bucket_start \<alpha> T b0 \<le> i"
                with lms_init_D[OF lms_init_unchanged
                                    [OF l_perm_inv_elims(8)[OF assms(1)]],
                                OF _ _ l_perm_inv_elims(14)[OF assms(1)] `b0 \<le> \<alpha> _`]
                     l_perm_inv_elims(2,3)[OF assms(1)]
                     `i < bucket_end \<alpha> T b0`
                have "SA ! i \<in> lms_bucket \<alpha> T b0"
                  by (metis bucket_end_le_length list_slice_nth_mem)
                hence "suffix_type T (SA ! i) = S_type"
                  by (metis \<open>b0 \<le> \<alpha> (Max (set T))\<close> 
                            \<open>i < bucket_end \<alpha> T b0\<close> 
                            \<open>length SA = length SA0\<close>
                            \<open>length SA0 = length T\<close> 
                            \<open>lms_bucket_start \<alpha> T b0 \<le> i\<close>
                            \<open>lms_init \<alpha> T SA0\<close> assms(1) 
                            abs_is_lms_def l_perm_inv_elims(8) lms_init_nth
                            lms_init_unchanged)
                moreover
                from l_locations_inv_D[OF l_perm_inv_elims(9)[OF assms(1)] `b0 \<le> \<alpha> _`
                                          `i' < length SA` `bucket_start \<alpha> T b0 \<le> i'`
                                          `i' < B ! b0`]
                have "suffix_type T (SA ! i') = L_type" "SA ! i' < length T"
                  by blast+
                ultimately show ?thesis
                  using lms_prefix_l_less_than_s_type[of "SA ! i" T "SA ! i'"]
                  by (simp add: \<open>T ! (SA ! i') = T ! (SA ! i)\<close> assms(5-6)
                                lms_prefix_l_less_than_s_type
                                ordlistns.dual_order.strict_implies_order)
              qed
              ultimately show ?thesis
                using \<open>i < B ! b0 \<or> lms_bucket_start \<alpha> T b0 \<le> i\<close> by blast
            qed
            moreover
            have "lms_bucket_start \<alpha> T b0 \<le> i' \<Longrightarrow> ?thesis"
            proof -
              assume "lms_bucket_start \<alpha> T b0 \<le> i'"

              let ?xs = "list_slice SA (lms_bucket_start \<alpha> T b0) (bucket_end \<alpha> T b0)"

              from l_prefix_sorted_pre_maintained[OF l_perm_inv_elims(8)[OF assms(1)]]
                    l_perm_inv_elims(2,3)[OF assms(1)]
                    l_prefix_sorted_preD[of \<alpha> T SA b0, OF _ `b0 \<le> \<alpha> _`]
              have "ordlistns.sorted (map (lms_prefix T) ?xs)"
                by (simp add: assms(2))
              with ordlistns.list_slice_sorted_nth_mono
                              [of "map (lms_prefix T) SA"
                                  "lms_bucket_start \<alpha> T b0"
                                  "bucket_end \<alpha> T b0" i' i]
                   \<open>i < bucket_end \<alpha> T b0\<close> \<open>i' < i\<close> 
                   \<open>i' < length SA\<close> 
                   \<open>lms_bucket_start \<alpha> T b0 \<le> i'\<close>
              show ?thesis
                by (metis assms(4) length_map map_list_slice 
                          not_less not_less_iff_gr_or_eq nth_map)
            qed
            ultimately show ?thesis
              by blast
          qed
          ultimately show ?thesis
            by blast
        qed
        ultimately show "list_less_eq_ns x y"
          by simp
      qed
      ultimately show ?thesis
        using ordlistns.sorted_append
                          [of "map (lms_prefix T) ?ys"
                              "[lms_prefix T j]"]
        by blast
    qed
    ultimately show ?thesis
      by simp
  qed
  ultimately show "ordlistns.sorted (map (lms_prefix T) ?xs)"
    by blast
qed

lemma abs_induce_l_suffix_sorted_step:
  assumes "l_perm_inv \<alpha> T B SA0 SA i"
  and     "l_suffix_sorted_pre \<alpha> T SA0"
  and     "l_suffix_sorted_inv \<alpha> T B SA"
  and     "abs_induce_l_step (B, SA, i) (\<alpha>, T) = (B', SA', i')"
  shows "l_suffix_sorted_inv \<alpha> T B' SA'"
proof (cases "i < length SA \<and> SA ! i < length T")
  assume "\<not> (i < length SA \<and> SA ! i < length T)"
  then show ?thesis
    using assms(3,4) by force
next
  assume A: "i < length SA \<and> SA ! i < length T"
  show ?thesis
  proof (cases "SA ! i")
    case 0
    then show ?thesis
      using assms(3,4) A by force
  next
    case (Suc j)
    assume B: "SA ! i = Suc j"
    show ?thesis
    proof (cases "suffix_type T j")
      case S_type
      then show ?thesis
        using assms(3,4) A B by force
    next
      case L_type
      then show ?thesis
        using assms(3,4) A B 
              l_suffix_sorted_inv_maintained_step
                 [OF assms(1-3), of j "\<alpha> (T ! j)" "B ! \<alpha> (T ! j)"]
        by (clarsimp simp: Let_def)
    qed
  qed
qed

lemma abs_induce_l_prefix_sorted_step:
  assumes "l_perm_inv \<alpha> T B SA0 SA i"
  and     "l_prefix_sorted_pre \<alpha> T SA0"
  and     "l_prefix_sorted_inv \<alpha> T B SA"
  and     "abs_induce_l_step (B, SA, i) (\<alpha>, T) = (B', SA', i')"
  shows "l_prefix_sorted_inv \<alpha> T B' SA'"
proof (cases "i < length SA \<and> SA ! i < length T")
  assume "\<not> (i < length SA \<and> SA ! i < length T)"
  then show ?thesis
    using assms(3,4) by force
next
  assume A: "i < length SA \<and> SA ! i < length T"
  show ?thesis
  proof (cases "SA ! i")
    case 0
    then show ?thesis
      using assms(3,4) A by force
  next
    case (Suc j)
    assume B: "SA ! i = Suc j"
    show ?thesis
    proof (cases "suffix_type T j")
      case S_type
      then show ?thesis
        using assms(3,4) A B by force
    next
      case L_type
      then show ?thesis
        using assms(3,4) A B 
              l_prefix_sorted_inv_maintained_step[OF assms(1-3), of j "\<alpha> (T ! j)" "B ! \<alpha> (T ! j)"]
        by (clarsimp simp: Let_def)
    qed
  qed
qed

lemma abs_induce_l_base_suffix_sorted_inv_maintained:
  assumes "l_perm_inv \<alpha> T B SA0 SA 0"
  and     "l_suffix_sorted_pre \<alpha> T SA0"
  and     "l_suffix_sorted_inv \<alpha> T B SA"
  and     "abs_induce_l_base \<alpha> T B SA = (B', SA', i)"
  shows "l_suffix_sorted_inv \<alpha> T B' SA'"
proof -
  let ?P = "\<lambda>(B, SA, i). l_perm_inv \<alpha> T B SA0 SA i \<and> l_suffix_sorted_inv \<alpha> T B SA"

  from assms(4)
  have "repeat (length T) abs_induce_l_step (B, SA, 0) (\<alpha>, T) = (B', SA', i)"
    by (simp add: abs_induce_l_base_def)
  moreover
  have "\<And>a. ?P a \<Longrightarrow> ?P (abs_induce_l_step a (\<alpha>, T))"
    using abs_induce_l_perm_step abs_induce_l_suffix_sorted_step assms(2) by blast
  ultimately show ?thesis
    using repeat_maintain_inv[of ?P abs_induce_l_step "(\<alpha>, T)" "(B, SA, 0)" "length T"]
    using assms(1,2,3) by auto
qed

lemma abs_induce_l_base_prefix_sorted_inv_maintained:
  assumes "l_perm_inv \<alpha> T B SA0 SA 0"
  and     "l_prefix_sorted_pre \<alpha> T SA0"
  and     "l_prefix_sorted_inv \<alpha> T B SA"
  and     "abs_induce_l_base \<alpha> T B SA = (B', SA', i)"
  shows "l_prefix_sorted_inv \<alpha> T B' SA'"
proof -
  let ?P = "\<lambda>(B, SA, i). l_perm_inv \<alpha> T B SA0 SA i \<and> l_prefix_sorted_inv \<alpha> T B SA"

  from assms(4)
  have "repeat (length T) abs_induce_l_step (B, SA, 0) (\<alpha>, T) = (B', SA', i)"
    by (simp add: abs_induce_l_base_def)
  moreover
  have "\<And>a. ?P a \<Longrightarrow> ?P (abs_induce_l_step a (\<alpha>, T))"
    using abs_induce_l_perm_step abs_induce_l_prefix_sorted_step assms(2) by blast
  ultimately show ?thesis
    using repeat_maintain_inv[of ?P abs_induce_l_step "(\<alpha>, T)" "(B, SA, 0)" "length T"]
    using assms(1,2,3) by auto
qed

section "L-type Exhaustiveness"

text "The @{const abs_induce_l} function is exhaustive if it has inserted all the L-types"

definition l_type_exhaustive :: "('a :: {linorder, order_bot}) list \<Rightarrow> nat list \<Rightarrow> bool"
  where
"l_type_exhaustive T SA = (\<forall>i < length T. suffix_type T i = L_type \<longrightarrow> i \<in> set SA)"

text "There two cases when the @{const abs_induce_l} function is not exhaustive: when there is an L-type that is
      not in SA but its successor (right neighbour) is in SA, and the other is when there is an
      L-type that is not in SA and its successor is also not in SA. We will show that both cases
      will be False."

lemma not_l_type_exhaustive_imp_ex:
  "\<not>l_type_exhaustive T SA \<Longrightarrow>
   (\<exists>i < length T. suffix_type T i = L_type \<and> i \<notin> set SA \<and> Suc i \<in> set SA) \<or>
   ((\<exists>i < length T. suffix_type T i = L_type \<and> i \<notin> set SA) \<and>
    \<not>(\<exists>i. i < length T \<and> suffix_type T i = L_type \<and> i \<notin> set SA \<and> Suc i \<in> set SA))"
  using l_type_exhaustive_def
  by blast

lemma l_type_exhaustive_imp_l_bucket:
  "\<lbrakk>strict_mono \<alpha>; l_type_exhaustive T SA; b \<le> \<alpha> (Max (set T))\<rbrakk> \<Longrightarrow>
   {i. i \<in> set SA \<and> i \<in> l_bucket \<alpha> T b} = l_bucket \<alpha> T b"
  by (intro equalityI subsetI; clarsimp simp add: bucket_def l_bucket_def l_type_exhaustive_def)

lemma l_type_exhaustive_imp_all_l_types:
  "l_type_exhaustive T SA \<Longrightarrow>
   {i. i \<in> set SA \<and> i \<in> l_bucket \<alpha> T (\<alpha> (T ! i))} = {i. i < length T \<and> suffix_type T i = L_type}"
  apply (intro equalityI subsetI; clarsimp)
  apply (simp add: bucket_def l_bucket_def)
  by (simp add: l_type_exhaustive_def bucket_def l_bucket_def)

subsection "Case 1"

text "In the case 1, we have that
      @{term \<open>\<exists>k < length T. suffix_type T k = L_type \<and> k \<notin> set SA \<and> Suc k \<in> set SA\<close>}.
      From this, we know that @{term \<open>\<exists>j < length SA. SA ! j = Suc k\<close>}"

lemma
  "Suc k \<in> set SA\<Longrightarrow> \<exists>j < length SA. SA ! j = Suc k"
  by (simp add: in_set_conv_nth)

text "After executing the @{const abs_induce_l} function, we know that we have seen"

subsection "Case 2"

text "In the case 2, we have that
      @{term \<open>\<exists>k < length T. suffix_type T k = L_type \<and> k \<notin> set SA \<and> Suc k \<notin> set SA\<close>}."

lemma finite_and_Suc_imp_False:
  assumes finite_A: "finite A"
  and     not_empty: "A \<noteq> {}"
  and     Suc_A: "\<forall>a \<in> A. Suc a \<in> A"
  shows "False"
proof -
  from Max_in[OF finite_A not_empty]
  have "Max A \<in> A" by assumption

  with Suc_A bspec
  have "Suc (Max A) \<in> A" by blast

  with `Max A \<in> A` finite_A
  show ?thesis
    using Max_ge Suc_n_not_le_n by blast
qed

lemma not_exhaustive_neighbour_is_l_type:
  assumes A: "A = {k |k. suffix_type T k = L_type \<and> k \<notin> B \<and> Suc k \<notin> B \<and> k < length T}"
  and     subset_B: "{k |k. abs_is_lms T k} \<subseteq> B"
  and     "k \<in> A"
  shows "suffix_type T (Suc k) = L_type"
proof -
  from A `k \<in> A`
  have "Suc k \<notin> B"
    by blast
  with subset_B
  have "\<not>abs_is_lms T (Suc k)"
    by blast

  from A `k \<in> A`
  have "suffix_type T k = L_type"
    by blast

  with `~abs_is_lms T (Suc k)`
  show ?thesis
    by (meson abs_is_lms_def suffix_type_def)
qed

lemma no_exhausted_neighbour:
  assumes A: "A = {k |k. suffix_type T k = L_type \<and> k \<notin> B \<and> Suc k \<notin> B \<and> k < length T}"
  and     B: "{k |k. abs_is_lms T k} \<subseteq> B"
  and     C: "\<not>(\<exists>k. k < length T \<and> suffix_type T k = L_type \<and> k \<notin> B \<and> Suc k \<in> B)"
  and     D: "suffix_type T i = L_type"
  and     E: "i \<notin> B"
  and     F: "i < length T"
  shows "i \<in> A"
proof -
  from C[simplified] D E F
  have "Suc i \<notin> B"
    by blast

  with A D E F
  show ?thesis
    by blast
qed

lemma l_type_less_length_imp_neightbour_less_length:
  "\<lbrakk>suffix_type T i = L_type; i < length T\<rbrakk> \<Longrightarrow> Suc i < length T"
  by (metis SL_types.simps(2) Suc_lessI suffix_type_last)

lemma no_exhausted_neighbour_imp_False:
  assumes A: "A = {k |k. suffix_type T k = L_type \<and> k \<notin> B \<and> Suc k \<notin> B \<and> k < length T}"
  and     B: "{k |k. abs_is_lms T k} \<subseteq> B"
  and     C: "\<not>(\<exists>k. k < length T \<and> suffix_type T k = L_type \<and> k \<notin> B \<and> Suc k \<in> B)"
  and     nempty: "A \<noteq> {}"
  shows   "False"
proof -

  from A
  have "finite A"
    by auto

  have "\<forall>a \<in> A. Suc a \<in> A"
  proof
    fix a
    assume "a \<in> A"
    with not_exhaustive_neighbour_is_l_type[OF A B]
    have "suffix_type T (Suc a) = L_type"
      by blast

    from `a \<in> A` A
    have "Suc a < length T"
      by (simp add: l_type_less_length_imp_neightbour_less_length)

    from `a \<in> A` A
    have "Suc a \<notin> B"
      by blast

    from no_exhausted_neighbour[OF A B C `suffix_type T (Suc a) = L_type` `Suc a \<notin> B` `Suc a < length T`]
    show "Suc a \<in> A"
      by blast
  qed

  with `finite A` nempty
  show ?thesis
    using finite_and_Suc_imp_False by blast
qed

subsection "Exhaustiveness Proof"

lemma abs_induce_l_exhaustive:
  assumes "l_seen_inv T SA (length SA)"
  and     "lms_init \<alpha> T SA0"
  and     "length SA = length SA0"
  and     "length SA = length T"
  and     "strict_mono \<alpha>"
  and     "l_unchanged_inv \<alpha> T SA0 SA"
  shows "l_type_exhaustive T SA"
proof(rule ccontr)

  let ?P = "\<exists>i<length T. suffix_type T i = L_type \<and> i \<notin> set SA \<and> Suc i \<in> set SA" and
      ?Q1 = "\<exists>i<length T. suffix_type T i = L_type \<and> i \<notin> set SA" and
      ?Q2 = "\<not>(\<exists>i. i < length T \<and> suffix_type T i = L_type \<and> i \<notin> set SA \<and> Suc i \<in> set SA)"

  assume "\<not>l_type_exhaustive T SA"
  with not_l_type_exhaustive_imp_ex
  have "?P \<or> (?Q1 \<and> ?Q2)"
    by blast
  then show "False"
  proof
    assume ?P
    then obtain i where
      "i < length T"
      "suffix_type T i = L_type"
      "i \<notin> set SA"
      "Suc i \<in> set SA"
      by blast

    from `Suc i \<in> set SA`
    have "\<exists>k < length SA. SA ! k = Suc i"
      by (simp add: in_set_conv_nth)
    then obtain k where
      "k < length SA"
      "SA ! k = Suc i"
      by blast

    from l_type_less_length_imp_neightbour_less_length[OF `suffix_type T i = L_type` `i < length T`]
    have "Suc i < length T"
      by assumption

    from `l_seen_inv T SA (length SA)`
    have "\<forall>i < length SA. SA ! i < length T \<longrightarrow>
            (\<forall>j. SA ! i = Suc j \<and> suffix_type T j = L_type \<longrightarrow>
                (\<exists>k < length SA. SA ! k = j))"
      using l_seen_inv_def by blast
    with `k < length SA` `SA ! k = Suc i` `Suc i < length T`
    have "\<forall>j. SA ! k = Suc j \<and> suffix_type T j = L_type \<longrightarrow> (\<exists>k<length SA. SA ! k = j)"
      by auto
    with `SA ! k = Suc i` `suffix_type T i = L_type`
    have "\<exists>k<length SA. SA ! k = i"
      by blast
    with `i \<notin> set SA`
    show ?thesis
      using nth_mem by blast
  next
    assume "?Q1 \<and> ?Q2"
    then have "?Q1" "?Q2"
      by blast+
    then have "\<exists>A. A = {k |k. suffix_type T k = L_type \<and> k \<notin> set SA \<and> Suc k \<notin> set SA \<and> k < length T}"
      by blast
    then obtain A where
      A_eq: "A = {k |k. suffix_type T k = L_type \<and> k \<notin> set SA \<and> Suc k \<notin> set SA \<and> k < length T}"
      by blast

    from `?Q1` `?Q2` A_eq
    have "A \<noteq> {}"
      by blast

    from lms_init_unchanged[OF `l_unchanged_inv \<alpha> T SA0 SA`
                               `length SA = length SA0`
                               `length SA = length T`
                               `lms_init \<alpha> T SA0`]
         lms_init_imp_all_lms_in_SA[OF _ `strict_mono \<alpha>`]
    have lms_subset_SA : "{k |k. abs_is_lms T k} \<subseteq> set SA"
      by blast

    from no_exhausted_neighbour_imp_False[OF A_eq lms_subset_SA `?Q2` `A \<noteq> {}`]
    show ?thesis
      by assumption
  qed
qed

section "Correctness and Exhaustiveness"

lemma abs_induce_l_perm_inv_imp_exhaustiveness:
  assumes "abs_induce_l_base \<alpha> T B SA = (B', SA', i)"
  and     "l_perm_inv \<alpha> T B' SA SA' i"
shows "l_type_exhaustive T SA'"
proof -
  from abs_induce_l_index[of \<alpha> T B SA] assms(1)
  have "i = length T"
    by simp
  hence "i = length SA'"
    using assms(2) l_perm_inv_elims(2,3) by fastforce
  hence P: "l_perm_inv \<alpha> T B' SA SA' (length SA')"
    using assms(2) by blast

  have "length SA' = length T"
    using \<open>i = length SA'\<close> \<open>i = length T\<close> by blast
  with abs_induce_l_exhaustive[OF l_perm_inv_elims(11,14,3)[OF P] _ l_perm_inv_elims(12,8)[OF P]]
  show ?thesis .
qed

lemma abs_induce_l_perm_inv_B_val:
  assumes "abs_induce_l_base \<alpha> T B SA = (B', SA', i)"
  and     "l_perm_inv \<alpha> T B' SA SA' i"
  and     "b \<le> \<alpha> (Max (set T))"
shows "B' ! b = l_bucket_end \<alpha> T b"
proof -
from abs_induce_l_perm_inv_imp_exhaustiveness[OF assms(1-2)]
  have "l_type_exhaustive T SA'"
    by assumption

  have "strict_mono \<alpha>"
    using assms(2) l_perm_inv_elims(12) by blast

  from l_bucket_ptr_inv_D[OF l_perm_inv_elims(6)[OF assms(2)] assms(3)]
  have "B' ! b = bucket_start \<alpha> T b + num_l_types \<alpha> T SA' b"
    by blast
  moreover
  from l_type_exhaustive_imp_l_bucket[OF `strict_mono \<alpha>` `l_type_exhaustive T SA'` assms(3)]
  have "cur_l_types \<alpha> T SA' b = l_bucket \<alpha> T b"
    unfolding cur_l_types_def
    by blast
  hence "num_l_types \<alpha> T SA' b = l_bucket_size \<alpha> T b"
    by (simp add: l_bucket_size_def num_l_types_def)
  ultimately
  show ?thesis
    by (simp add: l_bucket_end_def)
qed

theorem abs_induce_l_distinct_l_bucket:
  assumes "l_perm_pre \<alpha> T B SA"
  and     "b \<le> \<alpha> (Max (set T))"
shows "distinct (list_slice (abs_induce_l \<alpha> T B SA) (bucket_start \<alpha> T b) (l_bucket_end \<alpha> T b))"
proof -
  from abs_induce_l_index[of \<alpha> T B SA]
  obtain B' SA' where
    A: "abs_induce_l_base \<alpha> T B SA = (B', SA', length T)"
    by blast
  with abs_induce_l_base_perm_inv_maintained[OF l_perm_inv_established[OF assms(1)],
                                         of B' SA' "length T"]
  have B: "l_perm_inv \<alpha> T B' SA SA' (length T)" .
  with abs_induce_l_perm_inv_B_val[OF A _ assms(2)]
  have "B' ! b = l_bucket_end \<alpha> T b" .
  with l_distinct_slice[OF l_perm_inv_elims(4,9)[OF B] _ assms(2)] l_perm_inv_elims(2,3)[OF B]
  have "distinct (list_slice SA' (bucket_start \<alpha> T b) (l_bucket_end \<alpha> T b))"
    by simp
  then show ?thesis
    by (simp add: A abs_induce_l_def)
qed

theorem abs_induce_l_list_slice_l_bucket:
  assumes "l_perm_pre \<alpha> T B SA"
  and     "b \<le> \<alpha> (Max (set T))"
shows "set (list_slice (abs_induce_l \<alpha> T B SA) (bucket_start \<alpha> T b) (l_bucket_end \<alpha> T b)) = l_bucket \<alpha> T b"
      (is "set ?xs = l_bucket \<alpha> T b")
proof -
  from abs_induce_l_index[of \<alpha> T B SA]
  obtain B' SA' where
    A: "abs_induce_l_base \<alpha> T B SA = (B', SA', length T)"
    by blast
  with abs_induce_l_base_perm_inv_maintained[OF l_perm_inv_established[OF assms(1)],
                                         of B' SA' "length T"]
  have B: "l_perm_inv \<alpha> T B' SA SA' (length T)" .
  with abs_induce_l_perm_inv_B_val[OF A _ assms(2)]
  have "B' ! b = l_bucket_end \<alpha> T b" .
  with l_locations_list_slice[OF l_perm_inv_elims(9)[OF B] assms(2)]
  have "set (list_slice SA' (bucket_start \<alpha> T b) (l_bucket_end \<alpha> T b)) \<subseteq> l_bucket \<alpha> T b"
    by simp
  hence "set ?xs \<subseteq> l_bucket \<alpha> T b"
    by (simp add: A abs_induce_l_def)
  moreover
  from distinct_card[OF abs_induce_l_distinct_l_bucket[OF assms]]
  have "card (set ?xs) = length ?xs" .
  hence "card (set ?xs) = l_bucket_end \<alpha> T b - bucket_start \<alpha> T b"
    by (metis B bucket_end_le_length abs_induce_l_length l_bucket_end_le_bucket_end l_perm_inv_elims(2)
              le_trans length_list_slice min_def)
  hence "card (set ?xs) = card (l_bucket \<alpha> T b)"
    by (simp add: l_bucket_end_def l_bucket_size_def)
  ultimately show ?thesis
    using card_subset_eq[OF finite_l_bucket]
    by blast
qed

lemma abs_induce_l_unchanged:
  assumes "l_perm_pre \<alpha> T B SA"
  and     "b \<le> \<alpha> (Max (set T))"
  and     "s_bucket_start \<alpha> T b \<le> i"
  and     "i < bucket_end \<alpha> T b"
shows "(abs_induce_l \<alpha> T B SA) ! i = SA ! i"
proof -
  from abs_induce_l_index[of \<alpha> T B SA]
  obtain B' SA' where
    A: "abs_induce_l_base \<alpha> T B SA = (B', SA', length T)"
    by blast
  with abs_induce_l_base_perm_inv_maintained[OF l_perm_inv_established[OF assms(1)],
                                         of B' SA' "length T"]
  have B: "l_perm_inv \<alpha> T B' SA SA' (length T)" .

  have "i < length SA"
    by (metis B assms(4) bucket_end_le_length l_perm_inv_elims(2) le_less_trans not_less_eq)
  moreover
  have "l_bucket_end \<alpha> T b \<le> i"
    by (metis assms(3) s_bucket_start_eq_l_bucket_end)
  ultimately have "SA' ! i = SA ! i"
    using l_unchanged_inv_D[OF l_perm_inv_elims(8,3)[OF B] assms(2) _ _  assms(4)]
    by auto
  then show ?thesis
    by (simp add: A abs_induce_l_def)
qed

 \<comment>\<open> Used in SAIS algorithm as part of inducing the suffix ordering based on LMS \<close>
theorem abs_induce_l_suffix_sorted_l_bucket:
  assumes "l_perm_pre \<alpha> T B SA"
  and     "l_suffix_sorted_pre \<alpha> T SA"
  and     "b \<le> \<alpha> (Max (set T))"
shows "ordlistns.sorted (map (suffix T)
        (list_slice (abs_induce_l \<alpha> T B SA) (bucket_start \<alpha> T b) (l_bucket_end \<alpha> T b)))"
proof -

  from l_perm_inv_established[OF assms(1)]
  have A: "l_perm_inv \<alpha> T B SA SA 0" .

  from l_suffix_sorted_inv_established[OF l_perm_pre_elims(4)[OF assms(1)], of SA]
  have D: "l_suffix_sorted_inv \<alpha> T B SA" .

  from abs_induce_l_index[of \<alpha> T B SA]
  obtain B' SA' where
    B: "abs_induce_l_base \<alpha> T B SA = (B', SA', length T)"
    by blast
  with abs_induce_l_base_perm_inv_maintained[OF A, of B' SA' "length T"]
  have C: "l_perm_inv \<alpha> T B' SA SA' (length T)" .
  with abs_induce_l_perm_inv_B_val[OF B _ assms(3)]
  have "B' ! b = l_bucket_end \<alpha> T b" .
  moreover
  from abs_induce_l_base_suffix_sorted_inv_maintained[OF A assms(2) D B]
  have "l_suffix_sorted_inv \<alpha> T B' SA'" .
  ultimately show ?thesis
    using l_suffix_sorted_invD[of \<alpha> T B' SA', OF _ assms(3)]
    by (simp add: B abs_induce_l_def)
qed

 \<comment>\<open> Used in SAIS algorithm as part of inducing the prefix ordering based on LMS \<close>
theorem abs_induce_l_prefix_sorted_l_bucket:
  assumes "l_perm_pre \<alpha> T B SA"
  and     "l_prefix_sorted_pre \<alpha> T SA"
  and     "b \<le> \<alpha> (Max (set T))"
shows "ordlistns.sorted (map (lms_prefix T)
        (list_slice (abs_induce_l \<alpha> T B SA) (bucket_start \<alpha> T b) (l_bucket_end \<alpha> T b)))"
proof -

  from l_perm_inv_established[OF assms(1)]
  have A: "l_perm_inv \<alpha> T B SA SA 0" .

  from l_prefix_sorted_inv_established[OF l_perm_pre_elims(4)[OF assms(1)], of SA]
  have D: "l_prefix_sorted_inv \<alpha> T B SA" .

  from abs_induce_l_index[of \<alpha> T B SA]
  obtain B' SA' where
    B: "abs_induce_l_base \<alpha> T B SA = (B', SA', length T)"
    by blast
  with abs_induce_l_base_perm_inv_maintained[OF A, of B' SA' "length T"]
  have C: "l_perm_inv \<alpha> T B' SA SA' (length T)" .
  with abs_induce_l_perm_inv_B_val[OF B _ assms(3)]
  have "B' ! b = l_bucket_end \<alpha> T b" .
  moreover
  from abs_induce_l_base_prefix_sorted_inv_maintained[OF A assms(2) D B]
  have "l_prefix_sorted_inv \<alpha> T B' SA'" .
  ultimately show ?thesis
    using l_prefix_sorted_invD[of \<alpha> T B' SA', OF _ assms(3)]
    by (simp add: B abs_induce_l_def)
qed

end