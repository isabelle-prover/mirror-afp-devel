theory LMS_List_Slice_Util
  imports List_Type
begin

section \<open>Helpers\<close>

lemma filter_abs_is_lms_upt_0:
  "filter (abs_is_lms xs) [0..<n] = filter (abs_is_lms xs) [Suc 0..<n]"
  by (metis filter.simps(2) abs_is_lms_0 tl_upt upt_0 upt_rec)

lemma filter_abs_is_lms_upt_hd:
  "\<lbrakk>abs_is_lms xs i; i < n\<rbrakk> \<Longrightarrow>
   filter (abs_is_lms xs) [i..<n] = i # filter (abs_is_lms xs) [Suc i..<n]"
  by (metis filter.simps(2) upt_rec)


section \<open>LMS Slice\<close>

subsection \<open>Find the next LMS position\<close>

fun 
  abs_find_index' :: "('a \<Rightarrow> bool) \<Rightarrow> 'a list \<Rightarrow> nat \<Rightarrow> nat"
where
  "abs_find_index' P xs i =
    (case xs of
      [] \<Rightarrow> i
      | x#xs' \<Rightarrow>
        (if P x 
           then i
           else abs_find_index' P xs' (Suc i)))"

definition 
  abs_find_next_lms :: "('a :: {linorder, order_bot}) list \<Rightarrow> nat \<Rightarrow> nat"
where
  "abs_find_next_lms T i =
    (case find (\<lambda>j. abs_is_lms T j) [Suc i..<length T] of
       Some j \<Rightarrow> j
     | _ \<Rightarrow> length T)"

lemma abs_find_next_lms_le_length:
  "abs_find_next_lms T i \<le> length T"
  unfolding abs_find_next_lms_def
  apply (clarsimp split: option.split)
  by (metis find_Some_iff abs_is_lms_gre_length not_less order.order_iff_strict)

lemma abs_find_next_lms_abs_is_lms:
  "abs_is_lms T (Suc i) \<Longrightarrow> abs_find_next_lms T i = Suc i"
  unfolding abs_find_next_lms_def
  apply (frule abs_is_lms_imp_less_length)
  apply (clarsimp split: option.split simp: upt_rec)
  done

lemma Suc_not_lms_imp_abs_find_next_eq_Suc:
  "\<not> abs_is_lms T (Suc i) \<Longrightarrow> abs_find_next_lms T i = abs_find_next_lms T (Suc i)"
  unfolding abs_find_next_lms_def
  by (simp add: upt_rec)

lemma abs_find_next_lms_lower_bound_1:
  "i < length T \<Longrightarrow> i < abs_find_next_lms T i"
  unfolding abs_find_next_lms_def
  apply (clarsimp split: option.split)
  using findSomeD by fastforce

lemma abs_find_next_lms_lower_bound_2:
  "length T \<le> i \<Longrightarrow> length T \<le> abs_find_next_lms T i"
  unfolding abs_find_next_lms_def
  by (clarsimp split: option.split)

lemma abs_find_next_lms_le_Suc:
  "abs_find_next_lms T i \<le> abs_find_next_lms T (Suc i)"
  apply (cases "Suc i < length T")
   apply (metis find.simps(2) abs_find_next_lms_def abs_find_next_lms_abs_is_lms abs_find_next_lms_lower_bound_1
            le_less upt_rec)
  by (simp add: abs_find_next_lms_def)

lemma no_lms_between_i_and_next:
  "\<lbrakk>i < k; k < abs_find_next_lms T i\<rbrakk> \<Longrightarrow> \<not>abs_is_lms T k"
  unfolding abs_find_next_lms_def
  apply (clarsimp split: option.splits)
   apply (drule findNoneD)
   apply (erule ballE[of _ _ k])
    apply blast
   apply simp
  apply (drule find_Some_iff[THEN iffD1])
  apply clarsimp
  apply (erule allE[of _ "k - Suc i"])
  apply clarsimp
  done

lemma abs_find_next_lms_less_length_abs_is_lms:
  "abs_find_next_lms T i < length T \<Longrightarrow> 
    abs_is_lms T (abs_find_next_lms T i)"
  unfolding abs_find_next_lms_def
  apply (clarsimp split: option.splits)
  apply (drule find_Some_iff[THEN iffD1])
  apply clarsimp
  done

lemma abs_find_next_lms_strict_upper_imp_lower_bound:
  "abs_find_next_lms T i < length T \<Longrightarrow> 
    i < abs_find_next_lms T i"
  unfolding abs_find_next_lms_def
  apply (clarsimp split: option.splits)
  using findSomeD by fastforce

lemma abs_find_next_lms_suffix:
  assumes "i \<le> length T"
  shows "abs_find_next_lms T i = 
         i + abs_find_next_lms (suffix T i) 0"
proof -
  from abs_is_lms_i_gr_0[of _ i T] no_lms_between_i_and_next[of i _ T]
  have P: "\<And>k. \<lbrakk>0 < k; k < abs_find_next_lms T i - i\<rbrakk> \<Longrightarrow> \<not>abs_is_lms (suffix T i) k"
    by (meson less_add_same_cancel2 less_diff_conv)

  have "abs_find_next_lms T i = length T \<or> abs_find_next_lms T i < length T"
    using abs_find_next_lms_le_length le_neq_implies_less by blast
  moreover
  have "abs_find_next_lms T i = length T \<Longrightarrow> ?thesis"
  proof -
    assume "abs_find_next_lms T i = length T"
    hence "\<And>k. \<lbrakk>0 < k; k < length T - i\<rbrakk> \<Longrightarrow> \<not>abs_is_lms (suffix T i) k"
      using P by presburger
    hence "abs_find_next_lms (suffix T i) 0 = length T - i"
      by (metis abs_find_next_lms_le_length abs_find_next_lms_less_length_abs_is_lms
                abs_find_next_lms_strict_upper_imp_lower_bound le_neq_implies_less length_drop)
    then show ?thesis
      by (simp add: \<open>abs_find_next_lms T i = length T\<close> assms)
  qed
  moreover
  have "abs_find_next_lms T i < length T \<Longrightarrow> ?thesis"
  proof -
    assume "abs_find_next_lms T i < length T"
    hence "abs_is_lms T (abs_find_next_lms T i)"
      using abs_find_next_lms_less_length_abs_is_lms by blast
    hence "abs_is_lms (suffix T i) (abs_find_next_lms T i - i)"
      by (simp add: abs_is_lms_i_gr_0 \<open>abs_find_next_lms T i < length T\<close>
                    abs_find_next_lms_strict_upper_imp_lower_bound less_or_eq_imp_le)
    with P
    show ?thesis
      by (metis add.commute abs_find_next_lms_le_length abs_find_next_lms_less_length_abs_is_lms
                abs_find_next_lms_strict_upper_imp_lower_bound abs_is_lms_imp_less_length
                le_neq_implies_less length_drop less_or_eq_imp_le nat_neq_iff
                no_lms_between_i_and_next ordered_cancel_comm_monoid_diff_class.diff_add
                zero_less_diff)
  qed
  ultimately show ?thesis
    by blast
qed

lemma abs_find_next_lms_cons_Suc:
  assumes "i \<le> length xs"
  shows "abs_find_next_lms (x # xs) (Suc i) = 
          Suc (abs_find_next_lms xs i)"
proof -
  have "abs_find_next_lms xs i = length xs \<or> abs_find_next_lms xs i < length xs"
    using abs_find_next_lms_le_length le_neq_implies_less by blast
  moreover
  have "abs_find_next_lms xs i = length xs \<Longrightarrow> ?thesis"
    by (metis Suc_le_mono add.assoc assms drop_Suc_Cons 
              abs_find_next_lms_suffix length_Cons plus_1_eq_Suc)
  moreover
  have "abs_find_next_lms xs i < length xs \<Longrightarrow> ?thesis"
    by (metis (no_types, lifting) Suc_le_mono add.assoc length_Cons
              assms drop_Suc_Cons abs_find_next_lms_suffix plus_1_eq_Suc)
  ultimately show ?thesis
    by blast
qed

lemma abs_find_next_lms_funpow_Suc:
  "((abs_find_next_lms T)^^(Suc k)) i = 
    abs_find_next_lms T (((abs_find_next_lms T)^^k) i)"
  by simp

lemma abs_find_next_lms_funpow_le:
  "i < length T \<Longrightarrow> 
    ((abs_find_next_lms T)^^k) i \<le> 
    ((abs_find_next_lms T)^^(Suc k)) i"
  apply (induct k; clarsimp)
   apply (simp add: abs_find_next_lms_lower_bound_1 less_or_eq_imp_le)
  by (simp add: abs_find_next_lms_le_Suc lift_Suc_mono_le)

lemma no_lms_between_i_and_next_funpow:
  "\<lbrakk>((abs_find_next_lms T)^^k) i < 
    ((abs_find_next_lms T)^^(Suc k)) i;
    ((abs_find_next_lms T)^^k) i < j; 
    j < ((abs_find_next_lms T)^^(Suc k)) i\<rbrakk> \<Longrightarrow>
     \<not> abs_is_lms T j"
  by (simp add: no_lms_between_i_and_next)

lemma abs_find_next_lms_eq_Suc:
  "xs \<noteq> [] \<Longrightarrow> \<exists>k. abs_find_next_lms xs i = Suc k"
  by (metis abs_find_next_lms_less_length_abs_is_lms 
            abs_is_lms_0 length_greater_0_conv not0_implies_Suc)

lemma filter_no_lms1:
  "\<lbrakk>abs_is_lms xs i; i < k; k \<le> abs_find_next_lms xs i\<rbrakk> \<Longrightarrow>
   filter (abs_is_lms xs) [Suc i..<k] = []"
proof (induct k)
  case 0
  then show ?case
    by simp
next
  case (Suc k)
  then show ?case
    by (metis Suc_leD Suc_le_eq append_Nil filter.simps(1,2)
              upt_Suc filter_append no_lms_between_i_and_next)
qed

lemma filter_no_lms2:
  "\<lbrakk>\<not>abs_is_lms xs i; i < k; k \<le> abs_find_next_lms xs i\<rbrakk> \<Longrightarrow>
   filter (abs_is_lms xs) [i..<k] = []"
proof (induct k)
  case 0
  then show ?case
    by simp
next
  case (Suc k)
  then show ?case
    by (metis Suc_le_eq append_Nil filter.simps(1) 
              filter.simps(2) filter_append 
              not_less_eq_eq upt.simps(2) nle_le
              no_lms_between_i_and_next upt_conv_Cons)
qed

subsection \<open>LMS Prefix\<close>

fun 
  closest_lms ::
    "('a :: {linorder, order_bot}) list \<Rightarrow> nat \<Rightarrow> nat"
where
  "closest_lms T i = 
     (if abs_is_lms T i 
      then i 
      else abs_find_next_lms T i)"

definition 
  lms_prefix ::  
     "('a :: {linorder, order_bot}) list \<Rightarrow> nat \<Rightarrow> 'a list"
where
  "lms_prefix T i = 
    list_slice T i (Suc (closest_lms T i))"


lemma lms_lms_prefix:
  "abs_is_lms T i \<Longrightarrow> lms_prefix T i = [T ! i]"
  unfolding lms_prefix_def
  by (simp add: abs_is_lms_imp_less_length list_slice_Suc)

lemma suffix_to_lms_prefix:
  "i < length T \<Longrightarrow>
     suffix T i = 
     lms_prefix T i @ 
       (list_slice T (Suc (closest_lms T i)) (length T))"
  unfolding lms_prefix_def
  apply clarsimp
  apply (intro impI conjI)
   apply (rule suffix_to_list_slice_app)
   apply linarith
  by (meson abs_find_next_lms_lower_bound_1 less_SucI 
            less_or_eq_imp_le suffix_to_list_slice_app)

lemma abs_find_next_lms_funpow_all_lms:
  "\<lbrakk>abs_is_lms xs ((abs_find_next_lms xs ^^ Suc k) x); 
      i \<le> k\<rbrakk> \<Longrightarrow>
   abs_is_lms xs ((abs_find_next_lms xs ^^ Suc i) x)"
proof (induct k arbitrary: i)
  case 0
  then show ?case
    by blast
next
  case (Suc k)
  note IH = this
  hence "(abs_find_next_lms xs ^^ Suc (Suc k)) x < length xs"
    using abs_is_lms_imp_less_length by blast
  moreover
  have "x < length xs"
    by (metis calculation abs_find_next_lms_funpow_Suc 
              abs_find_next_lms_le_length abs_find_next_lms_lower_bound_2 
              abs_find_next_lms_strict_upper_imp_lower_bound funpow_swap1
              linorder_not_less nat_neq_iff)
  ultimately 
  have "(abs_find_next_lms xs ^^ Suc k) x < length xs"
    using abs_find_next_lms_funpow_le order.strict_trans1 by blast
  hence P: "abs_is_lms xs ((abs_find_next_lms xs ^^ Suc k) x)"
    by (simp add: abs_find_next_lms_less_length_abs_is_lms)

  from IH(3)
  have "i \<le> k \<or> i = Suc k"
    by (meson le_Suc_eq le_neq_implies_less)
  moreover
  from IH(1)[OF P, of i]
  have "i \<le> k \<Longrightarrow> ?case"
    by blast
  moreover
  from IH(2)
  have "i = Suc k \<Longrightarrow> ?case"
    by simp
  ultimately show ?case
    by blast
qed

subsection \<open>LMS Slice\<close>

definition 
  lms_slice ::  "('a :: {linorder, order_bot}) list \<Rightarrow> nat \<Rightarrow> 'a list"
where
  "lms_slice T i = 
   list_slice T i (Suc (abs_find_next_lms T i))"

lemma suffix_to_lms_slice:
  "i < length T \<Longrightarrow>
   suffix T i = 
   lms_slice T i @ 
     (list_slice T (Suc (abs_find_next_lms T i)) (length T))"
  unfolding lms_slice_def
  apply (rule suffix_to_list_slice_app)
  by (simp add: abs_find_next_lms_lower_bound_1 
                le_Suc_eq less_or_eq_imp_le)

lemma suffix_to_lms_slice_app_suffix:
  "i < length T \<Longrightarrow>
   suffix T i = 
   lms_slice T i @ 
     (suffix T (Suc (abs_find_next_lms T i)))"
  by (metis suffix_eq_list_slice suffix_to_lms_slice)

lemma lms_slice_cons:
  "\<lbrakk>i < length T; suffix_type T i = S_type\<rbrakk> \<Longrightarrow>
   lms_slice T i = 
   T ! i # lms_slice T (Suc i)" 
  using abs_is_lms_def Suc_not_lms_imp_abs_find_next_eq_Suc 
        abs_find_next_lms_lower_bound_1 i_s_type_imp_Suc_i_not_lms 
        list_slice_Suc Suc_not_lms_imp_abs_find_next_eq_Suc
  by (clarsimp simp: lms_slice_def) fastforce

lemma lms_slice_hd:
  "i < length T \<Longrightarrow> 
   \<exists>xs. lms_slice T i = T ! i # xs"
  by (simp add: abs_find_next_lms_lower_bound_1 less_SucI list_slice_Suc lms_slice_def)

lemma lms_slice_suffix:
  assumes "i \<le> length T"
  shows "lms_slice (suffix T i) 0 = 
         lms_slice T i"
proof -
  from list_slice_suffix[of T i "Suc (abs_find_next_lms T i)"]
       lms_slice_def[of T i]
       abs_find_next_lms_suffix[OF assms]
       lms_slice_def[of "suffix T i" 0]
  show ?thesis
    by (metis add_Suc_right add_diff_cancel_left')
qed

lemma lms_slice_suffix_gen:
  assumes "i \<le> length T"
  and     "j \<le> length T - i"
shows "lms_slice (suffix T i) j = 
       lms_slice T (i + j)"
proof -
  have "lms_slice T (i + j) = 
        lms_slice (suffix T (i + j)) 0"
    by (metis add.commute assms lms_slice_suffix le_diff_conv2)
  hence "lms_slice T (i + j) = 
         lms_slice (suffix (suffix T i) j) 0"
    by (simp add: add.commute)
  moreover
  have "lms_slice (suffix T i) j = lms_slice (suffix (suffix T i) j) 0"
    by (metis assms(2) length_drop lms_slice_suffix)
  ultimately show ?thesis
    by simp
qed

lemma lms_slice_cons_Suc:
  "i \<le> length xs \<Longrightarrow> lms_slice (x # xs) (Suc i) = lms_slice xs i"
  by (metis Suc_le_mono drop_Suc_Cons length_Cons lms_slice_suffix)

subsection \<open>LMS Substring butlast\<close>

definition lms_slice_butlast ::  "('a :: {linorder, order_bot}) list \<Rightarrow> nat \<Rightarrow> 'a list"
  where
"lms_slice_butlast T i = list_slice T i (abs_find_next_lms T i)"

lemma lms_slice_to_butlast_app:
  "abs_find_next_lms T i < length T \<Longrightarrow>
   lms_slice T i = lms_slice_butlast T i @ [T ! abs_find_next_lms T i]"
  unfolding lms_slice_def lms_slice_butlast_def
  apply (subst list_slice_append[of _ "abs_find_next_lms T i"])
    apply (simp add: abs_find_next_lms_strict_upper_imp_lower_bound order.strict_implies_order)
   apply simp
  by (simp add: list_slice_Suc)

lemma lms_slice_eq_butlast:
  "length T \<le> abs_find_next_lms T i \<Longrightarrow>
   lms_slice T i = lms_slice_butlast T i"
  by (metis le_SucI list_slice_end_gre_length lms_slice_butlast_def lms_slice_def)

lemma lms_slice_eq_suffix:
  "length T \<le> abs_find_next_lms T i \<Longrightarrow>
   lms_slice T i = suffix T i"
  by (simp add: list_slice.simps lms_slice_butlast_def lms_slice_eq_butlast)

lemma suffix_abs_find_next_lms:
  "abs_find_next_lms T i < length T \<Longrightarrow>
   suffix T i = lms_slice_butlast T i @ suffix T (abs_find_next_lms T i)"
  by (simp add: abs_find_next_lms_strict_upper_imp_lower_bound less_or_eq_imp_le list_slice_append
                lms_slice_butlast_def suffix_eq_list_slice)

subsection \<open>Suffix Types\<close>

lemma suffix_type_lms_slice_l_s:
  assumes "suffix_type T i = L_type"
  and     "suffix_type T (Suc i) = S_type"
  shows   "suffix_type (lms_slice T i) 0 = suffix_type T i"
proof -
  have "Suc i < length T"
    by (simp add: assms(2) suffix_type_s_bound)

  have "abs_is_lms T (Suc i)"
    by (simp add: assms abs_is_lms_def)
  hence "abs_find_next_lms T i = Suc i"
    by (simp add: abs_find_next_lms_abs_is_lms)
  hence "lms_slice T i = [T ! i, T ! Suc i]"
    by (metis Suc_n_not_le_n \<open>Suc i < length T\<close> le_Suc_eq not_le
              list_slice_Suc list_slice_n_n lms_slice_def)
  moreover
  have "T ! i > T ! Suc i"
    using \<open>abs_is_lms T (Suc i)\<close> abs_is_lms_neq by blast
  ultimately show ?thesis
    by (simp add: \<open>suffix_type T i = L_type\<close> suffix_type_cons_greater)
qed

lemma abs_find_next_lms_same_types:
  assumes "\<forall>k. i \<le> k \<and> k < length T \<longrightarrow> suffix_type T k = suffix_type T i"
  and     "i \<le> j"
shows "abs_find_next_lms T j = length T"
proof (cases "find (abs_is_lms T) [Suc j..<length T]")
  assume "find (abs_is_lms T) [Suc j..<length T] = None"
  then show "abs_find_next_lms T j = length T"
    by (simp add: abs_find_next_lms_def)
next
  fix x
  assume "find (abs_is_lms T) [Suc j..<length T] = Some x"
  hence "x < length T" "Suc j \<le> x" "abs_is_lms T x"
    using \<open>find (abs_is_lms T) [Suc j..<length T] = Some x\<close> findSomeD by force+
  hence "\<exists>y. x = Suc y"
    using abs_is_lms_def by blast
  then obtain y where
    "x = Suc y"
    by blast
  hence "suffix_type T y = L_type" "suffix_type T (Suc y) = S_type"
    using \<open>abs_is_lms T x\<close> abs_is_lms_def by auto

  have "i \<le> y"
    using \<open>Suc j \<le> x\<close> \<open>x = Suc y\<close> assms(2) le_trans by blast
  moreover
  have "y < length T"
    using Suc_lessD \<open>x < length T\<close> \<open>x = Suc y\<close> by blast
  ultimately have "suffix_type T i = L_type"
    by (metis \<open>suffix_type T y = L_type\<close> assms(1))

  have "i \<le> Suc y"
    by (simp add: \<open>i \<le> y\<close> le_SucI)
  moreover
  have "Suc y < length T"
    using \<open>x < length T\<close> \<open>x = Suc y\<close> by blast
  ultimately have "suffix_type T i = S_type"
    by (metis \<open>suffix_type T (Suc y) = S_type\<close> assms(1))
  with \<open>suffix_type T i = L_type\<close>
  have "x = length T"
    by simp
  then show ?thesis
    using \<open>x < length T\<close> by blast
qed

lemma lms_slice_same_types:
  assumes "\<forall>k. i \<le> k \<and> k < length T \<longrightarrow> suffix_type T k = suffix_type T i"
  and     "i \<le> j"
shows "lms_slice T j = suffix T j"
proof -
  have "abs_find_next_lms T j = length T"
    using assms abs_find_next_lms_same_types by blast
  then show ?thesis
    by (metis le0 le_add_same_cancel2 list_slice_end_gre_length lms_slice_def plus_1_eq_Suc
              suffix_eq_list_slice)
qed

lemma all_l_types_up_to_next_lms:
  "\<lbrakk>i \<le> k; k < abs_find_next_lms T i; suffix_type T i = L_type\<rbrakk> \<Longrightarrow> suffix_type T k = L_type"
proof(induct "k - i" arbitrary: k)
  case 0
  then show ?case by simp
next
  case (Suc x)
  have "\<exists>k'. k = Suc k'"
    using Suc.hyps(2) Suc_le_D diff_le_self by presburger
  then obtain k' where
    "k = Suc k'"
    by blast
  hence "x = k' - i"
    using Suc.hyps(2) by linarith
  moreover
  have "i \<le> k'"
    using Suc.hyps(2) \<open>k = Suc k'\<close> by linarith
  moreover
  have "k' < abs_find_next_lms T i"
    using Suc.prems(2) Suc_lessD \<open>k = Suc k'\<close> by blast
  ultimately have "suffix_type T k' = L_type"
    using Suc.hyps(1) Suc.prems(3) by blast

  have "i < k"
    by (simp add: \<open>i \<le> k'\<close> \<open>k = Suc k'\<close> le_imp_less_Suc)
  with  Suc.prems(2) no_lms_between_i_and_next[of i k T]
  have "\<not> abs_is_lms T k"
    by blast
  with \<open>suffix_type T k' = L_type\<close> \<open>k = Suc k'\<close>
  show ?case
    using SL_types.exhaust abs_is_lms_def by blast
qed

lemma abs_find_next_lms_eq_length:
  assumes "abs_find_next_lms T i = length T"
  and     "i < length T"
shows "suffix_type T i = S_type"
proof (rule ccontr)
  assume "suffix_type T i \<noteq> S_type"
  hence "suffix_type T i = L_type"
    using SL_types.exhaust by blast
  moreover
  have "\<exists>k. abs_find_next_lms T i = Suc k"
    by (metis assms(1) assms(2) not_less0 old.nat.exhaust)
  then obtain k where
    "abs_find_next_lms T i = Suc k"
    by blast
  moreover
  have "i \<le> k"
    using assms(1,2) calculation by linarith
  ultimately have "suffix_type T k = L_type"
    by (metis all_l_types_up_to_next_lms lessI)
  moreover
  have "length T = Suc k"
    using \<open>abs_find_next_lms T i = Suc k\<close> assms(1) by auto
  ultimately show False
    using suffix_type_last[of T k]
    by simp
qed

lemma abs_find_next_lms_eq_length_all_s_types:
  assumes "abs_find_next_lms T i = length T"
  and     "i \<le> j"
  and     "j < length T"
shows "suffix_type T j = S_type"
  by (metis assms abs_find_next_lms_eq_length abs_find_next_lms_le_length abs_find_next_lms_less_length_abs_is_lms
        abs_find_next_lms_lower_bound_1 le_neq_implies_less no_lms_between_i_and_next
        order.strict_trans1)

lemma abs_find_next_lms_first_l_after_s_type:
  assumes "abs_find_next_lms T i < length T"
  and     "suffix_type T i = S_type"
shows "\<exists>j>i. j < abs_find_next_lms T i \<and> (\<forall>k<j. i \<le> k \<longrightarrow> suffix_type T k = S_type) \<and>
        suffix_type T j = L_type"
proof -
  have "\<exists>j. abs_find_next_lms T i = Suc j"
    by (metis assms(2) abs_find_next_lms_lower_bound_1 not_less0 old.nat.exhaust suffix_type_s_bound)
  then obtain j where
    "abs_find_next_lms T i = Suc j"
    by blast
  hence "abs_is_lms T (Suc j)"
    using assms(1) abs_find_next_lms_less_length_abs_is_lms by fastforce
  hence "suffix_type T j = L_type"
    using SL_types.exhaust i_s_type_imp_Suc_i_not_lms by auto
  moreover
  have "j < length T"
    using \<open>abs_find_next_lms T i = Suc j\<close> assms(1) by linarith
  moreover
  have "i \<le> j"
    by (metis \<open>abs_find_next_lms T i = Suc j\<close> assms(1) abs_find_next_lms_strict_upper_imp_lower_bound
          less_Suc_eq_le)
  moreover
  have "\<forall>k>i. k \<le> j \<longrightarrow> \<not> abs_is_lms T k"
    by (simp add: \<open>abs_find_next_lms T i = Suc j\<close> no_lms_between_i_and_next)
  ultimately show ?thesis
    using first_l_type_after_s_type[OF _ _ _ _assms(2), of j]
    by (metis SL_types.simps(2) \<open>abs_find_next_lms T i = Suc j\<close> assms(2) dual_order.order_iff_strict
          le_imp_less_Suc)
qed

lemma lms_slice_type:
  assumes "i < length T"
  shows "suffix_type (lms_slice T i) 0 = suffix_type T i"
proof -
  have "\<exists>k. abs_find_next_lms T i = Suc k"
    by (meson Nat.lessE assms abs_find_next_lms_lower_bound_1)
  then obtain k where
    "abs_find_next_lms T i = Suc k"
    by blast

  have "suffix_type T i = L_type \<or> suffix_type T i = S_type"
    using SL_types.exhaust by blast
  moreover
  have "suffix_type T i = L_type \<Longrightarrow> ?thesis"
  proof -
    assume "suffix_type T i = L_type"

    have "suffix_type T (Suc i) = L_type \<or> suffix_type T (Suc i) = S_type"
      using SL_types.exhaust by blast
    moreover
    have "suffix_type T (Suc i) = S_type \<Longrightarrow> ?thesis"
      by (simp add: \<open>suffix_type T i = L_type\<close> suffix_type_lms_slice_l_s)
    moreover
    have "suffix_type T (Suc i) = L_type \<Longrightarrow> ?thesis"
    proof -
      assume "suffix_type T (Suc i) = L_type"

      from \<open>abs_find_next_lms T i = Suc k\<close>
      have P: "\<forall>k'\<ge>i. k' < Suc k \<longrightarrow> suffix_type T k' = L_type"
        by (simp add: \<open>suffix_type T i = L_type\<close> all_l_types_up_to_next_lms)

      have "lms_slice T i = list_slice T i (Suc (Suc k))"
        by (simp add: lms_slice_def \<open>abs_find_next_lms T i = Suc k\<close>)
      moreover
      {
        have "i < k"
          by (metis SL_types.simps(2) Suc_lessI \<open>abs_find_next_lms T i = Suc k\<close>
                \<open>suffix_type T (Suc i) = L_type\<close> \<open>suffix_type T i = L_type\<close> assms
                abs_find_next_lms_less_length_abs_is_lms abs_find_next_lms_lower_bound_1 less_antisym
                suffix_type_last suffix_type_same_imp_not_lms)
        hence "list_slice T i (Suc (Suc k)) = list_slice T i k @ list_slice T k (Suc (Suc k))"
          by (meson dual_order.order_iff_strict le_Suc_eq list_slice_append)
        moreover
        have "list_slice T k (Suc (Suc k)) = [T ! k, T ! (Suc k)]"
          by (metis SL_types.simps(2) \<open>abs_find_next_lms T i = Suc k\<close> \<open>suffix_type T i = L_type\<close>
                all_l_types_up_to_next_lms assms dual_order.order_iff_strict
                abs_find_next_lms_le_length less_Suc_eq_le list_slice_Suc list_slice_n_n
                not_less_eq suffix_type_last)
        moreover
        have "list_slice T i k = T ! i # list_slice T (Suc i) k"
          using \<open>i < k\<close> assms list_slice_Suc by blast
        ultimately have
          "list_slice T i (Suc (Suc k)) = T ! i # (list_slice T (Suc i) k) @ [T ! k, T ! Suc k]"
          by simp
      }
      ultimately have
        "lms_slice T i = T ! i # (list_slice T (Suc i) k) @ [T ! k, T ! Suc k]"
        by simp


      let ?bs = "list_slice T (Suc i) k"

      have "abs_is_lms T (Suc k)"
        by (metis SL_types.simps(2) \<open>abs_find_next_lms T i = Suc k\<close> \<open>suffix_type T i = L_type\<close>
              all_l_types_up_to_next_lms assms dual_order.order_iff_strict suffix_type_last
              abs_find_next_lms_le_length abs_find_next_lms_less_length_abs_is_lms less_Suc_eq_le)
      hence "T ! k > T ! Suc k"
        using abs_is_lms_neq by blast
      moreover
      from sorted_letters_l_types[OF P[simplified \<open>abs_find_next_lms T i = Suc k\<close>]]
      have "sorted (rev (list_slice T i (Suc k)))"
        using \<open>abs_is_lms T (Suc k)\<close> abs_is_lms_gre_length linear by blast
      moreover
      have "list_slice T i (Suc k) = T ! i # (list_slice T (Suc i) k) @ [T ! k]"
        by (metis SL_types.simps(2) \<open>abs_find_next_lms T i = Suc k\<close> \<open>abs_is_lms T (Suc k)\<close>
              \<open>suffix_type T (Suc i) = L_type\<close> assms dual_order.order_iff_strict not_less_eq
              abs_find_next_lms_le_length abs_find_next_lms_lower_bound_1 abs_is_lms_def list_slice_Suc not_less
              list_slice_append list_slice_n_n )
      ultimately have
        "list_less_ns (?bs @ [T ! k, T ! Suc k]) (T ! i # ?bs @ [T ! k, T ! Suc k])"
        using rev_sorted_list_less_ns[of "T ! i" ?bs "T ! k" "T ! Suc k" "[]" "[]"]
        by simp
      moreover
      have "suffix (lms_slice T i) 0 = T ! i # ?bs @ [T ! k, T ! Suc k]"
        by (simp add: \<open>lms_slice T i = T ! i # ?bs @ [T ! k, T ! Suc k]\<close>)
      moreover
      have "suffix (lms_slice T i) (Suc 0) = ?bs @ [T ! k, T ! Suc k]"
        by (simp add: \<open>lms_slice T i = T ! i # list_slice T (Suc i) k @ [T ! k, T ! Suc k]\<close>)
      ultimately show ?thesis
        by (metis \<open>suffix_type T i = L_type\<close> ordlistns.less_asym suffix_type_def)
    qed
    ultimately show ?thesis
      by blast
  qed
  moreover
  have "suffix_type T i = S_type \<Longrightarrow> ?thesis"
  proof -
    assume "suffix_type T i = S_type"
    hence "lms_slice T i = T ! i # lms_slice T (Suc i)"
      using assms lms_slice_cons by blast

    have "abs_find_next_lms T i < length T \<or> abs_find_next_lms T i = length T"
      by (simp add: abs_find_next_lms_le_length nat_less_le)
    moreover
    have "abs_find_next_lms T i < length T \<Longrightarrow> ?thesis"
    proof -
      assume "abs_find_next_lms T i < length T"
      with abs_find_next_lms_first_l_after_s_type[OF _ \<open>suffix_type T i = S_type\<close>]
      obtain j where
        "i < j"
        "j < abs_find_next_lms T i"
        "\<forall>k<j. i \<le> k \<longrightarrow> suffix_type T k = S_type"
        "suffix_type T j = L_type"
        by blast
      hence "sorted (list_slice T i j)"
        by (meson \<open>abs_find_next_lms T i < length T\<close> dual_order.order_iff_strict order.strict_trans
              sorted_letters_s_types)
      have "\<exists>l. j = Suc l"
        using \<open>i < j\<close> less_imp_Suc_add by blast
      then obtain l where
        "j = Suc l"
        by blast

      let ?xs = "list_slice T (Suc i) (Suc l)"
      and ?ys = "list_slice T (Suc ((Suc l))) (Suc (Suc k))"

      have "lms_slice T i = list_slice T i j @ list_slice T j (Suc (Suc k))"
        by (metis \<open>abs_find_next_lms T i = Suc k\<close> \<open>i < j\<close> \<open>j < abs_find_next_lms T i\<close> less_SucI
              less_imp_le_nat list_slice_append lms_slice_def)
      moreover
      have "list_slice T i j = T ! i # ?xs"
        using \<open>i < j\<close> \<open>j = Suc l\<close> assms list_slice_Suc by blast
      moreover
      have "list_slice T j (Suc (Suc k)) = T ! Suc l # ?ys"
        by (metis \<open>abs_find_next_lms T i < length T\<close> \<open>abs_find_next_lms T i = Suc k\<close> \<open>j < abs_find_next_lms T i\<close>
              \<open>j = Suc l\<close> less_SucI list_slice_Suc order.strict_trans)
      ultimately have "lms_slice T i = T ! i # ?xs @ [T ! Suc l] @ ?ys"
        by auto

      have "i = l \<or> i < l"
        using \<open>i < j\<close> less_antisym \<open>j = Suc l\<close> by blast
      moreover
      have "i = l \<Longrightarrow> ?thesis"
      proof -
        assume "i = l"
        hence "?xs = []"
          using list_slice_n_n by blast
        hence "lms_slice T i = T ! i # [T ! Suc l] @ ?ys"
          using \<open>lms_slice T i = T ! i # ?xs @ [T ! Suc l] @ ?ys\<close>
          by simp
        moreover
        have "T ! i < T ! Suc l"
          by (metis SL_types.simps(2) \<open>abs_find_next_lms T i < length T\<close> \<open>i = l\<close> \<open>j < abs_find_next_lms T i\<close>
                \<open>j = Suc l\<close> \<open>suffix_type T i = S_type\<close> \<open>suffix_type T j = L_type\<close> suffix_type_neq
                le_imp_less_or_eq order.strict_trans s_type_letter_le_Suc)
        ultimately show ?thesis
          by (simp add: \<open>suffix_type T i = S_type\<close> suffix_type_cons_less)
      qed
      moreover
      have "i < l \<Longrightarrow> ?thesis"
      proof -
        let ?zs = "list_slice T (Suc i) l"
        assume "i < l"
        hence "?xs = ?zs @ [T ! l]"
          by (metis Suc_leI Suc_n_not_le_n \<open>abs_find_next_lms T i < length T\<close> \<open>j < abs_find_next_lms T i\<close>
                \<open>j = Suc l\<close> lessI less_le_trans linear list_slice_Suc list_slice_append
                list_slice_n_n)
        hence "lms_slice T i = T ! i # ?zs @ [T ! l, T ! Suc l] @ ?ys"
          using \<open>lms_slice T i = T ! i # ?xs @ [T ! Suc l] @ ?ys\<close>
          by simp
        moreover
        have "suffix_type T l = S_type"
          by (simp add: \<open>\<forall>k<j. i \<le> k \<longrightarrow> suffix_type T k = S_type\<close> \<open>i < l\<close> \<open>j = Suc l\<close> less_or_eq_imp_le)
        hence "T ! l < T ! Suc l"
          by (metis SL_types.simps(2) \<open>abs_find_next_lms T i < length T\<close> \<open>j < abs_find_next_lms T i\<close>
                \<open>j = Suc l\<close> \<open>suffix_type T j = L_type\<close> order.strict_iff_order order.strict_trans
                s_type_letter_le_Suc suffix_type_neq)
        ultimately show ?thesis
          using \<open>sorted (list_slice T i j)\<close>
                sorted_list_less_ns[of "T ! i" ?zs "T ! l" "T ! Suc l" ?ys ?ys]
          by (metis \<open>?xs = ?zs @ [T ! l]\<close> \<open>list_slice T i j = T ! i # ?xs\<close> suffix_0 length_Cons
                \<open>suffix_type T i = S_type\<close> list.inject suffix_0 suffix_cons_Suc suffix_type_def
                 zero_less_Suc)
      qed
      ultimately show ?thesis
        by blast
    qed
    moreover
    have "abs_find_next_lms T i = length T \<Longrightarrow> ?thesis"
    proof -
      assume "abs_find_next_lms T i = length T"
      hence P: "\<forall>k'\<ge>i. k' < length T \<longrightarrow> suffix_type T k' = S_type"
        using abs_find_next_lms_eq_length_all_s_types by blast

      have "lms_slice T i = T ! i # list_slice T (Suc i) (length T)"
        by (metis \<open>abs_find_next_lms T i = length T\<close> assms leI less_not_refl list_slice_Suc
              lms_slice_butlast_def lms_slice_eq_butlast)
      with sorted_letters_s_types[OF P]
           sorted_cons_list_less_ns[of "T ! i" "list_slice T (Suc i) (length T)"]
      show ?thesis
        by (metis assms list_slice_Suc suffix_eq_list_slice suffix_type_suffix)
    qed

    ultimately show ?thesis
      by blast
  qed
  ultimately show ?thesis
    by blast
qed

lemma lms_slice_l_less_than_s_type_gen:
  assumes "suffix_type (a # as) 0 = L_type"
  and     "suffix_type (a # bs) 0 = S_type"
shows "list_less_ns (lms_slice (a # as) 0) (lms_slice (a # bs) 0)"
proof -
  from lms_slice_type[of 0 "a # as"] assms(1)
  have "suffix_type (lms_slice (a # as) 0) 0 = L_type"
    by simp
  moreover
  have "\<exists>xs. lms_slice (a # as) 0 = a # xs"
    by (simp add: list_slice_Suc lms_slice_def)
  then obtain xs where
    "lms_slice (a # as) 0 = a # xs"
    by blast
  moreover
  from lms_slice_type[of 0 "a # bs"] assms(2)
  have "suffix_type (lms_slice (a # bs) 0) 0 = S_type"
    by simp
  moreover
  have "\<exists>xs. lms_slice (a # bs) 0 = a # xs"
    by (simp add: assms(2) lms_slice_cons)
  then obtain ys where
    "lms_slice (a # bs) 0 = a # ys"
    by blast
  ultimately show ?thesis
    by (simp add: l_less_than_s_type_general)
qed

lemma lms_slice_l_less_than_s_type:
  assumes "i < length T"
  and     "j < length T"
  and     "T ! i = T ! j"
  and     "suffix_type T i = L_type"
  and     "suffix_type T j = S_type"
shows "list_less_ns (lms_slice T i) (lms_slice T j)"
  by (metis assms abs_find_next_lms_lower_bound_1 l_less_than_s_type_general less_SucI list_slice_Suc
        lms_slice_def lms_slice_type)

lemma lms_prefix_type:
  assumes "i < length T"
  shows "suffix_type (lms_prefix T i) 0 = suffix_type T i"
proof -
  have "abs_is_lms T i \<or> \<not>abs_is_lms T i"
    by blast
  moreover
  have "\<not>abs_is_lms T i \<Longrightarrow> ?thesis"
    by (metis assms closest_lms.simps lms_prefix_def lms_slice_def
          lms_slice_type)
  moreover
  have "abs_is_lms T i \<Longrightarrow> ?thesis"
    by (simp add: abs_is_lms_def lms_lms_prefix suffix_type_last)
  ultimately show ?thesis
    by blast
qed

lemma lms_prefix_l_less_than_s_type_gen:
  assumes "suffix_type (a # as) 0 = L_type"
  and     "suffix_type (a # bs) 0 = S_type"
shows "list_less_ns (lms_prefix (a # as) 0) (lms_prefix (a # bs) 0)"
  by (metis assms closest_lms.simps lms_prefix_def abs_is_lms_def lessI lms_slice_def
        lms_slice_l_less_than_s_type_gen not_gr_zero not_less_iff_gr_or_eq)

lemma lms_prefix_l_less_than_s_type:
  assumes "i < length T"
  and     "j < length T"
  and     "T ! i = T ! j"
  and     "suffix_type T i = L_type"
  and     "suffix_type T j = S_type"
shows "list_less_ns (lms_prefix T i) (lms_prefix T j)"
proof -
  let ?a = "T ! i"

  have "\<exists>as. lms_prefix T i = ?a # as"
    by (simp add: assms(1) lms_prefix_def abs_find_next_lms_lower_bound_1 less_SucI
          list_slice_Suc)
  then obtain as where
    "lms_prefix T i = ?a # as"
    by blast
  hence "suffix_type (?a # as) 0 = L_type"
    using assms(1,4) lms_prefix_type by fastforce

  have "\<exists>bs. lms_prefix T j = ?a # bs"
    by (simp add: assms(2,3) lms_prefix_def abs_find_next_lms_lower_bound_1 less_SucI
          list_slice_Suc)
  then obtain bs where
    "lms_prefix T j = ?a # bs"
    by blast
  hence "suffix_type (?a # bs) 0 = S_type"
    using assms(2) assms(5) lms_prefix_type by fastforce
  with l_less_than_s_type_general[OF _ \<open>suffix_type (?a # as) 0 = _\<close>, of bs]
  have "list_less_ns (?a # as) (?a # bs)" .
  then show ?thesis
    by (simp add: \<open>lms_prefix T i = T ! i # as\<close> \<open>lms_prefix T j = T ! i # bs\<close>)
qed

lemma l_type_lms_prefix_cons:
  assumes "suffix_type T i = L_type"
  and     "i < length T"
shows "lms_prefix T i = T ! i # lms_prefix T (Suc i)"
proof -
  have "suffix_type T (Suc i) = L_type \<or> suffix_type T (Suc i) = S_type"
    using SL_types.exhaust by blast
  moreover
  have "suffix_type T (Suc i) = L_type \<Longrightarrow> ?thesis"
  proof -
    assume "suffix_type T (Suc i) = L_type"
    hence "\<not>abs_is_lms T (Suc i)"
      by (simp add: \<open>suffix_type T i = L_type\<close> suffix_type_same_imp_not_lms)
    with Suc_not_lms_imp_abs_find_next_eq_Suc
    have "abs_find_next_lms T i = abs_find_next_lms T (Suc i)" .
    hence "closest_lms T i = abs_find_next_lms T (Suc i)"
      by (simp add: \<open>suffix_type T i = L_type\<close> abs_is_lms_def)
    hence "lms_prefix T i = list_slice T i (Suc (abs_find_next_lms T (Suc i)))"
      by (simp add: lms_prefix_def)
    moreover
    have "Suc i < Suc (abs_find_next_lms T (Suc i))"
      using \<open>abs_find_next_lms T i = abs_find_next_lms T (Suc i)\<close> assms(2) abs_find_next_lms_lower_bound_1
      by force
    ultimately have
      "lms_prefix T i = T ! i # list_slice T (Suc i) (Suc (abs_find_next_lms T (Suc i)))"
      by (simp add:  assms(2) list_slice_Suc)
    then show ?thesis
      by (simp add: \<open>\<not> abs_is_lms T (Suc i)\<close> lms_prefix_def)
  qed
  moreover
  have "suffix_type T (Suc i) = S_type \<Longrightarrow> ?thesis"
  proof -
    assume "suffix_type T (Suc i) = S_type"
    hence "abs_is_lms T (Suc i)"
      by (simp add: assms(1) abs_is_lms_def)
    hence "abs_find_next_lms T i = Suc i"
      by (simp add: abs_find_next_lms_abs_is_lms)
    hence "lms_prefix T i = [T ! i, T ! Suc i]"
      by (metis Suc_lessD \<open>abs_is_lms T (Suc i)\<close> assms(2) closest_lms.simps lms_prefix_def
            abs_is_lms_consec(1) lessI list_slice_Suc lms_lms_prefix)
    moreover
    have "lms_prefix T (Suc i) = [T ! Suc i]"
      by (simp add: \<open>abs_is_lms T (Suc i)\<close> lms_lms_prefix)
    ultimately show ?thesis
      by simp
  qed
  ultimately show ?thesis
    by blast
qed

section \<open>Ordering LMS-substrings\<close>

text \<open> This section contains theorems about how LMS-substrings and suffixes are ordered. \<close>

lemma lms_slice_eq_suffix_less:
  assumes "lms_slice T i = lms_slice T j"
  shows "list_less_ns (suffix T i) (suffix T j) \<longleftrightarrow>
         list_less_ns (suffix T (abs_find_next_lms T i)) (suffix T (abs_find_next_lms T j))"
proof -
  have "\<lbrakk>abs_find_next_lms T i < length T; abs_find_next_lms T j < length T\<rbrakk> \<Longrightarrow> ?thesis"
  proof -
    assume A: "abs_find_next_lms T i < length T" "abs_find_next_lms T j < length T"
    have "suffix T i = lms_slice_butlast T i @ suffix T (abs_find_next_lms T i)"
      using A(1) suffix_abs_find_next_lms by blast
    moreover
    have "suffix T j = lms_slice_butlast T j @ suffix T (abs_find_next_lms T j)"
      using A(2) suffix_abs_find_next_lms by blast
    moreover
    have "lms_slice_butlast T i = lms_slice_butlast T j"
      by (metis A(1) A(2) assms butlast_snoc lms_slice_to_butlast_app)
    ultimately show ?thesis
      by (simp add: list_less_ns_app_same)
  qed
  moreover
  have "\<lbrakk>abs_find_next_lms T i = length T; abs_find_next_lms T j = length T\<rbrakk> \<Longrightarrow> ?thesis"
    by (metis assms dual_order.refl lms_slice_eq_suffix ordlistns.less_irrefl)
  moreover
  have "\<lbrakk>abs_find_next_lms T i = length T; abs_find_next_lms T j < length T\<rbrakk> \<Longrightarrow> ?thesis"
  proof -
    assume A: "abs_find_next_lms T i = length T" "abs_find_next_lms T j < length T"
    have "suffix T i = lms_slice T i"
      by (simp add: A(1) lms_slice_eq_suffix)
    moreover
    have "suffix T j = lms_slice T j @ suffix T (Suc (abs_find_next_lms T j))"
      by (meson A(2) abs_find_next_lms_lower_bound_2 linorder_not_less
                suffix_to_lms_slice_app_suffix)
    ultimately show ?thesis
      by (metis A(1) append.right_neutral assms cancel_comm_monoid_add_class.diff_cancel
                length_0_conv length_drop list_less_ns_app ordlistns.not_less_iff_gr_or_eq
                ordlistns.top.extremum_strict)
  qed
  moreover
  have "\<lbrakk>abs_find_next_lms T i < length T; abs_find_next_lms T j = length T\<rbrakk> \<Longrightarrow> ?thesis"
  proof -
    assume A: "abs_find_next_lms T i < length T" "abs_find_next_lms T j = length T"
    have "suffix T i = lms_slice T i @ suffix T (Suc (abs_find_next_lms T i))"
      by (meson A(1) abs_find_next_lms_lower_bound_2 linorder_not_less
                suffix_to_lms_slice_app_suffix)
    moreover
    have "suffix T j = lms_slice T j"
      by (simp add: A(2) lms_slice_eq_suffix)
    ultimately show ?thesis
      by (metis A append_Nil2 assms drop_eq_Nil2 abs_find_next_lms_lower_bound_2 linorder_le_less_linear
                list_less_ns_app nless_le ordlistns.top.not_eq_extremum suffix_neq_nil suffixes_neq)
  qed
  ultimately show ?thesis
    by (meson abs_find_next_lms_le_length le_neq_implies_less)
qed

lemma lms_slice_eq_suffix_less_funpow':
  assumes "\<forall>k < n. lms_slice T (((abs_find_next_lms T)^^k) i) =
                   lms_slice T (((abs_find_next_lms T)^^k) j)"
  and     "k < n"
  shows "list_less_ns (suffix T i) (suffix T j) \<longleftrightarrow>
         list_less_ns (suffix T (((abs_find_next_lms T)^^k) i)) (suffix T (((abs_find_next_lms T)^^k) j))"
  using assms
proof (induct n arbitrary: k)
  case 0
  then show ?case
    by blast
next
  case (Suc n)
  note IH = this
  have "k < n \<Longrightarrow> ?case"
    by (simp add: Suc.hyps Suc.prems(1))
  moreover
  have "k = n \<Longrightarrow> ?case"
  proof -
    assume "k = n"

    have "k = 0 \<Longrightarrow> ?thesis"
      by auto
    moreover
    have "\<exists>m. k = Suc m \<Longrightarrow> ?thesis"
    proof -
      assume "\<exists>m. k = Suc m"
      then obtain m where "k = Suc m"
        by blast
      hence "m < n"
        using \<open>k = n\<close> by blast
      with IH(1)[of m]
      have "list_less_ns (suffix T i) (suffix T j) =
            list_less_ns (suffix T ((abs_find_next_lms T ^^ m) i))
                         (suffix T ((abs_find_next_lms T ^^ m) j))"
        using Suc.prems(1) less_Suc_eq_le less_or_eq_imp_le by presburger
      moreover
      have "list_less_ns (suffix T ((abs_find_next_lms T ^^ m) i))
                         (suffix T ((abs_find_next_lms T ^^ m) j)) =
            list_less_ns (suffix T (abs_find_next_lms T ((abs_find_next_lms T ^^ m) i)))
                         (suffix T (abs_find_next_lms T ((abs_find_next_lms T ^^ m) j)))"
        using Suc.prems(1,2) Suc_lessD \<open>k = Suc m\<close> lms_slice_eq_suffix_less by blast
      ultimately show ?thesis
        by (simp add: \<open>k = Suc m\<close>)
    qed
    ultimately show ?thesis
      using not0_implies_Suc by blast
  qed
  ultimately show ?case
    using Suc.prems(2) less_Suc_eq by blast
qed

lemma lms_slice_eq_suffix_less_funpow:
  assumes "\<forall>k < n. lms_slice T (((abs_find_next_lms T)^^k) i) =
                   lms_slice T (((abs_find_next_lms T)^^k) j)"
  shows "list_less_ns (suffix T i) (suffix T j) \<longleftrightarrow>
         list_less_ns (suffix T (((abs_find_next_lms T)^^n) i)) (suffix T (((abs_find_next_lms T)^^n) j))"
proof (cases n)
  case 0
  then show ?thesis
    by auto
next
  case (Suc m)
  then show ?thesis
    by (metis assms abs_find_next_lms_funpow_Suc lessI lms_slice_eq_suffix_less
              lms_slice_eq_suffix_less_funpow')
qed

lemma list_slice_single:
  "i < length xs \<Longrightarrow> list_slice xs i (Suc i) = [xs ! i]"
  by (simp add: list_slice_Suc)

lemma less_lms_slice_imp_suffix:
  assumes "i < length T"
  and     "j < length T"
  and     "list_less_ns (lms_slice T i) (lms_slice T j)"
  shows "list_less_ns (suffix T i) (suffix T j)"
proof -

  let ?c1 = "\<exists>b c as bs cs. lms_slice T i = as @ b # bs \<and>
                          lms_slice T j = as @ c # cs \<and> b < c"
  let ?c2 = "\<exists>c cs. lms_slice T i = lms_slice T j @ c # cs"

  from list_less_ns_exE[OF assms(3)[simplified list_less_ns_alt_def]]
  have "?c1 \<or> ?c2" .
  moreover
  have "?c1 \<Longrightarrow> ?thesis"
    by (metis append.assoc append_Cons assms(1,2) list_less_ns_app_same list_less_ns_cons_diff
              suffix_to_lms_slice_app_suffix)
  moreover
  have "?c2 \<Longrightarrow> ?thesis"
  proof -
    assume "?c2"
    then obtain c cs where
      "lms_slice T i = lms_slice T j @ c # cs"
      by blast
    moreover
    from lms_slice_hd[OF assms(2)]
    obtain xs where
      Sj: "lms_slice T j = T ! j # xs"
      by blast
    ultimately have Si: "lms_slice T i = T ! j # xs @ c # cs"
      by simp

    let ?i = "abs_find_next_lms T i"
    let ?j = "abs_find_next_lms T j"
    have "\<exists>k. ?j = Suc k"
      by (meson Nat.lessE assms(1) dual_order.strict_trans1
                abs_find_next_lms_strict_upper_imp_lower_bound linorder_not_less)
    then obtain k where
      "?j = Suc k"
      by blast
    hence "j \<le> k"
      using assms(2) abs_find_next_lms_lower_bound_1 by force

    have "?j = length T \<Longrightarrow> ?thesis"
      by (metis append_Nil2 assms(1,3) abs_find_next_lms_le_length list_less_ns_app
                lms_slice_eq_suffix ordlistns.dual_order.strict_trans
                suffix_to_lms_slice_app_suffix)
    moreover
    have "?j < length T \<Longrightarrow> ?thesis"
    proof -
      assume "?j < length T"
      with lms_slice_to_butlast_app
      have "lms_slice T j = lms_slice_butlast T j @ [T ! Suc k]"
        using \<open>?j = Suc k\<close> by fastforce
      moreover
      have "\<exists>ys. lms_slice_butlast T j = ys @ [T ! k]"
      proof (cases "j = k")
        case True
        hence "lms_slice_butlast T j = list_slice T k (Suc k)"
          by (metis \<open>?j = Suc k\<close> lms_slice_butlast_def)
        moreover
        have "list_slice T k (Suc k) = [T ! k]"
          using True assms(2) list_slice_single by auto
        ultimately show ?thesis
          by simp
      next
        case False
        hence "j < k"
          by (simp add: \<open>j \<le> k\<close> le_neq_implies_less)
        hence "list_slice T j (Suc k) = list_slice T j k @ [T ! k]"
          by (metis \<open>?j < length T\<close> \<open>?j = Suc k\<close> \<open>j \<le> k\<close> le_SucI le_add2 list_slice_append
                   list_slice_single not_less plus_1_eq_Suc)
        then show ?thesis
          by (simp add: \<open>?j = Suc k\<close> lms_slice_butlast_def)
      qed
      then obtain ys where
        "lms_slice_butlast T j = ys @ [T ! k]"
        by blast
      ultimately have Sj': "lms_slice T j = ys @ [T ! k, T ! Suc k]"
        by simp

      have Si': "lms_slice T i = ys @ T ! k # T ! Suc k # c # cs"
        using Si Sj Sj' by auto

      have "suffix_type T k = L_type"
        by (metis \<open>?j < length T\<close> \<open>?j = Suc k\<close> abs_find_next_lms_less_length_abs_is_lms
                  abs_is_lms_neq nth_gr_imp_l_type)

      have "abs_is_lms T (Suc k)"
        by (metis \<open>?j < length T\<close> \<open>?j = Suc k\<close> abs_find_next_lms_less_length_abs_is_lms)
      hence "T ! k > T ! Suc k"
        using abs_is_lms_neq by blast

      have Si: "suffix T i = ys @ T ! k # T ! Suc k # c # cs @ suffix T (Suc ?i)"
        by (simp add: Si' assms(1) suffix_to_lms_slice_app_suffix)
      moreover
      have "suffix T j = ys @ T ! k # T ! Suc k # suffix T (Suc ?j)"
        by (simp add: \<open>lms_slice T j = ys @ [T ! k, T ! Suc k]\<close> assms(2)
                      suffix_to_lms_slice_app_suffix)
      ultimately have "list_less_ns (suffix T i) (suffix T j) \<longleftrightarrow>
                       list_less_ns (T ! k # T ! Suc k # c # cs @ suffix T (Suc ?i))
                                    (T ! k # T ! Suc k # suffix T (Suc ?j))"
        by (simp add: list_less_ns_app_same)
      moreover
      have "suffix_type (T ! k # T ! Suc k # c # cs @ suffix T (Suc ?i)) (Suc 0) = L_type \<Longrightarrow> ?thesis"
        by (metis Cons_nth_drop_Suc \<open>?j < length T\<close> \<open>?j = Suc k\<close> \<open>abs_is_lms T (Suc k)\<close> calculation
                  abs_is_lms_def l_less_than_s_type_general list_less_ns_cons_same suffix_type_cons_suc
                  suffix_type_suffix)
      moreover
      have "suffix_type (T ! k # T ! Suc k # c # cs @ suffix T (Suc ?i)) (Suc 0) = S_type \<Longrightarrow> ?thesis"
      proof -
        assume "suffix_type (T ! k # T ! Suc k # c # cs @ suffix T (Suc ?i)) (Suc 0) = S_type"
        with Si
        have "suffix_type T (Suc (i + length ys)) = S_type"
          by (metis One_nat_def plus_1_eq_Suc suffix_cons_app suffix_type_suffix_gen)
        moreover
        have "suffix_type (T ! k # T ! Suc k # c # cs @ suffix T (Suc ?i)) 0 = L_type"
          using \<open>T ! Suc k < T ! k\<close> suffix_type_cons_greater by blast
        hence "suffix_type T (i + length ys) = L_type"
          by (simp add: Si suffix_cons_app suffix_type_list_type_eq)
        ultimately have "abs_is_lms T (Suc (i + length ys))"
          using abs_is_lms_def by blast
        moreover
        {
          have "i < ?i"
            by (simp add: assms(1) abs_find_next_lms_lower_bound_1)

          from \<open>lms_slice T i = ys @ T ! k # T ! Suc k # c # cs\<close>
          have "Suc (Suc (length ys)) < length (lms_slice T i)"
            by simp

          have "?i = length T \<Longrightarrow> Suc (i + length ys) < ?i"
            by (simp add: \<open>abs_is_lms T (Suc (i + length ys))\<close> abs_is_lms_imp_less_length)
          moreover
          have "?i < length T \<Longrightarrow> Suc (i + length ys) < ?i"
          proof -
            assume "?i < length T"
            hence "length (lms_slice T i) = Suc ?i - i"
              by (simp add: lms_slice_def Suc_leI)
            hence "Suc (Suc (length ys)) < Suc ?i - i"
              using \<open>Suc (Suc (length ys)) < length (lms_slice T i)\<close> by presburger
            then show ?thesis
              by linarith
          qed
          ultimately have "Suc (i + length ys) < ?i"
            using abs_find_next_lms_le_length le_neq_implies_less by blast
        }
        ultimately show ?thesis
          using no_lms_between_i_and_next[of i "Suc (i + length ys)"] less_add_Suc1 by blast
      qed
      ultimately show ?thesis
        using SL_types.exhaust by blast
    qed
    ultimately show ?thesis
      using abs_find_next_lms_le_length le_neq_implies_less by blast
  qed
  ultimately show ?thesis
    by blast
qed

lemma lms_slice_list_less_ns_suffix:
  assumes "abs_is_lms T i"
  and     "abs_is_lms T j"
  and     "list_less_ns (lms_slice T i) (lms_slice T j)"
shows "list_less_ns (suffix T i) (suffix T j)"
  by (simp add: assms abs_is_lms_imp_less_length less_lms_slice_imp_suffix)

lemma less_suffix_imp_lms_slice:
  assumes "i < length T"
  and     "j < length T"
  and     "lms_slice T i \<noteq> lms_slice T j"
  and     "list_less_ns (suffix T i) (suffix T j)"
shows "list_less_ns (lms_slice T i) (lms_slice T j)"
  by (meson assms less_lms_slice_imp_suffix ordlistns.less_asym ordlistns.neqE)

lemma not_lms_imp_next_eq_lms_prefix:
  "\<not>abs_is_lms T i \<Longrightarrow> lms_slice T i = lms_prefix T i"
  by (simp add: lms_prefix_def lms_slice_def)

lemma lms_slice_last:
  assumes "valid_list T"
  and     "length T = Suc n"
shows "lms_slice T n = [bot]"
  by (metis add_diff_cancel_left' assms butlast_snoc abs_find_next_lms_lower_bound_1 le_Suc_eq
        length_butlast less_Suc_eq list_slice_Suc list_slice_start_gre_length lms_slice_def
        nth_append_length plus_1_eq_Suc valid_list_ex_def)

lemma Min_valid_lms_slice:
  assumes "valid_list T"
  and     "length T = Suc n"
shows "ordlistns.Min {lms_slice T i |i. i < length T} = lms_slice T n"
proof -
  from lms_slice_last[OF assms]
  have "lms_slice T n = [bot]"
    by assumption

  have "\<forall>i < n. (lms_slice T i) ! 0 \<noteq> bot"
    by (metis add_diff_cancel_left' assms abs_find_next_lms_lower_bound_1 less_SucI list_slice_Suc
          lms_slice_def nth_Cons_0 plus_1_eq_Suc valid_list_def)
  hence A: "\<forall>i < n. bot < (lms_slice T i) ! 0"
    using bot.not_eq_extremum by blast

  have B: "\<forall>i < length T. length (lms_slice T i) > 0"
    by (simp add: abs_find_next_lms_lower_bound_1 less_SucI list_slice_Suc lms_slice_def)

  show ?thesis
  proof (intro ordlistns.Min_eqI conjI)
    show "finite {lms_slice T i |i. i < length T}"
      using finite_image_set by blast
  next
    fix ys
    assume "ys \<in> {lms_slice T i |i. i < length T}"
    hence "\<exists>i < length T. ys = lms_slice T i"
      by blast
    then obtain i where
      "i < length T"
      "ys = lms_slice T i"
      by blast

    with \<open>ys = lms_slice T i\<close>
    have R1: "i = n \<Longrightarrow> list_less_eq_ns (lms_slice T n) ys"
      by simp

    from \<open>i < length T\<close> assms(2)
    have R2_1: "i \<noteq> n \<Longrightarrow> i < n"
      by linarith

    from A \<open>lms_slice T n = [bot]\<close> \<open>i < length T\<close> \<open>ys = lms_slice T i\<close>
    have R2_2: "i < n \<Longrightarrow> list_less_eq_ns (lms_slice T n) ys"
      using list_less_eq_ns_def by fastforce

    from R1 R2_2[OF R2_1]
    show "list_less_eq_ns (lms_slice T n) ys"
      by blast
  next
    show "lms_slice T n \<in> {lms_slice T i |i. i < length T}"
      using assms(2) by auto
  qed
qed

lemma unique_valid_lms_slice:
  assumes "valid_list T"
  and     "length T = Suc n"
shows "\<forall>i < n. lms_slice T i \<noteq> lms_slice T n"
proof (intro allI impI)
  fix i
  assume "i < n"
  from lms_slice_last[OF assms]
  have "lms_slice T n = [bot]"
    by assumption

  have "\<forall>i < n. (lms_slice T i) ! 0 \<noteq> bot"
    by (metis add_diff_cancel_left' assms abs_find_next_lms_lower_bound_1 less_SucI list_slice_Suc
          lms_slice_def nth_Cons_0 plus_1_eq_Suc valid_list_def)
  hence "\<forall>i < n. bot < (lms_slice T i) ! 0"
    using bot.not_eq_extremum by blast
  with \<open>lms_slice T n = [bot]\<close> \<open>i < n\<close>
  show "lms_slice T i \<noteq> lms_slice T n"
    by auto
qed

lemma strict_Min_valid_lms_slice:
  assumes "valid_list T"
  and     "length T = Suc n"
shows "\<forall>i < n. list_less_ns (lms_slice T n) (lms_slice T i)"
  by (metis add_diff_cancel_left' assms bot.not_eq_extremum abs_find_next_lms_lower_bound_1 less_Suc_eq
        list_less_ns_cons_diff list_slice_Suc lms_slice_def lms_slice_last plus_1_eq_Suc
        valid_list_def)

lemma ordlistns_lms_slice_imp_suffix_strict_sorted:
  assumes "set xs \<subseteq> {i. abs_is_lms T i}" "ordlistns.strict_sorted (map (lms_slice T) xs)"
  shows "ordlistns.strict_sorted (map (suffix T) xs)"
proof (intro sorted_wrt_mapI)
  fix i j
  assume "i < j" "j < length xs"
  with sorted_wrt_mapD[OF assms(2), of i j]
  have "list_less_ns (lms_slice T (xs ! i)) (lms_slice T (xs ! j))"
    by blast
  moreover
  have "abs_is_lms T (xs ! i)"
    using \<open>i < j\<close> \<open>j < length xs\<close> assms(1) subsetD by fastforce
  hence "xs ! i < length T"
    by (simp add: abs_is_lms_imp_less_length)
  moreover
  have "abs_is_lms T (xs ! j)"
    using \<open>j < length xs\<close> assms(1) nth_mem by auto
  hence "xs ! j < length T"
    by (simp add: abs_is_lms_imp_less_length)
  ultimately show "list_less_ns (suffix T (xs ! i)) (suffix T (xs ! j))"
    using less_lms_slice_imp_suffix by blast
qed

section \<open>Mapping from suffix to lists of LMS-Substrings\<close>

text \<open> This section contains the mapping from LMS-type suffixes to suffixes of the reduced sequence.
       The mapping is constructed in 3 major steps.
       1) From suffix ID to a sequence of LMS-type suffix IDs
       2) From a sequence of LMS-type suffix IDs to a sequence of LMS-substrings
       3) From a LMS-type suffix to a reduced suffix
          using the mappings 1, 2 and @{const ordlistns.elem_rank}
       The mapping is also shown to be monotonic. \<close>

abbreviation "lms_substrs xs \<equiv> lms_slice xs ` {i. abs_is_lms xs i}"
abbreviation "lms_suffixes xs \<equiv> suffix xs ` {i. abs_is_lms xs i}"

abbreviation "nth_lms xs i \<equiv> (abs_find_next_lms xs ^^ Suc i) 0"

abbreviation "lms0 xs \<equiv> abs_find_next_lms xs 0"
abbreviation "lms0_suffix xs \<equiv> suffix xs (lms0 xs)"
abbreviation "lms0_substr xs \<equiv> lms_slice xs (lms0 xs)"

subsection \<open>LMS Sequence\<close>

definition lms_seq :: "'a :: {linorder,order_bot} list \<Rightarrow> nat \<Rightarrow> nat list"
  where
"lms_seq xs i = filter (abs_is_lms xs) [i..<length xs]"

lemma lms_seq_distinct:
  "distinct (lms_seq xs i)"
  by (simp add: lms_seq_def)

lemma lms_seq_sorted:
  "sorted (lms_seq xs i)"
  by (simp add: filter_sorted lms_seq_def)

lemma lms_seq_strict_sorted:
  "strict_sorted (lms_seq xs i)"
  by (simp add: lms_seq_distinct lms_seq_sorted sorted_and_distinct_imp_strict_sorted)

lemma lms_seq_abs_is_lms_hd:
  "abs_is_lms xs i \<Longrightarrow> \<exists>ys. lms_seq xs i = i # ys"
  by (simp add: filter_abs_is_lms_upt_hd abs_is_lms_imp_less_length lms_seq_def)

lemma length_lms_seq:
  assumes "abs_is_lms xs i"
  shows "length (lms_seq xs i) = card {j. abs_is_lms xs j \<and> i \<le> j}"
proof -
  from distinct_length_filter[of "[i..<length xs]" "abs_is_lms xs"]
  have "length (lms_seq xs i) = card ({x. abs_is_lms xs x} \<inter> {i..<length xs})"
    by (simp add: lms_seq_def)
  moreover
  have "{x. abs_is_lms xs x} \<inter> {i..<length xs} = {x. abs_is_lms xs x \<and> i \<le> x}"
    by (safe; clarsimp simp: abs_is_lms_imp_less_length)
  ultimately show ?thesis
    by simp
qed

lemma length_lms_seq_less:
  assumes "abs_is_lms xs i"
  and     "abs_is_lms xs j"
  and     "i < j"
shows "length (lms_seq xs j) < length (lms_seq xs i)"
proof -
  have "{k. abs_is_lms xs k \<and> j \<le> k} \<subseteq> {j. abs_is_lms xs j \<and> i \<le> j}"
    using assms(3) by force
  moreover
  have "i \<in> {j. abs_is_lms xs j \<and> i \<le> j}"
    using assms(1) less_or_eq_imp_le by blast
  moreover
  have "i \<notin> {k. abs_is_lms xs k \<and> j \<le> k}"
    using assms(3) linorder_not_less by blast
  ultimately have "{k. abs_is_lms xs k \<and> j \<le> k} \<subset> {j. abs_is_lms xs j \<and> i \<le> j}"
    by blast
  hence "card {k. abs_is_lms xs k \<and> j \<le> k} < card {j. abs_is_lms xs j \<and> i \<le> j}"
    by (simp add: lms_finite psubset_card_mono)
  then show ?thesis
    by (simp add: assms(1) assms(2) length_lms_seq)
qed

lemma lms_seq_nth_0:
  "lms_seq xs (Suc k) \<noteq> [] \<Longrightarrow> lms_seq xs (Suc k) ! 0 = abs_find_next_lms xs k"
  unfolding lms_seq_def
  apply (simp add: abs_find_next_lms_funpow_Suc abs_find_next_lms_def)
  apply (drule filter_find)
  by (clarsimp split: option.splits)

lemma lms_seq_eq_cons_lms:
  assumes "abs_is_lms xs i" "i < k" "k \<le> abs_find_next_lms xs i"
  shows "lms_seq xs i = i # lms_seq xs k"
proof -
  have "filter (abs_is_lms xs) [Suc i..<k] = []"
    using assms(1) assms(2) assms(3) filter_no_lms1 by blast
  moreover
  have "[i..<length xs] = i # [Suc i..<k] @ [k..<length xs]"
    by (metis Suc_leI assms dual_order.trans abs_find_next_lms_le_length abs_is_lms_imp_less_length
              le_add_diff_inverse upt_add_eq_append upt_conv_Cons)
  hence "lms_seq xs i = i # (filter (abs_is_lms xs) [Suc i..<k]) @ (filter (abs_is_lms xs) [k..<length xs])"
    by (simp add: assms(1) lms_seq_def)
  ultimately show ?thesis
    by (metis append_Nil lms_seq_def)
qed

lemma lms_seq_not_lms:
  assumes "\<not>abs_is_lms xs i" "i < k" "k \<le> abs_find_next_lms xs i"
  shows "lms_seq xs i = lms_seq xs k"
proof -
  have "filter (abs_is_lms xs) [i..<k] = []"
    using assms filter_no_lms2 by blast
  moreover
  have "[i..<length xs] = [i..<k] @ [k..<length xs]"
    by (metis assms(2,3) dual_order.trans abs_find_next_lms_le_length le_add_diff_inverse
              less_or_eq_imp_le upt_add_eq_append)
  ultimately show ?thesis
    by (simp add: lms_seq_def)
qed

lemma lms_seq_eq_cons:
  assumes "lms_seq xs (Suc i) \<noteq> []"
  shows "lms_seq xs (Suc i) = abs_find_next_lms xs i # lms_seq xs (Suc (abs_find_next_lms xs i))"
proof -
  from lms_seq_nth_0[OF assms]
  have "lms_seq xs (Suc i) ! 0 = abs_find_next_lms xs i" .
  moreover
  have "i < abs_find_next_lms xs i"
    by (metis Suc_lessD assms filter.simps(1) abs_find_next_lms_lower_bound_1 lms_seq_def upt_rec)
  hence "Suc i \<le> abs_find_next_lms xs i"
    by simp
  hence "lms_seq xs (Suc i) = lms_seq xs (abs_find_next_lms xs i)"
    by (metis abs_find_next_lms_abs_is_lms abs_find_next_lms_le_Suc lms_seq_not_lms order_le_imp_less_or_eq)
  ultimately show ?thesis
    by (metis Suc_leI assms filter.simps(1) abs_find_next_lms_less_length_abs_is_lms
              abs_find_next_lms_lower_bound_1 lessI lms_seq_def lms_seq_eq_cons_lms upt_rec)
qed

lemma lms_seq_nth_abs_is_lms:
  "i < length (lms_seq xs k) \<Longrightarrow> abs_is_lms xs ((lms_seq xs k) ! i)"
  unfolding lms_seq_def
  using nth_mem by fastforce

lemma lms_seq_0:
  "lms_seq xs 0 = lms_seq xs (Suc 0)"
  by (metis filter_abs_is_lms_upt_0 lms_seq_def)

lemma lms_seq_nth:
  "i < length (lms_seq xs (Suc k)) \<Longrightarrow> lms_seq xs (Suc k) ! i = ((abs_find_next_lms xs)^^(Suc i)) k"
proof (induct i arbitrary: k)
  case 0
  then show ?case
    by (simp add: lms_seq_nth_0)
next
  case (Suc i)
  note IH = this
  let ?j = "abs_find_next_lms xs k"
  have "lms_seq xs (Suc k) = ?j # lms_seq xs (Suc ?j)"
    using Suc.prems lms_seq_eq_cons by force
  with IH(1)[of "?j"]
  have "lms_seq xs (Suc ?j) ! i = (abs_find_next_lms xs ^^ Suc i) ?j"
    using Suc.prems by fastforce
  then show ?case
    by (simp add: \<open>lms_seq xs (Suc k) = ?j # lms_seq xs (Suc ?j)\<close> funpow_swap1)
qed

lemma inj_on_lms_seq:
  "inj_on (lms_seq xs) {i. abs_is_lms xs i}"
  by (metis (mono_tags, lifting) inj_onI list.inject lms_seq_abs_is_lms_hd mem_Collect_eq)

lemma list_app_imp_suffix:
  "xs = ys @ zs \<Longrightarrow> suffix xs (length ys) = zs"
  by auto

abbreviation "nth_lms_seq xs i \<equiv> lms_seq xs (nth_lms xs i)"

abbreviation "lms0_seq xs \<equiv> lms_seq xs (lms0 xs)"

lemma lms_seq_0_zeroth_lms:
  "lms_seq xs 0 = lms0_seq xs"
  by (metis gr_zeroI abs_is_lms_0 le_refl lms_seq_not_lms)

lemma lms_seq_set:
  "set (lms_seq xs i) = {k. abs_is_lms xs k \<and> i \<le> k}"
  by (intro equalityI subsetI; clarsimp simp add: abs_is_lms_def suffix_type_s_bound lms_seq_def)

lemma lms_seq_last_eq_length:
  "length (lms_seq xs i) = Suc n \<Longrightarrow>
   abs_find_next_lms xs ((lms_seq xs i) ! n) = length xs"
proof -
  let ?k = "(lms_seq xs i) ! n"
  assume "length (lms_seq xs i) = Suc n"
  hence "i \<le> ?k"
    by (metis (no_types, lifting) lessI lms_seq_set mem_Collect_eq nth_mem)
  have "\<forall>j < length xs. ?k < j \<longrightarrow> \<not>abs_is_lms xs j"
  proof safe
    fix j
    assume "j < length xs" "?k < j" "abs_is_lms xs j"
    hence "j \<in> set (lms_seq xs i)"
      using \<open>i \<le> lms_seq xs i ! n\<close> lms_seq_set by fastforce
    hence "\<exists>j'< length (lms_seq xs i). (lms_seq xs i) ! j' = j"
      by (simp add: in_set_conv_nth)
    then obtain j' where
      "j' < length (lms_seq xs i)"
      "(lms_seq xs i) ! j' = j"
      by blast
    with strict_sorted_nth_less_mono[OF lms_seq_strict_sorted[of xs i], of n j']
    have "n < j'"
      using \<open>length (lms_seq xs i) = Suc n\<close> \<open>lms_seq xs i ! n < j\<close> by fastforce
    then show False
      using \<open>j' < length (lms_seq xs i)\<close> \<open>length (lms_seq xs i) = Suc n\<close> by linarith
  qed
  then show ?thesis
    by (meson abs_find_next_lms_le_length abs_find_next_lms_less_length_abs_is_lms
              abs_find_next_lms_strict_upper_imp_lower_bound order.strict_iff_order)
qed

lemma lms0_seq_has_all_lms:
  "set (lms0_seq xs) = {i. abs_is_lms xs i}"
  by (metis (mono_tags, lifting) Collect_cong linorder_le_less_linear lms_seq_set mem_Collect_eq
                                 no_lms_between_i_and_next set_lms_gr_0)

lemma lms0_seq_length:
  "length (lms0_seq xs) = card {i. abs_is_lms xs i}"
  by (metis distinct_card lms0_seq_has_all_lms lms_seq_distinct)

lemma lms0_seq_nth:
  "i < card {i. abs_is_lms xs i} \<Longrightarrow> lms0_seq xs ! i = nth_lms xs i"
  by (metis lms0_seq_length lms_seq_0 lms_seq_0_zeroth_lms lms_seq_nth)

lemma lms_seq_Suc1:
  assumes "abs_is_lms xs i"
  shows "lms_seq xs i = i # lms_seq xs (Suc i)"
  by (simp add: assms filter_abs_is_lms_upt_hd abs_is_lms_imp_less_length lms_seq_def)

lemma lms_seq_Suc2:
  assumes "\<not>abs_is_lms xs i"
  shows "lms_seq xs i = lms_seq xs (Suc i)"
  by (metis (no_types, lifting) assms dual_order.strict_trans2 filter.simps(2) lessI
                                less_or_eq_imp_le lms_seq_def upt_rec)

lemma lms_seq_suf:
  "i \<le> j \<Longrightarrow> \<exists>ys. lms_seq xs i = ys @ lms_seq xs j"
proof (induct "j - i" arbitrary: i j)
  case 0
  then show ?case
    by force
next
  case (Suc x)
  note IH = this
  hence "\<exists>j'. j = Suc j'"
    by (metis Suc_le_D diff_le_self)
  then obtain j' where
    A: "j = Suc j'"
    by blast
  with IH(1)[of j' i] IH(2,3)
  have B: "\<exists>ys. lms_seq xs i = ys @ lms_seq xs j'"
    by (metis Suc_diff_le Suc_eq_plus1 add.commute add_left_imp_eq antisym_conv2 le_Suc_eq
              zero_less_Suc zero_less_diff)
  show ?case
  proof (cases "abs_is_lms xs j'")
    assume "abs_is_lms xs j'"
    with A B lms_seq_Suc1[of xs j']
    show ?thesis
      by auto
  next
    assume "\<not>abs_is_lms xs j'"
    with A B lms_seq_Suc2[of xs j']
    show ?thesis
      by simp
  qed
qed

lemma lms_lms_seq_is_suffix:
  assumes "abs_is_lms xs i"
  shows "\<exists>k < length (lms0_seq xs).
          suffix (lms0_seq xs) k = lms_seq xs i"
proof -
  have "lms0 xs \<le> i"
    by (metis assms bot_nat_0.not_eq_extremum abs_is_lms_0 linorder_not_less no_lms_between_i_and_next)
  with lms_seq_suf[of "lms0 xs" i xs]
  show ?thesis
    by (metis assms length_Cons length_append length_greater_0_conv less_add_same_cancel1
              less_numeral_extra(1) list.size(3) list_app_imp_suffix lms_seq_Suc1 plus_1_eq_Suc
              zero_eq_add_iff_both_eq_0)
qed

lemma nth_lms:
  "i < card {i. abs_is_lms xs i} \<Longrightarrow>
   abs_is_lms xs (nth_lms xs i)"
proof -
  assume "i < card {i. abs_is_lms xs i}"
  hence "i < length (lms0_seq xs)"
    by (metis distinct_card lms0_seq_has_all_lms lms_seq_distinct)
  moreover
  have "\<exists>k. lms0 xs = Suc k"
    by (metis calculation filter.simps(1) abs_find_next_lms_eq_Suc less_nat_zero_code list.size(3)
              lms_seq_def upt.simps(1))
  then obtain k where "lms0 xs = Suc k" by blast
  ultimately show ?thesis
    by (metis lms_seq_0 lms_seq_0_zeroth_lms lms_seq_nth lms_seq_nth_abs_is_lms)
qed

lemma card_abs_find_next_lms_funpow:
  "i < card {k. abs_is_lms xs k} \<Longrightarrow>
   card {k. abs_is_lms xs k \<and> k < nth_lms xs i} = i"
proof (induct i)
  case 0
  then show ?case
    by (metis (mono_tags, lifting) Collect_empty_eq card_eq_0_iff comp_apply funpow.simps(2)
                                   funpow_0 gr_zeroI abs_is_lms_0 no_lms_between_i_and_next)
next
  case (Suc i)
  note IH = this
  let ?i = "nth_lms xs i"
  let ?j = "nth_lms xs (Suc i)"
  let ?A = "{k. abs_is_lms xs k \<and> k < ?i}"
  let ?B = "{k. abs_is_lms xs k \<and> k < ?j}"

  from IH
  have A: "card ?A = i"
    using Suc_lessD by blast
  moreover
  have P: "?i < ?j"
    by (metis Suc.prems Suc_lessD abs_find_next_lms_funpow_Suc abs_find_next_lms_lower_bound_1
              abs_is_lms_imp_less_length nth_lms)
  with no_lms_between_i_and_next_funpow
  have B: "\<forall>j. ?i < j \<and> j < ?j \<longrightarrow> j \<notin> ?B"
    by blast

  have C: "?i \<in> ?B"
    using P Suc.prems Suc_lessD nth_lms by fastforce

  have D: "?A \<subseteq> ?B"
    using P by force

  have "?B = insert ?i ?A"
    using B nat_neq_iff C D
    by (intro equalityI subsetI insert_iff[THEN iffD2]; auto)
  moreover
  have "?i \<notin> ?A"
    by blast
  hence "card (insert ?i ?A) = Suc (card ?A)"
    by simp
  ultimately show ?case
    by simp
qed

lemma lms_seq_nth_suffix:
  "i < card {i. abs_is_lms xs i} \<Longrightarrow>
   suffix (lms0_seq xs) i = nth_lms_seq xs i"
proof -
  let ?i = "lms0 xs"
  let ?j = "nth_lms xs i"
  assume A: "i < card {i. abs_is_lms xs i}"
  from nth_lms[OF A]
  have "abs_is_lms xs ?j" .
  moreover
  have "?i \<le> ?j"
    by (metis bot_nat_0.not_eq_extremum calculation abs_is_lms_0 linorder_not_less
              no_lms_between_i_and_next)
  hence "[?i..<length xs] = [?i..<?j] @ [?j..<length xs]"
    by (metis abs_find_next_lms_funpow_Suc abs_find_next_lms_le_length le_add_diff_inverse
              upt_add_eq_append)
  moreover
  have "length (filter (abs_is_lms xs) [?i..<?j]) = card {k. abs_is_lms xs k \<and> k < ?j}"
  proof -
    from filter_no_lms2[of xs 0 ?i]
    have "filter (abs_is_lms xs) [0..<?i] = []"
      using abs_is_lms_0 by fastforce
    moreover
    have "[0..<?j] = [0..<?i] @ [?i..<?j]"
      by (metis \<open>?i \<le> ?j\<close> bot_nat_0.not_eq_extremum le_add_diff_inverse less_or_eq_imp_le
                upt_add_eq_append)
    ultimately have "filter (abs_is_lms xs) [0..<?j] = filter (abs_is_lms xs) [?i..<?j]"
      by fastforce
    moreover
    have "length (filter (abs_is_lms xs) [0..<?j]) = card {k. abs_is_lms xs k \<and> k < ?j}"
    proof -
      from length_filter_conv_card[of "abs_is_lms xs" "[0..<?j]", simplified length_upt]
      have "length (filter (abs_is_lms xs) [0..<?j]) = card {k. k < ?j \<and> abs_is_lms xs ([0..<?j] ! k)}"
        by simp
      moreover
      have "{k. k < ?j \<and> abs_is_lms xs ([0..<?j] ! k)} = {k. abs_is_lms xs k \<and> k < ?j}"
        by force
      ultimately show ?thesis
        by simp
    qed
    ultimately show ?thesis
      by presburger
  qed
  ultimately show ?thesis
    by (metis (no_types, lifting) A Collect_cong card_abs_find_next_lms_funpow filter_append
                                  list_app_imp_suffix lms_seq_def)
qed

subsection \<open>LMS-Substring Sequence\<close>

definition lms_substr_seq :: "'a :: {linorder,order_bot} list \<Rightarrow> nat \<Rightarrow> 'a list list"
  where
"lms_substr_seq xs i = map (lms_slice xs) (lms_seq xs i)"

lemma lms_substr_seq_length:
  "length (lms_substr_seq xs i) = length (lms_seq xs i)"
  by (simp add: lms_substr_seq_def)

lemma inj_on_map_lms_slice_lms_seq:
  "inj_on (map (lms_slice xs)) (lms_seq xs ` {i. abs_is_lms xs i})"
proof (intro inj_onI)
  fix x y
  assume "x \<in> lms_seq xs ` {i. abs_is_lms xs i}"
         "y \<in> lms_seq xs ` {i. abs_is_lms xs i}"
         "map (lms_slice xs) x = map (lms_slice xs) y"
  then obtain i j where
    "x = lms_seq xs i" "y = lms_seq xs j"
    "map (lms_slice xs) (lms_seq xs i) = map (lms_slice xs) (lms_seq xs j)"
    "abs_is_lms xs i" "abs_is_lms xs j"
    by clarsimp+
  then have "lms_seq xs i = lms_seq xs j"
    by (metis length_lms_seq_less length_map nat_neq_iff)
  then show "x = y"
    by (simp add: \<open>x = lms_seq xs i\<close> \<open>y = lms_seq xs j\<close>)
qed

lemma inj_on_lms_substr_seq:
  "inj_on (lms_substr_seq xs) {i. abs_is_lms xs i}"
  unfolding lms_substr_seq_def
  using comp_inj_on[OF inj_on_lms_seq inj_on_map_lms_slice_lms_seq, simplified o_def]
  by blast

lemma lms_substr_seq_nth:
  "i < length (lms_substr_seq xs (Suc k)) \<Longrightarrow>
   lms_substr_seq xs (Suc k) ! i = lms_slice xs ((abs_find_next_lms xs ^^ Suc i) k)"
  by (simp add: lms_seq_nth lms_substr_seq_def)

lemma lms_substr_seq_nth_abs_is_lms:
  "i < length (lms_substr_seq xs k) \<Longrightarrow>
   (lms_substr_seq xs k) ! i \<in> lms_substrs xs"
  by (simp add: lms_seq_nth_abs_is_lms lms_substr_seq_def)

definition suffix_to_id
  where
"suffix_to_id xs ys = length xs - length ys"

lemma suffix_lengths_neq:
  "\<lbrakk>i < j; j < length xs\<rbrakk> \<Longrightarrow> length (suffix xs i) > length (suffix xs j)"
  by simp

lemma inj_on_suffix_to_id:
  "inj_on (suffix_to_id xs) (suffix xs ` {i. abs_is_lms xs i})"
  by (intro inj_onI; clarsimp simp: suffix_to_id_def abs_is_lms_imp_less_length less_or_eq_imp_le)

lemma suffix_id_suffix:
  "i < length xs \<Longrightarrow> suffix_to_id xs (suffix xs i) = i"
  by (simp add: suffix_to_id_def)

lemma suffix_to_id_image:
  "suffix_to_id xs ` suffix xs ` {i. abs_is_lms xs i} = {i. abs_is_lms xs i}"
proof safe
  fix i
  assume "abs_is_lms xs i"
  then show "abs_is_lms xs (suffix_to_id xs (suffix xs i))"
    by (simp add: abs_is_lms_imp_less_length suffix_id_suffix)
next
  fix i
  assume "abs_is_lms xs i"
  then show "i \<in> suffix_to_id xs ` lms_suffixes xs"
    by (simp add: image_iff abs_is_lms_imp_less_length suffix_id_suffix)
qed

abbreviation "lms_substr_seq_id xs \<equiv> (lms_substr_seq xs) \<circ> (suffix_to_id xs)"

lemma lms_subtrs_seq_id_suffix:
  "lms_substr_seq_id xs (suffix xs i) = lms_substr_seq xs i"
  apply simp
  apply (cases "i < length xs")
   apply (simp add: suffix_id_suffix)
  by (simp add: lms_seq_def lms_substr_seq_def suffix_to_id_def)

lemma lms_substr_seq_id_nth_abs_is_lms:
  "i < length (lms_substr_seq_id xs (suffix xs k)) \<Longrightarrow>
   (lms_substr_seq_id xs (suffix xs k)) ! i \<in> lms_substrs xs"
  by (simp add: lms_seq_nth_abs_is_lms lms_substr_seq_def)

lemma inj_on_lms_substr_seq_o_suffix_to_id:
  "inj_on (lms_substr_seq_id xs) (lms_suffixes xs)"
proof -
  have "lms_substr_seq xs = map (lms_slice xs) \<circ> lms_seq xs"
    using lms_substr_seq_def by fastforce
  with comp_inj_on[OF inj_on_lms_seq inj_on_map_lms_slice_lms_seq, of xs]
  have "inj_on (lms_substr_seq xs) {i. abs_is_lms xs i}"
    by simp
  with comp_inj_on[OF inj_on_suffix_to_id[of xs], simplified suffix_to_id_image[of xs]]
  show ?thesis
    by blast
qed

lemma list_less_ns_lms_substr_seq_suffix:
  assumes "abs_is_lms xs i"
  and     "abs_is_lms xs j"
  and     "nslexordp list_less_ns (lms_substr_seq xs i) (lms_substr_seq xs j)"
shows "list_less_ns (suffix xs i) (suffix xs j)"
proof -
  have "\<exists>i'. i = Suc i'"
    using assms(1) abs_is_lms_def by blast
  then obtain i' where
    "i = Suc i'"
    by blast
  hence "abs_find_next_lms xs i' = i"
    using assms(1) abs_find_next_lms_abs_is_lms by blast

  have A: "\<And>k. k < length (lms_substr_seq xs i) \<Longrightarrow>
               lms_substr_seq xs i ! k = lms_slice xs ((abs_find_next_lms xs ^^ k) i)"
    by (simp add: \<open>abs_find_next_lms xs i' = i\<close> \<open>i = Suc i'\<close> funpow_swap1 lms_substr_seq_nth)

  have "\<exists>j'. j = Suc j'"
    using assms(2) abs_is_lms_def by blast
  then obtain j' where
    "j = Suc j'"
    by blast
  hence "abs_find_next_lms xs j' = j"
    using assms(2) abs_find_next_lms_abs_is_lms by blast

  have B: "\<And>k. k < length (lms_substr_seq xs j) \<Longrightarrow>
               lms_substr_seq xs j ! k = lms_slice xs ((abs_find_next_lms xs ^^ k) j)"
    by (simp add: \<open>abs_find_next_lms xs j' = j\<close> \<open>j = Suc j'\<close> funpow_swap1 lms_substr_seq_nth)

  let ?c1 = "\<exists>b c as bs cs.
              lms_substr_seq xs i = as @ b # bs \<and> lms_substr_seq xs j = as @ c # cs \<and>
              list_less_ns b c"
  let ?c2 = "\<exists>c cs. lms_substr_seq xs i = lms_substr_seq xs j @ c # cs"
  from nslexordpE[OF assms(3)]
  have "?c1 \<or> ?c2" .
  moreover
  have "?c1 \<Longrightarrow> ?thesis"
  proof -
    assume ?c1
    then obtain b c as bs cs where
      "lms_substr_seq xs i = as @ b # bs"
      "lms_substr_seq xs j = as @ c # cs"
      "list_less_ns b c"
      by blast

    let ?b = "lms_slice xs ((abs_find_next_lms xs ^^ (length as)) i)"
    from lms_substr_seq_nth[of "length as" xs i'] \<open>i = Suc i'\<close>
         \<open>lms_substr_seq xs i = as @ b # bs\<close>
    have "b = lms_slice xs ((abs_find_next_lms xs ^^ Suc (length as)) i')"
      by simp
    with \<open>abs_find_next_lms xs i' = i\<close>
    have "b = ?b"
      by (simp add: funpow_swap1)

    let ?c = "lms_slice xs ((abs_find_next_lms xs ^^ (length as)) j)"
    from lms_substr_seq_nth[of "length as" xs j'] \<open>j = Suc j'\<close>
           \<open>lms_substr_seq xs j = as @ c # cs\<close>
    have "c = lms_slice xs ((abs_find_next_lms xs ^^ Suc (length as)) j')"
      by simp
    with \<open>abs_find_next_lms xs j' = j\<close>
    have "c = lms_slice xs ((abs_find_next_lms xs ^^ (length as)) j)"
      by (simp add: funpow_swap1)

    have P: "\<forall>k<length as. lms_slice xs ((abs_find_next_lms xs ^^ k) i) =
                           lms_slice xs ((abs_find_next_lms xs ^^ k) j)"
    proof (safe)
      fix k
      assume "k < length as"
      with \<open>lms_substr_seq xs i = as @ b # bs\<close> A[of k]
      have "as ! k = lms_slice xs ((abs_find_next_lms xs ^^ k) i)"
        by (simp add: nth_append)
      moreover
      from \<open>lms_substr_seq xs j = as @ c # cs\<close> \<open>k < length as\<close> B[of k]
      have "as ! k = lms_slice xs ((abs_find_next_lms xs ^^ k) j)"
        by (simp add: nth_append)
      ultimately show
        "lms_slice xs ((abs_find_next_lms xs ^^ k) i) =
         lms_slice xs ((abs_find_next_lms xs ^^ k) j)"
        by simp
    qed

    have Q: "list_less_ns (suffix xs ((abs_find_next_lms xs ^^ (length as)) i))
                          (suffix xs ((abs_find_next_lms xs ^^ (length as)) j))"
      by (metis \<open>b = ?b\<close> \<open>c = ?c\<close> \<open>list_less_ns b c\<close> drop_eq_Nil abs_find_next_lms_lower_bound_2
                less_lms_slice_imp_suffix list_less_ns_nil lms_slice_eq_suffix
                not_le_imp_less ordlistns.less_asym)

    show ?thesis
    proof (cases "length as")
      case 0
      then show ?thesis
        using Q by force
    next
      case (Suc n)
      assume "length as = Suc n"
      moreover
      from lms_slice_eq_suffix_less_funpow[OF P]
      have "list_less_ns (suffix xs i) (suffix xs j) =
            list_less_ns (suffix xs ((abs_find_next_lms xs ^^ (length as)) i))
                         (suffix xs ((abs_find_next_lms xs ^^ (length as)) j))"
        using lessI by presburger
      ultimately show ?thesis
        using Q by blast
    qed
  qed
  moreover
  have "?c2 \<Longrightarrow> ?thesis"
  proof -
    assume ?c2
    then obtain c cs where
      "lms_substr_seq xs i = lms_substr_seq xs j @ c # cs"
      by blast

    have "lms_substr_seq xs j \<noteq> []"
      by (metis assms(2) list.distinct(1) list.map_disc_iff lms_seq_abs_is_lms_hd lms_substr_seq_def)
    hence "\<exists>n. length (lms_substr_seq xs j) = Suc n"
      using not0_implies_Suc by auto
    then obtain n where
      "length (lms_substr_seq xs j) = Suc n"
      by blast

    have P: "\<forall>k < Suc n. lms_slice xs ((abs_find_next_lms xs ^^ k) i) =
                         lms_slice xs ((abs_find_next_lms xs ^^ k) j)"
    proof safe
      fix k
      assume "k < Suc n"
      hence "lms_substr_seq xs j ! k  = lms_slice xs ((abs_find_next_lms xs ^^ k) j)"
        by (simp add: B \<open>length (lms_substr_seq xs j) = Suc n\<close>)
      moreover
      from \<open>lms_substr_seq xs i = lms_substr_seq xs j @ c # cs\<close> \<open>k < Suc n\<close>
      have "lms_substr_seq xs i ! k = lms_slice xs ((abs_find_next_lms xs ^^ k) j)"
        by (simp add: B \<open>length (lms_substr_seq xs j) = Suc n\<close> nth_append)
      moreover
      have "lms_substr_seq xs i ! k = lms_slice xs ((abs_find_next_lms xs ^^ k) i)"
        using A \<open>k < Suc n\<close> \<open>length (lms_substr_seq xs j) = Suc n\<close>
              \<open>lms_substr_seq xs i = lms_substr_seq xs j @ c # cs\<close> by auto
      ultimately show
        "lms_slice xs ((abs_find_next_lms xs ^^ k) i) =
         lms_slice xs ((abs_find_next_lms xs ^^ k) j)"
        by simp
    qed

    have "list_less_ns (suffix xs i) (suffix xs j) =
           list_less_ns (suffix xs ((abs_find_next_lms xs ^^ Suc n) i))
                        (suffix xs ((abs_find_next_lms xs ^^ Suc n) j))"
      using lms_slice_eq_suffix_less_funpow[OF P]
      by blast
    moreover
    from lms_seq_last_eq_length[of xs j n]
    have "(abs_find_next_lms xs ^^ Suc n) j = length xs"
      by (metis \<open>abs_find_next_lms xs j' = j\<close> \<open>j = Suc j'\<close> \<open>length (lms_substr_seq xs j) = Suc n\<close>
                funpow_swap1 length_map lessI lms_seq_nth lms_substr_seq_def)
    hence "suffix xs ((abs_find_next_lms xs ^^ Suc n) j) = []"
      by force
    ultimately show ?thesis
      by (metis P \<open>lms_substr_seq xs i = lms_substr_seq xs j @ c # cs\<close> append_self_conv assms(1,2)
                abs_is_lms_imp_less_length list.distinct(1) list_less_ns_nil suffix_id_suffix
                lms_slice_eq_suffix_less_funpow ordlistns.not_less_iff_gr_or_eq)
  qed
  ultimately show ?thesis
    by blast
qed

lemma monotone_on_lms_substr_seq_id:
  "monotone_on (lms_suffixes xs) list_less_ns (nslexordp list_less_ns) (lms_substr_seq_id xs)"
  (is "monotone_on ?A ?orda ?ordb ?f")
proof -
  let ?B = "?f ` ?A"

  from inj_on_imp_bij_betw[OF inj_on_lms_substr_seq_o_suffix_to_id]
  have A: "bij_betw ?f ?A ?B" .
  with bij_betw_inv_alt
  have "\<exists>g. bij_betw g ?B ?A \<and> inverses_on ?f g ?A ?B"
    by blast
  then obtain g where B:
    "bij_betw g ?B ?A"
    "inverses_on ?f g ?A ?B"
    by blast

  have C: "monotone_on ?B ?ordb ?orda g"
  proof (intro monotone_onI)
    fix x y
    assume "x \<in> ?B" "y \<in> ?B" "nslexordp list_less_ns x y"
    moreover
    have "\<exists>i. abs_is_lms xs i \<and> g x = suffix xs i"
      using \<open>x \<in> ?B\<close> bij_betw_apply B(1) by fastforce
    then obtain i where
      "abs_is_lms xs i" "g x = suffix xs i"
      by blast
    moreover
    have "\<exists>j. abs_is_lms xs j \<and> g y = suffix xs j"
      using \<open>y \<in> ?B\<close> bij_betw_apply B(1) by fastforce
    then obtain j where
      "abs_is_lms xs j" "g y = suffix xs j"
      by blast
    ultimately show "list_less_ns (g x) (g y)"
      using list_less_ns_lms_substr_seq_suffix[of xs i j]
      by (metis (mono_tags, lifting) B(2) comp_def inverses_onD2 abs_is_lms_imp_less_length
                                     suffix_id_suffix)
  qed

  from nslexordp_asymp[of list_less_ns]
  have "asymp_on ?B ?ordb"
    using asympD by fastforce

  from totalp_on_subset[OF nslexordp_totalp[of list_less_ns]]
  have "totalp_on ?B ?ordb"
    using ordlistns.totalp_on_less by blast

  note D = \<open>asymp_on ?B ?ordb\<close> \<open>totalp_on ?B ?ordb\<close>

  from monotone_on_bij_betw_inv[OF C D _ _ B(1) A inverses_on_sym[THEN iffD1, OF B(2)],
                                simplified]
  show ?thesis .
qed

lemma list_less_ns_suffix_lms_substr_seq:
  assumes "abs_is_lms xs i"
  and     "abs_is_lms xs j"
  and     "list_less_ns (suffix xs i) (suffix xs j)"
shows "nslexordp list_less_ns (lms_substr_seq xs i) (lms_substr_seq xs j)"
  using monotone_onD[OF monotone_on_lms_substr_seq_id _ _ assms(3)]
        assms(1,2) abs_is_lms_imp_less_length suffix_id_suffix by fastforce

lemma lms_substr_seq_suf:
  "i \<le> j \<Longrightarrow> \<exists>ys. lms_substr_seq xs i = ys @ lms_substr_seq xs j"
  unfolding lms_substr_seq_def
  by (frule lms_seq_suf[of _ _ xs]; clarsimp)

lemma lms_lms_substr_seq_is_suffix:
  assumes "abs_is_lms xs i"
  shows "\<exists>k < length (lms_substr_seq xs (abs_find_next_lms xs 0)).
          suffix (lms_substr_seq xs (abs_find_next_lms xs 0)) k = lms_substr_seq xs i"
  unfolding lms_substr_seq_def
  by (metis assms length_map lms_lms_seq_is_suffix[of xs i] suffix_map)

lemma lms_substr_seq_nth_suffix:
  "i < card {i. abs_is_lms xs i} \<Longrightarrow>
   suffix (lms_substr_seq xs (abs_find_next_lms xs 0)) i =
   lms_substr_seq xs ((abs_find_next_lms xs ^^ Suc i) 0)"
  by (simp add: lms_seq_nth_suffix lms_substr_seq_def suffix_map)

subsection \<open>LMS Map\<close>

lemma finite_lms_substrs:
  "finite (lms_substrs xs)"
  by (simp add: lms_finite)

definition lms_map :: "('a :: {linorder, order_bot}) list \<Rightarrow> 'a list \<Rightarrow> nat list"
  where
"lms_map xs \<equiv> (map (ordlistns.elem_rank (lms_substrs xs))) \<circ> (lms_substr_seq_id xs)"

lemma lms_substr_seq_o_suffix_to_id_range:
  "(lms_substr_seq xs \<circ> suffix_to_id xs) ` lms_suffixes xs \<subseteq> {ys. set ys \<subseteq> lms_substrs xs}"
  unfolding lms_substr_seq_def suffix_to_id_def
  by (safe; clarsimp simp: lms_seq_set)

lemma lms_map_o_def:
  "lms_map xs ys = map (ordlistns.elem_rank (lms_substrs xs)) (lms_substr_seq_id xs ys)"
  by (simp add: lms_map_def)

lemma inj_on_lms_map:
  "inj_on (lms_map xs) (lms_suffixes xs)"
proof -
  note A = comp_inj_on[OF inj_on_lms_substr_seq_o_suffix_to_id]
  note B = inj_on_subset[OF bij_betw_imp_inj_on[OF bij_betw_map[OF ordlistns.bij_betw_elem_rank_upt]]]
  from A[OF B, OF finite_lms_substrs lms_substr_seq_o_suffix_to_id_range, of xs]
  show ?thesis
    by (simp add: lms_map_def)
qed

lemma lms_map_length:
  "length (lms_map xs ys) = length (lms_substr_seq xs (suffix_to_id xs ys))"
  by (simp add: lms_map_def)

lemma lms_map_nth_suffix:
  "i < card {i. abs_is_lms xs i} \<Longrightarrow>
   suffix (lms_map xs (suffix xs (abs_find_next_lms xs 0))) i =
   lms_map xs (suffix xs ((abs_find_next_lms xs ^^ Suc i) 0))"
  by (simp add: abs_find_next_lms_le_length lms_map_def lms_seq_nth_suffix lms_substr_seq_def suffix_map
                suffix_to_id_def)

lemma lms_lms_map_is_suffix:
  assumes "abs_is_lms xs i"
  shows "\<exists>k < length (lms_map xs (suffix xs (abs_find_next_lms xs 0))).
          suffix (lms_map xs (suffix xs (abs_find_next_lms xs 0))) k = lms_map xs (suffix xs i)"

proof -
  have "suffix_to_id xs (suffix xs i) = i"
    by (simp add: assms abs_is_lms_imp_less_length suffix_id_suffix)
  moreover
  have "suffix_to_id xs (suffix xs (abs_find_next_lms xs 0)) = abs_find_next_lms xs 0"
    by (simp add: abs_find_next_lms_le_length suffix_to_id_def)
  moreover
  from lms_lms_substr_seq_is_suffix[OF assms]
  obtain k where
    "k < length (lms_substr_seq xs (abs_find_next_lms xs 0))"
    "suffix (lms_substr_seq xs (abs_find_next_lms xs 0)) k = lms_substr_seq xs i"
    by blast
  moreover
  have "k < length (lms_map xs (suffix xs (abs_find_next_lms xs 0)))"
    by (simp add: calculation(2) calculation(3) lms_map_length)
  moreover
  have "suffix (lms_map xs (suffix xs (abs_find_next_lms xs 0))) k = lms_map xs (suffix xs i)"
    by (simp add: lms_map_def calculation suffix_map)
  ultimately show ?thesis
    by blast
qed

lemma length_reduced_seq:
  "length (lms_map xs (suffix xs (abs_find_next_lms xs 0))) = card (lms_suffixes xs)"
  apply (simp add: lms_map_length lms_substr_seq_length)
  apply (cases "abs_find_next_lms xs 0 < length xs")
   apply (simp add: suffix_id_suffix)
   apply (subst distinct_card[OF lms_seq_distinct[of xs "abs_find_next_lms xs 0"], symmetric])
   apply (simp add: lms0_seq_has_all_lms)
   apply (metis card_image inj_on_suffix_to_id suffix_to_id_image)
  by (metis card_eq_0_iff diff_diff_cancel empty_set filter.simps(1) abs_find_next_lms_le_length
            lms0_seq_has_all_lms image_is_empty length_drop linorder_le_less_linear list.size(3)
            lms_seq_def suffix_to_id_def upt_eq_Nil_conv)

corollary lms_lms_map_in_suffixes:
  "abs_is_lms xs i \<Longrightarrow>
   lms_map xs (suffix xs i) \<in>
   suffix (lms_map xs (suffix xs (abs_find_next_lms xs 0))) ` {0..<card (lms_suffixes xs)}"
  by (metis atLeastLessThan_iff imageI length_reduced_seq lms_lms_map_is_suffix zero_le)

lemma card_lms_suffixes:
  "card (lms_suffixes xs) = card {i. abs_is_lms xs i}"
  by (metis card_image inj_on_suffix_to_id suffix_to_id_image)

lemma lms_map_image:
  "lms_map xs ` lms_suffixes xs =
   suffix (lms_map xs (suffix xs (abs_find_next_lms xs 0))) ` {0..<card (lms_suffixes xs)}"
proof (safe)
  fix i
  assume "abs_is_lms xs i"
  then show "lms_map xs (suffix xs i) \<in>
        suffix (lms_map xs (lms0_suffix xs)) ` {0..<card (lms_suffixes xs)}"
    using lms_lms_map_in_suffixes by blast
next
  fix i
  assume "i \<in> {0..<card (lms_suffixes xs)}"
  with card_lms_suffixes
  have "i < card {i. abs_is_lms xs i}"
    by (metis atLeastLessThan_iff)
  with lms_map_nth_suffix[of i xs]
  have "suffix (lms_map xs (lms0_suffix xs)) i = lms_map xs (suffix xs (nth_lms xs i))"
    by blast
  moreover
  have "suffix xs (nth_lms xs i) \<in> lms_suffixes xs"
    using \<open>i < card {i. abs_is_lms xs i}\<close> nth_lms by fastforce
  ultimately show "suffix (lms_map xs (lms0_suffix xs)) i \<in> lms_map xs ` lms_suffixes xs"
    by blast
qed

lemma monotone_on_lms_map:
  "monotone_on (lms_suffixes xs) list_less_ns list_less_ns (lms_map xs)"
proof (intro monotone_onI)
  fix x y
  assume "x \<in> lms_suffixes xs" "y \<in> lms_suffixes xs" "list_less_ns x y"
  with monotone_onD[OF monotone_on_lms_substr_seq_id, of x xs y]
  have "nslexordp list_less_ns (lms_substr_seq_id xs x) (lms_substr_seq_id xs y)"
    by blast
  moreover
  have "\<And>x. lms_map xs x = map (ordlistns.elem_rank (lms_substrs xs)) (lms_substr_seq_id xs x)"
    by (simp add: lms_map_def)
  moreover
  {
    have "set (lms_substr_seq_id xs x) \<subseteq> lms_substrs xs"
      by (simp add: Collect_mono_iff image_mono lms_seq_set lms_substr_seq_def)
    moreover
    have "set (lms_substr_seq_id xs y) \<subseteq> lms_substrs xs"
      by (simp add: Collect_mono_iff image_mono lms_seq_set lms_substr_seq_def)
    ultimately have
      "nslexordp list_less_ns (lms_substr_seq_id xs x) (lms_substr_seq_id xs y) =
       nslexordp (<) (map (ordlistns.elem_rank (lms_substrs xs)) (lms_substr_seq_id xs x))
                     (map (ordlistns.elem_rank (lms_substrs xs)) (lms_substr_seq_id xs y))"
      using monotone_on_iff_nslexordp[OF ordlistns.strict_mono_on_elem_rank, simplified,
                                 OF finite_lms_substrs[of xs] ordlistns.bij_betw_elem_rank_upt,
                                 OF finite_lms_substrs[of xs]]
      by blast
  }
  ultimately show "list_less_ns (lms_map xs x) (lms_map xs y)"
    by (simp add: nslexordp_eq_list_less_ns)
qed

lemma list_less_ns_lms_map_suffix:
  assumes "abs_is_lms xs i"
  and     "abs_is_lms xs j"
  and     "list_less_ns (lms_map xs (suffix xs i)) (lms_map xs (suffix xs j))"
shows "list_less_ns (suffix xs i) (suffix xs j)"
  using monotone_on_iff[OF monotone_on_lms_map, simplified] assms by blast

abbreviation 
  "lms0_map xs \<equiv> 
    lms_map xs (lms0_suffix xs)"

lemma sorted_reduced_seq_imp_lms:
  assumes "ordlistns.strict_sorted (map (suffix (lms0_map xs)) ys)"
  and     "\<forall>y \<in> set ys. y < card {i. abs_is_lms xs i}"
  shows "ordlistns.strict_sorted (map (suffix xs) (map ((!) (lms0_seq xs)) ys))"
proof (intro sorted_wrt_mapI)
  fix i j
  assume "i < j" "j < length (map ((!) (lms0_seq xs)) ys)"
  hence A: "i < j" "j < length ys"
    by simp_all
  with sorted_wrt_mapD[OF assms(1)]
  have "list_less_ns (suffix (lms0_map xs) (ys ! i)) (suffix (lms0_map xs) (ys ! j))" .
  moreover
  from lms_map_nth_suffix[of "ys ! i" xs]
  have "suffix (lms0_map xs) (ys ! i) = lms_map xs (suffix xs (nth_lms xs (ys ! i)))"
    using A(1) A(2) assms(2) by fastforce
  moreover
  from lms_map_nth_suffix[of "ys ! j" xs]
  have "suffix (lms0_map xs) (ys ! j) = lms_map xs (suffix xs (nth_lms xs (ys ! j)))"
    using A(2) assms(2) by fastforce
  moreover
  have "abs_is_lms xs (nth_lms xs (ys ! i))"
    by (meson A(1) A(2) assms(2) nth_lms nth_mem order.strict_trans)
  hence "suffix xs (nth_lms xs (ys ! i)) \<in> lms_suffixes xs"
    by blast
  moreover
  have "abs_is_lms xs (nth_lms xs (ys ! j))"
    by (meson A(2) assms(2) nth_lms nth_mem order.strict_trans)
  hence "suffix xs (nth_lms xs (ys ! j)) \<in> lms_suffixes xs"
    by blast
  ultimately have
    "list_less_ns (suffix xs (nth_lms xs (ys ! i))) (suffix xs (nth_lms xs (ys ! j)))"
    using monotone_on_iff[OF monotone_on_lms_map, simplified] by auto
  moreover
  from lms0_seq_nth[of "ys ! i" xs]
  have "lms0_seq xs ! (ys ! i) = nth_lms xs (ys ! i)"
    using A(1) A(2) assms(2) by force
  moreover
  from lms0_seq_nth[of "ys ! j" xs]
  have "lms0_seq xs ! (ys ! j) = nth_lms xs (ys ! j)"
    using A(2) assms(2) by force
  ultimately have
    "list_less_ns (suffix xs (lms0_seq xs ! (ys ! i))) (suffix xs (lms0_seq xs ! (ys ! j)))"
    by presburger
  then show "list_less_ns (suffix xs (map ((!) (lms0_seq xs)) ys ! i))
                          (suffix xs (map ((!) (lms0_seq xs)) ys ! j))"
    using A(1) A(2) by fastforce
qed

lemma sorted_distinct_lms_substr:
  assumes "ordlistns.sorted (map (lms_slice xs) ys)"
  and     "distinct (map (lms_slice xs) ys)"
  and     "\<forall>y \<in> set ys. y < length xs"
shows "ordlistns.sorted (map (suffix xs) ys)"
proof (intro sorted_wrt_mapI)
  fix i j
  assume "i < j" "j < length ys"
  with sorted_wrt_mapD[OF assms(1)]
  have "list_less_eq_ns (lms_slice xs (ys ! i)) (lms_slice xs (ys ! j))" .
  moreover
  have "lms_slice xs (ys ! i) \<noteq> lms_slice xs (ys ! j)"
    using \<open>i < j\<close> \<open>j < length ys\<close> assms(2) nth_eq_iff_index_eq by fastforce
  ultimately have  "list_less_ns (lms_slice xs (ys ! i)) (lms_slice xs (ys ! j))"
    using ordlistns.nless_le by blast
  then show "list_less_eq_ns (suffix xs (ys ! i)) (suffix xs (ys ! j))"
    by (metis \<open>i < j\<close> \<open>j < length ys\<close> less_lms_slice_imp_suffix assms(3) dual_order.strict_trans
              nth_mem ordlistns.dual_order.strict_implies_order)
qed

lemma distinct_lms0_map:
  assumes "distinct (lms0_map xs)"
  shows "distinct (map (lms_slice xs) (lms0_seq xs))"
proof (intro distinct_conv_nth[THEN iffD2] allI impI)
  fix i j
  assume "i < length (map (lms_slice xs) (lms0_seq xs))"
         "j < length (map (lms_slice xs) (lms0_seq xs))"
         "i \<noteq> j"
  hence A: "i < length (lms0_seq xs)" "j < length (lms0_seq xs)" "i \<noteq> j"
    by simp_all
  with distinct_conv_nth[THEN iffD1, OF assms]
  have B: "lms0_map xs ! i \<noteq> lms0_map xs ! j"
    by (metis card_lms_suffixes length_reduced_seq lms0_seq_length)
  moreover
  have "lms_substr_seq_id xs (lms0_suffix xs) = map (lms_slice xs) (lms0_seq xs)"
    by (metis lms_substr_seq_def lms_subtrs_seq_id_suffix)
  hence "lms0_map xs = map (ordlistns.elem_rank (lms_substrs xs)) (map (lms_slice xs) (lms0_seq xs))"
    by (simp add: lms_map_o_def)
  with A
  have "lms0_map xs ! i = ordlistns.elem_rank (lms_substrs xs) (lms_slice xs (lms0_seq xs ! i))"
       "lms0_map xs ! j = ordlistns.elem_rank (lms_substrs xs) (lms_slice xs (lms0_seq xs ! j))"
    by auto
  ultimately have "lms_slice xs (lms0_seq xs ! i) \<noteq> lms_slice xs (lms0_seq xs ! j)"
    by fastforce
  then show "map (lms_slice xs) (lms0_seq xs) ! i \<noteq> map (lms_slice xs) (lms0_seq xs) ! j"
    by (simp add: A(1) A(2))
qed

lemma sorted_distinct_lms_substr_perm:
  assumes "ordlistns.sorted (map (lms_slice xs) ys)"
  and     "distinct (lms0_map xs)"
  and     "ys <~~> lms0_seq xs"
shows "ordlistns.sorted (map (suffix xs) ys)"
  by (metis sorted_distinct_lms_substr[OF assms(1)] distinct_lms0_map[OF assms(2)] assms(3)
            distinct_map abs_is_lms_imp_less_length lms0_seq_has_all_lms mem_Collect_eq
            perm_distinct_iff perm_set_eq)

lemma list_less_ns_suffix_lms_map:
  assumes "abs_is_lms xs i"
  and     "abs_is_lms xs j"
  and     "list_less_ns (suffix xs i) (suffix xs j)"
shows "list_less_ns (lms_map xs (suffix xs i)) (lms_map xs (suffix xs j))"
  using monotone_on_iff[OF monotone_on_lms_map, simplified] assms by blast

lemma valid_list_lms_map:
  assumes "valid_list (a # b # xs)"
  and     "abs_is_lms (a # b # xs) i"
shows "valid_list (lms_map (a # b # xs) (suffix (a # b # xs) i))"
proof -
  let ?xs = "a # b # xs"
  have "\<exists>n. length ?xs = Suc n"
    by simp
  then obtain n where
    "length ?xs = Suc n"
    by blast
  hence "abs_is_lms ?xs n"
    using assms(1) abs_is_lms_last by fastforce

  have "lms_slice ?xs n = [bot]"
    using \<open>length ?xs = Suc n\<close> assms(1) lms_slice_last by blast

  have "\<exists>m. i = Suc m"
    using assms(2) lms_type_list_less_ns by auto
  then obtain m where
    "i = Suc m"
    by blast

  have P: "\<forall>x \<in> {k. abs_is_lms ?xs k}. x \<noteq> n \<longrightarrow>
            list_less_ns (lms_slice ?xs n) (lms_slice ?xs x)"
  proof safe
    fix x
    assume "abs_is_lms ?xs x" "x \<noteq> n"
    hence "\<exists>ys. lms_slice ?xs x = ?xs ! x # ys"
      using abs_is_lms_imp_less_length lms_slice_hd by blast
    then obtain ys where
      "lms_slice ?xs x = ?xs ! x # ys"
      by blast
    moreover
    have "bot < ?xs ! x"
      by (metis \<open>abs_is_lms ?xs x\<close> \<open>length ?xs = Suc n\<close> \<open>x \<noteq> n\<close> assms(1) bot.not_eq_extremum
                diff_Suc_1 hd_drop_conv_nth abs_is_lms_imp_less_length last_suffix_index)
    ultimately show "list_less_ns (lms_slice ?xs n) (lms_slice ?xs x)"
      by (simp add: \<open>lms_slice ?xs n = [bot]\<close> list_less_ns_cons_diff)
  qed

  have Q: "ordlistns.elem_rank (lms_substrs ?xs) (lms_slice ?xs n) = 0"
    unfolding ordlistns.elem_rank_def elm_rank_def
  proof -
    have "{y \<in> lms_substrs ?xs. list_less_ns y (lms_slice ?xs n)} = {}"
      using P by auto
    then show "card {y \<in> lms_substrs ?xs. list_less_ns y (lms_slice ?xs n)} = 0"
      by (metis card.empty)
  qed

  have R: "\<forall>x \<in> lms_substrs ?xs. list_less_ns (lms_slice ?xs n) x \<longrightarrow>
            ordlistns.elem_rank (lms_substrs ?xs) x > 0"
    using \<open>abs_is_lms ?xs n\<close> finite_lms_substrs ordlistns.strict_mono_onD
          ordlistns.strict_mono_on_elem_rank by fastforce

  have "[i..<length ?xs] = [i..<n] @ [n..<Suc n]"
    using \<open>length ?xs = Suc n\<close> assms(2) abs_is_lms_imp_less_length by fastforce
  hence "last (lms_seq ?xs i) = n"
    unfolding lms_seq_def
    by (simp add: \<open>abs_is_lms ?xs n\<close>)
  hence "last (lms_substr_seq ?xs i) = lms_slice ?xs n"
    by (metis assms(2) last_map list.discI lms_seq_Suc1 lms_substr_seq_def)
  hence "last (lms_substr_seq_id ?xs (suffix ?xs i)) = lms_slice ?xs n"
    by (metis lms_subtrs_seq_id_suffix)
  hence "last (lms_map ?xs (suffix ?xs i)) = 0"
    unfolding lms_map_o_def
    by (metis assms(2) Q last_map length_0_conv list.discI lms_seq_Suc1 lms_substr_seq_length
              lms_subtrs_seq_id_suffix)
  moreover
  have "butlast (lms_seq ?xs i) = filter (abs_is_lms ?xs) [i..<n]"
    unfolding lms_seq_def
    using \<open>[i..<length ?xs] = [i..<n] @ [n..<Suc n]\<close> \<open>abs_is_lms ?xs n\<close> by auto
  hence "\<forall>x \<in> set (butlast (lms_seq ?xs i)). x \<noteq> n \<and> abs_is_lms ?xs x"
    by clarsimp
  hence "\<forall>x \<in> set (butlast (lms_substr_seq ?xs i)).
          list_less_ns (lms_slice ?xs n) x"
    by (clarsimp simp: P map_butlast[symmetric] lms_substr_seq_def)
  hence S: "\<forall>x \<in> set (butlast (lms_substr_seq_id ?xs (suffix ?xs i))).
              list_less_ns (lms_slice ?xs n) x"
    by (metis lms_subtrs_seq_id_suffix)
  have "\<forall>x \<in> set (butlast (lms_map ?xs (suffix ?xs i))). x > 0"
  proof safe
    fix x
    assume "x \<in> set (butlast (lms_map ?xs (suffix ?xs i)))"
    moreover
    have "butlast (lms_map ?xs (suffix ?xs i)) =
           map (ordlistns.elem_rank (lms_substrs ?xs)) (butlast (lms_substr_seq_id ?xs (suffix ?xs i)))"
      unfolding lms_map_o_def
      by (simp add: map_butlast)
    ultimately have
      "\<exists>y \<in> set (butlast (lms_substr_seq_id ?xs (suffix ?xs i))).
          x = ordlistns.elem_rank (lms_substrs ?xs) y"
      by (simp add: in_set_mapD)
    then obtain y where A:
      "y \<in> set (butlast (lms_substr_seq_id ?xs (suffix ?xs i)))"
      "x = ordlistns.elem_rank (lms_substrs ?xs) y"
      by blast
    moreover
    have "y \<in> lms_substrs (a # b # xs)"
      by (metis calculation(1) in_set_butlastD in_set_conv_nth lms_substr_seq_id_nth_abs_is_lms)
    ultimately show "0 < x"
      using S R by blast
  qed
  moreover
  have "lms_map ?xs (suffix ?xs i) \<noteq> []"
    unfolding lms_map_o_def
    by (metis assms(2) list.discI list.map_disc_iff lms_seq_Suc1 lms_substr_seq_def
              lms_subtrs_seq_id_suffix)
  ultimately show ?thesis
    unfolding valid_list_iff_butlast_app_last
    by (metis bot_nat_def less_numeral_extra(3))
qed

end