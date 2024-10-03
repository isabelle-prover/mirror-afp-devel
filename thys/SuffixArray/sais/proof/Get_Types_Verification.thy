theory Get_Types_Verification
  imports 
    "../abs-def/Abs_SAIS"
    "../def/Get_Types"
begin

section "Suffix Types"

lemma get_suffix_types_step_r0_ret:
  "\<exists>xs' i'. get_suffix_types_step_r0 (xs, i) ys = (xs', i') \<and>
            length xs' = length xs \<and> (i = 0 \<longrightarrow> i' = 0) \<and> (\<exists>j. i = Suc j \<longrightarrow> i' = j)"
  by (cases i; simp)

lemma get_suffix_types_step_r0_0:
  "get_suffix_types_step_r0 (xs, 0) ys = (xs, 0)"
  by simp

lemma get_suffix_types_step_r0_Suc:
  "\<lbrakk>Suc i < length xs; length xs = length ys; \<forall>k < length xs. i < k \<longrightarrow> xs ! k = suffix_type ys k\<rbrakk> \<Longrightarrow>
   get_suffix_types_step_r0 (xs, Suc i) ys = (xs[i := suffix_type ys i], i)"
  apply clarsimp
  apply (intro conjI impI arg_cong[where f = "\<lambda>x. xs[i := x]"])
    apply (simp add: nth_gr_imp_l_type)
   apply (simp add: nth_less_imp_s_type)
  by (metis suffix_type_neq)

fun get_suffix_types_inv
  where
"get_suffix_types_inv ys (xs, i) =
  (length xs = length ys \<and> i < length xs \<and> (\<forall>k < length xs. i \<le> k \<longrightarrow> xs ! k = suffix_type ys k))"

lemma get_suffix_types_inv_maintained:
  assumes "get_suffix_types_inv ys (xs, i)"
shows "get_suffix_types_inv ys (get_suffix_types_step_r0 (xs, i) ys)"
proof (cases i)
  case 0
  hence "get_suffix_types_step_r0 (xs, i) ys = (xs, 0)"
    using get_suffix_types_step_r0_0 by simp
  moreover
  have "get_suffix_types_inv ys (xs, 0)"
    using "0" assms by auto
  ultimately show ?thesis
    by presburger
next
  case (Suc n)
  hence "get_suffix_types_step_r0 (xs, i) ys = (xs[n := suffix_type ys n], n)"
    by (metis Suc_leI assms get_suffix_types_inv.simps get_suffix_types_step_r0_Suc)
  moreover
  have "get_suffix_types_inv ys (xs[n := suffix_type ys n], n)"
    using Suc assms le_eq_less_or_eq by fastforce
  ultimately show ?thesis
    by simp
qed

lemma get_suffix_types_inv_established:
  "xs \<noteq> [] \<Longrightarrow> get_suffix_types_inv xs (replicate (length xs) S_type, length xs - Suc 0)"
  by (simp add: suffix_type_last)

lemma get_suffix_types_base_prod':
  "\<exists>xs'. repeat n get_suffix_types_step_r0 (xs, m) ys = (xs', m - n)"
proof (induct n arbitrary: xs m)
  case 0
  then show ?case
    by (simp add: repeat_0)
next
  case (Suc n)
  note IH = this

  from repeat_step[of n get_suffix_types_step_r0 "(xs, m)" ys]
  have "repeat (Suc n) get_suffix_types_step_r0 (xs, m) ys
          = get_suffix_types_step_r0 (repeat n get_suffix_types_step_r0 (xs, m) ys) ys" .
  moreover
  from IH[of xs m]
  obtain xs' where
    "repeat n get_suffix_types_step_r0 (xs, m) ys = (xs', m - n)"
    by blast
  moreover
  have "\<exists>xs''. get_suffix_types_step_r0 (xs', m - n) ys = (xs'', m - Suc n)"
  proof (cases "m-n")
    case 0
    hence "get_suffix_types_step_r0 (xs', m - n) ys = (xs', 0)"
      by auto
    moreover
    have "m - Suc n = 0"
      using "0" by auto
    ultimately show ?thesis
      by simp
  next
    case (Suc k)
    have "(m - n < length xs' \<and> m - n < length ys) \<or> \<not>(m - n < length xs' \<and> m - n < length ys)"
      by blast
    moreover
    have "m - n < length xs' \<and> m - n < length ys \<Longrightarrow> ?thesis"
      by (clarsimp simp add: Suc diff_Suc)
    moreover
    have "\<not>(m - n < length xs' \<and> m - n < length ys) \<Longrightarrow> ?thesis"
     by (clarsimp simp add: Suc diff_Suc)
    ultimately show ?thesis
      by blast
  qed
  ultimately show ?case
    by presburger
qed

lemma get_suffix_types_inv_holds:
  assumes "xs \<noteq> []"
  shows "get_suffix_types_inv xs (get_suffix_types_base xs)"
  unfolding get_suffix_types_base_def
  apply (rule repeat_maintain_inv)
   apply (metis get_suffix_types_inv_maintained prod.collapse)
  apply (rule get_suffix_types_inv_established[OF assms])
  done

lemma get_suffix_types_base_prod:
  "\<exists>xs'. get_suffix_types_base xs = (xs', 0)"
  unfolding get_suffix_types_base_def
  by (metis cancel_comm_monoid_add_class.diff_cancel get_suffix_types_base_prod')

lemma get_suffix_types_base_ref:
  "get_suffix_types_base xs = (abs_get_suffix_types xs, 0)"
proof (cases "xs \<noteq> []")
  assume "\<not> xs \<noteq> []"
  then show ?thesis
    by (clarsimp simp: get_suffix_types_base_def repeat_0 get_suffix_types_def)
next
  assume "xs \<noteq> []"
  with get_suffix_types_inv_holds
  have "get_suffix_types_inv xs (get_suffix_types_base xs)"
    by blast
  moreover
  from get_suffix_types_base_prod[of xs]
  obtain xs' where
    "get_suffix_types_base xs = (xs', 0)"
    by blast
  ultimately have "get_suffix_types_inv xs (xs', 0)"
    by auto
  moreover
  have "abs_get_suffix_types xs = xs'"
    unfolding list_eq_iff_nth_eq
    by (metis bot_nat_0.extremum calculation get_suffix_types_correct 
              get_suffix_types_inv.simps
              length_abs_get_suffix_types)
  ultimately show ?thesis
    by (simp add: \<open>get_suffix_types_base xs = (xs', 0)\<close>)
qed

lemma get_suffix_types_eq:
  "get_suffix_types xs = abs_get_suffix_types xs"
  by (simp add: get_suffix_types_base_ref get_suffix_types_def)

lemmas length_get_suffix_types = 
       length_abs_get_suffix_types[simplified get_suffix_types_eq]
(*
abbreviation "get_suffix_types_ref \<equiv> get_suffix_types"
lemmas get_suffix_types_refinement = get_suffix_types_r0_ref
*)

section "LMS types"

lemma is_lms_refinement:
  assumes "length ST = length T" "\<forall>i < length T. ST ! i = suffix_type T i"
  shows "is_lms_ref ST = abs_is_lms T"
proof
  fix i
  show "is_lms_ref ST i = abs_is_lms T i"
  proof (cases i)
    case 0
    then show ?thesis
      by (simp add: abs_is_lms_0)
  next
    case (Suc n)
    then show ?thesis
      by (metis Suc_lessD assms abs_is_lms_def abs_is_lms_imp_less_length is_lms_ref.simps(2))
  qed
qed

section "Extracting LMS types"

lemma extract_lms_eq:
  "\<lbrakk>length ST = length T; \<forall>i < length T. ST ! i = suffix_type T i\<rbrakk> \<Longrightarrow>
   extract_lms ST = abs_extract_lms T"
  by (clarsimp simp: fun_eq_iff is_lms_refinement)

section "LMS Substrings"

lemma find_next_lms_refinement:
  "\<lbrakk>length ST = length T; \<forall>i < length T. ST ! i = suffix_type T i\<rbrakk> \<Longrightarrow>
   find_next_lms ST=  abs_find_next_lms T"
  unfolding find_next_lms_def abs_find_next_lms_def
  apply (clarsimp simp: is_lms_refinement fun_eq_iff)
  by argo

lemma lms_slice_refinement:
  "\<lbrakk>length ST = length T; \<forall>i < length T. ST ! i = suffix_type T i\<rbrakk> \<Longrightarrow>
   lms_slice_ref T ST = lms_slice T"
  unfolding lms_slice_ref_def lms_slice_def
  by (clarsimp simp: find_next_lms_refinement fun_eq_iff)

section \<open>Rename Mapping\<close>

lemma rename_mapping'_refinement:
  assumes "length ST = length T" "\<forall>i < length T. ST ! i = suffix_type T i"
  shows "rename_mapping' T ST = abs_rename_mapping' T"
proof (intro fun_eq_iff[THEN iffD2] allI)
  fix xs ns i
  show "rename_mapping' T ST xs ns i = abs_rename_mapping' T xs ns i"
    using assms
  proof (induct rule: rename_mapping'.induct[of _ T ST xs ns i])
    case (1 T ST ns i)
    then show ?case
      by simp
  next
    case (2 T ST x ns i)
    then show ?case
      by simp
  next
    case (3 T ST a b xs ns i)
    then show ?case
      by (simp add: lms_slice_refinement)
  qed
qed

lemma rename_mapping_refinement:
  assumes "length ST = length T" 
  assumes "\<forall>i < length T. ST ! i = suffix_type T i"
  shows "rename_mapping T ST =  abs_rename_mapping T"
  by (clarsimp simp: fun_eq_iff assms rename_mapping'_refinement abs_rename_mapping_def
                        rename_mapping_def)

end