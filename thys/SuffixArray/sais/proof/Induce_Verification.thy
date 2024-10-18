theory Induce_Verification
  imports 
   "../abs-proof/Abs_Induce_Verification" 
   "../def/Induce"
   Induce_S_Verification Induce_L_Verification Bucket_Insert_Verification 
begin         

section "Induce"

lemma sa_induce_to_r0:
  assumes "set LMS = {i. abs_is_lms T i}"
  and     "distinct LMS"
  and     "valid_list T"
  and     "strict_mono \<alpha>"
  and     "\<alpha> bot = 0"
  and     "Suc 0 < length T"
  shows   "abs_sa_induce \<alpha> T LMS = sa_induce_r0 \<alpha> T LMS"
proof -

  let ?ST = "abs_get_suffix_types T"

  note A = length_abs_get_suffix_types[of T]

  from get_suffix_types_correct[of T] A
  have B: "\<forall>i < length ?ST. ?ST ! i = suffix_type T i"
    by simp

  let ?B0 = "map (bucket_end \<alpha> T) [0..<Suc (\<alpha> (Max (set T)))]" and
      ?B1 = "map (bucket_start \<alpha> T) [0..<Suc (\<alpha> (Max (set T)))]" and
      ?SA0 = "replicate (length T) (length T)"

  let ?B2 = "?B0[0 := 0]"
  let ?SA1 = "abs_bucket_insert \<alpha> T ?B0 ?SA0 (rev LMS)"
  let ?SA2 = "abs_induce_l \<alpha> T ?B1 ?SA1"
  let ?SA3 = "abs_induce_s \<alpha> T (?B0[0 := 0]) ?SA2"

  let ?SA2' = "induce_l \<alpha> T ?ST ?B1 ?SA1"
  let ?SA3' = "induce_s \<alpha> T ?ST (?B0[0 := 0]) ?SA2"

  from lms_pre_established[OF assms(1,2,4)]
  have "lms_pre \<alpha> T ?B0 ?SA0 (rev LMS)" .

  have "l_perm_pre \<alpha> T ?B1 ?SA1"
    using \<open>lms_pre \<alpha> T ?B0 ?SA0 (rev LMS)\<close> 
assms(3,4) l_perm_pre_established by blast
  with A B
  have "?SA2 = ?SA2'"
    using abs_induce_l_eq l_perm_pre_elims(7) by blast

  have "s_perm_pre \<alpha> T ?B2 ?SA2 (length T)"
    using \<open>l_perm_pre \<alpha> T ?B1 ?SA1\<close> \<open>lms_pre \<alpha> T ?B0 ?SA0 (rev LMS)\<close> assms(3-6)
          s_perm_pre_established by blast
  with A B
  have "?SA3 = ?SA3'"
    using abs_induce_s_eq by blast
  then show ?thesis
    by (metis `?SA2 = ?SA2'` abs_sa_induce_def sa_induce_r0_def)
qed

definition sa_induce_r1 ::
  "(('a :: {linorder, order_bot}) \<Rightarrow> nat) \<Rightarrow>
   'a list \<Rightarrow>
   SL_types list \<Rightarrow>
   nat list \<Rightarrow>
   nat list"
  where
"sa_induce_r1 \<alpha> T ST LMS =
  (let
      B0 = map (bucket_end \<alpha> T) [0..<Suc (\<alpha> (Max (set T)))];
      B1 = map (bucket_start \<alpha> T) [0..<Suc (\<alpha> (Max (set T)))];

      \<comment>\<open>Initialise SA\<close>
      SA = replicate (length T) (length T);

      \<comment>\<open>Insert the LMS types into the suffix array\<close>
      SA = abs_bucket_insert \<alpha> T B0 SA (rev LMS);

      \<comment>\<open>Insert the L types into the suffix array\<close>
      SA = induce_l \<alpha> T ST B1 SA

   \<comment>\<open>Insert the S types into the suffix array\<close>
   in induce_s \<alpha> T ST (B0[0 := 0]) SA)"

lemma sa_induce_r0_to_r1:
  assumes "length ST = length T"
  and     "\<forall>i < length ST. ST ! i = suffix_type T i"
shows "sa_induce_r0 \<alpha> T LMS = sa_induce_r1 \<alpha> T ST LMS"
proof -
  let ?ST = "abs_get_suffix_types T"

  note A = length_abs_get_suffix_types[of T]

  from get_suffix_types_correct[of T] A
  have B: "\<forall>i < length ?ST. ?ST ! i = suffix_type T i"
    by simp
  with A
  have "?ST = ST"
    by (simp add: assms nth_equalityI)
  then show ?thesis
    by (simp add: sa_induce_r0_def sa_induce_r1_def)
qed

lemma sa_induce_to_r1:
  assumes "set LMS = {i. abs_is_lms T i}"
  and     "distinct LMS"
  and     "valid_list T"
  and     "strict_mono \<alpha>"
  and     "\<alpha> bot = 0"
  and     "Suc 0 < length T"
  and     "length ST = length T"
  and     "\<forall>i < length ST. ST ! i = suffix_type T i"
shows "abs_sa_induce \<alpha> T LMS = sa_induce_r1 \<alpha> T ST LMS"
  by (simp add: assms sa_induce_r0_to_r1 sa_induce_to_r0)

lemma sa_induce_r1_to_r2:
  "sa_induce_r1 \<alpha> T ST LMS = sa_induce_r2 \<alpha> T ST LMS"
  by (simp add: abs_bucket_insert_eq sa_induce_r1_def sa_induce_r2_def)

lemma abs_sa_induce_to_r2:
  assumes "set LMS = {i. abs_is_lms T i}"
  and     "distinct LMS"
  and     "valid_list T"
  and     "strict_mono \<alpha>"
  and     "\<alpha> bot = 0"
  and     "Suc 0 < length T"
  and     "length ST = length T"
  and     "\<forall>i < length ST. ST ! i = suffix_type T i"
shows "abs_sa_induce \<alpha> T LMS = sa_induce_r2 \<alpha> T ST LMS"
  by (metis assms sa_induce_r1_to_r2 sa_induce_to_r1)

end