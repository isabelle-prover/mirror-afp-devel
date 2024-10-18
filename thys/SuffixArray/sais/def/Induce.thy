theory Induce
  imports Induce_S Induce_L Bucket_Insert 
begin

section "Induce"

definition sa_induce_r0 ::
  "(('a :: {linorder, order_bot}) \<Rightarrow> nat) \<Rightarrow>
   'a list \<Rightarrow>
   nat list \<Rightarrow>
   nat list"
  where
"sa_induce_r0 \<alpha> T LMS =
  (let
      B0 = map (bucket_end \<alpha> T) [0..<Suc (\<alpha> (Max (set T)))];
      B1 = map (bucket_start \<alpha> T) [0..<Suc (\<alpha> (Max (set T)))];

      \<comment>\<open>Initialise SA\<close>
      SA = replicate (length T) (length T);

      \<comment>\<open>Get the suffix types\<close>
      ST = abs_get_suffix_types T;

      \<comment>\<open>Insert the LMS types into the suffix array \<close>
      SA = abs_bucket_insert \<alpha> T B0 SA (rev LMS);

      \<comment>\<open>Insert the L types into the suffix array \<close>
      SA = induce_l \<alpha> T ST B1 SA

   \<comment>\<open>Insert the S types into the suffix array \<close>
   in induce_s \<alpha> T ST (B0[0 := 0]) SA)"

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

definition sa_induce_r2 ::
  "(('a :: {linorder, order_bot}) \<Rightarrow> nat) \<Rightarrow>
   'a list \<Rightarrow>
   SL_types list \<Rightarrow>
   nat list \<Rightarrow>
   nat list"
  where
"sa_induce_r2 \<alpha> T ST LMS =
  (let
      B0 = map (bucket_end \<alpha> T) [0..<Suc (\<alpha> (Max (set T)))];
      B1 = map (bucket_start \<alpha> T) [0..<Suc (\<alpha> (Max (set T)))];

      \<comment>\<open>Initialise SA\<close>
      SA = replicate (length T) (length T);

      \<comment>\<open>Insert the LMS types into the suffix array\<close>
      SA = bucket_insert \<alpha> T B0 SA (rev LMS);

      \<comment>\<open>Insert the L types into the suffix array\<close>
      SA = induce_l \<alpha> T ST B1 SA

   \<comment>\<open>Insert the S types into the suffix array\<close>
   in induce_s \<alpha> T ST (B0[0 := 0]) SA)"

abbreviation "sa_induce \<equiv> sa_induce_r2"

end