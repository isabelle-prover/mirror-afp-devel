theory Abs_SAIS
  imports "../prop/Buckets"
          "../prop/LMS_List_Slice_Util"
          "../../util/Repeat"
begin 

section \<open>Induce Sorting\<close>

subsection \<open>Bucket Insert\<close>

fun abs_bucket_insert ::
  "(('a :: {linorder, order_bot}) \<Rightarrow> nat) \<Rightarrow>
   'a list \<Rightarrow>
   nat list \<Rightarrow>
   nat list \<Rightarrow>
   nat list \<Rightarrow>
   nat list"
  where
"abs_bucket_insert \<alpha> T _ SA [] = SA" |
"abs_bucket_insert \<alpha> T B SA (x # xs) =
  (let b = \<alpha> (T ! x);
       k = B ! b - Suc 0;
       SA' = SA[k := x];
       B' = B[b := k]
   in abs_bucket_insert \<alpha> T B' SA' xs)"

subsection \<open>Induce L-types\<close>

fun abs_induce_l_step ::
  "nat list \<times> nat list \<times> nat \<Rightarrow>
   (('a :: {linorder, order_bot}) \<Rightarrow> nat) \<times> 'a list \<Rightarrow>
   nat list \<times> nat list \<times> nat"
  where
"abs_induce_l_step (B, SA, i) (\<alpha>, T) =
  (if i < length SA \<and> SA ! i < length T
   then
     (case SA ! i of
        Suc j \<Rightarrow>
          (case suffix_type T j of
             L_type \<Rightarrow>
               (let k = \<alpha> (T ! j);
                    l = B ! k
                in (B[k := Suc l], SA[l := j], Suc i))
             | _ \<Rightarrow> (B, SA, Suc i))
        | _ \<Rightarrow> (B, SA, Suc i))
   else (B, SA, Suc i))"

definition abs_induce_l_base ::
  "(('a :: {linorder, order_bot}) \<Rightarrow> nat) \<Rightarrow>
   'a list \<Rightarrow>
   nat list \<Rightarrow>
   nat list \<Rightarrow>
   nat list \<times> nat list \<times> nat"
  where
"abs_induce_l_base \<alpha> T B SA = repeat (length T) abs_induce_l_step (B, SA, 0) (\<alpha>, T)"

definition abs_induce_l ::
  "(('a :: {linorder, order_bot}) \<Rightarrow> nat) \<Rightarrow>
   'a list \<Rightarrow>
   nat list \<Rightarrow>
   nat list \<Rightarrow>
   nat list"
  where
"abs_induce_l \<alpha> T B SA =
  (let (B', SA', i) = abs_induce_l_base \<alpha> T B SA
   in SA')"

subsection \<open>Induce S-types\<close>

fun abs_induce_s_step ::
  "nat list \<times> nat list \<times> nat \<Rightarrow>
   (('a :: {linorder, order_bot}) \<Rightarrow> nat) \<times> 'a list \<Rightarrow>
   nat list \<times> nat list \<times> nat"
  where
"abs_induce_s_step (B, SA, i) (\<alpha>, T) =
  (case i of
    Suc n \<Rightarrow>
      (if Suc n < length SA \<and> SA ! Suc n < length T then
        (case SA ! Suc n of
          Suc j \<Rightarrow>
            (case suffix_type T j of
              S_type \<Rightarrow>
                (let b = \<alpha> (T ! j);
                     k = B ! b - Suc 0
                 in (B[b := k], SA[k := j], n)
                )
              | _ \<Rightarrow> (B, SA, n)
            )
          | _ \<Rightarrow> (B, SA, n)
        )
        else
          (B, SA, n)
       )
    | _   \<Rightarrow> (B, SA, 0)
  )"

definition abs_induce_s_base ::
  "(('a :: {linorder, order_bot}) \<Rightarrow> nat) \<Rightarrow>
   'a list \<Rightarrow>
   nat list \<Rightarrow>
   nat list \<Rightarrow>
   nat list \<times> nat list \<times> nat"
  where
"abs_induce_s_base \<alpha> T B SA = repeat (length T) abs_induce_s_step (B, SA, length T) (\<alpha>, T)"

definition abs_induce_s ::
  "(('a :: {linorder, order_bot}) \<Rightarrow> nat) \<Rightarrow>
   'a list \<Rightarrow>
   nat list \<Rightarrow>
   nat list \<Rightarrow>
   nat list"
  where
"abs_induce_s \<alpha> T B SA =
  (let (B', SA', i) = abs_induce_s_base \<alpha> T B SA
   in SA')"

subsection \<open>Induce Sorting\<close>

definition abs_sa_induce ::
  "(('a :: {linorder, order_bot}) \<Rightarrow> nat) \<Rightarrow>
   'a list \<Rightarrow>
   nat list \<Rightarrow>
   nat list"
  where
"abs_sa_induce \<alpha> T LMS =
  (let
      B0 = map (bucket_end \<alpha> T) [0..<Suc (\<alpha> (Max (set T)))];
      B1 = map (bucket_start \<alpha> T) [0..<Suc (\<alpha> (Max (set T)))];

      \<comment>\<open>Initialise SA\<close>
      SA = replicate (length T) (length T);

      \<comment>\<open>Insert the LMS types into the suffix array \<close>
      SA = abs_bucket_insert \<alpha> T B0 SA (rev LMS);

      \<comment>\<open>Insert the L types into the suffix array \<close>
      SA = abs_induce_l \<alpha> T B1 SA

   \<comment>\<open>Insert the S types into the suffix array \<close>
   in abs_induce_s \<alpha> T (B0[0 := 0]) SA)"

section \<open>Rename Mapping\<close>

fun abs_rename_mapping' ::
  "('a :: {linorder, order_bot}) list \<Rightarrow>
    nat list \<Rightarrow>
    nat list \<Rightarrow>
    nat \<Rightarrow>
    nat list"
  where
"abs_rename_mapping' _ [] names _  = names" |
"abs_rename_mapping' _ [x] names i = names[x := i]" |
"abs_rename_mapping' T (a # b # xs) names i =
  (if lms_slice T a = lms_slice T b
    then abs_rename_mapping' T (b # xs) (names[a := i]) i
   else abs_rename_mapping' T (b # xs) (names[a := i]) (Suc i))"

definition abs_rename_mapping :: "('a :: {linorder, order_bot}) list \<Rightarrow> nat list \<Rightarrow> nat list"
  where
"abs_rename_mapping T LMS = abs_rename_mapping' T LMS (replicate (length T) (length T)) 0"


section \<open>Rename String\<close>

fun rename_string :: "nat list \<Rightarrow> nat list \<Rightarrow> nat list"
  where
"rename_string [] _ = []" |
"rename_string (x#xs) names = (names ! x) # rename_string xs names"

section \<open>Order LMS\<close>

fun order_lms :: "nat list \<Rightarrow> nat list \<Rightarrow> nat list"
  where
"order_lms LMS [] = []" |
"order_lms LMS (x # xs) = LMS ! x # order_lms LMS xs"

section \<open>Extract LMS\<close>

abbreviation abs_extract_lms :: "('a :: {linorder, order_bot}) list \<Rightarrow> nat list \<Rightarrow> nat list"
  where
"abs_extract_lms \<equiv> filter \<circ> abs_is_lms "

section \<open>SAIS Definition\<close>

function abs_sais ::
  "nat list \<Rightarrow>
   nat list"
where
  "abs_sais [] = []" |
  "abs_sais [x] = [0]" |
  "abs_sais (a # b # xs) =
   (let
      T = a # b # xs;

      \<comment>\<open> Extract the LMS types \<close>
      LMS0 = abs_extract_lms T [0..<length T];

      \<comment>\<open> Induce the prefix ordering based on LMS \<close>
      SA = abs_sa_induce id T LMS0;

      \<comment>\<open> Extract the LMS types \<close>
      LMS = abs_extract_lms T SA;

      \<comment>\<open> Create a new alphabet \<close>
      names = abs_rename_mapping T LMS;

      \<comment>\<open> Make a reduced string \<close>
      T' = rename_string LMS0 names;

      \<comment>\<open> Obtain the correct ordering of LMS-types \<close>
      LMS = (if distinct T' then LMS else order_lms LMS0 (abs_sais T'))

   \<comment>\<open> Induce the suffix ordering based of LMS \<close>
   in abs_sa_induce id T LMS)"
  by pat_completeness blast+

end