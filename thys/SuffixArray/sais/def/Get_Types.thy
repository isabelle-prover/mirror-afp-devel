theory Get_Types
  imports 
    "../prop/List_Type" 
    "../prop/LMS_List_Slice_Util" 
    "../../util/Repeat" 
begin

section "Suffix Types"

fun 
  get_suffix_types_step_r0 ::
    "SL_types list \<times> nat \<Rightarrow> 'a :: {linorder, order_bot} list \<Rightarrow> SL_types list \<times> nat"
where
  "get_suffix_types_step_r0 (xs, i) ys =
    (case i of
      0 \<Rightarrow> (xs, 0)
      | Suc j \<Rightarrow>
        (if Suc j < length xs \<and> Suc j < length ys then
          (if ys ! j < ys ! Suc j then
            (xs[j := S_type], j)
           else if ys ! j > ys ! Suc j then
            (xs[j := L_type], j)
           else
            (xs[j := xs ! Suc j], j))
         else
          (xs, j)))"

definition get_suffix_types_base
  where
"get_suffix_types_base xs \<equiv>
  repeat (length xs - Suc 0) get_suffix_types_step_r0
         (replicate (length xs) S_type, length xs - Suc 0) xs"

definition get_suffix_types
  where
"get_suffix_types xs \<equiv> fst (get_suffix_types_base xs)"

section "LMS types"

fun is_lms_ref
  where
"is_lms_ref ST 0 = False" |
"is_lms_ref ST (Suc i) =
  (if Suc i < length ST then ST ! i = L_type \<and> ST ! (Suc i) = S_type else False)"

section "Extracting LMS types"

abbreviation "extract_lms ST xs \<equiv> filter (\<lambda>i. is_lms_ref ST i) xs"

section "LMS Substrings"

definition find_next_lms :: "SL_types list \<Rightarrow> nat \<Rightarrow> nat"
  where
"find_next_lms ST i =
  (case find (\<lambda>j. is_lms_ref ST j) [Suc i..<length ST] of
    Some j \<Rightarrow> j
    | _ \<Rightarrow> length ST)"

definition 
  lms_slice_ref :: 
    "('a :: {linorder, order_bot}) list \<Rightarrow> SL_types list \<Rightarrow> nat \<Rightarrow> 'a list"
where
  "lms_slice_ref T ST i = 
    list_slice T i (Suc (find_next_lms ST i))"

section \<open>Rename Mapping\<close>

fun rename_mapping' ::
  "('a :: {linorder, order_bot}) list \<Rightarrow> SL_types list \<Rightarrow> 
   nat list \<Rightarrow> nat list \<Rightarrow> nat \<Rightarrow> nat list"
where
  "rename_mapping' _ _ [] names _  = names" |
  "rename_mapping' _ _ [x] names i = names[x := i]" |
  "rename_mapping' T ST (a # b # xs) names i =
    (if lms_slice_ref T ST a = lms_slice_ref T ST b
      then 
        rename_mapping' T ST (b # xs) (names[a := i]) i
     else 
        rename_mapping' T ST (b # xs) (names[a := i]) (Suc i))"

definition 
  rename_mapping :: 
    "('a :: {linorder, order_bot}) list \<Rightarrow> SL_types list \<Rightarrow> nat list \<Rightarrow> nat list"
where
  "rename_mapping T ST LMS = 
    rename_mapping' T ST LMS (replicate (length T) (length T)) 0"

end