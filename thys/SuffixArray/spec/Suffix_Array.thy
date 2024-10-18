theory Suffix_Array
  imports
    "../util/Sorting_Util"
    "../order/List_Lexorder_Util"
    "../order/Suffix"
    "../order/Valid_List"
    "../order/List_Permutation_Util"
begin

section \<open>Axiomatic Suffix Array Specification\<close>

locale Suffix_Array_General =
  fixes sa :: "('a  :: {linorder, order_bot}) list \<Rightarrow> nat list"
  assumes sa_g_permutation: "sa s <~~> [0..<length s]"
    and sa_g_sorted: "strict_sorted (map (suffix s) (sa s))"

locale Suffix_Array_Restricted =
  fixes sa :: "nat list \<Rightarrow> nat list"
  assumes sa_r_permutation: "valid_list s \<Longrightarrow> sa s <~~> [0..<length s]"
    and sa_r_sorted: "valid_list s \<Longrightarrow> strict_sorted (map (suffix s) (sa s))"

section \<open>Wrapper for Natural Number String only Algorithm\<close>

definition sa_nat_wrapper ::
  "('a :: linorder list \<Rightarrow> 'a \<Rightarrow> nat) \<Rightarrow> (nat list \<Rightarrow> nat list) \<Rightarrow> 'a :: linorder list \<Rightarrow> nat list"
where
  "sa_nat_wrapper \<alpha> sa xs = 
  tl (sa ((map (\<lambda>x. Suc (\<alpha> xs x)) xs) @ [bot]))"

end