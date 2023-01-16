
theory Evasive
  imports
    Bij_betw_simplicial_complex_bool_func
    MkIfex
begin

section\<open>Relation between type @{typ "bool vec => bool"}
    and type @{typ "'a boolfunc"}\<close>

definition vec_to_boolfunc :: "nat \<Rightarrow> (bool vec => bool) => (nat boolfunc)"
  where "vec_to_boolfunc n f = (\<lambda>i. f (vec n i))"

lemma
  ris: "reads_inside_set (\<lambda>i. bool_fun_threshold_2_3 (vec 4 i)) (set [0,1,2,3])"
  unfolding reads_inside_set_def
  unfolding bool_fun_threshold_2_3_def
  unfolding count_true_def
  unfolding dim_vec
  unfolding set_list_four [symmetric] by simp

lemma
  shows "val_ifex (mk_ifex (vec_to_boolfunc 4 bool_fun_threshold_2_3) [0,1,2,3])
    = vec_to_boolfunc 4 bool_fun_threshold_2_3"
  apply (rule ext)
  apply (rule val_ifex_mk_ifex_equal)
  unfolding vec_to_boolfunc_def
  using ris .

text\<open>For any Boolean function in dimension @{term n},
  its ifex representation is @{const ifex_ordered} and @{const ifex_minimal}.\<close>

lemma mk_ifex_boolean_function:
  fixes f :: "bool vec => bool"
  shows "ro_ifex (mk_ifex (vec_to_boolfunc n f) [0..n])"
  using mk_ifex_ro by fast

text\<open>Any Boolean function in dimension @{term n} can be
  seen as an expression over the underlying set of variables.\<close>

lemma
  reads_inside_set_boolean_function:
  fixes f :: "bool vec => bool"
  shows "reads_inside_set (vec_to_boolfunc n f) {..<n}"
  unfolding vec_to_boolfunc_def
  unfolding reads_inside_set_def
  by (smt (verit, best) dim_vec eq_vecI index_vec lessThan_iff)

text\<open>Any Boolean function of a finite dimension
  is equal to its ifex representation
  by means of @{const mk_ifex}.\<close>

lemma
  mk_ifex_equivalence:
  fixes f :: "bool vec => bool"
  shows "val_ifex (mk_ifex (vec_to_boolfunc n f) [0..n])
    = vec_to_boolfunc n f"
  apply (rule ext)
  apply (rule val_ifex_mk_ifex_equal)
  using reads_inside_set_boolean_function [of n f]
  unfolding reads_inside_set_def by auto

definition bcount_true :: "nat => (nat=> bool) => nat"
  where "bcount_true n f =  (\<Sum>i = 0..<n. if f i then 1 else (0::nat))"

definition boolfunc_threshold_2_3 :: "(nat => bool) => bool"
  where "boolfunc_threshold_2_3 = (\<lambda>v. 2 \<le> bcount_true 4 v)"

(*definition boolfunc_threshold_2_3 :: "(nat => bool) => bool"
  where "boolfunc_threshold_2_3 = (\<lambda>v. if 2 \<le> bcount_true 4 v then True else False)"*)

definition proj_2 :: "(nat => bool) => bool"
  where "proj_2 = (\<lambda>v. v 2)"

definition proj_2_n3 :: "(nat => bool) => bool"
  where "proj_2_n3 = (\<lambda>v. v 2 \<and> \<not> v 3)"

text\<open>The following definition computes the height of a @{typ "'a ifex"} expression.\<close>

fun height :: "'a ifex => nat"
  where "height Trueif = 0"
  | "height Falseif = 0"
  | "height (IF v va vb) = 1 + max (height va) (height vb)"

text\<open>Both @{term mk_ifex} and @{term height} can be used in computations.\<close>

lemma "height (mk_ifex (boolfunc_threshold_2_3) [0,1,2,3]) = 4"
  by eval

lemma "height (mk_ifex (proj_2) [0,1,2,3]) = 1"
  by eval

lemma "mk_ifex (proj_2) [0] = Falseif" by eval

lemma "height (mk_ifex (proj_2) [0]) = 0" by eval

lemma "mk_ifex (proj_2) [3,2,1,0] = IF 2 Trueif Falseif"
  by eval

lemma "mk_ifex (proj_2) [0,1,2,3] = IF 2 Trueif Falseif"
  by eval

lemma "height (mk_ifex (proj_2) [0,1,2,3]) = 1" by eval

lemma "mk_ifex (proj_2_n3) [0,1,2,3] = IF 2 (IF 3 Falseif Trueif) Falseif" by eval

lemma "mk_ifex (bf_False::nat boolfunc) [0,1,2,3] = Falseif" by eval

lemma "height (mk_ifex (bf_False::nat boolfunc) [0,1,2,3]) = 0" by eval

lemma "mk_ifex (bf_True::nat boolfunc) [0,1,2,3] = Trueif" by eval

lemma "height (mk_ifex (bf_True::nat boolfunc) [0,1,2,3]) = 0" by eval

section\<open>Definition of \emph{evasive} Boolean function\<close>

text\<open>Now we introduce the definition of evasive Boolean function.
  It is based on the height of the ifex expression of the given function.
  The definition is inspired by the one by Scoville~\<^cite>\<open>\<open>Ex. 6.19\<close> in "SC19"\<close>.\<close>

definition evasive :: "nat => ((nat => bool) => bool) => bool"
  where "evasive n f \<equiv> (height (mk_ifex f [0..n])) = n"

corollary "evasive 4 boolfunc_threshold_2_3" by eval

lemma "\<not> evasive 4 proj_2" by eval

lemma "\<not> evasive 4 proj_2_n3" by eval

lemma "\<not> evasive 4 bf_True" by eval

lemma "\<not> evasive 4 bf_False" by eval

end