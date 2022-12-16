(* This file includes the algorithm to construct the multivariate matrix equation.

As a naming convention, we try to maintain some consistency with prior work
for the univariate case.  When we write a function with a univariate analog in our
multivariate setting, we use _M to indicate that the function is now multivariate.
*)

theory Hybrid_Multiv_Matrix
  imports
    (* This entry is useful for the mpoly, mpoly poly connection *)
    "Factor_Algebraic_Polynomial.Poly_Connection"
    Multiv_Pseudo_Remainder_Sequence
    "BenOr_Kozen_Reif.More_Matrix"
    "HOL-Library.Mapping"
    "BenOr_Kozen_Reif.Renegar_Algorithm"

begin

section "Find CSAS to qs at zeros of p"

subsection "Towards Tarski Queries" 
  (* Should only be called with a degree list that is as long as sturm_seq *)
fun sminus:: "nat list \<Rightarrow> rat list \<Rightarrow> int" where
  "sminus degree_list sturm_seq = changes (map (\<lambda>i. (-1)^(nth degree_list i)*(nth sturm_seq i)) [0..< length degree_list]) "

definition changes_R_smods_multiv:: "rat list \<Rightarrow> nat list \<Rightarrow> int"
  where "changes_R_smods_multiv signs_list degree_list \<equiv> (sminus degree_list signs_list) - (changes signs_list)" 

definition changes_R_smods_multiv_val:: "real mpoly Polynomial.poly list \<Rightarrow> real list \<Rightarrow> int" where
  "changes_R_smods_multiv_val sturm_seq val \<equiv> (let (eval_ss::real Polynomial.poly list) = (eval_mpoly_poly_list val sturm_seq) in (changes_poly_neg_inf eval_ss - changes_poly_pos_inf eval_ss))"


subsection "Building the Matrix Equation"

type_synonym rmpoly = "real mpoly Polynomial.poly"
type_synonym assumps = "(real mpoly \<times> rat) list"
type_synonym matrix_equation = "(rat mat \<times> ((nat list * nat list) list \<times> rat list list))"

definition base_case_info_M:: "(assumps \<times> matrix_equation) list"
  where "base_case_info_M = [([], base_case_info_R)]"

definition base_case_info_M_assumps:: "assumps \<Rightarrow> (assumps \<times> matrix_equation) list"
  where "base_case_info_M_assumps init_assumps = [(init_assumps, base_case_info_R)]"

fun combine_systems_single_M:: "rmpoly \<Rightarrow> rmpoly list \<Rightarrow> (assumps \<times> matrix_equation) \<Rightarrow> rmpoly list \<Rightarrow> (assumps \<times> matrix_equation) \<Rightarrow> (assumps \<times> matrix_equation)"
  where "combine_systems_single_M p q1 (a1, m1) q2 (a2,m2) = 
  (append a1 a2, snd (combine_systems_R p (q1, m1) (q2, m2)))"

fun combine_systems_M:: "rmpoly \<Rightarrow> rmpoly list \<Rightarrow> (assumps \<times> matrix_equation) list \<Rightarrow> rmpoly list \<Rightarrow> 
(assumps \<times> matrix_equation) list => rmpoly list \<times> ((assumps \<times> matrix_equation) list)"
  where "combine_systems_M p q1 list1 q2 list2 = 
(append q1 q2, concat (map (\<lambda>l1. (map (\<lambda>l2. combine_systems_single_M p q1 l1 q2 l2) list2)) list1))"

(* returns list of (assumps \times sturm sequence)*)
definition construct_NofI_R_spmods:: "rmpoly \<Rightarrow> assumps \<Rightarrow> rmpoly list \<Rightarrow> rmpoly list \<Rightarrow> (assumps \<times> (rmpoly list)) list"
  where "construct_NofI_R_spmods p assumps I1 I2 = (
    let new_p = sum_list (map (\<lambda>x. x^2) (p # I1)) in
    spmods_multiv new_p ((pderiv new_p)*(prod_list I2))) assumps"

fun construct_NofI_single_M:: "(assumps \<times> (rmpoly list)) \<Rightarrow> 
  (assumps \<times> rat)"
  where "construct_NofI_single_M (input_assumps, ss)  = 
  (let lcs = lead_coeffs ss;
    sa_list = map (\<lambda>lc. lookup_assump lc input_assumps) lcs;
    degrees_list = degrees ss in
  (input_assumps, rat_of_int (changes_R_smods_multiv sa_list degrees_list)))"

fun construct_NofI_M:: "rmpoly \<Rightarrow> assumps \<Rightarrow> rmpoly list \<Rightarrow> rmpoly list => (assumps \<times> rat) list"
  where "construct_NofI_M p assumps I1 I2 =
(let ss_list = construct_NofI_R_spmods p assumps I1 I2 in
  map construct_NofI_single_M ss_list)"

fun pull_out_pairs:: "rmpoly list \<Rightarrow> (nat list * nat list) list \<Rightarrow> (rmpoly list \<times> rmpoly list) list"
  where "pull_out_pairs qs Is = 
  map (\<lambda>(I1, I2). ((retrieve_polys qs I1), (retrieve_polys qs I2))) Is"

fun construct_rhs_vector_rec_M:: "rmpoly \<Rightarrow> assumps \<Rightarrow> (rmpoly list \<times> rmpoly list) list \<Rightarrow> (assumps \<times> rat list) list"
  where "construct_rhs_vector_rec_M p assumps [] = [(assumps, [])]"
  | "construct_rhs_vector_rec_M p assumps ((qs1, qs2)#[]) = 
    (let TQ_list = construct_NofI_M p assumps qs1 qs2 in
    map (\<lambda>(new_assumps, tq). (new_assumps, [tq])) TQ_list)"
  | "construct_rhs_vector_rec_M p assumps ((qs1, qs2)#T) = 
    concat (let TQ_list = construct_NofI_M p assumps qs1 qs2 in
    (map (\<lambda>(new_assumps, tq). (let rec = construct_rhs_vector_rec_M p new_assumps T in
     map (\<lambda>r. (fst r,  tq#snd r)) rec)) TQ_list))"

definition construct_rhs_vector_M:: "rmpoly \<Rightarrow> assumps \<Rightarrow> rmpoly list \<Rightarrow> (nat list * nat list) list \<Rightarrow> (assumps \<times> rat vec) list"
  where "construct_rhs_vector_M p assumps qs Is = 
  map (\<lambda>res. (fst res, vec_of_list (snd res))) (construct_rhs_vector_rec_M p assumps (pull_out_pairs qs Is))"

definition solve_for_lhs_single_M:: "rmpoly \<Rightarrow> rmpoly list \<Rightarrow> (nat list * nat list) list \<Rightarrow> rat mat \<Rightarrow> rat vec \<Rightarrow> rat vec"
  where "solve_for_lhs_single_M p qs subsets matr rhs_vector =
     mult_mat_vec (matr_option (dim_row matr) (mat_inverse_var matr)) rhs_vector"

definition solve_for_lhs_M:: "rmpoly \<Rightarrow> assumps \<Rightarrow> rmpoly list \<Rightarrow> (nat list * nat list) list \<Rightarrow> rat mat \<Rightarrow> (assumps \<times> rat vec) list"
  where "solve_for_lhs_M p assumps qs subsets matr =
  map (\<lambda>rhs. (fst rhs, solve_for_lhs_single_M p qs subsets matr (snd rhs))) (construct_rhs_vector_M p assumps qs subsets)"

subsection "Reduction" 
fun reduce_system_single_M:: "rmpoly \<Rightarrow> rmpoly list \<Rightarrow> (assumps \<times> matrix_equation) \<Rightarrow> (assumps \<times> matrix_equation) list"
  where "reduce_system_single_M p qs (assumps, (m,subs,signs)) =
  map (\<lambda>lhs. (fst lhs, reduction_step_R m signs subs (snd lhs))) (solve_for_lhs_M p assumps qs subs m)"

fun reduce_system_M:: "rmpoly \<Rightarrow> rmpoly list \<Rightarrow> (assumps \<times> matrix_equation) list \<Rightarrow> (assumps \<times> matrix_equation) list"
  where "reduce_system_M p qs input_list = concat (map (reduce_system_single_M p qs) input_list)" 

subsection "Top-level Function"
fun calculate_data_M:: "rmpoly \<Rightarrow> rmpoly list \<Rightarrow> (assumps \<times> matrix_equation) list"
  where
    "calculate_data_M p qs = 
  ( let len = length qs in
    if len = 0 then map (\<lambda>(assumps,(a,(b,c))). (assumps, (a,b,map (drop 1) c))) (reduce_system_M p [1] base_case_info_M)
    else if len \<le> 1 then reduce_system_M p qs base_case_info_M
    else
    (let q1 = take (len div 2) qs; left = calculate_data_M p q1;
         q2 = drop (len div 2) qs; right = calculate_data_M p q2;
         comb = combine_systems_M p q1 left q2 right in
         reduce_system_M p (fst comb) (snd comb)
    )
  )"

(* Very similar to calculate_data_M, but takes assumptions as an input *)
(* The top-level function we use to construct the multivariate matrix equation *)
fun calculate_data_assumps_M:: "rmpoly \<Rightarrow> rmpoly list \<Rightarrow> assumps \<Rightarrow> (assumps \<times> matrix_equation) list"
  where
    "calculate_data_assumps_M p qs init_assumps = 
  ( let len = length qs in
    if len = 0 then map (\<lambda>(assumps,(a,(b,c))). (assumps, (a,b,map (drop 1) c))) (reduce_system_M p [1] (base_case_info_M_assumps init_assumps))
    else if len \<le> 1 then reduce_system_M p qs (base_case_info_M_assumps init_assumps)
    else
    (let q1 = take (len div 2) qs; left = calculate_data_assumps_M p q1 init_assumps;
         q2 = drop (len div 2) qs; right = calculate_data_assumps_M p q2 init_assumps;
         comb = combine_systems_M p q1 left q2 right in
         reduce_system_M p (fst comb) (snd comb)
    )
  )"

(* export_code vars calculate_data_assumps_M
in SML module_name export *)


end

