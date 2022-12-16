(* This file includes our top-level hybrid algorithm (which uses 
  the algorithm defined in Hybrid_Multiv_Matrix.thy as a component).
*)

theory Hybrid_Multiv_Algorithm

imports Hybrid_Multiv_Matrix
  Virtual_Substitution.ExportProofs

begin

section "Most recent code"
  (* Invariant: For all (a, q) in the output, either
  q is 0 or the leading coefficient of q is assumed nonzero in a *)
function lc_assump_generation:: "rmpoly \<Rightarrow> assumps\<Rightarrow> (assumps \<times> rmpoly) list"
  where "lc_assump_generation q assumps = 
     (if q = 0 then [(assumps, 0)] else
     (case (lookup_assump_aux (Polynomial.lead_coeff q) assumps) of
      None \<Rightarrow>
        let zero = lc_assump_generation (one_less_degree q) ((Polynomial.lead_coeff q, (0::rat)) # assumps);
            one  = ((Polynomial.lead_coeff q, (1::rat)) # assumps, q);
            minus_one  = ((Polynomial.lead_coeff q, (-1::rat)) # assumps, q) in
          one#minus_one#zero
      | (Some i) \<Rightarrow>
        (if i = 0 then lc_assump_generation (one_less_degree q) assumps
        else 
         [(assumps, q)]
        )
  )) "
  by auto
termination apply (relation  "measure (\<lambda>(q, assumps). (let w = (if q \<noteq> 0 then 1 else 0) in w + Polynomial.degree q))")
    apply (auto) using one_less_degree_degree
   apply (smt (verit, del_insts) Multiv_Poly_Props.one_less_degree_def Polynomial.coeff_diff Polynomial.lead_coeff_monom cancel_comm_monoid_add_class.diff_cancel coeff_eq_0 degree_monom_eq leading_coeff_neq_0 linorder_neqE_nat)
  using one_less_degree_degree
  by (smt (verit) Multiv_Poly_Props.one_less_degree_def Polynomial.coeff_diff Polynomial.lead_coeff_monom cancel_comm_monoid_add_class.diff_cancel coeff_eq_0 degree_monom_eq leading_coeff_neq_0 linorder_neqE_nat) 

declare lc_assump_generation.simps[simp del]

value "lc_assump_generation ([:Var 1:]::rmpoly) [(Var 1, 1)]"

fun lc_assump_generation_list:: "rmpoly list \<Rightarrow> assumps \<Rightarrow> (assumps \<times> rmpoly list) list"
  where "lc_assump_generation_list [] assumps = [(assumps, [])]"
  | "lc_assump_generation_list (q#qs) assumps = (let rec = lc_assump_generation q assumps in
    concat (map (
      \<lambda>(new_assumps, r). (let list_rec = lc_assump_generation_list qs new_assumps in
      map (\<lambda>elem. (fst elem, r#(snd elem))) list_rec) ) rec ))"

declare lc_assump_generation_list.simps[simp del]

value "lc_assump_generation_list [([:Var 1:]::rmpoly), ([:Var 1:]::rmpoly)] []"

value "(lc_assump_generation_list [([:Var 1:]::rmpoly)] []) ! 1"

definition poly_p:: "rmpoly list \<Rightarrow> rmpoly"
  where "poly_p qs = (let prod_list = prod_list qs in 
    prod_list*(pderiv prod_list))"

primrec check_all_const_deg_gen:: "('a::zero) Polynomial.poly list \<Rightarrow> bool"
  where "check_all_const_deg_gen  [] = True"
  | "check_all_const_deg_gen (h#T) = (if Polynomial.degree h = 0 then (check_all_const_deg_gen T) else False)"

primrec prod_list_var_gen:: "('a::idom) list \<Rightarrow> ('a::idom)"
  where "prod_list_var_gen [] = 1"
  | "prod_list_var_gen (h#T) = (if h = 0 then (prod_list_var_gen T) else (h* prod_list_var_gen T))"

fun poly_p_in_branch:: "(assumps \<times> rmpoly list) \<Rightarrow> rmpoly"
  where "poly_p_in_branch (assumps, qs) =
 (if (check_all_const_deg_gen qs = True) then  [:0, 1:] else 
  (pderiv (prod_list_var_gen qs)) * (prod_list_var_gen qs)
)"

fun limit_points_on_branch:: "(assumps \<times> rmpoly list) \<Rightarrow> (rat list \<times> rat list)"
  where "limit_points_on_branch (assumps, qs) = 
    (map (\<lambda>q. if q = 0 then 0 else (rat_of_int \<circ> Sturm_Tarski.sign) (lookup_assump (Polynomial.lead_coeff q) assumps)) qs, 
    map (\<lambda>q. if q = 0 then 0 else (rat_of_int \<circ> Sturm_Tarski.sign) (lookup_assump (Polynomial.lead_coeff q) assumps)*(-1)^(Polynomial.degree q)) qs)"

(* value "map limit_points_on_branch (lc_assump_generation_list [([:Var 1:]::rmpoly), ([:Var 1:]::rmpoly)] [])" *)

fun extract_signs:: "(assumps \<times> matrix_equation) list \<Rightarrow> (assumps \<times> rat list list) list"
  where "extract_signs qs = map (\<lambda>(assumps, (mat , (subs, signs))). (assumps, signs)) qs"

fun sign_determination_inner:: "rmpoly list \<Rightarrow> assumps \<Rightarrow> (assumps \<times> rat list list) list"
  where "sign_determination_inner qs assumps = 
( let branches = lc_assump_generation_list qs assumps  in
concat (map (\<lambda>branch. 
let poly_p_branch = poly_p_in_branch branch;
    (pos_limit_branch, neg_limit_branch) = limit_points_on_branch branch;
    calculate_data_branch = extract_signs (calculate_data_assumps_M poly_p_branch (snd branch) (fst branch))
in map (\<lambda>(a, signs). (a, pos_limit_branch#neg_limit_branch#signs)) calculate_data_branch
) branches
))"

fun extract_polys:: "atom fm \<Rightarrow> real mpoly list"
  where "extract_polys (Atom (Less p)) = [p]" |
    "extract_polys (Atom (Leq p)) = [p]" |
    "extract_polys (Atom (Eq p)) = [p]" |
    "extract_polys (Atom (Neq p)) = [p]" |
    "extract_polys (TrueF) = []" |
    "extract_polys (FalseF) = []" |
    "extract_polys (And \<phi> \<psi>) =  (extract_polys \<phi> )@ (extract_polys \<psi>)" |
    "extract_polys (Or \<phi> \<psi>) = (extract_polys \<phi>)@(extract_polys \<psi>)" |
    "extract_polys (Neg \<phi>)  = (extract_polys \<phi>)" |
    "extract_polys (ExN 0 \<phi>)  = (extract_polys \<phi>)" |
    "extract_polys (AllN 0 \<phi>)  = (extract_polys \<phi>)" |
    "extract_polys _  = []"

(* Evaluating a formula over a lookup semantics *)
fun lookup_sem_M :: "atom fm \<Rightarrow> (real mpoly \<times> rat) list \<Rightarrow> bool option"
  where
    "lookup_sem_M TrueF ls = Some (True)"
  | "lookup_sem_M FalseF ls = Some (False)"
  |  "lookup_sem_M (And l r) ls = (case (lookup_sem_M l ls, lookup_sem_M r ls) 
      of (Some i, Some j) \<Rightarrow> Some (i \<and> j)
      | _ \<Rightarrow> None)"
  | "lookup_sem_M (Or l r) ls = (case (lookup_sem_M l ls, lookup_sem_M r ls) 
      of (Some i, Some j) \<Rightarrow> Some (i \<or> j)
      | _ \<Rightarrow> None)"
  | "lookup_sem_M (Neg l) ls = (case (lookup_sem_M l ls) 
      of Some i \<Rightarrow> Some ((\<not>i))
      | _ \<Rightarrow> None)"
  | "lookup_sem_M (Atom (Less p)) ls = 
     (case (lookup_assump_aux p ls) of
     Some i \<Rightarrow> Some (i < 0)
    | _ \<Rightarrow> None
     )"
  | "lookup_sem_M (Atom (Leq p)) ls = 
     (case (lookup_assump_aux p ls) of
     Some i \<Rightarrow> Some (i \<le> 0)
    | _ \<Rightarrow> None
     )"
  | "lookup_sem_M (Atom (Eq p)) ls = 
     (case (lookup_assump_aux p ls) of
     Some i \<Rightarrow> Some (i = 0)
    | _ \<Rightarrow> None
     )"
  | "lookup_sem_M (Atom (Neq p)) ls = 
     (case (lookup_assump_aux p ls) of
     Some i \<Rightarrow> Some (i \<noteq> 0)
    | _ \<Rightarrow> None
     )"
  | "lookup_sem_M (ExN 0 l) ls = lookup_sem_M l ls"
  | "lookup_sem_M (AllN 0 l) ls = lookup_sem_M l ls"
  | "lookup_sem_M _ ls = None"

fun assump_to_atom:: "(real mpoly \<times> rat) \<Rightarrow> atom"
  where "assump_to_atom (p, r) = 
      (if r = 0 then (Eq p) 
    else (if r < 0 then (Less p)
    else (Less (-p))
  ))"

fun assump_to_atom_fm:: "assumps \<Rightarrow> atom fm"
  where "assump_to_atom_fm [] = TrueF"
  | "assump_to_atom_fm ((p, r)#T) = And (Atom (assump_to_atom (p, r))) (assump_to_atom_fm T)"

fun create_disjunction:: "(assumps \<times> rat list list) list  \<Rightarrow> atom fm"
  where "create_disjunction [] = FalseF"
  | "create_disjunction ((a, _)#T) = Or (assump_to_atom_fm a) (create_disjunction T)"

fun elim_forall:: "atom fm \<Rightarrow> atom fm"
  where "elim_forall F = 
  (
    let qs = extract_polys F;
        univ_qs = univariate_in qs 0;
        reindexed_univ_qs = map (map_poly (lowerPoly 0 1)) univ_qs;
        data = sign_determination_inner reindexed_univ_qs [];
        new_data = filter (\<lambda>(assumps, signs_list). 
          list_all (\<lambda> signs. 
          let paired_signs = zip qs signs in
            lookup_sem_M F paired_signs = (Some True)) 
          signs_list
          ) data
  in create_disjunction new_data
  )"

definition elim_exist:: "atom fm \<Rightarrow> atom fm"
  where "elim_exist F = Neg (elim_forall (Neg F))"

fun structural_complexity:: "atom fm \<Rightarrow> (nat \<times> nat)"
  where 
    "structural_complexity TrueF = (0, 1)"
  | "structural_complexity FalseF = (0, 1)"
  | "structural_complexity (Atom a) = (0, 1)"
  | "structural_complexity (And F1 F2) = 
  (let (qF1, sF1) = structural_complexity F1;
    (qF2, sF2) = structural_complexity F2
  in (qF1 + qF2, 1 + sF1 + sF2))"
  | "structural_complexity (Or F1 F2) = 
  (let (qF1, sF1) = structural_complexity F1;
    (qF2, sF2) = structural_complexity F2
  in (qF1 + qF2, 1 + sF1 + sF2))"
  | "structural_complexity (Neg F) =
  (let (qF, sF) = structural_complexity F
  in (qF, 1 + sF))"
  | "structural_complexity (ExQ F) = 
  (let (qF, sF) = structural_complexity F
  in (1+ qF, 1 + sF))"
  | "structural_complexity (AllQ F) =
  (let (qF, sF) = structural_complexity F
  in (1+ qF, 1 + sF))"
  | "structural_complexity (ExN n F) = 
  (let (qF, sF) = structural_complexity F
  in (2 + n+qF, 2+n+sF))"
  | "structural_complexity (AllN n F) = 
  (let (qF, sF) = structural_complexity F
  in (2 + n+qF, 2+n+sF))"

declare structural_complexity.simps[simp del]

(* Can take a few seconds to load*)
fun qe:: "atom fm \<Rightarrow> atom fm"
  where 
    "qe TrueF = TrueF"
  | "qe FalseF = FalseF"
  | "qe (Atom a) = (Atom a)"
  | "qe (And F1 F2) = And (qe F1) (qe F2)"
  | "qe (Or F1 F2) = Or (qe F1) (qe F2)"
  | "qe (Neg F) = Neg (qe F)"
  | "qe (ExQ F) = elim_exist (qe F)"
  | "qe (AllQ F) = elim_forall (qe F)"
  | "qe (AllN n F) = (elim_forall ^^ n) (qe F)"
  | "qe (ExN n F) = (elim_exist ^^ n) (qe F)"


definition qe_with_VS:: "atom fm \<Rightarrow> atom fm"
  where "qe_with_VS F = (qe \<circ> VSLEG) F"


value "((MPoly (Pm_fmap (fmap_of_list [(Pm_fmap (fmap_of_list []), 1)])))::real mpoly) = Const 1"

(* value "elim_forall (Atom (Less (Var 0)))"
value "elim_forall (Atom (Leq(Const (-1)*(Var 0)^2)))" *)
(* value "freeIn 0 (elim_forall (Atom (Leq(Const (-1)*(Var 0)^2))))" *)

(* eval_ground is only used for testing purposes, so we haven't proved
  anything about its correctness.
  Its purpose is to simplify the output of "qe" on fully quantified QE problems
  (sentences) to either True or False.  
  It should not be used outside of this context.
 *)
fun eval_ground :: "atom fm \<Rightarrow> real list \<Rightarrow> bool" where
  "eval_ground (Atom a) \<Gamma> = aEval a \<Gamma>" |
  "eval_ground (TrueF) _ = True" |
  "eval_ground (FalseF) _ = False" |
  "eval_ground (And \<phi> \<psi>) \<Gamma> = ((eval_ground \<phi> \<Gamma>) \<and> (eval_ground \<psi> \<Gamma>))" |
  "eval_ground (Or \<phi> \<psi>) \<Gamma> = ((eval_ground \<phi> \<Gamma>) \<or> (eval_ground \<psi> \<Gamma>))" |
  "eval_ground (Neg \<phi>) \<Gamma> = (\<not> (eval_ground \<phi> \<Gamma>))"

value "VSLEG (ExQ (ExQ (Atom (Less (Var 0^2*Var 1 ::real mpoly)))))"
value "(qe_with_VS (ExQ (ExQ (Atom (Less (Var 0^2*Var 1 ::real mpoly))))))"
  (* These may not finish *)
  (* value "qe (ExQ (ExQ (Atom (Less (Var 0^2*Var 1 ::real mpoly)))))" *)
  (* value "eval_ground (qe (ExQ (Atom (Less (Var 0^4 + Var 0 + 1 ::real mpoly)))))" *)


section "Decision Portion"

fun extract_polys_from_assumps:: "assumps \<Rightarrow> real mpoly list"
  where "extract_polys_from_assumps [] = []"
  | "extract_polys_from_assumps ((p, i)#T) = p#(extract_polys_from_assumps T)"

fun assumps_are_consistent:: "assumps \<Rightarrow> rat list list \<Rightarrow> bool"
  where "assumps_are_consistent assump ls = ((map snd assump) \<in> set ls)"

(* Extract the list of consistent sign assignments from a list of matrix equations with consistent assumptions *)
fun find_consistent_signs_at_roots_single_M:: "(assumps \<times> matrix_equation) \<Rightarrow> rat list list"
  where "find_consistent_signs_at_roots_single_M (assumps, (M, (subsets, signs))) = signs"

fun find_consistent_signs_at_roots_M:: "(assumps \<times> matrix_equation) list \<Rightarrow> rat list list"
  where "find_consistent_signs_at_roots_M l = concat (map find_consistent_signs_at_roots_single_M l)"

subsection "Limit Points and Helper Functions" 
definition expand_signs_list:: "real mpoly list \<Rightarrow> rat list list \<Rightarrow> (real mpoly \<times> rat) list list"
  where "expand_signs_list qs csas =  map (\<lambda>csa. zip qs csa) csas"

(* Under valuation, the lead coefficient has this sign *)
fun first_nonzero_coefficient_degree_helper:: "(real mpoly \<times> rat) list \<Rightarrow> real mpoly list \<Rightarrow> nat \<Rightarrow> (nat \<times> rat)"
  where "first_nonzero_coefficient_degree_helper assumps [] n = (n, 0)"
  | "first_nonzero_coefficient_degree_helper assumps (h # T) n = 
    (case lookup_assump_aux h assumps of
         (Some i) \<Rightarrow> (if i \<noteq> 0 then (n, i) else first_nonzero_coefficient_degree_helper assumps T (n-1))
          | None \<Rightarrow> first_nonzero_coefficient_degree_helper assumps T (n-1))"

fun first_nonzero_coefficient_degree_helper_simp:: "(real mpoly \<times> rat) list \<Rightarrow> real mpoly list  \<Rightarrow> (nat \<times> rat)"
  where "first_nonzero_coefficient_degree_helper_simp assumps [] = (0, 0)"
  | "first_nonzero_coefficient_degree_helper_simp assumps (h # T) = 
    (case lookup_assump_aux h assumps of
         (Some i) \<Rightarrow> (if i \<noteq> 0 then (length T, i) else first_nonzero_coefficient_degree_helper_simp assumps T)
          | None \<Rightarrow> first_nonzero_coefficient_degree_helper_simp assumps T)"

lemma first_nonzero_coefficient_degree_helper_simp:
  shows "first_nonzero_coefficient_degree_helper_simp assumps ell 
    = first_nonzero_coefficient_degree_helper assumps ell (length ell - 1)"
proof (induct "ell")
  case Nil
  then show ?case 
    by auto 
next
  case (Cons a ell)
  moreover { 
    assume *: "lookup_assump_aux a assumps = Some 0"
    then have "first_nonzero_coefficient_degree_helper_simp assumps (a # ell) =
       first_nonzero_coefficient_degree_helper assumps (a # ell) (length (a # ell) - 1)"
      using Cons.hyps 
      by simp
  }
  moreover { 
    assume *: "\<exists>k\<noteq>0. lookup_assump_aux a assumps = Some k"
    then obtain k where k_prop: "k\<noteq>0 \<and> lookup_assump_aux a assumps = Some k "
      by auto
    then have "first_nonzero_coefficient_degree_helper_simp assumps (a # ell) =
       first_nonzero_coefficient_degree_helper assumps (a # ell) (length (a # ell) - 1)"
      using Cons.hyps 
      by simp
  }
  moreover { 
    assume *: "lookup_assump_aux a assumps = None"
    then have "first_nonzero_coefficient_degree_helper_simp assumps (a # ell) =
       first_nonzero_coefficient_degree_helper assumps (a # ell) (length (a # ell) - 1)"
      by (simp add: local.Cons)
  }
  ultimately have "first_nonzero_coefficient_degree_helper_simp assumps (a # ell) =
       first_nonzero_coefficient_degree_helper assumps (a # ell) (length (a # ell) - 1)"
    by fastforce
  then show ?case by auto
qed

declare pull_out_pairs.simps [simp del]
declare construct_rhs_vector_rec_M.simps [simp del]

declare first_nonzero_coefficient_degree_helper.simps[simp del]
declare first_nonzero_coefficient_degree_helper_simp.simps[simp del]

definition sign_and_degree_of_first_nonzero_coefficient:: "(real mpoly \<times> rat) list \<Rightarrow> rmpoly \<Rightarrow> (nat \<times> rat)"
  where "sign_and_degree_of_first_nonzero_coefficient assumps q = 
    first_nonzero_coefficient_degree_helper assumps (rev (Polynomial.coeffs q)) ((length (Polynomial.coeffs q)) - 1)"

definition sign_and_degree_of_first_nonzero_coefficient_simp:: "(real mpoly \<times> rat) list \<Rightarrow> rmpoly \<Rightarrow> (nat \<times> rat)"
  where "sign_and_degree_of_first_nonzero_coefficient_simp assumps q = 
    first_nonzero_coefficient_degree_helper_simp assumps (rev (Polynomial.coeffs q))"

lemma sign_and_degree_of_first_nonzero_coefficient_simp:
  "sign_and_degree_of_first_nonzero_coefficient assumps q = sign_and_degree_of_first_nonzero_coefficient_simp assumps q"
  using first_nonzero_coefficient_degree_helper_simp
  by (simp add: sign_and_degree_of_first_nonzero_coefficient_def sign_and_degree_of_first_nonzero_coefficient_simp_def) 

definition sign_and_degree_of_first_nonzero_coefficient_list:: "rmpoly list \<Rightarrow> (real mpoly \<times> rat) list \<Rightarrow> (nat \<times> rat) list"
  where "sign_and_degree_of_first_nonzero_coefficient_list qs assumps = 
    map (\<lambda>q. sign_and_degree_of_first_nonzero_coefficient_simp assumps q) qs"

fun all_pos_limit_points:: "rmpoly list \<Rightarrow> rat list list \<Rightarrow> rat list list"
  where "all_pos_limit_points qs coeffs_signs  = 
(if qs = [] then []
else (if (all_coeffs qs = []) then ([map (\<lambda>x. 0) qs]) 
  else
  (let expand_coeffs_signs = expand_signs_list (all_coeffs qs) coeffs_signs in
  map  ((map snd) \<circ> sign_and_degree_of_first_nonzero_coefficient_list qs) expand_coeffs_signs)))"

fun all_neg_limit_points_aux:: "(nat \<times> rat) list \<Rightarrow> rat list"
  where "all_neg_limit_points_aux deg_sign_list = map (\<lambda>(deg, sgn). (-1)^deg*sgn) deg_sign_list"

fun all_neg_limit_points:: "rmpoly list \<Rightarrow> rat list list \<Rightarrow> rat list list"
  where "all_neg_limit_points qs coeffs_signs  = 
  (let expand_coeffs_signs = expand_signs_list (all_coeffs qs) coeffs_signs;
   (sgn_and_deg_list::(nat \<times> rat) list list) = map (sign_and_degree_of_first_nonzero_coefficient_list qs) expand_coeffs_signs
    in map all_neg_limit_points_aux sgn_and_deg_list)"

(* 
value "all_pos_limit_points [[:Var 0, Var 1:], [:Var 1:]] [[1, 1], [-1, 1]]"
value "all_neg_limit_points [[:Var 0, Var 1:], [:Var 1:]] [[1, 1], [-1, 1]]"
*)

subsection "Top-level functions QE"

definition transform:: "real mpoly list \<Rightarrow> real mpoly Polynomial.poly list"
  where "transform qs = (let vs = variables_list qs in
   map (\<lambda>q. (mpoly_to_mpoly_poly_alt (nth vs (length vs - 1)) q)) qs)"

fun calculate_data_to_signs:: "(assumps \<times> matrix_equation) list \<Rightarrow> (assumps \<times> rat list list) list"
  where "calculate_data_to_signs ell = map (\<lambda>x. (fst x, snd (snd (snd x)))) ell"

fun sum_list:: "nat list \<Rightarrow> nat"
  where "sum_list [] = 0"
  | "sum_list (a # ell) = a + (sum_list ell)"

fun limit_point_data:: "(rat \<times> nat) list \<Rightarrow> (rat list \<times> rat list)"
  where "limit_point_data ell = (map fst ell, map (\<lambda>x. fst x * (-1)^(snd x)) ell)"

fun generate_signs_and_assumptions:: "rmpoly list \<Rightarrow> (assumps \<times> rat list list) list"
  where "generate_signs_and_assumptions qs_univ =
    (let p = poly_p qs_univ; calc_data = calculate_data_M p qs_univ in [])"

(* This generates the code export.  Note that the resulting SML code 
  has to be slightly instrumented before it will run. *)
export_code calculate_data_assumps_M qe VSLEG add mult C V pow minus
  real_of_int real_mult real_plus real_minus real_div print_mpoly
  eval_ground
  in SML module_name export

end