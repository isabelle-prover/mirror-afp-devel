(* Author: Maximilian Schäffeler *)

theory Code_DP
  imports 
    Value_Iteration
    Policy_Iteration
    Modified_Policy_Iteration
    Splitting_Methods
    "HOL-Library.Code_Target_Numeral"
    "Gauss_Jordan.Code_Generation_IArrays"
begin

section \<open>Code Generation for MDP Algorithms\<close>

subsection \<open>Least Argmax\<close>

lemma least_list:
  assumes "sorted xs" "\<exists>x \<in> set xs. P x"
  shows "(LEAST x \<in> set xs. P x) = the (find P xs)"
  using assms
proof (induction xs)
  case (Cons a xs)
  thus ?case
  proof (cases "P a")
    case False
    have "(LEAST x \<in> set (a # xs). P x) = (LEAST x \<in> set xs. P x)"
      using False Cons(2)
      by simp metis
    thus ?thesis
      using False Cons
      by simp
  qed (auto intro: Least_equality)
qed auto

definition "least_enum P = the (find P (sorted_list_of_set (UNIV :: ('b:: {finite, linorder}) set)))"

lemma least_enum_eq: "\<exists>x. P x \<Longrightarrow> least_enum P = (LEAST x. P x)"
  by (auto simp: least_list[symmetric] least_enum_def)

definition "least_max_arg_max_list f init xs = 
  foldl (\<lambda>(am, m) x. if f x > m then (x, f x) else (am, m)) init xs"  

lemma snd_least_max_arg_max_list: 
  "snd (least_max_arg_max_list f (n, f n) xs) = (MAX x \<in> insert n (set xs). f x)"
  unfolding least_max_arg_max_list_def
proof (induction xs arbitrary: n)
  case (Cons a xs)
  then show ?case
    by (cases "xs = []") (fastforce simp: max.assoc[symmetric])+
qed auto

lemma least_max_arg_max_list_snd_fst: "snd (least_max_arg_max_list f (x, f x) xs) = f (fst (least_max_arg_max_list f (x, f x) xs))"
  by (induction xs arbitrary: x) (auto simp: least_max_arg_max_list_def)

lemma fst_least_max_arg_max_list: 
  fixes f :: "_ \<Rightarrow> _ :: linorder"
  assumes "sorted (n#xs)"
  shows "fst (least_max_arg_max_list f (n, f n) xs) 
  = (LEAST x. is_arg_max f (\<lambda>x. x \<in> insert n (set xs)) x)"
  unfolding least_max_arg_max_list_def
  using assms proof (induction xs arbitrary: n)
  case Nil
  then show ?case
    by (auto simp: is_arg_max_def intro!: Least_equality[symmetric])
next
  case (Cons a xs)
  hence "sorted (a#xs)"
    by auto
  then show ?case
  proof (cases "f a > f n")
    case True
    then show ?thesis
      by (fastforce simp: is_arg_max_def Cons.IH[OF \<open>sorted (a#xs)\<close>] intro!: cong[of Least, OF refl])
  next
    case False
    have "(LEAST b. is_arg_max f (\<lambda>x. x \<in> insert n (set (a # xs))) b)
      = (LEAST b. is_arg_max f (\<lambda>x. x \<in> (set (n # xs))) b)"
    proof (cases "is_arg_max f (\<lambda>x. x \<in> set (n #a# xs)) a")
      case True
      hence "(LEAST b. is_arg_max f (\<lambda>x. x \<in>  (set (n#a # xs))) b) = n"
        using Cons False
        by (fastforce simp: is_arg_max_linorder intro!: Least_equality)
      thus ?thesis
        using False True Cons
        by (fastforce simp: is_arg_max_linorder intro!: Least_equality[symmetric])
    next
      case False
      thus ?thesis
        by (fastforce simp: not_less is_arg_max_linorder intro!: cong[of Least, OF refl])
    qed
    thus ?thesis
      using False Cons
      by (auto simp add: Cons.IH[OF \<open>sorted (a#xs)\<close>])
  qed
qed

definition "least_arg_max_enum f X = (
  let xs = sorted_list_of_set (X :: (_ :: {finite, linorder}) set) in
  fst (least_max_arg_max_list f (hd xs, f (hd xs)) (tl xs)))"

definition "least_max_arg_max_enum f X = (
  let xs = sorted_list_of_set (X :: (_ :: {finite, linorder}) set) in
  (least_max_arg_max_list f (hd xs, f (hd xs)) (tl xs)))"

lemma least_arg_max_enum_correct: 
  assumes "X \<noteq> {}"
  shows "
  (least_arg_max_enum (f :: _ \<Rightarrow> (_ :: linorder)) X) = (LEAST x. is_arg_max f (\<lambda>x. x \<in> X) x)"
proof -
  have *: "xs \<noteq> [] \<Longrightarrow> (x = hd xs \<or> x \<in> set (tl xs)) \<longleftrightarrow> x \<in> set xs" for x xs
    using list.set_sel list.exhaust_sel set_ConsD by metis
  thus ?thesis
    unfolding least_arg_max_enum_def
    using  assms
    by (auto simp: Let_def fst_least_max_arg_max_list *)
qed

lemma least_max_arg_max_enum_correct1: 
  assumes "X \<noteq> {}" 
  shows "fst (least_max_arg_max_enum (f :: _ \<Rightarrow> (_ :: linorder)) X) = (LEAST x. is_arg_max f (\<lambda>x. x \<in> X) x)"
proof -
  have *: "xs \<noteq> [] \<Longrightarrow> (x = hd xs \<or> x \<in> set (tl xs)) \<longleftrightarrow> x \<in> set xs" for x xs
    using list.set_sel list.exhaust_sel set_ConsD by metis
  thus ?thesis
    using assms
    by (auto simp: least_max_arg_max_enum_def Let_def fst_least_max_arg_max_list *)
qed

lemma least_max_arg_max_enum_correct2: 
  assumes "X \<noteq> {}"
  shows "snd (least_max_arg_max_enum (f :: _ \<Rightarrow> (_ :: linorder)) X) = (MAX x \<in> X. f x)"
proof -
  have *: "xs \<noteq> [] \<Longrightarrow> insert (hd xs) (set (tl xs)) = set xs" for xs
    using list.exhaust_sel list.simps(15)
    by metis
  show ?thesis
    using assms
    by (auto simp: least_max_arg_max_enum_def Let_def snd_least_max_arg_max_list *)
qed

subsection \<open>Functions as Vectors\<close>
typedef ('a, 'b) Fun = "UNIV :: ('a \<Rightarrow> 'b) set"
  by blast

setup_lifting type_definition_Fun

lift_definition to_Fun :: "('a \<Rightarrow> 'b) \<Rightarrow> ('a, 'b) Fun" is id.

definition "fun_to_vec (v :: ('a::finite, 'b) Fun) = vec_lambda (Rep_Fun v)"

lift_definition vec_to_fun :: "'b^'a \<Rightarrow> ('a, 'b) Fun" is vec_nth.

lemma Fun_inverse[simp]: "Rep_Fun (Abs_Fun f) = f"
  using Abs_Fun_inverse by auto

lift_definition zero_Fun :: "('a, 'b::zero) Fun" is 0.

code_datatype vec_to_fun

lemmas vec_to_fun.rep_eq[code]

instantiation Fun :: (enum, equal) equal
begin
definition "equal_Fun (f :: ('a::enum, 'b::equal) Fun) g =  (Rep_Fun f = Rep_Fun g)"
instance 
  by standard (auto simp: equal_Fun_def Rep_Fun_inject)
end

subsection \<open>Bounded Functions as Vectors\<close>
lemma Bfun_inverse_fin[simp]: "apply_bfun (Bfun (f :: 'c :: finite \<Rightarrow> _)) = f"
  using finite by (fastforce intro!: Bfun_inverse simp: bfun_def)

definition "bfun_to_vec (v :: ('a::finite) \<Rightarrow>\<^sub>b ('b::metric_space)) = vec_lambda v"
definition "vec_to_bfun v = Bfun (vec_nth v)"

code_datatype vec_to_bfun

lemma apply_bfun_vec_to_bfun[code]: "apply_bfun (vec_to_bfun f) x = f $ x"
  by (auto simp: vec_to_bfun_def)

lemma [code]: "0 = vec_to_bfun 0"
  by (auto simp: vec_to_bfun_def)

subsection \<open>IArrays with Lengths in the Type\<close>

typedef ('s :: mod_type, 'a) iarray_type = "{arr :: 'a iarray. IArray.length arr = CARD('s)}"
  using someI_ex[OF Ex_list_of_length]
  by (auto intro!: exI[of _ "IArray (SOME xs. length xs = CARD('s))"])

setup_lifting type_definition_iarray_type

lift_definition fun_to_iarray_t :: "('s::{mod_type} \<Rightarrow> 'a) \<Rightarrow> ('s, 'a) iarray_type" is "\<lambda>f. IArray.of_fun (\<lambda>s. f (from_nat s)) (CARD('s))"
  by auto

lift_definition iarray_t_sub :: "('s::mod_type, 'a) iarray_type \<Rightarrow> 's \<Rightarrow> 'a" is "\<lambda>v x. IArray.sub v (to_nat x)".

lift_definition iarray_to_vec :: "('s, 'a) iarray_type \<Rightarrow> 'a^'s::{mod_type, finite}" 
  is "\<lambda>v. (\<chi> s. IArray.sub v (to_nat s))".

lift_definition vec_to_iarray :: "'a^'s::{mod_type, finite} \<Rightarrow> ('s, 'a) iarray_type" 
  is "\<lambda>v. IArray.of_fun (\<lambda>s. v $ ((from_nat s) :: 's)) (CARD('s))"
  by auto

lemma length_iarray_type [simp]: "length (IArray.list_of (Rep_iarray_type (v:: ('s::{mod_type}, 'a) iarray_type))) = CARD('s)"
  using Rep_iarray_type by auto

lemma iarray_t_eq_iff: "(v = w) = (\<forall>x. iarray_t_sub v x = iarray_t_sub w x)"
  unfolding iarray_t_sub.rep_eq IArray.sub_def
  by (metis Rep_iarray_type_inject iarray_exhaust2 length_iarray_type list_eq_iff_nth_eq to_nat_from_nat_id)

lemma iarray_to_vec_inv: "iarray_to_vec (vec_to_iarray v) = v"
  by (auto simp: to_nat_less_card iarray_to_vec.rep_eq vec_to_iarray.rep_eq vec_eq_iff)

lemma vec_to_iarray_inv: "vec_to_iarray (iarray_to_vec v) = v"
  by (auto simp: to_nat_less_card iarray_to_vec.rep_eq vec_to_iarray.rep_eq iarray_t_eq_iff iarray_t_sub.rep_eq)

code_datatype iarray_to_vec

lemma vec_nth_iarray_to_vec[code]: "vec_nth (iarray_to_vec v) x = iarray_t_sub v x"
  by (auto simp: iarray_to_vec.rep_eq iarray_t_sub.rep_eq)

lemma vec_lambda_iarray_t[code]: "vec_lambda v = iarray_to_vec (fun_to_iarray_t v)"
  by (auto simp: iarray_to_vec.rep_eq fun_to_iarray_t.rep_eq to_nat_less_card)

lemma zero_iarray[code]: "0 = iarray_to_vec (fun_to_iarray_t 0)"
  by (auto simp: iarray_to_vec.rep_eq fun_to_iarray_t.rep_eq to_nat_less_card vec_eq_iff)

subsection \<open>Value Iteration\<close>

locale vi_code = 
  MDP_ord A K r l for A :: "'s::mod_type \<Rightarrow> ('a::{finite, wellorder}) set" 
  and K :: "('s::{finite, mod_type} \<times> 'a::{finite, wellorder}) \<Rightarrow> 's pmf" and r l
begin
definition "vi_test (v::'s\<Rightarrow>\<^sub>b real) v' eps = 2 * l * dist v v'"

partial_function (tailrec) value_iteration_partial where [code]: "value_iteration_partial eps v = 
  (let v' = \<L>\<^sub>b v in
  (if 2 * l * dist v v' < eps * (1 - l) then v' else (value_iteration_partial eps v')))"

lemma vi_eq_partial: "eps > 0 \<Longrightarrow> value_iteration_partial eps v = value_iteration eps v"
proof (induction eps v rule: value_iteration.induct)
  case (1 eps v)
  then show ?case
    by (auto simp: Let_def value_iteration.simps value_iteration_partial.simps)
qed

definition "L_det d = L (mk_dec_det d)" 

lemma code_L_det [code]: "L_det d (vec_to_bfun v) = vec_to_bfun (\<chi> s. L\<^sub>a (d s) (vec_nth v) s)"
  by (auto simp: L_det_def vec_to_bfun_def L_eq_L\<^sub>a_det)

lemma code_\<L>\<^sub>b [code]: "\<L>\<^sub>b (vec_to_bfun v) = vec_to_bfun (\<chi> s. (MAX a \<in> A s. r (s, a) + l * measure_pmf.expectation (K (s, a)) (vec_nth v)))"
  by (auto simp: vec_to_bfun_def \<L>\<^sub>b_fin_eq_det A_ne cSup_eq_Max)

lemma code_value_iteration[code]: "value_iteration eps (vec_to_bfun v) = 
  (if eps \<le> 0 then \<L>\<^sub>b (vec_to_bfun v) else value_iteration_partial eps (vec_to_bfun v))"
  by (simp add: value_iteration.simps vi_eq_partial)

lift_definition find_policy_impl :: "('s \<Rightarrow>\<^sub>b real) \<Rightarrow> ('s, 'a) Fun" is "\<lambda>v. find_policy' v".
lemma code_find_policy_impl: "find_policy_impl v = vec_to_fun (\<chi> s. (LEAST x. x \<in> opt_acts v s))" 
  by (auto simp: vec_to_fun_def find_policy_impl_def find_policy'_def Abs_Fun_inject)

lemma code_find_policy_impl_opt[code]: "find_policy_impl v = vec_to_fun (\<chi> s. least_arg_max_enum (\<lambda>a. L\<^sub>a a v s) (A s))" 
  by (auto simp: is_opt_act_def code_find_policy_impl least_arg_max_enum_correct[OF A_ne])

lemma code_vi_policy'[code]: "vi_policy' eps v = Rep_Fun (find_policy_impl (value_iteration eps v))" 
  unfolding vi_policy'_def find_policy_impl_def by auto

subsection \<open>Policy Iteration\<close>

partial_function (tailrec) policy_iteration_partial where [code]: "policy_iteration_partial d = 
  (let d' = policy_step d in if d = d' then d else policy_iteration_partial d')"

lemma pi_eq_partial: "d \<in> D\<^sub>D \<Longrightarrow> policy_iteration_partial d = policy_iteration d"
proof (induction d rule: policy_iteration.induct)
  case (1 d)
  then show ?case
    by (auto simp: Let_def is_dec_det_pi policy_step_def policy_iteration_partial.simps)
qed

definition "P_mat d = (\<chi> i j. pmf (K (i, Rep_Fun d i)) j)"

definition "r_vec' d = (\<chi> i. r(i, Rep_Fun d i))"

lift_definition policy_eval' :: "('s::{mod_type, finite}, 'a) Fun \<Rightarrow> ('s \<Rightarrow>\<^sub>b real)" is "policy_eval".

lemma mat_eq_blinfun: "mat 1 - l *\<^sub>R (P_mat (vec_to_fun d)) = blinfun_to_matrix (id_blinfun - l *\<^sub>R \<P>\<^sub>1 (mk_dec_det (vec_nth d)))"
  unfolding blinfun_to_matrix_diff blinfun_to_matrix_id blinfun_to_matrix_scaleR
  unfolding blinfun_to_matrix_def P_mat_def \<P>\<^sub>1.rep_eq K_st_def push_exp_def matrix_def axis_def vec_to_fun_def
  by (auto simp: if_distrib mk_dec_det_def integral_measure_pmf[of UNIV]  pmf_expectation_bind[of UNIV] pmf_bind cong: if_cong)

lemma \<nu>\<^sub>b_vec: "policy_eval' (vec_to_fun d) = vec_to_bfun (matrix_inv (mat 1 - l *\<^sub>R (P_mat (vec_to_fun d))) *v (r_vec' (vec_to_fun d)))"
proof -
  let ?d = "Rep_Fun (vec_to_fun d)"
  have "vec_to_bfun (matrix_inv (mat 1 - l *\<^sub>R (P_mat (vec_to_fun d))) *v (r_vec' (vec_to_fun d))) = matrix_to_blinfun (matrix_inv (mat 1 - l *\<^sub>R (P_mat (vec_to_fun d)))) (vec_to_bfun (r_vec' (vec_to_fun d)))"
    by (auto simp: matrix_to_blinfun_mult vec_to_bfun_def r_vec'_def)
  also have "\<dots> = matrix_to_blinfun (matrix_inv (blinfun_to_matrix (id_blinfun - l *\<^sub>R \<P>\<^sub>1 (mk_dec_det ?d)))) (r_dec\<^sub>b (mk_dec_det ?d))"
    unfolding mat_eq_blinfun
    by (auto simp:  r_vec'_def vec_to_bfun_def vec_lambda_inverse r_dec\<^sub>b_def vec_to_fun_def)
  also have "\<dots> = inv\<^sub>L (id_blinfun - l *\<^sub>R \<P>\<^sub>1 (mk_dec_det ?d)) (r_dec\<^sub>b (mk_dec_det ?d))"
    by (auto simp: blinfun_to_matrix_inverse(2)[symmetric] invertible\<^sub>L_inf_sum matrix_to_blinfun_inv)
  finally have "vec_to_bfun (matrix_inv (mat 1 - l *\<^sub>R (P_mat (vec_to_fun d))) *v (r_vec' (vec_to_fun d))) = inv\<^sub>L (id_blinfun - l *\<^sub>R \<P>\<^sub>1 (mk_dec_det ?d)) (r_dec\<^sub>b (mk_dec_det ?d))".
  thus ?thesis
    by (auto simp: \<nu>_stationary policy_eval'.rep_eq policy_eval_def inv\<^sub>L_inf_sum blincomp_scaleR_right)
qed

lemma \<nu>\<^sub>b_vec_opt[code]: "policy_eval' (vec_to_fun d) = vec_to_bfun (Matrix_To_IArray.iarray_to_vec (Matrix_To_IArray.vec_to_iarray ((fst (Gauss_Jordan_PA ((mat 1 - l *\<^sub>R (P_mat (vec_to_fun d)))))) *v (r_vec' (vec_to_fun d)))))"
  using \<nu>\<^sub>b_vec
  by (auto simp: mat_eq_blinfun matrix_inv_Gauss_Jordan_PA blinfun_to_matrix_inverse(1) invertible\<^sub>L_inf_sum iarray_to_vec_vec_to_iarray)

lift_definition policy_improvement' :: "('s, 'a) Fun \<Rightarrow> ('s \<Rightarrow>\<^sub>b real) \<Rightarrow> ('s, 'a) Fun" 
  is policy_improvement.

lemma [code]: "policy_improvement' (vec_to_fun d) v = vec_to_fun (\<chi> s. (if is_arg_max (\<lambda>a. L\<^sub>a a v s) (\<lambda>a. a \<in> A s) (d $ s) then d $ s else LEAST x. is_arg_max (\<lambda>a. L\<^sub>a a v s) (\<lambda>a. a \<in> A s) x))"
  by (auto simp: is_opt_act_def policy_improvement'_def vec_to_fun_def vec_lambda_inverse policy_improvement_def Abs_Fun_inject)

lift_definition policy_step' :: "('s, 'a) Fun \<Rightarrow> ('s, 'a) Fun" 
  is policy_step.

lemma [code]: "policy_step' d = policy_improvement' d (policy_eval' d)"
  by (auto simp: policy_step'_def policy_step_def policy_improvement'_def policy_eval'_def apply_bfun_inverse)

lift_definition policy_iteration_partial' :: "('s, 'a) Fun \<Rightarrow> ('s, 'a) Fun" 
  is policy_iteration_partial.

lemma [code]: "policy_iteration_partial' d = (let d' = policy_step' d in if d = d' then d else policy_iteration_partial' d')"
  by (auto simp: policy_iteration_partial'.rep_eq policy_step'.rep_eq Let_def policy_iteration_partial.simps Rep_Fun_inject[symmetric])

lift_definition policy_iteration' :: "('s, 'a) Fun \<Rightarrow> ('s, 'a) Fun" is policy_iteration.

lemma code_policy_iteration'[code]: "policy_iteration' d =
  (if Rep_Fun d \<notin> D\<^sub>D then d else  (policy_iteration_partial' d))"
  by transfer (auto simp: pi_eq_partial)

lemma code_policy_iteration[code]: "policy_iteration d = Rep_Fun (policy_iteration' (vec_to_fun (vec_lambda d)))"
  by (auto simp add: vec_lambda_inverse policy_iteration'.rep_eq vec_to_fun_def)

subsection \<open>Gauss-Seidel Iteration\<close>

partial_function (tailrec) gs_iteration_partial where
  [code]: "gs_iteration_partial eps v = (
  let v' = (GS_rec_fun\<^sub>b v) in 
  (if 2 * l * dist v v' < eps * (1 - l) then v' else gs_iteration_partial eps v'))"

lemma gs_iteration_partial_eq: "eps > 0 \<Longrightarrow> gs_iteration_partial eps v = gs_iteration eps v"
  by (induction eps v rule: gs_iteration.induct) (auto simp: gs_iteration_partial.simps Let_def gs_iteration.simps)

lemma gs_iteration_code_opt[code]: "gs_iteration eps v = (if eps \<le> 0 then GS_rec_fun\<^sub>b v else gs_iteration_partial eps v)"
  by (auto simp: gs_iteration_partial_eq gs_iteration.simps)

definition "vec_upd v i x = (\<chi> j. if i = j then x else v $ j)"

lemma GS_rec_eq_fold: "GS_rec v = foldl (\<lambda>v s. (vec_upd v s (GS_iter_max v s))) v (sorted_list_of_set UNIV)"
proof -
  have "vec_lambda (foldl (\<lambda>v s. v(s := GS_rec_iter v s)) (($) v) xs) = foldl (\<lambda>v s. vec_upd v s (GS_iter_max v s)) v xs" for xs
  proof (induction xs arbitrary: v)
    case (Cons a xs)
    show ?case
      by (auto simp: vec_upd_def[of v] Cons[symmetric] eq_commute GS_rec_iter_eq_iter_max cong: if_cong)
  qed auto
  thus ?thesis
    unfolding GS_rec_def GS_rec_fun_code'
    by auto
qed

lemma GS_rec_fun_code''''[code]: "GS_rec_fun\<^sub>b (vec_to_bfun v) = vec_to_bfun (foldl (\<lambda>v s. (vec_upd v s (GS_iter_max v s))) v (sorted_list_of_set UNIV))"
  by (auto simp add:  GS_rec_eq_fold[symmetric] GS_rec_eq_elem GS_rec_fun\<^sub>b.rep_eq vec_to_bfun_def)

lemma GS_iter_max_code [code]: "GS_iter_max v s = (MAX a \<in> A s. GS_iter a v s)"
  using A_ne
  by (auto simp: GS_iter_max_def cSup_eq_Max)

lift_definition opt_policy_gs'' :: "('s \<Rightarrow>\<^sub>b real) \<Rightarrow> ('s, 'a) Fun" is opt_policy_gs.

declare opt_policy_gs''.rep_eq[symmetric, code]

lemma GS_rec_am_code'_prod: "GS_rec_am_code' v d = 
  (\<lambda>s'. (
    let (v', d') = foldl (\<lambda>(v,d) s. (v(s := (GS_iter_max (vec_lambda v) s)),  d(s := GS_iter_arg_max (vec_lambda v) s))) (vec_nth v, d) (sorted_list_of_set UNIV)
    in (v' s', d' s')))"
proof -
  have 1: "(\<lambda>x. (f x, g x))(y := (z, w)) = (\<lambda>x. ((f(y := z)) x, (g(y := w)) x))" for f g y z w
    by auto
  have 2: "(($) f)(a := y) = ($) (vec_lambda ((vec_nth f)(a := y)))" for f a y
    by auto
  have "foldl (\<lambda>vd s. vd(s := (GS_iter_max (\<chi> s. fst (vd s)) s, GS_iter_arg_max (\<chi> s. fst (vd s)) s))) (\<lambda>s. (v $ s, d s)) xs =
    (\<lambda>s'. let (v', d') = foldl (\<lambda>(v, d) s. (v(s := GS_iter_max (vec_lambda v) s), d(s := GS_iter_arg_max (vec_lambda v) s))) (($) v, d) xs in (v' s', d' s'))" for xs
  proof (induction xs arbitrary: v d)
    case Nil
    then show ?case by auto
  next
    case (Cons a xs)
    show ?case
      by (simp add: 1 Cons.IH[of "(vec_lambda ((($) v)(a := GS_iter_max v a)))", unfolded 2[symmetric]] del: fun_upd_apply)
  qed
  thus ?thesis
    unfolding GS_rec_am_code'_def by blast
qed


lemma code_GS_rec_am_arr_opt[code]: "opt_policy_gs'' (vec_to_bfun v) = vec_to_fun ((snd (foldl (\<lambda>(v, d) s.
  let (am, m) = least_max_arg_max_enum (\<lambda>a. r (s, a) + l * (\<Sum>s' \<in> UNIV. pmf (K (s,a)) s' * v $ s')) (A s) in
  (vec_upd v s m, vec_upd d s am)) 
  (v, (\<chi> s. (least_enum (\<lambda>a. a \<in> A s)))) (sorted_list_of_set UNIV))))"
proof -
  have 1: "opt_policy_gs'' v' = Abs_Fun (opt_policy_gs v')" for v'
    by (simp add: opt_policy_gs''.abs_eq)
  have 2: "opt_policy_gs (vec_to_bfun v) = opt_policy_gs' d v" for v d
    by (metis Bfun_inverse_fin opt_policy_gs_eq' vec_lambda_eta vec_to_bfun_def)
  have 3: "opt_policy_gs' d v = (\<lambda>s. snd (GS_rec_am_code v d s))" for d
    by (simp add: GS_rec_am_code_eq)
  have 4: "GS_rec_am_code v d = (\<lambda>s'. let (v', d') = foldl (\<lambda>(v, d) s. (v(s := GS_iter_max (vec_lambda v) s), d(s := GS_iter_arg_max (vec_lambda v) s))) (($) v, d) (sorted_list_of_set UNIV) in (v' s', d' s'))" for d s v
    using GS_rec_am_code' GS_rec_am_code'_prod by presburger
  have 5: "foldl (\<lambda>(v, d) s. (v(s := GS_iter_max (vec_lambda v) s), d(s := GS_iter_arg_max (vec_lambda v) s))) (($) v, ($) d) xs = 
      (let (v', d') = foldl (\<lambda>(v, d) s. (vec_upd v s (GS_iter_max v s), vec_upd d s (GS_iter_arg_max v s))) (v, d) xs in (vec_nth v', vec_nth d'))" for d v xs
  proof (induction xs arbitrary: d v)
    case Nil
    then show ?case by auto
  next
    case (Cons a xs)
    show ?case
      unfolding  vec_lambda_inverse Let_def
      using Cons[symmetric, unfolded Let_def]
      by simp (auto simp: vec_lambda_inverse vec_upd_def Let_def eq_commute cong: if_cong)
  qed
  have 6: "opt_policy_gs'' (vec_to_bfun v) = vec_to_fun (snd (foldl (\<lambda>(v, d) s. (vec_upd v s (GS_iter_max v s), vec_upd d s (GS_iter_arg_max v s))) (v, d) (sorted_list_of_set UNIV)))" for d
    unfolding 1
    unfolding 2[of _ "Rep_Fun (vec_to_fun d)"]
    unfolding 3
    unfolding 4
    using 5
    by (auto simp: Let_def case_prod_beta vec_to_fun_def)
  show ?thesis
    unfolding Let_def case_prod_beta
    unfolding least_max_arg_max_enum_correct1[OF A_ne]
    using least_max_arg_max_enum_correct2[OF A_ne]
    unfolding least_max_arg_max_enum_correct2[OF A_ne]
    using 6 fin_actions A_ne 
    unfolding GS_iter_max_def GS_iter_def GS_iter_arg_max_def 
    by (auto simp: cSup_eq_Max split_beta')
qed


subsection \<open>Modified Policy Iteration\<close>

sublocale MDP_MPI A K r l "\<lambda>X. Least (\<lambda>x. x \<in> X)"
  using MDP_act_axioms MDP_reward_axioms
  by unfold_locales auto


definition "d0 s = (LEAST a. a \<in> A s)" 
lift_definition d0' :: "('s, 'a) Fun" is d0.

lemma d0_dec_det: "is_dec_det d0"
  using A_ne unfolding d0_def is_dec_det_def
  by simp

lemma v0_code[code]: "v0_mpi\<^sub>b = vec_to_bfun (\<chi> s. r_min / (1 - l))"
  by (auto simp: v0_mpi\<^sub>b_def v0_mpi_def vec_to_bfun_def )

lemma d0'_code[code]: "d0' = vec_to_fun (\<chi> s. (LEAST a. a \<in> A s))"
  by (auto simp: d0'.rep_eq d0_def Rep_Fun_inject[symmetric] vec_to_fun_def)

lemma step_value_code[code]: "L_pow v d m = (L_det d ^^ Suc m) v"
  unfolding L_pow_def L_det_def
  by auto

partial_function  (tailrec) mpi_partial where [code]: "mpi_partial eps d v m = 
  (let d' = policy_improvement d v in (
    if 2 * l * dist v (\<L>\<^sub>b v) <  eps * (1 - l)
    then (d', v) 
    else mpi_partial eps d' (L_pow v d' (m 0 v)) (\<lambda>n. m (Suc n))))"

lemma mpi_partial_eq_algo:
  assumes "eps > 0" "d \<in> D\<^sub>D" "v \<le> \<L>\<^sub>b v"
  shows "mpi_partial eps d v m = mpi_algo eps d v m"
proof -
  have "mpi_algo_dom eps (d,v,m)"
    using assms termination_mpi_algo by blast
  thus ?thesis
    by (induction rule: mpi_algo.pinduct) (auto simp: Let_def mpi_algo.psimps mpi_partial.simps)
qed

lift_definition mpi_partial' :: "real \<Rightarrow> ('s, 'a) Fun \<Rightarrow> ('s \<Rightarrow>\<^sub>b real) \<Rightarrow> (nat \<Rightarrow> ('s \<Rightarrow>\<^sub>b real) \<Rightarrow> nat)
            \<Rightarrow> ('s, 'a) Fun \<times> ('s \<Rightarrow>\<^sub>b real)" is mpi_partial.

lemma mpi_partial'_code[code]: "mpi_partial' eps d v m =
  (let d' = policy_improvement' d v in (
    if 2 * l * dist v (\<L>\<^sub>b v) <  eps * (1 - l)
    then (d', v) 
    else mpi_partial' eps d' (L_pow v (Rep_Fun d') (m 0 v)) (\<lambda>n. m (Suc n))))"
  by (auto simp: mpi_partial'_def mpi_partial.simps Let_def policy_improvement'_def)

lemma r_min_code[code_unfold]: "r_min = (MIN s. MIN a. r(s,a))"
  by (auto simp: cInf_eq_Min)

lemma mpi_user_code[code]: "mpi_user eps m = 
  (if eps \<le> 0 then undefined else 
    let (d, v) = mpi_partial' eps d0' v0_mpi\<^sub>b m in (Rep_Fun d, v))"
  unfolding mpi_user_def case_prod_beta mpi_partial'_def
  using mpi_partial_eq_algo A_ne v0_mpi\<^sub>b_le_\<L>\<^sub>b d0_dec_det
  by (auto simp: d0'.rep_eq d0_def[symmetric])
end

subsection \<open>Auxiliary Equations\<close>
lemma [code_unfold]: "dist (f::'a::finite \<Rightarrow>\<^sub>b 'b::metric_space) g = (MAX a. dist (apply_bfun f a) (g a))" 
  by (auto simp: dist_bfun_def cSup_eq_Max)

lemma member_code[code del]: "x \<in> List.coset xs \<longleftrightarrow> \<not> List.member xs x"
  by (auto simp: in_set_member)

lemma [code]: "iarray_to_vec v + iarray_to_vec u = (Matrix_To_IArray.iarray_to_vec (Rep_iarray_type v + Rep_iarray_type u))"
  by (metis (no_types, lifting) Matrix_To_IArray.vec_to_iarray_def iarray_to_vec_vec_to_iarray vec_to_iarray.rep_eq vec_to_iarray_inv vec_to_iarray_plus)

lemma [code]: "iarray_to_vec v - iarray_to_vec u = (Matrix_To_IArray.iarray_to_vec (Rep_iarray_type v - Rep_iarray_type u))"
  unfolding minus_iarray_def Matrix_To_IArray.iarray_to_vec_def iarray_to_vec_def
  by (auto simp: vec_eq_iff to_nat_less_card)

lemma matrix_to_iarray_minus[code_unfold]: "matrix_to_iarray (A - B) = matrix_to_iarray A - matrix_to_iarray B"
  unfolding matrix_to_iarray_def o_def minus_iarray_def Matrix_To_IArray.vec_to_iarray_def
  by simp

declare matrix_to_iarray_fst_Gauss_Jordan_PA[code_unfold] 

end