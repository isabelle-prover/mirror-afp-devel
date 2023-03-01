theory PI_Code
  imports
    "../Policy_Iteration_Fin" 
    "HOL-Library.Code_Target_Numeral"
    "Jordan_Normal_Form.Matrix_Impl"
    Code_Setup
begin
context MDP_Code begin

definition "policy_eval_code d = 
  inverse_mat (1\<^sub>m states - 
  l \<cdot>\<^sub>m (Matrix.mat states states (\<lambda>(s, s'). pmf (MDP_K (s, d_lookup' d s)) s'))) *\<^sub>v 
  (vec states (\<lambda>i. MDP_r (i, d_lookup' d i)))"

lemma d_lookup'_eq_map_to_fun: "D_Map.invar d \<Longrightarrow> s \<in> D_Map.keys d \<Longrightarrow> d_lookup' d s = D_Map.map_to_fun d s"
  using D_Map.lookup_None_set_inorder
  by (auto simp: D_Map.map_to_fun_def d_lookup'_def split: option.splits)

lemma policy_eval_correct: 
  assumes "D_Map.keys d = {0..<states}" "D_Map.invar d" "s < states"
  shows "policy_eval_code d $v s = MDP.\<nu>\<^sub>b (MDP.mk_stationary_det (D_Map.map_to_fun d)) s"
  unfolding policy_eval_code_def MDP.vec_\<nu>\<^sub>b''[OF assms(3)]
  using assms d_lookup'_eq_map_to_fun
  by (auto cong: vec_cong MDP.mat_cong)

definition "transition_vecs =
  Matrix.vec states (\<lambda>s. M.from_list (map (\<lambda>(a, _, ps). (a, 
    Matrix.vec states (\<lambda>s'. \<Sum>x \<leftarrow> ps. if fst x = s' then snd x else 0))) (a_inorder (s_lookup mdp s))))"

lemma transition_vecs_correct:
  assumes "s < states" "a \<in> MDP_A s" "s' < states"
  shows "M.lookup' (transition_vecs $v s) a $v s' = pmf (MDP_K (s,a)) s'"
proof -
  have *: "Matrix.vec states (\<lambda>s'. \<Sum>x\<leftarrow>snd (a_lookup' (s_lookup mdp s) a). if fst x = s' then snd x else 0) $v s' = pmf (pmf_of_list (snd (a_lookup' (s_lookup mdp s) a))) s'"
    by (auto simp: pmf_pmf_of_list assms pmf_of_list_wf_mdp sum_list_map_filter')
  have **: "
  M.lookup' (M.from_list (map (\<lambda>(a, _, ps). (a, Matrix.vec states (\<lambda>s'. \<Sum>x\<leftarrow>ps. if fst x = s' then snd x else 0))) (a_inorder (s_lookup mdp s)))) a $v s' = 
  pmf (pmf_of_list (snd (a_lookup' (s_lookup mdp s) a))) s'"
    unfolding *[symmetric]
    using a_map_entries_lookup[OF assms(1,2)] A_Map.distinct_inorder invar_s_lookup[OF assms(1)]
    by (subst M.lookup'_from_list_distinct) (force simp: comp_def case_prod_beta A_Map.entries_def[symmetric] intro!: imageI)+
  show ?thesis
    unfolding transition_vecs_def MDP_K_def
    using assms a_lookup_None_notin_A sa_lookup_eq(2) snd_sa_lookup'_eq 
    by (auto split: option.splits simp: **)
qed

lemma policy_eval_code: "policy_eval_code d =
  the (mat_inverse ((1\<^sub>m states) - 
  l \<cdot>\<^sub>m (Matrix.mat states states (\<lambda>(s, s'). pmf (MDP_K (s, d_lookup' d s)) s')))) *\<^sub>v 
  (vec states (\<lambda>i. MDP_r (i, d_lookup' d i)))"
  unfolding policy_eval_code_def
  by (subst mat_inverse_eq_inverse_mat) (auto simp: MDP.invertible_\<nu>\<^sub>b_mat')

definition "one_st = 1\<^sub>m states"
definition "k_mat d = Matrix.mat states states (\<lambda>(s, y). pmf (MDP_K (s, d_lookup' d s)) y)"

definition "k_mat' d m = (
  Matrix.mat_of_row_fun states states (\<lambda>i. M.lookup' (m $v i) (d_lookup' d i)))"

lemma invertible_imp_inv_ex: "invertible_mat m \<Longrightarrow> \<exists>x\<in>carrier_mat (dim_row m) (dim_row m). x * m = 1\<^sub>m (dim_row m) \<and> m * x = 1\<^sub>m (dim_row m)"
  by (metis carrier_matD(1) inverse_mat_mult inverse_mats_def invertible_inverse_mats)

lemma policy_eval_code':
  fixes d
  defines "m \<equiv> (one_st - l \<cdot>\<^sub>m Matrix.mat states states (\<lambda>(s, y). pmf (MDP_K (s, d_lookup' d s)) y))"
  shows "policy_eval_code d = snd (gauss_jordan m (1\<^sub>m states)) *\<^sub>v (vec states (\<lambda>i. MDP_r (i, d_lookup' d i)))"
proof -
  have m: "m \<in> carrier_mat states states"
    using assms by fastforce
  hence "fst (gauss_jordan m (1\<^sub>m states)) = 1\<^sub>m states"
    using MDP.invertible_\<nu>\<^sub>b_mat'[of "d_lookup' d", unfolded m_def[symmetric] one_st_def[symmetric]]
    using m invertible_imp_inv_ex[of m]
    by (auto simp: ring_mat_simps Units_def intro!: gauss_jordan_inverse_other_direction[of _ _  states _ states])
  thus ?thesis
    unfolding policy_eval_code mat_inverse_def
    by (auto split: if_splits simp: one_st_def m_def case_prod_beta)
qed

lemma policy_eval_code''[code]:
  fixes d
  defines "m \<equiv> (one_st - l \<cdot>\<^sub>m ((k_mat d)))"
  shows "policy_eval_code d = snd (gauss_jordan m one_st) *\<^sub>v (vec states (\<lambda>i. MDP_r (i, d_lookup' d i)))"
  unfolding m_def policy_eval_code' k_mat_def one_st_def by (simp add: mat_code)

definition "policy_eval_code' d m = snd (gauss_jordan (one_st - l \<cdot>\<^sub>m ((k_mat' d m))) one_st) *\<^sub>v (vec states (\<lambda>i. MDP_r (i, d_lookup' d i)))"

lemma dim_policy_eval_code: "dim_vec (policy_eval_code d) = states"
  by (simp add: policy_eval_code_def MDP.invertible_\<nu>\<^sub>b_mat' inverse_mat_dims(2))

lemma policy_eval_correct': 
  assumes "D_Map.keys d = {0..<states}" "D_Map.invar d"
  shows "vec_to_bfun (policy_eval_code d) = MDP.\<nu>\<^sub>b (MDP.mk_stationary_det (D_Map.map_to_fun d))"
  using policy_eval_correct assms dim_policy_eval_code MDP.\<nu>\<^sub>b_zero_notin
  by (auto simp: vec_to_bfun.rep_eq)

(* todo, just never go downwards when choosing new actions in case of draw *)
definition "pi_find_policy_state_code_aux' d v s = (
  let (d', v') = find_policy_state_code_aux' v s in
  if L\<^sub>a_code (a_lookup' (s_lookup mdp s) d) v = v' then d else d')"

definition "pi_find_policy_code d v = 
 D_Map.from_list' (\<lambda>s. pi_find_policy_state_code_aux' (d_lookup' d s) v s) [0..<states]"

lemma vi_find_policy_code_invar: "D_Map.invar (pi_find_policy_code d v)"
  unfolding pi_find_policy_code_def by simp

lemma keys_vi_find_policy_code_aux_upt: "D_Map.keys (pi_find_policy_code d v) = {0..<states}"
  unfolding pi_find_policy_code_def by simp

lemma find_policy_state_code_aux'_in_acts:
  assumes "s < states" "v_len v = states" "v_invar v"
  shows "fst (find_policy_state_code_aux' v s) \<in> MDP_A s"
  using MDP.A_ne MDP.A_fin assms least_arg_max_prop[of "\<lambda>x. x \<in> MDP_A s"]
  by (fastforce simp: find_policy_state_code_aux'_eq')

lemma pi_find_policy_state_code_aux'_correct:
  assumes "s < states" "D_Map.invar d" "v_len v = states" "v_invar v" "D_Map.keys d = MDP.state_space" "d_lookup' d s \<in> MDP_A s"
  shows "pi_find_policy_state_code_aux' (d_lookup' d s) v s = MDP.policy_improvement (D_Map.map_to_fun d) (V_Map.map_to_bfun v) s"
proof (cases "is_arg_max (\<lambda>a. MDP.L\<^sub>a a (apply_bfun (V_Map.map_to_bfun v)) s) (\<lambda>a. a \<in> MDP_A s) (D_Map.map_to_fun d s)")
  case True
  hence aux: "L\<^sub>a_code (a_lookup' (s_lookup mdp s) (d_lookup' d s)) v = snd (find_policy_state_code_aux' v s)"
    using MDP.A_fin
    by (subst L_GS_code_correct') (fastforce intro!: Max_eqI[symmetric] simp: assms find_policy_state_code_aux'_eq' d_lookup'_eq_map_to_fun split: option.splits)+
  then show ?thesis
  proof -
    have "pi_find_policy_state_code_aux' (d_lookup' d s) v s = d_lookup' d s"
      unfolding pi_find_policy_state_code_aux'_def 
      by (simp add: aux case_prod_unfold)
    thus ?thesis
      using True
      by (fastforce simp: assms MDP.policy_improvement_def d_lookup'_eq_map_to_fun  split: option.splits)
  qed
next
  case False
  hence "L\<^sub>a_code (a_lookup' (s_lookup mdp s) (d_lookup' d s)) v < (MAX a \<in> MDP_A s. MDP.L\<^sub>a a (apply_bfun (V_Map.map_to_bfun v)) s)"
    using False assms by (auto simp: L_GS_code_correct' is_arg_max_linorder not_le map_to_fun_lookup Max_gr_iff)
  thus ?thesis
    unfolding pi_find_policy_state_code_aux'_def MDP.policy_improvement_def
    using False
    by (auto simp: assms find_policy_state_code_aux'_eq' least_arg_max_def MDP.is_opt_act_def)
qed

lemma pi_find_policy_code_correct:
  assumes "v_len v = states" "D_Map.keys d = MDP.state_space" "v_invar v" "D_Map.invar d" "\<And>s. s < states \<Longrightarrow> d_lookup' d s \<in> MDP_A s"
  shows "D_Map.map_to_fun ((pi_find_policy_code d v)) s = MDP.policy_improvement (D_Map.map_to_fun d) (V_Map.map_to_bfun v) s"
  using assms
proof (cases "s < states")
  case True
  then show ?thesis
    unfolding pi_find_policy_code_def
    by (simp add: assms pi_find_policy_state_code_aux'_correct  D_Map.map_to_fun_def)
next
  case False
  then show ?thesis
    using keys_vi_find_policy_code_aux_upt assms vi_find_policy_code_invar is_arg_max_const MDP.A_outside
    by (auto intro!: Least_equality simp: map_to_fun_notin MDP.policy_improvement_def MDP.is_opt_act_def)
qed

definition "eq_policy d1 d2 = (\<forall>x<states. d_lookup d1 x = d_lookup d2 x)"
definition "policy_step_code d = (
let v = policy_eval_code d in
  pi_find_policy_code d (V_Map.arr_tabulate (($v) v) states))"

definition "policy_step_code' d m = (
let v = policy_eval_code' d m in
  pi_find_policy_code d (V_Map.arr_tabulate (($v) v) states))"

partial_function (tailrec) PI_code_aux' where
  "PI_code_aux' d m = (
  let d' = policy_step_code' d m in
    if eq_policy d d'
    then d
    else PI_code_aux' d' m)"

partial_function (tailrec) PI_code_aux where
  "PI_code_aux d = (
  let d' = policy_step_code d in
    if eq_policy d d'
    then d
    else PI_code_aux d')"

lemma fold_policy_eval_update_eq: 
  assumes "s < states"  "D_Map.keys d = MDP.state_space" "D_Map.invar d"
  shows "v_lookup (V_Map.arr_tabulate (\<lambda>x. policy_eval_code d $v x) states) s = (MDP.policy_eval (D_Map.map_to_fun d) s)"
  using assms
  by (auto simp: v_lookup_fold policy_eval_correct MDP.policy_eval_def)

lemma fold_policy_eval_update_eq': 
  assumes "D_Map.keys d = MDP.state_space" "D_Map.invar d"
  shows "V_Map.map_to_bfun (V_Map.arr_tabulate (\<lambda>x. (policy_eval_code d $v x)) states) = 
  (MDP.policy_eval (D_Map.map_to_fun d))"
proof (rule bfun_eqI)
  fix s
  show "(V_Map.map_to_bfun (V_Map.arr_tabulate (($v) (policy_eval_code d)) states)) s = 
  (MDP.policy_eval (D_Map.map_to_fun d)) s"
  proof (cases "s < states")
    case True
    then show ?thesis
      by (auto simp: V_Map.map_to_bfun.rep_eq assms policy_eval_correct MDP.policy_eval_def)
  next
    case False
    then show ?thesis
      by (auto simp: MDP.policy_eval_def V_Map.map_to_bfun.rep_eq MDP.\<nu>\<^sub>b_zero_notin)
  qed
qed

lemmas PI_code_aux.simps[code]
lemmas PI_code_aux'.simps[code]

lemmas MDP.policy_iteration.simps[simp del]

definition "is_dec_det_code d \<longleftrightarrow> 
  D_Map.keys d = {0..<states} \<and> D_Map.invar d \<and> (\<forall>s \<in> set [0..<states]. a_lookup (s_lookup mdp s) (d_lookup' d s) \<noteq> None)"

lemma [code]: "is_dec_det_code d \<longleftrightarrow> 
  (map fst (d_inorder d)) = [0..<states] \<and> D_Map.invar d \<and> (\<forall>s \<in> set [0..<states]. a_lookup (s_lookup mdp s) (d_lookup' d s) \<noteq> None)"
proof -
  have "D_Map.invar d \<Longrightarrow> fst ` set (d_inorder d) = {0..<n} \<Longrightarrow> (map fst (d_inorder d)) = [0..<n]" for n
    by (simp add: D_Map.invar_def strict_sorted_equal)
  moreover have "D_Map.invar d \<Longrightarrow> map fst (d_inorder d) = [0..<n] \<Longrightarrow> fst ` set (d_inorder d) = {0..<n}" for n
    using image_set[of "fst" "d_inorder d"]
    by auto
  ultimately show ?thesis
    unfolding D_Map.keys_def is_dec_det_code_def
    by blast
qed

definition "PI_code d0 = (if \<not> is_dec_det_code d0 then d0 else PI_code_aux d0)"

lemma k_mat_eq': "is_dec_det_code d \<Longrightarrow> k_mat d = k_mat' d transition_vecs"
  unfolding k_mat_def k_mat'_def Matrix.mat_eq_iff
  by (auto simp:  is_dec_det_code_def intro!: transition_vecs_correct[symmetric] intro: a_lookup_some_in_A)

lemma policy_eval_code_eq': "is_dec_det_code d \<Longrightarrow> policy_eval_code d = policy_eval_code' d transition_vecs"
  unfolding policy_eval_code'' policy_eval_code'_def
  using k_mat_eq'
  by force

lemma policy_step_code_eq': "is_dec_det_code d \<Longrightarrow> policy_step_code d = policy_step_code' d transition_vecs"
  unfolding policy_step_code_def policy_step_code'_def 
  using policy_eval_code_eq' by presburger

lemma policy_step_code_correct:
  assumes "D_Map.keys d = MDP.state_space" "D_Map.invar d" "(\<And>s. s < states \<Longrightarrow> d_lookup' d s \<in> MDP_A s)"
  shows "D_Map.map_to_fun (policy_step_code d) = (MDP.policy_step (D_Map.map_to_fun d))"
  unfolding policy_step_code_def MDP.policy_step_def
  by (auto simp: fold_policy_eval_update_eq'  pi_find_policy_code_correct assms)

lemma PI_code_aux_correct_aux:
  assumes "D_Map.invar d" "D_Map.keys d = {0..<states}" "(\<And>s. s < states \<Longrightarrow> d_lookup' d s \<in> MDP_A s)"
  shows "D_Map.map_to_fun (PI_code_aux d) = MDP.policy_iteration (D_Map.map_to_fun d) 
    \<and> (is_dec_det_code d \<longrightarrow> PI_code_aux d = PI_code_aux' d transition_vecs)"
  using assms
proof (induction "(D_Map.map_to_fun d)" arbitrary: d rule: MDP.policy_iteration.induct)
  case 1
  show ?case
  proof (cases "eq_policy d (policy_step_code d)")
    case True
    hence *: "D_Map.map_to_fun d s = (MDP.policy_step (D_Map.map_to_fun d)) s" for s
    proof (cases "s < states")
      case True
      then show ?thesis
        using True vi_find_policy_code_invar 1 \<open>eq_policy d (policy_step_code d)\<close> 
        by (auto simp: D_Map.map_to_fun_def eq_policy_def policy_step_code_correct[symmetric] policy_step_code_def)
    next
      case False
      hence "MDP.policy_step (D_Map.map_to_fun d) s = 0"
        by (auto simp: 1 MDP.policy_improvement_def is_arg_max_linorder MDP.policy_step_def MDP_A_def map_to_fun_notin)
      then show ?thesis
        using 1 D_Map.lookup_some_set_key False 
        by (auto simp: D_Map.map_to_fun_def split: option.splits)
    qed
    have "D_Map.map_to_fun (PI_code_aux d) = D_Map.map_to_fun d"
      by (simp add: PI_code_aux.simps policy_step_code_correct True)
    thus ?thesis
      using * MDP.policy_iteration.simps[of "D_Map.map_to_fun d"] True
      by (fastforce simp: policy_step_code_eq' PI_code_aux'.simps[of d] PI_code_aux.simps[of d])
  next
    case False
    then obtain s where s: "s < states" "d_lookup d s \<noteq> d_lookup (policy_step_code d) s"
      unfolding eq_policy_def policy_step_code_def
      using 1(2,3) D_Map.lookup_notin_keys keys_vi_find_policy_code_aux_upt vi_find_policy_code_invar
      by (auto simp: d_lookup'_def)
    have invar_step: "D_Map.invar (policy_step_code d)"
      by (simp add: policy_step_code_def vi_find_policy_code_invar)
    have keys_step: "D_Map.keys (policy_step_code d) = D_Map.keys d"
      by (simp add: 1 keys_vi_find_policy_code_aux_upt policy_step_code_def)
    have *: "D_Map.map_to_fun d s \<noteq> (MDP.policy_step (D_Map.map_to_fun d)) s"
      using D_Map.lookup_in_keys[OF invar_step] D_Map.lookup_notin_keys[OF invar_step] s(2) keys_step invar_step 1(2-4)
      by (fastforce dest: D_Map.lookup_None_set_inorder[OF \<open>D_Map.invar d\<close>] D_Map.lookup_some_set_key[OF \<open>D_Map.invar d\<close>] 
          split: option.splits simp: policy_step_code_correct[symmetric] D_Map.map_to_fun_def)
    have **: "MDP.is_dec_det (D_Map.map_to_fun d)"
      using 1 by (auto simp: MDP.is_dec_det_def MDP_A_def map_to_fun_lookup map_to_fun_notin)
    have lookup': "s < states \<Longrightarrow> d_lookup' (policy_step_code d) s \<in> MDP_A s" for s
      using 1(2-4) keys_step invar_step MDP.is_dec_det_pi
      by (force simp: MDP.is_dec_det_def policy_step_code_correct d_lookup'_eq_map_to_fun MDP.policy_step_def)
    have "D_Map.map_to_fun (PI_code_aux d) = D_Map.map_to_fun (PI_code_aux (policy_step_code d))"
      by (simp add: PI_code_aux.simps policy_step_code_correct False)
    also have "\<dots> = MDP.policy_iteration (D_Map.map_to_fun (policy_step_code d))"
      using 1(2-4) * ** policy_step_code_correct lookup' invar_step keys_step 
      by (intro conjunct1[OF 1(1)]) (auto )
    also have "\<dots> = MDP.policy_iteration (MDP.policy_step (D_Map.map_to_fun d))"
      using 1 by (auto simp: policy_step_code_correct)
    finally have aux: "D_Map.map_to_fun (PI_code_aux d) = MDP.policy_iteration (D_Map.map_to_fun d)"
      unfolding  PI_code_aux.simps[of d] PI_code_aux'.simps[of d]
      using ** by (auto simp:  MDP.policy_iteration.simps)
    thus ?thesis
    proof -      
      have d: "is_dec_det_code d"
        unfolding is_dec_det_code_def
        using 1 a_lookup_None_notin_A
        by (metis atLeastLessThan_iff set_upt)
      hence "is_dec_det_code (policy_step_code d)"
        by (metis a_lookup_None_notin_A atLeastLessThan_iff invar_step is_dec_det_code_def keys_step lookup' set_upt)
      hence "PI_code_aux (policy_step_code d) = PI_code_aux' (policy_step_code d) transition_vecs"
        using * ** 1 invar_step keys_step lookup' policy_step_code_correct by metis
      hence "PI_code_aux d = PI_code_aux' d transition_vecs"
        unfolding  PI_code_aux.simps[of d] PI_code_aux'.simps[of d]
        using policy_step_code_eq'[OF d]
        by auto
      thus ?thesis
        using ** aux
        by fastforce
    qed
  qed
qed

lemma PI_code_correct:
  assumes "D_Map.invar d" "D_Map.keys d = MDP.state_space" "(\<And>s. s < states \<Longrightarrow> d_lookup' d s \<in> MDP_A s)"
  shows "D_Map.map_to_fun (PI_code d) = MDP.policy_iteration (D_Map.map_to_fun d)"
proof -
  have "is_dec_det_code d"
    unfolding is_dec_det_code_def
    using a_lookup_None_notin_A assms
    by (fastforce simp: not_Some_eq[symmetric])
  thus ?thesis
    using assms
    by (auto simp: PI_code_def conjunct1[OF PI_code_aux_correct_aux])
qed

lemma [code]: "PI_code d0 = (if \<not> is_dec_det_code d0 then d0 else PI_code_aux' d0 transition_vecs)"
  using conjunct2[OF PI_code_aux_correct_aux[of d0]]
  unfolding PI_code_def is_dec_det_code_def
  using a_lookup_some_in_A
  by force

definition "d0 = D_Map.from_list' (\<lambda>s. fst (hd (a_inorder (s_lookup mdp s)))) [0..<states]"

end

lemma inorder_empty: "Tree2.inorder am = [] \<Longrightarrow> am = \<langle>\<rangle>"
  using Tree2.inorder.elims by blast

global_interpretation PI_Code: MDP_Code
(* state map (transition system) *)
"IArray.sub" "\<lambda>n x arr. IArray ((IArray.list_of arr)[n:= x])" "IArray.length" "IArray" "IArray.list_of" "\<lambda>_. True"

(* action map *)
RBT_Set.empty RBT_Map.update RBT_Map.delete Lookup2.lookup Tree2.inorder rbt

"MDP.transitions (Rep_Valid_MDP mdp)" "MDP.states (Rep_Valid_MDP mdp)"

(* value map *)
starray_get "\<lambda>i x arr. starray_set arr i x" starray_length starray_of_list "\<lambda>arr. starray_foldr (\<lambda>x xs. x # xs) arr []" "\<lambda>_. True"

(* decision rule map *)
RBT_Set.empty RBT_Map.update RBT_Map.delete Lookup2.lookup Tree2.inorder rbt

"MDP.disc (Rep_Valid_MDP mdp)"
for mdp
defines PI_code = PI_Code.PI_code  
  and PI_code_aux = PI_Code.PI_code_aux
  and L\<^sub>a_code = PI_Code.L\<^sub>a_code
  and a_lookup' = PI_Code.a_lookup'
  and d_lookup' = PI_Code.d_lookup'
  and find_policy_state_code_aux' = PI_Code.find_policy_state_code_aux'
  and find_policy_state_code_aux = PI_Code.find_policy_state_code_aux
  and entries = M.entries
  and from_list' = M.from_list'
  and pi_find_policy_code = PI_Code.pi_find_policy_code
  and pi_find_policy_state_code_aux' = PI_Code.pi_find_policy_state_code_aux'
  and policy_eval_code = PI_Code.policy_eval_code
  and is_dec_det_code = PI_Code.is_dec_det_code
  and policy_step_code = PI_Code.policy_step_code
  and eq_policy = PI_Code.eq_policy
  and MDP_r = PI_Code.MDP_r
  and MDP_K = PI_Code.MDP_K
  and d0 = PI_Code.d0
  and k_mat = PI_Code.k_mat
  and one_st = PI_Code.one_st
  and arr_tabulate = starray_Array.arr_tabulate
  and transition_vecs = PI_Code.transition_vecs
  and M_from_list = M.from_list
  and M_lookup' = M.lookup'
  and M_keys = M.keys
  and M_invar = M.invar

and PI_code_aux' = PI_Code.PI_code_aux'
and policy_step_code' = PI_Code.policy_step_code'
and policy_eval_code' = PI_Code.policy_eval_code'
and k_mat' = PI_Code.k_mat'

  using Rep_Valid_MDP is_MDP_def
  by unfold_locales 
    (fastforce simp: Ball_set_list_all[symmetric] case_prod_beta pmf_of_list_wf_def is_MDP_def M.invar_def empty_def M.entries_def M.is_empty_def length_0_conv[symmetric])+

lemmas arr_tabulate_def[unfolded starray_Array.arr_tabulate_def, code]
lemmas entries_def[unfolded M.entries_def, code]
lemmas from_list'_def[unfolded M.from_list'_def, code]

lemmas M_from_list_def[unfolded M.from_list_def, code]
lemmas M_lookup'_def[unfolded M.lookup'_def, code]
lemmas M_keys_def[unfolded M.keys_def, code]
lemmas M_invar_def[unfolded M.invar_def, code]


lift_definition mat_of_row_fun_code :: "nat \<Rightarrow> nat \<Rightarrow> (nat \<Rightarrow> 'a vec_impl) \<Rightarrow> 'a mat_impl" is
  "\<lambda> nr nc f. (nr, nc, 
  let m = IArray.of_fun (\<lambda> i. snd (Rep_vec_impl (f i))) nr in
    if \<forall>i<nr. IArray.length (IArray.sub m i) = nc 
    then m else Code.abort (STR ''set_fold_cfc RBT_set: ccompare = None'')
    (\<lambda>_. IArray.of_fun (\<lambda> i. IArray.of_fun (\<lambda> j. vec_index_impl (f i) j) nc) nr))
  " by auto

lift_definition vec_to_vec_impl :: "'a vec \<Rightarrow> 'a vec_impl" is
  "\<lambda>v. vec_of_fun (dim_vec v) (($) v)".

lemma vec_impl_eqI: "snd (Rep_vec_impl v) = snd (Rep_vec_impl u) \<Longrightarrow> fst (Rep_vec_impl v) = fst (Rep_vec_impl u) \<Longrightarrow> v = u"
  by (meson Rep_vec_impl_inject prod_eq_iff)

lemma vec_impl_exhaust: "(\<And>v. P (Abs_vec_impl (IArray.length v, v))) \<Longrightarrow> P u"
  by (auto intro: Abs_vec_impl_induct)

lemma vec_to_vec_impl_code[code]: "vec_to_vec_impl (vec_impl v) = v"
proof - 
  have "vec_to_vec_impl (vec_impl (Abs_vec_impl (length v, IArray v))) = Abs_vec_impl (length v, IArray v)" for v
  proof -
    have "vec_to_vec_impl (vec_impl (Abs_vec_impl (length v, IArray v))) = vec_of_fun (length v) (($v) (vec_impl (Abs_vec_impl (length v, IArray v))))"
      unfolding vec_to_vec_impl.abs_eq 
      by (metis dim_vec_of_list vec_of_list vec_of_list_impl.abs_eq)
    also have "\<dots> = Abs_vec_impl (length v, IArray (map (($v) (Abs_vec (length v, Matrix.mk_vec (length v) ((!!) (IArray v))))) [0..<length v]))"
      by (subst vec_impl.abs_eq) (auto simp: eq_onp_same_args vec_of_fun_def )
    also have "\<dots> = Abs_vec_impl (length v, IArray (map (Matrix.mk_vec (length v) ((!!) (IArray v))) [0..<length v]))"
      by (subst vec_index.abs_eq) (auto simp: eq_onp_same_args)
    also have "\<dots> = Abs_vec_impl (length v, IArray (map (((!!) (IArray v))) [0..<length v]))"
      by (metis IArray.sub_def Matrix.mk_vec_def list_of.simps undef_vec)
    also have "\<dots> = Abs_vec_impl (length v, IArray v)"
      by (simp add: list.map_cong map_nth)
    finally show ?thesis.
  qed
  hence "vec_to_vec_impl (vec_impl (Abs_vec_impl (IArray.length v, v))) = Abs_vec_impl (IArray.length v, v)" for v
    unfolding IArray.length_def using list_of.simps iarray.exhaust by metis
  thus ?thesis
    by (rule vec_impl_exhaust)
qed

lemma dim_row_mat_of_row_fun_code[simp]: "dim_row (mat_impl (mat_of_row_fun_code nr nc f)) = nr"
  by (simp add: dim_row_code dim_row_impl.abs_eq eq_onp_same_args mat_of_row_fun_code.abs_eq)

lemma dim_col_mat_of_row_fun_code[simp]: "dim_col (mat_impl (mat_of_row_fun_code nr nc f)) = nc"
  by (simp add: dim_col_code dim_col_impl.abs_eq eq_onp_same_args mat_of_row_fun_code.abs_eq)

lemma mat_of_row_fun_code[code]: "mat_of_row_fun nr nc f =
  mat_impl (mat_of_row_fun_code nr nc (\<lambda>i. vec_to_vec_impl (f i)))"
proof - 
  have "index_mat_impl (mat_of_row_fun_code nr nc (\<lambda>i. vec_to_vec_impl (f i))) (i, j) = f i $v j" if "i < nr" "j < nc" for i j 
  proof (cases "\<forall>i<nr. length (IArray.list_of (snd (Rep_vec_impl (vec_to_vec_impl (f i))))) = nc")
    case True
    then show ?thesis
      using that 
      unfolding mat_of_row_fun_code.abs_eq vec_to_vec_impl.rep_eq 
      by (auto simp: index_mat_impl.abs_eq eq_onp_same_args vec_of_fun.rep_eq)
  next
    case False
    then show ?thesis 
      using that
      unfolding mat_of_row_fun_code.abs_eq vec_to_vec_impl.rep_eq
      using list_of_vec_index[of "f i" j] list_of_vec_map[of "f i"]
      by (auto simp: index_mat_impl.abs_eq eq_onp_same_args vec_of_fun.rep_eq vec_index_impl.rep_eq)
  qed
  thus ?thesis
    by (auto simp: index_mat_code)
qed
end