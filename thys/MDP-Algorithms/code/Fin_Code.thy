theory Fin_Code
  imports 
    "../Backward_Induction"
    Code_Setup
begin

locale MDP_nat_fin = MDP_nat + MDP_reward_fin
begin
end

locale MDP_Code_Fin = MDP_Code_raw +
  R_Fin_Map : Array' "r_fin_lookup :: 'tf \<Rightarrow> nat \<Rightarrow> real" r_fin_update r_fin_len r_fin_array r_fin_list r_fin_invar +
  V_Map : Array' "v_lookup :: 'tv \<Rightarrow> nat \<Rightarrow> real" v_update v_len v_array v_list v_invar +
  D_Map : Array' "d_lookup :: 'td \<Rightarrow> nat \<Rightarrow> nat" d_update d_len d_array d_list d_invar +
  VD_Map : Array' "vd_lookup :: 'tvd \<Rightarrow> nat \<Rightarrow> (nat \<times> real)" vd_update vd_len vd_array vd_list vd_invar 
  for v_lookup v_update v_len v_array v_list v_invar
    and d_lookup d_update d_len d_array d_list  d_invar
    and vd_lookup vd_update vd_len vd_array vd_list  vd_invar
    and r_fin_lookup r_fin_update r_fin_len r_fin_array r_fin_list r_fin_invar +
  fixes 
    N_code :: nat and
    r_fin_code :: 'tf
begin

definition "v_map_from_list xs = v_array xs"
definition "MDP_r_fin s = (if s \<ge> states then 0 else r_fin_lookup r_fin_code s)"

lemma bounded_r_fin: "bounded (range MDP_r_fin)"
  unfolding MDP_r_fin_def
  by (fastforce simp add: nle_le bounded_const finite_nat_set_iff_bounded_le intro!: finite_imageI)

sublocale MDP: MDP_reward_disc "(MDP_A)" "(MDP_K)" "(MDP_r)" 0
  using bounded_MDP_r
  by unfold_locales auto

sublocale MDP: MDP_act "(MDP_A)" "(MDP_K)" "\<lambda>X. LEAST x. x \<in> X"
  using MDP.MDP_reward_disc_axioms
  by unfold_locales 
   (auto intro: LeastI2 simp: MDP_reward_disc.max_L_ex_def has_arg_max_def finite_is_arg_max)
 
sublocale MDP: MDP_nat_fin "\<lambda>X. LEAST x. x \<in> X" "(MDP_A)" "(MDP_K)" states "(MDP_r)" MDP_r_fin N_code
  using MDP_K_closed MDP_K_comp_closed MDP_r_zero_notin_states MDP_A_outside bounded_MDP_r bounded_r_fin 
  by unfold_locales (auto intro: LeastI2)

sublocale V_Map: Array_real v_lookup v_update v_len v_array v_list v_invar
  by unfold_locales

sublocale V_Map: Array_zero v_lookup v_update v_len v_array v_list v_invar
  by unfold_locales

sublocale D_Map: Array_zero d_lookup d_update d_len d_array d_list d_invar
  by unfold_locales

definition "L\<^sub>a_code rp v = ( 
    let (r, ps) = rp in r + (foldl (\<lambda> acc (s', p). p * v_lookup v s' + acc)) 0 ps)"

lemma L\<^sub>a_code_correct:
  assumes 
    "s < states" 
    "v_len v = states" "v_invar v" 
    "pmf_of_list (snd rps) = MDP_K (s, a)" "pmf_of_list_wf (snd rps)" 
    "fst ` set (snd rps) \<subseteq> {0..<states}" "fst rps = MDP_r (s, a)"
  shows "L\<^sub>a_code rps v = MDP_r (s, a) + measure_pmf.expectation (MDP_K (s,a)) (V_Map.map_to_bfun v)"
proof -
  have "measure_pmf.expectation (MDP_K (s, a)) (v_lookup v) = measure_pmf.expectation (MDP_K (s, a)) (V_Map.map_to_bfun v)"
    using assms MDP.K_closed
    by (force simp: V_Map.map_to_bfun.rep_eq split: option.splits 
        intro!: Bochner_Integration.integral_cong_AE AE_pmfI)
  have "foldl (\<lambda>acc x. f x + acc) x xs = (\<Sum>x\<leftarrow>xs. f x) + x" for f xs and x :: real
    by (induction xs arbitrary: x) (auto simp: algebra_simps)
  hence *: "(\<Sum>x\<leftarrow>xs. f x) = foldl (\<lambda>acc x. f x + acc) (0::real) xs" for f xs
    by (metis add.right_neutral)
  have "foldl (\<lambda>acc (s', p). p * v_lookup v s' + acc) 0 (snd rps) = 
    measure_pmf.expectation (MDP_K (s, a)) (apply_bfun (V_Map.map_to_bfun v))"
    unfolding assms(4)[symmetric] 
    using assms(5-7)
    by (auto intro!: foldl_cong simp: pmf_of_list_expectation * V_Map.map_to_bfun.rep_eq assms(2,3))
  thus ?thesis
    unfolding L\<^sub>a_code_def
    by (auto simp add: assms case_prod_unfold)
qed

definition "find_policy_state_code_aux v s = 
  (least_arg_max_max_ne (\<lambda>(_, rsuccs).    
    L\<^sub>a_code rsuccs v) ((a_inorder (s_lookup mdp s))))"

definition "find_policy_state_code_aux' v s = (
  case find_policy_state_code_aux v s of ((a, _, _), v) \<Rightarrow> (a, v))"

definition "vi_find_policy_code (v::'tv) = VD_Map.arr_tabulate (\<lambda>s. (find_policy_state_code_aux' v s)) states"

lemma find_policy_state_code_aux_eq:
  assumes "s < states"
  shows "find_policy_state_code_aux' v s = (least_arg_max_max_ne (\<lambda>a.
   L\<^sub>a_code (a_lookup' (s_lookup mdp s) a) v) ((map fst (a_inorder (s_lookup mdp s)))))"
  unfolding find_policy_state_code_aux'_def find_policy_state_code_aux_def
  using assms A_Map.is_empty_def ne_s_lookup 
  by(subst least_arg_max_max_ne_app'[symmetric]) 
    (auto simp: case_prod_unfold a_lookup'_def A_Map.entries_def A_Map.inorder_lookup_Some assms invar_s_lookup)


lemma L_GS_code_correct':
  assumes "s < states" "v_len v = states" "v_invar v" "a \<in> MDP_A s"
  shows "L\<^sub>a_code (a_lookup' (s_lookup mdp s) a) v = 
   MDP_r(s, a) + measure_pmf.expectation (MDP_K (s,a)) (V_Map.map_to_bfun v)"
  using pmf_of_list_wf_mdp assms set_list_pmf_in_states
  by (intro L\<^sub>a_code_correct) 
    (auto simp: fst_sa_lookup'_eq[symmetric] snd_sa_lookup'_eq)

lemma find_policy_state_code_aux'_eq':
  assumes "s < states" "v_len v = states" "v_invar v"
  shows "find_policy_state_code_aux' v s = 
  (least_arg_max (\<lambda>a. MDP_r(s, a) + measure_pmf.expectation (MDP_K (s,a)) (V_Map.map_to_bfun v)) (\<lambda>a. a \<in> MDP_A s), 
  Max ((\<lambda>a. MDP_r(s, a) + measure_pmf.expectation (MDP_K (s,a)) (V_Map.map_to_bfun v)) ` (MDP_A s)))"
proof -
  have "find_policy_state_code_aux' v s = least_arg_max_max_ne (\<lambda>a. L\<^sub>a_code (a_lookup' (s_lookup mdp s) a) v) (map fst (a_inorder (s_lookup mdp s)))"
    using find_policy_state_code_aux_eq assms by auto
  also have \<open>\<dots> = (least_arg_max (\<lambda>a. L\<^sub>a_code (a_lookup' (s_lookup mdp s) a) v) (List.member (map fst (a_inorder (s_lookup mdp s)))),
     MAX a\<in>set (map fst (a_inorder (s_lookup mdp s))). L\<^sub>a_code (a_lookup' (s_lookup mdp s) a) v)\<close>
    using A_Map.is_empty_def assms(1) A_Map.invar_def A_inv_locale S_Map.lookup_in_list s_invar s_len A_ne_locale 
    by (auto simp: fold_max_eq_arg_max')
  also have \<open>\<dots> = (least_arg_max (\<lambda>a. MDP_r(s, a) + measure_pmf.expectation (MDP_K (s,a)) (V_Map.map_to_bfun v)) (List.member (map fst (a_inorder (s_lookup mdp s)))),
     MAX a\<in>set (map fst (a_inorder (s_lookup mdp s))). MDP_r(s, a) + measure_pmf.expectation (MDP_K (s,a)) (V_Map.map_to_bfun v))\<close>
    using assms a_inorderD(1) A_Map.keys_def  MDP_A_def
    by (auto intro!: least_arg_max_cong simp: L_GS_code_correct' in_set_member[symmetric])
  also have \<open>\<dots> = (least_arg_max (\<lambda>a. MDP_r(s, a) + measure_pmf.expectation (MDP_K (s,a)) (V_Map.map_to_bfun v)) (\<lambda>a. a \<in> MDP_A s),
     MAX a\<in>MDP_A s. MDP_r(s, a) + measure_pmf.expectation (MDP_K (s,a)) (V_Map.map_to_bfun v))\<close>
    using assms A_Map.entries_def A_Map.keys_def A_Map.entries_imp_keys
    by (auto intro!: least_arg_max_cong' simp: MDP_A_def in_set_member[symmetric])
  finally show ?thesis.
qed

lemma vi_find_policy_code_correct:
  assumes "s < states" "v_len v = states" "v_invar v"
  shows "vd_lookup (vi_find_policy_code v) s = 
  ( least_arg_max 
      (\<lambda>a. MDP_r(s, a) + measure_pmf.expectation (MDP_K (s,a)) (V_Map.map_to_bfun v)) 
      (\<lambda>a. a \<in> MDP_A s)
  , Max ((\<lambda>a. MDP_r(s, a) + measure_pmf.expectation (MDP_K (s,a)) (V_Map.map_to_bfun v)) ` (MDP_A s)))"
  unfolding vi_find_policy_code_def
  by (auto simp: find_policy_state_code_aux'_eq' assms)

fun bw_ind_aux_code where
  "bw_ind_aux_code (Suc n) last_v m_v m_d = (let 
    vd = vi_find_policy_code last_v;
    v = V_Map.arr_tabulate (\<lambda>s. snd (vd_lookup vd s)) states;
    d = D_Map.arr_tabulate (\<lambda>s. fst (vd_lookup vd s)) states in 
    bw_ind_aux_code n v (last_v # m_v) (d # m_d))" |
  "bw_ind_aux_code 0 last_v m_v m_d = (last_v # m_v, m_d)"

definition "bw_ind_code = bw_ind_aux_code N_code (V_Map.arr_tabulate (r_fin_lookup r_fin_code) states) [] []" 

lemma bw_ind_aux_code_fst_index: "i < length v0 \<Longrightarrow> fst (bw_ind_aux_code n vl v0 d0) ! (i + n) = 
    (vl#v0) ! i"
  by (induction n arbitrary: vl v0 d0 i) (auto simp: add_Suc[symmetric] simp del: add_Suc)

lemma bw_ind_aux_code_fst_index': "n \<le> i \<Longrightarrow> fst (bw_ind_aux_code n vl v0 d0) ! i = 
    (vl#v0) ! (i - n)"
  by (induction n arbitrary: vl v0 d0 i) auto

lemma bw_ind_aux_code_snd_index': "n \<le> i  \<Longrightarrow> snd (bw_ind_aux_code n vl v0 d0) ! i = 
    (d0) ! (i - n)"
  by (induction n arbitrary: vl v0 d0 i) auto

lemma bw_ind_code_aux_correct:
  fixes n vl v0 d0
  defines "d \<equiv> snd (bw_ind_aux_code n vl v0 d0)"
  defines "v \<equiv> fst (bw_ind_aux_code n vl v0 d0)"
  assumes "v_len vl = states"
  assumes "v_invar vl"
  assumes "\<And>s. s < states \<Longrightarrow> m n s = v_lookup vl s"
  assumes "s < states"
  shows "(i \<le> n \<longrightarrow> v_lookup (v ! i) s = MDP.bw_ind_aux' n m i s) \<and> 
    (i < n \<longrightarrow> d_lookup (d ! i) s = (least_arg_max 
      (\<lambda>a. MDP_r (s, a) + measure_pmf.expectation (MDP_K (s, a)) (MDP.bw_ind_aux' n m (Suc i))) 
      (\<lambda>a. a \<in> MDP_A s)))"
  unfolding v_def d_def
  using assms
proof (induction n arbitrary: m i v0 d0 vl s)
  case (Suc n)
  show ?case
  proof (cases "i = Suc n")
    case True
    then show ?thesis
      by (simp add: Suc bw_ind_aux_code_fst_index')
  next
    case False
    then show ?thesis
    proof (cases "i = n")
      case True
      thus ?thesis
        using MDP_K_closed Suc.prems True
        by (auto intro!: least_arg_max_cong Bochner_Integration.integral_cong_AE AE_pmfI SUP_cong AE_pmfI
            simp: cSup_eq_Max[symmetric] bw_ind_aux_code_snd_index' bw_ind_aux_code_fst_index' 
              subset_eq V_Map.map_to_bfun.rep_eq vi_find_policy_code_correct)
    next
      case False
      have *: "\<And>s. s < states \<Longrightarrow>
         (\<Squnion>a\<in>MDP_A s. MDP_r (s, a) + measure_pmf.expectation (MDP_K (s, a)) (m (Suc n))) =
         v_lookup (V_Map.arr_tabulate (\<lambda>s. snd (vd_lookup (vi_find_policy_code vl) s)) states) s"
        using MDP.K_closed
        by (auto simp: subset_eq vi_find_policy_code_correct Suc cSup_eq_Max[symmetric] V_Map.map_to_bfun.rep_eq
            intro!: AE_pmfI  Bochner_Integration.integral_cong_AE SUP_cong)
      hence "v_lookup (fst (bw_ind_aux_code (Suc n) vl v0 d0) ! i) s = MDP.bw_ind_aux' (Suc n) m i s" if "i \<le> Suc n"
        unfolding bw_ind_aux_code.simps Let_def
        using \<open>i \<le> Suc n\<close> \<open>i \<noteq> Suc n\<close>
        by (subst Suc(1)[THEN conjunct1]) (auto simp: Suc)
      moreover have "d_lookup (snd (bw_ind_aux_code (Suc n) vl v0 d0) ! i) s =
     least_arg_max (\<lambda>a. MDP_r (s, a) + measure_pmf.expectation (MDP_K (s, a)) (MDP.bw_ind_aux' (Suc n) m (Suc i))) (\<lambda>a. a \<in> MDP_A s)" if "i < Suc n"
        unfolding bw_ind_aux_code.simps Let_def
        using \<open>i < Suc n\<close> \<open>i \<noteq> Suc n\<close> * False
        by (subst Suc(1)[THEN conjunct2]) (auto simp: Suc)
      ultimately show ?thesis
        by auto
    qed
  qed
qed auto


lemma bw_ind_code_correct:
  defines "d \<equiv> snd bw_ind_code"
  defines "v \<equiv> fst bw_ind_code"
  shows "\<And>n s. n \<le> N_code \<Longrightarrow> s < states \<Longrightarrow> v_lookup (v ! n) s = MDP.bw_ind n s"
    and "\<And>n. n < N_code \<Longrightarrow> s < states \<Longrightarrow> d_lookup (d ! n) s = MDP.bw_ind_pol_gen (\<lambda>X. LEAST a. a \<in> X) n s"
proof (goal_cases)
  case (1 n s)
  then show ?case 
    unfolding MDP.bw_ind_def
    by (subst bw_ind_code_aux_correct[THEN conjunct1, THEN mp, symmetric])
      (auto simp add: MDP_r_fin_def bw_ind_code_def v_def )
next
  case (2 n)
  then show ?case 
    unfolding MDP.bw_ind_pol_gen_def d_def bw_ind_code_def 
    by (subst bw_ind_code_aux_correct[THEN conjunct2])
      (auto simp: least_arg_max_def[symmetric] MDP_r_fin_def MDP.bw_ind_aux'_eq[symmetric])
qed
end


global_interpretation Fin_Code:
  MDP_Code_Fin

(* state map (transition system) *)
"IArray.sub" "\<lambda>n x arr. IArray ((IArray.list_of arr)[n:= x])" "IArray.length" "IArray" "IArray.list_of" "\<lambda>_. True"

(* action map *)
RBT_Set.empty RBT_Map.update RBT_Map.delete Lookup2.lookup Tree2.inorder rbt

"MDP.transitions (Rep_Valid_MDP mdp)" "MDP.states (Rep_Valid_MDP mdp)" 

(* value map *)
starray_get "\<lambda>i x arr. starray_set arr i x" starray_length starray_of_list "\<lambda>arr. starray_foldr (\<lambda>x xs. x # xs) arr []" "\<lambda>_. True"

(* decision map *)
starray_get "\<lambda>i x arr. starray_set arr i x" starray_length starray_of_list "\<lambda>arr. starray_foldr (\<lambda>x xs. x # xs) arr []" "\<lambda>_. True"

(* value-decision map *)
starray_get "\<lambda>i x arr. starray_set arr i x" starray_length starray_of_list "\<lambda>arr. starray_foldr (\<lambda>x xs. x # xs) arr []" "\<lambda>_. True"

(* r_fin map *)
starray_get "\<lambda>i x arr. starray_set arr i x" starray_length starray_of_list "\<lambda>arr. starray_foldr (\<lambda>x xs. x # xs) arr []" "\<lambda>_. True"

for mdp r_fin_code N_code
defines L\<^sub>a_code = Fin_Code.L\<^sub>a_code
  and a_lookup' = Fin_Code.a_lookup'
  and v_map_from_list = Fin_Code.v_map_from_list
  and find_policy_state_code_aux' = Fin_Code.find_policy_state_code_aux'
  and find_policy_state_code_aux = Fin_Code.find_policy_state_code_aux
  and entries = M.entries
  and from_list' = M.from_list'
  and from_list = M.from_list
  and bw_ind_code = Fin_Code.bw_ind_code
  and bw_ind_aux_code = Fin_Code.bw_ind_aux_code
  and vi_find_policy_code = Fin_Code.vi_find_policy_code
  and arr_tabulate = starray_Array.arr_tabulate
  using Rep_Valid_MDP  
  by unfold_locales
    (fastforce simp: Ball_set_list_all[symmetric] case_prod_beta pmf_of_list_wf_def is_MDP_def RBT_Set.empty_def M.invar_def empty_def M.entries_def M.is_empty_def length_0_conv[symmetric])+

lemmas arr_tabulate_def[unfolded starray_Array.arr_tabulate_def, code]
lemmas entries_def[unfolded M.entries_def, code]
lemmas from_list'_def[unfolded M.from_list'_def, code]
lemmas from_list_def[unfolded M.from_list_def, code]

function tabulate where
  "tabulate f acc upper n = (
  if n < upper then tabulate f (update n (f n) acc) upper (Suc n) else acc)"
  by auto
termination
  by (relation "Wellfounded.measure (\<lambda>(_, _, i,N). i - N)") auto

lemma tabulate_Suc: "j \<le> n' \<Longrightarrow> update n' (f n') (tabulate f m n' j) = tabulate f m (Suc n') j"
proof (induction "n' - j" arbitrary: m n' j)
  case 0
  then show ?case by auto
next
  case (Suc j)
  then show ?case
    by auto
qed

lemma from_list'_upt [code_unfold]: "from_list' f [0..<n] = tabulate f empty n 0"
proof -
  have "j \<le> n \<Longrightarrow> foldl (\<lambda>acc s. update s (f s) acc) m [j..<n] = tabulate f m n j" for m j
  proof (induction "n - j" arbitrary: m n j)
    case 0
    then show ?case by auto
  next
    case (Suc x)
    then obtain n' where n': "n = Suc n'"
      using diff_le_self Suc_le_D by metis
    then show ?case
      using Suc
      by (auto simp del: tabulate.simps simp: n' tabulate_Suc)
  qed
  thus ?thesis
    unfolding from_list'_def M.from_list'_def
    by auto
qed

end