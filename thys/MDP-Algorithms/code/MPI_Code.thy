theory MPI_Code
  imports 
    Code_Setup
    "../Modified_Policy_Iteration"
    "HOL-Library.Code_Target_Numeral"
begin

sublocale MDP_nat_disc \<subseteq> MDP_MPI
  by unfold_locales

context MDP_Code begin

definition "d0 = D_Map.from_list' (\<lambda>s. fst (hd (a_inorder (s_lookup mdp s)))) [0..<states]"

definition "r_min_code =
  min 0 (MIN s \<in> set [0..<states]. MIN (_, r, _) \<in> set (a_inorder (s_lookup mdp s)). r)"

definition "v0_code = V_Map.arr_tabulate (\<lambda>s. r_min_code / (1 - l)) states"

definition "d0_code = D_Map.from_list' (\<lambda>s. fst (hd (a_inorder (s_lookup mdp s)))) [0..<states]"

definition "find_policy_L_code v =
  fold (\<lambda>s (d', v').
    let (ds, vs) = find_policy_state_code_aux' v s in
    (d_update s ds d', v_update s vs v')) [0..<states] (d_empty, V_Map.arr_tabulate (\<lambda>_. 0) states)"

definition "find_policy_L_code' v =
  fold (\<lambda>s (d', v'). 
    let (ds, vs) = find_policy_state_code_aux' v s in
    (d_update s ds d', v_update s vs v')) [0..<states] (d_empty, v)"

lemma fold_prod: "fold (\<lambda>x (a1, a2). (f x a1, g x a2)) xs (z1, z2) = 
    (fold f xs z1, fold g xs z2)"
  by (induction xs arbitrary: z1 z2) auto

lemma s_lookup_entries_eq:
  assumes "s < states"
  shows "{(a, r, pmf_of_list k) | a r k. (a, r, k) \<in> A_Map.entries (s_lookup mdp s)}
     = {(a, MDP_r (s,a), MDP_K (s,a)) | a . a \<in> MDP_A s}"
proof -
  have "\<exists>k. MDP_K (s, a) = pmf_of_list k \<and> (a, MDP_r (s, a), k) \<in> A_Map.entries (s_lookup mdp s)" 
    if "a \<in> MDP_A s" for a
    by (metis a_map_entries_lookup fst_sa_lookup'_eq assms prod.collapse snd_sa_lookup'_eq that)
  thus ?thesis
    using entries_A_eq_K assms entries_A_eq_r
    by (auto simp: a_inorderD(1))
qed

lemma a_lookup_entries: "A_Map.invar m \<Longrightarrow> kv \<in> A_Map.entries m \<Longrightarrow> a_lookup' m (fst kv) = snd kv"
  by (metis A_Map.inorder_lookup_Some a_lookup'_def option.case(2) prod.collapse)

lemma a_inorder_eq_MDP_A: "x < states \<Longrightarrow> fst ` set (a_inorder (s_lookup mdp x)) = MDP_A x"
  using A_Map.keys_def MDP_A_def by presburger

lemma find_policy_L_code_split: 
  assumes "v_len v = states" "v_invar v"
  shows "fst (find_policy_L_code v) = vi_find_policy_code v"
    "\<And>i. i < states \<Longrightarrow> v_lookup (snd (find_policy_L_code v)) i = v_lookup (\<L>_code v) i "
    "v_len (snd (find_policy_L_code v)) = states"
    "v_invar (snd (find_policy_L_code v))"
proof (goal_cases)  
  have **: "(x,y) \<in> A_Map.entries ( (s_lookup mdp i)) \<Longrightarrow> (a_lookup' (s_lookup mdp i) x) = y" 
    if "i < states" for i x y
    by (simp add: A_Map.inorder_lookup_Some a_lookup'_def invar_s_lookup that)

  have *: "find_policy_L_code v = 
    (vi_find_policy_code v, 
     fold (\<lambda>s. v_update s (snd (find_policy_state_code_aux' v s))) [0..<states] 
      (V_Map.arr_tabulate (\<lambda>_.0) states))"
    unfolding find_policy_L_code_def vi_find_policy_code_def
    by (simp add: foldl_conv_fold case_prod_beta fold_prod D_Map.from_list'_def)

  have **: 
    "v_lookup (fold (\<lambda>s. v_update s (snd (find_policy_state_code_aux' v s))) [0..<states] v0) i = 
      v_lookup (\<L>_code v) i" 
    if "i < states" for i
    unfolding \<L>_code_def \<L>_GS_code_def V_Map.arr_tabulate_def
    using V_Map.invar_array v0_correct
    using A_Map.is_empty_def A_Map.invar_def A_Map.entries_def
    using ne_s_lookup invar_s_lookup a_lookup_entries 
    using that
    by (auto simp: fold_max_eq_arg_max' image_image case_prod_beta find_policy_state_code_aux_eq 
        V_Map.lookup_array v_lookup_fold)
  case 1
  thus ?case using * by auto

  case 3
  show ?case
    unfolding *
    by (auto simp: V_len_fold)
  case 4
  show ?case
    unfolding *
    by (auto simp: V_invar_fold)
  case (2 i) thus ?case
    using **
    by (auto simp: * v0_def)
qed

definition "L_code d v = 
  V_Map.arr_tabulate (\<lambda>s.  L\<^sub>a_code (a_lookup' (s_lookup mdp s) (d_lookup' d s)) v) states"

lemma L_code_correct:
  assumes "s < states" "v_len v = states" "v_invar v"
    "D_Map.keys d = MDP.state_space" "D_Map.invar d" "(\<And>s. s < states \<Longrightarrow> d_lookup' d s \<in> MDP_A s)"
  shows 
    "v_lookup (L_code d v) s = MDP.L (MDP.mk_dec_det (D_Map.map_to_fun d)) (V_Map.map_to_bfun v) s"
  using assms
  unfolding L_code_def MDP.L_eq_L\<^sub>a_det
  by (auto simp: map_to_fun_lookup L_GS_code_correct')

lemma L_code_invar: "v_invar (L_code d v)"
  by (simp add: L_code_def)

lemma L_code_keys: 
  assumes "v_len v = states" "v_invar v" 
    "D_Map.keys d = MDP.state_space" "D_Map.invar d" "(\<And>s. s < states \<Longrightarrow> d_lookup' d s \<in> MDP_A s)"
  shows "v_len (L_code d v) = states"
  by (simp add: L_code_def)

definition "L_pow_code v d m = (L_code d ^^ m) v"

lemma L_pow_code_Suc: "L_pow_code v d (Suc m) = L_code d (L_pow_code v d m)"
  by (auto simp: L_pow_code_def)

lemma L_code_to_bfun:
  assumes "v_len v = states" "v_invar v"
    "D_Map.keys d = MDP.state_space" "D_Map.invar d" "(\<And>s. s < states \<Longrightarrow> d_lookup' d s \<in> MDP_A s)"
  shows "V_Map.map_to_bfun (L_code d v) = 
      MDP.L (MDP.mk_dec_det  (D_Map.map_to_fun d)) (V_Map.map_to_bfun v)"
proof (rule bfun_eqI)
  fix s
  show "(V_Map.map_to_bfun (L_code d v)) s = 
    (MDP.L (MDP.mk_dec_det (D_Map.map_to_fun d)) (V_Map.map_to_bfun v)) s"
  proof (cases "s < states")
    case True
    then show ?thesis
      using L_code_correct assms
      by (auto simp: L_code_def v_lookup_map_to_bfun)
  next
    case False
    then show ?thesis 
      using assms
      by (subst MDP.L_zero) (auto simp: L_code_def V_Map.map_to_bfun.rep_eq split: option.splits)
  qed
qed

lemma L_pow_code_correct:
  assumes "v_len v = states" "v_invar v"
    "D_Map.keys d = MDP.state_space" "D_Map.invar d" "(\<And>s. s < states \<Longrightarrow> d_lookup' d s \<in> MDP_A s)"
  shows 
    "v_len (L_pow_code v d m) = states"
    "v_invar (L_pow_code v d m)"
    "V_Map.map_to_bfun (L_pow_code v d m) = ((MDP.L_pow (V_Map.map_to_bfun v) ((D_Map.map_to_fun d))) m) "
  using assms
proof (induction m arbitrary: v)
  case (Suc m)
  {
    case 3
    then show ?case 
      using Suc
      by (auto simp: L_pow_code_def L_code_to_bfun  MDP.L_pow_def)
  }
qed (auto simp add: L_pow_code_def L_code_to_bfun L_code_def MDP.L_pow_def)

partial_function (tailrec) mpi_partial_code  where
  "mpi_partial_code eps d v m =
  (let (d', v') = find_policy_L_code v in (
    if l = 0 \<or> check_dist v v' eps
    then (d', v)
    else mpi_partial_code eps d' (L_pow_code v' d' m) m))"

lemmas mpi_partial_code.simps[code]

lemma vi_find_policy_code_correct': 
  assumes "v_len v_code = states" "v_invar v_code"
  shows "d_lookup (vi_find_policy_code v_code) s = (
  if s < states then Some (MDP.find_policy' (V_Map.map_to_bfun v_code) s) else None)"
  using assms vi_find_policy_code_correct[of v_code s] d_invar_vi_find_policy_code
  using d_keys_vi_find_policy_code D_Map.lookup_None_set_inorder[of "vi_find_policy_code v_code" s]
  unfolding MDP.find_policy'_def D_Map.map_to_fun_def
  by (auto simp: least_arg_max_def MDP.is_opt_act_def vi_find_policy_code_notin split: option.splits)


lemma L\<^sub>a_equiv: "(L\<^sub>a_code (a_lookup' (s_lookup mdp s) (d_lookup' d s)) v) = (L\<^sub>a_code (a_lookup' (s_lookup mdp s) (d_lookup' d s)) v')"
  if "\<And>i. i < states \<Longrightarrow> v_lookup v i = v_lookup v' i" "s < states" "v_len v = states" "v_len v' = states" "v_invar v" "v_invar v'"
    "D_Map.keys d = MDP.state_space" "D_Map.invar d" "(\<And>s. s < states \<Longrightarrow> d_lookup' d s \<in> MDP_A s)"  
  for s v v' d
proof -
  have "V_Map.map_to_bfun v = V_Map.map_to_bfun v'"
    using that
    by (auto simp: V_Map.map_to_bfun.rep_eq)
  moreover have *: "L\<^sub>a_code (a_lookup' (s_lookup mdp s) (d_lookup' d s)) v = MDP.L\<^sub>a (d_lookup' d s) (apply_bfun (V_Map.map_to_bfun v)) s"
    using that snd_sa_lookup'_eq pmf_of_list_wf_mdp set_list_pmf_in_states[of s "(d_lookup' d s)"]
    by (subst L\<^sub>a_code_correct[of s _ _ "(d_lookup' d s)"]) (fastforce simp add: fst_sa_lookup'_eq)+
  ultimately show ?thesis
    unfolding *
    using that snd_sa_lookup'_eq pmf_of_list_wf_mdp set_list_pmf_in_states[of s " d_lookup' d s"]
    by (subst L\<^sub>a_code_correct[of s _ _ "(d_lookup' d s)"]) (auto simp add: fst_sa_lookup'_eq )
qed

lemma L_code_equiv: "v_lookup (L_code d v) i = v_lookup (L_code d v') i" 
  if "\<And>i. i < states \<Longrightarrow> v_lookup v i = v_lookup v' i" "i < states" "D_Map.keys d = MDP.state_space" "D_Map.invar d" "(\<And>s. s < states \<Longrightarrow> d_lookup' d s \<in> MDP_A s)"  
    "v_len v = states" "v_len v' = states" "v_invar v" "v_invar v'"
  unfolding L_code_def 
  using that 
  by (auto intro!: L\<^sub>a_equiv)

lemma L_pow_code_equiv: "v_lookup (L_pow_code v d m) i = v_lookup (L_pow_code v' d m) i" if "\<And>i. i < states \<Longrightarrow> v_lookup v i = v_lookup v' i" "i < states" 
  "D_Map.keys d = MDP.state_space" "D_Map.invar d" "(\<And>s. s < states \<Longrightarrow> d_lookup' d s \<in> MDP_A s)" "v_len v = states" "v_len v' = states" "v_invar v" "v_invar v'"
for v v' d i m
  using that L_code_invar
proof (induction m arbitrary: v v' i)
  case 0
  then show ?case by (simp add: L_pow_code_def)
next
  case (Suc m)
  thus ?case
    unfolding L_pow_code_Suc
    using L_pow_code_correct L_code_equiv
    by presburger
qed

lemma map_to_bfun_snd_find_policy_L_code:
  assumes "v_len v_code = states" "v_invar v_code"
  shows "V_Map.map_to_bfun (snd (find_policy_L_code v_code)) = V_Map.map_to_bfun(\<L>_code v_code)"
  using invar_\<L>_code 
  by (auto simp: V_Map.map_to_bfun.rep_eq assms find_policy_L_code_split)

lemma mpi_partial_code_correct:
  fixes eps d_code v_code m_code

assumes "MDP.mpi_algo_dom eps (d, v, m)"
assumes "v = V_Map.map_to_bfun v_code"
assumes "d = D_Map.map_to_fun d_code"
assumes "m = (\<lambda>(a::nat) (b:: nat \<Rightarrow>\<^sub>b real). m_code)"
assumes "eps > 0"
assumes "d \<in> MDP.D\<^sub>D"
assumes "v \<le> MDP.\<L>\<^sub>b v"
assumes "v_invar v_code"
assumes "v_len v_code = states"
shows 
  "D_Map.map_to_fun (fst (mpi_partial_code eps d_code v_code m_code)) = fst (MDP.mpi_algo eps d v m)"
  "V_Map.map_to_bfun (snd (mpi_partial_code eps d_code v_code m_code)) = snd (MDP.mpi_algo eps d v m)"
proof -
  have "MDP.mpi_algo eps d v m = (D_Map.map_to_fun (fst (mpi_partial_code eps d_code v_code m_code)), 
    V_Map.map_to_bfun (snd (mpi_partial_code eps d_code v_code m_code)))"
    using assms
  proof (induction d v m arbitrary: d_code v_code m_code rule: MDP.mpi_algo.pinduct)
    case (1 d v m)
    then show ?case
    proof (cases "l = 0")
      case True
      have *: "mpi_partial_code eps d_code v_code m_code = (let (d', v') = find_policy_L_code v_code in (d', v_code))" for v_code
        using True mpi_partial_code.simps by presburger
      have "MDP.mpi_algo eps (D_Map.map_to_fun d_code) (V_Map.map_to_bfun v_code) (\<lambda>a b. m_code) = (MDP.find_policy' v, v)"
        using 1 True MDP.mpi_algo.psimps 
        by auto
      also have "\<dots> = (D_Map.map_to_fun (fst (mpi_partial_code eps d_code v_code m_code)), V_Map.map_to_bfun (snd (mpi_partial_code eps d_code v_code m_code)))"
        using "1.prems"
        by (auto simp: * case_prod_beta vi_find_policy_correct find_policy_L_code_split)
      finally show ?thesis
        unfolding 1
        by auto
    next
      case False
      hence "check_dist v_code (\<L>_code v_code) eps \<longleftrightarrow> dist v (MDP.\<L>\<^sub>b v) <  (eps * (1 - l)) / (2 * l)"
        using 1 invar_\<L>_code assms(6) \<L>_code_correct' 
        by (auto simp: check_dist_correct)
      hence *: "check_dist v_code (\<L>_code v_code) eps \<longleftrightarrow> 2 * l * dist v (MDP.\<L>\<^sub>b v) <  eps * (1 - l)"
        using zero_le_disc_locale False 
        by (auto simp: algebra_simps less_divide_eq)
      then show ?thesis 
      proof (cases "check_dist v_code (\<L>_code v_code) eps")
        case True
        hence "2 * l * dist v (MDP.\<L>\<^sub>b v) <  eps * (1 - l)"
          using * by auto
        hence *: "MDP.mpi_algo eps d v m = (MDP.find_policy' v, v)"
          by (simp add: MDP.mpi_algo.domintros MDP.mpi_algo.psimps)
        moreover have **:
          "(mpi_partial_code eps d_code v_code m_code) = (fst (find_policy_L_code v_code), v_code)"
          using "1.prems" True False
          by (simp add: mpi_partial_code.simps check_dist_def find_policy_L_code_split case_prod_beta)
        ultimately show ?thesis
          using "1.prems"
          by (simp add: find_policy_L_code_split vi_find_policy_correct)
      next
        case False
        hence not_check: "\<not>2 * l * dist v (MDP.\<L>\<^sub>b v) <  eps * (1 - l)"
          using * by auto

        have d_in_A: "\<And>s. s < states \<Longrightarrow> d_lookup' (vi_find_policy_code v_code) s \<in> MDP_A s"
          unfolding d_lookup'_def
          using "1.prems" MDP.find_policy'_is_dec_det MDP.is_dec_det_def  
          by (auto simp: vi_find_policy_code_correct' )
        have aux: "V_Map.map_to_bfun (L_pow_code  v_code (vi_find_policy_code v_code) (Suc m_code)) = 
          V_Map.map_to_bfun (L_pow_code (\<L>_code v_code) (vi_find_policy_code v_code) m_code)"
        proof -
          have **: "i < states \<Longrightarrow> v_lookup (L_code (vi_find_policy_code v_code) v_code) i = v_lookup (\<L>_code v_code) i" for i
            using  d_in_A d_invar_vi_find_policy_code d_keys_vi_find_policy_code
            using "1.prems"(7,8) MDP.\<nu>_improving_imp_\<L>\<^sub>b[OF MDP.find_policy'_improving]
            by (auto simp: L_code_correct \<L>_code_correct vi_find_policy_correct)

          have *: "V_Map.map_to_bfun (L_pow_code  v_code (vi_find_policy_code v_code) (Suc m_code)) = 
            V_Map.map_to_bfun (L_pow_code (L_code (vi_find_policy_code v_code) v_code) (vi_find_policy_code v_code) m_code)"
            by (simp add: L_pow_code_def funpow_swap1)
          show ?thesis
            unfolding *
            by (auto intro!: bfun_eqI L_pow_code_equiv simp: L_pow_code_correct(1,2)
                d_invar_vi_find_policy_code d_keys_vi_find_policy_code
                L_code_keys L_code_invar invar_\<L>_code keys_\<L>_code
                V_Map.map_to_bfun.rep_eq ** "1.prems"(7,8) d_in_A)
        qed
        have "MDP.mpi_algo eps d v m = MDP.mpi_algo eps (D_Map.map_to_fun d_code) (V_Map.map_to_bfun v_code) (\<lambda>a b. m_code)"
          using 1 by auto
        also have "\<dots> =
           MDP.mpi_algo eps (MDP.find_policy' v) (MDP.L_pow v (MDP.find_policy' v) (Suc m_code)) m"
          using 1 not_check by (auto simp: MDP.mpi_algo.psimps)
        also have "\<dots> = MDP.mpi_algo eps (D_Map.map_to_fun (vi_find_policy_code v_code)) (MDP.L_pow (V_Map.map_to_bfun v_code) (D_Map.map_to_fun (vi_find_policy_code v_code)) (Suc m_code)) m"
          using 1 by (auto simp: vi_find_policy_correct[symmetric])
        also have "\<dots> = MDP.mpi_algo eps (D_Map.map_to_fun (vi_find_policy_code v_code)) (V_Map.map_to_bfun (L_pow_code  v_code (vi_find_policy_code v_code) (Suc m_code))) m"
          using 1 L_pow_code_correct(3) d_in_A d_invar_vi_find_policy_code d_keys_vi_find_policy_code 
          by auto
        also have "\<dots> = MDP.mpi_algo eps (D_Map.map_to_fun (vi_find_policy_code v_code)) (V_Map.map_to_bfun (L_pow_code (\<L>_code v_code) (vi_find_policy_code v_code) m_code)) m"
          using aux by auto
        also have "\<dots> = (let (d', v') = (mpi_partial_code eps (vi_find_policy_code v_code) (L_pow_code (\<L>_code v_code) (vi_find_policy_code v_code) m_code) m_code) in 
        (D_Map.map_to_fun d', V_Map.map_to_bfun v'))"
        proof -
          have
            [simp]: "v_invar (L_pow_code (\<L>_code v_code) (vi_find_policy_code v_code) m_code)"
            and [simp]: "v_len (L_pow_code (\<L>_code v_code) (vi_find_policy_code v_code) m_code) = states"
            and L_pow_code_eq: 
            "MDP.L_pow (V_Map.map_to_bfun v_code) (MDP.find_policy' (V_Map.map_to_bfun v_code)) (Suc m_code) = V_Map.map_to_bfun (L_pow_code (\<L>_code v_code) (vi_find_policy_code v_code) m_code)"
            using d_in_A keys_\<L>_code invar_\<L>_code 1 d_keys_vi_find_policy_code d_invar_vi_find_policy_code L_pow_code_correct
            by (auto simp: aux[symmetric] vi_find_policy_correct)
          show ?thesis
            unfolding Let_def case_prod_beta
            using MDP.find_policy'_is_dec_det not_check "1.prems"(6)
            by (subst 1(2)[symmetric]) (auto simp: "1.prems" L_pow_code_eq[symmetric] vi_find_policy_correct intro!: MDP.L_pow_\<L>\<^sub>b_mono_inv')
        qed
        also have "\<dots> = MDP.mpi_algo eps (MDP.find_policy' v) (MDP.L_pow v (MDP.find_policy' v) (Suc (m 0 v))) (\<lambda>a. m (Suc a))"
          unfolding Let_def case_prod_beta
          using \<open>l\<noteq> 0\<close> not_check
          using MDP.find_policy'_is_dec_det d_invar_vi_find_policy_code d_keys_vi_find_policy_code
          using MDP.L_pow_\<L>\<^sub>b_mono_inv'  vi_find_policy_correct
          using "1.prems" L_pow_code_correct d_in_A   invar_\<L>_code keys_\<L>_code  
          by (auto simp: 1(2)[symmetric] aux[symmetric])
        also have "\<dots> = (D_Map.map_to_fun (fst (mpi_partial_code eps d_code v_code m_code)), V_Map.map_to_bfun (snd (mpi_partial_code eps d_code v_code m_code)))"
        proof -
          have *: "MDP.L_pow (V_Map.map_to_bfun v_code) (MDP.find_policy' (V_Map.map_to_bfun v_code)) (Suc m_code) =
        V_Map.map_to_bfun (L_pow_code (snd (find_policy_L_code v_code)) (fst (find_policy_L_code v_code)) m_code)"
            using d_keys_vi_find_policy_code d_invar_vi_find_policy_code d_in_A
            using "1.prems" L_pow_code_correct aux invar_\<L>_code map_to_bfun_snd_find_policy_L_code vi_find_policy_correct 
            by (auto simp: find_policy_L_code_split)
          show ?thesis
            unfolding mpi_partial_code.simps[of _ _ v_code]
            using not_check False "1.prems" 
            using d_in_A d_invar_vi_find_policy_code d_keys_vi_find_policy_code
              find_policy_L_code_split MDP.L_pow_\<L>\<^sub>b_mono_inv' *[symmetric]
            using MDP.find_policy'_is_dec_det
            by (auto simp: case_prod_beta check_dist_def 1(2)[symmetric] L_pow_code_correct vi_find_policy_correct) 
        qed
        finally show "MDP.mpi_algo eps d v m = (D_Map.map_to_fun (fst (mpi_partial_code eps d_code v_code m_code)), V_Map.map_to_bfun (snd (mpi_partial_code eps d_code v_code m_code)))"
          by auto
      qed
    qed
  qed
  thus "D_Map.map_to_fun (fst (mpi_partial_code eps d_code v_code m_code)) = fst (MDP.mpi_algo eps d v m)" " V_Map.map_to_bfun (snd (mpi_partial_code eps d_code v_code m_code)) = snd (MDP.mpi_algo eps d v m)"
    using assms
    by (auto simp: MDP.termination_mpi_algo)
qed

lemma d_map_to_fun_from_list': "D_Map.map_to_fun (D_Map.from_list' f xs) a = (if a \<in> set xs then f a else 0)"
  by (simp add: d_lookup'_def map_to_fun_lookup map_to_fun_notin)

definition "MPI_code eps m =
  (if eps \<le> 0 then undefined else 
    let (d, v) = mpi_partial_code eps d0_code v0_code m in d)"

lemma d0_code_is_dec_det: "MDP.is_dec_det (D_Map.map_to_fun d0_code)"
  unfolding d0_code_def  A_Map.keys_def  MDP.is_dec_det_def MDP_A_def
  using MDP_A_outside ne_s_lookup A_Map.is_empty_def
  by (auto split: option.splits simp: d_map_to_fun_from_list')

lemma Min_cong: "finite X \<Longrightarrow> X \<noteq> {} \<Longrightarrow> (\<And>x. x \<in> X \<Longrightarrow> f x = g x) \<Longrightarrow> (MIN x \<in> X. f x) = (MIN x \<in> X. g x)"
  by force

lemma r_min_code_correct:
  assumes "states > 0"
  shows "r_min_code = MDP.r_min"
proof -
  have bounded_r': "bounded ((\<lambda>a. MDP_r (x, a)) ` MDP_A x)" for x
    using MDP.r_bounded'
    unfolding bounded_def
    by simp (meson UNIV_I)
  have *: "(\<Sqinter>a\<in>MDP_A x. MDP_r (x, a)) \<le> MDP_r (x,a)" if "a \<in> MDP_A x" for  a x
    using  bounded_r' that 
    by (auto intro!: cInf_lower bounded_imp_bdd_below)
  have ****: "MDP_r (s,a) \<le> MDP.r\<^sub>M" for s a
    using abs_le_iff MDP.abs_r_le_r\<^sub>M by blast
  have **: "bounded (range (\<lambda>s'. \<Sqinter>a\<in>MDP_A s'. MDP_r (s', a)))"
    using MDP.abs_r_le_r\<^sub>M  MDP.ex_dec_det MDP.is_dec_det_def MDP.A_ne
    by (auto simp add: minus_le_iff abs_le_iff intro!: cINF_greatest order.trans[OF *]  boundedI[of _ "MDP.r\<^sub>M"])
  have "MDP.r_min \<le> MDP_r (s, a)" if "a \<in> MDP_A s" for s a
    using  MDP.r_bounded' that **
    by (auto intro!: bounded_imp_bdd_below cInf_lower2[OF _ *])
  have bdd: "bdd_below ((\<lambda>x. \<Sqinter>a\<in>MDP_A x. MDP_r (x, a)) ` {states..})"
    using "**" bounded_real by (auto intro!: bounded_imp_bdd_below)
  have "(\<Sqinter>x. (\<Sqinter>a\<in>MDP_A x. MDP_r (x, a))) =  (\<Sqinter>x\<in>{0..<states} \<union> {states..}. (\<Sqinter>a\<in>MDP_A x. MDP_r (x, a)))"
    by (simp add: ivl_disj_un_one(8))
  also have "\<dots> = min (\<Sqinter>x\<in>{0..<states}. (\<Sqinter>a\<in>MDP_A x. MDP_r (x, a))) (\<Sqinter>x\<in>{states..}. (\<Sqinter>a\<in>MDP_A x. MDP_r (x, a)))"
    using bdd
    by (auto simp add: image_Un cInf_union_distrib inf_min assms)
  also have "\<dots> = min (\<Sqinter>x\<in>{0..<states}. (\<Sqinter>a\<in>MDP_A x. MDP_r (x, a))) (\<Sqinter>x\<in>{states..}. (\<Sqinter>a\<in>MDP_A x. 0))"
    using MDP_r_zero_notin_states by auto
  also have "\<dots> = min (\<Sqinter>x\<in>{0..<states}. (\<Sqinter>a\<in>MDP_A x. MDP_r (x, a))) 0"
    by auto
  also have "\<dots> = min (MIN x\<in>{0..<states}. (MIN a\<in>MDP_A x. MDP_r (x, a))) 0"
    using assms
    by (simp add: cInf_eq_Min)
  also have "\<dots> = r_min_code"
    unfolding r_min_code_def
    using assms A_Map.is_empty_def ne_s_lookup A_Map.entries_def entries_A_eq_r     
    by (auto simp: case_prod_beta MDP_A_def A_Map.keys_def min.commute image_image 
        intro!: Min_cong cong[of "min 0", OF refl])
  finally show ?thesis..
qed

lemma v0_code_correct: "s < states \<Longrightarrow> v_lookup v0_code s = (MDP.v0_mpi\<^sub>b s)"
  unfolding v0_code_def MDP.v0_mpi\<^sub>b.rep_eq  MDP.v0_mpi_def
  by (auto simp add: not_less MDP_r_zero_notin_states r_min_code_correct)

lemma v0_invar: "v_invar v0_code"
  by (simp add: v0_code_def)

lemma v0_keys: "v_len v0_code = states"
  by (simp add: v0_code_def)

lemma L\<^sub>a_indep_notin: 
  assumes "s < states" 
  shows "MDP.L\<^sub>a d (apply_bfun v) s = MDP.L\<^sub>a d (bfun_if (\<lambda>s. s < states) v u) s"
proof -
  have " measure_pmf.expectation (MDP_K (s, d)) v = 
    measure_pmf.expectation (MDP_K (s, d)) (\<lambda>s. if s < states then v s else u s)"
    using MDP_K_closed assms
    by (auto intro!: AE_pmfI integral_cong_AE simp: subset_eq)  
  thus ?thesis
    by (auto simp: bfun_if.rep_eq)
qed

lemma \<L>\<^sub>b_indep_notin: "s < states \<Longrightarrow> MDP.\<L>\<^sub>b v s = MDP.\<L>\<^sub>b (bfun_if (\<lambda>s. s < states) v u) s"
  unfolding MDP.\<L>\<^sub>b_eq_SUP_L\<^sub>a'
  using L\<^sub>a_indep_notin by presburger

lemma 
  v0_code_inc_\<L>\<^sub>b:
  "V_Map.map_to_bfun v0_code \<le> MDP.\<L>\<^sub>b (V_Map.map_to_bfun v0_code)"
proof (rule less_eq_bfunI)
  fix x
  show "(V_Map.map_to_bfun v0_code) x \<le> (MDP.\<L>\<^sub>b (V_Map.map_to_bfun v0_code)) x" 
  proof (cases "x < states")
    case True
    have "(V_Map.map_to_bfun v0_code) x = MDP.v0_mpi\<^sub>b x"
      using True v0_keys
      by (simp add: True V_Map.map_to_bfun.rep_eq v0_code_correct v0_invar)
    also have "\<dots> \<le> MDP.\<L>\<^sub>b MDP.v0_mpi\<^sub>b x"
      using MDP.v0_mpi\<^sub>b_le_\<L>\<^sub>b by blast
    also have "\<dots> = MDP.\<L>\<^sub>b ((bfun_if (\<lambda>s. s < states) (V_Map.map_to_bfun v0_code)) (MDP.v0_mpi\<^sub>b)) x"
      using v0_invar
      by (auto simp: apply_bfun_inverse bfun_if_def V_Map.map_to_bfun.rep_eq v0_code_correct MDP.L_def v0_keys MDP.\<L>_def cong: if_cong)
    also have "\<dots> =  MDP.\<L>\<^sub>b (V_Map.map_to_bfun v0_code) x"
      using True \<L>\<^sub>b_indep_notin by presburger
    finally show ?thesis.
  next
    case False
    then show ?thesis
      by (simp add: MDP.\<L>\<^sub>b_zero v0_code_def V_Map.map_to_bfun.rep_eq)
  qed
qed

lemma
  fixes eps m_code
  defines "d_opt_code \<equiv> (MPI_code eps m_code)"
  defines "m \<equiv> (\<lambda>(a::nat) (b:: nat \<Rightarrow>\<^sub>b real). m_code)"
  assumes "eps > 0"
  defines "v \<equiv> V_Map.map_to_bfun v0_code"
  defines "d \<equiv> D_Map.map_to_fun d0_code"
  defines "m \<equiv> (\<lambda>(a::nat) (b:: nat \<Rightarrow>\<^sub>b real). m_code)"
  shows 
    "D_Map.map_to_fun d_opt_code = fst (MDP.mpi_algo eps d v m)"
  unfolding d_def v_def m_def d_opt_code_def MPI_code_def
  using assms d0_code_is_dec_det v0_code_inc_\<L>\<^sub>b v0_invar MDP.termination_mpi_algo
  by (auto simp: v0_keys case_prod_beta intro!: mpi_partial_code_correct(1))
end

global_interpretation MPI_Code: MDP_Code
(* state map (transition system) *)
"IArray.sub" "\<lambda>n x arr. IArray ((IArray.list_of arr)[n:= x])" "IArray.length" "IArray" "IArray.list_of" "\<lambda>_. True"

(* action map *)
RBT_Set.empty RBT_Map.update RBT_Map.delete Lookup2.lookup Tree2.inorder rbt

"MDP.transitions (Rep_Valid_MDP mdp)" "MDP.states (Rep_Valid_MDP mdp)"

(* value map *)
starray_get "\<lambda>i x arr. starray_set arr i x"  starray_length starray_of_list  "\<lambda>arr. starray_foldr (\<lambda>x xs. x # xs) arr []" "\<lambda>_. True"

(* decision rule map *)
RBT_Set.empty RBT_Map.update RBT_Map.delete Lookup2.lookup Tree2.inorder rbt

"MDP.disc (Rep_Valid_MDP mdp)"
for mdp
defines MPI_code = MPI_Code.MPI_code
  and a_lookup' = MPI_Code.a_lookup'
  and d_lookup' = MPI_Code.d_lookup'

and check_dist = MPI_Code.check_dist

and entries = M.entries
and from_list' = M.from_list'

and mpi_partial_code = MPI_Code.mpi_partial_code
and L\<^sub>a_code = MPI_Code.L\<^sub>a_code
and L_pow_code = MPI_Code.L_pow_code
and L_code = MPI_Code.L_code

and find_policy_state_code_aux' = MPI_Code.find_policy_state_code_aux'
and find_policy_state_code_aux = MPI_Code.find_policy_state_code_aux
and find_policy_L_code = MPI_Code.find_policy_L_code

and r_min_code = MPI_Code.r_min_code
and v0_code = MPI_Code.v0_code
and d0_code = MPI_Code.d0_code
and arr_tabulate = starray_Array.arr_tabulate
  using Rep_Valid_MDP
  by unfold_locales  
    (auto simp: pmf_of_list_wf_def Ball_set_list_all[symmetric] case_prod_beta is_MDP_def 
      RBT_Set.empty_def M.invar_def empty_def M.entries_def M.is_empty_def length_0_conv[symmetric])

lemmas entries_def[unfolded M.entries_def, code]
lemmas from_list'_def[unfolded M.from_list'_def, code]
lemmas arr_tabulate_def[unfolded starray_Array.arr_tabulate_def, code]

end