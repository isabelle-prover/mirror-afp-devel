theory VI_Code
  imports
    Code_Setup
    "../Value_Iteration" 
    "HOL-Library.Code_Target_Numeral"
begin

context MDP_Code begin

partial_function (tailrec) VI_code_aux where
"VI_code_aux v eps = (
  let v' = \<L>_code v in
    if check_dist v v' eps 
    then v'  
    else VI_code_aux v' eps)"

lemmas VI_code_aux.simps[code]

definition "VI_code v eps = (if l = 0 \<or> eps \<le> 0 then \<L>_code v else VI_code_aux v eps)"


lemma VI_code_aux_correct_aux:
  assumes "eps > 0" "v_invar v" "v_len v = states" "l \<noteq> 0"
  shows "V_Map.map_to_fun (VI_code_aux v eps) = MDP.value_iteration eps (V_Map.map_to_bfun v) 
  \<and> v_len (VI_code_aux v eps) = states 
  \<and> v_invar (VI_code_aux v eps)"
  using assms
proof (induction eps "V_Map.map_to_bfun v" arbitrary: v rule: MDP.value_iteration.induct)
  case (1 eps)
  have *: "(check_dist v (\<L>_code v) eps) \<longleftrightarrow> 2 * l * dist (V_Map.map_to_bfun v) (MDP.\<L>\<^sub>b (V_Map.map_to_bfun v)) < eps * (1 - l)"
  proof (subst check_dist_correct)
    have " 0 < l" using 1 MDP.zero_le_disc by linarith
    thus "(dist (V_Map.map_to_bfun v) (V_Map.map_to_bfun (\<L>_code v)) < eps * (1 - l) / (2 * l)) =
    (2 * l * dist (V_Map.map_to_bfun v) (MDP.\<L>\<^sub>b (V_Map.map_to_bfun v)) < eps * (1 - l))"
      by (subst pos_less_divide_eq) (fastforce simp: \<L>_code_correct' 1 algebra_simps)+
  qed (auto simp: 1 intro: invar_\<L>_code)
  hence **: "V_Map.map_to_fun (VI_code_aux v eps) = (MDP.value_iteration eps (V_Map.map_to_bfun (\<L>_code v)))" if "\<not> (check_dist v (\<L>_code v) eps)"
    using invar_\<L>_code 1 that by (auto simp: VI_code_aux.simps \<L>_code_correct')
  have "V_Map.map_to_fun (VI_code_aux v eps) = (MDP.value_iteration eps (V_Map.map_to_bfun v))"
  proof (cases "(check_dist v (\<L>_code v) eps)")
    case True
    thus ?thesis
    using 1 invar_\<L>_code
    by (auto simp: MDP.value_iteration.simps VI_code_aux.simps[of v] * map_to_bfun_eq_fun[symmetric] \<L>_code_correct')
next
  case False
  thus ?thesis 
    using 1 \<L>_code_correct' ** * MDP.value_iteration.simps by auto
qed
  thus ?case
    using 1 VI_code_aux.simps \<L>_code_correct' * invar_\<L>_code by auto
qed

lemma VI_code_aux_correct:
  assumes "eps > 0" "v_invar v" "v_len v = states" "l \<noteq> 0"
  shows "V_Map.map_to_fun (VI_code_aux v eps) = MDP.value_iteration eps (V_Map.map_to_bfun v)"
  using assms VI_code_aux_correct_aux by auto

lemma VI_code_aux_keys:
  assumes "eps > 0" "v_invar v" "v_len v = states" "l \<noteq> 0"
  shows "v_len (VI_code_aux v eps) = states"
  using assms VI_code_aux_correct_aux by auto

lemma VI_code_aux_invar:
  assumes "eps > 0" "v_invar v" "v_len v = states" "l \<noteq> 0"
  shows "v_invar (VI_code_aux v eps)"
  using assms VI_code_aux_correct_aux by auto

lemma VI_code_correct:
  assumes "eps > 0" "v_invar v" "v_len v = states"
  shows "V_Map.map_to_fun (VI_code v eps) = MDP.value_iteration eps (V_Map.map_to_bfun v)"
proof (cases "l = 0")
  case True
  then show ?thesis  
    using assms invar_\<L>_code \<L>_code_correct'
    unfolding VI_code_def MDP.value_iteration.simps[of _ "V_Map.map_to_bfun v"]
    by (fastforce simp: map_to_bfun_eq_fun)
next
  case False
  then show ?thesis
    using assms
    by (auto simp add: VI_code_def VI_code_aux_correct)
qed

definition "VI_policy_code v eps = vi_find_policy_code (VI_code v eps)"

lemma VI_policy_code_correct:
  assumes "eps > 0" "v_invar v" "v_len v = states"
  shows "D_Map.map_to_fun (VI_policy_code v eps) = MDP.vi_policy' eps (V_Map.map_to_bfun v)"
proof -
  have "V_Map.map_to_bfun (VI_code v eps) = (MDP.value_iteration eps (V_Map.map_to_bfun v))"
    using  assms VI_code_correct
    by (auto simp:  VI_code_aux_invar map_to_bfun_eq_fun)
  moreover have "D_Map.map_to_fun (VI_policy_code v eps) = MDP.find_policy' (V_Map.map_to_bfun (VI_code v eps))"
    unfolding VI_code_def VI_policy_code_def
    using assms invar_\<L>_code keys_\<L>_code vi_find_policy_correct vi_find_policy_correct VI_code_aux_correct_aux assms by (cases "l = 0") auto
  ultimately show ?thesis 
    unfolding MDP.vi_policy'_def
    by presburger
qed

end

context MDP_nat_disc
begin

lemma dist_opt_bound_\<L>\<^sub>b: "dist v \<nu>\<^sub>b_opt \<le> dist v (\<L>\<^sub>b v) / (1 - l)"
  using contraction_\<L>_dist
  by (simp add: mult.commute mult_imp_le_div_pos)

lemma cert_\<L>\<^sub>b: 
  assumes "\<epsilon> \<ge> 0" "dist v (\<L>\<^sub>b v) / (1 - l) \<le> \<epsilon>"
  shows "dist v \<nu>\<^sub>b_opt \<le> \<epsilon>"
  using assms dist_opt_bound_\<L>\<^sub>b order_trans by auto

definition "check_value_\<L>\<^sub>b eps v \<longleftrightarrow> dist v (\<L>\<^sub>b v) / (1 - l) \<le> eps"

definition "vi_policy_bound_error v = (
  let v' = (\<L>\<^sub>b v); err = (2 * l) * dist v v' / (1 - l) in
  (err, find_policy' v'))"

lemma 
  assumes "vi_policy_bound_error v = (err, d)"
  shows "dist (\<nu>\<^sub>b (mk_stationary_det d)) \<nu>\<^sub>b_opt \<le> err"
proof (cases "l = 0")
  case True
  hence "vi_policy_bound_error v = (0, find_policy' (\<L>\<^sub>b v))"
    unfolding vi_policy_bound_error_def by auto
  have "\<L>\<^sub>b v = \<L>\<^sub>b \<nu>\<^sub>b_opt"
    by (auto simp: \<L>\<^sub>b.rep_eq L_def simp del: \<L>\<^sub>b_opt intro!: bfun_eqI simp: \<L>_def) (simp add: True)
  hence "\<L>\<^sub>b v = \<nu>\<^sub>b_opt"
    by auto
  hence "\<nu>\<^sub>b (mk_stationary_det (find_policy' (\<L>\<^sub>b v))) = \<nu>\<^sub>b_opt"
    using L_\<nu>_fix \<nu>_improving_opt_acts conserving_imp_opt
    unfolding find_policy'_def \<nu>_conserving_def
    by auto
  then show ?thesis
    using assms unfolding vi_policy_bound_error_def 
    by (auto simp: True)
next
  case False
  then show ?thesis
  proof (cases "\<L>\<^sub>b v = v")
    case True
  hence "\<nu>\<^sub>b (mk_stationary_det (find_policy' (\<L>\<^sub>b v))) = \<nu>\<^sub>b_opt"
    using L_\<nu>_fix \<nu>_improving_opt_acts conserving_imp_opt
    unfolding find_policy'_def \<nu>_conserving_def
    by auto
  then show ?thesis
    using assms unfolding vi_policy_bound_error_def 
    by (auto simp: True)
  next
    case False
    hence 1: "dist v (\<L>\<^sub>b v) > 0"
      by fastforce
    hence "2 * l * dist v (\<L>\<^sub>b v) > 0"
      using \<open>l \<noteq> 0\<close> zero_le_disc by (simp add: less_le)
    hence "err > 0"
      using assms unfolding vi_policy_bound_error_def by auto
    hence "dist (\<nu>\<^sub>b (mk_stationary_det (find_policy' (\<L>\<^sub>b v)))) \<nu>\<^sub>b_opt < err'" if "err < err'" for err'
      using that assms
      unfolding vi_policy_bound_error_def
      by (auto simp:  pos_divide_less_eq[symmetric] intro: find_policy'_error_bound)
    then show ?thesis
      using assms unfolding vi_policy_bound_error_def Let_def
      by force
  qed
qed

end

context MDP_Code
begin
definition "vi_policy_bound_error_code v = (
  let v' = (\<L>_code v);
    d = if states = 0 then 0 else (MAX s \<in> {..< states}. dist (v_lookup v s) (v_lookup v' s));
   err = (2 * l) * d / (1 - l) in
  (err, vi_find_policy_code v'))"

lemma 
  assumes "v_len v = states" "v_invar v"
  shows "D_Map.map_to_fun (snd (vi_policy_bound_error_code v)) = snd (MDP.vi_policy_bound_error (V_Map.map_to_bfun v))"
  using assms \<L>_code_correct' invar_\<L>_code vi_find_policy_correct
  by (auto simp: vi_policy_bound_error_code_def MDP.vi_policy_bound_error_def)

lemma MAX_cong:
  assumes "\<And>x. x \<in> X \<Longrightarrow> f x = g x"
  shows "(MAX x \<in> X. f x) = (MAX x \<in> X. g x)"
  using assms by auto

lemma 
  assumes "v_len v = states" "v_invar v"
  shows "(fst (vi_policy_bound_error_code v)) = fst (MDP.vi_policy_bound_error (V_Map.map_to_bfun v))"
proof-
  have dist_zero_ge: "dist (apply_bfun (V_Map.map_to_bfun v) x) (apply_bfun (V_Map.map_to_bfun (\<L>_code v)) x) = 0" if "x \<ge> states" for x
    using assms that 
    by (auto simp: V_Map.map_to_bfun.rep_eq)
  have univ: "UNIV = {0..<states} \<union> {states..}" by auto
  let ?d = "\<lambda>x. dist (apply_bfun (V_Map.map_to_bfun v) x) (apply_bfun (V_Map.map_to_bfun (\<L>_code v)) x)"

 have fin: "finite (range (\<lambda>x. ?d x))"
   by (auto simp: dist_zero_ge univ Set.image_Un Set.image_constant[of states])
  
  have r: "range (\<lambda>x. ?d x) = ?d ` {..<states} \<union> ?d ` {states..}"
    by force
  hence "Sup (range ?d) = Max (range ?d)"
    using fin cSup_eq_Max by blast
  also have "\<dots> = (if states = 0 then (Max (?d ` {states..})) else max (Max (?d ` {..<states})) (Max (?d ` {states..})))"
    using r fin by (auto intro: Max_Un)
  also have "\<dots> = (if states = 0 then 0 else max (Max (?d ` {..<states})) 0)"
    using dist_zero_ge
    by (auto simp: Set.image_constant[of states] cSup_eq_Max[symmetric, of "(\<lambda>_. 0) ` {states..}"])
  also have "\<dots> = (if states = 0 then 0 else (Max (?d ` {..<states})))"
    by (auto intro!: max_absorb1 max_geI)
  finally have 1: "Sup (range ?d) = (if states = 0 then 0 else (Max (?d ` {..<states})))".
  thus ?thesis
    unfolding  MDP.vi_policy_bound_error_def vi_policy_bound_error_code_def dist_bfun_def
    using assms v_lookup_map_to_bfun \<L>_code_correct' \<L>_code_correct 
    by fastforce
qed

end

global_interpretation VI_Code:
  MDP_Code
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
  defines VI_code = VI_Code.VI_code
    and vi_policy_bound_error_code = VI_Code.vi_policy_bound_error_code
    and VI_code_aux = VI_Code.VI_code_aux
    and L\<^sub>a_code = VI_Code.L\<^sub>a_code
    and a_lookup' = VI_Code.a_lookup'
    and d_lookup' = VI_Code.d_lookup'
    and find_policy_state_code_aux' = VI_Code.find_policy_state_code_aux'
    and find_policy_state_code_aux = VI_Code.find_policy_state_code_aux
    and check_dist = VI_Code.check_dist
    and \<L>_code = VI_Code.\<L>_code
    and VI_policy_code = VI_Code.VI_policy_code
    and \<L>_GS_code = VI_Code.\<L>_GS_code
    and v0 = VI_Code.v0
    and entries = M.entries
    and from_list' = M.from_list'
    and from_list = M.from_list
    and vi_find_policy_code = VI_Code.vi_find_policy_code
    and v_map_from_list = VI_Code.v_map_from_list
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