(*
    Authors:    Maximilian Haslbeck
                René Thiemann
    License:    BSD
*)
section \<open>Complexity of the LLL algorithm\<close>

subsection \<open>Explicit Bound on Number of Arithmetic Operations\<close>

text \<open>In this section we define a version of the LLL algorithm which explicitly returns the
  costs of running the algorithm. Its soundness is mainly proven by stating that 
  projecting away yields the original result.

  The cost model counts the number of arithmetic operations that occur in vector-addition, scalar-products,
  and scalar multiplication and we prove a polynomial bound on this number.\<close>

theory LLL_Mu_Integer_Impl_Complexity
  imports 
    LLL_Mu_Integer_Impl
    Cost
begin

definition floor_ceil_num_denom_cost :: "int \<Rightarrow> int \<Rightarrow> int cost" where
  "floor_ceil_num_denom_cost n d = ((2 * n + d) div (2 * d), 4)" \<comment> \<open>4 arith. operations\<close>

lemma floor_ceil_num_denom_cost:  
  shows "result (floor_ceil_num_denom_cost n d) = floor_ceil_num_denom n d"  
   "cost (floor_ceil_num_denom_cost n d) \<le> 4" 
  unfolding floor_ceil_num_denom_cost_def floor_ceil_num_denom_def by (auto simp: cost_simps) 

context LLL_with_assms
begin

context
  fixes arith_cost :: nat
  assumes \<alpha>_gt: "\<alpha> > 4/3" and m0: "m \<noteq> 0" 
begin


fun basis_reduction_add_rows_loop_cost where
  "basis_reduction_add_rows_loop_cost state i j [] = (state, 0)" 
| "basis_reduction_add_rows_loop_cost state i sj (fj # fjs) = (
     let fi = fi_state state;
         dsj = d_state state sj;
         j = sj - 1;
         (c,cost1) = floor_ceil_num_denom_cost (dmu_ij_state state i j) dsj;
         state' = (if c = 0 then state else upd_fi_mu_state state i (fi - c \<cdot>\<^sub>v fj) \<comment> \<open>2n arith. operations\<close>
             (IArray.of_fun (\<lambda> jj. let mu = dmu_ij_state state i jj in \<comment> \<open>3 sj arith. operations\<close>
                  if jj < j then mu - c * dmu_ij_state state j jj else 
                  if jj = j then mu - dsj * c else mu) i));
         local_cost = 2 * n + 3 * sj;
         (res,cost2) = basis_reduction_add_rows_loop_cost state' i j fjs
      in (res, cost1 + local_cost + cost2))"


lemma basis_reduction_add_rows_loop_cost: assumes "length fs = j" 
  shows "result (basis_reduction_add_rows_loop_cost state i j fs) = basis_reduction_add_rows_loop state i j fs"  
   "cost (basis_reduction_add_rows_loop_cost state i j fs) \<le> sum (\<lambda> j. (2 * n + 4 + 3 * (Suc j))) {0..<j}" 
  using assms
proof (atomize(full), induct fs arbitrary: state j)
  case (Cons fj fs state j)
  let ?dm_ij = "dmu_ij_state state i (j - 1)" 
  let ?dj = "d_state state j" 
  obtain c1 fc where flc: "floor_ceil_num_denom_cost ?dm_ij ?dj = (fc, c1)" by force
  from floor_ceil_num_denom_cost[of ?dm_ij ?dj, unfolded flc] 
  have fl: "floor_ceil_num_denom ?dm_ij ?dj = fc" and c1: "c1 \<le> 4" by (auto simp: cost_simps)
  obtain st where st: "(if fc = 0 then state
             else upd_fi_mu_state state i (fi_state state - fc \<cdot>\<^sub>v fj)
                   (IArray.of_fun
                     (\<lambda>jj. if jj < j - 1 then dmu_ij_state state i jj - fc * dmu_ij_state state (j - 1) jj
                           else if jj = j - 1 then dmu_ij_state state i jj - d_state state j * fc else dmu_ij_state state i jj)
                     i)) = st"  by auto
  obtain res c2 where rec: "basis_reduction_add_rows_loop_cost st i (j - 1) fs = (res,c2)" (is "?x = _") by (cases ?x, auto)
  from Cons(2) have "length fs = j - 1" by auto
  from Cons(1)[OF this, of st, unfolded rec cost_simps]
  have res: "basis_reduction_add_rows_loop st i (j - 1) fs = res" 
    and c2: "c2 \<le> (\<Sum>j = 0..<j - 1. 2 * n + 4 + 3 * Suc j)" by auto
  show ?case unfolding basis_reduction_add_rows_loop_cost.simps Let_def flc split 
      basis_reduction_add_rows_loop.simps fl st rec res cost_simps
  proof (intro conjI refl, goal_cases)
    case 1 
    have "c1 + (2 * n + 3 * j) + c2 \<le> (\<Sum>j = 0..<j - 1. 2 * n + 4 + 3 * Suc j) + (2 * n + 4 + 3 * Suc (j - 1))" 
      using c1 c2 by auto
    also have "\<dots> = (\<Sum>j = 0..<j. 2 * n + 4 + 3 * (Suc j))" 
      by (subst (2) sum.remove[of _ "j - 1"], insert Cons(2), auto intro: sum.cong)
    finally show ?case .
  qed
qed (auto simp: cost_simps)

definition basis_reduction_add_rows_cost where
  "basis_reduction_add_rows_cost upw i state = 
     (if upw then basis_reduction_add_rows_loop_cost state i i (small_fs_state state) 
        else (state,0))" 

lemma basis_reduction_add_rows_cost: assumes impl: "LLL_impl_inv state i fs" and inv: "LLL_invariant upw i fs" 
  shows "result (basis_reduction_add_rows_cost upw i state) = basis_reduction_add_rows upw i state"  
   "cost (basis_reduction_add_rows_cost upw i state) \<le> (2 * n + 2 * i + 7) * i"
proof (atomize (full), goal_cases)
  case 1
  note d = basis_reduction_add_rows_cost_def basis_reduction_add_rows_def
  show ?case
  proof (cases upw)
    case False
    thus ?thesis by (auto simp: d cost_simps)
  next
    case True
    hence upw: "upw = True" by simp
    obtain f mu ds where state: "state = (f,mu,ds)" by (cases state, auto)
    from to_list_repr[OF impl inv state] 
    have len: "length (small_fs_state state) = i" 
      unfolding small_fs_state.simps state list_repr_def by auto
    let ?call = "basis_reduction_add_rows_cost upw i state" 
    have res: "result ?call = basis_reduction_add_rows upw i state" 
      and cost: "cost ?call \<le> sum (\<lambda> j. (2 * n + 4 + 3 * (Suc j))) {0..<i}"
      unfolding d upw if_True using basis_reduction_add_rows_loop_cost[OF len, of state i] by auto
    note cost
    also have "sum (\<lambda> j. (2 * n + 4 + 3 * (Suc j))) {0..<i} = (2 * n + 7) * i + 3 * (\<Sum>j = 0..<i. j)" 
      by (auto simp: algebra_simps  sum.distrib sum_distrib_right sum_distrib_left)
    also have "(\<Sum>j = 0..<i. j) = (i * (i - 1) div 2)" 
    proof (induct i)
      case (Suc i)
      thus ?case by (cases i, auto)
    qed auto
    finally have "cost ?call \<le> (2 * n + 7) * i + 3 * (i * (i - 1) div 2)" .
    also have "\<dots> \<le> (2 * n + 7) * i + 2 * i * i" 
    proof (rule add_left_mono)
      have "3 * (i * (i - 1) div 2) \<le> 2 * i * (i - 1)" by simp
      also have "\<dots> \<le> 2 * i * i" by (intro mult_mono, auto)
      finally show "3 * (i * (i - 1) div 2) \<le> 2 * i * i" .
    qed
    also have "\<dots> = (2 * n + 2 * i + 7) * i" by (simp add: algebra_simps)
    finally have cost: "cost ?call \<le> (2 * n + 2 * i + 7) * i" .
    show ?thesis using res cost by simp
  qed
qed

definition swap_mu_cost :: "int iarray iarray \<Rightarrow> nat \<Rightarrow> int \<Rightarrow> int \<Rightarrow> int \<Rightarrow> int \<Rightarrow> int iarray iarray cost" where
  "swap_mu_cost dmu i dmu_i_im1 dim1 di dsi = (let im1 = i - 1;
       res = IArray.of_fun (\<lambda> ii. if ii < im1 then dmu !! ii else 
         if ii > i then let dmu_ii = dmu !! ii in 
             IArray.of_fun (\<lambda> j. let dmu_ii_j = dmu_ii !! j in   \<comment> \<open>8 arith. operations for whole line\<close>
                 if j = i then (dsi * dmu_ii !! im1 - dmu_i_im1 * dmu_ii_j) div di \<comment> \<open>4 arith. operations for this entry\<close>
                 else if j = im1 then (dmu_i_im1 * dmu_ii_j + dmu_ii !! i * dim1) div di \<comment> \<open>4 arith. operations for this entry\<close>
                 else dmu_ii_j) ii else 
         if ii = i then let mu_im1 = dmu !! im1 in 
             IArray.of_fun (\<lambda> j. if j = im1 then dmu_i_im1 else mu_im1 !! j) ii 
           else IArray.of_fun (\<lambda> j. dmu !! i !! j) ii) \<comment> \<open>ii = i - 1\<close>
         m; \<comment> \<open>in total, there are m - (i+1) many lines that require arithmetic operations: i + 1, ..., m - 1\<close>
       cost = 8 * (m - Suc i)
    in (res,cost))" 

lemma swap_mu_cost: 
   "result (swap_mu_cost dmu i dmu_i_im1 dim1 di dsi) = swap_mu m dmu i dmu_i_im1 dim1 di dsi"  
   "cost (swap_mu_cost dmu i dmu_i_im1 dim1 di dsi) \<le> 8 * (m - Suc i)" 
  by (auto simp: swap_mu_cost_def swap_mu_def Let_def cost_simps)

definition basis_reduction_swap_cost where
  "basis_reduction_swap_cost i state = (let 
       di = d_state state i;
       dsi = d_state state (Suc i);
       dim1 = d_state state (i - 1);
       fi = fi_state state;
       fim1 = fim1_state state;
       dmu_i_im1 = dmu_ij_state state i (i - 1);
       fi' = fim1;
       fim1' = fi;
       di' = (dsi * dim1 + dmu_i_im1 * dmu_i_im1) div di; \<comment> \<open>4 arith. operations\<close>
       local_cost = 4 
     in (case state of (f,dmus,djs) \<Rightarrow>
        case swap_mu_cost dmus i dmu_i_im1 dim1 di dsi of
          (swap_res, swap_cost) \<Rightarrow>
          let res = (False, i - 1, 
                     (dec_i (update_im1 (update_i f fi') fim1'), 
                      swap_res, 
                      iarray_update djs i di'));
              cost = local_cost + swap_cost 
         in (res, cost)))"

lemma basis_reduction_swap_cost: 
   "result (basis_reduction_swap_cost i state) = basis_reduction_swap m i state"  
   "cost (basis_reduction_swap_cost i state) \<le> 8 * (m - Suc i) + 4" 
proof (atomize(full), goal_cases)
  case 1
  obtain f dmus djs where state: "state = (f,dmus,djs)" by (cases state, auto)
  let ?mu = "dmu_ij_state (f, dmus, djs) i (i - 1)"
  let ?di1 = "d_state (f, dmus, djs) (i - 1)" 
  let ?di = "d_state (f, dmus, djs) i" 
  let ?dsi = "d_state (f, dmus, djs) (Suc i)" 
  show ?case unfolding basis_reduction_swap_cost_def basis_reduction_swap_def Let_def state split
    using swap_mu_cost[of dmus i ?mu ?di1 ?di ?dsi] 
    by (cases "swap_mu_cost dmus i ?mu ?di1 ?di ?dsi", auto simp: cost_simps)
qed

definition basis_reduction_step_cost where
  "basis_reduction_step_cost upw i state = (if i = 0 then ((True, Suc i, inc_state state), 0)
     else let 
       (state',cost_add) = basis_reduction_add_rows_cost upw i state;
       di = d_state state' i;
       dsi = d_state state' (Suc i);
       dim1 = d_state state' (i - 1);
       (num,denom) = quotient_of \<alpha>;
       cond = (di * di * denom \<le> num * dim1 * dsi); \<comment> \<open>5 arith. operations\<close>
       local_cost = 5
    in if cond then
          ((True, Suc i, inc_state state'), local_cost + cost_add) 
        else case basis_reduction_swap_cost i state' of (res, cost_swap) \<Rightarrow> (res, local_cost + cost_swap + cost_add))" 

definition "body_cost = 2 + (8 + 2 * n + 2 * m) * m" 

lemma basis_reduction_step_cost: assumes 
    impl: "LLL_impl_inv state i fs" 
  and inv: "LLL_invariant upw i fs" 
  and i: "i < m" 
  shows "result (basis_reduction_step_cost upw i state) = basis_reduction_step \<alpha> m upw i state" (is ?g1)
     "cost (basis_reduction_step_cost upw i state) \<le> body_cost" (is ?g2)
proof -
  obtain state' c_add where add: "basis_reduction_add_rows_cost upw i state = (state',c_add)" 
    (is "?add = _") by (cases ?add, auto)
  obtain state'' c_swap where swapc: "basis_reduction_swap_cost i state' = (state'',c_swap)" 
    (is "?swap = _") by (cases ?swap, auto)
  note res = basis_reduction_step_cost_def[of upw i state, unfolded add split swap]
  from basis_reduction_add_rows_cost[OF impl inv, unfolded add]
  have add: "basis_reduction_add_rows upw i state = state'" 
    and c_add: "c_add \<le> (2 * n + 2 * i + 7) * i" 
    by (auto simp: cost_simps)
  from basis_reduction_swap_cost[of i state', unfolded swapc cost_simps]
  have swap: "basis_reduction_swap m i state' = state''" 
    and c_swap: "c_swap \<le> 8 * (m - Suc i) + 4" by auto
  have "c_add + c_swap + 5 \<le> 8 * m + 2 + (2 * n + 2 * i) * i" 
    using c_add c_swap i by (auto simp: field_simps)
  also have "\<dots> \<le> 8 * m + 2 + (2 * n + 2 * m) * m" 
    by (intro add_left_mono mult_mono, insert i, auto)
  also have "\<dots> = 2 + (8 + 2 * n + 2 * m) * m" by (simp add: field_simps)
  finally have body: "c_add + c_swap + 5 \<le> body_cost" unfolding body_cost_def .
  obtain num denom where alpha: "quotient_of \<alpha> = (num,denom)" by force
  note res' = basis_reduction_step_def[of \<alpha> m upw i state, unfolded add swap Let_def alpha split]
  note d = res res'
  show ?g1 unfolding d by (auto split: if_splits simp: cost_simps Let_def alpha swapc)
  show ?g2 unfolding d nat_distrib using body by (auto split: if_splits simp: cost_simps alpha Let_def swapc)
qed

function basis_reduction_main_cost where
  "basis_reduction_main_cost upw i state = (if i < m 
     \<and> LLL_impl_inv state i (fs_state state) \<and> LLL_invariant upw i (fs_state state)
     \<comment> \<open>The check on the invariants is just to be able to prove termination. 
        One cannot use partial-function at this point, since the function with cost is not tail-recursive.\<close>
     then case basis_reduction_step_cost upw i state of ((upw',i',state'), c_step) \<Rightarrow> 
       case basis_reduction_main_cost upw' i' state' of (state'', c_rec) \<Rightarrow> (state'', c_step + c_rec) else
       (state, 0))"
  by pat_completeness auto

termination
proof (standard, rule wf_measure[of "\<lambda> (upw,i,state). LLL_measure i (fs_state state)"], goal_cases)
  case (1 upw i state tup cost upw' pair i' state')
  note * = 1(2-4)[symmetric] 
  from 1(1) have i: "i < m" 
    and impl: "LLL_impl_inv state i (fs_state state)" 
    and inv: "LLL_invariant upw i (fs_state state)" by auto
  from basis_reduction_step_cost[OF impl inv i, unfolded * cost_simps]
  have "basis_reduction_step \<alpha> m upw i state = (upw',i',state')" by auto
  from basis_reduction_step[OF impl inv this i refl]
  show ?case by simp
qed

declare basis_reduction_main_cost.simps[simp del]

definition "num_loops = m + 2 * m * m * nat (ceiling (log base (real A)))"

lemma basis_reduction_main_cost: assumes impl: "LLL_impl_inv state i (fs_state state)" 
  and inv: "LLL_invariant upw i (fs_state state)" 
  and state: "state = initial_state m fs_init" 
  and i: "i = 0" 
  shows "result (basis_reduction_main_cost upw i state) = basis_reduction_main \<alpha> m upw i state" (is ?g1) 
   "cost (basis_reduction_main_cost upw i state) \<le> body_cost * num_loops" (is ?g2)
proof -
  have ?g1 and cost: "cost (basis_reduction_main_cost upw i state) \<le> body_cost * LLL_measure i (fs_state state)"
    using assms(1-2)
  proof (atomize (full), induct "LLL_measure i (fs_state state)" arbitrary: upw i state rule: less_induct)
    case (less i state upw)
    note inv = less(3)
    note impl = less(2)
    obtain i' upw' state' c_step where step: "basis_reduction_step_cost upw i state = ((upw',i',state'),c_step)" 
      (is "?step = _") by (cases ?step, auto)
    obtain state'' c_rec where rec: "basis_reduction_main_cost upw' i' state' = (state'', c_rec)"
      (is "?rec = _") by (cases ?rec, auto)
    note step' = basis_reduction_step_cost[OF impl inv, unfolded step cost_simps]
    note d = basis_reduction_main_cost.simps[of upw] step split rec 
        basis_reduction_main.simps[of _ _ upw] 
    show ?case 
    proof (cases "i < m")
      case i: True
      from step'[OF i] have step': "basis_reduction_step \<alpha> m upw i state = (upw',i',state')"
         and c_step: "c_step \<le> body_cost" 
        by auto
      note d = d step'
      from basis_reduction_step[OF impl inv step' i refl]
      have impl': "LLL_impl_inv state' i' (fs_state state')" 
        and inv': "LLL_invariant upw' i' (fs_state state')"
        and meas: "LLL_measure i' (fs_state state') < LLL_measure i (fs_state state)" 
        by auto
      from less(1)[OF meas impl' inv', unfolded rec cost_simps]
      have rec': "basis_reduction_main \<alpha> m upw' i' state' = state''" 
        and c_rec: "c_rec \<le> body_cost * LLL_measure i' (fs_state state')" by auto
      from c_step c_rec have "c_step + c_rec \<le> body_cost * Suc (LLL_measure i' (fs_state state'))" 
        by auto
      also have "\<dots> \<le> body_cost * LLL_measure i (fs_state state)" 
        by (rule mult_left_mono, insert meas, auto)
      finally show ?thesis unfolding d rec' using i inv impl by (auto simp: cost_simps)
    next
      case False
      thus ?thesis unfolding d by (auto simp: cost_simps)
    qed
  qed
  show ?g1 by fact
  note cost also have "body_cost * LLL_measure i (fs_state state) \<le> body_cost * num_loops" 
  proof (rule mult_left_mono; linarith?)
    define l where "l = log base (real A)" 
    define k where "k = 2 * m * m" 
    obtain f mu ds where init: "initial_state m fs_init = (f,mu,ds)" by (cases "initial_state m fs_init", auto)
    from fs_state[OF initial_state LLL_inv_initial_state init] LLL_invD(6)[OF LLL_inv_initial_state]
    have fs: "fs_state (initial_state m fs_init) = fs_init" by auto
    have "LLL_measure i (fs_state state) \<le> nat (ceiling (m + k * l))" unfolding l_def k_def
      using LLL_measure_approx_fs_init[OF LLL_inv_initial_state \<alpha>_gt m0] unfolding state fs i
      by linarith
    also have "\<dots> \<le> num_loops" unfolding num_loops_def l_def[symmetric] k_def[symmetric]
      by (simp add: of_nat_ceiling times_right_mono)
    finally show "LLL_measure i (fs_state state) \<le> num_loops" .
  qed
  finally show ?g2 .
qed

(* TODO: integrate cost for initial_state: below is the calculation for the GSO-based initial state

definition "initial_gso_cost = (4 * m + 3) * m * n * arith_cost" 

definition initial_state_cost :: "int vec list \<Rightarrow> LLL_gso_state cost" where
  "initial_state_cost fs = (case gram_schmidt_triv_cost (map (map_vec of_int) fs)
     of (gs,c) \<Rightarrow> (([], (zip fs gs)), c))" 

definition basis_reduction_cost :: "int vec list \<Rightarrow> LLL_gso_state cost" where 
  "basis_reduction_cost fs = (
    case initial_state_cost fs of (state1, c1) \<Rightarrow> 
    case basis_reduction_main_cost True 0 state1 of (state2, c2) \<Rightarrow> 
      (state2, c1 + c2))" 

definition reduce_basis_cost :: "int vec list \<Rightarrow> int vec list cost" where
  "reduce_basis_cost fs = (case fs of Nil \<Rightarrow> (fs, 0) | Cons f _ \<Rightarrow> 
    case basis_reduction_cost fs of (state,c) \<Rightarrow> 
    (fs_state state, c))" 

lemma initial_state_cost: "result (initial_state_cost fs_init) = initial_state n fs_init" (is ?g1)
  "cost (initial_state_cost fs_init) \<le> initial_gso_cost" (is ?g2)
proof -
  let ?F = "map (map_vec rat_of_int) fs_init" 
  have len: "length ?F \<le> m" using len by auto
  obtain G c where gso: "gram_schmidt_triv_cost ?F = (G,c)" (is "?gso = _")
    by (cases ?gso, auto)
  note gsoc = gram_schmidt_triv_cost[OF len, unfolded gso cost_simps]
  show ?g1 ?g2 unfolding initial_gso_cost_def initial_state_cost_def gso split cost_simps 
    initial_state_def Let_def gsoc(1)[symmetric] using gsoc(2) by auto
qed

lemma basis_reduction_cost: 
   "result (basis_reduction_cost fs_init) = basis_reduction \<alpha> n fs_init"  (is ?g1)
   "cost (basis_reduction_cost fs_init) \<le> initial_gso_cost + body_cost * num_loops" (is ?g2)
proof -
  obtain state1 c1 where init: "initial_state_cost fs_init = (state1, c1)" (is "?init = _") by (cases ?init, auto)
  obtain state2 c2 where main: "basis_reduction_main_cost True 0 state1 = (state2, c2)" (is "?main = _") by (cases ?main, auto)
  have res: "basis_reduction_cost fs_init = (state2, c1 + c2)" 
    unfolding basis_reduction_cost_def init main split by simp
  from initial_state_cost[unfolded init cost_simps]
  have c1: "c1 \<le> initial_gso_cost" and init: "initial_state n fs_init = state1" by auto
  note inv = LLL_inv_initial_state
  note impl = initial_state
  from fs_state[OF impl LLL_invD(6)[OF inv]] 
  have fs: "fs_state (initial_state n fs_init) = fs_init" by auto
  from basis_reduction_main_cost[of "initial_state n fs_init", unfolded fs, OF impl inv,
    unfolded init main cost_simps] 
  have main: "basis_reduction_main \<alpha> m True 0 state1 = state2" and c2: "c2 \<le> body_cost * num_loops" 
    by auto
  have res': "basis_reduction \<alpha> n fs_init = state2" unfolding basis_reduction_def len init main ..
  show ?g1 unfolding res res' cost_simps ..
  show ?g2 unfolding res cost_simps using c1 c2 by auto
qed

text \<open>The lemma for the LLL algorithm with explicit cost annotations @{const reduce_basis_cost}
  shows that the termination measure
  indeed gives rise to an explicit cost bound. Moreover, the computed result is
  the same as in the non-cost counting @{const reduce_basis}.\<close>

lemma reduce_basis_cost: 
   "result (reduce_basis_cost fs_init) = reduce_basis \<alpha> fs_init"  (is ?g1)
   "cost (reduce_basis_cost fs_init) \<le> initial_gso_cost + body_cost * num_loops" (is ?g2)
proof (atomize(full), goal_cases)
  case 1
  note d = reduce_basis_cost_def reduce_basis_def
  show ?case
  proof (cases fs_init)
    case Nil
    show ?thesis unfolding d unfolding Nil by (auto simp: cost_simps)
  next
    case (Cons f)
    obtain state c where b: "basis_reduction_cost fs_init = (state,c)" (is "?b = _") by (cases ?b, auto)
    from basis_reduction_cost[unfolded b cost_simps]
    have bb: "basis_reduction \<alpha> n fs_init = state" and c: "c \<le> initial_gso_cost + body_cost * num_loops" 
      by auto
    from fs_init[unfolded Cons] have dim: "dim_vec f = n" by auto
    show ?thesis unfolding d b split unfolding Cons list.simps unfolding Cons[symmetric] dim bb
      using c by (auto simp: cost_simps)
  qed
qed


text \<open>Theorem with expanded costs: $O(n\cdot m^3 \cdot \log (\mathit{maxnorm}\ F))$ arithmetic operations\<close>
lemma reduce_basis_cost_expanded: 
  assumes "Log = nat \<lceil>log (of_rat (4 * \<alpha> / (4 + \<alpha>))) AA\<rceil>"   
  and "AA = max_list (map (nat \<circ> sq_norm) fs_init)" 
  shows "cost (reduce_basis_cost fs_init)
  \<le> (4 * m * m + 3 * m + (4 * m * m + 8 * m) * (1 + 2 * m * Log)) * n * arith_cost"
  unfolding assms A_def[symmetric]
  using reduce_basis_cost(2)[unfolded num_loops_def body_cost_def initial_gso_cost_def base_def]
  by (auto simp: nat_distrib ac_simps) *)

end (* fixing arith_cost and assume \<alpha> > 4/3 *)
end (* LLL locale *)
end (* theory *)