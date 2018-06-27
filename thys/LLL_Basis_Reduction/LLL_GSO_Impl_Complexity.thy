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

theory LLL_GSO_Impl_Complexity
  imports 
    LLL_GSO_Impl
    Cost
begin

context LLL_with_assms
begin

context
  fixes arith_cost :: nat
  assumes \<alpha>_gt: "\<alpha> > 4/3" and m0: "m \<noteq> 0" 
begin

fun basis_reduction_add_rows_loop_cost where
  "basis_reduction_add_rows_loop_cost state [] = (state, 0)" 
| "basis_reduction_add_rows_loop_cost state ((fj,gj,ngj) # rest) = (
     let fi = fi_state state;
         c = round ((fi \<bullet>i gj) / ngj); \<comment> \<open>2n arithmetic operations in scalar product\<close>
         state' = (if c = 0 then state else upd_fi_state state (fi - c \<cdot>\<^sub>v fj)) 
            \<comment> \<open>2n arithmetic operations in subtraction and scalar multiplication\<close>
      in case basis_reduction_add_rows_loop_cost state' rest of (state'',c_rec) \<Rightarrow> (state'', c_rec + (2 + 2) * n * arith_cost))" 

lemma basis_reduction_add_rows_loop_cost: 
   "result (basis_reduction_add_rows_loop_cost state xs) = basis_reduction_add_rows_loop state xs"  
   "cost (basis_reduction_add_rows_loop_cost state xs) \<le> length xs * (4 * n * arith_cost)" 
proof (atomize(full), induct xs arbitrary: state)
  case (Cons fgn xs state)
  obtain f g n where fgn: "fgn = (f,g,n)" by (cases fgn, auto)
  let ?fi = "fi_state state"
  let ?c = "round ((?fi \<bullet>i g) / n)" 
  let ?state' = "if ?c = 0 then state else upd_fi_state state (?fi - ?c \<cdot>\<^sub>v f)" 
  obtain state'' c_rec where rec: "basis_reduction_add_rows_loop_cost ?state' xs = (state'', c_rec)" (is "?rec = _")
    by (cases ?rec, auto)
  show ?case unfolding basis_reduction_add_rows_loop_cost.simps basis_reduction_add_rows_loop.simps 
    fgn Let_def rec split using Cons[of ?state', unfolded rec] by (auto simp: cost_simps)
qed (auto simp: cost_simps)

definition basis_reduction_add_rows_cost where
  "basis_reduction_add_rows_cost upw state = 
     (if upw then basis_reduction_add_rows_loop_cost state (small_fs_gso_norms state) 
       else (state,0))" 

lemma basis_reduction_add_rows_cost: assumes impl: "LLL_impl_inv state i fs"
  shows "result (basis_reduction_add_rows_cost upw state) = basis_reduction_add_rows upw state"  
   "cost (basis_reduction_add_rows_cost upw state) \<le> 4 * m * n * arith_cost" 
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
    from to_list_repr[OF impl] 
    have len: "length (small_fs_gso_norms state) \<le> m" 
      unfolding small_fs_gso_norms_def list_repr_def by auto
    hence le: "4 * length (small_fs_gso_norms state) * n * arith_cost \<le> 4 * m * n * arith_cost" 
      by (intro mult_mono, auto)
    show ?thesis unfolding d upw if_True 
      using basis_reduction_add_rows_loop_cost[of state "small_fs_gso_norms state"] le
      by (auto simp: ac_simps intro: le_trans)
  qed
qed

definition basis_reduction_swap_cost where
  "basis_reduction_swap_cost i state = (let 
       ni = ni_state state;
       nim1 = nim1_state state;
       fi = fi_state state;
       fim1 = fim1_state state;
       gi = gi_state state;
       gim1 = gim1_state state;
       mu = (fi \<bullet>i gim1) / nim1; \<comment> \<open>2n arithmetic operations: scalar product\<close>
       fi' = fim1;
       fim1' = fi;
       gim1' = gi + mu \<cdot>\<^sub>v gim1; \<comment> \<open>2n arithmetic operations: addition and scalar multiplication\<close>
       nim1' = ni + square_rat mu * nim1;
       gi' = gim1 - ((fim1 \<bullet>i gim1') / nim1') \<cdot>\<^sub>v gim1'; \<comment> \<open>4n arithmetic operations: minus, scalar prod and scalar mult\<close>
       ni' = ni * nim1 / nim1'
     in ((False, i - 1, dec_i (update_im1 (update_i state (fi',gi',ni')) (fim1',gim1',nim1'))), 
       (2 + 2 + 4) * n * arith_cost))" 

lemma basis_reduction_swap_cost: 
   "result (basis_reduction_swap_cost i state) = basis_reduction_swap i state"  
   "cost (basis_reduction_swap_cost i state) \<le> 8 * n * arith_cost" 
  by (auto simp: basis_reduction_swap_def basis_reduction_swap_cost_def Let_def cost_simps)

definition basis_reduction_step_cost where
  "basis_reduction_step_cost upw i state = (if i = 0 then ((True, Suc i, inc_i state), 0) \<comment> \<open>0 costs\<close>
     else case basis_reduction_add_rows_cost upw state
       of (state', c_add) \<Rightarrow> let 
       ni = ni_state state';
       nim1 = nim1_state state'
    in if nim1 \<le> \<alpha> * ni then
          ((True, Suc i, inc_i state'), c_add) 
        else case basis_reduction_swap_cost i state' of (state'', c_swap) \<Rightarrow> (state'', c_add + c_swap))" 

definition "body_cost = (4 * m + 8) * n * arith_cost" 

lemma basis_reduction_step_cost: assumes 
    impl: "LLL_impl_inv state i fs" 
  and inv: "LLL_invariant upw i fs" 
  shows "result (basis_reduction_step_cost upw i state) = basis_reduction_step \<alpha> upw i state" (is ?g1)
     "cost (basis_reduction_step_cost upw i state) \<le> body_cost" (is ?g2)
proof -
  obtain state' c_add where add: "basis_reduction_add_rows_cost upw state = (state',c_add)" 
    (is "?add = _") by (cases ?add, auto)
  obtain state'' c_swap where swap: "basis_reduction_swap_cost i state' = (state'',c_swap)" 
    (is "?swap = _") by (cases ?swap, auto)
  note res = basis_reduction_step_cost_def[of upw i state, unfolded add split swap]
  from basis_reduction_add_rows_cost[OF impl, of upw, unfolded add]
  have add: "basis_reduction_add_rows upw state = state'" 
    and c_add: "c_add \<le> 4 * m * n * arith_cost" 
    by (auto simp: cost_simps)
  from basis_reduction_swap_cost[of i state', unfolded swap cost_simps]
  have swap: "basis_reduction_swap i state' = state''" 
    and c_swap: "c_swap \<le> 8 * n * arith_cost" by auto
  note res' = basis_reduction_step_def[of \<alpha> upw i state, unfolded add swap Let_def]
  note d = res res'
  show ?g1 unfolding d by (auto split: if_splits simp: cost_simps)
  show ?g2 unfolding d nat_distrib body_cost_def using c_add c_swap by (auto split: if_splits simp: cost_simps)
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
  from basis_reduction_step_cost[OF impl inv, unfolded * cost_simps]
  have "basis_reduction_step \<alpha> upw i state = (upw',i',state')" by auto
  from basis_reduction_step[OF impl inv this i refl]
  show ?case by simp
qed

declare basis_reduction_main_cost.simps[simp del]

definition "num_loops = m + 2 * m * m * nat (ceiling (log base (real A)))"

lemma basis_reduction_main_cost: assumes impl: "LLL_impl_inv state i (fs_state state)" 
  and inv: "LLL_invariant upw i (fs_state state)" 
  and state: "state = initial_state n fs_init" 
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
    from basis_reduction_step_cost[OF impl inv, unfolded step cost_simps]
    have step': "basis_reduction_step \<alpha> upw i state = (upw',i',state')"
     and c_step: "c_step \<le> body_cost" 
      by auto
    note d = basis_reduction_main_cost.simps[of upw] step split rec 
        basis_reduction_main.simps[of _ _ upw] step'
    show ?case 
    proof (cases "i < m")
      case i: True
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
    from fs_state[OF initial_state] LLL_invD(6)[OF LLL_inv_initial_state]
    have fs: "fs_state (initial_state n fs_init) = fs_init" by auto
    have "LLL_measure i (fs_state state) \<le> nat (ceiling (m + k * l))" unfolding l_def k_def
      using LLL_measure_approx_fs_init[OF LLL_inv_initial_state \<alpha>_gt m0] unfolding state fs i
      by linarith
    also have "\<dots> \<le> num_loops" unfolding num_loops_def l_def[symmetric] k_def[symmetric]
      by (simp add: of_nat_ceiling times_right_mono)
    finally show "LLL_measure i (fs_state state) \<le> num_loops" .
  qed
  finally show ?g2 .
qed

fun adjuster_triv_cost :: "'a :: trivial_conjugatable_ordered_field vec \<Rightarrow> ('a vec \<times> 'a) list \<Rightarrow> 'a vec cost" where 
  "adjuster_triv_cost w [] = (0\<^sub>v n, 0)" \<comment> \<open>0 cost\<close>
| "adjuster_triv_cost w ((u,nu)#us) = (case adjuster_triv_cost w us of (res,c1)
     \<Rightarrow> let c2 = 4 * n * arith_cost in \<comment> \<open>2n for scalar-prod, n for scalar-mult and n for vector addition\<close>
      ((-(w \<bullet> u)/ nu \<cdot>\<^sub>v u) + res, c1 + c2))"

lemma adjuster_triv_cost: "result (adjuster_triv_cost w xs) = adjuster_triv n w xs"
  "cost (adjuster_triv_cost w xs) \<le> 4 * length xs * n * arith_cost" 
proof (atomize(full), induct xs)
  case (Cons unu us)
  obtain u nu where unu: "unu = (u,nu)" by force
  obtain res c1 where rec: "adjuster_triv_cost w us = (res,c1)" (is "?adj = _") by (cases ?adj, auto)
  show ?case using Cons
    unfolding unu adjuster_triv_cost.simps adjuster_triv.simps rec split Let_def cost_simps
    by (auto simp: nat_distrib)
qed (auto simp: cost_simps)

fun gram_schmidt_sub_triv_cost
  where "gram_schmidt_sub_triv_cost us [] = (let cost = 0 in (us, cost))"
  | "gram_schmidt_sub_triv_cost us (w # ws) = (
     case adjuster_triv_cost w us of (adj,c1) \<Rightarrow> 
      let u = adj + w in \<comment> \<open>n ops\<close>
      let sqn = sq_norm u in \<comment> \<open>2n ops\<close>
      let c2 = 3 * n * arith_cost in
     case gram_schmidt_sub_triv_cost ((u, sqn) # us) ws of (res,c3) \<Rightarrow>
       (res, c1 + c2 + c3))"

lemma gram_schmidt_sub_triv_cost: assumes "length us + length ws \<le> m" 
  shows "result (gram_schmidt_sub_triv_cost us ws) = gram_schmidt_sub_triv n us ws" (is ?g1)
  "cost (gram_schmidt_sub_triv_cost us ws) \<le> (4 * m + 3) * m * n * arith_cost" (is ?g2)
proof -
  have main: "?g1 \<and> cost (gram_schmidt_sub_triv_cost us ws) \<le> (4 * m + 3) * length ws * n * arith_cost" 
    using assms
  proof (induct ws arbitrary: us)
    case (Cons w ws us)
    obtain adj c1 where adj: "adjuster_triv_cost w us = (adj,c1)" (is "?adj = _") by (cases ?adj, auto)  
    from adjuster_triv_cost[of w us, unfolded adj cost_simps]
    have adj': "adjuster_triv n w us = adj" and c1: "c1 \<le> 4 * length us * n * arith_cost" by auto
    note c1
    also have "4 * length us * n * arith_cost \<le> 4 * m * n * arith_cost" using Cons(2)
      by (auto simp: nat_distrib)
    finally have c1: "c1 \<le> 4 * m * n * arith_cost" .
    let ?us = "((adj + w, \<parallel>adj + w\<parallel>\<^sup>2) # us)" 
    from Cons(2) have "length ?us + length ws \<le> m" by auto
    note IH = Cons(1)[OF this]
    obtain c3 res where rec: "gram_schmidt_sub_triv_cost ?us ws = (res,c3)" (is "?rec = _") by (cases ?rec, auto)
    note d = gram_schmidt_sub_triv_cost.simps gram_schmidt_sub_triv.simps adj split adj'
      Let_def rec cost_simps
    have c3: "c3 \<le> (4 * m + 3) * length ws * n * arith_cost" 
      using IH[unfolded d] by auto
    have "cost (gram_schmidt_sub_triv_cost us (w # ws)) = (c1 + 3 * n * arith_cost) + c3" 
      unfolding d by auto
    also have "\<dots> \<le> (4 * m + 3) * length (w # ws) * n * arith_cost" 
      using c1 c3 by (auto simp: nat_distrib)
    finally have cost: "cost (gram_schmidt_sub_triv_cost us (w # ws)) \<le> (4 * m + 3) * length (w # ws) * n * arith_cost" 
      by auto
    show ?case using IH cost unfolding d by auto
  qed (auto simp: cost_simps)
  thus ?g1 by blast
  from main have "cost (gram_schmidt_sub_triv_cost us ws) \<le> (4 * m + 3) * length ws * n * arith_cost" by auto
  also have "\<dots> \<le> (4 * m + 3) * m * n * arith_cost" using assms by auto
  finally show ?g2 .
qed

definition gram_schmidt_triv_cost :: "'a :: trivial_conjugatable_ordered_field vec list \<Rightarrow> ('a vec \<times> 'a) list cost"
  where "gram_schmidt_triv_cost ws = (case gram_schmidt_sub_triv_cost [] ws of (res,c) \<Rightarrow> (rev res, c))" 

lemma gram_schmidt_triv_cost: assumes "length ws \<le> m" 
  shows "result (gram_schmidt_triv_cost ws) = gram_schmidt_triv n ws" (is ?g1)
  "cost (gram_schmidt_triv_cost ws) \<le> (4 * m + 3) * m * n * arith_cost" (is ?g2)
proof -
  let ?us = "Nil :: ('a vec \<times> 'a) list" 
  obtain res c where sub: "gram_schmidt_sub_triv_cost ?us ws = (res,c)" (is "?sub = _") by (cases ?sub, auto) 
  from assms have "length ?us + length ws \<le> m" by auto
  note subc = gram_schmidt_sub_triv_cost[OF this, unfolded sub cost_simps]
  show ?g1 ?g2 unfolding gram_schmidt_triv_cost_def sub split cost_simps gram_schmidt_triv_def subc(1)[symmetric]
    using subc(2) by auto
qed

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
  by (auto simp: nat_distrib ac_simps)
end (* fixing arith_cost and assume \<alpha> > 4/3 *)
end (* LLL locale *)
end (* theory *)