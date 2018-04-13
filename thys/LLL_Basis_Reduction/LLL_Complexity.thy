(*
    Authors:    Maximilian Haslbeck
                René Thiemann
    License:    BSD
*)
section \<open>Complexity of the LLL algorithm\<close>

text \<open>In this section we define a version of the LLL algorithm which explicitly returns the
  costs of running the algorithm. Its soundness is mainly proven by stating that 
  projecting away yields the original result.

  The cost model counts the number of arithmetic operations that occur in vector-addition, scalar-products,
  and scalar multiplication and we prove a polynomial bound on this number.\<close>

theory LLL_Complexity
  imports LLL 
begin

type_synonym 'a cost = "'a \<times> nat" 

definition cost :: "'a cost \<Rightarrow> nat" where "cost = snd" 
definition result :: "'a cost \<Rightarrow> 'a" where "result = fst" 

lemma cost_simps: "cost (a,c) = c" "result (a,c) = a" 
  unfolding cost_def result_def by auto

context LLL
begin

context
  fixes arith_cost :: nat
  assumes \<alpha>: "\<alpha> > 4/3" and m0: "m \<noteq> 0" 
begin

private lemma alpha: "\<alpha> \<ge> 4/3" using \<alpha> by auto

fun basis_reduction_add_row_main_cost :: "state \<Rightarrow> int vec \<Rightarrow> rat \<Rightarrow> (state \<times> int) cost" where 
  "basis_reduction_add_row_main_cost (i,F,G) fj mu = (let     
     c = floor_ceil mu \<comment> \<open>ignore costs for this computation\<close>
     in if c = 0 then let costs = 0 in
       (((i,F,G), c), costs)
     else 
     let 
     fi = get_nth_i F - (c \<cdot>\<^sub>v fj);
     F' = update_i F fi;
     costs = n * arith_cost \<comment> \<open>n arithmetic operations in scalar-multiplication\<close>
     in (((i,F',G), c), costs))"

lemma basis_reduction_add_row_main_cost: 
   "result (basis_reduction_add_row_main_cost state fj mu) = basis_reduction_add_row_main state fj mu"  
   "cost (basis_reduction_add_row_main_cost state fj mu) \<le> n * arith_cost" 
  by (cases "state", auto simp: Let_def cost_simps)+

definition \<mu>_ij_cost :: "int vec \<Rightarrow> rat vec \<times> rat \<Rightarrow> rat cost" where
  "\<mu>_ij_cost fi gj_norm = (let cost = 2 * n * arith_cost 
    in \<comment> \<open>2n arithmetic operations in scalar-product\<close>
    case gj_norm of (gj,norm_gj) \<Rightarrow> ((fi \<bullet>i gj) / norm_gj, cost))" 

lemma \<mu>_ij_cost:  
   "result (\<mu>_ij_cost fi gj_norm) = \<mu>_ij fi gj_norm"  
   "cost (\<mu>_ij_cost fi gj_norm) \<le> 2* n * arith_cost" 
  unfolding \<mu>_ij_cost_def \<mu>_ij_def Let_def by (cases gj_norm, auto simp: cost_simps)+

definition "\<mu>_i_im1_cost Fr Gr = (let cost = 2 * n * arith_cost 
  in \<comment> \<open>2n arithmetic operations in scalar-product\<close>
  ((get_nth_i Fr \<bullet>i g_im1 Gr) / sqnorm_g_im1 Gr, cost))" 

lemma \<mu>_i_im1_cost:  
   "result (\<mu>_i_im1_cost fr gr) = \<mu>_i_im1 fr gr"  
   "cost (\<mu>_i_im1_cost fr gr) \<le> 2 * n * arith_cost" 
  unfolding \<mu>_i_im1_cost_def \<mu>_i_im1_def Let_def by (auto simp: cost_simps)

fun basis_reduction_add_row_i_all_main_cost :: "state \<Rightarrow> int vec list \<Rightarrow> (rat vec \<times> rat) list \<Rightarrow> state cost" where
  "basis_reduction_add_row_i_all_main_cost state (Cons fj fjs) (Cons gj gjs) = (case state of (i,F,G) \<Rightarrow> 
    let fi = get_nth_i F in
    case \<mu>_ij_cost fi gj of (mu, c1) \<Rightarrow> 
    case basis_reduction_add_row_main_cost state fj mu of (res,c2) \<Rightarrow>
    case basis_reduction_add_row_i_all_main_cost (fst res) fjs gjs of (state, c3) \<Rightarrow>
      (state, c1 + c2 + c3))"
| "basis_reduction_add_row_i_all_main_cost state _ _ = (let costs = 0 in (state,costs))" 

lemma basis_reduction_add_row_i_all_main_cost: 
   "result (basis_reduction_add_row_i_all_main_cost state fjs gjs) = basis_reduction_add_row_i_all_main state fjs gjs"  
   "cost (basis_reduction_add_row_i_all_main_cost state fjs gjs) \<le> 3 * length fjs * n * arith_cost" 
proof (atomize (full), induct fjs arbitrary: gjs state)
  case (Cons fj fjs gs)
  show ?case 
  proof (cases gs)
    case gs: (Cons gj gjs)
    obtain i F G where state: "state = (i, F, G)" by (cases state, auto)
    let ?fi = "get_nth_i F"
    obtain mu c1 where mu: "\<mu>_ij_cost ?fi gj = (mu, c1)" (is "?mu = _") by (cases ?mu, auto)
    obtain res c2 where row: "basis_reduction_add_row_main_cost (i, F, G) fj mu = (res, c2)" (is "?row = _") 
      by (cases ?row, auto)
    obtain state c3 where rec: "basis_reduction_add_row_i_all_main_cost (fst res) fjs gjs = (state, c3)" (is "?rec = _")
      by (cases ?rec, auto)    
    from \<mu>_ij_cost[of ?fi gj, unfolded mu cost_simps]
    have mu': "\<mu>_ij (get_nth_i F) gj = mu" and c1: "c1 \<le> 2 * n * arith_cost" by auto
    from basis_reduction_add_row_main_cost[of "(i,F,G)" fj mu, unfolded row cost_simps]
    have row': "basis_reduction_add_row_main (i, F, G) fj mu = res" and c2: "c2 \<le> n * arith_cost" by auto
    from Cons[of "fst res" gjs, unfolded rec cost_simps] 
    have rec': "basis_reduction_add_row_i_all_main (fst res) fjs gjs = state" and 
      c3: "c3 \<le> 3 * length fjs * n * arith_cost" by auto
    have c: "c1 + c2 + c3 \<le> 3 * length (fj # fjs) * n * arith_cost" using c1 c2 c3 
      by (auto simp: distrib_right)  
    show ?thesis 
      unfolding basis_reduction_add_row_i_all_main_cost.simps 
        basis_reduction_add_row_i_all_main.simps gs state split mu Let_def row rec cost_simps 
        mu' row' rec' using c by auto
  qed (auto simp: cost_simps)
qed (auto simp: cost_simps)

fun basis_reduction_swap_cost :: "state \<Rightarrow> state cost" where
  "basis_reduction_swap_cost (i,F,G) = (
    case \<mu>_i_im1_cost F G of (mu,c1) \<Rightarrow>
    let
      gi = g_i G; 
      gim1 = g_im1 G;
      fi = get_nth_i F;
      fim1 = get_nth_im1 F;
      new_gim1 = gi + mu \<cdot>\<^sub>v gim1; \<comment> \<open>2n arithmetic operations in scalar-product and addition\<close>
      norm_gim1 = sq_norm new_gim1; \<comment> \<open>2n arithmetic operations to compute squared norm\<close>
      new_gi = gim1 - (fim1 \<bullet>i new_gim1 / norm_gim1) \<cdot>\<^sub>v new_gim1; \<comment> \<open>4n arithmetic operations: minus, scalar-prod and scalar-mult\<close>
      norm_gi = sq_norm new_gi; \<comment> \<open>2n arithmetic operations to compute squared norm\<close>
      G' = dec_i (update_im1 (update_i G (new_gi,norm_gi)) (new_gim1,norm_gim1));
      F' = dec_i (update_im1 (update_i F fim1) fi);
      c2 = (2 + 2 + 4 + 2) * n * arith_cost
    in ((i - 1, F', G'), c1 + c2))"

lemma basis_reduction_swap_cost: 
   "result (basis_reduction_swap_cost state) = basis_reduction_swap state"  
   "cost (basis_reduction_swap_cost state) \<le> 12 * n * arith_cost" 
proof (atomize(full), goal_cases)
  case 1
  obtain i F G where state: "state = (i,F,G)" by (cases state, auto)
  obtain mu c1 where mu: "\<mu>_i_im1_cost F G = (mu,c1)" (is "?mu = _") by (cases ?mu, auto)
  from \<mu>_i_im1_cost[of F G, unfolded mu cost_simps]
  have mu': "\<mu>_i_im1 F G = mu" and c1: "c1 \<le> 2 * n * arith_cost" by auto
  show ?case unfolding state basis_reduction_swap_cost.simps 
    basis_reduction_swap.simps mu split Let_def mu' cost_simps
    by (intro conjI[OF refl], insert c1, auto simp: ac_simps)
qed
  
definition basis_reduction_add_rows_cost :: "state \<Rightarrow> state cost" where 
  "basis_reduction_add_rows_cost state = (case state of (i,F,G) \<Rightarrow>
    let fjs = fst F;
        gjs = fst G
      in basis_reduction_add_row_i_all_main_cost state fjs gjs)" 

lemma basis_reduction_add_rows_cost: assumes "LLL_invariant A state F G" 
  shows "result (basis_reduction_add_rows_cost state) = basis_reduction_add_rows state" (is ?g1)
     "cost (basis_reduction_add_rows_cost state) \<le> 4 * m * n * arith_cost" (is ?g2)
proof -
  obtain i Fr Gr where state: "state = (i, Fr, Gr)" by (cases state, auto)
  show ?g1 unfolding basis_reduction_add_rows_cost_def state split Let_def basis_reduction_add_rows_def
    by (simp add: basis_reduction_add_row_i_all_main_cost)
  from LLL_invD(1,4)[OF assms[unfolded state]] have len: "length (fst Fr) \<le> m"
    unfolding of_list_repr_def by auto
  show ?g2 unfolding basis_reduction_add_rows_cost_def state split Let_def
    by (rule order.trans, rule basis_reduction_add_row_i_all_main_cost, insert len, auto)
qed

definition basis_reduction_step_cost :: "state \<Rightarrow> state cost" where
  "basis_reduction_step_cost state = (if fst state = 0 then (let c = 0 in (increase_i state, c))
     else case basis_reduction_add_rows_cost state of (state',c1) \<Rightarrow>
     case state' of (i, F, G) \<Rightarrow>
      if sqnorm_g_im1 G > \<alpha> * sqnorm_g_i G 
      then case basis_reduction_swap_cost state' of (state'',c2) \<Rightarrow> (state'', c1 + c2)
      else (increase_i state', c1)
     )" 

definition "body_cost = (4 * m + 12) * n * arith_cost" 

lemma basis_reduction_step_cost: assumes "LLL_invariant A state F G" 
  shows "result (basis_reduction_step_cost state) = basis_reduction_step \<alpha> state" (is ?g1)
     "cost (basis_reduction_step_cost state) \<le> body_cost" (is ?g2)
proof -
  obtain state' c1 where add: "basis_reduction_add_rows_cost state = (state',c1)" (is "?add = _") by (cases ?add, auto)
  obtain i F G where state': "state' = (i,F,G)" by (cases state', auto)
  obtain state'' c2 where swap: "basis_reduction_swap_cost (i,F,G) = (state'',c2)" (is "?swap = _") by (cases ?swap, auto)
  from basis_reduction_add_rows_cost[OF assms, unfolded add cost_simps]
  have add': "basis_reduction_add_rows state = state'" 
    and c1: "c1 \<le> 4 * m * n * arith_cost" by auto
  from basis_reduction_swap_cost[of "(i,F,G)", unfolded swap cost_simps]
  have swap': "basis_reduction_swap (i, F, G) = state''" 
    and c2: "c2 \<le> 12 * n * arith_cost" by auto
  note d = basis_reduction_step_cost_def basis_reduction_step_def Let_def add split swap 
      state' add' swap'
  show ?g1 unfolding d by (auto split: if_splits simp: cost_simps)
  show ?g2 unfolding d nat_distrib body_cost_def using c1 c2 by (auto split: if_splits simp: cost_simps)
qed

function basis_reduction_main_cost :: "state \<Rightarrow> state cost" where
  "basis_reduction_main_cost state = (
     case state of (i,F,G) \<Rightarrow>
     if i < m \<and> (\<exists> A FF GG. LLL_invariant A state FF GG) 
       \<comment> \<open>The check on the invariant is just to be able to prove termination. 
          One cannot use partial-function at this point, since the function with cost is not tail-recursive.\<close>
     then case basis_reduction_step_cost state of 
       (state1,c1) \<Rightarrow> 
       case basis_reduction_main_cost state1 of
       (state2,c2) \<Rightarrow> (state2, c1 + c2)
     else (state, 0))"
  by pat_completeness auto

termination
proof (standard, rule wf_measure[of LLL_measure], goal_cases)
  case (1 state i FG F G state1 c1)
  note * = 1(1)[symmetric] 1(2)[symmetric] 1(3) 1(4)[symmetric]
  from * obtain FF GG A where i: "i < m" and inv: "LLL_invariant A (i, F, G) FF GG" by auto
  from basis_reduction_step_cost[OF inv, unfolded *] 
  have res: "basis_reduction_step \<alpha> (i, F, G) = state1" using * cost_simps(2) by metis
  from basis_reduction_step[OF alpha inv i res]
  show ?case unfolding * by auto
qed

declare basis_reduction_main_cost.simps[simp del]

definition "num_loops A = m + 2 * m * m * nat (ceiling (log (4 * of_rat \<alpha> / (4 + of_rat \<alpha>)) (real A)))"

lemma basis_reduction_main_cost: fixes F G assumes "LLL_invariant A state F G"
  shows "result (basis_reduction_main_cost state) = basis_reduction_main \<alpha> m state" (is ?g1) 
   "cost (basis_reduction_main_cost state) \<le> body_cost * num_loops A" (is ?g2)
proof -
  have inv: "LLL_partial_invariant A state F G" using assms unfolding LLL_invariant_def by auto
  have ?g1 and cost: "cost (basis_reduction_main_cost state) \<le> body_cost * LLL_measure state"
    using assms
  proof (atomize (full), induct state arbitrary: F G rule: wf_induct[OF wf_measure[of LLL_measure]])
    case (1 state F G)
    note inv = 1(2)
    have ex: "(\<exists>A FF. Ex (LLL_invariant A state FF)) = True" using inv by auto
    note IH = 1(1)[rule_format]
    obtain i Fr1 Gr1 where state: "state = (i,Fr1,Gr1)" by (cases state, auto)
    note inv = inv[unfolded state]
    note simp = basis_reduction_main_cost.simps[of state, unfolded state split, folded state, unfolded ex]
    show ?case
    proof (cases "i < m")
      case i: True
      obtain c1 state1 where b: "basis_reduction_step_cost (i, Fr1, Gr1) = (state1, c1)" (is "?b = _")
        by (cases ?b, auto)
      note simp = simp[unfolded state b split, folded state]
      from basis_reduction_step_cost[OF inv, unfolded state b cost_simps]
      have c1: "c1 \<le> body_cost" and bb: "basis_reduction_step \<alpha> (i, Fr1, Gr1) = state1" by auto
      obtain c2 state2 where rec: "basis_reduction_main_cost state1 = (state2, c2)" (is "?rec = _")
        by (cases ?rec, auto)
      note simp = simp[unfolded rec split]
      from simp i have res: "basis_reduction_main_cost state = (state2, c1 + c2)" by auto    
      note bsr = basis_reduction_step[OF alpha inv i bb]
      from bsr(1) obtain F' G' where inv: "LLL_invariant A state1 F' G'" by auto
      from bsr(2) have "(state1 ,state) \<in> measure LLL_measure" by (auto simp: state)
      from IH[OF this inv, unfolded rec cost_simps]
      have res': "basis_reduction_main \<alpha> m state1 = state2" 
        and c2: "c2 \<le> body_cost * LLL_measure state1" by auto
      have res': "basis_reduction_main \<alpha> m state = state2"
        unfolding basis_reduction_main.simps[of _ _ state] unfolding split b state bb res' using i by auto
      from bsr(2)[folded state] obtain k where meas: "LLL_measure state = Suc (LLL_measure state1) + k" 
        and "k = LLL_measure state - Suc (LLL_measure state1)" by simp 
      show ?thesis unfolding res' res cost_simps
        by (intro conjI[OF refl], rule order.trans[OF add_mono[OF c1 c2]], unfold meas, auto)
    next
      case False
      thus ?thesis unfolding simp basis_reduction_main.simps[of _ _ state] unfolding state split
        by (auto simp: cost_simps)
    qed
  qed
  show ?g1 by fact
  obtain i F G where state: "state = (i, F, G)" by (cases state, auto)
  note cost also have "body_cost * LLL_measure state \<le> body_cost * num_loops A" 
  proof (rule mult_left_mono; linarith?)
    define l where "l = log (4 * real_of_rat \<alpha> / (4 + real_of_rat \<alpha>)) (real A)" 
    define k where "k = 2 * m * m" 
    have "LLL_measure state \<le> nat (ceiling (m + k * l))" unfolding l_def k_def
      using LLL_measure_approx[OF alpha inv[unfolded state] \<alpha> m0, folded state] by linarith
    also have "\<dots> \<le> num_loops A" unfolding num_loops_def l_def[symmetric] k_def[symmetric]
      by (simp add: of_nat_ceiling times_right_mono)
    finally show "LLL_measure state \<le> num_loops A" .
  qed
  finally show ?g2 . 
qed

fun adjuster_triv_cost :: "'a :: trivial_conjugatable_ordered_field vec \<Rightarrow> ('a vec \<times> 'a) list \<Rightarrow> 'a vec cost"
  where "adjuster_triv_cost w [] = (let cost = 0 in (0\<^sub>v n, cost))"
  |  "adjuster_triv_cost w ((u,nu)#us) = (case adjuster_triv_cost w us of (res,c1)
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

definition initial_state_cost :: "int vec list \<Rightarrow> state cost" where
  "initial_state_cost F = (case gram_schmidt_triv_cost (map (map_vec of_int) F)
     of (G,c) \<Rightarrow> ((0, ([], F), ([], G)), c))" 

definition basis_reduction_state_cost :: "int vec list \<Rightarrow> state cost" where 
  "basis_reduction_state_cost F = (
    case initial_state_cost F of (state1, c1) \<Rightarrow> 
    case basis_reduction_main_cost state1 of (state2, c2) \<Rightarrow> 
      (state2, c1 + c2))" 

definition reduce_basis_cost :: "int vec list \<Rightarrow> int vec list cost" where
  "reduce_basis_cost F = (case basis_reduction_state_cost F of (state,c) \<Rightarrow> 
    ((of_list_repr o fst o snd) state, c))" 

definition "max_sqnorm (F :: int vec list) = max_list (map (nat o sq_norm) F)" 

context
  fixes F :: "int vec list" 
  assumes len: "length F = m"
  and lin_dep: "gs.lin_indpt_list (RAT F)" 
  and L: "lattice_of F = L" 
begin

lemma initial_state_cost: "result (initial_state_cost F) = initial_state n F" (is ?g1)
  "cost (initial_state_cost F) \<le> initial_gso_cost" (is ?g2)
proof -
  let ?F = "map (map_vec rat_of_int) F" 
  have len: "length ?F \<le> m" using len by auto
  obtain G c where gso: "gram_schmidt_triv_cost ?F = (G,c)" (is "?gso = _")
    by (cases ?gso, auto)
  note gsoc = gram_schmidt_triv_cost[OF len, unfolded gso cost_simps]
  show ?g1 ?g2 unfolding initial_gso_cost_def initial_state_cost_def gso split cost_simps 
    initial_state_def Let_def gsoc(1)[symmetric] using gsoc(2) by auto
qed

lemma basis_reduction_state_cost: 
   "result (basis_reduction_state_cost F) = basis_reduction_state n \<alpha> F"  (is ?g1)
   "cost (basis_reduction_state_cost F) \<le> initial_gso_cost + body_cost * num_loops (max_sqnorm F)" (is ?g2)
proof -
  obtain state1 c1 where init: "initial_state_cost F = (state1, c1)" (is "?init = _") by (cases ?init, auto)
  obtain state2 c2 where main: "basis_reduction_main_cost state1 = (state2, c2)" (is "?main = _") by (cases ?main, auto)
  have res: "basis_reduction_state_cost F = (state2, c1 + c2)" 
    unfolding basis_reduction_state_cost_def init main split by simp
  from initial_state_cost[unfolded init cost_simps]
  have c1: "c1 \<le> initial_gso_cost" and init: "initial_state n F = state1" by auto
  from initial_state[OF alpha lin_dep len L init refl, folded max_sqnorm_def]
  obtain F' G' where inv: "LLL_invariant (max_sqnorm F) state1 F' G'" by auto
  from basis_reduction_main_cost[OF inv, unfolded main cost_simps]
  have main: "basis_reduction_main \<alpha> m state1 = state2" and c2: "c2 \<le> body_cost * num_loops (max_sqnorm F)" 
    by auto
  have res': "basis_reduction_state n \<alpha> F = state2" unfolding basis_reduction_state_def len init main ..
  show ?g1 unfolding res res' cost_simps ..
  show ?g2 unfolding res cost_simps using c1 c2 by auto
qed

text \<open>The lemma for the LLL algorithm with explicit cost annotations @{const reduce_basis_cost}
  shows that the termination measure
  indeed gives rise to an explicit cost bound. Moreover, the computed result is
  the same as in the non-cost counting @{const reduce_basis}.\<close>

lemma reduce_basis_cost: 
   "result (reduce_basis_cost F) = fst (reduce_basis n \<alpha> F)"  (is ?g1)
   "cost (reduce_basis_cost F) \<le> initial_gso_cost + body_cost * num_loops (max_sqnorm F)" (is ?g2)
proof -
  obtain state c where b: "basis_reduction_state_cost F = (state,c)" (is "?b = _") by (cases ?b, auto)
  from basis_reduction_state_cost[unfolded b cost_simps]
  have bb: "basis_reduction_state n \<alpha> F = state" and c: "c \<le> initial_gso_cost + body_cost * num_loops (max_sqnorm F)" 
    by auto
  show ?g1 ?g2 unfolding reduce_basis_cost_def reduce_basis_def b bb split cost_simps fst_conv using c by auto
qed

text \<open>Theorem with expanded costs: $O(n\cdot m^3 \cdot \log (\mathit{maxnorm}\ F))$ arithmetic operations\<close>
lemma reduce_basis_cost_full: 
  "cost (reduce_basis_cost F)
  \<le> (4 * m * m + 3 * m  +
     (4 * m * m + 12 * m) * 
      (1 + 2 * m * nat \<lceil>log (4 * real_of_rat \<alpha> / (4 + real_of_rat \<alpha>)) 
         (real (max_list (map (nat \<circ> sq_norm) F)))\<rceil>))
     * n * arith_cost"
  using reduce_basis_cost(2)[unfolded num_loops_def max_sqnorm_def body_cost_def initial_gso_cost_def]
  by (auto simp: nat_distrib ac_simps)

end (* lin-indep F *)
end (* fixing arith_cost and assume \<alpha> > 4/3 *)
end (* LLL locale which fixes n m \<alpha> L *)

text \<open>Expanded theorem outside locale listing all preconditions\<close>
thm LLL.reduce_basis_cost_full[OF _ _ refl _ refl]
end (* theory *)