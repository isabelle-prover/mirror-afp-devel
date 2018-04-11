(*
    Authors:    Maximilian Haslbeck
                René Thiemann
    License:    BSD
*)
section \<open>Complexity of the LLL algorithm\<close>

text \<open>In this section we define a version of the LLL algorithm which explicitly returns the
  costs of running the algorithm. Its soundness is mainly proven by stating that 
  projecting away yields the original result.

  The cost model is quite basic. At the moment it uses a fixed parameter for the costs 
  of executing the body of the outer while-loop.\<close>

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
  fixes \<alpha> :: rat and L :: "int vec set"
  assumes \<alpha>: "\<alpha> > 4/3" and m0: "m \<noteq> 0" 
begin

private lemma alpha: "\<alpha> \<ge> 4/3" using \<alpha> by auto

context
  fixes body_cost initial_gso_cost :: nat
begin

definition basis_reduction_step_cost :: "state \<Rightarrow> state cost" where
  "basis_reduction_step_cost state = (basis_reduction_step \<alpha> state, body_cost)"

lemma basis_reduction_step_cost: "cost (basis_reduction_step_cost state) \<le> body_cost" 
  "result (basis_reduction_step_cost state) = basis_reduction_step \<alpha> state" 
  unfolding basis_reduction_step_cost_def cost_simps by auto

function basis_reduction_main_cost :: "state \<Rightarrow> state cost" where
  "basis_reduction_main_cost state = (
     case state of (i,F,G) \<Rightarrow>
     if i < m \<and> (\<exists> A FF GG. LLL_invariant L \<alpha> A state FF GG) 
       \<comment> \<open>The check on the invariant is just to be able to prove termination. 
          One cannot use partial-function at this point, since the function with cost is not tail-recursive.\<close>
     then case basis_reduction_step_cost state of 
       (state1,c1) \<Rightarrow> 
       case basis_reduction_main_cost state1 of
       (state2,c2) \<Rightarrow> (state2, c1 + c2)
     else (state, 0))"
  by pat_completeness auto

termination
proof (standard, rule wf_measure[of "LLL_measure \<alpha>"], goal_cases)
  case (1 state i FG F G state1 c1)
  note * = 1(1)[symmetric] 1(2)[symmetric] 1(3) 1(4)[symmetric]
  from * obtain FF GG A where i: "i < m" and inv: "LLL_invariant L \<alpha> A (i, F, G) FF GG" by auto
  from basis_reduction_step_cost[of state, unfolded *(4)] 
  have res: "basis_reduction_step \<alpha> (i, F, G) = state1" unfolding * cost_simps by auto
  from basis_reduction_step[OF alpha inv i res]
  show ?case unfolding * by auto
qed

declare basis_reduction_main_cost.simps[simp del]

definition "num_loops A = nat (ceiling (m + 2 * m * m * log (4 * of_rat \<alpha> / (4 + of_rat \<alpha>)) (real A)))"

lemma basis_reduction_main_cost: fixes F G assumes "LLL_invariant L \<alpha> A state F G"
  shows "result (basis_reduction_main_cost state) = basis_reduction_main \<alpha> m state" (is ?g1) 
   "cost (basis_reduction_main_cost state) \<le> body_cost * num_loops A" (is ?g2)
proof -
  have ?g1 and cost: "cost (basis_reduction_main_cost state) \<le> body_cost * LLL_measure \<alpha> state"
    using assms
  proof (atomize (full), induct state arbitrary: F G rule: wf_induct[OF wf_measure[of "LLL_measure \<alpha>"]])
    case (1 state F G)
    note inv = 1(2)
    have ex: "(\<exists>A FF. Ex (LLL_invariant L \<alpha> A state FF)) = True" using inv by auto
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
      from basis_reduction_step_cost[of state, unfolded state b cost_simps]
      have c1: "c1 \<le> body_cost" and bb: "basis_reduction_step \<alpha> (i, Fr1, Gr1) = state1" by auto
      obtain c2 state2 where rec: "basis_reduction_main_cost state1 = (state2, c2)" (is "?rec = _")
        by (cases ?rec, auto)
      note simp = simp[unfolded rec split]
      from simp i have res: "basis_reduction_main_cost state = (state2, c1 + c2)" by auto    
      note bsr = basis_reduction_step[OF alpha inv i bb]
      from bsr(1) obtain F' G' where inv: "LLL_invariant L \<alpha> A state1 F' G'" by auto
      from bsr(2) have "(state1 ,state) \<in> measure (LLL_measure \<alpha>)" by (auto simp: state)
      from IH[OF this inv, unfolded rec cost_simps]
      have res': "basis_reduction_main \<alpha> m state1 = state2" 
        and c2: "c2 \<le> body_cost * LLL_measure \<alpha> state1" by auto
      have res': "basis_reduction_main \<alpha> m state = state2"
        unfolding basis_reduction_main.simps[of _ _ state] unfolding split b state bb res' using i by auto
      from bsr(2)[folded state] obtain k where meas: "LLL_measure \<alpha> state = Suc (LLL_measure \<alpha> state1) + k" 
        and "k = LLL_measure \<alpha> state - Suc (LLL_measure \<alpha> state1)" by simp 
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
  note cost also have "body_cost * LLL_measure \<alpha> state \<le> body_cost * num_loops A" 
    by (rule mult_left_mono, unfold num_loops_def, insert 
    LLL_measure_approx[OF alpha assms[unfolded state] \<alpha> m0, folded state], linarith+)
  finally show ?g2 . 
qed

definition initial_state_cost :: "int vec list \<Rightarrow> state cost" where
  "initial_state_cost F = (let G = gram_schmidt_triv n (map (map_vec of_int) F);
     Fr = ([], F);
     Gr = ([], G)
     in ((0, Fr, Gr), initial_gso_cost))" 

lemma initial_state_cost: "cost (initial_state_cost F) \<le> initial_gso_cost" 
  "result (initial_state_cost F) = initial_state n F" 
  unfolding initial_state_cost_def initial_state_def Let_def cost_simps by auto

definition basis_reduction_state_cost :: "int vec list \<Rightarrow> state cost" where 
  "basis_reduction_state_cost F = (case initial_state_cost F of
     (state1,c1) \<Rightarrow> case basis_reduction_main_cost state1
     of (state2,c2) \<Rightarrow> (state2,c1 + c2))" 

definition reduce_basis_cost :: "int vec list \<Rightarrow> int vec list cost" where
  "reduce_basis_cost F = (case basis_reduction_state_cost F of (state,c) \<Rightarrow> 
    ((of_list_repr o fst o snd) state, c))" 

definition "A (F :: int vec list) = max_list (map (nat o sq_norm) F)" 

context
  fixes F :: "int vec list" 
  assumes len: "length F = m"
  and lin_dep: "gs.lin_indpt_list (RAT F)" 
  and L: "lattice_of F = L" 
begin

lemma basis_reduction_state_cost: 
   "result (basis_reduction_state_cost F) = basis_reduction_state n \<alpha> F"  (is ?g1)
   "cost (basis_reduction_state_cost F) \<le> initial_gso_cost + body_cost * num_loops (A F)" (is ?g2)
proof -
  obtain state1 c1 where init: "initial_state_cost F = (state1, c1)" (is "?init = _") by (cases ?init, auto)
  obtain state2 c2 where main: "basis_reduction_main_cost state1 = (state2, c2)" (is "?main = _") by (cases ?main, auto)
  have res: "basis_reduction_state_cost F = (state2, c1 + c2)" 
    unfolding basis_reduction_state_cost_def init main split by simp
  from initial_state_cost[of F, unfolded init cost_simps]
  have c1: "c1 \<le> initial_gso_cost" and init: "initial_state n F = state1" by auto
  from initial_state[OF alpha lin_dep len init refl, folded A_def] L
  obtain F' G' where inv: "LLL_invariant L \<alpha> (A F) state1 F' G'" by auto
  from basis_reduction_main_cost[OF inv, unfolded main cost_simps]
  have main: "basis_reduction_main \<alpha> m state1 = state2" and c2: "c2 \<le> body_cost * num_loops (A F)" 
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
   "cost (reduce_basis_cost F) \<le> initial_gso_cost + body_cost * num_loops (A F)" (is ?g2)
proof -
  obtain state c where b: "basis_reduction_state_cost F = (state,c)" (is "?b = _") by (cases ?b, auto)
  from basis_reduction_state_cost[unfolded b cost_simps]
  have bb: "basis_reduction_state n \<alpha> F = state" and c: "c \<le> initial_gso_cost + body_cost * num_loops (A F)" 
    by auto
  show ?g1 ?g2 unfolding reduce_basis_cost_def reduce_basis_def b bb split cost_simps fst_conv using c by auto
qed

text \<open>Theorem with expanded costs\<close>
thm reduce_basis_cost(2)[unfolded num_loops_def A_def]

end (* lin-indep F *)
end (* fixing body_cost and initial_gso_cost *)
end (* fixing \<alpha> and assume \<alpha> > 4/3 *)
end (* LLL locale which just fixes n and m *)
end (* theory *)