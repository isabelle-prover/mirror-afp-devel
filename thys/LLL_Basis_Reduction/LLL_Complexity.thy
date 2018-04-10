(*
    Authors:    Maximilian Haslbeck
                René Thiemann
    License:    BSD
*)
theory LLL_Complexity
  imports LLL
begin

context
  fixes body_cost :: nat
begin

context
  fixes \<alpha> :: rat and m :: nat 
begin

definition basis_reduction_step_cost :: "state \<Rightarrow> state \<times> nat" where
  "basis_reduction_step_cost state = (basis_reduction_step \<alpha> state, body_cost)"

partial_function (tailrec) basis_reduction_main_cost :: "state \<times> nat \<Rightarrow> state \<times> nat" where
  [code]: "basis_reduction_main_cost state_cost = (case state_cost of (state, cost) \<Rightarrow>
     case state of (i,F,G) \<Rightarrow>
     if i < m
     then case basis_reduction_step_cost state of 
       (state',c) \<Rightarrow> basis_reduction_main_cost (state', c + cost) 
     else state_cost)"
end

definition basis_reduction_state_cost :: "nat \<Rightarrow> rat \<Rightarrow> int vec list \<Rightarrow> state \<times> nat" where 
  "basis_reduction_state_cost n \<alpha> F = basis_reduction_main_cost \<alpha> (length F) (initial_state n F, 0)" 


definition reduce_basis_cost :: "nat \<Rightarrow> rat \<Rightarrow> int vec list \<Rightarrow> int vec list \<times> nat" where
  "reduce_basis_cost n \<alpha> F = (\<lambda> (state, cost). ((of_list_repr o fst o snd) state, cost))
     (basis_reduction_state_cost n \<alpha> F)" 
end

context LLL
begin

context fixes \<alpha> :: rat and body_cost :: nat
 assumes \<alpha>: "\<alpha> > 4/3"
begin

private lemma alpha: "\<alpha> \<ge> 4/3" using \<alpha> by auto

context fixes L :: "int vec set" and A :: nat
begin

lemma basis_reduction_main_cost: fixes F G assumes "LLL_invariant L \<alpha> A state F G"
  and "basis_reduction_main_cost body_cost \<alpha> m (state,c) = (state',c')" 
shows "\<exists> F' G'. LLL_invariant L \<alpha> A state' F' G' \<and> fst state' = m \<and> 
  basis_reduction_main \<alpha> m state = state' \<and> c' \<le> c + body_cost * LLL_measure \<alpha> state"
  using assms
proof (induct state arbitrary: F G c rule: wf_induct[OF wf_measure[of "LLL_measure \<alpha>"]])
  case (1 state F G c)
  note inv = 1(2)
  note IH = 1(1)[rule_format]
  note res = 1(3)
  obtain i Fr1 Gr1 where state: "state = (i,Fr1,Gr1)" by (cases state, auto)
  note inv = inv[unfolded state]
  show ?case
  proof (cases "i < m")
    case True
    with inv have i: "i < m" unfolding LLL_invariant_def by auto
    obtain state'' where b: "basis_reduction_step \<alpha> (i, Fr1, Gr1) = state''" by auto
    from res[unfolded basis_reduction_main_cost.simps[of _ _ _ "(state,c)"], unfolded state b split
        basis_reduction_step_cost_def] True
    have res: "basis_reduction_main_cost body_cost \<alpha> m (state'', body_cost + c) = (state', c')" by auto 
    note bsr = basis_reduction_step[OF alpha inv i b]
    from bsr(1) obtain F' G' where inv: "LLL_invariant L \<alpha> A state'' F' G'" by auto
    from bsr(2) have "(state'' ,state) \<in> measure (LLL_measure \<alpha>)" by (auto simp: state)
    from IH[OF this inv res] obtain F' G' where
      inv: "LLL_invariant L \<alpha> A state' F' G'" 
      and fst: "fst state' = m"
      and res': "basis_reduction_main \<alpha> m state'' = state'" 
      and c: "c' \<le> c + body_cost * (Suc (LLL_measure \<alpha> state''))" by auto
    have res: "basis_reduction_main \<alpha> m state = state'"
      unfolding basis_reduction_main.simps[of _ _ state] unfolding state split b res' using True by auto
    show ?thesis
      by (intro exI conjI fst res, rule inv, rule order.trans[OF c add_left_mono[OF mult_left_mono]],
        insert bsr(2) state, auto)
  next
    case False
    from False res have state': "state' = (i, Fr1, Gr1)" and c: "c' = c"
      and res: "basis_reduction_main \<alpha> m state = (i, Fr1, Gr1)" 
      unfolding basis_reduction_main_cost.simps[of _ _ _ "(state,c)"] 
        basis_reduction_main.simps[of _ _ state] unfolding split state by auto
    from False LLL_invD[OF inv] have im: "i = m" by auto
    show ?thesis unfolding state' fst_conv c
      by (intro exI conjI im res, rule inv, auto)
  qed
qed
end

context
  fixes F :: "int vec list" 
  assumes len: "length F = m"
    and lin_dep: "gs.lin_indpt_list (RAT F)" 
    and m0: "m \<noteq> 0" 
begin

qualified definition "A = max_list (map (nat o sq_norm) F)" 
qualified definition "num_loops = m + 2 * m * m * log (4 * of_rat \<alpha> / (4 + of_rat \<alpha>)) A"

lemma basis_reduction_state_cost: assumes res: "basis_reduction_state_cost body_cost n \<alpha> F = (state,c)"
shows "basis_reduction_state n \<alpha> F = state" 
  "c \<le> body_cost * num_loops" 
proof -
  let ?init = "initial_state n F" 
  from res[unfolded basis_reduction_state_cost_def len]
  have res_main: "basis_reduction_main_cost body_cost \<alpha> m (?init, 0) = (state, c)" by auto
  from initial_state[OF alpha lin_dep len refl A_def]
  obtain F' G' where inv: "LLL_invariant (lattice_of F) \<alpha> A ?init F' G'" by auto
  from basis_reduction_main_cost[OF this res_main]
  have "basis_reduction_main \<alpha> m ?init = state" 
    and c: "c \<le> body_cost * LLL_measure \<alpha> ?init" by auto
  thus "basis_reduction_state n \<alpha> F = state" unfolding basis_reduction_state_def len by auto
  obtain i Fr Gr where init: "?init = (i,Fr,Gr)" by (cases ?init, auto)
  from LLL_measure_approx[OF alpha inv[unfolded init] \<alpha> m0, folded init]
  have num: "real (LLL_measure \<alpha> (initial_state n F)) \<le> num_loops" unfolding num_loops_def .
  have "real c \<le> body_cost * (real (LLL_measure \<alpha> ?init))" using c
    using SN_Orders.of_nat_mono by force
  also have "\<dots> \<le> body_cost * num_loops" 
    by (rule mult_left_mono[OF num], auto)
  finally show "c \<le> body_cost * num_loops" .
qed

text \<open>The lemma for the LLL algorithm with explicit cost @{const reduce_basis_cost}
  shows that the termination measure
  is indeed a bound for the explicit costs. Moreover, we get the same result
  as in the non-cost counting @{const reduce_basis}. Therefore, we can easily
  carry over results derived for @{const reduce_basis}.\<close>

lemma reduce_basis_cost: assumes res: "reduce_basis_cost body_cost n \<alpha> F = (F',c)" 
  shows "c \<le> body_cost * num_loops" (is ?g1)
    "reduce_basis n \<alpha> F = (F', gram_schmidt n (RAT F'))" (is ?g2)
    "lattice_of F = lattice_of F'" (is ?g3)
    "gs.reduced \<alpha> m (gram_schmidt n (RAT F')) (gs.\<mu> (RAT F'))" (is ?g4)
proof -
  let ?basis = "basis_reduction_state_cost body_cost n \<alpha> F" 
  from res[unfolded reduce_basis_cost_def]
  obtain state where res': "?basis = (state, c)" 
    and F': "F' = (of_list_repr \<circ> fst \<circ> snd) state" by (cases ?basis, auto)
  from basis_reduction_state_cost[OF res']
  have res': "basis_reduction_state n \<alpha> F = state" 
    and c: "c \<le> body_cost * num_loops" by auto 
  obtain G' where res: "reduce_basis n \<alpha> F = (F', G')" unfolding F' reduce_basis_def res' by auto
  show ?g1 by fact
  note reduce = reduce_basis[OF alpha lin_dep len res]
  show ?g2 unfolding res using reduce by auto
  show ?g3 by fact
  show ?g4 using reduce by auto
qed

thm reduce_basis_cost(1)[unfolded A_def num_loops_def]

end (* common assumption on fs, like lin-indep *)
end (* fixing \<alpha> and assume \<alpha> > 4/3 *)
end (* LLL locale which just fixes n and m *)
end (* theory *)