(* Author: Maximilian Schäffeler *)

theory Code_Inventory
  imports 
    Code_Mod
  (* Remove for precise results, approximates real numbers by floats, UNSOUND! *)
    Code_Real_Approx_By_Float_Fix
begin

section \<open>Inventory Management Example\<close>

lemma [code abstype]: "embed_pmf (pmf P) = P"
  by (metis (no_types, lifting) td_pmf_embed_pmf type_definition_def)

lemmas [code_abbrev del] = pmf_integral_code_unfold

lemma [code_unfold]: 
  "measure_pmf.expectation P (f :: 'a :: enum \<Rightarrow> real) = (\<Sum>x \<in> UNIV. pmf P x * f x)"
  by (metis (no_types, lifting) UNIV_I finite_class.finite_UNIV integral_measure_pmf 
      real_scaleR_def sum.cong)

lemma [code]: "pmf (return_pmf x) = (\<lambda>y. indicat_real {y} x) " 
  by auto

lemma [code]: 
  "pmf (bind_pmf N f) = (\<lambda>i :: 'a. measure_pmf.expectation N (\<lambda>(x :: 'b ::enum). pmf (f x) i))" 
  using Probability_Mass_Function.pmf_bind
  by fast

lemma pmf_finite_le: "finite (X :: ('a::finite) set) \<Longrightarrow> sum (pmf p) X \<le> 1"
  by (subst sum_pmf_eq_1[symmetric, of UNIV p]) (auto intro: sum_mono2)

lemma mod_less_diff: 
  assumes "0 < (x::'s::{mod_type})" "x \<le> y" 
  shows "y - x < y"
proof -
  have "0 \<le> Rep y - Rep x"
    using assms mono_Rep unfolding mono_def
    by auto
  have 1: "Rep y - Rep x = Rep (y - x)"
    unfolding mod_type_class.diff_def Rep_Abs_mod
    using Rep_ge_0
    by (auto intro!: mod_pos_pos_trivial[OF \<open>0 \<le> Rep y - Rep x\<close> order.strict_trans1[OF _ Rep_less_n, of _ y], symmetric])
  have "Rep y - Rep x < Rep y"
    using assms(1) strict_mono_Rep Rep_ge_0 le_less not_less 
    by (fastforce simp: strict_mono_def)
  hence "Rep (y - x) < Rep y"
    unfolding 1 by blast
  thus ?thesis
    by (metis not_less_iff_gr_or_eq strict_mono_Rep strict_mono_def)
qed

locale inventory =
  fixes fixed_cost :: real
    and var_cost :: "'s::{mod_type, finite} \<Rightarrow> real"
    and inv_cost :: "'s \<Rightarrow> real"
    and demand_prob :: "'s pmf"
    and revenue :: "'s \<Rightarrow> real"
    and discount :: "real"
begin
definition "order_cost u = (if u = 0 then 0 else fixed_cost + var_cost u)" 
definition "prob_ge_inv u = 1 - (\<Sum>j<u. pmf demand_prob j)"
definition "exp_rev u = (\<Sum>j<u. revenue j * pmf demand_prob j) + revenue u * prob_ge_inv u"
definition "reward sa = (case sa of (s,a) \<Rightarrow> exp_rev (s + a) - order_cost a - inv_cost (s + a))"
lift_definition transition :: "('s \<times> 's) \<Rightarrow> 's pmf" is "\<lambda>(s, a) s'. 
  (if CARD('s) \<le> Rep s + Rep a 
  then (if s' = 0 then 1 else 0)
  else (if s + a < s' then 0 else
   if s' = 0 then prob_ge_inv (s+a)
   else pmf demand_prob (s + a - s')))
  "
proof (safe, goal_cases)
  case (1 a b x)
  then show ?case unfolding prob_ge_inv_def using pmf_finite_le by auto
next
  case (2 a b)
  then show ?case
  proof (cases "int CARD('s) \<le> Rep a + Rep b")  next
    case False
    hence "(\<integral>\<^sup>+ x. ennreal (if int CARD('s) \<le> Rep a + Rep b then if x = 0 then 1 else 0 else if a + b < x then 0 else if x = 0 then prob_ge_inv (a + b) else pmf demand_prob (a + b - x)) \<partial>count_space UNIV) =
      (\<Sum>x \<in> UNIV. (if a + b < x then 0 else if x = 0 then prob_ge_inv (a + b) else pmf demand_prob (a + b - x)))"
      using pmf_nonneg prob_ge_inv_def pmf_finite_le
      by (auto simp: nn_integral_count_space_finite intro!: sum_ennreal)
    also have "\<dots> =(\<Sum>x \<in> UNIV. (if x = 0 then prob_ge_inv (a + b) else if a + b < x then 0 else pmf demand_prob (a + b - x)))"
      by (auto intro!: sum.cong ennreal_cong simp add: leD least_mod_type)
    also have "\<dots> = prob_ge_inv (a + b) + (\<Sum>x \<in> UNIV-{0}. (if a + b < x then 0 else pmf demand_prob (a + b - x)))"
      by (auto simp: sum.remove[of UNIV 0])
    also have "\<dots> = prob_ge_inv (a + b) + (\<Sum>x\<in>{0<..}. (if a + b < x then 0 else pmf demand_prob (a + b - x)))"
      by (auto simp add: greaterThan_def le_neq_trans least_mod_type intro!: cong[of "sum _"] ennreal_cong)
    also have "\<dots> = prob_ge_inv (a + b) + (\<Sum>x\<in>{0<..a+b}. (pmf demand_prob (a + b - x)))"
      unfolding atMost_def greaterThan_def greaterThanAtMost_def
      by (auto simp: Collect_neg_eq[symmetric] not_less sum.If_cases)
    also have "\<dots> =  1 - (\<Sum>j<(a + b). pmf demand_prob j) + (\<Sum>x\<in>{0<..a+b}. pmf demand_prob (a + b - x))"
      unfolding prob_ge_inv_def
      by auto
    also have "\<dots> =  1 - (\<Sum>j<(a + b). pmf demand_prob j) + (\<Sum>x\<in>{..<a+b}. (pmf demand_prob x))"
    proof -
      have "(\<Sum>x\<in>{0<..a+b}. pmf demand_prob (a + b - x)) = (\<Sum>x\<in>{..<a+b}. (pmf demand_prob x))"
      proof (intro sum.reindex_bij_betw bij_betw_imageI)
        show "inj_on ((-) (a + b)) {0<..a + b}"
          unfolding inj_on_def 
          by (metis add.left_cancel diff_add_cancel)
        have "x + (a + b) = a + (b + x)" for x
          by (metis add.assoc add.commute add_to_nat_def)
        moreover have "x < a + b \<Longrightarrow> 0 < a + b - x" for x
          by (metis add.left_neutral diff_add_cancel least_mod_type less_le)
        moreover have "x < a + b \<Longrightarrow> a + b - x \<le> a + b" for x
          by (metis diff_0_right least_mod_type less_le mod_less_diff not_less)
        ultimately have "x < a + b \<Longrightarrow> \<exists>xa. x = a + b - xa \<and> 0 < xa \<and> xa \<le> a + b" for x
          by (auto simp: algebra_simps intro: exI[of _ "a + b - x"])
        thus "(-) (a + b) ` {0<..a + b} = {..<a + b}" 
          by (fastforce intro!: mod_less_diff)
      qed
      thus ?thesis 
        by auto
    qed
    also have "\<dots> =  1"
      by auto
    finally show ?thesis.
  qed (simp add: nn_integral_count_space_finite)
qed

definition "A_inv (s::'s) = {a::'s. Rep s + Rep a < CARD('s)}"

end

definition "var_cost_lin (c::real) n = c * Rep n"
definition "inv_cost_lin (c::real) n = c * Rep n"
definition "revenue_lin (c::real) n = c * Rep n"

lift_definition demand_unif :: "('a::finite) pmf" is "\<lambda>_. 1 / card (UNIV::'a set)"
  by (auto simp: ennreal_divide_times divide_ennreal[symmetric] ennreal_of_nat_eq_real_of_nat)

lift_definition demand_three :: "3 pmf" is "\<lambda>i. if i = 1 then 1/4 else if i = 2 then 1/2 else 1/4"
proof -
  have *: "(UNIV :: (3 set)) = {0,1,2}"
    using exhaust_3
    by fastforce
  show ?thesis
    apply (auto simp: nn_integral_count_space_finite)
    unfolding *
    by auto
qed

abbreviation "fixed_cost \<equiv> 4"
abbreviation "var_cost \<equiv> var_cost_lin 2"
abbreviation "inv_cost \<equiv> inv_cost_lin 1"
abbreviation "revenue \<equiv> revenue_lin 8"
abbreviation "discount \<equiv> 0.99"
type_synonym capacity = "30"

lemma card_ge_2_imp_ne: "CARD('a) \<ge> 2 \<Longrightarrow> \<exists>(x::'a::finite) y::'a. x \<noteq> y"
  by (meson card_2_iff' ex_card)  

global_interpretation inventory_ex: inventory fixed_cost "var_cost:: capacity \<Rightarrow> real" inv_cost demand_unif revenue discount
  defines A_inv = inventory_ex.A_inv
    and transition = inventory_ex.transition
    and reward = inventory_ex.reward
    and prob_ge_inv = inventory_ex.prob_ge_inv
    and order_cost = inventory_ex.order_cost
    and exp_rev = inventory_ex.exp_rev.

abbreviation "K \<equiv> inventory_ex.transition"
abbreviation "A \<equiv> inventory_ex.A_inv"
abbreviation "r \<equiv> inventory_ex.reward"
abbreviation "l \<equiv> 0.95"
definition "eps = 0.1"

definition "fun_to_list f = map f (sorted_list_of_set UNIV)"
definition "benchmark_gs (_ :: unit) = map Rep (fun_to_list (vi_policy' K A r l eps 0))"
definition "benchmark_vi (_ :: unit) = map Rep (fun_to_list (vi_gs_policy K A r l eps 0))"
definition "benchmark_mpi (_ :: unit ) = map Rep (fun_to_list (fst (mpi_user K A r l eps (\<lambda>_ _. 3))))"
definition "benchmark_pi (_ :: unit) = map Rep (fun_to_list (policy_iteration K A r l 0))"

fun vs_n where
  "vs_n 0 v = v"
| "vs_n (Suc n) v = vs_n n (mod_MDP_\<L>\<^sub>b K A r l v)"

definition "vs_n' n = vs_n n 0"

definition "benchmark_vi_n n = (fun_to_list (vs_n n 0))"
definition "benchmark_vi_nopol = (fun_to_list (mod_MDP_value_iteration K A r l (1/10) 0))"

(*
value "benchmark_gs ()"
value "benchmark_vi ()"
value "benchmark_pi ()"
value "benchmark_mpi ()"
*)


export_code dist vs_n' benchmark_vi_nopol benchmark_vi_n nat_of_integer integer_of_int benchmark_gs benchmark_vi benchmark_mpi benchmark_pi
  in Haskell module_name DP

export_code integer_of_int benchmark_gs benchmark_vi benchmark_mpi benchmark_pi in SML module_name DP

end