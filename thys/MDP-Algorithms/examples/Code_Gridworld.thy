(* Author: Maximilian Schäffeler *)

theory Code_Gridworld
  imports 
    Code_Mod
begin
section \<open>Gridworld Example\<close>

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

(* 3 x 4 + 1 * Trap *)
type_synonym state_robot = "13"

definition "from_state x = (Rep x div 4, Rep x mod 4)"
definition "to_state x = (Abs (fst x * 4 + snd x) :: state_robot)"

(* up, right, down, left *)
type_synonym action_robot = 4

fun A_robot :: "state_robot \<Rightarrow> action_robot set" where
  "A_robot pos = UNIV"

abbreviation "noise \<equiv> (0.2 :: real)"

lift_definition add_noise :: "action_robot \<Rightarrow> action_robot pmf" is "\<lambda>det rnd. (
  if det = rnd then 1 - noise else if det = rnd - 1 \<or> det = rnd + 1 then noise / 2 else 0)"
  subgoal for n
    unfolding nn_integral_count_space_finite[OF finite] UNIV_4
    using exhaust_4[of n]
    by fastforce
  done

fun r_robot :: "(state_robot \<times> action_robot) \<Rightarrow> real" where
  "r_robot (s,a) = (
  if from_state s = (2,3) then 1 else
  if from_state s = (1,3) then -1 else 
  if from_state s = (3,0) then 0 else
  0)"

fun K_robot :: "(state_robot \<times> action_robot) \<Rightarrow> state_robot pmf" where
  "K_robot (loc, a) = 
  do {
  a \<leftarrow> add_noise a;
  let (y, x) = from_state loc;
  let (y', x') =
    (if a = 0 then (y + 1 , x)
      else if a = 1 then (y, x+1)
      else if a = 2 then (y-1, x)
      else if a = 3 then (y, x-1)
      else undefined);
   return_pmf (
      if (y,x) = (2,3) \<or> (y,x) = (1,3) \<or> (y,x) = (3,0) 
        then to_state (3,0)
      else if y' < 0 \<or> y' > 2 \<or> x' < 0 \<or> x' > 3 \<or> (y',x') = (1,1)
      then to_state (y, x)
        else to_state (y', x'))
  }"

definition "l_robot = 0.9"

lemma "vi_code A_robot r_robot l_robot"
  by standard (auto simp: l_robot_def)


abbreviation "to_gridworld f \<equiv> f K_robot r_robot l_robot"
abbreviation "to_gridworld' f \<equiv> f K_robot A_robot r_robot l_robot"

abbreviation "gridworld_policy_eval' \<equiv> to_gridworld mod_MDP_policy_eval'"
abbreviation "gridworld_policy_step' \<equiv> to_gridworld' mod_MDP_policy_iteration_policy_step'"
abbreviation "gridworld_mpi_user \<equiv> to_gridworld' mod_MDP_mpi_user"
abbreviation "gridworld_opt_policy_gs \<equiv> to_gridworld' mod_MDP_opt_policy_gs"
abbreviation "gridworld_\<L>\<^sub>b \<equiv> to_gridworld' mod_MDP_\<L>\<^sub>b"
abbreviation "gridworld_find_policy' \<equiv> to_gridworld' mod_MDP_find_policy'"
abbreviation "gridworld_GS_rec_fun\<^sub>b \<equiv> to_gridworld' mod_MDP_GS_rec_fun\<^sub>b"
abbreviation "gridworld_vi_policy' \<equiv> to_gridworld' mod_MDP_vi_policy'"
abbreviation "gridworld_vi_gs_policy \<equiv> to_gridworld' mod_MDP_vi_gs_policy"
abbreviation "gridworld_policy_iteration \<equiv> to_gridworld' mod_MDP_policy_iteration"


fun pi_robot_n where
  "pi_robot_n 0 d = (d, gridworld_policy_eval' d)" | 
  "pi_robot_n (Suc n) d = pi_robot_n n (gridworld_policy_step' d)"

definition "mpi_robot eps = gridworld_mpi_user eps (\<lambda>_. 3)"

fun gs_robot_n where
  "gs_robot_n (0 :: nat) v = (gridworld_opt_policy_gs v, v)" |
  "gs_robot_n (Suc n :: nat) v = gs_robot_n n (gridworld_GS_rec_fun\<^sub>b v)"

fun vi_robot_n where
  "vi_robot_n (0 :: nat) v = (gridworld_find_policy' v, v)" |
  "vi_robot_n (Suc n :: nat) v = vi_robot_n n (gridworld_\<L>\<^sub>b v)"

definition "mpi_result eps = 
  (let (d, v) = mpi_robot eps in (d,v))"

definition "gs_result n = 
  (let (d,v) = gs_robot_n n 0 in (d,v))"

definition "vi_result_n n = 
  (let (d, v) = vi_robot_n n 0 in (d,v))"

definition "pi_result_n n = 
  (let (d, v) = pi_robot_n n (vec_to_fun 0) in (d,v))"

definition "fun_to_list f = map f (sorted_list_of_set UNIV)"

definition "benchmark_gs = fun_to_list (gridworld_vi_policy' 0.1 0)"
definition "benchmark_vi = fun_to_list (gridworld_vi_gs_policy 0.1 0)"
definition "benchmark_mpi = fun_to_list (fst (gridworld_mpi_user 0.1 (\<lambda>_ _. 3)))"
definition "benchmark_pi = fun_to_list (gridworld_policy_iteration 0)"

(*
value [code] "gs_result 20"
value [code] "mpi_result 0.1"
value [code] "vi_result_n 20"
value [code] "pi_result_n 3"
value "benchmark_gs"
value "benchmark_vi"
value "benchmark_mpi"
value "benchmark_pi"
*)

export_code benchmark_gs benchmark_vi benchmark_mpi benchmark_pi in Haskell module_name DP
export_code benchmark_gs benchmark_vi benchmark_mpi benchmark_pi in SML module_name DP
end