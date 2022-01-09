theory Code_Mod
  imports Code_DP
begin
section \<open>Code Generation for Concrete Finite MDPs\<close>

locale mod_MDP =
  fixes transition :: "'s::{enum, mod_type} \<times> 'a::{enum, mod_type} \<Rightarrow> 's pmf"
    and A :: "'s \<Rightarrow> 'a set"
    and reward :: "'s \<times> 'a \<Rightarrow> real"
    and discount :: "real"
begin

sublocale mdp: vi_code 
  "\<lambda>s. (if Set.is_empty (A s) then UNIV else A s)" 
  transition 
  reward
  "(if 1 \<le> discount \<or> discount < 0 then 0 else discount)"
  defines \<L>\<^sub>b = mdp.\<L>\<^sub>b
    and L_det = mdp.L_det
    and value_iteration = mdp.value_iteration
    and vi_policy' = mdp.vi_policy'
    and find_policy' = mdp.find_policy'
    and find_policy_impl = mdp.find_policy_impl
    and is_opt_act = mdp.is_opt_act
    and value_iteration_partial = mdp.value_iteration_partial
    and policy_iteration = mdp.policy_iteration
    and is_dec_det = mdp.is_dec_det
    and policy_step = mdp.policy_step
    and policy_improvement = mdp.policy_improvement
    and policy_eval = mdp.policy_eval
    and mk_markovian = mdp.mk_markovian
    and policy_eval' = mdp.policy_eval'
    and policy_iteration_partial' = mdp.policy_iteration_partial'
    and policy_iteration' = mdp.policy_iteration'
    and policy_iteration_policy_step' = mdp.policy_step'
    and policy_iteration_policy_eval' = mdp.policy_eval'
    and policy_iteration_policy_improvement' = mdp.policy_improvement'
    and gs_iteration = mdp.gs_iteration
    and gs_iteration_partial = mdp.gs_iteration_partial
    and vi_gs_policy = mdp.vi_gs_policy
    and opt_policy_gs = mdp.opt_policy_gs
    and opt_policy_gs'' = mdp.opt_policy_gs''
    and P_mat = mdp.P_mat
    and r_vec' = mdp.r_vec'
    and GS_rec_fun\<^sub>b = mdp.GS_rec_fun\<^sub>b
    and GS_iter_max = mdp.GS_iter_max
    and GS_iter = mdp.GS_iter
    and mpi_user = mdp.mpi_user
    and v0_mpi\<^sub>b = mdp.v0_mpi\<^sub>b
    and mpi_partial' = mdp.mpi_partial'
    and L_pow = mdp.L_pow
    and v0_mpi = mdp.v0_mpi
    and r_min = mdp.r_min
    and d0 = mdp.d0
    and d0' = mdp.d0'
    and \<nu>\<^sub>b = mdp.\<nu>\<^sub>b
    and vi_test = mdp.vi_test
  by unfold_locales (auto simp add: Set.is_empty_def)
end

global_interpretation mod_MDP transition A reward discount 
  for transition A reward discount 
  defines mod_MDP_\<L>\<^sub>b = mdp.\<L>\<^sub>b
    and mod_MDP_\<L>\<^sub>b_L_det = mdp.L_det
    and mod_MDP_value_iteration = mdp.value_iteration
    and mod_MDP_vi_policy' = mdp.vi_policy'
    and mod_MDP_find_policy' = mdp.find_policy'
    and mod_MDP_find_policy_impl = mdp.find_policy_impl
    and mod_MDP_is_opt_act = mdp.is_opt_act
    and mod_MDP_value_iteration_partial = mdp.value_iteration_partial
    and mod_MDP_policy_iteration = mdp.policy_iteration
    and mod_MDP_is_dec_det = mdp.is_dec_det
    and mod_MDP_policy_step = mdp.policy_step
    and mod_MDP_policy_improvement = mdp.policy_improvement
    and mod_MDP_policy_eval = mdp.policy_eval
    and mod_MDP_mk_markovian = mdp.mk_markovian
    and mod_MDP_policy_eval' = mdp.policy_eval'
    and mod_MDP_policy_iteration_partial' = mdp.policy_iteration_partial'
    and mod_MDP_policy_iteration' = mdp.policy_iteration'
    and mod_MDP_policy_iteration_policy_step' = mdp.policy_step'
    and mod_MDP_policy_iteration_policy_eval' = mdp.policy_eval'
    and mod_MDP_policy_iteration_policy_improvement' = mdp.policy_improvement'
    and mod_MDP_gs_iteration = mdp.gs_iteration
    and mod_MDP_gs_iteration_partial = mdp.gs_iteration_partial
    and mod_MDP_vi_gs_policy = mdp.vi_gs_policy
    and mod_MDP_opt_policy_gs = mdp.opt_policy_gs
    and mod_MDP_opt_policy_gs'' = mdp.opt_policy_gs''
    and mod_MDP_P_mat = mdp.P_mat
    and mod_MDP_r_vec' = mdp.r_vec'
    and mod_MDP_GS_rec_fun\<^sub>b = mdp.GS_rec_fun\<^sub>b
    and mod_MDP_GS_iter_max = mdp.GS_iter_max
    and mod_MDP_GS_iter = mdp.GS_iter
    and mod_MDP_mpi_user = mdp.mpi_user
    and mod_MDP_v0_mpi\<^sub>b = mdp.v0_mpi\<^sub>b
    and mod_MDP_mpi_partial' = mdp.mpi_partial'
    and mod_MDP_L_pow = mdp.L_pow
    and mod_MDP_v0_mpi = mdp.v0_mpi
    and mod_MDP_r_min = mdp.r_min
    and mod_MDP_d0 = mdp.d0
    and mod_MDP_d0' = mdp.d0'
    and mod_MDP_\<nu>\<^sub>b = mdp.\<nu>\<^sub>b
    and mod_MDP_vi_test = mdp.vi_test
  .

(*
value "mod_MDP_vi_gs_policy (\<lambda>_::(2\<times>2). return_pmf (1::2)) (\<lambda>_. {}) (\<lambda>_. 0) 0.5 0.5 (vec_to_bfun (\<chi> i. 1)) 0"
*)

end
