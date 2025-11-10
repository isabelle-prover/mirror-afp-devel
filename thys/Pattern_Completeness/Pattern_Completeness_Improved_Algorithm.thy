theory Pattern_Completeness_Improved_Algorithm
  imports 
    Pattern_Completeness_List
    FCF_List
    Finite_IDL_Solver
begin

text \<open>Combining the three solvers to get the full algorithm of section 5:
  arbitrary-to-fcf: @{const pat_complete_impl_fcf},
  fcf-to-idl: @{const pattern_completeness_context.fcf_solver_alg}, and
  idl-solver: @{const default_fidl_solver}\<close>

definition decide_pat_complete :: "_ \<Rightarrow> _ \<Rightarrow> (('f \<times> 's list) \<times> 's)list \<Rightarrow> ('f,'v,'s)pats_problem_list \<Rightarrow> bool" where
  "decide_pat_complete rn rv Cs P = (let 
      m = max_arity_list Cs;
      Cl = constr_list Cs; 
      Cm = Mapping.of_alist Cs;
      k = compute_k_parameter P;
      (IS,CD) = compute_inf_card_sorts_bnd k Cs;
      solve = pattern_completeness_context.fcf_solver_alg (Mapping.lookup Cm) m Cl CD default_fidl_solver
     in pat_complete_impl_fcf m Cl (\<lambda> s. s \<in> IS) (Mapping.lookup Cm) rn rv solve P)" 

theorem decide_pat_complete:
  assumes dist: "distinct (map fst Cs)" 
    and non_empty_sorts: "decide_nonempty_sorts (sorts_of_ssig_list Cs) Cs = None" 
    and P: "snd ` \<Union> (vars ` fst ` set (concat (concat P))) \<subseteq> set (sorts_of_ssig_list Cs)"
    and ren: "renaming_funs rn rv" 
  shows "decide_pat_complete rn rv Cs P \<longleftrightarrow> pats_complete (map_of Cs) (pat_list ` set P)"
proof -
  let ?k = "compute_k_parameter P" 
  interpret pattern_completeness_list Cs ?k
    apply unfold_locales
    using dist non_empty_sorts compute_k_parameter_1 .
  have nemp:
    "\<forall> f \<tau>s \<tau> \<tau>'. f : \<tau>s \<rightarrow> \<tau> in map_of Cs \<longrightarrow> \<tau>' \<in> set \<tau>s \<longrightarrow> \<not> empty_sort (map_of Cs) \<tau>'"
    using C_sub_S by (auto intro!: nonempty_sort)
  obtain inf cd where "compute_inf_card_sorts_bnd ?k Cs = (inf,cd)" by force
  with compute_inf_card_sorts_bnd(2,3)[OF refl nemp dist this]
  have cics: "compute_inf_card_sorts_bnd ?k Cs = (compute_inf_sorts Cs, min ?k o card_of_sort (map_of Cs))"
    by (simp add: Compute_Nonempty_Infinite_Sorts.compute_inf_sorts(2) dist nemp)
  have Cm: "Mapping.lookup (Mapping.of_alist Cs) = map_of Cs" using dist
    using lookup_of_alist by fastforce
  have fcf: "pattern_completeness_context.fcf_solver_alg (map_of Cs) (max_arity_list Cs) (constr_list Cs)
       (min ?k \<circ> card_of_sort (map_of Cs)) default_fidl_solver
    = fcf_solver_alg default_fidl_solver" 
    unfolding compute_card_sorts by auto
  show ?thesis
    apply (unfold decide_pat_complete_def Let_def case_prod_beta cics fst_conv snd_conv)
    unfolding pat_complete_impl_fcf_def Cm
    apply (rule pat_complete_impl[OF ren _ refl P refl])
    by (rule fcf_solver_alg'[OF default_fidl_solver, folded fcf])
qed
  
export_code decide_pat_complete checking 
end