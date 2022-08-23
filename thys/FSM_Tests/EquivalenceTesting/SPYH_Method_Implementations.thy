section \<open>Implementations of the SPYH-Method\<close>

theory SPYH_Method_Implementations
imports Intermediate_Frameworks
begin

subsection \<open>Using the H-Framework\<close>

definition spyh_method_via_h_framework :: "('a::linorder,'b::linorder,'c::linorder) fsm \<Rightarrow> nat \<Rightarrow> bool \<Rightarrow> bool \<Rightarrow> ('b\<times>'c) prefix_tree" where
  "spyh_method_via_h_framework = h_framework_dynamic (\<lambda> M V t X l . True)"

definition spyh_method_via_h_framework_lists :: "('a::linorder,'b::linorder,'c::linorder) fsm \<Rightarrow> nat \<Rightarrow> bool \<Rightarrow> bool \<Rightarrow> (('b\<times>'c) \<times> bool) list list" where
  "spyh_method_via_h_framework_lists M m completeInputTraces useInputHeuristic = sorted_list_of_maximal_sequences_in_tree (test_suite_from_io_tree M (initial M) (spyh_method_via_h_framework M m completeInputTraces useInputHeuristic))"

lemma spyh_method_via_h_framework_completeness_and_finiteness :
  fixes M1 :: "('a::linorder,'b::linorder,'c::linorder) fsm"
  fixes M2 :: "('e,'b,'c) fsm"
  assumes "observable M1"
  and     "observable M2"
  and     "minimal M1"
  and     "minimal M2"
  and     "size_r M1 \<le> m"
  and     "size M2 \<le> m"
  and     "inputs M2 = inputs M1"
  and     "outputs M2 = outputs M1"
shows "(L M1 = L M2) \<longleftrightarrow> ((L M1 \<inter> set (spyh_method_via_h_framework M1 m completeInputTraces useInputHeuristic)) = (L M2 \<inter> set (spyh_method_via_h_framework M1 m completeInputTraces useInputHeuristic)))"
and "finite_tree (spyh_method_via_h_framework M1 m completeInputTraces useInputHeuristic)"
  using h_framework_dynamic_completeness_and_finiteness[OF assms]
  unfolding spyh_method_via_h_framework_def 
  by blast+

lemma spyh_method_via_h_framework_lists_completeness :
  fixes M1 :: "('a::linorder,'b::linorder,'c::linorder) fsm"
  fixes M2 :: "('d,'b,'c) fsm"
  assumes "observable M1"
  and     "observable M2"
  and     "minimal M1"
  and     "minimal M2"
  and     "size_r M1 \<le> m"
  and     "size M2 \<le> m"
  and     "inputs M2 = inputs M1"
  and     "outputs M2 = outputs M1"
shows "(L M1 = L M2) \<longleftrightarrow> list_all (passes_test_case M2 (initial M2)) (spyh_method_via_h_framework_lists M1 m completeInputTraces useInputHeuristic)"
  using h_framework_dynamic_lists_completeness[OF assms]
  unfolding spyh_method_via_h_framework_lists_def h_framework_dynamic_lists_def spyh_method_via_h_framework_def
  by blast


subsection \<open>Using the SPY-Framework\<close>


definition spyh_method_via_spy_framework :: "('a::linorder,'b::linorder,'c::linorder) fsm \<Rightarrow> nat \<Rightarrow> bool \<Rightarrow> bool \<Rightarrow> ('b\<times>'c) prefix_tree" where
  "spyh_method_via_spy_framework M1 m completeInputTraces useInputHeuristic = 
    spy_framework M1
                   get_state_cover_assignment 
                   (handle_state_cover_dynamic completeInputTraces useInputHeuristic (get_distinguishing_sequence_from_ofsm_tables M1))
                   sort_unverified_transitions_by_state_cover_length
                   (establish_convergence_dynamic completeInputTraces useInputHeuristic (get_distinguishing_sequence_from_ofsm_tables M1))
                   (handle_io_pair completeInputTraces useInputHeuristic)
                   simple_cg_initial
                   simple_cg_insert
                   simple_cg_lookup_with_conv
                   simple_cg_merge
                   m"

lemma spyh_method_via_spy_framework_completeness_and_finiteness :
  fixes M1 :: "('a::linorder,'b::linorder,'c::linorder) fsm"
  fixes M2 :: "('d,'b,'c) fsm"
  assumes "observable M1"
  and     "observable M2"
  and     "minimal M1"
  and     "minimal M2"
  and     "size_r M1 \<le> m"
  and     "size M2 \<le> m"
  and     "inputs M2 = inputs M1"
  and     "outputs M2 = outputs M1"
shows "(L M1 = L M2) \<longleftrightarrow> ((L M1 \<inter> set (spyh_method_via_spy_framework M1 m completeInputTraces useInputHeuristic)) = (L M2 \<inter> set (spyh_method_via_spy_framework M1 m completeInputTraces useInputHeuristic)))"
and "finite_tree (spyh_method_via_spy_framework M1 m completeInputTraces useInputHeuristic)"
  using spy_framework_completeness_and_finiteness[OF assms,
                                                of get_state_cover_assignment 
                                                   sort_unverified_transitions_by_state_cover_length ,
                                                OF get_state_cover_assignment_is_state_cover_assignment
                                                   sort_unverified_transitions_by_state_cover_length_retains_set[of _ M1 get_state_cover_assignment]
                                                   simple_cg_initial_invar_with_conv[OF assms(1,2)]
                                                   simple_cg_insert_invar_with_conv[OF assms(1,2)]
                                                   simple_cg_merge_invar_with_conv[OF assms(1,2)]
                                                   handle_state_cover_dynamic_separates_state_cover[OF get_distinguishing_sequence_from_ofsm_tables_distinguishes[OF assms(1,3)], of completeInputTraces useInputHeuristic M2 simple_cg_initial simple_cg_insert simple_cg_lookup_with_conv]
                                                   establish_convergence_dynamic_verifies_transition[of M1 "(get_distinguishing_sequence_from_ofsm_tables M1)" completeInputTraces useInputHeuristic M2 _ _ simple_cg_insert simple_cg_lookup_with_conv, OF get_distinguishing_sequence_from_ofsm_tables_distinguishes[OF assms(1,3)]]
                                                   handle_io_pair_verifies_io_pair[of completeInputTraces useInputHeuristic M1 M2 simple_cg_insert simple_cg_lookup_with_conv]
                                                ]
    unfolding spyh_method_via_spy_framework_def[symmetric]
    by presburger+



definition spyh_method_via_spy_framework_lists :: "('a::linorder,'b::linorder,'c::linorder) fsm \<Rightarrow> nat \<Rightarrow> bool \<Rightarrow> bool \<Rightarrow> (('b\<times>'c) \<times> bool) list list" where
  "spyh_method_via_spy_framework_lists M m completeInputTraces useInputHeuristic = sorted_list_of_maximal_sequences_in_tree (test_suite_from_io_tree M (initial M) (spyh_method_via_spy_framework M m completeInputTraces useInputHeuristic))"

lemma spyh_method_via_spy_framework_lists_completeness :
  fixes M1 :: "('a::linorder,'b::linorder,'c::linorder) fsm"
  fixes M2 :: "('d,'b,'c) fsm"
  assumes "observable M1"
  and     "observable M2"
  and     "minimal M1"
  and     "minimal M2"
  and     "size_r M1 \<le> m"
  and     "size M2 \<le> m"
  and     "inputs M2 = inputs M1"
  and     "outputs M2 = outputs M1"
shows "(L M1 = L M2) \<longleftrightarrow> list_all (passes_test_case M2 (initial M2)) (spyh_method_via_spy_framework_lists M1 m completeInputTraces useInputHeuristic)"
  unfolding spyh_method_via_spy_framework_lists_def
            spyh_method_via_spy_framework_completeness_and_finiteness(1)[OF assms, of completeInputTraces useInputHeuristic]
            passes_test_cases_from_io_tree[OF assms(1,2) fsm_initial fsm_initial spyh_method_via_spy_framework_completeness_and_finiteness(2)[OF assms]]
  by blast




subsection \<open>Code Generation\<close>



(* one-time pre-computation of OFSM tables *)
lemma spyh_method_via_spy_framework_code[code] :
  "spyh_method_via_spy_framework M1 m completeInputTraces useInputHeuristic = (let 
      tables = (compute_ofsm_tables M1 (size M1 - 1));
      distMap = mapping_of (map (\<lambda> (q1,q2) . ((q1,q2), get_distinguishing_sequence_from_ofsm_tables_with_provided_tables tables M1 q1 q2))
                        (filter (\<lambda> qq . fst qq \<noteq> snd qq) (List.product (states_as_list M1) (states_as_list M1))));
      distHelper = (\<lambda> q1 q2 . if q1 \<in> states M1 \<and> q2 \<in> states M1 \<and> q1 \<noteq> q2 then the (Mapping.lookup distMap (q1,q2)) else get_distinguishing_sequence_from_ofsm_tables M1 q1 q2)
    in
      spy_framework M1
                     get_state_cover_assignment 
                     (handle_state_cover_dynamic completeInputTraces useInputHeuristic distHelper)
                     sort_unverified_transitions_by_state_cover_length
                     (establish_convergence_dynamic completeInputTraces useInputHeuristic distHelper)
                     (handle_io_pair completeInputTraces useInputHeuristic)
                     simple_cg_initial
                     simple_cg_insert
                     simple_cg_lookup_with_conv
                     simple_cg_merge
                     m)"
  unfolding spyh_method_via_spy_framework_def
  apply (subst (1 2) get_distinguishing_sequence_from_ofsm_tables_precomputed[of M1])
  unfolding Let_def 
  by presburger

end