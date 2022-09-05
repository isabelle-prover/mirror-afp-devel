section \<open>Intermediate Frameworks\<close>

text \<open>This theory provides partial applications of the H, SPY, and Pair-Frameworks.\<close>

theory Intermediate_Frameworks
imports Intermediate_Implementations Test_Suite_Representations "../OFSM_Tables_Refined" Simple_Convergence_Graph Empty_Convergence_Graph
begin

subsection \<open>Partial Applications of the SPY-Framework\<close>

definition spy_framework_static_with_simple_graph :: "('a::linorder,'b::linorder,'c::linorder) fsm \<Rightarrow> 
                              (nat \<Rightarrow> 'a \<Rightarrow> ('b\<times>'c) prefix_tree) \<Rightarrow>
                              nat \<Rightarrow>
                              ('b\<times>'c) prefix_tree" 
  where
  "spy_framework_static_with_simple_graph M1
                         dist_fun 
                         m 
    = spy_framework M1
                  get_state_cover_assignment 
                  (handle_state_cover_static dist_fun)
                  (\<lambda> M V ts . ts)
                  (establish_convergence_static dist_fun)
                  (handle_io_pair False True)
                  simple_cg_initial
                  simple_cg_insert
                  simple_cg_lookup_with_conv
                  simple_cg_merge
                  m"


lemma spy_framework_static_with_simple_graph_completeness_and_finiteness :
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
  and     "\<And> q1 q2 . q1 \<in> states M1 \<Longrightarrow> q2 \<in> states M1 \<Longrightarrow> q1 \<noteq> q2 \<Longrightarrow> \<exists> io . \<forall> k1 k2 . io \<in> set (dist_fun k1 q1) \<inter> set (dist_fun k2 q2) \<and> distinguishes M1 q1 q2 io"
  and     "\<And> q k . q \<in> states M1 \<Longrightarrow> finite_tree (dist_fun k q)"
shows "(L M1 = L M2) \<longleftrightarrow> ((L M1 \<inter> set (spy_framework_static_with_simple_graph M1 dist_fun m)) = (L M2 \<inter> set (spy_framework_static_with_simple_graph M1 dist_fun m)))"
and "finite_tree (spy_framework_static_with_simple_graph M1 dist_fun m)"  
  using spy_framework_completeness_and_finiteness[OF assms(1-8), 
                                                   of get_state_cover_assignment, OF get_state_cover_assignment_is_state_cover_assignment,
                                                   of "(\<lambda> M V ts . ts)", 
                                                   OF _ simple_cg_initial_invar_with_conv[OF assms(1,2)],
                                                   OF _ simple_cg_insert_invar_with_conv[OF assms(1,2)],
                                                   OF _ simple_cg_merge_invar_with_conv[OF assms(1,2)],
                                                   of "handle_state_cover_static dist_fun" 
                                                      "establish_convergence_static dist_fun" 
                                                      "handle_io_pair False True"
                                                   ]
  using handle_state_cover_static_separates_state_cover[OF assms(9,10)]
  using establish_convergence_static_verifies_transition[of M1 dist_fun M2 "get_state_cover_assignment M1" simple_cg_initial simple_cg_insert simple_cg_lookup_with_conv, OF assms(9,10)]
  using handle_io_pair_verifies_io_pair[of False True M1 M2 simple_cg_insert simple_cg_lookup_with_conv]
  unfolding spy_framework_static_with_simple_graph_def
  by blast+





definition spy_framework_static_with_empty_graph :: "('a::linorder,'b::linorder,'c::linorder) fsm \<Rightarrow> 
                              (nat \<Rightarrow> 'a \<Rightarrow> ('b\<times>'c) prefix_tree) \<Rightarrow>
                              nat \<Rightarrow>
                              ('b\<times>'c) prefix_tree" 
  where
  "spy_framework_static_with_empty_graph M1
                 dist_fun 
                 m 
    = spy_framework M1
                     get_state_cover_assignment 
                     (handle_state_cover_static dist_fun)
                     (\<lambda> M V ts . ts)
                     (establish_convergence_static dist_fun)
                     (handle_io_pair False True)
                     empty_cg_initial
                     empty_cg_insert
                     empty_cg_lookup
                     empty_cg_merge
                     m"

lemma spy_framework_static_with_empty_graph_completeness_and_finiteness :
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
  and     "\<And> q1 q2 . q1 \<in> states M1 \<Longrightarrow> q2 \<in> states M1 \<Longrightarrow> q1 \<noteq> q2 \<Longrightarrow> \<exists> io . \<forall> k1 k2 . io \<in> set (dist_fun k1 q1) \<inter> set (dist_fun k2 q2) \<and> distinguishes M1 q1 q2 io"
  and     "\<And> q k . q \<in> states M1 \<Longrightarrow> finite_tree (dist_fun k q)"
shows "(L M1 = L M2) \<longleftrightarrow> ((L M1 \<inter> set (spy_framework_static_with_empty_graph M1 dist_fun m)) = (L M2 \<inter> set (spy_framework_static_with_empty_graph M1 dist_fun m)))"
and "finite_tree (spy_framework_static_with_empty_graph M1 dist_fun m)"  
  using spy_framework_completeness_and_finiteness[OF assms(1-8), 
                                                   of get_state_cover_assignment, OF get_state_cover_assignment_is_state_cover_assignment,
                                                   of "(\<lambda> M V ts . ts)", 
                                                   OF _ empty_graph_initial_invar,
                                                   OF _ empty_graph_insert_invar,
                                                   OF _ empty_graph_merge_invar,
                                                   of "handle_state_cover_static dist_fun" 
                                                      "establish_convergence_static dist_fun" 
                                                      "handle_io_pair False True"
                                                   ]
  using handle_state_cover_static_separates_state_cover[OF assms(9,10)]
  using establish_convergence_static_verifies_transition[of M1 dist_fun M2 "get_state_cover_assignment M1" empty_cg_initial empty_cg_insert empty_cg_lookup, OF assms(9,10)]
  using handle_io_pair_verifies_io_pair[of False True M1 M2 empty_cg_insert empty_cg_lookup]
  unfolding spy_framework_static_with_empty_graph_def
  by blast+



subsection \<open>Partial Applications of the H-Framework\<close>


definition h_framework_static_with_simple_graph :: "('a::linorder,'b::linorder,'c::linorder) fsm \<Rightarrow> 
                                        (nat \<Rightarrow> 'a \<Rightarrow> ('b\<times>'c) prefix_tree) \<Rightarrow>
                                        nat \<Rightarrow>
                                        ('b\<times>'c) prefix_tree" 
  where
  "h_framework_static_with_simple_graph M1 dist_fun m = 
    h_framework M1
                   get_state_cover_assignment 
                   (handle_state_cover_static dist_fun)
                   (\<lambda> M V ts . ts)
                   (handleUT_static dist_fun)
                   (handle_io_pair False False)
                   simple_cg_initial
                   simple_cg_insert
                   simple_cg_lookup_with_conv
                   simple_cg_merge
                   m"

lemma h_framework_static_with_simple_graph_completeness_and_finiteness :
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
  and     "\<And> q1 q2 . q1 \<in> states M1 \<Longrightarrow> q2 \<in> states M1 \<Longrightarrow> q1 \<noteq> q2 \<Longrightarrow> \<exists> io . \<forall> k1 k2 . io \<in> set (dist_fun k1 q1) \<inter> set (dist_fun k2 q2) \<and> distinguishes M1 q1 q2 io"
  and     "\<And> q k . q \<in> states M1 \<Longrightarrow> finite_tree (dist_fun k q)"
shows "(L M1 = L M2) \<longleftrightarrow> ((L M1 \<inter> set (h_framework_static_with_simple_graph  M1 dist_fun m)) = (L M2 \<inter> set (h_framework_static_with_simple_graph  M1 dist_fun m)))"
and "finite_tree (h_framework_static_with_simple_graph  M1 dist_fun m)"
  using h_framework_completeness_and_finiteness[OF assms(1-8),
                                             of get_state_cover_assignment 
                                                "(\<lambda> M V ts . ts)" ,
                                             OF get_state_cover_assignment_is_state_cover_assignment
                                                _
                                                simple_cg_initial_invar_with_conv[OF assms(1,2)]
                                                simple_cg_insert_invar_with_conv[OF assms(1,2)]
                                                simple_cg_merge_invar_with_conv[OF assms(1,2)]
                                                handle_state_cover_static_separates_state_cover[OF assms(9,10)]
                                                handleUT_static_handles_transition[OF assms(9,10)]
                                                verifies_io_pair_handled[OF handle_io_pair_verifies_io_pair[of False False M1 M2 simple_cg_insert simple_cg_lookup_with_conv]]
                                             ]
  unfolding h_framework_static_with_simple_graph_def[symmetric]
  by presburger+

definition h_framework_static_with_simple_graph_lists :: "('a::linorder,'b::linorder,'c::linorder) fsm \<Rightarrow> (nat \<Rightarrow> 'a \<Rightarrow> ('b\<times>'c) prefix_tree) \<Rightarrow> nat \<Rightarrow> (('b\<times>'c) \<times> bool) list list" where
  "h_framework_static_with_simple_graph_lists M dist_fun m = sorted_list_of_maximal_sequences_in_tree (test_suite_from_io_tree M (initial M) (h_framework_static_with_simple_graph M dist_fun m))"

lemma h_framework_static_with_simple_graph_lists_completeness :
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
  and     "\<And> q1 q2 . q1 \<in> states M1 \<Longrightarrow> q2 \<in> states M1 \<Longrightarrow> q1 \<noteq> q2 \<Longrightarrow> \<exists> io . \<forall> k1 k2 . io \<in> set (dist_fun k1 q1) \<inter> set (dist_fun k2 q2) \<and> distinguishes M1 q1 q2 io"
  and     "\<And> q k . q \<in> states M1 \<Longrightarrow> finite_tree (dist_fun k q)"
shows "(L M1 = L M2) \<longleftrightarrow> list_all (passes_test_case M2 (initial M2)) (h_framework_static_with_simple_graph_lists M1 dist_fun m)"
  unfolding h_framework_static_with_simple_graph_lists_def
  using h_framework_static_with_simple_graph_completeness_and_finiteness(1)[OF assms(1,2,3,4,5,6,7,8,9,10)]
  using passes_test_cases_from_io_tree[OF assms(1,2) fsm_initial fsm_initial h_framework_static_with_simple_graph_completeness_and_finiteness(2)[OF assms]]
  by blast


definition h_framework_static_with_empty_graph :: "('a::linorder,'b::linorder,'c::linorder) fsm \<Rightarrow> 
                                        (nat \<Rightarrow> 'a \<Rightarrow> ('b\<times>'c) prefix_tree) \<Rightarrow>
                                        nat \<Rightarrow>
                                        ('b\<times>'c) prefix_tree" 
  where
  "h_framework_static_with_empty_graph M1 dist_fun m = 
    h_framework M1
                   get_state_cover_assignment 
                   (handle_state_cover_static dist_fun)
                   (\<lambda> M V ts . ts)
                   (handleUT_static dist_fun)
                   (handle_io_pair False False)
                   empty_cg_initial
                   empty_cg_insert
                   empty_cg_lookup
                   empty_cg_merge
                   m"

lemma h_framework_static_with_empty_graph_completeness_and_finiteness :
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
  and     "\<And> q1 q2 . q1 \<in> states M1 \<Longrightarrow> q2 \<in> states M1 \<Longrightarrow> q1 \<noteq> q2 \<Longrightarrow> \<exists> io . \<forall> k1 k2 . io \<in> set (dist_fun k1 q1) \<inter> set (dist_fun k2 q2) \<and> distinguishes M1 q1 q2 io"
  and     "\<And> q k . q \<in> states M1 \<Longrightarrow> finite_tree (dist_fun k q)"
shows "(L M1 = L M2) \<longleftrightarrow> ((L M1 \<inter> set (h_framework_static_with_empty_graph  M1 dist_fun m)) = (L M2 \<inter> set (h_framework_static_with_empty_graph  M1 dist_fun m)))"
and "finite_tree (h_framework_static_with_empty_graph  M1 dist_fun m)"
  using h_framework_completeness_and_finiteness[OF assms(1-8),
                                             of get_state_cover_assignment 
                                                "(\<lambda> M V ts . ts)" ,
                                             OF get_state_cover_assignment_is_state_cover_assignment
                                                _
                                                empty_graph_initial_invar
                                                empty_graph_insert_invar
                                                empty_graph_merge_invar
                                                handle_state_cover_static_separates_state_cover[OF assms(9,10)]
                                                handleUT_static_handles_transition[OF assms(9,10)]
                                                verifies_io_pair_handled[OF handle_io_pair_verifies_io_pair[of False False M1 M2 empty_cg_insert empty_cg_lookup]]
                                             ]
  unfolding h_framework_static_with_empty_graph_def[symmetric]
  by presburger+

definition h_framework_static_with_empty_graph_lists :: "('a::linorder,'b::linorder,'c::linorder) fsm \<Rightarrow> (nat \<Rightarrow> 'a \<Rightarrow> ('b\<times>'c) prefix_tree) \<Rightarrow> nat \<Rightarrow> (('b\<times>'c) \<times> bool) list list" where
  "h_framework_static_with_empty_graph_lists M dist_fun m = sorted_list_of_maximal_sequences_in_tree (test_suite_from_io_tree M (initial M) (h_framework_static_with_empty_graph M dist_fun m))"

lemma h_framework_static_with_empty_graph_lists_completeness :
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
  and     "\<And> q1 q2 . q1 \<in> states M1 \<Longrightarrow> q2 \<in> states M1 \<Longrightarrow> q1 \<noteq> q2 \<Longrightarrow> \<exists> io . \<forall> k1 k2 . io \<in> set (dist_fun k1 q1) \<inter> set (dist_fun k2 q2) \<and> distinguishes M1 q1 q2 io"
  and     "\<And> q k . q \<in> states M1 \<Longrightarrow> finite_tree (dist_fun k q)"
shows "(L M1 = L M2) \<longleftrightarrow> list_all (passes_test_case M2 (initial M2)) (h_framework_static_with_empty_graph_lists M1 dist_fun m)"
  unfolding h_framework_static_with_empty_graph_lists_def
  using h_framework_static_with_empty_graph_completeness_and_finiteness(1)[OF assms(1,2,3,4,5,6,7,8,9,10)]
  using passes_test_cases_from_io_tree[OF assms(1,2) fsm_initial fsm_initial h_framework_static_with_empty_graph_completeness_and_finiteness(2)[OF assms]]
  by blast


definition h_framework_dynamic :: "
              (('a,'b,'c) fsm \<Rightarrow> ('a,'b,'c) state_cover_assignment \<Rightarrow> ('a,'b,'c) transition \<Rightarrow> ('a,'b,'c) transition list \<Rightarrow> nat \<Rightarrow> bool) \<Rightarrow>
              ('a::linorder,'b::linorder,'c::linorder) fsm \<Rightarrow> 
              nat \<Rightarrow> 
              bool \<Rightarrow> 
              bool \<Rightarrow> 
              ('b\<times>'c) prefix_tree" 
  where
  "h_framework_dynamic convergence_decisision M1 m completeInputTraces useInputHeuristic = 
    h_framework M1
                   get_state_cover_assignment 
                   (handle_state_cover_dynamic completeInputTraces useInputHeuristic (get_distinguishing_sequence_from_ofsm_tables M1))
                   sort_unverified_transitions_by_state_cover_length
                   (handleUT_dynamic completeInputTraces useInputHeuristic (get_distinguishing_sequence_from_ofsm_tables M1) convergence_decisision)
                   (handle_io_pair completeInputTraces useInputHeuristic)
                   simple_cg_initial
                   simple_cg_insert
                   simple_cg_lookup_with_conv
                   simple_cg_merge
                   m"


lemma h_framework_dynamic_completeness_and_finiteness :
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
shows "(L M1 = L M2) \<longleftrightarrow> ((L M1 \<inter> set (h_framework_dynamic convergenceDecision M1 m completeInputTraces useInputHeuristic)) = (L M2 \<inter> set (h_framework_dynamic convergenceDecision M1 m completeInputTraces useInputHeuristic)))"
and "finite_tree (h_framework_dynamic convergenceDecision M1 m completeInputTraces useInputHeuristic)"
  using h_framework_completeness_and_finiteness[OF assms,
                                             of get_state_cover_assignment 
                                                sort_unverified_transitions_by_state_cover_length ,
                                             OF get_state_cover_assignment_is_state_cover_assignment
                                                sort_unverified_transitions_by_state_cover_length_retains_set[of _ M1 get_state_cover_assignment]
                                                simple_cg_initial_invar_with_conv[OF assms(1,2)]
                                                simple_cg_insert_invar_with_conv[OF assms(1,2)]
                                                simple_cg_merge_invar_with_conv[OF assms(1,2)]
                                                handle_state_cover_dynamic_separates_state_cover[OF get_distinguishing_sequence_from_ofsm_tables_distinguishes[OF assms(1,3)], of completeInputTraces useInputHeuristic M2 simple_cg_initial simple_cg_insert simple_cg_lookup_with_conv]
                                                handleUT_dynamic_handles_transition[of M1 "(get_distinguishing_sequence_from_ofsm_tables M1)" completeInputTraces useInputHeuristic convergenceDecision M2 _ _ simple_cg_insert simple_cg_lookup_with_conv simple_cg_merge, OF get_distinguishing_sequence_from_ofsm_tables_distinguishes[OF assms(1,3)]]
                                                verifies_io_pair_handled[OF handle_io_pair_verifies_io_pair[of completeInputTraces useInputHeuristic M1 M2 simple_cg_insert simple_cg_lookup_with_conv]]
                                             ]
  unfolding h_framework_dynamic_def[symmetric]
  by presburger+


definition h_framework_dynamic_lists :: "(('a,'b,'c) fsm \<Rightarrow> ('a,'b,'c) state_cover_assignment \<Rightarrow> ('a,'b,'c) transition \<Rightarrow> ('a,'b,'c) transition list \<Rightarrow> nat \<Rightarrow> bool) \<Rightarrow> ('a::linorder,'b::linorder,'c::linorder) fsm \<Rightarrow> nat \<Rightarrow> bool \<Rightarrow> bool \<Rightarrow> (('b\<times>'c) \<times> bool) list list" where
  "h_framework_dynamic_lists convergenceDecision M m completeInputTraces useInputHeuristic = sorted_list_of_maximal_sequences_in_tree (test_suite_from_io_tree M (initial M) (h_framework_dynamic convergenceDecision M m completeInputTraces useInputHeuristic))"

lemma h_framework_dynamic_lists_completeness :
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
shows "(L M1 = L M2) \<longleftrightarrow> list_all (passes_test_case M2 (initial M2)) (h_framework_dynamic_lists convergenceDecision M1 m completeInputTraces useInputHeuristic)"
  unfolding h_framework_dynamic_lists_def
            h_framework_dynamic_completeness_and_finiteness(1)[OF assms, of convergenceDecision completeInputTraces useInputHeuristic]
            passes_test_cases_from_io_tree[OF assms(1,2) fsm_initial fsm_initial h_framework_dynamic_completeness_and_finiteness(2)[OF assms]]
  by blast



subsection \<open>Partial Applications of the Pair-Framework\<close>

definition pair_framework_h_components :: "('a::linorder,'b::linorder,'c::linorder) fsm \<Rightarrow> nat \<Rightarrow>
                                           (('a,'b,'c) fsm \<Rightarrow> (('b \<times> 'c) list \<times> 'a) \<times> ('b \<times> 'c) list \<times> 'a \<Rightarrow> ('b \<times> 'c) prefix_tree \<Rightarrow> ('b \<times> 'c) prefix_tree) \<Rightarrow>
                                           ('b\<times>'c) prefix_tree" 
where
  "pair_framework_h_components M m get_separating_traces = (let 
    V = get_state_cover_assignment M
  in pair_framework M m (get_initial_test_suite_H V) (get_pairs_H V) get_separating_traces)"



lemma pair_framework_h_components_completeness_and_finiteness :
  fixes M1 :: "('a::linorder,'b::linorder,'c::linorder) fsm"
  fixes M2 :: "('e,'b,'c) fsm"
  assumes "observable M1"
  and     "observable M2"
  and     "minimal M1"
  and     "size_r M1 \<le> m"
  and     "size M2 \<le> m"
  and     "inputs M2 = inputs M1"
  and     "outputs M2 = outputs M1"
  and     "\<And> \<alpha> \<beta> t . \<alpha> \<in> L M1 \<Longrightarrow> \<beta> \<in> L M1 \<Longrightarrow> after_initial M1 \<alpha> \<noteq> after_initial M1 \<beta> \<Longrightarrow> \<exists> io \<in> set (get_separating_traces M1 ((\<alpha>,after_initial M1 \<alpha>),(\<beta>,after_initial M1 \<beta>)) t) \<union> (set (after t \<alpha>) \<inter> set (after t \<beta>)) . distinguishes M1 (after_initial M1 \<alpha>) (after_initial M1 \<beta>) io"
  and     "\<And> \<alpha> \<beta> t . \<alpha> \<in> L M1 \<Longrightarrow> \<beta> \<in> L M1 \<Longrightarrow> after_initial M1 \<alpha> \<noteq> after_initial M1 \<beta> \<Longrightarrow> finite_tree (get_separating_traces M1 ((\<alpha>,after_initial M1 \<alpha>),(\<beta>,after_initial M1 \<beta>)) t)"
shows "(L M1 = L M2) \<longleftrightarrow> ((L M1 \<inter> set (pair_framework_h_components M1 m get_separating_traces)) = (L M2 \<inter> set (pair_framework_h_components M1 m get_separating_traces)))"
and "finite_tree (pair_framework_h_components M1 m get_separating_traces)"
proof -
  show "(L M1 = L M2) \<longleftrightarrow> ((L M1 \<inter> set (pair_framework_h_components M1 m get_separating_traces)) = (L M2 \<inter> set (pair_framework_h_components M1 m get_separating_traces)))"
    using pair_framework_completeness[ OF assms(1,2,3,5,4,6,7) get_state_cover_assignment_is_state_cover_assignment
                                     , of "get_initial_test_suite_H (get_state_cover_assignment M1)" "get_pairs_H (get_state_cover_assignment M1)" get_separating_traces
                                     , OF get_initial_test_suite_H_set_and_finite(1)[of "get_state_cover_assignment M1" M1 m]
                                     , OF get_pairs_H_set(1)[OF assms(1) get_state_cover_assignment_is_state_cover_assignment, where m=m] assms(8)
                                     ]
    unfolding pair_framework_h_components_def Let_def 
    using get_pairs_H_set(1)[OF assms(1) get_state_cover_assignment_is_state_cover_assignment, where m=m]
    using assms(8) 
    unfolding pair_framework_h_components_def Let_def
    by presburger 


  show "finite_tree (pair_framework_h_components M1 m get_separating_traces)"
    using pair_framework_finiteness[of M1 get_separating_traces "get_initial_test_suite_H (get_state_cover_assignment M1)" m "get_pairs_H (get_state_cover_assignment M1)",
                                    OF assms(9) get_initial_test_suite_H_set_and_finite(2)[of "get_state_cover_assignment M1" M1 m] get_pairs_H_set(2)[OF assms(1) get_state_cover_assignment_is_state_cover_assignment] ]
    unfolding pair_framework_h_components_def Let_def
    by auto
qed


definition pair_framework_h_components_2 :: "('a::linorder,'b::linorder,'c::linorder) fsm \<Rightarrow> nat \<Rightarrow>
                                           (('a,'b,'c) fsm \<Rightarrow> (('b \<times> 'c) list \<times> 'a) \<times> ('b \<times> 'c) list \<times> 'a \<Rightarrow> ('b \<times> 'c) prefix_tree \<Rightarrow> ('b \<times> 'c) prefix_tree) \<Rightarrow>
                                            bool \<Rightarrow>
                                           ('b\<times>'c) prefix_tree" 
where
  "pair_framework_h_components_2 M m get_separating_traces c = (let 
    V = get_state_cover_assignment M
  in pair_framework M m (get_initial_test_suite_H_2 c V) (get_pairs_H V) get_separating_traces)"


lemma pair_framework_h_components_2_completeness_and_finiteness :
  fixes M1 :: "('a::linorder,'b::linorder,'c::linorder) fsm"
  fixes M2 :: "('e,'b,'c) fsm"
  assumes "observable M1"
  and     "observable M2"
  and     "minimal M1"
  and     "size_r M1 \<le> m"
  and     "size M2 \<le> m"
  and     "inputs M2 = inputs M1"
  and     "outputs M2 = outputs M1"
  and     "\<And> \<alpha> \<beta> t . \<alpha> \<in> L M1 \<Longrightarrow> \<beta> \<in> L M1 \<Longrightarrow> after_initial M1 \<alpha> \<noteq> after_initial M1 \<beta> \<Longrightarrow> \<exists> io \<in> set (get_separating_traces M1 ((\<alpha>,after_initial M1 \<alpha>),(\<beta>,after_initial M1 \<beta>)) t) \<union> (set (after t \<alpha>) \<inter> set (after t \<beta>)) . distinguishes M1 (after_initial M1 \<alpha>) (after_initial M1 \<beta>) io"
  and     "\<And> \<alpha> \<beta> t . \<alpha> \<in> L M1 \<Longrightarrow> \<beta> \<in> L M1 \<Longrightarrow> after_initial M1 \<alpha> \<noteq> after_initial M1 \<beta> \<Longrightarrow> finite_tree (get_separating_traces M1 ((\<alpha>,after_initial M1 \<alpha>),(\<beta>,after_initial M1 \<beta>)) t)"
shows "(L M1 = L M2) \<longleftrightarrow> ((L M1 \<inter> set (pair_framework_h_components_2 M1 m get_separating_traces c)) = (L M2 \<inter> set (pair_framework_h_components_2 M1 m get_separating_traces c)))"
and "finite_tree (pair_framework_h_components_2 M1 m get_separating_traces c)"
proof -
  show "(L M1 = L M2) \<longleftrightarrow> ((L M1 \<inter> set (pair_framework_h_components_2 M1 m get_separating_traces c)) = (L M2 \<inter> set (pair_framework_h_components_2 M1 m get_separating_traces c)))"
    using pair_framework_completeness[ OF assms(1,2,3,5,4,6,7) get_state_cover_assignment_is_state_cover_assignment
                                     , of "get_initial_test_suite_H_2 c (get_state_cover_assignment M1)" "get_pairs_H (get_state_cover_assignment M1)" get_separating_traces
                                     , OF get_initial_test_suite_H_2_set_and_finite(1)[of "get_state_cover_assignment M1" M1 m]
                                     , OF get_pairs_H_set(1)[OF assms(1) get_state_cover_assignment_is_state_cover_assignment, where m=m] assms(8)
                                     ]
    unfolding pair_framework_h_components_2_def Let_def 
    using get_pairs_H_set(1)[OF assms(1) get_state_cover_assignment_is_state_cover_assignment, where m=m]
    using assms(8) 
    unfolding pair_framework_h_components_def Let_def
    by presburger 


  show "finite_tree (pair_framework_h_components_2 M1 m get_separating_traces c)"
    using pair_framework_finiteness[of M1 get_separating_traces "get_initial_test_suite_H_2 c (get_state_cover_assignment M1)" m "get_pairs_H (get_state_cover_assignment M1)",
                                    OF assms(9) get_initial_test_suite_H_2_set_and_finite(2)[of c "get_state_cover_assignment M1" M1 m] get_pairs_H_set(2)[OF assms(1) get_state_cover_assignment_is_state_cover_assignment] ]
    unfolding pair_framework_h_components_2_def Let_def
    by auto
qed

subsection \<open>Code Generation\<close>


(* one-time pre-computation of OFSM tables *)
lemma h_framework_dynamic_code[code] :
  "h_framework_dynamic convergence_decisision M1 m completeInputTraces useInputHeuristic = (let 
      tables = (compute_ofsm_tables M1 (size M1 - 1));
      distMap = mapping_of (map (\<lambda> (q1,q2) . ((q1,q2), get_distinguishing_sequence_from_ofsm_tables_with_provided_tables tables M1 q1 q2))
                        (filter (\<lambda> qq . fst qq \<noteq> snd qq) (List.product (states_as_list M1) (states_as_list M1))));
      distHelper = (\<lambda> q1 q2 . if q1 \<in> states M1 \<and> q2 \<in> states M1 \<and> q1 \<noteq> q2 then the (Mapping.lookup distMap (q1,q2)) else get_distinguishing_sequence_from_ofsm_tables M1 q1 q2)
    in
      h_framework  M1
                   get_state_cover_assignment 
                   (handle_state_cover_dynamic completeInputTraces useInputHeuristic distHelper)
                   sort_unverified_transitions_by_state_cover_length
                   (handleUT_dynamic completeInputTraces useInputHeuristic distHelper convergence_decisision)
                   (handle_io_pair completeInputTraces useInputHeuristic)
                   simple_cg_initial
                   simple_cg_insert
                   simple_cg_lookup_with_conv
                   simple_cg_merge
                   m)"
  unfolding h_framework_dynamic_def
  apply (subst (1 2) get_distinguishing_sequence_from_ofsm_tables_precomputed[of M1])
  unfolding Let_def 
  by presburger

end