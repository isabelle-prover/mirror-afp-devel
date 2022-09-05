section \<open>Implementations of the W-Method\<close>

theory W_Method_Implementations
imports Intermediate_Frameworks Pair_Framework "../Distinguishability" Test_Suite_Representations "../OFSM_Tables_Refined" "HOL-Library.List_Lexorder"
begin

subsection \<open>Using the H-Framework\<close>

definition w_method_via_h_framework :: "('a::linorder,'b::linorder,'c::linorder) fsm \<Rightarrow> nat \<Rightarrow> ('b\<times>'c) prefix_tree" where
  "w_method_via_h_framework M m = h_framework_static_with_empty_graph M (\<lambda> k q . distinguishing_set M) m"

definition w_method_via_h_framework_lists :: "('a::linorder,'b::linorder,'c::linorder) fsm \<Rightarrow> nat \<Rightarrow> (('b\<times>'c) \<times> bool) list list" where
  "w_method_via_h_framework_lists M m = sorted_list_of_maximal_sequences_in_tree (test_suite_from_io_tree M (initial M) (w_method_via_h_framework M m))"

lemma w_method_via_h_framework_completeness_and_finiteness :
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
shows "(L M1 = L M2) \<longleftrightarrow> ((L M1 \<inter> set (w_method_via_h_framework M1 m)) = (L M2 \<inter> set (w_method_via_h_framework M1 m)))"
and "finite_tree (w_method_via_h_framework M1 m)"
  using h_framework_static_with_empty_graph_completeness_and_finiteness[OF assms, where dist_fun="(\<lambda> k q . distinguishing_set M1)"]
  using distinguishing_set_distinguishes[OF assms(1,3)]
  using distinguishing_set_finite 
  unfolding w_method_via_h_framework_def 
  by blast+

lemma w_method_via_h_framework_lists_completeness :
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
shows "(L M1 = L M2) \<longleftrightarrow> list_all (passes_test_case M2 (initial M2)) (w_method_via_h_framework_lists M1 m)"
  using h_framework_static_with_empty_graph_lists_completeness[OF assms, where dist_fun="(\<lambda> k q . distinguishing_set M1)", OF _ distinguishing_set_finite]
  using distinguishing_set_distinguishes[OF assms(1,3)] 
  unfolding w_method_via_h_framework_lists_def h_framework_static_with_empty_graph_lists_def w_method_via_h_framework_def 
  by blast



definition w_method_via_h_framework_2 :: "('a::linorder,'b::linorder,'c::linorder) fsm \<Rightarrow> nat \<Rightarrow> ('b\<times>'c) prefix_tree" where
  "w_method_via_h_framework_2 M m = h_framework_static_with_empty_graph M (\<lambda> k q . distinguishing_set_reduced M) m"

definition w_method_via_h_framework_2_lists :: "('a::linorder,'b::linorder,'c::linorder) fsm \<Rightarrow> nat \<Rightarrow> (('b\<times>'c) \<times> bool) list list" where
  "w_method_via_h_framework_2_lists M m = sorted_list_of_maximal_sequences_in_tree (test_suite_from_io_tree M (initial M) (w_method_via_h_framework_2 M m))"

lemma w_method_via_h_framework_2_completeness_and_finiteness :
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
shows "(L M1 = L M2) \<longleftrightarrow> ((L M1 \<inter> set (w_method_via_h_framework_2 M1 m)) = (L M2 \<inter> set (w_method_via_h_framework_2 M1 m)))"
and "finite_tree (w_method_via_h_framework_2 M1 m)"
  using h_framework_static_with_empty_graph_completeness_and_finiteness[OF assms, where dist_fun="(\<lambda> k q . distinguishing_set_reduced M1)"]
  using distinguishing_set_reduced_distinguishes[OF assms(1,3)]
  using distinguishing_set_reduced_finite 
  unfolding w_method_via_h_framework_2_def 
  by blast+

lemma w_method_via_h_framework_lists_2_completeness :
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
shows "(L M1 = L M2) \<longleftrightarrow> list_all (passes_test_case M2 (initial M2)) (w_method_via_h_framework_2_lists M1 m)"
  using h_framework_static_with_empty_graph_lists_completeness[OF assms, where dist_fun="(\<lambda> k q . distinguishing_set_reduced M1)", OF _ distinguishing_set_reduced_finite]
  using distinguishing_set_reduced_distinguishes[OF assms(1,3)] 
  unfolding w_method_via_h_framework_2_lists_def h_framework_static_with_empty_graph_lists_def w_method_via_h_framework_2_def 
  by blast


subsection \<open>Using the SPY-Framework\<close>

definition w_method_via_spy_framework :: "('a::linorder,'b::linorder,'c::linorder) fsm \<Rightarrow> nat \<Rightarrow> ('b\<times>'c) prefix_tree" where
  "w_method_via_spy_framework M m = spy_framework_static_with_empty_graph M (\<lambda> k q . distinguishing_set M) m"

lemma w_method_via_spy_framework_completeness_and_finiteness :
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
shows "(L M1 = L M2) \<longleftrightarrow> ((L M1 \<inter> set (w_method_via_spy_framework M1 m)) = (L M2 \<inter> set (w_method_via_spy_framework M1 m)))"
and "finite_tree (w_method_via_spy_framework M1 m)"  
  unfolding w_method_via_spy_framework_def
  using spy_framework_static_with_empty_graph_completeness_and_finiteness[OF assms, of "(\<lambda> k q . distinguishing_set M1)"]
  using distinguishing_set_distinguishes[OF assms(1,3)]
  using distinguishing_set_finite[of M1]
  by (metis IntI)+

definition w_method_via_spy_framework_lists :: "('a::linorder,'b::linorder,'c::linorder) fsm \<Rightarrow> nat \<Rightarrow> (('b\<times>'c) \<times> bool) list list" where
  "w_method_via_spy_framework_lists M m = sorted_list_of_maximal_sequences_in_tree (test_suite_from_io_tree M (initial M) (w_method_via_spy_framework M m))"

lemma w_method_via_spy_framework_lists_completeness :
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
shows "(L M1 = L M2) \<longleftrightarrow> list_all (passes_test_case M2 (initial M2)) (w_method_via_spy_framework_lists M1 m)"
  unfolding w_method_via_spy_framework_lists_def
            w_method_via_spy_framework_completeness_and_finiteness(1)[OF assms]
            passes_test_cases_from_io_tree[OF assms(1,2) fsm_initial fsm_initial w_method_via_spy_framework_completeness_and_finiteness(2)[OF assms]]
  by blast


subsection \<open>Using the Pair-Framework\<close>

definition w_method_via_pair_framework :: "('a::linorder,'b::linorder,'c::linorder) fsm \<Rightarrow> nat \<Rightarrow> ('b\<times>'c) prefix_tree" where
  "w_method_via_pair_framework M m = pair_framework_h_components M m add_distinguishing_set"


lemma w_method_via_pair_framework_completeness_and_finiteness :
  assumes "observable M"
  and     "observable I"
  and     "minimal M"
  and     "size I \<le> m"
  and     "m \<ge> size_r M"
  and     "inputs I = inputs M"
  and     "outputs I = outputs M"
shows "(L M = L I) \<longleftrightarrow> (L M \<inter> set (w_method_via_pair_framework M m) = L I \<inter> set (w_method_via_pair_framework M m))"
and   "finite_tree (w_method_via_pair_framework M m)"
  using pair_framework_h_components_completeness_and_finiteness[OF assms(1,2,3,5,4,6,7), where get_separating_traces="add_distinguishing_set", OF add_distinguishing_set_distinguishes[OF assms(1,3)] add_distinguishing_set_finite]
  using get_distinguishing_sequence_from_ofsm_tables_distinguishes[OF assms(1,3)]
  unfolding w_method_via_pair_framework_def[symmetric]
  by blast+

definition w_method_via_pair_framework_lists :: "('a::linorder,'b::linorder,'c::linorder) fsm \<Rightarrow> nat \<Rightarrow> (('b\<times>'c) \<times> bool) list list" where
  "w_method_via_pair_framework_lists M m = sorted_list_of_maximal_sequences_in_tree (test_suite_from_io_tree M (initial M) (w_method_via_pair_framework M m))"

lemma w_method_implementation_lists_completeness :
  assumes "observable M"
  and     "observable I"
  and     "minimal M"
  and     "size I \<le> m"
  and     "m \<ge> size_r M"
  and     "inputs I = inputs M"
  and     "outputs I = outputs M"
shows "(L M = L I) \<longleftrightarrow> list_all (passes_test_case I (initial I)) (w_method_via_pair_framework_lists M m)"
unfolding w_method_via_pair_framework_lists_def
            w_method_via_pair_framework_completeness_and_finiteness(1)[OF assms]
            passes_test_cases_from_io_tree[OF assms(1,2) fsm_initial fsm_initial w_method_via_pair_framework_completeness_and_finiteness(2)[OF assms]]
  by blast



subsection \<open>Code Generation\<close>

lemma w_method_via_pair_framework_code[code] :
  "w_method_via_pair_framework M m = (let 
      tables = (compute_ofsm_tables M (size M - 1));
      distMap = mapping_of (map (\<lambda> (q1,q2) . ((q1,q2), get_distinguishing_sequence_from_ofsm_tables_with_provided_tables tables M q1 q2))
                        (filter (\<lambda> qq . fst qq \<noteq> snd qq) (List.product (states_as_list M) (states_as_list M))));
      distHelper = (\<lambda> q1 q2 . if q1 \<in> states M \<and> q2 \<in> states M \<and> q1 \<noteq> q2 then the (Mapping.lookup distMap (q1,q2)) else get_distinguishing_sequence_from_ofsm_tables M q1 q2);
      pairs = filter (\<lambda> (x,y) . x \<noteq> y) (list_ordered_pairs (states_as_list M));
      distSet = from_list (map (case_prod distHelper) pairs);
      distFun = (\<lambda>  M x t . distSet)
    in pair_framework_h_components M m distFun)"  
  unfolding w_method_via_pair_framework_def pair_framework_h_components_def pair_framework_def
  unfolding add_distinguishing_set.simps
  unfolding distinguishing_set.simps
  apply (subst get_distinguishing_sequence_from_ofsm_tables_precomputed[of M])
  unfolding Let_def 
  by presburger

lemma w_method_via_spy_framework_code[code] :
  "w_method_via_spy_framework M m = (let 
      tables = (compute_ofsm_tables M (size M - 1));
      distMap = mapping_of (map (\<lambda> (q1,q2) . ((q1,q2), get_distinguishing_sequence_from_ofsm_tables_with_provided_tables tables M q1 q2))
                        (filter (\<lambda> qq . fst qq \<noteq> snd qq) (List.product (states_as_list M) (states_as_list M))));
      distHelper = (\<lambda> q1 q2 . if q1 \<in> states M \<and> q2 \<in> states M \<and> q1 \<noteq> q2 then the (Mapping.lookup distMap (q1,q2)) else get_distinguishing_sequence_from_ofsm_tables M q1 q2);
      pairs = filter (\<lambda> (x,y) . x \<noteq> y) (list_ordered_pairs (states_as_list M));
      distSet = from_list (map (case_prod distHelper) pairs);
      distFun = (\<lambda> k q . distSet)
    in spy_framework_static_with_empty_graph M distFun m)"  
  unfolding w_method_via_spy_framework_def
  unfolding add_distinguishing_set.simps
  unfolding distinguishing_set.simps
  apply (subst get_distinguishing_sequence_from_ofsm_tables_precomputed[of M])
  unfolding Let_def
  by presburger

lemma w_method_via_h_framework_code[code] :
  "w_method_via_h_framework M m = (let 
      tables = (compute_ofsm_tables M (size M - 1));
      distMap = mapping_of (map (\<lambda> (q1,q2) . ((q1,q2), get_distinguishing_sequence_from_ofsm_tables_with_provided_tables tables M q1 q2))
                        (filter (\<lambda> qq . fst qq \<noteq> snd qq) (List.product (states_as_list M) (states_as_list M))));
      distHelper = (\<lambda> q1 q2 . if q1 \<in> states M \<and> q2 \<in> states M \<and> q1 \<noteq> q2 then the (Mapping.lookup distMap (q1,q2)) else get_distinguishing_sequence_from_ofsm_tables M q1 q2);
      pairs = filter (\<lambda> (x,y) . x \<noteq> y) (list_ordered_pairs (states_as_list M));
      distSet = from_list (map (case_prod distHelper) pairs);
      distFun = (\<lambda> k q . distSet)
    in h_framework_static_with_empty_graph M distFun m)"  
  unfolding w_method_via_h_framework_def
  unfolding distinguishing_set.simps
  apply (subst get_distinguishing_sequence_from_ofsm_tables_precomputed[of M])
  unfolding Let_def
  by presburger


lemma w_method_via_h_framework_2_code[code] :
  "w_method_via_h_framework_2 M m = (let 
      tables = (compute_ofsm_tables M (size M - 1));
      distMap = mapping_of (map (\<lambda> (q1,q2) . ((q1,q2), get_distinguishing_sequence_from_ofsm_tables_with_provided_tables tables M q1 q2))
                        (filter (\<lambda> qq . fst qq \<noteq> snd qq) (List.product (states_as_list M) (states_as_list M))));
      distHelper = (\<lambda> q1 q2 . if q1 \<in> states M \<and> q2 \<in> states M \<and> q1 \<noteq> q2 then the (Mapping.lookup distMap (q1,q2)) else get_distinguishing_sequence_from_ofsm_tables M q1 q2);
      pairs = filter (\<lambda> (x,y) . x \<noteq> y) (list_ordered_pairs (states_as_list M));
      handlePair = (\<lambda> W (q,q') . if contains_distinguishing_trace M W q q'
                                then W
                                else insert W (distHelper q q'));
      distSet = foldl handlePair empty pairs;
      distFun = (\<lambda> k q . distSet)
    in h_framework_static_with_empty_graph M distFun m)"  
  unfolding w_method_via_h_framework_2_def
  unfolding distinguishing_set_reduced.simps
  apply (subst get_distinguishing_sequence_from_ofsm_tables_precomputed[of M])
  unfolding Let_def
  by presburger

end 