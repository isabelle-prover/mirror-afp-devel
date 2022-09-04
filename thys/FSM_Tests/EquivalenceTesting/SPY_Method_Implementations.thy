section \<open>Implementations of the SPY-Method\<close>

theory SPY_Method_Implementations
imports Intermediate_Frameworks Pair_Framework "../Distinguishability" Test_Suite_Representations "../OFSM_Tables_Refined" "HOL-Library.List_Lexorder"
begin

subsection \<open>Using the H-Framework\<close>

definition spy_method_via_h_framework :: "('a::linorder,'b::linorder,'c::linorder) fsm \<Rightarrow> nat \<Rightarrow> ('b\<times>'c) prefix_tree" where
  "spy_method_via_h_framework M m = h_framework_static_with_simple_graph M (\<lambda> k q . get_HSI M q) m"

definition spy_method_via_h_framework_lists :: "('a::linorder,'b::linorder,'c::linorder) fsm \<Rightarrow> nat \<Rightarrow> (('b\<times>'c) \<times> bool) list list" where
  "spy_method_via_h_framework_lists M m = sorted_list_of_maximal_sequences_in_tree (test_suite_from_io_tree M (initial M) (spy_method_via_h_framework M m))"

lemma spy_method_via_h_framework_completeness_and_finiteness :
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
shows "(L M1 = L M2) \<longleftrightarrow> ((L M1 \<inter> set (spy_method_via_h_framework M1 m)) = (L M2 \<inter> set (spy_method_via_h_framework M1 m)))"
and "finite_tree (spy_method_via_h_framework M1 m)"
  using h_framework_static_with_simple_graph_completeness_and_finiteness[OF assms, where dist_fun="(\<lambda> k q . get_HSI M1 q)"]
  using get_HSI_distinguishes[OF assms(1,3)]
  using get_HSI_finite 
  unfolding spy_method_via_h_framework_def 
  by blast+

lemma spy_method_via_h_framework_lists_completeness :
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
shows "(L M1 = L M2) \<longleftrightarrow> list_all (passes_test_case M2 (initial M2)) (spy_method_via_h_framework_lists M1 m)"
  using h_framework_static_with_simple_graph_lists_completeness[OF assms, where dist_fun="(\<lambda> k q . get_HSI M1 q)", OF _ get_HSI_finite]
  using get_HSI_distinguishes[OF assms(1,3)] 
  unfolding spy_method_via_h_framework_lists_def h_framework_static_with_simple_graph_lists_def spy_method_via_h_framework_def 
  by blast

subsection \<open>Using the SPY-Framework\<close>

definition spy_method_via_spy_framework :: "('a::linorder,'b::linorder,'c::linorder) fsm \<Rightarrow> nat \<Rightarrow> ('b\<times>'c) prefix_tree" where
  "spy_method_via_spy_framework M m = spy_framework_static_with_simple_graph M (\<lambda> k q . get_HSI M q) m"

lemma spy_method_via_spy_framework_completeness_and_finiteness :
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
shows "(L M1 = L M2) \<longleftrightarrow> ((L M1 \<inter> set (spy_method_via_spy_framework M1 m)) = (L M2 \<inter> set (spy_method_via_spy_framework M1 m)))"
and "finite_tree (spy_method_via_spy_framework M1 m)"  
  unfolding spy_method_via_spy_framework_def
  using spy_framework_static_with_simple_graph_completeness_and_finiteness[OF assms, of "(\<lambda> k q . get_HSI M1 q)"]
  using get_HSI_distinguishes[OF assms(1,3)]
  using get_HSI_finite[of M1]
  by blast+

definition spy_method_via_spy_framework_lists :: "('a::linorder,'b::linorder,'c::linorder) fsm \<Rightarrow> nat \<Rightarrow> (('b\<times>'c) \<times> bool) list list" where
  "spy_method_via_spy_framework_lists M m = sorted_list_of_maximal_sequences_in_tree (test_suite_from_io_tree M (initial M) (spy_method_via_spy_framework M m))"

lemma spy_method_via_spy_framework_lists_completeness :
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
shows "(L M1 = L M2) \<longleftrightarrow> list_all (passes_test_case M2 (initial M2)) (spy_method_via_spy_framework_lists M1 m)"
  unfolding spy_method_via_spy_framework_lists_def
            spy_method_via_spy_framework_completeness_and_finiteness(1)[OF assms]
            passes_test_cases_from_io_tree[OF assms(1,2) fsm_initial fsm_initial spy_method_via_spy_framework_completeness_and_finiteness(2)[OF assms]]
  by blast


subsection \<open>Code Generation\<close>


lemma spy_method_via_spy_framework_code[code] :
  "spy_method_via_spy_framework M m = (let 
    tables = (compute_ofsm_tables M (size M - 1));
    distMap = mapping_of (map (\<lambda> (q1,q2) . ((q1,q2), get_distinguishing_sequence_from_ofsm_tables_with_provided_tables tables M q1 q2))
                      (filter (\<lambda> qq . fst qq \<noteq> snd qq) (List.product (states_as_list M) (states_as_list M))));
    distHelper = (\<lambda> q1 q2 . if q1 \<in> states M \<and> q2 \<in> states M \<and> q1 \<noteq> q2 then the (Mapping.lookup distMap (q1,q2)) else get_distinguishing_sequence_from_ofsm_tables M q1 q2);
    
    hsiMap = mapping_of (map (\<lambda> q . (q,from_list (map (\<lambda>q' . distHelper q q') (filter ((\<noteq>) q) (states_as_list M))))) (states_as_list M));
    distFun = (\<lambda> k q . if q \<in> states M then the (Mapping.lookup hsiMap q) else get_HSI M q)
  in spy_framework_static_with_simple_graph M distFun m)"
(is "?f1 = ?f2")
proof -

  define hsiMap' where "hsiMap' = mapping_of (map (\<lambda> q . (q,from_list (map (\<lambda>q' . get_distinguishing_sequence_from_ofsm_tables M q q') (filter ((\<noteq>) q) (states_as_list M))))) (states_as_list M))"
  define distFun' where "distFun' = (\<lambda> M q . if q \<in> states M then the (Mapping.lookup hsiMap' q) else get_HSI M q)"

  have *: "?f2 = spy_framework_static_with_simple_graph M (\<lambda> k q . distFun' M q) m"
    unfolding distFun'_def hsiMap'_def Let_def
    apply (subst (2) get_distinguishing_sequence_from_ofsm_tables_precomputed[of M])
    unfolding Let_def  
    by presburger


  define hsiMap where "hsiMap = map_of (map (\<lambda> q . (q,from_list (map (\<lambda>q' . get_distinguishing_sequence_from_ofsm_tables M q q') (filter ((\<noteq>) q) (states_as_list M))))) (states_as_list M))"
  define distFun where "distFun = (\<lambda> M q . if q \<in> states M then the (hsiMap q) else get_HSI M q)"

  have "distinct (map fst (map (\<lambda> q . (q,from_list (map (\<lambda>q' . get_distinguishing_sequence_from_ofsm_tables M q q') (filter ((\<noteq>) q) (states_as_list M))))) (states_as_list M)))"
    using states_as_list_distinct
    by (metis map_pair_fst) 
  then have "Mapping.lookup hsiMap' = hsiMap"
    unfolding hsiMap_def hsiMap'_def  
    using mapping_of_map_of
    by blast
  then have "distFun' = distFun"
    unfolding distFun_def distFun'_def by meson
    
  have **:"distFun M = get_HSI M" 
  proof     
    fix q show "distFun M q = get_HSI M q"
    proof (cases "q \<in> states M")
      case True
      then have "q \<in> list.set (states_as_list M)"
        using states_as_list_set by blast
      then show ?thesis
        unfolding distFun_def hsiMap_def map_of_map_pair_entry get_HSI.simps
        using True
        by fastforce
    next
      case False
      then show ?thesis using distFun_def by auto
    qed
  qed
  
  show ?thesis
    unfolding * ** \<open>distFun' = distFun\<close> spy_method_via_spy_framework_def by simp
qed

lemma spy_method_via_h_framework_code[code] :
  "spy_method_via_h_framework M m = (let 
      tables = (compute_ofsm_tables M (size M - 1));
      distMap = mapping_of (map (\<lambda> (q1,q2) . ((q1,q2), get_distinguishing_sequence_from_ofsm_tables_with_provided_tables tables M q1 q2))
                        (filter (\<lambda> qq . fst qq \<noteq> snd qq) (List.product (states_as_list M) (states_as_list M))));
      distHelper = (\<lambda> q1 q2 . if q1 \<in> states M \<and> q2 \<in> states M \<and> q1 \<noteq> q2 then the (Mapping.lookup distMap (q1,q2)) else get_distinguishing_sequence_from_ofsm_tables M q1 q2);
      
      hsiMap = mapping_of (map (\<lambda> q . (q,from_list (map (\<lambda>q' . distHelper q q') (filter ((\<noteq>) q) (states_as_list M))))) (states_as_list M));
      distFun = (\<lambda> k q . if q \<in> states M then the (Mapping.lookup hsiMap q) else get_HSI M q)
    in h_framework_static_with_simple_graph M distFun m)"  
(is "?f1 = ?f2")
proof -

  define hsiMap' where "hsiMap' = mapping_of (map (\<lambda> q . (q,from_list (map (\<lambda>q' . get_distinguishing_sequence_from_ofsm_tables M q q') (filter ((\<noteq>) q) (states_as_list M))))) (states_as_list M))"
  define distFun' where "distFun' = (\<lambda> M q . if q \<in> states M then the (Mapping.lookup hsiMap' q) else get_HSI M q)"

  have *: "?f2 = h_framework_static_with_simple_graph M (\<lambda> k q . distFun' M q) m"
    unfolding distFun'_def hsiMap'_def Let_def
    apply (subst (2) get_distinguishing_sequence_from_ofsm_tables_precomputed[of M])
    unfolding Let_def  
    by presburger


  define hsiMap where "hsiMap = map_of (map (\<lambda> q . (q,from_list (map (\<lambda>q' . get_distinguishing_sequence_from_ofsm_tables M q q') (filter ((\<noteq>) q) (states_as_list M))))) (states_as_list M))"
  define distFun where "distFun = (\<lambda> M q . if q \<in> states M then the (hsiMap q) else get_HSI M q)"

  have "distinct (map fst (map (\<lambda> q . (q,from_list (map (\<lambda>q' . get_distinguishing_sequence_from_ofsm_tables M q q') (filter ((\<noteq>) q) (states_as_list M))))) (states_as_list M)))"
    using states_as_list_distinct
    by (metis map_pair_fst) 
  then have "Mapping.lookup hsiMap' = hsiMap"
    unfolding hsiMap_def hsiMap'_def  
    using mapping_of_map_of
    by blast
  then have "distFun' = distFun"
    unfolding distFun_def distFun'_def by meson
    
  have **:"distFun M = get_HSI M" 
  proof     
    fix q show "distFun M q = get_HSI M q"
    proof (cases "q \<in> states M")
      case True
      then have "q \<in> list.set (states_as_list M)"
        using states_as_list_set by blast
      then show ?thesis
        unfolding distFun_def hsiMap_def map_of_map_pair_entry get_HSI.simps
        using True
        by fastforce
    next
      case False
      then show ?thesis using distFun_def by auto
    qed
  qed
  
  show ?thesis
    unfolding * ** \<open>distFun' = distFun\<close> spy_method_via_h_framework_def by simp
qed



end 