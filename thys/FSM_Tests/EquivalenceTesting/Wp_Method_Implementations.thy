section \<open>Implementations of the Wp-Method\<close>

theory Wp_Method_Implementations
imports Intermediate_Frameworks Pair_Framework "../Distinguishability" Test_Suite_Representations "../OFSM_Tables_Refined" "HOL-Library.List_Lexorder"
begin

subsection \<open>Distinguishing Sets\<close>

fun add_distinguishing_set_or_state_identifier :: "nat \<Rightarrow> ('a :: linorder, 'b :: linorder, 'c :: linorder) fsm \<Rightarrow> (('b \<times> 'c) list \<times> 'a) \<times> ('b \<times> 'c) list \<times> 'a \<Rightarrow> ('b \<times> 'c) prefix_tree \<Rightarrow> ('b\<times>'c) prefix_tree" where
  "add_distinguishing_set_or_state_identifier k M ((io1,q1),(io2,q2)) t = (if length io1 = k \<or> length io2 = k
    then insert empty (get_distinguishing_sequence_from_ofsm_tables M q1 q2)
    else distinguishing_set M)"

lemma add_distinguishing_set_or_state_identifier_distinguishes :
  assumes "observable M"
  and     "minimal M"
  and     "\<alpha> \<in> L M"
  and     "\<beta> \<in> L M" 
  and     "after_initial M \<alpha> \<noteq> after_initial M \<beta>"   
shows "\<exists> io \<in> set (add_distinguishing_set_or_state_identifier k M ((\<alpha>,after_initial M \<alpha>),(\<beta>,after_initial M \<beta>)) t) \<union> (set (after t \<alpha>) \<inter> set (after t \<beta>)) . distinguishes M (after_initial M \<alpha>) (after_initial M \<beta>) io"
proof (cases "length \<alpha> = k \<or> length \<beta> = k")
  case False
  then show ?thesis 
    using distinguishing_set_distinguishes[OF assms(1,2) after_is_state[OF assms(1,3)] after_is_state[OF assms(1,4)] assms(5)]
    by auto
next
  case True
  then have "set ((add_distinguishing_set_or_state_identifier k) M ((\<alpha>,after_initial M \<alpha>),(\<beta>,after_initial M \<beta>)) t) = set (insert empty (get_distinguishing_sequence_from_ofsm_tables M (after_initial M \<alpha>) (after_initial M \<beta>)))"
    by auto
  then have "get_distinguishing_sequence_from_ofsm_tables M (after_initial M \<alpha>) (after_initial M \<beta>) \<in> set ((add_distinguishing_set_or_state_identifier k) M ((\<alpha>,after_initial M \<alpha>),(\<beta>,after_initial M \<beta>)) t) \<union> (set (after t \<alpha>) \<inter> set (after t \<beta>))"
    unfolding insert_set by auto
  then show ?thesis
    by (meson after_is_state assms(1) assms(2) assms(3) assms(4) assms(5) get_distinguishing_sequence_from_ofsm_tables_distinguishes) 
qed


lemma add_distinguishing_set_or_state_identifier_finite : 
  "finite_tree ((add_distinguishing_set_or_state_identifier k) M ((\<alpha>,after_initial M \<alpha>),(\<beta>,after_initial M \<beta>)) t)"
proof (cases "length \<alpha> = k \<or> length \<beta> = k")
  case False
  then show ?thesis 
    unfolding add_distinguishing_set.simps distinguishing_set.simps Let_def
    using from_list_finite_tree
    by simp
next
  case True
  then have "((add_distinguishing_set_or_state_identifier k) M ((\<alpha>,after_initial M \<alpha>),(\<beta>,after_initial M \<beta>)) t) = (insert empty (get_distinguishing_sequence_from_ofsm_tables M (after_initial M \<alpha>) (after_initial M \<beta>)))"
    by auto
  then show ?thesis
    using insert_finite_tree[OF empty_finite_tree] by metis
qed  



fun distinguishing_set_or_state_identifier :: "nat \<Rightarrow> ('a :: linorder, 'b :: linorder, 'c :: linorder) fsm \<Rightarrow> nat \<Rightarrow> 'a \<Rightarrow> ('b\<times>'c) prefix_tree" where
  "distinguishing_set_or_state_identifier l M k q = (if k = l 
    then get_HSI M q
    else distinguishing_set M)"

lemma get_HSI_subset :
  assumes "observable M"
  and     "minimal M"
  and     "q \<in> states M"
shows "set (get_HSI M q) \<subseteq> set (distinguishing_set M)"
proof 
  fix io assume "io \<in> set (get_HSI M q)"

  show "io \<in> set (distinguishing_set M)"
  proof (cases "io = []")
    case True
    then show ?thesis by auto
  next
    case False

    then obtain io' where *:"io@io' \<in> list.set (map (get_distinguishing_sequence_from_ofsm_tables M q) (filter ((\<noteq>) q) (states_as_list M)))"
      using \<open>io \<in> set (get_HSI M q)\<close>
      unfolding get_HSI.simps from_list_set
      by blast
    obtain q' where "q \<noteq> q'" and "q' \<in> states M" and "io@io' = get_distinguishing_sequence_from_ofsm_tables M q q'"
      using states_as_list_set[of M] filter_map_elem[OF *]
      by blast

    have "(q,q') \<in> list.set (filter (\<lambda> (x,y) . x \<noteq> y) (list_ordered_pairs (states_as_list M)))
            \<or> (q',q) \<in> list.set (filter (\<lambda> (x,y) . x \<noteq> y) (list_ordered_pairs (states_as_list M)))"
      using list_ordered_pairs_set_containment[of q "states_as_list M" q'] \<open>q \<in> states M\<close> \<open>q' \<in> states M\<close> \<open>q \<noteq> q'\<close>
      unfolding states_as_list_set
      by force
    moreover define pairs where pairs: "pairs = filter (\<lambda> (x,y) . x \<noteq> y) (list_ordered_pairs (states_as_list M))"
    ultimately have "(q,q') \<in> list.set pairs \<or> (q',q) \<in> list.set pairs"
      by auto      
    then have "get_distinguishing_sequence_from_ofsm_tables M q q' \<in> list.set (map (case_prod (get_distinguishing_sequence_from_ofsm_tables M)) pairs)"
      using get_distinguishing_sequence_from_ofsm_tables_sym[OF assms \<open>q' \<in> states M\<close> \<open>q \<noteq> q'\<close>, symmetric]
      by (metis case_prod_conv map_set)
    then have "io@io' \<in> set (distinguishing_set M)"
      unfolding \<open>io@io' = get_distinguishing_sequence_from_ofsm_tables M q q'\<close> distinguishing_set.simps Let_def pairs
      using from_list_set_elem
      by blast
    then show ?thesis 
      using set_prefix by metis
  qed
qed

lemma distinguishing_set_or_state_identifier_distinguishes :
  assumes "observable M"
  and     "minimal M"
  and     "q1 \<in> states M" and "q2 \<in> states M" and "q1 \<noteq> q2"
shows "\<exists> io . \<forall> k1 k2 . io \<in> set (distinguishing_set_or_state_identifier l M k1 q1) \<inter> set (distinguishing_set_or_state_identifier l M k2 q2) \<and> distinguishes M q1 q2 io"
  using get_HSI_distinguishes[OF assms]
  using distinguishing_set_distinguishes[OF assms]
  using get_HSI_subset[OF assms(1,2,3)]
  using get_HSI_subset[OF assms(1,2,4)]
  unfolding distinguishing_set_or_state_identifier.simps
  by auto

lemma distinguishing_set_or_state_identifier_finite :
  "finite_tree (distinguishing_set_or_state_identifier l M k q)"
  using get_HSI_finite[of M q]
  using distinguishing_set_finite[of M]
  unfolding distinguishing_set_or_state_identifier.simps 
  by (cases "k = l"; force)



subsection \<open>Using the H-Framework\<close>

definition wp_method_via_h_framework :: "('a::linorder,'b::linorder,'c::linorder) fsm \<Rightarrow> nat \<Rightarrow> ('b\<times>'c) prefix_tree" where
  "wp_method_via_h_framework M m = h_framework_static_with_empty_graph M (distinguishing_set_or_state_identifier (Suc (m - size_r M)) M) m"

definition wp_method_via_h_framework_lists :: "('a::linorder,'b::linorder,'c::linorder) fsm \<Rightarrow> nat \<Rightarrow> (('b\<times>'c) \<times> bool) list list" where
  "wp_method_via_h_framework_lists M m = sorted_list_of_maximal_sequences_in_tree (test_suite_from_io_tree M (initial M) (wp_method_via_h_framework M m))"

lemma wp_method_via_h_framework_completeness_and_finiteness :
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
shows "(L M1 = L M2) \<longleftrightarrow> ((L M1 \<inter> set (wp_method_via_h_framework M1 m)) = (L M2 \<inter> set (wp_method_via_h_framework M1 m)))"
and "finite_tree (wp_method_via_h_framework M1 m)"
  using h_framework_static_with_empty_graph_completeness_and_finiteness[OF assms, where dist_fun="distinguishing_set_or_state_identifier (Suc (m - size_r M1)) M1"]
  using distinguishing_set_or_state_identifier_distinguishes[OF assms(1,3)]
  using distinguishing_set_or_state_identifier_finite 
  unfolding wp_method_via_h_framework_def 
  by blast+

lemma wp_method_via_h_framework_lists_completeness :
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
shows "(L M1 = L M2) \<longleftrightarrow> list_all (passes_test_case M2 (initial M2)) (wp_method_via_h_framework_lists M1 m)"
  using h_framework_static_with_empty_graph_lists_completeness[OF assms, where dist_fun="distinguishing_set_or_state_identifier (Suc (m - size_r M1)) M1", OF _ distinguishing_set_or_state_identifier_finite]
  using distinguishing_set_or_state_identifier_distinguishes[OF assms(1,3)] 
  unfolding wp_method_via_h_framework_lists_def h_framework_static_with_empty_graph_lists_def wp_method_via_h_framework_def 
  by blast


subsection \<open>Using the SPY-Framework\<close>

definition wp_method_via_spy_framework :: "('a::linorder,'b::linorder,'c::linorder) fsm \<Rightarrow> nat \<Rightarrow> ('b\<times>'c) prefix_tree" where
  "wp_method_via_spy_framework M m = spy_framework_static_with_empty_graph M (distinguishing_set_or_state_identifier (Suc (m - size_r M)) M) m"

lemma wp_method_via_spy_framework_completeness_and_finiteness :
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
shows "(L M1 = L M2) \<longleftrightarrow> ((L M1 \<inter> set (wp_method_via_spy_framework M1 m)) = (L M2 \<inter> set (wp_method_via_spy_framework M1 m)))"
and "finite_tree (wp_method_via_spy_framework M1 m)"  
  unfolding wp_method_via_spy_framework_def
  using spy_framework_static_with_empty_graph_completeness_and_finiteness[OF assms, of "distinguishing_set_or_state_identifier (Suc (m - size_r M1)) M1"]
  using distinguishing_set_or_state_identifier_distinguishes[OF assms(1,3)]
  using distinguishing_set_or_state_identifier_finite
  by metis+

definition wp_method_via_spy_framework_lists :: "('a::linorder,'b::linorder,'c::linorder) fsm \<Rightarrow> nat \<Rightarrow> (('b\<times>'c) \<times> bool) list list" where
  "wp_method_via_spy_framework_lists M m = sorted_list_of_maximal_sequences_in_tree (test_suite_from_io_tree M (initial M) (wp_method_via_spy_framework M m))"

lemma wp_method_via_spy_framework_lists_completeness :
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
shows "(L M1 = L M2) \<longleftrightarrow> list_all (passes_test_case M2 (initial M2)) (wp_method_via_spy_framework_lists M1 m)"
  unfolding wp_method_via_spy_framework_lists_def
            wp_method_via_spy_framework_completeness_and_finiteness(1)[OF assms]
            passes_test_cases_from_io_tree[OF assms(1,2) fsm_initial fsm_initial wp_method_via_spy_framework_completeness_and_finiteness(2)[OF assms]]
  by blast


subsection \<open>Code Generation\<close>

lemma wp_method_via_spy_framework_code[code] :
  "wp_method_via_spy_framework M m = (let 
      tables = (compute_ofsm_tables M (size M - 1));
      distMap = mapping_of (map (\<lambda> (q1,q2) . ((q1,q2), get_distinguishing_sequence_from_ofsm_tables_with_provided_tables tables M q1 q2))
                        (filter (\<lambda> qq . fst qq \<noteq> snd qq) (List.product (states_as_list M) (states_as_list M))));
      distHelper = (\<lambda> q1 q2 . if q1 \<in> states M \<and> q2 \<in> states M \<and> q1 \<noteq> q2 then the (Mapping.lookup distMap (q1,q2)) else get_distinguishing_sequence_from_ofsm_tables M q1 q2);
      pairs = filter (\<lambda> (x,y) . x \<noteq> y) (list_ordered_pairs (states_as_list M));
      distSet = from_list (map (case_prod distHelper) pairs);
      hsiMap = mapping_of (map (\<lambda> q . (q,from_list (map (\<lambda>q' . distHelper q q') (filter ((\<noteq>) q) (states_as_list M))))) (states_as_list M));
      l = (Suc (m - size_r M));
      distFun = (\<lambda> k q . if k = l 
                      then (if q \<in> states M then the (Mapping.lookup hsiMap q) else get_HSI M q)
                      else distSet)
    in spy_framework_static_with_empty_graph M distFun m)"   
(is "?f1 = ?f2") 
proof -
  define hsiMap' where "hsiMap' = mapping_of (map (\<lambda> q . (q,from_list (map (\<lambda>q' . get_distinguishing_sequence_from_ofsm_tables M q q') (filter ((\<noteq>) q) (states_as_list M))))) (states_as_list M))"
  define distFun' where "distFun' = (\<lambda> k q . if k = (Suc (m - size_r M))
                      then (if q \<in> states M then the (Mapping.lookup hsiMap' q) else get_HSI M q)
                      else distinguishing_set M)"
  have *: "?f2 = spy_framework_static_with_empty_graph M distFun' m"
    unfolding distFun'_def hsiMap'_def distinguishing_set.simps Let_def
    apply (subst (3 4 ) get_distinguishing_sequence_from_ofsm_tables_precomputed[of M])
    unfolding Let_def  
    by presburger

  define hsiMap where "hsiMap = map_of (map (\<lambda> q . (q,from_list (map (\<lambda>q' . get_distinguishing_sequence_from_ofsm_tables M q q') (filter ((\<noteq>) q) (states_as_list M))))) (states_as_list M))"
  define distFun where "distFun = (\<lambda> k q . if k = (Suc (m - size_r M))
                      then (if q \<in> states M then the (hsiMap q) else get_HSI M q)
                      else distinguishing_set M)"

  have "distinct (map fst (map (\<lambda> q . (q,from_list (map (\<lambda>q' . get_distinguishing_sequence_from_ofsm_tables M q q') (filter ((\<noteq>) q) (states_as_list M))))) (states_as_list M)))"
    using states_as_list_distinct
    by (metis map_pair_fst) 
  then have "Mapping.lookup hsiMap' = hsiMap"
    unfolding hsiMap_def hsiMap'_def  
    using mapping_of_map_of
    by blast
  then have "distFun' = distFun"
    unfolding distFun_def distFun'_def by meson

  have **:"distFun' = (distinguishing_set_or_state_identifier (Suc (m - size_r M)) M)" 
  proof     
    fix k show "distFun' k = (distinguishing_set_or_state_identifier (Suc (m - size_r M)) M) k"
    proof (cases "k = (Suc (m - size_r M))")
      case False
      then show ?thesis 
        unfolding distFun_def distinguishing_set_or_state_identifier.simps \<open>distFun' = distFun\<close> by auto
    next
      case True
      then have "distFun k = (\<lambda> q . (if q \<in> states M then the (hsiMap q) else get_HSI M q))"
            and "(distinguishing_set_or_state_identifier (Suc (m - size_r M)) M) k = (\<lambda> q . get_HSI M q)"
        unfolding distFun_def distinguishing_set_or_state_identifier.simps by auto
      moreover have "(\<lambda> q . (if q \<in> states M then the (hsiMap q) else get_HSI M q)) = (\<lambda> q . get_HSI M q)"
      proof 
        fix q show "(if q \<in> states M then the (hsiMap q) else get_HSI M q) = get_HSI M q"
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
      ultimately show ?thesis unfolding \<open>distFun' = distFun\<close> by simp
    qed
  qed
  
  show ?thesis
    unfolding * ** wp_method_via_spy_framework_def by simp
qed

lemma wp_method_via_h_framework_code[code] :
  "wp_method_via_h_framework M m = (let 
      tables = (compute_ofsm_tables M (size M - 1));
      distMap = mapping_of (map (\<lambda> (q1,q2) . ((q1,q2), get_distinguishing_sequence_from_ofsm_tables_with_provided_tables tables M q1 q2))
                        (filter (\<lambda> qq . fst qq \<noteq> snd qq) (List.product (states_as_list M) (states_as_list M))));
      distHelper = (\<lambda> q1 q2 . if q1 \<in> states M \<and> q2 \<in> states M \<and> q1 \<noteq> q2 then the (Mapping.lookup distMap (q1,q2)) else get_distinguishing_sequence_from_ofsm_tables M q1 q2);
      pairs = filter (\<lambda> (x,y) . x \<noteq> y) (list_ordered_pairs (states_as_list M));
      distSet = from_list (map (case_prod distHelper) pairs);
      hsiMap = mapping_of (map (\<lambda> q . (q,from_list (map (\<lambda>q' . distHelper q q') (filter ((\<noteq>) q) (states_as_list M))))) (states_as_list M));
      l = (Suc (m - size_r M));
      distFun = (\<lambda> k q . if k = l 
                      then (if q \<in> states M then the (Mapping.lookup hsiMap q) else get_HSI M q)
                      else distSet)
    in h_framework_static_with_empty_graph M distFun m)"  
(is "?f1 = ?f2") 
proof -
  define hsiMap' where "hsiMap' = mapping_of (map (\<lambda> q . (q,from_list (map (\<lambda>q' . get_distinguishing_sequence_from_ofsm_tables M q q') (filter ((\<noteq>) q) (states_as_list M))))) (states_as_list M))"
  define distFun' where "distFun' = (\<lambda> k q . if k = (Suc (m - size_r M))
                      then (if q \<in> states M then the (Mapping.lookup hsiMap' q) else get_HSI M q)
                      else distinguishing_set M)"
  have *: "?f2 = h_framework_static_with_empty_graph M distFun' m"
    unfolding distFun'_def hsiMap'_def distinguishing_set.simps Let_def
    apply (subst (3 4 ) get_distinguishing_sequence_from_ofsm_tables_precomputed[of M])
    unfolding Let_def  
    by presburger

  define hsiMap where "hsiMap = map_of (map (\<lambda> q . (q,from_list (map (\<lambda>q' . get_distinguishing_sequence_from_ofsm_tables M q q') (filter ((\<noteq>) q) (states_as_list M))))) (states_as_list M))"
  define distFun where "distFun = (\<lambda> k q . if k = (Suc (m - size_r M))
                      then (if q \<in> states M then the (hsiMap q) else get_HSI M q)
                      else distinguishing_set M)"

  have "distinct (map fst (map (\<lambda> q . (q,from_list (map (\<lambda>q' . get_distinguishing_sequence_from_ofsm_tables M q q') (filter ((\<noteq>) q) (states_as_list M))))) (states_as_list M)))"
    using states_as_list_distinct
    by (metis map_pair_fst) 
  then have "Mapping.lookup hsiMap' = hsiMap"
    unfolding hsiMap_def hsiMap'_def  
    using mapping_of_map_of
    by blast
  then have "distFun' = distFun"
    unfolding distFun_def distFun'_def by meson

  have **:"distFun' = (distinguishing_set_or_state_identifier (Suc (m - size_r M)) M)" 
  proof     
    fix k show "distFun' k = (distinguishing_set_or_state_identifier (Suc (m - size_r M)) M) k"
    proof (cases "k = (Suc (m - size_r M))")
      case False
      then show ?thesis 
        unfolding distFun_def distinguishing_set_or_state_identifier.simps \<open>distFun' = distFun\<close> by auto
    next
      case True
      then have "distFun k = (\<lambda> q . (if q \<in> states M then the (hsiMap q) else get_HSI M q))"
            and "(distinguishing_set_or_state_identifier (Suc (m - size_r M)) M) k = (\<lambda> q . get_HSI M q)"
        unfolding distFun_def distinguishing_set_or_state_identifier.simps by auto
      moreover have "(\<lambda> q . (if q \<in> states M then the (hsiMap q) else get_HSI M q)) = (\<lambda> q . get_HSI M q)"
      proof 
        fix q show "(if q \<in> states M then the (hsiMap q) else get_HSI M q) = get_HSI M q"
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
      ultimately show ?thesis unfolding \<open>distFun' = distFun\<close> by simp
    qed
  qed
  
  show ?thesis
    unfolding * ** wp_method_via_h_framework_def by simp
qed


end 