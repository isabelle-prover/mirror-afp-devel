section \<open>Intermediate Implementations\<close>

text \<open>This theory implements various functions to be supplied to the H, SPY, and Pair-Frameworks.\<close>


theory Intermediate_Implementations
  imports H_Framework SPY_Framework Pair_Framework "../Distinguishability"  Automatic_Refinement.Misc 
begin



subsection \<open>Functions for the Pair Framework\<close>

definition get_initial_test_suite_H :: "('a,'b,'c) state_cover_assignment \<Rightarrow> 
                                    ('a::linorder,'b::linorder,'c::linorder) fsm \<Rightarrow>                        
                                    nat \<Rightarrow>
                                    ('b\<times>'c) prefix_tree" 
where
  "get_initial_test_suite_H V M m = 
    (let 
      rstates       = reachable_states_as_list M;
      n             = size_r M;
      iM            = inputs_as_list M; 
      T             = from_list (concat (map (\<lambda>q . map (\<lambda>\<tau>. (V q)@\<tau>) (h_extensions M q (m-n))) rstates))
    in T)"

lemma get_initial_test_suite_H_set_and_finite :
shows  "{(V q)@io@[(x,y)] | q io x y . q \<in> reachable_states M \<and> io \<in> LS M q \<and> length io \<le> m - size_r M \<and> x \<in> inputs M \<and> y \<in> outputs M} \<subseteq> set (get_initial_test_suite_H V M m)"
and "finite_tree (get_initial_test_suite_H V M m)"
proof -

  define rstates where "rstates       = reachable_states_as_list M"
  moreover define n where "n             = size_r M"
  moreover define iM where "iM            = inputs_as_list M"
  moreover define T where "T             = from_list (concat (map (\<lambda>q . map (\<lambda>\<tau>. (V q)@\<tau>) (h_extensions M q (m-n))) rstates))"
  ultimately have res: "get_initial_test_suite_H V M m = T"
    unfolding get_initial_test_suite_H_def Let_def by auto

  define \<X> where \<X>: "\<X> = (\<lambda> q . {io@[(x,y)] | io x y . io \<in> LS M q \<and> length io \<le> m-n \<and> x \<in> inputs M \<and> y \<in> outputs M})"

  have "list.set rstates = reachable_states M"
    unfolding rstates_def reachable_states_as_list_set by simp

  have "{ (V q) @ \<tau> | q \<tau> . q \<in> reachable_states M \<and> \<tau> \<in> \<X> q} \<subseteq> set T"
  proof 
    fix io assume "io \<in> { (V q) @ \<tau> | q \<tau> . q \<in> reachable_states M \<and> \<tau> \<in> \<X> q}"
    then obtain q \<tau> where "io = (V q) @ \<tau>"
                      and "q \<in> reachable_states M"
                      and "\<tau> \<in> \<X> q"
      by blast
    
    have "\<tau> \<in> list.set (h_extensions M q (m - n))"
      using \<open>\<tau> \<in> \<X> q\<close> unfolding \<X>
      using h_extensions_set[OF reachable_state_is_state[OF \<open>q \<in> reachable_states M\<close>]]
      by auto
    then have "io \<in> list.set (map ((@) (V q)) (h_extensions M q (m - n)))"
      unfolding \<open>io = (V q) @ \<tau>\<close> by auto
    moreover have "q \<in> list.set rstates"
      using \<open>list.set rstates = reachable_states M\<close> \<open>q \<in> reachable_states M\<close> by auto
    ultimately have "io \<in> list.set (concat (map (\<lambda>q. map ((@) (V q)) (h_extensions M q (m - n))) rstates))"
      by auto
    then show "io \<in> set T"
      unfolding T_def from_list_set by blast
  qed
  moreover have "{ (V q) @ \<tau> | q \<tau> . q \<in> reachable_states M \<and> \<tau> \<in> \<X> q} = {(V q)@io@[(x,y)] | q io x y . q \<in> reachable_states M \<and> io \<in> LS M q \<and> length io \<le> m - size_r M \<and> x \<in> inputs M \<and> y \<in> outputs M}"
    unfolding \<X> n_def[symmetric] by force
  ultimately show "{(V q)@io@[(x,y)] | q io x y . q \<in> reachable_states M \<and> io \<in> LS M q \<and> length io \<le> m - size_r M \<and> x \<in> inputs M \<and> y \<in> outputs M} \<subseteq> set (get_initial_test_suite_H V M m)"
    unfolding res by simp

  show "finite_tree (get_initial_test_suite_H V M m)"
    unfolding res T_def
    using from_list_finite_tree by auto 
qed



fun complete_inputs_to_tree :: "('a::linorder,'b::linorder,'c::linorder) fsm \<Rightarrow> 'a \<Rightarrow> 'c list \<Rightarrow> 'b list \<Rightarrow> ('b \<times> 'c) prefix_tree" where
  "complete_inputs_to_tree M q ys [] = Prefix_Tree.empty" |
  "complete_inputs_to_tree M q ys (x#xs) = foldl (\<lambda> t y . case h_obs M q x y of None \<Rightarrow> insert t [(x,y)] |
                                                                             Some q' \<Rightarrow> combine_after t [(x,y)] (complete_inputs_to_tree M q' ys xs)) Prefix_Tree.empty ys"

lemma complete_inputs_to_tree_finite_tree :
  "finite_tree (complete_inputs_to_tree M q ys xs)"
proof (induction xs arbitrary: q ys)
  case Nil
  then show ?case using empty_finite_tree by auto
next
  case (Cons x xs)
  
  define ys' where "ys' = ys"
  moreover define f where "f = (\<lambda> t y . case h_obs M q x y of None \<Rightarrow> insert t [(x,y)] | Some q' \<Rightarrow> combine_after t [(x,y)] (complete_inputs_to_tree M q' ys' xs))"
  ultimately have *:"complete_inputs_to_tree M q ys (x # xs) 
              = foldl f Prefix_Tree.empty ys"
    by auto
  moreover have "finite_tree (foldl f Prefix_Tree.empty ys)" 
  proof (induction ys rule: rev_induct)
    case Nil
    then show ?case using empty_finite_tree by auto
  next
    case (snoc y ys)

    define t where "t = foldl (\<lambda> t y . case h_obs M q x y of None \<Rightarrow> insert t [(x,y)] | Some q' \<Rightarrow> combine_after t [(x,y)] (complete_inputs_to_tree M q' ys' xs)) Prefix_Tree.empty ys"
    then have *:"foldl f Prefix_Tree.empty (ys@[y])
                = (case h_obs M q x y of None \<Rightarrow> insert t [(x,y)] | Some q' \<Rightarrow> combine_after t [(x,y)] (complete_inputs_to_tree M q' ys' xs))"
      unfolding f_def by auto

    have "finite_tree t" 
      using snoc unfolding t_def f_def by force

    have "finite_tree (insert t [(x,y)])"
      using \<open>finite_tree t\<close> insert_finite_tree by blast
    moreover have "\<And> q' . finite_tree (combine_after t [(x,y)] (complete_inputs_to_tree M q' ys' xs))"
      using \<open>finite_tree t\<close> \<open>\<And> q ys . finite_tree (complete_inputs_to_tree M q ys xs)\<close> combine_after_finite_tree by blast
    ultimately show ?case 
      unfolding * by auto
  qed
  ultimately show ?case by auto
qed

fun complete_inputs_to_tree_initial :: "('a::linorder,'b::linorder,'c::linorder) fsm \<Rightarrow> 'b list \<Rightarrow> ('b \<times> 'c) prefix_tree" where
  "complete_inputs_to_tree_initial M xs = complete_inputs_to_tree M (initial M) (outputs_as_list M) xs"


definition get_initial_test_suite_H_2 :: "bool \<Rightarrow> ('a,'b,'c) state_cover_assignment \<Rightarrow> 
                                    ('a::linorder,'b::linorder,'c::linorder) fsm \<Rightarrow>                        
                                    nat \<Rightarrow>
                                    ('b\<times>'c) prefix_tree" where
  "get_initial_test_suite_H_2 c V M m = 
    (if c then get_initial_test_suite_H V M m
       else let TS = get_initial_test_suite_H V M m;
                xss = map (map fst) (sorted_list_of_maximal_sequences_in_tree TS);
                ys  = outputs_as_list M
            in 
              foldl (\<lambda> t xs . combine t (complete_inputs_to_tree_initial M xs)) TS xss)" 


lemma get_initial_test_suite_H_2_set_and_finite :
shows  "{(V q)@io@[(x,y)] | q io x y . q \<in> reachable_states M \<and> io \<in> LS M q \<and> length io \<le> m - size_r M \<and> x \<in> inputs M \<and> y \<in> outputs M} \<subseteq> set (get_initial_test_suite_H_2 c V M m)" (is ?P1)
and "finite_tree (get_initial_test_suite_H_2 c V M m)" (is ?P2)
proof -
  have "?P1 \<and> ?P2"
  proof (cases c)
    case True
    then have "get_initial_test_suite_H_2 c V M m = get_initial_test_suite_H V M m"
      unfolding get_initial_test_suite_H_2_def by auto
    then show ?thesis 
      using get_initial_test_suite_H_set_and_finite 
      by fastforce
  next
    case False

    define TS where "TS = get_initial_test_suite_H V M m"
    moreover define xss where "xss = map (map fst) (sorted_list_of_maximal_sequences_in_tree TS)"
    moreover define ys where "ys  = outputs_as_list M"
    ultimately have "get_initial_test_suite_H_2 c V M m = foldl (\<lambda> t xs . combine t (complete_inputs_to_tree M (initial M) ys xs)) TS xss"
      unfolding get_initial_test_suite_H_2_def Let_def using False by auto
    moreover have "set TS \<subseteq> set (foldl (\<lambda> t xs . combine t (complete_inputs_to_tree M (initial M) ys xs)) TS xss)"
      using combine_set by (induction xss rule: rev_induct; auto)
    moreover have "finite_tree (foldl (\<lambda> t xs . combine t (complete_inputs_to_tree M (initial M) ys xs)) TS xss)"
      using complete_inputs_to_tree_finite_tree get_initial_test_suite_H_set_and_finite(2)[of V M m] combine_finite_tree
      unfolding TS_def[symmetric] by (induction xss rule: rev_induct; auto; blast)   
    ultimately show ?thesis 
      using get_initial_test_suite_H_set_and_finite(1)[of V M m] unfolding TS_def[symmetric]
      by force
  qed
  then show ?P1 and ?P2
    by blast+
qed


definition get_pairs_H :: "('a,'b,'c) state_cover_assignment \<Rightarrow> 
                       ('a::linorder,'b::linorder,'c::linorder) fsm \<Rightarrow> 
                       nat \<Rightarrow>
                       ((('b \<times> 'c) list \<times> 'a) \<times> (('b \<times> 'c) list \<times> 'a)) list" 
where
  "get_pairs_H V M m = 
    (let 
      rstates       = reachable_states_as_list M;
      n             = size_r M;
      iM            = inputs_as_list M;
      hMap          = mapping_of (map (\<lambda>(q,x) . ((q,x), map (\<lambda>(y,q') . (q,x,y,q')) (sorted_list_of_set (h M (q,x))))) (List.product (states_as_list M) iM));
      hM            = (\<lambda> q x . case Mapping.lookup hMap (q,x) of Some ts \<Rightarrow> ts | None \<Rightarrow> []);    
      pairs         = pairs_to_distinguish M V (\<lambda>q . paths_up_to_length_with_targets q hM iM ((m-n)+1)) rstates
     in 
      pairs)"


lemma get_pairs_H_set :
  assumes "observable M"
  and     "is_state_cover_assignment M V"
shows
  "\<And> \<alpha> \<beta> . (\<alpha>,\<beta>) \<in> (V ` reachable_states M) \<times> (V ` reachable_states M)
                      \<union> (V ` reachable_states M) \<times> { (V q) @ \<tau> | q \<tau> . q \<in> reachable_states M \<and> \<tau> \<in> {io@[(x,y)] | io x y . io \<in> LS M q \<and> length io \<le> m-size_r M \<and> x \<in> inputs M \<and> y \<in> outputs M}}
                      \<union> (\<Union> q \<in> reachable_states M . \<Union> \<tau> \<in> {io@[(x,y)] | io x y . io \<in> LS M q \<and> length io \<le> m-size_r M \<and> x \<in> inputs M \<and> y \<in> outputs M} . { (V q) @ \<tau>' | \<tau>' . \<tau>' \<in> list.set (prefixes \<tau>)} \<times> {(V q)@\<tau>}) \<Longrightarrow>
                    \<alpha> \<in> L M \<Longrightarrow> \<beta> \<in> L M \<Longrightarrow> after_initial M \<alpha> \<noteq> after_initial M \<beta> \<Longrightarrow>
                    ((\<alpha>,after_initial M \<alpha>),(\<beta>,after_initial M \<beta>)) \<in> list.set (get_pairs_H V M m)"
and "\<And> \<alpha> q' \<beta> q'' . ((\<alpha>,q'),(\<beta>,q'')) \<in> list.set (get_pairs_H V M m) \<Longrightarrow> \<alpha> \<in> L M \<and> \<beta> \<in> L M \<and> after_initial M \<alpha> \<noteq> after_initial M \<beta> \<and> q' = after_initial M \<alpha> \<and> q'' = after_initial M \<beta>"
proof -

  define rstates where "rstates       = reachable_states_as_list M"
  moreover define n where "n             = size_r M"
  moreover define iM where "iM            = inputs_as_list M"
  moreover define hMap' where "hMap'          = mapping_of (map (\<lambda>(q,x) . ((q,x), map (\<lambda>(y,q') . (q,x,y,q')) (sorted_list_of_set (h M (q,x))))) (List.product (states_as_list M) iM))"
  moreover define hM' where "hM'            = (\<lambda> q x . case Mapping.lookup hMap' (q,x) of Some ts \<Rightarrow> ts | None \<Rightarrow> [])"
  ultimately have "get_pairs_H V M m = pairs_to_distinguish M V (\<lambda>q . paths_up_to_length_with_targets q hM' iM ((m-n)+1)) rstates"
    unfolding get_pairs_H_def Let_def by force

  
  define hMap where "hMap          = map_of (map (\<lambda>(q,x) . ((q,x), map (\<lambda>(y,q') . (q,x,y,q')) (sorted_list_of_set (h M (q,x))))) (List.product (states_as_list M) iM))"
  define hM where "hM            = (\<lambda> q x . case hMap (q,x) of Some ts \<Rightarrow> ts | None \<Rightarrow> [])"

  have "distinct (List.product (states_as_list M) iM)"
    using states_as_list_distinct inputs_as_list_distinct distinct_product
    unfolding iM_def 
    by blast
  
  then have "Mapping.lookup hMap' = hMap"
    using mapping_of_map_of
    unfolding hMap_def hMap'_def
    using map_pair_fst_helper[of "\<lambda> q x . map (\<lambda>(y,q') . (q,x,y,q')) (sorted_list_of_set (h M (q,x)))"]
    by (metis (no_types, lifting))
  then have "hM' = hM"
    unfolding hM'_def hM_def
    by meson
  moreover define pairs where "pairs         = pairs_to_distinguish M V (\<lambda>q . paths_up_to_length_with_targets q hM iM ((m-n)+1)) rstates"
  ultimately have res: "get_pairs_H V M m = pairs"
    unfolding \<open>get_pairs_H V M m = pairs_to_distinguish M V (\<lambda>q . paths_up_to_length_with_targets q hM' iM ((m-n)+1)) rstates\<close>
    by force

  
  have *:"list.set rstates = reachable_states M"
    unfolding rstates_def reachable_states_as_list_set by simp

  define \<X>' where \<X>': "\<X>' = (\<lambda>q . paths_up_to_length_with_targets q hM iM ((m-n)+1))"


  have **: "\<And> q p q' . q \<in> reachable_states M \<Longrightarrow> (p,q') \<in> list.set (\<X>' q) \<longleftrightarrow> path M q p \<and> target q p = q' \<and> length p \<le> m-n+1"
  proof -
    fix q p q' assume "q \<in> reachable_states M"

    define qxPairs where qxPairs: "qxPairs = (List.product (states_as_list M) iM)"
    moreover define mapList where mapList: "mapList = (map (\<lambda>(q,x) . ((q,x), map (\<lambda>(y,q') . (q,x,y,q')) (sorted_list_of_set (h M (q,x))))) qxPairs)"
    ultimately have hMap': "hMap = map_of mapList"
      unfolding hMap_def by simp

    have "distinct (states_as_list M)" and "distinct iM"
      unfolding iM_def
      by auto
    then have "distinct qxPairs"
      unfolding qxPairs by (simp add: distinct_product)
    moreover have "(map fst mapList) = qxPairs"
      unfolding mapList by (induction qxPairs; auto)
    ultimately have "distinct (map fst mapList)"
      by auto

    have "\<And> q x . hM q x = map (\<lambda>(y, q'). (q, x, y, q')) (sorted_list_of_set (h M (q, x)))"
    proof -
      fix q x
      show "hM q x = map (\<lambda>(y, q'). (q, x, y, q')) (sorted_list_of_set (h M (q, x)))"
      proof (cases "q \<in> states M \<and> x \<in> inputs M")
        case False
        then have "(h M (q, x)) = {}"
          unfolding h_simps using fsm_transition_source fsm_transition_input by fastforce
        then have "map (\<lambda>(y, q'). (q, x, y, q')) (sorted_list_of_set (h M (q, x))) = []"
          by auto

        have "q \<notin> list.set (states_as_list M) \<or> x \<notin> list.set iM"
          using False unfolding states_as_list_set iM_def inputs_as_list_set by simp
        then have "(q,x) \<notin> list.set qxPairs"
          unfolding qxPairs by auto
        then have "\<nexists> y . ((q,x),y) \<in> list.set mapList"
          unfolding mapList by auto
        then have "hMap (q,x) = None"
          unfolding hMap' using map_of_eq_Some_iff[OF \<open>distinct (map fst mapList)\<close>]
          by (meson option.exhaust)
        then show ?thesis
          using \<open>map (\<lambda>(y, q'). (q, x, y, q')) (sorted_list_of_set (h M (q, x))) = []\<close> 
          unfolding hM_def by auto 
      next
        case True
        then have "q \<in> list.set (states_as_list M) \<and> x \<in> list.set iM"
          unfolding states_as_list_set iM_def inputs_as_list_set by simp
        then have "(q,x) \<in> list.set qxPairs"
          unfolding qxPairs by auto
        then have "((q,x),map (\<lambda>(y, q'). (q, x, y, q')) (sorted_list_of_set (h M (q, x)))) \<in> list.set mapList"
          unfolding mapList by auto
        then have "hMap (q,x) = Some (map (\<lambda>(y, q'). (q, x, y, q')) (sorted_list_of_set (h M (q, x))))"
          unfolding hMap' using map_of_eq_Some_iff[OF \<open>distinct (map fst mapList)\<close>]
          by (meson option.exhaust)
        then show ?thesis 
          unfolding hM_def by auto 
      qed
    qed
    then have hM_alt_def: "hM = (\<lambda> q x . map (\<lambda>(y, q'). (q, x, y, q')) (sorted_list_of_set (h M (q, x))))"
      by auto

    show "(p,q') \<in> list.set (\<X>' q) \<longleftrightarrow> path M q p \<and> target q p = q' \<and> length p \<le> m-n+1"
      unfolding \<X>' hM_alt_def iM_def
                  paths_up_to_length_with_targets_set[OF reachable_state_is_state[OF \<open>q \<in> reachable_states M\<close>]]
      by blast
  qed

  show "\<And> \<alpha> \<beta> . (\<alpha>,\<beta>) \<in> (V ` reachable_states M) \<times> (V ` reachable_states M)
                      \<union> (V ` reachable_states M) \<times> { (V q) @ \<tau> | q \<tau> . q \<in> reachable_states M \<and> \<tau> \<in> {io@[(x,y)] | io x y . io \<in> LS M q \<and> length io \<le> m-size_r M \<and> x \<in> inputs M \<and> y \<in> outputs M}}
                      \<union> (\<Union> q \<in> reachable_states M . \<Union> \<tau> \<in> {io@[(x,y)] | io x y . io \<in> LS M q \<and> length io \<le> m-size_r M \<and> x \<in> inputs M \<and> y \<in> outputs M} . { (V q) @ \<tau>' | \<tau>' . \<tau>' \<in> list.set (prefixes \<tau>)} \<times> {(V q)@\<tau>}) \<Longrightarrow>
                    \<alpha> \<in> L M \<Longrightarrow> \<beta> \<in> L M \<Longrightarrow> after_initial M \<alpha> \<noteq> after_initial M \<beta> \<Longrightarrow>
                    ((\<alpha>,after_initial M \<alpha>),(\<beta>,after_initial M \<beta>)) \<in> list.set (get_pairs_H V M m)"
    using pairs_to_distinguish_containment[OF assms(1,2) * **]
    unfolding res pairs_def \<X>'[symmetric] n_def[symmetric]
    by presburger 





  show "\<And> \<alpha> q' \<beta> q'' . ((\<alpha>,q'),(\<beta>,q'')) \<in> list.set (get_pairs_H V M m) \<Longrightarrow> \<alpha> \<in> L M \<and> \<beta> \<in> L M \<and> after_initial M \<alpha> \<noteq> after_initial M \<beta> \<and> q' = after_initial M \<alpha> \<and> q'' = after_initial M \<beta>"
    using pairs_to_distinguish_elems(3,4,5,6,7)[OF assms(1,2) * **]
    unfolding res pairs_def \<X>'[symmetric] n_def[symmetric]
    by blast
qed



subsection \<open>Functions of the SPYH-Method\<close>

subsubsection \<open>Heuristic Functions for Selecting Traces to Extend\<close>
 
(* results:
    errorValue - (x,y) need not be considered, as it is not in the language of either state
                 or (x,y) reaches the same states again or converges to a single state
    1    - (x,y) immediately distinguishes the states
    else - |(x,y)| + twice the length of the shortest distinguishing trace for the states
*)
fun estimate_growth :: "('a::linorder,'b::linorder,'c::linorder) fsm \<Rightarrow> ('a \<Rightarrow> 'a \<Rightarrow> ('b \<times> 'c) list) \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> 'b \<Rightarrow> 'c \<Rightarrow> nat \<Rightarrow> nat" where
  "estimate_growth M dist_fun q1 q2 x y errorValue= (case h_obs M q1 x y of 
    None \<Rightarrow> (case h_obs M q1 x y of 
      None \<Rightarrow> errorValue | 
      Some q2' \<Rightarrow> 1) |
    Some q1' \<Rightarrow> (case h_obs M q2 x y of
      None \<Rightarrow> 1 |
      Some q2' \<Rightarrow> if q1' = q2' \<or> {q1',q2'} = {q1,q2}
        then errorValue
        else 1 + 2 * (length (dist_fun q1 q2))))"

 
lemma estimate_growth_result :
  assumes "observable M"
  and     "minimal M"
  and     "q1 \<in> states M"
  and     "q2 \<in> states M"
  and     "estimate_growth M dist_fun q1 q2 x y errorValue < errorValue"
shows "\<exists> \<gamma> . distinguishes M q1 q2 ([(x,y)]@\<gamma>)"
proof (cases "h_obs M q1 x y")
  case None
  show ?thesis proof (cases "h_obs M q2 x y")
    case None
    then show ?thesis 
      using \<open>h_obs M q1 x y = None\<close> assms(5) 
      by auto
  next
    case (Some a)
    then have "distinguishes M q1 q2 [(x,y)]"
      using h_obs_distinguishes[OF assms(1) _ None] distinguishes_sym
      by metis
    then show ?thesis 
      by auto
  qed 
next
  case (Some q1')
  show ?thesis proof (cases "h_obs M q2 x y")
    case None
    then have "distinguishes M q1 q2 [(x,y)]"
      using h_obs_distinguishes[OF assms(1) Some]
      by metis
    then show ?thesis 
      by auto
  next
    case (Some q2')
    then have "q1' \<noteq> q2'"
      using \<open>h_obs M q1 x y = Some q1'\<close> assms(5)
      by auto
    then obtain \<gamma> where "distinguishes M q1' q2' \<gamma>"
      using h_obs_state[OF \<open>h_obs M q1 x y = Some q1'\<close>]
      using h_obs_state[OF Some]
      using \<open>minimal M\<close> unfolding minimal.simps distinguishes_def
      by blast
    then have "distinguishes M q1 q2 ([(x,y)]@\<gamma>)"
      using h_obs_language_iff[OF assms(1), of x y \<gamma>]
      using \<open>h_obs M q1 x y = Some q1'\<close> Some
      unfolding distinguishes_def
      by force
    then show ?thesis 
      by blast      
  qed
qed


fun shortest_list_or_default :: "'a list list \<Rightarrow> 'a list \<Rightarrow> 'a list" where
  "shortest_list_or_default xs x = foldl (\<lambda> a b . if length a < length b then a else b) x xs"

lemma shortest_list_or_default_elem :
  "shortest_list_or_default xs x \<in> Set.insert x (list.set xs)"
  by (induction xs rule: rev_induct; auto)

fun shortest_list :: "'a list list \<Rightarrow> 'a list" where
  "shortest_list [] = undefined" |
  "shortest_list (x#xs) = shortest_list_or_default xs x"

lemma shortest_list_elem :
  assumes "xs \<noteq> []"
shows "shortest_list xs \<in> list.set xs"
  using assms shortest_list_or_default_elem
  by (metis list.simps(15) shortest_list.elims) 

fun shortest_list_in_tree_or_default :: "'a list list \<Rightarrow> 'a prefix_tree \<Rightarrow> 'a list \<Rightarrow> 'a list" where
  "shortest_list_in_tree_or_default xs T x = foldl (\<lambda> a b . if isin T a \<and> length a < length b then a else b) x xs"

lemma shortest_list_in_tree_or_default_elem :
  "shortest_list_in_tree_or_default xs T x \<in> Set.insert x (list.set xs)"
  by (induction xs rule: rev_induct; auto)


fun has_leaf :: "('b\<times>'c) prefix_tree \<Rightarrow> 'd \<Rightarrow> ('d \<Rightarrow> ('b\<times>'c) list \<Rightarrow> ('b\<times>'c) list list) \<Rightarrow> ('b\<times>'c) list \<Rightarrow> bool" where
  "has_leaf T G cg_lookup \<alpha> = 
    (find (\<lambda> \<beta> . is_maximal_in T \<beta>) (\<alpha> # cg_lookup G \<alpha>) \<noteq> None)"

fun has_extension :: "('b\<times>'c) prefix_tree \<Rightarrow> 'd \<Rightarrow> ('d \<Rightarrow> ('b\<times>'c) list \<Rightarrow> ('b\<times>'c) list list) \<Rightarrow> ('b\<times>'c) list \<Rightarrow> 'b \<Rightarrow> 'c \<Rightarrow> bool" where
  "has_extension T G cg_lookup \<alpha> x y = 
    (find (\<lambda> \<beta> . isin T (\<beta>@[(x,y)])) (\<alpha> # cg_lookup G \<alpha>) \<noteq> None)"

fun get_extension :: "('b\<times>'c) prefix_tree \<Rightarrow> 'd \<Rightarrow> ('d \<Rightarrow> ('b\<times>'c) list \<Rightarrow> ('b\<times>'c) list list) \<Rightarrow> ('b\<times>'c) list \<Rightarrow> 'b \<Rightarrow> 'c \<Rightarrow> ('b\<times>'c) list option" where
  "get_extension T G cg_lookup \<alpha> x y = 
    (find (\<lambda> \<beta> . isin T (\<beta>@[(x,y)])) (\<alpha> # cg_lookup G \<alpha>))"





(* uses a fixed recursion depth to avoid partiality, as the lookup function of the convergence 
   graph is not constrained here in any way *)
fun get_prefix_of_separating_sequence :: "('a::linorder,'b::linorder,'c::linorder) fsm \<Rightarrow> ('b\<times>'c) prefix_tree \<Rightarrow> 'd \<Rightarrow> ('d \<Rightarrow> ('b\<times>'c) list \<Rightarrow> ('b\<times>'c) list list) \<Rightarrow> ('a \<Rightarrow> 'a \<Rightarrow> ('b\<times>'c) list) \<Rightarrow> ('b\<times>'c) list \<Rightarrow> ('b\<times>'c) list \<Rightarrow> nat \<Rightarrow> (nat \<times> ('b\<times>'c) list)" where
  "get_prefix_of_separating_sequence M T G cg_lookup get_distinguishing_trace u v 0 = (1,[])" |
  "get_prefix_of_separating_sequence M T G cg_lookup get_distinguishing_trace u v (Suc k)= (let
    u' = shortest_list_or_default (cg_lookup G u) u;
    v' = shortest_list_or_default (cg_lookup G v) v;
    su = after_initial M u;
    sv = after_initial M v;
    bestPrefix0 = get_distinguishing_trace su sv;
    minEst0 = length bestPrefix0 + (if (has_leaf T G cg_lookup u') then 0 else length u') + (if (has_leaf T G cg_lookup v') then 0 else length v');
    errorValue = Suc minEst0;
    XY = List.product (inputs_as_list M) (outputs_as_list M);
    tryIO = (\<lambda> (minEst,bestPrefix) (x,y) . 
              if minEst = 0 
                then (minEst,bestPrefix)
                else (case get_extension T G cg_lookup u' x y of
                      Some u'' \<Rightarrow> (case get_extension T G cg_lookup v' x y of
                        Some v'' \<Rightarrow> if (h_obs M su x y = None) \<noteq> (h_obs M sv x y = None)
                          then (0,[])
                          else if h_obs M su x y = h_obs M sv x y
                            then (minEst,bestPrefix)
                            else (let (e,w) = get_prefix_of_separating_sequence M T G cg_lookup get_distinguishing_trace (u''@[(x,y)]) (v''@[(x,y)]) k
                                    in if e = 0
                                      then (0,[])
                                      else if e \<le> minEst
                                        then (e,(x,y)#w)
                                        else (minEst,bestPrefix)) |
                        None \<Rightarrow> (let e = estimate_growth M get_distinguishing_trace su sv x y errorValue;
                                  e' = if e \<noteq> 1
                                        then if has_leaf T G cg_lookup u''
                                          then e + 1
                                          else if \<not>(has_leaf T G cg_lookup (u''@[(x,y)])) 
                                            then e + length u' + 1
                                            else e
                                        else e;
                                  e'' = e' + (if \<not>(has_leaf T G cg_lookup v') then length v' else 0)
                                in if e'' \<le> minEst
                                  then (e'',[(x,y)])
                                  else (minEst,bestPrefix))) |
                      None \<Rightarrow> (case get_extension T G cg_lookup v' x y of
                        Some v'' \<Rightarrow> (let e = estimate_growth M get_distinguishing_trace su sv x y errorValue;
                                  e' = if e \<noteq> 1
                                        then if has_leaf T G cg_lookup v''
                                          then e + 1
                                          else if \<not>(has_leaf T G cg_lookup (v''@[(x,y)]))
                                            then e + length v' + 1
                                            else e
                                        else e;
                                  e'' = e' + (if \<not>(has_leaf T G cg_lookup u') then length u' else 0)
                                in if e'' \<le> minEst
                                  then (e'',[(x,y)])
                                  else (minEst,bestPrefix)) |
                        None \<Rightarrow> (minEst,bestPrefix))))
  in if \<not> isin T u' \<or> \<not> isin T v'
      then (errorValue,[])
      else foldl tryIO (minEst0,[]) XY)"


lemma estimate_growth_Suc :
  assumes "errorValue > 0"
  shows "estimate_growth M get_distinguishing_trace q1 q2 x y errorValue > 0" 
  using assms unfolding estimate_growth.simps 
  by (cases "FSM.h_obs M q1 x y"; cases "FSM.h_obs M q2 x y"; fastforce)

lemma get_extension_result:
  assumes "u \<in> L M1" and "u \<in> L M2"
  and     "convergence_graph_lookup_invar M1 M2 cg_lookup G"
  and     "get_extension T G cg_lookup u x y = Some u'"
shows "converge M1 u u'" and "u' \<in> L M2 \<Longrightarrow> converge M2 u u'" and "u'@[(x,y)] \<in> set T"    
proof -

  have "find (\<lambda> \<beta> . isin T (\<beta>@[(x,y)])) (u # cg_lookup G u) = Some u'"
    using assms(4) 
    by auto
  then have "isin T (u'@[(x,y)])" 
    using find_condition by metis
  then show "u'@[(x,y)] \<in> set T"
    by auto

  have "u' \<in> Set.insert u (list.set (cg_lookup G u))"
    using \<open>find (\<lambda> \<beta> . isin T (\<beta>@[(x,y)])) (u # cg_lookup G u) = Some u'\<close>
    by (metis find_set list.simps(15)) 
  then show "converge M1 u u'" and "u' \<in> L M2 \<Longrightarrow> converge M2 u u'"
    using assms(1,2,3)
    by (metis converge.elims(3) convergence_graph_lookup_invar_def insert_iff)+
qed


lemma get_prefix_of_separating_sequence_result :
  fixes M1 :: "('a::linorder,'b::linorder,'c::linorder) fsm"
  assumes "observable M1"
  and     "observable M2"
  and     "minimal M1"
  and     "u \<in> L M1" and "u \<in> L M2"
  and     "v \<in> L M1" and "v \<in> L M2"
  and     "after_initial M1 u \<noteq> after_initial M1 v"
  and     "\<And> \<alpha> \<beta> q1 q2 . q1 \<in> states M1 \<Longrightarrow> q2 \<in> states M1 \<Longrightarrow> q1 \<noteq> q2 \<Longrightarrow> distinguishes M1 q1 q2 (get_distinguishing_trace q1 q2)"
  and     "convergence_graph_lookup_invar M1 M2 cg_lookup G"  
  and     "L M1 \<inter> set T = L M2 \<inter> set T"
shows "fst (get_prefix_of_separating_sequence M1 T G cg_lookup get_distinguishing_trace u v k) = 0 \<Longrightarrow> \<not> converge M2 u v"
and   "fst (get_prefix_of_separating_sequence M1 T G cg_lookup get_distinguishing_trace u v k) \<noteq> 0 \<Longrightarrow>  \<exists> \<gamma> . distinguishes M1 (after_initial M1 u) (after_initial M1 v) ((snd (get_prefix_of_separating_sequence M1 T G cg_lookup get_distinguishing_trace u v k))@\<gamma>)"
proof -
  have "(fst (get_prefix_of_separating_sequence M1 T G cg_lookup get_distinguishing_trace u v k) = 0 \<longrightarrow> \<not> converge M2 u v)
        \<and> (fst (get_prefix_of_separating_sequence M1 T G cg_lookup get_distinguishing_trace u v k) \<noteq> 0 \<longrightarrow>  (\<exists> \<gamma> . distinguishes M1 (after_initial M1 u) (after_initial M1 v) ((snd (get_prefix_of_separating_sequence M1 T G cg_lookup get_distinguishing_trace u v k))@\<gamma>)))"
    using assms(4,5,6,7,8)
  proof (induction k arbitrary: u v)
    case 0

    then have "\<exists> \<gamma> . distinguishes M1 (after_initial M1 u) (after_initial M1 v) \<gamma>"
      using \<open>minimal M1\<close> unfolding minimal.simps
      by (meson after_is_state assms(1) assms(9)) 
   then show ?case 
     unfolding get_prefix_of_separating_sequence.simps fst_conv snd_conv
     by auto
  next
    case (Suc k)

    define u' where u': "u' = shortest_list_or_default (cg_lookup G u) u"
    define v' where v': "v' = shortest_list_or_default (cg_lookup G v) v"
    define su where su: "su = after_initial M1 u"
    define sv where sv: "sv = after_initial M1 v"
    define bestPrefix0 where bestPrefix0: "bestPrefix0 = get_distinguishing_trace su sv"
    define minEst0 where minEst0: "minEst0 = length bestPrefix0 + (if (has_leaf T G cg_lookup u') then 0 else length u') + (if (has_leaf T G cg_lookup v') then 0 else length v')"
    define errorValue where errorValue: "errorValue = Suc minEst0"
    define XY where XY: "XY = List.product (inputs_as_list M1) (outputs_as_list M1)"
    define tryIO where tryIO: "tryIO = (\<lambda> (minEst,bestPrefix) (x,y) . 
              if minEst = 0 
                then (minEst,bestPrefix)
                else (case get_extension T G cg_lookup u' x y of
                      Some u'' \<Rightarrow> (case get_extension T G cg_lookup v' x y of
                        Some v'' \<Rightarrow> if (h_obs M1 su x y = None) \<noteq> (h_obs M1 sv x y = None)
                          then (0,[])
                          else if h_obs M1 su x y = h_obs M1 sv x y
                            then (minEst,bestPrefix)
                            else (let (e,w) = get_prefix_of_separating_sequence M1 T G cg_lookup get_distinguishing_trace (u''@[(x,y)]) (v''@[(x,y)]) k
                                    in if e = 0
                                      then (0,[])
                                      else if e \<le> minEst
                                        then (e,(x,y)#w)
                                        else (minEst,bestPrefix)) |
                        None \<Rightarrow> (let e = estimate_growth M1 get_distinguishing_trace su sv x y errorValue;
                                  e' = if e \<noteq> 1
                                        then if has_leaf T G cg_lookup u''
                                          then e + 1
                                          else if \<not>(has_leaf T G cg_lookup (u''@[(x,y)])) 
                                            then e + length u' + 1
                                            else e
                                        else e;
                                  e'' = e' + (if \<not>(has_leaf T G cg_lookup v') then length v' else 0)
                                in if e'' \<le> minEst
                                  then (e'',[(x,y)])
                                  else (minEst,bestPrefix))) |
                      None \<Rightarrow> (case get_extension T G cg_lookup v' x y of
                        Some v'' \<Rightarrow> (let e = estimate_growth M1 get_distinguishing_trace su sv x y errorValue;
                                  e' = if e \<noteq> 1
                                        then if has_leaf T G cg_lookup v''
                                          then e + 1
                                          else if \<not>(has_leaf T G cg_lookup (v''@[(x,y)]))
                                            then e + length v' + 1
                                            else e
                                        else e;
                                  e'' = e' + (if \<not>(has_leaf T G cg_lookup u') then length u' else 0)
                                in if e'' \<le> minEst
                                  then (e'',[(x,y)])
                                  else (minEst,bestPrefix)) |
                        None \<Rightarrow> (minEst,bestPrefix))))"


    have res': "(get_prefix_of_separating_sequence M1 T G cg_lookup get_distinguishing_trace u v (Suc k)) = 
                  (if \<not> isin T u' \<or> \<not> isin T v' then (errorValue,[]) else foldl tryIO (minEst0,[]) XY)"
      unfolding tryIO XY errorValue minEst0 bestPrefix0 sv su v' u'
      unfolding get_prefix_of_separating_sequence.simps Let_def
      by force


    show ?case proof (cases "\<not> isin T u' \<or> \<not> isin T v'")
      case True
      then have *:"(get_prefix_of_separating_sequence M1 T G cg_lookup get_distinguishing_trace u v (Suc k)) = (errorValue,[])"
        using res' by auto
      
      show ?thesis
        unfolding * fst_conv snd_conv errorValue
        by (metis Suc.prems(1,3,5) Zero_not_Suc after_is_state append_Nil assms(1) assms(9))
    next
      case False

      then have res: "(get_prefix_of_separating_sequence M1 T G cg_lookup get_distinguishing_trace u v (Suc k)) = foldl tryIO (minEst0,[]) XY"
        using res' by auto

      
      have "converge M1 u u'" and "converge M2 u u'"
        unfolding u' 
        using shortest_list_or_default_elem[of "cg_lookup G u" u] assms(10) Suc.prems(1,2,3)
        by (metis converge.elims(3) convergence_graph_lookup_invar_def insertE)+

      have "converge M1 v v'" and "converge M2 v v'"
        unfolding v' 
        using shortest_list_or_default_elem[of "cg_lookup G v" v] assms(10) Suc.prems
        by (metis converge.elims(3) convergence_graph_lookup_invar_def insertE)+
  
      have "su \<in> states M1"
        unfolding su
        using after_is_state[OF assms(1) Suc.prems(1)] .
  
      have "sv \<in> states M1"
        unfolding sv
        using after_is_state[OF assms(1) Suc.prems(3)] .
  
      define P where P: "P = (\<lambda> (ew :: (nat \<times> ('b \<times> 'c) list)) . 
                                      (fst ew = 0 \<longrightarrow> \<not> converge M2 u v)
                                      \<and> (fst ew \<noteq> 0 \<longrightarrow>  (\<exists> \<gamma> . distinguishes M1 (after_initial M1 u) (after_initial M1 v) ((snd ew)@\<gamma>))))"
  
      have "P (minEst0,[])"
      proof -
        have "distinguishes M1 (after_initial M1 u) (after_initial M1 v) bestPrefix0"
          using assms(9)[of su sv]
          using \<open>su \<in> states M1\<close> \<open>sv \<in> states M1\<close>
          using Suc.prems(5) 
          unfolding bestPrefix0 su sv
          by blast
        
        moreover have "minEst0 \<noteq> 0"
          unfolding minEst0
          using calculation distinguishes_not_Nil[OF _ after_is_state[OF assms(1) Suc.prems(1)] after_is_state[OF assms(1) Suc.prems(3)]]
          by auto
        ultimately show ?thesis
          unfolding P fst_conv snd_conv
          by (metis append.left_neutral) 
      qed
  
      have "errorValue > 0"
        unfolding errorValue by auto
  
      have "\<And> x y e w . e < errorValue \<Longrightarrow> P (e,w) \<Longrightarrow> P (tryIO (e,w) (x,y)) \<and> fst (tryIO (e,w) (x,y)) \<le> e" 
      proof -
        fix x y e w
        assume "e < errorValue" and "P (e,w)"
  
        have *:"\<And> x y a b f . (case (x, y) of (x, y) \<Rightarrow> (\<lambda>(a, b). f x y a b)) (a,b)  = f x y a b"
          by auto
  
        
        show "P (tryIO (e,w) (x,y)) \<and> fst (tryIO (e,w) (x,y)) \<le> e"
        proof (cases "e = 0")
          case True
          then have "tryIO (e,w) (x,y) = (e,w)"
            unfolding P tryIO fst_conv snd_conv case_prod_conv 
            by auto
          then show ?thesis 
            using \<open>P (e,w)\<close>
            by auto
        next
          case False
          show ?thesis 
          proof (cases "get_extension T G cg_lookup u' x y")
            case None
            
            show ?thesis 
            proof (cases "get_extension T G cg_lookup v' x y")
              case None
              then have "tryIO (e,w) (x,y) = (e,w)"
                using \<open>get_extension T G cg_lookup u' x y = None\<close>
                unfolding tryIO by auto
              then show ?thesis 
                using \<open>P (e,w)\<close>
                by auto
            next
              case (Some v'')
    
              define c where c: "c = estimate_growth M1 get_distinguishing_trace su sv x y errorValue"
              define c' where c': "c' = (if c \<noteq> 1 then if has_leaf T G cg_lookup v'' then c + 1 else if \<not>(has_leaf T G cg_lookup (v''@[(x,y)])) then c + length v' + 1 else c else c)"
              define c'' where c'': "c'' = c' + (if \<not>(has_leaf T G cg_lookup u') then length u' else 0)"
    
              have "tryIO (e,w) (x,y) = (if c'' \<le> e then (c'',[(x,y)]) else (e,w))"
                unfolding c c' c'' tryIO Let_def
                using None Some False
                by auto
    
              show ?thesis proof (cases "c'' \<le> e")
                case True
                then have "c'' < errorValue"
                  using \<open>e < errorValue\<close> by auto
                then have "c' < errorValue"
                  unfolding c'' by auto
                then have "estimate_growth M1 get_distinguishing_trace su sv x y errorValue < errorValue"
                  unfolding c' c
                  using add_lessD1 by presburger
    
                have "c > 0"
                  using estimate_growth_Suc[OF \<open>errorValue > 0\<close>] unfolding c
                  by blast 
                then have "c'' > 0"
                  unfolding c' c''
                  using add_gr_0 by presburger 
                then have "c'' \<noteq> 0"
                  by auto
                then have "P (c'',[(x,y)])"
                  using True estimate_growth_result[OF assms(1,3) \<open>su \<in> states M1\<close> \<open>sv \<in> states M1\<close> \<open>estimate_growth M1 get_distinguishing_trace su sv x y errorValue < errorValue\<close>]
                  unfolding P fst_conv su sv snd_conv 
                  by blast
                then show ?thesis 
                  using \<open>tryIO (e,w) (x,y) = (if c'' \<le> e then (c'',[(x,y)]) else (e,w))\<close> True
                  by auto
              next
                case False
                then show ?thesis 
                  using \<open>tryIO (e,w) (x,y) = (if c'' \<le> e then (c'',[(x,y)]) else (e,w))\<close> \<open>P (e,w)\<close>
                  by auto
              qed
            qed
          next
            case (Some u'')
            
            show ?thesis proof (cases "get_extension T G cg_lookup v' x y")
              case None
    
              define c where c: "c = estimate_growth M1 get_distinguishing_trace su sv x y errorValue"
              define c' where c': "c' = (if c \<noteq> 1 then if has_leaf T G cg_lookup u'' then c + 1 else if \<not>(has_leaf T G cg_lookup (u''@[(x,y)])) then c + length u' + 1 else c else c)"
              define c'' where c'': "c'' = c' + (if \<not>(has_leaf T G cg_lookup v') then length v' else 0)"
    
              have "tryIO (e,w) (x,y) = (if c'' \<le> e then (c'',[(x,y)]) else (e,w))"
                unfolding c c' c'' tryIO Let_def
                using None Some False
                by auto
    
              show ?thesis proof (cases "c'' \<le> e")
                case True
                then have "c'' < errorValue"
                  using \<open>e < errorValue\<close> by auto
                then have "c' < errorValue"
                  unfolding c'' by auto
                then have "estimate_growth M1 get_distinguishing_trace su sv x y errorValue < errorValue"
                  unfolding c' c
                  using add_lessD1 by presburger
    
                have "c > 0"
                  using estimate_growth_Suc[OF \<open>errorValue > 0\<close>] unfolding c
                  by blast 
                then have "c'' > 0"
                  unfolding c' c''
                  using add_gr_0 by presburger 
                then have "c'' \<noteq> 0"
                  by auto
                then have "P (c'',[(x,y)])"
                  using True estimate_growth_result[OF assms(1,3) \<open>su \<in> states M1\<close> \<open>sv \<in> states M1\<close> \<open>estimate_growth M1 get_distinguishing_trace su sv x y errorValue < errorValue\<close>]
                  unfolding P fst_conv su sv snd_conv 
                  by blast
                then show ?thesis 
                  using \<open>tryIO (e,w) (x,y) = (if c'' \<le> e then (c'',[(x,y)]) else (e,w))\<close> True
                  by auto
              next
                case False
                then show ?thesis 
                  using \<open>tryIO (e,w) (x,y) = (if c'' \<le> e then (c'',[(x,y)]) else (e,w))\<close> \<open>P (e,w)\<close>
                  by auto
              qed
    
    
            next
              case (Some v'')
  
              have "u' \<in> L M1"
                using \<open>converge M1 u u'\<close> converge.simps by blast 
              have "v' \<in> L M1"
                using \<open>converge M1 v v'\<close> converge.simps by blast 
              have "u' \<in> L M2"
                using \<open>converge M2 u u'\<close> converge.simps by blast 
              have "v' \<in> L M2"
                using \<open>converge M2 v v'\<close> converge.simps by blast 
                
  
              have "converge M1 u' u''" and "u'' @ [(x, y)] \<in> set T"
                using get_extension_result(1,3)[OF \<open>u' \<in> L M1\<close> \<open>u' \<in> L M2\<close> assms(10) \<open>get_extension T G cg_lookup u' x y = Some u''\<close>]
                by blast+
              then have "converge M1 u u''"
                using \<open>converge M1 u u'\<close> by auto
              then have "u'' \<in> set T \<inter> L M1"
                using set_prefix[OF \<open>u'' @ [(x, y)] \<in> set T\<close>] by auto
  
              have "converge M1 v' v''" and "v'' @ [(x, y)] \<in> set T"
                using get_extension_result[OF \<open>v' \<in> L M1\<close> \<open>v' \<in> L M2\<close> assms(10) \<open>get_extension T G cg_lookup v' x y = Some v''\<close>]
                by blast+
              then have "converge M1 v v''"
                using \<open>converge M1 v v'\<close> by auto
              then have "v'' \<in> set T \<inter> L M1"
                using set_prefix[OF \<open>v'' @ [(x, y)] \<in> set T\<close>] by auto
    
              show ?thesis proof (cases "(h_obs M1 su x y = None) \<noteq> (h_obs M1 sv x y = None)")
                case True
    
                then have "tryIO (e,w) (x,y) = (0,[])"
                  using Some \<open>get_extension T G cg_lookup u' x y = Some u''\<close> False
                  unfolding tryIO Let_def by auto
    
                have "\<not> converge M2 u v"
                proof -
                  note \<open>L M1 \<inter> set T = L M2 \<inter> set T\<close>
  
                  then have "u' \<in> L M2" and "v' \<in> L M2"
                    using False \<open>u' \<in> L M1\<close> \<open>v' \<in> L M1\<close> \<open>\<not> (\<not> isin T u' \<or> \<not> isin T v')\<close>
                    by auto
  
                  have "u'' \<in> L M2"
                    using \<open>L M1 \<inter> set T = L M2 \<inter> set T\<close> \<open>u'' \<in> set T \<inter> L M1\<close>
                    by blast
                  then have "converge M2 u' u''"
                    using get_extension_result(2)[OF \<open>u' \<in> L M1\<close> \<open>u' \<in> L M2\<close> assms(10) \<open>get_extension T G cg_lookup u' x y = Some u''\<close>] 
                    by blast                
                  moreover note \<open>converge M2 u u'\<close>
                  ultimately have "converge M2 u u''"
                    by auto
                    
                  have "v'' \<in> L M2"
                    using \<open>L M1 \<inter> set T = L M2 \<inter> set T\<close> \<open>v'' \<in> set T \<inter> L M1\<close>
                    by blast
                  then have "converge M2 v' v''"
                    using get_extension_result(2)[OF \<open>v' \<in> L M1\<close> \<open>v' \<in> L M2\<close> assms(10) \<open>get_extension T G cg_lookup v' x y = Some v''\<close>] 
                    by blast
                  moreover note \<open>converge M2 v v'\<close>
                  ultimately have "converge M2 v v''"
                    by auto
  
                  have "distinguishes M1 su sv ([(x,y)])"
                    using h_obs_distinguishes[OF assms(1), of su x y _ sv] 
                    using distinguishes_sym[OF h_obs_distinguishes[OF assms(1), of sv x y _ su]]
                    using True 
                    by (cases "h_obs M1 su x y"; cases "h_obs M1 sv x y"; metis)
                  then have "distinguishes M1 (after_initial M1 u) (after_initial M1 v) ([(x,y)])"
                    unfolding su sv by auto
  
                  show "\<not> converge M2 u v"
                    using distinguish_converge_diverge[OF assms(1-3) _ _ \<open>converge M1 u u''\<close> \<open>converge M1 v v''\<close> \<open>converge M2 u u''\<close> \<open>converge M2 v v''\<close> \<open>distinguishes M1 (after_initial M1 u) (after_initial M1 v) ([(x,y)])\<close> \<open>u'' @ [(x, y)] \<in> set T\<close> \<open>v'' @ [(x, y)] \<in> set T\<close> \<open>L M1 \<inter> set T = L M2 \<inter> set T\<close>]
                          \<open>u'' \<in> set T \<inter> L M1\<close> \<open>v'' \<in> set T \<inter> L M1\<close>
                    by blast
                qed
                then show ?thesis
                  unfolding P \<open>tryIO (e,w) (x,y) = (0,[])\<close> fst_conv snd_conv su sv
                  by blast
  
              next
                case False
    
                show ?thesis proof (cases "h_obs M1 su x y = h_obs M1 sv x y")
                  case True
    
                  then have "tryIO (e,w) (x,y) = (e,w)"
                    using \<open>get_extension T G cg_lookup u' x y = Some u''\<close> Some
                    unfolding tryIO by auto
                  then show ?thesis 
                    using \<open>P (e,w)\<close>
                    by auto
                next
                  case False 
    
                  then have "h_obs M1 su x y \<noteq> None" and "h_obs M1 sv x y \<noteq> None"
                    using \<open>\<not> (h_obs M1 su x y = None) \<noteq> (h_obs M1 sv x y = None)\<close> 
                    by metis+
    
                  have "u''@[(x,y)] \<in> L M1"
                    by (metis \<open>converge M1 u u''\<close> \<open>h_obs M1 su x y \<noteq> None\<close> after_language_iff assms(1) converge.elims(2) h_obs_language_single_transition_iff su) 
                  have "v''@[(x,y)] \<in> L M1"
                    by (metis \<open>converge M1 v v''\<close> \<open>h_obs M1 sv x y \<noteq> None\<close> after_language_iff assms(1) converge.elims(2) h_obs_language_single_transition_iff sv) 

                  have "u''@[(x,y)] \<in> L M2"
                    using \<open>u''@[(x,y)] \<in> L M1\<close> \<open>u''@[(x,y)] \<in> set T\<close> \<open>L M1 \<inter> set T = L M2 \<inter> set T\<close>
                    by blast
                  have "v''@[(x,y)] \<in> L M2"
                    using \<open>v''@[(x,y)] \<in> L M1\<close> \<open>v''@[(x,y)] \<in> set T\<close> \<open>L M1 \<inter> set T = L M2 \<inter> set T\<close>
                    by blast

                  have "FSM.after M1 (FSM.initial M1) (u'' @ [(x, y)]) \<noteq> FSM.after M1 (FSM.initial M1) (v'' @ [(x, y)])"
                    using False \<open>converge M1 u u''\<close> \<open>converge M1 v v''\<close> unfolding su sv
                  proof - (* auto-generated proof *)
                    assume a1: "h_obs M1 (FSM.after M1 (FSM.initial M1) u) x y \<noteq> h_obs M1 (FSM.after M1 (FSM.initial M1) v) x y"
                    have f2: "\<forall>f ps psa. converge (f::('a, 'b, 'c) fsm) ps psa = (ps \<in> L f \<and> psa \<in> L f \<and> LS f (FSM.after f (FSM.initial f) ps) = LS f (FSM.after f (FSM.initial f) psa))"
                      by (meson converge.simps)
                    then have f3: "u \<in> L M1 \<and> u'' \<in> L M1 \<and> LS M1 (FSM.after M1 (FSM.initial M1) u) = LS M1 (FSM.after M1 (FSM.initial M1) u'')"
                      using \<open>converge M1 u u''\<close> by presburger
                    have f4: "\<forall>f ps psa. \<not> minimal (f::('a, 'b, 'c) fsm) \<or> \<not> observable f \<or> ps \<notin> L f \<or> psa \<notin> L f \<or> converge f ps psa = (FSM.after f (FSM.initial f) ps = FSM.after f (FSM.initial f) psa)"
                      using convergence_minimal by blast
                    have f5: "v \<in> L M1 \<and> v'' \<in> L M1 \<and> LS M1 (FSM.after M1 (FSM.initial M1) v) = LS M1 (FSM.after M1 (FSM.initial M1) v'')"
                      using f2 \<open>converge M1 v v''\<close> by blast
                    then have f6: "FSM.after M1 (FSM.initial M1) v = FSM.after M1 (FSM.initial M1) v''"
                      using f4 \<open>converge M1 v v''\<close> assms(1) assms(3) by blast
                    have "FSM.after M1 (FSM.initial M1) u = FSM.after M1 (FSM.initial M1) u''"
                      using f4 f3 \<open>converge M1 u u''\<close> assms(1) assms(3) by blast
                    then show ?thesis
                      using f6 f5 f3 a1 by (metis (no_types) \<open>u'' @ [(x, y)] \<in> L M1\<close> \<open>v'' @ [(x, y)] \<in> L M1\<close> after_h_obs after_language_iff after_split assms(1) h_obs_from_LS)
                  qed
    
                  obtain e' w' where "get_prefix_of_separating_sequence M1 T G cg_lookup get_distinguishing_trace (u''@[(x,y)]) (v''@[(x,y)]) k = (e',w')"
                    using prod.exhaust by metis
    
                  then have "tryIO (e,w) (x,y) = (if e' = 0 then (0,[]) else if e' \<le> e then (e',(x,y)#w') else (e,w))"
                    using \<open>get_extension T G cg_lookup u' x y = Some u''\<close> Some False \<open>\<not> (h_obs M1 su x y = None) \<noteq> (h_obs M1 sv x y = None)\<close> \<open>e \<noteq> 0\<close>
                    unfolding tryIO Let_def by auto
    
    
                  show ?thesis proof (cases "e' = 0")
                    case True
    
                    have "\<not> converge M2 u v"
                    proof -
                      note \<open>L M1 \<inter> set T = L M2 \<inter> set T\<close>
                      then have "u' \<in> L M2" and "v' \<in> L M2"
                        using \<open>\<not> (\<not> isin T u' \<or> \<not> isin T v')\<close> \<open>u' \<in> L M1\<close> \<open>v' \<in> L M1\<close>
                        by auto
      
                      have "u'' \<in> L M2"
                        using \<open>L M1 \<inter> set T = L M2 \<inter> set T\<close> \<open>u'' \<in> set T \<inter> L M1\<close>
                        by blast
                      then have "converge M2 u' u''"
                        using get_extension_result(2)[OF \<open>u' \<in> L M1\<close> \<open>u' \<in> L M2\<close> assms(10) \<open>get_extension T G cg_lookup u' x y = Some u''\<close>] 
                        by blast                
                      moreover note \<open>converge M2 u u'\<close>
                      ultimately have "converge M2 u u''"
                        by auto
                      
                      have "v'' \<in> L M2"
                        using \<open>L M1 \<inter> set T = L M2 \<inter> set T\<close> \<open>v'' \<in> set T \<inter> L M1\<close>
                        by blast
                      then have "converge M2 v' v''"
                        using get_extension_result(2)[OF \<open>v' \<in> L M1\<close> \<open>v' \<in> L M2\<close> assms(10) \<open>get_extension T G cg_lookup v' x y = Some v''\<close>] 
                        by blast
                      moreover note \<open>converge M2 v v'\<close>
                      ultimately have "converge M2 v v''"
                        by auto
    
                      have "fst (get_prefix_of_separating_sequence M1 T G cg_lookup get_distinguishing_trace (u'' @ [(x, y)]) (v'' @ [(x, y)]) k) = 0"
                        using True \<open>get_prefix_of_separating_sequence M1 T G cg_lookup get_distinguishing_trace (u''@[(x,y)]) (v''@[(x,y)]) k = (e',w')\<close>
                        by auto
                      then have "\<not> converge M2 (u'' @ [(x, y)]) (v'' @ [(x, y)])"
                        using Suc.IH[OF \<open>u''@[(x,y)] \<in> L M1\<close> \<open>u''@[(x,y)] \<in> L M2\<close> \<open>v''@[(x,y)] \<in> L M1\<close> \<open>v''@[(x,y)] \<in> L M2\<close> \<open>FSM.after M1 (FSM.initial M1) (u'' @ [(x, y)]) \<noteq> FSM.after M1 (FSM.initial M1) (v'' @ [(x, y)])\<close>]
                        using \<open>L M1 \<inter> Prefix_Tree.set T = L M2 \<inter> Prefix_Tree.set T\<close>
                        by blast
                      then have "\<not> converge M2 u'' v''"
                        using diverge_prefix[OF assms(2) \<open>u''@[(x,y)] \<in> L M2\<close> \<open>v''@[(x,y)] \<in> L M2\<close>]
                        by blast
                      then show "\<not> converge M2 u v"
                        using \<open>converge M2 u u''\<close> \<open>converge M2 v v''\<close>
                        by fastforce
                    qed
                    then show ?thesis
                      unfolding P \<open>tryIO (e,w) (x,y) = (if e' = 0 then (0,[]) else if e' \<le> e then (e',(x,y)#w') else (e,w))\<close> True fst_conv snd_conv su sv
                      by simp
                  next
                    case False

                    show ?thesis proof (cases "e' \<le> e")
                      case True
                      then have "fst (get_prefix_of_separating_sequence M1 T G cg_lookup get_distinguishing_trace (u'' @ [(x, y)]) (v'' @ [(x, y)]) k) \<noteq> 0"
                        using \<open>get_prefix_of_separating_sequence M1 T G cg_lookup get_distinguishing_trace (u''@[(x,y)]) (v''@[(x,y)]) k = (e',w')\<close> False
                        by auto
                      then have "(\<exists>\<gamma>. distinguishes M1 (FSM.after M1 (FSM.initial M1) (u'' @ [(x, y)])) (FSM.after M1 (FSM.initial M1) (v'' @ [(x, y)]))
                                     (snd (get_prefix_of_separating_sequence M1 T G cg_lookup get_distinguishing_trace (u'' @ [(x, y)]) (v'' @ [(x, y)]) k) @ \<gamma>))"
                        using Suc.IH[OF \<open>u''@[(x,y)] \<in> L M1\<close> \<open>u''@[(x,y)] \<in> L M2\<close> \<open>v''@[(x,y)] \<in> L M1\<close> \<open>v''@[(x,y)] \<in> L M2\<close> \<open>FSM.after M1 (FSM.initial M1) (u'' @ [(x, y)]) \<noteq> FSM.after M1 (FSM.initial M1) (v'' @ [(x, y)])\<close>]
                        by blast
                      then obtain \<gamma> where "distinguishes M1 (FSM.after M1 (FSM.initial M1) (u'' @ [(x, y)])) (FSM.after M1 (FSM.initial M1) (v'' @ [(x, y)])) (w'@\<gamma>)"
                        unfolding \<open>get_prefix_of_separating_sequence M1 T G cg_lookup get_distinguishing_trace (u''@[(x,y)]) (v''@[(x,y)]) k = (e',w')\<close>  snd_conv
                        by blast
                      have "distinguishes M1 (after_initial M1 u'') (after_initial M1 v'')  ((x,y)#(w'@\<gamma>))"
                        using distinguishes_after_initial_prepend[OF assms(1) language_prefix[OF \<open>u''@[(x,y)] \<in> L M1\<close>] language_prefix[OF \<open>v''@[(x,y)] \<in> L M1\<close>]]
                        by (metis Suc.prems(1) Suc.prems(3) \<open>converge M1 u u'\<close> \<open>converge M1 u' u''\<close> \<open>converge M1 v v''\<close> \<open>distinguishes M1 (after_initial M1 (u'' @ [(x, y)])) (after_initial M1 (v'' @ [(x, y)])) (w' @ \<gamma>)\<close> \<open>h_obs M1 su x y \<noteq> None\<close> \<open>h_obs M1 sv x y \<noteq> None\<close> \<open>u' \<in> L M1\<close> \<open>u'' @ [(x, y)] \<in> L M1\<close> \<open>v'' @ [(x, y)] \<in> L M1\<close> assms(1) assms(3) convergence_minimal language_prefix su sv)                    
                      then have "distinguishes M1 (after_initial M1 u) (after_initial M1 v)  (((x,y)#w')@\<gamma>)"
                        by (metis Cons_eq_appendI Suc.prems(1) Suc.prems(3) \<open>converge M1 u u''\<close> \<open>converge M1 v v''\<close> \<open>u'' @ [(x, y)] \<in> L M1\<close> \<open>v'' @ [(x, y)] \<in> L M1\<close> assms(1) assms(3) convergence_minimal language_prefix)
    
                      have "tryIO (e,w) (x,y) = (e',(x,y)#w')"
                        using \<open>tryIO (e,w) (x,y) = (if e' = 0 then (0,[]) else if e' \<le> e then (e',(x,y)#w') else (e,w))\<close> True False
                        by auto
                      
                      show ?thesis
                      unfolding P \<open>tryIO (e,w) (x,y) = (e',(x,y)#w')\<close> fst_conv snd_conv
                        using \<open>distinguishes M1 (after_initial M1 u) (after_initial M1 v) (((x,y)#w')@\<gamma>)\<close>
                              False True
                      by blast
                    next
                      case False
    
                      then have "tryIO (e,w) (x,y) = (e,w)"
                        using \<open>e' \<noteq> 0\<close> \<open>tryIO (e,w) (x,y) = (if e' = 0 then (0,[]) else if e' \<le> e then (e',(x,y)#w') else (e,w))\<close>
                        by auto
                      then show ?thesis 
                        using \<open>P (e,w)\<close>
                        by auto
                    qed
                  qed
                qed
              qed
            qed
          qed
        qed
      qed
  
      have "minEst0 < errorValue"
        unfolding errorValue by auto
  
      have "P (foldl tryIO (minEst0,[]) XY) \<and> fst (foldl tryIO (minEst0,[]) XY) \<le> minEst0"
      proof (induction XY rule: rev_induct)
        case Nil
        then show ?case 
          using \<open>P (minEst0,[])\<close>
          by auto
      next
        case (snoc a XY)
        
        obtain x y where "a = (x,y)"
          using prod.exhaust by metis
        moreover obtain e w where "(foldl tryIO (minEst0,[]) XY) = (e,w)"
          using prod.exhaust by metis
        ultimately have "(foldl tryIO (minEst0, []) (XY@[a])) = tryIO (e,w) (x,y)"
          by auto
  
        have "P (e,w)" and "e \<le> minEst0" and "e < errorValue"
          using snoc.IH \<open>minEst0 < errorValue\<close>
          unfolding \<open>(foldl tryIO (minEst0,[]) XY) = (e,w)\<close> 
          by auto
        
        then show ?case
          unfolding \<open>(foldl tryIO (minEst0, []) (XY@[a])) = tryIO (e,w) (x,y)\<close>
          using \<open>\<And> x y e w . e < errorValue \<Longrightarrow> P (e,w) \<Longrightarrow> P (tryIO (e,w) (x,y)) \<and> fst (tryIO (e,w) (x,y)) \<le> e\<close>
          using dual_order.trans by blast
      qed
  
      then have "P (get_prefix_of_separating_sequence M1 T G cg_lookup get_distinguishing_trace u v (Suc k))"
        unfolding res by blast
      then show ?thesis
        unfolding P by blast
    qed
  qed

  then show "fst (get_prefix_of_separating_sequence M1 T G cg_lookup get_distinguishing_trace u v k) = 0 \<Longrightarrow> \<not> converge M2 u v"
       and  "fst (get_prefix_of_separating_sequence M1 T G cg_lookup get_distinguishing_trace u v k) \<noteq> 0 \<Longrightarrow>  \<exists> \<gamma> . distinguishes M1 (after_initial M1 u) (after_initial M1 v) ((snd (get_prefix_of_separating_sequence M1 T G cg_lookup get_distinguishing_trace u v k))@\<gamma>)"
    by blast+
qed



subsubsection \<open>Distributing Convergent Traces\<close>

fun append_heuristic_io :: "('b\<times>'c) prefix_tree \<Rightarrow> ('b\<times>'c) list \<Rightarrow> (('b\<times>'c) list \<times> int) \<Rightarrow> ('b\<times>'c) list \<Rightarrow> (('b\<times>'c) list \<times> int)" where
  "append_heuristic_io T w (uBest,lBest) u' = (let t' = after T u';
                                        w' = maximum_prefix t' w
                                    in if w' = w
                                        then (u',0::int)
                                        else if (is_maximal_in t' w' \<and> (int (length w') > lBest \<or> (int (length w') = lBest \<and> length u' < length uBest)))
                                          then (u', int (length w'))
                                          else (uBest,lBest))"
  

lemma append_heuristic_io_in :
  "fst (append_heuristic_io T w (uBest,lBest) u') \<in> {u',uBest}"
  unfolding append_heuristic_io.simps Let_def by auto


fun append_heuristic_input :: "('a::linorder,'b::linorder,'c::linorder) fsm \<Rightarrow> ('b\<times>'c) prefix_tree \<Rightarrow> ('b\<times>'c) list \<Rightarrow> (('b\<times>'c) list \<times> int) \<Rightarrow> ('b\<times>'c) list \<Rightarrow> (('b\<times>'c) list \<times> int)" where
"append_heuristic_input M T w (uBest,lBest) u' = (let t' = after T u';
                                       ws = maximum_fst_prefixes t' (map fst w) (outputs_as_list M)
                                    in
                                      foldr (\<lambda> w' (uBest',lBest'::int) .
                                                if w' = w
                                                  then (u',0::int)
                                                  else if (int (length w') > lBest' \<or> (int (length w') = lBest' \<and> length u' < length uBest'))
                                                    then (u',int (length w'))
                                                    else (uBest',lBest'))
                                            ws (uBest,lBest))"

lemma append_heuristic_input_in :
  "fst (append_heuristic_input M T w (uBest,lBest) u') \<in> {u',uBest}"
proof -
  define ws where ws: "ws = maximum_fst_prefixes (after T u') (map fst w) (outputs_as_list M)"
  define f where f: "f = (\<lambda> w' (uBest',lBest'::int) .
                                                if w' = w
                                                  then (u',0::int)
                                                  else if (int (length w') > lBest' \<or> (int (length w') = lBest' \<and> length u' < length uBest'))
                                                    then (u',int (length w'))
                                                    else (uBest',lBest'))"

  have "\<And> w' b' . fst b' \<in> {u',uBest} \<Longrightarrow> fst (f w' b') \<in> {u',uBest}"
    unfolding f by auto
  then have "fst (foldr f ws (uBest,lBest)) \<in> {u',uBest}"
    by (induction ws; auto)
  moreover have "append_heuristic_input M T w (uBest,lBest) u' = foldr f ws (uBest,lBest)"
    unfolding append_heuristic_input.simps Let_def ws f by force
  ultimately show ?thesis
    by simp
qed

fun distribute_extension :: "('a::linorder,'b::linorder,'c::linorder) fsm \<Rightarrow> ('b\<times>'c) prefix_tree \<Rightarrow> 'd \<Rightarrow> ('d \<Rightarrow> ('b\<times>'c) list \<Rightarrow> ('b\<times>'c) list list) \<Rightarrow> ('d \<Rightarrow> ('b\<times>'c) list \<Rightarrow> 'd) \<Rightarrow>('b\<times>'c) list \<Rightarrow> ('b\<times>'c) list \<Rightarrow> bool \<Rightarrow> (('b\<times>'c) prefix_tree \<Rightarrow> ('b\<times>'c) list \<Rightarrow> (('b\<times>'c) list \<times> int) \<Rightarrow> ('b\<times>'c) list \<Rightarrow> (('b\<times>'c) list \<times> int)) \<Rightarrow> (('b\<times>'c) prefix_tree \<times>'d)" where
 "distribute_extension M T G cg_lookup cg_insert u w completeInputTraces append_heuristic = (let
      cu = cg_lookup G u;
      u0 = shortest_list_in_tree_or_default cu T u;
      l0 = -1::int;
      u' = fst ((foldl (append_heuristic T w) (u0,l0) (filter (isin T) cu)) :: (('b\<times>'c) list \<times> int));
      T' = insert T (u'@w);
      G' = cg_insert G (maximal_prefix_in_language M (initial M) (u'@w)) 
    in if completeInputTraces
      then let TC = complete_inputs_to_tree M (initial M) (outputs_as_list M) (map fst (u'@w));
               T'' = Prefix_Tree.combine T' TC
           in (T'',G')     
      else (T',G'))"

(* alternative implementation: consider inserting the intersection of L M and TC into G' *)
(*
fun distribute_extension :: "('a::linorder,'b::linorder,'c::linorder) fsm \<Rightarrow> ('b\<times>'c) prefix_tree \<Rightarrow> 'd \<Rightarrow> ('d \<Rightarrow> ('b\<times>'c) list \<Rightarrow> ('b\<times>'c) list list) \<Rightarrow> ('d \<Rightarrow> ('b\<times>'c) list \<Rightarrow> 'd) \<Rightarrow>('b\<times>'c) list \<Rightarrow> ('b\<times>'c) list \<Rightarrow> bool \<Rightarrow> (('b\<times>'c) prefix_tree \<Rightarrow> ('b\<times>'c) list \<Rightarrow> ('b\<times>'c) list \<Rightarrow> (('b\<times>'c) list \<times> int) \<Rightarrow> (('b\<times>'c) list \<times> int)) \<Rightarrow> (('b\<times>'c) prefix_tree \<times>'d)" where
 "distribute_extension M T G cg_lookup cg_insert u w completeInputTraces append_heuristic = (let
      u0 = shortest_list_in_tree_or_default (cg_lookup G u) T u;
      l0 = -1::int;
      u' = fst ((foldr (append_heuristic T w) (filter (isin T) (cg_lookup G u)) (u0,l0)) :: (('b\<times>'c) list \<times> int));
      T' = insert T (u'@w);
      G' = cg_insert G (maximal_prefix_in_language M (initial M) (u'@w)) 
    in if completeInputTraces
      then let lang = language_for_input M (after_initial M u') (map fst w);
               T'' = combine_after T' u' (Prefix_Tree.from_list lang);
               G'' = foldr (\<lambda> io G . cg_insert G (u'@io)) lang G'
           in (T'',G'')
      else (T',G'))"
*)


lemma distribute_extension_subset :
  "set T \<subseteq> set (fst (distribute_extension M T G cg_lookup cg_insert u w b heuristic))"
proof -

  define u0 where u0: "u0 = shortest_list_in_tree_or_default (cg_lookup G u) T u"
  define l0 where l0: "l0 = (-1::int)"
  define u' where u': "u' = fst (foldl (heuristic T w) (u0,l0) (filter (isin T) (cg_lookup G u)))"
  define T' where T': "T' = insert T (u'@w)"
  define G' where G': "G' = cg_insert G (maximal_prefix_in_language M (initial M) (u'@w))"

  have "set T \<subseteq> set T'"
    unfolding T' insert_set
    by blast

  show ?thesis proof (cases b)
    case True
    then show ?thesis
      using \<open>set T \<subseteq> set T'\<close> 
      unfolding distribute_extension.simps u0 l0 u' T' G' Let_def
      using combine_set
      by force
  next
    case False
    then have "fst (distribute_extension M T G cg_lookup cg_insert u w b heuristic) = T'"
      unfolding distribute_extension.simps u0 l0 u' T' G' Let_def by force
    then show ?thesis 
      using \<open>set T \<subseteq> set T'\<close>
      by blast
  qed
qed


lemma distribute_extension_finite :
  assumes "finite_tree T"
  shows "finite_tree (fst (distribute_extension M T G cg_lookup cg_insert u w b heuristic))"
proof -

  define u0 where u0: "u0 = shortest_list_in_tree_or_default (cg_lookup G u) T u"
  define l0 where l0: "l0 = (-1::int)"
  define u' where u': "u' = fst (foldl (heuristic T w) (u0,l0) (filter (isin T) (cg_lookup G u)))"
  define T' where T': "T' = insert T (u'@w)"
  define G' where G': "G' = cg_insert G (maximal_prefix_in_language M (initial M) (u'@w))"

  have "finite_tree T'"
    unfolding T' 
    using insert_finite_tree[OF assms]
    by blast

  show ?thesis proof (cases b)
    case True
    then show ?thesis
      using \<open>finite_tree T'\<close> 
      unfolding distribute_extension.simps u0 l0 u' T' G' Let_def
      by (simp add: combine_finite_tree complete_inputs_to_tree_finite_tree)
  next
    case False
    then have "fst (distribute_extension M T G cg_lookup cg_insert u w b heuristic) = T'"
      unfolding distribute_extension.simps u0 l0 u' T' G' Let_def by force
    then show ?thesis 
      using \<open>finite_tree T'\<close>
      by blast
  qed
qed
  

lemma distribute_extension_adds_sequence :
  fixes M1 :: "('a::linorder,'b::linorder,'c::linorder) fsm"
  assumes "observable M1"
  and     "minimal M1"
  and     "u \<in> L M1" and "u \<in> L M2"
  and     "convergence_graph_lookup_invar M1 M2 cg_lookup G"
  and     "convergence_graph_insert_invar M1 M2 cg_lookup cg_insert"
  and     "(L M1 \<inter> set (fst (distribute_extension M1 T G cg_lookup cg_insert u w b heuristic)) = L M2 \<inter> set (fst (distribute_extension M1 T G cg_lookup cg_insert u w b heuristic)))"
  and     "\<And> u' uBest lBest . fst (heuristic T w (uBest,lBest) u') \<in> {u',uBest}"
shows "\<exists> u' . converge M1 u u' \<and> u'@w \<in> set (fst (distribute_extension M1 T G cg_lookup cg_insert u w b heuristic)) \<and> converge M2 u u'"
and   "convergence_graph_lookup_invar M1 M2 cg_lookup (snd (distribute_extension M1 T G cg_lookup cg_insert u w b heuristic))"
proof -

  define u0 where u0: "u0 = shortest_list_in_tree_or_default (cg_lookup G u) T u"
  define l0 where l0: "l0 = (-1::int)"
  define u' where u': "u' = fst (foldl (heuristic T w) (u0,l0) (filter (isin T) (cg_lookup G u)))"
  define T' where T': "T' = insert T (u'@w)"
  define G' where G': "G' = cg_insert G (maximal_prefix_in_language M1 (initial M1) (u'@w))"

  define TC where TC: "TC = complete_inputs_to_tree M1 (initial M1) (outputs_as_list M1) (map fst (u'@w))"
  define T'' where T'': "T'' = Prefix_Tree.combine T' TC"

  have "distribute_extension M1 T G cg_lookup cg_insert u w b heuristic = (T',G') \<or>
        distribute_extension M1 T G cg_lookup cg_insert u w b heuristic = (T'',G')"
    unfolding distribute_extension.simps u0 l0 u' T' G' TC T'' Let_def by force
  moreover have "set T' \<subseteq> set T''"
    unfolding T'' combine_set by blast
  ultimately have "set T' \<subseteq> set (fst (distribute_extension M1 T G cg_lookup cg_insert u w b heuristic))"
    by force

  have "\<And> xs . fst (foldl (heuristic T w) (u0,l0) xs) \<in> Set.insert u0 (list.set xs)"
  proof -
    fix xs
    
    show "fst (foldl (heuristic T w) (u0,l0) xs) \<in> Set.insert u0 (list.set xs)"
    proof (induction xs rule: rev_induct)
      case Nil
      then show ?case 
        by auto
    next
      case (snoc x xs)
      have "\<And> u' uBest lBest . (fst ((heuristic T w) (uBest,lBest) u')) = u' \<or> (fst ((heuristic T w) (uBest,lBest) u')) = uBest"
        using assms(8) by blast
      then have "(fst ((heuristic T w) (foldl (heuristic T w) (u0, l0) xs) x)) = x \<or> (fst ((heuristic T w) (foldl (heuristic T w) (u0, l0) xs) x)) = fst (foldl (heuristic T w) (u0, l0) xs)"
        by (metis prod.exhaust_sel)
      then show ?case 
        using snoc.IH by auto        
    qed
  qed
  then have "u' \<in> Set.insert u0 (list.set (filter (isin T) (cg_lookup G u)))" 
    unfolding u'
    by blast
  then have "u' \<in> Set.insert u0 (list.set (cg_lookup G u))" 
    by auto
  moreover have "converge M1 u u0"
    unfolding u' 
    using shortest_list_in_tree_or_default_elem[of "cg_lookup G u" T u] 
    by (metis assms(1-5) convergence_graph_lookup_invar_def convergence_minimal insert_iff u0)
  moreover have "\<And> u' . u' \<in> list.set (cg_lookup G u) \<Longrightarrow> converge M1 u u'"
    using assms(3,4,5)
    by (metis convergence_graph_lookup_invar_def) 
  ultimately have "converge M1 u u'"
    by blast
  moreover have "u'@w \<in> set (fst (distribute_extension M1 T G cg_lookup cg_insert u w b heuristic))"
    using \<open>set T' \<subseteq> set (fst (distribute_extension M1 T G cg_lookup cg_insert u w b heuristic))\<close>
    unfolding T' insert_set fst_conv
    by blast
  moreover have "converge M2 u u'"
    by (metis \<open>u' \<in> Set.insert u0 (list.set (cg_lookup G u))\<close> assms(3) assms(4) assms(5) converge.elims(3) convergence_graph_lookup_invar_def insertE shortest_list_in_tree_or_default_elem u0)
  ultimately show "\<exists> u' . converge M1 u u' \<and> u'@w \<in> set (fst (distribute_extension M1 T G cg_lookup cg_insert u w b heuristic)) \<and> converge M2 u u'"
    by blast


  have "(maximal_prefix_in_language M1 (initial M1) (u'@w)) \<in> L M1"
  and  "(maximal_prefix_in_language M1 (initial M1) (u'@w)) \<in> list.set (prefixes (u'@w))"
    using maximal_prefix_in_language_properties[OF assms(1) fsm_initial]
    by auto
  
  moreover have "(maximal_prefix_in_language M1 (initial M1) (u'@w)) \<in> set (fst (distribute_extension M1 T G cg_lookup cg_insert u w b heuristic))"
    using \<open>u'@w \<in> set (fst (distribute_extension M1 T G cg_lookup cg_insert u w b heuristic))\<close> set_prefix
    by (metis (no_types, lifting) \<open>maximal_prefix_in_language M1 (FSM.initial M1) (u' @ w) \<in> list.set (prefixes (u' @ w))\<close> prefixes_set_ob) 
  ultimately have "(maximal_prefix_in_language M1 (initial M1) (u'@w)) \<in> L M2"
    using assms(7)
    by blast

  have "convergence_graph_lookup_invar M1 M2 cg_lookup G'"
    using assms(5,6) \<open>(maximal_prefix_in_language M1 (initial M1) (u'@w)) \<in> L M1\<close> \<open>(maximal_prefix_in_language M1 (initial M1) (u'@w)) \<in> L M2\<close>
    unfolding G' convergence_graph_insert_invar_def 
    by blast
  
  
  show "convergence_graph_lookup_invar M1 M2 cg_lookup (snd (distribute_extension M1 T G cg_lookup cg_insert u w b heuristic))"
    using \<open>convergence_graph_lookup_invar M1 M2 cg_lookup G'\<close> 
    unfolding distribute_extension.simps u0 l0 u' T' G' Let_def by force
qed


subsubsection \<open>Distinguishing a Trace from Other Traces\<close>

fun spyh_distinguish :: "('a::linorder,'b::linorder,'c::linorder) fsm \<Rightarrow> ('b\<times>'c) prefix_tree \<Rightarrow> 'd \<Rightarrow> ('d \<Rightarrow> ('b\<times>'c) list \<Rightarrow> ('b\<times>'c) list list) \<Rightarrow> ('d \<Rightarrow> ('b\<times>'c) list \<Rightarrow> 'd) \<Rightarrow> ('a \<Rightarrow> 'a \<Rightarrow> ('b\<times>'c) list) \<Rightarrow> ('b\<times>'c) list \<Rightarrow> ('b\<times>'c) list list \<Rightarrow> nat \<Rightarrow> bool \<Rightarrow> (('b\<times>'c) prefix_tree \<Rightarrow> ('b\<times>'c) list \<Rightarrow> (('b\<times>'c) list \<times> int) \<Rightarrow> ('b\<times>'c) list \<Rightarrow> (('b\<times>'c) list \<times> int)) \<Rightarrow> (('b\<times>'c) prefix_tree \<times> 'd)" where
  "spyh_distinguish M T G cg_lookup cg_insert get_distinguishing_trace u X k completeInputTraces append_heuristic = (let 
      dist_helper = (\<lambda> (T,G) v . if after_initial M u = after_initial M v
                                  then (T,G)
                                  else (let ew = get_prefix_of_separating_sequence M T G cg_lookup get_distinguishing_trace u v k
                                         in if fst ew = 0
                                              then (T,G)
                                              else (let u' = (u@(snd ew));
                                                        v' = (v@(snd ew));
                                                        w' = if does_distinguish M (after_initial M u) (after_initial M v) (snd ew) then (snd ew) else (snd ew)@(get_distinguishing_trace (after_initial M u') (after_initial M v'));
                                                        TG' = distribute_extension M T G cg_lookup cg_insert u w' completeInputTraces append_heuristic
                                                    in distribute_extension M (fst TG') (snd TG') cg_lookup cg_insert v w' completeInputTraces append_heuristic)))
    in foldl dist_helper (T,G) X)"



lemma spyh_distinguish_subset :
  "set T \<subseteq> set (fst (spyh_distinguish M T G cg_lookup cg_insert get_distinguishing_trace u X k completeInputTraces append_heuristic))"
proof (induction X rule: rev_induct)
  case Nil
  then show ?case by auto
next
  case (snoc a X)

  have "set (fst (spyh_distinguish M T G cg_lookup cg_insert get_distinguishing_trace u X k completeInputTraces append_heuristic))
         \<subseteq> set (fst (spyh_distinguish M T G cg_lookup cg_insert get_distinguishing_trace u (X@[a]) k completeInputTraces append_heuristic))"
  proof -
    define dh where dh: "dh = (\<lambda> (T,G) v . if after_initial M u = after_initial M v
                                  then (T,G)
                                  else (let ew = get_prefix_of_separating_sequence M T G cg_lookup get_distinguishing_trace u v k
                                         in if fst ew = 0
                                              then (T,G)
                                              else (let u' = (u@(snd ew));
                                                        v' = (v@(snd ew));
                                                        w' = if does_distinguish M (after_initial M u) (after_initial M v) (snd ew) then (snd ew) else (snd ew)@(get_distinguishing_trace (after_initial M u') (after_initial M v'));
                                                        TG' = distribute_extension M T G cg_lookup cg_insert u w' completeInputTraces append_heuristic
                                                    in distribute_extension M (fst TG') (snd TG') cg_lookup cg_insert v w' completeInputTraces append_heuristic)))"

    have "spyh_distinguish M T G cg_lookup cg_insert get_distinguishing_trace u (X@[a]) k completeInputTraces append_heuristic
                = dh (spyh_distinguish M T G cg_lookup cg_insert get_distinguishing_trace u X k completeInputTraces append_heuristic) a"
      unfolding dh spyh_distinguish.simps Let_def
      unfolding foldl_append
      by auto

    moreover have "\<And> T G . set T \<subseteq> set (fst (dh (T,G) a))"
    proof -
      fix T G 
      show "set T \<subseteq> set (fst (dh (T,G) a))"        
      proof (cases "after_initial M u = after_initial M a")
        case True
        then show ?thesis using dh by auto
      next
        case False
        then show ?thesis proof (cases "fst (get_prefix_of_separating_sequence M T G cg_lookup get_distinguishing_trace u a k) = 0")
          case True
          then show ?thesis using False dh by auto
        next
          case False

          define u' where u': "u' = (u@(snd (get_prefix_of_separating_sequence M T G cg_lookup get_distinguishing_trace u a k)))"
          define v' where v': "v' = (a@(snd (get_prefix_of_separating_sequence M T G cg_lookup get_distinguishing_trace u a k)))"
          define w where w: "w = get_distinguishing_trace (after_initial M u') (after_initial M v')"
          define w' where w': "w' = (if does_distinguish M (after_initial M u) (after_initial M a) (snd (get_prefix_of_separating_sequence M T G cg_lookup get_distinguishing_trace u a k)) then (snd (get_prefix_of_separating_sequence M T G cg_lookup get_distinguishing_trace u a k)) else (snd (get_prefix_of_separating_sequence M T G cg_lookup get_distinguishing_trace u a k))@w)"
          define TG' where TG': "TG' = distribute_extension M T G cg_lookup cg_insert u w' completeInputTraces append_heuristic"

          have "dh (T,G) a = distribute_extension M (fst (distribute_extension M T G cg_lookup cg_insert u w' completeInputTraces append_heuristic)) (snd (distribute_extension M T G cg_lookup cg_insert u w' completeInputTraces append_heuristic)) cg_lookup cg_insert a w' completeInputTraces append_heuristic"
            using False \<open>FSM.after M (FSM.initial M) u \<noteq> FSM.after M (FSM.initial M) a\<close>
            unfolding dh u' v' w w' TG' Let_def case_prod_conv by metis

          then show ?thesis
            using distribute_extension_subset
            by (metis (no_types, lifting) subset_trans)
        qed
      qed
    qed

    ultimately show ?thesis 
      by (metis eq_fst_iff)
  qed

  then show ?case 
    using snoc.IH by blast
qed

lemma spyh_distinguish_finite :
  fixes T :: "('b::linorder\<times>'c::linorder) prefix_tree"
  assumes "finite_tree T"
  shows "finite_tree (fst (spyh_distinguish M T G cg_lookup cg_insert get_distinguishing_trace u X k completeInputTraces append_heuristic))"
proof (induction X rule: rev_induct)
  case Nil
  then show ?case using assms by auto
next
  case (snoc a X)

  
  define dh where dh: "dh = (\<lambda> (T,G) v . if after_initial M u = after_initial M v
                                then (T,G)
                                else (let ew = get_prefix_of_separating_sequence M T G cg_lookup get_distinguishing_trace u v k
                                       in if fst ew = 0
                                            then (T,G)
                                            else (let u' = (u@(snd ew));
                                                      v' = (v@(snd ew));
                                                      w' = if does_distinguish M (after_initial M u) (after_initial M v) (snd ew) then (snd ew) else (snd ew)@(get_distinguishing_trace (after_initial M u') (after_initial M v'));
                                                      TG' = distribute_extension M T G cg_lookup cg_insert u w' completeInputTraces append_heuristic
                                                  in distribute_extension M (fst TG') (snd TG') cg_lookup cg_insert v w' completeInputTraces append_heuristic)))"

  have *: "spyh_distinguish M T G cg_lookup cg_insert get_distinguishing_trace u (X@[a]) k completeInputTraces append_heuristic
                = dh (spyh_distinguish M T G cg_lookup cg_insert get_distinguishing_trace u X k completeInputTraces append_heuristic) a"
      unfolding dh spyh_distinguish.simps Let_def
      unfolding foldl_append
      by auto

  have **:"\<And> T G . finite_tree T \<Longrightarrow> finite_tree (fst (dh (T,G) a))"
  proof -
    fix T :: "('b\<times>'c) prefix_tree"
    fix G 
    assume "finite_tree T"                      
    show "finite_tree (fst (dh (T,G) a))"        
    proof (cases "after_initial M u = after_initial M a")
      case True
      then show ?thesis using dh \<open>finite_tree T\<close> by auto
    next
      case False
      then show ?thesis proof (cases "fst (get_prefix_of_separating_sequence M T G cg_lookup get_distinguishing_trace u a k) = 0")
        case True
        then show ?thesis using False dh \<open>finite_tree T\<close> by auto
      next
        case False

        define u' where u': "u' = (u@(snd (get_prefix_of_separating_sequence M T G cg_lookup get_distinguishing_trace u a k)))"
        define v' where v': "v' = (a@(snd (get_prefix_of_separating_sequence M T G cg_lookup get_distinguishing_trace u a k)))"
        define w where w: "w = get_distinguishing_trace (after_initial M u') (after_initial M v')"
        define w' where w': "w' = (if does_distinguish M (after_initial M u) (after_initial M a) (snd (get_prefix_of_separating_sequence M T G cg_lookup get_distinguishing_trace u a k)) then (snd (get_prefix_of_separating_sequence M T G cg_lookup get_distinguishing_trace u a k)) else (snd (get_prefix_of_separating_sequence M T G cg_lookup get_distinguishing_trace u a k))@w)"
        define TG' where TG': "TG' = distribute_extension M T G cg_lookup cg_insert u w'"

        have *:"dh (T,G) a = distribute_extension M (fst (distribute_extension M T G cg_lookup cg_insert u w' completeInputTraces append_heuristic)) (snd (distribute_extension M T G cg_lookup cg_insert u w' completeInputTraces append_heuristic)) cg_lookup cg_insert a w' completeInputTraces append_heuristic"
          using False \<open>FSM.after M (FSM.initial M) u \<noteq> FSM.after M (FSM.initial M) a\<close>
          unfolding dh u' v' w w' TG' Let_def case_prod_conv by metis

        show ?thesis
          unfolding *
          using distribute_extension_finite[OF distribute_extension_finite[OF \<open>finite_tree T\<close>]]
          by metis
      qed
    qed
  qed

  show ?case 
    unfolding *
    using **[OF snoc]
    by (metis eq_fst_iff)
qed


lemma spyh_distinguish_establishes_divergence :
  fixes M1 :: "('a::linorder,'b::linorder,'c::linorder) fsm"
  assumes "observable M1"
  and     "observable M2"
  and     "minimal M1"
  and     "minimal M2"
  and     "u \<in> L M1" and "u \<in> L M2"
  and     "\<And> \<alpha> \<beta> q1 q2 . q1 \<in> states M1 \<Longrightarrow> q2 \<in> states M1 \<Longrightarrow> q1 \<noteq> q2 \<Longrightarrow> distinguishes M1 q1 q2 (get_distinguishing_trace q1 q2)"
  and     "convergence_graph_lookup_invar M1 M2 cg_lookup G"
  and     "convergence_graph_insert_invar M1 M2 cg_lookup cg_insert"
  and     "list.set X \<subseteq> L M1"
  and     "list.set X \<subseteq> L M2"
  and     "L M1 \<inter> set (fst (spyh_distinguish M1 T G cg_lookup cg_insert get_distinguishing_trace u X k completeInputTraces append_heuristic)) = L M2 \<inter> set (fst (spyh_distinguish M1 T G cg_lookup cg_insert get_distinguishing_trace u X k completeInputTraces append_heuristic))"
  and     "\<And> T w u' uBest lBest . fst (append_heuristic T w (uBest,lBest) u') \<in> {u',uBest}"
shows "\<forall> v . v \<in> list.set X \<longrightarrow> \<not> converge M1 u v \<longrightarrow> \<not> converge M2 u v"
(is "?P1 X")
and   "convergence_graph_lookup_invar M1 M2 cg_lookup (snd (spyh_distinguish M1 T G cg_lookup cg_insert get_distinguishing_trace u X k completeInputTraces append_heuristic))"
(is "?P2 X")
proof -
  have "?P1 X \<and> ?P2 X"
    using assms(10,11,12) 
  proof (induction X rule: rev_induct)
    case Nil

    have *: "spyh_distinguish M1 T G cg_lookup cg_insert get_distinguishing_trace u [] k completeInputTraces append_heuristic = (T,G)"
      by auto

    show ?case 
      using Nil assms(8)
      unfolding * fst_conv snd_conv by auto
  next
    case (snoc a X)

    define dh where dh: "dh = (\<lambda> (T,G) v . if after_initial M1 u = after_initial M1 v
                                  then (T,G)
                                  else (let ew = get_prefix_of_separating_sequence M1 T G cg_lookup get_distinguishing_trace u v k
                                         in if fst ew = 0
                                              then (T,G)
                                              else (let u' = (u@(snd ew));
                                                        v' = (v@(snd ew));
                                                        w' = (if does_distinguish M1 (after_initial M1 u) (after_initial M1 v) (snd ew) then (snd ew) else (snd ew)@(get_distinguishing_trace (after_initial M1 u') (after_initial M1 v')));
                                                        TG' = distribute_extension M1 T G cg_lookup cg_insert u w' completeInputTraces append_heuristic
                                                    in distribute_extension M1 (fst TG') (snd TG') cg_lookup cg_insert v w' completeInputTraces append_heuristic)))"

    have "spyh_distinguish M1 T G cg_lookup cg_insert get_distinguishing_trace u (X@[a]) k completeInputTraces append_heuristic
                = dh (spyh_distinguish M1 T G cg_lookup cg_insert get_distinguishing_trace u X k completeInputTraces append_heuristic) a"
      unfolding dh spyh_distinguish.simps Let_def
      unfolding foldl_append
      by auto



    have "\<And> T G . set T \<subseteq> set (fst (dh (T,G) a))"
    proof -
      fix T G 
      show "set T \<subseteq> set (fst (dh (T,G) a))"        
      proof (cases "after_initial M1 u = after_initial M1 a")
        case True
        then show ?thesis using dh by auto
      next
        case False
        then show ?thesis proof (cases "fst (get_prefix_of_separating_sequence M1 T G cg_lookup get_distinguishing_trace u a k) = 0")
          case True
          then show ?thesis using False dh by auto
        next
          case False

          define u' where u': "u' = (u@(snd (get_prefix_of_separating_sequence M1 T G cg_lookup get_distinguishing_trace u a k)))"
          define v' where v': "v' = (a@(snd (get_prefix_of_separating_sequence M1 T G cg_lookup get_distinguishing_trace u a k)))"
          define w where w: "w = get_distinguishing_trace (after_initial M1 u') (after_initial M1 v')"
          define w' where w': "w' = (if does_distinguish M1 (after_initial M1 u) (after_initial M1 a) (snd (get_prefix_of_separating_sequence M1 T G cg_lookup get_distinguishing_trace u a k)) then (snd (get_prefix_of_separating_sequence M1 T G cg_lookup get_distinguishing_trace u a k)) else (snd (get_prefix_of_separating_sequence M1 T G cg_lookup get_distinguishing_trace u a k))@w)"
          define TG' where TG': "TG' = distribute_extension M1 T G cg_lookup cg_insert u w'"

          have "dh (T,G) a = distribute_extension M1 (fst (distribute_extension M1 T G cg_lookup cg_insert u w' completeInputTraces append_heuristic)) (snd (distribute_extension M1 T G cg_lookup cg_insert u w' completeInputTraces append_heuristic)) cg_lookup cg_insert a w' completeInputTraces append_heuristic"
            using False \<open>FSM.after M1 (FSM.initial M1) u \<noteq> FSM.after M1 (FSM.initial M1) a\<close>
            unfolding dh u' v' w w' TG' Let_def case_prod_conv by metis

          then show ?thesis
            using distribute_extension_subset
            by (metis (no_types, lifting) subset_trans)
        qed
      qed
    qed
    then have "set (fst (spyh_distinguish M1 T G cg_lookup cg_insert get_distinguishing_trace u X k completeInputTraces append_heuristic)) \<subseteq> set (fst (spyh_distinguish M1 T G cg_lookup cg_insert get_distinguishing_trace u (X@[a]) k completeInputTraces append_heuristic))" 
      unfolding \<open>spyh_distinguish M1 T G cg_lookup cg_insert get_distinguishing_trace u (X@[a]) k completeInputTraces append_heuristic = dh (spyh_distinguish M1 T G cg_lookup cg_insert get_distinguishing_trace u X k completeInputTraces append_heuristic) a\<close>
      by (metis prod.exhaust_sel)
    then have "L M1 \<inter> Prefix_Tree.set (fst (spyh_distinguish M1 T G cg_lookup cg_insert get_distinguishing_trace u X k completeInputTraces append_heuristic)) = L M2 \<inter> Prefix_Tree.set (fst (spyh_distinguish M1 T G cg_lookup cg_insert get_distinguishing_trace u X k completeInputTraces append_heuristic))"
      using snoc.prems(3) by blast
    moreover have "list.set X \<subseteq> L M1"
      using snoc.prems(1) by auto
    moreover have "list.set X \<subseteq> L M2"
      using snoc.prems(2) by auto
    ultimately have "?P1 X" and "?P2 X"
      using snoc.IH by blast+


    obtain T' G' where "(spyh_distinguish M1 T G cg_lookup cg_insert get_distinguishing_trace u X k completeInputTraces append_heuristic) = (T',G')"
      using prod.exhaust by metis

    then have "convergence_graph_lookup_invar M1 M2 cg_lookup G'"
      using \<open>?P2 X\<close> by auto

    have "L M1 \<inter> set T' = L M2 \<inter> set T'"
      using \<open>L M1 \<inter> Prefix_Tree.set (fst (spyh_distinguish M1 T G cg_lookup cg_insert get_distinguishing_trace u X k completeInputTraces append_heuristic)) = L M2 \<inter> Prefix_Tree.set (fst (spyh_distinguish M1 T G cg_lookup cg_insert get_distinguishing_trace u X k completeInputTraces append_heuristic))\<close>
            \<open>(spyh_distinguish M1 T G cg_lookup cg_insert get_distinguishing_trace u X k completeInputTraces append_heuristic) = (T',G')\<close>
      by auto 
    

    have "\<not>converge M1 u a \<Longrightarrow> \<not>converge M2 u a" and "?P2 (X@[a])"
    proof -
      have "a \<in> L M1"
        using snoc.prems(1) by auto
      then have "\<not>converge M1 u a \<Longrightarrow> after_initial M1 u \<noteq> after_initial M1 a"
        using \<open>u \<in> L M1\<close> 
        using assms(1) assms(3) convergence_minimal by blast

      have "a \<in> L M2"
        using snoc.prems(2) by auto

      define ew where ew: "ew = get_prefix_of_separating_sequence M1 T' G' cg_lookup get_distinguishing_trace u a k"

      have "(\<not>converge M1 u a \<longrightarrow> \<not>converge M2 u a) \<and> ?P2 (X@[a])"
      proof (cases "fst ew = 0")
        case True
        then have *: "fst (get_prefix_of_separating_sequence M1 T' G' cg_lookup get_distinguishing_trace u a k) = 0"
          unfolding ew by auto

        have "L M1 \<inter> Prefix_Tree.set T' = L M2 \<inter> Prefix_Tree.set T' \<Longrightarrow> \<not> converge M1 u a \<Longrightarrow> \<not> converge M2 u a" 
          using get_prefix_of_separating_sequence_result(1)[OF assms(1,2,3) \<open>u \<in> L M1\<close> \<open>u \<in> L M2\<close> \<open>a \<in> L M1\<close> \<open>a \<in> L M2\<close> \<open>\<not>converge M1 u a \<Longrightarrow> after_initial M1 u \<noteq> after_initial M1 a\<close> assms(7) \<open>convergence_graph_lookup_invar M1 M2 cg_lookup G'\<close> _ *] 
          by fast
        then have "(\<not>converge M1 u a \<longrightarrow> \<not>converge M2 u a)"
          using \<open>L M1 \<inter> set T' = L M2 \<inter> set T'\<close>
          by blast

        have "(snd (spyh_distinguish M1 T G cg_lookup cg_insert get_distinguishing_trace u (X@[a]) k completeInputTraces append_heuristic)) = (snd (spyh_distinguish M1 T G cg_lookup cg_insert get_distinguishing_trace u X k completeInputTraces append_heuristic))"
          unfolding \<open>spyh_distinguish M1 T G cg_lookup cg_insert get_distinguishing_trace u (X@[a]) k completeInputTraces append_heuristic = dh (spyh_distinguish M1 T G cg_lookup cg_insert get_distinguishing_trace u X k completeInputTraces append_heuristic) a\<close>
          unfolding \<open>(spyh_distinguish M1 T G cg_lookup cg_insert get_distinguishing_trace u X k completeInputTraces append_heuristic) = (T',G')\<close>
          unfolding dh case_prod_conv snd_conv
          using True ew
          by fastforce 
        then have "?P2 (X@[a])"
          using \<open>?P2 X\<close>
          by auto
        then show ?thesis 
          using \<open>(\<not>converge M1 u a \<longrightarrow> \<not>converge M2 u a)\<close>
          by auto          
      next
        case False
        then have *: "fst (get_prefix_of_separating_sequence M1 T' G' cg_lookup get_distinguishing_trace u a k) \<noteq> 0"
          unfolding ew by auto

        define w where w: "w = get_distinguishing_trace (after_initial M1 (u@(snd ew))) (after_initial M1 (a@(snd ew)))"
        define w' where w': "w' = (if does_distinguish M1 (after_initial M1 u) (after_initial M1 a) (snd ew) then (snd ew) else (snd ew)@w)"
        define TG' where TG': "TG' = distribute_extension M1 T' G' cg_lookup cg_insert u w' completeInputTraces append_heuristic"

        show ?thesis proof (cases "\<not> converge M1 u a")
          case True
          then have "after_initial M1 u \<noteq> after_initial M1 a"
            using \<open>u \<in> L M1\<close> \<open>a \<in> L M1\<close>
            using assms(1) assms(3) convergence_minimal by blast

          obtain \<gamma> where "distinguishes M1 (after_initial M1 u) (after_initial M1 a) (snd ew @ \<gamma>)"
            unfolding \<open>ew = get_prefix_of_separating_sequence M1 T' G' cg_lookup get_distinguishing_trace u a k\<close>
            using get_prefix_of_separating_sequence_result(2)[OF assms(1,2,3) \<open>u \<in> L M1\<close> \<open>u \<in> L M2\<close> \<open>a \<in> L M1\<close> \<open>a \<in> L M2\<close> \<open>after_initial M1 u \<noteq> after_initial M1 a\<close> assms(7) \<open>convergence_graph_lookup_invar M1 M2 cg_lookup G'\<close> _ *]
            using \<open>L M1 \<inter> Prefix_Tree.set T' = L M2 \<inter> Prefix_Tree.set T'\<close> by presburger

          have "dh (T',G') a = distribute_extension M1 (fst TG') (snd TG') cg_lookup cg_insert a w' completeInputTraces append_heuristic"
            unfolding dh w w' TG' case_prod_conv
            unfolding ew[symmetric] Let_def
            using ew False \<open>after_initial M1 u \<noteq> after_initial M1 a\<close>
            by meson 
  
          have "L M1 \<inter> set (fst (dh (T',G') a)) = L M2 \<inter> set (fst (dh (T',G') a))"
            using snoc.prems(3)
            using \<open>spyh_distinguish M1 T G cg_lookup cg_insert get_distinguishing_trace u (X@[a]) k completeInputTraces append_heuristic = dh (spyh_distinguish M1 T G cg_lookup cg_insert get_distinguishing_trace u X k completeInputTraces append_heuristic) a\<close> \<open>spyh_distinguish M1 T G cg_lookup cg_insert get_distinguishing_trace u X k completeInputTraces append_heuristic = (T', G')\<close> 
            by auto 
          moreover have "set (fst (distribute_extension M1 T' G' cg_lookup cg_insert u w' completeInputTraces append_heuristic)) \<subseteq> set (fst (dh (T',G') a))"
            by (metis TG' \<open>dh (T', G') a = distribute_extension M1 (fst TG') (snd TG') cg_lookup cg_insert a w' completeInputTraces append_heuristic\<close> distribute_extension_subset)
          ultimately have "(L M1 \<inter> set (fst (distribute_extension M1 T' G' cg_lookup cg_insert u w' completeInputTraces append_heuristic)) = L M2 \<inter> set (fst (distribute_extension M1 T' G' cg_lookup cg_insert u w' completeInputTraces append_heuristic)))"
            by blast
  
          obtain u' where "converge M1 u u'" and "converge M2 u u'"
                      and "u' @ w' \<in> set (fst (distribute_extension M1 T' G' cg_lookup cg_insert u w' completeInputTraces append_heuristic))"
                      and "convergence_graph_lookup_invar M1 M2 cg_lookup (snd TG')"
            using distribute_extension_adds_sequence[OF assms(1,3) \<open>u \<in> L M1\<close> \<open>u \<in> L M2\<close> \<open>convergence_graph_lookup_invar M1 M2 cg_lookup G'\<close> \<open>convergence_graph_insert_invar M1 M2 cg_lookup cg_insert\<close>, of _ _ completeInputTraces append_heuristic, OF _ assms(13) ]  
                  \<open>(L M1 \<inter> set (fst (distribute_extension M1 T' G' cg_lookup cg_insert u w' completeInputTraces append_heuristic)) = L M2 \<inter> set (fst (distribute_extension M1 T' G' cg_lookup cg_insert u w' completeInputTraces append_heuristic)))\<close>
            unfolding TG'
            by blast
          then have "u' @ w' \<in> set (fst (dh (T',G') a))"
            unfolding \<open>dh (T',G') a = distribute_extension M1 (fst TG') (snd TG') cg_lookup cg_insert a w' completeInputTraces append_heuristic\<close> 
            by (metis (no_types, opaque_lifting) TG' distribute_extension_subset in_mono)
  
  
          obtain a' where "converge M1 a a'" and "converge M2 a a'"
                      and "a' @ w' \<in> set (fst (dh (T',G') a))"
                      and "convergence_graph_lookup_invar M1 M2 cg_lookup (snd (dh (T',G') a))"
            using distribute_extension_adds_sequence[OF assms(1,3) \<open>a \<in> L M1\<close> \<open>a \<in> L M2\<close> \<open>convergence_graph_lookup_invar M1 M2 cg_lookup (snd TG')\<close> \<open>convergence_graph_insert_invar M1 M2 cg_lookup cg_insert\<close>, of "fst TG'" w' completeInputTraces append_heuristic, OF _ assms(13)]
                  \<open>L M1 \<inter> set (fst (dh (T',G') a)) = L M2 \<inter> set (fst (dh (T',G') a))\<close>
            unfolding \<open>dh (T',G') a = distribute_extension M1 (fst TG') (snd TG') cg_lookup cg_insert a w' completeInputTraces append_heuristic\<close>
            by blast
  
          have "u' \<in> L M1" and "a' \<in> L M1"
            using \<open>converge M1 u u'\<close> \<open>converge M1 a a'\<close> by auto
  
          have "?P2 (X@[a])"
            using \<open>convergence_graph_lookup_invar M1 M2 cg_lookup (snd (dh (T',G') a))\<close>
            using False \<open>after_initial M1 u \<noteq> after_initial M1 a\<close>
            using \<open>spyh_distinguish M1 T G cg_lookup cg_insert get_distinguishing_trace u (X@[a]) k completeInputTraces append_heuristic = dh (spyh_distinguish M1 T G cg_lookup cg_insert get_distinguishing_trace u X k completeInputTraces append_heuristic) a\<close> \<open>spyh_distinguish M1 T G cg_lookup cg_insert get_distinguishing_trace u X k completeInputTraces append_heuristic= (T', G')\<close> 
            by presburger
            
  
          show ?thesis proof (cases "does_distinguish M1 (after_initial M1 u) (after_initial M1 a) (snd ew)")
            case True
            then have "distinguishes M1 (after_initial M1 u) (after_initial M1 a) w'"
              using does_distinguish_correctness[OF assms(1) after_is_state[OF assms(1) \<open>u \<in> L M1\<close>] after_is_state[OF assms(1) \<open>a \<in> L M1\<close>]] w'
              by metis
  
            show ?thesis 
              using distinguish_converge_diverge[OF assms(1,2,3) \<open>u' \<in> L M1\<close> \<open>a' \<in> L M1\<close> \<open>converge M1 u u'\<close> \<open>converge M1 a a'\<close> \<open>converge M2 u u'\<close> \<open>converge M2 a a'\<close> \<open>distinguishes M1 (after_initial M1 u) (after_initial M1 a) w'\<close> \<open>u' @ w' \<in> set (fst (dh (T',G') a))\<close> \<open>a' @ w' \<in> set (fst (dh (T',G') a))\<close> \<open>L M1 \<inter> set (fst (dh (T',G') a)) = L M2 \<inter> set (fst (dh (T',G') a))\<close>] 
                    \<open>?P2 (X@[a])\<close>  
              by blast
          next
            case False
            then have "\<not> distinguishes M1 (after_initial M1 u) (after_initial M1 a) (snd ew)"
              using does_distinguish_correctness[OF assms(1) after_is_state[OF assms(1) \<open>u \<in> L M1\<close>] after_is_state[OF assms(1) \<open>a \<in> L M1\<close>]] 
              by blast
            then have "snd ew \<in> LS M1 (after_initial M1 u) = (snd ew \<in> LS M1 (after_initial M1 a))"
              unfolding distinguishes_def 
              by blast
            moreover have "snd ew \<in> LS M1 (after_initial M1 u) \<or> (snd ew \<in> LS M1 (after_initial M1 a))"
              using \<open>distinguishes M1 (after_initial M1 u) (after_initial M1 a) (snd ew @ \<gamma>)\<close>
              using language_prefix[of "snd ew" \<gamma>]
              unfolding distinguishes_def 
              by fast
            ultimately have "snd ew \<in> LS M1 (after_initial M1 u)" and "snd ew \<in> LS M1 (after_initial M1 a)"
              by auto
  
            have "after_initial M1 (u @ snd ew) \<in> states M1"
              using \<open>snd ew \<in> LS M1 (after_initial M1 u)\<close> after_is_state[OF assms(1) \<open>u \<in> L M1\<close>]
              by (meson after_is_state after_language_iff assms(1) assms(5))
            moreover have "after_initial M1 (a @ snd ew) \<in> states M1"
              using \<open>snd ew \<in> LS M1 (after_initial M1 a)\<close> after_is_state[OF assms(1) \<open>a \<in> L M1\<close>]
              by (meson \<open>a \<in> L M1\<close> after_is_state after_language_iff assms(1))
            moreover have "after_initial M1 (u @ snd ew) \<noteq> after_initial M1 (a @ snd ew)" 
              using \<open>distinguishes M1 (after_initial M1 u) (after_initial M1 a) (snd ew @ \<gamma>)\<close>
              by (metis \<open>a \<in> L M1\<close> \<open>snd ew \<in> LS M1 (after_initial M1 a)\<close> \<open>snd ew \<in> LS M1 (after_initial M1 u)\<close> after_distinguishes_language after_language_iff append.assoc assms(1) assms(5))
            ultimately have "distinguishes M1 (after_initial M1 (u @ snd ew)) (after_initial M1 (a @ snd ew)) w"
              unfolding w using assms(7)
              by blast 
            moreover have "w' = snd ew @ w"
              using False w' by auto
            ultimately have "distinguishes M1 (after_initial M1 u) (after_initial M1 a) w'"
              using distinguish_prepend_initial[OF assms(1)]
              by (meson \<open>a \<in> L M1\<close> \<open>snd ew \<in> LS M1 (after_initial M1 a)\<close> \<open>snd ew \<in> LS M1 (after_initial M1 u)\<close> after_language_iff assms(1) assms(5))
  
            show ?thesis 
              using distinguish_converge_diverge[OF assms(1,2,3) \<open>u' \<in> L M1\<close> \<open>a' \<in> L M1\<close> \<open>converge M1 u u'\<close> \<open>converge M1 a a'\<close> \<open>converge M2 u u'\<close> \<open>converge M2 a a'\<close> \<open>distinguishes M1 (after_initial M1 u) (after_initial M1 a) w'\<close> \<open>u' @ w' \<in> set (fst (dh (T',G') a))\<close> \<open>a' @ w' \<in> set (fst (dh (T',G') a))\<close> \<open>L M1 \<inter> set (fst (dh (T',G') a)) = L M2 \<inter> set (fst (dh (T',G') a))\<close>]
                    \<open>?P2 (X@[a])\<close>  
              by blast
          qed
        next
          case False
          then have "after_initial M1 u = after_initial M1 a"
            by (meson \<open>a \<in> L M1\<close> assms(1) assms(3) assms(5) convergence_minimal)
          then have "dh (T',G') a = (T',G')"
            unfolding dh case_prod_conv 
            by auto
          then have "?P2 (X@[a])"
            using \<open>?P2 X\<close>
            by (metis \<open>spyh_distinguish M1 T G cg_lookup cg_insert get_distinguishing_trace u (X@[a]) k completeInputTraces append_heuristic = dh (spyh_distinguish M1 T G cg_lookup cg_insert get_distinguishing_trace u X k completeInputTraces append_heuristic) a\<close> \<open>spyh_distinguish M1 T G cg_lookup cg_insert get_distinguishing_trace u X k completeInputTraces append_heuristic = (T', G')\<close>) 
          then show ?thesis
            using False
            by blast
        qed
      qed
      then show "\<not> converge M1 u a \<Longrightarrow> \<not> converge M2 u a"
            and "?P2 (X@[a])"
        by blast+
    qed
    
    have "?P1 (X@[a])"
    proof -  
      have "\<And> v . v \<in> list.set X \<Longrightarrow> \<not>converge M1 u v \<Longrightarrow> \<not>converge M2 u v"
        using \<open>?P1 X\<close> 
        unfolding preserves_divergence.simps
        using Int_absorb2 \<open>list.set X \<subseteq> L M1\<close> assms(5) by blast 
      then show ?thesis
        using \<open>\<not> converge M1 u a \<Longrightarrow> \<not> converge M2 u a\<close> by auto
    qed
    then show ?case
      using \<open>?P2 (X@[a])\<close> by auto
  qed

  then show "?P1 X" and "?P2 X"
    by auto
qed


lemma spyh_distinguish_preserves_divergence :
  fixes M1 :: "('a::linorder,'b::linorder,'c::linorder) fsm"
  assumes "observable M1"
  and     "observable M2"
  and     "minimal M1"
  and     "minimal M2"
  and     "u \<in> L M1" and "u \<in> L M2"
  and     "\<And> \<alpha> \<beta> q1 q2 . q1 \<in> states M1 \<Longrightarrow> q2 \<in> states M1 \<Longrightarrow> q1 \<noteq> q2 \<Longrightarrow> distinguishes M1 q1 q2 (get_distinguishing_trace q1 q2)"
  and     "convergence_graph_lookup_invar M1 M2 cg_lookup G"
  and     "convergence_graph_insert_invar M1 M2 cg_lookup cg_insert"
  and     "list.set X \<subseteq> L M1"
  and     "list.set X \<subseteq> L M2"
  and     "L M1 \<inter> set (fst (spyh_distinguish M1 T G cg_lookup cg_insert get_distinguishing_trace u X k completeInputTraces append_heuristic)) = L M2 \<inter> set (fst (spyh_distinguish M1 T G cg_lookup cg_insert get_distinguishing_trace u X k completeInputTraces append_heuristic))"
  and     "\<And> T w u' uBest lBest . fst (append_heuristic T w (uBest,lBest) u') \<in> {u',uBest}"
  and     "preserves_divergence M1 M2 (list.set X)"
shows "preserves_divergence M1 M2 (Set.insert u (list.set X))"
(is "?P1 X")
  using spyh_distinguish_establishes_divergence(1)[OF assms(1-13)] 
  using assms(14) 
  unfolding preserves_divergence.simps
  by (metis IntD2 Int_iff assms(10) converge.elims(2) converge.elims(3) inf.absorb_iff2 insert_iff)
  

subsection \<open>HandleIOPair\<close>


definition handle_io_pair :: "bool \<Rightarrow> bool \<Rightarrow> (('a::linorder,'b::linorder,'c::linorder) fsm \<Rightarrow>
                                            ('a,'b,'c) state_cover_assignment \<Rightarrow>
                                            ('b\<times>'c) prefix_tree \<Rightarrow> 
                                            'd \<Rightarrow>
                                            ('d \<Rightarrow> ('b\<times>'c) list \<Rightarrow> 'd) \<Rightarrow> 
                                            ('d \<Rightarrow> ('b\<times>'c) list \<Rightarrow> ('b\<times>'c) list list) \<Rightarrow> 
                                            'a \<Rightarrow> 'b \<Rightarrow> 'c \<Rightarrow>  
                                            (('b\<times>'c) prefix_tree \<times> 'd))" where
  "handle_io_pair completeInputTraces useInputHeuristic M V T G cg_insert cg_lookup q x y = 
      distribute_extension M T G cg_lookup cg_insert (V q) [(x,y)] completeInputTraces (if useInputHeuristic then append_heuristic_input M else append_heuristic_io)"
    
lemma handle_io_pair_verifies_io_pair : "verifies_io_pair (handle_io_pair b c) M1 M2 cg_lookup cg_insert"
proof -
  
  have *:"\<And> (M::('a::linorder,'b::linorder,'c::linorder) fsm) V T (G::'d) cg_insert cg_lookup q x y . set T \<subseteq> set (fst (handle_io_pair b c M V T G cg_insert cg_lookup q x y))"
    using distribute_extension_subset unfolding handle_io_pair_def
    by metis 

  have ***:"\<And> (M::('a::linorder,'b::linorder,'c::linorder) fsm) V T (G::'d) cg_insert cg_lookup q x y . finite_tree T \<longrightarrow> finite_tree (fst (handle_io_pair b c M V T G cg_insert cg_lookup q x y))"
    using distribute_extension_finite unfolding handle_io_pair_def
    by metis 

  have **:"\<And> (M1::('a::linorder,'b::linorder,'c::linorder) fsm) V T (G::'d) cg_insert cg_lookup q x y.
        observable M1 \<Longrightarrow>
        observable M2 \<Longrightarrow>
        minimal M1 \<Longrightarrow>
        minimal M2 \<Longrightarrow>
        FSM.inputs M2 = FSM.inputs M1 \<Longrightarrow>
        FSM.outputs M2 = FSM.outputs M1 \<Longrightarrow>
        is_state_cover_assignment M1 V \<Longrightarrow>
        L M1 \<inter> V ` reachable_states M1 = L M2 \<inter> V ` reachable_states M1 \<Longrightarrow>
        q \<in> reachable_states M1 \<Longrightarrow>
        x \<in> inputs M1 \<Longrightarrow>
        y \<in> outputs M1 \<Longrightarrow> 
        convergence_graph_lookup_invar M1 M2 cg_lookup G \<Longrightarrow>
        convergence_graph_insert_invar M1 M2 cg_lookup cg_insert \<Longrightarrow>
        L M1 \<inter> set (fst (handle_io_pair b c M1 V T G cg_insert cg_lookup q x y)) = L M2 \<inter> set (fst (handle_io_pair b c M1 V T G cg_insert cg_lookup q x y)) \<Longrightarrow>
        (\<exists> \<alpha> . 
             converge M1 \<alpha> (V q) \<and> 
             converge M2 \<alpha> (V q) \<and>
             \<alpha> \<in> set (fst (handle_io_pair b c M1 V T G cg_insert cg_lookup q x y)) \<and>
             \<alpha>@[(x,y)] \<in> set (fst (handle_io_pair b c M1 V T G cg_insert cg_lookup q x y)))
        \<and> convergence_graph_lookup_invar M1 M2 cg_lookup (snd (handle_io_pair b c M1 V T G cg_insert cg_lookup q x y))"
  proof -
    fix M1 :: "('a::linorder,'b::linorder,'c::linorder) fsm"
    fix G :: 'd
    fix V T cg_insert cg_lookup q x y
    assume a01: "observable M1"
    assume a02: "observable M2"
    assume a03: "minimal M1"
    assume a04: "minimal M2"
    assume a05: "FSM.inputs M2 = FSM.inputs M1"
    assume a06: "FSM.outputs M2 = FSM.outputs M1"
    assume a07: "is_state_cover_assignment M1 V"
    assume a09: "L M1 \<inter> V ` reachable_states M1 = L M2 \<inter> V ` reachable_states M1"
    assume a10: "q \<in> reachable_states M1"
    assume a11: "x \<in> inputs M1"
    assume a12: "y \<in> outputs M1"
    assume a13: "convergence_graph_lookup_invar M1 M2 cg_lookup G"
    assume a14: "convergence_graph_insert_invar M1 M2 cg_lookup cg_insert"
    assume a15: "L M1 \<inter> set (fst (handle_io_pair b c M1 V T G cg_insert cg_lookup q x y)) = L M2 \<inter> set (fst (handle_io_pair b c M1 V T G cg_insert cg_lookup q x y))"

    let ?heuristic = "(if c then append_heuristic_input M1 else append_heuristic_io)"

    have d1: "V q \<in> L M1"
      using is_state_cover_assignment_language[OF a07 a10] by auto
    have d2: "V q \<in> L M2"
      using is_state_cover_assignment_language[OF a07 a10]
      using a09 a10 by auto 

    have d3: "L M1 \<inter> Prefix_Tree.set (fst (distribute_extension M1 T G cg_lookup cg_insert (V q) [(x,y)] b ?heuristic)) = L M2 \<inter> Prefix_Tree.set (fst (distribute_extension M1 T G cg_lookup cg_insert (V q) [(x,y)] b ?heuristic))"
      using a15 unfolding handle_io_pair_def .

    have d4: "(\<And>T w u' uBest lBest. fst (?heuristic T w (uBest, lBest) u') \<in> {u', uBest})"
      using append_heuristic_input_in[of M1] append_heuristic_io_in
      by fastforce

    show "(\<exists> \<alpha> . 
             converge M1 \<alpha> (V q) \<and> 
             converge M2 \<alpha> (V q) \<and>
             \<alpha> \<in> set (fst (handle_io_pair b c M1 V T G cg_insert cg_lookup q x y)) \<and>
             \<alpha>@[(x,y)] \<in> set (fst (handle_io_pair b c M1 V T G cg_insert cg_lookup q x y)))
        \<and> convergence_graph_lookup_invar M1 M2 cg_lookup (snd (handle_io_pair b c M1 V T G cg_insert cg_lookup q x y))"
      using distribute_extension_adds_sequence[OF a01 a03 d1 d2 a13 a14 d3 d4]
      unfolding handle_io_pair_def
      by (metis converge_sym set_prefix) 
  qed

  show ?thesis
    unfolding verifies_io_pair_def
    using * *** ** by presburger
qed

lemma handle_io_pair_handles_io_pair : "handles_io_pair (handle_io_pair b c) M1 M2 cg_lookup cg_insert"
  using verifies_io_pair_handled[OF handle_io_pair_verifies_io_pair] .



subsection \<open>HandleStateCover\<close>

subsubsection \<open>Dynamic\<close>


fun handle_state_cover_dynamic :: "bool \<Rightarrow> 
                                  bool \<Rightarrow>
                                  ('a \<Rightarrow> 'a \<Rightarrow> ('b\<times>'c) list) \<Rightarrow>
                                  ('a::linorder,'b::linorder,'c::linorder) fsm \<Rightarrow>
                                  ('a,'b,'c) state_cover_assignment \<Rightarrow>
                                  (('a,'b,'c) fsm \<Rightarrow> ('b\<times>'c) prefix_tree \<Rightarrow> 'd) \<Rightarrow> 
                                  ('d \<Rightarrow> ('b\<times>'c) list \<Rightarrow> 'd) \<Rightarrow> 
                                  ('d \<Rightarrow> ('b\<times>'c) list \<Rightarrow> ('b\<times>'c) list list) \<Rightarrow> 
                                  (('b\<times>'c) prefix_tree \<times> 'd)" 
  where
  "handle_state_cover_dynamic completeInputTraces useInputHeuristic get_distinguishing_trace M V cg_initial cg_insert cg_lookup  = 
    (let
      k = (2 * size M);
      heuristic = (if useInputHeuristic then append_heuristic_input M else append_heuristic_io);
      rstates = reachable_states_as_list M;
      T0' = from_list (map V rstates);
      T0 = (if completeInputTraces 
                then Prefix_Tree.combine T0' (from_list (concat (map (\<lambda> q . language_for_input M (initial M) (map fst (V q))) rstates))) 
                else T0');
      G0 = cg_initial M T0;
      separate_state = (\<lambda> (X,T,G) q . let u = V q;
                                          TG' = spyh_distinguish M T G cg_lookup cg_insert get_distinguishing_trace u X k completeInputTraces heuristic;
                                          X' = u#X
                                      in (X',TG'))
    in snd (foldl separate_state ([],T0,G0) rstates))"


lemma handle_state_cover_dynamic_separates_state_cover: 
  fixes M1 :: "('a::linorder,'b::linorder,'c::linorder) fsm"
  fixes M2 :: "('e,'b,'c) fsm"
  fixes cg_insert :: "('d \<Rightarrow> ('b\<times>'c) list \<Rightarrow> 'd)"
  assumes "\<And> \<alpha> \<beta> q1 q2 . q1 \<in> states M1 \<Longrightarrow> q2 \<in> states M1 \<Longrightarrow> q1 \<noteq> q2 \<Longrightarrow> distinguishes M1 q1 q2 (dist_fun q1 q2)"
  shows "separates_state_cover (handle_state_cover_dynamic b c dist_fun) M1 M2 cg_initial cg_insert cg_lookup"
proof -

  let ?f = "(handle_state_cover_dynamic b c dist_fun)"

  have "\<And> (V :: ('a,'b,'c) state_cover_assignment) .
          (V ` reachable_states M1 \<subseteq> set (fst (?f M1 V cg_initial cg_insert cg_lookup)))
            \<and> finite_tree (fst (?f M1 V cg_initial cg_insert cg_lookup))
            \<and> (observable M1 \<longrightarrow>
                observable M2 \<longrightarrow>
                minimal M1 \<longrightarrow>
                minimal M2 \<longrightarrow>
                inputs M2 = inputs M1 \<longrightarrow>
                outputs M2 = outputs M1 \<longrightarrow>
                is_state_cover_assignment M1 V \<longrightarrow>
                convergence_graph_insert_invar M1 M2 cg_lookup cg_insert \<longrightarrow>
                convergence_graph_initial_invar M1 M2 cg_lookup cg_initial \<longrightarrow>
                L M1 \<inter> set (fst (?f M1 V cg_initial cg_insert cg_lookup)) = L M2 \<inter> set (fst (?f M1 V cg_initial cg_insert cg_lookup)) \<longrightarrow>
                (preserves_divergence M1 M2 (V ` reachable_states M1)
                \<and> convergence_graph_lookup_invar M1 M2 cg_lookup (snd (?f M1 V cg_initial cg_insert cg_lookup))))" (is "\<And> V . ?P V")
  proof -
    fix V :: "('a,'b,'c) state_cover_assignment"

    define k where "k = 2 * size M1"
    define heuristic where "heuristic = (if c then append_heuristic_input M1 else append_heuristic_io)"
    define separate_state where "separate_state = (\<lambda> (X,T,G::'d) q . let u = V q;
                                          TG' = spyh_distinguish M1 T G cg_lookup cg_insert dist_fun u X k b heuristic;
                                          X' = u#X
                                      in (X',TG'))"
    define rstates where "rstates = reachable_states_as_list M1"
    define T0' where "T0' = from_list (map V rstates)"
    define T0 where "T0 = (if b 
                then Prefix_Tree.combine T0' (from_list (concat (map (\<lambda> q . language_for_input M1 (initial M1) (map fst (V q))) rstates))) 
                else T0')"
    define G0 where "G0 = cg_initial M1 T0"
    
    have *:"(?f M1 V cg_initial cg_insert cg_lookup) = snd (foldl separate_state ([],T0,G0) rstates)"
      unfolding k_def separate_state_def rstates_def heuristic_def T0'_def T0_def G0_def handle_state_cover_dynamic.simps Let_def
      by simp

    have separate_state_subset : "\<And> q X T G . set T \<subseteq> set (fst (snd (separate_state (X,T,G) q)))"
      using spyh_distinguish_subset
      unfolding separate_state_def case_prod_conv Let_def snd_conv
      by metis
    then have "set T0 \<subseteq> set (fst (?f M1 V cg_initial cg_insert cg_lookup))"
      unfolding *
      by (induction rstates rule: rev_induct; auto; metis (mono_tags, opaque_lifting) Collect_mono_iff prod.exhaust_sel)
    moreover have "set T0' \<subseteq> set T0"
      unfolding T0_def using combine_set by auto
    moreover have "V ` reachable_states M1 \<subseteq> set T0'"
      unfolding T0'_def rstates_def using from_list_subset
      by (metis image_set reachable_states_as_list_set) 
    ultimately have p1: "V ` reachable_states M1 \<subseteq> set (fst (?f M1 V cg_initial cg_insert cg_lookup))"
      by blast

    have "finite_tree T0'"
      unfolding T0'_def using from_list_finite_tree by auto
    then have "finite_tree T0"
      unfolding T0_def using combine_finite_tree[OF _ from_list_finite_tree]
      by auto 

    have separate_state_finite : "\<And> q X T G . finite_tree T \<Longrightarrow> finite_tree (fst (snd (separate_state (X,T,G) q)))"
      using spyh_distinguish_finite
      unfolding separate_state_def case_prod_conv Let_def snd_conv
      by metis
    have p2: "finite_tree (fst (?f M1 V cg_initial cg_insert cg_lookup))"
      unfolding *  
    proof (induction rstates rule: rev_induct)
      case Nil
      show ?case using \<open>finite_tree T0\<close> by auto
    next
      case (snoc a rstates) 
      have *:"foldl separate_state ([], T0, G0) (rstates@[a]) = separate_state (foldl separate_state ([], T0, G0) rstates) a"
        by auto
      show ?case 
        using separate_state_finite[OF snoc.IH]
        unfolding *
        by (metis prod.collapse)  
    qed

    have "\<And> q X T G . fst (separate_state (X,T,G) q) = V q # X"
      unfolding separate_state_def case_prod_conv Let_def fst_conv by blast

    have heuristic_prop: "(\<And>T w u' uBest lBest. fst (heuristic T w (uBest, lBest) u') \<in> {u', uBest})"
      unfolding heuristic_def
      using append_heuristic_input_in[of M1] append_heuristic_io_in
      by fastforce
      

    have p3: "observable M1 \<Longrightarrow>
                observable M2 \<Longrightarrow>
                minimal M1 \<Longrightarrow>
                minimal M2 \<Longrightarrow>
                inputs M2 = inputs M1 \<Longrightarrow>
                outputs M2 = outputs M1 \<Longrightarrow>
                is_state_cover_assignment M1 V \<Longrightarrow>
                convergence_graph_insert_invar M1 M2 cg_lookup cg_insert \<Longrightarrow>
                convergence_graph_initial_invar M1 M2 cg_lookup cg_initial \<Longrightarrow>
                L M1 \<inter> set (fst (?f M1 V cg_initial cg_insert cg_lookup)) = L M2 \<inter> set (fst (?f M1 V cg_initial cg_insert cg_lookup)) \<Longrightarrow>
                (preserves_divergence M1 M2 (V ` reachable_states M1)
                \<and> convergence_graph_lookup_invar M1 M2 cg_lookup (snd (?f M1 V cg_initial cg_insert cg_lookup)))"
    proof -
      assume a0: "observable M1"
         and a1: "observable M2"
         and a2: "minimal M1"
         and a3: "minimal M2"
         and a4: "inputs M2 = inputs M1"
         and a5: "outputs M2 = outputs M1"
         and a6: "is_state_cover_assignment M1 V"
         and a7: "convergence_graph_insert_invar M1 M2 cg_lookup cg_insert"
         and a8: "convergence_graph_initial_invar M1 M2 cg_lookup cg_initial"
         and a9: "L M1 \<inter> set (fst (?f M1 V cg_initial cg_insert cg_lookup)) = L M2 \<inter> set (fst (?f M1 V cg_initial cg_insert cg_lookup))"

      have "\<And> rstates . (list.set (fst (foldl separate_state ([],T0,G0) rstates))) = V ` list.set rstates"
      proof -
        fix rstates show "(list.set (fst (foldl separate_state ([],T0,G0) rstates))) = V ` list.set rstates"
        proof (induction rstates rule: rev_induct)
          case Nil
          then show ?case by auto
        next
          case (snoc a rstates)
          have *:"(foldl separate_state ([], T0, G0) (rstates@[a])) = separate_state (foldl separate_state ([], T0, G0) rstates) a"
            by auto
          have **: "\<And> q XTG . fst (separate_state XTG q) = V q # fst XTG"
            using \<open>\<And> q X T G . fst (separate_state (X,T,G) q) = V q # X\<close> by auto
  
          show ?case
            unfolding * **
            using snoc by auto
        qed
      qed
      then have "(list.set (fst (foldl separate_state ([],T0,G0) rstates))) = V ` reachable_states M1"
        by (metis reachable_states_as_list_set rstates_def)

      have "\<And> q . q \<in> reachable_states M1 \<Longrightarrow> V q \<in> set T0"
        using \<open>Prefix_Tree.set T0' \<subseteq> Prefix_Tree.set T0\<close> \<open>V ` reachable_states M1 \<subseteq> Prefix_Tree.set T0'\<close> by auto


      have "list.set rstates \<subseteq> reachable_states M1"
        unfolding rstates_def
        using reachable_states_as_list_set by auto 
      moreover have "L M1 \<inter> set (fst (snd (foldl separate_state ([],T0,G0) rstates))) = L M2 \<inter> set (fst (snd (foldl separate_state ([],T0,G0) rstates)))"
        using "*" a9 by presburger
      ultimately have "preserves_divergence M1 M2 (list.set (fst (foldl separate_state ([],T0,G0) rstates)))
                        \<and> convergence_graph_lookup_invar M1 M2 cg_lookup (snd (snd (foldl separate_state ([],T0,G0) rstates)))"
      proof (induction rstates rule: rev_induct)
        case Nil
        have "L M1 \<inter> set T0 = L M2 \<inter> set T0"
          using a9
          using \<open>set T0 \<subseteq> set (fst (handle_state_cover_dynamic b c dist_fun M1 V cg_initial cg_insert cg_lookup))\<close> by blast 
        then have "convergence_graph_lookup_invar M1 M2 cg_lookup G0"
          using a8 \<open>finite_tree T0\<close>
          unfolding G0_def convergence_graph_initial_invar_def
          by blast
        then show ?case by auto  
      next
        case (snoc q rstates)

        obtain X' T' G' where "foldl separate_state ([],T0,G0) rstates = (X',T',G')"
          using prod_cases3 by blast
        then have "T' = fst (snd (foldl separate_state ([],T0,G0) rstates))"  
             and  "X' = fst (foldl separate_state ([],T0,G0) rstates)"
          by auto

        define u where "u = V q"
        define TG'' where "TG'' = spyh_distinguish M1 T' G' cg_lookup cg_insert dist_fun u X' k b heuristic"
        define X'' where "X'' = u#X'"

        have "foldl separate_state ([], T0, G0) (rstates@[q]) = separate_state (X',T',G') q"
          using \<open>foldl separate_state ([],T0,G0) rstates = (X',T',G')\<close>  by auto
        also have "separate_state (X',T',G') q = (X'',TG'')"
          unfolding separate_state_def u_def TG''_def X''_def case_prod_conv Let_def
          by auto        
        finally have "foldl separate_state ([], T0, G0) (rstates@[q]) = (X'',TG'')" .


        have "set T' \<subseteq> set (fst (snd (foldl separate_state ([],T0,G0) (rstates@[q]))))"
          using separate_state_subset
          unfolding \<open>foldl separate_state ([], T0, G0) (rstates@[q]) = separate_state (X',T',G') q\<close> by simp
        then have "L M1 \<inter> set T' = L M2 \<inter> set T'"
          using snoc.prems(2) by blast

        then have "preserves_divergence M1 M2 (list.set X')"
        and       "convergence_graph_lookup_invar M1 M2 cg_lookup G'"
          using snoc unfolding \<open>foldl separate_state ([],T0,G0) rstates = (X',T',G')\<close> 
          by auto

        have "set T0 \<subseteq> set T'"
          using separate_state_subset 
          unfolding \<open>T' = fst (snd (foldl separate_state ([],T0,G0) rstates))\<close>
          by (induction rstates rule: rev_induct; auto; metis (mono_tags, opaque_lifting) Collect_mono_iff prod.collapse) 

        have "V q \<in> set T0"
          using snoc.prems
          using \<open>\<And>q. q \<in> reachable_states M1 \<Longrightarrow> V q \<in> Prefix_Tree.set T0\<close> by auto 
        then have "V q \<in> set T'" 
          using \<open>set T0 \<subseteq> set T'\<close> by auto 
        moreover have "V q \<in> L M1"
        proof -
          have "q \<in> reachable_states M1"
            using snoc.prems(1) by auto
          then show ?thesis
            using is_state_cover_assignment_language[OF a6] by blast
        qed 
        ultimately have "V q \<in> L M2"
          using \<open>L M1 \<inter> set T' = L M2 \<inter> set T'\<close> by blast

        
        have "list.set X' = V ` list.set rstates"
          unfolding \<open>X' = fst (foldl separate_state ([],T0,G0) rstates)\<close>
          using \<open>\<And> rstates . (list.set (fst (foldl separate_state ([],T0,G0) rstates))) = V ` list.set rstates\<close>
          by blast
        moreover have "list.set rstates \<subseteq> reachable_states M1"
          using snoc.prems(1) by auto
        ultimately have "list.set X' \<subseteq> set T'"
          using \<open>set T0 \<subseteq> set T'\<close>
          using \<open>\<And>q. q \<in> reachable_states M1 \<Longrightarrow> V q \<in> Prefix_Tree.set T0\<close> by auto 
        moreover have "list.set X' \<subseteq> L M1"
          using \<open>list.set X' = V ` list.set rstates\<close> \<open>list.set rstates \<subseteq> reachable_states M1\<close> a6
          by (metis dual_order.trans image_mono state_cover_assignment_language) 
        ultimately have "list.set X' \<subseteq> L M2"
          using \<open>L M1 \<inter> set T' = L M2 \<inter> set T'\<close> by blast

        have *: "L M1 \<inter> set (fst (spyh_distinguish M1 T' G' cg_lookup cg_insert dist_fun (V q) X' k b heuristic)) =
                 L M2 \<inter> set (fst (spyh_distinguish M1 T' G' cg_lookup cg_insert dist_fun (V q) X' k b heuristic))"
          using snoc.prems(2) TG''_def \<open>foldl separate_state ([], T0, G0) (rstates@[q]) = separate_state (X', T', G') q\<close> \<open>separate_state (X', T', G') q = (X'', TG'')\<close> u_def by auto
          

        have "preserves_divergence M1 M2 (Set.insert (V q) (list.set X'))"
          using spyh_distinguish_preserves_divergence[OF a0 a1 a2 a3 \<open>V q \<in> L M1\<close> \<open>V q \<in> L M2\<close> assms(1) \<open>convergence_graph_lookup_invar M1 M2 cg_lookup G'\<close> a7 \<open>list.set X' \<subseteq> L M1\<close> \<open>list.set X' \<subseteq> L M2\<close> * heuristic_prop \<open>preserves_divergence M1 M2 (list.set X')\<close>]
          by presburger
        then have "preserves_divergence M1 M2 (list.set X'')"
          by (metis X''_def list.simps(15) u_def)

        moreover have "convergence_graph_lookup_invar M1 M2 cg_lookup (snd TG'')"
          using spyh_distinguish_establishes_divergence(2)[OF a0 a1 a2 a3 \<open>V q \<in> L M1\<close> \<open>V q \<in> L M2\<close> assms(1) \<open>convergence_graph_lookup_invar M1 M2 cg_lookup G'\<close> a7 \<open>list.set X' \<subseteq> L M1\<close> \<open>list.set X' \<subseteq> L M2\<close> * heuristic_prop ]
          unfolding u_def[symmetric] TG''_def[symmetric]
          by presburger
        ultimately show ?case 
          unfolding \<open>foldl separate_state ([], T0, G0) (rstates@[q]) = (X'',TG'')\<close> snd_conv fst_conv
          by blast
      qed
      then show ?thesis
        unfolding \<open>(list.set (fst (foldl separate_state ([],T0,G0) rstates))) = V ` reachable_states M1\<close>
        unfolding * .
    qed

    show "?P V"
      using p1 p2 p3 by blast
  qed

  then show ?thesis 
    unfolding separates_state_cover_def by blast
qed



subsubsection \<open>Static\<close>


fun handle_state_cover_static :: "(nat \<Rightarrow> 'a \<Rightarrow> ('b\<times>'c) prefix_tree) \<Rightarrow>
                                  ('a::linorder,'b::linorder,'c::linorder) fsm \<Rightarrow> 
                                  ('a,'b,'c) state_cover_assignment \<Rightarrow> 
                                  (('a,'b,'c) fsm \<Rightarrow> ('b\<times>'c) prefix_tree \<Rightarrow> 'd) \<Rightarrow> 
                                  ('d \<Rightarrow> ('b\<times>'c) list \<Rightarrow> 'd) \<Rightarrow> 
                                  ('d \<Rightarrow> ('b\<times>'c) list \<Rightarrow> ('b\<times>'c) list list) \<Rightarrow> 
                                  (('b\<times>'c) prefix_tree \<times> 'd)" 
  where
  "handle_state_cover_static dist_set M V cg_initial cg_insert cg_lookup  = 
    (let
      separate_state = (\<lambda> T q . combine_after T (V q) (dist_set 0 q));
      T' = foldl separate_state empty (reachable_states_as_list M);
      G' = cg_initial M T'
    in (T',G'))"





lemma handle_state_cover_static_applies_dist_sets:
  assumes "q \<in> reachable_states M1"
  shows "set (dist_fun 0 q) \<subseteq> set (after (fst (handle_state_cover_static dist_fun M1 V cg_initial cg_insert cg_lookup)) (V q))"
  (is "set (dist_fun 0 q) \<subseteq> set (after ?T (V q))")
proof -

  define k where "k = 2 * size M1"
  define separate_state where "separate_state = (\<lambda> T q . combine_after T (V q) (dist_fun 0 q))"
  define rstates where "rstates = reachable_states_as_list M1"
  define T where "T = foldl separate_state empty rstates"
  define G where "G = cg_initial M1 T"
  
  have *:"?T = T"
    unfolding k_def separate_state_def rstates_def T_def G_def handle_state_cover_static.simps Let_def
    by simp

  have separate_state_subset : "\<And> q T . set T \<subseteq> set (separate_state T q)"
    unfolding separate_state_def combine_after_set 
    by blast

  have "\<And> q . q \<in> list.set rstates \<Longrightarrow> set (dist_fun 0 q) \<subseteq> set (after T (V q))"
  proof -
    fix q assume "q \<in> list.set rstates"
    then show "set (dist_fun 0 q) \<subseteq> set (after T (V q))"
      unfolding T_def proof (induction rstates arbitrary: q rule: rev_induct )
      case Nil
      then show ?case by auto
    next
      case (snoc a rstates)
      have *: "foldl separate_state empty (rstates@[a]) = separate_state (foldl separate_state empty rstates) a"
        by auto
      show ?case proof (cases "q = a")
        case True
        show ?thesis 
          unfolding True using separate_state_def combine_after_after_subset by force
      next
        case False
        then have \<open>q \<in> list.set rstates\<close> using snoc.prems by auto
        then have "set (dist_fun 0 q) \<subseteq> set (after (foldl separate_state empty rstates) (V q))"
          using snoc.IH by auto
        moreover have "set (after (foldl separate_state empty rstates) (V q)) \<subseteq> set (after (foldl separate_state empty (rstates@[a])) (V q))"
          unfolding *
          using subset_after_subset[OF separate_state_subset] by blast
        ultimately show ?thesis by blast
      qed
    qed
  qed

  then show ?thesis
    unfolding rstates_def \<open>?T = T\<close> using assms
    using reachable_states_as_list_set by auto 
qed



lemma handle_state_cover_static_separates_state_cover: 
  fixes M1 :: "('a::linorder,'b::linorder,'c::linorder) fsm"
  fixes M2 :: "('e,'b,'c) fsm"
  fixes cg_insert :: "('d \<Rightarrow> ('b\<times>'c) list \<Rightarrow> 'd)"
  assumes "observable M1 \<Longrightarrow> minimal M1 \<Longrightarrow> (\<And> q1 q2 . q1 \<in> states M1 \<Longrightarrow> q2 \<in> states M1 \<Longrightarrow> q1 \<noteq> q2 \<Longrightarrow> \<exists> io . \<forall> k1 k2 . io \<in> set (dist_fun k1 q1) \<inter> set (dist_fun k2 q2) \<and> distinguishes M1 q1 q2 io)"   
  and     "\<And> k q . q \<in> states M1 \<Longrightarrow> finite_tree (dist_fun k q)"
shows "separates_state_cover (handle_state_cover_static dist_fun) M1 M2 cg_initial cg_insert cg_lookup"
proof -

  let ?f = "(handle_state_cover_static dist_fun)"

  have "\<And> (V :: ('a,'b,'c) state_cover_assignment) .
          (V ` reachable_states M1 \<subseteq> set (fst (?f M1 V cg_initial cg_insert cg_lookup)))
            \<and> finite_tree (fst (?f M1 V cg_initial cg_insert cg_lookup))
            \<and> (observable M1 \<longrightarrow>
                observable M2 \<longrightarrow>
                minimal M1 \<longrightarrow>
                minimal M2 \<longrightarrow>
                inputs M2 = inputs M1 \<longrightarrow>
                outputs M2 = outputs M1 \<longrightarrow>
                is_state_cover_assignment M1 V \<longrightarrow>
                convergence_graph_insert_invar M1 M2 cg_lookup cg_insert \<longrightarrow>
                convergence_graph_initial_invar M1 M2 cg_lookup cg_initial \<longrightarrow>
                L M1 \<inter> set (fst (?f M1 V cg_initial cg_insert cg_lookup)) = L M2 \<inter> set (fst (?f M1 V cg_initial cg_insert cg_lookup)) \<longrightarrow>
                (preserves_divergence M1 M2 (V ` reachable_states M1)
                \<and> convergence_graph_lookup_invar M1 M2 cg_lookup (snd (?f M1 V cg_initial cg_insert cg_lookup))))" (is "\<And> V . ?P V")
  proof -
    fix V :: "('a,'b,'c) state_cover_assignment"

    define k where "k = 2 * size M1"
    define separate_state where "separate_state = (\<lambda> T q . combine_after T (V q) (dist_fun 0 q))"
    define rstates where "rstates = reachable_states_as_list M1"
    define T where "T = foldl separate_state empty rstates"
    define G where "G = cg_initial M1 T"
    
    have *:"(?f M1 V cg_initial cg_insert cg_lookup) = (T,G)"
      unfolding k_def separate_state_def rstates_def T_def G_def handle_state_cover_static.simps Let_def
      by simp

    have separate_state_subset : "\<And> q T . set T \<subseteq> set (separate_state T q)"
      unfolding separate_state_def combine_after_set 
      by blast

    have "V ` (list.set rstates) \<subseteq> set T"
      unfolding T_def proof (induction rstates rule: rev_induct)
      case Nil
      then show ?case by auto
    next
      case (snoc a rstates)
      have *: "foldl separate_state empty (rstates@[a]) = separate_state (foldl separate_state empty rstates) a"
        by auto

      have "V ` (list.set rstates) \<subseteq> set (foldl separate_state empty (rstates@[a]))"
        using snoc separate_state_subset by auto
      moreover have "V a \<in> set (separate_state (foldl separate_state empty rstates) a)"
        unfolding separate_state_def combine_after_set
        by simp 
      ultimately show ?case 
        unfolding * by auto
    qed
    then have p1: "(V ` reachable_states M1 \<subseteq> set (fst (?f M1 V cg_initial cg_insert cg_lookup)))"
      unfolding rstates_def *
      using reachable_states_as_list_set by auto 

    have separate_state_finite : "\<And> q X T G . q \<in> states M1 \<Longrightarrow> finite_tree T \<Longrightarrow> finite_tree (separate_state T q)"
      unfolding separate_state_def using combine_after_finite_tree[OF _ assms(2)]
      by metis
    moreover have "\<And> q . q \<in> list.set rstates \<Longrightarrow> q \<in> states M1"
      unfolding rstates_def
      by (metis reachable_state_is_state reachable_states_as_list_set) 
    ultimately have p2: "finite_tree (fst (?f M1 V cg_initial cg_insert cg_lookup))"
      unfolding *  fst_conv T_def using empty_finite_tree
      by (induction rstates rule: rev_induct; auto) 

    have p3: "observable M1 \<Longrightarrow>
                observable M2 \<Longrightarrow>
                minimal M1 \<Longrightarrow>
                minimal M2 \<Longrightarrow>
                inputs M2 = inputs M1 \<Longrightarrow>
                outputs M2 = outputs M1 \<Longrightarrow>
                is_state_cover_assignment M1 V \<Longrightarrow>
                convergence_graph_insert_invar M1 M2 cg_lookup cg_insert \<Longrightarrow>
                convergence_graph_initial_invar M1 M2 cg_lookup cg_initial \<Longrightarrow>
                L M1 \<inter> set (fst (?f M1 V cg_initial cg_insert cg_lookup)) = L M2 \<inter> set (fst (?f M1 V cg_initial cg_insert cg_lookup)) \<Longrightarrow>
                (preserves_divergence M1 M2 (V ` reachable_states M1)
                \<and> convergence_graph_lookup_invar M1 M2 cg_lookup (snd (?f M1 V cg_initial cg_insert cg_lookup)))"
    proof -
      assume a0: "observable M1"
         and a1: "observable M2"
         and a2: "minimal M1"
         and a3: "minimal M2"
         and a4: "inputs M2 = inputs M1"
         and a5: "outputs M2 = outputs M1"
         and a6: "is_state_cover_assignment M1 V"
         and a7: "convergence_graph_insert_invar M1 M2 cg_lookup cg_insert"
         and a8: "convergence_graph_initial_invar M1 M2 cg_lookup cg_initial"
         and a9: "L M1 \<inter> set (fst (?f M1 V cg_initial cg_insert cg_lookup)) = L M2 \<inter> set (fst (?f M1 V cg_initial cg_insert cg_lookup))"

      have "L M1 \<inter> set T = L M2 \<inter> set T"
        using a9 unfolding * by auto
      then have "convergence_graph_lookup_invar M1 M2 cg_lookup (snd (?f M1 V cg_initial cg_insert cg_lookup))"
        using a8 p2
        unfolding * fst_conv snd_conv G_def convergence_graph_initial_invar_def
        by blast 
      moreover have "preserves_divergence M1 M2 (V ` reachable_states M1)"
      proof -
        have "\<And> u v . u\<in>L M1 \<inter> V ` reachable_states M1 \<Longrightarrow> v\<in>L M1 \<inter> V ` reachable_states M1 \<Longrightarrow> \<not> converge M1 u v \<Longrightarrow> \<not> converge M2 u v"
        proof -
          fix u v assume "u\<in>L M1 \<inter> V ` reachable_states M1" and "v\<in>L M1 \<inter> V ` reachable_states M1" and "\<not> converge M1 u v"
          then obtain qv qu where "qu \<in> reachable_states M1" and "u = V qu"
                                  "qv \<in> reachable_states M1" and "v = V qv"
            by auto
          then have "u \<in> L M1" and "v \<in> L M1"
            using a6 by (meson is_state_cover_assignment_language)+ 
          then have "qu \<noteq> qv" 
            using a6 \<open>\<not> converge M1 u v\<close>
            using \<open>u = V qu\<close> \<open>v = V qv\<close> a0 a2 convergence_minimal by blast 
          moreover have "qu \<in> states M1" and "qv \<in> states M1"
            using \<open>qu \<in> reachable_states M1\<close> \<open>qv \<in> reachable_states M1\<close>
            by (simp add: reachable_state_is_state)+
          ultimately obtain w where "distinguishes M1 qu qv w" and "w \<in> set (dist_fun 0 qu)" and "w \<in> set (dist_fun 0 qv)"
            using assms(1)[OF a0 a2]
            by (metis Int_iff) 
          then have "w \<noteq> []"
            by (meson \<open>qu \<in> FSM.states M1\<close> \<open>qv \<in> FSM.states M1\<close> distinguishes_not_Nil) 
          
          have "(u@w \<in> L M1) \<noteq> (v@w \<in> L M1)"
            unfolding \<open>u = V qu\<close> \<open>v = V qv\<close>
            using state_cover_assignment_after[OF a0 a6 \<open>qu \<in> reachable_states M1\<close>]
            using state_cover_assignment_after[OF a0 a6 \<open>qv \<in> reachable_states M1\<close>]
            by (metis \<open>distinguishes M1 qu qv w\<close> a0 after_distinguishes_language)
          moreover have "u@w \<in> set T" 
            using handle_state_cover_static_applies_dist_sets[OF \<open>qu \<in> reachable_states M1\<close>, of dist_fun V cg_initial cg_insert cg_lookup] \<open>w \<in> set (dist_fun 0 qu)\<close> \<open>w \<noteq> []\<close>
            unfolding * fst_conv after_set \<open>u = V qu\<close> by auto
          moreover have "v@w \<in> set T" 
            using handle_state_cover_static_applies_dist_sets[OF \<open>qv \<in> reachable_states M1\<close>, of dist_fun V cg_initial cg_insert cg_lookup] \<open>w \<in> set (dist_fun 0 qv)\<close> \<open>w \<noteq> []\<close>
            unfolding * fst_conv after_set \<open>v = V qv\<close> by auto
          ultimately have "(u@w \<in> L M2) \<noteq> (v@w \<in> L M2)"
            using \<open>L M1 \<inter> set T = L M2 \<inter> set T\<close>
            by blast 
          then show "\<not> converge M2 u v"
            using a1 converge_append_language_iff by blast            
        qed
        then show ?thesis
          unfolding preserves_divergence.simps by blast
      qed
      ultimately show ?thesis
        by blast
    qed

    show "?P V"
      using p1 p2 p3 by blast
  qed

  then show ?thesis 
    unfolding separates_state_cover_def by blast
qed




subsection \<open>Establishing Convergence of Traces\<close>

subsubsection \<open>Dynamic\<close>

fun distinguish_from_set :: "('a::linorder,'b::linorder,'c::linorder) fsm \<Rightarrow> ('a,'b,'c) state_cover_assignment \<Rightarrow> ('b\<times>'c) prefix_tree \<Rightarrow> 'd \<Rightarrow> ('d \<Rightarrow> ('b\<times>'c) list \<Rightarrow> ('b\<times>'c) list list) \<Rightarrow> ('d \<Rightarrow> ('b\<times>'c) list \<Rightarrow> 'd) \<Rightarrow> ('a \<Rightarrow> 'a \<Rightarrow> ('b\<times>'c) list) \<Rightarrow> ('b\<times>'c) list \<Rightarrow> ('b\<times>'c) list \<Rightarrow> ('b\<times>'c) list list \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> bool \<Rightarrow> (('b\<times>'c) prefix_tree \<Rightarrow> ('b\<times>'c) list \<Rightarrow> (('b\<times>'c) list \<times> int) \<Rightarrow> ('b\<times>'c) list \<Rightarrow> (('b\<times>'c) list \<times> int)) \<Rightarrow> bool \<Rightarrow> (('b\<times>'c) prefix_tree \<times> 'd)" where
  "distinguish_from_set M V T G cg_lookup cg_insert get_distinguishing_trace u v X k depth completeInputTraces append_heuristic u_is_v= 
    (let TG' = spyh_distinguish M T G cg_lookup cg_insert get_distinguishing_trace u X k completeInputTraces append_heuristic;
         vClass = Set.insert v (list.set (cg_lookup (snd TG') v));
         notReferenced = (\<not> u_is_v) \<and> (\<forall> q \<in> reachable_states M . V q \<notin> vClass);
         TG'' = (if notReferenced then spyh_distinguish M (fst TG') (snd TG') cg_lookup cg_insert get_distinguishing_trace v X k completeInputTraces append_heuristic
                                  else TG')
      in if depth > 0
        then let X' = if notReferenced then (v#u#X) else (u#X);
                 XY = List.product (inputs_as_list M) (outputs_as_list M);
                 handleIO = (\<lambda> (T,G) (x,y) . (let TGu = distribute_extension M T G cg_lookup cg_insert u [(x,y)] completeInputTraces append_heuristic;
                                                 TGv = if u_is_v then TGu else distribute_extension M (fst TGu) (snd TGu) cg_lookup cg_insert v [(x,y)] completeInputTraces append_heuristic
                                             in if is_in_language M (initial M) (u@[(x,y)])
                                                  then distinguish_from_set M V (fst TGv) (snd TGv) cg_lookup cg_insert get_distinguishing_trace (u@[(x,y)]) (v@[(x,y)]) X' k (depth - 1) completeInputTraces append_heuristic u_is_v
                                                  else TGv))
            in foldl handleIO TG'' XY
        else TG'')"

lemma distinguish_from_set_subset :
  "set T \<subseteq> set (fst (distinguish_from_set M V T G cg_lookup cg_insert get_distinguishing_trace u v X k depth completeInputTraces append_heuristic u_is_v))"
proof (induction depth arbitrary: T G u v X)
  case 0

  define TG' where TG': "TG' = spyh_distinguish M T G cg_lookup cg_insert get_distinguishing_trace u X k completeInputTraces append_heuristic "
  define vClass where vClass: "vClass = Set.insert v (list.set (cg_lookup (snd TG') v))"
  define notReferenced where notReferenced: "notReferenced = ((\<not> u_is_v) \<and> (\<forall> q \<in> reachable_states M . V q \<notin> vClass))"
  define TG'' where TG'': "TG'' = (if notReferenced then spyh_distinguish M (fst TG') (snd TG') cg_lookup cg_insert get_distinguishing_trace v X k completeInputTraces append_heuristic else TG')"

  have "distinguish_from_set M V T G cg_lookup cg_insert get_distinguishing_trace u v X k 0 completeInputTraces append_heuristic u_is_v = TG''"
    apply (subst distinguish_from_set.simps)
    unfolding TG' vClass notReferenced TG'' Let_def 
    by force
  moreover have "set T \<subseteq> set (fst (TG'))"
    unfolding TG'
    using spyh_distinguish_subset
    by metis
  moreover have "set (fst (TG')) \<subseteq> set (fst (TG''))"
    unfolding TG'' 
    using spyh_distinguish_subset
    by (metis (mono_tags, lifting) equalityE)
  ultimately show ?case 
    by blast
next
  case (Suc depth)

  have "(Suc depth - 1) = depth"
    by auto

  define TG' where TG': "TG' = spyh_distinguish M T G cg_lookup cg_insert get_distinguishing_trace u X k completeInputTraces append_heuristic"
  define vClass where vClass: "vClass = Set.insert v (list.set (cg_lookup (snd TG') v))"
  define notReferenced where notReferenced: "notReferenced = ((\<not> u_is_v) \<and> (\<forall> q \<in> reachable_states M . V q \<notin> vClass))"
  define TG'' where TG'': "TG'' = (if notReferenced then spyh_distinguish M (fst TG') (snd TG') cg_lookup cg_insert get_distinguishing_trace v X k completeInputTraces append_heuristic else TG')"
  define X' where X': "X' = (if notReferenced then (v#u#X) else (u#X))"
  define XY where XY: "XY = List.product (inputs_as_list M) (outputs_as_list M)"
  define handleIO where handleIO: "handleIO = (\<lambda> (T,G) (x,y) . (let TGu = distribute_extension M T G cg_lookup cg_insert u [(x,y)] completeInputTraces append_heuristic;
                                                 TGv = if u_is_v then TGu else distribute_extension M (fst TGu) (snd TGu) cg_lookup cg_insert v [(x,y)] completeInputTraces append_heuristic
                                             in if is_in_language M (initial M) (u@[(x,y)])
                                                  then distinguish_from_set M V (fst TGv) (snd TGv) cg_lookup cg_insert get_distinguishing_trace (u@[(x,y)]) (v@[(x,y)]) X' k (depth) completeInputTraces append_heuristic u_is_v
                                                  else TGv))"

  

  have "\<And> x y T G . set T \<subseteq> set (fst (handleIO (T,G) (x,y)))"
  proof -
    fix x y T G 

    define TGu where TGu: "TGu = distribute_extension M T G cg_lookup cg_insert u [(x,y)] completeInputTraces append_heuristic"
    define TGv where TGv: "TGv = (if u_is_v then TGu else distribute_extension M (fst TGu) (snd TGu) cg_lookup cg_insert v [(x,y)] completeInputTraces append_heuristic)"
    have *: "handleIO (T,G) (x,y) = (if is_in_language M (initial M) (u@[(x,y)])
                                                  then distinguish_from_set M V (fst TGv) (snd TGv) cg_lookup cg_insert get_distinguishing_trace (u@[(x,y)]) (v@[(x,y)]) X' k (depth) completeInputTraces append_heuristic u_is_v
                                                  else TGv)"
      unfolding handleIO TGu TGv case_prod_conv Let_def 
      by auto
    
    have "set T \<subseteq> set (fst TGu)"
      unfolding TGu
      using distribute_extension_subset
      by metis
    moreover have "set (fst TGu) \<subseteq> set (fst TGv)"
      unfolding TGv 
      using distribute_extension_subset by force
    ultimately have "set T \<subseteq> set (fst TGv)"
      by blast
      
    show "set T \<subseteq> set (fst (handleIO (T,G) (x,y)))"
      unfolding *
      using \<open>set T \<subseteq> set (fst TGv)\<close>
      using Suc.IH[of "fst TGv" "snd TGv" "u@[(x,y)]" "v@[(x,y)]" X'] 
      by (cases "is_in_language M (initial M) (u@[(x,y)])"; auto)
  qed
  
  have "set (fst TG'') \<subseteq> set (fst (foldl handleIO TG'' XY))"
  proof (induction XY rule: rev_induct)
    case Nil
    then show ?case by auto
  next
    case (snoc a XY)
    obtain x y where "a = (x,y)"
      using prod.exhaust by metis
    then have *: "(foldl handleIO TG'' (XY@[a])) = handleIO (fst (foldl handleIO TG'' XY),snd (foldl handleIO TG'' XY)) (x,y) "
      by auto

    show ?case 
      using snoc unfolding * 
      using \<open>\<And> x y T G . set T \<subseteq> set (fst (handleIO (T,G) (x,y)))\<close>
      by blast       
  qed
  moreover have "set T \<subseteq> set (fst TG'')"
  proof -
    have "set T \<subseteq> set (fst TG')"
      unfolding TG'
      using spyh_distinguish_subset
      by metis
    moreover have "set (fst TG') \<subseteq> set (fst TG'')"
      unfolding TG''
      using spyh_distinguish_subset
      by (metis (mono_tags, lifting) order_refl)
    ultimately show ?thesis
      by blast
  qed
  moreover have "distinguish_from_set M V T G cg_lookup cg_insert get_distinguishing_trace u v X k (Suc depth) completeInputTraces append_heuristic u_is_v = foldl handleIO TG'' XY"
    apply (subst distinguish_from_set.simps)
    unfolding TG' vClass notReferenced TG'' Let_def X' XY handleIO 
    unfolding \<open>(Suc depth - 1) = depth\<close> 
    by force

  ultimately show ?case
    by (metis (no_types, lifting) order_trans) 
qed


lemma distinguish_from_set_finite :
  fixes T :: "('b::linorder\<times>'c::linorder) prefix_tree "
  assumes "finite_tree T"
  shows "finite_tree (fst (distinguish_from_set M V T G cg_lookup cg_insert get_distinguishing_trace u v X k depth completeInputTraces append_heuristic u_is_v))"
using assms proof (induction depth arbitrary: T G u v X)
  case 0

  define TG' where TG': "TG' = spyh_distinguish M T G cg_lookup cg_insert get_distinguishing_trace u X k completeInputTraces append_heuristic"
  define vClass where vClass: "vClass = Set.insert v (list.set (cg_lookup (snd TG') v))"
  define notReferenced where notReferenced: "notReferenced = ((\<not> u_is_v) \<and> (\<forall> q \<in> reachable_states M . V q \<notin> vClass))"
  define TG'' where TG'': "TG'' = (if notReferenced then spyh_distinguish M (fst TG') (snd TG') cg_lookup cg_insert get_distinguishing_trace v X k completeInputTraces append_heuristic else TG')"

  have "finite_tree (fst (TG'))"
    unfolding TG'
    using spyh_distinguish_finite 0
    by metis
  then have "finite_tree (fst (TG''))"
    unfolding TG'' 
    using spyh_distinguish_finite[OF \<open>finite_tree (fst (TG'))\<close>, of M "snd TG'" ] 
    by auto
  moreover have "distinguish_from_set M V T G cg_lookup cg_insert get_distinguishing_trace u v X k 0 completeInputTraces append_heuristic u_is_v= TG''"
    apply (subst distinguish_from_set.simps)
    unfolding TG' vClass notReferenced TG'' Let_def 
    by force
  ultimately show ?case 
    by blast
next
  case (Suc depth)

  have "(Suc depth - 1) = depth"
    by auto

  define TG' where TG': "TG' = spyh_distinguish M T G cg_lookup cg_insert get_distinguishing_trace u X k completeInputTraces append_heuristic"
  define vClass where vClass: "vClass = Set.insert v (list.set (cg_lookup (snd TG') v))"
  define notReferenced where notReferenced: "notReferenced = ((\<not> u_is_v) \<and> (\<forall> q \<in> reachable_states M . V q \<notin> vClass))"
  define TG'' where TG'': "TG'' = (if notReferenced then spyh_distinguish M (fst TG') (snd TG') cg_lookup cg_insert get_distinguishing_trace v X k completeInputTraces append_heuristic else TG')"
  define X' where X': "X' = (if notReferenced then (v#u#X) else (u#X))"
  define XY where XY: "XY = List.product (inputs_as_list M) (outputs_as_list M)"
  define handleIO where handleIO: "handleIO = (\<lambda> (T,G) (x,y) . (let TGu = distribute_extension M T G cg_lookup cg_insert u [(x,y)] completeInputTraces append_heuristic;
                                                 TGv = if u_is_v then TGu else distribute_extension M (fst TGu) (snd TGu) cg_lookup cg_insert v [(x,y)] completeInputTraces append_heuristic
                                             in if is_in_language M (initial M) (u@[(x,y)])
                                                  then distinguish_from_set M V (fst TGv) (snd TGv) cg_lookup cg_insert get_distinguishing_trace (u@[(x,y)]) (v@[(x,y)]) X' k (depth) completeInputTraces append_heuristic u_is_v
                                                  else TGv))"

  

  have "\<And> x y T G . finite_tree T \<Longrightarrow> finite_tree (fst (handleIO (T,G) (x,y)))"
  proof -
    fix T :: "('b::linorder\<times>'c::linorder) prefix_tree "
    fix x y G assume "finite_tree T"

    define TGu where TGu: "TGu = distribute_extension M T G cg_lookup cg_insert u [(x,y)] completeInputTraces append_heuristic"
    define TGv where TGv: "TGv = (if u_is_v then TGu else distribute_extension M (fst TGu) (snd TGu) cg_lookup cg_insert v [(x,y)] completeInputTraces append_heuristic)"
    have *: "handleIO (T,G) (x,y) = (if is_in_language M (initial M) (u@[(x,y)])
                                                  then distinguish_from_set M V (fst TGv) (snd TGv) cg_lookup cg_insert get_distinguishing_trace (u@[(x,y)]) (v@[(x,y)]) X' k (depth) completeInputTraces append_heuristic u_is_v
                                                  else TGv)"
      unfolding handleIO TGu TGv case_prod_conv Let_def 
      by auto
    
    have "finite_tree (fst TGu)"
      unfolding TGu
      using distribute_extension_finite \<open>finite_tree T\<close>
      by metis
    then have "finite_tree (fst TGv)"
      unfolding TGv 
      using distribute_extension_finite by force      
    then show "finite_tree (fst (handleIO (T,G) (x,y)))"
      unfolding *
      using Suc.IH[of "fst TGv" "snd TGv" "u@[(x,y)]" "v@[(x,y)]" X'] 
      by (cases "is_in_language M (initial M) (u@[(x,y)])"; auto)
  qed

  have "finite_tree (fst TG')"
    unfolding TG'
    using spyh_distinguish_finite \<open>finite_tree T\<close>
    by metis
  then have "finite_tree (fst TG'')"
    unfolding TG'' 
    using spyh_distinguish_finite[OF \<open>finite_tree (fst (TG'))\<close>, of M "snd TG'" ] 
    by auto
    
  
  have "finite_tree (fst (foldl handleIO TG'' XY))"
  proof (induction XY rule: rev_induct)
    case Nil
    then show ?case using \<open>finite_tree (fst TG'')\<close> by auto
  next
    case (snoc a XY)
    obtain x y where "a = (x,y)"
      using prod.exhaust by metis
    then have *: "(foldl handleIO TG'' (XY@[a])) = handleIO (fst (foldl handleIO TG'' XY),snd (foldl handleIO TG'' XY)) (x,y)"
      by auto

    show ?case 
      using snoc unfolding * 
      using \<open>\<And> x y T G . finite_tree T \<Longrightarrow> finite_tree (fst (handleIO (T,G) (x,y)))\<close>
      by blast       
  qed
  moreover have "distinguish_from_set M V T G cg_lookup cg_insert get_distinguishing_trace u v X k (Suc depth) completeInputTraces append_heuristic u_is_v = foldl handleIO TG'' XY"
    apply (subst distinguish_from_set.simps)
    unfolding TG' vClass notReferenced TG'' Let_def X' XY handleIO 
    unfolding \<open>(Suc depth - 1) = depth\<close> 
    by force

  ultimately show ?case
    by (metis (no_types, lifting)) 
qed


lemma distinguish_from_set_properties :
  assumes "observable M1"
      and "observable M2"
      and "minimal M1"
      and "minimal M2"
      and "inputs M2 = inputs M1"
      and "outputs M2 = outputs M1"
      and "is_state_cover_assignment M1 V"
      and "V ` reachable_states M1 \<subseteq> list.set X"
      and "preserves_divergence M1 M2 (list.set X)"
      and "\<And> w . w \<in> list.set X \<Longrightarrow> \<exists> w' . converge M1 w w' \<and> converge M2 w w'"
      and "converge M1 u v"
      and "u \<in> L M2"
      and "v \<in> L M2"
      and "convergence_graph_lookup_invar M1 M2 cg_lookup G"
      and "convergence_graph_insert_invar M1 M2 cg_lookup cg_insert"
      and "\<And> \<alpha> \<beta> q1 q2 . q1 \<in> states M1 \<Longrightarrow> q2 \<in> states M1 \<Longrightarrow> q1 \<noteq> q2 \<Longrightarrow> distinguishes M1 q1 q2 (get_distinguishing_trace q1 q2)"
      and "L M1 \<inter> set (fst (distinguish_from_set M1 V T G cg_lookup cg_insert get_distinguishing_trace u v X k depth completeInputTraces append_heuristic (u = v))) = L M2 \<inter> set (fst (distinguish_from_set M1 V T G cg_lookup cg_insert get_distinguishing_trace u v X k depth completeInputTraces append_heuristic (u = v)))"
      and "\<And> T w u' uBest lBest . fst (append_heuristic T w (uBest,lBest) u') \<in> {u',uBest}"
shows "\<forall> \<gamma> x y . length (\<gamma>@[(x,y)]) \<le> depth \<longrightarrow>
                  \<gamma> \<in> LS M1 (after_initial M1 u) \<longrightarrow>
                  x \<in> inputs M1 \<longrightarrow> y \<in> outputs M1 \<longrightarrow>
                  L M1 \<inter> (list.set X \<union> {\<omega>@\<omega>' | \<omega> \<omega>' . \<omega> \<in> {u,v} \<and> \<omega>' \<in> list.set (prefixes (\<gamma>@[(x,y)]))}) = L M2 \<inter>  (list.set X \<union> {\<omega>@\<omega>' | \<omega> \<omega>' . \<omega> \<in> {u,v} \<and> \<omega>' \<in> list.set (prefixes (\<gamma>@[(x,y)]))})
                  \<and> preserves_divergence M1 M2 (list.set X \<union> {\<omega>@\<omega>' | \<omega> \<omega>' . \<omega> \<in> {u,v} \<and> \<omega>' \<in> list.set (prefixes (\<gamma>@[(x,y)]))})"
(is "?P1a X u v depth")
and     "preserves_divergence M1 M2 (list.set X \<union> {u,v})"
(is "?P1b X u v")
and   "convergence_graph_lookup_invar M1 M2 cg_lookup (snd (distinguish_from_set M1 V T G cg_lookup cg_insert get_distinguishing_trace u v X k depth completeInputTraces append_heuristic (u = v)))"
(is "?P2 T G u v X depth")
proof -
  have "?P1a X u v depth \<and> ?P1b X u v \<and> ?P2 T G u v X depth"
    using assms(8-14) assms(17)
  proof (induction depth arbitrary: T G u v X)
    case 0

    define TG' where TG': "TG' = spyh_distinguish M1 T G cg_lookup cg_insert get_distinguishing_trace u X k completeInputTraces append_heuristic"
    define vClass where vClass: "vClass = Set.insert v (list.set (cg_lookup (snd TG') v))"
    define notReferenced where notReferenced: "notReferenced = ((\<not> (u = v)) \<and> (\<forall> q \<in> reachable_states M1 . V q \<notin> vClass))"
    define TG'' where TG'': "TG'' = (if notReferenced then spyh_distinguish M1 (fst TG') (snd TG') cg_lookup cg_insert get_distinguishing_trace v X k completeInputTraces append_heuristic else TG')"
  
    have "distinguish_from_set M1 V T G cg_lookup cg_insert get_distinguishing_trace u v X k 0 completeInputTraces append_heuristic (u = v) = TG''"
      apply (subst distinguish_from_set.simps)
      unfolding TG' vClass notReferenced TG'' Let_def 
      by force

    have "set T \<subseteq> set (fst (distinguish_from_set M1 V T G cg_lookup cg_insert get_distinguishing_trace u v X k 0 completeInputTraces append_heuristic (u = v)))"
      using distinguish_from_set_subset by metis
    then have "L M1 \<inter> set T = L M2 \<inter> set T"
      using  "0.prems"(8) 
      by blast

    have "list.set X \<subseteq> L M1" and "list.set X \<subseteq> L M2"
      using "0.prems"(3)
      by (meson converge.elims(2) subsetI)+
    have "set (fst TG') \<subseteq> set (fst (distinguish_from_set M1 V T G cg_lookup cg_insert get_distinguishing_trace u v X k 0 completeInputTraces append_heuristic (u = v)))"
      by (metis TG'' \<open>distinguish_from_set M1 V T G cg_lookup cg_insert get_distinguishing_trace u v X k 0 completeInputTraces append_heuristic (u = v) = TG''\<close> order_refl spyh_distinguish_subset)      
    then have *: "L M1 \<inter> Prefix_Tree.set (fst (spyh_distinguish M1 T G cg_lookup cg_insert get_distinguishing_trace u X k completeInputTraces append_heuristic)) =
                    L M2 \<inter> Prefix_Tree.set (fst (spyh_distinguish M1 T G cg_lookup cg_insert get_distinguishing_trace u X k completeInputTraces append_heuristic))"
      using "0.prems"(8) unfolding TG' 
      by blast
    have "u \<in> L M1" and "v \<in> L M1"
      using \<open>converge M1 u v\<close> by auto

    have "preserves_divergence M1 M2 (Set.insert u (list.set X))"
      using spyh_distinguish_preserves_divergence[OF assms(1-4) \<open>u \<in> L M1\<close> \<open>u \<in> L M2\<close> assms(16) "0.prems"(7) assms(15) \<open>list.set X \<subseteq> L M1\<close> \<open>list.set X \<subseteq> L M2\<close> * assms(18) "0.prems"(2)] 
      unfolding TG' by presburger

    have "convergence_graph_lookup_invar M1 M2 cg_lookup (snd TG')"
      unfolding TG'
      using spyh_distinguish_establishes_divergence[OF assms(1-4) \<open>u \<in> L M1\<close> \<open>u \<in> L M2\<close> assms(16) "0.prems"(7) assms(15) \<open>list.set X \<subseteq> L M1\<close> \<open>list.set X \<subseteq> L M2\<close> * assms(18)] 
      by linarith

    have "L M1 \<inter> set (fst TG'') = L M2 \<inter> set (fst TG'')"
      using "0.prems"(8)
      unfolding \<open>distinguish_from_set M1 V T G cg_lookup cg_insert get_distinguishing_trace u v X k 0 completeInputTraces append_heuristic (u = v) = TG''\<close>
      by blast

    have "preserves_divergence M1 M2 (Set.insert v (list.set X))"
    and  "convergence_graph_lookup_invar M1 M2 cg_lookup (snd TG'')"
    proof -
      have "preserves_divergence M1 M2 (Set.insert v (list.set X)) \<and> convergence_graph_lookup_invar M1 M2 cg_lookup (snd TG'')"
      proof (cases "notReferenced")
        case True

        then have "TG'' = spyh_distinguish M1 (fst TG') (snd TG') cg_lookup cg_insert get_distinguishing_trace v X k completeInputTraces append_heuristic"
          unfolding TG'' by auto
        then have *: "L M1 \<inter> Prefix_Tree.set (fst (spyh_distinguish M1 (fst TG') (snd TG') cg_lookup cg_insert get_distinguishing_trace v X k completeInputTraces append_heuristic)) =
                    L M2 \<inter> Prefix_Tree.set (fst (spyh_distinguish M1 (fst TG') (snd TG') cg_lookup cg_insert get_distinguishing_trace v X k completeInputTraces append_heuristic))"
          using \<open>L M1 \<inter> set (fst TG'') = L M2 \<inter> set (fst TG'')\<close>
          by simp

        show ?thesis 
          using spyh_distinguish_preserves_divergence[OF assms(1-4) \<open>v \<in> L M1\<close> \<open>v \<in> L M2\<close> assms(16) \<open>convergence_graph_lookup_invar M1 M2 cg_lookup (snd TG')\<close> assms(15) \<open>list.set X \<subseteq> L M1\<close> \<open>list.set X \<subseteq> L M2\<close> * assms(18) "0.prems"(2)]
          using spyh_distinguish_establishes_divergence(2)[OF assms(1-4) \<open>v \<in> L M1\<close> \<open>v \<in> L M2\<close> assms(16) \<open>convergence_graph_lookup_invar M1 M2 cg_lookup (snd TG')\<close> assms(15) \<open>list.set X \<subseteq> L M1\<close> \<open>list.set X \<subseteq> L M2\<close> * assms(18)] 
          unfolding \<open>TG'' = spyh_distinguish M1 (fst TG') (snd TG') cg_lookup cg_insert get_distinguishing_trace v X k completeInputTraces append_heuristic\<close>
          by presburger
      next
        case False
        then consider "u = v" | "(u \<noteq> v) \<and> \<not>(\<forall> q \<in> reachable_states M1 . V q \<notin> vClass)"
          unfolding notReferenced by blast
        then show ?thesis proof cases
          case 1 
          then show ?thesis
            using False TG'' \<open>convergence_graph_lookup_invar M1 M2 cg_lookup (snd TG')\<close> \<open>preserves_divergence M1 M2 (Set.insert u (list.set X))\<close> by presburger 
        next
          case 2          
          then have "TG'' = TG'"
            unfolding TG'' using False  by auto
  
          obtain q where "q \<in> reachable_states M1"
                     and "V q \<in> Set.insert v (list.set (cg_lookup (snd TG') v))"
            using 2 
            unfolding notReferenced vClass
            by blast
  
          have "converge M1 (V q) v" and "converge M2 (V q) v"
          proof -
            have "converge M1 v (V q) \<and> converge M2 v (V q)"
            proof (cases "V q = v")
              case True
              then show ?thesis 
                using \<open>v \<in> L M1\<close> \<open>v \<in> L M2\<close> by auto
            next
              case False
              then have "V q \<in> list.set (cg_lookup (snd TG') v)"
                using \<open>V q \<in> Set.insert v (list.set (cg_lookup (snd TG') v))\<close> 
                by blast
              then show ?thesis 
                using \<open>convergence_graph_lookup_invar M1 M2 cg_lookup (snd TG')\<close> 
                unfolding convergence_graph_lookup_invar_def
                using "0.prems"(6) \<open>v \<in> L M1\<close> by blast
            qed
            then show "converge M1 (V q) v" and "converge M2 (V q) v"
              by auto
          qed
  
          have "V q \<in> Set.insert u (list.set X)"
            using \<open>q \<in> reachable_states M1\<close> "0.prems"(1) by blast 
            
          have "preserves_divergence M1 M2 (Set.insert v (list.set X))"
            using preserves_divergence_converge_insert[OF assms(1-4) \<open>converge M1 (V q) v\<close> \<open>converge M2 (V q) v\<close> \<open>preserves_divergence M1 M2 (Set.insert u (list.set X))\<close> \<open>V q \<in> Set.insert u (list.set X)\<close>]
            unfolding preserves_divergence.simps by blast
          then show ?thesis 
            unfolding \<open>TG'' = TG'\<close>
            using \<open>convergence_graph_lookup_invar M1 M2 cg_lookup (snd TG')\<close>
            by auto
        qed
      qed
      then show "preserves_divergence M1 M2 (Set.insert v (list.set X))" and  "convergence_graph_lookup_invar M1 M2 cg_lookup (snd TG'')"
        by auto
    qed

    have "converge M1 u u" and "converge M1 v v" and "converge M1 v u" and "converge M1 u v"
      using \<open>u \<in> L M1\<close> \<open>v \<in> L M1\<close> \<open>converge M1 u v\<close> by auto
    then have "preserves_divergence M1 M2 (Set.insert u (Set.insert v (list.set X)))"
      using \<open>preserves_divergence M1 M2 (Set.insert v (list.set X))\<close>
            \<open>preserves_divergence M1 M2 (Set.insert u (list.set X))\<close>
      unfolding preserves_divergence.simps 
      by blast 
    then have "?P1b X u v"
      by (metis Un_insert_right sup_bot_right) 
    moreover have "?P2 T G u v X 0"  
      using \<open>convergence_graph_lookup_invar M1 M2 cg_lookup (snd TG'')\<close>
      using \<open>distinguish_from_set M1 V T G cg_lookup cg_insert get_distinguishing_trace u v X k 0 completeInputTraces append_heuristic (u = v) = TG''\<close> by blast
    moreover have P1: "?P1a X u v 0"
      by auto
    ultimately show ?case 
      by blast
  next
    case (Suc depth)
    have "0 < Suc depth = True"
      by auto
    have "Suc depth - 1 = depth"
      by auto

    have "u \<in> L M1" and "v \<in> L M1"
      using \<open>converge M1 u v\<close> by auto

    define TG' where TG': "TG' = spyh_distinguish M1 T G cg_lookup cg_insert get_distinguishing_trace u X k completeInputTraces append_heuristic"
    define vClass where vClass: "vClass = Set.insert v (list.set (cg_lookup (snd TG') v))"
    define notReferenced where notReferenced: "notReferenced = (\<not>(u = v) \<and> (\<forall> q \<in> reachable_states M1 . V q \<notin> vClass))"
    define TG'' where TG'': "TG'' = (if notReferenced then spyh_distinguish M1 (fst TG') (snd TG') cg_lookup cg_insert get_distinguishing_trace v X k completeInputTraces append_heuristic else TG')"
    define X' where X': "X' = (if notReferenced then (v#u#X) else (u#X))"
    define XY where XY: "XY = List.product (inputs_as_list M1) (outputs_as_list M1)"
    define handleIO where handleIO: "handleIO = (\<lambda> (T,G) (x,y). (let TGu = distribute_extension M1 T G cg_lookup cg_insert u [(x,y)] completeInputTraces append_heuristic;
                                                 TGv = if (u = v) then TGu else distribute_extension M1 (fst TGu) (snd TGu) cg_lookup cg_insert v [(x,y)] completeInputTraces append_heuristic
                                             in if is_in_language M1 (initial M1) (u@[(x,y)])
                                                  then distinguish_from_set M1 V (fst TGv) (snd TGv) cg_lookup cg_insert get_distinguishing_trace (u@[(x,y)]) (v@[(x,y)]) X' k depth completeInputTraces append_heuristic (u = v) 
                                                  else TGv))"
    
    have result: "distinguish_from_set M1 V T G cg_lookup cg_insert get_distinguishing_trace u v X k (Suc depth) completeInputTraces append_heuristic (u = v) = foldl handleIO TG'' XY"
      apply (subst distinguish_from_set.simps)
      unfolding TG' vClass notReferenced TG'' X' XY handleIO \<open>0 < Suc depth = True\<close> case_prod_conv \<open>Suc depth - 1 = depth\<close> if_True Let_def 
      by force
    then have pass_result: "L M1 \<inter> set (fst (foldl handleIO TG'' XY)) = L M2 \<inter> set (fst (foldl handleIO TG'' XY))"
      using Suc.prems(8)
      by metis 

    have handleIO_subset : "\<And> x y T G . set T \<subseteq> set (fst (handleIO (T,G) (x,y)))"
    proof -
      fix x y T G 

      define TGu where TGu: "TGu = distribute_extension M1 T G cg_lookup cg_insert u [(x,y)] completeInputTraces append_heuristic"
      define TGv where TGv: "TGv = (if (u = v) then TGu else distribute_extension M1 (fst TGu) (snd TGu) cg_lookup cg_insert v [(x,y)] completeInputTraces append_heuristic)" 

      have handleIO: "handleIO (T,G) (x,y) = (if is_in_language M1 (initial M1) (u@[(x,y)])
                                                  then distinguish_from_set M1 V (fst TGv) (snd TGv) cg_lookup cg_insert get_distinguishing_trace (u@[(x,y)]) (v@[(x,y)]) X' k depth completeInputTraces append_heuristic (u = v) 
                                                  else TGv)"
        unfolding handleIO TGu TGv case_prod_conv Let_def 
        by force

      have "set T \<subseteq> set (fst TGu)"
        using distribute_extension_subset[of T]
        unfolding TGu by metis
      moreover have "set (fst TGu) \<subseteq> set (fst TGv)"
        using distribute_extension_subset[of "fst TGu"]
        unfolding TGv by force
      moreover have "set (fst TGv) \<subseteq> set (fst (handleIO (T,G) (x,y)))"
        unfolding handleIO 
        using distinguish_from_set_subset[of "fst TGv" M1 V "snd TGv" cg_lookup cg_insert get_distinguishing_trace "u@[(x,y)]" "v@[(x,y)]" X' k depth] 
        by auto
      ultimately show "set T \<subseteq> set (fst (handleIO (T,G) (x,y)))"
        by blast
    qed
    
    have result_subset: "set (fst TG'') \<subseteq> set (fst (foldl handleIO TG'' XY))"
    proof (induction XY rule: rev_induct)
      case Nil
      then show ?case by auto
    next
      case (snoc x xs)
      then show ?case 
        using handleIO_subset[of "fst (foldl handleIO TG'' xs)" "snd (foldl handleIO TG'' xs)" "fst x" "snd x"]
        by force
    qed 
    then have pass_TG'' : "L M1 \<inter> set (fst TG'') = L M2 \<inter> set (fst TG'')"
      using pass_result by blast

    
    have "set (fst TG') \<subseteq> set (fst TG'')"
      unfolding TG'' using spyh_distinguish_subset
      by (metis (mono_tags, lifting) equalityE) 
    then have pass_TG': "L M1 \<inter> set (fst TG') = L M2 \<inter> set (fst TG')"
      using pass_TG'' by blast

    have "set T \<subseteq> set (fst TG')"
      unfolding TG' using spyh_distinguish_subset by metis
    then have pass_T: "L M1 \<inter> set T = L M2 \<inter> set T"
      using pass_TG' by blast

    have "list.set X \<subseteq> L M1" and "list.set X \<subseteq> L M2"
      using Suc.prems(3) by auto 
    

    have "preserves_divergence M1 M2 (Set.insert u (list.set X))"
    and  "convergence_graph_lookup_invar M1 M2 cg_lookup (snd TG')"
      using spyh_distinguish_preserves_divergence[OF assms(1-4) \<open>u \<in> L M1\<close> \<open>u \<in> L M2\<close> assms(16) Suc.prems(7) assms(15) \<open>list.set X \<subseteq> L M1\<close> \<open>list.set X \<subseteq> L M2\<close> _ _Suc.prems(2), of T k completeInputTraces append_heuristic, OF _ _ _ _ assms(18)] 
            spyh_distinguish_establishes_divergence(2)[OF assms(1-4) \<open>u \<in> L M1\<close> \<open>u \<in> L M2\<close> assms(16) Suc.prems(7) assms(15) \<open>list.set X \<subseteq> L M1\<close> \<open>list.set X \<subseteq> L M2\<close>, of T k completeInputTraces append_heuristic, OF _ _ _ _ assms(18)]
            pass_TG'
      unfolding TG'[symmetric]
      by linarith+

    have "preserves_divergence M1 M2 (Set.insert v (list.set X))"
    and  "convergence_graph_lookup_invar M1 M2 cg_lookup (snd TG'')"
    proof -
      have "preserves_divergence M1 M2 (Set.insert v (list.set X)) \<and> convergence_graph_lookup_invar M1 M2 cg_lookup (snd TG'')"
      proof (cases "notReferenced")
        case True

        then have "TG'' = spyh_distinguish M1 (fst TG') (snd TG') cg_lookup cg_insert get_distinguishing_trace v X k completeInputTraces append_heuristic"
          unfolding TG'' by auto
        then have *: "L M1 \<inter> Prefix_Tree.set (fst (spyh_distinguish M1 (fst TG') (snd TG') cg_lookup cg_insert get_distinguishing_trace v X k completeInputTraces append_heuristic)) =
                    L M2 \<inter> Prefix_Tree.set (fst (spyh_distinguish M1 (fst TG') (snd TG') cg_lookup cg_insert get_distinguishing_trace v X k completeInputTraces append_heuristic))"
          using \<open>L M1 \<inter> set (fst TG'') = L M2 \<inter> set (fst TG'')\<close>
          by simp

        show ?thesis 
          using spyh_distinguish_preserves_divergence[OF assms(1-4) \<open>v \<in> L M1\<close> \<open>v \<in> L M2\<close> assms(16) \<open>convergence_graph_lookup_invar M1 M2 cg_lookup (snd TG')\<close> assms(15) \<open>list.set X \<subseteq> L M1\<close> \<open>list.set X \<subseteq> L M2\<close> * assms(18) Suc.prems(2)]
                spyh_distinguish_establishes_divergence(2)[OF assms(1-4) \<open>v \<in> L M1\<close> \<open>v \<in> L M2\<close> assms(16) \<open>convergence_graph_lookup_invar M1 M2 cg_lookup (snd TG')\<close> assms(15) \<open>list.set X \<subseteq> L M1\<close> \<open>list.set X \<subseteq> L M2\<close> * assms(18)]
          unfolding \<open>TG'' = spyh_distinguish M1 (fst TG') (snd TG') cg_lookup cg_insert get_distinguishing_trace v X k completeInputTraces append_heuristic\<close>
          by presburger
      next
        case False
        then consider "u = v" | "(u \<noteq> v) \<and> \<not>(\<forall> q \<in> reachable_states M1 . V q \<notin> vClass)"
          unfolding notReferenced by blast
        then show ?thesis proof cases
          case 1 
          then show ?thesis
            using False TG'' \<open>convergence_graph_lookup_invar M1 M2 cg_lookup (snd TG')\<close> \<open>preserves_divergence M1 M2 (Set.insert u (list.set X))\<close> by presburger 
        next
          case 2          
          then have "TG'' = TG'"
            unfolding TG'' using False  by auto
        
        

          obtain q where "q \<in> reachable_states M1"
                     and "V q \<in> Set.insert v (list.set (cg_lookup (snd TG') v))"
            using 2 
            unfolding notReferenced vClass
            by blast
  
          have "converge M1 (V q) v" and "converge M2 (V q) v"
          proof -
            have "converge M1 v (V q) \<and> converge M2 v (V q)"
            proof (cases "V q = v")
              case True
              then show ?thesis 
                using \<open>v \<in> L M1\<close> \<open>v \<in> L M2\<close> by auto
            next
              case False
              then have "V q \<in> list.set (cg_lookup (snd TG') v)"
                using \<open>V q \<in> Set.insert v (list.set (cg_lookup (snd TG') v))\<close> 
                by blast
              then show ?thesis 
                using \<open>convergence_graph_lookup_invar M1 M2 cg_lookup (snd TG')\<close> 
                unfolding convergence_graph_lookup_invar_def
                using Suc.prems(6) \<open>v \<in> L M1\<close> by blast
            qed
            then show "converge M1 (V q) v" and "converge M2 (V q) v"
              by auto
          qed
  
          have "V q \<in> Set.insert u (list.set X)"
            using \<open>q \<in> reachable_states M1\<close> Suc.prems(1) by blast 
            
          have "preserves_divergence M1 M2 (Set.insert v (list.set X))"
            using preserves_divergence_converge_insert[OF assms(1-4) \<open>converge M1 (V q) v\<close> \<open>converge M2 (V q) v\<close> \<open>preserves_divergence M1 M2 (Set.insert u (list.set X))\<close> \<open>V q \<in> Set.insert u (list.set X)\<close>]
            unfolding preserves_divergence.simps by blast
          then show ?thesis 
            unfolding \<open>TG'' = TG'\<close>
            using \<open>convergence_graph_lookup_invar M1 M2 cg_lookup (snd TG')\<close>
            by auto
        qed
      qed
      then show "preserves_divergence M1 M2 (Set.insert v (list.set X))" and  "convergence_graph_lookup_invar M1 M2 cg_lookup (snd TG'')"
        by auto
    qed

    have "converge M1 u u" and "converge M1 v v" and "converge M1 v u" and "converge M1 u v"
      using \<open>u \<in> L M1\<close> \<open>v \<in> L M1\<close> \<open>converge M1 u v\<close> by auto
    then have "preserves_divergence M1 M2 (Set.insert u (Set.insert v (list.set X)))"
      using \<open>preserves_divergence M1 M2 (Set.insert v (list.set X))\<close>
            \<open>preserves_divergence M1 M2 (Set.insert u (list.set X))\<close>
      unfolding preserves_divergence.simps 
      by blast 


    have IS1: "V ` reachable_states M1 \<subseteq> list.set X'"
      using Suc.prems(1) unfolding X' by auto

    have IS2: "preserves_divergence M1 M2 (list.set X')"
      using \<open>preserves_divergence M1 M2 (Set.insert u (Set.insert v (list.set X)))\<close>
            \<open>preserves_divergence M1 M2 (Set.insert u (list.set X))\<close>
      unfolding X'
      by (simp add: insert_commute) 
    
    have handleIO_props : "\<And> x y T' G' . set T \<subseteq> set T' \<Longrightarrow> convergence_graph_lookup_invar M1 M2 cg_lookup G' \<Longrightarrow> L M1 \<inter> set (fst (handleIO (T',G') (x,y))) = L M2 \<inter> set (fst (handleIO (T',G') (x,y))) \<Longrightarrow>
                                          x \<in> inputs M1 \<Longrightarrow> y \<in> outputs M1 \<Longrightarrow> 
                                          convergence_graph_lookup_invar M1 M2 cg_lookup (snd (handleIO (T',G') (x,y)))
                                          \<and> L M1 \<inter> (list.set X \<union> {\<omega>@\<omega>' | \<omega> \<omega>' . \<omega> \<in> {u,v} \<and> \<omega>' \<in> list.set (prefixes [(x,y)])}) = L M2 \<inter> (list.set X \<union> {\<omega>@\<omega>' | \<omega> \<omega>' . \<omega> \<in> {u,v} \<and> \<omega>' \<in> list.set (prefixes [(x,y)])})
                                          \<and> preserves_divergence M1 M2 (list.set X \<union> {\<omega>@\<omega>' | \<omega> \<omega>' . \<omega> \<in> {u,v} \<and> \<omega>' \<in> list.set (prefixes [(x,y)])})
                                          \<and> (\<forall> \<gamma> x' y' . length ((x,y)#\<gamma>@[(x',y')]) \<le> Suc depth \<longrightarrow>
                                                      ((x,y)#\<gamma>) \<in> LS M1 (after_initial M1 u) \<longrightarrow>
                                                      x' \<in> inputs M1 \<longrightarrow> y' \<in> outputs M1 \<longrightarrow>
                                                      L M1 \<inter> (list.set X \<union> {\<omega>@\<omega>' | \<omega> \<omega>' . \<omega> \<in> {u,v} \<and> \<omega>' \<in> list.set (prefixes ((x,y)#\<gamma>@[(x',y')]))}) = L M2 \<inter> (list.set X \<union> {\<omega>@\<omega>' | \<omega> \<omega>' . \<omega> \<in> {u,v} \<and> \<omega>' \<in> list.set (prefixes ((x,y)#\<gamma>@[(x',y')]))})
                                                      \<and> preserves_divergence M1 M2 (list.set X \<union> {\<omega>@\<omega>' | \<omega> \<omega>' . \<omega> \<in> {u,v} \<and> \<omega>' \<in> list.set (prefixes ((x,y)#\<gamma>@[(x',y')]))}))"
    proof -
      fix x y T' G' 

      assume "convergence_graph_lookup_invar M1 M2 cg_lookup G'" 
         and "L M1 \<inter> set (fst (handleIO (T',G') (x,y))) = L M2 \<inter> set (fst (handleIO (T',G') (x,y)))"
         and "x \<in> inputs M1"
         and "y \<in> outputs M1"
         and "set T \<subseteq> set T'"

      define TGu where TGu: "TGu = distribute_extension M1 T' G' cg_lookup cg_insert u [(x,y)] completeInputTraces append_heuristic"
      define TGv where TGv: "TGv = (if (u=v) then TGu else distribute_extension M1 (fst TGu) (snd TGu) cg_lookup cg_insert v [(x,y)] completeInputTraces append_heuristic)"

      have handleIO: "handleIO (T',G') (x,y) = (if is_in_language M1 (initial M1) (u@[(x,y)])
                                                  then distinguish_from_set M1 V (fst TGv) (snd TGv) cg_lookup cg_insert get_distinguishing_trace (u@[(x,y)]) (v@[(x,y)]) X' k depth completeInputTraces append_heuristic (u=v)
                                                  else TGv)"
        unfolding handleIO TGu TGv case_prod_conv Let_def 
        by force

      have "set T' \<subseteq> set (fst TGu)"
        using distribute_extension_subset[of T']
        unfolding TGu by metis
      have "set (fst TGu) \<subseteq> set (fst TGv)"
        using distribute_extension_subset[of "fst TGu"]
        unfolding TGv by force
      have "set (fst TGv) \<subseteq> set (fst (handleIO (T',G') (x,y)))"
        unfolding handleIO 
        using distinguish_from_set_subset[of "fst TGv" M1 V "snd TGv" cg_lookup cg_insert get_distinguishing_trace "u@[(x,y)]" "v@[(x,y)]" X' k depth] 
        by auto
      then have pass_TGv: "L M1 \<inter> set (fst TGv) = L M2 \<inter> set (fst TGv)"
        using \<open>L M1 \<inter> set (fst (handleIO (T',G') (x,y))) = L M2 \<inter> set (fst (handleIO (T',G') (x,y)))\<close> \<open>set (fst TGv) \<subseteq> set (fst (handleIO (T',G') (x,y)))\<close>
        by blast

      have *:"L M1 \<inter> set (fst (distribute_extension M1 T' G' cg_lookup cg_insert u [(x,y)] completeInputTraces append_heuristic)) = L M2 \<inter> set (fst (distribute_extension M1 T' G' cg_lookup cg_insert u [(x,y)] completeInputTraces append_heuristic))"
        using \<open>L M1 \<inter> set (fst (handleIO (T',G') (x,y))) = L M2 \<inter> set (fst (handleIO (T',G') (x,y)))\<close> \<open>set (fst TGv) \<subseteq> set (fst (handleIO (T',G') (x,y)))\<close> \<open>set (fst TGu) \<subseteq> set (fst TGv)\<close>
        unfolding TGu
        by blast

      obtain u' where "converge M1 u u'"  
                      "u' @ [(x, y)] \<in> set (fst TGv)"
                      "converge M2 u u'"
                      "convergence_graph_lookup_invar M1 M2 cg_lookup (snd TGu)"
        using distribute_extension_adds_sequence[OF assms(1,3) \<open>u \<in> L M1\<close> \<open>u \<in> L M2\<close> \<open>convergence_graph_lookup_invar M1 M2 cg_lookup G'\<close> assms(15) * assms(18)]
        using \<open>set (fst TGu) \<subseteq> set (fst TGv)\<close>
        unfolding TGu by blast

      have "u' \<in> set (fst TGv)"
        using \<open>u' @ [(x, y)] \<in> set (fst TGv)\<close> set_prefix by metis
      have "u' \<in> L M1"
        using \<open>converge M1 u u'\<close> by auto

      have *:"\<not>(u=v) \<Longrightarrow> L M1 \<inter> set (fst (distribute_extension M1 (fst TGu) (snd TGu) cg_lookup cg_insert v [(x,y)] completeInputTraces append_heuristic)) = L M2 \<inter> set (fst (distribute_extension M1 (fst TGu) (snd TGu) cg_lookup cg_insert v [(x,y)] completeInputTraces append_heuristic))"
        using \<open>L M1 \<inter> set (fst (handleIO (T',G') (x,y))) = L M2 \<inter> set (fst (handleIO (T',G') (x,y)))\<close> \<open>set (fst TGv) \<subseteq> set (fst (handleIO (T',G') (x,y)))\<close>
        using TGv pass_TGv by presburger 

      obtain v' where "converge M1 v v'"  
                      "v' @ [(x, y)] \<in> set (fst TGv)"
                      "converge M2 v v'"
                      "convergence_graph_lookup_invar M1 M2 cg_lookup (snd TGv)"
                      "u=v \<Longrightarrow> u' = v'"
      proof (cases "u=v")
        case True
        then have "TGv = TGu" unfolding TGv by auto
        show ?thesis 
          using that
          using \<open>converge M1 u u'\<close> \<open>u' @ [(x, y)] \<in> set (fst TGv)\<close> \<open>converge M2 u u'\<close> \<open>convergence_graph_lookup_invar M1 M2 cg_lookup (snd TGu)\<close>
          unfolding True \<open>TGv = TGu\<close> by blast
      next
        case False
        then show ?thesis 
          using that
          using distribute_extension_adds_sequence[OF assms(1,3) \<open>v \<in> L M1\<close> \<open>v \<in> L M2\<close> \<open>convergence_graph_lookup_invar M1 M2 cg_lookup (snd TGu)\<close> assms(15) *[OF False] assms(18)]
          unfolding TGv by auto
      qed
        

      have "v' \<in> set (fst TGv)"
        using \<open>v' @ [(x, y)] \<in> set (fst TGv)\<close> set_prefix by metis
      have "v' \<in> L M1"
        using \<open>converge M1 v v'\<close> by auto

      have *: "{\<omega>@\<omega>' | \<omega> \<omega>' . \<omega> \<in> {u,v} \<and> \<omega>' \<in> list.set (prefixes [(x,y)])} = {u,v,u@[(x,y)],v@[(x,y)]}"
        by auto

      have "u \<in> L M1 = (u \<in> L M2)"
        using Suc.prems(5) \<open>u \<in> L M1\<close> by auto
      moreover have "v \<in> L M1 = (v \<in> L M2)"
        using Suc.prems(6) \<open>v \<in> L M1\<close> by auto
      moreover have "u @ [(x, y)] \<in> L M1 = (u @ [(x, y)] \<in> L M2)"
      proof -
        have "u @ [(x, y)] \<in> L M1 = (u' @ [(x, y)] \<in> L M1)"
          using \<open>converge M1 u u'\<close> assms(1) converge_append_language_iff by blast
        also have "\<dots> = (u' @ [(x, y)] \<in> L M2)"
          using pass_TGv \<open>u' @ [(x, y)] \<in> set (fst TGv)\<close> by blast
        also have "\<dots> = (u @ [(x, y)] \<in> L M2)"
          using \<open>converge M2 u u'\<close> assms(2) converge_append_language_iff by blast 
        finally show ?thesis .
      qed
      moreover have "v @ [(x, y)] \<in> L M1 = (v @ [(x, y)] \<in> L M2)"
      proof -
        have "v @ [(x, y)] \<in> L M1 = (v' @ [(x, y)] \<in> L M1)"
          using \<open>converge M1 v v'\<close> assms(1) converge_append_language_iff by blast
        also have "\<dots> = (v' @ [(x, y)] \<in> L M2)"
          using pass_TGv \<open>v' @ [(x, y)] \<in> set (fst TGv)\<close> by blast
        also have "\<dots> = (v @ [(x, y)] \<in> L M2)"
          using \<open>converge M2 v v'\<close> assms(2) converge_append_language_iff by blast 
        finally show ?thesis .
      qed
      moreover have "L M1 \<inter> list.set X = (L M2 \<inter> list.set X)"
        using Suc.prems(3)
        by fastforce
      ultimately have p2: "L M1 \<inter> (list.set X \<union> {\<omega>@\<omega>' | \<omega> \<omega>' . \<omega> \<in> {u,v} \<and> \<omega>' \<in> list.set (prefixes [(x,y)])}) = L M2 \<inter> (list.set X \<union> {\<omega>@\<omega>' | \<omega> \<omega>' . \<omega> \<in> {u,v} \<and> \<omega>' \<in> list.set (prefixes [(x,y)])})"
        unfolding * by blast


      show "convergence_graph_lookup_invar M1 M2 cg_lookup (snd (handleIO (T',G') (x,y)))
                                          \<and> L M1 \<inter> (list.set X \<union> {\<omega>@\<omega>' | \<omega> \<omega>' . \<omega> \<in> {u,v} \<and> \<omega>' \<in> list.set (prefixes [(x,y)])}) = L M2 \<inter> (list.set X \<union> {\<omega>@\<omega>' | \<omega> \<omega>' . \<omega> \<in> {u,v} \<and> \<omega>' \<in> list.set (prefixes [(x,y)])})
                                          \<and> preserves_divergence M1 M2 (list.set X \<union> {\<omega>@\<omega>' | \<omega> \<omega>' . \<omega> \<in> {u,v} \<and> \<omega>' \<in> list.set (prefixes [(x,y)])})
                                          \<and> (\<forall> \<gamma> x' y' . length ((x,y)#\<gamma>@[(x',y')]) \<le> Suc depth \<longrightarrow>
                                                      ((x,y)#\<gamma>) \<in> LS M1 (after_initial M1 u) \<longrightarrow>
                                                      x' \<in> inputs M1 \<longrightarrow> y' \<in> outputs M1 \<longrightarrow>
                                                      L M1 \<inter> (list.set X \<union> {\<omega>@\<omega>' | \<omega> \<omega>' . \<omega> \<in> {u,v} \<and> \<omega>' \<in> list.set (prefixes ((x,y)#\<gamma>@[(x',y')]))}) = L M2 \<inter> (list.set X \<union> {\<omega>@\<omega>' | \<omega> \<omega>' . \<omega> \<in> {u,v} \<and> \<omega>' \<in> list.set (prefixes ((x,y)#\<gamma>@[(x',y')]))})
                                                      \<and> preserves_divergence M1 M2 (list.set X \<union> {\<omega>@\<omega>' | \<omega> \<omega>' . \<omega> \<in> {u,v} \<and> \<omega>' \<in> list.set (prefixes ((x,y)#\<gamma>@[(x',y')]))}))"
      proof (cases "is_in_language M1 (initial M1) (u@[(x,y)])")
        case False

        
        have "u@[(x,y)] \<notin> L M1"
          using False by (meson assms(1) fsm_initial is_in_language_iff)
        moreover have "v@[(x,y)] \<notin> L M1"
          using calculation Suc.prems(4) assms(1) converge_append_language_iff by blast
        moreover have "preserves_divergence M1 M2 (list.set X \<union> {u,v})"
          by (metis (no_types) Un_insert_right \<open>preserves_divergence M1 M2 (Set.insert u (Set.insert v (list.set X)))\<close> sup_bot_right)
        ultimately have p3: "preserves_divergence M1 M2 (list.set X \<union> {\<omega>@\<omega>' | \<omega> \<omega>' . \<omega> \<in> {u,v} \<and> \<omega>' \<in> list.set (prefixes [(x,y)])})"
          unfolding * preserves_divergence.simps
          by blast 
          
        have handleIO: "(handleIO (T',G') (x,y)) = TGv"
          using handleIO False by auto

        have "\<And> x xs . x # xs = [x] @ xs" by auto
        then have "\<And> \<gamma> . (x, y) # \<gamma> \<notin> LS M1 (after_initial M1 u)"
          by (metis \<open>u @ [(x, y)] \<notin> L M1\<close> \<open>u \<in> L M1\<close> after_language_iff assms(1) language_prefix)

        
        have "convergence_graph_lookup_invar M1 M2 cg_lookup (snd (handleIO (T',G') (x,y)))"
          unfolding handleIO
          by (simp add: \<open>convergence_graph_lookup_invar M1 M2 cg_lookup (snd TGv)\<close>) 
        moreover note p2 p3 \<open>\<And> \<gamma> . (x, y) # \<gamma> \<notin> LS M1 (after_initial M1 u)\<close>
        ultimately show ?thesis
          by presburger 
      next
        case True
        then have handleIO: "(handleIO (T',G') (x,y)) = distinguish_from_set M1 V (fst TGv) (snd TGv) cg_lookup cg_insert get_distinguishing_trace (u @ [(x, y)]) (v @ [(x, y)]) X' k depth completeInputTraces append_heuristic (u@[(x,y)] = v@[(x,y)])"
          using handleIO by auto

        have "converge M1 (u@[(x,y)]) (v@[(x,y)])"
          by (meson Suc.prems(4) True \<open>v \<in> L M1\<close> assms(1) converge_append fsm_initial is_in_language_iff)
        then have "(u@[(x,y)]) \<in> L M1" and "(v@[(x,y)]) \<in> L M1"
          by auto
        have "(u@[(x,y)]) \<in> L M2"
          by (meson True \<open>(u @ [(x, y)] \<in> L M1) = (u @ [(x, y)] \<in> L M2)\<close> assms(1) fsm_initial is_in_language_iff) 
        have "(v@[(x,y)]) \<in> L M2"
          using Suc.prems(4) \<open>(u @ [(x, y)] \<in> L M1) = (u @ [(x, y)] \<in> L M2)\<close> \<open>(v @ [(x, y)] \<in> L M1) = (v @ [(x, y)] \<in> L M2)\<close> \<open>u @ [(x, y)] \<in> L M2\<close> assms(1) converge_append_language_iff by blast
        have "preserves_divergence M1 M2 (list.set X \<union> {u,v})"
          by (metis (no_types) Un_insert_right \<open>preserves_divergence M1 M2 (Set.insert u (Set.insert v (list.set X)))\<close> sup_bot_right)


        have IS3: "\<And>w. w \<in> list.set X' \<Longrightarrow> \<exists>w'. converge M1 w w' \<and> converge M2 w w'"
          unfolding X'
          by (metis (full_types) Suc.prems(3) \<open>converge M1 u u'\<close> \<open>converge M1 v v'\<close> \<open>converge M2 u u'\<close> \<open>converge M2 v v'\<close> set_ConsD) 

        have "(u@[(x,y)] = v@[(x,y)]) = (u=v)"
          by auto
        have IS4: "L M1 \<inter> Prefix_Tree.set (fst (distinguish_from_set M1 V (fst TGv) (snd TGv) cg_lookup cg_insert get_distinguishing_trace (u @ [(x, y)]) (v @ [(x, y)]) X' k depth completeInputTraces append_heuristic (u@[(x,y)] = v@[(x,y)]))) = L M2 \<inter> Prefix_Tree.set (fst (distinguish_from_set M1 V (fst TGv) (snd TGv) cg_lookup cg_insert get_distinguishing_trace (u @ [(x, y)]) (v @ [(x, y)]) X' k depth completeInputTraces append_heuristic (u@[(x,y)] = v@[(x,y)])))"
          using \<open>L M1 \<inter> set (fst (handleIO (T',G') (x,y))) = L M2 \<inter> set (fst (handleIO (T',G') (x,y)))\<close>
          unfolding handleIO \<open>(u@[(x,y)] = v@[(x,y)]) = (u=v)\<close>
          by blast

        have IH1: "\<And> \<gamma> xa ya. length (\<gamma> @ [(xa, ya)]) \<le> depth \<Longrightarrow>
                     \<gamma> \<in> LS M1 (after_initial M1 (u @ [(x, y)])) \<Longrightarrow>
                     xa \<in> FSM.inputs M1 \<Longrightarrow>
                     ya \<in> FSM.outputs M1 \<Longrightarrow>
                     L M1 \<inter> (list.set X' \<union> {\<omega> @ \<omega>' |\<omega> \<omega>'. \<omega> \<in> {u @ [(x, y)], v @ [(x, y)]} \<and> \<omega>' \<in> list.set (prefixes (\<gamma> @ [(xa, ya)]))}) = L M2 \<inter> (list.set X' \<union> {\<omega> @ \<omega>' |\<omega> \<omega>'. \<omega> \<in> {u @ [(x, y)], v @ [(x, y)]} \<and> \<omega>' \<in> list.set (prefixes (\<gamma> @ [(xa, ya)]))}) \<and> 
                     preserves_divergence M1 M2 (list.set X' \<union> {\<omega> @ \<omega>' |\<omega> \<omega>'. \<omega> \<in> {u @ [(x, y)], v @ [(x, y)]} \<and> \<omega>' \<in> list.set (prefixes (\<gamma> @ [(xa, ya)]))})"
        and  IH2: "preserves_divergence M1 M2 (list.set X' \<union> {u @ [(x, y)], v @ [(x, y)]})"
        and  IH3: "convergence_graph_lookup_invar M1 M2 cg_lookup (snd (handleIO (T', G') (x, y)))"          
          using Suc.IH[OF IS1 IS2 IS3 \<open>converge M1 (u@[(x,y)]) (v@[(x,y)])\<close> \<open>u@[(x,y)] \<in> L M2\<close> \<open>v@[(x,y)] \<in> L M2\<close> \<open>convergence_graph_lookup_invar M1 M2 cg_lookup (snd TGv)\<close> IS4]
          unfolding handleIO[symmetric]
          by blast+
        

        have p3: "preserves_divergence M1 M2 (list.set X \<union> {\<omega>@\<omega>' | \<omega> \<omega>' . \<omega> \<in> {u,v} \<and> \<omega>' \<in> list.set (prefixes [(x,y)])})"
        proof (cases notReferenced)
          case True
          then have "list.set X' = list.set X \<union> {u,v}"
            unfolding X' by auto
          show ?thesis 
            using IH2
            unfolding * preserves_divergence.simps \<open>list.set X' = list.set X \<union> {u,v}\<close>
            by blast
        next
          case False
          then consider "u = v" | "(u \<noteq> v) \<and> \<not>(\<forall> q \<in> reachable_states M1 . V q \<notin> vClass)"
            unfolding notReferenced by blast
          then show ?thesis proof cases
            case 1
            then show ?thesis
              by (metis (no_types, lifting) "*" False IH2 Un_insert_left Un_insert_right X' insertI1 insert_absorb list.simps(15)) 
          next
            case 2

            then have **:"(list.set X \<union> {\<omega>@\<omega>' | \<omega> \<omega>' . \<omega> \<in> {u,v} \<and> \<omega>' \<in> list.set (prefixes [(x,y)])}) = (list.set X' \<union> {u @ [(x, y)], v @ [(x, y)]}) \<union> {v}"
              unfolding * X'
              by auto
  
            obtain q where "q \<in> reachable_states M1" and "V q \<in> vClass"
              using 2 notReferenced by blast
            then have "V q \<in> list.set (cg_lookup (snd TG') v)"
              unfolding vClass
              using \<open>convergence_graph_lookup_invar M1 M2 cg_lookup (snd TG')\<close> \<open>v \<in> L M1\<close> \<open>v \<in> L M2\<close>
              unfolding convergence_graph_lookup_invar_def by blast
            then have "converge M1 (V q) v" and "converge M2 (V q) v"
              using convergence_graph_lookup_invar_simp[OF \<open>convergence_graph_lookup_invar M1 M2 cg_lookup (snd TG')\<close> \<open>v \<in> L M1\<close> \<open>v \<in> L M2\<close>, of "V q"]
              by auto
            
            have "\<And> \<beta> . \<beta> \<in> L M1 \<inter> (list.set X \<union> {\<omega>@\<omega>' | \<omega> \<omega>' . \<omega> \<in> {u,v} \<and> \<omega>' \<in> list.set (prefixes [(x,y)])}) \<Longrightarrow> \<not>converge M1 v \<beta> \<Longrightarrow> \<not>converge M2 v \<beta>"
            proof -
              fix \<beta> assume "\<beta> \<in> L M1 \<inter> (list.set X \<union> {\<omega>@\<omega>' | \<omega> \<omega>' . \<omega> \<in> {u,v} \<and> \<omega>' \<in> list.set (prefixes [(x,y)])})" and "\<not>converge M1 v \<beta>"
              then consider "\<beta> = v" | "\<beta> \<in> L M1 \<inter> (list.set X' \<union> {u @ [(x, y)], v @ [(x, y)]})"
                unfolding ** by blast
              then show "\<not>converge M2 v \<beta>"
              proof cases
                case 1
                then show ?thesis using \<open>\<not>converge M1 v \<beta>\<close> \<open>v \<in> L M1\<close> by auto
              next
                case 2
                moreover have "\<not>converge M1 (V q) \<beta>"
                  using \<open>converge M1 (V q) v\<close> \<open>\<not>converge M1 v \<beta>\<close>
                  by auto
                moreover have "V q \<in> list.set X'"
                  using Suc.prems(1) \<open>q \<in> reachable_states M1\<close> 
                  unfolding X' by auto
                moreover have "V q \<in> L M1"
                  using \<open>converge M1 (V q) v\<close> converge.simps by blast 
                ultimately have "\<not>converge M2 (V q) \<beta>"
                  using IH2
                  unfolding preserves_divergence.simps
                  by blast
                then show ?thesis 
                  using \<open>converge M2 (V q) v\<close> unfolding converge.simps by force
              qed 
            qed
            
            have "\<And> \<alpha> \<beta> . \<alpha> \<in> L M1 \<inter> (list.set X \<union> {\<omega>@\<omega>' | \<omega> \<omega>' . \<omega> \<in> {u,v} \<and> \<omega>' \<in> list.set (prefixes [(x,y)])}) \<Longrightarrow> \<beta> \<in> L M1 \<inter> (list.set X \<union> {\<omega>@\<omega>' | \<omega> \<omega>' . \<omega> \<in> {u,v} \<and> \<omega>' \<in> list.set (prefixes [(x,y)])}) \<Longrightarrow> \<not>converge M1 \<alpha> \<beta> \<Longrightarrow> \<not>converge M2 \<alpha> \<beta>"
            proof - 
              fix \<alpha> \<beta> assume "\<alpha> \<in> L M1 \<inter> (list.set X \<union> {\<omega>@\<omega>' | \<omega> \<omega>' . \<omega> \<in> {u,v} \<and> \<omega>' \<in> list.set (prefixes [(x,y)])})"
                             "\<beta> \<in> L M1 \<inter> (list.set X \<union> {\<omega>@\<omega>' | \<omega> \<omega>' . \<omega> \<in> {u,v} \<and> \<omega>' \<in> list.set (prefixes [(x,y)])})"
                             "\<not>converge M1 \<alpha> \<beta>"
              then consider "\<alpha> = v \<and> \<beta> \<in> L M1 \<inter> (list.set X \<union> {\<omega>@\<omega>' | \<omega> \<omega>' . \<omega> \<in> {u,v} \<and> \<omega>' \<in> list.set (prefixes [(x,y)])})" | 
                            "\<beta> = v \<and> \<alpha> \<in> L M1 \<inter> (list.set X \<union> {\<omega>@\<omega>' | \<omega> \<omega>' . \<omega> \<in> {u,v} \<and> \<omega>' \<in> list.set (prefixes [(x,y)])})" |
                            "\<alpha> \<in> L M1 \<inter> (list.set X' \<union> {u @ [(x, y)], v @ [(x, y)]}) \<and> \<beta> \<in> L M1 \<inter> (list.set X' \<union> {u @ [(x, y)], v @ [(x, y)]})"
                unfolding ** by auto
              then show "\<not>converge M2 \<alpha> \<beta>" proof cases
                case 1
                then show ?thesis using \<open>\<And> \<beta> . \<beta> \<in> L M1 \<inter> (list.set X \<union> {\<omega>@\<omega>' | \<omega> \<omega>' . \<omega> \<in> {u,v} \<and> \<omega>' \<in> list.set (prefixes [(x,y)])}) \<Longrightarrow> \<not>converge M1 v \<beta> \<Longrightarrow> \<not>converge M2 v \<beta>\<close>
                  using \<open>\<not> converge M1 \<alpha> \<beta>\<close> by blast                
              next
                case 2
                then show ?thesis using \<open>\<And> \<beta> . \<beta> \<in> L M1 \<inter> (list.set X \<union> {\<omega>@\<omega>' | \<omega> \<omega>' . \<omega> \<in> {u,v} \<and> \<omega>' \<in> list.set (prefixes [(x,y)])}) \<Longrightarrow> \<not>converge M1 v \<beta> \<Longrightarrow> \<not>converge M2 v \<beta>\<close>[of \<alpha>]
                  using \<open>\<not> converge M1 \<alpha> \<beta>\<close> 
                  unfolding converge_sym[of _ \<alpha>] by blast                
              next
                case 3
                then show ?thesis 
                  using IH2 \<open>\<not> converge M1 \<alpha> \<beta>\<close> 
                  unfolding preserves_divergence.simps by blast
              qed
            qed
            then show ?thesis
              unfolding preserves_divergence.simps 
              by blast
          qed
        qed

        have p4: "(\<And> \<gamma> x' y'.
                      length ((x, y) # \<gamma> @ [(x', y')]) \<le> Suc depth \<Longrightarrow>
                      (x, y) # \<gamma> \<in> LS M1 (after_initial M1 u) \<Longrightarrow>
                      x' \<in> FSM.inputs M1 \<Longrightarrow>
                      y' \<in> FSM.outputs M1 \<Longrightarrow>
                      L M1 \<inter> (list.set X \<union> {\<omega> @ \<omega>' |\<omega> \<omega>'. \<omega> \<in> {u, v} \<and> \<omega>' \<in> list.set (prefixes ((x, y) # \<gamma> @ [(x', y')]))}) =
                      L M2 \<inter> (list.set X \<union> {\<omega> @ \<omega>' |\<omega> \<omega>'. \<omega> \<in> {u, v} \<and> \<omega>' \<in> list.set (prefixes ((x, y) # \<gamma> @ [(x', y')]))}) \<and>
                      preserves_divergence M1 M2 (list.set X \<union> {\<omega> @ \<omega>' |\<omega> \<omega>'. \<omega> \<in> {u, v} \<and> \<omega>' \<in> list.set (prefixes ((x, y) # \<gamma> @ [(x', y')]))}))"
        proof -
          fix \<gamma> x' y'
          assume "length ((x, y) # \<gamma> @ [(x', y')]) \<le> Suc depth"
                 "(x, y) # \<gamma> \<in> LS M1 (after_initial M1 u)"
                 "x' \<in> FSM.inputs M1"
                 "y' \<in> FSM.outputs M1"

          
          have s1: "length (\<gamma> @ [(x', y')]) \<le> depth"
            using \<open>length ((x, y) # \<gamma> @ [(x', y')]) \<le> Suc depth\<close> by auto
          have s2: "\<gamma> \<in> LS M1 (after_initial M1 (u @ [(x, y)]))"
            using \<open>(x, y) # \<gamma> \<in> LS M1 (after_initial M1 u)\<close>
            by (metis \<open>u @ [(x, y)] \<in> L M1\<close> after_language_append_iff append_Cons assms(1) empty_append_eq_id)

          have pass': "L M1 \<inter> (list.set X' \<union> {\<omega> @ \<omega>' |\<omega> \<omega>'. \<omega> \<in> {u @ [(x, y)], v @ [(x, y)]} \<and> \<omega>' \<in> list.set (prefixes (\<gamma> @ [(x', y')]))}) = L M2 \<inter> (list.set X' \<union> {\<omega> @ \<omega>' |\<omega> \<omega>'. \<omega> \<in> {u @ [(x, y)], v @ [(x, y)]} \<and> \<omega>' \<in> list.set (prefixes (\<gamma> @ [(x', y')]))})"
          and  preserve': "preserves_divergence M1 M2 (list.set X' \<union> {\<omega> @ \<omega>' |\<omega> \<omega>'. \<omega> \<in> {u @ [(x, y)], v @ [(x, y)]} \<and> \<omega>' \<in> list.set (prefixes (\<gamma> @ [(x', y')]))})"
            using IH1[OF s1 s2 \<open>x' \<in> FSM.inputs M1\<close> \<open>y' \<in> FSM.outputs M1\<close>]
            by blast+         


          have ***:"{\<omega> @ \<omega>' |\<omega> \<omega>'. \<omega> \<in> {u, v} \<and> \<omega>' \<in> list.set (prefixes ((x, y) # \<gamma> @ [(x', y')]))}
                = {\<omega> @ \<omega>' |\<omega> \<omega>'. \<omega> \<in> {u @ [(x, y)], v @ [(x, y)]} \<and> \<omega>' \<in> list.set (prefixes (\<gamma> @ [(x', y')]))} \<union> {u,v}"
            (is "?A = ?B")
          proof 
            show "?A \<subseteq> ?B"
            proof  
              fix w assume "w \<in> ?A"
              then obtain \<omega> \<omega>' where "w = \<omega> @ \<omega>'" and "\<omega> \<in> {u, v}" and "\<omega>' \<in> list.set (prefixes ((x, y) # \<gamma> @ [(x', y')]))"
                by blast

              show "w \<in> ?B"
              proof (cases \<omega>')
                case Nil
                then show ?thesis unfolding \<open>w = \<omega> @ \<omega>'\<close> prefixes_set using \<open>\<omega> \<in> {u, v}\<close> by auto
              next
                case (Cons a list)
                then have "a = (x,y)" and "list \<in> list.set (prefixes (\<gamma> @ [(x', y')]))"
                  using \<open>\<omega>' \<in> list.set (prefixes ((x, y) # \<gamma> @ [(x', y')]))\<close>
                  by (meson prefixes_Cons)+ 
                moreover have "\<omega>@[(x,y)] \<in> {u @ [(x, y)], v @ [(x, y)]}"
                  using \<open>\<omega> \<in> {u, v}\<close>
                  by auto
                ultimately have "((\<omega>@[(x,y)])@list) \<in> {\<omega> @ \<omega>' |\<omega> \<omega>'. \<omega> \<in> {u @ [(x, y)], v @ [(x, y)]} \<and> \<omega>' \<in> list.set (prefixes (\<gamma> @ [(x', y')]))}"
                  by blast
                then show ?thesis 
                  unfolding \<open>w = \<omega> @ \<omega>'\<close> Cons \<open>a = (x,y)\<close> 
                  by auto
              qed
            qed
            show "?B \<subseteq> ?A"
            proof 
              fix w assume "w \<in> ?B"
              then consider "w \<in> {u,v}" | "w \<in> {\<omega> @ \<omega>' |\<omega> \<omega>'. \<omega> \<in> {u @ [(x, y)], v @ [(x, y)]} \<and> \<omega>' \<in> list.set (prefixes (\<gamma> @ [(x', y')]))}"
                by blast
              then show "w \<in> ?A" proof cases
                case 1
                then show ?thesis using prefixes_set_Nil[of " ((x, y) # \<gamma> @ [(x', y')])"]
                  using append.right_neutral by blast
              next
                case 2
                then obtain \<omega> \<omega>' where "w = \<omega> @ \<omega>'" and "\<omega> \<in> {u @ [(x, y)], v @ [(x, y)]}" and "\<omega>' \<in> list.set (prefixes (\<gamma> @ [(x', y')]))"
                  by blast

                obtain \<omega>'' where "\<omega> = \<omega>''@[(x,y)]"
                  using \<open>\<omega> \<in> {u @ [(x, y)], v @ [(x, y)]}\<close> by auto
                then have "\<omega>'' \<in> {u,v}"
                  using \<open>\<omega> \<in> {u @ [(x, y)], v @ [(x, y)]}\<close> by auto
                moreover have "[(x,y)]@\<omega>' \<in> list.set (prefixes ((x, y) # \<gamma> @ [(x', y')]))"
                  using prefixes_prepend[OF \<open>\<omega>' \<in> list.set (prefixes (\<gamma> @ [(x', y')]))\<close>]
                  by (metis append_Cons empty_append_eq_id)
                ultimately show "w \<in> ?A"
                  unfolding \<open>w = \<omega> @ \<omega>'\<close> \<open>\<omega> = \<omega>''@[(x,y)]\<close>
                  using append_assoc by blast
              qed 
            qed
          qed

          have "list.set X \<subseteq> list.set X'"
            unfolding X' by auto
          then have pass'': "L M1 \<inter> (list.set X \<union> {\<omega> @ \<omega>' |\<omega> \<omega>'. \<omega> \<in> {u, v} \<and> \<omega>' \<in> list.set (prefixes ((x, y) # \<gamma> @ [(x', y')]))}) = L M2 \<inter> (list.set X \<union> {\<omega> @ \<omega>' |\<omega> \<omega>'. \<omega> \<in> {u, v} \<and> \<omega>' \<in> list.set (prefixes ((x, y) # \<gamma> @ [(x', y')]))})"
            using pass' \<open>u \<in> L M1\<close> \<open>v \<in> L M1\<close> \<open>u \<in> L M2\<close> \<open>v \<in> L M2\<close>
            unfolding ***
            by blast

          have preserve'': "preserves_divergence M1 M2 (list.set X \<union> {\<omega> @ \<omega>' |\<omega> \<omega>'. \<omega> \<in> {u, v} \<and> \<omega>' \<in> list.set (prefixes ((x, y) # \<gamma> @ [(x', y')]))})"
          proof (cases notReferenced)
            case True
            then have "list.set X' = list.set X \<union> {u,v}"
              unfolding X' by auto
            show ?thesis 
              using preserve'
              unfolding *** preserves_divergence.simps \<open>list.set X' = list.set X \<union> {u,v}\<close>
              by blast
          next
            case False
            then consider "u = v" | "(u \<noteq> v) \<and> \<not>(\<forall> q \<in> reachable_states M1 . V q \<notin> vClass)"
              unfolding notReferenced by blast
            then show ?thesis proof cases
              case 1
              then show ?thesis
                using "***" X' preserve' by fastforce                 
            next
              case 2

              then have **:"(list.set X \<union> {\<omega> @ \<omega>' |\<omega> \<omega>'. \<omega> \<in> {u, v} \<and> \<omega>' \<in> list.set (prefixes ((x, y) # \<gamma> @ [(x', y')]))}) = (list.set X' \<union> {\<omega> @ \<omega>' |\<omega> \<omega>'. \<omega> \<in> {u @ [(x, y)], v @ [(x, y)]} \<and> \<omega>' \<in> list.set (prefixes (\<gamma> @ [(x', y')]))}) \<union> {v}"
                unfolding *** X' by auto
    
              obtain q where "q \<in> reachable_states M1" and "V q \<in> vClass"
                using 2 notReferenced by blast
              then have "V q \<in> list.set (cg_lookup (snd TG') v)"
                unfolding vClass
                using \<open>convergence_graph_lookup_invar M1 M2 cg_lookup (snd TG')\<close> \<open>v \<in> L M1\<close> \<open>v \<in> L M2\<close>
                unfolding convergence_graph_lookup_invar_def by blast
              then have "converge M1 (V q) v" and "converge M2 (V q) v"
                using convergence_graph_lookup_invar_simp[OF \<open>convergence_graph_lookup_invar M1 M2 cg_lookup (snd TG')\<close> \<open>v \<in> L M1\<close> \<open>v \<in> L M2\<close>, of "V q"]
                by auto
              
              have "\<And> \<beta> . \<beta> \<in> L M1 \<inter> (list.set X \<union> {\<omega> @ \<omega>' |\<omega> \<omega>'. \<omega> \<in> {u, v} \<and> \<omega>' \<in> list.set (prefixes ((x, y) # \<gamma> @ [(x', y')]))}) \<Longrightarrow> \<not>converge M1 v \<beta> \<Longrightarrow> \<not>converge M2 v \<beta>"
              proof -
                fix \<beta> assume "\<beta> \<in> L M1 \<inter> (list.set X \<union> {\<omega> @ \<omega>' |\<omega> \<omega>'. \<omega> \<in> {u, v} \<and> \<omega>' \<in> list.set (prefixes ((x, y) # \<gamma> @ [(x', y')]))})" and "\<not>converge M1 v \<beta>"
                then consider "\<beta> = v" | "\<beta> \<in> L M1 \<inter> (list.set X' \<union> {\<omega> @ \<omega>' |\<omega> \<omega>'. \<omega> \<in> {u @ [(x, y)], v @ [(x, y)]} \<and> \<omega>' \<in> list.set (prefixes (\<gamma> @ [(x', y')]))})"
                  unfolding ** by blast
                then show "\<not>converge M2 v \<beta>"
                proof cases
                  case 1
                  then show ?thesis using \<open>\<not>converge M1 v \<beta>\<close> \<open>v \<in> L M1\<close> by auto
                next
                  case 2
                  moreover have "\<not>converge M1 (V q) \<beta>"
                    using \<open>converge M1 (V q) v\<close> \<open>\<not>converge M1 v \<beta>\<close>
                    by auto
                  moreover have "V q \<in> list.set X'"
                    using Suc.prems(1) \<open>q \<in> reachable_states M1\<close> 
                    unfolding X' by auto
                  moreover have "V q \<in> L M1"
                    using \<open>converge M1 (V q) v\<close> converge.simps by blast 
                  ultimately have "\<not>converge M2 (V q) \<beta>"
                    using preserve'
                    unfolding preserves_divergence.simps
                    by blast
                  then show ?thesis 
                    using \<open>converge M2 (V q) v\<close> unfolding converge.simps by force
                qed 
              qed
              
              have "\<And> \<alpha> \<beta> . \<alpha> \<in> L M1 \<inter> (list.set X \<union> {\<omega> @ \<omega>' |\<omega> \<omega>'. \<omega> \<in> {u, v} \<and> \<omega>' \<in> list.set (prefixes ((x, y) # \<gamma> @ [(x', y')]))}) \<Longrightarrow> \<beta> \<in> L M1 \<inter> (list.set X \<union> {\<omega> @ \<omega>' |\<omega> \<omega>'. \<omega> \<in> {u, v} \<and> \<omega>' \<in> list.set (prefixes ((x, y) # \<gamma> @ [(x', y')]))}) \<Longrightarrow> \<not>converge M1 \<alpha> \<beta> \<Longrightarrow> \<not>converge M2 \<alpha> \<beta>"
              proof - 
                fix \<alpha> \<beta> assume "\<alpha> \<in> L M1 \<inter> (list.set X \<union> {\<omega> @ \<omega>' |\<omega> \<omega>'. \<omega> \<in> {u, v} \<and> \<omega>' \<in> list.set (prefixes ((x, y) # \<gamma> @ [(x', y')]))})"
                               "\<beta> \<in> L M1 \<inter> (list.set X \<union> {\<omega> @ \<omega>' |\<omega> \<omega>'. \<omega> \<in> {u, v} \<and> \<omega>' \<in> list.set (prefixes ((x, y) # \<gamma> @ [(x', y')]))})"
                               "\<not>converge M1 \<alpha> \<beta>"
                then consider "\<alpha> = v \<and> \<beta> \<in> L M1 \<inter> (list.set X \<union> {\<omega> @ \<omega>' |\<omega> \<omega>'. \<omega> \<in> {u, v} \<and> \<omega>' \<in> list.set (prefixes ((x, y) # \<gamma> @ [(x', y')]))})" | 
                              "\<beta> = v \<and> \<alpha> \<in> L M1 \<inter> (list.set X \<union> {\<omega> @ \<omega>' |\<omega> \<omega>'. \<omega> \<in> {u, v} \<and> \<omega>' \<in> list.set (prefixes ((x, y) # \<gamma> @ [(x', y')]))})" |
                              "\<alpha> \<in> L M1 \<inter> (list.set X' \<union> {\<omega> @ \<omega>' |\<omega> \<omega>'. \<omega> \<in> {u @ [(x, y)], v @ [(x, y)]} \<and> \<omega>' \<in> list.set (prefixes (\<gamma> @ [(x', y')]))}) \<and> \<beta> \<in> L M1 \<inter> (list.set X' \<union> {\<omega> @ \<omega>' |\<omega> \<omega>'. \<omega> \<in> {u @ [(x, y)], v @ [(x, y)]} \<and> \<omega>' \<in> list.set (prefixes (\<gamma> @ [(x', y')]))})"
                  unfolding ** by auto
                then show "\<not>converge M2 \<alpha> \<beta>" proof cases
                  case 1
                  then show ?thesis using \<open>\<And> \<beta> . \<beta> \<in> L M1 \<inter> (list.set X \<union> {\<omega> @ \<omega>' |\<omega> \<omega>'. \<omega> \<in> {u, v} \<and> \<omega>' \<in> list.set (prefixes ((x, y) # \<gamma> @ [(x', y')]))}) \<Longrightarrow> \<not>converge M1 v \<beta> \<Longrightarrow> \<not>converge M2 v \<beta>\<close>
                    using \<open>\<not> converge M1 \<alpha> \<beta>\<close> by blast                
                next
                  case 2
                  then show ?thesis using \<open>\<And> \<beta> . \<beta> \<in> L M1 \<inter> (list.set X \<union> {\<omega> @ \<omega>' |\<omega> \<omega>'. \<omega> \<in> {u, v} \<and> \<omega>' \<in> list.set (prefixes ((x, y) # \<gamma> @ [(x', y')]))}) \<Longrightarrow> \<not>converge M1 v \<beta> \<Longrightarrow> \<not>converge M2 v \<beta>\<close>[of \<alpha>]
                    using \<open>\<not> converge M1 \<alpha> \<beta>\<close> 
                    unfolding converge_sym[of _ \<alpha>] by blast                
                next
                  case 3
                  then show ?thesis 
                    using preserve' \<open>\<not> converge M1 \<alpha> \<beta>\<close> 
                    unfolding preserves_divergence.simps by blast
                qed
              qed
              then show ?thesis
                unfolding preserves_divergence.simps 
                by blast
            qed 
          qed

          show "L M1 \<inter> (list.set X \<union> {\<omega> @ \<omega>' |\<omega> \<omega>'. \<omega> \<in> {u, v} \<and> \<omega>' \<in> list.set (prefixes ((x, y) # \<gamma> @ [(x', y')]))}) =
                      L M2 \<inter> (list.set X \<union> {\<omega> @ \<omega>' |\<omega> \<omega>'. \<omega> \<in> {u, v} \<and> \<omega>' \<in> list.set (prefixes ((x, y) # \<gamma> @ [(x', y')]))}) \<and>
                      preserves_divergence M1 M2 (list.set X \<union> {\<omega> @ \<omega>' |\<omega> \<omega>'. \<omega> \<in> {u, v} \<and> \<omega>' \<in> list.set (prefixes ((x, y) # \<gamma> @ [(x', y')]))})"
            using pass'' preserve''
            by presburger
        qed

        show ?thesis 
          using IH3 p2 p3 p4
          by blast
      qed
    qed

    have foldl_handleIO_subset: "\<And> XY T G . set T \<subseteq> set (fst (foldl handleIO (T,G) XY))"
    proof -
      fix XY T G 
      show "set T \<subseteq> set (fst (foldl handleIO (T,G) XY))"
      proof (induction XY rule: rev_induct)
        case Nil
        then show ?case by auto
      next
        case (snoc x xs)
        then show ?case 
          using handleIO_subset[of "fst (foldl handleIO (T, G) xs)" "snd (foldl handleIO (T, G) xs)" "fst x" "snd x"] 
          by force
      qed  
    qed


    have "list.set XY = inputs M1 \<times> outputs M1"
      unfolding XY
      by (metis inputs_as_list_set outputs_as_list_set set_product) 
    then have "list.set XY \<subseteq> inputs M1 \<times> outputs M1"
      by auto
    moreover have "L M1 \<inter> set (fst (foldl handleIO (fst TG'', snd TG'') XY)) = L M2 \<inter> set (fst (foldl handleIO (fst TG'', snd TG'') XY))"
      using pass_result by auto
    ultimately have foldl_handleIO_props: "convergence_graph_lookup_invar M1 M2 cg_lookup (snd (foldl handleIO (fst TG'', snd TG'') XY))
                                           \<and> (\<forall> x y . (x,y) \<in> list.set XY \<longrightarrow> 
                                                    L M1 \<inter> (list.set X \<union> {\<omega>@\<omega>' | \<omega> \<omega>' . \<omega> \<in> {u,v} \<and> \<omega>' \<in> list.set (prefixes [(x,y)])}) = L M2 \<inter> (list.set X \<union> {\<omega>@\<omega>' | \<omega> \<omega>' . \<omega> \<in> {u,v} \<and> \<omega>' \<in> list.set (prefixes [(x,y)])})    
                                                    \<and> preserves_divergence M1 M2 (list.set X \<union> {\<omega>@\<omega>' | \<omega> \<omega>' . \<omega> \<in> {u,v} \<and> \<omega>' \<in> list.set (prefixes [(x,y)])})
                                                    \<and> (\<forall> \<gamma> x' y' . length ((x,y)#\<gamma>@[(x',y')]) \<le> Suc depth \<longrightarrow>
                                                           ((x,y)#\<gamma>) \<in> LS M1 (after_initial M1 u) \<longrightarrow>
                                                          x' \<in> inputs M1 \<longrightarrow> y' \<in> outputs M1 \<longrightarrow>
                                                          L M1 \<inter> (list.set X \<union> {\<omega>@\<omega>' | \<omega> \<omega>' . \<omega> \<in> {u,v} \<and> \<omega>' \<in> list.set (prefixes ((x,y)#\<gamma>@[(x',y')]))}) = L M2 \<inter> (list.set X \<union> {\<omega>@\<omega>' | \<omega> \<omega>' . \<omega> \<in> {u,v} \<and> \<omega>' \<in> list.set (prefixes ((x,y)#\<gamma>@[(x',y')]))})
                                                          \<and> preserves_divergence M1 M2 (list.set X \<union> {\<omega>@\<omega>' | \<omega> \<omega>' . \<omega> \<in> {u,v} \<and> \<omega>' \<in> list.set (prefixes ((x,y)#\<gamma>@[(x',y')]))})))"
    proof (induction XY rule: rev_induct)
      case Nil

      have *:"(foldl handleIO (fst TG'', snd TG'') []) = (fst TG'', snd TG'')"
        by auto

      show ?case 
        using \<open>convergence_graph_lookup_invar M1 M2 cg_lookup (snd TG'')\<close>
        unfolding * snd_conv 
        by auto
    next
      case (snoc a XY)
      obtain x' y' where "a = (x',y')"
        using prod.exhaust by metis
      then have "x' \<in> inputs M1" and "y' \<in> outputs M1"
        using snoc.prems(1) by auto

      have "set T \<subseteq> set (fst TG'')"
        using \<open>Prefix_Tree.set (fst TG') \<subseteq> Prefix_Tree.set (fst TG'')\<close> \<open>Prefix_Tree.set T \<subseteq> Prefix_Tree.set (fst TG')\<close> by auto

      have "(foldl handleIO (fst TG'', snd TG'') (XY@[a])) = handleIO (foldl handleIO (fst TG'', snd TG'') XY) (x',y')"
        unfolding \<open>a = (x',y')\<close> by auto
      then have "set (fst (foldl handleIO (fst TG'', snd TG'') XY)) \<subseteq> set (fst (foldl handleIO (fst TG'', snd TG'') (XY@[a])))"
        using handleIO_subset
        by (metis prod.collapse) 
      then have pass_XY: "L M1 \<inter> set (fst (foldl handleIO (fst TG'', snd TG'') XY)) = L M2 \<inter> set (fst (foldl handleIO (fst TG'', snd TG'') XY))"
        using snoc.prems(2) by blast
      have "set T \<subseteq> set (fst (foldl handleIO (fst TG'', snd TG'') XY))"
        using foldl_handleIO_subset \<open>set T \<subseteq> set (fst TG'')\<close>
        by blast 

      have "list.set XY \<subseteq> FSM.inputs M1 \<times> FSM.outputs M1"
        using snoc.prems(1) by auto
      have "convergence_graph_lookup_invar M1 M2 cg_lookup (snd (foldl handleIO (fst TG'', snd TG'') XY))"
        using snoc.IH[OF \<open>list.set XY \<subseteq> FSM.inputs M1 \<times> FSM.outputs M1\<close> pass_XY] by blast
      have pass_aXY: "L M1 \<inter> Prefix_Tree.set (fst (handleIO (fst (foldl handleIO (fst TG'', snd TG'') XY), snd (foldl handleIO (fst TG'', snd TG'') XY)) (x',y') )) = L M2 \<inter> Prefix_Tree.set (fst (handleIO (fst (foldl handleIO (fst TG'', snd TG'') XY), snd (foldl handleIO (fst TG'', snd TG'') XY)) (x',y') ))"
        using snoc.prems(2) 
        unfolding \<open>(foldl handleIO (fst TG'', snd TG'') (XY@[a])) = handleIO (foldl handleIO (fst TG'', snd TG'') XY) (x',y')\<close> 
        unfolding prod.collapse .


      show ?case (is "?P1 \<and> ?P2")
      proof 
        show "convergence_graph_lookup_invar M1 M2 cg_lookup (snd (foldl handleIO (fst TG'', snd TG'') (XY@[a])))"
          using handleIO_props[OF \<open>set T \<subseteq> set (fst (foldl handleIO (fst TG'', snd TG'') XY))\<close> \<open>convergence_graph_lookup_invar M1 M2 cg_lookup (snd (foldl handleIO (fst TG'', snd TG'') XY))\<close> pass_aXY \<open>x' \<in> inputs M1\<close> \<open>y' \<in> outputs M1\<close>]
          unfolding \<open>(foldl handleIO (fst TG'', snd TG'') (XY@[a])) = handleIO (foldl handleIO (fst TG'', snd TG'') XY) (x',y')\<close> 
          unfolding prod.collapse
          by blast

        have "\<And> x y. (x, y) \<in> list.set (XY@[a]) \<Longrightarrow>
          L M1 \<inter> (list.set X \<union> {\<omega>@\<omega>' | \<omega> \<omega>' . \<omega> \<in> {u,v} \<and> \<omega>' \<in> list.set (prefixes [(x,y)])}) = L M2 \<inter> (list.set X \<union> {\<omega>@\<omega>' | \<omega> \<omega>' . \<omega> \<in> {u,v} \<and> \<omega>' \<in> list.set (prefixes [(x,y)])}) \<and>
          preserves_divergence M1 M2 (list.set X \<union> {\<omega> @ \<omega>' |\<omega> \<omega>'. \<omega> \<in> {u, v} \<and> \<omega>' \<in> list.set (prefixes [(x, y)])}) \<and>
          (\<forall>\<gamma> x' y'.
              length ((x, y) # \<gamma> @ [(x', y')]) \<le> Suc depth \<longrightarrow>
              (x, y) # \<gamma> \<in> LS M1 (after_initial M1 u) \<longrightarrow>
              x' \<in> FSM.inputs M1 \<longrightarrow>
              y' \<in> FSM.outputs M1 \<longrightarrow>
              L M1 \<inter> (list.set X \<union> {\<omega> @ \<omega>' |\<omega> \<omega>'. \<omega> \<in> {u, v} \<and> \<omega>' \<in> list.set (prefixes ((x, y) # \<gamma> @ [(x', y')]))}) =
              L M2 \<inter> (list.set X \<union> {\<omega> @ \<omega>' |\<omega> \<omega>'. \<omega> \<in> {u, v} \<and> \<omega>' \<in> list.set (prefixes ((x, y) # \<gamma> @ [(x', y')]))}) \<and>
              preserves_divergence M1 M2 (list.set X \<union> {\<omega> @ \<omega>' |\<omega> \<omega>'. \<omega> \<in> {u, v} \<and> \<omega>' \<in> list.set (prefixes ((x, y) # \<gamma> @ [(x', y')]))}))"
        proof -
          fix x y assume "(x, y) \<in> list.set (XY@[a])"

          show "L M1 \<inter> (list.set X \<union> {\<omega>@\<omega>' | \<omega> \<omega>' . \<omega> \<in> {u,v} \<and> \<omega>' \<in> list.set (prefixes [(x,y)])}) = L M2 \<inter> (list.set X \<union> {\<omega>@\<omega>' | \<omega> \<omega>' . \<omega> \<in> {u,v} \<and> \<omega>' \<in> list.set (prefixes [(x,y)])}) \<and>
                preserves_divergence M1 M2 (list.set X \<union> {\<omega> @ \<omega>' |\<omega> \<omega>'. \<omega> \<in> {u, v} \<and> \<omega>' \<in> list.set (prefixes [(x, y)])}) \<and>
                  (\<forall>\<gamma> x' y'.
                      length ((x, y) # \<gamma> @ [(x', y')]) \<le> Suc depth \<longrightarrow>
                      (x, y) # \<gamma> \<in> LS M1 (after_initial M1 u) \<longrightarrow>
                      x' \<in> FSM.inputs M1 \<longrightarrow>
                      y' \<in> FSM.outputs M1 \<longrightarrow>
                      L M1 \<inter> (list.set X \<union> {\<omega> @ \<omega>' |\<omega> \<omega>'. \<omega> \<in> {u, v} \<and> \<omega>' \<in> list.set (prefixes ((x, y) # \<gamma> @ [(x', y')]))}) =
                      L M2 \<inter> (list.set X \<union> {\<omega> @ \<omega>' |\<omega> \<omega>'. \<omega> \<in> {u, v} \<and> \<omega>' \<in> list.set (prefixes ((x, y) # \<gamma> @ [(x', y')]))}) \<and>
                      preserves_divergence M1 M2 (list.set X \<union> {\<omega> @ \<omega>' |\<omega> \<omega>'. \<omega> \<in> {u, v} \<and> \<omega>' \<in> list.set (prefixes ((x, y) # \<gamma> @ [(x', y')]))}))"
          proof (cases "a = (x,y)")
            case True
            then have *:"(x',y') = (x,y)"
              using \<open>a = (x',y')\<close> by auto

            show ?thesis
              using handleIO_props[OF \<open>set T \<subseteq> set (fst (foldl handleIO (fst TG'', snd TG'') XY))\<close> \<open>convergence_graph_lookup_invar M1 M2 cg_lookup (snd (foldl handleIO (fst TG'', snd TG'') XY))\<close> pass_aXY \<open>x' \<in> inputs M1\<close> \<open>y' \<in> outputs M1\<close>]
              unfolding \<open>(foldl handleIO (fst TG'', snd TG'') (XY@[a])) = handleIO (foldl handleIO (fst TG'', snd TG'') XY) (x',y')\<close> 
              unfolding prod.collapse * 
              by presburger
          next
            case False
            then have "(x,y) \<in> list.set XY"
              using \<open>(x, y) \<in> list.set (XY@[a])\<close> by auto
            
            then show ?thesis 
              using snoc.IH[OF \<open>list.set XY \<subseteq> FSM.inputs M1 \<times> FSM.outputs M1\<close> pass_XY]
              by presburger
          qed
        qed
        then show "?P2"
          by blast
      qed
    qed

    have "\<And> x y . (x,y) \<in> list.set XY = (x \<in> inputs M1 \<and> y \<in> outputs M1)"
      unfolding \<open>list.set XY = inputs M1 \<times> outputs M1\<close> by auto

    have result_props_1: "\<And> x y \<gamma> x' y'. x \<in> inputs M1 \<Longrightarrow> y \<in> outputs M1 \<Longrightarrow>
             length ((x, y) # \<gamma> @ [(x', y')]) \<le> Suc depth \<Longrightarrow>
             (x, y) # \<gamma> \<in> LS M1 (after_initial M1 u) \<Longrightarrow>
             x' \<in> FSM.inputs M1 \<Longrightarrow>
             y' \<in> FSM.outputs M1 \<Longrightarrow>
             L M1 \<inter> (list.set X \<union> {\<omega> @ \<omega>' |\<omega> \<omega>'. \<omega> \<in> {u, v} \<and> \<omega>' \<in> list.set (prefixes ((x, y) # \<gamma> @ [(x', y')]))}) =
             L M2 \<inter> (list.set X \<union> {\<omega> @ \<omega>' |\<omega> \<omega>'. \<omega> \<in> {u, v} \<and> \<omega>' \<in> list.set (prefixes ((x, y) # \<gamma> @ [(x', y')]))}) \<and>
             preserves_divergence M1 M2 (list.set X \<union> {\<omega> @ \<omega>' |\<omega> \<omega>'. \<omega> \<in> {u, v} \<and> \<omega>' \<in> list.set (prefixes ((x, y) # \<gamma> @ [(x', y')]))})"
      using foldl_handleIO_props
      unfolding \<open>\<And> x y . (x,y) \<in> list.set XY = (x \<in> inputs M1 \<and> y \<in> outputs M1)\<close>
      by blast


    have "?P1a X u v (Suc depth)"
    proof -
      have "\<And> \<gamma> x y.
               length (\<gamma> @ [(x, y)]) \<le> Suc depth \<Longrightarrow>
               \<gamma> \<in> LS M1 (after_initial M1 u) \<Longrightarrow>
               x \<in> FSM.inputs M1 \<Longrightarrow>
               y \<in> FSM.outputs M1 \<Longrightarrow>
               L M1 \<inter> (list.set X \<union> {\<omega> @ \<omega>' |\<omega> \<omega>'. \<omega> \<in> {u, v} \<and> \<omega>' \<in> list.set (prefixes (\<gamma> @ [(x, y)]))}) =
               L M2 \<inter> (list.set X \<union> {\<omega> @ \<omega>' |\<omega> \<omega>'. \<omega> \<in> {u, v} \<and> \<omega>' \<in> list.set (prefixes (\<gamma> @ [(x, y)]))}) \<and>
               preserves_divergence M1 M2 (list.set X \<union> {\<omega> @ \<omega>' |\<omega> \<omega>'. \<omega> \<in> {u, v} \<and> \<omega>' \<in> list.set (prefixes (\<gamma> @ [(x, y)]))})"
      proof -
        fix \<gamma> x y
        assume "length (\<gamma> @ [(x, y)]) \<le> Suc depth"
               "\<gamma> \<in> LS M1 (after_initial M1 u)"
               "x \<in> FSM.inputs M1"
               "y \<in> FSM.outputs M1"

        show "L M1 \<inter> (list.set X \<union> {\<omega> @ \<omega>' |\<omega> \<omega>'. \<omega> \<in> {u, v} \<and> \<omega>' \<in> list.set (prefixes (\<gamma> @ [(x, y)]))}) =
               L M2 \<inter> (list.set X \<union> {\<omega> @ \<omega>' |\<omega> \<omega>'. \<omega> \<in> {u, v} \<and> \<omega>' \<in> list.set (prefixes (\<gamma> @ [(x, y)]))}) \<and>
               preserves_divergence M1 M2 (list.set X \<union> {\<omega> @ \<omega>' |\<omega> \<omega>'. \<omega> \<in> {u, v} \<and> \<omega>' \<in> list.set (prefixes (\<gamma> @ [(x, y)]))})"
        proof (cases \<gamma>)
          case Nil
          then have *:"\<gamma> @ [(x,y)] = [(x,y)]"
            by auto
          have "(x,y) \<in> list.set XY"
            unfolding \<open>list.set XY = inputs M1 \<times> outputs M1\<close>
            using \<open>x \<in> FSM.inputs M1\<close> \<open>y \<in> FSM.outputs M1\<close>
            by auto
          show ?thesis
            unfolding * 
            using foldl_handleIO_props  \<open>(x,y) \<in> list.set XY\<close>
            by presburger
        next
          case (Cons a \<gamma>')
          obtain x' y' where "a = (x',y')"
            using prod.exhaust by metis
          then have *: "\<gamma> = (x',y')#\<gamma>'"
            unfolding Cons by auto
          then have **: "\<gamma> @ [(x, y)] = (x',y')#\<gamma>'@ [(x, y)]"
            by auto

          have \<open>x' \<in> inputs M1\<close> \<open>y' \<in> outputs M1\<close>
            using language_io[OF \<open>\<gamma> \<in> LS M1 (after_initial M1 u)\<close>, of x' y']
            unfolding * 
            by auto
          have "length ((x', y') # (\<gamma>' @ [(x, y)])) \<le> Suc depth"
            using \<open>length (\<gamma> @ [(x, y)]) \<le> Suc depth\<close> unfolding * by auto
          have "(x', y') # \<gamma>' \<in> LS M1 (after_initial M1 u)"
            using \<open>\<gamma> \<in> LS M1 (after_initial M1 u)\<close> unfolding * .

          show ?thesis 
            using result_props_1[OF \<open>x' \<in> inputs M1\<close> \<open>y' \<in> outputs M1\<close> \<open>length ((x', y') # (\<gamma>' @ [(x, y)])) \<le> Suc depth\<close> \<open>(x', y') # \<gamma>' \<in> LS M1 (after_initial M1 u)\<close> \<open>x \<in> FSM.inputs M1\<close> \<open>y \<in> outputs M1\<close>]
            unfolding ** .
        qed
      qed
      then show ?thesis by blast
    qed

    moreover have "?P1b X u v"
      using \<open>preserves_divergence M1 M2 (Set.insert u (Set.insert v (list.set X)))\<close> by auto
            
    moreover have "?P2 T G u v X (Suc depth)"
      using foldl_handleIO_props
      unfolding result prod.collapse 
      by blast
    
    ultimately show ?case
      by blast
  qed

  then show "?P1a X u v depth" and "?P1b X u v" and "?P2 T G u v X depth"
    by presburger+
qed


lemma distinguish_from_set_establishes_convergence :
  assumes "observable M1"
      and "observable M2"
      and "minimal M1"
      and "minimal M2"
      and "size_r M1 \<le> m"
      and "size M2 \<le> m"
      and "inputs M2 = inputs M1"
      and "outputs M2 = outputs M1"
      and "is_state_cover_assignment M1 V"
      and "preserves_divergence M1 M2 (V ` reachable_states M1)"
      and "L M1 \<inter> (V ` reachable_states M1) = L M2 \<inter> V ` reachable_states M1"
      and "converge M1 u v"
      and "u \<in> L M2"
      and "v \<in> L M2"
      and "convergence_graph_lookup_invar M1 M2 cg_lookup G"
      and "convergence_graph_insert_invar M1 M2 cg_lookup cg_insert"
      and "\<And> q1 q2 . q1 \<in> states M1 \<Longrightarrow> q2 \<in> states M1 \<Longrightarrow> q1 \<noteq> q2 \<Longrightarrow> distinguishes M1 q1 q2 (get_distinguishing_trace q1 q2)"
      and "L M1 \<inter> set (fst (distinguish_from_set M1 V T G cg_lookup cg_insert get_distinguishing_trace u v (map V (reachable_states_as_list M1)) k (m - size_r M1) completeInputTraces append_heuristic (u=v))) = L M2 \<inter> set (fst (distinguish_from_set M1 V T G cg_lookup cg_insert get_distinguishing_trace u v (map V (reachable_states_as_list M1)) k (m - size_r M1) completeInputTraces append_heuristic (u=v)))"
      and "\<And> T w u' uBest lBest . fst (append_heuristic T w (uBest,lBest) u') \<in> {u',uBest}"
shows "converge M2 u v"
  and "convergence_graph_lookup_invar M1 M2 cg_lookup (snd (distinguish_from_set M1 V T G cg_lookup cg_insert get_distinguishing_trace u v (map V (reachable_states_as_list M1)) k (m - size_r M1) completeInputTraces append_heuristic (u=v)))"
proof -
  have d1: "V ` reachable_states M1 \<subseteq> list.set (map V (reachable_states_as_list M1))"
    using reachable_states_as_list_set by auto 
  have d2: "preserves_divergence M1 M2 (list.set (map V (reachable_states_as_list M1)))"
    using assms(10) reachable_states_as_list_set
    by (metis image_set) 
  have d3: "(\<And>w. w \<in> list.set (map V (reachable_states_as_list M1)) \<Longrightarrow> \<exists>w'. converge M1 w w' \<and> converge M2 w w')"
  proof -
    fix w assume "w \<in> list.set (map V (reachable_states_as_list M1))"
    then have "w \<in> V ` reachable_states M1"
      using reachable_states_as_list_set by auto
    moreover have "w \<in> L M1"
      by (metis assms(1) assms(9) calculation image_iff state_cover_assignment_after(1))
    ultimately have "w \<in> L M2"
      using assms(11) by blast

    have "converge M1 w w"
      using \<open>w \<in> L M1\<close> by auto
    moreover have "converge M2 w w"
      using \<open>w \<in> L M2\<close> by auto
    ultimately show "\<exists>w'. converge M1 w w' \<and> converge M2 w w'"
      by blast
  qed

  have "list.set (map V (reachable_states_as_list M1)) = V ` reachable_states M1"
    using reachable_states_as_list_set by auto


  have prop1: "\<And>\<gamma> x y.
     length (\<gamma> @ [(x, y)]) \<le> (m - size_r M1) \<Longrightarrow>
     \<gamma> \<in> LS M1 (after_initial M1 u) \<Longrightarrow>
     x \<in> FSM.inputs M1 \<Longrightarrow>
     y \<in> FSM.outputs M1 \<Longrightarrow>
     L M1 \<inter> (V ` reachable_states M1 \<union> {\<omega> @ \<omega>' |\<omega> \<omega>'. \<omega> \<in> {u, v} \<and> \<omega>' \<in> list.set (prefixes (\<gamma> @ [(x, y)]))}) =
     L M2 \<inter> (V ` reachable_states M1 \<union> {\<omega> @ \<omega>' |\<omega> \<omega>'. \<omega> \<in> {u, v} \<and> \<omega>' \<in> list.set (prefixes (\<gamma> @ [(x, y)]))}) \<and>
     preserves_divergence M1 M2
      (V ` reachable_states M1 \<union> {\<omega> @ \<omega>' |\<omega> \<omega>'. \<omega> \<in> {u, v} \<and> \<omega>' \<in> list.set (prefixes (\<gamma> @ [(x, y)]))})"
  and prop2: "preserves_divergence M1 M2 (V ` reachable_states M1 \<union> {u, v})"
  and prop3: "convergence_graph_lookup_invar M1 M2 cg_lookup (snd (distinguish_from_set M1 V T G cg_lookup cg_insert get_distinguishing_trace u v (map V (reachable_states_as_list M1)) k (m - size_r M1) completeInputTraces append_heuristic (u=v)))"
    using distinguish_from_set_properties[OF assms(1-4,7,8,9) d1 d2 d3 assms(12-19)]
    unfolding \<open>list.set (map V (reachable_states_as_list M1)) = V ` reachable_states M1\<close>
    by presburger+
  then show "convergence_graph_lookup_invar M1 M2 cg_lookup (snd (distinguish_from_set M1 V T G cg_lookup cg_insert get_distinguishing_trace u v (map V (reachable_states_as_list M1)) k (m - size_r M1) completeInputTraces append_heuristic (u=v)))"
    by presburger

  show "converge M2 u v"
    using establish_convergence_from_pass[OF assms(1-9,11-14) prop1 prop2]
    by blast
qed


definition establish_convergence_dynamic :: "bool \<Rightarrow> bool \<Rightarrow> ('a \<Rightarrow> 'a \<Rightarrow> ('b \<times> 'c) list) \<Rightarrow> 
                                  ('a::linorder,'b::linorder,'c::linorder) fsm \<Rightarrow>
                                  ('a,'b,'c) state_cover_assignment \<Rightarrow>
                                  ('b\<times>'c) prefix_tree \<Rightarrow> 
                                  'd \<Rightarrow>
                                  ('d \<Rightarrow> ('b\<times>'c) list \<Rightarrow> 'd) \<Rightarrow>
                                  ('d \<Rightarrow> ('b\<times>'c) list \<Rightarrow> ('b\<times>'c) list list) \<Rightarrow> 
                                  nat \<Rightarrow>
                                  ('a,'b,'c) transition \<Rightarrow>  
                                  (('b\<times>'c) prefix_tree \<times> 'd)" where
  "establish_convergence_dynamic completeInputTraces useInputHeuristic dist_fun M1 V T G cg_insert cg_lookup m t = 
    distinguish_from_set M1 V T G cg_lookup cg_insert 
                         dist_fun
                         ((V (t_source t))@[(t_input t, t_output t)]) 
                         (V (t_target t)) 
                         (map V (reachable_states_as_list M1)) 
                         (2 * size M1) 
                         (m - size_r M1) 
                         completeInputTraces
                         (if useInputHeuristic then append_heuristic_input M1 else append_heuristic_io)
                         False"


lemma establish_convergence_dynamic_verifies_transition :
  assumes "\<And> q1 q2 . q1 \<in> states M1 \<Longrightarrow> q2 \<in> states M1 \<Longrightarrow> q1 \<noteq> q2 \<Longrightarrow> distinguishes M1 q1 q2 (dist_fun q1 q2)"
  shows "verifies_transition (establish_convergence_dynamic b c dist_fun) M1 M2 V T0 cg_insert cg_lookup"
proof -
  have *:"\<And> (M1::('a::linorder,'b::linorder,'c::linorder) fsm) V T (G::'d) cg_insert cg_lookup m t. Prefix_Tree.set T \<subseteq> Prefix_Tree.set (fst (establish_convergence_dynamic b c dist_fun M1 V T G cg_insert cg_lookup m t))"
    using distinguish_from_set_subset unfolding establish_convergence_dynamic_def
    by metis 

  have ***:"\<And> (M1::('a::linorder,'b::linorder,'c::linorder) fsm) V T (G::'d) cg_insert cg_lookup m t. finite_tree T \<longrightarrow> finite_tree (fst (establish_convergence_dynamic b c dist_fun M1 V T G cg_insert cg_lookup m t))"
    using distinguish_from_set_finite unfolding establish_convergence_dynamic_def
    by metis 

  have **:"\<And> V T (G::'d) cg_insert cg_lookup m t.
        observable M1 \<Longrightarrow>
        observable M2 \<Longrightarrow>
        minimal M1 \<Longrightarrow>
        minimal M2 \<Longrightarrow>
        size_r M1 \<le> m \<Longrightarrow>
        FSM.size M2 \<le> m \<Longrightarrow>
        FSM.inputs M2 = FSM.inputs M1 \<Longrightarrow>
        FSM.outputs M2 = FSM.outputs M1 \<Longrightarrow>
        is_state_cover_assignment M1 V \<Longrightarrow>
        preserves_divergence M1 M2 (V ` reachable_states M1) \<Longrightarrow>
        V ` reachable_states M1 \<subseteq> set T \<Longrightarrow>
        t \<in> FSM.transitions M1 \<Longrightarrow>
        t_source t \<in> reachable_states M1 \<Longrightarrow>
        ((V (t_source t)) @ [(t_input t,t_output t)]) \<noteq> (V (t_target t)) \<Longrightarrow>
        V (t_source t) @ [(t_input t, t_output t)] \<in> L M2 \<Longrightarrow>
        convergence_graph_lookup_invar M1 M2 cg_lookup G \<Longrightarrow>
        convergence_graph_insert_invar M1 M2 cg_lookup cg_insert \<Longrightarrow>
        L M1 \<inter> Prefix_Tree.set (fst (establish_convergence_dynamic b c dist_fun M1 V T G cg_insert cg_lookup m t)) =
        L M2 \<inter> Prefix_Tree.set (fst (establish_convergence_dynamic b c dist_fun M1 V T G cg_insert cg_lookup m t)) \<Longrightarrow>
        converge M2 (V (t_source t) @ [(t_input t, t_output t)]) (V (t_target t)) \<and>
        convergence_graph_lookup_invar M1 M2 cg_lookup (snd (establish_convergence_dynamic b c dist_fun M1 V T G cg_insert cg_lookup m t))"
  proof -
    
    fix G :: 'd
    fix V T cg_insert cg_lookup m t
    assume a01: "observable M1"
    assume a02: "observable M2"
    assume a03: "minimal M1"
    assume a04: "minimal M2"
    assume a05: "size_r M1 \<le> m"
    assume a06: "FSM.size M2 \<le> m"
    assume a07: "FSM.inputs M2 = FSM.inputs M1"
    assume a08: "FSM.outputs M2 = FSM.outputs M1"
    assume a09: "is_state_cover_assignment M1 V"
    assume a10: "preserves_divergence M1 M2 (V ` reachable_states M1)"
    assume a11: "V ` reachable_states M1 \<subseteq> set T"
    assume a12: "t \<in> FSM.transitions M1"
    assume a13: "t_source t \<in> reachable_states M1"
    assume a14: "V (t_source t) @ [(t_input t, t_output t)] \<in> L M2"
    assume a15: "convergence_graph_lookup_invar M1 M2 cg_lookup G"
    assume a16: "convergence_graph_insert_invar M1 M2 cg_lookup cg_insert"
    assume a17: "L M1 \<inter> Prefix_Tree.set (fst (establish_convergence_dynamic b c dist_fun M1 V T G cg_insert cg_lookup m t)) = L M2 \<inter> Prefix_Tree.set (fst (establish_convergence_dynamic b c dist_fun M1 V T G cg_insert cg_lookup m t))"
    assume a18: "((V (t_source t)) @ [(t_input t,t_output t)]) \<noteq> (V (t_target t))"

    let ?heuristic = "(if c then append_heuristic_input M1 else append_heuristic_io)"

    have d2: "converge M1 (V (t_source t) @ [(t_input t, t_output t)]) (V (t_target t))"
      using state_cover_transition_converges[OF a01 a09 a12 a13] .

    have d1: "L M1 \<inter> V ` reachable_states M1 = L M2 \<inter> V ` reachable_states M1"
      using a11 a17 *[of T M1 V G cg_insert cg_lookup m t]
      by blast

    then have d3: "V (t_target t) \<in> L M2"
      using a11 is_state_cover_assignment_language[OF a09, of "t_target t"] reachable_states_next[OF a13 a12] by auto

    have d5: "L M1 \<inter> Prefix_Tree.set  (fst (distinguish_from_set M1 V T G cg_lookup cg_insert dist_fun (V (t_source t) @ [(t_input t, t_output t)]) (V (t_target t)) (map V (reachable_states_as_list M1)) (2 * size M1) (m - size_r M1) b ?heuristic (((V (t_source t)) @ [(t_input t,t_output t)]) = (V (t_target t))))) = L M2 \<inter> Prefix_Tree.set (fst (distinguish_from_set M1 V T G cg_lookup cg_insert dist_fun (V (t_source t) @ [(t_input t, t_output t)]) (V (t_target t)) (map V (reachable_states_as_list M1)) (2 * size M1) (m - size_r M1) b ?heuristic (((V (t_source t)) @ [(t_input t,t_output t)]) = (V (t_target t)))))"
      using a17 a18 unfolding establish_convergence_dynamic_def by force

    have d6: "(\<And>T w u' uBest lBest. fst (?heuristic T w (uBest, lBest) u') \<in> {u', uBest})"
      using append_heuristic_input_in[of M1] append_heuristic_io_in
      by fastforce
    
    show "converge M2 (V (t_source t) @ [(t_input t, t_output t)]) (V (t_target t)) \<and>
          convergence_graph_lookup_invar M1 M2 cg_lookup (snd (establish_convergence_dynamic b c dist_fun M1 V T G cg_insert cg_lookup m t))"
      using distinguish_from_set_establishes_convergence[OF a01 a02 a03 a04 a05 a06 a07 a08 a09 a10 d1 d2 a14 d3 a15 a16 assms d5 d6] a18
      unfolding establish_convergence_dynamic_def by force
  qed

  show ?thesis
    unfolding verifies_transition_def
    using * *** ** by presburger
qed



definition handleUT_dynamic :: "bool \<Rightarrow> 
                                   bool \<Rightarrow> 
                                   ('a \<Rightarrow> 'a \<Rightarrow> ('b \<times> 'c) list) \<Rightarrow> 
                                   (('a,'b,'c) fsm \<Rightarrow> ('a,'b,'c) state_cover_assignment \<Rightarrow> ('a,'b,'c) transition \<Rightarrow> ('a,'b,'c) transition list \<Rightarrow> nat \<Rightarrow> bool) \<Rightarrow>
                                   ('a::linorder,'b::linorder,'c::linorder) fsm \<Rightarrow>
                                   ('a,'b,'c) state_cover_assignment \<Rightarrow>
                                   ('b\<times>'c) prefix_tree \<Rightarrow> 
                                   'd \<Rightarrow>
                                   ('d \<Rightarrow> ('b\<times>'c) list \<Rightarrow> 'd) \<Rightarrow>
                                   ('d \<Rightarrow> ('b\<times>'c) list \<Rightarrow> ('b\<times>'c) list list) \<Rightarrow>  
                                   ('d \<Rightarrow> ('b\<times>'c) list \<Rightarrow> ('b\<times>'c) list \<Rightarrow> 'd) \<Rightarrow>
                                   nat \<Rightarrow>
                                   ('a,'b,'c) transition \<Rightarrow>  
                                   ('a,'b,'c) transition list \<Rightarrow>
                                   (('a,'b,'c) transition list \<times> ('b\<times>'c) prefix_tree \<times> 'd)" 
  where
  "handleUT_dynamic complete_input_traces 
                       use_input_heuristic 
                       dist_fun 
                       do_establish_convergence 
                       M 
                       V 
                       T 
                       G 
                       cg_insert 
                       cg_lookup 
                       cg_merge 
                       m 
                       t
                       X 
    = 
    (let k         = (2 * size M); 
         l         = (m - size_r M); 
         heuristic = (if use_input_heuristic then append_heuristic_input M 
                                             else append_heuristic_io);
         rstates   = (map V (reachable_states_as_list M));
         (T1,G1)   = handle_io_pair complete_input_traces 
                                    use_input_heuristic 
                                    M 
                                    V 
                                    T 
                                    G 
                                    cg_insert 
                                    cg_lookup 
                                    (t_source t) 
                                    (t_input t) 
                                    (t_output t);
         u         = ((V (t_source t))@[(t_input t, t_output t)]);
         v         = (V (t_target t));
         X'        = butlast X  
      in if (do_establish_convergence M V t X' l)
          then let (T2,G2) = distinguish_from_set M 
                                                  V
                                                  T1 
                                                  G1 
                                                  cg_lookup 
                                                  cg_insert 
                                                  dist_fun
                                                  u 
                                                  v
                                                  rstates 
                                                  k 
                                                  l 
                                                  complete_input_traces
                                                  heuristic
                                                  False;
                  G3 = cg_merge G2 u v  
               in
                  (X',T2,G3) 
          else (X',distinguish_from_set M 
                                        V
                                        T1 
                                        G1 
                                        cg_lookup 
                                        cg_insert 
                                        dist_fun
                                        u
                                        u 
                                        rstates 
                                        k 
                                        l 
                                        complete_input_traces
                                        heuristic
                                        True))"


lemma handleUT_dynamic_handles_transition :
  fixes M1::"('a::linorder,'b::linorder,'c::linorder) fsm"
  fixes M2::"('e,'b,'c) fsm"
  assumes "\<And> q1 q2 . q1 \<in> states M1 \<Longrightarrow> q2 \<in> states M1 \<Longrightarrow> q1 \<noteq> q2 \<Longrightarrow> distinguishes M1 q1 q2 (dist_fun q1 q2)"
  shows "handles_transition (handleUT_dynamic b c dist_fun d) M1 M2 V T0 cg_insert cg_lookup cg_merge"
proof -       

  have "\<And> T G m t X . 
       Prefix_Tree.set T \<subseteq> Prefix_Tree.set (fst (snd (handleUT_dynamic b c dist_fun d M1 V T G cg_insert cg_lookup cg_merge m t X))) \<and>
       (finite_tree T \<longrightarrow> finite_tree (fst (snd (handleUT_dynamic b c dist_fun d M1 V T G cg_insert cg_lookup cg_merge m t X)))) \<and>
       (observable M1 \<longrightarrow>
        observable M2 \<longrightarrow>
        minimal M1 \<longrightarrow>
        minimal M2 \<longrightarrow>
        size_r M1 \<le> m \<longrightarrow>
        FSM.size M2 \<le> m \<longrightarrow>
        FSM.inputs M2 = FSM.inputs M1 \<longrightarrow>
        FSM.outputs M2 = FSM.outputs M1 \<longrightarrow>
        is_state_cover_assignment M1 V \<longrightarrow>
        preserves_divergence M1 M2 (V ` reachable_states M1) \<longrightarrow>
        V ` reachable_states M1 \<subseteq> Prefix_Tree.set T \<longrightarrow>
        t \<in> FSM.transitions M1 \<longrightarrow>
        t_source t \<in> reachable_states M1 \<longrightarrow>
        V (t_source t) @ [(t_input t, t_output t)] \<noteq> V (t_target t) \<longrightarrow>
        convergence_graph_lookup_invar M1 M2 cg_lookup G \<longrightarrow>
        convergence_graph_insert_invar M1 M2 cg_lookup cg_insert \<longrightarrow>
        convergence_graph_merge_invar M1 M2 cg_lookup cg_merge \<longrightarrow>
        L M1 \<inter> Prefix_Tree.set (fst (snd (handleUT_dynamic b c dist_fun d M1 V T G cg_insert cg_lookup cg_merge m t X))) =
        L M2 \<inter> Prefix_Tree.set (fst (snd (handleUT_dynamic b c dist_fun d M1 V T G cg_insert cg_lookup cg_merge m t X))) \<longrightarrow>
        Prefix_Tree.set T0 \<subseteq> Prefix_Tree.set T \<longrightarrow>
        (\<forall>\<gamma>. length \<gamma> \<le> m - size_r M1 \<and> list.set \<gamma> \<subseteq> FSM.inputs M1 \<times> FSM.outputs M1 \<and> butlast \<gamma> \<in> LS M1 (t_target t) \<longrightarrow>
             L M1 \<inter> (V ` reachable_states M1 \<union> {(V (t_source t) @ [(t_input t, t_output t)]) @ \<omega>' |\<omega>'. \<omega>' \<in> list.set (prefixes \<gamma>)}) =
             L M2 \<inter> (V ` reachable_states M1 \<union> {(V (t_source t) @ [(t_input t, t_output t)]) @ \<omega>' |\<omega>'. \<omega>' \<in> list.set (prefixes \<gamma>)}) \<and>
             preserves_divergence M1 M2 (V ` reachable_states M1 \<union> {(V (t_source t) @ [(t_input t, t_output t)]) @ \<omega>' |\<omega>'. \<omega>' \<in> list.set (prefixes \<gamma>)})) \<and>
        convergence_graph_lookup_invar M1 M2 cg_lookup (snd (snd (handleUT_dynamic b c dist_fun d M1 V T G cg_insert cg_lookup cg_merge m t X))))"
    (is "\<And> T G m t X . ?P T G m t X")
  proof -

    fix T :: "('b\<times>'c) prefix_tree"
    fix G :: 'd
    fix m :: nat
    fix t :: "('a,'b,'c) transition"
    fix X :: "('a,'b,'c) transition list"
  
    let ?TG = "snd (handleUT_dynamic b c dist_fun d M1 V T G cg_insert cg_lookup cg_merge m t X)"

    define k where "k = (2 * size M1)"
    define l where "l = (m - size_r M1)"
    define X' where "X' = butlast X"
    define heuristic where "heuristic = (if c then append_heuristic_input M1 else append_heuristic_io)"
    define rstates where "rstates   = (map V (reachable_states_as_list M1))"
    obtain T1 G1 where "(T1,G1)   = handle_io_pair b c M1 V T G cg_insert cg_lookup (t_source t) (t_input t) (t_output t)"
      using prod.collapse by blast
    then have T1_def: "T1 = fst (handle_io_pair b c M1 V T G cg_insert cg_lookup (t_source t) (t_input t) (t_output t))"
         and  G1_def: "G1 = snd (handle_io_pair b c M1 V T G cg_insert cg_lookup (t_source t) (t_input t) (t_output t))"
      using fst_conv[of T1 G1] snd_conv[of T1 G1] by force+
    define u where "u         = ((V (t_source t))@[(t_input t, t_output t)])"
    define v where "v         = (V (t_target t))"

    obtain T2 G2 where "(T2,G2) = distinguish_from_set M1 V T1 G1 cg_lookup cg_insert dist_fun u v rstates k l b heuristic False"
      using prod.collapse by blast
    then have T2_def: "T2 = fst (distinguish_from_set M1 V T1 G1 cg_lookup cg_insert dist_fun u v rstates k l b heuristic False)"
         and  G2_def: "G2 = snd (distinguish_from_set M1 V T1 G1 cg_lookup cg_insert dist_fun u v rstates k l b heuristic False)"
      using fst_conv[of T2 G2] snd_conv[of T2 G2] by force+

    define G3 where "G3 = cg_merge G2 u v"

    obtain TH GH where "(TH,GH) = distinguish_from_set M1 V T1 G1 cg_lookup cg_insert dist_fun u u rstates k l b heuristic True" 
    using prod.collapse by blast
    then have TH_def: "TH = fst (distinguish_from_set M1 V T1 G1 cg_lookup cg_insert dist_fun u u rstates k l b heuristic True)"
         and  GH_def: "GH = snd (distinguish_from_set M1 V T1 G1 cg_lookup cg_insert dist_fun u u rstates k l b heuristic True)"
      using fst_conv[of TH GH] snd_conv[of TH GH] by force+

    have TG_cases: "?TG = (if (d M1 V t X' l) then (T2,G3) else (TH,GH))"
      unfolding handleUT_dynamic_def Let_def
      unfolding u_def[symmetric] v_def[symmetric] rstates_def[symmetric] k_def[symmetric] l_def[symmetric] heuristic_def[symmetric]
      unfolding \<open>(T1,G1)   = handle_io_pair b c M1 V T G cg_insert cg_lookup (t_source t) (t_input t) (t_output t)\<close>[symmetric] case_prod_conv
      unfolding \<open>(T2,G2) = distinguish_from_set M1 V T1 G1 cg_lookup cg_insert dist_fun u v rstates k l b heuristic False\<close>[symmetric] case_prod_conv
      unfolding G3_def[symmetric]
      unfolding \<open>(TH,GH) = distinguish_from_set M1 V T1 G1 cg_lookup cg_insert dist_fun u u rstates k l b heuristic True\<close>[symmetric]
      unfolding X'_def[symmetric]
      by auto
    then have TG_cases_fst: "fst ?TG = (if (d M1 V t X' l) then T2 else TH)"
         and  TG_cases_snd: "snd ?TG = (if (d M1 V t X' l) then G3 else GH)"
      by auto


    have "set T \<subseteq> set T1" 
      unfolding T1_def handle_io_pair_def
      by (metis distribute_extension_subset) 
    moreover have "set T1 \<subseteq> set T2"
      unfolding T2_def
      by (meson distinguish_from_set_subset) 
    moreover have "set T1 \<subseteq> set TH"
      unfolding TH_def
      by (meson distinguish_from_set_subset) 
    ultimately have *:"set T \<subseteq> set (fst ?TG)"
      using TG_cases by auto

    have "finite_tree T \<Longrightarrow> finite_tree T1"
      unfolding T1_def handle_io_pair_def
      by (metis distribute_extension_finite) 
    moreover have "finite_tree T1 \<Longrightarrow> finite_tree T2"
      unfolding T2_def
      by (meson distinguish_from_set_finite) 
    moreover have "finite_tree T1 \<Longrightarrow> finite_tree TH"
      unfolding TH_def
      by (meson distinguish_from_set_finite) 
    ultimately have **:"finite_tree T \<Longrightarrow> finite_tree (fst ?TG)"
      using TG_cases by auto
  
    have ***: "observable M1 \<Longrightarrow>
              observable M2 \<Longrightarrow>
              minimal M1 \<Longrightarrow>
              minimal M2 \<Longrightarrow>
              size_r M1 \<le> m \<Longrightarrow>
              size M2 \<le> m \<Longrightarrow>
              inputs M2 = inputs M1 \<Longrightarrow>
              outputs M2 = outputs M1 \<Longrightarrow>
              is_state_cover_assignment M1 V \<Longrightarrow>
              preserves_divergence M1 M2 (V ` reachable_states M1) \<Longrightarrow>
              V ` reachable_states M1 \<subseteq> set T \<Longrightarrow>
              t \<in> transitions M1 \<Longrightarrow>
              t_source t \<in> reachable_states M1 \<Longrightarrow> 
              V (t_source t) @ [(t_input t, t_output t)] \<noteq> V (t_target t) \<Longrightarrow>
              convergence_graph_lookup_invar M1 M2 cg_lookup G \<Longrightarrow>
              convergence_graph_insert_invar M1 M2 cg_lookup cg_insert \<Longrightarrow>
              convergence_graph_merge_invar M1 M2 cg_lookup cg_merge \<Longrightarrow>
              L M1 \<inter> set (fst ?TG) = L M2 \<inter> set (fst ?TG) \<Longrightarrow>
              (set T0 \<subseteq> set T) \<Longrightarrow>
              (\<forall> \<gamma> . (length \<gamma> \<le> (m-size_r M1) \<and> list.set \<gamma> \<subseteq> inputs M1 \<times> outputs M1 \<and> butlast \<gamma> \<in> LS M1 (t_target t))
                      \<longrightarrow> ((L M1 \<inter> (V ` reachable_states M1 \<union> {((V (t_source t))@[(t_input t,t_output t)]) @ \<omega>' | \<omega>'. \<omega>' \<in> list.set (prefixes \<gamma>)})
                            = L M2 \<inter> (V ` reachable_states M1 \<union> {((V (t_source t))@[(t_input t,t_output t)]) @ \<omega>' | \<omega>'. \<omega>' \<in> list.set (prefixes \<gamma>)}))
                           \<and> preserves_divergence M1 M2 (V ` reachable_states M1 \<union> {((V (t_source t))@[(t_input t,t_output t)]) @ \<omega>' | \<omega>'. \<omega>' \<in> list.set (prefixes \<gamma>)})))   
              \<and> convergence_graph_lookup_invar M1 M2 cg_lookup (snd ?TG)"
    proof -
      assume a01 : "observable M1"
      assume a02 : "observable M2"
      assume a03 : "minimal M1"
      assume a04 : "minimal M2"
      assume a05 : "size_r M1 \<le> m"
      assume a06 : "size M2 \<le> m"
      assume a07 : "inputs M2 = inputs M1"
      assume a08 : "outputs M2 = outputs M1"
      assume a09 : "is_state_cover_assignment M1 V"
      assume a10 : "preserves_divergence M1 M2 (V ` reachable_states M1)"
      assume a11 : "V ` reachable_states M1 \<subseteq> set T"
      assume a12 : "t \<in> transitions M1"
      assume a13 : "t_source t \<in> reachable_states M1"
      assume a14 : "convergence_graph_lookup_invar M1 M2 cg_lookup G"
      assume a15 : "convergence_graph_insert_invar M1 M2 cg_lookup cg_insert"
      assume a16 : "convergence_graph_merge_invar M1 M2 cg_lookup cg_merge"
      assume a17 : "L M1 \<inter> set (fst ?TG) = L M2 \<inter> set (fst ?TG)"
      assume a18 : "(set T0 \<subseteq> set T)" 
      assume a19 : "V (t_source t) @ [(t_input t, t_output t)] \<noteq> V (t_target t)"

      have pass_T1 : "L M1 \<inter> set T1 = L M2 \<inter> set T1"
        using a17 \<open>set T1 \<subseteq> set T2\<close> \<open>set T1 \<subseteq> set TH\<close> unfolding TG_cases_fst 
        by (cases "d M1 V t X' l"; auto)
      then have pass_T : "L M1 \<inter> set T = L M2 \<inter> set T"
        using \<open>set T \<subseteq> set T1\<close> by blast


      have "t_target t \<in> reachable_states M1"
        using reachable_states_next[OF a13 a12] by auto
      then have "(V (t_target t)) \<in> L M1"
        using is_state_cover_assignment_language[OF a09] by blast
      moreover have "(V (t_target t)) \<in> set T"
        using a11 \<open>t_target t \<in> reachable_states M1\<close> by blast
      ultimately have "(V (t_target t)) \<in> L M2"
        using pass_T by blast
      then have "v \<in> L M2"
        unfolding v_def .

      have "(V (t_source t)) \<in> L M1"
        using is_state_cover_assignment_language[OF a09 a13] by blast
      moreover have "(V (t_source t)) \<in> set T"
        using a11 a13 by blast
      ultimately have "(V (t_source t)) \<in> L M2"
        using pass_T by blast
      have "u \<in> L M1"
        unfolding u_def
        using a01 a09 a12 a13 converge.simps state_cover_transition_converges by blast 


      have heuristic_prop: "(\<And>T w u' uBest lBest. fst (heuristic T w (uBest, lBest) u') \<in> {u', uBest})"
        unfolding heuristic_def 
        using append_heuristic_input_in append_heuristic_io_in 
        by fastforce 

      have "convergence_graph_lookup_invar M1 M2 cg_lookup G1"
        using distribute_extension_adds_sequence(2)[OF a01 a03 \<open>(V (t_source t)) \<in> L M1\<close> \<open>(V (t_source t)) \<in> L M2\<close> a14 a15, of T "[(t_input t, t_output t)]" b heuristic, OF _ heuristic_prop]
        using pass_T1
        unfolding T1_def G1_def handle_io_pair_def
        unfolding heuristic_def[symmetric]
        by blast

      have "list.set rstates = V ` reachable_states M1"
        unfolding rstates_def
        using reachable_states_as_list_set by auto 
      then have "V ` reachable_states M1 \<subseteq> list.set rstates"
        by auto 
      have "preserves_divergence M1 M2 (list.set rstates)"
        unfolding rstates_def
        using a10
        by (metis image_set reachable_states_as_list_set) 
      then have "preserves_divergence M1 M2 (V ` reachable_states M1)"
        unfolding \<open>list.set rstates = V ` reachable_states M1\<close> .
      have "(\<And>w. w \<in> list.set rstates \<Longrightarrow> \<exists>w'. converge M1 w w' \<and> converge M2 w w')"
      proof -
        fix w assume "w \<in> list.set rstates"
        then obtain q where "w = V q" and "q \<in> reachable_states M1"
          unfolding rstates_def
          using reachable_states_as_list_set by auto
        then have "w \<in> L M1" and "w \<in> set T"
          using is_state_cover_assignment_language[OF a09] a11 by blast+
        then have "w \<in> L M2"
          using pass_T by blast
        then have "converge M1 w w" and "converge M2 w w"
          using \<open>w \<in> L M1\<close> by auto
        then show "\<exists>w'. converge M1 w w' \<and> converge M2 w w'"
          by blast
      qed
      have "L M1 \<inter> V ` reachable_states M1 = L M2 \<inter> V ` reachable_states M1"
        by (meson a11 inter_eq_subsetI pass_T)


      have "converge M1 u v"
        unfolding u_def v_def
        using a01 a09 a12 a13 state_cover_transition_converges by blast 
      have "u \<in> L M2" 
        using distribute_extension_adds_sequence(1)[OF a01 a03 \<open>(V (t_source t)) \<in> L M1\<close> \<open>(V (t_source t)) \<in> L M2\<close> a14 a15, of T "[(t_input t, t_output t)]" b heuristic, OF _ heuristic_prop]
        using pass_T1
        unfolding T1_def G1_def handle_io_pair_def
        unfolding heuristic_def[symmetric]
        by (metis (no_types, lifting) Int_iff \<open>V (t_target t) \<in> L M1\<close> \<open>converge M1 u v\<close> a01 a02 append_Nil2 converge_append_language_iff u_def v_def)

      have "(u = v) = False"
        unfolding u_def v_def using a19 by simp

      

      have "after_initial M1 u = t_target t"
        using a09 unfolding u_def
        by (metis \<open>converge M1 u v\<close> \<open>t_target t \<in> reachable_states M1\<close> a01 a03 converge.elims(2) convergence_minimal is_state_cover_assignment_observable_after u_def v_def) 

      have "\<And> \<gamma> x y . {u @ \<omega>' | \<omega>'. \<omega>' \<in> list.set (prefixes (\<gamma> @ [(x, y)]))} \<subseteq> {\<omega> @ \<omega>' |\<omega> \<omega>'. \<omega> \<in> {u, v} \<and> \<omega>' \<in> list.set (prefixes (\<gamma> @ [(x, y)]))}"
        by blast

      show "(\<forall> \<gamma> . (length \<gamma> \<le> (m-size_r M1) \<and> list.set \<gamma> \<subseteq> inputs M1 \<times> outputs M1 \<and> butlast \<gamma> \<in> LS M1 (t_target t))
                      \<longrightarrow> ((L M1 \<inter> (V ` reachable_states M1 \<union> {((V (t_source t))@[(t_input t,t_output t)]) @ \<omega>' | \<omega>'. \<omega>' \<in> list.set (prefixes \<gamma>)})
                            = L M2 \<inter> (V ` reachable_states M1 \<union> {((V (t_source t))@[(t_input t,t_output t)]) @ \<omega>' | \<omega>'. \<omega>' \<in> list.set (prefixes \<gamma>)}))
                           \<and> preserves_divergence M1 M2 (V ` reachable_states M1 \<union> {((V (t_source t))@[(t_input t,t_output t)]) @ \<omega>' | \<omega>'. \<omega>' \<in> list.set (prefixes \<gamma>)})))   
              \<and> convergence_graph_lookup_invar M1 M2 cg_lookup (snd ?TG)"
      proof (cases "d M1 V t X' l")
        case True
        then have "?TG = (T2,G3)"
          unfolding TG_cases by auto

        have pass_T2: "L M1 \<inter> set T2 = L M2 \<inter> set T2"
          using a17 unfolding \<open>?TG = (T2,G3)\<close> by auto

        have "convergence_graph_lookup_invar M1 M2 cg_lookup G2"  
        and  "converge M2 u v"
          using pass_T2
          using distinguish_from_set_establishes_convergence[OF a01 a02 a03 a04 a05 a06 a07 a08 a09 \<open>preserves_divergence M1 M2 (V ` reachable_states M1)\<close> \<open>L M1 \<inter> V ` reachable_states M1 = L M2 \<inter> V ` reachable_states M1\<close> \<open>converge M1 u v\<close> \<open>u \<in> L M2\<close> \<open>v \<in> L M2\<close> \<open>convergence_graph_lookup_invar M1 M2 cg_lookup G1\<close> a15 assms, of T1 k b heuristic, OF _ _ _ _ heuristic_prop]
          unfolding G2_def T2_def \<open>(u = v) = False\<close> rstates_def[symmetric] l_def[symmetric]
          by blast+
        then have "convergence_graph_lookup_invar M1 M2 cg_lookup (snd ?TG)"
          unfolding \<open>?TG = (T2,G3)\<close> G3_def snd_conv using a16
          by (meson \<open>converge M1 u v\<close> convergence_graph_merge_invar_def) 


        have cons_prop: "\<And>\<gamma> x y.
                           length (\<gamma> @ [(x, y)]) \<le> l \<Longrightarrow>
                           \<gamma> \<in> LS M1 (after_initial M1 u) \<Longrightarrow>
                           x \<in> FSM.inputs M1 \<Longrightarrow>
                           y \<in> FSM.outputs M1 \<Longrightarrow>
                           L M1 \<inter> (list.set rstates \<union> {\<omega> @ \<omega>' |\<omega> \<omega>'. \<omega> \<in> {u, v} \<and> \<omega>' \<in> list.set (prefixes (\<gamma> @ [(x, y)]))}) =
                           L M2 \<inter> (list.set rstates \<union> {\<omega> @ \<omega>' |\<omega> \<omega>'. \<omega> \<in> {u, v} \<and> \<omega>' \<in> list.set (prefixes (\<gamma> @ [(x, y)]))}) \<and>
                           preserves_divergence M1 M2 (list.set rstates \<union> {\<omega> @ \<omega>' |\<omega> \<omega>'. \<omega> \<in> {u, v} \<and> \<omega>' \<in> list.set (prefixes (\<gamma> @ [(x, y)]))})"
         and nil_prop: "preserves_divergence M1 M2 (list.set rstates \<union> {u, v})"        
          using pass_T2
          using distinguish_from_set_properties(1,2)[OF a01 a02 a03 a04 a07 a08 a09 \<open>V ` reachable_states M1 \<subseteq> list.set rstates\<close> \<open>preserves_divergence M1 M2 (list.set rstates)\<close> \<open>(\<And>w. w \<in> list.set rstates \<Longrightarrow> \<exists>w'. converge M1 w w' \<and> converge M2 w w')\<close> \<open>converge M1 u v\<close> \<open>u \<in> L M2\<close> \<open>v \<in> L M2\<close> \<open>convergence_graph_lookup_invar M1 M2 cg_lookup G1\<close> a15 assms, of T1 k l b heuristic, OF _ _ _ _ _ heuristic_prop ]
          unfolding G2_def T2_def \<open>(u = v) = False\<close>  
          by presburger+
        have "\<And> \<gamma> . (length \<gamma> \<le> (m-size_r M1) \<and> list.set \<gamma> \<subseteq> inputs M1 \<times> outputs M1 \<and> butlast \<gamma> \<in> LS M1 (t_target t))
                      \<Longrightarrow> ((L M1 \<inter> (V ` reachable_states M1 \<union> {((V (t_source t))@[(t_input t,t_output t)]) @ \<omega>' | \<omega>'. \<omega>' \<in> list.set (prefixes \<gamma>)})
                            = L M2 \<inter> (V ` reachable_states M1 \<union> {((V (t_source t))@[(t_input t,t_output t)]) @ \<omega>' | \<omega>'. \<omega>' \<in> list.set (prefixes \<gamma>)}))
                           \<and> preserves_divergence M1 M2 (V ` reachable_states M1 \<union> {((V (t_source t))@[(t_input t,t_output t)]) @ \<omega>' | \<omega>'. \<omega>' \<in> list.set (prefixes \<gamma>)}))"
          (is "\<And> \<gamma> . (length \<gamma> \<le> (m-size_r M1) \<and> list.set \<gamma> \<subseteq> inputs M1 \<times> outputs M1 \<and> butlast \<gamma> \<in> LS M1 (t_target t)) \<Longrightarrow> ?P1 \<gamma> \<and> ?P2 \<gamma>")          
        proof -
          fix \<gamma> assume assm:"(length \<gamma> \<le> (m-size_r M1) \<and> list.set \<gamma> \<subseteq> inputs M1 \<times> outputs M1 \<and> butlast \<gamma> \<in> LS M1 (t_target t))"
          show "?P1 \<gamma> \<and> ?P2 \<gamma>" 
          proof (cases \<gamma> rule: rev_cases)
            case Nil
            have *: "(V ` reachable_states M1 \<union> {((V (t_source t))@[(t_input t,t_output t)]) @ \<omega>' | \<omega>'. \<omega>' \<in> list.set (prefixes \<gamma>)})
                        = (V ` reachable_states M1 \<union> {u})"
              unfolding u_def[symmetric] \<open>list.set rstates = V ` reachable_states M1\<close> Nil by auto

            have "?P1 \<gamma>"
              using \<open>L M1 \<inter> V ` reachable_states M1 = L M2 \<inter> V ` reachable_states M1\<close>
                    \<open>u \<in> L M1\<close> \<open>u \<in> L M2\<close>
              unfolding * by blast
            moreover have "?P2 \<gamma>"
              using preserves_divergence_subset[OF nil_prop]
              unfolding * \<open>list.set rstates = V ` reachable_states M1\<close>
              by (metis Un_empty_right Un_insert_right Un_upper1 insertI1 insert_subsetI)
            ultimately show ?thesis
              by simp 
          next
            case (snoc \<gamma>' xy)
            moreover obtain x y where "xy = (x,y)" 
              using prod.exhaust by metis
            ultimately have "\<gamma> = \<gamma>'@[(x,y)]"
              by auto

            have *: "(V ` reachable_states M1 \<union> {u @ \<omega>' |\<omega>'. \<omega>' \<in> list.set (prefixes \<gamma>)}) \<subseteq> (V ` reachable_states M1 \<union> {\<omega> @ \<omega>' |\<omega> \<omega>'. \<omega> \<in> {u, v} \<and> \<omega>' \<in> list.set (prefixes \<gamma>)})"
              by blast

            have "length (\<gamma>' @ [(x, y)]) \<le> l"
              using assm unfolding l_def \<open>\<gamma> = \<gamma>'@[(x,y)]\<close> by auto
            moreover have "\<gamma>' \<in> LS M1 (after_initial M1 u)"
              using assm unfolding l_def \<open>\<gamma> = \<gamma>'@[(x,y)]\<close>
              by (simp add: \<open>after_initial M1 u = t_target t\<close>) 
            moreover have "x \<in> FSM.inputs M1" and "y \<in> FSM.outputs M1"
              using assm unfolding \<open>\<gamma> = \<gamma>'@[(x,y)]\<close> by auto
            ultimately show ?thesis
              using cons_prop[of \<gamma>' x y] preserves_divergence_subset[of M1 M2 "(V ` reachable_states M1 \<union> {\<omega> @ \<omega>' |\<omega> \<omega>'. \<omega> \<in> {u, v} \<and> \<omega>' \<in> list.set (prefixes \<gamma>)})", OF _ *]
              unfolding \<open>\<gamma> = \<gamma>'@[(x,y)]\<close>[symmetric] u_def[symmetric] \<open>list.set rstates = V ` reachable_states M1\<close>
              by blast
          qed 
        qed
        then show ?thesis
          using \<open>convergence_graph_lookup_invar M1 M2 cg_lookup (snd ?TG)\<close>
          by presburger
      next
        case False

        then have "?TG = (TH,GH)"
          unfolding TG_cases by auto

        have pass_TH: "L M1 \<inter> set TH = L M2 \<inter> set TH"
          using a17 unfolding \<open>?TG = (TH,GH)\<close> by auto

        have "converge M1 u u"
          using \<open>u \<in> L M1\<close> by auto

        have cons_prop: "\<And>\<gamma> x y.
                           length (\<gamma> @ [(x, y)]) \<le> l \<Longrightarrow>
                           \<gamma> \<in> LS M1 (t_target t) \<Longrightarrow>
                           x \<in> FSM.inputs M1 \<Longrightarrow>
                           y \<in> FSM.outputs M1 \<Longrightarrow>
                           L M1 \<inter> (V ` reachable_states M1 \<union> {\<omega> @ \<omega>' |\<omega> \<omega>'. \<omega> \<in> {u, u} \<and> \<omega>' \<in> list.set (prefixes (\<gamma> @ [(x, y)]))}) =
                           L M2 \<inter> (V ` reachable_states M1 \<union> {\<omega> @ \<omega>' |\<omega> \<omega>'. \<omega> \<in> {u, u} \<and> \<omega>' \<in> list.set (prefixes (\<gamma> @ [(x, y)]))}) \<and>
                           preserves_divergence M1 M2 (V ` reachable_states M1 \<union> {\<omega> @ \<omega>' |\<omega> \<omega>'. \<omega> \<in> {u, u} \<and> \<omega>' \<in> list.set (prefixes (\<gamma> @ [(x, y)]))})"
        and  nil_prop: "preserves_divergence M1 M2 (V ` reachable_states M1 \<union> {u,u})"  
        and  "convergence_graph_lookup_invar M1 M2 cg_lookup (snd ?TG)"
          using pass_TH
          using distinguish_from_set_properties[OF a01 a02 a03 a04 a07 a08 a09 \<open>V ` reachable_states M1 \<subseteq> list.set rstates\<close> \<open>preserves_divergence M1 M2 (list.set rstates)\<close> \<open>(\<And>w. w \<in> list.set rstates \<Longrightarrow> \<exists>w'. converge M1 w w' \<and> converge M2 w w')\<close> \<open>converge M1 u u\<close> \<open>u \<in> L M2\<close> \<open>u \<in> L M2\<close> \<open>convergence_graph_lookup_invar M1 M2 cg_lookup G1\<close> a15 assms, of T1 k l b heuristic, OF _ _ _ _ _ heuristic_prop ]
          unfolding \<open>?TG = (TH,GH)\<close> snd_conv
          unfolding GH_def TH_def \<open>list.set rstates = V ` reachable_states M1\<close> \<open>after_initial M1 u = t_target t\<close> 
          by presburger+

        have "\<And> \<gamma> . (length \<gamma> \<le> (m-size_r M1) \<and> list.set \<gamma> \<subseteq> inputs M1 \<times> outputs M1 \<and> butlast \<gamma> \<in> LS M1 (t_target t))
                      \<Longrightarrow> ((L M1 \<inter> (V ` reachable_states M1 \<union> {((V (t_source t))@[(t_input t,t_output t)]) @ \<omega>' | \<omega>'. \<omega>' \<in> list.set (prefixes \<gamma>)})
                            = L M2 \<inter> (V ` reachable_states M1 \<union> {((V (t_source t))@[(t_input t,t_output t)]) @ \<omega>' | \<omega>'. \<omega>' \<in> list.set (prefixes \<gamma>)}))
                           \<and> preserves_divergence M1 M2 (V ` reachable_states M1 \<union> {((V (t_source t))@[(t_input t,t_output t)]) @ \<omega>' | \<omega>'. \<omega>' \<in> list.set (prefixes \<gamma>)}))"
          (is "\<And> \<gamma> . (length \<gamma> \<le> (m-size_r M1) \<and> list.set \<gamma> \<subseteq> inputs M1 \<times> outputs M1 \<and> butlast \<gamma> \<in> LS M1 (t_target t)) \<Longrightarrow> ?P1 \<gamma> \<and> ?P2 \<gamma>")          
        proof -
          fix \<gamma> assume assm:"(length \<gamma> \<le> (m-size_r M1) \<and> list.set \<gamma> \<subseteq> inputs M1 \<times> outputs M1 \<and> butlast \<gamma> \<in> LS M1 (t_target t))"
          show "?P1 \<gamma> \<and> ?P2 \<gamma>" 
          proof (cases \<gamma> rule: rev_cases)
            case Nil
            have *: "(V ` reachable_states M1 \<union> {((V (t_source t))@[(t_input t,t_output t)]) @ \<omega>' | \<omega>'. \<omega>' \<in> list.set (prefixes \<gamma>)})
                        = (V ` reachable_states M1 \<union> {u})"
              unfolding u_def[symmetric] \<open>list.set rstates = V ` reachable_states M1\<close> Nil by auto

            have "?P1 \<gamma>"
              using \<open>L M1 \<inter> V ` reachable_states M1 = L M2 \<inter> V ` reachable_states M1\<close>
                    \<open>u \<in> L M1\<close> \<open>u \<in> L M2\<close>
              unfolding * by blast
            moreover have "?P2 \<gamma>"
              using nil_prop
              unfolding * by auto
            ultimately show ?thesis
              by simp 
          next
            case (snoc \<gamma>' xy)
            moreover obtain x y where "xy = (x,y)" 
              using prod.exhaust by metis
            ultimately have "\<gamma> = \<gamma>'@[(x,y)]"
              by auto

            have *: "{\<omega> @ \<omega>' |\<omega> \<omega>'. \<omega> \<in> {u, u} \<and> \<omega>' \<in> list.set (prefixes \<gamma>)} = {u @ \<omega>' |\<omega>'. \<omega>' \<in> list.set (prefixes \<gamma>)}"
              by blast

            have "length (\<gamma>' @ [(x, y)]) \<le> l"
              using assm unfolding l_def \<open>\<gamma> = \<gamma>'@[(x,y)]\<close> by auto
            moreover have "\<gamma>' \<in> LS M1 (t_target t)"
              using assm unfolding l_def \<open>\<gamma> = \<gamma>'@[(x,y)]\<close>
              by simp 
            moreover have "x \<in> FSM.inputs M1" and "y \<in> FSM.outputs M1"
              using assm unfolding \<open>\<gamma> = \<gamma>'@[(x,y)]\<close> by auto
            ultimately show ?thesis
              using cons_prop[of \<gamma>' x y] 
              unfolding \<open>\<gamma> = \<gamma>'@[(x,y)]\<close>[symmetric] u_def[symmetric] \<open>list.set rstates = V ` reachable_states M1\<close> *
              by blast
          qed 
        qed
        then show ?thesis
          using \<open>convergence_graph_lookup_invar M1 M2 cg_lookup (snd ?TG)\<close>
          by presburger
      qed
    qed


  
    show "?P T G m t X"
      using * ** ***  by blast
  qed
  then show ?thesis
    unfolding handles_transition_def
    by blast
qed







subsubsection \<open>Static\<close>

fun traces_to_check :: "('a,'b::linorder,'c::linorder) fsm \<Rightarrow> 'a \<Rightarrow> nat \<Rightarrow> ('b\<times>'c) list list" where
  "traces_to_check M q 0 = []" |
  "traces_to_check M q (Suc k) = (let
      ios  = List.product (inputs_as_list M) (outputs_as_list M)
      in concat (map (\<lambda>(x,y) . case h_obs M q x y of None \<Rightarrow> [[(x,y)]] | Some q' \<Rightarrow> [(x,y)] # (map ((#) (x,y)) (traces_to_check M q' k))) ios))"  

lemma traces_to_check_set :
  fixes M :: "('a,'b::linorder,'c::linorder) fsm"
  assumes "observable M"
  and     "q \<in> states M" 
shows "list.set (traces_to_check M q k) = {(\<gamma> @ [(x, y)]) | \<gamma> x y . length (\<gamma> @ [(x, y)]) \<le> k \<and> \<gamma> \<in> LS M q \<and> x \<in> inputs M \<and> y \<in> outputs M}"
  using assms(2) proof (induction k arbitrary: q)
  case 0
  then show ?case by auto
next
  case (Suc k)

  define ios where ios: "ios  = List.product (inputs_as_list M) (outputs_as_list M)"
  define f where f: "f = (\<lambda>(x,y) . case h_obs M q x y of None \<Rightarrow> [[(x,y)]] | Some q' \<Rightarrow> [(x,y)] # (map ((#) (x,y)) (traces_to_check M q' k)))"

  have "list.set ios = inputs M \<times> outputs M"
    using inputs_as_list_set outputs_as_list_set unfolding ios by auto 
  moreover have "traces_to_check M q (Suc k) = concat (map f ios)"
    unfolding f ios by auto
  ultimately have in_ex : "\<And> io . io \<in> list.set (traces_to_check M q (Suc k)) \<longleftrightarrow> (\<exists> x y . x \<in> inputs M \<and> y \<in> outputs M \<and> io \<in> list.set (f (x,y)))"
    by auto 

  show ?case
  proof 
    show "list.set (traces_to_check M q (Suc k)) \<subseteq> {(\<gamma> @ [(x, y)]) | \<gamma> x y . length (\<gamma> @ [(x, y)]) \<le> (Suc k) \<and> \<gamma> \<in> LS M q \<and> x \<in> inputs M \<and> y \<in> outputs M}"
    proof 
      fix io assume "io \<in> list.set (traces_to_check M q (Suc k))"
      then obtain x y where "x \<in> inputs M" and "y \<in> outputs M"
                        and "io \<in> list.set (f (x,y))"
        using in_ex by blast

      have "[(x,y)] \<in> {(\<gamma> @ [(x, y)]) | \<gamma> x y . length (\<gamma> @ [(x, y)]) \<le> (Suc k) \<and> \<gamma> \<in> LS M q \<and> x \<in> inputs M \<and> y \<in> outputs M}" 
      proof -
        have "length ([] @ [(x, y)]) \<le> Suc k"
          by auto
        moreover have "[] \<in> LS M q"
          using Suc.prems by auto
        ultimately show ?thesis 
          using \<open>x \<in> inputs M\<close> \<open>y \<in> outputs M\<close> by blast
      qed


      show "io \<in> {(\<gamma> @ [(x, y)]) | \<gamma> x y . length (\<gamma> @ [(x, y)]) \<le> (Suc k) \<and> \<gamma> \<in> LS M q \<and> x \<in> inputs M \<and> y \<in> outputs M}"
      proof (cases "h_obs M q x y")
        case None
        then have "io = [(x,y)]"
          using \<open>io \<in> list.set (f (x,y))\<close> unfolding f by auto
        then show ?thesis
          using \<open>[(x,y)] \<in> {(\<gamma> @ [(x, y)]) | \<gamma> x y . length (\<gamma> @ [(x, y)]) \<le> (Suc k) \<and> \<gamma> \<in> LS M q \<and> x \<in> inputs M \<and> y \<in> outputs M}\<close>
          by blast
      next
        case (Some q')
        then consider "io = [(x,y)]" | "io \<in> list.set (map ((#) (x,y)) (traces_to_check M q' k))"
          using \<open>io \<in> list.set (f (x,y))\<close> unfolding f by auto
        then show ?thesis proof cases
          case 1
          then show ?thesis
            using \<open>[(x,y)] \<in> {(\<gamma> @ [(x, y)]) | \<gamma> x y . length (\<gamma> @ [(x, y)]) \<le> (Suc k) \<and> \<gamma> \<in> LS M q \<and> x \<in> inputs M \<and> y \<in> outputs M}\<close>
            by blast
        next
          case 2
          then obtain io' where "io = (x,y)#io'" and "io' \<in> list.set (traces_to_check M q' k)"
            by auto
          then have "io' \<in> {(\<gamma> @ [(x, y)]) | \<gamma> x y . length (\<gamma> @ [(x, y)]) \<le> k \<and> \<gamma> \<in> LS M q' \<and> x \<in> inputs M \<and> y \<in> outputs M}"
            using Suc.IH[OF h_obs_state[OF Some]] by blast
          then obtain \<gamma> x' y' where "io' = (\<gamma> @ [(x', y')])" and "length (\<gamma> @ [(x', y')]) \<le> k" and "\<gamma> \<in> LS M q'" and "x' \<in> inputs M" and "y' \<in> outputs M"
            by auto
  
          have "length (((x,y)#\<gamma>) @ [(x', y')]) \<le> Suc k"
            using \<open>length (\<gamma> @ [(x', y')]) \<le> k\<close> by auto
          moreover have "((x,y)#\<gamma>) \<in> LS M q"
            using \<open>\<gamma> \<in> LS M q'\<close> Some assms(1)
            by (meson h_obs_language_iff) 
          ultimately show ?thesis 
            using \<open>x' \<in> inputs M\<close> \<open>y' \<in> outputs M\<close> unfolding \<open>io = (x,y)#io'\<close> \<open>io' = (\<gamma> @ [(x', y')])\<close>
            by auto
        qed
      qed
    qed

    show "{\<gamma> @ [(x, y)] |\<gamma> x y. length (\<gamma> @ [(x, y)]) \<le> Suc k \<and> \<gamma> \<in> LS M q \<and> x \<in> FSM.inputs M \<and> y \<in> FSM.outputs M} \<subseteq> list.set (traces_to_check M q (Suc k))"
    proof 
      fix io assume "io \<in> {\<gamma> @ [(x, y)] |\<gamma> x y. length (\<gamma> @ [(x, y)]) \<le> Suc k \<and> \<gamma> \<in> LS M q \<and> x \<in> FSM.inputs M \<and> y \<in> FSM.outputs M}"
      then obtain \<gamma> x' y' where "io = (\<gamma> @ [(x', y')])" and "length (\<gamma> @ [(x', y')]) \<le> Suc k" and "\<gamma> \<in> LS M q" and "x' \<in> inputs M" and "y' \<in> outputs M"
        by auto
      show "io \<in> list.set (traces_to_check M q (Suc k))"
      proof (cases \<gamma>)
        case Nil
        then have "io = [(x',y')]"
          using \<open>io = (\<gamma> @ [(x', y')])\<close> by auto
        have "io \<in> list.set (f (x',y'))"
          unfolding f case_prod_conv \<open>io = [(x',y')]\<close> 
          by (cases "FSM.h_obs M q x' y'"; auto)
        then show ?thesis 
          using in_ex[of io] \<open>x' \<in> inputs M\<close> \<open>y' \<in> outputs M\<close> by blast
      next
        case (Cons xy \<gamma>')

        obtain x y where "xy = (x,y)"
          using prod.exhaust by metis

        obtain q' where "h_obs M q x y = Some q'"  and "x \<in> inputs M" and "y \<in> outputs M" and "\<gamma>' \<in> LS M q'"
          using \<open>\<gamma> \<in> LS M q\<close> unfolding Cons \<open>xy = (x,y)\<close>
          by (meson assms(1) h_obs_language_iff language_io(1) language_io(2) list.set_intros(1))
        then have "\<gamma>'@[(x',y')] \<in> {\<gamma> @ [(x, y)] |\<gamma> x y. length (\<gamma> @ [(x, y)]) \<le> k \<and> \<gamma> \<in> LS M q' \<and> x \<in> FSM.inputs M \<and> y \<in> FSM.outputs M}"
          using \<open>length (\<gamma> @ [(x', y')]) \<le> Suc k\<close> \<open>x' \<in> inputs M\<close> \<open>y' \<in> outputs M\<close> unfolding Cons by auto
        then have "\<gamma>'@[(x',y')] \<in> list.set (traces_to_check M q' k)"
          using Suc.IH[OF h_obs_state[OF \<open>h_obs M q x y = Some q'\<close>]] by blast
        then have "io \<in> list.set (f (x,y))"
          unfolding f case_prod_conv \<open>h_obs M q x y = Some q'\<close> unfolding \<open>io = (\<gamma> @ [(x', y')])\<close> Cons \<open>xy = (x,y)\<close>
          by auto
        then show ?thesis 
          using in_ex[of io] \<open>x \<in> inputs M\<close> \<open>y \<in> outputs M\<close> by blast
      qed
    qed
  qed
qed 

fun establish_convergence_static :: "(nat \<Rightarrow> 'a \<Rightarrow> ('b\<times>'c) prefix_tree) \<Rightarrow> 
                                  ('a::linorder,'b::linorder,'c::linorder) fsm \<Rightarrow> 
                                  ('a,'b,'c) state_cover_assignment \<Rightarrow> 
                                  ('b\<times>'c) prefix_tree \<Rightarrow> 
                                  'd \<Rightarrow> 
                                  ('d \<Rightarrow> ('b\<times>'c) list \<Rightarrow> 'd) \<Rightarrow> 
                                  ('d \<Rightarrow> ('b\<times>'c) list \<Rightarrow> ('b\<times>'c) list list) \<Rightarrow> 
                                  nat \<Rightarrow> 
                                  ('a,'b,'c) transition \<Rightarrow> 
                                  (('b\<times>'c) prefix_tree \<times> 'd)" 
  where
  "establish_convergence_static dist_fun M V T G cg_insert cg_lookup m t =
    (let 
        \<alpha> = V (t_source t);
        xy = (t_input t, t_output t);
        \<beta> = V (t_target t);
        qSource = (after_initial M (V (t_source t)));
        qTarget = (after_initial M (V (t_target t)));
        k = m - size_r M;
        ttc = [] # traces_to_check M qTarget k;
        handleTrace = (\<lambda> (T,G) u . 
          if is_in_language M qTarget u 
            then let
                qu = FSM.after M qTarget u; 
                ws = sorted_list_of_maximal_sequences_in_tree (dist_fun (Suc (length u)) qu);
                appendDistTrace = (\<lambda> (T,G) w . let
                                                  (T',G') = distribute_extension M T G cg_lookup cg_insert \<alpha> (xy#u@w) False (append_heuristic_input M)
                                                in distribute_extension M T' G' cg_lookup cg_insert \<beta> (u@w) False (append_heuristic_input M))
                in foldl appendDistTrace (T,G) ws
            else let
                  (T',G') = distribute_extension M T G cg_lookup cg_insert \<alpha> (xy#u) False (append_heuristic_input M)
                 in distribute_extension M T' G' cg_lookup cg_insert \<beta> u False (append_heuristic_input M))
    in 
      foldl handleTrace (T,G) ttc)"



lemma appendDistTrace_subset_helper :
  assumes "appendDistTrace = (\<lambda> (T,G) w . let
                                            (T',G') = distribute_extension M T G cg_lookup cg_insert \<alpha> (xy#u@w) False (append_heuristic_input M)
                                            in distribute_extension M T' G' cg_lookup cg_insert \<beta> (u@w) False (append_heuristic_input M))"
shows "set T \<subseteq> set (fst (appendDistTrace (T,G) w))"
proof -
  obtain T' G' where ***: "distribute_extension M T G cg_lookup cg_insert \<alpha> (xy#u@w) False (append_heuristic_input M) = (T',G')"
    using prod.exhaust by metis

  show "set T \<subseteq> set (fst (appendDistTrace (T,G) w))"            
    using distribute_extension_subset[of T M G cg_lookup cg_insert \<alpha> "xy#u@w" False "(append_heuristic_input M)"]
    using distribute_extension_subset[of T' M G' cg_lookup cg_insert \<beta> "u@w" False "(append_heuristic_input M)"]
    unfolding assms case_prod_conv *** Let_def fst_conv 
    by blast
qed

lemma handleTrace_subset_helper :
  assumes "handleTrace = (\<lambda> (T,G) u . 
          if is_in_language M qTarget u 
            then let
                qu = FSM.after M qTarget u; 
                ws = sorted_list_of_maximal_sequences_in_tree (dist_fun (Suc (length u)) qu);
                appendDistTrace = (\<lambda> (T,G) w . let
                                                  (T',G') = distribute_extension M T G cg_lookup cg_insert \<alpha> (xy#u@w) False (append_heuristic_input M)
                                                in distribute_extension M T' G' cg_lookup cg_insert \<beta> (u@w) False (append_heuristic_input M))
                in foldl appendDistTrace (T,G) ws               
            else let
                (T',G') = distribute_extension M T G cg_lookup cg_insert \<alpha> (xy#u) False (append_heuristic_input M)
                in distribute_extension M T' G' cg_lookup cg_insert \<beta> u False (append_heuristic_input M))"
shows "set T \<subseteq> set (fst (handleTrace (T,G) u))"
proof (cases "is_in_language M qTarget u")
  case True

  define qu where qu: "qu = FSM.after M qTarget u"
  define ws where ws: "ws = sorted_list_of_maximal_sequences_in_tree (dist_fun (Suc (length u)) qu)"
  define appendDistTrace where appendDistTrace: "appendDistTrace = (\<lambda> (T,G) w . let
                                            (T',G') = distribute_extension M T G cg_lookup cg_insert \<alpha> (xy#u@w) False (append_heuristic_input M)
                                            in distribute_extension M T' G' cg_lookup cg_insert \<beta> (u@w) False (append_heuristic_input M))"

  have **: "handleTrace (T,G) u = foldl appendDistTrace (T,G) ws"
    unfolding qu ws appendDistTrace Let_def case_prod_conv assms using True by force

  show ?thesis
    using appendDistTrace_subset_helper[OF appendDistTrace]
    unfolding ** 
    apply (induction ws rule: rev_induct; simp)
    by (metis (no_types, opaque_lifting) Collect_mono_iff fst_conv old.prod.exhaust) 
next
  case False

  obtain T' G' where ***: "distribute_extension M T G cg_lookup cg_insert \<alpha> (xy#u) False (append_heuristic_input M) = (T',G')"
      using prod.exhaust by metis

  show "set T \<subseteq> set (fst (handleTrace (T, G) u))"            
    using distribute_extension_subset[of T M G cg_lookup cg_insert \<alpha> "xy#u" False "(append_heuristic_input M)"]
    using distribute_extension_subset[of T' M G' cg_lookup cg_insert \<beta> "u" False "(append_heuristic_input M)"]
    using False
    unfolding case_prod_conv *** Let_def fst_conv assms 
    by force
qed


lemma establish_convergence_static_subset :
  "set T \<subseteq> set (fst (establish_convergence_static dist_fun M V T G cg_insert cg_lookup m t))"
proof -
  define \<alpha> where \<alpha>: "\<alpha> = V (t_source t)"
  define xy where xy: "xy = (t_input t, t_output t)"
  define \<beta> where \<beta>: "\<beta> = V (t_target t)"
  define qSource where qSource: "qSource = (after_initial M (V (t_source t)))"
  define qTarget where qTarget: "qTarget = (after_initial M (V (t_target t)))"
  define k where k: "k = m - size_r M"
  define ttc where ttc : "ttc = [] # traces_to_check M qTarget k"
  define handleTrace where handleTrace: "handleTrace = (\<lambda> (T,G) u . 
          if is_in_language M qTarget u 
            then let
                qu = FSM.after M qTarget u; 
                ws = sorted_list_of_maximal_sequences_in_tree (dist_fun (Suc (length u)) qu);
                appendDistTrace = (\<lambda> (T,G) w . let
                                                  (T',G') = distribute_extension M T G cg_lookup cg_insert \<alpha> (xy#u@w) False (append_heuristic_input M)
                                                in distribute_extension M T' G' cg_lookup cg_insert \<beta> (u@w) False (append_heuristic_input M))
                in foldl appendDistTrace (T,G) ws
            else let
                (T',G') = distribute_extension M T G cg_lookup cg_insert \<alpha> (xy#u) False (append_heuristic_input M)
                in distribute_extension M T' G' cg_lookup cg_insert \<beta> u False (append_heuristic_input M))"

  have *:"establish_convergence_static dist_fun M V T G cg_insert cg_lookup m t = foldl handleTrace (T,G) ttc"
    unfolding establish_convergence_static.simps \<alpha> xy \<beta> qSource qTarget k ttc handleTrace Let_def by force

  
  show ?thesis
    unfolding * proof (induction ttc rule: rev_induct)
    case Nil
    then show ?case by auto
  next
    case (snoc io ttc)

    have *:"foldl handleTrace (T, G) (ttc@[io]) = handleTrace (foldl handleTrace (T,G) ttc) io"
      by auto

    have "\<And> u T G . set T \<subseteq> set (fst (handleTrace (T,G) u))"
      using handleTrace_subset_helper[of handleTrace] handleTrace
      unfolding \<alpha> xy \<beta> qSource qTarget k ttc by blast
    then show ?case
      unfolding *
      by (metis (no_types, opaque_lifting) snoc.IH dual_order.trans fst_conv old.prod.exhaust) 
  qed
qed


lemma establish_convergence_static_finite :
  fixes M :: "('a::linorder,'b::linorder,'c::linorder) fsm"
  assumes "finite_tree T"
shows "finite_tree (fst (establish_convergence_static dist_fun M V T G cg_insert cg_lookup m t))"
proof -
  define \<alpha> where \<alpha>: "\<alpha> = V (t_source t)"
  define xy where xy: "xy = (t_input t, t_output t)"
  define \<beta> where \<beta>: "\<beta> = V (t_target t)"
  define qSource where qSource: "qSource = (after_initial M (V (t_source t)))"
  define qTarget where qTarget: "qTarget = (after_initial M (V (t_target t)))"
  define k where k: "k = m - size_r M"
  define ttc where ttc : "ttc = [] # traces_to_check M qTarget k"
  define handleTrace where handleTrace: "handleTrace = (\<lambda> (T,G) u . 
          if is_in_language M qTarget u 
            then let
                qu = FSM.after M qTarget u; 
                ws = sorted_list_of_maximal_sequences_in_tree (dist_fun (Suc (length u)) qu);
                appendDistTrace = (\<lambda> (T,G) w . let
                                                  (T',G') = distribute_extension M T G cg_lookup cg_insert \<alpha> (xy#u@w) False (append_heuristic_input M)
                                                in distribute_extension M T' G' cg_lookup cg_insert \<beta> (u@w) False (append_heuristic_input M))
                in foldl appendDistTrace (T,G) ws                
            else let
                (T',G') = distribute_extension M T G cg_lookup cg_insert \<alpha> (xy#u) False (append_heuristic_input M)
                in distribute_extension M T' G' cg_lookup cg_insert \<beta> u False (append_heuristic_input M))"

  have *:"establish_convergence_static dist_fun M V T G cg_insert cg_lookup m t = foldl handleTrace (T,G) ttc"
    unfolding establish_convergence_static.simps \<alpha> xy \<beta> qSource qTarget k ttc handleTrace Let_def by force

  
  show ?thesis
    unfolding * proof (induction ttc rule: rev_induct)
    case Nil
    then show ?case using assms by auto
  next
    case (snoc io ttc)

    have *:"foldl handleTrace (T, G) (ttc@[io]) = handleTrace (foldl handleTrace (T,G) ttc) io"
      by auto

    have "\<And> u T G . finite_tree T \<Longrightarrow> finite_tree (fst (handleTrace (T,G) u))"
    proof -
      fix T :: "('b\<times>'c) prefix_tree"
      fix u G assume "finite_tree T"
      show "finite_tree (fst (handleTrace (T,G) u))" proof (cases "is_in_language M qTarget u")
        case True

        define qu where qu: "qu = FSM.after M qTarget u"
        define ws where ws: "ws = sorted_list_of_maximal_sequences_in_tree (dist_fun (Suc (length u)) qu)"
        define appendDistTrace where appendDistTrace: "appendDistTrace = (\<lambda> (T,G) w . let
                                                  (T',G') = distribute_extension M T G cg_lookup cg_insert \<alpha> (xy#u@w) False (append_heuristic_input M)
                                                  in distribute_extension M T' G' cg_lookup cg_insert \<beta> (u@w) False (append_heuristic_input M))"

        have **: "handleTrace (T,G) u = foldl appendDistTrace (T,G) ws"
          unfolding handleTrace qu ws appendDistTrace Let_def case_prod_conv using True by force

        have "\<And> w T G . finite_tree T \<Longrightarrow> finite_tree (fst (appendDistTrace (T,G) w))"
        proof -
          fix T :: "('b\<times>'c) prefix_tree"
          fix w G assume "finite_tree T"

          obtain T' G' where ***: "distribute_extension M T G cg_lookup cg_insert \<alpha> (xy#u@w) False (append_heuristic_input M) = (T',G')"
            using prod.exhaust by metis

          show "finite_tree (fst (appendDistTrace (T,G) w))"            
            using distribute_extension_finite[of T M G cg_lookup cg_insert \<alpha> "xy#u@w" False "(append_heuristic_input M)", OF \<open>finite_tree T\<close>]
            using distribute_extension_finite[of T' M G' cg_lookup cg_insert \<beta> "u@w" False "(append_heuristic_input M)"]
            unfolding appendDistTrace case_prod_conv *** Let_def fst_conv 
            by blast
        qed
        then show ?thesis
          unfolding ** using \<open>finite_tree T\<close>
          apply (induction ws rule: rev_induct; simp)
          by (metis (no_types, opaque_lifting) fst_conv old.prod.exhaust) 
      next
        case False

        obtain T' G' where ***: "distribute_extension M T G cg_lookup cg_insert \<alpha> (xy#u) False (append_heuristic_input M) = (T',G')"
            using prod.exhaust by metis

        show "finite_tree (fst (handleTrace (T, G) u))"            
          using distribute_extension_finite[of T M G cg_lookup cg_insert \<alpha> "xy#u" False "(append_heuristic_input M)", OF \<open>finite_tree T\<close>]
          using distribute_extension_finite[of T' M G' cg_lookup cg_insert \<beta> "u" False "(append_heuristic_input M)"]
          using False
          unfolding case_prod_conv *** Let_def fst_conv handleTrace 
          by force
      qed
    qed

    then show ?case
      unfolding *
      by (metis (no_types, opaque_lifting) snoc.IH fst_conv old.prod.exhaust) 
  qed
qed


lemma establish_convergence_static_properties :
  assumes "observable M1"
      and "observable M2"
      and "minimal M1"
      and "minimal M2"
      and "inputs M2 = inputs M1"
      and "outputs M2 = outputs M1"
      and "t \<in> transitions M1"
      and "t_source t \<in> reachable_states M1"
      and "is_state_cover_assignment M1 V"
      and "V (t_source t) @ [(t_input t, t_output t)] \<in> L M2"
      and "V ` reachable_states M1 \<subseteq> set T"
      and "preserves_divergence M1 M2 (V ` reachable_states M1)"
      and "convergence_graph_lookup_invar M1 M2 cg_lookup G"
      and "convergence_graph_insert_invar M1 M2 cg_lookup cg_insert"
      and "\<And> q1 q2 . q1 \<in> states M1 \<Longrightarrow> q2 \<in> states M1 \<Longrightarrow> q1 \<noteq> q2 \<Longrightarrow> \<exists> io . \<forall> k1 k2 . io \<in> set (dist_fun k1 q1) \<inter> set (dist_fun k2 q2) \<and> distinguishes M1 q1 q2 io"
      and "\<And> q . q \<in> reachable_states M1 \<Longrightarrow> set (dist_fun 0 q) \<subseteq> set (after T (V q))"
      and "\<And> q k . q \<in> states M1 \<Longrightarrow> finite_tree (dist_fun k q)"
      and "L M1 \<inter> set (fst (establish_convergence_static dist_fun M1 V T G cg_insert cg_lookup m t)) = L M2 \<inter> set (fst (establish_convergence_static dist_fun M1 V T G cg_insert cg_lookup m t))"
shows "\<forall> \<gamma> x y . length (\<gamma>@[(x,y)]) \<le> m - size_r M1 \<longrightarrow>
                  \<gamma> \<in> LS M1 (after_initial M1 (V (t_source t) @ [(t_input t, t_output t)])) \<longrightarrow>
                  x \<in> inputs M1 \<longrightarrow> y \<in> outputs M1 \<longrightarrow>
                  L M1 \<inter> ((V ` reachable_states M1) \<union> {\<omega>@\<omega>' | \<omega> \<omega>' . \<omega> \<in> {((V (t_source t)) @ [(t_input t,t_output t)]), (V (t_target t))} \<and> \<omega>' \<in> list.set (prefixes (\<gamma>@[(x,y)]))}) = L M2 \<inter>  ((V ` reachable_states M1) \<union> {\<omega>@\<omega>' | \<omega> \<omega>' . \<omega> \<in> {((V (t_source t)) @ [(t_input t,t_output t)]), (V (t_target t))} \<and> \<omega>' \<in> list.set (prefixes (\<gamma>@[(x,y)]))})
                  \<and> preserves_divergence M1 M2 ((V ` reachable_states M1) \<union> {\<omega>@\<omega>' | \<omega> \<omega>' . \<omega> \<in> {((V (t_source t)) @ [(t_input t,t_output t)]), (V (t_target t))} \<and> \<omega>' \<in> list.set (prefixes (\<gamma>@[(x,y)]))})"
(is "?P1a")
and   "preserves_divergence M1 M2 ((V ` reachable_states M1) \<union> {((V (t_source t)) @ [(t_input t,t_output t)]), (V (t_target t))})"
(is "?P1b")
and   "convergence_graph_lookup_invar M1 M2 cg_lookup (snd (establish_convergence_static dist_fun M1 V T G cg_insert cg_lookup m t))"
(is "?P2")
proof -

  
  define \<alpha> where \<alpha>: "\<alpha> = V (t_source t)"
  define xy where xy: "xy = (t_input t, t_output t)"
  define \<beta> where \<beta>: "\<beta> = V (t_target t)"
  define qSource where qSource: "qSource = (after_initial M1 (V (t_source t)))"
  define qTarget where qTarget: "qTarget = (after_initial M1 (V (t_target t)))"
  define k where k: "k = m - size_r M1"
  define ttc where ttc : "ttc = [] # traces_to_check M1 qTarget k"
  define handleTrace where handleTrace: "handleTrace = (\<lambda> (T,G) u . 
          if is_in_language M1 qTarget u 
            then let
                qu = FSM.after M1 qTarget u; 
                ws = sorted_list_of_maximal_sequences_in_tree (dist_fun (Suc (length u)) qu);
                appendDistTrace = (\<lambda> (T,G) w . let
                                                  (T',G') = distribute_extension M1 T G cg_lookup cg_insert \<alpha> (xy#u@w) False (append_heuristic_input M1)
                                                in distribute_extension M1 T' G' cg_lookup cg_insert \<beta> (u@w) False (append_heuristic_input M1))
                in foldl appendDistTrace (T,G) ws                
            else let
                (T',G') = distribute_extension M1 T G cg_lookup cg_insert \<alpha> (xy#u) False (append_heuristic_input M1)
                in distribute_extension M1 T' G' cg_lookup cg_insert \<beta> u False (append_heuristic_input M1))"


  have result: "establish_convergence_static dist_fun M1 V T G cg_insert cg_lookup m t = foldl handleTrace (T,G) ttc"
    unfolding establish_convergence_static.simps \<alpha> xy \<beta> qSource qTarget k ttc handleTrace Let_def by force
  then have result_pass: "L M1 \<inter> set (fst (foldl handleTrace (T,G) ttc)) = L M2 \<inter> set (fst (foldl handleTrace (T,G) ttc))"
    using assms(18) by auto

  have "V (t_source t) \<in> L M1" and "t_source t = qSource"
    using state_cover_assignment_after[OF assms(1,9,8)] unfolding qSource by auto
  then have "qSource \<in> states M1"
    unfolding qSource
    by (simp add: assms(8) reachable_state_is_state) 
  have "\<alpha> \<in> L M1"
    using \<open>V (t_source t) \<in> L M1\<close> unfolding \<alpha> by auto
  have "\<alpha> \<in> L M2"
    by (metis \<alpha> assms(10) language_prefix)


  have "qTarget \<in> reachable_states M1"
    using reachable_states_next[OF assms(8,7)] unfolding qTarget
    by (metis assms(1) assms(9) is_state_cover_assignment_observable_after) 
  then have "qTarget \<in> states M1"
    using reachable_state_is_state by metis
  have "V (t_target t) \<in> L M1"
    by (meson assms(7) assms(8) assms(9) is_state_cover_assignment_language reachable_states_next) 
  then have "\<beta> \<in> L M1"
    unfolding \<beta> by auto
  have "t_target t = qTarget"
    by (metis assms(1) assms(7) assms(8) assms(9) is_state_cover_assignment_observable_after qTarget reachable_states_next)
  have "converge M1 (\<alpha>@[xy]) \<beta>"
    using state_cover_transition_converges[OF assms(1,9,7,8)]
    unfolding \<alpha> xy \<beta> .
  then have "\<alpha>@[xy] \<in> L M1"
    by auto

  have "L M1 \<inter> set T = L M2 \<inter> set T"
    using assms(18) establish_convergence_static_subset[of T dist_fun M1 V G cg_insert cg_lookup m t]
    by blast
  then have "\<beta> \<in> L M2"
    using reachable_states_next[OF assms(8,7)] assms(11) \<open>\<beta> \<in> L M1\<close>
    unfolding \<beta> qTarget by blast   

  have "(\<forall> u w . u \<in> list.set ttc \<longrightarrow> u \<in> LS M1 qTarget \<longrightarrow> w \<in> set (dist_fun (Suc (length u)) (FSM.after M1 qTarget u)) \<longrightarrow> L M1 \<inter> {\<alpha> @ [xy] @ u @ w, \<beta> @ u @ w} = L M2 \<inter> {\<alpha> @ [xy] @ u @ w, \<beta> @ u @ w})
        \<and> (\<forall> u w . u \<in> list.set ttc \<longrightarrow> u \<notin> LS M1 qTarget \<longrightarrow> L M1 \<inter> {\<alpha>@[xy]@u,\<beta>@u} = L M2 \<inter> {\<alpha>@[xy]@u,\<beta>@u})
        \<and> (convergence_graph_lookup_invar M1 M2 cg_lookup (snd (foldl handleTrace (T,G) ttc)))"
    using result_pass
  proof (induction ttc rule: rev_induct)
    case Nil
    then show ?case using assms(13) by auto
  next
    case (snoc a ttc)

    have *:"foldl handleTrace (T, G) (ttc@[a]) = handleTrace (foldl handleTrace (T,G) ttc) a"
      by auto
    have "L M1 \<inter> Prefix_Tree.set (fst (foldl handleTrace (T, G) ttc)) = L M2 \<inter> Prefix_Tree.set (fst (foldl handleTrace (T, G) ttc))"
      using snoc.prems handleTrace_subset_helper[of handleTrace M1 qTarget dist_fun cg_lookup cg_insert, OF handleTrace]
      unfolding *
      by (metis (no_types, opaque_lifting) fst_conv inter_eq_subsetI old.prod.exhaust)
    then have IH1: "\<And> u w. u \<in> list.set ttc \<Longrightarrow> u \<in> LS M1 qTarget \<Longrightarrow> w \<in> Prefix_Tree.set (dist_fun (Suc (length u)) (FSM.after M1 qTarget u)) \<Longrightarrow> L M1 \<inter> {\<alpha> @ [xy] @ u @ w, \<beta> @ u @ w} = L M2 \<inter> {\<alpha> @ [xy] @ u @ w, \<beta> @ u @ w}"
          and IH2: "\<And>u w. u \<in> list.set ttc \<Longrightarrow> u \<notin> LS M1 qTarget \<Longrightarrow> L M1 \<inter> {\<alpha> @ [xy] @ u, \<beta> @ u} = L M2 \<inter> {\<alpha> @ [xy] @ u, \<beta> @ u}"
          and IH3: "convergence_graph_lookup_invar M1 M2 cg_lookup (snd (foldl handleTrace (T, G) ttc))"
      using snoc.IH
      by presburger+


    show ?case proof (cases "is_in_language M1 qTarget a")
      case True

      define qa where qa: "qa = FSM.after M1 qTarget a"
      define ws where ws: "ws = sorted_list_of_maximal_sequences_in_tree (dist_fun (Suc (length a)) qa)"
      define appendDistTrace where appendDistTrace: "appendDistTrace = (\<lambda> (T,G) w . let
                                                (T',G') = distribute_extension M1 T G cg_lookup cg_insert \<alpha> (xy#a@w) False (append_heuristic_input M1)
                                                in distribute_extension M1 T' G' cg_lookup cg_insert \<beta> (a@w) False (append_heuristic_input M1))"


      have **: "\<And> TG . handleTrace TG a = foldl appendDistTrace TG ws"
        using \<open>is_in_language M1 qTarget a\<close> 
        unfolding qa ws appendDistTrace Let_def case_prod_conv assms True handleTrace by force
      have "foldl handleTrace (T, G) (ttc@[a]) = foldl appendDistTrace (foldl handleTrace (T, G) ttc) ws"
        unfolding *  
        unfolding True 
        unfolding ** by auto
      then have "L M1 \<inter> set (fst (foldl appendDistTrace (foldl handleTrace (T, G) ttc) ws)) = L M2 \<inter> set (fst (foldl appendDistTrace (foldl handleTrace (T, G) ttc) ws))"
        using snoc.prems by metis

      then have handleTrace_props: "(\<forall> w . w \<in> list.set ws \<longrightarrow> ((\<exists> \<alpha>' . converge M1 \<alpha> \<alpha>' \<and> (\<alpha>'@[xy]@a@w) \<in> set (fst (foldl appendDistTrace (foldl handleTrace (T, G) ttc) ws)) \<and> converge M2 \<alpha> \<alpha>')
                                        \<and> (\<exists> \<beta>' . converge M1 \<beta> \<beta>' \<and> (\<beta>'@a@w) \<in> set (fst (foldl appendDistTrace (foldl handleTrace (T, G) ttc) ws)) \<and> converge M2 \<beta> \<beta>')))
            \<and> convergence_graph_lookup_invar M1 M2 cg_lookup (snd (foldl appendDistTrace (foldl handleTrace (T, G) ttc) ws))"
      proof (induction ws rule: rev_induct)
        case Nil
        then show ?case using IH3 by auto
      next
        case (snoc v ws)

        have *:"foldl appendDistTrace (foldl handleTrace (T, G) ttc) (ws@[v]) = appendDistTrace (foldl appendDistTrace (foldl handleTrace (T, G) ttc) ws) v"
          by auto

            
        define Tws where Tws: "Tws = fst (foldl appendDistTrace (foldl handleTrace (T, G) ttc) ws)"
        define Gws where Gws: "Gws = snd (foldl appendDistTrace (foldl handleTrace (T, G) ttc) ws)"

        have "(foldl appendDistTrace (foldl handleTrace (T, G) ttc) ws) = (Tws,Gws)"
          unfolding Tws Gws by auto

        obtain T' G' where "distribute_extension M1 Tws Gws cg_lookup cg_insert \<alpha> (xy#a@v) False (append_heuristic_input M1) = (T',G')"
          using prod.exhaust by metis

        have **: "appendDistTrace (foldl appendDistTrace (foldl handleTrace (T, G) ttc) ws) v
                = distribute_extension M1 T' G' cg_lookup cg_insert \<beta> (a@v) False (append_heuristic_input M1)"
          using \<open>distribute_extension M1 Tws Gws cg_lookup cg_insert \<alpha> (xy # a @ v) False (append_heuristic_input M1) = (T', G')\<close> \<open>foldl appendDistTrace (foldl handleTrace (T, G) ttc) ws = (Tws, Gws)\<close> appendDistTrace by auto 

        have pass_outer : "L M1 \<inter> set (fst (distribute_extension M1 T' G' cg_lookup cg_insert \<beta> (a@v) False (append_heuristic_input M1)))
                            = L M2 \<inter> set (fst (distribute_extension M1 T' G' cg_lookup cg_insert \<beta> (a@v) False (append_heuristic_input M1)))"  
          using snoc.prems unfolding * ** .
        moreover have "set (fst (distribute_extension M1 Tws Gws cg_lookup cg_insert \<alpha> (xy#a@v) False (append_heuristic_input M1))) \<subseteq> set (fst (distribute_extension M1 T' G' cg_lookup cg_insert \<beta> (a@v) False (append_heuristic_input M1)))"
          using distribute_extension_subset[of T' M1 G' cg_lookup cg_insert \<beta> "(a@v)" False "(append_heuristic_input M1)"]
          using \<open>distribute_extension M1 Tws Gws cg_lookup cg_insert \<alpha> (xy#a@v) False (append_heuristic_input M1) = (T',G')\<close>
          by (metis fst_conv)
        ultimately have pass_inner: "L M1 \<inter> set (fst (distribute_extension M1 Tws Gws cg_lookup cg_insert \<alpha> (xy#a@v) False (append_heuristic_input M1)))
                            = L M2 \<inter> set (fst (distribute_extension M1 Tws Gws cg_lookup cg_insert \<alpha> (xy#a@v) False (append_heuristic_input M1)))"  
          by blast
        then have pass_ws: "L M1 \<inter> Prefix_Tree.set (fst (foldl appendDistTrace (foldl handleTrace (T, G) ttc) ws)) =
                              L M2 \<inter> Prefix_Tree.set (fst (foldl appendDistTrace (foldl handleTrace (T, G) ttc) ws))"
          using distribute_extension_subset[of Tws M1 Gws cg_lookup cg_insert]
          unfolding Tws Gws
          by blast


        have "set (fst (foldl appendDistTrace (foldl handleTrace (T, G) ttc) ws)) \<subseteq> set (fst (foldl appendDistTrace (foldl handleTrace (T, G) ttc) (ws@[v])))"
          using appendDistTrace_subset_helper[OF appendDistTrace]
          by (metis "*" Tws \<open>foldl appendDistTrace (foldl handleTrace (T, G) ttc) ws = (Tws, Gws)\<close>)  

        have "convergence_graph_lookup_invar M1 M2 cg_lookup (snd (foldl appendDistTrace (foldl handleTrace (T, G) ttc) ws))"
          using snoc.IH[OF pass_ws ] by auto
        then have "convergence_graph_lookup_invar M1 M2 cg_lookup (snd (distribute_extension M1 Tws Gws cg_lookup cg_insert \<alpha> (xy#a@v) False (append_heuristic_input M1)))"
          using distribute_extension_adds_sequence(2)[OF assms(1,3) \<open>\<alpha> \<in> L M1\<close> \<open>\<alpha> \<in> L M2\<close> _ assms(14) pass_inner append_heuristic_input_in]
          unfolding Gws by blast
        then have "convergence_graph_lookup_invar M1 M2 cg_lookup (snd (appendDistTrace (foldl appendDistTrace (foldl handleTrace (T, G) ttc) ws) v))"
          unfolding ** \<open>distribute_extension M1 Tws Gws cg_lookup cg_insert \<alpha> (xy#a@v) False (append_heuristic_input M1) = (T',G')\<close> snd_conv
          using distribute_extension_adds_sequence(2)[OF assms(1,3) \<open>\<beta> \<in> L M1\<close> \<open>\<beta> \<in> L M2\<close> _ assms(14) pass_outer append_heuristic_input_in]
          by blast
        moreover have "\<And> w . w \<in> list.set (ws@[v]) \<Longrightarrow> ((\<exists> \<alpha>' . converge M1 \<alpha> \<alpha>' \<and> (\<alpha>'@[xy]@a@w) \<in> set (fst (foldl appendDistTrace (foldl handleTrace (T, G) ttc) (ws@[v]))) \<and> converge M2 \<alpha> \<alpha>')
                                        \<and> (\<exists> \<beta>' . converge M1 \<beta> \<beta>' \<and> (\<beta>'@a@w) \<in> set (fst (foldl appendDistTrace (foldl handleTrace (T, G) ttc) (ws@[v]))) \<and> converge M2 \<beta> \<beta>'))"
        proof -
          fix w assume "w \<in> list.set (ws@[v])"
          then consider "w \<in> list.set ws" | "v = w"
            by auto
          then show "((\<exists> \<alpha>' . converge M1 \<alpha> \<alpha>' \<and> (\<alpha>'@[xy]@a@w) \<in> set (fst (foldl appendDistTrace (foldl handleTrace (T, G) ttc) (ws@[v]))) \<and> converge M2 \<alpha> \<alpha>')
                                        \<and> (\<exists> \<beta>' . converge M1 \<beta> \<beta>' \<and> (\<beta>'@a@w) \<in> set (fst (foldl appendDistTrace (foldl handleTrace (T, G) ttc) (ws@[v]))) \<and> converge M2 \<beta> \<beta>'))"
          proof cases
            case 1
            then show ?thesis using snoc.IH[OF pass_ws] 
              using \<open>set (fst (foldl appendDistTrace (foldl handleTrace (T, G) ttc) ws)) \<subseteq> set (fst (foldl appendDistTrace (foldl handleTrace (T, G) ttc) (ws@[v])))\<close>
              by blast
          next
            case 2

            have "\<exists>u'. converge M1 \<alpha> u' \<and> u' @ xy # a @ w \<in> set T' \<and> converge M2 \<alpha> u'"
              using distribute_extension_adds_sequence(1)[OF assms(1,3) \<open>\<alpha> \<in> L M1\<close> \<open>\<alpha> \<in> L M2\<close> _ assms(14) pass_inner append_heuristic_input_in]
                    \<open>convergence_graph_lookup_invar M1 M2 cg_lookup (snd (foldl appendDistTrace (foldl handleTrace (T, G) ttc) ws))\<close>
              unfolding Gws[symmetric] 
              unfolding \<open>distribute_extension M1 Tws Gws cg_lookup cg_insert \<alpha> (xy#a@v) False (append_heuristic_input M1) = (T',G')\<close>  
              unfolding 2 fst_conv
              by blast
            then have "(\<exists> \<alpha>' . converge M1 \<alpha> \<alpha>' \<and> (\<alpha>'@[xy]@a@w) \<in> set (fst (foldl appendDistTrace (foldl handleTrace (T, G) ttc) (ws@[v]))) \<and> converge M2 \<alpha> \<alpha>')"
              using "**" \<open>Prefix_Tree.set (fst (distribute_extension M1 Tws Gws cg_lookup cg_insert \<alpha> (xy # a @ v) False (append_heuristic_input M1))) \<subseteq> Prefix_Tree.set (fst (distribute_extension M1 T' G' cg_lookup cg_insert \<beta> (a @ v) False (append_heuristic_input M1)))\<close> \<open>distribute_extension M1 Tws Gws cg_lookup cg_insert \<alpha> (xy # a @ v) False (append_heuristic_input M1) = (T', G')\<close> by auto
            moreover have "(\<exists> \<beta>' . converge M1 \<beta> \<beta>' \<and> (\<beta>'@a@w) \<in> set (fst (foldl appendDistTrace (foldl handleTrace (T, G) ttc) (ws@[v]))) \<and> converge M2 \<beta> \<beta>')"
              using distribute_extension_adds_sequence(1)[OF assms(1,3) \<open>\<beta> \<in> L M1\<close> \<open>\<beta> \<in> L M2\<close> _ assms(14) pass_outer append_heuristic_input_in]
              using \<open>convergence_graph_lookup_invar M1 M2 cg_lookup (snd (distribute_extension M1 Tws Gws cg_lookup cg_insert \<alpha> (xy#a@v) False (append_heuristic_input M1)))\<close>
              unfolding \<open>distribute_extension M1 Tws Gws cg_lookup cg_insert \<alpha> (xy#a@v) False (append_heuristic_input M1) = (T',G')\<close> snd_conv
              unfolding * ** 
              unfolding 2
              by blast
            ultimately show ?thesis by blast
          qed
        qed
        ultimately show ?case 
          by fastforce
      qed

      have "\<And> u w. u \<in> list.set (ttc@[a]) \<Longrightarrow> u \<in> LS M1 qTarget \<Longrightarrow> w \<in> Prefix_Tree.set (dist_fun (Suc (length u)) (FSM.after M1 qTarget u)) \<Longrightarrow> L M1 \<inter> {\<alpha> @ [xy] @ u @ w, \<beta> @ u @ w} = L M2 \<inter> {\<alpha> @ [xy] @ u @ w, \<beta> @ u @ w}"
      proof -
        fix u w assume "u \<in> list.set (ttc@[a])" and a1:"u \<in> LS M1 qTarget" and a2:"w \<in> Prefix_Tree.set (dist_fun (Suc (length u)) (FSM.after M1 qTarget u))"
        then consider "u \<in> list.set ttc" | "a = u"
          by auto
        then show "L M1 \<inter> {\<alpha> @ [xy] @ u @ w, \<beta> @ u @ w} = L M2 \<inter> {\<alpha> @ [xy] @ u @ w, \<beta> @ u @ w}" 
        proof cases
          case 1
          then show ?thesis 
            using IH1[OF _ a1 a2] by blast
        next
          case 2

          obtain w' where "w@w' \<in> list.set ws"
          proof -
            have "qa \<in> reachable_states M1"
              using \<open>qTarget \<in> reachable_states M1\<close> \<open>u \<in> LS M1 qTarget\<close>
              by (metis "2" after_reachable assms(1) qa)
            then have "finite_tree (dist_fun (Suc (length u)) qa)"  
              using \<open>\<And> q k . q \<in> states M1 \<Longrightarrow> finite_tree (dist_fun k q)\<close> reachable_state_is_state[of qa M1]
              by blast
            moreover have "w \<in> set (dist_fun (Suc (length u)) qa)"
              using \<open>w \<in> set (dist_fun (Suc (length u)) (FSM.after M1 qTarget u))\<close>
              unfolding qa 2 .
            ultimately show ?thesis
              using sorted_list_of_maximal_sequences_in_tree_ob[of "dist_fun (Suc (length u)) qa" w]
              using that unfolding ws 2 by blast
          qed
          then obtain \<alpha>' \<beta>' where "converge M1 \<alpha> \<alpha>'" and "\<alpha>' @ [xy] @ a @ w@w' \<in> Prefix_Tree.set (fst (foldl handleTrace (T, G) (ttc@[a])))" and "converge M2 \<alpha> \<alpha>'"
                               and "converge M1 \<beta> \<beta>'" and "\<beta>' @ a @ w@w' \<in> Prefix_Tree.set (fst (foldl handleTrace (T, G) (ttc@[a])))" and "converge M2 \<beta> \<beta>'"
            using handleTrace_props
            unfolding **[symmetric] *[symmetric]
            by blast
          then have "\<alpha>' @ [xy] @ a @ w \<in> Prefix_Tree.set (fst (foldl handleTrace (T, G) (ttc@[u])))"
                and "\<beta>' @ a @ w \<in> Prefix_Tree.set (fst (foldl handleTrace (T, G) (ttc@[u])))"
            using set_prefix[of "\<alpha>' @ [xy] @ a @ w" w']
            using set_prefix[of "\<beta>' @ a @ w" w']
            unfolding 2
            by auto

          
          have "\<alpha> @ [xy] @ u @ w \<in> L M1 = (\<alpha>' @ [xy] @ u @ w \<in> L M1)"
            using \<open>converge M1 \<alpha> \<alpha>'\<close>
            using assms(1) converge_append_language_iff by blast
          also have "\<dots> = (\<alpha>' @ [xy] @ u @ w \<in> L M2)"
            using \<open>\<alpha>' @ [xy] @ a @ w \<in> Prefix_Tree.set (fst (foldl handleTrace (T, G) (ttc@[u])))\<close>
            using snoc.prems unfolding 2
            by blast
          also have "\<dots> = (\<alpha> @ [xy] @ u @ w \<in> L M2)"
            using \<open>converge M2 \<alpha> \<alpha>'\<close>
            using assms(2) converge_append_language_iff by blast
          finally have "\<alpha> @ [xy] @ u @ w \<in> L M1 = (\<alpha> @ [xy] @ u @ w \<in> L M2)" .

          have "\<beta> @ u @ w \<in> L M1 = (\<beta>' @ u @ w \<in> L M1)"
            using \<open>converge M1 \<beta> \<beta>'\<close>
            using assms(1) converge_append_language_iff by blast
          also have "\<dots> = (\<beta>' @ u @ w \<in> L M2)"
            using \<open>\<beta>' @ a @ w \<in> Prefix_Tree.set (fst (foldl handleTrace (T, G) (ttc@[u])))\<close>
            using snoc.prems unfolding 2
            by blast
          also have "\<dots> = (\<beta> @ u @ w \<in> L M2)"
            using \<open>converge M2 \<beta> \<beta>'\<close>
            using assms(2) converge_append_language_iff by blast
          finally have "\<beta> @ u @ w \<in> L M1 = (\<beta> @ u @ w \<in> L M2)" .

          then show ?thesis
            using \<open>\<alpha> @ [xy] @ u @ w \<in> L M1 = (\<alpha> @ [xy] @ u @ w \<in> L M2)\<close> 
            by blast
        qed 
      qed
      moreover have "\<And> u w . u \<in> list.set (ttc@[a]) \<Longrightarrow> u \<notin> LS M1 qTarget \<Longrightarrow> L M1 \<inter> {\<alpha> @ [xy] @ u, \<beta> @ u} = L M2 \<inter> {\<alpha> @ [xy] @ u, \<beta> @ u}"
      proof -
        fix u w assume "u \<in> list.set (ttc@[a])" and "u \<notin> LS M1 qTarget"

        then have "u \<noteq> a"
          using True 
          unfolding is_in_language_iff[OF assms(1) \<open>qTarget \<in> states M1\<close>]
          by auto
        then have "u \<in> list.set ttc"
          using \<open>u \<in> list.set (ttc@[a])\<close> by auto
        then show "L M1 \<inter> {\<alpha> @ [xy] @ u, \<beta> @ u} = L M2 \<inter> {\<alpha> @ [xy] @ u, \<beta> @ u}"
          using IH2[OF _ \<open>u \<notin> LS M1 qTarget\<close>] by blast
      qed
      moreover have "convergence_graph_lookup_invar M1 M2 cg_lookup (snd (foldl handleTrace (T, G) (ttc@[a])))"
        using handleTrace_props unfolding * ** by blast
      ultimately show ?thesis
        by blast
    next
      case False

      define Tc where Tc: "Tc = fst (foldl handleTrace (T, G) ttc)"
      define Gc where Gc: "Gc = snd (foldl handleTrace (T, G) ttc)"

      have "(foldl handleTrace (T, G) ttc) = (Tc,Gc)"
        unfolding Tc Gc by auto

      define T' where T': "T' = fst (distribute_extension M1 Tc Gc cg_lookup cg_insert \<alpha> (xy#a) False (append_heuristic_input M1))"
      define G' where G': "G' = snd (distribute_extension M1 Tc Gc cg_lookup cg_insert \<alpha> (xy#a) False (append_heuristic_input M1))"

      have **: "handleTrace (foldl handleTrace (T,G) ttc) a = distribute_extension M1 T' G' cg_lookup cg_insert \<beta> a False (append_heuristic_input M1)"
        using False
        unfolding \<open>(foldl handleTrace (T, G) ttc) = (Tc,Gc)\<close>
        unfolding handleTrace 
        unfolding case_prod_conv Let_def 
        unfolding T' G' Tc Gc
        by (meson case_prod_beta') 


      have pass_outer : "L M1 \<inter> set (fst (distribute_extension M1 T' G' cg_lookup cg_insert \<beta> a False (append_heuristic_input M1)))
                            = L M2 \<inter> set (fst (distribute_extension M1 T' G' cg_lookup cg_insert \<beta> a False (append_heuristic_input M1)))"  
        using snoc.prems unfolding * ** .
      moreover have "set (fst (distribute_extension M1 Tc Gc cg_lookup cg_insert \<alpha> (xy#a) False (append_heuristic_input M1))) \<subseteq> set (fst (distribute_extension M1 T' G' cg_lookup cg_insert \<beta> (a) False (append_heuristic_input M1)))"
        using distribute_extension_subset[of T' M1 G' cg_lookup cg_insert \<beta> "a" False "(append_heuristic_input M1)"]
        using \<open>(foldl handleTrace (T, G) ttc) = (Tc,Gc)\<close>
        using T' by blast
      ultimately have pass_inner: "L M1 \<inter> set (fst (distribute_extension M1 Tc Gc cg_lookup cg_insert \<alpha> (xy#a) False (append_heuristic_input M1)))
                          = L M2 \<inter> set (fst (distribute_extension M1 Tc Gc cg_lookup cg_insert \<alpha> (xy#a) False (append_heuristic_input M1)))"  
        by blast
        
      
      have "convergence_graph_lookup_invar M1 M2 cg_lookup Gc"
        using snoc.IH[OF \<open>L M1 \<inter> Prefix_Tree.set (fst (foldl handleTrace (T, G) ttc)) = L M2 \<inter> Prefix_Tree.set (fst (foldl handleTrace (T, G) ttc))\<close>]
        unfolding Gc by blast
      then have "convergence_graph_lookup_invar M1 M2 cg_lookup G'"
        using distribute_extension_adds_sequence(2)[OF assms(1,3) \<open>\<alpha> \<in> L M1\<close> \<open>\<alpha> \<in> L M2\<close> _ assms(14) pass_inner append_heuristic_input_in]
        unfolding G' by blast  
      then have "convergence_graph_lookup_invar M1 M2 cg_lookup (snd (foldl handleTrace (T, G) (ttc@[a])))"
          unfolding * **
          using distribute_extension_adds_sequence(2)[OF assms(1,3) \<open>\<beta> \<in> L M1\<close> \<open>\<beta> \<in> L M2\<close> _ assms(14) pass_outer append_heuristic_input_in]
          by blast
      moreover have "\<And> u w. u \<in> list.set (ttc@[a]) \<Longrightarrow> u \<in> LS M1 qTarget \<Longrightarrow> w \<in> Prefix_Tree.set (dist_fun (Suc (length u)) (FSM.after M1 qTarget u)) \<Longrightarrow> L M1 \<inter> {\<alpha> @ [xy] @ u @ w, \<beta> @ u @ w} = L M2 \<inter> {\<alpha> @ [xy] @ u @ w, \<beta> @ u @ w}"
      proof -
        fix u w assume "u \<in> list.set (ttc@[a])" and a1:"u \<in> LS M1 qTarget" and a2:"w \<in> Prefix_Tree.set (dist_fun (Suc (length u)) (FSM.after M1 qTarget u))"
        then have "u \<noteq> a"
          using False 
          unfolding is_in_language_iff[OF assms(1) \<open>qTarget \<in> states M1\<close>]
          by auto
        then have "u \<in> list.set ttc"
          using \<open>u \<in> list.set (ttc@[a])\<close> by auto
        then show "L M1 \<inter> {\<alpha> @ [xy] @ u @ w, \<beta> @ u @ w} = L M2 \<inter> {\<alpha> @ [xy] @ u @ w, \<beta> @ u @ w}"
          using IH1[OF _ a1 a2]
          by blast
      qed
      moreover have "\<And> u w . u \<in> list.set (ttc@[a]) \<Longrightarrow> u \<notin> LS M1 qTarget \<Longrightarrow> L M1 \<inter> {\<alpha> @ [xy] @ u, \<beta> @ u} = L M2 \<inter> {\<alpha> @ [xy] @ u, \<beta> @ u}"
      proof -
        fix u w assume "u \<in> list.set (ttc@[a])" and "u \<notin> LS M1 qTarget"
        then consider "u \<in> list.set ttc" | "a = u"
          by auto
        then show "L M1 \<inter> {\<alpha> @ [xy] @ u, \<beta> @ u} = L M2 \<inter> {\<alpha> @ [xy] @ u, \<beta> @ u}" proof cases
          case 1
          then show ?thesis 
            using IH2[OF _ \<open>u \<notin> LS M1 qTarget\<close>] by blast
        next
          case 2

          obtain \<alpha>' where "converge M1 \<alpha> \<alpha>'" and "\<alpha>' @ xy # a \<in> set (fst (foldl handleTrace (T, G) (ttc@[a])))" and "converge M2 \<alpha> \<alpha>'"
            using distribute_extension_adds_sequence(1)[OF assms(1,3) \<open>\<alpha> \<in> L M1\<close> \<open>\<alpha> \<in> L M2\<close> _ assms(14) pass_inner append_heuristic_input_in] \<open>convergence_graph_lookup_invar M1 M2 cg_lookup Gc\<close>
            unfolding T'[symmetric]
            using distribute_extension_subset[of T' M1 G' cg_lookup cg_insert \<beta> "a" False "(append_heuristic_input M1)"] 
            unfolding * ** by blast
          have "\<And> \<alpha>' . \<alpha>' @ xy # u = \<alpha>' @ [xy] @ u"
            by auto

          obtain \<beta>' where "converge M1 \<beta> \<beta>'" and "\<beta>' @ a \<in> set (fst (foldl handleTrace (T, G) (ttc@[a])))" and "converge M2 \<beta> \<beta>'"
            using distribute_extension_adds_sequence(1)[OF assms(1,3) \<open>\<beta> \<in> L M1\<close> \<open>\<beta> \<in> L M2\<close> _ assms(14) pass_outer append_heuristic_input_in] \<open>convergence_graph_lookup_invar M1 M2 cg_lookup G'\<close>
            unfolding * ** by blast

          have "\<alpha> @ [xy] @ u \<in> L M1 = (\<alpha>' @ [xy] @ u \<in> L M1)"
            using \<open>converge M1 \<alpha> \<alpha>'\<close>
            using assms(1) converge_append_language_iff by blast
          also have "\<dots> = (\<alpha>' @ [xy] @ u \<in> L M2)"
            using \<open>\<alpha>' @ xy # a \<in> Prefix_Tree.set (fst (foldl handleTrace (T, G) (ttc@[a])))\<close>
            using snoc.prems unfolding 2 \<open>\<And> \<alpha>' . \<alpha>' @ xy # u = \<alpha>' @ [xy] @ u\<close> 
            by blast
          also have "\<dots> = (\<alpha> @ [xy] @ u \<in> L M2)"
            using \<open>converge M2 \<alpha> \<alpha>'\<close>
            using assms(2) converge_append_language_iff by blast
          finally have "\<alpha> @ [xy] @ u \<in> L M1 = (\<alpha> @ [xy] @ u \<in> L M2)" .

          have "\<beta> @ u \<in> L M1 = (\<beta>' @ u \<in> L M1)"
            using \<open>converge M1 \<beta> \<beta>'\<close>
            using assms(1) converge_append_language_iff by blast
          also have "\<dots> = (\<beta>' @ u \<in> L M2)"
            using \<open>\<beta>' @ a \<in> Prefix_Tree.set (fst (foldl handleTrace (T, G) (ttc@[a])))\<close>
            using snoc.prems unfolding 2
            by blast
          also have "\<dots> = (\<beta> @ u \<in> L M2)"
            using \<open>converge M2 \<beta> \<beta>'\<close>
            using assms(2) converge_append_language_iff by blast
          finally have "\<beta> @ u \<in> L M1 = (\<beta> @ u \<in> L M2)" .
          then show ?thesis
            using \<open>\<alpha> @ [xy] @ u \<in> L M1 = (\<alpha> @ [xy] @ u \<in> L M2)\<close>
            by blast
        qed 
      qed
      ultimately show ?thesis 
        by blast
    qed
  qed

  

  then have handleTrace_foldl_props_1: "\<And> u w. u \<in> list.set ttc \<Longrightarrow>
            u \<in> LS M1 qTarget \<Longrightarrow>
            w \<in> Prefix_Tree.set (dist_fun (Suc (length u)) (FSM.after M1 qTarget u)) \<Longrightarrow>
            L M1 \<inter> {\<alpha> @ [xy] @ u @ w, \<beta> @ u @ w} = L M2 \<inter> {\<alpha> @ [xy] @ u @ w, \<beta> @ u @ w}"
  and  handleTrace_foldl_props_2: "\<And>u w. u \<in> list.set ttc \<Longrightarrow> u \<notin> LS M1 qTarget \<Longrightarrow> L M1 \<inter> {\<alpha> @ [xy] @ u, \<beta> @ u} = L M2 \<inter> {\<alpha> @ [xy] @ u, \<beta> @ u}"
  and  "convergence_graph_lookup_invar M1 M2 cg_lookup (snd (foldl handleTrace (T, G) ttc))"
    by presburger+

  then show "?P2"
    unfolding result by blast

  show "preserves_divergence M1 M2 ((V ` reachable_states M1) \<union> {((V (t_source t)) @ [(t_input t,t_output t)]), (V (t_target t))})"
  proof -
    let ?w = "((V (t_source t)) @ [(t_input t,t_output t)])"

    

    have "V (t_target t) \<in> (V ` reachable_states M1)"
      by (simp add: \<open>qTarget \<in> reachable_states M1\<close> \<open>t_target t = qTarget\<close>)
    then have "((V ` reachable_states M1) \<union> {((V (t_source t)) @ [(t_input t,t_output t)]), (V (t_target t))}) = Set.insert ((V (t_source t)) @ [(t_input t,t_output t)]) (V ` reachable_states M1)"
      by blast
    moreover have "Set.insert ?w (V ` reachable_states M1) \<subseteq> L M1"
      using state_cover_assignment_language[OF assms(9)]
      using \<alpha> \<open>converge M1 (\<alpha> @ [xy]) \<beta>\<close> xy by auto 
    ultimately have *:"L M1 \<inter> (V ` reachable_states M1 \<union> {V (t_source t) @ [(t_input t, t_output t)], V (t_target t)}) = Set.insert ?w (V ` reachable_states M1)"
                and **:"L M1 \<inter> (V ` reachable_states M1) = (V ` reachable_states M1)"
      by blast+

    have "\<And> u . u \<in> Set.insert ?w (V ` reachable_states M1) \<Longrightarrow> \<not>converge M1 u ?w \<Longrightarrow> \<not>converge M2 u ?w"
    proof -
      fix u assume "u \<in> Set.insert ?w (V ` reachable_states M1)" and "\<not>converge M1 u ?w"
      moreover have "converge M1 ?w ?w"
        using \<open>\<alpha>@[xy] \<in> L M1\<close> unfolding \<alpha> xy by auto
      ultimately have "u \<in> (V ` reachable_states M1)" 
        by auto
      
      have "\<not>converge M1 u \<beta>"
        using \<open>\<not>converge M1 u ?w\<close> \<open>converge M1 (\<alpha>@[xy]) \<beta>\<close> unfolding \<alpha> xy \<beta>
        by auto  

      have "\<beta> = V qTarget"
        by (simp add: \<beta> \<open>t_target t = qTarget\<close>) 

      obtain qU where "qU \<in> reachable_states M1" and "u = V qU"
        using \<open>u \<in> (V ` reachable_states M1)\<close> by blast
      then have "qU = after_initial M1 u"
        using state_cover_assignment_after[OF assms(1,9)] by metis
      then have "qU \<noteq> qTarget"
        using \<open>\<not>converge M1 u \<beta>\<close>
        using \<beta> \<open>\<beta> \<in> L M1\<close> \<open>t_target t = qTarget\<close> \<open>u = V qU\<close> by fastforce 

      then obtain w where "\<forall> k1 k2 . w \<in> set (dist_fun k1 qU) \<inter> set (dist_fun k2 qTarget)" and "distinguishes M1 qU qTarget w"
        using assms(15)[OF reachable_state_is_state[OF \<open>qU \<in> reachable_states M1\<close>] \<open>qTarget \<in> states M1\<close>]
        by blast
      then have "w \<in> set (after T (V qU))" and "w \<in> set (after T (V qTarget))"
        using assms(16)[OF \<open>qU \<in> reachable_states M1\<close>]
        using assms(16)[OF \<open>qTarget \<in> reachable_states M1\<close>]
        by blast+


      have "[] \<in> list.set ttc"
        unfolding ttc by auto
      moreover have "[] \<in> LS M1 qTarget"
        using \<open>qTarget \<in> states M1\<close> by auto
      moreover have "w \<in> set (dist_fun (Suc (length [])) (FSM.after M1 qTarget []))"
        using \<open>\<forall> k1 k2 . w \<in> set (dist_fun k1 qU) \<inter> set (dist_fun k2 qTarget)\<close> by auto
      ultimately have "L M1 \<inter> {?w @ w, \<beta> @ w} = L M2 \<inter> {?w @ w, \<beta> @ w}"
        using handleTrace_foldl_props_1[of "[]" w]
        unfolding \<alpha> xy
        by auto
      moreover have "(?w @ w \<in> L M1) = (\<beta>@w \<in> L M1)"
        using converge_extend[OF assms(1) \<open>converge M1 (\<alpha>@[xy]) \<beta>\<close> _ \<open>\<beta> \<in> L M1\<close>, of w]
        using converge_extend[OF assms(1) _ _ \<open>\<alpha>@[xy] \<in> L M1\<close>, of \<beta> w] 
        using \<open>converge M1 (\<alpha>@[xy]) \<beta>\<close> unfolding converge_sym[where u=\<beta>]
        unfolding \<alpha>[symmetric] xy[symmetric]
        by blast
      ultimately have "(?w @ w \<in> L M2) = (\<beta>@w \<in> L M2)"
        by blast


      have "(w \<in> LS M1 qU) \<noteq> (w \<in> LS M1 qTarget)"
        using \<open>distinguishes M1 qU qTarget w\<close>
        unfolding distinguishes_def
        by blast 
      moreover have "(w \<in> LS M1 qU) = (u@w \<in> L M1)"
        by (metis "**" IntD1 \<open>qU = after_initial M1 u\<close> \<open>u \<in> V ` reachable_states M1\<close> after_language_iff assms(1))
      moreover have "(w \<in> LS M1 qTarget) = (\<beta>@w \<in> L M1)"
        by (metis \<open>\<beta> = V qTarget\<close> \<open>\<beta> \<in> L M1\<close> \<open>qTarget \<in> reachable_states M1\<close> after_language_iff assms(1) assms(9) is_state_cover_assignment_observable_after)
      ultimately have "(u@w \<in> L M1) \<noteq> (\<beta>@w \<in> L M1)"
        by blast
      moreover have "u@w \<in> set T" 
        using \<open>w \<in> set (after T (V qU))\<close>
        unfolding after_set \<open>u = V qU\<close>[symmetric]
        using \<open>u \<in> V ` reachable_states M1\<close> assms(11) by auto
      moreover have "\<beta>@w \<in> set T"
        using \<open>w \<in> set (after T (V qTarget))\<close>
        unfolding after_set \<open>\<beta> = V qTarget\<close>
        using \<open>qTarget \<in> reachable_states M1\<close> assms(11) by auto   
      ultimately have "(u@w \<in> L M2) \<noteq> (\<beta>@w \<in> L M2)"
        using \<open>L M1 \<inter> set T = L M2 \<inter> set T\<close> by blast
      then have "(u@w \<in> L M2) \<noteq> (?w@w \<in> L M2)"
        unfolding \<open>(?w @ w \<in> L M2) = (\<beta>@w \<in> L M2)\<close> .
      moreover have "(u@w \<in> L M2) = (w \<in> LS M2 (after_initial M2 u))"
        by (metis (no_types, lifting) "**" Int_iff \<open>L M1 \<inter> Prefix_Tree.set T = L M2 \<inter> Prefix_Tree.set T\<close> \<open>u \<in> V ` reachable_states M1\<close> after_language_iff assms(11) assms(2) inter_eq_subsetI)
      moreover have "(?w@w \<in> L M2) = (w \<in> LS M2 (after_initial M2 ?w))"
        using assms(10) unfolding \<alpha>[symmetric] xy[symmetric]
        by (metis assms(2) observable_after_language_append observable_after_language_none) 
      ultimately show "\<not>converge M2 u ?w"
        using converge.elims(2) by blast
    qed
    moreover have "\<And> v . v \<in> (V ` reachable_states M1) \<Longrightarrow> \<not>converge M1 ?w v \<Longrightarrow> \<not>converge M2 ?w v"
      using calculation unfolding converge_sym[where v="?w"]
      by blast
    ultimately show ?thesis
      using assms(12)
      unfolding preserves_divergence.simps
      unfolding * **
      by blast
  qed    

  have "\<And> \<gamma> x y . length (\<gamma>@[(x,y)]) \<le> m - size_r M1 \<Longrightarrow>
                  \<gamma> \<in> LS M1 (after_initial M1 (V (t_source t) @ [(t_input t, t_output t)])) \<Longrightarrow>
                  x \<in> inputs M1 \<Longrightarrow> y \<in> outputs M1 \<Longrightarrow>
                  L M1 \<inter> ((V ` reachable_states M1) \<union> {\<omega>@\<omega>' | \<omega> \<omega>' . \<omega> \<in> {((V (t_source t)) @ [(t_input t,t_output t)]), (V (t_target t))} \<and> \<omega>' \<in> list.set (prefixes (\<gamma>@[(x,y)]))}) = L M2 \<inter>  ((V ` reachable_states M1) \<union> {\<omega>@\<omega>' | \<omega> \<omega>' . \<omega> \<in> {((V (t_source t)) @ [(t_input t,t_output t)]), (V (t_target t))} \<and> \<omega>' \<in> list.set (prefixes (\<gamma>@[(x,y)]))})
                  \<and> preserves_divergence M1 M2 ((V ` reachable_states M1) \<union> {\<omega>@\<omega>' | \<omega> \<omega>' . \<omega> \<in> {((V (t_source t)) @ [(t_input t,t_output t)]), (V (t_target t))} \<and> \<omega>' \<in> list.set (prefixes (\<gamma>@[(x,y)]))})"
  proof 
    fix \<gamma> x y 
    assume "length (\<gamma>@[(x,y)]) \<le> m - size_r M1"
    and    "\<gamma> \<in> LS M1 (after_initial M1 (V (t_source t) @ [(t_input t, t_output t)]))"
    and    "x \<in> inputs M1"
    and    "y \<in> outputs M1"

    have "(after_initial M1 (V (t_source t) @ [(t_input t, t_output t)])) = qTarget"
      using \<open>converge M1 (\<alpha>@[xy]) \<beta>\<close>
      unfolding \<alpha>[symmetric] xy[symmetric] qTarget \<beta>[symmetric]
      using \<open>\<alpha> @ [xy] \<in> L M1\<close> \<open>\<beta> \<in> L M1\<close> assms(1) assms(3) convergence_minimal by blast
    then have "\<gamma> \<in> LS M1 qTarget"
      using \<open>\<gamma> \<in> LS M1 (after_initial M1 (V (t_source t) @ [(t_input t, t_output t)]))\<close>
      by auto

    then have "\<gamma>@[(x,y)] \<in> list.set (traces_to_check M1 qTarget k)"
      unfolding traces_to_check_set[OF assms(1) \<open>qTarget \<in> states M1\<close>] k
      using \<open>length (\<gamma>@[(x,y)]) \<le> m - size_r M1\<close> \<open>x \<in> inputs M1\<close> \<open>y \<in> outputs M1\<close>
      by blast
    then have "(\<gamma>@[(x,y)]) \<in> list.set ttc"
      unfolding ttc by auto

    have "\<And> \<gamma>' . \<gamma>' \<in> list.set (prefixes \<gamma>) \<Longrightarrow> \<gamma>' \<in> list.set ttc \<and> \<gamma>' \<in> LS M1 qTarget"
    proof 
      fix \<gamma>' assume "\<gamma>' \<in> list.set (prefixes \<gamma>)"
      then obtain \<gamma>'' where "\<gamma> = \<gamma>'@\<gamma>''"
        using prefixes_set_ob by blast
      then show "\<gamma>' \<in> LS M1 qTarget"
        using \<open>\<gamma> \<in> LS M1 qTarget\<close> language_prefix by metis

      show "\<gamma>' \<in> list.set ttc" proof (cases \<gamma>' rule: rev_cases)
        case Nil
        then show ?thesis unfolding ttc by auto
      next
        case (snoc ioI ioL)
        then obtain xL yL where "\<gamma>' = ioI@[(xL,yL)]"
          using prod.exhaust by metis
        then have "xL \<in> inputs M1" and "yL \<in> outputs M1"
          using language_io[OF \<open>\<gamma>' \<in> LS M1 qTarget\<close>, of xL yL]
          by auto
        moreover have "length \<gamma>' \<le> m - size_r M1"
          using \<open>length (\<gamma>@[(x,y)]) \<le> m - size_r M1\<close> \<open>\<gamma> = \<gamma>'@\<gamma>''\<close> by auto
        moreover have "ioI \<in> LS M1 qTarget"
          using \<open>\<gamma>' \<in> LS M1 qTarget\<close> \<open>\<gamma>' = ioI@[(xL,yL)]\<close> language_prefix by metis
        ultimately have "\<gamma>' \<in> list.set (traces_to_check M1 qTarget k)"
          unfolding traces_to_check_set[OF assms(1) \<open>qTarget \<in> states M1\<close>] k \<open>\<gamma>' = ioI@[(xL,yL)]\<close>
          by blast
        then show ?thesis 
          unfolding ttc by auto
      qed
    qed



    show "L M1 \<inter> ((V ` reachable_states M1) \<union> {\<omega>@\<omega>' | \<omega> \<omega>' . \<omega> \<in> {((V (t_source t)) @ [(t_input t,t_output t)]), (V (t_target t))} \<and> \<omega>' \<in> list.set (prefixes (\<gamma>@[(x,y)]))}) = L M2 \<inter>  ((V ` reachable_states M1) \<union> {\<omega>@\<omega>' | \<omega> \<omega>' . \<omega> \<in> {((V (t_source t)) @ [(t_input t,t_output t)]), (V (t_target t))} \<and> \<omega>' \<in> list.set (prefixes (\<gamma>@[(x,y)]))})"
    proof -
      have "L M1 \<inter> (V ` reachable_states M1) = L M2 \<inter> (V ` reachable_states M1)"
        using assms(11) \<open>L M1 \<inter> set T = L M2 \<inter> set T\<close>
        by blast
      moreover have "L M1 \<inter> {\<omega>@\<omega>' | \<omega> \<omega>' . \<omega> \<in> {((V (t_source t)) @ [(t_input t,t_output t)]), (V (t_target t))} \<and> \<omega>' \<in> list.set (prefixes (\<gamma>@[(x,y)]))} = L M2 \<inter> {\<omega>@\<omega>' | \<omega> \<omega>' . \<omega> \<in> {((V (t_source t)) @ [(t_input t,t_output t)]), (V (t_target t))} \<and> \<omega>' \<in> list.set (prefixes (\<gamma>@[(x,y)]))}"
      proof -
        have *:"{\<omega>@\<omega>' | \<omega> \<omega>' . \<omega> \<in> {\<alpha>@[xy],\<beta>} \<and> \<omega>' \<in> list.set (prefixes (\<gamma>@[(x,y)]))}
                = {\<omega>@\<omega>' | \<omega> \<omega>' . \<omega> \<in> {\<alpha>@[xy],\<beta>} \<and> \<omega>' \<in> list.set (prefixes \<gamma>)} \<union> {(\<alpha>@[xy])@(\<gamma>@[(x,y)]),\<beta>@(\<gamma>@[(x,y)])}"
          unfolding prefixes_set_Cons_insert by blast
        have "L M1 \<inter> {\<omega>@\<omega>' | \<omega> \<omega>' . \<omega> \<in> {\<alpha>@[xy],\<beta>} \<and> \<omega>' \<in> list.set (prefixes \<gamma>)} = L M2 \<inter> {\<omega>@\<omega>' | \<omega> \<omega>' . \<omega> \<in> {\<alpha>@[xy],\<beta>} \<and> \<omega>' \<in> list.set (prefixes \<gamma>)}"
        proof -
          have "\<And> io . io \<in> {\<omega>@\<omega>' | \<omega> \<omega>' . \<omega> \<in> {\<alpha>@[xy],\<beta>} \<and> \<omega>' \<in> list.set (prefixes \<gamma>)} \<Longrightarrow> (io \<in> L M1) = (io \<in> L M2)"
          proof -
            fix io assume "io \<in> {\<omega>@\<omega>' | \<omega> \<omega>' . \<omega> \<in> {\<alpha>@[xy],\<beta>} \<and> \<omega>' \<in> list.set (prefixes \<gamma>)}"
            then obtain \<gamma>' where "io \<in> {\<alpha>@[xy]@\<gamma>',\<beta>@\<gamma>'}" and "\<gamma>' \<in> list.set (prefixes \<gamma>)"
              by force
            then have "\<gamma>' \<in> list.set ttc" and "\<gamma>' \<in> LS M1 qTarget"
              using \<open>\<And> \<gamma>' . \<gamma>' \<in> list.set (prefixes \<gamma>) \<Longrightarrow> \<gamma>' \<in> list.set ttc \<and> \<gamma>' \<in> LS M1 qTarget\<close>
              by blast+
            moreover have "[] \<in> Prefix_Tree.set (dist_fun (length \<gamma>') (FSM.after M1 qTarget \<gamma>'))"
              by simp
            ultimately have "L M1 \<inter> {\<alpha>@[xy]@\<gamma>',\<beta>@\<gamma>'} = L M2 \<inter> {\<alpha>@[xy]@\<gamma>',\<beta>@\<gamma>'}"
              using handleTrace_foldl_props_1[of \<gamma>' "[]"]
              by auto 
            then show "(io \<in> L M1) = (io \<in> L M2)"
              using \<open>io \<in> {\<alpha>@[xy]@\<gamma>',\<beta>@\<gamma>'}\<close> by blast
          qed
          then show ?thesis by blast
        qed
        moreover have "L M1 \<inter> {(\<alpha>@[xy])@(\<gamma>@[(x,y)]),\<beta>@(\<gamma>@[(x,y)])} = L M2 \<inter> {(\<alpha>@[xy])@(\<gamma>@[(x,y)]),\<beta>@(\<gamma>@[(x,y)])}"
        proof (cases "(\<gamma>@[(x,y)]) \<in> LS M1 qTarget")
          case True
          show ?thesis 
            using handleTrace_foldl_props_1[OF \<open>(\<gamma>@[(x,y)]) \<in> list.set ttc\<close> True, of "[]"] 
            by auto
        next
          case False
          show ?thesis 
            using handleTrace_foldl_props_2[OF \<open>(\<gamma>@[(x,y)]) \<in> list.set ttc\<close> False] 
            by auto
        qed
        ultimately show ?thesis 
          unfolding \<alpha>[symmetric] xy[symmetric] \<beta>[symmetric] *
          by (metis (no_types, lifting) Int_Un_distrib) 
      qed
      ultimately show ?thesis 
        by (metis (no_types, lifting) Int_Un_distrib) 
    qed
          
    show "preserves_divergence M1 M2 ((V ` reachable_states M1) \<union> {\<omega>@\<omega>' | \<omega> \<omega>' . \<omega> \<in> {((V (t_source t)) @ [(t_input t,t_output t)]), (V (t_target t))} \<and> \<omega>' \<in> list.set (prefixes (\<gamma>@[(x,y)]))})"
    proof -

      have "\<And> u v . u \<in> L M1 \<inter> (V ` reachable_states M1 \<union> {\<omega> @ \<omega>' |\<omega> \<omega>'. \<omega> \<in> {\<alpha> @ [xy], \<beta>} \<and> \<omega>' \<in> list.set (prefixes (\<gamma> @ [(x, y)]))}) \<Longrightarrow>
                     v \<in> L M1 \<inter> (V ` reachable_states M1 \<union> {\<omega> @ \<omega>' |\<omega> \<omega>'. \<omega> \<in> {\<alpha> @ [xy], \<beta>} \<and> \<omega>' \<in> list.set (prefixes (\<gamma> @ [(x, y)]))}) \<Longrightarrow>
                     \<not> converge M1 u v \<Longrightarrow> 
                     \<not> converge M2 u v"
      proof -
        fix u v assume "u \<in> L M1 \<inter> (V ` reachable_states M1 \<union> {\<omega> @ \<omega>' |\<omega> \<omega>'. \<omega> \<in> {\<alpha> @ [xy], \<beta>} \<and> \<omega>' \<in> list.set (prefixes (\<gamma> @ [(x, y)]))})"
                   and "v \<in> L M1 \<inter> (V ` reachable_states M1 \<union> {\<omega> @ \<omega>' |\<omega> \<omega>'. \<omega> \<in> {\<alpha> @ [xy], \<beta>} \<and> \<omega>' \<in> list.set (prefixes (\<gamma> @ [(x, y)]))})"
                   and "\<not> converge M1 u v"

        then have "u \<in> L M1" and "v \<in> L M1" and "after_initial M1 u \<noteq> after_initial M1 v" 
          by auto
        then have "after_initial M1 u \<in> states M1"
              and "after_initial M1 v \<in> states M1"
          using after_is_state[OF assms(1)] by auto

        have pass_dist: "\<And> u . u \<in> L M1 \<inter> (V ` reachable_states M1 \<union> {\<omega> @ \<omega>' |\<omega> \<omega>'. \<omega> \<in> {\<alpha> @ [xy], \<beta>} \<and> \<omega>' \<in> list.set (prefixes (\<gamma> @ [(x, y)]))}) \<Longrightarrow>
                     (\<exists> k . \<forall> w \<in> Prefix_Tree.set (dist_fun k (after_initial M1 u)) . (u@w \<in> L M1) = (u@w \<in> L M2))"
        proof -
          fix u assume "u \<in> L M1 \<inter> (V ` reachable_states M1 \<union> {\<omega> @ \<omega>' |\<omega> \<omega>'. \<omega> \<in> {\<alpha> @ [xy], \<beta>} \<and> \<omega>' \<in> list.set (prefixes (\<gamma> @ [(x, y)]))})"
          then consider "u \<in> V ` reachable_states M1" | "u \<in> {\<omega> @ \<omega>' |\<omega> \<omega>'. \<omega> \<in> {\<alpha> @ [xy], \<beta>} \<and> \<omega>' \<in> list.set (prefixes (\<gamma> @ [(x, y)]))}"
            by blast
          then show "(\<exists> k . \<forall> w \<in> Prefix_Tree.set (dist_fun k (after_initial M1 u)) . (u@w \<in> L M1) = (u@w \<in> L M2))"
          proof cases
            case 1
            then obtain qU where "qU \<in> reachable_states M1" and "V qU = u"
              by blast
            have "after_initial M1 u = qU"
              by (metis \<open>V qU = u\<close> \<open>qU \<in> reachable_states M1\<close> assms(1) assms(9) is_state_cover_assignment_observable_after) 

            have "\<And>w . w \<in> Prefix_Tree.set (dist_fun 0 (after_initial M1 u)) \<Longrightarrow> (u@w \<in> L M1) = (u@w \<in> L M2)"
            proof -
              fix w assume "w \<in> Prefix_Tree.set (dist_fun 0 (after_initial M1 u))"
              then have "w \<in> Prefix_Tree.set (Prefix_Tree.after T u)"
                using assms(16)[OF \<open>qU \<in> reachable_states M1\<close>] 
                unfolding \<open>V qU = u\<close> \<open>after_initial M1 u = qU\<close>
                by blast
              moreover have "u \<in> set T"
                using "1" assms(11) by auto
              ultimately have "u@w \<in> set T" 
                unfolding after_set
                by auto 
              then show "(u@w \<in> L M1) = (u@w \<in> L M2)"
                using \<open>L M1 \<inter> set T = L M2 \<inter> set T\<close> by blast
            qed
            then show ?thesis
              by blast
          next 
            case 2
            then obtain \<gamma>' where "u \<in> {(\<alpha> @ [xy]) @ \<gamma>', \<beta> @ \<gamma>'}" and "\<gamma>' \<in> list.set (prefixes (\<gamma> @ [(x, y)]))"
              by blast
            then have "\<gamma>' \<in> list.set ttc"
              using \<open>(\<gamma> @ [(x, y)]) \<in> list.set ttc\<close> \<open>\<And> \<gamma>' . \<gamma>' \<in> list.set (prefixes \<gamma>) \<Longrightarrow> \<gamma>' \<in> list.set ttc \<and> \<gamma>' \<in> LS M1 qTarget\<close>
              unfolding prefixes_set_Cons_insert by blast
            
            have "\<gamma>' \<in> LS M1 qTarget"
            proof -
              have "u \<in> L M1"
                using \<open>u \<in> L M1 \<inter> (V ` reachable_states M1 \<union> {\<omega> @ \<omega>' |\<omega> \<omega>'. \<omega> \<in> {\<alpha> @ [xy], \<beta>} \<and> \<omega>' \<in> list.set (prefixes (\<gamma> @ [(x, y)]))})\<close> by blast
              then show ?thesis
                using \<open>u \<in> {(\<alpha> @ [xy]) @ \<gamma>', \<beta> @ \<gamma>'}\<close> \<open>converge M1 (\<alpha> @ [xy]) \<beta>\<close> 
                unfolding qTarget \<beta>[symmetric]
                by (metis \<open>\<beta> \<in> L M1\<close> assms(1) converge_append_language_iff insert_iff observable_after_language_none singleton_iff) 
            qed

            then have "(FSM.after M1 qTarget \<gamma>') = (after_initial M1 u)"
              using \<open>u \<in> {(\<alpha> @ [xy]) @ \<gamma>', \<beta> @ \<gamma>'}\<close> \<open>converge M1 (\<alpha> @ [xy]) \<beta>\<close> 
              unfolding qTarget \<beta>[symmetric]
              by (metis \<open>\<alpha> @ [xy] \<in> L M1\<close> \<open>\<beta> \<in> L M1\<close> after_split assms(1) assms(3) convergence_minimal insert_iff observable_after_language_append singleton_iff)
            have "\<And> w . {\<alpha> @ [xy] @ \<gamma>' @ w, \<beta> @ \<gamma>' @ w} = {((\<alpha> @ [xy]) @ \<gamma>') @ w, (\<beta> @ \<gamma>') @ w}"
              by auto

            have "\<And> w . w \<in> set (dist_fun (Suc (length \<gamma>')) (after_initial M1 u)) \<Longrightarrow> (u @ w \<in> L M1) = (u @ w \<in> L M2)"
              using handleTrace_foldl_props_1[OF \<open>\<gamma>' \<in> list.set ttc\<close> \<open>\<gamma>' \<in> LS M1 qTarget\<close>] 
              unfolding \<open>(FSM.after M1 qTarget \<gamma>') = (after_initial M1 u)\<close>
              using \<open>u \<in> {(\<alpha> @ [xy]) @ \<gamma>', \<beta> @ \<gamma>'}\<close> 
              unfolding \<open>\<And> w . {\<alpha> @ [xy] @ \<gamma>' @ w, \<beta> @ \<gamma>' @ w} = {((\<alpha> @ [xy]) @ \<gamma>') @ w, (\<beta> @ \<gamma>') @ w}\<close> by blast

            then show ?thesis
              by blast
          qed
        qed

        obtain ku where "\<And> w . w \<in> set (dist_fun ku (after_initial M1 u)) \<Longrightarrow> (u@w \<in> L M1) = (u@w \<in> L M2)"
          using pass_dist[OF \<open>u \<in> L M1 \<inter> (V ` reachable_states M1 \<union> {\<omega> @ \<omega>' |\<omega> \<omega>'. \<omega> \<in> {\<alpha> @ [xy], \<beta>} \<and> \<omega>' \<in> list.set (prefixes (\<gamma> @ [(x, y)]))})\<close>]
          by blast

        obtain kv where "\<And> w . w \<in> set (dist_fun kv (after_initial M1 v)) \<Longrightarrow> (v@w \<in> L M1) = (v@w \<in> L M2)"
          using pass_dist[OF \<open>v \<in> L M1 \<inter> (V ` reachable_states M1 \<union> {\<omega> @ \<omega>' |\<omega> \<omega>'. \<omega> \<in> {\<alpha> @ [xy], \<beta>} \<and> \<omega>' \<in> list.set (prefixes (\<gamma> @ [(x, y)]))})\<close>]
          by blast

        obtain w where "w \<in> set (dist_fun ku (after_initial M1 u))" 
                   and "w \<in> set (dist_fun kv (after_initial M1 v))"
                   and "distinguishes M1 (after_initial M1 u) (after_initial M1 v) w"
          using assms(15)[OF \<open>after_initial M1 u \<in> states M1\<close> \<open>after_initial M1 v \<in> states M1\<close> \<open>after_initial M1 u \<noteq> after_initial M1 v\<close>]
          by blast

        then have "(w \<in> LS M1 (after_initial M1 u)) \<noteq> (w \<in> LS M1 (after_initial M1 v))"
          unfolding distinguishes_def by blast
        moreover have "w \<in> LS M1 (after_initial M1 u) = (w \<in> LS M2 (after_initial M2 u))"
          by (metis \<open>\<And>w. w \<in> Prefix_Tree.set (dist_fun ku (after_initial M1 u)) \<Longrightarrow> (u @ w \<in> L M1) = (u @ w \<in> L M2)\<close> \<open>u \<in> L M1\<close> \<open>w \<in> Prefix_Tree.set (dist_fun ku (after_initial M1 u))\<close> append_Nil2 assms(1) assms(2) observable_after_language_append observable_after_language_none set_Nil)
        moreover have "w \<in> LS M1 (after_initial M1 v) = (w \<in> LS M2 (after_initial M2 v))"
          by (metis \<open>\<And>w. w \<in> Prefix_Tree.set (dist_fun kv (after_initial M1 v)) \<Longrightarrow> (v @ w \<in> L M1) = (v @ w \<in> L M2)\<close> \<open>v \<in> L M1\<close> \<open>w \<in> Prefix_Tree.set (dist_fun kv (after_initial M1 v))\<close> append_Nil2 assms(1) assms(2) observable_after_language_append observable_after_language_none set_Nil)
        ultimately have "(w \<in> LS M2 (after_initial M2 u)) \<noteq> (w \<in> LS M2 (after_initial M2 v))" 
          by blast
        then have "after_initial M2 u \<noteq> after_initial M2 v"
          by auto
        then show "\<not> converge M2 u v"
          using assms(2) assms(4) converge.simps convergence_minimal by blast 
      qed
  
      then show ?thesis
        unfolding preserves_divergence.simps \<alpha>[symmetric] xy[symmetric] \<beta>[symmetric]
        by blast
    qed
  qed
  then show "?P1a"
    by blast
qed




lemma establish_convergence_static_establishes_convergence :
  assumes "observable M1"
      and "observable M2"
      and "minimal M1"
      and "minimal M2"
      and "size_r M1 \<le> m"
      and "size M2 \<le> m"
      and "inputs M2 = inputs M1"
      and "outputs M2 = outputs M1"
      and "t \<in> transitions M1"
      and "t_source t \<in> reachable_states M1"
      and "is_state_cover_assignment M1 V"
      and "V (t_source t) @ [(t_input t, t_output t)] \<in> L M2"
      and "V ` reachable_states M1 \<subseteq> set T"
      and "preserves_divergence M1 M2 (V ` reachable_states M1)"
      and "convergence_graph_lookup_invar M1 M2 cg_lookup G"
      and "convergence_graph_insert_invar M1 M2 cg_lookup cg_insert"
      and "\<And> q1 q2 . q1 \<in> states M1 \<Longrightarrow> q2 \<in> states M1 \<Longrightarrow> q1 \<noteq> q2 \<Longrightarrow> \<exists> io . \<forall> k1 k2 . io \<in> set (dist_fun k1 q1) \<inter> set (dist_fun k2 q2) \<and> distinguishes M1 q1 q2 io"
      and "\<And> q . q \<in> reachable_states M1 \<Longrightarrow> set (dist_fun 0 q) \<subseteq> set (after T (V q))"
      and "\<And> q k . q \<in> states M1 \<Longrightarrow> finite_tree (dist_fun k q)"
      and "L M1 \<inter> set (fst (establish_convergence_static dist_fun M1 V T G cg_insert cg_lookup m t)) = L M2 \<inter> set (fst (establish_convergence_static dist_fun M1 V T G cg_insert cg_lookup m t))"
shows "converge M2 (V (t_source t) @ [(t_input t, t_output t)]) (V (t_target t))"
(is "converge M2 ?u ?v")
proof -

   have prop1: "\<And>\<gamma> x y.
     length (\<gamma> @ [(x, y)]) \<le> (m - size_r M1) \<Longrightarrow>
     \<gamma> \<in> LS M1 (after_initial M1 ?u) \<Longrightarrow>
     x \<in> FSM.inputs M1 \<Longrightarrow>
     y \<in> FSM.outputs M1 \<Longrightarrow>
     L M1 \<inter> (V ` reachable_states M1 \<union> {\<omega> @ \<omega>' |\<omega> \<omega>'. \<omega> \<in> {?u, ?v} \<and> \<omega>' \<in> list.set (prefixes (\<gamma> @ [(x, y)]))}) =
     L M2 \<inter> (V ` reachable_states M1 \<union> {\<omega> @ \<omega>' |\<omega> \<omega>'. \<omega> \<in> {?u, ?v} \<and> \<omega>' \<in> list.set (prefixes (\<gamma> @ [(x, y)]))}) \<and>
     preserves_divergence M1 M2
      (V ` reachable_states M1 \<union> {\<omega> @ \<omega>' |\<omega> \<omega>'. \<omega> \<in> {?u, ?v} \<and> \<omega>' \<in> list.set (prefixes (\<gamma> @ [(x, y)]))})"
  and prop2: "preserves_divergence M1 M2 (V ` reachable_states M1 \<union> {?u, ?v})"
     using establish_convergence_static_properties(1,2)[OF assms(1-4,7-20)]
     by presburger+

  have "L M1 \<inter> V ` reachable_states M1 = L M2 \<inter> V ` reachable_states M1" 
    using assms(13,20) 
    using establish_convergence_static_subset[of T dist_fun M1 V G cg_insert cg_lookup m t ]
    by blast
  then have "V (t_target t) \<in> L M2"
    by (metis Int_iff assms(10) assms(11) assms(9) imageI is_state_cover_assignment_language reachable_states_next)
    
  have "converge M1 ?u ?v"
    using state_cover_transition_converges[OF assms(1,11,9,10)] .

  show ?thesis
    using establish_convergence_from_pass[OF assms(1-8,11) \<open>L M1 \<inter> V ` reachable_states M1 = L M2 \<inter> V ` reachable_states M1\<close> \<open>converge M1 ?u ?v\<close> \<open>V (t_source t) @ [(t_input t, t_output t)] \<in> L M2\<close> \<open>V (t_target t) \<in> L M2\<close> prop1 prop2]
    by blast
qed

 


lemma establish_convergence_static_verifies_transition :
  assumes "\<And> q1 q2 . q1 \<in> states M1 \<Longrightarrow> q2 \<in> states M1 \<Longrightarrow> q1 \<noteq> q2 \<Longrightarrow> \<exists> io . \<forall> k1 k2 . io \<in> set (dist_fun k1 q1) \<inter> set (dist_fun k2 q2) \<and> distinguishes M1 q1 q2 io"
      and "\<And> q k . q \<in> states M1 \<Longrightarrow> finite_tree (dist_fun k q)"
shows "verifies_transition (establish_convergence_static dist_fun) M1 M2 V (fst (handle_state_cover_static dist_fun M1 V cg_initial cg_insert cg_lookup)) cg_insert cg_lookup"
proof -
  have *:"\<And> V T (G::'d) m t. set T \<subseteq> set (fst ((establish_convergence_static dist_fun) M1 V T G cg_insert cg_lookup m t))"
    using establish_convergence_static_subset 
    by metis 

  have ***:"\<And> V T (G::'d) m t. finite_tree T \<longrightarrow> finite_tree (fst ((establish_convergence_static dist_fun) M1 V T G cg_insert cg_lookup m t))"
    using establish_convergence_static_finite 
    by metis 

  let ?distinguish_traces = "(\<lambda> \<alpha> t' q' \<beta> t'' g'' . dist_fun 0 q')"

  have **:"\<And> T (G::'d) m t.
        observable M1 \<Longrightarrow>
        observable M2 \<Longrightarrow>
        minimal M1 \<Longrightarrow>
        minimal M2 \<Longrightarrow>
        size_r M1 \<le> m \<Longrightarrow>
        FSM.size M2 \<le> m \<Longrightarrow>
        FSM.inputs M2 = FSM.inputs M1 \<Longrightarrow>
        FSM.outputs M2 = FSM.outputs M1 \<Longrightarrow>
        is_state_cover_assignment M1 V \<Longrightarrow>
        preserves_divergence M1 M2 (V ` reachable_states M1) \<Longrightarrow>
        V ` reachable_states M1 \<subseteq> set T \<Longrightarrow>
        t \<in> FSM.transitions M1 \<Longrightarrow>
        t_source t \<in> reachable_states M1 \<Longrightarrow>
        V (t_source t) @ [(t_input t, t_output t)] \<in> L M2 \<Longrightarrow>
        convergence_graph_lookup_invar M1 M2 cg_lookup G \<Longrightarrow>
        convergence_graph_insert_invar M1 M2 cg_lookup cg_insert \<Longrightarrow>
        set (fst (handle_state_cover_static dist_fun M1 V cg_initial cg_insert cg_lookup)) \<subseteq> set T \<Longrightarrow>
        L M1 \<inter> Prefix_Tree.set (fst ((establish_convergence_static dist_fun) M1 V T G cg_insert cg_lookup m t)) =
        L M2 \<inter> Prefix_Tree.set (fst ((establish_convergence_static dist_fun) M1 V T G cg_insert cg_lookup m t)) \<Longrightarrow>
        converge M2 (V (t_source t) @ [(t_input t, t_output t)]) (V (t_target t)) \<and>
        convergence_graph_lookup_invar M1 M2 cg_lookup (snd ((establish_convergence_static dist_fun) M1 V T G cg_insert cg_lookup m t))"
  proof 
    fix G :: 'd
    fix T m t
    assume a01: "observable M1"
    assume a02: "observable M2"
    assume a03: "minimal M1"
    assume a04: "minimal M2"
    assume a05: "size_r M1 \<le> m"
    assume a06: "FSM.size M2 \<le> m"
    assume a07: "FSM.inputs M2 = FSM.inputs M1"
    assume a08: "FSM.outputs M2 = FSM.outputs M1"
    assume a09: "is_state_cover_assignment M1 V"
    assume a10: "preserves_divergence M1 M2 (V ` reachable_states M1)"
    assume a11: "V ` reachable_states M1 \<subseteq> set T"
    assume a12: "t \<in> FSM.transitions M1"
    assume a13: "t_source t \<in> reachable_states M1"
    assume a14: "V (t_source t) @ [(t_input t, t_output t)] \<in> L M2"
    assume a15: "convergence_graph_lookup_invar M1 M2 cg_lookup G"
    assume a16: "convergence_graph_insert_invar M1 M2 cg_lookup cg_insert"
    assume a17: "L M1 \<inter> Prefix_Tree.set (fst ((establish_convergence_static dist_fun) M1 V T G cg_insert cg_lookup m t)) = L M2 \<inter> Prefix_Tree.set (fst ((establish_convergence_static dist_fun) M1 V T G cg_insert cg_lookup m t))"
    assume a18: "set (fst (handle_state_cover_static dist_fun M1 V cg_initial cg_insert cg_lookup)) \<subseteq> set T"

    have "L M1 \<inter> V ` reachable_states M1 = L M2 \<inter> V ` reachable_states M1"
      using a11 a17 *
      by blast
    then have d2: "V (t_target t) \<in> L M2"
      using a11 is_state_cover_assignment_language[OF a09, of "t_target t"] reachable_states_next[OF a13 a12]
      by blast

    have d1: "\<And> q . q \<in> reachable_states M1 \<Longrightarrow> set (dist_fun 0 q) \<subseteq> set (after T (V q))" 
      using handle_state_cover_static_applies_dist_sets[of _ M1 dist_fun V cg_initial cg_insert cg_lookup] a18
      by (meson in_mono subsetI subset_after_subset) 

    show "converge M2 (V (t_source t) @ [(t_input t, t_output t)]) (V (t_target t))"
      using establish_convergence_static_establishes_convergence[where dist_fun=dist_fun, OF a01 a02 a03 a04 a05 a06 a07 a08 a12 a13 a09 a14 a11 a10 a15 a16 assms(1) d1 assms(2) a17]
      by force

    show "convergence_graph_lookup_invar M1 M2 cg_lookup (snd (establish_convergence_static dist_fun M1 V T G cg_insert cg_lookup m t))"
      using establish_convergence_static_properties(3)[where dist_fun=dist_fun, OF a01 a02 a03 a04 a07 a08 a12 a13 a09 a14 a11 a10 a15 a16 assms(1) d1 assms(2) a17]
      by blast
  qed

  show ?thesis
    unfolding verifies_transition_def
    using * *** ** 
    by presburger
qed



definition handleUT_static :: "(nat \<Rightarrow> 'a \<Rightarrow> ('b\<times>'c) prefix_tree) \<Rightarrow>
                                     (('a::linorder,'b::linorder,'c::linorder) fsm \<Rightarrow>
                                     ('a,'b,'c) state_cover_assignment \<Rightarrow>
                                     ('b\<times>'c) prefix_tree \<Rightarrow> 
                                     'd \<Rightarrow>
                                     ('d \<Rightarrow> ('b\<times>'c) list \<Rightarrow> 'd) \<Rightarrow>
                                     ('d \<Rightarrow> ('b\<times>'c) list \<Rightarrow> ('b\<times>'c) list list) \<Rightarrow>
                                     ('d \<Rightarrow> ('b\<times>'c) list \<Rightarrow> ('b\<times>'c) list \<Rightarrow> 'd) \<Rightarrow> 
                                     nat \<Rightarrow>
                                     ('a,'b,'c) transition \<Rightarrow> 
                                     ('a,'b,'c) transition list \<Rightarrow>   
                                     (('a,'b,'c) transition list \<times> ('b\<times>'c) prefix_tree \<times> 'd))"
  where 
  "handleUT_static dist_fun M V T G cg_insert cg_lookup cg_merge l t X = (let
      (T1,G1) = handle_io_pair False False M V T G cg_insert cg_lookup (t_source t) (t_input t) (t_output t);
      (T2,G2) = establish_convergence_static dist_fun M V T1 G1 cg_insert cg_lookup l t;
      G3      = cg_merge G2 ((V (t_source t))@[(t_input t, t_output t)]) (V (t_target t))
    in (X,T2,G3))"


lemma handleUT_static_handles_transition :
  fixes M1::"('a::linorder,'b::linorder,'c::linorder) fsm"
  fixes M2::"('e,'b,'c) fsm"
  assumes "\<And> q1 q2 . q1 \<in> states M1 \<Longrightarrow> q2 \<in> states M1 \<Longrightarrow> q1 \<noteq> q2 \<Longrightarrow> \<exists> io . \<forall> k1 k2 . io \<in> set (dist_fun k1 q1) \<inter> set (dist_fun k2 q2) \<and> distinguishes M1 q1 q2 io"
      and "\<And> q k . q \<in> states M1 \<Longrightarrow> finite_tree (dist_fun k q)"
    shows "handles_transition (handleUT_static dist_fun) M1 M2 V (fst (handle_state_cover_static dist_fun M1 V cg_initial cg_insert cg_lookup)) cg_insert cg_lookup cg_merge"
proof -

  let ?T0 = "(fst (handle_state_cover_static dist_fun M1 V cg_initial cg_insert cg_lookup))"

  have "\<And> T G m t X . 
       Prefix_Tree.set T \<subseteq> Prefix_Tree.set (fst (snd (handleUT_static dist_fun M1 V T G cg_insert cg_lookup cg_merge m t X))) \<and>
       (finite_tree T \<longrightarrow> finite_tree (fst (snd (handleUT_static dist_fun M1 V T G cg_insert cg_lookup cg_merge m t X)))) \<and>
       (observable M1 \<longrightarrow>
        observable M2 \<longrightarrow>
        minimal M1 \<longrightarrow>
        minimal M2 \<longrightarrow>
        size_r M1 \<le> m \<longrightarrow>
        FSM.size M2 \<le> m \<longrightarrow>
        FSM.inputs M2 = FSM.inputs M1 \<longrightarrow>
        FSM.outputs M2 = FSM.outputs M1 \<longrightarrow>
        is_state_cover_assignment M1 V \<longrightarrow>
        preserves_divergence M1 M2 (V ` reachable_states M1) \<longrightarrow>
        V ` reachable_states M1 \<subseteq> Prefix_Tree.set T \<longrightarrow>
        t \<in> FSM.transitions M1 \<longrightarrow>
        t_source t \<in> reachable_states M1 \<longrightarrow>
        V (t_source t) @ [(t_input t, t_output t)] \<noteq> V (t_target t) \<longrightarrow>
        convergence_graph_lookup_invar M1 M2 cg_lookup G \<longrightarrow>
        convergence_graph_insert_invar M1 M2 cg_lookup cg_insert \<longrightarrow>
        convergence_graph_merge_invar M1 M2 cg_lookup cg_merge \<longrightarrow>
        L M1 \<inter> Prefix_Tree.set (fst (snd (handleUT_static dist_fun M1 V T G cg_insert cg_lookup cg_merge m t X))) =
        L M2 \<inter> Prefix_Tree.set (fst (snd (handleUT_static dist_fun M1 V T G cg_insert cg_lookup cg_merge m t X))) \<longrightarrow>
        Prefix_Tree.set ?T0 \<subseteq> Prefix_Tree.set T \<longrightarrow>
        (\<forall>\<gamma>. length \<gamma> \<le> m - size_r M1 \<and> list.set \<gamma> \<subseteq> FSM.inputs M1 \<times> FSM.outputs M1 \<and> butlast \<gamma> \<in> LS M1 (t_target t) \<longrightarrow>
             L M1 \<inter> (V ` reachable_states M1 \<union> {(V (t_source t) @ [(t_input t, t_output t)]) @ \<omega>' |\<omega>'. \<omega>' \<in> list.set (prefixes \<gamma>)}) =
             L M2 \<inter> (V ` reachable_states M1 \<union> {(V (t_source t) @ [(t_input t, t_output t)]) @ \<omega>' |\<omega>'. \<omega>' \<in> list.set (prefixes \<gamma>)}) \<and>
             preserves_divergence M1 M2 (V ` reachable_states M1 \<union> {(V (t_source t) @ [(t_input t, t_output t)]) @ \<omega>' |\<omega>'. \<omega>' \<in> list.set (prefixes \<gamma>)})) \<and>
        convergence_graph_lookup_invar M1 M2 cg_lookup (snd (snd (handleUT_static dist_fun M1 V T G cg_insert cg_lookup cg_merge m t X))))"
    (is "\<And> T G m t X . ?P T G m t X")
  proof -

    fix T :: "('b\<times>'c) prefix_tree"
    fix G :: 'd
    fix m :: nat
    fix t :: "('a,'b,'c) transition"
    fix X :: "('a,'b,'c) transition list"
  
    let ?TG = "snd (handleUT_static dist_fun M1 V T G cg_insert cg_lookup cg_merge m t X)"

    obtain T1 G1 where "(T1,G1)   = handle_io_pair False False M1 V T G cg_insert cg_lookup (t_source t) (t_input t) (t_output t)"
      using prod.collapse by blast
    then have T1_def: "T1 = fst (handle_io_pair False False M1 V T G cg_insert cg_lookup (t_source t) (t_input t) (t_output t))"
         and  G1_def: "G1 = snd (handle_io_pair False False M1 V T G cg_insert cg_lookup (t_source t) (t_input t) (t_output t))"
      using fst_conv[of T1 G1] snd_conv[of T1 G1] by force+

    obtain T2 G2 where "(T2,G2)   = establish_convergence_static dist_fun M1 V T1 G1 cg_insert cg_lookup m t"
      using prod.collapse by blast
    have T2_def: "T2 = fst (establish_convergence_static dist_fun M1 V T1 G1 cg_insert cg_lookup m t)"
    and  G2_def: "G2 = snd (establish_convergence_static dist_fun M1 V T1 G1 cg_insert cg_lookup m t)"
      unfolding \<open>(T2,G2)   = establish_convergence_static dist_fun M1 V T1 G1 cg_insert cg_lookup m t\<close>[symmetric] by auto
    define u where "u         = ((V (t_source t))@[(t_input t, t_output t)])"
    define v where "v         = (V (t_target t))"

    define G3 where "G3 = cg_merge G2 u v"

    have TG_cases: "?TG = (T2,G3)"
      unfolding handleUT_static_def Let_def
      unfolding \<open>(T1,G1)   = handle_io_pair False False M1 V T G cg_insert cg_lookup (t_source t) (t_input t) (t_output t)\<close>[symmetric] case_prod_conv
      unfolding \<open>(T2,G2)   = establish_convergence_static dist_fun M1 V T1 G1 cg_insert cg_lookup m t\<close>[symmetric] case_prod_conv
      unfolding G3_def u_def v_def 
      by simp


    have "set T1 \<subseteq> set T2"
    and  "finite_tree T1 \<Longrightarrow> finite_tree T2"
      using establish_convergence_static_verifies_transition[OF assms, of M2 V cg_initial cg_insert cg_lookup]
      unfolding T2_def verifies_transition_def by blast+
    moreover have "set T \<subseteq> set T1"
             and  "finite_tree T \<Longrightarrow> finite_tree T1"
      using handle_io_pair_verifies_io_pair[of False False M1 M2 cg_insert cg_lookup]
      unfolding T1_def verifies_io_pair_def 
      by blast+
    ultimately have *:"set T \<subseteq> set (fst ?TG)"
               and **:"finite_tree T \<Longrightarrow> finite_tree (fst ?TG)"
      using TG_cases by auto

    
    have ***: "observable M1 \<Longrightarrow>
              observable M2 \<Longrightarrow>
              minimal M1 \<Longrightarrow>
              minimal M2 \<Longrightarrow>
              size_r M1 \<le> m \<Longrightarrow>
              size M2 \<le> m \<Longrightarrow>
              inputs M2 = inputs M1 \<Longrightarrow>
              outputs M2 = outputs M1 \<Longrightarrow>
              is_state_cover_assignment M1 V \<Longrightarrow>
              preserves_divergence M1 M2 (V ` reachable_states M1) \<Longrightarrow>
              V ` reachable_states M1 \<subseteq> set T \<Longrightarrow>
              t \<in> transitions M1 \<Longrightarrow>
              t_source t \<in> reachable_states M1 \<Longrightarrow> 
              V (t_source t) @ [(t_input t, t_output t)] \<noteq> V (t_target t) \<Longrightarrow>
              convergence_graph_lookup_invar M1 M2 cg_lookup G \<Longrightarrow>
              convergence_graph_insert_invar M1 M2 cg_lookup cg_insert \<Longrightarrow>
              convergence_graph_merge_invar M1 M2 cg_lookup cg_merge \<Longrightarrow>
              L M1 \<inter> set (fst ?TG) = L M2 \<inter> set (fst ?TG) \<Longrightarrow>
              (set ?T0 \<subseteq> set T) \<Longrightarrow>
              (\<forall> \<gamma> . (length \<gamma> \<le> (m-size_r M1) \<and> list.set \<gamma> \<subseteq> inputs M1 \<times> outputs M1 \<and> butlast \<gamma> \<in> LS M1 (t_target t))
                      \<longrightarrow> ((L M1 \<inter> (V ` reachable_states M1 \<union> {((V (t_source t))@[(t_input t,t_output t)]) @ \<omega>' | \<omega>'. \<omega>' \<in> list.set (prefixes \<gamma>)})
                            = L M2 \<inter> (V ` reachable_states M1 \<union> {((V (t_source t))@[(t_input t,t_output t)]) @ \<omega>' | \<omega>'. \<omega>' \<in> list.set (prefixes \<gamma>)}))
                           \<and> preserves_divergence M1 M2 (V ` reachable_states M1 \<union> {((V (t_source t))@[(t_input t,t_output t)]) @ \<omega>' | \<omega>'. \<omega>' \<in> list.set (prefixes \<gamma>)})))   
              \<and> convergence_graph_lookup_invar M1 M2 cg_lookup (snd ?TG)"
    proof -
      assume a01 : "observable M1"
      assume a02 : "observable M2"
      assume a03 : "minimal M1"
      assume a04 : "minimal M2"
      assume a05 : "size_r M1 \<le> m"
      assume a06 : "size M2 \<le> m"
      assume a07 : "inputs M2 = inputs M1"
      assume a08 : "outputs M2 = outputs M1"
      assume a09 : "is_state_cover_assignment M1 V"
      assume a10 : "preserves_divergence M1 M2 (V ` reachable_states M1)"
      assume a11 : "V ` reachable_states M1 \<subseteq> set T"
      assume a12 : "t \<in> transitions M1"
      assume a13 : "t_source t \<in> reachable_states M1"
      assume a14 : "convergence_graph_lookup_invar M1 M2 cg_lookup G"
      assume a15 : "convergence_graph_insert_invar M1 M2 cg_lookup cg_insert"
      assume a16 : "convergence_graph_merge_invar M1 M2 cg_lookup cg_merge"
      assume a17 : "L M1 \<inter> set (fst ?TG) = L M2 \<inter> set (fst ?TG)"
      assume a18 : "(set ?T0 \<subseteq> set T)" 
      assume a19 : "V (t_source t) @ [(t_input t, t_output t)] \<noteq> V (t_target t)"

      have pass_T1 : "L M1 \<inter> set T1 = L M2 \<inter> set T1"
        using a17 \<open>set T1 \<subseteq> set T2\<close> unfolding TG_cases by auto
      then have pass_T : "L M1 \<inter> set T = L M2 \<inter> set T"
        using \<open>set T \<subseteq> set T1\<close> by blast


      have "t_target t \<in> reachable_states M1"
        using reachable_states_next[OF a13 a12] by auto
      then have "(V (t_target t)) \<in> L M1"
        using is_state_cover_assignment_language[OF a09] by blast
      moreover have "(V (t_target t)) \<in> set T"
        using a11 \<open>t_target t \<in> reachable_states M1\<close> by blast
      ultimately have "(V (t_target t)) \<in> L M2"
        using pass_T by blast
      then have "v \<in> L M2"
        unfolding v_def .

      have "(V (t_source t)) \<in> L M1"
        using is_state_cover_assignment_language[OF a09 a13] by blast
      moreover have "(V (t_source t)) \<in> set T"
        using a11 a13 by blast
      ultimately have "(V (t_source t)) \<in> L M2"
        using pass_T by blast
      have "u \<in> L M1" 
        unfolding u_def
        using a01 a09 a12 a13 converge.simps state_cover_transition_converges by blast
      
      have "after_initial M1 u = t_target t"
        using a09 unfolding u_def
        by (metis \<open>u \<in> L M1\<close> a01 a12 a13 after_split after_transition_exhaust is_state_cover_assignment_observable_after u_def)


      have "u \<in> L M2" 
        using distribute_extension_adds_sequence(1)[OF a01 a03 \<open>(V (t_source t)) \<in> L M1\<close> \<open>(V (t_source t)) \<in> L M2\<close> a14 a15, of T "[(t_input t, t_output t)]", of False "(if False then append_heuristic_input M1 else append_heuristic_io)"]
        using pass_T1 append_heuristic_io_in
        unfolding T1_def G1_def handle_io_pair_def u_def
        by (metis (no_types, lifting) Int_iff \<open>u \<in> L M1\<close> a01 a02 converge_append_language_iff u_def) 
      then have "V (t_source t) @ [(t_input t, t_output t)] \<in> L M2"
        unfolding u_def .
      have "L M1 \<inter> V ` reachable_states M1 = L M2 \<inter> V ` reachable_states M1"
        using a11 a17 *
        by blast
      have "V ` reachable_states M1 \<subseteq> set T1"
        using a11 \<open>set T \<subseteq> set T1\<close> by blast
      have "\<And> q . q \<in> reachable_states M1 \<Longrightarrow> set (dist_fun 0 q) \<subseteq> set (after T (V q))" 
        using handle_state_cover_static_applies_dist_sets[of _ M1 dist_fun V cg_initial cg_insert cg_lookup] a18
        by (meson in_mono subsetI subset_after_subset) 
      then have "\<And> q . q \<in> reachable_states M1 \<Longrightarrow> set (dist_fun 0 q) \<subseteq> set (after T1 (V q))" 
        using \<open>set T \<subseteq> set T1\<close>
        by (meson dual_order.trans subset_after_subset) 

      have pass_T2: "L M1 \<inter> Prefix_Tree.set (fst (establish_convergence_static dist_fun M1 V T1 G1 cg_insert cg_lookup m t)) = L M2 \<inter> Prefix_Tree.set (fst (establish_convergence_static dist_fun M1 V T1 G1 cg_insert cg_lookup m t))"
        using a17 unfolding TG_cases T2_def fst_conv .
      have "convergence_graph_lookup_invar M1 M2 cg_lookup G1"
        using handle_io_pair_verifies_io_pair[of False False M1 M2 cg_insert cg_lookup] 
        using a01 a02 a03 a04 a07 a08 a09 \<open>L M1 \<inter> V ` reachable_states M1 = L M2 \<inter> V ` reachable_states M1\<close> pass_T1 a13 fsm_transition_input[OF a12] fsm_transition_output[OF a12] a14 a15
        unfolding T1_def G1_def verifies_io_pair_def
        by blast


      have cons_prop: "\<And>\<gamma> x y.
                           length (\<gamma> @ [(x, y)]) \<le> m-size_r M1 \<Longrightarrow>
                           \<gamma> \<in> LS M1 (after_initial M1 u) \<Longrightarrow>
                           x \<in> FSM.inputs M1 \<Longrightarrow>
                           y \<in> FSM.outputs M1 \<Longrightarrow>
                           L M1 \<inter> (V ` reachable_states M1 \<union> {\<omega> @ \<omega>' |\<omega> \<omega>'. \<omega> \<in> {u, v} \<and> \<omega>' \<in> list.set (prefixes (\<gamma> @ [(x, y)]))}) =
                           L M2 \<inter> (V ` reachable_states M1 \<union> {\<omega> @ \<omega>' |\<omega> \<omega>'. \<omega> \<in> {u, v} \<and> \<omega>' \<in> list.set (prefixes (\<gamma> @ [(x, y)]))}) \<and>
                           preserves_divergence M1 M2 (V ` reachable_states M1 \<union> {\<omega> @ \<omega>' |\<omega> \<omega>'. \<omega> \<in> {u, v} \<and> \<omega>' \<in> list.set (prefixes (\<gamma> @ [(x, y)]))})"
       and nil_prop: "preserves_divergence M1 M2 (V ` reachable_states M1 \<union> {u, v})"  
       and conv_G2: "convergence_graph_lookup_invar M1 M2 cg_lookup G2"
        using establish_convergence_static_properties[OF a01 a02 a03 a04 a07 a08 a12 a13 a09 \<open>V (t_source t) @ [(t_input t, t_output t)] \<in> L M2\<close> \<open>V ` reachable_states M1 \<subseteq> set T1\<close> a10 \<open>convergence_graph_lookup_invar M1 M2 cg_lookup G1\<close> a15 assms(1) \<open>\<And> q . q \<in> reachable_states M1 \<Longrightarrow> set (dist_fun 0 q) \<subseteq> set (after T1(V q))\<close> assms(2) pass_T2]
        unfolding G2_def[symmetric] u_def[symmetric] v_def[symmetric]
        by blast+

      have "converge M2 u v"
        using establish_convergence_static_establishes_convergence[OF a01 a02 a03 a04 a05 a06 a07 a08 a12 a13 a09 \<open>V (t_source t) @ [(t_input t, t_output t)] \<in> L M2\<close> \<open>V ` reachable_states M1 \<subseteq> set T1\<close> a10 \<open>convergence_graph_lookup_invar M1 M2 cg_lookup G1\<close> a15 assms(1) \<open>\<And> q . q \<in> reachable_states M1 \<Longrightarrow> set (dist_fun 0 q) \<subseteq> set (after T1(V q))\<close> assms(2) pass_T2]
        unfolding u_def v_def by blast
      moreover have "converge M1 u v" 
        unfolding u_def v_def using a09 a12 a13
        using a01 state_cover_transition_converges by blast
      ultimately have "convergence_graph_lookup_invar M1 M2 cg_lookup G3"
        using \<open>convergence_graph_lookup_invar M1 M2 cg_lookup G2\<close> a16
        unfolding G3_def
        by (meson convergence_graph_merge_invar_def) 
      then have "convergence_graph_lookup_invar M1 M2 cg_lookup (snd ?TG)"
        unfolding TG_cases by auto

      moreover have "\<And> \<gamma> . (length \<gamma> \<le> (m-size_r M1) \<and> list.set \<gamma> \<subseteq> inputs M1 \<times> outputs M1 \<and> butlast \<gamma> \<in> LS M1 (t_target t))
                    \<Longrightarrow> ((L M1 \<inter> (V ` reachable_states M1 \<union> {((V (t_source t))@[(t_input t,t_output t)]) @ \<omega>' | \<omega>'. \<omega>' \<in> list.set (prefixes \<gamma>)})
                          = L M2 \<inter> (V ` reachable_states M1 \<union> {((V (t_source t))@[(t_input t,t_output t)]) @ \<omega>' | \<omega>'. \<omega>' \<in> list.set (prefixes \<gamma>)}))
                         \<and> preserves_divergence M1 M2 (V ` reachable_states M1 \<union> {((V (t_source t))@[(t_input t,t_output t)]) @ \<omega>' | \<omega>'. \<omega>' \<in> list.set (prefixes \<gamma>)}))"
        (is "\<And> \<gamma> . (length \<gamma> \<le> (m-size_r M1) \<and> list.set \<gamma> \<subseteq> inputs M1 \<times> outputs M1 \<and> butlast \<gamma> \<in> LS M1 (t_target t)) \<Longrightarrow> ?P1 \<gamma> \<and> ?P2 \<gamma>")          
      proof -
        fix \<gamma> assume assm:"(length \<gamma> \<le> (m-size_r M1) \<and> list.set \<gamma> \<subseteq> inputs M1 \<times> outputs M1 \<and> butlast \<gamma> \<in> LS M1 (t_target t))"
        show "?P1 \<gamma> \<and> ?P2 \<gamma>" 
        proof (cases \<gamma> rule: rev_cases)
          case Nil
          have *: "(V ` reachable_states M1 \<union> {((V (t_source t))@[(t_input t,t_output t)]) @ \<omega>' | \<omega>'. \<omega>' \<in> list.set (prefixes \<gamma>)})
                      = (V ` reachable_states M1 \<union> {u})"
            unfolding u_def[symmetric] Nil by auto

          have "?P1 \<gamma>"
            using \<open>L M1 \<inter> V ` reachable_states M1 = L M2 \<inter> V ` reachable_states M1\<close>
                  \<open>u \<in> L M1\<close> \<open>u \<in> L M2\<close>
            unfolding * by blast
          moreover have "?P2 \<gamma>"
            using preserves_divergence_subset[OF nil_prop]
            unfolding * 
            by (metis Un_empty_right Un_insert_right Un_upper1 insertI1 insert_subsetI)
          ultimately show ?thesis
            by simp 
        next
          case (snoc \<gamma>' xy)
          moreover obtain x y where "xy = (x,y)" 
            using prod.exhaust by metis
          ultimately have "\<gamma> = \<gamma>'@[(x,y)]"
            by auto

          have *: "(V ` reachable_states M1 \<union> {u @ \<omega>' |\<omega>'. \<omega>' \<in> list.set (prefixes \<gamma>)}) \<subseteq> (V ` reachable_states M1 \<union> {\<omega> @ \<omega>' |\<omega> \<omega>'. \<omega> \<in> {u, v} \<and> \<omega>' \<in> list.set (prefixes \<gamma>)})"
            by blast

          have "length (\<gamma>' @ [(x, y)]) \<le> m - size_r M1"
            using assm unfolding \<open>\<gamma> = \<gamma>'@[(x,y)]\<close> by auto
          moreover have "\<gamma>' \<in> LS M1 (after_initial M1 u)"
            using assm unfolding \<open>\<gamma> = \<gamma>'@[(x,y)]\<close>
            by (simp add: \<open>after_initial M1 u = t_target t\<close>) 
          moreover have "x \<in> FSM.inputs M1" and "y \<in> FSM.outputs M1"
            using assm unfolding \<open>\<gamma> = \<gamma>'@[(x,y)]\<close> by auto
          ultimately show ?thesis
            using cons_prop[of \<gamma>' x y] preserves_divergence_subset[of M1 M2 "(V ` reachable_states M1 \<union> {\<omega> @ \<omega>' |\<omega> \<omega>'. \<omega> \<in> {u, v} \<and> \<omega>' \<in> list.set (prefixes \<gamma>)})", OF _ *]
            unfolding \<open>\<gamma> = \<gamma>'@[(x,y)]\<close>[symmetric] u_def[symmetric] 
            by blast
        qed 
      qed
      then show ?thesis
        using \<open>convergence_graph_lookup_invar M1 M2 cg_lookup (snd ?TG)\<close>
        by presburger
    qed  
    show "?P T G m t X"
      using * ** ***  by blast
  qed
  then show ?thesis
    unfolding handles_transition_def
    by blast
qed


subsection \<open>Distinguishing Traces\<close>

subsubsection \<open>Symmetry\<close>
text \<open>The following lemmata serve to show that the function to choose distinguishing sequences
      returns the same sequence for reversed pairs, thus ensuring that the HSIs do not contain two
      sequences for the same pair of states.\<close>





lemma select_diverging_ofsm_table_io_sym :
  assumes "observable M"
  and     "q1 \<in> states M"
  and     "q2 \<in> states M"
  and     "ofsm_table M (\<lambda>q . states M)  (Suc k) q1 \<noteq> ofsm_table M (\<lambda>q . states M)  (Suc k) q2"
  assumes "(select_diverging_ofsm_table_io M q1 q2 (Suc k)) = (io,(a,b))"
  shows "(select_diverging_ofsm_table_io M q2 q1 (Suc k)) = (io,(b,a))"
proof -
  define xs where xs: "xs = (List.product (inputs_as_list M) (outputs_as_list M))"

  define f1' where f1': "f1' = (\<lambda>(x, y) \<Rightarrow> (case (h_obs M q1 x y, h_obs M q2 x y) of 
                    (None, None) \<Rightarrow> None | 
                    (None, Some q2') \<Rightarrow> Some ((x, y), None, Some q2') | 
                    (Some q1', None) \<Rightarrow> Some ((x, y), Some q1', None) | 
                    (Some q1', Some q2') \<Rightarrow> (if ofsm_table M (\<lambda>q . states M)  ((Suc k) - 1) q1' \<noteq> ofsm_table M (\<lambda>q . states M)  ((Suc k) - 1) q2' then Some ((x, y), Some q1', Some q2') else None)))"
  define f1 where f1: "f1 = (\<lambda>xs . (hd (List.map_filter f1' xs)))"

  define f2' where f2': "f2' = (\<lambda>(x, y) \<Rightarrow> (case (h_obs M q2 x y, h_obs M q1 x y) of 
                    (None, None) \<Rightarrow> None | 
                    (None, Some q2') \<Rightarrow> Some ((x, y), None, Some q2') | 
                    (Some q1', None) \<Rightarrow> Some ((x, y), Some q1', None) | 
                    (Some q1', Some q2') \<Rightarrow> (if ofsm_table M (\<lambda>q . states M)  ((Suc k) - 1) q1' \<noteq> ofsm_table M (\<lambda>q . states M)  ((Suc k) - 1) q2' then Some ((x, y), Some q1', Some q2') else None)))"
  define f2 where f2: "f2 = (\<lambda>xs . (hd (List.map_filter f2' xs)))"

  obtain x y where "select_diverging_ofsm_table_io M q1 q2 (Suc k) = ((x,y),(h_obs M q1 x y, h_obs M q2 x y))"
    using select_diverging_ofsm_table_io_Some(1)[OF assms(1-4)]
    by meson


  have "\<And> xy io a b . f1' xy = Some (io,(a,b)) \<Longrightarrow> f2' xy = Some (io,(b,a))"
  proof -
    fix xy io a b assume *: "f1' xy = Some (io,(a,b))"
    obtain x y where "xy = (x,y)"
      using prod.exhaust by metis

    show "f2' xy = Some (io,(b,a))"      
    proof (cases "h_obs M q1 x y")
      case None
      show ?thesis proof (cases "h_obs M q2 x y")
        case None
        then show ?thesis using \<open>h_obs M q1 x y = None\<close> * unfolding f1' f2' \<open>xy = (x,y)\<close> by auto
      next
        case (Some q2')
        
        show ?thesis using * unfolding f1' f2'
          unfolding case_prod_conv None Some \<open>xy = (x,y)\<close> by auto
      qed 
    next
      case (Some q1')
      show ?thesis proof (cases "h_obs M q2 x y")
        case None
        show ?thesis using * unfolding f1' f2'
          unfolding case_prod_conv None Some \<open>xy = (x,y)\<close> by auto
      next
        case (Some q2')
        have "ofsm_table M (\<lambda>q . states M)  ((Suc k) - 1) q2' \<noteq> ofsm_table M (\<lambda>q . states M)  ((Suc k) - 1) q1'" 
          using * unfolding f1' case_prod_conv \<open>h_obs M q1 x y = Some q1'\<close> Some \<open>xy = (x,y)\<close> by auto
        then have "f1' (x,y) = Some ((x,y),(h_obs M q1 x y,h_obs M q2 x y))"
          unfolding f1' case_prod_conv \<open>h_obs M q1 x y = Some q1'\<close> Some by auto
        then have "io = (x,y)" and "b = h_obs M q2 x y" and "a = h_obs M q1 x y"
          using * \<open>xy = (x,y)\<close> by auto
          
        show ?thesis unfolding f2'
          unfolding case_prod_conv \<open>h_obs M q1 x y = Some q1'\<close> Some \<open>io = (x,y)\<close> \<open>b = h_obs M q2 x y\<close> \<open>a = h_obs M q1 x y\<close> \<open>xy = (x,y)\<close>
          using \<open>ofsm_table M (\<lambda>q . states M)  ((Suc k) - 1) q2' \<noteq> ofsm_table M (\<lambda>q . states M)  ((Suc k) - 1) q1'\<close> by simp
      qed 
    qed
  qed
  moreover have "\<And> xy io a b . f2' xy = Some (io,(a,b)) \<Longrightarrow> f1' xy = Some (io,(b,a))"
  proof -
    fix xy io a b assume *: "f2' xy = Some (io,(a,b))"
    obtain x y where "xy = (x,y)"
      using prod.exhaust by metis

    show "f1' xy = Some (io,(b,a))"      
    proof (cases "h_obs M q1 x y")
      case None
      show ?thesis proof (cases "h_obs M q2 x y")
        case None
        then show ?thesis using \<open>h_obs M q1 x y = None\<close> * unfolding f1' f2' \<open>xy = (x,y)\<close> by auto
      next
        case (Some q2')
        
        show ?thesis using * unfolding f1' f2'
          unfolding case_prod_conv None Some \<open>xy = (x,y)\<close> by auto
      qed 
    next
      case (Some q1')
      show ?thesis proof (cases "h_obs M q2 x y")
        case None
        show ?thesis using * unfolding f1' f2'
          unfolding case_prod_conv None Some \<open>xy = (x,y)\<close> by auto
      next
        case (Some q2')
        have "ofsm_table M (\<lambda>q . states M)  ((Suc k) - 1) q2' \<noteq> ofsm_table M (\<lambda>q . states M)  ((Suc k) - 1) q1'" 
          using * unfolding f2' case_prod_conv \<open>h_obs M q1 x y = Some q1'\<close> Some \<open>xy = (x,y)\<close> by auto
        then have "f2' (x,y) = Some ((x,y),(h_obs M q2 x y,h_obs M q1 x y))"
          unfolding f2' case_prod_conv \<open>h_obs M q1 x y = Some q1'\<close> Some by auto
        then have "io = (x,y)" and "b = h_obs M q1 x y" and "a = h_obs M q2 x y"
          using * \<open>xy = (x,y)\<close> by auto
          
        show ?thesis unfolding f1'
          unfolding case_prod_conv \<open>h_obs M q1 x y = Some q1'\<close> Some \<open>io = (x,y)\<close> \<open>b = h_obs M q1 x y\<close> \<open>a = h_obs M q2 x y\<close> \<open>xy = (x,y)\<close>
          using \<open>ofsm_table M (\<lambda>q . states M)  ((Suc k) - 1) q2' \<noteq> ofsm_table M (\<lambda>q . states M)  ((Suc k) - 1) q1'\<close> by simp
      qed 
    qed
  qed
  ultimately have "\<And> xy io a b . f2' xy = Some (io,(a,b)) \<longleftrightarrow> f1' xy = Some (io,(b,a))" 
    by blast

  moreover have "\<And> xs . (\<And> xy io a b . f1' xy = Some (io,(a,b)) \<longleftrightarrow> f2' xy = Some (io,(b,a))) \<Longrightarrow> \<exists> xy \<in> list.set xs . f1' xy \<noteq> None \<Longrightarrow> f1 xs = (io,(a,b)) \<Longrightarrow> f2 xs = (io,(b,a))"
  proof -
    fix xs assume "(\<And> xy io a b . f1' xy = Some (io,(a,b)) \<longleftrightarrow> f2' xy = Some (io,(b,a)))" 
                  "\<exists> xy \<in> list.set xs . f1' xy \<noteq> None" 
                  "f1 xs = (io,(a,b))"
    then show "f2 xs = (io,(b,a))"
    proof (induction xs)
      case Nil
      then show ?case by auto
    next
      case (Cons xy xs)
      show ?case proof (cases "f1' xy")
        case None
        then have "\<nexists> io a b . f1' xy = Some (io,(a,b))"
          by auto
        then have "f2' xy = None"
          using Cons.prems(1)
          by (metis option.exhaust prod_cases3) 
        then have "f2 (xy#xs) = f2 xs"
          unfolding f2 map_filter_simps by auto
        moreover have "f1 (xy#xs) = f1 xs"
          using None unfolding f1 map_filter_simps by auto
        ultimately show ?thesis
          using Cons.IH Cons.prems(1) Cons.prems(2) Cons.prems(3) None by fastforce          
      next
        case (Some ioab)
        then have "f1 (xy#xs) = ioab"
          unfolding f1 map_filter_simps
          by simp 
        then have "ioab = (io,(a,b))"
          using Cons.prems(3) by auto
        then have "f2' xy = Some (io,(b,a))"
          using Cons.prems(1) Some by auto
        then show "f2 (xy#xs) = (io,(b,a))"
          unfolding f2 map_filter_simps by auto
      qed
    qed
  qed

  moreover have "f1 xs = (io,(a,b))"
    using \<open>(select_diverging_ofsm_table_io M q1 q2 (Suc k)) = (io,(a,b))\<close> 
    unfolding select_diverging_ofsm_table_io.simps f1 f1' xs Let_def by auto

  moreover have "\<exists> xy \<in> list.set xs . f1' xy \<noteq> None"
  proof -
    let ?P = "\<forall> x y . x \<in> inputs M \<longrightarrow> y \<in> outputs M \<longrightarrow> (h_obs M q1 x y = None \<longleftrightarrow> h_obs M q2 x y = None)"
    show ?thesis proof (cases ?P)
      case False
      then obtain x y where "x \<in> inputs M" and "y \<in> outputs M" and "\<not> (h_obs M q1 x y = None \<longleftrightarrow> h_obs M q2 x y = None)"
        by blast
      then consider "h_obs M q1 x y = None \<and> (\<exists> q2' . h_obs M q2 x y = Some q2')" |
                    "h_obs M q2 x y = None \<and> (\<exists> q1' . h_obs M q1 x y = Some q1')"
        by fastforce
      then show ?thesis proof cases
        case 1
        then obtain q2' where "h_obs M q1 x y = None" and "h_obs M q2 x y = Some q2'" by blast
        then have "f1' (x,y) = Some ((x,y),(None, Some q2'))"
          unfolding f1' by force
        moreover have "(x,y) \<in> list.set xs"
          unfolding xs
          using \<open>y \<in> outputs M\<close> outputs_as_list_set[of M]
          using \<open>x \<in> inputs M\<close> inputs_as_list_set[of M] 
          using image_iff by fastforce 
        ultimately show ?thesis 
          by blast
      next
        case 2
        then obtain q1' where "h_obs M q2 x y = None" and "h_obs M q1 x y = Some q1'" by blast
        then have "f1' (x,y) = Some ((x,y),(Some q1', None))"
          unfolding f1' by force
        moreover have "(x,y) \<in> list.set xs"
          unfolding xs
          using \<open>y \<in> outputs M\<close> outputs_as_list_set[of M]
          using \<open>x \<in> inputs M\<close> inputs_as_list_set[of M] 
          using image_iff by fastforce 
        ultimately show ?thesis 
          by blast
      qed
    next 
      case True
  
      obtain io where "length io \<le> Suc k" and "io \<in> LS M q1 \<union> LS M q2" and "io \<notin> LS M q1 \<inter> LS M q2"
        using \<open>ofsm_table M (\<lambda>q . states M)  (Suc k) q1 \<noteq> ofsm_table M (\<lambda>q . states M)  (Suc k) q2\<close>
        unfolding ofsm_table_set_observable[OF assms(1,2) minimise_initial_partition] ofsm_table_set_observable[OF assms(1,3) minimise_initial_partition] by blast
    
      then have "io \<noteq> []"
        using assms(2) assms(3) by auto 
      then have "io = [hd io] @ tl io"
        by (metis append.left_neutral append_Cons list.exhaust_sel)    
      then obtain x y where "hd io = (x,y)"
        by (meson prod.exhaust_sel)
    
      have "[(x,y)] \<in> LS M q1 \<inter> LS M q2"
      proof -
        have "[(x,y)] \<in> LS M q1 \<union> LS M q2"
          using \<open>io \<in> LS M q1 \<union> LS M q2\<close> language_prefix \<open>hd io = (x,y)\<close> \<open>io = [hd io] @ tl io\<close>
          by (metis Un_iff) 
        then have "x \<in> inputs M" and "y \<in> outputs M"
          by auto
        
        consider "[(x,y)] \<in> LS M q1" | "[(x,y)] \<in> LS M q2"
          using \<open>[(x,y)] \<in> LS M q1 \<union> LS M q2\<close> by blast
        then show ?thesis 
        proof cases
          case 1
          then have "h_obs M q1 x y \<noteq> None"
            using h_obs_None[OF \<open>observable M\<close>] unfolding LS_single_transition by auto
          then have "h_obs M q2 x y \<noteq> None"
            using True \<open>x \<in> inputs M\<close> \<open>y \<in> outputs M\<close> by meson
          then show ?thesis 
            using 1 h_obs_None[OF \<open>observable M\<close>] 
            by (metis IntI LS_single_transition fst_conv snd_conv) 
        next
          case 2
          then have "h_obs M q2 x y \<noteq> None"
            using h_obs_None[OF \<open>observable M\<close>] unfolding LS_single_transition by auto
          then have "h_obs M q1 x y \<noteq> None"
            using True \<open>x \<in> inputs M\<close> \<open>y \<in> outputs M\<close> by meson
          then show ?thesis 
            using 2 h_obs_None[OF \<open>observable M\<close>] 
            by (metis IntI LS_single_transition fst_conv snd_conv) 
        qed
      qed
      then obtain q1' q2' where "(q1,x,y,q1') \<in> transitions M" 
                            and "(q2,x,y,q2') \<in> transitions M"
        using LS_single_transition by force
      then have "q1' \<in> states M" and "q2' \<in> states M" using fsm_transition_target by auto
    
      have "tl io \<in> LS M q1' \<union> LS M q2'"
        using observable_language_transition_target[OF \<open>observable M\<close> \<open>(q1,x,y,q1') \<in> transitions M\<close>]
              observable_language_transition_target[OF \<open>observable M\<close> \<open>(q2,x,y,q2') \<in> transitions M\<close>]
              \<open>io \<in> LS M q1 \<union> LS M q2\<close>
        unfolding fst_conv snd_conv
        by (metis Un_iff \<open>hd io = (x, y)\<close> \<open>io = [hd io] @ tl io\<close> append_Cons append_Nil) 
      moreover have "tl io \<notin> LS M q1' \<inter> LS M q2'"
        using observable_language_transition_target[OF \<open>observable M\<close> \<open>(q1,x,y,q1') \<in> transitions M\<close>]
              observable_language_transition_target[OF \<open>observable M\<close> \<open>(q2,x,y,q2') \<in> transitions M\<close>]
              \<open>io \<in> LS M q1 \<union> LS M q2\<close>
        unfolding fst_conv snd_conv
        by (metis Int_iff LS_prepend_transition \<open>(q1, x, y, q1') \<in> FSM.transitions M\<close> \<open>(q2, x, y, q2') \<in> FSM.transitions M\<close> \<open>hd io = (x, y)\<close> \<open>io \<noteq> []\<close> \<open>io \<notin> LS M q1 \<inter> LS M q2\<close> fst_conv list.collapse snd_conv)    
      ultimately have "((tl io) \<in> LS M q1') \<noteq> (tl io \<in> LS M q2')"
        by blast
      moreover have "length (tl io) \<le> k"
        using \<open>length io \<le> Suc k\<close> by auto
      ultimately have "q2' \<notin> ofsm_table M (\<lambda>q . states M)  k q1'"
        unfolding ofsm_table_set_observable[OF assms(1) \<open>q1' \<in> states M\<close> minimise_initial_partition] 
        by blast
      then have "ofsm_table M (\<lambda>q . states M)  k q1' \<noteq> ofsm_table M (\<lambda>q . states M)  k q2'"
        by (metis \<open>q2' \<in> FSM.states M\<close> ofsm_table_containment) 
      moreover have "h_obs M q1 x y = Some q1'"
        using \<open>(q1,x,y,q1') \<in> transitions M\<close> \<open>observable M\<close> unfolding h_obs_Some[OF \<open>observable M\<close>] observable_alt_def by auto
      moreover have "h_obs M q2 x y = Some q2'"
        using \<open>(q2,x,y,q2') \<in> transitions M\<close> \<open>observable M\<close> unfolding h_obs_Some[OF \<open>observable M\<close>] observable_alt_def by auto
      ultimately have "f1' (x,y) = Some ((x,y),(Some q1', Some q2'))"
        unfolding f1' by force
          
      moreover have "(x,y) \<in> list.set xs"
        unfolding xs 
        using fsm_transition_output[OF \<open>(q1,x,y,q1') \<in> transitions M\<close>] outputs_as_list_set[of M]
        using fsm_transition_input[OF \<open>(q1,x,y,q1') \<in> transitions M\<close>] inputs_as_list_set[of M] 
        using image_iff by fastforce 
      ultimately show ?thesis 
        by blast
    qed
  qed

  ultimately have "f2 xs = (io,(b,a))"
    by blast
  then show ?thesis
    unfolding select_diverging_ofsm_table_io.simps f2 f2' xs Let_def by auto
qed


lemma assemble_distinguishing_sequence_from_ofsm_table_sym :
  assumes "observable M"
  and     "q1 \<in> states M"
  and     "q2 \<in> states M"
  and     "ofsm_table M (\<lambda>q . states M)  k q1 \<noteq> ofsm_table M (\<lambda>q . states M)  k q2"
shows "assemble_distinguishing_sequence_from_ofsm_table M q1 q2 k = assemble_distinguishing_sequence_from_ofsm_table M q2 q1 k"
  using assms(2,3,4) proof (induction k arbitrary: q1 q2)
  case 0
  then show ?case by auto
next
  case (Suc k)
  obtain xy a b where "select_diverging_ofsm_table_io M q1 q2 (Suc k) = (xy,(a,b))"
    using prod_cases3 by blast
  then have "select_diverging_ofsm_table_io M q2 q1 (Suc k) = (xy,(b, a))"
      using select_diverging_ofsm_table_io_sym[OF assms(1) Suc.prems] by auto

  consider "\<exists> q1' q2' . a = Some q1' \<and> b = Some q2'" | "a = None \<or> b = None"
    using option.exhaust_sel by auto 
  then show ?case proof cases
    case 1
    then obtain q1' q2' where "select_diverging_ofsm_table_io M q1 q2 (Suc k) = (xy,(Some q1', Some q2'))"
      using \<open>select_diverging_ofsm_table_io M q1 q2 (Suc k) = (xy,(a,b))\<close> by auto
    then have "select_diverging_ofsm_table_io M q2 q1 (Suc k) = (xy,(Some q2', Some q1'))"
      using select_diverging_ofsm_table_io_sym[OF assms(1) Suc.prems] by auto

    obtain x y where "select_diverging_ofsm_table_io M q1 q2 (Suc k) = ((x,y),(h_obs M q1 x y, h_obs M q2 x y))"
                 and "\<And> q1' q2' . h_obs M q1 x y = Some q1' \<Longrightarrow> h_obs M q2 x y = Some q2' \<Longrightarrow> ofsm_table M (\<lambda>q . states M)  k q1' \<noteq> ofsm_table M (\<lambda>q . states M)  k q2'"
                 and "h_obs M q1 x y \<noteq> None \<or> h_obs M q2 x y \<noteq> None"
      using select_diverging_ofsm_table_io_Some(1)[OF assms(1) Suc.prems]
      by blast
    then have "xy = (x,y)" and "h_obs M q1 x y = Some q1'" and "h_obs M q2 x y = Some q2'"
      using \<open>select_diverging_ofsm_table_io M q1 q2 (Suc k) = (xy,(Some q1', Some q2'))\<close> by auto
    then have "q1' \<in> states M" and "q2' \<in> states M"
      unfolding h_obs_Some[OF assms(1)] using fsm_transition_target by fastforce+
    moreover have "ofsm_table M (\<lambda>q . states M)  k q1' \<noteq> ofsm_table M (\<lambda>q . states M)  k q2'"
      using \<open>h_obs M q1 x y = Some q1'\<close> \<open>h_obs M q2 x y = Some q2'\<close> \<open>\<And> q1' q2' . h_obs M q1 x y = Some q1' \<Longrightarrow> h_obs M q2 x y = Some q2' \<Longrightarrow> ofsm_table M (\<lambda>q . states M)  k q1' \<noteq> ofsm_table M (\<lambda>q . states M)  k q2'\<close>
      by blast
    ultimately have "assemble_distinguishing_sequence_from_ofsm_table M  q1' q2' k = assemble_distinguishing_sequence_from_ofsm_table M  q2' q1' k"
      using Suc.IH by auto
    then show ?thesis
      using \<open>select_diverging_ofsm_table_io M q1 q2 (Suc k) = (xy,(Some q1', Some q2'))\<close>
            \<open>select_diverging_ofsm_table_io M q2 q1 (Suc k) = (xy,(Some q2', Some q1'))\<close>
      by auto
  next
    case 2

    obtain x y where "xy = (x,y)"
      using prod.exhaust by metis
    have helper: "\<And> f f1 f2 .(case ((x,y),(a,b)) of ((x,y),(Some a',Some b')) \<Rightarrow> f1 x y a' b' | ((x,y),_) \<Rightarrow> f2 x y) = f2 x y"
      using 2 by (metis case_prod_conv option.case_eq_if)
    have helper2: "\<And> f f1 f2 .(case ((x,y),(b,a)) of ((x,y),(Some a',Some b')) \<Rightarrow> f1 x y a' b' | ((x,y),_) \<Rightarrow> f2 x y) = f2 x y"
      using 2 by (metis case_prod_conv option.case_eq_if)
    

    have "assemble_distinguishing_sequence_from_ofsm_table M  q1 q2 (Suc k) = [xy]"
      unfolding assemble_distinguishing_sequence_from_ofsm_table.simps
                \<open>select_diverging_ofsm_table_io M q1 q2 (Suc k) = (xy,(a, b))\<close>  \<open>xy = (x,y)\<close> helper 
      by simp
    moreover have "assemble_distinguishing_sequence_from_ofsm_table M  q2 q1 (Suc k) = [xy]"
      unfolding assemble_distinguishing_sequence_from_ofsm_table.simps
                \<open>select_diverging_ofsm_table_io M q2 q1 (Suc k) = (xy,(b, a))\<close>  \<open>xy = (x,y)\<close> helper2 
      by simp
    ultimately show ?thesis 
      by simp 
  qed
qed 

lemma find_first_distinct_ofsm_table_sym :
  assumes "q1 \<in> FSM.states M" 
      and "q2 \<in> FSM.states M"
      and "ofsm_table_fix M (\<lambda>q . states M) 0 q1 \<noteq> ofsm_table_fix M (\<lambda>q . states M) 0 q2"
shows  "find_first_distinct_ofsm_table M q1 q2 = find_first_distinct_ofsm_table M q2 q1"
proof -
  have "\<And> q1 q2 . q1 \<in> FSM.states M \<Longrightarrow> q2 \<in> FSM.states M \<Longrightarrow> ofsm_table_fix M (\<lambda>q . states M) 0 q1 \<noteq> ofsm_table_fix M (\<lambda>q . states M) 0 q2 \<Longrightarrow> find_first_distinct_ofsm_table M q2 q1 < find_first_distinct_ofsm_table M q1 q2 \<Longrightarrow> False"
  proof -
    fix q1 q2 assume "q1 \<in> FSM.states M" and "q2 \<in> FSM.states M"
                 and "ofsm_table_fix M (\<lambda>q . states M) 0 q1 \<noteq> ofsm_table_fix M (\<lambda>q . states M) 0 q2"
                 and "find_first_distinct_ofsm_table M q2 q1 < find_first_distinct_ofsm_table M q1 q2"
  
    show False
      using find_first_distinct_ofsm_table_is_first(1)[OF \<open>q1 \<in> FSM.states M\<close> \<open>q2 \<in> FSM.states M\<close> \<open>ofsm_table_fix M (\<lambda>q . states M) 0 q1 \<noteq> ofsm_table_fix M (\<lambda>q . states M) 0 q2\<close>]
            find_first_distinct_ofsm_table_is_first(2)[OF \<open>q1 \<in> FSM.states M\<close> \<open>q2 \<in> FSM.states M\<close> \<open>ofsm_table_fix M (\<lambda>q . states M) 0 q1 \<noteq> ofsm_table_fix M (\<lambda>q . states M) 0 q2\<close> \<open>find_first_distinct_ofsm_table M q2 q1 < find_first_distinct_ofsm_table M q1 q2\<close>]
            \<open>find_first_distinct_ofsm_table M q2 q1 < find_first_distinct_ofsm_table M q1 q2\<close>
      by (metis \<open>ofsm_table_fix M (\<lambda>q . states M) 0 q1 \<noteq> ofsm_table_fix M (\<lambda>q . states M) 0 q2\<close> \<open>q1 \<in> FSM.states M\<close> \<open>q2 \<in> FSM.states M\<close> find_first_distinct_ofsm_table_gt_is_first_gt(1))
  qed
  then show ?thesis
    using assms
    by (metis linorder_neqE_nat) 
qed


lemma get_distinguishing_sequence_from_ofsm_tables_sym :
  assumes "observable M"
  and     "minimal M"
  and     "q1 \<in> states M"
  and     "q2 \<in> states M"
  and     "q1 \<noteq> q2"
shows "get_distinguishing_sequence_from_ofsm_tables M q1 q2 = get_distinguishing_sequence_from_ofsm_tables M q2 q1"
proof -

  have "ofsm_table_fix M (\<lambda>q . states M) 0 q1 \<noteq> ofsm_table_fix M (\<lambda>q . states M) 0 q2"
    using \<open>minimal M\<close> unfolding minimal_observable_code[OF assms(1)]
    using assms(3,4,5) by blast

  let ?k = "find_first_distinct_ofsm_table_gt M q1 q2 0"
  have "ofsm_table M (\<lambda>q . states M)  ?k q1 \<noteq> ofsm_table M (\<lambda>q . states M)  ?k q2"
    using find_first_distinct_ofsm_table_is_first(1)[OF assms(3,4) \<open>ofsm_table_fix M (\<lambda>q . states M) 0 q1 \<noteq> ofsm_table_fix M (\<lambda>q . states M) 0 q2\<close>] .

  show ?thesis
    using assemble_distinguishing_sequence_from_ofsm_table_sym[OF assms(1,3,4) \<open>ofsm_table M (\<lambda>q . states M)  ?k q1 \<noteq> ofsm_table M (\<lambda>q . states M)  ?k q2\<close>]
    unfolding get_distinguishing_sequence_from_ofsm_tables.simps Let_def
              find_first_distinct_ofsm_table_sym[OF assms(3,4) \<open>ofsm_table_fix M (\<lambda>q . states M) 0 q1 \<noteq> ofsm_table_fix M (\<lambda>q . states M) 0 q2\<close>] .
qed

subsubsection \<open>Harmonised State Identifiers\<close>


fun add_distinguishing_sequence :: "('a,'b::linorder,'c::linorder) fsm \<Rightarrow> (('b\<times>'c) list \<times> 'a) \<times> (('b\<times>'c) list \<times> 'a) \<Rightarrow> ('b\<times>'c) prefix_tree \<Rightarrow> ('b\<times>'c) prefix_tree" where
  "add_distinguishing_sequence M ((\<alpha>,q1), (\<beta>,q2)) t = insert empty (get_distinguishing_sequence_from_ofsm_tables M q1 q2)"

lemma add_distinguishing_sequence_distinguishes :
  assumes "observable M"
  and     "minimal M"
  and     "\<alpha> \<in> L M"
  and     "\<beta> \<in> L M" 
  and     "after_initial M \<alpha> \<noteq> after_initial M \<beta>" 
shows "\<exists> io \<in> set (add_distinguishing_sequence M ((\<alpha>,after_initial M \<alpha>),(\<beta>,after_initial M \<beta>)) t) \<union> (set (after t \<alpha>) \<inter> set (after t \<beta>)) .  distinguishes M (after_initial M \<alpha>) (after_initial M \<beta>) io"
proof -
  have "set (add_distinguishing_sequence M ((\<alpha>,after_initial M \<alpha>),(\<beta>,after_initial M \<beta>)) t) = set (insert empty (get_distinguishing_sequence_from_ofsm_tables M (after_initial M \<alpha>) (after_initial M \<beta>)))"
    by auto
  then have "get_distinguishing_sequence_from_ofsm_tables M (after_initial M \<alpha>) (after_initial M \<beta>) \<in> set (add_distinguishing_sequence M ((\<alpha>,after_initial M \<alpha>),(\<beta>,after_initial M \<beta>)) t) \<union> (set (after t \<alpha>) \<inter> set (after t \<beta>))"
    unfolding insert_set by auto
  then show ?thesis 
    using get_distinguishing_sequence_from_ofsm_tables_is_distinguishing_trace(1,2)[OF assms(1,2) after_is_state[OF assms(1,3)] after_is_state[OF assms(1,4)] assms(5)]
    by (meson distinguishes_def) 
qed

lemma add_distinguishing_sequence_finite : 
  "finite_tree (add_distinguishing_sequence M ((\<alpha>,after_initial M \<alpha>),(\<beta>,after_initial M \<beta>)) t)"
  unfolding add_distinguishing_sequence.simps
  using insert_finite_tree[OF empty_finite_tree] by metis



fun get_HSI :: "('a::linorder,'b::linorder,'c::linorder) fsm \<Rightarrow> 'a \<Rightarrow> ('b\<times>'c) prefix_tree" where
  "get_HSI M q = from_list (map (\<lambda>q' . get_distinguishing_sequence_from_ofsm_tables M q q') (filter ((\<noteq>) q) (states_as_list M)))"


lemma get_HSI_elem :
  assumes "q2 \<in> states M"
  and     "q2 \<noteq> q1"
shows "get_distinguishing_sequence_from_ofsm_tables M q1 q2 \<in> set (get_HSI M q1)"
proof -
  have "q2 \<in> list.set (filter ((\<noteq>) q1) (states_as_list M))"
    using assms unfolding states_as_list_set[of M,symmetric] by auto
  then have *:"get_distinguishing_sequence_from_ofsm_tables M q1 q2 \<in> list.set (map (\<lambda>q' . get_distinguishing_sequence_from_ofsm_tables M q1 q') (filter ((\<noteq>) q1) (states_as_list M)))"
    by auto
  show ?thesis
    using from_list_set_elem[OF *]
    unfolding get_HSI.simps .
qed

lemma get_HSI_distinguishes :
  assumes "observable M"
  and     "minimal M"
  and     "q1 \<in> states M" and "q2 \<in> states M" and "q1 \<noteq> q2"
shows "\<exists> io \<in> set (get_HSI M q1) \<inter> set (get_HSI M q2) . distinguishes M q1 q2 io"
proof -

  have "get_distinguishing_sequence_from_ofsm_tables M q2 q1 \<in> set (get_HSI M q1)"
    using get_HSI_elem[OF assms(4), of q1] assms(5) 
    unfolding get_distinguishing_sequence_from_ofsm_tables_sym[OF assms]
    by metis
  moreover have "get_distinguishing_sequence_from_ofsm_tables M q2 q1 \<in> set (get_HSI M q2)"
    using get_HSI_elem[OF assms(3)] assms(5) by metis
  moreover have "distinguishes M q1 q2 (get_distinguishing_sequence_from_ofsm_tables M q2 q1)"
    using get_distinguishing_sequence_from_ofsm_tables_is_distinguishing_trace(1,2)[OF assms]
    unfolding get_distinguishing_sequence_from_ofsm_tables_sym[OF assms]
    unfolding distinguishes_def
    by blast
  ultimately show ?thesis
    by blast
qed
    
lemma get_HSI_finite :
  "finite_tree (get_HSI M q)"
  unfolding get_HSI.simps using from_list_finite_tree by metis


subsubsection \<open>Distinguishing Sets\<close>

fun distinguishing_set :: "('a :: linorder, 'b :: linorder, 'c :: linorder) fsm \<Rightarrow> ('b \<times> 'c) prefix_tree" where
  "distinguishing_set M = (let 
    pairs = filter (\<lambda> (x,y) . x \<noteq> y) (list_ordered_pairs (states_as_list M))
  in from_list (map (case_prod (get_distinguishing_sequence_from_ofsm_tables M)) pairs))"



lemma distinguishing_set_distinguishes :
  assumes "observable M"
  and     "minimal M"
  and     "q1 \<in> states M"
  and     "q2 \<in> states M" 
  and     "q1 \<noteq> q2"   
shows "\<exists> io \<in> set (distinguishing_set M) .  distinguishes M q1 q2 io"
proof -
  define pairs where pairs: "pairs = filter (\<lambda> (x,y) . x \<noteq> y) (list_ordered_pairs (states_as_list M))"
  then have *: "distinguishing_set M = from_list (map (case_prod (get_distinguishing_sequence_from_ofsm_tables M)) pairs)"
    by auto

  have "q1 \<in> list.set (states_as_list M)" and "q2 \<in> list.set (states_as_list M)"
    unfolding states_as_list_set using assms(3,4) by blast+
  then have "(q1,q2) \<in> list.set pairs \<or> (q2,q1) \<in> list.set pairs"
    using list_ordered_pairs_set_containment[OF _ _ assms(5)] assms(5) unfolding pairs by auto
  then have "get_distinguishing_sequence_from_ofsm_tables M q1 q2 \<in> list.set (map (case_prod (get_distinguishing_sequence_from_ofsm_tables M)) pairs)
              | get_distinguishing_sequence_from_ofsm_tables M q2 q1 \<in> list.set (map (case_prod (get_distinguishing_sequence_from_ofsm_tables M)) pairs)"
    by (metis image_iff old.prod.case set_map)
  then have "get_distinguishing_sequence_from_ofsm_tables M q1 q2 \<in> set (distinguishing_set M) 
              \<or> get_distinguishing_sequence_from_ofsm_tables M q2 q1 \<in> set (distinguishing_set M)"
    unfolding * from_list_set by blast
  then show ?thesis
    using get_distinguishing_sequence_from_ofsm_tables_is_distinguishing_trace(1,2)[OF assms]
          get_distinguishing_sequence_from_ofsm_tables_is_distinguishing_trace(1,2)[OF assms(1,2,4,3)] assms(5)
    unfolding distinguishes_def by blast
qed


lemma distinguishing_set_finite :
  "finite_tree (distinguishing_set M)"
  unfolding distinguishing_set.simps Let_def
  using from_list_finite_tree by metis




function (domintros) intersection_is_distinguishing :: "('a,'b,'c) fsm \<Rightarrow> ('b \<times> 'c) prefix_tree \<Rightarrow> 'a \<Rightarrow> ('b \<times> 'c) prefix_tree \<Rightarrow> 'a \<Rightarrow> bool" where
  "intersection_is_distinguishing M (PT t1) q1 (PT t2) q2 = 
    (\<exists> (x,y) \<in> dom t1 \<inter> dom t2 .
      case h_obs M q1 x y of
        None \<Rightarrow> h_obs M q2 x y \<noteq> None |
        Some q1' \<Rightarrow> (case h_obs M q2 x y of
          None \<Rightarrow> True |
          Some q2' \<Rightarrow> intersection_is_distinguishing M (the (t1 (x,y))) q1' (the (t2 (x,y))) q2'))"
  by pat_completeness auto
termination 
proof -
  {
    fix M :: "('a,'b,'c) fsm"
    fix t1
    fix q1
    fix t2
    fix q2
  
    have "intersection_is_distinguishing_dom (M, t1,q1, t2,q2)" 
    proof (induction t1 arbitrary: t2 q1 q2)
      case (PT m1)
  
      obtain m2 where "t2 = PT m2"
        by (metis prefix_tree.exhaust)
  
      have "(\<And>xy t1' t2' q1' q2' . m1 xy = Some t1' \<Longrightarrow> intersection_is_distinguishing_dom (M, t1', q1', t2', q2'))"
      proof -
        fix xy t1' t2' q1' q2' assume "m1 xy = Some t1'"
  
        then have "Some t1' \<in> range m1"
          by (metis  range_eqI) 
        
        show "intersection_is_distinguishing_dom (M, t1', q1', t2', q2')"
          using PT(1)[OF \<open>Some t1' \<in> range m1\<close>]
          by simp 
      qed
  
      then show ?case
        using intersection_is_distinguishing.domintros[of q1 M q2 m1 m2] unfolding \<open>t2 = PT m2\<close> by blast
    qed
  }
  then show ?thesis by auto
qed


        

lemma intersection_is_distinguishing_code[code] :
  "intersection_is_distinguishing M (MPT t1) q1 (MPT t2) q2 = 
    (\<exists> (x,y) \<in> Mapping.keys t1 \<inter> Mapping.keys t2 .
      case h_obs M q1 x y of
        None \<Rightarrow> h_obs M q2 x y \<noteq> None |
        Some q1' \<Rightarrow> (case h_obs M q2 x y of
          None \<Rightarrow> True |
          Some q2' \<Rightarrow> intersection_is_distinguishing M (the (Mapping.lookup t1 (x,y))) q1' (the (Mapping.lookup  t2 (x,y))) q2'))"
  unfolding intersection_is_distinguishing.simps MPT_def
  by (simp add: keys_dom_lookup) 

lemma intersection_is_distinguishing_correctness :
  assumes "observable M"
  and     "q1 \<in> states M"
  and     "q2 \<in> states M"
shows "intersection_is_distinguishing M t1 q1 t2 q2 = (\<exists> io . isin t1 io \<and> isin t2 io \<and> distinguishes M q1 q2 io)"
  (is "?P1 = ?P2")
proof 
  show "?P1 \<Longrightarrow> ?P2"
  proof (induction t1 arbitrary: t2 q1 q2)
    case (PT m1)

    obtain m2 where "t2 = PT m2"
      using prefix_tree.exhaust by blast
    then obtain x y where "(x,y) \<in> dom m1" and "(x,y) \<in> dom m2"
                            and *: "case h_obs M q1 x y of
                                    None \<Rightarrow> h_obs M q2 x y \<noteq> None |
                                    Some q1' \<Rightarrow> (case h_obs M q2 x y of
                                      None \<Rightarrow> True |
                                      Some q2' \<Rightarrow> intersection_is_distinguishing M (the (m1 (x,y))) q1' (the (m2 (x,y))) q2')"
      using PT.prems(1) intersection_is_distinguishing.simps by force

    obtain t1' where "m1 (x,y) = Some t1'"
      using \<open>(x,y) \<in> dom m1\<close> by auto
    then have "isin (PT m1) [(x,y)]"
      by auto

    obtain t2' where "m2 (x,y) = Some t2'"
      using \<open>(x,y) \<in> dom m2\<close> by auto
    then have "isin t2 [(x,y)]"
      unfolding \<open>t2 = PT m2\<close> by auto

    show ?case proof (cases "h_obs M q1 x y")
      case None
      then have "h_obs M q2 x y \<noteq> None"
        using * by auto
      then have "[(x,y)] \<in> LS M q2"
        unfolding LS_single_transition h_obs_None[OF \<open>observable M\<close>]
        by fastforce
      moreover have "[(x,y)] \<notin> LS M q1"
        using None unfolding LS_single_transition h_obs_None[OF \<open>observable M\<close>]
        by auto
      ultimately have "distinguishes M q1 q2 [(x,y)]"
        unfolding distinguishes_def by blast
      then show ?thesis 
        using \<open>isin (PT m1) [(x,y)]\<close> \<open>isin t2 [(x,y)]\<close> by blast
    next
      case (Some q1')
      then have "[(x,y)] \<in> LS M q1"
        unfolding LS_single_transition h_obs_Some[OF \<open>observable M\<close>]
        using insert_compr by fastforce
        
      
      show ?thesis proof (cases "h_obs M q2 x y")
        case None
        then have "[(x,y)] \<notin> LS M q2"
          unfolding LS_single_transition h_obs_None[OF \<open>observable M\<close>]
          by auto
        then have "distinguishes M q1 q2 [(x,y)]"
          using \<open>[(x,y)] \<in> LS M q1\<close> unfolding distinguishes_def by blast
        then show ?thesis 
          using \<open>isin (PT m1) [(x,y)]\<close> \<open>isin t2 [(x,y)]\<close> by blast
      next
        case (Some q2')
        then have "intersection_is_distinguishing M (the (m1 (x,y))) q1' (the (m2 (x,y))) q2'"
          using \<open>h_obs M q1 x y = Some q1'\<close> * by auto
        moreover have "(the (m1 (x,y))) = t1'"
          using \<open>m1 (x,y) = Some t1'\<close> by auto
        moreover have "(the (m2 (x,y))) = t2'"
          using \<open>m2 (x,y) = Some t2'\<close> by auto
        ultimately have "intersection_is_distinguishing M t1' q1' t2' q2'"
          by simp
        then have "\<exists>io. isin t1' io \<and> isin t2' io \<and> distinguishes M q1' q2' io"
          using PT.IH[of "Some t1'" t1' q1' t2' q2']
          by (metis \<open>m1 (x, y) = Some t1'\<close> option.set_intros rangeI) 
        then obtain io where "isin t1' io"
                         and "isin t2' io"
                         and "distinguishes M q1' q2' io"
          by blast

        have "isin (PT m1) ((x,y)#io)"
          using \<open>m1 (x, y) = Some t1'\<close> \<open>isin t1' io\<close> by auto
        moreover have "isin t2 ((x,y)#io)"
          using \<open>t2 = PT m2\<close> \<open>m2 (x, y) = Some t2'\<close> \<open>isin t2' io\<close> by auto
        moreover have "distinguishes M q1 q2 ((x,y)#io)"
          using h_obs_language_iff[OF \<open>observable M\<close>, of x y io  q1] unfolding \<open>h_obs M q1 x y = Some q1'\<close> 
          using h_obs_language_iff[OF \<open>observable M\<close>, of x y io  q2] unfolding Some
          using \<open>distinguishes M q1' q2' io\<close>
          unfolding distinguishes_def
          by auto
        ultimately show ?thesis
          by blast
      qed
    qed
  qed

  show "?P2 \<Longrightarrow> ?P1"
  proof -
    assume ?P2
    then obtain io where "isin t1 io" 
                     and "isin t2 io" 
                     and "distinguishes M q1 q2 io"
      by blast
    then show ?P1 
    using assms(2,3) proof (induction io arbitrary: t1 t2 q1 q2)
      case Nil 
      then have "[] \<in> LS M q1 \<inter> LS M q2"
        by auto
      then have "\<not> distinguishes M q1 q2 []"
        unfolding distinguishes_def by blast
      then show ?case 
        using \<open>distinguishes M q1 q2 []\<close> by simp
    next
      case (Cons a io)

      obtain x y where "a = (x,y)"
        by fastforce

      obtain m1 where "t1 = PT m1"
        using prefix_tree.exhaust by blast
      obtain t1' where "m1 (x,y) = Some t1'"
                   and "isin t1' io"
        using \<open>isin t1 (a # io)\<close> unfolding \<open>a = (x,y)\<close> \<open>t1 = PT m1\<close> isin.simps
        using case_optionE by blast 
  
      obtain m2 where "t2 = PT m2"
        using prefix_tree.exhaust by blast
      obtain t2' where "m2 (x,y) = Some t2'"
                   and "isin t2' io"
        using \<open>isin t2 (a # io)\<close> unfolding \<open>a = (x,y)\<close> \<open>t2 = PT m2\<close> isin.simps
        using case_optionE by blast
      then have "(x,y) \<in> dom m1 \<inter> dom m2"
        using \<open>m1 (x,y) = Some t1'\<close> by auto
    

      show ?case proof (cases "h_obs M q1 x y")
        case None
        then have "[(x,y)] \<notin> LS M q1"
          unfolding LS_single_transition h_obs_None[OF \<open>observable M\<close>]
          by auto
        then have "a#io \<notin> LS M q1"
          unfolding \<open>a = (x,y)\<close>
          by (metis None assms(1) h_obs_language_iff option.distinct(1))
        then have "a#io \<in> LS M q2"
          using \<open>distinguishes M q1 q2 (a#io)\<close> unfolding distinguishes_def by blast
        then have "[(x,y)] \<in> LS M q2"
          unfolding \<open>a = (x,y)\<close>
          using language_prefix
          by (metis append_Cons append_Nil) 
        then have "h_obs M q2 x y \<noteq> None"
          unfolding h_obs_None[OF \<open>observable M\<close>] LS_single_transition by force
        then show ?thesis
          using None \<open>(x,y) \<in> dom m1 \<inter> dom m2\<close> unfolding \<open>t1 = PT m1\<close> \<open>t2 = PT m2\<close> 
          by force
      next
        case (Some q1') 
        then have "[(x,y)] \<in> LS M q1"
          unfolding LS_single_transition h_obs_Some[OF \<open>observable M\<close>]
          by (metis Some assms(1) fst_conv h_obs_None option.distinct(1) snd_conv) 
  
        show ?thesis proof (cases "h_obs M q2 x y")
          case None
          then show ?thesis 
            using Some \<open>(x,y) \<in> dom m1 \<inter> dom m2\<close> unfolding \<open>t1 = PT m1\<close> \<open>t2 = PT m2\<close>  
            unfolding intersection_is_distinguishing.simps
            by (metis (no_types, lifting) case_prodI option.case_eq_if option.distinct(1)) 
        next
          case (Some q2')

          have "distinguishes M q1' q2' io"
            using h_obs_language_iff[OF \<open>observable M\<close>, of x y io  q1] unfolding \<open>h_obs M q1 x y = Some q1'\<close> 
            using h_obs_language_iff[OF \<open>observable M\<close>, of x y io  q2] unfolding Some
            using \<open>distinguishes M q1 q2 (a#io)\<close> unfolding \<open>a = (x,y)\<close> distinguishes_def 
            by blast
          moreover have "q1' \<in> states M" and "q2' \<in> states M"
            using Some \<open>h_obs M q1 x y = Some q1'\<close> unfolding h_obs_Some[OF \<open>observable M\<close>]
            using fsm_transition_target[where M=M]
            by fastforce+
          ultimately have "intersection_is_distinguishing M t1' q1' t2' q2'"
            using Cons.IH[OF \<open>isin t1' io\<close> \<open>isin t2' io\<close>]
            by auto
          then show ?thesis 
            using \<open>(x,y) \<in> dom m1 \<inter> dom m2\<close> Some \<open>h_obs M q1 x y = Some q1'\<close> 
            unfolding \<open>t1 = PT m1\<close> \<open>t2 = PT m2\<close>
            unfolding intersection_is_distinguishing.simps
            by (metis (no_types, lifting) \<open>m1 (x, y) = Some t1'\<close> \<open>m2 (x, y) = Some t2'\<close> case_prodI option.case_eq_if option.distinct(1) option.sel) 
        qed
      qed
    qed
  qed
qed


fun contains_distinguishing_trace :: "('a,'b,'c) fsm \<Rightarrow> ('b \<times> 'c) prefix_tree \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> bool" where
  "contains_distinguishing_trace M T q1 q2 = intersection_is_distinguishing M T q1 T q2"

lemma contains_distinguishing_trace_code[code] :
  "contains_distinguishing_trace M (MPT t1) q1 q2 = 
    (\<exists> (x,y) \<in> Mapping.keys t1.
      case h_obs M q1 x y of
        None \<Rightarrow> h_obs M q2 x y \<noteq> None |
        Some q1' \<Rightarrow> (case h_obs M q2 x y of
          None \<Rightarrow> True |
          Some q2' \<Rightarrow> contains_distinguishing_trace M (the (Mapping.lookup t1 (x,y))) q1' q2'))"
  unfolding intersection_is_distinguishing.simps MPT_def
  by (simp add: keys_dom_lookup) 

lemma contains_distinguishing_trace_correctness :
  assumes "observable M"
  and     "q1 \<in> states M"
  and     "q2 \<in> states M"
shows "contains_distinguishing_trace M t q1 q2 = (\<exists> io . isin t io \<and> distinguishes M q1 q2 io)"
  using intersection_is_distinguishing_correctness[OF assms]
  by simp  


fun distinguishing_set_reduced :: "('a :: linorder, 'b :: linorder, 'c :: linorder) fsm \<Rightarrow> ('b \<times> 'c) prefix_tree" where
  "distinguishing_set_reduced M = (let 
    pairs = filter (\<lambda> (q,q') . q \<noteq> q') (list_ordered_pairs (states_as_list M));
    handlePair = (\<lambda> W (q,q') . if contains_distinguishing_trace M W q q'
                                then W
                                else insert W (get_distinguishing_sequence_from_ofsm_tables M q q'))
   in foldl handlePair empty pairs)" 


lemma distinguishing_set_reduced_distinguishes :
  assumes "observable M"
  and     "minimal M"
  and     "q1 \<in> states M"
  and     "q2 \<in> states M" 
  and     "q1 \<noteq> q2"   
shows "\<exists> io \<in> set (distinguishing_set_reduced M) . distinguishes M q1 q2 io"
proof -
  define pairs where pairs: "pairs = filter (\<lambda> (x,y) . x \<noteq> y) (list_ordered_pairs (states_as_list M))"
  
  
  define handlePair where "handlePair = (\<lambda> W (q,q') . if contains_distinguishing_trace M W q q'
                                then W
                                else insert W (get_distinguishing_sequence_from_ofsm_tables M q q'))"

  have "distinguishing_set_reduced M = foldl handlePair empty pairs"
    unfolding distinguishing_set_reduced.simps handlePair_def pairs Let_def by metis
  
  have handlePair_subset: "\<And> W q q' . set W \<subseteq> set (handlePair W (q,q'))"
    unfolding handlePair_def
    using insert_set unfolding case_prod_conv
    by (metis (mono_tags) Un_upper1 order_refl)


  have "q1 \<in> list.set (states_as_list M)" and "q2 \<in> list.set (states_as_list M)"
    unfolding states_as_list_set using assms(3,4) by blast+
  then have "(q1,q2) \<in> list.set pairs \<or> (q2,q1) \<in> list.set pairs"
    using list_ordered_pairs_set_containment[OF _ _ assms(5)] assms(5) unfolding pairs by auto
  moreover have "\<And> pairs' . list.set pairs' \<subseteq> list.set pairs \<Longrightarrow> (q1,q2) \<in> list.set pairs' \<or> (q2,q1) \<in> list.set pairs' \<Longrightarrow> (\<exists> io \<in> set (foldl handlePair empty pairs') .  distinguishes M q1 q2 io)"
  proof -
    fix pairs' assume "list.set pairs' \<subseteq> list.set pairs" and "(q1,q2) \<in> list.set pairs' \<or> (q2,q1) \<in> list.set pairs'"
    then show "(\<exists> io \<in> set (foldl handlePair empty pairs') .  distinguishes M q1 q2 io)"
    proof (induction pairs' rule: rev_induct)
      case Nil
      then show ?case by auto
    next
      case (snoc qq qqs)

      define W where "W = foldl handlePair empty qqs"
      have "foldl handlePair empty (qqs@[qq]) = handlePair W qq"
        unfolding W_def by auto
      then have W_subset: "set W \<subseteq> set (foldl handlePair empty (qqs@[qq]))"
        by (metis handlePair_subset prod.collapse)


      have handlePair_sym : "handlePair W (q1,q2) = handlePair W (q2,q1)"
        unfolding handlePair_def case_prod_conv
        unfolding contains_distinguishing_trace_correctness[OF assms(1,3,4)] contains_distinguishing_trace_correctness[OF assms(1,4,3)]
        unfolding get_distinguishing_sequence_from_ofsm_tables_sym[OF assms]
        using distinguishes_sym
        by metis

      show ?case proof (cases "qq = (q1,q2) \<or> qq = (q2,q1)")
        case True
        then have "foldl handlePair empty (qqs@[qq]) = handlePair W (q1,q2)"
          unfolding \<open>foldl handlePair empty (qqs@[qq]) = handlePair W qq\<close>
          using handlePair_sym
          by auto

        show ?thesis proof (cases "contains_distinguishing_trace M W q1 q2")
          case True
          then show ?thesis 
            unfolding contains_distinguishing_trace_correctness[OF assms(1,3,4)]
            using W_subset
            by auto 
        next
          case False
          then have "foldl handlePair empty (qqs@[qq]) = insert W (get_distinguishing_sequence_from_ofsm_tables M q1 q2)"
            unfolding \<open>foldl handlePair empty (qqs@[qq]) = handlePair W (q1,q2)\<close>
            unfolding handlePair_def case_prod_conv
            by auto
          then have "get_distinguishing_sequence_from_ofsm_tables M q1 q2 \<in> set (foldl handlePair empty (qqs@[qq]))"
            using insert_isin
            by metis 
          then show ?thesis 
            using get_distinguishing_sequence_from_ofsm_tables_distinguishes[OF assms]
            by blast
        qed
      next
        case False
        then have "(q1, q2) \<in> list.set qqs \<or> (q2, q1) \<in> list.set qqs"
          using snoc.prems by auto
        then show ?thesis using snoc W_subset unfolding W_def
          by (meson dual_order.trans list_prefix_subset subsetD)
      qed
    qed
  qed
  ultimately show ?thesis
    unfolding \<open>distinguishing_set_reduced M = foldl handlePair empty pairs\<close>
    by blast
qed


lemma distinguishing_set_reduced_finite :
  "finite_tree (distinguishing_set_reduced M)"
proof -
  define pairs where pairs: "pairs = filter (\<lambda> (x,y) . x \<noteq> y) (list_ordered_pairs (states_as_list M))"
  
  
  define handlePair where "handlePair = (\<lambda> W (q,q') . if contains_distinguishing_trace M W q q'
                                then W
                                else insert W (get_distinguishing_sequence_from_ofsm_tables M q q'))"

  have "distinguishing_set_reduced M = foldl handlePair empty pairs"
    unfolding distinguishing_set_reduced.simps handlePair_def pairs Let_def by metis

  show ?thesis
    unfolding \<open>distinguishing_set_reduced M = foldl handlePair empty pairs\<close>
  proof (induction pairs rule: rev_induct)
    case Nil
    then show ?case using empty_finite_tree by auto
  next
    case (snoc qq qqs)
    define W where "W = foldl handlePair empty qqs"
    have "foldl handlePair empty (qqs@[qq]) = handlePair W qq"
      unfolding W_def by auto 

    have "finite_tree W"
      using snoc W_def by auto
    then show ?case
      unfolding \<open>foldl handlePair empty (qqs@[qq]) = handlePair W qq\<close>
      unfolding handlePair_def
      using insert_finite_tree[of W]
      by (simp add: case_prod_unfold) 
  qed
qed
  


fun add_distinguishing_set :: "('a :: linorder, 'b :: linorder, 'c :: linorder) fsm \<Rightarrow> (('b\<times>'c) list \<times> 'a) \<times> (('b\<times>'c) list \<times> 'a) \<Rightarrow> ('b\<times>'c) prefix_tree \<Rightarrow> ('b\<times>'c) prefix_tree" where
  "add_distinguishing_set M _ t = distinguishing_set M"



lemma add_distinguishing_set_distinguishes :
  assumes "observable M"
  and     "minimal M"
  and     "\<alpha> \<in> L M"
  and     "\<beta> \<in> L M" 
  and     "after_initial M \<alpha> \<noteq> after_initial M \<beta>"   
shows "\<exists> io \<in> set (add_distinguishing_set M ((\<alpha>,after_initial M \<alpha>),(\<beta>,after_initial M \<beta>)) t) \<union> (set (after t \<alpha>) \<inter> set (after t \<beta>)) . distinguishes M (after_initial M \<alpha>) (after_initial M \<beta>) io"
  using distinguishing_set_distinguishes[OF assms(1,2) after_is_state[OF assms(1,3)] after_is_state[OF assms(1,4)] assms(5)]
  by force

lemma add_distinguishing_set_finite : 
  "finite_tree ((add_distinguishing_set M) x t)"
  unfolding add_distinguishing_set.simps distinguishing_set.simps Let_def
  using from_list_finite_tree
  by simp



subsection \<open>Transition Sorting\<close>

definition sort_unverified_transitions_by_state_cover_length :: "('a :: linorder,'b :: linorder,'c :: linorder) fsm \<Rightarrow> ('a,'b,'c) state_cover_assignment \<Rightarrow> ('a,'b,'c) transition list \<Rightarrow> ('a,'b,'c) transition list" where
  "sort_unverified_transitions_by_state_cover_length M V ts = (let
      default_weight = 2 * size M;
      weights = mapping_of (map (\<lambda>t . (t, length (V (t_source t)) + length (V (t_target t)))) ts);
      weight  = (\<lambda>q . case Mapping.lookup weights q of Some w \<Rightarrow> w | None \<Rightarrow> default_weight)
    in mergesort_by_rel (\<lambda> t1 t2 . weight t1 \<le> weight t2) ts)"

lemma sort_unverified_transitions_by_state_cover_length_retains_set :
  "List.set xs = List.set (sort_unverified_transitions_by_state_cover_length M1 (get_state_cover M1) xs)"
  unfolding sort_unverified_transitions_by_state_cover_length_def Let_def
  unfolding set_mergesort_by_rel
  by simp 

end