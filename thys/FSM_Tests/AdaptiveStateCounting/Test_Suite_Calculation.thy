section \<open>Calculating Sufficient Test Suites\<close>

text \<open>This theory describes algorithms to calculate test suites that satisfy the sufficiency
      criterion for a given specification FSM and upper bound m on the number of states in the
      System Under Test.\<close>

theory Test_Suite_Calculation
imports Test_Suite_IO
begin

subsection \<open>Calculating Path Prefixes that are to be Extended With Adaptive Cest Cases\<close>

subsubsection \<open>Calculating Tests along m-Traversal-Paths\<close>

fun prefix_pair_tests :: "'a \<Rightarrow> (('a,'b,'c) traversal_path \<times> ('a set \<times> 'a set)) set \<Rightarrow> ('a \<times> ('a,'b,'c) traversal_path \<times> 'a) set" where
  "prefix_pair_tests q pds 
    = \<Union>{{(q,p1,(target q p2)), (q,p2,(target q p1))} | p1 p2 . 
          \<exists> (p,(rd,dr)) \<in> pds .  
              (p1,p2) \<in> set (prefix_pairs p) \<and> 
              (target q p1) \<in> rd \<and> 
              (target q p2) \<in> rd \<and> 
              (target q p1) \<noteq> (target q p2)}"

lemma prefix_pair_tests_code[code] :
  "prefix_pair_tests q pds = (\<Union>(image (\<lambda> (p,(rd,dr)) . \<Union> (set (map (\<lambda> (p1,p2) . {(q,p1,(target q p2)), (q,p2,(target q p1))}) (filter (\<lambda> (p1,p2) . (target q p1) \<in> rd \<and> (target q p2) \<in> rd \<and> (target q p1) \<noteq> (target q p2)) (prefix_pairs p))))) pds))"
proof -
  have "\<And> tp . tp \<in> prefix_pair_tests q pds \<Longrightarrow> tp \<in> (\<Union>(image (\<lambda> (p,(rd,dr)) . \<Union> (set (map (\<lambda> (p1,p2) . {(q,p1,(target q p2)), (q,p2,(target q p1))}) (filter (\<lambda> (p1,p2) . (target q p1) \<in> rd \<and> (target q p2) \<in> rd \<and> (target q p1) \<noteq> (target q p2)) (prefix_pairs p))))) pds))"
  proof -
    fix tp assume "tp \<in> prefix_pair_tests q pds"
    then obtain tps where "tp \<in> tps"
                    and   "tps \<in> {{(q,p1,(target q p2)), (q,p2,(target q p1))} | p1 p2 . \<exists> (p,(rd,dr)) \<in> pds . (p1,p2) \<in> set (prefix_pairs p) \<and> (target q p1) \<in> rd \<and> (target q p2) \<in> rd \<and> (target q p1) \<noteq> (target q p2)}"
      unfolding prefix_pair_tests.simps
      by (meson UnionE) 
    then obtain p1 p2 where "tps = {(q,p1,(target q p2)), (q,p2,(target q p1))}"
                      and   "\<exists> (p,(rd,dr)) \<in> pds . (p1,p2) \<in> set (prefix_pairs p) \<and> (target q p1) \<in> rd \<and> (target q p2) \<in> rd \<and> (target q p1) \<noteq> (target q p2)"
      unfolding mem_Collect_eq by blast

    then obtain p rd dr where "(p,(rd,dr)) \<in> pds" and "(p1,p2) \<in> set (prefix_pairs p)" and "(target q p1) \<in> rd \<and> (target q p2) \<in> rd \<and> (target q p1) \<noteq> (target q p2)"
      by blast

    have scheme : "\<And> f x xs . x \<in> set xs \<Longrightarrow> f x \<in> set (map f xs)" 
      by auto

    have "(p1,p2) \<in> set (filter (\<lambda>(p1, p2). target q p1 \<in> rd \<and> target q p2 \<in> rd \<and> target q p1 \<noteq> target q p2) (prefix_pairs p))"
      using \<open>(p1,p2) \<in> set (prefix_pairs p)\<close>
            \<open>(target q p1) \<in> rd \<and> (target q p2) \<in> rd \<and> (target q p1) \<noteq> (target q p2)\<close> 
      by auto
    have "{(q,p1,(target q p2)), (q,p2,(target q p1))} \<in> (set (map (\<lambda> (p1,p2) . {(q,p1,(target q p2)), (q,p2,(target q p1))}) (filter (\<lambda> (p1,p2) . (target q p1) \<in> rd \<and> (target q p2) \<in> rd \<and> (target q p1) \<noteq> (target q p2)) (prefix_pairs p))))"
      using scheme[OF \<open>(p1,p2) \<in> set (filter (\<lambda>(p1, p2). target q p1 \<in> rd \<and> target q p2 \<in> rd \<and> target q p1 \<noteq> target q p2) (prefix_pairs p))\<close>, of "(\<lambda> (p1,p2) . {(q,p1,(target q p2)), (q,p2,(target q p1))})"] 
      by simp

    then show "tp \<in> (\<Union>(image (\<lambda> (p,(rd,dr)) . \<Union> (set (map (\<lambda> (p1,p2) . {(q,p1,(target q p2)), (q,p2,(target q p1))}) (filter (\<lambda> (p1,p2) . (target q p1) \<in> rd \<and> (target q p2) \<in> rd \<and> (target q p1) \<noteq> (target q p2)) (prefix_pairs p))))) pds))"
      using \<open>tp \<in> tps\<close> \<open>(p,(rd,dr)) \<in> pds\<close>
      unfolding \<open>tps = {(q,p1,(target q p2)), (q,p2,(target q p1))}\<close> 
      by blast
  qed
  moreover have "\<And> tp . tp \<in> (\<Union>(image (\<lambda> (p,(rd,dr)) . \<Union> (set (map (\<lambda> (p1,p2) . {(q,p1,(target q p2)), (q,p2,(target q p1))}) (filter (\<lambda> (p1,p2) . (target q p1) \<in> rd \<and> (target q p2) \<in> rd \<and> (target q p1) \<noteq> (target q p2)) (prefix_pairs p))))) pds))
                        \<Longrightarrow> tp \<in> prefix_pair_tests q pds"
  proof -
    fix tp assume "tp \<in> (\<Union>(image (\<lambda> (p,(rd,dr)) . \<Union> (set (map (\<lambda> (p1,p2) . {(q,p1,(target q p2)), (q,p2,(target q p1))}) (filter (\<lambda> (p1,p2) . (target q p1) \<in> rd \<and> (target q p2) \<in> rd \<and> (target q p1) \<noteq> (target q p2)) (prefix_pairs p))))) pds))"
    then obtain prddr where "prddr \<in> pds"
                        and "tp \<in> (\<lambda> (p,(rd,dr)) . \<Union> (set (map (\<lambda> (p1,p2) . {(q,p1,(target q p2)), (q,p2,(target q p1))}) (filter (\<lambda> (p1,p2) . (target q p1) \<in> rd \<and> (target q p2) \<in> rd \<and> (target q p1) \<noteq> (target q p2)) (prefix_pairs p))))) prddr"
      by blast
    then obtain p rd dr where "prddr = (p,(rd,dr))" by auto

    then have "tp \<in> \<Union> (set (map (\<lambda> (p1,p2) . {(q,p1,(target q p2)), (q,p2,(target q p1))}) (filter (\<lambda> (p1,p2) . (target q p1) \<in> rd \<and> (target q p2) \<in> rd \<and> (target q p1) \<noteq> (target q p2)) (prefix_pairs p))))"
      using \<open>tp \<in> (\<lambda> (p,(rd,dr)) . \<Union> (set (map (\<lambda> (p1,p2) . {(q,p1,(target q p2)), (q,p2,(target q p1))}) (filter (\<lambda> (p1,p2) . (target q p1) \<in> rd \<and> (target q p2) \<in> rd \<and> (target q p1) \<noteq> (target q p2)) (prefix_pairs p))))) prddr\<close> by auto

    then obtain p1 p2 where "(p1,p2) \<in> set (filter (\<lambda> (p1,p2) . (target q p1) \<in> rd \<and> (target q p2) \<in> rd \<and> (target q p1) \<noteq> (target q p2)) (prefix_pairs p))"
                      and   "tp \<in> {(q,p1,(target q p2)), (q,p2,(target q p1))}" 
      by auto
    then have "(target q p1) \<in> rd \<and> (target q p2) \<in> rd \<and> (target q p1) \<noteq> (target q p2)" 
         and  "(p1,p2) \<in> set (prefix_pairs p)"
      by auto

    then show "tp \<in> prefix_pair_tests q pds"
      using \<open>prddr \<in> pds\<close> \<open>tp \<in> {(q,p1,(target q p2)), (q,p2,(target q p1))}\<close>
      unfolding prefix_pair_tests.simps  \<open>prddr = (p,(rd,dr))\<close> 
      by blast
  qed
  ultimately show ?thesis 
    by blast
qed





subsubsection \<open>Calculating Tests between Preambles\<close>


fun preamble_prefix_tests' :: "'a \<Rightarrow> (('a,'b,'c) traversal_path \<times> ('a set \<times> 'a set)) list \<Rightarrow> 'a list \<Rightarrow> ('a \<times> ('a,'b,'c) traversal_path \<times> 'a) list" where
  "preamble_prefix_tests' q pds drs = 
    concat (map (\<lambda>((p,(rd,dr)),q2,p1) . [(q,p1,q2), (q2,[],(target q p1))]) 
                (filter (\<lambda>((p,(rd,dr)),q2,p1) . (target q p1) \<in> rd \<and> q2 \<in> rd \<and> (target q p1) \<noteq> q2) 
                        (concat (map (\<lambda>((p,(rd,dr)),q2) . map (\<lambda>p1 . ((p,(rd,dr)),q2,p1)) (prefixes p)) (List.product pds drs)))))"


definition preamble_prefix_tests :: "'a \<Rightarrow> (('a,'b,'c) traversal_path \<times> ('a set \<times> 'a set)) set \<Rightarrow> 'a set \<Rightarrow> ('a \<times> ('a,'b,'c) traversal_path \<times> 'a) set" where
  "preamble_prefix_tests q pds drs = \<Union>{{(q,p1,q2), (q2,[],(target q p1))} | p1 q2 . \<exists> (p,(rd,dr)) \<in> pds . q2 \<in> drs \<and> (\<exists> p2 . p = p1@p2) \<and> (target q p1) \<in> rd \<and> q2 \<in> rd \<and> (target q p1) \<noteq> q2}"

lemma preamble_prefix_tests_code[code] :
  "preamble_prefix_tests q pds drs = (\<Union>(image (\<lambda> (p,(rd,dr)) . \<Union>(image (\<lambda> (p1,q2) . {(q,p1,q2), (q2,[],(target q p1))}) (Set.filter (\<lambda> (p1,q2) . (target q p1) \<in> rd \<and> q2 \<in> rd \<and> (target q p1) \<noteq> q2) ((set (prefixes p)) \<times> drs)))) pds))"
proof -
  have "\<And> pp . pp \<in> preamble_prefix_tests q pds drs \<Longrightarrow> pp \<in> (\<Union>(image (\<lambda> (p,(rd,dr)) . \<Union>(image (\<lambda> (p1,q2) . {(q,p1,q2), (q2,[],(target q p1))}) (Set.filter (\<lambda> (p1,q2) . (target q p1) \<in> rd \<and> q2 \<in> rd \<and> (target q p1) \<noteq> q2) ((set (prefixes p)) \<times> drs)))) pds))"  
  proof -
    fix pp assume "pp \<in> preamble_prefix_tests q pds drs"
    then obtain p1 q2 where "pp \<in> {(q,p1,q2), (q2,[],(target q p1))}"
                      and   "\<exists> (p,(rd,dr)) \<in> pds . q2 \<in> drs \<and> (\<exists> p2 . p = p1@p2) \<and> (target q p1) \<in> rd \<and> q2 \<in> rd \<and> (target q p1) \<noteq> q2"
      unfolding preamble_prefix_tests_def by blast
    then obtain p rd dr where "(p,(rd,dr)) \<in> pds" and "q2 \<in> drs" and "(\<exists> p2 . p = p1@p2)" and "(target q p1) \<in> rd \<and> q2 \<in> rd \<and> (target q p1) \<noteq> q2"
      by auto

    then have "(p1,q2) \<in> (Set.filter (\<lambda> (p1,q2) . (target q p1) \<in> rd \<and> q2 \<in> rd \<and> (target q p1) \<noteq> q2) ((set (prefixes p)) \<times> drs))"
      unfolding prefixes_set by force
    then show "pp \<in> (\<Union>(image (\<lambda> (p,(rd,dr)) . \<Union>(image (\<lambda> (p1,q2) . {(q,p1,q2), (q2,[],(target q p1))}) (Set.filter (\<lambda> (p1,q2) . (target q p1) \<in> rd \<and> q2 \<in> rd \<and> (target q p1) \<noteq> q2) ((set (prefixes p)) \<times> drs)))) pds))"
      using \<open>(p,(rd,dr)) \<in> pds\<close>
            \<open>pp \<in> {(q,p1,q2), (q2,[],(target q p1))}\<close> by blast
  qed
  moreover have "\<And> pp . pp \<in> (\<Union>(image (\<lambda> (p,(rd,dr)) . \<Union>(image (\<lambda> (p1,q2) . {(q,p1,q2), (q2,[],(target q p1))}) (Set.filter (\<lambda> (p1,q2) . (target q p1) \<in> rd \<and> q2 \<in> rd \<and> (target q p1) \<noteq> q2) ((set (prefixes p)) \<times> drs)))) pds))
                         \<Longrightarrow> pp \<in> preamble_prefix_tests q pds drs"
  proof -
    fix pp assume "pp \<in> (\<Union>(image (\<lambda> (p,(rd,dr)) . \<Union>(image (\<lambda> (p1,q2) . {(q,p1,q2), (q2,[],(target q p1))}) (Set.filter (\<lambda> (p1,q2) . (target q p1) \<in> rd \<and> q2 \<in> rd \<and> (target q p1) \<noteq> q2) ((set (prefixes p)) \<times> drs)))) pds))"
    then obtain prddr where "prddr \<in> pds"
                      and   "pp \<in> (\<lambda> (p,(rd,dr)) . \<Union>(image (\<lambda> (p1,q2) . {(q,p1,q2), (q2,[],(target q p1))}) (Set.filter (\<lambda> (p1,q2) . (target q p1) \<in> rd \<and> q2 \<in> rd \<and> (target q p1) \<noteq> q2) ((set (prefixes p)) \<times> drs)))) prddr"
      by blast

    obtain p rd dr where "prddr = (p,(rd,dr))"
      using prod_cases3 by blast 

    obtain p1 q2 where "(p1,q2) \<in> (Set.filter (\<lambda> (p1,q2) . (target q p1) \<in> rd \<and> q2 \<in> rd \<and> (target q p1) \<noteq> q2) ((set (prefixes p)) \<times> drs))"
                 and   "pp \<in> {(q,p1,q2), (q2,[],(target q p1))}"
      using \<open>pp \<in> (\<lambda> (p,(rd,dr)) . \<Union>(image (\<lambda> (p1,q2) . {(q,p1,q2), (q2,[],(target q p1))}) (Set.filter (\<lambda> (p1,q2) . (target q p1) \<in> rd \<and> q2 \<in> rd \<and> (target q p1) \<noteq> q2) ((set (prefixes p)) \<times> drs)))) prddr\<close>
      unfolding \<open>prddr = (p,(rd,dr))\<close> 
      by blast

    have "q2 \<in> drs \<and> (\<exists> p2 . p = p1@p2) \<and> (target q p1) \<in> rd \<and> q2 \<in> rd \<and> (target q p1) \<noteq> q2"
      using \<open>(p1,q2) \<in> (Set.filter (\<lambda> (p1,q2) . (target q p1) \<in> rd \<and> q2 \<in> rd \<and> (target q p1) \<noteq> q2) ((set (prefixes p)) \<times> drs))\<close>
      unfolding prefixes_set 
      by auto
    then have "\<exists>(p, rd, dr)\<in>pds. q2 \<in> drs \<and> (\<exists>p2. p = p1 @ p2) \<and> target q p1 \<in> rd \<and> q2 \<in> rd \<and> target q p1 \<noteq> q2"
      using \<open>prddr \<in> pds\<close> \<open>prddr = (p,(rd,dr))\<close> 
      by blast
    then have *: "{(q,p1,q2), (q2,[],(target q p1))} \<in> {{(q, p1, q2), (q2, [], target q p1)} |p1 q2.
             \<exists>(p, rd, dr)\<in>pds. q2 \<in> drs \<and> (\<exists>p2. p = p1 @ p2) \<and> target q p1 \<in> rd \<and> q2 \<in> rd \<and> target q p1 \<noteq> q2}" by blast

    show "pp \<in> preamble_prefix_tests q pds drs"
      using UnionI[OF * \<open>pp \<in> {(q,p1,q2), (q2,[],(target q p1))}\<close>]
      unfolding preamble_prefix_tests_def by assumption
  qed
  ultimately show ?thesis by blast
qed



subsubsection "Calculating Tests between m-Traversal-Paths Prefixes and Preambles"

fun preamble_pair_tests :: "'a set set \<Rightarrow> ('a \<times> 'a) set \<Rightarrow> ('a \<times> ('a,'b,'c) traversal_path \<times> 'a) set" where
  "preamble_pair_tests drss rds = (\<Union> drs \<in> drss . (\<lambda> (q1,q2) . (q1,[],q2)) ` ((drs \<times> drs) \<inter> rds))"





subsection \<open>Calculating a Test Suite\<close>


definition calculate_test_paths ::
  "('a,'b,'c) fsm
  \<Rightarrow> nat
  \<Rightarrow> 'a set
  \<Rightarrow> ('a \<times> 'a) set
  \<Rightarrow> ('a set \<times> 'a set) list
  \<Rightarrow> (('a \<Rightarrow> ('a,'b,'c) traversal_path set) \<times> (('a \<times> ('a,'b,'c) traversal_path) \<Rightarrow> 'a set))" 
  where
  "calculate_test_paths M m d_reachable_states r_distinguishable_pairs repetition_sets =
    (let
         paths_with_witnesses 
              = (image (\<lambda> q . (q,m_traversal_paths_with_witness M q repetition_sets m)) d_reachable_states);
         get_paths                        
              = m2f (set_as_map paths_with_witnesses);
         PrefixPairTests                    
              = \<Union> q \<in> d_reachable_states . \<Union> mrsps \<in> get_paths q . prefix_pair_tests q mrsps;
         PreamblePrefixTests
              = \<Union> q \<in> d_reachable_states . \<Union> mrsps \<in> get_paths q . preamble_prefix_tests q mrsps d_reachable_states;
         PreamblePairTests
              = preamble_pair_tests (\<Union> (q,pw) \<in> paths_with_witnesses . ((\<lambda> (p,(rd,dr)) . dr) ` pw)) r_distinguishable_pairs;
         tests
              = PrefixPairTests \<union> PreamblePrefixTests \<union> PreamblePairTests; 
         tps'  
              = m2f_by \<Union> (set_as_map (image (\<lambda> (q,p) . (q, image fst p)) paths_with_witnesses));
         tps''  
              = m2f (set_as_map (image (\<lambda> (q,p,q') . (q,p)) tests));
         tps  
              = (\<lambda> q . tps' q \<union> tps'' q);
         rd_targets 
              = m2f (set_as_map (image (\<lambda> (q,p,q') . ((q,p),q')) tests))    
  in 
    ( tps, rd_targets ))"


definition combine_test_suite ::
  "('a,'b,'c) fsm
  \<Rightarrow> nat
  \<Rightarrow> ('a \<times> ('a,'b,'c) preamble) set
  \<Rightarrow> (('a \<times> 'a) \<times> (('d,'b,'c) separator \<times> 'd \<times> 'd)) set
  \<Rightarrow> ('a set \<times> 'a set) list
  \<Rightarrow> ('a,'b,'c,'d) test_suite" 
  where
  "combine_test_suite M m states_with_preambles pairs_with_separators repetition_sets =
    (let drs = image fst states_with_preambles;
        rds = image fst pairs_with_separators;
        tps_and_targets = calculate_test_paths M m drs rds repetition_sets;
        atcs = m2f (set_as_map pairs_with_separators) 
in (Test_Suite states_with_preambles (fst tps_and_targets) (snd tps_and_targets) atcs))"




definition calculate_test_suite_for_repetition_sets :: 
  "('a::linorder,'b::linorder,'c) fsm \<Rightarrow> nat \<Rightarrow> ('a set \<times> 'a set) list \<Rightarrow> ('a,'b,'c, ('a \<times> 'a) + 'a) test_suite" 
  where
  "calculate_test_suite_for_repetition_sets M m repetition_sets = 
    (let
         states_with_preambles = d_reachable_states_with_preambles M;
         pairs_with_separators = image (\<lambda>((q1,q2),A) . ((q1,q2),A,Inr q1,Inr q2)) (r_distinguishable_state_pairs_with_separators M)
  in combine_test_suite M m states_with_preambles pairs_with_separators repetition_sets)"




subsection \<open>Sufficiency of the Calculated Test Suite\<close>

lemma calculate_test_suite_for_repetition_sets_sufficient_and_finite :
  fixes M :: "('a::linorder,'b::linorder,'c) fsm"
  assumes "observable M"
  and     "completely_specified M"
  and     "inputs M \<noteq> {}"
  and     "\<And>q. q \<in> FSM.states M \<Longrightarrow> \<exists>d\<in>set RepSets. q \<in> fst d"
  and     "\<And>d. d \<in> set RepSets \<Longrightarrow> fst d \<subseteq> states M \<and> (snd d = fst d \<inter> fst ` d_reachable_states_with_preambles M)" 
  and     "\<And> q1 q2 d. d \<in> set RepSets \<Longrightarrow> q1\<in>fst d \<Longrightarrow> q2\<in>fst d \<Longrightarrow> q1 \<noteq> q2 \<Longrightarrow> (q1, q2) \<in> fst ` r_distinguishable_state_pairs_with_separators M"
shows "implies_completeness (calculate_test_suite_for_repetition_sets M m RepSets) M m"
and   "is_finite_test_suite (calculate_test_suite_for_repetition_sets M m RepSets)"
proof -
  obtain states_with_preambles tps rd_targets atcs where "calculate_test_suite_for_repetition_sets M m RepSets 
                                                          = Test_Suite states_with_preambles tps rd_targets atcs"
    using test_suite.exhaust by blast

  have "\<And> a b c d . Test_Suite states_with_preambles tps rd_targets atcs = Test_Suite a b c d \<Longrightarrow> tps = b"
    by blast

  have states_with_preambles_def : "states_with_preambles = d_reachable_states_with_preambles M"
    
  
  and tps_def                   : "tps = (\<lambda>q. (m2f_by \<Union> (set_as_map ((\<lambda>(q, p). (q, fst ` p)) ` (\<lambda>q. (q, m_traversal_paths_with_witness M q RepSets m)) ` fst ` d_reachable_states_with_preambles M))) q
                                            \<union> (m2f (set_as_map ((\<lambda>(q, p, q'). (q, p)) `
                                                ((\<Union>q\<in>fst ` d_reachable_states_with_preambles M. \<Union> (prefix_pair_tests q ` (m2f (set_as_map ((\<lambda>q. (q, m_traversal_paths_with_witness M q RepSets m)) ` fst ` d_reachable_states_with_preambles M)) q))) 
                                                \<union> (\<Union>q\<in>fst ` d_reachable_states_with_preambles M. \<Union>mrsps\<in> m2f (set_as_map ((\<lambda>q. (q, m_traversal_paths_with_witness M q RepSets m)) ` fst ` d_reachable_states_with_preambles M)) q . preamble_prefix_tests q mrsps (fst ` d_reachable_states_with_preambles M)) 
                                                \<union> preamble_pair_tests (\<Union>(q, y)\<in>(\<lambda>q. (q, m_traversal_paths_with_witness M q RepSets m)) ` fst ` d_reachable_states_with_preambles M. (\<lambda>(p, rd, dr). dr) ` y) (fst ` (\<lambda>((q1, q2), A). ((q1, q2), A, Inr q1 :: 'a \<times> 'a + 'a, Inr q2 :: 'a \<times> 'a + 'a)) ` r_distinguishable_state_pairs_with_separators M))))) q)"
  and rd_targets_def            : "rd_targets = m2f (set_as_map
                                              ((\<lambda>(q, p, y). ((q, p), y)) `
                                               ((\<Union>q\<in>fst ` d_reachable_states_with_preambles M. \<Union> (prefix_pair_tests q ` (m2f (set_as_map ((\<lambda>q. (q, m_traversal_paths_with_witness M q RepSets m)) ` fst ` d_reachable_states_with_preambles M)) q))) 
                                               \<union> (\<Union>q\<in>fst ` d_reachable_states_with_preambles M. \<Union>mrsps\<in> m2f (set_as_map ((\<lambda>q. (q, m_traversal_paths_with_witness M q RepSets m)) ` fst ` d_reachable_states_with_preambles M)) q . preamble_prefix_tests q mrsps (fst ` d_reachable_states_with_preambles M)) 
                                               \<union> preamble_pair_tests (\<Union>(q, y)\<in>(\<lambda>q. (q, m_traversal_paths_with_witness M q RepSets m)) ` fst ` d_reachable_states_with_preambles M. (\<lambda>(p, rd, dr). dr) ` y) (fst ` (\<lambda>((q1, q2), A). ((q1, q2), A, Inr q1 :: 'a \<times> 'a + 'a, Inr q2 :: 'a \<times> 'a + 'a)) ` r_distinguishable_state_pairs_with_separators M))))"
  and  atcs_def                 : "atcs = m2f (set_as_map ((\<lambda>((q1, q2), A). ((q1, q2), A, Inr q1, Inr q2)) ` r_distinguishable_state_pairs_with_separators M))"
    using \<open>calculate_test_suite_for_repetition_sets M m RepSets = Test_Suite states_with_preambles tps rd_targets atcs\<close>[symmetric]
    unfolding calculate_test_suite_for_repetition_sets_def combine_test_suite_def Let_def calculate_test_paths_def fst_conv snd_conv by force+
  

  have tps_alt_def: "\<And> q . q \<in> fst ` d_reachable_states_with_preambles M \<Longrightarrow> 
          tps q = (fst ` m_traversal_paths_with_witness M q RepSets m) \<union> 
                  {z. (q, z)
                    \<in> (\<lambda>(q, p, q'). (q, p)) `
                       ((prefix_pair_tests q (m_traversal_paths_with_witness M q RepSets m)) \<union>
                        (\<Union>q\<in>fst ` d_reachable_states_with_preambles M.
                            \<Union>mrsps\<in>{m_traversal_paths_with_witness M q RepSets m}.
                               preamble_prefix_tests q mrsps (fst ` d_reachable_states_with_preambles M)) \<union>
                        preamble_pair_tests (\<Union>(q, y)\<in>(\<lambda>q. (q, m_traversal_paths_with_witness M q RepSets m)) ` fst ` d_reachable_states_with_preambles M. (\<lambda>(p, rd, dr). dr) ` y) (fst ` (\<lambda>((q1, q2), A). ((q1, q2), A, Inr q1 :: 'a \<times> 'a + 'a, Inr q2 :: 'a \<times> 'a + 'a)) ` r_distinguishable_state_pairs_with_separators M))}"
  and rd_targets_alt_def: "\<And> q p . q \<in> fst ` d_reachable_states_with_preambles M \<Longrightarrow> 
          rd_targets (q,p) = {z. ((q, p), z)
                   \<in> (\<lambda>(q, p, y). ((q, p), y)) `
                      ((prefix_pair_tests q (m_traversal_paths_with_witness M q RepSets m)) \<union>
                       (\<Union>q\<in>fst ` d_reachable_states_with_preambles M.
                           \<Union>mrsps\<in>{m_traversal_paths_with_witness M q RepSets m}.
                              preamble_prefix_tests q mrsps (fst ` d_reachable_states_with_preambles M)) \<union>
                       preamble_pair_tests (\<Union>(q, y)\<in>(\<lambda>q. (q, m_traversal_paths_with_witness M q RepSets m)) ` fst ` d_reachable_states_with_preambles M. (\<lambda>(p, rd, dr). dr) ` y) (fst ` (\<lambda>((q1, q2), A). ((q1, q2), A, Inr q1 :: 'a \<times> 'a + 'a, Inr q2 :: 'a \<times> 'a + 'a)) ` r_distinguishable_state_pairs_with_separators M))}"
  proof -
    fix q p assume "q \<in> fst ` d_reachable_states_with_preambles M"

  

    have scheme0 : "(case set_as_map
             ((\<lambda>(q, p). (q, fst ` p)) `
              (\<lambda>q. (q, m_traversal_paths_with_witness M q RepSets m)) `
              fst ` d_reachable_states_with_preambles M)
             q of
       None \<Rightarrow> \<Union> {} | Some x \<Rightarrow> \<Union> x) = image fst (m_traversal_paths_with_witness M q RepSets m)"
    proof -
      have *: "((\<lambda>(q, p). (q, fst ` p)) `
              (\<lambda>q. (q, m_traversal_paths_with_witness M q RepSets m)) `
              fst ` d_reachable_states_with_preambles M)
               = (\<lambda> q . (q , image fst (m_traversal_paths_with_witness M q RepSets m))) ` (fst ` d_reachable_states_with_preambles M)"
        by force
      have **: "\<And> f q xs . (case set_as_map
                              ((\<lambda>q. (q, f q)) ` xs)
                              q of
                        None \<Rightarrow> \<Union> {} | Some xs \<Rightarrow> \<Union> xs) = (if q \<in> xs then \<Union> {f q} else \<Union> {})" 
      unfolding set_as_map_def by auto

      show ?thesis
        unfolding * **
        using \<open>q \<in> fst ` d_reachable_states_with_preambles M\<close>
        by auto
    qed
    
    
    have scheme1 : "\<And> f q xs . (case set_as_map
                              ((\<lambda>q. (q, f q)) ` xs)
                              q of
                        None \<Rightarrow> {} | Some xs \<Rightarrow> xs) = (if q \<in> xs then {f q} else {})" 
      unfolding set_as_map_def by auto        


    have scheme2: "(\<Union>q\<in>fst ` d_reachable_states_with_preambles M.
                   \<Union> (prefix_pair_tests q `
                       (if q \<in> fst ` d_reachable_states_with_preambles M
                        then {m_traversal_paths_with_witness M q RepSets m} else {})))
      = (\<Union>q\<in>fst ` d_reachable_states_with_preambles M. (\<Union> (prefix_pair_tests q ` {m_traversal_paths_with_witness M q RepSets m})))"
      unfolding set_as_map_def by auto


    have scheme3: "(\<Union>q\<in>fst ` d_reachable_states_with_preambles M.
                   \<Union>mrsps\<in>if q \<in> fst ` d_reachable_states_with_preambles M
                           then {m_traversal_paths_with_witness M q RepSets m} else {}.
                      preamble_prefix_tests q mrsps (fst ` d_reachable_states_with_preambles M))
      = (\<Union>q\<in>fst ` d_reachable_states_with_preambles M. (\<Union>mrsps\<in>{m_traversal_paths_with_witness M q RepSets m} . preamble_prefix_tests q mrsps (fst ` d_reachable_states_with_preambles M)))"
      unfolding set_as_map_def by auto

    have scheme4 : "(fst ` (\<lambda>((q1, q2), A). ((q1, q2), A, Inr q1, Inr q2)) ` r_distinguishable_state_pairs_with_separators M)
                    = image fst (r_distinguishable_state_pairs_with_separators M)" 
      by force

    have *:"tps q = (fst ` m_traversal_paths_with_witness M q RepSets m) \<union> 
                  {z. (q, z)
                    \<in> (\<lambda>(q, p, q'). (q, p)) `
                       ((\<Union>q\<in>fst ` d_reachable_states_with_preambles M.
                            \<Union> (prefix_pair_tests q ` {m_traversal_paths_with_witness M q RepSets m})) \<union>
                        (\<Union>q\<in>fst ` d_reachable_states_with_preambles M.
                            \<Union>mrsps\<in>{m_traversal_paths_with_witness M q RepSets m}.
                               preamble_prefix_tests q mrsps (fst ` d_reachable_states_with_preambles M)) \<union>
                        preamble_pair_tests (\<Union>(q, y)\<in>(\<lambda>q. (q, m_traversal_paths_with_witness M q RepSets m)) ` fst ` d_reachable_states_with_preambles M. (\<lambda>(p, rd, dr). dr) ` y) (fst ` (\<lambda>((q1, q2), A). ((q1, q2), A, Inr q1 :: 'a \<times> 'a + 'a, Inr q2 :: 'a \<times> 'a + 'a)) ` r_distinguishable_state_pairs_with_separators M))}"
      unfolding tps_def 
      unfolding scheme0 scheme1 scheme2 scheme3 scheme4
      unfolding set_as_map_def
      by auto

    have **: "{z. (q, z)
                    \<in> (\<lambda>(q, p, q'). (q, p)) `
                       ((\<Union>q\<in>fst ` d_reachable_states_with_preambles M.
                            \<Union> (prefix_pair_tests q ` {m_traversal_paths_with_witness M q RepSets m})) \<union>
                        (\<Union>q\<in>fst ` d_reachable_states_with_preambles M.
                            \<Union>mrsps\<in>{m_traversal_paths_with_witness M q RepSets m}.
                               preamble_prefix_tests q mrsps (fst ` d_reachable_states_with_preambles M)) \<union>
                        preamble_pair_tests (\<Union>(q, y)\<in>(\<lambda>q. (q, m_traversal_paths_with_witness M q RepSets m)) ` fst ` d_reachable_states_with_preambles M. (\<lambda>(p, rd, dr). dr) ` y) (fst ` (\<lambda>((q1, q2), A). ((q1, q2), A, Inr q1 :: 'a \<times> 'a + 'a, Inr q2 :: 'a \<times> 'a + 'a)) ` r_distinguishable_state_pairs_with_separators M))}
          = {z. (q, z)
                    \<in> (\<lambda>(q, p, q'). (q, p)) `
                       ((prefix_pair_tests q (m_traversal_paths_with_witness M q RepSets m)) \<union>
                        (\<Union>q\<in>fst ` d_reachable_states_with_preambles M.
                            \<Union>mrsps\<in>{m_traversal_paths_with_witness M q RepSets m}.
                               preamble_prefix_tests q mrsps (fst ` d_reachable_states_with_preambles M)) \<union>
                        preamble_pair_tests (\<Union>(q, y)\<in>(\<lambda>q. (q, m_traversal_paths_with_witness M q RepSets m)) ` fst ` d_reachable_states_with_preambles M. (\<lambda>(p, rd, dr). dr) ` y) (fst ` (\<lambda>((q1, q2), A). ((q1, q2), A, Inr q1 :: 'a \<times> 'a + 'a, Inr q2 :: 'a \<times> 'a + 'a)) ` r_distinguishable_state_pairs_with_separators M))}" 
      (is "{z. (q, z) \<in> ?S1} = {z. (q, z) \<in> ?S2}")
    proof -
      have "\<And> z . (q, z) \<in> ?S1 \<Longrightarrow> (q, z) \<in> ?S2"
      proof -
        fix z assume "(q, z) \<in> ?S1"
        then consider "(q, z) \<in> (\<lambda>(q, p, q'). (q, p)) ` (\<Union>q\<in>fst ` d_reachable_states_with_preambles M.
                            \<Union> (prefix_pair_tests q ` {m_traversal_paths_with_witness M q RepSets m}))"
                    | "(q,z) \<in> (\<lambda>(q, p, q'). (q, p)) `  (\<Union>q\<in>fst ` d_reachable_states_with_preambles M.
                            \<Union>mrsps\<in>{m_traversal_paths_with_witness M q RepSets m}.
                               preamble_prefix_tests q mrsps (fst ` d_reachable_states_with_preambles M))"
                    | "(q,z) \<in> (\<lambda>(q, p, q'). (q, p)) ` (preamble_pair_tests (\<Union>(q, y)\<in>(\<lambda>q. (q, m_traversal_paths_with_witness M q RepSets m)) ` fst ` d_reachable_states_with_preambles M. (\<lambda>(p, rd, dr). dr) ` y) (fst ` (\<lambda>((q1, q2), A). ((q1, q2), A, Inr q1 :: 'a \<times> 'a + 'a, Inr q2 :: 'a \<times> 'a + 'a)) ` r_distinguishable_state_pairs_with_separators M))"
          by blast
        then show "(q, z) \<in> ?S2" proof cases
          case 1
          have scheme: "\<And> f y xs . y \<in> image f xs \<Longrightarrow> \<exists> x . x \<in> xs \<and> f x = y" by auto

          obtain qzq where "qzq \<in> (\<Union>q\<in>fst ` d_reachable_states_with_preambles M. \<Union> (prefix_pair_tests q ` {m_traversal_paths_with_witness M q RepSets m}))"
                     and   "(\<lambda>(q, p, q'). (q, p)) qzq = (q,z)"
            using scheme[OF 1] by blast
          then obtain q' where "q'\<in>fst ` d_reachable_states_with_preambles M"
                         and   "qzq \<in> \<Union> (prefix_pair_tests q' ` {m_traversal_paths_with_witness M q' RepSets m})"
            by blast
          then have "fst qzq = q'"
            by auto
          then have "q' = q"
            using \<open>(\<lambda>(q, p, q'). (q, p)) qzq = (q,z)\<close>
            by (simp add: prod.case_eq_if) 
          then have "qzq \<in> \<Union> (prefix_pair_tests q ` {m_traversal_paths_with_witness M q RepSets m})"
            using \<open>qzq \<in> \<Union> (prefix_pair_tests q' ` {m_traversal_paths_with_witness M q' RepSets m})\<close> 
            by blast
          then have "(\<lambda>(q, p, q'). (q, p)) qzq \<in> ?S2"
            by auto
          then show ?thesis 
            unfolding \<open>(\<lambda>(q, p, q'). (q, p)) qzq = (q,z)\<close> 
            by assumption
        next
          case 2 
          then show ?thesis by blast
        next
          case 3
          then show ?thesis by blast
        qed
      qed
      moreover have "\<And> z . (q, z) \<in> ?S2 \<Longrightarrow> (q, z) \<in> ?S1"
        using \<open>q \<in> fst ` d_reachable_states_with_preambles M\<close> by blast
      ultimately show ?thesis
        by meson
    qed

    show "tps q = (fst ` m_traversal_paths_with_witness M q RepSets m) \<union> 
                  {z. (q, z)
                    \<in> (\<lambda>(q, p, q'). (q, p)) `
                       ((prefix_pair_tests q (m_traversal_paths_with_witness M q RepSets m)) \<union>
                        (\<Union>q\<in>fst ` d_reachable_states_with_preambles M.
                            \<Union>mrsps\<in>{m_traversal_paths_with_witness M q RepSets m}.
                               preamble_prefix_tests q mrsps (fst ` d_reachable_states_with_preambles M)) \<union>
                        preamble_pair_tests (\<Union>(q, y)\<in>(\<lambda>q. (q, m_traversal_paths_with_witness M q RepSets m)) ` fst ` d_reachable_states_with_preambles M. (\<lambda>(p, rd, dr). dr) ` y) (fst ` (\<lambda>((q1, q2), A). ((q1, q2), A, Inr q1 :: 'a \<times> 'a + 'a, Inr q2 :: 'a \<times> 'a + 'a)) ` r_distinguishable_state_pairs_with_separators M))}"
     using * unfolding ** by assumption

    have ***: "rd_targets (q,p) = {z. ((q, p), z)
                   \<in> (\<lambda>(q, p, y). ((q, p), y)) `
                      ((\<Union>q\<in>fst ` d_reachable_states_with_preambles M.
                           \<Union> (prefix_pair_tests q ` {m_traversal_paths_with_witness M q RepSets m})) \<union>
                       (\<Union>q\<in>fst ` d_reachable_states_with_preambles M.
                           \<Union>mrsps\<in>{m_traversal_paths_with_witness M q RepSets m}.
                              preamble_prefix_tests q mrsps (fst ` d_reachable_states_with_preambles M)) \<union>
                       preamble_pair_tests (\<Union>(q, y)\<in>(\<lambda>q. (q, m_traversal_paths_with_witness M q RepSets m)) ` fst ` d_reachable_states_with_preambles M. (\<lambda>(p, rd, dr). dr) ` y) (fst ` (\<lambda>((q1, q2), A). ((q1, q2), A, Inr q1 :: 'a \<times> 'a + 'a, Inr q2 :: 'a \<times> 'a + 'a)) ` r_distinguishable_state_pairs_with_separators M))}"
      unfolding rd_targets_def
      unfolding scheme1 scheme2 scheme3 scheme4
      unfolding set_as_map_def
      by auto


    have ****: "{z. ((q, p), z)
                   \<in> (\<lambda>(q, p, y). ((q, p), y)) `
                      ((\<Union>q\<in>fst ` d_reachable_states_with_preambles M.
                           \<Union> (prefix_pair_tests q ` {m_traversal_paths_with_witness M q RepSets m})) \<union>
                       (\<Union>q\<in>fst ` d_reachable_states_with_preambles M.
                           \<Union>mrsps\<in>{m_traversal_paths_with_witness M q RepSets m}.
                              preamble_prefix_tests q mrsps (fst ` d_reachable_states_with_preambles M)) \<union>
                       preamble_pair_tests (\<Union>(q, y)\<in>(\<lambda>q. (q, m_traversal_paths_with_witness M q RepSets m)) ` fst ` d_reachable_states_with_preambles M. (\<lambda>(p, rd, dr). dr) ` y) (fst ` (\<lambda>((q1, q2), A). ((q1, q2), A, Inr q1 :: 'a \<times> 'a + 'a, Inr q2 :: 'a \<times> 'a + 'a)) ` r_distinguishable_state_pairs_with_separators M))}
          = {z. ((q, p), z)
                   \<in> (\<lambda>(q, p, y). ((q, p), y)) `
                      ((prefix_pair_tests q (m_traversal_paths_with_witness M q RepSets m)) \<union>
                       (\<Union>q\<in>fst ` d_reachable_states_with_preambles M.
                           \<Union>mrsps\<in>{m_traversal_paths_with_witness M q RepSets m}.
                              preamble_prefix_tests q mrsps (fst ` d_reachable_states_with_preambles M)) \<union>
                       preamble_pair_tests (\<Union>(q, y)\<in>(\<lambda>q. (q, m_traversal_paths_with_witness M q RepSets m)) ` fst ` d_reachable_states_with_preambles M. (\<lambda>(p, rd, dr). dr) ` y) (fst ` (\<lambda>((q1, q2), A). ((q1, q2), A, Inr q1 :: 'a \<times> 'a + 'a, Inr q2 :: 'a \<times> 'a + 'a)) ` r_distinguishable_state_pairs_with_separators M))}" 
      (is "{z. ((q, p), z) \<in> ?S1} = {z. ((q, p), z) \<in> ?S2}")
    proof -
      have "\<And> z . ((q, p), z) \<in> ?S1 \<Longrightarrow> ((q, p), z) \<in> ?S2"
      proof -
        fix z assume "((q, p), z) \<in> ?S1"
        then consider "((q, p), z) \<in> (\<lambda>(q, p, y). ((q, p), y)) ` (\<Union>q\<in>fst ` d_reachable_states_with_preambles M.
                            \<Union> (prefix_pair_tests q ` {m_traversal_paths_with_witness M q RepSets m}))"
                    | "((q, p), z) \<in> (\<lambda>(q, p, y). ((q, p), y)) `  (\<Union>q\<in>fst ` d_reachable_states_with_preambles M.
                            \<Union>mrsps\<in>{m_traversal_paths_with_witness M q RepSets m}.
                               preamble_prefix_tests q mrsps (fst ` d_reachable_states_with_preambles M))"
                    | "((q, p), z) \<in> (\<lambda>(q, p, y). ((q, p), y)) ` (preamble_pair_tests (\<Union>(q, y)\<in>(\<lambda>q. (q, m_traversal_paths_with_witness M q RepSets m)) ` fst ` d_reachable_states_with_preambles M. (\<lambda>(p, rd, dr). dr) ` y) (fst ` (\<lambda>((q1, q2), A). ((q1, q2), A, Inr q1 :: 'a \<times> 'a + 'a, Inr q2 :: 'a \<times> 'a + 'a)) ` r_distinguishable_state_pairs_with_separators M))"
          by blast
        then show "((q, p), z) \<in> ?S2" proof cases
          case 1
          have scheme: "\<And> f y xs . y \<in> image f xs \<Longrightarrow> \<exists> x . x \<in> xs \<and> f x = y" by auto

          obtain qzq where "qzq \<in> (\<Union>q\<in>fst ` d_reachable_states_with_preambles M. \<Union> (prefix_pair_tests q ` {m_traversal_paths_with_witness M q RepSets m}))"
                     and   "(\<lambda>(q, p, y). ((q, p), y)) qzq = ((q,p),z)"
            using scheme[OF 1] by blast
          then obtain q' where "q'\<in>fst ` d_reachable_states_with_preambles M"
                         and   "qzq \<in> \<Union> (prefix_pair_tests q' ` {m_traversal_paths_with_witness M q' RepSets m})"
            by blast
          then have "fst qzq = q'"
            by auto
          then have "q' = q"
            using \<open>(\<lambda>(q, p, y). ((q, p), y)) qzq = ((q,p),z)\<close>
            by (simp add: prod.case_eq_if) 
          then have "qzq \<in> \<Union> (prefix_pair_tests q ` {m_traversal_paths_with_witness M q RepSets m})"
            using \<open>qzq \<in> \<Union> (prefix_pair_tests q' ` {m_traversal_paths_with_witness M q' RepSets m})\<close> 
            by blast
          then have "(\<lambda>(q, p, y). ((q, p), y)) qzq \<in> ?S2"
            by auto
          then show ?thesis 
            unfolding \<open>(\<lambda>(q, p, y). ((q, p), y)) qzq = ((q,p),z)\<close> 
            by assumption
        next
          case 2 
          then show ?thesis by blast
        next
          case 3
          then show ?thesis by blast
        qed
      qed
      moreover have "\<And> z . ((q, p), z) \<in> ?S2 \<Longrightarrow> ((q, p), z) \<in> ?S1"
        using \<open>q \<in> fst ` d_reachable_states_with_preambles M\<close> by blast
      ultimately show ?thesis
        by meson
    qed

    show "rd_targets (q,p) = {z. ((q, p), z)
                   \<in> (\<lambda>(q, p, y). ((q, p), y)) `
                      ((prefix_pair_tests q (m_traversal_paths_with_witness M q RepSets m)) \<union>
                       (\<Union>q\<in>fst ` d_reachable_states_with_preambles M.
                           \<Union>mrsps\<in>{m_traversal_paths_with_witness M q RepSets m}.
                              preamble_prefix_tests q mrsps (fst ` d_reachable_states_with_preambles M)) \<union>
                       preamble_pair_tests (\<Union>(q, y)\<in>(\<lambda>q. (q, m_traversal_paths_with_witness M q RepSets m)) ` fst ` d_reachable_states_with_preambles M. (\<lambda>(p, rd, dr). dr) ` y) (fst ` (\<lambda>((q1, q2), A). ((q1, q2), A, Inr q1 :: 'a \<times> 'a + 'a, Inr q2 :: 'a \<times> 'a + 'a)) ` r_distinguishable_state_pairs_with_separators M))}"
      using ***  unfolding **** by assumption
  qed


  define pps_alt :: "('a \<times> ('a,'b,'c) traversal_path \<times> 'a) set" where pps_alt_def : "pps_alt = {(q1,[],q2) | q1 q2 . \<exists> q p rd dr . q \<in> fst ` d_reachable_states_with_preambles M \<and> (p,(rd,dr)) \<in> m_traversal_paths_with_witness M q RepSets m \<and> q1 \<in> dr \<and> q2 \<in> dr \<and> (q1,q2) \<in> fst  ` r_distinguishable_state_pairs_with_separators M}"
  have preamble_pair_tests_alt :
    "preamble_pair_tests (\<Union>(q, y)\<in>(\<lambda>q. (q, m_traversal_paths_with_witness M q RepSets m)) ` fst ` d_reachable_states_with_preambles M. (\<lambda>(p, rd, dr). dr) ` y) (fst ` (\<lambda>((q1, q2), A). ((q1, q2), A, Inr q1 :: 'a \<times> 'a + 'a, Inr q2 :: 'a \<times> 'a + 'a)) ` r_distinguishable_state_pairs_with_separators M)
     = pps_alt"
    (is "?PP1 = ?PP2")
  proof -
    have "\<And> x . x \<in> ?PP1 \<Longrightarrow> x \<in> ?PP2"
    proof -
      fix x assume "x \<in> ?PP1"
      then obtain drs where "drs \<in> (\<Union>(q, y)\<in>(\<lambda>q. (q, m_traversal_paths_with_witness M q RepSets m)) ` fst ` d_reachable_states_with_preambles M. (\<lambda>(p, rd, dr). dr) ` y)"
                      and   "x \<in> (\<lambda>(q1, q2). (q1, [], q2)) ` (drs \<times> drs \<inter> fst ` (\<lambda>((q1, q2), A). ((q1, q2), A, Inr q1, Inr q2)) ` r_distinguishable_state_pairs_with_separators M)"
        unfolding preamble_pair_tests.simps by force

      obtain q y where "(q,y) \<in> (\<lambda>q. (q, m_traversal_paths_with_witness M q RepSets m)) ` fst ` d_reachable_states_with_preambles M"
                 and   "drs \<in> (\<lambda>(p, rd, dr). dr) ` y"
        using \<open>drs \<in> (\<Union>(q, y)\<in>(\<lambda>q. (q, m_traversal_paths_with_witness M q RepSets m)) ` fst ` d_reachable_states_with_preambles M. (\<lambda>(p, rd, dr). dr) ` y)\<close>
        by force

      have "q \<in> fst ` d_reachable_states_with_preambles M"
      and  "y = m_traversal_paths_with_witness M q RepSets m"
        using \<open>(q,y) \<in> (\<lambda>q. (q, m_traversal_paths_with_witness M q RepSets m)) ` fst ` d_reachable_states_with_preambles M\<close>
        by force+

      obtain p rd where "(p,(rd,drs)) \<in> m_traversal_paths_with_witness M q RepSets m"
        using \<open>drs \<in> (\<lambda>(p, rd, dr). dr) ` y\<close> unfolding \<open>y = m_traversal_paths_with_witness M q RepSets m\<close>
        by force


      obtain q1 q2 where "(q1,q2) \<in> (drs \<times> drs \<inter> fst ` (\<lambda>((q1, q2), A). ((q1, q2), A, Inr q1, Inr q2)) ` r_distinguishable_state_pairs_with_separators M)"
                   and   "x = (q1, [], q2)"
        using \<open>x \<in> (\<lambda>(q1, q2). (q1, [], q2)) ` (drs \<times> drs \<inter> fst ` (\<lambda>((q1, q2), A). ((q1, q2), A, Inr q1, Inr q2)) ` r_distinguishable_state_pairs_with_separators M)\<close>
        by force

      have "q1 \<in> drs \<and> q2 \<in> drs \<and> (q1,q2) \<in> fst  ` r_distinguishable_state_pairs_with_separators M"
        using \<open>(q1,q2) \<in> (drs \<times> drs \<inter> fst ` (\<lambda>((q1, q2), A). ((q1, q2), A, Inr q1, Inr q2)) ` r_distinguishable_state_pairs_with_separators M)\<close>
        by force

      then show "x \<in> ?PP2"
        unfolding \<open>x = (q1, [], q2)\<close> pps_alt_def
        using \<open>q \<in> fst ` d_reachable_states_with_preambles M\<close> \<open>(p,(rd,drs)) \<in> m_traversal_paths_with_witness M q RepSets m\<close>
        by blast
    qed

    moreover have "\<And> x . x \<in> ?PP2 \<Longrightarrow> x \<in> ?PP1" 
    proof -
      fix x assume "x \<in> ?PP2"
      then obtain q1 q2 where "x = (q1,[],q2)" unfolding pps_alt_def
        by auto
      then obtain q p rd dr where "q \<in> fst ` d_reachable_states_with_preambles M" 
                            and   "(p,(rd,dr)) \<in> m_traversal_paths_with_witness M q RepSets m" 
                            and   "q1 \<in> dr \<and> q2 \<in> dr \<and> (q1,q2) \<in> fst  ` r_distinguishable_state_pairs_with_separators M"
        using \<open>x \<in> ?PP2\<close> unfolding pps_alt_def by blast

      have "dr \<in> (\<Union>(q, y)\<in>(\<lambda>q. (q, m_traversal_paths_with_witness M q RepSets m)) ` fst ` d_reachable_states_with_preambles M. (\<lambda>(p, rd, dr). dr) ` y)"
        using \<open>q \<in> fst ` d_reachable_states_with_preambles M\<close> \<open>(p,(rd,dr)) \<in> m_traversal_paths_with_witness M q RepSets m\<close> by force

      moreover have "x \<in> (\<lambda>(q1, q2). (q1, [], q2)) ` (dr \<times> dr \<inter> fst ` (\<lambda>((q1, q2), A). ((q1, q2), A, Inr q1, Inr q2)) ` r_distinguishable_state_pairs_with_separators M)"
        unfolding \<open>x = (q1,[],q2)\<close> using \<open>q1 \<in> dr \<and> q2 \<in> dr \<and> (q1,q2) \<in> fst  ` r_distinguishable_state_pairs_with_separators M\<close> by force

      ultimately show "x \<in> ?PP1"
        unfolding preamble_pair_tests.simps by force
    qed

    ultimately show ?thesis by blast
  qed


  have p1: "(initial M,initial_preamble M) \<in> states_with_preambles"
    using fsm_initial[of M]
    unfolding states_with_preambles_def d_reachable_states_with_preambles_def calculate_state_preamble_from_input_choices.simps by force

  have p2a: "\<And> q P . (q,P) \<in> states_with_preambles \<Longrightarrow> is_preamble P M q"
    using assms(1) d_reachable_states_with_preambles_soundness(1) states_with_preambles_def by blast

  have p2b: "\<And> q P . (q,P) \<in> states_with_preambles \<Longrightarrow> (tps q) \<noteq> {}"
  proof -
    fix q P assume "(q,P) \<in> states_with_preambles"
    then have "q \<in> (image fst (d_reachable_states_with_preambles M))"
      unfolding states_with_preambles_def
      by (simp add: rev_image_eqI) 
    
    have "q \<in> states M"
      using \<open>(q, P) \<in> states_with_preambles\<close> assms(1) d_reachable_states_with_preambles_soundness(2) states_with_preambles_def by blast 


    obtain p' d' where  "(p', d') \<in> m_traversal_paths_with_witness M q RepSets m"
      using m_traversal_path_exist[OF assms(2) \<open>q \<in> states M\<close> assms(3) \<open>\<And>q. q \<in> FSM.states M \<Longrightarrow> \<exists>d\<in>set RepSets. q \<in> fst d\<close>] assms(5) 
      by blast
    then have "p' \<in> image fst (m_traversal_paths_with_witness M q RepSets m)"
      using image_iff by fastforce
    
    have "(q, image fst (m_traversal_paths_with_witness M q RepSets m)) \<in> (image (\<lambda> (q,p) . (q, image fst p)) (image (\<lambda> q . (q,m_traversal_paths_with_witness M q RepSets m)) (image fst (d_reachable_states_with_preambles M))))"
      using \<open>q \<in> (image fst (d_reachable_states_with_preambles M))\<close> by force
    have "(image fst (m_traversal_paths_with_witness M q RepSets m)) \<in> (m2f (set_as_map (image (\<lambda> (q,p) . (q, image fst p)) (image (\<lambda> q . (q,m_traversal_paths_with_witness M q RepSets m)) (image fst (d_reachable_states_with_preambles M)))))) q"
      using set_as_map_containment[OF \<open>(q, image fst (m_traversal_paths_with_witness M q RepSets m)) \<in> (image (\<lambda> (q,p) . (q, image fst p)) (image (\<lambda> q . (q,m_traversal_paths_with_witness M q RepSets m)) (image fst (d_reachable_states_with_preambles M))))\<close>]
      by assumption
    then have "p' \<in> (\<Union> ((m2f (set_as_map (image (\<lambda> (q,p) . (q, image fst p)) (image (\<lambda> q . (q,m_traversal_paths_with_witness M q RepSets m)) (image fst (d_reachable_states_with_preambles M)))))) q))"
      using \<open>p' \<in> image fst (m_traversal_paths_with_witness M q RepSets m)\<close> by blast

    then show "(tps q) \<noteq> {}"
      unfolding tps_def m2f_by_from_m2f by blast
  qed

  have p2: "(\<forall>q P. (q, P) \<in> states_with_preambles \<longrightarrow> is_preamble P M q \<and> tps q \<noteq> {})"
    using p2a p2b by blast

  have "\<And> q1 q2 A d1 d2 . ((A,d1,d2) \<in> atcs (q1,q2)) \<Longrightarrow> ((q1,q2),A) \<in> r_distinguishable_state_pairs_with_separators M \<and> d1 = Inr q1 \<and> d2 = Inr q2"
  proof -
    fix q1 q2 A d1 d2 assume "((A,d1,d2) \<in> atcs (q1,q2))"
    then have "atcs (q1,q2) = {z. ((q1, q2), z) \<in> (\<lambda>((q1, q2), A). ((q1, q2), A, Inr q1, Inr q2)) ` r_distinguishable_state_pairs_with_separators M}"
      unfolding atcs_def set_as_map_def by auto
    then show "((q1,q2),A) \<in> r_distinguishable_state_pairs_with_separators M \<and> d1 = Inr q1 \<and> d2 = Inr q2"
      using \<open>((A,d1,d2) \<in> atcs (q1,q2))\<close> by auto
  qed


  have "\<And> q1 q2 A d1 d2 . (A,d1,d2) \<in> atcs (q1,q2) \<Longrightarrow> (A,d2,d1) \<in> atcs (q2,q1) \<and> is_separator M q1 q2 A d1 d2"
  proof -
    fix q1 q2 A d1 d2 assume "(A,d1,d2) \<in> atcs (q1,q2)"
    then have "((q1,q2),A) \<in> r_distinguishable_state_pairs_with_separators M" and "d1 = Inr q1" and "d2 = Inr q2"
      using \<open>\<And> q1 q2 A d1 d2 . ((A,d1,d2) \<in> atcs (q1,q2)) \<Longrightarrow> ((q1,q2),A) \<in> r_distinguishable_state_pairs_with_separators M \<and> d1 = Inr q1 \<and> d2 = Inr q2\<close>
      by blast+
    then have "((q2,q1),A) \<in> r_distinguishable_state_pairs_with_separators M"
      unfolding r_distinguishable_state_pairs_with_separators_def
      by auto  
    then have "(A,d2,d1) \<in> atcs (q2,q1)"
      unfolding atcs_def \<open>d1 = Inr q1\<close> \<open>d2 = Inr q2\<close> set_as_map_def by force
    moreover have "is_separator M q1 q2 A d1 d2"
      using r_distinguishable_state_pairs_with_separators_elem_is_separator[OF \<open>((q1,q2),A) \<in> r_distinguishable_state_pairs_with_separators M\<close> assms(1,2)]
      unfolding \<open>d1 = Inr q1\<close> \<open>d2 = Inr q2\<close>
      by assumption
    ultimately show "(A,d2,d1) \<in> atcs (q2,q1) \<and> is_separator M q1 q2 A d1 d2"
      by simp
  qed
  then have p3 : "(\<forall>q1 q2 A d1 d2. (A, d1, d2) \<in> atcs (q1, q2) \<longrightarrow> (A, d2, d1) \<in> atcs (q2, q1) \<and> is_separator M q1 q2 A d1 d2)"
    by blast

  have p4: "\<And> q . q \<in> states M \<Longrightarrow> (\<exists>d \<in> set RepSets. q \<in> fst d)"
    by (simp add: assms(4))
  
  have p5: "\<And> d . d \<in> set RepSets \<Longrightarrow> ((fst d \<subseteq> states M) \<and> (snd d = fst d \<inter> fst ` states_with_preambles) \<and> (\<forall> q1 q2 . q1 \<in> fst d \<longrightarrow> q2 \<in> fst d \<longrightarrow> q1 \<noteq> q2 \<longrightarrow> atcs (q1,q2) \<noteq> {}))"
  proof -
    fix d assume "d \<in> set RepSets"
    
    then have "\<And> q1 q2 . q1 \<in> fst d \<Longrightarrow> q2 \<in> fst d \<Longrightarrow> q1 \<noteq> q2 \<Longrightarrow> atcs (q1,q2) \<noteq> {}"
    proof -
      fix q1 q2 assume "q1 \<in> fst d" and "q2 \<in> fst d" and "q1 \<noteq> q2"
      then have "(q1, q2) \<in> fst ` r_distinguishable_state_pairs_with_separators M" 
        using assms(6)[OF \<open>d \<in> set RepSets\<close>] by blast
      then obtain A where "((q1,q2),A) \<in> r_distinguishable_state_pairs_with_separators M"
        by auto
      then have "(A,Inr q1,Inr q2) \<in> atcs (q1,q2)"
        unfolding atcs_def set_as_map_def 
        by force
      then show "atcs (q1,q2) \<noteq> {}"
        by blast
    qed
    then show "((fst d \<subseteq> states M) \<and> (snd d = fst d \<inter> fst ` states_with_preambles) \<and> (\<forall> q1 q2 . q1 \<in> fst d \<longrightarrow> q2 \<in> fst d \<longrightarrow> q1 \<noteq> q2 \<longrightarrow> atcs (q1,q2) \<noteq> {}))"
      using assms(5)[OF \<open>d \<in> set RepSets\<close>] unfolding states_with_preambles_def by blast
  qed

  have p6 : "\<And> q . q \<in> image fst states_with_preambles \<Longrightarrow> tps q \<subseteq> {p1 . \<exists> p2 d . (p1@p2,d) \<in> m_traversal_paths_with_witness M q RepSets m} \<and> fst ` (m_traversal_paths_with_witness M q RepSets m) \<subseteq> tps q"
  proof 
    fix q assume "q \<in> image fst states_with_preambles"
    then have "q \<in> fst ` d_reachable_states_with_preambles M"
      unfolding states_with_preambles_def by assumption
    then have "q \<in> states M"
      by (metis (no_types, lifting) assms(1) d_reachable_states_with_preambles_soundness(2) image_iff prod.collapse)
    show "fst ` m_traversal_paths_with_witness M q RepSets m \<subseteq> tps q"
      unfolding tps_alt_def[OF \<open>q \<in> fst ` d_reachable_states_with_preambles M\<close>]
      by blast


    show "tps q \<subseteq> {p1 . \<exists> p2 d . (p1@p2,d) \<in> m_traversal_paths_with_witness M q RepSets m}"
    proof
      fix p assume "p \<in> tps q"


      have * : "(\<And> q . q \<in> states M \<Longrightarrow> (\<exists>d \<in> set RepSets. q \<in> fst d))" 
        using p4 by blast

      have  **: "(\<And> d . d \<in> set RepSets \<Longrightarrow> (snd d \<subseteq> fst d))"
        using p5 by simp

      from \<open>p \<in> tps q\<close> consider 
        (a) "p \<in> fst ` m_traversal_paths_with_witness M q RepSets m" |
        (b) "(q, p) \<in> (\<lambda>(q, p, q'). (q, p)) ` (prefix_pair_tests q (m_traversal_paths_with_witness M q RepSets m))" |
        (c) "(q, p) \<in> (\<lambda>(q, p, q'). (q, p)) ` (\<Union>q\<in>fst ` d_reachable_states_with_preambles M.
                \<Union>mrsps\<in>{m_traversal_paths_with_witness M q RepSets m}.
                   preamble_prefix_tests q mrsps (fst ` d_reachable_states_with_preambles M))" |
        (d) "(q, p) \<in> (\<lambda>(q, p, q'). (q, p)) ` pps_alt"  
        unfolding tps_alt_def[OF \<open>q \<in> fst ` d_reachable_states_with_preambles M\<close>] preamble_pair_tests_alt by blast

      then show "p \<in> {p1. \<exists>p2 d. (p1 @ p2, d) \<in> m_traversal_paths_with_witness M q RepSets m}"
      proof cases
        case a
        then obtain d where "(p,d) \<in> m_traversal_paths_with_witness M q RepSets m"
          by auto
        then have "\<exists>p2 d. (p @ p2, d) \<in> m_traversal_paths_with_witness M q RepSets m"
          by (metis append_eq_append_conv2)
        then show ?thesis 
          by blast
      next
        case b
  
        obtain p1 p2  where "(q,p) \<in> ((\<lambda>(q, p, q'). (q, p)) `{(q, p1, target q p2), (q, p2, target q p1)})"
           and "\<exists>(p, rd, dr)\<in>m_traversal_paths_with_witness M q RepSets m.
              (p1, p2) \<in> set (prefix_pairs p) \<and> target q p1 \<in> rd \<and> target q p2 \<in> rd \<and> target q p1 \<noteq> target q p2"
          using b
          unfolding prefix_pair_tests.simps by blast
  
        obtain p' d where "(p', d) \<in> m_traversal_paths_with_witness M q RepSets m"
                    and   "(p1, p2) \<in> set (prefix_pairs p')"
          using \<open>\<exists>(p, rd, dr)\<in>m_traversal_paths_with_witness M q RepSets m.
              (p1, p2) \<in> set (prefix_pairs p) \<and> target q p1 \<in> rd \<and> target q p2 \<in> rd \<and> target q p1 \<noteq> target q p2\<close>
          by blast
  
        have "\<exists> p'' . p' = p @ p''"
          using \<open>(p1, p2) \<in> set (prefix_pairs p')\<close> unfolding prefix_pairs_set_alt 
          using \<open>(q,p) \<in> ((\<lambda>(q, p, q'). (q, p)) `{(q, p1, target q p2), (q, p2, target q p1)})\<close> by auto
        then show ?thesis
          using \<open>(p', d) \<in> m_traversal_paths_with_witness M q RepSets m\<close>  
          by blast
      next
        case c     
  
        obtain q' where "q' \<in> fst ` d_reachable_states_with_preambles M"
                  and   "(q,p) \<in> (\<lambda>(q, p, q'). (q, p)) ` (preamble_prefix_tests q' (m_traversal_paths_with_witness M q' RepSets m) (fst ` d_reachable_states_with_preambles M))"
          using c by blast
  
        obtain p1 q2  where "(q,p) \<in> ((\<lambda>(q, p, q'). (q, p)) `{(q', p1, q2), (q2, [], target q' p1)})"
           and "\<exists>(p, rd, dr)\<in>m_traversal_paths_with_witness M q' RepSets m.
              q2 \<in> fst ` d_reachable_states_with_preambles M \<and> (\<exists>p2. p = p1 @ p2) \<and> target q' p1 \<in> rd \<and> q2 \<in> rd \<and> target q' p1 \<noteq> q2"
          using \<open>(q,p) \<in> (\<lambda>(q, p, q'). (q, p)) ` (preamble_prefix_tests q' (m_traversal_paths_with_witness M q' RepSets m) (fst ` d_reachable_states_with_preambles M))\<close>
          unfolding preamble_prefix_tests_def
          by blast
  
        obtain p2 d where "(p1@p2, d)\<in>m_traversal_paths_with_witness M q' RepSets m"
                        and   "q2 \<in> fst ` d_reachable_states_with_preambles M"
          using \<open>\<exists>(p, rd, dr)\<in>m_traversal_paths_with_witness M q' RepSets m.
              q2 \<in> fst ` d_reachable_states_with_preambles M \<and> (\<exists>p2. p = p1 @ p2) \<and> target q' p1 \<in> rd \<and> q2 \<in> rd \<and> target q' p1 \<noteq> q2\<close>
          by blast
  
        consider (a) "q = q' \<and> p = p1" | (b) "q = q2 \<and> p = []"
          using \<open>(q,p) \<in> ((\<lambda>(q, p, q'). (q, p)) `{(q', p1, q2), (q2, [], target q' p1)})\<close> by auto
        then show ?thesis proof cases
          case a
          then show ?thesis
            using \<open>(p1 @ p2, d) \<in> m_traversal_paths_with_witness M q' RepSets m\<close> by blast 
  
        next
          case b
  
          then have "q \<in> states M" and "p = []"
            using \<open>q2 \<in> fst ` d_reachable_states_with_preambles M\<close> unfolding d_reachable_states_with_preambles_def by auto
  
          have "\<exists>p' d'. (p', d') \<in> m_traversal_paths_with_witness M q RepSets m"
            using m_traversal_path_exist[OF assms(2) \<open>q \<in> states M\<close> assms(3) * **]
            by blast
          then show ?thesis 
            unfolding \<open>p = []\<close>
            by simp
        qed
      next
        case d 
        then have "p = []" 
          unfolding pps_alt_def by force
        
        have "q \<in> states M"
          using \<open>q \<in> fst ` d_reachable_states_with_preambles M\<close> unfolding d_reachable_states_with_preambles_def by auto
  
        have "\<exists>p' d'. (p', d') \<in> m_traversal_paths_with_witness M q RepSets m"
          using m_traversal_path_exist[OF assms(2) \<open>q \<in> states M\<close> assms(3) * **]
          by blast
        then show ?thesis 
          unfolding \<open>p = []\<close>
          by simp
      qed
    qed
  qed
 
  have p7 : "\<And> q p d . q \<in> image fst states_with_preambles \<Longrightarrow> (p,d) \<in> m_traversal_paths_with_witness M q RepSets m \<Longrightarrow> 
            ( (\<forall> p1 p2 p3 . p=p1@p2@p3 \<longrightarrow> p2 \<noteq> [] \<longrightarrow> target q p1 \<in> fst d \<longrightarrow> target q (p1@p2) \<in> fst d \<longrightarrow> target q p1 \<noteq> target q (p1@p2) \<longrightarrow> (p1 \<in> tps q \<and> (p1@p2) \<in> tps q \<and> target q p1 \<in> rd_targets (q,(p1@p2)) \<and> target q (p1@p2) \<in> rd_targets (q,p1)))
            \<and> (\<forall> p1 p2 q' . p=p1@p2 \<longrightarrow> q' \<in> image fst states_with_preambles \<longrightarrow> target q p1 \<in> fst d \<longrightarrow> q' \<in> fst d \<longrightarrow> target q p1 \<noteq> q' \<longrightarrow> (p1 \<in> tps q \<and> [] \<in> tps q' \<and> target q p1 \<in> rd_targets (q',[]) \<and> q' \<in> rd_targets (q,p1)))
            \<and> (\<forall> q1 q2 . q1 \<noteq> q2 \<longrightarrow> q1 \<in> snd d \<longrightarrow> q2 \<in> snd d \<longrightarrow> ([] \<in> tps q1 \<and> [] \<in> tps q2 \<and> q1 \<in> rd_targets (q2,[]) \<and> q2 \<in> rd_targets (q1,[]))))"
  proof -
    fix q p d assume "q \<in> image fst states_with_preambles" and "(p,d) \<in> m_traversal_paths_with_witness M q RepSets m"
    then have "(p,(fst d, snd d)) \<in> m_traversal_paths_with_witness M q RepSets m" by auto

    have "q \<in> fst ` d_reachable_states_with_preambles M"
      using \<open>q \<in> image fst states_with_preambles\<close> unfolding states_with_preambles_def by assumption

    have p7c1 : "\<And> p1 p2 p3 . p=p1@p2@p3 \<Longrightarrow> p2 \<noteq> [] \<Longrightarrow> target q p1 \<in> fst d \<Longrightarrow> target q (p1@p2) \<in> fst d \<Longrightarrow> target q p1 \<noteq> target q (p1@p2) \<Longrightarrow> (p1 \<in> tps q \<and> (p1@p2) \<in> tps q \<and> target q p1 \<in> rd_targets (q,(p1@p2)) \<and> target q (p1@p2) \<in> rd_targets (q,p1))"
    proof -
      fix p1 p2 p3 assume "p=p1@p2@p3" and "p2 \<noteq> []" and "target q p1 \<in> fst d" and "target q (p1@p2) \<in> fst d" and "target q p1 \<noteq> target q (p1@p2)"

      have "(p1,p1@p2) \<in> set (prefix_pairs p)"
        using \<open>p=p1@p2@p3\<close> \<open>p2 \<noteq> []\<close> unfolding prefix_pairs_set
        by simp 
      then have "(p1,p1@p2) \<in> set (filter (\<lambda>(p1, p2). target q p1 \<in> fst d \<and> target q p2 \<in> fst d \<and> target q p1 \<noteq> target q p2) (prefix_pairs p))"
        using \<open>target q p1 \<in> fst d\<close> \<open>target q (p1@p2) \<in> fst d\<close> \<open>target q p1 \<noteq> target q (p1@p2)\<close>
        by auto
      have "{(q, p1, target q (p1@p2)), (q, (p1@p2), target q p1)} \<in> ((set (map (\<lambda>(p1, p2). {(q, p1, target q p2), (q, p2, target q p1)})
            (filter (\<lambda>(p1, p2). target q p1 \<in> fst d \<and> target q p2 \<in> fst d \<and> target q p1 \<noteq> target q p2) (prefix_pairs p)))))"
        using map_set[OF \<open>(p1,p1@p2) \<in> set (filter (\<lambda>(p1, p2). target q p1 \<in> fst d \<and> target q p2 \<in> fst d \<and> target q p1 \<noteq> target q p2) (prefix_pairs p))\<close>, of "(\<lambda>(p1, p2). {(q, p1, target q p2), (q, p2, target q p1)})"] 
        by force
      then have "(q, p1, target q (p1@p2)) \<in> prefix_pair_tests q (m_traversal_paths_with_witness M q RepSets m)"
           and  "(q, p1@p2, target q p1) \<in> prefix_pair_tests q (m_traversal_paths_with_witness M q RepSets m)"
        unfolding prefix_pair_tests_code[of q "m_traversal_paths_with_witness M q RepSets m"]
        using \<open>(p,(fst d, snd d)) \<in> m_traversal_paths_with_witness M q RepSets m\<close>
        by blast+

      have "p1 \<in> tps q"
      proof -
        have "(q, p1) \<in> ((\<lambda>(q, p, q'). (q, p)) ` (prefix_pair_tests q (m_traversal_paths_with_witness M q RepSets m)))"
          using \<open>(q, p1, target q (p1@p2)) \<in> prefix_pair_tests q (m_traversal_paths_with_witness M q RepSets m)\<close>
          by (simp add: rev_image_eqI)  
        then show ?thesis 
          unfolding tps_alt_def[OF \<open>q \<in> fst ` d_reachable_states_with_preambles M\<close>] 
          by blast
      qed

      moreover have "(p1@p2) \<in> tps q"
      proof -
        have "(q, p1@p2) \<in> ((\<lambda>(q, p, q'). (q, p)) ` (prefix_pair_tests q (m_traversal_paths_with_witness M q RepSets m)))"
          using \<open>(q, p1@p2, target q p1) \<in> prefix_pair_tests q (m_traversal_paths_with_witness M q RepSets m)\<close>
          by (simp add: rev_image_eqI) 
        then show ?thesis 
          unfolding tps_alt_def[OF \<open>q \<in> fst ` d_reachable_states_with_preambles M\<close>] 
          by blast          
      qed

      moreover have "target q p1 \<in> rd_targets (q,(p1@p2))"
      proof -
        have "((q, p1@p2), target q p1) \<in> (\<lambda>(q, p, y). ((q, p), y)) ` prefix_pair_tests q (m_traversal_paths_with_witness M q RepSets m)"
          using \<open>(q, p1@p2, target q p1) \<in> prefix_pair_tests q (m_traversal_paths_with_witness M q RepSets m)\<close>
          by (simp add: rev_image_eqI)
        then show ?thesis
          unfolding rd_targets_alt_def[OF \<open>q \<in> fst ` d_reachable_states_with_preambles M\<close>] 
          by blast
      qed

      moreover have "target q (p1@p2) \<in> rd_targets (q,p1)"
      proof -
        have "((q, p1), target q (p1@p2)) \<in> (\<lambda>(q, p, y). ((q, p), y)) ` prefix_pair_tests q (m_traversal_paths_with_witness M q RepSets m)"
          using \<open>(q, p1, target q (p1@p2)) \<in> prefix_pair_tests q (m_traversal_paths_with_witness M q RepSets m)\<close>
          by (simp add: rev_image_eqI)
        then show ?thesis
          unfolding rd_targets_alt_def[OF \<open>q \<in> fst ` d_reachable_states_with_preambles M\<close>] 
          by blast
      qed
      
      ultimately show "(p1 \<in> tps q \<and> (p1@p2) \<in> tps q \<and> target q p1 \<in> rd_targets (q,(p1@p2)) \<and> target q (p1@p2) \<in> rd_targets (q,p1))"
        by blast
    qed

    moreover have p7c2: "\<And> p1 p2 q' . p=p1@p2 \<Longrightarrow> q' \<in> image fst states_with_preambles \<Longrightarrow> target q p1 \<in> fst d \<Longrightarrow> q' \<in> fst d \<Longrightarrow> target q p1 \<noteq> q' \<Longrightarrow> (p1 \<in> tps q \<and> [] \<in> tps q' \<and> target q p1 \<in> rd_targets (q',[]) \<and> q' \<in> rd_targets (q,p1))"
    proof -
      fix p1 p2 q' assume "p=p1@p2" and "q' \<in> image fst states_with_preambles" and "target q p1 \<in> fst d" and "q' \<in> fst d" and "target q p1 \<noteq> q'"
      then have "q' \<in> fst ` d_reachable_states_with_preambles M"
        unfolding states_with_preambles_def by blast
      
      have "p1 \<in> set (prefixes p)"
        using \<open>p=p1@p2\<close> unfolding prefixes_set
        by simp 
      then have "(p1,q') \<in> Set.filter (\<lambda>(p1, q2). target q p1 \<in> fst d \<and> q2 \<in> fst d \<and> target q p1 \<noteq> q2) (set (prefixes p) \<times> fst ` d_reachable_states_with_preambles M)"
        using \<open>target q p1 \<in> fst d\<close> \<open>q' \<in> fst d\<close> \<open>q' \<in> image fst states_with_preambles\<close> \<open>target q p1 \<noteq> q'\<close> unfolding states_with_preambles_def
        by force
      then have "{(q, p1, q'), (q', [], target q p1)} \<subseteq> preamble_prefix_tests q (m_traversal_paths_with_witness M q RepSets m) (fst ` d_reachable_states_with_preambles M)"
        using preamble_prefix_tests_code[of q "m_traversal_paths_with_witness M q RepSets m" "(fst ` d_reachable_states_with_preambles M)"]
        using \<open>(p,(fst d, snd d)) \<in> m_traversal_paths_with_witness M q RepSets m\<close>
        by blast
      then have "(q, p1, q') \<in> preamble_prefix_tests q (m_traversal_paths_with_witness M q RepSets m) (fst ` d_reachable_states_with_preambles M)"
           and  "(q', [], target q p1) \<in> preamble_prefix_tests q (m_traversal_paths_with_witness M q RepSets m) (fst ` d_reachable_states_with_preambles M)"
        by blast+

      have "p1 \<in> tps q"
        using \<open>(q, p1, q') \<in> preamble_prefix_tests q (m_traversal_paths_with_witness M q RepSets m) (fst ` d_reachable_states_with_preambles M)\<close>        
              \<open>q \<in> fst ` d_reachable_states_with_preambles M\<close>
        unfolding tps_alt_def[OF \<open>q \<in> fst ` d_reachable_states_with_preambles M\<close>]
        by force

      moreover have "[] \<in> tps q'"
        using \<open>(q', [], target q p1) \<in> preamble_prefix_tests q (m_traversal_paths_with_witness M q RepSets m) (fst ` d_reachable_states_with_preambles M)\<close>        
              \<open>q \<in> fst ` d_reachable_states_with_preambles M\<close>
        unfolding tps_alt_def[OF \<open>q' \<in> fst ` d_reachable_states_with_preambles M\<close>]
        by force

      moreover have "target q p1 \<in> rd_targets (q',[])"
        using \<open>(q', [], target q p1) \<in> preamble_prefix_tests q (m_traversal_paths_with_witness M q RepSets m) (fst ` d_reachable_states_with_preambles M)\<close>        
              \<open>q \<in> fst ` d_reachable_states_with_preambles M\<close>
        unfolding rd_targets_alt_def[OF \<open>q' \<in> fst ` d_reachable_states_with_preambles M\<close>] 
        by force

      moreover have "q' \<in> rd_targets (q,p1)"
        using \<open>(q, p1, q') \<in> preamble_prefix_tests q (m_traversal_paths_with_witness M q RepSets m) (fst ` d_reachable_states_with_preambles M)\<close>        
              \<open>q \<in> fst ` d_reachable_states_with_preambles M\<close>
        unfolding rd_targets_alt_def[OF \<open>q \<in> fst ` d_reachable_states_with_preambles M\<close>]
        by force

      ultimately show "(p1 \<in> tps q \<and> [] \<in> tps q' \<and> target q p1 \<in> rd_targets (q',[]) \<and> q' \<in> rd_targets (q,p1))"
        by blast
    qed


    moreover have p7c3: "\<And> q1 q2 . q1 \<noteq> q2 \<Longrightarrow> q1 \<in> snd d \<Longrightarrow> q2 \<in> snd d \<Longrightarrow> ([] \<in> tps q1 \<and> [] \<in> tps q2 \<and> q1 \<in> rd_targets (q2,[]) \<and> q2 \<in> rd_targets (q1,[]))"
    proof -
      fix q1 q2 assume "q1 \<noteq> q2" and "q1 \<in> snd d" and "q2 \<in> snd d"

      have "(\<And>d. d \<in> set RepSets \<Longrightarrow> snd d \<subseteq> fst d)"
        using p5 by blast
      have "q \<in> states M"
        by (metis (no_types, lifting) \<open>q \<in> fst ` d_reachable_states_with_preambles M\<close> assms(1) 
              d_reachable_states_with_preambles_soundness(2) image_iff prod.collapse) 

      have "d \<in> set RepSets" 
        using m_traversal_paths_with_witness_set[OF p4 \<open>(\<And>d. d \<in> set RepSets \<Longrightarrow> snd d \<subseteq> fst d)\<close> \<open>q \<in> states M\<close>, of m]
        using \<open>(p, d) \<in> m_traversal_paths_with_witness M q RepSets m\<close> find_set 
        by force 

      have "fst d \<subseteq> states M" 
      and  "snd d = fst d \<inter> fst ` states_with_preambles" 
      and  "\<And> q1 q2. q1 \<in> fst d \<Longrightarrow> q2 \<in> fst d \<Longrightarrow> q1 \<noteq> q2 \<Longrightarrow> atcs (q1, q2) \<noteq> {}"
        using p5[OF \<open>d \<in> set RepSets\<close>] by blast+

      have "q1 \<in> fst d" 
       and "q2 \<in> fst d" 
       and "q1 \<in> fst ` d_reachable_states_with_preambles M" 
       and "q2 \<in> fst ` d_reachable_states_with_preambles M"
        using \<open>q1 \<in> snd d\<close> \<open>q2 \<in> snd d\<close> unfolding \<open>snd d = fst d \<inter> fst ` states_with_preambles\<close> 
        unfolding states_with_preambles_def by blast+

      obtain A t1 t2 where "(A,t1,t2) \<in> atcs (q1, q2)"
        using \<open>\<And> q1 q2. q1 \<in> fst d \<Longrightarrow> q2 \<in> fst d \<Longrightarrow> q1 \<noteq> q2 \<Longrightarrow> atcs (q1, q2) \<noteq> {}\<close>[OF \<open>q1 \<in> fst d\<close> \<open>q2 \<in> fst d\<close> \<open>q1 \<noteq> q2\<close>] 
        by auto

      then have "(q1, q2) \<in> fst ` r_distinguishable_state_pairs_with_separators M" 
        unfolding atcs_def using set_as_map_elem by force
      then have "(q1,[],q2) \<in> pps_alt"
        using \<open>q \<in> fst ` d_reachable_states_with_preambles M\<close> \<open>(p,(fst d, snd d)) \<in> m_traversal_paths_with_witness M q RepSets m\<close>
        unfolding pps_alt_def
        by (metis (mono_tags, lifting) \<open>q1 \<in> snd d\<close> \<open>q2 \<in> snd d\<close> mem_Collect_eq) 
      then have "[] \<in> tps q1" and "q2 \<in> rd_targets (q1,[])"
        unfolding tps_alt_def[OF \<open>q1 \<in> fst ` d_reachable_states_with_preambles M\<close>] 
                  rd_targets_alt_def[OF \<open>q1 \<in> fst ` d_reachable_states_with_preambles M\<close>] 
                  preamble_pair_tests_alt 
        by force+

      have "(A,t2,t1) \<in> atcs (q2, q1)"
        using p3 \<open>(A,t1,t2) \<in> atcs (q1, q2)\<close> by blast
      then have "(q2, q1) \<in> fst ` r_distinguishable_state_pairs_with_separators M" 
        unfolding atcs_def using set_as_map_elem by force
      then have "(q2,[],q1) \<in> pps_alt"
        using \<open>q \<in> fst ` d_reachable_states_with_preambles M\<close> \<open>(p,(fst d, snd d)) \<in> m_traversal_paths_with_witness M q RepSets m\<close>
        unfolding pps_alt_def
        by (metis (mono_tags, lifting) \<open>q1 \<in> snd d\<close> \<open>q2 \<in> snd d\<close> mem_Collect_eq) 
      then have "[] \<in> tps q2" and "q1 \<in> rd_targets (q2,[])"
        unfolding tps_alt_def[OF \<open>q2 \<in> fst ` d_reachable_states_with_preambles M\<close>] 
                  rd_targets_alt_def[OF \<open>q2 \<in> fst ` d_reachable_states_with_preambles M\<close>] 
                  preamble_pair_tests_alt 
        by force+

      then show "([] \<in> tps q1 \<and> [] \<in> tps q2 \<and> q1 \<in> rd_targets (q2,[]) \<and> q2 \<in> rd_targets (q1,[]))"
        using \<open>[] \<in> tps q1\<close> \<open>q2 \<in> rd_targets (q1,[])\<close> 
        by simp
    qed

    ultimately show "(\<forall> p1 p2 p3 . p=p1@p2@p3 \<longrightarrow> p2 \<noteq> [] \<longrightarrow> target q p1 \<in> fst d \<longrightarrow> target q (p1@p2) \<in> fst d \<longrightarrow> target q p1 \<noteq> target q (p1@p2) \<longrightarrow> (p1 \<in> tps q \<and> (p1@p2) \<in> tps q \<and> target q p1 \<in> rd_targets (q,(p1@p2)) \<and> target q (p1@p2) \<in> rd_targets (q,p1)))
            \<and> (\<forall> p1 p2 q' . p=p1@p2 \<longrightarrow> q' \<in> image fst states_with_preambles \<longrightarrow> target q p1 \<in> fst d \<longrightarrow> q' \<in> fst d \<longrightarrow> target q p1 \<noteq> q' \<longrightarrow> (p1 \<in> tps q \<and> [] \<in> tps q' \<and> target q p1 \<in> rd_targets (q',[]) \<and> q' \<in> rd_targets (q,p1)))
            \<and> (\<forall> q1 q2 . q1 \<noteq> q2 \<longrightarrow> q1 \<in> snd d \<longrightarrow> q2 \<in> snd d \<longrightarrow> ([] \<in> tps q1 \<and> [] \<in> tps q2 \<and> q1 \<in> rd_targets (q2,[]) \<and> q2 \<in> rd_targets (q1,[])))"
      by blast
  qed

  have "implies_completeness_for_repetition_sets (Test_Suite states_with_preambles tps rd_targets atcs) M m RepSets"
    unfolding implies_completeness_for_repetition_sets.simps
    using p1 p2 p3 p4 p5 p6 p7
    by force
  then show "implies_completeness (calculate_test_suite_for_repetition_sets M m RepSets) M m"
    unfolding \<open>calculate_test_suite_for_repetition_sets M m RepSets = Test_Suite states_with_preambles tps rd_targets atcs\<close>
              implies_completeness_def
    by blast


  show "is_finite_test_suite (calculate_test_suite_for_repetition_sets M m RepSets)"
  proof -
    have "finite states_with_preambles"
      unfolding states_with_preambles_def d_reachable_states_with_preambles_def 
      using fsm_states_finite[of M] by simp

    moreover have "\<And> q p. q \<in> fst ` states_with_preambles \<Longrightarrow> finite (rd_targets (q, p))"
    proof -
      fix q p assume "q \<in> fst ` states_with_preambles"
      then have "q \<in> fst ` d_reachable_states_with_preambles M" unfolding states_with_preambles_def by assumption

      have *: "finite ((\<lambda>(q, p, y). ((q, p), y)) ` (prefix_pair_tests q (m_traversal_paths_with_witness M q RepSets m) \<union>
             (\<Union>q\<in>fst ` d_reachable_states_with_preambles M.
                 \<Union>mrsps\<in>{m_traversal_paths_with_witness M q RepSets m}.
                    preamble_prefix_tests q mrsps (fst ` d_reachable_states_with_preambles M)) \<union>
             preamble_pair_tests
              (\<Union>(q, y)\<in>(\<lambda>q. (q, m_traversal_paths_with_witness M q RepSets m)) `
                        fst ` d_reachable_states_with_preambles M.
                  (\<lambda>(p, rd, dr). dr) ` y)
              (fst ` (\<lambda>((q1, q2), A). ((q1, q2), A, Inr q1, Inr q2)) ` r_distinguishable_state_pairs_with_separators M)))"
      proof -
        have * : "\<And> a b c f . finite (f ` (a \<union> b \<union> c)) = (finite (f`a) \<and> finite (f`b) \<and> finite (f`c))"
          by (simp add: image_Un) 

        have "finite ((\<lambda>(q, p, y). ((q, p), y)) ` (prefix_pair_tests q (m_traversal_paths_with_witness M q RepSets m)))"
        proof -
          have "prefix_pair_tests q (m_traversal_paths_with_witness M q RepSets m) \<subseteq> 
                    (\<Union> (p, rd, dr)\<in>m_traversal_paths_with_witness M q RepSets m . \<Union> (p1, p2) \<in> set (prefix_pairs p) .{(q, p1, target q p2), (q, p2, target q p1)})"
            unfolding prefix_pair_tests.simps by blast
          moreover have "finite (\<Union> (p, rd, dr)\<in>m_traversal_paths_with_witness M q RepSets m . \<Union> (p1, p2) \<in> set (prefix_pairs p) .{(q, p1, target q p2), (q, p2, target q p1)})"
          proof -
            have "finite (m_traversal_paths_with_witness M q RepSets m)"
              using m_traversal_paths_with_witness_finite[of M q "RepSets" m] by assumption
            moreover have "\<And> p rd dr . finite (\<Union> (p1, p2) \<in> set (prefix_pairs p) .{(q, p1, target q p2), (q, p2, target q p1)})"
              by auto
            ultimately show ?thesis by force
          qed
          ultimately show ?thesis using infinite_super by blast
        qed

        moreover have "finite ((\<lambda>(q, p, y). ((q, p), y)) ` (\<Union>q\<in>fst ` d_reachable_states_with_preambles M.
                 \<Union>mrsps\<in>{m_traversal_paths_with_witness M q RepSets m}.
                    preamble_prefix_tests q mrsps (fst ` d_reachable_states_with_preambles M)))"
        proof -
          have "finite (fst ` d_reachable_states_with_preambles M)" using \<open>finite states_with_preambles\<close> unfolding states_with_preambles_def by auto
          moreover have "\<And> q . q\<in>fst ` d_reachable_states_with_preambles M \<Longrightarrow> finite (\<Union>mrsps\<in>{m_traversal_paths_with_witness M q RepSets m}. preamble_prefix_tests q mrsps (fst ` d_reachable_states_with_preambles M))"
          proof -
            fix q assume "q\<in>fst ` d_reachable_states_with_preambles M"

            have "finite {m_traversal_paths_with_witness M q RepSets m}" by simp
            moreover have "\<And> mrsps . mrsps\<in>{m_traversal_paths_with_witness M q RepSets m} \<Longrightarrow> finite (preamble_prefix_tests q mrsps (fst ` d_reachable_states_with_preambles M))"
            proof -
              fix mrsps assume "mrsps\<in>{m_traversal_paths_with_witness M q RepSets m}"
              then have *: "mrsps = m_traversal_paths_with_witness M q RepSets m" by simp


              have "preamble_prefix_tests q mrsps (fst ` d_reachable_states_with_preambles M) 
                      \<subseteq> (\<Union> (p,rd,dr) \<in> m_traversal_paths_with_witness M q RepSets m . \<Union> q2 \<in> (fst ` d_reachable_states_with_preambles M) . (\<Union> p1 \<in> set (prefixes p) . {(q,p1,q2), (q2,[],(target q p1))}))"              
                unfolding preamble_prefix_tests_def * prefixes_set by blast
              moreover have "finite (\<Union> (p,rd,dr) \<in> m_traversal_paths_with_witness M q RepSets m . \<Union> q2 \<in> (fst ` d_reachable_states_with_preambles M) . (\<Union> p1 \<in> set (prefixes p) . {(q,p1,q2), (q2,[],(target q p1))}))"
              proof -
                have "finite (m_traversal_paths_with_witness M q RepSets m)"
                  using m_traversal_paths_with_witness_finite by metis
                moreover have "\<And> p rd dr . (p,rd,dr) \<in> m_traversal_paths_with_witness M q RepSets m \<Longrightarrow> finite (\<Union> q2 \<in> (fst ` d_reachable_states_with_preambles M) . (\<Union> p1 \<in> set (prefixes p) . {(q,p1,q2), (q2,[],(target q p1))}))"
                  using \<open>finite (fst ` d_reachable_states_with_preambles M)\<close> by blast
                ultimately show ?thesis by force
              qed
              ultimately show "finite (preamble_prefix_tests q mrsps (fst ` d_reachable_states_with_preambles M))" using infinite_super by blast
            qed
            ultimately show "finite (\<Union>mrsps\<in>{m_traversal_paths_with_witness M q RepSets m}. preamble_prefix_tests q mrsps (fst ` d_reachable_states_with_preambles M))" by force
          qed
          ultimately show ?thesis by blast
        qed

        moreover have "finite ((\<lambda>(q, p, y). ((q, p), y)) ` (preamble_pair_tests
              (\<Union>(q, y)\<in>(\<lambda>q. (q, m_traversal_paths_with_witness M q RepSets m)) `
                        fst ` d_reachable_states_with_preambles M.
                  (\<lambda>(p, rd, dr). dr) ` y)
              (fst ` (\<lambda>((q1, q2), A). ((q1, q2), A, Inr q1, Inr q2)) ` r_distinguishable_state_pairs_with_separators M)))"
        proof -

          have "finite (\<Union>(q, y)\<in>(\<lambda>q. (q, m_traversal_paths_with_witness M q RepSets m)) `
                        fst ` d_reachable_states_with_preambles M.
                  (\<lambda>(p, rd, dr). dr) ` y)"
          proof -

            have *: "(\<Union>(q, y)\<in>(\<lambda>q. (q, m_traversal_paths_with_witness M q RepSets m)) `
                        fst ` d_reachable_states_with_preambles M.
                  (\<lambda>(p, rd, dr). dr) ` y) =
                  (\<Union> q \<in> fst ` d_reachable_states_with_preambles M . \<Union> (p, rd, dr) \<in> m_traversal_paths_with_witness M q RepSets m . {dr})"
              by force

            have "finite (\<Union> q \<in> fst ` d_reachable_states_with_preambles M . \<Union> (p, rd, dr) \<in> m_traversal_paths_with_witness M q RepSets m . {dr})"
            proof -
              have "finite (fst ` d_reachable_states_with_preambles M)"
                using \<open>finite states_with_preambles\<close> unfolding states_with_preambles_def by auto

              moreover have "\<And>q . q \<in> fst ` d_reachable_states_with_preambles M \<Longrightarrow> finite (\<Union> (p, rd, dr) \<in> m_traversal_paths_with_witness M q RepSets m . {dr})"
              proof -
                fix q assume "q \<in> fst ` d_reachable_states_with_preambles M"

                have "finite (m_traversal_paths_with_witness M q RepSets m)"
                  using  m_traversal_paths_with_witness_finite by metis 
                moreover have "\<And> p rd dr . (p, rd, dr) \<in> m_traversal_paths_with_witness M q RepSets m \<Longrightarrow> finite {dr}"
                  by simp
                ultimately show "finite (\<Union> (p, rd, dr) \<in> m_traversal_paths_with_witness M q RepSets m . {dr})"
                  by force
              qed
              ultimately show ?thesis by blast
            qed
            then show ?thesis unfolding * by assumption
          qed
          moreover have "finite (fst ` (\<lambda>((q1, q2), A). ((q1, q2), A, Inr q1, Inr q2)) ` r_distinguishable_state_pairs_with_separators M)"
          proof - 
            have "(fst ` (\<lambda>((q1, q2), A). ((q1, q2), A, Inr q1, Inr q2)) ` r_distinguishable_state_pairs_with_separators M) \<subseteq> states M \<times> states M"
              unfolding r_distinguishable_state_pairs_with_separators_def by auto
            moreover have "finite (states M \<times> states M)"
              using fsm_states_finite by auto
            ultimately show ?thesis using infinite_super by blast
          qed
          ultimately show ?thesis
            unfolding preamble_pair_tests.simps by blast
        qed

        ultimately show ?thesis 
          unfolding * by blast
          
      qed

      show "finite (rd_targets (q, p))"
        unfolding rd_targets_alt_def[OF \<open>q \<in> fst ` d_reachable_states_with_preambles M\<close>] 
        using finite_snd_helper[of _ q p, OF *] by assumption
    qed

    
    moreover have "\<And> q q'. finite (atcs (q, q'))"
    proof -
      fix q q' 
      show "finite (atcs (q,q'))" proof (cases "set_as_map ((\<lambda>((q1, q2), A). ((q1, q2), A, Inr q1:: ('a \<times> 'a) + 'a, Inr q2 :: ('a \<times> 'a) + 'a)) ` r_distinguishable_state_pairs_with_separators M) (q, q')")
        case None
        then have "atcs (q, q') = {}" unfolding atcs_def by auto
        then show ?thesis by auto
      next
        case (Some a)
        then have "atcs (q, q') = a" unfolding atcs_def by auto
        then have *: "atcs (q, q') = {z. ((q, q'), z) \<in> (\<lambda>((q1, q2), A). ((q1, q2), A, Inr q1:: ('a \<times> 'a) + 'a, Inr q2:: ('a \<times> 'a) + 'a)) ` r_distinguishable_state_pairs_with_separators M}" using Some unfolding set_as_map_def
          by (metis (no_types, lifting) option.distinct(1) option.inject) 


        have "finite (r_distinguishable_state_pairs_with_separators M)"
        proof -
          have "r_distinguishable_state_pairs_with_separators M \<subseteq> (\<Union> q1 \<in> states M . \<Union> q2 \<in> states M . {((q1,q2), the (state_separator_from_s_states M q1 q2)), ((q1,q2), the (state_separator_from_s_states M q2 q1))})"
          proof 
            fix x assume "x \<in> r_distinguishable_state_pairs_with_separators M"
            then obtain q1 q2 Sep where "x = ((q1,q2),Sep)"
                                    and "q1 \<in> states M"
                                    and "q2 \<in> states M"
                                    and "(q1 < q2 \<and> state_separator_from_s_states M q1 q2 = Some Sep) \<or> (q2 < q1 \<and> state_separator_from_s_states M q2 q1 = Some Sep)"
              unfolding r_distinguishable_state_pairs_with_separators_def by blast
            then consider "state_separator_from_s_states M q1 q2 = Some Sep" | "state_separator_from_s_states M q2 q1 = Some Sep" by blast

            then show "x \<in> (\<Union> q1 \<in> states M . \<Union> q2 \<in> states M . {((q1,q2), the (state_separator_from_s_states M q1 q2)), ((q1,q2), the (state_separator_from_s_states M q2 q1))})"
              using \<open>q1 \<in> states M\<close> \<open>q2 \<in> states M\<close> unfolding \<open>x = ((q1,q2),Sep)\<close> by (cases; force)
          qed

          moreover have "finite (\<Union> q1 \<in> states M . \<Union> q2 \<in> states M . {((q1,q2), the (state_separator_from_s_states M q1 q2)), ((q1,q2), the (state_separator_from_s_states M q2 q1))})"
            using fsm_states_finite[of M] by force

          ultimately show ?thesis using infinite_super by blast
        qed
        then show ?thesis unfolding * by (simp add: finite_snd_helper)
      qed
    qed


    ultimately show ?thesis 
      unfolding \<open>calculate_test_suite_for_repetition_sets M m  RepSets = Test_Suite states_with_preambles tps rd_targets atcs\<close>
                is_finite_test_suite.simps 
      by blast
  qed
qed






subsection \<open>Two Complete Example Implementations\<close>

subsubsection \<open>Naive Repetition Set Strategy\<close>

definition calculate_test_suite_naive :: "('a::linorder,'b::linorder,'c) fsm \<Rightarrow> nat \<Rightarrow> ('a,'b,'c, ('a \<times> 'a) + 'a) test_suite" where
  "calculate_test_suite_naive M m = calculate_test_suite_for_repetition_sets M m (maximal_repetition_sets_from_separators_list_naive M)" 

definition calculate_test_suite_naive_as_io_sequences :: "('a::linorder,'b::linorder,'c) fsm \<Rightarrow> nat \<Rightarrow> ('b \<times> 'c) list set" where
  "calculate_test_suite_naive_as_io_sequences M m = test_suite_to_io_maximal M (calculate_test_suite_naive M m)"


lemma calculate_test_suite_naive_completeness :
  fixes M :: "('a::linorder,'b::linorder,'c) fsm"
  assumes "observable M" 
  and     "observable M'"
  and     "inputs M' = inputs M"
  and     "inputs M \<noteq> {}"
  and     "completely_specified M"
  and     "completely_specified M'"
  and     "size M' \<le> m"
shows     "(L M' \<subseteq> L M) \<longleftrightarrow> passes_test_suite M (calculate_test_suite_naive M m) M'"
and       "(L M' \<subseteq> L M) \<longleftrightarrow> pass_io_set_maximal M' (calculate_test_suite_naive_as_io_sequences M m)"
proof -

  have  "\<And>q. q \<in> FSM.states M \<Longrightarrow> \<exists>d\<in>set (maximal_repetition_sets_from_separators_list_naive M). q \<in> fst d"
    unfolding maximal_repetition_sets_from_separators_list_naive_def Let_def
    by (metis (mono_tags, lifting) list.set_map maximal_pairwise_r_distinguishable_state_sets_from_separators_code maximal_repetition_sets_from_separators_code maximal_repetition_sets_from_separators_cover)
  moreover have "\<And>d. d \<in> set (maximal_repetition_sets_from_separators_list_naive M) \<Longrightarrow> fst d \<subseteq> states M \<and> (snd d = fst d \<inter> fst ` d_reachable_states_with_preambles M)" 
            and "\<And> d q1 q2. d \<in> set (maximal_repetition_sets_from_separators_list_naive M) \<Longrightarrow> q1\<in>fst d \<Longrightarrow> q2\<in>fst d \<Longrightarrow> q1 \<noteq> q2 \<Longrightarrow> (q1, q2) \<in> fst ` r_distinguishable_state_pairs_with_separators M"
  proof 
    fix d assume "d \<in> set (maximal_repetition_sets_from_separators_list_naive M)"
    then have "d \<in> maximal_repetition_sets_from_separators M"
      by (simp add: maximal_repetition_sets_from_separators_code_alt)
      

    then show "fst d \<subseteq> states M" and "(snd d = fst d \<inter> fst ` d_reachable_states_with_preambles M)" 
          and "\<And> q1 q2 . q1\<in>fst d \<Longrightarrow> q2\<in>fst d \<Longrightarrow> q1 \<noteq> q2 \<Longrightarrow> (q1, q2) \<in> fst ` r_distinguishable_state_pairs_with_separators M"
      unfolding maximal_repetition_sets_from_separators_def 
                maximal_pairwise_r_distinguishable_state_sets_from_separators_def
                pairwise_r_distinguishable_state_sets_from_separators_def 
      by force+
  qed
  ultimately have "implies_completeness (calculate_test_suite_naive M m) M m"
             and  "is_finite_test_suite (calculate_test_suite_naive M m)"
    using calculate_test_suite_for_repetition_sets_sufficient_and_finite[OF \<open>observable M\<close> \<open>completely_specified M\<close> \<open>inputs M \<noteq> {}\<close>]
    unfolding calculate_test_suite_naive_def by force+

  then show "(L M' \<subseteq> L M) \<longleftrightarrow> passes_test_suite M (calculate_test_suite_naive M m) M'"
       and  "(L M' \<subseteq> L M) \<longleftrightarrow> pass_io_set_maximal M' (calculate_test_suite_naive_as_io_sequences M m)"
    using passes_test_suite_completeness[OF _ assms] 
          passes_test_suite_as_maximal_sequences_completeness[OF _ _ assms] 
    unfolding calculate_test_suite_naive_as_io_sequences_def
    by blast+
qed


definition calculate_test_suite_naive_as_io_sequences_with_assumption_check :: "('a::linorder,'b::linorder,'c) fsm \<Rightarrow> nat \<Rightarrow> String.literal + (('b \<times> 'c) list set)" where
  "calculate_test_suite_naive_as_io_sequences_with_assumption_check M m = 
    (if inputs M \<noteq> {}
      then if observable M 
        then if completely_specified M
          then (Inr (test_suite_to_io_maximal M (calculate_test_suite_naive M m)))
          else (Inl (STR ''specification is not completely specified''))
        else (Inl (STR ''specification is not observable''))
      else (Inl (STR ''specification has no inputs'')))"

lemma calculate_test_suite_naive_as_io_sequences_with_assumption_check_completeness :
  fixes M :: "('a::linorder,'b::linorder,'c) fsm"
  assumes "observable M'"
  and     "inputs M' = inputs M"
  and     "completely_specified M'"
  and     "size M' \<le> m"
  and     "calculate_test_suite_naive_as_io_sequences_with_assumption_check M m = Inr ts"
shows  "(L M' \<subseteq> L M) \<longleftrightarrow> pass_io_set_maximal M' ts"
proof -

  have "inputs M \<noteq> {}"
  and  "observable M" 
  and  "completely_specified M"
    using \<open>calculate_test_suite_naive_as_io_sequences_with_assumption_check M m = Inr ts\<close>
    unfolding calculate_test_suite_naive_as_io_sequences_with_assumption_check_def 
    by (meson Inl_Inr_False)+ 
  then have "ts = (test_suite_to_io_maximal M (calculate_test_suite_naive M m))"
    using \<open>calculate_test_suite_naive_as_io_sequences_with_assumption_check M m = Inr ts\<close>
    unfolding calculate_test_suite_naive_as_io_sequences_with_assumption_check_def
    by (metis sum.inject(2)) 
  then show ?thesis 
    using calculate_test_suite_naive_completeness(2)[OF \<open>observable M\<close> assms(1,2) \<open>inputs M \<noteq> {}\<close> 
                                                        \<open>completely_specified M\<close> assms(3,4)] 
    unfolding calculate_test_suite_naive_as_io_sequences_def
    by simp
qed



subsubsection \<open>Greedy Repetition Set Strategy\<close>

definition calculate_test_suite_greedy :: "('a::linorder,'b::linorder,'c) fsm \<Rightarrow> nat \<Rightarrow> ('a,'b,'c, ('a \<times> 'a) + 'a) test_suite" where
  "calculate_test_suite_greedy M m = calculate_test_suite_for_repetition_sets M m (maximal_repetition_sets_from_separators_list_greedy M)" 

definition calculate_test_suite_greedy_as_io_sequences :: "('a::linorder,'b::linorder,'c) fsm \<Rightarrow> nat \<Rightarrow> ('b \<times> 'c) list set" where
  "calculate_test_suite_greedy_as_io_sequences M m = test_suite_to_io_maximal M (calculate_test_suite_greedy M m)"

lemma calculate_test_suite_greedy_completeness :
  fixes M :: "('a::linorder,'b::linorder,'c) fsm"
  assumes "observable M" 
  and     "observable M'"
  and     "inputs M' = inputs M"
  and     "inputs M \<noteq> {}"
  and     "completely_specified M"
  and     "completely_specified M'"
  and     "size M' \<le> m"
shows     "(L M' \<subseteq> L M) \<longleftrightarrow> passes_test_suite M (calculate_test_suite_greedy M m) M'"
and       "(L M' \<subseteq> L M) \<longleftrightarrow> pass_io_set_maximal M' (calculate_test_suite_greedy_as_io_sequences M m)"
proof -

  have  "\<And>q. q \<in> FSM.states M \<Longrightarrow> \<exists>d\<in>set (maximal_repetition_sets_from_separators_list_greedy M). q \<in> fst d"
    unfolding maximal_repetition_sets_from_separators_list_greedy_def Let_def
    using greedy_pairwise_r_distinguishable_state_sets_from_separators_cover[of _ M]
    by simp 

  moreover have "\<And>d. d \<in> set (maximal_repetition_sets_from_separators_list_greedy M) \<Longrightarrow> fst d \<subseteq> states M \<and> (snd d = fst d \<inter> fst ` d_reachable_states_with_preambles M)" 
            and "\<And> d q1 q2. d \<in> set (maximal_repetition_sets_from_separators_list_greedy M) \<Longrightarrow> q1\<in>fst d \<Longrightarrow> q2\<in>fst d \<Longrightarrow> q1 \<noteq> q2 \<Longrightarrow> (q1, q2) \<in> fst ` r_distinguishable_state_pairs_with_separators M"
  proof 
    fix d assume "d \<in> set (maximal_repetition_sets_from_separators_list_greedy M)"
    then have "fst d \<in> set (greedy_pairwise_r_distinguishable_state_sets_from_separators M)"
         and  "(snd d = fst d \<inter> fst ` d_reachable_states_with_preambles M)"
      unfolding maximal_repetition_sets_from_separators_list_greedy_def Let_def by force+

    then have "fst d \<in> pairwise_r_distinguishable_state_sets_from_separators M"
      using greedy_pairwise_r_distinguishable_state_sets_from_separators_soundness by blast
    then show "fst d \<subseteq> states M" and "(snd d = fst d \<inter> fst ` d_reachable_states_with_preambles M)" 
          and "\<And> q1 q2 . q1\<in>fst d \<Longrightarrow> q2\<in>fst d \<Longrightarrow> q1 \<noteq> q2 \<Longrightarrow> (q1, q2) \<in> fst ` r_distinguishable_state_pairs_with_separators M"
      using \<open>(snd d = fst d \<inter> fst ` d_reachable_states_with_preambles M)\<close>
      unfolding pairwise_r_distinguishable_state_sets_from_separators_def
      by force+ 
  qed
  ultimately have "implies_completeness (calculate_test_suite_greedy M m) M m"
             and  "is_finite_test_suite (calculate_test_suite_greedy M m)"
    using calculate_test_suite_for_repetition_sets_sufficient_and_finite[OF \<open>observable M\<close> \<open>completely_specified M\<close> \<open>inputs M \<noteq> {}\<close>]
    unfolding calculate_test_suite_greedy_def by force+

  then show "(L M' \<subseteq> L M) \<longleftrightarrow> passes_test_suite M (calculate_test_suite_greedy M m) M'"
       and  "(L M' \<subseteq> L M) \<longleftrightarrow> pass_io_set_maximal M' (calculate_test_suite_greedy_as_io_sequences M m)"
    using passes_test_suite_completeness[OF _ assms] 
          passes_test_suite_as_maximal_sequences_completeness[OF _ _ assms] 
    unfolding calculate_test_suite_greedy_as_io_sequences_def
    by blast+
qed


definition calculate_test_suite_greedy_as_io_sequences_with_assumption_check :: "('a::linorder,'b::linorder,'c) fsm \<Rightarrow> nat \<Rightarrow> String.literal + (('b \<times> 'c) list set)" where
  "calculate_test_suite_greedy_as_io_sequences_with_assumption_check M m = 
    (if inputs M \<noteq> {}
      then if observable M 
        then if completely_specified M
          then (Inr (test_suite_to_io_maximal M (calculate_test_suite_greedy M m)))
          else (Inl (STR ''specification is not completely specified''))
        else (Inl (STR ''specification is not observable''))
      else (Inl (STR ''specification has no inputs'')))"

lemma calculate_test_suite_greedy_as_io_sequences_with_assumption_check_completeness :
  fixes M :: "('a::linorder,'b::linorder,'c) fsm"
  assumes "observable M'"
  and     "inputs M' = inputs M"
  and     "completely_specified M'"
  and     "size M' \<le> m"
  and     "calculate_test_suite_greedy_as_io_sequences_with_assumption_check M m = Inr ts"
shows  "(L M' \<subseteq> L M) \<longleftrightarrow> pass_io_set_maximal M' ts"
proof -

  have "inputs M \<noteq> {}"
  and  "observable M" 
  and  "completely_specified M"
    using \<open>calculate_test_suite_greedy_as_io_sequences_with_assumption_check M m = Inr ts\<close>
    unfolding calculate_test_suite_greedy_as_io_sequences_with_assumption_check_def 
    by (meson Inl_Inr_False)+ 
  then have "ts = (test_suite_to_io_maximal M (calculate_test_suite_greedy M m))"
    using \<open>calculate_test_suite_greedy_as_io_sequences_with_assumption_check M m = Inr ts\<close>
    unfolding calculate_test_suite_greedy_as_io_sequences_with_assumption_check_def
    by (metis sum.inject(2)) 
  then show ?thesis 
    using calculate_test_suite_greedy_completeness(2)[OF \<open>observable M\<close> assms(1,2) \<open>inputs M \<noteq> {}\<close> 
                                                        \<open>completely_specified M\<close> assms(3,4)] 
    unfolding calculate_test_suite_greedy_as_io_sequences_def
    by simp
qed

end