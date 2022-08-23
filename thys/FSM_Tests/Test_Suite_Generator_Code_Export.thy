section \<open>Code Export\<close>

text \<open>This theory exports various functions developed in this library.\<close>

theory Test_Suite_Generator_Code_Export
  imports "EquivalenceTesting/H_Method_Implementations"       
          "EquivalenceTesting/HSI_Method_Implementations"
          "EquivalenceTesting/W_Method_Implementations"
          "EquivalenceTesting/Wp_Method_Implementations"
          "EquivalenceTesting/SPY_Method_Implementations"
          "EquivalenceTesting/SPYH_Method_Implementations"
          "EquivalenceTesting/Partial_S_Method_Implementations"
          "AdaptiveStateCounting/Test_Suite_Calculation_Refined"
          "Prime_Transformation"
          "Prefix_Tree_Refined"
          "EquivalenceTesting/Test_Suite_Representations_Refined"
          "HOL-Library.List_Lexorder"
          "HOL-Library.Code_Target_Nat" 
          "HOL-Library.Code_Target_Int"
          "Native_Word.Uint64"
          FSM_Code_Datatype 
begin


subsection \<open>Reduction Testing\<close>


definition generate_reduction_test_suite_naive :: "(uint64,uint64,uint64) fsm \<Rightarrow> integer \<Rightarrow> String.literal + (uint64\<times>uint64) list list" where
  "generate_reduction_test_suite_naive M m = (case (calculate_test_suite_naive_as_io_sequences_with_assumption_check M (nat_of_integer m)) of
    Inl err \<Rightarrow> Inl err |
    Inr ts \<Rightarrow> Inr (sorted_list_of_set ts))"

definition generate_reduction_test_suite_greedy :: "(uint64,uint64,uint64) fsm \<Rightarrow> integer \<Rightarrow> String.literal + (uint64\<times>uint64) list list" where
  "generate_reduction_test_suite_greedy M m = (case (calculate_test_suite_greedy_as_io_sequences_with_assumption_check M (nat_of_integer m)) of
    Inl err \<Rightarrow> Inl err |
    Inr ts \<Rightarrow> Inr (sorted_list_of_set ts))"

subsubsection \<open>Fault Detection Capabilities of the Test Harness\<close>

text \<open>The test harness for reduction testing (see https://bitbucket.org/RobertSachtleben/an-approach-for-the-verification-and-synthesis-of-complete)
      applies a test suite to a system under test (SUT) by repeatedly applying each IO-sequence 
      (test case) in the test suite input by input to the SUT until either the test case has been
      fully applied or the first output is observed that does not correspond to the outputs in the 
      IO-sequence and then checks whether the observed IO-sequence (consisting of a prefix of the 
      test case possibly followed by an IO-pair consisting of the next input in the test case and an
      output that is not the next output in the test case) is prefix of some test case in the test
      suite. If such a prefix exists, then the application passes, else it fails and the overall
      application is aborted, reporting a failure.

      The following lemma shows that the SUT (whose behaviour corresponds to an FSM @{text "M'"}) 
      conforms to the specification (here FSM @{text "M"}) if and only if the above application 
      procedure does not fail. As the following lemma uses quantification over all possible 
      responses of the SUT to each test case, a further testability hypothesis is required to 
      transfer this result to the actual test application process, which by necessity can only
      perform a finite number of applications: we assume that some value @{text "k"} exists such 
      that by applying each test case @{text "k"} times, all responses of the SUT to it can be 
      observed.\<close> 

lemma reduction_test_harness_soundness :
  fixes M :: "(uint64,uint64,uint64) fsm"
  assumes "observable M'"
  and     "FSM.inputs M' = FSM.inputs M"
  and     "completely_specified M'"
  and     "size M' \<le> nat_of_integer m"
  and     "generate_reduction_test_suite_greedy M m = Inr ts"
shows  "(L M' \<subseteq> L M) \<longleftrightarrow> (list_all  (\<lambda> io . \<not> (\<exists> ioPre x y y' ioSuf . io = ioPre@[(x,y)]@ioSuf \<and> ioPre@[(x,y')] \<in> L M' \<and> \<not>(\<exists> ioSuf' . ioPre@[(x,y')]@ioSuf' \<in> list.set ts))) ts)"
proof -

  obtain tss where "calculate_test_suite_greedy_as_io_sequences_with_assumption_check M (nat_of_integer m) = Inr tss"
    using assms(5) unfolding generate_reduction_test_suite_greedy_def 
    by (metis Inr_Inl_False old.sum.exhaust old.sum.simps(5))


  have "FSM.inputs M \<noteq> {}"
  and  "observable M" 
  and  "completely_specified M"
    using \<open>calculate_test_suite_greedy_as_io_sequences_with_assumption_check M (nat_of_integer m) = Inr tss\<close>
    unfolding calculate_test_suite_greedy_as_io_sequences_with_assumption_check_def 
    by (meson Inl_Inr_False)+ 
  then have "tss = (test_suite_to_io_maximal M (calculate_test_suite_greedy M (nat_of_integer m)))"
    using \<open>calculate_test_suite_greedy_as_io_sequences_with_assumption_check M (nat_of_integer m) = Inr tss\<close>
    unfolding calculate_test_suite_greedy_as_io_sequences_with_assumption_check_def
    by (metis sum.inject(2)) 

  have  "\<And>q. q \<in> FSM.states M \<Longrightarrow> \<exists>d\<in>list.set (maximal_repetition_sets_from_separators_list_greedy M). q \<in> fst d"
    unfolding maximal_repetition_sets_from_separators_list_greedy_def Let_def
    using greedy_pairwise_r_distinguishable_state_sets_from_separators_cover[of _ M]
    by simp 
  moreover have "\<And>d. d \<in> list.set (maximal_repetition_sets_from_separators_list_greedy M) \<Longrightarrow> fst d \<subseteq> FSM.states M \<and> (snd d = fst d \<inter> fst ` d_reachable_states_with_preambles M)" 
            and "\<And> d q1 q2. d \<in> list.set (maximal_repetition_sets_from_separators_list_greedy M) \<Longrightarrow> q1\<in>fst d \<Longrightarrow> q2\<in>fst d \<Longrightarrow> q1 \<noteq> q2 \<Longrightarrow> (q1, q2) \<in> fst ` r_distinguishable_state_pairs_with_separators M"
  proof 
    fix d assume "d \<in> list.set (maximal_repetition_sets_from_separators_list_greedy M)"
    then have "fst d \<in> list.set (greedy_pairwise_r_distinguishable_state_sets_from_separators M)"
         and  "(snd d = fst d \<inter> fst ` d_reachable_states_with_preambles M)"
      unfolding maximal_repetition_sets_from_separators_list_greedy_def Let_def by force+

    then have "fst d \<in> pairwise_r_distinguishable_state_sets_from_separators M"
      using greedy_pairwise_r_distinguishable_state_sets_from_separators_soundness by blast
    then show "fst d \<subseteq> FSM.states M" and "(snd d = fst d \<inter> fst ` d_reachable_states_with_preambles M)" 
          and "\<And> q1 q2 . q1\<in>fst d \<Longrightarrow> q2\<in>fst d \<Longrightarrow> q1 \<noteq> q2 \<Longrightarrow> (q1, q2) \<in> fst ` r_distinguishable_state_pairs_with_separators M"
      using \<open>(snd d = fst d \<inter> fst ` d_reachable_states_with_preambles M)\<close>
      unfolding pairwise_r_distinguishable_state_sets_from_separators_def
      by force+ 
  qed
  ultimately have "implies_completeness (calculate_test_suite_greedy M (nat_of_integer m)) M (nat_of_integer m)"
             and  "is_finite_test_suite (calculate_test_suite_greedy M (nat_of_integer m))"
    using calculate_test_suite_for_repetition_sets_sufficient_and_finite[OF \<open>observable M\<close> \<open>completely_specified M\<close> \<open>FSM.inputs M \<noteq> {}\<close>]
    unfolding calculate_test_suite_greedy_def
    by simp+
    
  then have "finite tss" 
    using test_suite_to_io_maximal_finite[OF _ _ \<open>observable M\<close>] 
    unfolding \<open>tss = (test_suite_to_io_maximal M (calculate_test_suite_greedy M (nat_of_integer m)))\<close>
    by blast 

  have "list.set ts = test_suite_to_io_maximal M (calculate_test_suite_greedy M (nat_of_integer m))"
  and  "ts = sorted_list_of_set tss"
    using sorted_list_of_set(1)[OF \<open>finite tss\<close>]
    using assms(5)
    unfolding \<open>tss = (test_suite_to_io_maximal M (calculate_test_suite_greedy M (nat_of_integer m)))\<close>
              \<open>calculate_test_suite_greedy_as_io_sequences_with_assumption_check M (nat_of_integer m) = Inr tss\<close>
              generate_reduction_test_suite_greedy_def
    by simp+

  then have "(L M' \<subseteq> L M) = pass_io_set_maximal M' (list.set ts)"
    using calculate_test_suite_greedy_as_io_sequences_with_assumption_check_completeness[OF assms(1,2,3,4)]
          \<open>calculate_test_suite_greedy_as_io_sequences_with_assumption_check M (nat_of_integer m) = Inr tss\<close> 
          \<open>tss = test_suite_to_io_maximal M (calculate_test_suite_greedy M (nat_of_integer m))\<close>
    by simp

  moreover have "pass_io_set_maximal M' (list.set ts) 
                  = (list_all (\<lambda> io . \<not> (\<exists> ioPre x y y' ioSuf . io = ioPre@[(x,y)]@ioSuf \<and> ioPre@[(x,y')] \<in> L M' \<and> \<not>(\<exists> ioSuf' . ioPre@[(x,y')]@ioSuf' \<in> list.set ts))) ts)"
  proof -
    have "\<And> P . list_all P (sorted_list_of_set tss) = (\<forall> x \<in> tss . P x)"
      by (simp add: \<open>finite tss\<close> list_all_iff)
    then have scheme: "\<And> P . list_all P ts = (\<forall> x \<in> (list.set ts) . P x)"
      unfolding \<open>ts = sorted_list_of_set tss\<close> sorted_list_of_set(1)[OF \<open>finite tss\<close>] 
      by simp
      
    show ?thesis
      using scheme[of "(\<lambda> io . \<not> (\<exists> ioPre x y y' ioSuf . io = ioPre@[(x,y)]@ioSuf \<and> ioPre@[(x,y')] \<in> L M' \<and> \<not>(\<exists> ioSuf' . ioPre@[(x,y')]@ioSuf' \<in> list.set ts)))"]
      unfolding pass_io_set_maximal_def 
      by fastforce
  qed

  ultimately show ?thesis
    by simp
qed



subsection \<open>Equivalence Testing\<close>

subsubsection \<open>Test Strategy Application and Transformation\<close>


fun apply_method_to_prime :: "(uint64,uint64,uint64) fsm \<Rightarrow> integer \<Rightarrow> bool \<Rightarrow> ((uint64,uint64,uint64) fsm \<Rightarrow> nat \<Rightarrow> (uint64\<times>uint64) prefix_tree) \<Rightarrow> (uint64\<times>uint64) prefix_tree" where
  "apply_method_to_prime M additionalStates isAlreadyPrime f = (let 
    M' = (if isAlreadyPrime then M else to_prime_uint64 M);
    m = size_r M' + (nat_of_integer additionalStates)
  in f M' m)"


lemma apply_method_to_prime_completeness :
  fixes M2 :: "('a,uint64,uint64) fsm"
  assumes "\<And> M1 m (M2 :: ('a,uint64,uint64) fsm) .  
              observable M1 \<Longrightarrow>
              observable M2 \<Longrightarrow>
              minimal M1 \<Longrightarrow>
              minimal M2 \<Longrightarrow>
              size_r M1 \<le> m \<Longrightarrow>
              size M2 \<le> m \<Longrightarrow>
              FSM.inputs M2 = FSM.inputs M1 \<Longrightarrow>
              FSM.outputs M2 = FSM.outputs M1 \<Longrightarrow>
              (L M1 = L M2) \<longleftrightarrow> ((L M1 \<inter> set (f M1 m)) = (L M2 \<inter> set (f M1 m)))"
  and   "observable M2"
  and   "minimal M2"
  and   "size M2 \<le> size_r (to_prime M1) + (nat_of_integer additionalStates)"
  and   "FSM.inputs M2 = FSM.inputs M1"
  and   "FSM.outputs M2 = FSM.outputs M1"
  and   "isAlreadyPrime \<Longrightarrow> observable M1 \<and> minimal M1 \<and> reachable_states M1 = states M1"
  and   "size (to_prime M1) < 2^64"
shows "(L M1 = L M2) \<longleftrightarrow> ((L M1 \<inter> set (apply_method_to_prime M1 additionalStates isAlreadyPrime f)) = (L M2 \<inter> set (apply_method_to_prime M1 additionalStates isAlreadyPrime f)))"
proof -

  define M' where "M' = (if isAlreadyPrime then M1 else to_prime_uint64 M1)"
  have "observable M'" and "minimal M'" and "L M1 = L M'" and "FSM.inputs M' = FSM.inputs M1" and "FSM.outputs M' = FSM.outputs M1"
    unfolding M'_def using to_prime_uint64_props[OF assms(8)] assms(7) 
    by (metis (full_types))+
  then have "FSM.inputs M2 = FSM.inputs M'" and "FSM.outputs M2 = FSM.outputs M'"
    using assms(5,6) by auto

  have "size_r M' = size_r (to_prime M1)"
    by (metis (no_types) \<open>L M1 = L M'\<close> \<open>minimal M'\<close> \<open>observable M'\<close> minimal_equivalence_size_r to_prime_props(1) to_prime_props(2) to_prime_props(3))
  then have "size_r M' \<le> size_r (to_prime M1) + (nat_of_integer additionalStates)"
    by simp

  show ?thesis
    using assms(1)[OF \<open>observable M'\<close> assms(2) \<open>minimal M'\<close> assms(3) \<open>size_r M' \<le> size_r (to_prime M1) + (nat_of_integer additionalStates)\<close> assms(4) \<open>FSM.inputs M2 = FSM.inputs M'\<close> \<open>FSM.outputs M2 = FSM.outputs M'\<close>]
    unfolding apply_method_to_prime.simps Let_def \<open>size_r M' = size_r (to_prime M1)\<close>[symmetric] M'_def \<open>L M1 = L M'\<close> .
qed


fun apply_to_prime_and_return_io_lists :: "(uint64,uint64,uint64) fsm \<Rightarrow> integer \<Rightarrow> bool \<Rightarrow> ((uint64,uint64,uint64) fsm \<Rightarrow> nat \<Rightarrow> (uint64\<times>uint64) prefix_tree) \<Rightarrow> ((uint64\<times>uint64)\<times>bool) list list" where
  "apply_to_prime_and_return_io_lists M additionalStates isAlreadyPrime f = (let M' = (if isAlreadyPrime then M else to_prime_uint64 M) in
    sorted_list_of_maximal_sequences_in_tree (test_suite_from_io_tree M' (FSM.initial M') (apply_method_to_prime M additionalStates isAlreadyPrime f)))"


lemma apply_to_prime_and_return_io_lists_completeness :
  fixes M2 :: "('a,uint64,uint64) fsm"
  assumes "\<And> M1 m (M2 :: ('a,uint64,uint64) fsm) .  
              observable M1 \<Longrightarrow>
              observable M2 \<Longrightarrow>
              minimal M1 \<Longrightarrow>
              minimal M2 \<Longrightarrow>
              size_r M1 \<le> m \<Longrightarrow>
              size M2 \<le> m \<Longrightarrow>
              FSM.inputs M2 = FSM.inputs M1 \<Longrightarrow>
              FSM.outputs M2 = FSM.outputs M1 \<Longrightarrow>
              ((L M1 = L M2) \<longleftrightarrow> ((L M1 \<inter> set (f M1 m)) = (L M2 \<inter> set (f M1 m))))
                \<and> finite_tree (f M1 m)"
  and   "observable M2"
  and   "minimal M2"
  and   "size M2 \<le> size_r (to_prime M1) + (nat_of_integer additionalStates)"
  and   "FSM.inputs M2 = FSM.inputs M1"
  and   "FSM.outputs M2 = FSM.outputs M1"
  and   "isAlreadyPrime \<Longrightarrow> observable M1 \<and> minimal M1 \<and> reachable_states M1 = states M1" 
  and   "size (to_prime M1) < 2^64"
shows "(L M1 = L M2) \<longleftrightarrow> list_all (passes_test_case M2 (FSM.initial M2)) (apply_to_prime_and_return_io_lists M1 additionalStates isAlreadyPrime f)"
proof -

  define M' where "M' = (if isAlreadyPrime then M1 else to_prime_uint64 M1)"
  have "observable M'" and "minimal M'" and "L M1 = L M'" and "FSM.inputs M' = FSM.inputs M1" and "FSM.outputs M' = FSM.outputs M1"
    unfolding M'_def using to_prime_uint64_props[OF assms(8)] assms(7) 
    by (metis (full_types))+
  then have "FSM.inputs M2 = FSM.inputs M'" and "FSM.outputs M2 = FSM.outputs M'"
    using assms(5,6) by auto

  have "L M' = L (to_prime M1)"
    using to_prime_props(1) M'_def
    using \<open>L M1 = L M'\<close> by blast
  
  have "size_r M' = size_r (to_prime M1)" 
    using minimal_equivalence_size_r[OF \<open>minimal M'\<close> _ \<open>observable M'\<close> _ \<open>L M' = L (to_prime M1)\<close>]
    using assms(7) to_prime_props(2,3)
    unfolding M'_def
    by blast 
  then have "size_r M' \<le> size_r (to_prime M1) + (nat_of_integer additionalStates)"
    by simp

  have *:"(L M1 = L M2) \<longleftrightarrow> ((L M1 \<inter> set (f M' (size_r (to_prime M1) + nat_of_integer additionalStates))) = (L M2 \<inter> set (f M' (size_r (to_prime M1) + nat_of_integer additionalStates))))"
   and **:"finite_tree (f M' (size_r (to_prime M1) + nat_of_integer additionalStates))"
    using assms(1)[OF \<open>observable M'\<close> assms(2) \<open>minimal M'\<close> assms(3) \<open>size_r M' \<le> size_r (to_prime M1) + (nat_of_integer additionalStates)\<close> assms(4) \<open>FSM.inputs M2 = FSM.inputs M'\<close> \<open>FSM.outputs M2 = FSM.outputs M'\<close>]
    unfolding \<open>L M1 = L M'\<close> by blast+

  show ?thesis
    unfolding *
    using passes_test_cases_from_io_tree[OF \<open>observable M'\<close> assms(2) fsm_initial[of M'] fsm_initial[of M2] ** ]
    unfolding \<open>size_r M' = size_r (to_prime M1)\<close>[symmetric]
    unfolding apply_to_prime_and_return_io_lists.simps apply_method_to_prime.simps Let_def \<open>L M1 = L M'\<close>
    unfolding M'_def by blast
qed

     
fun apply_to_prime_and_return_input_lists :: "(uint64,uint64,uint64) fsm \<Rightarrow> integer \<Rightarrow> bool \<Rightarrow> ((uint64,uint64,uint64) fsm \<Rightarrow> nat \<Rightarrow> (uint64\<times>uint64) prefix_tree) \<Rightarrow> uint64 list list" where
  "apply_to_prime_and_return_input_lists M additionalStates isAlreadyPrime f = test_suite_to_input_sequences (apply_method_to_prime M additionalStates isAlreadyPrime f)"    

lemma apply_to_prime_and_return_input_lists_completeness :
  fixes M2 :: "('a,uint64,uint64) fsm"
  assumes "\<And> M1 m (M2 :: ('a,uint64,uint64) fsm) .  
              observable M1 \<Longrightarrow>
              observable M2 \<Longrightarrow>
              minimal M1 \<Longrightarrow>
              minimal M2 \<Longrightarrow>
              size_r M1 \<le> m \<Longrightarrow>
              size M2 \<le> m \<Longrightarrow>
              FSM.inputs M2 = FSM.inputs M1 \<Longrightarrow>
              FSM.outputs M2 = FSM.outputs M1 \<Longrightarrow>
              ((L M1 = L M2) \<longleftrightarrow> ((L M1 \<inter> set (f M1 m)) = (L M2 \<inter> set (f M1 m))))
                \<and> finite_tree (f M1 m)"
  and   "observable M2"
  and   "minimal M2"
  and   "size M2 \<le> size_r (to_prime M1) + (nat_of_integer additionalStates)"
  and   "FSM.inputs M2 = FSM.inputs M1"
  and   "FSM.outputs M2 = FSM.outputs M1"
  and   "isAlreadyPrime \<Longrightarrow> observable M1 \<and> minimal M1 \<and> reachable_states M1 = states M1"
  and   "size (to_prime M1) < 2^64"
shows "(L M1 = L M2) \<longleftrightarrow> (\<forall>xs\<in>list.set (apply_to_prime_and_return_input_lists M1 additionalStates isAlreadyPrime f). \<forall>xs'\<in>list.set (prefixes xs). {io \<in> L M1. map fst io = xs'} = {io \<in> L M2. map fst io = xs'})"
proof -
  define M' where "M' = (if isAlreadyPrime then M1 else to_prime_uint64 M1)"
  have "observable M'" and "minimal M'" and "L M1 = L M'" and "FSM.inputs M' = FSM.inputs M1" and "FSM.outputs M' = FSM.outputs M1"
    unfolding M'_def using to_prime_uint64_props[OF assms(8)] assms(7) 
    by (metis (full_types))+
  then have "FSM.inputs M2 = FSM.inputs M'" and "FSM.outputs M2 = FSM.outputs M'"
    using assms(5,6) by auto

  have "L M' = L (to_prime M1)"
    using to_prime_props(1) M'_def \<open>L M1 = L M'\<close> by metis
  
  have "size_r M' = size_r (to_prime M1)" 
    using minimal_equivalence_size_r[OF \<open>minimal M'\<close> _ \<open>observable M'\<close> _ \<open>L M' = L (to_prime M1)\<close>]
    using assms(7) to_prime_props(2,3)
    unfolding M'_def
    by blast 
  then have "size_r M' \<le> size_r (to_prime M1) + (nat_of_integer additionalStates)"
    by simp

  have *:"(L M1 = L M2) = ((L M1 \<inter> set (f M' (size_r (to_prime M1) + nat_of_integer additionalStates))) = (L M2 \<inter> set (f M' (size_r (to_prime M1) + nat_of_integer additionalStates))))"
   and **:"finite_tree (f M' (size_r (to_prime M1) + nat_of_integer additionalStates))"
    using assms(1)[OF \<open>observable M'\<close> assms(2) \<open>minimal M'\<close> assms(3) \<open>size_r M' \<le> size_r (to_prime M1) + (nat_of_integer additionalStates)\<close> assms(4) \<open>FSM.inputs M2 = FSM.inputs M'\<close> \<open>FSM.outputs M2 = FSM.outputs M'\<close>]
    unfolding \<open>L M1 = L M'\<close> by blast+

  show ?thesis
    using test_suite_to_input_sequences_pass_alt_def[OF ** *] 
    unfolding \<open>size_r M' = size_r (to_prime M1)\<close>[symmetric]
    unfolding apply_to_prime_and_return_input_lists.simps apply_method_to_prime.simps Let_def M'_def .
qed


subsubsection \<open>W-Method\<close>

definition w_method_via_h_framework_ts :: "(uint64,uint64,uint64) fsm \<Rightarrow> integer \<Rightarrow> bool \<Rightarrow> ((uint64\<times>uint64)\<times>bool) list list" where
  "w_method_via_h_framework_ts M additionalStates isAlreadyPrime = apply_to_prime_and_return_io_lists M additionalStates isAlreadyPrime w_method_via_h_framework"

lemma w_method_via_h_framework_ts_completeness :
  assumes "observable M2"
  and   "minimal M2"
  and   "size M2 \<le> size_r (to_prime M1) + (nat_of_integer additionalStates)"
  and   "FSM.inputs M2 = FSM.inputs M1"
  and   "FSM.outputs M2 = FSM.outputs M1"
  and   "isAlreadyPrime \<Longrightarrow> observable M1 \<and> minimal M1 \<and> reachable_states M1 = states M1"
  and   "size (to_prime M1) < 2^64"
shows "(L M1 = L M2) \<longleftrightarrow> list_all (passes_test_case M2 (FSM.initial M2)) (w_method_via_h_framework_ts M1 additionalStates isAlreadyPrime)"
  using apply_to_prime_and_return_io_lists_completeness[where f=w_method_via_h_framework and isAlreadyPrime=isAlreadyPrime, OF _ assms(1,2,3,4,5,6,7)]
  using w_method_via_h_framework_completeness_and_finiteness
  unfolding w_method_via_h_framework_ts_def
  by metis

definition w_method_via_h_framework_input :: "(uint64,uint64,uint64) fsm \<Rightarrow> integer \<Rightarrow> bool \<Rightarrow> uint64 list list" where
  "w_method_via_h_framework_input M additionalStates isAlreadyPrime = apply_to_prime_and_return_input_lists M additionalStates isAlreadyPrime w_method_via_h_framework"

lemma w_method_via_h_framework_input_completeness :
  assumes "observable M2"
  and   "minimal M2"
  and   "size M2 \<le> size_r (to_prime M1) + (nat_of_integer additionalStates)"
  and   "FSM.inputs M2 = FSM.inputs M1"
  and   "FSM.outputs M2 = FSM.outputs M1"
  and   "isAlreadyPrime \<Longrightarrow> observable M1 \<and> minimal M1 \<and> reachable_states M1 = states M1" 
  and   "size (to_prime M1) < 2^64"
shows "(L M1 = L M2) \<longleftrightarrow> (\<forall>xs\<in>list.set (w_method_via_h_framework_input M1 additionalStates isAlreadyPrime). \<forall>xs'\<in>list.set (prefixes xs). {io \<in> L M1. map fst io = xs'} = {io \<in> L M2. map fst io = xs'})"
  using apply_to_prime_and_return_input_lists_completeness[where f=w_method_via_h_framework and isAlreadyPrime=isAlreadyPrime, OF _ assms(1,2,3,4,5,6,7)]
  using w_method_via_h_framework_completeness_and_finiteness
  unfolding w_method_via_h_framework_input_def[symmetric] 
  by (metis (no_types, lifting)) 

definition w_method_via_h_framework_2_ts :: "(uint64,uint64,uint64) fsm \<Rightarrow> integer \<Rightarrow> bool \<Rightarrow> ((uint64\<times>uint64)\<times>bool) list list" where
  "w_method_via_h_framework_2_ts M additionalStates isAlreadyPrime = apply_to_prime_and_return_io_lists M additionalStates isAlreadyPrime w_method_via_h_framework_2"

lemma w_method_via_h_framework_2_ts_completeness :
  assumes "observable M2"
  and   "minimal M2"
  and   "size M2 \<le> size_r (to_prime M1) + (nat_of_integer additionalStates)"
  and   "FSM.inputs M2 = FSM.inputs M1"
  and   "FSM.outputs M2 = FSM.outputs M1"
  and   "isAlreadyPrime \<Longrightarrow> observable M1 \<and> minimal M1 \<and> reachable_states M1 = states M1"
  and   "size (to_prime M1) < 2^64"
shows "(L M1 = L M2) \<longleftrightarrow> list_all (passes_test_case M2 (FSM.initial M2)) (w_method_via_h_framework_2_ts M1 additionalStates isAlreadyPrime)"
  using apply_to_prime_and_return_io_lists_completeness[where f=w_method_via_h_framework_2 and isAlreadyPrime=isAlreadyPrime, OF _ assms(1,2,3,4,5,6,7)]
  using w_method_via_h_framework_2_completeness_and_finiteness
  unfolding w_method_via_h_framework_2_ts_def
  by metis

definition w_method_via_h_framework_2_input :: "(uint64,uint64,uint64) fsm \<Rightarrow> integer \<Rightarrow> bool \<Rightarrow> uint64 list list" where
  "w_method_via_h_framework_2_input M additionalStates isAlreadyPrime = apply_to_prime_and_return_input_lists M additionalStates isAlreadyPrime w_method_via_h_framework_2"

lemma w_method_via_h_framework_2_input_completeness :
  assumes "observable M2"
  and   "minimal M2"
  and   "size M2 \<le> size_r (to_prime M1) + (nat_of_integer additionalStates)"
  and   "FSM.inputs M2 = FSM.inputs M1"
  and   "FSM.outputs M2 = FSM.outputs M1"
  and   "isAlreadyPrime \<Longrightarrow> observable M1 \<and> minimal M1 \<and> reachable_states M1 = states M1" 
  and   "size (to_prime M1) < 2^64"
shows "(L M1 = L M2) \<longleftrightarrow> (\<forall>xs\<in>list.set (w_method_via_h_framework_2_input M1 additionalStates isAlreadyPrime). \<forall>xs'\<in>list.set (prefixes xs). {io \<in> L M1. map fst io = xs'} = {io \<in> L M2. map fst io = xs'})"
  using apply_to_prime_and_return_input_lists_completeness[where f=w_method_via_h_framework_2 and isAlreadyPrime=isAlreadyPrime, OF _ assms(1,2,3,4,5,6,7)]
  using w_method_via_h_framework_2_completeness_and_finiteness
  unfolding w_method_via_h_framework_2_input_def[symmetric] 
  by (metis (no_types, lifting))
  
definition w_method_via_spy_framework_ts :: "(uint64,uint64,uint64) fsm \<Rightarrow> integer \<Rightarrow> bool \<Rightarrow> ((uint64\<times>uint64)\<times>bool) list list" where
  "w_method_via_spy_framework_ts M additionalStates isAlreadyPrime = apply_to_prime_and_return_io_lists M additionalStates isAlreadyPrime w_method_via_spy_framework"

lemma w_method_via_spy_framework_ts_completeness :
  assumes "observable M2"
  and   "minimal M2"
  and   "size M2 \<le> size_r (to_prime M1) + (nat_of_integer additionalStates)"
  and   "FSM.inputs M2 = FSM.inputs M1"
  and   "FSM.outputs M2 = FSM.outputs M1"
  and   "isAlreadyPrime \<Longrightarrow> observable M1 \<and> minimal M1 \<and> reachable_states M1 = states M1"
  and   "size (to_prime M1) < 2^64"
shows "(L M1 = L M2) \<longleftrightarrow> list_all (passes_test_case M2 (FSM.initial M2)) (w_method_via_spy_framework_ts M1 additionalStates isAlreadyPrime)"
  using apply_to_prime_and_return_io_lists_completeness[where f=w_method_via_spy_framework and isAlreadyPrime=isAlreadyPrime, OF _ assms(1,2,3,4,5,6,7)]
  using w_method_via_spy_framework_completeness_and_finiteness
  unfolding w_method_via_spy_framework_ts_def
  by metis

definition w_method_via_spy_framework_input :: "(uint64,uint64,uint64) fsm \<Rightarrow> integer \<Rightarrow> bool \<Rightarrow> uint64 list list" where
  "w_method_via_spy_framework_input M additionalStates isAlreadyPrime = apply_to_prime_and_return_input_lists M additionalStates isAlreadyPrime w_method_via_spy_framework"

lemma w_method_via_spy_framework_input_completeness :
  assumes "observable M2"
  and   "minimal M2"
  and   "size M2 \<le> size_r (to_prime M1) + (nat_of_integer additionalStates)"
  and   "FSM.inputs M2 = FSM.inputs M1"
  and   "FSM.outputs M2 = FSM.outputs M1"
  and   "isAlreadyPrime \<Longrightarrow> observable M1 \<and> minimal M1 \<and> reachable_states M1 = states M1" 
  and   "size (to_prime M1) < 2^64"
shows "(L M1 = L M2) \<longleftrightarrow> (\<forall>xs\<in>list.set (w_method_via_spy_framework_input M1 additionalStates isAlreadyPrime). \<forall>xs'\<in>list.set (prefixes xs). {io \<in> L M1. map fst io = xs'} = {io \<in> L M2. map fst io = xs'})"
  using apply_to_prime_and_return_input_lists_completeness[where f=w_method_via_spy_framework and isAlreadyPrime=isAlreadyPrime, OF _ assms(1,2,3,4,5,6,7)]
  using w_method_via_spy_framework_completeness_and_finiteness
  unfolding w_method_via_spy_framework_input_def[symmetric]
  by (metis (no_types, lifting)) 

definition w_method_via_pair_framework_ts :: "(uint64,uint64,uint64) fsm \<Rightarrow> integer \<Rightarrow> bool \<Rightarrow> ((uint64\<times>uint64)\<times>bool) list list" where
  "w_method_via_pair_framework_ts M additionalStates isAlreadyPrime = apply_to_prime_and_return_io_lists M additionalStates isAlreadyPrime w_method_via_pair_framework"

lemma w_method_via_pair_framework_ts_completeness :
  assumes "observable M2"
  and   "minimal M2"
  and   "size M2 \<le> size_r (to_prime M1) + (nat_of_integer additionalStates)"
  and   "FSM.inputs M2 = FSM.inputs M1"
  and   "FSM.outputs M2 = FSM.outputs M1"
  and   "isAlreadyPrime \<Longrightarrow> observable M1 \<and> minimal M1 \<and> reachable_states M1 = states M1" 
  and   "size (to_prime M1) < 2^64"
shows "(L M1 = L M2) \<longleftrightarrow> list_all (passes_test_case M2 (FSM.initial M2)) (w_method_via_pair_framework_ts M1 additionalStates isAlreadyPrime)"
  using apply_to_prime_and_return_io_lists_completeness[where f=w_method_via_pair_framework and isAlreadyPrime=isAlreadyPrime, OF _ assms(1,2,3,4,5,6,7)]
  using w_method_via_pair_framework_completeness_and_finiteness
  unfolding w_method_via_pair_framework_ts_def
  by metis

definition w_method_via_pair_framework_input :: "(uint64,uint64,uint64) fsm \<Rightarrow> integer \<Rightarrow> bool \<Rightarrow> uint64 list list" where
  "w_method_via_pair_framework_input M additionalStates isAlreadyPrime = apply_to_prime_and_return_input_lists M additionalStates isAlreadyPrime w_method_via_pair_framework"

lemma w_method_via_pair_framework_input_completeness :
  assumes "observable M2"
  and   "minimal M2"
  and   "size M2 \<le> size_r (to_prime M1) + (nat_of_integer additionalStates)"
  and   "FSM.inputs M2 = FSM.inputs M1"
  and   "FSM.outputs M2 = FSM.outputs M1"
  and   "isAlreadyPrime \<Longrightarrow> observable M1 \<and> minimal M1 \<and> reachable_states M1 = states M1" 
  and   "size (to_prime M1) < 2^64"
shows "(L M1 = L M2) \<longleftrightarrow> (\<forall>xs\<in>list.set (w_method_via_pair_framework_input M1 additionalStates isAlreadyPrime). \<forall>xs'\<in>list.set (prefixes xs). {io \<in> L M1. map fst io = xs'} = {io \<in> L M2. map fst io = xs'})"
  using apply_to_prime_and_return_input_lists_completeness[where f=w_method_via_pair_framework and isAlreadyPrime=isAlreadyPrime, OF _ assms(1,2,3,4,5,6,7)]
  using w_method_via_pair_framework_completeness_and_finiteness
  unfolding w_method_via_pair_framework_input_def[symmetric]
  by (metis (no_types, lifting)) 


subsubsection \<open>Wp-Method\<close>

definition wp_method_via_h_framework_ts :: "(uint64,uint64,uint64) fsm \<Rightarrow> integer \<Rightarrow> bool \<Rightarrow> ((uint64\<times>uint64)\<times>bool) list list" where
  "wp_method_via_h_framework_ts M additionalStates isAlreadyPrime = apply_to_prime_and_return_io_lists M additionalStates isAlreadyPrime wp_method_via_h_framework"

lemma wp_method_via_h_framework_ts_completeness :
  assumes "observable M2"
  and   "minimal M2"
  and   "size M2 \<le> size_r (to_prime M1) + (nat_of_integer additionalStates)"
  and   "FSM.inputs M2 = FSM.inputs M1"
  and   "FSM.outputs M2 = FSM.outputs M1"
  and   "isAlreadyPrime \<Longrightarrow> observable M1 \<and> minimal M1 \<and> reachable_states M1 = states M1" 
  and   "size (to_prime M1) < 2^64"
shows "(L M1 = L M2) \<longleftrightarrow> list_all (passes_test_case M2 (FSM.initial M2)) (wp_method_via_h_framework_ts M1 additionalStates isAlreadyPrime)"
  using apply_to_prime_and_return_io_lists_completeness[where f=wp_method_via_h_framework and isAlreadyPrime=isAlreadyPrime, OF _ assms(1,2,3,4,5,6,7)]
  using wp_method_via_h_framework_completeness_and_finiteness
  unfolding wp_method_via_h_framework_ts_def
  by metis

definition wp_method_via_h_framework_input :: "(uint64,uint64,uint64) fsm \<Rightarrow> integer \<Rightarrow> bool \<Rightarrow> uint64 list list" where
  "wp_method_via_h_framework_input M additionalStates isAlreadyPrime = apply_to_prime_and_return_input_lists M additionalStates isAlreadyPrime wp_method_via_h_framework"

lemma wp_method_via_h_framework_input_completeness :
  assumes "observable M2"
  and   "minimal M2"
  and   "size M2 \<le> size_r (to_prime M1) + (nat_of_integer additionalStates)"
  and   "FSM.inputs M2 = FSM.inputs M1"
  and   "FSM.outputs M2 = FSM.outputs M1"
  and   "isAlreadyPrime \<Longrightarrow> observable M1 \<and> minimal M1 \<and> reachable_states M1 = states M1" 
  and   "size (to_prime M1) < 2^64"
shows "(L M1 = L M2) \<longleftrightarrow> (\<forall>xs\<in>list.set (wp_method_via_h_framework_input M1 additionalStates isAlreadyPrime). \<forall>xs'\<in>list.set (prefixes xs). {io \<in> L M1. map fst io = xs'} = {io \<in> L M2. map fst io = xs'})"
  using apply_to_prime_and_return_input_lists_completeness[where f=wp_method_via_h_framework and isAlreadyPrime=isAlreadyPrime, OF _ assms(1,2,3,4,5,6,7)]
  using wp_method_via_h_framework_completeness_and_finiteness
  unfolding wp_method_via_h_framework_input_def[symmetric] 
  by (metis (no_types, lifting)) 
  
definition wp_method_via_spy_framework_ts :: "(uint64,uint64,uint64) fsm \<Rightarrow> integer \<Rightarrow> bool \<Rightarrow> ((uint64\<times>uint64)\<times>bool) list list" where
  "wp_method_via_spy_framework_ts M additionalStates isAlreadyPrime = apply_to_prime_and_return_io_lists M additionalStates isAlreadyPrime wp_method_via_spy_framework"

lemma wp_method_via_spy_framework_ts_completeness :
  assumes "observable M2"
  and   "minimal M2"
  and   "size M2 \<le> size_r (to_prime M1) + (nat_of_integer additionalStates)"
  and   "FSM.inputs M2 = FSM.inputs M1"
  and   "FSM.outputs M2 = FSM.outputs M1"
  and   "isAlreadyPrime \<Longrightarrow> observable M1 \<and> minimal M1 \<and> reachable_states M1 = states M1" 
  and   "size (to_prime M1) < 2^64"
shows "(L M1 = L M2) \<longleftrightarrow> list_all (passes_test_case M2 (FSM.initial M2)) (wp_method_via_spy_framework_ts M1 additionalStates isAlreadyPrime)"
  using apply_to_prime_and_return_io_lists_completeness[where f=wp_method_via_spy_framework and isAlreadyPrime=isAlreadyPrime, OF _ assms(1,2,3,4,5,6,7)]
  using wp_method_via_spy_framework_completeness_and_finiteness
  unfolding wp_method_via_spy_framework_ts_def
  by metis

definition wp_method_via_spy_framework_input :: "(uint64,uint64,uint64) fsm \<Rightarrow> integer \<Rightarrow> bool \<Rightarrow> uint64 list list" where
  "wp_method_via_spy_framework_input M additionalStates isAlreadyPrime = apply_to_prime_and_return_input_lists M additionalStates isAlreadyPrime wp_method_via_spy_framework"

lemma wp_method_via_spy_framework_input_completeness :
  assumes "observable M2"
  and   "minimal M2"
  and   "size M2 \<le> size_r (to_prime M1) + (nat_of_integer additionalStates)"
  and   "FSM.inputs M2 = FSM.inputs M1"
  and   "FSM.outputs M2 = FSM.outputs M1"
  and   "isAlreadyPrime \<Longrightarrow> observable M1 \<and> minimal M1 \<and> reachable_states M1 = states M1" 
  and   "size (to_prime M1) < 2^64"
shows "(L M1 = L M2) \<longleftrightarrow> (\<forall>xs\<in>list.set (wp_method_via_spy_framework_input M1 additionalStates isAlreadyPrime). \<forall>xs'\<in>list.set (prefixes xs). {io \<in> L M1. map fst io = xs'} = {io \<in> L M2. map fst io = xs'})"
  using apply_to_prime_and_return_input_lists_completeness[where f=wp_method_via_spy_framework and isAlreadyPrime=isAlreadyPrime, OF _ assms(1,2,3,4,5,6,7)]
  using wp_method_via_spy_framework_completeness_and_finiteness
  unfolding wp_method_via_spy_framework_input_def[symmetric]
  by (metis (no_types, lifting)) 


subsubsection \<open>HSI-Method\<close>

definition hsi_method_via_h_framework_ts :: "(uint64,uint64,uint64) fsm \<Rightarrow> integer \<Rightarrow> bool \<Rightarrow> ((uint64\<times>uint64)\<times>bool) list list" where
  "hsi_method_via_h_framework_ts M additionalStates isAlreadyPrime = apply_to_prime_and_return_io_lists M additionalStates isAlreadyPrime hsi_method_via_h_framework"

lemma hsi_method_via_h_framework_ts_completeness :
  assumes "observable M2"
  and   "minimal M2"
  and   "size M2 \<le> size_r (to_prime M1) + (nat_of_integer additionalStates)"
  and   "FSM.inputs M2 = FSM.inputs M1"
  and   "FSM.outputs M2 = FSM.outputs M1"
  and   "isAlreadyPrime \<Longrightarrow> observable M1 \<and> minimal M1 \<and> reachable_states M1 = states M1" 
  and   "size (to_prime M1) < 2^64"
shows "(L M1 = L M2) \<longleftrightarrow> list_all (passes_test_case M2 (FSM.initial M2)) (hsi_method_via_h_framework_ts M1 additionalStates isAlreadyPrime)"
  using apply_to_prime_and_return_io_lists_completeness[where f=hsi_method_via_h_framework and isAlreadyPrime=isAlreadyPrime, OF _ assms(1,2,3,4,5,6,7)]
  using hsi_method_via_h_framework_completeness_and_finiteness
  unfolding hsi_method_via_h_framework_ts_def
  by metis

definition hsi_method_via_h_framework_input :: "(uint64,uint64,uint64) fsm \<Rightarrow> integer \<Rightarrow> bool \<Rightarrow> uint64 list list" where
  "hsi_method_via_h_framework_input M additionalStates isAlreadyPrime = apply_to_prime_and_return_input_lists M additionalStates isAlreadyPrime hsi_method_via_h_framework"

lemma hsi_method_via_h_framework_input_completeness :
  assumes "observable M2"
  and   "minimal M2"
  and   "size M2 \<le> size_r (to_prime M1) + (nat_of_integer additionalStates)"
  and   "FSM.inputs M2 = FSM.inputs M1"
  and   "FSM.outputs M2 = FSM.outputs M1"
  and   "isAlreadyPrime \<Longrightarrow> observable M1 \<and> minimal M1 \<and> reachable_states M1 = states M1" 
  and   "size (to_prime M1) < 2^64"
shows "(L M1 = L M2) \<longleftrightarrow> (\<forall>xs\<in>list.set (hsi_method_via_h_framework_input M1 additionalStates isAlreadyPrime). \<forall>xs'\<in>list.set (prefixes xs). {io \<in> L M1. map fst io = xs'} = {io \<in> L M2. map fst io = xs'})"
  using apply_to_prime_and_return_input_lists_completeness[where f=hsi_method_via_h_framework and isAlreadyPrime=isAlreadyPrime, OF _ assms(1,2,3,4,5,6,7)]
  using hsi_method_via_h_framework_completeness_and_finiteness
  unfolding hsi_method_via_h_framework_input_def[symmetric] 
  by (metis (no_types, lifting)) 
  
definition hsi_method_via_spy_framework_ts :: "(uint64,uint64,uint64) fsm \<Rightarrow> integer \<Rightarrow> bool \<Rightarrow> ((uint64\<times>uint64)\<times>bool) list list" where
  "hsi_method_via_spy_framework_ts M additionalStates isAlreadyPrime = apply_to_prime_and_return_io_lists M additionalStates isAlreadyPrime hsi_method_via_spy_framework"

lemma hsi_method_via_spy_framework_ts_completeness :
  assumes "observable M2"
  and   "minimal M2"
  and   "size M2 \<le> size_r (to_prime M1) + (nat_of_integer additionalStates)"
  and   "FSM.inputs M2 = FSM.inputs M1"
  and   "FSM.outputs M2 = FSM.outputs M1"
  and   "isAlreadyPrime \<Longrightarrow> observable M1 \<and> minimal M1 \<and> reachable_states M1 = states M1" 
  and   "size (to_prime M1) < 2^64"
shows "(L M1 = L M2) \<longleftrightarrow> list_all (passes_test_case M2 (FSM.initial M2)) (hsi_method_via_spy_framework_ts M1 additionalStates isAlreadyPrime)"
  using apply_to_prime_and_return_io_lists_completeness[where f=hsi_method_via_spy_framework and isAlreadyPrime=isAlreadyPrime, OF _ assms(1,2,3,4,5,6,7)]
  using hsi_method_via_spy_framework_completeness_and_finiteness
  unfolding hsi_method_via_spy_framework_ts_def
  by metis

definition hsi_method_via_spy_framework_input :: "(uint64,uint64,uint64) fsm \<Rightarrow> integer \<Rightarrow> bool \<Rightarrow> uint64 list list" where
  "hsi_method_via_spy_framework_input M additionalStates isAlreadyPrime = apply_to_prime_and_return_input_lists M additionalStates isAlreadyPrime hsi_method_via_spy_framework"

lemma hsi_method_via_spy_framework_input_completeness :
  assumes "observable M2"
  and   "minimal M2"
  and   "size M2 \<le> size_r (to_prime M1) + (nat_of_integer additionalStates)"
  and   "FSM.inputs M2 = FSM.inputs M1"
  and   "FSM.outputs M2 = FSM.outputs M1"
  and   "isAlreadyPrime \<Longrightarrow> observable M1 \<and> minimal M1 \<and> reachable_states M1 = states M1" 
  and   "size (to_prime M1) < 2^64"
shows "(L M1 = L M2) \<longleftrightarrow> (\<forall>xs\<in>list.set (hsi_method_via_spy_framework_input M1 additionalStates isAlreadyPrime). \<forall>xs'\<in>list.set (prefixes xs). {io \<in> L M1. map fst io = xs'} = {io \<in> L M2. map fst io = xs'})"
  using apply_to_prime_and_return_input_lists_completeness[where f=hsi_method_via_spy_framework and isAlreadyPrime=isAlreadyPrime, OF _ assms(1,2,3,4,5,6,7)]
  using hsi_method_via_spy_framework_completeness_and_finiteness
  unfolding hsi_method_via_spy_framework_input_def[symmetric]
  by (metis (no_types, lifting)) 

definition hsi_method_via_pair_framework_ts :: "(uint64,uint64,uint64) fsm \<Rightarrow> integer \<Rightarrow> bool \<Rightarrow> ((uint64\<times>uint64)\<times>bool) list list" where
  "hsi_method_via_pair_framework_ts M additionalStates isAlreadyPrime = apply_to_prime_and_return_io_lists M additionalStates isAlreadyPrime hsi_method_via_pair_framework"

lemma hsi_method_via_pair_framework_ts_completeness :
  assumes "observable M2"
  and   "minimal M2"
  and   "size M2 \<le> size_r (to_prime M1) + (nat_of_integer additionalStates)"
  and   "FSM.inputs M2 = FSM.inputs M1"
  and   "FSM.outputs M2 = FSM.outputs M1"
  and   "isAlreadyPrime \<Longrightarrow> observable M1 \<and> minimal M1 \<and> reachable_states M1 = states M1" 
  and   "size (to_prime M1) < 2^64"
shows "(L M1 = L M2) \<longleftrightarrow> list_all (passes_test_case M2 (FSM.initial M2)) (hsi_method_via_pair_framework_ts M1 additionalStates isAlreadyPrime)"
  using apply_to_prime_and_return_io_lists_completeness[where f=hsi_method_via_pair_framework and isAlreadyPrime=isAlreadyPrime, OF _ assms(1,2,3,4,5,6,7)]
  using hsi_method_via_pair_framework_completeness_and_finiteness
  unfolding hsi_method_via_pair_framework_ts_def
  by metis

definition hsi_method_via_pair_framework_input :: "(uint64,uint64,uint64) fsm \<Rightarrow> integer \<Rightarrow> bool \<Rightarrow> uint64 list list" where
  "hsi_method_via_pair_framework_input M additionalStates isAlreadyPrime = apply_to_prime_and_return_input_lists M additionalStates isAlreadyPrime hsi_method_via_pair_framework"

lemma hsi_method_via_pair_framework_input_completeness :
  assumes "observable M2"
  and   "minimal M2"
  and   "size M2 \<le> size_r (to_prime M1) + (nat_of_integer additionalStates)"
  and   "FSM.inputs M2 = FSM.inputs M1"
  and   "FSM.outputs M2 = FSM.outputs M1"
  and   "isAlreadyPrime \<Longrightarrow> observable M1 \<and> minimal M1 \<and> reachable_states M1 = states M1" 
  and   "size (to_prime M1) < 2^64"
shows "(L M1 = L M2) \<longleftrightarrow> (\<forall>xs\<in>list.set (hsi_method_via_pair_framework_input M1 additionalStates isAlreadyPrime). \<forall>xs'\<in>list.set (prefixes xs). {io \<in> L M1. map fst io = xs'} = {io \<in> L M2. map fst io = xs'})"
  using apply_to_prime_and_return_input_lists_completeness[where f=hsi_method_via_pair_framework and isAlreadyPrime=isAlreadyPrime, OF _ assms(1,2,3,4,5,6,7)]
  using hsi_method_via_pair_framework_completeness_and_finiteness
  unfolding hsi_method_via_pair_framework_input_def[symmetric]
  by (metis (no_types, lifting)) 

subsubsection \<open>H-Method\<close>

definition h_method_via_h_framework_ts :: "(uint64,uint64,uint64) fsm \<Rightarrow> integer \<Rightarrow> bool \<Rightarrow> bool \<Rightarrow> bool \<Rightarrow> ((uint64\<times>uint64)\<times>bool) list list" where
  "h_method_via_h_framework_ts M additionalStates isAlreadyPrime c b = apply_to_prime_and_return_io_lists M additionalStates isAlreadyPrime (\<lambda> M m . h_method_via_h_framework M m c b)"

lemma h_method_via_h_framework_ts_completeness :
  assumes "observable M2"
  and   "minimal M2"
  and   "size M2 \<le> size_r (to_prime M1) + (nat_of_integer additionalStates)"
  and   "FSM.inputs M2 = FSM.inputs M1"
  and   "FSM.outputs M2 = FSM.outputs M1"
  and   "isAlreadyPrime \<Longrightarrow> observable M1 \<and> minimal M1 \<and> reachable_states M1 = states M1" 
  and   "size (to_prime M1) < 2^64"
shows "(L M1 = L M2) \<longleftrightarrow> list_all (passes_test_case M2 (FSM.initial M2)) (h_method_via_h_framework_ts M1 additionalStates isAlreadyPrime c b)"
  using apply_to_prime_and_return_io_lists_completeness[where f="(\<lambda> M m . h_method_via_h_framework M m c b)" and isAlreadyPrime=isAlreadyPrime, OF _ assms(1,2,3,4,5,6,7)]
  using h_method_via_h_framework_completeness_and_finiteness
  unfolding h_method_via_h_framework_ts_def
  by metis

definition h_method_via_h_framework_input :: "(uint64,uint64,uint64) fsm \<Rightarrow> integer \<Rightarrow> bool \<Rightarrow> bool \<Rightarrow> bool \<Rightarrow> uint64 list list" where
  "h_method_via_h_framework_input M additionalStates isAlreadyPrime c b = apply_to_prime_and_return_input_lists M additionalStates isAlreadyPrime (\<lambda> M m . h_method_via_h_framework M m c b)"

lemma h_method_via_h_framework_input_completeness :
  assumes "observable M2"
  and   "minimal M2"
  and   "size M2 \<le> size_r (to_prime M1) + (nat_of_integer additionalStates)"
  and   "FSM.inputs M2 = FSM.inputs M1"
  and   "FSM.outputs M2 = FSM.outputs M1"
  and   "isAlreadyPrime \<Longrightarrow> observable M1 \<and> minimal M1 \<and> reachable_states M1 = states M1" 
  and   "size (to_prime M1) < 2^64"
shows "(L M1 = L M2) \<longleftrightarrow> (\<forall>xs\<in>list.set (h_method_via_h_framework_input M1 additionalStates isAlreadyPrime c b). \<forall>xs'\<in>list.set (prefixes xs). {io \<in> L M1. map fst io = xs'} = {io \<in> L M2. map fst io = xs'})"
  using apply_to_prime_and_return_input_lists_completeness[where f="(\<lambda> M m . h_method_via_h_framework M m c b)" and isAlreadyPrime=isAlreadyPrime, OF _ assms(1,2,3,4,5,6,7)]
  using h_method_via_h_framework_completeness_and_finiteness
  unfolding h_method_via_h_framework_input_def[symmetric] 
  by (metis (no_types, lifting)) 
  

definition h_method_via_pair_framework_ts :: "(uint64,uint64,uint64) fsm \<Rightarrow> integer \<Rightarrow> bool \<Rightarrow> ((uint64\<times>uint64)\<times>bool) list list" where
  "h_method_via_pair_framework_ts M additionalStates isAlreadyPrime = apply_to_prime_and_return_io_lists M additionalStates isAlreadyPrime h_method_via_pair_framework"

lemma h_method_via_pair_framework_ts_completeness :
  assumes "observable M2"
  and   "minimal M2"
  and   "size M2 \<le> size_r (to_prime M1) + (nat_of_integer additionalStates)"
  and   "FSM.inputs M2 = FSM.inputs M1"
  and   "FSM.outputs M2 = FSM.outputs M1"
  and   "isAlreadyPrime \<Longrightarrow> observable M1 \<and> minimal M1 \<and> reachable_states M1 = states M1" 
  and   "size (to_prime M1) < 2^64"
shows "(L M1 = L M2) \<longleftrightarrow> list_all (passes_test_case M2 (FSM.initial M2)) (h_method_via_pair_framework_ts M1 additionalStates isAlreadyPrime)"
  using apply_to_prime_and_return_io_lists_completeness[where f=h_method_via_pair_framework and isAlreadyPrime=isAlreadyPrime, OF _ assms(1,2,3,4,5,6,7)]
  using h_method_via_pair_framework_completeness_and_finiteness
  unfolding h_method_via_pair_framework_ts_def
  by metis

definition h_method_via_pair_framework_input :: "(uint64,uint64,uint64) fsm \<Rightarrow> integer \<Rightarrow> bool \<Rightarrow> uint64 list list" where
  "h_method_via_pair_framework_input M additionalStates isAlreadyPrime = apply_to_prime_and_return_input_lists M additionalStates isAlreadyPrime h_method_via_pair_framework"

lemma h_method_via_pair_framework_input_completeness :
  assumes "observable M2"
  and   "minimal M2"
  and   "size M2 \<le> size_r (to_prime M1) + (nat_of_integer additionalStates)"
  and   "FSM.inputs M2 = FSM.inputs M1"
  and   "FSM.outputs M2 = FSM.outputs M1"
  and   "isAlreadyPrime \<Longrightarrow> observable M1 \<and> minimal M1 \<and> reachable_states M1 = states M1" 
  and   "size (to_prime M1) < 2^64"
shows "(L M1 = L M2) \<longleftrightarrow> (\<forall>xs\<in>list.set (h_method_via_pair_framework_input M1 additionalStates isAlreadyPrime). \<forall>xs'\<in>list.set (prefixes xs). {io \<in> L M1. map fst io = xs'} = {io \<in> L M2. map fst io = xs'})"
  using apply_to_prime_and_return_input_lists_completeness[where f=h_method_via_pair_framework and isAlreadyPrime=isAlreadyPrime, OF _ assms(1,2,3,4,5,6,7)]
  using h_method_via_pair_framework_completeness_and_finiteness
  unfolding h_method_via_pair_framework_input_def[symmetric]
  by (metis (no_types, lifting))


definition h_method_via_pair_framework_2_ts :: "(uint64,uint64,uint64) fsm \<Rightarrow> integer \<Rightarrow> bool \<Rightarrow> bool \<Rightarrow> ((uint64\<times>uint64)\<times>bool) list list" where
  "h_method_via_pair_framework_2_ts M additionalStates isAlreadyPrime c = apply_to_prime_and_return_io_lists M additionalStates isAlreadyPrime (\<lambda> M m . h_method_via_pair_framework_2 M m c)"

lemma h_method_via_pair_framework_2_ts_completeness :
  assumes "observable M2"
  and   "minimal M2"
  and   "size M2 \<le> size_r (to_prime M1) + (nat_of_integer additionalStates)"
  and   "FSM.inputs M2 = FSM.inputs M1"
  and   "FSM.outputs M2 = FSM.outputs M1"
  and   "isAlreadyPrime \<Longrightarrow> observable M1 \<and> minimal M1 \<and> reachable_states M1 = states M1" 
  and   "size (to_prime M1) < 2^64"
shows "(L M1 = L M2) \<longleftrightarrow> list_all (passes_test_case M2 (FSM.initial M2)) (h_method_via_pair_framework_2_ts M1 additionalStates isAlreadyPrime c)"
  using apply_to_prime_and_return_io_lists_completeness[where f="(\<lambda> M m . h_method_via_pair_framework_2 M m c)" and isAlreadyPrime=isAlreadyPrime, OF _ assms(1,2,3,4,5,6,7)]
  using h_method_via_pair_framework_2_completeness_and_finiteness
  unfolding h_method_via_pair_framework_2_ts_def
  by metis

definition h_method_via_pair_framework_2_input :: "(uint64,uint64,uint64) fsm \<Rightarrow> integer \<Rightarrow> bool \<Rightarrow> bool \<Rightarrow> uint64 list list" where
  "h_method_via_pair_framework_2_input M additionalStates isAlreadyPrime c = apply_to_prime_and_return_input_lists M additionalStates isAlreadyPrime (\<lambda> M m . h_method_via_pair_framework_2 M m c)"

lemma h_method_via_pair_framework_2_input_completeness :
  assumes "observable M2"
  and   "minimal M2"
  and   "size M2 \<le> size_r (to_prime M1) + (nat_of_integer additionalStates)"
  and   "FSM.inputs M2 = FSM.inputs M1"
  and   "FSM.outputs M2 = FSM.outputs M1"
  and   "isAlreadyPrime \<Longrightarrow> observable M1 \<and> minimal M1 \<and> reachable_states M1 = states M1" 
  and   "size (to_prime M1) < 2^64"
shows "(L M1 = L M2) \<longleftrightarrow> (\<forall>xs\<in>list.set (h_method_via_pair_framework_2_input M1 additionalStates isAlreadyPrime c). \<forall>xs'\<in>list.set (prefixes xs). {io \<in> L M1. map fst io = xs'} = {io \<in> L M2. map fst io = xs'})"
  using apply_to_prime_and_return_input_lists_completeness[where f="(\<lambda> M m . h_method_via_pair_framework_2 M m c)" and isAlreadyPrime=isAlreadyPrime, OF _ assms(1,2,3,4,5,6,7)]
  using h_method_via_pair_framework_2_completeness_and_finiteness
  unfolding h_method_via_pair_framework_2_input_def[symmetric]
  by (metis (no_types, lifting))


definition h_method_via_pair_framework_3_ts :: "(uint64,uint64,uint64) fsm \<Rightarrow> integer \<Rightarrow> bool \<Rightarrow> bool \<Rightarrow> bool \<Rightarrow> ((uint64\<times>uint64)\<times>bool) list list" where
  "h_method_via_pair_framework_3_ts M additionalStates isAlreadyPrime c1 c2 = apply_to_prime_and_return_io_lists M additionalStates isAlreadyPrime (\<lambda> M m . h_method_via_pair_framework_3 M m c1 c2)"

lemma h_method_via_pair_framework_3_ts_completeness :
  assumes "observable M2"
  and   "minimal M2"
  and   "size M2 \<le> size_r (to_prime M1) + (nat_of_integer additionalStates)"
  and   "FSM.inputs M2 = FSM.inputs M1"
  and   "FSM.outputs M2 = FSM.outputs M1"
  and   "isAlreadyPrime \<Longrightarrow> observable M1 \<and> minimal M1 \<and> reachable_states M1 = states M1" 
  and   "size (to_prime M1) < 2^64"
shows "(L M1 = L M2) \<longleftrightarrow> list_all (passes_test_case M2 (FSM.initial M2)) (h_method_via_pair_framework_3_ts M1 additionalStates isAlreadyPrime c1 c2)"
  using apply_to_prime_and_return_io_lists_completeness[where f="(\<lambda> M m . h_method_via_pair_framework_3 M m c1 c2)" and isAlreadyPrime=isAlreadyPrime, OF _ assms(1,2,3,4,5,6,7)]
  using h_method_via_pair_framework_3_completeness_and_finiteness
  unfolding h_method_via_pair_framework_3_ts_def
  by metis

definition h_method_via_pair_framework_3_input :: "(uint64,uint64,uint64) fsm \<Rightarrow> integer \<Rightarrow> bool \<Rightarrow> bool \<Rightarrow> bool \<Rightarrow> uint64 list list" where
  "h_method_via_pair_framework_3_input M additionalStates isAlreadyPrime c1 c2 = apply_to_prime_and_return_input_lists M additionalStates isAlreadyPrime (\<lambda> M m . h_method_via_pair_framework_3 M m c1 c2)"

lemma h_method_via_pair_framework_3_input_completeness :
  assumes "observable M2"
  and   "minimal M2"
  and   "size M2 \<le> size_r (to_prime M1) + (nat_of_integer additionalStates)"
  and   "FSM.inputs M2 = FSM.inputs M1"
  and   "FSM.outputs M2 = FSM.outputs M1"
  and   "isAlreadyPrime \<Longrightarrow> observable M1 \<and> minimal M1 \<and> reachable_states M1 = states M1" 
  and   "size (to_prime M1) < 2^64"
shows "(L M1 = L M2) \<longleftrightarrow> (\<forall>xs\<in>list.set (h_method_via_pair_framework_3_input M1 additionalStates isAlreadyPrime c1 c2). \<forall>xs'\<in>list.set (prefixes xs). {io \<in> L M1. map fst io = xs'} = {io \<in> L M2. map fst io = xs'})"
  using apply_to_prime_and_return_input_lists_completeness[where f="(\<lambda> M m . h_method_via_pair_framework_3 M m c1 c2)" and isAlreadyPrime=isAlreadyPrime, OF _ assms(1,2,3,4,5,6,7)]
  using h_method_via_pair_framework_3_completeness_and_finiteness
  unfolding h_method_via_pair_framework_3_input_def[symmetric]
  by (metis (no_types, lifting))


subsubsection \<open>SPY-Method\<close>

definition spy_method_via_h_framework_ts :: "(uint64,uint64,uint64) fsm \<Rightarrow> integer \<Rightarrow> bool \<Rightarrow> ((uint64\<times>uint64)\<times>bool) list list" where
  "spy_method_via_h_framework_ts M additionalStates isAlreadyPrime = apply_to_prime_and_return_io_lists M additionalStates isAlreadyPrime spy_method_via_h_framework"

lemma spy_method_via_h_framework_ts_completeness :
  assumes "observable M2"
  and   "minimal M2"
  and   "size M2 \<le> size_r (to_prime M1) + (nat_of_integer additionalStates)"
  and   "FSM.inputs M2 = FSM.inputs M1"
  and   "FSM.outputs M2 = FSM.outputs M1"
  and   "isAlreadyPrime \<Longrightarrow> observable M1 \<and> minimal M1 \<and> reachable_states M1 = states M1"
  and   "size (to_prime M1) < 2^64"
shows "(L M1 = L M2) \<longleftrightarrow> list_all (passes_test_case M2 (FSM.initial M2)) (spy_method_via_h_framework_ts M1 additionalStates isAlreadyPrime)"
  using apply_to_prime_and_return_io_lists_completeness[where f=spy_method_via_h_framework and isAlreadyPrime=isAlreadyPrime, OF _ assms(1,2,3,4,5,6,7)]
  using spy_method_via_h_framework_completeness_and_finiteness
  unfolding spy_method_via_h_framework_ts_def
  by metis

definition spy_method_via_h_framework_input :: "(uint64,uint64,uint64) fsm \<Rightarrow> integer \<Rightarrow> bool \<Rightarrow> uint64 list list" where
  "spy_method_via_h_framework_input M additionalStates isAlreadyPrime = apply_to_prime_and_return_input_lists M additionalStates isAlreadyPrime spy_method_via_h_framework"

lemma spy_method_via_h_framework_input_completeness :
  assumes "observable M2"
  and   "minimal M2"
  and   "size M2 \<le> size_r (to_prime M1) + (nat_of_integer additionalStates)"
  and   "FSM.inputs M2 = FSM.inputs M1"
  and   "FSM.outputs M2 = FSM.outputs M1"
  and   "isAlreadyPrime \<Longrightarrow> observable M1 \<and> minimal M1 \<and> reachable_states M1 = states M1" 
  and   "size (to_prime M1) < 2^64"
shows "(L M1 = L M2) \<longleftrightarrow> (\<forall>xs\<in>list.set (spy_method_via_h_framework_input M1 additionalStates isAlreadyPrime). \<forall>xs'\<in>list.set (prefixes xs). {io \<in> L M1. map fst io = xs'} = {io \<in> L M2. map fst io = xs'})"
  using apply_to_prime_and_return_input_lists_completeness[where f=spy_method_via_h_framework and isAlreadyPrime=isAlreadyPrime, OF _ assms(1,2,3,4,5,6,7)]
  using spy_method_via_h_framework_completeness_and_finiteness
  unfolding spy_method_via_h_framework_input_def[symmetric] 
  by (metis (no_types, lifting)) 
  
definition spy_method_via_spy_framework_ts :: "(uint64,uint64,uint64) fsm \<Rightarrow> integer \<Rightarrow> bool \<Rightarrow> ((uint64\<times>uint64)\<times>bool) list list" where
  "spy_method_via_spy_framework_ts M additionalStates isAlreadyPrime = apply_to_prime_and_return_io_lists M additionalStates isAlreadyPrime spy_method_via_spy_framework"

lemma spy_method_via_spy_framework_ts_completeness :
  assumes "observable M2"
  and   "minimal M2"
  and   "size M2 \<le> size_r (to_prime M1) + (nat_of_integer additionalStates)"
  and   "FSM.inputs M2 = FSM.inputs M1"
  and   "FSM.outputs M2 = FSM.outputs M1"
  and   "isAlreadyPrime \<Longrightarrow> observable M1 \<and> minimal M1 \<and> reachable_states M1 = states M1" 
  and   "size (to_prime M1) < 2^64" 
shows "(L M1 = L M2) \<longleftrightarrow> list_all (passes_test_case M2 (FSM.initial M2)) (spy_method_via_spy_framework_ts M1 additionalStates isAlreadyPrime)"
  using apply_to_prime_and_return_io_lists_completeness[where f=spy_method_via_spy_framework and isAlreadyPrime=isAlreadyPrime, OF _ assms(1,2,3,4,5,6,7)]
  using spy_method_via_spy_framework_completeness_and_finiteness
  unfolding spy_method_via_spy_framework_ts_def
  by metis

definition spy_method_via_spy_framework_input :: "(uint64,uint64,uint64) fsm \<Rightarrow> integer \<Rightarrow> bool \<Rightarrow> uint64 list list" where
  "spy_method_via_spy_framework_input M additionalStates isAlreadyPrime = apply_to_prime_and_return_input_lists M additionalStates isAlreadyPrime spy_method_via_spy_framework"

lemma spy_method_via_spy_framework_input_completeness :
  assumes "observable M2"
  and   "minimal M2"
  and   "size M2 \<le> size_r (to_prime M1) + (nat_of_integer additionalStates)"
  and   "FSM.inputs M2 = FSM.inputs M1"
  and   "FSM.outputs M2 = FSM.outputs M1"
  and   "isAlreadyPrime \<Longrightarrow> observable M1 \<and> minimal M1 \<and> reachable_states M1 = states M1"  
  and   "size (to_prime M1) < 2^64"
shows "(L M1 = L M2) \<longleftrightarrow> (\<forall>xs\<in>list.set (spy_method_via_spy_framework_input M1 additionalStates isAlreadyPrime). \<forall>xs'\<in>list.set (prefixes xs). {io \<in> L M1. map fst io = xs'} = {io \<in> L M2. map fst io = xs'})"
  using apply_to_prime_and_return_input_lists_completeness[where f=spy_method_via_spy_framework and isAlreadyPrime=isAlreadyPrime, OF _ assms(1,2,3,4,5,6,7)]
  using spy_method_via_spy_framework_completeness_and_finiteness
  unfolding spy_method_via_spy_framework_input_def[symmetric]
  by (metis (no_types, lifting)) 


subsubsection \<open>SPYH-Method\<close>

definition spyh_method_via_h_framework_ts :: "(uint64,uint64,uint64) fsm \<Rightarrow> integer \<Rightarrow> bool \<Rightarrow> bool \<Rightarrow> bool \<Rightarrow> ((uint64\<times>uint64)\<times>bool) list list" where
  "spyh_method_via_h_framework_ts M additionalStates isAlreadyPrime c b = apply_to_prime_and_return_io_lists M additionalStates isAlreadyPrime (\<lambda> M m . spyh_method_via_h_framework M m c b)"

lemma spyh_method_via_h_framework_ts_completeness :
  assumes "observable M2"
  and   "minimal M2"
  and   "size M2 \<le> size_r (to_prime M1) + (nat_of_integer additionalStates)"
  and   "FSM.inputs M2 = FSM.inputs M1"
  and   "FSM.outputs M2 = FSM.outputs M1"
  and   "isAlreadyPrime \<Longrightarrow> observable M1 \<and> minimal M1 \<and> reachable_states M1 = states M1" 
  and   "size (to_prime M1) < 2^64" 
shows "(L M1 = L M2) \<longleftrightarrow> list_all (passes_test_case M2 (FSM.initial M2)) (spyh_method_via_h_framework_ts M1 additionalStates isAlreadyPrime c b)"
  using apply_to_prime_and_return_io_lists_completeness[where f="(\<lambda> M m . spyh_method_via_h_framework M m c b)" and isAlreadyPrime=isAlreadyPrime, OF _ assms(1,2,3,4,5,6,7)]
  using spyh_method_via_h_framework_completeness_and_finiteness
  unfolding spyh_method_via_h_framework_ts_def
  by metis

definition spyh_method_via_h_framework_input :: "(uint64,uint64,uint64) fsm \<Rightarrow> integer \<Rightarrow> bool \<Rightarrow> bool \<Rightarrow> bool \<Rightarrow> uint64 list list" where
  "spyh_method_via_h_framework_input M additionalStates isAlreadyPrime c b = apply_to_prime_and_return_input_lists M additionalStates isAlreadyPrime (\<lambda> M m . spyh_method_via_h_framework M m c b)"

lemma spyh_method_via_h_framework_input_completeness :
  assumes "observable M2"
  and   "minimal M2"
  and   "size M2 \<le> size_r (to_prime M1) + (nat_of_integer additionalStates)"
  and   "FSM.inputs M2 = FSM.inputs M1"
  and   "FSM.outputs M2 = FSM.outputs M1"
  and   "isAlreadyPrime \<Longrightarrow> observable M1 \<and> minimal M1 \<and> reachable_states M1 = states M1" 
  and   "size (to_prime M1) < 2^64" 
shows "(L M1 = L M2) \<longleftrightarrow> (\<forall>xs\<in>list.set (spyh_method_via_h_framework_input M1 additionalStates isAlreadyPrime c b). \<forall>xs'\<in>list.set (prefixes xs). {io \<in> L M1. map fst io = xs'} = {io \<in> L M2. map fst io = xs'})"
  using apply_to_prime_and_return_input_lists_completeness[where f="(\<lambda> M m . spyh_method_via_h_framework M m c b)" and isAlreadyPrime=isAlreadyPrime, OF _ assms(1,2,3,4,5,6,7)]
  using spyh_method_via_h_framework_completeness_and_finiteness
  unfolding spyh_method_via_h_framework_input_def[symmetric] 
  by (metis (no_types, lifting)) 
  
definition spyh_method_via_spy_framework_ts :: "(uint64,uint64,uint64) fsm \<Rightarrow> integer \<Rightarrow> bool \<Rightarrow> bool \<Rightarrow> bool \<Rightarrow> ((uint64\<times>uint64)\<times>bool) list list" where
  "spyh_method_via_spy_framework_ts M additionalStates isAlreadyPrime c b = apply_to_prime_and_return_io_lists M additionalStates isAlreadyPrime (\<lambda> M m . spyh_method_via_spy_framework M m c b)"

lemma spyh_method_via_spy_framework_ts_completeness :
  assumes "observable M2"
  and   "minimal M2"
  and   "size M2 \<le> size_r (to_prime M1) + (nat_of_integer additionalStates)"
  and   "FSM.inputs M2 = FSM.inputs M1"
  and   "FSM.outputs M2 = FSM.outputs M1"
  and   "isAlreadyPrime \<Longrightarrow> observable M1 \<and> minimal M1 \<and> reachable_states M1 = states M1" 
  and   "size (to_prime M1) < 2^64" 
shows "(L M1 = L M2) \<longleftrightarrow> list_all (passes_test_case M2 (FSM.initial M2)) (spyh_method_via_spy_framework_ts M1 additionalStates isAlreadyPrime c b)"
  using apply_to_prime_and_return_io_lists_completeness[where f="(\<lambda> M m . spyh_method_via_spy_framework M m c b)" and isAlreadyPrime=isAlreadyPrime, OF _ assms(1,2,3,4,5,6,7)]
  using spyh_method_via_spy_framework_completeness_and_finiteness
  unfolding spyh_method_via_spy_framework_ts_def
  by metis

definition spyh_method_via_spy_framework_input :: "(uint64,uint64,uint64) fsm \<Rightarrow> integer \<Rightarrow> bool \<Rightarrow> bool \<Rightarrow> bool \<Rightarrow> uint64 list list" where
  "spyh_method_via_spy_framework_input M additionalStates isAlreadyPrime c b = apply_to_prime_and_return_input_lists M additionalStates isAlreadyPrime (\<lambda> M m . spyh_method_via_spy_framework M m c b)"

lemma spyh_method_via_spy_framework_input_completeness :
  assumes "observable M2"
  and   "minimal M2"
  and   "size M2 \<le> size_r (to_prime M1) + (nat_of_integer additionalStates)"
  and   "FSM.inputs M2 = FSM.inputs M1"
  and   "FSM.outputs M2 = FSM.outputs M1"
  and   "isAlreadyPrime \<Longrightarrow> observable M1 \<and> minimal M1 \<and> reachable_states M1 = states M1" 
  and   "size (to_prime M1) < 2^64" 
shows "(L M1 = L M2) \<longleftrightarrow> (\<forall>xs\<in>list.set (spyh_method_via_spy_framework_input M1 additionalStates isAlreadyPrime c b). \<forall>xs'\<in>list.set (prefixes xs). {io \<in> L M1. map fst io = xs'} = {io \<in> L M2. map fst io = xs'})"
  using apply_to_prime_and_return_input_lists_completeness[where f="(\<lambda> M m . spyh_method_via_spy_framework M m c b)" and isAlreadyPrime=isAlreadyPrime, OF _ assms(1,2,3,4,5,6,7)]
  using spyh_method_via_spy_framework_completeness_and_finiteness
  unfolding spyh_method_via_spy_framework_input_def[symmetric]
  by (metis (no_types, lifting)) 


subsubsection \<open>Partial S-Method\<close>

definition partial_s_method_via_h_framework_ts :: "(uint64,uint64,uint64) fsm \<Rightarrow> integer \<Rightarrow> bool \<Rightarrow> bool \<Rightarrow> bool \<Rightarrow> ((uint64\<times>uint64)\<times>bool) list list" where
  "partial_s_method_via_h_framework_ts M additionalStates isAlreadyPrime c b = apply_to_prime_and_return_io_lists M additionalStates isAlreadyPrime (\<lambda> M m . partial_s_method_via_h_framework M m c b)"

lemma partial_s_method_via_h_framework_ts_completeness :
  assumes "observable M2"
  and   "minimal M2"
  and   "size M2 \<le> size_r (to_prime M1) + (nat_of_integer additionalStates)"
  and   "FSM.inputs M2 = FSM.inputs M1"
  and   "FSM.outputs M2 = FSM.outputs M1"
  and   "isAlreadyPrime \<Longrightarrow> observable M1 \<and> minimal M1 \<and> reachable_states M1 = states M1"  
  and   "size (to_prime M1) < 2^64"
shows "(L M1 = L M2) \<longleftrightarrow> list_all (passes_test_case M2 (FSM.initial M2)) (partial_s_method_via_h_framework_ts M1 additionalStates isAlreadyPrime c b)"
  using apply_to_prime_and_return_io_lists_completeness[where f="(\<lambda> M m . partial_s_method_via_h_framework M m c b)" and isAlreadyPrime=isAlreadyPrime, OF _ assms(1,2,3,4,5,6,7)]
  using partial_s_method_via_h_framework_completeness_and_finiteness
  unfolding partial_s_method_via_h_framework_ts_def
  by metis

definition partial_s_method_via_h_framework_input :: "(uint64,uint64,uint64) fsm \<Rightarrow> integer \<Rightarrow> bool \<Rightarrow> bool \<Rightarrow> bool \<Rightarrow> uint64 list list" where
  "partial_s_method_via_h_framework_input M additionalStates isAlreadyPrime c b = apply_to_prime_and_return_input_lists M additionalStates isAlreadyPrime (\<lambda> M m . partial_s_method_via_h_framework M m c b)"

lemma partial_s_method_via_h_framework_input_completeness :
  assumes "observable M2"
  and   "minimal M2"
  and   "size M2 \<le> size_r (to_prime M1) + (nat_of_integer additionalStates)"
  and   "FSM.inputs M2 = FSM.inputs M1"
  and   "FSM.outputs M2 = FSM.outputs M1"
  and   "isAlreadyPrime \<Longrightarrow> observable M1 \<and> minimal M1 \<and> reachable_states M1 = states M1"  
  and   "size (to_prime M1) < 2^64"
shows "(L M1 = L M2) \<longleftrightarrow> (\<forall>xs\<in>list.set (partial_s_method_via_h_framework_input M1 additionalStates isAlreadyPrime c b). \<forall>xs'\<in>list.set (prefixes xs). {io \<in> L M1. map fst io = xs'} = {io \<in> L M2. map fst io = xs'})"
  using apply_to_prime_and_return_input_lists_completeness[where f="(\<lambda> M m . partial_s_method_via_h_framework M m c b)" and isAlreadyPrime=isAlreadyPrime, OF _ assms(1,2,3,4,5,6,7)]
  using partial_s_method_via_h_framework_completeness_and_finiteness
  unfolding partial_s_method_via_h_framework_input_def[symmetric] 
  by (metis (no_types, lifting)) 
  



subsection \<open>New Instances\<close>

(* alternative instantiations for fsets
derive (eq) ceq fset
derive (no) cenum fset
derive (no) ccompare fset
derive (dlist) set_impl fset

instantiation fset :: (infinite_UNIV) finite_UNIV begin
definition "finite_UNIV = Phantom(('a)fset) False"


lemma infinite_UNIV_fset : 
  shows "infinite (UNIV :: ('a :: infinite_UNIV) fset set)"
proof -
  (* if infinitely many elements exist, then infinitely many distinct singletons can be created *)
  define f :: "'a \<Rightarrow> ('a) fset" where f_def: "f = (\<lambda> q . {| q |})"
  have "inj f" 
  proof 
    fix x y assume "x \<in> (UNIV :: 'a set)" and "y \<in> UNIV" and "f x = f y" 
    then show "x = y" unfolding f_def by (transfer; auto)
  qed
  moreover have "infinite (UNIV :: 'a set)"
    using infinite_UNIV by auto
  ultimately show ?thesis
    by (meson finite_imageD infinite_iff_countable_subset top_greatest) 
qed

instance by (intro_classes)
            (simp add: finite_UNIV_fset_def infinite_UNIV_fset) 
end

instantiation fset :: (infinite_UNIV) cproper_interval begin
definition cproper_interval_fset :: "(('a) fset) proper_interval" 
  where "cproper_interval_fset _ _ = undefined"
instance by(intro_classes)(simp add: infinite_UNIV_fset)
end

lemma infinite_UNIV_fset : "infinite (UNIV :: ('a :: infinite_UNIV) fset set)"
proof -
  (* if infinitely many elements exist, then infinitely many distinct singletons can be created *)
  define f :: "'a \<Rightarrow> ('a) fset" where f_def: "f = (\<lambda> q . {| q |})"
  have "inj f" 
  proof 
    fix x y assume "x \<in> (UNIV :: 'a set)" and "y \<in> UNIV" and "f x = f y" 
    then show "x = y" unfolding f_def by (transfer; auto)
  qed
  moreover have "infinite (UNIV :: 'a set)"
    using infinite_UNIV by auto
  ultimately show ?thesis
    by (meson finite_imageD infinite_iff_countable_subset top_greatest) 
qed
*)

lemma finiteness_fset_UNIV : "finite (UNIV :: 'a fset set) = finite (UNIV :: 'a set)"
proof 

  define f :: "'a \<Rightarrow> ('a) fset" where f_def: "f = (\<lambda> q . {| q |})"
  have "inj f" 
  proof 
    fix x y assume "x \<in> (UNIV :: 'a set)" and "y \<in> UNIV" and "f x = f y" 
    then show "x = y" unfolding f_def by (transfer; auto)
  qed

  show "finite (UNIV :: 'a fset set) \<Longrightarrow> finite (UNIV :: 'a set)"
  proof (rule ccontr)
    assume "finite (UNIV :: 'a fset set)" and "\<not> finite (UNIV :: 'a set)"

    then have "\<not> finite (f ` UNIV)"
      using \<open>inj f\<close>
      using finite_imageD by blast 
    then have "\<not> finite (UNIV :: 'a fset set)"
      by (meson infinite_iff_countable_subset top_greatest) 
    then show False
      using \<open>finite (UNIV :: 'a fset set)\<close> by auto
  qed

  show "finite (UNIV :: 'a set) \<Longrightarrow> finite (UNIV :: 'a fset set)"
  proof -
    assume "finite (UNIV :: 'a set)"
    then have "finite (UNIV :: 'a set set)"
      by (simp add: Finite_Set.finite_set) 
    moreover have "fset ` (UNIV :: 'a fset set) \<subseteq> (UNIV :: 'a set set)"
      by auto
    moreover have "inj fset"
      by (meson fset_inject injI) 
    ultimately show ?thesis by (metis inj_on_finite)
  qed
qed

instantiation fset :: (finite_UNIV) finite_UNIV begin
definition "finite_UNIV = Phantom('a fset) (of_phantom (finite_UNIV :: 'a finite_UNIV))"
instance by(intro_classes)(simp add: finite_UNIV_fset_def finite_UNIV finiteness_fset_UNIV)
end

derive (eq) ceq fset
derive (no) cenum fset
derive (no) ccompare fset
derive (dlist) set_impl fset

instantiation fset :: (type) cproper_interval begin
definition cproper_interval_fset :: "(('a) fset) proper_interval" 
  where "cproper_interval_fset _ _ = undefined"
instance by(intro_classes)(simp add: ID_None ccompare_fset_def)
end

lemma card_fPow: "card (Pow (fset A)) = 2 ^ card (fset A)"
  using card_Pow[of "fset A"]
  by simp

 

lemma finite_sets_finite_univ : 
  assumes "finite (UNIV :: 'a set)" 
  shows "finite (xs :: 'a set)"
  by (metis Diff_UNIV Diff_infinite_finite assms finite_Diff) 


lemma card_UNIV_fset: "CARD('a fset) = (if CARD('a) = 0 then 0 else 2 ^ CARD('a))"
  apply (simp add: card_eq_0_iff)
proof 

  have "inj fset"
    by (meson fset_inject injI)
  have "card (UNIV :: 'a fset set) = card (fset ` (UNIV :: 'a fset set))"
    by (simp add: \<open>inj fset\<close> card_image)


  show "finite (UNIV :: 'a set) \<longrightarrow> CARD('a fset) = 2 ^ CARD('a)"
  proof 
    assume "finite (UNIV :: 'a set)"
    then have "CARD('a set) = 2 ^ CARD('a)"
      by (metis Pow_UNIV card_Pow)

    have "finite (UNIV :: 'a set set)" 
      using \<open>finite (UNIV :: 'a set)\<close>
      by (simp add: Finite_Set.finite_set) 
    
    have "finite (UNIV :: 'a fset set)"
      using \<open>finite (UNIV :: 'a set)\<close> finiteness_fset_UNIV by auto


    have "\<And> xs :: 'a set . finite xs"
      using finite_sets_finite_univ[OF \<open>finite (UNIV :: 'a set)\<close>] .
    then have "(UNIV :: 'a set set) = fset ` (UNIV :: 'a fset set)"
      by (metis UNIV_I UNIV_eq_I fset_to_fset image_iff)
    
    have "CARD('a fset) \<le> CARD('a set)"
      unfolding \<open>card (UNIV :: 'a fset set) = card (fset ` (UNIV :: 'a fset set))\<close> 
      by (metis \<open>finite (UNIV :: 'a set set)\<close> card_mono subset_UNIV)
    moreover have "CARD('a fset) \<ge> CARD('a set)" 
      unfolding \<open>(UNIV :: 'a set set) = fset ` (UNIV :: 'a fset set)\<close>
      using \<open>CARD('a::type fset) = card (range fset)\<close> by linarith
    ultimately have "CARD('a fset) = CARD('a set)"
      by linarith
    then show "CARD('a fset) = (2::nat) ^ CARD('a)"
      by (simp add: \<open>CARD('a::type set) = (2::nat) ^ CARD('a::type)\<close>)
  qed 

  show "infinite (UNIV :: 'a set) \<longrightarrow> infinite (UNIV :: 'a fset set)"
    by (simp add: finiteness_fset_UNIV)
qed

instantiation fset :: (card_UNIV) card_UNIV begin
definition "card_UNIV = Phantom('a fset)
  (let c = of_phantom (card_UNIV :: 'a card_UNIV) in if c = 0 then 0 else 2 ^ c)"
instance by intro_classes (simp add: card_UNIV_fset_def card_UNIV_fset card_UNIV)
end

derive (choose) mapping_impl fset

lemma uint64_range : "range nat_of_uint64 = {..<2 ^ 64}"
proof 
  show "{..<2 ^ 64} \<subseteq> range nat_of_uint64"
    using uint64_nat_bij
    by (metis lessThan_iff range_eqI subsetI) 
  have "\<And> x . nat_of_uint64 x < 2^64"
    apply transfer using take_bit_nat_eq_self
    by (metis uint64.size_eq_length unsigned_less)
  then show "range nat_of_uint64 \<subseteq> {..<2 ^ 64}"
    by auto
qed

lemma card_UNIV_uint64: "CARD(uint64) = 2^64" 
proof -
  have "inj nat_of_uint64"
    apply transfer
    by simp 
  then have "bij_betw nat_of_uint64 (UNIV :: uint64 set) {..<2^64}"
    using uint64_range
    unfolding bij_betw_def by blast
  then show ?thesis
    by (simp add: bij_betw_same_card) 
qed

lemma nat_of_uint64_bij_betw : "bij_betw nat_of_uint64  (UNIV :: uint64 set) {..<2 ^ 64}"
  unfolding bij_betw_def
  using uint64_range
  by transfer (auto)


lemma uint64_UNIV : "(UNIV :: uint64 set) = uint64_of_nat ` {..<2 ^ 64}"
  using nat_of_uint64_bij_betw
  by (metis UNIV_I UNIV_eq_I bij_betw_def card_UNIV_uint64 imageI image_eqI inj_on_contraD lessThan_iff rangeI uint64_nat_bij uint64_range)

lemma uint64_of_nat_bij_betw : "bij_betw uint64_of_nat  {..<2 ^ 64} (UNIV :: uint64 set)"  
  unfolding bij_betw_def
proof
  show "inj_on uint64_of_nat {..<2 ^ 64}"
    using nat_of_uint64_bij_betw uint64_nat_bij
    by (metis inj_on_inverseI lessThan_iff) 
  show "uint64_of_nat ` {..<2 ^ 64} = UNIV"
    using uint64_UNIV by blast
qed
    

lemma uint64_finite : "finite (UNIV :: uint64 set)"
  unfolding uint64_UNIV
  by simp 


instantiation uint64 :: finite_UNIV begin
definition "finite_UNIV = Phantom(uint64) True"
instance apply intro_classes
  by (simp add: finite_UNIV_uint64_def uint64_finite) 
end


instantiation uint64 :: card_UNIV begin
definition "card_UNIV = Phantom(uint64) (2^64)"
instance 
  by intro_classes (simp add: card_UNIV_uint64_def card_UNIV_uint64 card_UNIV)
end


instantiation uint64 :: compare
begin
definition compare_uint64 :: "uint64 \<Rightarrow> uint64 \<Rightarrow> order" where
  "compare_uint64 x y = (case (x < y, x = y) of (True,_) \<Rightarrow> Lt | (False,True) \<Rightarrow> Eq | (False,False) \<Rightarrow> Gt)"

instance 
  apply intro_classes 
proof 
  show "\<And>x y::uint64. invert_order (compare x y) = compare y x" 
  proof -
    fix x y::uint64 show "invert_order (compare x y) = compare y x"
    proof (cases "x = y")
      case True
      then show ?thesis unfolding compare_uint64_def by auto
    next
      case False
      then show ?thesis proof (cases "x < y")
        case True
        then show ?thesis unfolding compare_uint64_def using False
          using order_less_not_sym by fastforce 
      next
        case False
        then show ?thesis unfolding compare_uint64_def using \<open>x \<noteq> y\<close>
          using linorder_less_linear by fastforce
      qed
    qed
  qed

  show "\<And>x y::uint64. compare x y = Eq \<Longrightarrow> x = y" 
    unfolding compare_uint64_def
    by (metis (mono_tags) case_prod_conv old.bool.simps(3) old.bool.simps(4) order.distinct(1) order.distinct(3)) 

  show "\<And>x y z::uint64. compare x y = Lt \<Longrightarrow> compare y z = Lt \<Longrightarrow> compare x z = Lt"
    unfolding compare_uint64_def
    by (metis (full_types, lifting) case_prod_conv old.bool.simps(3) old.bool.simps(4) order.distinct(5) order_less_trans)
qed
end 

instantiation uint64 :: ccompare
begin
definition ccompare_uint64 :: "(uint64 \<Rightarrow> uint64 \<Rightarrow> order) option" where
  "ccompare_uint64 = Some compare"

instance by (intro_classes; simp add: ccompare_uint64_def comparator_compare)
end

derive (eq) ceq uint64
derive (no) cenum uint64
derive (rbt) set_impl uint64
derive (rbt) mapping_impl uint64


instantiation uint64 :: proper_interval begin
fun proper_interval_uint64 :: "uint64 proper_interval" 
  where 
    "proper_interval_uint64 None None = True" |
    "proper_interval_uint64 None (Some y) = (y > 0)"|
    "proper_interval_uint64 (Some x) None = (x \<noteq> uint64_of_nat (2^64-1))" | 
    "proper_interval_uint64 (Some x) (Some y) = (x < y \<and> x+1 < y)"

instance apply intro_classes
proof -
  show "proper_interval None (None :: uint64 option) = True" by auto

  show "\<And>y. proper_interval None (Some (y::uint64)) = (\<exists>z. z < y)"
    unfolding proper_interval_uint64.simps
    apply transfer
    using word_gt_a_gt_0 by auto
  
  have "\<And> x . (x \<noteq> uint64_of_nat (2^64-1)) = (nat_of_uint64 x \<noteq> 2^64-1)"
  proof 
    fix x 
    show "(x \<noteq> uint64_of_nat (2^64-1)) \<Longrightarrow> (nat_of_uint64 x \<noteq> 2^64-1)"
      apply transfer
      by (metis Word.of_nat_unat ucast_id) 
    show "nat_of_uint64 x \<noteq> 2 ^ 64 - 1 \<Longrightarrow> x \<noteq> uint64_of_nat (2 ^ 64 - 1)"
      by (meson diff_less pos2 uint64_nat_bij zero_less_one zero_less_power)
  qed
  then show "\<And>x. proper_interval (Some (x::uint64)) None = (\<exists>z. x < z)"
    unfolding proper_interval_uint64.simps
    apply transfer
    by (metis uint64.size_eq_length unat_minus_one_word word_le_less_eq word_le_not_less word_order.extremum)

  show "\<And>x y. proper_interval (Some x) (Some (y::uint64)) = (\<exists>z>x. z < y)"
    unfolding proper_interval_uint64.simps
    apply transfer
    using inc_le less_is_non_zero_p1 word_overflow 
    by fastforce
qed
end



                                  
instantiation uint64 :: cproper_interval begin
definition "cproper_interval = (proper_interval :: uint64 proper_interval)"
instance 
  apply intro_classes 
  apply (simp add: cproper_interval_uint64_def ord_defs ccompare_uint64_def ID_Some proper_interval_class.axioms uint64_finite) 
proof 

  fix x y :: uint64

  show "proper_interval None (None :: uint64 option) = True"
    by auto

  have "(\<exists>z. lt_of_comp compare z y) = (\<exists>z. z < y)"
    unfolding compare_uint64_def lt_of_comp_def
    by (metis bool.case_eq_if case_prod_conv order.simps(7) order.simps(8) order.simps(9)) 
  then show "proper_interval None (Some y) = (\<exists>z. lt_of_comp compare z y)"
    using proper_interval_simps(2) by blast 

  have "(\<exists>z. lt_of_comp compare x z) = (\<exists>z. x < z)"
    unfolding compare_uint64_def lt_of_comp_def
    by (metis bool.case_eq_if case_prod_conv order.simps(7) order.simps(8) order.simps(9))
  then show "proper_interval (Some x) None = (\<exists>z. lt_of_comp compare x z)"   
    using proper_interval_simps(3) by blast 

  have "(\<exists>z. lt_of_comp compare x z \<and> lt_of_comp compare z y) \<Longrightarrow> (\<exists>z>x. z < y)"
    unfolding compare_uint64_def lt_of_comp_def
    by (metis bool.case_eq_if case_prod_conv order.simps(7) order.simps(9))
  moreover have "(\<exists>z>x. z < y) \<Longrightarrow> (\<exists>z. lt_of_comp compare x z \<and> lt_of_comp compare z y)"
    unfolding compare_uint64_def lt_of_comp_def
    unfolding proper_interval_simps(4)[symmetric]
    using compare_uint64_def
    by (metis (mono_tags, lifting) \<open>\<And>y x. (\<exists>z>x. z < y) = proper_interval (Some x) (Some y)\<close> case_prod_conv old.bool.simps(3) order.simps(8))   
  ultimately show "proper_interval (Some x) (Some y) = (\<exists>z. lt_of_comp compare x z \<and> lt_of_comp compare z y)"
    using proper_interval_simps(4) by blast 
qed
end


subsection \<open>Exports\<close>

fun fsm_from_list_uint64 :: "uint64 \<Rightarrow> (uint64 \<times> uint64 \<times> uint64 \<times> uint64) list \<Rightarrow> (uint64, uint64, uint64) fsm" 
  where "fsm_from_list_uint64 q ts = fsm_from_list q ts"

fun fsm_from_list_integer :: "integer \<Rightarrow> (integer \<times> integer \<times> integer \<times> integer) list \<Rightarrow> (integer, integer, integer) fsm" 
  where "fsm_from_list_integer q ts = fsm_from_list q ts"




export_code Inl
            fsm_from_list
            fsm_from_list_uint64
            fsm_from_list_integer
            size 
            to_prime
            make_observable
            rename_states
            index_states
            restrict_to_reachable_states
            integer_of_nat 
            generate_reduction_test_suite_naive
            generate_reduction_test_suite_greedy
            w_method_via_h_framework_ts
            w_method_via_h_framework_input
            w_method_via_h_framework_2_ts
            w_method_via_h_framework_2_input
            w_method_via_spy_framework_ts
            w_method_via_spy_framework_input
            w_method_via_pair_framework_ts
            w_method_via_pair_framework_input
            wp_method_via_h_framework_ts
            wp_method_via_h_framework_input
            wp_method_via_spy_framework_ts
            wp_method_via_spy_framework_input
            hsi_method_via_h_framework_ts
            hsi_method_via_h_framework_input
            hsi_method_via_spy_framework_ts
            hsi_method_via_spy_framework_input
            hsi_method_via_pair_framework_ts
            hsi_method_via_pair_framework_input
            h_method_via_h_framework_ts
            h_method_via_h_framework_input
            h_method_via_pair_framework_ts
            h_method_via_pair_framework_input
            h_method_via_pair_framework_2_ts
            h_method_via_pair_framework_2_input
            h_method_via_pair_framework_3_ts
            h_method_via_pair_framework_3_input
            spy_method_via_h_framework_ts
            spy_method_via_h_framework_input
            spy_method_via_spy_framework_ts
            spy_method_via_spy_framework_input
            spyh_method_via_h_framework_ts
            spyh_method_via_h_framework_input
            spyh_method_via_spy_framework_ts
            spyh_method_via_spy_framework_input
            partial_s_method_via_h_framework_ts
            partial_s_method_via_h_framework_input
in Haskell module_name GeneratedCode file_prefix haskell_export


export_code Inl
            fsm_from_list
            fsm_from_list_uint64
            fsm_from_list_integer
            size 
            to_prime
            make_observable
            rename_states
            index_states
            restrict_to_reachable_states
            integer_of_nat 
            generate_reduction_test_suite_naive
            generate_reduction_test_suite_greedy
            w_method_via_h_framework_ts
            w_method_via_h_framework_input
            w_method_via_h_framework_2_ts
            w_method_via_h_framework_2_input
            w_method_via_spy_framework_ts
            w_method_via_spy_framework_input
            w_method_via_pair_framework_ts
            w_method_via_pair_framework_input
            wp_method_via_h_framework_ts
            wp_method_via_h_framework_input
            wp_method_via_spy_framework_ts
            wp_method_via_spy_framework_input
            hsi_method_via_h_framework_ts
            hsi_method_via_h_framework_input
            hsi_method_via_spy_framework_ts
            hsi_method_via_spy_framework_input
            hsi_method_via_pair_framework_ts
            hsi_method_via_pair_framework_input
            h_method_via_h_framework_ts
            h_method_via_h_framework_input
            h_method_via_pair_framework_ts
            h_method_via_pair_framework_input
            h_method_via_pair_framework_2_ts
            h_method_via_pair_framework_2_input
            h_method_via_pair_framework_3_ts
            h_method_via_pair_framework_3_input
            spy_method_via_h_framework_ts
            spy_method_via_h_framework_input
            spy_method_via_spy_framework_ts
            spy_method_via_spy_framework_input
            spyh_method_via_h_framework_ts
            spyh_method_via_h_framework_input
            spyh_method_via_spy_framework_ts
            spyh_method_via_spy_framework_input
            partial_s_method_via_h_framework_ts
            partial_s_method_via_h_framework_input
in Scala module_name GeneratedCode file_prefix scala_export (case_insensitive)


export_code Inl
            fsm_from_list
            fsm_from_list_uint64
            fsm_from_list_integer
            size 
            to_prime
            make_observable
            rename_states
            index_states
            restrict_to_reachable_states
            integer_of_nat 
            generate_reduction_test_suite_naive
            generate_reduction_test_suite_greedy
            w_method_via_h_framework_ts
            w_method_via_h_framework_input
            w_method_via_h_framework_2_ts
            w_method_via_h_framework_2_input
            w_method_via_spy_framework_ts
            w_method_via_spy_framework_input
            w_method_via_pair_framework_ts
            w_method_via_pair_framework_input
            wp_method_via_h_framework_ts
            wp_method_via_h_framework_input
            wp_method_via_spy_framework_ts
            wp_method_via_spy_framework_input
            hsi_method_via_h_framework_ts
            hsi_method_via_h_framework_input
            hsi_method_via_spy_framework_ts
            hsi_method_via_spy_framework_input
            hsi_method_via_pair_framework_ts
            hsi_method_via_pair_framework_input
            h_method_via_h_framework_ts
            h_method_via_h_framework_input
            h_method_via_pair_framework_ts
            h_method_via_pair_framework_input
            h_method_via_pair_framework_2_ts
            h_method_via_pair_framework_2_input
            h_method_via_pair_framework_3_ts
            h_method_via_pair_framework_3_input
            spy_method_via_h_framework_ts
            spy_method_via_h_framework_input
            spy_method_via_spy_framework_ts
            spy_method_via_spy_framework_input
            spyh_method_via_h_framework_ts
            spyh_method_via_h_framework_input
            spyh_method_via_spy_framework_ts
            spyh_method_via_spy_framework_input
            partial_s_method_via_h_framework_ts
            partial_s_method_via_h_framework_input
in SML module_name GeneratedCode file_prefix sml_export


export_code Inl
            fsm_from_list
            fsm_from_list_uint64
            fsm_from_list_integer
            size 
            to_prime
            make_observable
            rename_states
            index_states
            restrict_to_reachable_states
            integer_of_nat 
            generate_reduction_test_suite_naive
            generate_reduction_test_suite_greedy
            w_method_via_h_framework_ts
            w_method_via_h_framework_input
            w_method_via_h_framework_2_ts
            w_method_via_h_framework_2_input
            w_method_via_spy_framework_ts
            w_method_via_spy_framework_input
            w_method_via_pair_framework_ts
            w_method_via_pair_framework_input
            wp_method_via_h_framework_ts
            wp_method_via_h_framework_input
            wp_method_via_spy_framework_ts
            wp_method_via_spy_framework_input
            hsi_method_via_h_framework_ts
            hsi_method_via_h_framework_input
            hsi_method_via_spy_framework_ts
            hsi_method_via_spy_framework_input
            hsi_method_via_pair_framework_ts
            hsi_method_via_pair_framework_input
            h_method_via_h_framework_ts
            h_method_via_h_framework_input
            h_method_via_pair_framework_ts
            h_method_via_pair_framework_input
            h_method_via_pair_framework_2_ts
            h_method_via_pair_framework_2_input
            h_method_via_pair_framework_3_ts
            h_method_via_pair_framework_3_input
            spy_method_via_h_framework_ts
            spy_method_via_h_framework_input
            spy_method_via_spy_framework_ts
            spy_method_via_spy_framework_input
            spyh_method_via_h_framework_ts
            spyh_method_via_h_framework_input
            spyh_method_via_spy_framework_ts
            spyh_method_via_spy_framework_input
            partial_s_method_via_h_framework_ts
            partial_s_method_via_h_framework_input
in OCaml module_name GeneratedCode file_prefix ocaml_export

end