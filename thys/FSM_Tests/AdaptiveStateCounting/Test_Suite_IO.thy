section \<open>Representing Test Suites as Sets of Input-Output Sequences\<close>

text \<open>This theory describes the representation of test suites as sets of input-output sequences
      and defines a pass relation for this representation.\<close>


theory Test_Suite_IO
imports Test_Suite Maximal_Path_Trie
begin


fun test_suite_to_io :: "('a,'b,'c) fsm \<Rightarrow> ('a,'b,'c,'d) test_suite \<Rightarrow> ('b \<times> 'c) list set" where
  "test_suite_to_io M (Test_Suite prs tps rd_targets atcs) =
    (\<Union> (q,P) \<in> prs . L P)
    \<union> (\<Union>{(\<lambda> io' . p_io p @ io') ` (set (prefixes (p_io pt))) | p pt . \<exists> q P . (q,P) \<in> prs \<and> path P (initial P) p \<and> target (initial P) p = q \<and> pt \<in> tps q})
    \<union> (\<Union>{(\<lambda> io_atc . p_io p @ p_io pt @ io_atc) ` (atc_to_io_set (from_FSM M (target q pt)) A) | p pt q A . \<exists> P q' t1 t2 . (q,P) \<in> prs \<and> path P (initial P) p \<and> target (initial P) p = q \<and> pt \<in> tps q \<and> q' \<in> rd_targets (q,pt) \<and> (A,t1,t2) \<in> atcs (target q pt,q') })"


lemma test_suite_to_io_language :
  assumes "implies_completeness T M m"
shows "(test_suite_to_io M T) \<subseteq> L M"
proof 
  fix io assume "io \<in> test_suite_to_io M T"

  obtain prs tps rd_targets atcs where "T = Test_Suite prs tps rd_targets atcs"
    by (meson test_suite.exhaust)

  then obtain repetition_sets where repetition_sets_def: "implies_completeness_for_repetition_sets (Test_Suite prs tps rd_targets atcs) M m repetition_sets"
    using assms(1) unfolding implies_completeness_def 
    by blast
  then have "implies_completeness (Test_Suite prs tps rd_targets atcs) M m"
    unfolding implies_completeness_def 
    by blast

  have t2: "\<And> q P. (q, P) \<in> prs \<Longrightarrow> is_preamble P M q"
    using implies_completeness_for_repetition_sets_simps(2)[OF repetition_sets_def] 
    by blast
  
  have t5: "\<And>q. q \<in> FSM.states M \<Longrightarrow> (\<exists>d\<in>set repetition_sets. q \<in> fst d)"
    using implies_completeness_for_repetition_sets_simps(4)[OF repetition_sets_def] 
    by assumption

  have t6: "\<And> q. q \<in> fst ` prs \<Longrightarrow> tps q \<subseteq> {p1 . \<exists> p2 d . (p1@p2,d) \<in> m_traversal_paths_with_witness M q repetition_sets m} \<and> fst ` (m_traversal_paths_with_witness M q repetition_sets m) \<subseteq> tps q"
    using implies_completeness_for_repetition_sets_simps(7)[OF repetition_sets_def] 
    by assumption

  have t8: "\<And> d. d \<in> set repetition_sets \<Longrightarrow> snd d \<subseteq> fst d"
    using implies_completeness_for_repetition_sets_simps(5,6)[OF repetition_sets_def] 
    by blast


  from \<open>io \<in> test_suite_to_io M T\<close> consider
    (a) "io \<in> (\<Union> (q,P) \<in> prs . L P)" |
    (b) "io \<in> (\<Union>{(\<lambda> io' . p_io p @ io') ` (set (prefixes (p_io pt))) | p pt . \<exists> q P . (q,P) \<in> prs \<and> path P (initial P) p \<and> target (initial P) p = q \<and> pt \<in> tps q})" |
    (c) "io \<in> (\<Union>{(\<lambda> io_atc . p_io p @ p_io pt @ io_atc) ` (atc_to_io_set (from_FSM M (target q pt)) A) | p pt q A . \<exists> P q' t1 t2 . (q,P) \<in> prs \<and> path P (initial P) p \<and> target (initial P) p = q \<and> pt \<in> tps q \<and> q' \<in> rd_targets (q,pt) \<and> (A,t1,t2) \<in> atcs (target q pt,q') })"
    unfolding \<open>T = Test_Suite prs tps rd_targets atcs\<close> test_suite_to_io.simps
    by blast

  then show "io \<in> L M" proof cases
    case a
    then obtain q P  where "(q, P) \<in> prs" and "io \<in> L P"
      by blast

    have "is_submachine P M"
      using t2[OF \<open>(q, P) \<in> prs\<close>] unfolding is_preamble_def by blast

    show "io \<in> L M"
      using submachine_language[OF \<open>is_submachine P M\<close>] \<open>io \<in> L P\<close> by blast
  next
    case b
    then obtain p pt q P where "io \<in> (\<lambda> io' . p_io p @ io') ` (set (prefixes (p_io pt)))" 
                           and "(q,P) \<in> prs" 
                           and "path P (initial P) p" 
                           and "target (initial P) p = q" 
                           and "pt \<in> tps q"
      by blast 

    then obtain io' where "io = p_io p @ io'" and "io' \<in> (set (prefixes (p_io pt)))"
      by blast

    then obtain io'' where "p_io pt = io' @ io''" and "io = p_io p @ io'"
      unfolding prefixes_set
    proof -
      assume a1: "io' \<in> {xs'. \<exists>xs''. xs' @ xs'' = p_io pt}"
      assume "\<And>io''. \<lbrakk>p_io pt = io' @ io''; io = p_io p @ io'\<rbrakk> \<Longrightarrow> thesis"
      then show ?thesis
        using a1 \<open>io = p_io p @ io'\<close> by moura
    qed 

    have "q \<in> fst ` prs"
      using \<open>(q,P) \<in> prs\<close> 
      by force

    have "is_submachine P M"
      using t2[OF \<open>(q, P) \<in> prs\<close>] 
      unfolding is_preamble_def 
      by blast
    then have "initial P = initial M" 
      by auto

    have "path M (initial M) p"
      using submachine_path[OF \<open>is_submachine P M\<close> \<open>path P (initial P) p\<close>] 
      unfolding \<open>initial P = initial M\<close> 
      by assumption

    have "target (initial M) p = q"
      using \<open>target (initial P) p = q\<close> 
      unfolding \<open>initial P = initial M\<close> 
      by assumption

    obtain p2 d where "(pt @ p2, d) \<in> m_traversal_paths_with_witness M q repetition_sets m"
      using t6[OF \<open>q \<in> fst ` prs\<close>] \<open>pt \<in> tps q\<close> 
      by blast
    then have "path M q (pt @ p2)"
      using m_traversal_paths_with_witness_set[OF t5 t8 path_target_is_state[OF \<open>path M (initial M) p\<close>], of m]
      unfolding \<open>target (initial M) p = q\<close> 
      by blast
    then have "path M (initial M) (p@pt)"
      using \<open>path M (initial M) p\<close> \<open>target (initial M) p = q\<close> 
      by auto
    then have "p_io p @ p_io pt \<in> L M"
      by (metis (mono_tags, lifting) language_intro map_append)
    
    then show "io \<in> L M"
      unfolding \<open>io = p_io p @ io'\<close> \<open>p_io pt = io' @ io''\<close> append.assoc[symmetric] 
      using language_prefix[of "p_io p @ io'" io'' M "initial M"] 
      by blast
  next
    case c
                                                                                                                      
    then obtain p pt q A P q' t1 t2 where "io \<in> (\<lambda> io_atc . p_io p @ p_io pt @ io_atc) ` (atc_to_io_set (from_FSM M (target q pt)) A)"
                                    and   "(q,P) \<in> prs" 
                                    and   "path P (initial P) p"
                                    and   "target (initial P) p = q"
                                    and   "pt \<in> tps q"
                                    and   "q' \<in> rd_targets (q,pt)" 
                                    and   "(A,t1,t2) \<in> atcs (target q pt,q')"
      by blast

    obtain ioA where "io = p_io p @ p_io pt @ ioA"
               and   "ioA \<in> (atc_to_io_set (from_FSM M (target q pt)) A)"
      using \<open>io \<in> (\<lambda> io_atc . p_io p @ p_io pt @ io_atc) ` (atc_to_io_set (from_FSM M (target q pt)) A)\<close>
      by blast
    then have "ioA \<in> L (from_FSM M (target q pt))"
      unfolding atc_to_io_set.simps by blast


    have "q \<in> fst ` prs"
      using \<open>(q,P) \<in> prs\<close> by force
    

    have "is_submachine P M"
      using t2[OF \<open>(q, P) \<in> prs\<close>] unfolding is_preamble_def by blast
    then have "initial P = initial M" by auto

    have "path M (initial M) p"
      using submachine_path[OF \<open>is_submachine P M\<close> \<open>path P (initial P) p\<close>] 
      unfolding \<open>initial P = initial M\<close> 
      by assumption
    have "target (initial M) p = q"
      using \<open>target (initial P) p = q\<close> 
      unfolding \<open>initial P = initial M\<close> 
      by assumption

    obtain p2 d where "(pt @ p2, d) \<in> m_traversal_paths_with_witness M q repetition_sets m"
      using t6[OF \<open>q \<in> fst ` prs\<close>] \<open>pt \<in> tps q\<close> by blast

    then have "path M q (pt @ p2)"
      using m_traversal_paths_with_witness_set[OF t5 t8 path_target_is_state[OF \<open>path M (initial M) p\<close>], of m]
      unfolding \<open>target (initial M) p = q\<close> 
      by blast
    then have "path M (initial M) (p@pt)"
      using \<open>path M (initial M) p\<close> \<open>target (initial M) p = q\<close> 
      by auto
    moreover have "(target q pt) = target (initial M) (p@pt)"
      using \<open>target (initial M) p = q\<close>
      by auto
    ultimately have "(target q pt) \<in> states M"
      using path_target_is_state 
      by metis

    have "ioA \<in> LS M (target q pt)"
      using from_FSM_language[OF \<open>(target q pt) \<in> states M\<close>] \<open>ioA \<in> L (from_FSM M (target q pt))\<close>
      by blast
    then obtain pA where "path M (target q pt) pA" and "p_io pA = ioA"
      by auto
    then have "path M (initial M) (p @ pt @ pA)"
      using \<open>path M (initial M) (p@pt)\<close>  unfolding \<open>(target q pt) = target (initial M) (p@pt)\<close> 
      by auto
    then have "p_io p @ p_io pt @ ioA \<in> L M"
      unfolding \<open>p_io pA = ioA\<close>[symmetric]
      using language_intro by fastforce
    then show "io \<in> L M"
      unfolding \<open>io = p_io p @ p_io pt @ ioA\<close> 
      by assumption
  qed
qed

  
lemma minimal_io_seq_to_failure :
  assumes "\<not> (L M' \<subseteq> L M)"
  and     "inputs M' = inputs M"  
  and     "completely_specified M"
obtains io x y y' where "io@[(x,y)] \<in> L M" and "io@[(x,y')] \<notin>  L M" and "io@[(x,y')] \<in> L M'" 
proof -
  obtain ioF where "ioF \<in> L M'" and "ioF \<notin> L M"
    using assms(1) by blast
  

  let ?prefs = "{ioF' \<in> set (prefixes ioF) . ioF' \<in> L M' \<and> ioF' \<notin> L M}"
  have "finite ?prefs"
    using prefixes_finite by auto
  moreover have "?prefs \<noteq> {}"
    unfolding prefixes_set using \<open>ioF \<in> L M'\<close> \<open>ioF \<notin> L M\<close> by auto
  ultimately obtain ioF' where "ioF' \<in> ?prefs" and "\<And> ioF'' . ioF'' \<in> ?prefs \<Longrightarrow> length ioF' \<le> length ioF''"
    by (meson leI min_length_elem) 
  
  then have "ioF' \<in> L M'" and "ioF' \<notin> L M"
    by auto
  then have "ioF' \<noteq> []" 
    by auto
  then have "ioF' = (butlast ioF')@[last ioF']" and "length (butlast ioF') < length ioF'"
    by auto
  then have "butlast ioF' \<notin> ?prefs"
    using \<open>\<And> ioF'' . ioF'' \<in> ?prefs \<Longrightarrow> length ioF' \<le> length ioF''\<close> leD by blast 
  moreover have "butlast ioF' \<in> L M'"
    using \<open>ioF' \<in> L M'\<close> language_prefix[of "butlast ioF'" "[last ioF']" M' "initial M'"] 
    unfolding \<open>ioF' = (butlast ioF')@[last ioF']\<close>[symmetric] by blast
  moreover have "butlast ioF' \<in> set (prefixes ioF)"
    using \<open>ioF' = (butlast ioF')@[last ioF']\<close> \<open>ioF' \<in> ?prefs\<close> prefixes_set
  proof -
    have "\<exists>ps. (butlast ioF' @ [last ioF']) @ ps = ioF"
      using \<open>ioF' = butlast ioF' @ [last ioF']\<close> \<open>ioF' \<in> {ioF' \<in> set (prefixes ioF). ioF' \<in> L M' \<and> ioF' \<notin> L M}\<close> 
      unfolding prefixes_set 
      by auto
    then show ?thesis
      using prefixes_set by fastforce
  qed
  ultimately have "butlast ioF' \<in> L M" 
    by blast
  
  have *: "(butlast ioF')@[(fst (last ioF'), snd (last ioF'))] \<in> L M'"
    using \<open>ioF' \<in> L M'\<close> \<open>ioF' = (butlast ioF')@[last ioF']\<close> by auto
  have **: "(butlast ioF')@[(fst (last ioF'), snd (last ioF'))] \<notin> L M"
    using \<open>ioF' \<notin> L M\<close> \<open>ioF' = (butlast ioF')@[last ioF']\<close> by auto
  
  obtain p where "path M (initial M) p" and "p_io p = butlast ioF'"
    using \<open>butlast ioF' \<in> L M\<close> by auto
  moreover obtain t where "t \<in> transitions M" 
                      and "t_source t = target (initial M) p" 
                      and "t_input t = fst (last ioF')"
  proof -
    have "fst (last ioF') \<in> inputs M'"
      using language_io(1)[OF *, of "fst (last ioF')" "snd (last ioF')"] 
      by simp 
    then have "fst (last ioF') \<in> inputs M"
      using assms(2) by auto
    then show ?thesis
      using that \<open>completely_specified M\<close> path_target_is_state[OF \<open>path M (initial M) p\<close>] 
      unfolding completely_specified.simps by blast
  qed
  ultimately have ***: "(butlast ioF')@[(fst (last ioF'), t_output t)] \<in> L M"
  proof -
    have "p_io (p @ [t]) \<in> L M"
      by (metis (no_types) \<open>path M (FSM.initial M) p\<close> \<open>t \<in> FSM.transitions M\<close> \<open>t_source t = target (FSM.initial M) p\<close> 
            language_intro path_append single_transition_path)
    then show ?thesis
      by (simp add: \<open>p_io p = butlast ioF'\<close> \<open>t_input t = fst (last ioF')\<close>)
  qed

  show ?thesis 
    using that[OF *** ** *] 
    by assumption
qed



lemma observable_minimal_path_to_failure :
  assumes "\<not> (L M' \<subseteq> L M)"
  and     "observable M" 
  and     "observable M'"
  and     "inputs M' = inputs M"  
  and     "completely_specified M"
  and     "completely_specified M'"
obtains p p' t t' where "path M (initial M) (p@[t])" 
                  and   "path M' (initial M') (p'@[t'])"
                  and   "p_io p' = p_io p"
                  and   "t_input t' = t_input t"
                  and   "\<not>(\<exists> t'' . t'' \<in> transitions M \<and> t_source t'' = target (initial M) p \<and> t_input t'' = t_input t \<and> t_output t'' = t_output t')"
proof -
               
  obtain io x y y' where "io@[(x,y)] \<in> L M" and "io@[(x,y')] \<notin>  L M" and "io@[(x,y')] \<in> L M'" 
    using minimal_io_seq_to_failure[OF assms(1,4,5)] by blast

  obtain p t where "path M (initial M) (p@[t])" and "p_io p = io" and "t_input t = x" and "t_output t = y"
    using language_append_path_ob[OF \<open>io@[(x,y)] \<in> L M\<close>] by blast

  moreover obtain p' t' where "path M' (initial M') (p'@[t'])" and "p_io p' = io" and "t_input t' = x" and "t_output t' = y'"
    using language_append_path_ob[OF \<open>io@[(x,y')] \<in> L M'\<close>] by blast

  moreover have "\<not>(\<exists> t'' . t'' \<in> transitions M \<and> t_source t'' = target (initial M) p \<and> t_input t'' = t_input t \<and> t_output t'' = t_output t')"
  proof 
    assume "\<exists>t''. t'' \<in> FSM.transitions M \<and> t_source t'' = target (FSM.initial M) p \<and> t_input t'' = t_input t \<and> t_output t'' = t_output t'"
    then obtain t'' where "t'' \<in> FSM.transitions M" and "t_source t'' = target (FSM.initial M) p" and "t_input t'' = x" and "t_output t'' = y'"
      unfolding \<open>t_input t = x\<close> \<open>t_output t' = y'\<close> by blast

    then have "path M (initial M) (p@[t''])"
      using \<open>path M (initial M) (p@[t])\<close>
      by (meson path_append_elim path_append_transition)
    moreover have "p_io (p@[t'']) = io@[(x,y')]"
      using \<open>p_io p = io\<close> \<open>t_input t'' = x\<close> \<open>t_output t'' = y'\<close> by auto
    ultimately have "io@[(x,y')] \<in> L M"
      using language_state_containment
      by (metis (mono_tags, lifting)) 
    then show "False"
      using \<open>io@[(x,y')] \<notin> L M\<close> by blast
  qed

  ultimately show ?thesis using that[of p t p' t']
    by force
qed



lemma test_suite_to_io_pass :
  assumes "implies_completeness T M m"
  and     "observable M" 
  and     "observable M'"
  and     "inputs M' = inputs M"
  and     "inputs M \<noteq> {}"
  and     "completely_specified M"
  and     "completely_specified M'"  
shows "pass_io_set M' (test_suite_to_io M T) = passes_test_suite M T M'"
proof -
  obtain prs tps rd_targets atcs where "T = Test_Suite prs tps rd_targets atcs"
    by (meson test_suite.exhaust)
  then obtain repetition_sets where repetition_sets_def: "implies_completeness_for_repetition_sets (Test_Suite prs tps rd_targets atcs) M m repetition_sets"
    using assms(1) unfolding implies_completeness_def by blast
  then have "implies_completeness (Test_Suite prs tps rd_targets atcs) M m"
    unfolding implies_completeness_def by blast
  then have test_suite_language_prop: "test_suite_to_io M (Test_Suite prs tps rd_targets atcs) \<subseteq> L M"
    using test_suite_to_io_language by blast


  have t1: "(initial M, initial_preamble M) \<in> prs" 
    using implies_completeness_for_repetition_sets_simps(1)[OF repetition_sets_def] 
    by assumption
  have t2: "\<And> q P. (q, P) \<in> prs \<Longrightarrow> is_preamble P M q"
    using implies_completeness_for_repetition_sets_simps(2)[OF repetition_sets_def] 
    by blast
  have t3: "\<And> q1 q2 A d1 d2. (A, d1, d2) \<in> atcs (q1, q2) \<Longrightarrow> (A, d2, d1) \<in> atcs (q2, q1) \<and> is_separator M q1 q2 A d1 d2"
    using implies_completeness_for_repetition_sets_simps(3)[OF repetition_sets_def] 
    by assumption
  
  have t5: "\<And>q. q \<in> FSM.states M \<Longrightarrow> (\<exists>d\<in>set repetition_sets. q \<in> fst d)"
    using implies_completeness_for_repetition_sets_simps(4)[OF repetition_sets_def] 
    by assumption

  have t6: "\<And> q. q \<in> fst ` prs \<Longrightarrow> tps q \<subseteq> {p1 . \<exists> p2 d . (p1@p2,d) \<in> m_traversal_paths_with_witness M q repetition_sets m} \<and> fst ` (m_traversal_paths_with_witness M q repetition_sets m) \<subseteq> tps q"
    using implies_completeness_for_repetition_sets_simps(7)[OF repetition_sets_def] 
    by assumption

  have t7: "\<And> d. d \<in> set repetition_sets \<Longrightarrow> fst d \<subseteq> FSM.states M"
  and  t8: "\<And> d. d \<in> set repetition_sets \<Longrightarrow> snd d \<subseteq> fst d"
  and  t8':  "\<And> d. d \<in> set repetition_sets \<Longrightarrow> snd d = fst d \<inter> fst ` prs"
  and  t9: "\<And> d q1 q2. d \<in> set repetition_sets \<Longrightarrow> q1 \<in> fst d \<Longrightarrow> q2 \<in> fst d \<Longrightarrow> q1 \<noteq> q2 \<Longrightarrow> atcs (q1, q2) \<noteq> {}"
    using implies_completeness_for_repetition_sets_simps(5,6)[OF repetition_sets_def] 
    by blast+
    

  have "pass_io_set M' (test_suite_to_io M (Test_Suite prs tps rd_targets atcs)) \<Longrightarrow> passes_test_suite M (Test_Suite prs tps rd_targets atcs) M'"
  proof -
    assume "pass_io_set M' (test_suite_to_io M (Test_Suite prs tps rd_targets atcs))"

    then have pass_io_prop: "\<And> io x y y' . io @ [(x, y)] \<in> test_suite_to_io M (Test_Suite prs tps rd_targets atcs) \<Longrightarrow> io @ [(x, y')] \<in> L M' \<Longrightarrow> io @ [(x, y')] \<in> test_suite_to_io M (Test_Suite prs tps rd_targets atcs)"
      unfolding pass_io_set_def 
      by blast

    show "passes_test_suite M (Test_Suite prs tps rd_targets atcs) M'"
    proof (rule ccontr)
      assume "\<not> passes_test_suite M (Test_Suite prs tps rd_targets atcs) M'"


      then consider (a) "\<not> (\<forall>q P io x y y'. (q, P) \<in> prs \<longrightarrow> io @ [(x, y)] \<in> L P \<longrightarrow> io @ [(x, y')] \<in> L M' \<longrightarrow> io @ [(x, y')] \<in> L P)" |
                    (b) "\<not> ((\<forall>q P pP ioT pT x y y'.
                              (q, P) \<in> prs \<longrightarrow>
                              path P (FSM.initial P) pP \<longrightarrow>
                              target (FSM.initial P) pP = q \<longrightarrow>
                              pT \<in> tps q \<longrightarrow>
                              ioT @ [(x, y)] \<in> set (prefixes (p_io pT)) \<longrightarrow>
                              p_io pP @ ioT @ [(x, y')] \<in> L M' \<longrightarrow> (\<exists>pT'. pT' \<in> tps q \<and> ioT @ [(x, y')] \<in> set (prefixes (p_io pT')))))" |
                    (c) "\<not> ((\<forall>q P pP pT.
                              (q, P) \<in> prs \<longrightarrow>
                              path P (FSM.initial P) pP \<longrightarrow>
                              target (FSM.initial P) pP = q \<longrightarrow>
                              pT \<in> tps q \<longrightarrow>
                              p_io pP @ p_io pT \<in> L M' \<longrightarrow>
                              (\<forall>q' A d1 d2 qT.
                                  q' \<in> rd_targets (q, pT) \<longrightarrow>
                                  (A, d1, d2) \<in> atcs (target q pT, q') \<longrightarrow> qT \<in> io_targets M' (p_io pP @ p_io pT) (FSM.initial M') \<longrightarrow> pass_separator_ATC M' A qT d2)))"  
        unfolding passes_test_suite.simps by blast
      then show False proof cases
        case a
        then obtain q P io x y y' where "(q, P) \<in> prs" 
                                    and "io @ [(x, y)] \<in> L P" 
                                    and "io @ [(x, y')] \<in> L M'" 
                                    and "io @ [(x, y')] \<notin> L P"
          by blast

        have "is_preamble P M q"
          using t2[OF \<open>(q, P) \<in> prs\<close>] by assumption
        

        have "io @ [(x, y)] \<in> test_suite_to_io M (Test_Suite prs tps rd_targets atcs)"
          unfolding test_suite_to_io.simps using \<open>(q, P) \<in> prs\<close> \<open>io @ [(x, y)] \<in> L P\<close>
          by fastforce

        have "io @ [(x, y')] \<in> test_suite_to_io M (Test_Suite prs tps rd_targets atcs)"
          using pass_io_prop[OF \<open>io @ [(x, y)] \<in> test_suite_to_io M (Test_Suite prs tps rd_targets atcs)\<close> \<open>io @ [(x, y')] \<in> L M'\<close>] 
          by assumption

        then have "io @ [(x, y')] \<in> L M"
          using test_suite_language_prop 
          by blast

        have "io @ [(x, y')] \<in> L P"
          using passes_test_suite_soundness_helper_1[OF \<open>is_preamble P M q\<close> \<open>observable M\<close> \<open>io @ [(x, y)] \<in> L P\<close> \<open>io @ [(x, y')] \<in> L M\<close>] 
          by assumption
        then show "False"
          using \<open>io @ [(x, y')] \<notin> L P\<close> 
          by blast

      next
        case b
        then obtain q P pP ioT pT x y y' where "(q, P) \<in> prs"
                                           and "path P (FSM.initial P) pP"
                                           and "target (FSM.initial P) pP = q"
                                           and "pT \<in> tps q"
                                           and "ioT @ [(x, y)] \<in> set (prefixes (p_io pT))"
                                           and "p_io pP @ ioT @ [(x, y')] \<in> L M'"
                                           and "\<not> (\<exists>pT'. pT' \<in> tps q \<and> ioT @ [(x, y')] \<in> set (prefixes (p_io pT')))"
          by blast

        have "\<exists>q P. (q, P) \<in> prs \<and> path P (FSM.initial P) pP \<and> target (FSM.initial P) pP = q \<and> pT \<in> tps q"
          using \<open>(q, P) \<in> prs\<close> \<open>path P (FSM.initial P) pP\<close> \<open>target (FSM.initial P) pP = q\<close> \<open>pT \<in> tps q\<close> by blast
        moreover have "p_io pP @ ioT @ [(x, y)] \<in> (@) (p_io pP) ` set (prefixes (p_io pT))"
          using \<open>ioT @ [(x, y)] \<in> set (prefixes (p_io pT))\<close> by auto
        ultimately have "p_io pP @ ioT @ [(x, y)] \<in> (\<Union>{(@) (p_io p) ` set (prefixes (p_io pt)) |p pt. \<exists>q P. (q, P) \<in> prs \<and> path P (FSM.initial P) p \<and> target (FSM.initial P) p = q \<and> pt \<in> tps q})"
          by blast
        then have "p_io pP @ ioT @ [(x, y)] \<in> test_suite_to_io M (Test_Suite prs tps rd_targets atcs)"
          unfolding test_suite_to_io.simps  
          by blast
        then have *: "(p_io pP @ ioT) @ [(x, y)] \<in> test_suite_to_io M (Test_Suite prs tps rd_targets atcs)"
          by auto

        have **: "(p_io pP @ ioT) @ [(x, y')] \<in> L M'"
          using \<open>p_io pP @ ioT @ [(x, y')] \<in> L M'\<close> by auto

        have "(p_io pP @ ioT) @ [(x, y')] \<in> test_suite_to_io M (Test_Suite prs tps rd_targets atcs)"
          using pass_io_prop[OF * ** ] by assumption
        then have "(p_io pP @ ioT) @ [(x, y')] \<in> L M"
          using test_suite_language_prop by blast

        have "q \<in> states M"
          using is_preamble_is_state[OF t2[OF \<open>(q, P) \<in> prs\<close>]] by assumption

        have "q \<in> fst ` prs" 
          using \<open>(q, P) \<in> prs\<close> by force

        obtain pT' d' where "(pT @ pT', d') \<in> m_traversal_paths_with_witness M q repetition_sets m"
          using t6[OF \<open>q \<in> fst ` prs\<close>] \<open>pT \<in> tps q\<close> by blast

        then have "path M q (pT @ pT')"
             and  "find (\<lambda>d. Suc (m - card (snd d)) \<le> length (filter (\<lambda>t. t_target t \<in> fst d) (pT @ pT'))) repetition_sets = Some d'"
             and  "\<And> p' p''. (pT @ pT') = p' @ p'' \<Longrightarrow> p'' \<noteq> [] \<Longrightarrow> find (\<lambda>d. Suc (m - card (snd d)) \<le> length (filter (\<lambda>t. t_target t \<in> fst d) p')) repetition_sets = None"
          using m_traversal_paths_with_witness_set[OF t5 t8 \<open>q \<in> states M\<close>, of m]
          by blast+

        obtain ioT' where "p_io pT = ioT @ [(x,y)] @ ioT'"
          using prefixes_set_ob[OF \<open>ioT @ [(x, y)] \<in> set (prefixes (p_io pT))\<close>] 
          unfolding prefixes_set append.assoc[symmetric] 
          by blast

        let ?pt = "take (length (ioT @ [(x,y)])) pT"
        let ?p  = "butlast ?pt"
        let ?t  = "last ?pt"
         

        have "length ?pt > 0"
          using \<open>p_io pT = ioT @ [(x,y)] @ ioT'\<close> 
          unfolding length_map[of "(\<lambda> t . (t_input t, t_output t))", symmetric] 
          by auto
        then have "?pt = ?p @ [?t]"
          by auto
        moreover have "path M q ?pt"
          using \<open>path M q (pT @ pT')\<close>
          by (meson path_prefix path_prefix_take)
        ultimately have "path M q (?p@[?t])"
          by simp

        have "p_io ?p = ioT"
        proof -
          have "p_io ?pt = take (length (ioT @ [(x,y)])) (p_io pT)"
            by (simp add: take_map) 
          then have "p_io ?pt = ioT @ [(x,y)]"
            using \<open>p_io pT = ioT @ [(x,y)] @ ioT'\<close> by auto
          then show ?thesis
            by (simp add: map_butlast) 
        qed

        have "path M q ?p"
          using path_append_transition_elim[OF \<open>path M q (?p@[?t])\<close>] by blast
        
        have "is_submachine P M"
          using t2[OF \<open>(q, P) \<in> prs\<close>] unfolding is_preamble_def by blast
        then have "initial P = initial M" by auto
    
        have "path M (initial M) pP"
          using submachine_path[OF \<open>is_submachine P M\<close> \<open>path P (initial P) pP\<close>] 
          unfolding \<open>initial P = initial M\<close> 
          by assumption
        moreover have "target (initial M) pP = q"
          using \<open>target (initial P) pP = q\<close> 
          unfolding \<open>initial P = initial M\<close> 
          by assumption
        ultimately have "path M (initial M) (pP@?p)" 
          using \<open>path M q ?p\<close> 
          by auto
      

        have "find (\<lambda>d. Suc (m - card (snd d)) \<le> length (filter (\<lambda>t. t_target t \<in> fst d) ?p)) repetition_sets = None"
        proof -
          have *: "(pT @ pT') = ?p @ ([?t] @ (drop (length (ioT @ [(x,y)])) pT) @ pT')" 
            using \<open>?pt = ?p @ [?t]\<close>
            by (metis append_assoc append_take_drop_id) 
          have **: "([?t] @ (drop (length (ioT @ [(x,y)])) pT) @ pT') \<noteq> []"
            by simp
          show ?thesis 
            using \<open>\<And> p' p''. (pT @ pT') = p' @ p'' \<Longrightarrow> p'' \<noteq> [] \<Longrightarrow> find (\<lambda>d. Suc (m - card (snd d)) \<le> length (filter (\<lambda>t. t_target t \<in> fst d) p')) repetition_sets = None\<close>[OF * **] 
            by assumption
        qed


        (* obtain paths from the transition ending in y' to get a transition from ?p *)
        obtain p' t' where "path M (FSM.initial M) (p' @ [t'])" and "p_io p' = p_io pP @ ioT" and "t_input t' = x" and "t_output t' = y'"
          using language_append_path_ob[OF \<open>(p_io pP @ ioT) @ [(x, y')] \<in> L M\<close>] by blast
        then have "path M (FSM.initial M) p'" and "t_source t' = target (initial M) p'" and "t' \<in> transitions M"
          by auto
        
        have "p' = pP @ ?p"
          using observable_path_unique[OF \<open>observable M\<close> \<open>path M (FSM.initial M) p'\<close> \<open>path M (initial M) (pP@?p)\<close>] 
                \<open>p_io ?p = ioT\<close> 
          unfolding \<open>p_io p' = p_io pP @ ioT\<close>
          by simp 
        then have "t_source t' = target q ?p"
          unfolding \<open>t_source t' = target (initial M) p'\<close> using \<open>target (initial M) pP = q\<close>
          by auto  
                
        obtain pTt' dt' where "(?p @ [t'] @ pTt', dt') \<in> m_traversal_paths_with_witness M q repetition_sets m"
          using m_traversal_path_extension_exist_for_transition[OF \<open>completely_specified M\<close> \<open>q \<in> states M\<close> \<open>FSM.inputs M \<noteq> {}\<close> 
                                                                   t5 t8 \<open>path M q ?p\<close> \<open>find (\<lambda>d. Suc (m - card (snd d)) \<le> length (filter (\<lambda>t. t_target t \<in> fst d) ?p)) repetition_sets = None\<close> 
                                                                   \<open>t' \<in> transitions M\<close> \<open>t_source t' = target q ?p\<close>]
          by blast

        have "?p @ [t'] @ pTt' \<in> tps q"
          using t6[OF \<open>q \<in> fst ` prs\<close> ] \<open>(?p @ [t'] @ pTt', dt') \<in> m_traversal_paths_with_witness M q repetition_sets m\<close>
          by force
        moreover have "ioT @ [(x, y')] \<in> set (prefixes (p_io (?p @ [t'] @ pTt')))"
        proof -
          have "p_io (?p @ [t'] @ pTt') = ioT @ [(x,y')] @ p_io pTt'"
            using \<open>p_io ?p = ioT\<close> using \<open>t_input t' = x\<close> \<open>t_output t' = y'\<close> 
            by auto  
          then show ?thesis 
            unfolding prefixes_set
            by force
        qed

        ultimately show "False"
          using \<open>\<not> (\<exists>pT'. pT' \<in> tps q \<and> ioT @ [(x, y')] \<in> set (prefixes (p_io pT')))\<close> 
          by blast
      next
        case c

        then obtain q P pP pT q' A d1 d2 qT  where "(q, P) \<in> prs"
                                             and   "path P (FSM.initial P) pP"
                                             and   "target (FSM.initial P) pP = q"
                                             and   "pT \<in> tps q"
                                             and   "p_io pP @ p_io pT \<in> L M'"
                                             and   "q' \<in> rd_targets (q, pT)"
                                             and   "(A, d1, d2) \<in> atcs (target q pT, q')"
                                             and   "qT \<in> io_targets M' (p_io pP @ p_io pT) (FSM.initial M')"
                                             and   "\<not>pass_separator_ATC M' A qT d2"
          by blast


        have "is_submachine P M"
          using t2[OF \<open>(q, P) \<in> prs\<close>] 
          unfolding is_preamble_def 
          by blast
        then have "initial P = initial M" by auto
    
        have "path M (initial M) pP"
          using submachine_path[OF \<open>is_submachine P M\<close> \<open>path P (initial P) pP\<close>] 
          unfolding \<open>initial P = initial M\<close> 
          by assumption
        have "target (initial M) pP = q"
          using \<open>target (initial P) pP = q\<close> 
          unfolding \<open>initial P = initial M\<close> 
          by assumption

        have "q \<in> states M"
          using is_preamble_is_state[OF t2[OF \<open>(q, P) \<in> prs\<close>]] 
          by assumption

        have "q \<in> fst ` prs" 
          using \<open>(q, P) \<in> prs\<close> by force

        obtain pT' d' where "(pT @ pT', d') \<in> m_traversal_paths_with_witness M q repetition_sets m"
          using t6[OF \<open>q \<in> fst ` prs\<close>] \<open>pT \<in> tps q\<close> by blast

        then have "path M q (pT @ pT')"
             and  "find (\<lambda>d. Suc (m - card (snd d)) \<le> length (filter (\<lambda>t. t_target t \<in> fst d) (pT @ pT'))) repetition_sets = Some d'"
             and  "\<And> p' p''. (pT @ pT') = p' @ p'' \<Longrightarrow> p'' \<noteq> [] \<Longrightarrow> find (\<lambda>d. Suc (m - card (snd d)) \<le> length (filter (\<lambda>t. t_target t \<in> fst d) p')) repetition_sets = None"
          using m_traversal_paths_with_witness_set[OF t5 t8 \<open>q \<in> states M\<close>, of m]
          by blast+
        then have "path M q pT"
          by auto

        have "qT \<in> states M'"
          using \<open>qT \<in> io_targets M' (p_io pP @ p_io pT) (FSM.initial M')\<close> io_targets_states subset_iff 
          by fastforce 



        have "is_separator M (target q pT) q' A d1 d2"
          using  t3[OF \<open>(A, d1, d2) \<in> atcs (target q pT, q')\<close>] by blast

        have "\<not> pass_io_set (FSM.from_FSM M' qT) (atc_to_io_set (FSM.from_FSM M (target q pT)) A)"
          using \<open>\<not>pass_separator_ATC M' A qT d2\<close>
                pass_separator_pass_io_set_iff[OF \<open>is_separator M (target q pT) q' A d1 d2\<close> \<open>observable M\<close> 
                                                  \<open>observable M'\<close> path_target_is_state[OF \<open>path M q pT\<close>] 
                                                  \<open>qT \<in> states M'\<close> \<open>inputs M' = inputs M\<close> \<open>completely_specified M\<close>]
          by simp


        have "pass_io_set (FSM.from_FSM M' qT) (atc_to_io_set (FSM.from_FSM M (target q pT)) A)"
        proof -
          have "\<And> io x y y' . io @ [(x, y)] \<in> atc_to_io_set (FSM.from_FSM M (target q pT)) A \<Longrightarrow>
                               io @ [(x, y')] \<in> L (FSM.from_FSM M' qT) \<Longrightarrow> 
                                io @ [(x, y')] \<in> atc_to_io_set (FSM.from_FSM M (target q pT)) A"
          proof -
            fix io x y y' assume "io @ [(x, y)] \<in> atc_to_io_set (FSM.from_FSM M (target q pT)) A"
                          and    "io @ [(x, y')] \<in> L (FSM.from_FSM M' qT)"


            (* subsets of test_suite_to_io *)
            define tmp where tmp_def : "tmp = (\<Union> {(\<lambda>io_atc. p_io p @ p_io pt @ io_atc) ` atc_to_io_set (FSM.from_FSM M (target q pt)) A |p pt q A. \<exists>P q' t1 t2. (q, P) \<in> prs \<and> path P (FSM.initial P) p \<and> target (FSM.initial P) p = q \<and> pt \<in> tps q \<and> q' \<in> rd_targets (q, pt) \<and> (A, t1, t2) \<in> atcs (target q pt, q')})"
            define tmp2 where tmp2_def : "tmp2 = \<Union> {(@) (p_io p) ` set (prefixes (p_io pt)) |p pt. \<exists>q P. (q, P) \<in> prs \<and> path P (FSM.initial P) p \<and> target (FSM.initial P) p = q \<and> pt \<in> tps q}"
            have "\<exists>P q' t1 t2. (q, P) \<in> prs \<and> path P (FSM.initial P) pP \<and> target (FSM.initial P) pP = q \<and> pT \<in> tps q \<and> q' \<in> rd_targets (q, pT) \<and> (A, t1, t2) \<in> atcs (target q pT, q')"
              using \<open>(q, P) \<in> prs\<close> \<open>path P (FSM.initial P) pP\<close> \<open>target (FSM.initial P) pP = q\<close> \<open>pT \<in> tps q\<close> \<open>q' \<in> rd_targets (q, pT)\<close> \<open>(A, d1, d2) \<in> atcs (target q pT, q')\<close> by blast
            then have "(\<lambda>io_atc. p_io pP @ p_io pT @ io_atc) ` atc_to_io_set (FSM.from_FSM M (target q pT)) A \<subseteq> tmp"
              unfolding tmp_def by blast
            then have "(\<lambda>io_atc. p_io pP @ p_io pT @ io_atc) ` atc_to_io_set (FSM.from_FSM M (target q pT)) A \<subseteq> test_suite_to_io M (Test_Suite prs tps rd_targets atcs)"
              unfolding test_suite_to_io.simps tmp_def[symmetric] tmp2_def[symmetric] by blast
            moreover have "(p_io pP @ p_io pT @ (io @ [(x, y)])) \<in> (\<lambda>io_atc. p_io pP @ p_io pT @ io_atc) ` atc_to_io_set (FSM.from_FSM M (target q pT)) A"
              using \<open>io @ [(x, y)] \<in> atc_to_io_set (FSM.from_FSM M (target q pT)) A\<close> by auto
            ultimately have "(p_io pP @ p_io pT @ (io @ [(x, y)])) \<in> test_suite_to_io M (Test_Suite prs tps rd_targets atcs)"
              by blast
            then have *: "(p_io pP @ p_io pT @ io) @ [(x, y)] \<in> test_suite_to_io M (Test_Suite prs tps rd_targets atcs)"
              by simp

            have "io @ [(x, y')] \<in> LS M' qT"
              using \<open>io @ [(x, y')] \<in> L (FSM.from_FSM M' qT)\<close> \<open>qT \<in> states M'\<close>
              by (metis from_FSM_language) 
            have **: "(p_io pP @ p_io pT @ io) @ [(x, y')] \<in> L M'" 
              using io_targets_language_append[OF \<open>qT \<in> io_targets M' (p_io pP @ p_io pT) (FSM.initial M')\<close> \<open>io @ [(x, y')] \<in> LS M' qT\<close>] 
              by simp            
            
            have "(p_io pP @ p_io pT) @ (io @ [(x, y')]) \<in> test_suite_to_io M (Test_Suite prs tps rd_targets atcs)"
              using pass_io_prop[OF * ** ] by simp
            then have "(p_io pP @ p_io pT) @ (io @ [(x, y')]) \<in> L M"
              using test_suite_language_prop by blast

            moreover have "target q pT \<in> io_targets M (p_io pP @ p_io pT) (initial M)"
            proof -
              have "target (initial M) (pP@pT) = target q pT"
                unfolding \<open>target (initial M) pP = q\<close>[symmetric] by auto
              moreover have "path M (initial M) (pP@pT)"
                using \<open>path M (initial M) pP\<close> \<open>path M q pT\<close> unfolding \<open>target (initial M) pP = q\<close>[symmetric] 
                by auto
              moreover have "p_io (pP@pT) = (p_io pP @ p_io pT)" 
                by auto
              ultimately show ?thesis
                unfolding io_targets.simps
                by (metis (mono_tags, lifting) mem_Collect_eq) 
            qed

            ultimately have "io @ [(x, y')] \<in> LS M (target q pT)"
              using observable_io_targets_language[OF _ \<open>observable M\<close>, of "(p_io pP @ p_io pT)" "(io @ [(x, y')])" "initial M" "target q pT"] 
              by blast            
            then have "io @ [(x, y')] \<in> L (FSM.from_FSM M (target q pT))"
              unfolding from_FSM_language[OF path_target_is_state[OF \<open>path M q pT\<close>]] 
              by assumption

            moreover have "io @ [(x, y')] \<in> L A"
              by (metis Int_iff \<open>io @ [(x, y')] \<in> LS M (target q pT)\<close> \<open>io @ [(x, y)] \<in> atc_to_io_set (FSM.from_FSM M (target q pT)) A\<close> 
                      \<open>is_separator M (target q pT) q' A d1 d2\<close> atc_to_io_set.simps is_separator_simps(9))
              
            ultimately show "io @ [(x, y')] \<in> atc_to_io_set (FSM.from_FSM M (target q pT)) A"
              unfolding atc_to_io_set.simps by blast
          qed
              
          then show ?thesis unfolding pass_io_set_def by blast
        qed

        then show "False"
          using pass_separator_from_pass_io_set[OF \<open>is_separator M (target q pT) q' A d1 d2\<close> _ \<open>observable M\<close> 
                                                   \<open>observable M'\<close> path_target_is_state[OF \<open>path M q pT\<close>] 
                                                   \<open>qT \<in> states M'\<close> \<open>inputs M' = inputs M\<close> \<open>completely_specified M\<close>]
                \<open>\<not>pass_separator_ATC M' A qT d2\<close>
          by simp
      qed
    qed
  qed

  moreover have "passes_test_suite M (Test_Suite prs tps rd_targets atcs) M' \<Longrightarrow> pass_io_set M' (test_suite_to_io M (Test_Suite prs tps rd_targets atcs))"
  proof -
    assume "passes_test_suite M (Test_Suite prs tps rd_targets atcs) M'"

    (* pass properties *)
  
    have pass1: "\<And> q P io x y y' . (q,P) \<in> prs \<Longrightarrow> io@[(x,y)] \<in> L P \<Longrightarrow> io@[(x,y')] \<in> L M' \<Longrightarrow> io@[(x,y')] \<in> L P" 
      using \<open>passes_test_suite M (Test_Suite prs tps rd_targets atcs) M'\<close>
      unfolding passes_test_suite.simps
      by meson 
  
    have pass2: "\<And> q P pP ioT pT x y y' . (q,P) \<in> prs \<Longrightarrow> path P (initial P) pP \<Longrightarrow> target (initial P) pP = q \<Longrightarrow> pT \<in> tps q \<Longrightarrow> ioT@[(x,y)] \<in> set (prefixes (p_io pT)) \<Longrightarrow> (p_io pP)@ioT@[(x,y')] \<in> L M' \<Longrightarrow> (\<exists> pT' . pT' \<in> tps q \<and> ioT@[(x,y')] \<in> set (prefixes (p_io pT')))"
      using \<open>passes_test_suite M (Test_Suite prs tps rd_targets atcs) M'\<close>
      unfolding passes_test_suite.simps by blast
  
    have pass3: "\<And> q P pP pT q' A d1 d2 qT . (q,P) \<in> prs \<Longrightarrow> path P (initial P) pP \<Longrightarrow> target (initial P) pP = q \<Longrightarrow> pT \<in> tps q \<Longrightarrow> (p_io pP)@(p_io pT) \<in> L M' \<Longrightarrow> q' \<in> rd_targets (q,pT) \<Longrightarrow> (A,d1,d2) \<in> atcs (target q pT, q') \<Longrightarrow> qT \<in> io_targets M' ((p_io pP)@(p_io pT)) (initial M') \<Longrightarrow> pass_separator_ATC M' A qT d2"  
      using \<open>passes_test_suite M (Test_Suite prs tps rd_targets atcs) M'\<close>
      unfolding passes_test_suite.simps by blast



    show "pass_io_set M' (test_suite_to_io M (Test_Suite prs tps rd_targets atcs))"
    proof (rule ccontr)
      assume "\<not> pass_io_set M' (test_suite_to_io M (Test_Suite prs tps rd_targets atcs))"
      then obtain io x y y' where "io @ [(x, y)] \<in> test_suite_to_io M (Test_Suite prs tps rd_targets atcs)"
                            and   "io @ [(x, y')] \<in> L M'" 
                            and   "io @ [(x, y')] \<notin> test_suite_to_io M (Test_Suite prs tps rd_targets atcs)"
        unfolding pass_io_set_def by blast
          
       

      have preamble_prop: "\<And> q P . (q, P) \<in> prs \<Longrightarrow> io @ [(x, y)] \<in> L P \<Longrightarrow> False"
      proof - 
        fix q P assume "(q, P)\<in>prs" and "io @ [(x, y)] \<in> L P" 
        have "io @ [(x, y')] \<in> L P" using pass1[OF \<open>(q, P)\<in>prs\<close> \<open>io @ [(x, y)] \<in> L P\<close> \<open>io @ [(x, y')] \<in> L M'\<close> ] 
          by assumption
        then have "io @ [(x, y')] \<in> test_suite_to_io M (Test_Suite prs tps rd_targets atcs)"
          unfolding test_suite_to_io.simps using \<open>(q, P)\<in>prs\<close> by blast
        then show "False" using \<open>io @ [(x, y')] \<notin> test_suite_to_io M (Test_Suite prs tps rd_targets atcs)\<close> 
          by simp
      qed

      have traversal_path_prop : "\<And> pP pt q P .  io @ [(x, y)] \<in> (@) (p_io pP) ` set (prefixes (p_io pt)) \<Longrightarrow> (q, P) \<in> prs \<Longrightarrow> path P (FSM.initial P) pP \<Longrightarrow> target (FSM.initial P) pP = q \<Longrightarrow> pt \<in> tps q \<Longrightarrow> False"
      proof -
        fix pP pt q P assume "io @ [(x, y)] \<in> (@) (p_io pP) ` set (prefixes (p_io pt))"
                       and   "(q, P) \<in> prs" 
                       and   "path P (FSM.initial P) pP"
                       and   "target (FSM.initial P) pP = q"
                       and   "pt \<in> tps q"

        obtain io' io'' where "io @ [(x, y)] = (p_io pP) @ io'" and "io'@io'' = p_io pt"
          using \<open>io @ [(x, y)] \<in> (@) (p_io pP) ` set (prefixes (p_io pt))\<close> 
          unfolding prefixes_set
          by blast 


        have "is_submachine P M"
          using t2[OF \<open>(q, P) \<in> prs\<close>] 
          unfolding is_preamble_def 
          by blast
        then have "initial P = initial M" 
          by auto
    
        have "path M (initial M) pP"
          using submachine_path[OF \<open>is_submachine P M\<close> \<open>path P (initial P) pP\<close>] 
          unfolding \<open>initial P = initial M\<close> 
          by assumption
        have "target (initial M) pP = q"
          using \<open>target (initial P) pP = q\<close> 
          unfolding \<open>initial P = initial M\<close> 
          by assumption

        have "q \<in> states M"
          using is_preamble_is_state[OF t2[OF \<open>(q, P) \<in> prs\<close>]] 
          by assumption

        have "q \<in> fst ` prs" 
          using \<open>(q, P) \<in> prs\<close> by force


        show "False" proof (cases io' rule: rev_cases)
          case Nil
          then have "p_io pP = io @ [(x, y)]" 
            using \<open>io @ [(x, y)] = (p_io pP) @ io'\<close>
            by auto
          show ?thesis
            using preamble_prop[OF \<open>(q,P) \<in> prs\<close> language_state_containment[OF \<open>path P (FSM.initial P) pP\<close> \<open>p_io pP = io @ [(x, y)]\<close>]]
            by assumption
        next
          case (snoc ioI xy)
          then have "xy = (x,y)" and "io = (p_io pP) @ ioI"
            using \<open>io @ [(x, y)] = (p_io pP) @ io'\<close> by auto 
          then have "p_io pP @ ioI @ [(x, y')] \<in> L M'"
            using \<open>io @ [(x, y')] \<in> L M'\<close> by simp

          have "ioI @ [(x, y)] \<in> set (prefixes (p_io pt))"
            unfolding prefixes_set
            using \<open>io' @ io'' = p_io pt\<close> \<open>xy = (x, y)\<close> snoc 
            by auto 

          obtain pT' where "pT' \<in> tps q" and "ioI @ [(x, y')] \<in> set (prefixes (p_io pT'))"
            using pass2[OF \<open>(q, P) \<in> prs\<close> \<open>path P (FSM.initial P) pP\<close> \<open>target (FSM.initial P) pP = q\<close> \<open>pt \<in> tps q\<close>
                           \<open>ioI @ [(x, y)] \<in> set (prefixes (p_io pt))\<close> \<open>p_io pP @ ioI @ [(x, y')] \<in> L M'\<close>] by blast

          have "io @ [(x, y')] \<in> (@) (p_io pP) ` set (prefixes (p_io pT'))"
            using \<open>ioI @ [(x, y')] \<in> set (prefixes (p_io pT'))\<close> 
            unfolding \<open>io = (p_io pP) @ ioI\<close>
            by simp

          
          have "io @ [(x, y')] \<in> (\<Union> {(@) (p_io p) ` set (prefixes (p_io pt)) |p pt. \<exists>q P. (q, P) \<in> prs \<and> path P (FSM.initial P) p \<and> target (FSM.initial P) p = q \<and> pt \<in> tps q})"
            using \<open>(q, P) \<in> prs\<close> \<open>path P (FSM.initial P) pP\<close> \<open>target (FSM.initial P) pP = q\<close> 
                  \<open>pT' \<in> tps q\<close> \<open>io @ [(x, y')] \<in> (@) (p_io pP) ` set (prefixes (p_io pT'))\<close> 
            by blast
          then have "io @ [(x, y')] \<in> test_suite_to_io M (Test_Suite prs tps rd_targets atcs)"
            unfolding test_suite_to_io.simps 
            by blast

          then show "False"
            using \<open>io @ [(x, y')] \<notin> test_suite_to_io M (Test_Suite prs tps rd_targets atcs)\<close> 
            by blast
        qed
      qed

      consider (a) "io @ [(x, y)] \<in> (\<Union>(q, P)\<in>prs. L P)" |
               (b) "io @ [(x, y)] \<in> (\<Union> {(@) (p_io p) ` set (prefixes (p_io pt)) |p pt. \<exists>q P. (q, P) \<in> prs \<and> path P (FSM.initial P) p \<and> target (FSM.initial P) p = q \<and> pt \<in> tps q})" |
               (c) "io @ [(x, y)] \<in> (\<Union> {(\<lambda>io_atc. p_io p @ p_io pt @ io_atc) ` atc_to_io_set (FSM.from_FSM M (target q pt)) A |p pt q A.
                                           \<exists>P q' t1 t2.
                                              (q, P) \<in> prs \<and>
                                              path P (FSM.initial P) p \<and> target (FSM.initial P) p = q \<and> pt \<in> tps q \<and> q' \<in> rd_targets (q, pt) \<and> (A, t1, t2) \<in> atcs (target q pt, q')})"
        using \<open>io @ [(x, y)] \<in> test_suite_to_io M (Test_Suite prs tps rd_targets atcs)\<close>
        unfolding test_suite_to_io.simps by blast

      then show "False" proof cases
        case a 
        then show ?thesis using preamble_prop by blast
      next
        case b
        then show ?thesis using traversal_path_prop by blast
      next
        case c

        then obtain pP pt q A P q' t1 t2 where "io @ [(x, y)] \<in> (\<lambda>io_atc. p_io pP @ p_io pt @ io_atc) ` atc_to_io_set (FSM.from_FSM M (target q pt)) A"
                                          and "(q, P) \<in> prs"
                                          and "path P (FSM.initial P) pP"
                                          and "target (FSM.initial P) pP = q" 
                                          and "pt \<in> tps q" 
                                          and "q' \<in> rd_targets (q, pt)" 
                                          and "(A, t1, t2) \<in> atcs (target q pt, q')"
          by blast

        obtain ioA where "io @ [(x, y)] = p_io pP @ p_io pt @ ioA"
          using \<open>io @ [(x, y)] \<in> (\<lambda>io_atc. p_io pP @ p_io pt @ io_atc) ` atc_to_io_set (FSM.from_FSM M (target q pt)) A\<close> 
          unfolding prefixes_set
          by blast 

        show "False" proof (cases ioA rule: rev_cases)
          case Nil
          then have "io @ [(x, y)] = p_io pP @ p_io pt"
            using \<open>io @ [(x, y)] = p_io pP @ p_io pt @ ioA\<close> by simp
          then have "io @ [(x, y)] \<in> (@) (p_io pP) ` set (prefixes (p_io pt))"
            unfolding prefixes_set by blast
          show ?thesis 
            using traversal_path_prop[OF \<open>io @ [(x, y)] \<in> (@) (p_io pP) ` set (prefixes (p_io pt))\<close> \<open>(q, P) \<in> prs\<close> 
                                         \<open>path P (FSM.initial P) pP\<close> \<open>target (FSM.initial P) pP = q\<close> \<open>pt \<in> tps q\<close>]
            by assumption
        next
          case (snoc ioAI xy)
          then have "xy = (x,y)" and "io = p_io pP @ p_io pt @ ioAI"
            using \<open>io @ [(x, y)] = p_io pP @ p_io pt @ ioA\<close> by simp+
          then have "p_io pP @ p_io pt @ ioAI @ [(x,y)] \<in> (\<lambda>io_atc. p_io pP @ p_io pt @ io_atc) ` atc_to_io_set (FSM.from_FSM M (target q pt)) A"
            using \<open>io @ [(x, y)] \<in> (\<lambda>io_atc. p_io pP @ p_io pt @ io_atc) ` atc_to_io_set (FSM.from_FSM M (target q pt)) A\<close> 
            by auto
          then have "ioAI @ [(x,y)] \<in> atc_to_io_set (FSM.from_FSM M (target q pt)) A" 
            by auto


          have "p_io pP @ p_io pt \<in> L M'"
            using \<open>io @ [(x,y')] \<in> L M'\<close> language_prefix[of "p_io pP @ p_io pt" "ioAI @ [(x, y')]" M' "initial M'"] 
            unfolding \<open>io = p_io pP @ p_io pt @ ioAI\<close>
            by simp
          then obtain pt' where "path M' (initial M') pt'" and "p_io pt' = p_io pP @ p_io pt"
            by auto
          then have  "target (initial M') pt' \<in> io_targets M' (p_io pP @ p_io pt) (FSM.initial M')"
            by fastforce
              
            
          have "pass_separator_ATC M' A (target (FSM.initial M') pt') t2"
            using pass3[OF \<open>(q, P) \<in> prs\<close> \<open>path P (FSM.initial P) pP\<close> \<open>target (FSM.initial P) pP = q\<close> \<open>pt \<in> tps q\<close> 
                           \<open>p_io pP @ p_io pt \<in> L M'\<close> \<open>q' \<in> rd_targets (q, pt)\<close> \<open>(A, t1, t2) \<in> atcs (target q pt, q')\<close> 
                           \<open>target (initial M') pt' \<in> io_targets M' (p_io pP @ p_io pt) (FSM.initial M')\<close>]
            by assumption

          have "is_separator M (target q pt) q' A t1 t2"
            using  t3[OF \<open>(A, t1, t2) \<in> atcs (target q pt, q')\<close>] by blast

          have "is_submachine P M"
            using t2[OF \<open>(q, P) \<in> prs\<close>] unfolding is_preamble_def by blast
          then have "initial P = initial M" by auto
      
          have "path M (initial M) pP"
            using submachine_path[OF \<open>is_submachine P M\<close> \<open>path P (initial P) pP\<close>] 
            unfolding \<open>initial P = initial M\<close> 
            by assumption
          have "target (initial M) pP = q"
            using \<open>target (initial P) pP = q\<close> 
            unfolding \<open>initial P = initial M\<close> 
            by assumption
  
          have "q \<in> states M"
            using is_preamble_is_state[OF t2[OF \<open>(q, P) \<in> prs\<close>]] 
            by assumption
  
          have "q \<in> fst ` prs" 
            using \<open>(q, P) \<in> prs\<close> by force
  
          obtain pT' d' where "(pt @ pT', d') \<in> m_traversal_paths_with_witness M q repetition_sets m"
            using t6[OF \<open>q \<in> fst ` prs\<close>] \<open>pt \<in> tps q\<close> 
            by blast
  
          then have "path M q (pt @ pT')"
               and  "find (\<lambda>d. Suc (m - card (snd d)) \<le> length (filter (\<lambda>t. t_target t \<in> fst d) (pt @ pT'))) repetition_sets = Some d'"
               and  "\<And> p' p''. (pt @ pT') = p' @ p'' \<Longrightarrow> p'' \<noteq> [] \<Longrightarrow> find (\<lambda>d. Suc (m - card (snd d)) \<le> length (filter (\<lambda>t. t_target t \<in> fst d) p')) repetition_sets = None"
            using m_traversal_paths_with_witness_set[OF t5 t8 \<open>q \<in> states M\<close>, of m]
            by blast+
          then have "path M q pt"
            by auto
  
          have "target (initial M') pt' \<in> states M'"
            using \<open>target (initial M') pt' \<in> io_targets M' (p_io pP @ p_io pt) (FSM.initial M')\<close> io_targets_states
            using subset_iff 
            by fastforce 


          have "pass_io_set (FSM.from_FSM M' (target (FSM.initial M') pt')) (atc_to_io_set (FSM.from_FSM M (target q pt)) A)"
            using  pass_io_set_from_pass_separator[OF \<open>is_separator M (target q pt) q' A t1 t2\<close> 
                                                      \<open>pass_separator_ATC M' A (target (FSM.initial M') pt') t2\<close> 
                                                      \<open>observable M\<close> \<open>observable M'\<close> path_target_is_state[OF \<open>path M q pt\<close>] 
                                                      \<open>target (FSM.initial M') pt' \<in> FSM.states M'\<close> \<open>inputs M' = inputs M\<close>]
            by assumption
          moreover note \<open>ioAI @ [(x,y)] \<in> atc_to_io_set (FSM.from_FSM M (target q pt)) A\<close>
          moreover have "ioAI @ [(x, y')] \<in> L (FSM.from_FSM M' (target (FSM.initial M') pt'))" 
            using \<open>io @ [(x,y')] \<in> L M'\<close>   unfolding \<open>io = p_io pP @ p_io pt @ ioAI\<close>
            by (metis (no_types, lifting) \<open>target (FSM.initial M') pt' \<in> FSM.states M'\<close> 
                  \<open>target (FSM.initial M') pt' \<in> io_targets M' (p_io pP @ p_io pt) (FSM.initial M')\<close> 
                  append_assoc assms(3) from_FSM_language observable_io_targets_language)

          ultimately have "ioAI @ [(x,y')] \<in> atc_to_io_set (FSM.from_FSM M (target q pt)) A"
            unfolding pass_io_set_def by blast


          (* subsets of test_suite_to_io *)
          define tmp where tmp_def : "tmp = (\<Union> {(\<lambda>io_atc. p_io p @ p_io pt @ io_atc) ` atc_to_io_set (FSM.from_FSM M (target q pt)) A |p pt q A. \<exists>P q' t1 t2. (q, P) \<in> prs \<and> path P (FSM.initial P) p \<and> target (FSM.initial P) p = q \<and> pt \<in> tps q \<and> q' \<in> rd_targets (q, pt) \<and> (A, t1, t2) \<in> atcs (target q pt, q')})"
          define tmp2 where tmp2_def : "tmp2 = \<Union> {(@) (p_io p) ` set (prefixes (p_io pt)) |p pt. \<exists>q P. (q, P) \<in> prs \<and> path P (FSM.initial P) p \<and> target (FSM.initial P) p = q \<and> pt \<in> tps q}"
          have "\<exists>P q' t1 t2. (q, P) \<in> prs \<and> path P (FSM.initial P) pP \<and> target (FSM.initial P) pP = q \<and> pt \<in> tps q \<and> q' \<in> rd_targets (q, pt) \<and> (A, t1, t2) \<in> atcs (target q pt, q')"
            using \<open>(q, P) \<in> prs\<close> \<open>path P (FSM.initial P) pP\<close> \<open>target (FSM.initial P) pP = q\<close> \<open>pt \<in> tps q\<close> \<open>q' \<in> rd_targets (q, pt)\<close> \<open>(A, t1, t2) \<in> atcs (target q pt, q')\<close> by blast
          then have "(\<lambda>io_atc. p_io pP @ p_io pt @ io_atc) ` atc_to_io_set (FSM.from_FSM M (target q pt)) A \<subseteq> tmp"
            unfolding tmp_def by blast
          then have "(\<lambda>io_atc. p_io pP @ p_io pt @ io_atc) ` atc_to_io_set (FSM.from_FSM M (target q pt)) A \<subseteq> test_suite_to_io M (Test_Suite prs tps rd_targets atcs)"
            unfolding test_suite_to_io.simps tmp_def[symmetric] tmp2_def[symmetric] by blast
          moreover have "(p_io pP @ p_io pt @ (ioAI @ [(x, y')])) \<in> (\<lambda>io_atc. p_io pP @ p_io pt @ io_atc) ` atc_to_io_set (FSM.from_FSM M (target q pt)) A"
            using \<open>ioAI @ [(x, y')] \<in> atc_to_io_set (FSM.from_FSM M (target q pt)) A\<close> by auto
          ultimately have "(p_io pP @ p_io pt @ (ioAI @ [(x, y')])) \<in> test_suite_to_io M (Test_Suite prs tps rd_targets atcs)"
            by blast
          then have "io @ [(x, y')] \<in> test_suite_to_io M (Test_Suite prs tps rd_targets atcs)"
            unfolding \<open>io = p_io pP @ p_io pt @ ioAI\<close> by auto
          then show "False"
            using \<open>io @ [(x, y')] \<notin> test_suite_to_io M (Test_Suite prs tps rd_targets atcs)\<close> 
            by blast
        qed
      qed
    qed
  qed

  ultimately show ?thesis 
    unfolding \<open>T = Test_Suite prs tps rd_targets atcs\<close> 
    by blast
qed



lemma test_suite_to_io_finite :
  assumes "implies_completeness T M m"
  and     "is_finite_test_suite T"
shows "finite (test_suite_to_io M T)"
proof -
  obtain prs tps rd_targets atcs where "T = Test_Suite prs tps rd_targets atcs"
    by (meson test_suite.exhaust)
  then obtain repetition_sets where repetition_sets_def: "implies_completeness_for_repetition_sets (Test_Suite prs tps rd_targets atcs) M m repetition_sets"
    using assms(1) 
    unfolding implies_completeness_def 
    by blast
  then have "implies_completeness (Test_Suite prs tps rd_targets atcs) M m"
    unfolding implies_completeness_def 
    by blast
  then have test_suite_language_prop: "test_suite_to_io M (Test_Suite prs tps rd_targets atcs) \<subseteq> L M"
    using test_suite_to_io_language 
    by blast

  have f1: "(finite prs)" 
  and  f2: "\<And> q p . q \<in> fst ` prs \<Longrightarrow> finite (rd_targets (q,p))" 
  and  f3: "\<And> q q' . finite (atcs (q,q'))"
    using assms(2) 
    unfolding \<open>T = Test_Suite prs tps rd_targets atcs\<close> is_finite_test_suite.simps 
    by blast+

  have t1: "(initial M, initial_preamble M) \<in> prs" 
    using implies_completeness_for_repetition_sets_simps(1)[OF repetition_sets_def] 
    by assumption
  have t2: "\<And> q P. (q, P) \<in> prs \<Longrightarrow> is_preamble P M q"
    using implies_completeness_for_repetition_sets_simps(2)[OF repetition_sets_def] 
    by blast
  have t3: "\<And> q1 q2 A d1 d2. (A, d1, d2) \<in> atcs (q1, q2) \<Longrightarrow> (A, d2, d1) \<in> atcs (q2, q1) \<and> is_separator M q1 q2 A d1 d2"
    using implies_completeness_for_repetition_sets_simps(3)[OF repetition_sets_def] 
    by assumption
  
  have t5: "\<And>q. q \<in> FSM.states M \<Longrightarrow> (\<exists>d\<in>set repetition_sets. q \<in> fst d)"
    using implies_completeness_for_repetition_sets_simps(4)[OF repetition_sets_def] 
    by assumption

  have t6: "\<And> q. q \<in> fst ` prs \<Longrightarrow> tps q \<subseteq> {p1 . \<exists> p2 d . (p1@p2,d) \<in> m_traversal_paths_with_witness M q repetition_sets m} \<and> fst ` (m_traversal_paths_with_witness M q repetition_sets m) \<subseteq> tps q"
    using implies_completeness_for_repetition_sets_simps(7)[OF repetition_sets_def] 
    by assumption

  have t7: "\<And> d. d \<in> set repetition_sets \<Longrightarrow> fst d \<subseteq> FSM.states M"
  and  t8: "\<And> d. d \<in> set repetition_sets \<Longrightarrow> snd d \<subseteq> fst d"
  and  t8':  "\<And> d. d \<in> set repetition_sets \<Longrightarrow> snd d = fst d \<inter> fst ` prs"
  and  t9: "\<And> d q1 q2. d \<in> set repetition_sets \<Longrightarrow> q1 \<in> fst d \<Longrightarrow> q2 \<in> fst d \<Longrightarrow> q1 \<noteq> q2 \<Longrightarrow> atcs (q1, q2) \<noteq> {}"
    using implies_completeness_for_repetition_sets_simps(5,6)[OF repetition_sets_def] 
    by blast+


  have f4: "\<And> q . q \<in> fst ` prs \<Longrightarrow> finite (tps q)"
  proof -
    fix q assume "q \<in> fst ` prs"
    then have "tps q \<subseteq> {p1 . \<exists> p2 d . (p1@p2,d) \<in> m_traversal_paths_with_witness M q repetition_sets m}"
      using t6 by blast
    moreover have "{p1 . \<exists> p2 d . (p1@p2,d) \<in> m_traversal_paths_with_witness M q repetition_sets m} \<subseteq> (\<Union> p2 \<in> fst ` m_traversal_paths_with_witness M q repetition_sets m . set (prefixes p2))"
    proof 
      fix p1 assume "p1 \<in> {p1 . \<exists> p2 d . (p1@p2,d) \<in> m_traversal_paths_with_witness M q repetition_sets m}"
      then obtain p2 d where "(p1@p2,d) \<in> m_traversal_paths_with_witness M q repetition_sets m" by blast
      then have "p1@p2 \<in> fst ` m_traversal_paths_with_witness M q repetition_sets m" by force
      moreover have "p1 \<in> set (prefixes (p1@p2))" unfolding prefixes_set by blast
      ultimately show "p1 \<in> (\<Union> p2 \<in> fst ` m_traversal_paths_with_witness M q repetition_sets m . set (prefixes p2))" by blast
    qed
    ultimately have "tps q \<subseteq> (\<Union> p2 \<in> fst ` m_traversal_paths_with_witness M q repetition_sets m . set (prefixes p2))"
      by simp
    moreover have "finite (\<Union> p2 \<in> fst ` m_traversal_paths_with_witness M q repetition_sets m . set (prefixes p2))"
    proof -
      have "finite (fst ` m_traversal_paths_with_witness M q repetition_sets m)"
        using m_traversal_paths_with_witness_finite[of M q repetition_sets m] by auto
      moreover have "\<And> p2 . finite (set (prefixes p2))" by auto
      ultimately show ?thesis by blast
    qed
    ultimately show "finite (tps q)"
      using finite_subset by blast 
  qed
  then have f4' : "\<And> q P . (q,P) \<in> prs \<Longrightarrow> finite (tps q)"
    by force

  define T1 where T1_def : "T1 = (\<Union>(q, P)\<in>prs. L P)"
  define T2 where T2_def : "T2 = \<Union>{(@) (p_io p) ` set (prefixes (p_io pt)) |p pt. \<exists>q P. (q, P) \<in> prs \<and> path P (FSM.initial P) p \<and> target (FSM.initial P) p = q \<and> pt \<in> tps q}"
  define T3 where T3_def : "T3 = \<Union> {(\<lambda>io_atc. p_io p @ p_io pt @ io_atc) ` atc_to_io_set (FSM.from_FSM M (target q pt)) A |p pt q A.
        \<exists>P q' t1 t2.
           (q, P) \<in> prs \<and>
           path P (FSM.initial P) p \<and> target (FSM.initial P) p = q \<and> pt \<in> tps q \<and> q' \<in> rd_targets (q, pt) \<and> (A, t1, t2) \<in> atcs (target q pt, q')}"
  
  have "test_suite_to_io M T = T1 \<union> T2 \<union> T3"
    unfolding \<open>T = Test_Suite prs tps rd_targets atcs\<close> test_suite_to_io.simps T1_def T2_def T3_def by simp

  moreover have "finite T1" 
  proof -
    have "\<And> q P . (q, P)\<in>prs \<Longrightarrow> finite (L P)"
    proof -
      fix q P assume "(q, P)\<in>prs"
      have "acyclic P" 
        using t2[OF \<open>(q, P)\<in>prs\<close>] 
        unfolding is_preamble_def 
        by blast 
      then show "finite (L P)" 
        using acyclic_alt_def 
        by blast
    qed
    then show ?thesis using f1 unfolding T1_def
      by auto 
  qed

  moreover have "finite T2"
  proof -
    have *: "T2 = (\<Union> (p,pt) \<in> {(p,pt) | p pt. \<exists>q P. (q, P) \<in> prs \<and> path P (FSM.initial P) p \<and> target (FSM.initial P) p = q \<and> pt \<in> tps q} . ((@) (p_io p) ` set (prefixes (p_io pt))))"
      unfolding T2_def 
      by auto

    have "\<And> p pt . finite ((@) (p_io p) ` set (prefixes (p_io pt)))"
      by auto
    moreover have "finite {(p,pt) | p pt. \<exists>q P. (q, P) \<in> prs \<and> path P (FSM.initial P) p \<and> target (FSM.initial P) p = q \<and> pt \<in> tps q}"
    proof -
      have "{(p,pt) | p pt. \<exists>q P. (q, P) \<in> prs \<and> path P (FSM.initial P) p \<and> target (FSM.initial P) p = q \<and> pt \<in> tps q} \<subseteq> (\<Union> (q,P) \<in> prs . {p . path P (initial P) p} \<times> (tps q))"
        by auto
      moreover have "finite (\<Union> (q,P) \<in> prs . {p . path P (initial P) p} \<times> (tps q))"
      proof -
        note \<open>finite prs\<close>
        moreover have "\<And> q P . (q,P) \<in> prs \<Longrightarrow> finite ({p . path P (initial P) p} \<times> (tps q))"
        proof -
          fix q P assume "(q,P) \<in> prs"

          have "acyclic P" using t2[OF \<open>(q, P)\<in>prs\<close>]
            unfolding is_preamble_def 
            by blast
          then have "finite {p . path P (initial P) p}" 
            using acyclic_paths_finite[of P "initial P"] 
            unfolding acyclic.simps
            by (metis (no_types, lifting) Collect_cong) 
          then show "finite ({p . path P (initial P) p} \<times> (tps q))"
            using f4'[OF \<open>(q,P) \<in> prs\<close>] 
            by simp
        qed
        ultimately show ?thesis 
          by force
      qed
      ultimately show ?thesis
        by (meson rev_finite_subset) 
    qed
    ultimately show ?thesis 
      unfolding * by auto 
  qed


  moreover have "finite T3"
  proof -
    have scheme: "\<And> f P . (\<Union> {f a b c d | a b c d . P a b c d}) = (\<Union> (a,b,c,d) \<in> {(a,b,c,d) | a b c d . P a b c d} . f a b c d)" 
      by blast

    have *: "T3 = (\<Union> (p,pt,q,A) \<in> {(p, pt, q, A) | p pt q A . \<exists>P q' t1 t2. (q, P) \<in> prs \<and> path P (FSM.initial P) p \<and> target (FSM.initial P) p = q \<and> pt \<in> tps q \<and> q' \<in> rd_targets (q, pt) \<and> (A, t1, t2) \<in> atcs (target q pt, q')}
                       . (\<lambda>io_atc. p_io p @ p_io pt @ io_atc) ` atc_to_io_set (FSM.from_FSM M (target q pt)) A)"
      unfolding T3_def scheme by blast

    have "{(p, pt, q, A) | p pt q A . \<exists>P q' t1 t2. (q, P) \<in> prs \<and> path P (FSM.initial P) p \<and> target (FSM.initial P) p = q \<and> pt \<in> tps q \<and> q' \<in> rd_targets (q, pt) \<and> (A, t1, t2) \<in> atcs (target q pt, q')}
            \<subseteq> (\<Union> (q,P) \<in> prs . \<Union> pt \<in> tps q . \<Union> q' \<in> rd_targets (q, pt) . (\<Union> (A, t1, t2) \<in> atcs (target q pt, q') . {p . path P (initial P) p} \<times> {pt} \<times> {q} \<times> {A}))"
      by blast
    moreover have "finite (\<Union> (q,P) \<in> prs . \<Union> pt \<in> tps q . \<Union> q' \<in> rd_targets (q, pt) . (\<Union> (A, t1, t2) \<in> atcs (target q pt, q') . {p . path P (initial P) p} \<times> {pt} \<times> {q} \<times> {A}))"
    proof -
      note \<open>finite prs\<close>
      moreover have "\<And> q P . (q,P) \<in> prs \<Longrightarrow> finite (\<Union> pt \<in> tps q . \<Union> q' \<in> rd_targets (q, pt) . (\<Union> (A, t1, t2) \<in> atcs (target q pt, q') . {p . path P (initial P) p} \<times> {pt} \<times> {q} \<times> {A}))"
      proof -
        fix q P assume "(q,P) \<in> prs"
        then have "q \<in> fst ` prs" by force

        have "finite (tps q)" using f4'[OF \<open>(q,P) \<in> prs\<close>] by assumption
        moreover have "\<And> pt . pt \<in> tps q \<Longrightarrow> finite (\<Union> q' \<in> rd_targets (q, pt) . (\<Union> (A, t1, t2) \<in> atcs (target q pt, q') . {p . path P (initial P) p} \<times> {pt} \<times> {q} \<times> {A}))"
        proof -
          fix pt assume "pt \<in> tps q"
          
          have "finite (rd_targets (q,pt))" using f2[OF \<open>q \<in> fst ` prs\<close>] by blast
          moreover have "\<And> q' . q' \<in> rd_targets (q, pt) \<Longrightarrow> finite (\<Union> (A, t1, t2) \<in> atcs (target q pt, q') . {p . path P (initial P) p} \<times> {pt} \<times> {q} \<times> {A})"
          proof -
            fix q' assume "q' \<in> rd_targets (q, pt)"
            have "finite (atcs (target q pt, q'))" using f3 by blast
            moreover have "finite {p . path P (initial P) p}"
            proof -
              have "acyclic P" using t2[OF \<open>(q, P)\<in>prs\<close>] unfolding is_preamble_def by blast
              then show ?thesis using acyclic_paths_finite[of P "initial P"] unfolding acyclic.simps by (metis (no_types, lifting) Collect_cong) 
            qed
            ultimately show "finite (\<Union> (A, t1, t2) \<in> atcs (target q pt, q') . {p . path P (initial P) p} \<times> {pt} \<times> {q} \<times> {A})"
              by force
          qed
          ultimately show "finite (\<Union> q' \<in> rd_targets (q, pt) . (\<Union> (A, t1, t2) \<in> atcs (target q pt, q') . {p . path P (initial P) p} \<times> {pt} \<times> {q} \<times> {A}))"
            by force
        qed
        ultimately show "finite (\<Union> pt \<in> tps q . \<Union> q' \<in> rd_targets (q, pt) . (\<Union> (A, t1, t2) \<in> atcs (target q pt, q') . {p . path P (initial P) p} \<times> {pt} \<times> {q} \<times> {A}))"
          by force
      qed
      ultimately show ?thesis by force
    qed
    ultimately have "finite {(p, pt, q, A) | p pt q A . \<exists>P q' t1 t2. (q, P) \<in> prs \<and> path P (FSM.initial P) p \<and> target (FSM.initial P) p = q \<and> pt \<in> tps q \<and> q' \<in> rd_targets (q, pt) \<and> (A, t1, t2) \<in> atcs (target q pt, q')}"
      by (meson rev_finite_subset) 


    moreover have "\<And> p pt q A . (p,pt,q,A) \<in> {(p, pt, q, A) | p pt q A . \<exists>P q' t1 t2. (q, P) \<in> prs \<and> path P (FSM.initial P) p \<and> target (FSM.initial P) p = q \<and> pt \<in> tps q \<and> q' \<in> rd_targets (q, pt) \<and> (A, t1, t2) \<in> atcs (target q pt, q')}
                       \<Longrightarrow> finite ((\<lambda>io_atc. p_io p @ p_io pt @ io_atc) ` atc_to_io_set (FSM.from_FSM M (target q pt)) A)"
    proof -
      fix p pt q A assume "(p,pt,q,A) \<in> {(p, pt, q, A) | p pt q A . \<exists>P q' t1 t2. (q, P) \<in> prs \<and> path P (FSM.initial P) p \<and> target (FSM.initial P) p = q \<and> pt \<in> tps q \<and> q' \<in> rd_targets (q, pt) \<and> (A, t1, t2) \<in> atcs (target q pt, q')}"
      then obtain P q' t1 t2 where "(q, P) \<in> prs" and "path P (FSM.initial P) p" and "target (FSM.initial P) p = q" and "pt \<in> tps q" and "q' \<in> rd_targets (q, pt)" and "(A, t1, t2) \<in> atcs (target q pt, q')" by blast

      have "is_separator M (target q pt) q' A t1 t2"
        using t3[OF \<open>(A, t1, t2) \<in> atcs (target q pt, q')\<close>] by blast
      then have "acyclic A"
        using is_separator_simps(2) by simp
      then have "finite (L A)"
        unfolding acyclic_alt_def by assumption
      then have "finite (atc_to_io_set (FSM.from_FSM M (target q pt)) A)"
        unfolding atc_to_io_set.simps by blast
      then show "finite ((\<lambda>io_atc. p_io p @ p_io pt @ io_atc) ` atc_to_io_set (FSM.from_FSM M (target q pt)) A)"
        by blast
    qed

    ultimately show ?thesis unfolding * by force
  qed

  ultimately show ?thesis
    by simp 
qed



subsection \<open>Calculating the Sets of Sequences\<close>


abbreviation "L_acyclic M \<equiv> LS_acyclic M (initial M)"

(* collect the prefix-closed IO-sequence representation of a test suite for some reference FSM *)
fun test_suite_to_io' :: "('a,'b,'c) fsm \<Rightarrow> ('a,'b,'c,'d) test_suite \<Rightarrow> ('b \<times> 'c) list set" where
  "test_suite_to_io' M (Test_Suite prs tps rd_targets atcs) 
      = (\<Union> (q,P) \<in> prs . 
          L_acyclic P 
          \<union> (\<Union> ioP \<in> remove_proper_prefixes (L_acyclic P) . 
              \<Union> pt \<in> tps q . 
                ((\<lambda> io' . ioP @ io') ` (set (prefixes (p_io pt)))) 
                \<union> (\<Union> q' \<in> rd_targets (q,pt) . 
                    \<Union> (A,t1,t2) \<in> atcs (target q pt,q') . 
                      (\<lambda> io_atc . ioP @ p_io pt @ io_atc) ` (acyclic_language_intersection (from_FSM M (target q pt)) A))))"


lemma test_suite_to_io_code :
  assumes "implies_completeness T M m"
  and     "is_finite_test_suite T"  
  and     "observable M"
shows "test_suite_to_io M T = test_suite_to_io' M T"
proof -

  obtain prs tps rd_targets atcs where "T = Test_Suite prs tps rd_targets atcs"
    by (meson test_suite.exhaust)

  then obtain repetition_sets where repetition_sets_def: "implies_completeness_for_repetition_sets (Test_Suite prs tps rd_targets atcs) M m repetition_sets"
    using assms(1) 
    unfolding implies_completeness_def 
    by blast

  have t2: "\<And> q P. (q, P) \<in> prs \<Longrightarrow> is_preamble P M q"
    using implies_completeness_for_repetition_sets_simps(2)[OF repetition_sets_def] 
    by blast
  have t3: "\<And> q1 q2 A d1 d2. (A, d1, d2) \<in> atcs (q1, q2) \<Longrightarrow> (A, d2, d1) \<in> atcs (q2, q1) \<and> is_separator M q1 q2 A d1 d2"
    using implies_completeness_for_repetition_sets_simps(3)[OF repetition_sets_def] 
    by assumption


  have test_suite_to_io'_alt_def: "test_suite_to_io' M T  
    = (\<Union> (q,P) \<in> prs . L_acyclic P)
      \<union> (\<Union> (q,P) \<in> prs . \<Union> ioP \<in> remove_proper_prefixes (L_acyclic P) . \<Union> pt \<in> tps q . ((\<lambda> io' . ioP @ io') ` (set (prefixes (p_io pt))))) 
      \<union> (\<Union> (q,P) \<in> prs . \<Union> ioP \<in> remove_proper_prefixes (L_acyclic P) . \<Union> pt \<in> tps q . \<Union> q' \<in> rd_targets (q,pt) . \<Union> (A,t1,t2) \<in> atcs (target q pt,q') . (\<lambda> io_atc . ioP @ p_io pt @ io_atc) ` (acyclic_language_intersection (from_FSM M (target q pt)) A))"
    unfolding test_suite_to_io'.simps \<open>T = Test_Suite prs tps rd_targets atcs\<close> 
    by fast

  have test_suite_to_io_alt_def: "test_suite_to_io M T =
    (\<Union> (q,P) \<in> prs . L P)
    \<union> (\<Union>{(\<lambda> io' . p_io p @ io') ` (set (prefixes (p_io pt))) | p pt . \<exists> q P . (q,P) \<in> prs \<and> path P (initial P) p \<and> target (initial P) p = q \<and> pt \<in> tps q})
    \<union> (\<Union>{(\<lambda> io_atc . p_io p @ p_io pt @ io_atc) ` (atc_to_io_set (from_FSM M (target q pt)) A) | p pt q A . \<exists> P q' t1 t2 . (q,P) \<in> prs \<and> path P (initial P) p \<and> target (initial P) p = q \<and> pt \<in> tps q \<and> q' \<in> rd_targets (q,pt) \<and> (A,t1,t2) \<in> atcs (target q pt,q') })"
    unfolding \<open>T = Test_Suite prs tps rd_targets atcs\<close> test_suite_to_io.simps
    by force


  have preamble_language_prop: "\<And> q P . (q,P) \<in> prs \<Longrightarrow> L_acyclic P = L P"
  proof -
    fix q P assume "(q,P) \<in> prs"
    have "acyclic P" using t2[OF \<open>(q, P)\<in>prs\<close>] unfolding is_preamble_def by blast 
    then show "L_acyclic P = L P" using LS_from_LS_acyclic by blast
  qed

  have preamble_path_prop: "\<And> q P ioP . (q,P) \<in> prs \<Longrightarrow> ioP \<in> remove_proper_prefixes (L_acyclic P) \<longleftrightarrow> (\<exists> p . path P (initial P) p \<and> target (initial P) p = q \<and> p_io p = ioP)"
  proof -
    fix q P ioP assume "(q,P) \<in> prs"
    have "is_preamble P M q" using t2[OF \<open>(q, P)\<in>prs\<close>] by assumption

    have "ioP \<in> remove_proper_prefixes (L_acyclic P) \<Longrightarrow> (\<exists> p . path P (initial P) p \<and> target (initial P) p = q \<and> p_io p = ioP)"
    proof -
      assume "ioP \<in> remove_proper_prefixes (L_acyclic P)"
      then have "ioP \<in> L P"  and "\<nexists>x'. x' \<noteq> [] \<and> ioP @ x' \<in> L P"
        unfolding preamble_language_prop[OF \<open>(q,P) \<in> prs\<close>] remove_proper_prefixes_def by blast+
      show "(\<exists> p . path P (initial P) p \<and> target (initial P) p = q \<and> p_io p = ioP)"
        using preamble_maximal_io_paths_rev[OF \<open>is_preamble P M q\<close> \<open>observable M\<close> \<open>ioP \<in> L P\<close> \<open>\<nexists>x'. x' \<noteq> [] \<and> ioP @ x' \<in> L P\<close>] by blast
    qed
    moreover have "(\<exists> p . path P (initial P) p \<and> target (initial P) p = q \<and> p_io p = ioP) \<Longrightarrow> ioP \<in> remove_proper_prefixes (L_acyclic P)"
    proof -
      assume "(\<exists> p . path P (initial P) p \<and> target (initial P) p = q \<and> p_io p = ioP)"
      then obtain p where "path P (initial P) p" and "target (initial P) p = q" and "p_io p = ioP"
        by blast
      then have "\<nexists>io'. io' \<noteq> [] \<and> p_io p @ io' \<in> L P"
        using preamble_maximal_io_paths[OF \<open>is_preamble P M q\<close> \<open>observable M\<close>] by blast
      then show "ioP \<in> remove_proper_prefixes (L_acyclic P)"
        using language_state_containment[OF \<open>path P (initial P) p\<close> \<open>p_io p = ioP\<close>] unfolding preamble_language_prop[OF \<open>(q,P) \<in> prs\<close>] remove_proper_prefixes_def \<open>p_io p = ioP\<close> by blast
    qed
    ultimately show "ioP \<in> remove_proper_prefixes (L_acyclic P) \<longleftrightarrow> (\<exists> p . path P (initial P) p \<and> target (initial P) p = q \<and> p_io p = ioP)"
      by blast
  qed
    

  have eq1: "(\<Union> (q,P) \<in> prs . L_acyclic P) = (\<Union> (q,P) \<in> prs . L P)"
    using preamble_language_prop by blast

  have eq2: "(\<Union> (q,P) \<in> prs . \<Union> ioP \<in> remove_proper_prefixes (L_acyclic P) . \<Union> pt \<in> tps q . ((\<lambda> io' . ioP @ io') ` (set (prefixes (p_io pt))))) = (\<Union>{(\<lambda> io' . p_io p @ io') ` (set (prefixes (p_io pt))) | p pt . \<exists> q P . (q,P) \<in> prs \<and> path P (initial P) p \<and> target (initial P) p = q \<and> pt \<in> tps q})"
  proof 
    show "(\<Union>(q, P)\<in>prs. \<Union>ioP\<in>remove_proper_prefixes (L_acyclic P). \<Union>pt\<in>tps q. (@) ioP ` set (prefixes (p_io pt))) \<subseteq> \<Union> {(@) (p_io p) ` set (prefixes (p_io pt)) |p pt. \<exists>q P. (q, P) \<in> prs \<and> path P (FSM.initial P) p \<and> target (FSM.initial P) p = q \<and> pt \<in> tps q}"
    proof 
      fix io assume "io \<in> (\<Union> (q,P) \<in> prs . (\<Union> ioP \<in> remove_proper_prefixes (L_acyclic P) . \<Union> pt \<in> tps q . ((\<lambda> io' . ioP @ io') ` (set (prefixes (p_io pt))))))"
      then obtain q P where "(q,P) \<in> prs"
                      and   "io \<in> (\<Union> ioP \<in> remove_proper_prefixes (L_acyclic P) . \<Union> pt \<in> tps q . ((\<lambda> io' . ioP @ io') ` (set (prefixes (p_io pt)))))"
        by blast
      then obtain ioP where "ioP \<in> remove_proper_prefixes (L_acyclic P)"
                      and   "io \<in> (\<Union> pt \<in> tps q . ((\<lambda> io' . ioP @ io') ` (set (prefixes (p_io pt)))))"
        by blast

      obtain p where "path P (initial P) p" and "target (initial P) p = q" and "ioP = p_io p"
        using preamble_path_prop[OF \<open>(q,P) \<in> prs\<close>, of ioP] \<open>ioP \<in> remove_proper_prefixes (L_acyclic P)\<close> by auto 

      obtain pt where "pt \<in> tps q" and "io \<in> ((\<lambda> io' . p_io p @ io') ` (set (prefixes (p_io pt))))"
        using \<open>io \<in> (\<Union> pt \<in> tps q . ((\<lambda> io' . ioP @ io') ` (set (prefixes (p_io pt)))))\<close> unfolding \<open>ioP = p_io p\<close> by blast
      
      show "io \<in> (\<Union>{(\<lambda> io' . p_io p @ io') ` (set (prefixes (p_io pt))) | p pt . \<exists> q P . (q,P) \<in> prs \<and> path P (initial P) p \<and> target (initial P) p = q \<and> pt \<in> tps q})"
        using \<open>io \<in> ((\<lambda> io' . p_io p @ io') ` (set (prefixes (p_io pt))))\<close> \<open>(q,P) \<in> prs\<close> \<open>path P (initial P) p\<close> \<open>target (initial P) p = q\<close> \<open>pt \<in> tps q\<close> by blast
    qed

    show "\<Union> {(@) (p_io p) ` set (prefixes (p_io pt)) |p pt. \<exists>q P. (q, P) \<in> prs \<and> path P (FSM.initial P) p \<and> target (FSM.initial P) p = q \<and> pt \<in> tps q} \<subseteq> (\<Union>(q, P)\<in>prs. \<Union>ioP\<in>remove_proper_prefixes (L_acyclic P). \<Union>pt\<in>tps q. (@) ioP ` set (prefixes (p_io pt)))"
    proof 
      fix io assume "io \<in> (\<Union>{(\<lambda> io' . p_io p @ io') ` (set (prefixes (p_io pt))) | p pt . \<exists> q P . (q,P) \<in> prs \<and> path P (initial P) p \<and> target (initial P) p = q \<and> pt \<in> tps q})"
      then obtain p pt q P where "io \<in> (\<lambda> io' . p_io p @ io') ` (set (prefixes (p_io pt)))"
                           and   "(q,P) \<in> prs" and "path P (initial P) p" and "target (initial P) p = q" and "pt \<in> tps q" 
        by blast

      then obtain ioP where "ioP \<in> remove_proper_prefixes (L_acyclic P)"
                      and   "p_io p = ioP"
        using preamble_path_prop[OF \<open>(q,P) \<in> prs\<close>, of "p_io p"] by blast
      
      
      show "io \<in> (\<Union> (q,P) \<in> prs . (\<Union> ioP \<in> remove_proper_prefixes (L_acyclic P) . \<Union> pt \<in> tps q . ((\<lambda> io' . ioP @ io') ` (set (prefixes (p_io pt))))))"
        using \<open>(q,P) \<in> prs\<close> \<open>ioP \<in> remove_proper_prefixes (L_acyclic P)\<close> \<open>pt \<in> tps q\<close> \<open>io \<in> (\<lambda> io' . p_io p @ io') ` (set (prefixes (p_io pt)))\<close>  unfolding \<open>p_io p = ioP\<close> by blast
    qed
  qed

  have eq3: "(\<Union> (q,P) \<in> prs . \<Union> ioP \<in> remove_proper_prefixes (L_acyclic P) . \<Union> pt \<in> tps q . \<Union> q' \<in> rd_targets (q,pt) . \<Union> (A,t1,t2) \<in> atcs (target q pt,q') . (\<lambda> io_atc . ioP @ p_io pt @ io_atc) ` (acyclic_language_intersection (from_FSM M (target q pt)) A)) = (\<Union>{(\<lambda> io_atc . p_io p @ p_io pt @ io_atc) ` (atc_to_io_set (from_FSM M (target q pt)) A) | p pt q A . \<exists> P q' t1 t2 . (q,P) \<in> prs \<and> path P (initial P) p \<and> target (initial P) p = q \<and> pt \<in> tps q \<and> q' \<in> rd_targets (q,pt) \<and> (A,t1,t2) \<in> atcs (target q pt,q') })"
  proof
    show "(\<Union> (q,P) \<in> prs . \<Union> ioP \<in> remove_proper_prefixes (L_acyclic P) . \<Union> pt \<in> tps q . \<Union> q' \<in> rd_targets (q,pt) . \<Union> (A,t1,t2) \<in> atcs (target q pt,q') . (\<lambda> io_atc . ioP @ p_io pt @ io_atc) ` (acyclic_language_intersection (from_FSM M (target q pt)) A)) \<subseteq> (\<Union>{(\<lambda> io_atc . p_io p @ p_io pt @ io_atc) ` (atc_to_io_set (from_FSM M (target q pt)) A) | p pt q A . \<exists> P q' t1 t2 . (q,P) \<in> prs \<and> path P (initial P) p \<and> target (initial P) p = q \<and> pt \<in> tps q \<and> q' \<in> rd_targets (q,pt) \<and> (A,t1,t2) \<in> atcs (target q pt,q') })"    
    proof 
      fix io assume "io \<in> (\<Union> (q,P) \<in> prs . \<Union> ioP \<in> remove_proper_prefixes (L_acyclic P) . \<Union> pt \<in> tps q . \<Union> q' \<in> rd_targets (q,pt) . \<Union> (A,t1,t2) \<in> atcs (target q pt,q') . (\<lambda> io_atc . ioP @ p_io pt @ io_atc) ` (acyclic_language_intersection (from_FSM M (target q pt)) A))"
      then obtain q P ioP pt q' A t1 t2 where "(q,P) \<in> prs" 
                                        and   "ioP \<in> remove_proper_prefixes (L_acyclic P)"
                                        and   "pt \<in> tps q"
                                        and   "q' \<in> rd_targets (q,pt)"
                                        and   "(A,t1,t2) \<in> atcs (target q pt,q')"
                                        and   "io \<in> (\<lambda> io_atc . ioP @ p_io pt @ io_atc) ` (acyclic_language_intersection (from_FSM M (target q pt)) A)"
        by blast

      obtain p where "path P (initial P) p" and "target (initial P) p = q" and "ioP = p_io p"
        using preamble_path_prop[OF \<open>(q,P) \<in> prs\<close>, of ioP] \<open>ioP \<in> remove_proper_prefixes (L_acyclic P)\<close> by auto 

      have "acyclic A"
        using t3[OF \<open>(A,t1,t2) \<in> atcs (target q pt,q')\<close>] is_separator_simps(2) by metis
      have "(acyclic_language_intersection (from_FSM M (target q pt)) A) = (atc_to_io_set (from_FSM M (target q pt)) A)"
        unfolding acyclic_language_intersection_completeness[OF \<open>acyclic A\<close>] atc_to_io_set.simps by simp
      have "io \<in> (\<lambda> io_atc . p_io p @ p_io pt @ io_atc) ` (atc_to_io_set (from_FSM M (target q pt)) A)"
        using \<open>io \<in> (\<lambda> io_atc . ioP @ p_io pt @ io_atc) ` (acyclic_language_intersection (from_FSM M (target q pt)) A)\<close> unfolding \<open>(acyclic_language_intersection (from_FSM M (target q pt)) A) = (atc_to_io_set (from_FSM M (target q pt)) A)\<close> \<open>ioP = p_io p\<close> by simp

      then show "io \<in> (\<Union>{(\<lambda> io_atc . p_io p @ p_io pt @ io_atc) ` (atc_to_io_set (from_FSM M (target q pt)) A) | p pt q A . \<exists> P q' t1 t2 . (q,P) \<in> prs \<and> path P (initial P) p \<and> target (initial P) p = q \<and> pt \<in> tps q \<and> q' \<in> rd_targets (q,pt) \<and> (A,t1,t2) \<in> atcs (target q pt,q') })"
        using \<open>(q,P) \<in> prs\<close> \<open>path P (initial P) p\<close> \<open>target (initial P) p = q\<close> \<open>pt \<in> tps q\<close> \<open>q' \<in> rd_targets (q,pt)\<close> \<open>(A,t1,t2) \<in> atcs (target q pt,q')\<close> by blast
    qed

    show "(\<Union>{(\<lambda> io_atc . p_io p @ p_io pt @ io_atc) ` (atc_to_io_set (from_FSM M (target q pt)) A) | p pt q A . \<exists> P q' t1 t2 . (q,P) \<in> prs \<and> path P (initial P) p \<and> target (initial P) p = q \<and> pt \<in> tps q \<and> q' \<in> rd_targets (q,pt) \<and> (A,t1,t2) \<in> atcs (target q pt,q') }) \<subseteq> (\<Union> (q,P) \<in> prs . \<Union> ioP \<in> remove_proper_prefixes (L_acyclic P) . \<Union> pt \<in> tps q . \<Union> q' \<in> rd_targets (q,pt) . \<Union> (A,t1,t2) \<in> atcs (target q pt,q') . (\<lambda> io_atc . ioP @ p_io pt @ io_atc) ` (acyclic_language_intersection (from_FSM M (target q pt)) A))"
    proof 
      fix io assume "io \<in> (\<Union>{(\<lambda> io_atc . p_io p @ p_io pt @ io_atc) ` (atc_to_io_set (from_FSM M (target q pt)) A) | p pt q A . \<exists> P q' t1 t2 . (q,P) \<in> prs \<and> path P (initial P) p \<and> target (initial P) p = q \<and> pt \<in> tps q \<and> q' \<in> rd_targets (q,pt) \<and> (A,t1,t2) \<in> atcs (target q pt,q') })"
      then obtain p pt q A P q' t1 t2 where "io \<in> (\<lambda> io_atc . p_io p @ p_io pt @ io_atc) ` (atc_to_io_set (from_FSM M (target q pt)) A)"
                                      and   "(q,P) \<in> prs" 
                                      and   "path P (initial P) p" 
                                      and   "target (initial P) p = q" 
                                      and   "pt \<in> tps q" 
                                      and   "q' \<in> rd_targets (q,pt)" 
                                      and   "(A,t1,t2) \<in> atcs (target q pt,q')"
        by blast

      then obtain ioP where "ioP \<in> remove_proper_prefixes (L_acyclic P)"
                      and   "p_io p = ioP"
        using preamble_path_prop[OF \<open>(q,P) \<in> prs\<close>, of "p_io p"] by blast


      have "acyclic A"
        using t3[OF \<open>(A,t1,t2) \<in> atcs (target q pt,q')\<close>] is_separator_simps(2) by metis
      have *: "(atc_to_io_set (from_FSM M (target q pt)) A) = (acyclic_language_intersection (from_FSM M (target q pt)) A)"
        unfolding acyclic_language_intersection_completeness[OF \<open>acyclic A\<close>] atc_to_io_set.simps by simp
      have "io \<in> (\<lambda> io_atc . ioP @ p_io pt @ io_atc) ` (acyclic_language_intersection (from_FSM M (target q pt)) A)"
        using \<open>io \<in> (\<lambda> io_atc . p_io p @ p_io pt @ io_atc) ` (atc_to_io_set (from_FSM M (target q pt)) A)\<close> unfolding * \<open>p_io p = ioP\<close> by simp

      then show "io \<in> (\<Union> (q,P) \<in> prs . \<Union> ioP \<in> remove_proper_prefixes (L_acyclic P) . \<Union> pt \<in> tps q . \<Union> q' \<in> rd_targets (q,pt) . \<Union> (A,t1,t2) \<in> atcs (target q pt,q') . (\<lambda> io_atc . ioP @ p_io pt @ io_atc) ` (acyclic_language_intersection (from_FSM M (target q pt)) A))"
        using \<open>(q,P) \<in> prs\<close> \<open>ioP \<in> remove_proper_prefixes (L_acyclic P)\<close> \<open>pt \<in> tps q\<close> \<open>q' \<in> rd_targets (q,pt)\<close> \<open>(A,t1,t2) \<in> atcs (target q pt,q')\<close> by force
    qed
  qed

  show ?thesis
    unfolding test_suite_to_io'_alt_def test_suite_to_io_alt_def eq1 eq2 eq3 by simp
qed
  








subsection \<open>Using Maximal Sequences Only\<close>



fun test_suite_to_io_maximal :: "('a::linorder,'b::linorder,'c) fsm \<Rightarrow> ('a,'b,'c,'d::linorder) test_suite \<Rightarrow> ('b \<times> 'c) list set" where
  "test_suite_to_io_maximal M (Test_Suite prs tps rd_targets atcs) = 
      remove_proper_prefixes (\<Union> (q,P) \<in> prs . L_acyclic P \<union> (\<Union> ioP \<in> remove_proper_prefixes (L_acyclic P) . \<Union> pt \<in> tps q . Set.insert (ioP @ p_io pt) (\<Union> q' \<in> rd_targets (q,pt) . \<Union> (A,t1,t2) \<in> atcs (target q pt,q') . (\<lambda> io_atc . ioP @ p_io pt @ io_atc) ` (remove_proper_prefixes (acyclic_language_intersection (from_FSM M (target q pt)) A)))))"


lemma test_suite_to_io_maximal_code : 
  assumes "implies_completeness T M m"
  and     "is_finite_test_suite T"  
  and     "observable M"
shows  "{io' \<in> (test_suite_to_io M T) . \<not> (\<exists> io'' . io'' \<noteq> [] \<and> io'@io'' \<in> (test_suite_to_io M T))} = test_suite_to_io_maximal M T"
proof -

  obtain prs tps rd_targets atcs where "T = Test_Suite prs tps rd_targets atcs"
    by (meson test_suite.exhaust)

  have t_def: "test_suite_to_io M T = test_suite_to_io' M T"
    using test_suite_to_io_code[OF assms] by assumption

  have t1_def : "test_suite_to_io' M T = (\<Union> (q,P) \<in> prs . L_acyclic P \<union> (\<Union> ioP \<in> remove_proper_prefixes (L_acyclic P) . \<Union> pt \<in> tps q . ((\<lambda> io' . ioP @ io') ` (set (prefixes (p_io pt)))) \<union> (\<Union> q' \<in> rd_targets (q,pt) . \<Union> (A,t1,t2) \<in> atcs (target q pt,q') . (\<lambda> io_atc . ioP @ p_io pt @ io_atc) ` (acyclic_language_intersection (from_FSM M (target q pt)) A))))"
    unfolding \<open>T = Test_Suite prs tps rd_targets atcs\<close> by simp

  define tmax where tmax_def: "tmax = (\<Union> (q,P) \<in> prs . L_acyclic P \<union> (\<Union> ioP \<in> remove_proper_prefixes (L_acyclic P) . \<Union> pt \<in> tps q . Set.insert (ioP @ p_io pt) (\<Union> q' \<in> rd_targets (q,pt) . \<Union> (A,t1,t2) \<in> atcs (target q pt,q') . (\<lambda> io_atc . ioP @ p_io pt @ io_atc) ` (remove_proper_prefixes (acyclic_language_intersection (from_FSM M (target q pt)) A)))))"
  have t2_def : "test_suite_to_io_maximal M T = remove_proper_prefixes tmax"
    unfolding \<open>T = Test_Suite prs tps rd_targets atcs\<close> tmax_def by simp

  have tmax_sub: "tmax \<subseteq> (test_suite_to_io M T)"
    unfolding tmax_def t_def t1_def
  proof 
    fix io assume "io \<in> (\<Union> (q,P) \<in> prs . L_acyclic P \<union> (\<Union> ioP \<in> remove_proper_prefixes (L_acyclic P) . \<Union> pt \<in> tps q . Set.insert (ioP @ p_io pt) (\<Union> q' \<in> rd_targets (q,pt) . \<Union> (A,t1,t2) \<in> atcs (target q pt,q') . (\<lambda> io_atc . ioP @ p_io pt @ io_atc) ` (remove_proper_prefixes (acyclic_language_intersection (from_FSM M (target q pt)) A)))))"
    then obtain q P where "(q,P) \<in> prs"
                    and   "io \<in> L_acyclic P \<union> (\<Union> ioP \<in> remove_proper_prefixes (L_acyclic P) . \<Union> pt \<in> tps q . Set.insert (ioP @ p_io pt) (\<Union> q' \<in> rd_targets (q,pt) . \<Union> (A,t1,t2) \<in> atcs (target q pt,q') . (\<lambda> io_atc . ioP @ p_io pt @ io_atc) ` (remove_proper_prefixes (acyclic_language_intersection (from_FSM M (target q pt)) A))))"
      by force
    then consider (a) "io \<in> L_acyclic P" |
                  (b) "io \<in> (\<Union> ioP \<in> remove_proper_prefixes (L_acyclic P) . \<Union> pt \<in> tps q . Set.insert (ioP @ p_io pt) (\<Union> q' \<in> rd_targets (q,pt) . \<Union> (A,t1,t2) \<in> atcs (target q pt,q') . (\<lambda> io_atc . ioP @ p_io pt @ io_atc) ` (remove_proper_prefixes (acyclic_language_intersection (from_FSM M (target q pt)) A))))"
      by blast
    then show "io \<in> (\<Union> (q,P) \<in> prs . L_acyclic P \<union> (\<Union> ioP \<in> remove_proper_prefixes (L_acyclic P) . \<Union> pt \<in> tps q . ((\<lambda> io' . ioP @ io') ` (set (prefixes (p_io pt)))) \<union> (\<Union> q' \<in> rd_targets (q,pt) . \<Union> (A,t1,t2) \<in> atcs (target q pt,q') . (\<lambda> io_atc . ioP @ p_io pt @ io_atc) ` (acyclic_language_intersection (from_FSM M (target q pt)) A))))"
    proof cases
      case a
      then show ?thesis using \<open>(q,P) \<in> prs\<close> by blast
    next
      case b
      then obtain ioP pt where "ioP \<in> remove_proper_prefixes (L_acyclic P)" 
                         and   "pt \<in> tps q"
                         and   "io \<in> Set.insert (ioP @ p_io pt) (\<Union> q' \<in> rd_targets (q,pt) . \<Union> (A,t1,t2) \<in> atcs (target q pt,q') . (\<lambda> io_atc . ioP @ p_io pt @ io_atc) ` (remove_proper_prefixes (acyclic_language_intersection (from_FSM M (target q pt)) A)))"
        by blast
      then consider (b1) "io = (ioP @ p_io pt)" |
                    (b2) "io \<in> (\<Union> q' \<in> rd_targets (q,pt) . \<Union> (A,t1,t2) \<in> atcs (target q pt,q') . (\<lambda> io_atc . ioP @ p_io pt @ io_atc) ` (remove_proper_prefixes (acyclic_language_intersection (from_FSM M (target q pt)) A)))"
        by blast
      then show ?thesis proof cases
        case b1
        then have "io \<in> ((\<lambda> io' . ioP @ io') ` (set (prefixes (p_io pt))))" unfolding prefixes_set by blast
        then show ?thesis using \<open>(q,P) \<in> prs\<close> \<open>ioP \<in> remove_proper_prefixes (L_acyclic P)\<close> \<open>pt \<in> tps q\<close> by blast
      next
        case b2
        then obtain q' A t1 t2 where "q' \<in> rd_targets (q,pt)"
                               and   "(A,t1,t2) \<in> atcs (target q pt,q')"
                               and   "io \<in> (\<lambda> io_atc . ioP @ p_io pt @ io_atc) ` (remove_proper_prefixes (acyclic_language_intersection (from_FSM M (target q pt)) A))"
          by blast
        then have "io \<in> (\<lambda> io_atc . ioP @ p_io pt @ io_atc) ` (acyclic_language_intersection (from_FSM M (target q pt)) A)"
          unfolding remove_proper_prefixes_def by blast
        then show ?thesis using \<open>(q,P) \<in> prs\<close> \<open>ioP \<in> remove_proper_prefixes (L_acyclic P)\<close> \<open>pt \<in> tps q\<close> \<open>q' \<in> rd_targets (q,pt)\<close> \<open>(A,t1,t2) \<in> atcs (target q pt,q')\<close> by force
      qed 
    qed
  qed


  have tmax_max: "\<And> io . io \<in> test_suite_to_io M T \<Longrightarrow> io \<notin> tmax \<Longrightarrow> \<exists> io'' . io'' \<noteq> [] \<and> io@io'' \<in> (test_suite_to_io M T)"
  proof -
    fix io assume "io \<in> test_suite_to_io M T" and "io \<notin> tmax"

    then have "io \<in> (\<Union> (q,P) \<in> prs . L_acyclic P \<union> (\<Union> ioP \<in> remove_proper_prefixes (L_acyclic P) . \<Union> pt \<in> tps q . ((\<lambda> io' . ioP @ io') ` (set (prefixes (p_io pt)))) \<union> (\<Union> q' \<in> rd_targets (q,pt) . \<Union> (A,t1,t2) \<in> atcs (target q pt,q') . (\<lambda> io_atc . ioP @ p_io pt @ io_atc) ` (acyclic_language_intersection (from_FSM M (target q pt)) A))))"
      unfolding t_def t1_def by blast
    then obtain q P where "(q,P) \<in> prs"
                    and   "io \<in> (L_acyclic P \<union> (\<Union> ioP \<in> remove_proper_prefixes (L_acyclic P) . \<Union> pt \<in> tps q . ((\<lambda> io' . ioP @ io') ` (set (prefixes (p_io pt)))) \<union> (\<Union> q' \<in> rd_targets (q,pt) . \<Union> (A,t1,t2) \<in> atcs (target q pt,q') . (\<lambda> io_atc . ioP @ p_io pt @ io_atc) ` (acyclic_language_intersection (from_FSM M (target q pt)) A))))"
      by force
    then consider (a) "io \<in> L_acyclic P" |
                  (b) "io \<in> (\<Union> ioP \<in> remove_proper_prefixes (L_acyclic P) . \<Union> pt \<in> tps q . ((\<lambda> io' . ioP @ io') ` (set (prefixes (p_io pt)))) \<union> (\<Union> q' \<in> rd_targets (q,pt) . \<Union> (A,t1,t2) \<in> atcs (target q pt,q') . (\<lambda> io_atc . ioP @ p_io pt @ io_atc) ` (acyclic_language_intersection (from_FSM M (target q pt)) A)))"
      by blast
    then show "\<exists> io'' . io'' \<noteq> [] \<and> io@io'' \<in> (test_suite_to_io M T)" proof cases
      case a
      then have "io \<in> tmax"
        using \<open>(q,P) \<in> prs\<close> unfolding tmax_def by blast
      then show ?thesis 
        using \<open>io \<notin> tmax\<close> by simp
    next
      case b
      then obtain ioP pt where "ioP \<in> remove_proper_prefixes (L_acyclic P)"
                         and   "pt \<in> tps q"
                         and   "io \<in> ((\<lambda> io' . ioP @ io') ` (set (prefixes (p_io pt)))) \<union> (\<Union> q' \<in> rd_targets (q,pt) . \<Union> (A,t1,t2) \<in> atcs (target q pt,q') . (\<lambda> io_atc . ioP @ p_io pt @ io_atc) ` (acyclic_language_intersection (from_FSM M (target q pt)) A))"
        by blast
      then consider (b1) "io \<in> (\<lambda> io' . ioP @ io') ` (set (prefixes (p_io pt)))" |
                    (b2) "io \<in> (\<Union> q' \<in> rd_targets (q,pt) . \<Union> (A,t1,t2) \<in> atcs (target q pt,q') . (\<lambda> io_atc . ioP @ p_io pt @ io_atc) ` (acyclic_language_intersection (from_FSM M (target q pt)) A))"
        by blast
      then show ?thesis proof cases
        case b1
        then obtain pt1 pt2 where "io = ioP @ pt1" and "p_io pt = pt1@pt2"
          by (metis (no_types, lifting) b1 image_iff prefixes_set_ob) 

        have "ioP @ (p_io pt) \<in> tmax"
          using \<open>io \<notin> tmax\<close> \<open>(q,P) \<in> prs\<close> \<open>ioP \<in> remove_proper_prefixes (L_acyclic P)\<close> \<open>pt \<in> tps q\<close> unfolding tmax_def by force
        then have "io \<noteq> ioP @ (p_io pt)"
          using \<open>io \<notin> tmax\<close> by blast
        then have "pt2 \<noteq> []" 
          using \<open>io = ioP @ pt1\<close> unfolding \<open>p_io pt = pt1@pt2\<close> by auto

        have "ioP @ (p_io pt) \<in> test_suite_to_io M T"
          using \<open>ioP @ (p_io pt) \<in> tmax\<close> tmax_sub by blast
        then show ?thesis 
          unfolding \<open>io = ioP @ pt1\<close> append.assoc \<open>p_io pt = pt1@pt2\<close>
          using \<open>pt2 \<noteq> []\<close> by blast
      next
        case b2
        then obtain q' A t1 t2 where "q' \<in> rd_targets (q,pt)"
                               and   "(A,t1,t2) \<in> atcs (target q pt,q')"
                               and   "io \<in> (\<lambda> io_atc . ioP @ p_io pt @ io_atc) ` (acyclic_language_intersection (from_FSM M (target q pt)) A)"
          by blast

        then obtain ioA where "io = ioP @ p_io pt @ ioA" 
                        and   "ioA \<in> acyclic_language_intersection (from_FSM M (target q pt)) A"
          by blast

        moreover have "ioA \<notin> (remove_proper_prefixes (acyclic_language_intersection (from_FSM M (target q pt)) A))"
        proof 
          assume "ioA \<in> remove_proper_prefixes (acyclic_language_intersection (FSM.from_FSM M (target q pt)) A)"
          then have "io \<in> tmax"
            using \<open>(q,P) \<in> prs\<close> \<open>ioP \<in> remove_proper_prefixes (L_acyclic P)\<close> \<open>pt \<in> tps q\<close> \<open>q' \<in> rd_targets (q,pt)\<close> \<open>(A,t1,t2) \<in> atcs (target q pt,q')\<close> unfolding tmax_def \<open>io = ioP @ p_io pt @ ioA\<close> by force
          then show False
            using \<open>io \<notin> tmax\<close> by simp
        qed
        ultimately obtain ioA2 where "ioA @ ioA2 \<in> acyclic_language_intersection (from_FSM M (target q pt)) A" 
                               and   "ioA2 \<noteq> []"
          unfolding remove_proper_prefixes_def by blast
        then have "io@ioA2 \<in> test_suite_to_io M T"
          using \<open>(q,P) \<in> prs\<close> \<open>ioP \<in> remove_proper_prefixes (L_acyclic P)\<close> \<open>pt \<in> tps q\<close> \<open>q' \<in> rd_targets (q,pt)\<close> \<open>(A,t1,t2) \<in> atcs (target q pt,q')\<close> \<open>ioA @ ioA2 \<in> acyclic_language_intersection (from_FSM M (target q pt)) A\<close> unfolding t_def t1_def \<open>io = ioP @ p_io pt @ ioA\<close> by force
        
        then show ?thesis 
          using \<open>ioA2 \<noteq> []\<close> by blast
      qed
    qed 
  qed


  show ?thesis unfolding t2_def
  proof 
    show "{io' \<in> test_suite_to_io M T. \<nexists>io''. io'' \<noteq> [] \<and> io' @ io'' \<in> test_suite_to_io M T} \<subseteq> remove_proper_prefixes tmax"
    proof 
      fix io assume "io \<in> {io' \<in> test_suite_to_io M T. \<nexists>io''. io'' \<noteq> [] \<and> io' @ io'' \<in> test_suite_to_io M T}"
      then have "io \<in> test_suite_to_io M T" and "\<nexists>io''. io'' \<noteq> [] \<and> io @ io'' \<in> test_suite_to_io M T" 
        by blast+
      show "io \<in> remove_proper_prefixes tmax"
        using \<open>\<nexists>io''. io'' \<noteq> [] \<and> io @ io'' \<in> test_suite_to_io M T\<close>
        using tmax_sub tmax_max[OF \<open>io \<in> test_suite_to_io M T\<close>] unfolding remove_proper_prefixes_def
        by auto 
    qed
    show "remove_proper_prefixes tmax \<subseteq> {io' \<in> test_suite_to_io M T. \<nexists>io''. io'' \<noteq> [] \<and> io' @ io'' \<in> test_suite_to_io M T}"
    proof 
      fix io assume "io \<in> remove_proper_prefixes tmax"
      then have "io \<in> tmax" and "\<nexists>io''. io'' \<noteq> [] \<and> io @ io'' \<in> remove_proper_prefixes tmax"
        unfolding remove_proper_prefixes_def by blast+
      then have "io \<in> test_suite_to_io M T"
        using tmax_sub by blast
      moreover have "\<nexists>io''. io'' \<noteq> [] \<and> io @ io'' \<in> test_suite_to_io M T"
      proof 
        assume "\<exists>io''. io'' \<noteq> [] \<and> io @ io'' \<in> test_suite_to_io M T"
        then obtain io'' where "io'' \<noteq> []" and "io @ io'' \<in> test_suite_to_io M T"
          by blast
        then obtain io''' where "(io @ io'') @ io''' \<in> test_suite_to_io M T" 
                          and   "(\<nexists>zs. zs \<noteq> [] \<and> (io @ io'') @ io''' @ zs \<in> test_suite_to_io M T)"
          using finite_set_elem_maximal_extension_ex[OF \<open>io @ io'' \<in> test_suite_to_io M T\<close> test_suite_to_io_finite[OF assms(1,2)]] by blast

        have "io @ (io'' @ io''') \<in> tmax"
          using tmax_max[OF \<open>(io @ io'') @ io''' \<in> test_suite_to_io M T\<close>] \<open>(\<nexists>zs. zs \<noteq> [] \<and> (io @ io'') @ io''' @ zs \<in> test_suite_to_io M T)\<close> by force
        moreover have "io''@io''' \<noteq> []"
          using \<open>io'' \<noteq> []\<close> by auto

        ultimately show "False" 
          using \<open>\<nexists>io''. io'' \<noteq> [] \<and> io @ io'' \<in> remove_proper_prefixes tmax\<close> 
          by (metis (mono_tags, lifting) \<open>io \<in> remove_proper_prefixes tmax\<close> mem_Collect_eq remove_proper_prefixes_def) 
      qed
          

      ultimately show "io \<in> {io' \<in> test_suite_to_io M T. \<nexists>io''. io'' \<noteq> [] \<and> io' @ io'' \<in> test_suite_to_io M T}"
        by blast
    qed
  qed
qed


lemma test_suite_to_io_pass_maximal :
  assumes "implies_completeness T M m"
  and     "is_finite_test_suite T"  
shows "pass_io_set M' (test_suite_to_io M T) = pass_io_set_maximal M' {io' \<in> (test_suite_to_io M T) . \<not> (\<exists> io'' . io'' \<noteq> [] \<and> io'@io'' \<in> (test_suite_to_io M T))}"
proof -

  (* finiteness *)
  have p1: "finite (test_suite_to_io M T)"
    using test_suite_to_io_finite[OF assms] by assumption

  (* prefix closure *)
  obtain prs tps rd_targets atcs where "T = Test_Suite prs tps rd_targets atcs"
    by (meson test_suite.exhaust)
  then obtain repetition_sets where repetition_sets_def: "implies_completeness_for_repetition_sets (Test_Suite prs tps rd_targets atcs) M m repetition_sets"
    using assms(1) unfolding implies_completeness_def by blast
  then have "implies_completeness (Test_Suite prs tps rd_targets atcs) M m"
    unfolding implies_completeness_def by blast
  then have test_suite_language_prop: "test_suite_to_io M (Test_Suite prs tps rd_targets atcs) \<subseteq> L M"
    using test_suite_to_io_language by blast

  have p2: "\<And>io' io''. io' @ io'' \<in> test_suite_to_io M T \<Longrightarrow> io' \<in> test_suite_to_io M T"
    unfolding \<open>T = Test_Suite prs tps rd_targets atcs\<close>
  proof -
    fix io' io'' assume "io' @ io'' \<in> test_suite_to_io M (Test_Suite prs tps rd_targets atcs)"

    have preamble_prop : "\<And> io''' q P . (q,P) \<in> prs \<Longrightarrow> io'@io''' \<in> L P \<Longrightarrow> io' \<in> test_suite_to_io M (Test_Suite prs tps rd_targets atcs)"
    proof -
      fix io''' q P assume "(q,P) \<in> prs" and "io'@io''' \<in> L P" 
      have "io' \<in> (\<Union> (q,P) \<in> prs . L P)" 
        using \<open>(q,P) \<in> prs\<close> language_prefix[OF \<open>io'@io''' \<in> L P\<close>] by auto
      then show "io' \<in> test_suite_to_io M (Test_Suite prs tps rd_targets atcs)" 
        unfolding test_suite_to_io.simps by blast
    qed

    have traversal_path_prop : "\<And> io''' p pt q P . io'@io''' \<in> (\<lambda> io' . p_io p @ io') ` (set (prefixes (p_io pt))) \<Longrightarrow> (q,P) \<in> prs \<Longrightarrow> path P (initial P) p \<Longrightarrow> target (initial P) p = q \<Longrightarrow> pt \<in> tps q \<Longrightarrow> io' \<in> test_suite_to_io M (Test_Suite prs tps rd_targets atcs)"
    proof - 
      fix io''' p pt q P assume "io'@io''' \<in> (\<lambda> io' . p_io p @ io') ` (set (prefixes (p_io pt)))"  
                            and "(q,P) \<in> prs" 
                            and "path P (initial P) p" 
                            and "target (initial P) p = q" 
                            and "pt \<in> tps q"

      obtain ioP1 where "io'@io''' = p_io p @ ioP1" and "ioP1 \<in> (set (prefixes (p_io pt)))"
        using \<open>io'@io''' \<in> (\<lambda> io' . p_io p @ io') ` (set (prefixes (p_io pt)))\<close> by auto
      then obtain ioP2 where "ioP1 @ ioP2 = p_io pt"
         unfolding prefixes_set by blast


      show "io' \<in> test_suite_to_io M (Test_Suite prs tps rd_targets atcs)"
      proof (cases "length io' \<le> length (p_io p)")
        case True
        then have "io' = (take (length io') (p_io p))"
          using \<open>io'@io''' = p_io p @ ioP1\<close>
          by (metis (no_types, lifting) order_refl take_all take_le) 
        then have "p_io p = io'@(drop (length io') (p_io p))"
          by (metis (no_types, lifting) append_take_drop_id)
        then have "io'@(drop (length io') (p_io p)) \<in> L P"
          using language_state_containment[OF \<open>path P (initial P) p\<close>] by blast
        then show ?thesis 
          using preamble_prop[OF \<open>(q,P) \<in> prs\<close>] by blast
      next
        case False
        then have "io' = p_io p @ (take (length io' - length (p_io p)) ioP1)"
          using \<open>io'@io''' = p_io p @ ioP1\<close>
          by (metis (no_types, lifting) le_cases take_all take_append take_le) 
        moreover have "(take (length io' - length (p_io p)) ioP1) \<in> (set (prefixes (p_io pt)))"
        proof -
          have "ioP1 = (take (length io' - length (p_io p)) ioP1) @ (drop (length io' - length (p_io p)) ioP1)"
            by auto
          then have "(take (length io' - length (p_io p)) ioP1) @ ((drop (length io' - length (p_io p)) ioP1) @ ioP2) = p_io pt"
            using \<open>ioP1 @ ioP2 = p_io pt\<close> by (metis (mono_tags, lifting) append_assoc) 
          then show ?thesis
            unfolding prefixes_set by blast
        qed
        ultimately have "io' \<in> (\<lambda> io' . p_io p @ io') ` (set (prefixes (p_io pt)))"
          by blast
        then have "io' \<in> (\<Union>{(\<lambda> io' . p_io p @ io') ` (set (prefixes (p_io pt))) | p pt . \<exists> q P . (q,P) \<in> prs \<and> path P (initial P) p \<and> target (initial P) p = q \<and> pt \<in> tps q})"
          using \<open>(q,P) \<in> prs\<close> \<open>path P (initial P) p\<close> \<open>target (initial P) p = q\<close> \<open>pt \<in> tps q\<close> by blast
        then show ?thesis 
          unfolding test_suite_to_io.simps by blast          
      qed
    qed


    from \<open>io' @ io'' \<in> test_suite_to_io M (Test_Suite prs tps rd_targets atcs)\<close> consider
      (a) "io' @ io'' \<in> (\<Union> (q,P) \<in> prs . L P)" |
      (b) "io' @ io'' \<in> (\<Union>{(\<lambda> io' . p_io p @ io') ` (set (prefixes (p_io pt))) | p pt . \<exists> q P . (q,P) \<in> prs \<and> path P (initial P) p \<and> target (initial P) p = q \<and> pt \<in> tps q})" |
      (c) "io' @ io'' \<in> (\<Union>{(\<lambda> io_atc . p_io p @ p_io pt @ io_atc) ` (atc_to_io_set (from_FSM M (target q pt)) A) | p pt q A . \<exists> P q' t1 t2 . (q,P) \<in> prs \<and> path P (initial P) p \<and> target (initial P) p = q \<and> pt \<in> tps q \<and> q' \<in> rd_targets (q,pt) \<and> (A,t1,t2) \<in> atcs (target q pt,q') })"
      unfolding test_suite_to_io.simps
      by blast

    then show "io' \<in> test_suite_to_io M (Test_Suite prs tps rd_targets atcs)" 
    proof cases
      case a
      then show ?thesis using preamble_prop by blast
    next
      case b
      then show ?thesis using traversal_path_prop by blast
    next
      case c
      then obtain p pt q A  P q' t1 t2  where "io' @ io'' \<in> (\<lambda> io_atc . p_io p @ p_io pt @ io_atc) ` (atc_to_io_set (from_FSM M (target q pt)) A)"
                                          and "(q,P) \<in> prs" 
                                          and "path P (initial P) p"
                                          and "target (initial P) p = q"
                                          and "pt \<in> tps q"
                                          and "q' \<in> rd_targets (q,pt)"
                                          and "(A,t1,t2) \<in> atcs (target q pt,q')"
        by blast

      obtain ioA where "io' @ io'' = p_io p @ p_io pt @ ioA" 
                   and "ioA \<in> (atc_to_io_set (from_FSM M (target q pt)) A)"
        using \<open>io' @ io'' \<in> (\<lambda> io_atc . p_io p @ p_io pt @ io_atc) ` (atc_to_io_set (from_FSM M (target q pt)) A)\<close> 
        by blast


      show ?thesis proof (cases "length io' \<le> length (p_io p @ p_io pt)")
        case True
        then have "io' @ (drop (length io') (p_io p @ p_io pt)) = p_io p @ p_io pt"
          using \<open>io' @ io'' = p_io p @ p_io pt @ ioA\<close>
          by (simp add: append_eq_conv_conj) 
        moreover have "p_io p @ p_io pt \<in> (\<lambda> io' . p_io p @ io') ` (set (prefixes (p_io pt)))"
          unfolding prefixes_set by blast
        ultimately have "io'@(drop (length io') (p_io p @ p_io pt)) \<in> (\<lambda> io' . p_io p @ io') ` (set (prefixes (p_io pt)))"
          by simp
        then show ?thesis 
          using traversal_path_prop[OF _ \<open>(q,P) \<in> prs\<close> \<open>path P (initial P) p\<close> \<open>target (initial P) p = q\<close> \<open>pt \<in> tps q\<close>] by blast
      next
        case False
        then have "io' = (p_io p @ p_io pt) @ (take (length io' - length (p_io p @ p_io pt)) ioA)"
        proof -
          have "io' = take (length io') (io' @ io'')"
            by auto
          then show ?thesis
            using False \<open>io' @ io'' = p_io p @ p_io pt @ ioA\<close> by fastforce
        qed
        moreover have "(take (length io' - length (p_io p @ p_io pt)) ioA) \<in> (atc_to_io_set (from_FSM M (target q pt)) A)"
        proof -
          have "(take (length io' - length (p_io p @ p_io pt)) ioA)@(drop (length io' - length (p_io p @ p_io pt)) ioA) \<in> L (from_FSM M (target q pt)) \<inter> L A"
            using \<open>ioA \<in> (atc_to_io_set (from_FSM M (target q pt)) A)\<close> by auto
          then have *: "(take (length io' - length (p_io p @ p_io pt)) ioA)@(drop (length io' - length (p_io p @ p_io pt)) ioA) \<in> L (from_FSM M (target q pt))"
               and **: "(take (length io' - length (p_io p @ p_io pt)) ioA)@(drop (length io' - length (p_io p @ p_io pt)) ioA) \<in> L A"
            by blast+
          show ?thesis
            using language_prefix[OF *] language_prefix[OF **]
            unfolding atc_to_io_set.simps by blast
        qed
        ultimately have "io' \<in> (\<lambda> io_atc . p_io p @ p_io pt @ io_atc) ` (atc_to_io_set (from_FSM M (target q pt)) A)"
          by force
            
        then have "io' \<in> (\<Union>{(\<lambda> io_atc . p_io p @ p_io pt @ io_atc) ` (atc_to_io_set (from_FSM M (target q pt)) A) | p pt q A . \<exists> P q' t1 t2 . (q,P) \<in> prs \<and> path P (initial P) p \<and> target (initial P) p = q \<and> pt \<in> tps q \<and> q' \<in> rd_targets (q,pt) \<and> (A,t1,t2) \<in> atcs (target q pt,q') })"
          using \<open>(q,P) \<in> prs\<close> \<open>path P (initial P) p\<close> \<open>target (initial P) p = q\<close> \<open>pt \<in> tps q\<close> \<open>q' \<in> rd_targets (q,pt)\<close> \<open>(A,t1,t2) \<in> atcs (target q pt,q')\<close> by blast
        then show ?thesis 
          unfolding test_suite_to_io.simps by blast
      qed
    qed
  qed


  then show ?thesis
    using pass_io_set_maximal_from_pass_io_set[OF p1] by blast
qed



lemma passes_test_suite_as_maximal_sequences_completeness :
  assumes "implies_completeness T M m"
  and     "is_finite_test_suite T"
  and     "observable M" 
  and     "observable M'"
  and     "inputs M' = inputs M"
  and     "inputs M \<noteq> {}"
  and     "completely_specified M"
  and     "completely_specified M'"
  and     "size M' \<le> m"
shows     "(L M' \<subseteq> L M) \<longleftrightarrow> pass_io_set_maximal M' (test_suite_to_io_maximal M T)"
  unfolding passes_test_suite_completeness[OF assms(1,3-9)]
  unfolding test_suite_to_io_pass[OF assms(1,3-8),symmetric]
  unfolding test_suite_to_io_pass_maximal[OF assms(1,2)]
  unfolding test_suite_to_io_maximal_code[OF assms(1,2,3)]
  by simp


lemma test_suite_to_io_maximal_finite :
  assumes "implies_completeness T M m"
  and     "is_finite_test_suite T"
  and     "observable M"
shows "finite (test_suite_to_io_maximal M T)"
 using test_suite_to_io_finite[OF assms(1,2)]
 unfolding test_suite_to_io_maximal_code[OF assms, symmetric]
 by simp


end