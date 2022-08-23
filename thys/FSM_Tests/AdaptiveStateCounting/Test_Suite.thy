section \<open>Test Suites\<close>

text \<open>This theory introduces a predicate @{text "implies_completeness"} and proves that
      any test suite satisfying this predicate is sufficient to check the reduction conformance
      relation between two (possibly nondeterministic FSMs)\<close> 


theory Test_Suite
imports Helper_Algorithms Adaptive_Test_Case Traversal_Set 
begin

subsection \<open>Preliminary Definitions\<close>


type_synonym ('a,'b,'c) preamble = "('a,'b,'c) fsm"
type_synonym ('a,'b,'c) traversal_path = "('a \<times> 'b \<times> 'c \<times> 'a) list"
type_synonym ('a,'b,'c) separator = "('a,'b,'c) fsm"

text \<open>A test suite contains of
        1) a set of d-reachable states with their associated preambles
        2) a map from d-reachable states to their associated m-traversal paths 
        3) a map from d-reachable states and associated m-traversal paths to the set of states to r-distinguish the targets of those paths from
        4) a map from pairs of r-distinguishable states to a separator\<close>
datatype ('a,'b,'c,'d) test_suite = Test_Suite "('a \<times> ('a,'b,'c) preamble) set"   
                                               "'a \<Rightarrow> ('a,'b,'c) traversal_path set" 
                                               "('a \<times> ('a,'b,'c) traversal_path) \<Rightarrow> 'a set" 
                                               "('a \<times> 'a) \<Rightarrow> (('d,'b,'c) separator \<times> 'd \<times> 'd) set"




subsection \<open>A Sufficiency Criterion for Reduction Testing\<close>

(* to simplify the soundness proof, this formalisation also requires tps to contain nothing but the m-traversal paths;
   this could be lifted by requiring that for every additional path the suite retains additional paths such that all "non-deadlock"
   (w.r.t. the set of all (tps q) paths) states are output complete for the inputs applied *)  

fun implies_completeness_for_repetition_sets :: "('a,'b,'c,'d) test_suite \<Rightarrow> ('a,'b,'c) fsm \<Rightarrow> nat \<Rightarrow> ('a set \<times> 'a set) list \<Rightarrow> bool" where
  "implies_completeness_for_repetition_sets (Test_Suite prs tps rd_targets separators) M m repetition_sets = 
    ( (initial M,initial_preamble M) \<in> prs 
    \<and> (\<forall> q P . (q,P) \<in> prs \<longrightarrow> (is_preamble P M q) \<and> (tps q) \<noteq> {})
    \<and> (\<forall> q1 q2 A d1 d2 . (A,d1,d2) \<in> separators (q1,q2) \<longrightarrow> (A,d2,d1) \<in> separators (q2,q1) \<and> is_separator M q1 q2 A d1 d2)
    \<and> (\<forall> q . q \<in> states M \<longrightarrow> (\<exists>d \<in> set repetition_sets. q \<in> fst d))
    \<and> (\<forall> d . d \<in> set repetition_sets \<longrightarrow> ((fst d \<subseteq> states M) \<and> (snd d = fst d \<inter> fst ` prs) \<and> (\<forall> q1 q2 . q1 \<in> fst d \<longrightarrow> q2 \<in> fst d \<longrightarrow> q1 \<noteq> q2 \<longrightarrow> separators (q1,q2) \<noteq> {})))
    \<and> (\<forall> q . q \<in> image fst prs \<longrightarrow> tps q \<subseteq> {p1 . \<exists> p2 d . (p1@p2,d) \<in> m_traversal_paths_with_witness M q repetition_sets m} \<and> fst ` (m_traversal_paths_with_witness M q repetition_sets m) \<subseteq> tps q) 
    \<and> (\<forall> q p d . q \<in> image fst prs \<longrightarrow> (p,d) \<in> m_traversal_paths_with_witness M q repetition_sets m \<longrightarrow> 
          ( (\<forall> p1 p2 p3 . p=p1@p2@p3 \<longrightarrow> p2 \<noteq> [] \<longrightarrow> target q p1 \<in> fst d \<longrightarrow> target q (p1@p2) \<in> fst d \<longrightarrow> target q p1 \<noteq> target q (p1@p2) \<longrightarrow> (p1 \<in> tps q \<and> (p1@p2) \<in> tps q \<and> target q p1 \<in> rd_targets (q,(p1@p2)) \<and> target q (p1@p2) \<in> rd_targets (q,p1)))
          \<and> (\<forall> p1 p2 q' . p=p1@p2 \<longrightarrow> q' \<in> image fst prs \<longrightarrow> target q p1 \<in> fst d \<longrightarrow> q' \<in> fst d \<longrightarrow> target q p1 \<noteq> q' \<longrightarrow> (p1 \<in> tps q \<and> [] \<in> tps q' \<and> target q p1 \<in> rd_targets (q',[]) \<and> q' \<in> rd_targets (q,p1))))
          \<and> (\<forall> q1 q2 . q1 \<noteq> q2 \<longrightarrow> q1 \<in> snd d \<longrightarrow> q2 \<in> snd d \<longrightarrow> ([] \<in> tps q1 \<and> [] \<in> tps q2 \<and> q1 \<in> rd_targets (q2,[]) \<and> q2 \<in> rd_targets (q1,[]))))
  )"

definition implies_completeness :: "('a,'b,'c,'d) test_suite \<Rightarrow> ('a,'b,'c) fsm \<Rightarrow> nat \<Rightarrow> bool" where
  "implies_completeness T M m = (\<exists> repetition_sets . implies_completeness_for_repetition_sets T M m repetition_sets)"



lemma implies_completeness_for_repetition_sets_simps : 
  assumes "implies_completeness_for_repetition_sets (Test_Suite prs tps rd_targets separators) M m repetition_sets"
  shows "(initial M,initial_preamble M) \<in> prs" 
    and "\<And> q P . (q,P) \<in> prs \<Longrightarrow> (is_preamble P M q) \<and> (tps q) \<noteq> {}"
    and "\<And> q1 q2 A d1 d2 . (A,d1,d2) \<in> separators (q1,q2) \<Longrightarrow> (A,d2,d1) \<in> separators (q2,q1) \<and> is_separator M q1 q2 A d1 d2"
    and "\<And> q . q \<in> states M \<Longrightarrow> (\<exists>d \<in> set repetition_sets. q \<in> fst d)"
    and "\<And> d . d \<in> set repetition_sets \<Longrightarrow> (fst d \<subseteq> states M) \<and> (snd d = fst d \<inter> fst ` prs)"
    and "\<And> d q1 q2 . d \<in> set repetition_sets \<Longrightarrow> q1 \<in> fst d \<Longrightarrow> q2 \<in> fst d \<Longrightarrow> q1 \<noteq> q2 \<Longrightarrow> separators (q1,q2) \<noteq> {}"
    and "\<And> q . q \<in> image fst prs \<Longrightarrow> tps q \<subseteq> {p1 . \<exists> p2 d . (p1@p2,d) \<in> m_traversal_paths_with_witness M q repetition_sets m} \<and> fst ` (m_traversal_paths_with_witness M q repetition_sets m) \<subseteq> tps q" 
    and "\<And> q p d p1 p2 p3 . q \<in> image fst prs \<Longrightarrow> (p,d) \<in> m_traversal_paths_with_witness M q repetition_sets m \<Longrightarrow> p=p1@p2@p3 \<Longrightarrow> p2 \<noteq> [] \<Longrightarrow> target q p1 \<in> fst d \<Longrightarrow> target q (p1@p2) \<in> fst d \<Longrightarrow> target q p1 \<noteq> target q (p1@p2) \<Longrightarrow> (p1 \<in> tps q \<and> (p1@p2) \<in> tps q \<and> target q p1 \<in> rd_targets (q,(p1@p2)) \<and> target q (p1@p2) \<in> rd_targets (q,p1))"
    and "\<And> q p d p1 p2 q' . q \<in> image fst prs \<Longrightarrow> (p,d) \<in> m_traversal_paths_with_witness M q repetition_sets m \<Longrightarrow> p=p1@p2 \<Longrightarrow> q' \<in> image fst prs \<Longrightarrow> target q p1 \<in> fst d \<Longrightarrow> q' \<in> fst d \<Longrightarrow> target q p1 \<noteq> q' \<Longrightarrow> (p1 \<in> tps q \<and> [] \<in> tps q' \<and> target q p1 \<in> rd_targets (q',[]) \<and> q' \<in> rd_targets (q,p1))"
    and "\<And> q p d q1 q2 . q \<in> image fst prs \<Longrightarrow> (p,d) \<in> m_traversal_paths_with_witness M q repetition_sets m \<Longrightarrow> q1 \<noteq> q2 \<Longrightarrow> q1 \<in> snd d \<Longrightarrow> q2 \<in> snd d \<Longrightarrow> ([] \<in> tps q1 \<and> [] \<in> tps q2 \<and> q1 \<in> rd_targets (q2,[]) \<and> q2 \<in> rd_targets (q1,[]))"
proof-

  show "(initial M,initial_preamble M) \<in> prs" 
  and  "\<And> q . q \<in> image fst prs \<Longrightarrow> tps q \<subseteq> {p1 . \<exists> p2 d . (p1@p2,d) \<in> m_traversal_paths_with_witness M q repetition_sets m} \<and> fst ` (m_traversal_paths_with_witness M q repetition_sets m) \<subseteq> tps q"
    using assms unfolding implies_completeness_for_repetition_sets.simps by blast+

  show "\<And> q1 q2 A d1 d2 . (A,d1,d2) \<in> separators (q1,q2) \<Longrightarrow> (A,d2,d1) \<in> separators (q2,q1) \<and> is_separator M q1 q2 A d1 d2"
  and  "\<And> q P . (q,P) \<in> prs \<Longrightarrow> (is_preamble P M q) \<and> (tps q) \<noteq> {}"
  and  "\<And> q . q \<in> states M \<Longrightarrow> (\<exists>d \<in> set repetition_sets. q \<in> fst d)"
  and  "\<And> d . d \<in> set repetition_sets \<Longrightarrow> (fst d \<subseteq> states M) \<and> (snd d = fst d \<inter> fst ` prs)"
  and  "\<And> d q1 q2 . d \<in> set repetition_sets \<Longrightarrow> q1 \<in> fst d \<Longrightarrow> q2 \<in> fst d \<Longrightarrow> q1 \<noteq> q2 \<Longrightarrow> separators (q1,q2) \<noteq> {}"
    using assms unfolding implies_completeness_for_repetition_sets.simps by force+

  show "\<And> q p d p1 p2 p3 . q \<in> image fst prs \<Longrightarrow> (p,d) \<in> m_traversal_paths_with_witness M q repetition_sets m \<Longrightarrow> p=p1@p2@p3 \<Longrightarrow> p2 \<noteq> [] \<Longrightarrow> target q p1 \<in> fst d \<Longrightarrow> target q (p1@p2) \<in> fst d \<Longrightarrow> target q p1 \<noteq> target q (p1@p2) \<Longrightarrow> (p1 \<in> tps q \<and> (p1@p2) \<in> tps q \<and> target q p1 \<in> rd_targets (q,(p1@p2)) \<and> target q (p1@p2) \<in> rd_targets (q,p1))"
    using assms unfolding implies_completeness_for_repetition_sets.simps by (metis (no_types, lifting))

  show "\<And> q p d p1 p2 q' . q \<in> image fst prs \<Longrightarrow> (p,d) \<in> m_traversal_paths_with_witness M q repetition_sets m \<Longrightarrow> p=p1@p2 \<Longrightarrow> q' \<in> image fst prs \<Longrightarrow> target q p1 \<in> fst d \<Longrightarrow> q' \<in> fst d \<Longrightarrow> target q p1 \<noteq> q' \<Longrightarrow> (p1 \<in> tps q \<and> [] \<in> tps q' \<and> target q p1 \<in> rd_targets (q',[]) \<and> q' \<in> rd_targets (q,p1))"
    using assms unfolding implies_completeness_for_repetition_sets.simps by (metis (no_types, lifting))

  show "\<And> q p d q1 q2 . q \<in> image fst prs \<Longrightarrow> (p,d) \<in> m_traversal_paths_with_witness M q repetition_sets m \<Longrightarrow> q1 \<noteq> q2 \<Longrightarrow> q1 \<in> snd d \<Longrightarrow> q2 \<in> snd d \<Longrightarrow> ([] \<in> tps q1 \<and> [] \<in> tps q2 \<and> q1 \<in> rd_targets (q2,[]) \<and> q2 \<in> rd_targets (q1,[]))"
    using assms unfolding implies_completeness_for_repetition_sets.simps by (metis (no_types, lifting))
qed




subsection \<open>A Pass Relation for Test Suites and Reduction Testing\<close>

fun passes_test_suite :: "('a,'b,'c) fsm \<Rightarrow> ('a,'b,'c,'d) test_suite \<Rightarrow> ('e,'b,'c) fsm \<Rightarrow> bool" where
  "passes_test_suite M (Test_Suite prs tps rd_targets separators) M' = (
    \<comment> \<open>Reduction on preambles: as the preambles contain all responses of M to their chosen inputs, M' must not exhibit any other response\<close>
    (\<forall> q P io x y y' . (q,P) \<in> prs \<longrightarrow> io@[(x,y)] \<in> L P \<longrightarrow> io@[(x,y')] \<in> L M' \<longrightarrow> io@[(x,y')] \<in> L P) 
    \<comment> \<open>Reduction on traversal-paths applied after preambles (i.e., completed paths in preambles) - note that tps q is not necessarily prefix-complete\<close>
    \<and> (\<forall> q P pP ioT pT x y y' . (q,P) \<in> prs \<longrightarrow> path P (initial P) pP \<longrightarrow> target (initial P) pP = q \<longrightarrow> pT \<in> tps q \<longrightarrow> ioT@[(x,y)] \<in> set (prefixes (p_io pT)) \<longrightarrow> (p_io pP)@ioT@[(x,y')] \<in> L M' \<longrightarrow> (\<exists> pT' . pT' \<in> tps q \<and> ioT@[(x,y')] \<in> set (prefixes (p_io pT'))))
    \<comment> \<open>Passing separators: if M' contains an IO-sequence that in the test suite leads through a preamble and an m-traversal path and the target of the latter is to be r-distinguished from some other state, then M' passes the corresponding ATC\<close>
    \<and> (\<forall> q P pP pT . (q,P) \<in> prs \<longrightarrow> path P (initial P) pP \<longrightarrow> target (initial P) pP = q \<longrightarrow> pT \<in> tps q \<longrightarrow> (p_io pP)@(p_io pT) \<in> L M' \<longrightarrow> (\<forall> q' A d1 d2 qT . q' \<in> rd_targets (q,pT) \<longrightarrow> (A,d1,d2) \<in> separators (target q pT, q') \<longrightarrow> qT \<in> io_targets M' ((p_io pP)@(p_io pT)) (initial M') \<longrightarrow> pass_separator_ATC M' A qT d2))
    )"                                                                                                                                                                                                                                                                                                   





subsection \<open>Soundness of Sufficient Test Suites\<close>


lemma passes_test_suite_soundness_helper_1 :
  assumes "is_preamble P M q"
  and     "observable M"
  and     "io@[(x,y)] \<in> L P"
  and     "io@[(x,y')] \<in> L M"
shows     "io@[(x,y')] \<in> L P"
proof -
  have   "is_submachine P M"
  and *: "\<And> q' x t t' . q'\<in>reachable_states P \<Longrightarrow> x\<in>FSM.inputs M \<Longrightarrow>
            t\<in>FSM.transitions P \<Longrightarrow> t_source t = q' \<Longrightarrow> t_input t = x \<Longrightarrow>
            t'\<in>FSM.transitions M \<Longrightarrow> t_source t' = q' \<Longrightarrow> t_input t' = x \<Longrightarrow> t' \<in> FSM.transitions P"
    using assms(1)  unfolding is_preamble_def by blast+

  have "initial P = initial M"
    unfolding submachine_simps[OF \<open>is_submachine P M\<close>]
    by simp
  
  obtain p where "path M (initial M) p" and "p_io p = io @ [(x,y')]"
    using assms(4) unfolding submachine_simps[OF \<open>is_submachine P M\<close>] by auto
  
  obtain p' t where "p = p'@[t]"
    using \<open>p_io p = io @ [(x,y')]\<close> by (induction p rule: rev_induct; auto)

  have "path M (initial M) p'" and "t \<in> transitions M" and "t_source t = target (initial M) p'"
    using \<open>path M (initial M) p\<close> path_append_transition_elim
    unfolding \<open>p = p'@[t]\<close> by force+

  have "p_io p' = io" and "t_input t = x" and "t_output t = y'"
    using \<open>p_io p = io @ [(x,y')]\<close> unfolding \<open>p = p'@[t]\<close> by force+
     

  have "p_io p' \<in> LS P (FSM.initial M)"
    using assms(3) unfolding \<open>p_io p' = io\<close> \<open>initial P = initial M\<close>
    by (meson language_prefix) 

  have "FSM.initial M \<in> reachable_states P"
    unfolding submachine_simps(1)[OF \<open>is_submachine P M\<close>, symmetric]
    using reachable_states_initial by blast
  
  obtain pp where "path P (initial P) pp" and "p_io pp = io @ [(x,y)]"
    using assms(3) by auto
  then obtain pp' t' where "pp = pp'@[t']"
  proof -
    assume a1: "\<And>pp' t'. pp = pp' @ [t'] \<Longrightarrow> thesis"
    have "pp \<noteq> []"
      using \<open>p_io pp = io @ [(x, y)]\<close> by auto
    then show ?thesis
      using a1 by (metis (no_types) rev_exhaust)
  qed 

  have "path P (initial P) pp'" and "t' \<in> transitions P" and "t_source t' = target (initial P) pp'"
    using \<open>path P (initial P) pp\<close> path_append_transition_elim
    unfolding \<open>pp = pp'@[t']\<close> by force+
  have "p_io pp' = io" and "t_input t' = x"
    using \<open>p_io pp = io @ [(x,y)]\<close> unfolding \<open>pp = pp'@[t']\<close> by force+

  have "path M (initial M) pp'"
    using \<open>path P (initial P) pp'\<close> submachine_path_initial[OF \<open>is_submachine P M\<close>] by blast
  
  have "pp' = p'"
    using observable_path_unique[OF assms(2) \<open>path M (initial M) pp'\<close> \<open>path M (initial M) p'\<close> ]
    unfolding \<open>p_io pp' = io\<close> \<open>p_io p' = io\<close>
    by blast
  then have "t_source t' = target (initial M) p'"
    using \<open>t_source t' = target (initial P) pp'\<close> unfolding \<open>initial P = initial M\<close> by blast


  have "path P (FSM.initial M) p'"
    using observable_preamble_paths[OF assms(1,2) \<open>path M (initial M) p'\<close> 
                                                  \<open>p_io p' \<in> LS P (FSM.initial M)\<close> 
                                                  \<open>FSM.initial M \<in> reachable_states P\<close>]
    by assumption
  then have "target (initial M) p' \<in> reachable_states P"
    using reachable_states_intro unfolding \<open>initial P = initial M\<close>[symmetric] by blast
  moreover have "x \<in> inputs M"
    using \<open>t \<in> transitions M\<close> \<open>t_input t = x\<close> fsm_transition_input by blast


  have "t \<in> transitions P"
    using *[OF \<open>target (initial M) p' \<in> reachable_states P\<close> \<open>x \<in> inputs M\<close> \<open>t' \<in> transitions P\<close> 
               \<open>t_source t' = target (initial M) p'\<close> \<open>t_input t' = x\<close> \<open>t \<in> transitions M\<close> 
               \<open>t_source t = target (FSM.initial M) p'\<close> \<open>t_input t = x\<close>]
    by assumption

  then have "path P (initial P) (p'@[t])"
    using \<open>path P (initial P) pp'\<close> \<open>t_source t = target (initial M) p'\<close>
    unfolding \<open>pp' = p'\<close> \<open>initial P = initial M\<close> 
    using path_append_transition by simp
  then show ?thesis 
    unfolding \<open>p = p'@[t]\<close>[symmetric] LS.simps
    using \<open>p_io p = io@[(x,y')]\<close>
    by force
qed



lemma passes_test_suite_soundness :
  assumes "implies_completeness (Test_Suite prs tps rd_targets separators) M m"
  and     "observable M"
  and     "observable M'"
  and     "inputs M' = inputs M"
  and     "completely_specified M"
  and     "L M' \<subseteq> L M"
shows     "passes_test_suite M (Test_Suite prs tps rd_targets separators) M'"
proof -
  obtain repetition_sets where repetition_sets_def: "implies_completeness_for_repetition_sets (Test_Suite prs tps rd_targets separators) M m repetition_sets"
    using assms(1) unfolding implies_completeness_def by blast


  have t1: "(initial M, initial_preamble M) \<in> prs" 
    using implies_completeness_for_repetition_sets_simps(1)[OF repetition_sets_def] by assumption
  have t2: "\<And> q P. (q, P) \<in> prs \<Longrightarrow> is_preamble P M q \<and> tps q \<noteq> {}"
    using implies_completeness_for_repetition_sets_simps(2)[OF repetition_sets_def] by assumption
  have t3: "\<And> q1 q2 A d1 d2. (A, d1, d2) \<in> separators (q1, q2) \<Longrightarrow> (A, d2, d1) \<in> separators (q2, q1) \<and> is_separator M q1 q2 A d1 d2"
    using implies_completeness_for_repetition_sets_simps(3)[OF repetition_sets_def] by assumption
  
  have t5: "\<And>q. q \<in> FSM.states M \<Longrightarrow> (\<exists>d\<in>set repetition_sets. q \<in> fst d)"
    using implies_completeness_for_repetition_sets_simps(4)[OF repetition_sets_def] by assumption

  have t6: "\<And> q. q \<in> fst ` prs \<Longrightarrow> tps q \<subseteq> {p1 . \<exists> p2 d . (p1@p2,d) \<in> m_traversal_paths_with_witness M q repetition_sets m} 
                                                            \<and> fst ` (m_traversal_paths_with_witness M q repetition_sets m) \<subseteq> tps q"
    using implies_completeness_for_repetition_sets_simps(7)[OF repetition_sets_def] by assumption

  have t7: "\<And> d. d \<in> set repetition_sets \<Longrightarrow> fst d \<subseteq> FSM.states M"
  and  t8: "\<And> d. d \<in> set repetition_sets \<Longrightarrow> snd d \<subseteq> fst d"
  and  t9: "\<And> d q1 q2. d \<in> set repetition_sets \<Longrightarrow> q1 \<in> fst d \<Longrightarrow> q2 \<in> fst d \<Longrightarrow> q1 \<noteq> q2 \<Longrightarrow> separators (q1, q2) \<noteq> {}"
    using implies_completeness_for_repetition_sets_simps(5,6)[OF repetition_sets_def] 
    by blast+

  have t10: "\<And> q p d p1 p2 p3.
              q \<in> fst ` prs \<Longrightarrow>
              (p, d) \<in> m_traversal_paths_with_witness M q repetition_sets m \<Longrightarrow>
              p = p1 @ p2 @ p3 \<Longrightarrow>
              p2 \<noteq> [] \<Longrightarrow>
              target q p1 \<in> fst d \<Longrightarrow>
              target q (p1 @ p2) \<in> fst d \<Longrightarrow>
              target q p1 \<noteq> target q (p1 @ p2) \<Longrightarrow>
              p1 \<in> tps q \<and> p1 @ p2 \<in> tps q \<and> target q p1 \<in> rd_targets (q, p1 @ p2) \<and> target q (p1 @ p2) \<in> rd_targets (q, p1)"
    using implies_completeness_for_repetition_sets_simps(8)[OF repetition_sets_def] by assumption

  have t11: "\<And> q p d p1 p2 q'.
              q \<in> fst ` prs \<Longrightarrow>
              (p, d) \<in> m_traversal_paths_with_witness M q repetition_sets m \<Longrightarrow>
              p = p1 @ p2 \<Longrightarrow>
              q' \<in> fst ` prs \<Longrightarrow>
              target q p1 \<in> fst d \<Longrightarrow>
              q' \<in> fst d \<Longrightarrow> 
              target q p1 \<noteq> q' \<Longrightarrow> 
              p1 \<in> tps q \<and> [] \<in> tps q' \<and> target q p1 \<in> rd_targets (q', []) \<and> q' \<in> rd_targets (q, p1)"
    using implies_completeness_for_repetition_sets_simps(9)[OF repetition_sets_def] by assumption


  have "\<And> q P io x y y' . (q,P) \<in> prs \<Longrightarrow> io@[(x,y)] \<in> L P \<Longrightarrow> io@[(x,y')] \<in> L M' \<Longrightarrow> io@[(x,y')] \<in> L P"
  proof -
    fix q P io x y y' assume "(q,P) \<in> prs" and "io@[(x,y)] \<in> L P" and "io@[(x,y')] \<in> L M'"

    have "is_preamble P M q"
      using \<open>(q,P) \<in> prs\<close> \<open>\<And> q P. (q, P) \<in> prs \<Longrightarrow> is_preamble P M q \<and> tps q \<noteq> {}\<close> by blast

    have "io@[(x,y')] \<in> L M"
      using \<open>io@[(x,y')] \<in> L M'\<close> assms(6) by blast

    show "io@[(x,y')] \<in> L P"
      using passes_test_suite_soundness_helper_1[OF \<open>is_preamble P M q\<close> assms(2) \<open>io@[(x,y)] \<in> L P\<close> \<open>io@[(x,y')] \<in> L M\<close>]
      by assumption
  qed
  then have p1: "(\<forall> q P io x y y' . (q,P) \<in> prs \<longrightarrow> io@[(x,y)] \<in> L P \<longrightarrow> io@[(x,y')] \<in> L M' \<longrightarrow> io@[(x,y')] \<in> L P)"
    by blast



  have "\<And> q P pP ioT pT x x' y y' . (q,P) \<in> prs \<Longrightarrow> 
                                     path P (initial P) pP \<Longrightarrow> 
                                     target (initial P) pP = q \<Longrightarrow> 
                                     pT \<in> tps q \<Longrightarrow> 
                                     ioT @ [(x, y)] \<in> set (prefixes (p_io pT)) \<Longrightarrow> 
                                     (p_io pP)@ioT@[(x',y')] \<in> L M' \<Longrightarrow> 
                                     (\<exists> pT' . pT' \<in> tps q \<and> ioT @ [(x', y')] \<in> set (prefixes (p_io pT')))"
  proof -
    fix q P pP ioT pT x x' y y' 
    assume "(q,P) \<in> prs"  
       and "path P (initial P) pP" 
       and "target (initial P) pP = q" 
       and "pT \<in> tps q" 
       and "ioT @ [(x, y)] \<in> set (prefixes (p_io pT))" 
       and "(p_io pP)@ioT@[(x',y')] \<in> L M'"

    have "is_preamble P M q"
      using \<open>(q,P) \<in> prs\<close> \<open>\<And> q P. (q, P) \<in> prs \<Longrightarrow> is_preamble P M q \<and> tps q \<noteq> {}\<close> by blast
    then have "q \<in> states M"
      unfolding is_preamble_def
      by (metis \<open>path P (FSM.initial P) pP\<close> \<open>target (FSM.initial P) pP = q\<close> path_target_is_state submachine_path) 


    have "initial P = initial M"
      using \<open>is_preamble P M q\<close> unfolding is_preamble_def by auto
    have "path M (initial M) pP"
      using \<open>is_preamble P M q\<close> unfolding is_preamble_def using submachine_path_initial
      using \<open>path P (FSM.initial P) pP\<close> by blast
    

    have "(p_io pP)@ioT@[(x',y')] \<in> L M"
      using \<open>(p_io pP)@ioT@[(x',y')] \<in> L M'\<close> assms(6) by blast
    then obtain pM' where "path M (initial M) pM'" and "p_io pM' = (p_io pP)@ioT@[(x',y')]" 
      by auto

    let ?pP = "take (length pP) pM'"
    let ?pT = "take (length ioT) (drop (length pP) pM')"
    let ?t  = "last pM'"


    have "pM' = ?pP @ ?pT @ [?t]"
    proof -
      have "length pM' = (length pP) + (length ioT) + 1"
        using \<open>p_io pM' = (p_io pP)@ioT@[(x',y')]\<close> 
        unfolding length_map[of "(\<lambda> t . (t_input t, t_output t))", of pM', symmetric] 
                  length_map[of "(\<lambda> t . (t_input t, t_output t))", of pP, symmetric] 
        by auto
      then show ?thesis
        by (metis (no_types, lifting) add_diff_cancel_right' antisym_conv antisym_conv2 
              append_butlast_last_id append_eq_append_conv2 butlast_conv_take drop_Nil drop_eq_Nil 
              le_add1 less_add_one take_add) 
    qed   

    have "p_io ?pP = p_io pP"  
      using \<open>p_io pM' = (p_io pP)@ioT@[(x',y')]\<close>
      by (metis (no_types, lifting) append_eq_conv_conj length_map take_map)

    have "p_io ?pT = ioT" 
      using \<open>p_io pM' = (p_io pP)@ioT@[(x',y')]\<close>
      using \<open>pM' = ?pP @ ?pT @ [?t]\<close>
      by (metis (no_types, lifting) append_eq_conv_conj length_map map_append take_map) 
      
    have "p_io [?t] = [(x',y')]"
      using \<open>p_io pM' = (p_io pP)@ioT@[(x',y')]\<close>
      using \<open>pM' = ?pP @ ?pT @ [?t]\<close>
      by (metis (no_types, lifting) append_is_Nil_conv last_appendR last_map last_snoc list.simps(8) list.simps(9))

    have "path M (initial M) ?pP"
      using \<open>path M (initial M) pM'\<close> \<open>pM' = ?pP @ ?pT @ [?t]\<close>
      by (meson path_prefix_take)
      
    have "?pP = pP"
      using observable_path_unique[OF \<open>observable M\<close> \<open>path M (initial M) ?pP\<close> \<open>path M (initial M) pP\<close> \<open>p_io ?pP = p_io pP\<close>]
      by assumption
    then have "path M q (?pT@[?t])"
      by (metis \<open>FSM.initial P = FSM.initial M\<close> \<open>pM' = take (length pP) pM' @ take (length ioT) (drop (length pP) pM') @ [last pM']\<close> \<open>path M (FSM.initial M) pM'\<close> \<open>target (FSM.initial P) pP = q\<close> path_suffix)
    then have "path M q ?pT" 
         and  "?t \<in> transitions M" 
         and  "t_source ?t = target q ?pT"
      by auto

    have "inputs M \<noteq> {}"
      using language_io(1)[OF \<open>(p_io pP)@ioT@[(x',y')] \<in> L M\<close>, of x' y']
      by auto 

    have "q \<in> fst ` prs"
      using \<open>(q,P) \<in> prs\<close>
      using image_iff by fastforce 

    obtain ioT' where "p_io pT = (ioT @ [(x, y)]) @ ioT'"
      using \<open>ioT @ [(x, y)] \<in> set (prefixes (p_io pT))\<close>
      unfolding prefixes_set 
      by moura
    then have "length pT > length ioT"
      using length_map[of "(\<lambda> t . (t_input t, t_output t))" pT] 
      by auto
    
    obtain pT' d' where "(pT @ pT', d') \<in> m_traversal_paths_with_witness M q repetition_sets m"
      using t6[OF \<open>q \<in> fst ` prs\<close>] \<open>pT \<in> tps q\<close>
      by blast

    let ?p = "pT @ pT'"

    have "path M q ?p"
    and  "find (\<lambda>d. Suc (m - card (snd d)) \<le> length (filter (\<lambda>t. t_target t \<in> fst d) ?p)) repetition_sets = Some d'"
    and  "\<And> p' p''. ?p = p' @ p'' \<Longrightarrow> p'' \<noteq> [] \<Longrightarrow> find (\<lambda>d. Suc (m - card (snd d)) \<le> length (filter (\<lambda>t. t_target t \<in> fst d) p')) repetition_sets = None"
      using \<open>(pT @ pT', d') \<in> m_traversal_paths_with_witness M q repetition_sets m\<close>
            m_traversal_paths_with_witness_set[OF t5 t8 \<open>q \<in> states M\<close>, of m] 
      by blast+

    let ?pIO = "take (length ioT) pT"
    have "?pIO = take (length ioT) ?p" 
      using \<open>length pT > length ioT\<close> by auto
    then have "?p = ?pIO@(drop (length ioT) ?p)"
      by auto
    have "(drop (length ioT) ?p) \<noteq> []" 
      using \<open>length pT > length ioT\<close> by auto

    have "p_io ?pIO = ioT" 
    proof -
      have "p_io ?pIO = take (length ioT) (p_io pT)"
        by (simp add: take_map)
      moreover have "take (length ioT) (p_io pT) = ioT"
        using \<open>p_io pT = (ioT @ [(x, y)]) @ ioT'\<close> by auto
      ultimately show ?thesis by simp
    qed
    then have "p_io ?pIO = p_io ?pT"
      using \<open>p_io ?pT = ioT\<close> by simp
    
    have "path M q ?pIO"
      using \<open>path M q ?p\<close> unfolding \<open>?pIO = take (length ioT) ?p\<close> 
      using path_prefix_take by metis

    have "?pT = ?pIO"
      using observable_path_unique[OF \<open>observable M\<close> \<open>path M q ?pIO\<close> \<open>path M q ?pT\<close> \<open>p_io ?pIO = p_io ?pT\<close>] 
      by simp

    show "(\<exists> pT' . pT' \<in> tps q \<and> ioT @ [(x', y')] \<in> set (prefixes (p_io pT')))"
    proof (cases "find (\<lambda>d. Suc (m - card (snd d)) \<le> length (filter (\<lambda>t. t_target t \<in> fst d) (?pT@[?t]))) repetition_sets = None")
      case True

      obtain pT' d' where "(?pT @ [?t] @ pT', d') \<in> m_traversal_paths_with_witness M q repetition_sets m"
        using m_traversal_path_extension_exist[OF \<open>completely_specified M\<close> \<open>q \<in> states M\<close> \<open>inputs M \<noteq> {}\<close> t5 t8 \<open>path M q (?pT@[?t])\<close> True]
        by auto
      then have "?pT @ [?t] @ pT' \<in> tps q"
        using t6[OF \<open>q \<in> fst ` prs\<close>] by force

      moreover have "ioT @ [(x', y')] \<in> set (prefixes (p_io (?pT @ [?t] @ pT')))"
        using \<open>p_io ?pIO = ioT\<close> \<open>p_io [?t] = [(x',y')]\<close> 
        unfolding \<open>?pT = ?pIO\<close> prefixes_set by force

      ultimately show ?thesis 
        by blast
    next
      case False
      
      note \<open>path M q (?pT @ [?t])\<close> 
      moreover obtain d' where "find (\<lambda>d. Suc (m - card (snd d)) \<le> length (filter (\<lambda>t. t_target t \<in> fst d) (?pT@[?t]))) repetition_sets = Some d'"
        using False by blast

      moreover have "\<forall> p' p''. (?pT @ [?t]) = p' @ p'' \<and> p'' \<noteq> [] \<longrightarrow> find (\<lambda>d. Suc (m - card (snd d)) \<le> length (filter (\<lambda>t. t_target t \<in> fst d) p')) repetition_sets = None"
      proof -
        have "\<And> p' p''. (?pT @ [?t]) = p' @ p'' \<Longrightarrow> p'' \<noteq> [] \<Longrightarrow> find (\<lambda>d. Suc (m - card (snd d)) \<le> length (filter (\<lambda>t. t_target t \<in> fst d) p')) repetition_sets = None"
        proof -
          fix p' p'' assume "(?pT @ [?t]) = p' @ p''" and "p'' \<noteq> []" 
          then obtain pIO' where "?pIO = p' @ pIO'"
            unfolding \<open>?pT = ?pIO\<close>
            by (metis butlast_append butlast_snoc)
          then have "?p = p'@pIO'@(drop (length ioT) ?p)"
            using \<open>?p = ?pIO@((drop (length ioT) ?p))\<close>
            by (metis append.assoc) 
  
          have "pIO' @ drop (length ioT) (pT @ pT') \<noteq> []"
            using \<open>(drop (length ioT) ?p) \<noteq> []\<close> by auto
  
          show "find (\<lambda>d. Suc (m - card (snd d)) \<le> length (filter (\<lambda>t. t_target t \<in> fst d) p')) repetition_sets = None"
            using \<open>\<And> p' p''. ?p = p' @ p'' \<Longrightarrow> p'' \<noteq> [] \<Longrightarrow> find (\<lambda>d. Suc (m - card (snd d)) \<le> length (filter (\<lambda>t. t_target t \<in> fst d) p')) repetition_sets = None\<close>
                  [of p' "pIO'@(drop (length ioT) ?p)", OF \<open>?p = p'@pIO'@(drop (length ioT) ?p)\<close> \<open>pIO' @ drop (length ioT) (pT @ pT') \<noteq> []\<close>]
            by assumption
        qed
        then show ?thesis by blast
      qed

      ultimately have "((?pT @ [?t]),d') \<in> m_traversal_paths_with_witness M q repetition_sets m"
        using m_traversal_paths_with_witness_set[OF t5 t8 \<open>q \<in> states M\<close>, of m] 
        by auto
      then have "(?pT @ [?t]) \<in> tps q"
        using t6[OF \<open>q \<in> fst ` prs\<close>] by force
      moreover have "ioT @ [(x', y')] \<in> set (prefixes (p_io (?pT @ [?t])))"
        using \<open>p_io ?pT = ioT\<close> \<open>p_io [?t] = [(x',y')]\<close>
        unfolding prefixes_set by force

      ultimately show ?thesis 
        by blast
    qed
  qed
  then have p2: "(\<forall> q P pP ioT pT x y y' . (q,P) \<in> prs \<longrightarrow> 
                                            path P (initial P) pP \<longrightarrow> 
                                            target (initial P) pP = q \<longrightarrow> 
                                            pT \<in> tps q \<longrightarrow> 
                                            ioT @ [(x, y)] \<in> set (prefixes (p_io pT)) \<longrightarrow> 
                                            (p_io pP)@ioT@[(x,y')] \<in> L M' \<longrightarrow> 
                                            (\<exists> pT' . pT' \<in> tps q \<and> ioT @ [(x, y')] \<in> set (prefixes (p_io pT'))))"
    by blast


  have "\<And> q P pP pT q' A d1 d2 qT . (q,P) \<in> prs \<Longrightarrow> 
                                      path P (initial P) pP \<Longrightarrow> 
                                      target (initial P) pP = q \<Longrightarrow> 
                                      pT \<in> tps q \<Longrightarrow> 
                                      q' \<in> rd_targets (q,pT) \<Longrightarrow> 
                                      (A,d1,d2) \<in> separators (target q pT, q') \<Longrightarrow> 
                                      qT \<in> io_targets M' ((p_io pP)@(p_io pT)) (initial M') \<Longrightarrow> 
                                      pass_separator_ATC M' A qT d2"
  proof -
    fix q P pP pT q' A d1 d2 qT
    assume "(q,P) \<in> prs" 
    and    "path P (initial P) pP" 
    and    "target (initial P) pP = q" 
    and    "pT \<in> tps q"  
    and    "q' \<in> rd_targets (q,pT)" 
    and    "(A,d1,d2) \<in> separators (target q pT, q')" 
    and    "qT \<in> io_targets M' ((p_io pP)@(p_io pT)) (initial M')"

    have "q \<in> fst ` prs"
      using \<open>(q,P) \<in> prs\<close> by force
    have "is_preamble P M q"
      using \<open>(q,P) \<in> prs\<close> \<open>\<And> q P. (q, P) \<in> prs \<Longrightarrow> is_preamble P M q \<and> tps q \<noteq> {}\<close> by blast
    then have "q \<in> states M"
      unfolding is_preamble_def
      by (metis \<open>path P (FSM.initial P) pP\<close> \<open>target (FSM.initial P) pP = q\<close> path_target_is_state submachine_path) 

    have "initial P = initial M"
      using \<open>is_preamble P M q\<close> unfolding is_preamble_def by auto
    have "path M (initial M) pP"
      using \<open>is_preamble P M q\<close> unfolding is_preamble_def using submachine_path_initial
      using \<open>path P (FSM.initial P) pP\<close> by blast

    have "is_separator M (target q pT) q' A d1 d2"
      using t3[OF \<open>(A,d1,d2) \<in> separators (target q pT, q')\<close>]
      by blast

    have "qT \<in> states M'"
      using \<open>qT \<in> io_targets M' ((p_io pP)@(p_io pT)) (initial M')\<close>
            io_targets_states
      by (metis (no_types, lifting) subsetD) 

    obtain pT' d' where "(pT @ pT', d') \<in> m_traversal_paths_with_witness M q repetition_sets m"
      using t6[OF \<open>q \<in> fst ` prs\<close>] \<open>pT \<in> tps q\<close> 
      by blast
    then have "path M q pT"
      using m_traversal_paths_with_witness_set[OF t5 t8 \<open>q \<in> states M\<close>, of m] 
      by auto
    then have "target q pT \<in> FSM.states M"
      using path_target_is_state by metis

    have "q' \<in> FSM.states M"
      using is_separator_separated_state_is_state[OF \<open>is_separator M (target q pT) q' A d1 d2\<close>] by simp

    have "\<not> pass_separator_ATC M' A qT d2 \<Longrightarrow> \<not> LS M' qT \<subseteq> LS M (target q pT)"
      using pass_separator_ATC_fail_no_reduction[OF \<open>observable M'\<close> \<open>observable M\<close> \<open>qT \<in> states M'\<close>
                                                    \<open>target q pT \<in> FSM.states M\<close> \<open>q' \<in> FSM.states M\<close> 
                                                    \<open>is_separator M (target q pT) q' A d1 d2\<close> \<open>inputs M' = inputs M\<close>]
      by assumption

    moreover have "LS M' qT \<subseteq> LS M (target q pT)"
    proof -
      have "(target q pT) = target (initial M) (pP@pT)"
        using \<open>target (initial P) pP = q\<close> unfolding \<open>initial P = initial M\<close> by auto

      have "path M (initial M) (pP@pT)"
        using \<open>path M (initial M) pP\<close> \<open>target (initial P) pP = q\<close> \<open>path M q pT\<close> unfolding \<open>initial P = initial M\<close> by auto
      
      then have "(target q pT) \<in> io_targets M (p_io pP @ p_io pT) (FSM.initial M)"
        unfolding io_targets.simps \<open>(target q pT) = target (initial M) (pP@pT)\<close>
        using map_append by blast 
      
      show ?thesis
        using observable_language_target[OF \<open>observable M\<close> \<open>(target q pT) \<in> io_targets M (p_io pP @ p_io pT) (FSM.initial M)\<close> 
                                            \<open>qT \<in> io_targets M' ((p_io pP)@(p_io pT)) (initial M')\<close> \<open>L M' \<subseteq> L M\<close>]
        by assumption
    qed

    ultimately show "pass_separator_ATC M' A qT d2"
      by blast
  qed
  then have p3: "(\<forall> q P pP pT . (q,P) \<in> prs \<longrightarrow> 
                                  path P (initial P) pP \<longrightarrow> 
                                  target (initial P) pP = q \<longrightarrow> 
                                  pT \<in> tps q \<longrightarrow> 
                                  (p_io pP)@(p_io pT) \<in> L M' \<longrightarrow> 
                                  (\<forall> q' A d1 d2 qT . q' \<in> rd_targets (q,pT) \<longrightarrow> 
                                  (A,d1,d2) \<in> separators (target q pT, q') \<longrightarrow> 
                                  qT \<in> io_targets M' ((p_io pP)@(p_io pT)) (initial M') \<longrightarrow> 
                                  pass_separator_ATC M' A qT d2))"
    by blast


  show ?thesis 
    using p1 p2 p3
    unfolding passes_test_suite.simps 
    by blast
qed




subsection \<open>Exhaustiveness of Sufficient Test Suites\<close>

text \<open>This subsection shows that test suites satisfying the sufficiency criterion are exhaustive.
      That is, for a System Under Test with at most m states that contains an error (i.e.: is not
      a reduction) a test suite sufficient for m will not pass.\<close>


subsubsection \<open>R Functions\<close>


(* collect all proper suffixes of p that target q' if applied to q *)
definition R :: "('a,'b,'c) fsm \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> ('a \<times> 'b \<times> 'c \<times> 'a) list \<Rightarrow> ('a \<times> 'b \<times> 'c \<times> 'a) list \<Rightarrow> ('a \<times> 'b \<times> 'c \<times> 'a) list set" where
  "R M q q' pP p = {pP @ p' | p' . p' \<noteq> [] \<and> target q p' = q' \<and> (\<exists> p'' . p = p'@p'')}" 

(* add one completed path of some Preamble of q' to R if a preamble exists *)
definition RP :: "('a,'b,'c) fsm \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> ('a \<times> 'b \<times> 'c \<times> 'a) list \<Rightarrow> ('a \<times> 'b \<times> 'c \<times> 'a) list \<Rightarrow> ('a \<times> ('a,'b,'c) preamble) set \<Rightarrow> ('d,'b,'c) fsm \<Rightarrow> ('a \<times> 'b \<times> 'c \<times> 'a) list set" where
  "RP M q q' pP p PS M' = (if \<exists> P' .  (q',P') \<in> PS then insert (SOME pP' . \<exists> P' .  (q',P') \<in> PS \<and> path P' (initial P') pP' \<and> target (initial P') pP' = q' \<and> p_io pP' \<in> L M') (R M q q' pP p) else (R M q q' pP p))" 



lemma RP_from_R :
  assumes "\<And> q P . (q,P) \<in> PS \<Longrightarrow> is_preamble P M q"
  and     "\<And> q P io x y y' . (q,P) \<in> PS \<Longrightarrow> io@[(x,y)] \<in> L P \<Longrightarrow> io@[(x,y')] \<in> L M' \<Longrightarrow> io@[(x,y')] \<in> L P"
  and     "completely_specified M'"
  and     "inputs M' = inputs M"
shows "(RP M q q' pP p PS M' = R M q q' pP p) 
          \<or> (\<exists> P' pP' . (q',P') \<in> PS \<and> 
                        path P' (initial P') pP' \<and> 
                        target (initial P') pP' = q' \<and> 
                        path M (initial M) pP' \<and> 
                        target (initial M) pP' = q' \<and> 
                        p_io pP' \<in> L M' \<and> 
                        RP M q q' pP p PS M' = 
                        insert pP' (R M q q' pP p))"
proof (rule ccontr)
  assume "\<not> (RP M q q' pP p PS M' = R M q q' pP p \<or> (\<exists> P' pP' . (q',P') \<in> PS \<and> path P' (initial P') pP' \<and> target (initial P') pP' = q' \<and> path M (initial M) pP' \<and> target (initial M) pP' = q' \<and> p_io pP' \<in> L M' \<and> RP M q q' pP p PS M' = insert pP' (R M q q' pP p)))"
  then have "(RP M q q' pP p PS M' \<noteq> R M q q' pP p)"
       and  "\<not> (\<exists> P' pP' . (q',P') \<in> PS \<and> 
                            path P' (initial P') pP' \<and> 
                            target (initial P') pP' = q' \<and> 
                            path M (initial M) pP' \<and> 
                            target (initial M) pP' = q' \<and> 
                            p_io pP' \<in> L M' \<and> 
                            RP M q q' pP p PS M' = insert pP' (R M q q' pP p))"
    by blast+

  let ?p = "SOME pP' . \<exists> P' .  (q',P') \<in> PS \<and> path P' (initial P') pP' \<and> target (initial P') pP' = q' \<and> p_io pP' \<in> L M'"

  have "\<exists> P' .  (q',P') \<in> PS"
    using \<open>(RP M q q' pP p PS M' \<noteq> R M q q' pP p)\<close> unfolding RP_def by auto
  then obtain P' where "(q',P') \<in> PS"
    by auto
  then have "is_preamble P' M q'"
    using assms by blast

  obtain pP' where "path P' (initial P') pP'" and "target (initial P') pP' = q'" and "p_io pP' \<in> L M'"
    using preamble_pass_path[OF \<open>is_preamble P' M q'\<close>  
          assms(2)[OF \<open>(q',P') \<in> PS\<close>] assms(3,4)] 
    by force
  then have "\<exists> pP' . \<exists> P' .  (q',P') \<in> PS \<and> path P' (initial P') pP' \<and> target (initial P') pP' = q' \<and> p_io pP' \<in> L M'"
    using \<open>(q',P') \<in> PS\<close> by blast
  have "\<exists> P' .  (q',P') \<in> PS \<and> path P' (initial P') ?p \<and> target (initial P') ?p = q' \<and> p_io ?p \<in> L M'"
    using someI_ex[OF \<open>\<exists> pP' . \<exists> P' .  (q',P') \<in> PS \<and> path P' (initial P') pP' \<and> target (initial P') pP' = q' \<and> p_io pP' \<in> L M'\<close>] 
    by blast

  then obtain P'' where "(q',P'') \<in> PS" and "path P'' (initial P'') ?p" and "target (initial P'') ?p = q'" and "p_io ?p \<in> L M'"
    by auto
  then have "is_preamble P'' M q'"
    using assms by blast

  
  have "initial P'' = initial M"
    using \<open>is_preamble P'' M q'\<close> unfolding is_preamble_def by auto
  have "path M (initial M) ?p"
    using \<open>is_preamble P'' M q'\<close> unfolding is_preamble_def using submachine_path_initial
    using \<open>path P'' (FSM.initial P'') ?p\<close> by blast
  have "target (initial M) ?p = q'"
    using \<open>target (initial P'') ?p = q'\<close> unfolding \<open>initial P'' = initial M\<close> by assumption

  have "RP M q q' pP p PS M' = insert ?p (R M q q' pP p)"
    using \<open>\<exists> P' .  (q',P') \<in> PS\<close> unfolding RP_def by auto

  then have "(\<exists> P' pP' . (q',P') \<in> PS \<and> 
                          path P' (initial P') pP' \<and> 
                          target (initial P') pP' = q' \<and> 
                          path M (initial M) pP' \<and> 
                          target (initial M) pP' = q' \<and> 
                          p_io pP' \<in> L M' \<and> 
                          RP M q q' pP p PS M' = insert pP' (R M q q' pP p))"
    using \<open>(q',P'') \<in> PS\<close> \<open>path P'' (initial P'') ?p\<close> \<open>target (initial P'') ?p = q'\<close> 
          \<open>path M (initial M) ?p\<close> \<open>target (initial M) ?p = q'\<close> \<open>p_io ?p \<in> L M'\<close> by blast
  then show "False"
    using \<open>\<not> (\<exists> P' pP' . (q',P') \<in> PS \<and> path P' (initial P') pP' \<and> target (initial P') pP' = q' \<and> path M (initial M) pP' \<and> target (initial M) pP' = q' \<and> p_io pP' \<in> L M' \<and> RP M q q' pP p PS M' = insert pP' (R M q q' pP p))\<close>
    by blast
qed


lemma RP_from_R_inserted :
  assumes "\<And> q P . (q,P) \<in> PS \<Longrightarrow> is_preamble P M q"
  and     "\<And> q P io x y y' . (q,P) \<in> PS \<Longrightarrow> io@[(x,y)] \<in> L P \<Longrightarrow> io@[(x,y')] \<in> L M' \<Longrightarrow> io@[(x,y')] \<in> L P"
  and     "completely_specified M'"
  and     "inputs M' = inputs M"
  and     "pP' \<in> RP M q q' pP p PS M'"
  and     "pP' \<notin> R M q q' pP p"
obtains P' where  "(q',P') \<in> PS" 
                  "path P' (initial P') pP'" 
                  "target (initial P') pP' = q'" 
                  "path M (initial M) pP'"
                  "target (initial M) pP' = q'"
                  "p_io pP' \<in> L M'"
                  "RP M q q' pP p PS M' = insert pP' (R M q q' pP p)"
proof -
  have "(RP M q q' pP p PS M' \<noteq> R M q q' pP p)"
    using assms(5,6) by blast

  then have "(\<exists>P' pP'.
              (q', P') \<in> PS \<and>
              path P' (FSM.initial P') pP' \<and>
              target (FSM.initial P') pP' = q' \<and>
              path M (FSM.initial M) pP' \<and> target (FSM.initial M) pP' = q' \<and> p_io pP' \<in> L M' \<and> RP M q q' pP p PS M' = insert pP' (R M q q' pP p))"
        using RP_from_R[OF assms(1-4), of PS _ _ q q' pP p] by force
  then obtain P' pP'' where "(q', P') \<in> PS"
                            "path P' (FSM.initial P') pP''"
                            "target (FSM.initial P') pP'' = q'"
                            "path M (FSM.initial M) pP''" 
                            "target (FSM.initial M) pP'' = q'" 
                            "p_io pP'' \<in> L M'"
                            "RP M q q' pP p PS M' = insert pP'' (R M q q' pP p)"
    by blast

  moreover have "pP'' = pP'" using \<open>RP M q q' pP p PS M' = insert pP'' (R M q q' pP p)\<close> assms(5,6) by simp
  ultimately show ?thesis using that[of P'] unfolding \<open>pP'' = pP'\<close> by blast
qed


lemma finite_R :
  assumes "path M q p"
  shows "finite (R M q q' pP p)"
proof -
  have "\<And> p' . p' \<in> (R M q q' pP p) \<Longrightarrow> p' \<in> set (prefixes (pP@p))"
  proof -
    fix p' assume "p' \<in> (R M q q' pP p)"
    then obtain p'' where "p' = pP @ p''"
      unfolding R_def by blast
    then obtain p''' where "p = p'' @ p'''"
      using \<open>p' \<in> (R M q q' pP p)\<close> unfolding R_def by blast
    
    show "p' \<in> set (prefixes (pP@p))"
      unfolding prefixes_set \<open>p' = pP @ p''\<close> \<open>p = p'' @ p'''\<close> by auto
  qed
  then have "(R M q q' pP p) \<subseteq> set (prefixes (pP@p))"
    by blast
  then show ?thesis
    using rev_finite_subset by auto 
qed

lemma finite_RP :
  assumes "path M q p"
  and     "\<And> q P . (q,P) \<in> PS \<Longrightarrow> is_preamble P M q"
  and     "\<And> q P io x y y' . (q,P) \<in> PS \<Longrightarrow> io@[(x,y)] \<in> L P \<Longrightarrow> io@[(x,y')] \<in> L M' \<Longrightarrow> io@[(x,y')] \<in> L P"
  and     "completely_specified M'"
  and     "inputs M' = inputs M"
shows "finite (RP M q q' pP p PS M')"
  using finite_R[OF assms(1), of q' pP ]
        RP_from_R[OF assms(2,3,4,5), of PS _ _ q q' pP p] by force
  

lemma R_component_ob :
  assumes "pR' \<in> R M q q' pP p"
  obtains pR where "pR' = pP@pR"
  using assms unfolding R_def by blast


lemma R_component :
  assumes "(pP@pR) \<in> R M q q' pP p" 
shows "pR = take (length pR) p"
and   "length pR \<le> length p"
and   "t_target (p ! (length pR - 1)) = q'"
and   "pR \<noteq> []"
proof -
  let ?R = "R M q q' p"

  have "pR \<noteq> []" and "target q pR = q'" and "\<exists> p'' . p = pR@p''"
    using \<open>pP@pR \<in> R M q q' pP p\<close> unfolding R_def by blast+
  then obtain pR' where "p = pR@pR'"
    by blast

  then show "pR = take (length pR) p" and "length pR \<le> length p"
    by auto
  
  show "t_target (p ! (length pR - 1)) = q'"
    using \<open>pR \<noteq> []\<close> \<open>target q pR = q'\<close> unfolding target.simps visited_states.simps
    by (metis (no_types, lifting) Suc_diff_1 \<open>pR = take (length pR) p\<close> 
          append_butlast_last_id last.simps last_map length_butlast lessI list.map_disc_iff 
          not_gr_zero nth_append_length nth_take take_eq_Nil) 

  show "pR \<noteq> []" 
    using \<open>pR \<noteq> []\<close> 
    by assumption
qed


lemma R_component_observable :
  assumes "pP@pR \<in> R M (target (initial M) pP) q' pP p"
  and     "observable M"
  and     "path M (initial M) pP"
  and     "path M (target (initial M) pP) p"
shows "io_targets M (p_io pP @ p_io pR) (initial M) = {target (target (initial M) pP) (take (length pR) p)}"
proof -
  have "pR = take (length pR) p"
  and  "length pR \<le> length p"
  and  "t_target (p ! (length pR - 1)) = q'"
    using R_component[OF assms(1)] by blast+

  let ?q = "(target (initial M) pP)"
  have "path M ?q (take (length pR) p)"
    using assms(4) by (simp add: path_prefix_take) 
  have "p_io (take (length pR) p) = p_io pR"
    using \<open>pR = take (length pR) p\<close> by auto
    

  have *:"path M (initial M) (pP @ (take (length pR) p))"
    using \<open>path M (initial M) pP\<close> \<open>path M ?q (take (length pR) p)\<close> by auto
  have **:"p_io (pP @ (take (length pR) p)) = (p_io pP @ p_io pR)"
    using \<open>p_io (take (length pR) p) = p_io pR\<close> by auto
  
  have "target (initial M) (pP @ (take (length pR) p)) = target ?q (take (length pR) p)"
    by auto 
  then have "target ?q (take (length pR) p) \<in> io_targets M (p_io pP @ p_io pR) (initial M)"
    unfolding io_targets.simps using * **
    by (metis (mono_tags, lifting) mem_Collect_eq) 

  show "io_targets M (p_io pP @ p_io pR) (initial M) = {target ?q (take (length pR) p)}"
    using observable_io_targets[OF \<open>observable M\<close> language_state_containment[OF * **]]
    by (metis (no_types) \<open>target (target (FSM.initial M) pP) (take (length pR) p) \<in> io_targets M (p_io pP @ p_io pR) (FSM.initial M)\<close> singleton_iff)
qed


lemma R_count :                        
  assumes "minimal_sequence_to_failure_extending_preamble_path M M' PS pP io"
  and     "observable M"
  and     "observable M'"
  and     "\<And> q P. (q, P) \<in> PS \<Longrightarrow> is_preamble P M q"
  and     "path M (target (initial M) pP) p"
  and     "butlast io = p_io p @ ioX"
shows "card (\<Union> (image (\<lambda> pR . io_targets M' (p_io pR) (initial M')) (R M (target (initial M) pP) q' pP p))) = card (R M (target (initial M) pP) q' pP p)"
  (is "card ?Tgts = card ?R")
and   "\<And> pR . pR \<in> (R M (target (initial M) pP) q' pP p) \<Longrightarrow> \<exists> q . io_targets M' (p_io pR) (initial M') = {q}"
and   "\<And> pR1 pR2 . pR1 \<in> (R M (target (initial M) pP) q' pP p) \<Longrightarrow> 
                    pR2 \<in> (R M (target (initial M) pP) q' pP p) \<Longrightarrow> 
                    pR1 \<noteq> pR2 \<Longrightarrow> 
                    io_targets M' (p_io pR1) (initial M') \<inter> io_targets M' (p_io pR2) (initial M') = {}"
proof -

  have "sequence_to_failure_extending_preamble_path M M' PS pP io"
  and  "\<And> p' io' . sequence_to_failure_extending_preamble_path M M' PS p' io' \<Longrightarrow> length io \<le> length io'"
    using \<open>minimal_sequence_to_failure_extending_preamble_path M M' PS pP io\<close>
    unfolding minimal_sequence_to_failure_extending_preamble_path_def   
    by blast+

  obtain q P where "(q,P) \<in> PS"
              and  "path P (initial P) pP"
              and  "target (initial P) pP = q"
              and  "((p_io pP) @ butlast io) \<in> L M" 
              and  "((p_io pP) @ io) \<notin> L M"
              and  "((p_io pP) @ io) \<in> L M'"

    using \<open>sequence_to_failure_extending_preamble_path M M' PS pP io\<close>
    unfolding sequence_to_failure_extending_preamble_path_def  
    by blast

  have "is_preamble P M q"
    using \<open>(q,P) \<in> PS\<close> \<open>\<And> q P. (q, P) \<in> PS \<Longrightarrow> is_preamble P M q\<close> by blast
  then have "q \<in> states M"
    unfolding is_preamble_def
    by (metis \<open>path P (FSM.initial P) pP\<close> \<open>target (FSM.initial P) pP = q\<close> path_target_is_state submachine_path) 

  have "initial P = initial M"
    using \<open>is_preamble P M q\<close> unfolding is_preamble_def by auto
  have "path M (initial M) pP"
    using \<open>is_preamble P M q\<close> unfolding is_preamble_def using submachine_path_initial
    using \<open>path P (FSM.initial P) pP\<close> by blast
  have "target (initial M) pP = q"
    using \<open>target (initial P) pP = q\<close> unfolding \<open>initial P = initial M\<close> by assumption

  then have "path M q p"
    using \<open>path M (target (initial M) pP) p\<close> by auto

  have "io \<noteq> []"
    using \<open>((p_io pP) @ butlast io) \<in> L M\<close> \<open>((p_io pP) @ io) \<notin> L M\<close> by auto


  (* get the full path along (butlast io) in M, of which p is a (possibly proper) prefix *)

  obtain pX where "path M (target (initial M) pP) (p@pX)" and "p_io (p@pX) = butlast io"
  proof -
    have "p_io pP @ p_io p @ ioX \<in> L M"
      using \<open>((p_io pP) @ butlast io) \<in> L M\<close> 
      unfolding \<open>butlast io = p_io p @ ioX\<close> 
      by assumption

    obtain p1 p23 where "path M (FSM.initial M) p1" 
                    and "path M (target (FSM.initial M) p1) p23"
                    and "p_io p1 = p_io pP" 
                    and "p_io p23 = p_io p @ ioX"
      using language_state_split[OF \<open>p_io pP @ p_io p @ ioX \<in> L M\<close>] 
      by blast

    have "p1 = pP"
      using observable_path_unique[OF \<open>observable M\<close> \<open>path M (FSM.initial M) p1\<close> \<open>path M (FSM.initial M) pP\<close> \<open>p_io p1 = p_io pP\<close>] 
      by assumption
    then have "path M (target (FSM.initial M) pP) p23"
      using \<open>path M (target (FSM.initial M) p1) p23\<close> by auto
    then have "p_io p @ ioX \<in> LS M (target (initial M) pP)"
      using \<open>p_io p23 = p_io p @ ioX\<close> language_state_containment by auto

    obtain p2 p3 where "path M (target (FSM.initial M) pP) p2" 
                   and "path M (target (target (FSM.initial M) pP) p2) p3" 
                   and "p_io p2 = p_io p" 
                   and "p_io p3 = ioX"
      using language_state_split[OF \<open>p_io p @ ioX \<in> LS M (target (initial M) pP)\<close>] 
      by blast

    have "p2 = p"
      using observable_path_unique[OF \<open>observable M\<close> \<open>path M (target (FSM.initial M) pP) p2\<close> \<open>path M (target (FSM.initial M) pP) p\<close> \<open>p_io p2 = p_io p\<close>] 
      by assumption
    then have "path M (target (FSM.initial M) pP) (p@p3)"
      using \<open>path M (target (FSM.initial M) pP) p\<close> \<open>path M (target (target (FSM.initial M) pP) p2) p3\<close> 
      by auto
    moreover have "p_io (p@p3) = butlast io"
      unfolding \<open>butlast io = p_io p @ ioX\<close> using \<open>p_io p3 = ioX\<close> 
      by auto
    ultimately show ?thesis 
      using that[of p3] 
      by simp
  qed


  (* finiteness properties *)

  have "finite ?R"
    using finite_R[OF \<open>path M (target (initial M) pP) p\<close>]
    by assumption
  moreover have "\<And> pR . pR \<in> ?R \<Longrightarrow> finite (io_targets M' (p_io pR) (initial M'))"
    using io_targets_finite by metis
  ultimately have "finite ?Tgts"
    by blast


  (* path properties *)
  
  obtain pP' p' where "path M' (FSM.initial M') pP'" 
                and   "path M' (target (FSM.initial M') pP') p'" 
                and   "p_io pP' = p_io pP" 
                and   "p_io p' = io"
    using language_state_split[OF \<open>((p_io pP) @ io) \<in> L M'\<close>]
    by blast

  have "length p \<le> length (butlast io)"
    using \<open>butlast io = p_io p @ ioX\<close> by auto
  moreover have "length (butlast io) < length io"
    using \<open>io \<noteq> []\<close> by auto
  ultimately have "length p < length p'"
    unfolding \<open>p_io p' = io\<close> length_map[of "(\<lambda> t . (t_input t, t_output t))", symmetric] by simp


  let ?q = "(target (FSM.initial M') pP')"

  have "\<And> pR . pP@pR \<in> ?R \<Longrightarrow> path M' ?q (take (length pR) p') \<and> p_io (take (length pR) p') = p_io pR"
  proof -
    fix pR assume "pP@pR \<in> ?R"
    then have  "pR = take (length pR) p \<and> length pR \<le> length p"
      using R_component(1,2) by metis
    then have "p_io pR = take (length pR) (butlast io)"
      unfolding \<open>butlast io = p_io p @ ioX\<close>
      by (metis (no_types, lifting) length_map take_le take_map)
    moreover have "p_io (take (length pR) p') = take (length pR) io"
      by (metis (full_types) \<open>p_io p' = io\<close> take_map)
    moreover have "take (length pR) (butlast io) = take (length pR) io"
      by (meson \<open>length (butlast io) < length io\<close> \<open>length p \<le> length (butlast io)\<close> 
            \<open>pR = take (length pR) p \<and> length pR \<le> length p\<close> dual_order.strict_trans2 take_butlast)
    ultimately have "p_io (take (length pR) p') = p_io pR"
      by simp 
    moreover have "path M' ?q (take (length pR) p')"
      using \<open>path M' (target (FSM.initial M') pP') p'\<close>
      by (simp add: path_prefix_take) 
    ultimately show "path M' ?q (take (length pR) p') \<and> p_io (take (length pR) p') = p_io pR"
      by blast
  qed


  (* every element in R reaches exactly one state in M' *)

  have singleton_prop': "\<And> pR . pP@pR \<in> ?R \<Longrightarrow> io_targets M' (p_io (pP@pR)) (initial M') = {target ?q (take (length pR) p')}"
  proof -
    fix pR assume "pP@pR \<in> ?R"
    then have "path M' ?q (take (length pR) p')" and "p_io (take (length pR) p') = p_io pR"
      using \<open>\<And> pR . pP@pR \<in> ?R \<Longrightarrow> path M' ?q (take (length pR) p') \<and> p_io (take (length pR) p') = p_io pR\<close> by blast+

    have *:"path M' (initial M') (pP' @ (take (length pR) p'))"
      using \<open>path M' (initial M') pP'\<close> \<open>path M' ?q (take (length pR) p')\<close> by auto
    have **:"p_io (pP' @ (take (length pR) p')) = (p_io (pP@pR))"
      using \<open>p_io pP' = p_io pP\<close> \<open>p_io (take (length pR) p') = p_io pR\<close> by auto
    
    have "target (initial M') (pP' @ (take (length pR) p')) = target ?q (take (length pR) p')"
      by auto 
    then have "target ?q (take (length pR) p') \<in> io_targets M' (p_io (pP@pR)) (initial M')"
      unfolding io_targets.simps using * **
      by (metis (mono_tags, lifting) mem_Collect_eq) 

    show "io_targets M' (p_io (pP@pR)) (initial M') = {target ?q (take (length pR) p')}"
      using observable_io_targets[OF \<open>observable M'\<close> language_state_containment[OF * **]]
      by (metis (no_types) \<open>target (target (FSM.initial M') pP') (take (length pR) p') \<in> io_targets M' (p_io (pP@pR)) (FSM.initial M')\<close> singleton_iff)
  qed

  have singleton_prop: "\<And> pR . pR \<in> ?R \<Longrightarrow> io_targets M' (p_io pR) (initial M') = {target ?q (take (length pR - length pP) p')}"
  proof -
    fix pR assume "pR \<in> ?R"
    then obtain pR' where "pR = pP@pR'"
      using R_component_ob[of _ M "(target (FSM.initial M) pP)" q' pP p] by blast
    have **: "(length (pP @ pR') - length pP) = length pR'"
      by auto

    show "io_targets M' (p_io pR) (initial M') = {target ?q (take (length pR - length pP) p')}"
      using singleton_prop'[of pR'] \<open>pR \<in> ?R\<close> unfolding \<open>pR = pP@pR'\<close> ** by blast
  qed
  then show "\<And> pR . pR \<in> ?R \<Longrightarrow> \<exists> q . io_targets M' (p_io pR) (initial M') = {q}"
    by blast

  (* distinct elements in R reach distinct states in M' *)
  have pairwise_dist_prop': "\<And> pR1 pR2 . pP@pR1 \<in> ?R \<Longrightarrow> pP@pR2 \<in> ?R \<Longrightarrow> pR1 \<noteq> pR2 \<Longrightarrow> io_targets M' (p_io (pP@pR1)) (initial M') \<inter> io_targets M' (p_io (pP@pR2)) (initial M') = {}"
  proof -
    
    have diff_prop: "\<And> pR1 pR2 . pP@pR1 \<in> ?R \<Longrightarrow> pP@pR2 \<in> ?R \<Longrightarrow> length pR1 < length pR2 \<Longrightarrow> io_targets M' (p_io (pP@pR1)) (initial M') \<inter> io_targets M' (p_io (pP@pR2)) (initial M') = {}"
    proof -
      fix pR1 pR2 assume "pP@pR1 \<in> ?R" and "pP@pR2 \<in> ?R" and "length pR1 < length pR2"

      let ?i = "length pR1 - 1"
      let ?j = "length pR2 - 1"

      have "pR1 = take (length pR1) p" and \<open>length pR1 \<le> length p\<close> and "t_target (p ! ?i) = q'"
        using R_component[OF \<open>pP@pR1 \<in> ?R\<close>]
        by simp+
      have "length pR1 \<noteq> 0"
        using \<open>pP@pR1 \<in> ?R\<close> unfolding R_def
        by simp 
      then have "?i < ?j" 
        using \<open>length pR1 < length pR2\<close>
        by (simp add: less_diff_conv) 


      have "pR2 = take (length pR2) p" and \<open>length pR2 \<le> length p\<close> and "t_target (p ! ?j) = q'"
        using R_component[OF \<open>pP@pR2 \<in> ?R\<close>]
        by simp+
      then have "?j < length (butlast io)"
        using \<open>length p \<le> length (butlast io)\<close> \<open>length pR1 < length pR2\<close> by linarith


      have "?q \<in> io_targets M' (p_io pP) (FSM.initial M')"
        unfolding \<open>p_io pP' = p_io pP\<close>[symmetric] io_targets.simps
        using \<open>path M' (initial M') pP'\<close> by auto

      have "t_target (p ! ?i) = t_target (p ! ?j)"
        using \<open>t_target (p ! ?i) = q'\<close> \<open>t_target (p ! ?j) = q'\<close> by simp
      moreover have "(p @ pX) ! ?i = p ! ?i"
        by (meson \<open>length pR1 < length pR2\<close> \<open>length pR2 \<le> length p\<close> less_imp_diff_less less_le_trans nth_append)
      moreover have "(p @ pX) ! ?j = p ! ?j"
        by (metis (no_types) \<open>length pR1 < length pR2\<close> \<open>pR2 = take (length pR2) p\<close> diff_less less_imp_diff_less less_nat_zero_code less_numeral_extra(1) not_le_imp_less not_less_iff_gr_or_eq nth_append take_all)
      ultimately have "t_target (p' ! ?i) \<noteq> t_target (p' ! ?j)"
        using minimal_sequence_to_failure_extending_preamble_no_repetitions_along_path[OF assms(1,2) \<open>path M (target (initial M) pP) (p@pX)\<close> \<open>p_io (p @ pX) = butlast io\<close> \<open>?q \<in> io_targets M' (p_io pP) (FSM.initial M')\<close> \<open>path M' (target (FSM.initial M') pP') p'\<close> \<open>p_io p' = io\<close> \<open>?i < ?j\<close> \<open>?j < length (butlast io)\<close> assms(4)]
        by auto

      have t1: "io_targets M' (p_io (pP@pR1)) (initial M') = {t_target (p' ! ?i)}"
      proof -
        have "(p' ! ?i) = last (take (length pR1) p')"
          using \<open>length pR1 \<le> length p\<close> \<open>length p < length p'\<close>
          by (metis Suc_diff_1 \<open>length pR1 \<noteq> 0\<close> dual_order.strict_trans2 length_0_conv length_greater_0_conv less_imp_diff_less take_last_index)
        then have *: "target (target (FSM.initial M') pP') (take (length pR1) p') = t_target (p' ! ?i)"
          unfolding target.simps visited_states.simps
          by (metis (no_types, lifting) \<open>length p < length p'\<close> \<open>length pR1 \<noteq> 0\<close> gr_implies_not_zero last.simps last_map length_0_conv map_is_Nil_conv take_eq_Nil) 
        have **: "(length (pP @ pR1) - length pP) = length pR1"
          by auto
        show ?thesis
          using singleton_prop[OF \<open>pP@pR1 \<in> ?R\<close>]
          unfolding * ** by assumption
      qed

      have t2: "io_targets M' (p_io (pP@pR2)) (initial M') = {t_target (p' ! ?j)}"
      proof -
        have "(p' ! ?j) = last (take (length pR2) p')"
          using \<open>length pR2 \<le> length p\<close> \<open>length p < length p'\<close>
          by (metis Suc_diff_1 \<open>length pR1 - 1 < length pR2 - 1\<close> le_less_trans less_imp_diff_less 
                linorder_neqE_nat not_less_zero take_last_index zero_less_diff)
        then have *: "target (target (FSM.initial M') pP') (take (length pR2) p') = t_target (p' ! ?j)"
          unfolding target.simps visited_states.simps
          by (metis (no_types, lifting) Nil_is_map_conv \<open>length p < length p'\<close> \<open>length pR1 < length pR2\<close> 
                last.simps last_map list.size(3) not_less_zero take_eq_Nil)
        have **: "(length (pP @ pR2) - length pP) = length pR2"
          by auto  
        show ?thesis
          using singleton_prop'[OF \<open>pP@pR2 \<in> ?R\<close>]
          unfolding * ** by assumption
      qed

      show "io_targets M' (p_io (pP@pR1)) (initial M') \<inter> io_targets M' (p_io (pP@pR2)) (initial M') = {}"
        using \<open>t_target (p' ! ?i) \<noteq> t_target (p' ! ?j)\<close>
        unfolding t1 t2 by simp
    qed


    fix pR1 pR2 assume "pP@pR1 \<in> ?R" and "pP@pR2 \<in> ?R" and "pR1 \<noteq> pR2"
    then have "length pR1 \<noteq> length pR2"
      unfolding R_def
      by auto 

    then consider (a) "length pR1 < length pR2" | (b) "length pR2 < length pR1"
      using nat_neq_iff by blast 
    then show "io_targets M' (p_io (pP@pR1)) (initial M') \<inter> io_targets M' (p_io (pP@pR2)) (initial M') = {}"
    proof cases
      case a
      show ?thesis using diff_prop[OF \<open>pP@pR1 \<in> ?R\<close> \<open>pP@pR2 \<in> ?R\<close> a] by blast
    next
      case b
      show ?thesis using diff_prop[OF \<open>pP@pR2 \<in> ?R\<close> \<open>pP@pR1 \<in> ?R\<close> b] by blast
    qed
  qed

  then show pairwise_dist_prop: "\<And> pR1 pR2 . pR1 \<in> ?R \<Longrightarrow> pR2 \<in> ?R \<Longrightarrow> pR1 \<noteq> pR2 \<Longrightarrow> io_targets M' (p_io pR1) (initial M') \<inter> io_targets M' (p_io pR2) (initial M') = {}" 
    using R_component_ob
    by (metis (no_types, lifting)) 


  (* combining results *)

  let ?f = "(\<lambda> pR . io_targets M' (p_io pR) (initial M'))"
  
  have p1: "(\<And>S1 S2. S1 \<in> ?R \<Longrightarrow> S2 \<in> ?R \<Longrightarrow> S1 = S2 \<or> ?f S1 \<inter> ?f S2 = {})"
    using pairwise_dist_prop by blast
  have p2: "(\<And>S. S \<in> R M (target (FSM.initial M) pP) q' pP p \<Longrightarrow> io_targets M' (p_io S) (FSM.initial M') \<noteq> {})"
    using singleton_prop by blast
  have c1: "card (R M (target (FSM.initial M) pP) q' pP p) = card ((\<lambda>S. io_targets M' (p_io S) (FSM.initial M')) ` R M (target (FSM.initial M) pP) q' pP p)"
    using card_union_of_distinct[of ?R, OF p1 \<open>finite ?R\<close> p2] by force

  have p3: "(\<And>S. S \<in> (\<lambda>S. io_targets M' (p_io S) (FSM.initial M')) ` R M (target (FSM.initial M) pP) q' pP p \<Longrightarrow> \<exists>t. S = {t})"
    using singleton_prop by blast
  have c2:"card ((\<lambda>S. io_targets M' (p_io S) (FSM.initial M')) ` R M (target (FSM.initial M) pP) q' pP p) = card (\<Union>S\<in>R M (target (FSM.initial M) pP) q' pP p. io_targets M' (p_io S) (FSM.initial M'))"
    using card_union_of_singletons[of "((\<lambda>S. io_targets M' (p_io S) (FSM.initial M')) ` R M (target (FSM.initial M) pP) q' pP p)", OF p3] by force

    
  show "card ?Tgts = card ?R"
    unfolding c1 c2 by blast
qed


lemma R_update :
  "R M q q' pP (p@[t]) = (if (target q (p@[t]) = q')
                          then insert (pP@p@[t]) (R M q q' pP p)
                          else (R M q q' pP p))"
  (is "?R1 = ?R2")
proof (cases "(target q (p@[t]) = q')")
  case True
  then have *: "?R2 = insert (pP@p@[t]) (R M q q' pP p)"
    by auto
  
  have "\<And> p' . p' \<in> R M q q' pP (p@[t]) \<Longrightarrow> p' \<in> insert (pP@p@[t]) (R M q q' pP p)"
  proof -
    fix p' assume "p' \<in> R M q q' pP (p@[t])"

    obtain p'' where "p' = pP @ p''"
      using R_component_ob[OF \<open>p' \<in> R M q q' pP (p@[t])\<close>] by blast

    obtain p''' where "p'' \<noteq> []" and "target q p'' = q'" and "p @ [t] = p'' @ p'''"
      using \<open>p' \<in> R M q q' pP (p@[t])\<close> unfolding R_def \<open>p' = pP @ p''\<close>
      by auto 

    show "p' \<in> insert (pP@p@[t]) (R M q q' pP p)"
    proof (cases p''' rule: rev_cases)
      case Nil
      then have "p' = pP@(p@[t])" using \<open>p' = pP @ p''\<close> \<open>p @ [t] = p'' @ p'''\<close> by auto
      then show ?thesis by blast
    next
      case (snoc p'''' t')
      then have "p = p'' @ p''''" using \<open>p @ [t] = p'' @ p'''\<close> by auto
      then show ?thesis 
        unfolding R_def using \<open>p'' \<noteq> []\<close> \<open>target q p'' = q'\<close>
        by (simp add: \<open>p' = pP @ p''\<close>) 
    qed
  qed
  moreover have "\<And> p' . p' \<in> insert (pP@p@[t]) (R M q q' pP p) \<Longrightarrow> p' \<in> R M q q' pP (p@[t])"
  proof -
    fix p' assume "p' \<in> insert (pP@p@[t]) (R M q q' pP p)"
    then consider (a) "p' = (pP@p@[t])" | (b) "p' \<in> (R M q q' pP p)" by blast
    then show "p' \<in> R M q q' pP (p@[t])" proof cases
      case a
      then show ?thesis using True unfolding R_def
        by simp 
    next
      case b
      then show ?thesis unfolding R_def
        using append.assoc by blast 
    qed 
  qed
  ultimately show ?thesis 
    unfolding * by blast
next
  case False
  then have *: "?R2 = (R M q q' pP p)"
    by auto

  have "\<And> p' . p' \<in> R M q q' pP (p@[t]) \<Longrightarrow> p' \<in> (R M q q' pP p)"
  proof -
    fix p' assume "p' \<in> R M q q' pP (p@[t])"

    obtain p'' where "p' = pP @ p''"
      using R_component_ob[OF \<open>p' \<in> R M q q' pP (p@[t])\<close>] by blast

    obtain p''' where "p'' \<noteq> []" and "target q p'' = q'" and "p @ [t] = p'' @ p'''"
      using \<open>p' \<in> R M q q' pP (p@[t])\<close> unfolding R_def \<open>p' = pP @ p''\<close> by blast

    show "p' \<in> (R M q q' pP p)"
    proof (cases p''' rule: rev_cases)
      case Nil
      then have "p' = pP@(p@[t])" using \<open>p' = pP @ p''\<close> \<open>p @ [t] = p'' @ p'''\<close> by auto
      then show ?thesis
        using False \<open>p @ [t] = p'' @ p'''\<close> \<open>target q p'' = q'\<close> local.Nil by auto
    next
      case (snoc p'''' t')
      then have "p = p'' @ p''''" using \<open>p @ [t] = p'' @ p'''\<close> by auto
      then show ?thesis 
        unfolding R_def using \<open>p'' \<noteq> []\<close> \<open>target q p'' = q'\<close>
        by (simp add: \<open>p' = pP @ p''\<close>) 
    qed
  qed
  moreover have "\<And> p' . p' \<in> (R M q q' pP p) \<Longrightarrow> p' \<in> R M q q' pP (p@[t])"
  proof -
    fix p' assume "p' \<in> (R M q q' pP p)"
    then show "p' \<in> R M q q' pP (p@[t])" unfolding R_def
      using append.assoc by blast 
  qed
  ultimately show ?thesis 
    unfolding * by blast
qed


lemma R_union_card_is_suffix_length :
  assumes "path M (initial M) pP"
  and     "path M (target (initial M) pP) p"
shows "(\<Sum> q \<in> states M . card (R M (target (initial M) pP) q pP p)) = length p"
using assms(2) proof (induction p rule: rev_induct)
  case Nil
  have "\<And> q' . R M (target (initial M) pP) q' pP [] = {}"
    unfolding R_def by auto 
  then show ?case
    by simp 
next
  case (snoc t p)
  then have "path M (target (initial M) pP) p"
    by auto

  let ?q = "(target (initial M) pP)"
  let ?q' = "target ?q (p @ [t])"

  have "\<And> q . q \<noteq> ?q' \<Longrightarrow> R M ?q q pP (p@[t]) = R M ?q q pP p"
    using R_update[of M ?q _ pP p t] by force
  then have *: "(\<Sum> q \<in> states M - {?q'} . card (R M (target (initial M) pP) q pP (p@[t]))) 
                  = (\<Sum> q \<in> states M - {?q'} . card (R M (target (initial M) pP) q pP p))"
    by force



  have "R M ?q ?q' pP (p@[t]) = insert (pP@p@[t]) (R M ?q ?q' pP p)"
    using R_update[of M ?q ?q' pP p t] by force 
  moreover have "(pP@p@[t]) \<notin> (R M ?q ?q' pP p)"
    unfolding R_def by simp 
  ultimately have **: "card (R M (target (initial M) pP) ?q' pP (p@[t])) = Suc (card (R M (target (initial M) pP) ?q' pP p))"
    using finite_R[OF \<open>path M (target (initial M) pP) (p@[t])\<close>] finite_R[OF \<open>path M (target (initial M) pP) p\<close>]
    by simp


  have "?q' \<in> states M"
    using path_target_is_state[OF \<open>path M (target (FSM.initial M) pP) (p @ [t])\<close>] by assumption
  then have ***: "(\<Sum> q \<in> states M . card (R M (target (initial M) pP) q pP (p@[t]))) 
                    = (\<Sum> q \<in> states M - {?q'} . card (R M (target (initial M) pP) q pP (p@[t]))) + (card (R M (target (initial M) pP) ?q' pP (p@[t])))"
       and ****: "(\<Sum> q \<in> states M . card (R M (target (initial M) pP) q pP p)) 
                    = (\<Sum> q \<in> states M - {?q'} . card (R M (target (initial M) pP) q pP p)) + (card (R M (target (initial M) pP) ?q' pP p))"
    by (metis (no_types, lifting) Diff_insert_absorb add.commute finite_Diff fsm_states_finite mk_disjoint_insert sum.insert)+

  have "(\<Sum> q \<in> states M . card (R M (target (initial M) pP) q pP (p@[t]))) = Suc (\<Sum> q \<in> states M . card (R M (target (initial M) pP) q pP p))"
    unfolding **** *** ** * by simp

  then show ?case
    unfolding snoc.IH[OF \<open>path M (target (initial M) pP) p\<close>] by auto
qed



lemma RP_count :                        
  assumes "minimal_sequence_to_failure_extending_preamble_path M M' PS pP io"
  and     "observable M"
  and     "observable M'"
  and     "\<And> q P. (q, P) \<in> PS \<Longrightarrow> is_preamble P M q"
  and     "path M (target (initial M) pP) p"
  and     "butlast io = p_io p @ ioX"
  and     "\<And> q P io x y y' . (q,P) \<in> PS \<Longrightarrow> io@[(x,y)] \<in> L P \<Longrightarrow> io@[(x,y')] \<in> L M' \<Longrightarrow> io@[(x,y')] \<in> L P"
  and     "completely_specified M'"
  and     "inputs M' = inputs M"
shows "card (\<Union> (image (\<lambda> pR . io_targets M' (p_io pR) (initial M')) (RP M (target (initial M) pP) q' pP p PS M'))) 
        = card (RP M (target (initial M) pP) q' pP p PS M')"
  (is "card ?Tgts = card ?RP")
and "\<And> pR . pR \<in> (RP M (target (initial M) pP) q' pP p PS M') \<Longrightarrow> \<exists> q . io_targets M' (p_io pR) (initial M') = {q}"
and "\<And> pR1 pR2 . pR1 \<in> (RP M (target (initial M) pP) q' pP p PS M') \<Longrightarrow> pR2 \<in> (RP M (target (initial M) pP) q' pP p PS M') \<Longrightarrow> pR1 \<noteq> pR2 \<Longrightarrow> io_targets M' (p_io pR1) (initial M') \<inter> io_targets M' (p_io pR2) (initial M') = {}"
proof -
  let ?P1 = "card (\<Union> (image (\<lambda> pR . io_targets M' (p_io pR) (initial M')) (RP M (target (initial M) pP) q' pP p PS M'))) = card (RP M (target (initial M) pP) q' pP p PS M')"
  let ?P2 = "\<forall> pR . pR \<in> (RP M (target (initial M) pP) q' pP p PS M') \<longrightarrow> (\<exists> q . io_targets M' (p_io pR) (initial M') = {q})"
  let ?P3 = "\<forall> pR1 pR2 . pR1 \<in> (RP M (target (initial M) pP) q' pP p PS M') \<longrightarrow> pR2 \<in> (RP M (target (initial M) pP) q' pP p PS M') \<longrightarrow> pR1 \<noteq> pR2 \<longrightarrow> io_targets M' (p_io pR1) (initial M') \<inter> io_targets M' (p_io pR2) (initial M') = {}"
  let ?combined_goals = "?P1 \<and> ?P2 \<and> ?P3"
    
  let ?q = "(target (initial M) pP)"
  let ?R = "R M ?q q' pP p"

  consider (a) "(?RP = ?R)" |
           (b) "(\<exists> P' pP' . (q',P') \<in> PS \<and> 
                            path P' (initial P') pP' \<and> 
                            target (initial P') pP' = q' \<and> 
                            path M (initial M) pP' \<and> 
                            target (initial M) pP' = q' \<and> 
                            p_io pP' \<in> L M' \<and> 
                            ?RP = insert pP' ?R)"
    using RP_from_R[OF assms(4,7,8,9), of PS _ _ ?q q' pP p] by force

  then have ?combined_goals proof cases
    case a
    show ?thesis unfolding a using R_count[OF assms(1-6)] by blast
  next
    case b
    

    (* properties from R_count *)

    have "sequence_to_failure_extending_preamble_path M M' PS pP io"
    and  "\<And> p' io' . sequence_to_failure_extending_preamble_path M M' PS p' io' \<Longrightarrow> length io \<le> length io'"
      using \<open>minimal_sequence_to_failure_extending_preamble_path M M' PS pP io\<close>
      unfolding minimal_sequence_to_failure_extending_preamble_path_def   
      by blast+
  
    obtain q P where "(q,P) \<in> PS"
                and  "path P (initial P) pP"
                and  "target (initial P) pP = q"
                and  "((p_io pP) @ butlast io) \<in> L M" 
                and  "((p_io pP) @ io) \<notin> L M"
                and  "((p_io pP) @ io) \<in> L M'"
  
      using \<open>sequence_to_failure_extending_preamble_path M M' PS pP io\<close>
      unfolding sequence_to_failure_extending_preamble_path_def  
      by blast
  
    have "is_preamble P M q"
      using \<open>(q,P) \<in> PS\<close> \<open>\<And> q P. (q, P) \<in> PS \<Longrightarrow> is_preamble P M q\<close> by blast
    then have "q \<in> states M"
      unfolding is_preamble_def
      by (metis \<open>path P (FSM.initial P) pP\<close> \<open>target (FSM.initial P) pP = q\<close> path_target_is_state submachine_path) 
  
    have "initial P = initial M"
      using \<open>is_preamble P M q\<close> unfolding is_preamble_def by auto
    have "path M (initial M) pP"
      using \<open>is_preamble P M q\<close> unfolding is_preamble_def using submachine_path_initial
      using \<open>path P (FSM.initial P) pP\<close> by blast
    have "target (initial M) pP = q"
      using \<open>target (initial P) pP = q\<close> unfolding \<open>initial P = initial M\<close> by assumption
  
    then have "path M q p"
      using \<open>path M (target (initial M) pP) p\<close> by auto
  
    have "io \<noteq> []"
      using \<open>((p_io pP) @ butlast io) \<in> L M\<close> \<open>((p_io pP) @ io) \<notin> L M\<close> by auto
  
  
    (* finiteness properties *)
  
    have "finite ?RP"                                          
      using finite_RP[OF \<open>path M (target (initial M) pP) p\<close> assms(4,7,8,9)] by force
    moreover have "\<And> pR . pR \<in> ?RP \<Longrightarrow> finite (io_targets M' (p_io pR) (initial M'))"
      using io_targets_finite by metis
    ultimately have "finite ?Tgts"
      by blast
  
  
    (* path properties *)
    
    obtain pP' p' where "path M' (FSM.initial M') pP'" 
                  and   "path M' (target (FSM.initial M') pP') p'" 
                  and   "p_io pP' = p_io pP" 
                  and   "p_io p' = io"
      using language_state_split[OF \<open>((p_io pP) @ io) \<in> L M'\<close>]
      by blast
  
    have "length p \<le> length (butlast io)"
      using \<open>butlast io = p_io p @ ioX\<close> by auto
    moreover have "length (butlast io) < length io"
      using \<open>io \<noteq> []\<close> by auto
    ultimately have "length p < length p'"
      unfolding \<open>p_io p' = io\<close> length_map[of "(\<lambda> t . (t_input t, t_output t))", symmetric] by simp
  
    let ?q = "(target (FSM.initial M') pP')"
  
    have "\<And> pR . pP@pR \<in> ?R \<Longrightarrow> path M' ?q (take (length pR) p') \<and> p_io (take (length pR) p') = p_io pR"
    proof -
      fix pR assume "pP@pR \<in> ?R"
      then have  "pR = take (length pR) p \<and> length pR \<le> length p"
        using R_component(1,2) by metis
      then have "p_io pR = take (length pR) (butlast io)"
        by (metis (no_types, lifting) assms(6) length_map take_le take_map) 
      moreover have "p_io (take (length pR) p') = take (length pR) io"
        by (metis (full_types) \<open>p_io p' = io\<close> take_map)
      moreover have "take (length pR) (butlast io) = take (length pR) io"
        using \<open>length p \<le> length (butlast io)\<close> \<open>pR = take (length pR) p \<and> length pR \<le> length p\<close>
              butlast_take_le dual_order.trans 
        by blast
      ultimately have "p_io (take (length pR) p') = p_io pR"
        by simp 
      moreover have "path M' ?q (take (length pR) p')"
        using \<open>path M' (target (FSM.initial M') pP') p'\<close>
        by (simp add: path_prefix_take) 
      ultimately show "path M' ?q (take (length pR) p') \<and> p_io (take (length pR) p') = p_io pR"
        by blast
    qed
  
  
    (* every element in R reaches exactly one state in M' *)
  
    have singleton_prop'_R: "\<And> pR . pP@pR \<in> ?R \<Longrightarrow> io_targets M' (p_io (pP@pR)) (initial M') = {target ?q (take (length pR) p')}"
    proof -
      fix pR assume "pP@pR \<in> ?R"
      then have "path M' ?q (take (length pR) p')" and "p_io (take (length pR) p') = p_io pR"
        using \<open>\<And> pR . pP@pR \<in> ?R \<Longrightarrow> path M' ?q (take (length pR) p') \<and> p_io (take (length pR) p') = p_io pR\<close> by blast+
  
      have *:"path M' (initial M') (pP' @ (take (length pR) p'))"
        using \<open>path M' (initial M') pP'\<close> \<open>path M' ?q (take (length pR) p')\<close> by auto
      have **:"p_io (pP' @ (take (length pR) p')) = (p_io (pP@pR))"
        using \<open>p_io pP' = p_io pP\<close> \<open>p_io (take (length pR) p') = p_io pR\<close> by auto
      
      have "target (initial M') (pP' @ (take (length pR) p')) = target ?q (take (length pR) p')"
        by auto 
      then have "target ?q (take (length pR) p') \<in> io_targets M' (p_io (pP@pR)) (initial M')"
        unfolding io_targets.simps using * **
        by (metis (mono_tags, lifting) mem_Collect_eq) 
  
      show "io_targets M' (p_io (pP@pR)) (initial M') = {target ?q (take (length pR) p')}"
        using observable_io_targets[OF \<open>observable M'\<close> language_state_containment[OF * **]]
        by (metis (no_types) \<open>target (target (FSM.initial M') pP') (take (length pR) p') \<in> io_targets M' (p_io (pP@pR)) (FSM.initial M')\<close> singleton_iff)
    qed
  
    have singleton_prop_R: "\<And> pR . pR \<in> ?R \<Longrightarrow> io_targets M' (p_io pR) (initial M') = {target ?q (take (length pR - length pP) p')}"
    proof -
      fix pR assume "pR \<in> ?R"
      then obtain pR' where "pR = pP@pR'"
        using R_component_ob[of _ M "(target (FSM.initial M) pP)" q' pP p] by blast
      have **: "(length (pP @ pR') - length pP) = length pR'"
        by auto
  
      show "io_targets M' (p_io pR) (initial M') = {target ?q (take (length pR - length pP) p')}"
        using singleton_prop'_R[of pR'] \<open>pR \<in> ?R\<close> unfolding \<open>pR = pP@pR'\<close> ** by blast
    qed


    (* RP props *)

    from b obtain P' pP'' where "(q',P') \<in> PS"
                          and   "path P' (initial P') pP''"
                          and   "target (initial P') pP'' = q'"
                          and   "path M (initial M) pP''"
                          and   "target (initial M) pP'' = q'"
                          and   "p_io pP'' \<in> L M'"
                          and   "?RP = insert pP'' ?R"
      by blast
    have "initial P' = initial M"
      using assms(4)[OF \<open>(q',P') \<in> PS\<close>] unfolding is_preamble_def by auto

    

    (* revisiting singleton_prop *)

    have "\<And> pR . pR \<in> ?RP \<Longrightarrow> pR \<in> ?R \<or> pR = pP''"
      using \<open>?RP = insert pP'' ?R\<close> by blast
    then have rp_cases[consumes 1, case_names in_R inserted]: "\<And> pR P . (pR \<in> ?RP) \<Longrightarrow> (pR \<in> ?R \<Longrightarrow> P) \<Longrightarrow> (pR = pP'' \<Longrightarrow> P) \<Longrightarrow> P" 
      by force 

    have singleton_prop_RP: "\<And> pR . pR \<in> ?RP \<Longrightarrow> \<exists> q . io_targets M' (p_io pR) (initial M') = {q}"
    proof - 
      fix pR assume "pR \<in> ?RP"
      then show "\<exists> q . io_targets M' (p_io pR) (initial M') = {q}" 
      proof (cases rule: rp_cases)
        case in_R
        then show ?thesis using singleton_prop_R by blast
      next
        case inserted
        show ?thesis 
          using observable_io_targets[OF \<open>observable M'\<close> \<open>p_io pP'' \<in> L M'\<close>] unfolding inserted
          by meson 
      qed
    qed
    then have ?P2 by blast


    (* distinctness in RP *)

    have pairwise_dist_prop_RP: "\<And> pR1 pR2 . pR1 \<in> ?RP \<Longrightarrow> pR2 \<in> ?RP \<Longrightarrow> pR1 \<noteq> pR2 \<Longrightarrow> io_targets M' (p_io pR1) (initial M') \<inter> io_targets M' (p_io pR2) (initial M') = {}"
    proof -
      
      have pairwise_dist_prop_R: "\<And> pR1 pR2 . pR1 \<in> ?R \<Longrightarrow> pR2 \<in> ?R \<Longrightarrow> pR1 \<noteq> pR2 \<Longrightarrow> io_targets M' (p_io pR1) (initial M') \<inter> io_targets M' (p_io pR2) (initial M') = {}" 
        using R_count(3)[OF assms(1-6)] by force

      have pairwise_dist_prop_PS: "\<And> pR1 . pR1 \<in> ?RP \<Longrightarrow> pR1 \<noteq> pP'' \<Longrightarrow> io_targets M' (p_io pR1) (initial M') \<inter> io_targets M' (p_io pP'') (initial M') = {}"
      proof -
        fix pR1 assume "pR1 \<in> ?RP" and "pR1 \<noteq> pP''"
        then have "pR1 \<in> ?R"
          using \<open>\<And> pR . pR \<in> ?RP \<Longrightarrow> pR \<in> ?R \<or> pR = pP''\<close> by blast
        
        obtain pR' where "pR1 = pP@pR'"
          using R_component_ob[OF \<open>pR1 \<in> ?R\<close>] by blast
        then have "pP@pR' \<in> ?R"
          using \<open>pR1 \<in> ?R\<close> by blast

        have "pR' = take (length pR') p" 
         and "length pR' \<le> length p" 
         and "t_target (p ! (length pR' - 1)) = q'" 
         and "pR' \<noteq> []"
          using R_component[OF \<open>pP@pR' \<in> ?R\<close>] by blast+

        let ?i = "(length pR') - 1"
        have "?i < length p"
          using \<open>length pR' \<le> length p\<close> \<open>pR' \<noteq> []\<close>
          using diff_less dual_order.strict_trans1 less_numeral_extra(1) by blast 
        then have "?i < length (butlast io)"
          using \<open>length p \<le> length (butlast io)\<close> less_le_trans by blast 


        have "io_targets M' (p_io pR1) (initial M') = {t_target (p' ! ?i)}"
        proof -
          have "(p' ! ?i) = last (take (length pR') p')"
            using \<open>length pR' \<le> length p\<close> \<open>length p < length p'\<close>
            by (metis Suc_diff_1 \<open>pR' \<noteq> []\<close> dual_order.strict_trans2 length_greater_0_conv less_imp_diff_less take_last_index)
          then have *: "target ?q (take (length pR') p') = t_target (p' ! ?i)"
            unfolding target.simps visited_states.simps
            by (metis (no_types, lifting) \<open>length p < length p'\<close> \<open>pR' \<noteq> []\<close> gr_implies_not_zero last.simps 
                  last_map length_0_conv map_is_Nil_conv take_eq_Nil) 
          moreover have "io_targets M' (p_io pR1) (initial M') = {target ?q (take (length pR') p')}"
            using singleton_prop'_R \<open>pR1 \<in> ?R\<close> unfolding \<open>pR1 = pP@pR'\<close> by auto
          ultimately show ?thesis by auto
        qed

        have "t_target (p' ! (length pR' - 1)) \<notin> io_targets M' (p_io pP'') (FSM.initial M')"
        proof -
          (* get the full path along (butlast io) in M, of which p is a (possibly proper) prefix *)

          obtain pX where "path M (target (initial M) pP) (p@pX)" and "p_io (p@pX) = butlast io"
          proof -
            have "p_io pP @ p_io p @ ioX \<in> L M"
              using \<open>((p_io pP) @ butlast io) \<in> L M\<close> 
              unfolding \<open>butlast io = p_io p @ ioX\<close> 
              by assumption
        
            obtain p1 p23 where "path M (FSM.initial M) p1" and "path M (target (FSM.initial M) p1) p23" 
                            and "p_io p1 = p_io pP" and "p_io p23 = p_io p @ ioX"
              using language_state_split[OF \<open>p_io pP @ p_io p @ ioX \<in> L M\<close>] by blast
        
            have "p1 = pP"
              using observable_path_unique[OF \<open>observable M\<close> \<open>path M (FSM.initial M) p1\<close> \<open>path M (FSM.initial M) pP\<close> \<open>p_io p1 = p_io pP\<close>] 
              by assumption
            then have "path M (target (FSM.initial M) pP) p23"
              using \<open>path M (target (FSM.initial M) p1) p23\<close> by auto
            then have "p_io p @ ioX \<in> LS M (target (initial M) pP)"
              using \<open>p_io p23 = p_io p @ ioX\<close> language_state_containment by auto
        
            obtain p2 p3 where "path M (target (FSM.initial M) pP) p2" 
                           and "path M (target (target (FSM.initial M) pP) p2) p3" 
                           and "p_io p2 = p_io p" 
                           and "p_io p3 = ioX"
              using language_state_split[OF \<open>p_io p @ ioX \<in> LS M (target (initial M) pP)\<close>] 
              by blast
        
            have "p2 = p"
              using observable_path_unique[OF \<open>observable M\<close> \<open>path M (target (FSM.initial M) pP) p2\<close> \<open>path M (target (FSM.initial M) pP) p\<close> \<open>p_io p2 = p_io p\<close>] 
              by assumption
            then have "path M (target (FSM.initial M) pP) (p@p3)"
              using \<open>path M (target (FSM.initial M) pP) p\<close> \<open>path M (target (target (FSM.initial M) pP) p2) p3\<close> 
              by auto
            moreover have "p_io (p@p3) = butlast io"
              unfolding \<open>butlast io = p_io p @ ioX\<close> 
              using \<open>p_io p3 = ioX\<close> 
              by auto
            ultimately show ?thesis 
              using that[of p3] 
              by simp
          qed

          (* get index properties *)

          have "target (FSM.initial M') pP' \<in> io_targets M' (p_io pP) (FSM.initial M')"
            using \<open>p_io pP' = p_io pP\<close> \<open>path M' (FSM.initial M') pP'\<close> observable_path_io_target by auto 
  
          have "(t_target (p ! (length pR' - 1)), P') \<in> PS"
            using \<open>(q',P') \<in> PS\<close> unfolding \<open>t_target (p ! (length pR' - 1)) = q'\<close> by assumption
          then have "(t_target ((p @ pX) ! ?i), P') \<in> PS"
            by (metis \<open>length pR' - 1 < length p\<close> nth_append)
  
          have "target (FSM.initial P') pP'' = t_target (p ! (length pR' - 1))"
            unfolding \<open>target (initial M) pP'' = q'\<close> \<open>t_target (p ! (length pR' - 1)) = q'\<close> \<open>initial P' = initial M\<close> by simp
          then have "target (FSM.initial P') pP'' = t_target ((p @ pX) ! ?i)"
            by (metis \<open>length pR' - 1 < length p\<close> nth_append)
            

          show ?thesis
            using minimal_sequence_to_failure_extending_preamble_no_repetitions_with_other_preambles
                    [OF assms(1,2) \<open>path M (target (initial M) pP) (p@pX)\<close> \<open>p_io (p@pX) = butlast io\<close> 
                        \<open>target (FSM.initial M') pP' \<in> io_targets M' (p_io pP) (FSM.initial M')\<close> 
                        \<open>path M' (target (FSM.initial M') pP') p'\<close> \<open>p_io p' = io\<close> assms(4) 
                        \<open>?i < length (butlast io)\<close> \<open>(t_target ((p @ pX) ! ?i), P') \<in> PS\<close> 
                        \<open>path P' (initial P') pP''\<close> \<open>target (FSM.initial P') pP'' = t_target ((p @ pX) ! ?i)\<close>]
            by blast
        qed
        then show "io_targets M' (p_io pR1) (initial M') \<inter> io_targets M' (p_io pP'') (initial M') = {}"
          unfolding \<open>io_targets M' (p_io pR1) (initial M') = {t_target (p' ! ?i)}\<close> 
          by blast
      qed


      fix pR1 pR2 assume "pR1 \<in> ?RP" and "pR2 \<in> ?RP" and "pR1 \<noteq> pR2"

      then consider (a) "pR1 \<in> ?R \<and> pR2 \<in> ?R" |
                    (b) "pR1 = pP''" |
                    (c) "pR2 = pP''" 
        using \<open>\<And> pR . pR \<in> ?RP \<Longrightarrow> pR \<in> ?R \<or> pR = pP''\<close> \<open>pR1 \<noteq> pR2\<close> by blast
      then show "io_targets M' (p_io pR1) (initial M') \<inter> io_targets M' (p_io pR2) (initial M') = {}"
      proof cases
        case a
        then show ?thesis using pairwise_dist_prop_R[of pR1 pR2, OF _ _ \<open>pR1 \<noteq> pR2\<close>] by blast
      next
        case b
        then show ?thesis using pairwise_dist_prop_PS[OF \<open>pR2 \<in> ?RP\<close>] \<open>pR1 \<noteq> pR2\<close> by blast
      next
        case c
        then show ?thesis using pairwise_dist_prop_PS[OF \<open>pR1 \<in> ?RP\<close>] \<open>pR1 \<noteq> pR2\<close> by blast
      qed
    qed
    then have ?P3 by blast


    let ?f = "(\<lambda> pR . io_targets M' (p_io pR) (initial M'))"
  
    have p1: "(\<And>S1 S2. S1 \<in> ?RP \<Longrightarrow> S2 \<in> ?RP \<Longrightarrow> S1 = S2 \<or> ?f S1 \<inter> ?f S2 = {})"
      using pairwise_dist_prop_RP by blast
    have p2: "(\<And>S. S \<in> ?RP \<Longrightarrow> io_targets M' (p_io S) (FSM.initial M') \<noteq> {})"
      using singleton_prop_RP by blast
    have c1: "card ?RP = card ((\<lambda>S. io_targets M' (p_io S) (FSM.initial M')) ` ?RP)"
      using card_union_of_distinct[of ?RP, OF p1 \<open>finite ?RP\<close> p2] by force
  
    have p3: "(\<And>S. S \<in> (\<lambda>S. io_targets M' (p_io S) (FSM.initial M')) ` ?RP \<Longrightarrow> \<exists>t. S = {t})"
      using singleton_prop_RP by blast
    have c2:"card ((\<lambda>S. io_targets M' (p_io S) (FSM.initial M')) ` ?RP) = card (\<Union>S\<in>?RP. io_targets M' (p_io S) (FSM.initial M'))"
      using card_union_of_singletons[of "((\<lambda>S. io_targets M' (p_io S) (FSM.initial M')) ` ?RP)", OF p3] by force
        
    have ?P1
      unfolding c1 c2 by blast

    show ?combined_goals 
      using \<open>?P1\<close> \<open>?P2\<close> \<open>?P3\<close> 
      by blast
  qed

  

  then show "card (\<Union> (image (\<lambda> pR . io_targets M' (p_io pR) (initial M')) (RP M (target (initial M) pP) q' pP p PS M'))) = card (RP M (target (initial M) pP) q' pP p PS M')"
       and  "\<And> pR . pR \<in> (RP M (target (initial M) pP) q' pP p PS M') \<Longrightarrow> \<exists> q . io_targets M' (p_io pR) (initial M') = {q}"
       and  "\<And> pR1 pR2 . pR1 \<in> (RP M (target (initial M) pP) q' pP p PS M') \<Longrightarrow> pR2 \<in> (RP M (target (initial M) pP) q' pP p PS M') \<Longrightarrow> pR1 \<noteq> pR2 \<Longrightarrow> io_targets M' (p_io pR1) (initial M') \<inter> io_targets M' (p_io pR2) (initial M') = {}"
    by blast+
qed



lemma RP_target: 
  assumes "pR \<in> (RP M q q' pP p PS M')" 
  assumes "\<And> q P . (q,P) \<in> PS \<Longrightarrow> is_preamble P M q"
  and     "\<And> q P io x y y' . (q,P) \<in> PS \<Longrightarrow> io@[(x,y)] \<in> L P \<Longrightarrow> io@[(x,y')] \<in> L M' \<Longrightarrow> io@[(x,y')] \<in> L P"
  and     "completely_specified M'"
  and     "inputs M' = inputs M"
shows "target (initial M) pR = q'"
proof -
  show "target (initial M) pR = q'"
  proof (cases "pR \<in> R M q q' pP p")
    case True
    then show ?thesis unfolding R_def by force
  next
    case False
    then have "RP M q q' pP p PS M' \<noteq> R M q q' pP p"
      using assms(1) by blast
    then have "(\<exists>P' pP'.
        (q', P') \<in> PS \<and>
        path P' (FSM.initial P') pP' \<and>
        target (FSM.initial P') pP' = q' \<and>
        path M (FSM.initial M) pP' \<and> target (FSM.initial M) pP' = q' \<and> p_io pP' \<in> L M' \<and> RP M q q' pP p PS M' = insert pP' (R M q q' pP p))"
      using RP_from_R[OF assms(2-5), of PS _ _ q q' pP p] by force
    then obtain pP' where "target (FSM.initial M) pP' = q'" and "RP M q q' pP p PS M' = insert pP' (R M q q' pP p)"
      by blast
    
    have "pR = pP'"
      using \<open>RP M q q' pP p PS M' = insert pP' (R M q q' pP p)\<close> \<open>pR \<in> (RP M q q' pP p PS M')\<close> False by blast

    show ?thesis using \<open>target (FSM.initial M) pP' = q'\<close> unfolding \<open>pR = pP'\<close> by assumption
  qed
qed 


subsubsection \<open>Proof of Exhaustiveness\<close>

lemma passes_test_suite_exhaustiveness_helper_1 :
  assumes "completely_specified M'"
  and     "inputs M' = inputs M"
  and     "observable M"
  and     "observable M'"
  and     "(q,P) \<in> PS"
  and     "path P (initial P) pP"
  and     "target (initial P) pP = q"
  and     "p_io pP @ p_io p \<in> L M'"  
  and     "(p, d) \<in> m_traversal_paths_with_witness M q repetition_sets m"
  and     "implies_completeness_for_repetition_sets (Test_Suite PS tps rd_targets separators) M m repetition_sets"
  and     "passes_test_suite M (Test_Suite PS tps rd_targets separators) M'"
  and     "q' \<noteq> q''"
  and     "q' \<in> fst d"
  and     "q'' \<in> fst d"
  and     "pR1 \<in> (RP M q q' pP p PS M')"
  and     "pR2 \<in> (RP M q q'' pP p PS M')"
shows "io_targets M' (p_io pR1) (initial M') \<inter> io_targets M' (p_io pR2) (initial M') = {}"
proof -

  let ?RP1 = "(RP M q q' pP p PS M')"
  let ?RP2 = "(RP M q q'' pP p PS M')"
  let ?R1  = "(R M q q' pP p)"
  let ?R2  = "(R M q q'' pP p)"

  (* sufficiency properties *)


  have t1: "(initial M, initial_preamble M) \<in> PS" 
    using \<open>implies_completeness_for_repetition_sets (Test_Suite PS tps rd_targets separators) M m repetition_sets\<close> 
    unfolding implies_completeness_for_repetition_sets.simps by blast
  have t2: "\<And> q P. (q, P) \<in> PS \<Longrightarrow> is_preamble P M q"
    using \<open>implies_completeness_for_repetition_sets (Test_Suite PS tps rd_targets separators) M m repetition_sets\<close> 
    unfolding implies_completeness_for_repetition_sets.simps by force
  have t3: "\<And> q1 q2 A d1 d2. (A, d1, d2) \<in> separators (q1, q2) \<Longrightarrow> (A, d2, d1) \<in> separators (q2, q1) \<and> is_separator M q1 q2 A d1 d2"
    using \<open>implies_completeness_for_repetition_sets (Test_Suite PS tps rd_targets separators) M m repetition_sets\<close> 
    unfolding implies_completeness_for_repetition_sets.simps by force  


  have t5: "\<And>q. q \<in> FSM.states M \<Longrightarrow> (\<exists>d\<in>set repetition_sets. q \<in> fst d)"
    using \<open>implies_completeness_for_repetition_sets (Test_Suite PS tps rd_targets separators) M m repetition_sets\<close> 
    unfolding implies_completeness_for_repetition_sets.simps by force

  have t6: "\<And> q. q \<in> fst ` PS \<Longrightarrow> tps q \<subseteq> {p1 . \<exists> p2 d . (p1@p2,d) \<in> m_traversal_paths_with_witness M q repetition_sets m} \<and> fst ` (m_traversal_paths_with_witness M q repetition_sets m) \<subseteq> tps q"
    using \<open>implies_completeness_for_repetition_sets (Test_Suite PS tps rd_targets separators) M m repetition_sets\<close> 
    unfolding implies_completeness_for_repetition_sets.simps by auto

  have "\<And> d. d \<in> set repetition_sets \<Longrightarrow> fst d \<subseteq> FSM.states M \<and> snd d = fst d \<inter> fst ` PS \<and> (\<forall>q1 q2. q1 \<in> fst d \<longrightarrow> q2 \<in> fst d \<longrightarrow> q1 \<noteq> q2 \<longrightarrow> separators (q1, q2) \<noteq> {})"
    using \<open>implies_completeness_for_repetition_sets (Test_Suite PS tps rd_targets separators) M m repetition_sets\<close> 
    unfolding implies_completeness_for_repetition_sets.simps by force
  then have t7: "\<And> d. d \<in> set repetition_sets \<Longrightarrow> fst d \<subseteq> FSM.states M"
  and  t8: "\<And> d. d \<in> set repetition_sets \<Longrightarrow> snd d \<subseteq> fst d"
  and  t8': "\<And> d. d \<in> set repetition_sets \<Longrightarrow> snd d = fst d \<inter> fst ` PS"
  and  t9: "\<And> d q1 q2. d \<in> set repetition_sets \<Longrightarrow> q1 \<in> fst d \<Longrightarrow> q2 \<in> fst d \<Longrightarrow> q1 \<noteq> q2 \<Longrightarrow> separators (q1, q2) \<noteq> {}"
    by blast+

  have t10: "\<And> q p d p1 p2 p3.
              q \<in> fst ` PS \<Longrightarrow>
              (p, d) \<in> m_traversal_paths_with_witness M q repetition_sets m \<Longrightarrow>
              p = p1 @ p2 @ p3 \<Longrightarrow>
              p2 \<noteq> [] \<Longrightarrow>
              target q p1 \<in> fst d \<Longrightarrow>
              target q (p1 @ p2) \<in> fst d \<Longrightarrow>
              target q p1 \<noteq> target q (p1 @ p2) \<Longrightarrow>
              p1 \<in> tps q \<and> p1 @ p2 \<in> tps q \<and> target q p1 \<in> rd_targets (q, p1 @ p2) \<and> target q (p1 @ p2) \<in> rd_targets (q, p1)"
    using \<open>implies_completeness_for_repetition_sets (Test_Suite PS tps rd_targets separators) M m repetition_sets\<close> 
    unfolding implies_completeness_for_repetition_sets.simps
    by (metis (no_types, lifting)) 

  have t11: "\<And> q p d p1 p2 q'.
              q \<in> fst ` PS \<Longrightarrow>
              (p, d) \<in> m_traversal_paths_with_witness M q repetition_sets m \<Longrightarrow>
              p = p1 @ p2 \<Longrightarrow>
              q' \<in> fst ` PS \<Longrightarrow>
              target q p1 \<in> fst d \<Longrightarrow>
              q' \<in> fst d \<Longrightarrow> 
              target q p1 \<noteq> q' \<Longrightarrow> 
              p1 \<in> tps q \<and> [] \<in> tps q' \<and> target q p1 \<in> rd_targets (q', []) \<and> q' \<in> rd_targets (q, p1)"
    using \<open>implies_completeness_for_repetition_sets (Test_Suite PS tps rd_targets separators) M m repetition_sets\<close> 
    unfolding implies_completeness_for_repetition_sets.simps
    by (metis (no_types, lifting)) 

  have t12: "\<And> q p d q1 q2.
              q \<in> fst ` PS \<Longrightarrow>
              (p, d) \<in> m_traversal_paths_with_witness M q repetition_sets m \<Longrightarrow>
              q1 \<noteq> q2 \<Longrightarrow>
              q1 \<in> snd d \<Longrightarrow> 
              q2 \<in> snd d \<Longrightarrow> 
              [] \<in> tps q1 \<and> [] \<in> tps q2 \<and> q1 \<in> rd_targets (q2, []) \<and> q2 \<in> rd_targets (q1, [])"
    using \<open>implies_completeness_for_repetition_sets (Test_Suite PS tps rd_targets separators) M m repetition_sets\<close> 
    unfolding implies_completeness_for_repetition_sets.simps
    by (metis (no_types, lifting)) 


  (* pass properties *)

  have pass1: "\<And> q P io x y y' . (q,P) \<in> PS \<Longrightarrow> io@[(x,y)] \<in> L P \<Longrightarrow> io@[(x,y')] \<in> L M' \<Longrightarrow> io@[(x,y')] \<in> L P" 
    using \<open>passes_test_suite M (Test_Suite PS tps rd_targets separators) M'\<close>
    unfolding passes_test_suite.simps
    by meson 

  have pass2: "\<And> q P pP ioT pT x y y' . (q,P) \<in> PS \<Longrightarrow> path P (initial P) pP \<Longrightarrow> target (initial P) pP = q \<Longrightarrow> pT \<in> tps q \<Longrightarrow> ioT@[(x,y)] \<in> set (prefixes (p_io pT)) \<Longrightarrow> (p_io pP)@ioT@[(x,y')] \<in> L M' \<Longrightarrow> (\<exists> pT' . pT' \<in> tps q \<and> ioT@[(x,y')] \<in> set (prefixes (p_io pT')))"
    using \<open>passes_test_suite M (Test_Suite PS tps rd_targets separators) M'\<close>
    unfolding passes_test_suite.simps by blast

  have pass3: "\<And> q P pP pT q' A d1 d2 qT . (q,P) \<in> PS \<Longrightarrow> path P (initial P) pP \<Longrightarrow> target (initial P) pP = q \<Longrightarrow> pT \<in> tps q \<Longrightarrow> (p_io pP)@(p_io pT) \<in> L M' \<Longrightarrow> q' \<in> rd_targets (q,pT) \<Longrightarrow> (A,d1,d2) \<in> separators (target q pT, q') \<Longrightarrow> qT \<in> io_targets M' ((p_io pP)@(p_io pT)) (initial M') \<Longrightarrow> pass_separator_ATC M' A qT d2"  
    using \<open>passes_test_suite M (Test_Suite PS tps rd_targets separators) M'\<close>
    unfolding passes_test_suite.simps by blast


  (* additional props *)

  have "is_preamble P M q"
    using \<open>(q,P) \<in> PS\<close> \<open>\<And> q P. (q, P) \<in> PS \<Longrightarrow> is_preamble P M q\<close> 
    by blast
  then have "q \<in> states M"
    unfolding is_preamble_def
    by (metis \<open>path P (FSM.initial P) pP\<close> \<open>target (FSM.initial P) pP = q\<close> path_target_is_state submachine_path) 

  have "initial P = initial M"
    using \<open>is_preamble P M q\<close> unfolding is_preamble_def
    by auto
  have "path M (initial M) pP"
    using \<open>is_preamble P M q\<close> submachine_path_initial \<open>path P (FSM.initial P) pP\<close> 
    unfolding is_preamble_def  
    by blast
  moreover have "target (initial M) pP = q"
    using \<open>target (initial P) pP = q\<close> 
    unfolding \<open>initial P = initial M\<close> 
    by assumption
  ultimately have "q \<in> states M"
    using path_target_is_state 
    by metis


  have "q \<in> fst ` PS"
    using \<open>(q,P) \<in> PS\<close> by force

  have "d \<in> set repetition_sets" 
    using \<open>(p, d) \<in> m_traversal_paths_with_witness M q repetition_sets m\<close> 
    using m_traversal_paths_with_witness_set[OF t5 t8 \<open>q \<in> states M\<close>, of m]
    using find_set by force

  have "q' \<in> states M"
    by (meson \<open>d \<in> set repetition_sets\<close> assms(13) subset_iff t7)
  have "q'' \<in> states M"
    by (meson \<open>d \<in> set repetition_sets\<close> assms(14) subset_iff t7)


  have "target (initial M) pR1 = q'"
    using RP_target[OF \<open>pR1 \<in> ?RP1\<close> t2 pass1 \<open>completely_specified M'\<close> \<open>inputs M' = inputs M\<close>] by force
  then have "target (initial M) pR1 \<in> fst d"
    using \<open>q' \<in> fst d\<close> by blast
    

  have "target (initial M) pR2 = q''"
    using RP_target[OF \<open>pR2 \<in> ?RP2\<close> t2 pass1 \<open>completely_specified M'\<close> \<open>inputs M' = inputs M\<close>] by force
  then have "target (initial M) pR2 \<in> fst d"
    using \<open>q'' \<in> fst d\<close> by blast

  have "pR1 \<noteq> pR2"
    using \<open>target (initial M) pR1 = q'\<close> \<open>target (initial M) pR2 = q''\<close> \<open>q' \<noteq> q''\<close> by auto


  obtain A t1 t2 where "(A,t1,t2) \<in> separators (q',q'')"
    using t9[OF \<open>d \<in> set repetition_sets\<close> \<open>q' \<in> fst d\<close> \<open>q'' \<in> fst d\<close> \<open>q' \<noteq> q''\<close>]
    by auto
  have "(A,t2,t1) \<in> separators (q'',q')" and "is_separator M q' q'' A t1 t2"
    using t3[OF \<open>(A,t1,t2) \<in> separators (q',q'')\<close>] by simp+
  then have "is_separator M q'' q' A t2 t1"
    using is_separator_sym by force

  show "io_targets M' (p_io pR1) (initial M') \<inter> io_targets M' (p_io pR2) (initial M') = {}" 
  proof (rule ccontr) 
    assume "io_targets M' (p_io pR1) (FSM.initial M') \<inter> io_targets M' (p_io pR2) (FSM.initial M') \<noteq> {}"
    then obtain qT where "qT \<in> io_targets M' (p_io pR1) (FSM.initial M')"
                   and   "qT \<in> io_targets M' (p_io pR2) (FSM.initial M')"
      by blast

    then have "qT \<in> states M'"
      using path_target_is_state unfolding io_targets.simps by force

    consider (a) "pR1 \<in> ?R1 \<and> pR2 \<in> ?R2" |
             (b) "pR1 \<in> ?R1 \<and> pR2 \<notin> ?R2" |
             (c) "pR1 \<notin> ?R1 \<and> pR2 \<in> ?R2" |
             (d) "pR1 \<notin> ?R1 \<and> pR2 \<notin> ?R2"
      by blast

    then show "False" proof cases
      case a
      then have "pR1 \<in> ?R1" and "pR2 \<in> ?R2" by auto
                
      obtain pR1' where "pR1 = pP@pR1'" using R_component_ob[OF \<open>pR1 \<in> ?R1\<close>] by blast
      obtain pR2' where "pR2 = pP@pR2'" using R_component_ob[OF \<open>pR2 \<in> ?R2\<close>] by blast

      have "pR1' = take (length pR1') p" and "length pR1' \<le> length p" and "t_target (p ! (length pR1' - 1)) = q'" and "pR1' \<noteq> []"
        using R_component[of pP pR1' M q q' p] \<open>pR1 \<in> ?R1\<close> unfolding \<open>pR1 = pP@pR1'\<close> by blast+ 

      have "pR2' = take (length pR2') p" and "length pR2' \<le> length p" and "t_target (p ! (length pR2' - 1)) = q''" and "pR2' \<noteq> []"
        using R_component[of pP pR2' M q q'' p] \<open>pR2 \<in> ?R2\<close> unfolding \<open>pR2 = pP@pR2'\<close> by blast+ 

      have "target q pR1' = q'"
        using \<open>target (initial M) pR1 = q'\<close> \<open>pR1' \<noteq> []\<close> unfolding target.simps visited_states.simps \<open>pR1 = pP@pR1'\<close> by simp 
      then have "target q pR1' \<in> fst d"
        using \<open>q' \<in> fst d\<close> by blast

      have "target q pR2' = q''"
        using \<open>target (initial M) pR2 = q''\<close> \<open>pR2' \<noteq> []\<close> unfolding target.simps visited_states.simps \<open>pR2 = pP@pR2'\<close> by simp 
      then have "target q pR2' \<in> fst d"
        using \<open>q'' \<in> fst d\<close> by blast

      have "pR1' \<noteq> pR2'"
        using \<open>pR1 \<noteq> pR2\<close> unfolding \<open>pR1 = pP@pR1'\<close> \<open>pR2 = pP@pR2'\<close> by simp
      then have "length pR1' \<noteq> length pR2'"
        using \<open>pR1' = take (length pR1') p\<close> \<open>pR2' = take (length pR2') p\<close> by auto
      then consider (a1) "length pR1' < length pR2'" | (a2) "length pR2' < length pR1'"
        using nat_neq_iff by blast 
      then have "pR1' \<in> tps q \<and> pR2' \<in> tps q \<and> q' \<in> rd_targets (q, pR2') \<and> q'' \<in> rd_targets (q, pR1')"
      proof cases
        case a1
        then have "pR2' = pR1' @ (drop (length pR1') pR2')"
          using \<open>pR1' = take (length pR1') p\<close> \<open>pR2' = take (length pR2') p\<close>
          by (metis append_take_drop_id less_imp_le_nat take_le) 
        then have "p = pR1' @ (drop (length pR1') pR2') @ (drop (length pR2') p)"
          using \<open>pR2' = take (length pR2') p\<close>
          by (metis append.assoc append_take_drop_id)

        have "(drop (length pR1') pR2') \<noteq> []"
          using a1 \<open>pR2' = take (length pR2') p\<close> by auto
        have "target q (pR1' @ drop (length pR1') pR2') \<in> fst d"
          using \<open>pR2' = pR1' @ (drop (length pR1') pR2')\<close>[symmetric] \<open>target q pR2' \<in> fst d\<close> by auto

        show ?thesis
          using t10[OF \<open>q \<in> fst ` PS\<close> \<open>(p, d) \<in> m_traversal_paths_with_witness M q repetition_sets m\<close> 
                       \<open>p = pR1' @ (drop (length pR1') pR2') @ (drop (length pR2') p)\<close> 
                       \<open>(drop (length pR1') pR2') \<noteq> []\<close> \<open>target q pR1' \<in> fst d\<close> 
                       \<open>target q (pR1' @ drop (length pR1') pR2') \<in> fst d\<close>]
          unfolding \<open>pR2' = pR1' @ (drop (length pR1') pR2')\<close>[symmetric] \<open>target q pR1' = q'\<close>  \<open>target q pR2' = q''\<close>
          using \<open>q' \<noteq> q''\<close>
          by blast
      next
        case a2
        then have "pR1' = pR2' @ (drop (length pR2') pR1')"
          using \<open>pR1' = take (length pR1') p\<close> \<open>pR2' = take (length pR2') p\<close>
          by (metis append_take_drop_id less_imp_le_nat take_le) 
        then have "p = pR2' @ (drop (length pR2') pR1') @ (drop (length pR1') p)"
          using \<open>pR1' = take (length pR1') p\<close>
          by (metis append.assoc append_take_drop_id)

        have "(drop (length pR2') pR1') \<noteq> []"
          using a2 \<open>pR1' = take (length pR1') p\<close> by auto
        have "target q (pR2' @ drop (length pR2') pR1') \<in> fst d"
          using \<open>pR1' = pR2' @ (drop (length pR2') pR1')\<close>[symmetric] \<open>target q pR1' \<in> fst d\<close> by auto

        show ?thesis
          using t10[OF \<open>q \<in> fst ` PS\<close> \<open>(p, d) \<in> m_traversal_paths_with_witness M q repetition_sets m\<close>
                       \<open>p = pR2' @ (drop (length pR2') pR1') @ (drop (length pR1') p)\<close> 
                       \<open>(drop (length pR2') pR1') \<noteq> []\<close> \<open>target q pR2' \<in> fst d\<close> 
                       \<open>target q (pR2' @ drop (length pR2') pR1') \<in> fst d\<close>]
          unfolding \<open>pR1' = pR2' @ (drop (length pR2') pR1')\<close>[symmetric] \<open>target q pR1' = q'\<close> \<open>target q pR2' = q''\<close>
          using \<open>q' \<noteq> q''\<close>
          by blast
      qed 
      then have "pR1' \<in> tps q" and "pR2' \<in> tps q" and "q' \<in> rd_targets (q, pR2')" and "q'' \<in> rd_targets (q, pR1')"
        by simp+

      

      have "p_io pP @ p_io pR1' \<in> L M'"
        using language_prefix_append[OF \<open>p_io pP @ p_io p \<in> L M'\<close>, of "length pR1'"]
        using \<open>pR1' = take (length pR1') p\<close> by simp
      have "pass_separator_ATC M' A qT t2"
        using pass3[OF \<open>(q, P) \<in> PS\<close> \<open>path P (initial P) pP\<close> \<open>target (initial P) pP = q\<close> \<open>pR1' \<in> tps q\<close> 
                       \<open>p_io pP @ p_io pR1' \<in> L M'\<close> \<open>q'' \<in> rd_targets (q, pR1')\<close>, of A t1 t2]
              \<open>(A, t1, t2) \<in> separators (q', q'')\<close> \<open>qT \<in> io_targets M' (p_io pR1) (FSM.initial M')\<close> 
        unfolding \<open>target q pR1' = q'\<close> \<open>pR1 = pP @ pR1'\<close> by auto


      have "p_io pP @ p_io pR2' \<in> L M'"
        using language_prefix_append[OF \<open>p_io pP @ p_io p \<in> L M'\<close>, of "length pR2'"]
        using \<open>pR2' = take (length pR2') p\<close> by simp
      have "pass_separator_ATC M' A qT t1"
        using pass3[OF \<open>(q, P) \<in> PS\<close> \<open>path P (initial P) pP\<close> \<open>target (initial P) pP = q\<close> \<open>pR2' \<in> tps q\<close>
                       \<open>p_io pP @ p_io pR2' \<in> L M'\<close> \<open>q' \<in> rd_targets (q, pR2')\<close>, of A t2 t1]
              \<open>(A, t2, t1) \<in> separators (q'', q')\<close> \<open>qT \<in> io_targets M' (p_io pR2) (FSM.initial M')\<close> 
        unfolding \<open>target q pR2' = q''\<close> \<open>pR2 = pP @ pR2'\<close> by auto

      (* the state qT reached by both paths cannot satisfy the ATC that r-distinguishes their respective targets for both targets at the same time *)

      have "qT \<noteq> qT"
        using pass_separator_ATC_reduction_distinction[OF \<open>observable M\<close> \<open>observable M'\<close> \<open>inputs M' = inputs M\<close> \<open>pass_separator_ATC M' A qT t2\<close> \<open>pass_separator_ATC M' A qT t1\<close> \<open>q' \<in> states M\<close> \<open>q'' \<in> states M\<close> \<open>q' \<noteq> q''\<close> \<open>qT \<in> states M'\<close> \<open>qT \<in> states M'\<close> \<open>is_separator M q' q'' A t1 t2\<close> \<open>completely_specified M'\<close>]
        by assumption
      then show False
        by simp

    next
      case b

      then have "pR1 \<in> ?R1" and "pR2 \<notin> ?R2"
        using \<open>pR1 \<in> ?RP1\<close> by auto
                
      obtain pR1' where "pR1 = pP@pR1'" using R_component_ob[OF \<open>pR1 \<in> ?R1\<close>] by blast
      

      have "pR1' = take (length pR1') p" and "length pR1' \<le> length p" and "t_target (p ! (length pR1' - 1)) = q'" and "pR1' \<noteq> []"
        using R_component[of pP pR1' M q q' p] \<open>pR1 \<in> ?R1\<close> unfolding \<open>pR1 = pP@pR1'\<close> by blast+ 

      have "target q pR1' = q'"
        using \<open>target (initial M) pR1 = q'\<close> \<open>pR1' \<noteq> []\<close> unfolding target.simps visited_states.simps \<open>pR1 = pP@pR1'\<close> by simp 
      then have "target q pR1' \<in> fst d" and "target q pR1' \<noteq> q''"
        using \<open>q' \<in> fst d\<close> \<open>q' \<noteq> q''\<close> by blast+


      obtain P' where "(q'', P') \<in> PS"
                      "path P' (FSM.initial P') pR2"
                      "target (FSM.initial P') pR2 = q''"
                      "path M (FSM.initial M) pR2" 
                      "target (FSM.initial M) pR2 = q''" 
                      "p_io pR2 \<in> L M'"
                      "RP M q q'' pP p PS M' = insert pR2 (R M q q'' pP p)"
        using RP_from_R_inserted[OF t2 pass1 \<open>completely_specified M'\<close> \<open>inputs M' = inputs M\<close> \<open>pR2 \<in> ?RP2\<close> \<open>pR2 \<notin> ?R2\<close>, 
                                 of "\<lambda> q P io x y y' . q" "\<lambda> q P io x y y' . y"] 
        by blast


      
      have "q'' \<in> fst ` PS" using \<open>(q'',P') \<in> PS\<close> by force
      have "p = pR1' @ (drop (length pR1') p)" using \<open>pR1' = take (length pR1') p\<close>
        by (metis append_take_drop_id)

      have "pR1' \<in> tps q" and "[] \<in> tps q''" and "target q pR1' \<in> rd_targets (q'', [])" and "q'' \<in> rd_targets (q, pR1')"
        using t11[OF \<open>q \<in> fst ` PS\<close> \<open>(p, d) \<in> m_traversal_paths_with_witness M q repetition_sets m\<close>
                     \<open>p = pR1' @ (drop (length pR1') p)\<close> \<open>q'' \<in> fst ` PS\<close> 
                     \<open>target q pR1' \<in> fst d\<close> \<open>q'' \<in> fst d\<close> \<open>target q pR1' \<noteq> q''\<close>]
        by simp+


      have "p_io pP @ p_io pR1' \<in> L M'"
        using language_prefix_append[OF \<open>p_io pP @ p_io p \<in> L M'\<close>, of "length pR1'"]
        using \<open>pR1' = take (length pR1') p\<close> by simp
      have "pass_separator_ATC M' A qT t2"
        using pass3[OF \<open>(q, P) \<in> PS\<close> \<open>path P (initial P) pP\<close> \<open>target (initial P) pP = q\<close> \<open>pR1' \<in> tps q\<close> 
                       \<open>p_io pP @ p_io pR1' \<in> L M'\<close> \<open>q'' \<in> rd_targets (q, pR1')\<close>, of A t1 t2]
              \<open>(A, t1, t2) \<in> separators (q', q'')\<close> \<open>qT \<in> io_targets M' (p_io pR1) (FSM.initial M')\<close> 
        unfolding \<open>target q pR1' = q'\<close> \<open>pR1 = pP @ pR1'\<close> by auto

      have "pass_separator_ATC M' A qT t1"
        using pass3[OF \<open>(q'', P') \<in> PS\<close> \<open>path P' (FSM.initial P') pR2\<close> \<open>target (FSM.initial P') pR2 = q''\<close> 
                       \<open>[] \<in> tps q''\<close> _ \<open>target q pR1' \<in> rd_targets (q'', [])\<close>, of A t2 t1 qT]
              \<open>(A, t2, t1) \<in> separators (q'', q')\<close> \<open>qT \<in> io_targets M' (p_io pR2) (FSM.initial M')\<close> \<open>p_io pR2 \<in> L M'\<close>
        unfolding \<open>target q pR1' = q'\<close> by auto

      have "qT \<noteq> qT"
        using pass_separator_ATC_reduction_distinction[OF \<open>observable M\<close> \<open>observable M'\<close> \<open>inputs M' = inputs M\<close> 
                                                          \<open>pass_separator_ATC M' A qT t2\<close> 
                                                          \<open>pass_separator_ATC M' A qT t1\<close> \<open>q' \<in> states M\<close> 
                                                          \<open>q'' \<in> states M\<close> \<open>q' \<noteq> q''\<close> \<open>qT \<in> states M'\<close> 
                                                          \<open>qT \<in> states M'\<close> \<open>is_separator M q' q'' A t1 t2\<close> 
                                                          \<open>completely_specified M'\<close>]
        by assumption
      then show False
        by simp
    next
      case c
      then have "pR2 \<in> ?R2" and "pR1 \<notin> ?R1"
        using \<open>pR2 \<in> ?RP2\<close> by auto
                
      obtain pR2' where "pR2 = pP@pR2'" using R_component_ob[OF \<open>pR2 \<in> ?R2\<close>] by blast
      

      have "pR2' = take (length pR2') p" 
       and "length pR2' \<le> length p" 
       and "t_target (p ! (length pR2' - 1)) = q''" 
       and "pR2' \<noteq> []"
        using R_component[of pP pR2' M q q'' p] \<open>pR2 \<in> ?R2\<close> 
        unfolding \<open>pR2 = pP@pR2'\<close> 
        by blast+ 

      have "target q pR2' = q''"
        using \<open>target (initial M) pR2 = q''\<close> \<open>pR2' \<noteq> []\<close> 
        unfolding target.simps visited_states.simps \<open>pR2 = pP@pR2'\<close>
        by simp 
      then have "target q pR2' \<in> fst d" and "target q pR2' \<noteq> q'"
        using \<open>q'' \<in> fst d\<close> \<open>q' \<noteq> q''\<close> by blast+


      obtain P' where "(q', P') \<in> PS"
                      "path P' (FSM.initial P') pR1"
                      "target (FSM.initial P') pR1 = q'"
                      "path M (FSM.initial M) pR1" 
                      "target (FSM.initial M) pR1 = q'" 
                      "p_io pR1 \<in> L M'"
                      "RP M q q' pP p PS M' = insert pR1 (R M q q' pP p)"
        using RP_from_R_inserted[OF t2 pass1 \<open>completely_specified M'\<close> \<open>inputs M' = inputs M\<close> \<open>pR1 \<in> ?RP1\<close> \<open>pR1 \<notin> ?R1\<close>, 
                                 of "\<lambda> q P io x y y' . q" "\<lambda> q P io x y y' . y"] 
        by blast

      
      have "q' \<in> fst ` PS" using \<open>(q',P') \<in> PS\<close> by force
      have "p = pR2' @ (drop (length pR2') p)" using \<open>pR2' = take (length pR2') p\<close>
        by (metis append_take_drop_id)

      have "pR2' \<in> tps q" and "[] \<in> tps q'" and "target q pR2' \<in> rd_targets (q', [])" and "q' \<in> rd_targets (q, pR2')"
        using t11[OF \<open>q \<in> fst ` PS\<close> \<open>(p, d) \<in> m_traversal_paths_with_witness M q repetition_sets m\<close> 
                     \<open>p = pR2' @ (drop (length pR2') p)\<close> \<open>q' \<in> fst ` PS\<close> \<open>target q pR2' \<in> fst d\<close> 
                     \<open>q' \<in> fst d\<close> \<open>target q pR2' \<noteq> q'\<close>]
        by simp+


      have "p_io pP @ p_io pR2' \<in> L M'"
        using language_prefix_append[OF \<open>p_io pP @ p_io p \<in> L M'\<close>, of "length pR2'"]
        using \<open>pR2' = take (length pR2') p\<close> by simp
      have "pass_separator_ATC M' A qT t1"
        using pass3[OF \<open>(q, P) \<in> PS\<close> \<open>path P (initial P) pP\<close> \<open>target (initial P) pP = q\<close> \<open>pR2' \<in> tps q\<close> 
                       \<open>p_io pP @ p_io pR2' \<in> L M'\<close> \<open>q' \<in> rd_targets (q, pR2')\<close>, of A t2 t1]
              \<open>(A, t2, t1) \<in> separators (q'', q')\<close> \<open>qT \<in> io_targets M' (p_io pR2) (FSM.initial M')\<close> 
        unfolding \<open>target q pR2' = q''\<close> \<open>pR2 = pP @ pR2'\<close> by auto

      have "pass_separator_ATC M' A qT t2"
        using pass3[OF \<open>(q', P') \<in> PS\<close> \<open>path P' (FSM.initial P') pR1\<close> \<open>target (FSM.initial P') pR1 = q'\<close> 
                       \<open>[] \<in> tps q'\<close> _ \<open>target q pR2' \<in> rd_targets (q', [])\<close>, of A t1 t2 qT]
              \<open>(A, t1, t2) \<in> separators (q', q'')\<close> \<open>qT \<in> io_targets M' (p_io pR1) (FSM.initial M')\<close> \<open>p_io pR1 \<in> L M'\<close>
        unfolding \<open>target q pR2' = q''\<close> by auto

      have "qT \<noteq> qT"
        using pass_separator_ATC_reduction_distinction[OF \<open>observable M\<close> \<open>observable M'\<close> \<open>inputs M' = inputs M\<close>
                                                          \<open>pass_separator_ATC M' A qT t1\<close> \<open>pass_separator_ATC M' A qT t2\<close> 
                                                          \<open>q'' \<in> states M\<close> \<open>q' \<in> states M\<close> _ \<open>qT \<in> states M'\<close> \<open>qT \<in> states M'\<close> 
                                                          \<open>is_separator M q'' q' A t2 t1\<close> \<open>completely_specified M'\<close>]
              \<open>q' \<noteq> q''\<close> by simp
      then show False
        by simp
    next
      case d

      then have "pR1 \<notin> ?R1" and "pR2 \<notin> ?R2"
        by auto
                
      obtain P' where "(q', P') \<in> PS"
                      "path P' (FSM.initial P') pR1"
                      "target (FSM.initial P') pR1 = q'"
                      "path M (FSM.initial M) pR1" 
                      "target (FSM.initial M) pR1 = q'" 
                      "p_io pR1 \<in> L M'"
                      "RP M q q' pP p PS M' = insert pR1 (R M q q' pP p)"
        using RP_from_R_inserted[OF t2 pass1 \<open>completely_specified M'\<close> \<open>inputs M' = inputs M\<close> 
                                    \<open>pR1 \<in> ?RP1\<close> \<open>pR1 \<notin> ?R1\<close>, of "\<lambda> q P io x y y' . q" "\<lambda> q P io x y y' . y"] 
        by blast

      have "q' \<in> snd d"
        by (metis IntI \<open>(q', P') \<in> PS\<close> \<open>d \<in> set repetition_sets\<close> assms(13) fst_eqD image_eqI t8')

      obtain P'' where "(q'', P'') \<in> PS"
                      "path P'' (FSM.initial P'') pR2"
                      "target (FSM.initial P'') pR2 = q''"
                      "path M (FSM.initial M) pR2" 
                      "target (FSM.initial M) pR2 = q''" 
                      "p_io pR2 \<in> L M'"
                      "RP M q q'' pP p PS M' = insert pR2 (R M q q'' pP p)"
        using RP_from_R_inserted[OF t2 pass1 \<open>completely_specified M'\<close> \<open>inputs M' = inputs M\<close> \<open>pR2 \<in> ?RP2\<close> \<open>pR2 \<notin> ?R2\<close>, 
                                 of "\<lambda> q P io x y y' . q" "\<lambda> q P io x y y' . y"] 
        by blast

      have "q'' \<in> snd d"
        by (metis IntI \<open>(q'', P'') \<in> PS\<close> \<open>d \<in> set repetition_sets\<close> assms(14) fst_eqD image_eqI t8')

      have "[] \<in> tps q'" and "[] \<in> tps q''" and "q' \<in> rd_targets (q'', [])" and "q'' \<in> rd_targets (q', [])"
        using t12[OF \<open>q \<in> fst ` PS\<close> \<open>(p, d) \<in> m_traversal_paths_with_witness M q repetition_sets m\<close> \<open>q' \<noteq> q''\<close> \<open>q' \<in> snd d\<close> \<open>q'' \<in> snd d\<close>]
        by simp+


      have "pass_separator_ATC M' A qT t1"
        using pass3[OF \<open>(q'', P'') \<in> PS\<close> \<open>path P'' (initial P'') pR2\<close> \<open>target (initial P'') pR2 = q''\<close> 
                       \<open>[] \<in> tps q''\<close> _ \<open>q' \<in> rd_targets (q'', [])\<close>, of A t2 t1 qT]
              \<open>p_io pR2 \<in> L M'\<close> \<open>(A, t2, t1) \<in> separators (q'', q')\<close> \<open>qT \<in> io_targets M' (p_io pR2) (FSM.initial M')\<close> 
        by auto
      
      have "pass_separator_ATC M' A qT t2"
        using pass3[OF \<open>(q', P') \<in> PS\<close> \<open>path P' (initial P') pR1\<close> \<open>target (initial P') pR1 = q'\<close> 
                       \<open>[] \<in> tps q'\<close> _ \<open>q'' \<in> rd_targets (q', [])\<close>, of A t1 t2 qT]
              \<open>p_io pR1 \<in> L M'\<close> \<open>(A, t1, t2) \<in> separators (q', q'')\<close> \<open>qT \<in> io_targets M' (p_io pR1) (FSM.initial M')\<close> 
        by auto

      have "qT \<noteq> qT"
        using pass_separator_ATC_reduction_distinction[OF \<open>observable M\<close> \<open>observable M'\<close> 
                                                          \<open>inputs M' = inputs M\<close> \<open>pass_separator_ATC M' A qT t1\<close>
                                                          \<open>pass_separator_ATC M' A qT t2\<close> \<open>q'' \<in> states M\<close> 
                                                          \<open>q' \<in> states M\<close> _ \<open>qT \<in> states M'\<close> \<open>qT \<in> states M'\<close> 
                                                          \<open>is_separator M q'' q' A t2 t1\<close> \<open>completely_specified M'\<close>]
              \<open>q' \<noteq> q''\<close> by simp
      then show False
        by simp
    qed
  qed
qed




lemma passes_test_suite_exhaustiveness :
  assumes "passes_test_suite M (Test_Suite prs tps rd_targets separators) M'"
  and     "implies_completeness (Test_Suite prs tps rd_targets separators) M m"
  and     "observable M" 
  and     "observable M'"
  and     "inputs M' = inputs M"
  and     "inputs M \<noteq> {}"
  and     "completely_specified M"
  and     "completely_specified M'"
  and     "size M' \<le> m"
shows     "L M' \<subseteq> L M"
proof (rule ccontr)
  assume "\<not> L M' \<subseteq> L M"

  (* sufficiency properties *)

  obtain repetition_sets where repetition_sets_def: "implies_completeness_for_repetition_sets (Test_Suite prs tps rd_targets separators) M m repetition_sets"
    using assms(2) unfolding implies_completeness_def by blast


  have t1: "(initial M, initial_preamble M) \<in> prs" 
    using implies_completeness_for_repetition_sets_simps(1)[OF repetition_sets_def] 
    by assumption
  have t2: "\<And> q P. (q, P) \<in> prs \<Longrightarrow> is_preamble P M q"
    using implies_completeness_for_repetition_sets_simps(2)[OF repetition_sets_def] 
    by blast
  have t3: "\<And> q1 q2 A d1 d2. (A, d1, d2) \<in> separators (q1, q2) \<Longrightarrow> (A, d2, d1) \<in> separators (q2, q1) \<and> is_separator M q1 q2 A d1 d2"
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
  and  t9: "\<And> d q1 q2. d \<in> set repetition_sets \<Longrightarrow> q1 \<in> fst d \<Longrightarrow> q2 \<in> fst d \<Longrightarrow> q1 \<noteq> q2 \<Longrightarrow> separators (q1, q2) \<noteq> {}"
    using implies_completeness_for_repetition_sets_simps(5,6)[OF repetition_sets_def] 
    by blast+

  have t10: "\<And> q p d p1 p2 p3.
              q \<in> fst ` prs \<Longrightarrow>
              (p, d) \<in> m_traversal_paths_with_witness M q repetition_sets m \<Longrightarrow>
              p = p1 @ p2 @ p3 \<Longrightarrow>
              p2 \<noteq> [] \<Longrightarrow>
              target q p1 \<in> fst d \<Longrightarrow>
              target q (p1 @ p2) \<in> fst d \<Longrightarrow>
              target q p1 \<noteq> target q (p1 @ p2) \<Longrightarrow>
              p1 \<in> tps q \<and> p1 @ p2 \<in> tps q \<and> target q p1 \<in> rd_targets (q, p1 @ p2) \<and> target q (p1 @ p2) \<in> rd_targets (q, p1)"
    using implies_completeness_for_repetition_sets_simps(8)[OF repetition_sets_def] by assumption

  have t11: "\<And> q p d p1 p2 q'.
              q \<in> fst ` prs \<Longrightarrow>
              (p, d) \<in> m_traversal_paths_with_witness M q repetition_sets m \<Longrightarrow>
              p = p1 @ p2 \<Longrightarrow>
              q' \<in> fst ` prs \<Longrightarrow>
              target q p1 \<in> fst d \<Longrightarrow>
              q' \<in> fst d \<Longrightarrow> 
              target q p1 \<noteq> q' \<Longrightarrow> 
              p1 \<in> tps q \<and> [] \<in> tps q' \<and> target q p1 \<in> rd_targets (q', []) \<and> q' \<in> rd_targets (q, p1)"
    using implies_completeness_for_repetition_sets_simps(9)[OF repetition_sets_def] by assumption
  
  have t12: "\<And> q p d q1 q2.
              q \<in> fst ` prs \<Longrightarrow>
              (p, d) \<in> m_traversal_paths_with_witness M q repetition_sets m \<Longrightarrow>
              q1 \<noteq> q2 \<Longrightarrow>
              q1 \<in> snd d \<Longrightarrow> 
              q2 \<in> snd d \<Longrightarrow> 
              [] \<in> tps q1 \<and> [] \<in> tps q2 \<and> q1 \<in> rd_targets (q2, []) \<and> q2 \<in> rd_targets (q1, [])"
    using implies_completeness_for_repetition_sets_simps(10)[OF repetition_sets_def] by assumption
  


  (* pass properties *)

  have pass1: "\<And> q P io x y y' . (q,P) \<in> prs \<Longrightarrow> io@[(x,y)] \<in> L P \<Longrightarrow> io@[(x,y')] \<in> L M' \<Longrightarrow> io@[(x,y')] \<in> L P" 
    using \<open>passes_test_suite M (Test_Suite prs tps rd_targets separators) M'\<close>
    unfolding passes_test_suite.simps
    by meson 

  have pass2: "\<And> q P pP ioT pT x y y' . (q,P) \<in> prs \<Longrightarrow> path P (initial P) pP \<Longrightarrow> target (initial P) pP = q \<Longrightarrow> pT \<in> tps q \<Longrightarrow> ioT@[(x,y)] \<in> set (prefixes (p_io pT)) \<Longrightarrow> (p_io pP)@ioT@[(x,y')] \<in> L M' \<Longrightarrow> (\<exists> pT' . pT' \<in> tps q \<and> ioT@[(x,y')] \<in> set (prefixes (p_io pT')))"
    using \<open>passes_test_suite M (Test_Suite prs tps rd_targets separators) M'\<close>
    unfolding passes_test_suite.simps 
    by blast

  have pass3: "\<And> q P pP pT q' A d1 d2 qT . (q,P) \<in> prs \<Longrightarrow> path P (initial P) pP \<Longrightarrow> target (initial P) pP = q \<Longrightarrow> pT \<in> tps q \<Longrightarrow> (p_io pP)@(p_io pT) \<in> L M' \<Longrightarrow> q' \<in> rd_targets (q,pT) \<Longrightarrow> (A,d1,d2) \<in> separators (target q pT, q') \<Longrightarrow> qT \<in> io_targets M' ((p_io pP)@(p_io pT)) (initial M') \<Longrightarrow> pass_separator_ATC M' A qT d2"  
    using \<open>passes_test_suite M (Test_Suite prs tps rd_targets separators) M'\<close>
    unfolding passes_test_suite.simps 
    by blast


  (* seq to failure *)


  obtain pP io where "minimal_sequence_to_failure_extending_preamble_path M M' prs pP io"
    using minimal_sequence_to_failure_extending_preamble_ex[OF t1 \<open>\<not> L M' \<subseteq> L M\<close>] 
    by blast

  then have "sequence_to_failure_extending_preamble_path M M' prs pP io" 
            "\<And> io'. sequence_to_failure_extending_preamble_path M M' prs pP io' \<Longrightarrow> length io \<le> length io'"
    unfolding minimal_sequence_to_failure_extending_preamble_path_def
    by blast+

  obtain q P where "q \<in> states M"
               and "(q,P) \<in> prs"
               and "path P (initial P) pP"
               and "target (initial P) pP = q"
               and "((p_io pP) @ butlast io) \<in> L M" 
               and "((p_io pP) @ io) \<notin> L M"
               and "((p_io pP) @ io) \<in> L M'"
    using \<open>sequence_to_failure_extending_preamble_path M M' prs pP io\<close>
    unfolding sequence_to_failure_extending_preamble_path_def 
    by blast

  let ?xF = "fst (last io)"
  let ?yF = "snd (last io)"
  let ?xyF = "(?xF,?yF)"
  let ?ioF = "butlast io"
  have "io \<noteq> []"
    using \<open>((p_io pP) @ io) \<notin> L M\<close> \<open>((p_io pP) @ butlast io) \<in> L M\<close> by auto
  then have "io = ?ioF@[?xyF]"
    by auto

  have "?xF \<in> inputs M'"
    using language_io(1)[OF \<open>((p_io pP) @ io) \<in> L M'\<close>, of ?xF ?yF] \<open>io \<noteq> []\<close> by auto 
  then have "?xF \<in> inputs M"
    using \<open>inputs M' = inputs M\<close> by simp

  have "q \<in> fst ` prs"
    using \<open>(q,P) \<in> prs\<close> by force
  have "is_preamble P M q"
    using \<open>(q,P) \<in> prs\<close> t2 by blast
  then have "q \<in> states M"
    unfolding is_preamble_def
    by (metis \<open>path P (FSM.initial P) pP\<close> \<open>target (FSM.initial P) pP = q\<close> path_target_is_state submachine_path) 

  have "initial P = initial M"
    using \<open>is_preamble P M q\<close> unfolding is_preamble_def by auto
  have "path M (initial M) pP"
    using \<open>is_preamble P M q\<close> unfolding is_preamble_def using submachine_path_initial
    using \<open>path P (FSM.initial P) pP\<close> by blast
  have "target (initial M) pP = q"
    using \<open>target (initial P) pP = q\<close> unfolding \<open>initial P = initial M\<close> by assumption


  (* io must be a proper extension of some m-traversal path, as all m-traversal paths pass *)
  obtain pM dM ioEx where "(pM,dM) \<in> m_traversal_paths_with_witness M q repetition_sets m"
                    and   "io = (p_io pM)@ioEx"
                    and   "ioEx \<noteq> []"
  proof -
    
    obtain pF where "path M q pF" and "p_io pF = ?ioF"
      using observable_path_suffix[OF \<open>((p_io pP) @ ?ioF) \<in> L M\<close> \<open>path M (initial M) pP\<close> \<open>observable M\<close> ]
      unfolding \<open>target (initial M) pP = q\<close>
      by blast

    obtain tM where "tM \<in> transitions M" and "t_source tM = target q pF" and "t_input tM = ?xF"
      using \<open>?xF \<in> inputs M\<close> path_target_is_state[OF \<open>path M q pF\<close>]
            \<open>completely_specified M\<close>
      unfolding completely_specified.simps
      by blast

    then have "path M q (pF@[tM])"
      using \<open>path M q pF\<close> path_append_transition by simp

    show ?thesis proof (cases "find (\<lambda>d. Suc (m - card (snd d)) \<le> length (filter (\<lambda>t. t_target t \<in> fst d) (pF@[tM]))) repetition_sets")
      case None

      (* if no repetition_sets witness exists for (pF@[tM]), then it is a proper prefix of some m-traversal path and hence also in L M, providing a contradiction*)

      obtain pF' d' where "((pF@[tM]) @ pF', d') \<in> m_traversal_paths_with_witness M q repetition_sets m"
        using m_traversal_path_extension_exist[OF \<open>completely_specified M\<close> \<open>q \<in> states M\<close> \<open>inputs M \<noteq> {}\<close> t5 t8 \<open>path M q (pF@[tM])\<close> None]
        by blast
      then have "(pF@[tM]) @ pF' \<in> tps q"
        using t6[OF \<open>q \<in> fst ` prs\<close>] by force

      have "(p_io pF) @ [(?xF,t_output tM)] \<in> set (prefixes (p_io ((pF@[tM])@pF')))"
        using \<open>t_input tM = ?xF\<close>
        unfolding prefixes_set by auto

      have "p_io pP @ p_io pF @ [?xyF] \<in> L M'"
        using \<open>((p_io pP) @ io) \<in> L M'\<close> unfolding \<open>p_io pF = ?ioF\<close> \<open>io = ?ioF@[?xyF]\<close>[symmetric] by assumption

      obtain pT' where "pT' \<in> tps q" 
                 and   "p_io pF @ [(fst (last io), snd (last io))] \<in> set (prefixes (p_io pT'))"
        using pass2[OF \<open>(q,P) \<in> prs\<close> \<open>path P (initial P) pP\<close> \<open>target (initial P) pP = q\<close> \<open>(pF@[tM]) @ pF' \<in> tps q\<close> 
                       \<open>(p_io pF) @ [(?xF,t_output tM)] \<in> set (prefixes (p_io ((pF@[tM])@pF')))\<close> \<open>p_io pP @ p_io pF @ [?xyF] \<in> L M'\<close>]
        by blast

      have "path M q pT'"
      proof -
        obtain pT'' d'' where "(pT'@pT'', d'') \<in> m_traversal_paths_with_witness M q repetition_sets m"
          using \<open>pT' \<in> tps q\<close> t6[OF \<open>q \<in> fst ` prs\<close>] 
          by blast
        then have "path M q (pT'@pT'')"
          using m_traversal_paths_with_witness_set[OF t5 t8 \<open>q \<in> states M\<close>] 
          by force
        then show ?thesis 
          by auto
      qed
      then have "path M (initial M) (pP@pT')"
        using \<open>path M (initial M) pP\<close> \<open>target (initial M) pP = q\<close> by auto
      then have "(p_io (pP@pT')) \<in> L M"
        unfolding LS.simps by blast
      then have "(p_io pP)@(p_io pT') \<in> L M"
        by auto
      


      have "io \<in> set (prefixes (p_io pT'))"
        using \<open>p_io pF @ [(fst (last io), snd (last io))] \<in> set (prefixes (p_io pT'))\<close>
        unfolding \<open>p_io pF = ?ioF\<close> \<open>io = ?ioF@[?xyF]\<close>[symmetric] by assumption
      then obtain io' where "p_io pT' = io @ io'"
        unfolding prefixes_set by moura
      
      have " p_io pP @ io \<in> L M"
        using \<open>(p_io pP)@(p_io pT') \<in> L M\<close> 
        unfolding \<open>p_io pT' = io @ io'\<close>
        unfolding append.assoc[symmetric]
        using language_prefix[of "p_io pP @ io" io', of M "initial M"] 
        by blast
      
      then show ?thesis
        using \<open>(p_io pP) @ io \<notin> L M\<close> by simp
    next
      case (Some d)

      (* get the shortest prefix of pF that still has a RepSet witness *)

      let ?ps = "{ p1 . \<exists> p2 . (pF@[tM]) = p1 @ p2 \<and> find (\<lambda>d. Suc (m - card (snd d)) \<le> length (filter (\<lambda>t. t_target t \<in> fst d) p1)) repetition_sets \<noteq> None}"

      have "finite ?ps"
      proof -
        have "?ps \<subseteq> set (prefixes (pF@[tM]))"
          unfolding prefixes_set by force
        moreover have "finite (set (prefixes (pF@[tM])))"
          by simp
        ultimately show ?thesis
          by (simp add: finite_subset) 
      qed
      moreover have "?ps \<noteq> {}"
      proof -
        have "pF @ [tM] = (pF @ [tM]) @ [] \<and> find (\<lambda>d. Suc (m - card (snd d)) \<le> length (filter (\<lambda>t. t_target t \<in> fst d) (pF @ [tM]))) repetition_sets \<noteq> None"
          using Some by auto
        then have "(pF@[tM]) \<in> ?ps"
          by blast
        then show ?thesis by blast
      qed
      ultimately obtain pMin where "pMin \<in> ?ps" and "\<And> p' . p' \<in> ?ps \<Longrightarrow> length pMin \<le> length p'"
        by (meson leI min_length_elem) 

      obtain pMin' dMin where "(pF@[tM]) = pMin @ pMin'"
                          and "find (\<lambda>d. Suc (m - card (snd d)) \<le> length (filter (\<lambda>t. t_target t \<in> fst d) pMin)) repetition_sets = Some dMin"
        using \<open>pMin \<in> ?ps\<close> by blast
      then have "path M q pMin"
        using \<open>path M q (pF@[tM])\<close> by auto

      moreover have "(\<forall>p' p''. pMin = p' @ p'' \<and> p'' \<noteq> [] \<longrightarrow> find (\<lambda>d. Suc (m - card (snd d)) \<le> length (filter (\<lambda>t. t_target t \<in> fst d) p')) repetition_sets = None)"
      proof -
        have "\<And> p' p''. pMin = p' @ p'' \<Longrightarrow> p'' \<noteq> [] \<Longrightarrow> find (\<lambda>d. Suc (m - card (snd d)) \<le> length (filter (\<lambda>t. t_target t \<in> fst d) p')) repetition_sets = None"
        proof -
          fix p' p'' assume "pMin = p' @ p''" and "p'' \<noteq> []"
          show "find (\<lambda>d. Suc (m - card (snd d)) \<le> length (filter (\<lambda>t. t_target t \<in> fst d) p')) repetition_sets = None"
          proof (rule ccontr) 
            assume "find (\<lambda>d. Suc (m - card (snd d)) \<le> length (filter (\<lambda>t. t_target t \<in> fst d) p')) repetition_sets \<noteq> None"
            then have "p' \<in> ?ps"
              using \<open>(pF@[tM]) = pMin @ pMin'\<close> unfolding \<open>pMin = p' @ p''\<close> append.assoc by blast
            
            have "length p' < length pMin"
              using \<open>pMin = p' @ p''\<close> \<open>p'' \<noteq> []\<close> by auto
            then show "False"
              using \<open>\<And> p' . p' \<in> ?ps \<Longrightarrow> length pMin \<le> length p'\<close>[OF \<open>p' \<in> ?ps\<close>] by simp
          qed
        qed
        then show ?thesis by blast
      qed
      
      ultimately have "(pMin,dMin) \<in> m_traversal_paths_with_witness M q repetition_sets m"
        using \<open>find (\<lambda>d. Suc (m - card (snd d)) \<le> length (filter (\<lambda>t. t_target t \<in> fst d) pMin)) repetition_sets = Some dMin\<close>
              m_traversal_paths_with_witness_set[OF t5 t8 \<open>q \<in> states M\<close>, of m]
        by blast
      then have "pMin \<in> tps q"
        using t6[OF \<open>q \<in> fst ` prs\<close>]
        by force
  
      show ?thesis proof (cases "pMin = (pF@[tM])")
        (* if the m-traversal path is not shorter than io, then again the failure is observed *)
        case True 
        then have "?ioF @ [(?xF, t_output tM)] \<in> set (prefixes (p_io pMin))"
          using \<open>p_io pF = ?ioF\<close> \<open>t_input tM = ?xF\<close> unfolding prefixes_set by force

        obtain pMinF where "pMinF \<in> tps q" and "io \<in> set (prefixes (p_io pMinF))"
          using pass2[OF \<open>(q,P) \<in> prs\<close> \<open>path P (initial P) pP\<close> \<open>target (initial P) pP = q\<close> \<open>pMin \<in> tps q\<close> \<open>?ioF @ [(?xF, t_output tM)] \<in> set (prefixes (p_io pMin))\<close>, of ?yF]
          using \<open>p_io pP @ io \<in> L M'\<close>
          unfolding \<open>io = ?ioF@[?xyF]\<close>[symmetric]
          by blast

        have "path M q pMinF"
        proof -
          obtain pT'' d'' where "(pMinF@pT'', d'') \<in> m_traversal_paths_with_witness M q repetition_sets m"
            using \<open>pMinF \<in> tps q\<close> t6[OF \<open>q \<in> fst ` prs\<close>] by blast
          then have "path M q (pMinF@pT'')"
            using m_traversal_paths_with_witness_set[OF t5 t8 \<open>q \<in> states M\<close>] 
            by force
          then show ?thesis by auto
        qed
        then have "path M (initial M) (pP@pMinF)"
          using \<open>path M (initial M) pP\<close> \<open>target (initial M) pP = q\<close> by auto
        then have "(p_io (pP@pMinF)) \<in> L M"
          unfolding LS.simps by blast
        then have "(p_io pP)@(p_io pMinF) \<in> L M"
          by auto
        
        obtain io' where "p_io pMinF = io @ io'"
          using \<open>io \<in> set (prefixes (p_io pMinF))\<close> unfolding prefixes_set by moura
        
        have " p_io pP @ io \<in> L M"
          using \<open>(p_io pP)@(p_io pMinF) \<in> L M\<close> 
          unfolding \<open>p_io pMinF = io @ io'\<close>
          unfolding append.assoc[symmetric]
          using language_prefix[of "p_io pP @ io" io', of M "initial M"] 
          by blast        
        then show ?thesis
          using \<open>(p_io pP) @ io \<notin> L M\<close> by simp
      next
        case False
        then obtain pMin'' where "pF = pMin @ pMin''"
          using \<open>(pF@[tM]) = pMin @ pMin'\<close>
          by (metis butlast_append butlast_snoc) 
        then have "io = (p_io pMin) @ (p_io pMin'') @ [?xyF]"
          using \<open>io = ?ioF @ [?xyF]\<close> \<open>p_io pF = ?ioF\<close>
          by (metis (no_types, lifting) append_assoc map_append)
        then show ?thesis 
          using that[OF \<open>(pMin,dMin) \<in> m_traversal_paths_with_witness M q repetition_sets m\<close>, of "(p_io pMin'') @ [?xyF]"] 
          by auto
      qed
    qed
  qed


  (* collect length properties on pM to ultimately show that M' must have at least m+1 states *)

  have "p_io pP @ p_io pM \<in> L M'"
    using \<open>((p_io pP) @ io) \<in> L M'\<close> unfolding \<open>io = (p_io pM)@ioEx\<close> append.assoc[symmetric]
    using language_prefix[of "p_io pP @ p_io pM" ioEx M' "initial M'"] by blast

  have no_shared_targets_for_distinct_states : "\<And> q' q'' pR1 pR2. q' \<noteq> q'' \<Longrightarrow>
                                                  q' \<in> fst dM \<Longrightarrow>
                                                  q'' \<in> fst dM \<Longrightarrow>
                                                  pR1 \<in> RP M q q' pP pM prs M' \<Longrightarrow>
                                                  pR2 \<in> RP M q q'' pP pM prs M' \<Longrightarrow> 
                                                  io_targets M' (p_io pR1) (initial M') \<inter> io_targets M' (p_io pR2) (initial M') = {}"
    using passes_test_suite_exhaustiveness_helper_1[OF \<open>completely_specified M'\<close> \<open>inputs M' = inputs M\<close> \<open>observable M\<close> \<open>observable M'\<close> \<open>(q,P) \<in> prs\<close> \<open>path P (initial P) pP\<close> \<open>target (FSM.initial P) pP = q\<close> \<open>p_io pP @ p_io pM \<in> L M'\<close> \<open>(pM, dM) \<in> m_traversal_paths_with_witness M q repetition_sets m\<close> repetition_sets_def \<open>passes_test_suite M (Test_Suite prs tps rd_targets separators) M'\<close>]
    by blast



  have "path M q pM"
  and  "find (\<lambda>d. Suc (m - card (snd d)) \<le> length (filter (\<lambda>t. t_target t \<in> fst d) pM)) repetition_sets = Some dM"
    using \<open>(pM,dM) \<in> m_traversal_paths_with_witness M q repetition_sets m\<close>
    using m_traversal_paths_with_witness_set[OF t5 t8 \<open>q \<in> states M\<close>, of m] by force+
  then have "path M (target (FSM.initial M) pP) pM"
    unfolding \<open>(target (FSM.initial M) pP) = q\<close> by simp

  have "dM \<in> set repetition_sets"
    using find_set[OF \<open>find (\<lambda>d. Suc (m - card (snd d)) \<le> length (filter (\<lambda>t. t_target t \<in> fst d) pM)) repetition_sets = Some dM\<close>] by assumption
  have "Suc (m - card (snd dM)) \<le> length (filter (\<lambda>t. t_target t \<in> fst dM) pM)"
    using find_condition[OF \<open>find (\<lambda>d. Suc (m - card (snd d)) \<le> length (filter (\<lambda>t. t_target t \<in> fst d) pM)) repetition_sets = Some dM\<close>] by assumption

  obtain ioX where "butlast io = (p_io pM)@ioX"
    using \<open>io = (p_io pM)@ioEx\<close>
    by (simp add: \<open>ioEx \<noteq> []\<close> butlast_append) 


  have RP_card : "\<And> q' . card (\<Union>pR\<in>RP M (target (FSM.initial M) pP) q' pP pM prs M'. io_targets M' (p_io pR) (FSM.initial M')) = card (RP M (target (FSM.initial M) pP) q' pP pM prs M')"
  and  RP_targets: "\<And> q' pR . pR \<in> RP M (target (FSM.initial M) pP) q' pP pM prs M' \<Longrightarrow> \<exists>q. io_targets M' (p_io pR) (FSM.initial M') = {q}"
  and  no_shared_targets_for_identical_states: "\<And> q' pR1 pR2 . pR1 \<in> RP M (target (FSM.initial M) pP) q' pP pM prs M' \<Longrightarrow> pR2 \<in> RP M (target (FSM.initial M) pP) q' pP pM prs M' \<Longrightarrow> pR1 \<noteq> pR2 \<Longrightarrow> io_targets M' (p_io pR1) (FSM.initial M') \<inter> io_targets M' (p_io pR2) (FSM.initial M') = {}"
    using RP_count[OF \<open>minimal_sequence_to_failure_extending_preamble_path M M' prs pP io\<close> \<open>observable M\<close> \<open>observable M'\<close> t2 \<open>path M (target (FSM.initial M) pP) pM\<close> \<open>butlast io = (p_io pM)@ioX\<close> pass1 \<open>completely_specified M'\<close> \<open>inputs M' = inputs M\<close>, of "\<lambda> q P io x y y' . q" "\<lambda> q P io x y y' . y"]
    by blast+

  have snd_dM_prop: "\<And> q' . q' \<in> snd dM \<Longrightarrow> (\<Union> pR \<in> (RP M q q' pP pM prs M') . io_targets M' (p_io pR) (initial M')) \<noteq> (\<Union> pR \<in> (R M q q' pP pM) . io_targets M' (p_io pR) (initial M'))"
  proof -
    fix q' assume "q' \<in> snd dM"

    let ?RP = "(RP M q q' pP pM prs M')"
    let ?R  = "(R M q q' pP pM)"
    let ?P  = "\<lambda> pP' . \<exists>P'. (q', P') \<in> prs \<and> path P' (FSM.initial P') pP' \<and> target (FSM.initial P') pP' = q' \<and> p_io pP' \<in> L M'"

    
    obtain PQ where "(q',PQ) \<in> prs"
      using \<open>q' \<in> snd dM\<close> t8'[OF \<open>dM \<in> set repetition_sets\<close>] by auto
    then have "is_preamble PQ M q'" and "\<exists>P'. (q', P') \<in> prs"
      using t2 by blast+

    obtain pq where "path PQ (initial PQ) pq" and "target (initial PQ) pq = q'" and "p_io pq \<in> L M'"
      using preamble_pass_path[OF \<open>is_preamble PQ M q'\<close> pass1[OF \<open>(q',PQ) \<in> prs\<close>] \<open>completely_specified M'\<close> \<open>inputs M' = inputs M\<close>] 
      by force
    then have "\<exists> pP' . ?P pP'"
      using \<open>(q',PQ) \<in> prs\<close> by blast

    define pPQ where pPQ_def: "pPQ = (SOME pP'. ?P pP')"

    have "?P pPQ"
      unfolding pPQ_def using someI_ex[OF \<open>\<exists> pP' . ?P pP'\<close>] by assumption
    then obtain PQ' where "(q',PQ') \<in> prs" 
                      and "path PQ' (initial PQ') pPQ" 
                      and "target (initial PQ') pPQ = q'" 
                      and "p_io pPQ \<in> L M'"
      by blast

    have "?RP = insert pPQ (R M q q' pP pM)"
      unfolding RP_def pPQ_def
      using \<open>\<exists>P'. (q', P') \<in> prs\<close> by auto

    obtain pPQ' where "path M' (initial M') pPQ'" and "p_io pPQ' = p_io pPQ"
      using \<open>p_io pPQ \<in> L M'\<close> by auto

    then have "io_targets M' (p_io pPQ) (initial M') = {target (initial M') pPQ'}"
      using \<open>observable M'\<close> by (metis (mono_tags, lifting) observable_path_io_target) 
    
    moreover have "target (initial M') pPQ' \<notin> (\<Union> (image (\<lambda> pR . io_targets M' (p_io pR) (initial M')) ?R))"
    proof 
      assume "target (initial M') pPQ' \<in> (\<Union> (image (\<lambda> pR . io_targets M' (p_io pR) (initial M')) ?R))"
      then obtain pR where "pR \<in> ?R" and "target (initial M') pPQ' \<in> io_targets M' (p_io pR) (initial M')"
        by blast

      obtain pR' where "pR = pP@pR'"
        using R_component_ob[OF \<open>pR \<in> ?R\<close>] by blast
      then have "pP@pR' \<in> ?R"
        using \<open>pR \<in> ?R\<close> by simp
      have "pR' = take (length pR') pM" 
       and "length pR' \<le> length pM" 
       and "t_target (pM ! (length pR' - 1)) = q'" 
       and "pR' \<noteq> []"
        using R_component[OF \<open>pP@pR' \<in> ?R\<close>] by auto

      
      (* get the full path along (butlast io) in M, of which p is a (possibly proper) prefix *)

      obtain pX where "path M (target (initial M) pP) (pM@pX)" and "p_io (pM@pX) = butlast io"
      proof -
        have "p_io pP @ p_io pM @ ioX \<in> L M"
          using \<open>((p_io pP) @ butlast io) \<in> L M\<close> 
          unfolding \<open>butlast io = p_io pM @ ioX\<close> 
          by assumption
    
        obtain p1 p23 where "path M (FSM.initial M) p1" 
                        and "path M (target (FSM.initial M) p1) p23" 
                        and "p_io p1 = p_io pP" 
                        and "p_io p23 = p_io pM @ ioX"
          using language_state_split[OF \<open>p_io pP @ p_io pM @ ioX \<in> L M\<close>] 
          by blast
    
        have "p1 = pP"
          using observable_path_unique[OF \<open>observable M\<close> \<open>path M (FSM.initial M) p1\<close> \<open>path M (FSM.initial M) pP\<close> \<open>p_io p1 = p_io pP\<close>]
          by assumption
        then have "path M (target (FSM.initial M) pP) p23"
          using \<open>path M (target (FSM.initial M) p1) p23\<close> by auto
        then have "p_io pM @ ioX \<in> LS M (target (initial M) pP)"
          using \<open>p_io p23 = p_io pM @ ioX\<close> language_state_containment by auto
    
        obtain p2 p3 where "path M (target (FSM.initial M) pP) p2" 
                       and "path M (target (target (FSM.initial M) pP) p2) p3"
                       and "p_io p2 = p_io pM" 
                       and "p_io p3 = ioX"
          using language_state_split[OF \<open>p_io pM @ ioX \<in> LS M (target (initial M) pP)\<close>] 
          by blast
    
        have "p2 = pM"
          using observable_path_unique[OF \<open>observable M\<close> \<open>path M (target (FSM.initial M) pP) p2\<close> 
                                          \<open>path M (target (FSM.initial M) pP) pM\<close> \<open>p_io p2 = p_io pM\<close>] 
          by assumption
        then have "path M (target (FSM.initial M) pP) (pM@p3)"
          using \<open>path M (target (FSM.initial M) pP) pM\<close> \<open>path M (target (target (FSM.initial M) pP) p2) p3\<close> 
          by auto
        moreover have "p_io (pM@p3) = butlast io"
          unfolding \<open>butlast io = p_io pM @ ioX\<close> using \<open>p_io p3 = ioX\<close> 
          by auto
        ultimately show ?thesis 
          using that[of p3] by simp
      qed

      obtain pP' pIO where "path M' (FSM.initial M') pP'" 
                       and "path M' (target (FSM.initial M') pP') pIO" 
                       and "p_io pP' = p_io pP"
                       and "p_io pIO = io"
        using language_state_split[OF \<open>((p_io pP) @ io) \<in> L M'\<close>] 
        by blast
  
      have "target (initial M') pP' \<in> io_targets M' (p_io pP) (FSM.initial M')"
        using \<open>path M' (FSM.initial M') pP'\<close> 
        unfolding \<open>p_io pP' = p_io pP\<close>[symmetric] 
        by auto

      let ?i = "length pR' - 1"
      have "?i < length pR'"
        using \<open>pR' \<noteq> []\<close> by auto
      have "?i < length (butlast io)"
        using \<open>pR' = take (length pR') pM\<close> \<open>pR' \<noteq> []\<close>
        unfolding \<open>p_io (pM@pX) = butlast io\<close>[symmetric] 
        using leI by fastforce 

      have "t_target ((pM @ pX) ! (length pR' - 1)) = q'"
        by (metis \<open>length pR' - 1 < length pR'\<close> \<open>length pR' \<le> length pM\<close> \<open>t_target (pM ! (length pR' - 1)) = q'\<close> 
              dual_order.strict_trans1 nth_append) 
      then have "(t_target ((pM @ pX) ! (length pR' - 1)), PQ') \<in> prs"
        using \<open>(q',PQ') \<in> prs\<close> by simp
      have "target (FSM.initial PQ') pPQ = t_target ((pM @ pX) ! (length pR' - 1))"
        using \<open>t_target ((pM @ pX) ! (length pR' - 1)) = q'\<close> \<open>target (FSM.initial PQ') pPQ = q'\<close> 
        by blast


      have "t_target (pIO ! ?i) \<notin> io_targets M' (p_io pPQ) (FSM.initial M')"
        using minimal_sequence_to_failure_extending_preamble_no_repetitions_with_other_preambles
          [OF \<open>minimal_sequence_to_failure_extending_preamble_path M M' prs pP io\<close> \<open>observable M\<close> \<open>
              path M (target (initial M) pP) (pM@pX)\<close> \<open>p_io (pM@pX) = butlast io\<close>
              \<open>target (initial M') pP' \<in> io_targets M' (p_io pP) (FSM.initial M')\<close> 
              \<open>path M' (target (FSM.initial M') pP') pIO\<close> \<open>p_io pIO = io\<close> t2
              \<open>?i < length (butlast io)\<close> \<open>(t_target ((pM @ pX) ! (length pR' - 1)), PQ') \<in> prs\<close>
              \<open>path PQ' (initial PQ') pPQ\<close> \<open>target (FSM.initial PQ') pPQ = t_target ((pM @ pX) ! (length pR' - 1))\<close>]
        by blast

      moreover have "io_targets M' (p_io pPQ) (FSM.initial M') = {target (initial M') pPQ'}"
        using \<open>path M' (initial M') pPQ'\<close>
        using \<open>io_targets M' (p_io pPQ) (FSM.initial M') = {target (FSM.initial M') pPQ'}\<close> \<open>p_io pPQ' = p_io pPQ\<close> by auto 
      moreover have "io_targets M' (p_io (pP@pR')) (FSM.initial M') = {t_target (pIO ! ?i)}"
      proof -
        have "(take (length pR') pIO) \<noteq> []" 
          using \<open>p_io pIO = io\<close> \<open>?i < length pR'\<close>
          using \<open>io = p_io pM @ ioEx\<close> \<open>pR' = take (length pR') pM\<close> by auto
        moreover have "pIO ! ?i = last (take (length pR') pIO)" 
          using \<open>p_io pIO = io\<close> \<open>?i < length pR'\<close>
          by (metis (no_types, lifting) \<open>io = p_io pM @ ioEx\<close> \<open>length pR' \<le> length pM\<close> \<open>pR' = take (length pR') pM\<close> 
                butlast.simps(1) last_conv_nth length_butlast length_map neq_iff nth_take take_le take_map)
        ultimately have "t_target (pIO ! ?i) = target (target (FSM.initial M') pP') (take (length pR') pIO)"
          unfolding target.simps visited_states.simps
          by (simp add: last_map) 
        then have "t_target (pIO ! ?i) = target (initial M') (pP' @ (take (length pR') pIO))"
          by auto 
          
        have "path M' (target (FSM.initial M') pP') (take (length pR') pIO)"
          using \<open>path M' (target (FSM.initial M') pP') pIO\<close>
          by (simp add: path_prefix_take) 
        then have "path M' (initial M') (pP' @ (take (length pR') pIO))"
          using \<open>path M' (FSM.initial M') pP'\<close> by auto
        moreover have "p_io (pP' @ (take (length pR') pIO)) = (p_io (pP@pR'))"
        proof -
          have "p_io (take (length pR') pIO) = p_io pR'"
            using \<open>p_io pIO = io\<close> \<open>pR' = take (length pR') pM\<close> \<open>p_io (pM@pX) = butlast io\<close> \<open>length pR' \<le> length pM\<close>
            by (metis (no_types, lifting) \<open>io = p_io pM @ ioEx\<close> length_map take_le take_map) 
          then show ?thesis
            using \<open>p_io pP' = p_io pP\<close> by auto
        qed
        ultimately have "io_targets M' (p_io (pP@pR')) (FSM.initial M') = {target (initial M') (pP' @ (take (length pR') pIO))}"
          by (metis (mono_tags, lifting) assms(4) observable_path_io_target)

        then show ?thesis
          unfolding \<open>t_target (pIO ! ?i) = target (initial M') (pP' @ (take (length pR') pIO))\<close>
          by assumption
      qed

      ultimately have "target (initial M') pPQ' \<notin> io_targets M' (p_io pR) (initial M')"
        unfolding \<open>pR = pP@pR'\<close> by auto
      then show "False"
        using \<open>target (initial M') pPQ' \<in> io_targets M' (p_io pR) (initial M')\<close>
        by blast
    qed

    ultimately have "io_targets M' (p_io pPQ) (initial M') \<inter> (\<Union> (image (\<lambda> pR . io_targets M' (p_io pR) (initial M')) ?R)) = {}"
      by force

    then show "(\<Union> pR \<in> (RP M q q' pP pM prs M') . io_targets M' (p_io pR) (initial M')) \<noteq> (\<Union> pR \<in> (R M q q' pP pM) . io_targets M' (p_io pR) (initial M'))"
      unfolding \<open>?RP = insert pPQ (R M q q' pP pM)\<close>
      using \<open>io_targets M' (p_io pPQ) (FSM.initial M') = {target (FSM.initial M') pPQ'}\<close> 
      by force
  qed

  (* create a function that separates the additional entries for the preambles in the RP sets of states in (snd dM) *)

  then obtain f where f_def: "\<And> q' . q' \<in> snd dM \<Longrightarrow> (RP M q q' pP pM prs M') = insert (f q') (R M q q' pP pM) \<and> (f q') \<notin> (R M q q' pP pM)"
  proof -
    define f where f_def : "f = (\<lambda> q' . SOME p . (RP M q q' pP pM prs M') = insert p (R M q q' pP pM) \<and> p \<notin> (R M q q' pP pM))"

    have "\<And> q' . q' \<in> snd dM \<Longrightarrow> (RP M q q' pP pM prs M') = insert (f q') (R M q q' pP pM) \<and> (RP M q q' pP pM prs M') \<noteq> (R M q q' pP pM)"
    proof -
      fix q' assume "q' \<in> snd dM"

      have "(\<Union>pR\<in>RP M q q' pP pM prs M'. io_targets M' (p_io pR) (FSM.initial M')) \<noteq> (\<Union>pR\<in>R M q q' pP pM. io_targets M' (p_io pR) (FSM.initial M'))"
        using snd_dM_prop[OF \<open>q' \<in> snd dM\<close>]
        by assumption
      then have "(RP M q q' pP pM prs M') \<noteq> (R M q q' pP pM)"
        by blast
      then obtain x where "(RP M q q' pP pM prs M') = insert x (R M q q' pP pM)"
        using RP_from_R[OF t2 pass1 \<open>completely_specified M'\<close> \<open>inputs M' = inputs M\<close>, of prs "\<lambda> q P io x y y' . q" "\<lambda> q P io x y y' . y" q q' pP pM]
        by force
      then have "x \<notin> (R M q q' pP pM)"
        using \<open>(RP M q q' pP pM prs M') \<noteq> (R M q q' pP pM)\<close>
        by auto 
      then have "\<exists> p . (RP M q q' pP pM prs M') = insert p (R M q q' pP pM) \<and> p \<notin> (R M q q' pP pM)"
        using \<open>(RP M q q' pP pM prs M') = insert x (R M q q' pP pM)\<close> by blast

      show "(RP M q q' pP pM prs M') = insert (f q') (R M q q' pP pM) \<and> (RP M q q' pP pM prs M') \<noteq> (R M q q' pP pM)"
        using someI_ex[OF \<open>\<exists> p . (RP M q q' pP pM prs M') = insert p (R M q q' pP pM) \<and> p \<notin> (R M q q' pP pM)\<close>]
        unfolding f_def by auto 
    qed

    then show ?thesis using that by force
  qed



  (* 
     combine counting results on RP (from R) to show that the path along pM collects 
     at least m+1 distinct io-targets (i.e. visites at least m+1 distinct states) in M' 
   *)


  have "(\<Sum> q' \<in> fst dM . card (\<Union> pR \<in> (RP M q q' pP pM prs M') . io_targets M' (p_io pR) (initial M'))) \<ge> Suc m"
  proof -

    have "\<And> nds . finite nds \<Longrightarrow> nds \<subseteq> fst dM \<Longrightarrow> (\<Sum> q' \<in> nds . card (RP M q q' pP pM prs M')) \<ge> length (filter (\<lambda>t. t_target t \<in> nds) pM) + card (nds \<inter> snd dM)"
    proof -
      fix nds assume "finite nds" and "nds \<subseteq> fst dM"
      then show "(\<Sum> q' \<in> nds . card (RP M q q' pP pM prs M')) \<ge> length (filter (\<lambda>t. t_target t \<in> nds) pM) + card (nds \<inter> snd dM)"
      proof induction
        case empty
        then show ?case by auto
      next
        case (insert q' nds)
        then have leq1: "length (filter (\<lambda>t. t_target t \<in> nds) pM) + card (nds \<inter> snd dM) \<le> (\<Sum>q'\<in>nds. card (RP M q q' pP pM prs M'))"
          by blast

        have p4: "(card (R M q q' pP pM)) = length (filter (\<lambda>t. t_target t = q') pM)" 
        using \<open>path M q pM\<close> proof (induction pM rule: rev_induct)
          case Nil
          then show ?case unfolding R_def by auto
        next
          case (snoc t pM)
          then have "path M q pM" and "card (R M q q' pP pM) = length (filter (\<lambda>t. t_target t = q') pM)"
            by auto

          show ?case proof (cases "target q (pM @ [t]) = q'")
            case True
            then have "(R M q q' pP (pM @ [t])) = insert (pP @ pM @ [t]) (R M q q' pP pM)"
              unfolding R_update[of M q q' pP pM t] by simp
            moreover have "(pP @ pM @ [t]) \<notin> (R M q q' pP pM)"
              unfolding R_def by auto
            ultimately have "card (R M q q' pP (pM @ [t])) = Suc (card (R M q q' pP pM))"
              using finite_R[OF \<open>path M q pM\<close>, of q' pP] by simp 
            then show ?thesis 
              using True unfolding \<open>card (R M q q' pP pM) = length (filter (\<lambda>t. t_target t = q') pM)\<close> by auto
          next
            case False
            then have "card (R M q q' pP (pM @ [t])) = card (R M q q' pP pM)"
              unfolding R_update[of M q q' pP pM t] by simp
            then show ?thesis 
              using False unfolding \<open>card (R M q q' pP pM) = length (filter (\<lambda>t. t_target t = q') pM)\<close> by auto
          qed 
        qed

        show ?case proof (cases "q' \<in> snd dM")
          case True
          then have p0: "(RP M q q' pP pM prs M') = insert (f q') (R M q q' pP pM)" and "(f q') \<notin> (R M q q' pP pM)"
            using f_def by blast+
          then have "card (RP M q q' pP pM prs M') = Suc (card (R M q q' pP pM))"
            by (simp add: \<open>path M q pM\<close> finite_R)
          then have p1: "(\<Sum>q' \<in> (insert q' nds). card (RP M q q' pP pM prs M')) = (\<Sum>q'\<in>nds. card (RP M q q' pP pM prs M')) + Suc (card (R M q q' pP pM))"
            by (simp add: insert.hyps(1) insert.hyps(2))

          have p2: "length (filter (\<lambda>t. t_target t \<in> insert q' nds) pM) = length (filter (\<lambda>t. t_target t \<in> nds) pM) + length (filter (\<lambda>t. t_target t = q') pM)"
            using \<open>q' \<notin> nds\<close> by (induction pM; auto)
          have p3: "card ((insert q' nds) \<inter> snd dM) = Suc (card (nds \<inter> snd dM))"
            using True \<open>finite nds\<close> \<open>q' \<notin> nds\<close> by simp

          show ?thesis 
            using leq1
            unfolding  p1 p2 p3 p4 by simp
        next
          case False

          have "card (RP M q q' pP pM prs M') \<ge> (card (R M q q' pP pM))"
          proof (cases "(RP M q q' pP pM prs M') = (R M q q' pP pM)")
            case True
            then show ?thesis using finite_R[OF \<open>path M q pM\<close>, of q' pP] by auto
          next
            case False
            then obtain pX where "(RP M q q' pP pM prs M') = insert pX (R M q q' pP pM)"
              using RP_from_R[OF t2 pass1 \<open>completely_specified M'\<close> \<open>inputs M' = inputs M\<close>, of prs "\<lambda> q P io x y y' . q" "\<lambda> q P io x y y' . y" q q' pP pM] 
              by force
            then show ?thesis using finite_R[OF \<open>path M q pM\<close>, of q' pP]
              by (simp add: card_insert_le) 
          qed
          then have p1: "(\<Sum>q' \<in> (insert q' nds). card (RP M q q' pP pM prs M')) \<ge> ((\<Sum>q'\<in>nds. card (RP M q q' pP pM prs M')) + (card (R M q q' pP pM)))"
            by (simp add: insert.hyps(1) insert.hyps(2))


          have p2: "length (filter (\<lambda>t. t_target t \<in> insert q' nds) pM) = length (filter (\<lambda>t. t_target t \<in> nds) pM) + length (filter (\<lambda>t. t_target t = q') pM)"
            using \<open>q' \<notin> nds\<close> by (induction pM; auto)
          have p3: "card ((insert q' nds) \<inter> snd dM) = (card (nds \<inter> snd dM))"
            using False \<open>finite nds\<close> \<open>q' \<notin> nds\<close> by simp

          have "length (filter (\<lambda>t. t_target t \<in> nds) pM) + length (filter (\<lambda>t. t_target t = q') pM) + card (nds \<inter> snd dM) \<le> (\<Sum>q'\<in>nds. card (RP M q q' pP pM prs M')) + length (filter (\<lambda>t. t_target t = q') pM)"
            using leq1 add_le_cancel_right by auto 

          then show ?thesis 
            using p1 
            unfolding p2 p3 p4 by simp
        qed
      qed 
    qed

    moreover have "finite (fst dM)"
      using t7[OF \<open>dM \<in> set repetition_sets\<close>] fsm_states_finite[of M]
      using rev_finite_subset by auto 
    ultimately have "(\<Sum> q' \<in> fst dM . card (RP M q q' pP pM prs M')) \<ge> length (filter (\<lambda>t. t_target t \<in> fst dM) pM) + card (fst dM \<inter> snd dM)"
      by blast
    have "(fst dM \<inter> snd dM) = (snd dM)"
      using t8[OF \<open>dM \<in> set repetition_sets\<close>] by blast
    have "(\<Sum> q' \<in> fst dM . card (RP M q q' pP pM prs M')) \<ge> length (filter (\<lambda>t. t_target t \<in> fst dM) pM) + card (snd dM)"
      using \<open>(\<Sum> q' \<in> fst dM . card (RP M q q' pP pM prs M')) \<ge> length (filter (\<lambda>t. t_target t \<in> fst dM) pM) + card (fst dM \<inter> snd dM)\<close> 
      unfolding \<open>(fst dM \<inter> snd dM) = (snd dM)\<close> 
      by assumption
    moreover have "(\<Sum>q'\<in>fst dM. card (\<Union>pR\<in>RP M q q' pP pM prs M'. io_targets M' (p_io pR) (FSM.initial M'))) = (\<Sum> q' \<in> fst dM . card (RP M q q' pP pM prs M'))"
      using RP_card \<open>FSM.initial P = FSM.initial M\<close> \<open>target (FSM.initial P) pP = q\<close> by auto 
    ultimately have "(\<Sum>q'\<in>fst dM. card (\<Union>pR\<in>RP M q q' pP pM prs M'. io_targets M' (p_io pR) (FSM.initial M'))) \<ge> length (filter (\<lambda>t. t_target t \<in> fst dM) pM) + card (snd dM)"
      by linarith
    moreover have "Suc m \<le> length (filter (\<lambda>t. t_target t \<in> fst dM) pM) + card (snd dM)"
      using \<open>Suc (m - card (snd dM)) \<le> length (filter (\<lambda>t. t_target t \<in> fst dM) pM)\<close>
      by linarith 
    ultimately show ?thesis 
      by linarith
  qed


  moreover have "(\<Sum> q' \<in> fst dM . card (\<Union> pR \<in> (RP M q q' pP pM prs M') . io_targets M' (p_io pR) (initial M'))) \<le> card (states M')"
  proof -
    have "finite (fst dM)"
      by (meson \<open>dM \<in> set repetition_sets\<close> fsm_states_finite rev_finite_subset t7) 

    have "(\<And>x1. finite (RP M q x1 pP pM prs M'))"
      using finite_RP[OF \<open>path M q pM\<close> t2 pass1 \<open>completely_specified M'\<close> \<open>inputs M' = inputs M\<close>] by force

    have "(\<And>y1. finite (io_targets M' (p_io y1) (FSM.initial M')))"
      by (meson io_targets_finite)

    have "(\<And>y1. io_targets M' (p_io y1) (FSM.initial M') \<subseteq> states M')"
      by (meson io_targets_states)
      
    show ?thesis 
      using distinct_union_union_card
        [ of "fst dM" "\<lambda> q' . (RP M q q' pP pM prs M')" "\<lambda> pR . io_targets M' (p_io pR) (initial M')"
        , OF \<open>finite (fst dM)\<close>
             no_shared_targets_for_distinct_states
             no_shared_targets_for_identical_states
             \<open>(\<And>x1. finite (RP M q x1 pP pM prs M'))\<close>
             io_targets_finite
             io_targets_states
             fsm_states_finite[of M']] 
      unfolding \<open>(target (FSM.initial M) pP) = q\<close> by force
  qed

  (* create a contradiction due to the assumption that M' has at most m states *)

  moreover have "card (states M') \<le> m"
    using \<open>size M' \<le> m\<close> by auto

  ultimately show False
    by linarith
qed


subsection \<open>Completeness of Sufficient Test Suites\<close>

text \<open>This subsection combines the soundness and exhaustiveness properties of sufficient test suites
      to show completeness: for any System Under Test with at most m states a test suite sufficient 
      for m passes if and only if the System Under Test is a reduction of the specification.\<close>


lemma passes_test_suite_completeness :
  assumes "implies_completeness T M m"
  and     "observable M" 
  and     "observable M'"
  and     "inputs M' = inputs M"
  and     "inputs M \<noteq> {}"
  and     "completely_specified M"
  and     "completely_specified M'"
  and     "size M' \<le> m"
shows     "(L M' \<subseteq> L M) \<longleftrightarrow> passes_test_suite M T M'"
  using passes_test_suite_exhaustiveness[OF _ _ assms(2-8)]
        passes_test_suite_soundness[OF _ assms(2,3,4,6)] 
        assms(1) 
        test_suite.exhaust[of T]
  by metis




subsection \<open>Additional Test Suite Properties\<close>

(* Whether a (sufficient) test suite can be represented as a finite set of IO sequences *)
(* (tps q) must already be finite for a sufficient test suite due to being a subset of the maximal m-traversal paths *)
fun is_finite_test_suite :: "('a,'b,'c,'d) test_suite \<Rightarrow> bool" where
  "is_finite_test_suite (Test_Suite prs tps rd_targets separators) = 
    ((finite prs) \<and> (\<forall> q p . q \<in> fst ` prs \<longrightarrow> finite (rd_targets (q,p))) \<and> (\<forall> q q' . finite (separators (q,q'))))" 

end