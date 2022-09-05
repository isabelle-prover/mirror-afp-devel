section \<open>State Preambles\<close>

text \<open>This theory defines state preambles.
      A state preamble @{text "P"} of some state @{text "q"} of some FSM @{text "M"} is an acyclic single-input 
      submachine of @{text "M"} that contains for each of its states and defined inputs in that state
      all transitions of @{text "M"} and has @{text "q"} as its only deadlock state.
      That is, @{text "P"} represents a strategy of reaching @{text "q"} in every complete submachine
      of @{text "M"}.
      In testing, preambles are used to reach states in the SUT that must conform to a single known
      state in the specification.\<close>

theory State_Preamble
imports "../Product_FSM" Backwards_Reachability_Analysis
begin


definition is_preamble :: "('a,'b,'c) fsm \<Rightarrow> ('a,'b,'c) fsm \<Rightarrow> 'a \<Rightarrow> bool" where
  "is_preamble S M q = 
    ( acyclic S 
    \<and> single_input S 
    \<and> is_submachine S M 
    \<and> q \<in> reachable_states S 
    \<and> deadlock_state S q 
    \<and> (\<forall> q' \<in> reachable_states S . 
        (q = q' \<or> \<not> deadlock_state S q') \<and> 
        (\<forall> x \<in> inputs M . 
          (\<exists> t \<in> transitions S . t_source t = q' \<and> t_input t = x) 
            \<longrightarrow> (\<forall> t' \<in> transitions M . t_source t' = q' \<and> t_input t' = x \<longrightarrow> t' \<in> transitions S))))"

fun definitely_reachable :: "('a,'b,'c) fsm \<Rightarrow> 'a \<Rightarrow> bool" where
  "definitely_reachable M q = (\<exists> S . is_preamble S M q)"




subsection \<open>Basic Properties\<close>

lift_definition initial_preamble :: "('a,'b,'c) fsm \<Rightarrow> ('a,'b,'c) fsm" is FSM_Impl.initial_singleton 
  by auto

lemma initial_preamble_simps[simp] :
  "initial (initial_preamble M) = initial M"
  "states (initial_preamble M) = {initial M}"
  "inputs (initial_preamble M) = inputs M"
  "outputs (initial_preamble M) = outputs M"
  "transitions (initial_preamble M) = {}"
  by (transfer; auto)+


lemma is_preamble_initial : 
  "is_preamble (initial_preamble M) M (initial M)"
proof -
  have "acyclic (initial_preamble M)"
    by (metis acyclic_code empty_iff initial_preamble_simps(5))
  moreover have "single_input (initial_preamble M)"
    by auto
  moreover have "is_submachine (initial_preamble M) M"
    by (simp add: fsm_initial)
  moreover have "(initial M) \<in> reachable_states (initial_preamble M)"
    unfolding reachable_states_def using reachable_states_intro by auto 
  moreover have "deadlock_state (initial_preamble M) (initial M)"
    by simp
  ultimately show ?thesis  
    unfolding is_preamble_def
    using reachable_state_is_state by force
qed
  
 
 

lemma is_preamble_next :
  assumes "is_preamble S M q"
  and "q \<noteq> initial M"
  and "t \<in> transitions S"  
  and "t_source t = initial M"
shows "is_preamble (from_FSM S (t_target t)) (from_FSM M (t_target t)) q"
(is "is_preamble ?S ?M q")
proof -


  have "acyclic S"
  and  "single_input S" 
  and  "is_submachine S M" 
  and  "q \<in> reachable_states S"
  and  "deadlock_state S q" 
  and  *: "(\<forall> q' \<in> reachable_states S . (q = q' \<or> \<not> deadlock_state S q') 
            \<and> (\<forall> x \<in> inputs M . (\<exists> t \<in> transitions S . t_source t = q' \<and> t_input t = x) 
                                \<longrightarrow> (\<forall> t' \<in> transitions M . t_source t' = q' \<and> t_input t' = x 
                                                            \<longrightarrow> t' \<in> transitions S)))"
    using assms(1) unfolding is_preamble_def by linarith+

  have "t_target t \<in> states S"
    using assms(3) fsm_transition_target by metis
  have "t_target t \<in> states M"
    using \<open>is_submachine S M\<close> \<open>t_target t \<in> FSM.states S\<close> by auto 

  have is_acyclic: "acyclic ?S" 
    using from_FSM_path_initial[OF \<open>t_target t \<in> states S\<close>]
    unfolding acyclic.simps from_FSM_simps[OF \<open>t_target t \<in> states S\<close>]
    using acyclic_paths_from_reachable_states[OF \<open>acyclic S\<close>, of "[t]" "t_target t"]
    by (metis \<open>is_submachine S M\<close> assms(3) assms(4) is_submachine.elims(2) 
          prod.collapse single_transition_path target_single_transition)

  have is_single_input: "single_input ?S"
    using \<open>single_input S\<close> 
    unfolding single_input.simps from_FSM_simps[OF \<open>t_target t \<in> states S\<close>] by blast

  have "initial ?S = initial ?M"
    by (simp add: \<open>t_target t \<in> FSM.states M\<close> \<open>t_target t \<in> FSM.states S\<close>) 
  moreover have "inputs ?S = inputs ?M"
    using \<open>is_submachine S M\<close> by (simp add: \<open>t_target t \<in> FSM.states M\<close> \<open>t_target t \<in> FSM.states S\<close>)
  moreover have "outputs ?S = outputs ?M"
    using \<open>is_submachine S M\<close> by (simp add: \<open>t_target t \<in> FSM.states M\<close> \<open>t_target t \<in> FSM.states S\<close>) 
  moreover have "transitions ?S \<subseteq> transitions ?M"
    using \<open>is_submachine S M\<close>
    by (simp add: \<open>t_target t \<in> FSM.states M\<close> \<open>t_target t \<in> FSM.states S\<close>)
  ultimately have is_sub : "is_submachine ?S ?M"
    using \<open>is_submachine S M\<close> \<open>t_target t \<in> FSM.states M\<close> \<open>t_target t \<in> FSM.states S\<close> by auto


  have contains_q : "q \<in> reachable_states ?S"
  proof -
    obtain qd where "qd \<in> reachable_states ?S" and "deadlock_state ?S qd"
      using is_acyclic
      using acyclic_deadlock_reachable by blast 
    
    have "qd \<in> reachable_states S"
      by (metis (no_types, lifting) \<open>is_submachine S M\<close> \<open>qd \<in> reachable_states (FSM.from_FSM S (t_target t))\<close> 
            assms(3) assms(4) from_FSM_reachable_states in_mono is_submachine.elims(2) prod.collapse 
            reachable_states_intro single_transition_path target_single_transition)
    then have "deadlock_state S qd"
      using \<open>deadlock_state ?S qd\<close> unfolding deadlock_state.simps
      by (simp add: \<open>t_target t \<in> FSM.states S\<close>)
    then have "qd = q"
      using * \<open>qd \<in> reachable_states S\<close>
      by fastforce
    then show ?thesis 
      using \<open>qd \<in> reachable_states ?S\<close> by auto
  qed
  
  have has_deadlock_q : "deadlock_state ?S q"
    using *
    by (metis \<open>deadlock_state S q\<close> \<open>t_target t \<in> FSM.states S\<close> deadlock_state.simps from_FSM_simps(4))


  have has_states_prop_1: "\<And> q' . q' \<in> reachable_states ?S \<Longrightarrow> deadlock_state ?S q' \<Longrightarrow> q = q'"
  proof -
    fix q' assume "q' \<in> reachable_states ?S" and "deadlock_state ?S q'"
    have "q' \<in> reachable_states S"
      by (metis (no_types, lifting) \<open>is_submachine S M\<close> \<open>q' \<in> reachable_states (FSM.from_FSM S (t_target t))\<close> 
          assms(3) assms(4) from_FSM_reachable_states in_mono is_submachine.elims(2) prod.collapse 
          reachable_states_intro single_transition_path target_single_transition)      
    then have "deadlock_state S q'"
      using \<open>deadlock_state ?S q'\<close> unfolding deadlock_state.simps
      using \<open>q' \<in> reachable_states ?S\<close> by (simp add: \<open>t_target t \<in> FSM.states S\<close>)
    then show "q = q'"
      using * \<open>q' \<in> reachable_states S\<close> by fastforce 
  qed

  moreover have has_states_prop_2: "\<And> x t t' q' .
    q' \<in> reachable_states ?S \<Longrightarrow>
    t \<in> transitions ?S \<Longrightarrow> t_source t = q' \<Longrightarrow> t_input t = x \<Longrightarrow>
    t' \<in> transitions ?M \<Longrightarrow> t_source t' = q' \<Longrightarrow> t_input t' = x \<Longrightarrow> t' \<in> transitions ?S"
  proof -
    fix x tS tM q' assume "q' \<in> reachable_states ?S" and "tS \<in> transitions ?S" and "t_source tS = q'" 
                      and "t_input tS = x" and "tM \<in> transitions ?M" and "t_source tM = q'" 
                      and "t_input tM = x"


    have "q' \<in> reachable_states S"
      by (metis (no_types, lifting) \<open>is_submachine S M\<close> \<open>q' \<in> reachable_states (FSM.from_FSM S (t_target t))\<close> 
            assms(3) assms(4) from_FSM_reachable_states in_mono is_submachine.elims(2) prod.collapse 
            reachable_states_intro single_transition_path target_single_transition)
    

    have "tS \<in> transitions S"
      using \<open>tS \<in> transitions ?S\<close> by (simp add: \<open>t_target t \<in> FSM.states S\<close>)
    have "tM \<in> transitions M"
      using \<open>tM \<in> transitions ?M\<close>
      using \<open>t_target t \<in> FSM.states M\<close> by (simp add: \<open>t_target t \<in> FSM.states S\<close>)
    have "t_source tS \<in> states (from_FSM S (t_target t))"
      using \<open>tS \<in> transitions ?S\<close> by auto
    have "t_source tM \<in> states (from_FSM M (t_target t))"
      using \<open>tM \<in> transitions ?M\<close> by auto

    have "q' \<in> reachable_states ?M" 
      using \<open>q' \<in> reachable_states ?S\<close> submachine_path[OF \<open>is_submachine ?S ?M\<close>]
      unfolding reachable_states_def
    proof -
      assume "q' \<in> {target (FSM.initial (FSM.from_FSM S (t_target t))) p |p. 
                      path (FSM.from_FSM S (t_target t)) (FSM.initial (FSM.from_FSM S (t_target t))) p}"
      then show "q' \<in> {target (FSM.initial (FSM.from_FSM M (t_target t))) ps |ps. 
                        path (FSM.from_FSM M (t_target t)) (FSM.initial (FSM.from_FSM M (t_target t))) ps}"
        using \<open>FSM.initial (FSM.from_FSM S (t_target t)) = FSM.initial (FSM.from_FSM M (t_target t))\<close> 
              \<open>\<And>q p. path (FSM.from_FSM S (t_target t)) q p \<Longrightarrow> path (FSM.from_FSM M (t_target t)) q p\<close> 
        by fastforce
    qed
       

    show "tM \<in> transitions ?S" 
      using * \<open>q' \<in> reachable_states S\<close>
            \<open>tM \<in> FSM.transitions M\<close> \<open>tS \<in> FSM.transitions S\<close> \<open>t_input tM = x\<close> \<open>t_input tS = x\<close> 
            \<open>t_source tM = q'\<close> \<open>t_source tS = q'\<close> \<open>t_target t \<in> FSM.states S\<close> 
      by fastforce       
  qed 
     

  show ?thesis
    unfolding is_preamble_def
    using is_acyclic 
          is_single_input 
          is_sub
          contains_q
          has_deadlock_q
          has_states_prop_1
    using has_states_prop_2 by blast    
qed


lemma observable_preamble_paths :
  assumes "is_preamble P M q'"
  and     "observable M"
  and     "path M q p"  
  and     "p_io p \<in> LS P q"
  and     "q \<in> reachable_states P"
shows "path P q p"
using assms(3,4,5) proof (induction p arbitrary: q rule: list.induct)
  case Nil
  then show ?case by auto
next
  case (Cons t p)

  have   "is_submachine P M"
  and *: "\<And> q' x t t' . q'\<in>reachable_states P \<Longrightarrow> x\<in>FSM.inputs M \<Longrightarrow>
            t\<in>FSM.transitions P \<Longrightarrow> t_source t = q' \<Longrightarrow> t_input t = x \<Longrightarrow>
            t'\<in>FSM.transitions M \<Longrightarrow> t_source t' = q' \<Longrightarrow> t_input t' = x \<Longrightarrow> t' \<in> FSM.transitions P"
    using assms(1) unfolding is_preamble_def by blast+

  have "observable P"
    using submachine_observable[OF \<open>is_submachine P M\<close> \<open>observable M\<close>] by blast

  obtain t' where "t'\<in>FSM.transitions P" and "t_source t' = q" and "t_input t' = t_input t"
    using \<open>p_io (t # p) \<in> LS P q\<close> by auto

  have "t_source t = q" and "t \<in> transitions M" and "t_input t \<in> inputs M"
    using \<open>path M q (t # p)\<close> by auto

  have "t \<in> transitions P"
    using *[OF \<open>q \<in> reachable_states P\<close> \<open>t_input t \<in> inputs M\<close> \<open>t'\<in>FSM.transitions P\<close> 
               \<open>t_source t' = q\<close> \<open>t_input t' = t_input t\<close> \<open>t \<in> transitions M\<close> \<open>t_source t = q\<close>]
    by auto

  have "path M (t_target t) p"
    using \<open>path M q (t # p)\<close> by auto
  moreover have "p_io p \<in> LS P (t_target t)"
  proof -
    have f1: "t_input t = fst (t_input t, t_output t)"
      by (metis fst_conv)
    have f2: "t_output t = snd (t_input t, t_output t)"
      by auto
    have f3: "(t_input t, t_output t) # p_io p \<in> LS P (t_source t)"
      using Cons.prems(2) \<open>t_source t = q\<close> by fastforce
    have "L (FSM.from_FSM P (t_target t)) = LS P (t_target t)"
      by (meson \<open>t \<in> FSM.transitions P\<close> from_FSM_language fsm_transition_target)
    then show ?thesis
      using f3 f2 f1 \<open>observable P\<close> \<open>t \<in> FSM.transitions P\<close> observable_language_next by blast
  qed   
  moreover have "t_target t \<in> reachable_states P"
    using \<open>t \<in> transitions P\<close> \<open>t_source t = q\<close> \<open>q \<in> reachable_states P\<close>
    by (meson reachable_states_next) 
  ultimately have "path P (t_target t) p"
    using Cons.IH by blast
  then show ?case
    using \<open>t \<in> transitions P\<close> \<open>t_source t = q\<close> by auto
qed


lemma preamble_pass_path :
  assumes "is_preamble P M q"
  and     "\<And> io x y y' . io@[(x,y)] \<in> L P \<Longrightarrow> io@[(x,y')] \<in> L M' \<Longrightarrow> io@[(x,y')] \<in> L P"
  and     "completely_specified M'"
  and     "inputs M' = inputs M"
obtains p where "path P (initial P) p" and "target (initial P) p = q" and "p_io p \<in> L M'"
proof -
  (* get the longest paths p such that p_io p is still in L M' *)

  let ?ps = "{p . path P (initial P) p \<and> p_io p \<in> L M'}"
  have "?ps \<noteq> {}"
  proof -
    have "[] \<in> ?ps" by auto
    then show ?thesis by blast
  qed
  moreover have "finite ?ps"
  proof -
    have "acyclic P"
      using assms(1) unfolding is_preamble_def by blast
    have "finite {p. path P (FSM.initial P) p}"
      using acyclic_finite_paths_from_reachable_state[OF \<open>acyclic P\<close>, of "[]" "initial P"] by auto
    then show ?thesis
      by simp 
  qed
  ultimately obtain p where "p \<in> ?ps" and "\<And> p' . p' \<in> ?ps \<Longrightarrow> length p' \<le> length p" 
    by (meson leI max_length_elem) 
  then have "path P (initial P) p"
       and  "p_io p \<in> L M'"
    by blast+

  show ?thesis
  proof (cases "target (initial P) p = q")
    case True
    then show ?thesis using that[OF \<open>path P (initial P) p\<close> _ \<open>p_io p \<in> L M'\<close>] by blast
  next
    case False

    (* if p does not target the sole deadlock state q, then it can be extended *)

    then have "\<not> deadlock_state P (target (initial P) p)"
      using reachable_states_intro[OF \<open>path P (initial P) p\<close>] assms(1) unfolding is_preamble_def by fastforce
    then obtain t where "t \<in> transitions P" and "t_source t = target (initial P) p"
      by auto
    then have "path P (initial P) (p@[t])" 
      using \<open>path P (initial P) p\<close> path_append_transition by simp
    have "(p_io p) @ [(t_input t, t_output t)] \<in> L P"
      using language_intro[OF \<open>path P (initial P) (p@[t])\<close>] by simp

    have "t_input t \<in> inputs M'"
      using assms(1,4) fsm_transition_input[OF \<open>t \<in> transitions P\<close>] unfolding is_preamble_def is_submachine.simps by blast
    
    obtain p' where "path M' (initial M') p'" and "p_io p' = p_io p"
      using \<open>p_io p \<in> L M'\<close> by auto
    obtain t' where "t' \<in> transitions M'" and "t_source t' = target (initial M') p'" and "t_input t' = t_input t"
      using \<open>completely_specified M'\<close> \<open>t_input t \<in> inputs M'\<close> path_target_is_state[OF \<open>path M' (initial M') p'\<close>]
      unfolding completely_specified.simps by blast
    then have "path M' (initial M') (p'@[t'])" 
      using \<open>path M' (initial M') p'\<close> path_append_transition by simp
    have "(p_io p) @ [(t_input t, t_output t')] \<in> L M'"
      using language_intro[OF \<open>path M' (initial M') (p'@[t'])\<close>] 
      unfolding \<open>p_io p' = p_io p\<close>[symmetric] \<open>t_input t' = t_input t\<close>[symmetric] by simp

    have "(p_io p) @ [(t_input t, t_output t')] \<in> L P"
      using assms(2)[OF \<open>(p_io p) @ [(t_input t, t_output t)] \<in> L P\<close> \<open>(p_io p) @ [(t_input t, t_output t')] \<in> L M'\<close>]
      by assumption
    then obtain pt' where "path P (initial P) pt'" and "p_io pt' = (p_io p) @ [(t_input t, t_output t')]"
      by auto
    then have "pt' \<in> ?ps"
      using \<open>(p_io p) @ [(t_input t, t_output t')] \<in> L M'\<close> by auto
    then have "length pt' \<le> length p"
      using \<open>\<And> p' . p' \<in> ?ps \<Longrightarrow> length p' \<le> length p\<close> by blast
    moreover have "length pt' > length p"
      using \<open>p_io pt' = (p_io p) @ [(t_input t, t_output t')]\<close> 
      unfolding length_map[of "(\<lambda> t . (t_input t, t_output t))", symmetric] by simp
    ultimately have "False"
      by simp
    then show ?thesis 
      by simp
  qed
qed


lemma preamble_maximal_io_paths :
  assumes "is_preamble P M q"
  and     "observable M"
  and     "path P (initial P) p"
  and     "target (initial P) p = q"
shows "\<nexists>io' . io' \<noteq> [] \<and> p_io p @ io' \<in> L P" 
proof -
  have "deadlock_state P q"  
  and  "is_submachine P M"
    using assms(1) unfolding is_preamble_def by blast+

  have "observable P"
    using \<open>observable M\<close> \<open>is_submachine P M\<close>
    using submachine_observable by blast 

  show "\<nexists>io' . io' \<noteq> [] \<and> p_io p @ io' \<in> L P"
  proof
    assume "\<exists>io'. io' \<noteq> [] \<and> p_io p @ io' \<in> L P"
    then obtain io' where "io' \<noteq> []" and "p_io p @ io' \<in> L P"
      by blast

    obtain p1 p2 where "path P (FSM.initial P) p1" 
                   and "path P (target (FSM.initial P) p1) p2" 
                   and "p_io p1 = p_io p" 
                   and "p_io p2 = io'"
      using language_state_split[OF \<open>p_io p @ io' \<in> L P\<close>] by blast

    have "p1 = p"
      using observable_path_unique[OF \<open>observable P\<close> \<open>path P (FSM.initial P) p1\<close> \<open>path P (FSM.initial P) p\<close> \<open>p_io p1 = p_io p\<close>] 
      by assumption

    have "io' \<in> LS P q"
      using \<open>path P (target (FSM.initial P) p1) p2\<close> \<open>p_io p2 = io'\<close>
      unfolding \<open>p1 = p\<close> assms(4) by auto
    then show "False"
      using \<open>io' \<noteq> []\<close> \<open>deadlock_state P q\<close> 
      unfolding deadlock_state_alt_def 
      by blast
  qed
qed


lemma preamble_maximal_io_paths_rev :
  assumes "is_preamble P M q"
  and     "observable M"
  and     "io \<in> L P"
  and     "\<nexists>io' . io' \<noteq> [] \<and> io @ io' \<in> L P"
obtains p where "path P (initial P) p"
          and   "p_io p = io"
          and   "target (initial P) p = q"
proof -  
  have "acyclic P"
  and  "deadlock_state P q"  
  and  "is_submachine P M"
  and  "\<And> q' . q'\<in>reachable_states P \<Longrightarrow> (q = q' \<or> \<not> deadlock_state P q')"
    using assms(1) unfolding is_preamble_def by blast+

  have "observable P"
    using \<open>observable M\<close> \<open>is_submachine P M\<close>
    using submachine_observable by blast 

  obtain p where "path P (initial P) p" and "p_io p = io"
    using \<open>io \<in> L P\<close> by auto

  moreover have "target (initial P) p = q"
  proof (rule ccontr)
    assume "target (FSM.initial P) p \<noteq> q"
    then have "\<not> deadlock_state P (target (FSM.initial P) p)"
      using \<open>\<And> q' . q'\<in>reachable_states P \<Longrightarrow> (q = q' \<or> \<not> deadlock_state P q')\<close>[OF reachable_states_intro[OF \<open>path P (initial P) p\<close>]] by simp
    then obtain t where "t \<in> transitions P" and "t_source t = target (initial P) p"
      by auto
    then have "path P (initial P) (p @ [t])"
      using path_append_transition[OF \<open>path P (initial P) p\<close>] by auto
    then have "p_io (p@[t]) \<in> L P"
      unfolding LS.simps by (metis (mono_tags, lifting) mem_Collect_eq)
    then have "io @ [(t_input t, t_output t)] \<in> L P"
      using \<open>p_io p = io\<close> by auto
    then show "False"
      using assms(4) by auto
  qed

  ultimately show ?thesis using that by blast
qed


lemma is_preamble_is_state : 
  assumes "is_preamble P M q"
  shows "q \<in> states M"
  using assms unfolding is_preamble_def
  by (meson nil path_nil_elim reachable_state_is_state submachine_path) 


subsection \<open>Calculating State Preambles via Backwards Reachability Analysis\<close>


fun d_states :: "('a::linorder,'b::linorder,'c) fsm \<Rightarrow> 'a \<Rightarrow> ('a \<times> 'b) list" where
  "d_states M q = (if q = initial M 
                      then [] 
                      else select_inputs (h M) (initial M) (inputs_as_list M) (removeAll q (removeAll (initial M) (states_as_list M))) {q} [])"



lemma d_states_index_properties : 
  assumes "i < length (d_states M q)"
shows "fst (d_states M q ! i) \<in> (states M - {q})" 
      "fst (d_states M q ! i) \<noteq> q"
      "snd (d_states M q ! i) \<in> inputs M"
      "(\<forall> qx' \<in> set (take i (d_states M q)) . fst (d_states M q ! i) \<noteq> fst qx')"
      "(\<exists> t \<in> transitions M . t_source t = fst (d_states M q ! i) \<and> t_input t = snd (d_states M q ! i))"
      "(\<forall> t \<in> transitions M . (t_source t = fst (d_states M q ! i) \<and> t_input t = snd (d_states M q ! i)) \<longrightarrow> (t_target t = q \<or> (\<exists> qx' \<in> set (take i (d_states M q)) . fst qx' = (t_target t))))"
proof -
  have combined_goals : "fst (d_states M q ! i) \<in> (states M - {q})
                          \<and> fst (d_states M q ! i) \<noteq> q
                          \<and> snd (d_states M q ! i) \<in> inputs M
                          \<and> (\<forall> qx' \<in> set (take i (d_states M q)) . fst (d_states M q ! i) \<noteq> fst qx')
                          \<and> (\<exists> t \<in> transitions M . t_source t = fst (d_states M q ! i) \<and> t_input t = snd (d_states M q ! i))
                          \<and> (\<forall> t \<in> transitions M . (t_source t = fst (d_states M q ! i) \<and> t_input t = snd (d_states M q ! i)) \<longrightarrow> (t_target t = q \<or> (\<exists> qx' \<in> set (take i (d_states M q)) . fst qx' = (t_target t))))"
  proof (cases "q = initial M")
    case True
    then have "d_states M q = []" by auto
    then have "False" using assms by auto
    then show ?thesis by simp
  next
    case False
    then have *: "d_states M q = select_inputs (h M) (initial M) (inputs_as_list M) (removeAll q (removeAll (initial M) (states_as_list M))) {q} []" by auto

    have "initial M \<in> states M" by auto
    then have "insert (FSM.initial M) (set (removeAll q (removeAll (FSM.initial M) (states_as_list M)))) = states M - {q}"
      using states_as_list_set False by auto 



    have "i < length (select_inputs (h M) (FSM.initial M) (inputs_as_list M) (removeAll q (removeAll (FSM.initial M) (states_as_list M))) {q} [])"
      using assms * by simp
    moreover have "length [] \<le> i" by auto
    moreover have "distinct (map fst [])" by auto
    moreover have "{q} = {q} \<union> set (map fst [])" by auto
    moreover have "initial M \<notin> {q}" using False by auto
    moreover have "distinct (removeAll q (removeAll (FSM.initial M) (states_as_list M)))" using states_as_list_distinct
      by (simp add: distinct_removeAll) 
    moreover have "FSM.initial M \<notin> set (removeAll q (removeAll (FSM.initial M) (states_as_list M)))" by auto
    moreover have "set (removeAll q (removeAll (FSM.initial M) (states_as_list M))) \<inter> {q} = {}" by auto

    moreover show ?thesis 
      using select_inputs_index_properties[OF calculation] 
      unfolding *[symmetric] inputs_as_list_set \<open>insert (FSM.initial M) (set (removeAll q (removeAll (FSM.initial M) (states_as_list M)))) = states M - {q}\<close> by blast
  qed

  then show "fst (d_states M q ! i) \<in> (states M - {q})" 
      "fst (d_states M q ! i) \<noteq> q"
      "snd (d_states M q ! i) \<in> inputs M"
      "(\<forall> qx' \<in> set (take i (d_states M q)) . fst (d_states M q ! i) \<noteq> fst qx')"
      "(\<exists> t \<in> transitions M . t_source t = fst (d_states M q ! i) \<and> t_input t = snd (d_states M q ! i))"
      "(\<forall> t \<in> transitions M . (t_source t = fst (d_states M q ! i) \<and> t_input t = snd (d_states M q ! i)) \<longrightarrow> (t_target t = q \<or> (\<exists> qx' \<in> set (take i (d_states M q)) . fst qx' = (t_target t))))"
    by blast+
qed


lemma d_states_distinct :
  "distinct (map fst (d_states M q))"
proof -
  have *: "\<And> i q . i < length (map fst (d_states M q)) \<Longrightarrow> q \<in> set (take i (map fst (d_states M q))) \<Longrightarrow> ((map fst (d_states M q)) ! i) \<noteq> q"
    using d_states_index_properties(2,4) by fastforce 
  then have "(\<And>i. i < length (map fst (d_states M q)) \<Longrightarrow>
          map fst (d_states M q) ! i \<notin> set (take i (map fst (d_states M q))))"
  proof -
    fix i :: nat
    assume a1: "i < length (map fst (d_states M q))"
    then have "\<forall>p. p \<notin> set (take i (d_states M q)) \<or> fst (d_states M q ! i) \<noteq> fst p"
      by (metis (no_types) d_states_index_properties(4) length_map)
    then show "map fst (d_states M q) ! i \<notin> set (take i (map fst (d_states M q)))"
      using a1 by (metis (no_types) length_map list_map_source_elem nth_map take_map)
  qed
  then show ?thesis
    using list_distinct_prefix[of "map fst (d_states M q)"] by blast
qed


lemma d_states_states : 
  "set (map fst (d_states M q)) \<subseteq> states M - {q}"
  using d_states_index_properties(1)[of _ M q] list_property_from_index_property[of "map fst (d_states M q)" "\<lambda>q' . q' \<in> states M - {q}"]
  by (simp add: subsetI)


lemma d_states_size :
  assumes "q \<in> states M"
  shows "length (d_states M q) \<le> size M - 1"
proof -
  show ?thesis 
    using d_states_states[of M q]
          d_states_distinct[of M q]
          fsm_states_finite[of M]
          assms
    by (metis card_Diff_singleton_if card_mono distinct_card finite_Diff length_map size_def)    
qed


lemma d_states_initial :
  assumes "qx \<in> set (d_states M q)" 
  and     "fst qx = initial M"
shows "(last (d_states M q)) = qx"
  using assms(1) select_inputs_initial[of qx "h M" "initial M" _ _ _ "[]", OF _ assms(2)]
  by (cases "q = initial M"; auto)


lemma d_states_q_noncontainment :
  shows "\<not>(\<exists> qqx \<in> set (d_states M q) . fst qqx = q)" 
  using d_states_index_properties(2)
  by (metis in_set_conv_nth) 


lemma d_states_acyclic_paths' :
  fixes M :: "('a::linorder,'b::linorder,'c) fsm"
  assumes "path (filter_transitions M (\<lambda> t . (t_source t, t_input t) \<in> set (d_states M q))) q' p"
  and     "target q' p = q'"
  and     "p \<noteq> []"
shows "False"
proof -
  from \<open>p \<noteq> []\<close> obtain p' t' where "p = t'#p'"
    using list.exhaust by blast
  then have "path (filter_transitions M (\<lambda> t . (t_source t, t_input t) \<in> set (d_states M q))) q' (p@[t'])"
    using assms(1,2) by fastforce

  define f :: "('a \<times> 'b \<times> 'c \<times> 'a) \<Rightarrow> nat"
    where f_def: "f = (\<lambda> t . the (find_index (\<lambda> qx . fst qx = t_source t \<and> snd qx = t_input t) (d_states M q)))"
  
  have f_prop: "\<And> t . t \<in> set (p@[t']) \<Longrightarrow> (f t < length (d_states M q)) 
                                      \<and> ((d_states M q) ! (f t) = (t_source t, t_input t))
                                      \<and> (\<forall> j < f t . fst (d_states M q ! j) \<noteq> t_source t)"
  proof -
    fix t assume "t \<in> set (p@[t'])"
    then have "t \<in> set p" using \<open>p = t'#p'\<close> by auto
    then have "t \<in> transitions M" and "(t_source t, t_input t) \<in> set (d_states M q)"
      using assms(1) path_transitions by fastforce+
    then have "\<exists> qx \<in> set (d_states M q) . (\<lambda> qx . fst qx = t_source t \<and> snd qx = t_input t) qx"
      by (meson fst_conv snd_conv)
    then have "find_index (\<lambda> qx . fst qx = t_source t \<and> snd qx = t_input t) (d_states M q) \<noteq> None"
      by (simp add: find_index_exhaustive) 
    then obtain i where *: "find_index (\<lambda> qx . fst qx = t_source t \<and> snd qx = t_input t) (d_states M q) = Some i"
      by auto

    have "f t < length (d_states M q)"
      unfolding f_def using find_index_index(1)[OF *] unfolding * by simp
    moreover have "((d_states M q) ! (f t) = (t_source t, t_input t))"
      unfolding f_def using find_index_index(2)[OF *]
      by (metis "*" option.sel prod.collapse) 
    moreover have "\<forall> j < f t . fst (d_states M q ! j) \<noteq> t_source t"
      unfolding f_def using find_index_index(3)[OF *] unfolding * 
      using d_states_distinct[of M q]
      by (metis (mono_tags, lifting) calculation(1) calculation(2) distinct_conv_nth fst_conv length_map less_imp_le less_le_trans not_less nth_map option.sel snd_conv) 
    ultimately show "(f t < length (d_states M q)) 
                                      \<and> ((d_states M q) ! (f t) = (t_source t, t_input t))
                                      \<and> (\<forall> j < f t . fst (d_states M q ! j) \<noteq> t_source t)" by simp
  qed

  have *: "\<And> i . Suc i < length (p@[t']) \<Longrightarrow> f ((p@[t']) ! i) > f ((p@[t']) ! (Suc i))"
  proof -
    fix i assume "Suc i < length (p@[t'])"
    then have "(p@[t']) ! i \<in> set (p@[t'])" and "(p@[t']) ! (Suc i) \<in> set (p@[t'])"
      using Suc_lessD nth_mem by blast+
    then have "(p@[t']) ! i \<in> transitions M" and "(p@[t']) ! Suc i \<in> transitions M" 
      using path_transitions[OF \<open>path (filter_transitions M (\<lambda> t . (t_source t, t_input t) \<in> set (d_states M q))) q' (p@[t'])\<close>]
      using filter_transitions_simps(5) by blast+
            

    have "f ((p@[t']) ! i) < length (d_states M q)"
    and  "(d_states M q) ! (f ((p@[t']) ! i)) = (t_source ((p@[t']) ! i), t_input ((p@[t']) ! i))"
    and  "(\<forall>j<f ((p@[t']) ! i). fst (d_states M q ! j) \<noteq> t_source ((p@[t']) ! i))"
      using f_prop[OF \<open>(p@[t']) ! i \<in> set (p@[t'])\<close>] by auto

    have "f ((p@[t']) ! Suc i) < length (d_states M q)"
    and  "(d_states M q) ! (f ((p@[t']) ! Suc i)) = (t_source ((p@[t']) ! Suc i), t_input ((p@[t']) ! Suc i))"
    and  "(\<forall>j<f ((p@[t']) ! Suc i). fst (d_states M q ! j) \<noteq> t_source ((p@[t']) ! Suc i))"
      using f_prop[OF \<open>(p@[t']) ! Suc i \<in> set (p@[t'])\<close>] by auto

    have "t_target ((p@[t']) ! i) = t_source ((p@[t']) ! Suc i)"
      using \<open>Suc i < length (p@[t'])\<close> \<open>path (filter_transitions M (\<lambda> t . (t_source t, t_input t) \<in> set (d_states M q))) q' (p@[t'])\<close>
      by (simp add: path_source_target_index) 
    then have "t_target ((p@[t']) ! i) \<noteq> q"
      using d_states_index_properties(2)[OF \<open>f ((p@[t']) ! Suc i) < length (d_states M q)\<close>] 
      unfolding \<open>(d_states M q) ! (f ((p@[t']) ! Suc i)) = (t_source ((p@[t']) ! Suc i), t_input ((p@[t']) ! Suc i))\<close> by auto
    then have "(\<exists>qx'\<in>set (take (f ((p@[t']) ! i)) (d_states M q)). fst qx' = t_target ((p@[t']) ! i))"
      using d_states_index_properties(6)[OF \<open>f ((p@[t']) ! i) < length (d_states M q)\<close>] unfolding \<open>(d_states M q) ! (f ((p@[t']) ! i)) = (t_source ((p@[t']) ! i), t_input ((p@[t']) ! i))\<close> fst_conv snd_conv
      using \<open>(p@[t']) ! i \<in> transitions M\<close>
      by blast
    then have "(\<exists>qx'\<in>set (take (f ((p@[t']) ! i)) (d_states M q)). fst qx' = t_source ((p@[t']) ! Suc i))" 
      unfolding \<open>t_target ((p@[t']) ! i) = t_source ((p@[t']) ! Suc i)\<close> by assumption
    then obtain j where "fst (d_states M q ! j) = t_source ((p@[t']) ! Suc i)" and "j < f ((p@[t']) ! i)"
      by (metis (no_types, lifting) \<open>f ((p@[t']) ! i) < length (d_states M q)\<close> in_set_conv_nth leD length_take min_def_raw nth_take)
      
    then show "f ((p@[t']) ! i) > f ((p@[t']) ! (Suc i))"
      using \<open>(\<forall>j<f ((p@[t']) ! Suc i). fst (d_states M q ! j) \<noteq> t_source ((p@[t']) ! Suc i))\<close>
      using leI le_less_trans by blast 
  qed   

  have "\<And> i j . j < i \<Longrightarrow> i < length (p@[t']) \<Longrightarrow> f ((p@[t']) ! j) > f ((p@[t']) ! i)"
    using list_index_fun_gt[of "p@[t']" f] * by blast
  then have "f t' < f t'"
    unfolding \<open>p = t'#p'\<close> by fastforce 
  then show "False"
    by auto
qed


lemma d_states_acyclic_paths :
  fixes M :: "('a::linorder,'b::linorder,'c) fsm"
  assumes "path (filter_transitions M (\<lambda> t . (t_source t, t_input t) \<in> set (d_states M q))) q' p"
          (is "path ?FM q' p")
shows "distinct (visited_states q' p)"
proof (rule ccontr)
  assume "\<not> distinct (visited_states q' p)"
  
  obtain i j where p1:"take j (drop i p) \<noteq> []"
               and p2:"target (target q' (take i p)) (take j (drop i p)) = (target q' (take i p))"
               and p3:"path ?FM (target q' (take i p)) (take j (drop i p))"
    using cycle_from_cyclic_path[OF assms \<open>\<not> distinct (visited_states q' p)\<close>] by blast
  
  show "False"
    using d_states_acyclic_paths'[OF p3 p2 p1] by assumption
qed


lemma d_states_induces_state_preamble_helper_acyclic :
  shows "acyclic (filter_transitions M (\<lambda> t . (t_source t, t_input t) \<in> set (d_states M q)))"
  unfolding acyclic.simps
  using d_states_acyclic_paths by force

lemma d_states_induces_state_preamble_helper_single_input :
  shows "single_input (filter_transitions M (\<lambda> t . (t_source t, t_input t) \<in> set (d_states M q)))"
      (is "single_input ?FM")
  unfolding single_input.simps filter_transitions_simps
  by (metis (no_types, lifting) d_states_distinct eq_key_imp_eq_value mem_Collect_eq)


lemma d_states_induces_state_preamble :
  assumes "\<exists> qx \<in> set (d_states M q) . fst qx = initial M"
  shows "is_preamble (filter_transitions M (\<lambda> t . (t_source t, t_input t) \<in> set (d_states M q))) M q" 
    (is "is_preamble ?S M q")
proof (cases "q = initial M")
  case True
  then have "d_states M q = []" by auto
  then show ?thesis using assms(1) by auto
next
  case False

  have is_acyclic: "acyclic ?S" 
    using d_states_induces_state_preamble_helper_acyclic[of M q] by presburger

  have is_single_input: "single_input ?S" 
    using d_states_induces_state_preamble_helper_single_input[of M q] by presburger

  have is_sub : "is_submachine ?S M"
    unfolding is_submachine.simps filter_transitions_simps by blast

  have has_deadlock_q : "deadlock_state ?S q" 
    using d_states_q_noncontainment[of M q] unfolding deadlock_state.simps
    by fastforce

  have "\<And> q' . q' \<in> reachable_states ?S \<Longrightarrow> q' \<noteq> q \<Longrightarrow> \<not> deadlock_state ?S q'"
  proof -
    fix q' assume "q' \<in> reachable_states ?S" and "q' \<noteq> q"
    then obtain p where "path ?S (initial ?S) p" and "target (initial ?S) p = q'"
      unfolding reachable_states_def by auto

    have "\<exists> qx \<in> set (d_states M q) . fst qx = q'"
    proof (cases p rule: rev_cases)
      case Nil
      then show ?thesis 
        using assms(1) \<open>target (initial ?S) p = q'\<close> unfolding filter_transitions_simps
        by simp
    next
      case (snoc p' t)
      then have "t \<in> transitions ?S" and "t_target t = q'" 
        using \<open>path ?S (initial ?S) p\<close> \<open>target (initial ?S) p = q'\<close> by auto
      then have "(t_source t, t_input t) \<in> set (d_states M q)"
        by simp 
      then obtain i where "i < length (d_states M q)" and "d_states M q ! i = (t_source t, t_input t)"
        by (meson in_set_conv_nth)

      have "t \<in> transitions M"
        using \<open>t \<in> transitions ?S\<close>
        using is_sub by auto
      then show ?thesis
        using \<open>t_target t = q'\<close> \<open>q' \<noteq> q\<close>
        using d_states_index_properties(6)[OF \<open>i < length (d_states M q)\<close>]
        unfolding \<open>d_states M q ! i = (t_source t, t_input t)\<close> fst_conv snd_conv
        by (metis in_set_takeD)
    qed

    then obtain qx where "qx \<in> set (d_states M q)" and "fst qx = q'" by blast

    then have "(\<exists> t \<in> transitions M . t_source t = fst qx \<and> t_input t = snd qx)" 
      using d_states_index_properties(5)[of _ M q]
      by (metis in_set_conv_nth)
    then have "(\<exists> t \<in> transitions ?S . t_source t = fst qx \<and> t_input t = snd qx)"
      using \<open>qx \<in> set (d_states M q)\<close> by fastforce      

    then show "\<not> deadlock_state ?S q'" 
      unfolding deadlock_state.simps using \<open>fst qx = q'\<close> by blast
  qed

  then have has_states_prop_1 : "\<And> q' . q' \<in> reachable_states ?S \<Longrightarrow> (q = q' \<or> \<not> deadlock_state ?S q')" 
    by blast
  
  have has_states_prop_2 : "\<And> q' x t t'. q' \<in> reachable_states ?S \<Longrightarrow>  x \<in> inputs M \<Longrightarrow>
            t \<in> transitions ?S \<Longrightarrow> t_source t = q' \<Longrightarrow> t_input t = x \<Longrightarrow>
            t'\<in> transitions M \<Longrightarrow> t_source t' = q' \<Longrightarrow> t_input t' = x \<Longrightarrow> t' \<in> transitions ?S"
    by simp

  have contains_q : "q \<in> reachable_states ?S" 
    using \<open>\<And>q'. \<lbrakk>q' \<in> reachable_states ?S; q' \<noteq> q\<rbrakk> \<Longrightarrow> \<not> deadlock_state ?S q'\<close> acyclic_deadlock_reachable is_acyclic 
    by blast

  show ?thesis
    unfolding is_preamble_def
    using is_acyclic 
          is_single_input 
          is_sub
          contains_q
          has_deadlock_q
          has_states_prop_1 has_states_prop_2
    by blast
qed


fun calculate_state_preamble_from_input_choices :: "('a::linorder,'b::linorder,'c) fsm \<Rightarrow> 'a  \<Rightarrow> ('a,'b,'c) fsm option" 
  where
  "calculate_state_preamble_from_input_choices M q = (if q = initial M
    then Some (initial_preamble M)
    else 
      (let DS = (d_states M q);
           DSS = set DS 
        in (case DS of
            [] \<Rightarrow> None |
            _  \<Rightarrow> if fst (last DS) = initial M
                    then Some (filter_transitions M (\<lambda> t . (t_source t, t_input t) \<in> DSS))
                    else None)))"


lemma calculate_state_preamble_from_input_choices_soundness :
  assumes "calculate_state_preamble_from_input_choices M q = Some S"
  shows "is_preamble S M q"
proof (cases "q = initial M")
  case True
  then have "S = initial_preamble M" using assms by auto
  then show ?thesis 
    using is_preamble_initial[of M] True by presburger
next
  case False

  then have "S = (filter_transitions M (\<lambda> t . (t_source t, t_input t) \<in> set (d_states M q)))"
       and  "length (d_states M q) \<noteq> 0"
       and  "fst (last (d_states M q)) = initial M"
    using assms by (cases "(d_states M q)"; cases "fst (last (d_states M q)) = initial M"; simp)+

  then have "\<exists> qx \<in> set (d_states M q) . fst qx = initial M"
    by auto

  then show ?thesis 
    using d_states_induces_state_preamble
    unfolding \<open>S = (filter_transitions M (\<lambda> t . (t_source t, t_input t) \<in> set (d_states M q)))\<close>
    by blast 
qed


lemma calculate_state_preamble_from_input_choices_exhaustiveness :
  assumes "\<exists> S . is_preamble S M q"
  shows "calculate_state_preamble_from_input_choices M q \<noteq> None"
proof (cases "q = initial M")
  case True
  then show ?thesis by auto
next
  case False
  
  obtain S where "is_preamble S M q"
    using assms by blast

  then have "acyclic S"
        and "single_input S" 
        and "is_submachine S M"
        and "q \<in> reachable_states S"
        and "\<And> q' . q' \<in> reachable_states S \<Longrightarrow> (q = q' \<or> \<not> deadlock_state S q')" 
        and *: "\<And> q' x . q' \<in> reachable_states S \<Longrightarrow> x \<in> inputs M \<Longrightarrow> (\<exists> t \<in> transitions S . t_source t = q' \<and> t_input t = x) \<Longrightarrow> (\<forall> t' \<in> transitions M . t_source t' = q' \<and> t_input t' = x \<longrightarrow> t' \<in> transitions S)"
    unfolding is_preamble_def by blast+

 
  have p1: "(\<And>q x. q \<in> reachable_states S \<Longrightarrow> h S (q, x) \<noteq> {} \<Longrightarrow> h S (q, x) = h M (q, x))"
  proof - 
    fix q x assume "q \<in> reachable_states S" and "h S (q, x) \<noteq> {}"

    then have "x \<in> inputs M"
      using \<open>is_submachine S M\<close> fsm_transition_input by force
    have "(\<exists> t \<in> transitions S . t_source t = q \<and> t_input t = x)"
      using \<open>h S (q, x) \<noteq> {}\<close> by fastforce


    have "\<And> y q'' . (y,q'') \<in> h S (q,x) \<Longrightarrow> (y,q'') \<in> h M (q,x)" 
      using \<open>is_submachine S M\<close> by force 
    moreover have "\<And> y q'' . (y,q'') \<in> h M (q,x) \<Longrightarrow> (y,q'') \<in> h S (q,x)" 
      using *[OF \<open>q \<in> reachable_states S\<close> \<open>x \<in> inputs M\<close> \<open>(\<exists> t \<in> transitions S . t_source t = q \<and> t_input t = x)\<close>]
      unfolding h.simps by force
    ultimately show "h S (q, x) = h M (q, x)" 
      by force
  qed 

  have p2: "\<And>q'. q' \<in> reachable_states S \<Longrightarrow> deadlock_state S q' \<Longrightarrow> q' \<in> {q} \<union> set (map fst [])"
    using \<open>\<And> q' . q' \<in> reachable_states S \<Longrightarrow> (q = q' \<or> \<not> deadlock_state S q')\<close> by fast

  have "q \<in> states M"
    using \<open>q \<in> reachable_states S\<close> submachine_reachable_subset[OF \<open>is_submachine S M\<close>]
    by (meson assms is_preamble_is_state) 
  then have p3: "states M = insert (FSM.initial S) (set (removeAll q (removeAll (initial M) (states_as_list M))) \<union> {q} \<union> set (map fst []))"
    using states_as_list_set[of M] fsm_initial[of M]
    unfolding submachine_simps[OF \<open>is_submachine S M\<close>]
    by auto

  have p4: "initial S \<notin> set (removeAll q (removeAll (initial M) (states_as_list M))) \<union> {q} \<union> set (map fst [])"
    using False
    unfolding submachine_simps[OF \<open>is_submachine S M\<close>] by force

  have "fst (last (d_states M q)) = FSM.initial M" and "length (d_states M q) > 0"
    using False select_inputs_from_submachine[OF \<open>single_input S\<close> \<open>acyclic S\<close> \<open>is_submachine S M\<close> p1 p2 p3 p4]
    unfolding d_states.simps submachine_simps[OF \<open>is_submachine S M\<close>]
    by auto 


  have "(d_states M q) \<noteq> []"
    using \<open>length (d_states M q) > 0\<close> by auto
  then obtain dl dl' where "(d_states M q) = dl # dl'"
    using list.exhaust by blast
  then have "(fst (last (dl#dl')) = FSM.initial M) = True" using \<open>fst (last (d_states M q)) = FSM.initial M\<close> by simp
  then show ?thesis
    using False
    unfolding calculate_state_preamble_from_input_choices.simps Let_def \<open>(d_states M q) = dl # dl'\<close>  
    by auto
qed



subsection \<open>Minimal Sequences to Failures extending Preambles\<close>

definition sequence_to_failure_extending_preamble_path :: 
  "('a,'b,'c) fsm \<Rightarrow> ('d,'b,'c) fsm \<Rightarrow> ('a \<times> ('a,'b,'c) fsm) set \<Rightarrow> ('a\<times>'b\<times>'c\<times>'a) list \<Rightarrow> ('b \<times> 'c) list \<Rightarrow> bool" 
  where
  "sequence_to_failure_extending_preamble_path M M' PS p io = (\<exists> q P . q \<in> states M 
                                                                        \<and> (q,P) \<in> PS
                                                                        \<and> path P (initial P) p 
                                                                        \<and> target (initial P) p = q
                                                                        \<and> ((p_io p) @ butlast io) \<in> L M   
                                                                        \<and> ((p_io p) @ io) \<notin> L M
                                                                        \<and> ((p_io p) @ io) \<in> L M')"

lemma sequence_to_failure_extending_preamble_ex :
  assumes "(initial M, (initial_preamble M)) \<in> PS" (is "(initial M,?P) \<in> PS")
  and     "\<not> L M' \<subseteq> L M"
obtains p io where "sequence_to_failure_extending_preamble_path M M' PS p io"
proof -
  obtain io where "io \<in> L M' - L M"
    using \<open>\<not> L M' \<subseteq> L M\<close> by auto
  
  obtain j where "take j io \<in> L M" and "take (Suc j) io \<notin> L M" 
  proof -
    have "\<exists> j . take j io \<in> L M \<and> take (Suc j) io \<notin> L M"
    proof (rule ccontr)
      assume "\<nexists>j. take j io \<in> LS M (initial M) \<and> take (Suc j) io \<notin> LS M (initial M)"
      then have *: "\<And> j . take j io \<in> LS M (initial M) \<Longrightarrow> take (Suc j) io \<in> LS M (initial M)" by blast
      
      have "\<And> j . take j io \<in> LS M (initial M)"
      proof -
        fix j 
        show "take j io \<in> LS M (initial M)"
          using * by (induction j; auto)
      qed
      then have "take (length io) io \<in> L M" by blast
      then show "False"
        using \<open>io \<in> L M' - L M\<close> by auto
    qed
    then show ?thesis using that by blast
  qed

  have "\<And> i . take i io \<in> L M'" 
  proof -
    fix i show "take i io \<in> L M'" using \<open>io \<in> L M' - L M\<close> language_prefix[of "take i io" "drop i io" M' "initial M'"] by auto
  qed

  let ?io = "take (Suc j) io"
  

  have "initial M \<in> states M" 
    by auto
  moreover note \<open>(initial M, (initial_preamble M)) \<in> PS\<close>
  moreover have "path ?P (initial ?P) []" by force
  moreover have "((p_io []) @ butlast ?io) \<in> L M" 
    using \<open>take j io \<in> L M\<close>  
    unfolding List.list.map(1) append_Nil 
    by (metis Diff_iff One_nat_def \<open>io \<in> LS M' (initial M') - LS M (initial M)\<close> butlast_take 
          diff_Suc_Suc minus_nat.diff_0 not_less_eq_eq take_all)
  moreover have "((p_io []) @ ?io) \<notin> L M" 
    using \<open>take (Suc j) io \<notin> L M\<close> by auto
  moreover have "((p_io []) @ ?io) \<in> L M'" 
    using \<open>\<And> i . take i io \<in> L M'\<close> by auto
  ultimately have "sequence_to_failure_extending_preamble_path M M' PS [] ?io"
    unfolding sequence_to_failure_extending_preamble_path_def by force
  then show ?thesis 
    using that by blast
qed  
     

definition minimal_sequence_to_failure_extending_preamble_path :: 
  "('a,'b,'c) fsm \<Rightarrow> ('d,'b,'c) fsm \<Rightarrow> ('a \<times> ('a,'b,'c) fsm) set \<Rightarrow> ('a\<times>'b\<times>'c\<times>'a) list \<Rightarrow> ('b \<times> 'c) list \<Rightarrow> bool" 
  where
  "minimal_sequence_to_failure_extending_preamble_path M M' PS p io 
    = ((sequence_to_failure_extending_preamble_path M M' PS p io)
        \<and> (\<forall> p' io' . sequence_to_failure_extending_preamble_path M M' PS p' io' 
                        \<longrightarrow> length io \<le> length io'))"


lemma minimal_sequence_to_failure_extending_preamble_ex :
  assumes "(initial M, (initial_preamble M)) \<in> PS" (is "(initial M,?P) \<in> PS")
  and     "\<not> L M' \<subseteq> L M"
obtains p io where "minimal_sequence_to_failure_extending_preamble_path M M' PS p io"
proof -
  let ?ios = "{io . \<exists> p . sequence_to_failure_extending_preamble_path M M' PS p io}"
  let ?io_min = "arg_min length (\<lambda>io . io \<in> ?ios)"

  have "?ios \<noteq> {}"
    using sequence_to_failure_extending_preamble_ex[OF assms] by blast
  then have "?io_min \<in> ?ios" and "(\<forall> io' \<in> ?ios . length ?io_min \<le> length io')"
    by (meson arg_min_nat_lemma some_in_eq)+

  obtain p where "sequence_to_failure_extending_preamble_path M M' PS p ?io_min"
    using \<open>?io_min \<in> ?ios\<close>
    by auto
  moreover have "(\<forall> p' io' . sequence_to_failure_extending_preamble_path M M' PS p' io' \<longrightarrow> length ?io_min \<le> length io')"
    using \<open>(\<forall> io' \<in> ?ios . length ?io_min \<le> length io')\<close> by blast
  ultimately show ?thesis
    using that[of p ?io_min]
    unfolding minimal_sequence_to_failure_extending_preamble_path_def
    by blast
qed


lemma minimal_sequence_to_failure_extending_preamble_no_repetitions_along_path :
  assumes "minimal_sequence_to_failure_extending_preamble_path M M' PS pP io"
  and     "observable M"
  and     "path M (target (initial M) pP) p"
  and     "p_io p = butlast io"
  and     "q' \<in> io_targets M' (p_io pP) (initial M')"
  and     "path M' q' p'"
  and     "p_io p' = io"
  and     "i < j" 
  and     "j < length (butlast io)"
  and     "\<And> q P. (q, P) \<in> PS \<Longrightarrow> is_preamble P M q"
shows "t_target (p ! i) \<noteq> t_target (p ! j) \<or> t_target (p' ! i) \<noteq> t_target (p' ! j)"
proof (rule ccontr)
  assume "\<not> (t_target (p ! i) \<noteq> t_target (p ! j) \<or> t_target (p' ! i) \<noteq> t_target (p' ! j))"

  (* cut the loop and create a shorter path with the same target as p (p') *)

  then have "t_target (p ! i) = t_target (p ! j)"
       and  "t_target (p' ! i) = t_target (p' ! j)"
    by blast+

  have "sequence_to_failure_extending_preamble_path M M' PS pP io"
  and  "\<And> p' io' . sequence_to_failure_extending_preamble_path M M' PS p' io' 
                    \<Longrightarrow> length io \<le> length io'"
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
    by (metis \<open>path P (FSM.initial P) pP\<close> \<open>target (FSM.initial P) pP = q\<close> 
          path_target_is_state submachine_path) 

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
  then have "length p' > 0"
    using \<open>p_io p' = io\<close> by auto
  then have "p' = (butlast p')@[last p']"
    by auto
  then have "path M' q' ((butlast p')@[last p'])"
    using \<open>path M' q' p'\<close> by simp
  then have "path M' q' (butlast p')" and "(last p') \<in> transitions M'" and "t_source (last p') = target q' (butlast p')"
    by auto
    
  have "p_io (butlast p') = butlast io"
    using \<open>p' = (butlast p')@[last p']\<close> \<open>p_io p' = io\<close>
    using map_butlast by auto 

  let ?p = "((take (Suc i) p) @ (drop (Suc j) p))"
  let ?pCut = "(drop (Suc i) (take (Suc j) p))" (* the loop cut out of p *)
  let ?p' = "((take (Suc i) (butlast p')) @ (drop (Suc j) (butlast p')))"

  have "j < length p"
    using \<open>j < length (butlast io)\<close> \<open>p_io p = butlast io\<close>
    by (metis (no_types, lifting) length_map) 
  have "j < length (butlast p')"
    using \<open>j < length (butlast io)\<close> \<open>p_io p' = io\<close> \<open>p' = (butlast p')@[last p']\<close>
    by auto
  then have "t_target ((butlast p') ! i) = t_target ((butlast p') ! j)"
    using \<open>t_target (p' ! i) = t_target (p' ! j)\<close> 
    by (simp add: \<open>i < j\<close> dual_order.strict_trans nth_butlast) 

  have "path M q ?p" 
  and  "target q ?p = target q p" 
  and  "length ?p < length p"
  and  "path M (target q (take (Suc i) p)) ?pCut" 
  and  "target (target q (take (Suc i) p)) ?pCut = target q (take (Suc i) p)"
    using path_loop_cut[OF \<open>path M q p\<close> \<open>t_target (p ! i) = t_target (p ! j)\<close> \<open>i < j\<close> \<open>j < length p\<close>]
    by blast+

  have "path M' q' ?p'" 
  and  "target q' ?p' = target q' (butlast p')" 
  and  "length ?p' < length (butlast p')"
    using path_loop_cut[OF \<open>path M' q' (butlast p')\<close> \<open>t_target ((butlast p') ! i) = t_target ((butlast p') ! j)\<close> \<open>i < j\<close> \<open>j < length (butlast p')\<close>]
    by blast+
  
  have "path M' q' (?p'@[last p'])"
    using \<open>t_source (last p') = target q' (butlast p')\<close> 
    using path_append_transition[OF \<open>path M' q' ?p'\<close> \<open>(last p') \<in> transitions M'\<close>]
    unfolding \<open>target q' ?p' = target q' (butlast p')\<close> by simp

  have "p_io ?p' = p_io ?p"
    using \<open>p_io p = butlast io\<close> \<open>p_io (butlast p') = butlast io\<close>
    by (metis (no_types, lifting) drop_map map_append take_map)

  have min_prop: "length (p_io (?p'@[last p'])) < length io"
    using \<open>length ?p' < length (butlast p')\<close> \<open>p_io p' = io\<close> 
    unfolding length_map[of "(\<lambda> t . (t_input t, t_output t))"]
    by auto


  (* show that the shorter path would constitute a shorter seq to a failure, contradicting
     the minimality assumption on io *)

  have "q \<in> io_targets M (p_io pP) (initial M)"
    using \<open>path M (initial M) pP\<close> \<open>target (initial M) pP = q\<close> unfolding io_targets.simps
    by blast 

  have "((p_io pP) @ (p_io ?p)) \<in> L M"
    using language_io_target_append[OF \<open>q \<in> io_targets M (p_io pP) (initial M)\<close>, of "p_io ?p"]
          \<open>path M q ?p\<close>
    unfolding LS.simps by blast
  then have p1: "((p_io pP) @ butlast (p_io (?p' @ [last p']))) \<in> L M"
    unfolding \<open>p_io ?p' = p_io ?p\<close>[symmetric]
    by (metis (no_types, lifting) butlast_snoc map_butlast) 

  
  have p2: "((p_io pP) @ (p_io (?p' @ [last p']))) \<notin> L M"
  proof 
    assume "((p_io pP) @ (p_io (?p' @ [last p']))) \<in> L M"
    then obtain pCntr where "path M (initial M) pCntr" 
                        and "p_io pCntr = (p_io pP) @ (p_io (?p' @ [last p']))"
      by auto

    let ?pCntr1 = "(take (length (p_io pP)) pCntr)"
    let ?pCntr23 = "(drop (length (p_io pP)) pCntr)"

    have "path M (initial M) ?pCntr1" 
    and  "p_io ?pCntr1 = p_io pP"
    and  "path M (target (initial M) ?pCntr1) ?pCntr23"
    and  "p_io ?pCntr23 = p_io (?p' @ [last p'])"
      using path_io_split[OF \<open>path M (initial M) pCntr\<close> \<open>p_io pCntr = (p_io pP) @ (p_io (?p' @ [last p']))\<close>] 
      by blast+

    let ?pCntr2 = "(take (length (p_io (take (Suc i) (butlast p') @ drop (Suc j) (butlast p')))) (drop (length (p_io pP)) pCntr))"
    let ?pCntr3 = "(drop (length (p_io (take (Suc i) (butlast p') @ drop (Suc j) (butlast p')))) (drop (length (p_io pP)) pCntr))"

    have "p_io ?pCntr23 = p_io ?p' @ p_io [last p']"
      using \<open>p_io ?pCntr23 = p_io (?p' @ [last p'])\<close> by auto
    have "path M (target (initial M) ?pCntr1) ?pCntr2" 
    and  "p_io ?pCntr2 = p_io ?p'"
    and  "path M (target (target (initial M) ?pCntr1) ?pCntr2) ?pCntr3"
    and  "p_io ?pCntr3 = p_io [last p']"
      using path_io_split[OF \<open>path M (target (initial M) ?pCntr1) ?pCntr23\<close> \<open>p_io ?pCntr23 = p_io ?p' @ p_io [last p']\<close>]
      by blast+

    have "?pCntr1 = pP"
      using observable_path_unique[OF \<open>observable M\<close> \<open>path M (initial M) ?pCntr1\<close> \<open>path M (initial M) pP\<close> \<open>p_io ?pCntr1 = p_io pP\<close>]
      by assumption
    
    
    then have "(target (initial M) ?pCntr1) = q"
      using \<open>target (initial M) pP = q\<close> by auto
    then have "path M q ?pCntr2"
         and  "path M (target q ?pCntr2) ?pCntr3"
      using \<open>path M (target (initial M) ?pCntr1) ?pCntr2\<close>
            \<open>path M (target (target (initial M) ?pCntr1) ?pCntr2) ?pCntr3\<close>
      by auto

    have "?pCntr2 = ?p"
      using observable_path_unique[OF \<open>observable M\<close> \<open>path M q ?pCntr2\<close> \<open>path M q ?p\<close> ]
            \<open>p_io ?pCntr2 = p_io ?p'\<close>
      unfolding \<open>p_io ?p' = p_io ?p\<close>
      by blast
    then have "(target q ?pCntr2) = (target q ?p)"
      by auto
    then have "(target q ?pCntr2) = (target q p)"
      using \<open>target q ?p = target q p\<close> by auto    

    have "p_io ?pCntr3 = [last io]"
      using \<open>p_io ?pCntr3 = p_io [last p']\<close>
      by (metis (mono_tags, lifting) \<open>io \<noteq> []\<close> assms(7) last_map list.simps(8) list.simps(9))

    have "path M (initial M) (pP @ p @ ?pCntr3)"
      using \<open>path M (initial M) pP\<close> \<open>target (initial M) pP = q\<close> \<open>path M q p\<close> \<open>path M (target q ?pCntr2) ?pCntr3\<close>
      unfolding \<open>(target q ?pCntr2) = (target q p)\<close> 
      by auto
    moreover have "p_io (pP @ p @ ?pCntr3) = ((p_io pP) @ io)"
      using \<open>p_io p = butlast io\<close> \<open>p_io ?pCntr3 = [last io]\<close>
      by (simp add: \<open>io \<noteq> []\<close>) 
    ultimately have "((p_io pP) @ io) \<in> L M"
      by (metis (mono_tags, lifting) language_state_containment)
    then show "False"
      using \<open>((p_io pP) @ io) \<notin> L M\<close>
      by simp
  qed

  have p3: "((p_io pP) @ (p_io (?p' @ [last p']))) \<in> L M'"
    using language_io_target_append[OF \<open>q' \<in> io_targets M' (p_io pP) (initial M')\<close>, of "(p_io (?p' @ [last p']))"]
    using \<open>path M' q' (?p'@[last p'])\<close> 
    unfolding LS.simps
    by (metis (mono_tags, lifting) mem_Collect_eq) 

  have "sequence_to_failure_extending_preamble_path M M' PS pP (p_io (?p' @ [last p']))"
    unfolding sequence_to_failure_extending_preamble_path_def
    using \<open>q \<in> states M\<close>
          \<open>(q,P) \<in> PS\<close>
          \<open>path P (FSM.initial P) pP\<close>
          \<open>target (FSM.initial P) pP = q\<close>
          p1 p2 p3 by blast
  
  show "False"
    using \<open>\<And> p' io' . sequence_to_failure_extending_preamble_path M M' PS p' io' \<Longrightarrow> length io \<le> length io'\<close>[OF \<open>sequence_to_failure_extending_preamble_path M M' PS pP (p_io (?p' @ [last p']))\<close>]
          min_prop
    by simp
qed


lemma minimal_sequence_to_failure_extending_preamble_no_repetitions_with_other_preambles :
  assumes "minimal_sequence_to_failure_extending_preamble_path M M' PS pP io"
  and     "observable M"
  and     "path M (target (initial M) pP) p"
  and     "p_io p = butlast io"
  and     "q' \<in> io_targets M' (p_io pP) (initial M')"
  and     "path M' q' p'"
  and     "p_io p' = io"
  and     "\<And> q P. (q, P) \<in> PS \<Longrightarrow> is_preamble P M q"
  and     "i < length (butlast io)"
  and     "(t_target (p ! i), P') \<in> PS"
  and     "path P' (initial P') pP'"
  and     "target (initial P') pP' = t_target (p ! i)"
shows "t_target (p' ! i) \<notin> io_targets M' (p_io pP') (initial M')"
proof 
  assume "t_target (p' ! i) \<in> io_targets M' (p_io pP') (FSM.initial M')"

  (* Contradiction: (drop (Suc i) io) after (p_io pP') is a shorter sequence to a failure than io *)

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

  have "is_preamble P' M (t_target (p ! i))"
    using \<open>(t_target (p ! i), P') \<in> PS\<close> \<open>\<And> q P. (q, P) \<in> PS \<Longrightarrow> is_preamble P M q\<close> by blast
  then have "(t_target (p ! i)) \<in> states M"
    unfolding is_preamble_def
    by (metis \<open>path P' (initial P') pP'\<close> \<open>target (initial P') pP' = t_target (p ! i)\<close> path_target_is_state submachine_path) 

  have "initial P' = initial M"
    using \<open>is_preamble P' M (t_target (p ! i))\<close> unfolding is_preamble_def by auto
  have "path M (initial M) pP'"
    using \<open>is_preamble P' M (t_target (p ! i))\<close> unfolding is_preamble_def using submachine_path_initial
    using \<open>path P' (initial P') pP'\<close> by blast
  have "target (initial M) pP' = t_target (p ! i)"
    using \<open>target (initial P') pP' = t_target (p ! i)\<close> unfolding \<open>initial P' = initial M\<close> by simp

  have "io \<noteq> []"
    using \<open>((p_io pP) @ butlast io) \<in> L M\<close> \<open>((p_io pP) @ io) \<notin> L M\<close> by auto
  then have "length p' > 0"
    using \<open>p_io p' = io\<close> by auto
  then have "p' = (butlast p')@[last p']"
    by auto
  then have "path M' q' ((butlast p')@[last p'])"
    using \<open>path M' q' p'\<close> by simp
  then have "path M' q' (butlast p')" and "(last p') \<in> transitions M'" and "t_source (last p') = target q' (butlast p')"
    by auto    

  have "p_io (butlast p') = butlast io"
    using \<open>p' = (butlast p')@[last p']\<close> \<open>p_io p' = io\<close>
    using map_butlast by auto 

  have "butlast io \<noteq> []"
    using assms(9) by fastforce    

  let ?p = "(drop (Suc i) p)"
  let ?p' = "(drop (Suc i) (butlast p'))"

  have "i < length p"
    using \<open>i < length (butlast io)\<close> unfolding \<open>p_io p = butlast io\<close>[symmetric] length_map[of "(\<lambda> t . (t_input t, t_output t))"]
    by assumption
  then have "p ! i = last (take (Suc i) p)"
    by (simp add: take_last_index)
  then have "t_target (p ! i) = target q (take (Suc i) p)"
    unfolding target.simps visited_states.simps
    by (metis (no_types, lifting) \<open>i < length p\<close> gr_implies_not0 last_ConsR length_0_conv length_map nth_map old.nat.distinct(2) take_eq_Nil take_last_index take_map) 

  have "p = (take (Suc i) p @ ?p)"
    by simp
  then have "p_io p = (p_io (take (Suc i) p)) @ (p_io ?p)"
    by (metis map_append)
  have "(length (p_io (take (Suc i) p))) = Suc i"
    using \<open>i < length p\<close>
    unfolding length_map[of "(\<lambda> t . (t_input t, t_output t))"]
    by auto

  have "path M (t_target (p ! i)) ?p"
    using path_io_split(3)[OF \<open>path M q p\<close> \<open>p_io p = (p_io (take (Suc i) p)) @ (p_io ?p)\<close>]
    unfolding \<open>(length (p_io (take (Suc i) p))) = Suc i\<close> \<open>t_target (p ! i) = target q (take (Suc i) p)\<close>
    by assumption
  then have "path M (initial M) (pP' @ ?p)"
    using \<open>path M (initial M) pP'\<close> \<open>target (initial M) pP' = t_target (p ! i)\<close>
    by (simp add: path_append)
   
  let ?io = "(p_io ?p) @ [last io]"
  have is_shorter: "length ?io < length io"
  proof -
    have "p_io ?p = drop (Suc i) (butlast io)"
      by (metis assms(4) drop_map)
    moreover have "length (drop (Suc i) (butlast io)) < length (butlast io)"
      using assms(9) by auto
    ultimately have "length (p_io ?p) < length (butlast io)" 
      by simp
    then show ?thesis
      by auto
  qed
   
  have p1: "((p_io pP') @ (p_io ?p)) \<in> L M" 
    using \<open>path M (initial M) (pP' @ ?p)\<close>
    by (metis (mono_tags, lifting) language_state_containment map_append) 

  have p2: "((p_io pP') @ ?io) \<notin> L M"
  proof 
    assume "((p_io pP') @ ?io) \<in> L M"
    then obtain pCntr where "path M (initial M) pCntr" and "p_io pCntr = (p_io pP') @ (p_io ?p) @ [last io]"
      by auto

    let ?pCntr1 = "(take (length (p_io pP')) pCntr)"
    let ?pCntr23 = "(drop (length (p_io pP')) pCntr)"

    have "path M (initial M) ?pCntr1" 
    and  "p_io ?pCntr1 = p_io pP'"
    and  "path M (target (initial M) ?pCntr1) ?pCntr23"
    and  "p_io ?pCntr23 = (p_io ?p) @ [last io]"
      using path_io_split[OF \<open>path M (initial M) pCntr\<close> \<open>p_io pCntr = (p_io pP') @ (p_io ?p) @ [last io]\<close>] 
      by blast+

    have "?pCntr1 = pP'"
      using observable_path_unique[OF \<open>observable M\<close> \<open>path M (initial M) ?pCntr1\<close> \<open>path M (initial M) pP'\<close> \<open>p_io ?pCntr1 = p_io pP'\<close>]
      by assumption
    then have "(target (initial M) ?pCntr1) = (t_target (p ! i))"
      using \<open>target (initial M) pP' = (t_target (p ! i))\<close> by auto
    then have "path M (t_target (p ! i)) ?pCntr23"
      using \<open>path M (target (initial M) ?pCntr1) ?pCntr23\<close>
      by simp

    have "path M q (take (Suc i) p)"
      using \<open>path M q p\<close>
      by (metis append_take_drop_id path_prefix) 
    
    then have "path M q ((take (Suc i) p) @ ?pCntr23)"
      using \<open>path M (target (initial M) ?pCntr1) ?pCntr23\<close> 
      unfolding \<open>(target (initial M) ?pCntr1) = (t_target (p ! i))\<close>
      unfolding \<open>t_target (p ! i) = target q (take (Suc i) p)\<close> 
      by auto
    then have "path M (initial M) (pP @ ((take (Suc i) p) @ ?pCntr23))"
      using \<open>path M (initial M) pP\<close> \<open>target (initial M) pP = q\<close>
      by auto

    moreover have "p_io (pP @ ((take (Suc i) p) @ ?pCntr23)) = p_io pP @ io"
      using \<open>io \<noteq> []\<close> \<open>p_io (drop (length (p_io pP')) pCntr) = p_io (drop (Suc i) p) @ [last io]\<close> \<open>p_io p = p_io (take (Suc i) p) @ p_io (drop (Suc i) p)\<close> append_butlast_last_id assms(4) 
      by fastforce

    ultimately have "(p_io pP @ io) \<in> L M"
      by (metis (mono_tags, lifting) language_state_containment)

    then show "False" 
      using \<open>(p_io pP @ io) \<notin> L M\<close>
      by simp
  qed

  have p3: "((p_io pP') @ ?io) \<in> L M'"
  proof -
    have "i < length (butlast p')"
      using \<open>i < length (butlast io)\<close> unfolding \<open>p_io p' = io\<close>[symmetric] 
      using length_map[of "(\<lambda> t . (t_input t, t_output t))"]
      by simp
    then have "butlast p' ! i = last (take (Suc i) (butlast p'))"
      by (simp add: nth_butlast take_last_index) 
    moreover have "(take (Suc i) (butlast p')) \<noteq> []"
      by (metis Zero_not_Suc \<open>i < length (butlast p')\<close> list.size(3) not_less0 take_eq_Nil) 
    ultimately have "(target q' (take (Suc i) (butlast p'))) = t_target ((butlast p') ! i)"
      unfolding target.simps visited_states.simps
      by (simp add: last_map)
    moreover have "(butlast p') ! i = p' ! i"
      using \<open>i < length (butlast p')\<close>
      by (simp add: nth_butlast) 
    ultimately have "(target q' (take (Suc i) (butlast p'))) = t_target (p' ! i)"
      by simp

    have "p' = (take (Suc i) (butlast p')) @ ?p' @ [last p']"
      by (metis \<open>p' = butlast p' @ [last p']\<close> append.assoc append_take_drop_id) 
    then have "path M' (target q' (take (Suc i) (butlast p'))) (?p' @ [last p'])"
      by (metis assms(6) path_suffix) 
    then have "path M' (t_target (p' ! i)) (?p' @ [last p'])"
      unfolding \<open>(target q' (take (Suc i) (butlast p'))) = t_target (p' ! i)\<close> by assumption
    moreover have "p_io (?p' @ [last p']) = ?io"
      by (metis (no_types, lifting) \<open>io \<noteq> []\<close> \<open>p' = butlast p' @ [last p']\<close> \<open>p_io (butlast p') = butlast io\<close> append_butlast_last_id assms(4) assms(7) drop_map map_append same_append_eq) 
    ultimately have "?io \<in> LS M' (t_target (p' ! i))"
      by (metis (mono_tags, lifting) language_state_containment)

    show "((p_io pP') @ ?io) \<in> L M'"
      using language_io_target_append[OF \<open>t_target (p' ! i) \<in> io_targets M' (p_io pP') (FSM.initial M')\<close> \<open>?io \<in> LS M' (t_target (p' ! i))\<close>]
      by assumption   
  qed

  have *: "\<And> xs x . butlast (xs @ [x]) = xs" by auto

  have "sequence_to_failure_extending_preamble_path M M' PS pP' ?io"
    unfolding sequence_to_failure_extending_preamble_path_def
    using \<open>t_target (p ! i) \<in> states M\<close> assms(10-12) p1 p2 p3 
    unfolding * by blast

  then have "length io \<le> length ?io"
    using \<open>\<And> p' io' . sequence_to_failure_extending_preamble_path M M' PS p' io' \<Longrightarrow> length io \<le> length io'\<close>
    by blast

  then show "False"
    using is_shorter
    by simp
qed


end