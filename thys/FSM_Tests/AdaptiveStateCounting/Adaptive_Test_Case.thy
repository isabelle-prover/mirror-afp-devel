section \<open>Adaptive Test Cases\<close>

text \<open>An ATC is a single input, acyclic, observable FSM, which is equivalent to a tree whose non-leaf 
      states are labeled with inputs and whose edges are labeled with outputs.\<close>

theory Adaptive_Test_Case
  imports State_Separator 
begin


definition is_ATC :: "('a,'b,'c) fsm \<Rightarrow> bool" where
  "is_ATC M = (single_input M \<and> acyclic M \<and> observable M)"

lemma is_ATC_from :
  assumes "t \<in> transitions A"
  and     "t_source t \<in> reachable_states A"
  and     "is_ATC A"
shows "is_ATC (from_FSM A (t_target t))"
  using from_FSM_single_input[of A]
        from_FSM_acyclic[OF reachable_states_next[OF assms(2,1)]] 
        from_FSM_observable[of A]
        assms(3)
  unfolding is_ATC_def by fast
  


subsection \<open>Applying Adaptive Test Cases\<close>


(* FSM M passes ATC A if and only if the parallel execution of M and A does not visit a fail_state in A and M produces no output not allowed in A *)
fun pass_ATC' :: "('a,'b,'c) fsm \<Rightarrow> ('d,'b,'c) fsm \<Rightarrow> 'd set \<Rightarrow> nat \<Rightarrow> bool" where
  "pass_ATC' M A fail_states 0 = (\<not> (initial A \<in> fail_states))" |
  "pass_ATC' M A fail_states (Suc k) = ((\<not> (initial A \<in> fail_states)) \<and> 
    (\<forall> x \<in> inputs A . h A (initial A,x) \<noteq> {} \<longrightarrow> (\<forall> (yM,qM) \<in> h M (initial M,x) . \<exists> (yA,qA) \<in> h A (initial A,x) . yM = yA \<and> pass_ATC' (from_FSM M qM) (from_FSM A qA) fail_states k)))"


(* Applies pass_ATC' for a depth of at most (size A) (i.e., an upper bound on the length of paths in A) *)
fun pass_ATC :: "('a,'b,'c) fsm \<Rightarrow> ('d,'b,'c) fsm \<Rightarrow> 'd set \<Rightarrow> bool" where
  "pass_ATC M A fail_states = pass_ATC' M A fail_states (size A)"


lemma pass_ATC'_initial :
  assumes "pass_ATC' M A FS k"
  shows "initial A \<notin> FS"
using assms by (cases k; auto) 


lemma pass_ATC'_io :
  assumes "pass_ATC' M A FS k"
  and     "is_ATC A"
  and     "observable M"
  and     "(inputs A) \<subseteq> (inputs M)"
  and     "io@[ioA] \<in> L A"
  and     "io@[ioM] \<in> L M"
  and     "fst ioA = fst ioM"
  and     "length (io@[ioA]) \<le> k"
shows "io@[ioM] \<in> L A"
and   "io_targets A (io@[ioM]) (initial A) \<inter> FS = {}"
proof -
  have "io@[ioM] \<in> L A \<and> io_targets A (io@[ioM]) (initial A) \<inter> FS = {}"
    using assms proof (induction k arbitrary: io A M)
    case 0
    then show ?case by auto
  next
    case (Suc k)
    then show ?case proof (cases io)
      case Nil
      
      obtain tA where "tA \<in> transitions A"
                  and "t_source tA = initial A"
                  and "t_input tA = fst ioA"
                  and "t_output tA = snd ioA"
        using Nil \<open>io@[ioA] \<in> L A\<close> by auto
      then have "fst ioA \<in> (inputs A)"
        using fsm_transition_input by fastforce

      have "(t_output tA,t_target tA) \<in> h A (initial A,t_input tA)"
        using \<open>tA \<in> transitions A\<close> \<open>t_source tA = initial A\<close> unfolding h_simps
        by (metis (no_types, lifting) case_prodI mem_Collect_eq prod.collapse) 
      then have "h A (initial A,fst ioA) \<noteq> {}"
        unfolding \<open>t_input tA = fst ioA\<close> by blast
        
      then have *: "\<And> yM qM . (yM,qM) \<in> h M (initial M,fst ioA) \<Longrightarrow> (\<exists> (yA,qA) \<in> h A (initial A,fst ioA) . yM = yA \<and> pass_ATC' (from_FSM M qM) (from_FSM A qA) FS k)"
        using Suc.prems(1) pass_ATC'_initial[OF Suc.prems(1)] unfolding pass_ATC'.simps
        using \<open>fst ioA \<in> FSM.inputs A\<close> by auto

      obtain tM where "tM \<in> transitions M"
                  and "t_source tM = initial M"
                  and "t_input tM = fst ioA"
                  and "t_output tM = snd ioM"
        using Nil \<open>io@[ioM] \<in> L M\<close> \<open>fst ioA = fst ioM\<close> by auto
      have "(t_output tM,t_target tM) \<in> h M (initial M,fst ioA)"
        using \<open>tM \<in> transitions M\<close> \<open>t_source tM = initial M\<close> \<open>t_input tM = fst ioA\<close> unfolding h_simps
        by (metis (mono_tags, lifting) case_prodI mem_Collect_eq prod.collapse)

      obtain tA' where "tA' \<in> transitions A"
                        and "t_source tA' = initial A"
                        and "t_input tA' = fst ioA"
                        and "t_output tA' = snd ioM"
                        and "pass_ATC' (from_FSM M (t_target tM)) (from_FSM A (t_target tA')) FS k"
        using *[OF \<open>(t_output tM,t_target tM) \<in> h M (initial M,fst ioA)\<close>]
        unfolding h.simps \<open>t_output tM = snd ioM\<close> by fastforce

      then have "path A (initial A) [tA']"
        using single_transition_path[OF \<open>tA' \<in> transitions A\<close>] by auto
      moreover have "p_io [tA'] = [ioM]"
        using \<open>t_input tA' = fst ioA\<close> \<open>t_output tA' = snd ioM\<close> unfolding \<open>fst ioA = fst ioM\<close> by auto
      ultimately have "[ioM] \<in> LS A (initial A)"
        unfolding LS.simps by (metis (mono_tags, lifting) mem_Collect_eq) 
      then have "io @ [ioM] \<in> LS A (initial A)"
        using Nil by auto


      have "target (initial A) [tA'] = t_target tA'"
        by auto
      then have "t_target tA' \<in> io_targets A [ioM] (initial A)"
        unfolding io_targets.simps 
        using \<open>path A (initial A) [tA']\<close> \<open>p_io [tA'] = [ioM]\<close>
        by (metis (mono_tags, lifting) mem_Collect_eq)
      then have "io_targets A (io @ [ioM]) (initial A) = {t_target tA'}"
        using observable_io_targets[OF _ \<open>io @ [ioM] \<in> LS A (initial A)\<close>] \<open>is_ATC A\<close> Nil
        unfolding is_ATC_def
        by (metis append_self_conv2 singletonD) 
      moreover have "t_target tA' \<notin> FS"
        using pass_ATC'_initial[OF \<open>pass_ATC' (from_FSM M (t_target tM)) (from_FSM A (t_target tA')) FS k\<close>]
        unfolding from_FSM_simps(1)[OF fsm_transition_target[OF \<open>tA' \<in> transitions A\<close>]] by assumption
      ultimately have "io_targets A (io @ [ioM]) (initial A) \<inter> FS = {}"
        by auto
      
      then show ?thesis
        using \<open>io @ [ioM] \<in> LS A (initial A)\<close> by auto
    next
      case (Cons io' io'')

      have "[io'] \<in> L A"
        using Cons \<open>io@[ioA] \<in> L A\<close>
        by (metis append.left_neutral append_Cons language_prefix)
      then obtain tA where "tA \<in> transitions A"
                  and "t_source tA = initial A"
                  and "t_input tA = fst io'"
                  and "t_output tA = snd io'"
        by auto
      then have "fst io' \<in> (inputs A)" 
        using fsm_transition_input by metis


      have "(t_output tA,t_target tA) \<in> h A (initial A,t_input tA)"
        using \<open>tA \<in> transitions A\<close> \<open>t_source tA = initial A\<close> unfolding h_simps
        by (metis (no_types, lifting) case_prodI mem_Collect_eq prod.collapse) 
      then have "h A (initial A,fst io') \<noteq> {}"
        unfolding \<open>t_input tA = fst io'\<close> by blast
        
      then have *: "\<And> yM qM . (yM,qM) \<in> h M (initial M,fst io') \<Longrightarrow> (\<exists> (yA,qA) \<in> h A (initial A,fst io') . yM = yA \<and> pass_ATC' (from_FSM M qM) (from_FSM A qA) FS k)"
        using Suc.prems(1) pass_ATC'_initial[OF Suc.prems(1)] unfolding pass_ATC'.simps
        using \<open>fst io' \<in> FSM.inputs A\<close> by auto

      obtain tM where "tM \<in> transitions M"
                  and "t_source tM = initial M"
                  and "t_input tM = fst io'"
                  and "t_output tM = snd io'"
        using Cons \<open>io@[ioM] \<in> L M\<close> \<open>fst ioA = fst ioM\<close> by auto
      have "(t_output tM,t_target tM) \<in> h M (initial M,fst io')"
        using \<open>tM \<in> transitions M\<close> \<open>t_source tM = initial M\<close> \<open>t_input tM = fst io'\<close> unfolding h_simps
        by (metis (mono_tags, lifting) case_prodI mem_Collect_eq prod.collapse)

      obtain tA' where "tA' \<in> transitions A"
                        and "t_source tA' = initial A"
                        and "t_input tA' = fst io'"
                        and "t_output tA' = snd io'"
                        and "pass_ATC' (from_FSM M (t_target tM)) (from_FSM A (t_target tA')) FS k"
        using *[OF \<open>(t_output tM,t_target tM) \<in> h M (initial M,fst io')\<close>]
        unfolding h.simps \<open>t_output tM = snd io'\<close> by fastforce
      
      then have "tA = tA'"
        using \<open>is_ATC A\<close>
        unfolding is_ATC_def observable.simps 
        by (metis \<open>tA \<in> transitions A\<close> \<open>t_input tA = fst io'\<close> \<open>t_output tA = snd io'\<close> \<open>t_source tA = initial A\<close> prod.collapse)      
      then have "pass_ATC' (from_FSM M (t_target tM)) (from_FSM A (t_target tA)) FS k"
        using \<open>pass_ATC' (from_FSM M (t_target tM)) (from_FSM A (t_target tA')) FS k\<close> by auto
      
      have "(inputs (from_FSM A (t_target tA))) \<subseteq> (inputs (from_FSM M (t_target tM)))"
        using Suc.prems(4) 
        unfolding from_FSM_simps(2)[OF fsm_transition_target[OF \<open>tM \<in> transitions M\<close>]]
                  from_FSM_simps(2)[OF fsm_transition_target[OF \<open>tA \<in> transitions A\<close>]] by assumption

      have "length (io'' @ [ioA]) \<le> k"
        using Cons \<open>length (io @ [ioA]) \<le> Suc k\<close> by auto

      have "(io' # (io''@[ioA])) \<in> LS A (t_source tA)"
        using \<open>t_source tA = initial A\<close> \<open>io@[ioA] \<in> L A\<close> Cons by auto
      have "io'' @ [ioA] \<in> LS (from_FSM A (t_target tA)) (initial (from_FSM A (t_target tA)))"
        using observable_language_next[OF \<open>(io' # (io''@[ioA])) \<in> LS A (t_source tA)\<close>]
              \<open>is_ATC A\<close> \<open>tA \<in> transitions A\<close> \<open>t_input tA = fst io'\<close> \<open>t_output tA = snd io'\<close>
        using is_ATC_def by blast 

      have "(io' # (io''@[ioM])) \<in> LS M (t_source tM)"
        using \<open>t_source tM = initial M\<close> \<open>io@[ioM] \<in> L M\<close> Cons by auto
      have "io'' @ [ioM] \<in> LS (from_FSM M (t_target tM)) (initial (from_FSM M (t_target tM)))"
        using observable_language_next[OF \<open>(io' # (io''@[ioM])) \<in> LS M (t_source tM)\<close>]
              \<open>observable M\<close> \<open>tM \<in> transitions M\<close> \<open>t_input tM = fst io'\<close> \<open>t_output tM = snd io'\<close>
        by blast
        
      have "observable (from_FSM M (t_target tM))"
        using from_FSM_observable[OF \<open>observable M\<close>] by blast

      have "is_ATC (FSM.from_FSM A (t_target tA))"
        using is_ATC_from[OF \<open>tA \<in> transitions A\<close> _  \<open>is_ATC A\<close>] reachable_states_initial
        unfolding \<open>t_source tA = initial A\<close> by blast

      have "io'' @ [ioM] \<in> LS (from_FSM A (t_target tA)) (initial (from_FSM A (t_target tA)))"
       and "io_targets (from_FSM A (t_target tA)) (io'' @ [ioM]) (initial (from_FSM A (t_target tA))) \<inter> FS = {}" 
        using Suc.IH[OF \<open>pass_ATC' (from_FSM M (t_target tM)) (from_FSM A (t_target tA)) FS k\<close>
                        \<open>is_ATC (FSM.from_FSM A (t_target tA))\<close>
                        \<open>observable (from_FSM M (t_target tM))\<close>
                        \<open>(inputs (from_FSM A (t_target tA))) \<subseteq> (inputs (from_FSM M (t_target tM)))\<close>
                        \<open>io'' @ [ioA] \<in> LS (from_FSM A (t_target tA)) (initial (from_FSM A (t_target tA)))\<close>
                        \<open>io'' @ [ioM] \<in> LS (from_FSM M (t_target tM)) (initial (from_FSM M (t_target tM)))\<close>
                        \<open>fst ioA = fst ioM\<close>
                        \<open>length (io'' @ [ioA]) \<le> k\<close>]
        by blast+

      then obtain pA where "path (from_FSM A (t_target tA)) (initial (from_FSM A (t_target tA))) pA" and "p_io pA = io'' @ [ioM]"
        by auto

      have "path A (initial A) (tA#pA)"
        using \<open>path (from_FSM A (t_target tA)) (initial (from_FSM A (t_target tA))) pA\<close> \<open>tA \<in> transitions A\<close> 
        by (metis \<open>t_source tA = initial A\<close> cons from_FSM_path_initial fsm_transition_target)
      moreover have "p_io (tA#pA) = io' # io'' @ [ioM]"
        using \<open>t_input tA = fst io'\<close> \<open>t_output tA = snd io'\<close> \<open>p_io pA = io'' @ [ioM]\<close> by auto
      ultimately have "io' # io'' @ [ioM] \<in> L A"
        unfolding LS.simps
        by (metis (mono_tags, lifting) mem_Collect_eq) 
      then have "io @ [ioM] \<in> L A"
        using Cons by auto

      have "observable A"
        using Suc.prems(2) is_ATC_def by blast

      have "io_targets A (io @ [ioM]) (FSM.initial A) \<inter> FS = {}"
      proof -
        have "\<And> p . path A (FSM.initial A) p \<Longrightarrow> p_io p = (io' # io'') @ [ioM] \<Longrightarrow> p = tA # (tl p)"
          using \<open>observable A\<close> unfolding observable.simps 
          using \<open>tA \<in> transitions A\<close> \<open>t_source tA = initial A\<close> \<open>t_input tA = fst io'\<close> \<open>t_output tA = snd io'\<close> by fastforce

        have "\<And> q . q \<in> io_targets A (io @ [ioM]) (FSM.initial A) \<Longrightarrow> q \<in> io_targets (from_FSM A (t_target tA)) (io'' @ [ioM]) (initial (from_FSM A (t_target tA)))"
        proof -
          fix q assume "q \<in> io_targets A (io @ [ioM]) (FSM.initial A)"
          then obtain p where "q = target (FSM.initial A) p" and "path A (FSM.initial A) p" and "p_io p = (io' # io'') @ [ioM]"
            unfolding io_targets.simps Cons by blast
          then have "p = tA # (tl p)"
            using \<open>\<And> p . path A (FSM.initial A) p \<Longrightarrow> p_io p = (io' # io'') @ [ioM] \<Longrightarrow> p = tA # (tl p)\<close> by blast

          have "path A (FSM.initial A) (tA#(tl p))"
            using \<open>path A (FSM.initial A) p\<close> \<open>p = tA # (tl p)\<close> by simp
          then have "path (from_FSM A (t_target tA)) (initial (from_FSM A (t_target tA))) (tl p)"
            by (meson from_FSM_path_initial fsm_transition_target path_cons_elim)
          moreover have "p_io (tl p) = (io'') @ [ioM]"
            using \<open>p_io p = (io' # io'') @ [ioM]\<close> \<open>p = tA # (tl p)\<close> by auto
          moreover have "q = target (initial (from_FSM A (t_target tA))) (tl p)"
            using \<open>q = target (FSM.initial A) p\<close> \<open>p = tA # (tl p)\<close> 
            unfolding target.simps visited_states.simps from_FSM_simps[OF fsm_transition_target[OF \<open>tA \<in> transitions A\<close>]] 
            by (cases p; auto)
          ultimately show "q \<in> io_targets (from_FSM A (t_target tA)) (io'' @ [ioM]) (initial (from_FSM A (t_target tA)))"
            unfolding io_targets.simps by blast
        qed
        moreover have "\<And> q . q \<in> io_targets (from_FSM A (t_target tA)) (io'' @ [ioM]) (initial (from_FSM A (t_target tA))) \<Longrightarrow> q \<in> io_targets A (io @ [ioM]) (FSM.initial A)"
        proof -
          fix q assume "q \<in> io_targets (from_FSM A (t_target tA)) (io'' @ [ioM]) (initial (from_FSM A (t_target tA)))"
          then obtain p where "q = target (FSM.initial (FSM.from_FSM A (t_target tA))) p" and "path (FSM.from_FSM A (t_target tA)) (FSM.initial (FSM.from_FSM A (t_target tA))) p" and "p_io p = io'' @ [ioM]"
            unfolding io_targets.simps Cons by blast

          have "q = target (FSM.initial A) (tA#p)"
            unfolding \<open>q = target (FSM.initial (FSM.from_FSM A (t_target tA))) p\<close> from_FSM_simps[OF fsm_transition_target[OF \<open>tA \<in> transitions A\<close>]] by auto
          moreover have "path A (initial A) (tA#p)"
            using \<open>path (FSM.from_FSM A (t_target tA)) (FSM.initial (FSM.from_FSM A (t_target tA))) p\<close>
            unfolding from_FSM_path_initial[OF fsm_transition_target[OF \<open>tA \<in> transitions A\<close>], symmetric]
            using \<open>tA \<in> transitions A\<close> \<open>t_source tA = initial A\<close> cons 
            by fastforce 
          moreover have "p_io (tA#p) = io @ [ioM]"
            using \<open>p_io p = io'' @ [ioM]\<close> \<open>t_input tA = fst io'\<close> \<open>t_output tA = snd io'\<close> unfolding Cons by simp
          ultimately show "q \<in> io_targets A (io @ [ioM]) (FSM.initial A)"
            unfolding io_targets.simps by fastforce
        qed
        ultimately show ?thesis 
          using \<open>io_targets (from_FSM A (t_target tA)) (io'' @ [ioM]) (initial (from_FSM A (t_target tA))) \<inter> FS = {}\<close> by blast
      qed

      then show ?thesis
        using \<open>io @ [ioM] \<in> L A\<close> by simp
    qed
  qed

  then show "io@[ioM] \<in> L A"
        and "io_targets A (io@[ioM]) (initial A) \<inter> FS = {}"
    by simp+
qed


lemma pass_ATC_io :
  assumes "pass_ATC M A FS"
  and     "is_ATC A"
  and     "observable M"
  and     "(inputs A) \<subseteq> (inputs M)"
  and     "io@[ioA] \<in> L A"
  and     "io@[ioM] \<in> L M"
  and     "fst ioA = fst ioM" 
shows "io@[ioM] \<in> L A"
and   "io_targets A (io@[ioM]) (initial A) \<inter> FS = {}"
proof -

  have "acyclic A"
    using \<open>is_ATC A\<close> is_ATC_def by blast 

  then have "length (io @ [ioA]) \<le> (size A)"
    using \<open>io@[ioA] \<in> L A\<close> unfolding LS.simps 
    using acyclic_path_length_limit unfolding acyclic.simps by fastforce
  
  show "io@[ioM] \<in> L A"
  and  "io_targets A (io@[ioM]) (initial A) \<inter> FS = {}"
    using pass_ATC'_io[OF _ assms(2-7) \<open>length (io @ [ioA]) \<le> (size A)\<close>]
    using assms(1) by simp+
qed


lemma pass_ATC_io_explicit_io_tuple :
  assumes "pass_ATC M A FS"
  and     "is_ATC A"
  and     "observable M"
  and     "(inputs A) \<subseteq> (inputs M)"
  and     "io@[(x,y)] \<in> L A"
  and     "io@[(x,y')] \<in> L M" 
shows "io@[(x,y')] \<in> L A"
and   "io_targets A (io@[(x,y')]) (initial A) \<inter> FS = {}"
  apply (metis pass_ATC_io(1) assms fst_conv)
  by (metis pass_ATC_io(2) assms fst_conv)


lemma pass_ATC_io_fail_fixed_io :
  assumes "is_ATC A"
  and     "observable M"
  and     "(inputs A) \<subseteq> (inputs M)"
  and     "io@[ioA] \<in> L A"
  and     "io@[ioM] \<in> L M"
  and     "fst ioA = fst ioM" 
  and     "io@[ioM] \<notin> L A \<or> io_targets A (io@[ioM]) (initial A) \<inter> FS \<noteq> {}"
shows "\<not>pass_ATC M A FS" 
proof -
  consider (a) "io@[ioM] \<notin> L A" |
           (b) "io_targets A (io@[ioM]) (initial A) \<inter> FS \<noteq> {}"
    using assms(7) by blast 
  then show ?thesis proof (cases)
    case a
    then show ?thesis using pass_ATC_io(1)[OF _ assms(1-6)] by blast
  next
    case b
    then show ?thesis using pass_ATC_io(2)[OF _ assms(1-6)] by blast
  qed
qed


lemma pass_ATC'_io_fail :
  assumes "\<not>pass_ATC' M A FS k "
  and     "is_ATC A"
  and     "observable M"
  and     "(inputs A) \<subseteq> (inputs M)"
shows "initial A \<in> FS \<or> (\<exists> io ioA ioM . io@[ioA] \<in> L A
                          \<and> io@[ioM] \<in> L M
                          \<and> fst ioA = fst ioM
                          \<and> (io@[ioM] \<notin> L A \<or> io_targets A (io@[ioM]) (initial A) \<inter> FS \<noteq> {}))"
using assms proof (induction k arbitrary: M A)
  case 0
  then show ?case by auto
next
  case (Suc k)
  then show ?case proof (cases "initial A \<in> FS")
    case True
    then show ?thesis by auto
  next
    case False 
    then obtain x where "x \<in> inputs A"
                    and "h A (FSM.initial A, x) \<noteq> {}"
                    and "\<not>(\<forall>(yM, qM)\<in>h M (initial M, x). \<exists>(yA, qA)\<in>h A (FSM.initial A, x). yM = yA \<and> pass_ATC' (FSM.from_FSM M qM) (FSM.from_FSM A qA) FS k)"
      using Suc.prems(1) unfolding pass_ATC'.simps
      by fastforce 

    obtain tM where "tM \<in> transitions M"
                and "t_source tM = initial M"
                and "t_input tM = x"
                and "\<not>(\<exists>(yA, qA)\<in>h A (FSM.initial A, x). t_output tM = yA \<and> pass_ATC' (FSM.from_FSM M (t_target tM)) (FSM.from_FSM A qA) FS k)"
      using \<open>\<not>(\<forall>(yM, qM)\<in>h M (initial M, x). \<exists>(yA, qA)\<in>h A (FSM.initial A, x). yM = yA \<and> pass_ATC' (FSM.from_FSM M qM) (FSM.from_FSM A qA) FS k)\<close>  
      unfolding h.simps
      by auto  

    have "\<not> (\<exists> tA . tA \<in> transitions A \<and> t_source tA = initial A \<and> t_input tA = x \<and> t_output tA = t_output tM \<and> pass_ATC' (FSM.from_FSM M (t_target tM)) (FSM.from_FSM A (t_target tA)) FS k)"
      using \<open>\<not>(\<exists>(yA, qA)\<in>h A (FSM.initial A, x). t_output tM = yA \<and> pass_ATC' (FSM.from_FSM M (t_target tM)) (FSM.from_FSM A qA) FS k)\<close>
      unfolding h.simps by force
    moreover have "\<exists> tA . tA \<in> transitions A \<and> t_source tA = initial A \<and> t_input tA = x"
      using \<open>h A (FSM.initial A, x) \<noteq> {}\<close> unfolding h.simps by force
    ultimately consider 
      (a) "\<And> tA . tA \<in> transitions A \<Longrightarrow> t_source tA = initial A \<Longrightarrow> t_input tA = x \<Longrightarrow> t_output tM \<noteq> t_output tA" |
      (b) "\<exists> tA . tA \<in> transitions A \<and> t_source tA = initial A \<and> t_input tA = x \<and> t_output tA = t_output tM \<and> \<not>pass_ATC' (FSM.from_FSM M (t_target tM)) (FSM.from_FSM A (t_target tA)) FS k"
      by force
    then show ?thesis proof cases
      case a
      then have "[(x,t_output tM)] \<notin> L A" 
        unfolding LS.simps by fastforce 
      moreover have "\<exists> y . [(x,y)] \<in> L A"
        using \<open>h A (FSM.initial A, x) \<noteq> {}\<close> unfolding h.simps LS.simps 
      proof -
        obtain pp :: "'d \<times> 'b \<times> 'c \<times> 'd" where
          f1: "pp \<in> FSM.transitions A \<and> t_source pp = FSM.initial A \<and> t_input pp = x"
          using \<open>\<exists>tA. tA \<in> FSM.transitions A \<and> t_source tA = FSM.initial A \<and> t_input tA = x\<close> by blast
        then have "path A (FSM.initial A) [pp]"
          by (metis single_transition_path)
        then have "(t_input pp, t_output pp) # p_io ([]::('d \<times> 'b \<times> 'c \<times> _) list) \<in> {p_io ps |ps. path A (FSM.initial A) ps}"
          by force
        then show "\<exists>c. [(x, c)] \<in> {p_io ps |ps. path A (FSM.initial A) ps}"
          using f1 by force
      qed 
      moreover have "[(x,t_output tM)] \<in> L M"
        unfolding LS.simps using \<open>tM \<in> transitions M\<close> \<open>t_input tM = x\<close> \<open>t_source tM = initial M\<close>
      proof -
        have "\<exists>ps. p_io [tM] = p_io ps \<and> path M (FSM.initial M) ps"
          by (metis (no_types) \<open>tM \<in> FSM.transitions M\<close> \<open>t_source tM = FSM.initial M\<close> single_transition_path)
        then show "[(x, t_output tM)] \<in> {p_io ps |ps. path M (FSM.initial M) ps}"
          by (simp add: \<open>t_input tM = x\<close>)
      qed 
      ultimately have "(\<exists>io ioA ioM. io @ [ioA] \<in> L A \<and> io @ [ioM] \<in> L M \<and> fst ioA = fst ioM \<and> (io @ [ioM] \<notin> L A))"
        by (metis append_self_conv2 fst_conv)
      then show ?thesis by blast 
    next
      case b
      then obtain t' where "t' \<in> transitions A" 
                       and "t_source t' = initial A" 
                       and "t_input t' = x" 
                       and "t_output t' = t_output tM" 
                       and "\<not>pass_ATC' (FSM.from_FSM M (t_target tM)) (FSM.from_FSM A (t_target t')) FS k"
        by blast

      have "is_ATC (FSM.from_FSM A (t_target t'))"
        using is_ATC_from[OF \<open>t' \<in> transitions A\<close> _ \<open>is_ATC A\<close>] reachable_states_initial
        unfolding \<open>t_source t' = initial A\<close> by blast

      have "(inputs (from_FSM A (t_target t'))) \<subseteq> (inputs (from_FSM M (t_target tM)))"
        by (simp add: Suc.prems(4) \<open>t' \<in> FSM.transitions A\<close> \<open>tM \<in> FSM.transitions M\<close> fsm_transition_target)

      let ?ioM = "(x,t_output tM)"
      let ?ioA = "(x,t_output t')"


      consider (b1) "initial (from_FSM A (t_target t')) \<in> FS" |
               (b2) "(\<exists>io ioA ioM.
                        io @ [ioA] \<in> LS (from_FSM A (t_target t')) (initial (from_FSM A (t_target t'))) \<and>
                        io @ [ioM] \<in> LS (from_FSM M (t_target tM)) (initial (from_FSM M (t_target tM))) \<and>
                        fst ioA = fst ioM \<and>
                        (io @ [ioM] \<notin> LS (from_FSM A (t_target t')) (initial (from_FSM A (t_target t'))) \<or>
                        io_targets (from_FSM A (t_target t')) (io @ [ioM]) (initial (from_FSM A (t_target t'))) \<inter> FS \<noteq> {}))"
        using Suc.IH[OF \<open>\<not>pass_ATC' (FSM.from_FSM M (t_target tM)) (FSM.from_FSM A (t_target t')) FS k\<close>
                        \<open>is_ATC (FSM.from_FSM A (t_target t'))\<close>
                        from_FSM_observable[OF \<open>observable M\<close>]
                        \<open>(inputs (from_FSM A (t_target t'))) \<subseteq> (inputs (from_FSM M (t_target tM)))\<close>]
        by blast              
      then show ?thesis proof cases
        case b1 (* analogous to case a *)

        have "[?ioA] \<in> L A"
          unfolding LS.simps
        proof -
          have "\<exists>ps. [(x, t_output t')] = p_io ps \<and> path A (t_source t') ps"
            using \<open>t' \<in> FSM.transitions A\<close> \<open>t_input t' = x\<close> by force
          then show "[(x, t_output t')] \<in> {p_io ps |ps. path A (FSM.initial A) ps}"
            by (simp add: \<open>t_source t' = FSM.initial A\<close>)
        qed 

        have "[?ioM] \<in> L M" 
          unfolding LS.simps
        proof -
          have "path M (FSM.initial M) [tM]"
            by (metis \<open>tM \<in> FSM.transitions M\<close> \<open>t_source tM = FSM.initial M\<close> single_transition_path)
          then have "\<exists>ps. [(x, t_output tM)] = p_io ps \<and> path M (FSM.initial M) ps"
            using \<open>t_input tM = x\<close> by force
          then show "[(x, t_output tM)] \<in> {p_io ps |ps. path M (FSM.initial M) ps}"
            by simp
        qed

        have "p_io [t'] = [(x, t_output tM)]"
          using \<open>t_input t' = x\<close> \<open>t_output t' = t_output tM\<close>
          by auto
        moreover have "target (initial A) [t'] = t_target t'"
          using \<open>t_source t' = initial A\<close> by auto
        ultimately have "t_target t' \<in> io_targets A [(x,t_output tM)] (initial A)"
          unfolding io_targets.simps
          using single_transition_path[OF \<open>t' \<in> transitions A\<close>]
          by (metis (mono_tags, lifting) \<open>t_source t' = initial A\<close> mem_Collect_eq)
        then have "initial (from_FSM A (t_target t')) \<in> io_targets A [(x,t_output tM)] (initial A)"
          unfolding io_targets.simps from_FSM_simps[OF fsm_transition_target[OF \<open>t' \<in> transitions A\<close>]] by simp
        then have "io_targets A ([] @ [?ioM]) (initial A) \<inter> FS \<noteq> {}"
          using b1 by (metis IntI append_Nil empty_iff) 

        then have "\<exists> io ioA ioM . io@[ioA] \<in> L A
                          \<and> io@[ioM] \<in> L M
                          \<and> fst ioA = fst ioM
                          \<and> io_targets A (io @ [ioM]) (initial A) \<inter> FS \<noteq> {}"
          using \<open>[?ioA] \<in> L A\<close> \<open>[?ioM] \<in> L M\<close>
          by (metis \<open>t_output t' = t_output tM\<close> append.left_neutral) 
        
        then show ?thesis by blast

      next
        case b2 (* obtain io ioA ioM and prepend (x,t_output tM) *)

        then obtain io ioA ioM where
              "io @ [ioA] \<in> LS (from_FSM A (t_target t')) (initial (from_FSM A (t_target t')))"
          and "io @ [ioM] \<in> LS (from_FSM M (t_target tM)) (initial (from_FSM M (t_target tM)))"
          and "fst ioA = fst ioM"
          and "(io @ [ioM] \<notin> LS (from_FSM A (t_target t')) (initial (from_FSM A (t_target t'))) \<or> io_targets (from_FSM A (t_target t')) (io @ [ioM]) (initial (from_FSM A (t_target t'))) \<inter> FS \<noteq> {})"
          by blast

        have "observable A"
              using Suc.prems(2) is_ATC_def by blast

        have "(?ioM # io) @ [ioA] \<in> L A"
          using language_state_prepend_transition[OF \<open>io @ [ioA] \<in> LS (from_FSM A (t_target t')) (initial (from_FSM A (t_target t')))\<close> \<open>t' \<in> transitions A\<close>]
          using \<open>t_input t' = x\<close> \<open>t_source t' = initial A\<close> \<open>t_output t' = t_output tM\<close>
          by simp

        moreover have "(?ioM # io) @ [ioM] \<in> L M"
          using language_state_prepend_transition[OF \<open>io @ [ioM] \<in> L (from_FSM M (t_target tM))\<close> \<open>tM \<in> transitions M\<close>]
          using \<open>t_input tM = x\<close> \<open>t_source tM = initial M\<close>
          by simp

        moreover have "((?ioM # io) @ [ioM] \<notin> L A \<or> io_targets A ((?ioM # io) @ [ioM]) (initial A) \<inter> FS \<noteq> {})"
        proof -
          consider (f1) "io @ [ioM] \<notin> L (from_FSM A (t_target t'))" |
                   (f2) "io_targets (from_FSM A (t_target t')) (io @ [ioM]) (initial (from_FSM A (t_target t'))) \<inter> FS \<noteq> {}"
            using \<open>(io @ [ioM] \<notin> LS (from_FSM A (t_target t')) (initial (from_FSM A (t_target t'))) \<or> io_targets (from_FSM A (t_target t')) (io @ [ioM]) (initial (from_FSM A (t_target t'))) \<inter> FS \<noteq> {})\<close>
            by blast
          then show ?thesis proof cases
            case f1

            have "p_io [t'] = [(x, t_output tM)]"
              using \<open>t_input t' = x\<close> \<open>t_output t' = t_output tM\<close>
              by auto
            moreover have "target (initial A) [t'] = t_target t'"
              using \<open>t_source t' = initial A\<close> by auto
            ultimately have "t_target t' \<in> io_targets A [?ioM] (initial A)"
              unfolding io_targets.simps
              using single_transition_path[OF \<open>t' \<in> transitions A\<close>]
              by (metis (mono_tags, lifting) \<open>t_source t' = initial A\<close> mem_Collect_eq)

             
            
            show ?thesis 
              using observable_io_targets_language[of "[(x, t_output tM)]" "io@[ioM]" A "initial A" "t_target t'", OF _ \<open>observable A\<close> \<open>t_target t' \<in> io_targets A [?ioM] (initial A)\<close>]
                    f1
              by (metis \<open>observable A\<close> \<open>t' \<in> FSM.transitions A\<close> \<open>t_input t' = x\<close> \<open>t_output t' = t_output tM\<close> \<open>t_source t' = FSM.initial A\<close> append_Cons fst_conv observable_language_next snd_conv)

          next
            case f2

            
            have "io_targets A (p_io [t'] @ io @ [ioM]) (t_source t') = io_targets A ([?ioM] @ io @ [ioM]) (t_source t')"
              using \<open>t_input t' = x\<close> \<open>t_output t' = t_output tM\<close> by auto 
            moreover have "io_targets A (io @ [ioM]) (t_target t') = io_targets (from_FSM A (t_target t')) (io @ [ioM]) (initial (from_FSM A (t_target t')))"
              unfolding io_targets.simps
              using from_FSM_path_initial[OF fsm_transition_target[OF \<open>t' \<in> transitions A\<close>]] by auto
            ultimately have "io_targets A ([?ioM] @ io @ [ioM]) (t_source t') = io_targets (from_FSM A (t_target t')) (io @ [ioM]) (initial (from_FSM A (t_target t')))"
              using observable_io_targets_next[OF \<open>observable A\<close> \<open>t' \<in> transitions A\<close>, of "io @ [ioM]"] by auto

            then show ?thesis
              using f2 \<open>t_source t' = initial A\<close> by auto
          qed
        qed       

        ultimately show ?thesis 
          using \<open>fst ioA = fst ioM\<close> by blast
      qed
    qed
  qed
qed


lemma pass_ATC_io_fail :
  assumes "\<not>pass_ATC M A FS"
  and     "is_ATC A"
  and     "observable M"
  and     "(inputs A) \<subseteq> (inputs M)"
shows "initial A \<in> FS \<or> (\<exists> io ioA ioM . io@[ioA] \<in> L A
                          \<and> io@[ioM] \<in> L M
                          \<and> fst ioA = fst ioM
                          \<and> (io@[ioM] \<notin> L A \<or> io_targets A (io@[ioM]) (initial A) \<inter> FS \<noteq> {}))"
  using pass_ATC'_io_fail[OF _ assms(2-4)] using assms(1) by auto


lemma pass_ATC_fail :
  assumes "is_ATC A"
  and     "observable M"
  and     "(inputs A) \<subseteq> (inputs M)"
  and     "io@[(x,y)] \<in> L A"
  and     "io@[(x,y')] \<in> L M" 
  and     "io@[(x,y')] \<notin> L A"
shows "\<not> pass_ATC M A FS"
  using assms(6) pass_ATC_io_explicit_io_tuple(1)[OF _ assms(1,2,3,4,5)]
  by blast


lemma pass_ATC_reduction :
  assumes "L M2 \<subseteq> L M1"
  and     "is_ATC A"
  and     "observable M1"
  and     "observable M2"
  and     "(inputs A) \<subseteq> (inputs M1)"
  and     "(inputs M2) = (inputs M1)"
  and     "pass_ATC M1 A FS"
shows "pass_ATC M2 A FS"
proof (rule ccontr)
  assume "\<not> pass_ATC M2 A FS"
  have "(inputs A) \<subseteq> (inputs M2)"
    using assms(5,6) by blast
  
  have "initial A \<notin> FS"
    using \<open>pass_ATC M1 A FS\<close> by (cases "size A"; auto)  
  then show "False"
    using pass_ATC_io_fail[OF \<open>\<not> pass_ATC M2 A FS\<close> assms(2,4) \<open>(inputs A) \<subseteq> (inputs M2)\<close>]
    using assms(1) assms(2) assms(3) assms(5) assms(7) pass_ATC_io_fail_fixed_io by blast
qed


lemma pass_ATC_fail_no_reduction :
  assumes "is_ATC A"
  and     "observable T" 
  and     "observable M"
  and     "(inputs A) \<subseteq> (inputs M)"
  and     "(inputs T) = (inputs M)"
  and     "pass_ATC M A FS"
  and     "\<not>pass_ATC T A FS"
shows   "\<not> (L T \<subseteq> L M)" 
  using pass_ATC_reduction[OF _ assms(1,3,2,4,5,6)] assms(7) by blast



subsection \<open>State Separators as Adaptive Test Cases\<close>

fun pass_separator_ATC :: "('a,'b,'c) fsm \<Rightarrow> ('d,'b,'c) fsm \<Rightarrow> 'a \<Rightarrow> 'd \<Rightarrow> bool" where
  "pass_separator_ATC M S q1 t2 = pass_ATC (from_FSM M q1) S {t2}"


lemma separator_is_ATC :
  assumes "is_separator M q1 q2 A t1 t2"
  and     "observable M"
  and     "q1 \<in> states M"
  shows "is_ATC A"
unfolding is_ATC_def 
  using is_separator_simps(1,2,3)[OF assms(1)] by blast


lemma pass_separator_ATC_from_separator_left :
  assumes "observable M"
  and     "q1 \<in> states M"
  and     "q2 \<in> states M"
  and     "is_separator M q1 q2 A t1 t2" 
shows "pass_separator_ATC M A q1 t2" 
proof (rule ccontr)
  assume "\<not> pass_separator_ATC M A q1 t2"

  then have "\<not> pass_ATC (from_FSM M q1) A {t2}"
    by auto

  have "is_ATC A"
    using separator_is_ATC[OF assms(4,1,2)] by assumption

  have "initial A \<notin> {t2}"
    using separator_initial(2)[OF assms(4)] by blast
  then obtain io ioA ioM where
    "io @ [ioA] \<in> L A"
    "io @ [ioM] \<in> LS M q1"
    "fst ioA = fst ioM"
    "io @ [ioM] \<notin> L A \<or> io_targets A (io @ [ioM]) (initial A) \<inter> {t2} \<noteq> {}"

    using pass_ATC_io_fail[OF \<open>\<not> pass_ATC (from_FSM M q1) A {t2}\<close> \<open>is_ATC A\<close> from_FSM_observable[OF \<open>observable M\<close>] ] 
    using is_separator_simps(16)[OF assms(4)]
    using from_FSM_language[OF \<open>q1 \<in> states M\<close>]
    unfolding from_FSM_simps[OF \<open>q1 \<in> states M\<close>] by blast
  then obtain x ya ym where
    "io @ [(x,ya)] \<in> L A"
    "io @ [(x,ym)] \<in> LS M q1"
    "io @ [(x,ym)] \<notin> L A \<or> io_targets A (io @ [(x,ym)]) (initial A) \<inter> {t2} \<noteq> {}"
    by (metis fst_eqD old.prod.exhaust)

  have "io @ [(x,ym)] \<in> L A"
    using is_separator_simps(9)[OF assms(4) \<open>io @ [(x,ym)] \<in> LS M q1\<close> \<open>io @ [(x,ya)] \<in> L A\<close>] by assumption

  have "t1 \<noteq> t2" using is_separator_simps(15)[OF assms(4)] by assumption
  
  consider (a) "io @ [(x, ym)] \<in> LS M q1 - LS M q2" |
           (b) "io @ [(x, ym)] \<in> LS M q1 \<inter> LS M q2"
    using \<open>io @ [(x,ym)] \<in> LS M q1\<close> by blast 
  then have "io_targets A (io @ [(x,ym)]) (initial A) \<inter> {t2} = {}"
    
  proof (cases)
    case a
    show ?thesis using separator_language(1)[OF assms(4) \<open>io @ [(x,ym)] \<in> L A\<close> a] \<open>t1 \<noteq> t2\<close> by auto      
  next
    case b
    show ?thesis using separator_language(3)[OF assms(4) \<open>io @ [(x,ym)] \<in> L A\<close> b] \<open>t1 \<noteq> t2\<close> by auto
  qed
  
  then show "False"
    using \<open>io @ [(x,ym)] \<in> L A\<close>
    using \<open>io @ [(x,ym)] \<notin> L A \<or> io_targets A (io @ [(x,ym)]) (initial A) \<inter> {t2} \<noteq> {}\<close> by blast
qed


lemma pass_separator_ATC_from_separator_right :
  assumes "observable M"
  and     "q1 \<in> states M"
  and     "q2 \<in> states M"
  and     "is_separator M q1 q2 A t1 t2" 
shows "pass_separator_ATC M A q2 t1"
  using assms(1-3) is_separator_sym[OF assms(4)] pass_separator_ATC_from_separator_left by metis


lemma pass_separator_ATC_path_left :
  assumes "pass_separator_ATC S A s1 t2"
  and     "observable S" 
  and     "observable M"
  and     "s1 \<in> states S"
  and     "q1 \<in> states M"
  and     "q2 \<in> states M"
  and     "is_separator M q1 q2 A t1 t2"
  and     "(inputs S) = (inputs M)"
  and     "q1 \<noteq> q2"
  and     "path A (initial A) pA"
  and     "path S s1 pS"
  and     "p_io pA = p_io pS"
shows "target (initial A) pA \<noteq> t2"
and   "\<exists> pM . path M q1 pM \<and> p_io pM = p_io pA"
proof -

  have "pass_ATC (from_FSM S s1) A {t2}"
    using \<open>pass_separator_ATC S A s1 t2\<close> by auto

  have "is_ATC A"
    using separator_is_ATC[OF assms(7,3,5)] by assumption

  have "observable (from_FSM S s1)"
    using from_FSM_observable[OF assms(2)] by assumption

  have "(inputs A) \<subseteq> (inputs (from_FSM S s1))"
    using is_separator_simps(16)[OF assms(7)] \<open>(inputs S) = (inputs M)\<close>
    unfolding from_FSM_simps[OF \<open>s1 \<in> states S\<close>] by blast

  have "target (initial A) pA \<noteq> t2 \<and> (\<exists> pM . path M q1 pM \<and> p_io pM = p_io pA)"
  proof (cases pA rule: rev_cases)
    case Nil
    then have "target (initial A) pA \<noteq> t2"
      using separator_initial(2)[OF assms(7)] by auto
    moreover have "(\<exists> pM . path M q1 pM \<and> p_io pM = p_io pA)"
      unfolding Nil using \<open>q1 \<in> states M\<close> by auto
    ultimately show ?thesis by auto
  next
    case (snoc ys y)
    then have "p_io pA = (p_io ys)@[(t_input y,t_output y)]"
      by auto
    then have *: "(p_io ys)@[(t_input y,t_output y)] \<in> L A"
      using language_state_containment[OF \<open>path A (initial A) pA\<close>] by blast
    then have "p_io pS = (p_io ys)@[(t_input y,t_output y)]"
      using \<open>p_io pA = (p_io ys)@[(t_input y,t_output y)]\<close> \<open>p_io pA = p_io pS\<close> by auto
    then have **: "(p_io ys)@[(t_input y,t_output y)] \<in> L (from_FSM S s1)"
      using language_state_containment[OF \<open>path S s1 pS\<close>] 
      unfolding from_FSM_language[OF \<open>s1 \<in> states S\<close>] by blast
    
    have "io_targets A ((p_io ys)@[(t_input y,t_output y)]) (initial A) \<inter> {t2} = {}"
      using pass_ATC_io(2)[OF \<open>pass_ATC (from_FSM S s1) A {t2}\<close> \<open>is_ATC A\<close> \<open>observable (from_FSM S s1)\<close> \<open>(inputs A) \<subseteq> (inputs (from_FSM S s1))\<close> * **]
      unfolding fst_conv by auto
    then have "target (initial A) pA \<noteq> t2"
      using \<open>p_io pA = (p_io ys)@[(t_input y,t_output y)]\<close> \<open>path A (initial A) pA\<close>
      unfolding io_targets.simps
      by blast 

    have "p_io ys @ [(t_input y, t_output y)] \<in> LS M q1"
      using separator_language(2,4)[OF assms(7) \<open>(p_io ys)@[(t_input y,t_output y)] \<in> L A\<close>]
      using \<open>io_targets A ((p_io ys)@[(t_input y,t_output y)]) (initial A) \<inter> {t2} = {}\<close> by blast
    then have "\<exists> pM . path M q1 pM \<and> p_io pM = p_io pA"
      using \<open>p_io pA = (p_io ys)@[(t_input y,t_output y)]\<close> by auto

    then show ?thesis using \<open>target (initial A) pA \<noteq> t2\<close> by auto
  qed

  then show "target (initial A) pA \<noteq> t2" and   "\<exists> pM . path M q1 pM \<and> p_io pM = p_io pA"
    by blast+
qed


lemma pass_separator_ATC_path_right :
  assumes "pass_separator_ATC S A s2 t1"
  and     "observable S" 
  and     "observable M"
  and     "s2 \<in> states S"
  and     "q1 \<in> states M"
  and     "q2 \<in> states M"
  and     "is_separator M q1 q2 A t1 t2"
  and     "(inputs S) = (inputs M)"
  and     "q1 \<noteq> q2"
  and     "path A (initial A) pA"
  and     "path S s2 pS"
  and     "p_io pA = p_io pS"
shows "target (initial A) pA \<noteq> t1"
and   "\<exists> pM . path M q2 pM \<and> p_io pM = p_io pA" 
  using pass_separator_ATC_path_left[OF assms(1-4,6,5) is_separator_sym[OF assms(7)] assms(8) _ assms(10-12)] assms(9) by blast+


lemma pass_separator_ATC_fail_no_reduction :
  assumes "observable S" 
  and     "observable M"
  and     "s1 \<in> states S"
  and     "q1 \<in> states M"
  and     "q2 \<in> states M"
  and     "is_separator M q1 q2 A t1 t2"
  and     "(inputs S) = (inputs M)"
  and     "\<not>pass_separator_ATC S A s1 t2"
shows   "\<not> (LS S s1 \<subseteq> LS M q1)" 
proof 
  assume "LS S s1 \<subseteq> LS M q1"

  have "is_ATC A"
    using separator_is_ATC[OF assms(6,2,4)] by assumption

  have *: "(inputs A) \<subseteq> (inputs (from_FSM M q1))"
    using is_separator_simps(16)[OF assms(6)]
    unfolding is_submachine.simps canonical_separator_simps from_FSM_simps[OF \<open>q1 \<in> states M\<close>] by auto

  have "pass_ATC (from_FSM M q1) A {t2}"
    using pass_separator_ATC_from_separator_left[OF assms(2,4,5,6)] by auto

  have "\<not> pass_ATC (from_FSM S s1) A {t2}"
    using \<open>\<not>pass_separator_ATC S A s1 t2\<close> by auto

  moreover have "pass_ATC (from_FSM S s1) A {t2}"
    using pass_ATC_reduction[OF _ \<open>is_ATC A\<close> from_FSM_observable[OF \<open>observable M\<close>] from_FSM_observable[OF \<open>observable S\<close>] *]
    using \<open>LS S s1 \<subseteq> LS M q1\<close> \<open>pass_ATC (from_FSM M q1) A {t2}\<close>  
    unfolding from_FSM_language[OF assms(3)] from_FSM_language[OF assms(4)]
    using \<open>L (FSM.from_FSM S s1) = LS S s1\<close> assms(3) assms(4) assms(7) by auto
  ultimately show "False" by simp
qed


lemma pass_separator_ATC_pass_left :
  assumes "observable S" 
  and     "observable M"
  and     "s1 \<in> states S"
  and     "q1 \<in> states M"
  and     "q2 \<in> states M"
  and     "is_separator M q1 q2 A t1 t2"
  and     "(inputs S) = (inputs M)"
  and     "path A (initial A) p"
  and     "p_io p \<in> LS S s1"
  and     "q1 \<noteq> q2"
  and     "pass_separator_ATC S A s1 t2"
shows "target (initial A) p \<noteq> t2"
and   "target (initial A) p = t1 \<or> (target (initial A) p \<noteq> t1 \<and> target (initial A) p \<noteq> t2)" (* useless? *)
proof -

  from \<open>p_io p \<in> LS S s1\<close> obtain pS where "path S s1 pS" and "p_io p = p_io pS"
    by auto

  then show "target (initial A) p \<noteq> t2" 
    using pass_separator_ATC_path_left[OF assms(11,1-7,10,8)] by simp

  obtain pM where "path M q1 pM" and "p_io pM = p_io p"
    using pass_separator_ATC_path_left[OF assms(11,1-7,10,8) \<open>path S s1 pS\<close> \<open>p_io p = p_io pS\<close>]  by blast
  then have "p_io p \<in> LS M q1"
    unfolding LS.simps by force

  then show "target (initial A) p = t1 \<or> (target (initial A) p \<noteq> t1 \<and> target (initial A) p \<noteq> t2)"
    using separator_path_targets(1,3,4)[OF assms(6,8)] by blast
qed


lemma pass_separator_ATC_pass_right :
  assumes "observable S" 
  and     "observable M"
  and     "s2 \<in> states S"
  and     "q1 \<in> states M"
  and     "q2 \<in> states M"
  and     "is_separator M q1 q2 A t1 t2"
  and     "(inputs S) = (inputs M)"
  and     "path A (initial A) p"
  and     "p_io p \<in> LS S s2"
  and     "q1 \<noteq> q2"
  and     "pass_separator_ATC S A s2 t1"
shows "target (initial A) p \<noteq> t1"
and   "target (initial A) p = t2 \<or> (target (initial A) p \<noteq> t2 \<and> target (initial A) p \<noteq> t2)" 
  using pass_separator_ATC_pass_left[OF assms(1,2,3,5,4) is_separator_sym[OF assms(6)] assms(7-9) _ assms(11)] assms(10) by blast+


lemma pass_separator_ATC_completely_specified_left :
  assumes "observable S" 
  and     "observable M"
  and     "s1 \<in> states S"
  and     "q1 \<in> states M"
  and     "q2 \<in> states M"
  and     "is_separator M q1 q2 A t1 t2"
  and     "(inputs S) = (inputs M)"
  and     "q1 \<noteq> q2"
  and     "pass_separator_ATC S A s1 t2"
  and     "completely_specified S"
shows "\<exists> p . path A (initial A) p \<and> p_io p \<in> LS S s1 \<and> target (initial A) p = t1"
and   "\<not> (\<exists> p . path A (initial A) p \<and> p_io p \<in> LS S s1 \<and> target (initial A) p = t2)"
proof -
  have p1: "pass_ATC (from_FSM S s1) A {t2}"
    using assms(9) by auto

  have p2: "is_ATC A"
    using separator_is_ATC[OF assms(6,2,4)] by assumption

  have p3: "observable (from_FSM S s1)"
    using from_FSM_observable[OF assms(1)] by assumption

  have p4: "(inputs A) \<subseteq> (inputs (from_FSM S s1))"
    using is_separator_simps(16)[OF assms(6)] 
    unfolding from_FSM_simps[OF \<open>s1 \<in> states S\<close>] is_submachine.simps canonical_separator_simps assms(7) by auto

  have "t1 \<noteq> t2" and "observable A"
    using is_separator_simps(15,3)[OF assms(6)] by linarith+


  have path_ext: "\<And> p . path A (initial A) p \<Longrightarrow> p_io p \<in> LS S s1 \<Longrightarrow> (target (initial A) p \<noteq> t2) \<and> (target (initial A) p = t1 \<or> (\<exists> t . path A (initial A) (p@[t]) \<and> p_io (p@[t]) \<in> LS S s1))"
  proof -
    fix p assume "path A (initial A) p" and "p_io p \<in> LS S s1"

    consider (a) "target (initial A) p = t1" |
             (b) "target (initial A) p \<noteq> t1 \<and> target (initial A) p \<noteq> t2"
      using pass_separator_ATC_pass_left(2)[OF assms(1,2,3,4,5,6,7) \<open>path A (initial A) p\<close> \<open>p_io p \<in> LS S s1\<close> assms(8,9)] by blast
    then have "target (initial A) p = t1 \<or> (\<exists> t . path A (initial A) (p@[t]) \<and> p_io (p@[t]) \<in> LS S s1)"
    proof cases
      case a
      then show ?thesis by blast
    next
      case b

      let ?t3 = "target (initial A) p"
      have "?t3 \<noteq> t1" and "?t3 \<noteq> t2"
        using b by auto
      moreover have "?t3 \<in> reachable_states A"
        using \<open>path A (initial A) p\<close> reachable_states_intro by blast
      ultimately have "\<not> deadlock_state A ?t3"
        using is_separator_simps(8)[OF assms(6)] by blast
      then obtain tt where "tt \<in> transitions A" and "t_source tt = ?t3"
        by auto
      
      then have "path A (initial A) (p@[tt])" 
        using \<open>path A (initial A) p\<close> using path_append_transition by metis

      moreover have "p_io (p@[tt]) = (p_io p)@[(t_input tt, t_output tt)]"
        by auto

      ultimately have "(p_io p)@[(t_input tt,t_output tt)] \<in> L A"
        using language_state_containment[of A "initial A" "p@[tt]"] by metis

      let ?x = "t_input tt"
      have "?x \<in> (inputs S)"
        using \<open>tt \<in> transitions A\<close> is_separator_simps(16)[OF assms(6)] assms(7) by auto
      then obtain y where "(p_io p)@[(?x,y)] \<in> LS S s1"
        using completely_specified_language_extension[OF \<open>completely_specified S\<close> \<open>s1 \<in> states S\<close> \<open>p_io p \<in> LS S s1\<close> ] by auto

      then have "p_io p @ [(?x, y)] \<in> LS A (initial A)"
        using pass_ATC_io_explicit_io_tuple(1)[OF p1 p2 p3 p4 \<open>(p_io p)@[(t_input tt,t_output tt)] \<in> L A\<close>]
        unfolding from_FSM_language[OF \<open>s1 \<in> states S\<close>] by auto

      then obtain tt' where "path A (initial A) (p@[tt'])" and "t_input tt' = ?x" and "t_output tt' = y"
        using language_path_append_transition_observable[OF _ \<open>path A (initial A) p\<close> \<open>observable A\<close>] by blast

      then have "p_io (p @ [tt']) \<in> LS S s1"
        using \<open>(p_io p)@[(?x,y)] \<in> LS S s1\<close> by auto
      then show ?thesis
        using \<open>path A (initial A) (p@[tt'])\<close> by meson 
    qed

    moreover have "target (initial A) p \<noteq> t2"
      using pass_separator_ATC_pass_left(1)[OF assms(1,2,3,4,5,6,7) \<open>path A (initial A) p\<close> \<open>p_io p \<in> LS S s1\<close> assms(8,9)] by assumption

    ultimately show "(target (initial A) p \<noteq> t2) \<and> (target (initial A) p = t1 \<or> (\<exists> t . path A (initial A) (p@[t]) \<and> p_io (p@[t]) \<in> LS S s1))"
      by simp
  qed


  (* largest path that satisfies (path A (initial A) p) and (p_io p \<in> LS T t1) cannot be extended further and must thus target (Inr q1)  *)

  have "acyclic A"
    using \<open>is_ATC A\<close> is_ATC_def by auto
  then have "finite {p . path A (initial A) p}"
    using acyclic_paths_finite[of A "initial A"] unfolding acyclic.simps
    by (metis (no_types, lifting) Collect_cong) 
  then have "finite {p . path A (initial A) p \<and> p_io p \<in> LS S s1}"
    by auto

  have "[] \<in> {p . path A (initial A) p \<and> p_io p \<in> LS S s1}"
    using \<open>s1 \<in> states S\<close> by auto
  then have "{p . path A (initial A) p \<and> p_io p \<in> LS S s1} \<noteq> {}"
    by blast

  have scheme: "\<And> S . finite S \<Longrightarrow> S \<noteq> {} \<Longrightarrow> \<exists> x \<in> S . \<forall> y \<in> S . length y \<le> length x"
    by (meson leI max_length_elem)
    
  obtain p where "p \<in> {p . path A (initial A) p \<and> p_io p \<in> LS S s1}" and "\<And> p' . p' \<in> {p . path A (initial A) p \<and> p_io p \<in> LS S s1} \<Longrightarrow> length p' \<le> length p"
    using scheme[OF \<open>finite {p . path A (initial A) p \<and> p_io p \<in> LS S s1}\<close> \<open>{p . path A (initial A) p \<and> p_io p \<in> LS S s1} \<noteq> {}\<close>] 
    by blast
  then have "path A (initial A) p" and "p_io p \<in> LS S s1" and "\<And> p' . path A (initial A) p' \<Longrightarrow> p_io p' \<in> LS S s1 \<Longrightarrow> length p' \<le> length p"
    by blast+

  have "target (initial A) p = t1"
    using path_ext[OF \<open>path A (initial A) p\<close> \<open>p_io p \<in> LS S s1\<close>] \<open>\<And> p' . path A (initial A) p' \<Longrightarrow> p_io p' \<in> LS S s1 \<Longrightarrow> length p' \<le> length p\<close>
    by (metis (no_types, lifting) Suc_n_not_le_n length_append_singleton) 

  then show "\<exists>p. path A (initial A) p \<and> p_io p \<in> LS S s1 \<and> target (initial A) p = t1"
    using \<open>path A (initial A) p\<close> \<open>p_io p \<in> LS S s1\<close> by blast

  show "\<nexists>p. path A (initial A) p \<and> p_io p \<in> LS S s1 \<and> target (initial A) p = t2"
    using path_ext by blast
qed


lemma pass_separator_ATC_completely_specified_right :
  assumes "observable S" 
  and     "observable M"
  and     "s2 \<in> states S"
  and     "q1 \<in> states M"
  and     "q2 \<in> states M"
  and     "is_separator M q1 q2 A t1 t2"
  and     "(inputs S) = (inputs M)"
  and     "q1 \<noteq> q2"
  and     "pass_separator_ATC S A s2 t1"
  and     "completely_specified S"
shows "\<exists> p . path A (initial A) p \<and> p_io p \<in> LS S s2 \<and> target (initial A) p = t2"
and   "\<not> (\<exists> p . path A (initial A) p \<and> p_io p \<in> LS S s2 \<and> target (initial A) p = t1)"
  using pass_separator_ATC_completely_specified_left[OF assms(1,2,3,5,4) is_separator_sym[OF assms(6)] assms(7) _ assms(9,10)] assms(8) by blast+


lemma pass_separator_ATC_reduction_distinction : 
  assumes "observable M"
  and     "observable S"
  and     "(inputs S) = (inputs M)"
  and     "pass_separator_ATC S A s1 t2"
  and     "pass_separator_ATC S A s2 t1"
  and     "q1 \<in> states M"
  and     "q2 \<in> states M"
  and     "q1 \<noteq> q2"
  and     "s1 \<in> states S"
  and     "s2 \<in> states S"
  and     "is_separator M q1 q2 A t1 t2"  
  and     "completely_specified S"
shows "s1 \<noteq> s2"
proof -

  (* As s1 passes A against t2, t1 must be reached during application, while
     at the same time t2 is never reached *)

  have "\<exists>p. path A (initial A) p \<and> p_io p \<in> LS S s1 \<and> target (initial A) p = t1"
    using pass_separator_ATC_completely_specified_left[OF assms(2,1,9,6,7,11,3,8,4,12)] by blast

  (* As s2 passes A against t1, t2 must be reached during application, while
     at the same time t1 is never reached *)
  
  moreover have "\<not> (\<exists>p. path A (initial A) p \<and> p_io p \<in> LS S s2 \<and> target (initial A) p = t1)"
    using pass_separator_ATC_completely_specified_right[OF assms(2,1,10,6,7,11,3,8,5,12)] by blast

  (* Thus it is not possible for (s1 = s2) to hold *)

  ultimately show "s1 \<noteq> s2" by blast
qed


lemma pass_separator_ATC_failure_left : 
  assumes "observable M"
  and     "observable S"
  and     "(inputs S) = (inputs M)"
  and     "is_separator M q1 q2 A t1 t2"
  and     "\<not> pass_separator_ATC S A s1 t2"
  and     "q1 \<in> states M"
  and     "q2 \<in> states M"
  and     "q1 \<noteq> q2"
  and     "s1 \<in> states S"  
shows "LS S s1 - LS M q1 \<noteq> {}"
proof -
  
  have p1: "is_ATC A"
    using separator_is_ATC[OF assms(4,1,6)] by assumption

  have p2: "observable (from_FSM S s1)"
    using from_FSM_observable[OF assms(2)] by assumption

  have p3: "observable (from_FSM M q1)"
    using from_FSM_observable[OF assms(1)] by assumption

  have p4: "(inputs A) \<subseteq> (inputs (from_FSM M q1))"
    using is_separator_simps(16)[OF assms(4)] 
    unfolding from_FSM_simps[OF \<open>q1 \<in> states M\<close>] is_submachine.simps canonical_separator_simps assms(3) by auto

  have p5: "(inputs (from_FSM S s1)) = (inputs (from_FSM M q1))"
    using assms(3,6,9) by simp

  have p6: "pass_ATC (from_FSM M q1) A {t2}"
    using pass_separator_ATC_from_separator_left[OF assms(1,6,7,4)] by auto

  have p7: "\<not> pass_ATC (from_FSM S s1) A {t2}"
    using assms(5) by auto

  show ?thesis
    using pass_ATC_fail_no_reduction[OF p1 p2 p3 p4 p5 p6 p7]
    unfolding from_FSM_language[OF \<open>q1 \<in> states M\<close>] from_FSM_language[OF \<open>s1 \<in> states S\<close>] by blast
qed


lemma pass_separator_ATC_failure_right : 
  assumes "observable M"
  and     "observable S"
  and     "(inputs S) = (inputs M)"
  and     "is_separator M q1 q2 A t1 t2"
  and     "\<not> pass_separator_ATC S A s2 t1"
  and     "q1 \<in> states M"
  and     "q2 \<in> states M"
  and     "q1 \<noteq> q2"
  and     "s2 \<in> states S"  
shows "LS S s2 - LS M q2 \<noteq> {}"
  using pass_separator_ATC_failure_left[OF assms(1-3) is_separator_sym[OF assms(4)] assms(5,7,6) _ assms(9)] assms(8) by blast




subsection \<open>ATCs Represented as Sets of IO Sequences\<close>

fun atc_to_io_set :: "('a,'b,'c) fsm \<Rightarrow> ('d,'b,'c) fsm \<Rightarrow> ('b \<times> 'c) list set" where
  "atc_to_io_set M A = L M \<inter> L A"


lemma atc_to_io_set_code :
  assumes "acyclic A"
  shows "atc_to_io_set M A = acyclic_language_intersection M A"
  using acyclic_language_intersection_completeness[OF assms] unfolding atc_to_io_set.simps by blast


lemma pass_io_set_from_pass_separator :
  assumes "is_separator M q1 q2 A t1 t2"
  and     "pass_separator_ATC S A s1 t2"
  and     "observable M"
  and     "observable S"
  and     "q1 \<in> states M"
  and     "s1 \<in> states S"
  and     "(inputs S) = (inputs M)"
shows "pass_io_set (from_FSM S s1) (atc_to_io_set (from_FSM M q1) A)"
proof (rule ccontr) 
  assume "\<not> pass_io_set (from_FSM S s1) (atc_to_io_set (from_FSM M q1) A)"
  then obtain io x y y' where "io@[(x,y)] \<in> (atc_to_io_set (from_FSM M q1) A)" and "io@[(x,y')] \<in> L (from_FSM S s1)" and "io@[(x,y')] \<notin> (atc_to_io_set (from_FSM M q1) A)" 
    unfolding pass_io_set_def by blast

  have "is_ATC A"
    using separator_is_ATC[OF assms(1,3,5)]  by assumption
  then have "acyclic A" 
    unfolding is_ATC_def by auto
  have "observable (from_FSM S s1)"
    using from_FSM_observable[OF \<open>observable S\<close>] by assumption
  have "(inputs A) \<subseteq> (inputs (from_FSM S s1))"
    by (metis (no_types) assms(1) assms(6) assms(7) from_FSM_simps(2) is_separator_simps(16))

  obtain y'' where "io @ [(x, y'')] \<in> LS A (initial A)"
    using \<open>io@[(x,y)] \<in> (atc_to_io_set (from_FSM M q1) A)\<close> unfolding atc_to_io_set.simps by blast

  have "pass_ATC (from_FSM S s1) A {t2}"
    using \<open>pass_separator_ATC S A s1 t2\<close> by auto

  then have "io @ [(x, y')] \<in> L A"
    using pass_ATC_fail[OF \<open>is_ATC A\<close> 
                           \<open>observable (from_FSM S s1)\<close> 
                           \<open>(inputs A) \<subseteq> (inputs (from_FSM S s1))\<close> 
                           \<open>io @ [(x, y'')] \<in> LS A (initial A)\<close>
                           \<open>io@[(x,y')] \<in> L (from_FSM S s1)\<close>,
                        of "{t2}" ]
    by auto

  have "io_targets A (io @ [(x, y')]) (initial A) \<inter> {t2} = {}"  
    using pass_ATC_io(2)[OF \<open>pass_ATC (from_FSM S s1) A {t2}\<close> \<open>is_ATC A\<close> \<open>observable (from_FSM S s1)\<close> \<open>(inputs A) \<subseteq> (inputs (from_FSM S s1))\<close> \<open>io @ [(x, y')] \<in> L A\<close> \<open>io@[(x,y')] \<in> L (from_FSM S s1)\<close>]
    unfolding fst_conv by blast

  then have "io @ [(x, y')] \<in> LS M q1"
    using separator_language(1,3,4)[OF assms(1) \<open>io @ [(x, y')] \<in> L A\<close>] 
    by (metis UnE Un_Diff_cancel \<open>io @ [(x, y')] \<in> LS A (initial A)\<close> assms(1) disjoint_insert(2) is_separator_sym separator_language(1) singletonI)
  then show "False"
    using \<open>io @ [(x, y')] \<in> L A\<close> \<open>io@[(x,y')] \<notin> (atc_to_io_set (from_FSM M q1) A)\<close> 
    unfolding atc_to_io_set.simps from_FSM_language[OF \<open>q1 \<in> states M\<close>]
    by blast
qed


lemma separator_language_last_left :
  assumes "is_separator M q1 q2 A t1 t2"
  and     "completely_specified M"
  and     "q1 \<in> states M"
  and     "io @ [(x, y)] \<in> L A"
obtains y'' where "io@[(x,y'')] \<in> L A \<inter> LS M q1"
proof -
  obtain p t where "path A (initial A) (p@[t])" and "p_io (p@[t]) = io@[(x,y)]"
    using language_initial_path_append_transition[OF \<open>io @ [(x, y)] \<in> L A\<close>] by blast
  then have "\<not> deadlock_state A (target (initial A) p)"
    unfolding deadlock_state.simps by fastforce
  have "path A (initial A) p"
    using \<open>path A (initial A) (p@[t])\<close> by auto

  have "p_io p \<in> LS M q1"
    using separator_path_targets(1,2,4)[OF assms(1) \<open>path A (initial A) p\<close>]
    using is_separator_simps(4,5)[OF assms(1)] 
    using \<open>\<not> deadlock_state A (target (initial A) p)\<close> by fastforce
  then have "io \<in> LS M q1"
    using \<open>p_io (p@[t]) = io@[(x,y)]\<close> by auto

  have "x \<in> (inputs A)"
    using \<open>io @ [(x, y)] \<in> L A\<close> language_io(1) 
    by (metis in_set_conv_decomp)
  then have "x \<in> (inputs M)"
    using is_separator_simps(16)[OF assms(1)] by blast

  then obtain y'' where "io@[(x,y'')] \<in> LS M q1"
    using completely_specified_language_extension[OF \<open>completely_specified M\<close> \<open>q1 \<in> states M\<close> \<open>io \<in> LS M q1\<close>] by blast
  then have "io@[(x,y'')] \<in> L A \<inter> LS M q1"
    using is_separator_simps(9)[OF assms(1) _ \<open>io @ [(x, y)] \<in> L A\<close>] by blast
  then show ?thesis 
    using that by blast
qed


lemma separator_language_last_right :
  assumes "is_separator M q1 q2 A t1 t2"
  and     "completely_specified M"
  and     "q2 \<in> states M"
  and     "io @ [(x, y)] \<in> L A"
obtains y'' where "io@[(x,y'')] \<in> L A \<inter> LS M q2"
  using separator_language_last_left[OF is_separator_sym[OF assms(1)] assms(2,3,4)] by blast


lemma pass_separator_from_pass_io_set :
  assumes "is_separator M q1 q2 A t1 t2"
  and     "pass_io_set (from_FSM S s1) (atc_to_io_set (from_FSM M q1) A)"
  and     "observable M"
  and     "observable S"
  and     "q1 \<in> states M"
  and     "s1 \<in> states S"
  and     "(inputs S) = (inputs M)"
  and     "completely_specified M"
shows "pass_separator_ATC S A s1 t2"
proof (rule ccontr)
  assume "\<not> pass_separator_ATC S A s1 t2"
  then have "\<not> pass_ATC (from_FSM S s1) A {t2}" by auto

  have "is_ATC A"
    using separator_is_ATC[OF assms(1,3,5)]  by assumption
  then have "acyclic A" 
    unfolding is_ATC_def by auto
  have "observable (from_FSM S s1)"
    using from_FSM_observable[OF \<open>observable S\<close>] by assumption
  have "(inputs A) \<subseteq> (inputs (from_FSM S s1))"
    using assms(1) assms(6) assms(7) is_separator_simps(16) by fastforce

  obtain io x y y' where "io @ [(x,y)] \<in> L A"
                         "io @ [(x,y')] \<in> L (from_FSM S s1)"
                         "(io @ [(x,y')] \<notin> L A \<or> io_targets A (io @ [(x,y')]) (initial A) \<inter> {t2} \<noteq> {})"
    using pass_ATC_io_fail[OF \<open>\<not> pass_ATC (from_FSM S s1) A {t2}\<close> \<open>is_ATC A\<close> \<open>observable (from_FSM S s1)\<close> \<open>(inputs A) \<subseteq> (inputs (from_FSM S s1))\<close>]
    using separator_initial(2)[OF assms(1)]  
    using prod.exhaust fst_conv 
    by (metis empty_iff insert_iff)

  show "False" 
  proof (cases "io_targets A (io @ [(x,y')]) (initial A) \<inter> {t2} \<noteq> {}")
    case True
    then have "io @ [(x,y')] \<in> L A"
      unfolding io_targets.simps LS.simps by force
    
    have "io @ [(x,y')] \<in> LS M q2 - LS M q1"
    proof -
      have "t2 \<noteq> t1"
        by (metis (full_types) \<open>is_separator M q1 q2 A t1 t2\<close> is_separator_simps(15))
      then show ?thesis
        using True separator_language[OF assms(1) \<open>io @ [(x,y')] \<in> L A\<close>] 
        by blast
    qed
    then have "io @ [(x,y')] \<notin> LS M q1" by blast

    obtain y'' where "io @ [(x, y'')] \<in> LS M q1 \<inter> L A"
      using separator_language_last_left[OF assms(1,8,5) \<open>io @ [(x,y)] \<in> L A\<close>] by blast
    then have "io @ [(x, y')] \<in> LS M q1 \<inter> LS A (initial A)"
      using \<open>pass_io_set (from_FSM S s1) (atc_to_io_set (from_FSM M q1) A)\<close>
      using \<open>io @ [(x,y')] \<in> L (from_FSM S s1)\<close> 
      unfolding pass_io_set_def atc_to_io_set.simps from_FSM_language[OF \<open>q1 \<in> states M\<close>] by blast

    then show "False" 
      using \<open>io @ [(x,y')] \<notin> LS M q1\<close> by blast
  
  next
    case False  
    then have "io @ [(x,y')] \<notin> L A"
      using \<open>(io @ [(x,y')] \<notin> L A \<or> io_targets A (io @ [(x,y')]) (initial A) \<inter> {t2} \<noteq> {})\<close>
      by blast

    obtain y'' where "io @ [(x, y'')] \<in> LS M q1 \<inter> L A"
      using separator_language_last_left[OF assms(1,8,5) \<open>io @ [(x,y)] \<in> L A\<close>] by blast
    then have "io @ [(x, y')] \<in> L A"
      using \<open>pass_io_set (from_FSM S s1) (atc_to_io_set (from_FSM M q1) A)\<close>
      using \<open>io @ [(x,y')] \<in> L (from_FSM S s1)\<close> 
      unfolding pass_io_set_def atc_to_io_set.simps from_FSM_language[OF \<open>q1 \<in> states M\<close>] by blast

    then show "False"
      using \<open>io @ [(x,y')] \<notin> L A\<close> by blast
  qed
qed


lemma pass_separator_pass_io_set_iff:
  assumes "is_separator M q1 q2 A t1 t2"
  and     "observable M"
  and     "observable S"
  and     "q1 \<in> states M"
  and     "s1 \<in> states S"
  and     "(inputs S) = (inputs M)"
  and     "completely_specified M"
shows "pass_separator_ATC S A s1 t2 \<longleftrightarrow> pass_io_set (from_FSM S s1) (atc_to_io_set (from_FSM M q1) A)"
  using pass_separator_from_pass_io_set[OF assms(1) _ assms(2-7)]
        pass_io_set_from_pass_separator[OF assms(1) _ assms(2-6)] by blast


lemma pass_separator_pass_io_set_maximal_iff:
  assumes "is_separator M q1 q2 A t1 t2"
  and     "observable M"
  and     "observable S"
  and     "q1 \<in> states M"
  and     "s1 \<in> states S"
  and     "(inputs S) = (inputs M)"
  and     "completely_specified M"
shows "pass_separator_ATC S A s1 t2 \<longleftrightarrow> pass_io_set_maximal (from_FSM S s1) (remove_proper_prefixes (atc_to_io_set (from_FSM M q1) A))"
proof -

  have "is_ATC A"
    using separator_is_ATC[OF assms(1,2,4)]  by assumption
  then have "acyclic A" 
    unfolding is_ATC_def by auto
  then have "finite (L A)"
    unfolding acyclic_alt_def by assumption
  then have *: "finite (atc_to_io_set (from_FSM M q1) A)"
    unfolding atc_to_io_set.simps by blast

  have **: "\<And>io' io''. io' @ io'' \<in> atc_to_io_set (from_FSM M q1) A \<Longrightarrow> io' \<in> atc_to_io_set (from_FSM M q1) A"
    unfolding atc_to_io_set.simps
    using language_prefix[of _ _ "from_FSM M q1" "initial (from_FSM M q1)"]
    using language_prefix[of _ _ "A" "initial A"] by blast

  show ?thesis  
    unfolding pass_separator_pass_io_set_iff[OF assms] remove_proper_prefixes_def
    using pass_io_set_maximal_from_pass_io_set[of "(atc_to_io_set (from_FSM M q1) A)" "(from_FSM S s1)", OF * ] ** by blast
qed
  


end