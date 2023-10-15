section \<open>Reductions and \<open>\<tau>\<close>-sinks\<close>

text \<open>
  Checking trace inclusion can be reduced to contrasimulation checking,
  as can weak simulation checking to coupled simulation checking.
  The trick is to add a \<open>\<tau>\<close>-sink to the transition system, that is, a state that is reachable
  by \<open>\<tau>\<close>-steps from every other state, and cannot be left.
  An illustration of such an extension is given in Figure~\ref{fig:sink-illustration}.
  Intuitively, the extension means that the model is allowed to just stop progressing at any point.

  We here prove that, on systems with a \<open>\<tau>\<close>-sink, weak similarity equals coupled similarity and 
  weak trace inclusion equals contrasimilarity.
  We also prove that adding a \<open>\<tau>\<close>-sink to a system does not change weak similarity nor weak trace
  inclusion relationships within the system.
  As adding the \<open>\<tau>\<close>-sink only has negligible effect on the system sizes, these facts establish the
  reducibility relationships.
\<close>

text_raw \<open>
  \begin{figure}
    \centering
    \begin{tikzpicture}[scale=1, auto]
  
      \node (p0) [circle, draw=black] at (0,0)                    {};
      \node (p1) [circle, draw=black, below right= 1cm of p0]                {};
      \node (p2) [circle, draw=black, below left= 1.5cm and 2mm of p1]          {};
      \node (p3) [circle, draw=black, above left= 1cm of p2]           {};
      %\node (p5) [circle, draw=black, below left= 5mm and 8mm of p0]           {};
      
      \node (bot) [circle, draw= red, right= 2cm of p1] {\Large$\color{red}{\bot}$};
      
      \path[->]
        (p0)         edge[swap, bend left = 15]         node    {}         (p1)
        (p0)         edge[swap, bend right = 15]         node    {}         (p3)
        (p1)         edge[bend left = 15]               node    {}         (p2)
        (p2)         edge[loop below]   node    {}         (p2)
        (p3)         edge[bend left = 15]    node    {}         (p1)
        (p3)         edge[bend right = 15]   node    {}         (p2)
        (p1)         edge[bend left = 15]   node    {}         (p3)
        ;
       
      %Contrasim_ undirected
      \path[->, draw=red,  every node/.style={color=red}]
        (p0)         edge[bend left = 25]         node    {$\tau$}       (bot)
        (p1)         edge[bend left = 10]         node    {$\tau$}    (bot)
        (p2)         edge[swap,bend right = 25]   node    {$\tau$}         (bot)
        (p3)         edge[bend right = 0, out = -35, in=-168]   node    {$\tau$}         (bot)
        (bot)         edge[loop below]   node    {$\tau$}         (bot)
       ;
    ;
    \end{tikzpicture}
    \caption{Example of a $\tau$-sink extension with the original transition system in black and
      the extension in red.}
      \label{fig:sink-illustration}
  \end{figure}
\<close>

theory Tau_Sinks
imports
  Coupled_Simulation
begin

subsection \<open>\<open>\<tau>\<close>-Sink Properties\<close>

context lts_tau
begin

definition tau_sink ::
  \<open>'s \<Rightarrow> bool\<close>
where
  \<open>tau_sink p \<equiv> 
    (\<forall>a p'. p \<longmapsto>a p' \<longrightarrow> a = \<tau> \<and> p = p') \<and>
    (\<forall>p0. p0 \<longmapsto>\<tau> p)\<close>

text \<open>The tau sink is a supremum for the weak transition relation.\<close>

lemma tau_sink_maximal:
  assumes \<open>tau_sink sink\<close>
  shows
    \<open>tau_max sink\<close>
    \<open>(p \<longmapsto>* tau sink)\<close>
  using assms steps_loop step_weak_step_tau tau_tau unfolding tau_sink_def by metis+

lemma sink_has_no_word_transitions: 
  assumes 
    \<open>tau_sink sink\<close>
    \<open>A \<noteq> []\<close>
    \<open>\<forall> a \<in> set(A). a \<noteq> \<tau>\<close>
  shows \<open>\<nexists>s'. sink \<Rightarrow>$A s'\<close>
proof - 
  obtain a where \<open>\<exists>B. A = a#B\<close> using assms(2) list.exhaust_sel by auto
  hence \<open>\<nexists>s' . sink \<Rightarrow>^a s'\<close>
    by (metis assms(1,3) list.set_intros(1) lts_tau.tau_def steps_loop tau_sink_def)
  thus ?thesis using \<open>\<exists>B. A = a#B\<close> by fastforce
qed

subsection \<open>Contrasimulation Equals Weak Simulation on \<open>\<tau>\<close>-Sink Systems\<close>

lemma sink_coupled_simulates_all_states:
  assumes
    \<open>\<And> p . (p \<longmapsto>* tau sink)\<close>
  shows 
    \<open>sink \<sqsubseteq>cs p\<close> 
  by (simp add: assms coupledsim_refl coupledsim_step)

theorem coupledsim_weaksim_equiv_on_sink_expansion:
  assumes
    \<open>\<And> p . (p \<longmapsto>* tau sink)\<close>
  shows
    \<open>p \<sqsubseteq>ws q \<longleftrightarrow> p \<sqsubseteq>cs q\<close>
  using assms 
  using coupled_simulation_weak_simulation weak_sim_tau_step weaksim_greatest by auto

subsection \<open>Contrasimulation Equals Weak Trace Inclusion on \<open>\<tau>\<close>-Sink Systems\<close>
  
lemma sink_contrasimulates_all_states:
fixes A :: " 'a list"
  assumes 
    \<open>tau_sink sink\<close>
    \<open>\<And> p . (p \<longmapsto>* tau sink)\<close>
  shows 
    \<open>\<forall> p. sink \<sqsubseteq>c p\<close>
proof (cases A)
  case Nil
  hence empty_word: \<open>sink \<Rightarrow>$A sink\<close> by (simp add: steps.refl)
  have \<open>\<forall>p. p \<Rightarrow>$A sink\<close> using assms(2) Nil by auto
  have \<open>sink \<sqsubseteq>c sink\<close> using contrasim_tau_step empty_word Nil by auto 
  show ?thesis using assms(2) contrasim_tau_step by auto 
next
  case Cons
  hence \<open>\<nexists>s'. (\<forall> a \<in> set(A). a \<noteq> \<tau>) \<and> sink \<Rightarrow>$A s'\<close>
    using assms(1) sink_has_no_word_transitions by fastforce
  show ?thesis using assms(2) contrasim_tau_step by auto 
qed

lemma sink_trace_includes_all_states:
  assumes 
    \<open>\<And> p . (p \<longmapsto>* tau sink)\<close>
  shows 
    \<open>sink \<sqsubseteq>T p\<close>
  by (metis assms contrasim_tau_step lts_tau.contrasim_implies_trace_incl) 

lemma trace_incl_with_sink_is_contrasim:
  assumes
    \<open>\<And> p . (p \<longmapsto>* tau sink)\<close>
    \<open>\<And> p . R sink p\<close>
    \<open>trace_inclusion R\<close>
  shows
    \<open>contrasimulation R\<close>
 unfolding contrasimulation_def
proof clarify
  fix p q p' A
  assume \<open>R p q\<close> \<open>p \<Rightarrow>$A  p'\<close> \<open>\<forall> a \<in> set(A). a \<noteq> \<tau>\<close>
  hence \<open>\<exists>q'. q \<Rightarrow>$A  q'\<close>
    using assms(3) unfolding trace_inclusion_def by blast
  hence \<open>q \<Rightarrow>$A  sink\<close>
    using assms(1) tau_tau word_tau_concat by blast
  thus \<open>\<exists>q'. q \<Rightarrow>$ A  q' \<and> R q' p'\<close>
    using assms(2) by auto
qed

theorem contrasim_trace_incl_equiv_on_sink_expansion_R:
  assumes
    \<open>\<And> p . (p \<longmapsto>* tau sink)\<close>
    \<open>\<And> p . R sink p\<close>
  shows 
    \<open>contrasimulation R = trace_inclusion R\<close>
proof
  assume \<open>contrasimulation R\<close>
  thus \<open>trace_inclusion R\<close> by (simp add: contrasim_implies_trace_incl)
next
  assume \<open>trace_inclusion R\<close>
  thus \<open>contrasimulation R\<close>  by (meson assms lts_tau.trace_incl_with_sink_is_contrasim)
qed

theorem contrasim_trace_incl_equiv_on_sink_expansion:
  assumes
    \<open>\<And> p . (p \<longmapsto>* tau sink)\<close>
  shows
    \<open>p \<sqsubseteq>T q \<longleftrightarrow> p \<sqsubseteq>c q\<close>
  using assms weak_trace_inlcusion_greatest
    contrasim_tau_step contrasim_trace_incl_equiv_on_sink_expansion_R contrasim_implies_trace_incl
  by (metis (no_types, lifting))

end

subsection \<open>Weak Simulation Invariant under \<open>\<tau>\<close>-Sink Extension\<close>

lemma simulation_tau_sink_1:
  fixes
    step sink R \<tau>
  defines
    \<open>step2 \<equiv> \<lambda> p1 a p2 . (p1 \<noteq> sink \<and> a = \<tau> \<and> p2 = sink) \<or> step p1 a p2\<close>
  assumes
    \<open>\<And> a p . \<not> step sink a p\<close>
    \<open>lts_tau.weak_simulation step \<tau> R\<close>
  shows
    \<open>lts_tau.weak_simulation step2 \<tau> (\<lambda> p q. p = sink \<or> R p q)\<close>
proof -
  let ?tau = \<open>(lts_tau.tau \<tau>)\<close>
  let ?tauEx = \<open>\<tau>\<close>
  show ?thesis unfolding lts_tau.weak_simulation_def
  proof safe
    fix p q p' a
    assume \<open>step2 sink a p'\<close>
    hence \<open>p' = sink\<close> \<open>a = \<tau>\<close>
      using assms(2) unfolding step2_def by auto
    thus \<open>\<exists>q'. (p' = sink \<or> R p' q') \<and>
      (?tau a \<longrightarrow> lts.steps step2 q ?tau q') \<and> 
      (\<not> ?tau a \<longrightarrow> (\<exists>pq1 pq2. lts.steps step2 q ?tau pq1 \<and> step2 pq1 a pq2 
        \<and> lts.steps step2 pq2 ?tau q'))\<close>
      using lts_tau.step_tau_refl[of \<tau> step2 q] by auto
  next
    fix p q p' a
    assume \<open>step2 p a p'\<close> \<open>R p q\<close>
    have step_impl_step2: \<open>\<And> p1 a p2 . step p1 a p2 \<Longrightarrow> step2 p1 a p2\<close>
      unfolding step2_def by blast
    have \<open>(p \<noteq> sink \<and> a = ?tauEx \<and> p' = sink) \<or> step p a p'\<close>
      using `step2 p a p'` unfolding step2_def .
    thus \<open>\<exists>q'. (p' = sink \<or> R p' q') \<and>
      (?tau a \<longrightarrow> lts.steps step2 q ?tau q') \<and>
      (\<not> ?tau a \<longrightarrow> (\<exists>pq1 pq2. lts.steps step2 q ?tau pq1 \<and> step2 pq1 a pq2
        \<and> lts.steps step2 pq2 ?tau q'))\<close>
    proof safe
      show \<open>\<exists>q'. (sink = sink \<or> R sink q') \<and>
           (?tau ?tauEx \<longrightarrow> lts.steps step2 q ?tau q') \<and>
           (\<not> ?tau ?tauEx \<longrightarrow> (\<exists>pq1 pq2. lts.steps step2 q ?tau pq1
            \<and> step2 pq1 ?tauEx pq2 \<and> lts.steps step2 pq2 ?tau q'))\<close>
        using lts.steps.refl[of step2 q ?tau] assms(1) by (meson lts_tau.tau_tau)
    next
      assume \<open>step p a p'\<close>
      then obtain q' where q'_def:
        \<open>R p' q' \<and>
        (?tau a \<longrightarrow> lts.steps step q ?tau q') \<and>
        (\<not> ?tau a \<longrightarrow> (\<exists>pq1 pq2. lts.steps step q ?tau pq1 \<and> step pq1 a pq2
          \<and> lts.steps step pq2 ?tau q'))\<close>
        using assms(3) `R p q` unfolding lts_tau.weak_simulation_def by blast
      hence \<open>(p' = sink \<or> R p' q') \<and>
        (?tau a \<longrightarrow> lts.steps step2 q ?tau q') \<and>
        (\<not> ?tau a \<longrightarrow> (\<exists>pq1 pq2. lts.steps step2 q ?tau pq1 \<and> step2 pq1 a pq2
          \<and> lts.steps step2 pq2 ?tau q'))\<close>
        using lts_impl_steps[of step _ _ _ step2] step_impl_step2 by blast
      thus \<open>\<exists>q'. (p' = sink \<or> R p' q') \<and>
        (?tau a \<longrightarrow> lts.steps step2 q ?tau q') \<and>
        (\<not> ?tau a \<longrightarrow> (\<exists>pq1 pq2. lts.steps step2 q ?tau pq1 \<and> step2 pq1 a pq2
          \<and> lts.steps step2 pq2 ?tau q'))\<close>
        by blast
    qed
  qed
qed
  
lemma simulation_tau_sink_2:
  fixes
    step sink R \<tau>
  defines
    \<open>step2 \<equiv> \<lambda> p1 a p2 . (p1 \<noteq> sink \<and> a = \<tau> \<and> p2 = sink) \<or> step p1 a p2\<close>
  assumes
    \<open>\<And> a p . \<not> step sink a p \<and> \<not> step p a sink\<close>
    \<open>lts_tau.weak_simulation step2 \<tau> (\<lambda> p q. p = sink \<or> R p q)\<close>
    \<open>\<And> p' q' q . (p' = sink \<or> R p' q') 
      \<and> lts.steps step2 q (lts_tau.tau \<tau>) q'  \<longrightarrow> (p' = sink \<or> R p' q)\<close>
  shows
    \<open>lts_tau.weak_simulation step \<tau> (\<lambda> p q. p = sink \<or> R p q)\<close>
proof -
  let ?tau = \<open>(lts_tau.tau \<tau>)\<close>
  let ?tauEx = \<open>\<tau>\<close>
  let ?steps = \<open>lts.steps\<close>
  show ?thesis
    unfolding lts_tau.weak_simulation_def
  proof safe
    fix p q p' a
    assume
      \<open>step sink a p'\<close>
    hence False using assms(2) by blast
    thus \<open>\<exists>q'. (p' = sink \<or> R p' q') \<and>
      (?tau a \<longrightarrow> ?steps step q ?tau q') \<and>
      (\<not> ?tau a \<longrightarrow> (\<exists>pq1 pq2. ?steps step q ?tau pq1 \<and> step pq1 a pq2
        \<and> ?steps step pq2 ?tau q'))\<close> ..
  next
    fix p q p' a
    assume \<open>R p q\<close> \<open>step p a p'\<close>
    hence not_sink: \<open>p \<noteq> sink\<close> \<open>p' \<noteq> sink\<close>
      using assms(2)[of a p] assms(2)[of a p'] by auto
    have \<open>step2 p a p'\<close> using `step p a p'` unfolding step2_def by blast
    then obtain q' where q'_def:
      \<open>p' = sink \<or> R p' q'\<close>
      \<open>?tau a \<longrightarrow> ?steps step2 q ?tau q'\<close>  
      \<open>\<not> ?tau a \<longrightarrow> (\<exists>pq1 pq2. ?steps step2 q ?tau pq1 \<and> step2 pq1 a pq2 
        \<and> ?steps step2 pq2 ?tau q')\<close>
      using assms(3) `R p q` unfolding lts_tau.weak_simulation_def by blast
    hence outer_goal_a: \<open>R p' q'\<close> using not_sink by blast
    show \<open>\<exists>q'. (p' = sink \<or> R p' q') \<and>
      (?tau a \<longrightarrow> ?steps step q ?tau q') \<and>
      (\<not> ?tau a \<longrightarrow> (\<exists>pq1 pq2. ?steps step q ?tau pq1 \<and> step pq1 a pq2
        \<and> ?steps step pq2 ?tau q'))\<close>
    proof (cases \<open>q' = sink\<close>)
      assume \<open>q' = sink\<close>
      then obtain q'' where q''_def:
        \<open>?tau a \<longrightarrow> (?steps step q ?tau q'' \<and> ?steps step2 q'' ?tau q')\<close>
        \<open>\<not> ?tau a \<longrightarrow> (\<exists>pq1. ?steps step2 q ?tau pq1 \<and> step pq1 a q''
          \<and> ?steps step2 q'' ?tau q')\<close>
        using q'_def(2,3) assms(1) step2_def lts_tau.step_tau_refl[of \<tau>]
          lts_tau.tau_tau[of \<tau>] by metis
      hence \<open>q'' = sink \<longrightarrow> q = sink\<close>
        using assms(2) unfolding step2_def by (metis lts.steps.cases)
      have \<open>?steps step2 q'' ?tau q'\<close> using q''_def by auto
      hence \<open>p' = sink \<or> R p' q''\<close> using  q'_def(1) assms(4)[of p' q' q''] by blast
      moreover have \<open>\<not> ?tau a \<longrightarrow> (\<exists>pq1 pq2. ?steps step q ?tau pq1 \<and> step pq1 a pq2
        \<and> ?steps step pq2 ?tau q'')\<close>
      proof
        assume \<open>\<not> ?tau a\<close>
        hence \<open>q \<noteq> sink\<close> using q'_def by (metis assms(2) lts.steps_left step2_def)
        hence \<open>q'' \<noteq> sink\<close> using `q'' = sink \<longrightarrow> q = sink` by simp
        obtain pq1 where pq1_def:
            \<open>?steps step2 q ?tau pq1\<close> \<open>step pq1 a q''\<close> \<open>?steps step2 q'' ?tau q'\<close>
          using q''_def(2) `\<not> ?tau a` by blast
        hence \<open>pq1 \<noteq> sink\<close> using `q'' \<noteq> sink` assms(2) by blast
        hence \<open>?steps step q ?tau pq1\<close> using `q \<noteq> sink` `?steps step2 q ?tau pq1`
        proof (induct rule: lts.steps.induct[OF `?steps step2 q ?tau pq1`])
          case (1 p af)
          then show ?case using lts.steps.refl[of step p af] by blast
        next
          case (2 p af q1 a q)
          hence \<open>q1 \<noteq> sink\<close> \<open>step q1 a q\<close> using assms(2) unfolding step2_def by auto
          moreover hence \<open>?steps step p af q1\<close> using 2 by blast 
          ultimately show ?case using 2(4) by (meson lts.step)
        qed
        thus
          \<open>\<exists>pq1 pq2. ?steps step q ?tau pq1 \<and> step pq1 a pq2 \<and> ?steps step pq2 ?tau q''\<close>
          using pq1_def(2) lts.steps.refl[of step q'' ?tau] by blast
      qed
      ultimately show \<open>\<exists>q''. (p' = sink \<or> R p' q'') \<and>
           (?tau a \<longrightarrow> ?steps step q ?tau q'') \<and>
           (\<not> ?tau a \<longrightarrow> (\<exists>pq1 pq2. ?steps step q ?tau pq1 \<and> step pq1 a pq2
            \<and> ?steps step pq2 ?tau q''))\<close>
        using q''_def(1) q'_def(1) by auto
    next
      assume not_sink_q': \<open>q' \<noteq> sink\<close>
      have outer_goal_b: \<open>?tau a \<longrightarrow> ?steps step q ?tau q'\<close>
        using q'_def(2) not_sink_q' unfolding step2_def
      proof (safe)
        assume i:
          \<open>q' \<noteq> sink\<close> \<open>?tau a\<close>
          \<open>?steps (\<lambda>p1 a p2. p1 \<noteq> sink \<and> a = ?tauEx \<and> p2 = sink \<or> step p1 a p2) q ?tau q'\<close>
        thus \<open>?steps step q ?tau q'\<close>
        proof (induct rule: lts.steps.induct[OF i(3)])
          case (1 p af)
          then show ?case using lts.steps.refl[of _ p af] by auto
        next
          case (2 p af q1 a q)
          hence \<open>step q1 a q\<close> by blast
          moreover have \<open>?steps step p af q1\<close> using 2 assms(2) by blast
          ultimately show ?case using `af a` lts.step[of step p af q1 a q] by blast
        qed
      qed
      have outer_goal_c:
          \<open>\<not> ?tau a \<longrightarrow> (\<exists>pq1 pq2. ?steps step q ?tau pq1 \<and> step pq1 a pq2
          \<and> ?steps step pq2 ?tau q')\<close>
        using q'_def(3)
      proof safe
        fix pq1 pq2
        assume subassms:
          \<open>\<not> ?tau a\<close>
          \<open>?steps step2 q ?tau pq1\<close>
          \<open>step2 pq1 a pq2\<close>
          \<open>?steps step2 pq2 ?tau q'\<close>
        have \<open>pq2 \<noteq> sink\<close> 
          using subassms(4) assms(2) not_sink_q' lts.steps_loop
          unfolding step2_def by (metis (mono_tags, lifting))
        have  goal_c: \<open>?steps step pq2 ?tau q'\<close>
          using subassms(4) not_sink_q' unfolding step2_def
        proof (induct rule:lts.steps.induct[OF subassms(4)])
          case (1 p af) show ?case using lts.steps.refl by assumption
        next
          case (2 p af q1 a q)
          hence \<open>step q1 a q\<close> unfolding step2_def by simp
          moreover hence \<open>q1 \<noteq> sink\<close> using assms(2) by blast
          ultimately have \<open>?steps step p af q1\<close> using 2 unfolding step2_def by auto
          thus ?case using `step q1 a q` 2(4) lts.step[of step p af q1 a q] by blast
        qed
        have goal_b: \<open>step pq1 a pq2\<close>
          using `pq2 \<noteq> sink` subassms(3) unfolding step2_def by blast
        hence \<open>pq1 \<noteq> sink\<close> using assms(2) by blast
        hence goal_a: \<open>?steps step q ?tau pq1\<close>
          using subassms(4) unfolding step2_def
        proof (induct rule:lts.steps.induct[OF subassms(2)])
          case (1 p af) show ?case using lts.steps.refl by assumption
        next
          case (2 p af q1 a q)
          hence \<open>step q1 a q\<close> unfolding step2_def by simp
          moreover hence \<open>q1 \<noteq> sink\<close> using assms(2) by blast
          ultimately have \<open>?steps step p af q1\<close> using 2 unfolding step2_def by auto
          thus ?case using `step q1 a q` 2(4) lts.step[of step p af q1 a q] by blast
        qed
        thus
          \<open>\<exists>pq1 pq2. ?steps step q ?tau pq1 \<and> step pq1 a pq2 \<and> ?steps step pq2 ?tau q'\<close>
          using goal_b goal_c by auto
      qed
      thus \<open>\<exists>q'. (p' = sink \<or> R p' q') \<and> (?tau a \<longrightarrow> ?steps step q ?tau q') \<and>
        (\<not> ?tau a \<longrightarrow> (\<exists>pq1 pq2. ?steps step q ?tau pq1 \<and> step pq1 a pq2
          \<and> ?steps step pq2 ?tau q'))\<close>
        using outer_goal_a outer_goal_b by auto
    qed
  qed
qed

lemma simulation_sink_invariant:
  fixes
    step sink R \<tau>
  defines
    \<open>step2 \<equiv> \<lambda> p1 a p2 . (p1 \<noteq> sink \<and> a =  \<tau> \<and> p2 = sink) \<or> step p1 a p2\<close>
  assumes
    \<open>\<And> a p . \<not> step sink a p \<and> \<not> step p a sink\<close>
  shows \<open>lts_tau.weakly_simulated_by step2 \<tau> p q = lts_tau.weakly_simulated_by step \<tau> p q\<close>
proof (rule)
  have sink_sim_min: \<open>lts_tau.weak_simulation step2 \<tau> (\<lambda> p q. p = sink)\<close>
    unfolding lts_tau.weak_simulation_def step2_def using assms(2)
    by (meson lts.steps.simps)
  define R where \<open>R \<equiv> lts_tau.weakly_simulated_by step2 \<tau>\<close>
  have weak_sim_R: \<open>lts_tau.weak_simulation step2 \<tau> R\<close>
    using lts_tau.weaksim_greatest[of step2 \<tau>] unfolding R_def by blast
  have R_contains_inv_tau_closure:
    \<open>R = (\<lambda>p1 q1. R p1 q1 \<or> lts.steps step2 q1 (lts_tau.tau \<tau>) p1)\<close>
    unfolding R_def using lts_tau.weak_sim_tau_step by fastforce
  assume Rpq: \<open>R p q\<close>
  have \<open>\<And> p' q' q . R p' q' \<and> lts.steps step2 q (lts_tau.tau \<tau>) q'  \<longrightarrow> R p' q\<close>
    using R_contains_inv_tau_closure lts_tau.weak_sim_trans[of step2 \<open>\<tau>\<close> _ _ _] R_def assms(2)
    by meson
  hence closed_R:
      \<open>\<And> p' q' q . (p' = sink \<or> R p' q') \<and> lts.steps step2 q (lts_tau.tau \<tau>) q'
         \<longrightarrow> (p' = sink \<or> R p' q)\<close>
    using weak_sim_R sink_sim_min lts_tau.weak_sim_union_cl by blast
  have \<open>lts_tau.weak_simulation step2 \<tau> (\<lambda>p q. p = sink \<or> R p q)\<close>
    using weak_sim_R sink_sim_min lts_tau.weak_sim_union_cl[of step2 \<tau>] by blast
  hence \<open>lts_tau.weak_simulation step \<tau> (\<lambda>p q. p = sink \<or> R p q)\<close>
    using  simulation_tau_sink_2[of step sink \<tau> R] assms(2) closed_R
    unfolding step2_def by blast
  thus \<open>\<exists>R. lts_tau.weak_simulation step \<tau> R \<and> R p q\<close>
    using Rpq weak_sim_R by blast
next
  show \<open>\<exists>R. lts_tau.weak_simulation step \<tau> R \<and> R p q \<Longrightarrow>
        \<exists>R. lts_tau.weak_simulation step2 \<tau> R \<and> R p q\<close>
  proof clarify
    fix R
    assume
      \<open>lts_tau.weak_simulation step \<tau> R\<close>
      \<open>R p q\<close>
    hence \<open>lts_tau.weak_simulation
      (\<lambda>p1 a p2. p1 \<noteq> sink \<and> a = \<tau> \<and> p2 = sink \<or> step p1 a p2) \<tau> (\<lambda>p q. p = sink \<or> R p q)\<close>
      using simulation_tau_sink_1[of step sink \<tau> R] assms(2) unfolding step2_def by auto
    thus \<open>\<exists>R. lts_tau.weak_simulation step2 \<tau> R \<and> R p q\<close>
      using `R p q` unfolding step2_def by blast
  qed
qed

subsection \<open>Trace Inclusion Invariant under \<open>\<tau>\<close>-Sink Extension\<close>

lemma trace_inclusion_sink_invariant:
  fixes
    step sink R \<tau>
  defines
    \<open>step2 \<equiv> \<lambda> p1 a p2 . (p1 \<noteq> sink \<and> a =  \<tau> \<and> p2 = sink) \<or> step p1 a p2\<close>
  assumes
    \<open>\<And> a p . \<not> step sink a p \<and> \<not> step p a sink\<close>
  shows
    \<open>lts_tau.weakly_trace_included_by step2 \<tau> p q
    = lts_tau.weakly_trace_included_by step \<tau> p q\<close>
proof - 
  let ?tau = \<open>(lts_tau.tau \<tau>)\<close>
  let ?weak_step = \<open>lts_tau.weak_step_tau step \<tau>\<close>
  let ?weak_step2 = \<open>lts_tau.weak_step_tau step2 \<tau>\<close>
  let ?weak_seq = \<open>lts_tau.weak_step_seq step \<tau>\<close>
  let ?weak_seq2 = \<open>lts_tau.weak_step_seq step2 \<tau>\<close>
  {
    fix A
    have \<open>\<forall>p p'. (\<forall> a \<in> set(A). a \<noteq> \<tau>)
    \<and> ?weak_seq2 p A p' 
    \<longrightarrow> (\<exists>p''. ?weak_seq p A p''
    \<and> ?weak_step2 p'' \<tau> p')\<close>
    proof(clarify, induct A rule: rev_induct)
      case Nil
      hence \<open>?weak_step p \<tau> p\<close>
        using lts_tau.step_tau_refl by fastforce
      thus ?case
        by (metis Nil.prems(2) lts_tau.tau_tau lts_tau.weak_step_seq.simps(1)) 
    next
      case (snoc a A)
      hence not_in_set: \<open>\<forall>a\<in>set A. a \<noteq> \<tau>\<close> by force 
      then obtain p01 where 
        \<open>?weak_seq2 p A p01\<close> and
        p01_def2: \<open>?weak_step2 p01 a p'\<close>
        using snoc by (metis lts_tau.rev_seq_split) 
      then obtain p02 where p02_def: 
        \<open>?weak_seq p A p02\<close> 
        \<open>?weak_step2 p02 \<tau> p01\<close>
        using snoc.hyps[of p p01] snoc.prems(1) not_in_set by auto
      hence \<open>?weak_step2 p02 a p'\<close> 
        using p01_def2 lts_tau.step_tau_concat lts_tau.tau_tau
        by (smt (verit, del_insts))
      then obtain p03 p04 where 
        tau1: \<open>?weak_step2 p02 \<tau> p03\<close> and
        a_step2: \<open>step2 p03 a p04\<close> and
        tau2: \<open>?weak_step2 p04 \<tau> p'\<close>
        using snoc.prems(1) lts_tau.tau_def 
        by (metis last_in_set snoc_eq_iff_butlast)
      hence \<open>p04 \<noteq> sink\<close> using assms snoc.prems(1) by force
      hence a_step: \<open>step p03 a p04\<close> using a_step2 assms by auto
      have notsinkp03: \<open>p03 \<noteq> sink\<close> using a_step2 assms snoc.prems(1) by force
      have \<open>lts.steps step2 p02 ?tau p03\<close> using tau1 by (simp add: lts_tau.tau_tau)
      hence \<open>lts.steps step p02 ?tau p03\<close> using notsinkp03
      proof (induct rule: lts.steps.induct[OF `lts.steps step2 p02 ?tau  p03`])
        case (1 p A)
        thus ?case by (simp add: lts.refl)
      next
        case (2 p A q1 a q)
        hence \<open>q1 \<noteq> sink\<close> using assms(2) step2_def by blast 
        thus ?case using 2 lts.step step2_def by metis
      qed 
      hence \<open>?weak_step p02 \<tau> p03\<close> by (simp add: lts_tau.tau_tau)
      hence \<open>?weak_step p02 a p04\<close> using a_step
        by (metis lts.step lts_tau.step_tau_refl lts_tau.tau_tau) 
      hence \<open>?weak_seq p (A@[a]) p04\<close>
        using lts_tau.rev_seq_step_concat p02_def(1) by fastforce 
      thus ?case using tau2 by auto
    qed
  }
  hence step2_to_step: \<open>\<forall>A p p'. (\<forall> a \<in> set(A). a \<noteq> \<tau>)
    \<and> ?weak_seq2 p A p' 
    \<longrightarrow> (\<exists>p''. ?weak_seq p A p'')\<close>
    by fastforce

  have step_to_step2:  \<open>\<forall>A p p'. (\<forall> a \<in> set(A). a \<noteq> \<tau>)
    \<and> ?weak_seq p A p' 
    \<longrightarrow> ?weak_seq2 p A p'\<close>
  proof
    fix A
    show \<open>\<forall>p p'. (\<forall> a \<in> set(A). a \<noteq> \<tau>)
    \<and> ?weak_seq p A p' 
    \<longrightarrow> ?weak_seq2 p A p'\<close>
    proof(clarify, induct A rule: list.induct)
      case Nil
      assume \<open>?weak_seq p [] p'\<close>
      hence tau_step: \<open>?weak_step p \<tau> p'\<close>
        by (simp add: lts_tau.weak_step_seq.simps(1) lts_tau.tau_tau)
      hence \<open>?weak_step2 p \<tau> p'\<close>
        using lts_impl_steps step2_def lts_tau.tau_tau  by force 
      thus ?case by (simp add: lts_tau.weak_step_seq.simps(1) lts_tau.tau_tau) 
    next
      case (Cons x xs)
      then obtain p1 where p1_def: \<open>?weak_step p x p1\<close> 
      \<open>?weak_seq p1 xs p'\<close>
        by (metis (mono_tags, lifting) lts_tau.weak_step_seq.simps(2))
      hence IH: \<open>?weak_seq2 p1 xs p'\<close> using Cons by auto
      then obtain p01 p02 where \<open>?weak_step p \<tau> p01\<close> and
        strong: \<open>step p01 x p02\<close> and
        p02_weak: \<open>?weak_step p02 \<tau> p1\<close>
        using Cons.prems(1) p1_def lts_tau.tau_def by (metis list.set_intros(1))
      hence tau1: \<open>?weak_step2 p \<tau> p01\<close> 
        using lts_impl_steps step2_def
        by (smt (verit, best))
      have \<open>?weak_step2 p02 \<tau> p1\<close> 
        using p02_weak lts_impl_steps step2_def by (smt (verit, best))
      hence \<open>?weak_step2 p x p1\<close> 
        using tau1 strong step2_def Cons.prems(1) lts_tau.tau_def
        by (metis list.set_intros(1))  
      thus \<open>?weak_seq2 p (x#xs) p'\<close> 
        using IH lts_tau.weak_step_seq_def[of step2 \<tau>] by auto
    qed
  qed
  show ?thesis
  proof (rule)
    assume \<open>\<exists>R. lts_tau.trace_inclusion step2 \<tau> R \<and> R p q\<close>
    then obtain R where weak_sim_R: \<open>lts_tau.trace_inclusion step2 \<tau> R\<close>
      and Rpq: \<open>R p q\<close>
      by blast
    have \<open>lts_tau.trace_inclusion step \<tau> R\<close>
      unfolding lts_tau.trace_inclusion_def
    proof clarify
      fix p q p' A
      assume subassms: 
        \<open>\<forall>a\<in>set A. a \<noteq> \<tau>\<close>
        \<open>R p q\<close>
        \<open>?weak_seq p A p'\<close>
      hence \<open>(\<forall>a\<in>set A. a \<noteq> \<tau>) \<and>
       ?weak_seq2 p A p' \<longrightarrow>
       (\<exists>q'. ?weak_seq2 q A q')\<close> 
        using weak_sim_R 
        unfolding lts_tau.trace_inclusion_def by simp
      hence \<open>(\<forall>a\<in>set A. a \<noteq> \<tau>) \<and>
       ?weak_seq p A p' \<longrightarrow>
       (\<exists>q'. ?weak_seq q A q')\<close>
        using step2_to_step step_to_step2
        by auto
      thus "\<exists>q'. ?weak_seq q A q'"
        by (simp add: subassms)
    qed
    thus \<open>\<exists>R. lts_tau.trace_inclusion step \<tau> R \<and> R p q\<close>
      using Rpq by auto
  next 
    assume \<open>\<exists>R. lts_tau.trace_inclusion step \<tau> R \<and> R p q\<close>
    then obtain R where weak_sim_R: \<open>lts_tau.trace_inclusion step \<tau> R\<close>
      and Rpq: \<open>R p q\<close>
      by blast
    have \<open>lts_tau.trace_inclusion step2 \<tau> R\<close> 
      unfolding lts_tau.trace_inclusion_def
    proof clarify
      fix p q p' A
      assume subassms: 
        \<open>\<forall>a\<in>set A. a \<noteq> \<tau>\<close>
        \<open>R p q\<close>
        \<open>?weak_seq2 p A p'\<close>
      thus \<open>\<exists>q'. ?weak_seq2 q A q'\<close>
        using step2_to_step step_to_step2
        by (metis (full_types) lts_tau.trace_inclusion_def weak_sim_R)
    qed
    thus \<open>\<exists>R. lts_tau.trace_inclusion step2 \<tau> R \<and> R p q\<close> using Rpq by auto
  qed
qed

end
