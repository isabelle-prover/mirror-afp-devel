chapter \<open>Obliviousness\label{s:oblivious}\<close>

text \<open>
In order to show that \SAT{} is $\NP$-hard we will eventually show how to reduce
an arbitrary language $L \in \NP$ to \SAT{}. The proof can only use properties
of $L$ common to all languages in $\NP$. The definition of $\NP$ provides us
with a verifier Turing machine $M$ for $L$, of which we only know that it is
running in polynomial time. In addition by lemma~@{text NP_output_len_1} we can
assume that $M$ outputs a single bit symbol. In this chapter we are going to
show that we can make additional assumptions about $M$, namely:

\begin{enumerate}
  \item $M$ has only two tapes.
  \item $M$ halts on $\langle x, u\rangle$ with the output tape head on the
    symbol \textbf{1} iff.\ $u$ is a certificate for $x$.
  \item $M$ is \emph{oblivious}, which means that on any input $x$ the head
  positions of $M$ on all its tapes depend only on the \emph{length} of $x$, not
  on the symbols in $x$~\cite[Remark~1.7]{ccama}.
\end{enumerate}

These additional properties will somewhat simplify the reduction of $L$ to
\SAT{}, more precisely the construction of the CNF formulas (see
Chapter~\ref{s:Reducing}).

In order to achieve this goal we will show how to simulate any polynomial-time
multi-tape TM in polynomial time on a two-tape oblivious TM that halts with
the output tape head on cell~1.

Given a polynomial-time $k$-tape TM $M$, the basic approach is to construct a
two-tape TM that encodes the $k$ tapes of $M$ on its output tape in such a way
that every cell encodes $k$ symbols of $M$ and flags for $M$'s tape heads.  This
is the same idea as used by Dalvit and
Thiemann~\cite{Multitape_To_Singletape_TM-AFP} and originally Hartmanis and
Stearns~\cite{hs65} for simulating a multi-tape TM on a single-tape TM. After
all our two-tape simulator can only properly use a single tape (the output/work
tape). This simulator has roughly a quadratic running time overhead and so keeps
the running time polynomial. However, it is not generally an oblivious TM.

To make the simulator TM oblivious, we have it initially ``format'' a section on
the output tape that is long enough to hold everything $M$ is going to write and
whose length only depends on the input length. To simulate one step of $M$, the
simulator then sweeps its output tape head all the way from the start of the
tape to the end of the formatted space and back again, moving one cell per step.
During these sweeps it executes one step of the simulation of $M$. Since the
size of the formatted space only depends on the input length, the simulator
performs the same head movements on inputs of the same length, resulting in an
oblivious behavior. Moreover, it is easy to make it halt with the output tape
head on cell number~1.

The formatter TM is described in Section~~\ref{s:oblivious-polynomial}. The
simulator TM is then constructed in Section~\ref{s:oblivious-two-tape}. Finally
Section~\ref{s:oblivious-np} states the main result of this chapter.

Before any of this, however, we have to define some basic concepts surrounding
obliviousness.
\<close>


section \<open>Oblivious Turing machines\label{s:oblivious-tm}\<close>

theory Oblivious
  imports Memorizing
begin

text \<open>
This section provides us with the tools for showing that a Turing machine is
oblivious and for combining oblivious TMs into more complex oblivious TMs.

So far our analysis of Turing machines involved their semantics and running time
bounds. For this we mainly used the @{const transforms} predicate, which relates
a start configuration and a halting configuration and an upper bound for the
running time of a TM to transit from the one configuration to the other. To deal
with obliviousness, we need to look more closely and inspect the sequence of
tape head positions during the TM's execution, rather than only the running
time.

The subsections in this section roughly correspond to Sections~\ref{s:tm-basic}
to~\ref{s:tm-memorizing}. In the first subsection we introduce a predicate
@{term trace} analogous to @{const transforms} and show its behavior under
sequential composition of TMs and loops (we will not need branches). The next
subsection shows the head position sequences for those few elementary TMs from
Section~\ref{s:tm-elementary} that we need for our more complex oblivious TMs
later. These constructions will also heavily use the memorization-in-states
technique from Section~\ref{s:tm-memorizing}, which we adapt to this chapter's
needs in the final subsection.
\<close>


subsection \<open>Traces and head positions\<close>

text \<open>
In order to show that a Turing machine is oblivious we need to keep track of its
head positions. Consider a machine $M$ that transits from a configuration @{term
cfg1} to a configuration @{term cfg2} in $t$ steps.  We call the sequence of
head positions on the first two tapes a \emph{trace}. If we ignore the initial
head positions, the length of a trace equals $t$. Moreover we will only
consider traces where $M$ either does not halt or halts in the very last step.
These two properties mean, for example, that we can simply concatenate a trace
of a TM that halts and trace of another TM and get the trace of the sequential
execution of both TMs.  Similarly, analysing while loops is simplified by these
two extra assumptions. The next predicate defines what it means for a list
@{term "es :: (nat \<times> nat) list"} to be a trace.
\<close>

definition trace :: "machine \<Rightarrow> config \<Rightarrow> (nat \<times> nat) list \<Rightarrow> config \<Rightarrow> bool" where
  "trace M cfg1 es cfg2 \<equiv>
     execute M cfg1 (length es) = cfg2 \<and>
     (\<forall>i<length es. fst (execute M cfg1 i) < length M) \<and>
     (\<forall>i<length es. execute M cfg1 (Suc i) <#> 0 = fst (es ! i)) \<and>
     (\<forall>i<length es. execute M cfg1 (Suc i) <#> 1 = snd (es ! i))"

text \<open>
We will consider traces for machines with more than two tapes, too, but only for
auxiliary constructions in combination with the memorizing-in-states technique.
Therefore our definition is limited to start configurations with two tapes. A
machine is \emph{oblivious} if there is a function mapping the input length
to the trace that takes the machine from the start configuration with that
input to a halting configuration.
\<close>

definition oblivious :: "machine \<Rightarrow> bool" where
  "oblivious M \<equiv> \<exists>e.
    (\<forall>zs. bit_symbols zs \<longrightarrow> (\<exists>tps. trace M (start_config 2 zs) (e (length zs)) (length M, tps)))"

lemma trace_Nil: "trace M cfg [] cfg"
  unfolding trace_def by simp

lemma traceI:
  assumes "execute M (q1, tps1) (length es) = (q2, tps2)"
    and "\<And>i. i < length es \<Longrightarrow> fst (execute M (q1, tps1) i) < length M"
    and "\<And>i. i < length es \<Longrightarrow>
      execute M (q1, tps1) (Suc i) <#> 0 = fst (es ! i) \<and>
      execute M (q1, tps1) (Suc i) <#> 1 = snd (es ! i)"
  shows "trace M (q1, tps1) es (q2, tps2)"
  using trace_def assms by simp

lemma traceI':
  assumes "execute M cfg1 (length es) = cfg2"
    and "\<And>i. i < length es \<Longrightarrow> fst (execute M cfg1 i) < length M"
    and "\<And>i. i < length es \<Longrightarrow>
      execute M cfg1 (Suc i) <#> 0 = fst (es ! i) \<and>
      execute M cfg1 (Suc i) <#> 1 = snd (es ! i)"
  shows "trace M cfg1 es cfg2"
  using trace_def assms by simp

lemma trace_additive:
  assumes "trace M (q1, tps1) es1 (q2, tps2)" and "trace M (q2, tps2) es2 (q3, tps3)"
  shows "trace M (q1, tps1) (es1 @ es2) (q3, tps3)"
proof (rule traceI)
  let ?es = "es1 @ es2"
  show "execute M (q1, tps1) (length (es1 @ es2)) = (q3, tps3)"
    using trace_def assms by (simp add: execute_additive)
  show "fst (execute M (q1, tps1) i) < length M" if "i < length ?es" for i
  proof (cases "i < length es1")
    case True
    then show ?thesis
      using that assms(1) trace_def by simp
  next
    case False
    have "execute M (q1, tps1) (length es1 + (i - length es1)) = execute M (q2, tps2) (i - length es1)"
      using execute_additive that assms(1) trace_def by blast
    then have *: "execute M (q1, tps1) i = execute M (q2, tps2) (i - length es1)"
      using False by simp
    have "i - length es1 < length es2"
      using that False by simp
    then have "fst (execute M (q2, tps2) (i - length es1)) < length M"
      using assms(2) trace_def by simp
    then show ?thesis
      using * by simp
  qed
  show "execute M (q1, tps1) (Suc i) <#> 0 = fst (?es ! i) \<and>
        execute M (q1, tps1) (Suc i) <#> 1 = snd (?es ! i)"
    if "i < length ?es" for i
  proof (cases "i < length es1")
    case True
    then show ?thesis
      using that assms(1) trace_def by (simp add: nth_append)
  next
    case False
    have "execute M (q1, tps1) (length es1 + (Suc i - length es1)) = execute M (q2, tps2) (Suc i - length es1)"
      using execute_additive that assms(1) trace_def by blast
    then have *: "execute M (q1, tps1) (Suc i) = execute M (q2, tps2) (Suc (i - length es1))"
      using False by (simp add: Suc_diff_le)
    have "i - length es1 < length es2"
      using that False by simp
    then have "execute M (q2, tps2) (Suc (i - length es1)) <#> 0 = fst (es2 ! (i - length es1))"
      and "execute M (q2, tps2) (Suc (i - length es1)) <#> 1 = snd (es2 ! (i - length es1))"
      using assms(2) trace_def by simp_all
    then show ?thesis
      using * by (simp add: False nth_append)
  qed
qed

lemma trace_additive':
  assumes "trace M cfg1 es1 cfg2" and "trace M cfg2 es2 cfg3"
  shows "trace M cfg1 (es1 @ es2) cfg3"
  using trace_additive assms by (metis prod.collapse)

text \<open>
We mostly consider traces from the start state to the halting state, for which
we introduce the next predicate.
\<close>

definition traces :: "machine \<Rightarrow> tape list \<Rightarrow> (nat \<times> nat) list \<Rightarrow> tape list \<Rightarrow> bool" where
  "traces M tps1 es tps2 \<equiv> trace M (0, tps1) es (length M, tps2)"

text \<open>
The relation between @{const traces} and @{const trace} is like that between
@{const transforms} and @{const transits}.
\<close>

lemma tracesI [intro]:
  assumes "execute M (0, tps1) (length es) = (length M, tps2)"
    and "\<And>i. i < length es \<Longrightarrow> fst (execute M (0, tps1) i) < length M"
    and "\<And>i. i < length es \<Longrightarrow>
      execute M (0, tps1) (Suc i) <#> 0 = fst (es ! i) \<and>
      execute M (0, tps1) (Suc i) <#> 1 = snd (es ! i)"
  shows "traces M tps1 es tps2"
  using traces_def trace_def assms by simp

lemma traces_additive:
  assumes "trace M (0, tps1) es1 (0, tps2)"
    and "traces M tps2 es2 tps3"
  shows "traces M tps1 (es1 @ es2) tps3"
  using assms traces_def trace_additive by simp

lemma execute_trace_append:
  assumes "trace M1 (0, tps1) es1 (length M1, tps2)" (is "trace _ ?cfg1 _ _")
    and "t \<le> length es1"
  shows "execute (M1 @ M2) (0, tps1) t = execute M1 (0, tps1) t"
    (is "execute ?M _ _ = _")
  using assms(2)
proof (induction t)
  case 0
  then show ?case
    by simp
next
  case (Suc t)
  then have "t < length es1"
    by simp
  then have 1: "fst (execute M1 ?cfg1 t) < length M1"
    using traces_def trace_def assms(1) by simp
  have 2: "length ?M = length M1 + length M2"
    using length_turing_machine_sequential by simp
  have "execute ?M ?cfg1 (Suc t) = exe ?M (execute ?M ?cfg1 t)"
    by simp
  also have "... = exe ?M (execute M1 ?cfg1 t)" (is "_ = exe _ ?cfg")
    using Suc by simp
  also have "... = sem (?M ! (fst ?cfg)) ?cfg"
    using 1 2 exe_def by simp
  also have "... = sem (M1 ! (fst ?cfg)) ?cfg"
    using 1 by (simp add: nth_append turing_machine_sequential_def)
  also have "... = exe M1 (execute M1 ?cfg1 t)"
    using exe_def 1 by simp
  also have "... = execute M1 ?cfg1 (Suc t)"
    by simp
  finally show ?case .
qed


subsection \<open>Increasing the number of tapes\<close>

text \<open>
This is lemma @{thm [source] transforms_append_tapes} adapted for @{const
traces}.
\<close>

lemma traces_append_tapes:
  assumes "turing_machine 2 G M" and "length tps1 = 2" and "traces M tps1 es tps2"
  shows "traces (append_tapes 2 (2 + length tps') M) (tps1 @ tps') es (tps2 @ tps')"
proof
  let ?M = "append_tapes 2 (2 + length tps') M"
  show "execute ?M (0, tps1 @ tps') (length es) = (length ?M, tps2 @ tps')"
  proof -
    have "execute M (0, tps1) (length es) = (length M, tps2)"
      using assms(3) by (simp add: trace_def traces_def)
    moreover have "execute ?M (0, tps1 @ tps') (length es) =
        (fst (execute M (0, tps1) (length es)), snd (execute M (0, tps1) (length es)) @ tps')"
      using execute_append_tapes'[OF assms(1-2)] by simp
    ultimately show ?thesis
      by (simp add: length_append_tapes)
  qed
  show "fst (execute ?M (0, tps1 @ tps') i) < length ?M" if "i < length es" for i
  proof -
    have "fst (execute M (0, tps1) i) < length M"
      using that assms(3) trace_def traces_def by blast
    then show "fst (execute ?M (0, tps1 @ tps') i) < length ?M"
      by (metis (no_types) assms(1,2) execute_append_tapes' fst_conv length_append_tapes)
  qed
  show "snd (execute ?M (0, tps1 @ tps') (Suc i)) :#: 0 = fst (es ! i) \<and>
        snd (execute ?M (0, tps1 @ tps') (Suc i)) :#: 1 = snd (es ! i)"
    if "i < length es" for i
  proof -
    have "snd (execute ?M (0, tps1 @ tps') (Suc i)) = snd (execute M (0, tps1) (Suc i)) @ tps'"
      using execute_append_tapes' assms by (metis snd_conv)
    moreover have "||execute M (0, tps1) (Suc i)|| = 2"
      using assms(1,2) by (metis execute_num_tapes snd_conv)
    ultimately show ?thesis
      using that assms by (simp add: nth_append trace_def traces_def)
  qed
qed


subsection \<open>Combining Turing machines\<close>

text \<open>
Traces for sequentially composed Turing machines are just concatenated traces of
the individual machines.
\<close>

lemma traces_sequential:
  assumes "traces M1 tps1 es1 tps2" and "traces M2 tps2 es2 tps3"
  shows "traces (M1 ;; M2) tps1 (es1 @ es2) tps3"
proof
  let ?M = "M1 ;; M2"
  let ?cfg1 = "(0, tps1)"
  let ?cfg1' = "(length M1, tps2)"
  let ?cfg2 = "(0, tps2)"
  let ?cfg2' = "(length M2, tps3)"
  let ?es = "es1 @ es2"
  have 3: "execute M1 ?cfg1 (length es1) = ?cfg1'"
    using assms(1) traces_def trace_def by simp
  have "fst ?cfg1 = 0"
    by simp
  have 4: "execute M2 ?cfg2 (length es2) = ?cfg2'"
    using assms(2) traces_def trace_def by auto
  have "?cfg1' = ?cfg2 <+=> length M1"
    by simp
  have 2: "length ?M = length M1 + length M2"
    using length_turing_machine_sequential by simp
  have t_le: "execute ?M ?cfg1 t = execute M1 ?cfg1 t" if "t \<le> length es1" for t
    using that
  proof (induction t)
    case 0
    then show ?case
      by simp
  next
    case (Suc t)
    then have "t < length es1"
      by simp
    then have 1: "fst (execute M1 ?cfg1 t) < length M1"
      using traces_def trace_def assms(1) by simp
    have "execute ?M ?cfg1 (Suc t) = exe ?M (execute ?M ?cfg1 t)"
      by simp
    also have "... = exe ?M (execute M1 ?cfg1 t)" (is "_ = exe _ ?cfg")
      using Suc by simp
    also have "... = sem (?M ! (fst ?cfg)) ?cfg"
      using 1 2 exe_def by simp
    also have "... = sem (M1 ! (fst ?cfg)) ?cfg"
      using 1 by (simp add: nth_append turing_machine_sequential_def)
    also have "... = exe M1 (execute M1 ?cfg1 t)"
      using exe_def 1 by simp
    also have "... = execute M1 ?cfg1 (Suc t)"
      by simp
    finally show ?case .
  qed
  have t_ge: "execute ?M ?cfg1 (length es1 + t) = execute M2 ?cfg2 t <+=> length M1"
      if "t \<le> length es2" for t
    using that
  proof (induction t)
    case 0
    then show ?case
      using t_le 3 by simp
  next
    case (Suc t)
    have "execute ?M ?cfg1 (length es1 + Suc t) = execute ?M ?cfg1 (Suc (length es1 + t))"
      by simp
    also have "... = exe ?M (execute ?M ?cfg1 (length es1 + t))"
      by simp
    also have "... = exe ?M (execute M2 ?cfg2 t <+=> length M1)"
        (is "_ = exe _ (?cfg <+=> _)")
      using Suc by simp
    also have "... = (exe M2 (execute M2 ?cfg2 t)) <+=> length M1"
      using exe_relocate by simp
    also have "... = execute M2 ?cfg2 (Suc t) <+=> length M1"
      by simp
    finally show ?case .
  qed
  show "fst (execute ?M ?cfg1 i) < length ?M" if "i < length ?es" for i
  proof (cases "i < length es1")
    case True
    then show ?thesis
      using t_le assms(1) traces_def trace_def 2 by auto
  next
    case False
    then obtain i' where "i = length es1 + i'" "i' \<le> length es2"
      by (metis \<open>i < length (es1 @ es2)\<close> add_diff_inverse_nat add_le_cancel_left length_append less_or_eq_imp_le)
    then show ?thesis
      using t_ge assms(2) traces_def trace_def that 2 by simp
  qed
  show "execute ?M ?cfg1 (length ?es) = (length ?M, tps3)"
    by (simp add: 2 4 t_ge)
  show "execute ?M ?cfg1 (Suc i) <#> 0 = fst (?es ! i) \<and>
        execute ?M ?cfg1 (Suc i) <#> 1 = snd (?es ! i)"
        if "i < length ?es" for i
  proof (cases "i < length es1")
    case True
    then have "Suc i \<le> length es1"
      by simp
    then have "execute ?M ?cfg1 (Suc i) = execute M1 ?cfg1 (Suc i)"
      using t_le by blast
    then show ?thesis
      using assms(1) traces_def trace_def by (simp add: True nth_append)
  next
    case False
    have 8: "i - length es1 < length es2"
      using False that by simp
    with False have "Suc i - length es1 \<le> length es2"
      by simp
    then have "execute ?M ?cfg1 (Suc i) = execute M2 ?cfg2 (Suc i - length es1) <+=> length M1"
      using t_ge False by fastforce
    moreover have "?es ! i = es2 ! (i - length es1)"
      by (simp add: False nth_append)
    moreover have "execute M2 ?cfg2 (Suc i) <#> 0 = fst (es2 ! i) \<and>
        execute M2 ?cfg2 (Suc i) <#> 1 = snd (es2 ! i)" if "i < length es2" for i
        using that assms(2) traces_def trace_def by simp
    ultimately show ?thesis
      by (metis "8" False Nat.add_diff_assoc le_less_linear plus_1_eq_Suc snd_conv)
  qed
qed

text \<open>
Next we show how to derive traces for machines created by the @{text WHILE}
operation. If the condition is false, the trace of the loop is the trace for the
machine computing the condition plus a singleton trace for the jump.
\<close>

lemma tm_loop_sem_false_trace:
  assumes "traces M1 tps0 es1 tps1"
    and "\<not> cond (read tps1)"
  shows "trace
            (WHILE M1 ; cond DO M2 DONE)
            (0, tps0)
            (es1 @ [(tps1 :#: 0, tps1 :#: 1)])
            (length M1 + length M2 + 2, tps1)"
    (is "trace ?M _ _ _")
proof (rule traceI)
  let ?C1 = "M1"
  let ?C2 = "[cmd_jump cond (length M1 + 1) (length M1 + length M2 + 2)]"
  let ?C3 = "relocate (length M1 + 1) M2"
  let ?C4 = "[cmd_jump (\<lambda>_. True) 0 0]"
  let ?C34 = "?C3 @ ?C4"
  have parts: "?M = ?C1 @ ?C2 @ ?C3 @ ?C4"
    using turing_machine_loop_def by simp
  then have 1: "?M ! (length M1) = cmd_jump cond (length M1 + 1) (length M1 + length M2 + 2)"
    by simp
  let ?es = "es1 @ [(tps1 :#: 0, tps1 :#: 1)]"
  show goal1: "execute ?M (0, tps0) (length ?es) = (length M1 + length M2 + 2, tps1)"
  proof -
    have "execute ?M (0, tps0) (length es1) = execute M1 (0, tps0) (length es1)"
      using execute_trace_append assms by (simp add: traces_def turing_machine_loop_def)
    then have 2: "execute ?M (0, tps0) (length es1) = (length M1, tps1) "
      using assms trace_def traces_def by simp
    have "execute ?M (0, tps0) (length ?es) = execute ?M (0, tps0) (Suc (length es1))"
      by simp
    also have "... = exe ?M (execute ?M (0, tps0) (length es1))"
      by simp
    also have "... = exe ?M (length M1, tps1)"
      using 2 by simp
    also have "... = sem (cmd_jump cond (length M1 + 1) (length M1 + length M2 + 2)) (length M1, tps1)"
      by (simp add: "1" exe_lt_length turing_machine_loop_len)
    also have "... = (length M1 + length M2 + 2, tps1)"
      using assms(2) sem_jump by simp
    finally show ?thesis .
  qed
  show "fst (execute ?M (0, tps0) i) < length ?M" if "i < length ?es" for i
  proof (cases "i < length es1")
    case True
    then have "execute ?M (0, tps0) i = execute M1 (0, tps0) i"
      using execute_trace_append assms parts by (simp add: traces_def)
    then show ?thesis
      using assms(1) trace_def traces_def True turing_machine_loop_len by auto
  next
    case False
    with that have "i = length es1"
      by simp
    then show ?thesis
      using assms(1) trace_def traces_def turing_machine_loop_len
      by (simp add: execute_trace_append parts)
  qed
  show "execute ?M (0, tps0) (Suc i) <#> 0 = fst (?es ! i) \<and>
        execute ?M (0, tps0) (Suc i) <#> 1 = snd (?es ! i)"
    if "i < length ?es" for i
  proof (cases "i < length es1")
    case True
    then have "Suc i \<le> length es1"
      by simp
    then have "execute ?M (0, tps0) (Suc i) = execute M1 (0, tps0) (Suc i)"
      using execute_trace_append assms parts by (metis traces_def)
    then show ?thesis
      using assms(1) trace_def traces_def True by (simp add: nth_append)
  next
    case False
    with that have "Suc i = length ?es"
      by simp
    then show ?thesis
      using goal1 by simp
  qed
qed

lemma tm_loop_sem_false_traces:
  assumes "traces M1 tps0 es1 tps1"
    and "\<not> cond (read tps1)"
    and "es = es1 @ [(tps1 :#: 0, tps1 :#: 1)]"
  shows "traces (WHILE M1 ; cond DO M2 DONE) tps0 es tps1"
  using tm_loop_sem_false_trace assms traces_def turing_machine_loop_len by fastforce

text \<open>
If the loop condition evaluates to true, the trace of one iteration is the
concatenation of the traces of the condition machine and the loop body machine
with two additional singleton traces for the jumps.
\<close>

lemma tm_loop_sem_true_traces:
  assumes "traces M1 tps0 es1 tps1"
    and "traces M2 tps1 es2 tps2"
    and "cond (read tps1)"
  shows "trace
            (WHILE M1 ; cond DO M2 DONE)
            (0, tps0)
            (es1 @ [(tps1 :#: 0, tps1 :#: 1)] @ es2 @ [(tps2 :#: 0, tps2 :#: 1)])
            (0, tps2)"
    (is "trace ?M _ ?es _")
proof (rule traceI)
  let ?C1 = "M1"
  let ?C2 = "[cmd_jump cond (length M1 + 1) (length M1 + length M2 + 2)]"
  let ?C3 = "relocate (length M1 + 1) M2"
  let ?C4 = "[cmd_jump (\<lambda>_. True) 0 0]"
  let ?C34 = "?C3 @ ?C4"
  have parts: "?M = ?C1 @ ?C2 @ ?C3 @ ?C4"
    using turing_machine_loop_def by simp
  then have 1: "?M ! (length M1) = cmd_jump cond (length M1 + 1) (length M1 + length M2 + 2)"
    by simp
  from parts have parts': "?M = ((?C1 @ ?C2) @ ?C3) @ ?C4"
    by simp
  have len_M: "length ?M = length M1 + length M2 + 2"
    using turing_machine_loop_len assms by simp
  have len_es: "length ?es = length es1 + length es2 + 2"
    by simp

  have exec_1: "execute ?M (0, tps0) t = execute M1 (0, tps0) t" if "t \<le> length es1" for t
    using execute_trace_append assms by (simp add: parts that traces_def)

  have exec_2: "execute ?M (0, tps0) (length es1 + 1) = (length M1 + 1, tps1)"
  proof -
    have "execute ?M (0, tps0) (length es1) = execute M1 (0, tps0) (length es1)"
      using execute_trace_append assms by (simp add: traces_def turing_machine_loop_def)
    then have 2: "execute ?M (0, tps0) (length es1) = (length M1, tps1) "
      using assms trace_def traces_def by simp
    have "execute ?M (0, tps0) (length es1 + 1) = execute ?M (0, tps0) (Suc (length es1))"
      by simp
    also have "... = exe ?M (execute ?M (0, tps0) (length es1))"
      by simp
    also have "... = exe ?M (length M1, tps1)"
      using 2 by simp
    also have "... = sem (cmd_jump cond (length M1 + 1) (length M1 + length M2 + 2)) (length M1, tps1)"
      by (simp add: "1" exe_lt_length turing_machine_loop_len)
    also have "... = (length M1 + 1, tps1)"
      using assms(3) sem_jump by simp
    finally show ?thesis .
  qed

  have exec_3': "execute ?M (0, tps0) (length es1 + 1 + t) = execute M2 (0, tps1) t <+=> (length M1 + 1)"
    if "t \<le> length es2" for t
    using that
  proof (induction t)
    case 0
    then show ?case
      using exec_2 by simp
  next
    case (Suc t)
    then have 2: "fst (execute M2 (0, tps1) t) < length M2"
      using assms(2) trace_def traces_def by simp
    then have 3: "fst (execute M2 (0, tps1) t <+=> (length M1 + 1)) < length M1 + length M2 + 1"
      by simp
    have 4: "fst (execute M2 (0, tps1) t <+=> (length M1 + 1)) \<ge> length M1 + 1"
      by simp

    have "?M = (?C1 @ ?C2) @ (?C3 @ ?C4)"
      using parts by simp
    moreover have "length (?C1 @ ?C2) = length M1 + 1"
      by simp
    ultimately have "?M ! i = (?C3 @ ?C4) ! (i - (length M1 + 1))"
        if "i \<ge> length M1 + 1" and "i < length M1 + length M2 + 1" for i
      using that by (simp add: nth_append)
    then have "?M ! i = ?C3 ! (i - (length M1 + 1))"
        if "i \<ge> length M1 + 1" and "i < length M1 + length M2 + 1" for i
      using that
      by (smt One_nat_def \<open>length (?C1 @ ?C2) = length M1 + 1\<close>
        add.right_neutral add_Suc_right append.assoc length_append not_le nth_append plus_nat.simps(2) length_relocate)
    with 3 4 have "?M ! (fst (execute M2 (0, tps1) t <+=> (length M1 + 1))) =
        ?C3 ! ((fst (execute M2 (0, tps1) t <+=> (length M1 + 1))) - (length M1 + 1))"
      by simp
    then have in_C3: "?M ! (fst (execute M2 (0, tps1) t <+=> (length M1 + 1))) =
        ?C3 ! ((fst (execute M2 (0, tps1) t)))"
      by simp

    have "execute ?M (0, tps0) (length es1 + 1 + Suc t) = execute ?M (0, tps0) (Suc (length es1 + 1 + t))"
      by simp
    also have "... = exe ?M (execute ?M (0, tps0) (length es1 + 1 + t))"
      by simp
    also have "... = exe ?M (execute M2 (0, tps1) t <+=> (length M1 + 1))"
        (is "_ = exe ?M ?cfg")
      using Suc by simp
    also have "... = sem (?M ! (fst ?cfg)) ?cfg"
      using exe_def "3" len_M by simp
    also have "... = sem (?C3 ! (fst (execute M2 (0, tps1) t))) (execute M2 (0, tps1) t)"
      using in_C3 sem by simp
    also have "... = sem (M2 ! (fst (execute M2 (0, tps1) t))) (execute M2 (0, tps1) t) <+=> (length M1 + 1)"
      using sem_relocate 2 by simp
    also have "... = exe M2 (execute M2 (0, tps1) t) <+=> (length M1 + 1)"
      by (simp add: 2 exe_def)
    also have "... = (execute M2 (0, tps1) (Suc t)) <+=> (length M1 + 1)"
      by simp
    finally show ?case .
  qed
  then have exec_3: "execute ?M (0, tps0) t = execute M2 (0, tps1) (t - (length es1 + 1)) <+=> (length M1 + 1)"
      if "t \<ge> length es1 + 1 " and "t \<le> length es1 + length es2 + 1" for t
    using that
    by (smt Nat.add_diff_assoc2 Nat.diff_diff_right add_diff_cancel_left' add_diff_cancel_right' le_Suc_ex le_add2)

  have exec_4: "execute ?M (0, tps0) (length es1 + length es2 + 2) = (0, tps2)"
  proof -
    have "execute ?M (0, tps0) (length es1 + length es2 + 2) = execute ?M (0, tps0) (Suc (length es1 + length es2 + 1))"
      by simp
    also have "... = exe ?M (execute ?M (0, tps0) (length es1 + length es2 + 1))"
      by simp
    also have "... = exe ?M (execute M2 (0, tps1) (length es2) <+=> (length M1 + 1))"
        (is "_ = exe ?M ?cfg")
      using exec_3' by simp
    also have "... = sem (?M ! (fst ?cfg)) ?cfg"
      using exe_def assms(2) len_M trace_def traces_def by auto
    also have "... = sem (cmd_jump (\<lambda>_. True) 0 0) ?cfg"
    proof -
      have "fst ?cfg = length M1 + length M2 + 1"
        using assms(2) len_M trace_def traces_def by simp
      then have "?M ! (fst ?cfg) = cmd_jump (\<lambda>_. True) 0 0"
        by (metis (no_types, lifting) add.right_neutral add_Suc_right length_Cons
          list.size(3) nth_append_length nth_append_length_plus parts plus_1_eq_Suc length_relocate)
      then show ?thesis
        by simp
    qed
    also have "... = (0, tps2)"
      using assms(2) sem_jump trace_def traces_def by auto
    finally show ?thesis
      by simp
  qed

  show "execute ?M (0, tps0) (length ?es) = (0, tps2)"
    using exec_4 by auto
  show " fst (execute ?M (0, tps0) i) < length ?M"
      if "i < length ?es" for i
  proof -
    consider
       "i < length es1"
     | "i = length es1"
     | "i \<ge> length es1 + 1 " and "i \<le> length es1 + length es2 + 1"
     | "i = length es1 + length es2 + 2"
     using `i < length ?es` by fastforce
    then show ?thesis
    proof (cases)
      case 1
      then have "fst (execute ?M (0, tps0) i) = fst (execute M1 (0, tps0) i)"
        using exec_1 by simp
      moreover have "\<forall>i<length es1. fst (execute M1 (0, tps0) i) < length M1"
        using assms trace_def traces_def by simp
      ultimately have "fst (execute ?M (0, tps0) i) < length M1"
        using 1 by simp
      then show ?thesis
        using len_M by simp
    next
      case 2
      then have "fst (execute ?M (0, tps0) i) = fst (execute M1 (0, tps0) i)"
        using exec_1 by simp
      moreover have "execute M1 (0, tps0) (length es1) = (length M1, tps1)"
        using assms trace_def traces_def by simp
      ultimately show ?thesis
        using 2 by (simp add: len_M)
    next
      case 3
      then have eq: "execute ?M (0, tps0) i = execute M2 (0, tps1) (i - (length es1 + 1)) <+=> (length M1 + 1)"
        using exec_3 by simp
      have a: "\<forall>i<length es2. fst (execute M2 (0, tps1) i) < length M2"
        using assms(2) trace_def traces_def that by simp
      have b: "fst (execute M2 (0, tps1) (length es2)) = length M2"
        using assms(2) trace_def traces_def that by simp
      have "i - (length es1 + 1) \<le> length es2"
        using 3 by simp
      then have "fst (execute M2 (0, tps1) (i - (length es1 + 1))) \<le> length M2"
        using a b that using le_eq_less_or_eq by auto
      then have "fst (execute M2 (0, tps1) (i - (length es1 + 1)) <+=> (length M1 + 1)) < length ?M"
        by (simp add: len_M)
      then show ?thesis
        using eq by simp
    next
      case 4
      then show ?thesis
        using exec_4 using len_es that by linarith
    qed
  qed
  show "execute ?M (0, tps0) (Suc i) <#> 0 = fst (?es ! i) \<and>
        execute ?M (0, tps0) (Suc i) <#> 1 = snd (?es ! i)"
    if "i < length ?es" for i
  proof -
    consider
       "i < length es1"
     | "i = length es1"
     | "i \<ge> length es1 + 1 " and "i < length es1 + length es2 + 1"
     | "i = length es1 + length es2 + 1"
     using `i < length ?es` by fastforce
    then show ?thesis
    proof (cases)
      case 1
      then have "Suc i \<le> length es1"
        by simp
      then have "execute ?M (0, tps0) (Suc i) = execute M1 (0, tps0) (Suc i)"
        using exec_1 by blast
      then show ?thesis
        using assms(1) trace_def traces_def by (simp add: "1" nth_append)
    next
      case 2
      then have "execute ?M (0, tps0) (Suc i) = (length M1 + 1, tps1)"
        using exec_2 by simp
      then show ?thesis
        using 2 by simp
    next
      case 3
      then have Suc_i: "Suc i \<ge> length es1 + 1 " "Suc i \<le> length es1 + length es2 + 1"
        by simp_all
      then have *: "execute ?M (0, tps0) (Suc i) =
          execute M2 (0, tps1) (Suc i - (length es1 + 1)) <+=> (length M1 + 1)"
        using exec_3 by blast
      from 3 have i: "i - (length es1 + 1) < length es2" (is "?j < length es2")
        by simp
      then have **: "execute M2 (0, tps1) (Suc ?j) <#> 0 = fst (es2 ! ?j) \<and>
                 execute M2 (0, tps1) (Suc ?j) <#> 1 = snd (es2 ! ?j)"
        using assms(2) trace_def traces_def by simp
      have "((es1 @ [(tps1 :#: 0, tps1 :#: 1)]) @ es2) ! i = es2 ! ?j"
        using i 3 by (simp add: nth_append)
      then have "es2 ! ?j = ?es ! i"
        by (metis Suc_eq_plus1 append.assoc i length_append_singleton nth_append)
      then show ?thesis
        using * ** using "3"(1) Suc_diff_le by fastforce
    next
      case 4
      then have "execute ?M (0, tps0) (Suc i) = (0, tps2)"
        using exec_4 by simp
      then show ?thesis
        by (simp add: "4" nth_append)
    qed
  qed
qed

lemma tm_loop_sem_true_tracesI:
  assumes "traces M1 tps0 es1 tps1"
    and "traces M2 tps1 es2 tps2"
    and "cond (read tps1)"
    and "es = es1 @ [(tps1 :#: 0, tps1 :#: 1)] @ es2 @ [(tps2 :#: 0, tps2 :#: 1)]"
  shows "trace (WHILE M1 ; cond DO M2 DONE) (0, tps0) es (0, tps2)"
  using assms tm_loop_sem_true_traces by blast

text \<open>
Combining traces for $m$ iterations of a loop. Typically $m$ will be the total
number of iterations.
\<close>

lemma tm_loop_trace_simple:
  fixes m :: nat
    and M :: machine
    and tps :: "nat \<Rightarrow> tape list"
    and es :: "nat \<Rightarrow> (nat \<times> nat) list"
  assumes "\<And>i. i < m \<Longrightarrow> trace M (0, tps i) (es i) (0, tps (Suc i))"
  shows "trace M (0, tps 0) (concat (map es [0..<m])) (0, tps m)"
  using assms trace_Nil trace_additive by (induction m) simp_all

text \<open>
For simple loops, where we have an upper bound for the length of traces
independent of the iteration, there is a trivial upper bound for the length of
the trace of $m$ iterations. This is the only situation we will encounter.
\<close>

lemma length_concat_le:
  assumes "\<And>i. i < m \<Longrightarrow> length (es i) \<le> b"
  shows "length (concat (map es [0..<m])) \<le> m * b"
  using assms
proof (induction m)
  case 0
  then show ?case
    by simp
next
  case (Suc m)
  have "length (concat (map es [0..<Suc m])) = length (concat (map es [0..<m])) + length (es m)"
    by simp
  also have "... \<le> m * b + length (es m)"
    using Suc by simp
  also have "... \<le> m * b + b"
    using Suc by simp
  also have "... = (Suc m) * b"
    by simp
  finally show ?case .
qed


subsection \<open>Traces for elementary Turing machines\label{s:oblivious-traces}\<close>

text \<open>
Just like the not necessarily oblivious Turing machines considered so far, our
oblivious Turing machines will be built from elementary ones from
Section~\ref{s:tm-elementary}. In this subsection we show the traces of all the
elementary machines we will need.
\<close>

lemma tm_left_0_traces:
  assumes "length tps > 1"
  shows "traces
    (tm_left 0)
    tps
    [(tps :#: 0 - 1, tps :#: 1)]
    (tps[0:=(fst (tps ! 0), snd (tps ! 0) - 1)])"
proof -
  from assms have "length tps > 0"
    by auto
  with assms show ?thesis
    using execute_tm_left assms tm_left_def by (intro tracesI) simp_all
qed

lemma traces_tm_left_0I:
  assumes "length tps > 1"
    and "es = [(tps :#: 0 - 1, tps :#: 1)]"
    and "tps' = (tps[0:=(fst (tps ! 0), snd (tps ! 0) - 1)])"
  shows "traces (tm_left 0) tps es tps'"
  using tm_left_0_traces assms by simp

lemma tm_left_1_traces:
  assumes "length tps > 1"
  shows "traces
    (tm_left 1)
    tps
    [(tps :#: 0, tps :#: 1 - 1)]
    (tps[1:=(fst (tps ! 1), snd (tps ! 1) - 1)])"
proof -
  from assms have "length tps > 0"
    by auto
  with assms show ?thesis
    using execute_tm_left assms tm_left_def by (intro tracesI) simp_all
qed

lemma traces_tm_left_1I:
  assumes "length tps > 1"
    and "es = [(tps :#: 0, tps :#: 1 - 1)]"
    and "tps' = (tps[1:=(fst (tps ! 1), snd (tps ! 1) - 1)])"
  shows "traces (tm_left 1) tps es tps'"
  using tm_left_1_traces assms by simp

lemma tm_right_0_traces:
  assumes "length tps > 1"
  shows "traces
    (tm_right 0)
    tps
    [(tps :#: 0 + 1, tps :#: 1)]
    (tps[0:=(fst (tps ! 0), snd (tps ! 0) + 1)])"
proof -
  from assms have "length tps > 0"
    by auto
  with assms show ?thesis
    using execute_tm_right assms tm_right_def by (intro tracesI) simp_all
qed

lemma traces_tm_right_0I:
  assumes "length tps > 1"
    and "es = [(tps :#: 0 + 1, tps :#: 1)]"
    and "tps' = (tps[0:=(fst (tps ! 0), snd (tps ! 0) + 1)])"
  shows "traces (tm_right 0) tps es tps'"
  using tm_right_0_traces assms by simp

lemma tm_right_1_traces:
  assumes "length tps > 1"
  shows "traces
    (tm_right 1)
    tps
    [(tps :#: 0, tps :#: 1 + 1)]
    (tps[1:=(fst (tps ! 1), snd (tps ! 1) + 1)])"
proof -
  from assms have "length tps > 0"
    by auto
  with assms show ?thesis
    using execute_tm_right assms tm_right_def by (intro tracesI) simp_all
qed

lemma tm_rtrans_1_traces:
  assumes "1 < length tps"
  shows "traces
    (tm_rtrans 1 f)
    tps
    [(tps :#: 0, tps :#: 1 + 1)]
    (tps[1 := tps ! 1 |:=| f (tps :.: 1) |+| 1])"
  using execute_tm_rtrans assms tm_rtrans_def by (intro tracesI) simp_all

lemma traces_tm_right_1I:
  assumes "length tps > 1"
    and "es = [(tps :#: 0, tps :#: 1 + 1)]"
    and "tps' = (tps[1:=(fst (tps ! 1), snd (tps ! 1) + 1)])"
  shows "traces (tm_right 1) tps es tps'"
  using tm_right_1_traces assms by simp

lemma traces_tm_rtrans_1I:
  assumes "1 < length tps"
    and "es = [(tps :#: 0, tps :#: 1 + 1)]"
    and "tps' = (tps[1 := tps ! 1 |:=| f (tps :.: 1) |+| 1])"
  shows "traces (tm_rtrans 1 f) tps es tps'"
  using tm_rtrans_1_traces assms by simp

lemma tm_left_until_1_traces:
  assumes "length tps > 1" and "begin_tape H (tps ! 1)"
  shows "traces
    (tm_left_until H 1)
    tps
    (map (\<lambda>i. (tps :#: 0, i)) (rev [0..<tps :#: 1]) @ [(tps :#: 0, 0)])
    (tps[1 := tps ! 1 |#=| 0])"
proof
  let ?es = "map (\<lambda>i. (tps :#: 0, i)) (rev [0..<tps :#: 1]) @ [(tps :#: 0, 0)]"
  show "execute (tm_left_until H 1) (0, tps) (length ?es) = (length (tm_left_until H 1), tps[1 := tps ! 1 |#=| 0])"
    using execute_tm_left_until assms tm_left_until_def by simp
  show "\<And>i. i < length ?es \<Longrightarrow> fst (execute (tm_left_until H 1) (0, tps) i) < length (tm_left_until H 1)"
    using execute_tm_left_until_less assms tm_left_until_def by simp
  show "execute (tm_left_until H 1) (0, tps) (Suc i) <#> 0 = fst (?es ! i) \<and>
        execute (tm_left_until H 1) (0, tps) (Suc i) <#> 1 = snd (?es ! i)"
      if "i < length ?es" for i
  proof (cases "i < tps :#: 1")
    case True
    then have i: "Suc i \<le> tps :#: 1"
      by simp
    then have "execute (tm_left_until H 1) (0, tps) (Suc i) = (0, tps[1 := tps ! 1 |-| Suc i])"
      using execute_tm_left_until_less assms by presburger
    moreover have "?es ! i = (tps :#: 0, tps :#: 1 - Suc i)"
    proof -
      have "?es ! i = (map (\<lambda>i. (tps :#: 0, i)) (rev [0..<tps :#: 1])) ! i"
        using True by (simp add: nth_append)
      moreover have "(rev [0..<tps :#: 1]) ! i = tps :#: 1 - Suc i"
        using True by (simp add: rev_nth)
      ultimately show ?thesis
        using True by simp
    qed
    ultimately show ?thesis
      using assms(1) by simp
  next
    case False
    then have i: "i = tps :#: 1"
      using that by simp
    then have "execute (tm_left_until H 1) (0, tps) (Suc (tps :#: 1)) = (1, tps[1 := tps ! 1 |#=| 0])"
      using execute_tm_left_until assms by simp
    then have "execute (tm_left_until H 1) (0, tps) (Suc i) = (1, tps[1 := tps ! 1 |#=| 0])"
      using i by simp
    moreover have "?es ! i = (tps :#: 0, 0)"
      using i by (metis diff_zero length_map length_rev length_upt nth_append_length)
    ultimately show ?thesis
      using assms(1) by simp
  qed
qed

lemma traces_tm_left_until_1I:
  assumes "length tps > 1"
    and "begin_tape H (tps ! 1)"
    and "es = map (\<lambda>i. (tps :#: 0, i)) (rev [0..<tps :#: 1]) @ [(tps :#: 0, 0)]"
    and "tps' = tps[1 := tps ! 1 |#=| 0]"
  shows "traces (tm_left_until H 1) tps es tps'"
  using tm_left_until_1_traces assms by simp

lemma tm_left_until_0_traces:
  assumes "length tps > 1" and "begin_tape H (tps ! 0)"
  shows "traces
    (tm_left_until H 0)
    tps
    (map (\<lambda>i. (i, tps :#: 1)) (rev [0..<tps :#: 0]) @ [(0, tps :#: 1)])
    (tps[0 := tps ! 0 |#=| 0])"
proof
  have len: "length tps > 0"
    using assms(1) by auto
  let ?es = "map (\<lambda>i. (i, tps :#: 1)) (rev [0..<tps :#: 0]) @ [(0, tps :#: 1)]"
  show "execute (tm_left_until H 0) (0, tps) (length ?es) = (length (tm_left_until H 0), tps[0 := tps ! 0 |#=| 0])"
    using execute_tm_left_until assms(2) tm_left_until_def len by simp
  show "\<And>i. i < length ?es \<Longrightarrow> fst (execute (tm_left_until H 0) (0, tps) i) < length (tm_left_until H 0)"
    using execute_tm_left_until_less len assms(2) tm_left_until_def by simp
  show "execute (tm_left_until H 0) (0, tps) (Suc i) <#> 0 = fst (?es ! i) \<and>
        execute (tm_left_until H 0) (0, tps) (Suc i) <#> 1 = snd (?es ! i)"
      if "i < length ?es" for i
  proof (cases "i < tps :#: 0")
    case True
    then have i: "Suc i \<le> tps :#: 0"
      by simp
    then have "execute (tm_left_until H 0) (0, tps) (Suc i) = (0, tps[0 := tps ! 0 |-| Suc i])"
      using execute_tm_left_until_less assms(2) len by blast
    moreover have "?es ! i = (tps :#: 0 - Suc i, tps :#: 1)"
    proof -
      have "?es ! i = (map (\<lambda>i. (i, tps :#: 1)) (rev [0..<tps :#: 0])) ! i"
        using True by (simp add: nth_append)
      moreover have "(rev [0..<tps :#: 0]) ! i = tps :#: 0 - Suc i"
        using True by (simp add: rev_nth)
      ultimately show ?thesis
        using True by simp
    qed
    ultimately show ?thesis
      using len by simp
  next
    case False
    then have i: "i = tps :#: 0"
      using that by simp
    then have "execute (tm_left_until H 0) (0, tps) (Suc (tps :#: 0)) = (1, tps[0 := tps ! 0 |#=| 0])"
      using execute_tm_left_until assms len by simp
    then have "execute (tm_left_until H 0) (0, tps) (Suc i) = (1, tps[0 := tps ! 0 |#=| 0])"
      using i by simp
    moreover have "?es ! i = (0, tps :#: 1)"
        using i by (metis One_nat_def diff_Suc_1 diff_Suc_Suc length_map length_rev length_upt nth_append_length)
    ultimately show ?thesis
      using len by simp
  qed
qed

lemma traces_tm_left_until_0I:
  assumes "length tps > 1"
    and "begin_tape H (tps ! 0)"
    and "es = map (\<lambda>i. (i, tps :#: 1)) (rev [0..<tps :#: 0]) @ [(0, tps :#: 1)]"
    and "tps' = tps[0 := tps ! 0 |#=| 0]"
  shows "traces (tm_left_until H 0) tps es tps'"
  using tm_left_until_0_traces assms by simp

lemma tm_start_0_traces:
  assumes "length tps > 1" and "clean_tape (tps ! 0)"
  shows "traces
    (tm_start 0)
    tps
    (map (\<lambda>i. (i, tps :#: 1)) (rev [0..<tps :#: 0]) @ [(0, tps :#: 1)])
    (tps[0 := tps ! 0 |#=| 0])"
proof -
  have "begin_tape {1} (tps ! 0)"
    using clean_tape_def begin_tape_def assms(2) by simp
  then show ?thesis
    using tm_left_until_0_traces tm_start_def assms(1) by metis
qed

lemma tm_start_1_traces:
  assumes "length tps > 1" and "clean_tape (tps ! 1)"
  shows "traces
    (tm_start 1)
    tps
    (map (\<lambda>i. (tps :#: 0, i)) (rev [0..<tps :#: 1]) @ [(tps :#: 0, 0)])
    (tps[1 := tps ! 1 |#=| 0])"
proof -
  have "begin_tape {1} (tps ! 1)"
    using clean_tape_def begin_tape_def assms(2) by simp
  then show ?thesis
    using tm_left_until_1_traces tm_start_def assms(1) by metis
qed

lemma traces_tm_start_1I:
  assumes "length tps > 1"
    and "clean_tape (tps ! 1)"
    and "es = map (\<lambda>i. (tps :#: 0, i)) (rev [0..<tps :#: 1]) @ [(tps :#: 0, 0)]"
    and "tps' = tps[1 := tps ! 1 |#=| 0]"
  shows "traces (tm_start 1) tps es tps'"
  using tm_start_1_traces assms by simp

lemma tm_cr_0_traces:
  assumes "length tps > 1" and "clean_tape (tps ! 0)"
  shows "traces
    (tm_cr 0)
    tps
    ((map (\<lambda>i. (i, tps :#: 1)) (rev [0..<tps :#: 0]) @ [(0, tps :#: 1)]) @ [(1, tps :#: 1)])
    (tps[0 := tps ! 0 |#=| 1])"
  unfolding tm_cr_def
proof (rule traces_sequential[where ?tps2.0="tps[0 := tps ! 0 |#=| 0]"])
  from assms(1) have len: "length tps > 0"
    by auto
  show "traces (tm_start 0) tps
     (map (\<lambda>i. (i, tps :#: 1)) (rev [0..<tps :#: 0]) @ [(0, tps :#: 1)])
     (tps[0 := tps ! 0 |#=| 0])"
    using assms tm_start_0_traces by simp
  show "traces (tm_right 0) (tps[0 := tps ! 0 |#=| 0])
     [(1, tps :#: 1)] (tps[0 := tps ! 0 |#=| 1])"
    using assms tm_right_0_traces len
    by (smt One_nat_def add.commute fst_conv length_list_update list_update_overwrite neq0_conv
      nth_list_update_eq nth_list_update_neq plus_1_eq_Suc snd_conv zero_less_one)
qed

lemma traces_tm_cr_0I:
  assumes "length tps > 1" and "clean_tape (tps ! 0)"
    and "es = map (\<lambda>i. (i, tps :#: 1)) (rev [0..<tps :#: 0]) @ [(0, tps :#: 1), (1, tps :#: 1)]"
    and "tps' = tps[0 := tps ! 0 |#=| 1]"
  shows "traces (tm_cr 0) tps es tps'"
  using tm_cr_0_traces assms by simp

lemma tm_cr_1_traces:
  assumes "length tps > 1" and "clean_tape (tps ! 1)"
  shows "traces
    (tm_cr 1)
    tps
    ((map (\<lambda>i. (tps :#: 0, i)) (rev [0..<tps :#: 1]) @ [(tps :#: 0, 0)]) @ [(tps :#: 0, 1)])
    (tps[1 := tps ! 1 |#=| 1])"
  unfolding tm_cr_def
proof (rule traces_sequential[where ?tps2.0="tps[1 := tps ! 1 |#=| 0]"])
  show "traces (tm_start 1) tps
     (map (Pair (tps :#: 0)) (rev [0..<tps :#: 1]) @ [(tps :#: 0, 0)])
     (tps[1 := tps ! 1 |#=| 0])"
    using assms tm_start_1_traces by simp
  show "traces (tm_right 1) (tps[1 := tps ! 1 |#=| 0])
     [(tps :#: 0, 1)] (tps[1 := tps ! 1 |#=| 1])"
    using assms tm_right_1_traces
    by (smt One_nat_def add.commute fst_conv length_list_update list_update_overwrite neq0_conv
      nth_list_update_eq nth_list_update_neq plus_1_eq_Suc snd_conv zero_less_one)
qed

lemma traces_tm_cr_1I:
  assumes "length tps > 1" and "clean_tape (tps ! 1)"
    and "es = map (\<lambda>i. (tps :#: 0, i)) (rev [0..<tps :#: 1]) @ [(tps :#: 0, 0), (tps :#: 0, 1)]"
    and "tps' = tps[1 := tps ! 1 |#=| 1]"
  shows "traces (tm_cr 1) tps es tps'"
  using tm_cr_1_traces assms by simp

lemma heads_tm_trans_until_less:
  assumes "j1 < k" "j2 < k" and "length tps = k"
    and "rneigh (tps ! j1) H n"
    and "t \<le> n"
  shows "execute (tm_trans_until j1 j2 H f) (0, tps) t <#> j1 = tps :#: j1 + t"
    and "execute (tm_trans_until j1 j2 H f) (0, tps) t <#> j2 = tps :#: j2 + t"
  using assms execute_tm_trans_until_less[OF assms]
  by ((metis (no_types, lifting) length_list_update nth_list_update_eq nth_list_update_neq sndI transplant_def),
      (metis (no_types, lifting) length_list_update nth_list_update_eq sndI transplant_def))

lemma heads_tm_ltrans_until_less:
  assumes "j1 < k" and "j2 < k" and "length tps = k"
    and "lneigh (tps ! j1) H n"
    and "t \<le> n"
    and "n \<le> tps :#: j1"
    and "n \<le> tps :#: j2"
  shows "execute (tm_ltrans_until j1 j2 H f) (0, tps) t <#> j1 = tps :#: j1 - t"
    and "execute (tm_ltrans_until j1 j2 H f) (0, tps) t <#> j2 = tps :#: j2 - t"
  using assms execute_tm_ltrans_until_less[OF assms]
  by ((metis (no_types, lifting) length_list_update nth_list_update_eq nth_list_update_neq sndI ltransplant_def),
      (metis (no_types, lifting) length_list_update nth_list_update_eq sndI ltransplant_def))

lemma heads_tm_trans_until_less':
  assumes "j1 < k" and "j2 < k" and "length tps = k"
    and "rneigh (tps ! j1) H n"
    and "t \<le> n"
    and "j \<noteq> j1" and "j \<noteq> j2"
  shows "execute (tm_trans_until j1 j2 H f) (0, tps) t <#> j = tps :#: j"
  using assms execute_tm_trans_until_less[OF assms(1-5)] by simp

lemma heads_tm_ltrans_until_less':
  assumes "j1 < k" and "j2 < k" and "length tps = k"
    and "lneigh (tps ! j1) H n"
    and "t \<le> n"
    and "n \<le> tps :#: j1"
    and "n \<le> tps :#: j2"
    and "j \<noteq> j1" and "j \<noteq> j2"
  shows "execute (tm_ltrans_until j1 j2 H f) (0, tps) t <#> j = tps :#: j"
  using assms execute_tm_ltrans_until_less[OF assms(1-7)] by simp

lemma heads_tm_trans_until:
  assumes "j1 < k" and "j2 < k" and "length tps = k" and "rneigh (tps ! j1) H n"
  shows "execute (tm_trans_until j1 j2 H f) (0, tps) (Suc n) <#> j1 = tps :#: j1 + n"
    and "execute (tm_trans_until j1 j2 H f) (0, tps) (Suc n) <#> j2 = tps :#: j2 + n"
  using assms execute_tm_trans_until[OF assms]
    by ((metis (no_types, lifting) length_list_update nth_list_update_eq nth_list_update_neq snd_conv transplant_def),
        (metis (no_types, lifting) length_list_update nth_list_update_eq snd_conv transplant_def))

lemma heads_tm_ltrans_until:
  assumes "j1 < k" and "j2 < k" and "length tps = k"
    and "lneigh (tps ! j1) H n"
    and "n \<le> tps :#: j1"
    and "n \<le> tps :#: j2"
  shows "execute (tm_ltrans_until j1 j2 H f) (0, tps) (Suc n) <#> j1 = tps :#: j1 - n"
    and "execute (tm_ltrans_until j1 j2 H f) (0, tps) (Suc n) <#> j2 = tps :#: j2 - n"
  using assms execute_tm_ltrans_until[OF assms]
    by ((metis (no_types, lifting) length_list_update nth_list_update_eq nth_list_update_neq snd_conv ltransplant_def),
        (metis (no_types, lifting) length_list_update nth_list_update_eq snd_conv ltransplant_def))

lemma heads_tm_trans_until':
  assumes "j1 < k" and "j2 < k" and "length tps = k"
    and "rneigh (tps ! j1) H n"
    and "j \<noteq> j1" and "j \<noteq> j2"
  shows "execute (tm_trans_until j1 j2 H f) (0, tps) (Suc n) <#> j = tps :#: j"
  using assms execute_tm_trans_until[OF assms(1-4)] by simp

lemma heads_tm_ltrans_until':
  assumes "j1 < k" and "j2 < k" and "length tps = k"
    and "lneigh (tps ! j1) H n"
    and "n \<le> tps :#: j1"
    and "n \<le> tps :#: j2"
    and "j \<noteq> j1" and "j \<noteq> j2"
  shows "execute (tm_ltrans_until j1 j2 H f) (0, tps) (Suc n) <#> j = tps :#: j"
  using assms execute_tm_ltrans_until[OF assms(1-6)] by simp

lemma traces_tm_trans_until_11:
  assumes "1 < k" and "length tps = k" and "rneigh (tps ! 1) H n"
  shows "traces (tm_trans_until 1 1 H f)
    tps
    (map (\<lambda>i. (tps :#: 0, tps :#: 1 + Suc i)) [0..<n] @ [(tps :#: 0, tps :#: 1 + n)])
    (tps[1 := transplant (tps ! 1) (tps ! 1) f n])"
proof
  let ?es = "map (\<lambda>i. (tps :#: 0, tps :#: 1 + Suc i)) [0..<n] @ [(tps :#: 0, tps :#: 1 + n)]"
  let ?tps = "tps [1 := transplant (tps ! 1) (tps ! 1) f n]"
  let ?M = "tm_trans_until 1 1 H f"
  have len: "length ?es = Suc n"
    by simp
  show "execute ?M (0, tps) (length ?es) = (length ?M, ?tps)"
    using tm_trans_until_def len execute_tm_trans_until assms by simp
  show "fst (execute ?M (0, tps) i) < length ?M" if "i < length ?es" for i
  proof -
    from that len have "i \<le> n"
      by simp
    then have "fst (execute ?M (0, tps) i) = 0"
      using execute_tm_trans_until_less assms by simp
    then show ?thesis
      using tm_trans_until_def by simp
  qed
  show "execute ?M (0, tps) (Suc i) <#> 0 = fst (?es ! i) \<and>
        execute ?M (0, tps) (Suc i) <#> 1 = snd (?es ! i)"
    if "i < length ?es" for i
  proof (cases "i < n")
    case True
    then have "?es ! i = (tps :#: 0, tps :#: 1 + Suc i)"
      by (simp add: nth_append)
    moreover from True have "Suc i \<le> n"
      by simp
    ultimately show ?thesis
      using heads_tm_trans_until_less' heads_tm_trans_until_less assms
      by (metis One_nat_def Suc_neq_Zero fst_conv snd_conv)
  next
    case False
    then have "i = n"
      using that by simp
    then have "?es ! i = (tps :#: 0, tps :#: 1 + n)"
      by (metis (no_types, lifting) diff_zero length_map length_upt nth_append_length)
    then show ?thesis
      using heads_tm_trans_until' heads_tm_trans_until assms `i = n` by simp
  qed
qed

lemma traces_tm_ltrans_until_11:
  assumes "1 < k" and "length tps = k" and "lneigh (tps ! 1) H n" and "n \<le> tps :#: 1"
  shows "traces (tm_ltrans_until 1 1 H f)
    tps
    (map (\<lambda>i. (tps :#: 0, tps :#: 1 - Suc i)) [0..<n] @ [(tps :#: 0, tps :#: 1 - n)])
    (tps[1 := ltransplant (tps ! 1) (tps ! 1) f n])"
proof
  let ?es = "map (\<lambda>i. (tps :#: 0, tps :#: 1 - Suc i)) [0..<n] @ [(tps :#: 0, tps :#: 1 - n)]"
  let ?tps = "tps [1 := ltransplant (tps ! 1) (tps ! 1) f n]"
  let ?M = "tm_ltrans_until 1 1 H f"
  have len: "length ?es = Suc n"
    by simp
  show "execute ?M (0, tps) (length ?es) = (length ?M, ?tps)"
    using tm_ltrans_until_def len execute_tm_ltrans_until assms by simp
  show "fst (execute ?M (0, tps) i) < length ?M" if "i < length ?es" for i
  proof -
    from that len have "i \<le> n"
      by simp
    then have "fst (execute ?M (0, tps) i) = 0"
      using execute_tm_ltrans_until_less assms by simp
    then show ?thesis
      using tm_ltrans_until_def by simp
  qed
  show "execute ?M (0, tps) (Suc i) <#> 0 = fst (?es ! i) \<and>
        execute ?M (0, tps) (Suc i) <#> 1 = snd (?es ! i)"
    if "i < length ?es" for i
  proof (cases "i < n")
    case True
    then have "?es ! i = (tps :#: 0, tps :#: 1 - Suc i)"
      by (simp add: nth_append)
    moreover from True have "Suc i \<le> n"
      by simp
    ultimately show ?thesis
      using heads_tm_ltrans_until_less' heads_tm_ltrans_until_less assms
      by (metis One_nat_def Suc_neq_Zero fst_conv snd_conv)
  next
    case False
    then have "i = n"
      using that by simp
    then have "?es ! i = (tps :#: 0, tps :#: 1 - n)"
      by (metis (no_types, lifting) diff_zero length_map length_upt nth_append_length)
    then show ?thesis
      using heads_tm_ltrans_until' heads_tm_ltrans_until assms `i = n` by simp
  qed
qed

lemma traces_tm_trans_until_01:
  assumes "0 < k" and "1 < k" and "length tps = k" and "rneigh (tps ! 0) H n"
  shows "traces (tm_trans_until 0 1 H f)
    tps
    (map (\<lambda>i. (tps :#: 0 + Suc i, tps :#: 1 + Suc i)) [0..<n] @ [(tps :#: 0 + n, tps :#: 1 + n)])
    (tps[0 := tps ! 0 |+| n, 1 := transplant (tps ! 0) (tps ! 1) f n])"
proof
  let ?es = "map (\<lambda>i. (tps :#: 0 + Suc i, tps :#: 1 + Suc i)) [0..<n] @ [(tps :#: 0 + n, tps :#: 1 + n)]"
  let ?tps = "tps [0 := tps ! 0 |+| n, 1 := transplant (tps ! 0) (tps ! 1) f n]"
  let ?M = "tm_trans_until 0 1 H f"
  have len: "length ?es = Suc n"
    by simp
  show "execute ?M (0, tps) (length ?es) = (length ?M, ?tps)"
    using tm_trans_until_def len execute_tm_trans_until[of 0 k 1] assms by simp
  show "fst (execute ?M (0, tps) i) < length ?M" if "i < length ?es" for i
  proof -
    from that len have "i \<le> n"
      by simp
    then have "fst (execute ?M (0, tps) i) = 0"
      using execute_tm_trans_until_less[of 0 k 1] assms by simp
    then show ?thesis
      using tm_trans_until_def by simp
  qed
  show "execute ?M (0, tps) (Suc i) <#> 0 = fst (?es ! i) \<and>
        execute ?M (0, tps) (Suc i) <#> 1 = snd (?es ! i)"
    if "i < length ?es" for i
  proof (cases "i < n")
    case True
    then have "?es ! i = (tps :#: 0 + Suc i, tps :#: 1 + Suc i)"
      by (simp add: nth_append)
    moreover from True have "Suc i \<le> n"
      by simp
    ultimately show ?thesis
      using heads_tm_trans_until_less[of 0 k 1 tps H n "Suc i" f] assms by simp
  next
    case False
    then have "i = n"
      using that by simp
    then have "?es ! i = (tps :#: 0 + n, tps :#: 1 + n)"
      by (metis (no_types, lifting) diff_zero length_map length_upt nth_append_length)
    then show ?thesis
      using heads_tm_trans_until[of 0 k 1 tps H n f] assms `i = n` by simp
  qed
qed

lemma traces_tm_trans_until_01I:
  assumes "1 < length tps"
    and "rneigh (tps ! 0) H n"
    and "es = map (\<lambda>i. (tps :#: 0 + Suc i, tps :#: 1 + Suc i)) [0..<n] @ [(tps :#: 0 + n, tps :#: 1 + n)]"
    and "tps' = tps[0 := tps ! 0 |+| n, 1 := transplant (tps ! 0) (tps ! 1) f n]"
  shows "traces (tm_trans_until 0 1 H f) tps es tps'"
  using assms traces_tm_trans_until_01 by simp

lemma traces_tm_trans_until_11I:
  assumes "1 < length tps"
    and "rneigh (tps ! 1) H n"
    and "es = map (\<lambda>i. (tps :#: 0, tps :#: 1 + Suc i)) [0..<n] @ [(tps :#: 0, tps :#: 1 + n)]"
    and "tps' = tps[1 := transplant (tps ! 1) (tps ! 1) f n]"
  shows "traces (tm_trans_until 1 1 H f) tps es tps'"
  using assms traces_tm_trans_until_11 by simp

lemma traces_tm_ltrans_until_11I:
  assumes "1 < length tps" and "\<forall>h<G. f h < G"
    and "lneigh (tps ! 1) H n"
    and "n \<le> tps :#: 1"
    and "es = map (\<lambda>i. (tps :#: 0, tps :#: 1 - Suc i)) [0..<n] @ [(tps :#: 0, tps :#: 1 - n)]"
    and "tps' = tps[1 := ltransplant (tps ! 1) (tps ! 1) f n]"
  shows "traces (tm_ltrans_until 1 1 H f) tps es tps'"
  using assms traces_tm_ltrans_until_11 by simp

lemma traces_tm_const_until_01I:
  assumes "1 < length tps"
    and "rneigh (tps ! 0) H n"
    and "es = map (\<lambda>i. (tps :#: 0 + Suc i, tps :#: 1 + Suc i)) [0..<n] @ [(tps :#: 0 + n, tps :#: 1 + n)]"
    and "tps' = tps[0 := tps ! 0 |+| n, 1 := constplant (tps ! 1) h n]"
  shows "traces (tm_const_until 0 1 H h) tps es tps'"
  using assms traces_tm_trans_until_01 tm_const_until_def constplant_transplant[of _ _ _ "tps ! 0"] by simp

lemma traces_tm_const_until_11I:
  assumes "1 < length tps" and "h < G"
    and "rneigh (tps ! 1) H n"
    and "es = map (\<lambda>i. (tps :#: 0, tps :#: 1 + Suc i)) [0..<n] @ [(tps :#: 0, tps :#: 1 + n)]"
    and "tps' = tps[1 := constplant (tps ! 1) h n]"
  shows "traces (tm_const_until 1 1 H h) tps es tps'"
  using assms traces_tm_trans_until_11 tm_const_until_def constplant_transplant[of _ _ _ "tps ! 1"] by simp

lemma traces_tm_cp_until_01I:
  assumes "1 < length tps"
    and "rneigh (tps ! 0) H n"
    and "es = map (\<lambda>i. (tps :#: 0 + Suc i, tps :#: 1 + Suc i)) [0..<n] @ [(tps :#: 0 + n, tps :#: 1 + n)]"
    and "tps' = tps[0 := tps ! 0 |+| n, 1 := implant (tps ! 0) (tps ! 1) n]"
  shows "traces (tm_cp_until 0 1 H) tps es tps'"
  using assms traces_tm_trans_until_01 tm_cp_until_def by simp

lemma traces_tm_cp_until_11I:
  assumes "1 < length tps"
    and "rneigh (tps ! 1) H n"
    and "es = map (\<lambda>i. (tps :#: 0, tps :#: 1 + Suc i)) [0..<n] @ [(tps :#: 0, tps :#: 1 + n)]"
    and "tps' = tps[1 := implant (tps ! 1) (tps ! 1) n]"
  shows "traces (tm_cp_until 1 1 H) tps es tps'"
  using assms traces_tm_trans_until_11 tm_cp_until_def by simp

lemma traces_tm_right_until_1I:
  assumes "1 < length tps"
    and "rneigh (tps ! 1) H n"
    and "es = map (\<lambda>i. (tps :#: 0, tps :#: 1 + Suc i)) [0..<n] @ [(tps :#: 0, tps :#: 1 + n)]"
    and "tps' = tps[1 := (tps ! 1) |+| n]"
  shows "traces (tm_right_until 1 H) tps es tps'"
  using assms traces_tm_cp_until_11I tm_right_until_def implant_self by simp

lemma execute_tm_write:
  shows "execute (tm_write j h) (0, tps) 1 = (1, tps[j := tps ! j |:=| h])"
  using sem_cmd_write exe_lt_length tm_write_def by simp

lemma traces_tm_writeI:
  assumes "j > 0" and "j < length tps"
    and "es = [(tps :#: 0, tps :#: 1)]"
    and "tps' = tps[j := tps ! j |:=| h]"
  shows "traces (tm_write j h) tps es tps'"
  using assms execute_tm_write tm_write_def by (intro tracesI) (auto simp add: nth_list_update)

corollary traces_tm_write_1I:
  assumes "1 < length tps"
    and "es = [(tps :#: 0, tps :#: 1)]"
    and "tps' = tps[1 := tps ! 1 |:=| h]"
  shows "traces (tm_write 1 h) tps es tps'"
  using assms traces_tm_writeI by simp

corollary traces_tm_write_ge2I:
  assumes "j \<ge> 2"
    and "j < length tps"
    and "es = [(tps :#: 0, tps :#: 1)]"
    and "tps' = tps[j := tps ! j |:=| h]"
  shows "traces (tm_write j h) tps es tps'"
  using assms traces_tm_writeI by simp

lemma execute_tm_write_manyI:
  assumes "0 \<notin> J" and "\<forall>j\<in>J. j < k" and "k \<ge> 2" and "length tps = k"
    and "length tps' = k"
    and "\<And>j. j \<in> J \<Longrightarrow> tps' ! j = tps ! j |:=| h"
    and "\<And>j. j < k \<Longrightarrow> j \<notin> J \<Longrightarrow> tps' ! j = tps ! j"
  shows "execute (tm_write_many J h) (0, tps) 1 = (1, tps')"
proof -
  have "tps' = map (\<lambda>j. if j \<in> J then tps ! j |:=| h else tps ! j) [0..<length tps]" (is "_ = ?rhs")
    using assms by (intro nth_equalityI) simp_all
  then show ?thesis
    using assms execute_tm_write_many by simp
qed

lemma traces_tm_write_manyI:
  assumes "0 \<notin> J" and "\<forall>j\<in>J. j < k" and "k \<ge> 2" and "length tps = k"
    and "length tps' = k"
    and "\<And>j. j \<in> J \<Longrightarrow> tps' ! j = tps ! j |:=| h"
    and "\<And>j. j < k \<Longrightarrow> j \<notin> J \<Longrightarrow> tps' ! j = tps ! j"
    and "es = [(tps :#: 0, tps :#: 1)]"
  shows "traces (tm_write_many J h) tps es tps'"
proof
  show "execute (tm_write_many J h) (0, tps) (length es) = (length (tm_write_many J h), tps')"
    using execute_tm_write_manyI[OF assms(1-7)] tm_write_many_def assms(8) by simp
  show "\<And>i. i < length es \<Longrightarrow>
          fst (execute (tm_write_many J h) (0, tps) i) < length (tm_write_many J h)"
    using assms(8) tm_write_many_def by simp
  show "\<And>i. i < length es \<Longrightarrow>
        snd (execute (tm_write_many J h) (0, tps) (Suc i)) :#: 0 = fst (es ! i) \<and>
        snd (execute (tm_write_many J h) (0, tps) (Suc i)) :#: 1 = snd (es ! i)"
    using execute_tm_write_manyI[OF assms(1-7)] tm_write_many_def assms(3,6,7,8)
    by (metis One_nat_def Suc_1 Suc_lessD fst_conv length_Cons less_Suc0
      less_eq_Suc_le list.size(3) nth_Cons_0 snd_conv)
qed

lemma traces_tm_write_repeat_1I:
  assumes "1 < length tps"
    and "es = map (\<lambda>i. (tps :#: 0, tps :#: 1 + Suc i)) [0..<m]"
    and "tps' = tps[1 := overwrite (tps ! 1) h m]"
  shows "traces (tm_write_repeat 1 h m) tps es tps'"
proof
  let ?M = "tm_write_repeat 1 h m"
  have "length es = m"
    using assms(2) by simp
  moreover have "length ?M = m"
    using tm_write_repeat_def by simp
  ultimately show "execute ?M (0, tps) (length es) = (length ?M, tps')"
    using assms by (simp add: execute_tm_write_repeat)
  show "\<And>i. i < length es \<Longrightarrow> fst (execute ?M (0, tps) i) < length ?M"
    using assms execute_tm_write_repeat tm_write_repeat_def by simp
  show "execute ?M (0, tps) (Suc i) <#> 0 = fst (es ! i) \<and>
        execute ?M (0, tps) (Suc i) <#> 1 = snd (es ! i)"
      if "i < length es" for i
  proof -
    have "Suc i \<le> m"
      using assms \<open>length es = m\<close> that by linarith
    then have "execute ?M (0, tps) (Suc i) = (Suc i, tps[1 := overwrite (tps ! 1) h (Suc i)])"
      using that execute_tm_write_repeat assms by blast
    then show ?thesis
      using overwrite_def assms(1,2) that by simp
  qed
qed


subsection \<open>Memorizing in states\<close>

text \<open>
We need some results for the traces of ``cartesian'' machines used for the
memorizing-in-states technique introduced in Section~\ref{s:tm-memorizing}.
\<close>

lemma cartesian_trace:
  assumes "turing_machine (Suc k) G M"
    and "immobile M k (Suc k)"
    and "M' = cartesian M G"
    and "k \<ge> 2"
    and "\<forall>i<length zs. zs ! i < G"
    and "trace M (start_config (Suc k) zs) es cfg"
  shows "trace M' (start_config k zs) es (squish G (length M) cfg)"
proof (rule traceI')
  show "execute M' (start_config k zs) (length es) = squish G (length M) cfg"
    using assms cartesian_execute_start_config trace_def by auto
  have len: "length M' = G * length M"
    by (simp add: assms(3) length_cartesian)
  have "G > 0"
    using assms(1) turing_machine_sequential_def by (simp add: turing_machine_def)
  show "fst (execute M' (start_config k zs) i) < length M'"
      if "i < length es" for i
  proof (rule ccontr)
    assume "\<not> fst (execute M' (start_config k zs) i) < length M'"
    then have "fst (execute M' (start_config k zs) i) \<ge> length M'"
      by simp
    then have "fst (execute M' (start_config k zs) i) = length M'"
      using assms(1,3) cartesian_tm'
      by (metis (no_types, lifting) Suc_1 Suc_le_D assms(4) start_config_def start_config_length
        le_add2 le_add_same_cancel2 le_antisym less_Suc_eq_0_disj prod.sel(1) turing_machine_execute_states)
    then have "fst (squish G (length M) (execute M (start_config (Suc k) zs) i)) = G * length M"
      using assms cartesian_execute_start_config len by simp
    moreover have "fst (execute M (start_config (Suc k) zs) i) \<le> length M"
      using assms(1) assms(6) that trace_def by auto
    ultimately have "fst (execute M (start_config (Suc k) zs) i) = length M"
      using squish_halt_state `0 < G` by simp
    then show False
      using that assms(6) trace_def by auto
  qed
  show "execute M' (start_config k zs) (Suc i) <#> 0 = fst (es ! i) \<and>
        execute M' (start_config k zs) (Suc i) <#> 1 = snd (es ! i)"
    if "i < length es" for i
  proof (rule ccontr)
    assume a: "\<not> (snd (execute M' (start_config k zs) (Suc i)) :#: 0 = fst (es ! i) \<and>
       snd (execute M' (start_config k zs) (Suc i)) :#: 1 = snd (es ! i))"
    have *: "execute M' (start_config k zs) (Suc i) =
        squish G (length M) (execute M (start_config (Suc k) zs) (Suc i))"
      using assms cartesian_execute_start_config by blast
    then have "execute M' (start_config k zs) (Suc i) <#> 0 =
        squish G (length M) (execute M (start_config (Suc k) zs) (Suc i)) <#> 0"
      by simp
    also have "... = execute M (start_config (Suc k) zs) (Suc i) <#> 0"
      using squish_head_pos assms execute_num_tapes start_config_length le_imp_less_Suc zero_less_Suc
      by presburger
    also have "... = fst (es ! i)"
      using that assms trace_def by simp
    finally have fst: "execute M' (start_config k zs) (Suc i) <#> 0 = fst (es ! i)" .

    from * have "execute M' (start_config k zs) (Suc i) <#> 1 =
        squish G (length M) (execute M (start_config (Suc k) zs) (Suc i)) <#> 1"
      by simp
    also have "... = execute M (start_config (Suc k) zs) (Suc i) <#> 1"
      using squish_head_pos assms execute_num_tapes start_config_length le_imp_less_Suc zero_less_Suc
      by presburger
    also have "... = snd (es ! i)"
      using that assms trace_def by simp
    finally have "execute M' (start_config k zs) (Suc i) <#> 1 = snd (es ! i)" .
    then show False
      using fst a by simp
  qed
qed

lemma cartesian_traces:
  assumes "turing_machine (Suc k) G M"
    and "immobile M k (Suc k)"
    and "M' = cartesian M G"
    and "k \<ge> 2"
    and "\<forall>i<length zs. zs ! i < G"
    and "traces M (snd (start_config (Suc k) zs)) es tps"
  shows "traces M' (snd (start_config k zs)) es (butlast tps)"
proof -
  have "trace M (start_config (Suc k) zs) es (length M, tps)"
    using assms(6) traces_def by (simp add: start_config_def)
  then have "trace M' (start_config k zs) es (squish G (length M) (length M, tps))"
    using assms cartesian_trace by simp
  then show ?thesis
    using squish traces_def by (simp add: assms(3) start_config_def length_cartesian)
qed

lemma traces_tapes_length:
  assumes "turing_machine k G M"
    and "length tps = k"
    and "traces M tps es tps'"
  shows "length tps' = k"
  using assms traces_def execute_num_tapes by (metis snd_conv trace_def)

lemma icartesian:
  assumes "turing_machine (k + 2) G M"
    and "\<And>j. j < k \<Longrightarrow> immobile M (j + 2) (k + 2)"
    and "\<forall>i<length zs. zs ! i < G"
    and "traces M (snd (start_config (k + 2) zs)) es tps"
  shows "traces (icartesian k M G) (snd (start_config 2 zs)) es (take 2 tps)"
  using assms(1,2,4)
proof (induction k arbitrary: M tps)
  case 0
  let ?M = "icartesian 0 M G"
  have "||start_config (0 + 2) zs|| = 2"
    using 0 start_config_length by simp
  then have "length tps = 2"
    using 0 traces_tapes_length by (metis One_nat_def Suc_1 add_2_eq_Suc')
  then have "tps = take 2 tps"
    by simp
  then have "traces ?M (snd (start_config 2 zs)) es (take 2 tps)"
   using 0 by (metis icartesian.simps(1) plus_nat.add_0)
  then show ?case
    by auto
next
  case (Suc k)
  let ?M = "cartesian M G"
  have "turing_machine (Suc (k + 2)) G M"
    using Suc by simp
  moreover have "immobile M (k + 2) (Suc (k + 2))"
    using Suc by simp
  moreover have "k + 2 \<ge> 2"
    by simp
  moreover have "traces M (snd (start_config (Suc (k + 2)) zs)) es tps"
    using Suc by simp
  ultimately have *: "traces ?M (snd (start_config (k + 2) zs)) es (butlast tps)"
    using assms(3) cartesian_traces by simp

  have "turing_machine (k + 2) G ?M"
    using \<open>2 \<le> k + 2\<close> \<open>turing_machine (Suc (k + 2)) G M\<close> cartesian_tm' by blast
  moreover have "\<And>j. j < k \<Longrightarrow> immobile ?M (j + 2) (k + 2)"
    using cartesian_immobile Suc by simp
  ultimately have "traces (icartesian k ?M G) (snd (start_config 2 zs)) es (take 2 (butlast tps))"
    using * Suc by simp
  moreover have "take 2 (butlast tps) = take 2 tps"
  proof -
    have "length tps = Suc k + 2"
      using start_config_length traces_tapes_length Suc
      by (metis (mono_tags, lifting) add_gr_0 zero_less_Suc)
    then show ?thesis
      by (simp add: take_butlast)
  qed
  ultimately show ?case
    by simp
qed

end